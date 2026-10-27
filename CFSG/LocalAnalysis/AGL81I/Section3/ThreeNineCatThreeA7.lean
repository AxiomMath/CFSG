module

public import CFSG.LocalAnalysis.GL83PartI.I_27_9.Perm

public section

namespace GL83.PiGen

open Equiv Equiv.Perm MulAction

variable {Ω : Type*} {R : Subgroup (Perm Ω)}

theorem card_orbit_eq_three_of_card_nine [Fintype Ω] (hR : Nat.card R = 3 ^ 2) (hΩ : Fintype.card Ω < 9)
    {η : Ω} (hη : η ∉ fixSet R) : Nat.card (orbit R η) = 3 := by
  have hdvd : Nat.card (orbit R η) ∣ 3 ^ 2 :=
    hR ▸ Dvd.intro _ (card_mul_card_stabIn R η).symm
  obtain ⟨i, hi, hiq⟩ := (Nat.dvd_prime_pow Nat.prime_three).1 hdvd
  have hle : Nat.card (orbit R η) ≤ Fintype.card Ω := by
    rw [← Nat.card_eq_fintype_card]
    exact Nat.card_le_card_of_injective (Subtype.val : orbit R η → Ω) Subtype.val_injective
  have hne : Nat.card (orbit R η) ≠ 1 := by
    intro h1
    refine hη fun e he => ?_
    have : Subsingleton (orbit R η) := (Nat.card_eq_one_iff_unique.1 h1).1
    have hmem : e η ∈ orbit R η := by
      simpa [Subgroup.smul_def, Perm.smul_def] using mem_orbit η (⟨e, he⟩ : R)
    exact congrArg Subtype.val
      (Subsingleton.elim (⟨e η, hmem⟩ : orbit R η) ⟨η, mem_orbit_self η⟩)
  interval_cases i
  · exact absurd (by simpa using hiq) hne
  · simpa using hiq
  · rw [hiq] at hle
    omega

theorem card_stabIn_eq_three_of_card_nine [Fintype Ω] (hR : Nat.card R = 3 ^ 2) (hΩ : Fintype.card Ω < 9)
    {η : Ω} (hη : η ∉ fixSet R) : Nat.card (stabIn R η) = 3 := by
  have h := card_mul_card_stabIn R η
  rw [hR, card_orbit_eq_three_of_card_nine hR hΩ hη] at h
  omega

theorem mem_fixSet_stabIn_of_mem_orbit (hcomm : ∀ a b : R, a * b = b * a) (η : Ω) {ω : Ω}
    (hω : ω ∈ orbit R η) : ω ∈ fixSet (stabIn R η) := by
  obtain ⟨r, rfl⟩ := hω
  rintro _ ⟨g, hg, rfl⟩
  have h1 : (g : Perm Ω) η = η := by
    have := mem_stabilizer_iff.1 hg
    rwa [Subgroup.smul_def, Perm.smul_def] at this
  have h2 : (g : Perm Ω) * r = r * g := congrArg Subtype.val (hcomm g r)
  change ((g : Perm Ω) * r) η = (r : Perm Ω) η
  rw [h2, Perm.mul_apply, h1]

theorem mem_fixSet_of_mem_orbit (hcomm : ∀ a b : R, a * b = b * a) {E : Subgroup (Perm Ω)}
    (hER : E ≤ R) {ω η : Ω} (hη : η ∈ fixSet E) (hω : ω ∈ orbit R η) : ω ∈ fixSet E := by
  obtain ⟨r, rfl⟩ := hω
  intro e he
  have h2 : e * r = r * e := congrArg Subtype.val (hcomm ⟨e, hER he⟩ r)
  change (e * r) η = (r : Perm Ω) η
  rw [h2, Perm.mul_apply, hη e he]

theorem not_mem_fixSet_of_mem_orbit {η ω : Ω} (hη : η ∉ fixSet R) (hω : ω ∈ orbit R η) :
    ω ∉ fixSet R := by
  obtain ⟨r, rfl⟩ := hω
  intro hfix
  refine hη fun e he => ?_
  have h2 := hfix ((r : Perm Ω) * e * (r : Perm Ω)⁻¹)
    (R.mul_mem (R.mul_mem r.2 he) (R.inv_mem r.2))
  change ((r : Perm Ω) * e * (r : Perm Ω)⁻¹) ((r : Perm Ω) η) = (r : Perm Ω) η at h2
  rw [Perm.mul_apply, Perm.mul_apply, Equiv.Perm.inv_def, Equiv.symm_apply_apply] at h2
  exact (r : Perm Ω).injective h2

theorem exists_orbit_eq_three [Fintype Ω] {η : Ω} (h3 : Nat.card (orbit R η) = 3) :
    ∃ p q : Ω, η ≠ p ∧ η ≠ q ∧ p ≠ q ∧ p ∈ orbit R η ∧ q ∈ orbit R η := by
  classical
  have hcard : (orbit R η).toFinset.card = 3 := by
    rw [Set.toFinset_card, ← Nat.card_eq_fintype_card, h3]
  obtain ⟨x, y, z, hxy, hxz, hyz, hxyz⟩ := Finset.card_eq_three.1 hcard
  have hmem : ∀ ω, ω ∈ orbit R η ↔ ω = x ∨ ω = y ∨ ω = z := fun ω => by
    rw [← Set.mem_toFinset, hxyz]
    simp
  have hη := (hmem η).1 (mem_orbit_self η)
  rcases hη with rfl | rfl | rfl
  · exact ⟨y, z, hxy, hxz, hyz, (hmem y).2 (by simp), (hmem z).2 (by simp)⟩
  · exact ⟨x, z, hxy.symm, hyz, hxz, (hmem x).2 (by simp), (hmem z).2 (by simp)⟩
  · exact ⟨x, y, hxz.symm, hyz.symm, hxy, (hmem x).2 (by simp), (hmem y).2 (by simp)⟩

theorem isThreeCycle_sq_swaps [Fintype Ω] [DecidableEq Ω] {x y z u v w g : Ω} (hxz : x ≠ z) (hxu : x ≠ u)
    (hxv : x ≠ v) (hxw : x ≠ w) (hxg : x ≠ g) (hyz : y ≠ z) (hyu : y ≠ u) (hyv : y ≠ v)
    (hyw : y ≠ w) (hyg : y ≠ g) (hzu : z ≠ u) (hzv : z ≠ v) (hzw : z ≠ w) (hzg : z ≠ g)
    (huw : u ≠ w) (hug : u ≠ g) (hvw : v ≠ w) (hvg : v ≠ g) (hwg : w ≠ g) :
    IsThreeCycle ((swap x y * swap z g * (swap u v * swap w g)) ^ 2) := by
  have hAB : Commute (swap x y) (swap z g) :=
    swap_mul_swap_comm hxz.symm hyz.symm hxg.symm hyg.symm
  have hAC : Commute (swap x y) (swap u v) :=
    swap_mul_swap_comm hxu.symm hyu.symm hxv.symm hyv.symm
  have hAD : Commute (swap x y) (swap w g) :=
    swap_mul_swap_comm hxw.symm hyw.symm hxg.symm hyg.symm
  have hCB : Commute (swap u v) (swap z g) :=
    swap_mul_swap_comm hzu hzv hug.symm hvg.symm
  have hCD : Commute (swap u v) (swap w g) :=
    swap_mul_swap_comm huw.symm hvw.symm hug.symm hvg.symm
  have hrw : swap x y * swap z g * (swap u v * swap w g) =
      swap x y * swap u v * (swap z g * swap w g) := by
    rw [mul_assoc, ← mul_assoc (swap z g), hCB.eq.symm, mul_assoc, mul_assoc]
  have hcomm : Commute (swap x y * swap u v) (swap z g * swap w g) :=
    (hAB.mul_right hAD).mul_left (hCB.mul_right hCD)
  have hsq : (swap x y * swap u v) ^ 2 = 1 := by
    rw [hAC.mul_pow, sq, sq, swap_mul_self, swap_mul_self, one_mul]
  rw [hrw, hcomm.mul_pow, hsq, one_mul, sq, swap_comm z g, swap_comm w g]
  exact (isThreeCycle_swap_mul_swap_same hzg.symm hwg.symm hzw).isThreeCycle_sq

theorem alternatingGroup_le_closure_Y2_three_seven [Fintype Ω] [DecidableEq Ω] (hR : IsPGroup 3 R)
    (h7 : Fintype.card Ω = 7) : alternatingGroup Ω ≤ Subgroup.closure (Y2 3 R) := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hne : Nonempty Ω := Fintype.card_pos_iff.1 (by omega)
  obtain ⟨ω₀⟩ := hne
  obtain ⟨k, hk⟩ := hR.exists_card_eq
  have hk2 : k ≤ 2 := by
    have hdvd : 3 ^ k ∣ 5040 := by
      have := Subgroup.card_subgroup_dvd_card R
      rw [Nat.card_perm, hk, Nat.card_eq_fintype_card (α := Ω), h7] at this
      simpa [Nat.factorial] using this
    by_contra h
    exact absurd (dvd_trans (pow_dvd_pow 3 (by omega : 3 ≤ k)) hdvd) (by norm_num)
  rcases (show k ≤ 1 ∨ k = 2 by omega) with hk1 | rfl
  · refine alternatingGroup_le_closure_Y2_of_card_le (by omega) ?_ ω₀
    rw [hk]
    calc 3 ^ k ≤ 3 ^ 1 := Nat.pow_le_pow_right (by norm_num) hk1
      _ = 3 := by norm_num
  have hΩ : Fintype.card Ω < 9 := by omega
  have hcomm : ∀ a b : R, a * b = b * a :=
    fun a b => (IsPGroup.isMulCommutative_of_card_eq_prime_sq hk).is_comm.comm a b
  set H : Subgroup (Perm Ω) := Subgroup.closure (Y2 3 R) with hH
  obtain ⟨g, hg⟩ : ∃ g : Ω, g ∈ fixSet R := by
    by_contra hno
    push Not at hno
    have hfix : fixSet R = ∅ := Set.eq_empty_of_forall_notMem hno
    have h := card_fixSet_modEq hR
    rw [hfix, Nat.card_eq_fintype_card, h7] at h
    simp [Nat.ModEq] at h
  have hmoved : ∀ E : Subgroup (Perm Ω), Nat.card E = 3 → ∃ η, η ∉ fixSet E := by
    intro E hE
    by_contra hno
    push Not at hno
    have hbot : E = ⊥ := by
      rw [eq_bot_iff]
      intro e he
      rw [Subgroup.mem_bot]
      ext ω
      exact hno ω e he
    rw [hbot, Subgroup.card_bot] at hE
    omega
  have hR3 : Nat.card R ≤ 3 * 3 := by rw [hk]; norm_num
  have hstab : ∀ η, η ∉ fixSet R → Nat.card R ≤ 3 * Nat.card (stabIn R η) := fun η hη => by
    rw [card_stabIn_eq_three_of_card_nine hk hΩ hη]
    exact hR3
  have hgstab : ∀ η, g ∈ fixSet (stabIn R η) := fun η => fixSet_anti (stabIn_le R η) hg
  obtain ⟨x, hx⟩ : ∃ x, x ∉ fixSet R := by
    by_contra hno
    push Not at hno
    have hbot : R = ⊥ := by
      rw [eq_bot_iff]
      intro e he
      rw [Subgroup.mem_bot]
      ext ω
      exact hno ω e he
    rw [hbot, Subgroup.card_bot] at hk
    norm_num at hk
  set E₁ := stabIn R x with hE₁
  obtain ⟨y, z, hxy, hxz, hyz, hy, hz⟩ :=
    exists_orbit_eq_three (card_orbit_eq_three_of_card_nine hk hΩ hx)
  have hxE := mem_fixSet_stabIn R x
  have hyE := mem_fixSet_stabIn_of_mem_orbit hcomm x hy
  have hzE := mem_fixSet_stabIn_of_mem_orbit hcomm x hz
  have hgx : x ≠ g := fun h => hx (h ▸ hg)
  have hgy : y ≠ g := fun h => not_mem_fixSet_of_mem_orbit hx hy (h ▸ hg)
  have hgz : z ≠ g := fun h => not_mem_fixSet_of_mem_orbit hx hz (h ▸ hg)
  obtain ⟨u, hu⟩ := hmoved E₁ (card_stabIn_eq_three_of_card_nine hk hΩ hx)
  have huR : u ∉ fixSet R := fun h => hu (fixSet_anti (stabIn_le R x) h)
  obtain ⟨v, w, huv, huw, hvw, hv, hw⟩ :=
    exists_orbit_eq_three (card_orbit_eq_three_of_card_nine hk hΩ huR)
  have hout : ∀ ω, ω ∈ orbit R u → ω ∉ fixSet E₁ := fun ω hω hωE => by
    have hu' : u ∈ orbit R ω := mem_orbit_symm.1 hω
    exact hu (mem_fixSet_of_mem_orbit hcomm (stabIn_le R x) hωE hu')
  have hvE₁ := hout v hv
  have hwE₁ := hout w hw
  have huE := mem_fixSet_stabIn R u
  have hvE := mem_fixSet_stabIn_of_mem_orbit hcomm u hv
  have hwE := mem_fixSet_stabIn_of_mem_orbit hcomm u hw
  have hgu : u ≠ g := fun h => huR (h ▸ hg)
  have hgv : v ≠ g := fun h => not_mem_fixSet_of_mem_orbit huR hv (h ▸ hg)
  have hgw : w ≠ g := fun h => not_mem_fixSet_of_mem_orbit huR hw (h ▸ hg)
  have hne' : ∀ a b : Ω, a ∈ fixSet E₁ → b ∉ fixSet E₁ → a ≠ b := fun a b ha hb h => hb (h ▸ ha)
  have hs : swap x y * swap z g ∈ Y2 3 R :=
    swap_mul_swap_mem_Y2 (stabIn_le R x) (hstab x hx) hxE hyE hzE (hgstab x) hxy hgz
      hxz.symm hyz.symm hgx.symm hgy.symm
  have ht : swap u v * swap w g ∈ Y2 3 R :=
    swap_mul_swap_mem_Y2 (stabIn_le R u) (hstab u huR) huE hvE hwE (hgstab u) huv hgw
      huw.symm hvw.symm hgu.symm hgv.symm
  have h3 := isThreeCycle_sq_swaps hxz (hne' x u hxE hu) (hne' x v hxE hvE₁)
    (hne' x w hxE hwE₁) hgx hyz (hne' y u hyE hu) (hne' y v hyE hvE₁) (hne' y w hyE hwE₁) hgy
    (hne' z u hzE hu) (hne' z v hzE hvE₁) (hne' z w hzE hwE₁) hgz huw hgu hvw hgv hgw
  have hmem3 : (swap x y * swap z g * (swap u v * swap w g)) ^ 2 ∈ H :=
    Subgroup.pow_mem _ (Subgroup.mul_mem _ (Subgroup.subset_closure hs)
      (Subgroup.subset_closure ht)) 2
  have hreach : ∀ ω : Ω, ∃ h ∈ H, h g = ω := by
    intro ω
    by_cases hωg : ω = g
    · exact ⟨1, H.one_mem, by rw [hωg]; rfl⟩
    by_cases hωR : ω ∈ fixSet R
    ·
      have hωE := fixSet_anti (stabIn_le R x) hωR
      have hωx : ω ≠ x := fun h => hx (h ▸ hωR)
      have hωy : ω ≠ y := fun h => not_mem_fixSet_of_mem_orbit hx hy (h ▸ hωR)
      refine ⟨swap ω g * swap x y, Subgroup.subset_closure
        (swap_mul_swap_mem_Y2 (stabIn_le R x) (hstab x hx) hωE (hgstab x) hxE hyE hωg hxy
          hωx.symm hgx hωy.symm hgy), ?_⟩
      rw [Perm.mul_apply, swap_apply_of_ne_of_ne hgx.symm hgy.symm, swap_apply_right]
    ·
      obtain ⟨p, q, hωp, hωq, hpq, hp, hq⟩ :=
        exists_orbit_eq_three (card_orbit_eq_three_of_card_nine hk hΩ hωR)
      have hgp : p ≠ g := fun h => not_mem_fixSet_of_mem_orbit hωR hp (h ▸ hg)
      have hgq : q ≠ g := fun h => not_mem_fixSet_of_mem_orbit hωR hq (h ▸ hg)
      refine ⟨swap ω g * swap p q, Subgroup.subset_closure
        (swap_mul_swap_mem_Y2 (stabIn_le R ω) (hstab ω hωR) (mem_fixSet_stabIn R ω)
          (hgstab ω) (mem_fixSet_stabIn_of_mem_orbit hcomm ω hp)
          (mem_fixSet_stabIn_of_mem_orbit hcomm ω hq) hωg hpq hωp.symm hgp hωq.symm hgq), ?_⟩
      rw [Perm.mul_apply, swap_apply_of_ne_of_ne hgp.symm hgq.symm, swap_apply_right]
  have hpre : IsPretransitive H Ω := by
    refine ⟨fun a b => ?_⟩
    obtain ⟨ha, haH, hag⟩ := hreach a
    obtain ⟨hb, hbH, hbg⟩ := hreach b
    refine ⟨⟨hb * ha⁻¹, H.mul_mem hbH (H.inv_mem haH)⟩, ?_⟩
    rw [Subgroup.smul_def, Perm.smul_def]
    change (hb * ha⁻¹) a = b
    have hinv : ha⁻¹ a = g := by rw [Equiv.Perm.inv_eq_iff_eq, hag]
    rw [Perm.mul_apply, hinv, hbg]
  have hprim : IsPreprimitive H Ω :=
    IsPreprimitive.of_prime_card (by rw [Nat.card_eq_fintype_card, h7]; norm_num)
  exact alternatingGroup_le_of_isPreprimitive_of_isThreeCycle_mem hprim h3 hmem3

end GL83.PiGen
