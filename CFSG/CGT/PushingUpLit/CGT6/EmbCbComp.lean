module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.FStarSubnormal
public import CFSG.CGT.PushingUpLit.CGT6.EmbAltEnd

public section

namespace CFSG.CGT.PushingUpLit.CGT6

open CFSG CFSG.RankThree.PartOne CFSG.Quasithin CFSG.CGT.PushingUp CFSG.Open Equiv
open scoped commutatorElement

variable {V : Type} [CommGroup V] [Finite V]

omit [Finite V] in
private theorem cbc_isSimpleGroup_alt {X : Subgroup (MulAut V)} {k : ℕ} (hk : 5 ≤ k)
    (θ : ↥X ≃* alternatingGroup (Fin k)) : IsSimpleGroup ↥X := by
  have : IsSimpleGroup (alternatingGroup (Fin k)) :=
    alternatingGroup.isSimpleGroup (by simpa using hk)
  exact θ.isSimpleGroup

omit [Finite V] in
theorem cbc_isQuasisimple_alt {X : Subgroup (MulAut V)} {k : ℕ} (hk : 5 ≤ k)
    (θ : ↥X ≃* alternatingGroup (Fin k)) : CFSG.GorensteinWalter.IsQuasisimple ↥X := by
  have hk' : 5 ≤ Nat.card (Fin k) := by simpa using hk
  have hS : IsSimpleGroup ↥X := cbc_isSimpleGroup_alt hk θ
  have hperf : commutator ↥X = ⊤ := by
    have : Group.IsPerfect (alternatingGroup (Fin k)) :=
      Group.isPerfect_def.mpr (commutator_alternatingGroup_eq_top hk')
    have : Group.IsPerfect ↥X :=
      Group.IsPerfect.ofSurjective (f := θ.symm.toMonoidHom) θ.symm.surjective
    exact Group.isPerfect_def.mp this
  have hcen : Subgroup.center ↥X = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center ↥X) with h | h
    · exact h
    · exfalso
      have h1 := (commutator_eq_bot_iff_center_eq_top ↥X).mpr h
      rw [hperf] at h1
      exact top_ne_bot h1
  refine ⟨hS.toNontrivial, hperf, ?_⟩
  exact MulEquiv.isSimpleGroup
    ((QuotientGroup.quotientMulEquivOfEq hcen).trans QuotientGroup.quotientBot)

omit [Finite V] in
theorem cbc_map_conj_subnormal {H X : Subgroup (MulAut V)} {g : MulAut V} (hg : g ∈ H)
    (hX : (X.subgroupOf H).IsSubnormal) :
    ((X.map (MulAut.conj g).toMonoidHom).subgroupOf H).IsSubnormal := by
  have h1 := hX.comap (MulAut.conj (⟨g, hg⟩ : ↥H)⁻¹).toMonoidHom
  convert h1 using 1
  ext x
  simp only [Subgroup.mem_subgroupOf, Subgroup.mem_map, Subgroup.mem_comap]
  constructor
  · rintro ⟨y, hy, hxy⟩
    have : (g⁻¹ * (x : MulAut V) * g) = y := by
      rw [← hxy]
      simp [MulAut.conj_apply]
      group
    simpa [MulAut.conj_apply, this] using hy
  · intro hx
    refine ⟨g⁻¹ * (x : MulAut V) * g, by simpa [MulAut.conj_apply] using hx, ?_⟩
    simp [MulAut.conj_apply]
    group

theorem cbc_le_or_commute {H X X' : Subgroup (MulAut V)} (hXH : X ≤ H) (hX'H : X' ≤ H)
    (hX : (X.subgroupOf H).IsSubnormal) (hX' : (X'.subgroupOf H).IsSubnormal) {k : ℕ}
    (hk : 5 ≤ k) (θ : ↥X ≃* alternatingGroup (Fin k)) : X ≤ X' ∨ ⁅X, X'⁆ = ⊥ :=
  CFSG.GorensteinWalter.fstar_component_le_or_commutator_eq_bot_of_subnormal_subgroupOf hX'H hX'
    ⟨hXH, hX, cbc_isQuasisimple_alt hk θ⟩

omit [Finite V] in
private theorem cbc_le_of_simple {X X' Y : Subgroup (MulAut V)} (hs : IsSimpleGroup ↥X)
    (hsn : (X'.subgroupOf X).IsSubnormal) (hYX : Y ≤ X) (hYX' : Y ≤ X') (hY : Y ≠ ⊥) :
    X ≤ X' := by
  rcases hsn.eq_bot_or_top_of_isSimpleGroup hs with hbot | htop
  · exfalso
    apply hY
    rw [eq_bot_iff]
    intro y hy
    have h1 : (⟨y, hYX hy⟩ : ↥X) ∈ X'.subgroupOf X := hYX' hy
    rw [hbot, Subgroup.mem_bot] at h1
    exact Subgroup.mem_bot.mpr (congrArg Subtype.val h1)
  · exact Subgroup.subgroupOf_eq_top.mp htop

omit [Finite V] in
theorem cbc_le_of_subnormal_meet {H X X' Y : Subgroup (MulAut V)} (hXH : X ≤ H)
    (hX' : (X'.subgroupOf H).IsSubnormal) {k : ℕ} (hk : 5 ≤ k)
    (θ : ↥X ≃* alternatingGroup (Fin k)) (hYX : Y ≤ X) (hYX' : Y ≤ X') (hY : Y ≠ ⊥) : X ≤ X' :=
  cbc_le_of_simple (cbc_isSimpleGroup_alt hk θ)
    (CFSG.GroupTheory.isSubnormal_subgroupOf_of_le hXH hX') hYX hYX' hY

omit [Finite V] in
theorem cbc_le_of_normalizes {X X' Y : Subgroup (MulAut V)} {k : ℕ} (hk : 5 ≤ k)
    (θ : ↥X ≃* alternatingGroup (Fin k)) (hYX : Y ≤ X) (hYX' : Y ≤ X') (hY : Y ≠ ⊥)
    (hnorm : ∀ x ∈ X, ∀ z ∈ X', x * z * x⁻¹ ∈ X') : X ≤ X' := by
  have hN : (X'.subgroupOf X).Normal := by
    refine ⟨fun n hn g => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    simpa using hnorm g g.2 n hn
  exact cbc_le_of_simple (cbc_isSimpleGroup_alt hk θ) hN.isSubnormal hYX hYX' hY

private theorem cbc_exists_comm_involutions (m : ℕ) (hm : 6 ≤ m) :
    ∃ a₁ a₂ : alternatingGroup (Fin m), a₁ ^ 2 = 1 ∧ a₂ ^ 2 = 1 ∧ a₁ ≠ 1 ∧ a₂ ≠ 1 ∧
      a₁ ≠ a₂ ∧ a₁ * a₂ = a₂ * a₁ := by
  have hcomm : ∀ {a b c d : Fin m}, a ≠ c → a ≠ d → b ≠ c → b ≠ d →
      Commute (swap a b) (swap c d) := by
    intro a b c d hac had hbc hbd
    have : (swap a b).Disjoint (swap c d) := by
      intro x
      by_cases hx : x = a ∨ x = b
      · right
        apply swap_apply_of_ne_of_ne
        · rcases hx with rfl | rfl <;> assumption
        · rcases hx with rfl | rfl <;> assumption
      · left
        simp only [not_or] at hx
        exact swap_apply_of_ne_of_ne hx.1 hx.2
    exact this.commute
  let p : ℕ → Fin m := fun i => if h : i < m then ⟨i, h⟩ else ⟨0, by omega⟩
  have hp : ∀ i j, i < m → j < m → i ≠ j → p i ≠ p j := fun i j hi hj hij h => by
    simp only [p, hi, hj, dite_true, Fin.mk.injEq] at h
    exact hij h
  have h01 := hp 0 1 (by omega) (by omega) (by omega)
  have h23 := hp 2 3 (by omega) (by omega) (by omega)
  have h45 := hp 4 5 (by omega) (by omega) (by omega)
  have hsq : ∀ {a b : Fin m}, a ≠ b → swap a b * swap a b = 1 := fun _ => swap_mul_self _ _
  have c01_23 := hcomm (a := p 0) (b := p 1) (c := p 2) (d := p 3) (hp 0 2 (by omega) (by omega)
    (by omega)) (hp 0 3 (by omega) (by omega) (by omega)) (hp 1 2 (by omega) (by omega) (by omega))
    (hp 1 3 (by omega) (by omega) (by omega))
  have c01_45 := hcomm (a := p 0) (b := p 1) (c := p 4) (d := p 5) (hp 0 4 (by omega) (by omega)
    (by omega)) (hp 0 5 (by omega) (by omega) (by omega)) (hp 1 4 (by omega) (by omega) (by omega))
    (hp 1 5 (by omega) (by omega) (by omega))
  have c23_45 := hcomm (a := p 2) (b := p 3) (c := p 4) (d := p 5) (hp 2 4 (by omega) (by omega)
    (by omega)) (hp 2 5 (by omega) (by omega) (by omega)) (hp 3 4 (by omega) (by omega) (by omega))
    (hp 3 5 (by omega) (by omega) (by omega))
  have mem1 : swap (p 0) (p 1) * swap (p 2) (p 3) ∈ alternatingGroup (Fin m) := by
    rw [Equiv.Perm.mem_alternatingGroup, map_mul, Equiv.Perm.sign_swap h01,
      Equiv.Perm.sign_swap h23]
    decide
  have mem2 : swap (p 0) (p 1) * swap (p 4) (p 5) ∈ alternatingGroup (Fin m) := by
    rw [Equiv.Perm.mem_alternatingGroup, map_mul, Equiv.Perm.sign_swap h01,
      Equiv.Perm.sign_swap h45]
    decide
  refine ⟨⟨_, mem1⟩, ⟨_, mem2⟩, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · apply Subtype.ext
    show (swap (p 0) (p 1) * swap (p 2) (p 3)) ^ 2 = 1
    rw [c01_23.mul_pow, pow_two, pow_two, hsq h01, hsq h23, mul_one]
  · apply Subtype.ext
    show (swap (p 0) (p 1) * swap (p 4) (p 5)) ^ 2 = 1
    rw [c01_45.mul_pow, pow_two, pow_two, hsq h01, hsq h45, mul_one]
  · intro h
    have := congrArg (fun f : alternatingGroup (Fin m) => (f : Perm (Fin m)) (p 0)) h
    simp only [Perm.mul_apply, OneMemClass.coe_one, Perm.coe_one, id_eq] at this
    rw [swap_apply_of_ne_of_ne (hp 0 2 (by omega) (by omega) (by omega))
      (hp 0 3 (by omega) (by omega) (by omega)), swap_apply_left] at this
    exact h01 this.symm
  · intro h
    have := congrArg (fun f : alternatingGroup (Fin m) => (f : Perm (Fin m)) (p 0)) h
    simp only [Perm.mul_apply, OneMemClass.coe_one, Perm.coe_one, id_eq] at this
    rw [swap_apply_of_ne_of_ne (hp 0 4 (by omega) (by omega) (by omega))
      (hp 0 5 (by omega) (by omega) (by omega)), swap_apply_left] at this
    exact h01 this.symm
  · intro h
    have := congrArg (fun f : alternatingGroup (Fin m) => (f : Perm (Fin m)) (p 2)) h
    simp only [Perm.mul_apply] at this
    rw [swap_apply_left, swap_apply_of_ne_of_ne (hp 2 4 (by omega) (by omega) (by omega))
      (hp 2 5 (by omega) (by omega) (by omega)),
      swap_apply_of_ne_of_ne (hp 2 0 (by omega) (by omega) (by omega))
        (hp 2 1 (by omega) (by omega) (by omega)),
      swap_apply_of_ne_of_ne (hp 3 0 (by omega) (by omega) (by omega))
        (hp 3 1 (by omega) (by omega) (by omega))] at this
    exact h23.symm this
  · apply Subtype.ext
    show (swap (p 0) (p 1) * swap (p 2) (p 3)) * (swap (p 0) (p 1) * swap (p 4) (p 5)) =
      (swap (p 0) (p 1) * swap (p 4) (p 5)) * (swap (p 0) (p 1) * swap (p 2) (p 3))
    exact ((Commute.refl (swap (p 0) (p 1))).mul_right c01_45 |>.mul_left
      (c01_23.symm.mul_right c23_45 |>.symm.symm)).eq

omit [Finite V] in
private theorem cbc_exists_comm_in {Z : Subgroup (MulAut V)} {k : ℕ} (hk : 6 ≤ k)
    (θ : ↥Z ≃* alternatingGroup (Fin k)) :
    ∃ z₁ z₂ : MulAut V, z₁ ∈ Z ∧ z₂ ∈ Z ∧ z₁ ^ 2 = 1 ∧ z₂ ^ 2 = 1 ∧ z₁ ≠ 1 ∧ z₂ ≠ 1 ∧
      z₁ ≠ z₂ ∧ z₁ * z₂ = z₂ * z₁ := by
  obtain ⟨a₁, a₂, ha1, ha2, ha1n, ha2n, ha12, hac⟩ := cbc_exists_comm_involutions k hk
  have hsq : ∀ a : alternatingGroup (Fin k), a ^ 2 = 1 →
      ((θ.symm a : ↥Z) : MulAut V) ^ 2 = 1 := by
    intro a ha
    rw [← Subgroup.coe_pow, ← map_pow, ha, map_one, Subgroup.coe_one]
  have hne : ∀ a : alternatingGroup (Fin k), a ≠ 1 → ((θ.symm a : ↥Z) : MulAut V) ≠ 1 := by
    intro a ha hz
    apply ha
    have : θ.symm a = 1 := Subtype.ext (by simpa using hz)
    simpa using this
  refine ⟨θ.symm a₁, θ.symm a₂, (θ.symm a₁).2, (θ.symm a₂).2, hsq a₁ ha1, hsq a₂ ha2,
    hne a₁ ha1n, hne a₂ ha2n, fun hh => ha12 ?_, ?_⟩
  · exact θ.symm.injective (Subtype.ext hh)
  · have : θ.symm a₁ * θ.symm a₂ = θ.symm a₂ * θ.symm a₁ := by
      rw [← map_mul, ← map_mul, hac]
    exact congrArg Subtype.val this

theorem EndCfg4.not_alt_le_centralizer {G T Y : Subgroup (MulAut V)} (h2 : Alt2Rank1)
    (h : EndCfg4 G T Y) (hV : ∀ v : V, v ^ 2 = 1) {m : ℕ} (hm : 7 ≤ m) (hodd : Odd m)
    (hY : YAlt Y m) {Z : Subgroup (MulAut V)} {k : ℕ} (hk : 6 ≤ k)
    (θ : ↥Z ≃* alternatingGroup (Fin k)) (hZG : Z ≤ G) (hZC : ∀ z ∈ Z, ∀ y ∈ Y, z * y = y * z) :
    False := by
  obtain ⟨z₁, z₂, hz₁, hz₂, hs₁, hs₂, h1, h1', h12, hc⟩ := cbc_exists_comm_in hk θ
  exact h2 V hV G T Y h m hm hodd hY z₁ z₂ (hZG hz₁) (hZG hz₂)
    (Subgroup.mem_centralizer_iff.mpr fun y hy => (hZC z₁ hz₁ y hy).symm)
    (Subgroup.mem_centralizer_iff.mpr fun y hy => (hZC z₂ hz₂ y hy).symm) hs₁ hs₂ h1 h1' h12 hc

omit [Finite V] in
private theorem cbc_eq_one_of_central {Y : Subgroup (MulAut V)} {m : ℕ} (hm : 5 ≤ m)
    (θ : ↥Y ≃* alternatingGroup (Fin m)) {y : MulAut V} (hy : y ∈ Y)
    (hc : ∀ y' ∈ Y, y' * y = y * y') : y = 1 := by
  have hcen : Subgroup.center (alternatingGroup (Fin m)) = ⊥ :=
    alternatingGroup.center_eq_bot (by simpa using (by omega : 4 ≤ m))
  have hmem : θ ⟨y, hy⟩ ∈ Subgroup.center (alternatingGroup (Fin m)) := by
    rw [Subgroup.mem_center_iff]
    intro b
    obtain ⟨y', rfl⟩ := θ.surjective b
    rw [← map_mul, ← map_mul]
    exact congrArg θ (Subtype.ext (hc y' y'.2))
  rw [hcen, Subgroup.mem_bot] at hmem
  have h1 : (⟨y, hy⟩ : ↥Y) = 1 := θ.injective (by rw [hmem, map_one])
  exact congrArg Subtype.val h1

omit [Finite V] in
private theorem cbc_centralizes_of_inner {Y : Subgroup (MulAut V)} {z y : MulAut V} (hy : y ∈ Y)
    (h : ∀ y' ∈ Y, z * y' * z⁻¹ = y * y' * y⁻¹) :
    ∀ y' ∈ Y, y' * (z * y⁻¹) = (z * y⁻¹) * y' := by
  intro y' hy'
  have h5 := h (y⁻¹ * y' * y) (Y.mul_mem (Y.mul_mem (Y.inv_mem hy) hy') hy)
  have h6 : y * (y⁻¹ * y' * y) * y⁻¹ = y' := by group
  rw [h6] at h5
  calc y' * (z * y⁻¹) = (z * (y⁻¹ * y' * y) * z⁻¹) * (z * y⁻¹) := by rw [h5]
    _ = (z * y⁻¹) * y' := by group

omit [Finite V] in
private theorem cbc_exists_inner {Y Z : Subgroup (MulAut V)} {m : ℕ} (hm : 7 ≤ m)
    (θ : ↥Y ≃* alternatingGroup (Fin m)) (hperf : commutator ↥Z = ⊤)
    (hZN : ∀ z ∈ Z, ∀ y ∈ Y, z * y * z⁻¹ ∈ Y) {z : MulAut V} (hz : z ∈ Z) :
    ∃ y ∈ Y, ∀ y' ∈ Y, y' * (z * y⁻¹) = (z * y⁻¹) * y' := by
  have hZle : Z ≤ Subgroup.normalizer (Y : Set (MulAut V)) := by
    intro w hw
    rw [Subgroup.mem_normalizer_iff]
    intro y
    refine ⟨fun hy => hZN w hw y hy, fun hy => ?_⟩
    have := hZN w⁻¹ (Z.inv_mem hw) _ hy
    simpa [mul_assoc] using this
  obtain ⟨c, hc⟩ : ∃ c : Perm (Fin m) ≃* MulAut (alternatingGroup (Fin m)),
      ∀ (σ : Perm (Fin m)) (a : alternatingGroup (Fin m)),
        ((c σ a : alternatingGroup (Fin m)) : Perm (Fin m)) = σ * a * σ⁻¹ :=
    ⟨MulEquiv.ofBijective (MulAut.conjNormal (H := alternatingGroup (Fin m)))
      (CFSG.GroupTheory.AutAlternating.aut_alternatingGroup_bijective_conj m (by omega)
        (by omega)), fun σ a => by simp⟩
  let ρ : ↥Z →* Perm (Fin m) := c.symm.toMonoidHom.comp ((MulAut.congr θ).toMonoidHom.comp
    (Y.normalizerMonoidHom.comp (Subgroup.inclusion hZle)))
  have hcw : ∀ w : ↥Z, c (ρ w) =
      MulAut.congr θ (Y.normalizerMonoidHom (Subgroup.inclusion hZle w)) :=
    fun w => c.apply_symm_apply _
  have hcρ : ∀ (w : ↥Z) (y' : ↥Y),
      ((θ ⟨(w : MulAut V) * y' * (w : MulAut V)⁻¹, hZN w w.2 y' y'.2⟩ :
        alternatingGroup (Fin m)) : Perm (Fin m)) =
        ρ w * (θ y' : Perm (Fin m)) * (ρ w)⁻¹ := by
    intro w y'
    rw [← hc (ρ w) (θ y'), hcw w]
    simp only [MulAut.congr_apply]
    exact congrArg (fun u : ↥Y => ((θ u : alternatingGroup (Fin m)) : Perm (Fin m)))
      (Subtype.ext (by simp))
  have hsgn : Equiv.Perm.sign (ρ ⟨z, hz⟩) = 1 := by
    have h1 := Abelianization.commutator_subset_ker
      ((Equiv.Perm.sign : Perm (Fin m) →* ℤˣ).comp ρ)
    rw [hperf] at h1
    simpa using h1 (Subgroup.mem_top (⟨z, hz⟩ : ↥Z))
  have hmem : ρ ⟨z, hz⟩ ∈ alternatingGroup (Fin m) := Perm.mem_alternatingGroup.mpr hsgn
  have hinner : ∀ y' ∈ Y, z * y' * z⁻¹ = ((θ.symm ⟨ρ ⟨z, hz⟩, hmem⟩ : ↥Y) : MulAut V) * y' *
      ((θ.symm ⟨ρ ⟨z, hz⟩, hmem⟩ : ↥Y) : MulAut V)⁻¹ := by
    intro y' hy'
    have h1 := hcρ ⟨z, hz⟩ ⟨y', hy'⟩
    have h3 : (⟨z * y' * z⁻¹, hZN z hz y' hy'⟩ : ↥Y) =
        θ.symm ⟨ρ ⟨z, hz⟩, hmem⟩ * ⟨y', hy'⟩ * (θ.symm ⟨ρ ⟨z, hz⟩, hmem⟩)⁻¹ := by
      apply θ.injective
      rw [map_mul, map_mul, map_inv, θ.apply_symm_apply]
      apply Subtype.ext
      simpa using h1
    exact congrArg Subtype.val h3
  exact ⟨_, (θ.symm _).2, cbc_centralizes_of_inner (θ.symm _).2 hinner⟩

omit [Finite V] in
private theorem cbc_sq_eq_one {Y : Subgroup (MulAut V)} {m : ℕ} (hm : 5 ≤ m)
    (θ : ↥Y ≃* alternatingGroup (Fin m)) {z y : MulAut V} (hy : y ∈ Y) (hz : z ^ 2 = 1)
    (hd : ∀ y' ∈ Y, y' * (z * y⁻¹) = (z * y⁻¹) * y') : (z * y⁻¹) ^ 2 = 1 := by
  have hyd : y * (z * y⁻¹) = (z * y⁻¹) * y := hd y hy
  have key : (z * y⁻¹) ^ 2 = (y * y)⁻¹ := by
    refine eq_inv_of_mul_eq_one_left ?_
    calc (z * y⁻¹) ^ 2 * (y * y) = (z * y⁻¹) * ((z * y⁻¹) * y) * y := by rw [pow_two]; group
      _ = (z * y⁻¹) * (y * (z * y⁻¹)) * y := by rw [hyd]
      _ = z ^ 2 := by rw [pow_two]; group
      _ = 1 := hz
  refine cbc_eq_one_of_central hm θ (by rw [key]; exact Y.inv_mem (Y.mul_mem hy hy)) ?_
  intro y' hy'
  exact (Commute.pow_right (show Commute y' (z * y⁻¹) from hd y' hy') 2).eq

omit [Finite V] in
private theorem cbc_meet_of_commuting {G Y Z : Subgroup (MulAut V)} {m : ℕ} (hm : 5 ≤ m)
    (θ : ↥Y ≃* alternatingGroup (Fin m)) (hYG : Y ≤ G) (hZG : Z ≤ G)
    (hno : ∀ a b : MulAut V, a ∈ G → b ∈ G → (∀ y ∈ Y, y * a = a * y) →
      (∀ y ∈ Y, y * b = b * y) → a ^ 2 = 1 → b ^ 2 = 1 → a ≠ 1 → b ≠ 1 → a ≠ b →
      a * b = b * a → False)
    {z₁ z₂ y₁ y₂ : MulAut V} (hz₁ : z₁ ∈ Z) (hz₂ : z₂ ∈ Z) (hy₁ : y₁ ∈ Y) (hy₂ : y₂ ∈ Y)
    (hd₁ : ∀ y ∈ Y, y * (z₁ * y₁⁻¹) = (z₁ * y₁⁻¹) * y)
    (hd₂ : ∀ y ∈ Y, y * (z₂ * y₂⁻¹) = (z₂ * y₂⁻¹) * y)
    (hs₁ : z₁ ^ 2 = 1) (hs₂ : z₂ ^ 2 = 1) (h1 : z₁ ≠ 1) (h2 : z₂ ≠ 1) (h12 : z₁ ≠ z₂)
    (hc : z₁ * z₂ = z₂ * z₁) : ∃ w ∈ Z ⊓ Y, w ≠ 1 := by
  have hsq₁ := cbc_sq_eq_one hm θ hy₁ hs₁ hd₁
  have hsq₂ := cbc_sq_eq_one hm θ hy₂ hs₂ hd₂
  have hdG₁ : z₁ * y₁⁻¹ ∈ G := G.mul_mem (hZG hz₁) (G.inv_mem (hYG hy₁))
  have hdG₂ : z₂ * y₂⁻¹ ∈ G := G.mul_mem (hZG hz₂) (G.inv_mem (hYG hy₂))
  have hdC₁ : z₁ * y₁⁻¹ ∈ Subgroup.centralizer (Y : Set (MulAut V)) :=
    Subgroup.mem_centralizer_iff.mpr hd₁
  have hdC₂ : z₂ * y₂⁻¹ ∈ Subgroup.centralizer (Y : Set (MulAut V)) :=
    Subgroup.mem_centralizer_iff.mpr hd₂
  have hz1 : z₁ = (z₁ * y₁⁻¹) * y₁ := by simp
  have hz2 : z₂ = (z₂ * y₂⁻¹) * y₂ := by simp
  have P1 : y₁ * (z₂ * y₂⁻¹) = (z₂ * y₂⁻¹) * y₁ := hd₂ y₁ hy₁
  have P2 : y₂ * (z₁ * y₁⁻¹) = (z₁ * y₁⁻¹) * y₂ := hd₁ y₂ hy₂
  generalize z₁ * y₁⁻¹ = d₁ at *
  generalize z₂ * y₂⁻¹ = d₂ at *
  have e1 : z₁ * z₂ = d₁ * d₂ * (y₁ * y₂) := by
    calc z₁ * z₂ = d₁ * (y₁ * d₂) * y₂ := by rw [hz1, hz2]; group
      _ = d₁ * (d₂ * y₁) * y₂ := by rw [P1]
      _ = d₁ * d₂ * (y₁ * y₂) := by group
  have e2 : z₂ * z₁ = d₂ * d₁ * (y₂ * y₁) := by
    calc z₂ * z₁ = d₂ * (y₂ * d₁) * y₁ := by rw [hz1, hz2]; group
      _ = d₂ * (d₁ * y₂) * y₁ := by rw [P2]
      _ = d₂ * d₁ * (y₂ * y₁) := by group
  have e3 : d₁ * d₂ * (y₁ * y₂) = d₂ * d₁ * (y₂ * y₁) := by rw [← e1, ← e2]; exact hc
  have e4 : (d₂ * d₁)⁻¹ * (d₁ * d₂) = (y₂ * y₁) * (y₁ * y₂)⁻¹ := by
    rw [inv_mul_eq_iff_eq_mul]
    calc d₁ * d₂ = d₁ * d₂ * (y₁ * y₂) * (y₁ * y₂)⁻¹ := by group
      _ = d₂ * d₁ * (y₂ * y₁) * (y₁ * y₂)⁻¹ := by rw [e3]
      _ = d₂ * d₁ * ((y₂ * y₁) * (y₁ * y₂)⁻¹) := by group
  have hu : (d₂ * d₁)⁻¹ * (d₁ * d₂) = 1 := by
    have hmem : (d₂ * d₁)⁻¹ * (d₁ * d₂) ∈ Subgroup.centralizer (Y : Set (MulAut V)) :=
      mul_mem (inv_mem (mul_mem hdC₂ hdC₁)) (mul_mem hdC₁ hdC₂)
    refine cbc_eq_one_of_central hm θ ?_ (Subgroup.mem_centralizer_iff.mp hmem)
    rw [e4]
    exact Y.mul_mem (Y.mul_mem hy₂ hy₁) (Y.inv_mem (Y.mul_mem hy₁ hy₂))
  have hcomm : d₁ * d₂ = d₂ * d₁ := (inv_mul_eq_one.mp hu).symm
  by_cases hd1 : d₁ = 1
  · refine ⟨z₁, ⟨hz₁, ?_⟩, h1⟩
    rw [hz1, hd1, one_mul]
    exact hy₁
  by_cases hd2 : d₂ = 1
  · refine ⟨z₂, ⟨hz₂, ?_⟩, h2⟩
    rw [hz2, hd2, one_mul]
    exact hy₂
  by_cases hd12 : d₁ = d₂
  · refine ⟨z₁ * z₂, ⟨Z.mul_mem hz₁ hz₂, ?_⟩, fun h => h12 ?_⟩
    · rw [e1, ← hd12, ← pow_two, hsq₁, one_mul]
      exact Y.mul_mem hy₁ hy₂
    · rw [eq_inv_of_mul_eq_one_left h]
      exact inv_eq_of_mul_eq_one_right (by rw [← pow_two]; exact hs₂)
  exact (hno d₁ d₂ hdG₁ hdG₂ hd₁ hd₂ hsq₁ hsq₂ hd1 hd2 hd12 hcomm).elim

theorem EndCfg4.eq_of_alt_le_normalizer {G T Y : Subgroup (MulAut V)} (h2 : Alt2Rank1)
    (h : EndCfg4 G T Y) (hV : ∀ v : V, v ^ 2 = 1) {m : ℕ} (hm : 7 ≤ m) (hodd : Odd m)
    (hY : YAlt Y m) {Z : Subgroup (MulAut V)} (hZ : Nonempty (↥Z ≃* alternatingGroup (Fin m)))
    (hZG : Z ≤ G) (hZN : ∀ z ∈ Z, ∀ y ∈ Y, z * y * z⁻¹ ∈ Y) : Z = Y := by
  obtain ⟨e⟩ := hZ
  obtain ⟨θ⟩ := id hY
  have hYG : Y ≤ G := fun y hy => (h.adm.hYC hy).1
  have h5 : 5 ≤ m := by omega
  have hperf : commutator ↥Z = ⊤ := (cbc_isQuasisimple_alt h5 e).2.1
  have hno : ∀ a b : MulAut V, a ∈ G → b ∈ G → (∀ y ∈ Y, y * a = a * y) →
      (∀ y ∈ Y, y * b = b * y) → a ^ 2 = 1 → b ^ 2 = 1 → a ≠ 1 → b ≠ 1 → a ≠ b →
      a * b = b * a → False := fun a b ha hb hca hcb ha2 hb2 ha1 hb1 hab hba =>
    h2 V hV G T Y h m hm hodd hY a b ha hb (Subgroup.mem_centralizer_iff.mpr hca)
      (Subgroup.mem_centralizer_iff.mpr hcb) ha2 hb2 ha1 hb1 hab hba
  obtain ⟨z₁, z₂, hz₁, hz₂, hs₁, hs₂, h1, h1', h12, hc⟩ := cbc_exists_comm_in (by omega) e
  obtain ⟨y₁, hy₁, hd₁⟩ := cbc_exists_inner hm θ hperf hZN hz₁
  obtain ⟨y₂, hy₂, hd₂⟩ := cbc_exists_inner hm θ hperf hZN hz₂
  obtain ⟨w, hw, hw1⟩ :=
    cbc_meet_of_commuting h5 θ hYG hZG hno hz₁ hz₂ hy₁ hy₂ hd₁ hd₂ hs₁ hs₂ h1 h1' h12 hc
  have hmeet : Z ⊓ Y ≠ ⊥ := fun hb => hw1 (Subgroup.mem_bot.mp (hb ▸ hw))
  have hle : Z ≤ Y := cbc_le_of_normalizes h5 e inf_le_left inf_le_right hmeet hZN
  refine Subgroup.eq_of_le_of_card_ge hle ?_
  rw [Nat.card_congr e.toEquiv, Nat.card_congr θ.toEquiv]

end CFSG.CGT.PushingUpLit.CGT6
