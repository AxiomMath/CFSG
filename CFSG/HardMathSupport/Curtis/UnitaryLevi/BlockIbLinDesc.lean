module

public import CFSG.HardMathSupport.Curtis.UnitaryLevi.BlockIbLinTransport
public import CFSG.HardMathSupport.Curtis.UnitaryLevi.LiftAbstract
public import CFSG.HardMathSupport.Curtis.UnitaryLevi.OutRankY

public section

namespace CFSG.HardMathSupport.Curtis.UnitaryLevi

open scoped commutatorElement

section Desc

variable {Y : Type} [Group Y] {Lb Pb D : Subgroup Y} {X : Type} [Group X]

theorem descendHom_apply_psi (e : ↥Lb ⧸ Subgroup.center ↥Lb ≃* X) (y : Y)
    (hy : y ∈ Subgroup.normalizer (Lb : Set Y)) (l : ↥Lb) :
    descendAut e y hy (centralQuotientHom e l) = centralQuotientHom e (conjL y hy l) :=
  descendAut_apply e y hy l

theorem descendAut_map_eq (e : ↥Lb ⧸ Subgroup.center ↥Lb ≃* X) {y : Y}
    (hy : y ∈ Subgroup.normalizer (Lb : Set Y)) (hyP : y ∈ Subgroup.normalizer (Pb : Set Y)) :
    ((Pb.subgroupOf Lb).map (centralQuotientHom e)).map (descendAut e y hy).toMonoidHom =
      (Pb.subgroupOf Lb).map (centralQuotientHom e) := by
  apply le_antisymm
  · rintro _ ⟨_, ⟨l, hl, rfl⟩, rfl⟩
    refine ⟨conjL y hy l, ?_, ?_⟩
    · have : y * (l : Y) * y⁻¹ ∈ Pb := (Subgroup.mem_normalizer_iff.1 hyP _).1 hl
      exact this
    · exact (descendHom_apply_psi e y hy l).symm
  · intro j hj
    obtain ⟨l, hl, rfl⟩ := hj
    have hyi : y⁻¹ ∈ Subgroup.normalizer (Lb : Set Y) := inv_mem hy
    have hyiP : y⁻¹ ∈ Subgroup.normalizer (Pb : Set Y) := inv_mem hyP
    refine ⟨_, ⟨conjL y⁻¹ hyi l, ?_, rfl⟩, ?_⟩
    · have : y⁻¹ * (l : Y) * y⁻¹⁻¹ ∈ Pb := (Subgroup.mem_normalizer_iff.1 hyiP _).1 hl
      exact this
    · rw [MulEquiv.coe_toMonoidHom, descendHom_apply_psi]
      congr 1
      ext
      simp [mul_assoc]

theorem mem_centralizer_of_descendAut_eq_one [Group.IsPerfect ↥Lb]
    (e : ↥Lb ⧸ Subgroup.center ↥Lb ≃* X) {y : Y} (hy : y ∈ Subgroup.normalizer (Lb : Set Y))
    (h : descendAut e y hy = 1) : y ∈ Subgroup.centralizer (Lb : Set Y) := by
  have := inv_mul_mem_centralizer_of_descendAut_eq_conj e hy 1 (by
    rw [h]; simp)
  simpa using this

end Desc

section BarD

variable {Y : Type} [Group Y] {Lb Pb D : Subgroup Y} {X : Type} [Group X]

@[expose] def barD (D : Subgroup Y) (hPL : Pb ≤ Lb) (e : ↥Lb ⧸ Subgroup.center ↥Lb ≃* X) :
    Subgroup X :=
  ((Lift.actD Lb Pb D hPL).subgroupOf Lb).map (centralQuotientHom e)

theorem barD_le (hPL : Pb ≤ Lb) (e : ↥Lb ⧸ Subgroup.center ↥Lb ≃* X) :
    barD D hPL e ≤ (Pb.subgroupOf Lb).map (centralQuotientHom e) := by
  rintro _ ⟨l, hl, rfl⟩
  exact ⟨l, (show (l : Y) ∈ Lift.actD Lb Pb D hPL from hl).1, rfl⟩

theorem psi_eq_of_inv_mul_mem (e : ↥Lb ⧸ Subgroup.center ↥Lb ≃* X) {l l' : ↥Lb}
    (h : (l : Y)⁻¹ * (l' : Y) ∈ Lift.ZL Lb) :
    centralQuotientHom e l = centralQuotientHom e l' := by
  have hc : l⁻¹ * l' ∈ Subgroup.center ↥Lb := by
    rw [Subgroup.mem_center_iff]
    intro g
    obtain ⟨-, hz⟩ := Lift.mem_ZL.1 h
    exact Subtype.ext (by simpa [mul_assoc] using hz g g.2)
  have h1 : centralQuotientHom e (l⁻¹ * l') = 1 := by
    have : l⁻¹ * l' ∈ (centralQuotientHom e).ker := by rw [centralQuotientHom_ker e]; exact hc
    exact this
  rw [map_mul, map_inv, inv_mul_eq_one] at h1
  exact h1

theorem barD_perfect (hPL : Pb ≤ Lb) (hDperf : ⁅D, D⁆ = D)
    (hDle : D ≤ Pb ⊔ Subgroup.centralizer (Lb : Set Y)) (e : ↥Lb ⧸ Subgroup.center ↥Lb ≃* X) :
    ⁅barD D hPL e, barD D hPL e⁆ = barD D hPL e := by
  set D₁ : Subgroup ↥Lb := (Lift.actD Lb Pb D hPL).subgroupOf Lb with hD₁
  have hsub : D₁.map Lb.subtype = Lift.actD Lb Pb D hPL := by
    rw [hD₁, Subgroup.subgroupOf_map_subtype, inf_eq_left]; exact fun p hp => hPL hp.1
  rw [barD, ← hD₁, ← Subgroup.map_commutator]
  apply le_antisymm
  · exact Subgroup.map_mono (Lift.commutator_le_self' _)
  · rintro _ ⟨l, hl, rfl⟩
    obtain ⟨p', hp', hz⟩ := Lift.exists_mem_commutator_actD hPL hDperf hDle
      (show (l : Y) ∈ Lift.actD Lb Pb D hPL from hl)
    have : ⁅Lift.actD Lb Pb D hPL, Lift.actD Lb Pb D hPL⁆ = (⁅D₁, D₁⁆).map Lb.subtype := by
      rw [Subgroup.map_commutator, hsub]
    rw [this] at hp'
    obtain ⟨l', hl', rfl⟩ := hp'
    exact ⟨l', hl', (psi_eq_of_inv_mul_mem e hz).symm⟩

theorem descendAut_fixes_barD (hPL : Pb ≤ Lb) (e : ↥Lb ⧸ Subgroup.center ↥Lb ≃* X) {y : Y}
    (hy : y ∈ Subgroup.normalizer (Lb : Set Y)) (hyD : y ∈ Subgroup.centralizer (D : Set Y)) :
    ∀ j ∈ barD D hPL e, descendAut e y hy j = j := by
  rintro _ ⟨l, hl, rfl⟩
  obtain ⟨hlP, y', hy'D, hAct⟩ := (show (l : Y) ∈ Lift.actD Lb Pb D hPL from hl)
  rw [descendHom_apply_psi]
  have hyi : ∀ m ∈ Lb, y⁻¹ * m * y ∈ Lb := fun m hm => by
    have := (Subgroup.mem_normalizer_iff.1 (inv_mem hy) m).1 hm
    simpa using this
  have hyu : y' * y = y * y' := Subgroup.mem_centralizer_iff.1 hyD y' hy'D
  have hAct' : Lift.Act Lb y' (y * (l : Y) * y⁻¹) := by
    intro m hm
    have h1 := hAct (y⁻¹ * m * y) (hyi m hm)
    have hy'' : y * y' * y⁻¹ = y' := by rw [← hyu]; group
    calc y' * m * y'⁻¹ = (y * y' * y⁻¹) * m * (y * y' * y⁻¹)⁻¹ := by rw [hy'']
      _ = y * (y' * (y⁻¹ * m * y) * y'⁻¹) * y⁻¹ := by group
      _ = y * ((l : Y) * (y⁻¹ * m * y) * (l : Y)⁻¹) * y⁻¹ := by rw [h1]
      _ = (y * (l : Y) * y⁻¹) * m * (y * (l : Y) * y⁻¹)⁻¹ := by group
  have hz := Lift.act_comm l.2 (conjL y hy l).2 hAct hAct'
  exact (psi_eq_of_inv_mul_mem e hz).symm

end BarD

section Order

variable {Y : Type} [Group Y] [Finite Y]

theorem mem_zpowers_of_cyclic_three_group {A : Subgroup Y} [IsCyclic A] (hA : IsPGroup 3 A) {x y : Y}
    (hx : x ∈ A) (hxo : orderOf x = 3) (hy : y ∈ A) (hy1 : y ≠ 1) : x ∈ Subgroup.zpowers y := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let xA : A := ⟨x, hx⟩
  let yA : A := ⟨y, hy⟩
  have hxA : orderOf xA = 3 := by rw [← Subgroup.orderOf_coe]; exact hxo
  have hyA1 : yA ≠ 1 := fun h => hy1 (congrArg Subtype.val h)
  obtain ⟨j, hj⟩ := (IsPGroup.iff_orderOf.1 hA) yA
  have hj1 : 1 ≤ j := by
    rcases Nat.eq_zero_or_pos j with h0 | h0
    · rw [h0, pow_zero] at hj; exact absurd (orderOf_eq_one_iff.1 hj) hyA1
    · exact h0
  have hdvd : Nat.card (Subgroup.zpowers xA) ∣ Nat.card (Subgroup.zpowers yA) := by
    rw [Nat.card_zpowers, Nat.card_zpowers, hxA, hj]
    exact dvd_pow_self 3 (by omega)
  have hle : Subgroup.zpowers xA ≤ Subgroup.zpowers yA :=
    IsCyclic.subgroup_le_iff_card_dvd.2 hdvd
  have := hle (Subgroup.mem_zpowers xA)
  obtain ⟨n, hn⟩ := this
  refine ⟨n, ?_⟩
  have := congrArg Subtype.val hn
  simpa using this

theorem exists_elt_of_dvd {D : Subgroup Y}
    (Dcyc : ∀ A : Subgroup Y, A ≤ D → IsPGroup 3 A → IsCyclic A) {x : Y} (hxD : x ∈ D)
    (hx3 : x ^ 3 = 1) (hx1 : x ≠ 1) {k : ℕ} (hk : 1 ≤ k) (hdvd : 3 ^ k ∣ Nat.card D) :
    ∃ A : Subgroup Y, A ≤ D ∧ IsPGroup 3 A ∧ IsCyclic A ∧ x ∈ A ∧
      ∃ d ∈ A, orderOf d = 3 ^ k := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  classical
  let xD : D := ⟨x, hxD⟩
  have hxoD : orderOf xD = 3 := by
    rw [← Subgroup.orderOf_coe]
    exact orderOf_eq_prime hx3 hx1
  have hpx : IsPGroup 3 (Subgroup.zpowers xD) := by
    rw [IsPGroup.iff_card]
    refine ⟨1, ?_⟩
    rw [Nat.card_zpowers, hxoD]; norm_num
  obtain ⟨P, hP⟩ := hpx.exists_le_sylow
  set A : Subgroup Y := (P : Subgroup D).map D.subtype with hA
  have hAD : A ≤ D := by rintro _ ⟨a, -, rfl⟩; exact a.2
  have hAp : IsPGroup 3 A := (P.isPGroup').map D.subtype
  have hAc : IsCyclic A := Dcyc A hAD hAp
  have hxA : x ∈ A := ⟨xD, hP (Subgroup.mem_zpowers xD), rfl⟩
  refine ⟨A, hAD, hAp, hAc, hxA, ?_⟩
  have hcardA : Nat.card A = Nat.card P := by
    rw [hA]
    exact (Nat.card_congr (Subgroup.equivMapOfInjective _ D.subtype D.subtype_injective).toEquiv).symm
  have hPcard := P.card_eq_multiplicity
  obtain ⟨m, hm⟩ : ∃ m, Nat.card A = 3 ^ m := ⟨_, hcardA.trans hPcard⟩
  have hkm : k ≤ m := by
    have h1 : 3 ^ k ∣ Nat.card P := by
      rw [hPcard]
      have := (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_three
        (Nat.card_pos (α := D)).ne').1 hdvd
      exact pow_dvd_pow 3 this
    rw [← hcardA, hm] at h1
    exact (Nat.pow_dvd_pow_iff_le_right (by norm_num)).1 h1
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := A)
  have hgo : orderOf g = 3 ^ m := by rw [orderOf_eq_card_of_forall_mem_zpowers hg, hm]
  refine ⟨((g ^ 3 ^ (m - k) : A) : Y), (g ^ 3 ^ (m - k)).2, ?_⟩
  rw [Subgroup.orderOf_coe, orderOf_pow_of_dvd (by positivity) (by rw [hgo]; exact pow_dvd_pow 3 (by omega)), hgo]
  rw [Nat.pow_div (by omega) (by norm_num)]
  congr 1
  omega

end Order

section Carry

variable {Y : Type} [Group Y] [Finite Y] {Lb Pb D : Subgroup Y} {x : Y} {X : Type} [Group X]

theorem center_le_parab (hP : BlockIbParab Lb Pb) {z : ↥Lb} (hz : z ∈ Subgroup.center ↥Lb) :
    (z : Y) ∈ Pb := by
  obtain ⟨-, T, ⟨hTL, -, -⟩, hNJ⟩ := hP.parab
  refine hNJ ⟨z.2, ?_⟩
  show (z : Y) ∈ Subgroup.normalizer (T : Set Y)
  rw [Subgroup.mem_normalizer_iff]
  intro h
  have hc : ∀ t ∈ Lb, (z : Y) * t * (z : Y)⁻¹ = t := fun t ht => by
    have := Subgroup.mem_center_iff.1 hz ⟨t, ht⟩
    have h2 : (z : Y) * t = t * z := (congrArg Subtype.val this).symm
    rw [h2]; group
  by_cases hh : h ∈ Lb
  · rw [hc h hh]
  · constructor
    · intro hT; exact absurd (hTL hT) hh
    · intro hT
      exfalso
      apply hh
      have h1 : (z : Y)⁻¹ * ((z : Y) * h * (z : Y)⁻¹) * (z : Y) ∈ Lb :=
        Lb.mul_mem (Lb.mul_mem (Lb.inv_mem z.2) (hTL hT)) z.2
      simpa [mul_assoc] using h1

theorem exists_barD_order (hP : BlockIbParab Lb Pb) (hD : BlockIbData Lb Pb D x)
    (e : ↥Lb ⧸ Subgroup.center ↥Lb ≃* X) {k : ℕ} (hk : 1 ≤ k)
    (hcarry : ∃ V : Subgroup X, V ≤ (Pb.subgroupOf Lb).map (centralQuotientHom e) ∧ ⁅V, V⁆ = V ∧
      3 ^ k ∣ Nat.card V) :
    ∃ s ∈ barD D hP.parab.1 e, orderOf s = 3 ^ k := by
  have hPL : Pb ≤ Lb := hP.parab.1
  set ψ := centralQuotientHom e with hψ
  obtain ⟨V, hVJ, hVp, hVk⟩ := hcarry
  obtain ⟨W, hWp, hWle, hWmap⟩ := CFSG.AGLEmbedding.ParabPrime.exists_perfect_map_eq ψ
    (centralQuotientHom_ker e).le hVp
    (by rw [MonoidHom.range_eq_top.2 (centralQuotientHom_surjective e)]; exact le_top)
  have hkerJ : ψ.ker ≤ Pb.subgroupOf Lb := by
    intro z hz
    rw [hψ, centralQuotientHom_ker e] at hz
    exact center_le_parab hP hz
  have hWJ : W ≤ Pb.subgroupOf Lb := by
    intro w hw
    have h1 := hWle hw
    rw [Subgroup.mem_comap] at h1
    have h2 := hVJ h1
    have : w ∈ ((Pb.subgroupOf Lb).map ψ).comap ψ := h2
    rwa [Subgroup.comap_map_eq_self hkerJ] at this
  set W' : Subgroup Y := W.map Lb.subtype with hW'
  have hW'le : W' ≤ Pb := by
    rintro _ ⟨w, hw, rfl⟩
    exact hWJ hw
  have hW'p : ⁅W', W'⁆ = W' := by rw [hW', ← Subgroup.map_commutator, hWp]
  have hcardW' : Nat.card W' = Nat.card W :=
    Nat.card_congr (Subgroup.equivMapOfInjective W Lb.subtype Lb.subtype_injective).toEquiv.symm
  have hdvdVW : Nat.card V ∣ Nat.card W := by
    rw [← hWmap]
    exact Subgroup.card_dvd_of_surjective (ψ.subgroupMap_surjective W)
  have hdvdD : 3 ^ k ∣ Nat.card D :=
    hD.Dcarry W' hW'le hW'p k (by rw [hcardW']; exact hVk.trans hdvdVW)
  have hx1 : x ≠ 1 := fun h => hD.hxC (h ▸ Subgroup.one_mem _)
  have hxo : orderOf x = 3 := orderOf_eq_prime hD.hx3 hx1
  obtain ⟨A, hAD, hAp, hAc, hxA, d, hdA, hdo⟩ :=
    exists_elt_of_dvd hD.Dcyc hD.hx hD.hx3 hx1 hk hdvdD
  have hdD : d ∈ D := hAD hdA
  have hcomm : ∀ a ∈ Pb, ∀ b ∈ Subgroup.centralizer (Lb : Set Y), a * b = b * a :=
    fun a ha b hb => Subgroup.mem_centralizer_iff.mp hb a (hPL ha)
  obtain ⟨p, hp, c, hc, hdpc⟩ := Lift.exists_mul_of_mem_sup_of_commute hcomm (hD.Dle hdD)
  have hpc : p * c = c * p := hcomm p hp c hc
  have hAct : Lift.Act Lb d p := by
    intro l hl
    have hcl : c * l = l * c := (Subgroup.mem_centralizer_iff.mp hc l hl).symm
    rw [← hdpc]
    calc p * c * l * (p * c)⁻¹ = p * (c * l) * c⁻¹ * p⁻¹ := by group
      _ = p * (l * c) * c⁻¹ * p⁻¹ := by rw [hcl]
      _ = p * l * p⁻¹ := by group
  set l : ↥Lb := ⟨p, hPL hp⟩ with hl
  have hlmem : l ∈ (Lift.actD Lb Pb D hPL).subgroupOf Lb := ⟨hp, d, hdD, hAct⟩
  refine ⟨ψ l, ⟨l, hlmem, rfl⟩, ?_⟩
  have hpow : ∀ m : ℕ, ψ l ^ m = 1 ↔ p ^ m ∈ Subgroup.centralizer (Lb : Set Y) := by
    intro m
    rw [← map_pow]
    constructor
    · intro h
      have : l ^ m ∈ Subgroup.center ↥Lb := by
        rw [← centralQuotientHom_ker e]; exact h
      rw [Subgroup.mem_centralizer_iff]
      intro g hg
      have := Subgroup.mem_center_iff.1 this ⟨g, hg⟩
      exact congrArg Subtype.val this
    · intro h
      have : l ^ m ∈ Subgroup.center ↥Lb := by
        rw [Subgroup.mem_center_iff]
        intro g
        exact Subtype.ext (Subgroup.mem_centralizer_iff.mp h g.1 g.2)
      rw [← centralQuotientHom_ker e] at this
      exact this
  have hdm : ∀ m : ℕ, d ^ m = p ^ m * c ^ m := fun m => by
    rw [← hdpc]; exact (Commute.mul_pow hpc m)
  have hCmem : ∀ m : ℕ, c ^ m ∈ Subgroup.centralizer (Lb : Set Y) := fun m => Subgroup.pow_mem _ hc m
  apply Nat.dvd_antisymm
  · refine orderOf_dvd_of_pow_eq_one ((hpow _).2 ?_)
    have h1 : d ^ 3 ^ k = 1 := by rw [← hdo]; exact pow_orderOf_eq_one d
    rw [hdm] at h1
    have : p ^ 3 ^ k = (c ^ 3 ^ k)⁻¹ := eq_inv_of_mul_eq_one_left h1
    rw [this]
    exact Subgroup.inv_mem _ (hCmem _)
  · rw [← hdo]
    by_contra hnd
    have hs1 : ψ l ^ orderOf (ψ l) = 1 := pow_orderOf_eq_one _
    have hpC := (hpow _).1 hs1
    have hdC : d ^ orderOf (ψ l) ∈ Subgroup.centralizer (Lb : Set Y) := by
      rw [hdm]; exact Subgroup.mul_mem _ hpC (hCmem _)
    have hne : d ^ orderOf (ψ l) ≠ 1 := by
      intro h
      exact hnd (orderOf_dvd_of_pow_eq_one h)
    have hxz := mem_zpowers_of_cyclic_three_group hAp hxA hxo (Subgroup.pow_mem _ hdA _) hne
    exact hD.hxC (by
      have : Subgroup.zpowers (d ^ orderOf (ψ l)) ≤ Subgroup.centralizer (Lb : Set Y) :=
        (Subgroup.zpowers_le).2 hdC
      exact this hxz)

end Carry

end CFSG.HardMathSupport.Curtis.UnitaryLevi
