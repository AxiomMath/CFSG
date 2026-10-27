module

public import CFSG.LocalAnalysis.ComponentClassification.GSThmBCatalog5CovGen
public import CFSG.LocalAnalysis.ComponentClassification.M12J2CoverData
public import CFSG.LinearAlgebra.LinearGroups.TwoQuadraticOddSections

public section

namespace CFSG.ComponentClassification.SolMax.H35

open Subgroup CFSG.Blueprint CFSG.ComponentClassification.GSThmB
open scoped commutatorElement

theorem mem_or_mul_mem_of_mem_sup {G : Type*} [Group G] {t : G} {A : Subgroup G}
    (ht2 : t * t = 1) (htA : ∀ a ∈ A, a * t = t * a) {x : G} (hx : x ∈ zpowers t ⊔ A) :
    x ∈ A ∨ t * x ∈ A := by
  have hcomm : ∀ y : G, t * y ∈ A → y * t = t * y := by
    intro y hy
    have h1 := htA _ hy
    have h2 : t * (y * t) = t * (t * y) := by
      calc t * (y * t) = t * y * t := by group
        _ = t * (t * y) := h1
    exact mul_left_cancel h2
  let S : Subgroup G :=
    { carrier := {y | y ∈ A ∨ t * y ∈ A}
      one_mem' := Or.inl A.one_mem
      mul_mem' := by
        rintro a b (ha | ha) (hb | hb)
        · exact Or.inl (A.mul_mem ha hb)
        · refine Or.inr ?_
          have e : t * (a * b) = a * (t * b) := by
            calc t * (a * b) = (t * a) * b := by group
              _ = (a * t) * b := by rw [htA a ha]
              _ = a * (t * b) := by group
          rw [e]
          exact A.mul_mem ha hb
        · refine Or.inr ?_
          rw [← mul_assoc]
          exact A.mul_mem ha hb
        · refine Or.inl ?_
          have e : a * b = (t * a) * (t * b) := by
            calc a * b = (t * t) * a * b := by rw [ht2, one_mul]
              _ = t * (t * a) * b := by group
              _ = t * (a * t) * b := by rw [hcomm a ha]
              _ = (t * a) * (t * b) := by group
          rw [e]
          exact A.mul_mem ha hb
      inv_mem' := by
        rintro a (ha | ha)
        · exact Or.inl (A.inv_mem ha)
        · refine Or.inr ?_
          have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht2
          have e : t * a⁻¹ = (t * a)⁻¹ := by
            rw [mul_inv_rev, htinv]
            have h1 : a * t = t * a := hcomm a ha
            calc t * a⁻¹ = a⁻¹ * (a * t) * a⁻¹ := by group
              _ = a⁻¹ * (t * a) * a⁻¹ := by rw [h1]
              _ = a⁻¹ * t := by group
          rw [e]
          exact A.inv_mem ha }
  have hle : zpowers t ⊔ A ≤ S := by
    refine sup_le ?_ fun a ha => Or.inl ha
    rw [zpowers_le]
    exact Or.inr (by rw [ht2]; exact A.one_mem)
  exact hle hx

theorem commutatorElement_mul_left_of_commute {G : Type*} [Group G] {t a v : G}
    (ha : Commute t a) (hv : Commute t v) : ⁅t * a, v⁆ = ⁅a, v⁆ := by
  have hc : Commute t (a * v * a⁻¹) := (ha.mul_right hv).mul_right ha.inv_right
  simp only [commutatorElement_def, mul_inv_rev]
  calc t * a * v * (a⁻¹ * t⁻¹) * v⁻¹ = t * (a * v * a⁻¹) * t⁻¹ * v⁻¹ := by group
    _ = (a * v * a⁻¹) * t * t⁻¹ * v⁻¹ := by rw [hc.eq]
    _ = a * v * a⁻¹ * v⁻¹ := by group

theorem commutatorElement_mul_right_of_commute {G : Type*} [Group G] {t u b : G}
    (hu : Commute t u) (hb : Commute t b) : ⁅u, t * b⁆ = ⁅u, b⁆ := by
  have hc : Commute t (u * b * u⁻¹ * b⁻¹) :=
    (((hu.mul_right hb).mul_right hu.inv_right).mul_right hb.inv_right)
  simp only [commutatorElement_def, mul_inv_rev]
  calc u * (t * b) * u⁻¹ * (b⁻¹ * t⁻¹) = (u * t) * b * u⁻¹ * b⁻¹ * t⁻¹ := by group
    _ = (t * u) * b * u⁻¹ * b⁻¹ * t⁻¹ := by rw [hu.eq]
    _ = t * (u * b * u⁻¹ * b⁻¹) * t⁻¹ := by group
    _ = (u * b * u⁻¹ * b⁻¹) * t * t⁻¹ := by rw [hc.eq]
    _ = u * b * u⁻¹ * b⁻¹ := by group

theorem le_of_isPerfect_of_le_sup {G : Type*} [Group G] {t : G} {A P : Subgroup G}
    (ht2 : t * t = 1) (htA : ∀ a ∈ A, a * t = t * a) (hP : ⁅P, P⁆ = P)
    (hPA : P ≤ zpowers t ⊔ A) : P ≤ A := by
  have hct : ∀ a ∈ A, Commute t a := fun a ha => (htA a ha).symm
  have hsplit : ∀ x ∈ P, ∃ a ∈ A, (x = a ∨ x = t * a) := by
    intro x hx
    rcases mem_or_mul_mem_of_mem_sup ht2 htA (hPA hx) with h | h
    · exact ⟨x, h, Or.inl rfl⟩
    · refine ⟨t * x, h, Or.inr ?_⟩
      rw [← mul_assoc, ht2, one_mul]
  have hcx : ∀ x ∈ P, Commute t x := by
    intro x hx
    obtain ⟨a, ha, h | h⟩ := hsplit x hx
    · rw [h]
      exact hct a ha
    · rw [h]
      exact (Commute.refl t).mul_right (hct a ha)
  rw [← hP, commutator_le]
  intro x hx y hy
  obtain ⟨a, ha, hxa⟩ := hsplit x hx
  obtain ⟨b, hb, hyb⟩ := hsplit y hy
  have h1 : ⁅x, y⁆ = ⁅a, y⁆ := by
    rcases hxa with rfl | rfl
    · rfl
    · exact commutatorElement_mul_left_of_commute (hct a ha) (hcx y hy)
  have h2 : ⁅a, y⁆ = ⁅a, b⁆ := by
    rcases hyb with rfl | rfl
    · rfl
    · exact commutatorElement_mul_right_of_commute (hct a ha) (hct b hb)
  rw [h1, h2, commutatorElement_def]
  exact A.mul_mem (A.mul_mem (A.mul_mem ha hb) (A.inv_mem ha)) (A.inv_mem hb)

theorem false_of_perfect_mem {G : Type*} [Group G] {t : G} {A P C : Subgroup G}
    (ht : orderOf t = 2) (hC : zpowers t ⊔ A = C) (hinf : zpowers t ⊓ A = ⊥)
    (htA : ∀ a ∈ A, a * t = t * a) (hP : ⁅P, P⁆ = P) (hPC : P ≤ C) (htP : t ∈ P) : False := by
  have ht2 : t * t = 1 := by rw [← sq, ← ht, pow_orderOf_eq_one]
  have hPA := le_of_isPerfect_of_le_sup ht2 htA hP (hC ▸ hPC)
  have h1 : t ∈ zpowers t ⊓ A := ⟨mem_zpowers t, hPA htP⟩
  rw [hinf, mem_bot] at h1
  rw [h1, orderOf_one] at ht
  exact absurd ht (by norm_num)

theorem index_Lsub_le_two {L : Type*} [Group L] (α : MulAut L) (hα : α * α = 1) :
    (Cov.Lsub α).index ≤ 2 := by
  have h1 : (Cov.Lsub α).index = Nat.card (SemidirectProduct.rightHom :
      Cov.Semi α →* ↥(zpowers α)).range := by
    rw [Cov.Lsub, SemidirectProduct.range_inl_eq_ker_rightHom, index_ker]
  rw [h1, MonoidHom.range_eq_top.mpr SemidirectProduct.rightHom_surjective, Subgroup.card_top,
    Nat.card_zpowers]
  exact Nat.le_of_dvd (by norm_num) (orderOf_dvd_of_pow_eq_one (by rw [sq]; exact hα))

theorem coverSetting_semi {L : Type} [Group L] [Finite L] (hLq : Assembly.IsQuasisimple L)
    {t : L} (ht : orderOf t = 2) (hZ : center L = zpowers t) {X : Type} [Group X]
    (π : L →* X) (hπ : Function.Surjective π) (hker : π.ker = zpowers t) (α : MulAut L)
    (hα : α * α = 1) (hout : ∀ n : L, ¬ ∀ y, α y = n * y * n⁻¹) {s : TauCeti.SporadicName}
    (e : X ≃* NativeSporadic.Carrier s) :
    StandardRecognition.CoverSetting s (Cov.Semi α) (Cov.Lsub α)
      ((Cov.eL α t : Cov.Lsub α) : Cov.Semi α) := by
  have hZ' := Cov.center_Lsub α hZ
  refine ⟨inferInstance, Cov.isQuasisimple_Lsub α hLq, ?_, ?_, ?_,
    Cov.centralizer_Lsub_eq α hα hout hZ, index_Lsub_le_two α hα⟩
  · rw [Subgroup.orderOf_coe, MulEquiv.orderOf_eq, ht]
  · rw [hZ', MonoidHom.map_zpowers]
    rfl
  · obtain ⟨e'⟩ := Cov.nonempty_quotient_center_equiv (π.comp (Cov.eL α).symm.toMonoidHom)
      (hπ.comp (Cov.eL α).symm.surjective) (by rw [Cov.ker_comp_eL_symm α π hker, hZ'])
    exact ⟨e'.trans e⟩

theorem false_of_outer {L : Type} [Group L] [Finite L] (hLq : Assembly.IsQuasisimple L) {t : L}
    (ht : orderOf t = 2) (hZ : center L = zpowers t) {X : Type} [Group X] (π : L →* X)
    (hπ : Function.Surjective π) (hker : π.ker = zpowers t) (α : MulAut L) (hα : α * α = 1)
    (hout : ∀ n : L, ¬ ∀ y, α y = n * y * n⁻¹) {s : TauCeti.SporadicName}
    (e : X ≃* NativeSporadic.Carrier s) (hE : StandardRecognition.ExternalInvolutionData s)
    {Lt : Subgroup L} (hLt : ⁅Lt, Lt⁆ = Lt) (htL : t ∈ Lt) (hfix : ∀ y ∈ Lt, α y = y) :
    False := by
  have hα1 : α ≠ 1 := fun h1 => hout 1 fun y => by rw [h1]; simp
  obtain ⟨-, hdata⟩ := hE (Cov.Semi α) (Cov.Lsub α) _
    (coverSetting_semi hLq ht hZ π hπ hker α hα hout e)
  obtain ⟨A, -, hsup, hinf, hcomm, -⟩ :=
    hdata (Cov.pElt α) (Cov.pElt_not_mem α hα1) (Cov.orderOf_pElt α hα hα1)
  set P : Subgroup (Cov.Semi α) := Lt.map SemidirectProduct.inl
  have hP : ⁅P, P⁆ = P := by rw [← map_commutator, hLt]
  have hPC : P ≤ Cov.Lsub α ⊓ centralizer {Cov.pElt α} := by
    rintro _ ⟨y, hy, rfl⟩
    refine ⟨⟨y, rfl⟩, mem_centralizer_singleton_iff.mpr ?_⟩
    have h1 := Cov.pElt_conj α y
    rw [hfix y hy] at h1
    calc SemidirectProduct.inl y * Cov.pElt α =
        Cov.pElt α * SemidirectProduct.inl y * (Cov.pElt α)⁻¹ * Cov.pElt α := by rw [h1]
      _ = Cov.pElt α * SemidirectProduct.inl y := by group
  refine false_of_perfect_mem (t := ((Cov.eL α t : Cov.Lsub α) : Cov.Semi α))
    (by rw [Subgroup.orderOf_coe, MulEquiv.orderOf_eq, ht]) hsup hinf hcomm hP hPC ?_
  rw [Cov.coe_eL]
  exact ⟨t, htL, rfl⟩

theorem le_of_isSubnormal {G : Type*} [Group G] {H K : Subgroup G}
    (h : Assembly.IsSubnormal H K) : H ≤ K :=
  h.le

theorem mem_of_isSubnormal_of_coprime {G : Type*} [Group G] [Finite G] {H K : Subgroup G}
    (h : Assembly.IsSubnormal H K) {p : ℕ} (hp : p.Coprime (H.relIndex K)) {g : G}
    (hgK : g ∈ K) (hg : g ^ p = 1) : g ∈ H := by
  revert hp hgK
  induction h with
  | refl => exact fun _ hgK => hgK
  | @step H M K hHM hn hMK ih =>
    intro hp hgK
    have hMK' := le_of_isSubnormal hMK
    rw [← Subgroup.relIndex_mul_relIndex H M K hHM hMK'] at hp
    have hgM : g ∈ M := ih (Nat.Coprime.coprime_dvd_right (dvd_mul_left _ _) hp) hgK
    have hp' : p.Coprime (H.relIndex M) := Nat.Coprime.coprime_dvd_right (dvd_mul_right _ _) hp
    have hx : (⟨g, hgM⟩ : M) ∈ H.subgroupOf M := by
      rw [← QuotientGroup.eq_one_iff]
      have h1 : (QuotientGroup.mk (⟨g, hgM⟩ : M) : M ⧸ H.subgroupOf M) ^ p = 1 := by
        rw [← QuotientGroup.mk_pow]
        have : (⟨g, hgM⟩ : M) ^ p = 1 := Subtype.ext (by rw [Subgroup.coe_pow]; exact hg)
        rw [this, QuotientGroup.mk_one]
      have h2 : (QuotientGroup.mk (⟨g, hgM⟩ : M) : M ⧸ H.subgroupOf M) ^
          (H.relIndex M) = 1 := by
        rw [Subgroup.relIndex, Subgroup.index_eq_card]
        exact pow_card_eq_one'
      have h3 : orderOf (QuotientGroup.mk (⟨g, hgM⟩ : M) : M ⧸ H.subgroupOf M) ∣ 1 := by
        have := Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one h1) (orderOf_dvd_of_pow_eq_one h2)
        rwa [hp'.gcd_eq_one] at this
      exact orderOf_eq_one_iff.mp (Nat.dvd_one.mp h3)
    exact hx

theorem eq_five_of_ordA_one_dvd_240 {m : ℕ} (hm : 5 ≤ m) (h : Open.ordA 1 m ∣ 240) : m = 5 := by
  unfold Open.ordA at h
  rw [show 1 * (1 + 1) / 2 = 1 by rfl, pow_one, show Finset.Icc 2 (1 + 1) = {2} by rfl,
    Finset.prod_singleton] at h
  have hle := Nat.le_of_dvd (by norm_num) h
  have hg : Nat.gcd (1 + 1) (m - 1) ≤ 2 := Nat.gcd_le_left _ (by norm_num)
  have hg0 : 0 < Nat.gcd (1 + 1) (m - 1) := Nat.gcd_pos_of_pos_left _ (by norm_num)
  have hm8 : m < 8 := by
    by_contra hc
    push Not at hc
    have h1 : 8 * (8 ^ 2 - 1) ≤ m * (m ^ 2 - 1) :=
      Nat.mul_le_mul hc (Nat.sub_le_sub_right (Nat.pow_le_pow_left hc 2) 1)
    have h2 : m * (m ^ 2 - 1) / 2 ≤ m * (m ^ 2 - 1) / Nat.gcd (1 + 1) (m - 1) :=
      Nat.div_le_div_left hg hg0
    omega
  interval_cases m
  · rfl
  · norm_num at h
  · norm_num at h

theorem coprime_five_relIndex {G : Type} [Group G] [Finite G] {M C : Subgroup G} (hMC : M ≤ C)
    (hC : Nat.card C = 240) (hMt : Cov.SmallQ (↥M ⧸ center ↥M)) :
    Nat.Coprime 5 (M.relIndex C) := by
  have hcard : Nat.card C = Nat.card M * M.relIndex C := by
    rw [← Subgroup.card_mul_index (M.subgroupOf C), Subgroup.relIndex,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hMC).toEquiv]
  have hMdvd : Nat.card M ∣ 240 := hC ▸ Dvd.intro _ hcard.symm
  have hQdvd : Nat.card (↥M ⧸ center ↥M) ∣ 240 :=
    (Subgroup.card_quotient_dvd_card _).trans hMdvd
  have h5 : 5 ∣ Nat.card M := by
    rcases Cov.card_of_smallQ' hMt with ⟨q, hq5, hq⟩ | h7
    · rw [hq] at hQdvd
      have hq' := eq_five_of_ordA_one_dvd_240 hq5 hQdvd
      subst hq'
      have h60 : Open.ordA 1 5 = 60 := by decide
      rw [h60] at hq
      exact (show 5 ∣ 60 by norm_num).trans (hq ▸ Subgroup.card_quotient_dvd_card _)
    · rw [h7] at hQdvd
      exact absurd hQdvd (by norm_num)
  rw [Nat.Prime.coprime_iff_not_dvd (by norm_num)]
  intro hr
  have h25 : 25 ∣ 240 := by
    rw [← hC, hcard]
    exact Nat.mul_dvd_mul h5 hr
  exact absurd h25 (by norm_num)

theorem eq_one_or_eq_of_sl2 {L Lt : Type*} [Group L] [Finite L] [Group Lt] (f : L →* Lt)
    (hf : Function.Surjective f) (hker : ∀ x ∈ f.ker, Odd (orderOf x)) (N : Subgroup L)
    [N.Normal] (hN : ∀ x ∈ N, Odd (orderOf x)) {F : Type*} [Field F] (h2 : (2 : F) ≠ 0)
    (e : L ⧸ N ≃* Matrix.SpecialLinearGroup (Fin 2) F) {w : L} (hw : orderOf w = 2)
    (hwc : ∀ y : Lt, f w * y = y * f w) {y : Lt} (hy : y * y = 1) : y = 1 ∨ y = f w := by
  obtain ⟨l, rfl⟩ := hf y
  have hl2 : l * l ∈ f.ker := by rw [MonoidHom.mem_ker, map_mul, hy]
  obtain ⟨k, hk⟩ := hker _ hl2
  set l' := l ^ orderOf (l * l) with hl'def
  have hfl' : f l' = f l := by
    rw [hl'def, map_pow, hk, pow_succ, pow_mul, sq, hy, one_pow, one_mul]
  have hl'2 : l' * l' = 1 := by
    rw [hl'def, ← pow_add, ← two_mul, pow_mul, sq, pow_orderOf_eq_one]
  by_cases hl'1 : l' = 1
  · left
    rw [← hfl', hl'1, map_one]
  right
  have key : ∀ x : L, x * x = 1 → x ≠ 1 →
      ((e (QuotientGroup.mk x) : Matrix.SpecialLinearGroup (Fin 2) F) :
        Matrix (Fin 2) (Fin 2) F) = -1 := by
    intro x hx hx1
    have hxN : (QuotientGroup.mk x : L ⧸ N) ≠ 1 := by
      intro h
      rw [QuotientGroup.eq_one_iff] at h
      have hodd := hN x h
      rw [orderOf_eq_prime (by rw [sq]; exact hx) hx1] at hodd
      exact absurd hodd (by decide)
    refine CFSG.LinearGroups.SL2_coe_eq_neg_one_of_sq h2 _ ?_ ?_
    · rw [← map_pow, ← QuotientGroup.mk_pow, sq, hx, QuotientGroup.mk_one, map_one]
    · intro h
      exact hxN (e.injective (by rw [h, map_one]))
  have hw2 : w * w = 1 := by rw [← sq, ← hw, pow_orderOf_eq_one]
  have hw1 : w ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at hw
    exact absurd hw (by norm_num)
  have heq : (QuotientGroup.mk l' : L ⧸ N) = QuotientGroup.mk w :=
    e.injective (Subtype.ext (by rw [key l' hl'2 hl'1, key w hw2 hw1]))
  rw [QuotientGroup.eq] at heq
  set n := l'⁻¹ * w with hndef
  have hfl2 : f l * f l = 1 := hy
  have hfli : (f l)⁻¹ = f l := inv_eq_of_mul_eq_one_right hfl2
  have hfw2 : f w * f w = 1 := by rw [← map_mul, hw2, map_one]
  have hfn : f n = f l * f w := by rw [hndef, map_mul, map_inv, hfl', hfli]
  have hfn2 : f n ^ 2 = 1 := by
    rw [sq, hfn]
    calc f l * f w * (f l * f w) = f l * (f w * f l) * f w := by group
      _ = f l * (f l * f w) * f w := by rw [hwc (f l)]
      _ = (f l * f l) * (f w * f w) := by group
      _ = 1 := by rw [hfl2, hfw2, one_mul]
  have hodd : Odd (orderOf (f n)) := (hN n heq).of_dvd_nat (orderOf_map_dvd f n)
  have h1 : orderOf (f n) = 1 := by
    have hd : orderOf (f n) ∣ 2 := orderOf_dvd_of_pow_eq_one hfn2
    rcases (Nat.dvd_prime Nat.prime_two).mp hd with h | h
    · exact h
    · rw [h] at hodd
      exact absurd hodd (by decide)
  rw [orderOf_eq_one_iff, hfn] at h1
  calc f l = f l * (f w * f w) := by rw [hfw2, mul_one]
    _ = (f l * f w) * f w := by group
    _ = f w := by rw [h1, one_mul]

end CFSG.ComponentClassification.SolMax.H35
