module

public import CFSG.LocalAnalysis.ComponentClassification.Asc75T4ConjNormSL2
public import CFSG.LocalAnalysis.ComponentClassification.Asc75T4Hyp61

public section

namespace CFSG.ComponentClassification.Asc75T4

open Subgroup CFSG.ABGLocalTools CFSG.ComponentClassification.AS76b
open CFSG.ComponentClassification.AschbacherTightEmbedding

variable {G : Type} [Group G] [Finite G]

namespace MainSetting

variable {Q : Subgroup G} (hS : MainSetting Q)
include hS

theorem linkedLayer_le_normalizer_of_mem {B : Subgroup G} (hB : B ∈ linkedClass Q) :
    linkedLayer Q ≤ normalizer (B : Set G) :=
  iSup₂_le fun _ hA => (hS.linked_of_mem hA hB).1

theorem commutator_mem_oddCoreIn_of_ne {A B : Subgroup G} (hA : A ∈ linkedClass Q)
    (hB : B ∈ linkedClass Q) (hne : A ≠ B) {a b : G} (ha : a ∈ twoPrimeLayerIn A)
    (hb : b ∈ twoPrimeLayerIn B) : a * b * a⁻¹ * b⁻¹ ∈ oddCoreIn (linkedLayer Q) :=
  hS.inf_le_oddCoreIn hB hA (Ne.symm hne) (commutator_mem_inf (hS.linked_of_mem hB hA) a ha b hb)

theorem mem_linkedClass_of_fourGroup {j : G} {E : Subgroup G} (hEJ : E ≤ rightConjugate Q j)
    (hE : ∀ e ∈ E, e ^ 2 = 1) (hE4 : Nat.card E = 4) {B : Subgroup G} (hB : B ∈ linkedClass Q)
    (hEB : E ≤ normalizer (B : Set G)) : rightConjugate Q j ∈ linkedClass Q := by
  obtain ⟨⟨b, rfl⟩, hQB⟩ := hB
  have hK : twoPrimeLayerIn (rightConjugate Q b) ≤ normalizer (rightConjugate Q j : Set G) :=
    hS.caseI j b ⟨E, le_inf hEJ hEB, hE, hE4⟩
  exact hS.mem_linkedClass_of_linked ⟨⟨b, rfl⟩, hQB⟩ (hS.linked_of_le hK)

theorem mem_linkedClass_of_coversLayer {j : G} {X : Subgroup G} (hX : IsPGroup 2 X)
    (hXc : centralizer (X : Set G) ≠ ⊤) (hXJ : CoversLayer X (rightConjugate Q j))
    {B : Subgroup G} (hB : B ∈ linkedClass Q) (hXB : CoversLayer X B) :
    rightConjugate Q j ∈ linkedClass Q := by
  obtain ⟨⟨b, rfl⟩, hQB⟩ := hB
  rcases hS.star j b X hX hXc hXJ hXB with h | h
  · rw [h]
    exact ⟨⟨b, rfl⟩, hQB⟩
  · exact hS.mem_linkedClass_of_linked ⟨⟨b, rfl⟩, hQB⟩ h.symm

section Diagonal

variable {J C : Subgroup G} (hJ : ∃ j : G, J = rightConjugate Q j)
  (hC : C = twoPrimeLayerIn J ⊓ normalizer (linkedLayer Q : Set G))
  (hKC : twoPrimeLayerIn J ≤ C ⊔ oddCoreIn J) {n : ℕ} (hn : 2 ≤ n)
  {ψ : oUpperTwoPrime C →* Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 n)}
  (hψ : Function.Surjective ψ) (hker : ψ.ker = (oddCoreIn C).subgroupOf (oUpperTwoPrime C))
include hJ hC hKC hn hψ hker

theorem centMod_of_mem_linkedLayer (hJ0 : J ∉ linkedClass Q) {d : G}
    (hdD : d ∈ linkedLayer Q) (hdJ : d ∈ normalizer (J : Set G)) :
    CentMod (twoPrimeLayerIn J) (oddCoreIn J) d := by
  obtain ⟨j, rfl⟩ := hJ
  set D := linkedLayer Q
  have hCK : C ≤ twoPrimeLayerIn (rightConjugate Q j) := by rw [hC]; exact inf_le_left
  have hCN : C ≤ normalizer (D : Set G) := by rw [hC]; exact inf_le_right
  have h4C : HasFourGroup C := hasFourGroup_of_le_sup (hS.four_rightConjugate j) hCK hKC
  have hLD : oUpperTwoPrime C ≤ normalizer (D : Set G) := (oUpperTwoPrime_le C).trans hCN
  have hDO : D ⊓ oUpperTwoPrime C ≤ oddCoreIn C := by
    rcases inf_le_oddCoreIn_or_le_sup hn hψ hker hLD with h | h
    · exact h
    · exfalso
      obtain ⟨E, hE, hE2, hE4⟩ := hasFourGroup_inf_of_le_sup h4C h
      exact hJ0 (hS.mem_linkedClass_of_fourGroup
        (hE.trans (inf_le_right.trans ((oUpperTwoPrime_le C).trans
          (hCK.trans (twoPrimeLayerIn_le _))))) hE2 hE4 (self_mem_linkedClass Q)
        (hE.trans (inf_le_left.trans hS.linkedLayer_le_normalizer_self)))
  have hOC : oddCoreIn C ≤ oddCoreIn (rightConjugate Q j) := oddCoreIn_le_oddCoreIn hCK hKC
  have hKL := twoPrimeLayerIn_le_oUpperTwoPrime_sup hCK hKC
  have hdC : d ∈ normalizer (C : Set G) := by
    rw [hC]
    exact inf_normalizer_le_normalizer_inf _ _
      ⟨normalizer_le_normalizer_twoPrimeLayerIn _ hdJ, le_normalizer (le_normalizer hdD)⟩
  have hdL : d ∈ normalizer (oUpperTwoPrime C : Set G) :=
    normalizer_le_normalizer_oUpperTwoPrime C hdC
  have hdO : d ∈ normalizer (oddCoreIn (rightConjugate Q j) : Set G) :=
    normalizer_le_normalizer_oddCoreIn _ hdJ
  have hLO : oUpperTwoPrime C ≤ normalizer (oddCoreIn (rightConjugate Q j) : Set G) :=
    (oUpperTwoPrime_le C).trans (hCK.trans ((twoPrimeLayerIn_le _).trans
      (normalIn_le_normalizer (oddCoreIn_normalIn _))))
  have hcL : CentMod (oUpperTwoPrime C) (oddCoreIn (rightConjugate Q j)) d := by
    intro l hl
    have hlD : l ∈ normalizer (D : Set G) := hLD hl
    have h1 : d * l * d⁻¹ * l⁻¹ ∈ D := by
      have : d * l * d⁻¹ * l⁻¹ = d * (l * d⁻¹ * l⁻¹) := by group
      rw [this]
      exact mul_mem hdD ((mem_normalizer_iff.mp hlD _).mp (inv_mem hdD))
    have h2 : d * l * d⁻¹ * l⁻¹ ∈ oUpperTwoPrime C :=
      mul_mem ((mem_normalizer_iff.mp hdL l).mp hl) (inv_mem hl)
    exact hOC (hDO ⟨h1, h2⟩)
  exact (centMod_sup hLO hdO hcL).mono hKL

theorem exists_mem_linkedClass_ne (hJ0 : J ∉ linkedClass Q) {E : Subgroup G} (hEC : E ≤ C)
    (hE : ∀ e ∈ E, e ^ 2 = 1) (hE4 : Nat.card E = 4) {u : G} (huE : u ∈ E)
    (huQ : u ∉ normalizer (Q : Set G)) :
    ∃ B ∈ linkedClass Q, B ≠ Q ∧ B ≠ rightConjugate Q u := by
  obtain ⟨j, rfl⟩ := hJ
  have hCK : C ≤ twoPrimeLayerIn (rightConjugate Q j) := by rw [hC]; exact inf_le_left
  have hCN : C ≤ normalizer (linkedLayer Q : Set G) := by rw [hC]; exact inf_le_right
  by_contra hcon
  push Not at hcon
  have hmem : ∀ g ∈ normalizer (linkedLayer Q : Set G),
      rightConjugate Q g = Q ∨ rightConjugate Q g = rightConjugate Q u := fun g hg => by
    by_cases h : rightConjugate Q g = Q
    · exact Or.inl h
    · exact Or.inr (hcon _ (hS.rightConjugate_mem_linkedClass_of_mem_normalizer hg
        (self_mem_linkedClass Q)) h)
  have hu2 : u * u = 1 := by rw [← pow_two]; exact hE u huE
  have hconj : ∀ l ∈ C, ∀ y ∈ C ⊓ normalizer (Q : Set G),
      l * y * l⁻¹ ∈ C ⊓ normalizer (Q : Set G) := by
    intro l hl y hy
    refine mem_inf.mpr ⟨mul_mem (mul_mem hl hy.1) (inv_mem hl), ?_⟩
    rw [← rightConjugate_eq_self_iff, ← rightConjugate_mul, ← rightConjugate_mul]
    have hyQ : rightConjugate Q y = Q := (rightConjugate_eq_self_iff Q y).mpr hy.2
    have hyu : rightConjugate (rightConjugate Q u) y = rightConjugate Q u := by
      rw [rightConjugate_mul]
      rcases hmem (u * y) (mul_mem (hCN (hEC huE)) (hCN hy.1)) with h | h
      · exfalso
        apply huQ
        rw [← rightConjugate_eq_self_iff]
        calc rightConjugate Q u = rightConjugate (rightConjugate Q (u * y)) y⁻¹ := by
              rw [rightConjugate_mul, mul_inv_cancel_right]
          _ = rightConjugate Q y⁻¹ := by rw [h]
          _ = Q := (rightConjugate_eq_self_iff Q _).mpr (inv_mem hy.2)
      · exact h
    rcases hmem l (hCN hl) with h | h
    · rw [h, hyQ, rightConjugate_eq_self_iff]
      exact inv_mem ((rightConjugate_eq_self_iff Q l).mp h)
    · rw [h, hyu, ← h, rightConjugate_mul, mul_inv_cancel, rightConjugate_one]
  have hnorm : oUpperTwoPrime C ≤
      normalizer ((C ⊓ normalizer (Q : Set G) : Subgroup G) : Set G) := by
    intro l hl
    have hlC := oUpperTwoPrime_le C hl
    rw [mem_normalizer_iff]
    intro y
    refine ⟨hconj l hlC y, fun h => ?_⟩
    have := hconj l⁻¹ (inv_mem hlC) _ h
    rwa [show l⁻¹ * (l * y * l⁻¹) * l⁻¹⁻¹ = y by group] at this
  have h4C : HasFourGroup C := ⟨E, hEC, hE, hE4⟩
  have hEL : ∀ e ∈ E, e ∈ oUpperTwoPrime C := fun e he =>
    subset_closure ⟨hEC he, 1, by simpa using hE e he⟩
  rcases inf_le_oddCoreIn_or_le_sup hn hψ hker hnorm with h | h
  ·
    have hEu : ∀ e ∈ E, e = 1 ∨ e = u := by
      intro e he
      rcases hmem e (hCN (hEC he)) with h' | h'
      · left
        exact eq_one_of_mem_of_odd (odd_card_oddCoreIn C)
          (h ⟨⟨hEC he, (rightConjugate_eq_self_iff Q e).mp h'⟩, hEL e he⟩) (j := 1)
          (by simpa using hE e he)
      · right
        have heu : e * u ∈ normalizer (Q : Set G) := by
          rw [← rightConjugate_eq_self_iff, ← rightConjugate_mul, h', rightConjugate_mul, hu2,
            rightConjugate_one]
        have heuE : e * u ∈ E := mul_mem he huE
        have h1 := eq_one_of_mem_of_odd (odd_card_oddCoreIn C)
          (h ⟨⟨hEC heuE, heu⟩, hEL _ heuE⟩) (j := 1) (by simpa using hE _ heuE)
        calc e = e * u * u := by rw [mul_assoc, hu2, mul_one]
          _ = u := by rw [h1, one_mul]
    have hsub : (E : Set G) ⊆ {1, u} := fun e he => by
      rcases hEu e he with h' | h' <;> simp [h']
    have hle : Nat.card E ≤ 2 := by
      calc Nat.card E = Nat.card (E : Set G) := rfl
        _ ≤ Nat.card ({1, u} : Set G) := Nat.card_mono (Set.toFinite _) hsub
        _ ≤ 2 := by
          rw [Nat.card_coe_set_eq]
          exact (Set.ncard_insert_le _ _).trans (by rw [Set.ncard_singleton])
    omega
  · exfalso
    obtain ⟨F, hF, hF2, hF4⟩ := hasFourGroup_inf_of_le_sup h4C h
    exact hJ0 (hS.mem_linkedClass_of_fourGroup
      (hF.trans (inf_le_left.trans (inf_le_left.trans (hCK.trans (twoPrimeLayerIn_le _)))))
      hF2 hF4 (self_mem_linkedClass Q) (hF.trans (inf_le_left.trans inf_le_right)))

theorem mem_linkedClass_of_sl2 : J ∈ linkedClass Q := by
  by_contra hJ0
  obtain ⟨j, rfl⟩ := hJ
  set D := linkedLayer Q
  have hCK : C ≤ twoPrimeLayerIn (rightConjugate Q j) := by rw [hC]; exact inf_le_left
  have hCN : C ≤ normalizer (D : Set G) := by rw [hC]; exact inf_le_right
  obtain ⟨E, hEC, hE, hE4⟩ := hasFourGroup_of_le_sup (hS.four_rightConjugate j) hCK hKC
  have hEJ : E ≤ rightConjugate Q j := hEC.trans (hCK.trans (twoPrimeLayerIn_le _))
  obtain ⟨u, huE, huQ⟩ : ∃ u ∈ E, u ∉ normalizer (Q : Set G) := by
    by_contra h
    push Not at h
    exact hJ0 (hS.mem_linkedClass_of_fourGroup hEJ hE hE4 (self_mem_linkedClass Q) h)
  obtain ⟨B, hB, hBQ, hBu⟩ :=
    hS.exists_mem_linkedClass_ne ⟨j, rfl⟩ hC hKC hn hψ hker hJ0 hEC hE hE4 huE huQ
  have hu2 : u ^ 2 = 1 := hE u huE
  have huu : u * u = 1 := by rw [← pow_two, hu2]
  have hu1 : u ≠ 1 := fun h => huQ (h ▸ one_mem _)
  have hu_ord : orderOf u = 2 := orderOf_eq_prime hu2 hu1
  have huD : u ∈ normalizer (D : Set G) := hCN (hEC huE)
  have hQu : rightConjugate Q u ∈ linkedClass Q :=
    hS.rightConjugate_mem_linkedClass_of_mem_normalizer huD (self_mem_linkedClass Q)
  have hQu_ne : rightConjugate Q u ≠ Q := fun h => huQ ((rightConjugate_eq_self_iff Q u).mp h)
  have hQ := self_mem_linkedClass Q
  obtain ⟨x, hxK, ⟨k, hxk⟩, hxc⟩ := exists_two_element_not_centMod hS.four
  have hKD : twoPrimeLayerIn Q ≤ D := twoPrimeLayerIn_le_linkedLayer hQ
  have hxD : x ∈ D := hKD hxK
  obtain ⟨x', hx'⟩ : ∃ x' : G, x' = u * x * u := ⟨_, rfl⟩
  have hx'K : x' ∈ twoPrimeLayerIn (rightConjugate Q u) := by
    rw [twoPrimeLayerIn_rightConjugate, mem_rightConjugate_iff, hx']
    have : u * (u * x * u) * u⁻¹ = x := by
      rw [show u⁻¹ = u by rw [inv_eq_iff_mul_eq_one, huu]]
      simp only [← mul_assoc, huu, one_mul]
      rw [mul_assoc, huu, mul_one]
    rw [this]
    exact hxK
  have hx'D : x' ∈ D := twoPrimeLayerIn_le_linkedLayer hQu hx'K
  have hx'k : x' ^ (2 ^ k) = 1 := by
    rw [hx', show u * x * u = u * x * u⁻¹ by rw [show u⁻¹ = u by
      rw [inv_eq_iff_mul_eq_one, huu]], conj_pow, hxk, mul_one, mul_inv_cancel]
  have hyD : x * x' ∈ D := mul_mem hxD hx'D
  have huO : u ∈ normalizer (oddCoreIn D : Set G) := normalizer_le_normalizer_oddCoreIn D huD
  have hyO : x * x' ∈ normalizer (oddCoreIn D : Set G) :=
    linkedLayer_le_normalizer_oddCoreIn hyD
  have hcuy : u * (x * x') * u⁻¹ * (x * x')⁻¹ ∈ oddCoreIn D := by
    have h1 : u * (x * x') * u⁻¹ * (x * x')⁻¹ = x' * x * x'⁻¹ * x⁻¹ := by
      rw [hx']
      group
    rw [h1]
    exact hS.commutator_mem_oddCoreIn_of_ne hQu hQ hQu_ne hx'K hxK
  obtain ⟨c, hcu, hcy⟩ := exists_mem_centralizer_of_commutator
    (isPGroup_zpowers_of_pow_eq_one (k := 1) (by simpa using hu2)) (odd_card_oddCoreIn D)
    ((zpowers_le).mpr huO) hyO (zpowers_conj_commutator_mem huO hcuy)
  have hcD : c ∈ D := by
    have : c = (x * x') * (c⁻¹ * (x * x'))⁻¹ := by group
    rw [this]
    exact mul_mem hyD (inv_mem (oddCoreIn_le D hcy))
  set π := QuotientGroup.mk' (CFSG.Assembly.oddCore D)
  have hπcy : π ⟨c, hcD⟩ = π ⟨x, hxD⟩ * π ⟨x', hx'D⟩ := by
    rw [← map_mul]
    exact (mk_eq_mk_iff _ _).mpr hcy
  have hcxx' : Commute (π ⟨x, hxD⟩) (π ⟨x', hx'D⟩) :=
    (commute_mk_iff _ _).mpr (hS.commutator_mem_oddCoreIn_of_ne hQ hQu hQu_ne.symm hxK hx'K)
  have hπc2 : π ⟨c, hcD⟩ ^ (2 ^ k) = 1 := by
    have h1 : (⟨x, hxD⟩ : D) ^ (2 ^ k) = 1 := Subtype.ext (by simpa using hxk)
    have h2 : (⟨x', hx'D⟩ : D) ^ (2 ^ k) = 1 := Subtype.ext (by simpa using hx'k)
    rw [hπcy, hcxx'.mul_pow, ← map_pow, ← map_pow, h1, h2, map_one, mul_one]
  obtain ⟨⟨d, hdD⟩, hdc, ⟨i, hdi⟩, hπd⟩ := exists_two_element_pow π hπc2
  have hdi' : d ^ (2 ^ i) = 1 := by simpa using congrArg Subtype.val hdi
  have hπd' : π ⟨d, hdD⟩ = π ⟨x, hxD⟩ * π ⟨x', hx'D⟩ := hπd.trans hπcy
  have hdu : d ∈ centralizer ({u} : Set G) := by
    obtain ⟨m, hm⟩ := mem_zpowers_iff.mp hdc
    have hdm : d = c ^ m := by
      have := congrArg Subtype.val hm
      simpa using this.symm
    rw [mem_centralizer_iff]
    intro z hz
    rw [Set.mem_singleton_iff] at hz
    rw [hz, hdm]
    exact ((Commute.zpow_right (mem_centralizer_iff.mp hcu u (mem_zpowers u)) m)).eq
  have hdJ : d ∈ normalizer (rightConjugate Q j : Set G) :=
    centralizer_le_of_involution (rightConjugate_tightlyEmbedded Q hS.tight j) (hEJ huE)
      hu_ord hdu
  have hXJ : CoversLayer (zpowers d) (rightConjugate Q j) :=
    coversLayer_of_commutator (isPGroup_zpowers_of_pow_eq_one hdi') ((zpowers_le).mpr hdJ)
      (zpowers_commutator_mem (normalizer_le_normalizer_twoPrimeLayerIn _ hdJ)
        (normalizer_le_normalizer_oddCoreIn _ hdJ)
        (hS.centMod_of_mem_linkedLayer ⟨j, rfl⟩ hC hKC hn hψ hker hJ0 hdD hdJ))
  have hdB : d ∈ normalizer (B : Set G) := hS.linkedLayer_le_normalizer_of_mem hB hdD
  have hcB : ∀ z ∈ twoPrimeLayerIn B, d * z * d⁻¹ * z⁻¹ ∈ oddCoreIn B := by
    intro z hz
    have hzD : z ∈ D := twoPrimeLayerIn_le_linkedLayer hB hz
    have h1 : Commute (π ⟨x, hxD⟩) (π ⟨z, hzD⟩) :=
      (commute_mk_iff _ _).mpr (hS.commutator_mem_oddCoreIn_of_ne hQ hB hBQ.symm hxK hz)
    have h2 : Commute (π ⟨x', hx'D⟩) (π ⟨z, hzD⟩) :=
      (commute_mk_iff _ _).mpr (hS.commutator_mem_oddCoreIn_of_ne hQu hB hBu.symm hx'K hz)
    have h3 : Commute (π ⟨d, hdD⟩) (π ⟨z, hzD⟩) := by
      rw [hπd']
      exact h1.mul_left h2
    have h4 : d * z * d⁻¹ * z⁻¹ ∈ twoPrimeLayerIn B ⊓ oddCoreIn D :=
      mem_inf.mpr ⟨mul_mem ((mem_normalizer_iff.mp
        (normalizer_le_normalizer_twoPrimeLayerIn B hdB) z).mp hz) (inv_mem hz),
        (commute_mk_iff ⟨d, hdD⟩ ⟨z, hzD⟩).mp h3⟩
    rwa [inf_oddCoreIn_eq (hS.normalIn_linkedLayer hB), oddCoreIn_twoPrimeLayerIn] at h4
  have hXB : CoversLayer (zpowers d) B :=
    coversLayer_of_commutator (isPGroup_zpowers_of_pow_eq_one hdi') ((zpowers_le).mpr hdB)
      (zpowers_commutator_mem (normalizer_le_normalizer_twoPrimeLayerIn B hdB)
        (normalizer_le_normalizer_oddCoreIn B hdB) hcB)
  have hXc : centralizer (zpowers d : Set G) ≠ ⊤ := by
    intro htop
    apply hxc
    intro z hz
    have hzD : z ∈ D := hKD hz
    have hdz : d * z = z * d := by
      have hzC : z ∈ centralizer (zpowers d : Set G) := htop ▸ mem_top z
      exact mem_centralizer_iff.mp hzC d (mem_zpowers d)
    have h1 : Commute (π ⟨d, hdD⟩) (π ⟨z, hzD⟩) := by
      have : (⟨d, hdD⟩ : D) * ⟨z, hzD⟩ = ⟨z, hzD⟩ * ⟨d, hdD⟩ := Subtype.ext hdz
      rw [commute_iff_eq, ← map_mul, ← map_mul, this]
    have h2 : Commute (π ⟨x', hx'D⟩) (π ⟨z, hzD⟩) :=
      (commute_mk_iff _ _).mpr (hS.commutator_mem_oddCoreIn_of_ne hQu hQ hQu_ne hx'K hz)
    rw [hπd'] at h1
    have h4 : x * z * x⁻¹ * z⁻¹ ∈ twoPrimeLayerIn Q ⊓ oddCoreIn D :=
      mem_inf.mpr ⟨mul_mem (mul_mem (mul_mem hxK hz) (inv_mem hxK)) (inv_mem hz),
        (commute_mk_iff ⟨x, hxD⟩ ⟨z, hzD⟩).mp (commute_of_mul_commute h1 h2)⟩
    rwa [inf_oddCoreIn_eq (hS.normalIn_linkedLayer hQ), oddCoreIn_twoPrimeLayerIn] at h4
  exact hJ0 (hS.mem_linkedClass_of_coversLayer (isPGroup_zpowers_of_pow_eq_one hdi') hXc hXJ hB
    hXB)

end Diagonal

end MainSetting

end CFSG.ComponentClassification.Asc75T4
