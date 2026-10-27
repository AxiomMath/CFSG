module

public import CFSG.LocalAnalysis.ComponentClassification.Asc75T4Faithful
public import CFSG.LocalAnalysis.ComponentClassification.Asc75T4Case3

public section

namespace CFSG.ComponentClassification.Asc75T4

open Subgroup CFSG.ABGLocalTools CFSG.ComponentClassification.AS76b
open CFSG.ComponentClassification.AschbacherTightEmbedding
open scoped Pointwise

section Defs

variable {G : Type*} [Group G] [Finite G]

@[expose] def Thm4Case2Weak (Q : Subgroup G) : Prop :=
  CFSG.Open.pRank 2 (twoPrimeLayerIn Q) = 1

@[expose] def Thm4ConclusionWeak (Q : Subgroup G) : Prop :=
  Thm4Case1 Q ∨ Thm4Case2Weak Q ∨ Thm4Case3 Q

theorem Thm4Conclusion.weak {Q : Subgroup G} (h : Thm4Conclusion Q) : Thm4ConclusionWeak Q :=
  h.imp_right (Or.imp_left And.left)

end Defs

@[expose] def Thm4BelowWeak (n : ℕ) : Prop :=
  ∀ (H : Type) [Group H] [Finite H], Nat.card H < n → ∀ Q : Subgroup H, TightlyEmbedded Q →
    twoPrimeLayerIn Q ≠ oddCoreIn Q → Thm4ConclusionWeak Q

theorem Thm4Below.weak {n : ℕ} (h : Thm4Below n) : Thm4BelowWeak n :=
  fun H _ _ hH Q htight hK => (h H hH Q htight hK).weak

variable {G : Type} [Group G] [Finite G]

theorem le_normalizer_of_coversLayer {Q X : Subgroup G} (htight : TightlyEmbedded Q)
    (he : Even (Nat.card (twoPrimeLayerIn Q ⊓ centralizer (X : Set G) : Subgroup G))) :
    X ≤ normalizer (Q : Set G) := by
  have hXC : X ≤ centralizer ((twoPrimeLayerIn Q ⊓ centralizer (X : Set G) : Subgroup G) :
      Set G) := fun x hx =>
    mem_centralizer_iff.mpr fun c hc => (mem_centralizer_iff.mp (mem_inf.mp hc).2 x hx).symm
  exact (hXC.trans (centralizer_le_normalizer _)).trans
    (normalizer_le_of_even htight (inf_le_left.trans (twoPrimeLayerIn_le Q)) he)

theorem centMod_of_coversLayer {Q X : Subgroup G} (hXQ : CoversLayer X Q)
    (hXN : X ≤ normalizer (Q : Set G)) {x : G} (hx : x ∈ X) :
    CentMod (twoPrimeLayerIn Q) (oddCoreIn Q) x := by
  have hQO : Q ≤ normalizer (oddCoreIn Q : Set G) := normalIn_le_normalizer (oddCoreIn_normalIn Q)
  have hCO : twoPrimeLayerIn Q ⊓ centralizer (X : Set G) ≤ normalizer (oddCoreIn Q : Set G) :=
    inf_le_left.trans ((twoPrimeLayerIn_le Q).trans hQO)
  intro k hk
  have hk' : k ∈ ((twoPrimeLayerIn Q ⊓ centralizer (X : Set G) ⊔ oddCoreIn Q : Subgroup G) :
      Set G) := hXQ hk
  rw [coe_mul_of_left_le_normalizer_right _ _ hCO] at hk'
  obtain ⟨c, hc, o, ho, rfl⟩ := Set.mem_mul.mp hk'
  have hxc : x * c = c * x := mem_centralizer_iff.mp (mem_inf.mp hc).2 x hx
  have hxO : x ∈ normalizer (oddCoreIn Q : Set G) := normalizer_le_normalizer_oddCoreIn Q (hXN hx)
  have h1 : x * o * x⁻¹ ∈ oddCoreIn Q := (mem_normalizer_iff.mp hxO o).mp ho
  have h2 : x * (c * o) * x⁻¹ * (c * o)⁻¹ = c * (x * o * x⁻¹ * o⁻¹) * c⁻¹ := by
    rw [← mul_assoc x c o, hxc]
    group
  rw [h2]
  exact (mem_normalizer_iff.mp (hCO hc) _).mp (mul_mem h1 (inv_mem ho))

section Faithful

variable {Q X C U : Subgroup G} (hX : IsPGroup 2 X) (hXN : X ≤ normalizer (Q : Set G))
  (hXc : ∀ x ∈ X, CentMod (twoPrimeLayerIn Q) (oddCoreIn Q) x) (hCK : C ≤ twoPrimeLayerIn Q)
  (hU : IsSylowOf 2 U (Q ⊓ centralizer (X : Set G))) (hUL : U ≤ oUpperTwoPrime C)
  (hF : ∀ l ∈ oUpperTwoPrime C, CentMod (oUpperTwoPrime C) (oddCoreIn Q) l → l ∈ oddCoreIn C)
include hX hXN hXc hCK hU hUL hF

theorem inf_eq_bot_of_faithful : X ⊓ Q = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_contra hne
  have hHn : ((X ⊓ Q).subgroupOf X).Normal :=
    (normal_subgroupOf_iff_le_normalizer inf_le_left).mpr
      ((le_inf le_normalizer hXN).trans (inf_normalizer_le_normalizer_inf X Q))
  have hHne : (X ⊓ Q).subgroupOf X ≠ ⊥ := by
    intro h
    apply hne
    rw [eq_bot_iff]
    intro x hx
    have hx' : (⟨x, (mem_inf.mp hx).1⟩ : X) ∈ (X ⊓ Q).subgroupOf X := hx
    rw [h, mem_bot] at hx'
    rw [mem_bot]
    exact congrArg Subtype.val hx'
  have : Group.IsNilpotent X := hX.isNilpotent
  obtain ⟨⟨w, hw⟩, hw1⟩ :=
    ne_bot_iff_exists_ne_one.mp (Group.IsNilpotent.inf_center_ne_bot_of_normal hHne)
  obtain ⟨hwH, hwZ⟩ := mem_inf.mp hw
  have hwQ : (w : G) ∈ Q := (mem_inf.mp (mem_subgroupOf.mp hwH)).2
  have hwC : (w : G) ∈ centralizer (X : Set G) := mem_centralizer_iff.mpr fun x hx =>
    congrArg Subtype.val (mem_center_iff.mp hwZ ⟨x, hx⟩)
  have hwY : (w : G) ∈ Q ⊓ centralizer (X : Set G) := mem_inf.mpr ⟨hwQ, hwC⟩
  obtain ⟨k, hk⟩ := hX w
  have hk' : (w : G) ^ (2 ^ k) = 1 := by simpa using congrArg Subtype.val hk
  have hUw : U ≤ normalizer (zpowers (w : G) : Set G) := fun u hu =>
    centralizer_le_normalizer _ (Subgroup.centralizer_le (fun y hy => (zpowers_le.mpr w.2) hy)
      (mem_inf.mp (hU.le hu)).2)
  have hp : IsPGroup 2 (U ⊔ zpowers (w : G) : Subgroup G) :=
    hU.isPGroup.to_sup_of_normal_right' (isPGroup_zpowers_of_pow_eq_one hk') hUw
  have heq := hU.eq_of_le le_sup_left (sup_le hU.le ((zpowers_le).mpr hwY)) hp
  have hwU : (w : G) ∈ U := heq ▸ mem_sup_right (mem_zpowers _)
  have hwO := hF _ (hUL hwU) ((hXc w w.2).mono ((oUpperTwoPrime_le C).trans hCK))
  exact hw1 (Subtype.ext (Subtype.ext (eq_one_of_mem_of_odd (odd_card_oddCoreIn C) hwO hk')))

theorem isSylowOf_of_faithful : IsSylowOf 2 U Q := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hXQ := inf_eq_bot_of_faithful hX hXN hXc hCK hU hUL hF
  have hUQ : U ≤ Q := hU.le.trans inf_le_left
  have hUC : U ≤ centralizer (X : Set G) := hU.le.trans inf_le_right
  have hU2 : IsPGroup 2 U := hU.isPGroup
  have hKn : Q ≤ normalizer (twoPrimeLayerIn Q : Set G) :=
    le_normalizer.trans (normalizer_le_normalizer_twoPrimeLayerIn Q)
  have hOn : Q ≤ normalizer (oddCoreIn Q : Set G) := normalIn_le_normalizer (oddCoreIn_normalIn Q)
  have hXO : X ≤ normalizer (oddCoreIn Q : Set G) :=
    hXN.trans (normalizer_le_normalizer_oddCoreIn Q)
  have hXU : X ≤ normalizer (U : Set G) := fun x hx =>
    centralizer_le_normalizer _ (mem_centralizer_iff.mpr fun u hu =>
      (mem_centralizer_iff.mp (hUC hu) x hx).symm)
  have hXU2 : IsPGroup 2 (X ⊔ U : Subgroup G) := hX.to_sup_of_normal_right' hU2 hXU
  have hXUcoe : ((X ⊔ U : Subgroup G) : Set G) = (X : Set G) * (U : Set G) :=
    coe_mul_of_left_le_normalizer_right X U hXU
  have hXUQ : (X ⊔ U) ⊓ Q = U := by
    refine le_antisymm ?_ (le_inf le_sup_right hUQ)
    intro z hz
    obtain ⟨hz, hzQ⟩ := mem_inf.mp hz
    rw [← SetLike.mem_coe, hXUcoe] at hz
    obtain ⟨x, hx, u, hu, rfl⟩ := Set.mem_mul.mp hz
    have hxQ : x ∈ Q := by
      have := mul_mem hzQ (inv_mem (hUQ hu))
      rwa [mul_inv_cancel_right] at this
    have hx1 : x = 1 := by
      have : x ∈ X ⊓ Q := mem_inf.mpr ⟨hx, hxQ⟩
      rwa [hXQ, mem_bot] at this
    rw [hx1, one_mul]
    exact hu
  have hcent : ∀ z ∈ X ⊔ U, CentMod (twoPrimeLayerIn Q) (oddCoreIn Q) z → z ∈ X := by
    intro z hz hc
    rw [← SetLike.mem_coe, hXUcoe] at hz
    obtain ⟨x, hx, u, hu, rfl⟩ := Set.mem_mul.mp hz
    have hcu : CentMod (twoPrimeLayerIn Q) (oddCoreIn Q) u := by
      have := ((hXc x hx).inv (hXO hx)).mul hc (inv_mem (hXO hx))
      rwa [inv_mul_cancel_left] at this
    have huO := hF u (hUL hu) (hcu.mono ((oUpperTwoPrime_le C).trans hCK))
    obtain ⟨k, hk⟩ := hU2 ⟨u, hu⟩
    have hu1 := eq_one_of_mem_of_odd (odd_card_oddCoreIn C) huO
      (by simpa using congrArg Subtype.val hk)
    rw [hu1, mul_one]
    exact hx
  obtain ⟨P, hP, hXUP⟩ := AschbacherTheorem3.exists_isSylowOf_le hXU2
    (sup_le le_sup_right (hUQ.trans le_sup_left) : X ⊔ U ≤ Q ⊔ X)
  have hV : IsSylowOf 2 (P ⊓ Q) Q := hP.inf_of_le_normalizer le_sup_left (sup_le le_normalizer hXN)
  suffices h : U = P ⊓ Q by
    rw [h]
    exact hV
  by_contra hne
  have hlt : (X ⊔ U).subgroupOf P < ⊤ := by
    rw [lt_top_iff_ne_top]
    intro htop
    apply hne
    have hPXU : P ≤ X ⊔ U := fun p hp => by
      have : (⟨p, hp⟩ : P) ∈ (X ⊔ U).subgroupOf P := htop ▸ mem_top _
      exact this
    rw [← le_antisymm hXUP hPXU, hXUQ]
  have : Group.IsNilpotent P := hP.isPGroup.isNilpotent
  obtain ⟨w, hwN, hwXU⟩ :=
    IsConcreteLE.exists_of_lt (Group.normalizerCondition_of_isNilpotent (G := P) _ hlt)
  have hwN' : (w : G) ∈ normalizer ((X ⊔ U : Subgroup G) : Set G) := by
    rw [← subgroupOf_normalizer_eq hXUP] at hwN
    exact hwN
  have hwXU' : (w : G) ∉ X ⊔ U := hwXU
  have hwQX : (w : G) ∈ ((X ⊔ Q : Subgroup G) : Set G) := by
    rw [sup_comm]
    exact hP.le w.2
  rw [coe_mul_of_left_le_normalizer_right X Q hXN] at hwQX
  obtain ⟨x, hx, q, hq, hxq⟩ := Set.mem_mul.mp hwQX
  have hqw : q = x⁻¹ * w := by rw [← hxq]; group
  have hqP : q ∈ P := hqw ▸ mul_mem (inv_mem (hXUP (mem_sup_left hx))) w.2
  have hqN : q ∈ normalizer ((X ⊔ U : Subgroup G) : Set G) :=
    hqw ▸ mul_mem (inv_mem (le_normalizer (mem_sup_left hx))) hwN'
  have hqXU : q ∉ X ⊔ U := fun h => hwXU' (by rw [← hxq]; exact mul_mem (mem_sup_left hx) h)
  have hqX : q ∈ normalizer (X : Set G) := by
    rw [mem_normalizer_iff_map_conj_eq]
    refine eq_of_le_of_card_ge ?_ (card_map_of_injective (MulAut.conj q).injective).ge
    rintro _ ⟨y, hy, rfl⟩
    show q * y * q⁻¹ ∈ X
    exact hcent _ ((mem_normalizer_iff.mp hqN y).mp (mem_sup_left hy))
      ((hXc y hy).conj (hKn hq) (hOn hq))
  have hqC : q ∈ centralizer (X : Set G) := mem_centralizer_iff.mpr fun y hy => by
    have h1 : q * y * q⁻¹ * y⁻¹ ∈ X ⊓ Q := by
      refine mem_inf.mpr ⟨mul_mem ((mem_normalizer_iff.mp hqX y).mp hy) (inv_mem hy), ?_⟩
      have : q * y * q⁻¹ * y⁻¹ = q * (y * q⁻¹ * y⁻¹) := by group
      rw [this]
      exact mul_mem hq ((mem_normalizer_iff.mp (hXN hy) _).mp (inv_mem hq))
    rw [hXQ, mem_bot] at h1
    have h2 := mul_inv_eq_one.mp h1
    rw [mul_inv_eq_iff_eq_mul] at h2
    exact h2.symm
  have hqU : q ∈ normalizer (U : Set G) := by
    rw [← hXUQ]
    exact inf_normalizer_le_normalizer_inf (X ⊔ U) Q (mem_inf.mpr ⟨hqN, le_normalizer hq⟩)
  obtain ⟨k, hk⟩ := hP.isPGroup ⟨q, hqP⟩
  have hk' : q ^ (2 ^ k) = 1 := by simpa using congrArg Subtype.val hk
  have hp : IsPGroup 2 (U ⊔ zpowers q : Subgroup G) :=
    hU2.to_sup_of_normal_left' (isPGroup_zpowers_of_pow_eq_one hk') ((zpowers_le).mpr hqU)
  have heq := hU.eq_of_le le_sup_left
    (sup_le hU.le ((zpowers_le).mpr (mem_inf.mpr ⟨hq, hqC⟩))) hp
  exact hqXU (mem_sup_right (heq ▸ mem_sup_right (mem_zpowers q)))

end Faithful

theorem false_of_thm4Case3_centralizer (h3 : AschbacherTheorem3.Theorem3Statement)
    {Q X : Subgroup G} (htight : TightlyEmbedded Q) (h4 : HasFourGroup (twoPrimeLayerIn Q))
    (hno : ¬ Thm4Case3 Q) (hX : IsPGroup 2 X) (hXQ : CoversLayer X Q) {g : G}
    (hgM : g ∈ centralizer (X : Set G))
    (hgY : g ∉ normalizer ((Q ⊓ centralizer (X : Set G) : Subgroup G) : Set G))
    {T : Subgroup G} (hTM : T ≤ centralizer (X : Set G))
    (hT : IsSylowOf 2 T (rightConjugate (Q ⊓ centralizer (X : Set G)) g))
    (hTN : T ≤ normalizer ((Q ⊓ centralizer (X : Set G) : Subgroup G) : Set G)) {n : ℕ}
    (hn : 2 ≤ n)
    (φ : oUpperTwoPrime ((Q ⊓ centralizer (X : Set G)) ⊔ T) →*
      Multiplicative (Fin n → ZMod 2) × Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 n))
    (hφ : Function.Surjective φ)
    (hker : φ.ker = (oddCoreIn (Q ⊓ centralizer (X : Set G))).subgroupOf
      (oUpperTwoPrime ((Q ⊓ centralizer (X : Set G)) ⊔ T))) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hC4 := hasFourGroup_inf_centralizer hXQ h4
  have hCs := isSemisimpleQ_inf_centralizer hXQ
  have hCe := hC4.even_card
  have hCK : twoPrimeLayerIn Q ⊓ centralizer (X : Set G) ≤ twoPrimeLayerIn Q := inf_le_left
  have hCQ : twoPrimeLayerIn Q ⊓ centralizer (X : Set G) ≤ Q :=
    inf_le_left.trans (twoPrimeLayerIn_le Q)
  have hCY : twoPrimeLayerIn Q ⊓ centralizer (X : Set G) ≤ Q ⊓ centralizer (X : Set G) :=
    inf_le_inf_right _ (twoPrimeLayerIn_le Q)
  have hYe : Even (Nat.card (Q ⊓ centralizer (X : Set G) : Subgroup G)) :=
    even_iff_two_dvd.mpr ((even_iff_two_dvd.mp hCe).trans (card_dvd_of_le hCY))
  have hXN : X ≤ normalizer (Q : Set G) := le_normalizer_of_coversLayer htight hCe
  have hXc : ∀ x ∈ X, CentMod (twoPrimeLayerIn Q) (oddCoreIn Q) x :=
    fun x hx => centMod_of_coversLayer hXQ hXN hx
  have hYN : Q ⊓ centralizer (X : Set G) ≤
      normalizer ((twoPrimeLayerIn Q ⊓ centralizer (X : Set G) : Subgroup G) : Set G) :=
    (le_inf inf_le_right (inf_le_left.trans le_normalizer)).trans
      (inf_normalizer_le_normalizer_inf_centralizer X Q)
  have hCn := normalIn_of_le_normalizer hCY hYN
  have hgQ : g ∉ normalizer (Q : Set G) := fun h => hgY (inf_normalizer_le_normalizer_inf Q _
    (mem_inf.mpr ⟨h, le_normalizer hgM⟩))
  have hTQg : T ≤ rightConjugate Q g :=
    hT.le.trans (AschbacherTheorem3.rightConjugate_le_rightConjugate inf_le_left g)
  have hTQ : T ⊓ Q = ⊥ := two_subgroup_inf_conjugate_eq_bot Q T htight hT.isPGroup g hgQ hTQg
  have hTY : T ⊓ (Q ⊓ centralizer (X : Set G)) = ⊥ :=
    eq_bot_iff.mpr ((inf_le_inf_left _ inf_le_left).trans hTQ.le)
  have hTNQ : T ≤ normalizer (Q : Set G) := hTN.trans (normalizer_le_of_even htight inf_le_left hYe)
  have hTC : T ≤ normalizer ((twoPrimeLayerIn Q ⊓ centralizer (X : Set G) : Subgroup G) :
      Set G) := fun t ht =>
    inf_normalizer_le_normalizer_inf_centralizer X Q (mem_inf.mpr ⟨hTM ht, hTNQ ht⟩)
  have hTcard : Nat.card T =
      2 ^ (Nat.card (Q ⊓ centralizer (X : Set G) : Subgroup G)).factorization 2 := by
    rw [hT.card_eq, rightConjugate_card]
  have hfac := factorization_eq_of_surjective hTY hTN hTcard (by omega) φ hφ hker
  have hLV : oUpperTwoPrime (twoPrimeLayerIn Q ⊓ centralizer (X : Set G)) ≤
      oUpperTwoPrime ((Q ⊓ centralizer (X : Set G)) ⊔ T) :=
    oUpperTwoPrime_mono (hCY.trans le_sup_left)
  obtain ⟨hrange, hβker⟩ := range_comp_inclusion_eq_prod hCn hTC hCs hCe hn φ hφ hker hLV
  obtain ⟨hψ, hψker⟩ := snd_comp_of_range_eq_prod _ hrange
  have hψker' := hψker.trans hβker
  have hF : ∀ l ∈ oUpperTwoPrime (twoPrimeLayerIn Q ⊓ centralizer (X : Set G)),
      CentMod (oUpperTwoPrime (twoPrimeLayerIn Q ⊓ centralizer (X : Set G))) (oddCoreIn Q) l →
        l ∈ oddCoreIn (twoPrimeLayerIn Q ⊓ centralizer (X : Set G)) :=
    fun l hl hc => mem_oddCoreIn_of_centMod_self hCQ hψ hψker' hl hc
  have hvC := factorization_card_eq (by omega) hψ hψker'
  obtain ⟨E, hEC, hE, hE4⟩ := hC4
  obtain ⟨U, hUC, -⟩ := AschbacherTheorem3.exists_isSylowOf_le (isPGroup_of_sq_eq_one hE) hEC
  have hUY : IsSylowOf 2 U (Q ⊓ centralizer (X : Set G)) :=
    isSylowOf_of_card (hUC.le.trans hCY) (by rw [hUC.card_eq, hvC, hfac])
  have hUL : U ≤ oUpperTwoPrime (twoPrimeLayerIn Q ⊓ centralizer (X : Set G)) := fun u hu => by
    obtain ⟨k, hk⟩ := hUC.isPGroup ⟨u, hu⟩
    exact subset_closure ⟨hUC.le hu, k, by simpa using congrArg Subtype.val hk⟩
  have hUQ := isSylowOf_of_faithful hX hXN hXc hCK hUY hUL hF
  have hQfac : (Nat.card Q).factorization 2 = n := by
    have h1 := hUQ.card_eq
    rw [hUC.card_eq, hvC] at h1
    exact (Nat.pow_right_injective le_rfl h1).symm
  have hTsyl : IsSylowOf 2 T (rightConjugate Q g) :=
    isSylowOf_of_card hTQg (by rw [hTcard, hfac, rightConjugate_card, hQfac])
  have hTsyl' : IsSylowOf 2 T (rightConjugate Q g ⊓ normalizer (Q : Set G)) :=
    hTsyl.of_le (le_inf hTQg hTNQ) inf_le_left
  obtain ⟨c, -, hcT⟩ := AschbacherTheorem3.exists_rightConjugate_le_of_isSylowOf hT
    ((isPGroup_of_sq_eq_one hE).map (MulAut.conj g⁻¹).toMonoidHom)
    (AschbacherTheorem3.rightConjugate_le_rightConjugate (hEC.trans hCY) g)
  have hT4 : HasFourGroup T := (hasFourGroup_rightConjugate_iff.mpr
    (hasFourGroup_rightConjugate_iff.mpr ⟨E, le_rfl, hE, hE4⟩)).mono hcT
  obtain ⟨E', hE'T, hE', hE'4⟩ := hT4
  rcases commutator_mem_or_thm3Alt3 h3 htight hgQ hTsyl' hE'T hE' hE'4 with hc | halt
  swap
  · exact hno (thm4Case3_of_thm3Alt3 htight hgQ hTsyl' halt)
  have hTV : T ≤ oUpperTwoPrime ((Q ⊓ centralizer (X : Set G)) ⊔ T) := fun t ht => by
    obtain ⟨k, hk⟩ := hT.isPGroup ⟨t, ht⟩
    exact subset_closure ⟨mem_sup_right ht, k, by simpa using congrArg Subtype.val hk⟩
  have hOY : oddCoreIn Q ⊓ centralizer (X : Set G) ≤ oddCoreIn (Q ⊓ centralizer (X : Set G)) :=
    le_oddCoreIn (normalIn_of_le_normalizer (inf_le_inf_right _ (oddCoreIn_le Q))
      ((le_inf (inf_le_left.trans (normalIn_le_normalizer (oddCoreIn_normalIn Q)))
        (inf_le_right.trans le_normalizer)).trans (inf_normalizer_le_normalizer_inf _ _)))
      ((odd_card_oddCoreIn Q).of_dvd_nat (card_dvd_of_le inf_le_left))
  have hsnd : ∀ t : T, (φ (inclusion hTV t)).2 = 1 := by
    intro t
    refine snd_eq_one_of_commute CFSG.Walter.sl2_center_eq_bot_of_charTwo fun s => ?_
    obtain ⟨l, rfl⟩ := hψ s
    have hl : (1, (MonoidHom.snd _ _).comp (φ.comp (inclusion hLV)) l) =
        φ (inclusion hLV l) := by
      refine Prod.ext ?_ rfl
      have hx : φ.comp (inclusion hLV) l ∈ (φ.comp (inclusion hLV)).range := ⟨l, rfl⟩
      rw [hrange] at hx
      exact ((mem_prod.mp hx).1).symm
    rw [hl]
    have hlK : (l : G) ∈ twoPrimeLayerIn Q := ((oUpperTwoPrime_le _).trans hCK) l.2
    have hlM : (l : G) ∈ centralizer (X : Set G) :=
      ((oUpperTwoPrime_le _).trans inf_le_right) l.2
    have h1 : (t : G)⁻¹ * (l : G)⁻¹ * (t : G) * l ∈ oddCoreIn Q := by
      have := hc _ (inv_mem t.2) _ (inv_mem hlK)
      rwa [inv_inv, inv_inv] at this
    have h2 : (t : G)⁻¹ * (l : G)⁻¹ * (t : G) * l ∈ centralizer (X : Set G) :=
      mul_mem (mul_mem (mul_mem (inv_mem (hTM t.2)) (inv_mem hlM)) (hTM t.2)) hlM
    have hmem : (inclusion hLV l * inclusion hTV t)⁻¹ * (inclusion hTV t * inclusion hLV l) ∈
        φ.ker := by
      rw [hker, mem_subgroupOf]
      have h3' := hOY (mem_inf.mpr ⟨h1, h2⟩)
      show ((l : G) * t)⁻¹ * ((t : G) * l) ∈ oddCoreIn (Q ⊓ centralizer (X : Set G))
      simpa [mul_assoc] using h3'
    rw [← map_mul, ← map_mul]
    exact (φ.eq_iff).mpr hmem
  let f : T →* Multiplicative (Fin n → ZMod 2) :=
    (MonoidHom.fst _ _).comp (φ.comp (inclusion hTV))
  have hf : Function.Injective f := by
    rw [injective_iff_map_eq_one]
    intro t ht
    have h1 : φ (inclusion hTV t) = 1 := Prod.ext ht (hsnd t)
    rw [← MonoidHom.mem_ker, hker, mem_subgroupOf] at h1
    obtain ⟨k, hk⟩ := hT.isPGroup t
    have h2 := eq_one_of_mem_of_odd (odd_card_oddCoreIn _) h1
      (by simpa using congrArg Subtype.val hk)
    exact Subtype.ext h2
  have hEsq : ∀ x : Multiplicative (Fin n → ZMod 2), x ^ 2 = 1 := fun x => by
    apply Multiplicative.toAdd.injective
    rw [toAdd_pow, toAdd_one]
    funext i
    simp only [Pi.smul_apply, Pi.zero_apply, two_nsmul]
    exact CharTwo.add_self_eq_zero _
  have hTcomm : ∀ a ∈ T, ∀ b ∈ T, a * b = b * a := fun a ha b hb => by
    have h1 : f (⟨a, ha⟩ * ⟨b, hb⟩) = f (⟨b, hb⟩ * ⟨a, ha⟩) := by
      rw [map_mul, map_mul, mul_comm]
    exact congrArg Subtype.val (hf h1)
  have hTsq : ∀ t ∈ T, t ^ 2 = 1 := fun t ht => by
    have h1 : f (⟨t, ht⟩ ^ 2) = f 1 := by rw [map_pow, hEsq, map_one]
    simpa using congrArg Subtype.val (hf h1)
  exact hno (thm4Case3_of_sl2 htight hCK hXQ hn hψ hψker' hUQ hUL hgQ hTsyl hTNQ
    (fun t ht k hk => hc t ht k hk) hTcomm hTsq (hTcard.trans (by rw [hfac])))

theorem normalIn_of_coversLayer (h3 : AschbacherTheorem3.Theorem3Statement)
    (ih : Thm4BelowWeak (Nat.card G)) {Q : Subgroup G} (htight : TightlyEmbedded Q)
    (h4 : HasFourGroup (twoPrimeLayerIn Q)) (hno : ¬ Thm4Case3 Q) {X : Subgroup G}
    (hX : IsPGroup 2 X) (hXc : centralizer (X : Set G) ≠ ⊤) (hXQ : CoversLayer X Q) :
    NormalIn (twoPrimeLayerIn Q ⊓ centralizer (X : Set G))
      (twoPrimeLayerIn (centralizer (X : Set G))) := by
  have hC4 := hasFourGroup_inf_centralizer hXQ h4
  have hCs := isSemisimpleQ_inf_centralizer hXQ
  have hCY : twoPrimeLayerIn Q ⊓ centralizer (X : Set G) ≤ Q ⊓ centralizer (X : Set G) :=
    inf_le_inf_right _ (twoPrimeLayerIn_le Q)
  have hYM : Q ⊓ centralizer (X : Set G) ≤ centralizer (X : Set G) := inf_le_right
  have hYN : Q ⊓ centralizer (X : Set G) ≤
      normalizer ((twoPrimeLayerIn Q ⊓ centralizer (X : Set G) : Subgroup G) : Set G) :=
    (le_inf inf_le_right (inf_le_left.trans le_normalizer)).trans
      (inf_normalizer_le_normalizer_inf_centralizer X Q)
  have hCL : twoPrimeLayerIn Q ⊓ centralizer (X : Set G) ≤
      twoPrimeLayerIn (Q ⊓ centralizer (X : Set G)) :=
    le_twoPrimeLayerIn_of_normalIn (normalIn_of_le_normalizer hCY hYN) hCs
  have hL4 := hC4.mono hCL
  have hYe : Even (Nat.card (Q ⊓ centralizer (X : Set G) : Subgroup G)) :=
    even_iff_two_dvd.mpr ((even_iff_two_dvd.mp hC4.even_card).trans (card_dvd_of_le hCY))
  have hYMN : centralizer (X : Set G) ⊓ normalizer (Q : Set G) ≤
      normalizer ((Q ⊓ centralizer (X : Set G) : Subgroup G) : Set G) := fun m hm =>
    inf_normalizer_le_normalizer_inf Q _
      (mem_inf.mpr ⟨(mem_inf.mp hm).2, le_normalizer (mem_inf.mp hm).1⟩)
  have htY := tightlyEmbedded_subgroupOf htight inf_le_left hYM hYe hYMN
  have hne : twoPrimeLayerIn ((Q ⊓ centralizer (X : Set G)).subgroupOf (centralizer (X : Set G)))
      ≠ oddCoreIn ((Q ⊓ centralizer (X : Set G)).subgroupOf (centralizer (X : Set G))) := by
    intro h
    have h1 := congrArg (Subgroup.map (centralizer (X : Set G)).subtype) h
    rw [twoPrimeLayerIn_subgroupOf_map hYM, oddCoreIn_subgroupOf_map hYM] at h1
    have h2 := odd_card_oddCoreIn (Q ⊓ centralizer (X : Set G))
    rw [← h1] at h2
    exact Nat.not_even_iff_odd.mpr h2 hL4.even_card
  have hcard : Nat.card (centralizer (X : Set G)) < Nat.card G := by
    rw [← card_top (G := G)]
    exact card_lt_of_lt (lt_top_iff_ne_top.mpr hXc)
  rcases ih _ hcard _ htY hne with h1 | h2 | h3'
  ·
    have h := (normalIn_map_iff (centralizer (X : Set G)).subtype_injective).mpr h1
    rw [twoPrimeLayerIn_subgroupOf_map hYM, twoPrimeLayerIn_top_map] at h
    refine normalIn_of_le_normalizer (hCL.trans h.1) fun x hx => ?_
    have hxQ : x ∈ normalizer (Q : Set G) := normalizer_le_of_even htight
      ((twoPrimeLayerIn_le _).trans inf_le_left) hL4.even_card (normalIn_le_normalizer h hx)
    exact inf_normalizer_le_normalizer_inf_centralizer X Q
      (mem_inf.mpr ⟨twoPrimeLayerIn_le _ hx, hxQ⟩)
  ·
    exfalso
    have h : CFSG.Open.pRank 2 (twoPrimeLayerIn ((Q ⊓ centralizer (X : Set G)).subgroupOf
        (centralizer (X : Set G)))) = 1 := h2
    rw [← pRank_map_subtype, twoPrimeLayerIn_subgroupOf_map hYM] at h
    have := hL4.two_le_pRank
    omega
  ·
    exfalso
    obtain ⟨g, hgM, hgY, T, hTM, hT, hTN, n, hn, φ, hφ, hker⟩ := thm4Case3_subgroupOf hYM h3'
    exact false_of_thm4Case3_centralizer h3 htight h4 hno hX hXQ hgM hgY hTM hT hTN hn φ hφ hker

theorem normalInCentralizers_of_thm4BelowWeak (h3 : AschbacherTheorem3.Theorem3Statement)
    (ih : Thm4BelowWeak (Nat.card G)) {Q : Subgroup G} (htight : TightlyEmbedded Q)
    (h4 : HasFourGroup (twoPrimeLayerIn Q)) (hno : ¬ Thm4Case3 Q) : NormalInCentralizers Q :=
  fun a _ hX hXc hXa => normalIn_of_coversLayer h3 ih (rightConjugate_tightlyEmbedded Q htight a)
    (by rw [twoPrimeLayerIn_rightConjugate]; exact h4.map (MulAut.conj a⁻¹).injective)
    (not_thm4Case3_rightConjugate hno a) hX hXc hXa

end CFSG.ComponentClassification.Asc75T4
