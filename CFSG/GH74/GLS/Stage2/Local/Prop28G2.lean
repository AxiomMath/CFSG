module

public import CFSG.GH74.GLS.Stage2.Local.Prop28Basic
public import CFSG.GH74.GLS.Stage2.Local.Lemma23e
public import CFSG.LocalAnalysis.ComponentInitial.TwoPrimeSolvable

public section

namespace CFSG.GH74.GLS.Stage2.Local.Prop28

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.GH74.GLS.Stage12

theorem card_statedSL_two {F : Type} [Field F] [Finite F] :
    Nat.card (StatedSL 2 F) = Nat.card F * (Nat.card F ^ 2 - 1) :=
  CFSG.Open.StatedAPI.card_statedSL_two F

theorem isSolvable_of_hasSL2Model_three {L : Type} [Group L] (h : HasSL2Model L (fun q => q = 3)) :
    Group.IsSolvable L := by
  obtain ⟨F, hF, hfin, hq, ⟨e⟩⟩ := h
  have : Finite L := Finite.of_equiv (StatedSL 2 F) e.symm.toEquiv
  have hcard : Nat.card L = 2 ^ 3 * 3 := by
    rw [Nat.card_congr e.toEquiv, card_statedSL_two, hq]
    norm_num
  have : (Nat.card L).primeFactors.card ≤ 2 := by
    rw [hcard, Nat.primeFactors_mul (by norm_num) (by norm_num),
      Nat.primeFactors_prime_pow (by norm_num) Nat.prime_two, Nat.Prime.primeFactors Nat.prime_three]
    decide
  exact CFSG.LocalAnalysis.ComponentInitial.isSolvable_of_card_primeFactors_le_two this

theorem le_normalizer_of_comm {Y : Type} [Group Y] {A B : Subgroup Y}
    (h : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a) : B ≤ normalizer (A : Set Y) := fun b hb =>
  (Subgroup.centralizer_le_normalizer (A : Set Y))
    (Subgroup.mem_centralizer_iff.mpr fun a ha => h a ha b hb)

theorem isSubnormal_of_factor {Y : Type} [Group Y] {A B Lb : Subgroup Y} (hsup : A ⊔ B = Lb)
    (hcomm : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a) (hLb : Lb.Normal) : A.IsSubnormal := by
  have hLle : A ≤ Lb := hsup ▸ le_sup_left
  have hN : (A.subgroupOf Lb).Normal := by
    rw [Subgroup.normal_subgroupOf_iff_le_normalizer hLle, ← hsup]
    exact sup_le Subgroup.le_normalizer (le_normalizer_of_comm hcomm)
  exact Subgroup.IsSubnormal.step A Lb hLle (Subgroup.Normal.isSubnormal hLb) hN

theorem compsGood_of_g2 {G : Type} [Group G] [Finite G] {z : G} {S : Subgroup G}
    (h : Stage1G2 G z S) : CompsGood z := by
  obtain ⟨r₁, r₂, L₁, L₂, hr₁, hr₂, hr₁3, ⟨hsup, hcomm, hcard⟩, hsl₁, hsl₂, -, hF3, hFbig, -⟩ :=
    h.shape
  have hcomm' : ∀ b ∈ L₂, ∀ a ∈ L₁, b * a = a * b := fun b hb a ha => (hcomm a ha b hb).symm
  have hsup' : L₂ ⊔ L₁ = LBar z := by rw [sup_comm]; exact hsup
  have hL₁sub : L₁.IsSubnormal := isSubnormal_of_factor hsup hcomm (LBar_normal z)
  have hL₂sub : L₂.IsSubnormal := isSubnormal_of_factor hsup' hcomm' (LBar_normal z)
  have hr₂ge : 3 ≤ r₂ := by
    obtain ⟨F, hF, hfin, hq, -⟩ := hsl₂
    have h2 : 1 < Nat.card F := Finite.one_lt_card
    obtain ⟨k, hk⟩ := hr₂
    omega
  have hFle : generalizedFitting (CentralizerBar z) ≤ LBar z := by
    rcases hr₂ge.eq_or_lt with h3 | h3
    · rw [(hF3 h3.symm).2]
      exact Subgroup.map_subtype_le _
    · exact (hFbig h3).2.le
  intro K hK
  have hKL : K ≤ L₁ ⊔ L₂ :=
    hsup ▸ ((le_sSup hK : K ≤ layer (CentralizerBar z)).trans le_sup_right |>.trans hFle)
  have hsl₁' : IsQuasisimple ↥L₁ := (sl2_model_facts hr₁ (by omega) hsl₁).1
  have good : ∀ {L : Subgroup (CentralizerBar z)} {r : ℕ}, Odd r →
      HasSL2Model ↥L (fun q => q = r) → K = L → Good ↥K := by
    intro L r hr hsl hKL'
    subst hKL'
    obtain ⟨F, hF, hfin, hP, e⟩ := hsl
    exact Or.inr ⟨hK.1, Or.inr (Or.inl ⟨F, hF, hfin, hP ▸ hr, e⟩)⟩
  rcases CFSG.LocalCores.component_subnormal_subgroup hK hL₁sub with hK1 | hc1
  · exact good hr₁ hsl₁ (comp_eq_of_le hK hK1 hsl₁')
  rcases CFSG.LocalCores.component_subnormal_subgroup hK hL₂sub with hK2 | hc2
  · rcases hr₂ge.eq_or_lt with h3 | h3
    · exfalso
      rw [← h3] at hsl₂
      have hs : Group.IsSolvable ↥L₂ := isSolvable_of_hasSL2Model_three hsl₂
      exact false_of_component_isSolvable hK
        (Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective hK2))
    · exact good hr₂ hsl₂ (comp_eq_of_le hK hK2 (sl2_model_facts hr₂ (by omega) hsl₂).1)
  · exfalso
    have hL₁c : L₁ ≤ centralizer (K : Set (CentralizerBar z)) :=
      Subgroup.commutator_eq_bot_iff_le_centralizer.mp (by rw [Subgroup.commutator_comm]; exact hc1)
    have hL₂c : L₂ ≤ centralizer (K : Set (CentralizerBar z)) :=
      Subgroup.commutator_eq_bot_iff_le_centralizer.mp (by rw [Subgroup.commutator_comm]; exact hc2)
    have hKc : K ≤ centralizer (K : Set (CentralizerBar z)) := hKL.trans (sup_le hL₁c hL₂c)
    have hab : ∀ a b : ↥K, a * b = b * a := fun a b =>
      Subtype.ext (Subgroup.mem_centralizer_iff.mp (hKc b.2) a a.2)
    exact false_of_component_isSolvable hK (Group.isSolvable_of_comm hab)

theorem not_l2Meets_inG2_of_g2 {G : Type} [Group G] [Finite G] {z : G} {S : Subgroup G}
    (h : Stage1G2 G z S) (hz : orderOf z = 2) : ¬ L2Meets G InG2 :=
  not_l2Meets_inG2_of_oneClass (compsGood_of_g2 h) fun u hu => h.one_class z u hz hu

end CFSG.GH74.GLS.Stage2.Local.Prop28
