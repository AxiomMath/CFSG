module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.T1428Facts
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T1428Trans
public import CFSG.LocalAnalysis.GLTheoremA.P51.Conj
public import CFSG.HardMathSupport.Solomon.LocalBalance.Components

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T1428

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open scoped commutatorElement

private theorem k_normalizer_inf {Ω : Type} [Group Ω] {K : Subgroup Ω} {y b : Ω}
    (hbK : b ∈ Subgroup.normalizer (K : Set Ω)) (hby : Commute b y) :
    b ∈ Subgroup.normalizer ((K ⊓ Subgroup.centralizer ({y} : Set Ω) : Subgroup Ω) : Set Ω) := by
  rw [Subgroup.mem_normalizer_iff]
  intro h
  have hK' := (Subgroup.mem_normalizer_iff.1 hbK) h
  rw [Subgroup.mem_inf, Subgroup.mem_inf, Subgroup.mem_centralizer_singleton_iff,
    Subgroup.mem_centralizer_singleton_iff]
  have hc : Commute (b * h * b⁻¹) y ↔ Commute h y := by
    constructor
    · intro H
      have H' : Commute (b⁻¹ * (b * h * b⁻¹) * b) y := (hby.inv_left.mul_left H).mul_left hby
      have e : b⁻¹ * (b * h * b⁻¹) * b = h := by group
      rw [e] at H'
      exact H'
    · intro H
      exact ((hby.mul_left H).mul_left hby.inv_left)
  change h ∈ K ∧ Commute h y ↔ b * h * b⁻¹ ∈ K ∧ Commute (b * h * b⁻¹) y
  rw [hc]
  exact and_congr hK' Iff.rfl

private theorem k_three_conj {Ω : Type} [Group Ω] [Finite Ω] {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {B M : Subgroup Ω} {k : ℕ} (hB : Nat.card B = p ^ k) (hnot : ¬ B ≤ Subgroup.normalizer (M : Set Ω)) :
    ∃ b₁ ∈ B, ∃ b₂ ∈ B, GLBConj b₁ M ≠ M ∧ GLBConj b₂ M ≠ M ∧ GLBConj b₂ M ≠ GLBConj b₁ M := by
  obtain ⟨b₁, hb₁B, hb₁⟩ := SetLike.not_le_iff_exists.1 hnot
  have hb₁' : GLBConj b₁ M ≠ M := fun h => hb₁ (mem_normalizer_iff_gLBConj_eq.2 h)
  refine ⟨b₁, hb₁B, ?_⟩
  by_contra hcon
  have hall : ∀ b ∈ B, GLBConj b M = M ∨ GLBConj b M = GLBConj b₁ M := by
    intro b hb
    by_contra hne
    obtain ⟨hne1, hne2⟩ := not_or.1 hne
    exact hcon ⟨b, hb, hb₁', hne1, hne2⟩
  have hmemH : ∀ x : B, x ∈ (Subgroup.normalizer (M : Set Ω)).subgroupOf B ↔
      GLBConj (x : Ω) M = M := fun x => by
    rw [Subgroup.mem_subgroupOf, mem_normalizer_iff_gLBConj_eq]
  have hidx : ((Subgroup.normalizer (M : Set Ω)).subgroupOf B).index = 2 := by
    refine Subgroup.index_eq_two_iff.2 ⟨⟨b₁, hb₁B⟩⁻¹, fun b => ?_⟩
    rw [hmemH, hmemH, Subgroup.coe_mul, Subgroup.coe_inv]
    have key : GLBConj ((b : Ω) * b₁⁻¹) M = GLBConj b₁⁻¹ (GLBConj (b : Ω) M) :=
      (gLBConj_gLBConj b₁⁻¹ (b : Ω) M).symm
    rcases hall (b : Ω) b.2 with h1' | h1'
    · have hne : GLBConj ((b : Ω) * b₁⁻¹) M ≠ M := by
        rw [key, h1']
        intro h
        apply hb₁'
        have := gLBConj_gLBConj b₁ b₁⁻¹ M
        rw [h, inv_mul_cancel, gLBConj_one] at this
        exact this
      exact Or.inr ⟨h1', hne⟩
    · have heq : GLBConj ((b : Ω) * b₁⁻¹) M = M := by
        rw [key, h1', gLBConj_gLBConj b₁⁻¹ b₁ M, mul_inv_cancel, gLBConj_one]
      exact Or.inl ⟨heq, by rw [h1']; exact fun h => hb₁' h⟩
  have h2 : ((Subgroup.normalizer (M : Set Ω)).subgroupOf B).index ∣ p ^ k := by
    rw [← hB]
    exact Subgroup.index_dvd_card _
  rw [hidx] at h2
  have h3 : 2 ∣ p := Nat.Prime.dvd_of_dvd_pow Nat.prime_two h2
  exact hp2 ((Nat.prime_dvd_prime_iff_eq Nat.prime_two hp).1 h3).symm

private theorem k_L2_of_weak (i : TauCeti.CFSGIndex) (hi : weakExcIndex i) (hex : ¬ excIndex i) :
    ∃ r : ℕ, Odd r ∧ 1 < r ∧ S10.isL2n r i := by
  unfold weakExcIndex at hi
  rcases hi with h | h
  · exact absurd h hex
  · rcases i with ⟨p, hp⟩ | ⟨d, hd⟩ | ⟨⟨t, ht⟩⟩ | s
    · exact (h : False).elim
    · exact (h : False).elim
    · cases t with
      | A n q =>
        rcases n with _ | _ | n
        · exact (h : False).elim
        · refine ⟨q.exponent, h.2.1, h.2.2, ?_⟩
          show q.p = 2 ∧ q.exponent = q.exponent
          exact ⟨h.1, rfl⟩
        · exact (h : False).elim
      | _ => exact (h : False).elim
    · exact (h : False).elim

private theorem k_weak_cases {S : Type} [Group S] (h : catalogIs S weakExcIndex) :
    catalogIs S excIndex ∨ ∃ r : ℕ, Odd r ∧ 1 < r ∧ catalogIs S (S10.isL2n r) := by
  obtain ⟨i, hi, ⟨e⟩⟩ := h
  by_cases hex : excIndex i
  · exact Or.inl ⟨i, hex, ⟨e⟩⟩
  · right
    obtain ⟨r, hr1, hr2, hr3⟩ := k_L2_of_weak i hi hex
    exact ⟨r, hr1, hr2, ⟨i, hr3, ⟨e⟩⟩⟩

theorem t1428Core_of_facts (hNorm : T1428NormFact) (hType : T1428TypeFact) (hNonInn : T1428NonInnFact)
    (hField : T1428FieldFact) (hChev : T1428ChevFact) (hYS08 : YS08) (hExc : T1428ExcFact)
    (hU6 : T1428U6Fact) (hD4 : T1428D4Fact) (Ω : Type) [Group Ω] [Finite Ω]
    (hΩ : CFSG.Open.IsKGroup Ω) :
    ∀ p : ℕ, p.Prime → p ≠ 2 → ∀ (B K : Subgroup Ω),
      GLAIsBmax p B → GLAPComponent p ⊤ K → IsChevSimple 2 (PSimple p K) →
      GLAMarking (PQuot p K) (fun lab _ _ _ _ _ => p ∣ lab.n) →
      B ≤ Subgroup.normalizer (K : Set Ω) ∧ ∀ y ∈ B, y ≠ 1 →
        ((∀ M : Subgroup Ω, GLAPComponent p (K ⊓ Subgroup.centralizer ({y} : Set Ω)) M →
            B ≤ Subgroup.normalizer (M : Set Ω)) ∨
          (p = 3 ∧ ∃ m : ℕ, Odd m ∧ 1 < m ∧ catalogIs (PSimple 3 K) (S10.isU6n m) ∧
            ∀ M : Subgroup Ω, GLAPComponent 3 (K ⊓ Subgroup.centralizer ({y} : Set Ω)) M →
              catalogIs (PSimple 3 M) (S10.isL2n m))) := by
  intro p hp hp2 B K hBmax hK hKchev hmark
  obtain ⟨hBel, hcard, -⟩ := glaIsBmax_iff.1 hBmax
  have hrankX : GLATwoLocalRank p Ω ≤ CFSG.Open.pRank p B :=
    CFSG.SectionRank.le_pRank hp.one_lt le_rfl hBel hcard
  have hBK : B ≤ Subgroup.normalizer (K : Set Ω) := by
    by_contra hnot
    obtain ⟨rfl, -, hcat⟩ := hNorm p hp hp2 Ω hΩ B K hBmax hK hnot
    exact hExc (PQuot 3 K) hcat hKchev hmark
  refine ⟨hBK, ?_⟩
  intro y hyB hy1
  by_cases hall : ∀ M : Subgroup Ω, GLAPComponent p (K ⊓ Subgroup.centralizer ({y} : Set Ω)) M →
      B ≤ Subgroup.normalizer (M : Set Ω)
  · exact Or.inl hall
  right
  obtain ⟨M₁, hM₁, hnM₁⟩ : ∃ M : Subgroup Ω, GLAPComponent p (K ⊓ Subgroup.centralizer ({y} : Set Ω)) M ∧
      ¬ B ≤ Subgroup.normalizer (M : Set Ω) := by
    by_contra hc
    exact hall (fun M hM => by
      by_contra hne
      exact hc ⟨M, hM, hne⟩)
  have hyp : y ^ p = 1 := hBel.2 y hyB
  have hcomm : ∀ b ∈ B, Commute b y := fun b hb => isElemAbelian_commute hBel hb hyB
  have hyN : y ∈ Subgroup.normalizer (K : Set Ω) := hBK hyB
  have hBC : B ≤ Subgroup.normalizer ((K ⊓ Subgroup.centralizer ({y} : Set Ω) : Subgroup Ω) : Set Ω) :=
    fun b hb => k_normalizer_inf (hBK hb) (hcomm b hb)
  have hsub : CFSG.Open.IsSubnormal (K ⊓ Subgroup.centralizer ({y} : Set Ω))
      ((K ⊓ Subgroup.centralizer ({y} : Set Ω)) ⊔ B) :=
    CFSG.Open.IsSubnormal.step le_sup_left
      ((Subgroup.normal_subgroupOf_iff_le_normalizer le_sup_left).2
        (sup_le Subgroup.le_normalizer hBC))
      (CFSG.Open.IsSubnormal.refl _)
  have hM₁X' : GLAPComponent p ((K ⊓ Subgroup.centralizer ({y} : Set Ω)) ⊔ B) M₁ :=
    glaPComponent_of_isSubnormal' hp hsub hM₁
  have hBX' : B ≤ (K ⊓ Subgroup.centralizer ({y} : Set Ω)) ⊔ B := le_sup_right
  have hX'K : CFSG.Open.IsKGroup ↥((K ⊓ Subgroup.centralizer ({y} : Set Ω)) ⊔ B) :=
    CFSG.Open.IsKGroup.subgroup hΩ _
  have hrankX' : GLATwoLocalRank p ↥((K ⊓ Subgroup.centralizer ({y} : Set Ω)) ⊔ B) ≤
      CFSG.Open.pRank p (B.subgroupOf ((K ⊓ Subgroup.centralizer ({y} : Set Ω)) ⊔ B)) := by
    rw [pRank_subgroupOf_eq hBX']
    exact (twoLocalRank_le_subgroup hp _).trans hrankX
  have hB''el : IsElemAbelian p (B.subgroupOf ((K ⊓ Subgroup.centralizer ({y} : Set Ω)) ⊔ B)) :=
    isElemAbelian_subgroupOf_of hBel
  have hM₁'' : GLAPComponent p ⊤ (M₁.subgroupOf ((K ⊓ Subgroup.centralizer ({y} : Set Ω)) ⊔ B)) :=
    glaPComponent_top_of hp hM₁X'
  have hnM₁'' : ¬ B.subgroupOf ((K ⊓ Subgroup.centralizer ({y} : Set Ω)) ⊔ B) ≤
      Subgroup.normalizer ((M₁.subgroupOf ((K ⊓ Subgroup.centralizer ({y} : Set Ω)) ⊔ B) :
        Subgroup ↥((K ⊓ Subgroup.centralizer ({y} : Set Ω)) ⊔ B)) : Set ↥((K ⊓ Subgroup.centralizer ({y} : Set Ω)) ⊔ B)) := by
    intro h
    exact hnM₁ ((le_normalizer_subgroupOf_iff hBX' hM₁X'.1).1 h)
  obtain ⟨hp3, hcat'⟩ := hType p hp hp2 ↥((K ⊓ Subgroup.centralizer ({y} : Set Ω)) ⊔ B) hX'K
    (B.subgroupOf ((K ⊓ Subgroup.centralizer ({y} : Set Ω)) ⊔ B))
    (M₁.subgroupOf ((K ⊓ Subgroup.centralizer ({y} : Set Ω)) ⊔ B)) hB''el hrankX' hM₁'' hnM₁''
  obtain ⟨eM⟩ := nonempty_pSimple_subgroupOf p hM₁X'.1
  have hcatM₁ : catalogIs (PSimple p M₁) weakExcIndex := (catalogIs_congr eM).1 hcat'
  subst hp3
  obtain ⟨b₁, hb₁, b₂, hb₂, h1, h2, h3⟩ := k_three_conj hp hp2 hcard hnM₁
  have hCb : ∀ b ∈ B, GLBConj b (K ⊓ Subgroup.centralizer ({y} : Set Ω)) =
      K ⊓ Subgroup.centralizer ({y} : Set Ω) :=
    fun b hb => mem_normalizer_iff_gLBConj_eq.1 (hBC hb)
  have hconjComp : ∀ b ∈ B, GLAPComponent 3 (K ⊓ Subgroup.centralizer ({y} : Set Ω))
      (GLBConj b M₁) := fun b hb => by
    have := CFSG.HardMathSupport.Solomon.LocalBalance.glaPComponent_gLBConj b hM₁
    rwa [hCb b hb] at this
  have hcatConj : ∀ (b : Ω) (Q : TauCeti.CFSGIndex → Prop), catalogIs (PSimple 3 M₁) Q →
      catalogIs (PSimple 3 (GLBConj b M₁)) Q := by
    intro b Q h
    obtain ⟨e₁⟩ := CFSG.LocalAnalysis.GLTheoremA.P51.nonempty_pQuot_gLBConj 3 b M₁
    obtain ⟨e₂⟩ := nonempty_pSimple_congr e₁
    exact (catalogIs_congr e₂).2 h
  have hInn : S10.InnDiagOn 3 (Subgroup.zpowers y) K := by
    by_contra hni
    have hJeq := hNonInn 3 hp hp2 Ω hΩ K y hK hKchev hyp ⟨hyN, hni⟩ M₁ (GLBConj b₁ M₁) hM₁
      (hconjComp b₁ hb₁)
    exact h1 hJeq.symm
  have hMchev : IsChevSimple 2 (PSimple 3 M₁) := hChev Ω hΩ K y hK hyp hyN hKchev M₁ hM₁
  have hMmark : GLAMarking (PQuot 3 M₁) (fun lab _ _ _ _ _ => 3 ∣ lab.n) :=
    hField 3 hp hp2 Ω hΩ K y hK hKchev hyp hyN hInn hmark M₁ hM₁
      (hYS08 (PQuot 3 M₁) (isQuasisimple_pQuot_of_glaPComponent hp hM₁) hMchev)
  have hnotexc : ¬ catalogIs (PSimple 3 M₁) excIndex := fun hex => hExc (PQuot 3 M₁) hex hMchev hMmark
  obtain ⟨r, hr_odd, hr_gt, hcatL2⟩ : ∃ r : ℕ, Odd r ∧ 1 < r ∧
      catalogIs (PSimple 3 M₁) (S10.isL2n r) := by
    rcases k_weak_cases hcatM₁ with hex | h
    · exact absurd hex hnotexc
    · exact h
  have hcfg : T1428Config Ω K B y M₁ (GLBConj b₁ M₁) (GLBConj b₂ M₁) r := by
    unfold T1428Config
    exact ⟨hΩ, hBmax, hK, hKchev, hmark, hyB, hy1, hInn, hr_odd, hr_gt,
      h1.symm, h2.symm, h3.symm, hM₁, hconjComp b₁ hb₁, hconjComp b₂ hb₂,
      hcatL2, hcatConj b₁ _ hcatL2, hcatConj b₂ _ hcatL2⟩
  rcases hU6 Ω K B y M₁ (GLBConj b₁ M₁) (GLBConj b₂ M₁) r hcfg hnM₁ with hU | hD
  · exact ⟨rfl, r, hr_odd, hr_gt, hU.1, hU.2⟩
  · exact absurd (hD4 Ω K B y M₁ (GLBConj b₁ M₁) (GLBConj b₂ M₁) r hcfg hD) hnM₁

end CFSG.LocalAnalysis.GLTheoremA.T1428

end
