module

public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.Blueprint.SourceClassicalTransport
public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.SeitzReduction.EPilotPosition

public section

namespace CFSG.LocalAnalysis.GLTheoremA.OutCyc

theorem card_le_mul_card_ker_of_cyclic {X Q : Type} [Group X] [Finite X] [Group Q] [Finite Q]
    {A : Subgroup X} (f : A →* Q) (x : Q) (hx : ∀ a : A, f a ∈ Subgroup.zpowers x)
    {p : ℕ} (hp : 0 < p) (hexp : ∀ a : A, a ^ p = 1) :
    Nat.card A ≤ p * Nat.card f.ker := by
  have hrange_le : f.range ≤ Subgroup.zpowers x := by
    rintro _ ⟨a, rfl⟩
    exact hx a
  have hcyc : IsCyclic f.range := Subgroup.isCyclic_of_le hrange_le
  have hexp' : Monoid.exponent f.range ∣ p := by
    rw [Monoid.exponent_dvd_iff_forall_pow_eq_one]
    intro g
    obtain ⟨a, ha⟩ := MonoidHom.mem_range.1 g.2
    apply Subtype.ext
    simp only [SubgroupClass.coe_pow, OneMemClass.coe_one]
    rw [← ha, ← map_pow, hexp a, map_one]
  have hcard : Nat.card f.range ≤ p := by
    rw [← IsCyclic.exponent_eq_card]
    exact Nat.le_of_dvd hp hexp'
  rw [← Subgroup.card_mul_index f.ker, Subgroup.index_ker, mul_comm p]
  exact Nat.mul_le_mul_left _ hcard

theorem index_le_core {G : Type} [Group G] [Finite G] {R : Type} [Group R] [Finite (MulAut R)]
    {N A : Subgroup G} (hAN : A ≤ N) (ψ : N →* MulAut R)
    {p : ℕ} (hp : 0 < p) (hexp : ∀ a ∈ A, a ^ p = 1)
    {S J : Subgroup (MulAut R)} (hJS : J ≤ S) (hJn : (J.subgroupOf S).Normal)
    {g : MulAut R} (hg : g ∈ S) (hψS : ∀ (a : G) (ha : a ∈ A), ψ ⟨a, hAN ha⟩ ∈ S)
    (hgen : ∀ (a : G) (ha : a ∈ A), ∃ k : ℤ, g ^ k * ψ ⟨a, hAN ha⟩ ∈ J) :
    ∃ A₀ : Subgroup G, A₀ ≤ A ∧ (∀ (a : G) (ha : a ∈ A), a ∈ A₀ ↔ ψ ⟨a, hAN ha⟩ ∈ J) ∧
      Nat.card A ≤ p * Nat.card A₀ := by
  let ψA : A →* MulAut R := ψ.comp (Subgroup.inclusion hAN)
  have hψA : ∀ a : A, ψA a ∈ S := fun a => hψS a.1 a.2
  let fQ : A →* S ⧸ J.subgroupOf S :=
    (QuotientGroup.mk' (J.subgroupOf S)).comp (ψA.codRestrict S hψA)
  let x : S ⧸ J.subgroupOf S := QuotientGroup.mk ⟨g, hg⟩
  have hfQ : ∀ a : A, fQ a = QuotientGroup.mk ⟨ψA a, hψA a⟩ := fun a => rfl
  have hx : ∀ a : A, fQ a ∈ Subgroup.zpowers x := by
    intro a
    obtain ⟨k, hk⟩ := hgen a.1 a.2
    rw [hfQ]
    have hmem : (⟨g, hg⟩ : S) ^ k * ⟨ψA a, hψA a⟩ ∈ J.subgroupOf S := by
      rw [Subgroup.mem_subgroupOf]
      exact hk
    have h1 : (QuotientGroup.mk ((⟨g, hg⟩ : S) ^ k * ⟨ψA a, hψA a⟩) : S ⧸ J.subgroupOf S) = 1 :=
      (QuotientGroup.eq_one_iff _).2 hmem
    rw [QuotientGroup.mk_mul, QuotientGroup.mk_zpow] at h1
    have h2 : (QuotientGroup.mk ⟨ψA a, hψA a⟩ : S ⧸ J.subgroupOf S) = x ^ (-k) := by
      rw [zpow_neg, eq_inv_iff_mul_eq_one, mul_eq_one_comm]
      exact h1
    rw [h2]
    exact Subgroup.zpow_mem_zpowers x _
  have hexp' : ∀ a : A, a ^ p = 1 := fun a => Subtype.ext (by
    rw [SubgroupClass.coe_pow]
    simpa using hexp a.1 a.2)
  have hcard := card_le_mul_card_ker_of_cyclic fQ x hx hp hexp'
  refine ⟨fQ.ker.map A.subtype, ?_, ?_, ?_⟩
  · exact Subgroup.map_subtype_le _
  · intro a ha
    rw [Subgroup.mem_map]
    constructor
    · rintro ⟨⟨b, hb⟩, hbk, hba⟩
      change b = a at hba
      subst hba
      rw [MonoidHom.mem_ker, hfQ, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf] at hbk
      exact hbk
    · intro h
      refine ⟨⟨a, ha⟩, ?_, rfl⟩
      rw [MonoidHom.mem_ker, hfQ, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
      exact h
  · rw [Subgroup.card_map_of_injective A.subtype_injective]
    exact hcard

end CFSG.LocalAnalysis.GLTheoremA.OutCyc

end
