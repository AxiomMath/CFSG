module


public import CFSG.LocalAnalysis.RankThreeUC.Section5.ActionVocabulary

public section

namespace CFSG.LocalAnalysis.RankThreeUC.Section5.BstarFaithful

open CFSG.LocalAnalysis.RankThreeUC.Section5

variable {G : Type} [Group G] [Finite G]

@[expose] noncomputable def bAction {p : ℕ} {P T B : Subgroup G} {e : ℕ} (h51 : OddPrimeClassTwoAction G p P T B e) :
    B →* MulAut P :=
  P.normalizerMonoidHom.comp (Subgroup.inclusion h51.setting.normB)

theorem injective {p : ℕ} {P T B : Subgroup G} {e : ℕ} {V : Type} [AddCommGroup V]
    [Module (ZMod 2) V] {ρ : Representation (ZMod 2) G V}
    (h51 : OddPrimeClassTwoAction G p P T B e) (h53 : FaithfulBinaryIrreducibleAction G p P T B ρ) :
    Function.Injective (bAction h51) := by
  have bAction_apply {p : ℕ} {P T B : Subgroup G} {e : ℕ} (h51 : OddPrimeClassTwoAction G p P T B e)
      (b : B) (x : P) : ((bAction h51 b) x : G) = (b : G) * x * (b : G)⁻¹ := rfl
  have pRank_le_one_of_isCyclic {p : ℕ} (hp : p.Prime) {P : Subgroup G} (hP : IsCyclic P) :
      CFSG.Open.pRank p P ≤ 1 := by
    unfold CFSG.Open.pRank
    apply csSup_le'
    rintro k ⟨E, hEP, ⟨-, hexp⟩, hcard⟩
    have hEc : IsCyclic E := by
      have : IsCyclic (E.subgroupOf P) := inferInstance
      exact isCyclic_of_surjective (Subgroup.subgroupOfEquivOfLe hEP).toMonoidHom (Subgroup.subgroupOfEquivOfLe hEP).surjective
    obtain ⟨g, hg⟩ := hEc.exists_generator
    have h1 : orderOf g = Nat.card E := orderOf_eq_card_of_forall_mem_zpowers hg
    have h2 : orderOf g ∣ p := by
      apply orderOf_dvd_of_pow_eq_one
      exact Subtype.ext (hexp g g.2)
    rw [h1, hcard] at h2
    have : p ^ k ∣ p ^ 1 := by simpa using h2
    exact (Nat.pow_dvd_pow_iff_le_right hp.one_lt).mp this
  rw [injective_iff_map_eq_one]
  intro b hb
  by_contra hne
  have hb1 : (b : G) ≠ 1 := fun h => hne (Subtype.ext h)
  have hle : P ≤ Subgroup.centralizer ({(b : G)} : Set G) := by
    intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    rw [Set.mem_singleton_iff] at hy
    subst hy
    have := congrArg (fun f : MulAut P => (f ⟨x, hx⟩ : G)) hb
    simp only [bAction_apply, MulAut.one_apply] at this
    rw [mul_inv_eq_iff_eq_mul] at this
    exact this
  have hcyc := h51.cyclic_centralizer b b.2 hb1
  rw [inf_eq_left.mpr hle] at hcyc
  have := pRank_le_one_of_isCyclic h51.setting.prime hcyc
  have := h53.rank_gt
  omega

theorem range_eq {p : ℕ} {P T B : Subgroup G} {e : ℕ} (h51 : OddPrimeClassTwoAction G p P T B e) :
    Bstar P B = (bAction h51).range := by
  ext σ
  simp only [Bstar, bAction, Subgroup.mem_map, MonoidHom.mem_range, MonoidHom.coe_comp,
    Function.comp_apply]
  constructor
  · rintro ⟨n, hn, rfl⟩
    exact ⟨⟨n.1, hn⟩, rfl⟩
  · rintro ⟨b, rfl⟩
    exact ⟨Subgroup.inclusion h51.setting.normB b, b.2, rfl⟩

theorem card_eq {p : ℕ} {P T B : Subgroup G} {e : ℕ} {V : Type} [AddCommGroup V]
    [Module (ZMod 2) V] {ρ : Representation (ZMod 2) G V}
    (h51 : OddPrimeClassTwoAction G p P T B e) (h53 : FaithfulBinaryIrreducibleAction G p P T B ρ) :
    Nat.card (Bstar P B) = Nat.card B := by
  rw [range_eq h51]
  exact (Nat.card_congr (MonoidHom.ofInjective (injective h51 h53)).toEquiv).symm

theorem bAction_apply {G : Type} [Group G] [Finite G] {p : ℕ} {P T B : Subgroup G}
    {e : ℕ} (h51 : OddPrimeClassTwoAction G p P T B e) (b : B) (x : P) :
    ((bAction h51 b) x : G) = (b : G) * x * (b : G)⁻¹ := rfl

end CFSG.LocalAnalysis.RankThreeUC.Section5.BstarFaithful
