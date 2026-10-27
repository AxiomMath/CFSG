module

import CFSG.RankThree.Classical.SteinbergBJOddSymplecticOuterOrder
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.KlingenSpFourModel
public import CFSG.LocalAnalysis.ComponentInitial.SymplecticFlagOrder
import CFSG.Fischer.Classification.Recognition.PSU6
import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs

open CFSG.ComponentClassification.OuterAutomorphisms CFSG.AGLEmbedding.KlingenSpFour
  CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag

theorem card_quotient_dvd_card_outer {Y : Type} [Group Y] [Finite Y] (K : Subgroup Y)
    [K.Normal] (hC : Subgroup.centralizer (K : Set Y) = ⊥) :
    Nat.card (Y ⧸ K) ∣ Nat.card (Outer K) := by
  let ψ : Y →* Outer K :=
    (QuotientGroup.mk' (inner K)).comp (MulAut.conjNormal : Y →* MulAut K)
  have hker : ψ.ker = K := by
    ext y
    rw [MonoidHom.mem_ker]
    constructor
    · intro h
      have h1 : (MulAut.conjNormal y : MulAut K) ∈ inner K := (QuotientGroup.eq_one_iff _).mp h
      obtain ⟨k, hk⟩ := h1
      have hz : (k : Y)⁻¹ * y ∈ Subgroup.centralizer (K : Set Y) := by
        rw [Subgroup.mem_centralizer_iff]
        intro x hx
        have h2 := congrArg (fun α : MulAut K => ((α ⟨x, hx⟩ : K) : Y)) hk
        simp only [MulAut.conj_apply, MulAut.conjNormal_apply, Subgroup.coe_mul,
          InvMemClass.coe_inv] at h2
        calc x * ((k : Y)⁻¹ * y) = (k : Y)⁻¹ * ((k : Y) * x * (k : Y)⁻¹) * y := by group
          _ = (k : Y)⁻¹ * (y * x * y⁻¹) * y := by rw [h2]
          _ = (k : Y)⁻¹ * y * x := by group
      rw [hC, Subgroup.mem_bot, inv_mul_eq_one] at hz
      exact hz ▸ k.2
    · intro hy
      refine (QuotientGroup.eq_one_iff _).mpr ⟨⟨y, hy⟩, ?_⟩
      rw [← MulAut.conjNormal_val]
  have h1 : Nat.card (Y ⧸ K) = Nat.card ψ.range :=
    (Nat.card_congr (QuotientGroup.quotientMulEquivOfEq hker.symm).toEquiv).trans
      (Nat.card_congr (QuotientGroup.quotientKerEquivRange ψ).toEquiv)
  rw [h1]
  exact Subgroup.card_subgroup_dvd_card _

theorem card_outer_psp4_dvd_two (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) :
    Nat.card (Outer (PSp4 p)) ∣ 2 := by
  have hp : p.Prime := Fact.out
  have hK : Nat.card (ZMod p) = p ^ 1 := by rw [Nat.card_zmod, pow_one]
  have h := (CFSG.RankThree.Classical.odd_symplectic_outer_order_divides_field_multiplier_bound
    (r := 2) hp hp2 le_rfl le_rfl hK).1
  rw [one_mul] at h
  exact h.trans (Nat.gcd_dvd_left 2 _)

theorem card_quotient_dvd_two_of_psp4 {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) {Y : Type} [Group Y]
    [Finite Y] (K : Subgroup Y) [K.Normal] (hC : Subgroup.centralizer (K : Set Y) = ⊥)
    (ψ : K ≃* PSp4 p) : Nat.card (Y ⧸ K) ∣ 2 := by
  refine (card_quotient_dvd_card_outer K hC).trans ?_
  rw [Nat.card_congr (equivalence ψ).toEquiv]
  exact card_outer_psp4_dvd_two p hp2

theorem isSolvable_of_card_dvd_two {G : Type} [Group G] [Finite G] (h : Nat.card G ∣ 2) :
    Group.IsSolvable G := by
  rcases (Nat.dvd_prime Nat.prime_two).mp h with h1 | h2
  · have : Subsingleton G := (Nat.card_eq_one_iff_unique.mp h1).1
    infer_instance
  · have : Fact (Nat.card G).Prime := ⟨h2 ▸ Nat.prime_two⟩
    have : IsCyclic G := isCyclic_of_prime_card h2
    letI : CommGroup G := IsCyclic.commGroup
    exact Group.isSolvable_of_comm fun a b => mul_comm a b

theorem le_of_isPGroup_of_not_dvd_card_quotient {p : ℕ} [Fact p.Prime] {Y : Type} [Group Y]
    [Finite Y] (K : Subgroup Y) [K.Normal] {T : Subgroup Y} (hT : IsPGroup p T)
    (h : ¬ p ∣ Nat.card (Y ⧸ K)) : T ≤ K := by
  have hp : p.Prime := Fact.out
  have hmap : IsPGroup p (T.map (QuotientGroup.mk' K)) := hT.map _
  obtain ⟨n, hn⟩ := hmap.exists_card_eq
  have hdvd : Nat.card (T.map (QuotientGroup.mk' K)) ∣ Nat.card (Y ⧸ K) :=
    Subgroup.card_subgroup_dvd_card _
  have hn0 : n = 0 := by
    by_contra hn0
    exact h ((dvd_pow_self p hn0).trans (hn ▸ hdvd))
  have hbot : T.map (QuotientGroup.mk' K) = ⊥ :=
    Subgroup.eq_bot_of_card_eq _ (by rw [hn, hn0, pow_zero])
  intro x hx
  have : QuotientGroup.mk' K x ∈ T.map (QuotientGroup.mk' K) := ⟨x, hx, rfl⟩
  rw [hbot, Subgroup.mem_bot, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at this
  exact this

variable {p : ℕ} [Fact p.Prime]

theorem exists_mulEquiv_map_projUnipotent {Y : Type} [Group Y] [Finite Y] {K : Subgroup Y}
    [K.Normal] (ψ : K ≃* PSp4 p) (T : Sylow p Y) (hTK : (T : Subgroup Y) ≤ K) :
    ∃ Ψ : K ≃* PSp4 p, ((T : Subgroup Y).subgroupOf K).map Ψ.toMonoidHom =
      projUnipotent 2 (ZMod p) := by
  obtain ⟨Tstd, hTstd⟩ := exists_sylow_projUnipotent (K := ZMod p) p (r := 2) (by norm_num)
  have hψs : Function.Surjective ψ.toMonoidHom := ψ.surjective
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (PSp4 p) ((T.subtype hTK).mapSurjective hψs) Tstd
  refine ⟨ψ.trans (MulAut.conj g), ?_⟩
  have h1 := congrArg (fun P : Sylow p (PSp4 p) => (P : Subgroup (PSp4 p))) hg
  simp only [Sylow.coe_subgroup_smul] at h1
  rw [← hTstd, ← h1, Sylow.coe_mapSurjective, Sylow.coe_subtype, Subgroup.pointwise_smul_def]
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨ψ y, ⟨y, hy, rfl⟩, rfl⟩
  · rintro ⟨_, ⟨y, hy, rfl⟩, rfl⟩
    exact ⟨y, hy, rfl⟩

theorem exists_embedding {Y : Type} [Group Y] [Finite Y] {K : Subgroup Y} [K.Normal]
    (ψ : K ≃* PSp4 p) (T : Sylow p Y) (hTK : (T : Subgroup Y) ≤ K) :
    ∃ ι : PSp4 p →* Y, Function.Injective ι ∧ ι.range = K ∧
      (projUnipotent 2 (ZMod p)).map ι = (T : Subgroup Y) := by
  obtain ⟨Ψ, hΨ⟩ := exists_mulEquiv_map_projUnipotent ψ T hTK
  refine ⟨K.subtype.comp Ψ.symm.toMonoidHom, K.subtype_injective.comp Ψ.symm.injective, ?_, ?_⟩
  · ext y
    constructor
    · rintro ⟨x, rfl⟩
      exact (Ψ.symm x).2
    · intro hy
      exact ⟨Ψ ⟨y, hy⟩, by simp⟩
  · rw [← hΨ, Subgroup.map_map]
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      simpa using Subgroup.mem_subgroupOf.mp hx
    · intro hy
      exact ⟨⟨y, hTK hy⟩, hy, by simp⟩

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs
