module

public import CFSG.Timmesfeld.Orders.ClassicalLinear
public import CFSG.Timmesfeld.Transvection.PresSp
public import CFSG.LocalAnalysis.ComponentClassification.OuterAutomorphisms
public import CFSG.LocalAnalysis.QuasithinUnique.Defs

public section

namespace CFSG.QuasithinUnique.Lin2.Five

open CFSG.Assembly.LowTwoRank CFSG.Open

section

variable (F : Type) [Field F]

@[expose] noncomputable def projEquiv [CharP F 2] : StatedSp 2 F ≃* StatedProj (StatedSp 2 F) :=
  MulEquiv.ofBijective
    (QuotientGroup.mk' ((StatedScalars (Fin 2 ⊕ Fin 2) F).subgroupOf (StatedSp 2 F)))
    ⟨by
      rw [← MonoidHom.ker_eq_bot_iff, QuotientGroup.ker_mk']
      exact CFSG.Timmesfeld.ClassicalOrders.statedScalars_subgroupOf_statedSp_eq_bot 2,
     QuotientGroup.mk'_surjective _⟩

@[expose] noncomputable def projEquivSymplectic [CharP F 2] :
    StatedProj (StatedSp 2 F) ≃* Matrix.symplecticGroup (Fin 2) F :=
  (projEquiv F).symm.trans
    ((MulEquiv.subgroupCongr
        (CFSG.ClassicalGroups.Symplectic.statedSp_eq_GLSymplectic (n := 2) (K := F))).trans
      (TauCeti.GLSymplectic.mulEquivSymplecticGroup (Fin 2) F))

theorem center_statedProj_eq_bot [CharP F 2] :
    Subgroup.center (StatedProj (StatedSp 2 F)) = ⊥ := by
  have h := CFSG.ComponentClassification.OuterAutomorphisms.center_map_equiv (projEquiv F)
  rw [CFSG.Timmesfeld.Transvection.center_statedSp_eq_bot (n := 2) (K := F) (by norm_num),
    Subgroup.map_bot] at h
  exact h.symm

end

theorem center_eq_bot_of_equiv {F : Type} [Field F] [CharP F 2] {K : Type*} [Group K]
    (φ : K ≃* StatedProj (StatedSp 2 F)) : Subgroup.center K = ⊥ := by
  have h := CFSG.ComponentClassification.OuterAutomorphisms.center_map_equiv φ
  rw [center_statedProj_eq_bot F] at h
  exact (Subgroup.map_eq_bot_iff_of_injective _ φ.injective).mp h

theorem isSylowTwoOf_of_card {G : Type*} [Group G] {K R₀ : Subgroup G} {F : Type} [Field F]
    [Fintype F] {e : ℕ} (hF : Fintype.card F = 2 ^ e) (he : 0 < e)
    (φ : ↥K ≃* StatedProj (StatedSp 2 F)) (hRK : R₀ ≤ K) (hR2 : IsPGroup 2 R₀)
    (hcard : Nat.card R₀ = 2 ^ (4 * e)) : IsSylowTwoOf R₀ K := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : CharP F 2 := charP_of_card_eq_prime_pow hF
  have : Finite F := Finite.of_fintype F
  have hq : Nat.card F = 2 ^ e := by rw [Nat.card_eq_fintype_card, hF]
  have hK : Nat.card K = 2 ^ (4 * e) * ((2 ^ (2 * e) - 1) * (2 ^ (4 * e) - 1)) := by
    rw [Nat.card_congr φ.toEquiv, CFSG.Timmesfeld.ClassicalOrders.card_statedProj_statedSp_of_charTwo,
      hq]
    have hIcc : Finset.Icc 1 2 = {1, 2} := by decide
    rw [hIcc, Finset.prod_pair (by norm_num : (1 : ℕ) ≠ 2)]
    have h1 : (2 ^ e) ^ (2 ^ 2) = 2 ^ (4 * e) := by
      rw [← pow_mul]; congr 1; ring
    have h2 : (2 ^ e) ^ (2 * 1) = 2 ^ (2 * e) := by
      rw [← pow_mul]; congr 1; ring
    have h3 : (2 ^ e) ^ (2 * 2) = 2 ^ (4 * e) := by
      rw [← pow_mul]; congr 1; ring
    rw [h1, h2, h3]
  have hmul : (R₀.subgroupOf K).index * Nat.card R₀ = Nat.card K := by
    rw [← Nat.card_congr (Subgroup.subgroupOfEquivOfLe hRK).toEquiv]
    exact Subgroup.index_mul_card _
  have hidx : (R₀.subgroupOf K).index = (2 ^ (2 * e) - 1) * (2 ^ (4 * e) - 1) := by
    rw [hcard, hK] at hmul
    have hpos : 0 < 2 ^ (4 * e) := by positivity
    have : (R₀.subgroupOf K).index * 2 ^ (4 * e) =
        ((2 ^ (2 * e) - 1) * (2 ^ (4 * e) - 1)) * 2 ^ (4 * e) := by
      rw [hmul]; ring
    exact Nat.eq_of_mul_eq_mul_right hpos this
  refine ⟨hRK, hR2, ?_⟩
  rw [hidx]
  have hodd : ∀ j : ℕ, 0 < j → ¬ 2 ∣ 2 ^ (j * e) - 1 := by
    intro j hj
    obtain ⟨m, hm⟩ : 2 ∣ 2 ^ (j * e) := dvd_pow_self 2 (Nat.mul_pos hj he).ne'
    have hp : 0 < 2 ^ (j * e) := by positivity
    omega
  intro hd
  rcases (Nat.Prime.dvd_mul Nat.prime_two).mp hd with h | h
  · exact hodd 2 (by norm_num) h
  · exact hodd 4 (by norm_num) h

end CFSG.QuasithinUnique.Lin2.Five
