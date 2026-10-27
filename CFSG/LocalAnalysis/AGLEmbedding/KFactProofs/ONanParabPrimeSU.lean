module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanParabPrimeQuot
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanParabThreeSU
import CFSG.LieType.Steinberg.CentralExt.UnitaryRankOneLast
import CFSG.LieType.Steinberg.CentralExt.SUTwo
public import CFSG.ClassicalGroups.Unitary.Simple
public import CFSG.LieType.Universal.Unitary.Model

public section

namespace CFSG.AGLEmbedding.ParabPrime

open CFSG.Assembly.LowTwoRank CFSG.AGLEmbedding.ParabHub CFSG.LieType.Universal
  CFSG.LieType.Universal.Unitary CFSG.LieType.Steinberg CFSG.LieType.CurtisTits
  CFSG.LieType.BorelTits

section Generic

variable {K : Type*} [Group K]

theorem rankOneNode_of_range {D : UniversalRootDatum K} {i : Fin D.rank} {q : ℕ}
    {k : Type} [Field k] [Finite k] [CharP k 2] {ρ : Matrix.SpecialLinearGroup (Fin 2) k →* K}
    (hinj : Function.Injective ρ) (hrange : rankOne D.rootGroup i = ρ.range)
    (hkq : Nat.card k = q ∨ Nat.card k = q ^ 2) : RankOneNode D i q := by
  have hqk : q ≤ Nat.card k := by
    rcases hkq with h | h
    · exact h.ge
    · rw [h]
      exact Nat.le_self_pow two_ne_zero q
  refine ⟨fun h4 => ?_, fun p hp hp5 hpq => ?_⟩
  · rw [hrange, MonoidHom.range_eq_map, ← Subgroup.map_commutator]
    congr 1
    exact (sl2_isPerfect (h4.trans hqk)).commutator_eq_top
  · have : Fact p.Prime := ⟨hp⟩
    have hdvd : p ∣ Nat.card (Matrix.SpecialLinearGroup (Fin 2) k) := by
      rw [card_sl2]
      refine Dvd.dvd.mul_left ?_ _
      rcases hkq with h | h
      · rw [h]
        exact hpq
      · rw [h]
        refine hpq.trans ?_
        have : q ^ 2 - 1 ∣ (q ^ 2) ^ 2 - 1 := by
          have := Nat.sub_dvd_pow_sub_pow (q ^ 2) 1 2
          simpa using this
        exact this
    obtain ⟨y, hy⟩ := exists_prime_orderOf_dvd_card' p hdvd
    refine ⟨ρ y, hrange ▸ ⟨y, rfl⟩, ?_, ?_⟩
    · rw [orderOf_injective ρ hinj y, hy]
    · intro hc
      have hy1 : y ∈ Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) k) := by
        rw [Subgroup.mem_center_iff]
        intro z
        apply hinj
        rw [map_mul, map_mul]
        exact (Subgroup.mem_center_iff.1 hc (ρ z))
      rw [sl2_center_eq_bot, Subgroup.mem_bot] at hy1
      rw [hy1, orderOf_one] at hy
      exact hp.one_lt.ne hy

theorem range_subtype_comp_symm {L : Subgroup K} {M : Type*} [Group M] (e : L ≃* M) :
    (L.subtype.comp e.symm.toMonoidHom).range = L := by
  rw [MonoidHom.range_comp, MonoidHom.range_eq_top.2 e.symm.surjective, Subgroup.map_top,
    Subgroup.range_subtype]

theorem commutator_eq_self_of_isPerfect {L : Subgroup K} (h : Group.IsPerfect L) :
    ⁅L, L⁆ = L := by
  rw [← Subgroup.map_subtype_commutator, h.commutator_eq_top, Subgroup.map_top,
    Subgroup.range_subtype]

end Generic

section SU

variable {F : Type} [Field F] [Finite F] [CharP F 2] {f : ℕ} (hF : Nat.card F = (2 ^ f) ^ 2)
  {n : ℕ}

include hF in
theorem rankOneNode_su_short {k : Fin (n / 2)} (hk : k.val + 1 < n / 2) :
    RankOneNode (rootDatum hF n) k (2 ^ f) := by
  have hσ := unitaryInvolution_involutive hF
  set e := rankOneShortEquiv (hσ := hσ) hk
  exact rankOneNode_of_range (k := F) (ρ := (rankOne (rootGroup _ hσ n) k).subtype.comp
    e.symm.toMonoidHom) (Subtype.val_injective.comp e.symm.injective)
    (range_subtype_comp_symm e).symm (Or.inr hF)

include hF in
theorem rankOneNode_su_last_even (he : Even n) {k : Fin (n / 2)} (hk : ¬k.val + 1 < n / 2) :
    RankOneNode (rootDatum hF n) k (2 ^ f) := by
  have hσ := unitaryInvolution_involutive hF
  obtain ⟨ζ, hζ0, hζ⟩ := exists_unitaryInvolution_eq_neg hF
  set e := (rankOneLastEvenEquiv hF he hk).trans (hypEquiv hζ0 hζ).symm
  exact rankOneNode_of_range (k := fixedSubfield F 2 f)
    (ρ := (rankOne (rootGroup _ hσ n) k).subtype.comp e.symm.toMonoidHom)
    (Subtype.val_injective.comp e.symm.injective) (range_subtype_comp_symm e).symm
    (Or.inl (card_fixedSubfield hF))

omit [Finite F] [CharP F 2] in
theorem det_eq_one_of_mem_statedSU {n q : ℕ} {A : GL (Fin n) F} (hA : A ∈ StatedSU n q F) :
    (A : Matrix (Fin n) (Fin n) F).det = 1 :=
  CFSG.Open.StatedAPI.det_of_mem_statedSU hA

omit [Finite F] [CharP F 2] in
theorem pow_three_eq_one_of_scalar {g : GL (Fin 3) F} (hg : g ∈ StatedScalars (Fin 3) F)
    (hdet : (g : Matrix (Fin 3) (Fin 3) F).det = 1) : g ^ 3 = 1 := by
  obtain ⟨u, rfl⟩ := hg
  have h3 : (u : F) ^ 3 = 1 := by
    simpa [Matrix.GeneralLinearGroup.coe_scalar, Matrix.det_diagonal] using hdet
  rw [← map_pow]
  have : u ^ 3 = 1 := Units.ext (by simpa using h3)
  rw [this, map_one]

include hF in
theorem su_three_center_pow_three (hq : 4 ≤ 2 ^ f) {z : SU (unitaryInvolution F 2 f) 3}
    (hz : z ∈ Subgroup.center ↥(SU (unitaryInvolution F 2 f) 3)) : z ^ 3 = 1 := by
  have hnq : ((3 : ℕ), 2 ^ f) ≠ (3, 2) := fun h => by
    have := (Prod.mk.inj h).2
    omega
  have hperf := CFSG.ClassicalGroups.Unitary.isPerfect_statedSU hF (n := 3) le_rfl hnq
  have hsimple :=
    CFSG.ClassicalGroups.Unitary.isSimpleGroup_statedProj_statedSU F 2 f hF 3 le_rfl hnq
  have hcen := (isQuasisimple_statedSU hperf hsimple).2
  set ψ := equivStatedSU hF 3
  have h1 : ψ z ∈ Subgroup.center ↥(StatedSU 3 (2 ^ f) F) := by
    rw [← map_center_mulEquiv ψ]
    exact ⟨z, hz, rfl⟩
  rw [hcen, Subgroup.mem_subgroupOf] at h1
  have h2 := pow_three_eq_one_of_scalar h1 (det_eq_one_of_mem_statedSU (ψ z).2)
  apply ψ.injective
  rw [map_pow, map_one]
  exact Subtype.ext (by simpa using h2)

include hF in
theorem rankOneNode_su_last_odd (hn : ¬Even n) {k : Fin (n / 2)} (hk : ¬k.val + 1 < n / 2) :
    RankOneNode (rootDatum hF n) k (2 ^ f) := by
  have hσ := unitaryInvolution_involutive hF
  set e := rankOneLastOddEquiv hF hn hk
  have hq2 : 2 ≤ 2 ^ f := by
    have h1 := Finite.one_lt_card (α := F)
    rw [hF] at h1
    by_contra h
    have h2 : 2 ^ f ≤ 1 := by omega
    have := Nat.pow_le_pow_left h2 2
    omega
  refine ⟨fun h4 => ?_, fun p hp hp5 hpq => ?_⟩
  · have hnq : ((3 : ℕ), 2 ^ f) ≠ (3, 2) := fun h => by
      have := (Prod.mk.inj h).2
      omega
    have : Group.IsPerfect ↥(StatedSU 3 (2 ^ f) F) :=
      CFSG.ClassicalGroups.Unitary.isPerfect_statedSU hF (n := 3) le_rfl hnq
    have : Group.IsPerfect (SU (unitaryInvolution F 2 f) 3) :=
      Group.IsPerfect.ofSurjective (f := (equivStatedSU hF 3).symm.toMonoidHom)
        (equivStatedSU hF 3).symm.surjective
    have hperfL : Group.IsPerfect ↥(rankOne (rootGroup _ hσ n) k) :=
      Group.IsPerfect.ofSurjective (f := e.symm.toMonoidHom) e.symm.surjective
    exact commutator_eq_self_of_isPerfect hperfL
  · have : Fact p.Prime := ⟨hp⟩
    have hq4 : 4 ≤ 2 ^ f := by
      rcases f with _ | _ | f
      · omega
      · exfalso
        have : p ≤ 3 := Nat.le_of_dvd (by norm_num) (by simpa using hpq)
        omega
      · calc 4 = 2 ^ 2 := by norm_num
          _ ≤ 2 ^ (f + 2) := Nat.pow_le_pow_right (by norm_num) (by omega)
    have hdvd : p ∣ Nat.card (SU (unitaryInvolution F 2 f) 3) := by
      rw [card_SU_three hF]
      exact (hpq.mul_left _).mul_right _
    obtain ⟨y, hy⟩ := exists_prime_orderOf_dvd_card' p hdvd
    refine ⟨((e.symm y : rankOne (rootGroup _ hσ n) k) : SU (unitaryInvolution F 2 f) n),
      (e.symm y).2, ?_, fun hc => ?_⟩
    · rw [Subgroup.orderOf_coe, MulEquiv.orderOf_eq, hy]
    · have hyc : y ∈ Subgroup.center ↥(SU (unitaryInvolution F 2 f) 3) := by
        rw [Subgroup.mem_center_iff]
        intro g
        apply e.symm.injective
        apply Subtype.ext
        rw [map_mul, map_mul]
        exact Subgroup.mem_center_iff.1 hc (e.symm g : SU (unitaryInvolution F 2 f) n)
      have h3 := su_three_center_pow_three hF hq4 hyc
      have := orderOf_dvd_of_pow_eq_one h3
      rw [hy] at this
      have := Nat.le_of_dvd (by norm_num) this
      omega

include hF in
theorem rankOneNode_su (i : Fin (n / 2)) : RankOneNode (rootDatum hF n) i (2 ^ f) := by
  by_cases hk : i.val + 1 < n / 2
  · exact rankOneNode_su_short hF hk
  · by_cases he : Even n
    · exact rankOneNode_su_last_even hF he hk
    · exact rankOneNode_su_last_odd hF he hk

include hF in
theorem parabCore_su (hn : 3 ≤ n) {Y : Type} [Group Y] [Finite Y]
    (e : Y ≃* StatedProj (StatedSU n (2 ^ f) F)) (hq4 : 4 ≤ 2 ^ f) : ParabCore Y (2 ^ f) := by
  obtain ⟨ζ, hζ⟩ := exists_traceZero_ne_zero hF
  have : Finite (SU (unitaryInvolution F 2 f) n) := Finite.of_injective _ Subtype.val_injective
  exact (borelQuotient_su hF (by omega) ζ hζ e).parabCore hq4 (by rw [hF])
    (rankOneNode_su hF)

end SU

theorem parabCore_of_model_psu {Y : Type} [Group Y] [Finite Y] {n f : ℕ}
    (h : StatedClassicalModel Y .PSU n 2 f) (hf : 2 ≤ f) : ParabCore Y (2 ^ f) := by
  obtain ⟨⟨-, -, hn, -⟩, F, hF, hFfin, hcard, ⟨e⟩⟩ := h
  have := Fintype.ofFinite F
  have : CharP F 2 := charP_of_card_eq_prime_pow (f := f * 2)
    (by rw [← Nat.card_eq_fintype_card, hcard, pow_mul])
  exact parabCore_su hcard hn e (by
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf)

end CFSG.AGLEmbedding.ParabPrime
