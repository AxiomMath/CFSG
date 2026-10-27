module

public import CFSG.LocalAnalysis.ComponentClassification.AS81Sec3B0Coord
public import CFSG.LocalAnalysis.ComponentClassification.AS81Sec2Omega
public import CFSG.RankThree.PartOne.KC.OrthogonalEvenMinusSixExtract
public import CFSG.LieType.Multipliers.U42

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.ComponentClassification.AS81.SuzB0

open Subgroup Module CFSG.Open CFSG.PSL3Four.Native CFSG.ComponentClassification.PSL3Four
  CFSG.RankThree.PartOne CFSG.RankThree.PartOne.KCOrthogonal Sec2Omega

theorem exists_qMinusForm_ne_zero (hts : noTS3 = true) (U : Submodule (ZMod 2) (Fin 6 → ZMod 2))
    (hU : finrank (ZMod 2) U = 3) : ∃ u ∈ U, qMinusForm u ≠ 0 := by
  by_contra hcon
  push Not at hcon
  have hq : ∀ u ∈ U, qMinus u = 0 := fun u hu => by rw [← qMinusForm_apply]; exact hcon u hu
  let e := Module.finBasisOfFinrankEq (ZMod 2) U hU
  set v : Fin 3 → (Fin 6 → ZMod 2) := fun i => (e i : Fin 6 → ZMod 2) with hv
  have hvU : ∀ i, v i ∈ U := fun i => (e i).2
  have hli : LinearIndependent (ZMod 2) v :=
    e.linearIndependent.map' U.subtype (Submodule.ker_subtype U)
  have hcomb : ∀ g : Fin 3 → ZMod 2, ∑ i, g i • v i = 0 → g = 0 := fun g h =>
    funext (Fintype.linearIndependent_iff.mp hli g h)
  obtain ⟨a, ha, hae⟩ := exists_bitVec (v 0)
  obtain ⟨b, hb, hbe⟩ := exists_bitVec (v 1)
  obtain ⟨c, hc, hce⟩ := exists_bitVec (v 2)
  have h := hts
  rw [noTS3, allBelow_eq_true] at h
  have h' := h a ha
  rw [allBelow_eq_true] at h'
  have h'' := h' b hb
  rw [allBelow_eq_true] at h''
  have h3 := h'' c hc
  simp only [Bool.or_eq_true, beq_iff_eq, List.any_cons, List.any_nil, Bool.or_false] at h3
  have hsum : ∀ g : Fin 3 → ZMod 2, ∑ i, g i • v i = g 0 • v 0 + g 1 • v 1 + g 2 • v 2 :=
    fun g => Fin.sum_univ_three _
  have h2 : ∀ w : Fin 6 → ZMod 2, w + w = 0 := fun w => by
    funext i
    simp only [Pi.add_apply, Pi.zero_apply]
    exact CharTwo.add_self_eq_zero (w i)
  have hne : ∀ g : Fin 3 → ZMod 2, g ≠ 0 → ∑ i, g i • v i ≠ 0 := fun g hg h0 => hg (hcomb g h0)
  have hsing : ∀ u, u < 64 → bitVec u ∈ U → qMinusBit u = 1 → False := by
    intro u hu huU h1
    have := qMinus_bitVec u hu
    rw [hq _ huU, h1, Nat.cast_one] at this
    exact zero_ne_one this
  rcases h3 with ((((((h3 | h3) | h3) | h3) | h3) | h3) | h3) | h3
  · apply hne ![1, 0, 0] (by decide)
    rw [hsum, ← hae, h3, bitVec_zero]
    simp
  · apply hne ![0, 1, 0] (by decide)
    rw [hsum, ← hbe, h3, bitVec_zero]
    simp
  · apply hne ![1, 1, 0] (by decide)
    rw [hsum, ← hae, ← hbe, h3]
    simp [h2]
  · apply hne ![0, 0, 1] (by decide)
    rw [hsum, ← hce, h3, bitVec_zero]
    simp
  · apply hne ![1, 0, 1] (by decide)
    rw [hsum, ← hae, ← hce, h3]
    simp [h2]
  · apply hne ![0, 1, 1] (by decide)
    rw [hsum, ← hbe, ← hce, h3]
    simp [h2]
  · apply hne ![1, 1, 1] (by decide)
    rw [hsum, ← hae, ← hbe, ← hce, h3, bitVec_xor]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
      Matrix.tail_cons, one_smul]
    exact h2 _
  · have hab := xor_lt ha hb
    have hac := xor_lt ha hc
    have hbc := xor_lt hb hc
    have habc := xor_lt hab hc
    have hUa : bitVec a ∈ U := hae ▸ hvU 0
    have hUb : bitVec b ∈ U := hbe ▸ hvU 1
    have hUc : bitVec c ∈ U := hce ▸ hvU 2
    rcases h3 with h3 | h3 | h3 | h3 | h3 | h3 | h3
    · exact hsing a ha hUa h3
    · exact hsing b hb hUb h3
    · exact hsing c hc hUc h3
    · exact hsing _ hab (by rw [bitVec_xor]; exact U.add_mem hUa hUb) h3
    · exact hsing _ hac (by rw [bitVec_xor]; exact U.add_mem hUa hUc) h3
    · exact hsing _ hbc (by rw [bitVec_xor]; exact U.add_mem hUb hUc) h3
    · exact hsing _ habc (by rw [bitVec_xor, bitVec_xor]; exact U.add_mem (U.add_mem hUa hUb) hUc)
        h3

theorem omega_facts (hts : noTS3 = true) :
    Nat.card (timmesfeldOmega qMinus) = 25920 ∧
      ((timmesfeldOmega qMinus).subgroupOf
        (TauCeti.QuadraticMap.orthogonalGroup qMinusForm)).index = 2 ∧
      IsSimpleGroup ↥(timmesfeldOmega qMinus) ∧ center ↥(timmesfeldOmega qMinus) = ⊥ := by
  obtain ⟨E, _, _, D, ψ, ρ, -, -, -, -, hcomm, hs, -, hna, hcard, hidx, -⟩ :=
    even_minus_six_actual_derived_extraction qMinusForm qMinusForm_nondegenerate finrank_fin_six
      (exists_qMinusForm_ne_zero hts)
  rw [timmesfeldOmega_qMinus, hcomm]
  refine ⟨by rw [hcard, Nat.card_zmod]; norm_num, hidx, hs, ?_⟩
  refine (IsSimpleGroup.eq_bot_or_eq_top_of_normal (center _)).resolve_right fun h => hna ?_
  intro x y
  exact (mem_center_iff.mp (h ▸ mem_top x) y).symm

theorem omega_commutator (hts : noTS3 = true) :
    ⁅timmesfeldOmega qMinus, timmesfeldOmega qMinus⁆ = timmesfeldOmega qMinus := by
  obtain ⟨E, _, _, D, ψ, ρ, -, -, -, -, hcomm, -, hp, -⟩ :=
    even_minus_six_actual_derived_extraction qMinusForm qMinusForm_nondegenerate finrank_fin_six
      (exists_qMinusForm_ne_zero hts)
  rw [timmesfeldOmega_qMinus, hcomm]
  have h2 : (commutator ↥ρ.range).map ρ.range.subtype = ⁅ρ.range, ρ.range⁆ := by
    rw [_root_.commutator_def, Subgroup.map_commutator, ← MonoidHom.range_eq_map,
      Subgroup.range_subtype]
  rw [← h2, Group.isPerfect_def.mp hp, ← MonoidHom.range_eq_map, Subgroup.range_subtype]

theorem omega_lieModel (hts : noTS3 = true) :
    CFSG.Blueprint.LieModel (↥(timmesfeldOmega qMinus) ⧸ center ↥(timmesfeldOmega qMinus))
      .PSU 4 2 1 := by
  obtain ⟨E, _, _, D, ψ, ρ, -, -, hinj, -, hcomm, -⟩ :=
    even_minus_six_actual_derived_extraction qMinusForm qMinusForm_nondegenerate finrank_fin_six
      (exists_qMinusForm_ne_zero hts)
  have : CharP E 2 := charP_two_of_algebra (K := ZMod 2)
  obtain ⟨f, h, hK, hbar⟩ := D.exists_unitaryFieldData
  have hf : f = 1 := by
    rw [Nat.card_zmod] at hK
    exact Nat.pow_right_injective le_rfl (hK.symm.trans (pow_one 2).symm)
  subst hf
  obtain ⟨θ⟩ := D.nonempty_sixSU_mulEquiv h hbar
  let e : ↥(timmesfeldOmega qMinus) ≃* CFSG.Assembly.LowTwoRank.StatedSU 4 (2 ^ 1) E :=
    ((MulEquiv.subgroupCongr (timmesfeldOmega_qMinus.trans hcomm)).trans
      (MonoidHom.ofInjective hinj).symm).trans θ
  have hF : Nat.card E = (2 ^ 1) ^ 2 := h.card_eq_sq
  have hnq : ((4 : ℕ), 2 ^ 1) ≠ (3, 2) := by decide
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have := h.finite
  obtain ⟨-, hZc⟩ :=
    CFSG.LieType.Universal.Unitary.isQuasisimple_statedSU_of_card hF (by norm_num) hnq
  exact Or.inl ⟨by decide, ⟨Nat.prime_two, le_rfl, by norm_num, hnq⟩, E, inferInstance,
    inferInstance, hF, ⟨(QuotientGroup.congr _ _ e
      (CFSG.LieType.Universal.Unitary.map_center_mulEquiv e)).trans
        (QuotientGroup.quotientMulEquivOfEq hZc)⟩⟩

theorem card_ker_dvd_two
    (hts : noTS3 = true) {E : Type} [Group E] [Finite E] [Group.IsPerfect E]
    (p : E →* ↥(timmesfeldOmega qMinus)) (hp : Function.Surjective p)
    (hC : p.ker ≤ center E) : Nat.card p.ker ∣ 2 := by
  set S := ↥(timmesfeldOmega qMinus)
  have : Finite S := Finite.of_surjective p hp
  have hZ : center S = ⊥ := (omega_facts hts).2.2.2
  let p' : E →* S ⧸ center S := (QuotientGroup.mk' (center S)).comp p
  have hp' : Function.Surjective p' := (QuotientGroup.mk'_surjective _).comp hp
  have hker : p'.ker = p.ker := by
    ext g
    rw [MonoidHom.mem_ker, MonoidHom.mem_ker, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
      QuotientGroup.eq_one_iff, hZ, mem_bot]
  obtain ⟨hperf, ⟨eM⟩⟩ := LieType.Multipliers.U42.multiplier_PSU_four_two _ (omega_lieModel hts)
  have : Group.IsPerfect (S ⧸ center S) := Group.isPerfect_def.mpr hperf
  obtain ⟨-, ⟨h, -, -, -, hmap, -⟩, -⟩ :=
    RankThree.PerfectCover.perfect_central_kernel_quotient_of_schur_multiplier p' hp'
      (hker ▸ hC)
  have hM : Nat.card (RankThree.PerfectCover.hopfMultiplier (S ⧸ center S)) = 2 := by
    rw [← Nat.card_congr (RankThree.PerfectCover.hopfMultiplierEquivGriess _).toEquiv,
      Nat.card_congr eM.toEquiv, Nat.card_congr Multiplicative.toAdd, Nat.card_zmod]
  rw [← hker, ← hmap]
  exact (Subgroup.card_map_dvd (H := RankThree.PerfectCover.hopfMultiplier (S ⧸ center S)) h).trans
    hM.dvd

end CFSG.ComponentClassification.AS81.SuzB0
