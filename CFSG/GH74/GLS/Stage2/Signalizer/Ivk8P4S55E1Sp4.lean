module

public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55E1SpAut
public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55E1Gen
public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55E1Sub
public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55E1Tr
public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55E1BT
public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55E1Types

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Ivk8

open Subgroup CFSG CFSG.Assembly.LowTwoRank CFSG.Blueprint
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag
open CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher

section Core

variable {F : Type} [Field F] [Finite F]

theorem std_data {r : ℕ} [Fact r.Prime] [CharP F r] (hr2 : r ≠ 2) {d : ℕ} (hd1 : 1 ≤ d)
    (hd2 : d ≤ 2) :
    ∃ Rs : Subgroup (StatedProj (StatedSp 2 F)), IsPGroup r ↥Rs ∧
      Rs ≤ projStabilizer 2 F (flag 2 F d) ∧
      projStabilizer 2 F (flag 2 F d) ≤ normalizer (Rs : Set (StatedProj (StatedSp 2 F))) ∧
      ∀ b : MulAut (StatedProj (StatedSp 2 F)), (∀ y ∈ Rs, b y = y) → b ^ r = 1 := by
  have hr3 : 3 ≤ r := by
    have h2 := (Fact.out : r.Prime).two_le
    omega
  have hd : d = 1 ∨ d = 2 := by omega
  rcases hd with rfl | rfl
  · obtain ⟨h1, h2⟩ := map_le_normalizer_map (SymplecticFlag.proj 2 F)
      (spRad1_le_stabilizer (F := F)) (fun s hs g hg => conj_mem_spRad1 hs hg)
    refine ⟨(spRad1 F).map (SymplecticFlag.proj 2 F), ?_, h1, h2, fun b hb => ?_⟩
    · exact isPGroup_map_of_forall_pow _ fun g hg => pow_eq_one_of_mem_radFl hr3 hg
    · exact pow_eq_one_of_fix_spRad1 hr2 b fun g hg => hb _ ⟨g, hg, rfl⟩
  · obtain ⟨h1, h2⟩ := map_le_normalizer_map (SymplecticFlag.proj 2 F)
      (spRad2_le_stabilizer (F := F)) (fun s hs g hg => conj_mem_spRad2 hs hg)
    refine ⟨(spRad2 F).map (SymplecticFlag.proj 2 F), ?_, h1, h2, fun b hb => ?_⟩
    · exact isPGroup_map_of_forall_pow _ fun g hg => pow_eq_one_of_mem_radFl hr3 hg
    · exact pow_eq_one_of_fix_spRad2 hr2 b fun g hg => hb _ ⟨g, hg, rfl⟩

theorem e1Core_psp4 {r : ℕ} [Fact r.Prime] [CharP F r] (hr2 : r ≠ 2)
    (hBT : LieType.BorelTits.Holds (StatedProj (StatedSp 2 F)) r) :
    E1Core r (StatedProj (StatedSp 2 F)) := by
  intro b hb1 hbr hHH E hE hinv
  by_contra hne
  obtain ⟨M, S, hM, hS, hR⟩ := e1_engine hBT b hHH hE hinv hne
  have hmem : M ∈ spMaximalParabolics 2 F r := ⟨hM, _, ⟨S, rfl⟩, hS⟩
  obtain ⟨W, hW0, hWiso, rfl⟩ :=
    ((maximal_parabolics (K := F) (r := 2) r (by norm_num)).1 ▸ hmem :
      M ∈ {M | ∃ W : Submodule F (Fin 2 ⊕ Fin 2 → F), W ≠ ⊥ ∧
        IsTotallyIsotropic (pairedSympForm F 2) W ∧ M = projStabilizer 2 F W})
  obtain ⟨d, g, hd1, hd2, rfl⟩ := exists_map_flag_eq_of_isTotallyIsotropic hW0 hWiso
  rw [projStabilizer_map_spAct] at hR
  obtain ⟨Rs, hRp, hRle, hRnorm, hpow⟩ := std_data (F := F) (r := r) hr2 hd1 hd2
  set x := SymplecticFlag.proj 2 F g with hx
  have hnorm : ∀ s ∈ projStabilizer 2 F (flag 2 F d), ∀ y ∈ Rs, s * y * s⁻¹ ∈ Rs :=
    fun s hs y hy => (Subgroup.mem_normalizer_iff.mp (hRnorm hs) y).mp hy
  obtain ⟨h1, h2⟩ := map_le_normalizer_map (MulAut.conj x).toMonoidHom hRle hnorm
  have hfix := hR _ (hRp.map _) h1 h2
  have hb' := hpow ((MulAut.conj x)⁻¹ * b * MulAut.conj x) (fix_conj_of_fix x b hfix)
  have hbeq : b = MulAut.conj x * ((MulAut.conj x)⁻¹ * b * MulAut.conj x) * (MulAut.conj x)⁻¹ := by
    group
  have hbr1 : b ^ r = 1 := by
    rw [hbeq, conj_pow, hb', mul_one, mul_inv_cancel]
  have h1 : orderOf b ∣ r := orderOf_dvd_of_pow_eq_one hbr1
  rcases (Nat.dvd_prime (Fact.out : r.Prime)).mp h1 with h | h
  · exact hb1 (orderOf_eq_one_iff.mp h)
  · exact hbr (h ▸ dvd_refl r)

end Core

section Cell

theorem e1_sp4 : E1Type FSp4d := by
  intro r Y _ _ hr hr2 hF b hb1 hbr hHH E hE hinv
  obtain ⟨f, hf, hlie⟩ := hF
  have : Fact r.Prime := ⟨hr⟩
  obtain ⟨-, F, iF, fF, hcard, ⟨e⟩⟩ := Final.lieModel_psp_unpack hlie
  have : CharP F r := by
    have := Fintype.ofFinite F
    exact charP_of_card_eq_prime_pow (by rw [← Nat.card_eq_fintype_card, hcard])
  have hBT : LieType.BorelTits.Holds Y r := holds_of_lieModel hlie (by decide)
  have hBT' : LieType.BorelTits.Holds (StatedProj (StatedSp 2 F)) r :=
    LieType.BorelTits.Holds.of_mulEquiv e hBT
  exact E1Core.of_mulEquiv e (e1Core_psp4 hr2 hBT') b hb1 hbr hHH E hE hinv

end Cell

end CFSG.GH74.GLS.Stage2.Signalizer.Ivk8
