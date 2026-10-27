module

public import CFSG.RankThree.PartOne.KE6.Tw6A2b
public import CFSG.Quasithin.Vol2.F134Orders
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.LocalAnalysis.SeitzReduction.EPilotPosition
public import CFSG.Quasithin.Background.SmithC27RTypeGen
public import CFSG.Sporadic.Schreier.J4SSylowBase

public section

namespace CFSG.LocalAnalysis.GLTheoremA.Y10F

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.E6 Matrix
  CFSG.Assembly.LowTwoRank

theorem isQuasisimple_and_three_dvd_of_mulEquiv_statedSU {L : Type} [Group L] {K₂ : Type}
    [Field K₂] [Finite K₂] {n : ℕ} (hn : 2 ≤ n) (hK₂ : Nat.card K₂ = (2 ^ n) ^ 2)
    (e : L ≃* ↥(StatedSU 3 (2 ^ n) K₂)) :
    CFSG.Open.IsQuasisimple L ∧ 3 ∣ Nat.card (L ⧸ Subgroup.center L) := by
  have hnq : (3, 2 ^ n) ≠ (3, 2) := by
    intro h
    have h2 : 2 ^ n = 2 := congrArg Prod.snd h
    have h4 : 4 ≤ 2 ^ n := by
      calc (4 : ℕ) = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
    omega
  obtain ⟨hSU, hZ⟩ := CFSG.LieType.Universal.Unitary.isQuasisimple_statedSU_of_card
    (F := K₂) (p := 2) (f := n) (n := 3) hK₂ (by norm_num) hnq
  have hSUc : CFSG.IsQuasisimple ↥(StatedSU 3 (2 ^ n) K₂) := hSU
  have hLq : CFSG.IsQuasisimple L := CFSG.LocalCores.isQuasisimple_of_mulEquiv e.symm hSUc
  refine ⟨CFSG.Quasithin.A3.isQuasisimple_iff_open.mp hLq, ?_⟩
  have h3 : 3 ∣ Nat.card (↥(StatedSU 3 (2 ^ n) K₂) ⧸
      Subgroup.center ↥(StatedSU 3 (2 ^ n) K₂)) := by
    rw [hZ]
    exact CFSG.Quasithin.F134.three_dvd_card_statedProj_statedSU_three
      Nat.prime_two (by omega) hK₂
  rw [Nat.card_congr (CFSG.Quasithin.SmithC27.quotCenterCongr e).toEquiv]
  exact h3

variable {Ω : Type} [Field Ω] [CharP Ω 2]

def frobPow (n : ℕ) : Ω →+* Ω := (frobenius Ω 2) ^ n

theorem frobPow_apply (n : ℕ) (c : Ω) : frobPow (Ω := Ω) n c = c ^ (2 ^ n) := by
  induction n generalizing c with
  | zero => simp [frobPow]
  | succ n ih =>
      show ((frobenius Ω 2) ^ (n + 1)) c = c ^ (2 ^ (n + 1))
      rw [pow_succ]
      change frobPow (Ω := Ω) n ((frobenius Ω 2) c) = c ^ (2 ^ (n + 1))
      rw [ih ((frobenius Ω 2) c), frobenius_def, ← pow_mul, pow_succ']

theorem frobPow_surjective [IsAlgClosed Ω] (n : ℕ) :
    Function.Surjective (frobPow (Ω := Ω) n) := by
  intro y
  obtain ⟨z, hz⟩ := IsAlgClosed.exists_pow_nat_eq y (n := 2 ^ n) (by positivity)
  exact ⟨z, by rw [frobPow_apply]; exact hz⟩

section Certs

theorem twE6_theta_maps_block_of_chainRoot (n : ℕ)
    (θ : ModGL Tag.E6 Ω →* ModGL Tag.E6 Ω) (hinj : Function.Injective θ)
    (hθ' : ∀ i j : Fin 3, i ≠ j → ∃ e : Ω, e * e = 1 ∧ ∀ c : Ω,
      θ (pinnedX Tag.E6 Ω (chainRoot chain56 i j) c) =
        pinnedX Tag.E6 Ω (chainRoot chain56 j i) (e * frobPow (Ω := Ω) n c))
    [IsAlgClosed Ω] :
    ∀ g ∈ subsystemGroup Tag.E6 Ω support56, θ g ∈ subsystemGroup Tag.E6 Ω support56 := by
  have h := CFSG.RankThree.PartOne.KE6.exists_sl3_root_reversing_of_theta₂
    (Fr := frobPow (Ω := Ω) n) (frobPow_surjective n) θ hinj (Equiv.refl (Fin 3)) hθ'
  exact h.1

end Certs

end CFSG.LocalAnalysis.GLTheoremA.Y10F
