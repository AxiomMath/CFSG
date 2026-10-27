module

public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.L239PairsL52Q1
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.L239PairsL52Q2

public section

namespace CFSG.QuasithinUnique.Vol2Native.L239

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
  CFSG.QuasithinUnique.Vol2Native.A312L CFSG.QuasithinUnique CFSG.ABGLocalTools

namespace L52

theorem flagStabilizer_ne_top {K : Type*} [Field K] {n : ℕ} {I : Set ℕ} {i : ℕ} (hi : i ∈ I)
    (hi1 : 1 ≤ i) (hin : i < n) : flagStabilizer n K I ≠ ⊤ := by
  intro h
  have := ((subflag_stabilizer_generation (K := K) (n := n) I).2.2 i hi1 hin).1
    (h ▸ Subgroup.mem_top _)
  exact this hi

theorem pairConclusion_of_sl5 {G : Type} [Group G] [Finite G] {L R : Subgroup G}
    (φ : ↥L ≃* SpecialLinearGroup (Fin 5) (ZMod 2)) (hRN : R ≤ Subgroup.normalizer (L : Set G))
    (hS : IsSylowTwoOf (R ⊓ L) L) : PairConclusion L R := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set SL : Subgroup ↥L := (R ⊓ L).subgroupOf L with hSL
  have hSyl : IsSylowOf 2 SL (⊤ : Subgroup ↥L) := isSylowOf_top_of_sylowTwo hS
  have hSyl' : IsSylowOf 2 (SL.map φ.toMonoidHom)
      (⊤ : Subgroup (SpecialLinearGroup (Fin 5) (ZMod 2))) := by
    have := isSylowOf_map_injective_local φ.toMonoidHom φ.injective hSyl
    rwa [Subgroup.map_top_of_surjective φ.toMonoidHom φ.surjective] at this
  obtain ⟨Sy, hSy⟩ := exists_sylow_unitriangular (K := ZMod 2) 2 (n := 5) (by norm_num)
  have hU : IsSylowOf 2 (unitriangular 5 (ZMod 2)) ⊤ := by
    rw [isSylowOf_iff]
    refine ⟨le_top, ?_, ?_⟩
    · rw [← hSy]
      exact Sy.isPGroup'
    · rw [Subgroup.relIndex_top_right, ← hSy]
      exact Sy.not_dvd_index
  obtain ⟨k, -, hk⟩ := hSyl'.exists_mem_conj hU
  let φ' : ↥L ≃* SpecialLinearGroup (Fin 5) (ZMod 2) := φ.trans (MulAut.conj k)
  have hφ' : ∀ l : ↥L, φ' l ∈ unitriangular 5 (ZMod 2) ↔ l ∈ SL := by
    intro l
    have h1 : φ' l = k * φ l * k⁻¹ := rfl
    rw [hk, h1, Subgroup.mem_map_equiv]
    have h2 : k⁻¹ * (k * φ l * k⁻¹) * k = φ l := by group
    rw [h2, MulEquiv.symm_apply_apply]
  have hSφ : SL.map φ'.toMonoidHom = unitriangular 5 (ZMod 2) := by
    ext x
    rw [Subgroup.mem_map_equiv]
    rw [← hφ' (φ'.symm x), MulEquiv.apply_symm_apply]
  have hK2 : Nat.card (ZMod 2) = 2 := Nat.card_zmod 2
  refine pairConclusion_of_goodPair φ' hRN
    (flagStabilizer_ne_top (n := 5) (i := 1) (by simp) le_rfl (by norm_num))
    (flagStabilizer_ne_top (n := 5) (i := 2) (by simp) (by norm_num) (by norm_num))
    (CFSG.QuasithinUnique.Setup.Family.flagStabilizer_sup_eq_top (n := 5) (by norm_num))
    (fun α hα => flagStabilizer_pair_invariant α (by rw [← hSφ]; exact hα))
    (goodSub_q1 hK2) (goodSub_q2 hK2)

end L52

theorem pairsFor_L52Out : PairsFor TypeL52Out := by
  intro G _ _ L R _ ⟨hmodel, _⟩ _ hRN hS
  obtain ⟨-, K, hF, hFin, hcard, ⟨e⟩⟩ := hmodel
  have hK : Nat.card K = 2 := by simpa using hcard
  have := Fintype.ofFinite K
  have hKc : Fintype.card K = Fintype.card (ZMod 2) := by
    rw [← Nat.card_eq_fintype_card, hK, ZMod.card]
  let σ : K ≃+* ZMod 2 := FiniteField.ringEquivOfCardEq hKc
  let φ : ↥L ≃* SpecialLinearGroup (Fin 5) (ZMod 2) :=
    e.trans ((slEquivStatedProj hK 5).symm.trans (L52.slEquivOfRingEquiv σ 5))
  exact L52.pairConclusion_of_sl5 φ hRN hS

end CFSG.QuasithinUnique.Vol2Native.L239
