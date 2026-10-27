module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Escape
public import CFSG.LocalAnalysis.AGLEmbedding.TheoremZAux
public import CFSG.LocalAnalysis.AGLEmbedding.LemmaJStarAux

public section

namespace CFSG.AGLEmbeddingD2

open CFSG.Open CFSG.QuasithinUnique CFSG.RankThreeCoreUniqueness.Helpers CFSG.AGLEmbedding

structure AGLPair {G : Type} [Group G] [Finite G] (p : ℕ) (M H R : Subgroup G) : Prop where
  glob : AGLGlobal G
  prime : p.Prime
  ne_two : p ≠ 2
  maxTwoLocal_M : GLBIsMaxTwoLocal M
  maxTwoLocal_H : GLBIsMaxTwoLocal H
  le_H : R ≤ H
  le_M : R ≤ M
  isSylow : ∃ T : Sylow p H, (T : Subgroup H).map H.subtype = R
  not_le : ¬ H ≤ M
  primeCore_le : GLBPrimeCore p H ≤ M
  twoCore_inf : pCoreOf 2 (H ⊓ M) = pCoreOf 2 H

namespace AGLPair

variable {G : Type} [Group G] [Finite G] {p : ℕ} {M H R : Subgroup G}

theorem isPGroup_R (h : AGLPair p M H R) : IsPGroup p R := by
  obtain ⟨T, hT⟩ := h.isSylow
  exact hT ▸ T.isPGroup'.map H.subtype

theorem twoCore_le_primeCore (h : AGLPair p M H R) : pCoreOf 2 H ≤ GLBPrimeCore p H :=
  pCoreOf_le_glbPrimeCore Nat.prime_two
    ((Nat.coprime_primes h.prime Nat.prime_two).mpr h.ne_two) H

theorem twoCore_le (h : AGLPair p M H R) : pCoreOf 2 H ≤ M :=
  h.twoCore_le_primeCore.trans h.primeCore_le

theorem charTwo (h : AGLPair p M H R) : CharTwo M ∧ CharTwo H :=
  ⟨h.glob.charTwo M h.maxTwoLocal_M.1, h.glob.charTwo H h.maxTwoLocal_H.1⟩

theorem toTwoLocalPair (h : AGLPair p M H R) : TwoLocalPair M H :=
  ⟨h.maxTwoLocal_M, h.maxTwoLocal_H, h.not_le, h.twoCore_le⟩

theorem toTwoLocalPhaseThree (h : AGLPair p M H R) : TwoLocalPhaseThree M H :=
  { h.toTwoLocalPair with
    charTwo_M := h.charTwo.1
    twoCore_inf := h.twoCore_inf }

theorem inf_lt_left (h : AGLPair p M H R) : H ⊓ M < H :=
  h.toTwoLocalPair.inf_lt_left

theorem inf_lt_right (h : AGLPair p M H R) : H ⊓ M < M :=
  h.toTwoLocalPair.inf_lt_right

theorem cgsIn_eq (h : AGLPair p M H R) :
    CFSG.Quasithin.cgsIn M (pCoreOf 2 H) = M ⊓ H :=
  h.toTwoLocalPair.cgsIn_eq

theorem normalizer_twoCore_H (h : AGLPair p M H R) :
    Subgroup.normalizer (pCoreOf 2 H : Set G) = H :=
  h.toTwoLocalPair.normalizer_twoCore_H

theorem twoCore_M_le (h : AGLPair p M H R) : pCoreOf 2 M ≤ pCoreOf 2 H :=
  h.toTwoLocalPair.twoCore_M_le h.twoCore_inf

theorem exists_sylowTwo_primeCore (h : AGLPair p M H R) :
    ∃ T : Subgroup G, T ≤ GLBPrimeCore p H ∧ IsPGroup 2 T ∧
      ¬ 2 ∣ (T.subgroupOf (GLBPrimeCore p H)).index ∧
      R ≤ Subgroup.normalizer (T : Set G) ∧ pCoreOf 2 H ≤ T := by
  have : Fact p.Prime := ⟨h.prime⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨T, hTN, hT2, hTidx, hRT⟩ := exists_le_normalizer_of_coprime (q := 2) h.isPGroup_R
    (h.le_H.trans (le_normalizer_glbPrimeCore p H)) (glbPrimeCore_coprime p H)
  refine ⟨T, hTN, hT2, hTidx, hRT, ?_⟩
  have hTS : T ≤ Subgroup.normalizer (pCoreOf 2 H : Set G) :=
    (hTN.trans (glbPrimeCore_le p H)).trans (localGroup_le_normalizer_pCoreOf 2 H)
  have hST2 : IsPGroup 2 (pCoreOf 2 H ⊔ T : Subgroup G) :=
    IsPGroup.to_sup_of_normal_left' (pCoreOf_isPGroup 2 H) hT2 hTS
  exact le_sup_left.trans (le_of_le_of_isPGroup_of_not_dvd_index le_sup_right
    (sup_le h.twoCore_le_primeCore hTN) hST2 hTidx)

theorem pCoreOf_two_primeCore_ne_bot (h : AGLPair p M H R) {X : Subgroup G} (hXR : X ≤ R)
    (hX1 : X ≠ ⊥) : pCoreOf 2 (GLBPrimeCore p (nclIn H X)) ≠ ⊥ :=
  CFSG.AGLEmbedding.pCoreOf_two_primeCore_ne_bot h.prime h.ne_two h.charTwo.2
    (hXR.trans h.le_H) (h.isPGroup_R.to_le hXR) hX1

end AGLPair

theorem D2Escape.toPair {G : Type} [Group G] [Finite G] {p : ℕ} {P : Sylow p G}
    {M A H R : Subgroup G} (h : D2Escape p P M A H R) (hglob : AGLGlobal G)
    (htwo : pCoreOf 2 (H ⊓ M) = pCoreOf 2 H) : AGLPair p M H R where
  glob := hglob
  prime := h.prime
  ne_two := h.ne_two
  maxTwoLocal_M := h.maxTwoLocal_M
  maxTwoLocal_H := h.maxTwoLocal_H
  le_H := h.le_H
  le_M := h.le_M
  isSylow := h.isSylow
  not_le := h.not_le
  primeCore_le := h.primeCore_le
  twoCore_inf := htwo

end CFSG.AGLEmbeddingD2
