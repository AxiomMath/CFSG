module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.L2Survivor
public import CFSG.LocalAnalysis.AGLEmbedding.SurvivorTransfer

public section

namespace CFSG.AGLEmbeddingD2

open CFSG.Open CFSG.PreuniquenessRankFour.Helpers CFSG.RankThreeCoreUniqueness.Helpers
open CFSG.AGLEmbedding

variable {G : Type} [Group G] [Finite G] {p : ℕ} {P : Sylow p G} {M A H R : Subgroup G}

theorem D2Escape.primeCore_inf_eq_iff (h : D2Escape p P M A H R) :
    GLBPrimeCore p (H ⊓ M) = GLBPrimeCore p H ↔
      primeComplementCore (G := ((((H ⊓ M).subgroupOf H).map
        (QuotientGroup.mk' (primeComplementCore (G := H) p)) : Subgroup _) : Type _)) p = ⊥ := by
  set O := primeComplementCore (G := H) p with hO
  set B := (H ⊓ M).subgroupOf H with hB
  have hOB : O ≤ B := by
    rw [hO, hB, ← glbPrimeCore_subgroupOf]
    exact glbPrimeCore_subgroupOf_le_inf h.primeCore_le
  let φ : B →* B.map (QuotientGroup.mk' O) := (QuotientGroup.mk' O).subgroupMap B
  have hker : φ.ker = O.subgroupOf B := by
    ext a
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, ← OneMemClass.coe_eq_one]
    exact QuotientGroup.eq_one_iff (a : H)
  have hkercop : p.Coprime (Nat.card φ.ker) := by
    rw [hker, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hOB).toEquiv]
    exact primeComplementCore_coprime p
  refine Iff.trans ?_ (primeComplementCore_eq_bot_iff_le_ker φ
    ((QuotientGroup.mk' O).subgroupMap_surjective B) hkercop).symm
  rw [hker]
  have hge : GLBPrimeCore p H ≤ GLBPrimeCore p (H ⊓ M) :=
    le_glbPrimeCore (_root_.le_inf (glbPrimeCore_le p H) h.primeCore_le)
      (inf_le_left.trans (le_normalizer_glbPrimeCore p H)) (glbPrimeCore_coprime p H)
  have hHM : GLBPrimeCore p (H ⊓ M) =
      ((primeComplementCore (G := B) p).map B.subtype).map H.subtype := by
    have := primeComplementCoreOf_map_subtype p H B
    rw [hB, Subgroup.map_subgroupOf_eq_of_le inf_le_left] at this
    rw [glbPrimeCore_eq_primeComplementCoreOf, ← this]
    rfl
  have hH : GLBPrimeCore p H = O.map H.subtype := glbPrimeCore_eq_primeComplementCoreOf p H
  have key : GLBPrimeCore p (H ⊓ M) ≤ GLBPrimeCore p H ↔
      primeComplementCore (G := B) p ≤ O.subgroupOf B := by
    rw [hHM, hH, Subgroup.map_le_map_iff_of_injective H.subtype_injective]
    exact Subgroup.map_le_iff_le_comap
  rw [← key]
  exact ⟨fun heq => heq.le, fun hle => le_antisymm hle hge⟩

theorem D2Escape.twoCore_inf_eq_of_primeCore_inf_eq (h : D2Escape p P M A H R)
    (hU : GLBPrimeCore p (H ⊓ M) = GLBPrimeCore p H) : pCoreOf 2 (H ⊓ M) = pCoreOf 2 H :=
  pCoreOf_inf_eq_of_glbPrimeCore_inf_eq Nat.prime_two
    (Nat.coprime_two_right.mpr (h.prime.odd_of_ne_two h.ne_two)) h.primeCore_le hU

section LinTwo

variable {Rbar : Sylow p (H ⧸ primeComplementCore (G := H) p)}
  {K : Subgroup (H ⧸ primeComplementCore (G := H) p)}

theorem D2Escape.toPair_of_psl2 [Fact p.Prime] (h : D2Escape p P M A H R) (hglob : AGLGlobal G)
    (hK : D2AlmostSimple p _ Rbar ((A.subgroupOf H).map (QuotientGroup.mk' (primeComplementCore p)))
      (((H ⊓ M).subgroupOf H).map (QuotientGroup.mk' (primeComplementCore p))) K)
    (e : K ≃* PSL2GF p 2) : AGLPair p M H R :=
  h.toPair hglob (h.twoCore_inf_eq_of_primeCore_inf_eq
    (h.primeCore_inf_eq_iff.mpr (hK.primeComplementCore_eq_bot_of_psl2 e)))

theorem D2Escape.survivorData_of_psl2 [Fact p.Prime] (h : D2Escape p P M A H R)
    (hglob : AGLGlobal G)
    (hRbar : (Rbar : Subgroup _) = (R.subgroupOf H).map (QuotientGroup.mk' (primeComplementCore p)))
    (hK : D2AlmostSimple p _ Rbar ((A.subgroupOf H).map (QuotientGroup.mk' (primeComplementCore p)))
      (((H ⊓ M).subgroupOf H).map (QuotientGroup.mk' (primeComplementCore p))) K)
    (e : K ≃* PSL2GF p 2) : AGLSurvivorData p M H R A where
  pair := h.toPair_of_psl2 hglob hK e
  le_R := h.A_le
  ne_bot := by
    intro hbot
    have hc := h.card_A
    rw [hbot, Subgroup.card_bot] at hc
    have := Nat.one_lt_pow two_ne_zero h.prime.one_lt
    omega
  normal_dichotomy := fun _ hY hYN =>
    le_glbPrimeCore_or_le_of_forall h.primeCore_le (h.A_le.trans h.le_H)
      (h.isPGroup.to_le h.A_le) (fun _ hW hWn => hK.dichotomy_of_psl2 e hW hWn) hY hYN
  centralizer_le := centralizer_le_of_map (fun _ hx =>
    hRbar ▸ hK.A_le (hK.centralizer_A_le_of_psl2 e hx.2))

end LinTwo

end CFSG.AGLEmbeddingD2
