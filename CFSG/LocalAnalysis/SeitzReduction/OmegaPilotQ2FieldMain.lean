module

public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotQ2FieldEnd
public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotQ2PlusNbrMain
public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotQ2Minus
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotParamMain

public section

set_option linter.unusedSectionVars false

namespace CFSG.SeitzReduction.OmegaPilot

open Subgroup
open CFSG.Quasithin (perfectCore perfectCore_le perfectCore_perfect)
open CFSG.SeitzReduction.F4Pilot (centralizerPerfectCore)
open CFSG.SeitzReduction.UnitaryPilot (modelToG mem_modelToG)
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear (matrixProjectiveDerived)
open CFSG.ComponentClassification.CatalogueBOrthogonalPointData (coordinateQuadPlus
  coordinateQuadMinus)

section Join

variable {G : Type} [Group G]

@[expose] def anisoNeighbourJoin (L X : Subgroup G) : Subgroup G :=
  ⨆ l : L, centralizerPerfectCore (X.map (MulAut.conj (l : G)).toMonoidHom)

theorem centralizerPerfectCore_le_anisoNeighbourJoin (L X : Subgroup G) (l : L) :
    centralizerPerfectCore (X.map (MulAut.conj (l : G)).toMonoidHom) ≤ anisoNeighbourJoin L X :=
  le_iSup (fun l : L => centralizerPerfectCore (X.map (MulAut.conj (l : G)).toMonoidHom)) l

theorem mem_normalizer_anisoNeighbourJoin [Finite G] {L X : Subgroup G} (hXL : X ≤ L) {t : G}
    (htC : t ∈ centralizer (L : Set G)) :
    t ∈ normalizer (anisoNeighbourJoin L X : Set G) := by
  refine Subgroup.mem_normalizer_iff_map_conj_eq.2 ?_
  change (anisoNeighbourJoin L X).map (MulAut.conj t).toMonoidHom = anisoNeighbourJoin L X
  rw [anisoNeighbourJoin, Subgroup.map_iSup]
  refine iSup_congr fun l => ?_
  rw [F4Pilot.map_centralizerPerfectCore (MulAut.conj t)]
  congr 1
  have hXlL : X.map (MulAut.conj (l : G)).toMonoidHom ≤ L := by
    rintro _ ⟨x, hx, rfl⟩
    exact L.mul_mem (L.mul_mem l.2 (hXL hx)) (L.inv_mem l.2)
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    have hc : x * t = t * x := mem_centralizer_iff.1 htC x (hXlL hx)
    change t * x * t⁻¹ ∈ _
    rw [← hc, mul_inv_cancel_right]
    exact hx
  · intro hy
    refine ⟨y, hy, ?_⟩
    have hc : y * t = t * y := mem_centralizer_iff.1 htC y (hXlL hy)
    change t * y * t⁻¹ = y
    rw [← hc, mul_inv_cancel_right]

variable {P : Type*} [Group P]

theorem modelToG_trans_symm {P' : Type*} [Group P'] {L : Subgroup G} (e : L ≃* P) (Θ : P' ≃* P)
    (A : Subgroup P') : modelToG (e.trans Θ.symm) A = modelToG e (A.map Θ.toMonoidHom) := by
  ext g
  rw [mem_modelToG, mem_modelToG]
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨Θ x, ⟨x, hx, rfl⟩, rfl⟩
  · rintro ⟨_, ⟨x, hx, rfl⟩, rfl⟩
    exact ⟨x, hx, rfl⟩

theorem range_le_anisoNeighbourJoin [Finite G] [Finite P] {M : Type*} [Group M]
    {L : Subgroup G} (e : L ≃* M) (emb : M →* P) (X₀ : Subgroup M)
    (hgen : ⨆ y : M, perfectCore (centralizer
      (((X₀.map (MulAut.conj y).toMonoidHom).map emb : Subgroup P) : Set P)) = ⊤)
    {Φ : P →* G} (hΦ : ∀ x, Φ (emb x) = ((e.symm x : L) : G)) :
    Φ.range ≤ anisoNeighbourJoin L (modelToG e X₀) := by
  rw [MonoidHom.range_eq_map, ← hgen, Subgroup.map_iSup]
  refine iSup_le fun y => ?_
  refine le_trans ?_ (centralizerPerfectCore_le_anisoNeighbourJoin L (modelToG e X₀) (e.symm y))
  rw [← UnitaryPilot.modelToG_map_conj]
  refine F4Pilot.le_centralizerPerfectCore ?_ ?_
  · rw [← Subgroup.map_commutator, perfectCore_perfect]
  · rintro _ ⟨a, ha, rfl⟩
    rw [mem_centralizer_iff]
    intro g hg
    obtain ⟨x, hx, rfl⟩ := (mem_modelToG e).1 hg
    have hxa : emb x * a = a * emb x :=
      mem_centralizer_iff.1 (perfectCore_le _ ha) (emb x) ⟨x, hx, rfl⟩
    rw [← hΦ x, ← map_mul, ← map_mul, hxa]

end Join

theorem nonempty_plusModel_mulEquiv_of_card_eq {F F' : Type} [Field F] [Finite F] [CharP F 2]
    [Field F'] [Finite F'] [CharP F' 2] (h : Nat.card F' = Nat.card F) {n : ℕ} (hn : 1 ≤ n) :
    Nonempty (matrixProjectiveDerived (coordinateQuadPlus n F') ≃*
      matrixProjectiveDerived (coordinateQuadPlus n F)) := by
  have := Fintype.ofFinite F
  have := Fintype.ofFinite F'
  have φ : F' ≃+* F := FiniteField.ringEquivOfCardEq (by
    rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, h])
  exact ⟨(statedOmegaPlusEquiv F' n hn).symm.trans
    ((statedOmegaPlusCongr φ n).trans (statedOmegaPlusEquiv F n hn))⟩

section Plus

@[expose] def OmegaPlusTwoFieldGenInput : Prop :=
  ∀ (m : ℕ), 4 ≤ m → ∀ (K : Type) [Field K] [Finite K] [CharP K 2] (b c : K)
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0), Nat.card K = 2 →
    ∀ (F : Type) [Field F] [Finite F] [CharP F 2] (ι : K →+* F), Nat.card F = 4 →
      ⨆ y : matrixProjectiveDerived (coordinateQuadPlus (m + 2) K),
        perfectCore (centralizer (((((plusAnisoTorus m hirr).map
          (plusAnisoProjEquiv m hirr).toMonoidHom).map (MulAut.conj y).toMonoidHom).map
          (fieldEmbed ι (m + 2) (by omega)) :
            Subgroup (matrixProjectiveDerived (coordinateQuadPlus (m + 2) F))) :
          Set (matrixProjectiveDerived (coordinateQuadPlus (m + 2) F)))) = ⊤

@[expose] def OmegaPlusTwoFieldGlobalInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G), SeitzSetting G L →
    ∀ (m : ℕ), 4 ≤ m → ∀ (K : Type) [Field K] [Finite K] [CharP K 2] (b c : K)
      (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0), Nat.card K = 2 →
      ∀ (e : L ≃* matrixProjectiveDerived (coordinateQuadPlus (m + 2) K)) (t : G),
        orderOf t = 2 → centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t →
        ¬ (((modelToG (e.trans (plusAnisoProjEquiv m hirr).symm)
            (plusAnisoPerp (K := K) m b c)).subgroupOf
            (centralizer (modelToG (e.trans (plusAnisoProjEquiv m hirr).symm)
              (plusAnisoTorus m hirr) : Set G))).map
          (QuotientGroup.mk' (oddCore (centralizer
            (modelToG (e.trans (plusAnisoProjEquiv m hirr).symm)
              (plusAnisoTorus m hirr) : Set G))))).Normal →
        (∀ htX : t ∈ centralizer (modelToG (e.trans (plusAnisoProjEquiv m hirr).symm)
            (plusAnisoTorus m hirr) : Set G),
          NeighbourOvergroupOmega (QuotientGroup.mk' (oddCore (centralizer
              (modelToG (e.trans (plusAnisoProjEquiv m hirr).symm)
                (plusAnisoTorus m hirr) : Set G))) ⟨t, htX⟩)
            (((modelToG (e.trans (plusAnisoProjEquiv m hirr).symm)
                (plusAnisoPerp (K := K) m b c)).subgroupOf
                (centralizer (modelToG (e.trans (plusAnisoProjEquiv m hirr).symm)
                  (plusAnisoTorus m hirr) : Set G))).map
              (QuotientGroup.mk' (oddCore (centralizer
                (modelToG (e.trans (plusAnisoProjEquiv m hirr).symm)
                  (plusAnisoTorus m hirr) : Set G))))) (m + 1) 1) →
        OmegaRowAt t (modelToG (e.trans (plusAnisoProjEquiv m hirr).symm) (plusAnisoTorus m hirr))
          (modelToG (e.trans (plusAnisoProjEquiv m hirr).symm) (plusAnisoPerp (K := K) m b c))
          .field →
        ∃ (F : Type) (_ : Field F) (_ : Finite F) (_ : CharP F 2), Nat.card F = 4 ∧
          Nonempty (anisoNeighbourJoin L (modelToG (e.trans (plusAnisoProjEquiv m hirr).symm)
            (plusAnisoTorus m hirr)) ≃* matrixProjectiveDerived (coordinateQuadPlus (m + 2) F))

theorem omegaPlusTwoRowInput_field_of_inputs (hgen : OmegaPlusTwoFieldGenInput)
    (hglob : OmegaPlusTwoFieldGlobalInput) : OmegaPlusTwoRowInput .field := by
  intro G _ _ L hset m hm K _ _ _ b c hirr hK2 e t ht hKt hnn hN hrow
  obtain ⟨F', _, _, _, hF'4, ⟨ψ'⟩⟩ := hglob G L hset m hm K b c hirr hK2 e t ht hKt hnn hN hrow
  obtain ⟨F, _, _, ι, σ, hσ, hfix⟩ := SymplecticPilot.exists_quadraticExtension K
  have : CharP F 2 := charP_of_injective_ringHom ι.injective 2
  have hF4 : Nat.card F = 4 := by
    rw [SymplecticPilot.natCard_eq_two_pow_two_mul_of_fix ι (f := 1) (by rw [hK2, pow_one]) hσ
      hfix]
    norm_num
  obtain ⟨χ⟩ := nonempty_plusModel_mulEquiv_of_card_eq (F := F) (F' := F')
    (by rw [hF'4, hF4]) (n := m + 2) (by omega)
  have htC : t ∈ centralizer (L : Set G) := LinearPilot.mem_centralizer_of_inf_eq_zpowers hKt
  have hXL := UnitaryPilot.modelToG_le (e.trans (plusAnisoProjEquiv m hirr).symm)
    (plusAnisoTorus m hirr)
  refine false_of_plusFieldGlobal hset (by omega) e ht hKt ι hσ hfix
    (mem_normalizer_anisoNeighbourJoin hXL htC) (ψ'.trans χ) (fun Φ hΦ => ?_)
  rw [modelToG_trans_symm]
  exact range_le_anisoNeighbourJoin e (fieldEmbed ι (m + 2) (by omega)) _
    (hgen m hm K b c hirr hK2 F ι hF4) hΦ

end Plus

section Minus

@[expose] def OmegaMinusTwoFieldGenInput : Prop :=
  ∀ (n : ℕ) (hn : 6 ≤ n) (K : Type) [Field K] [Finite K] [CharP K 2] (b c : K),
    (∀ s : K, s ^ 2 + b * s + c ≠ 0) → Nat.card K = 2 →
    ∀ (F : Type) [Field F] [Finite F] [CharP F 2] (ι : K →+* F), Nat.card F = 4 →
      ⨆ y : matrixProjectiveDerived (coordinateQuadMinus n K (by omega) b c),
        perfectCore (centralizer ((((anisoTorus (K := K) (by omega) b c).map
          (MulAut.conj y).toMonoidHom).map (minusFieldEmbed ι (by omega) b c) :
            Subgroup (matrixProjectiveDerived (coordinateQuadMinus n F (by omega) (ι b) (ι c)))) :
          Set (matrixProjectiveDerived (coordinateQuadMinus n F (by omega) (ι b) (ι c))))) = ⊤

@[expose] def OmegaMinusTwoFieldGlobalInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G), SeitzSetting G L →
    ∀ (n : ℕ) (hn : 6 ≤ n) (K : Type) [Field K] [Finite K] [CharP K 2] (b c : K),
      (∀ s : K, s ^ 2 + b * s + c ≠ 0) → Nat.card K = 2 →
      ∀ (e : L ≃* matrixProjectiveDerived (coordinateQuadMinus n K (by omega) b c)) (t : G),
        orderOf t = 2 → centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t →
        ¬ (((modelToG e (anisoPerp (K := K) (by omega) b c)).subgroupOf
            (centralizer (modelToG e (anisoTorus (K := K) (by omega) b c) : Set G))).map
          (QuotientGroup.mk' (oddCore (centralizer
            (modelToG e (anisoTorus (K := K) (by omega) b c) : Set G))))).Normal →
        (∀ htX : t ∈ centralizer (modelToG e (anisoTorus (K := K) (by omega) b c) : Set G),
          NeighbourOvergroupOmega (QuotientGroup.mk' (oddCore (centralizer
              (modelToG e (anisoTorus (K := K) (by omega) b c) : Set G))) ⟨t, htX⟩)
            (((modelToG e (anisoPerp (K := K) (by omega) b c)).subgroupOf
                (centralizer (modelToG e (anisoTorus (K := K) (by omega) b c) : Set G))).map
              (QuotientGroup.mk' (oddCore (centralizer
                (modelToG e (anisoTorus (K := K) (by omega) b c) : Set G))))) (n - 1) 1) →
        OmegaRowAt t (modelToG e (anisoTorus (K := K) (by omega) b c))
          (modelToG e (anisoPerp (K := K) (by omega) b c)) .field →
        ∃ (F : Type) (_ : Field F) (_ : Finite F) (_ : CharP F 2), Nat.card F = 4 ∧
          Nonempty (anisoNeighbourJoin L (modelToG e (anisoTorus (K := K) (by omega) b c)) ≃*
            matrixProjectiveDerived (coordinateQuadPlus n F))

theorem omegaMinusTwoRowInput_field_of_inputs
    (hgen : OmegaMinusTwoFieldGenInput) (hglob : OmegaMinusTwoFieldGlobalInput) :
    OmegaMinusTwoRowInput .field := by
  intro G _ _ L hset n hn K _ _ _ b c hirr hK2 e t ht hKt hnn hN hrow
  obtain ⟨F', _, _, _, hF'4, ⟨ψ'⟩⟩ := hglob G L hset n hn K b c hirr hK2 e t ht hKt hnn hN hrow
  obtain ⟨F, _, _, ι, σ, hσ, hfix⟩ := SymplecticPilot.exists_quadraticExtension K
  have : CharP F 2 := charP_of_injective_ringHom ι.injective 2
  have hF4 : Nat.card F = 4 := by
    rw [SymplecticPilot.natCard_eq_two_pow_two_mul_of_fix ι (f := 1) (by rw [hK2, pow_one]) hσ
      hfix]
    norm_num
  obtain ⟨χ⟩ := nonempty_plusModel_mulEquiv_of_card_eq (F := F) (F' := F')
    (by rw [hF'4, hF4]) (n := n) (by omega)
  have hβ : σ (ι b) = ι b := (hfix (ι b)).2 ⟨b, rfl⟩
  have hγ : σ (ι c) = ι c := (hfix (ι c)).2 ⟨c, rfl⟩
  have hirrF : ∀ s : F, σ s = s → s ^ 2 + ι b * s + ι c ≠ 0 := by
    intro s hs h0
    obtain ⟨k, rfl⟩ := (hfix s).1 hs
    apply hirr k
    apply ι.injective
    rw [map_add, map_add, map_mul, map_pow, map_zero]
    exact h0
  obtain ⟨α, hα, -, hβ0⟩ := exists_root_frob_of_irreducible hσ hβ hγ hirrF
  have hαα : α ≠ -ι b - α := root_ne_other_of_ne_zero hβ0
  obtain ⟨r, rfl⟩ : ∃ r, n = r + 1 := ⟨n - 1, by omega⟩
  have htC : t ∈ centralizer (L : Set G) := LinearPilot.mem_centralizer_of_inf_eq_zpowers hKt
  have hXL := UnitaryPilot.modelToG_le e (anisoTorus (K := K) (by omega) b c)
  refine false_of_minusFieldGlobal hset hn hirr e ht hKt ι hσ hfix
    (mem_normalizer_anisoNeighbourJoin hXL htC)
    ((ψ'.trans χ).trans (minusPlusProjEquiv (r := r) (by omega) hα hαα).symm) (fun Φ hΦ => ?_)
  exact range_le_anisoNeighbourJoin e (minusFieldEmbed ι (by omega) b c) _
    (hgen (r + 1) hn K b c hirr hK2 F ι hF4) hΦ

end Minus

end CFSG.SeitzReduction.OmegaPilot
