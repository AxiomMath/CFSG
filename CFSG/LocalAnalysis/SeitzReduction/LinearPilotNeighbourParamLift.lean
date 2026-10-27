module

public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotNeighbourParamTorus
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotBLift
import CFSG.LocalAnalysis.SeitzReduction.LinearPilotRootSL2Aut

public section

namespace CFSG.SeitzReduction.LinearPilot

open Subgroup Matrix CFSG.LocalAnalysis.ComponentInitial
open CFSG.Quasithin (perfectCore)
open CFSG.SeitzReduction.F4Pilot (centralizerPerfectCore HasBLift oddCoreLift)

section Lift

variable {G : Type*} [Group G] [Finite G]

theorem centralizerPerfectCore_eq_map_perfectCore_top (X : Subgroup G) :
    centralizerPerfectCore X = (perfectCore (⊤ : Subgroup (centralizer (X : Set G)))).map
      (centralizer (X : Set G)).subtype := by
  rw [CFSG.Quasithin.map_perfectCore, ← MonoidHom.range_eq_map, range_subtype]
  rfl

theorem exists_surjective_centralizerPerfectCore_of_perfectCore_eq {X : Subgroup G}
    {Kc : Subgroup (centralizer (X : Set G) ⧸ oddCore (centralizer (X : Set G)))}
    (hcore : perfectCore (⊤ : Subgroup (centralizer (X : Set G) ⧸
      oddCore (centralizer (X : Set G)))) = Kc) (hB : HasBLift Kc) :
    ∃ q : centralizerPerfectCore X →* Kc, Function.Surjective q ∧
      q.ker ≤ center (centralizerPerfectCore X) ∧
      ∀ y : centralizerPerfectCore X, (q y : centralizer (X : Set G) ⧸
        oddCore (centralizer (X : Set G))) = QuotientGroup.mk' (oddCore (centralizer (X : Set G)))
          ⟨(y : G), F4Pilot.centralizerPerfectCore_le_centralizer X y.2⟩ := by
  have hle : centralizerPerfectCore X ≤ centralizer (X : Set G) :=
    F4Pilot.centralizerPerfectCore_le_centralizer X
  have hE := centralizerPerfectCore_eq_map_perfectCore_top X
  have hmemE : ∀ y : centralizerPerfectCore X,
      (⟨(y : G), hle y.2⟩ : centralizer (X : Set G)) ∈
        perfectCore (⊤ : Subgroup (centralizer (X : Set G))) := by
    intro y
    have hy : (y : G) ∈ (perfectCore (⊤ : Subgroup (centralizer (X : Set G)))).map
        (centralizer (X : Set G)).subtype := hE ▸ y.2
    obtain ⟨z, hz, hzy⟩ := hy
    have : z = ⟨(y : G), hle y.2⟩ := Subtype.ext hzy
    rwa [← this]
  have hπcore : (perfectCore (⊤ : Subgroup (centralizer (X : Set G)))).map
      (QuotientGroup.mk' (oddCore (centralizer (X : Set G)))) = Kc := by
    rw [CFSG.Quasithin.map_perfectCore, map_top_of_surjective _ (QuotientGroup.mk'_surjective _),
      hcore]
  have hmemK : ∀ y : centralizerPerfectCore X,
      QuotientGroup.mk' (oddCore (centralizer (X : Set G))) ⟨(y : G), hle y.2⟩ ∈ Kc := fun y =>
    hπcore ▸ mem_map_of_mem _ (hmemE y)
  let q : centralizerPerfectCore X →* Kc :=
    ((QuotientGroup.mk' (oddCore (centralizer (X : Set G)))).comp
      (Subgroup.inclusion hle)).codRestrict Kc fun y => hmemK y
  refine ⟨q, ?_, ?_, fun y => rfl⟩
  ·
    rintro ⟨k, hk⟩
    rw [← hπcore] at hk
    obtain ⟨z, hz, rfl⟩ := hk
    have hzE : (z : G) ∈ centralizerPerfectCore X := by
      rw [hE]
      exact mem_map_of_mem _ hz
    exact ⟨⟨(z : G), hzE⟩, Subtype.ext rfl⟩
  ·
    have hlift : perfectCore (⊤ : Subgroup (centralizer (X : Set G))) ≤ oddCoreLift Kc :=
      CFSG.Quasithin.le_perfectCore_of_perfect (fun z hz => by
        rw [mem_comap, ← hπcore]
        exact mem_map_of_mem _ hz) (CFSG.Quasithin.perfectCore_perfect _)
    intro y hy
    have hyO : (⟨(y : G), hle y.2⟩ : centralizer (X : Set G)) ∈
        oddCore (centralizer (X : Set G)) := by
      have h1 : QuotientGroup.mk' (oddCore (centralizer (X : Set G))) ⟨(y : G), hle y.2⟩ = 1 :=
        congrArg Subtype.val (MonoidHom.mem_ker.1 hy)
      exact (QuotientGroup.eq_one_iff _).1 h1
    rw [mem_center_iff]
    intro y'
    have hc := mem_centralizer_iff.1 (hB (hlift (hmemE y'))) _ hyO
    apply Subtype.ext
    exact (congrArg Subtype.val hc).symm

end Lift

section Assembly

variable {G : Type*} [Group G] {L : Subgroup G} {n : ℕ} {K : Type*} [Field K] {F : Type}
  [Field F]

theorem nonempty_fieldNeighbourParam_of_component [Finite G] [Finite K] [CharP K 2] [Finite F]
    (e : L ≃* LinearFlag.projectiveSL n K) {t : G} (htL : t ∈ centralizer (L : Set G))
    (ι : K →+* F) {σ : F ≃+* F} (hσ : σ * σ = 1) (hfix : ∀ x : F, σ x = x ↔ x ∈ Set.range ι)
    (Nb : Neighbour n) {m : ℕ} (eN : Nb.index ≃ Fin m) (hm : 3 ≤ m) (hF : 5 ≤ Nat.card F)
    (htX : t ∈ centralizer (modelToG e (Nb.torus K) : Set G))
    {Kc : Subgroup (centralizer (modelToG e (Nb.torus K) : Set G) ⧸
      oddCore (centralizer (modelToG e (Nb.torus K) : Set G)))}
    (hcore : perfectCore (⊤ : Subgroup (centralizer (modelToG e (Nb.torus K) : Set G) ⧸
      oddCore (centralizer (modelToG e (Nb.torus K) : Set G)))) = Kc) (hB : HasBLift Kc)
    (hsN : QuotientGroup.mk' (oddCore (centralizer (modelToG e (Nb.torus K) : Set G))) ⟨t, htX⟩ ∈
      normalizer (Kc : Set (centralizer (modelToG e (Nb.torus K) : Set G) ⧸
        oddCore (centralizer (modelToG e (Nb.torus K) : Set G)))))
    (ψ : Kc ≃* LinearFlag.projectiveSL m F)
    (hψD : ∀ (x : SpecialLinearGroup (Fin m) K)
      (hx : ((e.symm (LinearFlag.proj n K (blockSLEquiv Nb.index eN x)) : L) : G) ∈
        centralizer (modelToG e (Nb.torus K) : Set G))
      (hk : QuotientGroup.mk' (oddCore (centralizer (modelToG e (Nb.torus K) : Set G)))
        ⟨_, hx⟩ ∈ Kc),
      ψ ⟨_, hk⟩ = LinearFlag.proj m F (SpecialLinearGroup.map ι x))
    (hψt : ∀ k : Kc, ψ (Kc.normalizerMonoidHom ⟨_, hsN⟩ k) = LinearFlag.fieldAut m F σ (ψ k)) :
    Nonempty (FieldNeighbourParam e t ι σ (modelToG e (Nb.torus K)) Nb.index) := by
  obtain ⟨q, hq, hqker, hqapp⟩ :=
    exists_surjective_centralizerPerfectCore_of_perfectCore_eq hcore hB
  have hcard : 3 ≤ Nb.index.card := by
    rw [← Fintype.card_coe, Fintype.card_congr eN, Fintype.card_fin]
    exact hm
  have hD : modelToG e (blockSL (K := K) Nb.index) ≤
      centralizerPerfectCore (modelToG e (Nb.torus K)) :=
    modelToG_blockSL_index_le_neighbourCore e Nb (commutator_blockSL_eq_of_three_le hcard)
  have ht : t ∈ normalizer (centralizerPerfectCore (modelToG e (Nb.torus K)) : Set G) :=
    le_normalizer_neighbourCore e htL Nb
  refine nonempty_fieldNeighbourParam_of_proj_of_fixedField e t ι hσ hfix eN hm hF
    (ψ.toMonoidHom.comp q) (ψ.surjective.comp hq) ?_ hD ?_ ht ?_
    fun c => symm_mem_normalizer_neighbourCore e (proj_torusDiagSL_mem_normalizer_torus Nb c)
  ·
    intro y hy
    apply hqker
    have h1 : ψ (q y) = ψ 1 := by
      rw [map_one]
      exact hy
    exact ψ.injective h1
  ·
    intro x
    have hx := hD (symm_mem_modelToG e (proj_mem_blockSL (blockSLEquiv Nb.index eN x).2))
    have hxH := F4Pilot.centralizerPerfectCore_le_centralizer _ hx
    have hk : QuotientGroup.mk' (oddCore (centralizer (modelToG e (Nb.torus K) : Set G)))
        ⟨_, hxH⟩ ∈ Kc := by
      rw [← hqapp ⟨_, hx⟩]
      exact (q ⟨_, hx⟩).2
    have hq' : q ⟨_, hx⟩ = ⟨_, hk⟩ := Subtype.ext (hqapp _)
    rw [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, hq']
    exact hψD x hxH hk
  ·
    intro y
    have hqt : q ((centralizerPerfectCore (modelToG e (Nb.torus K))).normalizerMonoidHom ⟨t, ht⟩
        y) = Kc.normalizerMonoidHom ⟨_, hsN⟩ (q y) := by
      apply Subtype.ext
      have e1 : (⟨(((centralizerPerfectCore (modelToG e (Nb.torus K))).normalizerMonoidHom
          ⟨t, ht⟩ y : centralizerPerfectCore (modelToG e (Nb.torus K))) : G),
            F4Pilot.centralizerPerfectCore_le_centralizer _
              ((centralizerPerfectCore (modelToG e (Nb.torus K))).normalizerMonoidHom
                ⟨t, ht⟩ y).2⟩ : centralizer (modelToG e (Nb.torus K) : Set G)) =
          ⟨t, htX⟩ * ⟨(y : G), F4Pilot.centralizerPerfectCore_le_centralizer _ y.2⟩ *
            ⟨t, htX⟩⁻¹ := by
        apply Subtype.ext
        rw [Subgroup.normalizerMonoidHom_apply_apply_coe]
        rfl
      rw [Subgroup.normalizerMonoidHom_apply_apply_coe, hqapp, hqapp, e1, map_mul, map_mul,
        map_inv]
    show ψ (q ((centralizerPerfectCore (modelToG e (Nb.torus K))).normalizerMonoidHom ⟨t, ht⟩
      y)) = LinearFlag.fieldAut m F σ (ψ (q y))
    rw [hqt, hψt]

end Assembly

end CFSG.SeitzReduction.LinearPilot
