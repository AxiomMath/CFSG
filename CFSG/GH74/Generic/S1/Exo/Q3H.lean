module

public import CFSG.GH74.Generic.S1.Exo.Q3
public import CFSG.GH74.Generic.S1.Exo.Q3Hyp
public import CFSG.GH74.GLS.Balance.Bender.Final

public section

namespace CFSG.GH74.Generic.S1.Exo

open CFSG CFSG.GH74 CFSG.GH74.L5U5 Subgroup CFSG.GH74.Generic CFSG.GH74.GLS
  CFSG.Assembly.LowTwoRank CFSG.RankThreeCoreUniqueness.Helpers
open scoped commutatorElement MatrixGroups

@[expose] def Q3H : Prop :=
  ∀ (H : Type) [Group H] [Finite H] (c y : H) (JA JB : Subgroup H), Nbhd3Hyp H c y JA JB →
    ∀ u : H, u * u = 1 → ∀ P : Subgroup H, IsSimpleGroup ↥P → Nat.card ↥P = 360 → P ≤ layer H →
      P ≤ centralizer ({u} : Set H) →
      (∀ M : Subgroup H, ⁅M, M⁆ = M → M ≤ centralizer ({u} : Set H) → M ≤ P) → False

variable {G : Type} [Group G] [Finite G] {F : Type} [Field F] {S : Subgroup (GL (Fin 4) F)}

theorem exists_layer_with_z0_core (mc : ModelCore S) (hExact : S1LiftExactProp) {x : G}
    {K : Subgroup (CentralizerBar x)} (hset : S1Setup G x K) (hfront : S1Front G x K) (e : ↥K ≃* ↥S) {c : G}
    (hc : c ∈ centralizer ({x} : Set G)) (hc2 : orderOf c = 2)
    (hcL : (⟨c, hc⟩ : ↥(centralizer ({x} : Set G))) ∈ liftL x K) (hcne : barOf hc ≠ xbar x) :
    ∃ D : LayerData x S, D.K = K ∧ D.ι mc.z0 = c := by
  classical
  have hx : orderOf x = 2 := hset.inv
  have hxK : xbar x ∈ K := hset.shape.2
  set D₀ := layerOf hExact hset hfront e with hD₀
  obtain ⟨s, hs⟩ : ∃ s : ↥S, D₀.ι s = c := by
    refine ⟨D₀.liftIso.symm ⟨⟨c, hc⟩, hcL⟩, ?_⟩
    have h1 : D₀.ιC (D₀.liftIso.symm ⟨⟨c, hc⟩, hcL⟩) = ⟨c, hc⟩ := by
      change (((D₀.liftIso (D₀.liftIso.symm ⟨⟨c, hc⟩, hcL⟩)) : ↥(liftL x D₀.K)) :
        ↥(centralizer ({x} : Set G))) = _
      rw [MulEquiv.apply_symm_apply]
    exact congrArg Subtype.val h1
  have hc2' : c * c = 1 := by rw [← sq, ← hc2]; exact pow_orderOf_eq_one c
  have hs2 : s * s = 1 := D₀.ι_injective (by rw [map_mul, hs, hc2', map_one])
  have hc1 : c ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hc2
    omega
  have hs1 : s ≠ 1 := fun h => hc1 (by rw [← hs, h, map_one])
  have hsneg : s ≠ mc.neg := by
    intro h
    apply hcne
    have hcx : c = x := by rw [← hs, h]; exact ι_neg_eq_core mc D₀ hx hxK
    subst hcx
    rfl
  obtain ⟨P, hP⟩ := mc.norm s hs2 hs1 hsneg
  refine ⟨D₀.conjIso (MulAut.conj P), rfl, ?_⟩
  rw [LayerData.conjIso_ι, MulAut.conj_symm_apply, ← hs]
  congr 1
  rw [← hP]
  group

theorem s1LayerCmpQ3_of_q3H (hExact : S1LiftExactProp) (hq3 : Q3H) : S1LayerCmpQ3 := by
  intro G _ _ x K hset hfront hmodel c hc hc2 hcL hcne t hxt hconj P hPs hP360 hPlayer hPc hPmax
  classical
  have hcx : c ≠ x := by
    intro h
    subst h
    exact hcne rfl
  rcases hmodel with ⟨hε, hq4, F, _, _, hF, ⟨e⟩⟩ | ⟨hε, hq4, F, _, _, hF, ⟨e⟩⟩
  swap
  · norm_num at hε
  have hF4 : Nat.card F % 4 = 3 := by omega
  obtain ⟨D, hDK, hDc⟩ := exists_layer_with_z0_core (linModelCore hF4) hExact hset hfront e hc hc2 hcL hcne
  have hxK : xbar x ∈ D.K := hDK ▸ hset.shape.2
  obtain ⟨y, JA, JB, hyp⟩ := nbhd3Hyp_of_classical Balance.solvableL2PrimeBalance_proved hF D hset.simple hset.nonab
    hset.gen4 hset.kgh hset.inv hxK hDc hc2 hcx
  obtain ⟨g, hg⟩ := isConj_iff.1 hconj
  subst hg
  set φ : CentralizerBar c ≃* CentralizerBar (g * c * g⁻¹) := barConj c g with hφ
  set P' : Subgroup (CentralizerBar c) := P.comap φ.toMonoidHom with hP'
  have hmapP : P'.map φ.toMonoidHom = P := Subgroup.map_comap_eq_self_of_surjective φ.surjective P
  let eP : ↥P' ≃* ↥P := (P'.equivMapOfInjective φ.toMonoidHom φ.injective).trans
    (MulEquiv.subgroupCongr hmapP)
  have hlay := layer_map_mulEquiv' φ
  set u : CentralizerBar c := φ.symm (proj (g * c * g⁻¹) ⟨x, hxt⟩) with hu
  have hφu : φ u = proj (g * c * g⁻¹) ⟨x, hxt⟩ := MulEquiv.apply_symm_apply _ _
  have hx2 : x * x = 1 := by rw [← sq, ← hset.inv]; exact pow_orderOf_eq_one x
  refine hq3 (CentralizerBar c) (xbar c) y JA JB hyp u ?_ P' (by have := hPs; exact eP.isSimpleGroup) ?_ ?_ ?_ ?_
  · apply φ.injective
    rw [map_mul, hφu, map_one, ← map_mul]
    have : (⟨x, hxt⟩ : ↥(centralizer ({g * c * g⁻¹} : Set G))) * ⟨x, hxt⟩ = 1 := Subtype.ext hx2
    rw [this, map_one]
  · rw [Nat.card_congr eP.toEquiv]
    exact hP360
  · intro p hp
    have hp' : φ p ∈ P := hp
    have h1 := hPlayer hp'
    rw [← hlay] at h1
    obtain ⟨l, hl, hlp⟩ := h1
    have : l = p := φ.injective hlp
    rw [← this]
    exact hl
  · intro p hp
    have hp' : φ p ∈ P := hp
    rw [mem_centralizer_singleton_iff]
    apply φ.injective
    rw [map_mul, map_mul, hφu]
    exact mem_centralizer_singleton_iff.1 (hPc hp')
  · intro M hM hMc
    have hMperf : ⁅M.map φ.toMonoidHom, M.map φ.toMonoidHom⁆ = M.map φ.toMonoidHom := by
      rw [← Subgroup.map_commutator, hM]
    have hMc' : M.map φ.toMonoidHom ≤ centralizer ({proj (g * c * g⁻¹) ⟨x, hxt⟩} : Set _) := by
      rintro _ ⟨m, hm, rfl⟩
      rw [mem_centralizer_singleton_iff, ← hφu]
      change φ m * φ u = φ u * φ m
      rw [← map_mul, ← map_mul]
      exact congrArg φ (mem_centralizer_singleton_iff.1 (hMc hm))
    intro m hm
    have : φ m ∈ P := hPmax _ hMperf hMc' ⟨m, hm, rfl⟩
    exact this

theorem s1FrameExists_of_nbhd_q3H (hExact : S1LiftExactProp) (hNb : NbhdNoPrime) (hq3 : Q3H) :
    S1FrameExists :=
  s1FrameExists_of_nbhd_q3 hExact hNb (s1LayerCmpQ3_of_q3H hExact hq3)


end CFSG.GH74.Generic.S1.Exo
