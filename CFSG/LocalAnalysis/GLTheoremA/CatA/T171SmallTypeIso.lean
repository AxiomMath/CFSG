module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171SmallTypeDefs
import CFSG.LocalAnalysis.GLTheoremA.CatA.S172XLayer
import CFSG.LocalAnalysis.GLTheoremA.CatB.HStdExclTE6Lang

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T171S

open CFSG.Open

variable {G₀ G₁ : Type} [Group G₀] [Group G₁]

theorem TwoLocal.map {E : Subgroup G₀} (h : TwoLocal E) (f : G₀ →* G₁)
    (hf : Function.Injective f) : TwoLocal (E.map f) := by
  obtain ⟨P, hP2, hP1, hEN⟩ := h
  exact ⟨P.map f, hP2.map f, fun hbot => hP1 ((Subgroup.map_eq_bot_iff_of_injective P hf).mp hbot),
    (Subgroup.map_mono hEN).trans (Subgroup.le_normalizer_map f)⟩

private theorem centralizer_singleton_mulEquiv (e : G₀ ≃* G₁) (y : G₀) :
    Subgroup.centralizer ({e y} : Set G₁) =
      (Subgroup.centralizer ({y} : Set G₀)).map e.toMonoidHom := by
  rw [← Set.image_singleton, CFSG.OrderReductions.NormalizerAuxiliary.centralizer_image_eq]

private theorem ker_le_center (e : G₀ ≃* G₁) :
    ∀ g : G₀, e.toMonoidHom g = 1 → g ∈ Subgroup.center G₀ := fun g hg => by
  rw [(map_eq_one_iff _ e.injective).1 hg]
  exact Subgroup.one_mem _

theorem glaLayer_centralizer_mulEquiv (e : G₀ ≃* G₁) (y : G₀) :
    GLALayer (Subgroup.centralizer ({e y} : Set G₁)) =
      (GLALayer (Subgroup.centralizer ({y} : Set G₀))).map e.toMonoidHom := by
  rw [centralizer_singleton_mulEquiv]
  exact S172X.glaLayer_map_eq e.toMonoidHom (ker_le_center e) _

theorem stdAt_map_iff (e : G₀ ≃* G₁) (Bb : Subgroup G₀) (y : G₀) :
    StdAt (Bb.map e.toMonoidHom) (e y) ↔ StdAt Bb y := by
  unfold StdAt
  have hL := glaLayer_centralizer_mulEquiv e y
  have hcomp : IsComponentOf (GLALayer (Subgroup.centralizer ({e y} : Set G₁)))
      (Subgroup.centralizer ({e y} : Set G₁)) ↔
      IsComponentOf (GLALayer (Subgroup.centralizer ({y} : Set G₀)))
        (Subgroup.centralizer ({y} : Set G₀)) := by
    rw [centralizer_singleton_mulEquiv]
    exact S172X.isComponentOf_glaLayer_map_iff e.toMonoidHom (ker_le_center e) _
  have hcent : Bb.map e.toMonoidHom ⊓
      Subgroup.centralizer (GLALayer (Subgroup.centralizer ({e y} : Set G₁)) : Set G₁) =
      (Bb ⊓ Subgroup.centralizer (GLALayer (Subgroup.centralizer ({y} : Set G₀)) : Set G₀)).map
        e.toMonoidHom := by
    rw [hL, Subgroup.coe_map, MulEquiv.coe_toMonoidHom,
      CFSG.OrderReductions.NormalizerAuxiliary.centralizer_image_eq,
      Subgroup.map_inf_eq _ _ _ e.injective]
  have hz : Subgroup.zpowers (e y) = (Subgroup.zpowers y).map e.toMonoidHom :=
    (MonoidHom.map_zpowers e.toMonoidHom y).symm
  rw [hcomp, hcent, hz]
  exact and_congr_right fun _ => (Subgroup.map_injective e.injective).eq_iff

theorem smallOrd_map (e : G₀ ≃* G₁) {X : Subgroup G₀} (h : HStdExcl.SmallOrd X) :
    HStdExcl.SmallOrd (X.map e.toMonoidHom) :=
  HStdExcl.smallOrd_of_mulEquiv (X.equivMapOfInjective e.toMonoidHom e.injective) h

theorem smallModel_map (e : G₀ ≃* G₁) {Bb : Subgroup G₀} (h : SmallModel G₀ Bb) :
    SmallModel G₁ (Bb.map e.toMonoidHom) := by
  have hc : Nat.card (Bb.map e.toMonoidHom) = Nat.card Bb :=
    Subgroup.card_map_of_injective e.injective
  refine ⟨h.elem.map _, hc ▸ h.card_ge, hc ▸ h.card_le, h.twoLocal.map _ e.injective, ?_, ?_, ?_⟩
  · intro E hE hEl
    have hE' := h.max (E.map e.symm.toMonoidHom) (hE.map _) (hEl.map _ e.symm.injective)
    rw [Subgroup.card_map_of_injective e.symm.injective] at hE'
    rw [hc]
    exact hE'
  · obtain ⟨d, hdB, hd1, hstd⟩ := h.std
    refine ⟨e d, Subgroup.mem_map_of_mem _ hdB, fun h1 => hd1 ((map_eq_one_iff _ e.injective).1 h1),
      (stdAt_map_iff e Bb d).2 hstd⟩
  · rintro y' hy' hy1 hstd
    obtain ⟨y, hyB, rfl⟩ := Subgroup.mem_map.1 hy'
    have hstd' := (stdAt_map_iff e Bb y).1 hstd
    have hy1' : y ≠ 1 := fun h1 => hy1 (by rw [h1, map_one])
    have hs := smallOrd_map e (h.small y hyB hy1' hstd')
    change HStdExcl.SmallOrd (GLALayer (Subgroup.centralizer ({e y} : Set G₁)))
    rw [glaLayer_centralizer_mulEquiv]
    exact hs

theorem noSmallModel_of_mulEquiv (e : G₀ ≃* G₁) (h : NoSmallModel G₁) : NoSmallModel G₀ :=
  fun Bb hB => h _ (smallModel_map e hB)

end CFSG.LocalAnalysis.GLTheoremA.T171S

end
