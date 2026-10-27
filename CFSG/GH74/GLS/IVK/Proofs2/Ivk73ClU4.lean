module

public import CFSG.GH74.GLS.IVK.Proofs2.Ivk73ClU4Glue
public import CFSG.GH74.GLS.IVK.Proofs2.Ivk73ClBridge
public import CFSG.GH74.GLS.IVK.Proofs2.Ivk73G4Main

public section

namespace CFSG.GH74.GLS.IVK

open CFSG CFSG.Blueprint Subgroup CFSG.Assembly.LowTwoRank
open CFSG.ComponentClassification.RestrictedStd
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open CFSG.ClassicalGroups.UnitaryFlag CFSG.ComponentClassification.CatalogueBUnitaryB
open CFSG.ComponentClassification.OddClassSelector

theorem su4_socle_false {A : Type} [Group A] [Finite A] {W : Subgroup A} [W.Normal]
    (hWs : IsSimpleGroup W) (hWnab : ∃ x y : W, x * y ≠ y * x)
    (hCW : centralizer (W : Set A) = ⊥) {a b : A} (ha : orderOf a = 2) (hb : orderOf b = 2)
    (hab : a * b = b * a) (hne : a ≠ b) {L : Subgroup A}
    (hLa : CFSG.Assembly.IsComponentOf L (W ⊓ centralizer {a}))
    (hLb : CFSG.Assembly.IsComponentOf L (W ⊓ centralizer {b}))
    (hLab : CFSG.Assembly.IsComponentOf L (W ⊓ centralizer {a * b})) (hs : SmallSource L)
    {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hf : 1 ≤ f) {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = (p ^ f) ^ 2) (e : W ≃* StatedProj (StatedSU 4 (p ^ f) K)) : False := by
  classical
  have hud : UnitaryFieldData p f K := ⟨hp, hf, by rw [hK, ← pow_mul, mul_comm]⟩
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨R, hR⟩ := (unitary_hyperbolic_model_transport hud (r := 2) (ε := 0) (by norm_num)
    (by norm_num)).1
  let θ : W ≃* hypPSU hud 2 0 := (e.trans (unitaryPSUEquiv hud (by norm_num)).symm).trans
    (hypProjTransport hud (R := R) hR).symm
  have : IsSimpleGroup (hypPSU hud 2 0) := θ.symm.isSimpleGroup
  have hnab : ∃ x y : hypPSU hud 2 0, x * y ≠ y * x := by
    obtain ⟨x, y, hxy⟩ := hWnab
    refine ⟨θ x, θ y, fun h => hxy (θ.injective ?_)⟩
    rw [map_mul, map_mul, h]
  have hZ := CFSG.ComponentClassification.OutcomeLocal.center_eq_bot_of_isSimpleGroup hnab
  have hcj := conj_injective hZ
  obtain ⟨ρ, hinj, hρW, -, -⟩ :=
    CFSG.ComponentClassification.OutcomeLocal.socle_extension hCW θ hZ
  have key : ∀ c : A, CFSG.Assembly.IsComponentOf L (W ⊓ centralizer {c}) →
      CFSG.Assembly.IsComponentOf ((L.map ρ).comap MulAut.conj) (CFSG.ComponentClassification.FixedCommutingProduct.fixedSubgroup (ρ c)) := by
    intro c hL
    obtain ⟨hWimg, hCWimg, -⟩ :=
      CFSG.ComponentClassification.OutcomeLocal.socle_images hinj θ hρW c
    have hL₁ := CFSG.ComponentClassification.SymmetricLocal.isComponentOf_map_of_injective ρ hinj hL
    rw [hCWimg] at hL₁
    exact (isComponentOf_comap_conj hcj hL₁).1
  have hXmap : (((L.map ρ).comap MulAut.conj).map MulAut.conj) = L.map ρ := by
    obtain ⟨hWimg, hCWimg, -⟩ :=
      CFSG.ComponentClassification.OutcomeLocal.socle_images hinj θ hρW a
    have hL₁ := CFSG.ComponentClassification.SymmetricLocal.isComponentOf_map_of_injective ρ hinj hLa
    rw [hCWimg] at hL₁
    exact (isComponentOf_comap_conj hcj hL₁).2
  let eLX : L ≃* ((L.map ρ).comap MulAut.conj) :=
    (L.equivMapOfInjective ρ hinj).trans ((MulEquiv.subgroupCongr hXmap.symm).trans
      (((L.map ρ).comap MulAut.conj).equivMapOfInjective _ hcj).symm)
  have hsX := smallSource_of_mulEquiv eLX hs
  have hα : orderOf (ρ a) = 2 := (orderOf_injective ρ hinj a).trans ha
  have hβ : orderOf (ρ b) = 2 := (orderOf_injective ρ hinj b).trans hb
  refine su4_triple_false hud hp2 hsX hα hβ (by rw [← map_mul, ← map_mul, hab])
    (fun h => hne (hinj h)) (key a hLa) (key b hLb) ?_
  rw [← map_mul]
  exact key (a * b) hLab

variable {N : Type} [Group N] [Finite N] {L K Q : Subgroup N}

theorem ivk73_u4 (p f : ℕ)
    (hp : p.Prime) (hp2 : p ≠ 2) (hf : 1 ≤ f) (_hmod : p ^ f % 8 ≠ 7) :
    Ivk73Empty (fun X _ => LieModel X .PSU 4 p f) := by
  intro N _ _ L K Q h hm
  have := h.normal
  obtain ⟨x, hxQ, y, hyQ, hx, hy, hne, hcomm⟩ :=
    C3.Layer1.U1a.exists_commuting_involutions h.Q_rank
  have hxC : x ∈ centralizer (K : Set N) := h.Q_sylow.le hxQ
  have hyC : y ∈ centralizer (K : Set N) := h.Q_sylow.le hyQ
  have hxy2 : orderOf (x * y) = 2 := orderOf_mul_of_commute hx hy hcomm hne
  have hxyC : x * y ∈ centralizer (K : Set N) := Subgroup.mul_mem _ hxC hyC
  have hcomp : ∀ c : N, orderOf c = 2 → c ∈ centralizer (K : Set N) →
      CFSG.Assembly.IsComponentOf K (L ⊓ centralizer {c}) := fun c hc2 hcC => by
    have hc := h.isComponentOf_centralizer hc2 hcC
    exact LocalAnalysis.ComponentInitial.isComponentOf_of_le hc (le_inf h.K_le hc.1) inf_le_right
  have hstated := CFSG.ComponentClassification.OddClassSelector.statedClassicalModel_of_lieModel hm
    (by simp [chevalleyExceptionalTags]) (by simp [reeTitsTags]) (by decide)
  obtain ⟨-, F, _, _, hF, ⟨e⟩⟩ := hstated
  exact su4_socle_false h.simple h.exists_noncomm h.centralizer_eq_bot hx hy hcomm hne
    (hcomp x hx hxC) (hcomp y hy hyC) (hcomp (x * y) hxy2 hxyC) h.smallSource hp hp2 hf hF e

end CFSG.GH74.GLS.IVK
