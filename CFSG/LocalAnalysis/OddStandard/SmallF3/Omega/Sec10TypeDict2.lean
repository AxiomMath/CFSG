module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec10TypeDict
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec2FiveInv

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint CFSG.GH74.KGroups CFSG.ComponentClassification.CatFactsSmall
  CFSG.ComponentClassification.CatFactsSmall.PSp43 QuadraticMap

local notation "P45" => Equiv.Perm (Fin 45)

namespace TyDict

variable {G : Type} [Group G] {L : Subgroup G}
  {V : Type} [AddCommGroup V] [Module (ZMod 3) V] [FiniteDimensional (ZMod 3) V]
  {Q : QuadraticForm (ZMod 3) V}

theorem natCard_L (F : PspFrame L) : Nat.card ↥L = 25920 := by
  rw [← F.card_img (le_refl L), F.img_L, card_QP45]

theorem center_eq_bot (F : PspFrame L) (hQ : Q.Nondegenerate)
    (hdim : Module.finrank (ZMod 3) V = 5) (e : ↥L ⧸ Subgroup.center ↥L ≃* omegaProj hQ) :
    Subgroup.center ↥L = ⊥ := by
  have h1 : Nat.card (↥L ⧸ Subgroup.center ↥L) = 25920 := by
    rw [Nat.card_congr e.toEquiv, natCard_omegaProj_five hQ hdim]
  have h2 := Subgroup.card_mul_index (Subgroup.center ↥L)
  rw [Subgroup.index_eq_card, h1, natCard_L F] at h2
  exact Subgroup.eq_bot_of_card_eq _ (by omega)

@[expose] noncomputable def modelEquiv (hbot : Subgroup.center ↥L = ⊥) (hQ : Q.Nondegenerate)
    (e : ↥L ⧸ Subgroup.center ↥L ≃* omegaProj hQ) : ↥L ≃* omegaProj hQ :=
  MulEquiv.ofBijective (e.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center ↥L)))
    ⟨fun l l' h => by
      have h1 : (QuotientGroup.mk l : ↥L ⧸ Subgroup.center ↥L) = QuotientGroup.mk l' :=
        e.injective h
      have h2 := QuotientGroup.eq.1 h1
      rw [hbot, Subgroup.mem_bot, inv_mul_eq_one] at h2
      exact h2, fun w => by
      obtain ⟨q, rfl⟩ := e.surjective w
      obtain ⟨l, rfl⟩ := QuotientGroup.mk_surjective q
      exact ⟨l, rfl⟩⟩

theorem hasType_mul_self {x : ProjOrth Q} {r : ℕ} {α : ℤˣ} (h : HasType x r α) : x * x = 1 := by
  obtain ⟨-, t, htt, -, rfl⟩ := h
  rw [← map_mul, htt, map_one]

variable (hL : IsPSp43 L) (F : PspFrame L)
  (hQ : Q.Nondegenerate) (ε : ↥L ≃* omegaProj hQ)

theorem phi_eq_conjOf_iff (s : G) (hs : s ∈ normalizer (L : Set G)) (y : ProjOrth Q) :
    F.φ ⟨s, hs⟩ = conjOf hL F hQ ε y ↔
      ∀ l : ↥L, ((ε (PspFrame.conjL ⟨s, hs⟩ l) : omegaProj hQ) : ProjOrth Q) =
        y * (ε l : ProjOrth Q) * y⁻¹ := by
  constructor
  · intro h l
    have h1 : PspFrame.conjL ⟨s, hs⟩ l = indAut hQ ε y l := by
      apply F.ψ_injective
      rw [F.psi_conjL, psi_indAut hL F hQ ε, h]
    rw [h1, coe_eps_indAut]
  · intro h
    refine eq_conjOf hL F hQ ε (F.mem_A _) fun l => ?_
    have h1 : indAut hQ ε y l = PspFrame.conjL ⟨s, hs⟩ l := by
      apply ε.injective
      apply Subtype.ext
      rw [coe_eps_indAut, h]
    rw [h1, F.psi_conjL]

include hL in
theorem invCent_of_inducesTypeSome (r : ℕ) (α : ℤˣ) (N : ℕ)
    (hN : ∀ (W : Type) [AddCommGroup W] [Module (ZMod 3) W] [FiniteDimensional (ZMod 3) W]
      (R : QuadraticForm (ZMod 3) W) (hR : R.Nondegenerate), Module.finrank (ZMod 3) W = 5 →
      quadSign R = 1 → ∀ x : ProjOrth R, x * x = 1 → x ≠ 1 →
        (HasType x r α ↔ Nat.card (Subgroup.centralizer ({x} : Set (ProjOrth R))) = N))
    {s : G} (h : InducesTypeSome L s 5 1 r α) :
    ∃ hs : s ∈ normalizer (L : Set G), InvCent N (F.φ ⟨s, hs⟩) := by
  obtain ⟨W, i1, i2, i3, R, hR, e, x, hdim, hσ, ⟨hs, hind⟩, y, rfl, hy⟩ := h
  have hbot := center_eq_bot F hR hdim e
  have key : ∀ l : ↥L, ((modelEquiv hbot hR e (PspFrame.conjL ⟨s, hs⟩ l) : omegaProj hR) :
      ProjOrth R) = y * (modelEquiv hbot hR e l : ProjOrth R) * y⁻¹ := by
    intro l
    have h1 := hind l (PspFrame.conjL ⟨s, hs⟩ l) rfl
    rw [projSimAct_projOrthToProjSim] at h1
    exact h1
  have hphi := (phi_eq_conjOf_iff hL F hR (modelEquiv hbot hR e) s hs y).2 key
  have hyy : y * y = 1 := hasType_mul_self hy
  have hy1 : y ≠ 1 := hy.1
  refine ⟨hs, F.mem_A _, ?_, ?_, ?_⟩
  · rw [hphi, ← conjOf_mul, hyy, conjOf_one]
  · rw [hphi]
    intro h1
    apply hy1
    apply conjHom_injective hL F hR (modelEquiv hbot hR e) hdim hσ
    exact h1.trans (conjOf_one hL F hR (modelEquiv hbot hR e)).symm
  · rw [hphi, ← natCard_centralizer_eq hL F hR (modelEquiv hbot hR e) hdim hσ y]
    exact (hN W R hR hdim hσ y hyy hy1).1 hy

include hL in
theorem inducesTypeSome_of_invCent (r : ℕ) (α : ℤˣ) (N : ℕ)
    (hN : ∀ (W : Type) [AddCommGroup W] [Module (ZMod 3) W] [FiniteDimensional (ZMod 3) W]
      (R : QuadraticForm (ZMod 3) W) (hR : R.Nondegenerate), Module.finrank (ZMod 3) W = 5 →
      quadSign R = 1 → ∀ x : ProjOrth R, x * x = 1 → x ≠ 1 →
        (HasType x r α ↔ Nat.card (Subgroup.centralizer ({x} : Set (ProjOrth R))) = N))
    {s : G} (hs : s ∈ normalizer (L : Set G)) (h : InvCent N (F.φ ⟨s, hs⟩)) :
    InducesTypeSome L s 5 1 r α := by
  obtain ⟨W, i1, i2, i3, R, hR, hdim, hσ, ⟨e⟩⟩ := exists_model_five hL
  have hbot := center_eq_bot F hR hdim e
  obtain ⟨hA, hsq, hne, hcnt⟩ := h
  obtain ⟨y, hy⟩ := exists_conjOf_eq hL F hR (modelEquiv hbot hR e) hdim hσ hA
  have hyy : y * y = 1 := by
    apply conjHom_injective hL F hR (modelEquiv hbot hR e) hdim hσ
    show conjOf hL F hR (modelEquiv hbot hR e) (y * y) =
      conjOf hL F hR (modelEquiv hbot hR e) 1
    rw [conjOf_mul, conjOf_one, hy]
    exact hsq
  have hy1 : y ≠ 1 := by
    rintro rfl
    rw [conjOf_one] at hy
    exact hne hy.symm
  have hty : HasType y r α := (hN W R hR hdim hσ y hyy hy1).2 (by
    rw [natCard_centralizer_eq hL F hR (modelEquiv hbot hR e) hdim hσ y, hy]
    exact hcnt)
  refine ⟨W, i1, i2, i3, R, hR, e, projOrthToProjSim R y, hdim, hσ, ⟨hs, ?_⟩, y, rfl, hty⟩
  intro l l' hl'
  have h1 := (phi_eq_conjOf_iff hL F hR (modelEquiv hbot hR e) s hs y).1 hy.symm l
  rw [projSimAct_projOrthToProjSim]
  have h2 : l' = PspFrame.conjL ⟨s, hs⟩ l := Subtype.ext hl'
  rw [h2]
  exact h1

include hL in
theorem inducesTypeSome_iff (r : ℕ) (α : ℤˣ) (N : ℕ)
    (hN : ∀ (W : Type) [AddCommGroup W] [Module (ZMod 3) W] [FiniteDimensional (ZMod 3) W]
      (R : QuadraticForm (ZMod 3) W) (hR : R.Nondegenerate), Module.finrank (ZMod 3) W = 5 →
      quadSign R = 1 → ∀ x : ProjOrth R, x * x = 1 → x ≠ 1 →
        (HasType x r α ↔ Nat.card (Subgroup.centralizer ({x} : Set (ProjOrth R))) = N))
    (s : G) :
    InducesTypeSome L s 5 1 r α ↔
      ∃ hs : s ∈ normalizer (L : Set G), InvCent N (F.φ ⟨s, hs⟩) :=
  ⟨fun h => invCent_of_inducesTypeSome hL F r α N hN h,
    fun ⟨hs, h⟩ => inducesTypeSome_of_invCent hL F r α N hN hs h⟩

include hL in
theorem inducesTypeSome_four_plus_iff (s : G) :
    InducesTypeSome L s 5 1 4 1 ↔
      ∃ hs : s ∈ normalizer (L : Set G), InvCent 1152 (F.φ ⟨s, hs⟩) :=
  inducesTypeSome_iff hL F 4 1 1152 (by
    intro W _ _ _ R hR hdim hσ x hxx hx1
    exact hasType_four_plus_iff_natCard_five hR hdim hσ hxx hx1) s

include hL in
theorem inducesTypeSome_two_minus_iff (s : G) :
    InducesTypeSome L s 5 1 2 (-1) ↔
      ∃ hs : s ∈ normalizer (L : Set G), InvCent 192 (F.φ ⟨s, hs⟩) :=
  inducesTypeSome_iff hL F 2 (-1) 192 (by
    intro W _ _ _ R hR hdim hσ x hxx hx1
    exact hasType_two_minus_iff_natCard_five hR hdim hσ hxx hx1) s

include hL in
theorem inducesTypeSome_four_minus_iff (s : G) :
    InducesTypeSome L s 5 1 4 (-1) ↔
      ∃ hs : s ∈ normalizer (L : Set G), InvCent 1440 (F.φ ⟨s, hs⟩) :=
  inducesTypeSome_iff hL F 4 (-1) 1440 (by
    intro W _ _ _ R hR hdim hσ x hxx hx1
    exact hasType_four_minus_iff_natCard_five hR hdim hσ hxx hx1) s

include hL in
theorem inducesTypeSome_two_plus_iff (s : G) :
    InducesTypeSome L s 5 1 2 1 ↔
      ∃ hs : s ∈ normalizer (L : Set G), InvCent 96 (F.φ ⟨s, hs⟩) :=
  inducesTypeSome_iff hL F 2 1 96 (by
    intro W _ _ _ R hR hdim hσ x hxx hx1
    exact hasType_two_plus_iff_natCard_five hR hdim hσ hxx hx1) s

end TyDict

end CFSG.OddStandard.SmallF3.Omega
