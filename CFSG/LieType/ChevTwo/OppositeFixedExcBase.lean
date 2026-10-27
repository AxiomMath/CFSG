module

public import CFSG.LieType.ChevTwo.Defs

public section

namespace CFSG.LieType.ChevTwo

open CFSG.Open CFSG.LieType.BorelTits

private theorem autCentralizer_map_congr {K K' : Type} [Group K] [Group K'] (e : K ≃* K')
    (R : Subgroup (MulAut K)) :
    (autCentralizer R).map e.toMonoidHom =
      autCentralizer (R.map (MulAut.congr e).toMonoidHom) := by
  ext x'
  constructor
  · rintro ⟨x, hx, rfl⟩ _ ⟨α, hα, rfl⟩
    simp [MulAut.congr_apply, hx α hα]
  · intro hx'
    refine ⟨e.symm x', fun α hα => ?_, by simp⟩
    have h := hx' _ ⟨α, hα, rfl⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.congr_apply, MulEquiv.trans_apply] at h
    exact e.injective (by simpa using h)

@[expose] def OppositeFixedAt {K : Type} [Group K] (R : Subgroup (MulAut K)) (Q : Subgroup K) :
    Prop :=
  Q ≠ ⊥ → IsPGroup 2 Q → pCoreOf 2 (Subgroup.normalizer (Q : Set K)) = Q →
    Subgroup.normalizer (Q : Set K) ≠ ⊤ → (∀ α ∈ R, Q.map α.toMonoidHom = Q) →
      autCentralizer R ≤ Subgroup.normalizer (Q : Set K) → autCentralizer R ⊓ Q = ⊥

theorem oppositeFixedAt_of_map_congr {K K' : Type} [Group K] [Group K'] (e : K ≃* K')
    {R : Subgroup (MulAut K)} {Q : Subgroup K}
    (h : OppositeFixedAt (R.map (MulAut.congr e).toMonoidHom) (Q.map e.toMonoidHom)) :
    OppositeFixedAt R Q := by
  intro hQ hQ2 hcore hne hRQ hC
  have hN : Subgroup.normalizer ((Q.map e.toMonoidHom : Subgroup K') : Set K') =
      (Subgroup.normalizer (Q : Set K)).map e.toMonoidHom :=
    (Subgroup.map_equiv_normalizer_eq Q e).symm
  have hQ' : Q.map e.toMonoidHom ≠ ⊥ := fun h0 =>
    hQ ((Subgroup.map_eq_bot_iff_of_injective _ e.injective).1 h0)
  have hcore' : pCoreOf 2 (Subgroup.normalizer ((Q.map e.toMonoidHom : Subgroup K') : Set K')) =
      Q.map e.toMonoidHom := by
    rw [hN, pCoreOf_map_mulEquiv, hcore]
  have hne' : Subgroup.normalizer ((Q.map e.toMonoidHom : Subgroup K') : Set K') ≠ ⊤ := by
    rw [hN]
    intro htop
    apply hne
    have := congrArg (Subgroup.comap e.toMonoidHom) htop
    rwa [Subgroup.comap_map_eq_self_of_injective e.injective, Subgroup.comap_top] at this
  have hRQ' : ∀ α' ∈ R.map (MulAut.congr e).toMonoidHom,
      (Q.map e.toMonoidHom).map α'.toMonoidHom = Q.map e.toMonoidHom := by
    rintro _ ⟨α, hα, rfl⟩
    show (Q.map e.toMonoidHom).map (MulAut.congr e α).toMonoidHom = Q.map e.toMonoidHom
    have hcomp : ((MulAut.congr e α).toMonoidHom).comp e.toMonoidHom =
        e.toMonoidHom.comp α.toMonoidHom := by
      ext x; simp
    rw [Subgroup.map_map, hcomp, ← Subgroup.map_map, hRQ α hα]
  have hC' : autCentralizer (R.map (MulAut.congr e).toMonoidHom) ≤
      Subgroup.normalizer ((Q.map e.toMonoidHom : Subgroup K') : Set K') := by
    rw [← autCentralizer_map_congr, hN]
    exact Subgroup.map_mono hC
  have h0 := h hQ' (hQ2.map _) hcore' hne' hRQ' hC'
  rw [← autCentralizer_map_congr, ← Subgroup.map_inf _ _ e.toMonoidHom e.injective,
    Subgroup.map_eq_bot_iff_of_injective _ e.injective] at h0
  exact h0

theorem oppositeFixed_of_mulEquiv {K K' : Type} [Group K] [Group K'] (e : K ≃* K')
    (h : OppositeFixed K') : OppositeFixed K :=
  fun p hp hp2 R hR Q =>
    oppositeFixedAt_of_map_congr e (h p hp hp2 _ (hR.map _) (Q.map e.toMonoidHom))

theorem eq_of_le_of_inf_normalizer_le {G : Type} [Group G] [Finite G] {A Q : Subgroup G}
    (hA : IsPGroup 2 A) (hQA : Q ≤ A) (h : A ⊓ Subgroup.normalizer (Q : Set G) ≤ Q) :
    Q = A := by
  haveI : Group.IsNilpotent ↥A := hA.isNilpotent
  have hself : Subgroup.normalizer ((Q.subgroupOf A : Subgroup ↥A) : Set ↥A) = Q.subgroupOf A := by
    refine le_antisymm (fun x hx => ?_) Subgroup.le_normalizer
    rw [← Subgroup.subgroupOf_normalizer_eq hQA, Subgroup.mem_subgroupOf] at hx
    exact Subgroup.mem_subgroupOf.2 (h ⟨x.2, hx⟩)
  have htop := normalizerCondition_iff_only_full_group_self_normalizing.1
    Group.normalizerCondition_of_isNilpotent _ hself
  exact le_antisymm hQA (Subgroup.subgroupOf_eq_top.1 htop)

theorem std_position {K : Type} [Group K] [Finite K] {Q PJ QJ : Subgroup K} (g : K)
    (hcore : pCoreOf 2 (Subgroup.normalizer (Q : Set K)) = Q)
    (hQJ2 : IsPGroup 2 QJ) (hPJ : PJ ≤ Subgroup.normalizer (QJ : Set K))
    (hN : ∀ x ∈ Subgroup.normalizer (Q : Set K), g⁻¹ * x * g ∈ PJ)
    (hQ : ∀ q ∈ Q, g⁻¹ * q * g ∈ QJ) :
    Q.map (MulAut.conj g⁻¹).toMonoidHom = QJ ∧ Subgroup.normalizer (QJ : Set K) = PJ := by
  let c : K ≃* K := MulAut.conj g⁻¹
  have hc : ∀ x, c x = g⁻¹ * x * g := fun x => by simp [c]
  have hQ'le : Q.map c.toMonoidHom ≤ QJ := by
    rintro _ ⟨q, hq, rfl⟩
    simpa [hc] using hQ q hq
  have hNeq : Subgroup.normalizer ((Q.map c.toMonoidHom : Subgroup K) : Set K) =
      (Subgroup.normalizer (Q : Set K)).map c.toMonoidHom :=
    (Subgroup.map_equiv_normalizer_eq Q c).symm
  have hNle : Subgroup.normalizer ((Q.map c.toMonoidHom : Subgroup K) : Set K) ≤ PJ := by
    rw [hNeq]
    rintro _ ⟨x, hx, rfl⟩
    simpa [hc] using hN x hx
  have hcore' : pCoreOf 2 (Subgroup.normalizer ((Q.map c.toMonoidHom : Subgroup K) : Set K)) =
      Q.map c.toMonoidHom := by
    rw [hNeq, pCoreOf_map_mulEquiv, hcore]
  have hinf : QJ ⊓ Subgroup.normalizer ((Q.map c.toMonoidHom : Subgroup K) : Set K) ≤
      Q.map c.toMonoidHom := by
    refine le_trans ?_ hcore'.le
    refine le_pCoreOf 2 inf_le_right ?_ (hQJ2.to_le inf_le_left)
    rw [Subgroup.normal_subgroupOf_iff_le_normalizer inf_le_right]
    intro x hx
    rw [Subgroup.mem_normalizer_iff]
    intro y
    have hxJ := Subgroup.mem_normalizer_iff.1 (hPJ (hNle hx)) y
    have hxN := Subgroup.mem_normalizer_iff.1 (Subgroup.le_normalizer hx) y
    simp only [SetLike.mem_coe, Subgroup.mem_inf]
    rw [hxJ, hxN]
  have hEq := eq_of_le_of_inf_normalizer_le hQJ2 hQ'le hinf
  refine ⟨hEq, le_antisymm ?_ hPJ⟩
  rw [← hEq]
  exact hNle

end CFSG.LieType.ChevTwo
