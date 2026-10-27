module

public import CFSG.GF2Type.SmithTypeE.E8.IdNoA2
public import CFSG.GF2Type.SmithTypeE.E8.IdChev
public import CFSG.GF2Type.SmithTypeE.E8.ModW0
public import CFSG.GF2Type.SmithTypeE.E8.AbelQA
public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverChevalley
public import CFSG.SignalizerFunctorTheorem.CatalogBridge.FieldChevalleyOdd

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.GF2Type.SmithTypeE.E8

open Subgroup CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.Open CFSG.LargeExtraspecial
  CFSG.LargeExtraspecial.S14
open CFSG.LieType.Chevalley (parabolicRadical parabolicSubgroup)
open CFSG.LieType.Steinberg.Minuscule (e7Data)
open CFSG.HardMathSupport.Cooperstein.Coordinator.Survivors (e7Rep56 e7Y56 e7n6)
open CFSG.SeitzReduction (highRoot)
open CFSG.SeitzReduction.EPilot (pinnedElt)
open CFSG.LargeExtraspecial.S14.SMK (Inputs10 cMbar mem_normalizer_subgroupOf_iff)

theorem nonempty_mulEquiv_of_lieModel {H : Type} [Group H] (h : LieModel H .E7 0 2 1) :
    Nonempty (H ≃* ↥(adjointGroup .E7 (ZMod 2))) :=
  CFSG.ClassicalInvolution.Upgrade.untwistedChevalleyModel_unique
    (h.chevalleyExceptionalModel (by decide)).2
    (CFSG.SignalizerFunctorTheorem.CatalogBridge.untwistedChevalleyModel_adjointGroup
      (τ := .E7) (K := ZMod 2) (by simp [Nat.card_zmod]))

@[expose] noncomputable def QAg : Subgroup ↥(adjointGroup .E7 (ZMod 2)) :=
  QA.comap (adjointGroup .E7 (ZMod 2)).subtype

section Id

variable {G : Type} [Group G] [Finite G] [IsSimpleGroup G] {S : Setting G}

@[expose] noncomputable def Lp (S : Setting G) (h₀ : G) : Subgroup S.Mbar := (S.Lbar h₀).subgroupOf S.Mbar

section Ext

theorem exists_psi (hw : S.width = 28) (hU : LieModel S.Mbar .E7 0 2 1)
    {h₀ : G} (haQ : h₀ * S.z * h₀⁻¹ ∈ S.QG) (hne : h₀ * S.z * h₀⁻¹ ≠ S.z) :
    ∃ ψ : S.Mbar ≃* ↥(adjointGroup .E7 (ZMod 2)), QAg = (Lp S h₀).map ψ.toMonoidHom := by
  obtain ⟨ψ₀⟩ := nonempty_mulEquiv_of_lieModel hU
  have hmapinj : Function.Injective (adjointGroup .E7 (ZMod 2)).subtype := Subtype.val_injective
  have hEle : ((Lp S h₀).map ψ₀.toMonoidHom).map (adjointGroup .E7 (ZMod 2)).subtype ≤
      adjointGroup .E7 (ZMod 2) := by
    rintro _ ⟨x, -, rfl⟩
    exact x.2
  have hcomm : ∀ a ∈ ((Lp S h₀).map ψ₀.toMonoidHom).map (adjointGroup .E7 (ZMod 2)).subtype,
      ∀ b ∈ ((Lp S h₀).map ψ₀.toMonoidHom).map (adjointGroup .E7 (ZMod 2)).subtype,
        a * b = b * a := by
    rintro _ ⟨_, ⟨x, hx, rfl⟩, rfl⟩ _ ⟨_, ⟨y, hy, rfl⟩, rfl⟩
    have h := S.Lbar_comm haQ (mem_subgroupOf.mp hx) (mem_subgroupOf.mp hy)
    have h' : x * y = y * x := Subtype.ext h
    show ((ψ₀ x : ↥(adjointGroup .E7 (ZMod 2))) : ModGL .E7 (ZMod 2)) *
      ((ψ₀ y : ↥(adjointGroup .E7 (ZMod 2))) : ModGL .E7 (ZMod 2)) = _
    rw [← Subgroup.coe_mul, ← map_mul, h', map_mul, Subgroup.coe_mul]
    rfl
  have hp : IsPGroup 2 (((Lp S h₀).map ψ₀.toMonoidHom).map (adjointGroup .E7 (ZMod 2)).subtype) :=
    ((S.isPGroup_Lbar_subgroupOf haQ).map ψ₀.toMonoidHom).map _
  have hcard : 2 ^ 27 ≤ Nat.card (((Lp S h₀).map ψ₀.toMonoidHom).map
      (adjointGroup .E7 (ZMod 2)).subtype) := by
    rw [Subgroup.card_map_of_injective hmapinj, Subgroup.card_map_of_injective ψ₀.injective]
    have h1 : Nat.card (Lp S h₀) = Nat.card (S.Lbar h₀) :=
      Nat.card_congr (subgroupOfEquivOfLe (S.Lbar_le_Mbar h₀)).toEquiv
    have h2 := S.card_Lbar_ge haQ hne
    rw [hw] at h2
    omega
  obtain ⟨g, hg, hgE⟩ := abelian_conj_QA _ hEle hcomm hp hcard
  refine ⟨ψ₀.trans (MulAut.conj (⟨g, hg⟩ : ↥(adjointGroup .E7 (ZMod 2)))⁻¹), ?_⟩
  ext q
  constructor
  · intro hq
    have hq' : g * (q : ModGL .E7 (ZMod 2)) * g⁻¹ ∈
        ((Lp S h₀).map ψ₀.toMonoidHom).map (adjointGroup .E7 (ZMod 2)).subtype := by
      rw [hgE]
      exact ⟨q, hq, rfl⟩
    obtain ⟨_, ⟨x, hx, rfl⟩, hxq⟩ := hq'
    refine ⟨x, hx, ?_⟩
    apply Subtype.ext
    show (g⁻¹ * ((ψ₀ x : ↥(adjointGroup .E7 (ZMod 2))) : ModGL .E7 (ZMod 2)) * g) = q
    have hxq' : ((ψ₀ x : ↥(adjointGroup .E7 (ZMod 2))) : ModGL .E7 (ZMod 2)) = g * q * g⁻¹ := hxq
    rw [hxq']
    group
  · rintro ⟨x, hx, rfl⟩
    have hmem : ((ψ₀ x : ↥(adjointGroup .E7 (ZMod 2))) : ModGL .E7 (ZMod 2)) ∈
        ((Lp S h₀).map ψ₀.toMonoidHom).map (adjointGroup .E7 (ZMod 2)).subtype :=
      ⟨_, ⟨x, hx, rfl⟩, rfl⟩
    rw [hgE] at hmem
    obtain ⟨p, hp', hpx⟩ := hmem
    show ((((ψ₀.trans (MulAut.conj (⟨g, hg⟩ : ↥(adjointGroup .E7 (ZMod 2)))⁻¹)) x :
      ↥(adjointGroup .E7 (ZMod 2))) : ModGL .E7 (ZMod 2))) ∈ QA
    have hpx' : g * p * g⁻¹ = ((ψ₀ x : ↥(adjointGroup .E7 (ZMod 2))) : ModGL .E7 (ZMod 2)) := hpx
    have : ((((ψ₀.trans (MulAut.conj (⟨g, hg⟩ : ↥(adjointGroup .E7 (ZMod 2)))⁻¹)) x :
      ↥(adjointGroup .E7 (ZMod 2))) : ModGL .E7 (ZMod 2))) = p := by
      show g⁻¹ * ((ψ₀ x : ↥(adjointGroup .E7 (ZMod 2))) : ModGL .E7 (ZMod 2)) * g = p
      rw [← hpx']
      group
    rw [this]
    exact hp'

end Ext

theorem QA_le_adjointGroup : QA ≤ adjointGroup .E7 (ZMod 2) :=
  ((CFSG.LieType.Chevalley.parabolic_root_radical_Levi_factors .E7 (ZMod 2)
    {i | i ≠ e7n6}).1).trans (CFSG.LieType.Chevalley.parabolicSubgroup_le_adjointGroup _ _ _)

theorem mem_normalizer_QA_iff (s : ↥(adjointGroup .E7 (ZMod 2))) :
    (s : ModGL .E7 (ZMod 2)) ∈ Subgroup.normalizer (QA : Set (ModGL .E7 (ZMod 2))) ↔
      s ∈ Subgroup.normalizer (QAg : Set ↥(adjointGroup .E7 (ZMod 2))) := by
  rw [Subgroup.mem_normalizer_iff, Subgroup.mem_normalizer_iff]
  constructor
  · intro h q
    exact h (q : ModGL .E7 (ZMod 2))
  · intro h x
    by_cases hx : x ∈ adjointGroup .E7 (ZMod 2)
    · exact h ⟨x, hx⟩
    · constructor
      · intro hxQ
        exact absurd (QA_le_adjointGroup hxQ) hx
      · intro hxQ
        exfalso
        apply hx
        have h1 := QA_le_adjointGroup hxQ
        have h2 : (s : ModGL .E7 (ZMod 2))⁻¹ * ((s : ModGL .E7 (ZMod 2)) * x *
            (s : ModGL .E7 (ZMod 2))⁻¹) * (s : ModGL .E7 (ZMod 2)) ∈
            adjointGroup .E7 (ZMod 2) :=
          mul_mem (mul_mem (inv_mem s.2) h1) s.2
        simpa [mul_assoc] using h2

theorem mem_normalizer_map_iff {H K : Type*} [Group H] [Group K] (ψ : H ≃* K) (L : Subgroup H)
    (m : H) : ψ m ∈ Subgroup.normalizer ((L.map ψ.toMonoidHom : Subgroup K) : Set K) ↔
      m ∈ Subgroup.normalizer (L : Set H) := by
  rw [Subgroup.mem_normalizer_iff, Subgroup.mem_normalizer_iff]
  simp only [Subgroup.mem_map_equiv, map_mul, map_inv, MulEquiv.symm_apply_apply]
  constructor
  · intro h x
    simpa using h (ψ x)
  · intro h k
    exact h (ψ.symm k)

theorem mem_cMbar_iff_psi (I : Inputs10) (hw : S.width = 28) (hU : LieModel S.Mbar .E7 0 2 1)
    {h₀ : G} (haQ : h₀ * S.z * h₀⁻¹ ∈ S.QG) (hne : h₀ * S.z * h₀⁻¹ ≠ S.z)
    (ψ : S.Mbar ≃* ↥(adjointGroup .E7 (ZMod 2))) (hψ : QAg = (Lp S h₀).map ψ.toMonoidHom)
    (m : S.Mbar) :
    ((m : S.O) ∈ cMbar S h₀) ↔
      (ψ m : ModGL .E7 (ZMod 2)) ∈ parabolicSubgroup .E7 (ZMod 2) {i | i ≠ e7n6} := by
  have hSF10 := CFSG.LieType.Chevalley.adjointGroup_inf_normalizer_parabolicRadical
    (τ := .E7) (K := ZMod 2) {i | i ≠ e7n6}
  rw [← hSF10, Subgroup.mem_inf, cMbar_eq_normalizer I hw hU haQ hne, Subgroup.mem_inf]
  have h1 : ((m : S.O) ∈ Subgroup.normalizer (S.Lbar h₀ : Set S.O)) ↔
      m ∈ Subgroup.normalizer ((Lp S h₀ : Subgroup S.Mbar) : Set S.Mbar) :=
    (mem_normalizer_subgroupOf_iff (S.Lbar_le_Mbar h₀) m).symm
  have h2 : m ∈ Subgroup.normalizer ((Lp S h₀ : Subgroup S.Mbar) : Set S.Mbar) ↔
      ψ m ∈ Subgroup.normalizer (QAg : Set ↥(adjointGroup .E7 (ZMod 2))) := by
    rw [hψ]
    exact (mem_normalizer_map_iff ψ (Lp S h₀) m).symm
  rw [h1, h2, ← mem_normalizer_QA_iff]
  exact ⟨fun h => ⟨(ψ m).2, h.2⟩, fun h => ⟨m.2, h.2⟩⟩

@[expose] noncomputable def rhoM (S : Setting G) : S.M →* S.Mbar :=
  S.ρ.codRestrict S.Mbar fun m => ⟨m, rfl⟩

theorem coe_rhoM (m : S.M) : (rhoM S m : S.O) = S.ρ m := rfl

theorem exists_rhoM_eq (m : S.Mbar) : ∃ x : S.M, rhoM S x = m := by
  obtain ⟨x, hx⟩ := MonoidHom.mem_range.mp m.2
  exact ⟨x, Subtype.ext hx⟩

@[expose] noncomputable def repQ (S : Setting G) (ψ : S.Mbar ≃* ↥(adjointGroup .E7 (ZMod 2))) :
    Representation (ZMod 2) ↥(adjointGroup .E7 (ZMod 2)) S.Qt :=
  LinearEquiv.automorphismGroup.toLinearMapMonoidHom.comp
    ((S.O.subtype.comp S.Mbar.subtype).comp ψ.symm.toMonoidHom)

theorem repQ_apply (ψ : S.Mbar ≃* ↥(adjointGroup .E7 (ZMod 2))) (x : S.Mbar) (v : S.Qt) :
    repQ S ψ (ψ x) v = ((x : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) v := by
  simp [repQ]

theorem isSimpleRep_repQ (ψ : S.Mbar ≃* ↥(adjointGroup .E7 (ZMod 2))) (hirr : ¬ S.IsReducible)
    {y : S.Qt} (hy : y ≠ 0) : CFSG.Quasithin.SmithCurtis.IsSimpleRep (repQ S ψ) := by
  refine ⟨⟨y, 0, hy⟩, fun W hW => ?_⟩
  by_contra hcon
  push Not at hcon
  refine hirr ⟨W, hcon.1, hcon.2, fun m v hv => ?_⟩
  have := hW (ψ (rhoM S m)) v hv
  rw [repQ_apply] at this
  exact this

open CFSG.HardMathSupport.Cooperstein.Coordinator.Survivors (e7_iso_56) in
theorem exists_phi (I : Inputs10) (hw : S.width = 28) (hU : LieModel S.Mbar .E7 0 2 1)
    {h₀ : G} (haQ : h₀ * S.z * h₀⁻¹ ∈ S.QG) (hne : h₀ * S.z * h₀⁻¹ ≠ S.z)
    (ψ : S.Mbar ≃* ↥(adjointGroup .E7 (ZMod 2))) (hψ : QAg = (Lp S h₀).map ψ.toMonoidHom) :
    ∃ φ : S.Qt ≃ₗ[ZMod 2] (Fin e7Data.d →₀ ZMod 2), SmithE8Equiv S φ ψ ∧
      φ (S.cl (h₀ * S.z * h₀⁻¹)) = e7Y56 := by
  have hy : S.cl (h₀ * S.z * h₀⁻¹) ≠ 0 := S.cl_conj_z_ne_zero haQ hne
  have hirr := irreducible I.hDW hw hU haQ hne
  have hsimple := isSimpleRep_repQ ψ hirr hy
  have hstab : ∀ g : ↥(adjointGroup .E7 (ZMod 2)),
      repQ S ψ g (S.cl (h₀ * S.z * h₀⁻¹)) = S.cl (h₀ * S.z * h₀⁻¹) ↔
        (g : ModGL .E7 (ZMod 2)) ∈ parabolicSubgroup .E7 (ZMod 2) {i | i ≠ e7n6} := by
    intro g
    have h1 := repQ_apply ψ (ψ.symm g) (S.cl (h₀ * S.z * h₀⁻¹))
    rw [MulEquiv.apply_symm_apply] at h1
    rw [h1]
    have h2 := mem_cMbar_iff_psi I hw hU haQ hne ψ hψ (ψ.symm g)
    rw [MulEquiv.apply_symm_apply] at h2
    rw [← h2]
    exact ⟨fun h => SMK.mem_cMbar.2 ⟨(ψ.symm g).2, h⟩, fun h => (SMK.mem_cMbar.1 h).2⟩
  have htype := isChevType_of_stab (repQ S ψ) _ hy hstab
  obtain ⟨β, hβ⟩ := e7_iso_56 hsimple htype
  have hφ : ∀ (g : ↥(adjointGroup .E7 (ZMod 2))) (v : S.Qt),
      β.symm (repQ S ψ g v) = e7Rep56 (ZMod 2) g (β.symm v) := fun g v => by
    apply β.injective
    rw [LinearEquiv.apply_symm_apply, hβ, LinearEquiv.apply_symm_apply]
  refine ⟨β.symm, fun m v => ?_, ?_⟩
  · rw [← hφ, repQ_apply]
  · rcases eq_zero_or_eq_e7Y56 (β.symm (S.cl (h₀ * S.z * h₀⁻¹))) (fun u hu => by
        rw [← hφ, (hstab u).2 (chv_borel_le_parabolic _ (chv_posUnipotent_le_borel hu))]) with h | h
    · exact absurd (β.symm.map_eq_zero_iff.mp h) hy
    · exact h

theorem e7Y56_mem_W0 : (e7Y56 : Fin e7Data.d →₀ ZMod 2) ∈ W0 := by
  rw [mem_W0]
  intro b hb
  unfold e7Y56
  rw [Finsupp.single_apply, if_neg]
  intro h
  rw [← h] at hb
  revert hb
  decide

structure IdBase (S : Setting G) (h₀ : G) (ψ : S.Mbar ≃* ↥(adjointGroup .E7 (ZMod 2)))
    (φ : S.Qt ≃ₗ[ZMod 2] (Fin e7Data.d →₀ ZMod 2)) : Prop where
  haQ : h₀ * S.z * h₀⁻¹ ∈ S.QG
  hne : h₀ * S.z * h₀⁻¹ ≠ S.z
  hψ : QAg = (Lp S h₀).map ψ.toMonoidHom
  hE : SmithE8Equiv S φ ψ
  hφ : φ (S.cl (h₀ * S.z * h₀⁻¹)) = e7Y56

variable {h₀ : G} {ψ : S.Mbar ≃* ↥(adjointGroup .E7 (ZMod 2))}
  {φ : S.Qt ≃ₗ[ZMod 2] (Fin e7Data.d →₀ ZMod 2)}

theorem IdBase.conj_cl (B : IdBase S h₀ ψ φ) (m : S.M) {y : G} (hy : y ∈ S.QG) :
    φ (S.cl ((m : G) * y * (m : G)⁻¹)) =
      e7Rep56 (ZMod 2) (ψ (rhoM S m)) (φ (S.cl y)) := by
  rw [← B.hE (rhoM S m) (S.cl y), coe_rhoM, S.ρ_cl m hy]

theorem IdBase.conj_a₀ (B : IdBase S h₀ ψ φ) (m : S.M) :
    φ (S.cl ((m : G) * (h₀ * S.z * h₀⁻¹) * (m : G)⁻¹)) =
      e7Rep56 (ZMod 2) (ψ (rhoM S m)) e7Y56 := by
  rw [B.conj_cl m B.haQ, B.hφ]

theorem IdBase.phi_cl_mem_W0 (B : IdBase S h₀ ψ φ) {x : G} (hx : x ∈ S.QG ⊓ S.Qa h₀) :
    φ (S.cl x) ∈ W0 := by
  by_cases hx0 : S.cl x = 0
  · rw [hx0, map_zero]
    exact zero_mem _
  by_cases hxa : S.cl x = S.cl (h₀ * S.z * h₀⁻¹)
  · rw [hxa, B.hφ]
    exact e7Y56_mem_W0
  rw [mem_W0_iff']
  intro q hq
  have hq' : q ∈ (Lp S h₀).map ψ.toMonoidHom := B.hψ ▸ hq
  obtain ⟨ℓ, hℓ, rfl⟩ := hq'
  obtain ⟨y, hyL, hyℓ⟩ := S.mem_Lbar_iff.mp (mem_subgroupOf.mp hℓ)
  have hconj := (S.conj_L0_of_mem_QG_inf_Qa B.haQ B.hne hx ⟨hx0, hxa⟩).1 y hyL
  have hyx : (((ψ ℓ : ↥(adjointGroup .E7 (ZMod 2)))) : _) = _ := rfl
  have e : e7Rep56 (ZMod 2) (ψ.toMonoidHom ℓ) (φ (S.cl x)) =
      φ (S.cl ((y : G) * x * (y : G)⁻¹)) := by
    show e7Rep56 (ZMod 2) (ψ ℓ) (φ (S.cl x)) = _
    rw [← B.hE ℓ (S.cl x), ← hyℓ]
    show φ ((S.ρ y : S.Qt ≃ₗ[ZMod 2] S.Qt) (S.cl x)) = _
    rw [S.ρ_cl y hx.1]
  rw [e]
  rcases hconj with h | h
  · rw [h, sub_self]
    exact zero_mem _
  · rw [h, S.cl_mul B.haQ hx.1, map_add, B.hφ, add_sub_cancel_right]
    exact Submodule.mem_span_singleton_self _

theorem exists_M_conj (I : Inputs10) (hw : S.width = 28) (hU : LieModel S.Mbar .E7 0 2 1)
    (B : IdBase S h₀ ψ φ) {c : G} (hc : IsConj S.z c) (hcQ : c ∈ S.QG) (hcz : c ≠ S.z) :
    ∃ m : S.M, (m : G) * (h₀ * S.z * h₀⁻¹) * (m : G)⁻¹ = c := by
  obtain ⟨k, rfl⟩ := isConj_iff.mp hc
  have hno : ∀ g : G, g * S.z * g⁻¹ ∈ S.QG → g * S.z * g⁻¹ ≠ S.z → ¬ S.HasTypeAInL g :=
    fun g h1 h2 => noA2_of_insp5 I hw hU h1 h2
  have e : (k * h₀⁻¹) * (h₀ * S.z * h₀⁻¹) * (k * h₀⁻¹)⁻¹ = k * S.z * k⁻¹ := by group
  have hx1 : h₀ * S.z * h₀⁻¹ ≠ 1 := fun h => S.z_ne_one (by
    calc S.z = h₀⁻¹ * (h₀ * S.z * h₀⁻¹) * h₀ := by group
      _ = h₀⁻¹ * 1 * h₀ := by rw [h]
      _ = 1 := by group)
  obtain ⟨m, hm, hmx⟩ := S.lemma_3_13 (by omega) hno B.haQ hx1 B.hne (by rw [e]; exact hcQ)
    (by rw [e]; exact hcz)
  exact ⟨⟨m, hm⟩, by rw [e] at hmx; exact hmx⟩

section Ext

theorem card_QA : Nat.card QA = 2 ^ 27 := by
  show Nat.card (parabolicRadical .E7 (ZMod 2) {i | i ≠ e7n6}) = _
  rw [parabolicRadical_eq_Ge]
  exact card_Ge_15625

theorem IdBase.card_Lbar (B : IdBase S h₀ ψ φ) : Nat.card (S.Lbar h₀) = 2 ^ 27 := by
  have h1 : Nat.card (Lp S h₀) = Nat.card (S.Lbar h₀) :=
    Nat.card_congr (subgroupOfEquivOfLe (S.Lbar_le_Mbar h₀)).toEquiv
  have h2 : Nat.card ((Lp S h₀).map ψ.toMonoidHom) = Nat.card (Lp S h₀) :=
    Subgroup.card_map_of_injective ψ.injective
  have h3 : Nat.card QAg = Nat.card QA :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe QA_le_adjointGroup).toEquiv
  rw [← h1, ← h2, ← B.hψ, h3, card_QA]

theorem IdBase.finrank_clSub (B : IdBase S h₀ ψ φ) (hw : S.width = 28) :
    Module.finrank (ZMod 2) (S.clSub (S.QG ⊓ S.Qa h₀)) = 28 := by
  have h1 := S.card_Lbar_mul h₀
  rw [S.card_L0 B.haQ B.hne, B.card_Lbar, hw] at h1
  have h2 := S.card_QG_inf_Qa_eq B.haQ B.hne
  have h3 : Nat.card (S.QG ⊓ S.Qa h₀ : Subgroup G) = 2 ^ 29 := by
    have : 2 ^ 27 * Nat.card (S.QG ⊓ S.Qa h₀ : Subgroup G) = 2 ^ 27 * 2 ^ 29 := by
      rw [h1, ← pow_add]
    exact Nat.eq_of_mul_eq_mul_left (by positivity) this
  rw [h3] at h2
  have h4 : 2 ^ 28 = 2 ^ Module.finrank (ZMod 2) (S.clSub (S.QG ⊓ S.Qa h₀)) := by
    have : 2 * 2 ^ 28 = 2 * 2 ^ Module.finrank (ZMod 2) (S.clSub (S.QG ⊓ S.Qa h₀)) := by
      rw [← h2]
      norm_num
    exact Nat.eq_of_mul_eq_mul_left (by norm_num) this
  exact (Nat.pow_right_injective (le_refl 2) h4).symm

theorem IdBase.mem_Qa_iff_W0 (B : IdBase S h₀ ψ φ) (hw : S.width = 28) {b : G} (hb : b ∈ S.QG) :
    b ∈ S.Qa h₀ ↔ φ (S.cl b) ∈ W0 := by
  constructor
  · intro hba
    exact B.phi_cl_mem_W0 ⟨hb, hba⟩
  · intro hW
    have hle : (S.clSub (S.QG ⊓ S.Qa h₀)).map (φ : S.Qt →ₗ[ZMod 2] (Fin e7Data.d →₀ ZMod 2)) ≤
        W0 := by
      rintro _ ⟨v, hv, rfl⟩
      obtain ⟨x, hx, hxQ, rfl⟩ := S.mem_clSub_iff.mp hv
      exact B.phi_cl_mem_W0 hx
    have heq : (S.clSub (S.QG ⊓ S.Qa h₀)).map
        (φ : S.Qt →ₗ[ZMod 2] (Fin e7Data.d →₀ ZMod 2)) = W0 := by
      haveI : Module.Finite (ZMod 2) (Fin e7Data.d →₀ ZMod 2) := inferInstance
      refine Submodule.eq_of_le_of_finrank_le hle ?_
      rw [LinearEquiv.finrank_map_eq, B.finrank_clSub hw, finrank_W0]
    rw [← heq, Submodule.mem_map_equiv] at hW
    have hz : S.z ∈ S.QG ⊓ S.Qa h₀ := ⟨S.z_mem_QG, S.z_mem_Qa B.haQ B.hne⟩
    simp only [LinearEquiv.symm_apply_apply] at hW
    exact ((S.clPre_clSub inf_le_left hz).le ⟨hb, hW⟩).2

theorem IdBase.clauses123 (I : Inputs10) (hw : S.width = 28) (hU : LieModel S.Mbar .E7 0 2 1)
    (B : IdBase S h₀ ψ φ) : SmithE8Clauses123 S φ ψ := by
  refine ⟨B.hE, ?_, ?_, ?_⟩
  · intro c hc hcQ hcz
    obtain ⟨m, hm⟩ := exists_M_conj I hw hU B hc hcQ hcz
    rw [← hm, B.conj_a₀ m]
    exact ⟨_, rfl⟩
  · rintro _ ⟨g, rfl⟩
    obtain ⟨m, hm⟩ := exists_rhoM_eq (ψ.symm g)
    refine ⟨(m : G) * (h₀ * S.z * h₀⁻¹) * (m : G)⁻¹, ?_, S.conj_mem_QG m.2 B.haQ, ?_⟩
    · rw [isConj_iff]
      exact ⟨(m : G) * h₀, by group⟩
    · rw [B.conj_a₀ m, hm, MulEquiv.apply_symm_apply]
  · intro h b haQ' hne' hb hbQ hbz
    obtain ⟨m, hm⟩ := exists_M_conj I hw hU B (isConj_iff.mpr ⟨h, rfl⟩) haQ' hne'
    have hQa : S.Qa h = S.Qa ((m : G) * h₀) := S.Qa_eq_of_conj_eq (by rw [← hm]; group)
    have hφa : φ (S.cl (h * S.z * h⁻¹)) = e7Rep56 (ZMod 2) (ψ (rhoM S m)) e7Y56 := by
      rw [← hm, B.conj_a₀ m]
    rw [hφa, mem_collSpace_iff, hQa, S.mem_Qa_mul_iff]
    have hb' : (m : G)⁻¹ * b * (m : G) ∈ S.QG := by
      have := S.conj_mem_QG (S.M.inv_mem m.2) hbQ
      simpa using this
    have h1 : e7Rep56 (ZMod 2) (ψ (rhoM S m))⁻¹ (φ (S.cl b)) =
        φ (S.cl ((m : G)⁻¹ * b * (m : G))) := by
      have := B.conj_cl m⁻¹ hbQ
      simp only [Subgroup.coe_inv, inv_inv, map_inv] at this
      exact this.symm
    rw [h1]
    exact B.mem_Qa_iff_W0 hw hb'

theorem clauses123 (I : Inputs10) (hAS : AschbacherSmithWideInput) (S : Setting G)
    (hw : S.width = 28) (hU : LieModel S.Mbar .E7 0 2 1) :
    ∃ (φ : S.Qt ≃ₗ[ZMod 2] (Fin e7Data.d →₀ ZMod 2))
      (ψ : S.Mbar ≃* ↥(adjointGroup .E7 (ZMod 2))), SmithE8Clauses123 S φ ψ := by
  obtain ⟨h₀, haQ, hne⟩ := exists_conj_mem_QG hAS hw hU
  obtain ⟨ψ, hψ⟩ := exists_psi hw hU haQ hne
  obtain ⟨φ, hE, hφ⟩ := exists_phi I hw hU haQ hne ψ hψ
  exact ⟨φ, ψ, IdBase.clauses123 I hw hU ⟨haQ, hne, hψ, hE, hφ⟩⟩
end Ext

end Id

end CFSG.GF2Type.SmithTypeE.E8
