module

public import CFSG.LocalAnalysis.SeitzReduction.F4PilotPositionBasic

public section

namespace CFSG.SeitzReduction.F4Pilot

open Subgroup CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley

section Conj

variable {G : Type*} [Group G]

theorem centralizer_map_conj (H : Subgroup G) (m : G) :
    centralizer ((H.map (MulAut.conj m).toMonoidHom : Subgroup G) : Set G) =
      (centralizer (H : Set G)).map (MulAut.conj m).toMonoidHom := by
  ext g
  constructor
  · intro hg
    refine ⟨m⁻¹ * g * m, ?_, by simp [MulAut.conj_apply, mul_assoc]⟩
    rw [SetLike.mem_coe, mem_centralizer_iff]
    intro h hh
    have := mem_centralizer_iff.1 hg (m * h * m⁻¹) ⟨h, hh, by simp [MulAut.conj_apply]⟩
    calc h * (m⁻¹ * g * m) = m⁻¹ * ((m * h * m⁻¹) * g) * m := by group
      _ = m⁻¹ * (g * (m * h * m⁻¹)) * m := by rw [this]
      _ = m⁻¹ * g * m * h := by group
  · rintro ⟨c, hc, rfl⟩
    rw [mem_centralizer_iff]
    rintro _ ⟨h, hh, rfl⟩
    have := mem_centralizer_iff.1 hc h hh
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    calc m * h * m⁻¹ * (m * c * m⁻¹) = m * (h * c) * m⁻¹ := by group
      _ = m * (c * h) * m⁻¹ := by rw [this]
      _ = m * c * m⁻¹ * (m * h * m⁻¹) := by group

end Conj

section Core

variable {K : Type} [Field K]
variable {G : Type*} [Group G] [Finite G]

theorem exists_le_centralizer_mulEquiv_of_two_levi (hF3 : FactF3 K) (hF3p : FactF3Perfect K)
    (hLS : FactLeviSimple K) (hF5 : FactF5 K) (hF6 : FactF6 K)
    {φ φ' : adjointGroup .F4 K →* G} (hφ : Function.Injective φ) (hφ' : Function.Injective φ')
    {κ κ' : TwoCentral}
    (hΛ : (centralizer ({yRep K κ} : Set (adjointGroup .F4 K))).map φ =
      (centralizer ({yRep K κ'} : Set (adjointGroup .F4 K))).map φ')
    {X : Subgroup G} (hXodd : Odd (Nat.card X)) (hXJ : X ≤ (rootSL2 K rootR).map φ) :
    ∃ P : Subgroup G, P ≤ φ'.range ⊓ centralizer (X : Set G) ∧ Nonempty (P ≃* C3Levi K) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨Q, hQp, hQM, hQMinf, hMQ⟩ := hF3 κ
  obtain ⟨Q', hQ'p, hQ'M, hQ'Minf, hM'Q'⟩ := hF3 κ'
  have hΛ₁ : Q.map φ ⊔ (levi K κ).map φ =
      (centralizer ({yRep K κ} : Set (adjointGroup .F4 K))).map φ := by
    rw [← Subgroup.map_sup, hQM]
  have hΛ₂ : Q'.map φ' ⊔ (levi K κ').map φ' =
      (centralizer ({yRep K κ} : Set (adjointGroup .F4 K))).map φ := by
    rw [hΛ, ← Subgroup.map_sup, hQ'M]
  have hinf₁ : Q.map φ ⊓ (levi K κ).map φ = ⊥ := by
    rw [← map_inf_eq _ _ _ hφ, hQMinf, Subgroup.map_bot]
  have hinf₂ : Q'.map φ' ⊓ (levi K κ').map φ' = ⊥ := by
    rw [← map_inf_eq _ _ _ hφ', hQ'Minf, Subgroup.map_bot]
  have hN₁ : (levi K κ).map φ ≤ normalizer ((Q.map φ : Subgroup G) : Set G) :=
    (map_mono hMQ).trans (le_normalizer_map φ)
  have hN₂ : (levi K κ').map φ' ≤ normalizer ((Q'.map φ' : Subgroup G) : Set G) :=
    (map_mono hM'Q').trans (le_normalizer_map φ')
  have hQ₁p : IsPGroup 2 (Q.map φ) := hQp.map φ
  have hQ₂p : IsPGroup 2 (Q'.map φ') := hQ'p.map φ'
  set eM₁ : levi K κ ≃* (levi K κ).map φ := (levi K κ).equivMapOfInjective φ hφ with heM₁
  set eM₂ : levi K κ' ≃* (levi K κ').map φ' := (levi K κ').equivMapOfInjective φ' hφ'
    with heM₂
  have hM₁s : IsSimpleGroup ((levi K κ).map φ) := by
    have := hLS κ
    exact eM₁.symm.isSimpleGroup
  have hM₂s : IsSimpleGroup ((levi K κ').map φ') := by
    have := hLS κ'
    exact eM₂.symm.isSimpleGroup
  have hperf : ⁅(centralizer ({yRep K κ} : Set (adjointGroup .F4 K))).map φ,
      (centralizer ({yRep K κ} : Set (adjointGroup .F4 K))).map φ⁆ =
      (centralizer ({yRep K κ} : Set (adjointGroup .F4 K))).map φ := by
    rw [← map_commutator, hF3p κ]
  have hle₂₁ : Q'.map φ' ≤ Q.map φ := by
    refine le_of_sup_eq_of_isSimpleGroup hQ₁p hQ₂p hM₁s (hΛ₁ ▸ hperf) hN₁ ?_ ?_
    · rw [hΛ₁, ← hΛ₂]
      exact le_sup_left
    · rw [hΛ₁, ← hΛ₂]
      exact sup_le le_normalizer hN₂
  have hle₁₂ : Q.map φ ≤ Q'.map φ' := by
    refine le_of_sup_eq_of_isSimpleGroup hQ₂p hQ₁p hM₂s (hΛ₂ ▸ hperf) hN₂ ?_ ?_
    · rw [hΛ₂, ← hΛ₁]
      exact le_sup_left
    · rw [hΛ₂, ← hΛ₁]
      exact sup_le le_normalizer hN₁
  have hQeq : Q'.map φ' = Q.map φ := le_antisymm hle₂₁ hle₁₂
  rw [hQeq] at hinf₂ hN₂ hΛ₂
  obtain ⟨ι, hι⟩ := exists_mulEquiv_of_sup_eq (hΛ₁.trans hΛ₂.symm) hinf₁ hinf₂ hN₁ hN₂
  set ιC : levi K κ ≃* levi K κ' := eM₁.trans (ι.trans eM₂.symm) with hιC
  have hιC : ∀ a : levi K κ, ((ι (eM₁ a) : (levi K κ').map φ') : G) = φ' (ιC a) := by
    intro a
    have h1 : ιC a = eM₂.symm (ι (eM₁ a)) := rfl
    rw [h1]
    conv_lhs => rw [← eM₂.apply_symm_apply (ι (eM₁ a))]
    rfl
  obtain ⟨γ, hγ, m, hm, hJ'⟩ := hF5 κ κ' ιC (rootSL2 K rootR)
    (rootSL2_mem_leviRootSL2s (rootR_mem_phi0 κ))
  set J' := (rootSL2 K γ).map (MulAut.conj m).toMonoidHom with hJ'def
  obtain ⟨eF6⟩ := hF6 γ hγ.1
  have hXM₁ : X ≤ (levi K κ).map φ := hXJ.trans (map_mono (rootSL2_rootR_le_levi κ))
  set X₂ : Subgroup G := ((X.subgroupOf ((levi K κ).map φ)).map ι.toMonoidHom).map
    ((levi K κ').map φ').subtype with hX₂def
  have hX₂M₂ : X₂ ≤ (levi K κ').map φ' := by
    rw [hX₂def]
    exact map_subtype_le _
  have hX₂J : X₂ ≤ J'.map φ' := by
    rintro _ ⟨_, ⟨x, hx, rfl⟩, rfl⟩
    have hxX : (x : G) ∈ X := mem_subgroupOf.1 hx
    obtain ⟨j, hj, hjx⟩ := hXJ hxX
    have hjM : j ∈ levi K κ := rootSL2_rootR_le_levi κ hj
    have hx' : x = eM₁ ⟨j, hjM⟩ := Subtype.ext (by rw [← hjx]; rfl)
    have hmem : (ιC ⟨j, hjM⟩ : adjointGroup .F4 K) ∈ J' := by
      rw [← hJ']
      exact ⟨ιC ⟨j, hjM⟩, ⟨⟨j, hjM⟩, mem_subgroupOf.2 hj, rfl⟩, rfl⟩
    refine ⟨(ιC ⟨j, hjM⟩ : adjointGroup .F4 K), hmem, ?_⟩
    simp only [MulEquiv.coe_toMonoidHom, coe_subtype]
    rw [hx', hιC]
  have hQX : Q.map φ ⊓ X = ⊥ :=
    le_bot_iff.1 (hinf₁ ▸ inf_le_inf_left _ hXM₁)
  have hQX₂ : Q.map φ ⊓ X₂ = ⊥ :=
    le_bot_iff.1 (hinf₂ ▸ inf_le_inf_left _ hX₂M₂)
  have hsup : Q.map φ ⊔ X = Q.map φ ⊔ X₂ := by
    apply le_antisymm
    · refine sup_le le_sup_left fun x hx => ?_
      have h := hι ⟨x, hXM₁ hx⟩
      have hιx : ((ι ⟨x, hXM₁ hx⟩ : (levi K κ').map φ') : G) ∈ X₂ :=
        ⟨ι ⟨x, hXM₁ hx⟩, ⟨⟨x, hXM₁ hx⟩, mem_subgroupOf.2 hx, rfl⟩, rfl⟩
      have : x = ((ι ⟨x, hXM₁ hx⟩ : (levi K κ').map φ') : G) *
          (((ι ⟨x, hXM₁ hx⟩ : (levi K κ').map φ') : G)⁻¹ * x) := by group
      rw [this]
      exact mul_mem (mem_sup_right hιx) (mem_sup_left h)
    · refine sup_le le_sup_left ?_
      rintro _ ⟨_, ⟨x, hx, rfl⟩, rfl⟩
      have h := hι x
      have hxX : (x : G) ∈ X := mem_subgroupOf.1 hx
      have : ((ι x : (levi K κ').map φ') : G) =
          (x : G) * ((((ι x : (levi K κ').map φ') : G))⁻¹ * x)⁻¹ := by group
      simp only [MulEquiv.coe_toMonoidHom, coe_subtype]
      rw [this]
      exact mul_mem (mem_sup_right hxX) (mem_sup_left (inv_mem h))
  have hX2 : ¬ 2 ∣ Nat.card X := fun h => (Nat.not_even_iff_odd.2 hXodd) (even_iff_two_dvd.2 h)
  obtain ⟨n, hn, hX₂eq⟩ := exists_mem_conj_eq_of_complement hQ₁p hX2 (hXM₁.trans hN₁)
    (hX₂M₂.trans hN₂) hQX hQX₂ hsup
  refine ⟨((centralizer (J' : Set (adjointGroup .F4 K))).map φ').map (MulAut.conj n).toMonoidHom,
    le_inf ?_ ?_, ?_⟩
  · rintro _ ⟨_, ⟨c, -, rfl⟩, rfl⟩
    have hn' : n ∈ φ'.range := by
      rw [← hQeq] at hn
      obtain ⟨n', -, rfl⟩ := hn
      exact ⟨n', rfl⟩
    obtain ⟨n', rfl⟩ := hn'
    exact ⟨n' * c * n'⁻¹, by simp [MulAut.conj_apply]⟩
  · rintro _ ⟨_, ⟨c, hc, rfl⟩, rfl⟩
    rw [mem_centralizer_iff]
    intro x hx
    have hx₂ : n⁻¹ * x * n ∈ X₂ := by
      rw [hX₂eq]
      exact ⟨x, hx, by simp⟩
    obtain ⟨j, hj, hjx⟩ := hX₂J hx₂
    have hcj := mem_centralizer_iff.1 hc j hj
    have hφc : φ' c * (n⁻¹ * x * n) = (n⁻¹ * x * n) * φ' c := by
      rw [← hjx, ← map_mul, ← map_mul, hcj]
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    calc x * (n * φ' c * n⁻¹) = n * ((n⁻¹ * x * n) * φ' c) * n⁻¹ := by group
      _ = n * (φ' c * (n⁻¹ * x * n)) * n⁻¹ := by rw [hφc]
      _ = n * φ' c * n⁻¹ * x := by group
  · have e1 : ((centralizer (J' : Set (adjointGroup .F4 K))).map φ').map
        (MulAut.conj n).toMonoidHom ≃* (centralizer (J' : Set (adjointGroup .F4 K))).map φ' :=
      (((centralizer (J' : Set (adjointGroup .F4 K))).map φ').equivMapOfInjective _
        (MulAut.conj n).injective).symm
    have e2 : (centralizer (J' : Set (adjointGroup .F4 K))).map φ' ≃*
        centralizer (J' : Set (adjointGroup .F4 K)) :=
      ((centralizer (J' : Set (adjointGroup .F4 K))).equivMapOfInjective _ hφ').symm
    have hcJ : centralizer (J' : Set (adjointGroup .F4 K)) =
        (centralizer (rootSL2 K γ : Set (adjointGroup .F4 K))).map (MulAut.conj m).toMonoidHom := by
      rw [centralizer_map_conj]
    have e3 : centralizer (J' : Set (adjointGroup .F4 K)) ≃*
        centralizer (rootSL2 K γ : Set (adjointGroup .F4 K)) := by
      rw [hcJ]
      exact ((centralizer (rootSL2 K γ : Set (adjointGroup .F4 K))).equivMapOfInjective _
        (MulAut.conj m).injective).symm
    exact ⟨e1.trans (e2.trans (e3.trans eF6))⟩

end Core

end CFSG.SeitzReduction.F4Pilot
