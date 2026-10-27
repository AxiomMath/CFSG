module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.CampbellStruct1
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.CampbellCalc

public section

namespace CFSG.QuasithinUnique.Setup.Campbell

open Subgroup CFSG CFSG.Quasithin CFSG.Quasithin.BlueprintB2
open scoped LinearAlgebra.Projectivization commutatorElement

@[expose] def Fcore (G : Type*) [Group G] : Subgroup G :=
  centerTorsion 2 (thompsonJ (CFSG.pCore 2 G))

@[expose] def Zfix {G : Type*} [Group G] (S : Sylow 2 G) : Subgroup G :=
  Vmod G ⊓ Subgroup.centralizer ((S : Subgroup G) : Set G)

@[expose] def Hone {G : Type*} [Group G] (S : Sylow 2 G) : Subgroup G :=
  Subgroup.normalClosure ((thompsonJ (S : Subgroup G) : Subgroup G) : Set G)

section Basic

variable {G : Type*} [Group G]

instance Fcore_normal [Finite G] : (Fcore G).Normal :=
  ⟨fun _ hn g => centerTorsion_thompsonJ_conj_mem hn g⟩

instance Hone_normal {S : Sylow 2 G} : (Hone S).Normal := by
  unfold Hone; infer_instance

instance thompsonJ_core_normal [Finite G] : (thompsonJ (CFSG.pCore 2 G)).Normal :=
  ⟨fun _ hn g => thompsonJ_conj_mem hn g⟩

theorem mem_Fcore_iff [Finite G] {x : G} :
    x ∈ Fcore G ↔ x ∈ CFSG.pCore 2 G ∧ ∀ A : Subgroup G, IsMaxElemAbelian (CFSG.pCore 2 G) A →
      x ∈ A :=
  mem_centerTorsion_thompsonJ_iff

theorem Fcore_le_thompsonJ : Fcore G ≤ thompsonJ (CFSG.pCore 2 G) := centerTorsion_le _ _

theorem thompsonJ_core_le_core : thompsonJ (CFSG.pCore 2 G) ≤ CFSG.pCore 2 G :=
  thompsonJ_le_self' _

theorem Fcore_le_core : Fcore G ≤ CFSG.pCore 2 G := Fcore_le_thompsonJ.trans thompsonJ_core_le_core

theorem Fcore_commute {x y : G} (hx : x ∈ Fcore G) (hy : y ∈ Fcore G) [Finite G] : x * y = y * x := by
  obtain ⟨hxQ, hxA⟩ := mem_Fcore_iff.mp hx
  obtain ⟨A₀, hA₀⟩ := exists_maxElem (CFSG.pCore 2 G)
  exact (isElemAbelian_iff.mp hA₀.2.1).1 x (hxA A₀ hA₀) y ((mem_Fcore_iff.mp hy).2 A₀ hA₀)

theorem eq_one_of_forall_smul_eq' {k : Type*} [Field k] {g : Matrix.SpecialLinearGroup (Fin 2) k}
    (hall : ∀ w : Fin 2 → k, g • w = w) : g = 1 := by
  ext i j
  have := congrFun (hall (Pi.single j 1)) i
  rw [Matrix.SpecialLinearGroup.smul_def] at this
  simpa [Matrix.mulVec, dotProduct, Pi.single_apply, Matrix.one_apply] using this

end Basic

section Seed

variable {G : Type*} [Group G] {k : Type*} [Field k] {S : Sylow 2 G}
  {ρ : G →* Matrix.SpecialLinearGroup (Fin 2) k} {ψ : Ecore G →* Multiplicative (Fin 2 → k)}

namespace IsNatBase

theorem mem_core_of_centralizes_Ecore [Finite G] [Finite k] (h : IsNatBase S ρ (Ecore G) ψ) {a : G}
    (haS : a ∈ (S : Subgroup G)) (hc : ∀ e ∈ Ecore G, a * e = e * a) : a ∈ CFSG.pCore 2 G := by
  have hρ : ρ a = 1 := by
    apply eq_one_of_forall_smul_eq'
    intro w
    obtain ⟨e, he⟩ := h.ψ_surj (Multiplicative.ofAdd w)
    have h1 := h.ψ_equiv a e e (by
      have := hc e e.2
      calc (e : G) = (a * e) * a⁻¹ * 1 := by rw [this]; group
        _ = a * e * a⁻¹ := by group)
    rw [he, toAdd_ofAdd] at h1
    rw [Matrix.SpecialLinearGroup.smul_def]
    exact h1.symm
  have hx : a ∈ (S : Subgroup G) ⊓ ρ.ker := ⟨haS, hρ⟩
  rwa [h.sylow_inf_ker] at hx

theorem map_eq_top_of_normal_of_rootGrp_le [Finite G] [Finite k] (h : IsNatBase S ρ (Ecore G) ψ)
    {Y : Subgroup G} [Y.Normal] {ℓ : ℙ k (Fin 2 → k)} (hℓ : rootGrp ℓ ≤ Y.map ρ) :
    Y.map ρ = ⊤ := by
  obtain ⟨m, hm⟩ := exists_ne_point ℓ
  obtain ⟨s, hs⟩ := exists_smul_eq' ℓ m
  have hn : (Y.map ρ).Normal := Subgroup.Normal.map inferInstance ρ h.surj
  have h2 : rootGrp m ≤ Y.map ρ := by
    rw [← hs, rootGrp_smul_eq_map]
    rintro _ ⟨x, hx, rfl⟩
    exact hn.conj_mem x (hℓ hx) s
  rw [eq_top_iff, ← rootGrp_sup_rootGrp (Ne.symm hm)]
  exact sup_le hℓ h2

theorem normalClosure_sylow_eq_top [Finite G] [Finite k] (h : IsNatBase S ρ (Ecore G) ψ) :
    Subgroup.normalClosure ((S : Subgroup G) : Set G) = ⊤ := by
  obtain ⟨ℓ, hℓ⟩ := h.exists_rootGrp_eq
  have hSJ : (S : Subgroup G) ≤ Subgroup.normalClosure ((S : Subgroup G) : Set G) :=
    Subgroup.le_normalClosure
  have : rootGrp ℓ ≤ (Subgroup.normalClosure ((S : Subgroup G) : Set G)).map ρ := by
    rw [← hℓ]; exact Subgroup.map_mono hSJ
  exact h.eq_top_of_map_eq_top ((core_le_sylow S).trans hSJ)
    (h.map_eq_top_of_normal_of_rootGrp_le this)

theorem sylow_commutator_Vmod [Finite G] [Finite k] (h : IsNatBase S ρ (Ecore G) ψ) :
    ⁅(S : Subgroup G), Vmod G⁆ = Zfix S := by
  obtain ⟨ℓ, hℓ⟩ := h.exists_rootGrp_eq
  exact (h.natural_module_facts hℓ).2.1

end IsNatBase

namespace IsSeed

theorem Ecore_le_of_maxElem_core [Finite G] [Finite k] (h : IsSeed S ρ (Ecore G) ψ)
    {A : Subgroup G} (hA : IsMaxElemAbelian (CFSG.pCore 2 G) A) : Ecore G ≤ A := by
  intro e he
  have hAS : IsMaxElemAbelian (S : Subgroup G) A := h.max_core_facts.1 A hA
  refine maxElem_mem_of_centralizer hAS (Ecore_le_sylow he)
    (Subgroup.mem_centralizer_iff.mpr fun a ha => ?_) (Ecore_sq he)
  exact (Ecore_commute_core (hA.1 ha) he)

theorem Ecore_le_Fcore [Finite G] [Finite k] (h : IsSeed S ρ (Ecore G) ψ) : Ecore G ≤ Fcore G :=
  fun _ he => mem_Fcore_iff.mpr ⟨Ecore_le_core he, fun _ hA => h.Ecore_le_of_maxElem_core hA he⟩

theorem thompsonJ_core_le_thompsonJ_sylow [Finite G] [Finite k] (h : IsSeed S ρ (Ecore G) ψ) :
    thompsonJ (CFSG.pCore 2 G) ≤ thompsonJ (S : Subgroup G) :=
  thompsonJ_le_of_forall fun A hA => maxElem_le_thompsonJ (h.max_core_facts.1 A hA)

theorem isMaxElemAbelian_core_of_not_le [Finite G] [Finite k] (h : IsSeed S ρ (Ecore G) ψ)
    {A : Subgroup G} (hA : IsMaxElemAbelian (S : Subgroup G) A) (hAQ : ¬ A ≤ CFSG.pCore 2 G) :
    IsMaxElemAbelian (CFSG.pCore 2 G) ((A ⊓ CFSG.pCore 2 G) ⊔ Ecore G) := by
  obtain ⟨-, -, -, -, -, hB⟩ := h.max_outside hA hAQ
  have hBQ : (A ⊓ CFSG.pCore 2 G) ⊔ Ecore G ≤ CFSG.pCore 2 G :=
    sup_le inf_le_right Ecore_le_core
  exact ⟨hBQ, hB.2.1, fun _ hBQ' hB' => maxElem_card_le hB (hBQ'.trans (core_le_sylow S)) hB'⟩

theorem isMaxElemAbelian_core_of_le [Finite G] {A : Subgroup G}
    (hA : IsMaxElemAbelian (S : Subgroup G) A) (hAQ : A ≤ CFSG.pCore 2 G) :
    IsMaxElemAbelian (CFSG.pCore 2 G) A :=
  ⟨hAQ, hA.2.1, fun _ hBQ hB => maxElem_card_le hA (hBQ.trans (core_le_sylow S)) hB⟩

theorem exists_core_max [Finite G] [Finite k] (h : IsSeed S ρ (Ecore G) ψ) {A : Subgroup G}
    (hA : IsMaxElemAbelian (S : Subgroup G) A) :
    ∃ A' : Subgroup G, IsMaxElemAbelian (CFSG.pCore 2 G) A' ∧ A ⊓ CFSG.pCore 2 G ≤ A' ∧
      (¬ A ≤ CFSG.pCore 2 G → A' = (A ⊓ CFSG.pCore 2 G) ⊔ Ecore G) ∧
      (A ≤ CFSG.pCore 2 G → A' = A) := by
  by_cases hAQ : A ≤ CFSG.pCore 2 G
  · exact ⟨A, isMaxElemAbelian_core_of_le hA hAQ, inf_le_left, fun h' => absurd hAQ h',
      fun _ => rfl⟩
  · exact ⟨_, h.isMaxElemAbelian_core_of_not_le hA hAQ, le_sup_left, fun _ => rfl,
      fun h' => absurd h' hAQ⟩

theorem sylow_eq_sup [Finite G] [Finite k] (h : IsSeed S ρ (Ecore G) ψ) {A : Subgroup G}
    (hA : IsMaxElemAbelian (S : Subgroup G) A) (hAQ : ¬ A ≤ CFSG.pCore 2 G) :
    (S : Subgroup G) = A ⊔ CFSG.pCore 2 G := by
  obtain ⟨hmap, -⟩ := h.max_outside hA hAQ
  apply le_antisymm
  · intro s hs
    have : ρ s ∈ A.map ρ := by rw [hmap]; exact ⟨s, hs, rfl⟩
    obtain ⟨a, ha, hρa⟩ := this
    have hsa : s * a⁻¹ ∈ CFSG.pCore 2 G := by
      have hx : s * a⁻¹ ∈ (S : Subgroup G) ⊓ ρ.ker :=
        Subgroup.mem_inf.mpr ⟨(S : Subgroup G).mul_mem hs ((S : Subgroup G).inv_mem (hA.1 ha)),
          by simp [hρa]⟩
      rwa [h.sylow_inf_ker] at hx
    have : s = (s * a⁻¹) * a := by group
    rw [this]
    exact mul_mem (Subgroup.mem_sup_right hsa) (Subgroup.mem_sup_left ha)
  · exact sup_le hA.1 (core_le_sylow S)

theorem inf_centralizer_Fcore [Finite G] [Finite k] (h : IsSeed S ρ (Ecore G) ψ) {A : Subgroup G}
    (hA : IsMaxElemAbelian (S : Subgroup G) A) :
    A ⊓ Subgroup.centralizer (Fcore G : Set G) = A ⊓ CFSG.pCore 2 G := by
  apply le_antisymm
  · rintro a ⟨haA, hac⟩
    refine ⟨haA, h.mem_core_of_centralizes_Ecore (hA.1 haA) fun e he => ?_⟩
    exact (Subgroup.mem_centralizer_iff.mp hac e (h.Ecore_le_Fcore he)).symm
  · rintro a ⟨haA, haQ⟩
    refine ⟨haA, Subgroup.mem_centralizer_iff.mpr fun f hf => ?_⟩
    obtain ⟨A', hA', hle, -⟩ := h.exists_core_max hA
    exact (isElemAbelian_iff.mp hA'.2.1).1 f ((mem_Fcore_iff.mp hf).2 A' hA') a (hle ⟨haA, haQ⟩)

theorem inf_core_sup_Fcore_of_not_le [Finite G] [Finite k] (h : IsSeed S ρ (Ecore G) ψ)
    {A : Subgroup G} (hA : IsMaxElemAbelian (S : Subgroup G) A) (hAQ : ¬ A ≤ CFSG.pCore 2 G) :
    (A ⊓ CFSG.pCore 2 G) ⊔ Fcore G = (A ⊓ CFSG.pCore 2 G) ⊔ Ecore G := by
  apply le_antisymm
  · refine sup_le le_sup_left fun f hf => ?_
    exact (mem_Fcore_iff.mp hf).2 _ (h.isMaxElemAbelian_core_of_not_le hA hAQ)
  · exact sup_le_sup_left h.Ecore_le_Fcore _

theorem Fcore_le_of_le_core [Finite G] {A : Subgroup G}
    (hA : IsMaxElemAbelian (S : Subgroup G) A) (hAQ : A ≤ CFSG.pCore 2 G) : Fcore G ≤ A :=
  fun _ hf => (mem_Fcore_iff.mp hf).2 A (isMaxElemAbelian_core_of_le hA hAQ)

theorem inf_core_sup_Fcore_of_le [Finite G] {A : Subgroup G}
    (hA : IsMaxElemAbelian (S : Subgroup G) A) (hAQ : A ≤ CFSG.pCore 2 G) :
    (A ⊓ CFSG.pCore 2 G) ⊔ Fcore G = A := by
  rw [inf_eq_left.mpr hAQ]
  exact sup_eq_left.mpr (Fcore_le_of_le_core hA hAQ)

theorem isMaxElemAbelian_core_sup_Fcore [Finite G] [Finite k] (h : IsSeed S ρ (Ecore G) ψ)
    {A : Subgroup G} (hA : IsMaxElemAbelian (S : Subgroup G) A) :
    IsMaxElemAbelian (CFSG.pCore 2 G) ((A ⊓ CFSG.pCore 2 G) ⊔ Fcore G) ∧
      IsMaxElemAbelian (S : Subgroup G) ((A ⊓ CFSG.pCore 2 G) ⊔ Fcore G) := by
  by_cases hAQ : A ≤ CFSG.pCore 2 G
  · rw [inf_core_sup_Fcore_of_le hA hAQ]
    exact ⟨isMaxElemAbelian_core_of_le hA hAQ, hA⟩
  · rw [h.inf_core_sup_Fcore_of_not_le hA hAQ]
    exact ⟨h.isMaxElemAbelian_core_of_not_le hA hAQ, (h.max_outside hA hAQ).2.2.2.2.2⟩

theorem Fcore_eq_Vmod_sup [Finite G] [Finite k] (h : IsSeed S ρ (Ecore G) ψ) {A : Subgroup G}
    (hA : IsMaxElemAbelian (S : Subgroup G) A) : Fcore G = Vmod G ⊔ (A ⊓ Fcore G) := by
  apply le_antisymm
  · intro f hf
    by_cases hAQ : A ≤ CFSG.pCore 2 G
    · exact Subgroup.mem_sup_right ⟨Fcore_le_of_le_core hA hAQ hf, hf⟩
    · have hA' := h.isMaxElemAbelian_core_of_not_le hA hAQ
      have hfA' : f ∈ (A ⊓ CFSG.pCore 2 G) ⊔ Ecore G := (mem_Fcore_iff.mp hf).2 _ hA'
      obtain ⟨a, ha, e, he, rfl⟩ := Subgroup.mem_sup_of_normal_right.mp hfA'
      have haF : a ∈ Fcore G := by
        have : a = (a * e) * e⁻¹ := by group
        rw [this]
        exact mul_mem hf ((Fcore G).inv_mem (h.Ecore_le_Fcore he))
      have he' : e ∈ Vmod G ⊔ (Ecore G ⊓ Subgroup.center G) := by
        rw [← h.Ecore_eq_Vmod_sup]; exact he
      obtain ⟨v, hv, c, hc, hvc⟩ := Subgroup.mem_sup_of_normal_left.mp he'
      have hcA : c ∈ A := maxElem_mem_of_centralizer hA (Ecore_le_sylow hc.1)
        (Subgroup.mem_centralizer_iff.mpr fun x _ => (Subgroup.mem_center_iff.mp hc.2 x))
        (Ecore_sq hc.1)
      rw [← hvc]
      have : a * (v * c) = (a * v * a⁻¹) * (a * c) := by group
      rw [this]
      exact mul_mem (Subgroup.mem_sup_left ((inferInstance : (Vmod G).Normal).conj_mem v hv a))
        (Subgroup.mem_sup_right ⟨mul_mem ha.1 hcA, mul_mem haF (h.Ecore_le_Fcore hc.1)⟩)
  · exact sup_le (Vmod_le_Ecore.trans h.Ecore_le_Fcore) inf_le_right

open scoped commutatorElement in
theorem commutator_A_Vmod [Finite G] [Finite k] (h : IsSeed S ρ (Ecore G) ψ) {A : Subgroup G}
    (hA : IsMaxElemAbelian (S : Subgroup G) A) (hAQ : ¬ A ≤ CFSG.pCore 2 G) :
    ⁅A, Vmod G⁆ = Zfix S := by
  rw [← h.sylow_commutator_Vmod]
  apply le_antisymm (Subgroup.commutator_mono hA.1 le_rfl)
  rw [Subgroup.commutator_le]
  intro s hs v hv
  rw [h.sylow_eq_sup hA hAQ] at hs
  obtain ⟨a, ha, q, hq, rfl⟩ := Subgroup.mem_sup_of_normal_right.mp hs
  have hqv : q * v = v * q := Ecore_commute_core hq (Vmod_le_Ecore hv)
  have : ⁅a * q, v⁆ = ⁅a, v⁆ := by
    simp only [commutatorElement_def]
    calc a * q * v * (a * q)⁻¹ * v⁻¹ = a * (q * v * q⁻¹) * a⁻¹ * v⁻¹ := by group
      _ = a * v * a⁻¹ * v⁻¹ := by rw [hqv]; group
  rw [this]
  exact Subgroup.commutator_mem_commutator ha hv

open scoped commutatorElement in
theorem commutator_A_Fcore [Finite G] [Finite k] (h : IsSeed S ρ (Ecore G) ψ) {A : Subgroup G}
    (hA : IsMaxElemAbelian (S : Subgroup G) A) (hAQ : ¬ A ≤ CFSG.pCore 2 G) :
    ⁅A, Fcore G⁆ = Zfix S := by
  rw [← h.commutator_A_Vmod hA hAQ]
  apply le_antisymm
  · rw [Subgroup.commutator_le]
    intro a ha f hf
    rw [h.Fcore_eq_Vmod_sup hA] at hf
    obtain ⟨v, hv, w, hw, rfl⟩ := Subgroup.mem_sup_of_normal_left.mp hf
    have hwa : Commute a w := (isElemAbelian_iff.mp hA.2.1).1 a ha w hw.1
    have h1 : w * a⁻¹ = a⁻¹ * w := hwa.inv_left.eq.symm
    have : ⁅a, v * w⁆ = ⁅a, v⁆ := by
      simp only [commutatorElement_def]
      calc a * (v * w) * a⁻¹ * (v * w)⁻¹ = a * v * (w * a⁻¹) * w⁻¹ * v⁻¹ := by group
        _ = a * v * a⁻¹ * v⁻¹ := by rw [h1]; group
    rw [this]
    exact Subgroup.commutator_mem_commutator ha hv
  · exact Subgroup.commutator_mono le_rfl (Vmod_le_Ecore.trans h.Ecore_le_Fcore)

open scoped commutatorElement in
theorem commutator_A_Fcore_of_le [Finite G] {A : Subgroup G}
    (hA : IsMaxElemAbelian (S : Subgroup G) A) (hAQ : A ≤ CFSG.pCore 2 G) :
    ⁅A, Fcore G⁆ = ⊥ := by
  rw [eq_bot_iff, Subgroup.commutator_le]
  intro a ha f hf
  have hfA := Fcore_le_of_le_core hA hAQ hf
  have : a * f = f * a := (isElemAbelian_iff.mp hA.2.1).1 a ha f hfA
  rw [Subgroup.mem_bot]
  simp only [commutatorElement_def]
  calc a * f * a⁻¹ * f⁻¹ = (f * a) * a⁻¹ * f⁻¹ := by rw [this]
    _ = 1 := by group

theorem Hone_map_eq_top [Finite G] [Finite k] (h : IsSeed S ρ (Ecore G) ψ) :
    (Hone S).map ρ = ⊤ := by
  obtain ⟨A, hA, hAQ⟩ := h.exists_max_outside
  obtain ⟨hmap, -⟩ := h.max_outside hA hAQ
  obtain ⟨ℓ, hℓ⟩ := h.exists_rootGrp_eq
  have : rootGrp ℓ ≤ (Hone S).map ρ := by
    rw [← hℓ, ← hmap]
    exact Subgroup.map_mono ((maxElem_le_thompsonJ hA).trans Subgroup.le_normalClosure)
  exact h.map_eq_top_of_normal_of_rootGrp_le this

theorem Hone_sup_core [Finite G] [Finite k] (h : IsSeed S ρ (Ecore G) ψ) :
    Hone S ⊔ CFSG.pCore 2 G = ⊤ := by
  refine h.eq_top_of_map_eq_top le_sup_right ?_
  rw [Subgroup.map_sup, h.Hone_map_eq_top, (Subgroup.map_eq_bot_iff _).mpr h.core_le, sup_bot_eq]

theorem Kodd_le_Hone [Finite G] [Finite k] (h : IsSeed S ρ (Ecore G) ψ) : Kodd G ≤ Hone S :=
  pPrimeGen_top_le_of_sup_eq_top (CFSG.pCore_isPGroup (G := G) (p := 2)) h.Hone_sup_core

theorem Zfix_le_Vmod : Zfix S ≤ Vmod G := inf_le_left

theorem Zfix_central {z : G} (hz : z ∈ Zfix S) {s : G} (hs : s ∈ (S : Subgroup G)) :
    s * z = z * s := Subgroup.mem_centralizer_iff.mp hz.2 s hs

open scoped commutatorElement in
theorem commutator_thompsonJ_Fcore [Finite G] [Finite k] (h : IsSeed S ρ (Ecore G) ψ) :
    ⁅thompsonJ (S : Subgroup G), Fcore G⁆ = Zfix S := by
  apply le_antisymm
  · rw [Subgroup.commutator_comm]
    have hNV : ∀ n ∈ (S : Subgroup G), ∀ v ∈ Zfix S, n * v * n⁻¹ ∈ Zfix S := by
      intro n hn z hz
      have : n * z * n⁻¹ = z := by
        calc n * z * n⁻¹ = (z * n) * n⁻¹ := by rw [Zfix_central hz hn]
          _ = z := by group
      rw [this]; exact hz
    have hle : thompsonJ (S : Subgroup G) ≤ commModIn (Fcore G) (Zfix S) (S : Subgroup G) hNV := by
      refine thompsonJ_le_of_forall fun A hA x hx => ⟨hA.1 hx, fun f hf => ?_⟩
      have h3 : ⁅f, x⁆ = ⁅x, f⁆⁻¹ := by simp only [commutatorElement_def]; group
      have h2 : ⁅x, f⁆ ∈ (⁅A, Fcore G⁆ : Subgroup G) := Subgroup.commutator_mem_commutator hx hf
      by_cases hAQ : A ≤ CFSG.pCore 2 G
      · rw [commutator_A_Fcore_of_le hA hAQ, Subgroup.mem_bot] at h2
        rw [h3, h2, inv_one]
        exact one_mem _
      · rw [h.commutator_A_Fcore hA hAQ] at h2
        rw [h3]
        exact (Zfix S).inv_mem h2
    exact Subgroup.commutator_le.mpr fun f hf x hx => (hle hx).2 f hf
  · obtain ⟨A, hA, hAQ⟩ := h.exists_max_outside
    rw [← h.commutator_A_Fcore hA hAQ]
    exact Subgroup.commutator_mono (maxElem_le_thompsonJ hA) le_rfl

open scoped commutatorElement in
theorem commutator_Hone_Fcore [Finite G] [Finite k] (h : IsSeed S ρ (Ecore G) ψ) :
    ⁅Hone S, Fcore G⁆ = Vmod G := by
  have hFT := h.commutator_thompsonJ_Fcore
  have hTH : thompsonJ (S : Subgroup G) ≤ Hone S := Subgroup.le_normalClosure
  apply le_antisymm
  · rw [Subgroup.commutator_comm]
    have hle : Hone S ≤ commModIn (Fcore G) (Vmod G) ⊤
        (fun n _ v hv => (inferInstance : (Vmod G).Normal).conj_mem v hv n) := by
      refine Subgroup.normalClosure_le_normal fun t ht => ⟨Subgroup.mem_top _, fun f hf => ?_⟩
      have h1 : ⁅t, f⁆ ∈ (⁅thompsonJ (S : Subgroup G), Fcore G⁆ : Subgroup G) :=
        Subgroup.commutator_mem_commutator ht hf
      rw [hFT] at h1
      have h3 : ⁅f, t⁆ = ⁅t, f⁆⁻¹ := by simp only [commutatorElement_def]; group
      rw [h3]
      exact (Vmod G).inv_mem (Zfix_le_Vmod h1)
    exact Subgroup.commutator_le.mpr fun f hf x hx => (hle hx).2 f hf
  · have hW'le : Subgroup.normalClosure ((Zfix S : Subgroup G) : Set G) ≤ ⁅Hone S, Fcore G⁆ := by
      refine Subgroup.normalClosure_le_normal ?_
      intro z hz
      rw [← hFT] at hz
      exact Subgroup.commutator_mono hTH le_rfl hz
    have hVW : Vmod G ≤ Subgroup.normalClosure ((Zfix S : Subgroup G) : Set G) := by
      set W' : Subgroup G := Subgroup.normalClosure ((Zfix S : Subgroup G) : Set G) with hW'
      have hS : (S : Subgroup G) ≤ commModIn (Vmod G) W' ⊤
          (fun n _ v hv => (inferInstance : W'.Normal).conj_mem v hv n) := by
        intro s hs
        refine ⟨Subgroup.mem_top _, fun v hv => ?_⟩
        have h1 : ⁅s, v⁆ ∈ (⁅(S : Subgroup G), Vmod G⁆ : Subgroup G) :=
          Subgroup.commutator_mem_commutator hs hv
        rw [h.sylow_commutator_Vmod] at h1
        have h3 : ⁅v, s⁆ = ⁅s, v⁆⁻¹ := by simp only [commutatorElement_def]; group
        rw [h3]
        exact W'.inv_mem (Subgroup.le_normalClosure h1)
      have hJ : Subgroup.normalClosure ((S : Subgroup G) : Set G) ≤ commModIn (Vmod G) W' ⊤
          (fun n _ v hv => (inferInstance : W'.Normal).conj_mem v hv n) :=
        Subgroup.normalClosure_le_normal hS
      rw [h.normalClosure_sylow_eq_top] at hJ
      calc Vmod G = ⁅Vmod G, Kodd G⁆ := Vmod_commutator.symm
        _ ≤ W' := Subgroup.commutator_le.mpr fun v hv x _ => (hJ (Subgroup.mem_top x)).2 v hv
    exact hVW.trans hW'le

theorem mem_Fcore_of_central_involution [Finite G] [Finite k] (h : IsSeed S ρ (Ecore G) ψ)
    {s : G} (hs : s ∈ (S : Subgroup G)) (hc : ∀ t ∈ (S : Subgroup G), s * t = t * s)
    (hs2 : s ^ 2 = 1) : s ∈ Fcore G := by
  obtain ⟨A₀, hA₀⟩ := exists_maxElem (CFSG.pCore 2 G)
  have hmem : ∀ A : Subgroup G, IsMaxElemAbelian (CFSG.pCore 2 G) A → s ∈ A := by
    intro A hA
    refine maxElem_mem_of_centralizer (h.max_core_facts.1 A hA) hs
      (Subgroup.mem_centralizer_iff.mpr fun a ha => ?_) hs2
    exact (hc a (core_le_sylow S (hA.1 ha))).symm
  exact mem_Fcore_iff.mpr ⟨hA₀.1 (hmem A₀ hA₀), hmem⟩

theorem sylow_inf_centralizer_Fcore_le [Finite G] [Finite k] (h : IsSeed S ρ (Ecore G) ψ) :
    (S : Subgroup G) ⊓ Subgroup.centralizer (Fcore G : Set G) ≤ CFSG.pCore 2 G := by
  rintro a ⟨haS, hac⟩
  exact h.mem_core_of_centralizes_Ecore haS fun e he =>
    (Subgroup.mem_centralizer_iff.mp hac e (h.Ecore_le_Fcore he)).symm

open scoped commutatorElement in
theorem Campbell_Thompson_center_module_structure [Finite G] [Finite k]
    (h : IsSeed S ρ (Ecore G) ψ) :
    Odd (Nat.card (ρ.ker.map (QuotientGroup.mk' (CFSG.pCore 2 G)))) ∧
    (S : Subgroup G) ⊓ ρ.ker = CFSG.pCore 2 G ∧
    ρ.ker ≤ Subgroup.centralizer (Ecore G : Set G) ∧
    ⁅Vmod G, Kodd G⁆ = Vmod G ∧
    Ecore G = Vmod G ⊔ (Ecore G ⊓ Subgroup.center G) ∧
    (∀ w : Multiplicative (Fin 2 → k), ∃ v : Ecore G, (v : G) ∈ Vmod G ∧ ψ v = w) ∧
    (∀ v : Ecore G, (v : G) ∈ Vmod G → (ψ v = 1 ↔ (v : G) ∈ Subgroup.center G)) ∧
    ⁅(S : Subgroup G), Vmod G⁆ = Zfix S ∧
    (∀ z ∈ Zfix S, ∀ s ∈ (S : Subgroup G), s * z = z * s) ∧
    Hone S ⊔ CFSG.pCore 2 G = ⊤ ∧ Kodd G ≤ Hone S ∧ (Hone S).map ρ = ⊤ ∧
    Vmod G ≤ Ecore G ∧ Ecore G ≤ Fcore G ∧ Fcore G ≤ thompsonJ (CFSG.pCore 2 G) ∧
    thompsonJ (CFSG.pCore 2 G) ≤ thompsonJ (S : Subgroup G) ∧
    (Ecore G).Normal ∧ (Fcore G).Normal ∧ (thompsonJ (CFSG.pCore 2 G)).Normal ∧
    (Vmod G).Normal ∧
    (∀ A B : Subgroup G, IsMaxElemAbelian (S : Subgroup G) A →
      IsMaxElemAbelian (CFSG.pCore 2 G) B → Nat.card B = Nat.card A) ∧
    (∀ B : Subgroup G, IsMaxElemAbelian (CFSG.pCore 2 G) B →
      IsMaxElemAbelian (S : Subgroup G) B) ∧
    (∀ A : Subgroup G, IsMaxElemAbelian (S : Subgroup G) A →
      A ⊓ Subgroup.centralizer (Fcore G : Set G) = A ⊓ CFSG.pCore 2 G ∧
      IsMaxElemAbelian (CFSG.pCore 2 G) ((A ⊓ CFSG.pCore 2 G) ⊔ Fcore G) ∧
      IsMaxElemAbelian (S : Subgroup G) ((A ⊓ CFSG.pCore 2 G) ⊔ Fcore G) ∧
      Fcore G = Vmod G ⊔ (A ⊓ Fcore G) ∧
      (¬ A ≤ CFSG.pCore 2 G → (S : Subgroup G) = A ⊔ CFSG.pCore 2 G ∧
        ⁅A, Fcore G⁆ = ⁅A, Vmod G⁆ ∧ ⁅A, Vmod G⁆ = Zfix S) ∧
      (A ≤ CFSG.pCore 2 G → ⁅A, Fcore G⁆ = ⊥)) ∧
    ⁅thompsonJ (S : Subgroup G), Fcore G⁆ = Zfix S ∧ ⁅Hone S, Fcore G⁆ = Vmod G ∧
    (∀ Y A : Subgroup G, IsMaxElemAbelian (S : Subgroup G) A → Y ≤ A →
      (∃ A' : Subgroup G, IsMaxElemAbelian (CFSG.pCore 2 G) A' ∧ Y ⊓ CFSG.pCore 2 G ≤ A') ∧
      ⁅Y ⊓ CFSG.pCore 2 G, Fcore G⁆ = ⊥ ∧
      Fcore G = Vmod G ⊔ (Fcore G ⊓ Subgroup.centralizer (Y : Set G))) ∧
    (∀ s ∈ (S : Subgroup G), (∀ t ∈ (S : Subgroup G), s * t = t * s) → s ^ 2 = 1 →
      s ∈ Fcore G) ∧
    (S : Subgroup G) ⊓ Subgroup.centralizer (Fcore G : Set G) ≤ CFSG.pCore 2 G := by
  refine ⟨h.odd_card_ker, h.sylow_inf_ker, h.ker_le_centralizer_Ecore, Vmod_commutator,
    h.Ecore_eq_Vmod_sup, h.ψ_Vmod_surj, fun v _ => h.ψ_eq_one_iff, h.sylow_commutator_Vmod,
    fun z hz s hs => Zfix_central hz hs, h.Hone_sup_core, h.Kodd_le_Hone, h.Hone_map_eq_top,
    Vmod_le_Ecore, h.Ecore_le_Fcore, Fcore_le_thompsonJ, h.thompsonJ_core_le_thompsonJ_sylow,
    inferInstance, inferInstance, inferInstance, inferInstance, h.max_core_facts.2,
    h.max_core_facts.1, ?_, h.commutator_thompsonJ_Fcore, h.commutator_Hone_Fcore, ?_,
    fun s hs hc hs2 => h.mem_Fcore_of_central_involution hs hc hs2,
    h.sylow_inf_centralizer_Fcore_le⟩
  · intro A hA
    refine ⟨h.inf_centralizer_Fcore hA, (h.isMaxElemAbelian_core_sup_Fcore hA).1,
      (h.isMaxElemAbelian_core_sup_Fcore hA).2, h.Fcore_eq_Vmod_sup hA, fun hAQ => ?_, fun hAQ => ?_⟩
    · exact ⟨h.sylow_eq_sup hA hAQ, (h.commutator_A_Fcore hA hAQ).trans
        (h.commutator_A_Vmod hA hAQ).symm, h.commutator_A_Vmod hA hAQ⟩
    · exact commutator_A_Fcore_of_le hA hAQ
  · intro Y A hA hYA
    obtain ⟨A', hA', hle, -⟩ := h.exists_core_max hA
    refine ⟨⟨A', hA', (inf_le_inf_right _ hYA).trans hle⟩, ?_, ?_⟩
    · rw [eq_bot_iff, Subgroup.commutator_le]
      intro y hy f hf
      have hy' : y ∈ A' := (inf_le_inf_right _ hYA).trans hle hy
      have hf' : f ∈ A' := (mem_Fcore_iff.mp hf).2 A' hA'
      rw [Subgroup.mem_bot]
      simp only [commutatorElement_def]
      have := (isElemAbelian_iff.mp hA'.2.1).1 y hy' f hf'
      calc y * f * y⁻¹ * f⁻¹ = (f * y) * y⁻¹ * f⁻¹ := by rw [this]
        _ = 1 := by group
    · apply le_antisymm
      · calc Fcore G = Vmod G ⊔ (A ⊓ Fcore G) := h.Fcore_eq_Vmod_sup hA
          _ ≤ Vmod G ⊔ (Fcore G ⊓ Subgroup.centralizer (Y : Set G)) := by
            refine sup_le_sup_left ?_ _
            rintro w ⟨hwA, hwF⟩
            refine ⟨hwF, Subgroup.mem_centralizer_iff.mpr fun y hy => ?_⟩
            exact (isElemAbelian_iff.mp hA.2.1).1 y (hYA hy) w hwA
      · exact sup_le (Vmod_le_Ecore.trans h.Ecore_le_Fcore) inf_le_left

end IsSeed

end Seed

end CFSG.QuasithinUnique.Setup.Campbell
