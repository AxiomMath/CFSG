module

import CFSG.GroupTheory.ElementaryAbelianTransport
public import CFSG.CGT.PushingUpLit.BHS.ParabolicChoice
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Basic245BaumannSetting

public section

namespace CFSG.CGT.PushingUpLit.BHS

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.QuasithinUnique.Setup.Campbell
open scoped commutatorElement

variable {Γ : Type} [Group Γ]

theorem isMinParabolic2_of_minimal_gen {S P M₀ : Subgroup Γ} (hS : IsSylowTwoOf S P)
    (hSM : S ≤ M₀) (hnn : ¬ P ≤ Subgroup.normalizer (S : Set Γ)) (hP : ¬ P ≤ M₀)
    (hmin : ∀ X : Subgroup Γ, S ≤ X → X < P → X ≤ M₀) : IsMinParabolic2 S P :=
  ⟨hS, hnn, P ⊓ M₀, le_inf hS.1 hSM, lt_of_le_of_ne inf_le_left fun h => hP (h ▸ inf_le_right),
    fun X hSX hXP => le_inf hXP.le (hmin X hSX hXP)⟩

section SL2

variable {F : Type} [Field F] {G V : Subgroup Γ}

theorem centralizer_le_of_map_eq_top (α : ↥G →* Matrix.SpecialLinearGroup (Fin 2) F)
    (hαk : α.ker = (Subgroup.centralizer (V : Set Γ)).subgroupOf G) {X : Subgroup Γ}
    (hX : (X.subgroupOf G).map α = ⊤) {v : Γ} (hv : v ∈ V)
    (hvX : v ∈ Subgroup.centralizer (X : Set Γ)) : v ∈ Subgroup.centralizer (G : Set Γ) := by
  rw [Subgroup.mem_centralizer_iff]
  intro g hg
  have hmem : α ⟨g, hg⟩ ∈ (X.subgroupOf G).map α := hX ▸ Subgroup.mem_top _
  obtain ⟨y, hy, hyg⟩ := hmem
  have hy' : (y : Γ) ∈ X := Subgroup.mem_subgroupOf.mp hy
  have h1 : α (y⁻¹ * ⟨g, hg⟩) = 1 := by rw [map_mul, map_inv, hyg, inv_mul_cancel]
  have h2 : (y⁻¹ * ⟨g, hg⟩ : ↥G) ∈ α.ker := h1
  rw [hαk, Subgroup.mem_subgroupOf, Subgroup.mem_centralizer_iff] at h2
  have h3 : v * ((y : Γ)⁻¹ * g) = ((y : Γ)⁻¹ * g) * v := h2 v hv
  have h4 := Subgroup.mem_centralizer_iff.mp hvX (y : Γ) hy'
  calc g * v = (y : Γ) * (((y : Γ)⁻¹ * g) * v) := by group
    _ = (y : Γ) * (v * ((y : Γ)⁻¹ * g)) := by rw [h3]
    _ = ((y : Γ) * v) * ((y : Γ)⁻¹ * g) := by group
    _ = (v * (y : Γ)) * ((y : Γ)⁻¹ * g) := by rw [h4]
    _ = v * g := by group

theorem map_cStarIn_ne_top {C : Subgroup Γ} (hCG : C ≤ G)
    (α : ↥G →* Matrix.SpecialLinearGroup (Fin 2) F)
    (hαk : α.ker = (Subgroup.centralizer (V : Set Γ)).subgroupOf G)
    (hKC : G ⊓ Subgroup.centralizer (V : Set Γ) ≤ C) (hne : C ≠ G) :
    (C.subgroupOf G).map α ≠ ⊤ := by
  intro htop
  apply hne
  refine le_antisymm hCG fun g hg => ?_
  have hmem : α ⟨g, hg⟩ ∈ (C.subgroupOf G).map α := htop ▸ Subgroup.mem_top _
  obtain ⟨y, hy, hyg⟩ := hmem
  have hy' : (y : Γ) ∈ C := Subgroup.mem_subgroupOf.mp hy
  have h1 : α (y⁻¹ * ⟨g, hg⟩) = 1 := by rw [map_mul, map_inv, hyg, inv_mul_cancel]
  have h2 : (y⁻¹ * ⟨g, hg⟩ : ↥G) ∈ α.ker := h1
  rw [hαk, Subgroup.mem_subgroupOf] at h2
  have h3 : ((y : Γ)⁻¹ * g) ∈ C := hKC ⟨(y⁻¹ * ⟨g, hg⟩ : ↥G).2, h2⟩
  have e : g = (y : Γ) * ((y : Γ)⁻¹ * g) := by group
  rw [e]
  exact C.mul_mem hy' h3

end SL2

theorem characteristic_map_mulEquiv' {A B : Type*} [Group A] [Group B] {K : Subgroup A}
    (hK : K.Characteristic) (e : A ≃* B) : (K.map e.toMonoidHom).Characteristic := by
  refine Subgroup.characteristic_iff_map_eq.mpr fun φ => ?_
  have h := Subgroup.characteristic_iff_map_eq.mp hK ((e.trans φ).trans e.symm)
  rw [Subgroup.map_map]
  calc K.map (φ.toMonoidHom.comp e.toMonoidHom)
      = (K.map ((e.trans φ).trans e.symm).toMonoidHom).map e.toMonoidHom := by
        rw [Subgroup.map_map]; congr 1; ext x; simp
    _ = K.map e.toMonoidHom := by rw [h]

theorem noCharNormal_top_subgroupOf' {H S : Subgroup Γ} (hSH : S ≤ H)
    (hnc : ∀ C : Subgroup Γ, C ≤ S → C ≠ ⊥ → (C.subgroupOf S).Characteristic →
      ¬ H ≤ Subgroup.normalizer (C : Set Γ)) :
    NoCharNormal (S.subgroupOf H) (⊤ : Subgroup H) := by
  intro C hCS hC1 hCchar hCn
  have hCS' : C.map H.subtype ≤ S := by
    rintro _ ⟨c, hc, rfl⟩
    exact Subgroup.mem_subgroupOf.mp (hCS hc)
  refine hnc (C.map H.subtype) hCS' ?_ ?_ ?_
  · intro h
    exact hC1 ((Subgroup.map_eq_bot_iff_of_injective _ H.subtype_injective).mp h)
  · set e : ↥(S.subgroupOf H) ≃* ↥S := Subgroup.subgroupOfEquivOfLe hSH
    have he : (C.subgroupOf (S.subgroupOf H)).map e.toMonoidHom =
        (C.map H.subtype).subgroupOf S := by
      ext x
      simp only [Subgroup.mem_map, Subgroup.mem_subgroupOf]
      constructor
      · rintro ⟨y, hy, rfl⟩
        exact ⟨(y : H), hy, rfl⟩
      · rintro ⟨y, hy, hyx⟩
        have hyS : (y : Γ) ∈ S := by rw [show (y : Γ) = x from hyx]; exact x.2
        refine ⟨⟨y, Subgroup.mem_subgroupOf.mpr hyS⟩, hy, ?_⟩
        exact Subtype.ext hyx
    rw [← he]
    exact characteristic_map_mulEquiv' hCchar e
  · intro g hg
    have h1 := hCn (Subgroup.mem_top (⟨g, hg⟩ : H))
    rw [Subgroup.mem_normalizer_iff] at h1 ⊢
    intro x
    constructor
    · rintro ⟨c, hc, rfl⟩
      exact ⟨⟨g, hg⟩ * c * ⟨g, hg⟩⁻¹, (h1 c).mp hc, rfl⟩
    · rintro ⟨c, hc, hcx⟩
      have hxH : x ∈ H := by
        have : g⁻¹ * (g * x * g⁻¹) * g ∈ H :=
          mul_mem (mul_mem (inv_mem hg) (hcx ▸ c.2)) hg
        simpa [mul_assoc] using this
      refine ⟨⟨x, hxH⟩, (h1 ⟨x, hxH⟩).mpr ?_, rfl⟩
      have : (⟨g, hg⟩ : H) * ⟨x, hxH⟩ * (⟨g, hg⟩ : H)⁻¹ = c := Subtype.ext hcx.symm
      rw [this]
      exact hc

theorem isElemAbelian_of_le' {A B : Subgroup Γ} (hAB : A ≤ B) (hB : IsElemAbelian 2 B) :
    IsElemAbelian 2 A := CFSG.Open.IsElemAbelian.mono hB hAB

theorem isElemAbelian_omegaOneCenterOf' (X : Subgroup Γ) :
    IsElemAbelian 2 (omegaOneCenterOf X) := by
  have hle : omegaOneCenterOf X ≤ centerOf X := by
    refine (Subgroup.closure_le _).mpr fun x hx => hx.1
    
  have hcomm : ∀ a ∈ omegaOneCenterOf X, ∀ b ∈ omegaOneCenterOf X, a * b = b * a := by
    intro a ha b hb
    have hb' : b ∈ X := (hle hb).1
    exact (Subgroup.mem_centralizer_iff.mp (hle ha).2 b hb').symm
  refine ⟨GammaExtra.isMulCommutative_iff_forall.mpr hcomm, fun x hx => ?_⟩
  induction hx using Subgroup.closure_induction with
  | mem x hx => exact hx.2
  | one => simp
  | mul x y hx hy ihx ihy =>
    have hc : Commute x y := hcomm x hx y hy
    rw [hc.mul_pow, ihx, ihy, one_mul]
  | inv x hx ih => rw [inv_pow, ih, inv_one]

theorem normalizer_le_normalizer_of_char' {S C : Subgroup Γ} (hCS : C ≤ S)
    (hchar : (C.subgroupOf S).Characteristic) :
    Subgroup.normalizer (S : Set Γ) ≤ Subgroup.normalizer (C : Set Γ) := by
  intro g hg
  let φ : MulAut ↥S := Subgroup.normalizerMonoidHom S ⟨g, hg⟩
  have hφ : ∀ c ∈ C, g * c * g⁻¹ ∈ C := by
    intro c hc
    have hcS : c ∈ S := hCS hc
    have h1 : φ ⟨c, hcS⟩ ∈ C.subgroupOf S :=
      (Subgroup.characteristic_iff_le_comap.mp hchar) φ (Subgroup.mem_subgroupOf.mpr hc)
    have h2 : ((φ ⟨c, hcS⟩ : ↥S) : Γ) = g * c * g⁻¹ :=
      Subgroup.normalizerMonoidHom_apply_apply_coe S ⟨g, hg⟩ ⟨c, hcS⟩
    exact h2 ▸ Subgroup.mem_subgroupOf.mp h1
  have hg' : g⁻¹ ∈ Subgroup.normalizer (S : Set Γ) := (Subgroup.normalizer _).inv_mem hg
  let φ' : MulAut ↥S := Subgroup.normalizerMonoidHom S ⟨g⁻¹, hg'⟩
  have hφ' : ∀ c ∈ C, g⁻¹ * c * g ∈ C := by
    intro c hc
    have hcS : c ∈ S := hCS hc
    have h1 : φ' ⟨c, hcS⟩ ∈ C.subgroupOf S :=
      (Subgroup.characteristic_iff_le_comap.mp hchar) φ' (Subgroup.mem_subgroupOf.mpr hc)
    have h2 : ((φ' ⟨c, hcS⟩ : ↥S) : Γ) = g⁻¹ * c * g⁻¹⁻¹ :=
      Subgroup.normalizerMonoidHom_apply_apply_coe S ⟨g⁻¹, hg'⟩ ⟨c, hcS⟩
    simpa [h2] using Subgroup.mem_subgroupOf.mp h1
  rw [Subgroup.mem_normalizer_iff]
  intro x
  exact ⟨hφ x, fun hx => by simpa [mul_assoc] using hφ' _ hx⟩

theorem commutator_thompson_ne_bot [Finite Γ] {R H V : Subgroup Γ} (hRH : R ≤ H) (hVH : V ≤ H)
    (hJ : ¬ thompsonJ R ≤ Subgroup.centralizer (V : Set Γ)) :
    ⁅elemThompsonIn 2 (R.subgroupOf H), V.subgroupOf H⁆ ≠ ⊥ := by
  intro hbot
  apply hJ
  intro j hj
  rw [← C56.elemThompsonIn_subgroupOf_map hRH] at hj
  obtain ⟨j', hj', rfl⟩ := hj
  refine Subgroup.mem_centralizer_iff.mpr fun u hu => ?_
  have hmem : ⁅j', (⟨u, hVH hu⟩ : ↥H)⁆ ∈ ⁅elemThompsonIn 2 (R.subgroupOf H), V.subgroupOf H⁆ :=
    Subgroup.commutator_mem_commutator hj' (Subgroup.mem_subgroupOf.mpr hu)
  rw [hbot, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at hmem
  exact (congrArg Subtype.val hmem).symm

section SL2Restrict

variable {F : Type} [Field F] {G V : Subgroup Γ}

theorem natural_data_restrict (α : ↥G →* Matrix.SpecialLinearGroup (Fin 2) F)
    (hαk : α.ker = (Subgroup.centralizer (V : Set Γ)).subgroupOf G)
    (β : ↥V →* Multiplicative (Fin 2 → F))
    (hβe : ∀ (g : ↥G) (v v' : ↥V), (v' : Γ) = g * v * g⁻¹ →
      Multiplicative.toAdd (β v') =
        (α g : Matrix (Fin 2) (Fin 2) F).mulVec (Multiplicative.toAdd (β v)))
    (hβk : β.ker = (Subgroup.centralizer (G : Set Γ)).subgroupOf V)
    {X : Subgroup Γ} (hXG : X ≤ G) (hX : (X.subgroupOf G).map α = ⊤) :
    Function.Surjective (α.comp (Subgroup.inclusion hXG)) ∧
      (α.comp (Subgroup.inclusion hXG)).ker = (Subgroup.centralizer (V : Set Γ)).subgroupOf X ∧
      (∀ (g : ↥X) (v v' : ↥V), (v' : Γ) = g * v * g⁻¹ →
        Multiplicative.toAdd (β v') = ((α.comp (Subgroup.inclusion hXG)) g :
          Matrix (Fin 2) (Fin 2) F).mulVec (Multiplicative.toAdd (β v))) ∧
      β.ker = (Subgroup.centralizer (X : Set Γ)).subgroupOf V := by
  refine ⟨?_, ?_, fun g v v' h => hβe (Subgroup.inclusion hXG g) v v' h, ?_⟩
  · intro A
    have hA : A ∈ (X.subgroupOf G).map α := hX ▸ Subgroup.mem_top A
    obtain ⟨y, hy, rfl⟩ := hA
    exact ⟨⟨y.1, hy⟩, rfl⟩
  · ext x
    rw [Subgroup.mem_subgroupOf]
    exact map_eq_one_iff_centralizer α hαk (hXG x.2)
  · ext v
    rw [hβk, Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
    constructor
    · intro hv
      exact Subgroup.centralizer_le hXG hv
    · intro hv
      exact centralizer_le_of_map_eq_top α hαk hX v.2 hv

end SL2Restrict

end CFSG.CGT.PushingUpLit.BHS
