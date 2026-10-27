module

public import CFSG.GH74.GLS.Stage2.Final.L26.GLevel

public section

namespace CFSG.GH74.GLS.Stage2.Final.L26

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage2.Local CFSG.GH74.GLS.Stage2.Final.Thm4
  CFSG.LocalAnalysis.ComponentInitial

section Aux

theorem card_center_eq_of_mulEquiv {A B : Type*} [Group A] [Group B] (e : A ≃* B) :
    Nat.card (center A) = Nat.card (center B) := by
  refine Nat.card_congr
    { toFun := fun x => ⟨e x, ?_⟩
      invFun := fun y => ⟨e.symm y, ?_⟩
      left_inv := fun x => Subtype.ext (by simp)
      right_inv := fun y => Subtype.ext (by simp) }
  · rw [Subgroup.mem_center_iff]
    intro g
    have := Subgroup.mem_center_iff.mp x.2 (e.symm g)
    simpa using congrArg e this
  · rw [Subgroup.mem_center_iff]
    intro g
    have := Subgroup.mem_center_iff.mp y.2 (e g)
    simpa using congrArg e.symm this

theorem card_center_le_two_of_hasSL2Model {K : Type} [Group K] {P : ℕ → Prop} (h : HasSL2Model K P) :
    Nat.card (center K) ≤ 2 := by
  obtain ⟨F, hF, hFin, -, ⟨e⟩⟩ := h
  rw [card_center_eq_of_mulEquiv (e.trans (specialLinearGroupEquivStatedSL 2 F).symm),
    Nat.card_congr (Matrix.SpecialLinearGroup.center_equiv_rootsOfUnity' (i := (0 : Fin 2)) (R := F)).toEquiv]
  simpa using card_rootsOfUnity F 2

theorem exists_mul_of_mem_sup_of_commute {Y : Type*} [Group Y] {A B : Subgroup Y}
    (h : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a) {x : Y} (hx : x ∈ A ⊔ B) : ∃ a ∈ A, ∃ b ∈ B, x = a * b := by
  rw [Subgroup.sup_eq_closure] at hx
  induction hx using Subgroup.closure_induction with
  | mem y hy =>
    rcases hy with hy | hy
    · exact ⟨y, hy, 1, B.one_mem, by simp⟩
    · exact ⟨1, A.one_mem, y, hy, by simp⟩
  | one => exact ⟨1, A.one_mem, 1, B.one_mem, by simp⟩
  | mul y₁ y₂ _ _ h₁ h₂ =>
    obtain ⟨a₁, ha₁, b₁, hb₁, rfl⟩ := h₁
    obtain ⟨a₂, ha₂, b₂, hb₂, rfl⟩ := h₂
    refine ⟨a₁ * a₂, A.mul_mem ha₁ ha₂, b₁ * b₂, B.mul_mem hb₁ hb₂, ?_⟩
    have := h a₂ ha₂ b₁ hb₁
    calc a₁ * b₁ * (a₂ * b₂) = a₁ * (b₁ * a₂) * b₂ := by group
      _ = a₁ * (a₂ * b₁) * b₂ := by rw [← this]
      _ = a₁ * a₂ * (b₁ * b₂) := by group
  | inv y _ h₁ =>
    obtain ⟨a, ha, b, hb, rfl⟩ := h₁
    refine ⟨a⁻¹, A.inv_mem ha, b⁻¹, B.inv_mem hb, ?_⟩
    have := h a⁻¹ (A.inv_mem ha) b hb
    calc (a * b)⁻¹ = b⁻¹ * a⁻¹ := by group
      _ = a⁻¹ * b⁻¹ := by
        have h2 : a⁻¹ * b = b * a⁻¹ := this
        calc b⁻¹ * a⁻¹ = b⁻¹ * (a⁻¹ * b) * b⁻¹ := by group
          _ = b⁻¹ * (b * a⁻¹) * b⁻¹ := by rw [h2]
          _ = a⁻¹ * b⁻¹ := by group

end Aux

section Pair

variable {G : Type} [Group G] [Finite G] {z : G} {k : Kind} {S : Subgroup G} {q : ℕ}
  {L₁ L₂ : Subgroup (CentralizerBar z)}

theorem lemma26_of_pair (hctx : Stage2Ctx G z k S) (h : Stage1Pair G z S q L₁ L₂) : Lemma26 z S := by
  obtain ⟨hsup, hcomm, hcard⟩ := h.prod
  have hc₁ : IsComponent L₁ := by
    have : L₁ ∈ {K : Subgroup (CentralizerBar z) | IsComponent K} := by
      rw [h.comps]
      exact Set.mem_insert _ _
    exact this
  have hc₂ : IsComponent L₂ := by
    have : L₂ ∈ {K : Subgroup (CentralizerBar z) | IsComponent K} := by
      rw [h.comps]
      exact Set.mem_insert_of_mem _ (Set.mem_singleton _)
    exact this
  have hlayer : layer (CentralizerBar z) = L₁ ⊔ L₂ := by
    simp only [CFSG.layer.eq_sSup]
    rw [h.comps, sSup_pair]
  have h1 : generalizedFitting (CentralizerBar z) ≤ layer (CentralizerBar z) := by
    rw [h.fitting, hlayer, hsup]
  obtain ⟨s, hsS, hswap⟩ := h.swap
  obtain ⟨hsC, hsw1, hsw2⟩ := hswap
  have hconj : ∀ (K A B : Subgroup (CentralizerBar z)), K.Normal →
      conjugate A (toBar z ⟨s, hsC⟩) = B → A ≤ K → B ≤ K := by
    intro K A B hK hAB hAK x hx
    rw [← hAB] at hx
    obtain ⟨a, ha, rfl⟩ := hx
    have := hK.conj_mem a (hAK ha) (toBar z ⟨s, hsC⟩)⁻¹
    simpa using this
  have hcommE : ∀ K : Subgroup (CentralizerBar z), (L₁ ≤ centralizer (K : Set (CentralizerBar z))) →
      (L₂ ≤ centralizer (K : Set (CentralizerBar z))) → ∀ x ∈ K, ∀ e ∈ layer (CentralizerBar z), x * e = e * x := by
    intro K hK1 hK2 x hx e he
    have hle : L₁ ⊔ L₂ ≤ centralizer ({x} : Set (CentralizerBar z)) := by
      refine sup_le (fun a ha => ?_) (fun a ha => ?_)
      · rw [Subgroup.mem_centralizer_singleton_iff]
        exact (Subgroup.mem_centralizer_iff.mp (hK1 ha) x hx).symm
      · rw [Subgroup.mem_centralizer_singleton_iff]
        exact (Subgroup.mem_centralizer_iff.mp (hK2 ha) x hx).symm
    rw [hlayer] at he
    exact (Subgroup.mem_centralizer_singleton_iff.mp (hle he)).symm
  refine lemma26_of_layer_data hctx h1 ?_ ?_
  · intro K hK hKE hnc
    rcases component_normal_subgroup hc₁ hK with h1' | h1'
    · rw [hlayer]
      exact sup_le h1' (hconj K L₁ L₂ hK hsw1 h1')
    · rcases component_normal_subgroup hc₂ hK with h2' | h2'
      · rw [hlayer]
        exact sup_le (hconj K L₂ L₁ hK hsw2 h2') h2'
      · exfalso
        apply hnc
        exact hcommE K (Subgroup.commutator_eq_bot_iff_le_centralizer.mp h1')
          (Subgroup.commutator_eq_bot_iff_le_centralizer.mp h2')
  ·
    have hS₁ : L₁ ⊓ L₂ = (center ↥L₁).map L₁.subtype := by
      have hle : L₁ ⊓ L₂ ≤ (center ↥L₁).map L₁.subtype := by
        intro a ha
        refine ⟨⟨a, ha.1⟩, ?_, rfl⟩
        show (⟨a, ha.1⟩ : ↥L₁) ∈ center ↥L₁
        rw [Subgroup.mem_center_iff]
        intro g
        exact Subtype.ext (hcomm g g.2 a ha.2)
      refine Subgroup.eq_of_le_of_card_ge hle ?_
      rw [Subgroup.card_map_of_injective L₁.subtype_injective, hcard]
      exact card_center_le_two_of_hasSL2Model h.sl₁
    have hS₂ : L₁ ⊓ L₂ = (center ↥L₂).map L₂.subtype := by
      have hle : L₁ ⊓ L₂ ≤ (center ↥L₂).map L₂.subtype := by
        intro a ha
        refine ⟨⟨a, ha.2⟩, ?_, rfl⟩
        show (⟨a, ha.2⟩ : ↥L₂) ∈ center ↥L₂
        rw [Subgroup.mem_center_iff]
        intro g
        exact Subtype.ext (hcomm a ha.1 g g.2).symm
      refine Subgroup.eq_of_le_of_card_ge hle ?_
      rw [Subgroup.card_map_of_injective L₂.subtype_injective, hcard]
      exact card_center_le_two_of_hasSL2Model h.sl₂
    have hZ : ∀ e : ↥(layer (CentralizerBar z)), e ∈ center ↥(layer (CentralizerBar z)) →
        (e : CentralizerBar z) ∈ L₁ ⊓ L₂ := by
      intro e he
      have heE : (e : CentralizerBar z) ∈ L₁ ⊔ L₂ := hlayer ▸ e.2
      obtain ⟨a, ha, b, hb, hab⟩ := exists_mul_of_mem_sup_of_commute hcomm heE
      have hal : ∀ l ∈ L₁, a * l = l * a := by
        intro l hl
        have hlE : l ∈ layer (CentralizerBar z) := hlayer ▸ Subgroup.mem_sup_left hl
        have h5 := congrArg Subtype.val (Subgroup.mem_center_iff.mp he ⟨l, hlE⟩)
        change l * (e : CentralizerBar z) = (e : CentralizerBar z) * l at h5
        rw [hab] at h5
        have hbl : b * l = l * b := (hcomm l hl b hb).symm
        have e1 : l * a * b = a * l * b := by
          calc l * a * b = l * (a * b) := by group
            _ = a * b * l := h5
            _ = a * (b * l) := by group
            _ = a * (l * b) := by rw [hbl]
            _ = a * l * b := by group
        exact (mul_right_cancel e1).symm
      have hbl : ∀ l ∈ L₂, b * l = l * b := by
        intro l hl
        have hlE : l ∈ layer (CentralizerBar z) := hlayer ▸ Subgroup.mem_sup_right hl
        have h5 := congrArg Subtype.val (Subgroup.mem_center_iff.mp he ⟨l, hlE⟩)
        change l * (e : CentralizerBar z) = (e : CentralizerBar z) * l at h5
        rw [hab] at h5
        have hal' : a * l = l * a := (hcomm a ha l hl)
        have e1 : a * (b * l) = a * (l * b) := by
          calc a * (b * l) = a * b * l := by group
            _ = l * (a * b) := h5.symm
            _ = l * a * b := by group
            _ = a * l * b := by rw [hal']
            _ = a * (l * b) := by group
        exact mul_left_cancel e1
      have haA : a ∈ L₁ ⊓ L₂ := by
        rw [hS₁]
        refine ⟨⟨a, ha⟩, ?_, rfl⟩
        show (⟨a, ha⟩ : ↥L₁) ∈ center ↥L₁
        rw [Subgroup.mem_center_iff]
        intro g
        exact Subtype.ext (hal g g.2).symm
      have hbA : b ∈ L₁ ⊓ L₂ := by
        rw [hS₂]
        refine ⟨⟨b, hb⟩, ?_, rfl⟩
        show (⟨b, hb⟩ : ↥L₂) ∈ center ↥L₂
        rw [Subgroup.mem_center_iff]
        intro g
        exact Subtype.ext (hbl g g.2).symm
      rw [hab]
      exact (L₁ ⊓ L₂).mul_mem haA hbA
    have hinj : Function.Injective (fun x : ↥(center ↥(layer (CentralizerBar z))) =>
        (⟨((x : ↥(layer (CentralizerBar z))) : CentralizerBar z), hZ x x.2⟩ : ↥(L₁ ⊓ L₂))) := by
      intro x y hxy
      have h5 := Subtype.ext_iff.mp hxy
      exact Subtype.ext (Subtype.ext h5)
    have h6 := Nat.card_le_card_of_injective _ hinj
    rw [hcard] at h6
    exact h6

end Pair

end CFSG.GH74.GLS.Stage2.Final.L26
