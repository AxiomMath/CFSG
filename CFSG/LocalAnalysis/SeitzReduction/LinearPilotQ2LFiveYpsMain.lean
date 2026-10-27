module

public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotQ2LFiveYpsAut
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotQ2LFiveYpsChain

public section

namespace CFSG.SeitzReduction.LinearPilot

open Subgroup CFSG.Blueprint CFSG.LocalAnalysis.ComponentInitial LinearFlag
open scoped commutatorElement

theorem mem_uFiveRow_iff_lt {F : Type*} [Field F] [Finite F] {x : unitriangular 5 F} :
    x ∈ uFiveRow ↔ ∀ i j : Fin 5, 0 < i → i < j → ypsMat x i j = 0 := by
  rw [mem_uFiveRow_iff_row]
  exact ⟨fun h i j hi hij => h i j hi.ne' hij.ne,
    fun h i j hi hij => (lt_or_gt_of_ne hij).elim (h i j (Fin.pos_iff_ne_zero.2 hi))
      (fun hji => ypsMat_apply_of_lt x hji)⟩

@[expose] def LFiveFieldSylowModelInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G), SeitzSetting G L →
    ∀ (K : Type) [Field K] [CharP K 2], Nat.card K = 2 →
    ∀ (e : L ≃* LinearFlag.projectiveSL 5 K) (t : G), orderOf t = 2 →
      centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t →
      (∃ g ∈ centralizer ({t} : Set G), ∀ l ∈ L, ∃ x ∈ L, g * x * g⁻¹ ≠ l * x * l⁻¹) →
    ∀ (c : Fin 5) (W₁ : Subgroup G), Nat.card W₁ = 2 ^ 8 → (∀ w ∈ W₁, w * w = 1) →
      W₁ ⊓ centralizer ({t} : Set G) = modelToG e (pointRadical c) →
    ∀ htN : t ∈ normalizer (W₁ : Set G),
      modelToG e (blockSL (K := K) ({c}ᶜ : Finset (Fin 5))) ≤ normalizer (W₁ : Set G) →
    ∀ Kc : Subgroup (seitzHat W₁), IsFieldTypeComponentAtNOne e t c W₁ htN Kc →
    ∀ S₀ : Subgroup G, IsLFiveFieldSylow L t (seitzTilde W₁ Kc) S₀ →
      ∃ (F : Type) (_ : Field F) (_ : Fintype F) (_ : CharP F 2) (σ : F ≃+* F),
        Nat.card F = 4 ∧ σ ≠ RingEquiv.refl F ∧
        ∃ Θ : S₀ ≃* unitriangular 5 F, (∀ x : S₀, (x : G) ∈ W₁ ↔ Θ x ∈ uFiveRow) ∧
          ∀ x y : S₀, (y : G) = t * x * t⁻¹ → ypsMat (Θ y) = (ypsMat (Θ x)).map σ

section Transfer

variable {A B : Type*} [Group A] [Group B]

theorem map_map_mulEquiv_conj (Θ : A ≃* B) (H : Subgroup A) (φ : MulAut A) :
    (H.map φ.toMonoidHom).map Θ.toMonoidHom =
      (H.map Θ.toMonoidHom).map (Θ.symm.trans (φ.trans Θ)).toMonoidHom := by
  rw [Subgroup.map_map, Subgroup.map_map]
  congr 1
  ext x
  simp

theorem map_orbit_of_mulEquiv (Θ : A ≃* B) {H : Subgroup A} {K : Subgroup B}
    (hHK : H.map Θ.toMonoidHom = K)
    (horb : ∀ φ ψ : MulAut B, K.map φ.toMonoidHom = K ∨ K.map ψ.toMonoidHom = K ∨
      K.map φ.toMonoidHom = K.map ψ.toMonoidHom) (φ ψ : MulAut A) :
    H.map φ.toMonoidHom = H ∨ H.map ψ.toMonoidHom = H ∨
      H.map φ.toMonoidHom = H.map ψ.toMonoidHom := by
  have hinj := Subgroup.map_injective (f := Θ.toMonoidHom) Θ.injective
  have hφ := map_map_mulEquiv_conj Θ H φ
  have hψ := map_map_mulEquiv_conj Θ H ψ
  rw [hHK] at hφ hψ
  rcases horb (Θ.symm.trans (φ.trans Θ)) (Θ.symm.trans (ψ.trans Θ)) with h | h | h
  · exact Or.inl (hinj (by rw [hφ, h, hHK]))
  · exact Or.inr (Or.inl (hinj (by rw [hψ, h, hHK])))
  · exact Or.inr (Or.inr (hinj (by rw [hφ, hψ, h])))

end Transfer

theorem map_subgroupOf_eq_uFiveRow {G : Type*} [Group G] {F : Type*} [Field F] [Finite F]
    {S₀ W₁ : Subgroup G} (Θ : S₀ ≃* unitriangular 5 F)
    (hΘW : ∀ x : S₀, (x : G) ∈ W₁ ↔ Θ x ∈ uFiveRow) :
    (W₁.subgroupOf S₀).map Θ.toMonoidHom = uFiveRow := by
  ext u
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact (hΘW x).1 hx
  · intro hu
    refine ⟨Θ.symm u, (hΘW _).2 ?_, by simp⟩
    rw [MulEquiv.apply_symm_apply]
    exact hu

theorem lFiveFieldSylowRadicalInput_of_model (h : LFiveFieldSylowModelInput) :
    LFiveFieldSylowRadicalInput := by
  intro G _ _ L hset K _ _ hK e t ht hKt hgraph c W₁ hW₁c hW₁2 hW₁t htN hLN Kc hfield S₀ hS₀
  obtain ⟨F, _, _, _, σ, hF, -, Θ, hΘW, -⟩ :=
    h G L hset K hK e t ht hKt hgraph c W₁ hW₁c hW₁2 hW₁t htN hLN Kc hfield S₀ hS₀
  exact map_orbit_of_mulEquiv Θ (map_subgroupOf_eq_uFiveRow Θ hΘW) (map_uFiveRow_orbit hF)

theorem commutatorElement_mem_of_eq_mul {H : Type*} [Group H] {N : Subgroup H} (hN : N.Normal)
    {a b s₁ s₂ w₁ w₂ : H} (hs₁ : s₁ ∈ N) (hs₂ : s₂ ∈ N) (ha : a = s₁ * w₁) (hb : b = s₂ * w₂)
    (hw : w₁ * w₂ = w₂ * w₁) : ⁅a, b⁆ ∈ N := by
  have e : ⁅a, b⁆ = s₁ * (w₁ * s₂ * w₁⁻¹) * ((w₁ * w₂) * (w₂ * w₁)⁻¹) * (w₂ * s₁⁻¹ * w₂⁻¹) *
      s₂⁻¹ := by
    rw [ha, hb, commutatorElement_def]
    group
  rw [e, hw, mul_inv_cancel, mul_one]
  exact mul_mem (mul_mem (mul_mem hs₁ (hN.conj_mem _ hs₂ _)) (hN.conj_mem _ (inv_mem hs₁) _))
    (inv_mem hs₂)

theorem lFiveGraphSylowChainInput_of_model
    (h : LFiveFieldSylowModelInput) :
    LFiveGraphSylowChainInput := by
  intro G _ _ L hset K _ _ hK e t ht hKt hgraph c W₁ hW₁c hW₁2 hW₁t htN hLN Kc hfield S₀ d hS₀
    hdata
  obtain ⟨F, _, _, _, σ, hF, hσ, Θ, hΘW, hΘt⟩ :=
    h G L hset K hK e t ht hKt hgraph c W₁ hW₁c hW₁2 hW₁t htN hLN Kc hfield S₀ hS₀
  obtain ⟨hW₁S₀, -, hdW⟩ :=
    graphSylowData_wOne_facts hset hK e ht hKt c hW₁c hW₁2 hW₁t htN hLN hfield hdata
  obtain ⟨-, -, -, htS₀, hdS₀, hdt, hdd, -⟩ := hdata
  have ht2 : t * t = 1 := by rw [← sq, ← ht, pow_orderOf_eq_one]
  obtain ⟨ω, hω⟩ : ∃ ω : F, σ ω ≠ ω := by
    by_contra hh
    push Not at hh
    exact hσ (RingEquiv.ext hh)
  set S : Subgroup G := S₀ ⊔ zpowers d ⊔ zpowers t with hSdef
  have hS₀S : S₀ ≤ S := le_sup_left.trans le_sup_left
  have hdS : d ∈ S := mem_sup_left (mem_sup_right (mem_zpowers d))
  have htS : t ∈ S := mem_sup_right (mem_zpowers t)
  have hSN : S ≤ normalizer (S₀ : Set G) :=
    sup_le (sup_le le_normalizer (zpowers_le.2 hdS₀)) (zpowers_le.2 htS₀)
  have : (S₀.subgroupOf S).Normal := (normal_subgroupOf_iff_le_normalizer hS₀S).2 hSN
  let Θ' : S₀.subgroupOf S ≃* unitriangular 5 F := (subgroupOfEquivOfLe hS₀S).trans Θ
  have hΘ' : ∀ x : S₀.subgroupOf S, Θ' x = Θ ⟨((x : S) : G), x.2⟩ := fun _ => rfl
  let δ : MulAut (unitriangular 5 F) :=
    Θ.symm.trans ((S₀.normalizerMonoidHom ⟨d, hdS₀⟩).trans Θ)
  have hδ : ∀ (x : S₀) (hx : d * (x : G) * d⁻¹ ∈ S₀), δ (Θ x) = Θ ⟨_, hx⟩ := by
    intro x hx
    change Θ ((S₀.normalizerMonoidHom ⟨d, hdS₀⟩) (Θ.symm (Θ x))) = _
    rw [MulEquiv.symm_apply_apply]
    congr 1
  have hδcol : (uFiveRow (F := F)).map δ.toMonoidHom = uFiveCol := by
    rcases map_uFiveRow_eq_or hF δ with h1 | h1
    · exfalso
      apply hdW
      refine mem_normalizer_of_conj_into_self fun w hw => ?_
      have hx : d * w * d⁻¹ ∈ S₀ := (mem_normalizer_iff.1 hdS₀ w).1 (hW₁S₀ hw)
      have h2 : δ (Θ ⟨w, hW₁S₀ hw⟩) ∈ uFiveRow := by
        rw [← h1]
        exact ⟨_, (hΘW ⟨w, hW₁S₀ hw⟩).1 hw, rfl⟩
      rw [hδ ⟨w, hW₁S₀ hw⟩ hx] at h2
      exact (hΘW ⟨_, hx⟩).2 h2
    · exact h1
  set t' : S := ⟨t, htS⟩
  set d' : S := ⟨d, hdS⟩
  have hdt' : d' * t' = t' * d' := Subtype.ext hdt
  have hcos : ∀ x : S, x ∈ S₀.subgroupOf S ∨ ∃ s ∈ S₀.subgroupOf S,
      x = s * t' ∨ x = s * d' ∨ x = s * (d' * t') := by
    intro x
    rcases mem_or_of_mem_sup_zpowers_sup_zpowers htS₀ hdS₀ hdt hdd ht2 x.2 with h1 | h1 | h1 | h1
    · exact Or.inl (mem_subgroupOf.2 h1)
    · refine Or.inr ⟨x * t', mem_subgroupOf.2 h1, Or.inl (Subtype.ext ?_)⟩
      change (x : G) = x * t * t
      rw [mul_assoc, ht2, mul_one]
    · refine Or.inr ⟨x * d'⁻¹, mem_subgroupOf.2 ?_, Or.inr (Or.inl (by group))⟩
      have h2 : ((x * d'⁻¹ : S) : G) = (x * d) * (d * d)⁻¹ := by
        change (x : G) * d⁻¹ = _
        group
      rw [h2]
      exact mul_mem h1 (inv_mem hdd)
    · refine Or.inr ⟨x * (d' * t')⁻¹, mem_subgroupOf.2 ?_, Or.inr (Or.inr (by group))⟩
      have h2 : ((x * (d' * t')⁻¹ : S) : G) = (x * (d * t)) * (d * d)⁻¹ := by
        change (x : G) * (d * t)⁻¹ = _
        have h3 : (d * t)⁻¹ = (d * t) * (d * d)⁻¹ := by
          rw [eq_mul_inv_iff_mul_eq, inv_mul_eq_iff_eq_mul]
          calc d * d = d * d * (t * t) := by rw [ht2, mul_one]
            _ = d * t * (d * t) := by rw [mul_assoc d t, ← mul_assoc t d t, ← hdt]; group
        rw [h3]
        group
      rw [h2]
      exact mul_mem h1 (inv_mem hdd)
  have hrep : ∀ x : S, ∃ s ∈ S₀.subgroupOf S, ∃ w : S,
      (w = 1 ∨ w = t' ∨ w = d' ∨ w = d' * t') ∧ x = s * w := by
    intro x
    rcases hcos x with h1 | ⟨s, hs, h1 | h1 | h1⟩
    · exact ⟨x, h1, 1, Or.inl rfl, (mul_one x).symm⟩
    · exact ⟨s, hs, t', Or.inr (Or.inl rfl), h1⟩
    · exact ⟨s, hs, d', Or.inr (Or.inr (Or.inl rfl)), h1⟩
    · exact ⟨s, hs, d' * t', Or.inr (Or.inr (Or.inr rfl)), h1⟩
  have hcw : ∀ w w' : S, (w = 1 ∨ w = t' ∨ w = d' ∨ w = d' * t') →
      (w' = 1 ∨ w' = t' ∨ w' = d' ∨ w' = d' * t') → w * w' = w' * w := by
    have hc : Commute d' t' := hdt'
    intro w w' hw hw'
    rcases hw with rfl | rfl | rfl | rfl <;> rcases hw' with rfl | rfl | rfl | rfl
    all_goals first
      | exact (Commute.one_left _).eq
      | exact (Commute.one_right _).eq
      | rfl
      | exact hc.eq
      | exact hc.symm.eq
      | exact (hc.symm.mul_right (Commute.refl t')).eq
      | exact ((Commute.refl d').mul_right hc).eq
      | exact (hc.mul_left (Commute.refl t')).eq
      | exact ((Commute.refl d').mul_left hc.symm).eq
  have hcomm : commutator S ≤ S₀.subgroupOf S := by
    rw [_root_.commutator, Subgroup.commutator_le]
    intro a _ b _
    obtain ⟨s₁, hs₁, w₁, hw₁, ha⟩ := hrep a
    obtain ⟨s₂, hs₂, w₂, hw₂, hb⟩ := hrep b
    exact commutatorElement_mem_of_eq_mul inferInstance hs₁ hs₂ ha hb (hcw w₁ w₂ hw₁ hw₂)
  have ht' : ∀ x y : S₀.subgroupOf S, ((y : S) : S) = t' * x * t'⁻¹ →
      ypsMat (Θ' y) = (ypsMat (Θ' x)).map σ := by
    intro x y hxy
    rw [hΘ', hΘ']
    exact hΘt _ _ (congrArg Subtype.val hxy)
  have hd' : ∀ x y : S₀.subgroupOf S, ((y : S) : S) = d' * x * d'⁻¹ → Θ' x ∈ uFiveRow →
      Θ' y ∈ uFiveCol := by
    intro x y hxy hx
    rw [hΘ'] at hx ⊢
    have hyG : ((y : S) : G) = d * ((x : S) : G) * d⁻¹ := congrArg Subtype.val hxy
    have hx' : d * ((x : S) : G) * d⁻¹ ∈ S₀ := hyG ▸ y.2
    rw [← hδcol]
    refine ⟨Θ ⟨((x : S) : G), x.2⟩, hx, ?_⟩
    change δ (Θ ⟨((x : S) : G), x.2⟩) = _
    rw [hδ _ hx']
    congr 1
    exact Subtype.ext hyG.symm
  exact (seitzChain_four_eq_of_model Θ' σ hω hcos hcomm ht' hd').symm

end CFSG.SeitzReduction.LinearPilot
