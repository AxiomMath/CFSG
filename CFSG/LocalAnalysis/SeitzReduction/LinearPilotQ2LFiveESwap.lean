module

public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotQ2SixWSwap

public section

namespace CFSG.SeitzReduction.LinearPilot

open Subgroup CFSG.Blueprint CFSG.LocalAnalysis.ComponentInitial
open CFSG.SeitzReduction.F4Pilot (centralizerPerfectCore OddSchurTrivial oddCoreLift)

@[expose] def LFiveFieldNOneLiftInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G), SeitzSetting G L →
    ∀ (K : Type) [Field K] [CharP K 2], Nat.card K = 2 →
    ∀ (e : L ≃* LinearFlag.projectiveSL 5 K) (t : G), orderOf t = 2 →
      centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t →
    ∀ (c : Fin 5) (W₁ : Subgroup G), Nat.card W₁ = 2 ^ 8 → (∀ w ∈ W₁, w * w = 1) →
      W₁ ⊓ centralizer ({t} : Set G) = modelToG e (pointRadical c) →
      t ∈ normalizer (W₁ : Set G) →
      modelToG e (blockSL (K := K) ({c}ᶜ : Finset (Fin 5))) ≤ normalizer (W₁ : Set G) →
    ∀ Ks : Subgroup (seitzBar W₁), IsComponent Ks → LieModel Ks .PSL 4 2 2 →
      ((modelToG e (blockSL (K := K) ({c}ᶜ : Finset (Fin 5)))).subgroupOf
          (normalizer (W₁ : Set G))).map
        (QuotientGroup.mk' (W₁.subgroupOf (normalizer (W₁ : Set G)))) ≤ Ks →
    ∀ (a b : Fin 5), a ≠ b → c ≠ a → c ≠ b → ∀ X₀ : Subgroup (LinearFlag.projectiveSL 5 K),
      X₀ ≤ rootSL2 a b → Nat.card X₀ = Nat.card K + 1 →
      ∃ P : Subgroup G, P ≤ centralizer (modelToG e X₀ : Set G) ∧ ⁅P, P⁆ = P ∧ 5 ∣ Nat.card P

@[expose] def LFiveSwapNOneHyp (G : Type) [Group G] (L : Subgroup G) (K : Type) [Field K]
    (t : G) : Prop :=
  ∀ e' : L ≃* LinearFlag.projectiveSL 5 K,
    (∀ (a b : Fin 5) (_ : a ≠ b) (X₀ : Subgroup (LinearFlag.projectiveSL 5 K)),
      X₀ ≤ rootSL2 a b → Nat.card X₀ = Nat.card K + 1 →
      ∀ htX : t ∈ centralizer (modelToG e' X₀ : Set G), LinearTwoSwapKindAt e' t a b X₀ htX) →
    ∀ c : Fin 5, ∃ W₁ : Subgroup G, Nat.card W₁ = 2 ^ 8 ∧ (∀ w ∈ W₁, w * w = 1) ∧
      W₁ ⊓ centralizer ({t} : Set G) = modelToG e' (pointRadical c) ∧
      ∃ htN : t ∈ normalizer (W₁ : Set G),
        modelToG e' (blockSL (K := K) ({c}ᶜ : Finset (Fin 5))) ≤ normalizer (W₁ : Set G) ∧
        LinearTwoSwapTypeAtNOne e' t c W₁ htN

@[expose] def LFiveSwapGOneInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G), SeitzSetting G L →
    ∀ (K : Type) [Field K] [CharP K 2], Nat.card K = 2 → ∀ (t : G), orderOf t = 2 →
      centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t →
      LFiveSwapNOneHyp G L K t →
      ∀ e : L ≃* LinearFlag.projectiveSL 5 K,
        (∀ (a b : Fin 5) (_ : a ≠ b) (X₀ : Subgroup (LinearFlag.projectiveSL 5 K)),
          X₀ ≤ rootSL2 a b → Nat.card X₀ = Nat.card K + 1 →
          ∀ htX : t ∈ centralizer (modelToG e X₀ : Set G), LinearTwoSwapKindAt e t a b X₀ htX) →
        ∃ G₁ : Subgroup G, ⁅G₁, G₁⁆ = G₁ ∧
          G₁.map (MulAut.conj t).toMonoidHom ≤ centralizer (G₁ : Set G) ∧
          (∀ x ∈ G₁, x * (t * x * t⁻¹) ∈ L) ∧ ∀ y ∈ L, ∃ x ∈ G₁, x * (t * x * t⁻¹) = y

section Diagonal

variable {G : Type} [Group G] {L : Subgroup G}

theorem modelToG_blockSL_compl_sup_eq {n : ℕ} (hn : 3 ≤ n) {K : Type} [Field K]
    (e : L ≃* LinearFlag.projectiveSL n K) {c₁ c₂ : Fin n} (hc : c₁ ≠ c₂) :
    modelToG e (blockSL (K := K) ({c₁}ᶜ : Finset (Fin n))) ⊔
      modelToG e (blockSL (K := K) ({c₂}ᶜ : Finset (Fin n))) = L := by
  obtain ⟨x, hx1, hx2⟩ : ∃ x : Fin n, x ≠ c₁ ∧ x ≠ c₂ := by
    by_contra h
    push Not at h
    have hsub : (Finset.univ : Finset (Fin n)) ⊆ {c₁, c₂} := fun y _ => by
      by_cases h1 : y = c₁
      · simp [h1]
      · simp [h y h1]
    have h2 := (Finset.card_le_card hsub).trans (Finset.card_insert_le _ _)
    rw [Finset.card_univ, Fintype.card_fin, Finset.card_singleton] at h2
    omega
  have hu : ({c₁}ᶜ : Finset (Fin n)) ∪ {c₂}ᶜ = Finset.univ := by
    ext y
    simp only [Finset.mem_union, Finset.mem_compl, Finset.mem_singleton, Finset.mem_univ,
      iff_true]
    by_contra h
    push Not at h
    exact hc (h.1.symm.trans h.2)
  have hle := blockSL_union_le_sup (K := K) (A := ({c₁}ᶜ : Finset (Fin n))) (B := {c₂}ᶜ)
    (x := x) (by simpa using hx1) (by simpa using hx2)
  rw [hu, blockSL_univ] at hle
  refine le_antisymm (sup_le (modelToG_le e _) (modelToG_le e _)) ?_
  calc L = modelToG e (⊤ : Subgroup (LinearFlag.projectiveSL n K)) := (modelToG_top e).symm
    _ ≤ modelToG e (blockSL (K := K) ({c₁}ᶜ : Finset (Fin n)) ⊔
          blockSL (K := K) ({c₂}ᶜ : Finset (Fin n))) := modelToG_mono e hle
    _ = _ := by simp only [modelToG, Subgroup.map_sup]

theorem exists_gOne_of_firstFactors {n : ℕ} (hn : 3 ≤ n) {K : Type} [Field K]
    (hL : IsSimpleGroup L) (e : L ≃* LinearFlag.projectiveSL n K) {t : G} {c : Fin 2 → Fin n}
    (hc : c 0 ≠ c 1) {F : Fin 2 → Subgroup G} (hperf : ∀ i, ⁅F i, F i⁆ = F i)
    (hcomm : ∀ i j, (F j).map (MulAut.conj t).toMonoidHom ≤ centralizer (F i : Set G))
    (hδ : ∀ i, ∀ x ∈ F i, x * (t * x * t⁻¹) ∈
      modelToG e (blockSL (K := K) ({c i}ᶜ : Finset (Fin n))))
    (hsurj : ∀ i, ∀ y ∈ modelToG e (blockSL (K := K) ({c i}ᶜ : Finset (Fin n))),
      ∃ x ∈ F i, x * (t * x * t⁻¹) = y) :
    ∃ G₁ : Subgroup G, ⁅G₁, G₁⁆ = G₁ ∧
      G₁.map (MulAut.conj t).toMonoidHom ≤ centralizer (G₁ : Set G) ∧
      (∀ x ∈ G₁, x * (t * x * t⁻¹) ∈ L) ∧ ∀ y ∈ L, ∃ x ∈ G₁, x * (t * x * t⁻¹) = y := by
  have hgen : ⨆ i, modelToG e (blockSL (K := K) ({c i}ᶜ : Finset (Fin n))) = L := by
    refine le_antisymm (iSup_le fun i => modelToG_le e _) ?_
    refine (modelToG_blockSL_compl_sup_eq hn e hc).symm.le.trans (sup_le ?_ ?_)
    · exact le_iSup (fun i => modelToG e (blockSL (K := K) ({c i}ᶜ : Finset (Fin n)))) 0
    · exact le_iSup (fun i => modelToG e (blockSL (K := K) ({c i}ᶜ : Finset (Fin n)))) 1
  obtain ⟨-, h₁₂, hδL, hsurjL⟩ := SeitzQ2.isQuasisimple_iSup_of_diag hL F
    (fun i => modelToG e (blockSL (K := K) ({c i}ᶜ : Finset (Fin n)))) hcomm hperf hδ hsurj hgen
  exact ⟨⨆ i, F i, commutator_iSup_eq_of_forall F hperf, h₁₂, hδL, hsurjL⟩

end Diagonal

section Assembly

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

theorem exists_ne_ne_of_fin_five (c : Fin 5) : ∃ a b : Fin 5, a ≠ b ∧ c ≠ a ∧ c ≠ b := by
  revert c
  decide

omit [Finite G] in
theorem seitzLeviHat_eq_map_map {n : ℕ} {K : Type} [Field K]
    (e : L ≃* LinearFlag.projectiveSL n K) (c : Fin n) (W : Subgroup G) :
    seitzLeviHat e c W = (((modelToG e (blockSL (K := K) ({c}ᶜ : Finset (Fin n)))).subgroupOf
        (normalizer (W : Set G))).map
          (QuotientGroup.mk' (W.subgroupOf (normalizer (W : Set G))))).map
      (QuotientGroup.mk' (oddCore (seitzBar W))) := by
  rw [seitzLeviHat, Subgroup.map_map]
  rfl

end Assembly

end CFSG.SeitzReduction.LinearPilot
