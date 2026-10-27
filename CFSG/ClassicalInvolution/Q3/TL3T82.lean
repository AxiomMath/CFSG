module

public import CFSG.ClassicalInvolution.Q3.TL3T71
public import CFSG.ClassicalInvolution.Q3.TL3T69

public section

namespace CFSG.ClassicalInvolution.Q3.AE

private theorem exists_alt_fix_escape {m : ℕ} {F β : Finset (Fin m)} (hFβ : Disjoint F β)
    (hβ : 2 ≤ β.card) (hF : (F ∪ β).card < m) :
    ∃ σ : alternatingGroup (Fin m), (∀ x ∈ F, (σ : Equiv.Perm (Fin m)) x = x) ∧
      (β ∪ β.map (σ : Equiv.Perm (Fin m)).toEmbedding).card ≤ β.card + 1 ∧
      β.map (σ : Equiv.Perm (Fin m)).toEmbedding ≠ β := by
  classical
  obtain ⟨w, hw⟩ : ∃ w : Fin m, w ∉ F ∪ β := by
    by_contra! h
    have h1 := Finset.card_le_card (show (Finset.univ : Finset (Fin m)) ⊆ F ∪ β from fun x _ => h x)
    rw [Finset.card_univ, Fintype.card_fin] at h1
    omega
  obtain ⟨b₁, hb₁, b₂, hb₂, hb₁₂⟩ := Finset.one_lt_card.mp (by omega : 1 < β.card)
  have hwβ : w ∉ β := fun h => hw (Finset.mem_union_right _ h)
  have hb₁w : b₁ ≠ w := fun h => hwβ (h ▸ hb₁)
  have hb₂w : b₂ ≠ w := fun h => hwβ (h ▸ hb₂)
  have hσw : (Equiv.swap b₁ b₂ * Equiv.swap b₂ w) b₂ = w := by
    show Equiv.swap b₁ b₂ (Equiv.swap b₂ w b₂) = w
    rw [Equiv.swap_apply_left, Equiv.swap_apply_of_ne_of_ne hb₁w.symm hb₂w.symm]
  have hsub : ∀ y ∈ β, (Equiv.swap b₁ b₂ * Equiv.swap b₂ w) y ∈ insert w β := by
    intro y hy
    show Equiv.swap b₁ b₂ (Equiv.swap b₂ w y) ∈ insert w β
    by_cases hy2 : y = b₂
    · rw [hy2, Equiv.swap_apply_left, Equiv.swap_apply_of_ne_of_ne hb₁w.symm hb₂w.symm]
      exact Finset.mem_insert_self _ _
    · have hyw : y ≠ w := fun h => hwβ (h ▸ hy)
      rw [Equiv.swap_apply_of_ne_of_ne hy2 hyw]
      refine Finset.mem_insert_of_mem ?_
      by_cases hy1 : y = b₁
      · rw [hy1, Equiv.swap_apply_left]
        exact hb₂
      · rw [Equiv.swap_apply_of_ne_of_ne hy1 hy2]
        exact hy
  refine ⟨⟨Equiv.swap b₁ b₂ * Equiv.swap b₂ w, ?_⟩, ?_, ?_, ?_⟩
  · rw [Equiv.Perm.mem_alternatingGroup, Equiv.Perm.sign_mul, Equiv.Perm.sign_swap hb₁₂,
      Equiv.Perm.sign_swap hb₂w]
    decide
  · intro x hx
    have hxb₁ : x ≠ b₁ := fun h => Finset.disjoint_left.mp hFβ hx (h ▸ hb₁)
    have hxb₂ : x ≠ b₂ := fun h => Finset.disjoint_left.mp hFβ hx (h ▸ hb₂)
    have hxw : x ≠ w := fun h => hw (Finset.mem_union_left _ (h ▸ hx))
    show Equiv.swap b₁ b₂ (Equiv.swap b₂ w x) = x
    rw [Equiv.swap_apply_of_ne_of_ne hxb₂ hxw, Equiv.swap_apply_of_ne_of_ne hxb₁ hxb₂]
  · refine (Finset.card_le_card (fun x hx => ?_)).trans (Finset.card_insert_le w β)
    rcases Finset.mem_union.mp hx with h | h
    · exact Finset.mem_insert_of_mem h
    · obtain ⟨y, hy, rfl⟩ := Finset.mem_map.mp h
      exact hsub y hy
  · intro h
    refine hwβ ?_
    rw [← h]
    exact Finset.mem_map.mpr ⟨b₂, hb₂, hσw⟩

end CFSG.ClassicalInvolution.Q3.AE

namespace CFSG.ClassicalInvolution.Q3.TC.Thin

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Q3.TC.Graph
open CFSG.ClassicalInvolution.Q3.AE CFSG.ClassicalInvolution.Q3.AE.Wr
open CFSG.ComponentClassification.PresentationLocal Amalg

section Assembly

variable {G : Type} [Group G] {m : ℕ}

structure LabHyp' (Ω : Set (Subgroup G)) (f : alternatingGroup (Fin m) →* G)
    (Ω₁ : Set (Subgroup G)) (lab₁ : Subgroup G → Subgroup (AEQ m)) (T : Finset (Fin m))
    (O : Set (Fin m)) : Prop where
  card_T : T.card = 2
  hm : 9 ≤ m
  sub : Ω₁ ⊆ Ω
  O_sub : O ⊆ (T : Set (Fin m))ᶜ
  O_four : ∃ α : Finset (Fin m), α.card = 4 ∧ (α : Set (Fin m)) ⊆ O
  inj : ∀ M ∈ Ω₁, ∀ M' ∈ Ω₁, lab₁ M = lab₁ M' → M = M'
  mem : ∀ M ∈ Ω₁, lab₁ M ∈ memLabelsOn ((T : Set (Fin m))ᶜ)
  surj : ∀ μ ∈ memLabelsOn ((T : Set (Fin m))ᶜ), ∃ M ∈ Ω₁, lab₁ M = μ
  conj : ∀ σ : alternatingGroup (Fin m), (∀ x ∈ T, (σ : Equiv.Perm (Fin m)) x = x) →
    ∀ M ∈ Ω₁, conjSub (f σ) M ∈ Ω₁ ∧ lab₁ (conjSub (f σ) M) = altAct σ (lab₁ M)
  loc : ∀ L ∈ Ω₁, ∀ l ∈ L, ∃ x ∈ lab₁ L, ∀ M' ∈ Ω₁, conjSub l M' ∈ Ω₁ ∧
    lab₁ (conjSub l M') = conjSub x (lab₁ M')
  cent : ∀ L ∈ Ω₁, ∀ (α : Finset (Fin m)) (hα : α.card = 4) (b : Bool), (α : Set (Fin m)) ⊆ O →
    lab₁ L = memBar α hα b → ∀ σ : alternatingGroup (Fin m),
      (∀ x ∈ α, (σ : Equiv.Perm (Fin m)) x = x) → ∀ l ∈ L, f σ * l = l * f σ

variable {Ω : Set (Subgroup G)} {f : alternatingGroup (Fin m) →* G} {Ω₁ : Set (Subgroup G)}
  {lab₁ : Subgroup G → Subgroup (AEQ m)} {T : Finset (Fin m)} {O : Set (Fin m)}

structure LabHyp'.Disj (H : LabHyp' Ω f Ω₁ lab₁ T O) : Prop where
  ex : ∃ (σ : alternatingGroup (Fin m)) (δ : Finset (Fin m)) (hδ : δ.card = 4) (N N' : Subgroup G),
    N ∈ Ω₁ ∧ N' ∈ Ω₁ ∧ lab₁ N = memBar δ hδ true ∧ lab₁ N' = memBar δ hδ false ∧
    T ⊆ δ.map (σ : Equiv.Perm (Fin m)).toEmbedding ∧
    ∀ P ∈ Ω₁, ∀ (β : Finset (Fin m)) (hβ : β.card = 4) (e : Bool), lab₁ P = memBar β hβ e →
      Disjoint β (δ.map (σ : Equiv.Perm (Fin m)).toEmbedding) →
      (∀ a ∈ conjSub (f σ) N, ∀ b ∈ P, a * b = b * a) ∧
      (∀ a ∈ conjSub (f σ) N', ∀ b ∈ P, a * b = b * a)

namespace LabHyp'

structure Base (H : LabHyp' Ω f Ω₁ lab₁ T O) where
  α₀ : Finset (Fin m)
  hα₀ : α₀.card = 4
  hα₀O : (α₀ : Set (Fin m)) ⊆ O
  M₀ : Subgroup G
  hM₀ : M₀ ∈ Ω₁
  hlab₀ : lab₁ M₀ = memBar α₀ hα₀ true

theorem nonempty_base (H : LabHyp' Ω f Ω₁ lab₁ T O) : Nonempty (Base H) := by
  obtain ⟨α₀, hα₀, hα₀O⟩ := H.O_four
  obtain ⟨M₀, hM₀, hlab₀⟩ := H.surj (memBar α₀ hα₀ true)
    ⟨α₀, hα₀, true, fun x hx => H.O_sub (hα₀O hx), rfl⟩
  exact ⟨⟨α₀, hα₀, hα₀O, M₀, hM₀, hlab₀⟩⟩

namespace Base

variable {H : LabHyp' Ω f Ω₁ lab₁ T O} (B : Base H)

@[expose] noncomputable def μ₀ : Subgroup (AEQ m) := memBar B.α₀ B.hα₀ true

theorem μ₀_mem : B.μ₀ ∈ memLabels m := memBar_mem_memLabels _ _ _

theorem μ₀_memOn : B.μ₀ ∈ memLabelsOn ((T : Set (Fin m))ᶜ) :=
  ⟨B.α₀, B.hα₀, true, fun x hx => H.O_sub (B.hα₀O hx), rfl⟩

theorem stab (σ : alternatingGroup (Fin m)) (hσ : altAct σ B.μ₀ = B.μ₀) :
    conjSub (f σ) B.M₀ = B.M₀ := by
  have hm := H.hm
  have hα₀map : B.α₀.map (σ : Equiv.Perm (Fin m)).toEmbedding = B.α₀ :=
    map_eq_of_permAct_memBar (by omega) hσ
  have hdisj : Disjoint B.α₀ T := by
    rw [Finset.disjoint_left]
    intro x hx hxT
    exact H.O_sub (B.hα₀O (Finset.mem_coe.mpr hx)) (Finset.mem_coe.mpr hxT)
  obtain ⟨τ, hτα, hτT⟩ := exists_alt_agree_fix (σ : Equiv.Perm (Fin m)) B.α₀ T hα₀map hdisj
    (by rw [B.hα₀, H.card_T]; omega)
  have hσ₂ : ∀ x ∈ B.α₀, ((τ⁻¹ * σ : alternatingGroup (Fin m)) : Equiv.Perm (Fin m)) x = x := by
    intro x hx
    show (τ : Equiv.Perm (Fin m))⁻¹ ((σ : Equiv.Perm (Fin m)) x) = x
    rw [Equiv.Perm.inv_eq_iff_eq, hτα x hx]
  have hcomm : conjSub (f (τ⁻¹ * σ)) B.M₀ = B.M₀ :=
    conjSub_eq_of_comm fun l hl =>
      H.cent B.M₀ B.hM₀ B.α₀ B.hα₀ true B.hα₀O B.hlab₀ (τ⁻¹ * σ) hσ₂ l hl
  obtain ⟨hτM, hτlab⟩ := H.conj τ hτT B.M₀ B.hM₀
  have hact : altAct τ B.μ₀ = B.μ₀ := by
    have h1 : altAct (τ⁻¹ * σ) B.μ₀ = B.μ₀ := permAct_eq_of_fix B.hα₀ true hσ₂
    have h2 : σ = τ * (τ⁻¹ * σ) := by rw [mul_inv_cancel_left]
    rw [h2, altAct_mul, h1] at hσ
    exact hσ
  have hτM₀ : conjSub (f τ) B.M₀ = B.M₀ :=
    H.inj _ hτM B.M₀ B.hM₀ (by rw [hτlab, B.hlab₀]; exact hact)
  have h3 : f σ = f τ * f (τ⁻¹ * σ) := by rw [← map_mul, mul_inv_cancel_left]
  rw [h3, conjSub_mul, hcomm, hτM₀]

@[expose] noncomputable def Λ (μ : Subgroup (AEQ m)) : Subgroup G := transMem f B.μ₀ B.M₀ μ

theorem Λ_altAct (σ : alternatingGroup (Fin m)) :
    B.Λ (altAct σ B.μ₀) = conjSub (f σ) B.M₀ := transMem_altAct B.stab σ

theorem Λ_μ₀ : B.Λ B.μ₀ = B.M₀ := by
  have := B.Λ_altAct 1
  rwa [altAct_one, map_one, conjSub_one] at this

theorem Λ_eqv (σ : alternatingGroup (Fin m)) {μ : Subgroup (AEQ m)} (hμ : μ ∈ memLabels m) :
    B.Λ (altAct σ μ) = conjSub (f σ) (B.Λ μ) := by
  have hm6 : 6 ≤ m := by have := H.hm; omega
  obtain ⟨σ', hσ'⟩ := exists_alt_permAct_eq hm6 B.μ₀_mem hμ
  have hσ'' : altAct σ' B.μ₀ = μ := hσ'
  subst hσ''
  rw [← altAct_mul, Λ_altAct, Λ_altAct, ← conjSub_mul, map_mul]

theorem Λ_mem (hΩ : ∀ L ∈ Ω, ∀ g : G, conjSub g L ∈ Ω) {μ : Subgroup (AEQ m)}
    (hμ : μ ∈ memLabels m) : B.Λ μ ∈ Ω := by
  have hm6 : 6 ≤ m := by have := H.hm; omega
  obtain ⟨σ, hσ⟩ := exists_alt_permAct_eq hm6 B.μ₀_mem hμ
  have hσ' : altAct σ B.μ₀ = μ := hσ
  subst hσ'
  rw [Λ_altAct]
  exact hΩ _ (H.sub B.hM₀) _

theorem Λ_spec₁ {μ : Subgroup (AEQ m)} (hμ : μ ∈ memLabelsOn ((T : Set (Fin m))ᶜ)) :
    B.Λ μ ∈ Ω₁ ∧ lab₁ (B.Λ μ) = μ := by
  have hm := H.hm
  obtain ⟨σ, hσT, hσ⟩ := exists_altFix_permAct_eq T (by rw [H.card_T]; omega) B.μ₀_memOn hμ
  have hσ' : altAct σ B.μ₀ = μ := hσ
  subst hσ'
  rw [Λ_altAct]
  obtain ⟨h1, h2⟩ := H.conj σ hσT B.M₀ B.hM₀
  exact ⟨h1, by rw [h2, B.hlab₀]; rfl⟩

theorem Λ_lab₁ {M : Subgroup G} (hM : M ∈ Ω₁) : B.Λ (lab₁ M) = M := by
  obtain ⟨h1, h2⟩ := B.Λ_spec₁ (H.mem M hM)
  exact H.inj _ h1 M hM h2

theorem Λ_injOn_room {α₁ α₂ : Finset (Fin m)} (h₁ : α₁.card = 4) (h₂ : α₂.card = 4)
    (b₁ b₂ : Bool) (hroom : (α₁ ∪ α₂).card + 2 ≤ m)
    (h : B.Λ (memBar α₁ h₁ b₁) = B.Λ (memBar α₂ h₂ b₂)) :
    memBar α₁ h₁ b₁ = memBar α₂ h₂ b₂ := by
  have hU : ((α₁ ∪ α₂) \ (∅ : Finset (Fin m))).card + (∅ : Finset (Fin m)).card + T.card ≤ m := by
    rw [Finset.sdiff_empty, Finset.card_empty, H.card_T]
    omega
  have hU' : ((∅ : Finset (Fin m)) ∪ (α₁ ∪ α₂)).card + 2 ≤ m := by
    rw [Finset.empty_union]
    exact hroom
  obtain ⟨σ, -, hσ⟩ := exists_alt_fix_avoid (∅ : Finset (Fin m)) (α₁ ∪ α₂) T
    (Finset.disjoint_empty_left _) hU hU'
  have hν₁ : altAct σ (memBar α₁ h₁ b₁) ∈ memLabelsOn ((T : Set (Fin m))ᶜ) :=
    permAct_mem_memLabelsOn _ b₁ fun x hx hxT =>
      hσ x (Finset.mem_union_left _ hx) (Finset.mem_coe.mp hxT)
  have hν₂ : altAct σ (memBar α₂ h₂ b₂) ∈ memLabelsOn ((T : Set (Fin m))ᶜ) :=
    permAct_mem_memLabelsOn _ b₂ fun x hx hxT =>
      hσ x (Finset.mem_union_right _ hx) (Finset.mem_coe.mp hxT)
  have e : B.Λ (altAct σ (memBar α₁ h₁ b₁)) = B.Λ (altAct σ (memBar α₂ h₂ b₂)) := by
    rw [B.Λ_eqv σ (memBar_mem_memLabels _ _ _), B.Λ_eqv σ (memBar_mem_memLabels _ _ _), h]
  have e1 := (B.Λ_spec₁ hν₁).2
  have e2 := (B.Λ_spec₁ hν₂).2
  have : altAct σ (memBar α₁ h₁ b₁) = altAct σ (memBar α₂ h₂ b₂) := by rw [← e1, ← e2, e]
  exact permAct_injective _ this

theorem Λ_ne_M₀ {β : Finset (Fin m)} (hβ : β.card = 4) (e : Bool) (hd : Disjoint B.α₀ β) :
    B.Λ (memBar β hβ e) ≠ B.M₀ := by
  intro h
  have hm := H.hm
  have hcard : (B.α₀ ∪ β).card < m := by
    have := Finset.card_union_le B.α₀ β
    rw [B.hα₀, hβ] at this
    omega
  obtain ⟨σ, hσα, hσc, hσne⟩ := exists_alt_fix_escape hd (by omega) hcard
  have hc : conjSub (f σ) B.M₀ = B.M₀ :=
    conjSub_eq_of_comm fun l hl =>
      H.cent B.M₀ B.hM₀ B.α₀ B.hα₀ true B.hα₀O B.hlab₀ σ hσα l hl
  obtain ⟨e', he'⟩ := permAct_memBar (σ : Equiv.Perm (Fin m)) β hβ e
  have hβσ : (β.map (σ : Equiv.Perm (Fin m)).toEmbedding).card = 4 := by
    rw [Finset.card_map]
    exact hβ
  have e2 : altAct σ (memBar β hβ e) =
      memBar (β.map (σ : Equiv.Perm (Fin m)).toEmbedding) hβσ e' := he'
  have h1 : B.Λ (memBar (β.map (σ : Equiv.Perm (Fin m)).toEmbedding) hβσ e') =
      B.Λ (memBar β hβ e) := by
    rw [← e2, B.Λ_eqv σ (memBar_mem_memLabels β hβ e), h, hc]
  have h3 := B.Λ_injOn_room hβσ hβ e' e (by rw [Finset.union_comm]; omega) h1
  exact hσne (eq_of_memBar_eq' (by omega) h3)

theorem Λ_ne_of_disjoint {α β : Finset (Fin m)} (hα : α.card = 4) (hβ : β.card = 4) (b e : Bool)
    (hd : Disjoint α β) : B.Λ (memBar α hα b) ≠ B.Λ (memBar β hβ e) := by
  intro h
  have hm6 : 6 ≤ m := by have := H.hm; omega
  obtain ⟨σ₁, hσ₁⟩ := exists_alt_permAct_eq hm6 (memBar_mem_memLabels α hα b) B.μ₀_mem
  have hσ₁' : altAct σ₁ (memBar α hα b) = B.μ₀ := hσ₁
  have hαmap : α.map (σ₁ : Equiv.Perm (Fin m)).toEmbedding = B.α₀ :=
    map_eq_of_permAct_memBar (by have := H.hm; omega) hσ₁
  obtain ⟨e', he'⟩ := permAct_memBar (σ₁ : Equiv.Perm (Fin m)) β hβ e
  have hβσ : (β.map (σ₁ : Equiv.Perm (Fin m)).toEmbedding).card = 4 := by
    rw [Finset.card_map]
    exact hβ
  have hdisj : Disjoint B.α₀ (β.map (σ₁ : Equiv.Perm (Fin m)).toEmbedding) := by
    rw [← hαmap]
    exact (Finset.disjoint_map _).mpr hd
  have e2 : altAct σ₁ (memBar β hβ e) =
      memBar (β.map (σ₁ : Equiv.Perm (Fin m)).toEmbedding) hβσ e' := he'
  refine B.Λ_ne_M₀ hβσ e' hdisj ?_
  rw [← e2, B.Λ_eqv σ₁ (memBar_mem_memLabels β hβ e), ← h,
    ← B.Λ_eqv σ₁ (memBar_mem_memLabels α hα b), hσ₁', B.Λ_μ₀]

theorem Λ_injOn' {μ₁ μ₂ : Subgroup (AEQ m)} (hμ₁ : μ₁ ∈ memLabels m) (hμ₂ : μ₂ ∈ memLabels m)
    (h : B.Λ μ₁ = B.Λ μ₂) : μ₁ = μ₂ := by
  obtain ⟨α₁, h₁, b₁, rfl⟩ := hμ₁
  obtain ⟨α₂, h₂, b₂, rfl⟩ := hμ₂
  by_cases hd : Disjoint α₁ α₂
  · exact absurd h (B.Λ_ne_of_disjoint h₁ h₂ b₁ b₂ hd)
  · refine B.Λ_injOn_room h₁ h₂ b₁ b₂ ?_ h
    have h1 := Finset.card_union_add_card_inter α₁ α₂
    have h2 : 0 < (α₁ ∩ α₂).card :=
      Finset.card_pos.mpr (Finset.not_disjoint_iff_nonempty_inter.mp hd)
    have := H.hm
    omega

theorem Λ_comm_of_disjoint (hD : H.Disj) {α β : Finset (Fin m)} (hα : α.card = 4)
    (hβ : β.card = 4) (b e : Bool) (hd : Disjoint α β) :
    ∀ x ∈ B.Λ (memBar α hα b), ∀ y ∈ B.Λ (memBar β hβ e), x * y = y * x := by
  obtain ⟨σ, δ, hδ, N, _, hN, -, hlN, -, hTδ, hcomm⟩ := hD.ex
  have hm := H.hm
  have hm6 : 6 ≤ m := by omega
  obtain ⟨b₁, hb₁⟩ := permAct_memBar (σ : Equiv.Perm (Fin m)) δ hδ true
  have hΛL : B.Λ (altAct σ (memBar δ hδ true)) = conjSub (f σ) N := by
    rw [B.Λ_eqv σ (memBar_mem_memLabels δ hδ true), ← hlN, B.Λ_lab₁ hN]
  obtain ⟨τ, hτ⟩ := exists_alt_permAct_eq hm6 (memBar_mem_memLabels α hα b)
    (permAct_mem_memLabels (σ : Equiv.Perm (Fin m)) (memBar_mem_memLabels δ hδ true))
  have hτ' : altAct τ (memBar α hα b) = altAct σ (memBar δ hδ true) := hτ
  have hτα : α.map (τ : Equiv.Perm (Fin m)).toEmbedding =
      δ.map (σ : Equiv.Perm (Fin m)).toEmbedding :=
    map_eq_of_permAct_memBar (by omega) (hτ.trans hb₁)
  obtain ⟨e', he'⟩ := permAct_memBar (τ : Equiv.Perm (Fin m)) β hβ e
  have hβτ : (β.map (τ : Equiv.Perm (Fin m)).toEmbedding).card = 4 := by
    rw [Finset.card_map]
    exact hβ
  have hdisjτ : Disjoint (β.map (τ : Equiv.Perm (Fin m)).toEmbedding)
      (δ.map (σ : Equiv.Perm (Fin m)).toEmbedding) := by
    rw [← hτα]
    exact (Finset.disjoint_map _).mpr hd.symm
  have hβT : ((β.map (τ : Equiv.Perm (Fin m)).toEmbedding : Finset (Fin m)) : Set (Fin m)) ⊆
      (T : Set (Fin m))ᶜ := fun x hx hxT =>
    Finset.disjoint_left.mp hdisjτ (Finset.mem_coe.mp hx) (hTδ (Finset.mem_coe.mp hxT))
  obtain ⟨hP₁, hP₂⟩ := B.Λ_spec₁ (μ := memBar (β.map (τ : Equiv.Perm (Fin m)).toEmbedding) hβτ e')
    ⟨_, hβτ, e', hβT, rfl⟩
  have hc := (hcomm _ hP₁ _ hβτ e' hP₂ hdisjτ).1
  have e2 : altAct τ (memBar β hβ e) =
      memBar (β.map (τ : Equiv.Perm (Fin m)).toEmbedding) hβτ e' := he'
  intro x hx y hy
  have hx' : f τ * x * (f τ)⁻¹ ∈ conjSub (f σ) N := by
    rw [← hΛL, ← hτ', B.Λ_eqv τ (memBar_mem_memLabels α hα b)]
    exact conj_mem_conjSub hx
  have hy' : f τ * y * (f τ)⁻¹ ∈
      B.Λ (memBar (β.map (τ : Equiv.Perm (Fin m)).toEmbedding) hβτ e') := by
    rw [← e2, B.Λ_eqv τ (memBar_mem_memLabels β hβ e)]
    exact conj_mem_conjSub hy
  have hxy := hc _ hx' _ hy'
  calc x * y = (f τ)⁻¹ * ((f τ * x * (f τ)⁻¹) * (f τ * y * (f τ)⁻¹)) * f τ := by group
    _ = (f τ)⁻¹ * ((f τ * y * (f τ)⁻¹) * (f τ * x * (f τ)⁻¹)) * f τ := by rw [hxy]
    _ = y * x := by group

theorem Λ_conj_base (hD : m = 9 → H.Disj) {l' : G} (hl' : l' ∈ B.M₀) {x' : AEQ m}
    (hx'M : x' ∈ B.μ₀)
    (hx' : ∀ M' ∈ Ω₁, conjSub l' M' ∈ Ω₁ ∧ lab₁ (conjSub l' M') = conjSub x' (lab₁ M'))
    {μ : Subgroup (AEQ m)} (hμ : μ ∈ memLabels m) :
    conjSub l' (B.Λ μ) = B.Λ (conjSub x' μ) := by
  have hm := H.hm
  obtain ⟨β, hβ, e, rfl⟩ := hμ
  by_cases hroom : (B.α₀ ∪ β).card + 2 ≤ m
  ·
    have hdisj : Disjoint B.α₀ T := by
      rw [Finset.disjoint_left]
      intro x hx hxT
      exact H.O_sub (B.hα₀O (Finset.mem_coe.mpr hx)) (Finset.mem_coe.mpr hxT)
    obtain ⟨σ, hσα, hσU⟩ := exists_alt_fix_avoid B.α₀ β T hdisj
      (by
        have h1 := Finset.card_sdiff_add_card β B.α₀
        rw [Finset.union_comm] at h1
        rw [H.card_T]
        omega)
      hroom
    have hν : altAct σ (memBar β hβ e) ∈ memLabelsOn ((T : Set (Fin m))ᶜ) :=
      permAct_mem_memLabelsOn _ e fun x hx hxT => hσU x hx (Finset.mem_coe.mp hxT)
    obtain ⟨hN₁, hN₂⟩ := B.Λ_spec₁ hν
    obtain ⟨hlN₁, hlN₂⟩ := hx' _ hN₁
    have hΛN : B.Λ (conjSub x' (altAct σ (memBar β hβ e))) =
        conjSub l' (B.Λ (altAct σ (memBar β hβ e))) := by
      have := B.Λ_lab₁ hlN₁
      rwa [hlN₂, hN₂] at this
    have hΛν : B.Λ (altAct σ (memBar β hβ e)) = conjSub (f σ) (B.Λ (memBar β hβ e)) :=
      B.Λ_eqv σ (memBar_mem_memLabels β hβ e)
    have hcommf : f σ * l' = l' * f σ :=
      H.cent B.M₀ B.hM₀ B.α₀ B.hα₀ true B.hα₀O B.hlab₀ σ hσα _ hl'
    have hcommP : mkQ m (ofPerm (σ : Equiv.Perm (Fin m))) * x' =
        x' * mkQ m (ofPerm (σ : Equiv.Perm (Fin m))) :=
      ofPerm_comm_memBar B.hα₀ true hσα x' hx'M
    have hx'ν : conjSub x' (altAct σ (memBar β hβ e)) =
        altAct σ (conjSub x' (memBar β hβ e)) :=
      conjSub_comm_conjSub hcommP.symm _
    have hΛ2 : B.Λ (altAct σ (conjSub x' (memBar β hβ e))) =
        conjSub (f σ) (B.Λ (conjSub x' (memBar β hβ e))) :=
      B.Λ_eqv σ (conjSub_mem_memLabels _ (memBar_mem_memLabels β hβ e))
    have h1 : conjSub (f σ) (conjSub l' (B.Λ (memBar β hβ e))) =
        conjSub (f σ) (B.Λ (conjSub x' (memBar β hβ e))) := by
      rw [← hΛ2, ← hx'ν, hΛN, hΛν, conjSub_comm_conjSub hcommf.symm]
    exact conjSub_injective (f σ) h1
  ·
    have hm9 : m = 9 := by
      have := Finset.card_union_le B.α₀ β
      rw [B.hα₀, hβ] at this
      omega
    have hdisj : Disjoint B.α₀ β := by
      have h1 := Finset.card_union_add_card_inter B.α₀ β
      rw [B.hα₀, hβ] at h1
      have h0 : (B.α₀ ∩ β).card = 0 := by omega
      exact Finset.disjoint_iff_inter_eq_empty.mpr (Finset.card_eq_zero.mp h0)
    have hl'' : l' ∈ B.Λ (memBar B.α₀ B.hα₀ true) := by
      have : B.Λ (memBar B.α₀ B.hα₀ true) = B.M₀ := B.Λ_μ₀
      rw [this]
      exact hl'
    have h1 : conjSub l' (B.Λ (memBar β hβ e)) = B.Λ (memBar β hβ e) :=
      conjSub_eq_of_comm fun s hs =>
        B.Λ_comm_of_disjoint (hD hm9) B.hα₀ hβ true e hdisj l' hl'' s hs
    have h2 : conjSub x' (memBar β hβ e) = memBar β hβ e :=
      conjSub_eq_of_comm fun s hs => comm_memBar_of_disjoint hdisj true e x' hx'M s hs
    rw [h1, h2]

theorem Λ_loc' (hD : m = 9 → H.Disj) {μ_L : Subgroup (AEQ m)} (hμ_L : μ_L ∈ memLabels m) {l : G}
    (hl : l ∈ B.Λ μ_L) :
    ∃ x ∈ μ_L, ∀ μ ∈ memLabels m, conjSub l (B.Λ μ) = B.Λ (conjSub x μ) := by
  have hm := H.hm
  have hm6 : 6 ≤ m := by omega
  obtain ⟨σ₀, hσ₀⟩ := exists_alt_permAct_eq hm6 hμ_L B.μ₀_mem
  have hσ₀' : altAct σ₀ μ_L = B.μ₀ := hσ₀
  have hLM : conjSub (f σ₀) (B.Λ μ_L) = B.M₀ := by
    rw [← B.Λ_eqv σ₀ hμ_L, hσ₀', B.Λ_μ₀]
  have hl' : f σ₀ * l * (f σ₀)⁻¹ ∈ B.M₀ := by
    rw [← hLM]
    exact conj_mem_conjSub hl
  obtain ⟨x', hx'M, hx'⟩ := H.loc B.M₀ B.hM₀ _ hl'
  rw [B.hlab₀] at hx'M
  have hx'P : x' ∈ conjSub (mkQ m (ofPerm (σ₀ : Equiv.Perm (Fin m)))) μ_L := by
    have : conjSub (mkQ m (ofPerm (σ₀ : Equiv.Perm (Fin m)))) μ_L = B.μ₀ := hσ₀'
    rw [this]
    exact hx'M
  refine ⟨(mkQ m (ofPerm (σ₀ : Equiv.Perm (Fin m))))⁻¹ * x' *
    mkQ m (ofPerm (σ₀ : Equiv.Perm (Fin m))), mem_conjSub_iff.mp hx'P, fun μ hμ => ?_⟩
  have hμ' : altAct σ₀ μ ∈ memLabels m := permAct_mem_memLabels _ hμ
  have hΛ1 : B.Λ (altAct σ₀ μ) = conjSub (f σ₀) (B.Λ μ) := B.Λ_eqv σ₀ hμ
  have h2 : conjSub (f σ₀ * l * (f σ₀)⁻¹) (conjSub (f σ₀) (B.Λ μ)) =
      B.Λ (conjSub x' (altAct σ₀ μ)) := by
    rw [← hΛ1]
    exact B.Λ_conj_base hD hl' hx'M hx' hμ'
  have h3 : conjSub x' (altAct σ₀ μ) = altAct σ₀
      (conjSub ((mkQ m (ofPerm (σ₀ : Equiv.Perm (Fin m))))⁻¹ * x' *
        mkQ m (ofPerm (σ₀ : Equiv.Perm (Fin m)))) μ) := by
    show conjSub x' (conjSub (mkQ m (ofPerm (σ₀ : Equiv.Perm (Fin m)))) μ) = _
    show _ = conjSub (mkQ m (ofPerm (σ₀ : Equiv.Perm (Fin m)))) _
    rw [← conjSub_mul, ← conjSub_mul]
    congr 1
    group
  calc conjSub l (B.Λ μ)
      = conjSub ((f σ₀)⁻¹ * (f σ₀ * l * (f σ₀)⁻¹) * f σ₀) (B.Λ μ) := by congr 1; group
    _ = conjSub (f σ₀)⁻¹ (conjSub (f σ₀ * l * (f σ₀)⁻¹) (conjSub (f σ₀) (B.Λ μ))) := by
        rw [conjSub_mul, conjSub_mul]
    _ = conjSub (f σ₀)⁻¹ (B.Λ (conjSub x' (altAct σ₀ μ))) := by rw [h2]
    _ = conjSub (f σ₀)⁻¹ (B.Λ (altAct σ₀ (conjSub ((mkQ m (ofPerm (σ₀ : Equiv.Perm (Fin m))))⁻¹ *
          x' * mkQ m (ofPerm (σ₀ : Equiv.Perm (Fin m)))) μ))) := by rw [h3]
    _ = conjSub (f σ₀)⁻¹ (conjSub (f σ₀)
          (B.Λ (conjSub ((mkQ m (ofPerm (σ₀ : Equiv.Perm (Fin m))))⁻¹ * x' *
            mkQ m (ofPerm (σ₀ : Equiv.Perm (Fin m)))) μ))) := by
        rw [B.Λ_eqv σ₀ (conjSub_mem_memLabels _ hμ)]
    _ = B.Λ (conjSub ((mkQ m (ofPerm (σ₀ : Equiv.Perm (Fin m))))⁻¹ * x' *
          mkQ m (ofPerm (σ₀ : Equiv.Perm (Fin m)))) μ) := conjSub_inv_conjSub _ _

end Base

theorem exists_labelling' (H : LabHyp' Ω f Ω₁ lab₁ T O) (hD : m = 9 → H.Disj)
    (hΩ : ∀ L ∈ Ω, ∀ g : G, conjSub g L ∈ Ω)
    (htrans : ∀ L ∈ Ω, ∀ L' ∈ Ω, ∃ g : G, conjSub g L = L')
    {P₁ P₂ : Set (Subgroup G)} (hP₁ : P₁ ⊆ Ω₁) (hgen : pSpan P₁ ⊔ pSpan P₂ = ⊤)
    (hP₂ : ∀ N ∈ P₂, ∃ σ : alternatingGroup (Fin m), ∃ M ∈ Ω₁, N = conjSub (f σ) M) :
    ∃ lab : Subgroup G → Subgroup (AEQ m),
      (∀ L ∈ Ω, ∃ (α : Finset (Fin m)) (h : α.card = 4) (b : Bool), lab L = memBar α h b) ∧
      (∀ L ∈ Ω, ∀ L' ∈ Ω, lab L = lab L' → L = L') ∧
      (∀ (α : Finset (Fin m)) (h : α.card = 4) (b : Bool), ∃ L ∈ Ω, lab L = memBar α h b) ∧
      (∀ L ∈ Ω, ∀ l ∈ L, ∃ x ∈ lab L, ActsBy Ω lab l x) := by
  classical
  obtain ⟨B⟩ := nonempty_base H
  set R : Set (Subgroup G) := {N | ∃ μ ∈ memLabels m, B.Λ μ = N} with hR
  have hRΩ : R ⊆ Ω := by
    rintro N ⟨μ, hμ, rfl⟩
    exact B.Λ_mem hΩ hμ
  have hΩ₁R : Ω₁ ⊆ R := fun M hM =>
    ⟨lab₁ M, memLabelsOn_subset _ (H.mem M hM), B.Λ_lab₁ hM⟩
  have hRf : ∀ σ : alternatingGroup (Fin m), ∀ N ∈ R, conjSub (f σ) N ∈ R := by
    rintro σ N ⟨μ, hμ, rfl⟩
    exact ⟨altAct σ μ, permAct_mem_memLabels _ hμ, B.Λ_eqv σ hμ⟩
  have hRloc : ∀ L ∈ R, ∀ l ∈ L, ∀ N ∈ R, conjSub l N ∈ R := by
    rintro L ⟨μ_L, hμ_L, rfl⟩ l hl N ⟨μ, hμ, rfl⟩
    obtain ⟨x, -, hx⟩ := B.Λ_loc' hD hμ_L hl
    exact ⟨conjSub x μ, conjSub_mem_memLabels _ hμ, (hx μ hμ).symm⟩
  have hP₂R : P₂ ⊆ R := by
    intro N hN
    obtain ⟨σ, M, hM, rfl⟩ := hP₂ N hN
    exact hRf σ M (hΩ₁R hM)
  let S : Subgroup G :=
    { carrier := {g | ∀ N ∈ R, conjSub g N ∈ R ∧ conjSub g⁻¹ N ∈ R}
      mul_mem' := fun {a b} ha hb N hN => by
        refine ⟨?_, ?_⟩
        · rw [conjSub_mul]
          exact (ha _ (hb N hN).1).1
        · rw [mul_inv_rev, conjSub_mul]
          exact (hb _ (ha N hN).2).2
      one_mem' := fun N hN => by
        refine ⟨?_, ?_⟩
        · rw [conjSub_one]
          exact hN
        · rw [inv_one, conjSub_one]
          exact hN
      inv_mem' := fun {a} ha N hN => by
        refine ⟨(ha N hN).2, ?_⟩
        rw [inv_inv]
        exact (ha N hN).1 }
  have hSR : ∀ L ∈ R, L ≤ S := by
    intro L hL l hl N hN
    exact ⟨hRloc L hL l hl N hN, hRloc L hL l⁻¹ (L.inv_mem hl) N hN⟩
  have hspan : pSpan R = ⊤ := by
    rw [eq_top_iff, ← hgen]
    exact sup_le (pSpan_le fun L hL => le_pSpan (hΩ₁R (hP₁ hL)))
      (pSpan_le fun L hL => le_pSpan (hP₂R hL))
  have hSall : ∀ g : G, g ∈ S := by
    intro g
    have : pSpan R ≤ S := pSpan_le hSR
    exact this (hspan ▸ Subgroup.mem_top g)
  have hΩR : Ω ⊆ R := by
    intro L hL
    obtain ⟨g, hg⟩ := htrans B.M₀ (H.sub B.hM₀) L hL
    rw [← hg]
    exact (hSall g _ (hΩ₁R B.hM₀)).1
  have hReq : ∀ L, L ∈ Ω → ∃ μ ∈ memLabels m, B.Λ μ = L := fun L hL => hΩR hL
  obtain ⟨lab, hlabdef⟩ : ∃ lab : Subgroup G → Subgroup (AEQ m),
      ∀ L, lab L = if h : ∃ μ ∈ memLabels m, B.Λ μ = L then h.choose else ⊥ := ⟨_, fun _ => rfl⟩
  have hlab_spec : ∀ L ∈ Ω, lab L ∈ memLabels m ∧ B.Λ (lab L) = L := by
    intro L hL
    have h := hReq L hL
    rw [hlabdef, dif_pos h]
    exact h.choose_spec
  have hlab_Λ : ∀ μ ∈ memLabels m, lab (B.Λ μ) = μ := by
    intro μ hμ
    obtain ⟨h1, h2⟩ := hlab_spec _ (B.Λ_mem hΩ hμ)
    exact B.Λ_injOn' h1 hμ h2
  refine ⟨lab, fun L hL => (hlab_spec L hL).1, fun L hL L' hL' h => ?_, fun α h b => ?_,
    fun L hL l hl => ?_⟩
  · rw [← (hlab_spec L hL).2, ← (hlab_spec L' hL').2, h]
  · exact ⟨B.Λ (memBar α h b), B.Λ_mem hΩ (memBar_mem_memLabels _ _ _),
      hlab_Λ _ (memBar_mem_memLabels _ _ _)⟩
  · obtain ⟨hμ_L, hLeq⟩ := hlab_spec L hL
    have hl' : l ∈ B.Λ (lab L) := by rw [hLeq]; exact hl
    obtain ⟨x, hx, hxμ⟩ := B.Λ_loc' hD hμ_L hl'
    refine ⟨x, hx, fun M hM => ?_⟩
    obtain ⟨hμM, hMeq⟩ := hlab_spec M hM
    have h1 : conjSub l (B.Λ (lab M)) = B.Λ (conjSub x (lab M)) := hxμ _ hμM
    rw [hMeq] at h1
    show lab (conjSub l M) = conjSub x (lab M)
    rw [h1]
    exact hlab_Λ _ (conjSub_mem_memLabels _ hμM)

end LabHyp'

end Assembly

end CFSG.ClassicalInvolution.Q3.TC.Thin
