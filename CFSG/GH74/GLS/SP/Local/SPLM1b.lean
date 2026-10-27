module

public import CFSG.GH74.GLS.SP.Local.SPLM1a

public section

namespace CFSG.GH74.GLS.SP.Local

open Subgroup CFSG CFSG.Blueprint CFSG.Assembly.LowTwoRank CFSG.GH74.GLS CFSG.GH74.BNPair
open CFSG.GH74.GLS.LU.Local CFSG.GH74.GLS.SP
open scoped Pointwise commutatorElement

variable {G : Type} [Group G]

section M1

variable [Finite G] (D : SPLNot3 G)

omit [Finite G] in
theorem mem_normalizer_of_conjBy_eq {g : G} {A : Subgroup G} (h : conjBy g A = A) :
    g ∈ normalizer (A : Set G) := by
  rw [mem_normalizer_iff]
  intro a
  rw [← mem_conjBy_iff, h]

omit [Finite G] in
theorem conjBy_t_X₂ (hs : SPLSetup D.toSPLNot0) : conjBy D.t D.X₂ = D.X₁ := by
  show conjBy D.t (conjBy D.t D.X₁) = D.X₁
  rw [conjBy_conjBy, t_mul_t D hs, conjBy_one']

omit [Finite G] in
theorem conjBy_t_R₁ (hs : SPLSetup D.toSPLNot0) (h3 : SPL3M2 D) : conjBy D.t D.R₁ = D.R₁ := by
  show conjBy D.t (D.X₁ ⊔ D.X₂ ⊔ D.X₃) = D.X₁ ⊔ D.X₂ ⊔ D.X₃
  unfold CFSG.GH74.BNPair.conjBy at *
  rw [Subgroup.map_sup, Subgroup.map_sup]
  have h1 : D.X₁.map (MulAut.conj D.t⁻¹).toMonoidHom = D.X₂ := rfl
  have h2 : D.X₂.map (MulAut.conj D.t⁻¹).toMonoidHom = D.X₁ := conjBy_t_X₂ D hs
  have h3' : D.X₃.map (MulAut.conj D.t⁻¹).toMonoidHom = D.X₃ := h3.t_X₃
  rw [h1, h2, h3', sup_comm D.X₂ D.X₁]

omit [Finite G] in
theorem t_mem_normalizer_R₁ (hs : SPLSetup D.toSPLNot0) (h3 : SPL3M2 D) :
    D.t ∈ normalizer (D.R₁ : Set G) :=
  mem_normalizer_of_conjBy_eq (conjBy_t_R₁ D hs h3)

theorem M₁_le_normalizer_R₁ (hs : SPLSetup D.toSPLNot0) (h1 : SPL2Set D.toSPLNot1) (h3 : SPL3M2 D) :
    D.M₁ ≤ normalizer (D.R₁ : Set G) := by
  refine sup_le (sup_le ?_ ?_) ?_
  · exact le_normalizer_of_normalizes (H_R₁ D hs h1 h3)
  · intro x hx
    apply mem_normalizer_of_conj_le
    intro r hr
    exact R₁_normal_P D hs h1 h3 x hx r hr
  · rw [zpowers_le]
    exact t_mem_normalizer_R₁ D hs h3

theorem B_coe_eq (hs : SPLSetup D.toSPLNot0) (h1 : SPL2Set D.toSPLNot1) (h3 : SPL3M2 D) :
    ((D.B : Subgroup G) : Set G) = (D.H : Set G) * (D.P : Set G) :=
  Subgroup.coe_mul_of_left_le_normalizer_right D.H D.P
    (le_normalizer_of_normalizes (H_P D hs h1 h3))

omit [Finite G] in
theorem H_le_B : D.H ≤ D.B := le_sup_left

omit [Finite G] in
theorem P_le_B : D.P ≤ D.B := le_sup_right

theorem t_B_t_mem (hs : SPLSetup D.toSPLNot0) (h1 : SPL2Set D.toSPLNot1) (h3 : SPL3M2 D)
    (hbru : ∀ y ∈ conjBy D.t D.X₄, y ≠ 1 →
      y ∈ (D.X₄ : Set G) * (D.H : Set G) * {D.t} * (D.X₄ : Set G)) :
    ∀ b ∈ D.B, D.t * b * D.t ∈ (D.B : Set G) ∪ (D.B : Set G) * {D.t} * (D.B : Set G) := by
  intro b hb
  have htt := t_mul_t D hs
  have htinv := t_inv D hs
  rw [← SetLike.mem_coe, B_coe_eq D hs h1 h3] at hb
  obtain ⟨h, hh, p, hp, rfl⟩ := hb
  obtain ⟨r, hr, x, hx, rfl⟩ := P_decomp' D hs h1 h3 p hp
  have e : D.t * (h * (r * x)) * D.t = (D.t * h * D.t) * (D.t * r * D.t) * (D.t * x * D.t) := by
    calc D.t * (h * (r * x)) * D.t = D.t * h * (D.t * D.t) * r * (D.t * D.t) * x * D.t := by
          rw [htt]; group
      _ = _ := by group
  have hh' : D.t * h * D.t ∈ D.H := by
    have := t_norm_H D hs h1 h hh
    rwa [htinv] at this
  have hr' : D.t * r * D.t ∈ D.R₁ := by
    have := (mem_normalizer_iff.mp (t_mem_normalizer_R₁ D hs h3) r).mp hr
    rwa [htinv] at this
  have hy : D.t * x * D.t ∈ conjBy D.t D.X₄ := by
    rw [mem_conjBy_iff, htinv]
    have : D.t * (D.t * x * D.t) * D.t = x := by
      calc D.t * (D.t * x * D.t) * D.t = (D.t * D.t) * x * (D.t * D.t) := by group
        _ = x := by rw [htt]; group
    rw [this]; exact hx
  have hBH : D.H ≤ D.B := H_le_B D
  have hBP : D.P ≤ D.B := P_le_B D
  by_cases hx1 : x = 1
  · left
    rw [e, hx1]
    have : D.t * (1 : G) * D.t = 1 := by rw [mul_one, htt]
    rw [this, mul_one]
    exact D.B.mul_mem (hBH hh') (hBP (D.R₁_le_P hr'))
  · right
    have hy1 : D.t * x * D.t ≠ 1 := by
      intro h'
      apply hx1
      calc x = D.t * (D.t * x * D.t) * D.t := by
            calc x = (D.t * D.t) * x * (D.t * D.t) := by rw [htt]; group
              _ = _ := by group
        _ = 1 := by rw [h', mul_one, htt]
    obtain ⟨_, ⟨_, ⟨a, ha, h', hh'', rfl⟩, tt, htt', rfl⟩, c, hc, hyc⟩ := hbru _ hy hy1
    have htt'' : tt = D.t := htt'
    subst htt''
    refine ⟨_, ⟨(D.t * h * D.t) * (D.t * r * D.t) * a * h', ?_, D.t, rfl, rfl⟩, c, ?_, ?_⟩
    · exact D.B.mul_mem (D.B.mul_mem (D.B.mul_mem (hBH hh') (hBP (D.R₁_le_P hr')))
        (hBP (D.X₄_le_P ha))) (hBH hh'')
    · exact hBP (D.X₄_le_P hc)
    · rw [e]
      have : (D.t * x * D.t) = a * h' * D.t * c := hyc.symm
      rw [this]
      group

theorem M₁_eq_union (hs : SPLSetup D.toSPLNot0) (h1 : SPL2Set D.toSPLNot1) (h3 : SPL3M2 D)
    (hbru : ∀ y ∈ conjBy D.t D.X₄, y ≠ 1 →
      y ∈ (D.X₄ : Set G) * (D.H : Set G) * {D.t} * (D.X₄ : Set G)) :
    (D.M₁ : Set G) = (D.B : Set G) ∪ (D.B : Set G) * {D.t} * (D.B : Set G) := by
  have hT := t_B_t_mem D hs h1 h3 hbru
  obtain ⟨S, hS⟩ : ∃ S : Set G, S = (D.B : Set G) ∪ (D.B : Set G) * {D.t} * (D.B : Set G) :=
    ⟨_, rfl⟩
  rw [← hS]
  have hBS : ∀ b ∈ D.B, ∀ s ∈ S, b * s ∈ S := by
    intro b hb s hs'
    rw [hS] at hs' ⊢
    rcases hs' with hs' | ⟨_, ⟨b₁, hb₁, tt, htt, rfl⟩, b₂, hb₂, rfl⟩
    · exact Or.inl (D.B.mul_mem hb hs')
    · right
      obtain rfl : tt = D.t := htt
      exact ⟨b * b₁ * D.t, ⟨b * b₁, D.B.mul_mem hb hb₁, D.t, rfl, rfl⟩, b₂, hb₂, by group⟩
  have htS : ∀ s ∈ S, D.t * s ∈ S := by
    intro s hs'
    rw [hS] at hs' ⊢
    rcases hs' with hs' | ⟨_, ⟨b₁, hb₁, tt, htt, rfl⟩, b₂, hb₂, rfl⟩
    · right
      exact ⟨1 * D.t, ⟨1, D.B.one_mem, D.t, rfl, rfl⟩, s, hs', by simp⟩
    · obtain rfl : tt = D.t := htt
      have hb := hT b₁ hb₁
      have e : D.t * (b₁ * D.t * b₂) = (D.t * b₁ * D.t) * b₂ := by group
      rw [e]
      rcases hb with hb | ⟨_, ⟨c₁, hc₁, t', ht', rfl⟩, c₂, hc₂, hc⟩
      · exact Or.inl (D.B.mul_mem hb hb₂)
      · right
        obtain rfl : t' = D.t := ht'
        rw [← hc]
        exact ⟨c₁ * D.t, ⟨c₁, hc₁, D.t, rfl, rfl⟩, c₂ * b₂, D.B.mul_mem hc₂ hb₂, by simp only [mul_assoc]⟩
  have hSfin : S.Finite := Set.toFinite S
  let K : Subgroup G :=
    { carrier := {g | ∀ s ∈ S, g * s ∈ S}
      mul_mem' := fun {a b} ha hb s hs' => by rw [mul_assoc]; exact ha _ (hb s hs')
      one_mem' := fun s hs' => by simpa using hs'
      inv_mem' := fun {g} hg => by
        intro s hs'
        have himg : (fun x => g * x) '' S ⊆ S := by
          rintro _ ⟨x, hx, rfl⟩; exact hg x hx
        have hcard : S.ncard ≤ ((fun x => g * x) '' S).ncard := by
          rw [Set.ncard_image_of_injective _ (mul_right_injective g)]
        have heq := Set.eq_of_subset_of_ncard_le himg hcard hSfin
        have : s ∈ (fun x => g * x) '' S := by rw [heq]; exact hs'
        obtain ⟨s', hs'', rfl⟩ := this
        simpa using hs'' }
  have hBK : D.B ≤ K := fun b hb s hs' => hBS b hb s hs'
  have htK : zpowers D.t ≤ K := by
    rw [zpowers_le]
    exact fun s hs' => htS s hs'
  apply Set.Subset.antisymm
  · intro g hg
    have hgK : g ∈ K := (sup_le hBK htK) hg
    have h1S : (1 : G) ∈ S := by rw [hS]; exact Or.inl D.B.one_mem
    simpa using hgK 1 h1S
  · intro g hg
    rw [hS] at hg
    rcases hg with hg | ⟨_, ⟨b₁, hb₁, tt, htt, rfl⟩, b₂, hb₂, rfl⟩
    · exact (le_sup_left : D.B ≤ D.M₁) hg
    · obtain rfl : tt = D.t := htt
      have hM : ∀ x ∈ D.B, x ∈ D.M₁ := fun x hx => (le_sup_left : D.B ≤ D.M₁) hx
      exact D.M₁.mul_mem (D.M₁.mul_mem (hM _ hb₁)
        ((le_sup_right : zpowers D.t ≤ D.M₁) (mem_zpowers _))) (hM _ hb₂)

end M1

end CFSG.GH74.GLS.SP.Local
