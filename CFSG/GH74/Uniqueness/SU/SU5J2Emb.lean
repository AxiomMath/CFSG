module

public import CFSG.GH74.Uniqueness.SU.SU5L34
public import CFSG.GH74.Uniqueness.SU.SU5J2Sub

public section

namespace CFSG.GH74.Uniqueness.SU.SU5

open Subgroup CFSG.GH74.GLS.Bg.TwoGroups

namespace J2Syl

theorem range_inl : (SemidirectProduct.inl : L34Syl →* J2Syl).range = W := by
  ext s
  constructor
  · rintro ⟨g, rfl⟩
    exact rfl
  · intro hs
    exact ⟨s.left, SemidirectProduct.ext rfl (by simpa using hs.symm)⟩

theorem map_inl_A : L34Syl.A.map (SemidirectProduct.inl : L34Syl →* J2Syl) = A := by
  ext s
  constructor
  · rintro ⟨g, hg, rfl⟩
    exact ⟨rfl, hg⟩
  · intro hs
    exact ⟨s.left, hs.2, SemidirectProduct.ext rfl (by simpa using hs.1.symm)⟩

theorem map_inl_B : L34Syl.B.map (SemidirectProduct.inl : L34Syl →* J2Syl) = B := by
  ext s
  constructor
  · rintro ⟨g, hg, rfl⟩
    exact ⟨rfl, hg⟩
  · intro hs
    exact ⟨s.left, hs.2, SemidirectProduct.ext rfl (by simpa using hs.1.symm)⟩

theorem Zc_W : Zc W = U := by
  have h : ∀ s : J2Syl, (s.right = 1 ∧ ∀ h : J2Syl, h.right = 1 → s * h = h * s) ↔
      (s.right = 1 ∧ s.left.a = 0 ∧ s.left.b = 0) := by decide +kernel
  ext s
  rw [mem_Zc]
  exact h s

end J2Syl

section Emb

variable {G : Type*} [Group G]

@[expose] def J2Emb (S T : Subgroup G) (x : G) : Prop :=
  ∃ f : J2Syl →* G, Function.Injective f ∧ f.range = S ∧ J2Syl.W.map f = T ∧ f J2Syl.x0 = x

namespace J2Emb

variable {S T : Subgroup G} {x : G}

theorem card_S (h : J2Emb S T x) : Nat.card S = 128 := by
  obtain ⟨f, hf, rfl, -, -⟩ := h
  rw [card_range_of_injective hf, card_J2Syl]

theorem card_T (h : J2Emb S T x) : Nat.card T = 64 := by
  obtain ⟨f, hf, -, rfl, -⟩ := h
  rw [Subgroup.card_map_of_injective hf, J2Syl.card_W]

theorem T_le (h : J2Emb S T x) : T ≤ S := by
  obtain ⟨f, hf, rfl, rfl, -⟩ := h
  exact Subgroup.map_le_range f _

theorem x_mem (h : J2Emb S T x) : x ∈ S := by
  obtain ⟨f, hf, rfl, -, rfl⟩ := h
  exact ⟨_, rfl⟩

theorem x_not_mem (h : J2Emb S T x) : x ∉ T := by
  obtain ⟨f, hf, -, rfl, rfl⟩ := h
  rw [Subgroup.mem_map_iff_mem hf]
  exact J2Syl.x0_not_mem_W

theorem x_sq (h : J2Emb S T x) : x ^ 2 = 1 := by
  obtain ⟨f, hf, -, -, rfl⟩ := h
  rw [pow_two, ← map_mul, J2Syl.x0_sq, map_one]

theorem T_normal (h : J2Emb S T x) : ∀ s ∈ S, ∀ t ∈ T, s * t * s⁻¹ ∈ T := by
  obtain ⟨f, hf, rfl, rfl, -⟩ := h
  rintro _ ⟨m, rfl⟩ _ ⟨w, hw, rfl⟩
  exact ⟨m * w * m⁻¹, J2Syl.W_normal m w hw, by simp⟩

theorem S_cover (h : J2Emb S T x) : ∀ s ∈ S, s ∈ T ∨ x * s ∈ T := by
  obtain ⟨f, hf, rfl, rfl, rfl⟩ := h
  rintro _ ⟨m, rfl⟩
  rcases J2Syl.cover m with h1 | h1
  · exact Or.inl ⟨m, h1, rfl⟩
  · exact Or.inr ⟨J2Syl.x0 * m, h1, by simp⟩

theorem l34Emb (h : J2Emb S T x) : L34Emb T := by
  obtain ⟨f, hf, -, rfl, -⟩ := h
  refine ⟨f.comp SemidirectProduct.inl, hf.comp SemidirectProduct.inl_injective, ?_⟩
  rw [MonoidHom.range_comp, J2Syl.range_inl]

theorem isL34Type (h : J2Emb S T x) : IsL34Type T := isL34Type_iff_emb.2 h.l34Emb

theorem exists_AB (h : J2Emb S T x) : ∃ A B : Subgroup G, L34Facts T A B ∧
    A.map (MulAut.conj x).toMonoidHom = B ∧ (∀ E : Subgroup G, E ≤ S → IsE 4 E → E = A ∨ E = B) ∧
    (∀ E : Subgroup G, E ≤ S → Open.IsElemAbelian 2 E → Nat.card E ≤ 16) ∧
    (∀ a ∈ A, a ∉ B → ∀ g ∈ S, (g * a = a * g ↔ g ∈ A)) ∧
    (∀ b ∈ B, b ∉ A → ∀ g ∈ S, (g * b = b * g ↔ g ∈ B)) := by
  obtain ⟨f, hf, rfl, rfl, rfl⟩ := h
  refine ⟨J2Syl.A.map f, J2Syl.B.map f, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have hg : Function.Injective (f.comp SemidirectProduct.inl) :=
      hf.comp SemidirectProduct.inl_injective
    have h1 := L34Syl.facts_map hg
    rwa [MonoidHom.range_comp, J2Syl.range_inl, ← Subgroup.map_map, ← Subgroup.map_map,
      J2Syl.map_inl_A, J2Syl.map_inl_B] at h1
  · rw [Subgroup.map_map]
    have : (MulAut.conj (f J2Syl.x0)).toMonoidHom.comp f =
        f.comp (MulAut.conj J2Syl.x0).toMonoidHom := by
      ext m; simp [MulAut.conj_apply]
    rw [this, ← Subgroup.map_map, J2Syl.map_conj_A]
  · intro E hE hEE
    obtain ⟨X, rfl⟩ := exists_eq_map_of_le_range hE
    rcases J2Syl.isE4_unique X ((isE_map hf).1 hEE) with rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr rfl
  · intro E hE hEE
    obtain ⟨X, rfl⟩ := exists_eq_map_of_le_range hE
    rw [Subgroup.card_map_of_injective hf]
    exact J2Syl.card_le_16 X ((isElemAbelian_map_iff hf).1 hEE)
  · rintro _ ⟨a, ha, rfl⟩ hna _ ⟨k, rfl⟩
    have hna' : a ∉ J2Syl.B := fun hb => hna (Subgroup.mem_map_of_mem f hb)
    rw [← map_mul, ← map_mul, hf.eq_iff, Subgroup.mem_map_iff_mem hf]
    exact J2Syl.cent_A a k ha hna'
  · rintro _ ⟨b, hb, rfl⟩ hnb _ ⟨k, rfl⟩
    have hnb' : b ∉ J2Syl.A := fun ha => hnb (Subgroup.mem_map_of_mem f ha)
    rw [← map_mul, ← map_mul, hf.eq_iff, Subgroup.mem_map_iff_mem hf]
    exact J2Syl.cent_B b k hb hnb'

theorem pRank [Finite G] (h : J2Emb S T x) : Open.pRank 2 S = 4 := by
  obtain ⟨A, B, hAB, -, huniq, hle, -, -⟩ := h.exists_AB
  exact pRank_eq_of ⟨A, hAB.A_le.trans h.T_le, hAB.A_E⟩ (fun E hE hEE => by
    have := hle E hE hEE
    norm_num; exact this)

theorem E16_le_T (h : J2Emb S T x) (E : Subgroup G) (hE : E ≤ S) (hEE : IsE 4 E) : E ≤ T := by
  obtain ⟨A, B, hAB, -, huniq, -, -, -⟩ := h.exists_AB
  rcases huniq E hE hEE with rfl | rfl
  · exact hAB.A_le
  · exact hAB.B_le

theorem JE_eq (h : J2Emb S T x) : JE S = T := by
  obtain ⟨A, B, hAB, -, huniq, hle, -, -⟩ := h.exists_AB
  rw [JE_eq_sup (hA := hAB.A_le.trans h.T_le) (hB := hAB.B_le.trans h.T_le) hAB.A_E hAB.B_E
    (fun F hF hFE => (hle F hF hFE).trans (by norm_num)) huniq, hAB.sup_eq]

theorem center_S (h : J2Emb S T x) : ∃ z ∈ S, z ≠ 1 ∧ z ^ 2 = 1 ∧ z ∈ Zc T ∧
    ∀ y ∈ S, ((∀ s ∈ S, y * s = s * y) ↔ (y = 1 ∨ y = z)) := by
  obtain ⟨f, hf, rfl, rfl, rfl⟩ := h
  refine ⟨f J2Syl.z0, ⟨_, rfl⟩, ?_, ?_, ?_, ?_⟩
  · intro h1
    exact J2Syl.z0_ne_one (hf (by rw [h1, map_one]))
  · rw [pow_two, ← map_mul, J2Syl.z0_sq, map_one]
  · rw [Zc_map hf, J2Syl.Zc_W]
    exact Subgroup.mem_map_of_mem f J2Syl.z0_mem_U
  · rintro _ ⟨m, rfl⟩
    constructor
    · intro hc
      have h2 : ∀ t : J2Syl, m * t = t * m := fun t =>
        hf (by rw [map_mul, map_mul]; exact hc (f t) ⟨t, rfl⟩)
      rcases (J2Syl.center_iff m).1 h2 with h3 | h3
      · left; rw [h3, map_one]
      · right; rw [h3]
    · rintro (h1 | h1) _ ⟨t, rfl⟩
      · have : m = 1 := hf (by rw [h1, map_one])
        rw [this]; simp
      · have : m = J2Syl.z0 := hf h1
        rw [this]
        have := (J2Syl.center_iff J2Syl.z0).2 (Or.inr rfl) t
        rw [← map_mul, ← map_mul, this]

theorem unique_normal_four (h : J2Emb S T x) : ∀ N : Subgroup G, N ≤ S →
    (∀ s ∈ S, ∀ n ∈ N, s * n * s⁻¹ ∈ N) → IsE 2 N → N = Zc T := by
  obtain ⟨f, hf, rfl, rfl, rfl⟩ := h
  intro N hNS hNn hNE
  obtain ⟨N₀, rfl⟩ := exists_eq_map_of_le_range hNS
  have hN₀ : N₀.Normal := ⟨fun n hn g => by
    have h1 := hNn (f g) ⟨g, rfl⟩ (f n) (Subgroup.mem_map_of_mem f hn)
    rw [← map_mul, ← map_inv, ← map_mul, Subgroup.mem_map_iff_mem hf] at h1
    exact h1⟩
  rw [Zc_map hf, J2Syl.Zc_W]
  exact congrArg (Subgroup.map f) (J2Syl.unique_normal_four N₀ hN₀ ((isE_map hf).1 hNE))

theorem conj_involutions (h : J2Emb S T x) :
    ∀ s ∈ S, s ∉ T → s ^ 2 = 1 → ∃ g ∈ S, g * x * g⁻¹ = s := by
  obtain ⟨f, hf, rfl, rfl, rfl⟩ := h
  rintro _ ⟨m, rfl⟩ hmT hm2
  have h1 : m.right ≠ 1 := fun h0 => hmT (Subgroup.mem_map_of_mem f h0)
  have h2 : m * m = 1 := hf (by rw [map_mul, map_one, ← pow_two]; exact hm2)
  obtain ⟨g, hg⟩ := J2Syl.conj_involutions m h1 h2
  exact ⟨f g, ⟨g, rfl⟩, by rw [← map_mul, ← map_inv, ← map_mul, hg]⟩

end J2Emb

end Emb

end CFSG.GH74.Uniqueness.SU.SU5
