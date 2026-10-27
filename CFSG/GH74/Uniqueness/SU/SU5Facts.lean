module

public import CFSG.GH74.Uniqueness.SU.SU5A8Emb
public import CFSG.GH74.Uniqueness.SU.SU5J2Emb3
public import CFSG.GH74.Uniqueness.SU.SU5J2Emb4

public section

namespace CFSG.GH74.Uniqueness.SU.SU5

open Subgroup CFSG.GH74.GLS.Bg.TwoGroups

variable {G : Type*} [Group G]

structure J2Facts (S T : Subgroup G) (x z : G) : Prop where
  T_le : T ≤ S
  x_mem : x ∈ S
  x_not_mem : x ∉ T
  x_sq : x ^ 2 = 1
  card_S : Nat.card S = 128
  card_T : Nat.card T = 64
  T_normal : ∀ s ∈ S, ∀ t ∈ T, s * t * s⁻¹ ∈ T
  S_cover : ∀ s ∈ S, s ∈ T ∨ x * s ∈ T
  T_L34 : IsL34Type T
  T_eq_J : JE S = T
  z_gen : IsZGen S z
  z_sq : z ^ 2 = 1
  z_mem : z ∈ Zc T
  AB : ∃ A B : Subgroup G, L34Facts T A B ∧ A.map (MulAut.conj x).toMonoidHom = B ∧
    (∀ E : Subgroup G, E ≤ S → IsE 4 E → E = A ∨ E = B) ∧
    (∀ E : Subgroup G, E ≤ S → Open.IsElemAbelian 2 E → Nat.card E ≤ 16) ∧
    (∀ a ∈ A, a ∉ B → ∀ g ∈ S, (g * a = a * g ↔ g ∈ A)) ∧
    (∀ b ∈ B, b ∉ A → ∀ g ∈ S, (g * b = b * g ↔ g ∈ B))
  U_unique : ∀ N : Subgroup G, N ≤ S → (∀ s ∈ S, ∀ n ∈ N, s * n * s⁻¹ ∈ N) → IsE 2 N → N = Zc T
  Q : Nonempty (↥(T ⊓ centralizer {x}) ≃* QuaternionGroup 2) ∧ z ∈ T ⊓ centralizer {x} ∧
    (∀ q ∈ T ⊓ centralizer {x}, ((∀ q' ∈ T ⊓ centralizer {x}, q * q' = q' * q) ↔
      (q = 1 ∨ q = z))) ∧
    S ⊓ centralizer {x} = zpowers x ⊔ (T ⊓ centralizer {x}) ∧
    zpowers x ⊓ (T ⊓ centralizer {x}) = ⊥ ∧ Nat.card ↥(S ⊓ centralizer {x}) = 16
  RV : ∃ R V : Subgroup G, R ≤ S ∧ V ≤ S ∧ (∀ s ∈ S, ∀ r ∈ R, s * r * s⁻¹ ∈ R) ∧ IsQ8D8 R ∧
    (∀ N : Subgroup G, N ≤ S → (∀ s ∈ S, ∀ n ∈ N, s * n * s⁻¹ ∈ N) → IsQ8D8 N → N = R) ∧
    R ⊔ V = S ∧ R ⊓ V = ⊥ ∧ IsE 2 V ∧ Nat.card R = 32 ∧ z ∈ R ∧
    (∀ s ∈ S, (s ∈ R ∧ s ≠ 1 ∧ s ^ 2 = 1) ↔
      ((s ∈ Zc T ∧ s ≠ 1) ∨ (s ∉ T ∧ s ^ 2 = 1))) ∧
    (∀ E : Subgroup G, E ≤ S → IsE 4 E → E ⊓ R = Zc T) ∧
    (∀ s ∈ S, s ^ 2 = z → s ∈ R) ∧
    (∀ s ∈ S, ((s ∈ R ∧ orderOf s = 4) ↔ (orderOf s = 4 ∧ s ^ 2 = z)))
  conj_invol : ∀ s ∈ S, s ∉ T → s ^ 2 = 1 → ∃ g ∈ S, g * x * g⁻¹ = s
  le4 : ∀ s ∈ S, s ∉ T → s ^ 2 = 1 →
    ∀ E : Subgroup G, E ≤ S ⊓ centralizer {s} → Open.IsElemAbelian 2 E → Nat.card E ≤ 4
  sq_z : ∀ s ∈ S, s ∉ T → s ^ 2 = 1 → ∀ M : Subgroup G, M ≤ S ⊓ centralizer {s} →
    5 ≤ Nat.card M → ∃ m ∈ M, m ^ 2 = z
  half_central : ∀ u ∈ Zc T, u ≠ 1 → u ≠ z → ∀ g ∈ S, (g * u = u * g ↔ g ∈ T)
  card_invol : {s : G | s ∈ S ∧ s ∉ T ∧ s ^ 2 = 1}.ncard = 8
  A8 : ∀ [((zpowers z).subgroupOf S).Normal], IsA8Type (↥S ⧸ (zpowers z).subgroupOf S)

namespace J2Emb

variable {S T : Subgroup G} {x : G}

theorem facts (h : J2Emb S T x) {z : G} (hz : IsZGen S z) : J2Facts S T x z where
  T_le := h.T_le
  x_mem := h.x_mem
  x_not_mem := h.x_not_mem
  x_sq := h.x_sq
  card_S := h.card_S
  card_T := h.card_T
  T_normal := h.T_normal
  S_cover := h.S_cover
  T_L34 := h.isL34Type
  T_eq_J := h.JE_eq
  z_gen := hz
  z_sq := (h.zgen_facts hz).1
  z_mem := (h.zgen_facts hz).2
  AB := h.exists_AB
  U_unique := h.unique_normal_four
  Q := h.facts_Q hz
  RV := h.facts_R hz
  conj_invol := h.conj_involutions
  le4 := h.le4_centralizer
  sq_z := h.exists_sq_eq_z hz
  half_central := h.half_central hz
  card_invol := h.card_invol
  A8 := by intro _; exact h.isA8Type_quotient hz

theorem of_types (hS : IsJ2Type S) (hTS : T ≤ S) (hT : IsL34Type T) (hx : x ∈ S) (hxT : x ∉ T)
    (hx2 : x ^ 2 = 1) : J2Emb S T x := by
  obtain ⟨e⟩ := hS
  let f0 : J2Syl →* G := S.subtype.comp e.symm.toMonoidHom
  have hf0 : Function.Injective f0 := S.subtype_injective.comp e.symm.injective
  have hrange0 : f0.range = S := by
    ext g
    constructor
    · rintro ⟨m, rfl⟩
      exact (e.symm m).2
    · intro hg
      exact ⟨e ⟨g, hg⟩, by simp [f0]⟩
  obtain ⟨T₀, hT₀⟩ := exists_eq_map_of_le_range (hTS.trans hrange0.ge)
  have hT₀L : IsL34Type T₀ := by
    obtain ⟨eT⟩ := hT
    exact ⟨(Subgroup.equivMapOfInjective T₀ f0 hf0).trans
      ((MulEquiv.subgroupCongr hT₀).trans eT)⟩
  obtain ⟨A', B', hAB'⟩ := hT₀L.facts
  have hA'1 := J2Syl.isE4_unique A' hAB'.A_E
  have hB'1 := J2Syl.isE4_unique B' hAB'.B_E
  have hT₀W : T₀ = J2Syl.W := by
    rw [← hAB'.sup_eq]
    rcases hA'1 with rfl | rfl <;> rcases hB'1 with rfl | rfl
    · exact absurd rfl hAB'.A_ne_B
    · exact J2Syl.A_sup_B
    · rw [sup_comm]; exact J2Syl.A_sup_B
    · exact absurd rfl hAB'.A_ne_B
  subst hT₀W
  obtain ⟨m, rfl⟩ : x ∈ f0.range := hrange0 ▸ hx
  have hmW : m.right ≠ 1 := fun h0 => hxT (hT₀ ▸ Subgroup.mem_map_of_mem f0 h0)
  have hm2 : m * m = 1 := hf0 (by rw [map_mul, map_one, ← pow_two]; exact hx2)
  obtain ⟨g, hg⟩ := J2Syl.conj_involutions m hmW hm2
  have hWc : J2Syl.W.map (MulAut.conj g).toMonoidHom = J2Syl.W := by
    ext s
    constructor
    · rintro ⟨w, hw, rfl⟩
      exact J2Syl.W_normal g w hw
    · intro hs
      refine ⟨g⁻¹ * s * g, ?_, ?_⟩
      · simpa using J2Syl.W_normal g⁻¹ s hs
      · simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
        group
  refine ⟨f0.comp (MulAut.conj g).toMonoidHom, hf0.comp (MulAut.conj g).injective, ?_, ?_, ?_⟩
  · ext s
    constructor
    · rintro ⟨m', rfl⟩
      exact hrange0 ▸ ⟨_, rfl⟩
    · intro hs
      obtain ⟨m', rfl⟩ : s ∈ f0.range := hrange0 ▸ hs
      refine ⟨g⁻¹ * m' * g, ?_⟩
      simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      congr 1
      group
  · rw [← Subgroup.map_map, hWc]
    exact hT₀
  · simp [MulAut.conj_apply, hg]

theorem facts_of_types (hS : IsJ2Type S) (hTS : T ≤ S) (hT : IsL34Type T) (hx : x ∈ S)
    (hxT : x ∉ T) (hx2 : x ^ 2 = 1) {z : G} (hz : IsZGen S z) : J2Facts S T x z :=
  (of_types hS hTS hT hx hxT hx2).facts hz

end J2Emb

end CFSG.GH74.Uniqueness.SU.SU5
