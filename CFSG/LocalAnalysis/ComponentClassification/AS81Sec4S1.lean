module

public import CFSG.LocalAnalysis.ComponentClassification.AS81Sec4HeSylowIso
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.LocalAnalysis.ComponentClassification.AS81Sec4Defs
public import CFSG.LocalAnalysis.SectionRank.PRank

public section

namespace CFSG.ComponentClassification.AS81

open Subgroup CFSG.Open CFSG.ABGLocalTools CFSG.ComponentClassification.AschbacherTightEmbedding
open CFSG.Blueprint.NativeSporadic HeSylow

variable {G : Type} [Group G] [Finite G]

theorem sup_le_of_isSylowOf_normalizer {A R : Subgroup G} {g : G} {E F S₁ : Subgroup G}
    (hset : Sec4Setting G A R g E F)
    (hSN : IsSylowOf 2 S₁ (normalizer ((E ⊔ F : Subgroup G) : Set G))) : E ⊔ F ≤ S₁ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨T, hT⟩ := hSN
  have hP : IsPGroup 2 ((E ⊔ F).subgroupOf (normalizer ((E ⊔ F : Subgroup G) : Set G))) :=
    hset.frame.sylow.isPGroup.of_equiv (subgroupOfEquivOfLe le_normalizer).symm
  have : ((E ⊔ F).subgroupOf (normalizer ((E ⊔ F : Subgroup G) : Set G))).Normal :=
    normal_in_normalizer
  have hle := hP.le_sylow_of_normal T
  intro x hx
  rw [← hT]
  exact ⟨⟨x, le_normalizer hx⟩, hle (show (⟨x, le_normalizer hx⟩ : ↥(normalizer
    ((E ⊔ F : Subgroup G) : Set G))) ∈ (E ⊔ F).subgroupOf _ from hx), rfl⟩

omit [Finite G] in
theorem exists_sylModel_of_equiv {H : Type} [Group H] {X Q E F U : Subgroup H} {z : H} {k : ℕ}
    (hm : SylModel X Q E F U z k) {S₁ : Subgroup G} (θ : ↥X ≃* ↥S₁) :
    ∃ (Q' E' F' U' : Subgroup G) (z' : G), SylModel S₁ Q' E' F' U' z' k := by
  let f : ↥X →* G := S₁.subtype.comp θ.toMonoidHom
  have hf : Function.Injective f := S₁.subtype_injective.comp θ.injective
  have hr : f.range = S₁ := by
    ext y
    constructor
    · rintro ⟨x, rfl⟩
      exact (θ x).2
    · intro hy
      exact ⟨θ.symm ⟨y, hy⟩, by simp [f]⟩
  have h := hm.map f hf
  rw [hr] at h
  exact ⟨_, _, _, _, _, h⟩

theorem exists_sylModel_of_step44
    (h44 : Step44ii) {A R : Subgroup G} {g : G} {E F S₁ : Subgroup G}
    (hset : Sec4Setting G A R g E F)
    (hSN : IsSylowOf 2 S₁ (normalizer ((E ⊔ F : Subgroup G) : Set G))) :
    ∃ (Q E' F' U : Subgroup G) (z : G) (k : ℕ), (k = 4 ∨ k = 8) ∧
      SylModel S₁ Q E' F' U z k := by
  rcases h44 G A R g E F hset S₁ hSN with ⟨_hc, P, ⟨e⟩⟩ |
    ⟨_hc, H, _, _, K, hKn, hK, hi, hC, P, ⟨e⟩⟩
  · obtain ⟨e0⟩ := nonempty_sylow_he_equiv P
    obtain ⟨Q, E', F', U, z, hm⟩ := exists_sylModel_of_equiv sylModel16 (e.trans e0).symm
    exact ⟨Q, E', F', U, z, 4, Or.inl rfl, hm⟩
  · obtain ⟨e0⟩ := nonempty_sylow_aut_equiv hKn hK hi hC P
    obtain ⟨Q, E', F', U, z, hm⟩ := exists_sylModel_of_equiv sylModel32 (e.trans e0).symm
    exact ⟨Q, E', F', U, z, 8, Or.inr rfl, hm⟩

theorem eq_or_eq_of_sylModel {A R : Subgroup G} {g : G} {E F S₁ Q E' F' U : Subgroup G} {z : G}
    {k : ℕ} (hset : Sec4Setting G A R g E F)
    (hSN : IsSylowOf 2 S₁ (normalizer ((E ⊔ F : Subgroup G) : Set G)))
    (hm : SylModel S₁ Q E' F' U z k) {V : Subgroup G} (hV : V ≤ S₁) (hVe : IsElemAbelian 2 V)
    (hc : Nat.card V = 2 ^ 6) : V = E ∨ V = F := by
  have hEle : E ≤ S₁ := le_sup_left.trans (sup_le_of_isSylowOf_normalizer hset hSN)
  have hFle : F ≤ S₁ := le_sup_right.trans (sup_le_of_isSylowOf_normalizer hset hSN)
  have hE := hm.uniqE E hEle hset.frame.elemE (by rw [hset.frame.cardE]; norm_num)
  have hF := hm.uniqE F hFle hset.frame.elemF (by rw [hset.frame.cardF]; norm_num)
  have hne : E ≠ F := hset.frame.ne
  rcases hm.uniqE V hV hVe hc with h | h <;> rcases hE with hE | hE <;>
    rcases hF with hF | hF <;>
    first
    | exact Or.inl (h.trans hE.symm)
    | exact Or.inr (h.trans hF.symm)
    | exact absurd (hE.trans hF.symm) hne

omit [Finite G] in
theorem isElemAbelian_map {K : Subgroup G} (hK : IsElemAbelian 2 K) (f : G →* G) :
    IsElemAbelian 2 (K.map f) := CFSG.SectionRank.isElemAbelian_map hK _

theorem mem_normalizer_of_map_conj_le {K : Subgroup G} {x : G}
    (h : K.map (MulAut.conj x).toMonoidHom ≤ K) : x ∈ normalizer (K : Set G) := by
  rw [mem_normalizer_iff_map_conj_eq]
  exact Subgroup.eq_of_le_of_card_ge h
    (le_of_eq (card_map_of_injective (MulAut.conj x).injective).symm)

theorem normalizer_le_of_sylModel {A R : Subgroup G} {g : G} {E F S₁ Q E' F' U : Subgroup G}
    {z : G} {k : ℕ} (hset : Sec4Setting G A R g E F)
    (hSN : IsSylowOf 2 S₁ (normalizer ((E ⊔ F : Subgroup G) : Set G)))
    (hm : SylModel S₁ Q E' F' U z k) :
    normalizer (S₁ : Set G) ≤ normalizer ((E ⊔ F : Subgroup G) : Set G) := by
  intro x hx
  have hS₁ : S₁.map (MulAut.conj x).toMonoidHom = S₁ := (mem_normalizer_iff_map_conj_eq.mp hx)
  have hEF := sup_le_of_isSylowOf_normalizer hset hSN
  have key : ∀ V : Subgroup G, V ≤ S₁ → IsElemAbelian 2 V → Nat.card V = 64 →
      V.map (MulAut.conj x).toMonoidHom ≤ E ⊔ F := by
    intro V hV hVe hc
    have hle : V.map (MulAut.conj x).toMonoidHom ≤ S₁ := hS₁ ▸ map_mono hV
    rcases eq_or_eq_of_sylModel hset hSN hm hle (isElemAbelian_map hVe _)
      (by rw [card_map_of_injective (MulAut.conj x).injective, hc]; norm_num) with h | h <;>
      rw [h]
    · exact le_sup_left
    · exact le_sup_right
  refine mem_normalizer_of_map_conj_le ?_
  rw [Subgroup.map_sup]
  exact sup_le (key E (le_sup_left.trans hEF) hset.frame.elemE hset.frame.cardE)
    (key F (le_sup_right.trans hEF) hset.frame.elemF hset.frame.cardF)

end CFSG.ComponentClassification.AS81
