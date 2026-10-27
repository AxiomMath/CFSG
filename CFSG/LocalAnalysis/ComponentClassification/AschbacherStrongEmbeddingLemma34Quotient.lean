module

public import CFSG.LocalAnalysis.ComponentClassification.AschbacherStrongEmbeddingLemma34Star
public import CFSG.LocalAnalysis.RankTwoShapes.FourShapes.SelfCentralizingFour

public section

namespace CFSG.ComponentClassification.AschbacherStrongEmbedding

namespace Lemma34

open CFSG.Open CFSG.ComponentClassification.AschbacherTightEmbedding
open CFSG.ComponentClassification.AschbacherTheorem3 (IsDihedralTwoGroup IsSemidihedralTwoGroup)

variable {G : Type} [Group G]

theorem mem_or_mul_mem_of_mem_sup_zpowers {K : Subgroup G} {y : G}
    (hyc : y ∈ Subgroup.center G) (hyy : y * y = 1) {x : G}
    (hx : x ∈ K ⊔ Subgroup.zpowers y) : x ∈ K ∨ x * y ∈ K := by
  have hcomm : ∀ g : G, g * y = y * g := fun g => Subgroup.mem_center_iff.mp hyc g
  let M : Subgroup G :=
    { carrier := {x | x ∈ K ∨ x * y ∈ K}
      mul_mem' := by
        intro a b ha hb
        change a ∈ K ∨ a * y ∈ K at ha
        change b ∈ K ∨ b * y ∈ K at hb
        change a * b ∈ K ∨ a * b * y ∈ K
        rcases ha with ha | ha <;> rcases hb with hb | hb
        · exact Or.inl (K.mul_mem ha hb)
        · right
          rw [mul_assoc]
          exact K.mul_mem ha hb
        · right
          rw [mul_assoc, hcomm b, ← mul_assoc]
          exact K.mul_mem ha hb
        · left
          have heq : a * y * (b * y) = a * b := by
            rw [mul_assoc, ← mul_assoc y b y, ← hcomm b, mul_assoc b y y, hyy, mul_one]
          rw [← heq]
          exact K.mul_mem ha hb
      one_mem' := Or.inl K.one_mem
      inv_mem' := by
        intro a ha
        change a ∈ K ∨ a * y ∈ K at ha
        change a⁻¹ ∈ K ∨ a⁻¹ * y ∈ K
        rcases ha with ha | ha
        · exact Or.inl (K.inv_mem ha)
        · right
          have hyinv : y⁻¹ = y := inv_eq_of_mul_eq_one_left hyy
          have := K.inv_mem ha
          rwa [mul_inv_rev, hyinv, ← hcomm] at this }
  have hle : K ⊔ Subgroup.zpowers y ≤ M := by
    refine sup_le (fun k hk => Or.inl hk) ?_
    rw [Subgroup.zpowers_le]
    exact Or.inr (by rw [hyy]; exact K.one_mem)
  exact hle hx

theorem card_le_two_mul_inf_of_le_sup_zpowers [Finite G] {A B : Subgroup G} {y : G}
    (hyc : y ∈ Subgroup.center G) (hyy : y * y = 1) (h : A ≤ B ⊔ Subgroup.zpowers y) :
    Nat.card A ≤ 2 * Nat.card (A ⊓ B : Subgroup G) := by
  have hcomm : ∀ g : G, g * y = y * g := fun g => Subgroup.mem_center_iff.mp hyc g
  by_cases hAB : A ≤ B
  · rw [inf_eq_left.mpr hAB]
    omega
  obtain ⟨c, hcA, hcB⟩ := Set.not_subset.mp hAB
  have hcy : c * y ∈ B := (mem_or_mul_mem_of_mem_sup_zpowers hyc hyy (h hcA)).resolve_left hcB
  set I := (A ⊓ B : Subgroup G)
  have hsub : (A : Set G) ⊆ (I : Set G) ∪ (fun x => c * x) '' (I : Set G) := by
    intro b hb
    rcases mem_or_mul_mem_of_mem_sup_zpowers hyc hyy (h hb) with hbB | hbB
    · exact Or.inl ⟨hb, hbB⟩
    · right
      refine ⟨c⁻¹ * b, ⟨A.mul_mem (A.inv_mem hcA) hb, ?_⟩, by simp⟩
      have := B.mul_mem (B.inv_mem hcy) hbB
      have hyinv : y⁻¹ = y := inv_eq_of_mul_eq_one_left hyy
      have heq : y * c⁻¹ * (b * y) = c⁻¹ * b := by
        calc y * c⁻¹ * (b * y) = y * (c⁻¹ * b * y) := by group
          _ = y * (y * (c⁻¹ * b)) := by rw [hcomm (c⁻¹ * b)]
          _ = c⁻¹ * b := by rw [← mul_assoc, hyy, one_mul]
      rwa [mul_inv_rev, hyinv, heq] at this
  have h1 : Nat.card A ≤ ((I : Set G) ∪ (fun x => c * x) '' (I : Set G)).ncard := by
    rw [← Nat.card_coe_set_eq]
    exact Set.ncard_le_ncard hsub (Set.toFinite _)
  have h2 := Set.ncard_union_le (I : Set G) ((fun x => c * x) '' (I : Set G))
  have h3 : ((fun x => c * x) '' (I : Set G)).ncard = (I : Set G).ncard :=
    Set.ncard_image_of_injective _ (mul_right_injective c)
  have h4 : (I : Set G).ncard = Nat.card I := Nat.card_coe_set_eq _
  omega

theorem rightConjugate_map_hom {G' : Type*} [Group G'] (f : G →* G') (Q : Subgroup G) (g : G) :
    rightConjugate (Q.map f) (f g) = (rightConjugate Q g).map f := by
  ext x
  rw [mem_rightConjugate_iff]
  constructor
  · rintro ⟨q, hq, hqx⟩
    rw [SetLike.mem_coe] at hq
    refine ⟨g⁻¹ * q * g, ?_, ?_⟩
    · rw [SetLike.mem_coe, mem_rightConjugate_iff]
      simpa only [mul_assoc, mul_inv_cancel, mul_one, mul_inv_cancel_left] using hq
    · rw [map_mul, map_mul, map_inv, hqx]
      group
  · rintro ⟨w, hw, rfl⟩
    rw [SetLike.mem_coe, mem_rightConjugate_iff] at hw
    exact ⟨g * w * g⁻¹, hw, by rw [map_mul, map_mul, map_inv]⟩

theorem injective_comp_subtype_of_inf_ker {G' : Type*} [Group G'] (f : G →* G') (A : Subgroup G)
    (hA : A ⊓ f.ker = ⊥) : Function.Injective (f.comp A.subtype) := by
  intro a b hab
  have hmem : (a : G)⁻¹ * b ∈ A ⊓ f.ker := by
    refine Subgroup.mem_inf.mpr ⟨A.mul_mem (A.inv_mem a.2) b.2, ?_⟩
    rw [MonoidHom.mem_ker, map_mul, map_inv]
    change (f.comp A.subtype a)⁻¹ * f.comp A.subtype b = 1
    rw [hab, inv_mul_cancel]
  rw [hA, Subgroup.mem_bot] at hmem
  exact Subtype.ext (by rw [← mul_inv_cancel_left (a : G) b, hmem, mul_one])

noncomputable def equivMapOfInfKer {G' : Type*} [Group G'] (f : G →* G') (A : Subgroup G)
    (hA : A ⊓ f.ker = ⊥) : A ≃* A.map f :=
  (MonoidHom.ofInjective (injective_comp_subtype_of_inf_ker f A hA)).trans
    (MulEquiv.subgroupCongr (by
      rw [MonoidHom.range_comp, Subgroup.range_subtype]))

theorem pRank_le_map_of_inf_ker [Finite G] {G' : Type*} [Group G'] [Finite G'] (f : G →* G')
    (A : Subgroup G) (hA : A ⊓ f.ker = ⊥) :
    CFSG.Open.pRank 2 A ≤ CFSG.Open.pRank 2 (A.map f) := by
  have h := CFSG.SectionRank.pRank_le_map (p := 2) (by norm_num) (f.comp A.subtype)
    (injective_comp_subtype_of_inf_ker f A hA) ⊤
  rw [← MonoidHom.range_eq_map, MonoidHom.range_comp, Subgroup.range_subtype] at h
  have h' := pRank_subgroupOf_eq A A
  rw [Subgroup.subgroupOf_self, inf_idem] at h'
  rw [← h']
  exact h

variable [Finite G] {S : Sylow 2 G} {A₁ A₂ : Subgroup G}

omit [Finite G] in
theorem mem_normalizer_one_of_mem_union (hc : ⁅A₁, A₂⁆ = ⊥) {b : G}
    (hb : b ∈ (A₁ : Set G) ∪ A₂) : b ∈ Subgroup.normalizer (A₁ : Set G) := by
  rcases hb with hb | hb
  · exact Subgroup.le_normalizer hb
  · rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · intro hx
      rw [← (commute_of_comm hc hx hb).eq, mul_inv_cancel_right]
      exact hx
    · intro hw
      have hc' := (commute_of_comm hc hw hb).eq
      have hx : x = b * x * b⁻¹ := by
        calc x = b⁻¹ * (b * x * b⁻¹ * b) := by group
          _ = b⁻¹ * (b * (b * x * b⁻¹)) := by rw [hc']
          _ = b * x * b⁻¹ := by group
      rw [hx]
      exact hw

omit [Finite G] in
theorem mem_normalizer_two_of_mem_union (hc : ⁅A₁, A₂⁆ = ⊥) {b : G}
    (hb : b ∈ (A₁ : Set G) ∪ A₂) : b ∈ Subgroup.normalizer (A₂ : Set G) := by
  have hc' : ⁅A₂, A₁⁆ = ⊥ := by rw [Subgroup.commutator_comm]; exact hc
  rw [Set.union_comm] at hb
  exact mem_normalizer_one_of_mem_union hc' hb

omit [Finite G] in
theorem mem_normalizer_of_mem_center {K : Subgroup G} {y : G} (hy : y ∈ Subgroup.center G) :
    y ∈ Subgroup.normalizer (K : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro x
  rw [← Subgroup.mem_center_iff.mp hy x, mul_inv_cancel_right]

omit [Finite G] in
theorem eq_one_or_eq_of_mem_zpowers_of_mul_self {y n : G} (hyy : y * y = 1)
    (hn : n ∈ Subgroup.zpowers y) : n = 1 ∨ n = y := by
  by_cases hy1 : y = 1
  · subst hy1
    rw [Subgroup.zpowers_one_eq_bot, Subgroup.mem_bot] at hn
    exact Or.inl hn
  · exact CFSG.RankTwoShapes.eq_one_or_eq_of_mem_zpowers
      (orderOf_eq_prime (by rw [sq]; exact hyy) hy1) hn

theorem Hyp.overlapClosure_map_le (h : Hyp S A₁ A₂) {y : G} (hyc : y ∈ Subgroup.center G)
    (hyS : y ∈ (S : Subgroup G)) (hyy : y * y = 1) [(Subgroup.zpowers y).Normal] :
    overlapClosure (A₁.map (QuotientGroup.mk' (Subgroup.zpowers y)))
        (A₂.map (QuotientGroup.mk' (Subgroup.zpowers y))) ≤
      (overlapClosure A₁ A₂).map (QuotientGroup.mk' (Subgroup.zpowers y)) := by
  set N := Subgroup.zpowers y with hNdef
  set π := QuotientGroup.mk' N with hπdef
  have hker : π.ker = N := QuotientGroup.ker_mk' N
  rw [overlapClosure, Subgroup.closure_le]
  rintro _ ⟨X', hX', Y', hY', hne⟩
  obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective N ‹_›
  obtain ⟨X, hX, rfl⟩ : ∃ X : Subgroup G, (X = A₁ ∨ X = A₂) ∧ X.map π = X' := by
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hX'
    rcases hX' with rfl | rfl
    · exact ⟨A₁, Or.inl rfl, rfl⟩
    · exact ⟨A₂, Or.inr rfl, rfl⟩
  obtain ⟨Y, hY, rfl⟩ : ∃ Y : Subgroup G, (Y = A₁ ∨ Y = A₂) ∧ Y.map π = Y' := by
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hY'
    rcases hY' with rfl | rfl
    · exact ⟨A₁, Or.inl rfl, rfl⟩
    · exact ⟨A₂, Or.inr rfl, rfl⟩
  have hU : ∀ {Z : Subgroup G}, (Z = A₁ ∨ Z = A₂) → ∀ {w : G}, w ∈ Z →
      w ∈ (A₁ : Set G) ∪ A₂ := by
    rintro Z (rfl | rfl) w hw
    · exact Or.inl hw
    · exact Or.inr hw
  change π g ∈ (overlapClosure A₁ A₂).map π
  rw [rightConjugate_map_hom] at hne
  obtain ⟨w', hw', hw'1⟩ := (Subgroup.bot_or_exists_ne_one _).resolve_left hne
  obtain ⟨⟨w₁, hw₁, hw₁e⟩, ⟨b, hb, hbe⟩⟩ := Subgroup.mem_inf.mp hw'
  rw [SetLike.mem_coe, mem_rightConjugate_iff] at hw₁
  rw [SetLike.mem_coe] at hb
  have hxw : g⁻¹ * (g * w₁ * g⁻¹) * g = w₁ := by group
  have hx1 : g * w₁ * g⁻¹ ≠ 1 := by
    intro h1
    apply hw'1
    rw [← hw₁e]
    have : w₁ = 1 := by
      calc w₁ = g⁻¹ * (g * w₁ * g⁻¹) * g := hxw.symm
        _ = 1 := by rw [h1]; group
    rw [this, map_one]
  have hxU := hU hX hw₁
  have hbU := hU hY hb
  have hbw : b⁻¹ * w₁ ∈ N := by
    rw [← hker, MonoidHom.mem_ker, map_mul, map_inv, hw₁e, hbe, inv_mul_cancel]
  refine ⟨g, ?_, rfl⟩
  rcases eq_one_or_eq_of_mem_zpowers_of_mul_self hyy hbw with h1 | h1
  · have hwb : w₁ = b := by
      calc w₁ = b * (b⁻¹ * w₁) := by group
        _ = b := by rw [h1, mul_one]
    exact mem_overlapClosure_of_union hxU hx1 (by rw [hxw, hwb]; exact hbU)
  · have hwb : w₁ = b * y := by
      calc w₁ = b * (b⁻¹ * w₁) := by group
        _ = b * y := by rw [h1]
    have hbS : b ∈ (S : Subgroup G) := by
      rcases hbU with hb' | hb'
      · exact h.le_one hb'
      · exact h.le_two hb'
    have hS' : g⁻¹ * (g * w₁ * g⁻¹) * g ∈ (S : Subgroup G) := by
      rw [hxw, hwb]
      exact Subgroup.mul_mem _ hbS hyS
    have hN' : g⁻¹ * (g * w₁ * g⁻¹) * g ∈ Subgroup.normalizer (A₁ : Set G) := by
      rw [hxw, hwb]
      exact Subgroup.mul_mem _ (mem_normalizer_one_of_mem_union h.comm hbU)
        (mem_normalizer_of_mem_center hyc)
    exact mem_overlapClosure_of_union hxU hx1
      (h.conj_mem_of_mem_normalizer hxU hS' (Or.inl hN'))

theorem Hyp.quotient_central (h : Hyp S A₁ A₂) (h12 : ¬ A₁ ≤ A₂) (h21 : ¬ A₂ ≤ A₁)
    (IH : Statement (Nat.card G - 1)) {y : G} (hyc : y ∈ Subgroup.center G) (hyy : y * y = 1)
    (hy₁ : y ∉ A₁) (hy₂ : y ∉ A₂)
    (hn₁ : ¬ A₁ ≤ A₂ ⊔ Subgroup.zpowers y) (hn₂ : ¬ A₂ ≤ A₁ ⊔ Subgroup.zpowers y) :
    overlapClosure A₁ A₂ = ⊤ ∨
      ((IsDihedralTwoGroup A₁ ∨ IsSemidihedralTwoGroup A₁) ∧
        ∃ a ∈ A₁, ∃ g : G, g⁻¹ * a * g ∈ (S : Subgroup G) ∧
          g⁻¹ * a * g ∉ Subgroup.normalizer (A₁ : Set G)) := by
  set N := Subgroup.zpowers y with hNdef
  have hy1 : y ≠ 1 := fun h1 => hy₁ (h1 ▸ A₁.one_mem)
  have hNc : N ≤ Subgroup.center G := Subgroup.zpowers_le.mpr hyc
  have hNn : N.Normal := ⟨fun n hn g => by
    rw [Subgroup.mem_center_iff.mp (hNc hn) g, mul_inv_cancel_right]
    exact hn⟩
  have hy2 : orderOf y = 2 := orderOf_eq_prime (by rw [sq]; exact hyy) hy1
  have hNp : IsPGroup 2 N := IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hy2, pow_one])
  have hNS : N ≤ (S : Subgroup G) := hNp.le_sylow_of_normal S
  have hyS : y ∈ (S : Subgroup G) := hNS (Subgroup.mem_zpowers y)
  set π := QuotientGroup.mk' N with hπdef
  have hπ : Function.Surjective π := QuotientGroup.mk'_surjective N
  have hker : π.ker = N := QuotientGroup.ker_mk' N
  have hπconj : ∀ g a : G, π (g⁻¹ * a * g) = (π g)⁻¹ * π a * π g := fun g a => by
    rw [map_mul, map_mul, map_inv]
  have hinf : ∀ {A : Subgroup G}, y ∉ A → A ⊓ π.ker = ⊥ := by
    intro A hyA
    rw [hker, eq_bot_iff]
    intro x hx
    rcases eq_one_or_eq_of_mem_zpowers_of_mul_self hyy hx.2 with h1 | h1
    · exact h1
    · exact absurd (h1 ▸ hx.1) hyA
  have hSH := h.sylow_le_overlapClosure h12 h21
  let S' : Sylow 2 (G ⧸ N) := S.mapSurjective hπ
  have hS' : (S' : Subgroup (G ⧸ N)) = (S : Subgroup G).map π := rfl
  have hliftS : ∀ x : G, π x ∈ (S : Subgroup G).map π → x ∈ (S : Subgroup G) := by
    rintro x ⟨s, hs, hsx⟩
    have hsn : s⁻¹ * x ∈ N := by
      rw [← hker, MonoidHom.mem_ker, map_mul, map_inv, hsx, inv_mul_cancel]
    have := Subgroup.mul_mem _ hs (hNS hsn)
    rwa [mul_inv_cancel_left] at this
  have hnot : ∀ {A B : Subgroup G}, ¬ A ≤ B ⊔ N → ¬ A.map π ≤ B.map π := by
    intro A B hAB hle
    apply hAB
    have : A ≤ (B.map π).comap π := fun x hx => hle ⟨x, hx, rfl⟩
    rwa [Subgroup.comap_map_eq, hker] at this
  have hHle := h.overlapClosure_map_le hyc hyS hyy
  have hlift : ∀ {a' : G ⧸ N}, a' ∈ ((A₁.map π : Subgroup (G ⧸ N)) : Set (G ⧸ N)) ∪
      (A₂.map π : Subgroup (G ⧸ N)) → ∃ a ∈ (A₁ : Set G) ∪ A₂, π a = a' := by
    rintro a' (⟨a, ha, rfl⟩ | ⟨a, ha, rfl⟩)
    · exact ⟨a, Or.inl ha, rfl⟩
    · exact ⟨a, Or.inr ha, rfl⟩
  have hpush : ∀ {x : G}, x ∈ (A₁ : Set G) ∪ A₂ →
      π x ∈ ((A₁.map π : Subgroup (G ⧸ N)) : Set (G ⧸ N)) ∪ (A₂.map π : Subgroup (G ⧸ N)) := by
    rintro x (hx | hx)
    · exact Or.inl ⟨x, hx, rfl⟩
    · exact Or.inr ⟨x, hx, rfl⟩
  have hyp : Hyp S' (A₁.map π) (A₂.map π) :=
    { le_one := Subgroup.map_mono h.le_one
      le_two := Subgroup.map_mono h.le_two
      comm := by rw [← Subgroup.map_commutator, h.comm, Subgroup.map_bot]
      rank_one := h.rank_one.trans (pRank_le_map_of_inf_ker π A₁ (hinf hy₁))
      rank_two := h.rank_two.trans (pRank_le_map_of_inf_ker π A₂ (hinf hy₂))
      closed_overlap := by
        intro a' ha' k' hk' hmem
        obtain ⟨a, haU, rfl⟩ := hlift ha'
        obtain ⟨k, hk, rfl⟩ := hHle hk'
        have hS : k⁻¹ * a * k ∈ (S : Subgroup G) :=
          hliftS _ (by rw [hπconj]; exact hmem.2)
        rw [← hπconj]
        exact hpush (h.conj_mem_of_mem_overlapClosure haU hk hS)
      closed_one := by
        intro a' ha' g' _ hmem
        obtain ⟨a, haU, rfl⟩ := hlift ha'
        obtain ⟨g, rfl⟩ := hπ g'
        rw [← hπconj] at hmem ⊢
        have hS : g⁻¹ * a * g ∈ (S : Subgroup G) := hliftS _ hmem.1
        have hN : g⁻¹ * a * g ∈ Subgroup.normalizer (A₁ : Set G) := by
          rcases h.sylow_le_pairStabilizer h12 h21 hS with ⟨h₁, -⟩ | ⟨h₁, -⟩
          · exact (rightConjugate_eq_self_iff _ _).mp h₁
          · exfalso
            have hn : π (g⁻¹ * a * g) ∈
                Subgroup.normalizer ((A₁.map π : Subgroup (G ⧸ N)) : Set (G ⧸ N)) := hmem.2
            rw [← rightConjugate_eq_self_iff, rightConjugate_map_hom, h₁] at hn
            exact hnot hn₂ (le_of_eq hn)
        exact hpush (h.conj_mem_of_mem_normalizer haU hS (Or.inl hN))
      closed_two := by
        intro a' ha' g' _ hmem
        obtain ⟨a, haU, rfl⟩ := hlift ha'
        obtain ⟨g, rfl⟩ := hπ g'
        rw [← hπconj] at hmem ⊢
        have hS : g⁻¹ * a * g ∈ (S : Subgroup G) := hliftS _ hmem.1
        have hN : g⁻¹ * a * g ∈ Subgroup.normalizer (A₂ : Set G) := by
          rcases h.sylow_le_pairStabilizer h12 h21 hS with ⟨-, h₂⟩ | ⟨-, h₂⟩
          · exact (rightConjugate_eq_self_iff _ _).mp h₂
          · exfalso
            have hn : π (g⁻¹ * a * g) ∈
                Subgroup.normalizer ((A₂.map π : Subgroup (G ⧸ N)) : Set (G ⧸ N)) := hmem.2
            rw [← rightConjugate_eq_self_iff, rightConjugate_map_hom, h₂] at hn
            exact hnot hn₁ (le_of_eq hn)
        exact hpush (h.conj_mem_of_mem_normalizer haU hS (Or.inr hN)) }
  have hcard : Nat.card (G ⧸ N) ≤ Nat.card G - 1 := by
    have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup N
    rw [Nat.card_zpowers, hy2] at h1
    have h2 : 0 < Nat.card (G ⧸ N) := Nat.card_pos
    omega
  rcases IH (G ⧸ N) hcard S' (A₁.map π) (A₂.map π) hyp with htop | hle | hle | hd
  · left
    rw [eq_top_iff]
    intro g _
    obtain ⟨k, hk, hkg⟩ := hHle (htop ▸ Subgroup.mem_top (π g))
    have hkn : k⁻¹ * g ∈ N := by
      rw [← hker, MonoidHom.mem_ker, map_mul, map_inv, hkg, inv_mul_cancel]
    have := Subgroup.mul_mem _ hk (hSH (hNS hkn))
    rwa [mul_inv_cancel_left] at this
  · exact absurd hle (hnot hn₁)
  · exact absurd hle (hnot hn₂)
  · right
    obtain ⟨⟨a', ha', g', hS, hconj⟩, hdih, -⟩ := hd
    obtain ⟨a, ha, rfl⟩ := ha'
    obtain ⟨g, rfl⟩ := hπ g'
    rw [← hπconj] at hS hconj
    refine ⟨dihedral_of_mulEquiv (equivMapOfInfKer π A₁ (hinf hy₁)).symm hdih, a, ha, g,
      hliftS _ hS, fun hN => ?_⟩
    rw [← rightConjugate_eq_self_iff] at hN
    rw [rightConjugate_map_hom, hN] at hconj
    exact hnot hn₁ (le_of_eq hconj)

end Lemma34

end CFSG.ComponentClassification.AschbacherStrongEmbedding
