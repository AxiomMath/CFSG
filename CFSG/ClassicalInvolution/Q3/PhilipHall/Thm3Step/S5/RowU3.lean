module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Thm3Step.S5.RowU3Model
public import CFSG.ClassicalInvolution.Q3.TL4E3S3OM1PF

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Thm3Step.S5

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Q3
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameAEmptyPf
  CFSG.Blueprint CFSG.GH74.KGroups Certificates.S5Rows

open scoped commutatorElement

section Helpers

variable {G : Type*} [Group G]

theorem commutatorElement_central_mul_left {q : G} (hq : q ∈ Subgroup.center G) (a b : G) :
    ⁅q * a, b⁆ = ⁅a, b⁆ := by
  rw [commutatorElement_def, commutatorElement_def]
  have h1 : q⁻¹ * b⁻¹ = b⁻¹ * q⁻¹ :=
    (Subgroup.mem_center_iff.mp (Subgroup.inv_mem _ hq) b⁻¹).symm
  have h2 : q * (a * b * a⁻¹ * b⁻¹) = a * b * a⁻¹ * b⁻¹ * q :=
    (Subgroup.mem_center_iff.mp hq _).symm
  calc q * a * b * (q * a)⁻¹ * b⁻¹ = q * a * b * a⁻¹ * (q⁻¹ * b⁻¹) := by group
    _ = q * a * b * a⁻¹ * (b⁻¹ * q⁻¹) := by rw [h1]
    _ = q * (a * b * a⁻¹ * b⁻¹) * q⁻¹ := by group
    _ = a * b * a⁻¹ * b⁻¹ * q * q⁻¹ := by rw [h2]
    _ = a * b * a⁻¹ * b⁻¹ := by group

theorem commutatorElement_central_mul_right {q : G} (hq : q ∈ Subgroup.center G) (a b : G) :
    ⁅a, q * b⁆ = ⁅a, b⁆ := by
  rw [← commutatorElement_inv, commutatorElement_central_mul_left hq, commutatorElement_inv]

theorem commutator_sup_le_of_le_center {D Q : Subgroup G} (hQc : Q ≤ Subgroup.center G) :
    ⁅D ⊔ Q, D ⊔ Q⁆ ≤ ⁅D, D⁆ := by
  haveI : Q.Normal := Subgroup.normal_of_le_center hQc
  rw [Subgroup.commutator_le]
  intro a ha b hb
  rw [sup_comm, Subgroup.mem_sup_of_normal_left] at ha hb
  obtain ⟨q, hq, d, hd, rfl⟩ := ha
  obtain ⟨q', hq', d', hd', rfl⟩ := hb
  rw [commutatorElement_central_mul_left (hQc hq), commutatorElement_central_mul_right (hQc hq')]
  exact Subgroup.commutator_mem_commutator hd hd'

theorem commutator_le_of_index_two {N : Subgroup G} (hidx : N.index = 2) : commutator G ≤ N := by
  rw [commutator_def, Subgroup.commutator_le]
  intro a _ b _
  have hm := @Subgroup.mul_mem_iff_of_index_two _ _ N hidx
  rw [commutatorElement_def, hm, hm, hm, Subgroup.inv_mem_iff, Subgroup.inv_mem_iff]
  tauto

theorem commutator_eq_top_of_simple {N : Type*} [Group N] (hs : IsSimpleGroup N)
    (hab : ∃ a b : N, a * b ≠ b * a) : commutator N = ⊤ := by
  rcases hs.eq_bot_or_eq_top_of_normal (commutator N) with h | h
  · exfalso
    obtain ⟨a, b, hab⟩ := hab
    apply hab
    have h1 : ⁅a, b⁆ ∈ commutator N :=
      Subgroup.commutator_mem_commutator (Subgroup.mem_top a) (Subgroup.mem_top b)
    rw [h, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at h1
    exact h1
  · exact h

theorem map_commutator_of_surjective {H : Type*} [Group H] (f : G →* H)
    (hf : Function.Surjective f) : (commutator G).map f = commutator H := by
  rw [commutator_def, commutator_def, Subgroup.map_commutator, Subgroup.map_top_of_surjective f hf]

theorem commute_pow_mul_center (x : G) (e f : ℕ) {z z' : G} (hz : z ∈ Subgroup.center G)
    (hz' : z' ∈ Subgroup.center G) : Commute (x ^ e * z) (x ^ f * z') := by
  have h1 : Commute (x ^ e) (x ^ f * z') :=
    (Commute.pow_pow_self x e f).mul_right (Subgroup.mem_center_iff.mp hz' (x ^ e))
  have h2 : Commute z (x ^ f * z') := (Subgroup.mem_center_iff.mp hz (x ^ f * z')).symm
  exact h1.mul_left h2

theorem eq_one_or_eq_of_mem_zpowers_of_mul_self {w x : G} (hw : w * w = 1)
    (hx : x ∈ Subgroup.zpowers w) : x = 1 ∨ x = w := by
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
  have hw2 : w ^ (2 : ℤ) = 1 := by rw [zpow_two]; exact hw
  rcases Int.even_or_odd k with ⟨m, rfl⟩ | ⟨m, rfl⟩
  · left
    rw [← two_mul, zpow_mul, hw2, one_zpow]
  · right
    rw [zpow_add, zpow_mul, hw2, one_zpow, one_mul, zpow_one]

theorem conj_mem_iff_of_normal {H : Subgroup G} [hH : H.Normal] (g y : G) :
    g⁻¹ * y * g ∈ H ↔ y ∈ H :=
  ⟨fun h1 => by simpa [mul_assoc] using hH.conj_mem _ h1 g,
    fun h1 => by simpa using hH.conj_mem _ h1 g⁻¹⟩

theorem pullback_conj {X M : Type*} [Group X] [Group M] (θ : X ≃* M) {g y : M} {a b : X}
    (h : y⁻¹ * (g⁻¹ * θ a * g) * y = g⁻¹ * θ b * g) :
    (θ.symm (g * y * g⁻¹))⁻¹ * a * θ.symm (g * y * g⁻¹) = b := by
  apply θ.injective
  rw [map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply]
  calc (g * y * g⁻¹)⁻¹ * θ a * (g * y * g⁻¹) = g * (y⁻¹ * (g⁻¹ * θ a * g) * y) * g⁻¹ := by
        group
    _ = g * (g⁻¹ * θ b * g) * g⁻¹ := by rw [h]
    _ = θ b := by group

end Helpers

section Row

variable {G : Type} [Group G] [Finite G] {Φ : Set (Subgroup G)} {K Q : Subgroup G}
  {X : Type} [Group X] {ρ : G →* X}

theorem S5Hyp.commutator_inf_eq_bot_of_u33
    (h : S5Hyp Φ K Q)
    (hρ : Function.Surjective ρ) (hker : ρ.ker = Q) {N : Subgroup X} [N.Normal]
    (hidx : N.index = 2) (hL : LieModel ↥N .PSU 3 3 1) : commutator G ⊓ Q = ⊥ := by
  obtain ⟨hs, a, b, hab⟩ := PhilipHall.Frame.u33_isSimpleGroup hL
  have hNperf : ⁅N, N⁆ = N :=
    Subgroup.isPerfect_iff.mp (Group.isPerfect_def.mpr (commutator_eq_top_of_simple hs ⟨a, b, hab⟩))
  have hX' : commutator X = N := by
    refine le_antisymm (commutator_le_of_index_two hidx) ?_
    rw [commutator_def]
    calc N = ⁅N, N⁆ := hNperf.symm
      _ ≤ ⁅⊤, ⊤⁆ := Subgroup.commutator_mono le_top le_top
  have hG' : (commutator G).map ρ = N := by rw [map_commutator_of_surjective ρ hρ, hX']
  set D : Subgroup G := ⁅commutator G, commutator G⁆ with hDdef
  have hD : D.map ρ = N := by rw [hDdef, Subgroup.map_commutator, hG', hNperf]
  have hG'D : commutator G ≤ D ⊔ Q := by
    rw [← hker, ← Subgroup.map_le_map_iff, hD, hG']
  have hDD : ⁅D, D⁆ = D := by
    refine le_antisymm (Subgroup.commutator_le_self D) ?_
    calc D = ⁅commutator G, commutator G⁆ := hDdef
      _ ≤ ⁅D ⊔ Q, D ⊔ Q⁆ := Subgroup.commutator_mono hG'D hG'D
      _ ≤ ⁅D, D⁆ := commutator_sup_le_of_le_center h.le_center
  haveI : Group.IsPerfect ↥D := Subgroup.isPerfect_iff.mpr hDD
  have hDN : ∀ d : ↥D, (ρ.comp D.subtype) d ∈ N := fun d => by
    rw [← hD]
    exact Subgroup.mem_map_of_mem ρ d.2
  set η : ↥D →* ↥N := (ρ.comp D.subtype).codRestrict N hDN with hη
  have hηs : Function.Surjective η := by
    rintro ⟨n, hn⟩
    rw [← hD] at hn
    obtain ⟨d, hd, rfl⟩ := hn
    exact ⟨⟨d, hd⟩, rfl⟩
  have hηker : ∀ d : ↥D, d ∈ η.ker ↔ (d : G) ∈ Q := by
    intro d
    rw [MonoidHom.mem_ker, ← hker, MonoidHom.mem_ker]
    constructor
    · intro h1
      exact congrArg Subtype.val h1
    · intro h1
      exact Subtype.ext h1
  have hcen : η.ker ≤ Subgroup.center ↥D := by
    intro d hd
    rw [Subgroup.mem_center_iff]
    intro d'
    exact Subtype.ext (Subgroup.mem_center_iff.mp (h.le_center ((hηker d).mp hd)) d')
  have h2 : IsPGroup 2 ↥η.ker := by
    rintro ⟨d, hd⟩
    obtain ⟨n, hn⟩ := h.pgrp ⟨d, (hηker d).mp hd⟩
    refine ⟨n, Subtype.ext (Subtype.ext ?_)⟩
    simpa using congrArg Subtype.val hn
  have hk := TL4.E3S3O.ker_eq_bot_of_psu33 η hηs hcen h2 hL
  have hDQ : D ⊓ Q = ⊥ := by
    rw [eq_bot_iff]
    intro g hg
    rw [Subgroup.mem_inf] at hg
    have h1 : (⟨g, hg.1⟩ : ↥D) ∈ η.ker := (hηker _).mpr hg.2
    rw [hk, Subgroup.mem_bot] at h1
    rw [Subgroup.mem_bot]
    exact congrArg Subtype.val h1
  have hG'leD : commutator G ≤ D := by
    obtain ⟨x₀, hx₀⟩ : ∃ x₀ : G, ρ x₀ ∉ N := by
      by_contra hall
      push Not at hall
      have hN : N = ⊤ := eq_top_iff.mpr fun x _ => by
        obtain ⟨g, rfl⟩ := hρ x
        exact hall g
      rw [hN, Subgroup.index_top] at hidx
      exact absurd hidx (by norm_num)
    have hmemDQ : ∀ g : G, ρ g ∈ N → ∃ d ∈ D, ∃ q ∈ Q, g = d * q := by
      intro g hg
      rw [← hD] at hg
      obtain ⟨d, hd, hdg⟩ := hg
      refine ⟨d, hd, d⁻¹ * g, ?_, by group⟩
      rw [← hker, MonoidHom.mem_ker, map_mul, map_inv, hdg, inv_mul_cancel]
    have hform : ∀ g : G, ∃ e : ℕ, ∃ d ∈ D, ∃ q ∈ Q, g = x₀ ^ e * (d * q) := by
      intro g
      by_cases hg : ρ g ∈ N
      · obtain ⟨d, hd, q, hq, rfl⟩ := hmemDQ g hg
        exact ⟨0, d, hd, q, hq, by rw [pow_zero, one_mul]⟩
      · have h1 : ρ (x₀⁻¹ * g) ∈ N := by
          rw [map_mul, map_inv, Subgroup.mul_mem_iff_of_index_two hidx, Subgroup.inv_mem_iff]
          exact iff_of_false hx₀ hg
        obtain ⟨d, hd, q, hq, hdq⟩ := hmemDQ _ h1
        exact ⟨1, d, hd, q, hq, by rw [pow_one, ← hdq]; group⟩
    have hcz : ∀ q ∈ Q, QuotientGroup.mk' D q ∈ Subgroup.center (G ⧸ D) := by
      intro q hq
      rw [Subgroup.mem_center_iff]
      intro l
      obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective D l
      rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.mp (h.le_center hq) g]
    have hmk : ∀ g : G, ∃ e : ℕ, ∃ z ∈ Subgroup.center (G ⧸ D),
        QuotientGroup.mk' D g = QuotientGroup.mk' D x₀ ^ e * z := by
      intro g
      obtain ⟨e, d, hd, q, hq, rfl⟩ := hform g
      refine ⟨e, _, hcz q hq, ?_⟩
      have hd1 : QuotientGroup.mk' D d = 1 := (QuotientGroup.eq_one_iff d).mpr hd
      rw [map_mul, map_pow, map_mul, hd1, one_mul]
    rw [commutator_def, Subgroup.commutator_le]
    intro a _ b _
    rw [← QuotientGroup.eq_one_iff, ← QuotientGroup.mk'_apply, map_commutatorElement,
      commutatorElement_eq_one_iff_mul_comm]
    obtain ⟨e, z, hz, hza⟩ := hmk a
    obtain ⟨f, z', hz', hzb⟩ := hmk b
    rw [hza, hzb]
    exact commute_pow_mul_center _ e f hz hz'
  rw [eq_bot_iff, ← hDQ]
  intro g hg
  rw [Subgroup.mem_inf] at hg ⊢
  exact ⟨hG'leD hg.1, hg.2⟩

theorem S5Hyp.false_of_rowU3
    (h : S5Hyp Φ K Q)
    (hρ : Function.Surjective ρ) (hker : ρ.ker = Q) (hX : NoNormalTwo X)
    (hrow : ∃ (N : Subgroup X) (_ : N.Normal), N.index = 2 ∧ LieModel ↥N .PSU 3 3 1) :
    False := by
  obtain ⟨N, hNn, hidx, hL⟩ := hrow
  obtain ⟨θ, hθ⟩ := exists_u33_model hidx hL (centralizer_eq_bot_of_u33 hidx hL hX)
  have hdisj := h.commutator_inf_eq_bot_of_u33 hρ hker hidx hL
  haveI := u33P_normal
  have hG'N : ∀ g ∈ commutator G, ρ g ∈ N := fun g hg =>
    commutator_le_of_index_two hidx (map_commutator_of_surjective ρ hρ ▸
      Subgroup.mem_map_of_mem ρ hg)
  have hconjP : ∀ (g : ↥U33.QA.originalSubgroup) (a : X), g⁻¹ * θ a * g ∈ u33P ↔ a ∈ N :=
    fun g a => (conj_mem_iff_of_normal g (θ a)).trans (hθ a)
  have hinner : ∀ T ∈ RSet Φ, (∀ t ∈ T, ρ t ∈ N) → T ≤ commutator G := fun T hT hTN =>
    @S5Hyp.le_commutator_of_model G _ _ Φ K Q X _ ρ ↥U33.QA.originalSubgroup inferInstance h hρ
      hker θ sylowU33 u33_conj_mem_sylow u33P u33P_normal
      (fun _ hi _ hj hiP hjP hij => u33_threeCyc hi hj hiP hjP hij) T hT
      fun t ht => (hθ (ρ t)).mpr (hTN t ht)
  have houter : ∀ T ∈ RSet Φ, (∃ t ∈ T, ρ t ∉ N) → ∃ i ∈ T, ∃ j ∈ T, Q8Rel i j ∧
      (∀ t ∈ T, t ∈ q8Span i j) ∧ i ∈ commutator G ∧ ρ j ∉ N := by
    intro T hT hout
    obtain ⟨e⟩ := h.nonempty_q8 hT
    obtain ⟨i, hi, j, hj, hij, hspan, hiN, hjN⟩ := exists_q8Pair_of_index_two e
      (p := fun t => ρ t ∈ N) (fun x _ y _ => by
        simp only [map_mul]
        exact Subgroup.mul_mem_iff_of_index_two hidx) hout
    obtain ⟨g, hgP, hq⟩ :=
      h.exists_model_pair hker θ.toMonoidHom θ.injective sylowU33 u33_conj_mem_sylow hT hi hij
    simp only [MulEquiv.coe_toMonoidHom] at hgP hq
    obtain ⟨n, hn1, hn2⟩ := u33_conjMul (hgP i hi) (hgP j hj) ((hconjP g _).mpr hiN)
      (fun h1 => hjN ((hconjP g _).mp h1)) hq
    set φ : G →* ↥U33.QA.originalSubgroup :=
      (MulAut.conj g⁻¹).toMonoidHom.comp (θ.toMonoidHom.comp ρ) with hφ
    have hφx : ∀ x : G, φ x = g⁻¹ * θ (ρ x) * g := fun x => by
      simp [hφ, MulAut.conj_apply]
    rw [← hφx, ← hφx] at hn1 hn2
    obtain ⟨w, hw, hwe⟩ := exists_of_mem_q8Span_map φ hn1
    refine ⟨i, hi, j, hj, hij, hspan, ?_, hjN⟩
    refine h.mem_commutator_of_conjMul hρ hker hT hi hj hspan
      (n := θ.symm (g * n * g⁻¹)) ?_ ?_
    · rw [pullback_conj θ (a := ρ i) (b := ρ w) (by rw [← hφx, ← hφx, hwe])]
      exact Subgroup.mem_map_of_mem ρ (mem_of_mem_q8Span hi hj hw)
    · rcases hn2 with h2 | h2
      · left
        rw [← map_mul ρ j i]
        exact pullback_conj θ (by rw [← hφx, ← hφx, h2, map_mul])
      · right
        rw [← map_inv ρ i, ← map_mul ρ j i⁻¹]
        exact pullback_conj θ (by rw [← hφx, ← hφx, h2, map_mul, map_inv])
  have hconj : ∀ T₁ ∈ RSet Φ, ∀ T₂ ∈ RSet Φ, (∃ t ∈ T₁, ρ t ∉ N) → (∃ t ∈ T₂, ρ t ∉ N) →
      ∃ c : G, T₁ = conjSub c T₂ := by
    intro T₁ hT₁ T₂ hT₂ hout₁ hout₂
    obtain ⟨e₁⟩ := h.nonempty_q8 hT₁
    obtain ⟨e₂⟩ := h.nonempty_q8 hT₂
    obtain ⟨i₁, hi₁, j₁, hj₁, hij₁, hspan₁⟩ := exists_q8Pair e₁
    obtain ⟨i₂, hi₂, j₂, hj₂, hij₂, hspan₂⟩ := exists_q8Pair e₂
    obtain ⟨g₁, hgP₁, hq₁⟩ :=
      h.exists_model_pair hker θ.toMonoidHom θ.injective sylowU33 u33_conj_mem_sylow hT₁ hi₁ hij₁
    obtain ⟨g₂, hgP₂, hq₂⟩ :=
      h.exists_model_pair hker θ.toMonoidHom θ.injective sylowU33 u33_conj_mem_sylow hT₂ hi₂ hij₂
    simp only [MulEquiv.coe_toMonoidHom] at hgP₁ hq₁ hgP₂ hq₂
    have hnot : ∀ (T : Subgroup G) (i j : G) (g : ↥U33.QA.originalSubgroup),
        (∀ t ∈ T, t ∈ q8Span i j) → (∃ t ∈ T, ρ t ∉ N) →
          ¬ (g⁻¹ * θ (ρ i) * g ∈ u33P ∧ g⁻¹ * θ (ρ j) * g ∈ u33P) := by
      rintro T i j g hspan ⟨t, ht, htN⟩ ⟨h1, h2⟩
      apply htN
      exact mem_of_mem_q8Span (H := N.comap ρ) ((hconjP g _).mp h1) ((hconjP g _).mp h2)
        (hspan t ht)
    obtain ⟨hu1, hu2⟩ := u33_uniqueOuter (hgP₁ i₁ hi₁) (hgP₁ j₁ hj₁) (hgP₂ i₂ hi₂) (hgP₂ j₂ hj₂)
      hq₁ hq₂ (hnot T₁ i₁ j₁ g₁ hspan₁ hout₁) (hnot T₂ i₂ j₂ g₂ hspan₂ hout₂)
    set φ₁ : G →* ↥U33.QA.originalSubgroup :=
      (MulAut.conj g₁⁻¹).toMonoidHom.comp (θ.toMonoidHom.comp ρ) with hφ₁
    set φ₂ : G →* ↥U33.QA.originalSubgroup :=
      (MulAut.conj g₂⁻¹).toMonoidHom.comp (θ.toMonoidHom.comp ρ) with hφ₂
    have hφ₁x : ∀ x : G, φ₁ x = g₁⁻¹ * θ (ρ x) * g₁ := fun x => by
      simp [hφ₁, MulAut.conj_apply]
    have hφ₂x : ∀ x : G, φ₂ x = g₂⁻¹ * θ (ρ x) * g₂ := fun x => by
      simp [hφ₂, MulAut.conj_apply]
    rw [← hφ₁x, ← hφ₂x, ← hφ₂x] at hu1
    rw [← hφ₁x, ← hφ₂x, ← hφ₂x] at hu2
    have hi₂' : φ₂ i₂ ∈ T₂.map φ₂ := Subgroup.mem_map_of_mem φ₂ hi₂
    have hj₂' : φ₂ j₂ ∈ T₂.map φ₂ := Subgroup.mem_map_of_mem φ₂ hj₂
    have hT₂' : ∀ x ∈ q8Span (φ₁ i₁) (φ₁ j₁), x ∈ T₂.map φ₂ := fun x hx =>
      mem_of_mem_q8Span (mem_of_mem_q8Span hi₂' hj₂' hu1) (mem_of_mem_q8Span hi₂' hj₂' hu2) hx
    obtain ⟨c₀, hc₀⟩ := hρ (θ.symm (g₁ * g₂⁻¹))
    refine ⟨c₀, h.eq_of_map_rho_le hker hT₁ (h.conjSub_mem_RSet hT₂ c₀) ?_⟩
    rintro _ ⟨t, ht, rfl⟩
    obtain ⟨s, hs, hst⟩ := hT₂' _ (mem_q8Span_map φ₁ (hspan₁ t ht))
    refine ⟨(MulAut.conj c₀).toMonoidHom s, Subgroup.mem_map_of_mem _ hs, ?_⟩
    apply θ.injective
    rw [hφ₁x, hφ₂x] at hst
    have hs' : θ (ρ s) = g₂ * g₁⁻¹ * θ (ρ t) * g₁ * g₂⁻¹ := by
      calc θ (ρ s) = g₂ * (g₂⁻¹ * θ (ρ s) * g₂) * g₂⁻¹ := by group
        _ = g₂ * (g₁⁻¹ * θ (ρ t) * g₁) * g₂⁻¹ := by rw [hst]
        _ = g₂ * g₁⁻¹ * θ (ρ t) * g₁ * g₂⁻¹ := by group
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, map_mul, map_inv, hc₀,
      MulEquiv.apply_symm_apply, hs']
    group
  obtain ⟨T₀, hT₀, hT₀out⟩ : ∃ T ∈ RSet Φ, ∃ t ∈ T, ρ t ∉ N := by
    by_contra hall
    push Not at hall
    have hperf : commutator G = ⊤ := h.commutator_eq_top fun T hT => hinner T hT (hall T hT)
    have hNtop : N = ⊤ := eq_top_iff.mpr fun x _ => by
      obtain ⟨g, rfl⟩ := hρ x
      exact hG'N g (hperf ▸ Subgroup.mem_top g)
    rw [hNtop, Subgroup.index_top] at hidx
    exact absurd hidx (by norm_num)
  obtain ⟨i₀, hi₀, j₀, hj₀, hij₀, hspan₀, hi₀c, hj₀N⟩ := houter T₀ hT₀ hT₀out
  have hab1 : ∀ g ∈ commutator G, Abelianization.of g = 1 := fun g hg => by
    rw [← MonoidHom.mem_ker, Abelianization.ker_of]
    exact hg
  set U : Subgroup G := (Subgroup.zpowers (Abelianization.of j₀)).comap Abelianization.of
    with hU
  have hG'U : commutator G ≤ U := fun g hg => by
    show Abelianization.of g ∈ Subgroup.zpowers (Abelianization.of j₀)
    rw [hab1 g hg]
    exact Subgroup.one_mem _
  have hT₀U : T₀ ≤ U := fun t ht =>
    mem_of_mem_q8Span (hG'U hi₀c) (Subgroup.mem_zpowers (Abelianization.of j₀)) (hspan₀ t ht)
  have hallU : ∀ T ∈ RSet Φ, T ≤ U := by
    intro T hT
    by_cases hTN : ∀ t ∈ T, ρ t ∈ N
    · exact (hinner T hT hTN).trans hG'U
    · push Not at hTN
      obtain ⟨c, rfl⟩ := hconj T hT T₀ hT₀ hTN hT₀out
      rintro _ ⟨t, ht, rfl⟩
      show Abelianization.of ((MulAut.conj c).toMonoidHom t) ∈
        Subgroup.zpowers (Abelianization.of j₀)
      have h1 : Abelianization.of ((MulAut.conj c).toMonoidHom t) = Abelianization.of t := by
        simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, map_mul, map_inv]
        rw [mul_comm (Abelianization.of c) (Abelianization.of t), mul_inv_cancel_right]
      rw [h1]
      exact hT₀U ht
  have hQU : Q ≤ U := by
    have h1 : (⨆ T ∈ RSet Φ, T) ≤ U := iSup₂_le hallU
    rw [h.iSup_RSet_eq_top] at h1
    exact le_top.trans h1
  have hQG' : Q ≤ commutator G := by
    intro q hq
    have h1 : Abelianization.of q ∈ Subgroup.zpowers (Abelianization.of j₀) := hQU hq
    have hsq : Abelianization.of j₀ * Abelianization.of j₀ = 1 := by
      rw [← map_mul, ← sq, ← hij₀.2.2.1, map_pow, hab1 i₀ hi₀c, one_pow]
    rcases eq_one_or_eq_of_mem_zpowers_of_mul_self hsq h1 with h2 | h2
    · rw [← Abelianization.ker_of, MonoidHom.mem_ker]
      exact h2
    · exfalso
      have h3 : j₀⁻¹ * q ∈ commutator G := by
        rw [← Abelianization.ker_of, MonoidHom.mem_ker, map_mul, map_inv, h2, inv_mul_cancel]
      have h4 := hG'N _ h3
      have hρq : ρ q = 1 := by
        rw [← MonoidHom.mem_ker, hker]
        exact hq
      rw [map_mul, map_inv, hρq, mul_one, Subgroup.inv_mem_iff] at h4
      exact hj₀N h4
  apply h.ne_bot
  rw [eq_bot_iff, ← hdisj]
  intro q hq
  exact Subgroup.mem_inf.mpr ⟨hQG' hq, hq⟩

end Row

end CFSG.ClassicalInvolution.Q3.PhilipHall.Thm3Step.S5
