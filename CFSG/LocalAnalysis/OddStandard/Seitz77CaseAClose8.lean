module

public import CFSG.LocalAnalysis.OddStandard.Seitz77CaseAClose7

public section

namespace CFSG.OddStandard.Seitz77

open Subgroup CFSG.Open CFSG.ABGLocalTools CFSG.LocalAnalysis.ComponentInitial.FieldFourCover

section Ext

variable {G : Type*} [Group G] {M : Type*} [Group M] {T : Subgroup G}

open Classical in
@[expose] noncomputable def extFun (f : ↥T →* M) : G → M :=
  fun g => if hg : g ∈ T then f ⟨g, hg⟩ else 1

theorem extFun_apply (f : ↥T →* M) {g : G} (hg : g ∈ T) : extFun f g = f ⟨g, hg⟩ :=
  dite_eq_left hg

theorem extFun_mul (f : ↥T →* M) {x y : G} (hx : x ∈ T) (hy : y ∈ T) :
    extFun f (x * y) = extFun f x * extFun f y := by
  rw [extFun_apply f (T.mul_mem hx hy), extFun_apply f hx, extFun_apply f hy]
  exact map_mul f ⟨x, hx⟩ ⟨y, hy⟩

end Ext

theorem conjSub_inf_centralizer {G : Type} [Group G] (δ b : G) (W : Subgroup G) :
    conjSub δ W ⊓ centralizer ({b} : Set G) =
      (W ⊓ centralizer ({δ⁻¹ * b * δ} : Set G)).map (MulAut.conj δ).toMonoidHom := by
  ext x
  rw [mem_inf, mem_conjSub_iff, mem_centralizer_singleton_iff, mem_map_conj_iff, mem_inf,
    mem_centralizer_singleton_iff]
  refine and_congr_right fun _ => ?_
  constructor
  · intro h
    calc δ⁻¹ * x * δ * (δ⁻¹ * b * δ) = δ⁻¹ * (x * b) * δ := by group
      _ = δ⁻¹ * (b * x) * δ := by rw [h]
      _ = δ⁻¹ * b * δ * (δ⁻¹ * x * δ) := by group
  · intro h
    calc x * b = δ * (δ⁻¹ * x * δ * (δ⁻¹ * b * δ)) * δ⁻¹ := by group
      _ = δ * (δ⁻¹ * b * δ * (δ⁻¹ * x * δ)) * δ⁻¹ := by rw [h]
      _ = b * x := by group


theorem mem_normalizer_of_conjSub_eq {G : Type} [Group G] {W : Subgroup G} {δ₁ δ₂ : G}
    (h : conjSub δ₁ W = conjSub δ₂ W) : δ₂⁻¹ * δ₁ ∈ normalizer (W : Set G) := by
  rw [mem_normalizer_iff]
  intro y
  have hx := SetLike.ext_iff.mp h (δ₁ * y * δ₁⁻¹)
  rw [mem_conjSub_iff, mem_conjSub_iff] at hx
  have e1 : δ₁⁻¹ * (δ₁ * y * δ₁⁻¹) * δ₁ = y := by group
  have e2 : δ₂⁻¹ * (δ₁ * y * δ₁⁻¹) * δ₂ = (δ₂⁻¹ * δ₁) * y * (δ₂⁻¹ * δ₁)⁻¹ := by group
  rw [e1, e2] at hx
  exact hx

theorem conjSub_one {G : Type} [Group G] (W : Subgroup G) : conjSub (1 : G) W = W := by
  ext x
  rw [mem_conjSub_iff]
  simp

section Split3

variable {G : Type} [Group G] [Finite G] {A : Subgroup G} {d : Datum A} {F : Type} [Field F]
  [Finite F] [CharP F 2] {W S₁ S₀ W₀ : Subgroup G} {ι : G → F × F} {κ : G → F}
  {φ : G → RingAut F} (S : SylowA d W S₁ S₀ W₀ ι κ φ)

include S

namespace SylowA

variable {T : Subgroup G} {δ : G}

theorem card_cent_le (hle : conjSub δ W ≤ S₀) (hκ : ∀ b : F, ∃ w ∈ conjSub δ W, κ w = b)
    (D : Delta S₁ T δ) (hinf : W ⊓ conjSub δ W = W₀) {b : G} (hb : b ∈ hat D) (hbS₀ : b ∉ S₀) :
    Nat.card ↥(W ⊓ centralizer ({b} : Set G)) ≤ 16 ∧
      Nat.card ↥(conjSub δ W ⊓ centralizer ({b} : Set G)) ≤ 16 := by
  rcases (mem_hat_iff D).1 hb with hbS₁ | hbδ
  · refine ⟨S.card_fix_le b hbS₁ hbS₀, ?_⟩
    rw [conjSub_inf_centralizer, card_map_conj]
    refine S.card_fix_le _ ?_ ?_
    · rw [D.norm]
      simpa [mul_assoc] using hbS₁
    · intro h
      apply hbS₀
      rw [S.norm_S₀_delta D hle hκ] at h
      simpa [mul_assoc] using h
  · have hb' : b = δ * (δ⁻¹ * b) := by group
    have hW1 : ∀ w ∈ W, b * w * b⁻¹ ∈ conjSub δ W := by
      intro w hw
      have h1 : (δ⁻¹ * b) * w * (δ⁻¹ * b)⁻¹ ∈ W := S.normal_W hbδ hw
      have e1 : b * w * b⁻¹ = δ * ((δ⁻¹ * b) * w * (δ⁻¹ * b)⁻¹) * δ⁻¹ := by group
      rw [e1]
      exact conj_mem_conjSub h1
    have hW2 : ∀ w ∈ conjSub δ W, b * w * b⁻¹ ∈ W := by
      intro w hw
      have h1 : δ⁻¹ * w * δ ∈ W := mem_conjSub_iff.1 hw
      have hs : δ * (δ⁻¹ * b) * δ ∈ S₁ := by
        have e2 : δ * (δ⁻¹ * b) * δ = (δ * δ) * (δ⁻¹ * (δ⁻¹ * b) * δ) := by group
        rw [e2]
        refine S₁.mul_mem D.sq_mem ?_
        have e4 : δ * (δ⁻¹ * (δ⁻¹ * b) * δ) * δ⁻¹ = δ⁻¹ * b := by group
        exact (D.norm _).2 (by rw [e4]; exact hbδ)
      have h2 := S.normal_W hs h1
      have e3 : b * w * b⁻¹ = (δ * (δ⁻¹ * b) * δ) * (δ⁻¹ * w * δ) * (δ * (δ⁻¹ * b) * δ)⁻¹ := by
        group
      rw [e3]
      exact h2
    refine ⟨?_, ?_⟩
    · have hsub : W ⊓ centralizer ({b} : Set G) ≤ W₀ := by
        rw [← hinf]
        refine fun w hw => ⟨hw.1, ?_⟩
        have hc : w * b = b * w := mem_centralizer_singleton_iff.mp hw.2
        have h2 : b * w * b⁻¹ = w := by rw [mul_inv_eq_iff_eq_mul]; exact hc.symm
        have h3 := hW1 w hw.1
        rwa [h2] at h3
      exact (Subgroup.card_le_of_le hsub).trans S.card_W₀.le
    · have hsub : conjSub δ W ⊓ centralizer ({b} : Set G) ≤ W₀ := by
        rw [← hinf]
        refine fun w hw => ⟨?_, hw.1⟩
        have hc : w * b = b * w := mem_centralizer_singleton_iff.mp hw.2
        have h2 : b * w * b⁻¹ = w := by rw [mul_inv_eq_iff_eq_mul]; exact hc.symm
        have h3 := hW2 w hw.1
        rwa [h2] at h3
      exact (Subgroup.card_le_of_le hsub).trans S.card_W₀.le


theorem elem_le_S₀ (hle : conjSub δ W ≤ S₀) (hκ : ∀ b : F, ∃ w ∈ conjSub δ W, κ w = b)
    (D : Delta S₁ T δ) (hinf : W ⊓ conjSub δ W = W₀) {e : ↥S₀ ≃* ↥(unipAll F)}
    (E : SplitEq W S₀ κ δ e) {B : Subgroup G} (hBhat : B ≤ hat D) (hab : IsElemAbelian 2 B)
    (hB : Nat.card B = 2 ^ 8) : B ≤ S₀ := by
  by_contra hnot
  obtain ⟨b, hbB, hbS₀⟩ := Set.not_subset.mp hnot
  let ρ := conjAutHom e (hat D) (S.hat_norm_S₀ D hle hκ)
  let Φ' : ↥(hat D) →* RingAut F × Multiplicative (ZMod 2) :=
    (fieldHom.comp ρ).prod (swapHom.comp ρ)
  have hmem : ∀ x : ↥(hat D), (x : G) ∈ S₀ ↔ Φ' x = 1 := fun x =>
    (S.mem_S₀_iff_rho hle hκ D E x).trans Prod.mk_eq_one.symm
  have hB64 : 64 ≤ Nat.card ↥(B ⊓ S₀) := by
    have hmul : ∀ x ∈ B, ∀ y ∈ B, extFun Φ' (x * y) = extFun Φ' x * extFun Φ' y :=
      fun x hx y hy => extFun_mul Φ' (hBhat hx) (hBhat hy)
    have him : (extFun Φ' '' (B : Set G)).ncard ≤ 4 := by
      have hfin : Finite (RingAut F) := ringAut_finite
      have hsub : extFun Φ' '' (B : Set G) ⊆
          {a : RingAut F | a * a = 1} ×ˢ (Set.univ : Set (Multiplicative (ZMod 2))) := by
        rintro _ ⟨x, hx, rfl⟩
        rw [extFun_apply Φ' (hBhat hx)]
        refine ⟨?_, Set.mem_univ _⟩
        have hxx : (⟨x, hBhat hx⟩ : ↥(hat D)) * ⟨x, hBhat hx⟩ = 1 :=
          Subtype.ext (mul_self_of_isElemAbelian_two hab hx)
        have h1 := congrArg (fun z : ↥(hat D) => fieldHom (ρ z)) hxx
        simp only [map_mul, map_one] at h1
        exact h1
      calc (extFun Φ' '' (B : Set G)).ncard
          ≤ ({a : RingAut F | a * a = 1} ×ˢ
              (Set.univ : Set (Multiplicative (ZMod 2)))).ncard :=
            Set.ncard_le_ncard hsub (Set.toFinite _)
        _ = Set.ncard {a : RingAut F | a * a = 1} * 2 := by
            rw [Set.ncard_prod, Set.ncard_univ, Nat.card_congr Multiplicative.toAdd,
              Nat.card_zmod]
        _ ≤ 2 * 2 := Nat.mul_le_mul (ringAut_card_sq_eq_one_le S.card_F) le_rfl
    have h := le_card_fiber_of_partial_hom B (extFun Φ') hmul (a := 256) (b := 4)
      (by rw [hB]; norm_num) him
    have hfib : Nat.card {x : G // x ∈ B ∧ extFun Φ' x = 1} = Nat.card ↥(B ⊓ S₀) := by
      refine Nat.card_congr (Equiv.subtypeEquivRight fun x => ?_)
      rw [mem_inf]
      refine and_congr_right fun hx => ?_
      rw [extFun_apply Φ' (hBhat hx), ← hmem ⟨x, hBhat hx⟩]
    rw [hfib] at h
    omega
  have hcases : B ⊓ S₀ ≤ W ∨ B ⊓ S₀ ≤ conjSub δ W := by
    let E' : Subgroup ↥(unipAll F) := ((B ⊓ S₀).subgroupOf S₀).map e.toMonoidHom
    have hE' : ∀ g ∈ E', g * g = 1 := by
      rintro _ ⟨z, hz, rfl⟩
      have hz2 : z * z = 1 :=
        Subtype.ext (mul_self_of_isElemAbelian_two hab (mem_subgroupOf.mp hz).1)
      show e z * e z = 1
      rw [← map_mul, hz2, map_one]
    rcases le_radOne_or_le_radTwo E' hE' with h | h
    · left
      intro x hx
      have : e ⟨x, hx.2⟩ ∈ E' := ⟨⟨x, hx.2⟩, mem_subgroupOf.mpr hx, rfl⟩
      exact (E.hW ⟨x, hx.2⟩).2 (h this)
    · right
      intro x hx
      have : e ⟨x, hx.2⟩ ∈ E' := ⟨⟨x, hx.2⟩, mem_subgroupOf.mpr hx, rfl⟩
      exact (E.hW' ⟨x, hx.2⟩).2 (h this)
  have hcent : B ⊓ S₀ ≤ centralizer ({b} : Set G) := fun x hx =>
    mem_centralizer_singleton_iff.mpr (comm_of_isElemAbelian_two hab hx.1 hbB)
  obtain ⟨h16, h16'⟩ := S.card_cent_le hle hκ D hinf (hBhat hbB) hbS₀
  rcases hcases with h | h
  · have := Subgroup.card_le_of_le (le_inf h hcent : B ⊓ S₀ ≤ W ⊓ centralizer ({b} : Set G))
    omega
  · have := Subgroup.card_le_of_le
      (le_inf h hcent : B ⊓ S₀ ≤ conjSub δ W ⊓ centralizer ({b} : Set G))
    omega


omit [Finite G] in
theorem elem_eq (hle : conjSub δ W ≤ S₀) {e : ↥S₀ ≃* ↥(unipAll F)}
    (E : SplitEq W S₀ κ δ e) {B : Subgroup G} (hBS₀ : B ≤ S₀) (hab : IsElemAbelian 2 B)
    (hB : Nat.card B = 2 ^ 8) :
    B = W ∨ B = conjSub δ W := by
  classical
  let E' : Subgroup ↥(unipAll F) := (B.subgroupOf S₀).map e.toMonoidHom
  have hE' : ∀ g ∈ E', g * g = 1 := by
    rintro _ ⟨z, hz, rfl⟩
    have hz2 : z * z = 1 := Subtype.ext (mul_self_of_isElemAbelian_two hab (mem_subgroupOf.mp hz))
    show e z * e z = 1
    rw [← map_mul, hz2, map_one]
  have hcard : Nat.card E' = Nat.card F ^ 2 := by
    rw [Subgroup.card_map_of_injective e.injective,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hBS₀).toEquiv, hB, S.card_F]
    norm_num
  have hmemE' : ∀ x (hx : x ∈ S₀), x ∈ B ↔ e ⟨x, hx⟩ ∈ E' := by
    intro x hx
    constructor
    · intro hxB
      exact ⟨⟨x, hx⟩, mem_subgroupOf.mpr hxB, rfl⟩
    · rintro ⟨z, hz, hze⟩
      have : z = ⟨x, hx⟩ := e.injective hze
      rw [this] at hz
      exact mem_subgroupOf.mp hz
  rcases eq_radOne_or_radTwo_of_card hE' hcard with h | h
  · left
    ext x
    constructor
    · intro hxB
      have hx := hBS₀ hxB
      exact (E.hW ⟨x, hx⟩).2 (h ▸ (hmemE' x hx).1 hxB)
    · intro hxW
      have hx := S.W_le_S₀ hxW
      exact (hmemE' x hx).2 (h ▸ (E.hW ⟨x, hx⟩).1 hxW)
  · right
    ext x
    constructor
    · intro hxB
      have hx := hBS₀ hxB
      exact (E.hW' ⟨x, hx⟩).2 (h ▸ (hmemE' x hx).1 hxB)
    · intro hxW
      have hx := hle hxW
      exact (hmemE' x hx).2 (h ▸ (E.hW' ⟨x, hx⟩).1 hxW)


theorem hat_eq (hT : IsPGroup 2 T) (hST : S₁ ≤ T) (hle : conjSub δ W ≤ S₀)
    (hκ : ∀ b : F, ∃ w ∈ conjSub δ W, κ w = b) (D : Delta S₁ T δ)
    (hinf : W ⊓ conjSub δ W = W₀) {e : ↥S₀ ≃* ↥(unipAll F)} (E : SplitEq W S₀ κ δ e) :
    hat D = T := by
  by_contra hne
  obtain ⟨δ', hδ'T, hδ'N, hδ'not, -⟩ := exists_normalizing_sq_mem hT (hat_le D hST) hne
  have hWle : conjSub δ' W ≤ hat D := fun x hx => by
    have h1 : δ'⁻¹ * x * δ' ∈ W := mem_conjSub_iff.1 hx
    have h2 : δ' * (δ'⁻¹ * x * δ') * δ'⁻¹ ∈ hat D := (hδ'N _).1 (S₁_le_hat D (S.W_le_S₁ h1))
    simpa [mul_assoc] using h2
  obtain ⟨hab, hsq⟩ := S.elem_conjSub (δ := δ')
  have hE : IsElemAbelian 2 (conjSub δ' W) := isElemAbelian_of_forall_two hab hsq
  have hcard : Nat.card (conjSub δ' W) = 2 ^ 8 := S.card_conjSub
  have hle' := S.elem_le_S₀ hle hκ D hinf E hWle hE hcard
  apply hδ'not
  rcases S.elem_eq hle E hle' hE hcard with h | h
  · have h' : conjSub δ' W = conjSub 1 W := by rw [conjSub_one]; exact h
    have := mem_normalizer_of_conjSub_eq h'
    rw [inv_one, one_mul] at this
    exact S₁_le_hat D (S.mem_S₁_of_mem_normalizer hT hST hδ'T this)
  · have hmem := mem_normalizer_of_conjSub_eq h
    exact Or.inr (S.mem_S₁_of_mem_normalizer hT hST (T.mul_mem (T.inv_mem D.mem) hδ'T) hmem)

end SylowA

end Split3

end CFSG.OddStandard.Seitz77
