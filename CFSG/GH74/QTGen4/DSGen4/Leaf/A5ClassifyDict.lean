module

public import CFSG.GH74.QTGen4.DSGen4.Leaf.A5ClassifyCore
public import Certificates.Data.A5GL42

public section

namespace CFSG.GH74.QTGen4.DSGen4

open scoped commutatorElement Matrix
open Certificates.A5GL42 (Mat4 Vec4 commSet fixSet)

variable {G : Type} [Group G] {P E K : Subgroup G}

noncomputable def img (F : ElemFrame P E K) (X : Subgroup G) : Finset Vec4 :=
  open Classical in
  Finset.univ.filter fun v => ∃ e : ↥E, (e : G) ∈ X ∧ Multiplicative.toAdd (F.φ e) = v

theorem mem_img {F : ElemFrame P E K} {X : Subgroup G} {v : Vec4} :
    v ∈ img F X ↔ ∃ e : ↥E, (e : G) ∈ X ∧ Multiplicative.toAdd (F.φ e) = v := by
  classical
  simp [img]

theorem zero_mem_img (F : ElemFrame P E K) (X : Subgroup G) : (0 : Vec4) ∈ img F X :=
  mem_img.mpr ⟨1, X.one_mem, by simp⟩

theorem add_mem_img (F : ElemFrame P E K) (X : Subgroup G) {u w : Vec4} (hu : u ∈ img F X)
    (hw : w ∈ img F X) : u + w ∈ img F X := by
  obtain ⟨e₁, h₁, rfl⟩ := mem_img.mp hu
  obtain ⟨e₂, h₂, rfl⟩ := mem_img.mp hw
  exact mem_img.mpr ⟨e₁ * e₂, X.mul_mem h₁ h₂, by simp⟩

theorem img_mono (F : ElemFrame P E K) {X Y : Subgroup G} (h : X ≤ Y) : img F X ⊆ img F Y := by
  intro v hv
  obtain ⟨e, he, rfl⟩ := mem_img.mp hv
  exact mem_img.mpr ⟨e, h he, rfl⟩

theorem img_bot_of_ker (F : ElemFrame P E K) : img F K = {0} := by
  ext v
  rw [Finset.mem_singleton]
  constructor
  · intro hv
    obtain ⟨e, he, rfl⟩ := mem_img.mp hv
    have := (F.ker e).mpr he
    rw [this]; rfl
  · rintro rfl
    exact zero_mem_img F K

theorem img_top (F : ElemFrame P E K) : img F E = Finset.univ := by
  ext v
  simp only [Finset.mem_univ, iff_true]
  obtain ⟨e, he⟩ := F.surj (Multiplicative.ofAdd v)
  exact mem_img.mpr ⟨e, e.2, by rw [he]; rfl⟩

theorem mem_iff_img (F : ElemFrame P E K) {X : Subgroup G} (hKX : K ≤ X) (e : ↥E) :
    (e : G) ∈ X ↔ Multiplicative.toAdd (F.φ e) ∈ img F X := by
  constructor
  · intro he
    exact mem_img.mpr ⟨e, he, rfl⟩
  · intro hv
    obtain ⟨e', he', hee'⟩ := mem_img.mp hv
    have h1 : F.φ e' = F.φ e := Multiplicative.toAdd.injective hee'
    have h2 : F.φ (e'⁻¹ * e) = 1 := by
      apply Multiplicative.toAdd.injective
      rw [map_mul, map_inv, toAdd_mul, toAdd_inv, hee', toAdd_one]
      exact neg_add_cancel _
    have h3 : ((e'⁻¹ * e : ↥E) : G) ∈ K := (F.ker _).mp h2
    have h4 : (e : G) = (e' : G) * ((e'⁻¹ * e : ↥E) : G) := by simp
    rw [h4]
    exact X.mul_mem he' (hKX h3)

theorem ext_of_img (F : ElemFrame P E K) {X Y : Subgroup G} (hKX : K ≤ X) (hXE : X ≤ E)
    (hKY : K ≤ Y) (hYE : Y ≤ E) (h : img F X = img F Y) : X = Y := by
  apply le_antisymm
  · intro g hg
    have hgE := hXE hg
    have := (mem_iff_img F hKX ⟨g, hgE⟩).mp hg
    rw [h] at this
    exact (mem_iff_img F hKY ⟨g, hgE⟩).mpr this
  · intro g hg
    have hgE := hYE hg
    have := (mem_iff_img F hKY ⟨g, hgE⟩).mp hg
    rw [← h] at this
    exact (mem_iff_img F hKX ⟨g, hgE⟩).mpr this

def pre (F : ElemFrame P E K) (S : Finset Vec4) (h0 : 0 ∈ S)
    (hS : ∀ u ∈ S, ∀ w ∈ S, u + w ∈ S) : Subgroup G where
  carrier := {g | ∃ e : ↥E, (e : G) = g ∧ Multiplicative.toAdd (F.φ e) ∈ S}
  one_mem' := ⟨1, rfl, by simpa using h0⟩
  mul_mem' := by
    rintro _ _ ⟨e₁, rfl, h₁⟩ ⟨e₂, rfl, h₂⟩
    exact ⟨e₁ * e₂, rfl, by simpa using hS _ h₁ _ h₂⟩
  inv_mem' := by
    rintro _ ⟨e, rfl, h⟩
    refine ⟨e⁻¹, rfl, ?_⟩
    have : Multiplicative.toAdd (F.φ e⁻¹) = Multiplicative.toAdd (F.φ e) := by
      rw [map_inv, toAdd_inv]
      funext i
      have : ∀ z : ZMod 2, -z = z := by decide
      exact this _
    rw [this]; exact h

theorem mem_pre {F : ElemFrame P E K} {S : Finset Vec4} {h0 : 0 ∈ S}
    {hS : ∀ u ∈ S, ∀ w ∈ S, u + w ∈ S} {g : G} :
    g ∈ pre F S h0 hS ↔ ∃ e : ↥E, (e : G) = g ∧ Multiplicative.toAdd (F.φ e) ∈ S := Iff.rfl

theorem pre_le (F : ElemFrame P E K) {S : Finset Vec4} (h0 : 0 ∈ S)
    (hS : ∀ u ∈ S, ∀ w ∈ S, u + w ∈ S) : pre F S h0 hS ≤ E := by
  rintro _ ⟨e, rfl, -⟩
  exact e.2

theorem img_pre (F : ElemFrame P E K) {S : Finset Vec4} (h0 : 0 ∈ S)
    (hS : ∀ u ∈ S, ∀ w ∈ S, u + w ∈ S) : img F (pre F S h0 hS) = S := by
  ext v
  constructor
  · intro hv
    obtain ⟨e, ⟨e', he', hev⟩, rfl⟩ := mem_img.mp hv
    have : e' = e := Subtype.ext he'
    rw [← this]; exact hev
  · intro hv
    obtain ⟨e, he⟩ := F.surj (Multiplicative.ofAdd v)
    refine mem_img.mpr ⟨e, ⟨e, rfl, ?_⟩, by rw [he]; rfl⟩
    rw [he]; exact hv

theorem relIndex_eq_card_img (F : ElemFrame P E K) {X : Subgroup G} (hKX : K ≤ X) (hXE : X ≤ E) :
    K.relIndex X = (img F X).card := by
  classical
  let ψ : ↥X →* Multiplicative Vec4 := F.φ.comp (Subgroup.inclusion hXE)
  have hker : ψ.ker = K.subgroupOf X := by
    ext x
    simp only [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    exact F.ker (Subgroup.inclusion hXE x)
  have h1 : K.relIndex X = Nat.card ψ.range := by
    rw [Subgroup.relIndex, ← hker, Subgroup.index_ker]
  rw [h1]
  have hrange : (ψ.range : Set (Multiplicative Vec4)) =
      Multiplicative.ofAdd '' (img F X : Set Vec4) := by
    ext z
    simp only [SetLike.mem_coe, MonoidHom.mem_range, Set.mem_image, Finset.mem_coe, mem_img]
    constructor
    · rintro ⟨x, rfl⟩
      exact ⟨Multiplicative.toAdd (F.φ (Subgroup.inclusion hXE x)),
        ⟨Subgroup.inclusion hXE x, x.2, rfl⟩, rfl⟩
    · rintro ⟨v, ⟨e, he, rfl⟩, rfl⟩
      exact ⟨⟨e, he⟩, rfl⟩
  calc Nat.card ψ.range = Nat.card (ψ.range : Set (Multiplicative Vec4)) := rfl
    _ = Nat.card ((Multiplicative.ofAdd '' (img F X : Set Vec4) : Set (Multiplicative Vec4))) := by
        rw [hrange]
    _ = Nat.card (img F X : Set Vec4) :=
        Nat.card_image_of_injective Multiplicative.ofAdd.injective _
    _ = (img F X).card := by simp [Nat.card_eq_fintype_card]

theorem exists_mul_inv_mem_of_mem_sup {T Q P : Subgroup G} (hTP : T ≤ P)
    (hQP : P ≤ Subgroup.normalizer (Q : Set G)) : ∀ s ∈ T ⊔ Q, ∃ t ∈ T, s * t⁻¹ ∈ Q := by
  have hconj : ∀ t ∈ T, ∀ q ∈ Q, t * q * t⁻¹ ∈ Q := fun t ht q hq =>
    (Subgroup.mem_normalizer_iff.mp (hQP (hTP ht)) q).mp hq
  let QT : Subgroup G :=
    { carrier := {p | ∃ t ∈ T, p * t⁻¹ ∈ Q}
      one_mem' := ⟨1, T.one_mem, by simpa using Q.one_mem⟩
      mul_mem' := by
        rintro p₁ p₂ ⟨t₁, ht₁, h₁⟩ ⟨t₂, ht₂, h₂⟩
        refine ⟨t₁ * t₂, T.mul_mem ht₁ ht₂, ?_⟩
        have : p₁ * p₂ * (t₁ * t₂)⁻¹ = (p₁ * t₁⁻¹) * (t₁ * (p₂ * t₂⁻¹) * t₁⁻¹) := by group
        rw [this]
        exact Q.mul_mem h₁ (hconj t₁ ht₁ _ h₂)
      inv_mem' := by
        rintro p ⟨t, ht, h⟩
        refine ⟨t⁻¹, T.inv_mem ht, ?_⟩
        have : p⁻¹ * (t⁻¹)⁻¹ = t⁻¹ * (p * t⁻¹)⁻¹ * t⁻¹⁻¹ := by group
        rw [this]
        exact hconj t⁻¹ (T.inv_mem ht) _ (Q.inv_mem h) }
  have hle : T ⊔ Q ≤ QT := by
    refine sup_le ?_ ?_
    · intro t ht
      exact ⟨t, ht, by simpa using Q.one_mem⟩
    · intro q hq
      exact ⟨1, T.one_mem, by simpa using hq⟩
  intro s hs
  exact hle hs

section Comm

variable {F : ElemFrame P E K}

theorem comm_mem_pre (hPE : P ≤ Subgroup.normalizer (E : Set G)) {Y T : Subgroup G}
    (hYE : Y ≤ E) (hTP : T ≤ P) {A : Finset Mat4}
    (hAT : ∀ t : ↥P, (t : G) ∈ T → glMat (F.M t) ∈ A)
    {h0 : 0 ∈ commSet A (img F Y)}
    {hadd : ∀ u ∈ commSet A (img F Y), ∀ w ∈ commSet A (img F Y), u + w ∈ commSet A (img F Y)} :
    ⁅Y, T⁆ ≤ pre F (commSet A (img F Y)) h0 hadd := by
  rw [Subgroup.commutator_le]
  intro y hy t ht
  have hyE : y ∈ E := hYE hy
  let c : ↥E := ⟨⁅y, t⁆, ElemFrame.comm_right_mem hPE (hTP ht) hyE⟩
  refine ⟨c, rfl, ?_⟩
  have hφ := F.phi_comm hPE ⟨t, hTP ht⟩ ⟨y, hyE⟩ c rfl
  rw [hφ]
  unfold commSet
  rw [Finset.mem_image]
  exact ⟨(glMat (F.M ⟨t, hTP ht⟩), Multiplicative.toAdd (F.φ ⟨y, hyE⟩)),
    Finset.mem_product.mpr ⟨hAT ⟨t, hTP ht⟩ ht, mem_img.mpr ⟨⟨y, hyE⟩, hy, rfl⟩⟩, rfl⟩

theorem img_comm (hPE : P ≤ Subgroup.normalizer (E : Set G)) {Y T : Subgroup G}
    (hYE : Y ≤ E) (hTP : T ≤ P) {A : Finset Mat4}
    (hAT : ∀ t : ↥P, (t : G) ∈ T → glMat (F.M t) ∈ A)
    (hTA : ∀ a ∈ A, ∃ t : ↥P, (t : G) ∈ T ∧ glMat (F.M t) = a)
    (h0 : 0 ∈ commSet A (img F Y))
    (hadd : ∀ u ∈ commSet A (img F Y), ∀ w ∈ commSet A (img F Y), u + w ∈ commSet A (img F Y)) :
    img F ⁅Y, T⁆ = commSet A (img F Y) := by
  apply Finset.Subset.antisymm
  · intro v hv
    have := img_mono F (comm_mem_pre hPE hYE hTP hAT (h0 := h0) (hadd := hadd)) hv
    rwa [img_pre] at this
  · intro u hu
    unfold commSet at hu
    obtain ⟨⟨a, v⟩, hmem, rfl⟩ := Finset.mem_image.mp hu
    obtain ⟨ha, hv⟩ := Finset.mem_product.mp hmem
    obtain ⟨t, htT, rfl⟩ := hTA a ha
    obtain ⟨y, hyY, rfl⟩ := mem_img.mp hv
    let c : ↥E := ⟨⁅(y : G), (t : G)⁆, ElemFrame.comm_right_mem hPE t.2 y.2⟩
    have hφ := F.phi_comm hPE t y c rfl
    refine mem_img.mpr ⟨c, Subgroup.commutator_mem_commutator hyY htT, ?_⟩
    simpa using hφ

theorem img_comm_sup (hPE : P ≤ Subgroup.normalizer (E : Set G)) {Y T : Subgroup G}
    (hKE : K ≤ E) (hYE : Y ≤ E) (hTP : T ≤ P) {A : Finset Mat4}
    (hAT : ∀ t : ↥P, (t : G) ∈ T → glMat (F.M t) ∈ A)
    (hTA : ∀ a ∈ A, ∃ t : ↥P, (t : G) ∈ T ∧ glMat (F.M t) = a)
    (h0 : 0 ∈ commSet A (img F Y))
    (hadd : ∀ u ∈ commSet A (img F Y), ∀ w ∈ commSet A (img F Y), u + w ∈ commSet A (img F Y)) :
    img F (⁅Y, T⁆ ⊔ K) = commSet A (img F Y) := by
  apply Finset.Subset.antisymm
  · have hle : ⁅Y, T⁆ ⊔ K ≤ pre F (commSet A (img F Y)) h0 hadd := by
      refine sup_le (comm_mem_pre hPE hYE hTP hAT) ?_
      intro k hk
      refine ⟨⟨k, hKE hk⟩, rfl, ?_⟩
      rw [(F.ker ⟨k, hKE hk⟩).mpr hk, toAdd_one]
      exact h0
    intro v hv
    have := img_mono F hle hv
    rwa [img_pre] at this
  · rw [← img_comm hPE hYE hTP hAT hTA h0 hadd]
    exact img_mono F le_sup_left

theorem comm_mem_K_iff (hPE : P ≤ Subgroup.normalizer (E : Set G)) {p : G} (hp : p ∈ P) {e : G}
    (he : e ∈ E) :
    ⁅e, p⁆ ∈ K ↔ glMat (F.M ⟨p, hp⟩) *ᵥ Multiplicative.toAdd (F.φ ⟨e, he⟩) =
      Multiplicative.toAdd (F.φ ⟨e, he⟩) := by
  let c : ↥E := ⟨⁅e, p⁆, ElemFrame.comm_right_mem hPE hp he⟩
  have hφ := F.phi_comm hPE ⟨p, hp⟩ ⟨e, he⟩ c rfl
  rw [← F.ker c]
  constructor
  · intro h1
    rw [h1, toAdd_one] at hφ
    exact (sub_eq_zero.mp hφ.symm).symm
  · intro h1
    apply Multiplicative.toAdd.injective
    rw [hφ, h1, sub_self, toAdd_one]

theorem comm_mem_K_iff' (hPE : P ≤ Subgroup.normalizer (E : Set G)) {p : G} (hp : p ∈ P) {e : G}
    (he : e ∈ E) :
    ⁅p, e⁆ ∈ K ↔ glMat (F.M ⟨p, hp⟩) *ᵥ Multiplicative.toAdd (F.φ ⟨e, he⟩) =
      Multiplicative.toAdd (F.φ ⟨e, he⟩) := by
  rw [← comm_mem_K_iff hPE hp he, ← commutatorElement_inv]
  exact ⟨fun h => by simpa using K.inv_mem h, fun h => K.inv_mem h⟩

end Comm

end CFSG.GH74.QTGen4.DSGen4
