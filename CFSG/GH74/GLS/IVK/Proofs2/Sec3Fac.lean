module

public import CFSG.GH74.GLS.IVK.L2.Lemma113
public import CFSG.GroupTheory.ABGDGroups.LinearCentralizers
public import CFSG.LinearAlgebra.SL2MinimalFaithfulMatrix
public import CFSG.GH74.GLS.IVK.Proofs2.OddTools
public import CFSG.GH74.GLS.IVK.Proofs2.Pgl2Three
public import CFSG.GH74.GLS.IVK.Proofs2.Sec3S4
public import CFSG.GH74.GLS.IVK.Prod.Basic

public section

open Subgroup CFSG CFSG.GH74.GLS.IVK CFSG.GorensteinWalter
open scoped commutatorElement Pointwise

namespace CFSG.GH74.GLS.IVK.Proofs2

section Sec3Fac

theorem commutator_mem_of_index_two {G : Type*} [Group G] {N : Subgroup G} (hN : N.index = 2)
    (g h : G) : ⁅g, h⁆ ∈ N := by
  have key : ∀ a b : G, a * b ∈ N ↔ (a ∈ N ↔ b ∈ N) := fun a b =>
    Subgroup.mul_mem_iff_of_index_two hN
  show g * h * g⁻¹ * h⁻¹ ∈ N
  rw [key, key, key]
  simp only [inv_mem_iff]
  tauto

theorem commutator_le_of_index_two {G : Type*} [Group G] {N : Subgroup G} (hN : N.index = 2) :
    commutator G ≤ N := by
  have : N.Normal := Subgroup.normal_of_index_eq_two hN
  rw [commutator_def, Subgroup.commutator_le]
  intro g _ h _
  exact commutator_mem_of_index_two hN g h

variable {H : Type} [Group H] [Finite H] {K₁ K₂ : Subgroup H} {F₁ F₂ : Type} [Field F₁] [Field F₂]

structure QuotData (K₂ A : Subgroup H) (F₁ : Type) [Field F₁] where
  ρ : ↥A →* PGL2 F₁
  surj : Function.Surjective ρ
  ker_iff : ∀ a : ↥A, ρ a = 1 ↔ (a : H) ∈ K₂

omit [Finite H] in
theorem QuotData.of_equiv (K₂ A : Subgroup H) [(K₂.subgroupOf A).Normal]
    (θ : ↥A ⧸ K₂.subgroupOf A ≃* PGL2 F₁) : Nonempty (QuotData K₂ A F₁) :=
  ⟨{ ρ := θ.toMonoidHom.comp (QuotientGroup.mk' (K₂.subgroupOf A))
     surj := θ.surjective.comp (QuotientGroup.mk'_surjective _)
     ker_iff := fun a => by
       simp [QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf] }⟩

namespace QuotData

variable {A : Subgroup H} (Q : QuotData K₂ A F₁)
omit [Finite H]

open Classical in
noncomputable def f (x : H) : PGL2 F₁ := if hx : x ∈ A then Q.ρ ⟨x, hx⟩ else 1

theorem f_of_mem {x : H} (hx : x ∈ A) : Q.f x = Q.ρ ⟨x, hx⟩ := by
  classical
  simp [f, hx]

theorem f_mul {x y : H} (hx : x ∈ A) (hy : y ∈ A) : Q.f (x * y) = Q.f x * Q.f y := by
  rw [f_of_mem Q (A.mul_mem hx hy), f_of_mem Q hx, f_of_mem Q hy]
  exact map_mul Q.ρ ⟨x, hx⟩ ⟨y, hy⟩

theorem f_one : Q.f 1 = 1 := by
  rw [f_of_mem Q A.one_mem]
  exact map_one Q.ρ

theorem f_inv {x : H} (hx : x ∈ A) : Q.f x⁻¹ = (Q.f x)⁻¹ := by
  rw [f_of_mem Q (A.inv_mem hx), f_of_mem Q hx]
  exact map_inv Q.ρ ⟨x, hx⟩

theorem f_eq_one_iff {x : H} (hx : x ∈ A) : Q.f x = 1 ↔ x ∈ K₂ := by
  rw [f_of_mem Q hx]
  exact Q.ker_iff ⟨x, hx⟩

theorem exists_f_eq (g : PGL2 F₁) : ∃ x ∈ A, Q.f x = g := by
  obtain ⟨a, ha⟩ := Q.surj g
  exact ⟨a, a.2, by rw [f_of_mem Q a.2]; exact ha⟩

noncomputable def imK (hK : K₁ ≤ A) : Subgroup (PGL2 F₁) :=
  (Q.ρ.comp (Subgroup.inclusion hK)).range

theorem f_mem_imK (hK : K₁ ≤ A) {a : H} (ha : a ∈ K₁) : Q.f a ∈ Q.imK hK :=
  ⟨⟨a, ha⟩, (Q.f_of_mem (hK ha)).symm⟩

theorem exists_f_K₁ (hK : K₁ ≤ A) {g : PGL2 F₁} (hg : g ∈ Q.imK hK) : ∃ a ∈ K₁, Q.f a = g := by
  obtain ⟨⟨a, ha⟩, rfl⟩ := hg
  exact ⟨a, ha, Q.f_of_mem (hK ha)⟩

end QuotData

structure PGLInput (F : Type) [Field F] (R : Subgroup (PGL2 F)) : Prop where
  outer_conj : ∀ a b : PGL2 F, a * a = 1 → b * b = 1 → a ∉ R → b ∉ R → IsConj a b
  cent : ∀ g : PGL2 F, g * g = 1 → g ∉ R →
    ∃ m : ℕ, Odd m ∧ Nat.card ↥(R ⊓ Subgroup.centralizer ({g} : Set (PGL2 F))) = 2 * m

section PGLInputProofs

variable {F : Type} [Field F]

theorem PGLInput.of_gt_three [Finite F] (hF : IsOddPrimePower (Nat.card F)) (hq3 : 3 < Nat.card F)
    {R : Subgroup (PGL2 F)} (hR : R = commutator (PGL2 F)) : PGLInput F R := by
  have hcomm := pgl2_commutator_eq_psl2_range_of_card_gt_three F hF hq3
  refine ⟨?_, ?_⟩
  · intro a b ha hb haR hbR
    have ha1 : a ≠ 1 := fun h1 => haR (h1 ▸ R.one_mem)
    have hb1 : b ≠ 1 := fun h1 => hbR (h1 ▸ R.one_mem)
    rw [hR] at haR hbR
    exact pgl2_outer_involutions_conjugate F hF hq3 ⟨ha1, by rw [pow_two]; exact ha⟩
      ⟨hb1, by rw [pow_two]; exact hb⟩ haR hbR
  · intro g hg hgR
    have hg1 : g ≠ 1 := fun h1 => hgR (h1 ▸ R.one_mem)
    have hg2 : orderOf g = 2 := orderOf_eq_prime (by rw [pow_two]; exact hg) hg1
    have hRr : R = (Matrix.ProjectiveSpecialLinearGroup.toPGL (n := Fin 2) (R := F)).range :=
      hR.trans hcomm
    obtain ⟨ε, hε1, hε⟩ : ∃ ε : ℤ, (ε = 1 ∨ ε = -1) ∧ (Nat.card F : ℤ) ≡ ε [ZMOD 4] := by
      obtain ⟨p, f, -, hpodd, -, hq⟩ := hF
      have hodd : Odd (Nat.card F) := by rw [hq]; exact hpodd.pow
      obtain ⟨t, ht⟩ := hodd
      by_cases h2 : t % 2 = 0
      · exact ⟨1, Or.inl rfl, by unfold Int.ModEq; omega⟩
      · exact ⟨-1, Or.inr rfl, by unfold Int.ModEq; omega⟩
    rw [hRr] at hgR ⊢
    obtain ⟨m, hm, ⟨ψ⟩⟩ := CFSG.ABGDGroups.pgl2_inf_centralizer_outer_involution_dihedral hF hε hε1
      hg2 hgR
    have hq3' : (3 : ℤ) < Nat.card F := by exact_mod_cast hq3
    have hm0 : m ≠ 0 := by
      rintro rfl
      rcases hε1 with rfl | rfl <;> omega
    have : NeZero m := ⟨hm0⟩
    refine ⟨m, ?_, ?_⟩
    · have hmod : (Nat.card F : ℤ) % 4 = ε % 4 := hε
      rcases hε1 with rfl | rfl <;> (rw [Nat.odd_iff]; omega)
    · rw [Nat.card_congr ψ.toEquiv, Nat.card_eq_fintype_card, DihedralGroup.card]

theorem PGLInput.of_three (e : PGL2 F ≃* Equiv.Perm (Fin 4)) {R : Subgroup (PGL2 F)}
    (hR : R.index = 2) : PGLInput F R where
  outer_conj a b ha hb haR hbR := isConj_iff.mpr (Sec3S4.s4_outer_conj e R hR ha hb haR hbR)
  cent g hg hgR := ⟨1, odd_one, by rw [Sec3S4.s4_cent_card e R hR hg hgR]⟩

end PGLInputProofs


section Image

variable {A : Subgroup H} (Q : QuotData K₂ A F₁) (h : ProdSL2 H K₁ K₂ F₁ F₂) [Finite F₁]
include h

omit [Finite H] [Finite F₁] in
theorem QuotData.card_ker (hK : K₁ ≤ A) :
    Nat.card (Q.ρ.comp (Subgroup.inclusion hK)).ker = 2 := by
  have hker : (Q.ρ.comp (Subgroup.inclusion hK)).ker = K₂.subgroupOf K₁ := by
    ext a
    simp only [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, MonoidHom.comp_apply]
    exact Q.ker_iff ⟨a, hK a.2⟩
  rw [hker, ← Subgroup.inf_subgroupOf_left K₂ K₁,
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe (inf_le_left : K₁ ⊓ K₂ ≤ K₁)).toEquiv]
  exact h.card_inter

theorem QuotData.imK_index (hK : K₁ ≤ A) : (Q.imK hK).index = 2 := by
  set φ : ↥K₁ →* PGL2 F₁ := Q.ρ.comp (Subgroup.inclusion hK) with hφ
  have hkercard : Nat.card φ.ker = 2 := Q.card_ker h hK
  have hK₁card : Nat.card ↥K₁ = Nat.card F₁ * (Nat.card F₁ ^ 2 - 1) := by
    rw [Nat.card_congr h.slEquiv₁.toEquiv]
    exact CFSG.SL2MinimalFaithful.card_specialLinearGroup_fin_two F₁
  have hPGL : Nat.card (PGL2 F₁) = Nat.card F₁ * (Nat.card F₁ ^ 2 - 1) := pgl2_card_formula F₁
  have h1 : Nat.card φ.ker * φ.ker.index = Nat.card ↥K₁ := Subgroup.card_mul_index φ.ker
  have h2 : φ.ker.index = Nat.card φ.range := Subgroup.index_ker φ
  rw [hkercard, h2, hK₁card] at h1
  have h3 : Nat.card φ.range * φ.range.index = Nat.card (PGL2 F₁) :=
    Subgroup.card_mul_index φ.range
  have : Finite φ.range := Finite.of_surjective φ.rangeRestrict φ.rangeRestrict_surjective
  have hpos : 0 < Nat.card φ.range := Nat.card_pos
  show φ.range.index = 2
  rw [hPGL, ← h1] at h3
  exact Nat.eq_of_mul_eq_mul_left hpos (by linarith)

theorem QuotData.imK_eq_commutator (hF : IsOddPrimePower (Nat.card F₁)) (hq3 : 3 < Nat.card F₁)
    (hK : K₁ ≤ A) : Q.imK hK = commutator (PGL2 F₁) := by
  have hidx := Q.imK_index h hK
  have hPGL : Nat.card (PGL2 F₁) = Nat.card F₁ * (Nat.card F₁ ^ 2 - 1) := pgl2_card_formula F₁
  have hcomm : commutator (PGL2 F₁) =
      (Matrix.ProjectiveSpecialLinearGroup.toPGL (n := Fin 2) (R := F₁)).range :=
    pgl2_commutator_eq_psl2_range_of_card_gt_three F₁ hF hq3
  have hcidx : (commutator (PGL2 F₁)).index = 2 := by
    rw [hcomm]; exact pgl2_psl2Range_index_eq_two F₁ hF
  have hle : commutator (PGL2 F₁) ≤ Q.imK hK := commutator_le_of_index_two hidx
  symm
  apply Subgroup.eq_of_le_of_card_ge hle
  have h3 : Nat.card (Q.imK hK) * (Q.imK hK).index = Nat.card (PGL2 F₁) :=
    Subgroup.card_mul_index _
  have h4 : Nat.card (commutator (PGL2 F₁)) * (commutator (PGL2 F₁)).index = Nat.card (PGL2 F₁) :=
    Subgroup.card_mul_index _
  rw [hidx] at h3
  rw [hcidx] at h4
  have h5 : Nat.card (commutator (PGL2 F₁)) * 2 = Nat.card (Q.imK hK) * 2 := by linarith
  exact (Nat.eq_of_mul_eq_mul_right (by norm_num) h5).ge

end Image


section Outer

variable {A : Subgroup H} (Q : QuotData K₂ A F₁) (h : ProdSL2 H K₁ K₂ F₁ F₂) [Finite F₁]
include h

theorem QuotData.f_w_not_mem {w : H} (hK₁A : K₁ ≤ A) (hK₂A : K₂ ≤ A) (hwA : w ∈ A)
    (hA : A = K₁ ⊔ K₂ ⊔ zpowers w) : Q.f w ∉ Q.imK hK₁A := by
  intro hw
  set R := Q.imK hK₁A with hR
  set S : Subgroup H := (R.comap Q.ρ).map A.subtype with hS
  have hAS : A ≤ S := by
    refine hA.le.trans (sup_le (sup_le ?_ ?_) ?_)
    · intro a ha
      refine ⟨⟨a, hK₁A ha⟩, ?_, rfl⟩
      show Q.ρ ⟨a, hK₁A ha⟩ ∈ R
      rw [← Q.f_of_mem (hK₁A ha)]
      exact Q.f_mem_imK hK₁A ha
    · intro b hb
      refine ⟨⟨b, hK₂A hb⟩, ?_, rfl⟩
      show Q.ρ ⟨b, hK₂A hb⟩ ∈ R
      rw [(Q.ker_iff ⟨b, hK₂A hb⟩).mpr hb]
      exact R.one_mem
    · rw [Subgroup.zpowers_le]
      refine ⟨⟨w, hwA⟩, ?_, rfl⟩
      show Q.ρ ⟨w, hwA⟩ ∈ R
      rw [← Q.f_of_mem hwA]
      exact hw
  have htop : R = ⊤ := by
    rw [eq_top_iff]
    intro g _
    obtain ⟨x, hx, rfl⟩ := Q.exists_f_eq g
    obtain ⟨a, ha, rfl⟩ := hAS hx
    show Q.f (a : H) ∈ R
    rw [Q.f_of_mem a.2]
    exact ha
  have h2 := Q.imK_index h hK₁A
  rw [← hR, htop, Subgroup.index_top] at h2
  omega

end Outer



section Facts

variable {F : Type} [Field F] [Finite F]

theorem pgl2_eq_one_of_commutes_range (g : PGL2 F)
    (hg : ∀ x ∈ (Matrix.ProjectiveSpecialLinearGroup.toPGL (n := Fin 2) (R := F)).range,
      g * x = x * g) : g = 1 := by
  let e : L2 F ≃* L2 F := MulEquiv.refl _
  apply innDiagHom_injective e
  rw [map_one]
  ext x
  apply (toPSL e).injective
  apply Matrix.ProjectiveSpecialLinearGroup.toPGL_injective
  have h1 := toPGL_toPSL_innDiagHom e g x
  have hx : g * Matrix.ProjectiveSpecialLinearGroup.toPGL (toPSL e x) =
      Matrix.ProjectiveSpecialLinearGroup.toPGL (toPSL e x) * g := hg _ ⟨toPSL e x, rfl⟩
  rw [h1, MulAut.one_apply]
  calc g * Matrix.ProjectiveSpecialLinearGroup.toPGL (toPSL e x) * g⁻¹
      = Matrix.ProjectiveSpecialLinearGroup.toPGL (toPSL e x) * g * g⁻¹ := by rw [hx]
    _ = Matrix.ProjectiveSpecialLinearGroup.toPGL (toPSL e x) := by group

theorem card_comap_eq {G G' : Type*} [Group G] [Group G'] [Finite G] (φ : G →* G') (T : Subgroup G') :
    Nat.card (T.comap φ) = Nat.card φ.ker * Nat.card ↥(T ⊓ φ.range) := by
  let ψ : ↥(T.comap φ) →* G' := φ.comp (T.comap φ).subtype
  have hr : ψ.range = T ⊓ φ.range := by
    ext y
    constructor
    · rintro ⟨⟨a, ha⟩, rfl⟩
      exact ⟨ha, a, rfl⟩
    · rintro ⟨hyT, a, rfl⟩
      exact ⟨⟨a, hyT⟩, rfl⟩
  have hk : Nat.card ψ.ker = Nat.card φ.ker := by
    have : ψ.ker = φ.ker.subgroupOf (T.comap φ) := by
      ext a
      simp [ψ, MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    rw [this]
    have hle : φ.ker ≤ T.comap φ := fun a ha => by
      simp [Subgroup.mem_comap, MonoidHom.mem_ker.mp ha, T.one_mem]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv
  have h1 := Subgroup.card_mul_index ψ.ker
  rw [Subgroup.index_ker ψ, hr, hk] at h1
  exact h1.symm


omit [Finite H] in
theorem w_comm_z (h : ProdSL2 H K₁ K₂ F₁ F₂) {z w : H} (hz : z ∈ K₁ ⊓ K₂) (hz1 : z ≠ 1)
    (hw₁ : ∀ x ∈ K₁, w * x * w⁻¹ ∈ K₁) (hw₂ : ∀ x ∈ K₂, w * x * w⁻¹ ∈ K₂) :
    w * z = z * w := by
  have hmem : w * z * w⁻¹ ∈ K₁ ⊓ K₂ := ⟨hw₁ z hz.1, hw₂ z hz.2⟩
  have hne : w * z * w⁻¹ ≠ 1 := by
    intro h1
    apply hz1
    have : z = w⁻¹ * (w * z * w⁻¹) * w := by group
    rw [this, h1]; group
  have h2 := (h.inter_cases hz hz1 _ hmem).resolve_left hne
  calc w * z = (w * z * w⁻¹) * w := by group
    _ = z * w := by rw [h2]

omit [Finite H] in
theorem odd_card_left (h : ProdSL2 H K₁ K₂ F₁ F₂) [Finite F₁] {z : H} (hz : z ∈ K₁ ⊓ K₂)
    (hz1 : z ≠ 1) : Odd (Nat.card F₁) := by
  have hF : ringChar F₁ ≠ 2 := by
    intro hc
    apply (h.z_data₁ hz hz1).1
    have := CharP.cast_eq_zero F₁ (ringChar F₁)
    rw [hc] at this
    exact_mod_cast this
  have : Fintype F₁ := Fintype.ofFinite F₁
  have h2 := FiniteField.odd_card_of_char_ne_two hF
  rw [Nat.card_eq_fintype_card]
  exact Nat.odd_iff.mpr h2

end Facts


section FactorMain

variable {A : Subgroup H} (Q : QuotData K₂ A F₁) (h : ProdSL2 H K₁ K₂ F₁ F₂) [Finite F₁]
include h

theorem QuotData.conj_lemma {z w : H} (hz : z ∈ K₁ ⊓ K₂) (hz1 : z ≠ 1) (hw2 : w * w = 1)
    (hw₁ : ∀ x ∈ K₁, w * x * w⁻¹ ∈ K₁) (hw₂ : ∀ x ∈ K₂, w * x * w⁻¹ ∈ K₂)
    (hK₁A : K₁ ≤ A) (hwA : w ∈ A) (hP : PGLInput F₁ (Q.imK hK₁A))
    (hwout : Q.f w ∉ Q.imK hK₁A)
    {a : H} (ha : a ∈ K₁) (hsq : (a * w) * (a * w) ∈ K₂) :
    ∃ k ∈ K₁, a * w = k * w * k⁻¹ ∨ a * w = z * (k * w * k⁻¹) := by
  have hwi : w⁻¹ = w := inv_eq_of_mul_eq_one_right hw2
  have hawA : a * w ∈ A := A.mul_mem (hK₁A ha) hwA
  set R := Q.imK hK₁A with hR
  have hRidx : R.index = 2 := Q.imK_index h hK₁A
  have hfa : Q.f a ∈ R := Q.f_mem_imK hK₁A ha
  set ξ := Q.f (a * w) with hξ
  have hξeq : ξ = Q.f a * Q.f w := Q.f_mul (hK₁A ha) hwA
  have hξ2 : ξ * ξ = 1 := by
    rw [hξ, ← Q.f_mul hawA hawA]
    exact (Q.f_eq_one_iff (A.mul_mem hawA hawA)).mpr hsq
  have hξout : ξ ∉ R := by
    intro hξR
    apply hwout
    have : Q.f w = (Q.f a)⁻¹ * ξ := by rw [hξeq]; group
    rw [this]
    exact R.mul_mem (R.inv_mem hfa) hξR
  have hfw2 : Q.f w * Q.f w = 1 := by
    rw [← Q.f_mul hwA hwA, hw2, Q.f_one]
  obtain ⟨g, hg⟩ := isConj_iff.mp (hP.outer_conj (Q.f w) ξ hfw2 hξ2 hwout hξout)
  have hgR : ∃ g' ∈ R, g' * Q.f w * g'⁻¹ = ξ := by
    by_cases hgR : g ∈ R
    · exact ⟨g, hgR, hg⟩
    · refine ⟨g * Q.f w, ?_, ?_⟩
      · rw [Subgroup.mul_mem_iff_of_index_two hRidx]
        simp [hgR, hwout]
      · rw [← hg]
        calc g * Q.f w * Q.f w * (g * Q.f w)⁻¹
            = g * (Q.f w * Q.f w) * (Q.f w)⁻¹ * g⁻¹ := by group
          _ = g * Q.f w * g⁻¹ := by group
  obtain ⟨g', hg'R, hg'⟩ := hgR
  obtain ⟨k, hk, hkg⟩ := Q.exists_f_K₁ hK₁A hg'R
  have hkA : k ∈ A := hK₁A hk
  have hkwA : k * w * k⁻¹ ∈ A := A.mul_mem (A.mul_mem hkA hwA) (A.inv_mem hkA)
  have hfk : Q.f (k * w * k⁻¹) = ξ := by
    rw [Q.f_mul (A.mul_mem hkA hwA) (A.inv_mem hkA), Q.f_mul hkA hwA,
      Q.f_inv hkA, hkg, hg']
  set c := (k * w * k⁻¹)⁻¹ * (a * w) with hc
  have hcA : c ∈ A := A.mul_mem (A.inv_mem hkwA) hawA
  have hcK₂ : c ∈ K₂ := by
    rw [← Q.f_eq_one_iff hcA, hc, Q.f_mul (A.inv_mem hkwA) hawA, Q.f_inv hkwA, hfk, ← hξ]
    group
  have hcK₁ : c ∈ K₁ := by
    have h1 : w * (k⁻¹ * a) * w ∈ K₁ := by
      have := hw₁ (k⁻¹ * a) (K₁.mul_mem (K₁.inv_mem hk) ha)
      rwa [hwi] at this
    have : c = k * (w * (k⁻¹ * a) * w) := by
      simp only [hc, mul_inv_rev, inv_inv, hwi]
      group
    rw [this]
    exact K₁.mul_mem hk h1
  have hacw : a * w = (k * w * k⁻¹) * c := by simp only [hc]; group
  rcases h.inter_cases hz hz1 c ⟨hcK₁, hcK₂⟩ with h1 | h1
  · refine ⟨k, hk, Or.inl ?_⟩
    rw [hacw, h1, mul_one]
  · refine ⟨k, hk, Or.inr ?_⟩
    have hzk : Commute z k := (h.comm k hk z hz.2).symm
    have hzw : Commute z w := (w_comm_z h hz hz1 hw₁ hw₂).symm
    have hcomm : Commute z (k * w * k⁻¹) := (hzk.mul_right hzw).mul_right hzk.inv_right
    rw [hacw, h1]
    exact hcomm.eq.symm


theorem QuotData.exists_twist (hF : IsOddPrimePower (Nat.card F₁)) (hq3 : 3 < Nat.card F₁)
    {z w : H} (hz : z ∈ K₁ ⊓ K₂) (hz1 : z ≠ 1) (hw2 : w * w = 1)
    (hw₁ : ∀ x ∈ K₁, w * x * w⁻¹ ∈ K₁) (hK₁A : K₁ ≤ A) (hwA : w ∈ A)
    (hwout : Q.f w ∉ Q.imK hK₁A) :
    ∃ x ∈ K₁, x * x = z ∧ w * x * w⁻¹ = x⁻¹ := by
  have hwi : w⁻¹ = w := inv_eq_of_mul_eq_one_right hw2
  let α : MulAut ↥K₁ :=
    { toFun := fun x => ⟨w * x * w⁻¹, hw₁ x x.2⟩
      invFun := fun x => ⟨w * x * w⁻¹, hw₁ x x.2⟩
      left_inv := fun x => Subtype.ext (by
        show w * (w * (x : H) * w⁻¹) * w⁻¹ = x
        rw [hwi]
        calc w * (w * (x : H) * w) * w = (w * w) * x * (w * w) := by group
          _ = x := by rw [hw2]; group)
      right_inv := fun x => Subtype.ext (by
        show w * (w * (x : H) * w⁻¹) * w⁻¹ = x
        rw [hwi]
        calc w * (w * (x : H) * w) * w = (w * w) * x * (w * w) := by group
          _ = x := by rw [hw2]; group)
      map_mul' := fun x y => Subtype.ext (by
        show w * ((x : H) * y) * w⁻¹ = (w * x * w⁻¹) * (w * y * w⁻¹)
        group) }
  have hαapp : ∀ x : ↥K₁, ((α x : ↥K₁) : H) = w * x * w⁻¹ := fun x => rfl
  have hα2 : α * α = 1 := by
    ext x
    show ((α (α x) : ↥K₁) : H) = x
    rw [hαapp, hαapp, hwi]
    calc w * (w * (x : H) * w) * w = (w * w) * x * (w * w) := by group
      _ = x := by rw [hw2]; group
  have hα1 : α ≠ 1 := by
    intro hα
    apply hwout
    have hcomm : ∀ x ∈ (Matrix.ProjectiveSpecialLinearGroup.toPGL (n := Fin 2) (R := F₁)).range,
        Q.f w * x = x * Q.f w := by
      intro x hx
      rw [← pgl2_commutator_eq_psl2_range_of_card_gt_three F₁ hF hq3,
        ← Q.imK_eq_commutator h hF hq3 hK₁A] at hx
      obtain ⟨a, ha, rfl⟩ := Q.exists_f_K₁ hK₁A hx
      have hwa : w * a * w⁻¹ = a := by
        have := congrArg (fun β : MulAut ↥K₁ => ((β ⟨a, ha⟩ : ↥K₁) : H)) hα
        simpa [hαapp] using this
      have hwa' : w * a = a * w := by
        calc w * a = (w * a * w⁻¹) * w := by group
          _ = a * w := by rw [hwa]
      rw [← Q.f_mul hwA (hK₁A ha), ← Q.f_mul (hK₁A ha) hwA, hwa']
    have h1 := pgl2_eq_one_of_commutes_range (Q.f w) hcomm
    rw [h1]
    exact (Q.imK hK₁A).one_mem
  have hαo : orderOf α = 2 := orderOf_eq_prime (by rw [pow_two]; exact hα2) hα1
  have hodd : Odd (Nat.card F₁) := odd_card_left h hz hz1
  obtain ⟨x, hx4, hαx⟩ := ivk_1_13 F₁ hodd hq3 ↥K₁ h.iso₁.some α hαo
  refine ⟨x, x.2, ?_, ?_⟩
  · have hx4' : (x : H) * x * ((x : H) * x) = 1 := by
      have : x ^ 4 = 1 := by rw [← hx4]; exact pow_orderOf_eq_one x
      have h2 := congrArg (fun y : ↥K₁ => (y : H)) this
      simpa [pow_succ, mul_assoc] using h2
    have hu : (x : H) * x ∈ K₁ := K₁.mul_mem x.2 x.2
    rcases h.eq_one_or_eq_z₁ hz hz1 hu hx4' with h1 | h1
    · exfalso
      have : x * x = 1 := Subtype.ext h1
      have h3 : orderOf x ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact this)
      rw [hx4] at h3
      omega
    · exact h1
  · have := congrArg (fun y : ↥K₁ => (y : H)) hαx
    simpa [hαapp] using this



omit [Finite H] [Finite F₁] in
theorem QuotData.exists_twist_three {z w : H} (hz : z ∈ K₁ ⊓ K₂) (hz1 : z ≠ 1) (hw2 : w * w = 1)
    (hw₁ : ∀ x ∈ K₁, w * x * w⁻¹ ∈ K₁) (hw₂ : ∀ x ∈ K₂, w * x * w⁻¹ ∈ K₂)
    (hK₁A : K₁ ≤ A) (hwA : w ∈ A) (hwout : Q.f w ∉ Q.imK hK₁A)
    (hT : ∀ τ : PGL2 F₁, τ * τ = 1 → τ ∉ Q.imK hK₁A → ∃ d₀ ∈ Q.imK hK₁A, ∃ d₁ ∈ Q.imK hK₁A,
      d₀ ≠ 1 ∧ d₀ * d₀ = 1 ∧ τ * d₀ * τ⁻¹ = d₀ ∧ τ * d₁ * τ⁻¹ = d₀ * d₁) :
    ∃ x ∈ K₁, x * x = z ∧ w * x * w⁻¹ = x⁻¹ := by
  have hwi : w⁻¹ = w := inv_eq_of_mul_eq_one_right hw2
  have hfw2 : Q.f w * Q.f w = 1 := by
    rw [← Q.f_mul hwA hwA, hw2, Q.f_one]
  have hzz : z * z = 1 :=
    CFSG.GH74.GLS.IVK.Proofs2.mul_self_eq_one_of_orderOf_eq_two (h.inter_eq hz hz1).2
  have hker : ∀ a ∈ K₁, Q.f a = 1 → a = 1 ∨ a = z := by
    intro a ha hfa
    exact h.inter_cases hz hz1 a ⟨ha, (Q.f_eq_one_iff (hK₁A ha)).mp hfa⟩
  have hfz : Q.f z = 1 := (Q.f_eq_one_iff (hK₁A hz.1)).mpr hz.2
  obtain ⟨d₀, hd₀, d₁, hd₁, hd₀1, hd₀2, hτd₀, hτd₁⟩ := hT (Q.f w) hfw2 hwout
  obtain ⟨x, hx, hxd⟩ := Q.exists_f_K₁ hK₁A hd₀
  obtain ⟨y, hy, hyd⟩ := Q.exists_f_K₁ hK₁A hd₁
  have hxA : x ∈ A := hK₁A hx
  have hyA : y ∈ A := hK₁A hy
  have hxx : x * x = z := by
    have hfxx : Q.f (x * x) = 1 := by
      rw [Q.f_mul hxA hxA, hxd, hd₀2]
    rcases hker (x * x) (K₁.mul_mem hx hx) hfxx with h1 | h1
    · exfalso
      rcases h.eq_one_or_eq_z₁ hz hz1 hx h1 with h2 | h2
      · apply hd₀1; rw [← hxd, h2, Q.f_one]
      · apply hd₀1; rw [← hxd, h2, hfz]
    · exact h1
  have hwxA : w * x * w⁻¹ ∈ A := A.mul_mem (A.mul_mem hwA hxA) (A.inv_mem hwA)
  have hu : w * x * w⁻¹ * x⁻¹ ∈ K₁ := K₁.mul_mem (hw₁ x hx) (K₁.inv_mem hx)
  have hfu : Q.f (w * x * w⁻¹ * x⁻¹) = 1 := by
    rw [Q.f_mul hwxA (A.inv_mem hxA), Q.f_mul (A.mul_mem hwA hxA) (A.inv_mem hwA),
      Q.f_mul hwA hxA, Q.f_inv hwA, Q.f_inv hxA, hxd, hτd₀]
    group
  have hwz : w * z = z * w := w_comm_z h hz hz1 hw₁ hw₂
  refine ⟨x, hx, hxx, ?_⟩
  rcases hker _ hu hfu with h1 | h1
  ·
    exfalso
    have hwx : w * x * w⁻¹ = x := by
      calc w * x * w⁻¹ = (w * x * w⁻¹ * x⁻¹) * x := by group
        _ = x := by rw [h1]; group
    set v := w * y * w⁻¹ with hv
    have hvK : v ∈ K₁ := hw₁ y hy
    have hvA : v ∈ A := hK₁A hvK
    have hfv : Q.f v = Q.f (x * y) := by
      rw [hv, Q.f_mul (A.mul_mem hwA hyA) (A.inv_mem hwA), Q.f_mul hwA hyA, Q.f_inv hwA,
        Q.f_mul hxA hyA, hxd, hyd, hτd₁]
    set c := (x * y)⁻¹ * v with hc
    have hcK : c ∈ K₁ := K₁.mul_mem (K₁.inv_mem (K₁.mul_mem hx hy)) hvK
    have hfc : Q.f c = 1 := by
      rw [hc, Q.f_mul (A.inv_mem (A.mul_mem hxA hyA)) hvA, Q.f_inv (A.mul_mem hxA hyA), hfv]
      group
    have hcv : v = x * y * c := by rw [hc]; group
    have hwc : w * c * w⁻¹ = c := by
      rcases hker c hcK hfc with h2 | h2
      · rw [h2]; group
      · rw [h2]
        calc w * z * w⁻¹ = z * w * w⁻¹ := by rw [hwz]
          _ = z := by group
    have hcc : c * c = 1 := by
      rcases hker c hcK hfc with h2 | h2
      · rw [h2]; group
      · rw [h2]; exact hzz
    have hwv : w * v * w⁻¹ = y := by
      rw [hv]
      calc w * (w * y * w⁻¹) * w⁻¹ = (w * w) * y * (w * w)⁻¹ := by group
        _ = y := by rw [hw2]; group
    have hwv' : w * v * w⁻¹ = z * y := by
      calc w * v * w⁻¹ = w * (x * y * c) * w⁻¹ := by rw [hcv]
        _ = (w * x * w⁻¹) * (w * y * w⁻¹) * (w * c * w⁻¹) := by group
        _ = x * v * c := by rw [hwx, ← hv, hwc]
        _ = x * (x * y * c) * c := by rw [hcv]
        _ = (x * x) * y * (c * c) := by group
        _ = z * y := by rw [hxx, hcc]; group
    have hzy : z * y = y := by rw [← hwv', hwv]
    apply hz1
    calc z = z * y * y⁻¹ := by group
      _ = y * y⁻¹ := by rw [hzy]
      _ = 1 := by group
  ·
    have hx4 : x * x * (x * x) = 1 := by rw [hxx]; exact hzz
    calc w * x * w⁻¹ = (w * x * w⁻¹ * x⁻¹) * x := by group
      _ = z * x := by rw [h1]
      _ = x⁻¹ := by
        rw [← hxx]
        have : x * x * x * x = 1 := by
          calc x * x * x * x = x * x * (x * x) := by group
            _ = 1 := hx4
        calc x * x * x = x * x * x * x * x⁻¹ := by group
          _ = x⁻¹ := by rw [this]; group

end FactorMain


theorem commute_of_forall_sq' {G : Type*} [Group G] (H : Subgroup G) (hH : ∀ h ∈ H, h * h = 1)
    {a b : G} (ha : a ∈ H) (hb : b ∈ H) : a * b = b * a := by
  have hinv : ∀ h ∈ H, h⁻¹ = h := fun h hh => inv_eq_of_mul_eq_one_right (hH h hh)
  calc a * b = (a * b)⁻¹ := (hinv _ (H.mul_mem ha hb)).symm
    _ = b⁻¹ * a⁻¹ := mul_inv_rev a b
    _ = b * a := by rw [hinv b hb, hinv a ha]

theorem pgl2_card_le_four_of_sq'
    {F : Type} [Field F] [Finite F] (hK : IsOddPrimePower (Nat.card F))
    (E : Subgroup (PGL2 F)) (hE : ∀ e ∈ E, e * e = 1) : Nat.card E ≤ 4 := by
  by_contra hlt
  push Not at hlt
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hP : IsPGroup 2 E := fun x => ⟨1, by rw [pow_one, pow_two]; exact Subtype.ext (hE x x.2)⟩
  obtain ⟨k, hk⟩ := (IsPGroup.iff_card).mp hP
  have h4 : 2 ^ 2 ∣ Nat.card E := by
    rw [hk]
    apply Nat.pow_dvd_pow
    by_contra hk2
    push Not at hk2
    interval_cases k <;> simp_all
  obtain ⟨V, hV⟩ := Sylow.exists_subgroup_card_pow_prime 2 h4
  set V' : Subgroup (PGL2 F) := V.map E.subtype with hV'
  have hV'card : Nat.card V' = 4 := by
    rw [hV', Subgroup.card_map_of_injective E.subtype_injective, hV]
    norm_num
  have hV'E : V' ≤ E := by
    rintro _ ⟨x, -, rfl⟩
    exact x.2
  have hV'K : IsKleinFour V' := by
    have : Nontrivial V' := by
      rw [← Finite.one_lt_card_iff_nontrivial, hV'card]
      norm_num
    refine ⟨hV'card, (Monoid.exponent_eq_prime_iff Nat.prime_two).mpr fun g hg => ?_⟩
    apply orderOf_eq_prime
    · rw [pow_two]
      exact Subtype.ext (hE g (hV'E g.2))
    · exact hg
  have hEC : E ≤ centralizer (V' : Set (PGL2 F)) := by
    intro x hx
    rw [mem_centralizer_iff]
    intro v hv
    exact commute_of_forall_sq' E hE (hV'E hv) hx
  rw [pgl2_kleinFour_centralizer_eq_self F hK V' hV'K] at hEC
  have := Subgroup.card_le_of_le hEC
  omega

section Rank

variable {A : Subgroup H} (Q : QuotData K₂ A F₁) (h : ProdSL2 H K₁ K₂ F₁ F₂) [Finite F₁]
include Q h

theorem QuotData.card_le_eight
    (hF : IsOddPrimePower (Nat.card F₁)) (hK₁A : K₁ ≤ A) (hK₂A : K₂ ≤ A) {z : H}
    (hz : z ∈ K₁ ⊓ K₂) (hz1 : z ≠ 1) {E : Subgroup H} (hE : E ≤ K₁ ⊔ K₂)
    (hsq : ∀ x ∈ E, x * x = 1) :
    Nat.card E ≤ 8 := by
  have hEA : E ≤ A := hE.trans (sup_le hK₁A hK₂A)
  set ψ : ↥E →* PGL2 F₁ := Q.ρ.comp (Subgroup.inclusion hEA) with hψ
  have hrange : Nat.card ψ.range ≤ 4 := by
    apply pgl2_card_le_four_of_sq' hF ψ.range
    rintro _ ⟨a, rfl⟩
    rw [← map_mul]
    have : a * a = 1 := Subtype.ext (hsq a a.2)
    rw [this, map_one]
  have hker : Nat.card ψ.ker ≤ 2 := by
    have hk : ψ.ker = K₂.subgroupOf E := by
      ext a
      simp only [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, hψ, MonoidHom.comp_apply]
      exact Q.ker_iff ⟨a, hEA a.2⟩
    rw [hk]
    have hle : (K₂.subgroupOf E).map E.subtype ≤ K₁ ⊓ K₂ := by
      rintro _ ⟨a, ha, rfl⟩
      have haK₂ : (a : H) ∈ K₂ := ha
      have hz' : z ∈ K₂ ⊓ K₁ := by rwa [inf_comm] at hz
      rcases h.symm.eq_one_or_eq_z₁ hz' hz1 haK₂ (hsq a a.2) with h1 | h1
      · show (a : H) ∈ K₁ ⊓ K₂
        rw [h1]; exact (K₁ ⊓ K₂).one_mem
      · show (a : H) ∈ K₁ ⊓ K₂
        rw [h1]; exact hz
    calc Nat.card (K₂.subgroupOf E)
        = Nat.card ((K₂.subgroupOf E).map E.subtype) :=
          (Subgroup.card_map_of_injective E.subtype_injective).symm
      _ ≤ Nat.card ↥(K₁ ⊓ K₂) := Subgroup.card_le_of_le hle
      _ = 2 := h.card_inter
  have h1 := Subgroup.card_mul_index ψ.ker
  rw [Subgroup.index_ker ψ] at h1
  have h2 : Nat.card ↥E = Nat.card ψ.ker * Nat.card ψ.range := h1.symm
  rw [h2]
  calc Nat.card ψ.ker * Nat.card ψ.range ≤ 2 * 4 := Nat.mul_le_mul hker hrange
    _ = 8 := by norm_num


end Rank


section Card

variable {A : Subgroup H} (Q : QuotData K₂ A F₁) (h : ProdSL2 H K₁ K₂ F₁ F₂) [Finite F₁]
include h

omit [Finite F₁] in
theorem QuotData.exists_S {w : H} (hK₁A : K₁ ≤ A) (hwA : w ∈ A) (hw2 : w * w = 1)
    (hP : PGLInput F₁ (Q.imK hK₁A)) (hwout : Q.f w ∉ Q.imK hK₁A) :
    ∃ S : Subgroup H, (∀ a, a ∈ S ↔ a ∈ K₁ ∧ w * a * w⁻¹ * a⁻¹ ∈ K₂) ∧
      ∃ m : ℕ, Odd m ∧ Nat.card S = 4 * m := by
  set φ : ↥K₁ →* PGL2 F₁ := Q.ρ.comp (Subgroup.inclusion hK₁A) with hφ
  set T : Subgroup (PGL2 F₁) := Subgroup.centralizer ({Q.f w} : Set (PGL2 F₁)) with hT
  have hφa : ∀ a : ↥K₁, φ a = Q.f a := fun a => (Q.f_of_mem (hK₁A a.2)).symm
  have hrange : φ.range = Q.imK hK₁A := rfl
  have key : ∀ a : H, a ∈ K₁ → (w * a * w⁻¹ * a⁻¹ ∈ K₂ ↔ Q.f a ∈ T) := by
    intro a ha
    have haA : a ∈ A := hK₁A ha
    have hmemA : w * a * w⁻¹ * a⁻¹ ∈ A :=
      A.mul_mem (A.mul_mem (A.mul_mem hwA haA) (A.inv_mem hwA)) (A.inv_mem haA)
    rw [← Q.f_eq_one_iff hmemA,
      Q.f_mul (A.mul_mem (A.mul_mem hwA haA) (A.inv_mem hwA)) (A.inv_mem haA),
      Q.f_mul (A.mul_mem hwA haA) (A.inv_mem hwA), Q.f_mul hwA haA, Q.f_inv hwA, Q.f_inv haA,
      hT, Subgroup.mem_centralizer_singleton_iff]
    have h1 : Q.f w * Q.f a * (Q.f w)⁻¹ * (Q.f a)⁻¹ = ⁅Q.f w, Q.f a⁆ := rfl
    rw [h1, commutatorElement_eq_one_iff_mul_comm]
    exact ⟨fun h => h.symm, fun h => h.symm⟩
  refine ⟨(T.comap φ).map K₁.subtype, ?_, ?_⟩
  · intro a
    constructor
    · rintro ⟨a', ha', rfl⟩
      refine ⟨a'.2, (key a' a'.2).mpr ?_⟩
      have : φ a' ∈ T := ha'
      rwa [hφa] at this
    · rintro ⟨haK, hsq⟩
      refine ⟨⟨a, haK⟩, ?_, rfl⟩
      show φ ⟨a, haK⟩ ∈ T
      rw [hφa]
      exact (key a haK).mp hsq
  · have hcard : Nat.card ((T.comap φ).map K₁.subtype) = Nat.card (T.comap φ) :=
      Subgroup.card_map_of_injective K₁.subtype_injective
    rw [hcard, card_comap_eq φ T, hrange]
    have hker : Nat.card φ.ker = 2 := Q.card_ker h hK₁A
    have hfw2 : Q.f w * Q.f w = 1 := by
      rw [← Q.f_mul hwA hwA, hw2, Q.f_one]
    obtain ⟨m, hm, hmc⟩ := hP.cent (Q.f w) hfw2 hwout
    refine ⟨m, hm, ?_⟩
    rw [hker, inf_comm, hT, hmc]
    ring

end Card


structure FactorFacts {H : Type} [Group H] (K₁ K₂ : Subgroup H) (z w : H) : Prop where
  w_not_mem : w ∉ K₁ ⊔ K₂
  conj : ∀ a ∈ K₁, (a * w) * (a * w) ∈ K₂ →
    ∃ k ∈ K₁, a * w = k * w * k⁻¹ ∨ a * w = z * (k * w * k⁻¹)
  twist : ∃ x ∈ K₁, x * x = z ∧ w * x * w⁻¹ = x⁻¹
  card : ∃ S : Subgroup H, (∀ a, a ∈ S ↔ a ∈ K₁ ∧ w * a * w⁻¹ * a⁻¹ ∈ K₂) ∧
    ∃ m : ℕ, Odd m ∧ Nat.card S = 4 * m
  rank : ∀ E : Subgroup H, E ≤ K₁ ⊔ K₂ → (∀ x ∈ E, ∀ y ∈ E, x * y = y * x) →
    (∀ x ∈ E, x * x = 1) → Nat.card E ≤ 8

section FactorFactsThm

theorem factorFacts_of_input
    (h : ProdSL2 H K₁ K₂ F₁ F₂) [Finite F₁] {z w : H}
    (hz : z ∈ K₁ ⊓ K₂) (hz1 : z ≠ 1) (hw2 : w * w = 1)
    (hw₁ : ∀ x ∈ K₁, w * x * w⁻¹ ∈ K₁) (hw₂ : ∀ x ∈ K₂, w * x * w⁻¹ ∈ K₂)
    {A : Subgroup H} (hA : A = K₁ ⊔ K₂ ⊔ zpowers w) (Q : QuotData K₂ A F₁)
    (hF : IsOddPrimePower (Nat.card F₁)) (hK₁A : K₁ ≤ A) (hP : PGLInput F₁ (Q.imK hK₁A))
    (htw : Q.f w ∉ Q.imK hK₁A → ∃ x ∈ K₁, x * x = z ∧ w * x * w⁻¹ = x⁻¹) :
    FactorFacts K₁ K₂ z w := by
  have hK₂A : K₂ ≤ A := hA ▸ le_sup_right.trans le_sup_left
  have hwA : w ∈ A := hA ▸ Subgroup.mem_sup_right (Subgroup.mem_zpowers w)
  have hwout := Q.f_w_not_mem h hK₁A hK₂A hwA hA
  refine ⟨?_, fun a ha hsq => Q.conj_lemma h hz hz1 hw2 hw₁ hw₂ hK₁A hwA hP hwout ha hsq,
    htw hwout, Q.exists_S h hK₁A hwA hw2 hP hwout,
    fun E hE _ hs => Q.card_le_eight h hF hK₁A hK₂A hz hz1 hE hs⟩
  intro hw
  obtain ⟨a, ha, b, hb, rfl⟩ := (h.mem_sup_iff w).1 hw
  apply hwout
  rw [Q.f_mul (hK₁A ha) (hK₂A hb), (Q.f_eq_one_iff (hK₂A hb)).mpr hb, mul_one]
  exact Q.f_mem_imK hK₁A ha

theorem factorFacts
    (h : ProdSL2 H K₁ K₂ F₁ F₂) [Finite F₁] (hodd : Odd (Nat.card F₁)) {z w : H}
    (hz : z ∈ K₁ ⊓ K₂) (hz1 : z ≠ 1) (hw2 : w * w = 1)
    (hw₁ : ∀ x ∈ K₁, w * x * w⁻¹ ∈ K₁) (hw₂ : ∀ x ∈ K₂, w * x * w⁻¹ ∈ K₂)
    {A : Subgroup H} (hA : A = K₁ ⊔ K₂ ⊔ zpowers w) (Q : QuotData K₂ A F₁) :
    FactorFacts K₁ K₂ z w := by
  have hK₁A : K₁ ≤ A := hA ▸ le_sup_left.trans le_sup_left
  have hwA : w ∈ A := hA ▸ Subgroup.mem_sup_right (Subgroup.mem_zpowers w)
  have hge : 2 ≤ Nat.card F₁ := by
    have := Finite.one_lt_card (α := F₁)
    omega
  have hne2 : Nat.card F₁ ≠ 2 := by
    intro h2
    rw [h2] at hodd
    exact absurd hodd (by decide)
  rcases (show 3 ≤ Nat.card F₁ by omega).lt_or_eq with hlt | heq
  · have hF : IsOddPrimePower (Nat.card F₁) := isOddPrimePower_of_L2Field ⟨hodd, hlt⟩
    exact factorFacts_of_input h hz hz1 hw2 hw₁ hw₂ hA Q hF hK₁A
      (PGLInput.of_gt_three hF hlt (Q.imK_eq_commutator h hF hlt hK₁A))
      (fun hwout => Q.exists_twist h hF hlt hz hz1 hw2 hw₁ hK₁A hwA hwout)
  · have h3 : Nat.card F₁ = 3 := heq.symm
    have hF : IsOddPrimePower (Nat.card F₁) := ⟨3, 1, Nat.prime_three, ⟨1, rfl⟩, le_rfl, by rw [h3]; rfl⟩
    obtain ⟨e⟩ := exists_pgl2_equiv_perm (F := F₁) h3
    have hidx := Q.imK_index h hK₁A
    exact factorFacts_of_input h hz hz1 hw2 hw₁ hw₂ hA Q hF hK₁A (PGLInput.of_three e hidx)
      (fun hwout => Q.exists_twist_three h hz hz1 hw2 hw₁ hw₂ hK₁A hwA hwout
        (fun τ hτ hτR => Sec3S4.s4_twist e _ hidx hτ hτR))

end FactorFactsThm

end Sec3Fac

end CFSG.GH74.GLS.IVK.Proofs2
