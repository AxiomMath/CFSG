module

public import CFSG.LinearAlgebra.SL2MinimalFaithfulSection

public section

namespace CFSG.LocalAnalysis.EvenBN.Sp4.BothTrivialTwist

open Subgroup

variable {G : Type*} [Group G]

section SecAut

variable {Y Z : Subgroup G} [(Z.subgroupOf Y).Normal]

theorem map_conjAut_subgroupOf {g : G} (hY : g ∈ normalizer (Y : Set G))
    (hZ : g ∈ normalizer (Z : Set G)) :
    (Z.subgroupOf Y).map ((CFSG.SL2MinimalFaithful.conjAut hY : MulAut ↥Y) : ↥Y →* ↥Y) =
      Z.subgroupOf Y := by
  apply le_antisymm
  · rintro _ ⟨z, hz, rfl⟩
    change g * (z : G) * g⁻¹ ∈ Z
    exact (mem_normalizer_iff.mp hZ z).mp hz
  · intro z hz
    have hg : g⁻¹ ∈ normalizer (Y : Set G) := inv_mem hY
    refine ⟨⟨g⁻¹ * z * g, ?_⟩, ?_, ?_⟩
    · have := (mem_normalizer_iff.mp hg z).mp z.2
      simpa using this
    · change g⁻¹ * (z : G) * g ∈ Z
      have := (mem_normalizer_iff.mp (inv_mem hZ) z).mp hz
      simpa using this
    · apply Subtype.ext
      change g * (g⁻¹ * z * g) * g⁻¹ = z
      group

@[expose] noncomputable def secAut (g : G) (hY : g ∈ normalizer (Y : Set G))
    (hZ : g ∈ normalizer (Z : Set G)) : ↥Y ⧸ Z.subgroupOf Y ≃* ↥Y ⧸ Z.subgroupOf Y :=
  QuotientGroup.congr (Z.subgroupOf Y) (Z.subgroupOf Y) (CFSG.SL2MinimalFaithful.conjAut hY)
    (map_conjAut_subgroupOf hY hZ)

theorem secAut_mk (g : G) (hY : g ∈ normalizer (Y : Set G)) (hZ : g ∈ normalizer (Z : Set G))
    (y : Y) :
    secAut g hY hZ (y : ↥Y ⧸ Z.subgroupOf Y) =
      ((⟨g * y * g⁻¹, (mem_normalizer_iff.mp hY y).mp y.2⟩ : Y) : ↥Y ⧸ Z.subgroupOf Y) := by
  unfold secAut
  rw [QuotientGroup.congr_mk]
  rfl

theorem secAut_apply_eq_iff (hYZ : Y ≤ normalizer (Z : Set G)) {g : G}
    (hY : g ∈ normalizer (Y : Set G)) (hZ : g ∈ normalizer (Z : Set G)) (y : Y) :
    secAut g hY hZ (y : ↥Y ⧸ Z.subgroupOf Y) = y ↔ g * y * g⁻¹ * (y : G)⁻¹ ∈ Z := by
  rw [secAut_mk, QuotientGroup.eq, mem_subgroupOf]
  exact CFSG.SL2MinimalFaithful.inv_mul_mem_iff hYZ y.2

theorem secAut_mul {g h : G} (hgY : g ∈ normalizer (Y : Set G)) (hgZ : g ∈ normalizer (Z : Set G))
    (hhY : h ∈ normalizer (Y : Set G)) (hhZ : h ∈ normalizer (Z : Set G))
    (v : ↥Y ⧸ Z.subgroupOf Y) :
    secAut (g * h) (mul_mem hgY hhY) (mul_mem hgZ hhZ) v =
      secAut g hgY hgZ (secAut h hhY hhZ v) := by
  induction v using QuotientGroup.induction_on with
  | H y =>
    rw [secAut_mk, secAut_mk, secAut_mk]
    congr 1
    apply Subtype.ext
    change g * h * (y : G) * (g * h)⁻¹ = g * (h * (y : G) * h⁻¹) * g⁻¹
    group

theorem secAut_of_eq {g g' : G} (hg : g = g') (hY : g ∈ normalizer (Y : Set G))
    (hZ : g ∈ normalizer (Z : Set G)) (hY' : g' ∈ normalizer (Y : Set G))
    (hZ' : g' ∈ normalizer (Z : Set G)) (v : ↥Y ⧸ Z.subgroupOf Y) :
    secAut g hY hZ v = secAut g' hY' hZ' v := by
  subst hg
  rfl

theorem secAut_triv (hYZ : Y ≤ normalizer (Z : Set G)) {g : G} (hY : g ∈ normalizer (Y : Set G))
    (hZ : g ∈ normalizer (Z : Set G)) (h : ∀ y ∈ Y, g * y * g⁻¹ * y⁻¹ ∈ Z)
    (v : ↥Y ⧸ Z.subgroupOf Y) : secAut g hY hZ v = v := by
  induction v using QuotientGroup.induction_on with
  | H y => exact (secAut_apply_eq_iff hYZ hY hZ y).mpr (h y y.2)

theorem secAut_cube {g : G} (hY : g ∈ normalizer (Y : Set G)) (hZ : g ∈ normalizer (Z : Set G))
    (hg : g * g * g = 1) (v : ↥Y ⧸ Z.subgroupOf Y) :
    secAut g hY hZ (secAut g hY hZ (secAut g hY hZ v)) = v := by
  induction v using QuotientGroup.induction_on with
  | H y =>
    rw [secAut_mk, secAut_mk, secAut_mk]
    congr 1
    apply Subtype.ext
    change g * (g * (g * (y : G) * g⁻¹) * g⁻¹) * g⁻¹ = y
    rw [show g * (g * (g * (y : G) * g⁻¹) * g⁻¹) * g⁻¹ = (g * g * g) * y * (g * g * g)⁻¹ by group,
      hg]
    group

theorem quot_mul_comm (hab : ∀ a ∈ Y, ∀ b ∈ Y, a * b = b * a) (v w : ↥Y ⧸ Z.subgroupOf Y) :
    v * w = w * v := by
  induction v using QuotientGroup.induction_on with
  | H a =>
    induction w using QuotientGroup.induction_on with
    | H b =>
      rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
      congr 1
      exact Subtype.ext (hab a a.2 b b.2)

theorem quot_mul_self (hsq : ∀ a ∈ Y, a * a = 1) (v : ↥Y ⧸ Z.subgroupOf Y) : v * v = 1 := by
  induction v using QuotientGroup.induction_on with
  | H a =>
    rw [← QuotientGroup.mk_mul]
    have : a * a = 1 := Subtype.ext (hsq a a.2)
    rw [this]
    exact QuotientGroup.mk_one _

theorem secAut_conj_triv (hYZ : Y ≤ normalizer (Z : Set G)) {g s : G}
    (hgY : g ∈ normalizer (Y : Set G)) (hgZ : g ∈ normalizer (Z : Set G))
    (hsY : s ∈ normalizer (Y : Set G)) (hsZ : s ∈ normalizer (Z : Set G))
    (hsY' : s⁻¹ ∈ normalizer (Y : Set G)) (hsZ' : s⁻¹ ∈ normalizer (Z : Set G))
    (hY' : s * g * s⁻¹ ∈ normalizer (Y : Set G)) (hZ' : s * g * s⁻¹ ∈ normalizer (Z : Set G))
    (hs : ∀ y ∈ Y, s * y * s⁻¹ * y⁻¹ ∈ Z) (hs' : ∀ y ∈ Y, s⁻¹ * y * s⁻¹⁻¹ * y⁻¹ ∈ Z)
    (v : ↥Y ⧸ Z.subgroupOf Y) :
    secAut (s * g * s⁻¹) hY' hZ' v = secAut g hgY hgZ v := by
  calc secAut (s * g * s⁻¹) hY' hZ' v
      = secAut (s * g) (mul_mem hsY hgY) (mul_mem hsZ hgZ) (secAut s⁻¹ hsY' hsZ' v) :=
        secAut_mul (mul_mem hsY hgY) (mul_mem hsZ hgZ) hsY' hsZ' v
    _ = secAut s hsY hsZ (secAut g hgY hgZ (secAut s⁻¹ hsY' hsZ' v)) :=
        secAut_mul hsY hsZ hgY hgZ _
    _ = secAut g hgY hgZ v := by
        rw [secAut_triv hYZ hsY hsZ hs, secAut_triv hYZ hsY' hsZ' hs' v]

theorem secAut_mul_comm_of_triv (hYZ : Y ≤ normalizer (Z : Set G)) {g h c : G}
    (hgY : g ∈ normalizer (Y : Set G)) (hgZ : g ∈ normalizer (Z : Set G))
    (hhY : h ∈ normalizer (Y : Set G)) (hhZ : h ∈ normalizer (Z : Set G))
    (hcY : c ∈ normalizer (Y : Set G)) (hcZ : c ∈ normalizer (Z : Set G))
    (hc : ∀ y ∈ Y, c * y * c⁻¹ * y⁻¹ ∈ Z) (hgh : g * h = c * (h * g))
    (v : ↥Y ⧸ Z.subgroupOf Y) :
    secAut g hgY hgZ (secAut h hhY hhZ v) = secAut h hhY hhZ (secAut g hgY hgZ v) := by
  rw [← secAut_mul hgY hgZ hhY hhZ, ← secAut_mul hhY hhZ hgY hgZ,
    secAut_of_eq hgh (mul_mem hgY hhY) (mul_mem hgZ hhZ) (mul_mem hcY (mul_mem hhY hgY))
      (mul_mem hcZ (mul_mem hhZ hgZ)),
    secAut_mul hcY hcZ (mul_mem hhY hgY) (mul_mem hhZ hgZ), secAut_triv hYZ hcY hcZ hc]

end SecAut

section Transport

variable {Y Y' Z Z' : Subgroup G}

@[expose] def conjEquiv (u : G) (h : ∀ y ∈ Y, u * y * u⁻¹ ∈ Y')
    (h' : ∀ y ∈ Y', u⁻¹ * y * u ∈ Y) : ↥Y ≃* ↥Y' where
  toFun y := ⟨u * y * u⁻¹, h y y.2⟩
  invFun y := ⟨u⁻¹ * y * u, h' y y.2⟩
  left_inv y := Subtype.ext (by change u⁻¹ * (u * (y : G) * u⁻¹) * u = y; group)
  right_inv y := Subtype.ext (by change u * (u⁻¹ * (y : G) * u) * u⁻¹ = y; group)
  map_mul' a b := Subtype.ext (by
    change u * ((a : G) * (b : G)) * u⁻¹ = u * (a : G) * u⁻¹ * (u * (b : G) * u⁻¹)
    group)

theorem map_conjEquiv_subgroupOf {u : G} (h : ∀ y ∈ Y, u * y * u⁻¹ ∈ Y')
    (h' : ∀ y ∈ Y', u⁻¹ * y * u ∈ Y) (hZZ' : ∀ z ∈ Z, u * z * u⁻¹ ∈ Z')
    (hZ'Z : ∀ z ∈ Z', u⁻¹ * z * u ∈ Z) :
    (Z.subgroupOf Y).map ((conjEquiv u h h' : ↥Y ≃* ↥Y') : ↥Y →* ↥Y') = Z'.subgroupOf Y' := by
  apply le_antisymm
  · rintro _ ⟨z, hz, rfl⟩
    exact hZZ' z hz
  · intro z hz
    refine ⟨⟨u⁻¹ * z * u, h' z z.2⟩, hZ'Z z hz, ?_⟩
    apply Subtype.ext
    change u * (u⁻¹ * (z : G) * u) * u⁻¹ = z
    group

@[expose] noncomputable def secMap [(Z.subgroupOf Y).Normal] [(Z'.subgroupOf Y').Normal] (u : G)
    (h : ∀ y ∈ Y, u * y * u⁻¹ ∈ Y') (h' : ∀ y ∈ Y', u⁻¹ * y * u ∈ Y)
    (hZZ' : ∀ z ∈ Z, u * z * u⁻¹ ∈ Z') (hZ'Z : ∀ z ∈ Z', u⁻¹ * z * u ∈ Z) :
    ↥Y ⧸ Z.subgroupOf Y ≃* ↥Y' ⧸ Z'.subgroupOf Y' :=
  QuotientGroup.congr (Z.subgroupOf Y) (Z'.subgroupOf Y') (conjEquiv u h h')
    (map_conjEquiv_subgroupOf h h' hZZ' hZ'Z)

theorem secMap_mk [(Z.subgroupOf Y).Normal] [(Z'.subgroupOf Y').Normal] (u : G)
    (h : ∀ y ∈ Y, u * y * u⁻¹ ∈ Y') (h' : ∀ y ∈ Y', u⁻¹ * y * u ∈ Y)
    (hZZ' : ∀ z ∈ Z, u * z * u⁻¹ ∈ Z') (hZ'Z : ∀ z ∈ Z', u⁻¹ * z * u ∈ Z) (y : Y) :
    secMap u h h' hZZ' hZ'Z (y : ↥Y ⧸ Z.subgroupOf Y) =
      ((⟨u * y * u⁻¹, h y y.2⟩ : Y') : ↥Y' ⧸ Z'.subgroupOf Y') := by
  unfold secMap
  rw [QuotientGroup.congr_mk]
  rfl

theorem secMap_secAut [(Z.subgroupOf Y).Normal] [(Z'.subgroupOf Y').Normal] (u g : G)
    (h : ∀ y ∈ Y, u * y * u⁻¹ ∈ Y') (h' : ∀ y ∈ Y', u⁻¹ * y * u ∈ Y)
    (hZZ' : ∀ z ∈ Z, u * z * u⁻¹ ∈ Z') (hZ'Z : ∀ z ∈ Z', u⁻¹ * z * u ∈ Z)
    (hgY : g ∈ normalizer (Y : Set G)) (hgZ : g ∈ normalizer (Z : Set G))
    (hY' : u * g * u⁻¹ ∈ normalizer (Y' : Set G)) (hZ' : u * g * u⁻¹ ∈ normalizer (Z' : Set G))
    (v : ↥Y ⧸ Z.subgroupOf Y) :
    secMap u h h' hZZ' hZ'Z (secAut g hgY hgZ v) =
      secAut (u * g * u⁻¹) hY' hZ' (secMap u h h' hZZ' hZ'Z v) := by
  induction v using QuotientGroup.induction_on with
  | H y =>
    rw [secAut_mk, secMap_mk, secMap_mk, secAut_mk]
    congr 1
    apply Subtype.ext
    change u * (g * (y : G) * g⁻¹) * u⁻¹ = u * g * u⁻¹ * (u * (y : G) * u⁻¹) * (u * g * u⁻¹)⁻¹
    group

end Transport

section Pair

variable {Y₂ Y₁ F Z : Subgroup G} [(F.subgroupOf Y₂).Normal] [(F.subgroupOf Y₁).Normal]
  [(Z.subgroupOf F).Normal]

theorem comm_mul_eq {x y f f' : G} (h1 : f * y = y * f) (h2 : f * f' = f' * f)
    (h3 : f' * x⁻¹ = x⁻¹ * f') :
    x * f * (y * f') * (x * f)⁻¹ * (y * f')⁻¹ = x * y * x⁻¹ * y⁻¹ := by
  calc x * f * (y * f') * (x * f)⁻¹ * (y * f')⁻¹
      = x * (f * y) * f' * f⁻¹ * x⁻¹ * f'⁻¹ * y⁻¹ := by group
    _ = x * (y * f) * f' * f⁻¹ * x⁻¹ * f'⁻¹ * y⁻¹ := by rw [h1]
    _ = x * y * (f * f') * f⁻¹ * x⁻¹ * f'⁻¹ * y⁻¹ := by group
    _ = x * y * (f' * f) * f⁻¹ * x⁻¹ * f'⁻¹ * y⁻¹ := by rw [h2]
    _ = x * y * (f' * x⁻¹) * f'⁻¹ * y⁻¹ := by group
    _ = x * y * (x⁻¹ * f') * f'⁻¹ * y⁻¹ := by rw [h3]
    _ = x * y * x⁻¹ * y⁻¹ := by group

@[expose] noncomputable def secPair (hmem : ∀ x ∈ Y₂, ∀ y ∈ Y₁, x * y * x⁻¹ * y⁻¹ ∈ F) :
    ↥Y₂ ⧸ F.subgroupOf Y₂ → ↥Y₁ ⧸ F.subgroupOf Y₁ → ↥F ⧸ Z.subgroupOf F :=
  fun v w => QuotientGroup.mk ⟨(Quotient.out v : Y₂) * (Quotient.out w : Y₁) *
    (Quotient.out v : Y₂)⁻¹ * (Quotient.out w : Y₁)⁻¹, hmem _ (Quotient.out v).2 _
      (Quotient.out w).2⟩

theorem secPair_mk (hmem : ∀ x ∈ Y₂, ∀ y ∈ Y₁, x * y * x⁻¹ * y⁻¹ ∈ F) (hFY₂ : F ≤ Y₂)
    (hc₂ : ∀ f ∈ F, ∀ x ∈ Y₂, x * f = f * x)
    (hc₁ : ∀ f ∈ F, ∀ y ∈ Y₁, y * f = f * y) (x : Y₂) (y : Y₁) :
    secPair (Z := Z) hmem (x : ↥Y₂ ⧸ F.subgroupOf Y₂) (y : ↥Y₁ ⧸ F.subgroupOf Y₁) =
      QuotientGroup.mk ⟨(x : G) * y * (x : G)⁻¹ * (y : G)⁻¹, hmem _ x.2 _ y.2⟩ := by
  obtain ⟨a, ha⟩ := QuotientGroup.mk_out_eq_mul (F.subgroupOf Y₂) x
  obtain ⟨b, hb⟩ := QuotientGroup.mk_out_eq_mul (F.subgroupOf Y₁) y
  unfold secPair
  congr 1
  apply Subtype.ext
  have haF : (a : G) ∈ F := a.2
  have hbF : (b : G) ∈ F := b.2
  show ((Quotient.out (x : ↥Y₂ ⧸ F.subgroupOf Y₂) : Y₂) : G) *
      ((Quotient.out (y : ↥Y₁ ⧸ F.subgroupOf Y₁) : Y₁) : G) *
      ((Quotient.out (x : ↥Y₂ ⧸ F.subgroupOf Y₂) : Y₂) : G)⁻¹ *
      ((Quotient.out (y : ↥Y₁ ⧸ F.subgroupOf Y₁) : Y₁) : G)⁻¹ =
    (x : G) * y * (x : G)⁻¹ * (y : G)⁻¹
  rw [ha, hb]
  change (x : G) * a * ((y : G) * b) * ((x : G) * a)⁻¹ * ((y : G) * b)⁻¹ =
    (x : G) * y * (x : G)⁻¹ * (y : G)⁻¹
  refine comm_mul_eq (hc₁ _ haF y y.2).symm (hc₂ _ hbF a (hFY₂ haF)) ?_
  have hxb : Commute (x : G) (b : G) := hc₂ _ hbF x x.2
  exact hxb.inv_left.eq.symm

theorem secPair_secAut (hmem : ∀ x ∈ Y₂, ∀ y ∈ Y₁, x * y * x⁻¹ * y⁻¹ ∈ F) (hFY₂ : F ≤ Y₂)
    (hc₂ : ∀ f ∈ F, ∀ x ∈ Y₂, x * f = f * x)
    (hc₁ : ∀ f ∈ F, ∀ y ∈ Y₁, y * f = f * y) {g : G} (hg₂ : g ∈ normalizer (Y₂ : Set G))
    (hg₁ : g ∈ normalizer (Y₁ : Set G)) (hgF : g ∈ normalizer (F : Set G))
    (hgZ : g ∈ normalizer (Z : Set G)) (v : ↥Y₂ ⧸ F.subgroupOf Y₂) (w : ↥Y₁ ⧸ F.subgroupOf Y₁) :
    secPair (Z := Z) hmem (secAut g hg₂ hgF v) (secAut g hg₁ hgF w) =
      secAut g hgF hgZ (secPair hmem v w) := by
  induction v using QuotientGroup.induction_on with
  | H x =>
    induction w using QuotientGroup.induction_on with
    | H y =>
      rw [secAut_mk, secAut_mk, secPair_mk hmem hFY₂ hc₂ hc₁,
        secPair_mk hmem hFY₂ hc₂ hc₁, secAut_mk]
      congr 1
      apply Subtype.ext
      change g * (x : G) * g⁻¹ * (g * (y : G) * g⁻¹) * (g * (x : G) * g⁻¹)⁻¹ *
        (g * (y : G) * g⁻¹)⁻¹ = g * ((x : G) * y * (x : G)⁻¹ * (y : G)⁻¹) * g⁻¹
      group

theorem secPair_mul_right (hmem : ∀ x ∈ Y₂, ∀ y ∈ Y₁, x * y * x⁻¹ * y⁻¹ ∈ F) (hFY₂ : F ≤ Y₂)
    (hc₂ : ∀ f ∈ F, ∀ x ∈ Y₂, x * f = f * x)
    (hc₁ : ∀ f ∈ F, ∀ y ∈ Y₁, y * f = f * y) (v : ↥Y₂ ⧸ F.subgroupOf Y₂)
    (w w' : ↥Y₁ ⧸ F.subgroupOf Y₁) :
    secPair (Z := Z) hmem v (w * w') = secPair hmem v w * secPair hmem v w' := by
  induction v using QuotientGroup.induction_on with
  | H x =>
    induction w using QuotientGroup.induction_on with
    | H y =>
      induction w' using QuotientGroup.induction_on with
      | H y' =>
        rw [← QuotientGroup.mk_mul, secPair_mk hmem hFY₂ hc₂ hc₁,
          secPair_mk hmem hFY₂ hc₂ hc₁, secPair_mk hmem hFY₂ hc₂ hc₁,
          ← QuotientGroup.mk_mul]
        congr 1
        apply Subtype.ext
        have hf : (y : G) * ((x : G) * y' * (x : G)⁻¹ * (y' : G)⁻¹) =
            ((x : G) * y' * (x : G)⁻¹ * (y' : G)⁻¹) * y :=
          hc₁ _ (hmem _ x.2 _ y'.2) y y.2
        change (x : G) * (y * y') * (x : G)⁻¹ * ((y : G) * y')⁻¹ =
          (x : G) * y * (x : G)⁻¹ * (y : G)⁻¹ * ((x : G) * y' * (x : G)⁻¹ * (y' : G)⁻¹)
        calc (x : G) * (y * y') * (x : G)⁻¹ * ((y : G) * y')⁻¹
            = ((x : G) * y * (x : G)⁻¹ * (y : G)⁻¹) *
              ((y : G) * ((x : G) * y' * (x : G)⁻¹ * (y' : G)⁻¹) * (y : G)⁻¹) := by group
          _ = _ := by rw [hf]; group

end Pair

end CFSG.LocalAnalysis.EvenBN.Sp4.BothTrivialTwist
