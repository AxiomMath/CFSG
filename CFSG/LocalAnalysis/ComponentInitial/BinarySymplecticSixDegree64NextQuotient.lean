module

public import CFSG.LocalAnalysis.ComponentInitial.BinarySymplecticSixDegree64NextKernel
public import CFSG.LocalAnalysis.ComponentInitial.BinaryInvolutionEqualFixedImageLifting

public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.LocalAnalysis.ComponentInitial.BinarySymplecticSix.Degree64

open Subgroup Module Matrix SymplecticFlag CFSG.Assembly.LowTwoRank RadicalLabels FusionOrbits
open LinearMap (BilinForm)
open scoped Pointwise

local notation "M₃" => Matrix (Fin 3) (Fin 3) (ZMod 2)

section Generic

variable {F : Type*} [Group F]

theorem eq_bot_of_normal_isPGroup_GL (N : Subgroup (GL (Fin 3) (ZMod 2))) (hN : N.Normal)
    (h2 : IsPGroup 2 N) : N = ⊥ := by
  rcases isSimpleGroup_GL_three_two.eq_bot_or_eq_top_of_normal N with h | h
  · exact h
  · exfalso
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    obtain ⟨k, hk⟩ := h2.exists_card_eq
    rw [h, Subgroup.card_top, card_GL_three_two] at hk
    have h7 : 7 ∣ 2 ^ k := hk ▸ (by norm_num : 7 ∣ 168)
    exact absurd (Nat.Prime.dvd_of_dvd_pow (by norm_num : Nat.Prime 7) h7) (by norm_num)

theorem exists_not_comm_of_sylow [Finite F] {a : F}
    (hC : Nat.card (centralizer ({a} : Set F)) = 336) (h32 : 2 ^ 5 ∣ Nat.card F)
    (S : Sylow 2 F) : ∃ y ∈ S, y * a ≠ a * y := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_contra h
  push Not at h
  have hle : (S : Subgroup F) ≤ centralizer ({a} : Set F) := fun y hy =>
    mem_centralizer_singleton_iff.2 (h y hy)
  have hdvd1 : Nat.card S ∣ 336 := hC ▸ Subgroup.card_dvd_of_le hle
  have hdvd2 : 2 ^ 5 ∣ Nat.card S := S.pow_dvd_card_of_pow_dvd_card h32
  have h3 := Nat.dvd_trans hdvd2 hdvd1
  norm_num at h3

theorem pCore_eq_bot_of_centralizer_GL [Finite F] {a : F} (hao : orderOf a = 2)
    (ψ : Multiplicative (ZMod 2) × GL (Fin 3) (ZMod 2) ≃* centralizer ({a} : Set F))
    (hψ : ∀ s : Multiplicative (ZMod 2), ((ψ (s, 1) : centralizer ({a} : Set F)) : F) ∈ zpowers a)
    (hnc : ∃ y : F, y * a ≠ a * y) : CFSG.Assembly.pCore 2 F = ⊥ := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hQn : (CFSG.pCore 2 F).Normal := CFSG.pCore_normal
  have hQ2 : IsPGroup 2 (CFSG.pCore 2 F) := CFSG.pCore_isPGroup
  have ha1 : a ≠ 1 := fun h => by
    rw [h, orderOf_one] at hao
    exact absurd hao (by norm_num)
  have hza : ∀ x ∈ zpowers a, x = 1 ∨ x = a := fun x hx => eq_one_or_eq_of_mem_zpowers hao hx
  by_contra hQ
  obtain ⟨q, hqQ, hq1, hqa⟩ : ∃ q ∈ CFSG.pCore 2 F, q ≠ 1 ∧ q * a = a * q := by
    let _ : MulAction (zpowers a) (CFSG.pCore 2 F) :=
      MulAction.compHom (CFSG.pCore 2 F)
        ((MulAut.conjNormal (H := CFSG.pCore 2 F)).comp (zpowers a).subtype)
    have hW : IsPGroup 2 (zpowers a) :=
      IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hao, pow_one])
    have hmod := hW.card_modEq_card_fixedPoints (CFSG.pCore 2 F)
    have h1mem : (1 : CFSG.pCore 2 F) ∈ MulAction.fixedPoints (zpowers a) (CFSG.pCore 2 F) := by
      intro g
      apply Subtype.ext
      change (g : F) * 1 * (g : F)⁻¹ = 1
      group
    obtain ⟨k, hk⟩ := hQ2.exists_card_eq
    have hk0 : k ≠ 0 := by
      rintro rfl
      exact hQ (Subgroup.card_eq_one.1 (by rw [hk, pow_zero]))
    have h2 : 1 < Nat.card (MulAction.fixedPoints (zpowers a) (CFSG.pCore 2 F)) := by
      have hpos : 0 < Nat.card (MulAction.fixedPoints (zpowers a) (CFSG.pCore 2 F)) := by
        have : Nonempty (MulAction.fixedPoints (zpowers a) (CFSG.pCore 2 F)) := ⟨⟨1, h1mem⟩⟩
        exact Nat.card_pos
      rw [hk] at hmod
      unfold Nat.ModEq at hmod
      have h3 : 2 ^ k % 2 = 0 := by
        obtain ⟨k', rfl⟩ := Nat.exists_eq_succ_of_ne_zero hk0
        rw [pow_succ, Nat.mul_mod_left]
      omega
    have : Nontrivial (MulAction.fixedPoints (zpowers a) (CFSG.pCore 2 F)) :=
      Finite.one_lt_card_iff_nontrivial.mp h2
    obtain ⟨⟨q, hq⟩, hq1⟩ :=
      exists_ne (⟨1, h1mem⟩ : MulAction.fixedPoints (zpowers a) (CFSG.pCore 2 F))
    refine ⟨q, q.2, fun h => hq1 (Subtype.ext (Subtype.ext h)), ?_⟩
    have h4 : a * (q : F) * a⁻¹ = q := congrArg Subtype.val (hq ⟨a, mem_zpowers a⟩)
    calc (q : F) * a = a * q * a⁻¹ * a := by rw [h4]
      _ = a * q := by group
  have hRa : ∀ r ∈ CFSG.pCore 2 F, r * a = a * r → r ∈ zpowers a := by
    have hMn : ((CFSG.pCore 2 F ⊓ centralizer ({a} : Set F)).subgroupOf
        (centralizer ({a} : Set F))).Normal := ⟨fun n hn g => by
      rw [mem_subgroupOf] at hn ⊢
      exact ⟨hQn.conj_mem _ (mem_inf.1 hn).1 (g : F), (g * n * g⁻¹).2⟩⟩
    have hM2 : IsPGroup 2 ((CFSG.pCore 2 F ⊓ centralizer ({a} : Set F)).subgroupOf
        (centralizer ({a} : Set F))) :=
      (hQ2.to_le inf_le_left).comap_of_injective _ (centralizer ({a} : Set F)).subtype_injective
    set N := (((CFSG.pCore 2 F ⊓ centralizer ({a} : Set F)).subgroupOf
      (centralizer ({a} : Set F))).map ψ.symm.toMonoidHom).map
        (MonoidHom.snd (Multiplicative (ZMod 2)) (GL (Fin 3) (ZMod 2))) with hN
    have hNn : N.Normal := (hMn.map _ ψ.symm.surjective).map _ fun g => ⟨(1, g), rfl⟩
    have hN2 : IsPGroup 2 N := (hM2.map _).map _
    have hNbot := eq_bot_of_normal_isPGroup_GL N hNn hN2
    intro r hrQ hra
    have hrC : r ∈ centralizer ({a} : Set F) := mem_centralizer_singleton_iff.2 hra
    have hp2 : (ψ.symm ⟨r, hrC⟩).2 = 1 := by
      have h1 : (ψ.symm ⟨r, hrC⟩).2 ∈ N :=
        ⟨ψ.symm ⟨r, hrC⟩, ⟨⟨r, hrC⟩, by
          rw [SetLike.mem_coe, mem_subgroupOf]
          exact mem_inf.2 ⟨hrQ, hrC⟩, rfl⟩, rfl⟩
      rw [hNbot, mem_bot] at h1
      exact h1
    have hr : (⟨r, hrC⟩ : centralizer ({a} : Set F)) = ψ ((ψ.symm ⟨r, hrC⟩).1, 1) := by
      rw [← hp2, Prod.mk.eta, MulEquiv.apply_symm_apply]
    have h := hψ (ψ.symm ⟨r, hrC⟩).1
    rw [← hr] at h
    exact h
  have haQ : a ∈ CFSG.pCore 2 F := by
    rcases hza q (hRa q hqQ hqa) with h | h
    · exact absurd h hq1
    · exact h ▸ hqQ
  have hQa : CFSG.pCore 2 F ≤ zpowers a := by
    have hQnt : Nontrivial (CFSG.pCore 2 F) := (Subgroup.nontrivial_iff_ne_bot _).2 hQ
    have := hQ2.center_nontrivial
    obtain ⟨c, hc1⟩ := exists_ne (1 : center (CFSG.pCore 2 F))
    have hca : ((c : CFSG.pCore 2 F) : F) * a = a * ((c : CFSG.pCore 2 F) : F) :=
      (congrArg Subtype.val (mem_center_iff.1 c.2 ⟨a, haQ⟩)).symm
    have hcA : ((c : CFSG.pCore 2 F) : F) = a := by
      rcases hza _ (hRa _ (c : CFSG.pCore 2 F).2 hca) with h | h
      · exact absurd (Subtype.ext (Subtype.ext h)) hc1
      · exact h
    intro x hx
    refine hRa x hx ?_
    have h' := congrArg Subtype.val (mem_center_iff.1 c.2 ⟨x, hx⟩)
    change x * ((c : CFSG.pCore 2 F) : F) = ((c : CFSG.pCore 2 F) : F) * x at h'
    rw [hcA] at h'
    exact h'
  obtain ⟨y, hy⟩ := hnc
  apply hy
  have h1 : y * a * y⁻¹ ∈ zpowers a := hQa (hQn.conj_mem a haQ y)
  rcases hza _ h1 with h | h
  · exfalso
    apply ha1
    calc a = y⁻¹ * (y * a * y⁻¹) * y := by group
      _ = 1 := by rw [h]; group
  · calc y * a = y * a * y⁻¹ * y := by group
      _ = a * y := by rw [h]

end Generic

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V] {b : BilinForm (ZMod 2) V}
  {e : Basis (Fin 3 ⊕ Fin 3) (ZMod 2) V} (he : IsSymplecticBasis b e)

variable {G : Type} [Group G] {L : Subgroup G} (φ : L ≃* bilinIsometryGroup b) {z : G}
  (hzC : z ∈ centralizer (L : Set G)) (hinf : L ⊓ zpowers z = ⊥) (hz : orderOf z = 2)

local notation "𝒜₂" => pullSub φ (pointwiseStabilizer b (lagrangianOf e))
local notation "ℛ" => radSub φ z e
local notation "𝒩₂" => normalizer ((radSub φ z e : Subgroup G) : Set G)
local notation "𝒩₂₀" => (normalizer ((radSub φ z e : Subgroup G) : Set G) ⊓
  centralizer (Singleton.singleton z : Set G) : Subgroup G)

section Quotient

variable (σ : (normalizer ((radSub φ z e : Subgroup G) : Set G) ⊓
    centralizer (Singleton.singleton z : Set G) : Subgroup G) →* GL (Fin 3) (ZMod 2))
  (hσ : ∀ (n : (normalizer ((radSub φ z e : Subgroup G) : Set G) ⊓
      centralizer (Singleton.singleton z : Set G) : Subgroup G)) (a : G) (ha : a ∈ L) (B : M₃),
    Bᵀ = B →
    LinearMap.toMatrix e e (linOf (φ ⟨a, ha⟩)) = fromBlocks 1 B 0 1 →
    ∃ h : (n : G) * a * (n : G)⁻¹ ∈ L,
      LinearMap.toMatrix e e (linOf (φ ⟨(n : G) * a * (n : G)⁻¹, h⟩)) =
        fromBlocks 1 ((σ n : M₃) * B * (σ n : M₃)ᵀ) 0 1)

include he hzC hinf hz hσ in
theorem degree64_next_quotient [Finite G] {D₂ C₂ V₁ X : Subgroup G}
    {ν₂ : G → ↥(binarySymMatrices 3)}
    (hX : X = normalizer (C₂ : Set G)) [(C₂.subgroupOf X).Normal]
    (hRc : centralizer (ℛ : Set G) = ℛ) (hRD₂ : ℛ ≤ D₂)
    (hν₂z : ∀ d ∈ D₂, d⁻¹ * z * d = radHom φ he hzC hz (Multiplicative.ofAdd (ν₂ d, 1)))
    (hD₂A : ∀ d ∈ D₂, ∀ a ∈ 𝒜₂, d * a = a * d)
    (hD₂H : D₂ ⊓ centralizer ({z} : Set G) = ℛ)
    (hprod₂ : ∀ m ∈ 𝒩₂, ∃ d ∈ D₂, ∃ c ∈ 𝒩₂₀, m = d * c)
    (hC₂D : C₂ ≤ D₂) (hC₂n : ∀ m ∈ 𝒩₂, ∀ c ∈ C₂, m * c * m⁻¹ ∈ C₂)
    (hC₂R : C₂ ⊓ ℛ = 𝒜₂) (hC₂sq : ∀ c ∈ C₂, c ^ 2 = 1)
    (hDzC : (D₂ : Set G) = (zpowers z : Set G) * (C₂ : Set G))
    (hνs : ∀ B : ↥(binarySymMatrices 3), ∃ c ∈ C₂, ν₂ c = B)
    (hC₂card : Nat.card C₂ = 4096) (hV₁X : V₁ ≤ X) (hV₁rel : C₂.relIndex (V₁ ⊔ C₂) = 32) :
    ∃ hzX : z ∈ X,
      centralizer {(QuotientGroup.mk ⟨z, hzX⟩ : X ⧸ C₂.subgroupOf X)} =
        (Subgroup.subgroupOf 𝒩₂ X).map (QuotientGroup.mk' (C₂.subgroupOf X)) ∧ 𝒩₂ ≤ X ∧
      (∃ ψ : Multiplicative (ZMod 2) × GL (Fin 3) (ZMod 2) ≃*
          centralizer {(QuotientGroup.mk ⟨z, hzX⟩ : X ⧸ C₂.subgroupOf X)},
        ∀ (s : ZMod 2) (g : GL (Fin 3) (ZMod 2)) (h : z ^ s.val * leviHom φ he g ∈ X),
          (ψ (Multiplicative.ofAdd s, g) : X ⧸ C₂.subgroupOf X) = QuotientGroup.mk ⟨_, h⟩) ∧
      (∀ S : Sylow 2 (X ⧸ C₂.subgroupOf X),
        (QuotientGroup.mk ⟨z, hzX⟩ : X ⧸ C₂.subgroupOf X) ∈ S →
          ∃ y ∈ S, y * QuotientGroup.mk ⟨z, hzX⟩ ≠
            (QuotientGroup.mk ⟨z, hzX⟩ : X ⧸ C₂.subgroupOf X) * y) ∧
      CFSG.Assembly.pCore 2 (X ⧸ C₂.subgroupOf X) = ⊥ := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hzR : z ∈ ℛ := mem_sup_right (mem_zpowers z)
  have hz2 : z ^ 2 = 1 := by rw [← hz]; exact pow_orderOf_eq_one z
  have hzL : ∀ x ∈ L, x * z = z * x := fun x hx => mul_comm_z hzC hx
  have hA₂L : 𝒜₂ ≤ L := pullSub_le φ _
  have hA₂C₂ : 𝒜₂ ≤ C₂ := radA_le_of_inf_eq φ hC₂R
  have hzC₂ : z ∉ C₂ := z_not_mem_of_inf_eq φ hinf hz hC₂R
  have hCz : ∀ c ∈ C₂, c * z = z * c → c ∈ 𝒜₂ := fun c hc hcz => by
    have h : c ∈ C₂ ⊓ ℛ := by
      refine mem_inf.2 ⟨hc, ?_⟩
      rw [← hD₂H]
      exact mem_inf.2 ⟨hC₂D hc, mem_centralizer_singleton_iff.2 hcz⟩
    rw [hC₂R] at h
    exact h
  have hγC : ∀ c ∈ C₂, z⁻¹ * (c⁻¹ * z * c) ∈ 𝒜₂ := fun c hc => by
    rw [← tauHom_nu he φ hzC hz hν₂z (hC₂D hc)]
    exact (mem_pullSub_iff φ he).2 ⟨_, rfl⟩
  have hmemX : ∀ x : G, x ∈ X ↔ x ∈ normalizer (C₂ : Set G) := fun x => by rw [hX]
  have hN₂X : 𝒩₂ ≤ X := fun n hn => (hmemX n).2 (mem_normalizer_of_conj_mem (hC₂n n hn))
  have hzX : z ∈ X := hN₂X (le_normalizer hzR)
  have hC₂X : C₂ ≤ X := fun c hc => (hmemX c).2 (le_normalizer hc)
  have hlevX : ∀ g : GL (Fin 3) (ZMod 2), leviHom φ he g ∈ X := fun g =>
    hN₂X (leviHom_mem_normalizer_radSub φ he hzC hz g)
  have hzpowX : ∀ t ∈ zpowers z, t ∈ X := fun t ht => (zpowers_le.2 hzX) ht
  have htz : ∀ t ∈ zpowers z, t * z = z * t := fun t ht => by
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 ht
    exact ((Commute.refl z).zpow_left k).eq
  have hE : ∀ x ∈ C₂.subgroupOf X, x ^ 2 = 1 := fun x hx => Subtype.ext (by
    rw [Subgroup.coe_pow, Subgroup.coe_one]
    exact hC₂sq _ (mem_subgroupOf.1 hx))
  have hz2' : (⟨z, hzX⟩ : X) ^ 2 = 1 := Subtype.ext (by
    rw [Subgroup.coe_pow, Subgroup.coe_one]
    exact hz2)
  have hfix : (fun x => x⁻¹ * (⟨z, hzX⟩ : X)⁻¹ * x * ⟨z, hzX⟩) '' ((C₂.subgroupOf X : Subgroup X) :
      Set X) = ((C₂.subgroupOf X ⊓ centralizer {(⟨z, hzX⟩ : X)} : Subgroup X) : Set X) := by
    ext x
    constructor
    · rintro ⟨c, hc, rfl⟩
      have hcC : (c : G) ∈ C₂ := mem_subgroupOf.1 hc
      have hγ := inv_mem (hγC _ hcC)
      have h1 : ((c⁻¹ * (⟨z, hzX⟩ : X)⁻¹ * c * ⟨z, hzX⟩ : X) : G) =
          (z⁻¹ * ((c : G)⁻¹ * z * c))⁻¹ := by
        simp only [Subgroup.coe_mul, Subgroup.coe_inv]
        group
      refine mem_inf.2 ⟨mem_subgroupOf.2 ?_, mem_centralizer_singleton_iff.2 (Subtype.ext ?_)⟩
      · rw [h1]
        exact hA₂C₂ hγ
      · change ((c⁻¹ * (⟨z, hzX⟩ : X)⁻¹ * c * ⟨z, hzX⟩ : X) : G) * z =
          z * ((c⁻¹ * (⟨z, hzX⟩ : X)⁻¹ * c * ⟨z, hzX⟩ : X) : G)
        rw [h1]
        exact hzL _ (hA₂L hγ)
    · intro hx
      obtain ⟨hxE, hxz⟩ := mem_inf.1 hx
      have hxC : (x : G) ∈ C₂ := mem_subgroupOf.1 hxE
      have hxz' : (x : G) * z = z * (x : G) :=
        congrArg Subtype.val (mem_centralizer_singleton_iff.1 hxz)
      have hxA := hCz _ hxC hxz'
      obtain ⟨M, hM⟩ := (mem_pullSub_iff φ he).1 hxA
      obtain ⟨c, hc, hcM⟩ := hνs (Multiplicative.toAdd M)
      have hγc : z⁻¹ * (c⁻¹ * z * c) = (x : G) := by
        rw [← tauHom_nu he φ hzC hz hν₂z (hC₂D hc), hcM, ofAdd_toAdd, hM]
      refine ⟨⟨c, hC₂X hc⟩, mem_subgroupOf.2 hc, Subtype.ext ?_⟩
      have h1 : c⁻¹ * z⁻¹ * c * z = (z⁻¹ * (c⁻¹ * z * c))⁻¹ := by group
      change c⁻¹ * z⁻¹ * c * z = (x : G)
      rw [h1, hγc, inv_eq_of_mem_radA he φ hxA]
  obtain ⟨hcen, -⟩ :=
    EqualFixedImage.binary_involution_equal_fixed_image_centralizer_lifting hE hz2' hfix
  have hCXz : ∀ x : X, x ∈ centralizer {(⟨z, hzX⟩ : X)} → (x : G) ∈ 𝒩₂ := by
    intro x hx
    have hxz : (x : G) * z = z * (x : G) :=
      congrArg Subtype.val (mem_centralizer_singleton_iff.1 hx)
    have hxN : (x : G) ∈ normalizer (C₂ : Set G) := (hmemX x).1 x.2
    have hx1 : (x : G)⁻¹ * z = z * (x : G)⁻¹ := by
      rw [inv_mul_eq_iff_eq_mul, ← mul_assoc, hxz, mul_inv_cancel_right]
    refine mem_normalizer_of_conj_mem fun r hr => ?_
    refine (sup_le (fun a ha => ?_) ?_ :
      ℛ ≤ Subgroup.comap (MulAut.conj (x : G)).toMonoidHom ℛ) hr
    · rw [mem_comap, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      have h1 : (x : G) * a * (x : G)⁻¹ ∈ C₂ := (mem_normalizer_iff.1 hxN a).1 (hA₂C₂ ha)
      have h2 : (x : G) * a * (x : G)⁻¹ * z = z * ((x : G) * a * (x : G)⁻¹) := by
        calc (x : G) * a * (x : G)⁻¹ * z = (x : G) * a * ((x : G)⁻¹ * z) := by group
          _ = (x : G) * a * (z * (x : G)⁻¹) := by rw [hx1]
          _ = (x : G) * (a * z) * (x : G)⁻¹ := by group
          _ = (x : G) * (z * a) * (x : G)⁻¹ := by rw [hzL a (hA₂L ha)]
          _ = ((x : G) * z) * a * (x : G)⁻¹ := by group
          _ = (z * (x : G)) * a * (x : G)⁻¹ := by rw [hxz]
          _ = z * ((x : G) * a * (x : G)⁻¹) := by group
      exact mem_sup_left (hCz _ h1 h2)
    · rw [zpowers_le, mem_comap, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, hxz,
        mul_inv_cancel_right]
      exact mem_sup_right (mem_zpowers z)
  have hcenN : centralizer {(QuotientGroup.mk ⟨z, hzX⟩ : X ⧸ C₂.subgroupOf X)} =
      (Subgroup.subgroupOf 𝒩₂ X).map (QuotientGroup.mk' (C₂.subgroupOf X)) := by
    rw [hcen]
    apply le_antisymm
    · exact Subgroup.map_mono fun x hx => mem_subgroupOf.2 (hCXz x hx)
    · rintro _ ⟨n, hn, rfl⟩
      have hnN : (n : G) ∈ 𝒩₂ := mem_subgroupOf.1 hn
      obtain ⟨d, hd, c, hc, hdc⟩ := hprod₂ _ hnN
      have hd' : d ∈ (zpowers z : Set G) * (C₂ : Set G) := by
        rw [← hDzC]
        exact hd
      obtain ⟨t, ht, c₂, hc₂, htc₂⟩ := hd'
      change t * c₂ = d at htc₂
      have hcz : c * z = z * c := mem_centralizer_singleton_iff.1 (mem_inf.1 hc).2
      refine ⟨⟨t * c, mul_mem (hzpowX t ht) (hN₂X (mem_inf.1 hc).1)⟩,
        mem_centralizer_singleton_iff.2 (Subtype.ext ?_), ?_⟩
      · change t * c * z = z * (t * c)
        rw [mul_assoc, hcz, ← mul_assoc, htz t ht, mul_assoc]
      · rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq, mem_subgroupOf]
        change (t * c)⁻¹ * (n : G) ∈ C₂
        rw [hdc, ← htc₂]
        have h1 : (t * c)⁻¹ * (t * c₂ * c) = c⁻¹ * c₂ * c⁻¹⁻¹ := by group
        rw [h1]
        exact hC₂n _ (inv_mem (mem_inf.1 hc).1) c₂ hc₂
  let zH : Multiplicative (ZMod 2) →* G :=
    { toFun := fun s => z ^ (Multiplicative.toAdd s).val
      map_one' := by rw [toAdd_one, ZMod.val_zero, pow_zero]
      map_mul' := fun s s' => by
        rw [toAdd_mul]
        exact pow_val_add_of_sq hz2 _ _ }
  have hcomm : ∀ s g, Commute (zH s) (leviHom φ he g) := fun s g =>
    (Commute.symm (hzL _ (leviHom_mem φ he g))).pow_left _
  let Λ₀ := zH.noncommCoprod (leviHom φ he) hcomm
  have hΛ₀ : ∀ p, Λ₀ p = z ^ (Multiplicative.toAdd p.1).val * leviHom φ he p.2 := fun p => rfl
  have hΛX : ∀ p, Λ₀ p ∈ X := fun p => by
    rw [hΛ₀]
    exact mul_mem (pow_mem hzX _) (hlevX p.2)
  let f := (QuotientGroup.mk' (C₂.subgroupOf X)).comp (Λ₀.codRestrict X hΛX)
  have hf : ∀ p, f p = QuotientGroup.mk ⟨Λ₀ p, hΛX p⟩ := fun p => rfl
  have hΛz : ∀ p, Λ₀ p * z = z * Λ₀ p := fun p => by
    rw [hΛ₀, mul_assoc, hzL _ (leviHom_mem φ he p.2), ← mul_assoc,
      ((Commute.refl z).pow_left _).eq, mul_assoc]
  have hfinj : Function.Injective f := by
    rw [injective_iff_map_eq_one]
    rintro ⟨s, g⟩ h
    rw [hf, QuotientGroup.eq_one_iff, mem_subgroupOf] at h
    change Λ₀ (s, g) ∈ C₂ at h
    have h3 := hCz _ h (hΛz (s, g))
    rw [hΛ₀] at h3
    have h4 : leviHom φ he g ∈ ℛ := by
      have h5 : leviHom φ he g = (z ^ (Multiplicative.toAdd s).val)⁻¹ *
          (z ^ (Multiplicative.toAdd s).val * leviHom φ he g) := by group
      rw [h5]
      exact mul_mem (inv_mem (mem_sup_right (pow_mem (mem_zpowers z) _))) (mem_sup_left h3)
    have hg : g = 1 := by
      refine symThreeCongrHom_injective (LinearEquiv.ext fun M => ?_)
      rw [symThreeCongrHom_apply, symThreeCongrHom_apply, symThreeCongr_one]
      have h6 := leviHom_conj_tauHom' φ he g M
      have hτA : tauHom φ he (Multiplicative.ofAdd M) ∈ 𝒜₂ := (mem_pullSub_iff φ he).2 ⟨_, rfl⟩
      rw [hD₂A _ (hRD₂ h4) _ hτA, mul_inv_cancel_right] at h6
      exact (Multiplicative.ofAdd.injective (tauHom_injective φ he h6)).symm
    subst hg
    rw [map_one, mul_one] at h3
    have hs : Multiplicative.toAdd s = 0 := by
      rcases zmod_two_eq_zero_or_eq_one (Multiplicative.toAdd s) with h7 | h7
      · exact h7
      · rw [h7, ZMod.val_one, pow_one] at h3
        exact absurd h3 (z_not_mem_radA φ hinf hz)
    have hs' : s = 1 := by
      rw [← ofAdd_toAdd s, hs, ofAdd_zero]
    rw [hs']
    rfl
  have hrange : f.range = centralizer {(QuotientGroup.mk ⟨z, hzX⟩ : X ⧸ C₂.subgroupOf X)} := by
    apply le_antisymm
    · rintro _ ⟨p, rfl⟩
      rw [mem_centralizer_singleton_iff, hf, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
      congr 1
      exact Subtype.ext (hΛz p)
    · rw [hcen]
      rintro _ ⟨x, hx, rfl⟩
      have hxN₂ := hCXz x hx
      have hxz : (x : G) * z = z * (x : G) :=
        congrArg Subtype.val (mem_centralizer_singleton_iff.1 hx)
      have hxN₂₀ : (x : G) ∈ 𝒩₂₀ := mem_inf.2 ⟨hxN₂, mem_centralizer_singleton_iff.2 hxz⟩
      set g := σ ⟨x, hxN₂₀⟩ with hg
      have hyA : ∀ M : ↥(binarySymMatrices 3), (x : G) * (leviHom φ he g)⁻¹ *
          tauHom φ he (Multiplicative.ofAdd M) * ((x : G) * (leviHom φ he g)⁻¹)⁻¹ =
            tauHom φ he (Multiplicative.ofAdd M) := by
        intro M
        have h1 := leviHom_conj_tauHom' φ he g⁻¹ M
        rw [map_inv, inv_inv] at h1
        have h2 := conj_tauHom_of_sigma φ he σ hσ ⟨x, hxN₂₀⟩ (symThreeCongr g⁻¹ M)
        rw [← hg, ← symThreeCongr_mul, mul_inv_cancel, symThreeCongr_one] at h2
        calc (x : G) * (leviHom φ he g)⁻¹ * tauHom φ he (Multiplicative.ofAdd M) *
            ((x : G) * (leviHom φ he g)⁻¹)⁻¹ =
            (x : G) * ((leviHom φ he g)⁻¹ * tauHom φ he (Multiplicative.ofAdd M) *
              leviHom φ he g) * (x : G)⁻¹ := by group
          _ = _ := by rw [h1]; exact h2
      have hyz : (x : G) * (leviHom φ he g)⁻¹ * z = z * ((x : G) * (leviHom φ he g)⁻¹) := by
        have h1 : (leviHom φ he g)⁻¹ * z = z * (leviHom φ he g)⁻¹ := by
          rw [inv_mul_eq_iff_eq_mul, ← mul_assoc, hzL _ (leviHom_mem φ he g),
            mul_inv_cancel_right]
        rw [mul_assoc, h1, ← mul_assoc, hxz, mul_assoc]
      have hyR : (x : G) * (leviHom φ he g)⁻¹ ∈ ℛ := by
        rw [← hRc, mem_centralizer_iff]
        intro r hr
        refine mem_centralizer_singleton_iff.1 ((sup_le (fun a ha => ?_) ?_ :
          ℛ ≤ centralizer ({(x : G) * (leviHom φ he g)⁻¹} : Set G)) hr)
        · obtain ⟨M, rfl⟩ := (mem_pullSub_iff φ he).1 ha
          refine mem_centralizer_singleton_iff.2 ?_
          have h1 := hyA (Multiplicative.toAdd M)
          rw [ofAdd_toAdd] at h1
          calc tauHom φ he M * ((x : G) * (leviHom φ he g)⁻¹) =
              ((x : G) * (leviHom φ he g)⁻¹ * tauHom φ he M *
                ((x : G) * (leviHom φ he g)⁻¹)⁻¹) * ((x : G) * (leviHom φ he g)⁻¹) := by
                rw [h1]
            _ = (x : G) * (leviHom φ he g)⁻¹ * tauHom φ he M := by group
        · rw [zpowers_le]
          exact mem_centralizer_singleton_iff.2 hyz.symm
      obtain ⟨B, ε, hBε⟩ := (mem_radSub_iff φ he hzC hz).1 hyR
      refine ⟨(Multiplicative.ofAdd ε, g), ?_⟩
      rw [hf, QuotientGroup.mk'_apply, QuotientGroup.eq, mem_subgroupOf]
      change (Λ₀ (Multiplicative.ofAdd ε, g))⁻¹ * (x : G) ∈ C₂
      rw [hΛ₀]
      have hx' : (x : G) = tauHom φ he (Multiplicative.ofAdd B) * zPow z ε * leviHom φ he g := by
        rw [hBε, inv_mul_cancel_right]
      rw [hx']
      have hc := mul_comm_zPow hzC (tauHom_mem φ he (Multiplicative.ofAdd B)) ε
      have h1 : (z ^ (Multiplicative.toAdd (Multiplicative.ofAdd ε)).val * leviHom φ he g)⁻¹ *
          (tauHom φ he (Multiplicative.ofAdd B) * zPow z ε * leviHom φ he g) =
          (leviHom φ he g)⁻¹ * tauHom φ he (Multiplicative.ofAdd B) * (leviHom φ he g)⁻¹⁻¹ := by
        change (zPow z ε * leviHom φ he g)⁻¹ *
          (tauHom φ he (Multiplicative.ofAdd B) * zPow z ε * leviHom φ he g) = _
        calc (zPow z ε * leviHom φ he g)⁻¹ *
            (tauHom φ he (Multiplicative.ofAdd B) * zPow z ε * leviHom φ he g) =
            (leviHom φ he g)⁻¹ * ((zPow z ε)⁻¹ * (tauHom φ he (Multiplicative.ofAdd B) *
              zPow z ε) * leviHom φ he g) := by group
          _ = (leviHom φ he g)⁻¹ * ((zPow z ε)⁻¹ * (zPow z ε *
              tauHom φ he (Multiplicative.ofAdd B)) * leviHom φ he g) := by rw [hc]
          _ = _ := by group
      rw [h1]
      have hwN : (leviHom φ he g)⁻¹ ∈ 𝒩₂ := inv_mem (leviHom_mem_normalizer_radSub φ he hzC hz g)
      exact hC₂n _ hwN _ (hA₂C₂ ((mem_pullSub_iff φ he).2 ⟨_, rfl⟩))
  set ψ := (MonoidHom.ofInjective hfinj).trans (MulEquiv.subgroupCongr hrange) with hψdef
  have hψ : ∀ p, (ψ p : X ⧸ C₂.subgroupOf X) = f p := fun p => rfl
  have hψmk : ∀ (s : ZMod 2) (g : GL (Fin 3) (ZMod 2)) (h : z ^ s.val * leviHom φ he g ∈ X),
      (ψ (Multiplicative.ofAdd s, g) : X ⧸ C₂.subgroupOf X) = QuotientGroup.mk ⟨_, h⟩ :=
    fun s g h => by rw [hψ, hf]; rfl
  have hcardC : Nat.card (centralizer {(QuotientGroup.mk ⟨z, hzX⟩ : X ⧸ C₂.subgroupOf X)}) =
      336 := by
    rw [← Nat.card_congr ψ.toEquiv, Nat.card_prod, card_GL_three_two,
      show Nat.card (Multiplicative (ZMod 2)) = Nat.card (ZMod 2) from rfl, Nat.card_zmod]
  have h32 : 2 ^ 5 ∣ Nat.card (X ⧸ C₂.subgroupOf X) := by
    have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup (C₂.subgroupOf X)
    rw [Nat.card_congr (subgroupOfEquivOfLe hC₂X).toEquiv, hC₂card] at h1
    have h2 := Subgroup.relIndex_mul_card (H := C₂) (K := V₁ ⊔ C₂)
    rw [inf_of_le_left le_sup_right, hV₁rel, hC₂card] at h2
    have h3 : Nat.card (V₁ ⊔ C₂ : Subgroup G) ∣ Nat.card X :=
      Subgroup.card_dvd_of_le (sup_le hV₁X hC₂X)
    rw [← h2, h1] at h3
    exact Nat.dvd_of_mul_dvd_mul_right (by norm_num : 0 < 4096) (by simpa using h3)
  have hSyl : ∀ S : Sylow 2 (X ⧸ C₂.subgroupOf X),
      (QuotientGroup.mk ⟨z, hzX⟩ : X ⧸ C₂.subgroupOf X) ∈ S →
        ∃ y ∈ S, y * QuotientGroup.mk ⟨z, hzX⟩ ≠
          (QuotientGroup.mk ⟨z, hzX⟩ : X ⧸ C₂.subgroupOf X) * y := fun S _ =>
    exists_not_comm_of_sylow hcardC h32 S
  have hzbar : orderOf (QuotientGroup.mk ⟨z, hzX⟩ : X ⧸ C₂.subgroupOf X) = 2 := by
    refine orderOf_eq_prime ?_ ?_
    · rw [← QuotientGroup.mk_pow, hz2', QuotientGroup.mk_one]
    · rw [Ne, QuotientGroup.eq_one_iff, mem_subgroupOf]
      exact hzC₂
  have hnc : ∃ y : X ⧸ C₂.subgroupOf X,
      y * QuotientGroup.mk ⟨z, hzX⟩ ≠ (QuotientGroup.mk ⟨z, hzX⟩ : X ⧸ C₂.subgroupOf X) * y := by
    have hW : IsPGroup 2 (zpowers (QuotientGroup.mk ⟨z, hzX⟩ : X ⧸ C₂.subgroupOf X)) :=
      IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hzbar, pow_one])
    obtain ⟨S, hS⟩ := hW.exists_le_sylow
    obtain ⟨y, -, hy⟩ := hSyl S (hS (mem_zpowers _))
    exact ⟨y, hy⟩
  have hψ1 : ∀ s : Multiplicative (ZMod 2), ((ψ (s, 1) : centralizer
      {(QuotientGroup.mk ⟨z, hzX⟩ : X ⧸ C₂.subgroupOf X)}) : X ⧸ C₂.subgroupOf X) ∈
        zpowers (QuotientGroup.mk ⟨z, hzX⟩ : X ⧸ C₂.subgroupOf X) := by
    intro s
    rw [hψ, hf]
    have h1 : (⟨Λ₀ (s, 1), hΛX (s, 1)⟩ : X) = (⟨z, hzX⟩ : X) ^ (Multiplicative.toAdd s).val :=
      Subtype.ext (by
        change Λ₀ (s, 1) = (((⟨z, hzX⟩ : X) ^ (Multiplicative.toAdd s).val : X) : G)
        rw [hΛ₀, map_one, mul_one, Subgroup.coe_pow])
    rw [h1, QuotientGroup.mk_pow]
    exact pow_mem (mem_zpowers _) _
  exact ⟨hzX, hcenN, hN₂X, ⟨ψ, hψmk⟩, hSyl,
    pCore_eq_bot_of_centralizer_GL hzbar ψ hψ1 hnc⟩

end Quotient

end CFSG.LocalAnalysis.ComponentInitial.BinarySymplecticSix.Degree64
