module

public import CFSG.LocalAnalysis.EvenBN.G2.LocalP35A

public section

namespace CFSG.LocalAnalysis.EvenBN.G2

open Subgroup CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.ComponentClassification.UnbalancedCatalog CFSG.ComponentClassification.RankTwoExceptional
open CFSG.LocalAnalysis.EvenBN.Common (CosetData)
open scoped commutatorElement Pointwise

section Generic

variable {G : Type*} [Group G]

private theorem sq_mul_eq_comm_mul_sq {w m : G} (hw : w * w = 1) :
    w * m * (w * m) = (w * m * w⁻¹ * m⁻¹) * (m * m) := by
  have h : w⁻¹ = w := inv_eq_of_mul_eq_one_right hw
  rw [h]
  group

private theorem mul_self_eq_one_of_isElementaryAbelian {A : Subgroup G}
    (hA : CFSG.IsElementaryAbelian 2 A) {a : G} (ha : a ∈ A) : a * a = 1 := by
  have := hA
  rw [← sq]
  exact CFSG.elemPow_eq_one_of_isElementaryAbelian a ha

private theorem mul_comm_of_isElementaryAbelian {A : Subgroup G} (hA : CFSG.IsElementaryAbelian 2 A)
    {a b : G} (ha : a ∈ A) (hb : b ∈ A) : a * b = b * a := by
  have := hA
  exact congrArg Subtype.val (mul_comm' (⟨a, ha⟩ : A) ⟨b, hb⟩)

private noncomputable def commMap (A : Subgroup G) (t : G) (hA : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a)
    (ht : t ∈ normalizer (A : Set G)) : A →* A :=
  MonoidHom.mk' (fun a => ⟨t * a * t⁻¹ * a⁻¹,
    mul_mem ((mem_normalizer_iff.1 ht a).1 a.2) (inv_mem a.2)⟩)
    (fun a b => by
      apply Subtype.ext
      have hb' : t * (b : G) * t⁻¹ ∈ A := (mem_normalizer_iff.1 ht b).1 b.2
      have hcomm : ((t * (b : G) * t⁻¹) * (b : G)⁻¹) * (a : G)⁻¹ =
          (a : G)⁻¹ * ((t * (b : G) * t⁻¹) * (b : G)⁻¹) :=
        hA _ (mul_mem hb' (inv_mem b.2)) _ (inv_mem a.2)
      show t * ((a : G) * b) * t⁻¹ * ((a : G) * b)⁻¹ =
        (t * (a : G) * t⁻¹ * (a : G)⁻¹) * (t * (b : G) * t⁻¹ * (b : G)⁻¹)
      calc t * ((a : G) * b) * t⁻¹ * ((a : G) * b)⁻¹
          = (t * (a : G) * t⁻¹) * (((t * (b : G) * t⁻¹) * (b : G)⁻¹) * (a : G)⁻¹) := by group
        _ = (t * (a : G) * t⁻¹) * ((a : G)⁻¹ * ((t * (b : G) * t⁻¹) * (b : G)⁻¹)) := by
          rw [hcomm]
        _ = (t * (a : G) * t⁻¹ * (a : G)⁻¹) * (t * (b : G) * t⁻¹ * (b : G)⁻¹) := by group)

private theorem exists_subgroup_card_commutator {A : Subgroup G}
    (hA : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a) (hAe : ∀ a ∈ A, a * a = 1) {t : G} (htt : t * t = 1)
    (ht : t ∈ normalizer (A : Set G)) :
    ∃ B : Subgroup G, B ≤ A ∧ (∀ a ∈ A, (t * a) * (t * a) ∈ B) ∧
      (∀ b ∈ B, ∃ a ∈ A, b = (t * a) * (t * a)) ∧
      Nat.card B * Nat.card (A ⊓ centralizer ({t} : Set G) : Subgroup G) = Nat.card A := by
  set ψ := commMap A t hA ht with hψ
  have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_right htt
  have key : ∀ a : A, ((ψ a : A) : G) = (t * a) * (t * a) := by
    intro a
    have hainv : (a : G)⁻¹ = a := inv_eq_of_mul_eq_one_right (hAe a a.2)
    show t * (a : G) * t⁻¹ * (a : G)⁻¹ = (t * a) * (t * a)
    rw [htinv, hainv]
    group
  have hker : ψ.ker.map A.subtype = A ⊓ centralizer ({t} : Set G) := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      have h1 : t * (y : G) * t⁻¹ * (y : G)⁻¹ = 1 := congrArg Subtype.val hy
      have h2 : t * (y : G) * t⁻¹ = y := mul_inv_eq_one.1 h1
      have h3 : t * (y : G) = y * t := mul_inv_eq_iff_eq_mul.1 h2
      exact ⟨y.2, mem_centralizer_singleton_iff.2 h3.symm⟩
    · rintro ⟨hxA, hxC⟩
      refine ⟨⟨x, hxA⟩, ?_, rfl⟩
      apply Subtype.ext
      have hxC' : x * t = t * x := mem_centralizer_singleton_iff.1 hxC
      show t * x * t⁻¹ * x⁻¹ = 1
      rw [← hxC']
      group
  refine ⟨ψ.range.map A.subtype, ?_, ?_, ?_, ?_⟩
  · rintro _ ⟨y, -, rfl⟩
    exact y.2
  · intro a ha
    exact ⟨ψ ⟨a, ha⟩, ⟨⟨a, ha⟩, rfl⟩, key ⟨a, ha⟩⟩
  · rintro _ ⟨_, ⟨a, rfl⟩, rfl⟩
    exact ⟨a, a.2, key a⟩
  · rw [Subgroup.card_map_of_injective A.subtype_injective, ← hker,
      Subgroup.card_map_of_injective A.subtype_injective, mul_comm]
    exact Subgroup.card_ker_mul_card_range ψ

private def commNormalizer (A N : Subgroup G) : Subgroup G where
  carrier := {m | m ∈ normalizer (N : Set G) ∧ ∀ a ∈ A, a * m * a⁻¹ * m⁻¹ ∈ N}
  one_mem' := by
    refine ⟨one_mem _, fun a ha => ?_⟩
    simp
  mul_mem' := by
    rintro m₁ m₂ ⟨hm₁N, hm₁⟩ ⟨hm₂N, hm₂⟩
    refine ⟨mul_mem hm₁N hm₂N, fun a ha => ?_⟩
    have e : a * (m₁ * m₂) * a⁻¹ * (m₁ * m₂)⁻¹ =
        (a * m₁ * a⁻¹ * m₁⁻¹) * (m₁ * (a * m₂ * a⁻¹ * m₂⁻¹) * m₁⁻¹) := by group
    rw [e]
    exact mul_mem (hm₁ a ha) ((mem_normalizer_iff.1 hm₁N _).1 (hm₂ a ha))
  inv_mem' := by
    rintro m ⟨hmN, hm⟩
    refine ⟨inv_mem hmN, fun a ha => ?_⟩
    have e : a * m⁻¹ * a⁻¹ * m⁻¹⁻¹ = m⁻¹ * (a * m * a⁻¹ * m⁻¹)⁻¹ * m⁻¹⁻¹ := by group
    rw [e]
    exact (mem_normalizer_iff.1 (inv_mem hmN) _).1 (inv_mem (hm a ha))

private theorem autImage_commutator_mem {H : Subgroup G} (φ : H ≃* H) {A B N : Subgroup G}
    (hAB : ∀ a ∈ A, ∀ b ∈ B, a * b * a⁻¹ * b⁻¹ ∈ N) :
    ∀ y ∈ autImage φ A, ∀ g ∈ autImage φ B, y * g * y⁻¹ * g⁻¹ ∈ autImage φ N := by
  intro y hy g hg
  obtain ⟨a, ha, rfl⟩ := mem_autImage.1 hy
  obtain ⟨b, hb, rfl⟩ := mem_autImage.1 hg
  refine mem_autImage.2 ⟨a * b * a⁻¹ * b⁻¹, hAB _ ha _ hb, ?_⟩
  simp only [map_mul, map_inv, Subgroup.coe_mul, Subgroup.coe_inv]

private theorem isElementaryAbelian_autImage {H : Subgroup G} (φ : H ≃* H) {A : Subgroup G}
    (hc : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x) (hs : ∀ x ∈ A, x * x = 1) :
    CFSG.IsElementaryAbelian 2 (autImage φ A) := by
  refine isElementaryAbelian_two_of_forall (mul_comm_of_mem_autImage φ hc) fun x hx => ?_
  obtain ⟨a, ha, rfl⟩ := mem_autImage.1 hx
  have h1 : a * a = 1 := Subtype.ext (hs a ha)
  rw [← Subgroup.coe_mul, ← map_mul, h1, map_one]
  rfl

end Generic

namespace Setup

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {f : ℕ} {t : G}

section Local

variable
  {K : Type} [Field K] [Finite K]
  [CharP K 2]

private theorem yamadaR₃_inf_centralizer_le (hW : CFSG.Walter.WalterOrderForm) (h : Setup G L f t)
    (d : G2Data L K) (hK : Nat.card K = 2 ^ f) (hQ : h.QFacts d) {x : G}
    (hx : x ∈ yamadaR₃ d t) (hxC : x ∈ centralizer ({t} : Set G)) : x ∈ yamadaR₂ d t := by
  have hD := hQ.doubling
  obtain ⟨hR₃R, -, -, -, -⟩ := h.yamadaR₃_facts hW d hK hD
  exact (h.yamada_5_6_1 d hK).2.1 (h.yamadaRstar_inf_centralizer_le d hK hD ⟨hR₃R hx, hxC⟩)

private theorem yamadaW₃_inf_yamadaR₂ (hW : CFSG.Walter.WalterOrderForm) (h : Setup G L f t)
    (d : G2Data L K) (hK : Nat.card K = 2 ^ f) (hQ : h.QFacts d) :
    yamadaW₃ d t ⊓ yamadaR₂ d t = yamadaW₂ d t := by
  have hD := hQ.doubling
  obtain ⟨hW₃V₃, -, -, hW₂W₃, htW₃, -, -⟩ := h.yamadaW₃_facts hW d hK hD
  obtain ⟨-, -, -, hV₃R₂, -, -, -, -, -⟩ := h.yamadaV₃_facts hW d hK hD
  refine le_antisymm (fun x hx => ?_) (le_inf hW₂W₃ (sup_le (h.yamada_5_8_3 d hK).1
    (h.yamadaY₂_le_yamadaR₂ d hK hD)))
  obtain ⟨hxW₃, hxR₂⟩ := Subgroup.mem_inf.1 hx
  have hxV₂ : x ∈ yamadaV₂ d t := by
    rw [← hV₃R₂]
    exact Subgroup.mem_inf.2 ⟨hW₃V₃ hxW₃, hxR₂⟩
  rcases (mem_sup_zpowers_iff_of h.t_mul_t (h.t_mem_normalizer_yamadaW₂ d hK hD).1).1 hxV₂ with
    h1 | ⟨a, ha, rfl⟩
  · exact h1
  · exfalso
    refine htW₃ ?_
    have := mul_mem (inv_mem (hW₂W₃ ha)) hxW₃
    rwa [inv_mul_cancel_left] at this

private theorem yamadaW₃_inf_centralizer (hW : CFSG.Walter.WalterOrderForm) (h : Setup G L f t)
    (d : G2Data L K) (hK : Nat.card K = 2 ^ f) (hQ : h.QFacts d) :
    yamadaW₃ d t ⊓ centralizer ({t} : Set G) = d.W := by
  have hD := hQ.doubling
  obtain ⟨hW₃V₃, -, -, hW₂W₃, -, -, -⟩ := h.yamadaW₃_facts hW d hK hD
  obtain ⟨-, hV₃E₃, -, -, -, -, -, -, -⟩ := h.yamadaV₃_facts hW d hK hD
  refine le_antisymm (fun x hx => ?_) (le_inf ((le_sup_left : d.W ≤ yamadaW₂ d t).trans hW₂W₃)
    fun w hw => h.L_le_centralizer (d.image_le _ hw))
  obtain ⟨hxW₃, hxC⟩ := Subgroup.mem_inf.1 hx
  have hxR₃ : x ∈ yamadaR₃ d t := (hV₃E₃.trans (inf_le_left.trans le_sup_left)) (hW₃V₃ hxW₃)
  have hxR₂ := h.yamadaR₃_inf_centralizer_le hW d hK hQ hxR₃ hxC
  have h1 : x ∈ yamadaW₃ d t ⊓ yamadaR₂ d t := ⟨hxW₃, hxR₂⟩
  rw [h.yamadaW₃_inf_yamadaR₂ hW d hK hQ] at h1
  have h2 : x ∈ yamadaW₂ d t ⊓ centralizer ({t} : Set G) := ⟨h1, hxC⟩
  rwa [h.yamadaW₂_inf_centralizer d hK hD] at h2

private theorem mem_M_or_mem_D_of_mul_self_mem_W (d : G2Data L K) {s : G} (hs : s ∈ d.S)
    (hss : s * s ∈ d.W) : s ∈ d.M ∨ s ∈ d.D := by
  have hSW : d.S ≤ normalizer (d.W : Set G) := d.S_le_normalizers.2.2.2.1
  have hsN : zpowers s ≤ normalizer (d.W : Set G) := (zpowers_le).2 (hSW hs)
  have hWS : d.W ≤ d.S := d.inclusions.2.2.2.2.1.trans (d.inclusions.2.2.2.2.2.1.trans
    d.inclusions.2.2.2.2.2.2.2.1)
  have hP : d.W ≤ zpowers s ⊔ d.W ∧ zpowers s ⊔ d.W ≤ d.S ∧
      ElemModulo d.W (zpowers s ⊔ d.W) := by
    refine ⟨le_sup_right, sup_le ((zpowers_le).2 hs) hWS, ?_⟩
    have := mul_self_mem_of_sup (A := zpowers s) (B := d.W) (N := d.W) hsN
      (sup_le hsN Subgroup.le_normalizer)
      (fun a ha => by
        obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 ha
        have e : s ^ k * s ^ k = (s * s) ^ k := by
          rw [← zpow_add, ← two_mul, zpow_mul, zpow_two]
        rw [e]
        exact zpow_mem hss k)
      (fun b hb => mul_mem hb hb)
      (fun a ha b hb => mul_mem ((mem_normalizer_iff.1 (hsN ha) b).1 hb) (inv_mem hb))
    exact fun x hx y hy => ⟨this.1 x hx, this.2 x hx y hy⟩
  obtain ⟨E, hE1, hEmax⟩ := (Set.toFinite {E' : Subgroup G | d.W ≤ E' ∧ E' ≤ d.S ∧
    ElemModulo d.W E'}).exists_le_maximal hP
  rcases ((d.yamada_3_12_2_quotients E).2.1).1 hEmax with rfl | rfl
  · exact Or.inl (hE1 (mem_sup_left (mem_zpowers s)))
  · exact Or.inr (hE1 (mem_sup_left (mem_zpowers s)))

private theorem yamadaM_le_yamadaL₃ (hW : CFSG.Walter.WalterOrderForm) (h : Setup G L f t)
    (d : G2Data L K) (hK : Nat.card K = 2 ^ f) (hQ : h.QFacts d) : d.M ≤ yamadaL₃ d t := by
  have hD := hQ.doubling
  have hM₃L₃ : yamadaM₃ d t ≤ yamadaL₃ d t := by
    rw [← (h.yamada_5_30_2 hW d hK hD).2.2.2.1.1]
    exact le_sup_left
  exact ((le_sup_left : d.M ≤ yamadaM₂ d t).trans
    (le_sup_right : yamadaM₂ d t ≤ yamadaM₃ d t)).trans hM₃L₃

private theorem yamadaD_le_yamadaC₃ (hW : CFSG.Walter.WalterOrderForm) (h : Setup G L f t)
    (d : G2Data L K) (hK : Nat.card K = 2 ^ f) (hQ : h.QFacts d) : d.D ≤ yamadaC₃ d t := by
  have hD := hQ.doubling
  have hC₁Cs : yamadaC₁ d t ≤ yamadaCstar d t := by
    rw [h.yamadaCstar_eq d hK hD]
    exact h.yamadaC₁_le_yamadaV d hK hD
  exact fun x hx => ⟨(le_sup_right : d.S ≤ yamadaR₃ d t) (d.inclusions.2.2.2.2.2.2.2.1 hx),
    hC₁Cs ((le_sup_left.trans (h.tD_le_yamadaC₁ d hK)) hx)⟩

theorem mem_or_mem_of_mul_self_mem_yamadaW₂ (hW : CFSG.Walter.WalterOrderForm)
    (h : Setup G L f t) (d : G2Data L K) (hK : Nat.card K = 2 ^ f) (hQ : h.QFacts d) {x : G}
    (hx : x ∈ yamadaR₃ d t) (hxx : x * x ∈ yamadaW₂ d t) :
    x ∈ yamadaL₃ d t ∨ x ∈ yamadaC₃ d t := by
  have hD := hQ.doubling
  obtain ⟨-, -, -, -, -, -, -, hDS, -, -⟩ := d.inclusions
  obtain ⟨hW₃V₃, -, -, hW₂W₃, -, hsup, -⟩ := h.yamadaW₃_facts hW d hK hD
  obtain ⟨-, hV₃E₃, -, -, -, -, -, -, -⟩ := h.yamadaV₃_facts hW d hK hD
  obtain ⟨-, hR₂R₃, -, -, -⟩ := h.yamadaR₃_facts hW d hK hD
  have hRN := h.yamadaR₃_le_normalizer_W₃_V₃ hW d hK hQ
  have hR₂eq := h.yamadaR₂_eq_sup_yamadaY₂ d hK hD
  have hY₂W₃ : yamadaY₂ d t ≤ yamadaW₃ d t :=
    (le_sup_right : yamadaY₂ d t ≤ yamadaW₂ d t).trans hW₂W₃
  have hW₃E₃ : yamadaW₃ d t ≤ yamadaE₃ d t := hW₃V₃.trans hV₃E₃
  have htV₃ : t ∈ yamadaV₃ d t := by
    rw [← hsup]
    exact mem_sup_right (mem_zpowers t)
  have hM₃L₃ : yamadaM₃ d t ≤ yamadaL₃ d t := by
    rw [← (h.yamada_5_30_2 hW d hK hD).2.2.2.1.1]
    exact le_sup_left
  have hML₃ : d.M ≤ yamadaL₃ d t :=
    ((le_sup_left : d.M ≤ yamadaM₂ d t).trans
      (le_sup_right : yamadaM₂ d t ≤ yamadaM₃ d t)).trans hM₃L₃
  have hC₁Cs : yamadaC₁ d t ≤ yamadaCstar d t := by
    rw [h.yamadaCstar_eq d hK hD]
    exact h.yamadaC₁_le_yamadaV d hK hD
  have hDC₃ : d.D ≤ yamadaC₃ d t := fun x hx =>
    ⟨(le_sup_right : d.S ≤ yamadaR₃ d t) (hDS hx),
      hC₁Cs ((le_sup_left.trans (h.tD_le_yamadaC₁ d hK)) hx)⟩
  have hx' : x ∈ (yamadaR₃ d t : Set G) := hx
  rw [h.yamadaR₃_eq_mul hW d hK hQ] at hx'
  obtain ⟨w₀, hw₀, r, hr, rfl⟩ := Set.mem_mul.1 hx'
  rw [hR₂eq.1] at hr
  obtain ⟨ρ, hρ, y, hy, rfl⟩ := Common.exists_mul_of_le_normalizer' hR₂eq.2 r hr
  have htS : zpowers t ≤ normalizer (d.S : Set G) := (zpowers_le).2
    (Subgroup.centralizer_le_normalizer _ (mem_centralizer_iff.2 fun s hs =>
      mem_centralizer_singleton_iff.1 (h.S_le_centralizer d hs)))
  obtain ⟨s, hs, τ, hτ, rfl⟩ := Common.exists_mul_of_le_normalizer htS ρ hρ
  have hτs : τ * s = s * τ := (commute_of_mem_zpowers hτ (h.S_le_centralizer d hs)).symm
  have hττ : τ * τ = 1 := by
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 hτ
    rcases h.zpow_eq_one_or_eq k with hk | hk <;> rw [hk]
    · rw [mul_one]
    · exact h.t_mul_t
  have hρR₃ : s * τ ∈ yamadaR₃ d t := hR₂R₃ (by rw [hR₂eq.1]; exact mem_sup_left hρ)
  have hρN := (hRN hρR₃).1
  have hρY : s * τ ∈ normalizer (yamadaY₂ d t : Set G) := hR₂eq.2 hρ
  set w' := w₀ * ((s * τ) * y * (s * τ)⁻¹) with hw'
  have hw'W₃ : w' ∈ yamadaW₃ d t :=
    mul_mem hw₀ (hY₂W₃ ((mem_normalizer_iff.1 hρY y).1 hy))
  have hxe : w₀ * (s * τ * y) = w' * (s * τ) := by
    rw [hw']
    group
  rw [hxe] at hxx ⊢
  have hss : s * s ∈ d.W := by
    have hρρ : s * τ * (s * τ) = s * s := by
      calc s * τ * (s * τ) = s * (τ * s) * τ := by group
        _ = s * (s * τ) * τ := by rw [hτs]
        _ = s * s * (τ * τ) := by group
        _ = s * s := by rw [hττ, mul_one]
    have e : w' * (s * τ) * (w' * (s * τ)) =
        (w' * ((s * τ) * w' * (s * τ)⁻¹)) * (s * τ * (s * τ)) := by group
    rw [e, hρρ] at hxx
    have hxxW₃ : (w' * ((s * τ) * w' * (s * τ)⁻¹)) * (s * s) ∈ yamadaW₃ d t := hW₂W₃ hxx
    have hss₃ : s * s ∈ yamadaW₃ d t := by
      have := mul_mem (inv_mem (mul_mem hw'W₃ ((mem_normalizer_iff.1 hρN w').1 hw'W₃))) hxxW₃
      rwa [inv_mul_cancel_left] at this
    have hssC : s * s ∈ centralizer ({t} : Set G) :=
      mul_mem (h.S_le_centralizer d hs) (h.S_le_centralizer d hs)
    rw [← h.yamadaW₃_inf_centralizer hW d hK hQ]
    exact ⟨hss₃, hssC⟩
  have hτE₃ : τ ∈ yamadaE₃ d t := ((zpowers_le).2 (hV₃E₃ htV₃)) hτ
  have hE₃L₃ : yamadaE₃ d t ≤ yamadaL₃ d t := inf_le_left
  have hE₃C₃ : yamadaE₃ d t ≤ yamadaC₃ d t := inf_le_right
  rcases mem_M_or_mem_D_of_mul_self_mem_W d hs hss with hsM | hsD
  · left
    exact mul_mem (hE₃L₃ (hW₃E₃ hw'W₃)) (mul_mem (hML₃ hsM) (hE₃L₃ hτE₃))
  · right
    exact mul_mem (hE₃C₃ (hW₃E₃ hw'W₃)) (mul_mem (hDC₃ hsD) (hE₃C₃ hτE₃))

private theorem closure_sq_yamadaV₃ (hW : CFSG.Walter.WalterOrderForm) (h : Setup G L f t)
    (d : G2Data L K) (hK : Nat.card K = 2 ^ f) (hQ : h.QFacts d) :
    closure {z | ∃ g ∈ yamadaV₃ d t, z = g ^ 2} = d.W := by
  have hD := hQ.doubling
  obtain ⟨hW₃V₃, hV₃N, -, -, -, hsup, -⟩ := h.yamadaW₃_facts hW d hK hD
  obtain ⟨hel, hcard', -, -⟩ := h.yamada_5_33_3_uniform hW d hK hQ.doubling
  have hcomm : ∀ a ∈ yamadaW₃ d t, ∀ b ∈ yamadaW₃ d t, a * b = b * a := fun a ha b hb =>
    mul_comm_of_isElementaryAbelian hel ha hb
  have hsq1 : ∀ a ∈ yamadaW₃ d t, a * a = 1 := fun a ha =>
    mul_self_eq_one_of_isElementaryAbelian hel ha
  have htV₃ : t ∈ yamadaV₃ d t := by
    rw [← hsup]
    exact mem_sup_right (mem_zpowers t)
  have ht : t ∈ normalizer (yamadaW₃ d t : Set G) := hV₃N htV₃
  have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_right h.t_mul_t
  obtain ⟨B, -, hB1, hB2, hBcard⟩ := exists_subgroup_card_commutator hcomm hsq1 h.t_mul_t ht
  rw [h.yamadaW₃_inf_centralizer hW d hK hQ, hcard', d.cards.2.2.2.1] at hBcard
  have hq : 0 < Nat.card K := Nat.card_pos
  have hq3 : 0 < Nat.card K ^ 3 := by positivity
  have hBc : Nat.card B = Nat.card d.W := by
    rw [d.cards.2.2.2.1]
    refine Nat.eq_of_mul_eq_mul_right hq3 ?_
    rw [hBcard]
    ring
  have hBW : B ≤ d.W := by
    intro b hb
    obtain ⟨a, ha, rfl⟩ := hB2 b hb
    have hataW₃ : t * a * t⁻¹ ∈ yamadaW₃ d t := (mem_normalizer_iff.1 ht a).1 ha
    have hb1 : (t * a) * (t * a) = (t * a * t⁻¹) * a := by
      rw [htinv]
      group
    have hbW₃ : (t * a) * (t * a) ∈ yamadaW₃ d t := by
      rw [hb1]
      exact mul_mem hataW₃ ha
    have hbC : (t * a) * (t * a) ∈ centralizer ({t} : Set G) := by
      refine mem_centralizer_singleton_iff.2 ?_
      have hc := hcomm _ hataW₃ a ha
      rw [htinv] at hc
      have htt := h.t_mul_t
      have e1 : (t * a) * (t * a) * t = a * t * a := by
        calc (t * a) * (t * a) * t = (t * a * t * a) * t := by group
          _ = (a * (t * a * t)) * t := by rw [hc]
          _ = a * t * a * (t * t) := by group
          _ = a * t * a := by rw [htt, mul_one]
      have e2 : t * ((t * a) * (t * a)) = a * t * a := by
        calc t * ((t * a) * (t * a)) = (t * t) * a * t * a := by group
          _ = a * t * a := by rw [htt, one_mul]
      rw [e1, e2]
    have : (t * a) * (t * a) ∈ yamadaW₃ d t ⊓ centralizer ({t} : Set G) := ⟨hbW₃, hbC⟩
    rwa [h.yamadaW₃_inf_centralizer hW d hK hQ] at this
  have hBeq : B = d.W := Subgroup.eq_of_le_of_card_ge hBW hBc.ge
  refine le_antisymm ((closure_le _).2 fun z ⟨g, hg, e⟩ => ?_) ?_
  · rw [e, sq]
    rw [← hsup] at hg
    rcases (mem_sup_zpowers_iff_of h.t_mul_t ht).1 hg with h1 | ⟨a, ha, rfl⟩
    · rw [hsq1 g h1]
      exact one_mem _
    · have hataW₃ : t * a * t⁻¹ ∈ yamadaW₃ d t := (mem_normalizer_iff.1 ht a).1 ha
      have htt := h.t_mul_t
      have e0 : t * (t * a * t⁻¹) = a * t := by
        rw [htinv]
        calc t * (t * a * t) = (t * t) * a * t := by group
          _ = a * t := by rw [htt, one_mul]
      have := hBW (hB1 _ hataW₃)
      rwa [e0] at this
  · rw [← hBeq]
    intro b hb
    obtain ⟨a, ha, rfl⟩ := hB2 b hb
    exact subset_closure ⟨t * a, mul_mem htV₃ (hW₃V₃ ha), (sq _).symm⟩

private theorem yamadaW₃_inf_yamadaC₁_le (hW : CFSG.Walter.WalterOrderForm) (h : Setup G L f t)
    (d : G2Data L K) (hK : Nat.card K = 2 ^ f) (hQ : h.QFacts d) :
    yamadaW₃ d t ⊓ yamadaC₁ d t ≤ yamadaW₁ d t := by
  have hD := hQ.doubling
  obtain ⟨-, -, hYW, -, hWF, hFD, -, -, -, -⟩ := d.inclusions
  intro x hx
  obtain ⟨hxW₃, hxC₁⟩ := Subgroup.mem_inf.1 hx
  have hxR₂ : x ∈ yamadaR₂ d t := h.yamadaC₁_le_yamadaR₂ d hK hxC₁
  have h1 : x ∈ yamadaW₃ d t ⊓ yamadaR₂ d t := ⟨hxW₃, hxR₂⟩
  rw [h.yamadaW₃_inf_yamadaR₂ hW d hK hQ] at h1
  obtain ⟨w, hw, y, hy, rfl⟩ := Common.exists_mul_of_le_normalizer
    (h.yamadaY₂_le_normalizer_W d hK hD) _ h1
  have hwC₁ : w ∈ yamadaC₁ d t :=
    (le_sup_left.trans (h.tD_le_yamadaC₁ d hK)) ((hWF.trans hFD) hw)
  have hyC₁ : y ∈ yamadaC₁ d t := by
    have := mul_mem (inv_mem hwC₁) hxC₁
    rwa [inv_mul_cancel_left] at this
  have hyY₁ : y ∈ yamadaY₁ d t := by
    rw [← h.yamadaY₂_inf_yamadaR₁ d hK hD]
    exact ⟨hy, (le_sup_left : yamadaC₁ d t ≤ yamadaR₁ d t) hyC₁⟩
  have hY₁W₁ : yamadaY₁ d t ≤ yamadaW₁ d t := sup_le (hYW.trans le_sup_left) le_sup_right
  exact mul_mem (mem_sup_left hw) (hY₁W₁ hyY₁)

private theorem mul_self_mem_yamadaC₁_of_mem_yamadaC₃ (hW : CFSG.Walter.WalterOrderForm)
    (h : Setup G L f t) (d : G2Data L K) (hK : Nat.card K = 2 ^ f) (hQ : h.QFacts d) {c : G}
    (hc : c ∈ yamadaC₃ d t) : c * c ∈ yamadaC₁ d t := by
  have hD := hQ.doubling
  have hCV := h.yamadaCstar_eq d hK hD
  have hR₃ := h.yamada_5_23_4 hW d hK hD
  obtain ⟨hcR₃, hcC⟩ := Subgroup.mem_inf.1 hc
  have hcV : c ∈ h.yamadaV d hK hD := hCV ▸ hcC
  have hcN := ((h.mem_yamadaV d hK hD).1 hcV).1
  have hκ : t * c * t * c⁻¹ ∈ yamadaW₁ d t :=
    ((h.mem_yamadaR₃star_iff d hK hD).1 (hR₃ ▸ hcR₃)).2
  have h1 := h.crossed_mul_mem d hK hD hcV hcN
  rw [h.yamadaW₁_mul_self hW d hK hD hκ, inv_one, one_mul] at h1
  exact h.mem_yamadaC₁_of_crossed_mem d hK hD (mul_mem hcV hcV) h1

private theorem closure_sq_yamadaC₃ (hW : CFSG.Walter.WalterOrderForm) (h : Setup G L f t)
    (d : G2Data L K) (hK : Nat.card K = 2 ^ f) (hQ : h.QFacts d) :
    closure {z | ∃ g ∈ yamadaC₃ d t, z = g ^ 2} = yamadaW₁ d t := by
  have hD := hQ.doubling
  obtain ⟨hW₃V₃, -, -, hW₂W₃, -, -, -⟩ := h.yamadaW₃_facts hW d hK hD
  obtain ⟨-, hV₃E₃, -, -, -, -, -, -, -⟩ := h.yamadaV₃_facts hW d hK hD
  obtain ⟨-, hR₂R₃, -, -, hC₂⟩ := h.yamadaR₃_facts hW d hK hD
  have hV₃C₃ : yamadaV₃ d t ≤ yamadaC₃ d t := hV₃E₃.trans inf_le_right
  have hC₂C₃ : yamadaC₂ d t ≤ yamadaC₃ d t := by
    intro x hx
    rw [hC₂] at hx
    exact ⟨hR₂R₃ hx.2, hx.1⟩
  have hY₁W₃ : yamadaY₁ d t ≤ yamadaW₃ d t :=
    (h.yamadaY₁_le_yamadaY₂ d hK hD).trans
      ((le_sup_right : yamadaY₂ d t ≤ yamadaW₂ d t).trans hW₂W₃)
  have hRN := h.yamadaR₃_le_normalizer_W₃_V₃ hW d hK hQ
  refine le_antisymm ((closure_le _).2 fun z ⟨c, hc, e⟩ => ?_) (sup_le ?_ ?_)
  · rw [e, sq]
    have hcC₁ := h.mul_self_mem_yamadaC₁_of_mem_yamadaC₃ hW d hK hQ hc
    obtain ⟨hcR₃, hcC⟩ := Subgroup.mem_inf.1 hc
    have hcR₃' : c ∈ (yamadaR₃ d t : Set G) := hcR₃
    rw [h.yamadaR₃_eq_mul hW d hK hQ] at hcR₃'
    obtain ⟨w, hw, r, hr, rfl⟩ := Set.mem_mul.1 hcR₃'
    have hwC : w ∈ yamadaC₃ d t := hV₃C₃ (hW₃V₃ hw)
    have hrC₂ : r ∈ yamadaC₂ d t := by
      rw [hC₂]
      refine ⟨?_, hr⟩
      have := mul_mem (inv_mem (Subgroup.mem_inf.1 hwC).2) hcC
      rwa [inv_mul_cancel_left] at this
    have hr2 : r ^ 2 ∈ yamadaY₁ d t := by
      have : r ^ 2 ∈ closure {z | ∃ g ∈ yamadaC₂ d t, z = g ^ 2} := subset_closure ⟨r, hrC₂, rfl⟩
      rwa [h.closure_sq_yamadaC₂ d hK hD] at this
    have hrN : r ∈ normalizer (yamadaW₃ d t : Set G) := (hRN (hR₂R₃ hr)).1
    have hc2 : w * r * (w * r) ∈ yamadaW₃ d t := by
      have : w * r * (w * r) = (w * (r * w * r⁻¹)) * (r ^ 2) := by group
      rw [this]
      exact mul_mem (mul_mem hw ((mem_normalizer_iff.1 hrN w).1 hw)) (hY₁W₃ hr2)
    exact h.yamadaW₃_inf_yamadaC₁_le hW d hK hQ ⟨hc2, hcC₁⟩
  · rw [← h.closure_sq_yamadaV₃ hW d hK hQ]
    exact closure_mono fun z ⟨g, hg, e⟩ => ⟨g, hV₃C₃ hg, e⟩
  · intro u hu
    have hY₁ : u ∈ yamadaY₁ d t := (le_sup_right : yamadaU₁ d t ≤ yamadaY₁ d t) hu
    rw [← h.closure_sq_yamadaC₂ d hK hD] at hY₁
    have hmono : closure {z | ∃ g ∈ yamadaC₂ d t, z = g ^ 2} ≤
        closure {z | ∃ g ∈ yamadaC₃ d t, z = g ^ 2} :=
      closure_mono fun z ⟨g, hg, e⟩ => ⟨g, hC₂C₃ hg, e⟩
    exact hmono hY₁

private theorem commutator_mem_yamadaY₁_of_mem_yamadaF₂ (hW : CFSG.Walter.WalterOrderForm)
    (h : Setup G L f t) (d : G2Data L K) (hK : Nat.card K = 2 ^ f) (hQ : h.QFacts d)
    {x g : G} (hx : x ∈ yamadaF₂ d t) (hg : g ∈ yamadaR₃ d t) :
    x * g * x⁻¹ * g⁻¹ ∈ yamadaY₁ d t := by
  obtain ⟨-, h2, h3⟩ := h.yamada_5_35_1 hW d hK hQ
  rw [← h3] at hx
  obtain ⟨x₀, hx₀, rfl⟩ := Subgroup.mem_map.1 hx
  have h4 := Subgroup.mem_upperCentralSeries_succ_iff.1 hx₀ ⟨g, hg⟩
  rw [← h2]
  exact Subgroup.mem_map.2 ⟨_, h4, rfl⟩

private theorem wb_mem_normalizer_yamadaY₂_W₃ (hW : CFSG.Walter.WalterOrderForm) (h : Setup G L f t)
    (d : G2Data L K) (hK : Nat.card K = 2 ^ f) (hQ : h.QFacts d) :
    d.wb ∈ normalizer (yamadaY₂ d t : Set G) ∧ d.wb ∈ normalizer (yamadaW₃ d t : Set G) := by
  have hD := hQ.doubling
  have hwb := d.wb_mem_normalizer
  refine ⟨(h.normalizer_yamadaL₂_le d hK hD).2 (h.wb_mem_normalizer_yamadaL₂ d), ?_⟩
  exact (h.yamada_5_33_3_uniform hW d hK hQ.doubling).2.2.2 ⟨h.L_le_centralizer hwb.1.1, hwb.1.2⟩

private theorem commutator_mem_of_mem_yamadaM₂ (hW : CFSG.Walter.WalterOrderForm)
    (h : Setup G L f t) (d : G2Data L K) (hK : Nat.card K = 2 ^ f) (hQ : h.QFacts d)
    {N : Subgroup G} (hNR : yamadaR₂ d t ≤ normalizer (N : Set G))
    (hNwb : d.wb ∈ normalizer (N : Set G))
    (hF : ∀ x ∈ yamadaF₂ d t, ∀ a ∈ yamadaW₃ d t, a * x * a⁻¹ * x⁻¹ ∈ N)
    {w m : G} (hw : w ∈ yamadaW₃ d t) (hm : m ∈ yamadaM₂ d t) : w * m * w⁻¹ * m⁻¹ ∈ N := by
  have hD := hQ.doubling
  obtain ⟨-, -, -, hXF, hWF, hFD, -, hDS, -, -⟩ := d.inclusions
  obtain ⟨-, hwbW₃⟩ := h.wb_mem_normalizer_yamadaY₂_W₃ hW d hK hQ
  have hF₂R₂ : yamadaF₂ d t ≤ yamadaR₂ d t :=
    sup_le (((hFD.trans hDS).trans (le_sup_right : d.S ≤ yamadaR₂ d t)))
      (h.yamadaY₂_le_yamadaR₂ d hK hD)
  have hM₂ : yamadaM₂ d t ≤ yamadaF₂ d t ⊔ (yamadaF₂ d t).map (MulAut.conj d.wb).toMonoidHom := by
    have hXF₂ : d.X ≤ yamadaF₂ d t := hXF.trans le_sup_left
    have hWF₂ : d.W ≤ yamadaF₂ d t := hWF.trans le_sup_left
    refine sup_le ?_ (le_sup_of_le_left (le_sup_right : yamadaY₂ d t ≤ yamadaF₂ d t))
    refine d.M_le_sup_conj.trans (sup_le (sup_le ?_ ?_) ?_)
    · exact hWF₂.trans le_sup_left
    · exact hXF₂.trans le_sup_left
    · exact (Subgroup.map_mono hXF₂).trans le_sup_right
  have hP : yamadaM₂ d t ≤ commNormalizer (yamadaW₃ d t) N := by
    refine hM₂.trans (sup_le ?_ ?_)
    · intro x hx
      exact ⟨hNR (hF₂R₂ hx), hF x hx⟩
    · rintro _ ⟨x, hx, rfl⟩
      have hxe : (MulAut.conj d.wb).toMonoidHom x = d.wb * x * d.wb⁻¹ := rfl
      rw [hxe]
      refine ⟨mul_mem (mul_mem hNwb (hNR (hF₂R₂ hx))) (inv_mem hNwb), fun a ha => ?_⟩
      have ha' : d.wb⁻¹ * a * d.wb ∈ yamadaW₃ d t := by
        have := (mem_normalizer_iff.1 (inv_mem hwbW₃) a).1 ha
        rwa [inv_inv] at this
      have e : a * (d.wb * x * d.wb⁻¹) * a⁻¹ * (d.wb * x * d.wb⁻¹)⁻¹ =
          d.wb * ((d.wb⁻¹ * a * d.wb) * x * (d.wb⁻¹ * a * d.wb)⁻¹ * x⁻¹) * d.wb⁻¹ := by group
      rw [e]
      exact (mem_normalizer_iff.1 hNwb _).1 (hF x hx _ ha')
  exact (hP hm).2 w hw

private theorem commutator_mem_yamadaY₂_of_mem_yamadaM₂ (hW : CFSG.Walter.WalterOrderForm)
    (h : Setup G L f t) (d : G2Data L K) (hK : Nat.card K = 2 ^ f) (hQ : h.QFacts d)
    {w m : G} (hw : w ∈ yamadaW₃ d t) (hm : m ∈ yamadaM₂ d t) :
    w * m * w⁻¹ * m⁻¹ ∈ yamadaY₂ d t := by
  have hD := hQ.doubling
  obtain ⟨hwbY₂, -⟩ := h.wb_mem_normalizer_yamadaY₂_W₃ hW d hK hQ
  refine h.commutator_mem_of_mem_yamadaM₂ hW d hK hQ
    (fun x hx => h.yamadaR₂_le_normalizer_yamadaY₂ d hK hD hx) hwbY₂ ?_ hw hm
  intro x hx a ha
  have := h.commutator_mem_yamadaY₁_of_mem_yamadaF₂ hW d hK hQ hx
    (h.yamadaW₃_le_yamadaR₃ hW d hK hD ha)
  have e : a * x * a⁻¹ * x⁻¹ = (x * a * x⁻¹ * a⁻¹)⁻¹ := by group
  rw [e]
  exact inv_mem ((h.yamadaY₁_le_yamadaY₂ d hK hD) this)

private theorem closure_sq_yamadaM₃ (hW : CFSG.Walter.WalterOrderForm) (h : Setup G L f t)
    (d : G2Data L K) (hK : Nat.card K = 2 ^ f) (hQ : h.QFacts d) :
    closure {z | ∃ g ∈ yamadaM₃ d t, z = g ^ 2} = yamadaY₂ d t := by
  have hD := hQ.doubling
  have hK4 : 4 ≤ Nat.card K := hQ.four_le
  obtain ⟨hUY, hYX, -, hXF, -, hFD, hFM, hDS, -, -⟩ := d.inclusions
  obtain ⟨hel, hcard', -, -⟩ := h.yamada_5_33_3_uniform hW d hK hQ.doubling
  have hwb := d.wb_mem_normalizer
  have hM₃mul : (yamadaM₃ d t : Set G) = (yamadaW₃ d t : Set G) * (yamadaM₂ d t : Set G) :=
    (h.yamada_5_30_2 hW d hK hD).1.2.1
  have hM₂M₃ : yamadaM₂ d t ≤ yamadaM₃ d t := le_sup_right
  have hM₃ : d.M ≤ yamadaM₃ d t := (le_sup_left : d.M ≤ yamadaM₂ d t).trans hM₂M₃
  have hmm : ∀ m ∈ yamadaM₂ d t, m * m ∈ d.Y := fun m hm =>
    h.mul_self_mem_Y_of_mem_yamadaL₂ d hK hD (h.yamadaM₂_le_yamadaL₂ d hK hD hm)
  have hsq : ∀ w ∈ yamadaW₃ d t, ∀ m : G, (w * m) * (w * m) = (w * m * w⁻¹ * m⁻¹) * (m * m) :=
    fun w hw m => sq_mul_eq_comm_mul_sq (mul_self_eq_one_of_isElementaryAbelian hel hw)
  set Q := closure {z | ∃ g ∈ yamadaM₃ d t, z = g ^ 2} with hQdef
  have hQY₂ : Q ≤ yamadaY₂ d t := by
    refine (closure_le _).2 fun z ⟨g, hg, e⟩ => ?_
    rw [e, sq]
    have hg' : g ∈ (yamadaM₃ d t : Set G) := hg
    rw [hM₃mul] at hg'
    obtain ⟨w, hw, m, hm, rfl⟩ := Set.mem_mul.1 hg'
    rw [hsq w hw m]
    exact mul_mem (h.commutator_mem_yamadaY₂_of_mem_yamadaM₂ hW d hK hQ hw hm)
      (h.Y_le_yamadaY₂ d hK hD (hmm m hm))
  have hYQ : d.Y ≤ Q := by
    rw [hQdef, ← (d.yamada_3_12_mho hK4).2.1]
    exact closure_mono fun z ⟨g, hg, e⟩ => ⟨g, hM₃ hg, e⟩
  have hQsq : ∀ g ∈ yamadaM₃ d t, g * g ∈ Q := fun g hg => by
    have : g ^ 2 ∈ Q := subset_closure ⟨g, hg, rfl⟩
    rwa [sq] at this
  have hcommQ : ∀ w ∈ yamadaW₃ d t, ∀ m ∈ yamadaM₂ d t, w * m * w⁻¹ * m⁻¹ ∈ Q := by
    intro w hw m hm
    have hwm : w * m ∈ yamadaM₃ d t := by
      have : w * m ∈ (yamadaW₃ d t : Set G) * (yamadaM₂ d t : Set G) := Set.mul_mem_mul hw hm
      rw [← hM₃mul] at this
      exact this
    have h1 := hQsq _ hwm
    rw [hsq w hw m] at h1
    have := mul_mem h1 (inv_mem (hYQ (hmm m hm)))
    rwa [mul_inv_cancel_right] at this
  have hJC := h.J_le_centralizer_inf_normalizer_S d
  have hJY : d.J ≤ normalizer (d.Y : Set G) := fun j hj =>
    (h.centralizer_inf_normalizer_S_le d hK hD).2.2 (hJC hj)
  have hM₃N : L ⊓ normalizer (d.Y : Set G) ≤ normalizer (yamadaM₃ d t : Set G) :=
    h.yamada_5_30_3 hW d hK hD
  have hQN : normalizer (yamadaM₃ d t : Set G) ≤ normalizer (Q : Set G) :=
    normalizer_le_normalizer_closure_sq _
  have hJQ : d.J ≤ normalizer (Q : Set G) := fun j hj =>
    hQN (hM₃N ⟨d.image_le _ hj, hJY hj⟩)
  have hwbQ : d.wb ∈ normalizer (Q : Set G) := hQN (hM₃N ⟨hwb.1.1, hwb.1.2⟩)
  have hV : d.U ≤ Q ⊓ yamadaU₁ d t := le_inf (hUY.trans hYQ) (hD.spec).2.1
  have hJ : d.J₃ ≤ normalizer ((Q ⊓ yamadaU₁ d t : Subgroup G) : Set G) := fun j hj => by
    have hjJ : j ∈ d.J := d.image_mono inf_le_left hj
    exact Common.mem_normalizer_inf (hJQ hjJ) (h.J_le_normalizer_yamadaU₁ d hK hD hjJ)
  rcases h.eq_or_eq_of_le_yamadaU₁ d hK hD hV inf_le_right hJ with hVU | hVU₁
  · exfalso
    have hYU₁ : d.Y ≤ normalizer (yamadaU₁ d t : Set G) :=
      (h.Y_le_yamadaY₂ d hK hD).trans (h.yamadaY₂_le_normalizer_yamadaU₁ d hK hD)
    have hQY₁ : ∀ z ∈ Q, z ∈ yamadaY₁ d t → z ∈ d.Y := by
      intro z hzQ hzY₁
      obtain ⟨y₀, hy₀, u, hu, rfl⟩ := Common.exists_mul_of_le_normalizer' hYU₁ z hzY₁
      have huQ : u ∈ Q := by
        have := mul_mem (inv_mem (hYQ hy₀)) hzQ
        rwa [inv_mul_cancel_left] at this
      have huU : u ∈ d.U := by
        rw [← hVU]
        exact ⟨huQ, hu⟩
      exact mul_mem hy₀ (hUY huU)
    have hF₂M₂ : yamadaF₂ d t ≤ yamadaM₂ d t := sup_le_sup_right hFM _
    have hcommY : ∀ x ∈ yamadaF₂ d t, ∀ a ∈ yamadaW₃ d t, a * x * a⁻¹ * x⁻¹ ∈ d.Y := by
      intro x hx a ha
      have h1 := hcommQ a ha x (hF₂M₂ hx)
      have h2 : a * x * a⁻¹ * x⁻¹ ∈ yamadaY₁ d t := by
        have := h.commutator_mem_yamadaY₁_of_mem_yamadaF₂ hW d hK hQ hx
          (h.yamadaW₃_le_yamadaR₃ hW d hK hD ha)
        rw [show a * x * a⁻¹ * x⁻¹ = (x * a * x⁻¹ * a⁻¹)⁻¹ by group]
        exact inv_mem this
      exact hQY₁ _ h1 h2
    have hWM_Y : ∀ w ∈ yamadaW₃ d t, ∀ m ∈ yamadaM₂ d t, w * m * w⁻¹ * m⁻¹ ∈ d.Y :=
      fun w hw m hm => h.commutator_mem_of_mem_yamadaM₂ hW d hK hQ (N := d.Y)
        (fun x hx => h.yamadaR₂_le_normalizer_Y d hK hx) hwb.1.2 hcommY hw hm
    have hQY : Q ≤ d.Y := by
      refine (closure_le _).2 fun z ⟨g, hg, e⟩ => ?_
      rw [e, sq]
      have hg' : g ∈ (yamadaM₃ d t : Set G) := hg
      rw [hM₃mul] at hg'
      obtain ⟨w, hw, m, hm, rfl⟩ := Set.mem_mul.1 hg'
      rw [hsq w hw m]
      exact mul_mem (hWM_Y w hw m hm) (hmm m hm)
    have hsqY : ∀ g ∈ yamadaM₃ d t, g ^ 2 ∈ d.Y := fun g hg => hQY (subset_closure ⟨g, hg, rfl⟩)
    have hR₃Y : yamadaR₃ d t ≤ normalizer (d.Y : Set G) := fun x hx =>
      (h.normalizer_yamadaV₂_le_normalizer_Y hW d hK hD)
        ((h.yamadaL₃_facts hW d hK hD).2.2.2.1 hx)
    have hM₃R₃ : yamadaM₃ d t ≤ yamadaR₃ d t := by
      have : yamadaM₃ d t ≤ yamadaL₃ d t := by
        rw [← (h.yamada_5_30_2 hW d hK hD).2.2.2.1.1]
        exact le_sup_left
      exact this.trans le_sup_left
    have hYS : d.Y ≤ d.S := hYX.trans (hXF.trans (hFD.trans hDS))
    have hYM₁ : d.Y ≤ yamadaM₁ d t :=
      le_inf (le_inf ((h.Y_le_yamadaY₂ d hK hD).trans (h.yamadaY₂_le_yamadaL₂ d hK hD))
        (hYS.trans (le_sup_right : d.S ≤ yamadaR₁ d t)))
        (hYS.trans (le_sup_left : d.S ≤ yamadaS₁ d t))
    have hM₁M₃ : yamadaM₁ d t ≤ yamadaM₃ d t := (h.yamadaM₁_le_yamadaM₂ d hK hD).trans hM₂M₃
    have hM₃N : yamadaM₃ d t ≤ normalizer (yamadaM₁ d t : Set G) := by
      intro x hx
      apply mem_normalizer_of_conj_mem
      intro m hm
      have hc := commutator_mem_of_sq_mem (H := yamadaM₃ d t) (N := d.Y)
        (fun a ha n hn => (mem_normalizer_iff.1 (hR₃Y (hM₃R₃ ha)) n).1 hn) hsqY hx (hM₁M₃ hm)
      have e : x * m * x⁻¹ = (x * m * x⁻¹ * m⁻¹) * m := by group
      rw [e]
      exact mul_mem (hYM₁ hc) hm
    have hM₃R₅ : yamadaM₃ d t ≤ yamadaR₅ d t := by
      refine hM₃R₃.trans ?_
      rw [(h.yamada_5_27_2 hW d hK hD).1.1]
      exact le_sup_left
    have hM₃R₂ : yamadaM₃ d t ≤ yamadaR₂ d t := by
      rw [← (h.yamada_5_28 hW d hK hD).2.2]
      exact le_inf hM₃R₅ hM₃N
    have hW₃W₂ : yamadaW₃ d t ≤ yamadaW₂ d t := by
      rw [← h.yamadaW₃_inf_yamadaR₂ hW d hK hQ]
      exact le_inf le_rfl ((le_sup_left : yamadaW₃ d t ≤ yamadaM₃ d t).trans hM₃R₂)
    have hc := Subgroup.card_le_of_le hW₃W₂
    rw [hcard', h.card_yamadaW₂ d hK hD] at hc
    exact absurd hc (not_le.2 (Nat.pow_lt_pow_right hQ.one_lt (by norm_num)))
  · have hU₁Q : yamadaU₁ d t ≤ Q := by
      rw [← hVU₁]
      exact inf_le_left
    refine le_antisymm hQY₂ (sup_le hU₁Q ?_)
    rintro _ ⟨u, hu, rfl⟩
    exact (mem_normalizer_iff.1 hwbQ u).1 (hU₁Q hu)

private theorem commutator_t_mem_W_of_mem_yamadaW₃ (hW : CFSG.Walter.WalterOrderForm) (h : Setup G L f t)
    (d : G2Data L K) (hK : Nat.card K = 2 ^ f) (hQ : h.QFacts d) {a : G}
    (ha : a ∈ yamadaW₃ d t) : a * t * a⁻¹ * t⁻¹ ∈ d.W := by
  have hD := hQ.doubling
  obtain ⟨hW₃V₃, -, -, -, -, hsup, -⟩ := h.yamadaW₃_facts hW d hK hD
  obtain ⟨hel, -, -, -⟩ := h.yamada_5_33_3_uniform hW d hK hQ.doubling
  have htV₃ : t ∈ yamadaV₃ d t := by
    rw [← hsup]
    exact mem_sup_right (mem_zpowers t)
  have hainv : a⁻¹ = a := inv_eq_of_mul_eq_one_right (mul_self_eq_one_of_isElementaryAbelian hel ha)
  have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_right h.t_mul_t
  rw [← h.closure_sq_yamadaV₃ hW d hK hQ]
  have : (a * t) ^ 2 ∈ closure {z | ∃ g ∈ yamadaV₃ d t, z = g ^ 2} :=
    subset_closure ⟨a * t, mul_mem (hW₃V₃ ha) htV₃, rfl⟩
  rw [hainv, htinv]
  have e : a * t * a * t = (a * t) * (a * t) := by group
  rw [e]
  rwa [sq] at this

private theorem closure_sq_yamadaL₃ (hW : CFSG.Walter.WalterOrderForm) (h : Setup G L f t)
    (d : G2Data L K) (hK : Nat.card K = 2 ^ f) (hQ : h.QFacts d) :
    closure {z | ∃ g ∈ yamadaL₃ d t, z = g ^ 2} = yamadaW₂ d t := by
  have hD := hQ.doubling
  obtain ⟨hW₃V₃, -, -, -, -, hsup, -⟩ := h.yamadaW₃_facts hW d hK hD
  obtain ⟨hel, -, -, -⟩ := h.yamada_5_33_3_uniform hW d hK hQ.doubling
  obtain ⟨-, hV₃E₃, -, -, -, hV₃L₂, -, -, -⟩ := h.yamadaV₃_facts hW d hK hD
  obtain ⟨-, hR₂R₃, -, -, -⟩ := h.yamadaR₃_facts hW d hK hD
  have hRN := h.yamadaR₃_le_normalizer_W₃_V₃ hW d hK hQ
  have hM₃L₃ : yamadaM₃ d t ≤ yamadaL₃ d t := by
    rw [← (h.yamada_5_30_2 hW d hK hD).2.2.2.1.1]
    exact le_sup_left
  have hV₃L₃ : yamadaV₃ d t ≤ yamadaL₃ d t := hV₃E₃.trans inf_le_left
  have htL₂ : t ∈ yamadaL₂ d t := h.tM_le_yamadaL₂ d hK (mem_sup_right (mem_zpowers t))
  have hL₂R₂ : yamadaL₂ d t ≤ yamadaR₂ d t := le_sup_left
  have hL₂W₃ : yamadaL₂ d t ≤ normalizer (yamadaW₃ d t : Set G) := fun x hx =>
    (hRN (hR₂R₃ (hL₂R₂ hx))).1
  have hL₃eq : yamadaL₃ d t = yamadaW₃ d t ⊔ yamadaL₂ d t := by
    refine le_antisymm ?_ (sup_le (hW₃V₃.trans hV₃L₃) (h.yamadaL₃_facts hW d hK hD).1)
    rw [← hV₃L₂]
    refine sup_le ?_ le_sup_right
    rw [← hsup]
    exact sup_le le_sup_left ((zpowers_le).2 (mem_sup_right htL₂))
  have hW₂N : yamadaR₃ d t ≤ normalizer (yamadaW₂ d t : Set G) := fun x hx =>
    (h.normalizer_yamadaV₂_le hW d hK hD).1 ((h.yamadaL₃_facts hW d hK hD).2.2.2.1 hx)
  have hYW₂ : d.Y ≤ yamadaW₂ d t := (h.Y_le_yamadaY₂ d hK hD).trans le_sup_right
  have hP : yamadaL₂ d t ≤ commNormalizer (yamadaW₃ d t) (yamadaW₂ d t) := by
    rw [h.yamadaL₂_eq_sup d hK hD]
    refine sup_le (fun m hm => ⟨hW₂N (hR₂R₃ (hL₂R₂ (h.yamadaM₂_le_yamadaL₂ d hK hD hm))),
      fun a ha => ?_⟩) ((zpowers_le).2 ⟨hW₂N (hR₂R₃ (hL₂R₂ htL₂)), fun a ha => ?_⟩)
    · exact (le_sup_right : yamadaY₂ d t ≤ yamadaW₂ d t)
        (h.commutator_mem_yamadaY₂_of_mem_yamadaM₂ hW d hK hQ ha hm)
    · exact (le_sup_left : d.W ≤ yamadaW₂ d t)
        (h.commutator_t_mem_W_of_mem_yamadaW₃ hW d hK hQ ha)
  have hV₃L₃' : yamadaV₃ d t ≤ yamadaL₃ d t := hV₃L₃
  refine le_antisymm ((closure_le _).2 fun z ⟨l, hl, e⟩ => ?_) (sup_le ?_ ?_)
  · rw [e, sq]
    rw [hL₃eq] at hl
    obtain ⟨w, hw, l₂, hl₂, rfl⟩ := Common.exists_mul_of_le_normalizer hL₂W₃ l hl
    rw [sq_mul_eq_comm_mul_sq (mul_self_eq_one_of_isElementaryAbelian hel hw)]
    exact mul_mem ((hP hl₂).2 w hw)
      (hYW₂ (h.mul_self_mem_Y_of_mem_yamadaL₂ d hK hD hl₂))
  · rw [← h.closure_sq_yamadaV₃ hW d hK hQ]
    exact closure_mono fun z ⟨g, hg, e⟩ => ⟨g, hV₃L₃ hg, e⟩
  · rw [← h.closure_sq_yamadaM₃ hW d hK hQ]
    exact closure_mono fun z ⟨g, hg, e⟩ => ⟨g, hM₃L₃ hg, e⟩

theorem yamada_5_35_3 (hW : CFSG.Walter.WalterOrderForm) (h : Setup G L f t) (d : G2Data L K)
    (hK : Nat.card K = 2 ^ f) (hQ : h.QFacts d) :
    closure {z | ∃ g ∈ yamadaV₃ d t, z = g ^ 2} = d.W ∧
      closure {z | ∃ g ∈ yamadaC₃ d t, z = g ^ 2} = yamadaW₁ d t ∧
      closure {z | ∃ g ∈ yamadaL₃ d t, z = g ^ 2} = yamadaW₂ d t ∧
      closure {z | ∃ g ∈ yamadaM₃ d t, z = g ^ 2} = yamadaY₂ d t :=
  ⟨h.closure_sq_yamadaV₃ hW d hK hQ, h.closure_sq_yamadaC₃ hW d hK hQ,
    h.closure_sq_yamadaL₃ hW d hK hQ, h.closure_sq_yamadaM₃ hW d hK hQ⟩

private theorem commutator_mem_yamadaW₂_of_mem_yamadaL₃ (hW : CFSG.Walter.WalterOrderForm)
    (h : Setup G L f t) (d : G2Data L K) (hK : Nat.card K = 2 ^ f) (hQ : h.QFacts d) {a b : G}
    (ha : a ∈ yamadaL₃ d t) (hb : b ∈ yamadaL₃ d t) : a * b * a⁻¹ * b⁻¹ ∈ yamadaW₂ d t := by
  have hD := hQ.doubling
  have hW₂N : yamadaR₃ d t ≤ normalizer (yamadaW₂ d t : Set G) := fun x hx =>
    (h.normalizer_yamadaV₂_le hW d hK hD).1 ((h.yamadaL₃_facts hW d hK hD).2.2.2.1 hx)
  refine commutator_mem_of_sq_mem (H := yamadaL₃ d t) (N := yamadaW₂ d t)
    (fun x hx n hn => (mem_normalizer_iff.1
      (hW₂N ((le_sup_left : yamadaL₃ d t ≤ yamadaR₃ d t) hx)) n).1 hn) ?_ ha hb
  intro x hx
  have : x ^ 2 ∈ closure {z | ∃ g ∈ yamadaL₃ d t, z = g ^ 2} := subset_closure ⟨x, hx, rfl⟩
  rwa [h.closure_sq_yamadaL₃ hW d hK hQ] at this

private theorem commutator_mem_yamadaW₂_of_mem_yamadaC₃ (hW : CFSG.Walter.WalterOrderForm)
    (h : Setup G L f t) (d : G2Data L K) (hK : Nat.card K = 2 ^ f) (hQ : h.QFacts d) {a b : G}
    (ha : a ∈ yamadaC₃ d t) (hb : b ∈ yamadaC₃ d t) : a * b * a⁻¹ * b⁻¹ ∈ yamadaW₂ d t := by
  have hD := hQ.doubling
  have hW₂N : yamadaR₃ d t ≤ normalizer (yamadaW₂ d t : Set G) := fun x hx =>
    (h.normalizer_yamadaV₂_le hW d hK hD).1 ((h.yamadaL₃_facts hW d hK hD).2.2.2.1 hx)
  have hW₁W₂ : yamadaW₁ d t ≤ yamadaW₂ d t := sup_le_sup_left (yamadaU₁_le_yamadaY₂ d t) _
  refine commutator_mem_of_sq_mem (H := yamadaC₃ d t) (N := yamadaW₂ d t)
    (fun x hx n hn => (mem_normalizer_iff.1
      (hW₂N ((inf_le_left : yamadaC₃ d t ≤ yamadaR₃ d t) hx)) n).1 hn) ?_ ha hb
  intro x hx
  have : x ^ 2 ∈ closure {z | ∃ g ∈ yamadaC₃ d t, z = g ^ 2} := subset_closure ⟨x, hx, rfl⟩
  rw [h.closure_sq_yamadaC₃ hW d hK hQ] at this
  exact hW₁W₂ this

private theorem commutator_mem_yamadaW₂_of_mem_yamadaE₃ (hW : CFSG.Walter.WalterOrderForm)
    (h : Setup G L f t) (d : G2Data L K) (hK : Nat.card K = 2 ^ f) (hQ : h.QFacts d) {y g : G}
    (hy : y ∈ yamadaE₃ d t) (hg : g ∈ yamadaR₃ d t) : y * g * y⁻¹ * g⁻¹ ∈ yamadaW₂ d t := by
  have hD := hQ.doubling
  obtain ⟨-, -, hR₃L₃, -, -⟩ := h.yamadaL₃_facts hW d hK hD
  have hW₂N : yamadaR₃ d t ≤ normalizer (yamadaW₂ d t : Set G) := fun x hx =>
    (h.normalizer_yamadaV₂_le hW d hK hD).1 ((h.yamadaL₃_facts hW d hK hD).2.2.2.1 hx)
  have hS : d.S ≤ normalizer (yamadaL₃ d t : Set G) :=
    (le_sup_right : d.S ≤ yamadaR₃ d t).trans hR₃L₃
  have hg' : g ∈ yamadaL₃ d t ⊔ d.S := hg
  obtain ⟨l, hl, s, hs, rfl⟩ := Common.exists_mul_of_le_normalizer hS g hg'
  have hs' : s ∈ d.D ⊔ d.M := by
    rw [(d.yamada_defs).2.2.2.2.2.2.2.2]
    exact hs
  obtain ⟨-, -, -, -, -, -, -, hDS, hMS, -⟩ := d.inclusions
  obtain ⟨δ, hδ, m, hm, rfl⟩ := Common.exists_mul_of_le_normalizer
    (hMS.trans d.S_le_normalizers.2.2.2.2.2.1) s hs'
  have hl'L₃ : l * (δ * m * δ⁻¹) ∈ yamadaL₃ d t :=
    mul_mem hl (h.yamadaM_le_yamadaL₃ hW d hK hQ
      ((mem_normalizer_iff.1 (d.S_le_normalizers.2.2.2.2.2.2 (hDS hδ)) m).1 hm))
  have hl'N : l * (δ * m * δ⁻¹) ∈ normalizer (yamadaW₂ d t : Set G) :=
    hW₂N ((le_sup_left : yamadaL₃ d t ≤ yamadaR₃ d t) hl'L₃)
  have hge : l * (δ * m) = (l * (δ * m * δ⁻¹)) * δ := by group
  rw [hge]
  have e : y * ((l * (δ * m * δ⁻¹)) * δ) * y⁻¹ * ((l * (δ * m * δ⁻¹)) * δ)⁻¹ =
      (y * (l * (δ * m * δ⁻¹)) * y⁻¹ * (l * (δ * m * δ⁻¹))⁻¹) *
        ((l * (δ * m * δ⁻¹)) * (y * δ * y⁻¹ * δ⁻¹) * (l * (δ * m * δ⁻¹))⁻¹) := by group
  rw [e]
  exact mul_mem (h.commutator_mem_yamadaW₂_of_mem_yamadaL₃ hW d hK hQ
    ((inf_le_left : yamadaE₃ d t ≤ yamadaL₃ d t) hy) hl'L₃)
    ((mem_normalizer_iff.1 hl'N _).1 (h.commutator_mem_yamadaW₂_of_mem_yamadaC₃ hW d hK hQ
      ((inf_le_right : yamadaE₃ d t ≤ yamadaC₃ d t) hy)
      (h.yamadaD_le_yamadaC₃ hW d hK hQ hδ)))

private theorem mem_yamadaE₂_of_forall_commutator_mem_yamadaX₂ (hW : CFSG.Walter.WalterOrderForm)
    (h : Setup G L f t) (d : G2Data L K) (hK : Nat.card K = 2 ^ f) (hQ : h.QFacts d) {y : G}
    (hy : y ∈ yamadaR₃ d t)
    (hc : ∀ g ∈ yamadaR₃ d t, y * g * y⁻¹ * g⁻¹ ∈ yamadaX₂ d t) : y ∈ yamadaE₂ d t := by
  have hD := hQ.doubling
  have hK4 : 4 ≤ Nat.card K := hQ.four_le
  obtain ⟨-, -, -, hXF, -, hFD, -, hDS, -, -⟩ := d.inclusions
  obtain ⟨-, hR₂R₃, -, -, -⟩ := h.yamadaR₃_facts hW d hK hD
  have hR₂eq := h.yamadaR₂_eq_sup_yamadaY₂ d hK hD
  have hS₂ := h.yamada_5_13_3 d hK hD
  have htR₂ : t ∈ yamadaR₂ d t :=
    (h.yamada_5_6_1 d hK).2.1 (mem_sup_left (h.t_mem_yamadaC₁ d hK))
  have htR₃ : t ∈ yamadaR₃ d t := hR₂R₃ htR₂
  have hX₂R₂ : yamadaX₂ d t ≤ yamadaR₂ d t :=
    sup_le ((hXF.trans (hFD.trans hDS)).trans (le_sup_right : d.S ≤ yamadaR₂ d t))
      (h.yamadaY₂_le_yamadaR₂ d hK hD)
  have hY₂X₂ : yamadaY₂ d t ≤ yamadaX₂ d t := le_sup_right
  have hyX₂ : y ∈ normalizer (yamadaX₂ d t : Set G) := mem_normalizer_of_conj_mem fun x hx => by
    have := mul_mem (hc x (hR₂R₃ (hX₂R₂ hx))) hx
    rwa [show y * x * y⁻¹ * x⁻¹ * x = y * x * y⁻¹ by group] at this
  have hyt : y * t * y⁻¹ ∈ yamadaX₂ d t ⊔ zpowers t := by
    have := mul_mem (mem_sup_left (hc t htR₃)) (mem_sup_right (mem_zpowers t) :
      t ∈ yamadaX₂ d t ⊔ zpowers t)
    rwa [show y * t * y⁻¹ * t⁻¹ * t = y * t * y⁻¹ by group] at this
  have hyU₂ : y ∈ normalizer (yamadaU₂ d t : Set G) :=
    mem_normalizer_sup_zpowers_of_conj_mem hyX₂ hyt
  have hy' : y ∈ ((normalizer (yamadaU₂ d t : Set G) : Subgroup G) : Set G) := hyU₂
  rw [(h.yamada_5_25_1 hW d hK hD).2.2.1] at hy'
  obtain ⟨ρ₀, hρ₀, c, hcN, hyρ⟩ := Set.mem_mul.1 hy'
  have hR₅eq := (h.yamada_5_27_2 hW d hK hD).1
  have hR₃R₅ : yamadaR₃ d t ≤ yamadaR₅ d t := by
    rw [hR₅eq.1]
    exact le_sup_left
  have hR₄R₅ : yamadaR₄ d t ≤ yamadaR₅ d t := by
    rw [hR₅eq.1]
    exact le_sup_right
  have hcR : c ∈ yamadaR d t := by
    refine h.yamadaR₅_inf_le d hK hD ⟨?_, hcN⟩
    have := mul_mem (inv_mem (hR₄R₅ hρ₀)) (hR₃R₅ hy)
    rwa [← hyρ, inv_mul_cancel_left] at this
  have hcR₂ : c ∈ yamadaR₂ d t := (h.yamadaR₂_inf_centralizer d hK).1 hcR
  have hR₂R₄ : yamadaR₂ d t ≤ yamadaR₄ d t := (h.yamadaR₄_facts hW d hK hD).2.1
  have hyR₂ : y ∈ yamadaR₂ d t := by
    rw [← hR₅eq.2.1]
    exact ⟨hy, by rw [← hyρ]; exact mul_mem hρ₀ (hR₂R₄ hcR₂)⟩
  have hyR₂' := hyR₂
  rw [hR₂eq.1] at hyR₂'
  obtain ⟨ρ, hρ, y₂, hy₂, hyeq⟩ := Common.exists_mul_of_le_normalizer' hR₂eq.2 y hyR₂'
  have htS : zpowers t ≤ normalizer (d.S : Set G) := (zpowers_le).2
    (Subgroup.centralizer_le_normalizer _ (mem_centralizer_iff.2 fun s hs =>
      mem_centralizer_singleton_iff.1 (h.S_le_centralizer d hs)))
  obtain ⟨s, hs, τ, hτ, hρeq⟩ := Common.exists_mul_of_le_normalizer htS ρ hρ
  have hρY : ρ ∈ normalizer (yamadaY₂ d t : Set G) := hR₂eq.2 hρ
  have hsF : s ∈ d.F := by
    refine (d.mem_F_iff_commutator_X hK4 hs).2 fun g hg => ?_
    have hg' := hc g ((le_sup_right : d.S ≤ yamadaR₃ d t) hg)
    have hz : y₂ * (g * y₂⁻¹ * g⁻¹) ∈ yamadaY₂ d t :=
      mul_mem hy₂ ((mem_normalizer_iff.1 (hS₂.1 hg) _).1 (inv_mem hy₂))
    have hgτ : g * τ = τ * g := commute_of_mem_zpowers hτ (h.S_le_centralizer d hg)
    have hτg : τ * g * τ⁻¹ = g := by
      rw [← hgτ]
      group
    have e1 : y * g * y⁻¹ * g⁻¹ =
        (ρ * (y₂ * (g * y₂⁻¹ * g⁻¹)) * ρ⁻¹) * (ρ * g * ρ⁻¹ * g⁻¹) := by
      rw [hyeq]
      group
    have e2 : ρ * g * ρ⁻¹ * g⁻¹ = s * g * s⁻¹ * g⁻¹ := by
      rw [hρeq]
      calc s * τ * g * (s * τ)⁻¹ * g⁻¹ = s * (τ * g * τ⁻¹) * s⁻¹ * g⁻¹ := by group
        _ = s * g * s⁻¹ * g⁻¹ := by rw [hτg]
    have hzc : ρ * (y₂ * (g * y₂⁻¹ * g⁻¹)) * ρ⁻¹ ∈ yamadaX₂ d t :=
      hY₂X₂ ((mem_normalizer_iff.1 hρY _).1 hz)
    have hsg : s * g * s⁻¹ * g⁻¹ ∈ yamadaX₂ d t := by
      have h3 := mul_mem (inv_mem hzc) hg'
      rw [e1, e2, inv_mul_cancel_left] at h3
      exact h3
    have hsgS : s * g * s⁻¹ * g⁻¹ ∈ d.S :=
      mul_mem (mul_mem (mul_mem hs hg) (inv_mem hs)) (inv_mem hg)
    have hcen : s * g * s⁻¹ * g⁻¹ ∈ centralizer ({t} : Set G) := h.S_le_centralizer d hsgS
    have h4 : s * g * s⁻¹ * g⁻¹ ∈ yamadaX₂ d t ⊓ centralizer ({t} : Set G) := ⟨hsg, hcen⟩
    rwa [h.yamadaX₂_inf_centralizer d hK hD] at h4
  rw [hyeq, hρeq]
  have hE₂ : d.F ≤ yamadaE₂ d t := (le_sup_left : d.F ≤ yamadaF₂ d t).trans le_sup_left
  exact mul_mem (mul_mem (hE₂ hsF) (mem_sup_right hτ)) (mem_sup_left (mem_sup_right hy₂))

private theorem not_yamadaW₂_le_yamadaW₁ (h : Setup G L f t) (d : G2Data L K) (hK : Nat.card K = 2 ^ f)
    (hQ : h.QFacts d) : ¬ yamadaW₂ d t ≤ yamadaW₁ d t := by
  have hD := hQ.doubling
  obtain ⟨-, -, -, -, hWF, hFD, -, hDS, -, -⟩ := d.inclusions
  have hW₁R₁ : yamadaW₁ d t ≤ yamadaR₁ d t :=
    sup_le ((hWF.trans (hFD.trans hDS)).trans (le_sup_right : d.S ≤ yamadaR₁ d t))
      ((h.yamadaU₁_le_yamadaC₁ d hK hD).trans le_sup_left)
  intro hle
  obtain ⟨y, hy, hyR₁⟩ := h.exists_mem_yamadaY₂_not_mem_yamadaR₁ d hK hD
  exact hyR₁ (hW₁R₁ (hle ((le_sup_right : yamadaY₂ d t ≤ yamadaW₂ d t) hy)))

private theorem not_D_le_yamadaL₃ (hW : CFSG.Walter.WalterOrderForm) (h : Setup G L f t)
    (d : G2Data L K) (hK : Nat.card K = 2 ^ f) (hQ : h.QFacts d) :
    ¬ d.D ≤ yamadaL₃ d t := by
  have hD := hQ.doubling
  obtain ⟨-, -, -, -, hL₃S⟩ := h.yamadaL₃_facts hW d hK hD
  exact fun hle => d.not_D_le_M fun x hx => hL₃S.le ⟨hle hx, d.inclusions.2.2.2.2.2.2.2.1 hx⟩

theorem yamada_5_35_4 (hW : CFSG.Walter.WalterOrderForm) (h : Setup G L f t) (d : G2Data L K)
    (hK : Nat.card K = 2 ^ f) (hQ : h.QFacts d) :
    (yamadaW₂ d t ≤ yamadaR₃ d t ∧ yamadaX₂ d t ≤ yamadaR₃ d t ∧ yamadaE₃ d t ≤ yamadaR₃ d t ∧
      yamadaL₃ d t ≤ yamadaR₃ d t ∧ yamadaC₃ d t ≤ yamadaR₃ d t) ∧
    ((yamadaW₂ d t).subgroupOf (yamadaR₃ d t)).Characteristic ∧
      ((yamadaX₂ d t).subgroupOf (yamadaR₃ d t)).Characteristic ∧
      ((yamadaE₃ d t).subgroupOf (yamadaR₃ d t)).Characteristic ∧
      ((yamadaL₃ d t).subgroupOf (yamadaR₃ d t)).Characteristic ∧
      ((yamadaC₃ d t).subgroupOf (yamadaR₃ d t)).Characteristic := by
  have hD := hQ.doubling
  obtain ⟨-, -, -, hXF, -, hFD, -, hDS, -, -⟩ := d.inclusions
  obtain ⟨-, -, -, hW₂W₃, -, -, -⟩ := h.yamadaW₃_facts hW d hK hD
  obtain ⟨-, hR₂R₃, -, -, -⟩ := h.yamadaR₃_facts hW d hK hD
  have hX₂R₂ : yamadaX₂ d t ≤ yamadaR₂ d t :=
    sup_le ((hXF.trans (hFD.trans hDS)).trans (le_sup_right : d.S ≤ yamadaR₂ d t))
      (h.yamadaY₂_le_yamadaR₂ d hK hD)
  have hW₂R₃ : yamadaW₂ d t ≤ yamadaR₃ d t := hW₂W₃.trans (h.yamadaW₃_le_yamadaR₃ hW d hK hD)
  have hX₂R₃ : yamadaX₂ d t ≤ yamadaR₃ d t := hX₂R₂.trans hR₂R₃
  have hE₃R₃ : yamadaE₃ d t ≤ yamadaR₃ d t := inf_le_left.trans le_sup_left
  have hL₃R₃ : yamadaL₃ d t ≤ yamadaR₃ d t := le_sup_left
  have hC₃R₃ : yamadaC₃ d t ≤ yamadaR₃ d t := inf_le_left
  have hE₃L₃ : yamadaE₃ d t ≤ yamadaL₃ d t := inf_le_left
  have hE₃C₃ : yamadaE₃ d t ≤ yamadaC₃ d t := inf_le_right
  have hF₂ : ∀ φ : yamadaR₃ d t ≃* yamadaR₃ d t, autImage φ (yamadaF₂ d t) = yamadaF₂ d t :=
    fun φ => by
      rw [← (h.yamada_5_35_1 hW d hK hQ).2.2]
      exact autImage_map_subtype φ _
  have hTwo := h.twoElementaryProduct_yamadaF₂ hW d hK hQ
  have hW₂F₂ : yamadaW₂ d t ≤ yamadaF₂ d t := hTwo.le_left
  have hX₂F₂ : yamadaX₂ d t ≤ yamadaF₂ d t := hTwo.le_right
  have hcardWX : Nat.card (yamadaW₂ d t) = Nat.card (yamadaX₂ d t) := by
    rw [h.card_yamadaW₂ d hK hD, h.card_yamadaX₂ d hK hD]
  have hWneX : yamadaW₂ d t ≠ yamadaX₂ d t := by
    intro he
    have h1 := congrArg (fun A => A ⊓ centralizer ({t} : Set G)) he
    simp only [h.yamadaW₂_inf_centralizer d hK hD, h.yamadaX₂_inf_centralizer d hK hD] at h1
    exact d.W_ne_X h1
  have hperm : ∀ φ : yamadaR₃ d t ≃* yamadaR₃ d t,
      (autImage φ (yamadaW₂ d t) = yamadaW₂ d t ∨ autImage φ (yamadaW₂ d t) = yamadaX₂ d t) ∧
      (autImage φ (yamadaX₂ d t) = yamadaW₂ d t ∨ autImage φ (yamadaX₂ d t) = yamadaX₂ d t) := by
    intro φ
    have hW₂el := hTwo.isElementaryAbelian_left
    have hX₂el := hTwo.isElementaryAbelian_right
    have hcW : ∀ x ∈ yamadaW₂ d t, ∀ y ∈ yamadaW₂ d t, x * y = y * x :=
      fun x hx y hy => mul_comm_of_isElementaryAbelian hW₂el hx hy
    have hsW : ∀ x ∈ yamadaW₂ d t, x * x = 1 := fun x hx =>
      mul_self_eq_one_of_isElementaryAbelian hW₂el hx
    have hcX : ∀ x ∈ yamadaX₂ d t, ∀ y ∈ yamadaX₂ d t, x * y = y * x :=
      fun x hx y hy => mul_comm_of_isElementaryAbelian hX₂el hx hy
    have hsX : ∀ x ∈ yamadaX₂ d t, x * x = 1 := fun x hx =>
      mul_self_eq_one_of_isElementaryAbelian hX₂el hx
    have hW' := isElementaryAbelian_autImage φ hcW hsW
    have hX' := isElementaryAbelian_autImage φ hcX hsX
    have hW'F : autImage φ (yamadaW₂ d t) ≤ yamadaF₂ d t :=
      (autImage_mono φ hW₂F₂).trans (hF₂ φ).le
    have hX'F : autImage φ (yamadaX₂ d t) ≤ yamadaF₂ d t :=
      (autImage_mono φ hX₂F₂).trans (hF₂ φ).le
    have c1 : Nat.card (autImage φ (yamadaW₂ d t)) = Nat.card (yamadaW₂ d t) :=
      card_autImage φ hW₂R₃
    have c2 : Nat.card (autImage φ (yamadaX₂ d t)) = Nat.card (yamadaX₂ d t) :=
      card_autImage φ hX₂R₃
    refine ⟨?_, ?_⟩
    · rcases hTwo.le_or_le hW'F with h1 | h1
      · exact Or.inl (Subgroup.eq_of_le_of_card_ge h1 (by rw [c1]))
      · exact Or.inr (Subgroup.eq_of_le_of_card_ge h1 (by rw [c1, hcardWX]))
    · rcases hTwo.le_or_le hX'F with h1 | h1
      · exact Or.inl (Subgroup.eq_of_le_of_card_ge h1 (by rw [c2, ← hcardWX]))
      · exact Or.inr (Subgroup.eq_of_le_of_card_ge h1 (by rw [c2]))
  have hnoswap : ∀ φ : yamadaR₃ d t ≃* yamadaR₃ d t, autImage φ (yamadaW₂ d t) ≠ yamadaX₂ d t := by
    intro φ hφ
    have hE' : autImage φ (yamadaE₃ d t) ≤ yamadaE₂ d t := by
      intro y hy
      have hy' : y ∈ yamadaR₃ d t := autImage_le φ _ hy
      refine h.mem_yamadaE₂_of_forall_commutator_mem_yamadaX₂ hW d hK hQ hy' fun g hg => ?_
      have hg' : g ∈ autImage φ (yamadaR₃ d t) := by
        rw [autImage_self]
        exact hg
      have := autImage_commutator_mem φ (A := yamadaE₃ d t) (B := yamadaR₃ d t)
        (N := yamadaW₂ d t) (fun a ha b hb =>
          h.commutator_mem_yamadaW₂_of_mem_yamadaE₃ hW d hK hQ ha hb) y hy g hg'
      rwa [hφ] at this
    have hc := Subgroup.card_le_of_le hE'
    rw [card_autImage φ hE₃R₃, (h.yamadaE₃_facts hW d hK hD).2.2.2.2.2.1,
      (h.card_yamadaC₂_E₂_V₂ d hK hD).2.1] at hc
    have : Nat.card K ^ 6 < Nat.card K ^ 7 := Nat.pow_lt_pow_right hQ.one_lt (by norm_num)
    omega
  have hW₂fix : ∀ φ : yamadaR₃ d t ≃* yamadaR₃ d t, autImage φ (yamadaW₂ d t) = yamadaW₂ d t :=
    fun φ => (hperm φ).1.resolve_right (hnoswap φ)
  have hX₂fix : ∀ φ : yamadaR₃ d t ≃* yamadaR₃ d t, autImage φ (yamadaX₂ d t) = yamadaX₂ d t := by
    intro φ
    rcases (hperm φ).2 with h1 | h1
    · exact absurd (autImage_injective φ hX₂R₃ hW₂R₃ (h1.trans (hW₂fix φ).symm)).symm hWneX
    · exact h1
  have hW₂W₁ := h.not_yamadaW₂_le_yamadaW₁ d hK hQ
  have hsqL : ∀ l ∈ yamadaL₃ d t, l * l ∈ yamadaW₂ d t := fun l hl => by
    have : l ^ 2 ∈ closure {z | ∃ g ∈ yamadaL₃ d t, z = g ^ 2} := subset_closure ⟨l, hl, rfl⟩
    rw [h.closure_sq_yamadaL₃ hW d hK hQ] at this
    rwa [sq] at this
  have hW₁W₂ : yamadaW₁ d t ≤ yamadaW₂ d t := sup_le_sup_left (yamadaU₁_le_yamadaY₂ d t) _
  have hsqC : ∀ c ∈ yamadaC₃ d t, c * c ∈ yamadaW₂ d t := fun c hc => by
    have : c ^ 2 ∈ closure {z | ∃ g ∈ yamadaC₃ d t, z = g ^ 2} := subset_closure ⟨c, hc, rfl⟩
    rw [h.closure_sq_yamadaC₃ hW d hK hQ] at this
    rw [sq] at this
    exact hW₁W₂ this
  have hsq' : ∀ (φ : yamadaR₃ d t ≃* yamadaR₃ d t) (A : Subgroup G),
      (∀ a ∈ A, a * a ∈ yamadaW₂ d t) → ∀ y ∈ autImage φ A, y * y ∈ yamadaW₂ d t := by
    intro φ A hA y hy
    obtain ⟨a, ha, rfl⟩ := mem_autImage.1 hy
    rw [← hW₂fix φ]
    refine mem_autImage.2 ⟨a * a, hA _ ha, ?_⟩
    simp only [map_mul, Subgroup.coe_mul]
  have hL₃fix : ∀ φ : yamadaR₃ d t ≃* yamadaR₃ d t, autImage φ (yamadaL₃ d t) = yamadaL₃ d t := by
    intro φ
    have hL'R₃ : autImage φ (yamadaL₃ d t) ≤ yamadaR₃ d t := autImage_le φ _
    have hsq1 := hsq' φ _ hsqL
    rcases le_or_le_of_subset_union (fun y hy => h.mem_or_mem_of_mul_self_mem_yamadaW₂ hW d hK hQ
      (hL'R₃ hy) (hsq1 y hy)) with h1 | h1
    · exact Subgroup.eq_of_le_of_card_ge h1 (card_autImage φ hL₃R₃).ge
    · exfalso
      have h2 : autImage φ (closure {z | ∃ g ∈ yamadaL₃ d t, z = g ^ 2}) =
          closure {z | ∃ g ∈ autImage φ (yamadaL₃ d t), z = g ^ 2} := autImage_closure_sq φ hL₃R₃
      rw [h.closure_sq_yamadaL₃ hW d hK hQ, hW₂fix φ] at h2
      have h3 : closure {z | ∃ g ∈ autImage φ (yamadaL₃ d t), z = g ^ 2} ≤
          closure {z | ∃ g ∈ yamadaC₃ d t, z = g ^ 2} :=
        closure_mono fun z ⟨g, hg, e⟩ => ⟨g, h1 hg, e⟩
      rw [h.closure_sq_yamadaC₃ hW d hK hQ, ← h2] at h3
      exact hW₂W₁ h3
  have hDL₃ := h.not_D_le_yamadaL₃ hW d hK hQ
  have hC₃fix : ∀ φ : yamadaR₃ d t ≃* yamadaR₃ d t, autImage φ (yamadaC₃ d t) = yamadaC₃ d t := by
    intro φ
    have hC'R₃ : autImage φ (yamadaC₃ d t) ≤ yamadaR₃ d t := autImage_le φ _
    have hsq1 := hsq' φ _ hsqC
    rcases le_or_le_of_subset_union (fun y hy => h.mem_or_mem_of_mul_self_mem_yamadaW₂ hW d hK hQ
      (hC'R₃ hy) (hsq1 y hy)) with h1 | h1
    · exfalso
      have h2 : yamadaC₃ d t ≤ autImage φ.symm (yamadaL₃ d t) :=
        (autImage_le_iff φ hC₃R₃ hL₃R₃).1 h1
      have h3 : autImage φ.symm (yamadaL₃ d t) = yamadaL₃ d t := hL₃fix φ.symm
      rw [h3] at h2
      exact hDL₃ ((h.yamadaD_le_yamadaC₃ hW d hK hQ).trans h2)
    · exact Subgroup.eq_of_le_of_card_ge h1 (card_autImage φ hC₃R₃).ge
  have hE₃fix : ∀ φ : yamadaR₃ d t ≃* yamadaR₃ d t, autImage φ (yamadaE₃ d t) = yamadaE₃ d t := by
    intro φ
    have hle : autImage φ (yamadaE₃ d t) ≤ yamadaE₃ d t := by
      intro y hy
      obtain ⟨e, he, rfl⟩ := mem_autImage.1 hy
      refine ⟨?_, ?_⟩
      · rw [← hL₃fix φ]
        exact mem_autImage.2 ⟨e, hE₃L₃ he, rfl⟩
      · rw [← hC₃fix φ]
        exact mem_autImage.2 ⟨e, hE₃C₃ he, rfl⟩
    exact Subgroup.eq_of_le_of_card_ge hle (card_autImage φ hE₃R₃).ge
  exact ⟨⟨hW₂R₃, hX₂R₃, hE₃R₃, hL₃R₃, hC₃R₃⟩, characteristic_of_autImage hW₂fix,
    characteristic_of_autImage hX₂fix, characteristic_of_autImage hE₃fix,
    characteristic_of_autImage hL₃fix, characteristic_of_autImage hC₃fix⟩

end Local

end Setup

end CFSG.LocalAnalysis.EvenBN.G2
