module

public import CFSG.LocalAnalysis.EvenBN.G2.LocalYThree

public section

namespace CFSG.LocalAnalysis.EvenBN.G2

open Subgroup CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.ComponentClassification.UnbalancedCatalog CFSG.ComponentClassification.RankTwoExceptional
open CFSG.LocalAnalysis.EvenBN.Common (CosetData)
open scoped commutatorElement Pointwise

section Defs

variable
  {G : Type*} [Group G] {L : Subgroup G} {K : Type} [Field K] [CharP K 2]

@[expose] noncomputable def yamadaU₁ (d : G2Data L K) (t : G) : Subgroup G :=
  if 8 ≤ Nat.card K then yamadaD₁ d t ⊓ centralizer (d.J₁ : Set G)
  else (yamadaD₁ d t ⊓ centralizer (d.J₁ : Set G)) ⊓
    centralizer ((yamadaD₁ d t ⊓ centralizer (d.J₁ : Set G) : Subgroup G) : Set G)

@[expose] noncomputable def yamadaY₁ (d : G2Data L K) (t : G) : Subgroup G :=
  d.Y ⊔ yamadaU₁ d t

@[expose] noncomputable def yamadaW₁ (d : G2Data L K) (t : G) : Subgroup G :=
  d.W ⊔ yamadaU₁ d t

@[expose] noncomputable def yamadaX₁ (d : G2Data L K) (t : G) : Subgroup G :=
  d.X ⊔ yamadaU₁ d t

theorem yamadaU₁_eq (d : G2Data L K) (t : G) (h8 : 8 ≤ Nat.card K) :
    yamadaU₁ d t = yamadaD₁ d t ⊓ centralizer (d.J₁ : Set G) :=
  ite_eq_left h8

end Defs

theorem eq_zero_of_alternating_equivariant {K : Type*} [Field K] [Finite K] [CharP K 2]
    (β : K → K → K) (h1 : ∀ z z' w, β (z + z') w = β z w + β z' w)
    (h2 : ∀ z w w', β z (w + w') = β z w + β z w') (h3 : ∀ z, β z z = 0)
    (h4 : ∀ a z w, a ≠ 0 → β (a * z) (a * w) = a * β z w) (z w : K) : β z w = 0 := by
  have hsymm : ∀ z w, β w z = β z w := fun z w => by
    have h := h3 (z + w)
    rw [h1, h2, h2, h3, h3, zero_add, add_zero] at h
    exact (CharTwo.add_eq_zero.1 h).symm
  have h0 : ∀ w, β 0 w = 0 := fun w => by
    have h := h1 0 0 w
    rw [add_zero] at h
    exact left_eq_add.1 h
  set f : K → K := fun w => β 1 w with hfdef
  have hf_add : ∀ w w', f (w + w') = f w + f w' := fun w w' => h2 1 w w'
  have hf0 : f 0 = 0 := by
    change β 1 0 = 0
    rw [hsymm]
    exact h0 1
  have hf1 : f 1 = 0 := h3 1
  have hfinv : ∀ z, z ≠ 0 → f z⁻¹ = z⁻¹ * f z := fun z hz => by
    change β 1 z⁻¹ = z⁻¹ * β 1 z
    calc β 1 z⁻¹ = β (z⁻¹ * z) (z⁻¹ * 1) := by rw [inv_mul_cancel₀ hz, mul_one]
      _ = z⁻¹ * β z 1 := h4 _ _ _ (inv_ne_zero hz)
      _ = z⁻¹ * β 1 z := by rw [hsymm]
  have hsq : ∀ x, f (x * x) = 0 := by
    intro x
    by_cases hx0 : x = 0
    · rw [hx0, mul_zero, hf0]
    by_cases hx1 : x = 1
    · rw [hx1, mul_one, hf1]
    have hx1' : x + 1 ≠ 0 := fun h => hx1 (CharTwo.add_eq_zero.1 h)
    have hxx : x * x + x ≠ 0 := by
      rw [show x * x + x = x * (x + 1) by ring]
      exact mul_ne_zero hx0 hx1'
    have hinv : x⁻¹ + (x + 1)⁻¹ = (x * x + x)⁻¹ := by
      rw [inv_add_inv hx0 hx1', show x + (x + 1) = (1 : K) by
        rw [← add_assoc, CharTwo.add_self_eq_zero, zero_add],
        show x * (x + 1) = x * x + x by ring, one_div]
    have e := hf_add x⁻¹ (x + 1)⁻¹
    rw [hinv, hfinv _ hxx, hfinv _ hx0, hfinv _ hx1', hf_add x 1, hf1, add_zero, ← add_mul,
      hinv] at e
    have e' : f (x * x + x) = f x := mul_left_cancel₀ (inv_ne_zero hxx) e
    rw [hf_add, add_eq_right] at e'
    exact e'
  have hfz : ∀ w, f w = 0 := fun w => by
    obtain ⟨x, rfl⟩ := isSquare_of_charTwo' w
    exact hsq x
  by_cases hz : z = 0
  · rw [hz, h0]
  · have := h4 z 1 (z⁻¹ * w) hz
    rw [mul_one, ← mul_assoc, mul_inv_cancel₀ hz, one_mul] at this
    rw [this]
    have := hfz (z⁻¹ * w)
    simp only [hfdef] at this
    rw [this, mul_zero]

namespace G2Data

variable {G : Type*} [Group G] {L : Subgroup G} {K : Type} [Field K] (d : G2Data L K)

section Light


theorem J₁_le_centralizer_U : d.J₁ ≤ centralizer (d.U : Set G) := by
  have h := d.image_inf_centralizer (torusGroup .G2 K) (Model.U_le_adjointGroup K)
  intro x hx
  have hx' : x ∈ d.image (torusGroup .G2 K ⊓ centralizer (Model.U K : Set (ModGL .G2 K))) := hx
  rw [h] at hx'
  exact hx'.2

theorem card_J₁ [Finite K] : Nat.card d.J₁ = Nat.card K - 1 := by
  rw [G2Data.J₁, d.card_image (Model.torusFix_le_adjointGroup K g2c)]
  exact (Model.yamada_3_9_1 (K := K) 0).2

theorem J₁_comm_J₃ {x y : G} (hx : x ∈ d.J₁) (hy : y ∈ d.J₃) : x * y = y * x := by
  obtain ⟨a, ha, rfl⟩ := d.mem_image.1 hx
  obtain ⟨b, hb, rfl⟩ := d.mem_image.1 hy
  rw [← map_mul, ← map_mul]
  exact congrArg d.emb (Subtype.ext (Model.J_comm ha.1 hb.1))

theorem J₁_le_inf_normalizer_U : d.J₁ ≤ L ⊓ normalizer (d.U : Set G) :=
  le_inf (d.image_le _) (d.J₁_le_centralizer_U.trans (Subgroup.centralizer_le_normalizer _))

end Light

variable
  [Finite K] [CharP K 2]

omit [CharP K 2] in
theorem S_inf_centralizer_J₁ (h8 : 8 ≤ Nat.card K) :
    d.S ⊓ centralizer (d.J₁ : Set G) = d.U := by
  have h1 : Model.S K ⊓ centralizer (Model.J₁ K : Set (ModGL .G2 K)) = Model.U K :=
    Model.S_inf_centralizer_Ji (by omega) 0 (Or.inl h8)
  rw [G2Data.S, G2Data.J₁, ← d.image_inf_centralizer _ (Model.torusFix_le_adjointGroup K g2c), h1]
  rfl

theorem D_inf_centralizer_J₁ (h8 : 8 ≤ Nat.card K) :
    d.D ⊓ centralizer (d.J₁ : Set G) = d.U := by
  obtain ⟨hUY, hYX, -, hXF, -, hFD, -, hDS, -, -⟩ := d.inclusions
  refine le_antisymm ?_ (le_inf (hUY.trans (hYX.trans (hXF.trans hFD)))
    (by rw [← Subgroup.le_centralizer_iff]; exact d.J₁_le_centralizer_U))
  rw [← d.S_inf_centralizer_J₁ h8]
  exact inf_le_inf_right _ hDS

end G2Data

namespace Setup

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {f : ℕ} {t : G}

section Local

variable
  {K : Type} [Field K] [Finite K]
  [CharP K 2]

theorem elemModulo_U_yamadaC₁ (h : Setup G L f t) (d : G2Data L K) (hK : Nat.card K = 2 ^ f) :
    ElemModulo d.U (yamadaC₁ d t) := by
  obtain ⟨hC₁U, -, -, -⟩ := h.two_core_C₁ d hK
  refine elemModulo_of_mul_self_mem (hC₁U.trans (Subgroup.centralizer_le_normalizer _))
    fun x hx => ?_
  have h1 : x ^ 2 ∈ closure {z | ∃ g ∈ yamadaC₁ d t, z = g ^ 2} := subset_closure ⟨x, hx, rfl⟩
  rwa [h.yamada_5_6_4 d hK, sq] at h1

theorem mem_D_of_mem_tD_of_mem_yamadaD₁ (h : Setup G L f t) (d : G2Data L K)
    (hK : Nat.card K = 2 ^ f) {x : G} (hx : x ∈ d.D ⊔ zpowers t) (hx₁ : x ∈ yamadaD₁ d t) :
    x ∈ d.D := by
  rcases (h.mem_sup_zpowers_iff (d.image_le _)).1 hx with h1 | h1
  · exact h1
  · exfalso
    refine h.t_not_mem_yamadaD₁ d hK ?_
    have := mul_mem ((le_sup_right : d.D ≤ yamadaD₁ d t) h1) (inv_mem hx₁)
    rwa [mul_inv_cancel_right] at this

theorem mul_conj_mem_D_of_mem_J₁ (h : Setup G L f t) (d : G2Data L K) (hK : Nat.card K = 2 ^ f)
    {m j : G} (hm : m ∈ yamadaD₁ d t) (hj : j ∈ d.J₁) : m⁻¹ * (j * m * j⁻¹) ∈ d.D := by
  obtain ⟨hC₁U, hC₁t, -, -⟩ := h.two_core_C₁ d hK
  have hc₁ := h.cosetData_tU d hK
  have hD₁C₁ := h.yamadaD₁_le_yamadaC₁ d hK
  have hjN := h.inf_normalizer_U_le_normalizer_yamadaD₁ d hK (d.J₁_le_inf_normalizer_U hj)
  have hjm : j * m * j⁻¹ ∈ yamadaD₁ d t := (mem_normalizer_iff.1 hjN m).1 hm
  have hV : ∀ {x : G}, x ∈ yamadaC₁ d t → x ∈ normalizer ((d.U ⊔ zpowers t : Subgroup G) :
      Set G) ⊓ centralizer (d.U : Set G) := fun hx => ⟨yamadaC₁_le d t hx, hC₁U hx⟩
  have hmC := hD₁C₁ hm
  have hjmC := hD₁C₁ hjm
  have hjt : j * t = t * j := mem_centralizer_singleton_iff.1 (h.L_le_centralizer (d.image_le _ hj))
  have h1 : (m⁻¹ * (j * m * j⁻¹))⁻¹ * t * (m⁻¹ * (j * m * j⁻¹)) * t = 1 := by
    rw [hc₁.crossed_mul_of_mem (hV (inv_mem hmC)) (hV hjmC),
      CFSG.EvenSmallLie.UnitarySix.YamadaD.crossed_conj hjt, hc₁.crossed_inv_of_mem (hV hmC),
      ← mem_centralizer_iff.1 (d.J₁_le_centralizer_U hj) _ (hc₁.crossed_mem_of_mem (hV hmC)),
      mul_inv_cancel_right, inv_mul_cancel]
  have hC : m⁻¹ * (j * m * j⁻¹) ∈ centralizer ({t} : Set G) := by
    have e' := (hc₁.crossed_eq_iff (one_mem _)).1 h1
    rw [mul_one] at e'
    rw [mem_centralizer_singleton_iff]
    calc m⁻¹ * (j * m * j⁻¹) * t =
        m⁻¹ * (j * m * j⁻¹) * ((m⁻¹ * (j * m * j⁻¹))⁻¹ * t * (m⁻¹ * (j * m * j⁻¹))) := by
          rw [e']
      _ = t * (m⁻¹ * (j * m * j⁻¹)) := by group
  refine h.mem_D_of_mem_tD_of_mem_yamadaD₁ d hK ?_ (mul_mem (inv_mem hm) hjm)
  rw [← hC₁t]
  exact Subgroup.mem_inf.2 ⟨mul_mem (inv_mem hmC) hjmC, hC⟩

theorem yamadaU₁_spec (_h : Setup G L f t) (d : G2Data L K) (h8 : 8 ≤ Nat.card K) :
    yamadaU₁ d t ≤ yamadaD₁ d t ∧ d.U ≤ yamadaU₁ d t ∧ yamadaU₁ d t ⊓ d.D = d.U := by
  obtain ⟨hUY, hYX, -, hXF, -, hFD, -⟩ := d.inclusions
  have hDD₁ : d.D ≤ yamadaD₁ d t := le_sup_right
  rw [yamadaU₁_eq d t h8]
  refine ⟨inf_le_left, le_inf ((hUY.trans (hYX.trans (hXF.trans hFD))).trans hDD₁)
    (by rw [← Subgroup.le_centralizer_iff]; exact d.J₁_le_centralizer_U), ?_⟩
  rw [inf_right_comm, inf_eq_right.2 hDD₁, d.D_inf_centralizer_J₁ h8]

theorem isPGroup_yamadaD₁ (h : Setup G L f t) (d : G2Data L K) (hK : Nat.card K = 2 ^ f) :
    IsPGroup 2 (yamadaD₁ d t) :=
  (LieType.BorelTits.pCoreOf_isPGroup 2 _).to_le (h.yamadaD₁_le_yamadaC₁ d hK)

theorem yamadaD₁_eq_sup (h : Setup G L f t) (d : G2Data L K) (hK : Nat.card K = 2 ^ f)
    (h8 : 8 ≤ Nat.card K) : yamadaD₁ d t = d.D ⊔ yamadaU₁ d t := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hU₁D₁, -, -⟩ := h.yamadaU₁_spec d h8
  obtain ⟨hNU, hND, -, -⟩ := d.yamada_3_13_2_G
  have hDD₁ : d.D ≤ yamadaD₁ d t := le_sup_right
  refine le_antisymm (fun m hm => ?_) (sup_le hDD₁ hU₁D₁)
  have hJ₁D : d.J₁ ≤ normalizer (d.D : Set G) := fun j hj => by
    have : j ∈ L ⊓ normalizer (d.D : Set G) := by
      rw [hND, ← hNU]
      exact d.J₁_le_inf_normalizer_U hj
    exact this.2
  have h2 := h.isPGroup_yamadaD₁ d hK
  have hsolv : Group.IsSolvable (yamadaD₁ d t) := by
    have := h2.isNilpotent
    infer_instance
  have hcop : (Nat.card d.J₁).Coprime (Nat.card (yamadaD₁ d t)) := by
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.1 h2
    rw [hk, d.card_J₁, hK]
    exact (odd_two_pow_sub_one (by have := h.two_le; omega)).coprime_two_right.pow_right k
  obtain ⟨c, hc, n, hn, rfl⟩ := Common.exists_mem_inf_centralizer_mul_of_coprime hDD₁
    ((h.yamadaD₁_le_yamadaC₁ d hK).trans (h.yamadaC₁_le_normalizer_D d hK))
    (fun j hj => h.inf_normalizer_U_le_normalizer_yamadaD₁ d hK (d.J₁_le_inf_normalizer_U hj))
    hJ₁D hsolv hcop hm fun j hj => h.mul_conj_mem_D_of_mem_J₁ d hK hm hj
  rw [← yamadaU₁_eq d t h8] at hc
  exact mul_mem (mem_sup_right hc) (mem_sup_left hn)

theorem yamadaU₁_inf_centralizer (h : Setup G L f t) (d : G2Data L K) (hK : Nat.card K = 2 ^ f)
    (h8 : 8 ≤ Nat.card K) : yamadaU₁ d t ⊓ centralizer ({t} : Set G) = d.U := by
  obtain ⟨-, hC₁t, -, -⟩ := h.two_core_C₁ d hK
  obtain ⟨hU₁D₁, hUU₁, hU₁D⟩ := h.yamadaU₁_spec d h8
  refine le_antisymm (fun x hx => ?_) (le_inf hUU₁ ((d.image_le _).trans h.L_le_centralizer))
  obtain ⟨hx₁, hx₂⟩ := Subgroup.mem_inf.1 hx
  have hxD : x ∈ d.D := h.mem_D_of_mem_tD_of_mem_yamadaD₁ d hK (by
    rw [← hC₁t]
    exact ⟨h.yamadaD₁_le_yamadaC₁ d hK (hU₁D₁ hx₁), hx₂⟩) (hU₁D₁ hx₁)
  rw [← hU₁D]
  exact ⟨hx₁, hxD⟩

theorem exists_mem_yamadaU₁_crossed (h : Setup G L f t) (d : G2Data L K)
    (hK : Nat.card K = 2 ^ f) (h8 : 8 ≤ Nat.card K) {u : G} (hu : u ∈ d.U) :
    ∃ x ∈ yamadaU₁ d t, x⁻¹ * t * x * t = u := by
  obtain ⟨-, -, hC₁tr, -⟩ := h.two_core_C₁ d hK
  obtain ⟨hU₁D₁, -, -⟩ := h.yamadaU₁_spec d h8
  have hc₁ := h.cosetData_tU d hK
  obtain ⟨c, hc, hct⟩ := hC₁tr u hu
  have htN : zpowers t ≤ normalizer (yamadaD₁ d t : Set G) :=
    (zpowers_le).2 (h.yamadaC₁_le_normalizer_yamadaD₁ d hK (h.t_mem_yamadaC₁ d hK))
  have hU₁N : yamadaU₁ d t ≤ normalizer (d.D : Set G) :=
    hU₁D₁.trans ((h.yamadaD₁_le_yamadaC₁ d hK).trans (h.yamadaC₁_le_normalizer_D d hK))
  rw [(h.yamada_5_8_1 d hK).2.1, sup_comm] at hc
  obtain ⟨τ, hτ, d₁, hd₁, rfl⟩ := Common.exists_mul_of_le_normalizer' htN c hc
  rw [h.yamadaD₁_eq_sup d hK h8] at hd₁
  obtain ⟨δ, hδ, x, hx, rfl⟩ := Common.exists_mul_of_le_normalizer hU₁N d₁ hd₁
  refine ⟨x, hx, ?_⟩
  have hτt : τ * t = t * τ := (commute_of_mem_zpowers hτ h.t_mem_centralizer).symm
  have hδt : δ * t = t * δ := mem_centralizer_singleton_iff.1
    (h.L_le_centralizer (d.image_le _ hδ))
  have e : (τ * (δ * x))⁻¹ * t * (τ * (δ * x)) = x⁻¹ * t * x := by
    have h1 : τ⁻¹ * t * τ = t := by rw [mul_assoc, ← hτt, inv_mul_cancel_left]
    have h2 : δ⁻¹ * t * δ = t := by rw [mul_assoc, ← hδt, inv_mul_cancel_left]
    calc (τ * (δ * x))⁻¹ * t * (τ * (δ * x)) = x⁻¹ * (δ⁻¹ * (τ⁻¹ * t * τ) * δ) * x := by group
      _ = x⁻¹ * t * x := by rw [h1, h2]
  rw [← (hc₁.crossed_eq_iff hu).2 hct, e]

theorem yamada_5_10_1 (h : Setup G L f t) (d : G2Data L K) (hK : Nat.card K = 2 ^ f)
    (h8 : 8 ≤ Nat.card K) :
    yamadaD₁ d t = d.D ⊔ yamadaU₁ d t ∧ yamadaU₁ d t ⊓ centralizer ({t} : Set G) = d.U ∧
      Nat.card (yamadaU₁ d t) = Nat.card K ^ 2 := by
  obtain ⟨hC₁U, -, -, -⟩ := h.two_core_C₁ d hK
  obtain ⟨hU₁D₁, hUU₁, -⟩ := h.yamadaU₁_spec d h8
  have hc₁ := h.cosetData_tU d hK
  have hU₁C₁ : yamadaU₁ d t ≤ yamadaC₁ d t := hU₁D₁.trans (h.yamadaD₁_le_yamadaC₁ d hK)
  have hinf := h.yamadaU₁_inf_centralizer d hK h8
  refine ⟨h.yamadaD₁_eq_sup d hK h8, hinf, ?_⟩
  let ψ := CFSG.EvenSmallLie.UnitarySix.YamadaD.crossedHom h.t_mul_t d.U (yamadaU₁ d t)
    (hU₁C₁.trans hC₁U) fun y hy => hc₁.crossed_mem y (yamadaC₁_le d t (hU₁C₁ hy))
  have hsurj : Function.Surjective ψ := by
    rintro ⟨u, hu⟩
    obtain ⟨x, hx, hxu⟩ := h.exists_mem_yamadaU₁_crossed d hK h8 hu
    exact ⟨⟨x, hx⟩, Subtype.ext hxu⟩
  have hker : ψ.ker = d.U.subgroupOf (yamadaU₁ d t) := by
    ext x
    rw [CFSG.EvenSmallLie.UnitarySix.YamadaD.mem_ker_crossedHom, mem_subgroupOf, ← hinf]
    exact ⟨fun e => ⟨x.2, mem_centralizer_singleton_iff.2 e⟩,
      fun e => mem_centralizer_singleton_iff.1 e.2⟩
  rw [CFSG.EvenSmallLie.UnitarySix.YamadaD.card_eq_card_ker_mul_card_range ψ, hker,
    MonoidHom.range_eq_top.2 hsurj, Subgroup.card_top,
    Nat.card_congr (subgroupOfEquivOfLe hUU₁).toEquiv, d.cards.1, sq]

theorem conj_mem_yamadaU₁ (h : Setup G L f t) (d : G2Data L K) (hK : Nat.card K = 2 ^ f)
    (h8 : 8 ≤ Nat.card K) {j x : G} (hj : j ∈ d.J₃) (hx : x ∈ yamadaU₁ d t) :
    j * x * j⁻¹ ∈ yamadaU₁ d t := by
  rw [yamadaU₁_eq d t h8] at hx ⊢
  obtain ⟨hx₁, hx₂⟩ := Subgroup.mem_inf.1 hx
  refine Subgroup.mem_inf.2 ⟨(mem_normalizer_iff.1 (h.inf_normalizer_U_le_normalizer_yamadaD₁ d
    hK (d.J₃_le_inf_normalizer_U hj)) x).1 hx₁, mem_centralizer_iff.2 fun y hy => ?_⟩
  have hyj : y * j = j * y := d.J₁_comm_J₃ hy hj
  have hyx : y * x = x * y := mem_centralizer_iff.1 hx₂ y hy
  have hyj' : y * j⁻¹ = j⁻¹ * y := by
    calc y * j⁻¹ = j⁻¹ * (j * y) * j⁻¹ := by group
      _ = j⁻¹ * y := by rw [← hyj]; group
  calc y * (j * x * j⁻¹) = (y * j) * x * j⁻¹ := by group
    _ = j * (y * x) * j⁻¹ := by rw [hyj]; group
    _ = j * x * (y * j⁻¹) := by rw [hyx]; group
    _ = j * x * j⁻¹ * y := by rw [hyj']; group

theorem exists_coords_yamadaU₁ (h : Setup G L f t) (d : G2Data L K) (hK : Nat.card K = 2 ^ f)
    (h8 : 8 ≤ Nat.card K) :
    ∃ ν : G → K, (∀ {u u' : G}, u ∈ d.U → u' ∈ d.U → ν (u * u') = ν u + ν u') ∧
      (∀ {u u' : G}, u ∈ d.U → u' ∈ d.U → ν u = ν u' → u = u') ∧ (∀ z : K, ∃ u ∈ d.U, ν u = z) ∧
      (∀ a : K, a ≠ 0 → ∃ j ∈ d.J₃, ∀ u ∈ d.U, ν (j * u * j⁻¹) = a * ν u) ∧
      (∀ {x : G}, x ∈ yamadaU₁ d t → x⁻¹ * t * x * t ∈ d.U) ∧
      (∀ {x : G}, x ∈ yamadaU₁ d t → (ν (x⁻¹ * t * x * t) = ν 1 ↔ x ∈ d.U)) := by
  obtain ⟨ι, hι⟩ := d.exists_mulEquiv_U
  obtain ⟨hC₁U, -, -, -⟩ := h.two_core_C₁ d hK
  obtain ⟨hU₁D₁, -, -⟩ := h.yamadaU₁_spec d h8
  have hc₁ := h.cosetData_tU d hK
  have hU₁C₁ : yamadaU₁ d t ≤ yamadaC₁ d t := hU₁D₁.trans (h.yamadaD₁_le_yamadaC₁ d hK)
  have hinf := h.yamadaU₁_inf_centralizer d hK h8
  classical
  let ν : G → K := fun g => if hg : g ∈ d.U then Multiplicative.toAdd (ι.symm ⟨g, hg⟩) else 0
  have hν : ∀ {g : G} (hg : g ∈ d.U), ν g = Multiplicative.toAdd (ι.symm ⟨g, hg⟩) :=
    fun hg => dite_eq_left hg
  have hνι : ∀ z : K, ν (ι (Multiplicative.ofAdd z)) = z := fun z => by
    rw [hν (ι _).2, Subtype.coe_eta, MulEquiv.symm_apply_apply, toAdd_ofAdd]
  have hιν : ∀ {g : G} (hg : g ∈ d.U), (ι (Multiplicative.ofAdd (ν g)) : G) = g := fun hg => by
    rw [hν hg, ofAdd_toAdd, MulEquiv.apply_symm_apply]
  refine ⟨ν, fun {u u'} hu hu' => ?_, fun {u u'} hu hu' e => ?_, fun z => ⟨_, (ι _).2, hνι z⟩,
    fun a ha => ?_, fun {x} hx => hc₁.crossed_mem x (yamadaC₁_le d t (hU₁C₁ hx)),
    fun {x} hx => ?_⟩
  · rw [hν (mul_mem hu hu'), hν hu, hν hu', ← toAdd_mul, ← map_mul]
    rfl
  · rw [← hιν hu, ← hιν hu', e]
  · obtain ⟨j, hj, hjx⟩ := d.exists_mem_J₃_scalar ι hι ha
    refine ⟨j, hj, fun u hu => ?_⟩
    rw [← hιν hu, hjx, hνι, hνι]
  · have h1 : ν 1 = 0 := by
      rw [hν (one_mem _), show (⟨1, one_mem _⟩ : d.U) = 1 from rfl, map_one, toAdd_one]
    have hxU := hc₁.crossed_mem x (yamadaC₁_le d t (hU₁C₁ hx))
    rw [h1]
    constructor
    · intro e
      have e' : x⁻¹ * t * x * t = 1 := by
        rw [← hιν hxU, e, ofAdd_zero, map_one, OneMemClass.coe_one]
      rw [← hinf]
      refine ⟨hx, mem_centralizer_singleton_iff.2 ?_⟩
      have e'' := (hc₁.crossed_eq_iff (one_mem _)).1 e'
      rw [mul_one] at e''
      calc x * t = x * (x⁻¹ * t * x) := by rw [e'']
        _ = t * x := by group
    · intro hxU'
      have hxt : x * t = t * x := mem_centralizer_singleton_iff.1 (((d.image_le _).trans
        h.L_le_centralizer) hxU')
      rw [show x⁻¹ * t * x * t = 1 by rw [mul_assoc x⁻¹, ← hxt, inv_mul_cancel_left, h.t_mul_t],
        ← h1]

theorem yamadaU₁_mul_comm (h : Setup G L f t) (d : G2Data L K) (hK : Nat.card K = 2 ^ f)
    (h8 : 8 ≤ Nat.card K) {x y : G} (hx : x ∈ yamadaU₁ d t) (hy : y ∈ yamadaU₁ d t) :
    x * y = y * x := by
  obtain ⟨ν, hνmul, hνinj, hνsurj, hνscal, hκU, hκker⟩ := h.exists_coords_yamadaU₁ d hK h8
  obtain ⟨hC₁U, -, -, -⟩ := h.two_core_C₁ d hK
  obtain ⟨hU₁D₁, hUU₁, -⟩ := h.yamadaU₁_spec d h8
  have hc₁ := h.cosetData_tU d hK
  have hU₁C₁ : yamadaU₁ d t ≤ yamadaC₁ d t := hU₁D₁.trans (h.yamadaD₁_le_yamadaC₁ d hK)
  have hcen : ∀ {u g : G}, u ∈ d.U → g ∈ yamadaC₁ d t → u * g = g * u := fun hu hg =>
    mem_centralizer_iff.1 (hC₁U hg) _ hu
  have hcomm : ∀ {g g' : G}, g ∈ yamadaC₁ d t → g' ∈ yamadaC₁ d t → ⁅g, g'⁆ ∈ d.U :=
    fun hg hg' => ((h.elemModulo_U_yamadaC₁ d hK) _ hg _ hg').2
  have hV : ∀ {g : G}, g ∈ yamadaU₁ d t → g ∈ normalizer ((d.U ⊔ zpowers t : Subgroup G) :
      Set G) ⊓ centralizer (d.U : Set G) := fun hg =>
    ⟨yamadaC₁_le d t (hU₁C₁ hg), hC₁U (hU₁C₁ hg)⟩
  have hν1 : ν 1 = 0 := by
    have := hνmul (one_mem d.U) (one_mem d.U)
    rwa [mul_one, left_eq_add] at this
  set θ : G → K := fun g => ν (g⁻¹ * t * g * t) with hθdef
  have hθmul : ∀ {g g' : G}, g ∈ yamadaU₁ d t → g' ∈ yamadaU₁ d t →
      θ (g * g') = θ g + θ g' := fun hg hg' => by
    simp only [hθdef]
    rw [hc₁.crossed_mul_of_mem (hV hg) (hV hg'), hνmul (hκU hg) (hκU hg')]
  have hθker : ∀ {g : G}, g ∈ yamadaU₁ d t → (θ g = 0 ↔ g ∈ d.U) := fun hg => by
    rw [← hν1]
    exact hκker hg
  have hθ1 : θ 1 = 0 := (hθker (one_mem _)).2 (one_mem _)
  have hθsurj : ∀ z : K, ∃ g ∈ yamadaU₁ d t, θ g = z := fun z => by
    obtain ⟨u, hu, rfl⟩ := hνsurj z
    obtain ⟨g, hg, hgu⟩ := h.exists_mem_yamadaU₁_crossed d hK h8 hu
    exact ⟨g, hg, by simp only [hθdef]; rw [hgu]⟩
  have hθmod : ∀ {g g' : G}, g ∈ yamadaU₁ d t → g' ∈ yamadaU₁ d t → θ g = θ g' →
      g⁻¹ * g' ∈ d.U := fun {g g'} hg hg' e => by
    have h0 := hθmul (inv_mem hg) hg
    rw [inv_mul_cancel, hθ1] at h0
    refine (hθker (mul_mem (inv_mem hg) hg')).1 ?_
    rw [hθmul (inv_mem hg) hg', ← e]
    exact h0.symm
  have hP1 : ∀ {g g' u : G}, g' ∈ yamadaC₁ d t → u ∈ d.U → ⁅g * u, g'⁆ = ⁅g, g'⁆ :=
    fun {g g' u} hg' hu => by
      rw [commutatorElement_def, commutatorElement_def,
        show g * u * g' * (g * u)⁻¹ * g'⁻¹ = g * (u * g') * u⁻¹ * g⁻¹ * g'⁻¹ by group,
        hcen hu hg']
      group
  have hP2 : ∀ {g g' u : G}, g ∈ yamadaC₁ d t → u ∈ d.U → ⁅g, g' * u⁆ = ⁅g, g'⁆ :=
    fun {g g' u} hg hu => by
      rw [commutatorElement_def, commutatorElement_def,
        show g * (g' * u) * g⁻¹ * (g' * u)⁻¹ = g * g' * (u * g⁻¹) * u⁻¹ * g'⁻¹ by group,
        hcen hu (inv_mem hg)]
      group
  have hP3 : ∀ {g g' g'' : G}, g ∈ yamadaC₁ d t → g' ∈ yamadaC₁ d t → g'' ∈ yamadaC₁ d t →
      ⁅g * g', g''⁆ = ⁅g', g''⁆ * ⁅g, g''⁆ := fun {g g' g''} hg hg' hg'' => by
    calc ⁅g * g', g''⁆ = g * ⁅g', g''⁆ * (g'' * g⁻¹ * g''⁻¹) := by
          simp only [commutatorElement_def]
          group
      _ = ⁅g', g''⁆ * g * (g'' * g⁻¹ * g''⁻¹) := by rw [← hcen (hcomm hg' hg'') hg]
      _ = ⁅g', g''⁆ * ⁅g, g''⁆ := by
          simp only [commutatorElement_def]
          group
  have hP4 : ∀ {g g' g'' : G}, g ∈ yamadaC₁ d t → g' ∈ yamadaC₁ d t → g'' ∈ yamadaC₁ d t →
      ⁅g, g' * g''⁆ = ⁅g, g'⁆ * ⁅g, g''⁆ := fun {g g' g''} hg hg' hg'' => by
    calc ⁅g, g' * g''⁆ = ⁅g, g'⁆ * (g' * ⁅g, g''⁆) * g'⁻¹ := by
          simp only [commutatorElement_def]
          group
      _ = ⁅g, g'⁆ * (⁅g, g''⁆ * g') * g'⁻¹ := by rw [hcen (hcomm hg hg'') hg']
      _ = ⁅g, g'⁆ * ⁅g, g''⁆ := by group
  choose X hX hXθ using hθsurj
  have hXC : ∀ z, X z ∈ yamadaC₁ d t := fun z => hU₁C₁ (hX z)
  have hlift : ∀ {g : G} (z : K), g ∈ yamadaU₁ d t → θ g = z → ∃ u ∈ d.U, g = X z * u :=
    fun {g} z hg e => ⟨_, hθmod (hX z) hg ((hXθ z).trans e.symm), by group⟩
  set β : K → K → K := fun z w => ν ⁅X z, X w⁆ with hβdef
  have hβ1 : ∀ z z' w, β (z + z') w = β z w + β z' w := by
    intro z z' w
    obtain ⟨u, hu, hue⟩ := hlift (z + z') (mul_mem (hX z) (hX z'))
      (by rw [hθmul (hX z) (hX z'), hXθ, hXθ])
    simp only [hβdef]
    rw [← hP1 (hXC w) hu, ← hue, hP3 (hXC z) (hXC z') (hXC w),
      hνmul (hcomm (hXC z') (hXC w)) (hcomm (hXC z) (hXC w)), add_comm]
  have hβ2 : ∀ z w w', β z (w + w') = β z w + β z w' := by
    intro z w w'
    obtain ⟨u, hu, hue⟩ := hlift (w + w') (mul_mem (hX w) (hX w'))
      (by rw [hθmul (hX w) (hX w'), hXθ, hXθ])
    simp only [hβdef]
    rw [← hP2 (hXC z) hu, ← hue, hP4 (hXC z) (hXC w) (hXC w'),
      hνmul (hcomm (hXC z) (hXC w)) (hcomm (hXC z) (hXC w'))]
  have hβ3 : ∀ z, β z z = 0 := fun z => by
    simp only [hβdef]
    rw [commutatorElement_self, hν1]
  have hβ4 : ∀ a z w, a ≠ 0 → β (a * z) (a * w) = a * β z w := by
    intro a z w ha
    obtain ⟨j, hj, hju⟩ := hνscal a ha
    have hjt : j * t = t * j := mem_centralizer_singleton_iff.1
      (h.L_le_centralizer (d.image_le _ hj))
    have hθj : ∀ {g : G}, g ∈ yamadaU₁ d t → θ (j * g * j⁻¹) = a * θ g := fun {g} hg => by
      simp only [hθdef]
      rw [CFSG.EvenSmallLie.UnitarySix.YamadaD.crossed_conj hjt, hju _ (hκU hg)]
    obtain ⟨u, hu, hue⟩ := hlift (a * z) (h.conj_mem_yamadaU₁ d hK h8 hj (hX z))
      (by rw [hθj (hX z), hXθ])
    obtain ⟨u', hu', hue'⟩ := hlift (a * w) (h.conj_mem_yamadaU₁ d hK h8 hj (hX w))
      (by rw [hθj (hX w), hXθ])
    have hjz := hU₁C₁ (h.conj_mem_yamadaU₁ d hK h8 hj (hX z))
    simp only [hβdef]
    rw [← hP1 (hXC (a * w)) hu, ← hue, ← hP2 hjz hu', ← hue',
      show ⁅j * X z * j⁻¹, j * X w * j⁻¹⁆ = j * ⁅X z, X w⁆ * j⁻¹ by
        simp only [commutatorElement_def]
        group, hju _ (hcomm (hXC z) (hXC w))]
  have hβ := eq_zero_of_alternating_equivariant β hβ1 hβ2 hβ3 hβ4
  obtain ⟨u, hu, hxe⟩ := hlift (θ x) hx rfl
  obtain ⟨u', hu', hye⟩ := hlift (θ y) hy rfl
  have hc : ⁅x, y⁆ = 1 := by
    rw [hxe, hye, hP1 (mul_mem (hXC _) ((hUU₁.trans hU₁C₁) hu')) hu, hP2 (hXC _) hu']
    exact hνinj (hcomm (hXC _) (hXC _)) (one_mem _) ((hβ (θ x) (θ y)).trans hν1.symm)
  exact commutatorElement_eq_one_iff_mul_comm.1 hc

theorem yamada_5_10_2 (h : Setup G L f t) (d : G2Data L K) (hK : Nat.card K = 2 ^ f)
    (h8 : 8 ≤ Nat.card K) :
    CFSG.IsElementaryAbelian 2 (yamadaU₁ d t) ∨
      (IsMulCommutative (yamadaU₁ d t) ∧ (∀ x ∈ yamadaU₁ d t, x ^ 4 = 1) ∧
        (∀ x ∈ yamadaU₁ d t, x ^ 2 = 1 ↔ x ∈ d.U) ∧
        closure {z | ∃ g ∈ yamadaU₁ d t, z = g ^ 2} = d.U) := by
  obtain ⟨ν, hνmul, hνinj, hνsurj, hνscal, hκU, hκker⟩ := h.exists_coords_yamadaU₁ d hK h8
  obtain ⟨hC₁U, -, -, -⟩ := h.two_core_C₁ d hK
  obtain ⟨hU₁D₁, hUU₁, -⟩ := h.yamadaU₁_spec d h8
  have hc₁ := h.cosetData_tU d hK
  have hU₁C₁ : yamadaU₁ d t ≤ yamadaC₁ d t := hU₁D₁.trans (h.yamadaD₁_le_yamadaC₁ d hK)
  have hV : ∀ {g : G}, g ∈ yamadaU₁ d t → g ∈ normalizer ((d.U ⊔ zpowers t : Subgroup G) :
      Set G) ⊓ centralizer (d.U : Set G) := fun hg =>
    ⟨yamadaC₁_le d t (hU₁C₁ hg), hC₁U (hU₁C₁ hg)⟩
  have hcomm : ∀ {g g' : G}, g ∈ yamadaU₁ d t → g' ∈ yamadaU₁ d t → g * g' = g' * g :=
    fun hg hg' => h.yamadaU₁_mul_comm d hK h8 hg hg'
  have hν1 : ν 1 = 0 := by
    have := hνmul (one_mem d.U) (one_mem d.U)
    rwa [mul_one, left_eq_add] at this
  have hUsq : ∀ {u : G}, u ∈ d.U → u * u = 1 := fun hu => (h.cosetData_tU d hK).mul_self_of_mem hu
  have hsqU : ∀ {g : G}, g ∈ yamadaU₁ d t → g * g ∈ d.U := fun {g} hg => by
    have h1 : g ^ 2 ∈ closure {z | ∃ g ∈ yamadaC₁ d t, z = g ^ 2} :=
      subset_closure ⟨g, hU₁C₁ hg, rfl⟩
    rwa [h.yamada_5_6_4 d hK, sq] at h1
  set θ : G → K := fun g => ν (g⁻¹ * t * g * t) with hθdef
  have hθmul : ∀ {g g' : G}, g ∈ yamadaU₁ d t → g' ∈ yamadaU₁ d t →
      θ (g * g') = θ g + θ g' := fun hg hg' => by
    simp only [hθdef]
    rw [hc₁.crossed_mul_of_mem (hV hg) (hV hg'), hνmul (hκU hg) (hκU hg')]
  have hθker : ∀ {g : G}, g ∈ yamadaU₁ d t → (θ g = 0 ↔ g ∈ d.U) := fun hg => by
    rw [← hν1]
    exact hκker hg
  have hθ1 : θ 1 = 0 := (hθker (one_mem _)).2 (one_mem _)
  have hθsurj : ∀ z : K, ∃ g ∈ yamadaU₁ d t, θ g = z := fun z => by
    obtain ⟨u, hu, rfl⟩ := hνsurj z
    obtain ⟨g, hg, hgu⟩ := h.exists_mem_yamadaU₁_crossed d hK h8 hu
    exact ⟨g, hg, by simp only [hθdef]; rw [hgu]⟩
  have hθmod : ∀ {g g' : G}, g ∈ yamadaU₁ d t → g' ∈ yamadaU₁ d t → θ g = θ g' →
      g⁻¹ * g' ∈ d.U := fun {g g'} hg hg' e => by
    have h0 := hθmul (inv_mem hg) hg
    rw [inv_mul_cancel, hθ1] at h0
    refine (hθker (mul_mem (inv_mem hg) hg')).1 ?_
    rw [hθmul (inv_mem hg) hg', ← e]
    exact h0.symm
  choose X hX hXθ using hθsurj
  have hlift : ∀ {g : G} (z : K), g ∈ yamadaU₁ d t → θ g = z → ∃ u ∈ d.U, g = X z * u :=
    fun {g} z hg e => ⟨_, hθmod (hX z) hg ((hXθ z).trans e.symm), by group⟩
  have hsq_mul : ∀ {g u : G}, g ∈ yamadaU₁ d t → u ∈ d.U → (g * u) * (g * u) = g * g :=
    fun {g u} hg hu => by
      rw [show g * u * (g * u) = g * (u * g) * u by group, ← hcomm hg (hUU₁ hu)]
      rw [show g * (g * u) * u = g * g * (u * u) by group, hUsq hu, mul_one]
  have hsq_mul' : ∀ {g g' : G}, g ∈ yamadaU₁ d t → g' ∈ yamadaU₁ d t →
      (g * g') * (g * g') = (g * g) * (g' * g') := fun {g g'} hg hg' => by
    rw [show g * g' * (g * g') = g * (g' * g) * g' by group, ← hcomm hg hg']
    group
  set σ : K → K := fun z => ν (X z * X z) with hσdef
  have hσ_add : ∀ z w, σ (z + w) = σ z + σ w := by
    intro z w
    obtain ⟨u, hu, hue⟩ := hlift (z + w) (mul_mem (hX z) (hX w))
      (by rw [hθmul (hX z) (hX w), hXθ, hXθ])
    simp only [hσdef]
    rw [← hsq_mul (hX (z + w)) hu, ← hue, hsq_mul' (hX z) (hX w),
      hνmul (hsqU (hX z)) (hsqU (hX w))]
  have hσ_smul : ∀ a z, a ≠ 0 → σ (a * z) = a * σ z := by
    intro a z ha
    obtain ⟨j, hj, hju⟩ := hνscal a ha
    have hjt : j * t = t * j := mem_centralizer_singleton_iff.1
      (h.L_le_centralizer (d.image_le _ hj))
    have hjz := h.conj_mem_yamadaU₁ d hK h8 hj (hX z)
    obtain ⟨u, hu, hue⟩ := hlift (a * z) hjz (by
      simp only [hθdef]
      rw [CFSG.EvenSmallLie.UnitarySix.YamadaD.crossed_conj hjt, hju _ (hκU (hX z))]
      exact congrArg (a * ·) (hXθ z))
    simp only [hσdef]
    rw [← hsq_mul (hX (a * z)) hu, ← hue,
      show j * X z * j⁻¹ * (j * X z * j⁻¹) = j * (X z * X z) * j⁻¹ by group,
      hju _ (hsqU (hX z))]
  have hσ : ∀ z, σ z = z * σ 1 := fun z => by
    by_cases hz : z = 0
    · rw [hz, zero_mul]
      have := hσ_add 0 0
      rwa [add_zero, left_eq_add] at this
    · rw [← hσ_smul z 1 hz, mul_one]
  have hgsq : ∀ {g : G}, g ∈ yamadaU₁ d t → ν (g * g) = θ g * σ 1 := fun {g} hg => by
    obtain ⟨u, hu, hue⟩ := hlift (θ g) hg rfl
    have e : g * g = X (θ g) * X (θ g) := by
      calc g * g = (X (θ g) * u) * (X (θ g) * u) := by rw [← hue]
        _ = X (θ g) * X (θ g) := hsq_mul (hX _) hu
    rw [e]
    exact hσ (θ g)
  have hIC : IsMulCommutative (yamadaU₁ d t) :=
    ⟨⟨fun a b => Subtype.ext (hcomm a.2 b.2)⟩⟩
  by_cases hlam : σ 1 = 0
  · left
    refine isElementaryAbelian_of_forall (fun a ha b hb => hcomm ha hb) fun g hg => ?_
    refine hνinj (hsqU hg) (one_mem _) ?_
    rw [hgsq hg, hlam, mul_zero, hν1]
  · right
    have hsq1 : ∀ {g : G}, g ∈ yamadaU₁ d t → (g * g = 1 ↔ g ∈ d.U) := fun {g} hg => by
      rw [← hθker hg]
      constructor
      · intro e
        have := hgsq hg
        rw [e, hν1] at this
        exact (mul_eq_zero.1 this.symm).resolve_right hlam
      · intro e
        refine hνinj (hsqU hg) (one_mem _) ?_
        rw [hgsq hg, e, zero_mul, hν1]
    refine ⟨hIC, fun g hg => ?_, fun g hg => by rw [sq]; exact hsq1 hg, ?_⟩
    · rw [show g ^ 4 = (g * g) * (g * g) by rw [show (4 : ℕ) = 2 + 2 from rfl, pow_add, sq]]
      exact hUsq (hsqU hg)
    · refine le_antisymm ((closure_le _).2 fun z ⟨g, hg, e⟩ => e ▸ sq g ▸ hsqU hg) fun u hu => ?_
      obtain ⟨w, hw⟩ : ∃ w, ν u = w := ⟨_, rfl⟩
      refine subset_closure ⟨X ((σ 1)⁻¹ * w), hX _, ?_⟩
      rw [sq]
      refine hνinj hu (hsqU (hX _)) ?_
      rw [hgsq (hX _), hXθ, hw, mul_comm, ← mul_assoc, mul_inv_cancel₀ hlam, one_mul]

theorem le_centralizer_yamadaU₁_of (h : Setup G L f t) (d : G2Data L K) (hK : Nat.card K = 2 ^ f)
    (h8 : 8 ≤ Nat.card K) {P : Subgroup G} (hPS : P ≤ d.S)
    (hPN : P ≤ normalizer (yamadaU₁ d t : Set G)) (hJP : d.J₁ ≤ normalizer (P : Set G))
    (hcomm : ∀ {p u : G}, p ∈ P → u ∈ yamadaU₁ d t → ⁅p, u⁆ ∈ d.U) :
    P ≤ centralizer (yamadaU₁ d t : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hC₁U, -, -, -⟩ := h.two_core_C₁ d hK
  obtain ⟨hU₁D₁, -, -⟩ := h.yamadaU₁_spec d h8
  have hU₁C₁ : yamadaU₁ d t ≤ yamadaC₁ d t := hU₁D₁.trans (h.yamadaD₁_le_yamadaC₁ d hK)
  have hcenS : ∀ {u g : G}, u ∈ d.U → g ∈ d.S → u * g = g * u := fun {u g} hu hg => by
    rw [← (d.yamada_3_12_centers).1] at hu
    exact (mem_centralizer_iff.1 hu.2 g hg).symm
  have hJ₁U₁ : d.J₁ ≤ centralizer (yamadaU₁ d t : Set G) := by
    rw [← Subgroup.le_centralizer_iff, yamadaU₁_eq d t h8]
    exact inf_le_right
  have hCN : normalizer (yamadaU₁ d t : Set G) ≤
      normalizer (centralizer (yamadaU₁ d t : Set G) : Set G) := by
    intro n hn
    refine mem_normalizer_of_conj_mem fun y hy => mem_centralizer_iff.2 fun x hx => ?_
    have hx' : n⁻¹ * x * n ∈ yamadaU₁ d t := by
      have := (mem_normalizer_iff.1 (inv_mem hn) x).1 hx
      rwa [inv_inv] at this
    have e := mem_centralizer_iff.1 hy _ hx'
    calc x * (n * y * n⁻¹) = n * ((n⁻¹ * x * n) * y) * n⁻¹ := by group
      _ = n * (y * (n⁻¹ * x * n)) * n⁻¹ := by rw [e]
      _ = n * y * n⁻¹ * x := by group
  set N := P ⊓ centralizer (yamadaU₁ d t : Set G) with hNdef
  have h2 : IsPGroup 2 P := d.isSylowOf_S.isPGroup.to_le hPS
  have hsolv : Group.IsSolvable P := by
    have := h2.isNilpotent
    infer_instance
  have hcop : (Nat.card d.J₁).Coprime (Nat.card P) := by
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.1 h2
    rw [hk, d.card_J₁, hK]
    exact (odd_two_pow_sub_one (by have := h.two_le; omega)).coprime_two_right.pow_right k
  intro p hp
  have hfix : ∀ j ∈ d.J₁, p⁻¹ * (j * p * j⁻¹) ∈ N := by
    intro j hj
    have hjp : j * p * j⁻¹ ∈ P := (mem_normalizer_iff.1 (hJP hj) p).1 hp
    refine Subgroup.mem_inf.2 ⟨mul_mem (inv_mem hp) hjp, mem_centralizer_iff.2 fun u hu => ?_⟩
    have hju : j * u = u * j := (mem_centralizer_iff.1 (hJ₁U₁ hj) u hu).symm
    have hjc : ∀ {w : G}, w ∈ d.U → j * w * j⁻¹ = w := fun {w} hw => by
      rw [← mem_centralizer_iff.1 (d.J₁_le_centralizer_U hj) w hw, mul_inv_cancel_right]
    have hju' : j⁻¹ * u = u * j⁻¹ := by
      calc j⁻¹ * u = j⁻¹ * (u * j) * j⁻¹ := by group
        _ = j⁻¹ * (j * u) * j⁻¹ := by rw [← hju]
        _ = u * j⁻¹ := by group
    have hk1 : ⁅j * p * j⁻¹, u⁆ = ⁅p, u⁆ := by
      calc ⁅j * p * j⁻¹, u⁆ = j * p * (j⁻¹ * u) * j * p⁻¹ * j⁻¹ * u⁻¹ := by
            simp only [commutatorElement_def]
            group
        _ = j * p * (u * j⁻¹) * j * p⁻¹ * j⁻¹ * u⁻¹ := by rw [hju']
        _ = j * (p * u * p⁻¹ * u⁻¹) * (u * j⁻¹ * u⁻¹) := by group
        _ = j * ⁅p, u⁆ * j⁻¹ := by
            rw [← hju', mul_inv_cancel_right, commutatorElement_def]
        _ = ⁅p, u⁆ := hjc (hcomm hp hu)
    have hP3 : ∀ {g g' : G}, g ∈ P → g' ∈ P → ⁅g * g', u⁆ = ⁅g', u⁆ * ⁅g, u⁆ :=
      fun {g g'} hg hg' => by
        calc ⁅g * g', u⁆ = g * ⁅g', u⁆ * (u * g⁻¹ * u⁻¹) := by
              simp only [commutatorElement_def]
              group
          _ = ⁅g', u⁆ * g * (u * g⁻¹ * u⁻¹) := by rw [← hcenS (hcomm hg' hu) (hPS hg)]
          _ = ⁅g', u⁆ * ⁅g, u⁆ := by
              simp only [commutatorElement_def]
              group
    have h1 : ⁅p⁻¹ * (j * p * j⁻¹), u⁆ = 1 := by
      rw [hP3 (inv_mem hp) hjp, hk1, ← hP3 (inv_mem hp) hp, inv_mul_cancel,
        commutatorElement_one_left]
    exact (commutatorElement_eq_one_iff_mul_comm.1 h1).symm
  obtain ⟨c, hc, n, hn, rfl⟩ := Common.exists_mem_inf_centralizer_mul_of_coprime
    (N := N) inf_le_left
    (fun x hx => Common.mem_normalizer_inf (le_normalizer hx) (hCN (hPN hx)))
    hJP (fun j hj => Common.mem_normalizer_inf (hJP hj) (le_normalizer (hJ₁U₁ hj)))
    hsolv hcop hp hfix
  have hcU : c ∈ d.U := by
    rw [← d.S_inf_centralizer_J₁ h8]
    exact ⟨hPS hc.1, hc.2⟩
  refine mul_mem (mem_centralizer_iff.2 fun x hx => ?_) (Subgroup.mem_inf.1 hn).2
  exact mem_centralizer_iff.1 (hC₁U (hU₁C₁ hx)) c hcU |>.symm

theorem yamadaC₁_le_normalizer_yamadaU₁ (h : Setup G L f t) (d : G2Data L K)
    (hK : Nat.card K = 2 ^ f) (h8 : 8 ≤ Nat.card K) :
    yamadaC₁ d t ≤ normalizer (yamadaU₁ d t : Set G) := by
  obtain ⟨hU₁D₁, hUU₁, -⟩ := h.yamadaU₁_spec d h8
  have hU₁C₁ : yamadaU₁ d t ≤ yamadaC₁ d t := hU₁D₁.trans (h.yamadaD₁_le_yamadaC₁ d hK)
  refine le_normalizer_of_conj_mem fun c hc x hx => ?_
  have h1 := ((h.elemModulo_U_yamadaC₁ d hK) _ hc _ (hU₁C₁ hx)).2
  rw [commutatorElement_def] at h1
  rw [show c * x * c⁻¹ = c * x * c⁻¹ * x⁻¹ * x by group]
  exact mul_mem (hUU₁ h1) hx

theorem D_le_centralizer_yamadaU₁ (h : Setup G L f t) (d : G2Data L K) (hK : Nat.card K = 2 ^ f)
    (h8 : 8 ≤ Nat.card K) : d.D ≤ centralizer (yamadaU₁ d t : Set G) := by
  obtain ⟨hNU, hND, -, -⟩ := d.yamada_3_13_2_G
  obtain ⟨hU₁D₁, -, -⟩ := h.yamadaU₁_spec d h8
  have hU₁C₁ : yamadaU₁ d t ≤ yamadaC₁ d t := hU₁D₁.trans (h.yamadaD₁_le_yamadaC₁ d hK)
  have hDC₁ : d.D ≤ yamadaC₁ d t := le_sup_left.trans (h.tD_le_yamadaC₁ d hK)
  refine h.le_centralizer_yamadaU₁_of d hK h8 d.inclusions.2.2.2.2.2.2.2.1
    (hDC₁.trans (h.yamadaC₁_le_normalizer_yamadaU₁ d hK h8)) (fun j hj => ?_)
    fun hp hu => ((h.elemModulo_U_yamadaC₁ d hK) _ (hDC₁ hp) _ (hU₁C₁ hu)).2
  have : j ∈ L ⊓ normalizer (d.D : Set G) := by
    rw [hND, ← hNU]
    exact d.J₁_le_inf_normalizer_U hj
  exact this.2

theorem mem_yamadaL₂_of_mem_centralizer_Y (h : Setup G L f t) (d : G2Data L K)
    (hK : Nat.card K = 2 ^ f) {x : G} (hx : x ∈ yamadaR₂ d t)
    (hxY : x ∈ centralizer (d.Y : Set G)) : x ∈ yamadaL₂ d t := by
  obtain ⟨hL₂Y, -, -, -⟩ := h.two_core_L₂ d hK
  obtain ⟨l, hl, s, hs, rfl⟩ := Common.exists_mul_of_le_normalizer
    (h.S_le_normalizer_yamadaL₂ d) x hx
  have hsY : s ∈ centralizer (d.Y : Set G) := by
    have := mul_mem (inv_mem (hL₂Y hl)) hxY
    rwa [inv_mul_cancel_left] at this
  have hYU : ¬ d.Y ≤ d.U := by
    intro hYU
    have h1 := Subgroup.card_le_of_le hYU
    rw [d.cards.1, d.cards.2.1] at h1
    have h2 : 1 < Nat.card K := by have := hK ▸ h.four_le; omega
    nlinarith
  obtain ⟨y, hyY, hyU⟩ := Set.not_subset.1 hYU
  rcases d.mem_M_or_mem_U_of_commute hs hyY (mem_centralizer_iff.1 hsY y hyY).symm with h1 | h1
  · exact mul_mem hl (h.tM_le_yamadaL₂ d hK (mem_sup_left h1))
  · exact absurd h1 hyU

theorem yamada_5_10_3 (h : Setup G L f t) (d : G2Data L K) (hK : Nat.card K = 2 ^ f)
    (h8 : 8 ≤ Nat.card K) :
    yamadaU₁ d t = yamadaD₁ d t ⊓ centralizer (yamadaD₁ d t : Set G) ∧
      yamadaU₁ d t ≤ yamadaF₁ d t := by
  obtain ⟨hU₁D₁, hUU₁, -⟩ := h.yamadaU₁_spec d h8
  obtain ⟨-, hYX, -, hXF, -, hFD, -⟩ := d.inclusions
  have hD₁ := h.yamadaD₁_eq_sup d hK h8
  have hDU₁ := h.D_le_centralizer_yamadaU₁ d hK h8
  have hU₁C₁ : yamadaU₁ d t ≤ yamadaC₁ d t := hU₁D₁.trans (h.yamadaD₁_le_yamadaC₁ d hK)
  have hU₁Z : yamadaU₁ d t ≤ centralizer (yamadaD₁ d t : Set G) := by
    rw [← Subgroup.le_centralizer_iff, hD₁]
    refine sup_le hDU₁ fun x hx => mem_centralizer_iff.2 fun y hy => ?_
    exact h.yamadaU₁_mul_comm d hK h8 hy hx
  have heq : yamadaU₁ d t = yamadaD₁ d t ⊓ centralizer (yamadaD₁ d t : Set G) := by
    refine le_antisymm (le_inf hU₁D₁ hU₁Z) fun z hz => ?_
    obtain ⟨hz₁, hz₂⟩ := Subgroup.mem_inf.1 hz
    have hU₁N : yamadaU₁ d t ≤ normalizer (d.D : Set G) :=
      hU₁C₁.trans (h.yamadaC₁_le_normalizer_D d hK)
    rw [hD₁] at hz₁
    obtain ⟨δ, hδ, x, hx, rfl⟩ := Common.exists_mul_of_le_normalizer hU₁N z hz₁
    have hδZ : δ ∈ d.D ⊓ centralizer (d.D : Set G) := by
      refine ⟨hδ, mem_centralizer_iff.2 fun w hw => ?_⟩
      have hwD₁ : w ∈ yamadaD₁ d t := (le_sup_right : d.D ≤ yamadaD₁ d t) hw
      have h1 := mem_centralizer_iff.1 hz₂ w hwD₁
      have h2 := mem_centralizer_iff.1 (hU₁Z hx) w hwD₁
      calc w * δ = w * (δ * x) * x⁻¹ := by group
        _ = δ * x * w * x⁻¹ := by rw [h1]
        _ = δ * (x * w) * x⁻¹ := by group
        _ = δ * (w * x) * x⁻¹ := by rw [h2]
        _ = δ * w := by group
    rw [(d.yamada_3_12_centers).2.1] at hδZ
    exact mul_mem (hUU₁ hδZ) hx
  refine ⟨heq, fun x hx => ⟨⟨?_, hU₁C₁ hx⟩, hU₁D₁ hx⟩⟩
  refine h.mem_yamadaL₂_of_mem_centralizer_Y d hK ((h.yamada_5_6_1 d hK).2.1 (mem_sup_left
    (hU₁C₁ hx))) (mem_centralizer_iff.2 fun y hy => ?_)
  exact mem_centralizer_iff.1 (hU₁Z hx) y ((le_sup_right : d.D ≤ yamadaD₁ d t)
    (hFD (hXF (hYX hy))))

end Local

end Setup

end CFSG.LocalAnalysis.EvenBN.G2
