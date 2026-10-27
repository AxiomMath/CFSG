module

public import CFSG.LocalAnalysis.EvenBN.G2.LocalYFour

public section

namespace CFSG.LocalAnalysis.EvenBN.G2

open Subgroup CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.ComponentClassification.UnbalancedCatalog CFSG.ComponentClassification.RankTwoExceptional
open CFSG.LocalAnalysis.EvenBN.Common (CosetData)
open scoped commutatorElement Pointwise

@[expose] noncomputable def yamadaB
    {G : Type*} [Group G] {L : Subgroup G} {K : Type} [Field K] (d : G2Data L K) : Subgroup G :=
  (normalClosure (((L ⊓ centralizer (d.J₁ : Set G)).subgroupOf
    (centralizer (d.J₁ : Set G)) : Subgroup _) : Set (centralizer (d.J₁ : Set G)))).map
    (centralizer (d.J₁ : Set G)).subtype

section YamadaB

variable
  {G : Type*} [Group G] {L : Subgroup G} {K : Type} [Field K] (d : G2Data L K)

theorem yamadaB_le_centralizer_J₁ : yamadaB d ≤ centralizer (d.J₁ : Set G) :=
  map_subtype_le _

theorem inf_centralizer_J₁_le_yamadaB : L ⊓ centralizer (d.J₁ : Set G) ≤ yamadaB d := by
  intro x hx
  exact ⟨⟨x, hx.2⟩, subset_normalClosure (show (⟨x, hx.2⟩ : centralizer (d.J₁ : Set G)) ∈
    (L ⊓ centralizer (d.J₁ : Set G)).subgroupOf (centralizer (d.J₁ : Set G)) from hx), rfl⟩

theorem conj_mem_yamadaB {h b : G} (hh : h ∈ centralizer (d.J₁ : Set G)) (hb : b ∈ yamadaB d) :
    h * b * h⁻¹ ∈ yamadaB d := by
  obtain ⟨b', hb', rfl⟩ := hb
  exact ⟨⟨h, hh⟩ * b' * (⟨h, hh⟩)⁻¹, (normalClosure_normal).conj_mem _ hb' _, rfl⟩

theorem conj_mem_yamadaB_of_mem_normalizer {g b : G} (hgL : g ∈ normalizer (L : Set G))
    (hgJ : g ∈ normalizer (d.J₁ : Set G)) (hb : b ∈ yamadaB d) : g * b * g⁻¹ ∈ yamadaB d := by
  set H := centralizer (d.J₁ : Set G) with hH
  have hgH : ∀ x : G, x ∈ H ↔ g * x * g⁻¹ ∈ H := by
    intro x
    simp only [hH, mem_centralizer_iff]
    constructor
    · intro hx j hj
      have hj' : g⁻¹ * j * g ∈ d.J₁ := by
        have := (mem_normalizer_iff.1 (inv_mem hgJ) j).1 hj
        rwa [inv_inv] at this
      have e := hx _ hj'
      calc j * (g * x * g⁻¹) = g * ((g⁻¹ * j * g) * x) * g⁻¹ := by group
        _ = g * (x * (g⁻¹ * j * g)) * g⁻¹ := by rw [e]
        _ = g * x * g⁻¹ * j := by group
    · intro hx j hj
      have hj' : g * j * g⁻¹ ∈ d.J₁ := (mem_normalizer_iff.1 hgJ j).1 hj
      have e := hx _ hj'
      calc j * x = g⁻¹ * ((g * j * g⁻¹) * (g * x * g⁻¹)) * g := by group
        _ = g⁻¹ * ((g * x * g⁻¹) * (g * j * g⁻¹)) * g := by rw [e]
        _ = x * j := by group
  let φ : H ≃* H :=
    { toFun := fun x => ⟨g * x * g⁻¹, (hgH x).1 x.2⟩
      invFun := fun x => ⟨g⁻¹ * x * g, (hgH _).2 (by
        rw [show g * (g⁻¹ * (x : G) * g) * g⁻¹ = x by group]; exact x.2)⟩
      left_inv := fun x => Subtype.ext (by simp [mul_assoc])
      right_inv := fun x => Subtype.ext (by simp [mul_assoc])
      map_mul' := fun x y => Subtype.ext (by simp [mul_assoc]) }
  set S' : Set H := (((L ⊓ centralizer (d.J₁ : Set G)).subgroupOf H : Subgroup H) : Set H)
    with hS'
  have hφS : φ '' S' = S' := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact ⟨(mem_normalizer_iff.1 hgL y).1 hy.1, ((hgH y).1 y.2)⟩
    · intro hx
      refine ⟨φ.symm x, ⟨?_, (φ.symm x).2⟩, φ.apply_symm_apply x⟩
      have := (mem_normalizer_iff.1 (inv_mem hgL) (x : G)).1 hx.1
      rwa [inv_inv] at this
  have hN : (normalClosure S').map φ.toMonoidHom = normalClosure S' := by
    rw [map_normalClosure _ _ φ.surjective]
    congr 1
  obtain ⟨b', hb', rfl⟩ := hb
  have : φ b' ∈ normalClosure S' := by
    rw [← hN]
    exact ⟨b', hb', rfl⟩
  exact ⟨φ b', this, rfl⟩

end YamadaB

structure Setup.DoublingFacts
    {G : Type} [Group G] [Finite G] {L : Subgroup G} {f : ℕ} {t : G} {K : Type} [Field K]
    [CharP K 2] (_h : Setup G L f t) (d : G2Data L K) : Prop where
  le_D₁ : yamadaU₁ d t ≤ yamadaD₁ d t
  U_le : d.U ≤ yamadaU₁ d t
  inf_D : yamadaU₁ d t ⊓ d.D = d.U
  D₁_eq : yamadaD₁ d t = d.D ⊔ yamadaU₁ d t
  inf_centralizer : yamadaU₁ d t ⊓ centralizer ({t} : Set G) = d.U
  card_eq : Nat.card (yamadaU₁ d t) = Nat.card K ^ 2
  mul_comm : ∀ {x y : G}, x ∈ yamadaU₁ d t → y ∈ yamadaU₁ d t → x * y = y * x
  center_eq : yamadaU₁ d t = yamadaD₁ d t ⊓ centralizer (yamadaD₁ d t : Set G)
  le_F₁ : yamadaU₁ d t ≤ yamadaF₁ d t
  le_centralizer_J₁ : yamadaU₁ d t ≤ centralizer (d.J₁ : Set G)
  S_inf_le : d.S ⊓ centralizer (d.J₁ : Set G) ≤ centralizer (yamadaU₁ d t : Set G)
  branch : 8 ≤ Nat.card K ∨ (Nat.card K = 4 ∧ CFSG.IsElementaryAbelian 2 (yamadaU₁ d t) ∧
    yamadaD₁ d t ⊓ centralizer (d.J₁ : Set G) ≤ yamadaB d ∧
    ∀ P : Subgroup G, P ≤ yamadaB d → IsPGroup 2 P →
      yamadaD₁ d t ⊓ centralizer (d.J₁ : Set G) ≤ P → ElemModulo (yamadaU₁ d t) P)

namespace Setup

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {f : ℕ} {t : G}

section Doubling

variable
  {K : Type} [Field K] [Finite K]
  [CharP K 2]

theorem doublingFacts_of_eight (h : Setup G L f t) (d : G2Data L K) (hK : Nat.card K = 2 ^ f)
    (h8 : 8 ≤ Nat.card K) : h.DoublingFacts d := by
  obtain ⟨hU₁D₁, hUU₁, hU₁D⟩ := h.yamadaU₁_spec d h8
  obtain ⟨hD₁, hinf, hcard⟩ := h.yamada_5_10_1 d hK h8
  obtain ⟨hZ, hF₁⟩ := h.yamada_5_10_3 d hK h8
  refine ⟨hU₁D₁, hUU₁, hU₁D, hD₁, hinf, hcard, fun hx hy => h.yamadaU₁_mul_comm d hK h8 hx hy,
    hZ, hF₁, ?_, ?_, Or.inl h8⟩
  · rw [yamadaU₁_eq d t h8]
    exact inf_le_right
  · rw [d.S_inf_centralizer_J₁ h8]
    intro u hu
    exact mem_centralizer_iff.2 fun x hx => h.yamadaU₁_mul_comm d hK h8 hx (hUU₁ hu)

namespace DoublingFacts

variable {h : Setup G L f t} {d : G2Data L K}

omit [Finite K] in
theorem spec (hD : h.DoublingFacts d) :
    yamadaU₁ d t ≤ yamadaD₁ d t ∧ d.U ≤ yamadaU₁ d t ∧ yamadaU₁ d t ⊓ d.D = d.U :=
  ⟨hD.le_D₁, hD.U_le, hD.inf_D⟩

omit [Finite K] in
theorem yamada_5_10_1 (hD : h.DoublingFacts d) :
    yamadaD₁ d t = d.D ⊔ yamadaU₁ d t ∧ yamadaU₁ d t ⊓ centralizer ({t} : Set G) = d.U ∧
      Nat.card (yamadaU₁ d t) = Nat.card K ^ 2 :=
  ⟨hD.D₁_eq, hD.inf_centralizer, hD.card_eq⟩

omit [Finite K] in
theorem yamada_5_10_3 (hD : h.DoublingFacts d) :
    yamadaU₁ d t = yamadaD₁ d t ⊓ centralizer (yamadaD₁ d t : Set G) ∧
      yamadaU₁ d t ≤ yamadaF₁ d t :=
  ⟨hD.center_eq, hD.le_F₁⟩

theorem le_C₁ (hD : h.DoublingFacts d) (hK : Nat.card K = 2 ^ f) :
    yamadaU₁ d t ≤ yamadaC₁ d t :=
  hD.le_D₁.trans (h.yamadaD₁_le_yamadaC₁ d hK)

omit [Finite K] in
theorem D_le_centralizer (hD : h.DoublingFacts d) :
    d.D ≤ centralizer (yamadaU₁ d t : Set G) := by
  intro x hx
  rw [mem_centralizer_iff]
  intro u hu
  rw [hD.center_eq] at hu
  exact (mem_centralizer_iff.1 (Subgroup.mem_inf.1 hu).2 x
    ((le_sup_right : d.D ≤ yamadaD₁ d t) hx)).symm

theorem yamadaC₁_le_normalizer (hD : h.DoublingFacts d) (hK : Nat.card K = 2 ^ f) :
    yamadaC₁ d t ≤ normalizer (yamadaU₁ d t : Set G) := by
  refine le_normalizer_of_conj_mem fun c hc x hx => ?_
  have h1 := ((h.elemModulo_U_yamadaC₁ d hK) _ hc _ (hD.le_C₁ hK hx)).2
  rw [commutatorElement_def] at h1
  rw [show c * x * c⁻¹ = c * x * c⁻¹ * x⁻¹ * x by group]
  exact mul_mem (hD.U_le h1) hx

theorem inf_normalizer_U_le_normalizer (hD : h.DoublingFacts d) (hK : Nat.card K = 2 ^ f) :
    L ⊓ normalizer (d.U : Set G) ≤ normalizer (yamadaU₁ d t : Set G) := by
  intro n hn
  have hnD₁ := h.inf_normalizer_U_le_normalizer_yamadaD₁ d hK hn
  rw [hD.center_eq]
  refine mem_normalizer_of_conj_mem fun x hx => ⟨(mem_normalizer_iff.1 hnD₁ x).1 hx.1,
    mem_centralizer_iff.2 fun y hy => ?_⟩
  have hy' : n⁻¹ * y * n ∈ yamadaD₁ d t := by
    have := (mem_normalizer_iff.1 (inv_mem hnD₁) y).1 hy
    rwa [inv_inv] at this
  have e := mem_centralizer_iff.1 hx.2 _ hy'
  calc y * (n * x * n⁻¹) = n * ((n⁻¹ * y * n) * x) * n⁻¹ := by group
    _ = n * (x * (n⁻¹ * y * n)) * n⁻¹ := by rw [e]
    _ = n * x * n⁻¹ * y := by group

theorem conj_mem (hD : h.DoublingFacts d) (hK : Nat.card K = 2 ^ f) {j x : G} (hj : j ∈ d.J₃)
    (hx : x ∈ yamadaU₁ d t) : j * x * j⁻¹ ∈ yamadaU₁ d t :=
  (mem_normalizer_iff.1 (hD.inf_normalizer_U_le_normalizer hK (d.J₃_le_inf_normalizer_U hj))
    x).1 hx

theorem exists_mem_crossed (hD : h.DoublingFacts d) (hK : Nat.card K = 2 ^ f) {u : G}
    (hu : u ∈ d.U) : ∃ x ∈ yamadaU₁ d t, x⁻¹ * t * x * t = u := by
  obtain ⟨-, -, hC₁tr, -⟩ := h.two_core_C₁ d hK
  have hc₁ := h.cosetData_tU d hK
  obtain ⟨c, hc, hct⟩ := hC₁tr u hu
  have htN : zpowers t ≤ normalizer (yamadaD₁ d t : Set G) :=
    (zpowers_le).2 (h.yamadaC₁_le_normalizer_yamadaD₁ d hK (h.t_mem_yamadaC₁ d hK))
  have hU₁N : yamadaU₁ d t ≤ normalizer (d.D : Set G) :=
    (hD.le_C₁ hK).trans (h.yamadaC₁_le_normalizer_D d hK)
  rw [(h.yamada_5_8_1 d hK).2.1, sup_comm] at hc
  obtain ⟨τ, hτ, d₁, hd₁, rfl⟩ := Common.exists_mul_of_le_normalizer' htN c hc
  rw [hD.D₁_eq] at hd₁
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

theorem exists_coords (hD : h.DoublingFacts d) (hK : Nat.card K = 2 ^ f) :
    ∃ ν : G → K, (∀ {u u' : G}, u ∈ d.U → u' ∈ d.U → ν (u * u') = ν u + ν u') ∧
      (∀ {u u' : G}, u ∈ d.U → u' ∈ d.U → ν u = ν u' → u = u') ∧ (∀ z : K, ∃ u ∈ d.U, ν u = z) ∧
      (∀ a : K, a ≠ 0 → ∃ j ∈ d.J₃, ∀ u ∈ d.U, ν (j * u * j⁻¹) = a * ν u) ∧
      (∀ {x : G}, x ∈ yamadaU₁ d t → x⁻¹ * t * x * t ∈ d.U) ∧
      (∀ {x : G}, x ∈ yamadaU₁ d t → (ν (x⁻¹ * t * x * t) = ν 1 ↔ x ∈ d.U)) := by
  obtain ⟨ι, hι⟩ := d.exists_mulEquiv_U
  have hc₁ := h.cosetData_tU d hK
  have hU₁C₁ := hD.le_C₁ hK
  have hinf := hD.inf_centralizer
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

theorem le_centralizer_of (hD : h.DoublingFacts d) (hK : Nat.card K = 2 ^ f) {P : Subgroup G}
    (hPS : P ≤ d.S) (hPN : P ≤ normalizer (yamadaU₁ d t : Set G))
    (hJP : d.J₁ ≤ normalizer (P : Set G))
    (hcomm : ∀ {p u : G}, p ∈ P → u ∈ yamadaU₁ d t → ⁅p, u⁆ ∈ d.U) :
    P ≤ centralizer (yamadaU₁ d t : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hcenS : ∀ {u g : G}, u ∈ d.U → g ∈ d.S → u * g = g * u := fun {u g} hu hg => by
    rw [← (d.yamada_3_12_centers).1] at hu
    exact (mem_centralizer_iff.1 hu.2 g hg).symm
  have hJ₁U₁ : d.J₁ ≤ centralizer (yamadaU₁ d t : Set G) := by
    rw [← Subgroup.le_centralizer_iff]
    exact hD.le_centralizer_J₁
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
  exact mul_mem (hD.S_inf_le ⟨hPS (Subgroup.mem_inf.1 hc).1, (Subgroup.mem_inf.1 hc).2⟩)
    (Subgroup.mem_inf.1 hn).2

end DoublingFacts

end Doubling

end Setup

end CFSG.LocalAnalysis.EvenBN.G2
