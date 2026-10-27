module

public import CFSG.LocalAnalysis.EvenBN.G2.LocalYTwo
public import CFSG.LocalAnalysis.EvenBN.Common.CoprimeQuotient

public section

namespace CFSG.LocalAnalysis.EvenBN.G2

open Subgroup CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.ComponentClassification.UnbalancedCatalog CFSG.ComponentClassification.RankTwoExceptional
open CFSG.LocalAnalysis.EvenBN.Common (CosetData)
open scoped commutatorElement Pointwise

section Defs

variable
  {G : Type*} [Group G] {L : Subgroup G} {K : Type} [Field K] [CharP K 2]

@[expose] noncomputable def yamadaL₁ (d : G2Data L K) (t : G) : Subgroup G :=
  yamadaL₂ d t ⊓ yamadaR₁ d t

@[expose] noncomputable def yamadaE₁ (d : G2Data L K) (t : G) : Subgroup G :=
  yamadaL₂ d t ⊓ yamadaC₁ d t

@[expose] noncomputable def yamadaD₁ (d : G2Data L K) (t : G) : Subgroup G :=
  ⁅yamadaC₁ d t, d.J₃⁆ ⊔ d.D

@[expose] noncomputable def yamadaS₁ (d : G2Data L K) (t : G) : Subgroup G :=
  d.S ⊔ yamadaD₁ d t

@[expose] noncomputable def yamadaM₁ (d : G2Data L K) (t : G) : Subgroup G :=
  yamadaL₁ d t ⊓ yamadaS₁ d t

@[expose] noncomputable def yamadaF₁ (d : G2Data L K) (t : G) : Subgroup G :=
  yamadaE₁ d t ⊓ yamadaD₁ d t

end Defs

section Generic

variable {G : Type*} [Group G]

theorem map_conj_eq_of_mem_normalizer {H : Subgroup G} {g : G}
    (hg : g ∈ normalizer (H : Set G)) : H.map (MulAut.conj g).toMonoidHom = H := by
  ext y
  rw [mem_map_conj_iff]
  have := (mem_normalizer_iff.1 (inv_mem hg) y)
  rw [inv_inv] at this
  exact this.symm

theorem mem_normalizer_of_map_conj_eq {H : Subgroup G} {g : G}
    (h : H.map (MulAut.conj g).toMonoidHom = H) : g ∈ normalizer (H : Set G) := by
  rw [mem_normalizer_iff]
  intro y
  constructor
  · intro hy
    rw [← h]
    exact ⟨y, hy, rfl⟩
  · intro hy
    rw [← h, mem_map_conj_iff] at hy
    simpa [mul_assoc] using hy

theorem map_conj_mul (H : Subgroup G) (g g' : G) :
    H.map (MulAut.conj (g * g')).toMonoidHom =
      (H.map (MulAut.conj g').toMonoidHom).map (MulAut.conj g).toMonoidHom := by
  rw [Subgroup.map_map]
  congr 1
  ext x
  simp [mul_assoc]

theorem odd_two_pow_sub_one {f : ℕ} (hf : 1 ≤ f) : Odd (2 ^ f - 1) := by
  obtain ⟨k, hk⟩ : 2 ∣ 2 ^ f := dvd_pow_self 2 (by omega)
  have h1 : 1 ≤ 2 ^ f := Nat.one_le_two_pow
  generalize 2 ^ f = n at *
  exact ⟨k - 1, by omega⟩

end Generic

namespace Model

variable
  {K : Type} [Field K] [CharP K 2]

theorem wb_conj_U (x : K) :
    wb K * pinnedX .G2 K g2c x * (wb K)⁻¹ = pinnedX .G2 K g2b x := by
  rw [wb, pinnedX_c_eq_g2N, pinnedX_b_eq_g2N, weylElt_a_conj_g2N]
  refine g2N_eq_g2N rfl rfl rfl rfl ?_ ?_ <;> ring

end Model

namespace G2Data

variable {G : Type*} [Group G] {L : Subgroup G} {K : Type} [Field K] (d : G2Data L K)

section Light


theorem wb_mem_leviB : d.wb ∈ d.leviB :=
  d.emb_mem_image (weylElt_mem_g2RankOne g2ia 1)

theorem card_J₃ [Finite K] : Nat.card d.J₃ = Nat.card K - 1 := by
  rw [G2Data.J₃, d.card_image (Model.torusFix_le_adjointGroup K g2r)]
  exact (Model.yamada_3_9_1 (K := K) 2).2

end Light

variable
  [Finite K] [CharP K 2]

theorem wb_mem_normalizer : d.wb ∈ L ⊓ normalizer (d.Y : Set G) ∧
    d.wb ∈ normalizer (d.W : Set G) ∧ d.wb ∈ normalizer (d.M : Set G) := by
  obtain ⟨h1, h2, h3, -, -⟩ := d.yamada_3_13_3_G
  have hw : d.wb ∈ d.M ⊔ (d.leviB ⊔ d.J₄) := mem_sup_right (mem_sup_left d.wb_mem_leviB)
  refine ⟨h1 ▸ hw, ?_, ?_⟩
  · rw [← h2] at hw
    exact hw.2
  · rw [← h3] at hw
    exact hw.2

omit [Finite K] in
theorem exists_wb_conj_mul {y : G} (hy : y ∈ d.Y) :
    ∃ u ∈ d.U, ∃ v ∈ d.U, y = d.wb * v * d.wb⁻¹ * u := by
  obtain ⟨g, hg, rfl⟩ := d.mem_image.1 hy
  obtain ⟨e, f, hef⟩ := Model.mem_Y.1 hg
  refine ⟨d.emb ⟨pinnedX .G2 K g2c f, pinnedX_mem_adjointGroup g2c f⟩,
    d.emb_mem_image (mem_rootSubgroup.2 ⟨f, rfl⟩),
    d.emb ⟨pinnedX .G2 K g2c e, pinnedX_mem_adjointGroup g2c e⟩,
    d.emb_mem_image (mem_rootSubgroup.2 ⟨e, rfl⟩), ?_⟩
  rw [wb, ← map_inv, ← map_mul, ← map_mul, ← map_mul]
  refine congrArg d.emb (Subtype.ext ?_)
  change (g : ModGL .G2 K) = Model.wb K * pinnedX .G2 K g2c e * (Model.wb K)⁻¹ *
    pinnedX .G2 K g2c f
  rw [Model.wb_conj_U, hef, pinnedX_b_eq_g2N, pinnedX_c_eq_g2N, g2N_mul_coords]
  refine g2N_eq_g2N ?_ ?_ ?_ ?_ ?_ ?_ <;> ring

omit [Finite K] in
theorem eq_one_of_wb_conj_mem_U {v : G} (hv : v ∈ d.U) (hv' : d.wb * v * d.wb⁻¹ ∈ d.U) :
    v = 1 := by
  obtain ⟨g, hg, rfl⟩ := d.mem_image.1 hv
  obtain ⟨x, hx⟩ := mem_rootSubgroup.1 hg
  rw [wb, ← map_inv, ← map_mul, ← map_mul] at hv'
  have h1 : Model.wb K * (g : ModGL .G2 K) * (Model.wb K)⁻¹ ∈ Model.U K := d.emb_mem_image_iff.1 hv'
  rw [← hx, Model.wb_conj_U, pinnedX_b_eq_g2N, Model.g2N_mem_U_iff] at h1
  rw [← map_one d.emb]
  refine congrArg d.emb (Subtype.ext ?_)
  rw [← hx, h1.2.2.2.2, pinnedX_zero]
  rfl

omit [Finite K] in
theorem W_ne_X : d.W ≠ d.X := by
  intro hWX
  obtain ⟨hvW, hvY, -⟩ := d.xv_xc_spec
  refine hvY ?_
  rw [← (d.yamada_defs).2.2.2.2.2.2.1, ← hWX, inf_idem]
  exact hvW

theorem map_conj_mem_W_X [Finite G] {c : G} (hc : c ∈ normalizer (d.F : Set G)) {E : Subgroup G}
    (hE : E = d.W ∨ E = d.X) :
    E.map (MulAut.conj c).toMonoidHom = d.W ∨ E.map (MulAut.conj c).toMonoidHom = d.X := by
  obtain ⟨-, -, -, hXF, hWF, -⟩ := d.inclusions
  have hEF : E ≤ d.F := by
    rcases hE with rfl | rfl
    exacts [hWF, hXF]
  have hEe : CFSG.IsElementaryAbelian 2 E := by
    rcases hE with rfl | rfl
    exacts [d.isElementaryAbelian.2.2.2, d.isElementaryAbelian.2.2.1]
  have hcard : Nat.card E = Nat.card K ^ 3 := by
    rcases hE with rfl | rfl
    exacts [d.cards.2.2.2.1, d.cards.2.2.1]
  have hEcF : E.map (MulAut.conj c).toMonoidHom ≤ d.F := by
    rw [← map_conj_eq_of_mem_normalizer hc]
    exact map_mono hEF
  rcases d.le_W_or_le_X_of_le_F hEcF (isElementaryAbelian_map_conj hEe c) with h1 | h1
  · exact Or.inl (Subgroup.eq_of_le_of_card_ge h1 (by
      rw [card_map_conj, hcard, d.cards.2.2.2.1]))
  · exact Or.inr (Subgroup.eq_of_le_of_card_ge h1 (by
      rw [card_map_conj, hcard, d.cards.2.2.1]))

theorem J₃_le_inf_normalizer_U : d.J₃ ≤ L ⊓ normalizer (d.U : Set G) := by
  rw [(d.yamada_3_13_2_G).1]
  exact le_sup_right.trans le_sup_right

end G2Data

namespace Setup

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {f : ℕ} {t : G}

section Light

variable {K : Type} [Field K]

theorem inf_normalizer_U_le_normalizer_yamadaC₁ (h : Setup G L f t) (d : G2Data L K) :
    L ⊓ normalizer (d.U : Set G) ≤ normalizer (yamadaC₁ d t : Set G) := fun _ hn =>
  le_normalizer_yamadaC₁ d t (h.centralizer_inf_normalizer_U_le d ⟨h.L_le_centralizer hn.1, hn.2⟩)

end Light

section Local

variable
  {K : Type} [Field K] [Finite K]
  [CharP K 2]

theorem t_mem_yamadaC₁ (h : Setup G L f t) (d : G2Data L K) (hK : Nat.card K = 2 ^ f) :
    t ∈ yamadaC₁ d t :=
  h.tD_le_yamadaC₁ d hK (mem_sup_right (mem_zpowers t))

theorem yamadaC₁_le_normalizer_D (h : Setup G L f t) (d : G2Data L K) (hK : Nat.card K = 2 ^ f) :
    yamadaC₁ d t ≤ normalizer (d.D : Set G) :=
  (yamadaC₁_le d t).trans (h.yamada_5_3_1 d hK).2.2.2.1

theorem elemModulo_D_yamadaC₁ (h : Setup G L f t) (d : G2Data L K) (hK : Nat.card K = 2 ^ f) :
    ElemModulo d.D (yamadaC₁ d t) := by
  obtain ⟨hUY, hYX, -, hXF, -, hFD, -⟩ := d.inclusions
  refine elemModulo_of_mul_self_mem (h.yamadaC₁_le_normalizer_D d hK) fun x hx => ?_
  have h1 : x ^ 2 ∈ closure {z | ∃ g ∈ yamadaC₁ d t, z = g ^ 2} := subset_closure ⟨x, hx, rfl⟩
  rw [h.yamada_5_6_4 d hK, sq] at h1
  exact hFD (hXF (hYX (hUY h1)))

theorem yamadaD₁_le_yamadaC₁ (h : Setup G L f t) (d : G2Data L K) (hK : Nat.card K = 2 ^ f) :
    yamadaD₁ d t ≤ yamadaC₁ d t := by
  refine sup_le (commutator_le.2 fun c hc j hj => ?_) (le_sup_left.trans (h.tD_le_yamadaC₁ d hK))
  rw [commutatorElement_def, show c * j * c⁻¹ * j⁻¹ = c * (j * c⁻¹ * j⁻¹) by group]
  exact mul_mem hc ((mem_normalizer_iff.1 (h.inf_normalizer_U_le_normalizer_yamadaC₁ d
    (d.J₃_le_inf_normalizer_U hj)) _).1 (inv_mem hc))

theorem yamadaC₁_le_normalizer_yamadaD₁ (h : Setup G L f t) (d : G2Data L K)
    (hK : Nat.card K = 2 ^ f) : yamadaC₁ d t ≤ normalizer (yamadaD₁ d t : Set G) := by
  refine le_normalizer_of_conj_mem fun c hc x hx => ?_
  have hxC := h.yamadaD₁_le_yamadaC₁ d hK hx
  have h1 := ((h.elemModulo_D_yamadaC₁ d hK) c hc x hxC).2
  rw [commutatorElement_def] at h1
  rw [show c * x * c⁻¹ = c * x * c⁻¹ * x⁻¹ * x by group]
  exact mul_mem (mem_sup_right h1) hx

theorem inf_normalizer_U_le_normalizer_yamadaD₁ (h : Setup G L f t) (d : G2Data L K)
    (hK : Nat.card K = 2 ^ f) :
    L ⊓ normalizer (d.U : Set G) ≤ normalizer (yamadaD₁ d t : Set G) := by
  obtain ⟨hNU, hND, hJA, -⟩ := d.yamada_3_13_2_G
  have hNC₁ := h.inf_normalizer_U_le_normalizer_yamadaC₁ d
  have key : ∀ n : G, n ∈ L ⊓ normalizer (d.U : Set G) → n ∈ normalizer (d.J₃ : Set G) →
      n ∈ normalizer (yamadaD₁ d t : Set G) := fun n hn hnJ => by
    have hnD : n ∈ L ⊓ normalizer (d.D : Set G) := by
      rw [hND, ← hNU]
      exact hn
    have hcomm : n ∈ normalizer ((⁅yamadaC₁ d t, d.J₃⁆ : Subgroup G) : Set G) := by
      refine mem_normalizer_of_map_conj_eq ?_
      rw [map_commutator, map_conj_eq_of_mem_normalizer (hNC₁ hn),
        map_conj_eq_of_mem_normalizer hnJ]
    exact Common.mem_normalizer_sup hcomm hnD.2
  have hJ := d.J₃_le_inf_normalizer_U
  rw [hNU]
  refine sup_le ((le_sup_left.trans (h.tD_le_yamadaC₁ d hK)).trans
    (h.yamadaC₁_le_normalizer_yamadaD₁ d hK))
    (sup_le (fun a ha => key a ?_ ?_) fun j hj => key j (hJ hj) (le_normalizer hj))
  · rw [hNU]
    exact mem_sup_right (mem_sup_left ha)
  · refine Subgroup.centralizer_le_normalizer _ ?_
    rw [← Subgroup.le_centralizer_iff] at hJA
    exact hJA ha

theorem t_not_mem_yamadaD₁ (h : Setup G L f t) (d : G2Data L K) (hK : Nat.card K = 2 ^ f) :
    t ∉ yamadaD₁ d t := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hNU, hND, -, -⟩ := d.yamada_3_13_2_G
  have hJ := d.J₃_le_inf_normalizer_U
  have hNC₁ := h.inf_normalizer_U_le_normalizer_yamadaC₁ d
  intro htD
  have hcop : (Nat.card d.J₃).Coprime (Nat.card (yamadaC₁ d t)) := by
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.1 (LieType.BorelTits.pCoreOf_isPGroup 2
      (normalizer ((d.U ⊔ zpowers t : Subgroup G) : Set G)))
    have hk' : Nat.card (yamadaC₁ d t) = 2 ^ k := hk
    rw [hk', d.card_J₃, hK]
    exact (odd_two_pow_sub_one (by have := h.two_le; omega)).coprime_two_right.pow_right k
  have hcomm : ∀ y ∈ yamadaC₁ d t, ∀ y' ∈ yamadaC₁ d t, y * y' * y⁻¹ * y'⁻¹ ∈ d.D :=
    fun y hy y' hy' => by
      have := ((h.elemModulo_D_yamadaC₁ d hK) y hy y' hy').2
      rwa [commutatorElement_def] at this
  have hJD : d.J₃ ≤ normalizer (d.D : Set G) := fun j hj => by
    have : j ∈ L ⊓ normalizer (d.D : Set G) := by
      rw [hND, ← hNU]
      exact hJ hj
    exact this.2
  have htD' : t ∈ ⁅d.J₃, yamadaC₁ d t⁆ ⊔ d.D := by
    rw [commutator_comm]
    exact htD
  refine h.t_not_mem_L (d.image_le _ (Common.mem_of_mem_commutator_sup_of_fixed
    (le_sup_left.trans (h.tD_le_yamadaC₁ d hK)) hcomm (fun j hj => hNC₁ (hJ hj)) hJD hcop htD'
    fun a ha => ?_))
  rw [mem_centralizer_singleton_iff.1 (h.L_le_centralizer (hJ ha).1), mul_inv_cancel_right,
    mul_inv_cancel]
  exact one_mem _

theorem yamadaC₁_le_yamadaD₁_sup (h : Setup G L f t) (d : G2Data L K) (hK : Nat.card K = 2 ^ f) :
    yamadaC₁ d t ≤ yamadaD₁ d t ⊔ zpowers t := by
  have hK4 : 4 ≤ Nat.card K := hK ▸ h.four_le
  obtain ⟨hC₁U, hC₁t, hC₁tr, -⟩ := h.two_core_C₁ d hK
  have hc₁ := h.cosetData_tU d hK
  have hD₁C₁ := h.yamadaD₁_le_yamadaC₁ d hK
  have hNC₁ := h.inf_normalizer_U_le_normalizer_yamadaC₁ d
  have hJ := d.J₃_le_inf_normalizer_U
  intro c hc
  obtain ⟨ι, hι⟩ := d.exists_mulEquiv_U
  have hcV : c ∈ normalizer ((d.U ⊔ zpowers t : Subgroup G) : Set G) ⊓
      centralizer (d.U : Set G) := ⟨yamadaC₁_le d t hc, hC₁U hc⟩
  obtain ⟨y, hy⟩ := ι.surjective ⟨_, hc₁.crossed_mem_of_mem hcV⟩
  set x := Multiplicative.toAdd y with hxdef
  have hcx : c⁻¹ * t * c * t = ι (Multiplicative.ofAdd x) := by
    rw [hxdef, ofAdd_toAdd, hy]
  obtain ⟨a, ha0, ha1⟩ := exists_ne_zero_ne_one hK4
  have ha1' : 1 + a ≠ 0 := fun h0 => ha1 ((CharTwo.add_eq_zero.1 h0).symm)
  obtain ⟨e, he, hex⟩ := d.exists_mem_J₃_scalar ι hι ha0
  obtain ⟨c', hc', hc't⟩ := hC₁tr _ (ι (Multiplicative.ofAdd ((1 + a)⁻¹ * x))).2
  have hc'V : c' ∈ normalizer ((d.U ⊔ zpowers t : Subgroup G) : Set G) ⊓
      centralizer (d.U : Set G) := ⟨yamadaC₁_le d t hc', hC₁U hc'⟩
  have hc'x : c'⁻¹ * t * c' * t = ι (Multiplicative.ofAdd ((1 + a)⁻¹ * x)) :=
    (hc₁.crossed_eq_iff (ι _).2).2 hc't
  have heC₁ : e * c'⁻¹ * e⁻¹ ∈ yamadaC₁ d t :=
    (mem_normalizer_iff.1 (hNC₁ (hJ he)) _).1 (inv_mem hc')
  have heV : e * c'⁻¹ * e⁻¹ ∈ normalizer ((d.U ⊔ zpowers t : Subgroup G) : Set G) ⊓
      centralizer (d.U : Set G) := ⟨yamadaC₁_le d t heC₁, hC₁U heC₁⟩
  have het : e * t = t * e := mem_centralizer_singleton_iff.1 (h.L_le_centralizer (hJ he).1)
  set q := c' * (e * c'⁻¹ * e⁻¹) with hqdef
  have hk : q⁻¹ * t * q * t = c⁻¹ * t * c * t := by
    rw [hqdef, hc₁.crossed_mul_of_mem hc'V heV,
      CFSG.EvenSmallLie.UnitarySix.YamadaD.crossed_conj het, hc₁.crossed_inv_of_mem hc'V, hc'x,
      hcx, inv_eq_of_mul_eq_one_right (hc₁.mul_self_of_mem (ι _).2), hex, ← Subgroup.coe_mul,
      ← map_mul, ← ofAdd_add]
    congr 3
    rw [show (1 + a)⁻¹ * x + a * ((1 + a)⁻¹ * x) = (1 + a) * (1 + a)⁻¹ * x by ring,
      mul_inv_cancel₀ ha1', one_mul]
  have hw := Common.mul_inv_mem_centralizer_of_conj_eq (mul_right_cancel hk).symm
  have hqD₁ : q ∈ yamadaD₁ d t := by
    refine mem_sup_left ?_
    rw [hqdef, show c' * (e * c'⁻¹ * e⁻¹) = ⁅c', e⁆ by rw [commutatorElement_def]; group]
    exact commutator_mem_commutator hc' he
  have hwB : q * c⁻¹ ∈ d.D ⊔ zpowers t := by
    rw [← hC₁t]
    exact Subgroup.mem_inf.2 ⟨mul_mem (hD₁C₁ hqD₁) (inv_mem hc), hw⟩
  have hDD₁ : d.D ≤ yamadaD₁ d t := le_sup_right
  rw [show c = (q * c⁻¹)⁻¹ * q by group]
  exact mul_mem (inv_mem (sup_le_sup_right hDD₁ _ hwB)) (mem_sup_left hqD₁)

theorem yamada_5_8_1 (h : Setup G L f t) (d : G2Data L K) (hK : Nat.card K = 2 ^ f) :
    L ⊓ normalizer (d.U : Set G) ≤ normalizer (yamadaD₁ d t : Set G) ∧
      yamadaC₁ d t = yamadaD₁ d t ⊔ zpowers t ∧ yamadaD₁ d t < yamadaC₁ d t :=
  ⟨h.inf_normalizer_U_le_normalizer_yamadaD₁ d hK, le_antisymm (h.yamadaC₁_le_yamadaD₁_sup d hK)
    (sup_le (h.yamadaD₁_le_yamadaC₁ d hK) ((zpowers_le).2 (h.t_mem_yamadaC₁ d hK))),
    lt_of_le_of_ne (h.yamadaD₁_le_yamadaC₁ d hK) fun e =>
      h.t_not_mem_yamadaD₁ d hK (e ▸ h.t_mem_yamadaC₁ d hK)⟩

omit [Finite K] in
theorem mem_tF_of_mem_tD (h : Setup G L f t) (d : G2Data L K) {x : G}
    (hD : x ∈ d.D ⊔ zpowers t) (hM : x ∈ d.M ⊔ zpowers t) : x ∈ d.F ⊔ zpowers t := by
  have hnt : ∀ {a : G}, a ∈ L → t * a ∈ L → False := fun ha hta => h.t_not_mem_L (by
    have := mul_mem hta (inv_mem ha)
    rwa [mul_inv_cancel_right] at this)
  have hDM : ∀ {x : G}, x ∈ d.D → x ∈ d.M → x ∈ d.F := fun h1 h2 => by
    rw [← (d.yamada_defs).2.2.2.2.2.2.2.1]
    exact ⟨h1, h2⟩
  rcases (h.mem_sup_zpowers_iff (d.image_le _)).1 hD with h2 | h2 <;>
    rcases (h.mem_sup_zpowers_iff (d.image_le _)).1 hM with h3 | h3
  · exact mem_sup_left (hDM h2 h3)
  · exact (hnt (d.image_le _ h2) (d.image_le _ h3)).elim
  · exact (hnt (d.image_le _ h3) (d.image_le _ h2)).elim
  · rw [show x = t * (t * x) by rw [← mul_assoc, h.t_mul_t, one_mul]]
    exact mul_mem (mem_sup_right (mem_zpowers t)) (mem_sup_left (hDM h2 h3))

omit [Finite K] in
theorem S_le_inf_normalizer_U (_h : Setup G L f t) (d : G2Data L K) :
    d.S ≤ L ⊓ normalizer (d.U : Set G) :=
  le_inf (d.image_le _) d.S_le_normalizers.1

theorem yamadaS₁_spec (h : Setup G L f t) (d : G2Data L K) (hK : Nat.card K = 2 ^ f) :
    yamadaS₁ d t ≤ yamadaR₁ d t ∧ yamadaR₁ d t = yamadaS₁ d t ⊔ zpowers t ∧
      yamadaR₁ d t ≤ normalizer (yamadaS₁ d t : Set G) ∧ t ∉ yamadaS₁ d t := by
  obtain ⟨-, hC₁t, -, -⟩ := h.two_core_C₁ d hK
  have hD₁C₁ := h.yamadaD₁_le_yamadaC₁ d hK
  have hC₁D₁ := (h.yamada_5_8_1 d hK).2.1
  have htC₁ := h.t_mem_yamadaC₁ d hK
  have hSD₁ : d.S ≤ normalizer (yamadaD₁ d t : Set G) :=
    (h.S_le_inf_normalizer_U d).trans (h.inf_normalizer_U_le_normalizer_yamadaD₁ d hK)
  have hS₁R₁ : yamadaS₁ d t ≤ yamadaR₁ d t := sup_le le_sup_right (hD₁C₁.trans le_sup_left)
  have hR₁S₁ : yamadaR₁ d t = yamadaS₁ d t ⊔ zpowers t := by
    refine le_antisymm (sup_le ?_ (le_sup_left.trans le_sup_left)) (sup_le hS₁R₁
      ((zpowers_le).2 (mem_sup_left htC₁)))
    rw [hC₁D₁]
    exact sup_le_sup_right le_sup_right _
  have htN : t ∈ normalizer (yamadaS₁ d t : Set G) :=
    Common.mem_normalizer_sup (Subgroup.centralizer_le_normalizer _ (mem_centralizer_iff.2
      fun s hs => mem_centralizer_singleton_iff.1 (h.S_le_centralizer d hs)))
      (h.yamadaC₁_le_normalizer_yamadaD₁ d hK htC₁)
  refine ⟨hS₁R₁, hR₁S₁, ?_, fun htS => ?_⟩
  · rw [hR₁S₁]
    exact sup_le le_normalizer ((zpowers_le).2 htN)
  · obtain ⟨s, hs, e, he, hse⟩ := Common.exists_mul_of_le_normalizer' hSD₁ t htS
    have hsC₁ : s ∈ yamadaC₁ d t := by
      rw [show s = t * e⁻¹ by rw [hse, mul_inv_cancel_right]]
      exact mul_mem htC₁ (inv_mem (hD₁C₁ he))
    have hsD : s ∈ d.D := h.mem_D_of_mem_sup d (by
      rw [← hC₁t]
      exact ⟨hsC₁, h.S_le_centralizer d hs⟩) (d.image_le _ hs)
    have hse' : s * e ∈ yamadaD₁ d t := mul_mem (mem_sup_right hsD) he
    rw [← hse] at hse'
    exact h.t_not_mem_yamadaD₁ d hK hse'

theorem yamada_5_8_2 (h : Setup G L f t) (d : G2Data L K) (hK : Nat.card K = 2 ^ f) :
    closure {z | ∃ g ∈ yamadaR₁ d t, z = g ^ 2} = d.F ∧
      closure {z | ∃ g ∈ yamadaS₁ d t, z = g ^ 2} = d.F := by
  have hK4 : 4 ≤ Nat.card K := hK ▸ h.four_le
  obtain ⟨hC₁U, hC₁t, -, -⟩ := h.two_core_C₁ d hK
  obtain ⟨-, hL₂t, -, -⟩ := h.two_core_L₂ d hK
  obtain ⟨-, -, -, -, -, hFD, -, -, -, -⟩ := d.inclusions
  obtain ⟨hS₁R₁, hR₁S₁, hR₁N, htS₁⟩ := h.yamadaS₁_spec d hK
  have hc₁ := h.cosetData_tU d hK
  have hSU : d.S ≤ centralizer (d.U : Set G) := by
    rw [Subgroup.le_centralizer_iff, ← (d.yamada_3_12_centers).1]
    exact inf_le_right
  have hSC₁ : d.S ≤ normalizer (yamadaC₁ d t : Set G) :=
    (h.S_le_inf_normalizer_U d).trans (h.inf_normalizer_U_le_normalizer_yamadaC₁ d)
  have hFS : d.F = closure {z | ∃ g ∈ d.S, z = g ^ 2} := ((d.yamada_3_12_mho hK4).2.2).symm
  have hsq : ∀ r ∈ yamadaR₁ d t, r ^ 2 ∈ d.F := by
    intro r hr
    have hrD : r * r ∈ d.D ⊔ zpowers t := by
      obtain ⟨c, hc, s, hs, rfl⟩ := Common.exists_mul_of_le_normalizer hSC₁ r hr
      have hsc : s * c * s⁻¹ ∈ yamadaC₁ d t := (mem_normalizer_iff.1 (hSC₁ hs) c).1 hc
      have hcV : c ∈ normalizer ((d.U ⊔ zpowers t : Subgroup G) : Set G) ⊓
          centralizer (d.U : Set G) := ⟨yamadaC₁_le d t hc, hC₁U hc⟩
      have hscV : s * c * s⁻¹ ∈ normalizer ((d.U ⊔ zpowers t : Subgroup G) : Set G) ⊓
          centralizer (d.U : Set G) := ⟨yamadaC₁_le d t hsc, hC₁U hsc⟩
      have hst : s * t = t * s := mem_centralizer_singleton_iff.1 (h.S_le_centralizer d hs)
      have hκ := hc₁.crossed_mem_of_mem hcV
      have h1 : (c * (s * c * s⁻¹))⁻¹ * t * (c * (s * c * s⁻¹)) * t = 1 := by
        rw [hc₁.crossed_mul_of_mem hcV hscV,
          CFSG.EvenSmallLie.UnitarySix.YamadaD.crossed_conj hst,
          show s * (c⁻¹ * t * c * t) * s⁻¹ = c⁻¹ * t * c * t by
            rw [← mem_centralizer_iff.1 (hSU hs) _ hκ, mul_inv_cancel_right],
          hc₁.mul_self_of_mem hκ]
      have hC : c * (s * c * s⁻¹) ∈ d.D ⊔ zpowers t := by
        rw [← hC₁t]
        refine Subgroup.mem_inf.2 ⟨mul_mem hc hsc, mem_centralizer_singleton_iff.2 ?_⟩
        have e' := (hc₁.crossed_eq_iff (one_mem _)).1 h1
        rw [mul_one] at e' 
        calc c * (s * c * s⁻¹) * t =
            c * (s * c * s⁻¹) * ((c * (s * c * s⁻¹))⁻¹ * t * (c * (s * c * s⁻¹))) := by rw [e']
          _ = t * (c * (s * c * s⁻¹)) := by group
      have hs2 : s * s ∈ d.D := by
        have : s ^ 2 ∈ closure {z | ∃ g ∈ d.S, z = g ^ 2} := subset_closure ⟨s, hs, rfl⟩
        rw [← hFS, sq] at this
        exact hFD this
      rw [show c * s * (c * s) = c * (s * c * s⁻¹) * (s * s) by group]
      exact mul_mem hC (mem_sup_left hs2)
    have hrM : r * r ∈ d.M ⊔ zpowers t := by
      rw [← hL₂t]
      exact ⟨h.mul_self_mem_yamadaL₂ d hK ((h.yamada_5_6_1 d hK).2.1 hr),
        ((h.tD_le_yamadaR d).trans (h.yamadaR_le_centralizer d)) hrD⟩
    have hrF := h.mem_tF_of_mem_tD d hrD hrM
    have hrS₁ : r * r ∈ yamadaS₁ d t := by
      have htN : zpowers t ≤ normalizer (yamadaS₁ d t : Set G) := (zpowers_le).2
        (hR₁N (hR₁S₁ ▸ mem_sup_right (mem_zpowers t)))
      rw [hR₁S₁] at hr
      obtain ⟨s₁, hs₁, τ, hτ, rfl⟩ := Common.exists_mul_of_le_normalizer htN r hr
      have hττ : τ * τ = 1 := by
        obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 hτ
        rcases h.zpow_eq_one_or_eq k with hk | hk <;> rw [hk]
        · rw [mul_one]
        · exact h.t_mul_t
      rw [show s₁ * τ * (s₁ * τ) = s₁ * (τ * s₁ * τ⁻¹) * (τ * τ) by group, hττ, mul_one]
      exact mul_mem hs₁ ((mem_normalizer_iff.1 (htN hτ) s₁).1 hs₁)
    rw [sq]
    rcases (h.mem_sup_zpowers_iff (d.image_le _)).1 hrF with h1 | h1
    · exact h1
    · exfalso
      have hFS₁ : d.F ≤ yamadaS₁ d t := hFS ▸ (closure_le _).2 fun z ⟨g, hg, e⟩ =>
        e ▸ (le_sup_left : d.S ≤ yamadaS₁ d t) (pow_mem hg 2)
      refine htS₁ ?_
      have := mul_mem (hFS₁ h1) (inv_mem hrS₁)
      rwa [mul_inv_cancel_right] at this
  have hR₁F : closure {z | ∃ g ∈ yamadaR₁ d t, z = g ^ 2} ≤ d.F :=
    (closure_le _).2 fun z ⟨g, hg, e⟩ => e ▸ hsq g hg
  have hS₁R₁' : closure {z | ∃ g ∈ yamadaS₁ d t, z = g ^ 2} ≤
      closure {z | ∃ g ∈ yamadaR₁ d t, z = g ^ 2} :=
    closure_mono fun z ⟨g, hg, e⟩ => ⟨g, hS₁R₁ hg, e⟩
  have hFS₁' : d.F ≤ closure {z | ∃ g ∈ yamadaS₁ d t, z = g ^ 2} := by
    rw [hFS]
    exact closure_mono fun z ⟨g, hg, e⟩ => ⟨g, (le_sup_left : d.S ≤ yamadaS₁ d t) hg, e⟩
  exact ⟨le_antisymm hR₁F (hFS₁'.trans hS₁R₁'), le_antisymm (hS₁R₁'.trans hR₁F) hFS₁'⟩

theorem yamada_5_8_4 (h : Setup G L f t) (d : G2Data L K) (hK : Nat.card K = 2 ^ f) :
    yamadaL₂ d t = yamadaL₁ d t ⊔ (yamadaL₁ d t).map (MulAut.conj d.wb).toMonoidHom ∧
      yamadaL₁ d t ⊓ (yamadaL₁ d t).map (MulAut.conj d.wb).toMonoidHom = d.M ⊔ zpowers t := by
  obtain ⟨hL₂Y, hL₂t, hL₂tr, -⟩ := h.two_core_L₂ d hK
  obtain ⟨hwY, -, hwM⟩ := d.wb_mem_normalizer
  have hc₂ := h.cosetData_tY d hK
  set w := d.wb with hwdef
  have hwt : w * t = t * w := mem_centralizer_singleton_iff.1 (h.L_le_centralizer hwY.1)
  have hwt' : w⁻¹ * t = t * w⁻¹ := mem_centralizer_singleton_iff.1
    (h.L_le_centralizer (inv_mem hwY.1))
  have hwL₂ : w ∈ normalizer (yamadaL₂ d t : Set G) :=
    le_normalizer_yamadaL₂ d t (h.centralizer_inf_normalizer_Y_le d
      ⟨h.L_le_centralizer hwY.1, hwY.2⟩)
  have hV : ∀ {x : G}, x ∈ yamadaL₂ d t → x ∈ normalizer ((d.Y ⊔ zpowers t : Subgroup G) :
      Set G) ⊓ centralizer (d.Y : Set G) := fun hx => ⟨yamadaL₂_le d t hx, hL₂Y hx⟩
  have hL₁ : ∀ {x : G}, x ∈ yamadaL₂ d t → (x ∈ yamadaL₁ d t ↔ x⁻¹ * t * x * t ∈ d.U) :=
    fun hx => ⟨fun h1 => (h.mem_yamadaR₁_iff d hK (mem_sup_left hx)).1 h1.2,
      fun h1 => ⟨hx, (h.mem_yamadaR₁_iff d hK (mem_sup_left hx)).2 h1⟩⟩
  have hconj : ∀ {x : G}, (w⁻¹ * x * w)⁻¹ * t * (w⁻¹ * x * w) * t =
      w⁻¹ * (x⁻¹ * t * x * t) * w := fun {x} => by
    have := CFSG.EvenSmallLie.UnitarySix.YamadaD.crossed_conj (x := x) hwt'
    rwa [inv_inv] at this
  have hwx : ∀ {x : G}, x ∈ yamadaL₂ d t → w⁻¹ * x * w ∈ yamadaL₂ d t := fun hx => by
    have := (mem_normalizer_iff.1 (inv_mem hwL₂) _).1 hx
    rwa [inv_inv] at this
  have hL₁w : ∀ {x : G}, x ∈ yamadaL₂ d t →
      (x ∈ (yamadaL₁ d t).map (MulAut.conj w).toMonoidHom ↔
        w⁻¹ * (x⁻¹ * t * x * t) * w ∈ d.U) := fun hx => by
    rw [mem_map_conj_iff, hL₁ (hwx hx), hconj]
  have hkerC : ∀ {x : G}, x ∈ yamadaL₂ d t → x⁻¹ * t * x * t = 1 → x ∈ d.M ⊔ zpowers t :=
    fun {x} hx h1 => by
      rw [← hL₂t]
      refine ⟨hx, mem_centralizer_singleton_iff.2 ?_⟩
      have e' := (hc₂.crossed_eq_iff (one_mem _)).1 h1
      rw [mul_one] at e'
      calc x * t = x * (x⁻¹ * t * x) := by rw [e']
        _ = t * x := by group
  have htM₁ : d.M ⊔ zpowers t ≤ yamadaL₁ d t := by
    obtain ⟨-, -, -, -, -, -, -, -, hMS, -⟩ := d.inclusions
    exact le_inf (h.tM_le_yamadaL₂ d hK) (sup_le (hMS.trans le_sup_right)
      ((zpowers_le).2 (mem_sup_left (h.t_mem_yamadaC₁ d hK))))
  refine ⟨le_antisymm (fun x hx => ?_) (sup_le inf_le_left ?_), le_antisymm (fun x hx => ?_)
    (le_inf htM₁ fun x hx => ?_)⟩
  ·
    obtain ⟨u, hu, v, hv, huv⟩ := d.exists_wb_conj_mul (hc₂.crossed_mem_of_mem (hV hx))
    obtain ⟨x₁, hx₁, hx₁t⟩ := hL₂tr u (d.inclusions.1 hu)
    obtain ⟨x₂, hx₂, hx₂t⟩ := hL₂tr v (d.inclusions.1 hv)
    have hx₁κ : x₁⁻¹ * t * x₁ * t = u := (hc₂.crossed_eq_iff (d.inclusions.1 hu)).2 hx₁t
    have hx₂κ : x₂⁻¹ * t * x₂ * t = v := (hc₂.crossed_eq_iff (d.inclusions.1 hv)).2 hx₂t
    have hz : w * x₂ * w⁻¹ ∈ yamadaL₂ d t := (mem_normalizer_iff.1 hwL₂ x₂).1 hx₂
    have hzκ : (w * x₂ * w⁻¹)⁻¹ * t * (w * x₂ * w⁻¹) * t = w * v * w⁻¹ := by
      rw [CFSG.EvenSmallLie.UnitarySix.YamadaD.crossed_conj hwt, hx₂κ]
    have hx₁L₁ : x₁ ∈ yamadaL₁ d t := (hL₁ hx₁).2 (hx₁κ ▸ hu)
    have hzL₁ : w * x₂ * w⁻¹ ∈ (yamadaL₁ d t).map (MulAut.conj w).toMonoidHom := by
      rw [mem_map_conj_iff, show w⁻¹ * (w * x₂ * w⁻¹) * w = x₂ by group]
      exact (hL₁ hx₂).2 (hx₂κ ▸ hv)
    have hκ : (w * x₂ * w⁻¹ * x₁)⁻¹ * t * (w * x₂ * w⁻¹ * x₁) * t = x⁻¹ * t * x * t := by
      rw [hc₂.crossed_mul_of_mem (hV hz) (hV hx₁), hzκ, hx₁κ, huv]
    have hm := Common.mul_inv_mem_centralizer_of_conj_eq (mul_right_cancel hκ)
    have hmM : x * (w * x₂ * w⁻¹ * x₁)⁻¹ ∈ d.M ⊔ zpowers t := by
      rw [← hL₂t]
      exact Subgroup.mem_inf.2 ⟨mul_mem hx (inv_mem (mul_mem hz hx₁)), hm⟩
    rw [show x = x * (w * x₂ * w⁻¹ * x₁)⁻¹ * (w * x₂ * w⁻¹ * x₁) by group]
    exact mul_mem (mem_sup_left (htM₁ hmM)) (mul_mem (mem_sup_right hzL₁) (mem_sup_left hx₁L₁))
  · rintro _ ⟨l, hl, rfl⟩
    exact (mem_normalizer_iff.1 hwL₂ l).1 hl.1
  · obtain ⟨hx₁, hx₂⟩ := Subgroup.mem_inf.1 hx
    have hxL₂ : x ∈ yamadaL₂ d t := hx₁.1
    have hu := (hL₁ hxL₂).1 hx₁
    have hu' := (hL₁w hxL₂).1 hx₂
    have hv1 := d.eq_one_of_wb_conj_mem_U hu' (by
      rw [show w * (w⁻¹ * (x⁻¹ * t * x * t) * w) * w⁻¹ = x⁻¹ * t * x * t by group]
      exact hu)
    refine hkerC hxL₂ ?_
    have := congrArg (fun z => w * z * w⁻¹) hv1
    simp only [mul_one, mul_inv_cancel] at this
    rw [show w * (w⁻¹ * (x⁻¹ * t * x * t) * w) * w⁻¹ = x⁻¹ * t * x * t by group] at this
    exact this
  · rw [mem_map_conj_iff]
    refine htM₁ ?_
    have hwtM : w⁻¹ ∈ normalizer ((d.M ⊔ zpowers t : Subgroup G) : Set G) :=
      Common.mem_normalizer_sup (inv_mem hwM) (mem_normalizer_zpowers hwt')
    have := (mem_normalizer_iff.1 hwtM x).1 hx
    rwa [inv_inv] at this

theorem yamadaR₁_le_normalizer (h : Setup G L f t) (d : G2Data L K) (hK : Nat.card K = 2 ^ f) :
    yamadaR₁ d t ≤ normalizer (yamadaC₁ d t : Set G) ∧
      yamadaR₁ d t ≤ normalizer (d.S : Set G) ∧ yamadaR₁ d t ≤ normalizer (d.D : Set G) := by
  obtain ⟨-, hC₁t, -, -⟩ := h.two_core_C₁ d hK
  obtain ⟨hS₁R₁, -, hR₁N, htS₁⟩ := h.yamadaS₁_spec d hK
  have hR₁R : yamadaR₁ d t ≤ normalizer (yamadaR d t : Set G) := by
    rw [(h.yamada_5_6_1 d hK).1]
    exact inf_le_right
  have hC : yamadaR₁ d t ≤ normalizer (yamadaC₁ d t : Set G) :=
    sup_le le_normalizer ((h.S_le_inf_normalizer_U d).trans
      (h.inf_normalizer_U_le_normalizer_yamadaC₁ d))
  have hSR : yamadaS₁ d t ⊓ yamadaR d t = d.S := by
    refine le_antisymm (fun x hx => ?_) (le_inf le_sup_left fun y hy =>
      (h.yamadaR_eq d).ge (mem_sup_left hy))
    obtain ⟨hx₁, hx₂⟩ := Subgroup.mem_inf.1 hx
    rw [h.yamadaR_eq d] at hx₂
    rcases (h.mem_sup_zpowers_iff (d.image_le _)).1 hx₂ with h1 | h1
    · exact h1
    · exfalso
      refine htS₁ ?_
      have := mul_mem ((le_sup_left : d.S ≤ yamadaS₁ d t) h1) (inv_mem hx₁)
      rwa [mul_inv_cancel_right] at this
  have hS : yamadaR₁ d t ≤ normalizer (d.S : Set G) := by
    rw [← hSR]
    exact fun x hx => Common.mem_normalizer_inf (hR₁N hx) (hR₁R hx)
  have hCS : yamadaC₁ d t ⊓ d.S = d.D := by
    refine le_antisymm (fun x hx => ?_) (le_inf (le_sup_left.trans (h.tD_le_yamadaC₁ d hK))
      d.inclusions.2.2.2.2.2.2.2.1)
    obtain ⟨hx₁, hx₂⟩ := Subgroup.mem_inf.1 hx
    exact h.mem_D_of_mem_sup d (by
      rw [← hC₁t]
      exact ⟨hx₁, h.S_le_centralizer d hx₂⟩) (d.image_le _ hx₂)
  refine ⟨hC, hS, ?_⟩
  rw [← hCS]
  exact fun x hx => Common.mem_normalizer_inf (hC hx) (hS hx)

theorem yamadaC₁_le_of_index_two (h : Setup G L f t) (d : G2Data L K) (hK : Nat.card K = 2 ^ f)
    {H : Subgroup G} (hBH : d.D ⊔ zpowers t ≤ H) (hJH : d.J₃ ≤ normalizer (H : Set G))
    (hH : ∀ c ∈ yamadaC₁ d t, ∀ c' ∈ yamadaC₁ d t, c ∉ H → c' ∉ H → c * c' ∈ H) :
    yamadaC₁ d t ≤ H := by
  have hK4 : 4 ≤ Nat.card K := hK ▸ h.four_le
  obtain ⟨hC₁U, hC₁t, -, -⟩ := h.two_core_C₁ d hK
  have hc₁ := h.cosetData_tU d hK
  have hNC₁ := h.inf_normalizer_U_le_normalizer_yamadaC₁ d
  have hJ := d.J₃_le_inf_normalizer_U
  intro c hc
  by_contra hcH
  obtain ⟨ι, hι⟩ := d.exists_mulEquiv_U
  have hV : ∀ {x : G}, x ∈ yamadaC₁ d t → x ∈ normalizer ((d.U ⊔ zpowers t : Subgroup G) :
      Set G) ⊓ centralizer (d.U : Set G) := fun hx => ⟨yamadaC₁_le d t hx, hC₁U hx⟩
  obtain ⟨y, hy⟩ := ι.surjective ⟨_, hc₁.crossed_mem_of_mem (hV hc)⟩
  set x := Multiplicative.toAdd y with hxdef
  have hcx : c⁻¹ * t * c * t = ι (Multiplicative.ofAdd x) := by
    rw [hxdef, ofAdd_toAdd, hy]
  obtain ⟨a, ha0, ha1⟩ := exists_ne_zero_ne_one hK4
  have ha1' : 1 + a ≠ 0 := fun h0 => ha1 ((CharTwo.add_eq_zero.1 h0).symm)
  obtain ⟨e₁, he₁, he₁x⟩ := d.exists_mem_J₃_scalar ι hι ha0
  obtain ⟨e₂, he₂, he₂x⟩ := d.exists_mem_J₃_scalar ι hι ha1'
  have hmem : ∀ {e : G}, e ∈ d.J₃ → e * c * e⁻¹ ∈ yamadaC₁ d t := fun he =>
    (mem_normalizer_iff.1 (hNC₁ (hJ he)) c).1 hc
  have hnot : ∀ {e : G}, e ∈ d.J₃ → e * c * e⁻¹ ∉ H := fun {e} he he' => hcH (by
    have := (mem_normalizer_iff.1 (inv_mem (hJH he)) _).1 he'
    rwa [show e⁻¹ * (e * c * e⁻¹) * e⁻¹⁻¹ = c by group] at this)
  have hκ : ∀ {e : G} {b : K}, e ∈ d.J₃ → (∀ x' : K, e * (ι (Multiplicative.ofAdd x') : G) * e⁻¹ =
      ι (Multiplicative.ofAdd (b * x'))) →
        (e * c * e⁻¹)⁻¹ * t * (e * c * e⁻¹) * t = ι (Multiplicative.ofAdd (b * x)) := by
    intro e b he heb
    rw [CFSG.EvenSmallLie.UnitarySix.YamadaD.crossed_conj
      (mem_centralizer_singleton_iff.1 (h.L_le_centralizer (hJ he).1)), hcx, heb]
  have h12 : (c * (e₁ * c * e₁⁻¹))⁻¹ * t * (c * (e₁ * c * e₁⁻¹)) * t =
      (e₂ * c * e₂⁻¹)⁻¹ * t * (e₂ * c * e₂⁻¹) * t := by
    rw [hc₁.crossed_mul_of_mem (hV hc) (hV (hmem he₁)), hκ he₁ he₁x, hκ he₂ he₂x, hcx,
      ← Subgroup.coe_mul, ← map_mul, ← ofAdd_add]
    congr 3
    ring
  have hw := Common.mul_inv_mem_centralizer_of_conj_eq (mul_right_cancel h12)
  have hwB : (e₂ * c * e₂⁻¹) * (c * (e₁ * c * e₁⁻¹))⁻¹ ∈ d.D ⊔ zpowers t := by
    rw [← hC₁t]
    exact Subgroup.mem_inf.2 ⟨mul_mem (hmem he₂) (inv_mem (mul_mem hc (hmem he₁))), hw⟩
  refine hnot he₂ ?_
  rw [show e₂ * c * e₂⁻¹ = (e₂ * c * e₂⁻¹) * (c * (e₁ * c * e₁⁻¹))⁻¹ * (c * (e₁ * c * e₁⁻¹)) by
    group]
  exact mul_mem (hBH hwB) (hH c hc _ (hmem he₁) hcH (hnot he₁))

theorem yamadaR₁_le_normalizer_W (h : Setup G L f t) (d : G2Data L K) (hK : Nat.card K = 2 ^ f) :
    yamadaR₁ d t ≤ normalizer (d.W : Set G) := by
  obtain ⟨-, -, -, hXF, hWF, -, -, hDS, -, -⟩ := d.inclusions
  have hSW : d.S ≤ normalizer (d.W : Set G) := d.S_le_normalizers.2.2.2.1
  have htW : t ∈ normalizer (d.W : Set G) := Subgroup.centralizer_le_normalizer _
    (mem_centralizer_iff.2 fun w hw => mem_centralizer_singleton_iff.1
      (h.L_le_centralizer (d.image_le _ hw)))
  have hJW : d.J₃ ≤ normalizer (d.W : Set G) := fun j hj => by
    have hjJ : j ∈ d.J := d.image_mono inf_le_left hj
    have hjS : j ∈ L ⊓ normalizer (d.S : Set G) := by
      rw [(d.yamada_3_13_1_G).2.2]
      exact mem_sup_left hjJ
    exact h.normalizer_S_le_normalizer_W d hK ⟨h.L_le_centralizer hjS.1, hjS.2⟩
  have hFN : yamadaR₁ d t ≤ normalizer (d.F : Set G) := by
    rw [← (h.yamada_5_8_2 d hK).1]
    exact le_normalizer.trans (normalizer_le_normalizer_closure_sq _)
  have hswap : ∀ c ∈ yamadaR₁ d t, c ∉ normalizer (d.W : Set G) →
      d.W.map (MulAut.conj c).toMonoidHom = d.X ∧ d.X.map (MulAut.conj c).toMonoidHom = d.W := by
    intro c hc hcW
    have h1 := d.map_conj_mem_W_X (hFN hc) (Or.inl rfl)
    have h2 := d.map_conj_mem_W_X (hFN hc) (Or.inr rfl)
    have hW : d.W.map (MulAut.conj c).toMonoidHom = d.X :=
      h1.resolve_left fun e => hcW (mem_normalizer_of_map_conj_eq e)
    refine ⟨hW, h2.resolve_right fun e => d.W_ne_X ?_⟩
    exact Subgroup.map_injective (MulAut.conj c).injective (hW.trans e.symm)
  have hC₁W : yamadaC₁ d t ≤ normalizer (d.W : Set G) := by
    refine h.yamadaC₁_le_of_index_two d hK (sup_le (hDS.trans hSW) ((zpowers_le).2 htW))
      (hJW.trans le_normalizer) fun c hc c' hc' hcW hc'W => ?_
    have hcR : c ∈ yamadaR₁ d t := mem_sup_left hc
    have hc'R : c' ∈ yamadaR₁ d t := mem_sup_left hc'
    refine mem_normalizer_of_map_conj_eq ?_
    rw [map_conj_mul, (hswap c' hc'R hc'W).1, (hswap c hcR hcW).2]
  exact sup_le hC₁W hSW

theorem yamada_5_8_3 (h : Setup G L f t) (d : G2Data L K) (hK : Nat.card K = 2 ^ f) :
    d.W ≤ yamadaR₂ d t ∧ yamadaR₂ d t ≤ normalizer (d.W : Set G) ∧ d.X ≤ yamadaR₂ d t ∧
      yamadaR₂ d t ≤ normalizer (d.X : Set G) := by
  obtain ⟨-, -, -, hXF, hWF, hFD, -, hDS, -, -⟩ := d.inclusions
  obtain ⟨-, hwW, -⟩ := d.wb_mem_normalizer
  have hR₁W := h.yamadaR₁_le_normalizer_W d hK
  have hR₂W : yamadaR₂ d t ≤ normalizer (d.W : Set G) := by
    refine sup_le ?_ d.S_le_normalizers.2.2.2.1
    rw [(h.yamada_5_8_4 d hK).1]
    refine sup_le (inf_le_right.trans hR₁W) ?_
    rintro _ ⟨l, hl, rfl⟩
    exact mul_mem (mul_mem hwW (hR₁W hl.2)) (inv_mem hwW)
  have hSR₂ : d.S ≤ yamadaR₂ d t := le_sup_right
  refine ⟨(hWF.trans (hFD.trans hDS)).trans hSR₂, hR₂W, (hXF.trans (hFD.trans hDS)).trans hSR₂,
    fun g hg => ?_⟩
  have hFN : yamadaR₂ d t ≤ normalizer (d.F : Set G) := by
    rw [← (h.yamada_5_8_2 d hK).1]
    exact (h.yamada_5_6_1 d hK).2.2.1.trans (normalizer_le_normalizer_closure_sq _)
  refine mem_normalizer_of_map_conj_eq ((d.map_conj_mem_W_X (hFN hg) (Or.inr rfl)).resolve_left
    fun e => d.W_ne_X ?_)
  exact Subgroup.map_injective (MulAut.conj g).injective
    ((map_conj_eq_of_mem_normalizer (hR₂W hg)).trans e.symm)

theorem yamada_5_8_5 (h : Setup G L f t) (d : G2Data L K) (hK : Nat.card K = 2 ^ f) :
    d.M ≤ normalizer ((d.Y ⊔ zpowers t : Subgroup G) : Set G) ∧
      normalizer ((d.Y ⊔ zpowers t : Subgroup G) : Set G) ≤ normalizer (d.M : Set G) := by
  obtain ⟨-, -, hwM⟩ := d.wb_mem_normalizer
  obtain ⟨-, -, -, -, -, -, -, -, hMS, -⟩ := d.inclusions
  have hMt : (d.M ⊔ zpowers t) ⊓ d.S = d.M := by
    refine le_antisymm (fun x hx => ?_) (le_inf le_sup_left hMS)
    obtain ⟨hx₁, hx₂⟩ := Subgroup.mem_inf.1 hx
    rcases (h.mem_sup_zpowers_iff (d.image_le _)).1 hx₁ with h1 | h1
    · exact h1
    · exfalso
      refine h.t_not_mem_L ?_
      have := mul_mem (d.image_le _ h1) (inv_mem (d.image_le _ hx₂))
      rwa [mul_inv_cancel_right] at this
  have hL₁M : yamadaL₁ d t ≤ normalizer (d.M : Set G) := by
    rw [← hMt]
    intro x hx
    refine Common.mem_normalizer_inf ?_ ((h.yamadaR₁_le_normalizer d hK).2.1 hx.2)
    rw [← (h.yamada_5_5_1 d hK).1]
    exact yamadaL₂_le d t hx.1
  have hL₂M : yamadaL₂ d t ≤ normalizer (d.M : Set G) := by
    rw [(h.yamada_5_8_4 d hK).1]
    refine sup_le hL₁M ?_
    rintro _ ⟨l, hl, rfl⟩
    exact mul_mem (mul_mem hwM (hL₁M hl)) (inv_mem hwM)
  refine ⟨fun m hm => h.centralizer_inf_normalizer_Y_le d ⟨h.L_le_centralizer (d.image_le _ hm),
    d.S_le_normalizers.2.1 (hMS hm)⟩, ?_⟩
  rw [(h.yamada_5_5_1 d hK).2.1]
  exact sup_le hL₂M (h.centralizer_inf_normalizer_le_of_pCoreOf d (h.pCoreOf_range_act d hK).2)

theorem yamada_5_8_6 (h : Setup G L f t) (d : G2Data L K) (hK : Nat.card K = 2 ^ f) :
    yamadaR₂ d t ⊓ normalizer (d.S : Set G) = yamadaR₁ d t ∧
      yamadaR₂ d t ⊓ normalizer (d.D : Set G) = yamadaR₁ d t := by
  obtain ⟨hR₁, hR₁R₂, -, -, -⟩ := h.yamada_5_6_1 d hK
  obtain ⟨-, hS, hD⟩ := h.yamadaR₁_le_normalizer d hK
  obtain ⟨-, -, -, -, -, -, -, -, hMS, -⟩ := d.inclusions
  have hN := h.yamadaR₂_le_normalizer_tM d hK
  have hRS : d.M ⊔ zpowers t ⊔ d.S = yamadaR d t := by
    rw [h.yamadaR_eq d, sup_right_comm, sup_eq_right.2 hMS]
  have hRD : d.M ⊔ zpowers t ⊔ d.D = yamadaR d t := by
    rw [h.yamadaR_eq d, sup_right_comm, sup_comm d.M, (d.yamada_defs).2.2.2.2.2.2.2.2]
  refine ⟨le_antisymm (fun g hg => ?_) (le_inf hR₁R₂ hS), le_antisymm (fun g hg => ?_)
    (le_inf hR₁R₂ hD)⟩
  · rw [hR₁]
    refine ⟨hg.1, ?_⟩
    rw [← hRS]
    exact Common.mem_normalizer_sup (hN hg.1) hg.2
  · rw [hR₁]
    refine ⟨hg.1, ?_⟩
    rw [← hRD]
    exact Common.mem_normalizer_sup (hN hg.1) hg.2

end Local

end Setup

end CFSG.LocalAnalysis.EvenBN.G2
