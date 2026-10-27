module

public import CFSG.Quasithin.Vol2.Ch6Sec2Thm19B
public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch6Sec2Lem17C

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Assembly.LowTwoRank CFSG.QuasithinUnique CFSG.Quasithin.E3
  CFSG.LieType.BorelTits CFSG.Quasithin.ASInputs
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G] {T M L V : Subgroup G}

namespace Hyp6Sec2

variable (h : Hyp6Sec2 G T M L V)
include h

theorem sixteen_le_ch619_F4 (h331 : Stmt3_3_1_F4) (h432 : Stmt4_3_2_F4) (h512 : Stmt5_1_2_F4)
    (h614 : Stmt6_1_4_F4) (h615 : Stmt6_1_5_F4) (h626 : Stmt6_2_6_F4) (h6210 : Stmt6_2_10_F4)
    (h6211 : Stmt6_2_11_F4) (h6212 : Stmt6_2_12_F4) (hlt : ch6ZS T L V < V ⊓ uCh611 T L V) :
    16 ≤ (centerOf (uCh611 T L V)).relIndex (uCh611 T L V) := by
  obtain ⟨U₀, hU₀U, -, hU₀es, hU₀32, -⟩ :=
    h.exists_extraspecial_ch615_F4 h331 h432 h512 h614 h615 h626 h6210 h6211 h6212 hlt
  have hZ2 : Nat.card (zCh611 T) = 2 := h.card_omega_F4 h331 h432 h512 h614 h615
  have hUH : uCh611 T L V ≤ hCh611 T := h.uCh611_le_h_F4 h331 h432 h512 h614 h615
  have hZc : ∀ z ∈ zCh611 T, ∀ u ∈ uCh611 T L V, u * z = z * u := fun z hz u hu =>
    (Subgroup.mem_centralizer_iff.mp (hUH hu) z hz).symm
  have hcomm : ∀ a ∈ uCh611 T L V, ∀ b ∈ uCh611 T L V, a * b * a⁻¹ * b⁻¹ ∈ zCh611 T :=
    fun a ha b hb => h.comm_mem_ch615_F4 h331 h432 h512 h614 h615 ha hb
  obtain ⟨-, -, hcen⟩ := extraspecial_facts_ch615 hZ2 hU₀U hZc hcomm hU₀es
  have hle : centerOf (uCh611 T L V) ⊓ U₀ ≤ zCh611 T := fun x hx => hcen x hx.2 hx.1
  have hcard : Nat.card ↥(centerOf (uCh611 T L V) ⊓ U₀) ≤ 2 :=
    hZ2 ▸ Subgroup.card_le_of_le hle
  have h1 := Subgroup.relIndex_mul_card (centerOf (uCh611 T L V)) U₀
  have hne : (centerOf (uCh611 T L V)).relIndex (uCh611 T L V) ≠ 0 :=
    Subgroup.index_ne_zero_of_finite
  have h2 := Subgroup.relIndex_le_of_le_right hU₀U hne
  have h3 : 2 ^ 5 ≤ (centerOf (uCh611 T L V)).relIndex U₀ * 2 :=
    hU₀32.trans (h1 ▸ Nat.mul_le_mul_left _ hcard)
  omega

variable {A : Type} [AddCommGroup A] [Module (ZMod 2) A] [Finite A]
  {B : LinearMap.BilinForm (ZMod 2) A} {β : ↥(uCh611 T L V) →* Multiplicative A}
  {ρ : ↥(hCh611 T) →* (A ≃ₗ[ZMod 2] A)}

theorem mem_range_iff_ch619_F4 (h331 : Stmt3_3_1_F4) (h432 : Stmt4_3_2_F4) (h512 : Stmt5_1_2_F4)
    (h614 : Stmt6_1_4_F4) (h615 : Stmt6_1_5_F4) (h626 : Stmt6_2_6_F4) (h6210 : Stmt6_2_10_F4)
    (h6211 : Stmt6_2_11_F4) (h6212 : Stmt6_2_12_F4) (hlt : ch6ZS T L V < V ⊓ uCh611 T L V)
    (hR : IsSymplecticRealization (hCh611 T) (uCh611 T L V) (centerOf (uCh611 T L V)) A B β ρ)
    {v : G} (hv : v ∈ V) (hvU : v ∉ uCh611 T L V) (w : A) :
    w ∈ LinearMap.range ((ρ ⟨v, h.V_le_hCh611 hv⟩).toLinearMap - LinearMap.id) ↔
      ∃ y ∈ V ⊓ uCh611 T L V, w = piA_ch619 hR y := by
  have hHN := hCh611_le_normalizer_u T L V
  have hvH := h.V_le_hCh611 hv
  have hZZU : zCh611 T ≤ centerOf (uCh611 T L V) := by
    rw [← h.inf_centerOf_eq_ch616_F4 h331 h432 h512 h614 h615 h626 h6210 h6211 h6212 hlt]
    exact inf_le_right
  constructor
  · rintro ⟨x, rfl⟩
    obtain ⟨u, hu, rfl⟩ := piA_surj_ch619 hR x
    have hvu : v * u * v⁻¹ ∈ uCh611 T L V :=
      (Subgroup.mem_normalizer_iff.mp (hHN hvH) u).mp hu
    have huN : u ∈ Subgroup.normalizer (V : Set G) :=
      h.toHyp611.T_le_normalizer (h.uCh611_le_T_F4 h331 h432 h512 h614 h615 hu)
    have hV1 : u * v⁻¹ * u⁻¹ ∈ V := (Subgroup.mem_normalizer_iff.mp huN _).mp (V.inv_mem hv)
    refine ⟨v * u * v⁻¹ * u⁻¹, ⟨?_, (uCh611 T L V).mul_mem hvu ((uCh611 T L V).inv_mem hu)⟩, ?_⟩
    · have e : v * u * v⁻¹ * u⁻¹ = v * (u * v⁻¹ * u⁻¹) := by group
      rw [e]
      exact V.mul_mem hv hV1
    · have e2 : piA_ch619 hR (v * u * v⁻¹ * u⁻¹) =
          piA_ch619 hR (v * u * v⁻¹) - piA_ch619 hR u := by
        rw [piA_mul_ch619 hR hvu ((uCh611 T L V).inv_mem hu), piA_inv_ch619 hR hu,
          sub_eq_add_neg]
      simp only [LinearMap.sub_apply, LinearMap.id_apply, LinearEquiv.coe_coe]
      rw [rho_piA_ch619 hR hHN ⟨v, hvH⟩ hu]
      exact e2.symm
  · rintro ⟨y, hy, rfl⟩
    obtain ⟨a', ha', hz⟩ :=
      h.exists_comm_eq_U_ch616_F4 h331 h432 h512 h614 h615 h626 h6210 h6211 h6212 hlt hv hvU y hy
    have hva : v * a' * v⁻¹ ∈ uCh611 T L V :=
      (Subgroup.mem_normalizer_iff.mp (hHN hvH) a').mp ha'
    have hc : v * a' * v⁻¹ * a'⁻¹ ∈ uCh611 T L V :=
      (uCh611 T L V).mul_mem hva ((uCh611 T L V).inv_mem ha')
    refine ⟨piA_ch619 hR a', ?_⟩
    have e1 : piA_ch619 hR (v * a' * v⁻¹ * a'⁻¹) = piA_ch619 hR y := by
      rw [piA_eq_iff_ch619 hR hc hy.2, ← commutatorElement_def]
      exact hZZU hz
    have e2 : piA_ch619 hR (v * a' * v⁻¹ * a'⁻¹) =
        piA_ch619 hR (v * a' * v⁻¹) - piA_ch619 hR a' := by
      rw [piA_mul_ch619 hR hva ((uCh611 T L V).inv_mem ha'), piA_inv_ch619 hR ha',
        sub_eq_add_neg]
    simp only [LinearMap.sub_apply, LinearMap.id_apply, LinearEquiv.coe_coe]
    rw [rho_piA_ch619 hR hHN ⟨v, hvH⟩ ha']
    exact e2.symm.trans e1

theorem finrank_range_ch619_F4 (h331 : Stmt3_3_1_F4) (h432 : Stmt4_3_2_F4) (h512 : Stmt5_1_2_F4)
    (h614 : Stmt6_1_4_F4) (h615 : Stmt6_1_5_F4) (h626 : Stmt6_2_6_F4) (h6210 : Stmt6_2_10_F4)
    (h6211 : Stmt6_2_11_F4) (h6212 : Stmt6_2_12_F4) (hlt : ch6ZS T L V < V ⊓ uCh611 T L V)
    (hR : IsSymplecticRealization (hCh611 T) (uCh611 T L V) (centerOf (uCh611 T L V)) A B β ρ)
    {v : G} (hv : v ∈ V) (hvU : v ∉ uCh611 T L V) :
    Module.finrank (ZMod 2)
      (LinearMap.range ((ρ ⟨v, h.V_le_hCh611 hv⟩).toLinearMap - LinearMap.id)) = 2 := by
  set R := LinearMap.range ((ρ ⟨v, h.V_le_hCh611 hv⟩).toLinearMap - LinearMap.id) with hRdef
  have h0 : piA_ch619 hR 1 = 0 := piA_one_ch619 hR
  let φ : ↥(V ⊓ uCh611 T L V) →* Multiplicative A :=
    { toFun := fun y => Multiplicative.ofAdd (piA_ch619 hR y)
      map_one' := by
        show Multiplicative.ofAdd (piA_ch619 hR 1) = 1
        rw [h0, ofAdd_zero]
      map_mul' := fun y y' => by
        show Multiplicative.ofAdd (piA_ch619 hR ((y : G) * y')) =
          Multiplicative.ofAdd (piA_ch619 hR y) *
            Multiplicative.ofAdd (piA_ch619 hR y')
        rw [piA_mul_ch619 hR y.2.2 y'.2.2, ofAdd_add] }
  have hker : φ.ker = (centerOf (uCh611 T L V)).subgroupOf (V ⊓ uCh611 T L V) := by
    ext y
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    show Multiplicative.ofAdd (piA_ch619 hR y) = 1 ↔ _
    rw [← ofAdd_zero, Multiplicative.ofAdd.injective.eq_iff, piA_eq_zero_iff_ch619 hR y.2.2]
  have hcard8 : Nat.card ↥(V ⊓ uCh611 T L V) = 2 ^ 3 :=
    (stmt6_2_14_of_F4 h6210 h6211 h6212 G T M L V h hlt).2
  have hZ2 : Nat.card (zCh611 T) = 2 := h.card_omega_F4 h331 h432 h512 h614 h615
  have hinf : centerOf (uCh611 T L V) ⊓ (V ⊓ uCh611 T L V) = zCh611 T := by
    rw [← h.inf_centerOf_eq_ch616_F4 h331 h432 h512 h614 h615 h626 h6210 h6211 h6212 hlt]
    ext x
    simp only [Subgroup.mem_inf]
    constructor
    · rintro ⟨hz, hxV, -⟩
      exact ⟨hxV, hz⟩
    · rintro ⟨hxV, hz⟩
      exact ⟨hz, hxV, hz.1⟩
  have hrel := Subgroup.relIndex_mul_card (centerOf (uCh611 T L V)) (V ⊓ uCh611 T L V)
  rw [hinf, hZ2, hcard8] at hrel
  have hidx : φ.ker.index = 4 := by
    rw [hker]
    show (centerOf (uCh611 T L V)).relIndex (V ⊓ uCh611 T L V) = 4
    omega
  have hrange : Nat.card φ.range = 4 := by
    rw [← Subgroup.index_ker φ, hidx]
  have hR4 : Nat.card ↥R = 4 := by
    rw [← hrange]
    refine Nat.card_congr (Equiv.subtypeEquiv Multiplicative.ofAdd fun w => ?_)
    rw [hRdef, h.mem_range_iff_ch619_F4 h331 h432 h512 h614 h615 h626 h6210 h6211 h6212 hlt hR hv
      hvU w, MonoidHom.mem_range]
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact ⟨⟨y, hy⟩, rfl⟩
    · rintro ⟨y, hy⟩
      refine ⟨y, y.2, ?_⟩
      have := congrArg Multiplicative.toAdd hy
      exact this.symm
  have : Module.Finite (ZMod 2) ↥R := Module.Finite.of_finite
  have h2 := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := ↥R)
  rw [hR4, Nat.card_zmod] at h2
  have h4 : (2 : ℕ) ^ 2 = 2 ^ Module.finrank (ZMod 2) ↥R := by rw [← h2]; norm_num
  exact (Nat.pow_right_injective le_rfl h4).symm

theorem isA2_ch619_F4 (h331 : Stmt3_3_1_F4) (h432 : Stmt4_3_2_F4) (h512 : Stmt5_1_2_F4)
    (h614 : Stmt6_1_4_F4) (h615 : Stmt6_1_5_F4)
    (hR : IsSymplecticRealization (hCh611 T) (uCh611 T L V) (centerOf (uCh611 T L V)) A B β ρ)
    {v : G} (hv : v ∈ V) : ∀ x : A, B x (ρ ⟨v, h.V_le_hCh611 hv⟩ x) = 0 := by
  have hHN := hCh611_le_normalizer_u T L V
  have hvH := h.V_le_hCh611 hv
  intro x
  obtain ⟨u, hu, rfl⟩ := piA_surj_ch619 hR x
  have hvu : v * u * v⁻¹ ∈ uCh611 T L V := (Subgroup.mem_normalizer_iff.mp (hHN hvH) u).mp hu
  rw [rho_piA_ch619 hR hHN ⟨v, hvH⟩ hu]
  exact (B_piA_ch619 hR hu hvu).mpr
    (h.comm_conj_eq_one_ch616_F4 h331 h432 h512 h614 h615 hv hu)

theorem mem_map_X_ch619_F4 (h331 : Stmt3_3_1_F4) (h432 : Stmt4_3_2_F4) (h512 : Stmt5_1_2_F4)
    (h614 : Stmt6_1_4_F4) (h615 : Stmt6_1_5_F4) (h626 : Stmt6_2_6_F4) (h6210 : Stmt6_2_10_F4)
    (h6211 : Stmt6_2_11_F4) (h6212 : Stmt6_2_12_F4) (hlt : ch6ZS T L V < V ⊓ uCh611 T L V)
    (hR : IsSymplecticRealization (hCh611 T) (uCh611 T L V) (centerOf (uCh611 T L V)) A B β ρ)
    {l : G} (hl : l ∈ lsCh617 T L V) (hlH : l ∉ hCh611 T) {v : G} (hv : v ∈ V) :
    ρ ⟨v, h.V_le_hCh611 hv⟩ ∈ ((conjSubgroup (uCh611 T L V) l ⊓
      Subgroup.centralizer (ch6ZS T L V : Set G)).subgroupOf (hCh611 T)).map ρ := by
  have hHN := hCh611_le_normalizer_u T L V
  have h9 := h.nine_ch617_F4 h331 h432 h512 h614 h615 h626 h6210 h6211 h6212 hlt hl hlH hv
  have hXH : conjSubgroup (uCh611 T L V) l ⊓ Subgroup.centralizer (ch6ZS T L V : Set G) ≤
      hCh611 T := inf_le_right.trans (Subgroup.centralizer_le (h.omega_le_ZS_F4 h331 h432 h512 h614
        h615))
  have hXN := hXH.trans (hCh611_le_normalizer_CH_ch619 T L V)
  have hmem : v ∈ ((conjSubgroup (uCh611 T L V) l ⊓
      Subgroup.centralizer (ch6ZS T L V : Set G) : Subgroup G) : Set G) *
        ((centralizerMod (centerOf (uCh611 T L V)) (hCh611 T) (uCh611 T L V) : Subgroup G) :
          Set G) := by
    rw [← Subgroup.coe_mul_of_left_le_normalizer_right _ _ hXN]
    exact h9
  obtain ⟨x, hx, c, hc, hxc⟩ := Set.mem_mul.mp hmem
  have hcH : c ∈ hCh611 T := centralizerMod_le_left _ _ _ hc
  have e : (⟨v, h.V_le_hCh611 hv⟩ : ↥(hCh611 T)) = ⟨x, hXH hx⟩ * ⟨c, hcH⟩ :=
    Subtype.ext hxc.symm
  rw [e, map_mul, rho_eq_one_ch619 hR hHN ⟨c, hcH⟩ hc, mul_one]
  exact ⟨⟨x, hXH hx⟩, Subgroup.mem_subgroupOf.mpr hx, rfl⟩

theorem fix_ch619_F4 (h331 : Stmt3_3_1_F4) (h432 : Stmt4_3_2_F4) (h512 : Stmt5_1_2_F4)
    (h614 : Stmt6_1_4_F4) (h615 : Stmt6_1_5_F4) (h625 : Stmt6_2_5_F4) (h626 : Stmt6_2_6_F4)
    (h6210 : Stmt6_2_10_F4) (h6211 : Stmt6_2_11_F4) (h6212 : Stmt6_2_12_F4)
    (hlt : ch6ZS T L V < V ⊓ uCh611 T L V)
    (hR : IsSymplecticRealization (hCh611 T) (uCh611 T L V) (centerOf (uCh611 T L V)) A B β ρ)
    {v : G} (hv : v ∈ V) (hvU : v ∉ uCh611 T L V) {a : G} (ha : a ∈ ch6ZS T L V)
    (haZ : a ∉ zCh611 T) :
    ∀ γ ∈ ρ.range,
      (∀ w ∈ LinearMap.range ((ρ ⟨v, h.V_le_hCh611 hv⟩).toLinearMap - LinearMap.id),
        γ w ∈ LinearMap.range ((ρ ⟨v, h.V_le_hCh611 hv⟩).toLinearMap - LinearMap.id)) →
      γ (piA_ch619 hR a) = piA_ch619 hR a := by
  classical
  have hHN := hCh611_le_normalizer_u T L V
  have hZUN := hCh611_le_normalizer_centerOf_ch615 T L V
  have hZZS := h.omega_le_ZS_F4 h331 h432 h512 h614 h615
  have hZ2 : Nat.card (zCh611 T) = 2 := h.card_omega_F4 h331 h432 h512 h614 h615
  have hZS4 : Nat.card (ch6ZS T L V) = 4 := by rw [h.toHyp611Nat.card_ZS]; norm_num
  have hZZU : zCh611 T ≤ centerOf (uCh611 T L V) := by
    rw [← h.inf_centerOf_eq_ch616_F4 h331 h432 h512 h614 h615 h626 h6210 h6211 h6212 hlt]
    exact inf_le_right
  have haU : a ∈ uCh611 T L V := le_conjClosure _ _ ha
  have hVUN : V ⊓ uCh611 T L V ≤ Subgroup.normalizer (centerOf (uCh611 T L V) : Set G) :=
    fun y hy => hZUN (h.uCh611_le_h_F4 h331 h432 h512 h614 h615 hy.2)
  rintro γ ⟨h₀, rfl⟩ hγ
  have hmemR := h.mem_range_iff_ch619_F4 h331 h432 h512 h614 h615 h626 h6210 h6211 h6212 hlt hR hv
    hvU

  have hN : (h₀ : G) ∈ Subgroup.normalizer
      (((V ⊓ uCh611 T L V) ⊔ centerOf (uCh611 T L V) : Subgroup G) : Set G) := by
    apply mem_normalizer_of_conj_ch619
    intro g hg
    have hg' : g ∈ ((V ⊓ uCh611 T L V : Subgroup G) : Set G) *
        (centerOf (uCh611 T L V) : Set G) := by
      rw [← Subgroup.coe_mul_of_left_le_normalizer_right _ _ hVUN]
      exact hg
    obtain ⟨y, hy, z, hz, rfl⟩ := Set.mem_mul.mp hg'
    have e : (h₀ : G) * (y * z) * (h₀ : G)⁻¹ =
        ((h₀ : G) * y * (h₀ : G)⁻¹) * ((h₀ : G) * z * (h₀ : G)⁻¹) := by group
    rw [e]
    refine Subgroup.mul_mem _ ?_ (Subgroup.mem_sup_right
      ((Subgroup.mem_normalizer_iff.mp (hZUN h₀.2) z).mp hz))
    have hyR := (hmemR (piA_ch619 hR y)).mpr ⟨y, hy, rfl⟩
    obtain ⟨y', hy', hyy⟩ := (hmemR _).mp (hγ _ hyR)
    have hhy : (h₀ : G) * y * (h₀ : G)⁻¹ ∈ uCh611 T L V :=
      (Subgroup.mem_normalizer_iff.mp (hHN h₀.2) y).mp hy.2
    rw [rho_piA_ch619 hR hHN h₀ hy.2] at hyy
    have hyy' : piA_ch619 hR ((h₀ : G) * y * (h₀ : G)⁻¹) = piA_ch619 hR y' := hyy
    rw [piA_eq_iff_ch619 hR hhy hy'.2] at hyy'
    have e2 : (h₀ : G) * y * (h₀ : G)⁻¹ =
        y' * (((h₀ : G) * y * (h₀ : G)⁻¹)⁻¹ * y')⁻¹ := by group
    rw [e2]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hy')
      (Subgroup.mem_sup_right (Subgroup.inv_mem _ hyy'))

  have h5 := (h.five_sub_ch616_F4 h331 h432 h512 h614 h615 h625 h626 h6210 h6211 h6212 hlt).2
  obtain ⟨hHM, hNV, -, -⟩ := stmt6_2_9_F4 h331 h432 h512 h614 h615 G T M L V h
  have hHM' : hCh611 T ⊓ M = hCh611 T ⊓ Subgroup.normalizer (V : Set G) := hHM
  have hNV' : hCh611 T ⊓ Subgroup.normalizer (V : Set G) =
      hCh611 T ⊓ Subgroup.normalizer (ch6ZS T L V : Set G) := hNV
  have hmem : (h₀ : G) ∈ hCh611 T ⊓ Subgroup.normalizer (ch6ZS T L V : Set G) := by
    have : (h₀ : G) ∈ hCh611 T ⊓ Subgroup.normalizer
        (((V ⊓ uCh611 T L V) ⊔ centerOf (uCh611 T L V) : Subgroup G) : Set G) := ⟨h₀.2, hN⟩
    rwa [h5, hHM', hNV'] at this
  have haS' : (h₀ : G) * a * (h₀ : G)⁻¹ ∈ ch6ZS T L V :=
    (Subgroup.mem_normalizer_iff.mp hmem.2 a).mp ha
  have hhaU : (h₀ : G) * a * (h₀ : G)⁻¹ ∈ uCh611 T L V := le_conjClosure _ _ haS'
  rw [rho_piA_ch619 hR hHN h₀ haU]
  show piA_ch619 hR ((h₀ : G) * a * (h₀ : G)⁻¹) = piA_ch619 hR a
  rw [piA_eq_iff_ch619 hR hhaU haU]

  obtain ⟨z₀, hz₀Z, hz₀1⟩ : ∃ z₀ ∈ zCh611 T, z₀ ≠ 1 := by
    by_contra hcon
    push Not at hcon
    have : zCh611 T = ⊥ := (Subgroup.eq_bot_iff_forall _).mpr hcon
    rw [this, Subgroup.card_bot] at hZ2
    omega
  have hcz : ∀ z ∈ zCh611 T, (h₀ : G) * z * (h₀ : G)⁻¹ = z := fun z hz => by
    rw [← Subgroup.mem_centralizer_iff.mp h₀.2 z hz, mul_inv_cancel_right]
  rcases L128P.eq_of_mem_four hZZS hZ2 hZS4 hz₀Z hz₀1 haZ ha haS' with e | e | e | e
  · exfalso
    apply haZ
    have : a = 1 := by
      calc a = (h₀ : G)⁻¹ * ((h₀ : G) * a * (h₀ : G)⁻¹) * h₀ := by group
        _ = 1 := by rw [e]; group
    rw [this]
    exact (zCh611 T).one_mem
  · exfalso
    apply haZ
    have : a = z₀ := by
      calc a = (h₀ : G)⁻¹ * ((h₀ : G) * a * (h₀ : G)⁻¹) * h₀ := by group
        _ = (h₀ : G)⁻¹ * ((h₀ : G) * z₀ * (h₀ : G)⁻¹) * h₀ := by rw [e, hcz z₀ hz₀Z]
        _ = z₀ := by group
    rw [this]
    exact hz₀Z
  · rw [e, inv_mul_cancel]
    exact Subgroup.one_mem _
  · rw [e]
    have hz₀U := hZZU hz₀Z
    have hc := Subgroup.mem_centralizer_iff.mp hz₀U.2 a haU
    have e3 : (z₀ * a)⁻¹ * a = z₀⁻¹ := by
      calc (z₀ * a)⁻¹ * a = a⁻¹ * z₀⁻¹ * a := by group
        _ = a⁻¹ * (a * z₀⁻¹) := by
            rw [mul_assoc]
            congr 1
            have : a * z₀ = z₀ * a := hc
            calc z₀⁻¹ * a = z₀⁻¹ * (a * z₀) * z₀⁻¹ := by group
              _ = z₀⁻¹ * (z₀ * a) * z₀⁻¹ := by rw [this]
              _ = a * z₀⁻¹ := by group
        _ = z₀⁻¹ := by group
    rw [e3]
    exact Subgroup.inv_mem _ hz₀U

theorem four_le_finrank_ch619_F4 (h331 : Stmt3_3_1_F4) (h432 : Stmt4_3_2_F4) (h512 : Stmt5_1_2_F4)
    (h614 : Stmt6_1_4_F4) (h615 : Stmt6_1_5_F4) (h626 : Stmt6_2_6_F4) (h6210 : Stmt6_2_10_F4)
    (h6211 : Stmt6_2_11_F4) (h6212 : Stmt6_2_12_F4) (hlt : ch6ZS T L V < V ⊓ uCh611 T L V)
    (hR : IsSymplecticRealization (hCh611 T) (uCh611 T L V) (centerOf (uCh611 T L V)) A B β ρ) :
    4 ≤ Module.finrank (ZMod 2) A := by
  have h16 := h.sixteen_le_ch619_F4 h331 h432 h512 h614 h615 h626 h6210 h6211 h6212 hlt
  have hker : β.ker = (centerOf (uCh611 T L V)).subgroupOf (uCh611 T L V) := by
    ext u
    rw [MonoidHom.mem_ker, hR.2.1 u, Subgroup.mem_subgroupOf]
  have hcardA : Nat.card A = (centerOf (uCh611 T L V)).relIndex (uCh611 T L V) := by
    have h1 := Subgroup.index_ker β
    rw [hker, MonoidHom.range_eq_top.mpr hR.1, Subgroup.card_top] at h1
    rw [show (centerOf (uCh611 T L V)).relIndex (uCh611 T L V) =
      ((centerOf (uCh611 T L V)).subgroupOf (uCh611 T L V)).index from rfl, h1]
    exact (Nat.card_congr Multiplicative.toAdd.symm)
  have : Module.Finite (ZMod 2) A := Module.Finite.of_finite
  have h2 := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := A)
  rw [Nat.card_zmod, hcardA] at h2
  by_contra hlt4
  push Not at hlt4
  have : 2 ^ Module.finrank (ZMod 2) A ≤ 2 ^ 3 := Nat.pow_le_pow_right (by norm_num) (by omega)
  omega

theorem map_eq_bot_ch619_F4 (h331 : Stmt3_3_1_F4) (h432 : Stmt4_3_2_F4) (h512 : Stmt5_1_2_F4)
    (h614 : Stmt6_1_4_F4) (h615 : Stmt6_1_5_F4)
    (hR : IsSymplecticRealization (hCh611 T) (uCh611 T L V) (centerOf (uCh611 T L V)) A B β ρ)
    {l : G} (hl : l ∈ lsCh617 T L V) (hZU : centerOf (uCh611 T L V) = zCh611 T) :
    ((conjSubgroup (centerOf (uCh611 T L V)) l).subgroupOf (hCh611 T)).map ρ = ⊥ := by
  have hHN := hCh611_le_normalizer_u T L V
  have hZZS := h.omega_le_ZS_F4 h331 h432 h512 h614 h615
  rw [eq_bot_iff]
  rintro _ ⟨y, hy0, rfl⟩
  have hy := Subgroup.mem_subgroupOf.mp hy0
  rw [hZU, mem_conjSubgroup_iff] at hy
  have hlN := (ls_le_ch617 hl).2
  have hyS : (y : G) ∈ ch6ZS T L V := by
    have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hlN) _).mp (hZZS hy)
    simpa [mul_assoc] using this
  have hyU : (y : G) ∈ uCh611 T L V := le_conjClosure _ _ hyS
  rw [Subgroup.mem_bot, rho_eq_one_ch619 hR hHN y (h.U_le_CH_ch616_F4 h331 h432 h512 h614 h615 hyU)]

end Hyp6Sec2

end CFSG.Quasithin.H13
