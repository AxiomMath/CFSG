module

public import CFSG.GH74.GLS.C3.Layer2.L5A2
public import CFSG.GH74.GLS.C3.Layer2.L4PartB6

public section

namespace CFSG.GH74.GLS.C3.Layer2.L5

open Equiv Perm Subgroup CFSG CFSG.ABGLocalTools CFSG.GH74.GLS CFSG.GH74.GLS.C3.Prop121
  CFSG.GH74.GLS.C3.Layer2 CFSG.GH74.GLS.C3.Layer2.Model
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {x : G} {K T Q S : Subgroup G} {a : G}

theorem isElementaryAbelian_of_comm_sq {H : Type*} [Group H] (A : Subgroup H)
    (hc : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a) (hs : ∀ a ∈ A, a * a = 1) :
    IsElementaryAbelian 2 ↥A := by
  refine { toIsMulCommutative := ⟨⟨fun a b => Subtype.ext (hc a a.2 b b.2)⟩⟩, exponent_dvd_p := ?_ }
  refine Monoid.exponent_dvd_iff_forall_pow_eq_one.2 ?_
  intro a
  apply Subtype.ext
  show (a : H) ^ 2 = 1
  rw [pow_two]
  exact hs a a.2

theorem no_commuting_conj
    (h : IsAConfig 5 x K T Q S a) (c : Coord5 h) (hG4 : pRank 2 G ≤ 4)
    {u : G} (hu : u ∈ Q) (hu1 : u ≠ 1) {g : G} (hgu : ∀ k ∈ K, Commute (g * k * g⁻¹) u)
    (hcomm : ∀ k ∈ K, ∀ k₀ ∈ K, k * (g * k₀ * g⁻¹) = (g * k₀ * g⁻¹) * k) : False := by
  have hKu : ∀ k ∈ K, Commute k u := fun k hk => ((h.mem_Q_iff u).1 hu).2 k hk
  have hu2 : u ^ 2 = 1 := h.Q_sq hu
  have hZK' : ∀ k ∈ K, (∀ k₀ ∈ K, (g * k₀ * g⁻¹) * (g * k * g⁻¹) =
      (g * k * g⁻¹) * (g * k₀ * g⁻¹)) → g * k * g⁻¹ = 1 := by
    intro k hk hc'
    have hk1 : k = 1 := K_center_trivial h hk fun k₀ hk₀ => by
      have := hc' k₀ hk₀
      have h2 : g * (k₀ * k) * g⁻¹ = g * (k * k₀) * g⁻¹ := by
        calc g * (k₀ * k) * g⁻¹ = (g * k₀ * g⁻¹) * (g * k * g⁻¹) := by group
          _ = (g * k * g⁻¹) * (g * k₀ * g⁻¹) := this
          _ = g * (k * k₀) * g⁻¹ := by group
      simpa using h2
    rw [hk1]
    group
  have hE₁K : T ⊓ K ≤ K := inf_le_right
  have hE₁4 : Nat.card ↥(T ⊓ K) = 4 := by
    rw [Coord5.P_eq_lift (c := c)]
    exact Coord5.card_lift_Pm
  have hE₁el : IsElementaryAbelian 2 ↥(T ⊓ K) := by
    refine isElementaryAbelian_of_comm_sq _ (fun a ha b hb => ?_) (fun a ha => ?_)
    · exact Coord5.lift_comm (c := c) (M := Pm) (fun p hp q hq => Rm_comm p (Pm_le_Rm hp) q
        (Pm_le_Rm hq)) ((SetLike.ext_iff.1 (Coord5.P_eq_lift (c := c)) a).1 ha)
        ((SetLike.ext_iff.1 (Coord5.P_eq_lift (c := c)) b).1 hb)
    · exact Coord5.lift_sq (c := c) (M := Pm) (fun p hp => Rm_sq p (Pm_le_Rm hp))
        ((SetLike.ext_iff.1 (Coord5.P_eq_lift (c := c)) a).1 ha)
  set E₁ := T ⊓ K with hE₁
  set E₂ := E₁.map (MulAut.conj g).toMonoidHom with hE₂
  have hE₂el : IsElementaryAbelian 2 E₂ := IsElementaryAbelian.map _
  have hE₂4 : Nat.card E₂ = 4 := by
    rw [hE₂, Subgroup.card_map_of_injective (MulAut.conj g).injective, hE₁4]
  have hmemE₂ : ∀ y ∈ E₂, ∃ k ∈ K, y = g * k * g⁻¹ := by
    rintro _ ⟨k, hk, rfl⟩
    exact ⟨k, hE₁K hk, by simp [MulAut.conj_apply]⟩
  have hzel : IsElementaryAbelian 2 (zpowers u) := IsElementaryAbelian.zpowers_of_pow_eq_one hu2
  have hz2 : Nat.card (zpowers u) = 2 := by
    rw [Nat.card_zpowers, orderOf_eq_prime hu2 hu1]
  have huE₂ : zpowers u ≤ centralizer (E₂ : Set G) := by
    rw [zpowers_le, mem_centralizer_iff]
    intro y hy
    obtain ⟨k, hk, rfl⟩ := hmemE₂ y hy
    exact (hgu k hk).eq
  set B := E₂ ⊔ zpowers u with hB
  have hBel : IsElementaryAbelian 2 B := IsElementaryAbelian.sup_of_le_centralizer huE₂
  have hBK : B ≤ centralizer (K : Set G) := by
    refine sup_le ?_ (zpowers_le.2 (mem_centralizer_iff.2 fun k hk => (hKu k hk).eq))
    intro y hy
    rw [mem_centralizer_iff]
    intro k hk
    obtain ⟨k₀, hk₀, rfl⟩ := hmemE₂ y hy
    exact hcomm k hk k₀ hk₀
  have hBE₁ : B ≤ centralizer (E₁ : Set G) := hBK.trans (Subgroup.centralizer_le hE₁K)
  set W := E₁ ⊔ B with hW
  have hWel : IsElementaryAbelian 2 W := IsElementaryAbelian.sup_of_le_centralizer hBE₁
  have hinf₁ : E₂ ⊓ zpowers u = ⊥ := by
    rw [eq_bot_iff]
    rintro y ⟨hyE, hyq⟩
    obtain ⟨k, hk, rfl⟩ := hmemE₂ y hyE
    rw [Subgroup.mem_bot]
    refine hZK' k hk fun k₀ hk₀ => ?_
    have hc : g * k * g⁻¹ ∈ centralizer ({g * k₀ * g⁻¹} : Set G) := by
      have huc : u ∈ centralizer ({g * k₀ * g⁻¹} : Set G) :=
        mem_centralizer_singleton_iff.2 (hgu k₀ hk₀).eq.symm
      exact (zpowers_le.2 huc) hyq
    exact (mem_centralizer_singleton_iff.1 hc).symm
  have hinf₂ : E₁ ⊓ B = ⊥ := by
    rw [eq_bot_iff]
    rintro y ⟨hyE, hyB⟩
    rw [Subgroup.mem_bot]
    exact K_center_trivial h (hE₁K hyE) fun k hk => mem_centralizer_iff.1 (hBK hyB) k hk
  have hcB := card_mul_card_le_inf_mul_of_comm E₂ (zpowers u) B le_sup_left le_sup_right
    (fun v hv w hw => setLike_mul_comm hv hw)
  rw [hinf₁, Subgroup.card_bot, one_mul, hE₂4, hz2] at hcB
  have hcW := card_mul_card_le_inf_mul_of_comm E₁ B W le_sup_left le_sup_right
    (fun v hv w hw => setLike_mul_comm hv hw)
  rw [hinf₂, Subgroup.card_bot, one_mul, hE₁4] at hcW
  have hWle := card_elemAb_le_pow_pRank W
  have hpow : 2 ^ pRank 2 G ≤ 2 ^ 4 := Nat.pow_le_pow_right (by norm_num) hG4
  omega

theorem cent_normalizes_K
    (h : IsAConfig 5 x K T Q S a) (c : Coord5 h) (hG4 : pRank 2 G ≤ 4)
    {q : G} (hqQ : q ∈ Q) (hq1 : q ≠ 1) {r : G} (hr : r ∈ centralizer ({q} : Set G)) :
    ∀ k ∈ K, r * k * r⁻¹ ∈ K := by
  obtain ⟨-, -, -, hy⟩ := h.terminal
  have hq2 : orderOf q = 2 := orderOf_eq_prime (h.Q_sq hqQ) hq1
  have hKq : ∀ k ∈ K, Commute k q := fun k hk => ((h.mem_Q_iff q).1 hqQ).2 k hk
  obtain ⟨hKC1, hKcomp⟩ := hy q hq2 (mem_centralizer_iff.2 fun k hk => (hKq k hk).eq)
  set C₁ := centralizer ({q} : Set G) with hC₁
  set r' : C₁ := ⟨r, hr⟩ with hr'
  have hL' : IsComponent ((K.subgroupOf C₁).map (MulAut.conj r').toMonoidHom) :=
    CFSG.LocalCores.isComponent_map_mulEquiv (MulAut.conj r') hKcomp
  rcases CFSG.LocalCores.distinct_components_commute hKcomp hL' with heq | hcomm
  · intro k hk
    have hmem : (MulAut.conj r').toMonoidHom ⟨k, hKC1 hk⟩ ∈
        (K.subgroupOf C₁).map (MulAut.conj r').toMonoidHom :=
      Subgroup.mem_map_of_mem _ (show (⟨k, hKC1 hk⟩ : C₁) ∈ K.subgroupOf C₁ from hk)
    rw [← heq] at hmem
    exact hmem
  exfalso
  have hcomm' : ∀ k ∈ K, ∀ k₀ ∈ K, k * (r * k₀ * r⁻¹) = (r * k₀ * r⁻¹) * k := by
    intro k hk k₀ hk₀
    have hmem : ⁅(⟨k, hKC1 hk⟩ : C₁), (MulAut.conj r').toMonoidHom ⟨k₀, hKC1 hk₀⟩⁆ ∈
        ⁅K.subgroupOf C₁, (K.subgroupOf C₁).map (MulAut.conj r').toMonoidHom⁆ :=
      Subgroup.commutator_mem_commutator (show (⟨k, hKC1 hk⟩ : C₁) ∈ K.subgroupOf C₁ from hk)
        (Subgroup.mem_map_of_mem _ (show (⟨k₀, hKC1 hk₀⟩ : C₁) ∈ K.subgroupOf C₁ from hk₀))
    rw [hcomm, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at hmem
    have := congrArg Subtype.val hmem
    simpa [MulAut.conj_apply, hr'] using this
  have hrq : Commute r q := mem_centralizer_singleton_iff.1 hr
  exact no_commuting_conj h c hG4 hqQ hq1 (g := r)
    (fun k hk => (hrq.mul_left (hKq k hk)).mul_left hrq.inv_left) hcomm'

@[expose] def cj (g : G) (H : Subgroup G) : Subgroup G := H.map (MulAut.conj g).toMonoidHom

omit [Finite G] in
theorem mem_cj {g : G} {H : Subgroup G} {y : G} : y ∈ cj g H ↔ ∃ z ∈ H, g * z * g⁻¹ = y := by
  simp only [cj, Subgroup.mem_map, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]

omit [Finite G] in
theorem card_cj (g : G) (H : Subgroup G) : Nat.card (cj g H) = Nat.card H :=
  Subgroup.card_map_of_injective (MulAut.conj g).injective

theorem mem_cj_self {g : G} {H : Subgroup G} {z : G} (hz : z ∈ H) : g * z * g⁻¹ ∈ cj g H :=
  mem_cj.2 ⟨z, hz, rfl⟩

theorem K_conj_le
    (h : IsAConfig 5 x K T Q S a) (c : Coord5 h) (hG4 : pRank 2 G ≤ 4) {q u g : G}
    (hq : q ∈ Q) (hq1 : q ≠ 1) (hu : u ∈ Q) (hu1 : u ≠ 1) (hgu : g * q * g⁻¹ = u) :
    ∀ k ∈ K, g * k * g⁻¹ ∈ K := by
  have hKq : ∀ k ∈ K, Commute k q := fun k hk => ((h.mem_Q_iff q).1 hq).2 k hk
  have hKu : ∀ k ∈ K, Commute k u := fun k hk => ((h.mem_Q_iff u).1 hu).2 k hk
  have hq' : g⁻¹ * u * g = q := by rw [← hgu]; group
  have hconj1 : ∀ r ∈ centralizer ({u} : Set G), g⁻¹ * r * g ∈ centralizer ({q} : Set G) := by
    intro r hr
    rw [mem_centralizer_singleton_iff] at hr ⊢
    rw [← hq']
    calc g⁻¹ * r * g * (g⁻¹ * u * g) = g⁻¹ * (r * u) * g := by group
      _ = g⁻¹ * (u * r) * g := by rw [hr]
      _ = (g⁻¹ * u * g) * (g⁻¹ * r * g) := by group
  set K' := cj g K with hK'
  have hmemK' : ∀ z ∈ K', ∃ k ∈ K, z = g * k * g⁻¹ := by
    intro z hz
    obtain ⟨k, hk, rfl⟩ := mem_cj.1 hz
    exact ⟨k, hk, rfl⟩
  have hK'norm : ∀ r ∈ centralizer ({u} : Set G), ∀ z ∈ K', r * z * r⁻¹ ∈ K' := by
    intro r hr z hz
    obtain ⟨k, hk, rfl⟩ := hmemK' z hz
    have h1 := cent_normalizes_K h c hG4 hq hq1 (hconj1 r hr) k hk
    refine mem_cj.2 ⟨_, h1, ?_⟩
    group
  have hKC : ∀ k ∈ K, k ∈ centralizer ({u} : Set G) := fun k hk =>
    mem_centralizer_singleton_iff.2 (hKu k hk).eq
  have hK'C : ∀ z ∈ K', z ∈ centralizer ({u} : Set G) := by
    intro z hz
    obtain ⟨k, hk, rfl⟩ := hmemK' z hz
    rw [mem_centralizer_singleton_iff, ← hgu]
    calc g * k * g⁻¹ * (g * q * g⁻¹) = g * (k * q) * g⁻¹ := by group
      _ = g * (q * k) * g⁻¹ := by rw [(hKq k hk).eq]
      _ = g * q * g⁻¹ * (g * k * g⁻¹) := by group
  have hKnorm : ∀ k ∈ K, ∀ z ∈ K', k * z * k⁻¹ ∈ K' := fun k hk z hz =>
    hK'norm k (hKC k hk) z hz
  have : IsSimpleGroup ↥K := (h.K_equiv_alt.some).isSimpleGroup
  have hMn : ((K ⊓ K').subgroupOf K).Normal := ⟨fun z hz k => by
    rw [Subgroup.mem_subgroupOf] at hz ⊢
    refine ⟨?_, ?_⟩
    · exact K.mul_mem (K.mul_mem k.2 hz.1) (K.inv_mem k.2)
    · exact hKnorm k k.2 z hz.2⟩
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal ((K ⊓ K').subgroupOf K) with hb | ht
  ·
    exfalso
    have hcomm : ∀ k ∈ K, ∀ k₀ ∈ K, k * (g * k₀ * g⁻¹) = (g * k₀ * g⁻¹) * k := by
      intro k hk k₀ hk₀
      set e := g * k₀ * g⁻¹ with he
      have heK' : e ∈ K' := mem_cj_self hk₀
      have h1 : k * e * k⁻¹ * e⁻¹ ∈ K' :=
        mul_mem (hKnorm k hk e heK') (inv_mem heK')
      have h2 : k * e * k⁻¹ * e⁻¹ ∈ K := by
        have h3 := cent_normalizes_K h c hG4 hu hu1 (hK'C e heK') k⁻¹ (inv_mem hk)
        have : k * e * k⁻¹ * e⁻¹ = k * (e * k⁻¹ * e⁻¹) := by group
        rw [this]
        exact mul_mem hk h3
      have h4 : (⟨k * e * k⁻¹ * e⁻¹, h2⟩ : ↥K) ∈ (K ⊓ K').subgroupOf K :=
        Subgroup.mem_subgroupOf.2 ⟨h2, h1⟩
      rw [hb, Subgroup.mem_bot] at h4
      have h5 : k * e * k⁻¹ * e⁻¹ = 1 := congrArg Subtype.val h4
      calc k * e = (k * e * k⁻¹ * e⁻¹) * (e * k) := by group
        _ = e * k := by rw [h5, one_mul]
    exact no_commuting_conj h c hG4 hu hu1 (g := g)
      (fun k hk => by
        have := mem_centralizer_singleton_iff.1 (hK'C _ (mem_cj_self hk))
        exact this) hcomm
  ·
    have hKle : K ≤ K' := fun k hk => by
      have : (⟨k, hk⟩ : ↥K) ∈ (K ⊓ K').subgroupOf K := by rw [ht]; trivial
      exact (Subgroup.mem_subgroupOf.1 this).2
    have hKeq : K = K' := Subgroup.eq_of_le_of_card_ge hKle (by rw [hK', card_cj])
    intro k hk
    rw [hKeq]
    exact mem_cj_self hk

theorem TI_Q
    (h : IsAConfig 5 x K T Q S a) (c : Coord5 h) (hG4 : pRank 2 G ≤ 4) {g : G}
    (hg : g ∈ normalizer ((c.lift Rm : Subgroup G) : Set G)) {q : G} (hq : q ∈ Q) (hq1 : q ≠ 1)
    (hgq : g * q * g⁻¹ ∈ Q) : cj g Q = Q := by
  have hu1 : g * q * g⁻¹ ≠ 1 := by
    intro h1
    apply hq1
    have : q = g⁻¹ * (g * q * g⁻¹) * g := by group
    rw [this, h1]
    group
  have hK := K_conj_le h c hG4 hq hq1 hgq hu1 rfl
  have hKeq : cj g K = K :=
    Subgroup.eq_of_le_of_card_ge (fun z hz => by
      obtain ⟨k, hk, rfl⟩ := mem_cj.1 hz
      exact hK k hk) (by rw [card_cj])
  have hKinv : ∀ k ∈ K, g⁻¹ * k * g ∈ K := by
    intro k hk
    have hk' : k ∈ cj g K := by rw [hKeq]; exact hk
    obtain ⟨k₀, hk₀, hkk⟩ := mem_cj.1 hk'
    have : g⁻¹ * k * g = k₀ := by rw [← hkk]; group
    rw [this]
    exact hk₀
  have hle : cj g Q ≤ Q := by
    intro y hy
    obtain ⟨q', hq', rfl⟩ := mem_cj.1 hy
    have hq'R : q' ∈ c.lift Rm :=
      (Coord5.lift_mono Qm_le_Rm) ((SetLike.ext_iff.1 (Coord5.Q_eq_lift (c := c)) q').1 hq')
    have hR : g * q' * g⁻¹ ∈ c.lift Rm := (mem_normalizer_iff.1 hg q').1 hq'R
    refine Coord5.Rg_inf_centK (c := c) hR (fun k hk => ?_)
    have hkq' := ((h.mem_Q_iff q').1 hq').2 (g⁻¹ * k * g) (hKinv k hk)
    calc g * q' * g⁻¹ * k = g * (q' * (g⁻¹ * k * g)) * g⁻¹ := by group
      _ = g * ((g⁻¹ * k * g) * q') * g⁻¹ := by rw [hkq'.symm]
      _ = k * (g * q' * g⁻¹) := by group
  exact Subgroup.eq_of_le_of_card_ge hle (by rw [card_cj])

theorem eq_of_isSylowOf_le {P D C : Subgroup G} (hP : IsSylowOf 2 P C) (hDC : D ≤ C)
    (hD : IsPGroup 2 ↥D) (hPD : P ≤ D) : D = P := by
  obtain ⟨hPC, -, hidx⟩ := isSylowOf_iff.1 hP
  have h1 := Subgroup.relIndex_mul_relIndex P D C hPD hDC
  have hnd : ¬ 2 ∣ P.relIndex D := fun hd => hidx (h1 ▸ Dvd.dvd.mul_right hd _)
  obtain ⟨n, hn⟩ := hD.index (P.subgroupOf D)
  have hrel : P.relIndex D = 2 ^ n := hn
  have hn0 : n = 0 := by
    by_contra hne
    exact hnd (hrel ▸ dvd_pow_self 2 hne)
  rw [hn0, pow_zero, Subgroup.relIndex_eq_one] at hrel
  exact le_antisymm hrel hPD

theorem klein_elems {V : Subgroup G} (hV : Nat.card V = 4) (hsq : ∀ z ∈ V, z * z = 1)
    {u v : G} (hu : u ∈ V) (hv : v ∈ V) (hu1 : u ≠ 1) (hv1 : v ≠ 1) (huv : u ≠ v) :
    ∀ z ∈ V, z = 1 ∨ z = u ∨ z = v ∨ z = u * v := by
  classical
  intro z hz
  have hu2 : u * u = 1 := hsq u hu
  have huv1 : u * v ≠ 1 := by
    intro h1
    apply huv
    have : v = u⁻¹ * (u * v) := by group
    rw [this, h1, mul_one]
    exact (inv_eq_of_mul_eq_one_right hu2).symm
  have huvu : u * v ≠ u := by
    intro h1
    apply hv1
    have : v = u⁻¹ * (u * v) := by group
    rw [this, h1]
    group
  have huvv : u * v ≠ v := by
    intro h1
    apply hu1
    have : u = (u * v) * v⁻¹ := by group
    rw [this, h1]
    group
  let _inst : Fintype G := Fintype.ofFinite G
  let Vf : Finset G := Finset.univ.filter (· ∈ V)
  have hVf : Vf.card = 4 := by
    have h1 : Vf.card = Fintype.card ↥V := (Fintype.card_subtype _).symm
    rw [h1, ← Nat.card_eq_fintype_card, hV]
  have h4 : ({1, u, v, u * v} : Finset G).card = 4 := by
    rw [Finset.card_insert_of_notMem (by simp [hu1.symm, hv1.symm, huv1.symm]),
      Finset.card_insert_of_notMem (by simp [huv, huvu.symm]),
      Finset.card_insert_of_notMem (by simp [huvv.symm]), Finset.card_singleton]
  have hsub : ({1, u, v, u * v} : Finset G) ⊆ Vf := by
    intro e he
    simp only [Finset.mem_insert, Finset.mem_singleton] at he
    simp only [Vf, Finset.mem_filter, Finset.mem_univ, true_and]
    rcases he with rfl | rfl | rfl | rfl
    · exact V.one_mem
    · exact hu
    · exact hv
    · exact V.mul_mem hu hv
  have heq := Finset.eq_of_subset_of_card_le hsub (by rw [h4, hVf])
  have hzmem : z ∈ ({1, u, v, u * v} : Finset G) := by
    rw [heq]
    simpa [Vf] using hz
  simpa [Finset.mem_insert, Finset.mem_singleton] using hzmem

theorem Q_elems (h : IsAConfig 5 x K T Q S a) {q : G} (hq : q ∈ Q) (hq1 : q ≠ 1) (hqx : q ≠ x) :
    ∀ z ∈ Q, z = 1 ∨ z = x ∨ z = q ∨ z = x * q :=
  klein_elems h.card_Q (fun z hz => by rw [← pow_two]; exact h.Q_sq hz) h.x_mem_Q hq h.x_ne_one
    hq1 hqx.symm

theorem exists_klein_basis {V : Subgroup G} (hV : Nat.card V = 4) :
    ∃ u v : G, u ∈ V ∧ v ∈ V ∧ u ≠ 1 ∧ v ≠ 1 ∧ u ≠ v := by
  classical
  have h1 : ∃ u ∈ V, u ≠ 1 := by
    by_contra hcon
    push Not at hcon
    have : V = ⊥ := by
      rw [eq_bot_iff]
      intro z hz
      exact Subgroup.mem_bot.2 (hcon z hz)
    rw [this, Subgroup.card_bot] at hV
    omega
  obtain ⟨u, hu, hu1⟩ := h1
  have h2 : ∃ v ∈ V, v ≠ 1 ∧ v ≠ u := by
    by_contra hcon
    push Not at hcon
    let _inst : Fintype G := Fintype.ofFinite G
    let Vf : Finset G := Finset.univ.filter (· ∈ V)
    have hVf : Vf.card = 4 := by
      have h1 : Vf.card = Fintype.card ↥V := (Fintype.card_subtype _).symm
      rw [h1, ← Nat.card_eq_fintype_card, hV]
    have hsub : Vf ⊆ ({1, u} : Finset G) := by
      intro e he
      simp only [Vf, Finset.mem_filter, Finset.mem_univ, true_and] at he
      simp only [Finset.mem_insert, Finset.mem_singleton]
      by_cases he1 : e = 1
      · exact Or.inl he1
      · exact Or.inr (hcon e he he1)
    have h3 := Finset.card_le_card hsub
    have h4 : ({1, u} : Finset G).card ≤ 2 := Finset.card_le_two
    omega
  obtain ⟨v, hv, hv1, hvu⟩ := h2
  exact ⟨u, v, hu, hv, hu1, hv1, hvu.symm⟩

theorem U_fixes_x (h : IsAConfig 5 x K T Q S a) {U : Subgroup G} (hTU : T ≤ U)
    (hUQ : ∀ u ∈ U, ∀ z, z ∈ Q ↔ u * z * u⁻¹ ∈ Q) (hU : IsPGroup 2 ↥U) :
    ∀ u ∈ U, u * x * u⁻¹ = x := by
  classical
  obtain ⟨y, hyT, hyo, -, q, hqQ, hyq⟩ := h.fiveCase rfl
  by_contra hne
  push Not at hne
  obtain ⟨u, huU, hux⟩ := hne
  have hx1 := h.x_ne_one
  have hxQ := h.x_mem_Q
  have hyC := h.T_le_C hyT
  have hyx : y * x * y⁻¹ = x := by
    have := mem_centralizer_singleton_iff.1 hyC
    calc y * x * y⁻¹ = (x * y) * y⁻¹ := by rw [this]
      _ = x := by group
  have hx₁Q : u * x * u⁻¹ ∈ Q := (hUQ u huU x).1 hxQ
  have hx₁1 : u * x * u⁻¹ ≠ 1 := by
    intro h1
    apply hx1
    have : x = u⁻¹ * (u * x * u⁻¹) * u := by group
    rw [this, h1]
    group
  have hQel := Q_elems h hx₁Q hx₁1 hux
  have hy_x₁ : y * (u * x * u⁻¹) * y⁻¹ = x * (u * x * u⁻¹) := by
    have hyx₁Q : y * (u * x * u⁻¹) * y⁻¹ ∈ Q := h.Q_normal y hyC _ hx₁Q
    rcases hQel _ hyx₁Q with h1 | h1 | h1 | h1
    · exfalso
      apply hx₁1
      have : u * x * u⁻¹ = y⁻¹ * (y * (u * x * u⁻¹) * y⁻¹) * y := by group
      rw [this, h1]
      group
    · exfalso
      apply hux
      have hyx' : y⁻¹ * x * y = x := by
        calc y⁻¹ * x * y = y⁻¹ * (y * x * y⁻¹) * y := by rw [hyx]
          _ = x := by group
      have : u * x * u⁻¹ = y⁻¹ * (y * (u * x * u⁻¹) * y⁻¹) * y := by group
      rw [this, h1]
      exact hyx'
    · exfalso
      apply hyq
      have hc₁ : y * (u * x * u⁻¹) = (u * x * u⁻¹) * y := by
        have : y * (u * x * u⁻¹) = (y * (u * x * u⁻¹) * y⁻¹) * y := by group
        rw [this, h1]
      have hc₂ : y * x = x * y := by
        have : y * x = (y * x * y⁻¹) * y := by group
        rw [this, hyx]
      rcases hQel q hqQ with h2 | h2 | h2 | h2
      · rw [h2]; simp
      · rw [h2]; exact hc₂
      · rw [h2]; exact hc₁
      · rw [h2]
        calc y * (x * (u * x * u⁻¹)) = (y * x) * (u * x * u⁻¹) := by group
          _ = (x * y) * (u * x * u⁻¹) := by rw [hc₂]
          _ = x * (y * (u * x * u⁻¹)) := by group
          _ = x * ((u * x * u⁻¹) * y) := by rw [hc₁]
          _ = (x * (u * x * u⁻¹)) * y := by group
    · exact h1
  let xU : ↥U := ⟨x, hTU h.x_mem_T⟩
  let x₁U : ↥U := ⟨u * x * u⁻¹, U.mul_mem (U.mul_mem huU (hTU h.x_mem_T)) (U.inv_mem huU)⟩
  let x₂U : ↥U := ⟨x * (u * x * u⁻¹), U.mul_mem (hTU h.x_mem_T)
    (U.mul_mem (U.mul_mem huU (hTU h.x_mem_T)) (U.inv_mem huU))⟩
  let cls : Set ↥U := {z | ∃ c : ↥U, c * xU * c⁻¹ = z}
  have hcard := L4.PartB6.card_conj_mul_card_centralizer xU
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.1 hU
  have hdvd : cls.ncard ∣ 2 ^ k := ⟨_, by rw [← hk, ← hcard]⟩
  have hcls : cls = {xU, x₁U, x₂U} := by
    ext z
    constructor
    · rintro ⟨c, rfl⟩
      have hcQ : (c : G) * x * (c : G)⁻¹ ∈ Q := (hUQ c c.2 x).1 hxQ
      have hc1 : (c : G) * x * (c : G)⁻¹ ≠ 1 := by
        intro h1
        apply hx1
        have : x = (c : G)⁻¹ * ((c : G) * x * (c : G)⁻¹) * c := by group
        rw [this, h1]
        group
      rcases hQel _ hcQ with h1 | h1 | h1 | h1
      · exact absurd h1 hc1
      · left
        exact Subtype.ext h1
      · right; left
        exact Subtype.ext h1
      · right; right
        exact Subtype.ext h1
    · rintro (rfl | rfl | rfl)
      · exact ⟨1, by simp⟩
      · exact ⟨⟨u, huU⟩, rfl⟩
      · refine ⟨⟨y, hTU hyT⟩ * ⟨u, huU⟩, ?_⟩
        apply Subtype.ext
        show y * u * x * (y * u)⁻¹ = x * (u * x * u⁻¹)
        rw [← hy_x₁]
        group
  have hd1 : xU ≠ x₁U := fun h1 => hux (congrArg Subtype.val h1).symm
  have hd2 : xU ≠ x₂U := by
    intro h1
    apply hx₁1
    have := congrArg Subtype.val h1
    have h3 : x * 1 = x * (u * x * u⁻¹) := by rw [mul_one]; exact this
    exact (mul_left_cancel h3).symm
  have hd3 : x₁U ≠ x₂U := by
    intro h1
    apply hx1
    have := congrArg Subtype.val h1
    have h3 : 1 * (u * x * u⁻¹) = x * (u * x * u⁻¹) := by rw [one_mul]; exact this
    exact (mul_right_cancel h3).symm
  have h3 : cls.ncard = 3 := Set.ncard_eq_three.2 ⟨xU, x₁U, x₂U, hd1, hd2, hd3, hcls⟩
  rw [h3] at hdvd
  have := Nat.Prime.dvd_of_dvd_pow Nat.prime_three hdvd
  omega

theorem T_sylow_NQ (h : IsAConfig 5 x K T Q S a) (c : Coord5 h) :
    IsSylowOf 2 T (normalizer ((c.lift Rm : Subgroup G) : Set G) ⊓ normalizer (Q : Set G)) := by
  set H := normalizer ((c.lift Rm : Subgroup G) : Set G) ⊓ normalizer (Q : Set G) with hH
  have hTH : T ≤ H := by
    intro t ht
    refine ⟨?_, h.C_le_normalizer_Q (h.T_le_C ht)⟩
    refine mem_normalizer_iff.2 (fun y => ?_)
    constructor
    · exact fun hy => Coord5.Rg_norm_T (c := c) ht hy
    · intro hy
      have h1 := Coord5.Rg_norm_T (c := c) (inv_mem ht) hy
      have e : t⁻¹ * (t * y * t⁻¹) * t⁻¹⁻¹ = y := by group
      rw [e] at h1
      exact h1
  have hTp : IsPGroup 2 ↥T := (isSylowOf_iff.1 h.sylowT).2.1
  obtain ⟨Q', hQ'⟩ := (hTp.comap_subtype (K := H)).exists_le_sylow
  set U := Subgroup.map H.subtype (Q' : Subgroup ↥H) with hU
  have hTU : T ≤ U := by
    intro y hy
    exact ⟨⟨y, hTH hy⟩, hQ' (show (⟨y, hTH hy⟩ : ↥H) ∈ T.comap H.subtype from hy), rfl⟩
  have hUH : U ≤ H := by
    rintro _ ⟨z, -, rfl⟩
    exact z.2
  have hUp : IsPGroup 2 ↥U :=
    (Q'.isPGroup').of_equiv (Subgroup.equivMapOfInjective _ H.subtype H.subtype_injective)
  have hUQ : ∀ u ∈ U, ∀ z, z ∈ Q ↔ u * z * u⁻¹ ∈ Q := fun u hu z =>
    mem_normalizer_iff.1 (hUH hu).2 z
  have hfix := U_fixes_x h hTU hUQ hUp
  have hUC : U ≤ centralizer ({x} : Set G) := by
    intro u hu
    rw [mem_centralizer_singleton_iff]
    have := hfix u hu
    calc u * x = (u * x * u⁻¹) * u := by group
      _ = x * u := by rw [this]
  have hUT : U = T := eq_of_isSylowOf_le h.sylowT hUC hUp hTU
  exact ⟨Q', hUT⟩

theorem a_mem_N
    (h : IsAConfig 5 x K T Q S a) (c : Coord5 h) :
    a ∈ normalizer ((c.lift Rm : Subgroup G) : Set G) :=
  Coord5.R_char (c := c) a h.a_mem.2.1

theorem a_not_NQ
    (h : IsAConfig 5 x K T Q S a) (c : Coord5 h) : ∃ q ∈ Q, a * q * a⁻¹ ∉ Q := by
  by_contra hcon
  push Not at hcon
  have haQ : a ∈ normalizer (Q : Set G) := by
    rw [mem_normalizer_iff]
    intro z
    refine ⟨hcon z, fun hz => ?_⟩
    have hle : cj a Q ≤ Q := fun y hy => by
      obtain ⟨q, hq, rfl⟩ := mem_cj.1 hy
      exact hcon q hq
    have heq : cj a Q = Q := Subgroup.eq_of_le_of_card_ge hle (by rw [card_cj])
    have : a * z * a⁻¹ ∈ cj a Q := by rw [heq]; exact hz
    obtain ⟨z', hz', hzz⟩ := mem_cj.1 this
    have hz'z : z' = z := mul_left_cancel (mul_right_cancel hzz)
    rw [← hz'z]
    exact hz'
  set H := normalizer ((c.lift Rm : Subgroup G) : Set G) ⊓ normalizer (Q : Set G) with hH
  have haH : a ∈ H := ⟨a_mem_N h c, haQ⟩
  have hTH : T ≤ H := (T_sylow_NQ h c).le
  set U := T ⊔ zpowers a with hU
  have hUH : U ≤ H := sup_le hTH (zpowers_le.2 haH)
  have hUS : U ≤ S := sup_le h.T_lt_S.le (zpowers_le.2 h.a_mem.1)
  have hSp : IsPGroup 2 ↥S := by
    have := (isSylowOf_iff.1 h.sylowS).2.1
    exact this
  have hUp : IsPGroup 2 ↥U := hSp.to_le hUS
  have hUT := eq_of_isSylowOf_le (T_sylow_NQ h c) hUH hUp le_sup_left
  apply h.a_mem.2.2.1
  rw [← hUT]
  exact mem_sup_right (mem_zpowers a)

@[expose] def FamQ (R Q : Subgroup G) : Set (Subgroup G) :=
  {V | ∃ g ∈ normalizer (R : Set G), V = cj g Q}

theorem cj_mul (g g' : G) (H : Subgroup G) : cj (g * g') H = cj g (cj g' H) := by
  ext y
  simp only [mem_cj]
  constructor
  · rintro ⟨z, hz, rfl⟩
    exact ⟨g' * z * g'⁻¹, ⟨z, hz, rfl⟩, by group⟩
  · rintro ⟨_, ⟨z, hz, rfl⟩, rfl⟩
    exact ⟨z, hz, by group⟩

theorem cj_one (H : Subgroup G) : cj 1 H = H := by
  ext y
  simp [mem_cj]

theorem cj_inv_cj (g : G) (H : Subgroup G) : cj g⁻¹ (cj g H) = H := by
  rw [← cj_mul, inv_mul_cancel, cj_one]

theorem cj_inj {g : G} {H H' : Subgroup G} (h : cj g H = cj g H') : H = H' := by
  have := congrArg (cj g⁻¹) h
  rwa [cj_inv_cj, cj_inv_cj] at this

theorem mem_normalizer_of_cj_le {g : G} {H : Subgroup G} (hle : cj g H ≤ H) :
    g ∈ normalizer (H : Set G) := by
  have heq : cj g H = H := Subgroup.eq_of_le_of_card_ge hle (by rw [card_cj])
  refine mem_normalizer_iff.2 (fun y => ⟨fun hy => hle (mem_cj_self hy), fun hy => ?_⟩)
  have : g * y * g⁻¹ ∈ cj g H := by rw [heq]; exact hy
  obtain ⟨z, hz, hzz⟩ := mem_cj.1 this
  have hz'z : z = y := mul_left_cancel (mul_right_cancel hzz)
  rw [← hz'z]
  exact hz

theorem cj_eq_of_normalizes {g : G} {H : Subgroup G} (hg : g ∈ normalizer (H : Set G)) :
    cj g H = H := by
  ext y
  rw [mem_cj]
  constructor
  · rintro ⟨z, hz, rfl⟩
    exact (mem_normalizer_iff.1 hg z).1 hz
  · intro hy
    refine ⟨g⁻¹ * y * g, ?_, by group⟩
    have h1 := (mem_normalizer_iff.1 (inv_mem hg) y).1 hy
    simpa using h1

theorem fam_le_R {R Q V : Subgroup G} (hQR : Q ≤ R) (hV : V ∈ FamQ R Q) : V ≤ R := by
  obtain ⟨g, hg, rfl⟩ := hV
  intro y hy
  obtain ⟨z, hz, rfl⟩ := mem_cj.1 hy
  exact (mem_normalizer_iff.1 hg z).1 (hQR hz)

theorem fam_cj {R Q V : Subgroup G} {w : G} (hw : w ∈ normalizer (R : Set G))
    (hV : V ∈ FamQ R Q) : cj w V ∈ FamQ R Q := by
  obtain ⟨g, hg, rfl⟩ := hV
  exact ⟨w * g, mul_mem hw hg, (cj_mul w g Q).symm⟩

theorem Q_mem_fam {R Q : Subgroup G} : Q ∈ FamQ R Q := ⟨1, one_mem _, (cj_one Q).symm⟩

theorem fam_TI
    (h : IsAConfig 5 x K T Q S a) (c : Coord5 h) (hG4 : pRank 2 G ≤ 4)
    {V₁ V₂ : Subgroup G} (h₁ : V₁ ∈ FamQ (c.lift Rm) Q) (h₂ : V₂ ∈ FamQ (c.lift Rm) Q)
    (hne : V₁ ≠ V₂) : V₁ ⊓ V₂ = ⊥ := by
  obtain ⟨g₁, hg₁, rfl⟩ := h₁
  obtain ⟨g₂, hg₂, rfl⟩ := h₂
  rw [eq_bot_iff]
  rintro z ⟨hz₁, hz₂⟩
  by_contra hz
  have hz1 : z ≠ 1 := fun h1 => hz (Subgroup.mem_bot.2 h1)
  obtain ⟨q₁, hq₁, rfl⟩ := mem_cj.1 hz₁
  obtain ⟨q₂, hq₂, hqq⟩ := mem_cj.1 hz₂
  have hq1 : q₁ ≠ 1 := by
    intro h1
    apply hz1
    rw [h1]
    group
  have hgq : (g₂⁻¹ * g₁) * q₁ * (g₂⁻¹ * g₁)⁻¹ ∈ Q := by
    have : (g₂⁻¹ * g₁) * q₁ * (g₂⁻¹ * g₁)⁻¹ = q₂ := by
      calc (g₂⁻¹ * g₁) * q₁ * (g₂⁻¹ * g₁)⁻¹ = g₂⁻¹ * (g₁ * q₁ * g₁⁻¹) * g₂ := by group
        _ = g₂⁻¹ * (g₂ * q₂ * g₂⁻¹) * g₂ := by rw [hqq.symm]
        _ = q₂ := by group
    rw [this]
    exact hq₂
  have hTI := TI_Q h c hG4 (mul_mem (inv_mem hg₂) hg₁) hq₁ hq1 hgq
  apply hne
  calc cj g₁ Q = cj (g₂ * (g₂⁻¹ * g₁)) Q := by rw [mul_inv_cancel_left]
    _ = cj g₂ (cj (g₂⁻¹ * g₁) Q) := cj_mul _ _ _
    _ = cj g₂ Q := by rw [hTI]

theorem Q_le_R
    (h : IsAConfig 5 x K T Q S a) (c : Coord5 h) : Q ≤ c.lift Rm :=
  (Coord5.Q_eq_lift (c := c)).le.trans (Coord5.lift_mono Qm_le_Rm)

theorem P_le_R
    (h : IsAConfig 5 x K T Q S a) (c : Coord5 h) : T ⊓ K ≤ c.lift Rm :=
  (Coord5.P_eq_lift (c := c)).le.trans (Coord5.lift_mono Pm_le_Rm)

theorem w_mem_N (h : IsAConfig 5 x K T Q S a) (c : Coord5 h) :
    (c.wC : G) ∈ normalizer ((c.lift Rm : Subgroup G) : Set G) := by
  apply mem_normalizer_of_cj_le
  intro y hy
  obtain ⟨r, hr, rfl⟩ := mem_cj.1 hy
  have hrC := Coord5.lift_mem_cent hr
  have hw : (c.wC : G) ∈ centralizer ({x} : Set G) := c.wC.2
  rw [Coord5.mem_lift_rco c]
  refine ⟨mul_mem (mul_mem hw hrC) (inv_mem hw), ?_⟩
  rw [Coord5.rco_conj_w c hrC]
  exact wm_norm_R _ (Coord5.rco_mem c hr)

theorem cj_w_Q
    (h : IsAConfig 5 x K T Q S a) (c : Coord5 h) : cj (c.wC : G) Q = Q := by
  refine Subgroup.eq_of_le_of_card_ge (fun y hy => ?_) (by rw [card_cj])
  obtain ⟨z, hz, rfl⟩ := mem_cj.1 hy
  have hz' : z ∈ c.lift Qm := (SetLike.ext_iff.1 (Coord5.Q_eq_lift (c := c)) z).1 hz
  have : (c.wC : G) * z * (c.wC : G)⁻¹ = z := by
    rw [Coord5.wG_cent_Q hz', mul_inv_cancel_right]
  rw [this]
  exact hz

theorem cj_w_P (h : IsAConfig 5 x K T Q S a) (c : Coord5 h) :
    cj (c.wC : G) (T ⊓ K) = T ⊓ K := by
  refine Subgroup.eq_of_le_of_card_ge (fun y hy => ?_) (by rw [card_cj])
  obtain ⟨z, hz, rfl⟩ := mem_cj.1 hy
  have hz' : z ∈ c.lift Pm := (SetLike.ext_iff.1 (Coord5.P_eq_lift (c := c)) z).1 hz
  exact (SetLike.ext_iff.1 (Coord5.P_eq_lift (c := c)) _).2 (Coord5.wG_norm_P hz')

theorem card_fam {R Q V : Subgroup G} (hV : V ∈ FamQ R Q) : Nat.card V = Nat.card Q := by
  obtain ⟨g, -, rfl⟩ := hV
  exact card_cj g Q

theorem rco_ne_one {h : IsAConfig 5 x K T Q S a} (c : Coord5 h) {g : G} (hg : g ∈ centralizer ({x} : Set G)) (hg1 : g ≠ 1) :
    c.rco g ≠ 1 := by
  intro h1
  apply hg1
  exact Coord5.rco_inj c hg (one_mem _) (h1.trans (Coord5.rco_one c).symm)

theorem fam_w_fixed
    (h : IsAConfig 5 x K T Q S a) (c : Coord5 h) {V : Subgroup G}
    (hV : V ∈ FamQ (c.lift Rm) Q) (hw : cj (c.wC : G) V = V) : V = T ⊓ K ∨ V = Q := by
  have hVR : V ≤ c.lift Rm := fam_le_R (Q_le_R h c) hV
  have hV4 : Nat.card V = 4 := by rw [card_fam hV, h.card_Q]
  have hsq : ∀ z ∈ V, z * z = 1 := fun z hz =>
    Coord5.lift_sq (c := c) (M := Rm) (fun p hp => Rm_sq p hp) (hVR hz)
  obtain ⟨u, v, hu, hv, hu1, hv1, huv⟩ := exists_klein_basis hV4
  have hbasis := klein_elems hV4 hsq hu hv hu1 hv1 huv
  have huC := Coord5.lift_mem_cent (hVR hu)
  have hvC := Coord5.lift_mem_cent (hVR hv)
  have hw' : ∀ z ∈ V, (c.wC : G) * z * (c.wC : G)⁻¹ ∈ V := fun z hz => hw ▸ mem_cj_self hz
  have hcoord : ∀ z ∈ V, z ≠ 1 → c.rco z = c.rco u ∨ c.rco z = c.rco v ∨
      c.rco z = c.rco u * c.rco v := by
    intro z hz hz1
    rcases hbasis z hz with h1 | h1 | h1 | h1
    · exact absurd h1 hz1
    · exact Or.inl (by rw [h1])
    · exact Or.inr (Or.inl (by rw [h1]))
    · exact Or.inr (Or.inr (by rw [h1, Coord5.rco_mul c huC hvC]))
  have hwconj : ∀ z ∈ V, z ≠ 1 → wm * c.rco z * wm⁻¹ ∈ [c.rco u, c.rco v, c.rco u * c.rco v] := by
    intro z hz hz1
    have hzC := Coord5.lift_mem_cent (hVR hz)
    have h1 : (c.wC : G) * z * (c.wC : G)⁻¹ ≠ 1 := by
      intro h2
      apply hz1
      have : z = (c.wC : G)⁻¹ * ((c.wC : G) * z * (c.wC : G)⁻¹) * (c.wC : G) := by group
      rw [this, h2]
      group
    rw [← Coord5.rco_conj_w c hzC]
    have := hcoord _ (hw' z hz) h1
    simpa using this
  have hu'1 := rco_ne_one c huC hu1
  have hv'1 := rco_ne_one c hvC hv1
  have huv' : c.rco u ≠ c.rco v := fun h1 => huv (Coord5.rco_inj c huC hvC h1)
  have hFIN := FIN1 (Coord5.rco_mem c (hVR hu)) (Coord5.rco_mem c (hVR hv)) hu'1 hv'1 huv'
    (hwconj u hu hu1) (hwconj v hv hv1)
  rcases hFIN with ⟨hup, hvp⟩ | ⟨huq, hvq⟩
  · left
    have hu' : u ∈ T ⊓ K := (SetLike.ext_iff.1 (Coord5.P_eq_lift (c := c)) u).2
      ((Coord5.mem_lift_rco c).2 ⟨huC, hup⟩)
    have hv' : v ∈ T ⊓ K := (SetLike.ext_iff.1 (Coord5.P_eq_lift (c := c)) v).2
      ((Coord5.mem_lift_rco c).2 ⟨hvC, hvp⟩)
    have hle : V ≤ T ⊓ K := by
      intro z hz
      rcases hbasis z hz with rfl | rfl | rfl | rfl
      · exact one_mem _
      · exact hu'
      · exact hv'
      · exact mul_mem hu' hv'
    refine Subgroup.eq_of_le_of_card_ge hle ?_
    rw [hV4, Coord5.P_eq_lift (c := c)]
    exact (Coord5.card_lift_Pm (c := c)).le
  · right
    have hu' : u ∈ Q := (SetLike.ext_iff.1 (Coord5.Q_eq_lift (c := c)) u).2
      ((Coord5.mem_lift_rco c).2 ⟨huC, huq⟩)
    have hv' : v ∈ Q := (SetLike.ext_iff.1 (Coord5.Q_eq_lift (c := c)) v).2
      ((Coord5.mem_lift_rco c).2 ⟨hvC, hvq⟩)
    have hle : V ≤ Q := by
      intro z hz
      rcases hbasis z hz with rfl | rfl | rfl | rfl
      · exact one_mem _
      · exact hu'
      · exact hv'
      · exact mul_mem hu' hv'
    exact Subgroup.eq_of_le_of_card_ge hle (by rw [hV4, h.card_Q])

theorem fam_meet_P
    (h : IsAConfig 5 x K T Q S a) (c : Coord5 h) (hG4 : pRank 2 G ≤ 4)
    {V : Subgroup G} (hV : V ∈ FamQ (c.lift Rm) Q) (hVQ : V ≠ Q)
    (hw : cj (c.wC : G) V ≠ V) : V ⊓ (T ⊓ K) = ⊥ := by
  by_contra hne
  have hVQ' : V ⊓ Q = ⊥ := fam_TI h c hG4 hV Q_mem_fam hVQ
  have hVR : V ≤ c.lift Rm := fam_le_R (Q_le_R h c) hV
  have hV4 : Nat.card V = 4 := by rw [card_fam hV, h.card_Q]
  have hsq : ∀ z ∈ V, z * z = 1 := fun z hz =>
    Coord5.lift_sq (c := c) (M := Rm) (fun p hp => Rm_sq p hp) (hVR hz)
  obtain ⟨u, v, hu, hv, hu1, hv1, huv⟩ := exists_klein_basis hV4
  have hbasis := klein_elems hV4 hsq hu hv hu1 hv1 huv
  have huC := Coord5.lift_mem_cent (hVR hu)
  have hvC := Coord5.lift_mem_cent (hVR hv)
  have huvC : u * v ∈ centralizer ({x} : Set G) := mul_mem huC hvC
  have hu'R := Coord5.rco_mem c (hVR hu)
  have hv'R := Coord5.rco_mem c (hVR hv)
  have hu'1 := rco_ne_one c huC hu1
  have hv'1 := rco_ne_one c hvC hv1
  have huv' : c.rco u ≠ c.rco v := fun h1 => huv (Coord5.rco_inj c huC hvC h1)
  have hnotQ : ∀ z ∈ V, z ≠ 1 → c.rco z ∉ Qm := by
    intro z hz hz1 hzQ
    have hzC := Coord5.lift_mem_cent (hVR hz)
    have hzQ' : z ∈ Q := (SetLike.ext_iff.1 (Coord5.Q_eq_lift (c := c)) z).2
      ((Coord5.mem_lift_rco c).2 ⟨hzC, hzQ⟩)
    have : z ∈ V ⊓ Q := ⟨hz, hzQ'⟩
    rw [hVQ'] at this
    exact hz1 (Subgroup.mem_bot.1 this)
  have hQ : c.rco u ∉ Qm ∧ c.rco v ∉ Qm ∧ c.rco u * c.rco v ∉ Qm := by
    refine ⟨hnotQ u hu hu1, hnotQ v hv hv1, ?_⟩
    have := hnotQ (u * v) (mul_mem hu hv) (by
      intro h1
      apply huv
      have : v = u⁻¹ * (u * v) := by group
      rw [this, h1, mul_one]
      exact (inv_eq_of_mul_eq_one_right (hsq u hu)).symm) 
    rwa [Coord5.rco_mul c huC hvC] at this
  have hP : c.rco u ∈ Pm ∨ c.rco v ∈ Pm ∨ c.rco u * c.rco v ∈ Pm := by
    obtain ⟨z, hzmem⟩ : ∃ z, z ∈ V ⊓ (T ⊓ K) ∧ z ≠ 1 := by
      by_contra hcon
      push Not at hcon
      apply hne
      rw [eq_bot_iff]
      intro z hz
      exact Subgroup.mem_bot.2 (hcon z hz)
    obtain ⟨⟨hzV, hzP⟩, hz1⟩ := hzmem
    have hzP' : z ∈ c.lift Pm := (SetLike.ext_iff.1 (Coord5.P_eq_lift (c := c)) z).1 hzP
    have hzm := Coord5.rco_mem c hzP'
    rcases hbasis z hzV with h1 | h1 | h1 | h1
    · exact absurd h1 hz1
    · exact Or.inl (h1 ▸ hzm)
    · exact Or.inr (Or.inl (h1 ▸ hzm))
    · refine Or.inr (Or.inr ?_)
      rw [← Coord5.rco_mul c huC hvC, ← h1]
      exact hzm
  have hF := FIN2 hu'R hv'R hu'1 hv'1 huv' hQ hP
  have hwV : ∃ s ∈ V, s ≠ 1 ∧ (c.wC : G) * s * (c.wC : G)⁻¹ ∈ V := by
    have hconv : ∀ s ∈ V, wm * c.rco s * wm⁻¹ ∈ [c.rco u, c.rco v, c.rco u * c.rco v] →
        (c.wC : G) * s * (c.wC : G)⁻¹ ∈ V := by
      intro s hs hmem
      have hsC := Coord5.lift_mem_cent (hVR hs)
      have hwC : (c.wC : G) ∈ centralizer ({x} : Set G) := c.wC.2
      have hcon : (c.wC : G) * s * (c.wC : G)⁻¹ ∈ centralizer ({x} : Set G) :=
        mul_mem (mul_mem hwC hsC) (inv_mem hwC)
      rw [← Coord5.rco_conj_w c hsC] at hmem
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
      rcases hmem with h1 | h1 | h1
      · rwa [Coord5.rco_inj c hcon huC h1]
      · rwa [Coord5.rco_inj c hcon hvC h1]
      · rw [← Coord5.rco_mul c huC hvC] at h1
        rw [Coord5.rco_inj c hcon huvC h1]
        exact V.mul_mem hu hv
    rcases hF with h1 | h1 | h1
    · exact ⟨u, hu, hu1, hconv u hu h1⟩
    · exact ⟨v, hv, hv1, hconv v hv h1⟩
    · refine ⟨u * v, mul_mem hu hv, ?_, ?_⟩
      · intro h2
        apply huv
        have : v = u⁻¹ * (u * v) := by group
        rw [this, h2, mul_one]
        exact (inv_eq_of_mul_eq_one_right (hsq u hu)).symm
      · apply hconv _ (mul_mem hu hv)
        rwa [Coord5.rco_mul c huC hvC]
  obtain ⟨s, hsV, hs1, hws⟩ := hwV
  have hTI := fam_TI h c hG4 (fam_cj (w_mem_N h c) hV) hV hw
  have : (c.wC : G) * s * (c.wC : G)⁻¹ ∈ cj (c.wC : G) V ⊓ V := ⟨mem_cj_self hsV, hws⟩
  rw [hTI] at this
  have h2 := Subgroup.mem_bot.1 this
  apply hs1
  have : s = (c.wC : G)⁻¹ * ((c.wC : G) * s * (c.wC : G)⁻¹) * (c.wC : G) := by group
  rw [this, h2]
  group

theorem card_T_five
    (h : IsAConfig 5 x K T Q S a) (c : Coord5 h) : Nat.card T = 32 := by
  have := Coord5.card_lift (c := c) (M := T5) T5_le_Fgrp
  rw [← Coord5.T_eq_lift (c := c), card_T5] at this
  exact this

theorem fam_ncard_le
    (h : IsAConfig 5 x K T Q S a) (c : Coord5 h) (hG4 : pRank 2 G ≤ 4) :
    (FamQ (c.lift Rm) Q).ncard ≤ 5 := by
  classical
  let _inst : Fintype G := Fintype.ofFinite G
  have hfin : (FamQ (c.lift Rm) Q).Finite := Set.toFinite _
  let F : Finset (Subgroup G) := hfin.toFinset
  let t : Subgroup G → Finset G := fun V => (Finset.univ.filter (· ∈ V)).erase 1
  have hcardfilter : ∀ V : Subgroup G, (Finset.univ.filter (· ∈ V)).card = Nat.card V := by
    intro V
    rw [Nat.card_eq_fintype_card]
    exact (Fintype.card_subtype _).symm
  have ht : ∀ V ∈ F, (t V).card = 3 := by
    intro V hV
    have hV' : V ∈ FamQ (c.lift Rm) Q := hfin.mem_toFinset.1 hV
    simp only [t]
    rw [Finset.card_erase_of_mem (by simp), hcardfilter, card_fam hV', h.card_Q]
  have hdisj : ∀ V ∈ F, ∀ V' ∈ F, V ≠ V' → Disjoint (t V) (t V') := by
    intro V hV V' hV' hne
    rw [Finset.disjoint_left]
    intro z hz hz'
    simp only [t, Finset.mem_erase, Finset.mem_filter, Finset.mem_univ, true_and] at hz hz'
    have hTI := fam_TI h c hG4 (hfin.mem_toFinset.1 hV) (hfin.mem_toFinset.1 hV') hne
    have : z ∈ V ⊓ V' := ⟨hz.2, hz'.2⟩
    rw [hTI] at this
    exact hz.1 (Subgroup.mem_bot.1 this)
  have hsub : F.biUnion t ⊆ (Finset.univ.filter (· ∈ c.lift Rm)).erase 1 := by
    intro z hz
    rw [Finset.mem_biUnion] at hz
    obtain ⟨V, hV, hzV⟩ := hz
    simp only [t, Finset.mem_erase, Finset.mem_filter, Finset.mem_univ, true_and] at hzV ⊢
    exact ⟨hzV.1, fam_le_R (Q_le_R h c) (hfin.mem_toFinset.1 hV) hzV.2⟩
  have hcard := Finset.card_biUnion hdisj
  have hle := Finset.card_le_card hsub
  rw [Finset.card_erase_of_mem (by simp), hcardfilter,
    Coord5.card_lift_Rm] at hle
  rw [hcard, Finset.sum_congr rfl ht, Finset.sum_const, smul_eq_mul] at hle
  have hF : (FamQ (c.lift Rm) Q).ncard = F.card := Set.ncard_eq_toFinset_card (FamQ (c.lift Rm) Q) hfin
  omega

theorem fam_card_mul (R Q : Subgroup G) :
    Nat.card (FamQ R Q) * Nat.card ↥(normalizer (R : Set G) ⊓ normalizer (Q : Set G)) =
      Nat.card ↥(normalizer (R : Set G)) := by
  classical
  let N := normalizer (R : Set G)
  let _inst : MulAction ↥N (Subgroup G) :=
    { smul := fun g V => cj (g : G) V
      one_smul := fun V => cj_one V
      mul_smul := fun g g' V => cj_mul (g : G) (g' : G) V }
  have h1 := MulAction.index_stabilizer ↥N Q
  have h2 := Subgroup.card_mul_index (MulAction.stabilizer ↥N Q)
  have horb : MulAction.orbit ↥N Q = FamQ R Q := by
    ext V
    constructor
    · rintro ⟨g, rfl⟩
      exact ⟨g, g.2, rfl⟩
    · rintro ⟨g, hg, rfl⟩
      exact ⟨⟨g, hg⟩, rfl⟩
  have hstab : Nat.card (MulAction.stabilizer ↥N Q) =
      Nat.card ↥(normalizer (R : Set G) ⊓ normalizer (Q : Set G)) := by
    apply Nat.card_congr
    exact
      { toFun := fun g => ⟨(g.1 : G), g.1.2, mem_normalizer_of_cj_le (by
          have : cj (g.1 : G) Q = Q := g.2
          exact this.le)⟩
        invFun := fun g => ⟨⟨(g : G), g.2.1⟩, by
          show cj (g : G) Q = Q
          exact cj_eq_of_normalizes g.2.2⟩
        left_inv := fun g => rfl
        right_inv := fun g => rfl }
  rw [hstab] at h2
  rw [← horb, Nat.card_coe_set_eq, ← h1]
  rw [mul_comm]
  exact h2

theorem fam_even
    (h : IsAConfig 5 x K T Q S a) (c : Coord5 h) :
    2 ∣ Nat.card (FamQ (c.lift Rm) Q) := by
  classical
  have hmul := fam_card_mul (c.lift Rm) Q
  have hsyl := T_sylow_NQ h c
  obtain ⟨hTH, hTp, hidx⟩ := isSylowOf_iff.1 hsyl
  have hHcard : Nat.card ↥(normalizer ((c.lift Rm : Subgroup G) : Set G) ⊓ normalizer (Q : Set G)) =
      32 * T.relIndex (normalizer ((c.lift Rm : Subgroup G) : Set G) ⊓ normalizer (Q : Set G)) := by
    have h1 := Subgroup.card_mul_index (T.subgroupOf (normalizer ((c.lift Rm : Subgroup G) : Set G) ⊓
      normalizer (Q : Set G)))
    have h2 : Nat.card ↥(T.subgroupOf (normalizer ((c.lift Rm : Subgroup G) : Set G) ⊓
        normalizer (Q : Set G))) = Nat.card T :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hTH).toEquiv
    rw [h2, card_T_five h c] at h1
    exact h1.symm
  have hTN : T ≤ normalizer ((c.lift Rm : Subgroup G) : Set G) := hTH.trans inf_le_left
  have haN := a_mem_N h c
  set M₂ := T ⊔ zpowers a with hM₂
  have hM₂N : M₂ ≤ normalizer ((c.lift Rm : Subgroup G) : Set G) :=
    sup_le hTN (zpowers_le.2 haN)
  have hM₂S : M₂ ≤ S := sup_le h.T_lt_S.le (zpowers_le.2 h.a_mem.1)
  have hSp : IsPGroup 2 ↥S := (isSylowOf_iff.1 h.sylowS).2.1
  have hM₂p : IsPGroup 2 ↥M₂ := hSp.to_le hM₂S
  obtain ⟨j, hj⟩ := IsPGroup.iff_card.1 hM₂p
  have h32 : 32 ∣ 2 ^ j := by
    rw [← hj, ← card_T_five h c]
    exact Subgroup.card_dvd_of_le le_sup_left
  have hj6 : 6 ≤ j := by
    by_contra hlt
    push Not at hlt
    have hj5 : j = 5 := by
      interval_cases j <;> simp_all
    have hcard : Nat.card M₂ = Nat.card T := by rw [hj, hj5, card_T_five h c]; norm_num
    have heq : M₂ = T := Subgroup.eq_of_le_of_card_ge le_sup_left hcard.le |>.symm
    apply h.a_mem.2.2.1
    rw [← heq]
    exact mem_sup_right (mem_zpowers a)
  have h64 : 64 ∣ Nat.card ↥(normalizer ((c.lift Rm : Subgroup G) : Set G)) := by
    have h1 : 64 ∣ Nat.card M₂ := by
      rw [hj]
      exact (pow_dvd_pow 2 hj6)
    exact h1.trans (Subgroup.card_dvd_of_le hM₂N)
  rw [← hmul, hHcard] at h64
  have h2 : 2 ∣ Nat.card (FamQ (c.lift Rm) Q) *
      T.relIndex (normalizer ((c.lift Rm : Subgroup G) : Set G) ⊓ normalizer (Q : Set G)) := by
    have h3 : 32 * 2 ∣ 32 * (Nat.card (FamQ (c.lift Rm) Q) *
        T.relIndex (normalizer ((c.lift Rm : Subgroup G) : Set G) ⊓ normalizer (Q : Set G))) := by
      have : 32 * (Nat.card (FamQ (c.lift Rm) Q) *
          T.relIndex (normalizer ((c.lift Rm : Subgroup G) : Set G) ⊓ normalizer (Q : Set G))) =
          Nat.card (FamQ (c.lift Rm) Q) * (32 * T.relIndex (normalizer ((c.lift Rm : Subgroup G) :
            Set G) ⊓ normalizer (Q : Set G))) := by ring
      rw [this]
      exact (by norm_num : 32 * 2 = 64) ▸ h64
    exact Nat.dvd_of_mul_dvd_mul_left (by norm_num) h3
  rcases (Nat.Prime.dvd_mul Nat.prime_two).1 h2 with h4 | h4
  · exact h4
  · exact absurd h4 hidx

theorem P_inf_Q
    (h : IsAConfig 5 x K T Q S a) (c : Coord5 h) : (T ⊓ K) ⊓ Q = ⊥ := by
  have h1 : c.lift Pm ⊓ c.lift Qm = ⊥ := by
    rw [← Coord5.lift_inf, Pm_inf_Qm, Coord5.lift_bot]
  rw [eq_bot_iff]
  intro z hz
  have hz' : z ∈ c.lift Pm ⊓ c.lift Qm :=
    ⟨(SetLike.ext_iff.1 (Coord5.P_eq_lift (c := c)) z).1 hz.1,
      (SetLike.ext_iff.1 (Coord5.Q_eq_lift (c := c)) z).1 hz.2⟩
  rw [h1] at hz'
  exact hz'

theorem card_P_five
    (h : IsAConfig 5 x K T Q S a) (c : Coord5 h) : Nat.card ↥(T ⊓ K) = 4 := by
  rw [Coord5.P_eq_lift (c := c)]
  exact Coord5.card_lift_Pm

theorem cj_w_cube
    (h : IsAConfig 5 x K T Q S a) (c : Coord5 h) (V : Subgroup G) :
    cj (c.wC : G) (cj (c.wC : G) (cj (c.wC : G) V)) = V := by
  have hcube : (c.wC : G) * ((c.wC : G) * (c.wC : G)) = 1 := by
    have := congrArg Subtype.val (Coord5.wC_cube (c := c))
    simpa [mul_assoc] using this
  have h3 : (c.wC : G) * (c.wC : G) * (c.wC : G) = 1 := by rw [mul_assoc]; exact hcube
  rw [← cj_mul, ← cj_mul, h3, cj_one]

theorem fam_dichotomy
    (h : IsAConfig 5 x K T Q S a) (c : Coord5 h) (hG4 : pRank 2 G ≤ 4) :
    (∀ V ∈ FamQ (c.lift Rm) Q, V = Q ∨ V = T ⊓ K) ∨
      ((∀ V ∈ FamQ (c.lift Rm) Q, V ⊓ (T ⊓ K) = ⊥) ∧ (FamQ (c.lift Rm) Q).ncard = 4) := by
  classical
  have hwN := w_mem_N h c
  have hcjwQ := cj_w_Q h c
  have hcjwP := cj_w_P h c
  have hcube := cj_w_cube h c
  have hFfin : (FamQ (c.lift Rm) Q).Finite := Set.toFinite _
  have hle5 := fam_ncard_le h c hG4
  have heven : 2 ∣ (FamQ (c.lift Rm) Q).ncard := by
    rw [← Nat.card_coe_set_eq]
    exact fam_even h c
  have hPQ : T ⊓ K ≠ Q := by
    intro heq
    have h1 := P_inf_Q h c
    rw [heq, inf_idem] at h1
    have := h.card_Q
    rw [h1, Subgroup.card_bot] at this
    omega
  have hQfix : ∀ V : Subgroup G, cj (c.wC : G) V = Q → V = Q := fun V hV => by
    have h1 : cj (c.wC : G) V = cj (c.wC : G) Q := by rw [hV, hcjwQ]
    exact cj_inj h1
  have hPfix : ∀ V : Subgroup G, cj (c.wC : G) V = T ⊓ K → V = T ⊓ K := fun V hV => by
    have h1 : cj (c.wC : G) V = cj (c.wC : G) (T ⊓ K) := by rw [hV, hcjwP]
    exact cj_inj h1
  by_cases hP : T ⊓ K ∈ FamQ (c.lift Rm) Q
  · left
    intro V hV
    by_contra hVne
    push Not at hVne
    obtain ⟨hVQ, hVP⟩ := hVne
    set V₁ := cj (c.wC : G) V with hV₁
    set V₂ := cj (c.wC : G) V₁ with hV₂
    have hV₁F : V₁ ∈ FamQ (c.lift Rm) Q := fam_cj hwN hV
    have hV₂F : V₂ ∈ FamQ (c.lift Rm) Q := fam_cj hwN hV₁F
    have hnfix : ∀ U ∈ FamQ (c.lift Rm) Q, U ≠ Q → U ≠ T ⊓ K → cj (c.wC : G) U ≠ U := by
      intro U hU hUQ hUP hfix
      rcases fam_w_fixed h c hU hfix with h1 | h1
      · exact hUP h1
      · exact hUQ h1
    have hV₁ne : V₁ ≠ V := hnfix V hV hVQ hVP
    have hV₁Q : V₁ ≠ Q := fun h1 => hVQ (hQfix V h1)
    have hV₁P : V₁ ≠ T ⊓ K := fun h1 => hVP (hPfix V h1)
    have hV₂ne : V₂ ≠ V₁ := hnfix V₁ hV₁F hV₁Q hV₁P
    have hV₂Q : V₂ ≠ Q := fun h1 => hV₁Q (hQfix V₁ h1)
    have hV₂P : V₂ ≠ T ⊓ K := fun h1 => hV₁P (hPfix V₁ h1)
    have hV₂V : V₂ ≠ V := by
      intro h1
      apply hV₁ne
      have h2 : cj (c.wC : G) V₂ = V := hcube V
      rw [h1] at h2
      exact h2
    let s : Finset (Subgroup G) := {Q, T ⊓ K, V, V₁, V₂}
    have hs : s.card = 5 := by
      simp only [s]
      rw [Finset.card_insert_of_notMem (by simp [hPQ.symm, hVQ.symm, hV₁Q.symm, hV₂Q.symm]),
        Finset.card_insert_of_notMem (by simp [hVP.symm, hV₁P.symm, hV₂P.symm]),
        Finset.card_insert_of_notMem (by simp [hV₁ne.symm, hV₂V.symm]),
        Finset.card_insert_of_notMem (by simp [hV₂ne.symm]), Finset.card_singleton]
    have hsub : (↑s : Set (Subgroup G)) ⊆ FamQ (c.lift Rm) Q := by
      intro U hU
      simp only [s, Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
        Set.mem_singleton_iff] at hU
      rcases hU with rfl | rfl | rfl | rfl | rfl
      · exact Q_mem_fam
      · exact hP
      · exact hV
      · exact hV₁F
      · exact hV₂F
    have h5 : 5 ≤ (FamQ (c.lift Rm) Q).ncard := by
      have := Set.ncard_le_ncard hsub hFfin
      rwa [Set.ncard_coe_finset, hs] at this
    have : (FamQ (c.lift Rm) Q).ncard = 5 := le_antisymm hle5 h5
    rw [this] at heven
    omega
  · right
    have hcl1 : ∀ V ∈ FamQ (c.lift Rm) Q, V ⊓ (T ⊓ K) = ⊥ := by
      intro V hV
      by_cases hVQ : V = Q
      · rw [hVQ, inf_comm]
        exact P_inf_Q h c
      · have hfix : cj (c.wC : G) V ≠ V := by
          intro hfix
          rcases fam_w_fixed h c hV hfix with h1 | h1
          · exact hP (h1 ▸ hV)
          · exact hVQ h1
        exact fam_meet_P h c hG4 hV hVQ hfix
    refine ⟨hcl1, ?_⟩
    obtain ⟨q, hqQ, hq⟩ := a_not_NQ h c
    have hV₀F : cj a Q ∈ FamQ (c.lift Rm) Q := ⟨a, a_mem_N h c, rfl⟩
    have hV₀Q : cj a Q ≠ Q := by
      intro heq
      apply hq
      have : a * q * a⁻¹ ∈ cj a Q := mem_cj_self hqQ
      rwa [heq] at this
    have hsub2 : ({Q, cj a Q} : Set (Subgroup G)) ⊆ FamQ (c.lift Rm) Q := by
      intro U hU
      rcases hU with rfl | hU
      · exact Q_mem_fam
      · rw [Set.mem_singleton_iff.1 hU]
        exact hV₀F
    have h2 : 2 ≤ (FamQ (c.lift Rm) Q).ncard := by
      have := Set.ncard_le_ncard hsub2 hFfin
      rwa [Set.ncard_pair hV₀Q.symm] at this
    have hne2 : (FamQ (c.lift Rm) Q).ncard ≠ 2 := by
      intro h22
      have heq : ({Q, cj a Q} : Set (Subgroup G)) = FamQ (c.lift Rm) Q :=
        Set.eq_of_subset_of_ncard_le hsub2 (by rw [h22, Set.ncard_pair hV₀Q.symm]) hFfin
      have hw₀ : cj (c.wC : G) (cj a Q) ∈ ({Q, cj a Q} : Set (Subgroup G)) := by
        rw [heq]
        exact fam_cj hwN hV₀F
      rcases hw₀ with h1 | h1
      · exact hV₀Q (hQfix _ h1)
      · rw [Set.mem_singleton_iff] at h1
        rcases fam_w_fixed h c hV₀F h1 with h3 | h3
        · exact hP (h3 ▸ hV₀F)
        · exact hV₀Q h3
    omega

end CFSG.GH74.GLS.C3.Layer2.L5
