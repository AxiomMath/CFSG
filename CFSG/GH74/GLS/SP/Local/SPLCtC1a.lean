module

public import CFSG.GH74.GLS.SP.Local.SPLCtC1aSyl
public import CFSG.GH74.GLS.IVK.Proofs2.Lemma31i

public section

namespace CFSG.GH74.GLS.SP.Local

open Subgroup CFSG CFSG.Blueprint CFSG.Assembly.LowTwoRank CFSG.GH74.GLS CFSG.GH74.BNPair
open CFSG.GH74.GLS.LU.Local CFSG.GH74.GLS.SP
open scoped Pointwise commutatorElement

section C1a

theorem exists_sylow_subgroupOf {G : Type} [Group G] (S : Sylow 2 G) (X : Subgroup G)
    (hX : (S : Subgroup G) ≤ X) :
    ∃ T : Sylow 2 ↥X, (T : Subgroup ↥X) = (S : Subgroup G).subgroupOf X := by
  refine ⟨Sylow.mk ((S : Subgroup G).subgroupOf X) (IsPGroup.comap_subtype S.isPGroup') ?_, rfl⟩
  intro Q hQ hle
  have hQp : IsPGroup 2 ↥(Q.map X.subtype) := hQ.map _
  have hle' : (S : Subgroup G) ≤ Q.map X.subtype := fun x hx => ⟨⟨x, hX hx⟩, hle hx, rfl⟩
  have heq := S.is_maximal' hQp hle'
  apply le_antisymm
  · intro x hx
    have : (x : G) ∈ Q.map X.subtype := ⟨x, hx, rfl⟩
    rw [heq] at this
    exact this
  · exact hle

theorem conj_mem_U {G : Type} [Group G] {x u z : G} (hxu : x * u * x⁻¹ ∈ zpowers u ⊔ zpowers z)
    (hxz : x * z * x⁻¹ ∈ zpowers u ⊔ zpowers z) :
    ∀ v ∈ zpowers u ⊔ zpowers z, x * v * x⁻¹ ∈ zpowers u ⊔ zpowers z := by
  have h : (zpowers u ⊔ zpowers z).map (MulAut.conj x).toMonoidHom ≤ zpowers u ⊔ zpowers z := by
    rw [Subgroup.map_sup, MonoidHom.map_zpowers, MonoidHom.map_zpowers]
    exact sup_le (zpowers_le.mpr (by simpa [MulAut.conj_apply] using hxu))
      (zpowers_le.mpr (by simpa [MulAut.conj_apply] using hxz))
  intro v hv
  exact h ⟨v, hv, by simp [MulAut.conj_apply]⟩

variable {G : Type} [Group G] [Finite G] (D : SPLNot1 G)

omit [Finite G] in
theorem S_le_C' (hs : SPLSetup D.toSPLNot0) : (D.S : Subgroup G) ≤ D.C := fun _ hs' =>
  mem_centralizer_singleton_iff.mpr (hs.syl.comm_z hs')

omit [Finite G] in
theorem K₁_le_C' (hs : SPLSetup D.toSPLNot0) : D.K₁ ≤ D.C :=
  le_trans le_sup_left (K_le_C D.ext3 hs)

omit [Finite G] in
theorem K₂_le_C' (hs : SPLSetup D.toSPLNot0) : D.K₂ ≤ D.C :=
  le_trans le_sup_right (K_le_C D.ext3 hs)

omit [Finite G] in
theorem K'_eq (hs : SPLSetup D.toSPLNot0) :
    D.K₁.subgroupOf D.C ⊔ D.K₂.subgroupOf D.C = D.K.subgroupOf D.C :=
  (Subgroup.subgroupOf_sup (K₁_le_C' D hs) (K₂_le_C' D hs)).symm

theorem Q₁_card_pow (hs : SPLSetup D.toSPLNot0) :
    Nat.card ↥((D.S : Subgroup G) ⊓ D.K₁) = 2 ^ D.n := by
  have hq2 : 25 ≤ D.q ^ 2 := by have := hs.q_ge; nlinarith
  rw [Q₁_card hs, card_K₁ (D := D.toSPLNot0) hs, Nat.factorization_mul (by have := hs.q_ge; omega)
    (by omega)]
  simp only [Finsupp.add_apply]
  have hq0 : D.q.factorization 2 = 0 := Nat.factorization_eq_zero_of_not_dvd (by
    obtain ⟨k, hk⟩ := hs.odd_q; omega)
  rw [hq0, zero_add, v2_q_sq_sub_one_eq_n D hs]

theorem prodSL2_C (hs : SPLSetup D.toSPLNot0) :
    ∃ (F₁ F₂ : Type) (_ : Field F₁) (_ : Field F₂),
      IVK.ProdSL2 ↥D.C (D.K₁.subgroupOf D.C) (D.K₂.subgroupOf D.C) F₁ F₂ := by
  obtain ⟨F₁, i₁, f₁, hq₁, ⟨e₁⟩⟩ := hs.comps.sl₁
  obtain ⟨F₂, i₂, f₂, hq₂, ⟨e₂⟩⟩ := hs.comps.sl₂
  refine ⟨F₁, F₂, i₁, i₂, ?_⟩
  refine
    { comm := ?_
      iso₁ := ⟨(Subgroup.subgroupOfEquivOfLe (K₁_le_C' D hs)).trans e₁⟩
      iso₂ := ⟨(Subgroup.subgroupOfEquivOfLe (K₂_le_C' D hs)).trans e₂⟩
      card_inter := ?_
      fstar_normal := ?_
      fstar_centralizer := ?_ }
  · intro a ha b hb
    exact Subtype.ext (hs.comps.comm a ha b hb)
  · have h : D.K₁.subgroupOf D.C ⊓ D.K₂.subgroupOf D.C = (zpowers D.z).subgroupOf D.C := by
      ext x
      rw [Subgroup.mem_inf, Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf,
        Subgroup.mem_subgroupOf, ← hs.comps.inf_eq, Subgroup.mem_inf]
    rw [h]
    have hzC : zpowers D.z ≤ D.C := by
      rw [zpowers_le]; exact mem_centralizer_singleton_iff.mpr rfl
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hzC).toEquiv, Nat.card_zpowers,
      hs.syl.z_inv]
  · rw [K'_eq D hs]
    refine ⟨fun n hn g => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    exact hs.comps.conj_sup_mem g.2 hn
  · rw [K'_eq D hs]
    intro c hc
    rw [Subgroup.mem_subgroupOf]
    have hcz : (c : G) ∈ zpowers D.z := by
      refine cen_C_K hs c.2 ?_
      intro k hk
      have hkC : k ∈ D.C := K_le_C D.ext3 hs hk
      have hk' : (⟨k, hkC⟩ : ↥D.C) ∈ D.K.subgroupOf D.C := Subgroup.mem_subgroupOf.mpr hk
      have := Subgroup.mem_centralizer_iff.mp hc ⟨k, hkC⟩ hk'
      exact (congrArg Subtype.val this).symm
    exact zpowers_le.mpr (Subgroup.mem_sup_left (z_mem_K₁' D hs)) hcz

theorem ct1a_core (hs : SPLSetup D.toSPLNot0) {u : G} (hu : SPLCtU D u) :
    SPLDihStruct D.n ((D.S : Subgroup G) ⊓ centralizer ({u} : Set G)) := by
  obtain ⟨F₁, F₂, i₁, i₂, hprod⟩ := prodSL2_C D hs
  obtain ⟨T, hT⟩ := exists_sylow_subgroupOf D.S D.C (S_le_C' D hs)
  have hM1 : ∀ x : ↥D.C, x ∈ D.K₁.subgroupOf D.C ⊔ D.K₂.subgroupOf D.C ↔ (x : G) ∈ D.K := by
    intro x
    rw [K'_eq D hs, Subgroup.mem_subgroupOf]
  have hM2 : ∀ x : ↥D.C, x ∈ (T : Subgroup ↥D.C) ↔ (x : G) ∈ (D.S : Subgroup G) := by
    intro x
    rw [hT, Subgroup.mem_subgroupOf]
  have hz_C : D.z ∈ D.C := mem_centralizer_singleton_iff.mpr rfl
  have hu_S : u ∈ (D.S : Subgroup G) := hu.mem_S₁.1
  have hu_C : u ∈ D.C := S_le_C' D hs hu_S
  have ht_C : D.t ∈ D.C := S_le_C' D hs hs.syl.t_mem
  set z' : ↥D.C := ⟨D.z, hz_C⟩ with hz'
  set u' : ↥D.C := ⟨u, hu_C⟩ with hu'
  set t' : ↥D.C := ⟨D.t, ht_C⟩ with ht'
  have hz'mem : z' ∈ D.K₁.subgroupOf D.C ⊓ D.K₂.subgroupOf D.C :=
    ⟨Subgroup.mem_subgroupOf.mpr (z_mem_K₁' D hs), Subgroup.mem_subgroupOf.mpr (z_mem_K₂' D hs)⟩
  have hz1 : z' ≠ 1 := fun h => z_ne_one' D hs (congrArg Subtype.val h)
  have hu'mem : u' ∈ (T : Subgroup ↥D.C) ⊓ (D.K₁.subgroupOf D.C ⊔ D.K₂.subgroupOf D.C) :=
    ⟨(hM2 u').mpr hu_S, (hM1 u').mpr (Ict_le_K D hs hu.mem_I)⟩
  have hu2 : orderOf u' = 2 := by rw [hu', Subgroup.orderOf_mk]; exact hu.ord
  have hune : u' ≠ z' := fun h => u_ne_z D hs hu (congrArg Subtype.val h)
  have hM3 : ∀ w : ↥D.C, w ∈ zpowers u' ⊔ zpowers z' ↔ (w : G) ∈ zpowers u ⊔ zpowers D.z := by
    intro w
    have hmap : (zpowers u' ⊔ zpowers z').map D.C.subtype = zpowers u ⊔ zpowers D.z := by
      rw [Subgroup.map_sup, MonoidHom.map_zpowers, MonoidHom.map_zpowers]
      rfl
    rw [← hmap]
    exact (Subgroup.mem_map_iff_mem D.C.subtype_injective).symm
  have hnorm : ∀ x ∈ (T : Subgroup ↥D.C) ⊓ (D.K₁.subgroupOf D.C ⊔ D.K₂.subgroupOf D.C),
      ∀ v ∈ zpowers u' ⊔ zpowers z', x * v * x⁻¹ ∈ zpowers u' ⊔ zpowers z' := by
    intro x hx v hv
    have hxS₁ : (x : G) ∈ D.S₁ := ⟨(hM2 x).mp hx.1, (hM1 x).mp hx.2⟩
    have hxz : (x : G) * D.z * (x : G)⁻¹ = D.z := z_conj_S D hs ((hM2 x).mp hx.1)
    have h1 := conj_mem_U (x := (x : G)) (u := u) (z := D.z) (hu.norm _ hxS₁)
      (by rw [hxz]; exact Subgroup.mem_sup_right (mem_zpowers _))
    rw [hM3]
    exact h1 _ ((hM3 v).mp hv)
  have ht'T : t' ∈ (T : Subgroup ↥D.C) := (hM2 t').mpr hs.syl.t_mem
  have ht2 : orderOf t' = 2 := by rw [ht', Subgroup.orderOf_mk]; exact hs.syl.t_ord
  have htt : t' * t' = 1 := Subtype.ext (t_mul_t' D hs)
  have hswap : (D.K₁.subgroupOf D.C).map (MulAut.conj t').toMonoidHom = D.K₂.subgroupOf D.C := by
    apply le_antisymm
    · rintro _ ⟨y, hy, rfl⟩
      have hy' : y ∈ D.K₁.subgroupOf D.C := hy
      rw [Subgroup.mem_subgroupOf] at hy' ⊢
      exact t_conj_K₁' D hs _ hy'
    · intro x hx
      rw [Subgroup.mem_subgroupOf] at hx
      have hy : t' * x * t'⁻¹ ∈ D.K₁.subgroupOf D.C := by
        rw [Subgroup.mem_subgroupOf]
        exact t_conj_K₂' D hs _ hx
      refine ⟨t' * x * t'⁻¹, hy, ?_⟩
      show t' * (t' * x * t'⁻¹) * t'⁻¹ = x
      calc t' * (t' * x * t'⁻¹) * t'⁻¹ = (t' * t') * x * (t' * t')⁻¹ := by group
        _ = x := by rw [htt]; group
  have hut : u * D.t = D.t * u := mem_centralizer_singleton_iff.mp (Ict_le_Ct D hs hu.mem_I)
  have hzt : D.z * D.t = D.t * D.z := z_comm_t' D hs
  have hnormt : ∀ v ∈ zpowers u' ⊔ zpowers z', t' * v * t'⁻¹ ∈ zpowers u' ⊔ zpowers z' := by
    intro v hv
    have hxu : D.t * u * D.t⁻¹ ∈ zpowers u ⊔ zpowers D.z := by
      have : D.t * u * D.t⁻¹ = u := by
        calc D.t * u * D.t⁻¹ = u * D.t * D.t⁻¹ := by rw [hut]
          _ = u := by group
      rw [this]; exact Subgroup.mem_sup_left (mem_zpowers _)
    have hxz : D.t * D.z * D.t⁻¹ ∈ zpowers u ⊔ zpowers D.z := by
      have : D.t * D.z * D.t⁻¹ = D.z := by
        calc D.t * D.z * D.t⁻¹ = D.z * D.t * D.t⁻¹ := by rw [hzt]
          _ = D.z := by group
      rw [this]; exact Subgroup.mem_sup_right (mem_zpowers _)
    rw [hM3]
    exact conj_mem_U hxu hxz _ ((hM3 v).mp hv)
  have hcard : Nat.card ↥((T : Subgroup ↥D.C) ⊓ D.K₁.subgroupOf D.C) * 2 = 2 ^ (D.n + 1) := by
    have hmap : ((T : Subgroup ↥D.C) ⊓ D.K₁.subgroupOf D.C).map D.C.subtype =
        (D.S : Subgroup G) ⊓ D.K₁ := by
      rw [Subgroup.map_inf _ _ _ D.C.subtype_injective, hT,
        Subgroup.map_subgroupOf_eq_of_le (S_le_C' D hs),
        Subgroup.map_subgroupOf_eq_of_le (K₁_le_C' D hs)]
    have := Subgroup.card_map_of_injective
      (K := (T : Subgroup ↥D.C) ⊓ D.K₁.subgroupOf D.C) D.C.subtype_injective
    rw [hmap, Q₁_card_pow D hs] at this
    rw [← this, pow_succ]
  obtain ⟨B₁, B₂, y, hy, hR, hcomm, hinf, d₁, d₂, d₃, d₄⟩ :=
    IVK.Proofs2.ivk_3_1i_fixed F₁ F₂ ↥D.C (D.K₁.subgroupOf D.C) (D.K₂.subgroupOf D.C) hprod z'
      hz'mem hz1 T u' hu'mem hu2 hune hnorm t' ht'T ht2 hswap hnormt D.n hcard
  have hY : ((T : Subgroup ↥D.C) ⊓ (D.K₁.subgroupOf D.C ⊔ D.K₂.subgroupOf D.C)) ⊔ zpowers t' =
      (T : Subgroup ↥D.C) := by
    apply le_antisymm
    · exact sup_le inf_le_left (zpowers_le.mpr ht'T)
    · intro x hx
      have hxS : (x : G) ∈ (D.S : Subgroup G) := (hM2 x).mp hx
      rcases mem_K_or_mul_of_index_two (D.S : Subgroup G) D.K D.t hs.syl.t_mem
          (t_not_mem_K D.ext3 hs) hs.syl.index (x : G) hxS with h | h
      · exact Subgroup.mem_sup_left ⟨hx, (hM1 x).mpr h⟩
      · have h1 : x * t' ∈ (T : Subgroup ↥D.C) ⊓
            (D.K₁.subgroupOf D.C ⊔ D.K₂.subgroupOf D.C) :=
          ⟨(T : Subgroup ↥D.C).mul_mem hx ht'T, (hM1 _).mpr h⟩
        have : x = (x * t') * t' := by rw [mul_assoc, htt, mul_one]
        rw [this]
        exact Subgroup.mul_mem _ (Subgroup.mem_sup_left h1) (Subgroup.mem_sup_right (mem_zpowers t'))
  rw [hY] at hR
  have hstruct : SPLDihStruct D.n (centralizer ({u'} : Set ↥D.C) ⊓ (T : Subgroup ↥D.C)) :=
    ⟨B₁, B₂, y, hy, hR, hcomm, hinf, d₁, d₂, d₃, d₄⟩
  have hmap : (centralizer ({u'} : Set ↥D.C) ⊓ (T : Subgroup ↥D.C)).map D.C.subtype =
      (D.S : Subgroup G) ⊓ centralizer ({u} : Set G) := by
    ext x
    constructor
    · rintro ⟨r, ⟨hrc, hrT⟩, rfl⟩
      refine ⟨(hM2 r).mp hrT, ?_⟩
      have := mem_centralizer_singleton_iff.mp hrc
      exact mem_centralizer_singleton_iff.mpr (congrArg Subtype.val this)
    · rintro ⟨hxS, hxc⟩
      have hxC : x ∈ D.C := S_le_C' D hs hxS
      refine ⟨⟨x, hxC⟩, ⟨?_, (hM2 _).mpr hxS⟩, rfl⟩
      exact mem_centralizer_singleton_iff.mpr (Subtype.ext (mem_centralizer_singleton_iff.mp hxc))
  rw [← hmap]
  exact hstruct.map D.C.subtype D.C.subtype_injective

theorem ct1a (hs : SPLSetup D.toSPLNot0) {u : G} (hu : SPLCtU D u) :
    ∀ T : Subgroup G, T ≤ D.Ct → IsPGroup 2 T →
      (∀ P : Subgroup G, P ≤ D.Ct → IsPGroup 2 P → T ≤ P → P = T) →
      ∃ B₁ B₂ : Subgroup G, ∃ y : G, B₁ ≤ T ∧ B₂ ≤ T ∧ y ∈ T ∧ orderOf y = 2 ∧
        T = (B₁ ⊔ B₂) ⊔ zpowers y ∧ (∀ a ∈ B₁, ∀ b ∈ B₂, a * b = b * a) ∧ B₁ ⊓ B₂ = ⊥ ∧
        IVK.IsDihedralOrder ↥B₁ (2 ^ (D.n - 1)) ∧ IVK.IsDihedralOrder ↥B₂ (2 ^ (D.n - 1)) ∧
        IVK.IsDihedralOrder ↥(B₁ ⊔ zpowers y) (2 ^ D.n) ∧
        IVK.IsDihedralOrder ↥(B₂ ⊔ zpowers y) (2 ^ D.n) := by
  intro T hTle hTp hTmax
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have htu : IsConj D.t u := hs.syl.inv_K (Ict_le_K D hs hu.mem_I) hu.ord (u_ne_z D hs hu)
  obtain ⟨v, hv⟩ := isConj_iff.mp htu.symm
  have hvt : ∀ x : G, x * u = u * x ↔ (v * x * v⁻¹) * D.t = D.t * (v * x * v⁻¹) := by
    intro x
    constructor
    · intro h
      rw [← hv]
      calc v * x * v⁻¹ * (v * u * v⁻¹) = v * (x * u) * v⁻¹ := by group
        _ = v * (u * x) * v⁻¹ := by rw [h]
        _ = (v * u * v⁻¹) * (v * x * v⁻¹) := by group
    · intro h
      rw [← hv] at h
      have h2 : v * (x * u) * v⁻¹ = v * (u * x) * v⁻¹ := by
        calc v * (x * u) * v⁻¹ = v * x * v⁻¹ * (v * u * v⁻¹) := by group
          _ = (v * u * v⁻¹) * (v * x * v⁻¹) := h
          _ = v * (u * x) * v⁻¹ := by group
      exact mul_left_cancel (mul_right_cancel h2)
  have hvt' : ∀ p : G, p * D.t = D.t * p → (v⁻¹ * p * v) * u = u * (v⁻¹ * p * v) := by
    intro p hp
    apply (hvt _).mpr
    have e : v * (v⁻¹ * p * v) * v⁻¹ = p := by group
    rw [e]; exact hp
  have hstruct := ct1a_core D hs hu
  set Cu : Subgroup G := (D.S : Subgroup G) ⊓ centralizer ({u} : Set G) with hCu
  set T₀ : Subgroup G := Cu.map (MulAut.conj v).toMonoidHom with hT₀
  have hT₀le : T₀ ≤ D.Ct := by
    rintro _ ⟨x, hx, rfl⟩
    have hxu : x * u = u * x := mem_centralizer_singleton_iff.mp hx.2
    exact mem_centralizer_singleton_iff.mpr ((hvt x).mp hxu)
  have hT₀p : IsPGroup 2 T₀ := (IsPGroup.to_le D.S.isPGroup' inf_le_left).map _
  have hT₀max : ∀ P : Subgroup G, P ≤ D.Ct → IsPGroup 2 P → T₀ ≤ P → P = T₀ := by
    intro P hPle hPp hle
    set P' : Subgroup G := P.map (MulAut.conj v⁻¹).toMonoidHom with hP'
    have hP'c : P' ≤ centralizer ({u} : Set G) := by
      rintro _ ⟨p, hp, rfl⟩
      refine mem_centralizer_singleton_iff.mpr ?_
      have := hvt' p (mem_centralizer_singleton_iff.mp (hPle hp))
      simpa [MulAut.conj_apply] using this
    have hCuP' : Cu ≤ P' := by
      intro x hx
      exact ⟨v * x * v⁻¹, hle ⟨x, hx, rfl⟩, by simp; group⟩
    have hPeq : P' = Cu := CS_maximal D hs hu P' hP'c (hPp.map _) hCuP'
    apply le_antisymm _ hle
    intro p hp
    have hmem : (MulAut.conj v⁻¹).toMonoidHom p ∈ Cu := by
      rw [← hPeq]; exact ⟨p, hp, rfl⟩
    exact ⟨_, hmem, by simp; group⟩
  obtain ⟨x, -, hx⟩ := sylow_conj_of_maximal D.Ct hT₀le hT₀p hT₀max hTle hTp hTmax
  have hT₀struct : SPLDihStruct D.n T₀ := hstruct.map _ (MulAut.conj v).injective
  have hTstruct : SPLDihStruct D.n T := by
    rw [hx]; exact hT₀struct.map _ (MulAut.conj x).injective
  obtain ⟨B₁, B₂, y, hy, hR, hc, hi, d₁, d₂, d₃, d₄⟩ := hTstruct
  refine ⟨B₁, B₂, y, ?_, ?_, ?_, hy, hR, hc, hi, d₁, d₂, d₃, d₄⟩
  · rw [hR]; exact le_trans le_sup_left le_sup_left
  · rw [hR]; exact le_trans le_sup_right le_sup_left
  · rw [hR]; exact Subgroup.mem_sup_right (mem_zpowers y)

end C1a

end CFSG.GH74.GLS.SP.Local
