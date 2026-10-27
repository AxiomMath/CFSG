module

public import CFSG.ClassicalInvolution.Q3.Q3TIYTPAut
public import CFSG.ClassicalInvolution.Q3.Q3OFAlphaF
public import CFSG.ClassicalInvolution.Q3.Q3TAxis
public import CFSG.ClassicalInvolution.Q3.Q3TY11
public import CFSG.ClassicalInvolution.RouteD.TWZLayer
public import CFSG.ClassicalInvolution.Q3.Q3OFStmt
public import CFSG.ClassicalInvolution.Q3.Q3T6AutNorm

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3TIY

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Balance CFSG.ClassicalInvolution.Balance.Bootstrap
  CFSG.ClassicalInvolution.RouteD CFSG.ClassicalInvolution.Q3.Q3W CFSG.Assembly.Dichotomy
  CFSG.ClassicalInvolution.Q3.Q3OF CFSG.ClassicalInvolution.Q3.Q3T6
  CFSG.ClassicalInvolution.Generic.DeltaClosure CFSG.ClassicalInvolution.Disconnected.AschTight
  CFSG.ClassicalInvolution.RouteD.TWZ
open CFSG.ClassicalInvolution.RouteD.TwinY (IsTwinAt TwinElt TwinElt.u)
open scoped MatrixGroups commutatorElement

variable {G : Type} [Group G] [Finite G] [IsSimpleGroup G] {K T : Subgroup G} {z : G}

section Odd

theorem odd_orderOf_of_mem_oddCoreIn {X : Subgroup G} {r : G} (hr : r ∈ oddCoreIn X) :
    Odd (orderOf r) := by
  have h1 : orderOf (⟨r, hr⟩ : ↥(oddCoreIn X)) ∣ Nat.card ↥(oddCoreIn X) :=
    orderOf_dvd_natCard _
  rw [Subgroup.orderOf_mk] at h1
  exact (odd_card_oddCoreIn X).of_dvd_nat h1

theorem mem_of_sq_mem_of_odd {H : Subgroup G} {r : G} (hodd : Odd (orderOf r))
    (h : r * r ∈ H) : r ∈ H := by
  obtain ⟨k, hk⟩ := hodd
  have : r = (r * r) ^ (k + 1) := by
    have h1 : r ^ (orderOf r) = 1 := pow_orderOf_eq_one r
    calc r = r * r ^ (2 * k + 1) := by rw [← hk, h1, mul_one]
      _ = (r * r) ^ (k + 1) := by
        rw [← pow_two, ← pow_mul, ← pow_succ']
        congr 1
  rw [this]
  exact H.pow_mem h _

end Odd

section Member

theorem sl2Three_eq_neg_one_of_sq_eq_one :
    ∀ s : SL(2, ZMod 3), s * s = 1 → s ≠ 1 → s = -1 := by
  decide +kernel

theorem equiv_mk_involution_eq_neg_one {N : Subgroup G} {z : G} (hN : IsClassicalMember3 N z)
    (e : N ⧸ classicalInvolutionOddCore N ≃* SL(2, ZMod 3)) :
    e (QuotientGroup.mk (⟨z, hN.mem⟩ : N)) = -1 := by
  have h2 : orderOf (e (QuotientGroup.mk (⟨z, hN.mem⟩ : N))) = 2 := by
    rw [MulEquiv.orderOf_eq]
    exact orderOf_mk_oddCore_eq_two (Y := N) (z := (⟨z, hN.mem⟩ : N))
      (by rw [Subgroup.orderOf_mk]; exact hN.orderOf_eq_two)
  have hsq : e (QuotientGroup.mk (⟨z, hN.mem⟩ : N)) * e (QuotientGroup.mk (⟨z, hN.mem⟩ : N)) =
      1 := by
    have := pow_orderOf_eq_one (e (QuotientGroup.mk (⟨z, hN.mem⟩ : N)))
    rwa [h2, pow_two] at this
  have hne : e (QuotientGroup.mk (⟨z, hN.mem⟩ : N)) ≠ 1 := fun h => by
    rw [h, orderOf_one] at h2
    omega
  exact sl2Three_eq_neg_one_of_sq_eq_one _ hsq hne

theorem centralizes_of_comm_order_four {Ω : Set (Subgroup G)} (hΩ : ConjInvariant Ω)
    {N : Subgroup G} (hN : N ∈ centralizingMembers Ω {z})
    (hiso : ∀ M ∈ centralizingMembers Ω {z}, M ≠ N → Commutes N M)
    (hclsN : IsClassicalMember3 N z) (hexN : classicalInvolutionOddCore N = ⊥)
    {a : G} (haN : a ∈ N) (haa : a * a = z) {r : G} (hrz : r * z = z * r)
    (hodd : Odd (orderOf r)) (hra : r * a = a * r) : ∀ k ∈ N, r * k = k * r := by
  have hrC : r ∈ Subgroup.centralizer ({z} : Set G) :=
    Subgroup.mem_centralizer_singleton_iff.mpr hrz
  have hrN : r ∈ Subgroup.normalizer (N : Set G) := by
    rw [Asc77.mem_normalizer_iff_conjSub_eq]
    by_contra hne
    have hmem : conjSub r N ∈ centralizingMembers Ω {z} :=
      conjSub_mem_centralizingMembers hΩ hrC hN
    have hcomm := hiso _ hmem hne
    have haN' : a ∈ conjSub r N := by
      rw [mem_conjSub_iff]
      have : r⁻¹ * a * r = a := by
        calc r⁻¹ * a * r = r⁻¹ * (a * r) := by rw [mul_assoc]
          _ = r⁻¹ * (r * a) := by rw [hra]
          _ = a := by rw [← mul_assoc, inv_mul_cancel, one_mul]
      rw [this]
      exact haN
    exact not_central_of_sq hclsN haN haa fun k hk => (hcomm k hk a haN').symm
  obtain ⟨e⟩ := hclsN.nonempty_equiv
  set n : Subgroup.normalizer (N : Set G) := ⟨r, hrN⟩ with hn
  have hΨ : normalizerToAutSL3 e n = 1 := by
    refine sl2Three_mulAut_eq_one_of_odd_fix (normalizerToAutSL3 e n) (m := orderOf r) hodd ?_
      (s := e (QuotientGroup.mk (⟨a, haN⟩ : N))) ?_ ?_
    · rw [← map_pow]
      have : n ^ orderOf r = 1 := Subtype.ext (by simp [hn])
      rw [this, map_one]
    · rw [← map_mul, ← QuotientGroup.mk_mul]
      have : (⟨a, haN⟩ : N) * ⟨a, haN⟩ = ⟨z, hclsN.mem⟩ := Subtype.ext haa
      rw [this]
      exact equiv_mk_involution_eq_neg_one hclsN e
    · rw [normalizerToAutSL3_apply]
      congr 2
      apply Subtype.ext
      rw [normalizerConj_apply_coe]
      show r * a * r⁻¹ = a
      rw [hra]
      group
  intro k hk
  have h1 := (normalizerToAutSL3_eq_one_iff e n).mp hΨ k hk
  have h2 : Asc77.oddCoreOf N = ⊥ := by
    unfold Asc77.oddCoreOf
    rw [hexN, Subgroup.map_bot]
  rw [h2, Subgroup.mem_bot] at h1
  exact commutatorElement_eq_one_iff_mul_comm.mp h1

end Member

section Twin

theorem routeD3_nonabelian {K : Subgroup G} {z : G} (hR : RouteD3Setup K z) :
    ∃ a b : G, a * b ≠ b * a := by
  by_contra hcon
  push Not at hcon
  apply hR.cls.not_le_center
  intro x _
  rw [Subgroup.mem_center_iff]
  intro g
  exact hcon g x

structure TwinSetup3 (K T : Subgroup G) (z : G) : Prop where
  setup : RouteD3Setup K z
  twin : IsTwinAt (conjClass3 K) K T z
  clsT : IsClassicalMember3 T z

namespace TwinSetup3

variable (h : TwinSetup3 K T z)

include h

theorem hΩ : InClass3 (conjClass3 K) := h.setup.inClass

theorem hex : ExactMembers3 (conjClass3 K) := h.setup.setup.1

theorem hKΩ : K ∈ conjClass3 K := ⟨1, conjSub_one K⟩

theorem hz2 : z * z = 1 := h.setup.cls.isCentralInvolution.sq

theorem hKT : Commutes K T := h.twin.comm_K T h.twin.mem h.twin.ne

theorem hKz : K ∈ centralizingMembers (conjClass3 K) {z} :=
  ⟨h.hKΩ, isSubnormal_le h.setup.cls.subnormal⟩

theorem hTz : T ∈ centralizingMembers (conjClass3 K) {z} := h.twin.mem

theorem hKiso : ∀ N ∈ centralizingMembers (conjClass3 K) {z}, N ≠ K → Commutes K N :=
  fun N hN hNK => h.twin.comm_K N hN hNK

theorem hTiso : ∀ N ∈ centralizingMembers (conjClass3 K) {z}, N ≠ T → Commutes T N :=
  fun N hN hNT => h.twin.comm_T N hN hNT

theorem hO : LocalOddCentralizer3 (conjClass3 K) :=
  localOddCentralizer3_of_lieSystem lieSystemOddCentralizer3_proved h.setup.ih

theorem hnc {b : G} (hb : b ≠ 1) : b ∉ Subgroup.center G := fun hbc =>
  Balance.not_subset_center_of_ne_one (routeD3_nonabelian h.setup) hb
    (Set.singleton_subset_iff.mpr hbc)

theorem oddCore_z : involutionOddCore z = ⊥ :=
  involutionOddCore_eq_bot_of_member h.setup h.hKΩ h.setup.cls

theorem oddCore_member {J : Subgroup G} {w : G} (hJ : J ∈ conjClass3 K)
    (hw : IsClassicalMember3 J w) : involutionOddCore w = ⊥ :=
  involutionOddCore_eq_bot_of_member h.setup hJ hw

theorem memΩu (e : TwinElt K T z) {N : Subgroup G} (hN : N ∈ centralizingMembers (conjClass3 K) {z})
    (hNK : N ≠ K) (hNT : N ≠ T) : N ∈ centralizingMembers (conjClass3 K) {e.u} :=
  e.mem_centralizingMembers_u hN.1 (Commutes.symm (h.hKiso N hN hNK))
    (Commutes.symm (h.hTiso N hN hNT))

theorem u_mem_layer (e : TwinElt K T z) : e.u ∈ centralizingLayer (conjClass3 K) {z} :=
  (sup_le (le_centralizingLayer h.hKz) (le_centralizingLayer h.hTz)) e.u_mem_sup

theorem u_order (e : TwinElt K T z) : orderOf e.u = 2 :=
  Q3TY.twinElt_orderOf_u3 e h.setup.cls (h.hex K h.hKΩ) h.hKT

theorem z_comm_u (e : TwinElt K T z) : z * e.u = e.u * z :=
  (e.u_comm_z (isSubnormal_le h.setup.cls.subnormal) (isSubnormal_le h.clsT.subnormal)).symm

theorem a_comm_u (e : TwinElt K T z) : e.a * e.u = e.u * e.a := by
  have hc : e.a * e.a' = e.a' * e.a := h.hKT _ e.mem_a _ e.mem_a'
  unfold TwinElt.u
  calc e.a * (e.a * e.a') = e.a * (e.a' * e.a) := by rw [hc]
    _ = (e.a * e.a') * e.a := by group

theorem a'_comm_u (e : TwinElt K T z) : e.a' * e.u = e.u * e.a' := by
  have hc : e.a * e.a' = e.a' * e.a := h.hKT _ e.mem_a _ e.mem_a'
  unfold TwinElt.u
  calc e.a' * (e.a * e.a') = (e.a' * e.a) * e.a' := by group
    _ = (e.a * e.a') * e.a' := by rw [hc]

theorem comm_of_balance (e : TwinElt K T z) {r g : G} (hr : r ∈ involutionOddCore e.u)
    (hrz : r * z = z * r) (hg : g ∈ centralizingLayer (conjClass3 K) {z})
    (hgu : g * e.u = e.u * g) : r * g = g * r := by
  have h1 := commutator_mem_involutionOddCore_of_localOddCentralizer3 h.hΩ.conjInvariant h.hO
    (h.hnc h.setup.cls.ne_one) (h.u_mem_layer e) (h.u_order e) (r := r) (g := g)
    ⟨hr, Subgroup.mem_centralizer_singleton_iff.mpr hrz⟩
    ⟨hg, Subgroup.mem_centralizer_singleton_iff.mpr hgu⟩
  rw [h.oddCore_z, Subgroup.mem_bot] at h1
  exact commutatorElement_eq_one_iff_mul_comm.mp h1

theorem comm_member (e : TwinElt K T z) {r : G} (hr : r ∈ involutionOddCore e.u)
    (hrz : r * z = z * r) {M : Subgroup G} (hM : M ∈ centralizingMembers (conjClass3 K) {z}) :
    ∀ m ∈ M, r * m = m * r := by
  have hodd : Odd (orderOf r) := odd_orderOf_of_mem_oddCoreIn (X := Subgroup.centralizer {e.u}) hr
  by_cases hMK : M = K
  · subst hMK
    refine centralizes_of_comm_order_four h.hΩ.conjInvariant hM h.hKiso h.setup.cls
      (h.hex M h.hKΩ) e.mem_a e.mul_self_a hrz hodd ?_
    exact h.comm_of_balance e hr hrz (le_centralizingLayer h.hKz e.mem_a) (h.a_comm_u e)
  by_cases hMT : M = T
  · subst hMT
    refine centralizes_of_comm_order_four h.hΩ.conjInvariant hM h.hTiso h.clsT
      (h.hex M h.twin.mem.1) e.mem_a' e.mul_self_a' hrz hodd ?_
    exact h.comm_of_balance e hr hrz (le_centralizingLayer h.hTz e.mem_a') (h.a'_comm_u e)
  intro m hm
  have hMu := h.memΩu e hM hMK hMT
  exact h.comm_of_balance e hr hrz (le_centralizingLayer hM hm)
    (Subgroup.mem_centralizer_singleton_iff.mp (hMu.2 hm))

theorem layer_le_centralizer (e : TwinElt K T z) {r : G} (hr : r ∈ involutionOddCore e.u)
    (hrz : r * z = z * r) :
    centralizingLayer (conjClass3 K) {z} ≤ Subgroup.centralizer ({r} : Set G) :=
  iSup₂_le fun _ hM m hm =>
    Subgroup.mem_centralizer_singleton_iff.mpr (h.comm_member e hr hrz hM m hm).symm

theorem z_mem_layer : z ∈ centralizingLayer (conjClass3 K) {z} :=
  le_centralizingLayer h.hKz h.setup.cls.mem

theorem centralizer_layer_normalized {g : G} (hg : g ∈ Subgroup.centralizer ({z} : Set G)) :
    g ∈ Subgroup.normalizer
      ((Subgroup.centralizer (centralizingLayer (conjClass3 K) {z} : Set G) : Subgroup G) :
        Set G) := by
  have hgn : g ∈ Subgroup.normalizer (centralizingLayer (conjClass3 K) {z} : Set G) :=
    centralizer_le_normalizer_centralizingLayer h.hΩ.conjInvariant z hg
  have key : ∀ g : G, g ∈ Subgroup.normalizer (centralizingLayer (conjClass3 K) {z} : Set G) →
      ∀ x ∈ Subgroup.centralizer (centralizingLayer (conjClass3 K) {z} : Set G),
        g * x * g⁻¹ ∈ Subgroup.centralizer (centralizingLayer (conjClass3 K) {z} : Set G) := by
    intro g hgn x hx
    rw [Subgroup.mem_centralizer_iff] at hx ⊢
    intro m hm
    have hm' : g⁻¹ * m * g ∈ centralizingLayer (conjClass3 K) {z} := by
      have := (Subgroup.mem_normalizer_iff.mp ((Subgroup.normalizer _).inv_mem hgn) m).mp hm
      simpa using this
    have := hx _ hm'
    calc m * (g * x * g⁻¹) = g * ((g⁻¹ * m * g) * x) * g⁻¹ := by group
      _ = g * (x * (g⁻¹ * m * g)) * g⁻¹ := by rw [this]
      _ = g * x * g⁻¹ * m := by group
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · exact key g hgn x
  · intro hx
    have := key g⁻¹ ((Subgroup.normalizer _).inv_mem hgn) _ hx
    simpa [mul_assoc] using this

theorem oddCore_inf_centralizer_eq_bot (e : TwinElt K T z) :
    involutionOddCore e.u ⊓ Subgroup.centralizer ({z} : Set G) = ⊥ := by
  set P : Subgroup G := involutionOddCore e.u with hP
  set Y : Subgroup G := centralizingLayer (conjClass3 K) {z} with hY
  set D₀ : Subgroup G := Subgroup.centralizer (Y : Set G) with hD₀
  have hPD : P ⊓ Subgroup.centralizer ({z} : Set G) ≤ D₀ := by
    intro r hr m hm
    have := h.layer_le_centralizer e hr.1 (Subgroup.mem_centralizer_singleton_iff.mp hr.2) hm
    exact Subgroup.mem_centralizer_singleton_iff.mp this
  have hD₀z : D₀ ≤ Subgroup.centralizer ({z} : Set G) :=
    Subgroup.centralizer_le (Set.singleton_subset_iff.mpr h.z_mem_layer)
  have hD₀u : D₀ ≤ Subgroup.centralizer ({e.u} : Set G) :=
    Subgroup.centralizer_le (Set.singleton_subset_iff.mpr (h.u_mem_layer e))
  have hnorm : ∀ d ∈ D₀, ∀ y ∈ P ⊓ Subgroup.centralizer ({z} : Set G),
      d * y * d⁻¹ ∈ P ⊓ Subgroup.centralizer ({z} : Set G) := by
    intro d hd y hy
    refine ⟨conj_mem_oddCoreIn (hD₀u hd) hy.1, ?_⟩
    have hdz := hD₀z hd
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hdz hy.2) ((Subgroup.inv_mem _) hdz)
  have hP₀D : D₀ ≤ Subgroup.normalizer ((P ⊓ Subgroup.centralizer ({z} : Set G) : Subgroup G) :
      Set G) := by
    intro d hd
    rw [Subgroup.mem_normalizer_iff]
    intro y
    exact ⟨hnorm d hd y, fun hy => by
      have := hnorm d⁻¹ ((Subgroup.inv_mem _) hd) _ hy
      simpa [mul_assoc] using this⟩
  have hoddP₀ : Odd (Nat.card ↥(P ⊓ Subgroup.centralizer ({z} : Set G))) :=
    (odd_card_oddCoreIn (Subgroup.centralizer ({e.u} : Set G))).of_dvd_nat
      (Subgroup.card_dvd_of_le inf_le_left)
  have h1 : P ⊓ Subgroup.centralizer ({z} : Set G) ≤ oddCoreIn D₀ :=
    le_oddCoreIn_of_normalizes hPD hP₀D hoddP₀
  have h2 : oddCoreIn D₀ ≤ oddCoreIn (Subgroup.centralizer ({z} : Set G)) := by
    refine le_oddCoreIn_of_normalizes ((oddCoreIn_le D₀).trans hD₀z) ?_ (odd_card_oddCoreIn _)
    intro g hg
    rw [Subgroup.mem_normalizer_iff]
    intro y
    have hgn := h.centralizer_layer_normalized hg
    constructor
    · exact fun hy => conj_mem_oddCoreIn_of_mem_normalizer hgn hy
    · intro hy
      have := conj_mem_oddCoreIn_of_mem_normalizer ((Subgroup.normalizer _).inv_mem hgn) hy
      simpa [mul_assoc] using this
  have h3 : oddCoreIn (Subgroup.centralizer ({z} : Set G)) = ⊥ := h.oddCore_z
  exact le_bot_iff.mp ((h1.trans h2).trans h3.le)

theorem inv_z (e : TwinElt K T z) : ∀ x ∈ involutionOddCore e.u, z * x * z⁻¹ = x⁻¹ := by
  refine inv_of_fixedPointFree (P := involutionOddCore e.u) h.hz2 ?_ ?_
  · intro x hx
    exact conj_mem_oddCoreIn (X := Subgroup.centralizer ({e.u} : Set G))
      (Subgroup.mem_centralizer_singleton_iff.mpr (h.z_comm_u e)) hx
  · intro x hx hxz
    have : x ∈ involutionOddCore e.u ⊓ Subgroup.centralizer ({z} : Set G) :=
      ⟨hx, Subgroup.mem_centralizer_singleton_iff.mpr hxz.symm⟩
    rw [h.oddCore_inf_centralizer_eq_bot e] at this
    exact Subgroup.mem_bot.mp this

section Frame

variable {J : Subgroup G} {t : G}

theorem t_comm_u (e : TwinElt K T z) (hJ : J ∈ centralizingMembers (conjClass3 K) {z})
    (hJK : J ≠ K) (hJT : J ≠ T) (clsJ : IsClassicalMember3 J t) : t * e.u = e.u * t :=
  Subgroup.mem_centralizer_singleton_iff.mp ((h.memΩu e hJ hJK hJT).2 clsJ.mem)

theorem t_comm_z (hJ : J ∈ centralizingMembers (conjClass3 K) {z}) (clsJ : IsClassicalMember3 J t) :
    t * z = z * t :=
  Subgroup.mem_centralizer_singleton_iff.mp (hJ.2 clsJ.mem)

theorem K_comm_t (hJ : J ∈ centralizingMembers (conjClass3 K) {z}) (hJK : J ≠ K)
    (clsJ : IsClassicalMember3 J t) : ∀ k ∈ K, k * t = t * k :=
  fun k hk => h.hKiso J hJ hJK k hk t clsJ.mem

theorem T_comm_t (hJ : J ∈ centralizingMembers (conjClass3 K) {z}) (hJT : J ≠ T)
    (clsJ : IsClassicalMember3 J t) : ∀ k ∈ T, k * t = t * k :=
  fun k hk => h.hTiso J hJ hJT k hk t clsJ.mem

theorem u_mem_layer_of {b : G} (e : TwinElt K T z) (hKb : ∀ k ∈ K, k * b = b * k)
    (hTb : ∀ k ∈ T, k * b = b * k) : e.u ∈ centralizingLayer (conjClass3 K) {b} := by
  have hKm : K ∈ centralizingMembers (conjClass3 K) {b} :=
    ⟨h.hKΩ, fun k hk => Subgroup.mem_centralizer_singleton_iff.mpr (hKb k hk)⟩
  have hTm : T ∈ centralizingMembers (conjClass3 K) {b} :=
    ⟨h.twin.mem.1, fun k hk => Subgroup.mem_centralizer_singleton_iff.mpr (hTb k hk)⟩
  exact (sup_le (le_centralizingLayer hKm) (le_centralizingLayer hTm)) e.u_mem_sup

theorem oddCore_inf_centralizer_t_eq_bot (e : TwinElt K T z)
    (hJ : J ∈ centralizingMembers (conjClass3 K) {z}) (hJK : J ≠ K) (hJT : J ≠ T)
    (clsJ : IsClassicalMember3 J t) :
    involutionOddCore e.u ⊓ Subgroup.centralizer ({t} : Set G) = ⊥ := by
  rw [eq_bot_iff]
  intro r hr
  have hKt := h.K_comm_t hJ hJK clsJ
  have hTt := h.T_comm_t hJ hJT clsJ
  have hzt : z ∈ centralizingLayer (conjClass3 K) {t} := by
    have hKm : K ∈ centralizingMembers (conjClass3 K) {t} :=
      ⟨h.hKΩ, fun k hk => Subgroup.mem_centralizer_singleton_iff.mpr (hKt k hk)⟩
    exact le_centralizingLayer hKm h.setup.cls.mem
  have h1 := commutator_mem_involutionOddCore_of_localOddCentralizer3 h.hΩ.conjInvariant h.hO
    (h.hnc clsJ.ne_one) (h.u_mem_layer_of e hKt hTt) (h.u_order e) (r := r) (g := z) hr
    ⟨hzt, Subgroup.mem_centralizer_singleton_iff.mpr (h.z_comm_u e)⟩
  rw [h.oddCore_member hJ.1 clsJ, Subgroup.mem_bot] at h1
  have hrz : r * z = z * r := (commutatorElement_eq_one_iff_mul_comm.mp h1)
  have : r ∈ involutionOddCore e.u ⊓ Subgroup.centralizer ({z} : Set G) :=
    ⟨hr.1, Subgroup.mem_centralizer_singleton_iff.mpr hrz⟩
  rw [h.oddCore_inf_centralizer_eq_bot e] at this
  exact this

theorem inv_t (e : TwinElt K T z) (hJ : J ∈ centralizingMembers (conjClass3 K)
    {z}) (hJK : J ≠ K) (hJT : J ≠ T) (clsJ : IsClassicalMember3 J t) :
    ∀ x ∈ involutionOddCore e.u, t * x * t⁻¹ = x⁻¹ := by
  have ht2 : t * t = 1 := Q3NT.mul_self_eq_one_of_orderOf_eq_two clsJ.orderOf_eq_two
  refine inv_of_fixedPointFree (P := involutionOddCore e.u) ht2 ?_ ?_
  · intro x hx
    exact conj_mem_oddCoreIn (X := Subgroup.centralizer ({e.u} : Set G))
      (Subgroup.mem_centralizer_singleton_iff.mpr (h.t_comm_u e hJ hJK hJT clsJ)) hx
  · intro x hx hxt
    have : x ∈ involutionOddCore e.u ⊓ Subgroup.centralizer ({t} : Set G) :=
      ⟨hx, Subgroup.mem_centralizer_singleton_iff.mpr hxt.symm⟩
    rw [h.oddCore_inf_centralizer_t_eq_bot e hJ hJK hJT clsJ] at this
    exact Subgroup.mem_bot.mp this

theorem comm_zt (e : TwinElt K T z) (hJ : J ∈ centralizingMembers (conjClass3 K) {z})
    (hJK : J ≠ K) (hJT : J ≠ T) (clsJ : IsClassicalMember3 J t) :
    ∀ x ∈ involutionOddCore e.u, x * (z * t) = (z * t) * x := by
  intro x hx
  have h1 := h.inv_z e x hx
  have h2 := h.inv_t e hJ hJK hJT clsJ x hx
  have h3 : z * x⁻¹ * z⁻¹ = x := by
    have := congrArg (fun y : G => y⁻¹) h1
    simpa [mul_assoc] using this
  have e2 : t * x = x⁻¹ * t := by
    calc t * x = (t * x * t⁻¹) * t := by group
      _ = x⁻¹ * t := by rw [h2]
  have e3 : z * x⁻¹ = x * z := by
    calc z * x⁻¹ = (z * x⁻¹ * z⁻¹) * z := by group
      _ = x * z := by rw [h3]
  calc x * (z * t) = (x * z) * t := by group
    _ = (z * x⁻¹) * t := by rw [e3]
    _ = z * (x⁻¹ * t) := by group
    _ = z * (t * x) := by rw [e2]
    _ = (z * t) * x := by group

theorem le_oddCore_zt (e : TwinElt K T z) (hJ : J ∈ centralizingMembers (conjClass3 K) {z})
    (hJK : J ≠ K) (hJT : J ≠ T) (clsJ : IsClassicalMember3 J t) (htz : t ≠ z) :
    involutionOddCore e.u ≤ involutionOddCore (z * t) := by
  intro r hr
  have hodd : Odd (orderOf r) := odd_orderOf_of_mem_oddCoreIn (X := Subgroup.centralizer {e.u}) hr
  have hKt := h.K_comm_t hJ hJK clsJ
  have hTt := h.T_comm_t hJ hJT clsJ
  have hKzt : ∀ k ∈ K, k * (z * t) = (z * t) * k := fun k hk => by
    have h1 : k * z = z * k := Subgroup.mem_centralizer_singleton_iff.mp (h.hKz.2 hk)
    calc k * (z * t) = (k * z) * t := by group
      _ = z * (k * t) := by rw [h1]; group
      _ = z * (t * k) := by rw [hKt k hk]
      _ = (z * t) * k := by group
  have hTzt : ∀ k ∈ T, k * (z * t) = (z * t) * k := fun k hk => by
    have h1 : k * z = z * k := Subgroup.mem_centralizer_singleton_iff.mp (h.hTz.2 hk)
    calc k * (z * t) = (k * z) * t := by group
      _ = z * (k * t) := by rw [h1]; group
      _ = z * (t * k) := by rw [hTt k hk]
      _ = (z * t) * k := by group
  have hzt1 : z * t ≠ 1 := fun h1 => htz (by
    have : t = z⁻¹ := eq_inv_of_mul_eq_one_right h1
    rw [this]
    exact (inv_eq_of_mul_eq_one_right h.hz2))
  have hY : e.u ∈ centralizingLayer (conjClass3 K) {z * t} := h.u_mem_layer_of e hKzt hTzt
  have hzY : z ∈ centralizingLayer (conjClass3 K) {z * t} :=
    le_centralizingLayer (⟨h.hKΩ, fun k hk => Subgroup.mem_centralizer_singleton_iff.mpr
      (hKzt k hk)⟩ : K ∈ centralizingMembers (conjClass3 K) {z * t}) h.setup.cls.mem
  have hrC : r ∈ Subgroup.centralizer ({z * t} : Set G) :=
    Subgroup.mem_centralizer_singleton_iff.mpr (h.comm_zt e hJ hJK hJT clsJ r hr)
  have h1 := commutator_mem_involutionOddCore_of_localOddCentralizer3 h.hΩ.conjInvariant h.hO
    (h.hnc hzt1) hY (h.u_order e) (r := r) (g := z) ⟨hr, hrC⟩
    ⟨hzY, Subgroup.mem_centralizer_singleton_iff.mpr (h.z_comm_u e)⟩
  have h3 : z * r⁻¹ * z⁻¹ = r := by
    have := congrArg (fun y : G => y⁻¹) (h.inv_z e r hr)
    simpa [mul_assoc] using this
  have h2 : ⁅r, z⁆ = r * r := by
    calc ⁅r, z⁆ = r * (z * r⁻¹ * z⁻¹) := by simp only [commutatorElement_def]; group
      _ = r * r := by rw [h3]
  rw [h2] at h1
  exact mem_of_sq_mem_of_odd hodd h1

theorem oddCore_eq_bot (e : TwinElt K T z) (hJ : J ∈ centralizingMembers (conjClass3 K) {z})
    (hJK : J ≠ K) (hJT : J ≠ T) (clsJ : IsClassicalMember3 J t) (htz : t ≠ z)
    (hα : alphaCore (Subgroup.closure ({z, t} : Set G)) = ⊥) : involutionOddCore e.u = ⊥ := by
  rw [eq_bot_iff]
  intro r hr
  have ht2 : t * t = 1 := Q3NT.mul_self_eq_one_of_orderOf_eq_two clsJ.orderOf_eq_two
  have htz' : t * z = z * t := h.t_comm_z hJ clsJ
  have hα' : alphaCore (Subgroup.closure ({t, z} : Set G)) = ⊥ := by
    rwa [Set.pair_comm]
  have hiff := (alphaCore_pair_eq_bot_iff ht2 h.hz2 htz' clsJ.ne_one h.setup.cls.ne_one htz
    h.oddCore_z).mp hα'
  have hmem : r ∈ involutionOddCore (t * z) := by
    rw [htz']
    exact h.le_oddCore_zt e hJ hJK hJT clsJ htz hr
  have hzr : z * r = r * z := hiff.2 r hmem
  have : r ∈ involutionOddCore e.u ⊓ Subgroup.centralizer ({z} : Set G) :=
    ⟨hr, Subgroup.mem_centralizer_singleton_iff.mpr hzr.symm⟩
  rw [h.oddCore_inf_centralizer_eq_bot e] at this
  exact this

end Frame

end TwinSetup3

end Twin

end CFSG.ClassicalInvolution.Q3.Q3TIY
