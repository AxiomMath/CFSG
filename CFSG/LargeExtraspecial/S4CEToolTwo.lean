module

public import CFSG.LargeExtraspecial.S4CETool
public import CFSG.GroupTheory.AbelianNormalCoprimeComplementLifting

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.S4

open Subgroup
open scoped commutatorElement Pointwise

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] {K : Type*} [Group K]

@[expose] def stabIn (X : Subgroup (V ≃ₗ[ZMod 2] V)) (a : V) : Subgroup (V ≃ₗ[ZMod 2] V) where
  carrier := {g | g ∈ X ∧ g a = a}
  mul_mem' := fun {g g'} hg hg' => ⟨mul_mem hg.1 hg'.1, by rw [LinearEquiv.mul_apply, hg'.2, hg.2]⟩
  one_mem' := ⟨one_mem _, rfl⟩
  inv_mem' := fun {g} hg => ⟨inv_mem hg.1, by
    conv_lhs => rw [← hg.2]
    exact inv_apply_self' g a⟩

theorem mem_stabIn {X : Subgroup (V ≃ₗ[ZMod 2] V)} {a : V} {g : V ≃ₗ[ZMod 2] V} :
    g ∈ stabIn X a ↔ g ∈ X ∧ g a = a :=
  Iff.rfl

theorem card_sup_of_normal_of_inf_eq_bot {N U : Subgroup K} [N.Normal] (hNU : N ⊓ U = ⊥) :
    Nat.card ↥(N ⊔ U) = Nat.card N * Nat.card U := by
  let f : N × U → ↥(N ⊔ U) := fun p =>
    ⟨p.1 * p.2, mul_mem (mem_sup_left p.1.2) (mem_sup_right p.2.2)⟩
  have hf : Function.Bijective f := by
    constructor
    · rintro ⟨n, u⟩ ⟨n', u'⟩ heq
      have e : (n : K) * u = n' * u' := congrArg Subtype.val heq
      have h1 : (n' : K)⁻¹ * n = u' * (u : K)⁻¹ := by
        calc (n' : K)⁻¹ * n = (n' : K)⁻¹ * (n * u) * (u : K)⁻¹ := by group
          _ = (n' : K)⁻¹ * (n' * u') * (u : K)⁻¹ := by rw [e]
          _ = u' * (u : K)⁻¹ := by group
      have hmem : (n' : K)⁻¹ * n ∈ N ⊓ U :=
        mem_inf.mpr ⟨mul_mem (inv_mem n'.2) n.2, h1 ▸ mul_mem u'.2 (inv_mem u.2)⟩
      rw [hNU, mem_bot, inv_mul_eq_one] at hmem
      have hn : n = n' := Subtype.ext hmem.symm
      subst hn
      have hu : u = u' := Subtype.ext (mul_left_cancel e)
      rw [hu]
    · rintro ⟨x, hx⟩
      have hx' : x ∈ ((N ⊔ U : Subgroup K) : Set K) := hx
      rw [normal_mul] at hx'
      obtain ⟨n, hn, u, hu, rfl⟩ := hx'
      exact ⟨(⟨n, hn⟩, ⟨u, hu⟩), rfl⟩
  rw [← Nat.card_congr (Equiv.ofBijective f hf), Nat.card_prod]

namespace CEHyp

variable {π : K →* (V ≃ₗ[ZMod 2] V)} {E : Subgroup K} {a : V}
  {X E₀ : Subgroup (V ≃ₗ[ZMod 2] V)} (h : CEHyp π E a X E₀)
include h

theorem map_comap_stabIn : ((stabIn ⊤ a).comap π).map π = stabIn X a := by
  ext g
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨h.range_eq ▸ ⟨x, rfl⟩, hx.2⟩
  · rintro ⟨hg, hga⟩
    obtain ⟨x, rfl⟩ : g ∈ π.range := h.range_eq ▸ hg
    exact ⟨x, ⟨mem_top _, hga⟩, rfl⟩

theorem eq_of_mem {e e' : K} (he : e ∈ E) (he' : e' ∈ E) (hπ : π e = π e') : e = e' :=
  h.eq_of_mem_Eb (k := 1) (by rwa [Eb_one]) (by rwa [Eb_one]) hπ

theorem le_commutator_of_le_commutator (hperf : E₀ ≤ ⁅E₀, stabIn X a⁆) :
    E ≤ ⁅E, (stabIn ⊤ a).comap π⁆ := by
  intro e he
  have hπe : π e ∈ (⁅E, (stabIn ⊤ a).comap π⁆).map π := by
    rw [map_commutator, h.map_eq, h.map_comap_stabIn]
    exact hperf (h.map_eq ▸ ⟨e, he, rfl⟩)
  obtain ⟨c, hc, hce⟩ := hπe
  have hcE : c ∈ E := by
    refine (commutator_le.mpr fun e' he' x hx => ?_) hc
    rw [commutatorElement_def, show e' * x * e'⁻¹ * x⁻¹ = e' * (x * e'⁻¹ * x⁻¹) by group]
    exact mul_mem he' (h.conj_mem_of_apply_eq hx.2 (inv_mem he'))
  rwa [← h.eq_of_mem hcE he hce]

theorem le_ker_of_le_commutator (hperf : E₀ ≤ ⁅E₀, stabIn X a⁆) {A : Type*} [Group A]
    (f : K →* A) (hf : ∀ x y : K, Commute (f x) (f y)) : E ≤ f.ker := by
  refine (h.le_commutator_of_le_commutator hperf).trans (commutator_le.mpr fun e _ x _ => ?_)
  rw [MonoidHom.mem_ker, map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
  exact hf e x

theorem le_of_sup_eq_top (hperf : E₀ ≤ ⁅E₀, stabIn X a⁆) {D N : Subgroup K} [D.Normal]
    (hN : N ≤ π.ker) (hND : N ⊔ D = ⊤) : E ≤ D := by
  have hdec : ∀ x : K, ∃ n ∈ N, ∃ d ∈ D, x = n * d := by
    intro x
    have hx : x ∈ ((N ⊔ D : Subgroup K) : Set K) := by rw [hND]; exact mem_top x
    rw [mul_normal] at hx
    obtain ⟨n, hn, d, hd, rfl⟩ := hx
    exact ⟨n, hn, d, hd, rfl⟩
  have hmk : ∀ x : K, ∃ n ∈ N, (QuotientGroup.mk' D) x = (QuotientGroup.mk' D) n := by
    intro x
    obtain ⟨n, hn, d, hd, rfl⟩ := hdec x
    refine ⟨n, hn, ?_⟩
    rw [map_mul, show (QuotientGroup.mk' D) d = 1 from (QuotientGroup.eq_one_iff d).mpr hd,
      mul_one]
  have hle := h.le_ker_of_le_commutator hperf (QuotientGroup.mk' D) fun x y => by
    obtain ⟨n, hn, hx⟩ := hmk x
    obtain ⟨n', hn', hy⟩ := hmk y
    rw [hx, hy]
    exact Commute.map ((mem_center_iff.mp (h.ker_le_center (hN hn'))) n) _
  rwa [QuotientGroup.ker_mk'] at hle

theorem ker_eq_bot_of_hom_of_le_commutator (hperf : E₀ ≤ ⁅E₀, stabIn X a⁆) {G : Type*}
    [Group G] (σ : G →* K) (hinj : Function.Injective (π.comp σ))
    (hX : X ≤ (π.comp σ).range) : π.ker = ⊥ := by
  have hX' : X ≤ σ.range.map π := by rwa [MonoidHom.map_range]
  have := h.normal_of_le_map hX'
  refine h.ker_eq_bot_of_hom σ hinj hX (p := a) ⟨1, by rw [map_one]; rfl⟩ ?_
  rw [h.Ept_self]
  exact h.le_of_sup_eq_top hperf le_rfl (h.ker_sup_eq_top_of_le_map hX')

theorem ker_eq_bot_of_hom_of_odd [Finite K] (h2 : IsPGroup 2 E) (hodd : Odd (Nat.card π.ker))
    {G : Type*} [Group G] (σ : G →* K) (hinj : Function.Injective (π.comp σ))
    (hX : X ≤ (π.comp σ).range) : π.ker = ⊥ := by
  have hX' : X ≤ σ.range.map π := by rwa [MonoidHom.map_range]
  have := h.normal_of_le_map hX'
  refine h.ker_eq_bot_of_hom σ hinj hX (p := a) ⟨1, by rw [map_one]; rfl⟩ ?_
  rw [h.Ept_self]
  have hsurj : Function.Surjective ((QuotientGroup.mk' σ.range).comp π.ker.subtype) := by
    intro q
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective σ.range q
    obtain ⟨y, hy, hz⟩ := h.exists_mem_inv_mul_mem_ker hX' x
    refine ⟨⟨y⁻¹ * x, hz⟩, ?_⟩
    rw [MonoidHom.comp_apply, Subgroup.coe_subtype, map_mul, map_inv,
      show (QuotientGroup.mk' σ.range) y = 1 from (QuotientGroup.eq_one_iff y).mpr hy, inv_one,
      one_mul]
  have hdvd := Subgroup.card_dvd_of_surjective hsurj
  have hcop : Nat.Coprime 2 (Nat.card (K ⧸ σ.range)) :=
    (Nat.coprime_two_left.mpr hodd).coprime_dvd_right hdvd
  intro e he
  obtain ⟨k, hk⟩ := h2 ⟨e, he⟩
  have hk' : e ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
  rw [← QuotientGroup.ker_mk' σ.range, MonoidHom.mem_ker]
  have h1 : orderOf ((QuotientGroup.mk' σ.range) e) ∣ 2 ^ k :=
    orderOf_dvd_of_pow_eq_one (by rw [← map_pow, hk', map_one])
  have h2' : orderOf ((QuotientGroup.mk' σ.range) e) ∣ Nat.card (K ⧸ σ.range) :=
    orderOf_dvd_natCard _
  have h3 : orderOf ((QuotientGroup.mk' σ.range) e) = 1 :=
    Nat.dvd_one.mp ((Nat.Coprime.pow_left k hcop).gcd_eq_one ▸ Nat.dvd_gcd h1 h2')
  exact orderOf_eq_one_iff.mp h3

theorem odd_card_ker [Finite K] (hperf : E₀ ≤ ⁅E₀, stabIn X a⁆) {U : Subgroup K}
    (hU : U ⊓ π.ker = ⊥) {m : ℕ} (hm : Odd m) (hX : Nat.card X = Nat.card U * m) :
    Odd (Nat.card π.ker) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_contra hev
  let P : Sylow 2 π.ker := default
  set N : Subgroup K := (P : Subgroup π.ker).map π.ker.subtype with hNdef
  have hNZ : N ≤ π.ker := by
    rintro _ ⟨z, -, rfl⟩
    exact z.2
  have hcen : ∀ n ∈ N, n ∈ center K := fun n hn => h.ker_le_center (hNZ hn)
  have hNnormal : N.Normal := ⟨fun n hn g => by
    rw [(mem_center_iff.mp (hcen n hn)) g, mul_inv_cancel_right]
    exact hn⟩
  have : IsMulCommutative N :=
    ⟨⟨fun x y => Subtype.ext ((mem_center_iff.mp (hcen _ y.2)) x)⟩⟩
  have hcardN : Nat.card N = Nat.card P := card_map_of_injective π.ker.subtype_injective
  have hNU : N ⊓ U = ⊥ := by
    rw [eq_bot_iff, ← hU, inf_comm]
    exact inf_le_inf_left U hNZ
  have hcardK : Nat.card K = Nat.card π.ker * Nat.card X := by
    rw [card_eq_card_quotient_mul_card_subgroup π.ker,
      Nat.card_congr (QuotientGroup.quotientKerEquivRange π).toEquiv, h.range_eq, mul_comm]
  have hcardH := card_sup_of_normal_of_inf_eq_bot hNU
  have hPidx : Nat.card P * (P : Subgroup π.ker).index = Nat.card π.ker := card_mul_index _
  have hPodd : ¬ 2 ∣ (P : Subgroup π.ker).index := P.not_dvd_index
  have hidx : (N ⊔ U).index = (P : Subgroup π.ker).index * m := by
    have h1 := (N ⊔ U).index_mul_card
    rw [hcardH, hcardK, hX, hcardN, ← hPidx] at h1
    have hP0 : 0 < Nat.card P := Nat.card_pos
    have hU0 : 0 < Nat.card U := Nat.card_pos
    have h2 : (N ⊔ U).index * (Nat.card P * Nat.card U) =
        ((P : Subgroup π.ker).index * m) * (Nat.card P * Nat.card U) := by
      rw [h1]
      ring
    exact Nat.eq_of_mul_eq_mul_right (Nat.mul_pos hP0 hU0) h2
  have hcop : Nat.Coprime (N ⊔ U).index (Nat.card N) := by
    obtain ⟨e, he⟩ := (IsPGroup.iff_card.mp P.isPGroup')
    rw [hcardN, he]
    refine Nat.Coprime.pow_right _ (Nat.Coprime.symm ((Nat.coprime_two_left).mpr ?_))
    rw [hidx]
    exact (Nat.odd_iff.mpr (Nat.two_dvd_ne_zero.mp hPodd)).mul hm
  obtain ⟨D, -, hND, hNDtop⟩ :=
    CFSG.GroupTheory.abelian_normal_coprime_index_complement_lifting N (N ⊔ U) U hcop hNU rfl
  have : D.Normal := ⟨fun d hd g => by
    have hg : g ∈ ((N ⊔ D : Subgroup K) : Set K) := by rw [hNDtop]; exact mem_top g
    rw [normal_mul] at hg
    obtain ⟨n, hn, d', hd', rfl⟩ := hg
    have e : n * d' * d * (n * d')⁻¹ = d' * d * d'⁻¹ := by
      rw [show n * d' * d * (n * d')⁻¹ = n * (d' * d * d'⁻¹) * n⁻¹ by group,
        ← (mem_center_iff.mp (hcen n hn)) _, mul_inv_cancel_right]
    rw [e]
    exact mul_mem (mul_mem hd' hd) (inv_mem hd')⟩
  have hED := h.le_of_sup_eq_top hperf hNZ hNDtop
  have hDtop : D = ⊤ := h.eq_top_of_normal (k := 1) (by rwa [Eb_one])
  rw [hDtop, inf_top_eq] at hND
  have hN1 : Nat.card N = 1 := by rw [hND, card_bot]
  rw [hcardN] at hN1
  rw [hN1, one_mul] at hPidx
  exact hev (hPidx ▸ Nat.odd_iff.mpr (Nat.two_dvd_ne_zero.mp hPodd))

end CEHyp

theorem card_iSup_le_prod [Finite K] : ∀ {r : ℕ} (R : Fin r → Subgroup K),
    (∀ i j : Fin r, i < j → R j ≤ normalizer (R i : Set K)) →
      Nat.card ↥(⨆ i, R i) ≤ ∏ i, Nat.card (R i)
  | 0, R, _ => by simp
  | r + 1, R, hR => by
    set T : Subgroup K := ⨆ i : Fin r, R i.succ
    have hsup : (⨆ i, R i) = R 0 ⊔ T := by
      apply le_antisymm
      · refine iSup_le fun i => ?_
        refine Fin.cases ?_ (fun j => ?_) i
        · exact le_sup_left
        · exact le_sup_of_le_right (le_iSup (fun j : Fin r => R j.succ) j)
      · exact sup_le (le_iSup R 0) (iSup_le fun j => le_iSup R j.succ)
    have hT : T ≤ normalizer (R 0 : Set K) := iSup_le fun j => hR 0 j.succ (Fin.succ_pos j)
    have hIH := card_iSup_le_prod (fun j : Fin r => R j.succ) fun i j hij =>
      hR _ _ (Fin.succ_lt_succ_iff.mpr hij)
    rw [hsup, Fin.prod_univ_succ]
    have hcoe : ((R 0 ⊔ T : Subgroup K) : Set K) = (R 0 : Set K) * (T : Set K) :=
      coe_mul_of_right_le_normalizer_left (R 0) T hT
    calc Nat.card ↥(R 0 ⊔ T) = Nat.card ↑((R 0 : Set K) * (T : Set K)) := by rw [← hcoe]; rfl
      _ ≤ Nat.card (R 0 : Set K) * Nat.card (T : Set K) := Set.natCard_mul_le
      _ = Nat.card (R 0) * Nat.card T := rfl
      _ ≤ Nat.card (R 0) * ∏ i : Fin r, Nat.card (R i.succ) := Nat.mul_le_mul_left _ hIH

theorem inf_ker_eq_bot_of_card_le [Finite K] {G : Type*} [Group G] (f : K →* G)
    {U : Subgroup K} (hU : Nat.card U ≤ Nat.card (U.map f)) : U ⊓ f.ker = ⊥ := by
  have h1 := card_eq_card_quotient_mul_card_subgroup (f.comp U.subtype).ker
  rw [Nat.card_congr (QuotientGroup.quotientKerEquivRange (f.comp U.subtype)).toEquiv,
    MonoidHom.range_comp, range_subtype] at h1
  have hpos : 0 < Nat.card U := Nat.card_pos
  have hk : Nat.card (f.comp U.subtype).ker = 1 := by
    have hk0 : 0 < Nat.card (f.comp U.subtype).ker := Nat.card_pos
    by_contra hne
    have : 2 ≤ Nat.card (f.comp U.subtype).ker := by omega
    have := Nat.mul_le_mul_left (Nat.card (U.map f)) this
    omega
  rw [card_eq_one] at hk
  rw [eq_bot_iff]
  intro x hx
  obtain ⟨hxU, hxk⟩ := mem_inf.mp hx
  have hmem : (⟨x, hxU⟩ : U) ∈ (f.comp U.subtype).ker := by
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply]
    exact hxk
  rw [hk, mem_bot] at hmem
  rw [mem_bot]
  exact congrArg Subtype.val hmem

section Map

variable {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]

@[expose] def ceConj (L : V ≃ₗ[ZMod 2] W) : (V ≃ₗ[ZMod 2] V) ≃* (W ≃ₗ[ZMod 2] W) where
  toFun g := L.symm.trans (g.trans L)
  invFun g := L.trans (g.trans L.symm)
  left_inv g := by
    ext
    simp
  right_inv g := by
    ext
    simp
  map_mul' g g' := by
    ext
    simp

theorem ceConj_apply (L : V ≃ₗ[ZMod 2] W) (g : V ≃ₗ[ZMod 2] V) (w : W) :
    ceConj L g w = L (g (L.symm w)) :=
  rfl

theorem ceConj_apply_apply (L : V ≃ₗ[ZMod 2] W) (g : V ≃ₗ[ZMod 2] V) (v : V) :
    ceConj L g (L v) = L (g v) := by
  rw [ceConj_apply, LinearEquiv.symm_apply_apply]

theorem ker_comp_mulEquiv (π : K →* (V ≃ₗ[ZMod 2] V))
    (Φ : (V ≃ₗ[ZMod 2] V) ≃* (W ≃ₗ[ZMod 2] W)) : (Φ.toMonoidHom.comp π).ker = π.ker := by
  ext x
  rw [MonoidHom.mem_ker, MonoidHom.mem_ker, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
    MulEquiv.map_eq_one_iff]

variable {π : K →* (V ≃ₗ[ZMod 2] V)} {E : Subgroup K} {a : V}
  {X E₀ : Subgroup (V ≃ₗ[ZMod 2] V)}

theorem CEHyp.map (h : CEHyp π E a X E₀) (L : V ≃ₗ[ZMod 2] W)
    (Φ : (V ≃ₗ[ZMod 2] V) ≃* (W ≃ₗ[ZMod 2] W)) (hΦ : ∀ g v, Φ g (L v) = L (g v)) :
    CEHyp (Φ.toMonoidHom.comp π) E (L a) (X.map Φ.toMonoidHom) (E₀.map Φ.toMonoidHom) where
  range_eq := by rw [MonoidHom.range_comp, h.range_eq]
  ker_le_center := by rw [ker_comp_mulEquiv]; exact h.ker_le_center
  inf_ker_eq_bot := by rw [ker_comp_mulEquiv]; exact h.inf_ker_eq_bot
  map_eq := by rw [← map_map, h.map_eq]
  closure_conj_eq_top := h.closure_conj_eq_top
  le_normalizer x hx := h.le_normalizer x (L.injective (by
    rw [← hΦ]
    exact hx))

end Map

end CFSG.LargeExtraspecial.S4
