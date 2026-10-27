module

public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Inputs2311
public import CFSG.LieType.SeitzGeneration.Lift
import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Lemma119
import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Lemma129b

public section

namespace CFSG.LocalAnalysis.GLTheoremB.MovingAround.Inputs2311c

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.LocalAnalysis.GLTheoremB.MovingAround
open CFSG.HardMathSupport.Solomon.LocalBalance (barOf barAut)
open CFSG.Yardstones.Md0ec50421ce4 (IsChevSimple)
open CFSG.LieType.SeitzGeneration (Cat CentralPrimeFree PlaneGen planeClosure SeitzPlanes)

section Uni

variable {S : Type*} [Group S]

@[expose] def uniPlaneClosure (r : ℕ) (E : Subgroup (MulAut S)) : Subgroup S :=
  Subgroup.closure {s : S | ∃ e ∈ E, e ≠ 1 ∧ e s = s ∧ ∃ n : ℕ, s ^ (r ^ n) = 1}

@[expose] def UniPlaneGen (r : ℕ) (E : Subgroup (MulAut S)) : Prop :=
  uniPlaneClosure r E = ⊤

theorem mem_uniPlaneClosure {r : ℕ} {E : Subgroup (MulAut S)} {e : MulAut S} (he : e ∈ E) (he1 : e ≠ 1)
    {s : S} (hs : e s = s) {n : ℕ} (hn : s ^ (r ^ n) = 1) : s ∈ uniPlaneClosure r E :=
  Subgroup.subset_closure ⟨e, he, he1, hs, n, hn⟩

end Uni

@[expose] def UniSeitzPlanes
    (S : ∀ d : TauCeti.ValidLieTypeIndex, ℕ → Subgroup (MulAut (Cat d)) → Prop) : Prop :=
  ∀ (d : TauCeti.ValidLieTypeIndex) (p : ℕ), p.Prime → p ≠ 2 → p ≠ d.1.characteristic →
    ¬ CFSG.AGLEmbeddingD2.IsD2SeitzException p d.1 → ∀ E : Subgroup (MulAut (Cat d)), IsElemAbelian p E →
      Nat.card E = p ^ 2 → S d p E → UniPlaneGen d.1.characteristic E

theorem UniSeitzPlanes.mono {S S' : ∀ d : TauCeti.ValidLieTypeIndex, ℕ →
    Subgroup (MulAut (Cat d)) → Prop} (h : ∀ d p E, S d p E → S' d p E) (hS' : UniSeitzPlanes S') :
    UniSeitzPlanes S :=
  fun d p hp hp2 hpd hex E hE hc hs => hS' d p hp hp2 hpd hex E hE hc (h d p E hs)

theorem UniSeitzPlanes.of_cover {S S₁ S₂ : ∀ d : TauCeti.ValidLieTypeIndex, ℕ →
    Subgroup (MulAut (Cat d)) → Prop}
    (hcov : ∀ d p, p.Prime → p ≠ 2 → ∀ E, S d p E → S₁ d p E ∨ S₂ d p E)
    (h₁ : UniSeitzPlanes S₁) (h₂ : UniSeitzPlanes S₂) : UniSeitzPlanes S := by
  intro d p hp hp2 hpd hex E hE hc hs
  rcases hcov d p hp hp2 E hs with h | h
  · exact h₁ d p hp hp2 hpd hex E hE hc h
  · exact h₂ d p hp hp2 hpd hex E hE hc h

@[expose] def OddCpf (d : TauCeti.ValidLieTypeIndex) (p : ℕ) (_ : Subgroup (MulAut (Cat d))) : Prop :=
  d.1.characteristic ≠ 2 ∧ CentralPrimeFree p d.1

theorem characteristic_eq_two_of_d2Exc {p : ℕ} {d : TauCeti.LieTypeIndex}
    (h : CFSG.AGLEmbeddingD2.IsD2SeitzException p d) : d.characteristic = 2 := by
  rcases h with ⟨-, ⟨q, hq2, -, rfl⟩ | ⟨q, hq2, -, rfl⟩ | ⟨q, hq2, -, rfl⟩ |
      ⟨q, hq2, -, rfl | rfl⟩ | rfl⟩ | ⟨-, rfl | rfl⟩ <;> simp_all

section LiftQ

variable {Y : Type*} [Group Y] [Finite Y]

theorem exists_lift_fixed {q : ℕ} (hcop : Nat.Coprime (Nat.card (Subgroup.center Y)) q) (φ : MulAut Y)
    (y₀ : Y) {n : ℕ} (hu : (QuotientGroup.mk y₀ : Y ⧸ Subgroup.center Y) ^ (q ^ n) = 1)
    (hφ : (QuotientGroup.mk (φ y₀) : Y ⧸ Subgroup.center Y) = QuotientGroup.mk y₀) :
    ∃ y : Y, (QuotientGroup.mk y : Y ⧸ Subgroup.center Y) = QuotientGroup.mk y₀ ∧ y ^ (q ^ n) = 1 ∧
      φ y = y := by
  set N := Nat.card (Subgroup.center Y) with hN
  set u : Y ⧸ Subgroup.center Y := QuotientGroup.mk y₀ with hudef
  have hcopu : N.Coprime (orderOf u) :=
    Nat.Coprime.coprime_dvd_right (orderOf_dvd_of_pow_eq_one hu) (Nat.Coprime.pow_right n hcop)
  obtain ⟨m, hm⟩ := exists_pow_eq_self_of_coprime hcopu
  have hcN : ∀ c ∈ Subgroup.center Y, c ^ N = 1 := by
    intro c hc
    have h : (⟨c, hc⟩ : ↥(Subgroup.center Y)) ^ N = 1 := pow_card_eq_one'
    exact congrArg Subtype.val h
  have hc0 : y₀ ^ (q ^ n) ∈ Subgroup.center Y := by
    rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_pow]
    exact hu
  have hc1 : y₀⁻¹ * φ y₀ ∈ Subgroup.center Y := QuotientGroup.eq.1 hφ.symm
  refine ⟨(y₀ ^ N) ^ m, ?_, ?_, ?_⟩
  · rw [QuotientGroup.mk_pow, QuotientGroup.mk_pow]
    exact hm
  · calc ((y₀ ^ N) ^ m) ^ (q ^ n) = ((y₀ ^ (q ^ n)) ^ N) ^ m := by
          rw [← pow_mul, ← pow_mul, ← pow_mul, ← pow_mul]
          congr 1
          ring
      _ = 1 := by rw [hcN _ hc0, one_pow]
  · have hφy : φ y₀ = y₀ * (y₀⁻¹ * φ y₀) := by group
    have hcomm : Commute y₀ (y₀⁻¹ * φ y₀) :=
      ((Subgroup.mem_center_iff.1 hc1) y₀)
    rw [map_pow, map_pow, hφy, hcomm.mul_pow, hcN _ hc1, mul_one]

theorem eq_top_of_sup_center (hperf : commutator Y = ⊤) {H : Subgroup Y}
    (h : H ⊔ Subgroup.center Y = ⊤) : H = ⊤ := by
  rw [eq_top_iff, ← hperf, commutator_def, Subgroup.commutator_le]
  intro g₁ _ g₂ _
  have hmem : ∀ g : Y, ∃ x ∈ H, ∃ z ∈ Subgroup.center Y, x * z = g := by
    intro g
    have hg : g ∈ ((H ⊔ Subgroup.center Y : Subgroup Y) : Set Y) := by rw [h]; exact Subgroup.mem_top g
    rw [Subgroup.mul_normal] at hg
    obtain ⟨x, hx, z, hz, hxz⟩ := Set.mem_mul.1 hg
    exact ⟨x, hx, z, hz, hxz⟩
  obtain ⟨x₁, hx₁, z₁, hz₁, rfl⟩ := hmem g₁
  obtain ⟨x₂, hx₂, z₂, hz₂, rfl⟩ := hmem g₂
  rw [commutatorElement_def, commutator_mul_central hz₁ hz₂]
  exact H.mul_mem (H.mul_mem (H.mul_mem hx₁ hx₂) (H.inv_mem hx₁)) (H.inv_mem hx₂)

theorem coprime_card_center {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hqp : q ≠ p)
    (hO : GLAPPrimeCore p Y = ⊥) : Nat.Coprime (Nat.card (Subgroup.center Y)) q := by
  haveI : Fact q.Prime := ⟨hq⟩
  rw [Nat.coprime_comm, Nat.Prime.coprime_iff_not_dvd hq]
  intro hdvd
  obtain ⟨c, hc⟩ := exists_prime_orderOf_dvd_card' q hdvd
  have hcen : ∀ k : ℤ, ((c : Y) ^ k) ∈ Subgroup.center Y := fun k => Subgroup.zpow_mem _ c.2 k
  haveI hnorm : (Subgroup.zpowers (c : Y)).Normal := by
    refine ⟨fun x hx g => ?_⟩
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hx
    have h1 := (Subgroup.mem_center_iff.1 (hcen k)) g
    rw [h1, mul_inv_cancel_right]
    exact Subgroup.zpow_mem_zpowers _ k
  have hord : orderOf (c : Y) = q := by rw [Subgroup.orderOf_coe]; exact hc
  have hcard : Nat.card (Subgroup.zpowers (c : Y)) = q := by rw [Nat.card_zpowers, hord]
  have hle : Subgroup.zpowers (c : Y) ≤ GLAPPrimeCore p Y := by
    show _ ≤ CFSG.pPrimeCore p Y
    refine le_sSup ⟨hnorm, ?_⟩
    rw [hcard]
    exact (Nat.coprime_primes hp hq).mpr (Ne.symm hqp)
  rw [hO] at hle
  have h1 : (c : Y) = 1 := (Subgroup.zpowers_eq_bot).1 (le_bot_iff.1 hle)
  rw [h1, orderOf_one] at hord
  exact hq.one_lt.ne hord

end LiftQ

section Transfer

variable {G : Type} [Group G] [Finite G]

@[expose] noncomputable def catAct {p : ℕ} {K : Subgroup G} {d : TauCeti.ValidLieTypeIndex}
    (θ : barOf p K ⧸ Subgroup.center (barOf p K) ≃* Cat d) :
    ↥(Subgroup.normalizer (K : Set G)) →* MulAut (Cat d) :=
  (MulAut.congr θ).toMonoidHom.comp ((quotientCenterAut' (barOf p K)).comp (barAut p K))

theorem catAct_apply {p : ℕ} {K : Subgroup G} {d : TauCeti.ValidLieTypeIndex}
    (θ : barOf p K ⧸ Subgroup.center (barOf p K) ≃* Cat d) (x : ↥(Subgroup.normalizer (K : Set G)))
    (y : barOf p K) :
    catAct θ x (θ (QuotientGroup.mk y)) = θ (QuotientGroup.mk (barAut p K x y)) := by
  simp [catAct, MulAut.congr, quotientCenterAut']

theorem le_iSup_of_uniPlaneGen {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hqp : q ≠ p)
    {a : G} {K A0 D : Subgroup G} (hK : GLAPComponent p (Cg a) K) {d : TauCeti.ValidLieTypeIndex}
    (θ : barOf p K ⧸ Subgroup.center (barOf p K) ≃* Cat d)
    (hA0C : A0 ≤ Cg a) (hN : A0 ≤ Subgroup.normalizer (K : Set G)) (hDA : D ≤ A0)
    (hgen : UniPlaneGen q ((D.subgroupOf (Subgroup.normalizer (K : Set G))).map (catAct θ))) :
    barX p (Cg a) K ≤ ⨆ (z : ↥(Cg a)) (_ : (z : G) ∈ A0) (_ : z ≠ 1),
      CFSG.GH74.GLS.oPrimeResidualOf q (barX p (Cg a) K ⊓ Subgroup.centralizer
        ({QuotientGroup.mk' (GLAPPrimeCore p ↥(Cg a)) z} : Set (↥(Cg a) ⧸ GLAPPrimeCore p ↥(Cg a)))) := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  have hYq : CFSG.Open.IsQuasisimple (barOf p K) := l119_isQuasisimple_barOf hp hK
  have hperf : commutator (barOf p K) = ⊤ := hYq.1
  have hO : GLAPPrimeCore p (barOf p K) = ⊥ := glaPPrimeCore_quotient_eq_bot hp
  have hcop : Nat.Coprime (Nat.card (Subgroup.center (barOf p K))) q := coprime_card_center hp hq hqp hO
  set N : Subgroup G := Subgroup.normalizer (K : Set G) with hNdef
  set Eb : Subgroup (MulAut (Cat d)) := (D.subgroupOf N).map (catAct θ) with hEb
  set L : Set (barOf p K) := {y | ∃ x : ↥N, (x : G) ∈ D ∧ (x : G) ≠ 1 ∧ barAut p K x y = y ∧
    ∃ n : ℕ, y ^ (q ^ n) = 1} with hLdef
  have hmapL : (Subgroup.closure L).map (QuotientGroup.mk' (Subgroup.center (barOf p K))) = ⊤ := by
    set M := (Subgroup.closure L).map (QuotientGroup.mk' (Subgroup.center (barOf p K))) with hM
    have hgenM : uniPlaneClosure q Eb ≤ M.comap θ.symm.toMonoidHom := by
      rw [uniPlaneClosure, Subgroup.closure_le]
      rintro s ⟨e, he, he1, hes, n, hn⟩
      obtain ⟨x, hxD', rfl⟩ := Subgroup.mem_map.1 he
      have hxD : (x : G) ∈ D := Subgroup.mem_subgroupOf.1 hxD'
      have hx1 : (x : G) ≠ 1 := by
        intro h
        apply he1
        rw [show x = 1 from Subtype.ext h, map_one]
      obtain ⟨y₀, hy₀⟩ := QuotientGroup.mk_surjective (θ.symm s)
      have hs : s = θ (QuotientGroup.mk y₀) := by rw [hy₀, MulEquiv.apply_symm_apply]
      have hu : (QuotientGroup.mk y₀ : barOf p K ⧸ Subgroup.center (barOf p K)) ^ (q ^ n) = 1 := by
        apply θ.injective
        rw [map_pow, ← hs, hn, map_one]
      have hφ : (QuotientGroup.mk (barAut p K x y₀) : barOf p K ⧸ Subgroup.center (barOf p K)) =
          QuotientGroup.mk y₀ := by
        apply θ.injective
        rw [← catAct_apply, ← hs]
        exact hes
      obtain ⟨y, hy, hyn, hyx⟩ := exists_lift_fixed hcop (barAut p K x) y₀ hu hφ
      have hyL : y ∈ Subgroup.closure L := Subgroup.subset_closure ⟨x, hxD, hx1, hyx, n, hyn⟩
      show θ.symm s ∈ M
      rw [← hy₀, ← hy]
      exact Subgroup.mem_map_of_mem _ hyL
    rw [eq_top_iff]
    intro u _
    have h1 : θ u ∈ M.comap θ.symm.toMonoidHom := by
      apply hgenM
      rw [hgen]
      exact Subgroup.mem_top _
    rw [Subgroup.mem_comap] at h1
    simpa using h1
  have hLtop : Subgroup.closure L = ⊤ := by
    refine eq_top_of_sup_center hperf ?_
    have h1 := Subgroup.comap_map_eq (QuotientGroup.mk' (Subgroup.center (barOf p K))) (Subgroup.closure L)
    rw [hmapL, Subgroup.comap_top, QuotientGroup.ker_mk'] at h1
    exact h1.symm
  set f := quotEquivBarX hp hK.1 hK.2.1 with hf
  set F : barOf p K →* ↥(Cg a) ⧸ GLAPPrimeCore p ↥(Cg a) :=
    (barX p (Cg a) K).subtype.comp f.toMonoidHom with hF
  have hFL : (Subgroup.closure L).map F ≤ ⨆ (z : ↥(Cg a)) (_ : (z : G) ∈ A0) (_ : z ≠ 1),
      CFSG.GH74.GLS.oPrimeResidualOf q (barX p (Cg a) K ⊓ Subgroup.centralizer
        ({QuotientGroup.mk' (GLAPPrimeCore p ↥(Cg a)) z} : Set (↥(Cg a) ⧸ GLAPPrimeCore p ↥(Cg a)))) := by
    rw [Subgroup.map_le_iff_le_comap, Subgroup.closure_le]
    rintro y ⟨x, hxD, hx1, hyx, n, hyn⟩
    rw [SetLike.mem_coe, Subgroup.mem_comap]
    set z : ↥(Cg a) := ⟨(x : G), hA0C (hDA hxD)⟩ with hz
    have hz1 : z ≠ 1 := fun h => hx1 (congrArg Subtype.val h)
    have hconj := Lemma129b.quotEquivBarX_barAut hp hK (hA0C (hDA hxD)) (hN (hDA hxD)) y
    have hxx : (⟨(x : G), hN (hDA hxD)⟩ : ↥N) = x := Subtype.ext rfl
    rw [hxx, hyx] at hconj
    have hFy : F y = ((f y : ↥(barX p (Cg a) K)) : ↥(Cg a) ⧸ GLAPPrimeCore p ↥(Cg a)) := rfl
    have hmemK : F y ∈ barX p (Cg a) K := (f y).2
    have hmemC : F y ∈ Subgroup.centralizer
        ({QuotientGroup.mk' (GLAPPrimeCore p ↥(Cg a)) z} : Set (↥(Cg a) ⧸ GLAPPrimeCore p ↥(Cg a))) := by
      rw [Subgroup.mem_centralizer_iff]
      intro g hg
      rw [Set.mem_singleton_iff] at hg
      rw [hg, hFy]
      calc QuotientGroup.mk' (GLAPPrimeCore p ↥(Cg a)) z * ((f y : ↥(barX p (Cg a) K)) : _)
          = (QuotientGroup.mk' (GLAPPrimeCore p ↥(Cg a)) z * ((f y : ↥(barX p (Cg a) K)) : _) *
              (QuotientGroup.mk' (GLAPPrimeCore p ↥(Cg a)) z)⁻¹) *
              QuotientGroup.mk' (GLAPPrimeCore p ↥(Cg a)) z := by group
        _ = ((f y : ↥(barX p (Cg a) K)) : _) * QuotientGroup.mk' (GLAPPrimeCore p ↥(Cg a)) z := by
              rw [← hconj]
    have hpow : F y ^ (q ^ n) = 1 := by rw [← map_pow, hyn, map_one]
    have hmem : F y ∈ CFSG.GH74.GLS.oPrimeResidualOf q (barX p (Cg a) K ⊓ Subgroup.centralizer
        ({QuotientGroup.mk' (GLAPPrimeCore p ↥(Cg a)) z} : Set (↥(Cg a) ⧸ GLAPPrimeCore p ↥(Cg a)))) := by
      refine ⟨⟨F y, Subgroup.mem_inf.2 ⟨hmemK, hmemC⟩⟩, Subgroup.subset_closure ⟨n, ?_⟩, rfl⟩
      apply Subtype.ext
      rw [SubgroupClass.coe_pow, OneMemClass.coe_one]
      exact hpow
    exact Subgroup.mem_iSup_of_mem z (Subgroup.mem_iSup_of_mem (hDA hxD) (Subgroup.mem_iSup_of_mem hz1 hmem))
  intro w hw
  have hw' : w = F (f.symm ⟨w, hw⟩) := by rw [hF]; simp
  rw [hw']
  apply hFL
  rw [hLtop]
  exact Subgroup.mem_map_of_mem _ (Subgroup.mem_top _)

theorem catAct_plane {p : ℕ} (hp : p.Prime) {a : G} {K A0 D : Subgroup G} (hK : GLAPComponent p (Cg a) K)
    {d : TauCeti.ValidLieTypeIndex} (θ : barOf p K ⧸ Subgroup.center (barOf p K) ≃* Cat d)
    (hN : A0 ≤ Subgroup.normalizer (K : Set G)) (hF : ∀ x ∈ A0, x ∈ centBar p ⊤ K → x = 1)
    (hDA : D ≤ A0) (hDel : IsElemAbelian p D) (hDc : Nat.card D = p ^ 2) :
    IsElemAbelian p ((D.subgroupOf (Subgroup.normalizer (K : Set G))).map (catAct θ)) ∧
      Nat.card ((D.subgroupOf (Subgroup.normalizer (K : Set G))).map (catAct θ)) = p ^ 2 := by
  have hperf : commutator (barOf p K) = ⊤ := (l119_isQuasisimple_barOf hp hK).1
  set N : Subgroup G := Subgroup.normalizer (K : Set G) with hNdef
  set D' : Subgroup ↥N := D.subgroupOf N with hD'
  have hinj : ∀ x : ↥N, (x : G) ∈ D → catAct θ x = 1 → (x : G) = 1 := by
    intro x hxD hx
    have h1 : quotientCenterAut' (barOf p K) (barAut p K x) = 1 := by
      have h2 : (MulAut.congr θ) (quotientCenterAut' (barOf p K) (barAut p K x)) = 1 := hx
      rwa [MulEquiv.map_eq_one_iff] at h2
    have h2 : barAut p K x = 1 := quotientCenterAut'_injective hperf (by rw [h1, map_one])
    refine hF _ (hDA hxD) (Subgroup.mem_inf.2 ⟨?_, Subgroup.mem_top _⟩)
    exact ⟨x, MonoidHom.mem_ker.2 h2, rfl⟩
  have hinjOn : Set.InjOn (catAct θ) (D' : Set ↥N) := by
    intro x hx y hy hxy
    have h1 : catAct θ (x * y⁻¹) = 1 := by rw [map_mul, map_inv, hxy, mul_inv_cancel]
    have hxyD : ((x * y⁻¹ : ↥N) : G) ∈ D :=
      D.mul_mem (Subgroup.mem_subgroupOf.1 hx) (D.inv_mem (Subgroup.mem_subgroupOf.1 hy))
    exact mul_inv_eq_one.1 (Subtype.ext (hinj _ hxyD h1))
  refine ⟨CFSG.Open.IsElemAbelian.map (l119_isElemAbelian_subgroupOf hDel N) _, ?_⟩
  have h1 : Nat.card (D'.map (catAct θ)) = Nat.card ((catAct θ) '' (D' : Set ↥N)) := by
    rw [← Subgroup.coe_map]
    rfl
  rw [h1, Nat.card_image_of_injOn hinjOn]
  have h2 : Nat.card (D' : Set ↥N) = Nat.card D' := rfl
  rw [h2, hD', Nat.card_congr (Subgroup.subgroupOfEquivOfLe (hDA.trans hN)).toEquiv, hDc]

theorem le_iSup_of_uni {S : ∀ d : TauCeti.ValidLieTypeIndex, ℕ → Subgroup (MulAut (Cat d)) → Prop}
    (hU : UniSeitzPlanes S) {p q : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hq : q.Prime) (hqp : q ≠ p)
    {a : G} {K A0 : Subgroup G} (hK : GLAPComponent p (Cg a) K) {d : TauCeti.ValidLieTypeIndex}
    (hdq : d.1.characteristic = q) (hex : ¬ CFSG.AGLEmbeddingD2.IsD2SeitzException p d.1)
    (hS : ∀ E : Subgroup (MulAut (Cat d)), S d p E)
    (θ : barOf p K ⧸ Subgroup.center (barOf p K) ≃* Cat d)
    (hA0C : A0 ≤ Cg a) (hA0r : 2 ≤ CFSG.Open.pRank p A0)
    (hN : A0 ≤ Subgroup.normalizer (K : Set G)) (hF : ∀ x ∈ A0, x ∈ centBar p ⊤ K → x = 1) :
    barX p (Cg a) K ≤ ⨆ (z : ↥(Cg a)) (_ : (z : G) ∈ A0) (_ : z ≠ 1),
      CFSG.GH74.GLS.oPrimeResidualOf q (barX p (Cg a) K ⊓ Subgroup.centralizer
        ({QuotientGroup.mk' (GLAPPrimeCore p ↥(Cg a)) z} : Set (↥(Cg a) ⧸ GLAPPrimeCore p ↥(Cg a)))) := by
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨D, hDA, hDel, hDc⟩ := CFSG.SectionRank.exists_isElemAbelian_card_of_le_pRank hA0r
  obtain ⟨hEel, hEc⟩ := catAct_plane hp hK θ hN hF hDA hDel hDc
  have hgen := hU d p hp hp2 (by rw [hdq]; exact Ne.symm hqp) hex _ hEel hEc (hS _)
  rw [hdq] at hgen
  exact le_iSup_of_uniPlaneGen hp hq hqp hK θ hA0C hN hDA hgen

end Transfer

@[expose] def Input23_11Thm4Rest : Prop :=
  ∀ {G : Type} [Group G] [Finite G] {p q : ℕ}, p.Prime → p ≠ 2 → q.Prime → q ≠ 2 → q ≠ p →
    ∀ {a : G} {K E A : Subgroup G}, GLAPComponent p (Cg a) K →
      IsChevSimple q (barOf p K ⧸ Subgroup.center (barOf p K)) →
      (∀ d : TauCeti.ValidLieTypeIndex, d.1.characteristic = q → CentralPrimeFree p d.1 →
        IsEmpty (barOf p K ⧸ Subgroup.center (barOf p K) ≃* Cat d)) →
      E ⊓ A ≤ Cg a → IsElemAbelian p (E ⊓ A) → 2 ≤ CFSG.Open.pRank p (E ⊓ A) →
      E ⊓ A ≤ Subgroup.normalizer (K : Set G) → (∀ x ∈ E ⊓ A, x ∈ centBar p ⊤ K → x = 1) →
      ¬ Prop1116Iii p q E A K →
      barX p (Cg a) K ≤
        ⨆ (z : ↥(Cg a)) (_ : (z : G) ∈ E ⊓ A) (_ : z ≠ 1),
          CFSG.GH74.GLS.oPrimeResidualOf q (barX p (Cg a) K ⊓ Subgroup.centralizer
            ({QuotientGroup.mk' (GLAPPrimeCore p ↥(Cg a)) z} : Set (↥(Cg a) ⧸ GLAPPrimeCore p ↥(Cg a))))

theorem input23_11Thm4_of_uni (hU : UniSeitzPlanes OddCpf) (hR : Input23_11Thm4Rest) :
    Inputs2311.Input23_11Thm4 := by
  intro G _ _ p q hp hp2 hq hq2 hqp a K E A hK hchev hA0C hA0el hA0r hN hF hIii
  by_cases h : ∃ d : TauCeti.ValidLieTypeIndex, d.1.characteristic = q ∧ CentralPrimeFree p d.1 ∧
      Nonempty (barOf p K ⧸ Subgroup.center (barOf p K) ≃* Cat d)
  · obtain ⟨d, hdq, hcpf, ⟨θ⟩⟩ := h
    exact le_iSup_of_uni hU hp hp2 hq hqp hK hdq
      (fun hex => hq2 (hdq ▸ characteristic_eq_two_of_d2Exc hex)) (fun _ => ⟨hdq ▸ hq2, hcpf⟩) θ hA0C hA0r
      hN hF
  · refine hR hp hp2 hq hq2 hqp hK hchev (fun d hdq hcpf => ?_) hA0C hA0el hA0r hN hF hIii
    exact not_nonempty_iff.1 fun hne => h ⟨d, hdq, hcpf, hne⟩

end CFSG.LocalAnalysis.GLTheoremB.MovingAround.Inputs2311c
