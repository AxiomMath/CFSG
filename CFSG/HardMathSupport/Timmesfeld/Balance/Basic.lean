module


public import CFSG.HardMathSupport.Timmesfeld.Proving.CentreComponentPGroup
public import CFSG.ClassicalInvolution.Balance.LocalBalance.Moved
public import CFSG.HardMathSupport.Solomon.LocalBalance.Defs

public section

namespace CFSG.HardMathSupport.Timmesfeld.Balance

open CFSG CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.HardMathSupport.Solomon.LocalBalance
  CFSG.ClassicalInvolution.Balance.LocalBalance CFSG.LocalAnalysis.ComponentInitial

open scoped commutatorElement

universe u

@[expose] def H1Stmt : Prop :=
  ∀ {X Z : Type u} [Group X] [Finite X] [Group Z] (φ : X →* Z), Function.Surjective φ →
    ∀ {p : ℕ}, p.Prime → ∀ {Q : Subgroup X}, IsPGroup p Q →
      (GLAPPrimeCoreOf p (Subgroup.centralizer (Q : Set X))).map φ ≤
        GLAPPrimeCoreOf p (Subgroup.centralizer ((Q.map φ : Subgroup Z) : Set Z))

@[expose] noncomputable def fImage {Y : Type*} [Group Y] (F L : Subgroup Y) :
    Subgroup (MulAut ↥L) :=
  (F.subgroupOf (Subgroup.normalizer (L : Set Y))).map (normalizerConjHom L)

theorem map_gLAPPrimeCore_mulEquiv_le (p : ℕ) {A B : Type*} [Group A] [Group B] (e : A ≃* B) :
    (GLAPPrimeCore p A).map e.toMonoidHom ≤ GLAPPrimeCore p B := by
  rw [Subgroup.map_le_iff_le_comap]
  refine sSup_le fun N hN => ?_
  rw [← Subgroup.map_le_iff_le_comap]
  refine le_sSup ⟨hN.1.map e.toMonoidHom e.surjective, ?_⟩
  have h : Nat.card (N.map e.toMonoidHom) = Nat.card N :=
    Subgroup.card_map_of_injective e.injective
  rw [h]
  exact hN.2

theorem map_gLAPPrimeCore_mulEquiv (p : ℕ) {A B : Type*} [Group A] [Group B] (e : A ≃* B) :
    (GLAPPrimeCore p A).map e.toMonoidHom = GLAPPrimeCore p B := by
  refine le_antisymm (map_gLAPPrimeCore_mulEquiv_le p e) ?_
  have h := Subgroup.map_mono (f := e.toMonoidHom) (map_gLAPPrimeCore_mulEquiv_le p e.symm)
  rw [Subgroup.map_map] at h
  have hid : e.toMonoidHom.comp e.symm.toMonoidHom = MonoidHom.id B := by
    ext x; simp
  rwa [hid, Subgroup.map_id] at h

theorem eq_bot_of_isSubnormal_coprime {Y : Type*} [Group Y] [Finite Y] {p : ℕ} (hp : p.Prime)
    (hO : GLAPPrimeCore p Y = ⊥) {K : Subgroup Y} (hK : IsSubnormal K ⊤)
    (hcop : Nat.Coprime p (Nat.card K)) : K = ⊥ := by
  have h1 := CFSG.HardMathSupport.Timmesfeld.Proving.GLAPPrimeCoreOf_le_of_isSubnormal_sub
    (p := p) hp hK
  have h2 : GLAPPrimeCoreOf p (⊤ : Subgroup Y) = ⊥ := by
    unfold GLAPPrimeCoreOf
    rw [← map_gLAPPrimeCore_mulEquiv p (Subgroup.topEquiv (G := Y)).symm, hO, Subgroup.map_bot]
    simp
  have h3 : GLAPPrimeCoreOf p K = K := by
    have : GLAPPrimeCore p ↥K = ⊤ := by
      refine top_unique (le_sSup ⟨inferInstance, ?_⟩)
      simpa using hcop
    unfold GLAPPrimeCoreOf
    rw [this, ← MonoidHom.range_eq_map, Subgroup.range_subtype]
  rw [h2, h3] at h1
  exact le_bot_iff.1 h1

theorem commutator_central_mul_left {Q : Type*} [Group Q] {z : Q} (hz : z ∈ Subgroup.center Q)
    (g h : Q) : ⁅z * g, h⁆ = ⁅g, h⁆ := by
  have key : ∀ a : Q, z * a = a * z := fun a => (Subgroup.mem_center_iff.1 hz a).symm
  rw [commutatorElement_def, commutatorElement_def]
  simp only [mul_inv_rev]
  calc z * g * h * (g⁻¹ * z⁻¹) * h⁻¹ = z * (g * h * g⁻¹) * z⁻¹ * h⁻¹ := by group
    _ = (g * h * g⁻¹) * z * z⁻¹ * h⁻¹ := by rw [key]
    _ = g * h * g⁻¹ * h⁻¹ := by group

theorem commutator_central_mul_right {Q : Type*} [Group Q] {z : Q} (hz : z ∈ Subgroup.center Q)
    (g h : Q) : ⁅g, z * h⁆ = ⁅g, h⁆ := by
  have key : ∀ a : Q, z * a = a * z := fun a => (Subgroup.mem_center_iff.1 hz a).symm
  rw [commutatorElement_def, commutatorElement_def]
  simp only [mul_inv_rev]
  calc g * (z * h) * g⁻¹ * (h⁻¹ * z⁻¹) = (g * z) * h * g⁻¹ * h⁻¹ * z⁻¹ := by group
    _ = z * (g * h * g⁻¹ * h⁻¹) * z⁻¹ := by rw [← key g]; group
    _ = (g * h * g⁻¹ * h⁻¹) * z * z⁻¹ := by rw [key]
    _ = g * h * g⁻¹ * h⁻¹ := by group

theorem center_eq_bot_of_perfect_of_coprime {Q : Type*} [Group Q] [Finite Q]
    (hperf : Group.IsPerfect Q)
    (hcop : Nat.Coprime (Nat.card (Subgroup.center Q)) (Nat.card (Q ⧸ Subgroup.center Q))) :
    Subgroup.center Q = ⊥ := by
  obtain ⟨H, hH⟩ := Subgroup.exists_right_complement'_of_coprime (N := Subgroup.center Q) hcop
  have hcomm : ⁅(⊤ : Subgroup Q), ⊤⁆ ≤ H := by
    rw [Subgroup.commutator_le]
    intro g1 _ g2 _
    have hg : ∀ g : Q, ∃ z ∈ Subgroup.center Q, ∃ h ∈ H, z * h = g := fun g =>
      Subgroup.mem_sup_of_normal_left.1 (hH.isCompl.codisjoint.eq_top ▸ Subgroup.mem_top g)
    obtain ⟨z1, hz1, h1, hh1, rfl⟩ := hg g1
    obtain ⟨z2, hz2, h2, hh2, rfl⟩ := hg g2
    have e : ⁅z1 * h1, z2 * h2⁆ = ⁅h1, h2⁆ := by
      rw [commutator_central_mul_left hz1, commutator_central_mul_right hz2]
    rw [e]
    exact H.mul_mem (H.mul_mem (H.mul_mem hh1 hh2) (H.inv_mem hh1)) (H.inv_mem hh2)
  have hH' : H = ⊤ := by
    rw [← top_le_iff]
    have := hperf.commutator_eq_top
    rw [commutator_def] at this
    exact this ▸ hcomm
  have := hH.disjoint
  rw [hH'] at this
  exact disjoint_top.1 this

theorem isSubnormal_map_of_le_center {Y : Type*} [Group Y] {L : Subgroup Y}
    (hL : IsSubnormal L ⊤) {N : Subgroup ↥L} (hN : N ≤ Subgroup.center ↥L) :
    IsSubnormal (N.map L.subtype) ⊤ := by
  refine IsSubnormal.step (M := L) (Subgroup.map_subtype_le N) ?_ hL
  have : (N.map L.subtype).subgroupOf L = N := Subgroup.comap_map_eq_self_of_injective L.subtype_injective N
  rw [this]
  exact Subgroup.normal_of_le_center hN

theorem prime_eq_of_dvd_card_center {Y : Type*} [Group Y] [Finite Y] {p : ℕ} (hp : p.Prime)
    (hO : GLAPPrimeCore p Y = ⊥) {L : Subgroup Y} (hL : IsSubnormal L ⊤) {q : ℕ} (hq : q.Prime)
    (hdvd : q ∣ Nat.card (Subgroup.center ↥L)) : q = p := by
  by_contra hne
  have : Fact q.Prime := ⟨hq⟩
  obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' (G := Subgroup.center ↥L) q hdvd
  set N : Subgroup ↥L := Subgroup.zpowers (z : ↥L) with hN
  have hNc : N ≤ Subgroup.center ↥L := by
    rw [hN, Subgroup.zpowers_le]
    exact z.2
  have hcard : Nat.card (N.map L.subtype) = q := by
    rw [Subgroup.card_map_of_injective L.subtype_injective, hN, Nat.card_zpowers]
    rw [← hz]
    exact (Subgroup.orderOf_coe z)
  have h := eq_bot_of_isSubnormal_coprime hp hO (isSubnormal_map_of_le_center hL hNc)
    (by rw [hcard]; exact (Nat.coprime_primes hp hq).2 (Ne.symm hne))
  rw [h, Subgroup.card_bot] at hcard
  exact hq.one_lt.ne hcard

theorem gLAPPrimeCoreOf_eq_map_of_mulEquiv {M A : Type*} [Group M] [Group A] (p : ℕ)
    {B : Subgroup M} (φ : A →* M) (e : A ≃* ↥B) (he : ∀ x, ((e x : ↥B) : M) = φ x) :
    GLAPPrimeCoreOf p B = (GLAPPrimeCore p A).map φ := by
  unfold GLAPPrimeCoreOf
  rw [← map_gLAPPrimeCore_mulEquiv p e, Subgroup.map_map]
  congr 1
  ext x
  exact he x

variable {Y : Type u} [Group Y] [Finite Y] {p : ℕ}

theorem p_dvd_card_center_quot (hp : p.Prime) (hO : GLAPPrimeCore p Y = ⊥) {L : Subgroup Y}
    (hL : IsComponent L) : p ∣ Nat.card (↥L ⧸ Subgroup.center ↥L) := by
  have hLo := (isComponent_iff_open L).1 hL
  by_contra hdiv
  have hcop : Nat.Coprime (Nat.card (Subgroup.center ↥L)) (Nat.card (↥L ⧸ Subgroup.center ↥L)) :=
    Nat.coprime_of_dvd fun k hk hk1 hk2 => by
      have := prime_eq_of_dvd_card_center hp hO hLo.2.1 hk hk1
      exact hdiv (this ▸ hk2)
  have hZ := center_eq_bot_of_perfect_of_coprime hL.1.1 hcop
  have hLc : Nat.Coprime p (Nat.card L) := by
    have h1 : Nat.card (Subgroup.center ↥L) = 1 := by rw [hZ]; exact Subgroup.card_bot
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (Subgroup.center ↥L), h1, mul_one]
    exact (Nat.Prime.coprime_iff_not_dvd hp).2 hdiv
  have hbot := eq_bot_of_isSubnormal_coprime hp hO hLo.2.1 hLc
  obtain ⟨x, hx, y, hy, hxy⟩ := exists_noncomm_of_isQuasisimple hL.1
  rw [hbot, Subgroup.mem_bot] at hx hy
  exact hxy (by rw [hx, hy])

theorem gLAPPrimeCoreOf_inf_centralizer_eq_map {M : Type*} [Group M] [Finite M] (p : ℕ)
    (H' : Subgroup M) {d : M} (hd : d ∈ H') :
    GLAPPrimeCoreOf p (H' ⊓ Subgroup.centralizer ({d} : Set M)) =
      (GLAPPrimeCoreOf p (Subgroup.centralizer ({(⟨d, hd⟩ : H')} : Set H'))).map H'.subtype := by
  set T : Subgroup H' := Subgroup.centralizer ({(⟨d, hd⟩ : H')} : Set H') with hT
  have hmap : T.map H'.subtype = H' ⊓ Subgroup.centralizer ({d} : Set M) := by
    ext x
    simp only [Subgroup.mem_map, hT, Subgroup.mem_centralizer_iff, Set.mem_singleton_iff,
      forall_eq, Subgroup.mem_inf, Subgroup.coe_subtype]
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact ⟨y.2, by simpa using congrArg Subtype.val hy⟩
    · rintro ⟨hx, hc⟩
      exact ⟨⟨x, hx⟩, Subtype.ext (by simpa using hc), rfl⟩
  let e : ↥T ≃* ↥(H' ⊓ Subgroup.centralizer ({d} : Set M)) :=
    (Subgroup.equivMapOfInjective T H'.subtype H'.subtype_injective).trans
      (MulEquiv.subgroupCongr hmap)
  have := gLAPPrimeCoreOf_eq_map_of_mulEquiv p (H'.subtype.comp T.subtype) e (fun x => rfl)
  rw [this]
  show _ = Subgroup.map H'.subtype (Subgroup.map T.subtype _)
  rw [Subgroup.map_map]

end CFSG.HardMathSupport.Timmesfeld.Balance
