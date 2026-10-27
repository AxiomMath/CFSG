module

public import CFSG.HardMathSupport.Dickson.Bal207.CompShape
public import CFSG.HardMathSupport.Dickson.Bal207.GlueNorm
public import CFSG.HardMathSupport.Dickson.I271.Support.AmbBase

public section

namespace CFSG.HardMathSupport.Dickson.Bal207.Uni

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.HardMathSupport.Solomon.LocalBalance
  CFSG.HardMathSupport.Solomon.Coordinator CFSG.HardMathSupport.Dickson.I271

open scoped commutatorElement

variable {X : Type} [Group X]

section Maps

variable {K : Subgroup X} {S : Type} [Group S]

@[expose] noncomputable def uniMap (e : (↥K ⧸ Subgroup.center ↥K) ≃* S) : ↥K →* S :=
  e.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center ↥K))

@[expose] noncomputable def uniAut (e : (↥K ⧸ Subgroup.center ↥K) ≃* S) :
    ↥(Subgroup.normalizer (K : Set X)) →* MulAut S :=
  (MulAut.congr e).toMonoidHom.comp (actHom K)

variable (e : (↥K ⧸ Subgroup.center ↥K) ≃* S)

theorem uniMap_apply (k : ↥K) : uniMap e k = e (QuotientGroup.mk k) := rfl

theorem uniMap_surjective : Function.Surjective (uniMap e) :=
  e.surjective.comp (QuotientGroup.mk'_surjective _)

theorem uniMap_eq_one_iff (k : ↥K) : uniMap e k = 1 ↔ k ∈ Subgroup.center ↥K := by
  rw [uniMap_apply, map_eq_one_iff _ e.injective, QuotientGroup.eq_one_iff]

theorem uniAut_apply (g : ↥(Subgroup.normalizer (K : Set X))) (s : S) :
    uniAut e g s = e (actHom K g (e.symm s)) := rfl

theorem uniAut_uniMap (g : ↥(Subgroup.normalizer (K : Set X))) (k : ↥K) :
    uniAut e g (uniMap e k) = uniMap e (K.normalizerMonoidHom g k) := by
  rw [uniAut_apply, uniMap_apply, MulEquiv.symm_apply_apply, actHom_mk]
  rfl

theorem uniMap_conj {g : X} (hg : g ∈ Subgroup.normalizer (K : Set X)) (k : ↥K)
    (hk : g * (k : X) * g⁻¹ ∈ K) :
    uniMap e ⟨g * (k : X) * g⁻¹, hk⟩ = uniAut e ⟨g, hg⟩ (uniMap e k) := by
  rw [uniAut_uniMap]
  rfl

theorem mem_centralizer_of_uniAut_eq_one (hK : commutator ↥K = ⊤) {g : X}
    (hg : g ∈ Subgroup.normalizer (K : Set X)) (h1 : uniAut e ⟨g, hg⟩ = 1) :
    g ∈ Subgroup.centralizer (K : Set X) := by
  have hα : actHom K ⟨g, hg⟩ = 1 := by
    apply (MulAut.congr e).injective
    rw [map_one]
    exact h1
  have hα₀ : K.normalizerMonoidHom ⟨g, hg⟩ = 1 := by
    refine mulAut_eq_one_of_forall_mem_center hK _ fun k => ?_
    rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_mul, QuotientGroup.mk_inv]
    have h2 := congrArg (fun φ : MulAut (↥K ⧸ Subgroup.center ↥K) => φ (QuotientGroup.mk k)) hα
    simp only [actHom_mk, MulAut.one_apply] at h2
    rw [h2, inv_mul_cancel]
  rw [Subgroup.mem_centralizer_iff]
  intro k hk
  have h3 := congrArg (fun γ : MulAut ↥K => ((γ ⟨k, hk⟩ : ↥K) : X)) hα₀
  simp only [MulAut.one_apply] at h3
  change g * k * g⁻¹ = k at h3
  calc k * g = g * k * g⁻¹ * g := by rw [h3]
    _ = g * k := by group

end Maps

section Perfect

theorem uni_mem_center_of_map {J L : Type*} [Group J] [Group L] (hJ : Group.IsPerfect J)
    (φ : J →* L) (hker : φ.ker ≤ Subgroup.center J) {z : J} (hz : φ z ∈ Subgroup.center L) :
    z ∈ Subgroup.center J := by
  have hcen : (QuotientGroup.mk z : J ⧸ Subgroup.center J) ∈
      Subgroup.center (J ⧸ Subgroup.center J) := by
    rw [Subgroup.mem_center_iff]
    intro q
    obtain ⟨m, rfl⟩ := QuotientGroup.mk_surjective q
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq]
    have hc : ⁅z, m⁆ ∈ Subgroup.center J := by
      refine hker ?_
      rw [MonoidHom.mem_ker, map_commutatorElement, commutatorElement_def,
        ← (Subgroup.mem_center_iff.1 hz (φ m))]
      group
    have e : z * m = ⁅z, m⁆ * (m * z) := by
      rw [commutatorElement_def]
      group
    have hzc := Subgroup.mem_center_iff.1 hc (m * z)
    have e2 : (m * z)⁻¹ * (z * m) = ⁅z, m⁆ := by
      rw [e, ← hzc]
      exact inv_mul_cancel_left _ _
    rw [e2]
    exact hc
  rw [Group.IsPerfect.center_quotient_center_eq_bot] at hcen
  exact (QuotientGroup.eq_one_iff z).1 (Subgroup.mem_bot.1 hcen)

end Perfect

theorem uni_exists_comm_not_mem_core [Finite X] {p : ℕ} (hp : p.Prime) {J : Subgroup X}
    (hq : CFSG.Open.IsQuasisimple ↥J) (hpJ : p ∣ Nat.card ↥J) {b : X} (hbJ : b ∈ J)
    (hbZ : (⟨b, hbJ⟩ : ↥J) ∉ Subgroup.center ↥J) :
    ∃ y ∈ J, ⁅b, y⁆ ∉ GLAPPrimeCoreOf p J := by
  classical
  by_contra hcon
  push Not at hcon
  have hperf : Group.IsPerfect ↥J := Group.isPerfect_def.2 hq.1
  have hO : GLAPPrimeCore p ↥J ≤ Subgroup.center ↥J := by
    rcases i253_normal_le_center_or_top hq (GLAPPrimeCore p ↥J) with h | h
    · exact h
    · exfalso
      have hcop := coprime_card_gLAPPrimeCore_aux p ↥J
      rw [h, Subgroup.card_top] at hcop
      exact hp.one_lt.ne' (Nat.Coprime.eq_one_of_dvd hcop hpJ)
  refine hbZ (uni_mem_center_of_map hperf (QuotientGroup.mk' (Subgroup.center ↥J))
    (by rw [QuotientGroup.ker_mk']) ?_)
  rw [Subgroup.mem_center_iff]
  intro q
  obtain ⟨m, rfl⟩ := QuotientGroup.mk_surjective q
  rw [QuotientGroup.mk'_apply, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq]
  have hz : ⁅(⟨b, hbJ⟩ : ↥J), m⁆ ∈ Subgroup.center ↥J := by
    obtain ⟨_, hcore⟩ := (Glue.mem_gLAPPrimeCoreOf_iff' p J _).1 (hcon (m : X) m.2)
    exact hO hcore
  have e : (⟨b, hbJ⟩ : ↥J) * m = ⁅(⟨b, hbJ⟩ : ↥J), m⁆ * (m * ⟨b, hbJ⟩) := by
    rw [commutatorElement_def]
    group
  have hzc := Subgroup.mem_center_iff.1 hz (m * ⟨b, hbJ⟩)
  have e2 : (m * ⟨b, hbJ⟩)⁻¹ * ((⟨b, hbJ⟩ : ↥J) * m) = ⁅(⟨b, hbJ⟩ : ↥J), m⁆ := by
    rw [e, ← hzc]
    exact inv_mul_cancel_left _ _
  rw [e2]
  exact hz

theorem uni_exists_mem_of_fixed [Finite X] {p : ℕ} {K B : Subgroup X}
    (hB : IsSCp p ⊤ B) (hBK : B ≤ Subgroup.normalizer (K : Set X))
    (hZ : Nat.Coprime p (Nat.card (Subgroup.center ↥K))) {S : Type} [Group S]
    (e : (↥K ⧸ Subgroup.center ↥K) ≃* S) {s : S} (hs : s ^ p = 1)
    (hfix : ∀ (b : X) (hb : b ∈ B), uniAut e ⟨b, hBK hb⟩ s = s) :
    ∃ y ∈ B, ∃ hy : y ∈ K, uniMap e ⟨y, hy⟩ = s := by
  obtain ⟨k, rfl⟩ := uniMap_surjective e s
  set m := Nat.card (Subgroup.center ↥K) with hm
  have hcop : Nat.Coprime m (orderOf (uniMap e k)) :=
    Nat.Coprime.coprime_dvd_right (orderOf_dvd_of_pow_eq_one hs) hZ.symm
  obtain ⟨t, ht⟩ := exists_pow_eq_self_of_coprime hcop
  set y : ↥K := (k ^ m) ^ t with hy
  have hyψ : uniMap e y = uniMap e k := by rw [hy, map_pow, map_pow, ht]
  have hkp : k ^ p ∈ Subgroup.center ↥K := by
    rw [← uniMap_eq_one_iff e, map_pow]
    exact hs
  have hyp : y ^ p = 1 := by
    have h1 : (⟨k ^ p, hkp⟩ : ↥(Subgroup.center ↥K)) ^ m = 1 := pow_card_eq_one'
    have h2 : (k ^ p) ^ m = 1 := congrArg Subtype.val h1
    rw [hy, ← pow_mul, ← pow_mul, show m * (t * p) = p * m * t by ring, pow_mul, pow_mul, h2,
      one_pow]
  have hyp' : (y : X) ^ p = 1 := by
    rw [← Subgroup.coe_pow, hyp, Subgroup.coe_one]
  refine ⟨y, ?_, y.2, hyψ⟩
  refine Amb.mem_of_comm_of_isSCp hB hyp' fun b hb => ?_
  have hbN := hBK hb
  have hmem : b * (y : X) * b⁻¹ ∈ K := (Subgroup.mem_normalizer_iff.1 hbN y).1 y.2
  set y' : ↥K := ⟨b * (y : X) * b⁻¹, hmem⟩ with hy'
  have hψ' : uniMap e y' = uniMap e y := by
    rw [hy', uniMap_conj e hbN y hmem, hyψ]
    exact hfix b hb
  have hz : y' * y⁻¹ ∈ Subgroup.center ↥K := by
    rw [← uniMap_eq_one_iff e, map_mul, map_inv, hψ', mul_inv_cancel]
  have hy'p : y' ^ p = 1 := by
    apply Subtype.ext
    rw [Subgroup.coe_pow, hy', Subgroup.coe_one]
    have : (b * (y : X) * b⁻¹) ^ p = b * (y : X) ^ p * b⁻¹ := by
      rw [conj_pow]
    rw [this, hyp', mul_one, mul_inv_cancel]
  set z : ↥(Subgroup.center ↥K) := ⟨y' * y⁻¹, hz⟩ with hzdef
  have hzp : z ^ p = 1 := by
    apply Subtype.ext
    rw [Subgroup.coe_pow, hzdef, Subgroup.coe_one]
    have hcomm : Commute y' y⁻¹ := by
      refine Commute.symm (Commute.inv_left ?_)
      have := Subgroup.mem_center_iff.1 hz y
      show y * y' = y' * y
      calc y * y' = y * (y' * y⁻¹) * y := by group
        _ = (y' * y⁻¹) * y * y := by rw [this]
        _ = y' * y := by group
    rw [hcomm.mul_pow, hy'p, inv_pow, hyp, inv_one, one_mul]
  have hz1 : z = 1 := by
    have h1 : orderOf z ∣ p := orderOf_dvd_of_pow_eq_one hzp
    have h2 : orderOf z ∣ m := orderOf_dvd_natCard z
    have h3 : orderOf z ∣ Nat.gcd p m := Nat.dvd_gcd h1 h2
    rw [hZ.gcd_eq_one, Nat.dvd_one, orderOf_eq_one_iff] at h3
    exact h3
  have h4 : y' * y⁻¹ = 1 := congrArg Subtype.val hz1
  have h5 : b * (y : X) * b⁻¹ = y := by
    have := congrArg Subtype.val (mul_inv_eq_one.1 h4)
    exact this
  calc b * (y : X) = b * (y : X) * b⁻¹ * b := by group
    _ = (y : X) * b := by rw [h5]

section Lift

variable {K : Subgroup X} {S : Type} [Group S] (e : (↥K ⧸ Subgroup.center ↥K) ≃* S)

@[expose] noncomputable def uniRestr {J : Subgroup X} (hJK : J ≤ K) :
    ↥J →* ↥((J.comap K.subtype).map (uniMap e)) :=
  ((uniMap e).comp (Subgroup.inclusion hJK)).codRestrict _ fun j =>
    ⟨Subgroup.inclusion hJK j, j.2, rfl⟩

theorem uniRestr_surjective {J : Subgroup X} (hJK : J ≤ K) :
    Function.Surjective (uniRestr e hJK) := by
  rintro ⟨s, k, hk, rfl⟩
  exact ⟨⟨k, hk⟩, rfl⟩

theorem ker_uniRestr_le_center {J : Subgroup X} (hJK : J ≤ K) :
    (uniRestr e hJK).ker ≤ Subgroup.center ↥J := by
  intro j hj
  have h1 : uniMap e (Subgroup.inclusion hJK j) = 1 := congrArg Subtype.val hj
  rw [uniMap_eq_one_iff] at h1
  rw [Subgroup.mem_center_iff]
  intro i
  have := Subgroup.mem_center_iff.1 h1 (Subgroup.inclusion hJK i)
  exact Subtype.ext (congrArg (fun w : ↥K => (w : X)) this)

theorem uni_component [Finite X] {p : ℕ} (hp : p.Prime) (hK : CFSG.Open.IsQuasisimple ↥K)
    (hZ : Nat.Coprime p (Nat.card (Subgroup.center ↥K))) {a : X}
    (ha : a ∈ Subgroup.normalizer (K : Set X)) (hlay : PerfectInLayer (uniAut e ⟨a, ha⟩))
    {J : Subgroup X} (hJ : GLAPComponent p (K ⊓ Subgroup.centralizer ({a} : Set X)) J) :
    IsComponentOf J (K ⊓ Subgroup.centralizer ({a} : Set X)) ∧
      IsComponentOf ((J.comap K.subtype).map (uniMap e)) (fixSubgroup (uniAut e ⟨a, ha⟩)) ∧
      ∀ y : ↥K, y ^ p = 1 → uniMap e y ∈ (J.comap K.subtype).map (uniMap e) → (y : X) ∈ J := by
  let α₀ : MulAut ↥K := K.normalizerMonoidHom ⟨a, ha⟩
  have hα₀ : ∀ k : ↥K, ((α₀ k : ↥K) : X) = a * k * a⁻¹ := fun k => rfl
  let Z := Subgroup.center ↥K
  let π : ↥K →* (↥K ⧸ Z) := QuotientGroup.mk' Z
  have hπ : Function.Surjective π := QuotientGroup.mk'_surjective _
  have hker : π.ker ≤ Subgroup.center ↥K := by
    rw [QuotientGroup.ker_mk']
  set β := actHom K ⟨a, ha⟩ with hβdef
  have hbar : ∀ k, π (α₀ k) = β (π k) := fun k => (actHom_mk K ⟨a, ha⟩ k).symm
  have hlayβ : PerfectInLayer β := LieSemisimple.perfectInLayer_of_congr e β hlay
  set C : Subgroup ↥K := fixSubgroup α₀ with hC
  have hCmap : C.map K.subtype = K ⊓ Subgroup.centralizer ({a} : Set X) := by
    ext y
    constructor
    · rintro ⟨k, hk, rfl⟩
      have h1 : a * (k : X) * a⁻¹ = k := by
        have := congrArg Subtype.val (show α₀ k = k from hk)
        rwa [hα₀] at this
      refine ⟨k.2, Subgroup.mem_centralizer_singleton_iff.2 ?_⟩
      show (k : X) * a = a * (k : X)
      calc (k : X) * a = (a * (k : X) * a⁻¹) * a := by rw [h1]
        _ = a * (k : X) := by group
    · rintro ⟨hyK, hyC⟩
      refine ⟨⟨y, hyK⟩, ?_, rfl⟩
      show α₀ ⟨y, hyK⟩ = ⟨y, hyK⟩
      apply Subtype.ext
      rw [hα₀]
      have hyC' : y * a = a * y := Subgroup.mem_centralizer_singleton_iff.1 hyC
      show a * y * a⁻¹ = y
      calc a * y * a⁻¹ = (y * a) * a⁻¹ := by rw [hyC']
        _ = y := by group
  have hc : ∀ y ∈ C ⊓ K.subtype.ker, ∀ z ∈ C, z * y = y * z := by
    intro y hy z _
    have : y = 1 := Subtype.ext (MonoidHom.mem_ker.1 hy.2)
    rw [this, mul_one, one_mul]
  have hJ0 : GLAPComponent p (C.map K.subtype) J := by rw [hCmap]; exact hJ
  obtain ⟨J₁, hJ₁, hJ₁map⟩ := exists_glaPComponent_map_central hp K.subtype hc hJ0
  have hJcomap : J.comap K.subtype = J₁ := by
    rw [← hJ₁map]
    exact Subgroup.comap_map_eq_self_of_injective K.subtype_injective J₁
  have hJβ : GLAPComponent p (fixSubgroup β) (J₁.map π) :=
    glaPComponent_map_fixSubgroup π hker α₀ β hbar hπ hp hJ₁
  have hlay' : J₁.map π ≤ GLALayer (fixSubgroup β) :=
    hlayβ _ hJβ.1 (glaPComponent_perfect hJβ)
  have hJc : IsComponentOf (J₁.map π) (fixSubgroup β) :=
    (glaPComponent_isComponent_of_le_layer hJβ hlay').1
  have hJ₁perf : ⁅J₁, J₁⁆ = J₁ := glaPComponent_perfect hJ₁
  have hperf : Group.IsPerfect ↥J₁ := Subgroup.isPerfect_iff.2 hJ₁perf
  have hcov := ker_subgroupMap_le_center π hker J₁
  have hQ1 : CFSG.IsQuasisimple ↥J₁ :=
    isQuasisimple_of_central_cover (π.subgroupMap J₁) (MonoidHom.subgroupMap_surjective π J₁)
      hperf hcov
      ((CFSG.ComponentClassification.AssemblyBPredicates.isQuasisimple_iff_native _).1 hJc.2.2)
  have hQ1' : CFSG.Open.IsQuasisimple ↥J₁ :=
    (CFSG.ComponentClassification.AssemblyBPredicates.isQuasisimple_iff_native _).2 hQ1
  let e₂ : ↥J₁ ≃* ↥J :=
    (J₁.equivMapOfInjective K.subtype K.subtype_injective).trans
      (MulEquiv.subgroupCongr hJ₁map)
  refine ⟨⟨hJ.1, hJ.2.1, CFSG.SignalizerFunctorTheorem.TransportA.isQuasisimple_of_mulEquiv e₂
    hQ1'⟩, ?_, fun y hyp hy => ?_⟩
  ·
    have h1 := CFSG.SignalizerFunctorTheorem.TransportA.isComponentOf_map e hJc
    have h2 : (J₁.map π).map (e : (↥K ⧸ Subgroup.center ↥K) →* S) =
        (J.comap K.subtype).map (uniMap e) := by
      rw [hJcomap, Subgroup.map_map]
      rfl
    have h3 : (fixSubgroup β).map (e : (↥K ⧸ Subgroup.center ↥K) →* S) =
        fixSubgroup (uniAut e ⟨a, ha⟩) := (fixSubgroup_mulAutCongr e β).symm
    rw [h2, h3] at h1
    exact h1
  ·
    rw [hJcomap] at hy
    obtain ⟨j, hj, hjy⟩ := hy
    have hz : j⁻¹ * y ∈ Subgroup.center ↥K := by
      rw [← uniMap_eq_one_iff e, map_mul, map_inv, hjy, inv_mul_cancel]
    set z := j⁻¹ * y with hzdef
    have hyz : y = j * z := by rw [hzdef]; group
    have hzc : ∀ w : ↥K, z * w = w * z := fun w => (Subgroup.mem_center_iff.1 hz w).symm
    have hjp : j ^ p = (z⁻¹) ^ p := by
      have hj' : j = y * z⁻¹ := by rw [hyz]; group
      have hcomm : Commute y z⁻¹ := by
        refine Commute.inv_right ?_
        exact (hzc y).symm
      rw [hj', hcomm.mul_pow, hyp, one_mul]
    have hzp : (z⁻¹) ^ p ∈ J₁ := hjp ▸ J₁.pow_mem hj p
    have hcop : Nat.Coprime p (orderOf z⁻¹) := by
      have h1 : orderOf (⟨z⁻¹, inv_mem hz⟩ : ↥(Subgroup.center ↥K)) ∣
          Nat.card (Subgroup.center ↥K) := orderOf_dvd_natCard _
      rw [Subgroup.orderOf_mk] at h1
      exact Nat.Coprime.coprime_dvd_right h1 hZ
    obtain ⟨t, ht⟩ := exists_pow_eq_self_of_coprime hcop
    have hzJ : z⁻¹ ∈ J₁ := ht ▸ J₁.pow_mem hzp t
    have hyJ : y ∈ J₁ := by
      rw [hyz]
      exact J₁.mul_mem hj (by simpa using J₁.inv_mem hzJ)
    rw [← hJcomap] at hyJ
    exact hyJ

end Lift

end CFSG.HardMathSupport.Dickson.Bal207.Uni

end
