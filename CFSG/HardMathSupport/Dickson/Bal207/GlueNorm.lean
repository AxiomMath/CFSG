module

public import CFSG.HardMathSupport.Solomon.Coordinator.I25_3Quasi
public import CFSG.HardMathSupport.Dickson.Bal207.Restate

public section

namespace CFSG.HardMathSupport.Dickson.Bal207.Glue

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.HardMathSupport.Solomon.LocalBalance
  CFSG.HardMathSupport.Solomon.Coordinator CFSG.HardMathSupport.Dickson.I271

open scoped commutatorElement

section NoTriality

variable {X : Type} [Group X]

@[expose] def AutIsoInvariant (G : ∀ (S : Type) [Group S], MulAut S → Prop) : Prop :=
  ∀ {S S' : Type} [Group S] [Group S'] (e : S ≃* S') {φ : MulAut S},
    G S φ → G S' (MulAut.congr e φ)

@[expose] noncomputable def centerQuotEquiv {L M : Type*} [Group L] [Group M] (g : L ≃* M) :
    (L ⧸ Subgroup.center L) ≃* (M ⧸ Subgroup.center M) :=
  QuotientGroup.congr _ _ g (Subgroup.map_center_eq g)

@[expose] noncomputable def subgroupOfCenterQuotEquiv {J Y : Subgroup X} (hJY : J ≤ Y) :
    (↥(J.subgroupOf Y) ⧸ Subgroup.center ↥(J.subgroupOf Y)) ≃* (↥J ⧸ Subgroup.center ↥J) :=
  centerQuotEquiv (Subgroup.subgroupOfEquivOfLe hJY)

theorem mem_normalizer_of_subgroupOf {J Y : Subgroup X} (hJY : J ≤ Y) {y : ↥Y}
    (hy : y ∈ Subgroup.normalizer ((J.subgroupOf Y : Subgroup ↥Y) : Set ↥Y)) :
    (y : X) ∈ Subgroup.normalizer (J : Set X) := by
  rw [Subgroup.mem_normalizer_iff]
  intro h
  constructor
  · intro hh
    have := (Subgroup.mem_normalizer_iff.1 hy ⟨h, hJY hh⟩).1 hh
    simpa [Subgroup.mem_subgroupOf] using this
  · intro hh
    have hhY : h ∈ Y := by
      have h1 : (y : X) * h * (y : X)⁻¹ ∈ Y := hJY hh
      have := Y.mul_mem (Y.mul_mem (Y.inv_mem y.2) h1) y.2
      simpa [mul_assoc] using this
    have := (Subgroup.mem_normalizer_iff.1 hy ⟨h, hhY⟩).2
      (by simpa [Subgroup.mem_subgroupOf] using hh)
    simpa [Subgroup.mem_subgroupOf] using this

theorem congr_actHom_subgroupOf {J Y : Subgroup X} (hJY : J ≤ Y) {y : ↥Y}
    (hy : y ∈ Subgroup.normalizer ((J.subgroupOf Y : Subgroup ↥Y) : Set ↥Y)) :
    MulAut.congr (subgroupOfCenterQuotEquiv hJY) (actHom (J.subgroupOf Y) ⟨y, hy⟩) =
      actHom J ⟨(y : X), mem_normalizer_of_subgroupOf hJY hy⟩ := by
  refine MulEquiv.ext fun q => ?_
  obtain ⟨s, rfl⟩ := (subgroupOfCenterQuotEquiv hJY).surjective q
  show (subgroupOfCenterQuotEquiv hJY) ((actHom (J.subgroupOf Y) ⟨y, hy⟩)
    ((subgroupOfCenterQuotEquiv hJY).symm ((subgroupOfCenterQuotEquiv hJY) s))) = _
  rw [MulEquiv.symm_apply_apply]
  induction s using QuotientGroup.induction_on with
  | H j => rfl

theorem noTrialityOn_subgroupOf {G : ∀ (S : Type) [Group S], MulAut S → Prop}
    (hG : AutIsoInvariant G) {J B Y : Subgroup X} (hJY : J ≤ Y) (hNT : NoTrialityOn G B J) :
    NoTrialityOn G (B.subgroupOf Y) (J.subgroupOf Y) := by
  intro ψ hψ hψ'
  obtain ⟨y, hy, hyB, rfl⟩ := mem_autImage.1 hψ
  have hφ : actHom J ⟨(y : X), mem_normalizer_of_subgroupOf hJY hy⟩ ∈ autImage B J :=
    mem_autImage.2 ⟨(y : X), mem_normalizer_of_subgroupOf hJY hy, hyB, rfl⟩
  refine hNT _ hφ ⟨?_, ?_⟩
  · rw [← congr_actHom_subgroupOf hJY hy, ← map_pow, hψ'.1, map_one]
  · rw [← congr_actHom_subgroupOf hJY hy]
    exact hG _ hψ'.2

end NoTriality

section Conj

variable {X : Type} [Group X]

theorem mem_centralizer_mul_iff_of_mem_centralizer {K : Subgroup X} {a z x : X}
    (hz : z ∈ Subgroup.centralizer (K : Set X)) (hx : x ∈ K) :
    x ∈ Subgroup.centralizer ({z * a} : Set X) ↔ x ∈ Subgroup.centralizer ({a} : Set X) := by
  have hzx : z * x = x * z := (Subgroup.mem_centralizer_iff.1 hz x hx).symm
  rw [Subgroup.mem_centralizer_singleton_iff, Subgroup.mem_centralizer_singleton_iff]
  constructor
  · intro h
    have h1 : z * (x * a) = z * (a * x) := by
      calc z * (x * a) = (z * x) * a := by group
        _ = (x * z) * a := by rw [hzx]
        _ = x * (z * a) := by group
        _ = (z * a) * x := h
        _ = z * (a * x) := by group
    exact mul_left_cancel h1
  · intro h
    calc x * (z * a) = (x * z) * a := by group
      _ = (z * x) * a := by rw [hzx]
      _ = z * (x * a) := by group
      _ = z * (a * x) := by rw [h]
      _ = (z * a) * x := by group

theorem glaPComponent_gLBConj_of_comm [Finite X] {p : ℕ} {K J : Subgroup X} {a g : X}
    (hg : g ∈ Subgroup.normalizer (K : Set X))
    (hga : g * a * g⁻¹ * a⁻¹ ∈ Subgroup.centralizer (K : Set X))
    (hJ : GLAPComponent p (K ⊓ Subgroup.centralizer ({a} : Set X)) J) :
    GLAPComponent p (K ⊓ Subgroup.centralizer ({a} : Set X)) (GLBConj g J) := by
  have h := CFSG.LocalAnalysis.GLTheoremB.glaPComponent_gLBConj hJ g
  have hgK : ∀ x, x ∈ K ↔ g * x * g⁻¹ ∈ K := fun x => Subgroup.mem_normalizer_iff.1 hg x
  have hz'' : g⁻¹ * a * g * a⁻¹ ∈ Subgroup.centralizer (K : Set X) := by
    rw [Subgroup.mem_centralizer_iff]
    intro k hk
    have hk' : g * k * g⁻¹ ∈ K := (hgK k).1 hk
    have hz : Commute (g * k * g⁻¹) (g * a * g⁻¹ * a⁻¹) :=
      Subgroup.mem_centralizer_iff.1 hga _ hk'
    have hzi := hz.inv_right.eq
    have e : g⁻¹ * a * g * a⁻¹ = g⁻¹ * (g * a * g⁻¹ * a⁻¹)⁻¹ * g := by group
    rw [e]
    calc k * (g⁻¹ * (g * a * g⁻¹ * a⁻¹)⁻¹ * g)
        = g⁻¹ * ((g * k * g⁻¹) * (g * a * g⁻¹ * a⁻¹)⁻¹) * g := by group
      _ = g⁻¹ * ((g * a * g⁻¹ * a⁻¹)⁻¹ * (g * k * g⁻¹)) * g := by rw [hzi]
      _ = (g⁻¹ * (g * a * g⁻¹ * a⁻¹)⁻¹ * g) * k := by group
  have hconj : ∀ x, g * x * g⁻¹ ∈ Subgroup.centralizer ({a} : Set X) ↔
      x ∈ Subgroup.centralizer ({g⁻¹ * a * g} : Set X) := by
    intro x
    rw [Subgroup.mem_centralizer_singleton_iff, Subgroup.mem_centralizer_singleton_iff]
    constructor
    · intro h
      calc x * (g⁻¹ * a * g) = g⁻¹ * ((g * x * g⁻¹) * a) * g := by group
        _ = g⁻¹ * (a * (g * x * g⁻¹)) * g := by rw [h]
        _ = (g⁻¹ * a * g) * x := by group
    · intro h
      calc (g * x * g⁻¹) * a = g * (x * (g⁻¹ * a * g)) * g⁻¹ := by group
        _ = g * ((g⁻¹ * a * g) * x) * g⁻¹ := by rw [h]
        _ = a * (g * x * g⁻¹) := by group
  have heq : GLBConj g (K ⊓ Subgroup.centralizer ({a} : Set X)) =
      K ⊓ Subgroup.centralizer ({a} : Set X) := by
    ext x
    rw [mem_gLBConj, Subgroup.mem_inf, Subgroup.mem_inf, ← hgK x]
    constructor
    · rintro ⟨hx, hxc⟩
      refine ⟨hx, ?_⟩
      have h1 := (hconj x).1 hxc
      have e : g⁻¹ * a * g = (g⁻¹ * a * g * a⁻¹) * a := by group
      rw [e] at h1
      exact (mem_centralizer_mul_iff_of_mem_centralizer hz'' hx).1 h1
    · rintro ⟨hx, hxc⟩
      refine ⟨hx, (hconj x).2 ?_⟩
      have e : g⁻¹ * a * g = (g⁻¹ * a * g * a⁻¹) * a := by group
      rw [e]
      exact (mem_centralizer_mul_iff_of_mem_centralizer hz'' hx).2 hxc
  rwa [heq] at h

end Conj

section Normalization

variable {X : Type} [Group X]

theorem mem_gLAPPrimeCoreOf_iff' (p : ℕ) (L : Subgroup X) (y : X) :
    y ∈ GLAPPrimeCoreOf p L ↔ ∃ h : y ∈ L, (⟨y, h⟩ : ↥L) ∈ GLAPPrimeCore p ↥L := by
  unfold GLAPPrimeCoreOf
  simp [Subgroup.mem_map]

theorem exists_comm_not_mem_core [Finite X] {p : ℕ} (hp : p.Prime) {J : Subgroup X}
    (hq : CFSG.Open.IsQuasisimple ↥J) (hpZ : ¬ p ∣ Nat.card ↥(Subgroup.center ↥J))
    {b : X} (hbJ : b ∈ J) (hb1 : b ≠ 1) (hbp : b ^ p = 1) :
    ∃ y ∈ J, ⁅b, y⁆ ∉ GLAPPrimeCoreOf p J := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  by_contra hcon
  push Not at hcon
  set b' : ↥J := ⟨b, hbJ⟩ with hb'
  have hb'1 : b' ≠ 1 := fun h => hb1 (congrArg Subtype.val h)
  have hb'p : b' ^ p = 1 := Subtype.ext (by simpa using hbp)
  have hord : orderOf b' = p := orderOf_eq_prime hb'p hb'1
  have hpJ : p ∣ Nat.card ↥J := hord ▸ orderOf_dvd_natCard b'
  have hperf : Group.IsPerfect ↥J := Group.isPerfect_def.2 hq.1
  have hO : GLAPPrimeCore p ↥J ≤ Subgroup.center ↥J := by
    rcases i253_normal_le_center_or_top hq (GLAPPrimeCore p ↥J) with h | h
    · exact h
    · exfalso
      have hcop := coprime_card_gLAPPrimeCore_aux p ↥J
      rw [h, Subgroup.card_top] at hcop
      exact hp.one_lt.ne' (Nat.Coprime.eq_one_of_dvd hcop hpJ)
  have hcen : (QuotientGroup.mk b' : ↥J ⧸ Subgroup.center ↥J) ∈
      Subgroup.center (↥J ⧸ Subgroup.center ↥J) := by
    rw [Subgroup.mem_center_iff]
    intro q
    obtain ⟨m, rfl⟩ := QuotientGroup.mk_surjective q
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq]
    have hz : ⁅b', m⁆ ∈ Subgroup.center ↥J := by
      obtain ⟨hmem, hcore⟩ := (mem_gLAPPrimeCoreOf_iff' p J _).1 (hcon (m : X) m.2)
      exact hO hcore
    have e : b' * m = ⁅b', m⁆ * (m * b') := by
      rw [commutatorElement_def]
      group
    have hzc := Subgroup.mem_center_iff.1 hz (m * b')
    have e2 : (m * b')⁻¹ * (b' * m) = ⁅b', m⁆ := by
      rw [e, ← hzc]
      exact inv_mul_cancel_left _ _
    rw [e2]
    exact hz
  rw [Group.IsPerfect.center_quotient_center_eq_bot] at hcen
  have hb'Z : b' ∈ Subgroup.center ↥J :=
    (QuotientGroup.eq_one_iff b').1 (Subgroup.mem_bot.1 hcen)
  set c : ↥(Subgroup.center ↥J) := ⟨b', hb'Z⟩ with hc
  have hc1 : c ≠ 1 := fun h => hb'1 (congrArg Subtype.val h)
  have hcp : c ^ p = 1 := Subtype.ext (by simpa using hb'p)
  exact hpZ (orderOf_eq_prime hcp hc1 ▸ orderOf_dvd_natCard c)

theorem mem_normalizer_of_exists_comm [Finite X] {p : ℕ} (hp : p.Prime) {K B : Subgroup X}
    {a w : X} (hBK : B ≤ Subgroup.normalizer (K : Set X))
    (hw : w ∈ Subgroup.normalizer (K : Set X))
    (hwa : w * a * w⁻¹ * a⁻¹ ∈ Subgroup.centralizer (K : Set X))
    (hwB : ∀ b ∈ B, ⁅w, b⁆ ∈ Subgroup.centralizer (K : Set X))
    (hmove : ∀ J : Subgroup X,
      GLAPComponent p (K ⊓ Subgroup.centralizer ({a} : Set X)) J →
        ∃ b ∈ B, b ∈ J ∧ ∃ y ∈ J, ⁅b, y⁆ ∉ GLAPPrimeCoreOf p J)
    {J : Subgroup X} (hJ : GLAPComponent p (K ⊓ Subgroup.centralizer ({a} : Set X)) J) :
    w ∈ Subgroup.normalizer (J : Set X) := by
  have hJ'c : GLAPComponent p (K ⊓ Subgroup.centralizer ({a} : Set X)) (GLBConj w J) :=
    glaPComponent_gLBConj_of_comm hw hwa hJ
  by_cases hJJ : GLBConj w J = J
  · exact mem_normalizer_iff_gLBConj_eq.2 hJJ
  · exfalso
    obtain ⟨b, hbB, hbJ', y, hyJ', hy⟩ := hmove _ hJ'c
    have hbw : w * b * w⁻¹ ∈ J := mem_gLBConj.1 hbJ'
    have hcomm := commutator_mem_gLAPPrimeCoreOf_of_ne hp hJ'c hJ hJJ hbw hyJ'
    set z : X := ⁅w, b⁆ with hz
    have hzC : z ∈ Subgroup.centralizer (K : Set X) := hwB b hbB
    have hyK : y ∈ K := (hJ'c.1 hyJ').1
    have hbyK : b * y * b⁻¹ ∈ K := (Subgroup.mem_normalizer_iff.1 (hBK hbB) y).1 hyK
    have hzby : z * (b * y * b⁻¹) = (b * y * b⁻¹) * z :=
      (Subgroup.mem_centralizer_iff.1 hzC _ hbyK).symm
    have hc : w * b * w⁻¹ = z * b := by
      rw [hz, commutatorElement_def]
      group
    have e : (w * b * w⁻¹) * y * (w * b * w⁻¹)⁻¹ * y⁻¹ = ⁅b, y⁆ := by
      rw [hc, commutatorElement_def]
      calc z * b * y * (z * b)⁻¹ * y⁻¹ = (z * (b * y * b⁻¹) * z⁻¹) * y⁻¹ := by group
        _ = ((b * y * b⁻¹) * z * z⁻¹) * y⁻¹ := by rw [hzby]
        _ = b * y * b⁻¹ * y⁻¹ := by group
    rw [e] at hcomm
    exact hy hcomm

end Normalization

end CFSG.HardMathSupport.Dickson.Bal207.Glue

end
