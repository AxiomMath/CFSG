module

public import CFSG.Open.GeneratedCore
public import CFSG.LocalAnalysis.SectionRank.SubgroupRank
public import TauCeti.Algebra.Group.Subgroup.Map

public section

namespace CFSG.GroupTheory

open CFSG.Open

variable {H : Type*} [Group H] [Finite H]

theorem mem_of_mem_comap_of_orderOf_dvd_pow {Z : Subgroup H} [Z.Normal]
    (hZc : Z ≤ Subgroup.center H) {q : ℕ} (hq : q.Prime) (hZ : ¬ q ∣ Nat.card Z)
    {Q : Subgroup H} (hQ : IsPGroup q Q) {Rbar : Subgroup (H ⧸ Z)} {R : Subgroup H}
    (hR : R = Q ⊓ Rbar.comap (QuotientGroup.mk' Z))
    (hRmap : R.map (QuotientGroup.mk' Z) = Rbar)
    {s : H} (hs : s ∈ Rbar.comap (QuotientGroup.mk' Z))
    (hsq : ∃ n, orderOf s ∣ q ^ n) : s ∈ R := by
  have hRle : R ≤ Q := by rw [hR]; exact inf_le_left
  obtain ⟨r, hrR, hrs⟩ := Subgroup.mem_map.mp (by rw [hRmap]; exact hs)
  set z : H := r⁻¹ * s with hzdef
  have hzZ : z ∈ Z := by
    have h1 : QuotientGroup.mk' Z z = 1 := by
      rw [hzdef, map_mul, map_inv, hrs, inv_mul_cancel]
    exact (QuotientGroup.eq_one_iff z).mp h1
  have hcomm : Commute r z :=
    Subgroup.mem_center_iff.mp (hZc hzZ) r
  have hcopq : Nat.Coprime (orderOf z) q := by
    have hzo : orderOf z ∣ Nat.card Z := Subgroup.orderOf_dvd_natCard Z hzZ
    have hqZ : Nat.Coprime q (Nat.card Z) := (Nat.Prime.coprime_iff_not_dvd hq).2 hZ
    exact (hqZ.of_dvd_right hzo).symm
  obtain ⟨k, hk⟩ := hQ.exists_orderOf_dvd_pow (⟨r, hRle hrR⟩ : Q)
  have hrpow : orderOf r ∣ q ^ k := by
    rw [Subgroup.orderOf_mk] at hk
    exact hk
  have hcop : Nat.Coprime (orderOf r) (orderOf z) :=
    (hcopq.pow_right k).coprime_dvd_right hrpow |>.symm
  have hs_eq : s = r * z := by rw [hzdef]; group
  have hord : orderOf s = orderOf r * orderOf z := by
    rw [hs_eq]
    exact hcomm.orderOf_mul_eq_mul_orderOf_of_coprime hcop
  obtain ⟨n, hn⟩ := hsq
  have hdiv : orderOf z ∣ q ^ n := by
    refine (dvd_mul_left (orderOf z) (orderOf r)).trans ?_
    rw [← hord]
    exact hn
  have hzone : orderOf z = 1 :=
    Nat.eq_one_of_dvd_coprimes (hcopq.pow_right n) dvd_rfl hdiv
  have hz1 : z = 1 := orderOf_eq_one_iff.mp hzone
  rw [hs_eq, hz1, mul_one]
  exact hrR

theorem pRank_comap_inf_eq {Z : Subgroup H} [Z.Normal] {q : ℕ} (hq : q.Prime)
    {Q : Subgroup H} {Rbar : Subgroup (H ⧸ Z)} {R : Subgroup H}
    (hR : R = Q ⊓ Rbar.comap (QuotientGroup.mk' Z))
    (hRbarQ : Rbar ≤ Q.map (QuotientGroup.mk' Z)) (hdisj : Disjoint Q Z) :
    CFSG.Open.pRank q R = CFSG.Open.pRank q Rbar := by
  have hRmap : R.map (QuotientGroup.mk' Z) = Rbar := by
    rw [hR, Subgroup.map_inf_comap Q Rbar (QuotientGroup.mk' Z), inf_eq_right.2 hRbarQ]
  have hRle : R ≤ Q := by rw [hR]; exact inf_le_left
  let φ : R →* Rbar :=
    (QuotientGroup.mk' Z).comp R.subtype |>.codRestrict Rbar fun r => by
      have h : QuotientGroup.mk' Z (r : H) ∈ R.map (QuotientGroup.mk' Z) :=
        Subgroup.mem_map_of_mem _ r.2
      rwa [hRmap] at h
  have hφinj : Function.Injective φ := by
    intro a b hab
    have h1 : QuotientGroup.mk' Z ((a : H) * (b : H)⁻¹) = 1 := by
      have h2 : QuotientGroup.mk' Z (a : H) = QuotientGroup.mk' Z (b : H) :=
        congrArg Subtype.val hab
      rw [map_mul, map_inv, h2, mul_inv_cancel]
    have hmemZ : (a : H) * (b : H)⁻¹ ∈ Z := (QuotientGroup.eq_one_iff _).mp h1
    have hmemQ : (a : H) * (b : H)⁻¹ ∈ Q :=
      Q.mul_mem (hRle a.2) (Q.inv_mem (hRle b.2))
    have hbot : (a : H) * (b : H)⁻¹ ∈ (⊥ : Subgroup H) := by
      rw [← hdisj.eq_bot]
      exact ⟨hmemQ, hmemZ⟩
    have h2 : (a : H) * (b : H)⁻¹ = 1 := Subgroup.mem_bot.mp hbot
    exact Subtype.ext (mul_inv_eq_one.mp h2)
  have hφsurj : Function.Surjective φ := by
    intro y
    have hy : (y : H ⧸ Z) ∈ R.map (QuotientGroup.mk' Z) := by rw [hRmap]; exact y.2
    obtain ⟨r, hrR, hr⟩ := Subgroup.mem_map.mp hy
    exact ⟨⟨r, hrR⟩, Subtype.ext hr⟩
  let e : R ≃* Rbar := MulEquiv.ofBijective φ ⟨hφinj, hφsurj⟩
  calc CFSG.Open.pRank q R = CFSG.Open.pRank q (⊤ : Subgroup R) :=
        CFSG.SectionRank.pRank_eq_pRank_top_subgroup R
    _ = CFSG.Open.pRank q (⊤ : Subgroup Rbar) :=
        CFSG.SectionRank.pRank_top_eq_of_mulEquiv hq.one_lt e
    _ = CFSG.Open.pRank q Rbar :=
        (CFSG.SectionRank.pRank_eq_pRank_top_subgroup Rbar).symm

theorem mem_normalizer_of_mem_normalizer_comap {Z : Subgroup H} [Z.Normal]
    (hZc : Z ≤ Subgroup.center H) {q : ℕ} (hq : q.Prime) (hZ : ¬ q ∣ Nat.card Z)
    {Q : Subgroup H} (hQ : IsPGroup q Q) {Rbar : Subgroup (H ⧸ Z)} {R : Subgroup H}
    (hR : R = Q ⊓ Rbar.comap (QuotientGroup.mk' Z))
    (hRbarQ : Rbar ≤ Q.map (QuotientGroup.mk' Z)) {x : H}
    (hx : QuotientGroup.mk' Z x ∈ Subgroup.normalizer (Rbar : Set (H ⧸ Z))) :
    x ∈ Subgroup.normalizer (R : Set H) := by
  have hRmap : R.map (QuotientGroup.mk' Z) = Rbar := by
    rw [hR, Subgroup.map_inf_comap Q Rbar (QuotientGroup.mk' Z), inf_eq_right.2 hRbarQ]
  have himage : R.map (MulAut.conj x).toMonoidHom ≤ R := by
    intro y hy
    obtain ⟨r, hrR, rfl⟩ := Subgroup.mem_map.mp hy
    have hrR' : r ∈ Q ⊓ Rbar.comap (QuotientGroup.mk' Z) := by rwa [hR] at hrR
    have hrQ : r ∈ Q := (Subgroup.mem_inf.mp hrR').1
    have hrbar : QuotientGroup.mk' Z r ∈ Rbar := (Subgroup.mem_inf.mp hrR').2
    have hybar : QuotientGroup.mk' Z ((MulAut.conj x) r) ∈ Rbar := by
      have h := (Subgroup.mem_normalizer_iff.mp hx (QuotientGroup.mk' Z r)).1 hrbar
      simpa [MulAut.conj_apply, map_mul, map_inv] using h
    have hyq : ∃ n, orderOf ((MulAut.conj x) r) ∣ q ^ n := by
      obtain ⟨n, hn⟩ := hQ.exists_orderOf_dvd_pow (⟨r, hrQ⟩ : Q)
      refine ⟨n, ?_⟩
      rw [MulEquiv.orderOf_eq]
      rw [Subgroup.orderOf_mk] at hn
      exact hn
    exact mem_of_mem_comap_of_orderOf_dvd_pow hZc hq hZ hQ hR hRmap hybar hyq
  have hcard : Nat.card (R.map (MulAut.conj x).toMonoidHom) = Nat.card R :=
    Subgroup.card_map_of_injective (f := (MulAut.conj x).toMonoidHom) (MulAut.conj x).injective
  have heq : R.map (MulAut.conj x).toMonoidHom = R :=
    Subgroup.eq_of_le_of_card_ge himage (by rw [hcard])
  exact Subgroup.mem_normalizer_iff_map_conj_eq.mpr heq

theorem glbCore_map_le_of_central_quotient {Z : Subgroup H} [Z.Normal]
    (hZc : Z ≤ Subgroup.center H) {q k : ℕ} (hq : q.Prime) (hZ : ¬ q ∣ Nat.card Z)
    {Q : Subgroup H} (hQ : IsPGroup q Q) :
    GLBCore q k (Q.map (QuotientGroup.mk' Z)) ≤
      (GLBCore q k Q).map (QuotientGroup.mk' Z) := by
  refine sSup_le ?_
  rintro N ⟨Rbar, hRbarQ, hRk, rfl⟩
  intro y hy
  obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective Z y
  set R : Subgroup H := Q ⊓ Rbar.comap (QuotientGroup.mk' Z) with hR
  have hxN := mem_normalizer_of_mem_normalizer_comap hZc hq hZ hQ hR hRbarQ hy
  haveI : Fact q.Prime := ⟨hq⟩
  have hdisj : Disjoint Q Z := by
    obtain ⟨n, hn⟩ := hQ.exists_card_eq
    refine Subgroup.disjoint_of_coprime_natCard ?_
    rw [hn]
    exact Nat.Coprime.pow_left n ((Nat.Prime.coprime_iff_not_dvd hq).2 hZ)
  have hRk' : k ≤ CFSG.Open.pRank q R := by
    rw [pRank_comap_inf_eq hq hR hRbarQ hdisj]
    exact hRk
  have hmem : Subgroup.normalizer (R : Set H) ∈
      {N : Subgroup H | ∃ Q' : Subgroup H, Q' ≤ Q ∧ k ≤ CFSG.Open.pRank q Q' ∧
        N = Subgroup.normalizer (Q' : Set H)} := ⟨R, inf_le_left, hRk', rfl⟩
  exact Subgroup.mem_map_of_mem _ (Subgroup.mem_sSup_of_mem hmem hxN)

theorem glbCore_eq_top_of_central_quotient {Z : Subgroup H} [Z.Normal]
    (hZc : Z ≤ Subgroup.center H) {q k : ℕ} (hq : q.Prime) (hZ : ¬ q ∣ Nat.card Z)
    {Q : Subgroup H} (hQ : IsPGroup q Q) (hk : k ≤ CFSG.Open.pRank q Q)
    (hcore : GLBCore q k (Q.map (QuotientGroup.mk' Z)) = ⊤) :
    GLBCore q k Q = ⊤ := by
  have hmap := glbCore_map_le_of_central_quotient (k := k) hZc hq hZ hQ
  have hmapTop : (GLBCore q k Q).map (QuotientGroup.mk' Z) = ⊤ := by
    refine eq_top_iff.2 ?_
    rw [← hcore]
    exact hmap
  have hNQ : Subgroup.normalizer (Q : Set H) ≤ GLBCore q k Q :=
    le_sSup ⟨Q, le_rfl, hk, rfl⟩
  have hZN : Z ≤ Subgroup.normalizer (Q : Set H) :=
    hZc.trans (Subgroup.center_le_normalizer (Q : Set H))
  have hZΓ : Z ≤ GLBCore q k Q := hZN.trans hNQ
  refine eq_top_iff.2 ?_
  intro x _
  have hxmap : QuotientGroup.mk' Z x ∈ (GLBCore q k Q).map (QuotientGroup.mk' Z) := by
    rw [hmapTop]
    exact Subgroup.mem_top _
  obtain ⟨z, hzΓ, hzx⟩ := Subgroup.mem_map.mp hxmap
  have hzx' : z⁻¹ * x ∈ Z := by
    have h1 : QuotientGroup.mk' Z (z⁻¹ * x) = 1 := by
      rw [map_mul, map_inv, hzx, inv_mul_cancel]
    exact (QuotientGroup.eq_one_iff _).mp h1
  rw [show x = z * (z⁻¹ * x) by group]
  exact mul_mem hzΓ (hZΓ hzx')

end CFSG.GroupTheory
