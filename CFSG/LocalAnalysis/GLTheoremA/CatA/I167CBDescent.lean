module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.I167CDefs
public import CFSG.GroupTheory.PLayer.CenterQuotientAction

public section

namespace CFSG.LocalAnalysis.GLTheoremA.I167

open CFSG.Open
open scoped commutatorElement

theorem exists_pow_eq_one_of_pow_mem_central {G : Type*} [Group G] {p : ℕ} (hp : p.Prime)
    {Z : Subgroup G} (hZ : Z ≤ Subgroup.center G) (hZp : ¬ p ∣ Nat.card Z) {y : G} (hy : y ^ p ∈ Z) :
    ∃ y' : G, y' ^ p = 1 ∧ y⁻¹ * y' ∈ Z := by
  let z : G := y ^ p
  let t : ℕ := Nat.card Z
  have hzZ : z ∈ Z := hy
  have hzcenter : z ∈ Subgroup.center G := hZ hzZ
  have hcop : Nat.Coprime p t := (hp.coprime_iff_not_dvd).2 hZp
  obtain ⟨a, b, hab⟩ := Nat.Coprime.isCoprime hcop
  have hcomm : Commute y z := (Subgroup.mem_center_iff.1 hzcenter y)
  have hcommw : Commute y (z ^ (-a)) := hcomm.zpow_right (-a)
  have hw : (z ^ (-a)) ^ p = z ^ ((-a) * (p : ℤ)) := by
    rw [← zpow_natCast, zpow_mul]
  have hzpow : z * z ^ ((-a) * (p : ℤ)) = z ^ ((1 : ℤ) - a * (p : ℤ)) := by
    calc z * z ^ ((-a) * (p : ℤ))
        = z ^ (1 : ℤ) * z ^ ((-a) * (p : ℤ)) := by rw [zpow_one]
      _ = z ^ ((1 : ℤ) + (-a) * (p : ℤ)) := by rw [← zpow_add]
      _ = z ^ ((1 : ℤ) - a * (p : ℤ)) := by congr 1; ring
  have hExp : (1 : ℤ) - a * (p : ℤ) = (b : ℤ) * (t : ℤ) := by
    linarith
  have hzt : z ^ t = 1 := by
    have h := congrArg (fun w : ↥Z => (w : G))
      (pow_card_eq_one' (G := ↥Z) (x := ⟨z, hzZ⟩))
    simpa only [t, SubmonoidClass.coe_pow, OneMemClass.coe_one] using h
  have hzt' : z ^ (t : ℤ) = 1 := by simpa using hzt
  have hzbt : z ^ ((b : ℤ) * (t : ℤ)) = 1 := by
    rw [mul_comm, zpow_mul, hzt', one_zpow]
  refine ⟨y * z ^ (-a), ?_, ?_⟩
  · calc (y * z ^ (-a)) ^ p
        = y ^ p * (z ^ (-a)) ^ p := hcommw.mul_pow p
      _ = z * (z ^ (-a)) ^ p := by rw [show y ^ p = z from rfl]
      _ = z * z ^ ((-a) * (p : ℤ)) := by rw [hw]
      _ = z ^ ((1 : ℤ) - a * (p : ℤ)) := hzpow
      _ = z ^ ((b : ℤ) * (t : ℤ)) := by rw [hExp]
      _ = 1 := hzbt
  · rw [show y⁻¹ * (y * z ^ (-a)) = z ^ (-a) by group]
    exact Subgroup.zpow_mem Z hzZ (-a)

theorem eq_of_pow_eq_one_of_inv_mul_mem_central {G : Type*} [Group G] {p : ℕ} (hp : p.Prime)
    {Z : Subgroup G} (hZ : Z ≤ Subgroup.center G) (hZp : ¬ p ∣ Nat.card Z) {a b : G}
    (ha : a ^ p = 1) (hb : b ^ p = 1) (hab : a⁻¹ * b ∈ Z) : a = b := by
  let z : G := a⁻¹ * b
  have hzZ : z ∈ Z := hab
  have hzcenter : z ∈ Subgroup.center G := hZ hzZ
  have hcomm : Commute a z := Subgroup.mem_center_iff.1 hzcenter a
  have hb_eq : b = a * z := by
    show b = a * (a⁻¹ * b)
    group
  have hzp : z ^ p = 1 := by
    have h := hcomm.mul_pow p
    rw [← hb_eq, hb, ha, one_mul] at h
    exact h.symm
  have hzt : z ^ Nat.card Z = 1 := by
    have h := congrArg (fun w : ↥Z => (w : G))
      (pow_card_eq_one' (G := ↥Z) (x := ⟨z, hzZ⟩))
    simpa only [SubmonoidClass.coe_pow, OneMemClass.coe_one] using h
  have hcop : Nat.Coprime p (Nat.card Z) := (hp.coprime_iff_not_dvd).2 hZp
  have hgcd1 : Nat.gcd p (Nat.card Z) = 1 := by
    simpa [Nat.Coprime] using hcop
  have hz1 : z = 1 := by
    have h := (pow_gcd_eq_one (a := z) (m := p) (n := Nat.card Z)).2 ⟨hzp, hzt⟩
    simpa [hgcd1] using h
  rw [hz1, mul_one] at hb_eq
  exact hb_eq.symm

theorem mem_centralizer_of_rho_fixes_lift {Y : Type} [Group Y] {p : ℕ} (hp : p.Prime) {X B : Subgroup Y}
    (hBN : B ≤ Subgroup.normalizer (X : Set Y)) (hZ : ¬ p ∣ Nat.card (Subgroup.center ↥X)) {y : ↥X}
    (hy : y ^ p = 1)
    (hfix : ∀ b : ↥B, normalizerToCenterQuotientAut X B hBN b (QuotientGroup.mk y) = QuotientGroup.mk y) :
    (y : Y) ∈ Subgroup.centralizer (B : Set Y) := by
  rw [Subgroup.mem_centralizer_iff]
  intro b hb
  let bb : ↥B := ⟨b, hb⟩
  let σ : MulAut ↥X := normalizerConjAutOfMem X B hBN bb
  have hq : (QuotientGroup.mk (σ y) : ↥X ⧸ Subgroup.center ↥X) = QuotientGroup.mk y := by
    have h := normalizerConjAutOfMem_comp_mk X B hBN bb y
    simp only [QuotientGroup.mk'_apply] at h
    rw [hfix bb] at h
    simpa [σ] using h
  have hmem : y⁻¹ * σ y ∈ Subgroup.center ↥X := QuotientGroup.eq.1 hq.symm
  have hσp : (σ y) ^ p = 1 := by
    rw [← map_pow, hy, map_one]
  have hσeq : y = σ y :=
    eq_of_pow_eq_one_of_inv_mul_mem_central hp le_rfl hZ hy hσp hmem
  have h2 : b * (y : Y) * b⁻¹ = (y : Y) := by
    have hval := congrArg (fun w : ↥X => (w : Y)) hσeq
    have hσval : ((σ y : ↥X) : Y) = b * (y : Y) * b⁻¹ := by
      simp [σ, bb, normalizerConjAutOfMem, Subgroup.normalizerMonoidHom_apply_apply_coe]
    rw [hσval] at hval
    exact hval.symm
  calc b * (y : Y) = (b * (y : Y) * b⁻¹) * b := by group
    _ = (y : Y) * b := by rw [h2]

theorem rho_apply_of_mem {Y : Type} [Group Y] {X B : Subgroup Y}
    (hBN : B ≤ Subgroup.normalizer (X : Set Y)) {y : ↥X} (hyB : (y : Y) ∈ B) :
    normalizerToCenterQuotientAut X B hBN ⟨(y : Y), hyB⟩ =
      MulAut.conj (QuotientGroup.mk y : ↥X ⧸ Subgroup.center ↥X) := by
  apply MulEquiv.ext
  intro u
  induction u using QuotientGroup.induction_on with
  | H u =>
    change QuotientGroup.mk (normalizerConjAutOfMem X B hBN ⟨(y : Y), hyB⟩ u) =
      MulAut.conj (QuotientGroup.mk y) (QuotientGroup.mk u)
    rw [MulAut.conj_apply, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_inv,
      ← QuotientGroup.mk_mul]
    apply congrArg QuotientGroup.mk
    apply Subtype.ext
    simp only [normalizerConjAutOfMem, Subgroup.normalizerMonoidHom_apply_apply_coe,
      Subgroup.coe_inclusion, Subtype.coe_mk, Subgroup.coe_mul, Subgroup.coe_inv]

theorem scpS_of_sc {Y : Type} [Group Y] {p : ℕ} (hp : p.Prime) {X B : Subgroup Y}
    (hBN : B ≤ Subgroup.normalizer (X : Set Y)) (hZ : ¬ p ∣ Nat.card (Subgroup.center ↥X))
    (hSC : ∀ g ∈ X ⊔ B, g ∈ Subgroup.centralizer (B : Set Y) → orderOf g = p → g ∈ B) :
    ScpS p (↥X ⧸ Subgroup.center ↥X) (normalizerToCenterQuotientAut X B hBN).range := by
  intro s hfix hs
  obtain ⟨y0, rfl⟩ := QuotientGroup.mk_surjective s
  have hy0 : y0 ^ p ∈ Subgroup.center ↥X := by
    rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_pow]
    exact hs
  obtain ⟨y, hyp, hyz⟩ := exists_pow_eq_one_of_pow_mem_central hp le_rfl hZ hy0
  have hmk : (QuotientGroup.mk y0 : ↥X ⧸ Subgroup.center ↥X) = QuotientGroup.mk y :=
    QuotientGroup.eq.2 hyz
  rw [hmk] at hfix ⊢
  have hcent : (y : Y) ∈ Subgroup.centralizer (B : Set Y) :=
    mem_centralizer_of_rho_fixes_lift hp hBN hZ hyp (fun b => hfix _ ⟨b, rfl⟩)
  by_cases hy1 : y = 1
  · rw [hy1, QuotientGroup.mk_one, map_one]
    exact one_mem _
  · have hyY : (y : Y) ≠ 1 := fun h => hy1 (Subtype.ext h)
    haveI := Fact.mk hp
    have hord : orderOf (y : Y) = p := orderOf_eq_prime (by rw [← Subgroup.coe_pow, hyp]; rfl) hyY
    have hyB : (y : Y) ∈ B := hSC y (Subgroup.mem_sup_left y.2) hcent hord
    exact ⟨⟨y, hyB⟩, rho_apply_of_mem hBN hyB⟩

private theorem eq_self_of_perfect_of_inv_mul_mem_center_aux1 {G : Type*} [Group G] {z₁ z₂ : G}
    (h₁ : z₁ ∈ Subgroup.center G) (h₂ : z₂ ∈ Subgroup.center G) (a b : G) :
    ⁅a * z₁, b * z₂⁆ = ⁅a, b⁆ := by
  rw [commutatorElement_mul_left_eq_conj_mul]
  have e₁ : ⁅z₁, b * z₂⁆ = 1 :=
    commutatorElement_eq_one_iff_mul_comm.mpr (Subgroup.mem_center_iff.mp h₁ (b * z₂)).symm
  rw [e₁, commutatorElement_mul_right_eq_mul_conj]
  have e₂ : ⁅a, z₂⁆ = 1 :=
    commutatorElement_eq_one_iff_mul_comm.mpr (Subgroup.mem_center_iff.mp h₂ a)
  rw [e₂]
  group

theorem eq_self_of_perfect_of_inv_mul_mem_center {G : Type*} [Group G] (σ : G →* G) {J : Subgroup G}
    (hJ : ⁅J, J⁆ = J) (h : ∀ j ∈ J, j⁻¹ * σ j ∈ Subgroup.center G) : ∀ j ∈ J, σ j = j := by
  have hle : ⁅J, J⁆ ≤ J ⊓ MonoidHom.eqLocus σ (MonoidHom.id G) := by
    rw [Subgroup.commutator_le]
    intro a ha b hb
    refine Subgroup.mem_inf.2 ⟨?_, ?_⟩
    · rw [commutatorElement_def]
      exact J.mul_mem (J.mul_mem (J.mul_mem ha hb) (J.inv_mem ha)) (J.inv_mem hb)
    · have hza : a⁻¹ * σ a ∈ Subgroup.center G := h a ha
      have hzb : b⁻¹ * σ b ∈ Subgroup.center G := h b hb
      have hσa : σ a = a * (a⁻¹ * σ a) := by group
      have hσb : σ b = b * (b⁻¹ * σ b) := by group
      show σ ⁅a, b⁆ = ⁅a, b⁆
      rw [map_commutatorElement, hσa, hσb]
      exact eq_self_of_perfect_of_inv_mul_mem_center_aux1 hza hzb a b
  have hJle : J ≤ J ⊓ MonoidHom.eqLocus σ (MonoidHom.id G) := hJ.ge.trans hle
  intro j hj
  exact (Subgroup.mem_inf.1 (hJle hj)).2

theorem mem_centralizer_of_rho_fix {Y : Type} [Group Y] {X B : Subgroup Y}
    (hBN : B ≤ Subgroup.normalizer (X : Set Y)) {J : Subgroup Y} (hJX : J ≤ X) (hJ : ⁅J, J⁆ = J) (b : ↥B)
    (hfix : ∀ j ∈ (J.subgroupOf X).map (QuotientGroup.mk' (Subgroup.center ↥X)),
      normalizerToCenterQuotientAut X B hBN b j = j) :
    (b : Y) ∈ Subgroup.centralizer (J : Set Y) := by
  have hperf : ⁅J.subgroupOf X, J.subgroupOf X⁆ = J.subgroupOf X := by
    rw [← CFSG.LocalAnalysis.GLTheoremB.subgroupOf_commutator hJX hJX, hJ]
  have key := eq_self_of_perfect_of_inv_mul_mem_center
    (normalizerConjAutOfMem X B hBN b).toMonoidHom hperf (by
      intro j hj
      have h1 := hfix (QuotientGroup.mk' _ j) ⟨j, hj, rfl⟩
      rw [← normalizerConjAutOfMem_comp_mk] at h1
      exact QuotientGroup.eq.1 h1.symm)
  rw [Subgroup.mem_centralizer_iff]
  intro g hg
  have h2 := congrArg Subtype.val (key ⟨g, hJX hg⟩ (Subgroup.mem_subgroupOf.2 hg))
  have h3 : (b : Y) * g * (b : Y)⁻¹ = g := by
    simpa [normalizerConjAutOfMem, Subgroup.normalizerMonoidHom_apply_apply_coe] using h2
  calc g * (b : Y) = ((b : Y) * g * (b : Y)⁻¹) * (b : Y) := by rw [h3]
    _ = (b : Y) * g := by group

theorem rho_mem_zpowers_of_mem_sup {Y : Type} [Group Y] {X B : Subgroup Y} (hX : Group.IsPerfect ↥X)
    (hBN : B ≤ Subgroup.normalizer (X : Set Y)) {x : Y} (hxB : x ∈ B) {d : Y} (hdB : d ∈ B)
    (hd : d ∈ (B ⊓ Subgroup.centralizer (X : Set Y)) ⊔ Subgroup.zpowers x) :
    normalizerToCenterQuotientAut X B hBN ⟨d, hdB⟩ ∈
      Subgroup.zpowers (normalizerToCenterQuotientAut X B hBN ⟨x, hxB⟩) := by
  let ρ := normalizerToCenterQuotientAut X B hBN
  let T : Subgroup Y := ((Subgroup.zpowers (ρ ⟨x, hxB⟩)).comap ρ).map B.subtype
  have hle : (B ⊓ Subgroup.centralizer (X : Set Y)) ⊔ Subgroup.zpowers x ≤ T := by
    refine sup_le ?_ ?_
    · intro c hc
      rw [Subgroup.mem_map]
      refine ⟨⟨c, hc.1⟩, ?_, rfl⟩
      rw [Subgroup.mem_comap]
      rw [(normalizerToCenterQuotientAut_eq_one_iff hX hBN ⟨c, hc.1⟩).2 hc]
      exact Subgroup.one_mem _
    · intro y hy
      rw [Subgroup.mem_map]
      have hyB : y ∈ B := (Subgroup.zpowers_le.2 hxB) hy
      refine ⟨⟨y, hyB⟩, ?_, rfl⟩
      rw [Subgroup.mem_comap]
      rw [Subgroup.mem_zpowers_iff] at hy ⊢
      obtain ⟨k, hk⟩ := hy
      refine ⟨k, ?_⟩
      rw [← map_zpow]
      congr 1
      exact Subtype.ext hk
  have hdT : d ∈ T := hle hd
  rw [Subgroup.mem_map] at hdT
  obtain ⟨b, hb, hbd⟩ := hdT
  rw [Subgroup.mem_comap] at hb
  have hb_eq : b = ⟨d, hdB⟩ := Subtype.ext hbd
  rw [← hb_eq]
  exact hb

theorem centJ_descent {Y : Type} [Group Y] {X B : Subgroup Y} (hX : Group.IsPerfect ↥X)
    (hBN : B ≤ Subgroup.normalizer (X : Set Y)) {D J : Subgroup Y} {x : Y} (hxB : x ∈ B)
    (hJX : J ≤ X) (hJ : ⁅J, J⁆ = J) (hDJ : D = B ⊓ Subgroup.centralizer (J : Set Y))
    (hDx : D = (B ⊓ Subgroup.centralizer (X : Set Y)) ⊔ Subgroup.zpowers x) :
    CentJ (normalizerToCenterQuotientAut X B hBN).range
      (normalizerToCenterQuotientAut X B hBN ⟨x, hxB⟩)
      ((J.subgroupOf X).map (QuotientGroup.mk' (Subgroup.center ↥X))) := by
  rintro _ ⟨b, rfl⟩ hfix
  have hbJ : (b : Y) ∈ Subgroup.centralizer (J : Set Y) := mem_centralizer_of_rho_fix hBN hJX hJ b hfix
  have hbD : (b : Y) ∈ D := by
    rw [hDJ]
    exact ⟨b.2, hbJ⟩
  rw [hDx] at hbD
  exact rho_mem_zpowers_of_mem_sup hX hBN hxB b.2 hbD

theorem orderOf_rho_eq {Y : Type} [Group Y] {p : ℕ} (hp : p.Prime) {X B : Subgroup Y}
    (hX : Group.IsPerfect ↥X) (hBN : B ≤ Subgroup.normalizer (X : Set Y)) {x : Y} (hxB : x ∈ B)
    (hxp : x ^ p = 1) (hxX : x ∉ Subgroup.centralizer (X : Set Y)) :
    orderOf (normalizerToCenterQuotientAut X B hBN ⟨x, hxB⟩) = p := by
  haveI := Fact.mk hp
  apply orderOf_eq_prime
  · rw [← map_pow]
    have : (⟨x, hxB⟩ : ↥B) ^ p = 1 := Subtype.ext hxp
    rw [this, map_one]
  · intro h
    exact hxX ((normalizerToCenterQuotientAut_eq_one_iff hX hBN ⟨x, hxB⟩).1 h).2

theorem isElemAbelian_rho_range {Y : Type} [Group Y] {p : ℕ} {X B : Subgroup Y}
    (hBN : B ≤ Subgroup.normalizer (X : Set Y)) (hB : IsElemAbelian p B) :
    IsElemAbelian p (normalizerToCenterQuotientAut X B hBN).range := by
  haveI := hB.1
  refine ⟨⟨⟨fun a b => ?_⟩⟩, ?_⟩
  · obtain ⟨a, ha⟩ := a
    obtain ⟨b, hb⟩ := b
    obtain ⟨a', rfl⟩ := ha
    obtain ⟨b', rfl⟩ := hb
    apply Subtype.ext
    simp only [Subgroup.coe_mul]
    rw [← map_mul, ← map_mul, (IsMulCommutative.is_comm (M := ↥B)).comm a' b']
  · rintro _ ⟨b, rfl⟩
    rw [← map_pow]
    have : b ^ p = 1 := Subtype.ext (hB.2 b b.2)
    rw [this, map_one]

end CFSG.LocalAnalysis.GLTheoremA.I167

end
