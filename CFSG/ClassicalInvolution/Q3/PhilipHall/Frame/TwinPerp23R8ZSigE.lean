module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23R8ZSigIdx
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23R8ZTwoKF
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TightRefute
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinConnTransportLift

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23.ZTwo

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
  CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDisc CFSG.ClassicalInvolution.Uniform
  CFSG.ClassicalInvolution.Q3.Q3NL CFSG.ClassicalInvolution.Q3.TC.Thin
  CFSG.ClassicalInvolution.Q3.AE

section Omega

variable {n : ℕ} {Y : Type} [Group Y] [Finite Y] {R : Subgroup Y} {S : Sylow 2 R} {t : Y}
  {K' W : Subgroup Y} {u e g : Y}

theorem sq_eq_one_of_mem_ker {Q : Type} [Group Q] [Finite Q] {Φ : Set (Subgroup Q)}
    (D : AECover Q Φ) {κ : Q} (hκ : κ ∈ D.φ.ker) : κ ^ 2 = 1 := by
  have h1 := Subgroup.orderOf_dvd_natCard D.φ.ker hκ
  have h2 := D.ker_card
  have h3 : 0 < Nat.card D.φ.ker := Nat.card_pos
  have h4 : orderOf κ ∣ 2 := by
    rcases (show Nat.card D.φ.ker = 1 ∨ Nat.card D.φ.ker = 2 by omega) with h | h
    · rw [h] at h1; exact h1.trans (one_dvd _)
    · rw [h] at h1; exact h1
  exact orderOf_dvd_iff_pow_eq_one.mp h4

theorem exists_omega (hc : P23Cfg n Y R S t K' W u e g)
    (hAE : SecAE R e 6) :
    ∃ ω : Y, ω ∈ rLayer (Om R) e ∧ ω * t = t * ω ∧ IsPGroup 3 (Subgroup.zpowers ω) ∧
      ∃ k ∈ tightCore R, ω * k ≠ k * ω := by
  classical
  obtain ⟨D⟩ := exists_cover hc hAE
  obtain ⟨β, hβ, b₀, hlab, -, hzb, -, -, -⟩ := twin_labels hc D
  have hE := t_e_mem_rLayer hc
  have htC : t ∈ Subgroup.centralizer ({e} : Set Y) :=
    Subgroup.mem_centralizer_singleton_iff.mpr (e_comm_t hc).symm
  have ht2 : t * t = 1 :=
    (Inner.isUniqueInvolution_core (CoreData.of_S hc.std.perp.core).datum).sq
  set ι := emb β hβ with hι
  set a : AEQ 6 := mkQ 6 (yOf ι) with ha
  have ha3 : a ^ 3 = 1 := by
    have : a ^ 3 = mkQ 6 (yOf ι * yOf ι * yOf ι) := by
      simp only [ha, map_mul, pow_succ, pow_zero, one_mul]
    rw [this, yOf_pow_three, map_one]
  have haz : a * zBar β hβ = zBar β hβ * a := by
    have : zBar β hβ = mkQ 6 (zOf ι) := rfl
    rw [this, ha, ← map_mul, ← map_mul, yOf_comm_zOf]
  have hamove : ∃ x ∈ memBar β hβ b₀, a * x ≠ x * a := by
    cases b₀
    · obtain ⟨x, hx, hne⟩ := yOf_not_comm_memKStar ι
      refine ⟨mkQ 6 x, ⟨x, hx, rfl⟩, fun h => hne ?_⟩
      exact comm_of_mkQ_comm_of_supportedOn (by norm_num) (yOf_supportedOn ι)
        (supportedOn_of_mem_memKStar ι hx) h
    · obtain ⟨x, hx, hne⟩ := yOf_not_comm_memK ι
      refine ⟨mkQ 6 x, ⟨x, hx, rfl⟩, fun h => hne ?_⟩
      exact comm_of_mkQ_comm_of_supportedOn (by norm_num) (yOf_supportedOn ι)
        (supportedOn_of_mem_memK ι hx) h
  obtain ⟨q₀, hq₀⟩ : ∃ q₀ : SecQ R e, D.φ q₀ = a := by
    have : a ∈ D.φ.range := by
      rw [D.range_eq]
      exact ⟨yOf ι, yOf_mem_aeSub ι, rfl⟩
    exact this
  obtain ⟨q, hq⟩ : ∃ q : SecQ R e, q = q₀ ^ 4 := ⟨_, rfl⟩
  have hq₀3 : q₀ ^ 3 ∈ D.φ.ker := by
    rw [MonoidHom.mem_ker, map_pow, hq₀, ha3]
  have hq3 : q ^ 3 = 1 := by
    have h2 := sq_eq_one_of_mem_ker D hq₀3
    calc q ^ 3 = ((q₀ ^ 3) ^ 2) ^ 2 := by rw [hq]; group
      _ = 1 := by rw [h2, one_pow]
  have hφq : D.φ q = a := by
    rw [hq, map_pow, hq₀, show (4 : ℕ) = 3 + 1 by norm_num, pow_add, ha3, one_mul, pow_one]
  have hqt : q * tbar hc = tbar hc * q := by
    obtain ⟨κ', hκ'⟩ : ∃ κ' : SecQ R e, κ' = q * tbar hc * q⁻¹ * (tbar hc)⁻¹ := ⟨_, rfl⟩
    have hκ'ker : κ' ∈ D.φ.ker := by
      rw [MonoidHom.mem_ker, hκ']
      simp only [map_mul, map_inv, hφq, hzb]
      rw [haz]
      group
    have hκ'2 := sq_eq_one_of_mem_ker D hκ'ker
    have hcen := Subgroup.mem_center_iff.mp (D.ker_le hκ'ker)
    have h1 : q * tbar hc * q⁻¹ = κ' * tbar hc := by rw [hκ']; group
    have h3 : q ^ 3 * tbar hc * (q ^ 3)⁻¹ = κ' ^ 3 * tbar hc := by
      calc q ^ 3 * tbar hc * (q ^ 3)⁻¹
          = q * (q * (q * tbar hc * q⁻¹) * q⁻¹) * q⁻¹ := by rw [pow_three]; group
        _ = q * (q * (κ' * tbar hc) * q⁻¹) * q⁻¹ := by rw [h1]
        _ = q * ((q * κ' * q⁻¹) * (q * tbar hc * q⁻¹)) * q⁻¹ := by group
        _ = q * (κ' * (κ' * tbar hc)) * q⁻¹ := by
          rw [show q * κ' * q⁻¹ = κ' by rw [hcen q]; group, h1]
        _ = (q * κ' * q⁻¹) * ((q * κ' * q⁻¹) * (q * tbar hc * q⁻¹)) := by group
        _ = κ' * (κ' * (κ' * tbar hc)) := by
          rw [show q * κ' * q⁻¹ = κ' by rw [hcen q]; group, h1]
        _ = κ' ^ 3 * tbar hc := by rw [pow_three]; group
    rw [hq3] at h3
    have h4 : κ' ^ 3 = 1 := by
      have : tbar hc = κ' ^ 3 * tbar hc := by simpa using h3
      exact (mul_eq_right.mp this.symm)
    have h5 : κ' = 1 := by
      have h6 : κ' ^ 3 = κ' ^ 2 * κ' := pow_succ κ' 2
      rw [h6, hκ'2, one_mul] at h4
      exact h4
    have h6 : q * tbar hc * q⁻¹ = tbar hc := by rw [h1, h5, one_mul]
    calc q * tbar hc = (q * tbar hc * q⁻¹) * q := by group
      _ = tbar hc * q := by rw [h6]
  have hqσ : TwinExitPf6.secAut (Om R) e (hΩ_of hc) (hc2e_of hc) ⟨t, htC⟩ q = q := by
    rw [secAut_t hc htC, ← hqt]
    group
  obtain ⟨ã, hãC, hãq⟩ := exists_lift_fix hc htC ht2 hqσ
  have hN : orderOf (ã : Y) ≠ 0 := (orderOf_pos _).ne'
  obtain ⟨a', r, hr3, hNr⟩ := Nat.exists_eq_pow_mul_and_not_dvd hN 3 (by norm_num)
  set ω₀ : ↥(rLayer (Om R) e) := ã ^ r with hω₀
  have hωy : ((ω₀ : ↥(rLayer (Om R) e)) : Y) = (ã : Y) ^ r := rfl
  have hpiω : piE hc ω₀ = q ^ r := by rw [hω₀, map_pow, hãq]
  have hrr : r * r % 3 = 1 := by
    have : r % 3 = 1 ∨ r % 3 = 2 := by omega
    rcases this with h | h <;> simp [Nat.mul_mod, h]
  have hqrr : (q ^ r) ^ r = q := by
    rw [← pow_mul]
    obtain ⟨m, hm⟩ : ∃ m, r * r = 3 * m + 1 := ⟨r * r / 3, by omega⟩
    rw [hm, pow_succ, pow_mul, hq3, one_pow, one_mul]
  refine ⟨(ω₀ : Y), ω₀.2, ?_, ?_, ?_⟩
  · rw [hωy]
    exact (Subgroup.mem_centralizer_singleton_iff.mp
      ((Subgroup.centralizer ({t} : Set Y)).pow_mem hãC r))
  · have hp : ((ω₀ : ↥(rLayer (Om R) e)) : Y) ^ 3 ^ a' = 1 := by
      rw [hωy, ← pow_mul, mul_comm, ← hNr, pow_orderOf_eq_one]
    obtain ⟨i, -, hi⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp (orderOf_dvd_of_pow_eq_one hp)
    exact IsPGroup.of_card (by rw [Nat.card_zpowers, hi])
  · obtain ⟨x', hx', hxne⟩ := hamove
    rw [← hlab] at hx'
    obtain ⟨ā', hā', rfl⟩ := hx'
    obtain ⟨h, hh, rfl⟩ := hā'
    have hk : ((h : ↥(Subgroup.centralizer ({e} : Set Y))) : Y) ∈ TwinADescent.coreAt e (tightCore R) :=
      Subgroup.mem_subgroupOf.mp (Subgroup.mem_subgroupOf.mp hh)
    have hkK : ((h : ↥(Subgroup.centralizer ({e} : Set Y))) : Y) ∈ tightCore R :=
      TwinADescent.coreAt_le_left e _ hk
    have hkE : ((h : ↥(Subgroup.centralizer ({e} : Set Y))) : Y) ∈ rLayer (Om R) e := by
      rw [← hmap_of hc]
      exact ⟨h, h.2, rfl⟩
    refine ⟨((h : ↥(Subgroup.centralizer ({e} : Set Y))) : Y), hkK, fun hcomm => hxne ?_⟩
    have h1 : ω₀ * ⟨((h : ↥(Subgroup.centralizer ({e} : Set Y))) : Y), hkE⟩ =
        ⟨((h : ↥(Subgroup.centralizer ({e} : Set Y))) : Y), hkE⟩ * ω₀ := Subtype.ext hcomm
    have h2 := congrArg (piE hc) h1
    rw [map_mul, map_mul, hpiω, piE_mk hc h hkE] at h2
    have h3 : q * QuotientGroup.mk' (classicalInvolutionOddCore ↥(coreHull (Om R) e)) h =
        QuotientGroup.mk' (classicalInvolutionOddCore ↥(coreHull (Om R) e)) h * q := by
      have := (Commute.pow_left (show Commute (q ^ r) _ from h2) r).eq
      rwa [hqrr] at this
    have h4 := congrArg D.φ h3
    rw [map_mul, map_mul, hφq] at h4
    exact h4

theorem tightCore_le_rLayer (hc : P23Cfg n Y R S t K' W u e g)
    (hO : classicalInvolutionOddCore ↥(Subgroup.centralizer ({t} : Set Y)) = ⊥) :
    tightCore R ≤ rLayer (Om R) e := by
  have hd := hc.data
  have hC := CoreData.of_S hc.std.perp.core
  have hΩ : HypOmegaGen (Om R) := hC.hyp
  have hzt : IsUniqueInvolution (tightCore R) t := Inner.isUniqueInvolution_core hC.datum
  have hWab : ∀ a ∈ W, ∀ b ∈ W, a * b = b * a := Q3CL.Thompson.commutes_of_mem_WSet hΩ hd.hW
  have heW : e ∈ W := (T7K.e_mem_inf hd).1
  have hinj := piC_injective_of_eq_bot hO
  have heC : e ∈ Subgroup.centralizer ({t} : Set Y) :=
    Subgroup.mem_centralizer_singleton_iff.mpr (hWab e heW t hd.hzW)
  have htC : t ∈ Subgroup.centralizer ({t} : Set Y) :=
    Subgroup.mem_centralizer_singleton_iff.mpr rfl
  obtain ⟨-, -, h8A, -, -, -, -, heA, -, -⟩ := p23_twin_q8 hc rfl htC heC
  have hKC : tightCore R ≤ Subgroup.centralizer ({t} : Set Y) := le_centralizer_of_unique hzt
  have heK : ∀ k ∈ tightCore R, e * k = k * e := by
    intro k hk
    have h1 := heA (F7I.piC _ ⟨k, hKC hk⟩) ⟨⟨k, hKC hk⟩, Subgroup.mem_subgroupOf.mpr hk, rfl⟩
    rw [← map_mul, ← map_mul] at h1
    exact congrArg Subtype.val (hinj h1)
  have hK2 : IsPGroup 2 (tightCore R) := by
    rw [Subgroup.card_map_of_injective hinj,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hKC).toEquiv] at h8A
    exact IsPGroup.of_card (n := 3) (by rw [h8A]; norm_num)
  have hKe : tightCore R ≤ Subgroup.centralizer ({e} : Set Y) := fun k hk =>
    Subgroup.mem_centralizer_singleton_iff.mpr (heK k hk).symm
  have hcore : TwinADescent.coreAt e (tightCore R) = tightCore R := by
    show tightCore (tightCore R ⊓ Subgroup.centralizer ({e} : Set Y)) = tightCore R
    rw [inf_eq_left.mpr hKe]
    exact tightCore_eq_of_isPGroup hK2
  have hle : TwinADescent.coreAt e (tightCore R) ≤ rLayer (Om R) e := by
    intro x hx
    rw [← hmap_of hc]
    exact ⟨⟨x, TwinADescent.coreAt_le_centralizer e _ hx⟩,
      TwinDisc.le_coreHull (twins_tq hc).1 (Subgroup.mem_subgroupOf.mpr hx), rfl⟩
  exact hcore ▸ hle

theorem p23E8Z_eClass_ncard_le_three (hT : Thm4RTwinBelow 3 n)
    (hcit : CIT3Below n) (hP : TL4.TightBelowRPlus 3 n) (hc : P23Cfg n Y R S t K' W u e g)
    (hZ : u * e ∈ zStarOf (rLayer (Om R) u)) (hAE : SecAE R e 6)
    (hO : Balance.oddCoreIn (Subgroup.centralizer ({t} : Set Y)) = ⊥) :
    (eClass t e).ncard ≤ 3 := by
  obtain ⟨ω, hωE, hωt, hω3, hmove⟩ := exists_omega hc hAE
  have hωe : ω * e = e * ω :=
    Subgroup.mem_centralizer_singleton_iff.mp (rLayer_le_centralizer (Om R) e hωE)
  exact p23_eClass_ncard_le_three hcit hP hc (R56.p23_zstar_cu hT hc hZ)
    (TwinConnT.classicalOddCore_eq_bot_of_oddCoreIn hO) hωt hωe hω3 hmove

theorem p23E8Z_sig_of_x0 (hT : Thm4RTwinBelow 3 n)
    (hcit : CIT3Below n) (hP : TL4.TightBelowRPlus 3 n) (hc : P23Cfg n Y R S t K' W u e g)
    (hZ : u * e ∈ zStarOf (rLayer (Om R) u)) (hAE : SecAE R e 6)
    (hO : Balance.oddCoreIn (Subgroup.centralizer ({t} : Set Y)) = ⊥)
    {X : Subgroup Y} {x₀ : Y} (hEX : rLayer (Om R) e ≤ X) (hx₀X : x₀ ∈ X)
    (hx₀t : x₀ * t = t * x₀) (hx₀3 : IsPGroup 3 (Subgroup.zpowers x₀))
    (hx₀e : x₀ * e * x₀⁻¹ ≠ e) :
    ∀ J ∈ dstarComp (Om R) (tightCore R), J ≤ X :=
  sig_of_x0 hc (p23E8Z_eClass_ncard_le_three hT hcit hP hc hZ hAE hO) hEX
    ((tightCore_le_rLayer hc (TwinConnT.classicalOddCore_eq_bot_of_oddCoreIn hO)).trans hEX)
    hx₀X hx₀t hx₀3 hx₀e

end Omega

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23.ZTwo
