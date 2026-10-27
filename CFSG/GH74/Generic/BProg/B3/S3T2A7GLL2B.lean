module

public import CFSG.GH74.Generic.BProg.B2.GenLocL2Small
public import CFSG.RankThree.PartOne.S9.Planes.Basic
public import CFSG.LocalAnalysis.ComponentClassification.CentralCoverLemmasAFaithful
public import CFSG.GH74.Generic.BProg.B3.ObsPump

public section

namespace CFSG.GH74.Generic.BProg.B3.S3T2A7.GLR

open CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.ClassicalInvolution.Balance Subgroup

variable {Y : Type} [Group Y] [Finite Y] {L B X₀ : Subgroup Y} {z : Y}

theorem rankCertified_one_of_simple {T : Type} [Group T]
    [Finite T] [IsSimpleGroup T] (hnab : ∃ a b : T, a * b ≠ b * a) : RankCertified T 1 := by
  have heven := (CFSG.ComponentClassification.SimpleEvenOrder.nonabelian_simple_even hnab).1
  have h2 := two_le_twoRank T hnab heven
  obtain ⟨E, -, hE, hcard⟩ := (CFSG.RankThree.PartOne.Planes.le_pRank_iff Nat.prime_two ⊤ 2).1 h2
  refine ⟨↥E, ↥E, inferInstance, inferInstance, inferInstance, E.subtype, MonoidHom.id _,
    Function.surjective_id, fun a b => hE.is_comm.comm a b, fun a => ?_, ?_, ?_⟩
  · exact Monoid.exponent_dvd_iff_forall_pow_eq_one.mp (IsElementaryAbelian.exponent_dvd_p 2 ↥E) a
  · rw [hcard]
    norm_num
  · intro x hx
    rw [MonoidHom.mem_ker] at hx ⊢
    exact Subtype.ext hx

theorem mem_centralizer_of_inner_small {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hq : p ^ f ∈ ({5, 7, 9} : Finset ℕ)) (hL : CFSG.IsComponent L)
    (hT : LieModel (↥L ⧸ center ↥L) .PSL 2 p f) {f₀ : Y} (hf₀ : f₀ ∈ normalizer (L : Set Y))
    (hf2 : f₀ * f₀ = 1) {l : Y} (hl : l ∈ L) (hact : ∀ x ∈ L, f₀ * x * f₀⁻¹ = l * x * l⁻¹)
    (hnt : f₀ ∉ centralizer (L : Set Y)) {n : Y}
    (hn : n ∈ CFSG.Assembly.Dichotomy.involutionOddCore f₀) (hnL : n ∈ normalizer (L : Set Y)) :
    n ∈ centralizer (L : Set Y) := by
  classical
  set M : Subgroup Y := normalizer (L : Set Y) with hM
  let φ : ↥M →* ↥(rhoL L).range := (rhoL L).rangeRestrict
  have hcore : φ ⟨n, hnL⟩ ∈ CFSG.Assembly.Dichotomy.involutionOddCore (φ ⟨f₀, hf₀⟩) := by
    have h1 : (⟨n, hnL⟩ : ↥M) ∈ CFSG.Assembly.Dichotomy.involutionOddCore (⟨f₀, hf₀⟩ : ↥M) :=
      LocalBalance.subgroupOf_involutionOddCore_le ⟨f₀, hf₀⟩ (Subgroup.mem_subgroupOf.mpr hn)
    exact map_involutionOddCore_le φ (MonoidHom.rangeRestrict_surjective _)
      (isPGroup_zpowers_of_mul_self_eq_one (Subtype.ext hf2 : (⟨f₀, hf₀⟩ : ↥M) * ⟨f₀, hf₀⟩ = 1))
      (Subgroup.mem_map_of_mem φ h1)
  set t : ↥L ⧸ center ↥L := QuotientGroup.mk ⟨l, hl⟩ with ht
  have hρf : rhoL L ⟨f₀, hf₀⟩ = MulAut.conj t := by
    refine MulEquiv.ext fun xbar => ?_
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective xbar
    change CFSG.ComponentClassification.PerfectAutomorphisms.centerQuotientHom ↥L
      (CFSG.LocalAnalysis.ComponentInitial.normalizerConjHom L ⟨f₀, hf₀⟩)
        (QuotientGroup.mk x) = _
    rw [CFSG.ComponentClassification.CentralCover.centerQuotientHom_apply_mk, MulAut.conj_apply,
      ht, ← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
    congr 1
    apply Subtype.ext
    rw [CFSG.LocalAnalysis.ComponentInitial.coe_normalizerConjHom_apply, hact x x.2]
    rfl
  have hlsq : (⟨l * l, mul_mem hl hl⟩ : ↥L) ∈ center ↥L := by
    refine mem_center_iff.mpr fun g => Subtype.ext ?_
    have hg1 : f₀ * (g : Y) * f₀⁻¹ ∈ L := by
      rw [hact g g.2]
      exact mul_mem (mul_mem hl g.2) (inv_mem hl)
    have h1 : f₀ * (f₀ * (g : Y) * f₀⁻¹) * f₀⁻¹ = l * (l * (g : Y) * l⁻¹) * l⁻¹ := by
      rw [hact _ hg1, hact g g.2]
    have h2 : f₀ * (f₀ * (g : Y) * f₀⁻¹) * f₀⁻¹ = g := by
      calc f₀ * (f₀ * (g : Y) * f₀⁻¹) * f₀⁻¹ = (f₀ * f₀) * g * (f₀ * f₀)⁻¹ := by group
        _ = g := by rw [hf2]; group
    rw [h2] at h1
    show (g : Y) * (l * l) = l * l * g
    calc (g : Y) * (l * l) = (l * (l * g * l⁻¹) * l⁻¹) * (l * l) := by rw [← h1]
      _ = l * l * g := by group
  have ht2 : orderOf t = 2 := by
    refine orderOf_eq_prime ?_ ?_
    · rw [ht, ← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff, pow_two]
      exact hlsq
    · intro h1
      rw [ht, QuotientGroup.eq_one_iff] at h1
      apply hnt
      rw [Subgroup.mem_centralizer_iff]
      intro x hx
      have h3 : (l : Y) * x = x * l :=
        (congrArg Subtype.val (mem_center_iff.mp h1 ⟨x, hx⟩)).symm
      have h2 : f₀ * x * f₀⁻¹ = x := by rw [hact x hx, h3]; group
      calc x * f₀ = (f₀ * x * f₀⁻¹) * f₀ := by rw [h2]
        _ = f₀ * x := by group
  obtain ⟨-, -, -, -, F, _, _, -, ⟨e⟩⟩ :=
    CFSG.ComponentClassification.AutL2Facts.lieModel_psl2_data hT
  have hZ := B2.GenLocL2Small.center_trivial e
  have hinj := B2.GenLocL2Small.conj_injective_of_center hZ
  have hbot : CFSG.Assembly.Dichotomy.involutionOddCore (φ ⟨f₀, hf₀⟩) = ⊥ := by
    rw [eq_bot_iff]
    intro h hh
    rw [Subgroup.mem_bot]
    have hodd : Odd (orderOf h) := Odd.of_dvd_nat
      (CFSG.Assembly.Dichotomy.odd_card_involutionOddCore _)
      (by
        have := orderOf_dvd_natCard (⟨h, hh⟩ :
          ↥(CFSG.Assembly.Dichotomy.involutionOddCore (φ ⟨f₀, hf₀⟩)))
        rwa [Subgroup.orderOf_mk] at this)
    have hcomm : h * φ ⟨f₀, hf₀⟩ = φ ⟨f₀, hf₀⟩ * h := by
      have := CFSG.GH74.GLS.Prop27.involutionOddCore_le_centralizer (φ ⟨f₀, hf₀⟩) hh
      exact (mem_centralizer_singleton_iff.mp this)
    have hodd' : Odd (orderOf (h : MulAut (↥L ⧸ center ↥L))) := by
      rwa [Subgroup.orderOf_coe]
    obtain ⟨k, hk⟩ := B2.GenLocL2Small.exists_inner_of_odd hp hp2 hq hT _ hodd'
    have hfval : ((φ ⟨f₀, hf₀⟩ : ↥(rhoL L).range) : MulAut (↥L ⧸ center ↥L)) = MulAut.conj t :=
      hρf
    have hkt : t * k = k * t := by
      apply hinj
      have := congrArg Subtype.val hcomm
      simp only [Subgroup.coe_mul, hfval, hk] at this
      rw [map_mul, map_mul]
      exact this.symm
    obtain ⟨j, hj⟩ := B2.GenLocL2Small.commute_involution_two_power hp hp2 hq hT ht2 k hkt
    have hok : orderOf k = orderOf h := by
      rw [← orderOf_injective _ hinj k, ← hk, Subgroup.orderOf_coe]
    have hk1 : k = 1 := by
      have hdvd : orderOf k ∣ 2 ^ j := orderOf_dvd_of_pow_eq_one hj
      obtain ⟨i, -, hi⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hdvd
      rcases i with _ | i
      · rwa [pow_zero, orderOf_eq_one_iff] at hi
      · exfalso
        have hev : Even (orderOf h) := by
          rw [← hok, hi]
          exact Nat.even_pow.mpr ⟨even_two, Nat.succ_ne_zero i⟩
        exact (Nat.not_even_iff_odd.mpr hodd) hev
    apply Subtype.ext
    rw [hk, hk1, map_one]
    rfl
  have hn1 : φ ⟨n, hnL⟩ = 1 := by
    rw [hbot] at hcore
    exact (Subgroup.mem_bot.mp hcore)
  have h1 : rhoL L ⟨n, hnL⟩ = 1 := congrArg Subtype.val hn1
  rw [Subgroup.mem_centralizer_iff]
  intro x hx
  exact ((ObsPump.rhoL_eq_one_iff hL ⟨n, hnL⟩).mp h1 x hx).symm

end CFSG.GH74.Generic.BProg.B3.S3T2A7.GLR
