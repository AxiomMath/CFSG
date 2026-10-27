module

public import CFSG.Quasithin.Vol2.Ch5Sec1L34Lem516
public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch5Sec1L34Inputs
public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch5StatementsB
public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch5Sec1Lem515

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin

section Setting

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G] {T M L V H B D : Subgroup G} {n : ℕ}

namespace Hyp5_1_14

variable (h : Hyp5_1_14 G T M L V H B D n)
include h

theorem isUniqueM_F4 (h5114 : Stmt5_1_14_first_F4) :
    IsUniqueM H (Subgroup.normalizer (oTwoUpper H : Set G)) :=
  (h5114 G T M L V H B D n h.hyp h.notation59 h.module h.l34).1.2.1

theorem isMaxTwoLocal_F4 (h5114 : Stmt5_1_14_first_F4) :
    quasithinIsMaxTwoLocal (Subgroup.normalizer (oTwoUpper H : Set G)) :=
  (h.isUniqueM_F4 h5114).1.1

theorem pCoreOf_Mp_ne_bot_F4 (h5114 : Stmt5_1_14_first_F4) :
    pCoreOf 2 (Subgroup.normalizer (oTwoUpper H : Set G)) ≠ ⊥ :=
  pCoreOf_ne_bot_of_isTwoLocal (h.isMaxTwoLocal_F4 h5114).1

theorem charTwo_Mp_F4 (h5114 : Stmt5_1_14_first_F4) :
    CharTwo (Subgroup.normalizer (oTwoUpper H : Set G)) := by
  obtain ⟨S, hS⟩ := exists_sylow_coe_eq h.hyp.sylow
  have hT : (S : Subgroup G) ≤ Subgroup.normalizer (oTwoUpper H : Set G) := by
    rw [hS]; exact h.T_le_Mp
  exact charTwo_of_le h.hyp.qtke.2.1 S hT le_rfl ⟨hT, h.pCoreOf_Mp_ne_bot_F4 h5114⟩

theorem pRank_Mp_le_two_F4 (h5114 : Stmt5_1_14_first_F4) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) :
    CFSG.Open.pRank p (Subgroup.normalizer (oTwoUpper H : Set G)) ≤ 2 :=
  pRank_le_two_of_isTwoLocal h.hyp.qtke hp hp2 (h.isMaxTwoLocal_F4 h5114).1

theorem not_three_dvd_F4
    (h5114 : Stmt5_1_14_first_F4) (hE9 : L34ElemNineFact) :
    ¬ 3 ∣ Nat.card (centralizerModO2 (oTwoUpper H)) :=
  not_three_dvd_card_centralizerModO2 hE9 h.l34
    (h.pRank_Mp_le_two_F4 h5114 Nat.prime_three (by norm_num))

theorem pCoreOf_K_ne_bot_F4
    (h5114 : Stmt5_1_14_first_F4) : pCoreOf 2 (oTwoUpper H) ≠ ⊥ :=
  pCoreOf_ne_bot_of_subnormal (subnormal_normalizer _) (h.charTwo_Mp_F4 h5114) h.K_ne_bot

theorem pCoreOf_centralizerModO2_ne_bot_F4
    (h5114 : Stmt5_1_14_first_F4) :
    pCoreOf 2 (centralizerModO2 (oTwoUpper H)) ≠ ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro hbot
  apply h.pCoreOf_K_ne_bot_F4 h5114
  have hle : pCoreOf 2 (oTwoUpper H) ≤ pCoreOf 2 (centralizerModO2 (oTwoUpper H)) :=
    le_pCoreOf_of_le_normalizer 2 (pCoreOf_le_centralizerModO2 _)
      (centralizerMod_le_normalizer _ _ _) (pCoreOf_isPGroup 2 _)
  rw [hbot] at hle
  exact le_bot_iff.mp hle

end Hyp5_1_14

end Setting

section Components

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G] {T M L V H B D : Subgroup G} {n : ℕ}

namespace Hyp5_1_14

variable (h : Hyp5_1_14 G T M L V H B D n)
include h

theorem not_three_dvd_cComp_F4
    (h5114 : Stmt5_1_14_first_F4) (hE9 : L34ElemNineFact) {Kp : Subgroup G}
    (hKp : Kp ∈ cComp (centralizerModO2 (oTwoUpper H))) : ¬ 3 ∣ Nat.card Kp := fun h3 =>
  h.not_three_dvd_F4 h5114 hE9 (h3.trans (Subgroup.card_dvd_of_le (le_of_mem_cComp hKp)))

theorem suzuki_cComp_F4
    (h5114 : Stmt5_1_14_first_F4) (hE9 : L34ElemNineFact) (h36 : A36ForSQTK)
    (hSz : SimpleThreePrimeSuzukiFact) {Kp : Subgroup G}
    (hKp : Kp ∈ cComp (centralizerModO2 (oTwoUpper H))) :
    IsSimpleGroup (O2Q Kp) ∧ ∃ k : ℕ, SuzukiModel (O2Q Kp) 2 k :=
  isSimpleGroup_and_suzukiModel_of_cComp h.hyp.qtke h.hyp.simple h.hyp.nonabelian h36 hSz
    (h.pCoreOf_Mp_ne_bot_F4 h5114) (mem_cComp_normalizer_of_mem_cComp hKp)
    (h.not_three_dvd_cComp_F4 h5114 hE9 hKp)

theorem pCoreOf_cComp_ne_bot_F4 (h5114 : Stmt5_1_14_first_F4) {Kp : Subgroup G}
    (hKp : Kp ∈ cComp (centralizerModO2 (oTwoUpper H))) : pCoreOf 2 Kp ≠ ⊥ :=
  pCoreOf_ne_bot_of_subnormal (subnormal_of_mem_cComp (mem_cComp_normalizer_of_mem_cComp hKp))
    (h.charTwo_Mp_F4 h5114)
    (ne_bot_of_mem_cComp hKp)

theorem cComp_unique_F4
    (h5114 : Stmt5_1_14_first_F4) (hE9 : L34ElemNineFact) (h36 : A36ForSQTK)
    (h37 : A37ForSQTK) (hSz : SimpleThreePrimeSuzukiFact) {Kp Kp' : Subgroup G}
    (hKp : Kp ∈ cComp (centralizerModO2 (oTwoUpper H)))
    (hKp' : Kp' ∈ cComp (centralizerModO2 (oTwoUpper H))) : Kp = Kp' := by
  by_contra hne
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  set K := oTwoUpper H with hKdef
  set Mp := Subgroup.normalizer (K : Set G) with hMpdef
  have hO := h.pCoreOf_Mp_ne_bot_F4 h5114
  have hQ := sqtkHyp_quotient_of_pCoreOf_ne_bot h.hyp.qtke h.hyp.simple h.hyp.nonabelian hO
  have hA37 := h37 _ hQ
  have hKpM := mem_cComp_normalizer_of_mem_cComp hKp
  have hKpM' := mem_cComp_normalizer_of_mem_cComp hKp'
  have hAc := modO2Image_mem_cComp hKpM
  have hAc' := modO2Image_mem_cComp hKpM'
  set A := modO2Image Mp Kp with hAdef
  set A' := modO2Image Mp Kp' with hA'def
  have hAA' : A ≠ A' := fun e => hne (modO2Image_injOn Mp hKpM hKpM' e)
  have hcomm1 : ⁅A, A'⁆ = ⊥ := hA37 A hAc A' hAc' hAA'
  obtain ⟨hs1, k1, hk1⟩ := h.suzuki_cComp_F4 h5114 hE9 h36 hSz hKp
  obtain ⟨hs2, k2, hk2⟩ := h.suzuki_cComp_F4 h5114 hE9 h36 hSz hKp'
  obtain ⟨e1⟩ := modO2_mulEquiv hKpM
  obtain ⟨e2⟩ := modO2_mulEquiv hKpM'
  have hA5 : 5 ∣ Nat.card A ∧ ¬ (Nat.card A).Prime := by
    rw [← Nat.card_congr e1.toEquiv]; exact five_dvd_card_of_suzukiModel hk1
  have hA5' : 5 ∣ Nat.card A' ∧ ¬ (Nat.card A').Prime := by
    rw [← Nat.card_congr e2.toEquiv]; exact five_dvd_card_of_suzukiModel hk2
  have hsA : IsSimpleGroup ↥A := e1.symm.isSimpleGroup
  have hsA' : IsSimpleGroup ↥A' := e2.symm.isSimpleGroup
  have hZA : Subgroup.center ↥A = ⊥ := center_eq_bot_of_isSimpleGroup_of_not_prime hA5.2
  have hZA' : Subgroup.center ↥A' = ⊥ := center_eq_bot_of_isSimpleGroup_of_not_prime hA5'.2
  obtain ⟨a, ha⟩ := exists_prime_orderOf_dvd_card' 5 hA5.1
  obtain ⟨b, hb⟩ := exists_prime_orderOf_dvd_card' 5 hA5'.1

  have hK5 : 5 ∣ Nat.card (O2Q K) := by
    rw [card_of_lieModel_L34 h.l34]; norm_num
  obtain ⟨y, hy⟩ := exists_prime_orderOf_dvd_card' 5 hK5
  obtain ⟨k₀, rfl⟩ := QuotientGroup.mk_surjective y
  have hKMp : K ≤ Mp := Subgroup.le_normalizer
  set π := QuotientGroup.mk' (CFSG.pCore 2 ↥Mp) with hπ
  set c := π (Subgroup.inclusion hKMp k₀) with hcdef
  have hOKM : pCoreOf 2 K ≤ pCoreOf 2 Mp := A4.pCoreOf_le_of_subnormal 2 (subnormal_normalizer _)
  have hmemO : ∀ x : ↥Mp, (x : G) ∈ pCoreOf 2 Mp → π x = 1 := by
    intro x hx
    rw [hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    obtain ⟨z, hz, hzx⟩ := hx
    have : z = x := Subtype.ext hzx
    rw [← this]
    exact hz
  have hc5 : c ^ 5 = 1 := by
    rw [hcdef, ← map_pow, ← map_pow]
    apply hmemO
    apply hOKM
    have h1 : (QuotientGroup.mk (k₀ ^ 5) : O2Q K) = 1 := by
      rw [QuotientGroup.mk_pow, ← hy, pow_orderOf_eq_one]
    rw [QuotientGroup.eq_one_iff] at h1
    exact ⟨_, h1, by simp⟩
  have hc1 : c ≠ 1 := by
    intro hc
    rw [hcdef, hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hc
    have hk₀ : (k₀ : G) ∈ pCoreOf 2 Mp := ⟨_, hc, rfl⟩
    have hk₀K : (k₀ : G) ∈ pCoreOf 2 K := by
      refine le_pCoreOf_of_le_normalizer 2 (inf_le_left : K ⊓ pCoreOf 2 Mp ≤ K) ?_
        ((pCoreOf_isPGroup 2 Mp).to_le inf_le_right) ⟨k₀.2, hk₀⟩
      intro k hk
      rw [Subgroup.mem_normalizer_iff]
      intro x
      have h1 := Subgroup.mem_normalizer_iff.mp (Subgroup.le_normalizer hk) x
      have h2 := Subgroup.mem_normalizer_iff.mp (le_normalizer_pCoreOf 2 Mp (hKMp hk)) x
      simp only [Subgroup.mem_inf]
      exact and_congr h1 h2
    have : (QuotientGroup.mk k₀ : O2Q K) = 1 := by
      rw [QuotientGroup.eq_one_iff]
      obtain ⟨z, hz, hzx⟩ := hk₀K
      have : z = k₀ := Subtype.ext hzx
      rw [← this]
      exact hz
    rw [this, orderOf_one] at hy
    norm_num at hy
  have hcord : orderOf c = 5 := orderOf_eq_prime hc5 hc1

  have hcomm_c : ∀ {X : Subgroup G}, X ≤ centralizerModO2 K → ∀ x ∈ modO2Image Mp X,
      x * c = c * x := by
    intro X hX x hx
    obtain ⟨x₀, hx₀, rfl⟩ := hx
    replace hx₀ : (x₀ : G) ∈ X := Subgroup.mem_subgroupOf.mp hx₀
    rw [hcdef, ← map_mul, ← map_mul, hπ, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply,
      QuotientGroup.eq]
    have hmem := commutator_mem_of_mem_centralizerModO2 (hX hx₀) k₀.2
    have hn : ((x₀ : G) * k₀)⁻¹ ∈ Subgroup.normalizer (pCoreOf 2 Mp : Set G) :=
      le_normalizer_pCoreOf 2 Mp (Mp.inv_mem (Mp.mul_mem x₀.2 (hKMp k₀.2)))
    have hmem' := (Subgroup.mem_normalizer_iff.mp hn _).mp (hOKM (inv_mem hmem))
    obtain ⟨z, hz, hzx⟩ := hmem'
    have hz' : (x₀ * Subgroup.inclusion hKMp k₀)⁻¹ * (Subgroup.inclusion hKMp k₀ * x₀) = z := by
      apply Subtype.ext
      rw [show (z : G) = _ from hzx]
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_inclusion]
      group
    rw [hz']
    exact hz
  have hcA : ∀ x ∈ A, x * c = c * x :=
    hcomm_c (le_of_mem_cComp hKp)
  have hcA' : ∀ x ∈ A', x * c = c * x :=
    hcomm_c (le_of_mem_cComp hKp')
  have hAA'c : ∀ x ∈ A, ∀ x' ∈ A', x * x' = x' * x := by
    intro x hx x' hx'
    have := Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcomm1 hx
    exact (Subgroup.mem_centralizer_iff.mp this x' hx').symm

  have haA : (a : ↥Mp ⧸ CFSG.pCore 2 ↥Mp) ∈ A := a.2
  have hbA' : (b : ↥Mp ⧸ CFSG.pCore 2 ↥Mp) ∈ A' := b.2
  have hza : ∀ u ∈ Subgroup.zpowers (a : ↥Mp ⧸ CFSG.pCore 2 ↥Mp), u ∈ A := fun u hu => by
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hu
    exact A.zpow_mem haA i
  have hzb : ∀ u ∈ Subgroup.zpowers (b : ↥Mp ⧸ CFSG.pCore 2 ↥Mp), u ∈ A' := fun u hu => by
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hu
    exact A'.zpow_mem hbA' i
  have hzc : ∀ u ∈ Subgroup.zpowers c, ∀ x ∈ A, x * u = u * x := fun u hu x hx => by
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hu
    exact (Commute.zpow_right (hcA x hx) i).eq
  have hzc' : ∀ u ∈ Subgroup.zpowers c, ∀ x ∈ A', x * u = u * x := fun u hu x hx => by
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hu
    exact (Commute.zpow_right (hcA' x hx) i).eq
  have hbc : ∀ (v : ↥(Subgroup.zpowers (b : ↥Mp ⧸ CFSG.pCore 2 ↥Mp))) (w : ↥(Subgroup.zpowers c)),
      Commute ((Subgroup.zpowers _).subtype v) ((Subgroup.zpowers c).subtype w) := fun v w =>
    show Commute (v : ↥Mp ⧸ CFSG.pCore 2 ↥Mp) (w : ↥Mp ⧸ CFSG.pCore 2 ↥Mp) from
      hzc' w w.2 v (hzb v v.2)
  set g := MonoidHom.noncommCoprod (Subgroup.zpowers _).subtype (Subgroup.zpowers c).subtype hbc
    with hg
  have hag : ∀ (u : ↥(Subgroup.zpowers (a : ↥Mp ⧸ CFSG.pCore 2 ↥Mp)))
      (vw : ↥(Subgroup.zpowers (b : ↥Mp ⧸ CFSG.pCore 2 ↥Mp)) × ↥(Subgroup.zpowers c)),
      Commute ((Subgroup.zpowers _).subtype u) (g vw) := by
    rintro u ⟨v, w⟩
    rw [hg, MonoidHom.noncommCoprod_apply]
    simp only [Subgroup.coe_subtype]
    have h1 : (u : ↥Mp ⧸ CFSG.pCore 2 ↥Mp) * v = v * u := hAA'c _ (hza u u.2) _ (hzb v v.2)
    have h2 : (u : ↥Mp ⧸ CFSG.pCore 2 ↥Mp) * w = w * u := hzc w w.2 _ (hza u u.2)
    exact ((Commute.mul_right h1 h2))
  set f := MonoidHom.noncommCoprod (Subgroup.zpowers _).subtype g hag with hf
  have hf_inj : Function.Injective f := by
    rw [injective_iff_map_eq_one]
    rintro ⟨u, ⟨v, w⟩⟩ hfu
    rw [hf, MonoidHom.noncommCoprod_apply, hg, MonoidHom.noncommCoprod_apply] at hfu
    simp only [Subgroup.coe_subtype] at hfu
    have huA := hza u u.2
    have hvA' := hzb v v.2

    have hu1 : (u : ↥Mp ⧸ CFSG.pCore 2 ↥Mp) = 1 := by
      have hu : (u : ↥Mp ⧸ CFSG.pCore 2 ↥Mp) = ((v : ↥Mp ⧸ CFSG.pCore 2 ↥Mp) * w)⁻¹ :=
        eq_inv_of_mul_eq_one_left hfu
      have hcen : (⟨u, huA⟩ : ↥A) ∈ Subgroup.center ↥A := by
        rw [Subgroup.mem_center_iff]
        intro x
        apply Subtype.ext
        simp only [Subgroup.coe_mul]
        rw [hu]
        have h1 := hAA'c _ x.2 _ hvA'
        have h2 := hzc w w.2 _ x.2
        have h3 : Commute (x : ↥Mp ⧸ CFSG.pCore 2 ↥Mp) (v * w) := by
          show (x : ↥Mp ⧸ CFSG.pCore 2 ↥Mp) * (v * w) = (v * w) * x
          rw [← mul_assoc, h1, mul_assoc, h2, mul_assoc]
        exact (Commute.inv_right h3).eq
      rw [hZA, Subgroup.mem_bot] at hcen
      exact congrArg Subtype.val hcen
    rw [hu1, one_mul] at hfu
    have hv1 : (v : ↥Mp ⧸ CFSG.pCore 2 ↥Mp) = 1 := by
      have hv : (v : ↥Mp ⧸ CFSG.pCore 2 ↥Mp) = (w : ↥Mp ⧸ CFSG.pCore 2 ↥Mp)⁻¹ :=
        eq_inv_of_mul_eq_one_left hfu
      have hcen : (⟨v, hvA'⟩ : ↥A') ∈ Subgroup.center ↥A' := by
        rw [Subgroup.mem_center_iff]
        intro x
        apply Subtype.ext
        simp only [Subgroup.coe_mul]
        rw [hv]
        have h2 : Commute (x : ↥Mp ⧸ CFSG.pCore 2 ↥Mp) w := hzc' w w.2 _ x.2
        exact (Commute.inv_right h2).eq
      rw [hZA', Subgroup.mem_bot] at hcen
      exact congrArg Subtype.val hcen
    rw [hv1, one_mul] at hfu
    exact Prod.ext (Subtype.ext hu1) (Prod.ext (Subtype.ext hv1) (Subtype.ext hfu))
  have hpow5 : ∀ (z : ↥Mp ⧸ CFSG.pCore 2 ↥Mp), z ^ 5 = 1 →
      ∀ u : ↥(Subgroup.zpowers z), u ^ 5 = 1 := by
    intro z hz u
    obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.mp u.2
    apply Subtype.ext
    show (u : ↥Mp ⧸ CFSG.pCore 2 ↥Mp) ^ 5 = 1
    rw [← hi, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, show z ^ ((5 : ℕ) : ℤ) = 1 by
      exact_mod_cast hz, one_zpow]
  have ha5 : (a : ↥Mp ⧸ CFSG.pCore 2 ↥Mp) ^ 5 = 1 := by
    rw [← Subgroup.coe_pow, ← ha, pow_orderOf_eq_one, Subgroup.coe_one]
  have hb5 : (b : ↥Mp ⧸ CFSG.pCore 2 ↥Mp) ^ 5 = 1 := by
    rw [← Subgroup.coe_pow, ← hb, pow_orderOf_eq_one, Subgroup.coe_one]
  have hcommz : ∀ (z : ↥Mp ⧸ CFSG.pCore 2 ↥Mp) (u v : ↥(Subgroup.zpowers z)), u * v = v * u := by
    intro z u v
    obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.mp u.2
    obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp v.2
    apply Subtype.ext
    show (u : ↥Mp ⧸ CFSG.pCore 2 ↥Mp) * v = v * u
    rw [← hi, ← hj, ← zpow_add, ← zpow_add, add_comm]
  have hEcomm : ∀ x y : ↥(Subgroup.zpowers (a : ↥Mp ⧸ CFSG.pCore 2 ↥Mp)) ×
      (↥(Subgroup.zpowers (b : ↥Mp ⧸ CFSG.pCore 2 ↥Mp)) × ↥(Subgroup.zpowers c)),
      x * y = y * x := by
    rintro ⟨x1, x2, x3⟩ ⟨y1, y2, y3⟩
    exact Prod.ext (hcommz _ x1 y1) (Prod.ext (hcommz _ x2 y2) (hcommz _ x3 y3))
  have hEpow : ∀ x : ↥(Subgroup.zpowers (a : ↥Mp ⧸ CFSG.pCore 2 ↥Mp)) ×
      (↥(Subgroup.zpowers (b : ↥Mp ⧸ CFSG.pCore 2 ↥Mp)) × ↥(Subgroup.zpowers c)), x ^ 5 = 1 := by
    rintro ⟨x1, x2, x3⟩
    exact Prod.ext (by rw [Prod.pow_fst]; exact hpow5 _ ha5 x1)
      (Prod.ext (by rw [Prod.pow_snd, Prod.pow_fst]; exact hpow5 _ hb5 x2)
        (by rw [Prod.pow_snd, Prod.pow_snd]; exact hpow5 _ hc5 x3))
  have hEcard : Nat.card (↥(Subgroup.zpowers (a : ↥Mp ⧸ CFSG.pCore 2 ↥Mp)) ×
      (↥(Subgroup.zpowers (b : ↥Mp ⧸ CFSG.pCore 2 ↥Mp)) × ↥(Subgroup.zpowers c))) = 5 ^ 3 := by
    rw [Nat.card_prod, Nat.card_prod, Nat.card_zpowers, Nat.card_zpowers, Nat.card_zpowers,
      hcord, Subgroup.orderOf_coe, ha, Subgroup.orderOf_coe, hb]
    norm_num
  have h125 : 3 ≤ CFSG.Open.pRank 5 (⊤ : Subgroup (↥Mp ⧸ CFSG.pCore 2 ↥Mp)) :=
    CFSG.SectionRank.le_pRank_of_injective (by norm_num) hEcomm hEpow hEcard f hf_inj le_top
  have hQcard : ¬ 5 ∣ Nat.card (CFSG.pCore 2 ↥Mp) := by
    intro h5
    obtain ⟨m, hm⟩ := (CFSG.pCore_isPGroup (p := 2) (G := ↥Mp)).exists_card_eq
    rw [hm] at h5
    exact absurd (Nat.Prime.dvd_of_dvd_pow (by norm_num : (5 : ℕ).Prime) h5) (by norm_num)
  rw [CFSG.SectionRank.pRank_quotient_eq _ hQcard] at h125
  have h5' : CFSG.Open.pRank 5 (⊤ : Subgroup ↥Mp) ≤ CFSG.Open.pRank 5 Mp := by
    have := CFSG.SectionRank.pRank_le_map (p := 5) (by norm_num) Mp.subtype
      Mp.subtype_injective ⊤
    rwa [← MonoidHom.range_eq_map, Subgroup.range_subtype] at this
  have := h125.trans (h5'.trans (h.pRank_Mp_le_two_F4 h5114 (by norm_num) (by norm_num)))
  omega

theorem perfectCore_eq_F4
    (h5114 : Stmt5_1_14_first_F4) (hE9 : L34ElemNineFact) (h36 : A36ForSQTK)
    (h37 : A37ForSQTK) (h39 : A39ForSQTK) (hSz : SimpleThreePrimeSuzukiFact) {Kp : Subgroup G}
    (hKp : Kp ∈ cComp (centralizerModO2 (oTwoUpper H))) :
    perfectCore (centralizerModO2 (oTwoUpper H)) = Kp := by
  rw [← lemma_1_2_1_one h.hyp.qtke h.hyp.simple h.hyp.nonabelian h39
    (h.pCoreOf_centralizerModO2_ne_bot_F4 h5114)]
  refine le_antisymm (sSup_le fun K' hK' => ?_) (le_cCompSpan hKp)
  rw [← h.cComp_unique_F4 h5114 hE9 h36 h37 hSz hKp hK']

theorem normalizer_cComp_eq_F4
    (h5114 : Stmt5_1_14_first_F4) (hE9 : L34ElemNineFact)
    (h36 : A36ForSQTK) (h37 : A37ForSQTK) (h39 : A39ForSQTK) (hSz : SimpleThreePrimeSuzukiFact)
    {Kp : Subgroup G} (hKp : Kp ∈ cComp (centralizerModO2 (oTwoUpper H))) :
    Subgroup.normalizer (Kp : Set G) = Subgroup.normalizer (oTwoUpper H : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hPC := h.perfectCore_eq_F4 h5114 hE9 h36 h37 h39 hSz hKp
  have hMpN : Subgroup.normalizer (oTwoUpper H : Set G) ≤ Subgroup.normalizer (Kp : Set G) := by
    rw [← hPC]
    exact (normalizer_le_normalizer_centralizerModO2 _).trans
      (normalizer_le_normalizer_perfectCore _)
  have hloc : IsTwoLocal (Subgroup.normalizer (pCoreOf 2 Kp : Set G)) :=
    ⟨pCoreOf 2 Kp, h.pCoreOf_cComp_ne_bot_F4 h5114 hKp, pCoreOf_isPGroup 2 Kp, rfl⟩
  have hle : Subgroup.normalizer (Kp : Set G) ≤ Subgroup.normalizer (pCoreOf 2 Kp : Set G) :=
    normalizer_le_normalizer_pCoreOf 2 Kp
  have heq := (h.isMaxTwoLocal_F4 h5114).2 _ hloc (hMpN.trans hle)
  exact le_antisymm (heq ▸ hle) hMpN

theorem not_le_M_F4
    (h5114 : Stmt5_1_14_first_F4) (h331 : Stmt3_3_1_F4) (hE9 : L34ElemNineFact)
    (h36 : A36ForSQTK) (h37 : A37ForSQTK) (h39 : A39ForSQTK) (hSz : SimpleThreePrimeSuzukiFact)
    (hL2 : L2PerfectThreePrimeFact) {Kp : Subgroup G}
    (hKp : Kp ∈ cComp (centralizerModO2 (oTwoUpper H))) : ¬ Kp ≤ M := by
  intro hKpM
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hh := h.hyp.toHyp5_0_1
  have hKpN : Kp ≤ Subgroup.normalizer (L : Set G) := hKpM.trans hh.normal
  set φ := (quotConjAut L).comp (Subgroup.inclusion hKpN) with hφ
  have hperf : commutator ↥Kp = ⊤ :=
    Group.isPerfect_def.mp (Subgroup.isPerfect_iff.mpr (perfect_of_mem_cComp hKp))
  have hφ1 : φ = 1 := hL2 _ n hh.lie ↥Kp φ hperf (h.not_three_dvd_cComp_F4 h5114 hE9 hKp)
  have hcomm : ∀ k ∈ Kp, ∀ l ∈ L, k * l * k⁻¹ * l⁻¹ ∈ pCoreOf 2 L := by
    intro k hk l hl
    have h1 : quotConjAut L ⟨k, hKpN hk⟩ = 1 := by
      have := congrArg (fun ψ : ↥Kp →* MulAut (O2Q L) => ψ ⟨k, hk⟩) hφ1
      simp only [hφ, MonoidHom.comp_apply, MonoidHom.one_apply] at this
      exact this
    exact commutator_mem_of_quotConjAut_eq_one h1 ⟨l, hl⟩
  set Q := pCoreOf 2 L with hQdef
  set Y := Kp ⊔ Q with hYdef
  have hLY : L ≤ Subgroup.normalizer (Y : Set G) := by
    intro l hl
    apply mem_normalizer_of_forall_conj_mem'
    intro y hy
    have hle : Y ≤ Y.comap (MulAut.conj l).toMonoidHom := by
      refine sup_le (fun k hk => ?_) (fun q hq => ?_)
      · show l * k * l⁻¹ ∈ Y
        have e : l * k * l⁻¹ = (k * l * k⁻¹ * l⁻¹)⁻¹ * k := by group
        rw [e]
        exact Y.mul_mem (Subgroup.mem_sup_right (inv_mem (hcomm k hk l hl)))
          (Subgroup.mem_sup_left hk)
      · show l * q * l⁻¹ ∈ Y
        exact Subgroup.mem_sup_right ((Subgroup.mem_normalizer_iff.mp
          (le_normalizer_pCoreOf 2 L hl) q).mp hq)
    exact hle hy
  have hNKp := h.normalizer_cComp_eq_F4 h5114 hE9 h36 h37 h39 hSz hKp
  have hLT : IsSylowTwoOf T (L ⊔ T) := hh.isSylowTwoOf le_sup_right
  have hLsub : IsSubnormal L (L ⊔ T) :=
    A3.subnormal_of_normal le_sup_left
      ((Subgroup.normal_subgroupOf_iff_le_normalizer le_sup_left).mpr hh.sup_le_normalizer)
  have hQT : Q ≤ T :=
    (A4.pCoreOf_le_of_subnormal 2 hLsub).trans (CFSG.Quasithin.pCoreOf_le_of_isSylowTwoOf hLT)
  have hYN : Y ≤ Subgroup.normalizer (Kp : Set G) :=
    sup_le Subgroup.le_normalizer (hQT.trans (hNKp ▸ h.T_le_Mp))
  have hKpn : (Kp.subgroupOf Y).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer le_sup_left).mpr hYN
  have hQs : Group.IsSolvable ↥Q := by
    have := (pCoreOf_isPGroup 2 L).isNilpotent
    infer_instance
  have hPY : perfectCore Y = Kp :=
    le_antisymm (perfectCore_le_of_sup_solvable le_sup_left hKpn rfl hQs)
      (le_perfectCore_of_perfect le_sup_left (perfect_of_mem_cComp hKp))
  have hLN : L ≤ Subgroup.normalizer (oTwoUpper H : Set G) := by
    rw [← hNKp, ← hPY]
    exact hLY.trans (normalizer_le_normalizer_perfectCore Y)
  have hU := hh.isUniqueM_F4 h331
  have heq := hU.2 _ ⟨h.isMaxTwoLocal_F4 h5114, sup_le hLN h.T_le_Mp⟩
  exact h.hyp.hStar.2.1 (heq ▸ le_normalizer_oTwoUpper H)

theorem not_D_le_F4
    (h5114 : Stmt5_1_14_first_F4) (h331 : Stmt3_3_1_F4) (hE9 : L34ElemNineFact)
    (h36 : A36ForSQTK) (h37 : A37ForSQTK) (h39 : A39ForSQTK) (hSz : SimpleThreePrimeSuzukiFact)
    (hSzA : SzTwoAutInnerFact) (hL2 : L2PerfectThreePrimeFact) (hDS : DSSzStatement_F4)
    {Kp : Subgroup G} (hKp : Kp ∈ cComp (centralizerModO2 (oTwoUpper H))) :
    ¬ D ≤ Subgroup.normalizer (oTwoUpper H : Set G) := by
  intro hD
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hh := h.hyp.toHyp5_0_1
  set K := oTwoUpper H with hKdef
  set Mp := Subgroup.normalizer (K : Set G) with hMpdef
  have hNKp := h.normalizer_cComp_eq_F4 h5114 hE9 h36 h37 h39 hSz hKp
  have hKpMp : Kp ∈ cComp Mp := mem_cComp_normalizer_of_mem_cComp hKp
  obtain ⟨hsimp, k, hk⟩ := h.suzuki_cComp_F4 h5114 hE9 h36 hSz hKp
  have hnotM := h.not_le_M_F4 h5114 h331 hE9 h36 h37 h39 hSz hL2 hKp
  have hTMp : IsSylowTwoOf T Mp := hh.isSylowTwoOf h.T_le_Mp
  have hTKp : IsSylowTwoOf (T ⊓ Kp) Kp :=
    A312.isSylowTwoOf_inf_of_subnormal (subnormal_of_mem_cComp hKpMp) hTMp
  have hTL : IsSylowTwoOf (T ⊓ L) L :=
    A4.isSylowTwoOf_inf_normal (hh.isSylowTwoOf le_sup_right) le_sup_left hh.sup_le_normalizer
  have hTNKp : T ≤ Subgroup.normalizer (Kp : Set G) := hNKp ▸ h.T_le_Mp
  have hOT : pCoreOf 2 Kp ≤ T :=
    (A4.pCoreOf_le_of_subnormal 2 (subnormal_of_mem_cComp hKpMp)).trans
      (CFSG.Quasithin.pCoreOf_le_of_isSylowTwoOf hTMp)
  have hZKp : Subgroup.center (O2Q Kp) = ⊥ :=
    center_eq_bot_of_isSimpleGroup_of_not_prime (five_dvd_card_of_suzukiModel hk).2
  have hBp : borelOf Kp T ≤ Subgroup.normalizer (T : Set G) :=
    borelOf_le_normalizer_of_suzuki hSzA hh.sylow.1 hTNKp hTKp hOT hZKp hk
  have hNT : Subgroup.normalizer (T : Set G) ≤ M :=
    (h331 G T hh.simple hh.nonabelian hh.qtke hh.sylow).1 M L hh.maxTwoLocal hh.T_le hh.maximal
      hh.L_le hh.isQuasisimple
  have hBpL : borelOf Kp T ≤ Subgroup.normalizer (L : Set G) := hBp.trans (hNT.trans hh.normal)
  have hBL : borelOf L T ≤ Subgroup.normalizer (Kp : Set G) := by
    have e : borelOf L T = borelL T L := rfl
    rw [e, ← hh.borelL_eq_sup h.notation59.2.1, hNKp]
    exact sup_le hD (inf_le_left.trans h.T_le_Mp)
  obtain ⟨S, hS⟩ := exists_sylow_coe_eq hh.sylow
  have hEven := hh.qtke.2.1
  have hMO : pCoreOf 2 M ≠ ⊥ := pCoreOf_ne_bot_of_isTwoLocal hh.maxTwoLocal.1
  have hc1 : CharTwo (L ⊔ T ⊔ borelOf Kp T) := by
    have hle : L ⊔ T ⊔ borelOf Kp T ≤ M := sup_le (hh.sup_le_M) (hBp.trans hNT)
    have hTS : (S : Subgroup G) ≤ L ⊔ T ⊔ borelOf Kp T := by
      rw [hS]; exact le_sup_right.trans le_sup_left
    have hSM : (S : Subgroup G) ≤ M := by rw [hS]; exact hh.T_le
    exact charTwo_of_le hEven S hTS hle ⟨hSM, hMO⟩
  have hc2 : CharTwo (Kp ⊔ T ⊔ borelOf L T) := by
    have hle : Kp ⊔ T ⊔ borelOf L T ≤ Mp :=
      sup_le (sup_le (le_of_mem_cComp hKpMp) h.T_le_Mp) (hBL.trans hNKp.le)
    have hTS : (S : Subgroup G) ≤ Kp ⊔ T ⊔ borelOf L T := by
      rw [hS]; exact le_sup_right.trans le_sup_left
    have hSM : (S : Subgroup G) ≤ Mp := by rw [hS]; exact h.T_le_Mp
    exact charTwo_of_le hEven S hTS hle ⟨hSM, h.pCoreOf_Mp_ne_bot_F4 h5114⟩
  obtain ⟨a, ha, ⟨eSz⟩⟩ := exists_mulEquiv_sz_of_suzukiModel hk
  have eKp : O2Q Kp ≃* oTwoQuot ↥Kp :=
    QuotientGroup.quotientMulEquivOfEq (CFSG.pCore_eq_open ↥Kp 2)
  have eL : O2Q L ≃* oTwoQuot ↥L := QuotientGroup.quotientMulEquivOfEq (CFSG.pCore_eq_open ↥L 2)
  have hlistKp : IsRankOneListed (oTwoQuot ↥Kp) := Or.inr (Or.inl ⟨a, ⟨eKp.symm.trans eSz⟩⟩)
  have hlistL : IsRankOneListed (oTwoQuot ↥L) :=
    (isRankOneListed_of_lieModel (by have := hh.two_le; omega) hh.lie).of_mulEquiv eL
  have hO2 : pCoreOf 2 (Kp ⊔ L ⊔ T) = ⊥ := by
    by_contra hne
    have hloc : IsTwoLocal (Subgroup.normalizer (pCoreOf 2 (Kp ⊔ L ⊔ T) : Set G)) :=
      ⟨_, hne, pCoreOf_isPGroup 2 _, rfl⟩
    obtain ⟨M', hM', hle⟩ := exists_maxTwoLocal_ge hloc
    have hsup : Kp ⊔ L ⊔ T ≤ M' := (le_normalizer_pCoreOf 2 _).trans hle
    have hM'eq : M' = M := (hh.isUniqueM_F4 h331).2 M'
      ⟨hM', sup_le (le_sup_right.trans (le_sup_left.trans hsup)) (le_sup_right.trans hsup)⟩
    exact hnotM (hM'eq ▸ (le_sup_left.trans (le_sup_left.trans hsup)))
  have hhyp : Hyp111 Kp L T := by
    refine ⟨⟨inferInstance, hh.sylow.1, hTNKp, hTKp, hlistKp, hBL, hc2⟩,
      ⟨inferInstance, hh.sylow.1, hh.T_le_normalizer, hTL, hlistL, hBpL, hc1⟩, hO2⟩
  have hqt : IsQuasithinSub (Kp ⊔ L ⊔ T) := by
    intro p hp hp2 R _ hR hR2
    exact (CFSG.SectionRank.pRank_mono hp.one_lt inf_le_right).trans
      (pRank_le_two_of_isTwoLocal hh.qtke hp hp2 ⟨R, hR, hR2, rfl⟩)
  have hnorm : (T.subgroupOf (T ⊔ borelOf Kp T)).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer le_sup_left).mpr
      (sup_le Subgroup.le_normalizer hBp)
  have hLns : ¬ Group.IsSolvable ↥L := by
    rw [isSolvable_iff_perfectCore_eq_bot, perfectCore_eq_self_of_perfect hh.commutator_eq]
    intro hL
    have := hh.isSimple
    have hnt : Nontrivial (↥L ⧸ CFSG.pCore 2 ↥L) := IsSimpleGroup.toNontrivial
    obtain ⟨x, y, hxy⟩ := hnt.exists_pair_ne
    apply hxy
    induction x using QuotientGroup.induction_on with
    | H x =>
      induction y using QuotientGroup.induction_on with
      | H y =>
        have hall : ∀ z : ↥L, z = 1 := fun z => Subtype.ext (by
          have h1 : (z : G) ∈ (⊥ : Subgroup G) := by rw [← hL]; exact z.2
          exact Subgroup.mem_bot.mp h1)
        rw [hall x, hall y]
  obtain ⟨hTKp', -⟩ := hDS G Kp L T hhyp hqt (Or.inl hnorm) ⟨a, ha, ⟨eKp.symm.trans eSz⟩⟩ hLns

  have hTK : IsSylowTwoOf (T ⊓ K) K :=
    A4.isSylowTwoOf_inf_normal hTMp Subgroup.le_normalizer le_rfl
  have hZ := h.center_K hE9
  have hTKO : T ⊓ K ≤ pCoreOf 2 K := fun x hx =>
    mem_pCoreOf_of_mem_centralizerModO2 hZ hx.2 (le_of_mem_cComp hKp (hTKp' hx.1))
  have hdvd : (CFSG.pCore 2 ↥K).index ∣ ((T ⊓ K).subgroupOf K).index := by
    apply Subgroup.index_dvd_of_le
    intro x hx
    rw [Subgroup.mem_subgroupOf] at hx
    obtain ⟨z, hz, hzx⟩ := hTKO hx
    have : z = x := Subtype.ext hzx
    rw [← this]
    exact hz
  have hcard : (CFSG.pCore 2 ↥K).index = 20160 := by
    rw [Subgroup.index, ← card_of_lieModel_L34 h.l34]
  rw [hcard] at hdvd
  exact hTK.2.2 ((show (2 : ℕ) ∣ 20160 by norm_num).trans hdvd)

end Hyp5_1_14

end Components

theorem stmt5_1_16_of_inputs_F4
    (h5114 : Stmt5_1_14_first_F4) (h331 : Stmt3_3_1_F4) (h36 : A36ForSQTK)
    (h37 : A37ForSQTK) (h39 : A39ForSQTK) (hE9 : L34ElemNineFact)
    (hSz : SimpleThreePrimeSuzukiFact) (hSzA : SzTwoAutInnerFact) (hL2 : L2PerfectThreePrimeFact)
    (hDS : DSSzStatement_F4) : Stmt5_1_16_F4 := by
  intro G _ _ T M L V H B D n hyp hN hV hK
  have h : Hyp5_1_14 G T M L V H B D n := ⟨hyp, hN, hV, hK⟩
  refine ⟨h.not_three_dvd_F4 h5114 hE9, fun hns => ?_⟩
  obtain ⟨Kp, hKp⟩ := exists_mem_cComp_of_not_isSolvable' hns
  have hPC := h.perfectCore_eq_F4 h5114 hE9 h36 h37 h39 hSz hKp
  obtain ⟨-, k, hk⟩ := h.suzuki_cComp_F4 h5114 hE9 h36 hSz hKp
  refine ⟨⟨k, hPC ▸ hk⟩, hPC ▸ h.not_le_M_F4 h5114 h331 hE9 h36 h37 h39 hSz hL2 hKp,
    h.not_D_le_F4 h5114 h331 hE9 h36 h37 h39 hSz hSzA hL2 hDS hKp⟩

end CFSG.Quasithin.H13
