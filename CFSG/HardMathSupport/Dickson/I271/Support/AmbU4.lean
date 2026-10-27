module

public import CFSG.HardMathSupport.Dickson.I271.Support.AmbEngine
public import CFSG.LocalAnalysis.GLTheoremA.PartI.U42
public import CFSG.LocalAnalysis.GLTheoremB.InputPiGenProof
public import CFSG.LieType.Multipliers.U42
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.CenterHopf
public import CFSG.HardMathSupport.Timmesfeld.DefChar.CoreOrth
public import CFSG.LocalAnalysis.AGLEmbeddingD2.KFactSeitzRankThree
public import CFSG.HardMathSupport.Dickson.I271.Support.AmbBase

public section

namespace CFSG.HardMathSupport.Dickson.I271.Amb

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.HardMathSupport.Solomon.LocalBalance
  CFSG.HardMathSupport.Solomon.Coordinator CFSG.HardMathSupport.Dickson.I271
  CFSG.HardMathSupport.Timmesfeld.ComponentBalance CFSG.LocalAnalysis.GLTheoremA
  CFSG.Yardstones.Md0ec50421ce4

section Carrier

abbrev U4Group (q : TauCeti.PrimePower) (hv : (TauCeti.LieTypeIndex.twistedA 3 q).Valid) : Type :=
  (TauCeti.CFSGIndex.lie ⟨.twistedA 3 q, hv⟩).Group

variable {q : TauCeti.PrimePower} {hv : (TauCeti.LieTypeIndex.twistedA 3 q).Valid}

theorem u4_p_exponent (hq : q.card = 2) : q.p = 2 ∧ q.exponent = 1 := by
  have hcard : q.p ^ q.exponent = 2 := by rw [← TauCeti.PrimePower.card_def]; exact hq
  have hp : q.p = 2 := by
    have hdvd : q.p ∣ 2 := by
      rw [← hcard]
      exact dvd_pow_self q.p q.exponent_pos.ne'
    exact (Nat.prime_dvd_prime_iff_eq q.prime_p Nat.prime_two).1 hdvd
  refine ⟨hp, ?_⟩
  rw [hp] at hcard
  exact Nat.pow_right_injective (le_refl 2) (show 2 ^ q.exponent = 2 ^ 1 by simpa using hcard)

theorem u4_statedModel (hq : q.card = 2) : StatedClassicalModel (U4Group q hv) .PSU 4 2 1 := by
  obtain ⟨hp, hf⟩ := u4_p_exponent hq
  have h := CFSG.QuasithinUnique.SQTK.statedClassicalModel_twistedA 3 q hv
    (MulEquiv.refl (U4Group q hv))
  rw [hp, hf] at h
  exact h

theorem u4_lieModel (hq : q.card = 2) : Blueprint.LieModel (U4Group q hv) .PSU 4 2 1 :=
  Or.inl ⟨by decide, u4_statedModel hq⟩

theorem u4_card (hq : q.card = 2) :
    Nat.card (MulAut (U4Group q hv)) = 51840 ∧ Nat.card (U4Group q hv) = 25920 :=
  CFSG.EvenSporadicStandard.M22Std.card_mulAut_of_lieModel_psu42 (u4_lieModel hq)

theorem u4_center_eq_bot
    (hq : q.card = 2) {K : Type} [Group K] [Finite K] (hK : CFSG.Open.IsQuasisimple K)
    (hZp : IsPGroup 3 (Subgroup.center K))
    (e : K ⧸ Subgroup.center K ≃* U4Group q hv) : Subgroup.center K = ⊥ := by
  haveI : Fact (3 : ℕ).Prime := ⟨Nat.prime_three⟩
  obtain ⟨-, ⟨eM⟩⟩ := CFSG.LieType.Multipliers.U42.multiplier_PSU_four_two (U4Group q hv)
    (u4_lieModel hq)
  have hdvd := CFSG.AGLEmbedding.card_center_dvd_card_griessHopfMultiplier ⟨hK.1⟩ e
  rw [Nat.card_congr eM.toEquiv, Nat.card_congr Multiplicative.toAdd, Nat.card_zmod] at hdvd
  obtain ⟨k, hk⟩ := hZp.exists_card_eq
  have hk0 : k = 0 := by
    by_contra h
    have h3 : 3 ∣ 3 ^ k := dvd_pow_self 3 h
    rw [← hk] at h3
    have := h3.trans hdvd
    omega
  exact Subgroup.eq_bot_of_card_eq _ (by rw [hk, hk0]; rfl)

theorem u4_inner_of_pow_three (hq : q.card = 2) {S : Type}
    [Group S] [Finite S] (hZS : Subgroup.center S = ⊥) (e : S ≃* U4Group q hv)
    (α : MulAut S) (hα : α ^ 3 = 1) : α ∈ innerAut S := by
  obtain ⟨hAut, hG⟩ := u4_card (hv := hv) hq
  have hAutS : Nat.card (MulAut S) = 51840 := by
    rw [Nat.card_congr (MulAut.congr e).toEquiv]; exact hAut
  have hSS : Nat.card S = 25920 := by rw [Nat.card_congr e.toEquiv]; exact hG
  set Inn : Subgroup (MulAut S) := (MulAut.conj : S →* MulAut S).range with hInn
  have hInnCard : Nat.card Inn = 25920 := by
    rw [← hSS]
    exact (Nat.card_congr (MonoidHom.ofInjective
      (conj_injective_of_center_bot hZS)).toEquiv).symm
  have hidx : Inn.index = 2 := by
    have h := Subgroup.index_mul_card Inn
    rw [hInnCard, hAutS] at h
    omega
  haveI : Inn.Normal := CFSG.ComponentClassification.OuterAutomorphisms.inner_normal S
  have h1 := Subgroup.pow_index_mem Inn α
  rw [hidx] at h1
  have h2 : α ^ 2 = α⁻¹ := by
    rw [eq_inv_iff_mul_eq_one, ← pow_succ]
    exact hα
  rw [h2] at h1
  have h3 : α⁻¹⁻¹ ∈ Inn := Inn.inv_mem h1
  rw [inv_inv] at h3
  exact h3

theorem u4_coreFree {X : Type} [Group X] [Finite X] (hq : q.card = 2) {K : Subgroup X}
    (hK : CFSG.Open.IsQuasisimple ↥K) (e : ↥K ⧸ Subgroup.center ↥K ≃* U4Group q hv) :
    CoreFreeInner 3 K := by
  have hm : StatedClassicalModel (↥K ⧸ Subgroup.center ↥K) .PSp 2 3 1 :=
    CFSG.GH74.Exceptional.statedClassicalModel_PSp_two_three_of_PSU_four_two
      (CFSG.Open.StatedAPI.statedClassicalModel_of_mulEquiv e.symm (u4_statedModel hq))
  exact CFSG.HardMathSupport.Timmesfeld.DefChar.innerCoreFree_PSp_two hK.2
    (exists_noncomm_of_isQuasisimple hK) hm (by norm_num)

theorem u4_noComp {X : Type} [Group X] [Finite X] (hq : q.card = 2)
    {K : Subgroup X} (e : ↥K ⧸ Subgroup.center ↥K ≃* U4Group q hv) : NoCompInner 3 K := by
  intro β hβ3 hβ1 _
  have hβ' : MulAut.congr e β ^ 3 = 1 := by rw [← map_pow, hβ3, map_one]
  have hβ'1 : MulAut.congr e β ≠ 1 := fun h =>
    hβ1 ((MulAut.congr e).injective (h.trans (map_one _).symm))
  have hsol := u42_fixSubgroup_solvable q hv hq (MulAut.congr e β) hβ' hβ'1
  rw [fixSubgroup_congr] at hsol
  refine le_antisymm ?_ bot_le
  unfold GLAPLayer
  refine sSup_le fun L hL => ?_
  exfalso
  have h1 := glaPComponent_map Nat.prime_three e.toMonoidHom
    (coprime_ker_of_mulEquiv e (fixSubgroup β)) hL
  have hJ : L.map e.toMonoidHom = ⊥ :=
    eq_bot_of_perfect_of_solvable hsol h1.1 (glaPComponent_perfect h1)
  exact glaPComponent_ne_bot' hL
    ((Subgroup.map_eq_bot_iff_of_injective (f := e.toMonoidHom) _ e.injective).1 hJ)

theorem u4_sylow_elem (hq : q.card = 2) :
    ∃ (E₀ : Subgroup (U4Group q hv)) (P₀ : Sylow 3 (U4Group q hv)), IsElemAbelian 3 E₀ ∧
      3 ^ 2 ≤ Nat.card E₀ ∧ E₀ ≤ (P₀ : Subgroup (U4Group q hv)) ∧
        (P₀ : Subgroup (U4Group q hv)) ≤ Subgroup.normalizer (E₀ : Set (U4Group q hv)) := by
  haveI : Fact (3 : ℕ).Prime := ⟨Nat.prime_three⟩
  obtain ⟨-, hG⟩ := u4_card (hv := hv) hq
  haveI : Finite (U4Group q hv) := Nat.finite_of_card_ne_zero (by rw [hG]; norm_num)
  obtain ⟨-, F, _, _, hF, ⟨eF⟩⟩ := u4_statedModel (hv := hv) hq
  have h3 : 3 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup (U4Group q hv)) := by
    rw [CFSG.SectionRank.pRank_top_eq_of_mulEquiv (by norm_num) eF]
    exact CFSG.AGLEmbeddingD2.three_le_pRank_psu_four_two (by rw [hF]; rfl)
  obtain ⟨E, -, hE, hEcard⟩ := CFSG.SectionRank.exists_pRank (by norm_num : 1 < 3)
    (⊤ : Subgroup (U4Group q hv))
  obtain ⟨P₀, hEP⟩ := (isPGroup_of_isElemAbelian hE).exists_le_sylow
  have hP : Nat.card (P₀ : Subgroup (U4Group q hv)) = 81 := by
    rw [Sylow.card_eq_multiplicity, hG, show (25920 : ℕ).factorization 3 = 4 by decide +kernel]
    norm_num
  have hle : Nat.card E ≤ 81 := hP ▸ Subgroup.card_le_of_le hEP
  have hm : CFSG.Open.pRank 3 (⊤ : Subgroup (U4Group q hv)) ≤ 4 := by
    by_contra hlt
    have : 3 ^ 5 ≤ 3 ^ CFSG.Open.pRank 3 (⊤ : Subgroup (U4Group q hv)) :=
      Nat.pow_le_pow_right (by norm_num) (by omega)
    rw [← hEcard] at this
    omega
  refine ⟨E, P₀, hE, ?_, hEP, ?_⟩
  · rw [hEcard]
    calc 3 ^ 2 ≤ 3 ^ 3 := Nat.pow_le_pow_right (by norm_num) (by norm_num)
      _ ≤ 3 ^ CFSG.Open.pRank 3 (⊤ : Subgroup (U4Group q hv)) :=
        Nat.pow_le_pow_right (by norm_num) h3
  · rcases (by omega : CFSG.Open.pRank 3 (⊤ : Subgroup (U4Group q hv)) = 3 ∨
        CFSG.Open.pRank 3 (⊤ : Subgroup (U4Group q hv)) = 4) with h | h
    · rw [h] at hEcard
      have hrel := Subgroup.relIndex_mul_card E (P₀ : Subgroup (U4Group q hv))
      rw [inf_of_le_left hEP, hP, hEcard] at hrel
      have hidx : E.relIndex (P₀ : Subgroup (U4Group q hv)) = 3 := by omega
      have : (E.subgroupOf (P₀ : Subgroup (U4Group q hv))).Normal :=
        Subgroup.normal_of_index_eq_minFac_card (by
          have h81 : Nat.card ↥(P₀ : Subgroup (U4Group q hv)) = 81 := hP
          rw [h81, show Nat.minFac 81 = 3 by norm_num]
          exact hidx)
      exact (Subgroup.normal_subgroupOf_iff_le_normalizer hEP).1 this
    · rw [h] at hEcard
      have hEq : E = (P₀ : Subgroup (U4Group q hv)) :=
        Subgroup.eq_of_le_of_card_ge hEP (by rw [hP, hEcard]; norm_num)
      rw [← hEq]
      exact Subgroup.le_normalizer

end Carrier

section Case

variable {X : Type} [Group X] [Finite X]

theorem u4Case
    {q : TauCeti.PrimePower}
    {hv : (TauCeti.LieTypeIndex.twistedA 3 q).Valid} (hq2 : q.card = 2) {K B : Subgroup X}
    (hcore : GLAPPrimeCore 3 X = ⊥) (hcomp : GLAPComponent 3 ⊤ K) (hscp : IsSCp 3 ⊤ B)
    (hBN : B ≤ Subgroup.normalizer (K : Set X))
    (e : ↥K ⧸ Subgroup.center ↥K ≃* U4Group q hv) : IsStronglyBalancedIn 3 B K := by
  have hp : (3 : ℕ).Prime := Nat.prime_three
  haveI : Fact (3 : ℕ).Prime := ⟨hp⟩
  have hBel : IsElemAbelian 3 B := hscp.2.1
  have hq : CFSG.Open.IsQuasisimple ↥K := i116e_isQuasisimple hcore hcomp
  haveI : Group.IsPerfect ↥K := ⟨hq.1⟩
  have hOK : GLAPPrimeCore 3 ↥K = ⊥ := i271h_primeCore_eq_bot hcore hcomp
  have hZp : IsPGroup 3 (Subgroup.center ↥K) := isPGroup_center hp hOK
  have h3K : 3 ∣ Nat.card K := i116e_dvd_card hp hcore hcomp
  have hZ : Subgroup.center ↥K = ⊥ := u4_center_eq_bot hq2 hq hZp e
  obtain ⟨r, hr⟩ := exists_pow_autOrderIn hp hBel hBN
  obtain ⟨x, hxB, hxK, hx1, hxp⟩ := exists_mem_inf_of_isSCp hp hscp hBN h3K
  have hone : autOrderIn B K = 1 ↔ B ≤ Subgroup.centralizer (K : Set X) := by
    unfold autOrderIn
    rw [inf_of_le_left hBN, Subgroup.relIndex_eq_one]
  have hxC : x ∉ Subgroup.centralizer (K : Set X) := fun h =>
    hx1 (eq_one_of_mem_centralizer hZ hxK h)
  have hne1 : autOrderIn B K ≠ 1 := fun h => hxC ((hone.1 h) hxB)
  by_cases hr1 : r = 1
  ·
    exfalso
    have hcard : autOrderIn B K = 3 := by simpa [hr1] using hr
    obtain ⟨E₀, P₀, hE, h2, hEP, hPN⟩ := u4_sylow_elem (hv := hv) hq2
    let eK : ↥K ≃* U4Group q hv := mulEquivOfCenterBot hZ e
    haveI : Finite (U4Group q hv) := Finite.of_equiv ↥K eK.toEquiv
    have hx₁p : eK ⟨x, hxK⟩ ^ 3 = 1 := by
      rw [← map_pow]
      have : (⟨x, hxK⟩ : ↥K) ^ 3 = 1 := Subtype.ext (by simpa using hxp)
      rw [this, map_one]
    have hx₁1 : eK ⟨x, hxK⟩ ≠ 1 := by
      intro h
      apply hx1
      have := eK.injective (h.trans (map_one eK).symm)
      exact congrArg Subtype.val this
    obtain ⟨y₁, hy₁p, hy₁n, hy₁c⟩ := exists_comm_outside_zpowers hp hE h2 hEP hPN hx₁p hx₁1
    set y₀ : ↥K := eK.symm y₁ with hy₀
    refine cyclic_contra hp hscp hBN hZ hcard hxB hxK hx1 (y := (y₀ : X)) y₀.2 ?_ ?_ ?_
    · have : y₀ ^ 3 = 1 := by
        apply eK.injective
        rw [map_pow, hy₀, MulEquiv.apply_symm_apply, map_one]
        exact hy₁p
      simpa using congrArg Subtype.val this
    · have : y₀ * ⟨x, hxK⟩ = ⟨x, hxK⟩ * y₀ := by
        apply eK.injective
        rw [map_mul, map_mul, hy₀, MulEquiv.apply_symm_apply]
        exact hy₁c
      exact congrArg Subtype.val this
    · intro hmem
      apply hy₁n
      obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.1 hmem
      refine Subgroup.mem_zpowers_iff.2 ⟨n, ?_⟩
      have : y₀ = ⟨x, hxK⟩ ^ n := Subtype.ext (by simpa using hn.symm)
      rw [← map_zpow, ← this, hy₀, MulEquiv.apply_symm_apply]
  ·
    have hr2 : 2 ≤ r := by
      rcases r with _ | _ | r
      · exact absurd (by simpa using hr) hne1
      · exact absurd rfl hr1
      · omega
    have h2 : 3 ^ 2 ≤ autOrderIn B K := by
      rw [hr]
      exact Nat.pow_le_pow_right (by norm_num) hr2
    obtain ⟨A, hAB, hAnc, hAf⟩ := exists_faithful_noncyclic hp hBel hBN h2
    haveI : IsSimpleGroup (↥K ⧸ Subgroup.center ↥K) := hq.2
    have hZS : Subgroup.center (↥K ⧸ Subgroup.center ↥K) = ⊥ :=
      center_eq_bot_of_simple (exists_noncomm_of_isQuasisimple hq)
    have hin : ∀ a ∈ A, ∃ k ∈ K, k⁻¹ * a ∈ Subgroup.centralizer (K : Set X) := by
      intro a ha
      have haN : a ∈ Subgroup.normalizer (K : Set X) := hBN (hAB ha)
      have hap : a ^ 3 = 1 := hBel.2 a (hAB ha)
      have hα : actHom K ⟨a, haN⟩ ^ 3 = 1 := by
        rw [← map_pow]
        have : (⟨a, haN⟩ : ↥(Subgroup.normalizer (K : Set X))) ^ 3 = 1 :=
          Subtype.ext (by simpa using hap)
        rw [this, map_one]
      exact exists_inner_of_actHom_mem_innerAut' hq.1 haN
        (u4_inner_of_pow_three hq2 hZS e _ hα)
    exact engineInner hp (by norm_num) hcore hcomp hscp (u4_coreFree hq2 hq e) (u4_noComp hq2 e)
      hBN ⟨A, hAB, hAnc, hAf, hin⟩

end Case

end CFSG.HardMathSupport.Dickson.I271.Amb
