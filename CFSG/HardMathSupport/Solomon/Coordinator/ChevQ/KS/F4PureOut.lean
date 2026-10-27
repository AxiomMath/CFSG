module

public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.KS.F4InnerComp
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.KS.F4PureRank
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.KS.F4PureCount
public import CFSG.HardMathSupport.Dickson.I271.I202Full
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.KS.CompSLOB

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.ChevQ

namespace KSF4Pure

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.HardMathSupport.Solomon.LocalBalance
  CFSG.HardMathSupport.Dickson.I271 CFSG.HardMathSupport.Solomon.Coordinator
open scoped commutatorElement

set_option linter.unusedSectionVars false

@[expose] def SUTypeAt {X : Type} [Group X] (K : Subgroup X) (b : X) : Prop :=
  ¬ ∀ J : Subgroup X, GLAPComponent 3 (K ⊓ Subgroup.centralizer ({b} : Set X)) J →
    IsLieQuot ↥J KSF4Out.IsB3EightIndex

@[expose] def PureAt {X : Type} [Group X] (K B : Subgroup X) : Prop :=
  ∀ b ∈ B, Bal209F4Aux.InnerAt K b → b ∉ Subgroup.centralizer (K : Set X) → SUTypeAt K b

@[expose] def F4InnerCompOutP : Prop :=
  ∀ (X : Type) [Group X] [Finite X], CFSG.Open.IsKGroup X →
    ∀ (K B : Subgroup X) (a : X),
      CFSG.Open.IsComponentOf K ⊤ → IsSCp 3 ⊤ B →
        B ≤ Subgroup.normalizer (K : Set X) → GLATwoLocalRank 3 X ≤ CFSG.Open.pRank 3 B →
          IsLieQuot ↥K IsF4EightIndex → ¬ InducesInnerIn B K → a ∈ B →
            a ∉ Subgroup.centralizer (K : Set X) → Bal209F4Aux.InnerAt K a →
              (¬ SUTypeAt K a ∨ PureAt K B) →
              ∀ J : Subgroup X, GLAPComponent 3 (K ⊓ Subgroup.centralizer ({a} : Set X)) J →
                B ≤ Subgroup.normalizer (J : Set X) ∧ IsStronglyLocallyOneBalanced 3 B a J

@[expose] def F4SU3Rank3P : Prop :=
  ∀ (X : Type) [Group X] [Finite X], CFSG.Open.IsKGroup X → ∀ (K B : Subgroup X) (a : X),
    CFSG.Open.IsComponentOf K ⊤ → IsSCp 3 ⊤ B → B ≤ Subgroup.normalizer (K : Set X) →
      GLATwoLocalRank 3 X ≤ CFSG.Open.pRank 3 B → IsLieQuot ↥K IsF4EightIndex →
        ¬ InducesInnerIn B K → a ∈ B → a ∉ Subgroup.centralizer (K : Set X) →
          Bal209F4Aux.InnerAt K a → PureAt K B →
            ∀ J : Subgroup X, GLAPComponent 3 (K ⊓ Subgroup.centralizer ({a} : Set X)) J →
              B ≤ Subgroup.normalizer (J : Set X) → IsLieQuot ↥J KSF4SU3.IsU3EightIndexTwo →
                KSF4SU3.AutImageRankThree B J

@[expose] def F4InnerPartCount : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (K B : Subgroup X) (hBN : B ≤ Subgroup.normalizer (K : Set X)),
    CFSG.Open.IsComponentOf K ⊤ → IsSCp 3 ⊤ B → GLATwoLocalRank 3 X ≤ CFSG.Open.pRank 3 B →
      IsLieQuot ↥K IsF4EightIndex → ∀ x ∈ B, ¬ Bal209F4Aux.InnerAt K x →
        27 ≤ Nat.card ↥(KSF4Rank.innerPart hBN)

section Rank3

open CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.KSF4Rank


theorem suTypeK_of_pure {X : Type} [Group X] [Finite X] {K B : Subgroup X}
    (hBN : B ≤ Subgroup.normalizer (K : Set X)) (hZ : Subgroup.center ↥K = ⊥)
    (hpure : PureAt K B) {e : ↥K} (he : e ∈ innerPart hBN) (he1 : e ≠ 1) : SUTypeK e := by
  classical
  obtain ⟨b, hb, hbe⟩ := mem_innerPart'.1 he
  have hbI : Bal209F4Aux.InnerAt K b := innerAt_of_conj_eq e.2 (fun y hy => hbe ⟨y, hy⟩)
  have hbC : b ∉ Subgroup.centralizer (K : Set X) := by
    intro hbc
    apply he1
    have hec : e ∈ Subgroup.center ↥K := by
      rw [Subgroup.mem_center_iff]
      intro g
      apply Subtype.ext
      have h1 := hbe g
      have h2 : b * (g : X) = (g : X) * b :=
        (Subgroup.mem_centralizer_iff.1 hbc (g : X) g.2).symm
      have h3 : b * (g : X) * b⁻¹ = (g : X) := by rw [h2]; group
      rw [h3] at h1
      show (g : X) * (e : X) = (e : X) * (g : X)
      calc (g : X) * (e : X) = ((e : X) * (g : X) * (e : X)⁻¹) * (e : X) := by rw [← h1]
        _ = (e : X) * (g : X) := by group
    rw [hZ] at hec
    exact Subgroup.mem_bot.1 hec
  have hSU := hpure b hb hbI hbC
  intro hall
  apply hSU
  intro J hJ
  have haN : b ∈ Subgroup.normalizer (K : Set X) := hBN hb
  have hJK : J ≤ K := hJ.1.trans inf_le_left
  have hα : K.normalizerMonoidHom ⟨b, haN⟩ = MulAut.conj e := by
    refine MulEquiv.ext fun y => Subtype.ext ?_
    exact hbe y
  have hJ' : GLAPComponent 3 (Subgroup.centralizer ({e} : Set ↥K)) (J.subgroupOf K) := by
    have h1 := glaPComponent_fixSubgroup Nat.prime_three haN hJ
    rwa [hα, fixSubgroup_conj_eq'] at h1
  exact Bal209F4Aux.isLieQuot_mulEquiv (Subgroup.subgroupOfEquivOfLe hJK) (hall _ hJ')

theorem f4SU3Rank3P_of_pure (hCnt : F4InnerPartCount) (hPR : F4EightPureRank)
    (hOut : KSF4Rank.F4OutStatement) (hFix : Bal209F4Aux.F4Fixed)
    (hNo19 : KSF4Rank.F4TwoNoNineteen) : F4SU3Rank3P := by
  intro X _ _ hKG K B a hK hBSC hBN hrank hLie hunin haB haC hinn hpure J hJ hBJ hJL
  classical
  have hBel : IsElemAbelian 3 B := hBSC.2.1
  have hperf : ⁅J, J⁆ = J := glaPComponent_perfect hJ
  have hJK : J ≤ K := hJ.1.trans inf_le_left
  have haN : a ∈ Subgroup.normalizer (K : Set X) := hBN haB
  obtain ⟨hZ, -⟩ := hOut ↥K hK.2.2 hLie
  obtain ⟨x, hx, hxI⟩ : ∃ x ∈ B ⊓ Subgroup.normalizer (K : Set X), ¬ Bal209F4Aux.InnerAt K x := by
    by_contra hcon
    push Not at hcon
    exact hunin (fun b hb => hcon b hb)
  have hxB : x ∈ B := hx.1
  have hEel := isElemAbelian_innerPart hZ hBel hBN
  have h27 := hCnt X K B hBN hK hBSC hrank hLie x hxB hxI
  have hC : ∀ y ∈ B, ¬ Bal209F4Aux.InnerAt K y → y ∉ Subgroup.centralizer (J : Set X) := by
    intro y hyB hyI hyC
    obtain ⟨hsimp, hq, -, hLieF⟩ := hFix X K y hK hLie (hBN hyB) (hBel.2 y hyB) hyI
    have hJle : J ≤ K ⊓ Subgroup.centralizer ({y} : Set X) := by
      refine le_inf hJK (fun j hj => ?_)
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact Subgroup.mem_centralizer_iff.1 hyC j hj
    exact hNo19 _ hsimp hq hLieF ((nineteen_dvd_card hJL).trans (Subgroup.card_dvd_of_le hJle))
  obtain ⟨k0, hk0K, hk0c⟩ := hinn
  let k : ↥K := ⟨k0, hk0K⟩
  have hakc : ∀ y : X, y ∈ K → a * y * a⁻¹ = k0 * y * k0⁻¹ := fun y hy => conj_eq_of_inner hk0c hy
  have hkE : k ∈ innerPart hBN := mem_innerPart'.2 ⟨a, haB, fun y => hakc y y.2⟩
  have hk3 : orderOf k = 3 := by
    haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    refine orderOf_eq_prime (hEel.2 k hkE) ?_
    intro h
    apply haC
    have hk1' : k0 = 1 := congrArg Subtype.val h
    have h' : k0⁻¹ * a = a := by rw [hk1']; simp
    rw [← h']
    exact hk0c
  have hα : K.normalizerMonoidHom ⟨a, haN⟩ = MulAut.conj k := by
    refine MulEquiv.ext fun y => Subtype.ext ?_
    exact hakc y y.2
  have hJ' : GLAPComponent 3 (Subgroup.centralizer ({k} : Set ↥K)) (J.subgroupOf K) := by
    have h1 := glaPComponent_fixSubgroup Nat.prime_three haN hJ
    rwa [hα, fixSubgroup_conj_eq'] at h1
  have hJ'L : IsLieQuot ↥(J.subgroupOf K) KSF4SU3.IsU3EightIndexTwo :=
    Bal209F4Aux.isLieQuot_mulEquiv (Subgroup.subgroupOfEquivOfLe hJK).symm hJL
  have hpureE : ∀ e ∈ innerPart hBN, e ≠ 1 → SUTypeK e := fun e he he1 =>
    suTypeK_of_pure hBN hZ hpure he he1
  have h9 := hPR ↥K hK.2.2 hLie k hk3 (J.subgroupOf K) hJ' hJ'L (innerPart hBN) hEel hkE
    hpureE h27
  set N := Subgroup.normalizer (J : Set X) with hN
  have hEN : ∀ e : ↥(innerPart hBN), ((e : ↥K) : X) ∈ N := by
    intro e
    obtain ⟨b, hb, hbe⟩ := mem_innerPart'.1 e.2
    rw [hN, Subgroup.mem_normalizer_iff]
    intro h
    constructor
    · intro hh
      have hhK : h ∈ K := hJK hh
      have h1 := hbe ⟨h, hhK⟩
      have h2 := (Subgroup.mem_normalizer_iff.1 (hBJ hb) h).1 hh
      rw [← h1]
      exact h2
    · intro hh
      have hhK : h ∈ K := by
        have : ((e : ↥K) : X)⁻¹ * (((e : ↥K) : X) * h * ((e : ↥K) : X)⁻¹) * ((e : ↥K) : X) ∈ K :=
          K.mul_mem (K.mul_mem (K.inv_mem (e : ↥K).2) (hJK hh)) (e : ↥K).2
        have hh' : ((e : ↥K) : X)⁻¹ * (((e : ↥K) : X) * h * ((e : ↥K) : X)⁻¹) *
            ((e : ↥K) : X) = h := by group
        rwa [hh'] at this
      have h1 := hbe ⟨h, hhK⟩
      have h2 : b * h * b⁻¹ ∈ J := by
        have : b * h * b⁻¹ = ((e : ↥K) : X) * h * ((e : ↥K) : X)⁻¹ := h1
        rw [this]
        exact hh
      exact (Subgroup.mem_normalizer_iff.1 (hBJ hb) h).2 h2
  let ι : ↥(innerPart hBN) →* ↥N :=
    MonoidHom.codRestrict ((K.subtype).comp (innerPart hBN).subtype) N hEN
  let ε : ↥(innerPart hBN) →* MulAut (↥J ⧸ Subgroup.center ↥J) := (actHom J).comp ι
  have hεe : ∀ (e : ↥(innerPart hBN)) (b : X) (hb : b ∈ B),
      (∀ y : ↥K, b * (y : X) * b⁻¹ = ((e : ↥K) : X) * (y : X) * ((e : ↥K) : X)⁻¹) →
        ε e = actHom J ⟨b, hBJ hb⟩ := by
    intro e b hb hbe
    refine MulEquiv.ext fun q => ?_
    induction q using QuotientGroup.induction_on with
    | H j =>
      show actHom J ⟨((e : ↥K) : X), hEN e⟩ (QuotientGroup.mk j) =
        actHom J ⟨b, hBJ hb⟩ (QuotientGroup.mk j)
      rw [actHom_mk, actHom_mk]
      congr 1
      exact Subtype.ext (hbe ⟨j, hJK j.2⟩).symm
  have hrange : ε.range ≤ autImage B J := by
    rintro _ ⟨e, rfl⟩
    obtain ⟨b, hb, hbe⟩ := mem_innerPart'.1 e.2
    rw [hεe e b hb hbe]
    exact mem_autImage.2 ⟨b, hBJ hb, hb, rfl⟩
  have hker : ε.ker ≤ (Subgroup.centralizer ((J.subgroupOf K : Subgroup ↥K) : Set ↥K)).subgroupOf
      (innerPart hBN) := by
    intro e he
    rw [MonoidHom.mem_ker] at he
    have hcent : ((e : ↥K) : X) ∈ Subgroup.centralizer (J : Set X) :=
      KSF4SU3.mem_centralizer_of_actHom_eq_one hperf (hEN e) he
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_centralizer_iff]
    intro j' hj'
    apply Subtype.ext
    exact Subgroup.mem_centralizer_iff.1 hcent (j' : X) hj'
  have h9' : 9 ≤ Nat.card ε.range := by
    rw [← Subgroup.index_ker]
    refine h9.trans (Nat.le_of_dvd (Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite)
      (Subgroup.index_dvd_of_le hker))
  set A := autImage B J with hA
  have hAel : IsElemAbelian 3 A := by
    have h1 : IsElemAbelian 3 (B ⊓ N) := CFSG.Open.IsElemAbelian.mono hBel inf_le_left
    exact (h1.subgroupOf N).map (actHom J)
  have hu : actHom J ⟨x, hBJ hxB⟩ ∈ A := mem_autImage.2 ⟨x, hBJ hxB, hxB, rfl⟩
  have hu' : actHom J ⟨x, hBJ hxB⟩ ∉ ε.range := by
    rintro ⟨e, he⟩
    obtain ⟨b, hb, hbe⟩ := mem_innerPart'.1 e.2
    have hεb := hεe e b hb hbe
    have heq : actHom J ⟨x, hBJ hxB⟩ = actHom J ⟨b, hBJ hb⟩ := he.symm.trans hεb
    have hxbN : x * b⁻¹ ∈ N := N.mul_mem (hBJ hxB) (N.inv_mem (hBJ hb))
    have hone : actHom J ⟨x * b⁻¹, hxbN⟩ = 1 := by
      have : (⟨x * b⁻¹, hxbN⟩ : ↥N) = ⟨x, hBJ hxB⟩ * ⟨b, hBJ hb⟩⁻¹ := rfl
      rw [this, map_mul, map_inv, heq, mul_inv_cancel]
    have hcent := KSF4SU3.mem_centralizer_of_actHom_eq_one hperf hxbN hone
    have hbI : Bal209F4Aux.InnerAt K b :=
      innerAt_of_conj_eq (e : ↥K).2 (fun y hy => hbe ⟨y, hy⟩)
    have hxbI : ¬ Bal209F4Aux.InnerAt K (x * b⁻¹) := by
      intro h
      apply hxI
      have h1 : x ∈ Bal209F4Aux.innerSub K := by
        have : x = (x * b⁻¹) * b := by group
        rw [this]
        exact (Bal209F4Aux.innerSub K).mul_mem (Bal209F4Aux.mem_innerSub.2 h)
          (Bal209F4Aux.mem_innerSub.2 hbI)
      exact Bal209F4Aux.mem_innerSub.1 h1
    exact hC (x * b⁻¹) (B.mul_mem hxB (B.inv_mem hb)) hxbI hcent
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨n, hn⟩ := (IsPGroup.iff_card).1 hAel.isPGroup
  have hPA : ε.range ≤ A := hrange
  have hdvd : Nat.card ε.range ∣ 3 ^ n := hn ▸ Subgroup.card_dvd_of_le hPA
  obtain ⟨m, hmn, hm⟩ := (Nat.dvd_prime_pow Nat.prime_three).1 hdvd
  have hm2 : 2 ≤ m := by
    by_contra hlt
    push Not at hlt
    have h3m : 3 ^ m ≤ 3 := calc 3 ^ m ≤ 3 ^ 1 := Nat.pow_le_pow_right (by norm_num) (by omega)
      _ = 3 := by norm_num
    omega
  have hmn' : m < n := by
    rcases lt_or_eq_of_le hmn with h | h
    · exact h
    · exfalso
      have heqA : ε.range = A :=
        Subgroup.eq_of_le_of_card_ge hPA (by rw [hn, hm, h])
      exact hu' (heqA ▸ hu)
  have h27 : 3 ^ 3 ∣ Nat.card ↥A := by
    rw [hn]
    exact pow_dvd_pow 3 (by omega)
  obtain ⟨K₀, hK₀⟩ := Sylow.exists_subgroup_card_pow_prime (G := ↥A) 3 h27
  refine ⟨K₀.map A.subtype, Subgroup.map_subtype_le _, hAel.mono (Subgroup.map_subtype_le _), ?_⟩
  rw [Subgroup.card_map_of_injective A.subtype_injective, hK₀]
  norm_num


end Rank3

section Out



theorem f4InnerCompOutP_of_rank3P (h207 : CFSG.HardMathSupport.Dickson.Bal207.Bal207Corr)
    (hClass : KSF4Out.F4EightClass) (hR : F4SU3Rank3P) : F4InnerCompOutP := by
  intro X _ _ hKG K B a hK hBSC hBN hrank hLie hunin haB haC hinn hP J hJ
  have hBel : CFSG.Open.IsElemAbelian 3 B := hBSC.2.1
  have haN : a ∈ Subgroup.normalizer (K : Set X) := hBN haB
  obtain ⟨hcomp, h3⟩ := hClass X K a hK hLie haN (hBel.2 a haB) haC hinn
  have hBJ : B ≤ Subgroup.normalizer (J : Set X) := fun b hb =>
    KSF4Kit.mem_normalizer_of_card_le_two hBel
      (𝒥 := {J' | GLAPComponent 3 (K ⊓ Subgroup.centralizer ({a} : Set X)) J'})
      (fun J₁ hJ₁ J₂ hJ₂ J₃ hJ₃ => h3 J₁ J₂ J₃ hJ₁ hJ₂ hJ₃)
      (fun b' hb' J' hJ' => KSF4Kit.glaPComponent_gLBConj_centralizer (hBN hb')
        (Bal209F4Aux.commute_of_elemAbelian hBel hb' haB).eq hJ') hb hJ
  refine ⟨hBJ, ?_⟩
  obtain ⟨hq, d, hd, e⟩ := hcomp J hJ
  have hSp : IsLieQuot ↥J KSF4Out.IsB3EightIndex → IsStronglyLocallyOneBalanced 3 B a J :=
    fun hB3 => KSCompSLOB.sLOB_of_bal207_component h207 hKG hBSC haB
      (KSF4Kit.isComponentOf_centralizer_of_glaPComponent hK hJ hq) hBJ
      KSF4Out.isB3Eight_bal207 hB3
  rcases hP with hnot | hpure
  · exact hSp (not_not.1 hnot J hJ)
  · rcases hd with hB3 | hU3
    · exact hSp ⟨d, hB3, e⟩
    · exact KSF4SU3.isStronglyLocallyOneBalanced_of_autImageRankThree
        (glaPComponent_perfect hJ) ⟨d, hU3, e⟩
        (hR X hKG K B a hK hBSC hBN hrank hLie hunin haB haC hinn hpure J hJ hBJ ⟨d, hU3, e⟩)

end Out

section Consumer

open Bal209F4Aux

theorem centralizer_eq_of_inner_mem_pairSub {X : Type} [Group X] {K : Subgroup X} {x y : X}
    (hxy : Commute x y) (hx3 : x ^ 3 = 1) (hy3 : y ^ 3 = 1) (hxI : x ∉ innerSub K)
    (hyI : y ∈ innerSub K) (hy1 : y ≠ 1) {a : X} (ha : a ∈ pairSub hxy) (haI : a ∈ innerSub K)
    (ha1 : a ≠ 1) :
    Subgroup.centralizer ({a} : Set X) = Subgroup.centralizer ({y} : Set X) := by
  have hx1 : x ≠ 1 := fun h => hxI (h ▸ (innerSub K).one_mem)
  obtain ⟨i, j, rfl⟩ := mem_pairSub.1 ha
  have hxi : x ^ i ∈ innerSub K := by
    have h2 : y ^ j ∈ innerSub K := (innerSub K).zpow_mem hyI j
    have h3 := (innerSub K).mul_mem haI ((innerSub K).inv_mem h2)
    simpa using h3
  have hi3 : (3 : ℤ) ∣ i := by
    by_contra hi
    exact hxI (mem_of_zpow_mem hx3 hx1 hi hxi)
  obtain ⟨t, rfl⟩ := hi3
  have hx3z : x ^ (3 : ℤ) = 1 := by simpa using hx3
  have hxt : x ^ (3 * t) = 1 := by rw [zpow_mul, hx3z, one_zpow]
  rw [hxt, one_mul] at ha1 ⊢
  have hj3 : ¬ (3 : ℤ) ∣ j := by
    rintro ⟨u, rfl⟩
    apply ha1
    have hy3z : y ^ (3 : ℤ) = 1 := by simpa using hy3
    rw [zpow_mul, hy3z, one_zpow]
  ext g
  rw [Subgroup.mem_centralizer_singleton_iff, Subgroup.mem_centralizer_singleton_iff]
  constructor
  · intro h
    have hyj : y ∈ Subgroup.zpowers (y ^ j) :=
      mem_of_zpow_mem hy3 hy1 hj3 (Subgroup.mem_zpowers _)
    obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.1 hyj
    have hc : Commute g (y ^ j) := h
    have := hc.zpow_right m
    rw [← zpow_mul] at this
    have e1 : (y ^ j) ^ m = y := hm
    rw [← zpow_mul] at e1
    rw [e1] at this
    exact this
  · intro h
    have hc : Commute g y := h
    exact hc.zpow_right j


theorem bal209F4Eight_of_inputs_outP (h207 : CFSG.HardMathSupport.Dickson.Bal207.Bal207Corr)
    (hLoc : Bal209F4Aux.F4LocalOne) (hFix : Bal209F4Aux.F4Fixed) (hInner : F4InnerCompOutP)
    (hEx : Bal209F4Aux.F4InnerEx) : Bal209F4Eight := by
  intro X _ _ hKG K B hK hBSC hBN hrank hIsLie hunin
  obtain ⟨x, hx, hxI⟩ : ∃ x ∈ B ⊓ Subgroup.normalizer (K : Set X), ¬ Bal209F4Aux.InnerAt K x := by
    by_contra hcon
    push Not at hcon
    exact hunin (fun b hb => hcon b hb)
  obtain ⟨y, hyB, hyI, hyC, hyP⟩ : ∃ y ∈ B, Bal209F4Aux.InnerAt K y ∧
      y ∉ Subgroup.centralizer (K : Set X) ∧ (¬ SUTypeAt K y ∨ PureAt K B) := by
    by_cases hpure : PureAt K B
    · obtain ⟨y, hyB, hyI, hyC⟩ := hEx X hKG K B hK hBSC hBN hrank hIsLie
      exact ⟨y, hyB, hyI, hyC, Or.inr hpure⟩
    · unfold PureAt at hpure
      push Not at hpure
      obtain ⟨y, hyB, hyI, hyC, hy⟩ := hpure
      exact ⟨y, hyB, hyI, hyC, Or.inl hy⟩
  have hBel : CFSG.Open.IsElemAbelian 3 B := hBSC.2.1
  have hxB : x ∈ B := hx.1
  have hxN : x ∈ Subgroup.normalizer (K : Set X) := hx.2
  have hx3 : x ^ 3 = 1 := hBel.2 x hxB
  have hy3 : y ^ 3 = 1 := hBel.2 y hyB
  have hx1 : x ≠ 1 := by
    intro h
    apply hxI
    rw [h]
    exact ⟨1, K.one_mem, by simp⟩
  have hy1 : y ≠ 1 := by
    intro h
    apply hyC
    rw [h]
    exact Subgroup.one_mem _
  have hxy : Commute x y := Bal209F4Aux.commute_of_elemAbelian hBel hxB hyB
  have hxI' : x ∉ Bal209F4Aux.innerSub K := fun h => hxI (Bal209F4Aux.mem_innerSub.1 h)
  have hyI' : y ∈ Bal209F4Aux.innerSub K := Bal209F4Aux.mem_innerSub.2 hyI
  have hAB : Bal209F4Aux.pairSub hxy ≤ B := Bal209F4Aux.pairSub_le hxy hxB hyB
  have hAel : CFSG.Open.IsElemAbelian 3 (Bal209F4Aux.pairSub hxy) :=
    Bal209F4Aux.isElemAbelian_pairSub hxy hBel hxB hyB
  have hnc : ¬ IsCyclic ↥(Bal209F4Aux.pairSub hxy) :=
    Bal209F4Aux.not_isCyclic_pairSub hxy hBel hxB hyB hx1 hy1 hxI' hyI'
  have hSC : IsSCp 3 (K ⊔ B) B :=
    ⟨le_sup_right, hBel, fun E _ hEel hBE => hBSC.2.2 E le_top hEel hBE⟩
  have hdvd : 3 ∣ Nat.card K := by
    obtain ⟨-, -, h3, -⟩ := hFix X K x hK hIsLie hxN hx3 hxI
    exact h3.trans (Subgroup.card_dvd_of_le inf_le_left)
  have hloc := hLoc X K (Bal209F4Aux.pairSub hxy) hK hIsLie (hAB.trans hBN) hAel
  have hb : ∀ a ∈ Bal209F4Aux.pairSub hxy, a ≠ 1 → ∀ J : Subgroup X,
      GLAPComponent 3 (K ⊓ Subgroup.centralizer ({a} : Set X)) J →
        B ≤ Subgroup.normalizer (J : Set X) ∧ IsStronglyLocallyOneBalanced 3 B a J := by
    intro a ha ha1 J hJ
    have haB : a ∈ B := hAB ha
    have haC : a ∉ Subgroup.centralizer (K : Set X) := fun h =>
      ha1 (Bal209F4Aux.eq_one_of_mem_pairSub_centralizer hxy hx3 hy3 hxI' hyI' hyC ha h)
    by_cases hinn : Bal209F4Aux.InnerAt K a
    · have hP : ¬ SUTypeAt K a ∨ PureAt K B := by
        rcases hyP with hnot | hpure'
        · left
          have hcen : Subgroup.centralizer ({a} : Set X) = Subgroup.centralizer ({y} : Set X) :=
            centralizer_eq_of_inner_mem_pairSub hxy hx3 hy3 hxI' hyI' hy1 ha
              (Bal209F4Aux.mem_innerSub.2 hinn) ha1
          unfold SUTypeAt at hnot ⊢
          rw [hcen]
          exact hnot
        · exact Or.inr hpure'
      exact hInner X hKG K B a hK hBSC hBN hrank hIsLie hunin haB haC hinn hP J hJ
    · obtain ⟨hsimp, hquasi, -, hLieF⟩ :=
        hFix X K a hK hIsLie (hAB.trans hBN ha) (hBel.2 a haB) hinn
      have hJeq : J = K ⊓ Subgroup.centralizer ({a} : Set X) :=
        Bal209F4Aux.eq_of_glaPComponent hsimp hJ
      subst hJeq
      have hBH : ∀ b ∈ B, b ∈ Subgroup.normalizer
          ((K ⊓ Subgroup.centralizer ({a} : Set X) : Subgroup X) : Set X) := fun b hb =>
        Bal209F4Aux.mem_normalizer_inf_centralizer (hBN hb) (hBN haB) (by
          rw [commutatorElement_eq_one_iff_mul_comm.2
            (Bal209F4Aux.commute_of_elemAbelian hBel hb haB)]
          exact Subgroup.one_mem _)
      exact ⟨hBH, Bal209F4Aux.sLOB_of_bal207 h207 hKG hK hBSC hBN haB hquasi hLieF⟩
  have hc : ∃ a ∈ Bal209F4Aux.pairSub hxy, a ≠ 1 ∧ ∀ w ∈ Subgroup.normalizer (K : Set X),
      Nat.Coprime 3 (orderOf w) → (∀ b ∈ B, ⁅w, b⁆ ∈ Subgroup.centralizer (K : Set X)) →
        ∀ J : Subgroup X, GLAPComponent 3 (K ⊓ Subgroup.centralizer ({a} : Set X)) J →
          w ∈ Subgroup.normalizer (J : Set X) := by
    refine ⟨x, Bal209F4Aux.mem_pairSub.2 ⟨1, 0, by simp⟩, hx1, fun w hwN _ hwB J hJ => ?_⟩
    have hwx : ⁅w, x⁆ ∈ Subgroup.centralizer (K : Set X) := hwB x hxB
    obtain ⟨hsimp, -, -, -⟩ := hFix X K x hK hIsLie hxN hx3 hxI
    have hJeq : J = K ⊓ Subgroup.centralizer ({x} : Set X) :=
      Bal209F4Aux.eq_of_glaPComponent hsimp hJ
    subst hJeq
    exact Bal209F4Aux.mem_normalizer_inf_centralizer hwN hxN hwx
  exact CFSG.HardMathSupport.Dickson.I271.i202Full_holds X 3 Nat.prime_three (by decide) K B
    (Bal209F4Aux.pairSub hxy) hK.2.2 hdvd hBN hBel hSC hAB hnc hloc hb hc

end Consumer

section Final



theorem f4EightStruct_holds : F4EightStruct :=
  f4EightStruct_of_core_iso f4EightOPrimeCore_holds
    (fun _ _ _ hY hL => F4InnerExAux.center_bot_and_equiv hY hL)

theorem bal209F4Eight_of_count (h207 : CFSG.HardMathSupport.Dickson.Bal207.Bal207Corr)
    (hCnt : F4InnerPartCount) : Bal209F4Eight :=
  bal209F4Eight_of_inputs_outP h207
    (f4LocalOne_of_inputs f4EightOPrimeCore_holds f4EightNoOuterFixes_holds) f4Fixed_holds
    (f4InnerCompOutP_of_rank3P h207 f4EightClass_holds
      (f4SU3Rank3P_of_pure hCnt (f4EightPureRank_of_struct f4EightStruct_holds)
        f4OutStatement_holds f4Fixed_holds f4TwoNoNineteen_holds))
    f4InnerEx_holds

theorem f4InnerPartCount_holds : F4InnerPartCount :=
  fun _ _ _ _ _ hBN hK hBSC hrank hLie _ hxB hxI =>
    card_innerPart_ge_27 f4OutStatement_holds f4Fixed_holds hK hBSC hBN hrank hLie hxB hxI


end Final

end KSF4Pure

section Final

set_option linter.unusedSectionVars false



theorem bal209F4Eight_of_pure (h207 : CFSG.HardMathSupport.Dickson.Bal207.Bal207Corr) :
    Bal209F4Eight :=
  KSF4Pure.bal209F4Eight_of_count h207 KSF4Pure.f4InnerPartCount_holds

end Final

end CFSG.HardMathSupport.Solomon.Coordinator.ChevQ

end
