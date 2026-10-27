module

public import CFSG.CGT.PushingUpLit.BHS7.Basic
public import CFSG.CGT.PushingUpLit.BHS6.SixFour
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.ThompsonPQ
public import CFSG.CGT.PushingUpLit.BHS6.Conj

public section

namespace CFSG.CGT.PushingUpLit.BHS7

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.A1b CFSG.QuasithinUnique CFSG.RankThree.PartOne
  CFSG.CGT.PushingUpLit CFSG.CGT.PushingUpLit.BHS CFSG.CGT.PushingUpLit.BHS6
open scoped commutatorElement

variable {Γ : Type} [Group Γ] [Finite Γ]

theorem isPGroup_two_of_forall_odd {D : Subgroup Γ} (h : ∀ x ∈ D, Odd (orderOf x) → x = 1) :
    IsPGroup 2 ↥D := by
  intro x
  obtain ⟨a, m, hm, hdec⟩ := Nat.exists_eq_two_pow_mul_odd (n := orderOf (x : Γ))
    (orderOf_pos _).ne'
  refine ⟨a, ?_⟩
  have hy : ((x : Γ) ^ 2 ^ a) ∈ D := D.pow_mem x.2 _
  have hord : orderOf ((x : Γ) ^ 2 ^ a) = m := by
    rw [orderOf_pow_of_dvd (pow_ne_zero a two_ne_zero) ⟨m, hdec⟩, hdec,
      Nat.mul_div_cancel_left _ (pow_pos two_pos a)]
  exact Subtype.ext (h _ hy (hord ▸ hm))

omit [Finite Γ] in
theorem eq_one_of_odd_of_mem_isPGroup {B : Subgroup Γ} (hB : IsPGroup 2 ↥B) {x : Γ} (hx : x ∈ B)
    (hodd : Odd (orderOf x)) : x = 1 := by
  obtain ⟨n, hn⟩ := hB ⟨x, hx⟩
  have hn' : x ^ 2 ^ n = 1 := congrArg Subtype.val hn
  have hd : orderOf x ∣ 2 ^ n := orderOf_dvd_of_pow_eq_one hn'
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hd
  have hj0 : j = 0 := by
    by_contra hne
    have : Even (orderOf x) := by
      rw [hj]
      exact (Nat.even_pow.2 ⟨even_two, hne⟩)
    exact (Nat.not_even_iff_odd.2 hodd) this
  rw [hj0, pow_zero] at hj
  exact orderOf_eq_one_iff.1 hj

section Finite

theorem two_three_a {G T Q : Subgroup Γ} (hG : CharTwo G) (hT : IsSylowTwoOf T G) (hQT : Q ≤ T)
    (hQn : T ≤ Subgroup.normalizer (Q : Set Γ))
    (hC : T ⊓ Subgroup.centralizer (Q : Set Γ) ≤ Q) :
    G ⊓ Subgroup.centralizer (Q : Set Γ) ≤ Q := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set D : Subgroup Γ := G ⊓ Subgroup.centralizer (Q : Set Γ) with hD
  have hQ2 : IsPGroup 2 ↥Q := hT.2.1.to_le hQT
  have hT2 : IsPGroup 2 ↥T := hT.2.1
  set B : Subgroup Γ := pCoreOf 2 G with hB
  have hB2 : IsPGroup 2 ↥B := CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_isPGroup 2 G
  have hBT : B ≤ T := hT.pCoreOf_le
  have hGB : G ≤ Subgroup.normalizer (B : Set Γ) := BHS6.le_normalizer_pCoreOf_self' G
  have hD2 : IsPGroup 2 ↥D := by
    refine isPGroup_two_of_forall_odd fun x hx hodd => ?_
    have hxQ : ∀ q ∈ Q, q * x = x * q := fun q hq =>
      Subgroup.mem_centralizer_iff.1 hx.2 q hq
    have hzx : ∀ (q : Γ), q ∈ Q → ∀ y ∈ Subgroup.zpowers x, q * y = y * q := by
      intro q hq y hy
      obtain ⟨k, rfl⟩ := hy
      exact (Commute.zpow_right (show Commute q x from hxQ q hq) k).eq
    have hpq := CFSG.GorensteinWalter.ThompsonPQ.thompson_p_times_q (G := Γ) (p := 2) Q
      (Subgroup.zpowers x) B hQ2 hB2
      (by rw [Nat.card_zpowers]; exact Nat.coprime_two_left.2 hodd)
      (fun q hq => hGB (hT.1 (hQT hq)))
      (Subgroup.zpowers_le.2 (hGB hx.1))
      (by
        rw [eq_bot_iff, Subgroup.commutator_le]
        intro q hq y hy
        rw [Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm]
        exact hzx q hq y hy)
      (fun b hb => by
        have hbQ : b ∈ Q := hC ⟨hBT hb.1, hb.2⟩
        rw [Subgroup.mem_centralizer_iff]
        intro y hy
        exact (hzx b hbQ y hy).symm)
    have hxB : x ∈ B := by
      refine hG ⟨hx.1, Subgroup.mem_centralizer_iff.2 fun b hb => ?_⟩
      have h1 : ⁅b, x⁆ ∈ (⁅B, Subgroup.zpowers x⁆ : Subgroup Γ) :=
        Subgroup.commutator_mem_commutator hb (Subgroup.mem_zpowers x)
      rw [hpq, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at h1
      exact h1
    exact eq_one_of_odd_of_mem_isPGroup hB2 hxB hodd
  have hTD : T ≤ Subgroup.normalizer (D : Set Γ) := fun t ht =>
    Subgroup.inf_normalizer_le_normalizer_inf
      ⟨Subgroup.le_normalizer (hT.1 ht), B6.le_normalizer_centralizer hQn ht⟩
  have hDT2 : IsPGroup 2 ↥(D ⊔ T) := IsPGroup.to_sup_of_normal_left' hD2 hT2 hTD
  have hDTle : D ⊔ T ≤ T :=
    Nine.le_of_isSylowOf_of_le (hT : IsSylowOf 2 T G) hDT2 le_sup_right
      (sup_le inf_le_left hT.1)
  intro x hx
  exact hC ⟨hDTle ((le_sup_left : D ≤ D ⊔ T) hx), hx.2⟩

omit [Finite Γ] in
theorem inf_centralizer_baum_le (T : Subgroup Γ) :
    T ⊓ Subgroup.centralizer (baum T : Set Γ) ≤ baum T := by
  intro x hx
  refine ⟨hx.1, Subgroup.centralizer_le ?_ hx.2⟩
  exact (C1GN.omegaOneCenterOf_le_self (thompsonJ T)).trans (B6.thompsonJ_le_baum T)

omit [Finite Γ] in
theorem le_normalizer_baum (T : Subgroup Γ) : T ≤ Subgroup.normalizer (baum T : Set Γ) :=
  Subgroup.le_normalizer.trans (normalizer_le_normalizer_baum T)

omit [Finite Γ] in
@[expose] def conjClosureIn (L Q : Subgroup Γ) : Subgroup Γ :=
  ⨆ l : L, conjSub (l : Γ) Q

omit [Finite Γ] in
theorem le_conjClosureIn (L Q : Subgroup Γ) : Q ≤ conjClosureIn L Q := by
  have h : conjSub ((1 : L) : Γ) Q ≤ conjClosureIn L Q :=
    le_iSup (fun l : L => conjSub (l : Γ) Q) 1
  rwa [show ((1 : L) : Γ) = 1 from rfl, conjSub_one] at h

omit [Finite Γ] in
theorem conjClosureIn_le {L Q : Subgroup Γ} (hQL : Q ≤ L) : conjClosureIn L Q ≤ L := by
  refine iSup_le fun l x hx => ?_
  rw [mem_conjSub_iff] at hx
  have hxe : x = (l : Γ) * ((l : Γ)⁻¹ * x * l) * (l : Γ)⁻¹ := by group
  rw [hxe]
  exact mul_mem (mul_mem l.2 (hQL hx)) (inv_mem l.2)

omit [Finite Γ] in
theorem le_normalizer_conjClosureIn (L Q : Subgroup Γ) :
    L ≤ Subgroup.normalizer (conjClosureIn L Q : Set Γ) := by
  have key : ∀ l ∈ L, conjSub l (conjClosureIn L Q) ≤ conjClosureIn L Q := by
    intro l hl
    unfold conjClosureIn
    rw [conjSub_iSup]
    refine iSup_le fun e => ?_
    rw [← conjSub_mul]
    exact le_iSup (fun e : L => conjSub (e : Γ) Q) ⟨l * e, L.mul_mem hl e.2⟩
  intro l hl
  exact mem_normalizer_of_conjSub_le (key l hl) (key l⁻¹ (L.inv_mem hl))

omit [Finite Γ] in
def commutatorSub (L R : Subgroup Γ) (hR : L ≤ Subgroup.normalizer (R : Set Γ)) (x : Γ) :
    Subgroup Γ where
  carrier := {p | p ∈ L ∧ ⁅x, p⁆ ∈ R}
  mul_mem' := by
    rintro p₁ p₂ ⟨hp₁, h₁⟩ ⟨hp₂, h₂⟩
    refine ⟨L.mul_mem hp₁ hp₂, ?_⟩
    have e : ⁅x, p₁ * p₂⁆ = ⁅x, p₁⁆ * (p₁ * ⁅x, p₂⁆ * p₁⁻¹) := by
      simp only [commutatorElement_def]; group
    rw [e]
    refine R.mul_mem h₁ ?_
    exact (Subgroup.mem_normalizer_iff.1 (hR hp₁) _).1 h₂
  one_mem' := ⟨L.one_mem, by simp [R.one_mem]⟩
  inv_mem' := by
    rintro p ⟨hp, h⟩
    refine ⟨L.inv_mem hp, ?_⟩
    have e : ⁅x, p⁻¹⁆ = p⁻¹ * ⁅x, p⁆⁻¹ * p := by
      simp only [commutatorElement_def]; group
    rw [e]
    have h' : ⁅x, p⁆⁻¹ ∈ R := R.inv_mem h
    have := (Subgroup.mem_normalizer_iff.1 (hR (L.inv_mem hp)) _).1 h'
    simpa [mul_assoc] using this

theorem two_three_b {G T Q L : Subgroup Γ} (hG : CharTwo G) (hT : IsSylowTwoOf T G) (hQT : Q ≤ T)
    (hQn : T ≤ Subgroup.normalizer (Q : Set Γ))
    (hC : T ⊓ Subgroup.centralizer (Q : Set Γ) ≤ Q) (hQL : Q ≤ L) (hLG : L ≤ G) : CharTwo L := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hQ2 : IsPGroup 2 ↥Q := hT.2.1.to_le hQT
  set L₀ : Subgroup Γ := conjClosureIn L Q with hL₀
  have hL₀L : L₀ ≤ L := conjClosureIn_le hQL
  have hOn : pCoreOf 2 G ≤ Subgroup.normalizer (L₀ : Set Γ) :=
    le_normalizer_iSup_conj (E := L) (B := Q) (Q := pCoreOf 2 G)
      (hLG.trans (BHS6.le_normalizer_pCoreOf_self' G)) (hT.pCoreOf_le.trans hQn)
  have hchar₀ : CharTwo L₀ := two_two_normalizes hG (hL₀L.trans hLG) hOn
  set R : Subgroup Γ := pCoreOf 2 L with hR
  have hR2 : IsPGroup 2 ↥R := CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_isPGroup 2 L
  have hLR : L ≤ Subgroup.normalizer (R : Set Γ) := le_normalizer_pCoreOf_self L
  have hRL : R ≤ L := CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_le 2 L
  set C : Subgroup Γ := L ⊓ Subgroup.centralizer (R : Set Γ) with hCdef
  have hLC : L ≤ Subgroup.normalizer (C : Set Γ) := fun l hl =>
    Subgroup.inf_normalizer_le_normalizer_inf
      ⟨Subgroup.le_normalizer hl, B6.le_normalizer_centralizer hLR hl⟩
  have hO₀ : pCoreOf 2 L₀ ≤ R := by
    refine CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2
      ((CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_le 2 L₀).trans hL₀L) ?_
      (CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_isPGroup 2 L₀)
    intro l hl
    have h1 : conjSub l L₀ = L₀ := conjSub_eq_of_mem_normalizer (le_normalizer_conjClosureIn L Q hl)
    have h2 := pCoreOf_conjSub l L₀
    rw [h1] at h2
    exact mem_normalizer_of_conjSub_eq h2.symm
  have hcomm : ∀ c ∈ C, ∀ q ∈ Q, ⁅c, q⁆ ∈ R := by
    intro c hc q hq
    have hcL : c ∈ L := hc.1
    have h1 : ⁅c, q⁆ ∈ L₀ := by
      have hcq : c * q * c⁻¹ ∈ L₀ := by
        have := (Subgroup.mem_normalizer_iff.1 (le_normalizer_conjClosureIn L Q hcL) q).1
          (le_conjClosureIn L Q hq)
        exact this
      simpa [commutatorElement_def, mul_assoc] using
        mul_mem hcq (inv_mem (le_conjClosureIn L Q hq))
    have h2 : ⁅c, q⁆ ∈ C := by
      have hqL : q ∈ L := hQL hq
      have hqc : q * c⁻¹ * q⁻¹ ∈ C := by
        have := (Subgroup.mem_normalizer_iff.1 (hLC hqL) c⁻¹).1 (C.inv_mem hc)
        exact this
      have : c * (q * c⁻¹ * q⁻¹) ∈ C := C.mul_mem hc hqc
      simpa [commutatorElement_def, mul_assoc] using this
    exact hO₀ (hchar₀ ⟨h1, Subgroup.centralizer_le hO₀ h2.2⟩)
  have hC2 : IsPGroup 2 ↥C := by
    refine isPGroup_two_of_forall_odd fun x hx hodd => ?_
    have hRQ : IsPGroup 2 ↥(R ⊔ Q) :=
      IsPGroup.to_sup_of_normal_left' hR2 hQ2 (hQL.trans hLR)
    have hsub : R ⊔ Q ≤ commutatorSub L R hLR x := by
      refine sup_le (fun r hr => ⟨hRL hr, ?_⟩) (fun q hq => ⟨hQL hq, hcomm x hx q hq⟩)
      have : ⁅x, r⁆ = 1 := by
        rw [commutatorElement_eq_one_iff_mul_comm]
        exact (Subgroup.mem_centralizer_iff.1 hx.2 r hr).symm
      rw [this]
      exact R.one_mem
    have hxQ : x ∈ Subgroup.centralizer (Q : Set Γ) := by
      refine Subgroup.mem_centralizer_iff.2 fun q hq => ?_
      have hfix := commute_of_odd_of_stab hRQ (le_sup_left : R ≤ R ⊔ Q) hodd
        (fun p hp => (hsub hp).2) (fun w hw => (Subgroup.mem_centralizer_iff.1 hx.2 w hw).symm)
        ((le_sup_right : Q ≤ R ⊔ Q) hq)
      have : x * q = q * x := by
        calc x * q = (x * q * x⁻¹) * x := by group
          _ = q * x := by rw [hfix]
      exact this.symm
    have hxQ' : x ∈ Q := two_three_a hG hT hQT hQn hC ⟨hLG hx.1, hxQ⟩
    exact eq_one_of_odd_of_mem_isPGroup hQ2 hxQ' hodd
  intro x hx
  exact CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 inf_le_left hLC hC2 hx

theorem two_three_c {G T P T₀ : Subgroup Γ} (hG : CharTwo G) (hT : IsSylowTwoOf T G) (hPG : P ≤ G)
    (hT₀ : IsSylowTwoOf T₀ P) (hB : baum T ≤ T₀) : CharTwo P :=
  two_three_b hG hT (inf_le_left : baum T ≤ T) (le_normalizer_baum T) (inf_centralizer_baum_le T)
    (hB.trans hT₀.1) hPG

theorem cStarIn_eq_of_baum_eq {G T T' : Subgroup Γ} (hT : IsSylowTwoOf T G)
    (hT' : IsSylowTwoOf T' G) (hb : baum T' = baum T) (hb0 : baum T ≠ ⊥) :
    cStarIn G T' = cStarIn G T := by
  set N : Subgroup Γ := G ⊓ Subgroup.normalizer (baum T : Set Γ) with hN
  have hTN : IsSylowTwoOf T N :=
    isSylowTwoOf_of_le_of_le hT (le_inf hT.1 (le_normalizer_baum T)) inf_le_left
  have hT'N : IsSylowTwoOf T' N :=
    isSylowTwoOf_of_le_of_le hT' (le_inf hT'.1 (hb ▸ le_normalizer_baum T')) inf_le_left
  obtain ⟨n, hn, hnT⟩ := B6.isSylowTwoOf_exists_conj hTN hT'N
  have hnG : n ∈ G := hn.1
  have hnC : n ∈ cStarIn G T := inf_normalizer_baum_le_cStarIn hb0 hn
  rw [hnT, b6_conjSub_eq]
  have h1 : cStarIn G (conjSub n T) = conjSub n (cStarIn G T) := by
    have := cStarIn_conjSub n G T
    rwa [conjSub_eq_of_mem_normalizer (Subgroup.le_normalizer hnG)] at this
  rw [h1]
  exact conjSub_eq_of_mem_normalizer (Subgroup.le_normalizer hnC)

theorem two_three_d {G T P T₀ : Subgroup Γ} (hT : IsSylowTwoOf T G) (hb0 : baum T ≠ ⊥)
    (hPG : P ≤ G) (hT₀ : IsSylowTwoOf T₀ P) (hB : baum T ≤ T₀) :
    cStarIn P T₀ ≤ cStarIn G T := by
  have hT₀2 : IsPGroup 2 ↥T₀ := hT₀.2.1
  obtain ⟨T', hT', hT₀T'⟩ := B6.exists_isSylowTwoOf_ge hT₀2 (hT₀.1.trans hPG)
  have hb' : baum T' = baum T :=
    baum_eq_of_isPGroup_of_baum_le hT hT'.2.1 hT'.1 (hB.trans hT₀T')
  have hb₀ : baum T₀ = baum T :=
    baum_eq_of_isPGroup_of_baum_le hT hT₀2 (hT₀.1.trans hPG) hB
  have hcs : cStarIn G T' = cStarIn G T := cStarIn_eq_of_baum_eq hT hT' hb' hb0
  have hZ : omegaOneCenterOf T' ≤ omegaOneCenterOf T₀ := by
    refine Subgroup.closure_mono ?_
    rintro x ⟨hxZ, hx2⟩
    have hxZ' : x ∈ T' ⊓ Subgroup.centralizer (T' : Set Γ) := hxZ
    have hxc : ∀ y ∈ T', y * x = x * y := fun y hy => Subgroup.mem_centralizer_iff.1 hxZ'.2 y hy
    have hxB : x ∈ baum T' := inf_centralizer_baum_le T' ⟨hxZ'.1,
      Subgroup.mem_centralizer_iff.2 fun y hy => hxc y ((inf_le_left : baum T' ≤ T') hy)⟩
    have hxT₀ : x ∈ T₀ := hB (hb' ▸ hxB)
    exact ⟨⟨hxT₀, Subgroup.mem_centralizer_iff.2 fun y hy => hxc y (hT₀T' hy)⟩, hx2⟩
  have h1 : P ⊓ Subgroup.centralizer (omegaOneCenterOf T₀ : Set Γ) ≤ cStarIn G T' :=
    le_trans (inf_le_inf hPG (Subgroup.centralizer_le hZ)) (centralizer_le_cStarIn G T')
  have h2 : cgsIn P (baum T₀) ≤ cStarIn G T' := by
    rw [hb₀, ← hb']
    exact (cgsIn_mono hPG).trans le_sup_right
  rw [← hcs]
  exact sup_le h1 h2

end Finite

end CFSG.CGT.PushingUpLit.BHS7
