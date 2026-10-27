module

public import CFSG.HardMathSupport.Timmesfeld.LocalTwo.CrossBase
public import CFSG.HardMathSupport.Timmesfeld.LocalTwo.CrossLinOuter

public section

namespace CFSG.HardMathSupport.Timmesfeld.LocalTwo

open CFSG.Open CFSG.HardMathSupport.Solomon.LocalBalance Matrix
open CFSG.HardMathSupport.Timmesfeld.Coordinator
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher (relIndex_inner_linearAutGroup_dvd)
open CFSG.HardMathSupport.Timmesfeld.CrossChar

section Generic

theorem exists_gens_of_plane {M : Type*} [Group M] {p : ℕ} (hp : p.Prime) {D : Subgroup M}
    (hD : IsElemAbelian p D) (hcard : Nat.card D = p ^ 2) :
    ∃ y₁ ∈ D, ∃ y₂ ∈ D, y₁ ≠ 1 ∧ y₂ ∉ Subgroup.zpowers y₁ ∧
      D = Subgroup.closure {y₁, y₂} := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have hDfin : Finite D := Nat.finite_of_card_ne_zero (by rw [hcard]; exact pow_ne_zero 2 hp.ne_zero)
  obtain ⟨y₁, hy₁D, hy₁⟩ : ∃ y ∈ D, y ≠ 1 := by
    by_contra hno
    push Not at hno
    have hbot : D = ⊥ := eq_bot_iff.2 fun z hz => (Subgroup.mem_bot).2 (hno z hz)
    rw [hbot, Subgroup.card_bot] at hcard
    have := hp.one_lt
    nlinarith
  have hord : orderOf y₁ = p := orderOf_eq_prime (hD.2 y₁ hy₁D) hy₁
  have hz : Nat.card (Subgroup.zpowers y₁) = p := by rw [Nat.card_zpowers, hord]
  have hzD : Subgroup.zpowers y₁ ≤ D := (Subgroup.zpowers_le).2 hy₁D
  have : Finite (Subgroup.zpowers y₁) :=
    Finite.of_injective (Subgroup.inclusion hzD) (Subgroup.inclusion_injective hzD)
  obtain ⟨y₂, hy₂D, hy₂⟩ : ∃ y ∈ D, y ∉ Subgroup.zpowers y₁ := by
    by_contra hno
    push Not at hno
    have : D ≤ Subgroup.zpowers y₁ := fun z hz => hno z hz
    have h1 := Subgroup.card_le_of_le this
    rw [hz, hcard] at h1
    have h2 : p < p ^ 2 := by
      have := hp.one_lt
      nlinarith
    omega
  refine ⟨y₁, hy₁D, y₂, hy₂D, hy₁, hy₂, ?_⟩
  set C := Subgroup.closure ({y₁, y₂} : Set M) with hC
  have hCD : C ≤ D := (Subgroup.closure_le D).2 (by
    intro z hz
    rcases hz with rfl | rfl
    · exact hy₁D
    · exact hy₂D)
  have : Finite C := Finite.of_injective (Subgroup.inclusion hCD) (Subgroup.inclusion_injective hCD)
  have hzC : Subgroup.zpowers y₁ ≤ C := (Subgroup.zpowers_le).2
    (Subgroup.subset_closure (by simp))
  have hy₂C : y₂ ∈ C := Subgroup.subset_closure (by simp)
  have hCdvd : Nat.card C ∣ p ^ 2 := hcard ▸ Subgroup.card_dvd_of_le hCD
  have hpC : p ∣ Nat.card C := hz ▸ Subgroup.card_dvd_of_le hzC
  have hlt : p < Nat.card C := by
    have h1 := Subgroup.card_le_of_le hzC
    rw [hz] at h1
    rcases h1.lt_or_eq with h | h
    · exact h
    · exfalso
      have : Subgroup.zpowers y₁ = C := Subgroup.eq_of_le_of_card_ge hzC (by rw [hz]; omega)
      exact hy₂ (this ▸ hy₂C)
  obtain ⟨i, hi, hCi⟩ := (Nat.dvd_prime_pow hp).1 hCdvd
  have hi2 : i = 2 := by
    by_contra hne
    have : i ≤ 1 := by omega
    have h3 : p ^ i ≤ p ^ 1 := Nat.pow_le_pow_right hp.pos this
    rw [pow_one] at h3
    omega
  subst hi2
  exact (Subgroup.eq_of_le_of_card_ge hCD (by rw [hcard, hCi])).symm

theorem InnerPlaneBalance.of_mulEquiv {K K' : Type*} [Group K] [Group K'] {p : ℕ} (e : K ≃* K')
    (h : InnerPlaneBalance p K') : InnerPlaneBalance p K := by
  intro E hEin hE hEc H hH
  set ψ : MulAut K →* MulAut K' := (MulAut.congr e).toMonoidHom with hψ
  have hψinj : Function.Injective ψ := (MulAut.congr e).injective
  have hψconj : ∀ g : K, ψ (MulAut.conj g) = MulAut.conj (e g) := fun g => by
    ext z
    simp [hψ, MulAut.congr_apply, MulAut.conj_apply]
  have hinn : innerAut K' ≤ (innerAut K).map ψ := by
    rintro _ ⟨y, rfl⟩
    refine ⟨MulAut.conj (e.symm y), ⟨e.symm y, rfl⟩, ?_⟩
    rw [hψconj]
    simp
  have hE'in : E.map ψ ≤ innerAut K' := by
    rintro _ ⟨z, hz, rfl⟩
    obtain ⟨g, rfl⟩ := hEin hz
    exact ⟨e g, (hψconj g).symm⟩
  have h0 := h (E.map ψ) hE'in (isElemAbelian_map _ hE)
    (by rw [Subgroup.card_map_of_injective hψinj, hEc]) (H.map ψ)
    (hinn.trans (Subgroup.map_mono hH))
  have hle := map_localDeltaIn_le p ψ hψinj H E
  rw [h0, le_bot_iff, Subgroup.map_eq_bot_iff_of_injective _ hψinj] at hle
  exact hle

end Generic

section Linear

variable {n : ℕ} {F : Type} [Field F] [Finite F]

theorem mem_innerAut_of_mem_linearAutGroup (hn : 3 ≤ n) {p : ℕ} (hp : p.Prime)
    (hpg : ¬ p ∣ Nat.gcd n (Nat.card F - 1)) {x : MulAut (projectiveSL n F)}
    (hx : x ∈ linearAutGroup n F) (hxp : x ^ p = 1) : x ∈ innerAut (projectiveSL n F) := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  set Dl := linearAutGroup n F with hDl
  have hm := relIndex_inner_linearAutGroup_dvd (k := F) (n := n) (by omega)
  have hcop : Nat.Coprime p ((CFSG.ComponentClassification.OuterAutomorphisms.inner
      (projectiveSL n F)).relIndex Dl) := by
    rw [Nat.Prime.coprime_iff_not_dvd hp]
    exact fun h => hpg (h.trans hm)
  have hNorm : ((CFSG.ComponentClassification.OuterAutomorphisms.inner
      (projectiveSL n F)).subgroupOf Dl).Normal := inferInstance
  set y : Dl ⧸ (CFSG.ComponentClassification.OuterAutomorphisms.inner
      (projectiveSL n F)).subgroupOf Dl := QuotientGroup.mk ⟨x, hx⟩ with hy
  have hy1 : y ^ p = 1 := by
    rw [hy, ← QuotientGroup.mk_pow]
    have : (⟨x, hx⟩ : Dl) ^ p = 1 := Subtype.ext hxp
    rw [this]; rfl
  have hy2 : y ^ ((CFSG.ComponentClassification.OuterAutomorphisms.inner
      (projectiveSL n F)).relIndex Dl) = 1 := by
    have h1 := pow_card_eq_one' (G := Dl ⧸ (CFSG.ComponentClassification.OuterAutomorphisms.inner
      (projectiveSL n F)).subgroupOf Dl) (x := y)
    rw [← Subgroup.index_eq_card] at h1
    exact h1
  have hord : orderOf y ∣ Nat.gcd p ((CFSG.ComponentClassification.OuterAutomorphisms.inner
      (projectiveSL n F)).relIndex Dl) :=
    Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one hy1) (orderOf_dvd_of_pow_eq_one hy2)
  rw [hcop.gcd_eq_one, Nat.dvd_one, orderOf_eq_one_iff] at hord
  have := (QuotientGroup.eq_one_iff _).1 hord
  exact (Subgroup.mem_subgroupOf.1 this)

theorem localDeltaIn_eq_bot_of_comm_lifts (hn : 3 ≤ n) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hpF : p ∣ Nat.card F - 1) {A B : GL (Fin n) F} (hAB : A * B = B * A)
    (hA : conjAut n F A ^ p = 1) (hB : conjAut n F B ^ p = 1) (hA1 : conjAut n F A ≠ 1)
    (hBA : conjAut n F B ∉ Subgroup.zpowers (conjAut n F A))
    {H : Subgroup (MulAut (projectiveSL n F))} (hH : innerAut (projectiveSL n F) ≤ H) :
    localDeltaIn p H (Subgroup.closure {conjAut n F A, conjAut n F B}) = ⊥ := by
  by_cases hs : (∃ a : Fˣ, A ^ p = GeneralLinearGroup.scalar (Fin n) (a ^ p)) ∧
      ∃ b : Fˣ, B ^ p = GeneralLinearGroup.scalar (Fin n) (b ^ p)
  · exact diagAbelianPlaneBalance_split hn hp hp2 hpF hAB hs.1 hs.2 hA1 hBA hH
  · exact localDeltaIn_eq_bot_of_nonsplit hn hp hp2 hpF hAB hA hB hA1 hBA hs hH

@[expose] def LinHeisenbergBalance : Prop :=
  ∀ (n : ℕ) (F : Type) [Field F] [Finite F], 3 ≤ n → ∀ p : ℕ, p.Prime → 5 < p →
    p ∣ Nat.card F - 1 → n ≠ p → ∀ A B : GL (Fin n) F, ¬ (A * B = B * A) →
      conjAut n F A * conjAut n F B = conjAut n F B * conjAut n F A →
      conjAut n F A ^ p = 1 → conjAut n F B ^ p = 1 →
      ∀ H : Subgroup (MulAut (projectiveSL n F)), innerAut (projectiveSL n F) ≤ H →
        localDeltaIn p H (Subgroup.closure {conjAut n F A, conjAut n F B}) = ⊥

theorem isLocallyBalancedAbs_two_projectiveSL (hn : 3 ≤ n) {p : ℕ} (hp : p.Prime) (hp5 : 5 < p)
    (hpF : ¬ p ∣ Nat.card F) (hnp : p ∣ Nat.card F - 1 → n ≠ p)
    (hHeis : LinHeisenbergBalance)
    (hplane : ¬ p ∣ Nat.card F - 1 → InnerPlaneBalance p (projectiveSL n F)) :
    IsLocallyBalancedAbs p 2 (projectiveSL n F) := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have hp2 : p ≠ 2 := by omega
  intro D hD hcard H hH _
  by_cases hDl : D ≤ linearAutGroup n F
  · by_cases hq : p ∣ Nat.card F - 1
    · obtain ⟨y₁, hy₁D, y₂, hy₂D, hy₁, hy₂, hgen⟩ := exists_gens_of_plane hp hD hcard
      obtain ⟨A, hA⟩ := mem_linearAutGroup_iff.1 (hDl hy₁D)
      obtain ⟨B, hB⟩ := mem_linearAutGroup_iff.1 (hDl hy₂D)
      have hA' : conjAut n F A = y₁ := hA
      have hB' : conjAut n F B = y₂ := hB
      rw [hgen, ← hA', ← hB']
      rw [← hA'] at hy₁ hy₂
      rw [← hB'] at hy₂
      have hcomm : conjAut n F A * conjAut n F B = conjAut n F B * conjAut n F A := by
        rw [hA', hB']
        exact congrArg Subtype.val (hD.1.is_comm.comm ⟨y₁, hy₁D⟩ ⟨y₂, hy₂D⟩)
      have hAp : conjAut n F A ^ p = 1 := by rw [hA']; exact hD.2 y₁ hy₁D
      have hBp : conjAut n F B ^ p = 1 := by rw [hB']; exact hD.2 y₂ hy₂D
      by_cases hAB : A * B = B * A
      · exact localDeltaIn_eq_bot_of_comm_lifts hn hp hp2 hq hAB hAp hBp hy₁ hy₂ hH
      · exact hHeis n F hn p hp hp5 hq (hnp hq) A B hAB hcomm hAp hBp H hH
    · have hpg : ¬ p ∣ Nat.gcd n (Nat.card F - 1) := fun h => hq (h.trans (Nat.gcd_dvd_right _ _))
      refine hplane hq D (fun x hx => ?_) hD hcard H hH
      exact mem_innerAut_of_mem_linearAutGroup hn hp hpg (hDl hx) (hD.2 x hx)
  · exact localDeltaIn_eq_bot_of_not_le_linearAutGroup_two hn hp hp2 hpF hD hcard hDl hH

theorem conjInjective_of_mulEquiv_lin {G G' : Type*} [Group G] [Group G'] (e : G ≃* G')
    (h : Function.Injective (MulAut.conj : G' →* MulAut G')) :
    Function.Injective (MulAut.conj : G →* MulAut G) := by
  rw [injective_iff_map_eq_one]
  intro g hg
  have : MulAut.conj (e g) = (1 : MulAut G') := by
    ext z
    have h1 := DFunLike.congr_fun hg (e.symm z)
    simp only [MulAut.conj_apply, MulAut.one_apply] at h1 ⊢
    have h2 := congrArg e h1
    simpa using h2
  have h3 : e g = 1 := h (by rw [map_one]; exact this)
  exact e.injective (by rw [h3, map_one])

theorem innerPlaneBalance_projectiveSL_nonsplit (hn : 3 ≤ n) {p : ℕ} (hp : p.Prime) (hp5 : 5 < p)
    (hpF : ¬ p ∣ Nat.card F) (hpq : ¬ p ∣ Nat.card F - 1) :
    InnerPlaneBalance p (projectiveSL n F) := by
  have e := LinearCover.projectiveSpecialLinearEquivProjectiveSL n F
  have hinjG := CFSG.RankThree.RegularUnipotent.conj_injective_projectiveSL (k := F) hn
  have hinjP := conjInjective_of_mulEquiv_lin e hinjG
  refine InnerPlaneBalance.of_mulEquiv e.symm ?_
  intro E hEin hE hEc H hH
  set E₁ := E.comap (MulAut.conj : ProjectiveSpecialLinearGroup (Fin n) F →* _) with hE₁def
  have hE₁ : E₁.map (MulAut.conj : ProjectiveSpecialLinearGroup (Fin n) F →* _) = E :=
    Subgroup.map_comap_eq_self hEin
  have hE₁el := isElemAbelian_comap _ hinjP hE
  have hE₁c : Nat.card E₁ = p ^ 2 := by
    rw [← Subgroup.card_map_of_injective hinjP, hE₁, hEc]
  rw [← hE₁]
  exact localDeltaIn_eq_bot_psl_nonsplit hp (Or.inl (by omega)) hpF hpq (by omega) hinjP E₁
    hE₁el hE₁c hH

end Linear

end CFSG.HardMathSupport.Timmesfeld.LocalTwo
