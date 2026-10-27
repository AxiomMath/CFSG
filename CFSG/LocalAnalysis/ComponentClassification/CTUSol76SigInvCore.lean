module

public import CFSG.ClassicalInvolution.Balance.LocalBalance.Faithful
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitLocalBalanceTypes
public import CFSG.LocalAnalysis.ComponentClassification.Sol76LStruct
public import CFSG.LocalAnalysis.ComponentClassification.Sol76Lemma212Steps
public import Certificates.Kernel.ThCent.Leaves

public section

namespace CFSG.ComponentClassification.Sol76.Sig

open CFSG Subgroup CFSG.ClassicalInvolution.Balance CFSG.ClassicalInvolution.Balance.LocalBalance
  CFSG.LocalAnalysis.ComponentInitial

@[expose] def IsInvolutionCoreFree (L : Type*) [Group L] : Prop :=
  ∀ H : Subgroup (MulAut L), ∀ hH : (MulAut.conj : L →* MulAut L).range ≤ H,
    ∀ x : L, x * x = 1 →
      Assembly.Dichotomy.involutionOddCore (⟨MulAut.conj x, hH ⟨x, rfl⟩⟩ : H) = ⊥

section Transport

variable {L L' : Type*} [Group L] [Group L']

omit [Group L] [Group L'] in
theorem mulAut_congr_conj [Group L] [Group L'] (e : L ≃* L') (l : L) :
    MulAut.congr e (MulAut.conj l) = MulAut.conj (e l) := by
  ext y
  simp [MulAut.congr_apply, MulAut.conj_apply, map_mul, map_inv]

theorem isInvolutionCoreFree_of_mulEquiv [Finite L'] (e : L ≃* L')
    (h : IsInvolutionCoreFree L) : IsInvolutionCoreFree L' := by
  intro H' hH' x' hx'2
  have : Finite (MulAut L') := inferInstance
  set c : MulAut L ≃* MulAut L' := MulAut.congr e with hc
  set H : Subgroup (MulAut L) := H'.comap c.toMonoidHom with hHdef
  have hH : (MulAut.conj : L →* MulAut L).range ≤ H := by
    rintro _ ⟨l, rfl⟩
    show c (MulAut.conj l) ∈ H'
    rw [hc, mulAut_congr_conj]
    exact hH' ⟨e l, rfl⟩
  set x : L := e.symm x' with hx
  have hx2 : x * x = 1 := by rw [hx, ← map_mul, hx'2, map_one]
  have h0 := h H hH x hx2
  let g : H' →* H :=
    { toFun := fun σ => ⟨c.symm (σ : MulAut L'), by
        show c (c.symm (σ : MulAut L')) ∈ H'
        rw [MulEquiv.apply_symm_apply]
        exact σ.2⟩
      map_one' := Subtype.ext (map_one c.symm)
      map_mul' := fun σ τ => Subtype.ext (map_mul c.symm (σ : MulAut L') (τ : MulAut L')) }
  have hginj : Function.Injective g := fun σ τ hστ =>
    Subtype.ext (c.symm.injective (congrArg (fun w : H => (w : MulAut L)) hστ))
  have hgsurj : Function.Surjective g := fun τ =>
    ⟨⟨c (τ : MulAut L), τ.2⟩, Subtype.ext (by
      show c.symm (c (τ : MulAut L)) = τ
      exact MulEquiv.symm_apply_apply c (τ : MulAut L))⟩
  set a' : H' := ⟨MulAut.conj x', hH' ⟨x', rfl⟩⟩ with ha'
  have ha'2 : a' * a' = 1 := by
    apply Subtype.ext
    show MulAut.conj x' * MulAut.conj x' = 1
    rw [← map_mul, hx'2, map_one]
  have hga : g a' = ⟨MulAut.conj x, hH ⟨x, rfl⟩⟩ := by
    apply Subtype.ext
    show c.symm (MulAut.conj x') = MulAut.conj x
    rw [MulEquiv.symm_apply_eq, hc, mulAut_congr_conj, hx, MulEquiv.apply_symm_apply]
  have hle := map_involutionOddCore_le g hgsurj (isPGroup_zpowers_of_mul_self_eq_one ha'2)
  rw [hga, h0] at hle
  exact (map_eq_bot_iff_of_injective _ hginj).mp (le_bot_iff.mp hle)

end Transport

section Rigid

variable {L : Type} [Group L] [Finite L]

theorem involutionOddCore_eq_bot_of_rigidAt (hZ : center L = ⊥) {x : L}
    (hO : Assembly.Dichotomy.involutionOddCore x = ⊥)
    (hR : ∀ β : MulAut L, Odd (orderOf β) →
      (∀ c ∈ Subgroup.centralizer ({x} : Set L), β c = c) → β = 1)
    (H : Subgroup (MulAut L)) (hH : (MulAut.conj : L →* MulAut L).range ≤ H) :
    Assembly.Dichotomy.involutionOddCore (⟨MulAut.conj x, hH ⟨x, rfl⟩⟩ : H) = ⊥ := by
  have : Finite (MulAut L) := inferInstance
  have hinj := GrSLit.conj_injective_of_center_eq_bot hZ
  set a : H := ⟨MulAut.conj x, hH ⟨x, rfl⟩⟩ with ha
  set A := Assembly.Dichotomy.involutionOddCore a with hA
  have hAodd : Odd (Nat.card A) := by
    rw [hA, involutionOddCore_eq_oddCoreCentralizer]
    exact odd_card_oddCoreCentralizer _
  have hAC : A ≤ Subgroup.centralizer ({a} : Set H) := by
    rw [hA, involutionOddCore_eq_oddCoreCentralizer, ← centralizer_zpowers_eq]
    exact oddCoreCentralizer_le_centralizer _
  rw [eq_bot_iff]
  intro σ hσ
  rw [mem_bot]
  have hσx : (σ : MulAut L) x = x := by
    have h1 : σ * a = a * σ := (mem_centralizer_singleton_iff.mp (hAC hσ))
    have h2 : MulAut.conj ((σ : MulAut L) x) = MulAut.conj x := by
      rw [← GrSLit.mulAut_mul_conj_mul_inv]
      have h3 := congrArg Subtype.val h1
      simp only [Subgroup.coe_mul, ha] at h3
      rw [h3, mul_inv_cancel_right]
    exact hinj h2
  set Y : Subgroup L := (A.map H.subtype).comap (MulAut.conj : L →* MulAut L) ⊓
    Subgroup.centralizer ((zpowers x : Subgroup L) : Set L) with hY
  have hYC : Y ≤ Subgroup.centralizer ((zpowers x : Subgroup L) : Set L) := inf_le_right
  have hconjC : ∀ c ∈ Subgroup.centralizer ((zpowers x : Subgroup L) : Set L),
      (⟨MulAut.conj c, hH ⟨c, rfl⟩⟩ : H) ∈ Subgroup.centralizer ({a} : Set H) := by
    intro c hc
    rw [centralizer_zpowers_eq] at hc
    rw [mem_centralizer_singleton_iff]
    apply Subtype.ext
    show MulAut.conj c * MulAut.conj x = MulAut.conj x * MulAut.conj c
    rw [← map_mul, ← map_mul, (mem_centralizer_singleton_iff.mp hc)]
  have hYn : ∀ c ∈ Subgroup.centralizer ((zpowers x : Subgroup L) : Set L), ∀ y ∈ Y,
      c * y * c⁻¹ ∈ Y := by
    intro c hc y hy
    refine mem_inf.mpr ⟨?_, mul_mem (mul_mem hc (hYC hy)) (inv_mem hc)⟩
    obtain ⟨τ, hτ, hτy⟩ := (mem_inf.mp hy).1
    have hcA := conj_mem_involutionOddCore (hconjC c hc) hτ
    refine ⟨_, hcA, ?_⟩
    simp only [coe_subtype, Subgroup.coe_mul, Subgroup.coe_inv] at hτy ⊢
    rw [hτy, map_mul, map_mul, map_inv]
  have hYodd : Odd (Nat.card Y) := by
    let ι : Y →* A :=
      { toFun := fun y => ⟨⟨MulAut.conj (y : L), hH ⟨y, rfl⟩⟩, by
          obtain ⟨τ, hτ, hτy⟩ := (mem_inf.mp y.2).1
          have : τ = ⟨MulAut.conj (y : L), hH ⟨y, rfl⟩⟩ := Subtype.ext hτy
          rw [← this]
          exact hτ⟩
        map_one' := Subtype.ext (Subtype.ext (map_one _))
        map_mul' := fun y z => Subtype.ext (Subtype.ext (map_mul _ _ _)) }
    have hι : Function.Injective ι := fun y z hyz =>
      Subtype.ext (hinj (congrArg (fun w : A => ((w : H) : MulAut L)) hyz))
    exact hAodd.of_dvd_nat (Subgroup.card_dvd_of_injective ι hι)
  have hYO : Y ≤ Assembly.Dichotomy.involutionOddCore x := by
    rw [involutionOddCore_eq_oddCoreCentralizer]
    exact le_oddCoreCentralizer hYC hYn hYodd
  rw [hO] at hYO
  have hσC : ∀ c ∈ Subgroup.centralizer ({x} : Set L), (σ : MulAut L) c = c := by
    intro c hc
    have hc' : c ∈ Subgroup.centralizer ((zpowers x : Subgroup L) : Set L) := by
      rwa [centralizer_zpowers_eq]
    set τ : H := ⟨MulAut.conj c, hH ⟨c, rfl⟩⟩ with hτ
    have hcomm : σ * τ * σ⁻¹ * τ⁻¹ ∈ A := by
      have h1 : τ * σ⁻¹ * τ⁻¹ ∈ A := by
        have := conj_mem_involutionOddCore (hconjC c hc') (inv_mem hσ)
        simpa [hτ, mul_assoc] using this
      have := mul_mem hσ h1
      simpa [mul_assoc] using this
    have hσc : (σ : MulAut L) c ∈ Subgroup.centralizer ({x} : Set L) := by
      rw [mem_centralizer_singleton_iff] at hc ⊢
      rw [← hσx, ← map_mul, hc, map_mul]
    have hmem : (σ : MulAut L) c * c⁻¹ ∈ Y := by
      refine mem_inf.mpr ⟨⟨σ * τ * σ⁻¹ * τ⁻¹, hcomm, ?_⟩, ?_⟩
      · simp only [coe_subtype, Subgroup.coe_mul, Subgroup.coe_inv, hτ]
        rw [map_mul, map_inv, ← GrSLit.mulAut_mul_conj_mul_inv]
      · rw [centralizer_zpowers_eq]
        exact mul_mem hσc (inv_mem hc)
    have h1 := hYO hmem
    rw [mem_bot, mul_inv_eq_one] at h1
    exact h1
  have hσodd : Odd (orderOf (σ : MulAut L)) := by
    have h1 : orderOf (σ : MulAut L) = orderOf (⟨σ, hσ⟩ : A) := by
      rw [Subgroup.orderOf_mk, Subgroup.orderOf_coe]
    rw [h1]
    exact hAodd.of_dvd_nat (orderOf_dvd_natCard _)
  exact Subtype.ext (hR σ hσodd hσC)

theorem isInvolutionCoreFree_of_rigid (hZ : center L = ⊥)
    (hO : ∀ x : L, x * x = 1 → Assembly.Dichotomy.involutionOddCore x = ⊥)
    (hR : ∀ x : L, x * x = 1 → ∀ β : MulAut L, Odd (orderOf β) →
      (∀ c ∈ Subgroup.centralizer ({x} : Set L), β c = c) → β = 1) :
    IsInvolutionCoreFree L := fun H hH x hx2 =>
  involutionOddCore_eq_bot_of_rigidAt hZ (hO x hx2) (hR x hx2) H hH

end Rigid

section Faithful

variable {X : Type*} [Group X] [Finite X]

theorem commute_of_involutionCoreFree {L : Subgroup X} (hL : IsComponent L)
    (hfree : IsInvolutionCoreFree (L ⧸ Subgroup.center L)) {b : X} (hbL : b ∈ L)
    (hb2 : b * b = 1) {D : Subgroup X}
    (hD : D ≤ Assembly.Dichotomy.involutionOddCore b) :
    ∀ d ∈ D, ∀ x ∈ L, d * x = x * d := by
  have : Group.IsPerfect L := hL.1.1
  set M : Subgroup X := Subgroup.normalizer (L : Set X) with hM
  have hbM : b ∈ M := Subgroup.le_normalizer hbL
  have hDM : D ≤ M := fun d hd => LocalBalance.mem_normalizer_of_conjSub_eq
    (LocalBalance.conjSub_eq_of_mem_involutionOddCore hL hb2
      (LocalBalance.conjSub_eq_of_mem_normalizer hbM) (hD hd))
  let ρ : M →* MulAut (L ⧸ Subgroup.center L) :=
    (ComponentClassification.PerfectAutomorphisms.centerQuotientHom L).comp (normalizerConjHom L)
  have hker : ρ.ker = (Subgroup.centralizer (L : Set X)).subgroupOf M :=
    ker_centerQuotient_comp_normalizerConjHom L
  have hInn : (MulAut.conj : (L ⧸ Subgroup.center L) →* MulAut (L ⧸ Subgroup.center L)).range ≤
      ρ.range := inner_le_range_centerQuotient_comp L
  let φ : M →* ρ.range := ρ.rangeRestrict
  have hφ : Function.Surjective φ := MonoidHom.rangeRestrict_surjective ρ
  have hφker : φ.ker = ρ.ker := MonoidHom.ker_rangeRestrict ρ
  set b' : M := ⟨b, hbM⟩ with hb'
  have hb'2 : b' * b' = 1 := Subtype.ext hb2
  set bq : L ⧸ Subgroup.center L := QuotientGroup.mk' (Subgroup.center L) ⟨b, hbL⟩ with hbq
  have hbq2 : bq * bq = 1 := by
    rw [hbq, ← map_mul]
    have : (⟨b, hbL⟩ : L) * ⟨b, hbL⟩ = 1 := Subtype.ext hb2
    rw [this, map_one]
  have hρb : ρ b' = MulAut.conj bq := by
    show ComponentClassification.PerfectAutomorphisms.centerQuotientHom L
      (normalizerConjHom L b') = _
    rw [hbq, ← ComponentClassification.OuterAutomorphisms.centerQuotient_conj]
    congr 1
  have hφb : φ b' = ⟨MulAut.conj bq, hInn ⟨bq, rfl⟩⟩ := Subtype.ext hρb
  have hfr := hfree ρ.range hInn bq hbq2
  have hDle : (D.subgroupOf M).map φ ≤ ⊥ := by
    have h1 : D.subgroupOf M ≤ Assembly.Dichotomy.involutionOddCore b' := fun u hu =>
      subgroupOf_involutionOddCore_le b'
        ((Subgroup.mem_subgroupOf).mpr (hD ((Subgroup.mem_subgroupOf).mp hu)))
    refine (Subgroup.map_mono h1).trans ?_
    refine (map_involutionOddCore_le φ hφ (isPGroup_zpowers_of_mul_self_eq_one hb'2)).trans ?_
    rw [hφb, hfr]
  intro d hd x hx
  have hmem : φ ⟨d, hDM hd⟩ ∈ (⊥ : Subgroup ρ.range) :=
    hDle ⟨⟨d, hDM hd⟩, (Subgroup.mem_subgroupOf).mpr hd, rfl⟩
  have h1 : (⟨d, hDM hd⟩ : M) ∈ φ.ker := Subgroup.mem_bot.mp hmem
  rw [hφker, hker, Subgroup.mem_subgroupOf, Subgroup.mem_centralizer_iff] at h1
  exact (h1 x hx).symm

end Faithful

section Component

variable {G : Type} [Group G] [Finite G]

theorem commutator_le_oddCoreIn_of_involutionCoreFree {a b : G} {J : Subgroup G}
    (hJa : J ≤ centralizer ({a} : Set G))
    (hJ : IsPComponent 2 (J.subgroupOf (centralizer ({a} : Set G))))
    (hfree : IsInvolutionCoreFree (↥((J.subgroupOf (centralizer ({a} : Set G))).map
        (QuotientGroup.mk' (pPrimeCore 2 (centralizer ({a} : Set G))))) ⧸
      center ↥((J.subgroupOf (centralizer ({a} : Set G))).map
        (QuotientGroup.mk' (pPrimeCore 2 (centralizer ({a} : Set G)))))))
    (hbJ : b ∈ FooteLit.oddCoreIn (centralizer ({a} : Set G)) ⊔ J) (hb2 : b * b = 1) :
    ⁅J, FooteLit.oddCoreIn (centralizer ({b} : Set G)) ⊓ centralizer ({a} : Set G)⁆ ≤
      FooteLit.oddCoreIn (centralizer ({a} : Set G)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set C := centralizer ({a} : Set G) with hC
  set π := QuotientGroup.mk' (pPrimeCore 2 C) with hπ
  set W : Subgroup G := FooteLit.oddCoreIn (centralizer ({b} : Set G)) ⊓ C with hW
  have hWC : W ≤ C := inf_le_right
  set JC : Subgroup C := J.subgroupOf C with hJCdef
  set WC : Subgroup C := W.subgroupOf C with hWCdef
  set K : Subgroup (C ⧸ pPrimeCore 2 C) := JC.map π with hK
  obtain ⟨K', hK', -, hJK', -⟩ := hJ
  have hKc : IsComponent K := by rw [hK, hJK']; exact hK'
  have hOC : FooteLit.oddCoreIn C ≤ C := map_subtype_le _
  have hJN : J ≤ normalizer (FooteLit.oddCoreIn C : Set G) :=
    hJa.trans (le_normalizer_oddCoreIn C)
  obtain ⟨o, ho, j, hj, rfl⟩ := exists_mul_of_mem_sup_normalizer hJN hbJ
  have hbC : o * j ∈ C := mul_mem (hOC ho) (hJa hj)
  set bC : C := ⟨o * j, hbC⟩ with hbCdef
  have hbK : π bC ∈ K := by
    obtain ⟨o', ho', ho'o⟩ := ho
    have hπo : π o' = 1 := (QuotientGroup.eq_one_iff o').mpr ho'
    have : bC = o' * ⟨j, hJa hj⟩ := Subtype.ext (by
      show o * j = (o' : G) * j
      rw [← ho'o]
      rfl)
    rw [this, map_mul, hπo, one_mul]
    exact ⟨⟨j, hJa hj⟩, (Subgroup.mem_subgroupOf).mpr hj, rfl⟩
  have hbC2 : bC * bC = 1 := Subtype.ext hb2
  have hπb2 : π bC * π bC = 1 := by rw [← map_mul, hbC2, map_one]
  have h1 : WC ≤ Assembly.Dichotomy.involutionOddCore bC := by
    intro w hw
    rw [hWCdef, mem_subgroupOf] at hw
    have hw1 := (mem_inf.mp hw).1
    have h := GrSLit.subgroupOf_oddCore_centralizer_le C bC
      (by rw [mem_subgroupOf]; exact hw1)
    rw [Assembly.Dichotomy.involutionOddCore, Assembly.Dichotomy.oddCore_eq_pPrimeCore]
    exact h
  have h2 : WC.map π ≤ Assembly.Dichotomy.involutionOddCore (π bC) :=
    (Subgroup.map_mono h1).trans
      (map_involutionOddCore_le π (QuotientGroup.mk'_surjective _)
        (isPGroup_zpowers_of_mul_self_eq_one hbC2))
  have hcomm : ∀ d ∈ WC.map π, ∀ x ∈ K, d * x = x * d :=
    commute_of_involutionCoreFree hKc hfree hbK hπb2 h2
  have h4 : ⁅JC, WC⁆ ≤ pPrimeCore 2 C := by
    rw [commutator_le]
    intro j hj w hw
    rw [← QuotientGroup.eq_one_iff, ← QuotientGroup.mk'_apply, ← hπ, map_commutatorElement,
      commutatorElement_eq_one_iff_mul_comm]
    have hwD : π w ∈ WC.map π := ⟨w, hw, rfl⟩
    have hjK : π j ∈ K := by rw [hK]; exact ⟨j, hj, rfl⟩
    exact (hcomm _ hwD _ hjK).symm
  have h5 : ⁅J, W⁆ = ⁅JC, WC⁆.map C.subtype := by
    rw [Subgroup.map_commutator, hJCdef, hWCdef, map_subgroupOf_eq_of_le hJa,
      map_subgroupOf_eq_of_le hWC]
  rw [h5]
  exact Subgroup.map_mono h4

end Component

end CFSG.ComponentClassification.Sol76.Sig
