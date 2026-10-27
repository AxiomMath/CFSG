module

public import CFSG.LocalAnalysis.ComponentClassification.CTUSol76SigInvCore
public import Certificates.Kernel.ThCent.Leaves

public section

namespace CFSG.ComponentClassification.Sol76.Sig

open CFSG Subgroup CFSG.ClassicalInvolution.Balance CFSG.ClassicalInvolution.Balance.LocalBalance
  CFSG.LocalAnalysis.ComponentInitial

@[expose] def IsInvolutionCoreFreeInv (X : Type*) [Group X] : Prop :=
  ∀ H : Subgroup (MulAut (X ⧸ center X)),
    ∀ hH : (MulAut.conj : (X ⧸ center X) →* MulAut (X ⧸ center X)).range ≤ H,
    ∀ y : X, y * y = 1 →
      Assembly.Dichotomy.involutionOddCore
        (⟨MulAut.conj (QuotientGroup.mk y : X ⧸ center X), hH ⟨_, rfl⟩⟩ : H) = ⊥

theorem isInvolutionCoreFreeInv_of_quot {X : Type*} [Group X]
    (h : IsInvolutionCoreFree (X ⧸ center X)) : IsInvolutionCoreFreeInv X := fun H hH y hy =>
  h H hH _ (by rw [← QuotientGroup.mk_mul, hy, QuotientGroup.mk_one])

section Transport

variable {L L' : Type*} [Group L] [Group L']

theorem involutionOddCore_conj_eq_bot_of_mulEquiv [Finite L'] (e : L ≃* L') {x' : L'}
    (hx'2 : x' * x' = 1)
    (h : ∀ H : Subgroup (MulAut L), ∀ hH : (MulAut.conj : L →* MulAut L).range ≤ H,
      Assembly.Dichotomy.involutionOddCore (⟨MulAut.conj (e.symm x'), hH ⟨_, rfl⟩⟩ : H) = ⊥)
    (H' : Subgroup (MulAut L')) (hH' : (MulAut.conj : L' →* MulAut L').range ≤ H') :
    Assembly.Dichotomy.involutionOddCore (⟨MulAut.conj x', hH' ⟨x', rfl⟩⟩ : H') = ⊥ := by
  have : Finite (MulAut L') := inferInstance
  set c : MulAut L ≃* MulAut L' := MulAut.congr e with hc
  set H : Subgroup (MulAut L) := H'.comap c.toMonoidHom with hHdef
  have hH : (MulAut.conj : L →* MulAut L).range ≤ H := by
    rintro _ ⟨l, rfl⟩
    show c (MulAut.conj l) ∈ H'
    rw [hc, mulAut_congr_conj]
    exact hH' ⟨e l, rfl⟩
  set x : L := e.symm x' with hx
  have h0 := h H hH
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

theorem isInvolutionCoreFreeInv_of_mulEquiv {X X' : Type*} [Group X] [Group X'] [Finite X']
    (e : X ≃* X') (h : IsInvolutionCoreFreeInv X) : IsInvolutionCoreFreeInv X' := by
  intro H' hH' y' hy'2
  set ē : (X ⧸ center X) ≃* (X' ⧸ center X') :=
    QuotientGroup.congr (center X) (center X') e (Subgroup.map_center_eq e) with hē
  have hmk : ē.symm (QuotientGroup.mk y') = QuotientGroup.mk (e.symm y') := by
    rw [MulEquiv.symm_apply_eq, hē, QuotientGroup.congr_mk, MulEquiv.apply_symm_apply]
  have hy2 : e.symm y' * e.symm y' = 1 := by rw [← map_mul, hy'2, map_one]
  refine involutionOddCore_conj_eq_bot_of_mulEquiv ē
    (by rw [← QuotientGroup.mk_mul, hy'2, QuotientGroup.mk_one]) (fun H hH => ?_) H' hH'
  have key : ∀ (z : X ⧸ center X) (hz : z = QuotientGroup.mk (e.symm y')),
      Assembly.Dichotomy.involutionOddCore (⟨MulAut.conj z, hH ⟨z, rfl⟩⟩ : H) = ⊥ := by
    rintro z rfl
    exact h H hH (e.symm y') hy2
  exact key _ hmk

section Faithful

variable {X : Type*} [Group X] [Finite X]

theorem commute_of_involutionCoreFreeInv {L : Subgroup X} (hL : IsComponent L)
    (hfree : IsInvolutionCoreFreeInv ↥L) {b : X} (hbL : b ∈ L)
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
  have hρb : ρ b' = MulAut.conj bq := by
    show ComponentClassification.PerfectAutomorphisms.centerQuotientHom L
      (normalizerConjHom L b') = _
    rw [hbq, ← ComponentClassification.OuterAutomorphisms.centerQuotient_conj]
    congr 1
  have hφb : φ b' = ⟨MulAut.conj bq, hInn ⟨bq, rfl⟩⟩ := Subtype.ext hρb
  have hbL2 : (⟨b, hbL⟩ : L) * ⟨b, hbL⟩ = 1 := Subtype.ext hb2
  have hfr := hfree ρ.range hInn ⟨b, hbL⟩ hbL2
  have hDle : (D.subgroupOf M).map φ ≤ ⊥ := by
    have h1 : D.subgroupOf M ≤ Assembly.Dichotomy.involutionOddCore b' := fun u hu =>
      subgroupOf_involutionOddCore_le b'
        ((Subgroup.mem_subgroupOf).mpr (hD ((Subgroup.mem_subgroupOf).mp hu)))
    refine (Subgroup.map_mono h1).trans ?_
    refine (map_involutionOddCore_le φ hφ (isPGroup_zpowers_of_mul_self_eq_one hb'2)).trans ?_
    rw [hφb]
    exact le_of_eq hfr
  intro d hd x hx
  have hmem : φ ⟨d, hDM hd⟩ ∈ (⊥ : Subgroup ρ.range) :=
    hDle ⟨⟨d, hDM hd⟩, (Subgroup.mem_subgroupOf).mpr hd, rfl⟩
  have h1 : (⟨d, hDM hd⟩ : M) ∈ φ.ker := Subgroup.mem_bot.mp hmem
  rw [hφker, hker, Subgroup.mem_subgroupOf, Subgroup.mem_centralizer_iff] at h1
  exact (h1 x hx).symm

end Faithful

section Component

variable {G : Type} [Group G] [Finite G]

theorem commutator_le_oddCoreIn_of_involutionCoreFreeInv {a b : G} {J : Subgroup G}
    (hJa : J ≤ centralizer ({a} : Set G))
    (hJ : IsPComponent 2 (J.subgroupOf (centralizer ({a} : Set G))))
    (hfree : IsInvolutionCoreFreeInv ↥((J.subgroupOf (centralizer ({a} : Set G))).map
        (QuotientGroup.mk' (pPrimeCore 2 (centralizer ({a} : Set G))))))
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
    commute_of_involutionCoreFreeInv hKc hfree hbK hπb2 h2
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
