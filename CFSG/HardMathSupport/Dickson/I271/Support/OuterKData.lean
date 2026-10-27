module

public import CFSG.HardMathSupport.Dickson.I271.Support.OuterTransport
public import CFSG.HardMathSupport.Dickson.I271.Support.OuterStep
public import CFSG.LocalAnalysis.GLTheoremA.PartI.I1412Levels

public section

namespace CFSG.HardMathSupport.Dickson.I271

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.HardMathSupport.Solomon.LocalBalance
  CFSG.HardMathSupport.Solomon.Coordinator CFSG.HardMathSupport.Timmesfeld.Coordinator
  CFSG.HardMathSupport.Timmesfeld.ComponentBalance CFSG.LocalAnalysis.GLTheoremA
  CFSG.Yardstones.Md0ec50421ce4
open CFSG.ComponentClassification.OuterAutomorphisms (inner congr_conj)

@[expose] def KDOutExc : Prop :=
  ∀ (S : Type) [Group S] [Finite S], IsSimpleGroup S → (∃ a b : S, a * b ≠ b * a) →
    IsChevSimple 3 S → ∀ α : MulAut S, α ^ 3 = 1 → α ∉ inner S →
      ∀ I : Subgroup S, GLAPComponent 3 (fixSubgroup α) I →
        ¬ IsHatSix (↥I ⧸ GLAPPrimeCore 3 ↥I) ∧
          (IsLTwoTwentySeven (PSimple 3 I) → ∀ β : MulAut S, β ^ 3 = 1 → β * α = α * β →
            I.map β.toMonoidHom = I →
              ∃ i ∈ I, ∀ x ∈ I, β x * (i * x * i⁻¹)⁻¹ ∈ GLAPPrimeCoreOf 3 I)

section Inner

variable {X : Type} [Group X] [Finite X]

theorem exists_inner_of_subgroupOf {p : ℕ} {K J : Subgroup X} (hJK : J ≤ K) {b : X}
    (hbN : b ∈ Subgroup.normalizer (K : Set X))
    (h : ∃ i ∈ J.subgroupOf K, ∀ x ∈ J.subgroupOf K,
      K.normalizerMonoidHom ⟨b, hbN⟩ x * (i * x * i⁻¹)⁻¹ ∈ GLAPPrimeCoreOf p (J.subgroupOf K)) :
    ∃ j ∈ J, ∀ x ∈ J, b * x * b⁻¹ * (j * x * j⁻¹)⁻¹ ∈ GLAPPrimeCoreOf p J := by
  obtain ⟨i, hi, hx⟩ := h
  refine ⟨(i : X), Subgroup.mem_subgroupOf.1 hi, fun x hxJ => ?_⟩
  have h1 := hx ⟨x, hJK hxJ⟩ (Subgroup.mem_subgroupOf.2 hxJ)
  have h2 : GLAPPrimeCoreOf p J = (GLAPPrimeCoreOf p (J.subgroupOf K)).map K.subtype := by
    rw [map_glaPPrimeCoreOf_of_injective p K.subtype K.subtype_injective,
      Subgroup.map_subgroupOf_eq_of_le hJK]
  rw [h2]
  exact ⟨_, h1, by simp [coe_normalizerMonoidHom]⟩

theorem inducesInnerIn_bar {p : ℕ} (hp : p.Prime) {a : X} {B J : Subgroup X}
    (hJsn : IsSubnormal J (Subgroup.centralizer ({a} : Set X)))
    (hBC : B ≤ Subgroup.centralizer ({a} : Set X))
    (hBJ : B ≤ Subgroup.normalizer (J : Set X))
    (hinner : ∀ b ∈ B, ∃ j ∈ J, ∀ x ∈ J, b * x * b⁻¹ * (j * x * j⁻¹)⁻¹ ∈ GLAPPrimeCoreOf p J) :
    InducesInnerIn (barX p (Subgroup.centralizer ({a} : Set X)) B)
      (barX p (Subgroup.centralizer ({a} : Set X)) J) := by
  set C := Subgroup.centralizer ({a} : Set X) with hC
  have hJC : J ≤ C := hJsn.le
  intro bt hbt
  obtain ⟨c, hc, rfl⟩ := hbt.1
  have hcB : (c : X) ∈ B := Subgroup.mem_subgroupOf.1 hc
  obtain ⟨j, hjJ, hj⟩ := hinner (c : X) hcB
  set jC : ↥C := ⟨j, hJC hjJ⟩ with hjC
  refine ⟨QuotientGroup.mk' (GLAPPrimeCore p ↥C) jC, ⟨jC, Subgroup.mem_subgroupOf.2 hjJ, rfl⟩, ?_⟩
  rw [Subgroup.mem_centralizer_iff]
  rintro _ ⟨y, hy, rfl⟩
  have hyJ : (y : X) ∈ J := Subgroup.mem_subgroupOf.1 hy
  have hyinv : (y : X)⁻¹ ∈ J := J.inv_mem hyJ
  have hk := hj _ hyinv
  set o : X := (c : X) * (y : X)⁻¹ * (c : X)⁻¹ * (j * (y : X)⁻¹ * j⁻¹)⁻¹ with ho
  have hoJ : o ∈ GLAPPrimeCoreOf p J := hk
  have hcN : (c : X)⁻¹ ∈ Subgroup.normalizer (J : Set X) := inv_mem (hBJ hcB)
  have hoO : (c : X)⁻¹ * o⁻¹ * (c : X) ∈ GLAPPrimeCoreOf p J := by
    have hnorm := CFSG.LocalAnalysis.GLTheoremA.normalizer_le_normalizer_glaPPrimeCoreOf p J hcN
    have := (Subgroup.mem_normalizer_iff.1 hnorm o⁻¹).1 ((GLAPPrimeCoreOf p J).inv_mem hoJ)
    simpa using this
  have hOC : GLAPPrimeCoreOf p J ≤ GLAPPrimeCoreOf p C := glaPPrimeCoreOf_le_of_isSubnormal hp hJsn
  obtain ⟨z, hz, hzx⟩ := hOC hoO
  have hkey : (y * (jC⁻¹ * c))⁻¹ * ((jC⁻¹ * c) * y) ∈ GLAPPrimeCore p ↥C := by
    have h1 : (y * (jC⁻¹ * c))⁻¹ * ((jC⁻¹ * c) * y) = z := by
      apply Subtype.ext
      have hzx' : (z : X) = (c : X)⁻¹ * o⁻¹ * (c : X) := hzx
      rw [hzx']
      simp [hjC, ho]
      group
    rw [h1]
    exact hz
  have h : ((y * (jC⁻¹ * c) : ↥C) : ↥C ⧸ GLAPPrimeCore p ↥C) =
      ((jC⁻¹ * c * y : ↥C) : ↥C ⧸ GLAPPrimeCore p ↥C) := QuotientGroup.eq.2 hkey
  simpa [QuotientGroup.mk'_apply] using h

end Inner

section Main

variable {X : Type} [Group X] [Finite X]

theorem coprime_ker_mulEquiv {p : ℕ} {S T : Type} [Group S] [Group T] (e : S ≃* T)
    (A : Subgroup S) : Nat.Coprime p (Nat.card ↥(A ⊓ e.toMonoidHom.ker)) := by
  have hk : e.toMonoidHom.ker = ⊥ := (MonoidHom.ker_eq_bot_iff e.toMonoidHom).2 e.injective
  rw [hk, inf_bot_eq, Subgroup.card_bot]
  exact Nat.coprime_one_right p

theorem map_normalizerMonoidHom_subgroupOf {K J : Subgroup X} {b : X}
    (hbK : b ∈ Subgroup.normalizer (K : Set X)) (hbJ : b ∈ Subgroup.normalizer (J : Set X))
    (hJK : J ≤ K) :
    (J.subgroupOf K).map (K.normalizerMonoidHom ⟨b, hbK⟩).toMonoidHom = J.subgroupOf K := by
  ext z
  constructor
  · rintro ⟨x, hx, rfl⟩
    have hx' : (x : X) ∈ J := Subgroup.mem_subgroupOf.1 hx
    exact Subgroup.mem_subgroupOf.2 ((Subgroup.mem_normalizer_iff.1 hbJ x).1 hx')
  · intro hz
    have hz' : (z : X) ∈ J := Subgroup.mem_subgroupOf.1 hz
    refine ⟨K.normalizerMonoidHom ⟨b⁻¹, inv_mem hbK⟩ z, ?_, ?_⟩
    · refine Subgroup.mem_subgroupOf.2 ?_
      have := (Subgroup.mem_normalizer_iff.1 (inv_mem hbJ) z).1 hz'
      simpa [coe_normalizerMonoidHom] using this
    · apply Subtype.ext
      simp [coe_normalizerMonoidHom]
      group

theorem normalizerMonoidHom_not_mem_inner {K : Subgroup X} {a : X}
    (haN : a ∈ Subgroup.normalizer (K : Set X))
    (hout : ¬ ∃ k ∈ K, k⁻¹ * a ∈ Subgroup.centralizer (K : Set X)) :
    K.normalizerMonoidHom ⟨a, haN⟩ ∉ inner ↥K := by
  rintro ⟨k', hk'⟩
  apply hout
  refine ⟨(k' : X), k'.2, ?_⟩
  rw [Subgroup.mem_centralizer_iff]
  intro x hx
  have h1 := congrArg Subtype.val (DFunLike.congr_fun hk' ⟨x, hx⟩)
  have h2 : (k' : X) * x * (k' : X)⁻¹ = a * x * a⁻¹ := by
    simpa [MulAut.conj_apply, coe_normalizerMonoidHom] using h1
  calc x * ((k' : X)⁻¹ * a) = (k' : X)⁻¹ * ((k' : X) * x * (k' : X)⁻¹) * a := by group
    _ = (k' : X)⁻¹ * (a * x * a⁻¹) * a := by rw [h2]
    _ = ((k' : X)⁻¹ * a) * x := by group

theorem chevCentralizerStep_of_kdata
    (hU : ∀ p : ℕ, p.Prime → p ≠ 2 → KDChevUnique p)
    (hT : ∀ p : ℕ, p.Prime → p ≠ 2 → KDOutChev p) (hE : KDOutExc) : ChevCentralizerStep := by
  intro X _ _ p K B hH hLie hZ a haB ha1 hout
  have hp := hH.prime
  have hp2 := hH.odd
  haveI : Fact p.Prime := ⟨hp⟩
  have hq := hH.quasi
  have haN : a ∈ Subgroup.normalizer (K : Set X) := hH.norm haB
  have hap : a ^ p = 1 := hH.elem.2 a haB
  let eQ : (↥K ⧸ Subgroup.center ↥K) ≃* ↥K :=
    (QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot
  haveI hsimpQ : IsSimpleGroup (↥K ⧸ Subgroup.center ↥K) := hq.2
  haveI hsimp : IsSimpleGroup ↥K := eQ.symm.isSimpleGroup
  have hnc : ∃ x y : ↥K, x * y ≠ y * x := by
    obtain ⟨u, v, huv⟩ := exists_noncomm_of_isQuasisimple hq
    exact ⟨eQ u, eQ v, fun h => huv (eQ.injective (by rw [map_mul, map_mul]; exact h))⟩
  have hChevK : IsChevSimple p ↥K := isChevSimple_of_mulEquiv eQ hH.chev
  set α : MulAut ↥K := K.normalizerMonoidHom ⟨a, haN⟩ with hαdef
  have hα : α ^ p = 1 := by
    rw [hαdef, ← map_pow]
    have : (⟨a, haN⟩ : ↥(Subgroup.normalizer (K : Set X))) ^ p = 1 :=
      Subtype.ext (by simpa using hap)
    rw [this, map_one]
  have hαout : α ∉ inner ↥K := normalizerMonoidHom_not_mem_inner haN hout
  have hcompK : ∀ J : Subgroup X, GLAPComponent p (K ⊓ Subgroup.centralizer ({a} : Set X)) J →
      GLAPComponent p (fixSubgroup α) (J.subgroupOf K) := fun J hJ =>
    glaPComponent_fixSubgroup hp haN hJ
  have huniq : ∀ I J : Subgroup X, GLAPComponent p (K ⊓ Subgroup.centralizer ({a} : Set X)) I →
      GLAPComponent p (K ⊓ Subgroup.centralizer ({a} : Set X)) J → I = J := by
    intro I J hI hJ
    have h := hU p hp hp2 ↥K hsimp hnc hChevK α hα _ _ (hcompK I hI) (hcompK J hJ)
    have hIK : I ≤ K := hI.1.trans inf_le_left
    have hJK : J ≤ K := hJ.1.trans inf_le_left
    have := (Subgroup.subgroupOf_inj).1 h
    rwa [inf_of_le_left hIK, inf_of_le_left hJK] at this
  refine ⟨huniq, fun J hJ => ?_⟩
  set C := Subgroup.centralizer ({a} : Set X) with hC
  have hJC : J ≤ C := hJ.1.trans inf_le_right
  have hJK : J ≤ K := hJ.1.trans inf_le_left
  have hJcomp : GLAPComponent p C J := glaPComponent_centralizer hp hH.comp.2.1 hJ
  have hsn : IsSubnormal J C := hJcomp.2.1
  have hBN : B ≤ Subgroup.normalizer (J : Set X) :=
    le_normalizer_of_unique hH.norm hH.elem haB huniq hJ
  have hBC : B ≤ C := fun b hb =>
    Subgroup.mem_centralizer_singleton_iff.2 (CFSG.Open.IsElemAbelian.comm hH.elem hb haB)
  have hI : GLAPComponent p (fixSubgroup α) (J.subgroupOf K) := hcompK J hJ
  let fI : ↥(J.subgroupOf K) ≃* ↥J := Subgroup.subgroupOfEquivOfLe hJK
  let pS : PSimple p (J.subgroupOf K) ≃* (↥(barX p C J) ⧸ Subgroup.center ↥(barX p C J)) :=
    (pSimpleEquiv p fI).trans (pSimpleBarEquiv hp hJC hsn)
  refine ⟨?_, ?_⟩
  ·
    obtain ⟨idx, ⟨e0⟩, hchar⟩ := hLie
    let e : ↥K ≃* (TauCeti.CFSGIndex.lie idx).Group := eQ.symm.trans e0
    have hα1 : α ≠ 1 := fun h => hαout (h ▸ one_mem _)
    have hα' : MulAut.congr e α ^ p = 1 := by rw [← map_pow, hα, map_one]
    have hα'1 : MulAut.congr e α ≠ 1 := fun h =>
      hα1 ((MulAut.congr e).injective (by rw [h, map_one]))
    have hord : orderOf (MulAut.congr e α) = p := orderOf_eq_prime hα' hα'1
    have hα'out : MulAut.congr e α ∉
        (MulAut.conj : (TauCeti.CFSGIndex.lie idx).Group →* _).range := by
      rintro ⟨g, hg⟩
      apply hαout
      show α ∈ (MulAut.conj : ↥K →* MulAut ↥K).range
      rw [MonoidHom.mem_range]
      refine ⟨e.symm g, ?_⟩
      have : MulAut.congr e.symm (MulAut.congr e α) = α := by
        ext x
        simp [MulAut.congr_apply]
      rw [← this, ← hg, congr_conj]
    have hI' := glaPComponent_map hp e.toMonoidHom (coprime_ker_mulEquiv e (fixSubgroup α)) hI
    rw [← fixSubgroup_congr e α] at hI'
    have hty := hT p hp hp2 idx hchar _ hord hα'out _ hI'
    exact isChevSimple_of_mulEquiv
      ((pSimpleEquiv p (e.subgroupMap (J.subgroupOf K)).symm).trans pS) hty
  ·
    rintro ⟨h3, hb | hc⟩
    · obtain ⟨hL27, hninn⟩ := hb
      subst h3
      apply hninn
      have hL27' : IsLTwoTwentySeven (PSimple 3 (J.subgroupOf K)) :=
        isLTwoTwentySeven_of_mulEquiv pS.symm hL27
      refine inducesInnerIn_bar hp hsn hBC hBN fun b hb => ?_
      have hbK : b ∈ Subgroup.normalizer (K : Set X) := hH.norm hb
      have hba : b * a = a * b := (CFSG.Open.IsElemAbelian.comm hH.elem hb haB).symm ▸ rfl
      have hb3 : b ^ 3 = 1 := hH.elem.2 b hb
      have hβ3 : K.normalizerMonoidHom ⟨b, hbK⟩ ^ 3 = 1 := by
        rw [← map_pow]
        have : (⟨b, hbK⟩ : ↥(Subgroup.normalizer (K : Set X))) ^ 3 = 1 :=
          Subtype.ext (by simpa using hb3)
        rw [this, map_one]
      have hβα : K.normalizerMonoidHom ⟨b, hbK⟩ * α = α * K.normalizerMonoidHom ⟨b, hbK⟩ := by
        rw [hαdef, ← map_mul, ← map_mul]
        congr 1
        exact Subtype.ext (CFSG.Open.IsElemAbelian.comm hH.elem hb haB)
      have hmap := map_normalizerMonoidHom_subgroupOf hbK (hBN hb) hJK
      have := (hE ↥K hsimp hnc hChevK α hα hαout _ hI).2 hL27' _ hβ3 hβα hmap
      exact exists_inner_of_subgroupOf hJK hbK this
    · obtain ⟨hHat, -⟩ := hc
      subst h3
      let fQ : PQuot 3 (J.subgroupOf K) ≃* ↥(barX 3 C J) :=
        (pQuotEquiv 3 fI).trans (quotEquivBarX hp hJC hsn)
      exact (hE ↥K hsimp hnc hChevK α hα hαout _ hI).1 (isHatSix_of_mulEquiv fQ.symm hHat)

end Main

end CFSG.HardMathSupport.Dickson.I271
