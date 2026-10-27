module

public import CFSG.LocalAnalysis.ComponentClassification.SolMaxFiveN
public import CFSG.LocalAnalysis.ComponentClassification.SolMaxFiveT
public import CFSG.LocalAnalysis.ComponentClassification.SolMaxSigSwapNarrow
public import CFSG.Goldschmidt.Statements
public import CFSG.Goldschmidt.StatementsG4
public import CFSG.Goldschmidt.StatementsH
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherComponentInvolutionFitting
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherComponentInvolutionMoved
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherKnownGroupLemma37Statement
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTheorem5DeltaGlobalLSide
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherToolkitGlaubermanCore
public import CFSG.LocalAnalysis.ComponentClassification.FittingNilpotence
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitKG
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitPSL
public import CFSG.LocalAnalysis.ComponentClassification.Sol76T13L32Props
public import CFSG.LocalAnalysis.ComponentClassification.SolMaxClaimA11Q
public import CFSG.LocalAnalysis.ComponentClassification.SolMaxClaimA9K
public import CFSG.LocalAnalysis.ComponentClassification.SolMaxDiagD
public import CFSG.LocalAnalysis.ComponentClassification.SolMaxFiveB
public import CFSG.LocalAnalysis.ComponentClassification.SolMaxFiveM
public import CFSG.LocalAnalysis.ComponentClassification.SolMaxNineB
public import CFSG.LocalAnalysis.ComponentClassification.SolMaxNineC
public import CFSG.LocalAnalysis.ComponentClassification.SolMaxNineD
public import CFSG.LocalAnalysis.ComponentClassification.SolMaxSig36Y
public import CFSG.LocalAnalysis.ComponentClassification.SolMaxSig36ZB
public import CFSG.LocalAnalysis.ComponentClassification.SolMaxSig36ZC
public import CFSG.LocalAnalysis.ComponentClassification.SolMaxSmallN
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.AschbacherCanonicalRemaining
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.ExceptionalEightPlaneCentralizer
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.UnitaryRootAutomorphism
public import CFSG.Permutation.BurnsideSchur
public import CFSG.Walter.PSL2Facts
public import Certificates.Certificate7000
public import Certificates.Certificate7001
public import Certificates.Certificate7002
public import Certificates.Certificate7003
public import Certificates.Certificate7004
public import Certificates.Certificate7005
public import Certificates.Certificate7006
public import Certificates.Certificate7007
public import Certificates.Certificate7008
public import Certificates.Certificate7009
public import Certificates.Certificate7010
public import Certificates.Certificate7011

public section

namespace CFSG.ComponentClassification.SolMax

open CFSG Subgroup Equiv

variable {X : Type} [Group X]

theorem mem_of_mem_sup_odd_of_pow [Finite X] {U Y₀ : Subgroup X}
    (hYU : Y₀ ≤ normalizer (U : Set X)) (hodd : Odd (Nat.card Y₀)) {y : X} (hy : y ∈ U ⊔ Y₀)
    {k : ℕ} (hk : y ^ (2 ^ k) = 1) : y ∈ U := by
  classical
  set G : Subgroup X := U ⊔ Y₀ with hGdef
  have hGN : G ≤ normalizer (U : Set X) := sup_le le_normalizer hYU
  have : (U.subgroupOf G).Normal := Subgroup.normal_subgroupOf_of_le_normalizer hGN
  set N := U.subgroupOf G with hNdef
  have hy' : y ∈ ((Y₀ ⊔ U : Subgroup X) : Set X) := by rw [sup_comm]; exact hy
  rw [coe_mul_of_left_le_normalizer_right Y₀ U hYU] at hy'
  obtain ⟨y₀, hy₀, u, hu, hyu⟩ := hy'
  have hy₀G : y₀ ∈ G := mem_sup_right hy₀
  have huG : u ∈ G := mem_sup_left hu
  set π : ↥G →* ↥G ⧸ N := QuotientGroup.mk' N with hπdef
  have hyG : (⟨y, hy⟩ : ↥G) = ⟨y₀, hy₀G⟩ * ⟨u, huG⟩ := Subtype.ext hyu.symm
  have hu1 : π ⟨u, huG⟩ = 1 := (QuotientGroup.eq_one_iff _).mpr (by rw [mem_subgroupOf]; exact hu)
  have himg : π ⟨y, hy⟩ = π ⟨y₀, hy₀G⟩ := by rw [hyG, map_mul, hu1, mul_one]
  have h1 : orderOf (π ⟨y, hy⟩) ∣ 2 ^ k := by
    apply orderOf_dvd_of_pow_eq_one
    rw [← map_pow]
    have : (⟨y, hy⟩ : ↥G) ^ (2 ^ k) = 1 := Subtype.ext (by simpa using hk)
    rw [this, map_one]
  have h2 : orderOf (π ⟨y, hy⟩) ∣ Nat.card Y₀ := by
    rw [himg]
    refine (orderOf_map_dvd π _).trans ?_
    rw [Subgroup.orderOf_mk]
    have := orderOf_dvd_natCard (⟨y₀, hy₀⟩ : ↥Y₀)
    rwa [Subgroup.orderOf_mk] at this
  have h3 : orderOf (π ⟨y, hy⟩) = 1 := by
    have hcop : Nat.Coprime (2 ^ k) (Nat.card Y₀) :=
      Nat.Coprime.pow_left k (Nat.coprime_two_left.mpr hodd)
    exact Nat.Coprime.eq_one_of_dvd (Nat.Coprime.coprime_dvd_left h1 hcop) h2
  rw [orderOf_eq_one_iff, hπdef, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff,
    mem_subgroupOf] at h3
  exact h3

theorem oPrimeResidualOf_sup_odd [Finite X] {U Y₀ : Subgroup X}
    (hYU : Y₀ ≤ normalizer (U : Set X)) (hodd : Odd (Nat.card Y₀)) :
    GH74.GLS.oPrimeResidualOf 2 (U ⊔ Y₀) = GH74.GLS.oPrimeResidualOf 2 U := by
  rw [Sol78.oPrimeResidualOf_eq_closure, Sol78.oPrimeResidualOf_eq_closure]
  apply le_antisymm
  · refine closure_mono fun y ⟨hy, k, hk⟩ => ⟨mem_of_mem_sup_odd_of_pow hYU hodd hy hk, k, hk⟩
  · exact closure_mono fun y ⟨hy, k, hk⟩ => ⟨mem_sup_left hy, k, hk⟩

theorem inf_centralizer_eq_fixedLayer_sup [Finite X] {M T : Subgroup X}
    (hMq : IsQuasisimple (↥M ⧸ pPrimeCore 2 ↥M)) (hTM : T ≤ UnbalancedLayer.coreActionKernel M)
    (hT2 : IsPGroup 2 T) :
    M ⊓ centralizer (T : Set X) = GSLit.fixedLayer M T ⊔
      ((pPrimeCore 2 ↥M).map M.subtype ⊓ centralizer (T : Set X)) := by
  obtain ⟨hsup, -⟩ := GSLit.fixedLayer_sup_pPrimeCore hMq hTM hT2
  have hMTle : GSLit.fixedLayer M T ≤ M ⊓ centralizer (T : Set X) := GSLit.fixedLayer_le_inf M T
  apply le_antisymm
  · intro x hx
    have hxM : x ∈ ((GSLit.fixedLayer M T ⊔ (pPrimeCore 2 ↥M).map M.subtype : Subgroup X) :
        Set X) := by rw [hsup]; exact hx.1
    have hnorm : GSLit.fixedLayer M T ≤
        normalizer (((pPrimeCore 2 ↥M).map M.subtype : Subgroup X) : Set X) := fun y hy =>
      le_normalizer_pPrimeCore (le_normalizer (hMTle hy).1)
    rw [coe_mul_of_left_le_normalizer_right _ _ hnorm] at hxM
    obtain ⟨a, ha, b, hb, rfl⟩ := hxM
    have hbC : b ∈ centralizer (T : Set X) := by
      have hb' : b = a⁻¹ * (a * b) := by group
      rw [hb']
      exact mul_mem (inv_mem (hMTle ha).2) hx.2
    exact mul_mem (mem_sup_left ha) (mem_sup_right ⟨hb, hbC⟩)
  · exact sup_le hMTle (inf_le_inf_right _ (map_subtype_le _))

theorem core_inf_centralizer_le_normalizer_fixedLayer [Finite X] {M T : Subgroup X} :
    (pPrimeCore 2 ↥M).map M.subtype ⊓ centralizer (T : Set X) ≤
      normalizer ((GSLit.fixedLayer M T : Subgroup X) : Set X) := fun g hg =>
  Sol78.le_normalizer_map_subtype (pLayer ↥(M ⊓ centralizer (T : Set X)) 2)
    (⟨map_subtype_le _ hg.1, hg.2⟩ : g ∈ M ⊓ centralizer (T : Set X))

theorem odd_card_core_inf {M Y : Subgroup X} [Finite X] :
    Odd (Nat.card ((pPrimeCore 2 ↥M).map M.subtype ⊓ Y : Subgroup X)) := by
  have h1 : Odd (Nat.card ((pPrimeCore 2 ↥M).map M.subtype)) := by
    rw [Subgroup.card_map_of_injective M.subtype_injective]
    exact Nat.coprime_two_left.mp pPrimeCore_coprime_card
  exact h1.of_dvd_nat (Subgroup.card_dvd_of_le inf_le_left)

theorem le_fixedLayer_of_primeResidual [Finite X] {M T L : Subgroup X}
    (hMq : IsQuasisimple (↥M ⧸ pPrimeCore 2 ↥M)) (hTM : T ≤ UnbalancedLayer.coreActionKernel M)
    (hT2 : IsPGroup 2 T) (hLM : L ≤ M ⊓ centralizer (T : Set X))
    (hL : CatalogueBPrimeJoin.primeResidual 2 L = ⊤) : L ≤ GSLit.fixedLayer M T := by
  have h1 := Sol78.le_oPrimeResidualOf hLM hL
  rw [inf_centralizer_eq_fixedLayer_sup hMq hTM hT2,
    oPrimeResidualOf_sup_odd core_inf_centralizer_le_normalizer_fixedLayer odd_card_core_inf] at h1
  exact h1.trans (Sol78.oPrimeResidualOf_le _)

theorem isSolomonMember_of_fixedLayer [Finite X] {M T : Subgroup X} (hperf : ⁅M, M⁆ = M)
    (hMq : IsQuasisimple (↥M ⧸ pPrimeCore 2 ↥M)) (hT : T ≠ ⊥) (hT2 : IsPGroup 2 T)
    (hTM : T ≤ UnbalancedLayer.coreActionKernel M)
    (hMT : FooteLit.IsTwoComponentIn (GSLit.fixedLayer M T) (centralizer (T : Set X))) :
    FooteLit.IsSolomonMember M := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hMTC, hpc⟩ := hMT
  set C := centralizer (T : Set X) with hCdef
  set MT := GSLit.fixedLayer M T with hMTdef
  set OM := (pPrimeCore 2 ↥M).map M.subtype with hOMdef
  have hMC : M ⊓ C = MT ⊔ (OM ⊓ C) := inf_centralizer_eq_fixedLayer_sup hMq hTM hT2
  set OC := FooteLit.oddCoreIn C with hOCdef
  have hY₀N : OM ⊓ C ≤ normalizer ((OC ⊔ MT : Subgroup X) : Set X) := fun g hg =>
    sup_mem_normalizer (Sol78.le_normalizer_map_subtype (pPrimeCore 2 ↥C) hg.2)
      (core_inf_centralizer_le_normalizer_fixedLayer hg)
  have hY₀odd : Odd (Nat.card (OM ⊓ C : Subgroup X)) := odd_card_core_inf
  have heq : OC ⊔ (M ⊓ C) = (OC ⊔ MT) ⊔ (OM ⊓ C) := by rw [hMC, sup_assoc]
  refine ⟨hperf, T, hT, hT2, hTM, ?_⟩
  rw [heq, Sol78.oddResidualIn_eq_oPrimeResidualOf, oPrimeResidualOf_sup_odd hY₀N hY₀odd]
  change GH74.GLS.IsPCompIn 2 C (GH74.GLS.oPrimeResidualOf 2 (GH74.GLS.pPrimeCoreOf 2 C ⊔ MT))
  rw [Sol78.oPrimeResidualOf_core_sup_eq hMTC hpc]
  exact ⟨hMTC, hpc⟩

theorem oddCore_le_of_four_centralizer_le [Finite X] {H F : Subgroup X} {r : X}
    (hFk : Nonempty (F ≃* Multiplicative (ZMod 2) × Multiplicative (ZMod 2)))
    (hFr : F ≤ centralizer ({r} : Set X))
    (hFH : ∀ f ∈ F, f ≠ 1 → centralizer ({f} : Set X) ≤ H) :
    (pPrimeCore 2 ↥(centralizer ({r} : Set X))).map (centralizer ({r} : Set X)).subtype ≤ H := by
  classical
  set Or := (pPrimeCore 2 ↥(centralizer ({r} : Set X))).map (centralizer ({r} : Set X)).subtype
    with hOrdef
  have hFO : F ≤ normalizer (Or : Set X) :=
    hFr.trans (Sol78.le_normalizer_map_subtype (pPrimeCore 2 (centralizer ({r} : Set X))))
  have hodd : Odd (Nat.card Or) := by
    rw [hOrdef, Subgroup.card_map_of_injective (centralizer ({r} : Set X)).subtype_injective]
    exact Nat.coprime_two_left.mp pPrimeCore_coprime_card
  obtain ⟨hF4, hFsq⟩ := card_sq_of_klein hFk
  have : IsKleinFour ↥F := isKleinFour_of_card hF4 fun g => Subtype.ext (by
    rw [← sq]; exact hFsq g g.2)
  obtain ⟨a₁, a₂, a₃, h₁, h₂, h₃, h₁₁, h₂₁, h₃₁, h₁₂, h₁₃, h₂₃⟩ := exists_three_of_klein hFk
  have hprod := ABGLocalTools.four_group_odd_eq_mul_centralizers hodd hFO h₁ h₂ h₃ h₁₁ h₂₁ h₃₁
    h₁₂ h₁₃ h₂₃
  intro y hy
  have hy' : y ∈ (Or : Set X) := hy
  rw [hprod] at hy'
  obtain ⟨_, ⟨c₁, hc₁, c₂, hc₂, rfl⟩, c₃, hc₃, rfl⟩ := hy'
  exact mul_mem (mul_mem (hFH a₁ h₁ h₁₁ hc₁.2) (hFH a₂ h₂ h₂₁ hc₂.2)) (hFH a₃ h₃ h₃₁ hc₃.2)

namespace Sig36

variable [Finite X] [IsSimpleGroup X] {t : X} {J : Subgroup X} {n : ℕ}
  {e : J ⧸ pPrimeCore 2 J ≃* alternatingGroup (Fin n)} {E : Subgroup X} {D : Finset (Fin n)}
  (S : Sig36 X t J n e E D)
include S

theorem exists_perm_compat_of_swap {M : Subgroup X}
    (hCH : centralizer ({t} : Set X) ≤ normalizer (Sol78.signalizerCompletion E E : Set X))
    (hMH : M ≤ normalizer (Sol78.signalizerCompletion E E : Set X))
    (hMpc : IsPComponent 2 (M.subgroupOf (normalizer (Sol78.signalizerCompletion E E : Set X))))
    (hne : M.map (MulAut.conj t).toMonoidHom ≠ M)
    (hJM : J ≤ M ⊔ M.map (MulAut.conj t).toMonoidHom)
    {θ : ↥M ⧸ pPrimeCore 2 ↥M ≃* alternatingGroup (Fin n)}
    {ρ : ↥(normalizer (M : Set X)) →* Perm (Fin n)} (hρ : IsPermAction θ ρ) :
    ∃ π : Perm (Fin n), ∀ (j : X) (hj : j ∈ J) (hjN : j ∈ normalizer (M : Set X)),
      ρ ⟨j, hjN⟩ = π * coreImage e hj * π⁻¹ := by
  classical
  have hn9 := S.nine_le
  have hJN := le_normalizer_of_swap (hCH (mem_centralizer_singleton_iff.mpr rfl)) hMH hMpc hne hJM
  have hJK := S.not_le_coreActionKernel_of_swap hCH hMH hMpc hne hJM θ
  have hperf : ⁅J, J⁆ = J :=
    UnbalancedCorr.commutator_eq_of_isPComponent S.pair.1.2.1 S.pair.1.2.2.1
  have hQ : Nat.card (alternatingGroup (Fin n)) ≤ n.factorial / 2 := by
    have : Nontrivial (Fin n) := Fin.nontrivial_iff_two_le.mpr (by omega)
    rw [nat_card_alternatingGroup, Nat.card_fin]
  have halt : ∀ (y : X) (hy : y ∈ J), ρ ⟨y, hJN hy⟩ ∈ alternatingGroup (Fin n) :=
    fun y hy => IsPermAction.mem_alternatingGroup_of_perfect hJN hperf hy
  obtain ⟨hsurj, hO⟩ := hρ.image_eq_of_le hJN (by omega) e hperf hJK hQ halt
  let φ₀ : ↥J →* alternatingGroup (Fin n) :=
    (ρ.comp (inclusion hJN)).codRestrict (alternatingGroup (Fin n)) fun y => halt y y.2
  have hker : pPrimeCore 2 ↥J ≤ φ₀.ker := by
    intro y hy
    rw [MonoidHom.mem_ker]
    exact Subtype.ext (hO y y.2 ⟨y, hy, rfl⟩)
  let φ : ↥J ⧸ pPrimeCore 2 ↥J →* alternatingGroup (Fin n) :=
    QuotientGroup.lift (pPrimeCore 2 ↥J) φ₀ hker
  have hφs : Function.Surjective φ := by
    intro g
    obtain ⟨y, hy, hyg⟩ := hsurj g g.2
    exact ⟨((⟨y, hy⟩ : ↥J) : ↥J ⧸ pPrimeCore 2 ↥J), Subtype.ext hyg⟩
  let ψ₀ : alternatingGroup (Fin n) →* alternatingGroup (Fin n) := φ.comp e.symm.toMonoidHom
  have hψs : Function.Surjective ψ₀ := hφs.comp e.symm.surjective
  have hψb : Function.Bijective ψ₀ := ⟨Finite.injective_iff_surjective.mpr hψs, hψs⟩
  obtain ⟨ε, hε⟩ := exists_equiv_of_mulEquiv_alt (Fintype.card_fin n) (Fintype.card_fin n)
    (by omega) (MulEquiv.ofBijective ψ₀ hψb)
  refine ⟨ε, fun j hj hjN => ?_⟩
  have h1 := hε (e ((⟨j, hj⟩ : ↥J) : ↥J ⧸ pPrimeCore 2 ↥J))
  have h2 : ((MulEquiv.ofBijective ψ₀ hψb (e ((⟨j, hj⟩ : ↥J) : ↥J ⧸ pPrimeCore 2 ↥J)) :
      alternatingGroup (Fin n)) : Perm (Fin n)) = ρ ⟨j, hjN⟩ := by
    change ((φ (e.symm (e _)) : alternatingGroup (Fin n)) : Perm (Fin n)) = _
    rw [MulEquiv.symm_apply_apply, QuotientGroup.lift_mk]
    rfl
  rw [← h2, h1]
  ext ω
  simp [coreImage, Perm.mul_apply]

end Sig36

namespace SwapP2

abbrev Hn (E : Subgroup X) : Subgroup X := normalizer (Sol78.signalizerCompletion E E : Set X)

abbrev conjBy (M : Subgroup X) (g : X) : Subgroup X := M.map (MulAut.conj g).toMonoidHom

abbrev core (Y : Subgroup X) : Subgroup X := (pPrimeCore 2 ↥Y).map Y.subtype

abbrev fixA (M : Subgroup X) (e₀ r : X) : Subgroup X :=
  GSLit.fixedLayer (GSLit.fixedLayer M (zpowers e₀)) (zpowers r)

abbrev fixB (M : Subgroup X) (t e₀ r : X) : Subgroup X :=
  GSLit.fixedLayer (GSLit.fixedLayer (conjBy M t) (zpowers e₀)) (zpowers r)

structure Setting [Finite X] [IsSimpleGroup X] (t : X) (J : Subgroup X) (n : ℕ)
    (e : J ⧸ pPrimeCore 2 J ≃* alternatingGroup (Fin n)) (E : Subgroup X) (D : Finset (Fin n))
    (M : Subgroup X) : Prop where
  sig : Sig36 X t J n e E D
  cent : centralizer ({t} : Set X) ≤ Hn E
  le : M ≤ Hn E
  pc : IsPComponent 2 (M.subgroupOf (Hn E))
  swap : conjBy M t ≠ M
  diag : J ≤ M ⊔ conjBy M t
  alt : Nonempty (↥M ⧸ pPrimeCore 2 ↥M ≃* alternatingGroup (Fin n))
  small : ∀ P : Subgroup X, P ≤ UnbalancedLayer.coreActionKernel J → IsPGroup 2 P →
    Nat.card P ≤ 2
  narrow : ∀ R : Subgroup X, R ≠ ⊥ → IsPGroup 2 R → R ≤ Hn E →
    R ≤ UnbalancedLayer.coreActionKernel M → ¬ centralizer (R : Set X) ≤ Hn E

structure Data (t : X) (J : Subgroup X) (n : ℕ)
    (e : J ⧸ pPrimeCore 2 J ≃* alternatingGroup (Fin n)) (E : Subgroup X) (D : Finset (Fin n))
    (M : Subgroup X) (e₀ : X) (F : Subgroup X) (DF : Finset (Fin n)) (r : X) : Prop where
  e₀E : e₀ ∈ E
  e₀1 : e₀ ≠ 1
  FJ : F ≤ J
  Fk : Nonempty (F ≃* Multiplicative (ZMod 2) × Multiplicative (ZMod 2))
  DFc : DF.card = 4
  Fs : ∀ x : J, (x : X) ∈ F → ∀ ω ∉ DF,
    ((e (x : J ⧸ pPrimeCore 2 J) : alternatingGroup (Fin n)) : Perm (Fin n)) ω = ω
  disj : Disjoint D DF
  Fe₀ : F ≤ centralizer ({e₀} : Set X)
  rM : r ∈ conjBy M t
  r2 : r * r = 1
  r1 : r ≠ 1
  re₀ : r * e₀ = e₀ * r
  rF : F ≤ centralizer ({r} : Set X)
  lift : r * e₀⁻¹ ∈ UnbalancedLayer.coreActionKernel (conjBy M t)

structure PumpData (M : Subgroup X) (e₀ r : X) (N₁ : Subgroup X) : Prop where
  le : N₁ ≤ centralizer ({r} : Set X)
  pc : IsPComponent 2 (N₁.subgroupOf (centralizer ({r} : Set X)))
  cover : fixA M e₀ r ≤ N₁ ⊔ conjBy N₁ e₀
  layer : IsPComponent 2 ((fixA M e₀ r).subgroupOf
    ((N₁ ⊔ conjBy N₁ e₀) ⊓ centralizer ({e₀} : Set X)))

@[expose] def ClaimA : Prop :=
  ∀ (X : Type) [Group X] [Finite X] [IsSimpleGroup X] (t : X) (J : Subgroup X) (n : ℕ)
    (e : J ⧸ pPrimeCore 2 J ≃* alternatingGroup (Fin n)) (E : Subgroup X) (D : Finset (Fin n))
    (M : Subgroup X), Setting t J n e E D M → 13 ≤ n →
    ∀ F : Subgroup X, F ≤ J →
      Nonempty (F ≃* Multiplicative (ZMod 2) × Multiplicative (ZMod 2)) →
    ∀ DF : Finset (Fin n), DF.card = 4 → (∀ x : J, (x : X) ∈ F → ∀ ω ∉ DF,
        ((e (x : J ⧸ pPrimeCore 2 J) : alternatingGroup (Fin n)) : Perm (Fin n)) ω = ω) →
    ∀ f ∈ F, f ≠ 1 → centralizer ({f} : Set X) ≤ Hn E

@[expose] def DataExist : Prop :=
  ∀ (X : Type) [Group X] [Finite X] [IsSimpleGroup X] (t : X) (J : Subgroup X) (n : ℕ)
    (e : J ⧸ pPrimeCore 2 J ≃* alternatingGroup (Fin n)) (E : Subgroup X) (D : Finset (Fin n))
    (M : Subgroup X), Setting t J n e E D M →
    ∀ e₀ ∈ E, e₀ ≠ 1 →
    ∃ (F : Subgroup X) (DF : Finset (Fin n)) (r : X), Data t J n e E D M e₀ F DF r

@[expose] def OddCoreR : Prop :=
  ∀ (X : Type) [Group X] [Finite X] [IsSimpleGroup X] (t : X) (J : Subgroup X) (n : ℕ)
    (e : J ⧸ pPrimeCore 2 J ≃* alternatingGroup (Fin n)) (E : Subgroup X) (D : Finset (Fin n))
    (M : Subgroup X), Setting t J n e E D M →
    ∀ (e₀ : X) (F : Subgroup X) (DF : Finset (Fin n)) (r : X), Data t J n e E D M e₀ F DF r →
    (∀ f ∈ F, f ≠ 1 → centralizer ({f} : Set X) ≤ Hn E) →
    core (centralizer ({r} : Set X)) ≤ Hn E

@[expose] def Pump : Prop :=
  ∀ (X : Type) [Group X] [Finite X] [IsSimpleGroup X] (t : X) (J : Subgroup X) (n : ℕ)
    (e : J ⧸ pPrimeCore 2 J ≃* alternatingGroup (Fin n)) (E : Subgroup X) (D : Finset (Fin n))
    (M : Subgroup X), Setting t J n e E D M →
    ∀ (e₀ : X) (F : Subgroup X) (DF : Finset (Fin n)) (r : X), Data t J n e E D M e₀ F DF r →
    centralizer ({e₀} : Set X) ≤ Hn E →
    Nonempty (↥(fixA M e₀ r) ⧸ pPrimeCore 2 ↥(fixA M e₀ r) ≃* alternatingGroup (Fin (n - 4))) ∧
    FooteLit.IsTwoComponentIn (fixA M e₀ r)
      (centralizer ({r} : Set X) ⊓ centralizer ({e₀} : Set X)) ∧
    ∃ N₁ : Subgroup X, PumpData M e₀ r N₁

@[expose] def PumpSide : Prop :=
  ∀ (X : Type) [Group X] [Finite X] [IsSimpleGroup X] (t : X) (J : Subgroup X) (n : ℕ)
    (e : J ⧸ pPrimeCore 2 J ≃* alternatingGroup (Fin n)) (E : Subgroup X) (D : Finset (Fin n))
    (M : Subgroup X), Setting t J n e E D M → 13 ≤ n →
    ∀ (e₀ : X) (F : Subgroup X) (DF : Finset (Fin n)) (r : X), Data t J n e E D M e₀ F DF r →
    centralizer ({e₀} : Set X) ≤ Hn E →
    ∀ N₁ : Subgroup X, PumpData M e₀ r N₁ →
    ∀ f ∈ F, ∃ a ∈ fixA M e₀ r,
      f * a⁻¹ ∈ UnbalancedLayer.coreActionKernel (N₁ ⊔ conjBy N₁ e₀) ∧
        f * a⁻¹ ∈ UnbalancedLayer.coreActionKernel M

@[expose] def PumpLe : Prop :=
  ∀ (X : Type) [Group X] [Finite X] [IsSimpleGroup X] (t : X) (J : Subgroup X) (n : ℕ)
    (e : J ⧸ pPrimeCore 2 J ≃* alternatingGroup (Fin n)) (E : Subgroup X) (D : Finset (Fin n))
    (M : Subgroup X), Setting t J n e E D M → 13 ≤ n →
    ∀ (e₀ : X) (F : Subgroup X) (DF : Finset (Fin n)) (r : X), Data t J n e E D M e₀ F DF r →
    centralizer ({e₀} : Set X) ≤ Hn E →
    core (centralizer ({r} : Set X)) ≤ Hn E →
    ∀ N₁ : Subgroup X, PumpData M e₀ r N₁ → conjBy N₁ e₀ = N₁ →
    (∀ f ∈ F, ∃ a ∈ fixA M e₀ r, f * a⁻¹ ∈ UnbalancedLayer.coreActionKernel N₁ ∧
      f * a⁻¹ ∈ UnbalancedLayer.coreActionKernel M) →
    N₁ ≤ Hn E

@[expose] def PumpDiag : Prop :=
  ∀ (X : Type) [Group X] [Finite X] [IsSimpleGroup X] (t : X) (J : Subgroup X) (n : ℕ)
    (e : J ⧸ pPrimeCore 2 J ≃* alternatingGroup (Fin n)) (E : Subgroup X) (D : Finset (Fin n))
    (M : Subgroup X), Setting t J n e E D M → 13 ≤ n →
    ∀ (e₀ : X) (F : Subgroup X) (DF : Finset (Fin n)) (r : X), Data t J n e E D M e₀ F DF r →
    centralizer ({e₀} : Set X) ≤ Hn E →
    core (centralizer ({r} : Set X)) ≤ Hn E →
    ∀ N₁ : Subgroup X, PumpData M e₀ r N₁ →
    (∀ f ∈ F, ∃ a ∈ fixA M e₀ r,
      f * a⁻¹ ∈ UnbalancedLayer.coreActionKernel (N₁ ⊔ conjBy N₁ e₀) ∧
        f * a⁻¹ ∈ UnbalancedLayer.coreActionKernel M) →
    conjBy N₁ e₀ = N₁

@[expose] def FixedLayerComponent : Prop :=
  ∀ (X : Type) [Group X] [Finite X] [IsSimpleGroup X] (t : X) (J : Subgroup X) (n : ℕ)
    (e : J ⧸ pPrimeCore 2 J ≃* alternatingGroup (Fin n)) (E : Subgroup X) (D : Finset (Fin n))
    (M : Subgroup X), Setting t J n e E D M →
    ∀ (e₀ : X) (F : Subgroup X) (DF : Finset (Fin n)) (r : X), Data t J n e E D M e₀ F DF r →
    centralizer ({e₀} : Set X) ≤ Hn E →
    ∀ N₁ : Subgroup X, PumpData M e₀ r N₁ → conjBy N₁ e₀ = N₁ → N₁ ≤ Hn E →
    FooteLit.IsTwoComponentIn (GSLit.fixedLayer M (zpowers r)) (centralizer ({r} : Set X))

@[expose] def MemberOfFixedLayer : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (M T : Subgroup X), ⁅M, M⁆ = M →
    IsQuasisimple (↥M ⧸ pPrimeCore 2 ↥M) → T ≠ ⊥ → IsPGroup 2 T →
    T ≤ UnbalancedLayer.coreActionKernel M →
    FooteLit.IsTwoComponentIn (GSLit.fixedLayer M T) (centralizer (T : Set X)) →
    FooteLit.IsSolomonMember M

@[expose] def Assembly : Prop :=
  ClaimA → DataExist → OddCoreR → Pump → PumpSide → PumpLe → PumpDiag → FixedLayerComponent →
    MemberOfFixedLayer →
    ∀ (X : Type) [Group X] [Finite X] [IsSimpleGroup X] (t : X) (J : Subgroup X) (n : ℕ)
      (e : J ⧸ pPrimeCore 2 J ≃* alternatingGroup (Fin n)) (E : Subgroup X)
      (D : Finset (Fin n)) (M : Subgroup X), Setting t J n e E D M → 13 ≤ n →
      FooteLit.IsSolomonMember M

theorem memberOfFixedLayer_holds : MemberOfFixedLayer :=
  fun _ _ _ _ _ hperf hMq hT hT2 hTM hMT => isSolomonMember_of_fixedLayer hperf hMq hT hT2 hTM hMT

theorem oddCoreR_holds : OddCoreR := by
  intro X _ _ _ t J n e E D M _ e₀ F DF r hd hFH
  exact oddCore_le_of_four_centralizer_le hd.Fk hd.rF hFH

theorem fixedLayerComponent_holds : FixedLayerComponent := by
  intro X _ _ _ t J n e E D M hs e₀ F DF r hd _ N₁ hP hfix hN₁H
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have htH : t ∈ Hn E := hs.cent (mem_centralizer_singleton_iff.mpr rfl)
  obtain ⟨hMtH, hMtpc⟩ := isPComponent_conj hs.le hs.pc htH
  have hMtK : conjBy M t ≤ UnbalancedLayer.coreActionKernel M :=
    GSThmB.B5a.le_coreActionKernel_of_ne hs.le hMtH hs.pc hMtpc (Ne.symm hs.swap)
  have hrK : r ∈ UnbalancedLayer.coreActionKernel M := hMtK hd.rM
  have hrH : r ∈ Hn E := hMtH hd.rM
  have hr2 : orderOf r = 2 := orderOf_eq_prime (by rw [sq]; exact hd.r2) hd.r1
  have hR2 : IsPGroup 2 (zpowers r) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hr2, pow_one])
  have hMq : IsQuasisimple (↥M ⧸ pPrimeCore 2 ↥M) :=
    ((CatalogueBPrimeJoin.pComponent_subgroupOf_iff 2 M (Hn E) hs.le).mp hs.pc).2.2
  have hMsub : (M.subgroupOf (Hn E)).IsSubnormal := hs.pc.choose_spec.2.1
  have hCr : centralizer ((zpowers r : Subgroup X) : Set X) = centralizer ({r} : Set X) :=
    centralizer_zpowers_eq' r
  have hMrpc := GSLit.fixedLayer_isPComponent hs.le hMsub (zpowers_le.mpr hrH)
    (zpowers_le.mpr hrK) hR2 hMq
  rw [hCr] at hMrpc
  have hMrle := GSLit.fixedLayer_le_inf M (zpowers r)
  rw [hCr] at hMrle
  have hMrY : GSLit.fixedLayer M (zpowers r) ≤ Hn E ⊓ centralizer ({r} : Set X) :=
    le_inf ((hMrle.trans inf_le_left).trans hs.le) (hMrle.trans inf_le_right)
  have hN₁Y : N₁ ≤ Hn E ⊓ centralizer ({r} : Set X) := le_inf hN₁H hP.le
  have hN₁pc : IsPComponent 2 (N₁.subgroupOf (Hn E ⊓ centralizer ({r} : Set X))) :=
    CatalogueBPrimeJoin.pComponent_subgroupOf_of_le hN₁Y inf_le_right hP.pc
  have hArN : fixA M e₀ r ≤ N₁ := by
    have h1 := hP.cover
    rwa [hfix, sup_idem] at h1
  have hAle := GSLit.fixedLayer_le_inf M (zpowers e₀)
  have hArle := GSLit.fixedLayer_le_inf (GSLit.fixedLayer M (zpowers e₀)) (zpowers r)
  have hArY : fixA M e₀ r ≤ (N₁ ⊔ conjBy N₁ e₀) ⊓ centralizer ({e₀} : Set X) := by
    refine le_inf (hArN.trans le_sup_left) ?_
    have h1 := (hArle.trans inf_le_left).trans (hAle.trans inf_le_right)
    rwa [centralizer_zpowers_eq'] at h1
  obtain ⟨-, hArres, hArq⟩ :=
    (CatalogueBPrimeJoin.pComponent_subgroupOf_iff 2 _ _ hArY).mp hP.layer
  have hArMC : fixA M e₀ r ≤ M ⊓ centralizer ((zpowers r : Subgroup X) : Set X) :=
    le_inf ((hArle.trans inf_le_left).trans (hAle.trans inf_le_left)) (hArle.trans inf_le_right)
  have hArMr : fixA M e₀ r ≤ GSLit.fixedLayer M (zpowers r) :=
    le_fixedLayer_of_primeResidual hMq (zpowers_le.mpr hrK) hR2 hArMC hArres
  have hArperf : ⁅fixA M e₀ r, fixA M e₀ r⁆ = fixA M e₀ r :=
    UnbalancedCorr.commutator_eq_of_isPComponent hArY hP.layer
  have hArnt : Nontrivial (↥(fixA M e₀ r) ⧸ pPrimeCore 2 ↥(fixA M e₀ r)) :=
    LocalCores.isQuasisimple_nontrivial hArq
  have heq : N₁ = GSLit.fixedLayer M (zpowers r) :=
    eq_of_isPComponent_of_le_inf hN₁Y hMrY hN₁pc hMrpc hArN hArMr hArperf hArnt
  rw [← heq]
  exact ⟨hP.le, hP.pc⟩

theorem assembly_holds : Assembly := by
  intro hA hDE hOC hP hPS hPL hPD hFL hMF X _ _ _ t J n e E D M hs hn
  classical
  obtain ⟨e₀, -, -, he₀E, -, -, he₀1, -, -, -, -, -⟩ := exists_three_of_klein hs.sig.klein
  obtain ⟨F, DF, r, hd⟩ := hDE X t J n e E D M hs e₀ he₀E he₀1
  have hFH := hA X t J n e E D M hs hn F hd.FJ hd.Fk DF hd.DFc hd.Fs
  have he₀H : centralizer ({e₀} : Set X) ≤ Hn E :=
    hA X t J n e E D M hs hn E hs.sig.le hs.sig.klein D hs.sig.card hs.sig.supp e₀ he₀E he₀1
  have hOr := hOC X t J n e E D M hs e₀ F DF r hd hFH
  obtain ⟨-, -, N₁, hN₁⟩ := hP X t J n e E D M hs e₀ F DF r hd he₀H
  have hside := hPS X t J n e E D M hs hn e₀ F DF r hd he₀H N₁ hN₁
  have hfix := hPD X t J n e E D M hs hn e₀ F DF r hd he₀H hOr N₁ hN₁ hside
  have hside' : ∀ f ∈ F, ∃ a ∈ fixA M e₀ r, f * a⁻¹ ∈ UnbalancedLayer.coreActionKernel N₁ ∧
      f * a⁻¹ ∈ UnbalancedLayer.coreActionKernel M := by
    intro f hf
    obtain ⟨a, ha, h1, h2⟩ := hside f hf
    refine ⟨a, ha, ?_, h2⟩
    rwa [hfix, sup_idem] at h1
  have hN₁H := hPL X t J n e E D M hs hn e₀ F DF r hd he₀H hOr N₁ hN₁ hfix hside'
  have hMr := hFL X t J n e E D M hs e₀ F DF r hd he₀H N₁ hN₁ hfix hN₁H
  have htH : t ∈ Hn E := hs.cent (mem_centralizer_singleton_iff.mpr rfl)
  obtain ⟨hMtH, hMtpc⟩ := isPComponent_conj hs.le hs.pc htH
  have hMtK : conjBy M t ≤ UnbalancedLayer.coreActionKernel M :=
    GSThmB.B5a.le_coreActionKernel_of_ne hs.le hMtH hs.pc hMtpc (Ne.symm hs.swap)
  have hr2 : orderOf r = 2 := orderOf_eq_prime (by rw [sq]; exact hd.r2) hd.r1
  have hR2 : IsPGroup 2 (zpowers r) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hr2, pow_one])
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨-, -, hMq⟩ :=
    (CatalogueBPrimeJoin.pComponent_subgroupOf_iff 2 M (Hn E) hs.le).mp hs.pc
  have hperf : ⁅M, M⁆ = M := UnbalancedCorr.commutator_eq_of_isPComponent hs.le hs.pc
  refine hMF X M (zpowers r) hperf hMq (fun h => hd.r1 (zpowers_eq_bot.mp h)) hR2
    (zpowers_le.mpr (hMtK hd.rM)) ?_
  rwa [centralizer_zpowers_eq' r]

@[expose] def SwapMemberResidue : Prop :=
  ∀ (X : Type) [Group X] [Finite X] [IsSimpleGroup X] (t : X) (J : Subgroup X) (n : ℕ)
    (e : J ⧸ pPrimeCore 2 J ≃* alternatingGroup (Fin n)) (E : Subgroup X) (D : Finset (Fin n)),
    Sig36 X t J n e E D → n = 9 ∨ n = 11 →
    centralizer ({t} : Set X) ≤ normalizer (Sol78.signalizerCompletion E E : Set X) →
    ∀ M : Subgroup X, M ≤ normalizer (Sol78.signalizerCompletion E E : Set X) →
      IsPComponent 2 (M.subgroupOf (normalizer (Sol78.signalizerCompletion E E : Set X))) →
      M.map (MulAut.conj t).toMonoidHom ≠ M → J ≤ M ⊔ M.map (MulAut.conj t).toMonoidHom →
      Nonempty (↥M ⧸ pPrimeCore 2 ↥M ≃* alternatingGroup (Fin n)) →
      (∀ P : Subgroup X, P ≤ UnbalancedLayer.coreActionKernel J → IsPGroup 2 P →
        Nat.card P ≤ 2) →
      (∀ R : Subgroup X, R ≠ ⊥ → IsPGroup 2 R →
        R ≤ normalizer (Sol78.signalizerCompletion E E : Set X) →
        R ≤ UnbalancedLayer.coreActionKernel M →
        ¬ centralizer (R : Set X) ≤ normalizer (Sol78.signalizerCompletion E E : Set X)) →
      FooteLit.IsSolomonMember M

theorem signalizerSwapMemberNarrowInput_of_steps (hA : ClaimA) (hDE : DataExist) (hP : Pump)
    (hPS : PumpSide) (hPL : PumpLe) (hPD : PumpDiag) (hres : SwapMemberResidue) :
    SignalizerSwapMemberNarrowInput := by
  intro X _ _ _ t J n e E D S hCH M hMH hMpc hne hJM hMalt hsmall hnarrow
  by_cases hn : 13 ≤ n
  · exact assembly_holds hA hDE oddCoreR_holds hP hPS hPL hPD fixedLayerComponent_holds
      memberOfFixedLayer_holds X t J n e E D M
      ⟨S, hCH, hMH, hMpc, hne, hJM, hMalt, hsmall, hnarrow⟩ hn
  · have h9 := S.nine_le
    obtain ⟨k, hk⟩ := S.pair.2.1
    exact hres X t J n e E D S (by omega) hCH M hMH hMpc hne hJM hMalt hsmall hnarrow

end SwapP2

end CFSG.ComponentClassification.SolMax
