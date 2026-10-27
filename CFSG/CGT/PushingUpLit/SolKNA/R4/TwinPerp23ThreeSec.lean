module

public import CFSG.CGT.PushingUpLit.SolKNA.R4.TwinPerp25SixFam
public import CFSG.CGT.PushingUpLit.SolKNA.R4.TwinPerp23ThreeSylow
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThmEWPf18OddW
public import CFSG.ClassicalInvolution.Asc77.AscAETSecViol

public section

set_option linter.unusedSectionVars false

namespace CFSG.CGT.PushingUpLit.SolKNA.R4

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.Q3NL
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinExitPf2 CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDisc
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinADescent (coreAt)
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.Thm4Twin
open CFSG.ClassicalInvolution.Balance

namespace Perp23

namespace Three

section Sec

variable {Y : Type} [Group Y] [Finite Y]

theorem card_quat {r : ℕ} (hr : 2 ≤ r) : Nat.card (QuaternionGroup (2 ^ (r - 2))) = 2 ^ r := by
  rw [Nat.card_eq_fintype_card, QuaternionGroup.card]
  obtain ⟨k, rfl⟩ : ∃ k, r = k + 2 := ⟨r - 2, by omega⟩
  rw [Nat.add_sub_cancel, pow_add]
  ring

theorem mem_USet_restrict_of_le_free {Ω : Set (Subgroup Y)} (hΩ : HypOmegaGen Ω) {Y' L U : Subgroup Y}
    (hU : U ∈ USet Ω) (hL : L ∈ Ω) (hLY : L ≤ Y') (hUL : U ≤ L) :
    U.subgroupOf Y' ∈ USet (restrictFamily Ω Y') := by
  obtain ⟨-, -, -, -, -, -, -, -, h4⟩ := Sec6Gen.exists_data_of_mem_USet hΩ hU
  obtain ⟨R, hR, hUR, hcyc, hidx⟩ := hU
  obtain ⟨J, hJ, hRJ⟩ := exists_isSylow2In_of_mem_RSet hR
  have hJL : L = J := Sec6Gen.eq_of_le_of_le hΩ hL hJ (hRJ.2.1.to_le hUR) h4 hUL (hUR.trans hRJ.1)
  subst hJL
  exact AscAET.mem_USet_restrict_of_sylow hL hLY hRJ hUR hcyc hidx

theorem centBarMk_mul {a x y : Y} (hx : x ∈ Subgroup.centralizer ({a} : Set Y))
    (hy : y ∈ Subgroup.centralizer ({a} : Set Y)) :
    centBarMk a hx * centBarMk a hy =
      centBarMk a ((Subgroup.centralizer ({a} : Set Y)).mul_mem hx hy) := by
  simp only [centBarMk]
  rw [← map_mul]
  rfl

theorem centBarMk_inv {a x : Y} (hx : x ∈ Subgroup.centralizer ({a} : Set Y)) :
    (centBarMk a hx)⁻¹ = centBarMk a ((Subgroup.centralizer ({a} : Set Y)).inv_mem hx) := by
  simp only [centBarMk]
  rw [← map_inv]
  rfl

theorem centBarMk_one {a : Y} :
    centBarMk a ((Subgroup.centralizer ({a} : Set Y)).one_mem) = 1 := by
  simp only [centBarMk]
  rw [← map_one (QuotientGroup.mk' (classicalInvolutionOddCore (CentTop a)))]
  rfl

theorem centBarMk_congr {a x y : Y} (hx : x ∈ Subgroup.centralizer ({a} : Set Y))
    (hy : y ∈ Subgroup.centralizer ({a} : Set Y)) (h : x = y) : centBarMk a hx = centBarMk a hy := by
  subst h
  rfl

theorem centBarMk_pow {a x : Y} (hx : x ∈ Subgroup.centralizer ({a} : Set Y)) (n : ℕ) :
    (centBarMk a hx) ^ n = centBarMk a ((Subgroup.centralizer ({a} : Set Y)).pow_mem hx n) := by
  induction n with
  | zero =>
    rw [pow_zero]
    exact (centBarMk_one (a := a)).symm.trans (centBarMk_congr _ _ (pow_zero x).symm)
  | succ k ih =>
    rw [pow_succ, ih, centBarMk_mul]
    exact centBarMk_congr _ _ (pow_succ x k).symm

theorem centBarMk_eq_one_iff {a x : Y} (hx : x ∈ Subgroup.centralizer ({a} : Set Y)) :
    centBarMk a hx = 1 ↔ x ∈ oddCoreIn (Subgroup.centralizer ({a} : Set Y)) := by
  set C := Subgroup.centralizer ({a} : Set Y) with hC
  constructor
  · intro h
    have h1 : topMk (⟨x, hx⟩ : ↥C) ∈ classicalInvolutionOddCore (CentTop a) :=
      (QuotientGroup.eq_one_iff _).mp h
    have h2 := mem_oddCore_of_top h1
    exact ⟨⟨x, hx⟩, h2, rfl⟩
  · rintro ⟨y, hy, hyx⟩
    have hy' : y = ⟨x, hx⟩ := Subtype.ext hyx
    have hy2 : (⟨x, hx⟩ : ↥C) ∈ classicalInvolutionOddCore ↥C := by rw [← hy']; exact hy
    have hmap : Subgroup.map (Subgroup.topEquiv : ↥(⊤ : Subgroup ↥C) ≃* ↥C).toMonoidHom
        (classicalInvolutionOddCore ↥(⊤ : Subgroup ↥C)) = classicalInvolutionOddCore ↥C :=
      CFSG.ComponentClassification.OddCore.equiv_invariant _
    rw [← hmap] at hy2
    obtain ⟨n, hn, hnx⟩ := hy2
    have hn' : n = topMk ⟨x, hx⟩ := Subtype.ext hnx
    rw [hn'] at hn
    exact (QuotientGroup.eq_one_iff _).mpr hn

@[expose] def Utilde (a : Y) (Q : Subgroup (CentBar a)) : Subgroup Y where
  carrier := {y | ∃ hy : y ∈ Subgroup.centralizer ({a} : Set Y), centBarMk a hy ∈ Q}
  mul_mem' := by
    rintro x y ⟨hx, hxQ⟩ ⟨hy, hyQ⟩
    exact ⟨(Subgroup.centralizer ({a} : Set Y)).mul_mem hx hy, by
      rw [← centBarMk_mul hx hy]; exact Q.mul_mem hxQ hyQ⟩
  one_mem' := ⟨Subgroup.one_mem _, by rw [centBarMk_one]; exact Q.one_mem⟩
  inv_mem' := by
    rintro x ⟨hx, hxQ⟩
    exact ⟨(Subgroup.centralizer ({a} : Set Y)).inv_mem hx, by
      rw [← centBarMk_inv hx]; exact Q.inv_mem hxQ⟩

theorem Utilde_le {a : Y} (Q : Subgroup (CentBar a)) :
    Utilde a Q ≤ Subgroup.centralizer ({a} : Set Y) := fun _ hy => hy.1

theorem Utilde_conj {a : Y} {Q : Subgroup (CentBar a)} (hQ : Q.Normal) {c y : Y}
    (hc : c ∈ Subgroup.centralizer ({a} : Set Y)) (hy : y ∈ Utilde a Q) :
    c * y * c⁻¹ ∈ Utilde a Q := by
  obtain ⟨hyC, hyQ⟩ := hy
  set C := Subgroup.centralizer ({a} : Set Y) with hCdef
  have hcyc : c * y * c⁻¹ ∈ C := C.mul_mem (C.mul_mem hc hyC) (C.inv_mem hc)
  refine ⟨hcyc, ?_⟩
  have e : centBarMk a hcyc =
      centBarMk a hc * centBarMk a hyC * (centBarMk a hc)⁻¹ := by
    rw [centBarMk_inv hc, centBarMk_mul, centBarMk_mul]
  rw [e]
  exact hQ.conj_mem _ hyQ _

theorem oddCoreIn_le_Utilde {a : Y} (Q : Subgroup (CentBar a)) :
    oddCoreIn (Subgroup.centralizer ({a} : Set Y)) ≤ Utilde a Q := by
  intro x hx
  have hxC : x ∈ Subgroup.centralizer ({a} : Set Y) := oddCoreIn_le _ hx
  exact ⟨hxC, by rw [(centBarMk_eq_one_iff hxC).mpr hx]; exact Q.one_mem⟩

theorem exists_pow_mem_oddCoreIn_of_mem_Utilde {a : Y} {Q : Subgroup (CentBar a)} (hQ2 : IsPGroup 2 ↥Q)
    {y : Y} (hy : y ∈ Utilde a Q) :
    ∃ k : ℕ, y ^ (2 ^ k) ∈ oddCoreIn (Subgroup.centralizer ({a} : Set Y)) := by
  obtain ⟨hyC, hyQ⟩ := hy
  obtain ⟨k, hk⟩ := hQ2 ⟨centBarMk a hyC, hyQ⟩
  refine ⟨k, ?_⟩
  have h1 : (centBarMk a hyC) ^ (2 ^ k) = 1 := congrArg Subtype.val hk
  rw [centBarMk_pow] at h1
  exact (centBarMk_eq_one_iff _).mp h1

theorem exists_two_group_lift {a : Y} {Q : Subgroup (CentBar a)} (hQn : Q.Normal) (hQ2 : IsPGroup 2 ↥Q)
    {W : Subgroup Y} (hW2 : IsPGroup 2 W) (hWC : W ≤ Subgroup.centralizer ({a} : Set Y)) :
    ∃ T : Subgroup Y, W ≤ T ∧ IsPGroup 2 T ∧
      ∀ V : Subgroup Y, ∀ hV : V ≤ Subgroup.centralizer ({a} : Set Y), IsPGroup 2 V →
        (∀ (y : Y) (hy : y ∈ V), centBarMk a (hV hy) ∈ Q) →
        ∃ o ∈ oddCoreIn (Subgroup.centralizer ({a} : Set Y)), conjSub o V ≤ T := by
  obtain ⟨T, hWT, hT2, hT⟩ := exists_two_group_conj_of_odd_kernel (W := W) (U := Utilde a Q)
    (O := oddCoreIn (Subgroup.centralizer ({a} : Set Y))) hW2
    (fun w hw x hx => Utilde_conj hQn (hWC hw) hx)
    (oddCoreIn_le_Utilde Q)
    (fun x hx o ho => conj_mem_oddCoreIn (Utilde_le Q hx) ho)
    (odd_card_oddCoreIn _)
    (fun x hx => exists_pow_mem_oddCoreIn_of_mem_Utilde hQ2 hx)
  refine ⟨T, hWT, hT2, fun V hV hV2 hVQ => ?_⟩
  exact hT V (fun y hy => ⟨hV hy, hVQ y hy⟩) hV2

theorem exists_normal_two_group_U {r : ℕ} (hr : 4 ≤ r) {Ω : Set (Subgroup Y)} {a : Y}
    (hΩ : HypOmegaGen Ω) (hc2 : IsPGroup 2 (Subgroup.zpowers a))
    (h2 : ∀ M ∈ Ω, IsPGroup 2 (↥M ⧸ classicalInvolutionOddCore ↥M))
    (hq : ∀ M ∈ Ω, ∀ P : Subgroup Y, IsSylow2In P M →
      Nonempty (↥P ≃* QuaternionGroup (2 ^ (r - 2))))
    (hA : ∀ M ∈ Ω, AEmpty Ω M) {K : Subgroup Y} (hK : K ∈ tqMembers3 Ω a) {z : Y}
    (hz : IsUniqueInvolution K z) (hzC : z ∈ Subgroup.centralizer ({a} : Set Y))
    (hin : TightInO2 (centBarMk a hzC)) {P U : Subgroup Y} (hP : IsSylow2In P K)
    (hPa : P ≤ Subgroup.centralizer ({a} : Set Y)) (hUP : U ≤ P) (hUc : IsCyclic ↥U)
    (hUi : U.relIndex P = 2) :
    ∃ Q : Subgroup (CentBar a), Q.Normal ∧ IsPGroup 2 ↥Q ∧
      ∀ (y : Y) (hy : y ∈ U), centBarMk a (hPa (hUP hy)) ∈ Q := by
  classical
  set C := Subgroup.centralizer ({a} : Set Y) with hCdef
  set Δ : Set (Subgroup (CentBar a)) := famX Ω a (⊤ : Subgroup ↥C) with hΔ
  have hT4 : TwinT4Hyp r (CentBar a) Δ := twinT4Hyp_famX hΩ hc2 h2 hq hA ⊤
  set Δ₀ : Set (Subgroup (CentBar a)) :=
    {J | J ∈ Δ ∧ ∀ u : CentBar a, IsUniqueInvolution J u → TightInO2 u} with hΔ₀
  have hsub : Δ₀ ⊆ Δ := fun J hJ => hJ.1
  have hinv : ConjInvariant Δ₀ := by
    rintro g J ⟨hJΔ, hJE⟩
    refine ⟨hT4.hyp.conjInvariant g J hJΔ, fun u hu => ?_⟩
    have hu' : IsUniqueInvolution J (g⁻¹ * u * g⁻¹⁻¹) := by
      have := hu.conj g⁻¹
      rwa [conjSub_inv_conjSub] at this
    obtain ⟨Q, hQn, hQ2, huQ⟩ := hJE _ hu'
    refine ⟨Q, hQn, hQ2, ?_⟩
    have h1 := hQn.conj_mem _ huQ g
    have e : g * (g⁻¹ * u * g⁻¹⁻¹) * g⁻¹ = u := by group
    rwa [e] at h1
  have hT0 : TwinT4Hyp r (CentBar a) Δ₀ := hT4.sub hsub hinv
  have hĴΔ : imgX a (⊤ : Subgroup ↥C) K ∈ Δ := imgX_mem_famX hK le_top
  have hzcore : z ∈ coreAt a K :=
    TwinLayer.mem_exactCore_of_uniqueInvolution hΩ hc2 hK.1 hK.2 hz
  have hĴu : IsUniqueInvolution (imgX a (⊤ : Subgroup ↥C) K) (centBarMk a hzC) :=
    isUniqueInvolution_imgX hΩ hc2 hK hzcore hzC hz.sq hz.ne_one
  have hĴ₀ : imgX a (⊤ : Subgroup ↥C) K ∈ Δ₀ :=
    ⟨hĴΔ, fun u hu => (hĴu.eq hu) ▸ hin⟩
  set N : Subgroup (CentTop a) := classicalInvolutionOddCore (CentTop a) with hN
  set Û : Subgroup (CentBar a) :=
    ((U.subgroupOf C).subgroupOf (⊤ : Subgroup ↥C)).map (QuotientGroup.mk' N) with hÛdef
  have hcoreΦ : coreAt a K ∈ TwinADescent.coreFamily Ω a := TwinADescent.coreAt_mem_coreFamily hK
  have hPcore : IsSylow2In P (coreAt a K) :=
    (TwinADescent.isSylow2In_coreAt_iff hc2 hK.2).mpr ⟨hP, hPa⟩
  have hUcore : U ≤ coreAt a K := hUP.trans hPcore.1
  have hU1 : U.subgroupOf C ∈ USet (restrictFamily (TwinADescent.coreFamily Ω a) C) :=
    AscAET.mem_USet_restrict_of_sylow hcoreΦ (TwinADescent.coreAt_le_centralizer a K) hPcore hUP
      hUc hUi
  have hΩc : HypOmegaGen (cFam Ω a) := TwinADescent.hypOmegaGen_coreFamily hΩ hc2
  have hLmem : (coreAt a K).subgroupOf C ∈ cFam Ω a :=
    subgroupOf_mem_restrictFamily hcoreΦ (TwinADescent.coreAt_le_centralizer a K)
  have hU2 : (U.subgroupOf C).subgroupOf (⊤ : Subgroup ↥C) ∈ USet (restrictFamily (cFam Ω a) ⊤) :=
    mem_USet_restrict_of_le_free hΩc hU1 hLmem le_top (Subgroup.subgroupOf_mono _ hUcore)
  have hÛΔ : Û ∈ USet Δ :=
    TwinThmEW.map_mem_USet (CFSG.ComponentClassification.OddCore.odd_card (CentTop a)) hU2
  have hÛĴ : Û ≤ imgX a (⊤ : Subgroup ↥C) K :=
    Subgroup.map_mono (Subgroup.subgroupOf_mono _ (Subgroup.subgroupOf_mono _ hUcore))
  have hÛ₀ : Û ∈ USet Δ₀ := by
    obtain ⟨R, hR, hÛR, hcyc, hidx⟩ := hÛΔ
    obtain ⟨J', hJ'Δ, hRJ'⟩ := exists_isSylow2In_of_mem_RSet hR
    have hÛ2 : IsPGroup 2 ↥Û := Sec6Gen.isPGroup_of_mem_USet hT4.hyp ⟨R, hR, hÛR, hcyc, hidx⟩
    obtain ⟨-, -, -, -, -, -, -, -, h4⟩ :=
      Sec6Gen.exists_data_of_mem_USet hT4.hyp ⟨R, hR, hÛR, hcyc, hidx⟩
    have hJ'Ĵ : J' = imgX a (⊤ : Subgroup ↥C) K :=
      Sec6Gen.eq_of_le_of_le hT4.hyp hJ'Δ hĴΔ hÛ2 h4 (hÛR.trans hRJ'.1) hÛĴ
    exact ⟨R, mem_RSet_of_isSylow2In hĴ₀ (hJ'Ĵ ▸ hRJ'), hÛR, hcyc, hidx⟩
  have h2' : ∀ J ∈ Δ₀, IsPGroup 2 ↥J := by
    intro J hJ
    obtain ⟨u, hu⟩ := Sec6Gen.exists_uniqueInvolution hT0.hyp hJ
    exact hT4.isPGroup_of_inO2 hJ.1 hu (hJ.2 u hu)
  have h8' : ∀ J ∈ Δ₀, Nat.card ↥J = 2 ^ r := by
    intro J hJ
    obtain ⟨e⟩ := hT4.quat J hJ.1 J ⟨le_rfl, h2' J hJ, fun V' hV'J _ hJV' => le_antisymm hV'J hJV'⟩
    rw [Nat.card_congr e.toEquiv]
    exact card_quat (by omega)
  have hnorm : ∀ U₁ ∈ USet Δ₀, ∀ U₂ ∈ USet Δ₀, U₂ ≤ Subgroup.normalizer (U₁ : Set (CentBar a)) :=
    fun U₁ h₁ U₂ h₂ => le_normalizer_of_four_le hr hT0.hyp h2' h8' hT0.aEmpty hT0.odd
      (fun L hL u hu => hL.2 u hu) h₁ h₂
  refine ⟨⨆ V ∈ USet Δ₀, V, normal_iSup_uSet hT0.hyp, isPGroup_iSup_uSet hT0.hyp hnorm,
    fun y hy => ?_⟩
  have hmem : centBarMk a (hPa (hUP hy)) ∈ Û :=
    Subgroup.mem_map.mpr ⟨topMk ⟨y, hPa (hUP hy)⟩,
      Subgroup.mem_subgroupOf.mpr (Subgroup.mem_subgroupOf.mpr hy), rfl⟩
  exact (le_iSup₂ (f := fun V (_ : V ∈ USet Δ₀) => V) Û hÛ₀) hmem

end Sec

end Three

end Perp23

end CFSG.CGT.PushingUpLit.SolKNA.R4
