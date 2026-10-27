module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameAEmptyPf44Close
public import CFSG.ClassicalInvolution.Q3.Q3T6DSetupA

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameAEmptyPf

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Asc77.T3
  CFSG.ClassicalInvolution.Asc77.T3Typed CFSG.ClassicalInvolution.Asc77.T3Core
  CFSG.ClassicalInvolution.Disconnected.AschTight
  CFSG.ClassicalInvolution.Q3
open scoped commutatorElement

section Gen

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}

theorem exists_aViol_conj_centralizes (hΩ : HypOmegaGen Ω) {L J Q V : Subgroup G} {zL zJ : G}
    (hL : L ∈ Ω) (hv : AViol Ω L J zL zJ) (hQ : Q ∈ Ω) (hQL : Q ∉ twinSet Ω L)
    (hV : IsSylow2In V Q) (hVL : V ≤ Subgroup.normalizer (L : Set G)) :
    ∃ Lstar ∈ twinSet Ω L, ∃ o ∈ oddCoreOf (L ⊔ Lstar),
      AViol Ω L (conjSub o J) zL (o * zJ * o⁻¹) ∧
        V ≤ Subgroup.centralizer ({o * zJ * o⁻¹} : Set G) := by
  obtain ⟨v, Ls, hVU, hVJ, -, hLsL, htw, hvv⟩ :=
    Q3T6D.exists_hexagon_data3 hΩ hL hv.mem hv.hzK hv.hzJ hv.star hv.not_nbr hv.no_conj
  have hLsT : Ls ∈ twinSet Ω L := by
    rw [htw]
    exact Or.inr rfl
  have hLsΩ : Ls ∈ Ω := hLsT.1
  have hzLs : IsUniqueInvolution Ls zL := by
    obtain ⟨-, w, hwL, hwLs⟩ := hLsT
    rwa [hwL.eq hv.hzK] at hwLs
  have hzJ : zJ ∈ L ⊔ Ls := Q3T6D.mem_sup_of_hexagon3 hΩ hv.hzJ hVU hVJ hvv
  obtain ⟨zQ, hzQ⟩ := Sec6Gen.exists_uniqueInvolution hΩ hQ
  have hQL' : Q ≠ L := by
    rintro rfl
    exact hQL ⟨hL, zL, hv.hzK, hv.hzK⟩
  have hQLs : Q ≠ Ls := fun h => hQL (h ▸ hLsT)
  have h8 : 8 ≤ Nat.card V := Sec6Gen.eight_le_of_mem_RSet hΩ (mem_RSet_of_isSylow2In hQ hV)
  have hVC : V ≤ Subgroup.centralizer ({zL} : Set G) := fun x hx =>
    T3CII.mem_centralizer_singleton_of_conj_eq
      (hv.hzK.conj_eq (mem_normalizer_iff_conjSub_eq.mp (hVL hx)))
  have hVLs : V ≤ Subgroup.normalizer (Ls : Set G) :=
    Sec6Gen.le_normalizer_of_le_centralizer hΩ hLsΩ hQ (Ne.symm hQLs) hzLs hV.1 hV.2.1
      (by omega) hVC
  have hcL : ∀ x ∈ V, ∀ m ∈ L, ⁅x, m⁆ ∈ oddCoreOf L := fun x hx m hm =>
    Q3CL.Thompson.comm_le_oddCore_of_isSylow2In Sec6Gen.l6_2Gen hΩ hL hQ (Ne.symm hQL')
      hv.hzK hzQ hV hVC (Subgroup.commutator_mem_commutator hx hm)
  have hcLs : ∀ x ∈ V, ∀ m ∈ Ls, ⁅x, m⁆ ∈ oddCoreOf Ls := fun x hx m hm =>
    Q3CL.Thompson.comm_le_oddCore_of_isSylow2In Sec6Gen.l6_2Gen hΩ hLsΩ hQ (Ne.symm hQLs)
      hzLs hzQ hV hVC (Subgroup.commutator_mem_commutator hx hm)
  have hLsN : Ls ≤ Subgroup.normalizer (L : Set G) :=
    Sec6Gen.le_normalizer_of_twin hΩ hLsΩ hL hLsL hzLs hv.hzK
  have hLN : L ≤ Subgroup.normalizer (Ls : Set G) :=
    Sec6Gen.le_normalizer_of_twin hΩ hL hLsΩ (Ne.symm hLsL) hv.hzK hzLs
  have hcN := T3CII.commutator_mem_oddCore_sup hLsN hLN hcL hcLs
  have hVN : V ≤ Subgroup.normalizer (oddCoreOf (L ⊔ Ls) : Set G) := fun x hx =>
    mem_normalizer_of_conjSub_eq (Asc77.T7V.conjSub_oddCoreOf_eq_of_mem_normalizer
      (T3CII.mem_normalizer_sup (hVL hx) (hVLs hx)))
  have hzJi : zJ⁻¹ ∈ Subgroup.normalizer (oddCoreOf (L ⊔ Ls) : Set G) :=
    mem_normalizer_of_conjSub_eq (Asc77.T7V.conjSub_oddCoreOf_eq_of_mem_normalizer
      (Subgroup.le_normalizer ((L ⊔ Ls).inv_mem hzJ)))
  have hcoset : ∀ x ∈ V, zJ⁻¹ * (x * zJ * x⁻¹) ∈ oddCoreOf (L ⊔ Ls) := by
    intro x hx
    have h1 := (Subgroup.mem_normalizer_iff.mp hzJi ⁅x, zJ⁆).mp (hcN x hx zJ hzJ)
    have e : zJ⁻¹ * (x * zJ * x⁻¹) = zJ⁻¹ * ⁅x, zJ⁆ * zJ⁻¹⁻¹ := by
      simp only [commutatorElement_def]
      group
    rw [e]
    exact h1
  obtain ⟨o, ho, hVo⟩ := Thm3Quot.exists_centralizes_involution_coset
    (oddCoreOf_odd_natCard _) hV.2.1 hVN hv.hzJ.sq hcoset
  have hoL : conjSub o L = L := mem_normalizer_iff_conjSub_eq.mp
    ((sup_le Subgroup.le_normalizer hLsN) (oddCoreOf_le_self _ ho))
  have hzo : o * zL * o⁻¹ = zL := hv.hzK.conj_eq hoL
  have hv' : AViol Ω L (conjSub o J) zL (o * zJ * o⁻¹) := by
    have h := hv.conj hΩ.conjInvariant o
    rwa [hoL, hzo] at h
  exact ⟨Ls, hLsT, o, ho, hv', hVo⟩

end Gen

section Frame

variable {T : Type} [Group T] [Finite T] {K : Subgroup T} {z : T} {J : Subgroup T} {zJ : T}

theorem le_conjStab_aStar_of_odd_four (hs : FrameStd K z J zJ) {L J' D : Subgroup T} {zL zJ' : T}
    (hL : L ∈ CoreAssembly.conjClass K) (hv : AViol (CoreAssembly.conjClass K) L J' zL zJ')
    (hD : Odd (Nat.card D)) (hzL : zL ∈ Subgroup.normalizer (D : Set T))
    (hzJ' : zJ' ∈ Subgroup.normalizer (D : Set T)) :
    D ≤ conjStab (aStar (CoreAssembly.conjClass K) L) :=
  Thm3Quot.conjStab_aStar_of_four hs.hyp hL hv hD hzL hzJ'

private theorem oddCoreOf_conjStab_le_of_omegaNbr (hs : FrameStd K z J zJ) {L P : Subgroup T}
    (hL : L ∈ CoreAssembly.conjClass K) (hP : P ∈ omegaNbr (CoreAssembly.conjClass K) L)
    (hPB : P ∉ aStar (CoreAssembly.conjClass K) L) :
    oddCoreOf (conjStab (aStar (CoreAssembly.conjClass K) P)) ≤
      conjStab (aStar (CoreAssembly.conjClass K) L) := by
  have hΩ := hs.hyp
  have hPΩ : P ∈ CoreAssembly.conjClass K := hP.1
  obtain ⟨-, -, TP, hTP, hTPP, hTPN⟩ := hP
  have hTPs : IsSylow2In TP P := Sec6Gen.isSylow2In_of_mem_RSet_of_le hΩ hPΩ hTP hTPP
  obtain ⟨J₀, zL, zJ₀, hv⟩ := hs.exists_aViol hL
  have hPtw : P ∉ twinSet (CoreAssembly.conjClass K) L := by
    rintro ⟨-, w, hwL, hwP⟩
    exact hPB (mem_aStar_of_twin Relation.ReflTransGen.refl hPΩ hwL hwP)
  obtain ⟨-, -, o, -, hv', hTPc⟩ := exists_aViol_conj_centralizes hΩ hL hv hPΩ hPtw hTPs hTPN
  obtain ⟨p, hp⟩ := Sec6Gen.exists_uniqueInvolution hΩ hPΩ
  have hpT : p ∈ TP := Sec6Gen.mem_of_isSylow2In hp hTPs
  have hCp : Subgroup.centralizer ({p} : Set T) ≤
      conjStab (aStar (CoreAssembly.conjClass K) P) :=
    centralizer_le_conjStab_aStar hΩ.conjInvariant hPΩ hp
  have hzL : zL ∈ Subgroup.centralizer ({p} : Set T) := by
    have h1 : p * zL * p⁻¹ = zL := hv.hzK.conj_eq (mem_normalizer_iff_conjSub_eq.mp (hTPN hpT))
    rw [Subgroup.mem_centralizer_singleton_iff]
    calc zL * p = (p * zL * p⁻¹) * p := by rw [h1]
      _ = p * zL := by group
  have hzJ' : o * zJ₀ * o⁻¹ ∈ Subgroup.centralizer ({p} : Set T) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact (Subgroup.mem_centralizer_singleton_iff.mp (hTPc hpT)).symm
  have hN : ∀ g ∈ conjStab (aStar (CoreAssembly.conjClass K) P), g ∈
      Subgroup.normalizer (oddCoreOf (conjStab (aStar (CoreAssembly.conjClass K) P)) : Set T) :=
    fun g hg => mem_normalizer_of_conjSub_eq
      (Asc77.T7V.conjSub_oddCoreOf_eq_of_mem_normalizer (Subgroup.le_normalizer hg))
  exact le_conjStab_aStar_of_odd_four hs hL hv' (oddCoreOf_odd_natCard _) (hN _ (hCp hzL))
    (hN _ (hCp hzJ'))

theorem oddCoreOf_conjStab_le_conjStab_of_omegaNbr (hs : FrameStd K z J zJ) {L P : Subgroup T}
    (hL : L ∈ CoreAssembly.conjClass K) (hP : P ∈ omegaNbr (CoreAssembly.conjClass K) L)
    (hPB : P ∉ aStar (CoreAssembly.conjClass K) L) :
    oddCoreOf (conjStab (aStar (CoreAssembly.conjClass K) P)) ≤
        conjStab (aStar (CoreAssembly.conjClass K) L) ∧
      oddCoreOf (conjStab (aStar (CoreAssembly.conjClass K) L)) ≤
        conjStab (aStar (CoreAssembly.conjClass K) P) :=
  ⟨oddCoreOf_conjStab_le_of_omegaNbr hs hL hP hPB,
    oddCoreOf_conjStab_le_of_omegaNbr hs hP.1
      (Q3CL.T3.omegaNbr_symm Sec6Gen.l6_2Gen hs.hyp hL hP.1 hP)
      (fun h => hPB (mem_aStar_symm hP.1 h).2)⟩

theorem le_conjStab_of_omegaNbr (hs : FrameStd K z J zJ) {L P : Subgroup T}
    (hL : L ∈ CoreAssembly.conjClass K) (hP : P ∈ omegaNbr (CoreAssembly.conjClass K) L)
    (hPB : P ∉ aStar (CoreAssembly.conjClass K) L) :
    P ≤ conjStab (aStar (CoreAssembly.conjClass K) L) := by
  have hΩ := hs.hyp
  have hΩc := hΩ.conjInvariant
  have hPΩ : P ∈ CoreAssembly.conjClass K := hP.1
  have hOX' : oddCoreOf (conjStab (aStar (CoreAssembly.conjClass K) P)) ≤
      conjStab (aStar (CoreAssembly.conjClass K) L) :=
    (oddCoreOf_conjStab_le_conjStab_of_omegaNbr hs hL hP hPB).1
  obtain ⟨-, -, RL, hRL, hRLL, hRLN⟩ := Q3CL.T3.omegaNbr_symm Sec6Gen.l6_2Gen hΩ hL hPΩ hP
  have hRLs : IsSylow2In RL L := Sec6Gen.isSylow2In_of_mem_RSet_of_le hΩ hL hRL hRLL
  have hRLX' : RL ≤ conjStab (aStar (CoreAssembly.conjClass K) P) :=
    hRLN.trans (normalizer_le_conjStab_aStar hΩc hPΩ Relation.ReflTransGen.refl)
  have hLB' : L ∉ aStar (CoreAssembly.conjClass K) P := fun h => hPB (mem_aStar_symm hPΩ h).2
  have h33 := comm_locMember_of_sylow_le hs hPΩ hL hLB' hRLs hRLX'
    (Relation.ReflTransGen.refl : P ∈ aStar (CoreAssembly.conjClass K) P)
  have hRLc : RL ≤ tightCore (L ⊓ conjStab (aStar (CoreAssembly.conjClass K) P)) :=
    le_tightCore_of_isPGroup (le_inf hRLs.1 hRLX') hRLs.2.1
  have hLX : L ≤ conjStab (aStar (CoreAssembly.conjClass K) L) :=
    le_conjStab_aStar hΩc hL Relation.ReflTransGen.refl
  have hRLNO : RL ≤ Subgroup.normalizer (oddCoreOf P : Set T) := fun x hx =>
    mem_normalizer_of_conjSub_eq (Asc77.T7V.conjSub_oddCoreOf_eq_of_mem_normalizer (hRLN hx))
  have hsplit :=
    Lemma54Proof.commutator_sup_centralizer hRLs.2.1 hRLNO (oddCoreOf_odd_natCard P)
  obtain ⟨zL, hzL⟩ := Sec6Gen.exists_uniqueInvolution hΩ hL
  have h8 := Sec6Gen.eight_le_of_mem_RSet hΩ hRL
  have hzRL : zL ∈ RL := mem_of_isPGroup hzL hRLs.1 hRLs.2.1 (by omega)
  have hC : oddCoreOf P ⊓ Subgroup.centralizer (RL : Set T) ≤
      conjStab (aStar (CoreAssembly.conjClass K) L) := by
    intro x hx
    apply centralizer_le_conjStab_aStar hΩc hL hzL
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact (Subgroup.mem_centralizer_iff.mp hx.2 zL hzRL).symm
  have hcomm : ⁅oddCoreOf P, RL⁆ ≤ conjStab (aStar (CoreAssembly.conjClass K) L) := by
    have h1 := (Subgroup.commutator_mono (oddCoreOf_le_self P) hRLc).trans
      (Subgroup.commutator_comm _ _).le
    exact h1.trans (h33.trans (inf_le_left.trans (sup_le ((oddCoreOf_le_self _).trans
      ((tightCore_le _).trans (inf_le_left.trans hLX))) hOX')))
  have hOP : oddCoreOf P ≤ conjStab (aStar (CoreAssembly.conjClass K) L) := by
    rw [← hsplit]
    exact sup_le hcomm hC
  obtain ⟨-, -, TP, hTP, hTPP, hTPN⟩ := hP
  have hTPs : IsSylow2In TP P := Sec6Gen.isSylow2In_of_mem_RSet_of_le hΩ hPΩ hTP hTPP
  have hTPX : TP ≤ conjStab (aStar (CoreAssembly.conjClass K) L) :=
    hTPN.trans (normalizer_le_conjStab_aStar hΩc hL Relation.ReflTransGen.refl)
  exact (le_oddCoreOf_sup_of_isSylow2In (hs.typeRHyp.twoGroup P hPΩ) hTPs).trans
    (sup_le hOP hTPX)

theorem le_conjStab_of_mem_omegaNbr_rev (hs : FrameStd K z J zJ) {L P : Subgroup T}
    (hL : L ∈ CoreAssembly.conjClass K) (hP : P ∈ omegaNbr (CoreAssembly.conjClass K) L)
    (hPB : P ∉ aStar (CoreAssembly.conjClass K) L) :
    L ≤ conjStab (aStar (CoreAssembly.conjClass K) P) := by
  exact le_conjStab_of_omegaNbr hs hP.1 (Q3CL.T3.omegaNbr_symm Sec6Gen.l6_2Gen hs.hyp hL hP.1 hP)
    (fun h => hPB (mem_aStar_symm hP.1 h).2)

private theorem aStar_le_conjStab_of_omegaNbr_aux (hs : FrameStd K z J zJ) {L P : Subgroup T}
    (hL : L ∈ CoreAssembly.conjClass K) (hP : P ∈ omegaNbr (CoreAssembly.conjClass K) L)
    (hPB : P ∉ aStar (CoreAssembly.conjClass K) L) :
    ∀ L' ∈ aStar (CoreAssembly.conjClass K) L,
      L' ≤ conjStab (aStar (CoreAssembly.conjClass K) P) := by
  have hΩc := hs.hyp.conjInvariant
  have hPΩ : P ∈ CoreAssembly.conjClass K := hP.1
  have hPX := le_conjStab_of_omegaNbr hs hL hP hPB
  have hOH := (oddCoreOf_conjStab_le_conjStab_of_omegaNbr hs hL hP hPB).2
  obtain ⟨-, -, R, hR, hRP, -⟩ := hP
  have hRs : IsSylow2In R P := Sec6Gen.isSylow2In_of_mem_RSet_of_le hs.hyp hPΩ hR hRP
  intro L' hL'
  have hL'Ω := mem_of_mem_aStar hL hL'
  have hBL' : aStar (CoreAssembly.conjClass K) L' = aStar (CoreAssembly.conjClass K) L :=
    aStar_eq_of_mem_aStar hL hL'
  obtain ⟨J', zL', zJ', hv⟩ := hs.exists_aViol hL'Ω
  have hJ'B : J' ∈ aStar (CoreAssembly.conjClass K) L := hL'.trans (mem_aStar_of_aViol hv)
  have hPB' : P ∉ aStar (CoreAssembly.conjClass K) L' := by
    rw [hBL']
    exact hPB
  obtain ⟨n, hn, hRn, hnB⟩ := exists_conj_omegaNbr_of_le_of_aViol hs.typeRHyp hs.below
    (hs.conjStab_ne_top hL) hL'Ω (le_conjStab_aStar hΩc hL hL') (le_conjStab_aStar hΩc hL hJ'B)
    hv hPΩ hPX hPB' R hRs
  rw [hBL'] at hnB
  have hnΩ : conjSub n L' ∈ CoreAssembly.conjClass K := mem_of_mem_aStar hL hnB
  have hPn : P ∈ omegaNbr (CoreAssembly.conjClass K) (conjSub n L') :=
    ⟨hPΩ, fun h => hPB (h ▸ hnB), R, hR, hRP, hRn⟩
  have hPBn : P ∉ aStar (CoreAssembly.conjClass K) (conjSub n L') := by
    rw [aStar_eq_of_mem_aStar hL hnB]
    exact hPB
  have h1 := le_conjStab_of_mem_omegaNbr_rev hs hnΩ hPn hPBn
  have h2 : n ∈ conjStab (aStar (CoreAssembly.conjClass K) P) := hOH hn
  intro x hx
  have h3 := (conjStab (aStar (CoreAssembly.conjClass K) P)).mul_mem
    ((conjStab (aStar (CoreAssembly.conjClass K) P)).mul_mem
      ((conjStab (aStar (CoreAssembly.conjClass K) P)).inv_mem h2) (h1 (conj_mem_conjSub hx))) h2
  have e : n⁻¹ * (n * x * n⁻¹) * n = x := by group
  rwa [e] at h3

theorem aStar_le_conjStab_of_omegaNbr (hs : FrameStd K z J zJ) {L P : Subgroup T}
    (hL : L ∈ CoreAssembly.conjClass K) (hP : P ∈ omegaNbr (CoreAssembly.conjClass K) L)
    (hPB : P ∉ aStar (CoreAssembly.conjClass K) L) :
    (∀ L' ∈ aStar (CoreAssembly.conjClass K) L,
        L' ≤ conjStab (aStar (CoreAssembly.conjClass K) P)) ∧
      ∀ P' ∈ aStar (CoreAssembly.conjClass K) P,
        P' ≤ conjStab (aStar (CoreAssembly.conjClass K) L) :=
  ⟨aStar_le_conjStab_of_omegaNbr_aux hs hL hP hPB,
    aStar_le_conjStab_of_omegaNbr_aux hs hP.1
      (Q3CL.T3.omegaNbr_symm Sec6Gen.l6_2Gen hs.hyp hL hP.1 hP)
      (fun h => hPB (mem_aStar_symm hP.1 h).2)⟩

end Frame

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameAEmptyPf
