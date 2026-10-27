module

public import CFSG.ClassicalInvolution.Q3.TL4VtxMain
public import CFSG.ClassicalInvolution.Q3.TL4D4NCCor
public import CFSG.ClassicalInvolution.Q3.TL4VtxFree
public import CFSG.ClassicalInvolution.Q3.TL4VtxTwin

public section

namespace CFSG.ClassicalInvolution.Q3.TL4

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Balance
open CFSG.ClassicalInvolution.Asc77.T8 (XMem)
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {n : ℕ}


theorem hyp51At_of_vtxPair (h4 : Thm4RBelow 3 n) (h5 : Thm5RBelowF 3 n)
    (htw : PhilipHall.Frame.Thm1RTwinLiftSetBelow n) (hE4 : E4AutOddFreeR)
    (hBelow : CIT3Below (Nat.card G)) (hZ : Subgroup.center G = ⊥) (hGn : Nat.card G ≤ n)
    (hΩ : TypeRFam 3 Ω) {B : Subgroup G} (hB : IsElemAbelian 2 B) {a b c : G}
    (hgen : B = Subgroup.closure {a, b, c}) (hc1 : c ≠ 1) (ha1 : a ≠ 1) (hac : a ≠ c)
    (hb1 : b ≠ 1) (hbc : b ≠ c) (hab : a ≠ b) (habc : a * b ≠ c) {Ma Mb : Subgroup G}
    (hMa : XMem Ω c Ma) (hMb : XMem Ω c Mb) (ha : IsUniqueInvolution Ma a)
    (hb : IsUniqueInvolution Mb b) {P : Subgroup G} (hP : IsSylow2In P Mb)
    (hPc : P ≤ Subgroup.centralizer ({c} : Set G)) (hPN : P ≤ Subgroup.normalizer (Ma : Set G)) :
    Hyp51At B c := by
  have haB : a ∈ B := hgen ▸ Subgroup.subset_closure (Set.mem_insert _ _)
  have hbB : b ∈ B :=
    hgen ▸ Subgroup.subset_closure (Set.mem_insert_of_mem _ (Set.mem_insert _ _))
  have hcB : c ∈ B :=
    hgen ▸ Subgroup.subset_closure (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ rfl))
  have hBc : ∀ x ∈ B, ∀ y ∈ B, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hB.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  have hsq : ∀ x ∈ B, x * x = 1 := fun x hx => (sq x).symm.trans (hB.2 x hx)
  have haC : a ∈ Subgroup.centralizer ({c} : Set G) :=
    Subgroup.mem_centralizer_singleton_iff.mpr (hBc a haB c hcB)
  have hbC : b ∈ Subgroup.centralizer ({c} : Set G) :=
    Subgroup.mem_centralizer_singleton_iff.mpr (hBc b hbB c hcB)
  have habC : a * b ∈ Subgroup.centralizer ({c} : Set G) := Subgroup.mul_mem _ haC hbC
  have habB : a * b ∈ B := Subgroup.mul_mem _ haB hbB
  have hab1 : a * b ≠ 1 := fun h1 => hab (by
    calc a = a * (b * b) := by rw [hsq b hbB, mul_one]
      _ = (a * b) * b := by group
      _ = b := by rw [h1, one_mul])
  have hΦ : TypeRFam 3 (vtxFam Ω c) := hΩ.vtxFam
  have hO := oddQuot_oddCore_eq_bot c
  have hQn : Nat.card (OddQuot c) < n := lt_of_lt_of_le (natCard_oddQuot_lt hZ hc1) hGn
  have hKa := modOdd_coreAt_mem_vtxFam hMa
  have hKb := modOdd_coreAt_mem_vtxFam hMb
  have haz := isUniqueInvolution_modOdd_coreAt hΩ hMa ha haC
  have hbz := isUniqueInvolution_modOdd_coreAt hΩ hMb hb hbC
  have haB' := oddQuotMk_mem_modOdd haB haC
  have hbB' := oddQuotMk_mem_modOdd hbB hbC
  have habB' := oddQuotMk_mem_modOdd habB habC
  have haZ := Lemma52Proof.oddQuotMk_not_mem_zpowers hB hcB hc1 haB ha1 hac haC
  have hbZ := Lemma52Proof.oddQuotMk_not_mem_zpowers hB hcB hc1 hbB hb1 hbc hbC
  have habZ := Lemma52Proof.oddQuotMk_not_mem_zpowers hB hcB hc1 habB hab1 habc habC
  have hmul : oddQuotMk c ⟨a * b, habC⟩ = oddQuotMk c ⟨a, haC⟩ * oddQuotMk c ⟨b, hbC⟩ :=
    map_mul (oddQuotMk c) (⟨a, haC⟩ : ↥(Subgroup.centralizer ({c} : Set G))) ⟨b, hbC⟩
  have hcomm : oddQuotMk c ⟨a, haC⟩ * oddQuotMk c ⟨b, hbC⟩ =
      oddQuotMk c ⟨b, hbC⟩ * oddQuotMk c ⟨a, haC⟩ := by
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (hBc a haB b hbB)
  have hne : modOdd c (coreAt c Ma) ≠ modOdd c (coreAt c Mb) := by
    intro e
    have he := haz.eq (e ▸ hbz)
    apply habZ
    have hbb : (⟨b, hbC⟩ * ⟨b, hbC⟩ : ↥(Subgroup.centralizer ({c} : Set G))) = 1 :=
      Subtype.ext hb.sq
    rw [hmul, he, ← map_mul, hbb, map_one]
    exact Subgroup.one_mem _
  have hnbr := modOdd_coreAt_mem_omegaNbr hMb hP hPc hPN hne
  have hnbr' := Q3CL.T3.omegaNbr_symm Sec6Gen.l6_2Gen hΦ.hyp hKa hKb hnbr
  refine ⟨fun L₁ L₂ hL₁ hL₂ hm₁ hm₂ => Vtx.moves_atMostOne h4 hΦ hO hQn hKa haz hL₁ hL₂
    (hm₁ _ haB' haZ) (hm₂ _ haB' haZ), fun L hL hm => ?_⟩
  have hma := hm _ haB' haZ
  have hmb := hm _ hbB' hbZ
  have hmab : ∃ y ∈ L, oddQuotMk c ⟨a, haC⟩ * oddQuotMk c ⟨b, hbC⟩ * y ≠
      y * (oddQuotMk c ⟨a, haC⟩ * oddQuotMk c ⟨b, hbC⟩) := by
    rw [← hmul]
    exact hm _ habB' habZ
  have hmba : ∃ y ∈ L, oddQuotMk c ⟨b, hbC⟩ * oddQuotMk c ⟨a, haC⟩ * y ≠
      y * (oddQuotMk c ⟨b, hbC⟩ * oddQuotMk c ⟨a, haC⟩) := by
    rw [← hcomm]
    exact hmab
  have haN := Vtx.orbGrp_le_normalizer h4 hΦ hO hQn hKa haz hL hma (Vtx.le_orbGrp _ haz.mem)
  have hbN := Vtx.orbGrp_le_normalizer h4 hΦ hO hQn hKb hbz hL hmb (Vtx.le_orbGrp _ hbz.mem)
  have himg := Vtx.inducedImage_modOdd_eq haC hbC haN hbN
  have hsq' : ∀ x ∈ modOdd c B, x * x = 1 := by
    rintro _ ⟨k, hk, rfl⟩
    have hkk : k * k = 1 := Subtype.ext (hsq _ (Subgroup.mem_subgroupOf.mp hk))
    rw [← map_mul, hkk, map_one]
  obtain ⟨ya, hya, hnea⟩ := hma
  have hσa1 := Lemma52Proof.toInducedAutOn_ne_one_of_moved L haN hya hnea
  have hE4L : ∀ {K : Subgroup (OddQuot c)} {z : OddQuot c}, K ∈ vtxFam Ω c →
      IsUniqueInvolution K z → (∃ y ∈ L, z * y ≠ y * z) →
      PhilipHall.Frame.TwinE4 ↥(Vtx.orbGrp (vtxFam Ω c) K) →
        alphaOf (inducedImage L (modOdd c B)) = ⊥ := by
    intro K z hK hz hmz hT
    obtain ⟨y, hy, hne'⟩ := hmz
    have hLX := Vtx.le_orbGrp_of_moves hΦ.hyp.conjInvariant hK hL ⟨z, hz.mem, y, hy, hne'⟩
    have hLn := Vtx.normal_subgroupOf_orbGrp h4 hΦ hO hQn hK hz hL ⟨y, hy, hne'⟩
    exact Vtx.alphaOf_inducedImage_eq_bot_of_autOddFree (Vtx.autOddFree_of_quot_center hL.1.1
      (hE4 _ (Vtx.exLie_of_twinE4 hLX hLn hL hT))) hsq' haB' haN hσa1
  by_cases hta : Vtx.TwinFreeAt (vtxFam Ω c) (modOdd c (coreAt c Ma)) (oddQuotMk c ⟨a, haC⟩) L
  · rw [hgen, himg]
    exact Vtx.alphaOf_eq_bot_of_twinFree h4 h5 hΦ hO hQn hKa hnbr haz hbz hL ⟨ya, hya, hnea⟩
      hmb hmab hta haN hbN
  by_cases htb : Vtx.TwinFreeAt (vtxFam Ω c) (modOdd c (coreAt c Mb)) (oddQuotMk c ⟨b, hbC⟩) L
  · rw [hgen, himg, Set.pair_comm]
    exact Vtx.alphaOf_eq_bot_of_twinFree h4 h5 hΦ hO hQn hKb hnbr' hbz haz hL hmb
      ⟨ya, hya, hnea⟩ hmba htb hbN haN
  rcases Vtx.twin_outcome h4 htw hΦ hO hQn hKa haz hL ⟨ya, hya, hnea⟩ hta with hT | hla
  · exact hE4L hKa haz ⟨ya, hya, hnea⟩ hT
  rcases Vtx.twin_outcome h4 htw hΦ hO hQn hKb hbz hL hmb htb with hT | hlb
  · exact hE4L hKb hbz hmb hT
  have hH := hyp51At_of_classicalOrQuiet_pair hBelow hZ hB hgen hc1 ha1 hac hb1 hbc haC hbC
    (Vtx.classicalOrQuiet_of_hasLift hΩ hMa ha haC hla)
    (Vtx.classicalOrQuiet_of_hasLift hΩ hMb hb hbC hlb) d4OddAutInnerNC3_proved
  exact hH.2 L hL hm

end CFSG.ClassicalInvolution.Q3.TL4
