module

public import CFSG.ClassicalInvolution.Asc77.AscB3C2
public import CFSG.ClassicalInvolution.Asc77.AscT7Z7
public import CFSG.ClassicalInvolution.Asc77.AscC22N1
public import CFSG.ClassicalInvolution.Asc77.AscC22P14
public import CFSG.ClassicalInvolution.Asc77.AscC22P16

public section

namespace CFSG.ClassicalInvolution.Asc77

namespace B3C

set_option linter.unusedSectionVars false

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77.ExactLayer
open CFSG.ClassicalInvolution.Phan (UnitaryBlockStandardPair)

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
  {K K' W : Subgroup G} {z u e g : G}


theorem eSideU [IsSimpleGroup G] (hs : Hyp23Setting p f Ω K K' z)
    (hd : Hyp23bData Ω K K' W z u e g) (hα : alphaOf (Subgroup.closure ({u, z} : Set G)) = ⊥)
    (hex : ExactMembers Ω) (hOE : classicalInvolutionOddCore ↥(exactLayer Ω e) = ⊥)
    (hE : LayerOrthType p f Ω e 6 false) :
    (∃ W', UnitaryBlockStandardPair (GaloisField p (2 * f)) p f W' K (conjSub g K)) ∧
      (∃ W', UnitaryBlockStandardPair (GaloisField p (2 * f)) p f W' K (conjSub g K')) ∧
      exactLayer Ω e ≤ conjSub g K' ⊔ K ⊔ conjSub g K := by
  classical
  have hst := hs.stand
  have hp2 : p ≠ 2 := hst.odd
  have hq : 5 ≤ p ^ f := hst.five
  have hKΩ : K ∈ Ω := hst.mem
  have hK'Ω : K' ∈ Ω := hs.hK'.1
  have hcls := hst.hyp.classical
  have hzK' : IsUniqueInvolution K' z := isUniqueInvolution_of_mem_twinSet hs.hz hs.hK'
  obtain ⟨R, R', a, b, r, hR, hR', -, hRN, hR'N, haR, hbR', -, -, hu, haa, hbb, -, -⟩ :=
    T7K.exists_decomp hs hd
  have hKe : K ≤ Subgroup.centralizer ({e} : Set G) :=
    T7Y.le_centralizer_e hs hd hα hKΩ hs.hz hR hRN
  have hK'e : K' ≤ Subgroup.centralizer ({e} : Set G) :=
    T7Y.le_centralizer_e hs hd hα hK'Ω hzK' hR' hR'N
  have hJΩ : conjSub g K ∈ Ω := hst.hyp.conjInvariant g K hKΩ
  have hJ'Ω : conjSub g K' ∈ Ω := hst.hyp.conjInvariant g K' hK'Ω
  have hJe := T7Z.conjSub_le_centralizer_e hd hKe
  have hJ'e := T7Z.conjSub_le_centralizer_e hd hK'e
  have hKΦ : K ∈ exactFamily Ω e := centMembers_subset_exactFamily hcls ⟨hKΩ, hKe⟩
  have hK'Φ : K' ∈ exactFamily Ω e := centMembers_subset_exactFamily hcls ⟨hK'Ω, hK'e⟩
  have hJΦ : conjSub g K ∈ exactFamily Ω e := centMembers_subset_exactFamily hcls ⟨hJΩ, hJe⟩
  have hJ'Φ : conjSub g K' ∈ exactFamily Ω e :=
    centMembers_subset_exactFamily hcls ⟨hJ'Ω, hJ'e⟩
  have htJ : IsUniqueInvolution (conjSub g K) (u * e) := hd.hgt ▸ hs.hz.conj g
  have htJ' : IsUniqueInvolution (conjSub g K') (u * e) := hd.hgt ▸ hzK'.conj g
  have htz := T7Z.t_ne_z hs hd
  obtain ⟨hKJ, hKJc⟩ := T7Z.not_commutes_of_involution hs hJΩ htJ htz
  obtain ⟨hKJ', hKJc'⟩ := T7Z.not_commutes_of_involution hs hJ'Ω htJ' htz
  obtain ⟨P⟩ := C22N.nonempty_psuLayer_of_layerOrth hOE hE
  have hKle : K ≤ omegaGen (exactFamily Ω e) := le_omegaGen hKΦ
  have hK'le : K' ≤ omegaGen (exactFamily Ω e) := le_omegaGen hK'Φ
  have hJle : conjSub g K ≤ omegaGen (exactFamily Ω e) := le_omegaGen hJΦ
  have heΦ : e ∈ omegaGen (exactFamily Ω e) := by
    have hue : u ∈ omegaGen (exactFamily Ω e) := sup_le hKle hK'le hd.hu
    have ht : u * e ∈ omegaGen (exactFamily Ω e) := hJle htJ.mem
    have key : e = u * (u * e) := by
      have := hd.hu2
      calc e = (u * u) * e := by rw [this, one_mul]
        _ = u * (u * e) := by group
    have h := Subgroup.mul_mem _ hue ht
    rwa [← key] at h
  have hecen : ∀ y ∈ omegaGen (exactFamily Ω e), e * y = y * e := by
    intro y hy
    have hy' : y ∈ exactLayer Ω e := (T7Z.exactLayer_eq_omegaGen Ω e) ▸ hy
    exact (Subgroup.mem_centralizer_singleton_iff.mp (exactLayer_le_centralizer Ω e hy')).symm
  have htab : u * e = a * b * e := by rw [hu]
  have hcomm := T7Z.twin_commutes hs hex
  obtain ⟨RK, hRK, hKR⟩ := P.fund K hKΦ
  obtain ⟨RK', hRK', hKR'⟩ := P.fund K' hK'Φ
  obtain ⟨RJ, hRJ, hJR⟩ := P.fund _ hJΦ
  obtain ⟨RJ', hRJ', hJ'R⟩ := P.fund _ hJ'Φ
  have haK : a ∈ K := hR.1 haR
  have hbK' : b ∈ K' := hR'.1 hbR'
  obtain ⟨-, hpJ⟩ := C22G.PSULayer.pair_of_member_ne hp2 hq P hRK hRJ hKR hKR' hJR hs.hz htJ haK
    hbK' haa hcomm heΦ hecen htab hKJ hKJc
  obtain ⟨-, hpJ'⟩ := C22G.PSULayer.pair_of_member_ne hp2 hq P hRK hRJ' hKR hKR' hJ'R hs.hz htJ'
    haK hbK' haa hcomm heΦ hecen htab hKJ' hKJc'
  refine ⟨hpJ, hpJ', ?_⟩
  have hgen := C22G.PSULayer.sup_eq_of_chain hp2 hq P hRK hRJ hRJ' hKR hKR' hJR hJ'R hs.hz htJ
    htJ' haK hbK' haa hcomm (hcomm.conjSub g) heΦ hecen htab hKJ hKJc hKJ' hKJc'
  exact (T7Z.exactLayer_eq_omegaGen Ω e).le.trans hgen.ge

end B3C

end CFSG.ClassicalInvolution.Asc77
