module

public import CFSG.ClassicalInvolution.Asc77.AscT7Z6
public import CFSG.ClassicalInvolution.Asc77.AscT7Y1
public import CFSG.ClassicalInvolution.Asc77.AscT7Z1
public import CFSG.ClassicalInvolution.Asc77.AscT7Z5

public section

namespace CFSG.ClassicalInvolution.Asc77

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77.ExactLayer
open CFSG.ClassicalInvolution.WeakCT (LinearBlockStandardPair)
open scoped commutatorElement MatrixGroups

namespace T7Z

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
  {K K' W : Subgroup G} {z u e g : G}


theorem not_commutes_of_involution (hs : Hyp23Setting p f Ω K K' z) {L : Subgroup G} {t : G}
    (hLΩ : L ∈ Ω) (htL : IsUniqueInvolution L t) (htz : t ≠ z) : K ≠ L ∧ ¬ Commutes K L := by
  have hzK' : IsUniqueInvolution K' z := isUniqueInvolution_of_mem_twinSet hs.hz hs.hK'
  have hne : K ≠ L := by
    rintro rfl
    exact htz (htL.eq hs.hz)
  refine ⟨hne, fun h => ?_⟩
  have hmem : L ∈ omegaNbr Ω K := MuTab.mem_omegaNbr_of_commutes hLΩ hne.symm h
  have hperp : L ∈ KPerp Ω K := Or.inr hmem
  rw [hs.perp] at hperp
  rcases hperp with rfl | rfl
  · exact hne rfl
  · exact htz (htL.eq hzK')

theorem eSide [IsSimpleGroup G] (hs : Hyp23Setting p f Ω K K' z)
    (hd : Hyp23bData Ω K K' W z u e g) (hα : alphaOf (Subgroup.closure ({u, z} : Set G)) = ⊥)
    (hex : ExactMembers Ω) (hOE : classicalInvolutionOddCore ↥(exactLayer Ω e) = ⊥)
    (hE : LayerOrthType p f Ω e 6 true) :
    (∃ W', LinearBlockStandardPair (GaloisField p f) W' K (conjSub g K)) ∧
      (∃ W', LinearBlockStandardPair (GaloisField p f) W' K (conjSub g K')) ∧
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
  have hJe := conjSub_le_centralizer_e hd hKe
  have hJ'e := conjSub_le_centralizer_e hd hK'e
  have hKΦ : K ∈ exactFamily Ω e := centMembers_subset_exactFamily hcls ⟨hKΩ, hKe⟩
  have hK'Φ : K' ∈ exactFamily Ω e := centMembers_subset_exactFamily hcls ⟨hK'Ω, hK'e⟩
  have hJΦ : conjSub g K ∈ exactFamily Ω e := centMembers_subset_exactFamily hcls ⟨hJΩ, hJe⟩
  have hJ'Φ : conjSub g K' ∈ exactFamily Ω e :=
    centMembers_subset_exactFamily hcls ⟨hJ'Ω, hJ'e⟩
  have htJ : IsUniqueInvolution (conjSub g K) (u * e) := hd.hgt ▸ hs.hz.conj g
  have htJ' : IsUniqueInvolution (conjSub g K') (u * e) := hd.hgt ▸ hzK'.conj g
  have htz := t_ne_z hs hd
  obtain ⟨hKJ, hKJc⟩ := not_commutes_of_involution hs hJΩ htJ htz
  obtain ⟨hKJ', hKJc'⟩ := not_commutes_of_involution hs hJ'Ω htJ' htz
  have hexeq : ∀ L ∈ Ω, Nonempty (↥L ≃* SL(2, GaloisField p f)) := by
    intro L hL
    obtain ⟨zL, hzL⟩ := hcls L hL
    exact hzL.nonempty_equiv_sl2 (hex L hL)
  obtain ⟨t', n', ht', D, hcard, i, hit, hir⟩ := T7Z.exists_omegaLie_of_layerOrth hOE hE
  have htn : t' = .PSL ∧ n' = 4 := by
    rcases ht' with h | h | h | h | h | h <;> simp_all
  have hie : D.exp i = f := by
    rcases D.exp_eq i with h | ⟨h, -⟩
    · exact h
    · exact absurd (hit.symm.trans h) (by rw [htn.1]; decide)
  obtain ⟨P⟩ := nonempty_pslLayer_of_omegaLie D hcard i (hit.trans htn.1) (hir.trans htn.2) hie
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
    have hy' : y ∈ exactLayer Ω e := (exactLayer_eq_omegaGen Ω e) ▸ hy
    exact (Subgroup.mem_centralizer_singleton_iff.mp (exactLayer_le_centralizer Ω e hy')).symm
  have htab : u * e = a * b * e := by rw [hu]
  have hcomm := twin_commutes hs hex
  obtain ⟨RK, hRK, hKR⟩ := P.fund K hKΦ
  obtain ⟨RK', hRK', hKR'⟩ := P.fund K' hK'Φ
  have haK : a ∈ K := hR.1 haR
  have hbK' : b ∈ K' := hR'.1 hbR'
  obtain ⟨RJ, hRJ, hJR, hmJ, hpJ⟩ := PSLLayer.pair_of_member hp2 hq P hRK hKR hKR' hJΦ
    (hexeq K hKΩ) (hexeq _ hJΩ) hs.hz htJ haK hbK' haa hcomm heΦ hecen htab hKJ hKJc
  obtain ⟨RJ', hRJ', hJ'R, hmJ', hpJ'⟩ := PSLLayer.pair_of_member hp2 hq P hRK hKR hKR' hJ'Φ
    (hexeq K hKΩ) (hexeq _ hJ'Ω) hs.hz htJ' haK hbK' haa hcomm heΦ hecen htab hKJ' hKJc'
  refine ⟨hpJ, hpJ', ?_⟩
  obtain ⟨W₁, hW₁⟩ := hmJ'
  have hgen := PSLLayer.sup_eq_omegaGen hp2 hq P hRJ' hKR hJR hJ'R
    ⟨W₁, linearBlockStandardPair_symm hW₁⟩ hmJ (hcomm.conjSub g)
  exact (exactLayer_eq_omegaGen Ω e).le.trans hgen.ge

end T7Z

end CFSG.ClassicalInvolution.Asc77
