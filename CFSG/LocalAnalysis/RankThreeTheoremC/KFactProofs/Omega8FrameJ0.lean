module

public import Certificates.Certificate9490
public import CFSG.Certificates.NativeSchreierEnum
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.PumpTC7Word
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEightMinus.NativeModel

public noncomputable section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Omega8Frame

open CFSG.Open CFSG.Certificates CFSG.Certificates.Native CFSG.Monster.B.Co2
  CFSG.Monster.B.Co2.Native CFSG.EvenSmallLie.OmegaEightMinus CFSG.ComponentClassification

theorem chain_ok :
    rawChainOK 136 (betaArrs.extract 0 3) betaArrs (frameBase.map Fin.val).toArray j0W 4 = true ∧
      rawOrbitSizes 136 betaArrs (frameBase.map Fin.val).toArray = [3, 3, 3] ∧
      rawChainOK 136 (t0S.extract 0 4) t0S (frameBase.map Fin.val).toArray t0W 4 = true ∧
      rawOrbitSizes 136 t0S (frameBase.map Fin.val).toArray = [9, 3, 3] := by
  have h := (Certificates.certificate9490).1
  simp only [chainCheck, Bool.and_eq_true, beq_iff_eq] at h
  exact ⟨h.1.1.1, h.1.1.2, h.1.2, h.2⟩

theorem betaArrs_size : betaArrs.size = 3 := rfl

theorem t0S_size : t0S.size = 4 := rfl

@[expose] def j0Q : RawSchreierDatum 136 :=
  RawSchreierDatum.ofArrays 136 (by norm_num) betaArrs 3 (by rw [betaArrs_size]) frameBase
    (by decide) j0W

@[expose] def t0Q : RawSchreierDatum 136 :=
  RawSchreierDatum.ofArrays 136 (by norm_num) t0S 4 (by rw [t0S_size]) frameBase (by decide) t0W

@[expose] def J0 : Subgroup (Equiv.Perm (Fin 136)) := j0Q.originalSubgroup

@[expose] def T0 : Subgroup (Equiv.Perm (Fin 136)) := t0Q.originalSubgroup

@[expose] def betaP (i : ℕ) : Equiv.Perm (Fin 136) := permOfArr 136 betaArrs[i]!

@[expose] def cP : Equiv.Perm (Fin 136) := permOfArr 136 cArr

theorem J0_eq : J0 = Subgroup.closure {g | ∃ i < 3, betaP i = g} := by
  rw [J0, j0Q, J2Cover.ofArrays_originalSubgroup]
  rfl

theorem T0_eq : T0 = Subgroup.closure {g | ∃ i < 4, permOfArr 136 t0S[i]! = g} := by
  rw [T0, t0Q, J2Cover.ofArrays_originalSubgroup]

theorem t0S_getElem!_beta {i : ℕ} (hi : i < 3) : t0S[i]! = betaArrs[i]! := by
  interval_cases i <;> rfl

theorem t0S_getElem!_three : t0S[3]! = cArr := rfl

theorem rep_beta {i : ℕ} (hi : i < 3) :
    Rep 136 betaArrs[i]! (betaP i) :=
  J2Cover.rep_permOfArr_of_chainOK chain_ok.1 (by rw [betaArrs_size]; exact hi)

theorem rep_c : Rep 136 cArr cP := by
  have h := J2Cover.rep_permOfArr_of_chainOK chain_ok.2.2.1 (j := 3) (by rw [t0S_size]; omega)
  rwa [t0S_getElem!_three] at h

theorem betaP_mem_J0 {i : ℕ} (hi : i < 3) : betaP i ∈ J0 := by
  rw [J0_eq]
  exact Subgroup.subset_closure ⟨i, hi, rfl⟩

theorem betaP_mem_T0 {i : ℕ} (hi : i < 3) : betaP i ∈ T0 := by
  rw [T0_eq]
  exact Subgroup.subset_closure ⟨i, by omega, by rw [t0S_getElem!_beta hi]; rfl⟩

theorem cP_mem_T0 : cP ∈ T0 := by
  rw [T0_eq]
  exact Subgroup.subset_closure ⟨3, by omega, by rw [t0S_getElem!_three]; rfl⟩

theorem J0_le_T0 : J0 ≤ T0 := by
  rw [J0_eq, Subgroup.closure_le]
  rintro _ ⟨i, hi, rfl⟩
  exact betaP_mem_T0 hi

theorem card_J0 : Nat.card J0 = 27 := by
  rw [J0, j0Q, J2Cover.ofArrays_card (by norm_num) chain_ok.1, chain_ok.2.1]
  rfl

theorem card_T0 : Nat.card T0 = 81 := by
  rw [T0, t0Q, J2Cover.ofArrays_card (by norm_num) chain_ok.2.2.1, chain_ok.2.2.2]
  rfl

theorem mem_omegaT_of_sift {g : Array ℕ}
    {G : Equiv.Perm (Fin 136)} (hG : Rep 136 g G)
    (h : siftA 136 omegaLevels (omegaBase.map Fin.val).toArray 0 g = true) : G ∈ omegaT :=
  (J2Cover.ofArrays_mem_iff (by norm_num) omegaChain_ok.1 hG).1 h

theorem mem_J0_of_sift {g : Array ℕ}
    {G : Equiv.Perm (Fin 136)} (hG : Rep 136 g G)
    (h : siftA 136 j0Levels (frameBase.map Fin.val).toArray 0 g = true) : G ∈ J0 :=
  (J2Cover.ofArrays_mem_iff (by norm_num) chain_ok.1 hG).1 h

theorem mem_ok :
    (∀ k < 4, siftA 136 omegaLevels (omegaBase.map Fin.val).toArray 0 t0S[k]! = true) ∧
      siftA 136 omegaLevels (omegaBase.map Fin.val).toArray 0 tauArr = true ∧
      siftA 136 omegaLevels (omegaBase.map Fin.val).toArray 0 sArr = true ∧
      isInvA 136 tauArr (invCand 136 tauArr) = true ∧
      isInvA 136 sArr (invCand 136 sArr) = true ∧
      (∀ g < 3, ∀ i < 3, siftA 136 j0Levels (frameBase.map Fin.val).toArray 0
        (conjA nGens[g]! betaArrs[i]!) = true) ∧
      eqA 136 (conjA cArr betaArrs[0]!) betaArrs[1]! = true ∧
      eqA 136 (conjA cArr betaArrs[1]!) betaArrs[2]! = true ∧
      (∀ k < 6, suppA sixArrs[k]! = 108) ∧
      (∀ k < 6, ∀ l < 6, k ≠ l → eqA 136 sixArrs[k]! sixArrs[l]! = false) := by
  have h := (Certificates.certificate9490).2.1
  simp only [memCheck, Bool.and_eq_true, allLt_iff, beq_iff_eq, Bool.or_eq_true,
    Bool.not_eq_true', and_assoc] at h
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h11⟩ := h
  refine ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, fun k hk l hl hkl => ?_⟩
  rcases h11 k hk l hl with h | h
  · exact absurd h hkl
  · exact h

theorem T0_le_omegaT :
    T0 ≤ omegaT := by
  rw [T0_eq, Subgroup.closure_le]
  rintro _ ⟨k, hk, rfl⟩
  have hrep := J2Cover.rep_permOfArr_of_chainOK chain_ok.2.2.1 (by rw [t0S_size]; exact hk)
  exact mem_omegaT_of_sift hrep (mem_ok.1 k hk)

theorem cP_mem_omegaT :
    cP ∈ omegaT :=
  T0_le_omegaT cP_mem_T0

theorem j0Q_chainArrays :
    ChainArrays j0Q (betaArrs.extract 0 3) betaArrs (frameBase.map Fin.val).toArray j0W :=
  J2Cover.ofArrays_chainArrays chain_ok.1

theorem exists_rep_of_mem_J0 {x : Equiv.Perm (Fin 136)}
    (hx : x ∈ J0) : ∃ a < j0Levels[0]!.pts.size, ∃ b < j0Levels[1]!.pts.size,
      ∃ c < j0Levels[2]!.pts.size, Rep 136 (prod3 136 j0Levels a b c) x := by
  have hA := j0Q_chainArrays
  have hF := chainCheckFacts chain_ok.1
  obtain ⟨a, ha, b, hb, c, hc, hprod⟩ := ChainArrays.exists_prod3 hA (by norm_num) chain_ok.1
    (by decide) (fun i h3 hi => absurd hi (by change ¬ i < 3; omega)) hx
  refine ⟨a, ha, b, hb, c, hc, fun p => ?_⟩
  rw [prod3, getElem!_ofFn_nat _ p.2, ← hprod]
  exact (ChainArrays.prod3_apply hA hF (by decide) ha hb hc p).symm

theorem elt_ok {a b c : ℕ} (ha : a < j0Levels[0]!.pts.size)
    (hb : b < j0Levels[1]!.pts.size) (hc : c < j0Levels[2]!.pts.size) :
    eqA 136 (compA 136 (prod3 136 j0Levels a b c) (compA 136 (prod3 136 j0Levels a b c)
        (prod3 136 j0Levels a b c))) (idA 136) = true ∧
      (∀ a' < j0Levels[0]!.pts.size, ∀ b' < j0Levels[1]!.pts.size,
        ∀ c' < j0Levels[2]!.pts.size,
        eqA 136 (compA 136 (prod3 136 j0Levels a b c) (prod3 136 j0Levels a' b' c'))
          (compA 136 (prod3 136 j0Levels a' b' c') (prod3 136 j0Levels a b c)) = true) ∧
      (suppA (prod3 136 j0Levels a b c) = 108 ↔ notSix (prod3 136 j0Levels a b c) = false) ∧
      (eqA 136 (compA 136 (prod3 136 j0Levels a b c) cArr)
          (compA 136 cArr (prod3 136 j0Levels a b c)) = true →
        eqA 136 (prod3 136 j0Levels a b c) (idA 136) = true ∨
          eqA 136 (prod3 136 j0Levels a b c) zArr = true ∨
          eqA 136 (prod3 136 j0Levels a b c) (invCand 136 zArr) = true) ∧
      (eqA 136 (prod3 136 j0Levels a b c) (idA 136) = true ∨
        suppA (prod3 136 j0Levels a b c) = 108 ∨
        sepOK (prod3 136 j0Levels a b c) (pick4 (prod3 136 j0Levels a b c)) = true) := by
  have h := (Certificates.certificate9490).2.2.1
  rw [eltCheck] at h
  have h' := allLt_spec (allLt_spec (allLt_spec h ha) hb) hc
  simp only [Bool.and_eq_true, Bool.or_eq_true, allLt_iff, beq_iff_eq] at h'
  obtain ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩ := h'
  refine ⟨h1, h2, ?_, ?_, ?_⟩
  · rw [← beq_iff_eq, h3]
    cases notSix (prod3 136 j0Levels a b c) <;> simp
  · intro hcomm
    rcases h4 with (((h4 | h4) | h4) | h4)
    · rw [hcomm] at h4
      exact absurd h4 (by decide)
    · exact Or.inl h4
    · exact Or.inr (Or.inl h4)
    · exact Or.inr (Or.inr h4)
  · rcases h5 with ((h5 | h5) | h5)
    · exact Or.inl h5
    · exact Or.inr (Or.inl h5)
    · exact Or.inr (Or.inr h5)

theorem isElemAbelian_J0 : IsElemAbelian 3 J0 := by
  refine ⟨⟨⟨fun x y => Subtype.ext ?_⟩⟩, fun x hx => ?_⟩
  · obtain ⟨a, ha, b, hb, c, hc, hx⟩ := exists_rep_of_mem_J0 x.2
    obtain ⟨a', ha', b', hb', c', hc', hy⟩ := exists_rep_of_mem_J0 y.2
    exact eq_of_eqA (rep_compA hx hy) (rep_compA hy hx) ((elt_ok ha hb hc).2.1 a' ha' b' hb' c' hc')
  · obtain ⟨a, ha, b, hb, c, hc, hx'⟩ := exists_rep_of_mem_J0 hx
    have h := eq_of_eqA (rep_compA hx' (rep_compA hx' hx')) rep_idA (elt_ok ha hb hc).1
    rw [pow_three, h]

@[expose] def zP : Equiv.Perm (Fin 136) := betaP 0 * betaP 1 * betaP 2

theorem rep_z : Rep 136 zArr zP :=
  rep_compA (rep_compA (rep_beta (by norm_num)) (rep_beta (by norm_num))) (rep_beta (by norm_num))

theorem mem_of_mem_J0_of_commute_c {x : Equiv.Perm (Fin 136)}
    (hx : x ∈ J0) (hc : x * cP = cP * x) : x = 1 ∨ x = zP ∨ x = zP⁻¹ := by
  obtain ⟨a, ha, b, hb, c, hc', hx'⟩ := exists_rep_of_mem_J0 hx
  have h := (elt_ok ha hb hc').2.2.2.1
    ((eqA_iff (rep_compA hx' rep_c) (rep_compA rep_c hx')).2 hc)
  rcases h with h | h | h
  · exact Or.inl (eq_of_eqA hx' rep_idA h)
  · exact Or.inr (Or.inl (eq_of_eqA hx' rep_z h))
  · exact Or.inr (Or.inr (eq_of_eqA hx'
      (EvenSporadicStandard.HSStd.PumpTC7.rep_invCand_of_rep rep_z) h))

theorem card_inf_le_three {J' : Subgroup (Equiv.Perm (Fin 136))}
    (hJ' : IsElemAbelian 3 J') (hsup : J0 ⊔ J' = T0) : Nat.card ↥(J0 ⊓ J') ≤ 3 := by
  have hcen : T0 ≤ Subgroup.centralizer ((J0 ⊓ J' : Subgroup _) : Set (Equiv.Perm (Fin 136))) := by
    rw [← hsup, sup_le_iff]
    constructor
    · intro y hy
      rw [Subgroup.mem_centralizer_iff]
      intro x hx
      have := isElemAbelian_J0.1.1.comm ⟨x, hx.1⟩ ⟨y, hy⟩
      exact congrArg Subtype.val this
    · intro y hy
      rw [Subgroup.mem_centralizer_iff]
      intro x hx
      have := hJ'.1.1.comm ⟨x, hx.2⟩ ⟨y, hy⟩
      exact congrArg Subtype.val this
  have hsub : ((J0 ⊓ J' : Subgroup _) : Set (Equiv.Perm (Fin 136))) ⊆ {1, zP, zP⁻¹} := by
    intro x hx
    have hxc := Subgroup.mem_centralizer_iff.1 (hcen cP_mem_T0) x hx
    rcases mem_of_mem_J0_of_commute_c hx.1 hxc with h | h | h <;> simp [h]
  calc Nat.card ↥(J0 ⊓ J') = ((J0 ⊓ J' : Subgroup _) : Set (Equiv.Perm (Fin 136))).ncard :=
        (Nat.card_coe_set_eq _)
    _ ≤ ({1, zP, zP⁻¹} : Set (Equiv.Perm (Fin 136))).ncard := Set.ncard_le_ncard hsub
    _ ≤ 3 := by
        refine (Set.ncard_insert_le _ _).trans ?_
        refine Nat.succ_le_succ ((Set.ncard_insert_le _ _).trans ?_)
        simp

theorem eq_J0_of_le_T0 {J' : Subgroup (Equiv.Perm (Fin 136))}
    (hJ'T : J' ≤ T0) (hJ' : IsElemAbelian 3 J') (hcard : Nat.card J' = 27) : J' = J0 := by
  have hT : Nat.card T0 = 81 := card_T0
  have hJ : Nat.card J0 = 27 := card_J0
  by_contra hne
  have hsupT : J0 ⊔ J' ≤ T0 := sup_le J0_le_T0 hJ'T
  have hd1 : Nat.card ↥(J0 ⊔ J') ∣ 81 := hT ▸ Subgroup.card_dvd_of_le hsupT
  have hd2 : 27 ∣ Nat.card ↥(J0 ⊔ J') := hJ ▸ Subgroup.card_dvd_of_le le_sup_left
  have hsup : J0 ⊔ J' = T0 := by
    obtain ⟨k, hk⟩ := hd2
    have hk3 : k ∣ 3 := by
      rw [hk] at hd1
      exact (Nat.mul_dvd_mul_iff_left (by norm_num : 0 < 27)).1 (by simpa using hd1)
    rcases (Nat.dvd_prime Nat.prime_three).1 hk3 with rfl | rfl
    · exfalso
      have heq : J0 ⊔ J' = J0 := (Subgroup.eq_of_le_of_card_ge le_sup_left (by
        rw [hk, hJ])).symm
      have hle : J' ≤ J0 := heq ▸ le_sup_right
      exact hne (Subgroup.eq_of_le_of_card_ge hle (by rw [hcard, hJ]))
    · exact Subgroup.eq_of_le_of_card_ge hsupT (by rw [hk, hT])
  have h3 := card_inf_le_three hJ' hsup
  have hidxT : J0.relIndex T0 = 3 := by
    have h := Subgroup.card_mul_index (J0.subgroupOf T0)
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe J0_le_T0).toEquiv, hJ, hT] at h
    rw [Subgroup.relIndex]
    omega
  have hidx : J0.relIndex J' ≤ 3 :=
    hidxT ▸ Subgroup.relIndex_le_of_le_right hJ'T (by rw [hidxT]; norm_num)
  have hcardJ' := Subgroup.relIndex_mul_card (H := J0) (K := J')
  rw [hcard] at hcardJ'
  have : 27 ≤ 3 * 3 := by
    calc 27 = J0.relIndex J' * Nat.card ↥(J0 ⊓ J') := hcardJ'.symm
      _ ≤ 3 * 3 := Nat.mul_le_mul hidx h3
  omega

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Omega8Frame
