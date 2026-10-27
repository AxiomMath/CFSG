module

public import CFSG.LocalAnalysis.SectionRank.QTK.Insp443.M22Concl
public import CFSG.LocalAnalysis.SectionRank.QTK.Insp443.M22Cases
public import CFSG.LocalAnalysis.SectionRank.QTK.Insp443.ConclTransport
public import CFSG.LocalAnalysis.SectionRank.QTK.Insp443.Descent
public import CFSG.LocalAnalysis.SectionRank.QTK.Insp443.DescentCover
public import CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator.ProvedRows
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PrimeCardSubgroupIntersection
public import CFSG.Sporadic.J4
public import CFSG.Sporadic.Suz.Simple

public section

namespace CFSG.SectionRank.QTK.Insp443

open Subgroup CFSG.Open CFSG.Quasithin CFSG.Quasithin.H13 CFSG.Quasithin.H13.Ch4
  CFSG.Quasithin.H13.Ch4.E443 CFSG.QuasithinUnique CFSG.Quasithin.KGC31
  CFSG.Quasithin.KGC31.M22 CFSG.Blueprint CFSG.LieType.BorelTits
open scoped IsMulCommutative

private theorem card_center_eq_one_or_three {K X : Type} [Group K] [Finite K] [Group X]
    (hK : CFSG.IsQuasisimple K) (hodd : Odd (Nat.card ↥(Subgroup.center K)))
    (e : K ⧸ Subgroup.center K ≃* X)
    (hM : Nat.card ↥(CFSG.RankThree.PerfectCover.hopfMultiplier X) = 12) :
    Nat.card ↥(Subgroup.center K) = 1 ∨ Nat.card ↥(Subgroup.center K) = 3 := by
  have hdvd : Nat.card ↥(Subgroup.center K) ∣ 12 := by
    have h := CFSG.Quasithin.B69K.OddCovers.card_center_dvd_hopfMultiplier hK.1 e
    rwa [hM] at h
  have hdvd' : Nat.card ↥(Subgroup.center K) ∣ 4 * 3 := by
    rw [show 4 * 3 = 12 by norm_num]
    exact hdvd
  have hcop : Nat.Coprime (Nat.card ↥(Subgroup.center K)) 4 := by
    simpa using hodd.coprime_two_right.pow_right 2
  have hdvd3 : Nat.card ↥(Subgroup.center K) ∣ 3 := hcop.dvd_of_dvd_mul_left hdvd'
  rcases (Nat.dvd_prime Nat.prime_three).mp hdvd3 with h | h
  · exact Or.inl h
  · exact Or.inr h

private theorem isCyclic_sylow_three_of_not_nine_dvd
    {A : Type*} [Group A] [Finite A] (h9 : ¬ 9 ∣ Nat.card A) :
    ∀ S : Sylow 3 A, IsCyclic ↥(S : Subgroup A) := by
  intro S
  have hSdvd : Nat.card ↥(S : Subgroup A) ∣ Nat.card A := by
    simpa using Subgroup.card_dvd_of_le (H := (S : Subgroup A)) (K := ⊤) le_top
  have h9S : ¬ 9 ∣ Nat.card ↥(S : Subgroup A) := fun h => h9 (h.trans hSdvd)
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp S.isPGroup'
  have hnle : n ≤ 1 := by
    by_contra h
    apply h9S
    have h2 : 2 ≤ n := by omega
    rw [hn, show (9 : ℕ) = 3 ^ 2 by norm_num]
    exact pow_dvd_pow 3 h2
  have hn01 : n = 0 ∨ n = 1 := by omega
  rcases hn01 with rfl | rfl
  · have hS1 : Nat.card ↥(S : Subgroup A) = 1 := by simpa using hn
    haveI : Subsingleton ↥(S : Subgroup A) := (Nat.card_eq_one_iff_unique.mp hS1).1
    exact isCyclic_of_subsingleton
  · have hS3 : Nat.card ↥(S : Subgroup A) = 3 := by simpa using hn
    exact isCyclic_of_prime_card (p := 3) hS3

private theorem not_isSporadic_J4_carrier_M22 :
    ¬ IsSporadic .J4 (NativeSporadic.Carrier .M22) := by
  intro hJ
  obtain ⟨e⟩ := hJ
  have h1 : Nat.card (NativeSporadic.Carrier .M22) = Nat.card NativeSporadic.J4 :=
    Nat.card_congr e.toEquiv
  rw [CFSG.Sporadic.J4.card_J4] at h1
  have h2 : Nat.card (NativeSporadic.Carrier .M22) = 443520 := by
    change Nat.card ↥NativeSporadic.M22 = 443520
    exact CFSG.Sporadic.Mathieu.card_M22
  rw [h2] at h1
  norm_num at h1

private theorem inf_center_eq_bot_of_eq_map_of_card {K X : Type} [Group K] [Finite K] [Group X]
    {L V MK : Subgroup K} (hK : KConf K L V MK) (e : K ⧸ Subgroup.center K ≃* X)
    {M' : Subgroup X} (g : X)
    (hL : (L.map (QuotientGroup.mk' (Subgroup.center K))).map e.toMonoidHom =
      M'.map (MulAut.conj g).toMonoidHom)
    (hZcard : Nat.card ↥(Subgroup.center K) = 1 ∨ Nat.card ↥(Subgroup.center K) = 3)
    (N : ℕ) (hcard : Nat.card ↥M' = N) (h9 : ¬ 9 ∣ N) :
    L ⊓ Subgroup.center K = ⊥ := by
  let Z := Subgroup.center K
  let Lb : Subgroup (K ⧸ Z) := L.map (QuotientGroup.mk' Z)
  let Lb' : Subgroup X := Lb.map e.toMonoidHom
  let Q : Type := ↥Lb ⧸ CFSG.pCore 2 ↥Lb
  let Q' : Type := ↥Lb' ⧸ CFSG.pCore 2 ↥Lb'
  let eL : ↥Lb ≃* ↥Lb' := Subgroup.equivMapOfInjective Lb e.toMonoidHom e.injective
  let ψ : Q ≃* Q' :=
    QuotientGroup.congr _ _ eL (CFSG.LieType.BorelTits.map_pCore_mulEquiv 2 eL)
  have hcardLb' : Nat.card ↥Lb' = N := by
    change Nat.card ↥((L.map (QuotientGroup.mk' (Subgroup.center K))).map e.toMonoidHom) = N
    rw [hL, Subgroup.card_map_of_injective (MulAut.conj g).injective, hcard]
  have hQ'dvd : Nat.card Q' ∣ N := by
    have h := Subgroup.card_quotient_dvd_card (CFSG.pCore 2 ↥Lb')
    rwa [hcardLb'] at h
  have hQdvd : Nat.card Q ∣ N := by
    rwa [Nat.card_congr ψ.toEquiv]
  have h9Q : ¬ 9 ∣ Nat.card Q := fun h => h9 (h.trans hQdvd)
  have hcyc : ∀ r : ℕ, r.Prime → r ∣ Nat.card Z →
      ∀ S : Sylow r Q, IsCyclic ↥(S : Subgroup Q) := by
    intro r hr hrdiv S
    rcases hZcard with hZ1 | hZ3
    · exfalso
      rw [hZ1] at hrdiv
      exact hr.not_dvd_one hrdiv
    · rcases (Nat.dvd_prime (p := 3) (m := r) Nat.prime_three).mp (by rwa [hZ3] at hrdiv) with h1 | h3
      · exact absurd h1 hr.ne_one
      · subst r
        exact isCyclic_sylow_three_of_not_nine_dvd h9Q S
  exact hK.inf_center_eq_bot hcyc

private theorem inf_center_eq_bot_of_hexad
    {K : Type} [Group K] [Finite K] {L V MK : Subgroup K}
    (hK : KConf K L V MK) (e : K ⧸ Subgroup.center K ≃* NativeSporadic.Carrier .M22)
    {g : NativeSporadic.Carrier .M22}
    (hL : (L.map (QuotientGroup.mk' (Subgroup.center K))).map e.toMonoidHom =
      Mhex.map (MulAut.conj g).toMonoidHom)
    (hZcard : Nat.card ↥(Subgroup.center K) = 1 ∨ Nat.card ↥(Subgroup.center K) = 3)
    (h3A6 : Nat.card ↥(Subgroup.center K) = 3 →
      ¬ (Group.IsPerfect (↥L ⧸ CFSG.pCore 2 ↥L) ∧
        Nat.card ↥(Subgroup.center (↥L ⧸ CFSG.pCore 2 ↥L)) = 3 ∧
        Nonempty ((↥L ⧸ CFSG.pCore 2 ↥L) ⧸
          Subgroup.center (↥L ⧸ CFSG.pCore 2 ↥L) ≃* alternatingGroup (Fin 6)))) :
    L ⊓ Subgroup.center K = ⊥ := by
  rcases hZcard with hZ1 | hZ3
  · have hZbot : Subgroup.center K = ⊥ := Subgroup.card_eq_one.mp hZ1
    rw [hZbot, inf_bot_eq]
  · by_cases hZL : Subgroup.center K ≤ L
    · exfalso
      let Z := Subgroup.center K
      let Lb : Subgroup (K ⧸ Z) := L.map (QuotientGroup.mk' Z)
      let Lb' : Subgroup (NativeSporadic.Carrier .M22) := Lb.map e.toMonoidHom
      let Q : Type := ↥Lb ⧸ CFSG.pCore 2 ↥Lb
      let eL : ↥Lb ≃* ↥Lb' := Subgroup.equivMapOfInjective Lb e.toMonoidHom e.injective
      let ψ1 : Q ≃* (↥Lb' ⧸ CFSG.pCore 2 ↥Lb') :=
        QuotientGroup.congr _ _ eL (CFSG.LieType.BorelTits.map_pCore_mulEquiv 2 eL)
      let e2 : ↥Lb' ≃* ↥(Mhex.map (MulAut.conj g).toMonoidHom) :=
        MulEquiv.subgroupCongr hL
      let ψ2 : (↥Lb' ⧸ CFSG.pCore 2 ↥Lb') ≃*
          (↥(Mhex.map (MulAut.conj g).toMonoidHom) ⧸
            CFSG.pCore 2 ↥(Mhex.map (MulAut.conj g).toMonoidHom)) :=
        QuotientGroup.congr _ _ e2 (CFSG.LieType.BorelTits.map_pCore_mulEquiv 2 e2)
      let econj : ↥Mhex ≃* ↥(Mhex.map (MulAut.conj g).toMonoidHom) :=
        Subgroup.equivMapOfInjective Mhex (MulAut.conj g).toMonoidHom
          (MulAut.conj g).injective
      let ψ3 : (↥(Mhex.map (MulAut.conj g).toMonoidHom) ⧸
            CFSG.pCore 2 ↥(Mhex.map (MulAut.conj g).toMonoidHom)) ≃*
          (↥Mhex ⧸ CFSG.pCore 2 ↥Mhex) :=
        (QuotientGroup.congr _ _ econj (CFSG.LieType.BorelTits.map_pCore_mulEquiv 2 econj)).symm
      obtain ⟨eQ⟩ := nonempty_Mhex_quot_mulEquiv
      let φ : Q ≃* alternatingGroup (Fin 6) := ψ1.trans (ψ2.trans (ψ3.trans eQ))
      have hcenterQ : Subgroup.center Q = ⊥ :=
        CFSG.Quasithin.F420.center_eq_bot_of_mulEquiv' φ
          (alternatingGroup.center_eq_bot (by norm_num))
      have hperf : Group.IsPerfect (↥L ⧸ CFSG.pCore 2 ↥L) := by
        letI : Group.IsPerfect ↥L := Subgroup.isPerfect_iff.mpr hK.perfect
        exact Group.IsPerfect.ofSurjective (QuotientGroup.mk'_surjective (CFSG.pCore 2 ↥L))
      obtain ⟨hcardC, ⟨eC⟩⟩ :=
        CFSG.SectionRank.QTK.Insp443.center_quot_pCore_of_le (K := K) (Z := Z) (L := L)
          le_rfl hK.odd_card_center hZL hcenterQ
      refine h3A6 hZ3 ⟨hperf, ?_, ⟨eC.trans φ⟩⟩
      rw [hcardC, hZ3]
    · exact CFSG.GorensteinWalter.inf_eq_bot_of_not_le_of_prime_card L (Subgroup.center K)
        (by rw [hZ3]; exact Nat.prime_three) hZL

theorem conclK_M22
    {L V MK : Subgroup (NativeSporadic.Carrier .M22)}
    (h : KConfig (NativeSporadic.Carrier .M22) L V MK) :
    ConclK (NativeSporadic.Carrier .M22) L V MK := by
  haveI : Finite (NativeSporadic.Carrier .M22) := by
    change Finite ↥NativeSporadic.M22
    infer_instance
  obtain ⟨g, hg | hg | hg⟩ := KConfig.m22_cases h
  · exact KConfig.conclK_of_eq_map h (MulAut.conj g) hg.1 hg.2
      (fun MK' => conclK_m22_hex MK')
  · exact KConfig.conclK_of_eq_map h (MulAut.conj g) hg.1 hg.2
      (fun MK' => conclK_m22_duad MK')
  · exact KConfig.conclK_of_eq_map h (MulAut.conj g) hg.1 hg.2
      (fun MK' => conclK_m22_e8 MK')

theorem KConf.conclK_M22
    {K : Type} [Group K] [Finite K] {L V MK : Subgroup K} (hK : KConf K L V MK)
    (e : K ⧸ Subgroup.center K ≃* NativeSporadic.Carrier .M22)
    (h3A6 : Nat.card ↥(Subgroup.center K) = 3 →
      ¬ (Group.IsPerfect (↥L ⧸ CFSG.pCore 2 ↥L) ∧
        Nat.card ↥(Subgroup.center (↥L ⧸ CFSG.pCore 2 ↥L)) = 3 ∧
        Nonempty ((↥L ⧸ CFSG.pCore 2 ↥L) ⧸
          Subgroup.center (↥L ⧸ CFSG.pCore 2 ↥L) ≃* alternatingGroup (Fin 6)))) :
    ConclK K L V MK := by
  let Z := Subgroup.center K
  let Lb : Subgroup (K ⧸ Z) := L.map (QuotientGroup.mk' Z)
  let Lb' : Subgroup (NativeSporadic.Carrier .M22) := Lb.map e.toMonoidHom
  have hZcard : Nat.card ↥Z = 1 ∨ Nat.card ↥Z = 3 := by
    refine card_center_eq_one_or_three hK.quasisimple hK.odd_card_center e ?_
    rw [CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator.nativeRow_M22]
    rfl
  have hJ4 : IsSporadic .J4 (NativeSporadic.Carrier .M22) → Z = ⊥ :=
    fun hJ => (not_isSporadic_J4_carrier_M22 hJ).elim
  have hLZ : L ⊓ Z = ⊥ := by
    obtain ⟨g, hg | hg | hg⟩ := KConfig.m22_cases (hK.kConfig_bar.map_mulEquiv e)
    · exact inf_center_eq_bot_of_hexad hK e hg.2 hZcard h3A6
    · exact inf_center_eq_bot_of_eq_map_of_card hK e g hg.2 hZcard 960
        card_Mduad (by norm_num)
    · exact inf_center_eq_bot_of_eq_map_of_card hK e g hg.2 hZcard 1344
        card_eNorm_e8 (by norm_num)
  exact hK.conclK_of_mulEquiv e
    (fun L V MK h => CFSG.SectionRank.QTK.Insp443.conclK_M22 h) hLZ hJ4

end CFSG.SectionRank.QTK.Insp443

end
