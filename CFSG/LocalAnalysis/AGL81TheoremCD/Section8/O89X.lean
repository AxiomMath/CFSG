module

public import CFSG.LocalAnalysis.AGL81TheoremCD.Section8.KFact76RankThree
public import CFSG.Goldschmidt.Steps.Sec8Tools
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15R1511C
import CFSG.GroupTheory.PCore.PrimeSetCore
import CFSG.LocalAnalysis.GLTheoremB.ComponentTools
import CFSG.LocalAnalysis.GLTheoremB.PQuotientTools
import CFSG.LocalAnalysis.GLTheoremB.SchreierTools
import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.K2.Quotient
import CFSG.Quasithin.EmptyFaithful.SBc17Ent1
import CFSG.Timmesfeld.RankOne.Quotient

public section

namespace CFSG.LocalAnalysis.AGL81TheoremCD.Section8

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC.S15

variable {G : Type} [Group G] [Finite G]

@[expose] def quotientImagePPrimeCore (H A : Subgroup G) :
    Subgroup (↥H ⧸ CFSG.pPrimeCore 3 ↥H) :=
  (A.subgroupOf H).map (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥H))

section WeakClosure

variable {H : Type*} [Group H] [Finite H]

private theorem card_sup_prime_of_coprime {A I : Subgroup H} (hI : I.Normal)
    (hA3 : Nat.card A = 3) (hAI : A ⊓ I = ⊥) :
    Nat.card ↥(A ⊔ I) = 3 * Nat.card I := by
  have hrel : I.relIndex A = 3 := by
    have h := Subgroup.relIndex_mul_card (H := I) (K := A)
    rw [inf_comm, hAI, Subgroup.card_bot, mul_one, hA3] at h
    exact h
  have h := Subgroup.relIndex_mul_card (H := I) (K := I ⊔ A)
  rw [inf_of_le_left le_sup_left, Subgroup.relIndex_sup_left, hrel] at h
  rw [sup_comm]
  exact h.symm

private theorem factorization_three_card_sup {A I : Subgroup H} (hI : I.Normal)
    (hI3 : Nat.Coprime 3 (Nat.card I)) (hA3 : Nat.card A = 3) (hAI : A ⊓ I = ⊥) :
    (Nat.card ↥(A ⊔ I)).factorization 3 = 1 := by
  have hm : Nat.card I ≠ 0 := Nat.card_pos.ne'
  rw [card_sup_prime_of_coprime hI hA3 hAI,
    Nat.factorization_mul (by norm_num : (3 : ℕ) ≠ 0) hm, Finsupp.add_apply,
    Nat.prime_three.factorization_self,
    Nat.factorization_eq_zero_of_not_dvd
      ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp hI3), add_zero]

private theorem sup_eq_of_le_sup_of_weaklyClosed {A N I : Subgroup H} (hI : I.Normal)
    (hI3 : Nat.Coprime 3 (Nat.card I)) (hA3 : Nat.card A = 3) (hAI : A ⊓ I = ⊥)
    (hweak : ∀ g : H, A.map (MulAut.conj g).toMonoidHom ≤ N →
      A.map (MulAut.conj g).toMonoidHom = A)
    {g : H} (hg : A.map (MulAut.conj g).toMonoidHom ≤ I ⊔ N) :
    A.map (MulAut.conj g).toMonoidHom ⊔ I = A ⊔ I := by
  classical
  haveI : I.Normal := hI
  set B : Subgroup H := A.map (MulAut.conj g).toMonoidHom with hBdef
  have hB3 : Nat.card B = 3 := by
    rw [Subgroup.card_map_of_injective (MulAut.conj g).injective, hA3]
  have hBI : B ⊓ I = ⊥ :=
    (Subgroup.disjoint_of_coprime_natCard (H := B) (K := I) (by
      rw [hB3]; exact hI3)).eq_bot
  have hYcard : Nat.card ↥(B ⊔ I) = 3 * Nat.card I :=
    card_sup_prime_of_coprime hI hB3 hBI
  set C : Subgroup H := (B ⊔ I) ⊓ N with hCdef
  have hYC : B ⊔ I = I ⊔ C := by
    refine le_antisymm ?_ (sup_le le_sup_right inf_le_left)
    refine sup_le ?_ le_sup_left
    intro b hb
    obtain ⟨i, hi, n, hn, hbe⟩ :=
      (Subgroup.mem_sup_of_normal_left (s := I) (t := N)).mp (hg hb)
    have hnY : n ∈ B ⊔ I := by
      have h' : i⁻¹ * b ∈ B ⊔ I :=
        (B ⊔ I).mul_mem ((B ⊔ I).inv_mem ((le_sup_right : I ≤ B ⊔ I) hi))
          ((le_sup_left : B ≤ B ⊔ I) hb)
      rwa [← hbe, ← mul_assoc, inv_mul_cancel, one_mul] at h'
    exact (Subgroup.mem_sup_of_normal_left (s := I) (t := C)).mpr
      ⟨i, hi, n, ⟨hnY, hn⟩, hbe⟩
  have hIC : I.relIndex C = 3 := by
    have h1 : Nat.card ↥(I ⊔ C) = 3 * Nat.card I := by rw [← hYC, hYcard]
    have h2 := Subgroup.relIndex_mul_card (H := I) (K := I ⊔ C)
    rw [inf_of_le_left le_sup_left, Subgroup.relIndex_sup_left, h1] at h2
    exact Nat.eq_of_mul_eq_mul_right Nat.card_pos h2
  have hCcard : Nat.card C = 3 * Nat.card ↥(I ⊓ C) := by
    have h := Subgroup.relIndex_mul_card (H := I) (K := C)
    rw [hIC] at h
    exact h.symm
  have hCI3 : ¬ 3 ∣ Nat.card ↥(I ⊓ C) := fun h =>
    (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp hI3
      (h.trans (Subgroup.card_dvd_of_le (H := I ⊓ C) (K := I) inf_le_left))
  have hfacC : (Nat.card C).factorization 3 = 1 := by
    rw [hCcard, Nat.factorization_mul (by norm_num : (3 : ℕ) ≠ 0) Nat.card_pos.ne',
      Finsupp.add_apply, Nat.prime_three.factorization_self,
      Nat.factorization_eq_zero_of_not_dvd hCI3, add_zero]
  obtain ⟨S, hS⟩ := CFSG.ABGLocalTools.exists_isSylowOf 3 C
  have hS3 : Nat.card S = 3 := by
    rw [hS.card_eq, hfacC, pow_one]
  have hSle : S ≤ C := hS.le
  have hSN : S ≤ N := hSle.trans inf_le_right
  have hSI : S ⊓ I = ⊥ :=
    (Subgroup.disjoint_of_coprime_natCard (H := S) (K := I) (by
      rw [hS3]; exact hI3)).eq_bot
  have hSYC : S ⊔ I = B ⊔ I := by
    refine Subgroup.eq_of_le_of_card_ge (sup_le (hSle.trans inf_le_left) le_sup_right) ?_
    rw [card_sup_prime_of_coprime hI hS3 hSI, hYcard]
  have hfacY : (Nat.card ↥(B ⊔ I)).factorization 3 = 1 :=
    factorization_three_card_sup hI hI3 hB3 hBI
  have hYsylS : CFSG.ABGLocalTools.IsSylowOf 3 S (B ⊔ I) := by
    refine CFSG.ABGLocalTools.isSylowOf_of_card ?_ ?_
    · rw [← hSYC]; exact le_sup_left
    · rw [hS3, hfacY, pow_one]
  have hYsylB : CFSG.ABGLocalTools.IsSylowOf 3 B (B ⊔ I) := by
    refine CFSG.ABGLocalTools.isSylowOf_of_card le_sup_left ?_
    rw [hB3, hfacY, pow_one]
  obtain ⟨y, -, hy⟩ := hYsylB.exists_mem_conj hYsylS
  have hconj : S = B.map (MulAut.conj y).toMonoidHom := by
    refine Subgroup.eq_of_le_of_card_ge ?_ ?_
    · intro s hs
      refine Subgroup.mem_map.mpr ⟨y⁻¹ * s * y, (hy s).mp hs, ?_⟩
      show y * (y⁻¹ * s * y) * y⁻¹ = s
      group
    · rw [Subgroup.card_map_of_injective (MulAut.conj y).injective, hB3, hS3]
  have hBA : S = A.map (MulAut.conj (y * g)).toMonoidHom := by
    rw [hconj, Subgroup.map_map]
    congr 1
    ext x
    simp [MulAut.conj_apply, mul_assoc]
  have hweakS : S = A := by
    have h' := hweak (y * g) (hBA ▸ hSN)
    rwa [← hBA] at h' 
  rw [← hSYC, hweakS]

end WeakClosure

private theorem normalClosureIn_subgroupOf_normal (L A : Subgroup G) :
    ((CFSG.Goldschmidt.normalClosureIn L A).subgroupOf L).Normal :=
  (Subgroup.normal_subgroupOf_iff_le_normalizer
    (CFSG.Goldschmidt.Sec8.normalClosureIn_le_self L A)).mpr
    (CFSG.Goldschmidt.Sec8.le_normalizer_normalClosureIn L A)

private theorem sup_pPrimeCore_eq_top_of_normalClosure {M H L A : Subgroup G}
    (h : Hyp83 M H L A) (hL : IsLThreeTwoPow (↥L ⧸ CFSG.pPrimeCore 3 ↥L)) :
    (CFSG.Goldschmidt.normalClosureIn L A).subgroupOf L ⊔
      CFSG.pPrimeCore 3 ↥L = ⊤ := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let J : Subgroup ↥L := (CFSG.Goldschmidt.normalClosureIn L A).subgroupOf L
  let O : Subgroup ↥L := CFSG.pPrimeCore 3 ↥L
  let θ : ↥L →* (↥L ⧸ O) := QuotientGroup.mk' O
  let A_L : Subgroup ↥L := A.subgroupOf L
  have hJnorm : J.Normal := normalClosureIn_subgroupOf_normal L A
  have hA_L_card : Nat.card A_L = 3 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe h.le_L).toEquiv, h.card]
  have hA_L_le_J : A_L ≤ J := by
    intro x hx
    exact Subgroup.mem_subgroupOf.mpr
      (CFSG.Goldschmidt.Sec8.le_normalClosureIn h.le_L (Subgroup.mem_subgroupOf.mp hx))
  have hAq_ne : A_L.map θ ≠ ⊥ := by
    intro hbot
    have hle : A_L ≤ O := by
      have hker : A_L ≤ θ.ker := (Subgroup.map_eq_bot_iff A_L).mp hbot
      rwa [QuotientGroup.ker_mk'] at hker
    have hdisj : A_L ⊓ O = ⊥ :=
      (Subgroup.disjoint_of_coprime_natCard (H := A_L) (K := O) (by
        rw [hA_L_card]; exact CFSG.pPrimeCore_coprime_card)).eq_bot
    have hcard : Nat.card A_L = 1 := by
      rw [← inf_eq_left.mpr hle, hdisj, Subgroup.card_bot]
    omega
  have hJq_normal : (J.map θ).Normal :=
    Subgroup.Normal.map hJnorm θ (QuotientGroup.mk'_surjective O)
  have hJq_ne : J.map θ ≠ ⊥ := by
    intro hbot
    have hle : A_L.map θ ≤ J.map θ := Subgroup.map_mono hA_L_le_J
    rw [hbot] at hle
    exact hAq_ne (le_bot_iff.mp hle)
  have hJq_top : J.map θ = ⊤ := by
    haveI : IsSimpleGroup (↥L ⧸ O) :=
      CFSG.LocalAnalysis.RankThreeUC.S15.R1511C.isSimpleGroup_of_isLThreeTwoPow hL
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (J.map θ) with hbot | htop
    · exact absurd hbot hJq_ne
    · exact htop
  have hJKmap : (J ⊔ O).map θ = ⊤ := by
    rw [Subgroup.map_sup, hJq_top, QuotientGroup.map_mk'_self, sup_bot_eq]
  have hker_le : θ.ker ≤ J ⊔ O := by
    rw [QuotientGroup.ker_mk']
    exact le_sup_right
  have h := Subgroup.comap_map_eq_self (f := θ) hker_le
  rw [hJKmap] at h
  simpa using h.symm

private theorem coprime_index_normalClosure {M H L A : Subgroup G} (h : Hyp83 M H L A)
    (hJO : (CFSG.Goldschmidt.normalClosureIn L A).subgroupOf L ⊔
      CFSG.pPrimeCore 3 ↥L = ⊤) :
    Nat.Coprime 3 ((CFSG.Goldschmidt.normalClosureIn L A).subgroupOf L).index := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let J : Subgroup ↥L := (CFSG.Goldschmidt.normalClosureIn L A).subgroupOf L
  let O : Subgroup ↥L := CFSG.pPrimeCore 3 ↥L
  have hJnorm : J.Normal := normalClosureIn_subgroupOf_normal L A
  haveI : J.Normal := hJnorm
  let ψ : ↥O →* (↥L ⧸ J) := (QuotientGroup.mk' J).comp O.subtype
  have hψ : Function.Surjective ψ := by
    intro y
    obtain ⟨l, rfl⟩ := QuotientGroup.mk'_surjective J y
    have hl : l ∈ J ⊔ O := by rw [hJO]; exact Subgroup.mem_top l
    obtain ⟨j, hj, o, ho, hjo⟩ := (Subgroup.mem_sup_of_normal_left (s := J) (t := O)).mp hl
    refine ⟨⟨o, ho⟩, ?_⟩
    have hjmk : QuotientGroup.mk' J j = 1 := (QuotientGroup.eq_one_iff j).mpr hj
    calc ψ ⟨o, ho⟩ = QuotientGroup.mk' J (o : ↥L) := rfl
      _ = QuotientGroup.mk' J l := by
          rw [← hjo, map_mul, hjmk, one_mul]
  have hdvd : Nat.card (↥L ⧸ J) ∣ Nat.card ↥O := Subgroup.card_dvd_of_surjective hψ
  have hcop : Nat.Coprime 3 (Nat.card ↥O) := CFSG.pPrimeCore_coprime_card
  rw [Subgroup.index_eq_card]
  exact Nat.Coprime.of_dvd_right hdvd hcop

private theorem normalClosureIn_eq_of_isLThreeTwoPow {M H L A : Subgroup G}
    (h : Hyp83 M H L A) (hL : IsLThreeTwoPow (↥L ⧸ CFSG.pPrimeCore 3 ↥L)) :
    CFSG.Goldschmidt.normalClosureIn L A = L := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let J : Subgroup ↥L := (CFSG.Goldschmidt.normalClosureIn L A).subgroupOf L
  have hJnorm : J.Normal := normalClosureIn_subgroupOf_normal L A
  have hJO : J ⊔ CFSG.pPrimeCore 3 ↥L = ⊤ := sup_pPrimeCore_eq_top_of_normalClosure h hL
  have hcop : Nat.Coprime 3 J.index := coprime_index_normalClosure h hJO
  have hres : CFSG.ComponentClassification.CatalogueBPrimeJoin.primeResidual 3 ↥L = ⊤ :=
    CFSG.ComponentClassification.CatalogueBPrimeJoin.primeResidual_eq_top_of_equiv 3
      (Subgroup.subgroupOfEquivOfLe h.le)
      (CFSG.ComponentClassification.CatalogueBPrimeJoin.primeResidual_eq_top_of_pComponent 3
        (L.subgroupOf (H ⊓ M)) h.comp)
  have htop : J = ⊤ := by
    haveI : J.Normal := hJnorm
    have hle :=
      CFSG.ComponentClassification.CatalogueBPrimeJoin.primeResidual_le_normal_of_coprime_index
        (p := 3) J hcop
    rw [hres] at hle
    exact top_le_iff.mp hle
  have hmap := congrArg (Subgroup.map L.subtype) htop
  simp only [J] at hmap
  rw [Subgroup.map_subgroupOf_eq_of_le
    (CFSG.Goldschmidt.Sec8.normalClosureIn_le_self L A)] at hmap
  simpa [Subgroup.map_top, Subgroup.range_subtype] using hmap

theorem le_normalClosure_of_isPComponent {M H L A : Subgroup G} (h : Hyp83 M H L A)
    (hL : IsLThreeTwoPow (↥L ⧸ CFSG.pPrimeCore 3 ↥L)) :
    L ≤ CFSG.Goldschmidt.normalClosureIn H A := by
  have hgen : CFSG.Goldschmidt.normalClosureIn L A = L :=
    normalClosureIn_eq_of_isLThreeTwoPow h hL
  let K : Subgroup G := CFSG.Goldschmidt.normalClosureIn H A
  have hLH : L ≤ H := h.le.trans inf_le_left
  have hAL : A ≤ L := h.le_L
  have hAK : A ≤ K := CFSG.Goldschmidt.Sec8.le_normalClosureIn (hAL.trans hLH)
  have hKL : L ≤ Subgroup.normalizer (K : Set G) :=
    hLH.trans (CFSG.Goldschmidt.Sec8.le_normalizer_normalClosureIn H A)
  have hnorm : L ≤ Subgroup.normalizer ((K ⊓ L : Subgroup G) : Set G) := by
    intro l hl
    rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · rintro ⟨hxK, hxL⟩
      exact ⟨(Subgroup.mem_normalizer_iff.mp (hKL hl) x).mp hxK,
        L.mul_mem (L.mul_mem hl hxL) (L.inv_mem hl)⟩
    · rintro ⟨hxK, hxL⟩
      refine ⟨(Subgroup.mem_normalizer_iff.mp (hKL hl) x).mpr hxK, ?_⟩
      have h' := L.mul_mem (L.mul_mem (L.inv_mem hl) hxL) hl
      simpa [mul_assoc] using h'
  have hgenK : CFSG.Goldschmidt.normalClosureIn L A ≤ K ⊓ L :=
    CFSG.Goldschmidt.Sec8.normalClosureIn_le inf_le_right hnorm
      (le_inf (inf_le_left.trans hAK) inf_le_right)
  calc L = CFSG.Goldschmidt.normalClosureIn L A := hgen.symm
    _ ≤ K := hgenK.trans inf_le_left

theorem normalizer_le_of_hyp83 {M H L A : Subgroup G}
    (hM : CFSG.Open.rankThreeIsMaxTwoLocal M) (h : Hyp83 M H L A) :
    Subgroup.normalizer (A : Set G) ≤ M :=
  CFSG.LocalAnalysis.RankThreeUC.normalizer_le_of_mem_uniqueSet hM h.unique

private theorem weaklyClosed_normalizer_of_hyp83 {M H L A : Subgroup G}
    (hM : CFSG.Open.rankThreeIsMaxTwoLocal M) (h : Hyp83 M H L A) :
    ∀ g ∈ H, A.map (MulAut.conj g).toMonoidHom ≤ Subgroup.normalizer (A : Set G) →
      A.map (MulAut.conj g).toMonoidHom = A := by
  intro g hgH hgN
  have hA_le_H : A ≤ H := h.le_L.trans (h.le.trans inf_le_left)
  have hgH' : A.map (MulAut.conj g).toMonoidHom ≤ H := by
    rintro _ ⟨a, ha, rfl⟩
    exact H.mul_mem (H.mul_mem hgH (hA_le_H ha)) (H.inv_mem hgH)
  exact h.weak g hgH (le_inf hgN (le_inf hgH' (hgN.trans (normalizer_le_of_hyp83 hM h))))

theorem weaklyClosed_quotient_pPrimeCore {M H L A : Subgroup G}
    (hM : CFSG.Open.rankThreeIsMaxTwoLocal M) (h : Hyp83 M H L A) :
    Nat.card (quotientImagePPrimeCore H A) = 3 ∧
    Subgroup.normalizer (quotientImagePPrimeCore H A :
        Set (↥H ⧸ CFSG.pPrimeCore 3 ↥H)) =
      ((Subgroup.normalizer (A : Set G)).subgroupOf H).map
        (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥H)) ∧
    (∀ g : ↥H ⧸ CFSG.pPrimeCore 3 ↥H,
      (quotientImagePPrimeCore H A).map (MulAut.conj g).toMonoidHom ≤
        Subgroup.normalizer (quotientImagePPrimeCore H A :
          Set (↥H ⧸ CFSG.pPrimeCore 3 ↥H)) →
      (quotientImagePPrimeCore H A).map (MulAut.conj g).toMonoidHom =
        quotientImagePPrimeCore H A) := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let I : Subgroup ↥H := CFSG.pPrimeCore 3 ↥H
  let A_H : Subgroup ↥H := A.subgroupOf H
  let N_H : Subgroup ↥H := (Subgroup.normalizer (A : Set G)).subgroupOf H
  have hA_le_H : A ≤ H := h.le_L.trans (h.le.trans inf_le_left)
  have hI3 : Nat.Coprime 3 (Nat.card I) := CFSG.pPrimeCore_coprime_card
  have hAH3 : Nat.card A_H = 3 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hA_le_H).toEquiv, h.card]
  have hAHI : A_H ⊓ I = ⊥ :=
    (Subgroup.disjoint_of_coprime_natCard (H := A_H) (K := I) (by
      rw [hAH3]; exact hI3)).eq_bot
  have hcard : Nat.card (quotientImagePPrimeCore H A) = 3 := by
    have hdiv : Nat.card (quotientImagePPrimeCore H A) ∣ 3 := by
      have := Subgroup.card_map_dvd (H := A_H) (f := QuotientGroup.mk' I)
      rwa [hAH3] at this
    have hne : quotientImagePPrimeCore H A ≠ ⊥ := by
      intro hbot
      have hle : A_H ≤ I := by
        have := (Subgroup.map_eq_bot_iff (f := QuotientGroup.mk' I) (H := A_H)).mp hbot
        rwa [QuotientGroup.ker_mk'] at this
      have hbot2 : A_H ⊓ I = A_H := inf_eq_left.mpr hle
      have h1 : Nat.card A_H = 1 := by rw [← hbot2, hAHI]; exact Subgroup.card_bot
      omega
    have hlt : 1 < Nat.card (quotientImagePPrimeCore H A) :=
      (Subgroup.one_lt_card_iff_ne_bot _).mpr hne
    rcases (Nat.dvd_prime Nat.prime_three).mp hdiv with h1 | h3
    · omega
    · exact h3
  have hnorm : Subgroup.normalizer (quotientImagePPrimeCore H A :
      Set (↥H ⧸ CFSG.pPrimeCore 3 ↥H)) =
      ((Subgroup.normalizer (A : Set G)).subgroupOf H).map
        (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥H)) := by
    have hAHp : IsPGroup 3 A_H := IsPGroup.of_card (n := 1) (by rw [hAH3]; norm_num)
    have h := CFSG.GroupTheory.normal_coprime_quotient_normalizer 3 I
      ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp hI3) A_H hAHp
    rw [← Subgroup.subgroupOf_normalizer_eq hA_le_H] at h
    exact h.symm
  refine ⟨hcard, hnorm, ?_⟩
  intro g hg
  obtain ⟨hH, rfl⟩ := QuotientGroup.mk'_surjective I g
  have hweak : ∀ k : ↥H, A_H.map (MulAut.conj k).toMonoidHom ≤ N_H →
      A_H.map (MulAut.conj k).toMonoidHom = A_H := by
    intro k hk
    have h2 : (A_H.map (MulAut.conj k).toMonoidHom).map H.subtype =
        A.map (MulAut.conj (k : G)).toMonoidHom := by
      rw [← Subgroup.map_subgroupOf_eq_of_le hA_le_H]
      rw [Subgroup.map_map, Subgroup.map_map]
      congr 1
    have hkG : A.map (MulAut.conj (k : G)).toMonoidHom ≤
        Subgroup.normalizer (A : Set G) := by
      have h1 : (A_H.map (MulAut.conj k).toMonoidHom).map H.subtype ≤
          N_H.map H.subtype := Subgroup.map_mono hk
      have h3 : N_H.map H.subtype ≤ Subgroup.normalizer (A : Set G) := by
        rintro x ⟨y, hy, rfl⟩
        exact hy
      rw [h2] at h1
      exact h1.trans h3
    have hk_eq := weaklyClosed_normalizer_of_hyp83 hM h (k : G) k.2 hkG
    refine Subgroup.map_injective (f := H.subtype) H.subtype_injective ?_
    rw [h2, Subgroup.map_subgroupOf_eq_of_le hA_le_H]
    exact hk_eq
  have hIN : (I ⊔ N_H).map (QuotientGroup.mk' I) = N_H.map (QuotientGroup.mk' I) := by
    rw [Subgroup.map_sup, QuotientGroup.map_mk'_self, bot_sup_eq]
  have himg : (A_H.map (MulAut.conj hH).toMonoidHom).map (QuotientGroup.mk' I) ≤
      (I ⊔ N_H).map (QuotientGroup.mk' I) := by
    intro z hz
    obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp hz
    obtain ⟨a, ha, rfl⟩ := Subgroup.mem_map.mp hx
    have hxq : (QuotientGroup.mk' I) ((MulAut.conj hH).toMonoidHom a) ∈
        (quotientImagePPrimeCore H A).map
          (MulAut.conj (QuotientGroup.mk' I hH)).toMonoidHom := by
      refine Subgroup.mem_map.mpr ⟨(QuotientGroup.mk' I) a, ?_, ?_⟩
      · exact Subgroup.mem_map.mpr ⟨a, ha, rfl⟩
      · simp [MulAut.conj_apply, map_mul, map_inv]
    have hxN := hg hxq
    rw [hnorm] at hxN
    rwa [← hIN] at hxN
  have hB : A_H.map (MulAut.conj hH).toMonoidHom ≤ I ⊔ N_H := by
    have hpre : A_H.map (MulAut.conj hH).toMonoidHom ≤
        ((I ⊔ N_H).map (QuotientGroup.mk' I)).comap (QuotientGroup.mk' I) := by
      rw [← Subgroup.map_le_iff_le_comap]
      exact himg
    have hcomap : ((I ⊔ N_H).map (QuotientGroup.mk' I)).comap (QuotientGroup.mk' I) ≤
        I ⊔ N_H := by
      rw [Subgroup.comap_map_eq, QuotientGroup.ker_mk', sup_comm (I ⊔ N_H) I,
        ← sup_assoc, sup_idem]
    exact hpre.trans hcomap
  have hsup := sup_eq_of_le_sup_of_weaklyClosed (N := N_H) (I := I)
    CFSG.pPrimeCore_normal hI3 hAH3 hAHI hweak hB
  have hcomp : (QuotientGroup.mk' I).comp (MulAut.conj hH).toMonoidHom =
      (MulAut.conj (QuotientGroup.mk' I hH)).toMonoidHom.comp (QuotientGroup.mk' I) := by
    ext x
    simp [MulAut.conj_apply, mul_assoc]
  have hmap : (A_H.map (MulAut.conj hH).toMonoidHom).map (QuotientGroup.mk' I) =
      (quotientImagePPrimeCore H A).map
        (MulAut.conj (QuotientGroup.mk' I hH)).toMonoidHom := by
    calc (A_H.map (MulAut.conj hH).toMonoidHom).map (QuotientGroup.mk' I)
        = A_H.map ((QuotientGroup.mk' I).comp (MulAut.conj hH).toMonoidHom) := by
            rw [Subgroup.map_map]
      _ = A_H.map ((MulAut.conj (QuotientGroup.mk' I hH)).toMonoidHom.comp
            (QuotientGroup.mk' I)) := by rw [hcomp]
      _ = (A_H.map (QuotientGroup.mk' I)).map
            (MulAut.conj (QuotientGroup.mk' I hH)).toMonoidHom := by
            rw [Subgroup.map_map]
      _ = (quotientImagePPrimeCore H A).map
            (MulAut.conj (QuotientGroup.mk' I hH)).toMonoidHom := rfl
  have hπ := congrArg (fun K : Subgroup ↥H => K.map (QuotientGroup.mk' I)) hsup
  rw [Subgroup.map_sup, Subgroup.map_sup, QuotientGroup.map_mk'_self, sup_bot_eq, hmap] at hπ
  simpa [quotientImagePPrimeCore] using hπ

private theorem forall_conj_le_sup_pPrimeCore_of_le_normalizer {M H L A : Subgroup G}
    (h : Hyp83 M H L A)
    (hle : (L.subgroupOf H).map (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥H)) ≤
        Subgroup.normalizer (quotientImagePPrimeCore H A :
          Set (↥H ⧸ CFSG.pPrimeCore 3 ↥H))) :
    ∀ l : ↥L, (A.subgroupOf L).map (MulAut.conj l).toMonoidHom ≤
      A.subgroupOf L ⊔ CFSG.pPrimeCore 3 ↥L := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let I : Subgroup ↥H := CFSG.pPrimeCore 3 ↥H
  let π : ↥H →* (↥H ⧸ I) := QuotientGroup.mk' I
  let A_L : Subgroup ↥L := A.subgroupOf L
  let O : Subgroup ↥L := CFSG.pPrimeCore 3 ↥L
  have hLH : L ≤ H := h.le.trans inf_le_left
  let φ : ↥L →* (↥H ⧸ I) := π.comp (Subgroup.inclusion hLH)
  have hmap_incl : A_L.map (Subgroup.inclusion hLH) = A.subgroupOf H := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact hy
    · intro hx
      exact ⟨⟨(x : G), h.le_L hx⟩, hx, rfl⟩
  have hAstar : A_L.map φ = quotientImagePPrimeCore H A := by
    rw [quotientImagePPrimeCore]
    change A_L.map (π.comp (Subgroup.inclusion hLH)) = (A.subgroupOf H).map π
    rw [← Subgroup.map_map, hmap_incl]
  intro l
  have hmem : φ l ∈ (L.subgroupOf H).map π :=
    Subgroup.mem_map_of_mem π (Subgroup.mem_subgroupOf.mpr l.2)
  have hnorm : φ l ∈ Subgroup.normalizer ((A_L.map φ : Subgroup _) : Set _) := by
    simpa [hAstar] using hle hmem
  have h1 : (A_L.map (MulAut.conj l).toMonoidHom).map φ ≤ A_L.map φ :=
    (CFSG.Timmesfeld.RankOne.map_map_conj φ A_L l).le.trans
      (le_of_eq (Subgroup.mem_normalizer_iff_map_conj_eq.mp hnorm))
  have hle_comap : A_L.map (MulAut.conj l).toMonoidHom ≤ (A_L.map φ).comap φ :=
    Subgroup.map_le_iff_le_comap.mp h1
  have hker : φ.ker ≤ O := by
    have hker_eq : φ.ker = I.comap (Subgroup.inclusion hLH) := by
      ext x
      change π (Subgroup.inclusion hLH x) = 1 ↔ Subgroup.inclusion hLH x ∈ I
      exact QuotientGroup.eq_one_iff _
    have hdvd : Nat.card ↥(I.comap (Subgroup.inclusion hLH)) ∣ Nat.card ↥I :=
      Subgroup.card_comap_dvd_of_injective I (Subgroup.inclusion hLH)
        (Subgroup.inclusion_injective hLH)
    have hnot3 : ¬ 3 ∣ Nat.card ↥φ.ker := by
      rw [hker_eq]
      intro h3
      exact CFSG.LocalAnalysis.RankThreeUC.S15.R1511C.not_dvd_card_pPrimeCore ↥H
        (h3.trans hdvd)
    exact CFSG.LocalAnalysis.RankThreeUC.S15.R1511C.le_pPrimeCore_of_normal
      (MonoidHom.normal_ker φ) hnot3
  calc A_L.map (MulAut.conj l).toMonoidHom ≤ (A_L.map φ).comap φ := hle_comap
    _ = A_L ⊔ φ.ker := Subgroup.comap_map_eq φ A_L
    _ ≤ A_L ⊔ O := sup_le_sup_left hker A_L

private theorem sup_pPrimeCore_eq_top_of_forall_conj_le {M H L A : Subgroup G}
    (h : Hyp83 M H L A) (hL : IsLThreeTwoPow (↥L ⧸ CFSG.pPrimeCore 3 ↥L))
    (hineq : ∀ l : ↥L, (A.subgroupOf L).map (MulAut.conj l).toMonoidHom ≤
      A.subgroupOf L ⊔ CFSG.pPrimeCore 3 ↥L) :
    A.subgroupOf L ⊔ CFSG.pPrimeCore 3 ↥L = ⊤ := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let A_L : Subgroup ↥L := A.subgroupOf L
  let O : Subgroup ↥L := CFSG.pPrimeCore 3 ↥L
  have hOmap : ∀ l : ↥L, O.map (MulAut.conj l).toMonoidHom = O := by
    haveI : O.Normal := CFSG.pPrimeCore_normal
    intro l
    exact Subgroup.mem_normalizer_iff_map_conj_eq.mp (by
      rw [Subgroup.normalizer_eq_top]
      exact Subgroup.mem_top l)
  have hKnormal : (A_L ⊔ O).Normal := by
    rw [← Subgroup.normalizer_eq_top_iff]
    refine eq_top_iff.mpr fun l hl => ?_
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    have hmap : (A_L ⊔ O).map (MulAut.conj l).toMonoidHom =
        A_L.map (MulAut.conj l).toMonoidHom ⊔ O := by
      rw [Subgroup.map_sup, hOmap l]
    change (A_L ⊔ O).map (MulAut.conj l).toMonoidHom = A_L ⊔ O
    rw [hmap]
    have hcard : Nat.card ↥(A_L.map (MulAut.conj l).toMonoidHom ⊔ O) =
        Nat.card ↥(A_L ⊔ O) := by
      rw [← hmap, Subgroup.card_map_of_injective (MulAut.conj l).injective]
    exact Subgroup.eq_of_le_of_card_ge (sup_le (hineq l) le_sup_right) (by rw [hcard])
  let θ : ↥L →* (↥L ⧸ O) := QuotientGroup.mk' O
  have hKmapθ : (A_L ⊔ O).map θ = A_L.map θ := by
    rw [Subgroup.map_sup, QuotientGroup.map_mk'_self, sup_bot_eq]
  have hAqNormal : (A_L.map θ).Normal := by
    have h := Subgroup.Normal.map hKnormal θ (QuotientGroup.mk'_surjective O)
    rwa [hKmapθ] at h
  have hAqNe : A_L.map θ ≠ ⊥ := by
    have hcardA : Nat.card A_L = 3 := by
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe h.le_L).toEquiv, h.card]
    intro hbot
    have hleO : A_L ≤ O := by
      have hker : A_L ≤ θ.ker := (Subgroup.map_eq_bot_iff A_L).mp hbot
      rwa [QuotientGroup.ker_mk'] at hker
    have hdisj : A_L ⊓ O = ⊥ :=
      (Subgroup.disjoint_of_coprime_natCard (H := A_L) (K := O) (by
        rw [hcardA]; exact CFSG.pPrimeCore_coprime_card)).eq_bot
    have hcard : Nat.card A_L = 1 := by
      rw [← inf_eq_left.mpr hleO, hdisj, Subgroup.card_bot]
    omega
  haveI : IsSimpleGroup (↥L ⧸ O) :=
    CFSG.LocalAnalysis.RankThreeUC.S15.R1511C.isSimpleGroup_of_isLThreeTwoPow hL
  have hAtop : A_L.map θ = ⊤ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (A_L.map θ) with hbot | htop
    · exact absurd hbot hAqNe
    · exact htop
  have hmapTop : (A_L ⊔ O).map θ = ⊤ := by rw [hKmapθ, hAtop]
  have hker_le : θ.ker ≤ A_L ⊔ O := by
    rw [QuotientGroup.ker_mk']
    exact le_sup_right
  have h := Subgroup.comap_map_eq_self (f := θ) hker_le
  rw [hmapTop] at h
  simpa using h.symm

private theorem false_of_sup_pPrimeCore_eq_top {M H L A : Subgroup G}
    (h : Hyp83 M H L A)
    (htop : A.subgroupOf L ⊔ CFSG.pPrimeCore 3 ↥L = ⊤) : False := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let A_L : Subgroup ↥L := A.subgroupOf L
  let O : Subgroup ↥L := CFSG.pPrimeCore 3 ↥L
  have hnot3 : Nat.card (↥L ⧸ O) ≠ 3 := by
    let P : Subgroup G := H ⊓ M
    let Ls : Subgroup ↥P := L.subgroupOf P
    let eL : ↥Ls ≃* ↥L := Subgroup.subgroupOfEquivOfLe h.le
    let eQ : (↥Ls ⧸ CFSG.pPrimeCore 3 ↥Ls) ≃* (↥L ⧸ O) :=
      QuotientGroup.congr (CFSG.pPrimeCore 3 ↥Ls) O eL (CFSG.pPrimeCore_map_iso 3 eL)
    have hq : CFSG.IsQuasisimple (↥Ls ⧸ CFSG.pPrimeCore 3 ↥Ls) :=
      CFSG.ComponentClassification.CatalogueBHeldSmallCore.pComponent_coreQuotient_quasisimple
        3 Ls h.comp
    exact CFSG.Quasithin.SBc17.card_ne_three_of_quasisimple
      (CFSG.IsQuasisimple.of_mulEquiv eQ.symm hq)
  have hcardA : Nat.card A_L = 3 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe h.le_L).toEquiv, h.card]
  have hdisj : A_L ⊓ O = ⊥ :=
    (Subgroup.disjoint_of_coprime_natCard (H := A_L) (K := O) (by
      rw [hcardA]; exact CFSG.pPrimeCore_coprime_card)).eq_bot
  have hsupcard : Nat.card ↥(A_L ⊔ O) = 3 * Nat.card ↥O :=
    card_sup_prime_of_coprime (H := ↥L) (A := A_L) (I := O) CFSG.pPrimeCore_normal
      hcardA hdisj
  have hqmul := Subgroup.card_eq_card_quotient_mul_card_subgroup O
  have hLcard : Nat.card ↥L = Nat.card ↥(A_L ⊔ O) := by rw [htop, Subgroup.card_top]
  have hprod : Nat.card (↥L ⧸ O) * Nat.card ↥O = 3 * Nat.card ↥O := by
    rw [← hqmul, hLcard, hsupcard]
  exact hnot3 (Nat.eq_of_mul_eq_mul_right Nat.card_pos hprod)

private theorem not_le_normalizer_quotientImage_of_isLThreeTwoPow {M H L A : Subgroup G}
    (h : Hyp83 M H L A) (hL : IsLThreeTwoPow (↥L ⧸ CFSG.pPrimeCore 3 ↥L)) :
    ¬ ((L.subgroupOf H).map (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥H)) ≤
        Subgroup.normalizer (quotientImagePPrimeCore H A :
          Set (↥H ⧸ CFSG.pPrimeCore 3 ↥H))) := by
  intro hle
  exact false_of_sup_pPrimeCore_eq_top h
    (sup_pPrimeCore_eq_top_of_forall_conj_le h hL
      (forall_conj_le_sup_pPrimeCore_of_le_normalizer h hle))

theorem pRank_three_normalClosure_eq_one {M H L A : Subgroup G}
    (h76 : KFact76MaxRankThree) (hC : CStarGen G)
    (hM : CFSG.Open.rankThreeIsMaxTwoLocal M)
    (h : Hyp83 M H L A) (hL : IsLThreeTwoPow (↥L ⧸ CFSG.pPrimeCore 3 ↥L))
    (hH3 : CFSG.Open.pRank 3 H ≤ 3) :
    CFSG.Open.pRank 3 (CFSG.Goldschmidt.normalClosureIn H A) = 1 := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let I : Subgroup ↥H := CFSG.pPrimeCore 3 ↥H
  let π : ↥H →* (↥H ⧸ I) := QuotientGroup.mk' I
  let X : Subgroup G := CFSG.Goldschmidt.normalClosureIn H A
  haveI : IsSimpleGroup G := hC.simple
  have hHne : H ≠ ⊤ :=
    CFSG.RankThreeCoreUniqueness.Helpers.twoLocal_ne_top hC.nonab H h.twoLocal
  have hKH : CFSG.Open.IsKGroup ↥H :=
    CFSG.LocalAnalysis.GLTheoremB.isKGroup_of_isKProper hC.kProper hHne
  have hKQ : CFSG.Open.IsKGroup (↥H ⧸ I) :=
    CFSG.LocalAnalysis.GLTheoremB.isKGroup_quotient' hKH I
  have hOQ : CFSG.pPrimeCore 3 (↥H ⧸ I) = ⊥ :=
    CFSG.pPrimeCore_quotient_eq_bot Nat.prime_three
  have hwc := (weaklyClosed_quotient_pPrimeCore hM h).2.2
  have hnorm := (weaklyClosed_quotient_pPrimeCore hM h).2.1
  have hcard := (weaklyClosed_quotient_pPrimeCore hM h).1
  have hXq : (X.subgroupOf H).map π = Subgroup.normalClosure
      (quotientImagePPrimeCore H A : Set (↥H ⧸ I)) := by
    have h1 : X.subgroupOf H = Subgroup.normalClosure (A.subgroupOf H : Set ↥H) := by
      show ((Subgroup.normalClosure (A.subgroupOf H : Set ↥H)).map H.subtype).subgroupOf H = _
      rw [Subgroup.subgroupOf,
        Subgroup.comap_map_eq_self_of_injective H.subtype_injective]
    rw [h1, quotientImagePPrimeCore]
    exact Subgroup.map_normalClosure _ _ (QuotientGroup.mk'_surjective I)
  have hXp : CFSG.Open.pRank 3 X = CFSG.Open.pRank 3 ((X.subgroupOf H).map π) := by
    have h2 : CFSG.Open.pRank 3 X = CFSG.Open.pRank 3 (X.subgroupOf H) := by
      have hmap : (X.subgroupOf H).map H.subtype = X :=
        Subgroup.map_subgroupOf_eq_of_le (CFSG.Goldschmidt.Sec8.normalClosureIn_le_self H A)
      simpa [hmap] using CFSG.LocalAnalysis.GLTheoremB.pRank_map_eq_of_injective
        (by norm_num) H.subtype H.subtype_injective (X.subgroupOf H)
    have h3 : CFSG.Open.pRank 3 ((X.subgroupOf H).map π) =
        CFSG.Open.pRank 3 (X.subgroupOf H) := by
      refine CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.K2.pRank_map_eq_of_coprime_ker
        π Nat.prime_three ?_
      have hle : (X.subgroupOf H) ⊓ π.ker ≤ I := by
        rw [QuotientGroup.ker_mk']
        exact inf_le_right
      exact fun hdvd => (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp
        CFSG.pPrimeCore_coprime_card (hdvd.trans (Subgroup.card_dvd_of_le hle))
    rw [h2, ← h3]
  have hN3 : CFSG.Open.pRank 3 (Subgroup.normalClosure
      (quotientImagePPrimeCore H A : Set (↥H ⧸ I))) ≤ 3 := by
    rw [← hXq, ← hXp]
    exact (CFSG.SectionRank.pRank_mono (by norm_num)
      (CFSG.Goldschmidt.Sec8.normalClosureIn_le_self H A)).trans hH3
  obtain ⟨hsimple, hrank_or_max⟩ := h76 (↥H ⧸ I) hKQ hOQ
    (quotientImagePPrimeCore H A) hcard hwc hN3
  rcases hrank_or_max with hrank | hmax
  · rw [hXp, hXq]
    exact hrank
  · have hLleX : L ≤ X := le_normalClosure_of_isPComponent h hL
    have hLqleXq : (L.subgroupOf H).map π ≤ (X.subgroupOf H).map π :=
      Subgroup.map_mono (f := π) (fun x hx => hLleX hx)
    have hNqle : Subgroup.normalizer (quotientImagePPrimeCore H A :
        Set (↥H ⧸ I)) ≤ ((H ⊓ M).subgroupOf H).map π := by
      have hNM : (Subgroup.normalizer (A : Set G)).subgroupOf H ≤
          (H ⊓ M).subgroupOf H := by
        intro x hx
        exact ⟨x.2, (normalizer_le_of_hyp83 hM h) hx⟩
      rw [hnorm]
      exact Subgroup.map_mono (f := π) hNM
    have hLqleHM : (L.subgroupOf H).map π ≤ ((H ⊓ M).subgroupOf H).map π :=
      Subgroup.map_mono (f := π) (fun x hx =>
        ⟨h.le.trans inf_le_left hx, h.le.trans inf_le_right hx⟩)
    let NqK : Subgroup (↥H ⧸ I) :=
      Subgroup.normalizer (quotientImagePPrimeCore H A : Set (↥H ⧸ I)) ⊓
        Subgroup.normalClosure (quotientImagePPrimeCore H A : Set (↥H ⧸ I))
    have hNqKle : NqK ≤ ((H ⊓ M).subgroupOf H).map π :=
      inf_le_left.trans hNqle
    have hXLq : (X.subgroupOf H).map π = (L.subgroupOf H).map π ⊔ NqK := by
      have hLqK : (L.subgroupOf H).map π ≤
          Subgroup.normalClosure (quotientImagePPrimeCore H A : Set (↥H ⧸ I)) := by
        rw [← hXq]; exact hLqleXq
      have hNqKK : NqK ≤
          Subgroup.normalClosure (quotientImagePPrimeCore H A : Set (↥H ⧸ I)) :=
        inf_le_right
      have hmax' : (L.subgroupOf H).map π ⊔ NqK = NqK ∨
          (L.subgroupOf H).map π ⊔ NqK =
            Subgroup.normalClosure (quotientImagePPrimeCore H A : Set (↥H ⧸ I)) :=
        hmax ((L.subgroupOf H).map π ⊔ NqK)
          (le_sup_right : NqK ≤ (L.subgroupOf H).map π ⊔ NqK) (sup_le hLqK hNqKK)
      rcases hmax' with hNq | hNq
      · exact absurd ((le_sup_left.trans hNq.le).trans inf_le_left)
          (not_le_normalizer_quotientImage_of_isLThreeTwoPow h hL)
      · rw [hNq, ← hXq]
    have hKleHM : (X.subgroupOf H).map π ≤ ((H ⊓ M).subgroupOf H).map π := by
      rw [hXLq]
      exact sup_le hLqleHM hNqKle
    have hsub : CFSG.Open.IsSubnormal ((L.subgroupOf H).map π)
        (((H ⊓ M).subgroupOf H).map π) := by
      have hLM : L ≤ H ⊓ M := h.le
      have hMH : H ⊓ M ≤ H := inf_le_left
      obtain ⟨-, -, hsubHM, -, -⟩ := h.comp
      have h1 : CFSG.Open.IsSubnormal (L.subgroupOf (H ⊓ M)) ⊤ :=
        CFSG.Open.IsSubnormal.top_iff.mpr hsubHM
      have h2 := CFSG.Open.IsSubnormal.map (f := Subgroup.inclusion hMH)
        (H := L.subgroupOf (H ⊓ M)) (K := ⊤) h1
      have h3 : Subgroup.map (Subgroup.inclusion hMH) (L.subgroupOf (H ⊓ M)) =
          L.subgroupOf H := by
        ext x
        constructor
        · rintro ⟨y, hy, hyx⟩
          rw [← hyx]
          exact hy
        · intro hx
          refine ⟨⟨(x : G), ⟨x.2, (hLM hx).2⟩⟩, hx, ?_⟩
          rfl
      have h4 : Subgroup.map (Subgroup.inclusion hMH) (⊤ : Subgroup ↥(H ⊓ M)) =
          (H ⊓ M).subgroupOf H := by
        ext x
        constructor
        · rintro ⟨y, -, hyx⟩
          rw [← hyx]
          exact y.2
        · intro hx
          exact ⟨⟨(x : G), hx⟩, trivial, rfl⟩
      rw [h3, h4] at h2
      exact h2.map π
    have hsubK : CFSG.Open.IsSubnormal ((L.subgroupOf H).map π) ((X.subgroupOf H).map π) := by
      have := hsub.inf_of_le hKleHM
      rwa [inf_eq_left.mpr hLqleXq] at this
    have hLqne : (L.subgroupOf H).map π ≠ ⊥ := by
      have hAqle : quotientImagePPrimeCore H A ≤ (L.subgroupOf H).map π :=
        Subgroup.map_mono (f := π) (fun x hx => h.le_L hx)
      rintro hbot
      rw [hbot] at hAqle
      have hbotQ : quotientImagePPrimeCore H A = ⊥ := le_bot_iff.mp hAqle
      have hcard' : Nat.card (⊥ : Subgroup (↥H ⧸ I)) = 3 := by
        simpa [hbotQ] using (weaklyClosed_quotient_pPrimeCore hM h).1
      rw [Subgroup.card_bot] at hcard'
      omega
    have hLqX : (L.subgroupOf H).map π = (X.subgroupOf H).map π := by
      rcases CFSG.Open.IsSubnormal.eq_bot_or_eq_of_isSimpleGroup
        (H := (X.subgroupOf H).map π) hsubK (hXq ▸ hsimple) with h | h
      · exact absurd h hLqne
      · exact h
    have hLp : CFSG.Open.pRank 3 ((L.subgroupOf H).map π) = 1 := by
      have hLqranks : CFSG.Open.pRank 3 ((L.subgroupOf H).map π) =
          CFSG.Open.pRank 3 (L.subgroupOf H) := by
        refine CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.K2.pRank_map_eq_of_coprime_ker
          π Nat.prime_three ?_
        have hle : (L.subgroupOf H) ⊓ π.ker ≤ I := by
          rw [QuotientGroup.ker_mk']
          exact inf_le_right
        exact fun hdvd => (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp
          CFSG.pPrimeCore_coprime_card (hdvd.trans (Subgroup.card_dvd_of_le hle))
      have hLHrank : CFSG.Open.pRank 3 (L.subgroupOf H) = CFSG.Open.pRank 3 L := by
        have hmap : (L.subgroupOf H).map H.subtype = L :=
          Subgroup.map_subgroupOf_eq_of_le (h.le.trans inf_le_left)
        simpa [hmap] using (CFSG.LocalAnalysis.GLTheoremB.pRank_map_eq_of_injective
          (p := 3) (by norm_num) H.subtype H.subtype_injective (L.subgroupOf H)).symm
      rw [hLqranks, hLHrank]
      exact h.rank
    rw [hXp, ← hLqX]
    exact hLp

private theorem exists_normalizer_of_mem_normalClosure {M H L A : Subgroup G}
    (h76 : KFact76MaxRankThree) (hC : CStarGen G)
    (hM : CFSG.Open.rankThreeIsMaxTwoLocal M)
    (h : Hyp83 M H L A) (hL : IsLThreeTwoPow (↥L ⧸ CFSG.pPrimeCore 3 ↥L))
    (hH3 : CFSG.Open.pRank 3 H ≤ 3) :
    ∀ g ∈ H, ∃ x ∈ CFSG.Goldschmidt.normalClosureIn H A,
      x⁻¹ * g ∈ Subgroup.normalizer (A : Set G) := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let X : Subgroup G := CFSG.Goldschmidt.normalClosureIn H A
  have hXH : X ≤ H := CFSG.Goldschmidt.Sec8.normalClosureIn_le_self H A
  have hAX : A ≤ X :=
    CFSG.Goldschmidt.Sec8.le_normalClosureIn (h.le_L.trans (h.le.trans inf_le_left))
  have hXnorm : H ≤ Subgroup.normalizer (X : Set G) :=
    CFSG.Goldschmidt.Sec8.le_normalizer_normalClosureIn H A
  have hrank : CFSG.Open.pRank 3 X ≤ 1 := by
    have := pRank_three_normalClosure_eq_one h76 hC hM h hL hH3
    simpa [X] using le_of_eq this
  intro g hg
  have hAgX : A.map (MulAut.conj g).toMonoidHom ≤ X := by
    have h := Subgroup.map_mono (f := (MulAut.conj g).toMonoidHom) hAX
    have hXmap : X.map (MulAut.conj g).toMonoidHom = X :=
      Subgroup.mem_normalizer_iff_map_conj_eq.mp (hXnorm hg)
    exact h.trans (le_of_eq hXmap)
  have hAg3 : Nat.card ↥(A.map (MulAut.conj g).toMonoidHom) = 3 := by
    rw [Subgroup.card_map_of_injective (MulAut.conj g).injective, h.card]
  obtain ⟨x, hxX, hxconj⟩ :=
    CFSG.AGLEmbeddingD2.Tits.S3AmalgamBound.exists_conj_of_pRank_le_one
      Nat.prime_three hrank hAgX hAX hAg3 h.card
  refine ⟨x⁻¹, X.inv_mem hxX, ?_⟩
  have hxg : (x⁻¹)⁻¹ * g = x * g := by group
  rw [hxg, Subgroup.mem_normalizer_iff_map_conj_eq]
  calc A.map (MulAut.conj (x * g)).toMonoidHom
      = A.map ((MulAut.conj x).toMonoidHom.comp (MulAut.conj g).toMonoidHom) := by
        congr 1
        ext y
        simp [MulAut.conj_apply, mul_assoc]
    _ = (A.map (MulAut.conj g).toMonoidHom).map (MulAut.conj x).toMonoidHom :=
        (Subgroup.map_map A (MulAut.conj x).toMonoidHom (MulAut.conj g).toMonoidHom).symm
    _ = A := hxconj

theorem eq_sup_inf_of_pRank_one {M H L A : Subgroup G}
    (h76 : KFact76MaxRankThree) (hC : CStarGen G)
    (hM : CFSG.Open.rankThreeIsMaxTwoLocal M)
    (h : Hyp83 M H L A) (hL : IsLThreeTwoPow (↥L ⧸ CFSG.pPrimeCore 3 ↥L))
    (hH3 : CFSG.Open.pRank 3 H ≤ 3) :
    H = CFSG.Goldschmidt.normalClosureIn H A ⊔ (H ⊓ M) := by
  let X : Subgroup G := CFSG.Goldschmidt.normalClosureIn H A
  have hXle : X ≤ H := CFSG.Goldschmidt.Sec8.normalClosureIn_le_self H A
  have hconj : ∀ g ∈ H, ∃ x ∈ X, x⁻¹ * g ∈ Subgroup.normalizer (A : Set G) :=
    exists_normalizer_of_mem_normalClosure h76 hC hM h hL hH3
  refine le_antisymm ?_ (sup_le hXle inf_le_left)
  intro g hg
  obtain ⟨x, hxX, hgN⟩ := hconj g hg
  have hxH : x ∈ H := hXle hxX
  have hnHM : x⁻¹ * g ∈ H ⊓ M :=
    ⟨H.mul_mem (H.inv_mem hxH) hg, normalizer_le_of_hyp83 hM h hgN⟩
  have hgdecomp : g = x * (x⁻¹ * g) := by group
  let Y : Subgroup G := X ⊔ (H ⊓ M)
  have hxY : x ∈ Y := Subgroup.mem_sup_left (T := H ⊓ M) hxX
  have hnY : x⁻¹ * g ∈ Y := Subgroup.mem_sup_right (S := X) hnHM
  have hgY : g ∈ Y := by
    rw [hgdecomp]
    exact Subgroup.mul_mem Y hxY hnY
  exact hgY

end CFSG.LocalAnalysis.AGL81TheoremCD.Section8
