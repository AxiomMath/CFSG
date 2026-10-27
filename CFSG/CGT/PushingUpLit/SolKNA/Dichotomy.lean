module

public import CFSG.CGT.PushingUpLit.SolKNA.Thm3
public import CFSG.CGT.PushingUpLit.SolKNA.QuatCentral
public import CFSG.CGT.PushingUpLit.SolKNA.Extraspecial32

public section

namespace CFSG.CGT.PushingUpLit.SolKNA

open CFSG CFSG.ComponentClassification.AschbacherTightEmbedding
open CFSG.ABGLocalTools (IsSylowOf)
open CFSG.Assembly (pCoreOf)
open CFSG.ComponentClassification.AS76b (oUpperTwoPrime)
open CFSG.Open (IsElemAbelian)
open CFSG.CGT.PushingUpLit.SolKAb (IsCommSubgroup)

variable {G : Type} [Group G] [Finite G]

theorem le_sylow_of_normalizer {R K A : Subgroup G} (hR : IsSylowOf 2 R K)
    (hKR : K ≤ Subgroup.normalizer (R : Set G)) (hAK : A ≤ K) (hA : IsPGroup 2 A) : A ≤ R := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨Q, hQ⟩ := hR.exists_sylow_eq_subgroupOf
  have hQn : (Q : Subgroup K).Normal := by
    rw [hQ]
    exact (Subgroup.normal_subgroupOf_iff_le_normalizer hR.le).mpr hKR
  have hA' : IsPGroup 2 (A.subgroupOf K) := hA.comap_subtype
  obtain ⟨Q', hAQ'⟩ := hA'.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq K Q Q'
  have hQQ' : Q' = Q := by
    have := hQn
    rw [← hg]
    exact Sylow.smul_eq_of_normal
  intro x hx
  have h1 : (⟨x, hAK hx⟩ : K) ∈ A.subgroupOf K := hx
  have h2 := hAQ' h1
  rw [hQQ', hQ] at h2
  exact h2

omit [Finite G] in
theorem le_sylow_of_le_normalizer {P K A : Subgroup G} (hP : IsSylowOf 2 P K) (hAK : A ≤ K)
    (hKA : K ≤ Subgroup.normalizer (A : Set G)) (hA : IsPGroup 2 A) : A ≤ P := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨Q, hQ⟩ := hP.exists_sylow_eq_subgroupOf
  have : (Subgroup.comap K.subtype A).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hAK).mpr hKA
  have hle : A.subgroupOf K ≤ (Q : Subgroup K) := (hA.comap_subtype (K := K)).le_sylow_of_normal Q
  rw [hQ] at hle
  intro x hx
  exact hle (show (⟨x, hAK hx⟩ : K) ∈ A.subgroupOf K from hx)

theorem eq_of_normal_sylow {K R : Subgroup G} (hK : oUpperTwoPrime K = K)
    (hR : IsSylowOf 2 R K) (hKR : K ≤ Subgroup.normalizer (R : Set G)) : K = R := by
  refine le_antisymm ?_ hR.le
  rw [← hK]
  refine (Subgroup.closure_le R).mpr ?_
  rintro x ⟨hxK, k, hk⟩
  have hz : IsPGroup 2 (Subgroup.zpowers x) := by
    obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp (orderOf_dvd_of_pow_eq_one hk)
    exact IsPGroup.of_card (n := j) (by rw [Nat.card_zpowers]; exact hj)
  exact le_sylow_of_normalizer hR hKR (Subgroup.zpowers_le.mpr hxK) hz (Subgroup.mem_zpowers x)

namespace NAConfig

variable {K R T : Subgroup G} {g : G}

theorem caseI_not_normal (h : NAConfig G K R T g) (I : CaseI K R T)
    (hM : ¬ Subgroup.normalizer (K : Set G) ≤
      Subgroup.normalizer ((R ⊓ Subgroup.normalizer (T : Set G) : Subgroup G) : Set G)) :
    K = R ∧ R = pCoreOf 2 K ∧
      ∃ c : G, c ∈ R ∧ c ≠ 1 ∧ c * c = 1 ∧ (∀ r ∈ R, r * c = c * r) ∧
        ⁅R, R⁆ = Subgroup.zpowers c ∧
        (∀ y ∈ R, y ∈ R ⊓ Subgroup.centralizer (R : Set G) → y * y = 1) ∧
        (∀ y ∈ R, y ∉ R ⊓ Subgroup.centralizer (R : Set G) → y * y = c) ∧
        (R ⊓ Subgroup.centralizer (R : Set G)).relIndex R = 4 ∧
        4 ≤ Nat.card ↥(R ⊓ Subgroup.centralizer (R : Set G)) ∧
        R ⊓ Subgroup.centralizer (R : Set G) ≤ R ⊓ Subgroup.normalizer (T : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hNR : R ⊓ Subgroup.normalizer (T : Set G) ≤ R := inf_le_left
  have hNK : R ⊓ Subgroup.normalizer (T : Set G) ≤ K := hNR.trans h.R_le_K
  have hNP : R ⊓ Subgroup.normalizer (T : Set G) ≤ pCoreOf 2 K :=
    CFSG.LieType.BorelTits.le_pCoreOf 2 hNK I.normal (h.sylowR.isPGroup.to_le hNR)
  have hKP : K ≤ Subgroup.normalizer (pCoreOf 2 K : Set G) :=
    CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 K
  have hPR : pCoreOf 2 K ≤ R :=
    le_sylow_of_le_normalizer h.sylowR (CFSG.LieType.BorelTits.pCoreOf_le 2 K) hKP
      (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 K)
  have hcardR : 2 * Nat.card ↥(R ⊓ Subgroup.normalizer (T : Set G)) = Nat.card ↥R := by
    have := Subgroup.relIndex_mul_card (R ⊓ Subgroup.normalizer (T : Set G)) R
    rw [I.relIndex_two, inf_of_le_left hNR] at this
    exact this
  have hdvd1 := Subgroup.card_dvd_of_le hNP
  have hdvd2 := Subgroup.card_dvd_of_le hPR
  obtain ⟨a, ha⟩ := hdvd1
  have hpos : 0 < Nat.card ↥(R ⊓ Subgroup.normalizer (T : Set G)) := Nat.card_pos
  have ha2 : a ∣ 2 := by
    rw [ha, ← hcardR, mul_comm 2] at hdvd2
    exact Nat.dvd_of_mul_dvd_mul_left hpos hdvd2
  have hP : pCoreOf 2 K = R := by
    rcases (Nat.dvd_prime Nat.prime_two).mp ha2 with h1 | h2
    · exfalso
      rw [h1, mul_one] at ha
      have hPN : pCoreOf 2 K = R ⊓ Subgroup.normalizer (T : Set G) :=
        (Subgroup.eq_of_le_of_card_ge hNP (le_of_eq ha)).symm
      apply hM
      intro m hm
      have h5 : m ∈ Subgroup.normalizer ((pCoreOf 2 K : Subgroup G) : Set G) :=
        CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 K hm
      rwa [hPN] at h5
    · rw [h2, mul_comm, hcardR] at ha
      exact Subgroup.eq_of_le_of_card_ge hPR (le_of_eq ha.symm)
  have hKR : K = R := by
    refine eq_of_normal_sylow h.perfect h.sylowR ?_
    rw [← hP]
    exact hKP
  refine ⟨hKR, hP.symm, ?_⟩
  obtain ⟨m, hmK, hmN⟩ : ∃ m, m ∈ Subgroup.normalizer (K : Set G) ∧
      m ∉ Subgroup.normalizer ((R ⊓ Subgroup.normalizer (T : Set G) : Subgroup G) : Set G) := by
    by_contra hcon
    apply hM
    intro m hm
    by_contra hmN
    exact hcon ⟨m, hm, hmN⟩
  have hmR : m ∈ Subgroup.normalizer (R : Set G) := by
    rw [← hKR]
    exact hmK
  refine caseI_dichotomy h.sylowR.isPGroup hNR I.relIndex_two I.comm I.exists_sq_ne I.inv h.rank
    (MulAut.conj m) ?_ ?_
  · exact Subgroup.mem_normalizer_iff_map_conj_eq.mp hmR
  · exact fun heq => hmN (Subgroup.mem_normalizer_iff_map_conj_eq.mpr heq)

theorem caseII5_not_normal (h : NAConfig G K R T g) {H : Subgroup G} (h5 : CaseII5 K R T H)
    (hM : ¬ Subgroup.normalizer (K : Set G) ≤ Subgroup.normalizer (H : Set G)) :
    K = R ∧ R = pCoreOf 2 K ∧ Nat.card ↥T = 4 ∧
      ∃ c ∈ R ⊓ Subgroup.normalizer (T : Set G), c ≠ 1 ∧ (∀ r ∈ R, r * c = c * r) ∧
        ⁅R, R⁆ = Subgroup.zpowers c ∧ R ⊓ Subgroup.centralizer (R : Set G) = Subgroup.zpowers c ∧
        ∀ x ∈ H, x ∉ R ⊓ Subgroup.normalizer (T : Set G) → x * x = c := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hHK : H ≤ K := h5.H_le.trans h.R_le_K
  have hHP : H ≤ pCoreOf 2 K :=
    CFSG.LieType.BorelTits.le_pCoreOf 2 hHK h5.normal (h.sylowR.isPGroup.to_le h5.H_le)
  have hKP : K ≤ Subgroup.normalizer (pCoreOf 2 K : Set G) :=
    CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 K
  have hPR : pCoreOf 2 K ≤ R :=
    le_sylow_of_le_normalizer h.sylowR (CFSG.LieType.BorelTits.pCoreOf_le 2 K) hKP
      (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 K)
  have hcardR : 2 * Nat.card ↥H = Nat.card ↥R := by
    have := Subgroup.relIndex_mul_card H R
    rw [h5.relIndex_two, inf_of_le_left h5.H_le] at this
    exact this
  obtain ⟨a, ha⟩ := Subgroup.card_dvd_of_le hHP
  have hpos : 0 < Nat.card ↥H := Nat.card_pos
  have ha2 : a ∣ 2 := by
    have hdvd2 := Subgroup.card_dvd_of_le hPR
    rw [ha, ← hcardR, mul_comm 2] at hdvd2
    exact Nat.dvd_of_mul_dvd_mul_left hpos hdvd2
  have hP : pCoreOf 2 K = R := by
    rcases (Nat.dvd_prime Nat.prime_two).mp ha2 with h1 | h2
    · exfalso
      rw [h1, mul_one] at ha
      have hPH : pCoreOf 2 K = H := (Subgroup.eq_of_le_of_card_ge hHP (le_of_eq ha)).symm
      apply hM
      intro m hm
      have h5' : m ∈ Subgroup.normalizer ((pCoreOf 2 K : Subgroup G) : Set G) :=
        CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 K hm
      rwa [hPH] at h5'
    · rw [h2, mul_comm, hcardR] at ha
      exact Subgroup.eq_of_le_of_card_ge hPR (le_of_eq ha.symm)
  have hKR : K = R := by
    refine eq_of_normal_sylow h.perfect h.sylowR ?_
    rw [← hP]
    exact hKP
  obtain ⟨m, hmK, hmH⟩ : ∃ m, m ∈ Subgroup.normalizer (K : Set G) ∧
      m ∉ Subgroup.normalizer (H : Set G) := by
    by_contra hcon
    apply hM
    intro m hm
    by_contra hmN
    exact hcon ⟨m, hm, hmN⟩
  have hmR : m ∈ Subgroup.normalizer (R : Set G) := by
    rw [← hKR]
    exact hmK
  have hcardN : Nat.card ↥(R ⊓ Subgroup.normalizer (T : Set G)) = Nat.card ↥T :=
    Nat.card_congr h5.iso.some.toEquiv
  have hT2 : ∀ t ∈ T, t * t = 1 := fun t ht => by simpa [sq] using h5.elem_T.2 t ht
  have hTcomm : IsCommSubgroup T := fun a ha b hb =>
    congrArg Subtype.val (h5.elem_T.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  have hTI := h.tiPair hTcomm
  have hsq : ∀ x ∈ H, x * x ∈ R ⊓ Subgroup.normalizer (T : Set G) := fun x hx =>
    h5.omega_le (x * x) (H.mul_mem hx hx) (by
      calc (x * x) ^ 2 = x ^ 4 := by rw [← pow_two, ← pow_mul]
        _ = 1 := h5.pow_four x hx)
  obtain ⟨hT4, c, hcN, hc1, hcc, hcom, hsqc, hZ⟩ := caseII5_dichotomy' (T := T)
    (Z := R ⊓ Subgroup.normalizer (T : Set G)) h.sylowR.isPGroup h5.H_le h5.relIndex_two
    h5.N_le h5.N_conj h5.N_central h5.elem_N hsq
    (fun x hx hx2 => h5.omega_le x hx (by rw [pow_two]; exact hx2)) (by rw [h5.card_H, hcardN])
    (by rw [hcardN]; exact h5.four_le) hT2 hcardN.symm (fun z hz t ht => hTI.N_comm hz ht)
    h5.gen h5.comm_mem h5.comm_not_mem (MulAut.conj m)
    (Subgroup.mem_normalizer_iff_map_conj_eq.mp hmR)
    (fun heq => hmH (Subgroup.mem_normalizer_iff_map_conj_eq.mpr heq))
  refine ⟨hKR, hP.symm, hT4, c, hcN, hc1, hcc, hcom, ?_, hsqc⟩
  refine le_antisymm (fun y hy => hZ y hy.1 fun r hr => ?_) ?_
  · exact Subgroup.mem_centralizer_iff.mp hy.2 r hr
  · rw [Subgroup.zpowers_le]
    exact ⟨hcN.1, Subgroup.mem_centralizer_iff.mpr fun r hr => hcc r hr⟩

end NAConfig

end CFSG.CGT.PushingUpLit.SolKNA
