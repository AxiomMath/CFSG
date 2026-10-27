module

public import CFSG.GH74.GLS.C3.Layer1.Th2Main
public import CFSG.GH74.GLS.Stage1.Thm6.Prod.Resid

public section

namespace CFSG.GH74.GLS.Th2.CaseI

open Subgroup CFSG.ABGLocalTools CFSG.GH74.GLS

variable {G : Type} [Group G]

theorem ne_bot_of_one_le_pRank [Finite G] {H : Subgroup G} (h : 1 ≤ CFSG.pRank 2 ↥H) :
    H ≠ ⊥ := by
  rintro rfl
  have h0 : CFSG.pRank 2 ↥(⊥ : Subgroup G) ≤ 0 := by
    refine csSup_le' ?_
    rintro r ⟨A, -, hA⟩
    have h1 : Nat.card A ≤ Nat.card ↥(⊥ : Subgroup G) := A.card_le_card_group
    rw [Subgroup.card_bot, hA] at h1
    by_contra hr
    have : 1 < 2 ^ r := Nat.one_lt_two_pow (by omega)
    omega
  omega

theorem gammaK_le_normalizer_of_standard [Finite G] {K Q : Subgroup G}
    (hK : IsStandardSubgroup K) (hQ : IsSylowOf 2 Q (centralizer (K : Set G))) :
    gammaK 2 Q 1 ≤ normalizer (K : Set G) := by
  unfold gammaK
  refine iSup₂_le fun H hHQ => iSup_le fun hrk => ?_
  intro n hn
  by_contra hnK
  have hHne : H ≠ ⊥ := ne_bot_of_one_le_pRank hrk
  have hH2 : IsPGroup 2 H := hQ.isPGroup.to_le hHQ
  obtain ⟨u, huH, hu2⟩ := exists_involution_mem hH2 hHne
  have hnC : n ∉ normalizer ((centralizer (K : Set G) : Subgroup G) : Set G) := by
    rw [hK.2.2.2.1]; exact hnK
  have hodd := hK.2.2.1 n hnC
  have huC : u ∈ centralizer (K : Set G) ⊓ conjugate (centralizer (K : Set G)) n := by
    refine ⟨hQ.le (hHQ huH), ?_⟩
    have hnu : n * u * n⁻¹ ∈ H := (Subgroup.mem_normalizer_iff.1 hn u).1 huH
    refine Subgroup.mem_map.2 ⟨n * u * n⁻¹, hQ.le (hHQ hnu), ?_⟩
    simp
    group
  have hdvd : 2 ∣ Nat.card ↥(centralizer (K : Set G) ⊓ conjugate (centralizer (K : Set G)) n) := by
    have := Subgroup.orderOf_dvd_natCard _ huC
    rwa [hu2] at this
  exact (Nat.not_even_iff_odd.2 hodd) (even_iff_two_dvd.2 hdvd)

theorem exists_elemAbelian_four [Finite G] {Q : Subgroup G} (h : 2 ≤ CFSG.pRank 2 ↥Q) :
    ∃ E : Subgroup G, E ≤ Q ∧ CFSG.IsElementaryAbelian 2 ↥E ∧ 2 ^ 2 ≤ Nat.card ↥E := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨A, hA, hcard⟩ :=
    CFSG.StronglyEmbedded.SteinbergBU.exists_four_group_of_two_le_pRank (G := ↥Q) h
  have := hA
  refine ⟨A.map Q.subtype, Subgroup.map_subtype_le A, CFSG.IsElementaryAbelian.map_subtype, ?_⟩
  rw [Subgroup.card_map_of_injective Q.subtype_injective, hcard]

theorem pPrimeCoreOf_le_normalizer [Finite G] {K L M Q : Subgroup G}
    (hLnorm : ∀ m ∈ M, ∀ l ∈ L, m * l * m⁻¹ ∈ L) (hQM : Q ≤ M) (hrk : 2 ≤ CFSG.pRank 2 ↥Q)
    (hgam : gammaK 2 Q 1 ≤ normalizer (K : Set G)) :
    pPrimeCoreOf 2 L ≤ normalizer (K : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨E, hEQ, hE, hEcard⟩ := exists_elemAbelian_four hrk
  have hodd : ¬ 2 ∣ Nat.card ↥(pPrimeCoreOf 2 L) := by
    have h2 : Nat.card ↥(pPrimeCoreOf 2 L) = Nat.card ↥(pPrimeCore 2 ↥L) :=
      Subgroup.card_map_of_injective L.subtype_injective
    rw [h2]
    exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_two).1 CFSG.pPrimeCore_coprime_card
  refine CFSG.Asc75.le_of_forall_inf_centralizer_le' hE hEcard hodd ?_ ?_
  · intro e he
    exact C3.Layer1.U1a.mem_normalizer_pPrimeCoreOf hLnorm (hQM (hEQ he))
  · intro b hb hb1
    have hb2 : orderOf b = 2 :=
      orderOf_eq_prime (CFSG.elemPow_eq_one_of_isElementaryAbelian b hb) hb1
    exact inf_le_right.trans ((C3.Layer1.U1a.centralizer_le_gammaK (hEQ hb) hb2).trans hgam)

theorem mem_of_two_element [Finite G] {K L : Subgroup G} (hKL : K ≤ L)
    (hLeq : L = pPrimeCoreOf 2 L ⊔ K) (hLN : L ≤ normalizer (K : Set G))
    {s : G} (hs : s ∈ L) {k : ℕ} (hk : s ^ (2 ^ k) = 1) : s ∈ K := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hN1 : (pPrimeCore 2 ↥L).Normal := CFSG.pPrimeCore_normal
  have hN2 : (K.subgroupOf L).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hKL).2 hLN
  have hsup : pPrimeCore 2 ↥L ⊔ K.subgroupOf L = ⊤ := by
    have h1 : (pPrimeCoreOf 2 L).subgroupOf L = pPrimeCore 2 ↥L :=
      Subgroup.comap_map_eq_self_of_injective L.subtype_injective _
    have h2 := Subgroup.subgroupOf_sup (A := pPrimeCoreOf 2 L) (A' := K) (B := L)
      (TwoThin.pPrimeCoreOf_le L) hKL
    rw [← hLeq, Subgroup.subgroupOf_self, h1] at h2
    exact h2.symm
  have hmem : (⟨s, hs⟩ : ↥L) ∈ pPrimeCore 2 ↥L ⊔ K.subgroupOf L := by rw [hsup]; trivial
  obtain ⟨n, hn, k', hk', hnk⟩ := Subgroup.mem_sup_of_normal_left.1 hmem
  have hq : QuotientGroup.mk' (pPrimeCore 2 ↥L) (⟨s, hs⟩ : ↥L) ∈
      (K.subgroupOf L).map (QuotientGroup.mk' (pPrimeCore 2 ↥L)) := by
    have hn1 : QuotientGroup.mk' (pPrimeCore 2 ↥L) n = 1 := (QuotientGroup.eq_one_iff n).2 hn
    refine ⟨k', hk', ?_⟩
    rw [← hnk, map_mul, hn1, one_mul]
  exact Stage1.Thm6.Prod.two_elt_mem_of_map_mem (pPrimeCore 2 ↥L) (K.subgroupOf L)
    CFSG.pPrimeCore_coprime_card (s := (⟨s, hs⟩ : ↥L)) (k := k)
    (Subtype.ext (by simpa using hk)) hq

theorem oPrimeResidual_eq_top_of_isPerfect (X : Type*) [Group X] [Finite X] [Group.IsPerfect X] :
    oPrimeResidual 2 X = ⊤ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hn : (oPrimeResidual 2 X).Normal := Stage1.Thm6.Prod.oPrimeResidual_normal 2 X
  have hodd : Odd (Nat.card (X ⧸ oPrimeResidual 2 X)) := by
    obtain ⟨P⟩ : Nonempty (Sylow 2 X) := inferInstance
    have hP : (P : Subgroup X) ≤ oPrimeResidual 2 X := by
      intro x hx
      obtain ⟨k, hk⟩ := P.isPGroup' ⟨x, hx⟩
      refine Subgroup.subset_closure ⟨k, ?_⟩
      simpa using congrArg Subtype.val hk
    have hdvd : (oPrimeResidual 2 X).index ∣ (P : Subgroup X).index :=
      Subgroup.index_dvd_of_le hP
    have hnd : ¬ 2 ∣ (P : Subgroup X).index := P.not_dvd_index
    exact Nat.odd_iff.mpr (Nat.two_dvd_ne_zero.mp (fun h2 => hnd (h2.trans hdvd)))
  have hsolv : Group.IsSolvable (X ⧸ oPrimeResidual 2 X) :=
    CFSG.Milestones.odd_order_solvable hodd
  rcases subsingleton_or_nontrivial (X ⧸ oPrimeResidual 2 X) with hs | hnt
  · exact Subgroup.index_eq_one.1 (Nat.card_of_subsingleton 1)
  · exact absurd hsolv (Group.IsPerfect.not_isSolvable _)

theorem le_closure_two_elements [Finite G] {K : Subgroup G} (hK : Group.IsPerfect K) :
    K ≤ Subgroup.closure {g : G | g ∈ K ∧ ∃ n : ℕ, g ^ (2 ^ n) = 1} := by
  have htop := oPrimeResidual_eq_top_of_isPerfect ↥K
  have key : ∀ x : ↥K, x ∈ oPrimeResidual 2 ↥K →
      (x : G) ∈ Subgroup.closure {g : G | g ∈ K ∧ ∃ n : ℕ, g ^ (2 ^ n) = 1} := by
    intro x hx
    unfold oPrimeResidual at hx
    induction hx using Subgroup.closure_induction with
    | mem x hx =>
      obtain ⟨n, hn⟩ := hx
      exact Subgroup.subset_closure ⟨x.2, n, by simpa using congrArg Subtype.val hn⟩
    | one => exact Subgroup.one_mem _
    | mul x y _ _ hx hy => exact Subgroup.mul_mem _ hx hy
    | inv x _ hx => exact Subgroup.inv_mem _ hx
  intro g hg
  exact key ⟨g, hg⟩ (by rw [htop]; trivial)

theorem le_normalizer_of_two_elements [Finite G] {K L M : Subgroup G} (hK : Group.IsPerfect K)
    (hKL : K ≤ L) (hLnorm : ∀ m ∈ M, ∀ l ∈ L, m * l * m⁻¹ ∈ L)
    (h2 : ∀ s ∈ L, ∀ k : ℕ, s ^ (2 ^ k) = 1 → s ∈ K) : M ≤ normalizer (K : Set G) := by
  have key : ∀ m ∈ M, ∀ x ∈ K, m * x * m⁻¹ ∈ K := by
    intro m hm x hx
    have hx' := le_closure_two_elements hK hx
    clear hx
    induction hx' using Subgroup.closure_induction with
    | mem y hy =>
      obtain ⟨hyK, n, hn⟩ := hy
      refine h2 _ (hLnorm m hm y (hKL hyK)) n ?_
      rw [conj_pow, hn]
      group
    | one => simp
    | mul y z _ _ hy hz =>
      have : m * (y * z) * m⁻¹ = (m * y * m⁻¹) * (m * z * m⁻¹) := by group
      rw [this]; exact Subgroup.mul_mem _ hy hz
    | inv y _ hy =>
      have : m * y⁻¹ * m⁻¹ = (m * y * m⁻¹)⁻¹ := by group
      rw [this]; exact Subgroup.inv_mem _ hy
  intro m hm
  rw [Subgroup.mem_normalizer_iff]
  intro h
  refine ⟨key m hm h, fun hh => ?_⟩
  have := key m⁻¹ (M.inv_mem hm) _ hh
  simpa [mul_assoc] using this

end CFSG.GH74.GLS.Th2.CaseI

namespace CFSG.GH74.GLS

open Subgroup CFSG.ABGLocalTools

theorem caseI_M_of_leaves (h84 : B_thm2_l84) (h85 : B_thm2_p85) (h812 : B_thm2_p812)
    (hPU3 : B_thm2_PU3) : B_thm2_caseI_M := by
  intro G _ _ hG x y K T S M h
  have hchoice : Th2Choice x y K T S M := Or.inl h
  have hKM : K ≤ M := Subgroup.le_normalizer.trans h.le_M
  obtain ⟨hQ84, -⟩ := h84 G hG x y K T S M hchoice hKM
  obtain ⟨L, hL⟩ := Th2.exists_minSubnormal hKM
  obtain ⟨hLcomp, hLeq⟩ := h85 G hG x y K T S M hchoice hKM hQ84 L hL
  obtain ⟨hgam, hrk⟩ := h812 G hG x y K T S M hchoice hKM hQ84 L hL hLcomp hLeq
  have hLnorm := hPU3 G hG x y K T S M hchoice hKM hQ84 L hL hLcomp hLeq hgam hrk
  have hKL : K ≤ L := hL.1
  have hQM : T ⊓ CxK x K ≤ M := hQ84.le.trans inf_le_left
  have h1 : gammaK 2 (T ⊓ CxK x K) 1 ≤ normalizer (K : Set G) :=
    Th2.CaseI.gammaK_le_normalizer_of_standard h.standard h.sylowQ
  have h2 : pPrimeCoreOf 2 L ≤ normalizer (K : Set G) :=
    Th2.CaseI.pPrimeCoreOf_le_normalizer hLnorm hQM hrk h1
  have h3 : L ≤ normalizer (K : Set G) :=
    hLeq.le.trans (sup_le h2 Subgroup.le_normalizer)
  refine le_antisymm ?_ h.le_M
  exact Th2.CaseI.le_normalizer_of_two_elements h.standard.1.1 hKL hLnorm
    (fun s hs k hk => Th2.CaseI.mem_of_two_element hKL hLeq h3 hs hk)

end CFSG.GH74.GLS
