module

public import CFSG.ClassicalInvolution.AschTight.Hall196Wr2
public import CFSG.ClassicalInvolution.Asc77.AscL62Main
public import CFSG.ClassicalInvolution.AschTight.Hall196Wr

public section

namespace CFSG.ClassicalInvolution.Disconnected.AschTight.Hall196

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight

variable {G : Type} [Group G] [Finite G] {p f : ℕ} [Fact p.Prime] {K : Subgroup G} {z : G}
  {S : Sylow 2 G} {W L : Subgroup G} {t : G} {V : Subgroup G}

theorem ne_of_sec19DataT (hDT : Sec19DataT p f K z S W L t V) : L ≠ K := by
  rintro rfl
  exact hDT.ne ((isUniqueInvolution_of_tight hDT.tight.toTightBranch).eq hDT.invL).symm

theorem le_normalizer_of_sec19DataT (hDT : Sec19DataT p f K z S W L t V) :
    V ≤ Subgroup.normalizer (K : Set G) := by
  rw [normalizer_eq_centralizer_of_tight hDT.tight.toTightBranch]
  exact hDT.leW.trans (hDT.hWS.trans hDT.hSz)

theorem inf_eq_bot_of_sec19DataT (hDT : Sec19DataT p f K z S W L t V) : K ⊓ V = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hodd := odd_card_inf_of_tight hDT.tight.toTightBranch hDT.memL
    (CoreAssembly.mem_conjClass_self K) (ne_of_sec19DataT hDT)
  have hdvd : Nat.card ↥(K ⊓ V) ∣ Nat.card ↥(L ⊓ K) :=
    Subgroup.card_dvd_of_le (le_inf (inf_le_right.trans (le_of_sec19DataT hDT)) inf_le_left)
  have h2 : IsPGroup 2 ↥(K ⊓ V) :=
    (S.isPGroup'.to_le (hDT.leW.trans hDT.hWS)).to_le inf_le_right
  obtain ⟨k, hk⟩ := h2.exists_card_eq
  rcases k with _ | k
  · rw [pow_zero] at hk
    exact Subgroup.eq_bot_of_card_eq _ hk
  · exfalso
    rw [hk] at hdvd
    have h3 : 2 ∣ Nat.card ↥(L ⊓ K) := (dvd_pow_self 2 (Nat.succ_ne_zero k)).trans hdvd
    exact (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr h3)

theorem card_sup_of_sec19DataT (hDT : Sec19DataT p f K z S W L t V) :
    Nat.card ↥(K ⊔ V) = Nat.card K * Nat.card V := by
  have h := card_sup_mul_card_inf' (le_normalizer_of_sec19DataT hDT)
  rw [inf_eq_bot_of_sec19DataT hDT, Subgroup.card_bot, mul_one] at h
  exact h

theorem card_le_of_le_sup (hDT : Sec19DataT p f K z S W L t V) {T : Subgroup G}
    (hT : T ≤ K ⊔ V) (hT2 : IsPGroup 2 T) :
    Nat.card T ≤ Nat.card ↥((S : Subgroup G) ⊓ K) * Nat.card V := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨Q₀, hQ⟩ := hDT.sylow
  have hR : Nat.card ↥((S : Subgroup G) ⊓ K) = 2 ^ (Nat.card K).factorization 2 := by
    rw [inf_eq_map_of_sec19Data hQ,
      Subgroup.card_map_of_injective K.subtype_injective, Sylow.card_eq_multiplicity]
  obtain ⟨a, ha⟩ := hT2.exists_card_eq
  have hdvd : Nat.card T ∣ Nat.card K * Nat.card V := by
    rw [← card_sup_of_sec19DataT hDT]
    exact Subgroup.card_dvd_of_le hT
  have hK0 : Nat.card K ≠ 0 := Nat.card_pos.ne'
  have hsplit := Nat.ordProj_mul_ordCompl_eq_self (Nat.card K) 2
  have hcop : Nat.Coprime (2 ^ a) (Nat.card K / 2 ^ (Nat.card K).factorization 2) :=
    Nat.Coprime.pow_left a (Nat.coprime_ordCompl Nat.prime_two hK0)
  have h1 : 2 ^ a ∣ 2 ^ (Nat.card K).factorization 2 * Nat.card V := by
    rw [← ha]
    have h2 : Nat.card K * Nat.card V = (2 ^ (Nat.card K).factorization 2 * Nat.card V) *
        (Nat.card K / 2 ^ (Nat.card K).factorization 2) := by
      conv_lhs => rw [← hsplit]
      ring
    rw [h2] at hdvd
    exact (ha ▸ hcop).dvd_of_dvd_mul_right hdvd
  rw [ha, hR]
  exact Nat.le_of_dvd (Nat.mul_pos (by positivity) Nat.card_pos) h1

theorem isSylow2In_sup_of_sec19DataT (hDT : Sec19DataT p f K z S W L t V) {R₀ : Subgroup G}
    (hR₀ : IsSylow2In R₀ K) (hVR₀ : V ≤ Subgroup.normalizer (R₀ : Set G)) :
    IsSylow2In (R₀ ⊔ V) (K ⊔ V) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hV2 : IsPGroup 2 V := S.isPGroup'.to_le (hDT.leW.trans hDT.hWS)
  have hRsyl : IsSylow2In ((S : Subgroup G) ⊓ K) K := by
    obtain ⟨Q₀, hQ⟩ := hDT.sylow
    rw [inf_eq_map_of_sec19Data hQ]
    refine ⟨Subgroup.map_subtype_le _, Q₀.isPGroup'.map _, fun R' hR'K hR'2 hle => ?_⟩
    have hP : (Q₀ : Subgroup K) ≤ R'.subgroupOf K := Subgroup.map_le_iff_le_comap.mp hle
    have := Q₀.is_maximal' hR'2.comap_subtype hP
    rw [← Subgroup.map_subgroupOf_eq_of_le hR'K]
    exact congrArg (Subgroup.map K.subtype) this
  have hcard : Nat.card ↥(R₀ ⊔ V) = Nat.card ↥((S : Subgroup G) ⊓ K) * Nat.card V := by
    have h := card_sup_mul_card_inf' hVR₀
    have hbot : R₀ ⊓ V = ⊥ := by
      have := inf_eq_bot_of_sec19DataT hDT
      exact eq_bot_iff.mpr ((inf_le_inf_right V hR₀.1).trans this.le)
    rw [hbot, Subgroup.card_bot, mul_one, IsSylow2In.natCard_eq hR₀ hRsyl] at h
    exact h
  refine ⟨sup_le_sup_right hR₀.1 V, IsPGroup.to_sup_of_normal_left' hR₀.2.1 hV2 hVR₀,
    fun T hT hT2 hle => ?_⟩
  have h1 := card_le_of_le_sup hDT hT hT2
  rw [← hcard] at h1
  exact (Subgroup.eq_of_le_of_card_ge hle h1).symm

theorem four_le_card_of_sec19DataT (hDT : Sec19DataT p f K z S W L t V) : 4 ≤ Nat.card V := by
  obtain ⟨R', hR', -, hcard⟩ := exists_isSylow2In_of_sec19DataT hDT
  have h8 := (exists_ne_comm_of_mem_rSet hDT.tight.branch.odd hDT.tight.branch.five
    hDT.tight.branch.member (mem_RSet_of_isSylow2In hDT.memL hR')).2
  omega

theorem isWreathed_inf_sup [IsSimpleGroup G] (hDT : Sec19DataT p f K z S W L t V) :
    IsWreathed (((S : Subgroup G) ⊓ K) ⊔ V) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have ht := hDT.tight
  have htb := ht.toTightBranch
  have hI := isUniqueInvolution_of_tight htb
  have hΩ := hypOmegaMod_of_tightD ht
  have hLtwin : L ∉ twinSet (CoreAssembly.conjClass K) K := by
    rintro ⟨-, z', hKz', hLz'⟩
    exact hDT.ne ((hDT.invL.eq hLz').trans (hI.eq hKz').symm)
  have hVsyl := isSylow2In_inf_centralizer hDT
  have h4 := four_le_card_of_sec19DataT hDT
  have hcardt : Nat.card (Subgroup.zpowers t) = 2 := by
    rw [Nat.card_zpowers]
    exact orderOf_eq_prime (by rw [_root_.sq]; exact hDT.invL.sq) hDT.invL.ne_one
  rcases Asc77.l6_2 p f ht.branch.odd ht.branch.five G _ hΩ K (CoreAssembly.mem_conjClass_self K)
      z hI L hDT.memL hLtwin t hDT.invL V hVsyl hDT.memT with
    ⟨hV, -⟩ | ⟨hV, -⟩ | ⟨-, -, R₀, hR₀, hR₀K, hVR₀, hw⟩ | ⟨hVR, -⟩
  · rw [hV, hcardt] at h4
    omega
  · rw [hV, hcardt] at h4
    omega
  ·
    obtain ⟨J, hJ, hR₀J⟩ := exists_isSylow2In_of_mem_RSet hR₀
    have hJK : J = K := by
      by_contra hJK
      have hodd := odd_card_inf_of_tight htb hJ (CoreAssembly.mem_conjClass_self K) hJK
      have h8 := (exists_ne_comm_of_mem_rSet ht.branch.odd ht.branch.five ht.branch.member
        hR₀).2
      obtain ⟨k, hk⟩ := hR₀J.2.1.exists_card_eq
      have hdvd : Nat.card R₀ ∣ Nat.card ↥(J ⊓ K) :=
        Subgroup.card_dvd_of_le (le_inf hR₀J.1 hR₀K)
      rcases k with _ | k
      · rw [hk] at h8
        omega
      · rw [hk] at hdvd
        exact (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr
          ((dvd_pow_self 2 (Nat.succ_ne_zero k)).trans hdvd))
    rw [hJK] at hR₀J
    have hRsyl : IsSylow2In ((S : Subgroup G) ⊓ K) K := by
      obtain ⟨Q₀, hQ⟩ := hDT.sylow
      rw [inf_eq_map_of_sec19Data hQ]
      refine ⟨Subgroup.map_subtype_le _, Q₀.isPGroup'.map _, fun R' hR'K hR'2 hle => ?_⟩
      have hP : (Q₀ : Subgroup K) ≤ R'.subgroupOf K := Subgroup.map_le_iff_le_comap.mp hle
      have := Q₀.is_maximal' hR'2.comap_subtype hP
      rw [← Subgroup.map_subgroupOf_eq_of_le hR'K]
      exact congrArg (Subgroup.map K.subtype) this
    have hVN : V ≤ Subgroup.normalizer ((((S : Subgroup G) ⊓ K) : Subgroup G) : Set G) := by
      intro v hv
      have hvS : v ∈ (S : Subgroup G) := hDT.leW.trans hDT.hWS hv
      have hvK := le_normalizer_of_sec19DataT hDT hv
      rw [Subgroup.mem_normalizer_iff] at hvK ⊢
      intro x
      constructor
      · rintro ⟨hxS, hxK⟩
        exact ⟨S.mul_mem (S.mul_mem hvS hxS) (S.inv_mem hvS), (hvK x).mp hxK⟩
      · rintro ⟨hxS, hxK⟩
        refine ⟨?_, (hvK x).mpr hxK⟩
        have e : x = v⁻¹ * (v * x * v⁻¹) * v := by group
        rw [e]
        exact S.mul_mem (S.mul_mem (S.inv_mem hvS) hxS) hvS
    exact IsWreathed.of_isSylow2In (isSylow2In_sup_of_sec19DataT hDT hR₀J hVR₀) hw
      (isSylow2In_sup_of_sec19DataT hDT hRsyl hVN)
  ·
    exfalso
    obtain ⟨J, hJ, hVJ⟩ := exists_isSylow2In_of_mem_RSet hVR
    have hJL : J = L := eq_of_mem_of_sec19DataT hDT hJ (hVJ.1 hDT.memT)
    subst hJL
    obtain ⟨R', hR', hVR', hcard⟩ := exists_isSylow2In_of_sec19DataT hDT
    have := hVJ.eq_of_le hR'.2.1 hR'.1 hVR'
    rw [this] at hcard
    have hpos : 0 < Nat.card V := Nat.card_pos
    omega

end CFSG.ClassicalInvolution.Disconnected.AschTight.Hall196
