module

public import CFSG.ClassicalInvolution.AschTight.Sec6GenAPI2
public import CFSG.ClassicalInvolution.AschTight.Sec6GenTargets

public section

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
  CFSG.ClassicalInvolution.Disconnected.AschTight.Sec6Gen
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}

omit [Finite G] in
theorem oddCoreOf_eq_bot_of_isPGroup {K : Subgroup G} (hK : IsPGroup 2 ↥K) : oddCoreOf K = ⊥ := by
  have h : classicalInvolutionOddCore ↥K = ⊥ := by
    refine le_bot_iff.mp (sSup_le fun N hN => ?_)
    obtain ⟨-, hodd⟩ := hN
    rw [le_bot_iff, Subgroup.eq_bot_iff_forall]
    intro x hx
    obtain ⟨n, hn⟩ := hK x
    have h1 : orderOf x ∣ 2 ^ n := orderOf_dvd_of_pow_eq_one hn
    have h2 : orderOf x ∣ Nat.card N := Subgroup.orderOf_dvd_natCard N hx
    have hcop : Nat.Coprime (2 ^ n) (Nat.card N) :=
      Nat.Coprime.pow_left n (Nat.coprime_two_left.mpr hodd)
    have h3 : orderOf x ∣ 1 := by
      have := Nat.dvd_gcd h1 h2
      rwa [hcop.gcd_eq_one] at this
    exact orderOf_eq_one_iff.mp (Nat.dvd_one.mp h3)
  rw [oddCoreOf, h, Subgroup.map_bot]

theorem twin_commute (hΩ : HypOmegaGen Ω) {K J : Subgroup G} (hK : K ∈ Ω) (hJ : J ∈ Ω)
    (hKJ : K ≠ J) {z : G} (hzK : IsUniqueInvolution K z) (hzJ : IsUniqueInvolution J z)
    (h2K : IsPGroup 2 ↥K) : ∀ x ∈ K, ∀ y ∈ J, x * y = y * x := by
  have hc := comm_le_oddCore_of_twin hΩ hK hJ hKJ hzK hzJ
  have h1 : ⁅K, J⁆ ≤ oddCoreOf K := hc.trans inf_le_left
  rw [oddCoreOf_eq_bot_of_isPGroup h2K] at h1
  have hcomm : ⁅K, J⁆ = ⊥ := le_bot_iff.mp h1
  intro x hx y hy
  have hmem : ⁅x, y⁆ ∈ ⁅K, J⁆ := Subgroup.commutator_mem_commutator hx hy
  rw [hcomm, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at hmem
  exact hmem

theorem twin_inf_eq (hΩ : HypOmegaGen Ω) {K J : Subgroup G} (hK : K ∈ Ω) (hJ : J ∈ Ω)
    (hKJ : K ≠ J) {z : G} (hzK : IsUniqueInvolution K z) (hzJ : IsUniqueInvolution J z)
    (h2K : IsPGroup 2 ↥K) : K ⊓ J = Subgroup.zpowers z := by
  have hz2 : orderOf z = 2 := orderOf_eq_prime (by rw [pow_two]; exact hzK.sq) hzK.ne_one
  have hzle : Subgroup.zpowers z ≤ K ⊓ J :=
    Subgroup.zpowers_le.mpr (Subgroup.mem_inf.mpr ⟨hzK.mem, hzJ.mem⟩)
  have h2KJ : IsPGroup 2 ↥(K ⊓ J) := h2K.to_le inf_le_left
  obtain ⟨n, hn⟩ := h2KJ.exists_card_eq
  have hn1 : n ≤ 1 := by
    have := (hΩ.omega4 K hK J hJ hKJ).1
    rwa [hn, padicValNat.prime_pow] at this
  have hcard2 : Nat.card ↥(K ⊓ J) ≤ 2 := by
    rw [hn]
    calc 2 ^ n ≤ 2 ^ 1 := Nat.pow_le_pow_right (by norm_num) hn1
      _ = 2 := by norm_num
  have hzcard : Nat.card (Subgroup.zpowers z) = 2 := by
    rw [Nat.card_zpowers, hz2]
  have hge : Nat.card ↥(K ⊓ J) ≤ Nat.card (Subgroup.zpowers z) := by
    rw [hzcard]
    exact hcard2
  exact (Subgroup.eq_of_le_of_card_ge hzle hge).symm

omit [Finite G] in
theorem twinSet_eq {K : Subgroup G} (htr : ∀ J ∈ Ω, ∃ g : G, conjSub g K = J) {z : G}
    (hzK : IsUniqueInvolution K z) :
    twinSet Ω K = {J | J ∈ Ω ∧ ∃ g ∈ Subgroup.centralizer ({z} : Set G), conjSub g K = J} := by
  ext J
  constructor
  · rintro ⟨hJΩ, z', hz'K, hz'J⟩
    obtain ⟨g, rfl⟩ := htr J hJΩ
    have hgz : g * z * g⁻¹ = z' := (hzK.conj g).eq hz'J
    have hzz : z = z' := hzK.eq hz'K
    rw [← hzz] at hgz
    have hcomm : g * z = z * g := mul_inv_eq_iff_eq_mul.mp hgz
    refine ⟨hJΩ, g, ?_, rfl⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact hcomm
  · rintro ⟨hJΩ, g, hg, rfl⟩
    rw [Subgroup.mem_centralizer_singleton_iff] at hg
    have hgz : g * z * g⁻¹ = z := by
      rw [mul_inv_eq_iff_eq_mul]
      exact hg
    refine ⟨hJΩ, z, hzK, ?_⟩
    have := hzK.conj g
    rw [hgz] at this
    exact this

omit [Finite G] in
theorem le_centralizer_of_unique {K : Subgroup G} {z : G} (hzK : IsUniqueInvolution K z) :
    K ≤ Subgroup.centralizer ({z} : Set G) := fun _ hw =>
  Subgroup.mem_centralizer_singleton_iff.mpr (hzK.commute_of_mem hw).symm

omit [Finite G] in
theorem twinSet_eq_singleton_iff (hΩc : ConjInvariant Ω) {K : Subgroup G}
    (htr : ∀ J ∈ Ω, ∃ g : G, conjSub g K = J) (hK : K ∈ Ω) {z : G}
    (hzK : IsUniqueInvolution K z) :
    twinSet Ω K = {K} ↔ (K.subgroupOf (Subgroup.centralizer ({z} : Set G))).Normal := by
  rw [twinSet_eq htr hzK]
  constructor
  · intro h
    refine ⟨fun n hn c => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    have hmem : conjSub (c : G) K ∈ {J | J ∈ Ω ∧ ∃ g ∈ Subgroup.centralizer ({z} : Set G),
        conjSub g K = J} := ⟨hΩc _ K hK, c, c.2, rfl⟩
    rw [h, Set.mem_singleton_iff] at hmem
    have : (c : G) * n * (c : G)⁻¹ ∈ conjSub (c : G) K := conj_mem_conjSub hn
    rw [hmem] at this
    simpa using this
  · intro hn
    ext J
    simp only [Set.mem_ofPred_eq, Set.mem_singleton_iff]
    constructor
    · rintro ⟨-, g, hg, rfl⟩
      ext x
      constructor
      · intro hx
        obtain ⟨y, hy, rfl⟩ := hx
        have := hn.conj_mem ⟨y, le_centralizer_of_unique hzK hy⟩ (by
          rw [Subgroup.mem_subgroupOf]; exact hy) ⟨g, hg⟩
        rw [Subgroup.mem_subgroupOf] at this
        simpa [MulAut.conj_apply] using this
      · intro hx
        have := hn.conj_mem ⟨x, le_centralizer_of_unique hzK hx⟩ (by
          rw [Subgroup.mem_subgroupOf]; exact hx) ⟨g, hg⟩⁻¹
        rw [Subgroup.mem_subgroupOf] at this
        refine ⟨g⁻¹ * x * g, by simpa [mul_assoc] using this, ?_⟩
        simp [MulAut.conj_apply, mul_assoc]
    · rintro rfl
      refine ⟨hK, 1, Subgroup.one_mem _, ?_⟩
      ext x
      simp [conjSub]

theorem isSubnormal_of_hypOmegaGen (hΩ : HypOmegaGen Ω) {K : Subgroup G} (hK : K ∈ Ω) {z : G}
    (hzK : IsUniqueInvolution K z) :
    IsSubnormal K (Subgroup.centralizer ({z} : Set G)) := by
  set H : Subgroup G := ⨆ J ∈ twinSet Ω K, J with hH
  have hKtw : K ∈ twinSet Ω K := ⟨hK, z, hzK, hzK⟩
  have hKH : K ≤ H := le_iSup₂_of_le K hKtw le_rfl
  have hJz : ∀ J ∈ twinSet Ω K, IsUniqueInvolution J z := by
    rintro J ⟨-, z', hz'K, hz'J⟩
    rwa [hzK.eq hz'K]
  have hHN : H ≤ Subgroup.normalizer (K : Set G) := by
    refine iSup₂_le fun J hJ => ?_
    by_cases hJK : J = K
    · rw [hJK]
      exact Subgroup.le_normalizer
    · exact le_normalizer_of_twin hΩ hJ.1 hK hJK (hJz J hJ) hzK
  have hHC : H ≤ Subgroup.centralizer ({z} : Set G) :=
    iSup₂_le fun J hJ => le_centralizer_of_unique (hJz J hJ)
  have hnormK : (K.subgroupOf H).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hKH).mpr hHN
  have hle : ∀ d ∈ Subgroup.centralizer ({z} : Set G), ∀ x ∈ H, d * x * d⁻¹ ∈ H := by
    intro d hd x hx
    have hdz : d * z * d⁻¹ = z := by
      rw [Subgroup.mem_centralizer_singleton_iff] at hd
      rw [hd, mul_inv_cancel_right]
    have hmapd : ∀ J ∈ twinSet Ω K, conjSub d J ∈ twinSet Ω K := by
      intro J hJ
      refine ⟨hΩ.conjInvariant d J hJ.1, z, hzK, ?_⟩
      have := (hJz J hJ).conj d
      rwa [hdz] at this
    have hsub : H.map (MulAut.conj d).toMonoidHom ≤ H := by
      rw [hH, Subgroup.map_iSup]
      refine iSup_le fun J => ?_
      rw [Subgroup.map_iSup]
      exact iSup_le fun hJ => le_iSup₂_of_le (conjSub d J) (hmapd J hJ) le_rfl
    exact hsub ⟨x, hx, rfl⟩
  have hnormH : (H.subgroupOf (Subgroup.centralizer ({z} : Set G))).Normal := by
    rw [Subgroup.normal_subgroupOf_iff_le_normalizer hHC]
    intro c hc
    rw [Subgroup.mem_normalizer_iff]
    intro h
    constructor
    · exact hle c hc h
    · intro hch
      have := hle c⁻¹ (Subgroup.inv_mem _ hc) _ hch
      simpa [mul_assoc] using this
  exact IsSubnormal.step hKH hnormK (IsSubnormal.step hHC hnormH (IsSubnormal.refl _))
