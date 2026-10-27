module

public import CFSG.ClassicalInvolution.Q3.Q3URPat
public import CFSG.ClassicalInvolution.Q3.Q3URNodes
public import CFSG.ClassicalInvolution.Q3.Q3WASNorm

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3W

open CFSG.Open hiding StatedLieTag StatedLieAdmissible StatedSU
open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.RouteD
  CFSG.ClassicalInvolution.RouteD.Gaps CFSG.ClassicalInvolution.Models CFSG.ClassicalInvolution.Phan
  CFSG.Assembly.LowTwoRank CFSG.LieType.Universal CFSG.LieType.BorelTits
open CFSG.ClassicalInvolution.ModelFacts.UnitaryAut (conjSign)
open scoped MatrixGroups

section Std

variable {G : Type} [Group G]

theorem fix_of_stdpair3U {K β : Subgroup G} {z t : G} (hz : IsClassicalMember3 K z)
    (hwβ : IsClassicalMember3 β t)
    (hW : ∃ W : Subgroup G, UnitaryBlockStandardPair (GaloisField 3 2) 3 1 W K β) :
    t * z * t⁻¹ = z := by
  obtain ⟨W, hW⟩ := hW
  have hzt : z * t = t * z :=
    unitaryStandardPair_involutions_commute card_gf9 (by norm_num) hW hz.mem hwβ.mem
      hz.orderOf_eq_two hwβ.orderOf_eq_two
  rw [mul_inv_eq_iff_eq_mul]
  exact hzt.symm

variable [Finite G] {Ω : Set (Subgroup G)} {K : Subgroup G} {z : G}

theorem UNodes3.locImg_eq {m : ℕ} {c : UCtx3 m Ω K z} (nd : UNodes3 c) {a : ℕ} (ha : a < m) :
    locImg Ω z (nd.j a) =
      (blockEmb2 (GaloisField 3 2) 3 1 m ⟨a, ha⟩).range.map c.d.ψ := by
  rw [nd.img a ha, range_blockEmb2_eq_LcU_nodePair two_ne_zero_gf9 ha]

end Std

section Partner

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {K : Subgroup G} {z : G}

theorem UCtx3.commutes_partner_iff {m : ℕ} (c : UCtx3 m Ω K z)
    (hMFZ : RouteD.Gaps.FundNoncentral 3) {ι : Type}
    (D : LieSystemData3 ι (locQuot Ω z) (locFamily Ω z))
    (hsingle : ∀ L ∈ Ω, ∃ g : G, L = conjSub g K) {β : Subgroup G} (hβ : β ∈ Ω) {t : G}
    (hwβ : IsClassicalMember3 β t) (hnK : ¬ Commutes K β) {N : Subgroup G} (hN : N ∈ Ω)
    (hNK : Commutes N K) : Commutes N β ↔ N ≤ Subgroup.centralizer ({t} : Set G) := by
  have hconj := c.hΩ.conjInvariant
  obtain ⟨h, hh⟩ := hsingle β hβ
  have ht_eq : t = h * z * h⁻¹ := involution_unique3 hwβ (hh ▸ c.hz.conj h)
  have hP1t : LocalOddCentral Ω {t} := by
    rw [ht_eq]; exact Gaps.localOddCentral_conj hconj h z c.hP1
  have hO3t : LocalOddThreeFree3 Ω t := by
    rw [ht_eq]; exact localOddThreeFree3_conj hconj h z c.hO3
  obtain ⟨Dt⟩ := exists_lieSystemData_conj3 hconj h z D
  rw [← ht_eq] at Dt
  exact commutes_iff_le_centralizer3 hMFZ c.hΩ c.hex hP1t hO3t Dt hβ hwβ hN hNK hnK

theorem UCtx3.partner_pattern {m : ℕ} (c : UCtx3 m Ω K z) (hm : 4 ≤ m) (nd : UNodes3 c)
    (hMFZ : RouteD.Gaps.FundNoncentral 3) {ι : Type}
    (D : LieSystemData3 ι (locQuot Ω z) (locFamily Ω z))
    (hsingle : ∀ L ∈ Ω, ∃ g : G, L = conjSub g K)
    {β : Subgroup G} (hβ : β ∈ Ω) {t : G} (hwβ : IsClassicalMember3 β t)
    (hnK : ¬ Commutes K β) (htz : t * z * t⁻¹ = z)
    (hfixed : ∀ (a : ℕ) (ha : a < m), partnerFixed m ⟨a, ha⟩ → Commutes β (nd.j a))
    (hfirst : ¬ Commutes β (nd.j 0)) :
    ∃ w : ZMod 2,
      (∀ x, locAut c.hΩ.conjInvariant htz (c.d.ψ x) =
        c.d.ψ (conjSign card_gf9 (partnerSigns m w) x)) ∧
      (w = 0 ↔ ∀ A : Su (GaloisField 3 2) 3 1 2,
        locAut c.hΩ.conjInvariant htz
            (c.d.ψ (blockEmb2 (GaloisField 3 2) 3 1 m ⟨m - 2, by omega⟩ A)) =
          c.d.ψ (blockEmb2 (GaloisField 3 2) 3 1 m ⟨m - 2, by omega⟩ A)) ∧
      ∀ T : Pair (m + 1),
        ((LcU (GaloisField 3 2) 3 1 T).map c.d.ψ).map
            (locAut c.hΩ.conjInvariant htz).toMonoidHom =
          (LcU (GaloisField 3 2) 3 1 T).map c.d.ψ := by
  classical
  have h2 := two_ne_zero_gf9
  have hΩ := c.hΩ
  have hex := c.hex
  have hconj := hΩ.conjInvariant
  have htt : t * t = 1 := mul_self_of_isClassicalMember3 hwβ
  have attach := fun (N : Subgroup G) (hN : N ∈ Ω) (hNK : Commutes N K) =>
    c.commutes_partner_iff hMFZ D hsingle hβ hwβ hnK hN hNK
  have hmemΩz : ∀ L ∈ centralizingMembers Ω {z}, conjSub t L ∈ centralizingMembers Ω {z} :=
    fun L hL => conjSub_mem_centralizingMembers3 hconj htz hL
  set σ := locAut hconj htz with hσdef
  have hσ2 : ∀ y, σ (σ y) = y := locAut_locAut hconj htz htt
  set ψ := c.d.ψ with hψ
  have hcK : IsClassicalMember3 (conjSub t K) z := by
    have := c.hz.conj t
    rwa [htz] at this
  have hmem : conjSub t K ∈ centralizingMembers Ω {z} :=
    ⟨hconj t K c.hK, isSubnormal_le hcK.subnormal⟩
  have hKt : conjSub t K = K :=
    eq_of_locImg_le_Q₀U3 c.hm hΩ hex c.hK c.hz c.hP1 c.hO3 c.d hmem
      (locImg_self_le_Q₀U3 c.hm (hconj t K c.hK) hcK c.d)
  have hKt' : conjSub t⁻¹ K = K := by
    have := congrArg (conjSub t⁻¹) hKt
    rw [conjSub_inv_conjSub] at this
    exact this.symm
  have hconjne : ∀ L, conjSub t L ≠ K ↔ L ≠ K := by
    intro L
    constructor
    · intro hne heq
      apply hne
      rw [heq, hKt]
    · intro hne heq
      apply hne
      have := congrArg (conjSub t⁻¹) heq
      rwa [conjSub_inv_conjSub, hKt'] at this
  have hstab : ∀ x, σ (ψ x) ∈ ψ.range := by
    have hS : (⨆ i : Fin m, (blockEmb2 (GaloisField 3 2) 3 1 m i).range) ≤
        (ψ.range).comap (σ.toMonoidHom.comp ψ) := by
      refine iSup_le fun i => ?_
      rintro _ ⟨A, rfl⟩
      have hyL : ψ (blockEmb2 (GaloisField 3 2) 3 1 m i A) ∈ locImg Ω z (nd.j i.val) := by
        rw [nd.locImg_eq i.isLt]
        exact ⟨_, ⟨A, rfl⟩, rfl⟩
      have h1 : σ (ψ (blockEmb2 (GaloisField 3 2) 3 1 m i A)) ∈
          locImg Ω z (conjSub t (nd.j i.val)) := by
        rw [← locAut_locImg hconj htz]
        exact ⟨_, hyL, rfl⟩
      obtain ⟨R', -, hR'⟩ := exists_root_of_neU3 c.hm hΩ hex c.hK c.hz c.hP1 c.hO3 c.d
        (hmemΩz _ (nd.mem i.val i.isLt)) ((hconjne _).mpr (nd.ne_K i.val i.isLt))
      rw [hR'] at h1
      obtain ⟨y', -, hy'⟩ := h1
      exact ⟨y', hy'⟩
    intro x
    have hx : x ∈ ⨆ i : Fin m, (blockEmb2 (GaloisField 3 2) 3 1 m i).range := by
      rw [iSup_range_blockEmb2 card_gf9 (by norm_num : 3 ^ 1 ≠ 2) m]
      exact Subgroup.mem_top x
    exact hS hx
  have hfixedσ : ∀ a (ha : a < m), Commutes β (nd.j a) →
      ∀ A : Su (GaloisField 3 2) 3 1 2,
      σ (ψ (blockEmb2 (GaloisField 3 2) 3 1 m ⟨a, ha⟩ A)) =
        ψ (blockEmb2 (GaloisField 3 2) 3 1 m ⟨a, ha⟩ A) := by
    intro a ha hcomm A
    have hle : nd.j a ≤ Subgroup.centralizer ({t} : Set G) := fun n hn => by
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact (hcomm t hwβ.mem n hn).symm
    exact (locAut_fixed_iff3 hΩ hex c.hP1 c.hO3 htz (nd.mem a ha)).mp hle _
      (by rw [nd.locImg_eq ha]; exact ⟨_, ⟨A, rfl⟩, rfl⟩)
  have hfix : ∀ a : Fin m, partnerFixed m a → ∀ A : Su (GaloisField 3 2) 3 1 2,
      σ (ψ (blockEmb2 (GaloisField 3 2) 3 1 m a A)) = ψ (blockEmb2 (GaloisField 3 2) 3 1 m a A) :=
    fun a ha A => hfixedσ a.val a.isLt (hfixed a.val a.isLt ha) A
  have hmove : ∃ A : Su (GaloisField 3 2) 3 1 2,
      σ (ψ (blockEmb2 (GaloisField 3 2) 3 1 m ⟨0, by omega⟩ A)) ≠
        ψ (blockEmb2 (GaloisField 3 2) 3 1 m ⟨0, by omega⟩ A) := by
    by_contra hcon
    push Not at hcon
    have hfx : ∀ a ∈ locImg Ω z (nd.j 0), σ a = a := by
      intro a ha
      rw [nd.locImg_eq (by omega)] at ha
      obtain ⟨_, ⟨A, rfl⟩, rfl⟩ := ha
      exact hcon A
    have hle := (locAut_fixed_iff3 hΩ hex c.hP1 c.hO3 htz (nd.mem 0 (by omega))).mpr hfx
    exact hfirst (Gaps.commutes_symm
      ((attach (nd.j 0) (nd.mem 0 (by omega)).1
        (Gaps.commutes_symm (nd.commK 0 (by omega)))).mpr hle))
  obtain ⟨w, hpat, hiff, hroots⟩ := unitary_partner_pattern_roots3 card_gf9 (by norm_num)
    le_rfl su2_pow_three_mem_commutator
    (fun x hx => center_orderOf_not_dvd_three_su3 (by omega) hx) hm ψ c.d.ker_le σ hσ2 hstab
    hfix hmove
  exact ⟨w, hpat, hiff, hroots⟩

end Partner

end CFSG.ClassicalInvolution.Q3.Q3W
