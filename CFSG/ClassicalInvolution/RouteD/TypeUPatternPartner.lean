module

public import CFSG.ClassicalInvolution.RouteD.TypeUPatternModel
public import CFSG.ClassicalInvolution.RouteD.GapsEnd4Aux
public import CFSG.ClassicalInvolution.RouteD.GapsAut
public import CFSG.ClassicalInvolution.RouteD.TypeUChain

public section

namespace CFSG.ClassicalInvolution.RouteD

open CFSG.Open CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Models
  CFSG.ClassicalInvolution.Phan CFSG.Assembly.LowTwoRank CFSG.LieType.Universal
  CFSG.LieType.BorelTits CFSG.ClassicalInvolution.RouteD.Gaps
  CFSG.ClassicalInvolution.ModelFacts.UnitaryAut

variable {p f m : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
  {K : Subgroup G} {z : G}

theorem UCtx.partner_setup (c : UCtx p f m Ω K z) (nd : UNodes c) (hMFZ : FundNoncentral p)
    (hshape : LocalShapeU p f m Ω z) (hsingle : ∀ L ∈ Ω, ∃ g : G, L = conjSub g K)
    {β : Subgroup G} (hβ : β ∈ Ω) {t : G} (hwβ : IsClassicalMember p f β t) (hnK : ¬ Commutes K β)
    (hpair : ∃ W : Subgroup G, UnitaryBlockStandardPair (GaloisField p (2 * f)) p f W K β) :
    ∃ htz : t * z * t⁻¹ = z,
      (∀ y, locAut c.hΩ.conjInvariant htz (locAut c.hΩ.conjInvariant htz y) = y) ∧
      (∀ x, locAut c.hΩ.conjInvariant htz (c.d.ψ x) ∈ c.d.ψ.range) ∧
      (∀ L ∈ centralizingMembers Ω {z}, conjSub t L ∈ centralizingMembers Ω {z}) ∧
      ∀ N ∈ centralizingMembers Ω {z}, Commutes N K →
        ((∀ a ∈ locImg Ω z N, locAut c.hΩ.conjInvariant htz a = a) ↔ Commutes N β) := by
  classical
  have h2 : (2 : GaloisField p f) ≠ 0 := two_ne_zero_of_charP_ne_two c.hp2
  have hΩ := c.hΩ
  have hex := c.hex
  have hconj := hΩ.conjInvariant
  obtain ⟨W, hW⟩ := hpair
  have hz2 : orderOf z = 2 := c.hz.orderOf_eq_two
  have ht2 : orderOf t = 2 := hwβ.orderOf_eq_two
  have hzt : z * t = t * z :=
    unitaryStandardPair_involutions_commute c.card_eq c.hp2 hW c.hz.mem hwβ.mem hz2 ht2
  have htz : t * z * t⁻¹ = z := by rw [mul_inv_eq_iff_eq_mul]; exact hzt.symm
  have htt : t * t = 1 := by
    rw [← pow_two]
    have := pow_orderOf_eq_one t
    rwa [ht2] at this
  obtain ⟨D, hDcard, i₀, i₁, hne01, ht₀, hr₀, ht₁, hr₁⟩ := hshape
  obtain ⟨h, hh⟩ := hsingle β hβ
  have ht_eq : t = h * z * h⁻¹ :=
    unique_involution_of_isClassicalMember h2 (hex β hβ) hwβ (hh ▸ c.hz.conj h)
  have hP1t : LocalOddCentral Ω {t} := by
    rw [ht_eq]; exact localOddCentral_conj hconj h z c.hP1
  obtain ⟨Dt, -⟩ := exists_lieSystemData_conj hconj h z D
  have attach : ∀ N : Subgroup G, N ∈ Ω → Commutes N K →
      (Commutes N β ↔ N ≤ Subgroup.centralizer ({t} : Set G)) := by
    intro N hN hNK
    rw [ht_eq] at hwβ ⊢
    exact commutes_iff_le_centralizer hMFZ hΩ hex (by rw [← ht_eq]; exact hP1t) Dt hβ hwβ hN hNK
      hnK
  have hconj_t : centralizingMembers Ω {z} = conjSub t '' centralizingMembers Ω {z} := by
    have := centralizingMembers_conj hconj t z
    rwa [htz] at this
  have hmemΩz : ∀ L ∈ centralizingMembers Ω {z}, conjSub t L ∈ centralizingMembers Ω {z} := by
    intro L hL
    have : conjSub t L ∈ conjSub t '' centralizingMembers Ω {z} := ⟨L, hL, rfl⟩
    rwa [← hconj_t] at this
  have hσ2 : ∀ y, locAut hconj htz (locAut hconj htz y) = y := locAut_locAut hconj htz htt
  have hKt : conjSub t K = K := by
    have hcK : IsClassicalMember p f (conjSub t K) z := by
      have := c.hz.conj t
      rwa [htz] at this
    have hmem : conjSub t K ∈ centralizingMembers Ω {z} :=
      ⟨hconj t K c.hK, le_centralizer_of_isClassicalMember hcK⟩
    exact typeU_eq_of_locImg_le_Q₀ c.hp2 c.hq c.hm c.hΩ c.hex c.hK c.hz c.hP1 c.d hmem
      (typeU_locImg_self_le_Q₀ c.hp2 c.hq c.hm (hconj t K c.hK) hcK c.d)
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
  have himg : ∀ a (ha : a < m), locImg Ω z (nd.j a) =
      (blockEmb2 (GaloisField p (2 * f)) p f m ⟨a, ha⟩).range.map c.d.ψ := fun a ha => by
    rw [nd.img a ha, range_blockEmb2_eq_LcU_nodePair c.h2 ha]
  have hstab : ∀ x, locAut hconj htz (c.d.ψ x) ∈ c.d.ψ.range := by
    have hS : (⨆ i : Fin m, (blockEmb2 (GaloisField p (2 * f)) p f m i).range) ≤
        (c.d.ψ.range).comap ((locAut hconj htz).toMonoidHom.comp c.d.ψ) := by
      refine iSup_le fun i => ?_
      rintro _ ⟨A, rfl⟩
      have hyL : c.d.ψ (blockEmb2 (GaloisField p (2 * f)) p f m i A) ∈ locImg Ω z (nd.j i.val) := by
        rw [himg i.val i.isLt]
        exact ⟨_, ⟨A, rfl⟩, rfl⟩
      have h1 : locAut hconj htz (c.d.ψ (blockEmb2 (GaloisField p (2 * f)) p f m i A)) ∈
          locImg Ω z (conjSub t (nd.j i.val)) := by
        rw [← locAut_locImg hconj htz]
        exact ⟨_, hyL, rfl⟩
      obtain ⟨R', -, hR'⟩ := typeU_exists_root_of_ne c.hp2 c.hq c.hm c.hΩ c.hex c.hK c.hz c.hP1
        c.d (hmemΩz _ (nd.mem i.val i.isLt)) ((hconjne _).mpr (nd.ne_K i.val i.isLt))
      rw [hR'] at h1
      obtain ⟨y', -, hy'⟩ := h1
      exact ⟨y', hy'⟩
    intro x
    have hx : x ∈ ⨆ i : Fin m, (blockEmb2 (GaloisField p (2 * f)) p f m i).range := by
      rw [iSup_range_blockEmb2 c.card_eq (prime_pow_ne_two_of_ne_two c.hp2 f) m]
      exact Subgroup.mem_top x
    exact hS hx
  refine ⟨htz, hσ2, hstab, hmemΩz, fun N hN hNK => ?_⟩
  exact (locAut_fixed_iff hΩ c.hP1 htz hN).symm.trans (attach N hN.1 hNK).symm

theorem UCtx.partner_pattern (c : UCtx p f m Ω K z) (hm : 4 ≤ m) (nd : UNodes c)
    (hMFZ : FundNoncentral p) (hshape : LocalShapeU p f m Ω z)
    (hsingle : ∀ L ∈ Ω, ∃ g : G, L = conjSub g K) {β : Subgroup G} (hβ : β ∈ Ω) {t : G}
    (hwβ : IsClassicalMember p f β t) (hnK : ¬ Commutes K β)
    (hpair : ∃ W : Subgroup G, UnitaryBlockStandardPair (GaloisField p (2 * f)) p f W K β)
    (hfixed : ∀ (a : ℕ) (ha : a < m), partnerFixed m ⟨a, ha⟩ → Commutes β (nd.j a))
    (hfirst : ¬ Commutes β (nd.j 0)) :
    ∃ (htz : t * z * t⁻¹ = z) (w : ZMod 2),
      (∀ x, locAut c.hΩ.conjInvariant htz (c.d.ψ x) =
        c.d.ψ (conjSign c.card_eq (partnerSigns m w) x)) ∧
      (w = 0 → Commutes β (nd.j (m - 2))) ∧
      ∀ a, a < m → conjSub t (nd.j a) = nd.j a := by
  obtain ⟨htz, hσ2, hstab, hmemΩz, hfixiff⟩ :=
    c.partner_setup nd hMFZ hshape hsingle hβ hwβ hnK hpair
  have himg : ∀ a (ha : a < m), locImg Ω z (nd.j a) =
      (blockEmb2 (GaloisField p (2 * f)) p f m ⟨a, ha⟩).range.map c.d.ψ := fun a ha => by
    rw [nd.img a ha, range_blockEmb2_eq_LcU_nodePair c.h2 ha]
  have hfixB : ∀ a (ha : a < m), Commutes β (nd.j a) →
      ∀ A : Su (GaloisField p (2 * f)) p f 2,
        locAut c.hΩ.conjInvariant htz (c.d.ψ (blockEmb2 (GaloisField p (2 * f)) p f m ⟨a, ha⟩ A)) =
          c.d.ψ (blockEmb2 (GaloisField p (2 * f)) p f m ⟨a, ha⟩ A) := by
    intro a ha hcomm A
    refine (hfixiff (nd.j a) (nd.mem a ha) (commutes_symm (nd.commK a ha))).mpr
      (commutes_symm hcomm) _ ?_
    rw [himg a ha]
    exact ⟨_, ⟨A, rfl⟩, rfl⟩
  have hfix : ∀ a : Fin m, partnerFixed m a → ∀ A : Su (GaloisField p (2 * f)) p f 2,
      locAut c.hΩ.conjInvariant htz (c.d.ψ (blockEmb2 (GaloisField p (2 * f)) p f m a A)) =
        c.d.ψ (blockEmb2 (GaloisField p (2 * f)) p f m a A) :=
    fun a ha A => hfixB a.val a.isLt (hfixed a.val a.isLt ha) A
  have hmove : ∃ A : Su (GaloisField p (2 * f)) p f 2,
      locAut c.hΩ.conjInvariant htz
          (c.d.ψ (blockEmb2 (GaloisField p (2 * f)) p f m ⟨0, by omega⟩ A)) ≠
        c.d.ψ (blockEmb2 (GaloisField p (2 * f)) p f m ⟨0, by omega⟩ A) := by
    by_contra hcon
    push Not at hcon
    have hfx : ∀ a ∈ locImg Ω z (nd.j 0), locAut c.hΩ.conjInvariant htz a = a := by
      intro a ha
      rw [himg 0 (by omega)] at ha
      obtain ⟨_, ⟨A, rfl⟩, rfl⟩ := ha
      exact hcon A
    exact hfirst (commutes_symm ((hfixiff (nd.j 0) (nd.mem 0 (by omega))
      (commutes_symm (nd.commK 0 (by omega)))).mp hfx))
  obtain ⟨w, hpat, hiff, hroots⟩ := unitary_partner_pattern_roots c.card_eq c.hp2 c.hq hm c.d.ψ
    c.d.ker_le (locAut c.hΩ.conjInvariant htz) hσ2 hstab hfix hmove
  refine ⟨htz, w, hpat, fun hw => ?_, fun a ha => ?_⟩
  · refine commutes_symm ((hfixiff (nd.j (m - 2)) (nd.mem (m - 2) (by omega))
      (commutes_symm (nd.commK (m - 2) (by omega)))).mp ?_)
    intro a ha
    rw [himg (m - 2) (by omega)] at ha
    obtain ⟨_, ⟨A, rfl⟩, rfl⟩ := ha
    exact hiff.mp hw A
  · have h1 := locAut_locImg c.hΩ.conjInvariant htz (nd.j a)
    rw [nd.img a ha, hroots] at h1
    rw [← nd.img a ha] at h1
    exact locImg_injOn c.hΩ c.hP1 (hmemΩz _ (nd.mem a ha)) (nd.mem a ha) h1.symm

end CFSG.ClassicalInvolution.RouteD
