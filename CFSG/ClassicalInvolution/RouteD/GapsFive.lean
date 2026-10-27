module

public import CFSG.ClassicalInvolution.ModelFacts.LinearAutMain
public import CFSG.ClassicalInvolution.RouteD.GapsAut
public import CFSG.ClassicalInvolution.RouteD.GapsD4AAmbient
public import CFSG.ClassicalInvolution.RouteD.GapsEnd4Aux
public import CFSG.ClassicalInvolution.RouteD.TypeEFive
public import CFSG.ClassicalInvolution.RouteD.TypeENodes
public import CFSG.ClassicalInvolution.RouteD.TypeERecognition

public section

namespace CFSG.ClassicalInvolution.RouteD.Gaps

open CFSG.Open CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Models
  CFSG.ClassicalInvolution.WeakCT CFSG.ClassicalInvolution.RouteD CFSG.Assembly.LowTwoRank
  CFSG.ClassicalInvolution.ModelFacts.LinearAut
  CFSG.ComponentClassification.CatalogueBHigherLinearAction
open scoped MatrixGroups

section Diag

variable {F : Type} [Field F]

theorem slConjugation_diagGL_blockSL2_eq {m : ℕ} (d : Fin (m + 1) → Fˣ) (a : Fin m)
    (A : SL(2, F)) :
    slConjugation (m + 1) F (diagGL d) (blockSL2 F m a A) =
      blockSL2 F m a (slConjugation 2 F (diagGL fun i : Fin 2 =>
        d ⟨a.val + i.val, by have := a.isLt; have := i.isLt; omega⟩) A) := by
  refine Subtype.ext (Matrix.ext fun i j => ?_)
  rw [slConjugation_diagGL_apply]
  have hmat : ∀ B : SL(2, F), ((blockSL2 F m a B : SL(m + 1, F)) :
      Matrix (Fin (m + 1)) (Fin (m + 1)) F) i j =
      if h : (a.val ≤ i.val ∧ i.val < a.val + 2) ∧ (a.val ≤ j.val ∧ j.val < a.val + 2) then
        (B : Matrix (Fin 2) (Fin 2) F) ⟨i.val - a.val, by omega⟩ ⟨j.val - a.val, by omega⟩
      else (1 : Matrix (Fin (m + 1)) (Fin (m + 1)) F) i j :=
    fun B => CFSG.ClassicalInvolution.Phan.blockMat_apply _ i j
  rw [hmat A, hmat (slConjugation 2 F (diagGL fun i : Fin 2 =>
    d ⟨a.val + i.val, by have := a.isLt; have := i.isLt; omega⟩) A)]
  by_cases h : (a.val ≤ i.val ∧ i.val < a.val + 2) ∧ (a.val ≤ j.val ∧ j.val < a.val + 2)
  · rw [dite_eq_left h, dite_eq_left h, slConjugation_diagGL_apply]
    have hent : ∀ (k : Fin (m + 1)) (hk : a.val ≤ k.val ∧ k.val < a.val + 2),
        d k = d ⟨a.val + (k.val - a.val), by omega⟩ := fun k hk =>
      congrArg d (Fin.ext (by simp only; omega))
    rw [hent i h.1, hent j h.2]
  · rw [dite_eq_right h, dite_eq_right h]
    by_cases hij : i = j
    · subst hij; simp
    · simp [hij]

end Diag


section Partner

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
  {K : Subgroup G} {z : G}

theorem ACtx.partner_normalizes_nodes {m : ℕ} (c : ACtx p f m Ω K z) (hm : 4 ≤ m) (nd : Nodes c)
    (hMFZ : FundNoncentral p) (hcl : LinearAutClassification (GaloisField p f) (m + 1))
    (hshape : LocalShapeA p f m Ω z) (hsingle : ∀ L ∈ Ω, ∃ g : G, L = conjSub g K)
    {β : Subgroup G} (hβ : β ∈ Ω) {t : G} (hwβ : IsClassicalMember p f β t)
    (hnK : ¬ Commutes K β)
    (hpair : ∃ W : Subgroup G, LinearBlockStandardPair (GaloisField p f) W K β)
    (hfixed : ∀ (a : ℕ) (ha : a < m), partnerFixed m ⟨a, ha⟩ → Commutes β (nd.j a))
    (hfirst : ¬ Commutes β (nd.j 0)) :
    ∃ μ : (GaloisField p f)ˣ, (μ = 1 ∨ μ = -1) ∧ ∀ a : ℕ, a < m → conjSub t (nd.j a) = nd.j a := by
  classical
  have h2 := c.two_ne_zero
  have hΩ := c.hΩ
  have hex := c.hex
  have hconj := hΩ.conjInvariant
  obtain ⟨W, hW⟩ := hpair
  have hz2 : orderOf z = 2 := c.hz.orderOf_eq_two
  have ht2 : orderOf t = 2 := hwβ.orderOf_eq_two
  have hzt : z * t = t * z := standardPair_involutions_commute h2 hW c.hz.mem hwβ.mem hz2 ht2
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
  set σ := locAut hconj htz with hσdef
  have hσ2 : ∀ y, σ (σ y) = y := locAut_locAut hconj htz htt
  set ψ := c.d.ψ with hψ
  have hKz : K ∈ centralizingMembers Ω {z} := ⟨c.hK, le_centralizer_of_isClassicalMember c.hz⟩
  have hi₀ : ∀ i : Fin D.card, D.tag i = .PSL → D.rank i = 2 → i = i₀ := by
    intro i hti hri
    by_contra hne
    have hi : i = i₁ := by
      have h1 := i.isLt
      have h2' := i₀.isLt
      have h3 := i₁.isLt
      have h4 : i.val ≠ i₀.val := fun e => hne (Fin.ext e)
      have h5 : i₀.val ≠ i₁.val := fun e => hne01 (Fin.ext e)
      exact Fin.ext (by omega)
    rw [hi, hr₁] at hri
    omega
  have hKt : conjSub t K = K := by
    have hcK : IsClassicalMember p f (conjSub t K) z := by
      have := c.hz.conj t
      rwa [htz] at this
    have hmem : conjSub t K ∈ centralizingMembers Ω {z} :=
      ⟨hconj t K c.hK, le_centralizer_of_isClassicalMember hcK⟩
    obtain ⟨ia, hta, hra, hia⟩ := locImg_eq_range_of_involution hMFZ D hKz c.hz
    obtain ⟨ib, htb, hrb, hib⟩ := locImg_eq_range_of_involution hMFZ D hmem hcK
    have e1 := hi₀ ia hta hra
    have e2 := hi₀ ib htb hrb
    subst e1 e2
    exact locImg_injOn hΩ c.hP1 hmem hKz (hib.trans hia.symm)
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
    have hS : (⨆ R ∈ longRootSet (K := GaloisField p f) c.hn, R) ≤
        (ψ.range).comap (σ.toMonoidHom.comp ψ) := by
      refine iSup₂_le fun R hR y hy => ?_
      obtain ⟨L, hL, hLK, hLR⟩ :=
        exists_member_of_root c.hm c.hodd hΩ c.hK c.hz c.hP1 c.d hR
      have hyL : ψ y ∈ locImg Ω z L := by rw [hLR]; exact ⟨y, hy, rfl⟩
      have h1 : σ (ψ y) ∈ locImg Ω z (conjSub t L) := by
        rw [← locAut_locImg hconj htz L]; exact ⟨_, hyL, rfl⟩
      obtain ⟨R', -, hR'⟩ := exists_root_of_ne c.hm c.hodd hΩ hex c.hK c.hz c.hP1 c.d
        (hmemΩz L hL) ((hconjne L).mpr hLK)
      rw [hR'] at h1
      obtain ⟨y', -, hy'⟩ := h1
      exact ⟨y', hy'⟩
    intro x
    have hx : x ∈ ⨆ R ∈ longRootSet (K := GaloisField p f) c.hn, R := by
      rw [iSup_longRootSet_eq_top h2 c.hn]; exact Subgroup.mem_top x
    exact hS hx
  have himg : ∀ a (ha : a < m), locImg Ω z (nd.j a) =
      (blockSL2 (GaloisField p f) m ⟨a, ha⟩).range.map ψ := fun a ha => by
    rw [nd.img a ha, blockSL2_range_eq_Lc h2 ha]
  have hfixedσ : ∀ a (ha : a < m), Commutes β (nd.j a) → ∀ A : SL(2, GaloisField p f),
      σ (ψ (blockSL2 (GaloisField p f) m ⟨a, ha⟩ A)) =
        ψ (blockSL2 (GaloisField p f) m ⟨a, ha⟩ A) := by
    intro a ha hcomm A
    have hle : nd.j a ≤ Subgroup.centralizer ({t} : Set G) := fun n hn => by
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact (hcomm t hwβ.mem n hn).symm
    exact (locAut_fixed_iff hΩ c.hP1 htz (nd.mem a ha)).mp hle _
      (by rw [himg a ha]; exact ⟨_, ⟨A, rfl⟩, rfl⟩)
  have hfix : ∀ a : Fin m, partnerFixed m a → ∀ A : SL(2, GaloisField p f),
      σ (ψ (blockSL2 (GaloisField p f) m a A)) = ψ (blockSL2 (GaloisField p f) m a A) :=
    fun a ha A => hfixedσ a.val a.isLt (hfixed a.val a.isLt ha) A
  have hmove : ∃ A : SL(2, GaloisField p f),
      σ (ψ (blockSL2 (GaloisField p f) m ⟨0, by omega⟩ A)) ≠
        ψ (blockSL2 (GaloisField p f) m ⟨0, by omega⟩ A) := by
    by_contra hcon
    push Not at hcon
    have hfx : ∀ a ∈ locImg Ω z (nd.j 0), σ a = a := by
      intro a ha
      rw [himg 0 (by omega)] at ha
      obtain ⟨_, ⟨A, rfl⟩, rfl⟩ := ha
      exact hcon A
    have hle := (locAut_fixed_iff hΩ c.hP1 htz (nd.mem 0 (by omega))).mpr hfx
    exact hfirst (commutes_symm
      ((attach (nd.j 0) (nd.mem 0 (by omega)).1 (commutes_symm (nd.commK 0 (by omega)))).mpr hle))
  obtain ⟨μ, hμ, hpat, -⟩ := partner_pattern_amb c.hodd c.h5 hm hcl ψ c.d.ker_le σ hσ2
    hstab hfix hmove
  refine ⟨μ, hμ, fun a ha => ?_⟩
  have hsub : ∀ y ∈ locImg Ω z (nd.j a), σ y ∈ locImg Ω z (nd.j a) := by
    intro y hy
    rw [himg a ha] at hy ⊢
    obtain ⟨_, ⟨A, rfl⟩, rfl⟩ := hy
    rw [hpat]
    obtain ⟨A', hA'⟩ : ∃ A' : SL(2, GaloisField p f),
        slConjugation (m + 1) (GaloisField p f) (partnerDiag m μ)
          (blockSL2 (GaloisField p f) m ⟨a, ha⟩ A) =
        blockSL2 (GaloisField p f) m ⟨a, ha⟩ A' :=
      ⟨_, slConjugation_diagGL_blockSL2_eq (partnerEnt m μ) ⟨a, ha⟩ A⟩
    exact ⟨blockSL2 (GaloisField p f) m ⟨a, ha⟩ A', ⟨A', rfl⟩, by rw [hA']⟩
  have hmapeq : (locImg Ω z (nd.j a)).map σ.toMonoidHom = locImg Ω z (nd.j a) :=
    map_eq_of_involutive σ hσ2 _ hsub
  have h1 := locAut_locImg hconj htz (nd.j a)
  rw [hmapeq] at h1
  exact locImg_injOn hΩ c.hP1 (hmemΩz _ (nd.mem a ha)) (nd.mem a ha) h1.symm

omit [Finite G] in
theorem commute_of_conjSub_eq {L : Subgroup G} {w t : G} (h2 : (2 : GaloisField p f) ≠ 0)
    (hex : classicalInvolutionOddCore L = ⊥) (hL : IsClassicalMember p f L w)
    (ht : conjSub t L = L) : Commute t w := by
  have hcl : IsClassicalMember p f (conjSub t L) (t * w * t⁻¹) := hL.conj t
  rw [ht] at hcl
  have := unique_involution_of_isClassicalMember h2 hex hL hcl
  exact (mul_inv_eq_iff_eq_mul.mp this.symm : t * w = w * t)

theorem ACtx.adapted_partner (c : ACtx p f 5 Ω K z) (hMFZ : FundNoncentral p)
    (hshape : LocalShapeA p f 5 Ω z) (hsingle : ∀ L ∈ Ω, ∃ g : G, L = conjSub g K)
    (nd : Nodes c) :
    ∃ β, IsPartnerE c nd β ∧ ∀ wβ : G, IsClassicalMember p f β wβ → Commute wβ (nd.w 3) := by
  obtain ⟨β, hβ⟩ := c.exists_partnerE nd hsingle
  refine ⟨β, hβ, fun wβ hwβ => ?_⟩
  have hcl : LinearAutClassification (GaloisField p f) (5 + 1) :=
    linearAutClassification c.hp2 c.hq (by norm_num)
  have hfixed : ∀ (a : ℕ) (ha : a < 5), partnerFixed 5 ⟨a, ha⟩ → Commutes β (nd.j a) := by
    intro a ha hfx
    rcases hfx with hfx | ⟨h1, h2⟩
    · have : a = 4 := by simp only at hfx; omega
      subst this
      exact hβ.last
    · exact hβ.mid a (by simpa using h1) (by simp only at h2; omega)
  obtain ⟨μ, -, hnorm⟩ := ACtx.partner_normalizes_nodes c (by norm_num) nd hMFZ hcl hshape hsingle
    hβ.mem hwβ hβ.nK hβ.pK hfixed hβ.n0
  exact commute_of_conjSub_eq c.two_ne_zero (c.hex _ (nd.mem 3 (by norm_num)).1)
    (nd.isCl 3 (by norm_num)) (hnorm 3 (by norm_num))

theorem routeD_typeA_five_final (hMFZ : FundNoncentral p) (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f)
    (hΩ : InClass p f Ω) (hex : ExactMembers Ω) (hK : K ∈ Ω)
    (hsingle : ∀ L ∈ Ω, ∃ g : G, L = conjSub g K) (hconn : DeltaConnected Ω)
    (hz : IsClassicalMember p f K z) (hshape : LocalShapeA p f 5 Ω z)
    (hP1 : LocalOddCentral Ω {z}) :
    (∃ D : LieSystemData p f G Ω, D.card = 1 ∧ ∃ i, D.tag i = .PSL ∧ D.rank i = 8) ∨
    (∃ D : LieSystemData p f G Ω, D.card = 1 ∧ ∃ i, D.tag i = .E6 ∧ D.rank i = 0) := by
  obtain ⟨d⟩ := LocalShapeA.nonempty_dict (by norm_num) hΩ hK hz hshape
  let c : ACtx p f 5 Ω K z :=
    { hm := by norm_num, hp2 := hp2, hq := hq, hΩ := hΩ, hex := hex, hK := hK, hz := hz,
      hP1 := hP1, d := d, hF := oddCoverSL3_of_five_le hq, hlift := Or.inl (by norm_num) }
  obtain ⟨nd⟩ := c.nonempty_nodes
  obtain ⟨β, hβ, hadp⟩ := ACtx.adapted_partner c hMFZ hshape hsingle nd
  obtain ⟨wβ, hwβ⟩ := hβ.cl
  rcases c.commutes_or_stdpair_end nd hsingle hβ hwβ (hadp wβ hwβ) with h3 | h3
  · left
    obtain ⟨U, hUΩ, hcomm, hpair⟩ := c.chain_A7 nd hβ h3
    exact routeD_typeA_of_chain hp2 hq (by norm_num) hΩ hK hsingle hconn hz hshape hP1 U hUΩ hcomm
      hpair
  · right
    obtain ⟨U, hUΩ, hcomm, hpair⟩ := c.chain_E6 nd hβ h3
    exact routeD_typeE6_of_chain hp2 hq hΩ hK hsingle hconn hz hshape.toT hP1 U hUΩ hcomm hpair

end Partner

end CFSG.ClassicalInvolution.RouteD.Gaps
