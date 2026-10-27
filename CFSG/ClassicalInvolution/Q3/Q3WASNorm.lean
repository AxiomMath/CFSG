module

public import CFSG.ClassicalInvolution.Q3.Q3WASPat
public import CFSG.ClassicalInvolution.Q3.Q3WAFive
public import CFSG.ClassicalInvolution.Q3.Q3WAComp
public import CFSG.ClassicalInvolution.Q3.Generation

public section

namespace CFSG.ClassicalInvolution.Q3.Q3W

open CFSG.Open hiding StatedLieTag StatedLieAdmissible
open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Models
  CFSG.ClassicalInvolution.RouteD CFSG.ClassicalInvolution.RouteD.Gaps CFSG.Assembly.LowTwoRank
  CFSG.LieType.Universal CFSG.ComponentClassification.CatalogueBHigherLinearAction
open CFSG.ClassicalInvolution.WeakCT (LinearBlockStandardPair blockSL2)
open scoped MatrixGroups commutatorElement

section Aut

theorem fixed_of_pow3_of_central {Y : Type*} [Group Y] (σ : Y →* Y) {N : Subgroup Y}
    (hN : Pow3 N) {Z : Subgroup Y} (hZ : Z ≤ Subgroup.center Y)
    (hcop : ∀ x ∈ Z, ¬ 3 ∣ orderOf x) (h : ∀ n ∈ N, n⁻¹ * σ n ∈ Z) : ∀ n ∈ N, σ n = n := by
  let φ : N →* Subgroup.center Y :=
    { toFun := fun n => ⟨(n : Y)⁻¹ * σ n, hZ (h n n.2)⟩
      map_one' := by apply Subtype.ext; simp
      map_mul' := fun a b => by
        apply Subtype.ext
        have ha := Subgroup.mem_center_iff.mp (hZ (h a a.2))
        simp only [Subgroup.coe_mul, mul_inv_rev, map_mul, Subgroup.coe_mul]
        calc (b : Y)⁻¹ * (a : Y)⁻¹ * (σ a * σ b)
            = (b : Y)⁻¹ * ((a : Y)⁻¹ * σ a) * σ b := by group
          _ = ((a : Y)⁻¹ * σ a) * (b : Y)⁻¹ * σ b := by rw [ha ((b : Y)⁻¹)]
          _ = ((a : Y)⁻¹ * σ a) * ((b : Y)⁻¹ * σ b) := by group }
  let K : Subgroup Y := Subgroup.map N.subtype φ.ker
  have hK : ⁅N, N⁆ ≤ K := by
    rw [Subgroup.commutator_le]
    intro a ha b hb
    refine ⟨⁅(⟨a, ha⟩ : N), ⟨b, hb⟩⁆, ?_, rfl⟩
    show φ ⁅(⟨a, ha⟩ : N), ⟨b, hb⟩⁆ = 1
    rw [map_commutatorElement]
    exact commutatorElement_eq_one_iff_mul_comm.mpr (Subtype.ext
      (Subgroup.mem_center_iff.mp (φ ⟨b, hb⟩).2 (φ ⟨a, ha⟩ : Y)))
  intro n hn
  obtain ⟨x, hx, hxn⟩ := hK (hN n hn)
  have hxe : x = (⟨n, hn⟩ : N) ^ 3 := Subtype.ext (by simpa using hxn)
  have h3 : φ ((⟨n, hn⟩ : N)) ^ 3 = 1 := by
    rw [← map_pow, ← hxe]
    exact hx
  have h3' : ((n : Y)⁻¹ * σ n) ^ 3 = 1 := by
    have := congrArg (fun w : Subgroup.center Y => (w : Y)) h3
    simpa [φ] using this
  have hord : orderOf ((n : Y)⁻¹ * σ n) ∣ 3 := orderOf_dvd_of_pow_eq_one h3'
  have h1 : orderOf ((n : Y)⁻¹ * σ n) = 1 := by
    rcases (Nat.dvd_prime Nat.prime_three).mp hord with h1 | h1
    · exact h1
    · exact (hcop _ (h n hn) (by rw [h1])).elim
  have h4 : (n : Y)⁻¹ * σ n = 1 := orderOf_eq_one_iff.mp h1
  rw [inv_mul_eq_one] at h4
  exact h4.symm

variable {G : Type} [Group G]

theorem locAut_fixed_iff3 {Ω : Set (Subgroup G)} (hΩ : InClass3 Ω) (hex : ExactMembers3 Ω)
    {t z : G} (hP1 : LocalOddCentral Ω {z}) (hO3 : LocalOddThreeFree3 Ω z)
    (ht : t * z * t⁻¹ = z) {N : Subgroup G} (hN : N ∈ centralizingMembers Ω {z}) :
    N ≤ Subgroup.centralizer ({t} : Set G) ↔
      ∀ a ∈ locImg Ω z N, locAut hΩ.conjInvariant ht a = a := by
  constructor
  · rintro h _ ⟨b, hb, rfl⟩
    show locMk Ω z (layerAut hΩ.conjInvariant ht b) = locMk Ω z b
    congr 1
    apply Subtype.ext
    show t * (b : G) * t⁻¹ = b
    have := Subgroup.mem_centralizer_singleton_iff.mp (h (Subgroup.mem_subgroupOf.mp hb))
    rw [mul_inv_eq_iff_eq_mul]
    exact this.symm
  · intro h n hn
    obtain ⟨z₀, hz₀⟩ := hΩ.classical N hN.1
    obtain ⟨eN⟩ := hz₀.nonempty_equiv_sl2 (hex N hN.1)
    set Y := locLayer Ω z
    set O := classicalInvolutionOddCore ↥Y
    have hle : N ≤ Y := le_centralizingLayer hN
    have hpow : Pow3 (N.subgroupOf Y) := by
      intro l hl
      exact pow_three_mem_commutator_of_equiv (K := ZMod 3) (by simp)
        ((Subgroup.subgroupOfEquivOfLe hle).trans eN) l hl
    have hOc : ∀ b ∈ N.subgroupOf Y, b⁻¹ * layerAut hΩ.conjInvariant ht b ∈ O := by
      intro b hb
      have := h _ ⟨b, hb, rfl⟩
      have h2 : locMk Ω z (layerAut hΩ.conjInvariant ht b) = locMk Ω z b := this
      exact QuotientGroup.eq.mp h2.symm
    have hcop : ∀ x ∈ O, ¬ 3 ∣ orderOf x := by
      intro x hx h3
      have h1 : orderOf (⟨x, hx⟩ : O) ∣ Nat.card O := orderOf_dvd_natCard _
      rw [Subgroup.orderOf_mk] at h1
      exact hO3 (h3.trans h1)
    have key := fixed_of_pow3_of_central (layerAut hΩ.conjInvariant ht).toMonoidHom
      (N := N.subgroupOf Y) hpow hP1 hcop hOc
    have := key ⟨n, le_centralizingLayer hN hn⟩ (Subgroup.mem_subgroupOf.mpr hn)
    rw [Subgroup.mem_centralizer_singleton_iff]
    have h4 := congrArg Subtype.val this
    have h5 : t * n * t⁻¹ = n := h4
    rw [mul_inv_eq_iff_eq_mul] at h5
    exact h5.symm

end Aut

section Conj

variable {G : Type} [Group G] {Ω : Set (Subgroup G)}

theorem fix_of_stdpair3 {K β : Subgroup G} {z t : G} (hz : IsClassicalMember3 K z)
    (hwβ : IsClassicalMember3 β t)
    (hW : ∃ W : Subgroup G, LinearBlockStandardPair (GaloisField 3 1) W K β) :
    t * z * t⁻¹ = z := by
  obtain ⟨W, hW⟩ := hW
  have hzt : z * t = t * z :=
    standardPair_involutions_commute two_ne_zero_gf3 hW hz.mem hwβ.mem hz.orderOf_eq_two
      hwβ.orderOf_eq_two
  rw [mul_inv_eq_iff_eq_mul]
  exact hzt.symm

theorem conjSub_mem_centralizingMembers3 (hΩ : ConjInvariant Ω) {t z : G}
    (htz : t * z * t⁻¹ = z) {L : Subgroup G} (hL : L ∈ centralizingMembers Ω {z}) :
    conjSub t L ∈ centralizingMembers Ω {z} := by
  have hconj_t : centralizingMembers Ω {z} = conjSub t '' centralizingMembers Ω {z} := by
    have := centralizingMembers_conj hΩ t z
    rwa [htz] at this
  have : conjSub t L ∈ conjSub t '' centralizingMembers Ω {z} := ⟨L, hL, rfl⟩
  rwa [← hconj_t] at this

variable [Finite G]

theorem commute_of_conjSub_eq3 {L : Subgroup G} {w t : G} (hL : IsClassicalMember3 L w)
    (ht : conjSub t L = L) : Commute t w := by
  have hcl : IsClassicalMember3 (conjSub t L) (t * w * t⁻¹) := hL.conj t
  rw [ht] at hcl
  have := involution_unique3 hL hcl
  exact (mul_inv_eq_iff_eq_mul.mp this.symm : t * w = w * t)

theorem Nodes3.locImg_eq {m : ℕ} {K : Subgroup G} {z : G} {c : ACtx3 m Ω K z} (nd : Nodes3 c)
    {a : ℕ} (ha : a < m) :
    locImg Ω z (nd.j a) = (blockSL2 (GaloisField 3 1) m ⟨a, ha⟩).range.map c.d.ψ := by
  rw [nd.img a ha, blockSL2_range_eq_Lc two_ne_zero_gf3 ha]

end Conj

section Partner


variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {K : Subgroup G} {z : G}

omit [Finite G] in
theorem exists_lieSystemData_conj3 {ι : Type} (hΩ : ConjInvariant Ω) (g x : G)
    (D : LieSystemData3 ι (locQuot Ω x) (locFamily Ω x)) :
    Nonempty (LieSystemData3 ι (locQuot Ω (g * x * g⁻¹)) (locFamily Ω (g * x * g⁻¹))) := by
  have h := LieSystemData3.congr (locQuotConj hΩ g x) D
  rw [Gaps.locFamily_conj hΩ g x] at h
  exact ⟨h⟩

theorem commutes_iff_le_centralizer3 (hMFZ : RouteD.Gaps.FundNoncentral 3) {ι : Type}
    (hΩ : InClass3 Ω) (hex : ExactMembers3 Ω) {t : G} (hP1 : LocalOddCentral Ω {t})
    (hO3 : LocalOddThreeFree3 Ω t) (Dt : LieSystemData3 ι (locQuot Ω t) (locFamily Ω t))
    {β N : Subgroup G} (hβ : β ∈ Ω) (hwβ : IsClassicalMember3 β t) (hN : N ∈ Ω)
    (hNK : Commutes N K) (hnK : ¬ Commutes K β) :
    Commutes N β ↔ N ≤ Subgroup.centralizer ({t} : Set G) := by
  constructor
  · intro h x hx
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact h x hx t hwβ.mem
  · intro h
    have hβt : β ∈ centralizingMembers Ω {t} := ⟨hβ, isSubnormal_le hwβ.subnormal⟩
    have hNt : N ∈ centralizingMembers Ω {t} := ⟨hN, h⟩
    rcases commutes_or_eq_of_involution3 hMFZ hΩ hex hP1 hO3 Dt hβt hNt hwβ with hc | he
    · exact hc.symm
    · exfalso
      apply hnK
      rw [← he]
      exact hNK.symm

theorem ACtx3.commutes_partner_iff {m : ℕ} (c : ACtx3 m Ω K z)
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

theorem ACtx3.partner_pattern {m : ℕ} (c : ACtx3 m Ω K z) (hm : 4 ≤ m) (nd : Nodes3 c)
    (hMFZ : RouteD.Gaps.FundNoncentral 3)
    (hcl : LinearAutClassification (GaloisField 3 1) (m + 1)) {ι : Type}
    (D : LieSystemData3 ι (locQuot Ω z) (locFamily Ω z))
    (hsingle : ∀ L ∈ Ω, ∃ g : G, L = conjSub g K)
    {β : Subgroup G} (hβ : β ∈ Ω) {t : G} (hwβ : IsClassicalMember3 β t)
    (hnK : ¬ Commutes K β) (htz : t * z * t⁻¹ = z)
    (hfixed : ∀ (a : ℕ) (ha : a < m), partnerFixed m ⟨a, ha⟩ → Commutes β (nd.j a))
    (hfirst : ¬ Commutes β (nd.j 0)) :
    ∃ μ : (GaloisField 3 1)ˣ, (μ = 1 ∨ μ = -1) ∧
      (∀ x, locAut c.hΩ.conjInvariant htz (c.d.ψ x) =
        c.d.ψ (slConjugation (m + 1) (GaloisField 3 1) (partnerDiag m μ) x)) ∧
      (μ = 1 ↔ ∀ A : SL(2, GaloisField 3 1),
        locAut c.hΩ.conjInvariant htz
            (c.d.ψ (blockSL2 (GaloisField 3 1) m ⟨m - 2, by omega⟩ A)) =
          c.d.ψ (blockSL2 (GaloisField 3 1) m ⟨m - 2, by omega⟩ A)) := by
  classical
  have h2 := two_ne_zero_gf3
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
    eq_of_locImg_le_Q₀3 c.hm hΩ hex c.hK c.hz c.hP1 c.hO3 c.d hmem
      (locImg_self_le_Q₀3 c.hm (hconj t K c.hK) hcK c.d)
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
    have hS : (⨆ R ∈ longRootSet (K := GaloisField 3 1) c.hn, R) ≤
        (ψ.range).comap (σ.toMonoidHom.comp ψ) := by
      refine iSup₂_le fun R hR y hy => ?_
      obtain ⟨L, hL, hLK, hLR⟩ := exists_member_of_root3 c.hm hΩ hex c.hK c.hz c.hP1 c.hO3 c.d hR
      have hyL : ψ y ∈ locImg Ω z L := by rw [hLR]; exact ⟨y, hy, rfl⟩
      have h1 : σ (ψ y) ∈ locImg Ω z (conjSub t L) := by
        rw [← locAut_locImg hconj htz L]; exact ⟨_, hyL, rfl⟩
      obtain ⟨R', -, hR'⟩ := exists_root_of_ne3 c.hm hΩ hex c.hK c.hz c.hP1 c.hO3 c.d
        (hmemΩz L hL) ((hconjne L).mpr hLK)
      rw [hR'] at h1
      obtain ⟨y', -, hy'⟩ := h1
      exact ⟨y', hy'⟩
    intro x
    have hx : x ∈ ⨆ R ∈ longRootSet (K := GaloisField 3 1) c.hn, R := by
      rw [iSup_longRootSet_eq_top h2 c.hn]; exact Subgroup.mem_top x
    exact hS hx
  have hfixedσ : ∀ a (ha : a < m), Commutes β (nd.j a) → ∀ A : SL(2, GaloisField 3 1),
      σ (ψ (blockSL2 (GaloisField 3 1) m ⟨a, ha⟩ A)) =
        ψ (blockSL2 (GaloisField 3 1) m ⟨a, ha⟩ A) := by
    intro a ha hcomm A
    have hle : nd.j a ≤ Subgroup.centralizer ({t} : Set G) := fun n hn => by
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact (hcomm t hwβ.mem n hn).symm
    exact (locAut_fixed_iff3 hΩ hex c.hP1 c.hO3 htz (nd.mem a ha)).mp hle _
      (by rw [nd.locImg_eq ha]; exact ⟨_, ⟨A, rfl⟩, rfl⟩)
  have hfix : ∀ a : Fin m, partnerFixed m a → ∀ A : SL(2, GaloisField 3 1),
      σ (ψ (blockSL2 (GaloisField 3 1) m a A)) = ψ (blockSL2 (GaloisField 3 1) m a A) :=
    fun a ha A => hfixedσ a.val a.isLt (hfixed a.val a.isLt ha) A
  have hmove : ∃ A : SL(2, GaloisField 3 1),
      σ (ψ (blockSL2 (GaloisField 3 1) m ⟨0, by omega⟩ A)) ≠
        ψ (blockSL2 (GaloisField 3 1) m ⟨0, by omega⟩ A) := by
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
  exact partner_pattern_amb3 card_gf3 hm hcl ψ c.d.ker_le σ hσ2 hstab hfix hmove

theorem ACtx3.partner_normalizes_nodes {m : ℕ} (c : ACtx3 m Ω K z) (hm : 4 ≤ m) (nd : Nodes3 c)
    (hMFZ : RouteD.Gaps.FundNoncentral 3)
    (hcl : LinearAutClassification (GaloisField 3 1) (m + 1)) {ι : Type}
    (D : LieSystemData3 ι (locQuot Ω z) (locFamily Ω z))
    (hsingle : ∀ L ∈ Ω, ∃ g : G, L = conjSub g K)
    {β : Subgroup G} (hβ : β ∈ Ω) {t : G} (hwβ : IsClassicalMember3 β t)
    (hnK : ¬ Commutes K β)
    (hpair : ∃ W : Subgroup G, LinearBlockStandardPair (GaloisField 3 1) W K β)
    (hfixed : ∀ (a : ℕ) (ha : a < m), partnerFixed m ⟨a, ha⟩ → Commutes β (nd.j a))
    (hfirst : ¬ Commutes β (nd.j 0)) :
    ∃ μ : (GaloisField 3 1)ˣ, (μ = 1 ∨ μ = -1) ∧ ∀ a : ℕ, a < m → conjSub t (nd.j a) = nd.j a := by
  classical
  have hΩ := c.hΩ
  have hex := c.hex
  have hconj := hΩ.conjInvariant
  have htz : t * z * t⁻¹ = z := fix_of_stdpair3 c.hz hwβ hpair
  have htt : t * t = 1 := mul_self_of_isClassicalMember3 hwβ
  obtain ⟨μ, hμ, hpat, -⟩ := c.partner_pattern hm nd hMFZ hcl D hsingle hβ hwβ hnK htz hfixed
    hfirst
  refine ⟨μ, hμ, fun a ha => ?_⟩
  set σ := locAut hconj htz with hσdef
  have hσ2 : ∀ y, σ (σ y) = y := locAut_locAut hconj htz htt
  have hsub : ∀ y ∈ locImg Ω z (nd.j a), σ y ∈ locImg Ω z (nd.j a) := by
    intro y hy
    rw [nd.locImg_eq ha] at hy ⊢
    obtain ⟨_, ⟨A, rfl⟩, rfl⟩ := hy
    rw [hpat]
    obtain ⟨A', hA'⟩ : ∃ A' : SL(2, GaloisField 3 1),
        slConjugation (m + 1) (GaloisField 3 1) (partnerDiag m μ)
          (blockSL2 (GaloisField 3 1) m ⟨a, ha⟩ A) =
        blockSL2 (GaloisField 3 1) m ⟨a, ha⟩ A' :=
      ⟨_, slConjugation_diagGL_blockSL2_eq (partnerEnt m μ) ⟨a, ha⟩ A⟩
    exact ⟨blockSL2 (GaloisField 3 1) m ⟨a, ha⟩ A', ⟨A', rfl⟩, by rw [hA']⟩
  have hmapeq : (locImg Ω z (nd.j a)).map σ.toMonoidHom = locImg Ω z (nd.j a) :=
    map_eq_of_involutive σ hσ2 _ hsub
  have h1 := locAut_locImg hconj htz (nd.j a)
  rw [hmapeq] at h1
  exact locImg_injOn3 hΩ hex c.hP1 c.hO3 (conjSub_mem_centralizingMembers3 hconj htz (nd.mem a ha))
    (nd.mem a ha) h1.symm

end Partner

section Adapted



variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {K : Subgroup G} {z : G}

theorem ACtx3.adapted_partner (c : ACtx3 5 Ω K z) (hMFZ : RouteD.Gaps.FundNoncentral 3) {ι : Type}
    (D : LieSystemData3 ι (locQuot Ω z) (locFamily Ω z))
    (hsingle : ∀ L ∈ Ω, ∃ g : G, L = conjSub g K) (nd : Nodes3 c) :
    ∃ β, IsPartnerE3 c nd β ∧ ∀ wβ : G, IsClassicalMember3 β wβ → Commute wβ (nd.w 3) := by
  obtain ⟨β, hβ⟩ := c.exists_partnerE nd hsingle
  refine ⟨β, hβ, fun wβ hwβ => ?_⟩
  have hcl : LinearAutClassification (GaloisField 3 1) (5 + 1) :=
    linearAutClassification3 (by norm_num)
  have hfixed : ∀ (a : ℕ) (ha : a < 5), partnerFixed 5 ⟨a, ha⟩ → Commutes β (nd.j a) := by
    intro a ha hfx
    rcases hfx with hfx | ⟨h1, h2⟩
    · have : a = 4 := by simp only at hfx; omega
      subst this
      exact hβ.last
    · exact hβ.mid a (by simpa using h1) (by simp only at h2; omega)
  obtain ⟨μ, -, hnorm⟩ := c.partner_normalizes_nodes (by norm_num) nd hMFZ hcl D hsingle hβ.mem
    hwβ hβ.nK hβ.pK hfixed hβ.n0
  exact commute_of_conjSub_eq3 (nd.isCl 3 (by norm_num)) (hnorm 3 (by norm_num))

end Adapted

end CFSG.ClassicalInvolution.Q3.Q3W
