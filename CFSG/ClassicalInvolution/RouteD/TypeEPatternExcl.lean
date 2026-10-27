module

public import CFSG.ClassicalInvolution.RouteD.TypeEPatternExclTwin
public import CFSG.ClassicalInvolution.RouteD.TypeEPatternExclFrame
public import CFSG.ClassicalInvolution.RouteD.TypeEPatternRows
public import CFSG.ClassicalInvolution.RouteD.TypeEPatternExclChain

public section

namespace CFSG.ClassicalInvolution.RouteD

open CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.WeakCT CFSG.Assembly.LowTwoRank
  CFSG.LieType CFSG.LieType.RootSystem CFSG.LieType.Universal CFSG.LieType.Universal.Spin
  CFSG.LieType.CurtisTits CFSG.Timmesfeld

variable {p f : ℕ} [Fact p.Prime]

namespace TypeEPattern

theorem thetaD6_mem_roots : thetaD 6 ∈ (modelUniv .POmegaPlus 6 p f Fact.out).D.roots :=
  thetaD_mem_roots' (K := GaloisField p f) (by norm_num) (by norm_num)

theorem coeff_single_iff {r : ℕ} (a b : Fin r) :
    (((Pi.single a (1 : ℤ) : Fin r → ℤ) b : ℤ) : ZMod 2) = 0 ↔ a ≠ b := by
  by_cases h : a = b
  · subst h
    simp
  · simp [Ne.symm h, h]

theorem thetaD6_even {a : Fin 6} (h1 : 1 ≤ a.val) (h3 : a.val ≤ 3) :
    ((thetaD 6 a : ℤ) : ZMod 2) = 0 := by
  have : thetaD 6 a = 2 := by
    simp only [thetaD]
    split_ifs <;> first | rfl | omega
  rw [this]
  rfl

variable (p f) in
@[expose] noncomputable def rootθ6 : Subgroup (modelUniv .POmegaPlus 6 p f Fact.out).K :=
  rootθD 6 (GaloisField p f) (by norm_num)

theorem rootθ6_mem_fundamental :
    rootθ6 p f ∈ fundamentalSubgroups .POmegaPlus (modelUniv .POmegaPlus 6 p f Fact.out).D := by
  have hℓ := lenSq_roots_plusDatum (K := GaloisField p f) (by norm_num : 3 ≤ 6) ⟨0, by norm_num⟩
  exact fund_of_longest (t := .POmegaPlus) (plusDatum 6 (GaloisField p f) (by norm_num))
    (isLongestRoot_of_lenSq _ hℓ (thetaD_mem_roots' (K := GaloisField p f) (by norm_num)
      (by norm_num)))

theorem commutes_rootθ6_rankOne {a : Fin 6} (ha : a ≠ 1) :
    Commutes (rootθ6 p f) (rankOne (modelUniv .POmegaPlus 6 p f Fact.out).D.rootGroup a) :=
  commutes_rootθD_rankOne (K := GaloisField p f) (by norm_num) (by norm_num)
    (fun h => ha (Fin.ext h))

theorem stdPair_data {G : Type} [Group G] (h2 : (2 : GaloisField p f) ≠ 0) {U V : Subgroup G}
    {wU wV : G} (hU : IsClassicalMember p f U wU) (hV : IsClassicalMember p f V wV)
    (h : ∃ W, LinearBlockStandardPair (GaloisField p f) W U V) :
    U ≠ V ∧ ¬ Commutes U V ∧ Commute wU wV ∧ conjSub wV U = U := by
  obtain ⟨W, hW⟩ := h
  exact ⟨ne_of_linearBlockStandardPair hW, not_commutes_of_linearBlockStandardPair hW,
    Gaps.standardPair_involutions_commute h2 hW hU.mem hV.mem hU.orderOf_eq_two
      hV.orderOf_eq_two,
    Gaps.conjSub_eq_of_standardPair h2 hW hV.mem hV.orderOf_eq_two⟩

end TypeEPattern


namespace ETCtx

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {z : G} {K : Subgroup G}

theorem attached_zero_false (c : ETCtx p f .POmegaPlus 6 Ω K z)
    (hsingle : ∀ L ∈ Ω, ∃ g : G, L = conjSub g K) (hshape : LocalShapeT p f 1 .POmegaPlus 6 Ω z)
    {j : Fin 6 → Subgroup G} (hj : NodeSystem p f (edgeD 6) Ω K z j)
    {β : Subgroup G} (hβ : β ∈ Ω) {t : G} (htβ : IsClassicalMember p f β t)
    (hKβ : ∃ W, LinearBlockStandardPair (GaloisField p f) W K β)
    (hfix : ∀ a : Fin 6, a ≠ 0 → Commutes β (j a))
    (hstd : ∃ W, LinearBlockStandardPair (GaloisField p f) W β (j 0)) : False := by
  have h2 : (2 : GaloisField p f) ≠ 0 :=
    CFSG.ClassicalInvolution.ModelFacts.two_ne_zero_galoisField f c.hp2
  obtain ⟨x, hx⟩ := c.hΩ.classical (j 4) (hj.mem 4).1
  obtain ⟨cx⟩ := c.exists_ctx_member hsingle hshape (hj.mem 4).1 hx
  have hmem : ∀ {L : Subgroup G}, L ∈ Ω → Commutes L (j 4) → IsLayerMember cx L :=
    fun hL hc => IsLayerMember.of_commutes_self cx
      (mem_centralizingMembers_of_commutes hL hx.mem hc) hc
  obtain ⟨w₀, hw₀⟩ := c.hΩ.classical (j 0) (hj.mem 0).1
  obtain ⟨w₁, hw₁⟩ := c.hΩ.classical (j 1) (hj.mem 1).1
  obtain ⟨w₂, hw₂⟩ := c.hΩ.classical (j 2) (hj.mem 2).1
  exact cx.chain5_member_false (Gaps.chainBound1_plus (m := 6) c.hp2 (by norm_num) c.hq)
    (by norm_num) (hmem c.hK (hj.commK 4)) (hmem hβ (hfix 4 (by decide)))
    (hmem (hj.mem 0).1 (hj.comm 0 4 (by decide) (by decide) (by decide)))
    (hmem (hj.mem 1).1 (hj.comm 1 4 (by decide) (by decide) (by decide)))
    (hmem (hj.mem 2).1 (hj.comm 2 4 (by decide) (by decide) (by decide)))
    (hmem (hj.mem 5).1 (hj.comm 5 4 (by decide) (by decide) (by decide)))
    c.hz htβ hw₀ hw₁ hw₂ (TypeEPattern.stdPair_data h2 c.hz htβ hKβ)
    (TypeEPattern.stdPair_data h2 htβ hw₀ hstd)
    (TypeEPattern.stdPair_data h2 hw₀ hw₁ (hj.pair 0 1 (by decide)))
    (TypeEPattern.stdPair_data h2 hw₁ hw₂ (hj.pair 1 2 (by decide))) (hj.commK 0) (hj.commK 1)
    (hj.commK 2) (hfix 1 (by decide)) (hfix 2 (by decide))
    (hj.comm 0 2 (by decide) (by decide) (by decide))
    (Gaps.commutes_symm (hj.commK 5)) (Gaps.commutes_symm (hfix 5 (by decide)))
    (hj.comm 5 0 (by decide) (by decide) (by decide))
    (hj.comm 5 1 (by decide) (by decide) (by decide))
    (hj.comm 5 2 (by decide) (by decide) (by decide))

theorem attached_twin_false (c : ETCtx p f .POmegaPlus 6 Ω K z)
    (hsingle : ∀ L ∈ Ω, ∃ g : G, L = conjSub g K) (hshape : LocalShapeT p f 1 .POmegaPlus 6 Ω z)
    (hMFZ : Gaps.FundNoncentral p) (hS3 : Gaps.StandardPairAutAbelian (GaloisField p f))
    (hD4 : ∃ D : LieSystemData p f (locQuot Ω z) (locFamily Ω z), D.card ≤ 4)
    {j : Fin 6 → Subgroup G} (hj : NodeSystem p f (edgeD 6) Ω K z j)
    {β : Subgroup G} (hβ : β ∈ Ω) {t : G} (htβ : IsClassicalMember p f β t)
    (hKβ : ∃ W, LinearBlockStandardPair (GaloisField p f) W K β) (hβ0 : Commutes β (j 0))
    {N : Subgroup G} (hNz : N ∈ centralizingMembers Ω {z}) (hNK : N ≠ K)
    (hNnode : ∀ a : Fin 6, a ≠ 1 → Commutes N (j a))
    (hNt : N ≤ Subgroup.centralizer ({t} : Set G)) : False := by
  have h2 : (2 : GaloisField p f) ≠ 0 :=
    CFSG.ClassicalInvolution.ModelFacts.two_ne_zero_galoisField f c.hp2
  obtain ⟨W, hW⟩ := hKβ
  have hKN : Commutes K N := c.commutes_K_of_ne hNz hNK
  have hβN : Commutes β N :=
    c.commutes_partner_of_centralizes hsingle hMFZ hS3 hD4 hβ htβ ⟨W, hW⟩ hNz hNt hKN
  obtain ⟨x, hx⟩ := c.hΩ.classical (j 0) (hj.mem 0).1
  obtain ⟨cx⟩ := c.exists_ctx_member hsingle hshape (hj.mem 0).1 hx
  have hmem : ∀ {L : Subgroup G}, L ∈ Ω → Commutes L (j 0) → IsLayerMember cx L :=
    fun hL hc => IsLayerMember.of_commutes_self cx
      (mem_centralizingMembers_of_commutes hL hx.mem hc) hc
  obtain ⟨wN, hwN⟩ := c.hΩ.classical N hNz.1
  obtain ⟨w₂, hw₂⟩ := c.hΩ.classical (j 2) (hj.mem 2).1
  obtain ⟨w₃, hw₃⟩ := c.hΩ.classical (j 3) (hj.mem 3).1
  obtain ⟨w₄, hw₄⟩ := c.hΩ.classical (j 4) (hj.mem 4).1
  obtain ⟨w₅, hw₅⟩ := c.hΩ.classical (j 5) (hj.mem 5).1
  have hnodeC : ∀ a : Fin 6, a ≠ 0 → a ≠ 1 → ¬ edgeD 6 0 a → ¬ edgeD 6 a 0 →
      IsLayerMember cx (j a) := fun a _ _ h1 h2 =>
    hmem (hj.mem a).1 (hj.comm a 0 (by assumption) h2 h1)
  have hnc : ¬ Commutes K β := not_commutes_of_linearBlockStandardPair hW
  have key := cx.commutes_iff_of_d4 (Gaps.d4Centralizer_plus (m := 6) c.hp2 (by norm_num)
    (by norm_num) c.hq) (S := K) (S' := N) (J₂ := j 2) (J₃ := j 3) (J₄ := j 4) (J₅ := j 5)
    (B := β) (hmem c.hK (hj.commK 0)) (hmem hNz.1 (hNnode 0 (by decide)))
    (hnodeC 2 (by decide) (by decide) (by decide) (by decide))
    (hnodeC 3 (by decide) (by decide) (by decide) (by decide))
    (hnodeC 4 (by decide) (by decide) (by decide) (by decide))
    (hnodeC 5 (by decide) (by decide) (by decide) (by decide)) (hmem hβ hβ0) c.hz hwN hw₂ hw₃
    hw₄ hw₅ htβ (hj.pair 2 3 (by decide)) (hj.pair 3 4 (by decide)) (hj.pair 3 5 (by decide))
    (hj.comm 2 4 (by decide) (by decide) (by decide))
    (hj.comm 2 5 (by decide) (by decide) (by decide))
    (hj.comm 4 5 (by decide) (by decide) (by decide)) hNK.symm (hj.commK 2) (hj.commK 3)
    (hj.commK 4) (hj.commK 5) (hNnode 2 (by decide)) (hNnode 3 (by decide))
    (hNnode 4 (by decide)) (hNnode 5 (by decide))
    (ne_of_linearBlockStandardPair hW).symm (fun e => hnc (e ▸ hKN))
    (Gaps.standardPair_involutions_commute h2 hW c.hz.mem htβ.mem c.hz.orderOf_eq_two
      htβ.orderOf_eq_two).symm
    (Subgroup.mem_centralizer_singleton_iff.mp (hNt hwN.mem)).symm
  exact hnc (Gaps.commutes_symm (key.mpr hβN))

theorem exists_attached_D6 (c : ETCtx p f .POmegaPlus 6 Ω K z)
    (hsingle : ∀ L ∈ Ω, ∃ g : G, L = conjSub g K) (hshape : LocalShapeT p f 1 .POmegaPlus 6 Ω z)
    (hMFZ : Gaps.FundNoncentral p) (hS3 : Gaps.StandardPairAutAbelian (GaloisField p f))
    (hD4 : ∃ D : LieSystemData p f (locQuot Ω z) (locFamily Ω z), D.card ≤ 4)
    (hadm : StatedLieAdmissible .POmegaPlus 6 p f)
    (hLG : LayerGeom (fundamentalSubgroups .POmegaPlus (modelUniv .POmegaPlus 6 p f Fact.out).D)
      (GaloisField p f))
    {j : Fin 6 → Subgroup G} (hj : NodeSystem p f (edgeD 6) Ω K z j)
    (hjimg : ∀ a, locImg Ω z (j a) =
      (rankOne (modelUniv .POmegaPlus 6 p f Fact.out).D.rootGroup a).map c.d.ψ)
    {β : Subgroup G} (hβ : β ∈ Ω) {t : G} (htβ : IsClassicalMember p f β t)
    (hKβ : ∃ W : Subgroup G, LinearBlockStandardPair (GaloisField p f) W K β)
    {m₀ : Fin 6} (hβm₀ : Commutes β (j m₀)) (ht : t * z * t⁻¹ = z) (hT : ToralNormalE c ht) :
    ∃ j' : Fin 6 → Subgroup G, NodeSystem p f (edgeD 6) Ω K z j' ∧ ∃ p₀ : Fin 6,
      (p₀ = 4 ∨ p₀ = 5) ∧
        (∃ W : Subgroup G, LinearBlockStandardPair (GaloisField p f) W β (j' p₀)) ∧
        ∀ a, a ≠ p₀ → Commutes β (j' a) := by
  have hΩ := c.hΩ
  have h2 : (2 : GaloisField p f) ≠ 0 :=
    CFSG.ClassicalInvolution.ModelFacts.two_ne_zero_galoisField f c.hp2
  obtain ⟨W, hW⟩ := hKβ
  have hPat := TypeEPattern.patternLemma_plus (p := p) (f := f) (by norm_num : 4 ≤ 6)
  obtain ⟨n, H, hct, -⟩ := CFSG.ClassicalInvolution.ModelFacts.hasBruhatDatum .POmegaPlus 6 p f
    Fact.out trivial hadm
  obtain ⟨k₀, v, hTT⟩ := hT
  have hv : v ≠ 0 := by
    intro hv0
    obtain ⟨N, hNz, hNK, hKN, hβN⟩ := c.exists_moved_layer_member hLG hsingle hshape hβ htβ
      ⟨W, hW⟩ (hj.mem m₀).1 (hj.commK m₀) hβm₀
    obtain ⟨R, hR, hNR⟩ := c.exists_fund_of_ne hNz hNK
    have hgen := Balance.iSup_rankOneImage_eq_range .POmegaPlus 6 p f Fact.out trivial hadm
      c.d.ψ k₀
    have hfixrange : ∀ x ∈ c.d.ψ.range, Gaps.locAut hΩ.conjInvariant ht x = x := by
      intro x hx
      rw [← hgen] at hx
      let Fix : Subgroup (locQuot Ω z) :=
        MonoidHom.eqLocus (Gaps.locAut hΩ.conjInvariant ht).toMonoidHom (MonoidHom.id _)
      have hle : (⨆ γ ∈ (modelUniv .POmegaPlus 6 p f Fact.out).D.roots,
          Balance.rankOneImage (modelUniv .POmegaPlus 6 p f Fact.out).D c.d.ψ k₀ γ) ≤ Fix := by
        refine iSup₂_le fun γ hγ y hy => ?_
        exact ((hTT γ hγ).2).mpr (by simp [hv0, charOf]) y hy
      exact hle hx
    have hNt : N ≤ Subgroup.centralizer ({t} : Set G) :=
      (Gaps.locAut_fixed_iff hΩ c.hP1 ht hNz).mpr fun x hx => hfixrange x (by
        rw [hNR] at hx
        obtain ⟨r, -, rfl⟩ := hx
        exact ⟨r, rfl⟩)
    exact hβN (c.commutes_partner_of_centralizes hsingle hMFZ hS3 hD4 hβ htβ ⟨W, hW⟩ hNz hNt hKN)
  obtain ⟨y, hy, g, q, hjimg', hroot⟩ := Gaps.exists_adapted_frame_normal hΩ.conjInvariant
    c.d.ψ hct hPat ht v hv k₀ hTT hjimg
  obtain ⟨p₀, rfl⟩ : ∃ p₀ : Fin 6, p₀ = q := ⟨q, rfl⟩
  have hfixed : ∀ a : Fin 6, ((∀ x ∈ locImg Ω z (conjSub y (j a)),
      Gaps.locAut hΩ.conjInvariant ht x = x) ↔ a ≠ p₀) ∧
      (locImg Ω z (conjSub y (j a))).map (Gaps.locAut hΩ.conjInvariant ht).toMonoidHom =
        locImg Ω z (conjSub y (j a)) := by
    intro a
    obtain ⟨hn, hf⟩ := hroot (Pi.single a 1)
      (single_mem_roots (modelUniv .POmegaPlus 6 p f Fact.out).D a)
    rw [hjimg' a]
    refine ⟨?_, hn⟩
    show (∀ x ∈ (_ ⊔ _ : Subgroup _).map _, _) ↔ _
    rw [hf]
    exact TypeEPattern.coeff_single_iff a p₀
  have hyz : y * z * y⁻¹ = z := by
    have := Subgroup.mem_centralizer_singleton_iff.mp (centralizingLayer_le_centralizer Ω {z} hy)
    rw [mul_inv_eq_iff_eq_mul]
    exact this
  have hj' := hj.conjSub hΩ.conjInvariant hyz (c.locLayer_le_normalizer hy)
  have hmemy : ∀ a, conjSub y (j a) ∈ centralizingMembers Ω {z} := hj'.mem
  have hmemt : ∀ L ∈ centralizingMembers Ω {z}, conjSub t L ∈ centralizingMembers Ω {z} :=
    fun L hL => TypeEPattern.conjSub_mem_centralizingMembers hΩ.conjInvariant ht hL
  have hfix' : ∀ a, a ≠ p₀ → Commutes β (conjSub y (j a)) := fun a ha => by
    have h1 := (hfixed a).1.mpr ha
    have hNt := (Gaps.locAut_fixed_iff hΩ c.hP1 ht (hmemy a)).mpr h1
    exact c.commutes_partner_of_centralizes hsingle hMFZ hS3 hD4 hβ htβ ⟨W, hW⟩ (hmemy a) hNt
      (hj'.commK a)
  have hmov : ¬ Commutes β (conjSub y (j p₀)) := fun h => by
    have hNt : conjSub y (j p₀) ≤ Subgroup.centralizer ({t} : Set G) := fun n hn =>
      Subgroup.mem_centralizer_singleton_iff.mpr (h t htβ.mem n hn).symm
    have := (hfixed p₀).1.mp ((Gaps.locAut_fixed_iff hΩ c.hP1 ht (hmemy p₀)).mp hNt)
    exact this rfl
  have hnorm : conjSub t (conjSub y (j p₀)) = conjSub y (j p₀) := by
    have h1 := (hfixed p₀).2
    rw [Gaps.locAut_locImg hΩ.conjInvariant ht] at h1
    exact locImg_injOn hΩ c.hP1 (hmemt _ (hmemy p₀)) (hmemy p₀) h1
  have hstd : ∃ W : Subgroup G,
      LinearBlockStandardPair (GaloisField p f) W β (conjSub y (j p₀)) := by
    obtain ⟨b, hbp, hb1, hb2⟩ := TypeEPattern.edgeD6_far p₀
    obtain ⟨wJ, hwJ⟩ := hΩ.classical _ (hmemy p₀).1
    obtain ⟨xb, hxb⟩ := hΩ.classical _ (hmemy b).1
    exact c.scenarioC hLG hsingle hshape hβ htβ ⟨W, hW⟩ (hmemy p₀).1 (hmemy b).1 hwJ hxb
      (hj'.commK p₀) (hj'.commK b) (hfix' b hbp) (hj'.comm b p₀ hbp hb1 hb2).symm hmov hnorm
  have hp₀ : p₀ = 4 ∨ p₀ = 5 := by
    by_contra hnot
    by_cases h0 : p₀ = 0
    · subst h0
      exact c.attached_zero_false hsingle hshape hj' hβ htβ ⟨W, hW⟩ hfix' hstd
    · have h1 : 1 ≤ p₀.val := by
        rcases Nat.eq_zero_or_pos p₀.val with h | h
        · exact absurd (Fin.ext h) h0
        · exact h
      have h3 : p₀.val ≤ 3 := by
        have h6 := p₀.isLt
        by_contra h
        apply hnot
        have : p₀.val = 4 ∨ p₀.val = 5 := by omega
        rcases this with h' | h'
        · exact Or.inl (Fin.ext h')
        · exact Or.inr (Fin.ext h')
      obtain ⟨hθn, hθf⟩ := hroot (thetaD 6) TypeEPattern.thetaD6_mem_roots
      obtain ⟨N, hNz, hNK, hNeq⟩ := c.exists_member_of_fund
        (conjSub_mem_fundamentalSubgroups (TypeEPattern.rootθ6_mem_fundamental (p := p) (f := f))
          g)
      have hNeq' : locImg Ω z N = (TypeEPattern.rootθ6 p f).map
          (c.d.ψ.comp (MulAut.conj g).toMonoidHom) := by
        rw [hNeq]
        unfold conjSub
        rw [Subgroup.map_map]
      have hNnode : ∀ a : Fin 6, a ≠ 1 → Commutes N (conjSub y (j a)) := fun a ha =>
        commutes_of_commutes_locImg hΩ c.hP1 hNz (hmemy a) (by
          rw [hNeq', hjimg' a]
          exact commutes_map _ (TypeEPattern.commutes_rootθ6_rankOne ha))
      have hNt : N ≤ Subgroup.centralizer ({t} : Set G) :=
        (Gaps.locAut_fixed_iff hΩ c.hP1 ht hNz).mpr fun x hx =>
          (hθf.mpr (TypeEPattern.thetaD6_even h1 h3)) x (by rw [hNeq'] at hx; exact hx)
      exact c.attached_twin_false hsingle hshape hMFZ hS3 hD4 hj' hβ htβ ⟨W, hW⟩
        (hfix' 0 (fun h => h0 h.symm)) hNz hNK hNnode hNt
  exact ⟨fun a => conjSub y (j a), hj', p₀, hp₀, hstd, hfix'⟩

end ETCtx

section Rows

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {K : Subgroup G} {z : G}

theorem exists_partnerAt_E7_of_torus (hMFZ : Gaps.FundNoncentral p) (hp2 : p ≠ 2)
    (hq : 5 ≤ p ^ f) (hΩ : InClass p f Ω) (hex : ExactMembers Ω) (hK : K ∈ Ω)
    (hsingle : ∀ L ∈ Ω, ∃ g : G, L = conjSub g K) (hz : IsClassicalMember p f K z)
    (hshape : LocalShapeT p f 1 .POmegaPlus 6 Ω z) (hP1 : LocalOddCentral Ω {z})
    (hTor : ∀ c : ETCtx p f .POmegaPlus 6 Ω K z, ∀ j : Fin 6 → Subgroup G,
      NodeSystem p f (edgeD 6) Ω K z j →
      (∀ a, locImg Ω z (j a) =
        (rankOne (modelUniv .POmegaPlus 6 p f Fact.out).D.rootGroup a).map c.d.ψ) →
      ∀ β ∈ Ω, ∀ t : G, IsClassicalMember p f β t →
        (∃ W : Subgroup G, LinearBlockStandardPair (GaloisField p f) W K β) →
        Commutes β (j 0) → ∀ ht : t * z * t⁻¹ = z,
          TorusFixedP (by norm_num : 3 ≤ 6) c ((0 : Fin 6) : Fin (modelUniv .POmegaPlus 6 p f
            Fact.out).D.rank) ht) :
    ∃ j : Fin 6 → Subgroup G, NodeSystem p f (edgeD 6) Ω K z j ∧
      (PartnerAt p f Ω j 4 ∨ PartnerAt p f Ω j 5) := by
  have hp : p.Prime := Fact.out
  obtain ⟨hf, -⟩ := card_galoisField_of_four_le (p := p) (f := f) (by omega)
  have : NeZero f := ⟨hf⟩
  have hS3 : Gaps.StandardPairAutAbelian (GaloisField p f) :=
    Gaps.standardPairAutAbelian_galoisField hp2 hq
  have hadmY : StatedLieAdmissible .POmegaPlus 6 p f :=
    ⟨hp, Nat.one_le_iff_ne_zero.mpr hf, by norm_num⟩
  have hsc : FundamentalSingleClass .POmegaPlus (modelUniv .POmegaPlus 6 p f Fact.out).D :=
    ModelFacts.fundamentalSingleClass .POmegaPlus 6 p f hp trivial hadmY (by decide) (by decide)
  obtain ⟨d⟩ := LocalShapeT.nonempty_dictT (by decide) hsc hΩ hK hz hshape
  let c : ETCtx p f .POmegaPlus 6 Ω K z :=
    { hp2 := hp2, hq := hq, hΩ := hΩ, hex := hex, hK := hK, hz := hz, hP1 := hP1, d := d,
      hF := oddCoverSL3_of_five_le hq, hY := yData_D6 hadmY (by omega) }
  obtain ⟨j, hj, hjimg⟩ := c.exists_nodeSystem_D6' hadmY
  obtain ⟨β, hβΩ, hKβ, hβ0⟩ :=
    c.exists_partner_transport hsingle (hj.mem 0).1 (hj.ne_K 0) (hj.commK 0)
  obtain ⟨t, htβ⟩ := hΩ.classical β hβΩ
  have ht : t * z * t⁻¹ = z := partner_involution_commutes hp2 hz htβ hKβ
  have h2t : t * t = 1 := by
    have := pow_orderOf_eq_one t
    rwa [htβ.orderOf_eq_two, pow_two] at this
  have hKt : conjSub t K = K := by
    obtain ⟨W, hW⟩ := hKβ
    exact Gaps.conjSub_eq_of_standardPair
      (CFSG.ClassicalInvolution.ModelFacts.two_ne_zero_galoisField f hp2) hW htβ.mem
      htβ.orderOf_eq_two
  have hD4 : ∃ D : LieSystemData p f (locQuot Ω z) (locFamily Ω z), D.card ≤ 4 := by
    obtain ⟨D, hcard, -⟩ := hshape
    exact ⟨D, by omega⟩
  have hLG := (Gaps.orthFacts_plus (p := p) (f := f) (m := 6) hp2 (by norm_num) hq).toLayerGeom
  have hfix0 : ∀ x ∈ (rankOne (modelUniv .POmegaPlus 6 p f Fact.out).D.rootGroup
      ((0 : Fin 6) : Fin (modelUniv .POmegaPlus 6 p f Fact.out).D.rank)).map c.d.ψ,
      Gaps.locAut c.hΩ.conjInvariant ht x = x := by
    rw [← hjimg 0]
    exact c.fixed_of_commutes ht htβ (hj.mem 0) hβ0
  have hTN := c.toralNormal_plus (m := 6) (by norm_num) (by norm_num) ht h2t hKt
    ((0 : Fin 6) : Fin (modelUniv .POmegaPlus 6 p f Fact.out).D.rank) hfix0
    (hTor c j hj hjimg β hβΩ t htβ hKβ hβ0 ht)
  obtain ⟨j', hj', p₀, hp₀, ⟨W, hW⟩, hc⟩ := c.exists_attached_D6 hsingle hshape hMFZ hS3 hD4
    hadmY hLG hj hjimg hβΩ htβ hKβ hβ0 ht hTN
  refine ⟨j', hj', ?_⟩
  rcases hp₀ with rfl | rfl
  · exact Or.inl ⟨β, hβΩ, ⟨W, hW⟩, hc⟩
  · exact Or.inr ⟨β, hβΩ, ⟨W, hW⟩, hc⟩

end Rows

end CFSG.ClassicalInvolution.RouteD
