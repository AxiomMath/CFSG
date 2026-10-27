module

public import CFSG.ClassicalInvolution.Q3.Q3EPExclModel
public import CFSG.ClassicalInvolution.Q3.Q3EPFixed

public section

namespace CFSG.ClassicalInvolution.Q3.Q3W

open CFSG.Open hiding StatedLieTag StatedLieAdmissible
open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.RouteD
  CFSG.ClassicalInvolution.RouteD.Gaps CFSG.Assembly.LowTwoRank CFSG.LieType.Universal
  CFSG.LieType CFSG.LieType.RootSystem CFSG.LieType.CurtisTits CFSG.Timmesfeld
open CFSG.ClassicalInvolution.WeakCT (LinearBlockStandardPair)
open scoped MatrixGroups commutatorElement

set_option linter.unusedSectionVars false


section Config

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {K : Subgroup G} {z : G}

theorem ETCtx3.attached_zero_false (c : ETCtx3 .POmegaPlus 6 Ω K z)
    (hsingle : ∀ L ∈ Ω, ∃ g : G, L = conjSub g K)
    {j : Fin 6 → Subgroup G} (hj : NodeSystem 3 1 (edgeD 6) Ω K z j)
    {β : Subgroup G} (hβ : β ∈ Ω) {t : G} (htβ : IsClassicalMember3 β t)
    (hKβ : ∃ W, LinearBlockStandardPair (GaloisField 3 1) W K β)
    (hfix : ∀ a : Fin 6, a ≠ 0 → Commutes β (j a))
    (hstd : ∃ W, LinearBlockStandardPair (GaloisField 3 1) W β (j 0)) : False := by
  obtain ⟨x, hx⟩ := c.hΩ.classical (j 4) (hj.mem 4).1
  obtain ⟨cx⟩ := c.exists_ctx_member hsingle (hj.mem 4).1 hx
  have hmem : ∀ {L : Subgroup G}, L ∈ Ω → Commutes L (j 4) → cx.IsLayerMember L :=
    fun hL hc => ETCtx3.IsLayerMember.of_commutes_self cx
      (mem_centralizingMembers_of_commutes hL hx.mem hc) hc
  obtain ⟨w₀, hw₀⟩ := c.hΩ.classical (j 0) (hj.mem 0).1
  obtain ⟨w₁, hw₁⟩ := c.hΩ.classical (j 1) (hj.mem 1).1
  obtain ⟨w₂, hw₂⟩ := c.hΩ.classical (j 2) (hj.mem 2).1
  exact cx.chain5_member_false chainBound1_3_plus6 (by norm_num)
    (hmem c.hK (hj.commK 4)) (hmem hβ (hfix 4 (by decide)))
    (hmem (hj.mem 0).1 (hj.comm 0 4 (by decide) (by decide) (by decide)))
    (hmem (hj.mem 1).1 (hj.comm 1 4 (by decide) (by decide) (by decide)))
    (hmem (hj.mem 2).1 (hj.comm 2 4 (by decide) (by decide) (by decide)))
    (hmem (hj.mem 5).1 (hj.comm 5 4 (by decide) (by decide) (by decide)))
    c.hz htβ hw₀ hw₁ hw₂ (stdPair_data3 c.hz htβ hKβ) (stdPair_data3 htβ hw₀ hstd)
    (stdPair_data3 hw₀ hw₁ (hj.pair 0 1 (by decide)))
    (stdPair_data3 hw₁ hw₂ (hj.pair 1 2 (by decide))) (hj.commK 0) (hj.commK 1)
    (hj.commK 2) (hfix 1 (by decide)) (hfix 2 (by decide))
    (hj.comm 0 2 (by decide) (by decide) (by decide))
    (commutes_symm (hj.commK 5)) (commutes_symm (hfix 5 (by decide)))
    (hj.comm 5 0 (by decide) (by decide) (by decide))
    (hj.comm 5 1 (by decide) (by decide) (by decide))
    (hj.comm 5 2 (by decide) (by decide) (by decide))

theorem ETCtx3.attached_twin_false (c : ETCtx3 .POmegaPlus 6 Ω K z)
    (hsingle : ∀ L ∈ Ω, ∃ g : G, L = conjSub g K) (hMFZ : Gaps.FundNoncentral 3) {ι : Type}
    (D : LieSystemData3 ι (locQuot Ω z) (locFamily Ω z))
    {j : Fin 6 → Subgroup G} (hj : NodeSystem 3 1 (edgeD 6) Ω K z j)
    {β : Subgroup G} (hβ : β ∈ Ω) {t : G} (htβ : IsClassicalMember3 β t)
    (hKβ : ∃ W, LinearBlockStandardPair (GaloisField 3 1) W K β) (hβ0 : Commutes β (j 0))
    {N : Subgroup G} (hNz : N ∈ centralizingMembers Ω {z}) (hNK : N ≠ K)
    (hNnode : ∀ a : Fin 6, a ≠ 1 → Commutes N (j a))
    (hNt : N ≤ Subgroup.centralizer ({t} : Set G)) : False := by
  obtain ⟨W, hW⟩ := hKβ
  have hKN : Commutes K N := c.commutes_K_of_ne hNz hNK
  have hβN : Commutes β N :=
    c.commutes_partner_of_centralizes hMFZ hsingle D hβ htβ ⟨W, hW⟩ hNz hNt hKN
  obtain ⟨x, hx⟩ := c.hΩ.classical (j 0) (hj.mem 0).1
  obtain ⟨cx⟩ := c.exists_ctx_member hsingle (hj.mem 0).1 hx
  have hmem : ∀ {L : Subgroup G}, L ∈ Ω → Commutes L (j 0) → cx.IsLayerMember L :=
    fun hL hc => ETCtx3.IsLayerMember.of_commutes_self cx
      (mem_centralizingMembers_of_commutes hL hx.mem hc) hc
  obtain ⟨wN, hwN⟩ := c.hΩ.classical N hNz.1
  obtain ⟨w₂, hw₂⟩ := c.hΩ.classical (j 2) (hj.mem 2).1
  obtain ⟨w₃, hw₃⟩ := c.hΩ.classical (j 3) (hj.mem 3).1
  obtain ⟨w₄, hw₄⟩ := c.hΩ.classical (j 4) (hj.mem 4).1
  obtain ⟨w₅, hw₅⟩ := c.hΩ.classical (j 5) (hj.mem 5).1
  have hnodeC : ∀ a : Fin 6, a ≠ 0 → a ≠ 1 → ¬ edgeD 6 0 a → ¬ edgeD 6 a 0 →
      cx.IsLayerMember (j a) := fun a _ _ h1 h2 =>
    hmem (hj.mem a).1 (hj.comm a 0 (by assumption) h2 h1)
  have hnc : ¬ Commutes K β := not_commutes_of_linearBlockStandardPair hW
  have key := cx.commutes_iff_of_d4 (S := K) (S' := N) (J₂ := j 2) (J₃ := j 3) (J₄ := j 4)
    (J₅ := j 5) (B := β) (hmem c.hK (hj.commK 0)) (hmem hNz.1 (hNnode 0 (by decide)))
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
    (Gaps.standardPair_involutions_commute two_ne_zero_gf3 hW c.hz.mem htβ.mem
      c.hz.orderOf_eq_two htβ.orderOf_eq_two).symm
    (Subgroup.mem_centralizer_singleton_iff.mp (hNt hwN.mem)).symm
  exact hnc (commutes_symm (key.mpr hβN))

end Config

section Attached

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {K : Subgroup G} {z : G}

theorem ETCtx3.exists_attached_D6 (c : ETCtx3 .POmegaPlus 6 Ω K z)
    (hsingle : ∀ L ∈ Ω, ∃ g : G, L = conjSub g K) (hMFZ : Gaps.FundNoncentral 3) {ι : Type}
    (D : LieSystemData3 ι (locQuot Ω z) (locFamily Ω z))
    {j : Fin 6 → Subgroup G} (hj : NodeSystem 3 1 (edgeD 6) Ω K z j)
    (hjimg : ∀ a, locImg Ω z (j a) =
      (rankOne (modelUniv .POmegaPlus 6 3 1 Nat.prime_three).D.rootGroup a).map c.d.ψ)
    {β : Subgroup G} (hβ : β ∈ Ω) {t : G} (htβ : IsClassicalMember3 β t)
    (hKβ : ∃ W : Subgroup G, LinearBlockStandardPair (GaloisField 3 1) W K β)
    {m₀ : Fin 6} (hβm₀ : Commutes β (j m₀)) (ht : t * z * t⁻¹ = z) (hT : ToralNormalE3 c ht) :
    ∃ j' : Fin 6 → Subgroup G, NodeSystem 3 1 (edgeD 6) Ω K z j' ∧ ∃ p₀ : Fin 6,
      (p₀ = 4 ∨ p₀ = 5) ∧
        (∃ W : Subgroup G, LinearBlockStandardPair (GaloisField 3 1) W β (j' p₀)) ∧
        ∀ a, a ≠ p₀ → Commutes β (j' a) := by
  have hΩ := c.hΩ
  obtain ⟨W, hW⟩ := hKβ
  have hadm : StatedLieAdmissible .POmegaPlus 6 3 1 := ⟨Nat.prime_three, le_rfl, by norm_num⟩
  have hPat := TypeEPattern.patternLemma_plus (p := 3) (f := 1) (by norm_num : 4 ≤ 6)
  obtain ⟨n, H, hct, -⟩ := CFSG.ClassicalInvolution.ModelFacts.hasBruhatDatum .POmegaPlus 6 3 1
    Nat.prime_three trivial hadm
  obtain ⟨k₀, v, hTT⟩ := hT
  have hv : v ≠ 0 := by
    intro hv0
    obtain ⟨N, hNz, hNK, hKN, hβN⟩ := c.exists_moved_layer_member layerGeomD6_3 hsingle hβ htβ
      ⟨W, hW⟩ (hj.mem m₀).1 (hj.commK m₀) hβm₀
    obtain ⟨R, hR, hNR⟩ := c.exists_fund_of_ne hNz hNK
    have hgen := Balance.iSup_rankOneImage_eq_range .POmegaPlus 6 3 1 Nat.prime_three trivial
      hadm c.d.ψ k₀
    have hfixrange : ∀ x ∈ c.d.ψ.range, Gaps.locAut hΩ.conjInvariant ht x = x := by
      intro x hx
      rw [← hgen] at hx
      let Fix : Subgroup (locQuot Ω z) :=
        MonoidHom.eqLocus (Gaps.locAut hΩ.conjInvariant ht).toMonoidHom (MonoidHom.id _)
      have hle : (⨆ γ ∈ (modelUniv .POmegaPlus 6 3 1 Nat.prime_three).D.roots,
          Balance.rankOneImage (modelUniv .POmegaPlus 6 3 1 Nat.prime_three).D c.d.ψ k₀ γ) ≤
            Fix := by
        refine iSup₂_le fun γ hγ y hy => ?_
        exact ((hTT γ hγ).2).mpr (by simp [hv0, charOf]) y hy
      exact hle hx
    have hNt : N ≤ Subgroup.centralizer ({t} : Set G) :=
      (locAut_fixed_iff3 hΩ c.hex c.hP1 c.hO3 ht hNz).mpr fun x hx => hfixrange x (by
        rw [hNR] at hx
        obtain ⟨r, -, rfl⟩ := hx
        exact ⟨r, rfl⟩)
    exact hβN (c.commutes_partner_of_centralizes hMFZ hsingle D hβ htβ ⟨W, hW⟩ hNz hNt hKN)
  obtain ⟨y, hy, g, q, hjimg', hroot⟩ := Gaps.exists_adapted_frame_normal hΩ.conjInvariant
    c.d.ψ hct hPat ht v hv k₀ hTT hjimg
  obtain ⟨p₀, rfl⟩ : ∃ p₀ : Fin 6, p₀ = q := ⟨q, rfl⟩
  have hfixed : ∀ a : Fin 6, ((∀ x ∈ locImg Ω z (conjSub y (j a)),
      Gaps.locAut hΩ.conjInvariant ht x = x) ↔ a ≠ p₀) ∧
      (locImg Ω z (conjSub y (j a))).map (Gaps.locAut hΩ.conjInvariant ht).toMonoidHom =
        locImg Ω z (conjSub y (j a)) := by
    intro a
    obtain ⟨hn, hf⟩ := hroot (Pi.single a 1)
      (RouteD.single_mem_roots (modelUniv .POmegaPlus 6 3 1 Nat.prime_three).D a)
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
    have hNt := (locAut_fixed_iff3 hΩ c.hex c.hP1 c.hO3 ht (hmemy a)).mpr h1
    exact c.commutes_partner_of_centralizes hMFZ hsingle D hβ htβ ⟨W, hW⟩ (hmemy a) hNt
      (hj'.commK a)
  have hmov : ¬ Commutes β (conjSub y (j p₀)) := fun h => by
    have hNt : conjSub y (j p₀) ≤ Subgroup.centralizer ({t} : Set G) := fun n hn =>
      Subgroup.mem_centralizer_singleton_iff.mpr (h t htβ.mem n hn).symm
    have := (hfixed p₀).1.mp ((locAut_fixed_iff3 hΩ c.hex c.hP1 c.hO3 ht (hmemy p₀)).mp hNt)
    exact this rfl
  have hnorm : conjSub t (conjSub y (j p₀)) = conjSub y (j p₀) := by
    have h1 := (hfixed p₀).2
    rw [Gaps.locAut_locImg hΩ.conjInvariant ht] at h1
    exact locImg_injOn3 hΩ c.hex c.hP1 c.hO3 (hmemt _ (hmemy p₀)) (hmemy p₀) h1
  have hstd : ∃ W : Subgroup G,
      LinearBlockStandardPair (GaloisField 3 1) W β (conjSub y (j p₀)) := by
    obtain ⟨b, hbp, hb1, hb2⟩ := TypeEPattern.edgeD6_far p₀
    obtain ⟨wJ, hwJ⟩ := hΩ.classical _ (hmemy p₀).1
    obtain ⟨xb, hxb⟩ := hΩ.classical _ (hmemy b).1
    exact c.scenarioC layerGeomD6_3 hsingle hβ htβ ⟨W, hW⟩ (hmemy p₀).1 (hmemy b).1 hwJ hxb
      (hj'.commK p₀) (hj'.commK b) (hfix' b hbp) (hj'.comm b p₀ hbp hb1 hb2).symm hmov hnorm
  have hp₀ : p₀ = 4 ∨ p₀ = 5 := by
    by_contra hnot
    by_cases h0 : p₀ = 0
    · subst h0
      exact c.attached_zero_false hsingle hj' hβ htβ ⟨W, hW⟩ hfix' hstd
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
        (conjSub_mem_fundamentalSubgroups (TypeEPattern.rootθ6_mem_fundamental (p := 3) (f := 1))
          g)
      have hNeq' : locImg Ω z N = (TypeEPattern.rootθ6 3 1).map
          (c.d.ψ.comp (MulAut.conj g).toMonoidHom) := by
        rw [hNeq]
        unfold conjSub
        rw [Subgroup.map_map]
      have hNnode : ∀ a : Fin 6, a ≠ 1 → Commutes N (conjSub y (j a)) := fun a ha =>
        commutes_of_commutes_locImg3 hΩ c.hex c.hP1 c.hO3 hNz (hmemy a) (by
          rw [hNeq', hjimg' a]
          exact commutes_map _ (TypeEPattern.commutes_rootθ6_rankOne ha))
      have hNt : N ≤ Subgroup.centralizer ({t} : Set G) :=
        (locAut_fixed_iff3 hΩ c.hex c.hP1 c.hO3 ht hNz).mpr fun x hx =>
          (hθf.mpr (TypeEPattern.thetaD6_even h1 h3)) x (by rw [hNeq'] at hx; exact hx)
      exact c.attached_twin_false hsingle hMFZ D hj' hβ htβ ⟨W, hW⟩
        (hfix' 0 (fun h => h0 h.symm)) hNz hNK hNnode hNt
  exact ⟨fun a => conjSub y (j a), hj', p₀, hp₀, hstd, hfix'⟩

end Attached

section Rows

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {K : Subgroup G} {z : G}

theorem exists_partnerAt_E7_proved (hMFZ : Gaps.FundNoncentral 3)
    (c : ETCtx3 .POmegaPlus 6 Ω K z) (hsingle : ∀ L ∈ Ω, ∃ g : G, L = conjSub g K) {ι : Type}
    (D : LieSystemData3 ι (locQuot Ω z) (locFamily Ω z))
    (hTor : ∀ j : Fin 6 → Subgroup G, NodeSystem 3 1 (edgeD 6) Ω K z j →
      (∀ a, locImg Ω z (j a) =
        (rankOne (modelUniv .POmegaPlus 6 3 1 Nat.prime_three).D.rootGroup a).map c.d.ψ) →
      ∀ β ∈ Ω, ∀ t : G, IsClassicalMember3 β t →
        (∃ W : Subgroup G, LinearBlockStandardPair (GaloisField 3 1) W K β) →
        Commutes β (j 0) → ∀ ht : t * z * t⁻¹ = z, ToralNormalE3 c ht) :
    ∃ j : Fin 6 → Subgroup G, NodeSystem 3 1 (edgeD 6) Ω K z j ∧
      (PartnerAt 3 1 Ω j 4 ∨ PartnerAt 3 1 Ω j 5) := by
  have hadmY : StatedLieAdmissible .POmegaPlus 6 3 1 := ⟨Nat.prime_three, le_rfl, by norm_num⟩
  obtain ⟨j, hj, hjimg⟩ := c.exists_nodeSystem_D6' hadmY
  obtain ⟨β, hβΩ, hKβ, hβ0⟩ :=
    c.exists_partner_transport hsingle (hj.mem 0).1 (hj.ne_K 0) (hj.commK 0)
  obtain ⟨t, htβ⟩ := c.hΩ.classical β hβΩ
  have ht : t * z * t⁻¹ = z := c.partner_involution_commutes htβ hKβ
  have hTN := hTor j hj hjimg β hβΩ t htβ hKβ hβ0 ht
  obtain ⟨j', hj', p₀, hp₀, ⟨W, hW⟩, hc⟩ := c.exists_attached_D6 hsingle hMFZ D hj hjimg hβΩ htβ
    hKβ hβ0 ht hTN
  refine ⟨j', hj', ?_⟩
  rcases hp₀ with rfl | rfl
  · exact Or.inl ⟨β, hβΩ, ⟨W, hW⟩, hc⟩
  · exact Or.inr ⟨β, hβΩ, ⟨W, hW⟩, hc⟩

end Rows

theorem partnerExists3E7_proved (h3 : OddThreeFreeInput) : PartnerExists3E7Input := by
  intro G _ _ _ hnab K z hR hshape
  obtain ⟨c⟩ := nonempty_etctx3_D6 h3 hR hshape
  obtain ⟨ι, hι, D, -⟩ := id hshape
  have hsingle : ∀ L ∈ conjClass3 K, ∃ g : G, L = conjSub g K := by
    rintro L ⟨g, rfl⟩
    exact ⟨g, rfl⟩
  exact exists_partnerAt_E7_proved (Gaps.fundNoncentral 3) c hsingle D
    (e7PartnerToral3 G hnab K z hR hshape c)

theorem piece3E7_proved (h3 : OddThreeFreeInput) : Piece3E7 :=
  piece3E7_of_exists h3 (partnerExists3E7_proved h3)

end CFSG.ClassicalInvolution.Q3.Q3W
