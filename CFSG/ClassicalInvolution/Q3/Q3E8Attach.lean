module

public import CFSG.ClassicalInvolution.Q3.Q3E8Facts

public section

namespace CFSG.ClassicalInvolution.Q3.Q3W

open CFSG.Open hiding StatedLieTag StatedLieAdmissible
open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.RouteD
  CFSG.ClassicalInvolution.RouteD.Gaps CFSG.Assembly.LowTwoRank CFSG.LieType.Universal
  CFSG.LieType CFSG.LieType.RootSystem CFSG.LieType.CurtisTits CFSG.Timmesfeld
open CFSG.ClassicalInvolution.WeakCT (LinearBlockStandardPair)
open scoped MatrixGroups commutatorElement

set_option linter.unusedSectionVars false


section Attach

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {K : Subgroup G} {z : G}

theorem ETCtx3.exists_attached_at (c : ETCtx3 .E7 0 Ω K z)
    (hsingle : ∀ L ∈ Ω, ∃ g : G, L = conjSub g K) (hMFZ : Gaps.FundNoncentral 3) {ι : Type}
    (D : LieSystemData3 ι (locQuot Ω z) (locFamily Ω z)) (hLG : E8LayerGeom3)
    {j : Fin 7 → Subgroup G} (hj : NodeSystem 3 1 (edgeE 7) Ω K z j)
    (hjimg : ∀ a, locImg Ω z (j a) =
      (rankOne (modelUniv .E7 0 3 1 Nat.prime_three).D.rootGroup a).map c.d.ψ)
    {β : Subgroup G} (hβ : β ∈ Ω) {t : G} (htβ : IsClassicalMember3 β t)
    (hKβ : ∃ W : Subgroup G, LinearBlockStandardPair (GaloisField 3 1) W K β)
    {m₀ : Fin 7} (hβm₀ : Commutes β (j m₀)) (ht : t * z * t⁻¹ = z) (hT : ToralNormalE3 c ht) :
    ∃ j' : Fin 7 → Subgroup G, NodeSystem 3 1 (edgeE 7) Ω K z j' ∧ ∃ p₀ : Fin 7,
      (∃ W : Subgroup G, LinearBlockStandardPair (GaloisField 3 1) W β (j' p₀)) ∧
      (∀ a, a ≠ p₀ → Commutes β (j' a)) ∧
      ∃ g : TypeE8.K7 3 1, ToralNormalAt3 c ht g p₀ := by
  have hΩ := c.hΩ
  have hadm : StatedLieAdmissible .E7 0 3 1 := ⟨Nat.prime_three, le_rfl, rfl⟩
  obtain ⟨W, hW⟩ := hKβ
  obtain ⟨n, H, hct, -⟩ := CFSG.ClassicalInvolution.ModelFacts.hasBruhatDatum .E7 0 3 1
    Nat.prime_three trivial hadm
  obtain ⟨k₀, v, hTT⟩ := hT
  have hv : v ≠ 0 := by
    intro hv0
    obtain ⟨N, hNz, hNK, hKN, hβN⟩ := c.exists_moved_layer_member hLG hsingle hβ htβ
      ⟨W, hW⟩ (hj.mem m₀).1 (hj.commK m₀) hβm₀
    obtain ⟨R, hR, hNR⟩ := c.exists_fund_of_ne hNz hNK
    have hgen := Balance.iSup_rankOneImage_eq_range .E7 0 3 1 Nat.prime_three trivial hadm
      c.d.ψ k₀
    have hfixrange : ∀ x ∈ c.d.ψ.range, Gaps.locAut hΩ.conjInvariant ht x = x := by
      intro x hx
      rw [← hgen] at hx
      let Fix : Subgroup (locQuot Ω z) :=
        MonoidHom.eqLocus (Gaps.locAut hΩ.conjInvariant ht).toMonoidHom (MonoidHom.id _)
      have hle : (⨆ γ ∈ (modelUniv .E7 0 3 1 Nat.prime_three).D.roots,
          Balance.rankOneImage (modelUniv .E7 0 3 1 Nat.prime_three).D c.d.ψ k₀ γ) ≤ Fix := by
        refine iSup₂_le fun γ hγ y hy => ?_
        exact ((hTT γ hγ).2).mpr (by simp [hv0, charOf]) y hy
      exact hle hx
    have hNt : N ≤ Subgroup.centralizer ({t} : Set G) :=
      (locAut_fixed_iff3 hΩ c.hex c.hP1 c.hO3 ht hNz).mpr fun x hx => hfixrange x (by
        rw [hNR] at hx
        obtain ⟨r, -, rfl⟩ := hx
        exact ⟨r, rfl⟩)
    exact hβN (c.commutes_partner_of_centralizes hMFZ hsingle D hβ htβ ⟨W, hW⟩ hNz hNt hKN)
  obtain ⟨y, hy, g, p₀, hjimg', hframe⟩ := Gaps.exists_adapted_frame_normal hΩ.conjInvariant
    c.d.ψ hct TypeEPattern.patternLemma_E7_model ht v hv k₀ hTT hjimg
  have hmap : ∀ S : Subgroup (modelUniv .E7 0 3 1 Nat.prime_three).K,
      (conjSub g S).map c.d.ψ = S.map (c.d.ψ.comp (MulAut.conj g).toMonoidHom) := fun S => by
    unfold conjSub
    rw [Subgroup.map_map]
  have hTg : ToralNormalAt3 c ht g p₀ := by
    intro γ hγ
    rw [hmap]
    exact hframe γ hγ
  have hfixed : ∀ a : Fin 7, ((∀ x ∈ locImg Ω z (conjSub y (j a)),
      Gaps.locAut hΩ.conjInvariant ht x = x) ↔ a ≠ p₀) ∧
      (locImg Ω z (conjSub y (j a))).map (Gaps.locAut hΩ.conjInvariant ht).toMonoidHom =
        locImg Ω z (conjSub y (j a)) := by
    intro a
    obtain ⟨hn, hf⟩ := hframe (Pi.single a 1)
      (RouteD.single_mem_roots (modelUniv .E7 0 3 1 Nat.prime_three).D a)
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
  obtain ⟨b, hbp, hb1, hb2⟩ := TypeEPattern.edgeE7_far p₀
  obtain ⟨wJ, hwJ⟩ := hΩ.classical _ (hmemy p₀).1
  obtain ⟨xb, hxb⟩ := hΩ.classical _ (hmemy b).1
  have hstd := c.scenarioC hLG hsingle hβ htβ ⟨W, hW⟩ (hmemy p₀).1 (hmemy b).1 hwJ hxb
    (hj'.commK p₀) (hj'.commK b) (hfix' b hbp) (hj'.comm b p₀ hbp hb1 hb2).symm hmov hnorm
  exact ⟨fun a => conjSub y (j a), hj', p₀, hstd, hfix', g, hTg⟩

theorem exists_partnerAt_E8_proved (hMFZ : Gaps.FundNoncentral 3) (c : ETCtx3 .E7 0 Ω K z)
    (hsingle : ∀ L ∈ Ω, ∃ g : G, L = conjSub g K) {ι : Type}
    (D : LieSystemData3 ι (locQuot Ω z) (locFamily Ω z)) (hLG : E8LayerGeom3)
    (hTor : ∀ j : Fin 7 → Subgroup G, NodeSystem 3 1 (edgeE 7) Ω K z j →
      (∀ a, locImg Ω z (j a) =
        (rankOne (modelUniv .E7 0 3 1 Nat.prime_three).D.rootGroup a).map c.d.ψ) →
      ∀ β ∈ Ω, ∀ t : G, IsClassicalMember3 β t →
        (∃ W : Subgroup G, LinearBlockStandardPair (GaloisField 3 1) W K β) →
        Commutes β (j 0) → ∀ ht : t * z * t⁻¹ = z, ToralNormalE3 c ht)
    (hExcl : ∀ β ∈ Ω, ∀ t : G, IsClassicalMember3 β t →
      (∃ W : Subgroup G, LinearBlockStandardPair (GaloisField 3 1) W K β) →
      ∀ ht : t * z * t⁻¹ = z, ∀ (g : TypeE8.K7 3 1) (p₀ : Fin 7),
        ToralNormalAt3 c ht g p₀ → p₀ = 6) :
    ∃ j : Fin 7 → Subgroup G, NodeSystem 3 1 (edgeE 7) Ω K z j ∧ PartnerAt 3 1 Ω j 6 := by
  have hadmY : StatedLieAdmissible .E7 0 3 1 := ⟨Nat.prime_three, le_rfl, rfl⟩
  obtain ⟨j, hj, hjimg⟩ := c.exists_nodeSystem_E7' hadmY
  obtain ⟨β, hβΩ, hKβ, hβ0⟩ :=
    c.exists_partner_transport hsingle (hj.mem 0).1 (hj.ne_K 0) (hj.commK 0)
  obtain ⟨t, htβ⟩ := c.hΩ.classical β hβΩ
  have ht : t * z * t⁻¹ = z := c.partner_involution_commutes htβ hKβ
  have hTN := hTor j hj hjimg β hβΩ t htβ hKβ hβ0 ht
  obtain ⟨j', hj', p₀, ⟨W, hW⟩, hc, g, hg⟩ := c.exists_attached_at hsingle hMFZ D hLG hj hjimg
    hβΩ htβ hKβ hβ0 ht hTN
  refine ⟨j', hj', ?_⟩
  rcases hExcl β hβΩ t htβ hKβ ht g p₀ hg with rfl
  exact ⟨β, hβΩ, ⟨W, hW⟩, hc⟩

end Attach

end CFSG.ClassicalInvolution.Q3.Q3W
