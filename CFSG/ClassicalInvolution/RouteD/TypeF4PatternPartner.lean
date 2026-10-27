module

public import CFSG.ClassicalInvolution.RouteD.TypeF4PatternShape
public import CFSG.ClassicalInvolution.RouteD.ExoticTwinProofPSp

public section

namespace CFSG.ClassicalInvolution.RouteD.NonClassical

open CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Models
  CFSG.Assembly.LowTwoRank CFSG.LieType.Universal CFSG.ClassicalInvolution.RouteD
  CFSG.ClassicalInvolution.RouteD.Gaps
open CFSG.ClassicalInvolution.Models.SymplecticPairs (planeGroup IsHyperbolicPlane stdPlane
  isHyperbolicPlane_stdPlane longBlock longInv form)
open CFSG.ClassicalInvolution.WeakCT (LinearBlockStandardPair)
open scoped MatrixGroups

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G]

section Central

variable [Finite G] {Ω : Set (Subgroup G)} {K : Subgroup G} {z : G}

theorem commutes_or_eq_at_member_involution (hMFZ : Gaps.FundNoncentral p) (hΩ : InClass p f Ω)
    (hex : ExactMembers Ω) (hp2 : p ≠ 2) (hsingle : ∀ L ∈ Ω, ∃ g : G, L = conjSub g K)
    (hz : IsClassicalMember p f K z) (hP1 : LocalOddCentral Ω {z})
    (Dz : LieSystemData p f (locQuot Ω z) (locFamily Ω z)) {N : Subgroup G} (hN : N ∈ Ω) {y : G}
    (hy : IsClassicalMember p f N y) {L : Subgroup G} (hNy : N ∈ centralizingMembers Ω {y})
    (hL : L ∈ centralizingMembers Ω {y}) : Commutes N L ∨ L = N := by
  have h2 : (2 : GaloisField p f) ≠ 0 :=
    CFSG.ClassicalInvolution.ModelFacts.two_ne_zero_galoisField f hp2
  obtain ⟨g, hg⟩ := hsingle N hN
  have hyg : y = g * z * g⁻¹ :=
    unique_involution_of_isClassicalMember h2 (hex N hN) hy (hg ▸ hz.conj g)
  subst hyg
  obtain ⟨D', -, -⟩ := exists_lieSystemData_conj hΩ.conjInvariant g z Dz
  exact commutes_or_eq_of_involution hMFZ hΩ hex (localOddCentral_conj hΩ.conjInvariant g z hP1)
    D' hNy hL hy

theorem not_subset_center_mul_f4 (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f) (hMFZ : Gaps.FundNoncentral p)
    (hΩ : InClass p f Ω) (hex : ExactMembers Ω) (hsingle : ∀ L ∈ Ω, ∃ g : G, L = conjSub g K)
    (hK : K ∈ Ω) (hz : IsClassicalMember p f K z) (hP1 : LocalOddCentral Ω {z})
    (Dz : LieSystemData p f (locQuot Ω z) (locFamily Ω z)) (d : ShapeCDict p f 3 Ω z)
    {j₀ : Subgroup G} (hj₀ : j₀ ∈ centralizingMembers Ω {z})
    (hj₀img : locImg Ω z j₀ =
      (planeGroup (stdPlane (GaloisField p f) 3 (Fin.last 2))).map d.ψ) {w₀ : G}
    (hw₀ : IsClassicalMember p f j₀ w₀) :
    ¬ ({z * w₀} : Set G) ⊆ Subgroup.center G := by
  intro hcen
  have hx : z * w₀ ∈ Subgroup.center G := hcen rfl
  set F := GaloisField p f with hF
  have h2 : (2 : F) ≠ 0 := CFSG.ClassicalInvolution.ModelFacts.two_ne_zero_galoisField f hp2
  have h4 : 4 ≤ Nat.card F := four_le_natCard_galoisField hq
  have hex' := exists_unit_ne_inv hq
  have hker := d.ker_le
  let u : Fin 3 ⊕ Fin 3 → F := Pi.single (Sum.inl (Fin.last 2)) 1 + Pi.single (Sum.inl 1) 1
  let w : Fin 3 ⊕ Fin 3 → F := Pi.single (Sum.inr (Fin.last 2)) 1
  have huw : form u w = 1 := by
    simp only [u, w]
    rw [Models.SymplecticPairs.form_add_left, Models.SymplecticPairs.form_single_inl_inr,
      Models.SymplecticPairs.form_single_right]
    simp [Models.SymplecticPairs.par, Models.SymplecticPairs.sgn]
  have hH : IsHyperbolicPlane (Submodule.span F {u, w}) := ⟨u, w, huw, rfl⟩
  have hP₂ := isHyperbolicPlane_stdPlane (K := F) (n := 3) (Fin.last 2)
  obtain ⟨L, hLz, hLK, hLimg⟩ := typeC_exists_member_of_plane (by norm_num : 2 ≤ 3) hq hΩ hK hz
    hP1 d hH
  have hLw : L ≤ Subgroup.centralizer ({w₀} : Set G) := by
    refine (le_centralizer_pair_mul_iff hLz.2).mp fun n _ => ?_
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact Subgroup.mem_center_iff.mp hx n
  have hLw' : L ∈ centralizingMembers Ω {w₀} := ⟨hLz.1, hLw⟩
  have hj₀w : j₀ ∈ centralizingMembers Ω {w₀} :=
    ⟨hj₀.1, le_centralizer_of_isClassicalMember hw₀⟩
  have hnc : ¬ ⁅planeGroup (stdPlane F 3 (Fin.last 2)), planeGroup (Submodule.span F {u, w})⁆ ≤
      Subgroup.center (StatedSp 3 F) := by
    refine Models.SymplecticPairs.not_commutator_le_center_of_not_orth h2 hex' (by norm_num) hP₂
      hH (u := Pi.single (Sum.inl (Fin.last 2)) 1) (v := w)
      (Submodule.subset_span (by simp)) (Submodule.subset_span (by simp)) ?_
    simp only [w]
    rw [Models.SymplecticPairs.form_single_inl_inr]
    exact one_ne_zero
  have hperf2 : planeGroup (stdPlane F 3 (Fin.last 2)) ≤
      ⁅planeGroup (stdPlane F 3 (Fin.last 2)), planeGroup (stdPlane F 3 (Fin.last 2))⁆ :=
    planeGroup_perfect h4 (by norm_num) hP₂
  have hne : planeGroup (Submodule.span F {u, w}) ≠ planeGroup (stdPlane F 3 (Fin.last 2)) := by
    intro h
    have hHP := CFSG.ClassicalInvolution.RouteD.Exotic.planeGroup_injective h2 hH hP₂ h
    have hmem : u ∈ Submodule.span F {u, w} := Submodule.subset_span (by simp)
    rw [hHP, Models.SymplecticPairs.mem_stdPlane_iff] at hmem
    have := hmem (Sum.inl 1) (by simp [Models.SymplecticPairs.mem_coords, Fin.ext_iff])
    simp [u, Fin.ext_iff] at this
  rcases commutes_or_eq_at_member_involution hMFZ hΩ hex hp2 hsingle hz hP1 Dz hj₀.1 hw₀ hj₀w
    hLw' with hc | heq
  · apply hnc
    have h1 := commutes_locImg_of_commutes (x := z) (Ω := Ω) hc
    rw [hj₀img, hLimg] at h1
    have h3 := commutes_of_commutes_map d.ψ hker (Subgroup.isPerfect_iff.mpr
      (le_antisymm (commutator_self_le _) hperf2)) h1
    have : ⁅planeGroup (stdPlane F 3 (Fin.last 2)), planeGroup (Submodule.span F {u, w})⁆ = ⊥ := by
      rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
      intro a ha
      exact Subgroup.mem_centralizer_iff.mpr fun c hc' => (h3 a ha c hc').symm
    rw [this]
    exact bot_le
  · apply hne
    subst heq
    have := hLimg.symm.trans hj₀img
    exact injOn_map_planeGroupSet h4 (by norm_num) d.ψ hker
      ⟨_, hH, rfl⟩ ⟨_, hP₂, rfl⟩ this

end Central

section Partner

variable [Finite G] {Ω : Set (Subgroup G)} {K : Subgroup G} {z : G}

theorem exists_f4_twin_partner (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f) (hMFZ : Gaps.FundNoncentral p)
    (hΩ : InClass p f Ω) (hex : ExactMembers Ω) (hsingle : ∀ L ∈ Ω, ∃ g : G, L = conjSub g K)
    (hK : K ∈ Ω) (hz : IsClassicalMember p f K z) (hP1 : LocalOddCentral Ω {z})
    (hIH : LocalLieSystems p f Ω) (Dz : LieSystemData p f (locQuot Ω z) (locFamily Ω z))
    (d : ShapeCDict p f 3 Ω z) {j₀ : Subgroup G} (hj₀ : j₀ ∈ centralizingMembers Ω {z})
    (hj₀K : j₀ ≠ K)
    (hj₀img : locImg Ω z j₀ =
      (planeGroup (stdPlane (GaloisField p f) 3 (Fin.last 2))).map d.ψ) {w₀ : G}
    (hw₀ : IsClassicalMember p f j₀ w₀) (hKj₀ : Commutes K j₀)
    (hP1x : LocalOddCentral Ω {z * w₀})
    (hexc : ∀ (D : LieSystemData p f (locQuot Ω (z * w₀)) (locFamily Ω (z * w₀)))
      (c : Fin D.card), locImg Ω (z * w₀) K ≤ (D.hom c).range →
      locImg Ω (z * w₀) j₀ ≤ (D.hom c).range → D.tag c ≠ .G2 ∧ D.tag c ≠ .trialityD4)
    (hTable : F4PerpTableR p f) (hTwin : TwinPartnerFactTwin p f .POmegaOdd 4 f)
    (hlink : ∀ R ∈ centralizingMembers Ω {z * w₀, z}, Linked Ω (z * w₀) K R) :
    ∃ N : Subgroup G, N ∈ centralizingMembers Ω {z * w₀} ∧
      (∃ W : Subgroup G, LinearBlockStandardPair (GaloisField p f) W K N) ∧
      ∃ W : Subgroup G, LinearBlockStandardPair (GaloisField p f) W N j₀ := by
  classical
  obtain ⟨D⟩ := exists_lieSystemData hIH
    (not_subset_center_mul_f4 hp2 hq hMFZ hΩ hex hsingle hK hz hP1 Dz d hj₀ hj₀img hw₀)
  obtain ⟨φ, hφ, hφK⟩ := exists_visible_equiv_f4 hp2 hq hΩ hex hK hz hP1 d hj₀ hj₀img hw₀ hKj₀
  have hKz : K ∈ centralizingMembers Ω {z} := ⟨hK, le_centralizer_of_isClassicalMember hz⟩
  have hKvis : K ∈ centralizingMembers Ω {z * w₀, z} := by
    rw [centralizingMembers_mul_iff, mem_centralizingMembers_pair]
    exact ⟨hKz, le_centralizer_of_commutes hKj₀ hw₀.mem⟩
  have hKx : K ∈ centralizingMembers Ω {z * w₀} := (mem_centralizingMembers_pair.mp hKvis).1
  have hj₀vis : j₀ ∈ centralizingMembers Ω {z * w₀, z} := by
    rw [centralizingMembers_mul_iff, mem_centralizingMembers_pair]
    exact ⟨hj₀, le_centralizer_of_isClassicalMember hw₀⟩
  have hM0 : j₀ ∈ centralizingMembers Ω {z * w₀} := (mem_centralizingMembers_pair.mp hj₀vis).1
  have hcard : D.card = 1 := card_eq_one_of_linked hΩ hex hP1x D hKx hz.mem hlink
  have hsub : Subsingleton (Fin D.card) := Fin.subsingleton_iff_le_one.mpr hcard.le
  have hD : ∀ i, D.tag i ≠ .G2 ∧ D.tag i ≠ .trialityD4 := by
    obtain ⟨iK, hiK⟩ := exists_range_of_mem D (mem_locFamily_iff.mpr ⟨K, hKx, rfl⟩)
    obtain ⟨iM, hiM⟩ := exists_range_of_mem D (mem_locFamily_iff.mpr ⟨j₀, hM0, rfl⟩)
    intro i
    rw [hsub.elim i iK]
    exact hexc D iK hiK (hsub.elim iM iK ▸ hiM)
  obtain ⟨hsc, hperf⟩ := componentFacts_of_no_exotic D hp2 (by omega) hD
  obtain ⟨-, i₁, ht, hn, R₀, hR₀⟩ := shape_of_perpTableR hp2 hq hΩ hex hP1x D hD hKx
    hz hlink F4Layer.rel φ hφ hφK hTable
  have hexp : D.exp i₁ = f := by
    rcases D.exp_eq i₁ with h | ⟨h, -⟩
    · exact h
    · exact absurd (ht.symm.trans h) (by decide)
  have hTwin' : TwinPartnerFactTwin p f (D.tag i₁) (D.rank i₁) (D.exp i₁) := by
    rw [ht, hn, hexp]
    exact hTwin
  have hKc : K ∈ compMembers Ω (z * w₀) D i₁ := ⟨hKx, hR₀.2.2 ▸ Subgroup.map_le_range _ _⟩
  have hMc : j₀ ∈ compMembers Ω (z * w₀) D i₁ := by
    obtain ⟨j, hj⟩ := exists_range_of_mem D (mem_locFamily_iff.mpr ⟨j₀, hM0, rfl⟩)
    exact ⟨hM0, hsub.elim j i₁ ▸ hj⟩
  obtain ⟨N, hN, pKN, pNM⟩ := exists_twin_partner_of_twin hq hΩ hex hP1x D (hsc i₁) (hperf i₁)
    hTwin' hKc hMc hj₀K.symm hKj₀ hz.mem hw₀.mem hz.orderOf_eq_two hw₀.orderOf_eq_two rfl
  exact ⟨N, hN.1, pKN, pNM⟩

end Partner

end CFSG.ClassicalInvolution.RouteD.NonClassical
