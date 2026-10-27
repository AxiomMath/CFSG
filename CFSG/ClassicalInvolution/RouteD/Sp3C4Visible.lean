module

public import CFSG.ClassicalInvolution.RouteD.Sp3C4Link
public import CFSG.ClassicalInvolution.RouteD.TypeF4TwinPerpCount

public section

namespace CFSG.ClassicalInvolution.RouteD.Sp3C4

open CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Models CFSG.Assembly.LowTwoRank
  CFSG.LieType.Universal CFSG.ClassicalInvolution.RouteD
  CFSG.ClassicalInvolution.RouteD.NonClassical CFSG.ClassicalInvolution.RouteD.Gaps
open CFSG.ClassicalInvolution.Models.SymplecticPairs (planeGroup IsHyperbolicPlane stdPlane
  isHyperbolicPlane_stdPlane longBlock longInv form)
open scoped MatrixGroups

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}

theorem exists_layer_conj_of_ne {m : ℕ} (hm : 2 ≤ m) (hq : 5 ≤ p ^ f) (hΩ : InClass p f Ω)
    (hex : ExactMembers Ω) {K : Subgroup G} (hK : K ∈ Ω) {z : G} (hz : IsClassicalMember p f K z)
    (hP1 : LocalOddCentral Ω {z}) (d : ShapeCDict p f m Ω z) {L₁ L₂ : Subgroup G}
    (h₁ : L₁ ∈ centralizingMembers Ω {z}) (h₂ : L₂ ∈ centralizingMembers Ω {z}) (n₁ : L₁ ≠ K)
    (n₂ : L₂ ≠ K) :
    ∃ y : G, y ∈ locLayer Ω z ∧ conjSub y L₁ = L₂ ∧ conjSub y K = K := by
  have hKz : K ∈ centralizingMembers Ω {z} := ⟨hK, le_centralizer_of_isClassicalMember hz⟩
  obtain ⟨P₁, hP₁, hL₁⟩ := typeC_exists_plane_of_ne hm hq hΩ hex hK hz hP1 d h₁ n₁
  obtain ⟨P₂, hP₂, hL₂⟩ := typeC_exists_plane_of_ne hm hq hΩ hex hK hz hP1 d h₂ n₂
  obtain ⟨g₁, hg₁⟩ := Models.SymplecticPairs.exists_planeGroup_eq_conj_longBlock hP₁
    (⟨0, by omega⟩ : Fin m)
  obtain ⟨g₂, hg₂⟩ := Models.SymplecticPairs.exists_planeGroup_eq_conj_longBlock hP₂
    (⟨0, by omega⟩ : Fin m)
  obtain ⟨y, hy⟩ := QuotientGroup.mk_surjective (d.ψ (g₂ * g₁⁻¹))
  have hyx : (y : G) ∈ Subgroup.centralizer ({z} : Set G) :=
    centralizingLayer_le_centralizer Ω {z} y.2
  have hcent : ∀ {L : Subgroup G}, L ∈ centralizingMembers Ω {z} →
      conjSub (y : G) L ∈ centralizingMembers Ω {z} := by
    intro L hL
    refine ⟨hΩ.conjInvariant _ L hL.1, fun a ha => ?_⟩
    rw [mem_conjSub_iff] at ha
    have hx' := hL.2 ha
    have : a = (y : G) * ((y : G)⁻¹ * a * (y : G)) * (y : G)⁻¹ := by group
    rw [this]
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hyx hx') ((Subgroup.inv_mem _) hyx)
  refine ⟨y, y.2, ?_, ?_⟩
  · refine locImg_injOn hΩ hP1 (hcent h₁) h₂ ?_
    rw [Gaps.locImg_conjSub_layer, hL₁, hL₂,
      show Gaps.locMk Ω z y = d.ψ (g₂ * g₁⁻¹) from hy, hg₁, hg₂, Subgroup.map_map,
      Subgroup.map_map, Subgroup.map_map]
    congr 1
    ext a
    simp [mul_assoc]
  · refine locImg_injOn hΩ hP1 (hcent hKz) hKz ?_
    rw [Gaps.locImg_conjSub_layer]
    have hKQ := typeC_locImg_self_le_Q₀ hm hq hK hz d
    have hfix : ∀ a ∈ locImg Ω z K, (MulAut.conj (Gaps.locMk Ω z y)) a = a := by
      intro a ha
      have hc := d.commutes a (hKQ ha) (Gaps.locMk Ω z y)
        (by rw [show Gaps.locMk Ω z y = d.ψ (g₂ * g₁⁻¹) from hy]; exact ⟨_, rfl⟩)
      simp only [MulAut.conj_apply]
      rw [← hc]
      group
    ext a
    constructor
    · rintro ⟨b, hb, rfl⟩
      simp only [MulEquiv.coe_toMonoidHom]
      rw [hfix b hb]
      exact hb
    · intro ha
      exact ⟨a, ha, hfix a ha⟩

section Standard

variable {K : Subgroup G} {z : G}

theorem cliqueAt_standard (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f) (hΩ : InClass p f Ω)
    (hex : ExactMembers Ω) (hK : K ∈ Ω) (hz : IsClassicalMember p f K z)
    (hP1 : LocalOddCentral Ω {z}) (d : ShapeCDict p f 3 Ω z) {j₀ : Subgroup G}
    (hj₀ : j₀ ∈ centralizingMembers Ω {z})
    (hj₀img : locImg Ω z j₀ =
      (planeGroup (stdPlane (GaloisField p f) 3 (Fin.last 2))).map d.ψ) {w₀ : G}
    (hw₀ : IsClassicalMember p f j₀ w₀) :
    CliqueAt Ω K j₀ z w₀ := by
  classical
  have h2 : (2 : GaloisField p f) ≠ 0 :=
    CFSG.ClassicalInvolution.ModelFacts.two_ne_zero_galoisField f hp2
  have h4 : 4 ≤ Nat.card (GaloisField p f) := four_le_natCard_galoisField hq
  have hexF : ∃ a : (GaloisField p f)ˣ, (a : GaloisField p f) ≠ ((a⁻¹ : (GaloisField p f)ˣ) : _) :=
    exists_unit_ne_inv hq
  have hker := d.ker_le
  have hj₀Y : j₀ ≤ locLayer Ω z := le_centralizingLayer hj₀
  have hw₀Y : w₀ ∈ locLayer Ω z := hj₀Y hw₀.mem
  have hψw : d.ψ (longInv (GaloisField p f) 3 (Fin.last 2)) = locElt Ω z w₀ hw₀Y :=
    psi_longInv hp2 d hj₀Y hj₀img hw₀.mem hw₀.orderOf_eq_two
  have hperf : ∀ R ∈ planeGroupSet (GaloisField p f) 3, R ≤ ⁅R, R⁆ := by
    rintro _ ⟨P, hP, rfl⟩
    exact planeGroup_perfect h4 (by norm_num) hP
  have hcent : ∀ {L : Subgroup G}, L ∈ centralizingMembers Ω {z} →
      ∀ {R : Subgroup (StatedSp 3 (GaloisField p f))}, R ≤ ⁅R, R⁆ →
      locImg Ω z L = R.map d.ψ →
      (L ≤ Subgroup.centralizer ({w₀} : Set G) ↔
        R ≤ Subgroup.centralizer ({longInv (GaloisField p f) 3 (Fin.last 2)} : Set _)) := by
    intro L hL R hR hLR
    have h1 := le_centralizer_iff_locImg hΩ hP1 hL ⟨w₀, hw₀Y⟩
    have h2' := le_centralizer_iff_map d.ψ hker hR (longInv (GaloisField p f) 3 (Fin.last 2))
    rw [h2', hψw, ← hLR]
    exact h1
  have hvis : ∀ R ∈ centralizingMembers Ω {z * w₀, z}, R ≠ K → R ≠ j₀ →
      ∃ Q : SympPlanes (f4Compl p f), locImg Ω z R = (planeGroup Q.1).map d.ψ := by
    intro R hR hRK hRj
    rw [centralizingMembers_mul_iff, mem_centralizingMembers_pair] at hR
    obtain ⟨hRz, hRw⟩ := hR
    obtain ⟨P, hP, hRP⟩ := typeC_exists_plane_of_ne (by norm_num) hq hΩ hex hK hz hP1 d hRz hRK
    have hle : planeGroup P ≤
        Subgroup.centralizer ({longInv (GaloisField p f) 3 (Fin.last 2)} : Set _) :=
      (hcent hRz (hperf _ ⟨P, hP, rfl⟩) hRP).mp hRw
    obtain ⟨o, ho⟩ := (f4LayerOfPlane_bijective (p := p) (f := f) hp2).2
      ⟨some ⟨planeGroup P, ⟨P, hP, rfl⟩, hle⟩, Option.some_ne_none _⟩
    rcases o with _ | Q
    · exfalso
      apply hRj
      have h1 : f4Node p f = planeGroup P := by
        simp only [f4LayerOfPlane, f4NodePoint, Subtype.mk.injEq, Option.some.injEq] at ho
        exact ho
      refine locImg_injOn hΩ hP1 hRz hj₀ ?_
      rw [hRP, hj₀img, ← h1]
      rfl
    · have h1 : planeGroup Q.1 = planeGroup P := by
        simp only [f4LayerOfPlane, Subtype.mk.injEq, Option.some.injEq] at ho
        exact ho
      exact ⟨Q, by rw [hRP, h1]⟩
  have hmk : ∀ Q : SympPlanes (f4Compl p f), ∃ L ∈ centralizingMembers Ω {z * w₀, z},
      locImg Ω z L = (planeGroup Q.1).map d.ψ := by
    intro Q
    obtain ⟨L, hLz, -, hLimg⟩ :=
      typeC_exists_member_of_plane (by norm_num) hq hΩ hK hz hP1 d Q.2.1
    refine ⟨L, ?_, hLimg⟩
    rw [centralizingMembers_mul_iff, mem_centralizingMembers_pair]
    exact ⟨hLz, (hcent hLz (hperf _ ⟨Q.1, Q.2.1, rfl⟩) hLimg).mpr
      (sympPlane_le_centralizer hp2 Q)⟩
  intro R hR L hL hRK hRj hLK hLj
  have hRx : R ∈ centralizingMembers Ω {z * w₀} := (mem_centralizingMembers_pair.mp hR).1
  have hLx : L ∈ centralizingMembers Ω {z * w₀} := (mem_centralizingMembers_pair.mp hL).1
  have hRz : R ∈ centralizingMembers Ω {z} :=
    ⟨hRx.1, (mem_centralizingMembers_pair.mp hR).2⟩
  have hLz : L ∈ centralizingMembers Ω {z} :=
    ⟨hLx.1, (mem_centralizingMembers_pair.mp hL).2⟩
  by_cases hRL : R = L
  · subst hRL
    exact Relation.ReflTransGen.refl
  by_cases hc : Commutes R L
  swap
  · exact Linked.single ⟨hRx, hLx, hc⟩
  obtain ⟨QR, hQR⟩ := hvis R hR hRK hRj
  obtain ⟨QL, hQL⟩ := hvis L hL hLK hLj
  have hne : (planeGroup QR.1).map d.ψ ≠ (planeGroup QL.1).map d.ψ := by
    intro h
    exact hRL (locImg_injOn hΩ hP1 hRz hLz (by rw [hQR, hQL, h]))
  have hcomm : ∀ x ∈ (planeGroup QR.1).map d.ψ, ∀ y ∈ (planeGroup QL.1).map d.ψ, x * y = y * x := by
    have := commutes_locImg_of_commutes (Ω := Ω) (x := z) hc
    rw [hQR, hQL] at this
    exact this
  have horth := orth_of_commute_map h2 hexF d.ψ hker QR.2.1 QL.2.1 hne hcomm
  obtain ⟨u, v, huv, hQRspan⟩ := QR.2.1
  obtain ⟨u', v', hu'v', hQLspan⟩ := QL.2.1
  have hu : u ∈ QR.1 := by rw [hQRspan]; exact Submodule.subset_span (by simp)
  have hv : v ∈ QR.1 := by rw [hQRspan]; exact Submodule.subset_span (by simp)
  have hu' : u' ∈ QL.1 := by rw [hQLspan]; exact Submodule.subset_span (by simp)
  have hv' : v' ∈ QL.1 := by rw [hQLspan]; exact Submodule.subset_span (by simp)
  have o1 : form u u' = 0 := horth u hu u' hu'
  have o2 : form u v' = 0 := horth u hu v' hv'
  have o3 : form v u' = 0 := horth v hv u' hu'
  have o4 : form v v' = 0 := horth v hv v' hv'
  have o3' : form u' v = 0 := by rw [Models.SymplecticPairs.form_antisymm, o3, neg_zero]
  have hform : form (u + u') ((2 : GaloisField p f)⁻¹ • (v + v')) = 1 := by
    rw [Models.SymplecticPairs.form_smul_right, Models.SymplecticPairs.form_add_right,
      Models.SymplecticPairs.form_add_left, Models.SymplecticPairs.form_add_left, huv, o2, o3',
      hu'v']
    have : (1 : GaloisField p f) + 0 + (0 + 1) = 2 := by ring
    rw [this, inv_mul_cancel₀ h2]
  have hhyp : IsHyperbolicPlane
      (Submodule.span (GaloisField p f) {u + u', (2 : GaloisField p f)⁻¹ • (v + v')}) :=
    ⟨_, _, hform, rfl⟩
  have hle : Submodule.span (GaloisField p f) {u + u', (2 : GaloisField p f)⁻¹ • (v + v')} ≤
      f4Compl p f := by
    rw [Submodule.span_le]
    intro x hx
    rcases hx with rfl | rfl
    · exact (f4Compl p f).add_mem (QR.2.2 hu) (QL.2.2 hu')
    · exact (f4Compl p f).smul_mem _ ((f4Compl p f).add_mem (QR.2.2 hv) (QL.2.2 hv'))
  obtain ⟨N, hN, hNimg⟩ := hmk ⟨_, hhyp, hle⟩
  have hNx : N ∈ centralizingMembers Ω {z * w₀} := (mem_centralizingMembers_pair.mp hN).1
  have hNz : N ∈ centralizingMembers Ω {z} := ⟨hNx.1, (mem_centralizingMembers_pair.mp hN).2⟩
  have hmem1 : u + u' ∈ Submodule.span (GaloisField p f)
      {u + u', (2 : GaloisField p f)⁻¹ • (v + v')} := Submodule.subset_span (by simp)
  have hRN : ¬ Commutes R N := by
    intro hcRN
    by_cases hRN' : R = N
    · subst hRN'
      obtain ⟨z', hz'⟩ := hΩ.classical R hRx.1
      exact not_commutes_self_of_isClassicalMember hz' hcRN
    · have hne' : (planeGroup QR.1).map d.ψ ≠
          (planeGroup (Submodule.span (GaloisField p f)
            {u + u', (2 : GaloisField p f)⁻¹ • (v + v')})).map d.ψ := by
        intro h
        exact hRN' (locImg_injOn hΩ hP1 hRz hNz (by rw [hQR, hNimg, h]))
      have hcomm' : ∀ x ∈ (planeGroup QR.1).map d.ψ, ∀ y ∈ (planeGroup (Submodule.span
          (GaloisField p f) {u + u', (2 : GaloisField p f)⁻¹ • (v + v')})).map d.ψ,
          x * y = y * x := by
        have := commutes_locImg_of_commutes (Ω := Ω) (x := z) hcRN
        rw [hQR, hNimg] at this
        exact this
      have h0 := orth_of_commute_map h2 hexF d.ψ hker QR.2.1 hhyp hne' hcomm' v hv _ hmem1
      rw [Models.SymplecticPairs.form_add_right, Models.SymplecticPairs.form_antisymm u v, huv,
        o3] at h0
      have : (-1 : GaloisField p f) + 0 = 0 := h0
      simp at this
  have hmem2 : v' ∈ QL.1 := hv'
  have hNL : ¬ Commutes N L := by
    intro hcNL
    by_cases hNL' : N = L
    · subst hNL'
      obtain ⟨z', hz'⟩ := hΩ.classical N hNx.1
      exact not_commutes_self_of_isClassicalMember hz' hcNL
    · have hne' : (planeGroup (Submodule.span (GaloisField p f)
            {u + u', (2 : GaloisField p f)⁻¹ • (v + v')})).map d.ψ ≠
            (planeGroup QL.1).map d.ψ := by
        intro h
        exact hNL' (locImg_injOn hΩ hP1 hNz hLz (by rw [hQL, hNimg, h]))
      have hcomm' : ∀ x ∈ (planeGroup (Submodule.span (GaloisField p f)
          {u + u', (2 : GaloisField p f)⁻¹ • (v + v')})).map d.ψ,
          ∀ y ∈ (planeGroup QL.1).map d.ψ, x * y = y * x := by
        have := commutes_locImg_of_commutes (Ω := Ω) (x := z) hcNL
        rw [hNimg, hQL] at this
        exact this
      have h0 := orth_of_commute_map h2 hexF d.ψ hker hhyp QL.2.1 hne' hcomm' _ hmem1 v' hv'
      rw [Models.SymplecticPairs.form_add_left, o2, hu'v'] at h0
      have : (0 : GaloisField p f) + 1 = 0 := h0
      simp at this
  exact (Linked.single ⟨hRx, hNx, hRN⟩).trans (Linked.single ⟨hNx, hLx, hNL⟩)

end Standard

section Twin

variable {K : Subgroup G} {z : G}

theorem unlinked_and_clique_of_not_f4Linked (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f) (hΩ : InClass p f Ω)
    (hex : ExactMembers Ω) (hK : K ∈ Ω) (hz : IsClassicalMember p f K z)
    (hP1 : LocalOddCentral Ω {z}) (d : ShapeCDict p f 3 Ω z)
    (hnl : ¬ ∀ M ∈ Ω, ∀ w : G, IsClassicalMember p f M w → M ≠ K → Commutes K M →
      ∀ R ∈ centralizingMembers Ω {z * w, z}, Linked Ω (z * w) K R)
    {M : Subgroup G} (hM : M ∈ Ω) {w : G} (hw : IsClassicalMember p f M w) (hMK : M ≠ K)
    (hKM : Commutes K M) : UnlinkedAt Ω K z w ∧ CliqueAt Ω K M z w := by
  classical
  have h2 : (2 : GaloisField p f) ≠ 0 :=
    CFSG.ClassicalInvolution.ModelFacts.two_ne_zero_galoisField f hp2
  have hKz : K ∈ centralizingMembers Ω {z} := ⟨hK, le_centralizer_of_isClassicalMember hz⟩
  have hMz : M ∈ centralizingMembers Ω {z} :=
    ⟨hM, le_centralizer_of_commutes (Commutes.symm hKM) hz.mem⟩
  have hfixz : ∀ y : G, y ∈ locLayer Ω z → y * z * y⁻¹ = z := by
    intro y hy
    have hyx : y ∈ Subgroup.centralizer ({z} : Set G) := centralizingLayer_le_centralizer Ω {z} hy
    rw [mul_inv_eq_iff_eq_mul]
    exact Subgroup.mem_centralizer_singleton_iff.mp hyx
  obtain ⟨j₀, hj₀z, hj₀K, hj₀img⟩ := typeC_exists_member_of_plane (by norm_num) hq hΩ hK hz hP1 d
    (isHyperbolicPlane_stdPlane (K := GaloisField p f) (n := 3) (Fin.last 2))
  obtain ⟨w₁, hw₁⟩ := hΩ.classical j₀ hj₀z.1
  obtain ⟨y, hyY, hyj, hyK⟩ := exists_layer_conj_of_ne (by norm_num) hq hΩ hex hK hz hP1 d hj₀z
    hMz hj₀K hMK
  have hyw : y * w₁ * y⁻¹ = w := by
    have hcl := hw₁.conj y
    rw [hyj] at hcl
    exact Gaps.unique_involution_of_isClassicalMember h2 (hex M hM) hcl hw
  have hC : CliqueAt Ω K M z w := by
    have := (cliqueAt_standard hp2 hq hΩ hex hK hz hP1 d hj₀z hj₀img hw₁).conj
      hΩ.conjInvariant y
    rwa [hyK, hyj, hfixz y hyY, hyw] at this
  refine ⟨?_, hC⟩
  have hnl' : ∃ M₀ ∈ Ω, ∃ w₀ : G, IsClassicalMember p f M₀ w₀ ∧ M₀ ≠ K ∧ Commutes K M₀ ∧
      UnlinkedAt Ω K z w₀ := by
    by_contra hcon
    apply hnl
    intro M₀ hM₀ w₀ hw₀ hM₀K hKM₀ R hR
    by_contra hRn
    exact hcon ⟨M₀, hM₀, w₀, hw₀, hM₀K, hKM₀, R, hR, hRn⟩
  obtain ⟨M₀, hM₀, w₀, hw₀, hM₀K, hKM₀, hU₀⟩ := hnl'
  have hM₀z : M₀ ∈ centralizingMembers Ω {z} :=
    ⟨hM₀, le_centralizer_of_commutes (Commutes.symm hKM₀) hz.mem⟩
  obtain ⟨y', hy'Y, hy'M, hy'K⟩ := exists_layer_conj_of_ne (by norm_num) hq hΩ hex hK hz hP1 d
    hM₀z hMz hM₀K hMK
  have hy'w : y' * w₀ * y'⁻¹ = w := by
    have hcl := hw₀.conj y'
    rw [hy'M] at hcl
    exact Gaps.unique_involution_of_isClassicalMember h2 (hex M hM) hcl hw
  have := hU₀.conj hΩ.conjInvariant y'
  rwa [hy'K, hfixz y' hy'Y, hy'w] at this

end Twin

end CFSG.ClassicalInvolution.RouteD.Sp3C4
