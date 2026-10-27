module

public import CFSG.LocalAnalysis.GLTheoremA.CatB.HU42SE27CDefs
public import CFSG.LocalAnalysis.GLTheoremA.PartI.LevelLieU6Aut
import CFSG.LocalAnalysis.GLTheoremA.CatB.U4Tab5
import CFSG.LocalAnalysis.GLTheoremA.CatA.HSubTM5
import CFSG.LocalAnalysis.GLTheoremA.CatA.HSubTCompU6

public section

namespace CFSG.LocalAnalysis.GLTheoremA.CatB.U42Cat

open scoped commutatorElement

theorem u4Split_of_centSplitOn {G : Type} [Group G] [Finite G] (h : CentSplitOn G) {s : G}
    (hs : orderOf s = 3) {K : Subgroup G} (hK : K ≤ Subgroup.centralizer ({s} : Set G))
    (hKperf : Group.IsPerfect ↥K) (hU4 : HasU4Quot K) : U4Split s K := by
  obtain ⟨Y, Ygrp, hYcat, f, hf⟩ := hU4
  letI : Group Y := Ygrp
  have hYcard : Nat.card Y = 25920 := card_of_catalogIs_u4two hYcat
  have hdvd : Nat.card Y ∣ Nat.card ↥K := Subgroup.card_dvd_of_surjective hf
  have h5K : 5 ∣ Nat.card ↥K := dvd_trans (by rw [hYcard]; norm_num) hdvd
  rcases h s hs with hno | ⟨K₀, hsplit⟩
  · exact (hno K hK hKperf h5K).elim
  obtain ⟨hK₀le, hgen, hsK₀, hZ₀, hK₀card⟩ := hsplit
  have hs_comm : ∀ x ∈ K₀, Commute s x := fun x hx =>
    (Subgroup.mem_centralizer_singleton_iff.1 (hK₀le hx)).symm
  have commute_commutator : ∀ {a b c : G}, Commute a b → Commute a c → Commute a ⁅b, c⁆ := by
    intro a b c hab hac
    rw [commutatorElement_def]
    exact ((hab.mul_right hac).mul_right hab.inv_right).mul_right hac.inv_right
  have key1 : ∀ {a b c : G}, Commute a b → Commute a c → ⁅a * b, c⁆ = ⁅b, c⁆ := by
    intro a b c hab hac
    rw [commutatorElement_mul_left_eq_conj_mul, hac.commutator_eq, mul_one,
      (commute_commutator hab hac).eq, mul_assoc, mul_inv_cancel, mul_one]
  have key2 : ∀ {a b c : G}, Commute b a → Commute b c → ⁅a, b * c⁆ = ⁅a, c⁆ := by
    intro a b c hba hbc
    rw [commutatorElement_mul_right_eq_mul_conj, hba.symm.commutator_eq, one_mul,
      (commute_commutator hba hbc).eq, mul_assoc, mul_inv_cancel, mul_one]
  have hcomm_mem : ∀ a ∈ Subgroup.centralizer ({s} : Set G),
      ∀ b ∈ Subgroup.centralizer ({s} : Set G), ⁅a, b⁆ ∈ K₀ := by
    intro a ha b hb
    obtain ⟨n, ka, hka, rfl⟩ := hgen a ha
    obtain ⟨m, kb, hkb, rfl⟩ := hgen b hb
    have h1 : Commute (s ^ n) ka := (hs_comm ka hka).pow_left n
    have h2 : Commute (s ^ n) (s ^ m * kb) :=
      ((Commute.self_pow s m).pow_left n).mul_right ((hs_comm kb hkb).pow_left n)
    have h3 : Commute (s ^ m) ka := (hs_comm ka hka).pow_left m
    have h4 : Commute (s ^ m) kb := (hs_comm kb hkb).pow_left m
    rw [key1 h1 h2, key2 h3 h4]
    exact (Subgroup.commutator_le_self K₀)
      (Subgroup.commutator_mem_commutator (H₁ := K₀) (H₂ := K₀) hka hkb)
  have hKK : ⁅K, K⁆ = K := Subgroup.isPerfect_iff.1 hKperf
  have hle : K ≤ K₀ := by
    have hsub : ⁅K, K⁆ ≤ K₀ := by
      rw [Subgroup.commutator_le]
      intro a ha b hb
      exact hcomm_mem a (hK ha) b (hK hb)
    rwa [hKK] at hsub
  have hcard_le : Nat.card ↥K₀ ≤ Nat.card ↥K := by
    have hdvd' : Nat.card ↥K₀ ∣ Nat.card ↥K := by
      rw [hK₀card, ← hYcard]
      exact hdvd
    exact Nat.le_of_dvd Nat.card_pos hdvd'
  have hKeq : K = K₀ := Subgroup.eq_of_le_of_card_ge hle hcard_le
  rw [hKeq]
  exact ⟨hK₀le, hgen, hsK₀, hZ₀, hK₀card⟩

theorem centShapeOn_of_centSplitOn {G : Type} [Group G] [Finite G] (h : CentSplitOn G) :
    CentShapeOn G := by
  intro s hs K hK hKperf hU4
  obtain ⟨hKC, hgen, hsK, hZK, -⟩ := u4Split_of_centSplitOn h hs hK hKperf hU4
  have hs_comm : ∀ x ∈ K, Commute s x := fun x hx =>
    (Subgroup.mem_centralizer_singleton_iff.1 (hKC hx)).symm
  refine ⟨hsK, ?_, hgen, hZK⟩
  intro g hg k hk
  obtain ⟨n, k₀, hk₀, rfl⟩ := hgen g hg
  have hk₀' : Commute (s ^ n) k₀ := (hs_comm k₀ hk₀).pow_left n
  have hk' : Commute (s ^ n) k := (hs_comm k hk).pow_left n
  have hc : Commute (s ^ n) (k₀ * k * k₀⁻¹) :=
    (hk₀'.mul_right hk').mul_right hk₀'.inv_right
  have hfix : s ^ n * (k₀ * k * k₀⁻¹) * (s ^ n)⁻¹ = k₀ * k * k₀⁻¹ := by
    rw [hc.eq, mul_assoc, mul_inv_cancel, mul_one]
  rw [show (s ^ n * k₀) * k * (s ^ n * k₀)⁻¹
      = s ^ n * (k₀ * k * k₀⁻¹) * (s ^ n)⁻¹ from by group, hfix]
  exact K.mul_mem (K.mul_mem hk₀ hk) (K.inv_mem hk₀)

theorem CentShapeOn.of_mulEquiv {G G' : Type} [Group G] [Group G'] (e : G ≃* G')
    (h : CentShapeOn G) : CentShapeOn G' := by
  intro s' hs' K' hK' hperf' hU4'
  set s : G := e.symm s' with hsdef
  set K : Subgroup G := Subgroup.comap (e : G →* G') K' with hKdef
  have hse : (e : G →* G') s = s' := by simp [hsdef]
  have hse' : e s = s' := hse
  have hord : orderOf s = 3 := by
    rw [← MulEquiv.orderOf_eq e, hse', hs']
  have hrange : K' ≤ (e : G →* G').range := by
    rw [MonoidHom.range_eq_top.mpr e.surjective]
    exact le_top
  have hmap : Subgroup.map (e : G →* G') K = K' := by
    rw [hKdef]
    exact Subgroup.map_comap_eq_self hrange
  have hCmap : Subgroup.map (e : G →* G') (Subgroup.centralizer ({s} : Set G)) =
      Subgroup.centralizer ({s'} : Set G') := by
    rw [HSubT.map_centralizer_singleton, hse']
  have hK : K ≤ Subgroup.centralizer ({s} : Set G) := by
    rw [← Subgroup.map_le_map_iff_of_injective (f := (e : G →* G')) e.injective, hmap,
      hCmap]
    exact hK'
  have hperf : Group.IsPerfect ↥K := by
    rw [Subgroup.isPerfect_iff] at hperf' ⊢
    apply Subgroup.map_injective (f := (e : G →* G')) e.injective
    rw [Subgroup.map_commutator, hmap]
    exact hperf'
  let ψ : ↥K ≃* ↥K' := (e.subgroupMap K).trans (MulEquiv.subgroupCongr hmap)
  have hU4 : HasU4Quot K := by
    obtain ⟨Y, Ygrp, hY, f, hf⟩ := hU4'
    letI : Group Y := Ygrp
    exact ⟨Y, Ygrp, hY, f.comp (ψ : ↥K →* ↥K'), hf.comp ψ.surjective⟩
  obtain ⟨hsK, hnorm, hgen, hZ⟩ := h s hord K hK hperf hU4
  have hsymm_cent : ∀ g' : G', g' ∈ Subgroup.centralizer ({s'} : Set G') →
      e.symm g' ∈ Subgroup.centralizer ({s} : Set G) := by
    intro g' hg'
    rw [← Subgroup.mem_map_iff_mem (f := (e : G →* G')) e.injective, hCmap]
    simpa using hg'
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro hs'
    apply hsK
    rw [hKdef, Subgroup.mem_comap, hse]
    exact hs'
  · intro g' hg' k' hk'
    have hg : e.symm g' ∈ Subgroup.centralizer ({s} : Set G) := hsymm_cent g' hg'
    have hk : e.symm k' ∈ K := by
      rw [hKdef, Subgroup.mem_comap]
      simpa using hk'
    have hmem := hnorm (e.symm g') hg (e.symm k') hk
    rw [← hmap, Subgroup.mem_map]
    exact ⟨e.symm g' * e.symm k' * (e.symm g')⁻¹, hmem, by simp⟩
  · intro g' hg'
    have hg : e.symm g' ∈ Subgroup.centralizer ({s} : Set G) := hsymm_cent g' hg'
    obtain ⟨n, k, hk, hgk⟩ := hgen (e.symm g') hg
    refine ⟨n, e k, ?_, ?_⟩
    · rw [← hmap]
      exact Subgroup.mem_map_of_mem _ hk
    · have hgk' : g' = e (s ^ n * k) := by
        rw [← hgk, MulEquiv.apply_symm_apply]
      rw [hgk', map_mul, map_pow, hse']
  · have hmapc := Subgroup.map_center_eq (ψ : ↥K ≃* ↥K')
    rw [hZ] at hmapc
    rw [← hmapc, Subgroup.map_bot]

theorem u42E27CentAt_of_hosts (hD : CentShapeOn ↥CFSG.AGLEmbedding.Om8)
    (h5 : CentShapeOn CFSG.LocalAnalysis.GLTheoremA.CatB.U52Layer.M5)
    (h6 : CentShapeOn CFSG.LocalAnalysis.GLTheoremA.LevelLieU6.S6) : U42E27CentAt := by
  intro S _ _ hS s hs K hK hperf hU4
  obtain ⟨i, hi, ⟨e⟩⟩ := hS
  have hshape : CentShapeOn S := by
    rcases hi with h | h | h
    · obtain ⟨e'⟩ := bridge_d4two ⟨i, h, ⟨e⟩⟩
      exact CentShapeOn.of_mulEquiv e'.symm hD
    · obtain ⟨e'⟩ := U52Layer.bridge_u5two_stated ⟨i, h, ⟨e⟩⟩
      exact CentShapeOn.of_mulEquiv e'.symm h5
    · obtain ⟨e'⟩ := HSubT.nonempty_S6_of_isU6two ⟨i, h, ⟨e⟩⟩
      exact CentShapeOn.of_mulEquiv e'.symm h6
  exact hshape s hs K hK hperf hU4

end CFSG.LocalAnalysis.GLTheoremA.CatB.U42Cat

end
