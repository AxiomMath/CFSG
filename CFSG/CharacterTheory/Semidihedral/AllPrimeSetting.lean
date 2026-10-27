module

public import CFSG.LocalAnalysis.ABGTheoremB.Setting
public import CFSG.CharacterTheory.Semidihedral.AllPrimeOrdinaryBridge

public noncomputable section

namespace CFSG.Semidihedral.AllPrime

open CFSG.Open CFSG.Semidihedral CFSG.Semidihedral.ActualSimpleLayerLocalPackage
open CFSG.Semidihedral.EscapingLocalEigensubgroups
open CFSG.ABGTheoremB CFSG.ABGLocalTools CFSG.QuasiDihedralFusion

section Transport

variable {G : Type} [Group G]

theorem oddCoreIn_map_mulEquiv (φ : G ≃* G) (H : Subgroup G) :
    oddCoreIn (H.map φ.toMonoidHom) = (oddCoreIn H).map φ.toMonoidHom := by
  let e : H ≃* H.map φ.toMonoidHom := H.equivMapOfInjective φ.toMonoidHom φ.injective
  have hmap : (H.map φ.toMonoidHom).subtype.comp e.toMonoidHom = φ.toMonoidHom.comp H.subtype := by
    ext x
    rfl
  simp only [oddCoreIn, QuaternionFocalFactorization.oddCore_eq_twoPrimeCore]
  rw [← CFSG.pPrimeCore_map_iso 2 e, Subgroup.map_map, hmap, ← Subgroup.map_map]

theorem isSylowOf_map_mulEquiv [Finite G] {p : ℕ} [Fact p.Prime] (φ : G ≃* G)
    {P K : Subgroup G} (h : IsSylowOf p P K) :
    IsSylowOf p (P.map φ.toMonoidHom) (K.map φ.toMonoidHom) := by
  rw [isSylowOf_iff] at h ⊢
  obtain ⟨hle, hP, hdvd⟩ := h
  refine ⟨Subgroup.map_mono hle, hP.map _, ?_⟩
  rwa [Subgroup.relIndex_map_map, (MonoidHom.ker_eq_bot_iff _).mpr φ.injective, sup_bot_eq,
    sup_bot_eq]

theorem isSylowOf_oddCoreIn_normalizer_of_isSylowOf [Finite G] {p : ℕ} [Fact p.Prime]
    {R R' K : Subgroup G} (hR : IsSylowOf p R K) (hR' : IsSylowOf p R' K)
    (hst : IsSylowOf p R (oddCoreIn (Subgroup.normalizer (R : Set G)))) :
    IsSylowOf p R' (oddCoreIn (Subgroup.normalizer (R' : Set G))) := by
  obtain ⟨Q, rfl⟩ := hR
  obtain ⟨Q', rfl⟩ := hR'
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq K Q Q'
  have hQ' : (Q' : Subgroup K) = (Q : Subgroup K).map (MulAut.conj g).toMonoidHom := by
    rw [← hg, Sylow.coe_subgroup_smul]
    rfl
  have hconj : (Q' : Subgroup K).map K.subtype =
      ((Q : Subgroup K).map K.subtype).map (MulAut.conj (g : G)).toMonoidHom := by
    rw [hQ', Subgroup.map_map, Subgroup.map_map]
    congr 1
  rw [hconj, ← Subgroup.map_equiv_normalizer_eq, oddCoreIn_map_mulEquiv]
  exact isSylowOf_map_mulEquiv _ hst

theorem exists_sylow_of_isSylowOf_map_subtype [Finite G] {p : ℕ} [Fact p.Prime]
    (K : Subgroup G) (B : Subgroup K) {P : Subgroup G} (h : IsSylowOf p P (B.map K.subtype)) :
    ∃ Q : Sylow p B, (Q : Subgroup B).map (K.subtype.comp B.subtype) = P := by
  have hPK : P ≤ K := h.le.trans (Subgroup.map_subtype_le B)
  have hP : (P.subgroupOf K).map K.subtype = P := by
    rw [Subgroup.subgroupOf_map_subtype, inf_of_le_left hPK]
  rw [← hP] at h
  obtain ⟨Q, hQ⟩ := (isSylowOf_map_subtype_iff K).mp h
  exact ⟨Q, by rw [← Subgroup.map_map, hQ, hP]⟩

end Transport

@[expose] def frontierSetting {G : Type} [Group G] {n : ℕ} (S : Sylow 2 G)
    (fS : SemidihedralGroup n ≃* (S : Subgroup G)) (t : G) (p f : ℕ) :
    CFSG.ABGTheoremB.Setting G where
  x := t
  x₂ := (fS (s n) : G)
  S := S
  height := 1
  p := p
  f := f
  L₀ := (localLayerPreimage t).map (C t).subtype

theorem frontierSetting_ON {G : Type} [Group G] {n : ℕ} (S : Sylow 2 G)
    (fS : SemidihedralGroup n ≃* (S : Subgroup G)) (t : G) (p f : ℕ) :
    (frontierSetting S fS t p f).ON = (N t).map (C t).subtype := by
  change (CFSG.oddCore (C t)).map (C t).subtype = _
  rw [QuaternionFocalFactorization.oddCore_eq_twoPrimeCore]

section Layer

variable {G : Type} [Group G]

theorem localLayerPreimage_normal (t : G) : (localLayerPreimage t).Normal := by
  unfold localLayerPreimage
  infer_instance

theorem N_le_localLayerPreimage (t : G) : N t ≤ localLayerPreimage t := by
  intro c hc
  have h1 : nu t c = 1 := by
    rw [← MonoidHom.mem_ker, QuotientGroup.ker_mk']
    exact hc
  change nu t c ∈ (CFSG.generalizedFitting (Gamma t)).comap (barKappa t)
  rw [h1]
  exact Subgroup.one_mem _

@[expose] def layerQuotientHom (t : G) {F : Type} [Field F]
    (eta : (CFSG.generalizedFitting (Gamma t)).comap (barKappa t) ≃*
      Matrix.SpecialLinearGroup (Fin 2) F) :
    (localLayerPreimage t).map (C t).subtype →* Matrix.SpecialLinearGroup (Fin 2) F :=
  eta.toMonoidHom.comp
    (((nu t).comp (Subgroup.inclusion (Subgroup.map_subtype_le (localLayerPreimage t)))).codRestrict
      _ fun x => (Subgroup.mem_map_iff_mem (C t).subtype_injective
        (x := Subgroup.inclusion (Subgroup.map_subtype_le (localLayerPreimage t)) x)).mp
          x.property)

theorem layerQuotientHom_surjective (t : G) {F : Type} [Field F]
    (eta : (CFSG.generalizedFitting (Gamma t)).comap (barKappa t) ≃*
      Matrix.SpecialLinearGroup (Fin 2) F) :
    Function.Surjective (layerQuotientHom t eta) := by
  intro y
  obtain ⟨c, hc⟩ := QuotientGroup.mk'_surjective (N t) (eta.symm y : H t)
  have hcY : c ∈ localLayerPreimage t := by
    change nu t c ∈ (CFSG.generalizedFitting (Gamma t)).comap (barKappa t)
    rw [show nu t c = (eta.symm y : H t) from hc]
    exact (eta.symm y).property
  refine ⟨⟨c, c, hcY, rfl⟩, ?_⟩
  rw [← eta.apply_symm_apply y]
  change eta _ = eta _
  congr 1
  exact Subtype.ext hc

theorem layerQuotientHom_ker (t : G) {F : Type} [Field F]
    (eta : (CFSG.generalizedFitting (Gamma t)).comap (barKappa t) ≃*
      Matrix.SpecialLinearGroup (Fin 2) F) :
    (layerQuotientHom t eta).ker =
      ((N t).map (C t).subtype).subgroupOf ((localLayerPreimage t).map (C t).subtype) := by
  ext x
  rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
  change eta _ = 1 ↔ _
  rw [map_eq_one_iff _ eta.injective, ← Subtype.coe_inj]
  change nu t (Subgroup.inclusion (Subgroup.map_subtype_le (localLayerPreimage t)) x) = 1 ↔ _
  rw [← MonoidHom.mem_ker, QuotientGroup.ker_mk']
  exact (Subgroup.mem_map_iff_mem (C t).subtype_injective).symm

end Layer

theorem frontierSetting_isValid {G : Type} [Group G] [Finite G] [IsSimpleGroup G]
    (hGnonab : ∃ a b : G, a * b ≠ b * a)
    (n : ℕ) (hn : 4 ≤ n) (S : Sylow 2 G) (fS : SemidihedralGroup n ≃* (S : Subgroup G))
    (t : G) (ht : t = (fS (r n) : G) ^ 2 ^ (n - 2))
    [IsSimpleGroup (CFSG.generalizedFitting (Gamma t))]
    (hnonab : ∃ a b : CFSG.generalizedFitting (Gamma t), a * b ≠ b * a)
    (hcentral : Subgroup.centralizer (CFSG.generalizedFitting (Gamma t) : Set (Gamma t)) = ⊥)
    (hnc : ∀ U : Sylow 2 (CFSG.generalizedFitting (Gamma t)), ¬ IsCyclic U)
    (p f : ℕ) (hp : p.Prime) (hpodd : Odd p) (hf : 1 ≤ f) (hq : 5 < p ^ f)
    (hmodel : CFSG.Assembly.LowTwoRank.StatedClassicalModel
      (CFSG.generalizedFitting (Gamma t)) .PSL 2 p f) :
    (frontierSetting S fS t p f).IsValid := by
  obtain ⟨hz, ht2, -, hsC, hs2, hst⟩ := CFSG.Semidihedral.Principal.supplied_t_s_facts hn fS ht
  have hG : ∀ U : Subgroup G, U.index ≠ 2 :=
    CFSG.Semidihedral.Principal.index_ne_two_of_isSimpleGroup hGnonab
  obtain ⟨F, hfield, hfinite, A, rho, data⟩ :=
    actual_simple_layer_matrix_data n hn S fS hG t ht2 hnonab hcentral hnc p f hp hpodd hf hmodel
  obtain ⟨eta, -, -, -⟩ := data.compatible_layer
  have := localLayerPreimage_normal t
  exact
    { simple := inferInstance
      nonabelian := hGnonab
      sylow := Or.inl ⟨rfl, n, hn, fun S' => ⟨fS.trans (Sylow.equiv S S')⟩⟩
      x_order := ht2
      x_mem_center := by
        refine ⟨hz ▸ (fS (z n)).property, Subgroup.mem_centralizer_iff.mpr fun y hy => ?_⟩
        change y * t = t * y
        rw [← hz]
        have h := congrArg (fun w => ((fS w : S) : G))
          (Subgroup.mem_center_iff.mp (z_mem_center n hn) (fS.symm ⟨y, hy⟩))
        simpa only [map_mul, Subgroup.coe_mul, MulEquiv.apply_symm_apply] using h
      center_involution := by
        intro w hw hw2
        obtain ⟨hwS, hwC⟩ := Subgroup.mem_inf.mp hw
        change w ∈ (S : Subgroup G) at hwS
        change w ∈ Subgroup.centralizer ((S : Subgroup G) : Set G) at hwC
        change w = t
        rw [← hz]
        have hc : fS.symm ⟨w, hwS⟩ ∈ Subgroup.center (SemidihedralGroup n) := by
          rw [Subgroup.mem_center_iff]
          intro b
          apply fS.injective
          apply Subtype.ext
          simp only [map_mul, MulEquiv.apply_symm_apply, Subgroup.coe_mul]
          exact Subgroup.mem_centralizer_iff.mp hwC _ (fS b).property
        have ho : orderOf (fS.symm ⟨w, hwS⟩) = 2 := by
          rw [MulEquiv.orderOf_eq, Subgroup.orderOf_mk]
          exact hw2
        rw [← CentralQuotients.original_center_unique_involution n hn _ hc ho,
          MulEquiv.apply_symm_apply]
      x₂_order := hs2
      x₂_mem := (fS (s n)).property
      commute := (Subgroup.mem_centralizer_singleton_iff.mp hsC).symm
      x_ne_x₂ := hst.symm
      T_normal := fun h => absurd rfl h
      p_prime := hp
      p_ne_two := by
        rintro rfl
        exact absurd hpodd (by decide)
      one_le_f := hf
      five_lt_q := hq
      L₀_le_N := Subgroup.map_subtype_le _
      ON_le_L₀ := by
        rw [frontierSetting_ON]
        exact Subgroup.map_mono (N_le_localLayerPreimage t)
      N_le_normalizer_L₀ := CFSG.ABGTheoremB.le_normalizer_map_subtype (C t) (localLayerPreimage t)
      L₀_quotient := by
        have hker := layerQuotientHom_ker t eta
        rw [← frontierSetting_ON S fS t p f] at hker
        exact ⟨F, hfield, hfinite, data.field_card, layerQuotientHom t eta,
          layerQuotientHom_surjective t eta, hker⟩ }

theorem allLocalPrimesOrdinary_of_theoremBStar {G : Type} [Group G] [Finite G]
    {n : ℕ} (_hn : 4 ≤ n) (S : Sylow 2 G) (fS : SemidihedralGroup n ≃* (S : Subgroup G))
    (t : G) (_ht : t = (fS (r n) : G) ^ 2 ^ (n - 2)) (p f : ℕ)
    (h : (frontierSetting S fS t p f).TheoremBStar) :
    allLocalPrimesOrdinary t (fS (s n) : G) := by
  intro ell hell hdvd
  have : Fact ell.Prime := ⟨hell⟩
  have hON := frontierSetting_ON S fS t p f
  have hdvd' : ell ∣ Nat.card (frontierSetting S fS t p f).ON := by
    rw [hON, Subgroup.card_map_of_injective (C t).subtype_injective]
    exact hdvd
  obtain ⟨⟨R, hRON, hRst⟩, hCI⟩ := h ell hell hdvd'
  obtain ⟨R', hR'ON, hTR', hact⟩ : ∃ R' : Subgroup G,
      IsSylowOf ell R' (frontierSetting S fS t p f).ON ∧
      Subgroup.closure ({t, (fS (s n) : G)} : Set G) ≤ Subgroup.normalizer (R' : Set G) ∧
      ((∀ x ∈ R', (fS (s n) : G) * x * (fS (s n) : G)⁻¹ = x) ∨
        (∀ x ∈ R', (fS (s n) : G) * x * (fS (s n) : G)⁻¹ = x⁻¹)) := by
    rcases hCI with ⟨R', h1, h2, h3⟩ | ⟨R', h1, h2, h3⟩
    · refine ⟨R', h1, h2, Or.inl fun x hx => ?_⟩
      have hs : (fS (s n) : G) ∈ Subgroup.centralizer (R' : Set G) :=
        h3 (Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl))
      rw [← Subgroup.mem_centralizer_iff.mp hs x hx, mul_inv_cancel_right]
    · exact ⟨R', h1, h2, Or.inr h3⟩
  have hR'st := isSylowOf_oddCoreIn_normalizer_of_isSylowOf hRON hR'ON hRst
  rw [hON] at hR'ON
  obtain ⟨P, hP⟩ := exists_sylow_of_isSylowOf_map_subtype (C t) (N t) hR'ON
  have hPa : LocalSylowNormalizerFactorization.localSylowAmbient t P = R' := by
    rw [LocalSylowNormalizerFactorization.localSylowAmbient,
      LocalSylowNormalizerFactorization.localSylowInCentralizer, Subgroup.map_map]
    exact hP
  refine ⟨P, ?_⟩
  dsimp only [ordinaryLocalSylow]
  rw [hPa]
  refine ⟨hTR', ?_, hact⟩
  rw [oddCoreIn, QuaternionFocalFactorization.oddCore_eq_twoPrimeCore] at hR'st
  exact exists_sylow_of_isSylowOf_map_subtype _ _ hR'st

end CFSG.Semidihedral.AllPrime
