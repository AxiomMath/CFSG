module

public import CFSG.LocalAnalysis.GLTheoremB.GammaBasic
public import CFSG.SignalizerFunctorTheorem.Inheritance.TransportA.Fitting

public section

namespace CFSG.LocalAnalysis.GLTheoremB

open CFSG.Open

variable {G : Type*} [Group G]

theorem glaPPrimeCore_map_iso {X Y : Type*} [Group X] [Group Y] (p : ℕ) (e : X ≃* Y) :
    (GLAPPrimeCore p X).map e.toMonoidHom = GLAPPrimeCore p Y :=
  CFSG.pPrimeCore_map_iso p e

theorem glaPPrimeCoreOf_gLBConj (p : ℕ) (g : G) (K : Subgroup G) :
    GLAPPrimeCoreOf p (GLBConj g K) = GLBConj g (GLAPPrimeCoreOf p K) := by
  have hp := glaPPrimeCore_map_iso p (conjEquiv g K)
  have hf : (GLBConj g K).subtype.comp (conjEquiv g K).toMonoidHom =
      (MulAut.conj g⁻¹).toMonoidHom.comp K.subtype := by
    ext t
    simp
  calc GLAPPrimeCoreOf p (GLBConj g K)
      = ((GLAPPrimeCore p ↥K).map (conjEquiv g K).toMonoidHom).map (GLBConj g K).subtype := by
        rw [hp]; rfl
    _ = (GLAPPrimeCore p ↥K).map ((GLBConj g K).subtype.comp (conjEquiv g K).toMonoidHom) :=
        Subgroup.map_map _ _ _
    _ = (GLAPPrimeCore p ↥K).map ((MulAut.conj g⁻¹).toMonoidHom.comp K.subtype) := by rw [hf]
    _ = ((GLAPPrimeCore p ↥K).map K.subtype).map (MulAut.conj g⁻¹).toMonoidHom :=
        (Subgroup.map_map _ _ _).symm
    _ = GLBConj g (GLAPPrimeCoreOf p K) := rfl

theorem IsOmegaTwo.of_mulEquiv {ε : Bool} {n : ℕ} {X Y : Type*} [Group X] [Group Y] (e : X ≃* Y)
    (h : IsOmegaTwo ε n X) : IsOmegaTwo ε n Y := by
  cases ε
  · obtain ⟨f⟩ := h
    exact ⟨e.symm.trans f⟩
  · obtain ⟨f⟩ := h
    exact ⟨e.symm.trans f⟩

theorem IsPiGroup.of_mulEquiv {p : ℕ} {L L' : Type*} [Group L] [Group L'] (e : L ≃* L')
    (h : IsPiGroup p L) : IsPiGroup p L' := by
  obtain ⟨hq, hO, hcase⟩ := h
  have hc : (Subgroup.center L).map e.toMonoidHom = Subgroup.center L' := Subgroup.map_center_eq e
  let ec : (L ⧸ Subgroup.center L) ≃* (L' ⧸ Subgroup.center L') := QuotientGroup.congr _ _ e hc
  refine ⟨CFSG.SignalizerFunctorTheorem.TransportA.isQuasisimple_of_mulEquiv e hq, ?_, ?_⟩
  · rw [← glaPPrimeCore_map_iso p e, hO, Subgroup.map_bot]
  · rcases hcase with ⟨k, ⟨f⟩⟩ | ⟨n, ε, hn, hΩ, hfp⟩ | ⟨hp, ⟨f⟩⟩
    · exact Or.inl ⟨k, ⟨ec.symm.trans f⟩⟩
    · exact Or.inr (Or.inl ⟨n, ε, hn, hΩ.of_mulEquiv ec, hfp⟩)
    · exact Or.inr (Or.inr ⟨hp, ⟨ec.symm.trans f⟩⟩)

theorem isSubnormal_gLBConj {L K : Subgroup G} (h : IsSubnormal L K) (g : G) :
    IsSubnormal (GLBConj g L) (GLBConj g K) :=
  CFSG.SignalizerFunctorTheorem.TransportA.isSubnormal_map (MulAut.conj g⁻¹) h

@[expose] def conjQuotEquiv (p : ℕ) (g : G) (X : Subgroup G) :
    (↥X ⧸ GLAPPrimeCore p ↥X) ≃* (↥(GLBConj g X) ⧸ GLAPPrimeCore p ↥(GLBConj g X)) :=
  QuotientGroup.congr _ _ (conjEquiv g X) (glaPPrimeCore_map_iso p (conjEquiv g X))

abbrev conjQuotHom (p : ℕ) (g : G) (X : Subgroup G) :
    (↥X ⧸ GLAPPrimeCore p ↥X) →* (↥(GLBConj g X) ⧸ GLAPPrimeCore p ↥(GLBConj g X)) :=
  (conjQuotEquiv p g X : _ →* _)

@[expose] def barX (p : ℕ) (X K : Subgroup G) : Subgroup (↥X ⧸ GLAPPrimeCore p ↥X) :=
  (K.subgroupOf X).map (QuotientGroup.mk' (GLAPPrimeCore p ↥X))

theorem map_barX (p : ℕ) (g : G) (X K : Subgroup G) :
    (barX p X K).map (conjQuotHom p g X) = barX p (GLBConj g X) (GLBConj g K) := by
  ext z
  simp only [barX, Subgroup.mem_map]
  constructor
  · rintro ⟨_, ⟨x, hx, rfl⟩, rfl⟩
    refine ⟨conjEquiv g X x, ?_, ?_⟩
    · rw [Subgroup.mem_subgroupOf] at hx ⊢
      rw [coe_conjEquiv, mem_gLBConj]
      simpa [mul_assoc] using hx
    · exact (QuotientGroup.congr_mk _ _ (conjEquiv g X)
        (glaPPrimeCore_map_iso p (conjEquiv g X)) x).symm
  · rintro ⟨y, hy, rfl⟩
    refine ⟨QuotientGroup.mk' _ ((conjEquiv g X).symm y), ⟨(conjEquiv g X).symm y, ?_, rfl⟩, ?_⟩
    · rw [Subgroup.mem_subgroupOf] at hy ⊢
      rw [coe_conjEquiv_symm]
      exact mem_gLBConj.1 hy
    · exact (QuotientGroup.congr_mk _ _ (conjEquiv g X)
        (glaPPrimeCore_map_iso p (conjEquiv g X)) ((conjEquiv g X).symm y)).trans (by simp)

theorem glaPComponent_gLBConj {p : ℕ} {X L : Subgroup G} (h : GLAPComponent p X L) (g : G) :
    GLAPComponent p (GLBConj g X) (GLBConj g L) := by
  obtain ⟨hLX, hsn, hcomp, hmin⟩ := h
  refine ⟨gLBConj_mono g hLX, isSubnormal_gLBConj hsn g, ?_, ?_⟩
  · have := CFSG.SignalizerFunctorTheorem.TransportA.isComponentOf_map
      (conjQuotEquiv p g X) hcomp
    have htop : (⊤ : Subgroup (↥X ⧸ GLAPPrimeCore p ↥X)).map (conjQuotHom p g X) = ⊤ :=
      Subgroup.map_top_of_surjective (conjQuotHom p g X) (conjQuotEquiv p g X).surjective
    rw [htop] at this
    have h2 := map_barX p g X L
    simp only [barX] at h2 this ⊢
    rw [← h2]
    exact this
  · intro J hJ hJsn heq
    have hJ' : GLBConj g⁻¹ J < L := by
      refine lt_of_le_of_ne ?_ fun h => hJ.ne ?_
      · have := gLBConj_mono g⁻¹ hJ.le
        rwa [gLBConj_inv_gLBConj] at this
      · rw [← gLBConj_gLBConj_inv g J, h]
    have hsn' : IsSubnormal (GLBConj g⁻¹ J) X := by
      have := isSubnormal_gLBConj hJsn g⁻¹
      rwa [gLBConj_inv_gLBConj] at this
    refine hmin _ hJ' hsn' ?_
    have h1 := map_barX p g X (GLBConj g⁻¹ J)
    have h2 := map_barX p g X L
    rw [gLBConj_gLBConj_inv] at h1
    have h3 : (barX p X (GLBConj g⁻¹ J)).map (conjQuotHom p g X) =
        (barX p X L).map (conjQuotHom p g X) := by
      rw [h1, h2]
      exact heq
    exact Subgroup.map_injective (conjQuotEquiv p g X).injective h3

theorem gLBConj_eq_of_forall_ge {F : Subgroup G → Subgroup G}
    (h : ∀ (g : G) (H : Subgroup G), GLBConj g (F H) ≤ F (GLBConj g H)) (g : G)
    (H : Subgroup G) : F (GLBConj g H) = GLBConj g (F H) := by
  refine le_antisymm ?_ (h g H)
  have h1 := h g⁻¹ (GLBConj g H)
  rw [gLBConj_inv_gLBConj] at h1
  have h2 := gLBConj_mono g h1
  rwa [gLBConj_gLBConj_inv] at h2

theorem piPred_gLBConj {p : ℕ} {H L : Subgroup G}
    (h : GLAPComponent p H L ∧ IsPiGroup p (↥L ⧸ GLAPPrimeCore p ↥L)) (g : G) :
    GLAPComponent p (GLBConj g H) (GLBConj g L) ∧
      IsPiGroup p (↥(GLBConj g L) ⧸ GLAPPrimeCore p ↥(GLBConj g L)) := by
  exact ⟨glaPComponent_gLBConj h.1 g, h.2.of_mulEquiv (conjQuotEquiv p g L)⟩

theorem piLayer_gLBConj (p : ℕ) (g : G) (H : Subgroup G) :
    piLayer p (GLBConj g H) = GLBConj g (piLayer p H) := by
  refine gLBConj_eq_of_forall_ge (F := piLayer p) (fun g H => ?_) g H
  unfold GLBConj
  rw [Subgroup.map_le_iff_le_comap]
  refine iSup_le fun L => iSup_le fun hL => ?_
  rw [← Subgroup.map_le_iff_le_comap]
  exact le_iSup_of_le (GLBConj g L) (le_iSup_of_le (piPred_gLBConj hL g) le_rfl)

theorem piOf_gLBConj (p : ℕ) (g d : G) : piOf p (g⁻¹ * d * g) = GLBConj g (piOf p d) := by
  rw [piOf, piOf, centralizer_singleton_gLBConj, piLayer_gLBConj]

theorem piStar_gLBConj (p : ℕ) (g : G) (D : Subgroup G) :
    piStar p (GLBConj g D) = GLBConj g (piStar p D) := by
  refine gLBConj_eq_of_forall_le (F := piStar p) (fun g D => ?_) g D
  refine iSup_le fun d => iSup_le fun hd => iSup_le fun hd1 => ?_
  have hd' : g * d * g⁻¹ ∈ D := mem_gLBConj.1 hd
  have hd'1 : g * d * g⁻¹ ≠ 1 := fun h => hd1 (by simpa [mul_assoc] using congrArg (g⁻¹ * · * g) h)
  have hle : piOf p (g * d * g⁻¹) ⊔
      GLAPPrimeCoreOf p (Subgroup.centralizer ({g * d * g⁻¹} : Set G)) ≤ piStar p D :=
    le_iSup_of_le (g * d * g⁻¹) (le_iSup_of_le hd' (le_iSup_of_le hd'1 le_rfl))
  have hc := centralizer_singleton_gLBConj g (g * d * g⁻¹)
  rw [show g⁻¹ * (g * d * g⁻¹) * g = d by group] at hc
  have hpi := piOf_gLBConj p g (g * d * g⁻¹)
  rw [show g⁻¹ * (g * d * g⁻¹) * g = d by group] at hpi
  rw [hpi, hc, glaPPrimeCoreOf_gLBConj]
  have := gLBConj_mono g hle
  rwa [GLBConj, Subgroup.map_sup] at this

theorem gammaStar_gLBConj (p : ℕ) (g : G) (D : Subgroup G) :
    gammaStar p (GLBConj g D) = GLBConj g (gammaStar p D) := by
  rw [gammaStar, gammaStar, gammaD_gLBConj, piStar_gLBConj, pCoreOf_gLBConj]
  ext y
  simp only [mem_gLBConj, Subgroup.mem_inf]

theorem normalizer_le_normalizer_gammaStar (p : ℕ) (D : Subgroup G) :
    Subgroup.normalizer (D : Set G) ≤ Subgroup.normalizer (gammaStar p D : Set G) := by
  intro n hn
  rw [mem_normalizer_iff_gLBConj_eq] at hn ⊢
  rw [← gammaStar_gLBConj, hn]

theorem gammaStar_le_gammaD (p : ℕ) (D : Subgroup G) : gammaStar p D ≤ gammaD D :=
  inf_le_left

theorem isPGroup_gammaStar [Finite G] (p : ℕ) (D : Subgroup G) : IsPGroup 2 (gammaStar p D) :=
  (isPGroup_gammaD D).to_le (gammaStar_le_gammaD p D)

end CFSG.LocalAnalysis.GLTheoremB
