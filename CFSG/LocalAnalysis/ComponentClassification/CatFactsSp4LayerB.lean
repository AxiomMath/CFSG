module

public import CFSG.LocalAnalysis.ComponentClassification.CatFactsSp4LayerA
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsSp4OutCard

public noncomputable section

namespace CFSG.ComponentClassification.CatFactsSp4

open Matrix CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial
open SymplecticHigher SymplecticFlag Subgroup

variable {K : Type} [Field K]

theorem fixOf_one {G : Type*} [Group G] : fixOf (1 : MulAut G) = ⊤ := by
  ext x
  simp only [mem_fixOf, MulAut.one_apply, mem_top]

theorem exists_noncomm_P [Finite K] (h2 : (2 : K) ≠ 0) (h4 : 4 ≤ Nat.card K) :
    ∃ x y : StatedProj (StatedSp 2 K), x * y ≠ y * x := by
  obtain ⟨x, -, y, -, hxy⟩ := exists_mul_ne_of_isQuasisimple (isQuasisimple_E1 h2 h4)
  exact ⟨x, y, hxy⟩

theorem even_card_P [Finite K] (h2 : (2 : K) ≠ 0) :
    Even (Nat.card (StatedProj (StatedSp 2 K))) := by
  have := orderOf_dvd_natCard (u1 K)
  rw [orderOf_eq_prime (by rw [pow_two]; exact u1_mul_u1) (u1_ne_one h2)] at this
  exact even_iff_two_dvd.mpr this

theorem even_card_of_mem {G : Type*} [Group G] [Finite G] {E : Subgroup G} {x : G}
    (hx : x ∈ E) (hxo : orderOf x = 2) : Even (Nat.card E) := by
  have := orderOf_dvd_natCard (⟨x, hx⟩ : E)
  rw [Subgroup.orderOf_mk, hxo] at this
  exact even_iff_two_dvd.mpr this

theorem layerOf_top [Finite K] (h2 : (2 : K) ≠ 0) (h4 : 4 ≤ Nat.card K)
    (hs : IsSimpleGroup (StatedProj (StatedSp 2 K))) :
    layerOf (⊤ : Subgroup (StatedProj (StatedSp 2 K))) = ⊤ := by
  obtain ⟨hq, -⟩ := LocalCores.isQuasisimple_of_isSimpleGroup (exists_noncomm_P h2 h4)
  have hq' : CFSG.IsQuasisimple (⊤ : Subgroup (StatedProj (StatedSp 2 K))) :=
    (isQuasisimple_congr Subgroup.topEquiv).mpr hq
  have he : Even (Nat.card (⊤ : Subgroup (StatedProj (StatedSp 2 K)))) := by
    rw [Subgroup.card_top]
    exact even_card_P h2
  refine layerOf_eq_of_unique le_rfl (isPComponent_two_of_quasisimple' le_rfl hq'
    (by rw [subgroupOf_self]; exact IsSubnormal.top) he) fun M hMX hM => ?_
  have hne := ne_bot_of_isPComponent hM
  have hsub : (M.subgroupOf ⊤).IsSubnormal := hM.choose_spec.2.1
  have : IsSimpleGroup (⊤ : Subgroup (StatedProj (StatedSp 2 K))) :=
    Subgroup.topEquiv.symm.isSimpleGroup_congr.mp hs
  rcases hsub.eq_bot_or_top_of_isSimpleGroup this with hb | ht
  · exfalso
    apply hne
    rw [eq_bot_iff]
    intro m hm
    have : (⟨m, mem_top m⟩ : (⊤ : Subgroup (StatedProj (StatedSp 2 K)))) ∈ M.subgroupOf ⊤ := hm
    rw [hb] at this
    exact congrArg Subtype.val this
  · rw [eq_top_iff]
    intro m _
    have : (⟨m, mem_top m⟩ : (⊤ : Subgroup (StatedProj (StatedSp 2 K)))) ∈ M.subgroupOf ⊤ :=
      ht ▸ mem_top _
    exact this

theorem isPComponent_E1 [Finite K] (h2 : (2 : K) ≠ 0) (h4 : 4 ≤ Nat.card K) :
    CFSG.IsPComponent 2 ((E1 K).subgroupOf (centralizer {u1 K})) :=
  isPComponent_two_of_quasisimple' (E1_le_centralizer_u1 h2) (isQuasisimple_E1 h2 h4)
    (isComponent_E1 h2 h4).2 (even_card_of_mem u1_mem_E1
      (orderOf_eq_prime (by rw [pow_two]; exact u1_mul_u1) (u1_ne_one h2)))

theorem E2_le_centralizer_u1 (h2 : (2 : K) ≠ 0) : E2 K ≤ centralizer {u1 K} :=
  (E2_le_X0 h2).trans X0_le_centralizer

theorem isComponent_E2 [Finite K] (h2 : (2 : K) ≠ 0) (h4 : 4 ≤ Nat.card K) :
    IsComponent ((E2 K).subgroupOf (centralizer {u1 K})) := by
  have hE := E2_le_centralizer_u1 h2
  have hX : X0 K ≤ centralizer {u1 K} := X0_le_centralizer
  refine ⟨(isQuasisimple_congr (subgroupOfEquivOfLe hE)).mpr (isQuasisimple_E2 h2 h4), ?_⟩
  have hXn : ((X0 K).subgroupOf (centralizer {u1 K})).Normal := by
    rw [normal_subgroupOf_iff hX]
    intro x c hx hc
    exact conj_mem_map_centralizer (T1 K) hc hx
  have hEX : (E2 K).subgroupOf (centralizer {u1 K}) ≤ (X0 K).subgroupOf (centralizer {u1 K}) :=
    fun x hx => E2_le_X0 h2 hx
  refine IsSubnormal.trans hEX ?_ hXn.isSubnormal
  apply Normal.isSubnormal
  rw [normal_subgroupOf_iff hEX]
  intro x c hx hc
  exact conj_mem_E2 h2 hc hx

theorem isPComponent_E2 [Finite K] (h2 : (2 : K) ≠ 0) (h4 : 4 ≤ Nat.card K) :
    CFSG.IsPComponent 2 ((E2 K).subgroupOf (centralizer {u1 K})) :=
  isPComponent_two_of_quasisimple' (E2_le_centralizer_u1 h2) (isQuasisimple_E2 h2 h4)
    (isComponent_E2 h2 h4).2 (even_card_of_mem u1_mem_E2
      (orderOf_eq_prime (by rw [pow_two]; exact u1_mul_u1) (u1_ne_one h2)))

theorem layerOf_u1 [Finite K] (hodd : Odd (Nat.card K)) (h4 : 4 ≤ Nat.card K) :
    layerOf (centralizer {u1 K}) = E1 K ⊔ E2 K := by
  have h2 := two_ne_zero_of_odd_card hodd
  apply le_antisymm
  · refine sSup_le fun M ⟨hMX, hM⟩ => ?_
    rcases (pComponent_centralizer_u1 hodd hMX hM).1 with h | h <;> rw [h]
    · exact le_sup_left
    · exact le_sup_right
  · exact sup_le (le_layerOf (E1_le_centralizer_u1 h2) (isPComponent_E1 h2 h4))
      (le_layerOf (E2_le_centralizer_u1 h2) (isPComponent_E2 h2 h4))

theorem detE_diagSL (g : Matrix.SpecialLinearGroup (Fin 2) K) :
    detE ⟨diagSL K g, diagSL_mem_centralizer g⟩ = 1 := by
  have hb : blocksE ⟨diagSL K g, diagSL_mem_centralizer g⟩ =
      (g : Matrix (Fin 2) (Fin 2) K).map (algebraMap K (Gauss K)) := by
    apply gaussBlock_injective
    rw [gaussBlock_blocksE, gaussBlock_map]
    exact coe_diagSL g
  change (blocksE ⟨diagSL K g, diagSL_mem_centralizer g⟩).det = 1
  rw [hb, ← RingHom.mapMatrix_apply, ← RingHom.map_det, g.2, map_one]

theorem diagSL_range_normal (h2 : (2 : K) ≠ 0) :
    ((diagSL K).range.subgroupOf (centralizer {T2 K})).Normal := by
  have hker : (detE (K := K)).toHomUnits.ker =
      (diagSL K).range.subgroupOf (centralizer {T2 K}) := by
    ext x
    rw [MonoidHom.mem_ker, mem_subgroupOf]
    constructor
    · intro h
      exact mem_range_diagSL_of_detE h2 x (congrArg Units.val h)
    · rintro ⟨k, hk⟩
      apply Units.ext
      change detE x = 1
      have : x = ⟨diagSL K k, diagSL_mem_centralizer k⟩ := Subtype.ext hk.symm
      rw [this, detE_diagSL]
  rw [← hker]
  infer_instance

theorem J₁SL_not_mem_center :
    (J₁SL : Matrix.SpecialLinearGroup (Fin 2) K) ∉
      center (Matrix.SpecialLinearGroup (Fin 2) K) := by
  intro h
  obtain ⟨r, -, hr⟩ := (Matrix.SpecialLinearGroup.mem_center_iff).mp h
  have := congrFun (congrFun hr 0) 1
  simp [J₁SL, J₁] at this

theorem isQuasisimple_range_comp [Finite K] (h4 : 4 ≤ Nat.card K)
    (f : Matrix.SpecialLinearGroup (Fin 2) K →* StatedSp 2 K)
    (hker : ((proj 2 K).comp f).ker = center (Matrix.SpecialLinearGroup (Fin 2) K)) :
    CFSG.IsQuasisimple ((proj 2 K).comp f).range :=
  LocalCores.isQuasisimple_of_surjective (isQuasisimple_SL2' h4) ((proj 2 K).comp f).rangeRestrict
    ((proj 2 K).comp f).rangeRestrict_surjective (by rw [MonoidHom.ker_rangeRestrict, hker])

theorem orderOf_proj_J₁SL (f : Matrix.SpecialLinearGroup (Fin 2) K →* StatedSp 2 K)
    (hker : ((proj 2 K).comp f).ker = center (Matrix.SpecialLinearGroup (Fin 2) K)) :
    orderOf (proj 2 K (f J₁SL)) = 2 := by
  have hJJ : (J₁SL : Matrix.SpecialLinearGroup (Fin 2) K) * J₁SL ∈
      center (Matrix.SpecialLinearGroup (Fin 2) K) := by
    rw [Matrix.SpecialLinearGroup.mem_center_iff]
    refine ⟨-1, by simp [Fintype.card_fin], ?_⟩
    rw [Matrix.SpecialLinearGroup.coe_mul]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [J₁SL, J₁, Matrix.mul_apply, Fin.sum_univ_two]
  apply orderOf_eq_prime
  · rw [pow_two, ← map_mul, ← map_mul]
    rw [← hker] at hJJ
    exact hJJ
  · intro h
    apply J₁SL_not_mem_center (K := K)
    rw [← hker]
    exact h

theorem fixOf_conj_T2 : fixOf (MulAut.conj (T2 K)) = centralizer {T2 K} := fixOf_conj (T2 K)

theorem conj_u2_proj (g : StatedSp 2 K) :
    MulAut.conj (u2 K) (proj 2 K g) = proj 2 K (MulAut.conj (T2 K) g) := by
  rw [MulAut.conj_apply, MulAut.conj_apply, u2, map_mul, map_mul, map_inv]

theorem isPComponent_Lsub [Finite K] (h2 : (2 : K) ≠ 0) (h4 : 4 ≤ Nat.card K) :
    CFSG.IsPComponent 2 ((Lsub K).subgroupOf (centralizer {u2 K})) := by
  have hL : Lsub K = ((proj 2 K).comp (diagSL K)).range := by
    rw [Lsub, MonoidHom.range_comp]
  have hq : CFSG.IsQuasisimple (Lsub K) := by
    rw [hL]
    exact isQuasisimple_range_comp h4 (diagSL K) (ker_proj_comp_diagSL (K := K))
  have hsub : ((Lsub K).subgroupOf (centralizer {u2 K})).IsSubnormal := by
    have h := map_isSubnormal_fixOf (MulAut.conj (T2 K)) (α := MulAut.conj (u2 K))
      conj_u2_proj (M := (diagSL K).range)
      (by rw [fixOf_conj_T2]; rintro _ ⟨g, rfl⟩; exact diagSL_mem_centralizer g)
      (by
        have := diagSL_range_normal h2
        rw [← fixOf_conj_T2] at this
        exact this)
    rw [fixOf_conj] at h
    exact h
  exact isPComponent_two_of_quasisimple' Lsub_le_centralizer hq hsub
    (even_card_of_mem w0_mem_Lsub orderOf_w0)

theorem layerOf_u2 [Finite K] (hodd : Odd (Nat.card K)) (h4 : 4 ≤ Nat.card K) :
    layerOf (centralizer {u2 K}) = Lsub K := by
  have h2 := two_ne_zero_of_odd_card hodd
  exact layerOf_eq_of_unique Lsub_le_centralizer (isPComponent_Lsub h2 h4)
    fun M hMX hM => (pComponent_centralizer_u2 hodd hMX hM).1

variable {a : K}

theorem gI_range_normal (ha : a ≠ 0) (h2 : (2 : K) ≠ 0) :
    ((gI ha).range.subgroupOf (fixI a ha)).Normal := by
  have hker : (detI ha).toHomUnits.ker = ((gI ha).range).subgroupOf (fixI a ha) := by
    ext g
    rw [MonoidHom.mem_ker, mem_subgroupOf]
    constructor
    · intro h
      exact mem_range_gI_of_detI ha h2 g (congrArg Units.val h)
    · rintro ⟨k, hk⟩
      apply Units.ext
      change detI ha g = 1
      have : g = ⟨gI ha k, gI_mem_fixI ha k⟩ := Subtype.ext hk.symm
      rw [this, detI_gI]
  rw [← hker]
  infer_instance

theorem isPComponent_JI [Finite K] (ha : a ≠ 0) (h2 : (2 : K) ≠ 0) (h4 : 4 ≤ Nat.card K) :
    CFSG.IsPComponent 2 ((JI ha).subgroupOf (fixAlphaI ha)) := by
  have hJ : JI ha = ((proj 2 K).comp (gI ha)).range := by
    rw [JI, MonoidHom.range_comp]
  have hq : CFSG.IsQuasisimple (JI ha) := by
    rw [hJ]
    exact isQuasisimple_range_comp h4 (gI ha) (ker_proj_comp_gI ha)
  have hθα : ∀ g, alphaI ha (proj 2 K g) = proj 2 K (conjSp 2 K (aIgsp ha) g) := fun g => by
    rw [alphaI, conjAut_proj]
  have hsub := map_isSubnormal_fixOf (conjSp 2 K (aIgsp ha)) hθα (M := (gI ha).range)
    (by rintro _ ⟨k, rfl⟩; exact gI_mem_fixI ha k) (gI_range_normal ha h2)
  have hJmem : proj 2 K (gI ha J₁SL) ∈ JI ha := ⟨_, ⟨J₁SL, rfl⟩, rfl⟩
  exact isPComponent_two_of_quasisimple' (JI_le_fix ha) hq hsub
    (even_card_of_mem hJmem (orderOf_proj_J₁SL (gI ha) (ker_proj_comp_gI ha)))

theorem layerOf_alphaI [Finite K] (ha : a ≠ 0) (h2 : (2 : K) ≠ 0) (h4 : 4 ≤ Nat.card K) :
    layerOf (fixAlphaI ha) = JI ha :=
  layerOf_eq_of_unique (JI_le_fix ha) (isPComponent_JI ha h2 h4)
    fun _M hMX hM => pComponent_fix_alphaI ha h2 h4 hMX hM

end CFSG.ComponentClassification.CatFactsSp4
