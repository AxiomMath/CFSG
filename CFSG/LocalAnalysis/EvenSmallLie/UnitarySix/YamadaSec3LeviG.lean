module

public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.YamadaSec3K2
public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.YamadaSec3Fields
public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.YamadaSec3K1

public noncomputable section

namespace CFSG.EvenSmallLie.UnitarySix.YamadaSec3

open Matrix CFSG.Fischer CFSG.ClassicalInvolution.WeakCT Subgroup
open CFSG.EvenSmallLie.UnitarySix.YamadaEnd (conjR mem_conjR msigma sY pstd)
open scoped MatrixGroups

variable {G : Type} [Group G] {L : Subgroup G}
  {e : L ≃* T46}

theorem range_phiG_comp {H : Type*} [Group H] (f : H →* SUJ) :
    ((phiG e).comp f).range = toG e ((psi0.comp f).range) := by
  ext x
  rw [mem_toG]
  constructor
  · rintro ⟨h, rfl⟩
    refine ⟨psiT (f h), ?_, ?_⟩
    · rw [coe_psiT]
      exact ⟨h, rfl⟩
    · rw [MonoidHom.comp_apply, phiG_apply]
  · rintro ⟨g, ⟨h, hh⟩, rfl⟩
    refine ⟨h, ?_⟩
    rw [MonoidHom.comp_apply, phiG_apply]
    exact congrArg (iotaG e) (Subtype.ext (by rw [coe_psiT]; exact hh))

theorem map_phiG_comp {H : Type*} [Group H] (f : H →* SUJ) (K : Subgroup H) :
    K.map ((phiG e).comp f) = toG e (K.map (psi0.comp f)) := by
  ext x
  rw [mem_toG]
  constructor
  · rintro ⟨h, hK, rfl⟩
    refine ⟨psiT (f h), ?_, ?_⟩
    · rw [coe_psiT]
      exact ⟨h, hK, rfl⟩
    · rw [MonoidHom.comp_apply, phiG_apply]
  · rintro ⟨g, ⟨h, hK, hh⟩, rfl⟩
    refine ⟨h, hK, ?_⟩
    rw [MonoidHom.comp_apply, phiG_apply]
    exact congrArg (iotaG e) (Subtype.ext (by rw [coe_psiT]; exact hh))

theorem ker_phiG_comp {H : Type*} [Group H] (f : H →* SUJ) :
    ((phiG e).comp f).ker = (psi0.comp f).ker := by
  ext h
  rw [MonoidHom.mem_ker, MonoidHom.mem_ker, MonoidHom.comp_apply, phiG_apply,
    MonoidHom.comp_apply]
  constructor
  · intro h1
    have := iotaG_injective (h1.trans (map_one (iotaG e)).symm)
    rw [← coe_psiT, this]
    rfl
  · intro h1
    rw [show psiT (f h) = 1 from Subtype.ext (by rw [coe_psiT]; exact h1), map_one]

theorem injective_phiG_comp {H : Type*} [Group H] {f : H →* SUJ}
    (hf : Function.Injective (psi0.comp f)) : Function.Injective ((phiG e).comp f) := by
  intro a b hab
  apply hf
  have := congrArg Subtype.val (iotaG_injective hab)
  rwa [coe_psiT, coe_psiT] at this

theorem wP_inv_of_sq {k : ℕ} (hk : k < 18) (h : yamGen k * yamGen k = 1) :
    (wP [k])⁻¹ = wP [k] := by
  rw [wP_single, ← psi0_yamGen hk, inv_eq_iff_mul_eq_one, ← map_mul, h, map_one]

theorem conjR_wP_mem {X : Subgroup (Equiv.Perm (Fin 693))} {a b : ℕ} (ha : a < 18)
    (h : yamGen a * yamGen a = 1) (hb : wP [b] ∈ X) : wP [a, b, a] ∈ conjR X (wP [a]) := by
  have := YamadaEnd.conj_mem_conjR (g := wP [a]) hb
  rw [wP_inv_of_sq ha h] at this
  rw [wP_conj]
  exact this

theorem conjR_grp_le {c c' : ChainData} {a : ℕ} (ha : a < 18) (h : yamGen a * yamGen a = 1)
    (hc : ∀ w ∈ c.gens, ∃ b, w = [b] ∧ wP [a, b, a] ∈ c'.grp) :
    conjR c.grp (wP [a]) ≤ c'.grp := by
  rw [conjR, ChainData.grp, MonoidHom.map_closure, Subgroup.closure_le]
  rintro _ ⟨G, ⟨w, hw, rfl⟩, rfl⟩
  obtain ⟨b, rfl, hb⟩ := hc w hw
  simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
  rw [wP_inv_of_sq ha h, ← wP_conj]
  exact hb

theorem chB12_eq : chB12.grp = chX1.grp ⊔ conjR chX1.grp (wP [15]) := by
  apply le_antisymm
  · refine grp_le fun w hw => ?_
    simp only [chB12, List.mem_cons, List.not_mem_nil, or_false] at hw
    rcases hw with rfl | rfl | rfl | rfl
    · exact mem_sup_left (wP_mem_grp (by simp [chX1]))
    · exact mem_sup_left (wP_mem_grp (by simp [chX1]))
    · exact mem_sup_right (conjR_wP_mem (by norm_num) w₁_sq (wP_mem_grp (by simp [chX1])))
    · exact mem_sup_right (conjR_wP_mem (by norm_num) w₁_sq (wP_mem_grp (by simp [chX1])))
  · refine sup_le (grp_le fun w hw => wP_mem_grp ?_) (conjR_grp_le (by norm_num) w₁_sq ?_)
    · simp only [chX1, List.mem_cons, List.not_mem_nil, or_false] at hw
      rcases hw with rfl | rfl <;> simp [chB12]
    · intro w hw
      simp only [chX1, List.mem_cons, List.not_mem_nil, or_false] at hw
      rcases hw with rfl | rfl
      · exact ⟨0, rfl, wP_mem_grp (by simp [chB12])⟩
      · exact ⟨1, rfl, wP_mem_grp (by simp [chB12])⟩

theorem chB23_eq : chB23.grp = chX2.grp ⊔ conjR chX2.grp (wP [16]) := by
  apply le_antisymm
  · refine grp_le fun w hw => ?_
    simp only [chB23, List.mem_cons, List.not_mem_nil, or_false] at hw
    rcases hw with rfl | rfl | rfl | rfl
    · exact mem_sup_left (wP_mem_grp (by simp [chX2]))
    · exact mem_sup_left (wP_mem_grp (by simp [chX2]))
    · exact mem_sup_right (conjR_wP_mem (by norm_num) w₂_sq (wP_mem_grp (by simp [chX2])))
    · exact mem_sup_right (conjR_wP_mem (by norm_num) w₂_sq (wP_mem_grp (by simp [chX2])))
  · refine sup_le (grp_le fun w hw => wP_mem_grp ?_) (conjR_grp_le (by norm_num) w₂_sq ?_)
    · simp only [chX2, List.mem_cons, List.not_mem_nil, or_false] at hw
      rcases hw with rfl | rfl <;> simp [chB23]
    · intro w hw
      simp only [chX2, List.mem_cons, List.not_mem_nil, or_false] at hw
      rcases hw with rfl | rfl
      · exact ⟨2, rfl, wP_mem_grp (by simp [chB23])⟩
      · exact ⟨3, rfl, wP_mem_grp (by simp [chB23])⟩

variable (e) in
@[expose] noncomputable def thetaG : SL(3, F4) →* G := (phiG e).comp theta0

theorem range_thetaG : (thetaG e).range = sK₂ e := by
  rw [thetaG, range_phiG_comp]
  exact congrArg (toG e) range_psiTheta

theorem ker_thetaG : (thetaG e).ker = Subgroup.center SL(3, F4) := by
  rw [thetaG, ker_phiG_comp]
  exact ker_psiTheta

theorem sX₁_sup_conj : sX₁ e ⊔ conjR (sX₁ e) (sw e 0) = toG e chB12.grp := by
  rw [chB12_eq, toG_sup (grp_le_T46 gensOK_chX1), sw0, sX₁, conjR_toG]
  · rfl
  · exact fun x hx => by
      have := conjR_grp_le (c := chX1) (c' := chB12) (by norm_num) w₁_sq (by
        intro w hw
        simp only [chX1, List.mem_cons, List.not_mem_nil, or_false] at hw
        rcases hw with rfl | rfl
        · exact ⟨0, rfl, wP_mem_grp (by simp [chB12])⟩
        · exact ⟨1, rfl, wP_mem_grp (by simp [chB12])⟩) hx
      exact grp_le_T46 gensOK_chB12 this

theorem sX₂_sup_conj : sX₂ e ⊔ conjR (sX₂ e) (sw e 1) = toG e chB23.grp := by
  rw [chB23_eq, toG_sup (grp_le_T46 gensOK_chX2), sw1, sX₂, conjR_toG]
  · rfl
  · exact fun x hx => by
      have := conjR_grp_le (c := chX2) (c' := chB23) (by norm_num) w₂_sq (by
        intro w hw
        simp only [chX2, List.mem_cons, List.not_mem_nil, or_false] at hw
        rcases hw with rfl | rfl
        · exact ⟨2, rfl, wP_mem_grp (by simp [chB23])⟩
        · exact ⟨3, rfl, wP_mem_grp (by simp [chB23])⟩) hx
      exact grp_le_T46 gensOK_chB23 this

theorem map_B12_thetaG : (B12 F4).map (thetaG e) = sX₁ e ⊔ conjR (sX₁ e) (sw e 0) := by
  rw [sX₁_sup_conj, thetaG, map_phiG_comp]
  exact congrArg (toG e) map_B12

theorem map_B23_thetaG : (B23 F4).map (thetaG e) = sX₂ e ⊔ conjR (sX₂ e) (sw e 1) := by
  rw [sX₂_sup_conj, thetaG, map_phiG_comp]
  exact congrArg (toG e) map_B23

theorem isQuasisimple_of_mulEquiv' {A B : Type*} [Group A] [Group B] (f : A ≃* B)
    (hA : CFSG.Open.IsQuasisimple A) : CFSG.Open.IsQuasisimple B := by
  obtain ⟨hp, hs⟩ := hA
  have hc : (Subgroup.center A).map (f : A →* B) = Subgroup.center B := Subgroup.map_center_eq f
  let f' : A ⧸ Subgroup.center A ≃* B ⧸ Subgroup.center B := QuotientGroup.congr _ _ f hc
  refine ⟨?_, f'.symm.isSimpleGroup⟩
  rw [_root_.commutator_def] at hp ⊢
  rw [← Subgroup.map_top_of_surjective (f : A →* B) f.surjective, ← Subgroup.map_commutator, hp]

theorem isQuasisimple_SL2F4 : CFSG.Open.IsQuasisimple SL(2, F4) := by
  have h4 : 4 ≤ Nat.card F4 := by rw [Nat.card_eq_fintype_card, F4.card]
  refine ⟨(CFSG.LinearGroups.special_linear_dimension_two_perfect
    ⟨Finset.univ, ?_⟩).commutator_eq_top, Matrix.ProjectiveSpecialLinearGroup.rank_two_simple h4⟩
  rw [Finset.card_univ, F4.card]

theorem card_map_B23_thetaG : Nat.card ((B23 F4).map (thetaG e)) = Nat.card (B23 F4) := by
  have hle : (B23 F4).map psiTheta ≤ T46 := by rw [map_B23]; exact grp_le_T46 gensOK_chB23
  rw [thetaG, map_phiG_comp]
  exact (card_toG (e := e) hle).trans card_map_B23

theorem X₂_quasisimple_F4 :
    CFSG.Open.IsQuasisimple (sX₂ e ⊔ conjR (sX₂ e) (sw e 1) : Subgroup G) := by
  rw [← map_B23_thetaG]
  set f := (thetaG e).comp (B23 F4).subtype
  have hrange : f.range = (B23 F4).map (thetaG e) := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
  have hinj : Function.Injective f := by
    have hcard : Nat.card f.range = Nat.card (B23 F4) := by rw [hrange, card_map_B23_thetaG]
    have hbij := Function.Surjective.bijective_of_nat_card_le f.rangeRestrict_surjective hcard.ge
    intro a b hab
    exact hbij.1 (Subtype.ext hab)
  have e1 : SL(2, F4) ≃* B23 F4 :=
    MonoidHom.ofInjective (blockSL_injective (K := F4) (m := 3) (k := 2) (i := 1) (by omega))
  have e2 : B23 F4 ≃* (B23 F4).map (thetaG e) :=
    (MonoidHom.ofInjective hinj).trans (MulEquiv.subgroupCongr hrange)
  exact isQuasisimple_of_mulEquiv' (e1.trans e2) isQuasisimple_SL2F4

@[expose] noncomputable def sK₂EquivPSL :
    sK₂ e ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 3) F4 :=
  (MulEquiv.subgroupCongr range_thetaG).symm.trans
    ((QuotientGroup.quotientKerEquivRange (thetaG e)).symm.trans
      (QuotientGroup.quotientMulEquivOfEq ker_thetaG))

theorem K₂_lie_F4 : CFSG.Blueprint.LieModel (sK₂ e) .PSL 3 2 2 :=
  Or.inl ⟨by decide, ⟨Nat.prime_two, by norm_num, by norm_num, by simp, by simp⟩, F4,
    inferInstance, inferInstance, by rw [Nat.card_eq_fintype_card, F4.card]; norm_num,
    ⟨sK₂EquivPSL.trans (CFSG.Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj 3 F4)⟩⟩

variable (e) in
@[expose] noncomputable def chiG : msigma F4 →* G := (phiG e).comp chi0

theorem range_chiG : (chiG e).range = sK₁ e := by
  rw [chiG, range_phiG_comp]
  exact congrArg (toG e) range_psiChi

theorem chiG_injective : Function.Injective (chiG e) := injective_phiG_comp psiChi_injective

theorem K₁_model_F4 : ∃ χ : msigma F4 ≃* sK₁ e,
    (∀ A : msigma F4, (A : SL(4, F4)) = sY F4 0 * sY F4 2 → (χ A : G) = sw e 1) ∧
    (∀ A : msigma F4, (A : SL(4, F4)) = sY F4 1 → (χ A : G) = sw e 2) ∧
    ∀ A : msigma F4, (A : SL(4, F4)) ∈ pstd F4 →
      (χ A : G) ∈ sS e ⊓ conjR (sS e) (sw e 0 * sw e 1 * sw e 2 * sw e 1 * sw e 0) := by
  refine ⟨(MonoidHom.ofInjective chiG_injective).trans (MulEquiv.subgroupCongr range_chiG),
    fun A hA => ?_, fun A hA => ?_, fun A hA => ?_⟩
  · have : A = ⟨_, sY02_mem⟩ := Subtype.ext hA
    subst this
    show chiG e _ = phiG e (yamGen 16)
    rw [chiG, MonoidHom.comp_apply, chi0_sY02]
  · have : A = ⟨_, sY1_mem⟩ := Subtype.ext hA
    subst this
    show chiG e _ = phiG e (yamGen 17)
    rw [chiG, MonoidHom.comp_apply, chi0_sY1]
  · rw [S_u₁_eq]
    show chiG e A ∈ _
    rw [chiG, MonoidHom.comp_apply, phiG_mem_toG]
    exact psiChi_mem_T1 hA

end CFSG.EvenSmallLie.UnitarySix.YamadaSec3
