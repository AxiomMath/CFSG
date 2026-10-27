module

public import CFSG.ClassicalInvolution.ModelFacts.D4RigidFrame
public import CFSG.ClassicalInvolution.RouteD.TriageSU4Frame
public import CFSG.ClassicalInvolution.RouteD.GapsToralB

public section

namespace CFSG.ClassicalInvolution.ModelFacts.D4Rigid

open CFSG.LieType.Universal.Spin QuadraticMap CFSG.Assembly.LowTwoRank
open CFSG.ClassicalInvolution.Generic (Commutes conjSub fundamentalSubgroups)
open CFSG.ClassicalInvolution.WeakCT (LinearBlockStandardPair)
open CFSG.ClassicalInvolution.RouteD.Gaps

section Abstract

variable {K X : Type} [Group K] [Group X]

theorem map_range_le_of_fixes (hqs : CFSG.Open.IsQuasisimple K) (φ : K →* X)
    (hnorm : φ.range.Normal) (α : X ≃* X) {R₀ : Subgroup K} (hR₀ : ¬ R₀ ≤ Subgroup.center K)
    (hfix : ∀ a ∈ R₀.map φ, α a = a) : ∀ k : K, α (φ k) ∈ φ.range := by
  let S : Subgroup K := Subgroup.comap (α.toMonoidHom.comp φ) φ.range
  have hSn : S.Normal := by
    refine ⟨fun s hs g => ?_⟩
    rw [Subgroup.mem_comap] at hs ⊢
    have h1 := hnorm.conj_mem _ hs (α (φ g))
    simpa [map_mul, map_inv] using h1
  have hR₀S : R₀ ≤ S := by
    intro r hr
    rw [Subgroup.mem_comap]
    show α (φ r) ∈ φ.range
    rw [hfix _ ⟨r, hr, rfl⟩]
    exact ⟨r, rfl⟩
  have htop : ⊤ ≤ S := top_le_of_normal_of_not_le_center hqs hSn
    (fun h => hR₀ (hR₀S.trans h))
  intro k
  exact htop (Subgroup.mem_top k)

end Abstract

section Concrete

variable {p f : ℕ} [Fact p.Prime]

theorem exists_unit_sq_ne_one (hq : 5 ≤ p ^ f) :
    ∃ c : (GaloisField p f)ˣ, ((c : GaloisField p f)) ^ 2 ≠ 1 := by
  have : NeZero f := ⟨by rintro rfl; simp at hq⟩
  obtain ⟨ζ, hζ⟩ := IsCyclic.exists_generator (α := (GaloisField p f)ˣ)
  have hcard : Nat.card (GaloisField p f) = p ^ f := GaloisField.card p f (NeZero.ne f)
  have hord : orderOf ζ = Nat.card (GaloisField p f) - 1 := by
    rw [orderOf_eq_card_of_forall_mem_zpowers hζ, Nat.card_units]
  refine ⟨ζ, fun h => ?_⟩
  have h' : ζ ^ 2 = 1 := Units.ext (by simpa using h)
  have := Nat.le_of_dvd (by omega) (orderOf_dvd_of_pow_eq_one h')
  omega

theorem d4FrameRigid_spin (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f)
    (hqs : CFSG.Open.IsQuasisimple (spinGroup (quadPlus 4 (GaloisField p f))))
    {X : Type} [Group X] (φ : spinGroup (quadPlus 4 (GaloisField p f)) →* X)
    (hker : φ.ker ≤ Subgroup.center _) (hnorm : φ.range.Normal) (α : X ≃* X)
    {R : Fin 4 → Subgroup (spinGroup (quadPlus 4 (GaloisField p f)))}
    (hR : ∀ i, R i ∈ fundamentalSubgroups .POmegaPlus
      (plusDatum 4 (GaloisField p f) (by norm_num)))
    (hinj : Function.Injective R) (hcomm : ∀ i j, i ≠ j → Commutes (R i) (R j))
    (hfix : ∀ i, ∀ a ∈ (R i).map φ, α a = a)
    {R₅ : Subgroup (spinGroup (quadPlus 4 (GaloisField p f)))}
    (h5 : R₅ ∈ fundamentalSubgroups .POmegaPlus (plusDatum 4 (GaloisField p f) (by norm_num)))
    (hs₀ : ∃ W, LinearBlockStandardPair (GaloisField p f) W ((R 0).map φ) (R₅.map φ)) :
    (R₅.map φ).map (α : X →* X) = R₅.map φ := by
  classical
  have hm3 : 3 ≤ 4 := by norm_num
  have : NeZero 4 := ⟨by norm_num⟩
  have : Nonempty (Fin 4 ⊕ Fin 4) := ⟨Sum.inl 0⟩
  have hfin : Finite (spinGroup (quadPlus 4 (GaloisField p f))) :=
    finite_spinGroup_of_ker _ coe_ker_spinMatrix_quadPlus
  have cq := centralQuot_plus hp2 (le_refl 4) hm3 hq
  obtain ⟨-, hK⟩ := CFSG.ClassicalInvolution.RouteD.card_galoisField_of_four_le
    (p := p) (f := f) (by omega)
  have hC : ¬ p ∣ Nat.card (Subgroup.center (spinGroup (quadPlus 4 (GaloisField p f)))) :=
    not_dvd_card_center_plus hp2 hm3
  have hlinK : ∃ W, LinearBlockStandardPair (GaloisField p f) W (R 0) R₅ :=
    exists_lin_of_map (by omega) hC φ hker (cq.perf _ (hR 0)) (cq.perf _ h5) hs₀
  have hnc : ¬ R 0 ≤ Subgroup.center (spinGroup (quadPlus 4 (GaloisField p f))) := by
    intro hle
    obtain ⟨W, hW⟩ := hlinK
    exact CFSG.ClassicalInvolution.RouteD.not_commutes_of_linearBlockStandardPair hW
      fun a ha b _ => (Subgroup.mem_center_iff.mp (hle ha) b).symm
  have hα := map_range_le_of_fixes hqs φ hnorm α hnc (hfix 0)
  have hα' := map_range_le_of_fixes hqs φ hnorm α.symm hnc
    (fun a ha => (MulEquiv.symm_apply_eq α).mpr (hfix 0 a ha).symm)
  have hαY : ∀ y ∈ φ.range, α y ∈ φ.range := by
    rintro _ ⟨k, rfl⟩
    exact hα k
  have hα'Y : ∀ y ∈ φ.range, α.symm y ∈ φ.range := by
    rintro _ ⟨k, rfl⟩
    exact hα' k
  let σ : φ.range ≃* φ.range :=
    { toFun := fun y => ⟨α y, hαY y y.2⟩
      invFun := fun y => ⟨α.symm y, hα'Y y y.2⟩
      left_inv := fun y => Subtype.ext (α.symm_apply_apply y)
      right_inv := fun y => Subtype.ext (α.apply_symm_apply y)
      map_mul' := fun a b => Subtype.ext (map_mul α (a : X) (b : X)) }
  have hθker : φ.rangeRestrict.ker ≤ Subgroup.center (spinGroup (quadPlus 4 (GaloisField p f))) :=
    by rwa [MonoidHom.ker_rangeRestrict]
  have hθC : ¬ p ∣ Nat.card φ.rangeRestrict.ker := fun hd =>
    hC (hd.trans (Subgroup.card_dvd_of_le hθker))
  obtain ⟨β, hβ⟩ := (ModelFacts.OrthAut.centralPSection_spinPlus (p := p) hm3).exists_mulEquiv_lift
    φ.rangeRestrict φ.rangeRestrict_surjective hθker hθC σ
  have hβφ : ∀ k, φ (β k) = α (φ k) := fun k => congrArg Subtype.val (hβ k)
  have hβR : ∀ i, ∀ r ∈ R i, β r = r := by
    intro i r hr
    have : Group.IsPerfect ↥(R i) := Subgroup.isPerfect_iff.mpr (cq.perf _ (hR i))
    have := ModelFacts.OrthAut.eq_of_inv_mul_mem_center (R i).subtype
      (β.toMonoidHom.comp (R i).subtype) (fun y => ?_)
    · exact congrArg (fun g => g ⟨r, hr⟩) this
    · apply hker
      rw [MonoidHom.mem_ker, map_mul, map_inv]
      show (φ (β y))⁻¹ * φ y = 1
      rw [hβφ, hfix i _ ⟨y, y.2, rfl⟩, inv_mul_cancel]
  obtain ⟨x, h5eq, h0eq, hstd⟩ := exists_normal_position hp2 hq hR hinj hcomm h5 hlinK
  let β' : spinGroup (quadPlus 4 (GaloisField p f)) ≃* spinGroup (quadPlus 4 (GaloisField p f)) :=
    (MulAut.conj x).trans (β.trans (MulAut.conj x⁻¹))
  have hβ' : ∀ y, β' y = x⁻¹ * β (x * y * x⁻¹) * x := by
    intro y
    simp [β', MulAut.conj_apply]
  have hβ'' : ∀ y, β (x * y * x⁻¹) = x * β' y * x⁻¹ := by
    intro y
    rw [hβ']
    group
  have hfixstd : ∀ (j : Fin 4) (g : spinGroup (quadPlus 4 (GaloisField p f))),
      g ∈ stdSL2 (GaloisField p f) j → β' g = g := by
    intro j g hg
    obtain ⟨i, hi⟩ := hstd j
    have hmem : x * g * x⁻¹ ∈ R i := by
      rw [← hi]
      exact ⟨g, hg, rfl⟩
    rw [hβ', hβR i _ hmem]
    group
  have hF : FixesFrame β' :=
    ⟨fun M => hfixstd 0 _ ⟨M, rfl⟩, fun M => hfixstd 1 _ ⟨M, rfl⟩,
      fun M => hfixstd 2 _ ⟨M, rfl⟩, fun M => hfixstd 3 _ ⟨M, rfl⟩⟩
  obtain ⟨c, hc2⟩ := exists_unit_sq_ne_one (p := p) (f := f) hq
  have hrange := map_range_longSL2_eq hp2 hc2 hF
  have hβ5 : R₅.map β.toMonoidHom = R₅ := by
    apply le_antisymm
    · rintro _ ⟨r, hr, rfl⟩
      rw [h5eq] at hr
      obtain ⟨y, hy, rfl⟩ := hr
      have hy' : β' y ∈ ((fr (GaloisField p f)).longSL2 ne12 true false).range := by
        rw [← hrange]
        exact ⟨y, hy, rfl⟩
      rw [h5eq]
      exact ⟨β' y, hy', (hβ'' y).symm⟩
    · intro r hr
      rw [h5eq] at hr
      obtain ⟨y, hy, rfl⟩ := hr
      have hy' : y ∈ ((fr (GaloisField p f)).longSL2 ne12 true false).range.map β'.toMonoidHom := by
        rw [hrange]
        exact hy
      obtain ⟨y', hy'', rfl⟩ := hy'
      refine ⟨x * y' * x⁻¹, ?_, hβ'' y'⟩
      rw [h5eq]
      exact ⟨y', hy'', rfl⟩
  ext y
  constructor
  · rintro ⟨_, ⟨r, hr, rfl⟩, rfl⟩
    have h1 : β r ∈ R₅ := by
      have : β r ∈ R₅.map β.toMonoidHom := ⟨r, hr, rfl⟩
      rwa [hβ5] at this
    exact ⟨β r, h1, (hβφ r)⟩
  · rintro ⟨r, hr, rfl⟩
    have h1 : r ∈ R₅.map β.toMonoidHom := by
      rw [hβ5]
      exact hr
    obtain ⟨r', hr', rfl⟩ := h1
    exact ⟨φ r', ⟨r', hr', rfl⟩, (hβφ r').symm⟩

theorem d4FrameRigid (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f) :
    CFSG.ClassicalInvolution.RouteD.D4FrameRigid p f .POmegaPlus 4 f := by
  have hf1 : 1 ≤ f := by
    rcases Nat.eq_zero_or_pos f with h | h
    · subst h
      simp at hq
    · exact h
  have hm3 : 3 ≤ 4 := by norm_num
  have hadm : StatedLieAdmissible .POmegaPlus 4 p f := ⟨Fact.out, hf1, le_refl 4⟩
  have hqs := isQuasisimple_modelUniv .POmegaPlus 4 p f Fact.out trivial hadm
  have key : ∀ M : CFSG.LieType.Universal.LieUniversal,
      M = ⟨spinGroup (quadPlus 4 (GaloisField p f)), plusDatum 4 (GaloisField p f) hm3⟩ →
      CFSG.Open.IsQuasisimple M.K →
      ∀ (X : Type) [Group X] (φ : M.K →* X), φ.ker ≤ Subgroup.center _ → φ.range.Normal →
        ∀ (α : X ≃* X) (R : Fin 4 → Subgroup M.K),
          (∀ i, R i ∈ fundamentalSubgroups .POmegaPlus M.D) → Function.Injective R →
          (∀ i j, i ≠ j → Commutes (R i) (R j)) → (∀ i, ∀ a ∈ (R i).map φ, α a = a) →
          ∀ R₅ ∈ fundamentalSubgroups .POmegaPlus M.D,
            (∃ W, LinearBlockStandardPair (GaloisField p f) W ((R 0).map φ) (R₅.map φ)) →
            (∃ W, LinearBlockStandardPair (GaloisField p f) W ((R 2).map φ) (R₅.map φ)) →
            (R₅.map φ).map (α : X →* X) = R₅.map φ := by
    intro M hM hqsM
    subst hM
    intro X _ φ hker hnorm α R hR hinj hcomm hfix R₅ h5 hs₀ _
    exact d4FrameRigid_spin hp2 hq hqsM φ hker hnorm α hR hinj hcomm hfix h5 hs₀
  exact key _ (modelUniv_POmegaPlus hm3) hqs

end Concrete

end CFSG.ClassicalInvolution.ModelFacts.D4Rigid
