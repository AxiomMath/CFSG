module

public import CFSG.LieType.BorelTits.FormFlag
public import CFSG.LocalAnalysis.ComponentInitial.FieldUnitaryHermitian
public import CFSG.HardMathSupport.Curtis.UnitaryLevi.ChainPieceScalar

public section

namespace CFSG.LieType.BorelTits

open CFSG.HardMathSupport.Curtis.UnitaryLevi CFSG.LocalAnalysis.ComponentInitial

universe u v w

variable {K : Type u} {V : Type v} [Field K] [AddCommGroup V] [Module K V] {H : Type w} [Group H]
  (F : ReflForm K V) (ρ : H →* Module.End K V)

theorem isoFlag_eq_isoSeq (R : Subgroup H) {k : ℕ} (hk : k ≤ Module.finrank K V) :
    isoFlag F ρ R k = isoSeq F ρ R k := by
  rw [isoFlag, ite_eq_left hk]

theorem isoFlag_eq_top [FiniteDimensional K V] (R : Subgroup H) {k : ℕ}
    (hk : 2 * Module.finrank K V + 1 ≤ k) : isoFlag F ρ R k = ⊤ := by
  rcases eq_or_lt_of_le hk with h | h
  · rw [← h]
    exact isoFlag_top F ρ R
  · rw [isoFlag, ite_eq_right (by omega), ite_eq_right (by omega)]

theorem isoSeq_one_le_isoFlag (R : Subgroup H) {k : ℕ} (hk : 1 ≤ k)
    (hk' : k ≤ 2 * Module.finrank K V) : isoSeq F ρ R 1 ≤ isoFlag F ρ R k := by
  rcases le_or_gt k (Module.finrank K V) with h | h
  · rw [isoFlag_eq_isoSeq F ρ R (k := k) h]
    exact isoSeq_mono F ρ R hk
  · rw [isoFlag, ite_eq_right (by omega), ite_eq_left (by omega)]
    exact (isoSeq_mono F ρ R (show 1 ≤ 2 * Module.finrank K V + 1 - k by omega)).trans
      (isoSeq_isTotallyIsotropic F ρ R _)

theorem isoFlag_le_perp_isoSeq_one (R : Subgroup H) {k : ℕ} (hk : 1 ≤ k)
    (hk' : k ≤ 2 * Module.finrank K V) :
    isoFlag F ρ R k ≤ F.perp (isoSeq F ρ R 1) := by
  rcases le_or_gt k (Module.finrank K V) with h | h
  · rw [isoFlag_eq_isoSeq F ρ R (k := k) h]
    exact (isoSeq_isTotallyIsotropic F ρ R k).trans (F.perp_antitone (isoSeq_mono F ρ R hk))
  · rw [isoFlag, ite_eq_right (by omega), ite_eq_left (by omega)]
    exact F.perp_antitone (isoSeq_mono F ρ R (show 1 ≤ 2 * Module.finrank K V + 1 - k by omega))

theorem mem_flagKernel_isoFlag_of_trivial [FiniteDimensional K V] (hρ : IsIsometric F ρ)
    (R : Subgroup H) {g : H} (hg : g ∈ flagStab ρ (isoFlag F ρ R))
    (h1 : ∀ w ∈ isoSeq F ρ R 1, ρ g w = w)
    (h2 : ∀ v ∈ F.perp (isoSeq F ρ R 1), ρ g v - v ∈ isoSeq F ρ R 1) :
    g ∈ flagKernel ρ (isoFlag F ρ R) := by
  refine ⟨hg, ?_⟩
  intro k v hv
  by_cases hd : Module.finrank K V = 0
  · have hW : isoSeq F ρ R 1 = ⊥ := by
      have h := isoSeq_eq_of_le F ρ R (j := 1) (by omega)
      rwa [hd, isoSeq_zero] at h
    have htriv : ρ g v = v := by
      have hv' : v ∈ F.perp (isoSeq F ρ R 1) := by
        rw [hW, F.perp_bot]
        exact Submodule.mem_top
      have := h2 v hv'
      rwa [hW, Submodule.mem_bot, sub_eq_zero] at this
    rw [htriv, sub_self]
    exact (isoFlag F ρ R k).zero_mem
  · have hd1 : 1 ≤ Module.finrank K V := by omega
    have hflag1 : isoFlag F ρ R 1 = isoSeq F ρ R 1 := isoFlag_eq_isoSeq F ρ R hd1
    have hflag2 : isoFlag F ρ R (2 * Module.finrank K V) = F.perp (isoSeq F ρ R 1) := by
      rw [isoFlag, ite_eq_right (by omega), ite_eq_left (by omega),
        show 2 * Module.finrank K V + 1 - 2 * Module.finrank K V = 1 by omega]
    rcases Nat.eq_zero_or_pos k with rfl | hk1
    · rw [hflag1] at hv
      rw [h1 v hv, sub_self]
      exact (isoFlag F ρ R 0).zero_mem
    · rcases lt_or_ge k (2 * Module.finrank K V) with hk | hk
      · have hv' : v ∈ F.perp (isoSeq F ρ R 1) :=
          isoFlag_le_perp_isoSeq_one F ρ R (k := k + 1) (by omega) (by omega) hv
        exact isoSeq_one_le_isoFlag F ρ R (k := k) hk1 (by omega) (h2 v hv')
      · rcases eq_or_lt_of_le hk with rfl | hk
        · rw [hflag2, F.mem_perp]
          intro w hw
          rw [F.β_sub_right, ← h1 w hw, hρ g w v, h1 w hw, sub_self]
        · rw [isoFlag_eq_top F ρ R (by omega)]
          exact Submodule.mem_top

theorem flagStab_apply_mem_isoSeq_one [FiniteDimensional K V] {R : Subgroup H} {g : H}
    (hg : g ∈ flagStab ρ (isoFlag F ρ R)) {w : V} (hw : w ∈ isoSeq F ρ R 1) :
    ρ g w ∈ isoSeq F ρ R 1 := by
  rcases eq_or_ne (Module.finrank K V) 0 with hd | hd
  · have hW : isoSeq F ρ R 1 = ⊥ := by
      have h := isoSeq_eq_of_le F ρ R (j := 1) (by omega)
      rwa [hd, isoSeq_zero] at h
    rw [hW] at hw ⊢
    rw [hw]
    simp
  · have hd1 : 1 ≤ Module.finrank K V := by omega
    have hflag : isoFlag F ρ R 1 = isoSeq F ρ R 1 := isoFlag_eq_isoSeq F ρ R hd1
    have hmem : w ∈ isoFlag F ρ R 1 := by rwa [hflag]
    have := flagStab_apply_mem ρ hg hmem
    rwa [hflag] at this

theorem flagStab_inv_apply_mem_isoSeq_one [FiniteDimensional K V] {R : Subgroup H} {g : H}
    (hg : g ∈ flagStab ρ (isoFlag F ρ R)) {w : V} (hw : w ∈ isoSeq F ρ R 1) :
    ρ g⁻¹ w ∈ isoSeq F ρ R 1 := by
  rcases eq_or_ne (Module.finrank K V) 0 with hd | hd
  · have hW : isoSeq F ρ R 1 = ⊥ := by
      have h := isoSeq_eq_of_le F ρ R (j := 1) (by omega)
      rwa [hd, isoSeq_zero] at h
    rw [hW] at hw ⊢
    rw [hw]
    simp
  · have hd1 : 1 ≤ Module.finrank K V := by omega
    have hflag : isoFlag F ρ R 1 = isoSeq F ρ R 1 := isoFlag_eq_isoSeq F ρ R hd1
    have hmem : w ∈ isoFlag F ρ R 1 := by rwa [hflag]
    have := (hg 1 w hmem).2
    rwa [hflag] at this

theorem flagStab_apply_mem_perp_isoSeq_one [FiniteDimensional K V] (hρ : IsIsometric F ρ)
    {R : Subgroup H} {g : H}
    (hg : g ∈ flagStab ρ (isoFlag F ρ R)) {v : V}
    (hv : v ∈ F.perp (isoSeq F ρ R 1)) : ρ g v ∈ F.perp (isoSeq F ρ R 1) :=
  hρ.apply_mem_perp_of_forall (fun w hw => flagStab_inv_apply_mem_isoSeq_one F ρ hg hw) hv

theorem flagStab_inv_apply_mem_perp_isoSeq_one [FiniteDimensional K V] (hρ : IsIsometric F ρ)
    {R : Subgroup H} {g : H}
    (hg : g ∈ flagStab ρ (isoFlag F ρ R)) {v : V}
    (hv : v ∈ F.perp (isoSeq F ρ R 1)) : ρ g⁻¹ v ∈ F.perp (isoSeq F ρ R 1) :=
  hρ.apply_mem_perp_of_forall (h := g⁻¹) (fun w hw => by
    simpa using flagStab_apply_mem_isoSeq_one F ρ hg hw) hv

noncomputable def perpFormRestrict (τ : K →+* K) (hτ : ∀ c, F.σ c = τ c) (W : Submodule K V) :
    ↥(F.perp W) →ₛₗ[τ] ↥(F.perp W) →ₗ[K] K where
  toFun u :=
    { toFun := fun v => F.β u.1 v.1
      map_add' := fun v v' => by
        change F.β u.1 (v.1 + v'.1) = F.β u.1 v.1 + F.β u.1 v'.1
        rw [F.add_right]
      map_smul' := fun c v => by
        change F.β u.1 (c • v.1) = c * F.β u.1 v.1
        rw [F.smul_right] }
  map_add' u u' := by
    ext v
    change F.β (u.1 + u'.1) v.1 = F.β u.1 v.1 + F.β u'.1 v.1
    rw [F.add_left]
  map_smul' c u := by
    ext v
    change F.β (c • u.1) v.1 = τ c * F.β u.1 v.1
    rw [F.smul_left, hτ]

noncomputable def perpForm (τ : K →+* K) (hτ : ∀ c, F.σ c = τ c) (W : Submodule K V)
    (hW : F.IsTotallyIsotropic W) :
    PieceQ W (F.perp W) →ₛₗ[τ] PieceQ W (F.perp W) →ₗ[K] K :=
  (perpFormRestrict F τ hτ W).liftQ₂ (W.comap (F.perp W).subtype) (W.comap (F.perp W).subtype)
    (by
      intro u hu
      ext v
      exact F.mem_perp.mp v.2 u.1 (by simpa using Submodule.mem_comap.mp hu))
    (by
      intro v hv
      ext u
      exact F.refl v.1 u.1 (F.mem_perp.mp u.2 v.1 (by simpa using Submodule.mem_comap.mp hv)))

theorem perpForm_mk (τ : K →+* K) (hτ : ∀ c, F.σ c = τ c) {W : Submodule K V}
    (hW : F.IsTotallyIsotropic W) (u v : ↥(F.perp W)) :
    perpForm F τ hτ W hW (Submodule.Quotient.mk u) (Submodule.Quotient.mk v) = F.β u v := by
  rw [perpForm]
  exact LinearMap.liftQ₂_mk _ _ u v

theorem perpForm_isSymm (τ : K →+* K) (hτ : ∀ c, F.σ c = τ c) {W : Submodule K V}
    (hW : F.IsTotallyIsotropic W) (hherm : ∀ u v, τ (F.β u v) = F.β v u) :
    (perpForm F τ hτ W hW).IsSymm := by
  refine ⟨fun x y => ?_⟩
  induction x using Submodule.Quotient.induction_on with
  | H u =>
    induction y using Submodule.Quotient.induction_on with
    | H v =>
      rw [perpForm_mk, perpForm_mk]
      exact hherm u v

theorem perpForm_separatingLeft [FiniteDimensional K V] (τ : K →+* K)
    (hτ : ∀ c, F.σ c = τ c) {W : Submodule K V} (hW : F.IsTotallyIsotropic W) :
    (perpForm F τ hτ W hW).SeparatingLeft := by
  intro x hx
  obtain ⟨u, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  rw [Submodule.Quotient.mk_eq_zero, Submodule.mem_comap]
  have hmem : u.1 ∈ F.perp (F.perp W) := by
    rw [F.mem_perp]
    intro v hv
    exact F.refl u.1 v (by
      rw [← perpForm_mk F τ hτ hW u ⟨v, hv⟩]
      exact hx (Submodule.Quotient.mk ⟨v, hv⟩))
  rwa [F.perp_perp] at hmem

theorem finrank_pieceQ_perp [FiniteDimensional K V] {W : Submodule K V}
    (hW : F.IsTotallyIsotropic W) :
    Module.finrank K (PieceQ W (F.perp W)) + 2 * Module.finrank K W = Module.finrank K V := by
  have h1 := Submodule.finrank_quotient_add_finrank (W.comap (F.perp W).subtype)
  have h2 : Module.finrank K (W.comap (F.perp W).subtype) = Module.finrank K W :=
    (Submodule.comapSubtypeEquivOfLe hW).finrank_eq
  have h3 := F.finrank_perp W
  have h1' : Module.finrank K (PieceQ W (F.perp W)) + Module.finrank K W =
      Module.finrank K (F.perp W) := by
    rw [← h2]
    exact h1
  omega

theorem finrank_pieceQ_bot (W : Submodule K V) :
    Module.finrank K (PieceQ ⊥ W) = Module.finrank K W := by
  have hp : (⊥ : Submodule K V).comap W.subtype = ⊥ := by
    rw [Submodule.comap_bot, Submodule.ker_subtype]
  exact ((⊥ : Submodule K V).comap W.subtype).quotEquivOfEqBot hp |>.finrank_eq

noncomputable def leviStabPairOne [FiniteDimensional K V] (R : Subgroup H) :
    flagStab ρ (isoFlag F ρ R) →* stabPair ⊥ (isoSeq F ρ R 1) where
  toFun g := ⟨ρ.toHomUnits g.1, by
    rw [mem_stabPair]
    exact ⟨fun v hv => by
        rw [Submodule.mem_bot] at hv ⊢
        rw [hv]
        simp,
      fun v hv => by
        simpa [MonoidHom.coe_toHomUnits] using flagStab_apply_mem_isoSeq_one F ρ g.2 hv,
      fun v hv => by
        rw [Submodule.mem_bot] at hv ⊢
        rw [hv]
        simp,
      fun v hv => by
        change ρ g.1⁻¹ v ∈ isoSeq F ρ R 1
        exact flagStab_inv_apply_mem_isoSeq_one F ρ g.2 hv⟩⟩
  map_one' := Subtype.ext (map_one ρ.toHomUnits)
  map_mul' g h := Subtype.ext (map_mul ρ.toHomUnits g.1 h.1)

noncomputable def leviStabPairTwo [FiniteDimensional K V] (hρ : IsIsometric F ρ)
    (R : Subgroup H) :
    flagStab ρ (isoFlag F ρ R) →*
      stabPair (isoSeq F ρ R 1) (F.perp (isoSeq F ρ R 1)) where
  toFun g := ⟨ρ.toHomUnits g.1, by
    rw [mem_stabPair]
    exact ⟨fun v hv => by
        simpa [MonoidHom.coe_toHomUnits] using flagStab_apply_mem_isoSeq_one F ρ g.2 hv,
      fun v hv => by
        simpa [MonoidHom.coe_toHomUnits] using
          flagStab_apply_mem_perp_isoSeq_one F ρ hρ g.2 hv,
      fun v hv => by
        change ρ g.1⁻¹ v ∈ isoSeq F ρ R 1
        exact flagStab_inv_apply_mem_isoSeq_one F ρ g.2 hv,
      fun v hv => by
        change ρ g.1⁻¹ v ∈ F.perp (isoSeq F ρ R 1)
        exact flagStab_inv_apply_mem_perp_isoSeq_one F ρ hρ g.2 hv⟩⟩
  map_one' := Subtype.ext (map_one ρ.toHomUnits)
  map_mul' g h := Subtype.ext (map_mul ρ.toHomUnits g.1 h.1)

noncomputable def leviHomOne [FiniteDimensional K V] (R : Subgroup H) :
    flagStab ρ (isoFlag F ρ R) →* LinearMap.GeneralLinearGroup K (PieceQ ⊥ (isoSeq F ρ R 1)) :=
  (quotGL ⊥ (isoSeq F ρ R 1)).comp (leviStabPairOne F ρ R)

noncomputable def leviHomTwo [FiniteDimensional K V] (hρ : IsIsometric F ρ) (R : Subgroup H) :
    flagStab ρ (isoFlag F ρ R) →*
      LinearMap.GeneralLinearGroup K (PieceQ (isoSeq F ρ R 1) (F.perp (isoSeq F ρ R 1))) :=
  (quotGL (isoSeq F ρ R 1) (F.perp (isoSeq F ρ R 1))).comp (leviStabPairTwo F ρ hρ R)

noncomputable def leviHom [FiniteDimensional K V] (hρ : IsIsometric F ρ) (R : Subgroup H) :
    flagStab ρ (isoFlag F ρ R) →* LinearMap.GeneralLinearGroup K (PieceQ ⊥ (isoSeq F ρ R 1)) ×
      LinearMap.GeneralLinearGroup K (PieceQ (isoSeq F ρ R 1) (F.perp (isoSeq F ρ R 1))) :=
  (leviHomOne F ρ R).prod (leviHomTwo F ρ hρ R)

theorem quotGL_mem_sesqUnitaryGroup_of_isometry (τ : K →+* K) (hτ : ∀ c, F.σ c = τ c)
    {W : Submodule K V} (hW : F.IsTotallyIsotropic W) (g : stabPair W (F.perp W))
    (hg : ∀ u v, F.β (((g : LinearMap.GeneralLinearGroup K V) : Module.End K V) u)
      (((g : LinearMap.GeneralLinearGroup K V) : Module.End K V) v) = F.β u v) :
    quotGL W (F.perp W) g ∈ sesqUnitaryGroup (perpForm F τ hτ W hW) := by
  rw [mem_sesqUnitaryGroup]
  intro x y
  induction x using Submodule.Quotient.induction_on with
  | H u =>
    induction y using Submodule.Quotient.induction_on with
    | H v =>
      simpa only [coe_quotGL, quotEnd_mk, perpForm_mk] using hg u v

theorem leviHomTwo_mem_sesqSpecialUnitaryGroup [FiniteDimensional K V]
    (hρ : IsIsometric F ρ) (R : Subgroup H)
    (τ : K →+* K) (hτ : ∀ c, F.σ c = τ c) {T : Subgroup H}
    (hP : ⁅T, T⁆ ≤ flagStab ρ (isoFlag F ρ R)) (x : ↥⁅T, T⁆)
    (hdet : (leviHomTwo F ρ hρ R).comp (Subgroup.inclusion hP) x ∈
      (Units.map (LinearMap.det :
        Module.End K (PieceQ (isoSeq F ρ R 1) (F.perp (isoSeq F ρ R 1))) →* K)).ker) :
    (leviHomTwo F ρ hρ R).comp (Subgroup.inclusion hP) x ∈
      sesqSpecialUnitaryGroup (perpForm F τ hτ (isoSeq F ρ R 1)
        (isoSeq_isTotallyIsotropic F ρ R 1)) := by
  rw [mem_sesqSpecialUnitaryGroup]
  refine ⟨?_, ?_⟩
  · have hunit : quotGL (isoSeq F ρ R 1) (F.perp (isoSeq F ρ R 1))
        (leviStabPairTwo F ρ hρ R ((Subgroup.inclusion hP) x)) ∈
        sesqUnitaryGroup (perpForm F τ hτ (isoSeq F ρ R 1)
          (isoSeq_isTotallyIsotropic F ρ R 1)) :=
      quotGL_mem_sesqUnitaryGroup_of_isometry F τ hτ (isoSeq_isTotallyIsotropic F ρ R 1) _
        (fun u v => by
          simpa [leviStabPairTwo, MonoidHom.coe_toHomUnits] using
            hρ ((Subgroup.inclusion hP) x).1 u v)
    simpa [leviHomTwo] using hunit
  · have h := hdet
    simpa [MonoidHom.mem_ker, Units.ext_iff] using h

theorem mem_flagKernel_of_leviHom_eq_one [FiniteDimensional K V] (hρ : IsIsometric F ρ)
    (R : Subgroup H) {g : H} (hg : g ∈ flagStab ρ (isoFlag F ρ R))
    (h : leviHom F ρ hρ R ⟨g, hg⟩ = 1) : g ∈ flagKernel ρ (isoFlag F ρ R) := by
  have h1q : leviHomOne F ρ R ⟨g, hg⟩ = 1 := congrArg Prod.fst h
  have h2q : leviHomTwo F ρ hρ R ⟨g, hg⟩ = 1 := congrArg Prod.snd h
  have h1 : ∀ w ∈ isoSeq F ρ R 1, ρ g w = w := by
    intro w hw
    have hq : quotGL ⊥ (isoSeq F ρ R 1) (leviStabPairOne F ρ R ⟨g, hg⟩) = 1 := by
      simpa [leviHomOne] using h1q
    have hc : ((quotGL ⊥ (isoSeq F ρ R 1) (leviStabPairOne F ρ R ⟨g, hg⟩) :
        LinearMap.GeneralLinearGroup K (PieceQ ⊥ (isoSeq F ρ R 1))) :
        Module.End K (PieceQ ⊥ (isoSeq F ρ R 1))) = (1 : K) • 1 := by
      rw [hq]
      simp
    have := sub_smul_mem_of_quotGL_eq (F := ⊥) (F' := isoSeq F ρ R 1)
      (e := leviStabPairOne F ρ R ⟨g, hg⟩) (c := 1) hc w hw
    rw [Submodule.mem_bot, sub_eq_zero] at this
    simpa [leviStabPairOne, MonoidHom.coe_toHomUnits] using this
  have h2 : ∀ v ∈ F.perp (isoSeq F ρ R 1), ρ g v - v ∈ isoSeq F ρ R 1 := by
    intro v hv
    have hq : quotGL (isoSeq F ρ R 1) (F.perp (isoSeq F ρ R 1))
        (leviStabPairTwo F ρ hρ R ⟨g, hg⟩) = 1 := by
      simpa [leviHomTwo] using h2q
    have hc : ((quotGL (isoSeq F ρ R 1) (F.perp (isoSeq F ρ R 1))
        (leviStabPairTwo F ρ hρ R ⟨g, hg⟩) :
        LinearMap.GeneralLinearGroup K (PieceQ (isoSeq F ρ R 1) (F.perp (isoSeq F ρ R 1)))) :
        Module.End K (PieceQ (isoSeq F ρ R 1) (F.perp (isoSeq F ρ R 1)))) = (1 : K) • 1 := by
      rw [hq]
      simp
    have := sub_smul_mem_of_quotGL_eq (F := isoSeq F ρ R 1) (F' := F.perp (isoSeq F ρ R 1))
      (e := leviStabPairTwo F ρ hρ R ⟨g, hg⟩) (c := 1) hc v hv
    simpa [leviStabPairTwo, MonoidHom.coe_toHomUnits] using this
  exact mem_flagKernel_isoFlag_of_trivial F ρ hρ R hg h1 h2

theorem leviHomOne_mem_ker_det [FiniteDimensional K V] (R : Subgroup H) {T : Subgroup H}
    (hT : T ≤ flagStab ρ (isoFlag F ρ R))
    (hP : ⁅T, T⁆ ≤ flagStab ρ (isoFlag F ρ R)) (x : ↥⁅T, T⁆) :
    (leviHomOne F ρ R).comp (Subgroup.inclusion hP) x ∈
      (Units.map (LinearMap.det :
        Module.End K (PieceQ ⊥ (isoSeq F ρ R 1)) →* K)).ker := by
  have hcomm : commutator T ≤ ((Units.map (LinearMap.det :
      Module.End K (PieceQ ⊥ (isoSeq F ρ R 1)) →* K)).comp
        ((leviHomOne F ρ R).comp (Subgroup.inclusion hT))).ker :=
    Abelianization.commutator_subset_ker _
  have hx : x.1 ∈ (commutator T).map T.subtype := by
    rw [Subgroup.map_subtype_commutator T]
    exact x.2
  obtain ⟨y, hy, hyx⟩ := Subgroup.mem_map.mp hx
  have hy' : leviHomOne F ρ R ((Subgroup.inclusion hT) y) ∈
      (Units.map (LinearMap.det :
        Module.End K (PieceQ ⊥ (isoSeq F ρ R 1)) →* K)).ker := by
    simpa [leviHomOne] using hcomm hy
  have helem : (Subgroup.inclusion hP) x = (Subgroup.inclusion hT) y := Subtype.ext hyx.symm
  simpa only [MonoidHom.comp_apply, helem] using hy'

theorem leviHomTwo_mem_ker_det [FiniteDimensional K V] (hρ : IsIsometric F ρ)
    (R : Subgroup H) {T : Subgroup H}
    (hT : T ≤ flagStab ρ (isoFlag F ρ R))
    (hP : ⁅T, T⁆ ≤ flagStab ρ (isoFlag F ρ R)) (x : ↥⁅T, T⁆) :
    (leviHomTwo F ρ hρ R).comp (Subgroup.inclusion hP) x ∈
      (Units.map (LinearMap.det :
        Module.End K (PieceQ (isoSeq F ρ R 1) (F.perp (isoSeq F ρ R 1))) →* K)).ker := by
  have hcomm : commutator T ≤ ((Units.map (LinearMap.det :
      Module.End K (PieceQ (isoSeq F ρ R 1) (F.perp (isoSeq F ρ R 1))) →* K)).comp
        ((leviHomTwo F ρ hρ R).comp (Subgroup.inclusion hT))).ker :=
    Abelianization.commutator_subset_ker _
  have hx : x.1 ∈ (commutator T).map T.subtype := by
    rw [Subgroup.map_subtype_commutator T]
    exact x.2
  obtain ⟨y, hy, hyx⟩ := Subgroup.mem_map.mp hx
  have hy' : leviHomTwo F ρ hρ R ((Subgroup.inclusion hT) y) ∈
      (Units.map (LinearMap.det :
        Module.End K (PieceQ (isoSeq F ρ R 1) (F.perp (isoSeq F ρ R 1))) →* K)).ker := by
    simpa [leviHomTwo] using hcomm hy
  have helem : (Subgroup.inclusion hP) x = (Subgroup.inclusion hT) y := Subtype.ext hyx.symm
  simpa only [MonoidHom.comp_apply, helem] using hy'

theorem card_commutator_dvd_levi [Finite H] [FiniteDimensional K V] (hρ : IsIsometric F ρ)
    (R : Subgroup H) (τ : K →+* K) (hτ : ∀ c, F.σ c = τ c) {T : Subgroup H}
    (hT : T ≤ flagStab ρ (isoFlag F ρ R)) :
    Nat.card ↥⁅T, T⁆ ∣ Nat.card ↥(⁅T, T⁆ ⊓ flagKernel ρ (isoFlag F ρ R)) *
      (Nat.card ↥(Units.map (LinearMap.det :
          Module.End K (PieceQ ⊥ (isoSeq F ρ R 1)) →* K)).ker *
        Nat.card ↥(sesqSpecialUnitaryGroup (perpForm F τ hτ (isoSeq F ρ R 1)
          (isoSeq_isTotallyIsotropic F ρ R 1)))) := by
  classical
  set W := isoSeq F ρ R 1
  set SL := (Units.map (LinearMap.det : Module.End K (PieceQ ⊥ W) →* K)).ker
  set SU := sesqSpecialUnitaryGroup (perpForm F τ hτ W (isoSeq_isTotallyIsotropic F ρ R 1))
  set P := flagStab ρ (isoFlag F ρ R)
  set T' := ⁅T, T⁆
  have hP : T' ≤ P := (Subgroup.commutator_mono hT hT).trans (Subgroup.commutator_le_self P)
  let ψT : T' →* LinearMap.GeneralLinearGroup K (PieceQ ⊥ W) ×
      LinearMap.GeneralLinearGroup K (PieceQ W (F.perp W)) :=
    (leviHom F ρ hρ R).comp (Subgroup.inclusion hP)
  have hcard : Nat.card ψT.ker * Nat.card ψT.range = Nat.card T' :=
    Subgroup.card_ker_mul_card_range ψT
  have hker_le : ψT.ker ≤ (flagKernel ρ (isoFlag F ρ R)).subgroupOf T' := by
    intro x hx
    rw [Subgroup.mem_subgroupOf]
    have hx1 : leviHom F ρ hρ R ⟨x.1, hP x.2⟩ = 1 := by
      have hx2 := MonoidHom.mem_ker.mp hx
      rwa [show ψT x = leviHom F ρ hρ R ⟨x.1, hP x.2⟩ from rfl] at hx2
    exact mem_flagKernel_of_leviHom_eq_one F ρ hρ R (hP x.2) hx1
  have hker_dvd : Nat.card ψT.ker ∣ Nat.card ↥(T' ⊓ flagKernel ρ (isoFlag F ρ R)) := by
    have h := Subgroup.card_dvd_of_le hker_le
    have h2 : Nat.card ↥((flagKernel ρ (isoFlag F ρ R)).subgroupOf T') =
        Nat.card ↥(T' ⊓ flagKernel ρ (isoFlag F ρ R)) := by
      rw [← Subgroup.inf_subgroupOf_right (flagKernel ρ (isoFlag F ρ R)) T', inf_comm]
      exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv
    rwa [h2] at h
  have himg_le : ψT.range ≤ SL.prod SU := by
    intro x hx
    obtain ⟨y, rfl⟩ := MonoidHom.mem_range.mp hx
    refine Subgroup.mem_prod.mpr ⟨?_, ?_⟩
    · exact leviHomOne_mem_ker_det F ρ R hT hP y
    · exact leviHomTwo_mem_sesqSpecialUnitaryGroup F ρ hρ R τ hτ hP y
        (leviHomTwo_mem_ker_det F ρ hρ R hT hP y)
  have himg_dvd : Nat.card ψT.range ∣ Nat.card ↥SL * Nat.card ↥SU := by
    have h := Subgroup.card_dvd_of_le himg_le
    have hcardProd : Nat.card ↥(SL.prod SU) = Nat.card ↥SL * Nat.card ↥SU :=
      (Nat.card_congr (Subgroup.prodEquiv SL SU).toEquiv).trans (Nat.card_prod ↥SL ↥SU)
    rwa [hcardProd] at h
  rw [← hcard]
  exact mul_dvd_mul hker_dvd himg_dvd

end CFSG.LieType.BorelTits
