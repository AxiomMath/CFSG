module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.TypesSimil
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.TypesProj

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open QuadraticMap

variable {V : Type} [AddCommGroup V] [Module (ZMod 3) V] [FiniteDimensional (ZMod 3) V]
  {Q : QuadraticForm (ZMod 3) V}

@[expose] noncomputable def orthToSim (Q : QuadraticForm (ZMod 3) V) : OGroup Q →* simGroup Q :=
  Subgroup.inclusion orthogonalGroup_le_simGroup

theorem orthToSim_injective : Function.Injective (orthToSim Q) :=
  Subgroup.inclusion_injective _

@[simp] theorem coe_orthToSim (t : OGroup Q) :
    ((orthToSim Q t : simGroup Q) : V ≃ₗ[ZMod 3] V) = (t : V ≃ₗ[ZMod 3] V) :=
  rfl

@[expose] noncomputable def piSim (Q : QuadraticForm (ZMod 3) V) : Subgroup (simGroup Q) :=
  (piGroup Q).map (orthToSim Q)

theorem mem_piSim_iff {g : simGroup Q} :
    g ∈ piSim Q ↔ g = 1 ∨ g = orthToSim Q (piOrth Q) := by
  constructor
  · rintro ⟨x, hx, rfl⟩
    rcases mem_piGroup_iff.mp hx with rfl | rfl
    · exact Or.inl (map_one _)
    · exact Or.inr rfl
  · rintro (rfl | rfl)
    · exact (piSim Q).one_mem
    · exact ⟨piOrth Q, mem_piGroup_iff.mpr (Or.inr rfl), rfl⟩

theorem orthToSim_piOrth_comm (g : simGroup Q) :
    g * orthToSim Q (piOrth Q) = orthToSim Q (piOrth Q) * g := by
  apply Subtype.ext
  apply LinearEquiv.ext
  intro v
  change (g : V ≃ₗ[ZMod 3] V) ((piOrth Q : V ≃ₗ[ZMod 3] V) v) =
    (piOrth Q : V ≃ₗ[ZMod 3] V) ((g : V ≃ₗ[ZMod 3] V) v)
  rw [coe_piOrth_apply, coe_piOrth_apply, map_neg]

instance piSim_normal : (piSim Q).Normal :=
  ⟨fun n hn g => by
    rcases mem_piSim_iff.mp hn with rfl | rfl
    · rw [mul_one, mul_inv_cancel]
      exact (piSim Q).one_mem
    · rw [orthToSim_piOrth_comm g, mul_assoc, mul_inv_cancel, mul_one]
      exact mem_piSim_iff.mpr (Or.inr rfl)⟩

abbrev ProjSim (Q : QuadraticForm (ZMod 3) V) : Type := simGroup Q ⧸ piSim Q

@[expose] noncomputable def projOrthToProjSim (Q : QuadraticForm (ZMod 3) V) :
    ProjOrth Q →* ProjSim Q :=
  QuotientGroup.lift (piGroup Q) ((QuotientGroup.mk' (piSim Q)).comp (orthToSim Q))
    (fun g hg => by
      rw [MonoidHom.mem_ker, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
        QuotientGroup.eq_one_iff]
      exact ⟨g, hg, rfl⟩)

@[simp] theorem projOrthToProjSim_toProj (t : OGroup Q) :
    projOrthToProjSim Q (toProj Q t) = QuotientGroup.mk (orthToSim Q t) :=
  rfl

theorem projOrthToProjSim_injective : Function.Injective (projOrthToProjSim Q) := by
  rw [injective_iff_map_eq_one]
  intro a ha
  obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective (piGroup Q) a
  change projOrthToProjSim Q (toProj Q g) = 1 at ha
  rw [projOrthToProjSim_toProj, QuotientGroup.eq_one_iff] at ha
  obtain ⟨x, hx, hxg⟩ := ha
  have : x = g := orthToSim_injective hxg
  subst this
  exact (QuotientGroup.eq_one_iff x).mpr hx

@[expose] noncomputable def simAutAux (γ : simGroup Q) : MulAut (OGroup Q) where
  toFun t := simConj (Classical.choose_spec
    (show ∃ c : (ZMod 3)ˣ, IsSimilitude Q (γ : V ≃ₗ[ZMod 3] V) c from γ.2)) t
  invFun t := simConj (Classical.choose_spec
    (show ∃ c : (ZMod 3)ˣ, IsSimilitude Q ((γ⁻¹ : simGroup Q) : V ≃ₗ[ZMod 3] V) c from
      (γ⁻¹).2)) t
  left_inv t := by
    apply Subtype.ext
    simp only [coe_simConj, Subgroup.coe_inv]
    group
  right_inv t := by
    apply Subtype.ext
    simp only [coe_simConj, Subgroup.coe_inv]
    group
  map_mul' s t := simConj_mul _ s t

theorem coe_simAutAux (γ : simGroup Q) (t : OGroup Q) :
    ((simAutAux γ t : OGroup Q) : V ≃ₗ[ZMod 3] V) =
      (γ : V ≃ₗ[ZMod 3] V) * (t : V ≃ₗ[ZMod 3] V) * (γ : V ≃ₗ[ZMod 3] V)⁻¹ :=
  rfl

@[expose] noncomputable def simAct (Q : QuadraticForm (ZMod 3) V) :
    simGroup Q →* MulAut (OGroup Q) :=
  MonoidHom.mk' simAutAux (fun a b => by
    apply MulEquiv.ext
    intro t
    apply Subtype.ext
    change _ = ((simAutAux a (simAutAux b t) : OGroup Q) : V ≃ₗ[ZMod 3] V)
    rw [coe_simAutAux, coe_simAutAux, coe_simAutAux]
    simp only [Subgroup.coe_mul, mul_inv_rev]
    group)

theorem coe_simAct (γ : simGroup Q) (t : OGroup Q) :
    ((simAct Q γ t : OGroup Q) : V ≃ₗ[ZMod 3] V) =
      (γ : V ≃ₗ[ZMod 3] V) * (t : V ≃ₗ[ZMod 3] V) * (γ : V ≃ₗ[ZMod 3] V)⁻¹ :=
  rfl

theorem simAct_piOrth (γ : simGroup Q) : simAct Q γ (piOrth Q) = piOrth Q := by
  apply Subtype.ext
  rw [coe_simAct]
  have h := orthToSim_piOrth_comm γ
  have h' := congrArg (fun g : simGroup Q => (g : V ≃ₗ[ZMod 3] V)) h
  simp only [Subgroup.coe_mul, coe_orthToSim] at h'
  rw [h', mul_inv_cancel_right]

theorem simAct_orthToSim (t s : OGroup Q) :
    simAct Q (orthToSim Q t) s = t * s * t⁻¹ := by
  apply Subtype.ext
  rw [coe_simAct]
  rfl

theorem map_piGroup_simAct (γ : simGroup Q) :
    (piGroup Q).map (simAct Q γ).toMonoidHom = piGroup Q := by
  rw [piGroup, MonoidHom.map_zpowers]
  exact congrArg Subgroup.zpowers (simAct_piOrth γ)

@[expose] noncomputable def projActAux (γ : simGroup Q) : MulAut (ProjOrth Q) :=
  QuotientGroup.congr (piGroup Q) (piGroup Q) (simAct Q γ) (map_piGroup_simAct γ)

theorem projActAux_toProj (γ : simGroup Q) (t : OGroup Q) :
    projActAux γ (toProj Q t) = toProj Q (simAct Q γ t) :=
  rfl

theorem projActAux_mul (a b : simGroup Q) :
    projActAux (a * b) = projActAux a * projActAux b := by
  apply MulEquiv.ext
  intro y
  obtain ⟨t, rfl⟩ := QuotientGroup.mk'_surjective (piGroup Q) y
  change projActAux (a * b) (toProj Q t) = projActAux a (projActAux b (toProj Q t))
  rw [projActAux_toProj, projActAux_toProj, projActAux_toProj, map_mul]
  rfl

@[expose] noncomputable def projSimAct (Q : QuadraticForm (ZMod 3) V) :
    ProjSim Q →* MulAut (ProjOrth Q) :=
  QuotientGroup.lift (piSim Q) (MonoidHom.mk' projActAux projActAux_mul)
    (fun g hg => by
      rw [MonoidHom.mem_ker]
      apply MulEquiv.ext
      intro y
      obtain ⟨t, rfl⟩ := QuotientGroup.mk'_surjective (piGroup Q) y
      rcases mem_piSim_iff.mp hg with rfl | rfl
      · rfl
      · change projActAux (orthToSim Q (piOrth Q)) (toProj Q t) = toProj Q t
        rw [projActAux_toProj, simAct_orthToSim]
        have hc : t * piOrth Q = piOrth Q * t :=
          Subgroup.mem_center_iff.mp (piOrth_mem_center (Q := Q)) t
        have : piOrth Q * t * (piOrth Q)⁻¹ = t := by
          rw [← hc, mul_assoc, mul_inv_cancel, mul_one]
        rw [this])

theorem projSimAct_mk (γ : simGroup Q) (y : ProjOrth Q) :
    projSimAct Q (QuotientGroup.mk γ) y = projActAux γ y :=
  rfl

theorem projSimAct_projOrthToProjSim (x y : ProjOrth Q) :
    projSimAct Q (projOrthToProjSim Q x) y = x * y * x⁻¹ := by
  obtain ⟨s, rfl⟩ := QuotientGroup.mk'_surjective (piGroup Q) x
  obtain ⟨t, rfl⟩ := QuotientGroup.mk'_surjective (piGroup Q) y
  rw [projOrthToProjSim_toProj, projSimAct_mk, projActAux_toProj, simAct_orthToSim, map_mul,
    map_mul, map_inv]

@[expose] noncomputable def projSimActO (Q : QuadraticForm (ZMod 3) V) :
    ProjSim Q →* MulAut (OGroup Q) :=
  QuotientGroup.lift (piSim Q) (simAct Q)
    (fun g hg => by
      rw [MonoidHom.mem_ker]
      apply MulEquiv.ext
      intro t
      rcases mem_piSim_iff.mp hg with rfl | rfl
      · rfl
      · rw [simAct_orthToSim]
        have hc : t * piOrth Q = piOrth Q * t :=
          Subgroup.mem_center_iff.mp (piOrth_mem_center (Q := Q)) t
        have : piOrth Q * t * (piOrth Q)⁻¹ = t := by
          rw [← hc, mul_assoc, mul_inv_cancel, mul_one]
        exact this)

theorem projSimActO_mk (γ : simGroup Q) (t : OGroup Q) :
    projSimActO Q (QuotientGroup.mk γ) t = simAct Q γ t :=
  rfl

theorem toProj_projSimActO (x : ProjSim Q) (t : OGroup Q) :
    toProj Q (projSimActO Q x t) = projSimAct Q x (toProj Q t) := by
  obtain ⟨γ, rfl⟩ := QuotientGroup.mk_surjective x
  rfl

theorem projSimActO_projOrthToProjSim_toProj (s t : OGroup Q) :
    projSimActO Q (projOrthToProjSim Q (toProj Q s)) t = s * t * s⁻¹ := by
  rw [projOrthToProjSim_toProj, projSimActO_mk, simAct_orthToSim]

end CFSG.OddStandard.SmallF3.Omega
