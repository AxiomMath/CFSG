module

public import CFSG.CGT.T75N.L29Classify
public import CFSG.CGT.T75N.L29Module

public section

namespace CFSG.CGT.T75N

open Matrix MatrixGroups

variable {F : Type} [Field F] {m : ℕ} {V : Type} [CommGroup V]

@[expose] def actStab (σ : SpecialLinearGroup (Fin (m + 2)) F →* MulAut V) (v : V) :
    Subgroup (SpecialLinearGroup (Fin (m + 2)) F) where
  carrier := {g | σ g v = v}
  one_mem' := by simp
  mul_mem' := fun {a b} ha hb => by
    have ha' : σ a v = v := ha
    have hb' : σ b v = v := hb
    show σ (a * b) v = v
    rw [map_mul, MulAut.mul_apply, hb', ha']
  inv_mem' := fun {a} ha => by
    have ha' : σ a v = v := ha
    show σ a⁻¹ v = v
    conv_lhs => rw [← ha']
    rw [← MulAut.mul_apply, ← map_mul, inv_mul_cancel, map_one, MulAut.one_apply]

theorem mem_actStab {σ : SpecialLinearGroup (Fin (m + 2)) F →* MulAut V} {v : V}
    {g : SpecialLinearGroup (Fin (m + 2)) F} : g ∈ actStab σ v ↔ σ g v = v := Iff.rfl

theorem act_inv_act (σ : SpecialLinearGroup (Fin (m + 2)) F →* MulAut V)
    (g : SpecialLinearGroup (Fin (m + 2)) F) (x : V) : σ g⁻¹ (σ g x) = x := by
  rw [← MulAut.mul_apply, ← map_mul, inv_mul_cancel, map_one, MulAut.one_apply]

theorem act_act_inv (σ : SpecialLinearGroup (Fin (m + 2)) F →* MulAut V)
    (g : SpecialLinearGroup (Fin (m + 2)) F) (x : V) : σ g (σ g⁻¹ x) = x := by
  rw [← MulAut.mul_apply, ← map_mul, mul_inv_cancel, map_one, MulAut.one_apply]

theorem mem_actStab_smul (σ : SpecialLinearGroup (Fin (m + 2)) F →* MulAut V) (v : V)
    (g h : SpecialLinearGroup (Fin (m + 2)) F) :
    h ∈ actStab σ (σ g v) ↔ g⁻¹ * h * g ∈ actStab σ v := by
  rw [mem_actStab, mem_actStab, map_mul, map_mul, MulAut.mul_apply, MulAut.mul_apply]
  constructor
  · intro hh
    rw [hh, act_inv_act]
  · intro hh
    have h2 := congrArg (σ g) hh
    rwa [act_act_inv] at h2

section Index

variable [Finite V]

theorem index_actStab (σ : SpecialLinearGroup (Fin (m + 2)) F →* MulAut V) (v : V) (hv : v ≠ 1)
    (htrans : ∀ w : V, w ≠ 1 → ∃ g, σ g v = w) :
    (actStab σ v).index = Nat.card V - 1 := by
  classical
  let _ : MulAction (SpecialLinearGroup (Fin (m + 2)) F) V := MulAction.compHom V σ
  have hstab : actStab σ v = MulAction.stabilizer (SpecialLinearGroup (Fin (m + 2)) F) v := by
    ext g
    rw [MulAction.mem_stabilizer_iff]
    rfl
  rw [hstab, MulAction.index_stabilizer]
  have horb : MulAction.orbit (SpecialLinearGroup (Fin (m + 2)) F) v = ({1} : Set V)ᶜ := by
    ext w
    rw [MulAction.mem_orbit_iff, Set.mem_compl_iff, Set.mem_singleton_iff]
    constructor
    · rintro ⟨g, rfl⟩ h
      apply hv
      have h' : σ g v = 1 := h
      have : σ g v = σ g 1 := by rw [h', map_one]
      exact (σ g).injective this
    · intro hw
      exact htrans w hw
  rw [horb, Set.ncard_compl, Set.ncard_singleton]

end Index

section Natural

variable [Finite F] [Finite V]

theorem transitive_natural [CharP F 2] (hV2 : ∀ v : V, v * v = 1)
    (hcard : Nat.card V = Nat.card F ^ (m + 2))
    (σ : SpecialLinearGroup (Fin (m + 2)) F →* MulAut V)
    (htrans : ∀ v w : V, v ≠ 1 → w ≠ 1 → ∃ g, σ g v = w) :
    ∃ α : SpecialLinearGroup (Fin (m + 2)) F →* SpecialLinearGroup (Fin (m + 2)) F,
      (∀ g, α (α g) = g) ∧ ∃ φ : V ≃* Multiplicative (Fin (m + 2) → F),
        ∀ (g : SpecialLinearGroup (Fin (m + 2)) F) (v : V), φ (σ g v) = Multiplicative.ofAdd
          ((α g : Matrix (Fin (m + 2)) (Fin (m + 2)) F) *ᵥ Multiplicative.toAdd (φ v)) := by
  classical
  have hq : 2 ≤ Nat.card F := by
    have := Finite.one_lt_card (α := F)
    omega
  have hqn : 2 ^ (m + 2) ≤ Nat.card F ^ (m + 2) := Nat.pow_le_pow_left hq _
  have h4 : 4 ≤ 2 ^ (m + 2) := by
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ (m + 2) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hnt : Nontrivial V := Finite.one_lt_card_iff_nontrivial.1 (by rw [hcard]; omega)
  obtain ⟨v₀, hv₀⟩ := exists_ne (1 : V)
  have hidx := index_actStab σ v₀ hv₀ (htrans v₀ · hv₀)
  rw [hcard] at hidx
  have hne : ∀ (g : SpecialLinearGroup (Fin (m + 2)) F) (w : V), w ≠ 1 → σ g w ≠ 1 := by
    intro g w hw h
    apply hw
    have : σ g w = σ g 1 := by rw [h, map_one]
    exact (σ g).injective this
  rcases classify_stab (actStab σ v₀) hidx with ⟨g, hg⟩ | ⟨g, hg⟩
  · have ha1 : σ g v₀ ≠ 1 := hne g v₀ hv₀
    have hstab : ∀ h : SpecialLinearGroup (Fin (m + 2)) F, σ h (σ g v₀) = σ g v₀ ↔
        (h : Matrix (Fin (m + 2)) (Fin (m + 2)) F) *ᵥ (Pi.single 0 1 : Fin (m + 2) → F) =
          Pi.single 0 1 := by
      intro h
      have h1 := mem_actStab_smul σ v₀ g h
      have h2 := hg (g⁻¹ * h * g)
      have h3 : g * (g⁻¹ * h * g) * g⁻¹ = h := by group
      rw [h3] at h2
      exact (h1.trans h2).trans mem_vecStab
    obtain ⟨φ, hφ⟩ := natural_module hV2 hcard σ (σ g v₀) ha1 hstab
      (fun w hw => htrans _ w ha1 hw)
    exact ⟨MonoidHom.id _, fun _ => rfl, φ, hφ⟩
  · have ha1 : σ g v₀ ≠ 1 := hne g v₀ hv₀
    have hstab : ∀ h : SpecialLinearGroup (Fin (m + 2)) F,
        (σ.comp (tauHom (m + 2) F)) h (σ g v₀) = σ g v₀ ↔
        (h : Matrix (Fin (m + 2)) (Fin (m + 2)) F) *ᵥ (Pi.single 0 1 : Fin (m + 2) → F) =
          Pi.single 0 1 := by
      intro h
      have h1 := mem_actStab_smul σ v₀ g (tauHom (m + 2) F h)
      have h2 := hg (g⁻¹ * tauHom (m + 2) F h * g)
      have h3 : g * (g⁻¹ * tauHom (m + 2) F h * g) * g⁻¹ = tauHom (m + 2) F h := by group
      rw [h3] at h2
      have h4 : tauHom (m + 2) F h ∈ (vecStab (m + 2) (Pi.single 0 1 : Fin (m + 2) → F)).map
          (tauHom (m + 2) F) ↔ h ∈ vecStab (m + 2) (Pi.single 0 1 : Fin (m + 2) → F) :=
        Subgroup.mem_map_iff_mem (tauHom_bijective (m + 2)).1
      exact ((h1.trans h2).trans h4).trans mem_vecStab
    have htrans' : ∀ w : V, w ≠ 1 → ∃ k : SpecialLinearGroup (Fin (m + 2)) F,
        (σ.comp (tauHom (m + 2) F)) k (σ g v₀) = w := by
      intro w hw
      obtain ⟨k, hk⟩ := htrans _ w ha1 hw
      refine ⟨tauHom (m + 2) F k, ?_⟩
      rw [MonoidHom.comp_apply, tauHom_tauHom]
      exact hk
    obtain ⟨φ, hφ⟩ := natural_module hV2 hcard (σ.comp (tauHom (m + 2) F)) (σ g v₀) ha1 hstab
      htrans'
    refine ⟨tauHom (m + 2) F, tauHom_tauHom (m + 2), φ, fun h v => ?_⟩
    have := hφ (tauHom (m + 2) F h) v
    rwa [MonoidHom.comp_apply, tauHom_tauHom] at this

omit [Finite F] [Finite V] in
theorem injective_of_natural (σ : SpecialLinearGroup (Fin (m + 2)) F →* MulAut V)
    (α : SpecialLinearGroup (Fin (m + 2)) F →* SpecialLinearGroup (Fin (m + 2)) F)
    (hα : ∀ g, α (α g) = g) (φ : V ≃* Multiplicative (Fin (m + 2) → F))
    (hφ : ∀ (g : SpecialLinearGroup (Fin (m + 2)) F) (v : V), φ (σ g v) = Multiplicative.ofAdd
      ((α g : Matrix (Fin (m + 2)) (Fin (m + 2)) F) *ᵥ Multiplicative.toAdd (φ v))) :
    Function.Injective σ := by
  rw [injective_iff_map_eq_one]
  intro g hg
  have hall : ∀ x : Fin (m + 2) → F,
      (α g : Matrix (Fin (m + 2)) (Fin (m + 2)) F) *ᵥ x = x := by
    intro x
    have h1 := hφ g (φ.symm (Multiplicative.ofAdd x))
    rw [hg, MulAut.one_apply, MulEquiv.apply_symm_apply] at h1
    simpa using h1.symm
  have hα1 : α g = 1 := by
    apply Subtype.ext
    ext i j
    have := congrFun (hall (Pi.single j 1)) i
    rw [mulVec_single_one] at this
    have h2 : (α g : Matrix (Fin (m + 2)) (Fin (m + 2)) F) i j =
        (Pi.single j 1 : Fin (m + 2) → F) i := this
    rw [SpecialLinearGroup.coe_one, h2]
    simp [Matrix.one_apply, Pi.single_apply]
  calc g = α (α g) := (hα g).symm
    _ = 1 := by rw [hα1, map_one]

end Natural

end CFSG.CGT.T75N
