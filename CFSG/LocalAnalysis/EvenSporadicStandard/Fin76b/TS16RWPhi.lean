module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.TS16RWDef

public section

namespace CFSG.EvenSporadicStandard.Fin76b.W16

section Phi

variable {M : Type*} [Group M] {W : Subgroup M} {lab : Nat → M}

@[expose] def labF (h : TabLab W lab) (i : Fin 128) : ↥W := ⟨lab i, h.mem i i.2⟩

theorem labF_injective (h : TabLab W lab) : Function.Injective (labF h) := by
  intro i j hij
  apply Fin.ext
  exact h.inj i i.2 j j.2 (congrArg Subtype.val hij)

theorem labF_surjective (h : TabLab W lab) : Function.Surjective (labF h) := by
  intro w
  obtain ⟨c, hc, hcw⟩ := h.surj w.1 w.2
  exact ⟨⟨c, hc⟩, Subtype.ext hcw⟩

@[expose] noncomputable def labEquiv (h : TabLab W lab) : Fin 128 ≃ ↥W :=
  Equiv.ofBijective (labF h) ⟨labF_injective h, labF_surjective h⟩

theorem labF_mul (h : TabLab W lab) (hlt : ∀ a b : Nat, a < 128 → b < 128 → mulC a b < 128)
    (a b : Fin 128) : labF h (mulF a b) = labF h a * labF h b := by
  apply Subtype.ext
  have hab : mulC a b < 128 := hlt a b a.2 b.2
  have hv : ((mulF a b : Fin 128) : Nat) = mulC a b := Nat.mod_eq_of_lt hab
  show lab ((mulF a b : Fin 128) : Nat) = lab a * lab b
  rw [hv]
  exact h.mul a a.2 b b.2

@[expose] noncomputable def toPerm (h : TabLab W lab) : MulAut ↥W →* Equiv.Perm (Fin 128) where
  toFun α := (labEquiv h).symm.permCongr α.toEquiv
  map_one' := by
    ext i
    simp [Equiv.permCongr_apply]
  map_mul' α β := by
    ext i
    simp [Equiv.permCongr_apply]

theorem toPerm_apply (h : TabLab W lab) (α : MulAut ↥W) (i : Fin 128) :
    labF h (toPerm h α i) = α (labF h i) := by
  show labEquiv h (((labEquiv h).symm.permCongr α.toEquiv) i) = α (labEquiv h i)
  simp [Equiv.permCongr_apply]

theorem toPerm_injective (h : TabLab W lab) : Function.Injective (toPerm h) := by
  intro α β hαβ
  refine MulEquiv.ext fun w => ?_
  obtain ⟨i, rfl⟩ := labF_surjective h w
  have h1 := toPerm_apply h α i
  have h2 := toPerm_apply h β i
  rw [hαβ] at h1
  exact h1.symm.trans h2

theorem toPerm_mem_autC (h : TabLab W lab) (hlt : ∀ a b : Nat, a < 128 → b < 128 → mulC a b < 128)
    (α : MulAut ↥W) : toPerm h α ∈ AutC := by
  intro a b
  apply labF_injective h
  rw [toPerm_apply, labF_mul h hlt, map_mul, labF_mul h hlt, toPerm_apply, toPerm_apply]

theorem permCongr_apply_labF (h : TabLab W lab) (π : Equiv.Perm (Fin 128)) (i : Fin 128) :
    ((labEquiv h).permCongr π) (labF h i) = labF h (π i) := by
  have e : labF h i = labEquiv h i := rfl
  rw [e, Equiv.permCongr_apply, Equiv.symm_apply_apply]
  rfl

theorem permCongr_mul (h : TabLab W lab) (hlt : ∀ a b : Nat, a < 128 → b < 128 → mulC a b < 128)
    (π : Equiv.Perm (Fin 128)) (hπ : π ∈ AutC) (x y : ↥W) :
    ((labEquiv h).permCongr π) (x * y) =
      ((labEquiv h).permCongr π) x * ((labEquiv h).permCongr π) y := by
  obtain ⟨a, rfl⟩ := labF_surjective h x
  obtain ⟨b, rfl⟩ := labF_surjective h y
  rw [← labF_mul h hlt, permCongr_apply_labF, permCongr_apply_labF, permCongr_apply_labF, hπ a b,
    labF_mul h hlt]

@[expose] noncomputable def ofPerm (h : TabLab W lab)
    (hlt : ∀ a b : Nat, a < 128 → b < 128 → mulC a b < 128)
    (π : Equiv.Perm (Fin 128)) (hπ : π ∈ AutC) : MulAut ↥W :=
  { toEquiv := (labEquiv h).permCongr π
    map_mul' := permCongr_mul h hlt π hπ }

theorem ofPerm_apply (h : TabLab W lab) (hlt : ∀ a b : Nat, a < 128 → b < 128 → mulC a b < 128)
    (π : Equiv.Perm (Fin 128)) (hπ : π ∈ AutC) (i : Fin 128) :
    ofPerm h hlt π hπ (labF h i) = labF h (π i) :=
  permCongr_apply_labF h π i

theorem toPerm_ofPerm (h : TabLab W lab) (hlt : ∀ a b : Nat, a < 128 → b < 128 → mulC a b < 128)
    (π : Equiv.Perm (Fin 128)) (hπ : π ∈ AutC) : toPerm h (ofPerm h hlt π hπ) = π := by
  refine Equiv.ext fun i => labF_injective h ?_
  rw [toPerm_apply, ofPerm_apply]

theorem toPerm_range (h : TabLab W lab) (hlt : ∀ a b : Nat, a < 128 → b < 128 → mulC a b < 128) :
    (toPerm h).range = AutC := by
  ext π
  constructor
  · rintro ⟨α, rfl⟩
    exact toPerm_mem_autC h hlt α
  · intro hπ
    exact ⟨ofPerm h hlt π hπ, toPerm_ofPerm h hlt π hπ⟩

@[expose] noncomputable def phiEquiv (h : TabLab W lab)
    (hlt : ∀ a b : Nat, a < 128 → b < 128 → mulC a b < 128) : MulAut ↥W ≃* ↥AutC :=
  (MonoidHom.ofInjective (toPerm_injective h)).trans (MulEquiv.subgroupCongr (toPerm_range h hlt))

end Phi

end CFSG.EvenSporadicStandard.Fin76b.W16
