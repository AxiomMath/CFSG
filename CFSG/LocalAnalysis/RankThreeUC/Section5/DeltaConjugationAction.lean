module

public import CFSG.LocalAnalysis.RankThreeUC.Section5.Context
public import CFSG.LocalAnalysis.RankThreeUC.QuadraticSetConjugationTransport.QuadraticSetConjugationTransport

public section

namespace CFSG.LocalAnalysis.RankThreeUC.Section5.DeltaConjugationAction

open CFSG.LocalAnalysis.RankThreeUC.Section5

variable {G : Type} [Group G] {V : Type} [AddCommGroup V] [Module (ZMod 2) V]

private theorem conj_map_normal {P : Subgroup G} (hP : P.Normal) (s : G) :
    P.map (MulAut.conj s).toMonoidHom = P := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact hP.conj_mem y hy s
  · intro hx
    refine ⟨s⁻¹ * x * s, ?_, ?_⟩
    · simpa using hP.conj_mem x hx s⁻¹
    · simp [MulAut.conj_apply, mul_assoc]

theorem map_mem {p : ℕ} {P : Subgroup G} (hP : P.Normal) (ρ : Representation (ZMod 2) G V)
    (g : G) {D : Subgroup G} (hD : D ∈ Delta p P ρ) :
    D.map (MulAut.conj g).toMonoidHom ∈ Delta p P ρ := by
  obtain ⟨hDP, hidx, hne⟩ := hD
  have hPn := conj_map_normal hP g
  refine ⟨?_, ?_, ?_⟩
  · calc D.map (MulAut.conj g).toMonoidHom ≤ P.map (MulAut.conj g).toMonoidHom :=
          Subgroup.map_mono hDP
      _ = P := hPn
  · have := Subgroup.relIndex_map_map_of_injective (f := (MulAut.conj g).toMonoidHom) D P
      (MulAut.conj g).injective
    rw [hPn] at this
    rw [this]; exact hidx
  · rw [QuadraticSetConjugationTransport.fixedSubmodule_map_conj]
    intro h
    apply hne
    have h2 := congrArg (Submodule.map (ρ g⁻¹)) h
    rw [Submodule.map_bot, ← Submodule.map_comp] at h2
    have : (ρ g⁻¹).comp (ρ g) = LinearMap.id := by
      ext v; simp [← Module.End.mul_apply, ← map_mul]
    rw [this] at h2
    simpa using h2

@[expose] def actPerm {p : ℕ} {P : Subgroup G} (hP : P.Normal) (ρ : Representation (ZMod 2) G V)
    (g : G) : Equiv.Perm (Delta p P ρ) where
  toFun D := ⟨D.1.map (MulAut.conj g).toMonoidHom, map_mem hP ρ g D.2⟩
  invFun D := ⟨D.1.map (MulAut.conj g⁻¹).toMonoidHom, map_mem hP ρ g⁻¹ D.2⟩
  left_inv D := by
    apply Subtype.ext
    simp only [Subgroup.map_map]
    have : (MulAut.conj g⁻¹).toMonoidHom.comp (MulAut.conj g).toMonoidHom = MonoidHom.id G := by
      ext x; simp [MulAut.conj_apply, mul_assoc]
    rw [this]; simp
  right_inv D := by
    apply Subtype.ext
    simp only [Subgroup.map_map]
    have : (MulAut.conj g).toMonoidHom.comp (MulAut.conj g⁻¹).toMonoidHom = MonoidHom.id G := by
      ext x; simp [MulAut.conj_apply, mul_assoc]
    rw [this]; simp

@[expose] def act {p : ℕ} {P : Subgroup G} (hP : P.Normal) (ρ : Representation (ZMod 2) G V) :
    G →* Equiv.Perm (Delta p P ρ) where
  toFun g := actPerm hP ρ g
  map_one' := by
    refine Equiv.ext fun D => Subtype.ext ?_
    show Subgroup.map (MulAut.conj (1 : G)).toMonoidHom D.1 = D.1
    have : (MulAut.conj (1 : G)).toMonoidHom = MonoidHom.id G := by
      ext x; simp
    rw [this]; simp
  map_mul' g h := by
    refine Equiv.ext fun D => Subtype.ext ?_
    show Subgroup.map (MulAut.conj (g * h)).toMonoidHom D.1 =
      Subgroup.map (MulAut.conj g).toMonoidHom (Subgroup.map (MulAut.conj h).toMonoidHom D.1)
    rw [Subgroup.map_map]
    have : (MulAut.conj (g * h)).toMonoidHom =
        (MulAut.conj g).toMonoidHom.comp (MulAut.conj h).toMonoidHom := by
      ext x; simp [MulAut.conj_apply, mul_assoc]
    rw [this]

theorem apply_eq {p : ℕ} {P : Subgroup G} (hP : P.Normal) (ρ : Representation (ZMod 2) G V)
    (g : G) (D : Delta p P ρ) :
    ((act hP ρ g D : Delta p P ρ) : Subgroup G) = D.1.map (MulAut.conj g).toMonoidHom := rfl

theorem fixed_map {p : ℕ} {P : Subgroup G} (hP : P.Normal) (ρ : Representation (ZMod 2) G V)
    (g : G) (D : Delta p P ρ) :
    (CFSG.LocalAnalysis.RankThreeUC.fixedSubmodule ρ D.1).map (ρ g) =
      CFSG.LocalAnalysis.RankThreeUC.fixedSubmodule ρ (act hP ρ g D).1 := by
  rw [apply_eq, QuadraticSetConjugationTransport.fixedSubmodule_map_conj]

end CFSG.LocalAnalysis.RankThreeUC.Section5.DeltaConjugationAction
