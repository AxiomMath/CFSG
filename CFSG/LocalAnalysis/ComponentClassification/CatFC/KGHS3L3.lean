module

public import CFSG.LocalAnalysis.ComponentClassification.CatFC.KGHS3EigBase
public import CFSG.LocalAnalysis.ComponentClassification.CatFC.KGHS3BaseChange
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.LinearAlgebra.Eigenspace.Pi
public import Mathlib.RingTheory.Coalgebra.IsFrobenius
public import Mathlib.RingTheory.HopfAlgebra.Basic

public section

namespace CFSG.ComponentClassification.CatFC.KGHS3

open Module

section Singer3

variable {E V : Type*} [Field E] [AddCommGroup V] [Module E V]

def singer3Eig (ζ : E) (a b : Module.End E V) (p : Fin 3 × Fin 3) : Submodule E V :=
  a.eigenspace (ζ ^ (p.1 : ℕ)) ⊓ b.eigenspace (ζ ^ (p.2 : ℕ))

def singer3Shift (p : Fin 3 × Fin 3) : Fin 3 × Fin 3 := (p.2 - p.1, p.1)

theorem singer3Shift_iterate_eight : (singer3Shift^[8]) (1, 0) = (1, 0) := by
  decide

theorem singer3Shift_reach : ∀ p : Fin 3 × Fin 3, p ≠ (0, 0) →
    ∃ n : Fin 8, (singer3Shift^[(n : ℕ)]) (1, 0) = p := by
  decide

theorem mem_singer3Eig_iff {ζ : E} {a b : Module.End E V} {p : Fin 3 × Fin 3} {v : V} :
    v ∈ singer3Eig ζ a b p ↔ a v = ζ ^ (p.1 : ℕ) • v ∧ b v = ζ ^ (p.2 : ℕ) • v := by
  simp only [singer3Eig, Submodule.mem_inf, Module.End.mem_eigenspace_iff]

theorem singer3_pow_eq_one_of_mem {t : Module.End E V} {m : ℕ} (ht : t ^ m = 1) {μ : E}
    {v : V} (hv : v ∈ t.eigenspace μ) (hv0 : v ≠ 0) : μ ^ m = 1 := by
  have h1 := eigen_pow_apply_of_mem hv m
  rw [ht, Module.End.one_apply] at h1
  have h2 : (1 - μ ^ m) • v = 0 := by
    rw [sub_smul, one_smul, ← h1, sub_self]
  rcases smul_eq_zero.mp h2 with h3 | h3
  · exact (sub_eq_zero.mp h3).symm
  · exact absurd h3 hv0

theorem singer3_isFinitelySemisimple [FiniteDimensional E V] {t : Module.End E V} {m : ℕ}
    (hm : (m : E) ≠ 0) (ht : t ^ m = 1) : t.IsFinitelySemisimple := by
  have hsep : (Polynomial.X ^ m - Polynomial.C (1 : E)).Separable :=
    Polynomial.separable_X_pow_sub_C (1 : E) hm one_ne_zero
  exact (Module.End.isSemisimple_of_squarefree_aeval_eq_zero hsep.squarefree
    (by simp [ht])).isFinitelySemisimple

theorem singer3_pow_sub {ζ : E} (hζ : IsPrimitiveRoot ζ 3) (i j : Fin 3) :
    ζ ^ (j : ℕ) = ζ ^ (i : ℕ) * ζ ^ ((j - i : Fin 3) : ℕ) := by
  have key : ((i : ℕ) + ((j - i : Fin 3) : ℕ)) % 3 = (j : ℕ) := by
    revert i j
    decide
  calc ζ ^ (j : ℕ) = ζ ^ (((i : ℕ) + ((j - i : Fin 3) : ℕ)) % 3) := by rw [key]
    _ = ζ ^ ((i : ℕ) + ((j - i : Fin 3) : ℕ)) := (pow_eq_pow_mod _ hζ.pow_eq_one).symm
    _ = ζ ^ (i : ℕ) * ζ ^ ((j - i : Fin 3) : ℕ) := pow_add _ _ _

theorem singer3_index_injective {ζ : E} (hζ : IsPrimitiveRoot ζ 3) :
    Function.Injective fun p : Fin 3 × Fin 3 =>
      (![ζ ^ (p.1 : ℕ), ζ ^ (p.2 : ℕ)] : Fin 2 → E) := by
  rintro ⟨i, j⟩ ⟨i', j'⟩ h
  have h0 : ζ ^ (i : ℕ) = ζ ^ (i' : ℕ) := congrFun h 0
  have h1 : ζ ^ (j : ℕ) = ζ ^ (j' : ℕ) := congrFun h 1
  rw [Fin.ext (hζ.pow_inj i.isLt i'.isLt h0), Fin.ext (hζ.pow_inj j.isLt j'.isLt h1)]

theorem singer3_comm_fin_two {a b : Module.End E V} (hab : Commute a b) (i j : Fin 2) :
    Commute (![a, b] i) (![a, b] j) := by
  fin_cases i <;> fin_cases j
  · exact Commute.refl a
  · exact hab
  · exact hab.symm
  · exact Commute.refl b

theorem singer3_iInf_eq [FiniteDimensional E V] {a b : Module.End E V}
    (ha : a.IsFinitelySemisimple) (hb : b.IsFinitelySemisimple) (χ : Fin 2 → E) :
    (⨅ i, (![a, b] i).maxGenEigenspace (χ i)) = a.eigenspace (χ 0) ⊓ b.eigenspace (χ 1) := by
  ext v
  rw [Submodule.mem_iInf, Fin.forall_fin_two, Submodule.mem_inf]
  change v ∈ a.maxGenEigenspace (χ 0) ∧ v ∈ b.maxGenEigenspace (χ 1) ↔ _
  rw [ha.maxGenEigenspace_eq_eigenspace, hb.maxGenEigenspace_eq_eigenspace]

theorem singer3_joint_iSupIndep [FiniteDimensional E V] {a b : Module.End E V}
    (hab : Commute a b) (ha : a.IsFinitelySemisimple) (hb : b.IsFinitelySemisimple) :
    iSupIndep fun χ : Fin 2 → E => a.eigenspace (χ 0) ⊓ b.eigenspace (χ 1) := by
  have h := Module.End.independent_iInf_maxGenEigenspace_of_forall_mapsTo ![a, b]
    (fun i j μ => Module.End.mapsTo_maxGenEigenspace_of_comm (singer3_comm_fin_two hab j i) μ)
  have e : (fun χ : Fin 2 → E => a.eigenspace (χ 0) ⊓ b.eigenspace (χ 1)) =
      fun χ : Fin 2 → E => ⨅ i, (![a, b] i).maxGenEigenspace (χ i) :=
    funext fun χ => (singer3_iInf_eq ha hb χ).symm
  rw [e]
  exact h

section AlgClosed

variable [IsAlgClosed E] [FiniteDimensional E V]

theorem singer3_joint_iSup_eq_top {a b : Module.End E V} (hab : Commute a b)
    (ha : a.IsFinitelySemisimple) (hb : b.IsFinitelySemisimple) :
    ⨆ χ : Fin 2 → E, a.eigenspace (χ 0) ⊓ b.eigenspace (χ 1) = ⊤ := by
  have h := Module.End.iSup_iInf_maxGenEigenspace_eq_top_of_iSup_maxGenEigenspace_eq_top_of_commute
    ![a, b] (by intro i j _; exact singer3_comm_fin_two hab i j)
    (fun i => Module.End.iSup_maxGenEigenspace_eq_top (![a, b] i))
  simp only [singer3_iInf_eq ha hb] at h
  exact h

theorem singer3_iSupIndep {ζ : E} (hζ : IsPrimitiveRoot ζ 3) {a b : Module.End E V}
    (hab : Commute a b) (ha : a.IsFinitelySemisimple) (hb : b.IsFinitelySemisimple) :
    iSupIndep (singer3Eig ζ a b) := by
  have h := (singer3_joint_iSupIndep hab ha hb).comp (singer3_index_injective hζ)
  have e : (fun χ : Fin 2 → E => a.eigenspace (χ 0) ⊓ b.eigenspace (χ 1)) ∘
      (fun p : Fin 3 × Fin 3 => (![ζ ^ (p.1 : ℕ), ζ ^ (p.2 : ℕ)] : Fin 2 → E)) =
      singer3Eig ζ a b := by
    funext p
    rfl
  rw [e] at h
  exact h

theorem singer3_iSup_eq_top {ζ : E} (hζ : IsPrimitiveRoot ζ 3) {a b : Module.End E V}
    (hab : Commute a b) (ha : a.IsFinitelySemisimple) (hb : b.IsFinitelySemisimple)
    (ha3 : a ^ 3 = 1) (hb3 : b ^ 3 = 1) :
    ⨆ p, singer3Eig ζ a b p = ⊤ := by
  refine top_le_iff.mp ?_
  rw [← singer3_joint_iSup_eq_top hab ha hb]
  refine iSup_le fun χ => ?_
  by_cases hχ : a.eigenspace (χ 0) ⊓ b.eigenspace (χ 1) = ⊥
  · rw [hχ]
    exact bot_le
  · obtain ⟨v, hv, hv0⟩ := (Submodule.ne_bot_iff _).mp hχ
    obtain ⟨hva, hvb⟩ := Submodule.mem_inf.mp hv
    obtain ⟨i, hi, hiχ⟩ := hζ.eq_pow_of_pow_eq_one (singer3_pow_eq_one_of_mem ha3 hva hv0)
    obtain ⟨j, hj, hjχ⟩ := hζ.eq_pow_of_pow_eq_one (singer3_pow_eq_one_of_mem hb3 hvb hv0)
    refine le_trans ?_ (le_iSup (singer3Eig ζ a b) (⟨i, hi⟩, ⟨j, hj⟩))
    rw [← hiχ, ← hjχ]
    exact le_rfl

end AlgClosed

theorem singer3_sum_finrank [FiniteDimensional E V] {ι : Type*} [Fintype ι] [DecidableEq ι]
    {W : ι → Submodule E V} (hi : iSupIndep W) (hs : ⨆ i, W i = ⊤) :
    ∑ i, finrank E (W i) = finrank E V := by
  have hds : DirectSum.IsInternal W :=
    DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top hi hs
  have h := (LinearEquiv.ofBijective (DirectSum.coeLinearMap W) hds).finrank_eq
  rw [Module.finrank_directSum] at h
  exact h

theorem singer3_map {ζ : E} (hζ : IsPrimitiveRoot ζ 3) {a b g : Module.End E V}
    (hga : g * a = b * g) (hgb : g * b = a * b * g) (p : Fin 3 × Fin 3) :
    ∀ v ∈ singer3Eig ζ a b p, g v ∈ singer3Eig ζ a b (singer3Shift p) := by
  intro v hv
  rw [mem_singer3Eig_iff] at hv ⊢
  obtain ⟨hva, hvb⟩ := hv
  have hbgv : b (g v) = ζ ^ (p.1 : ℕ) • g v :=
    Module.End.mem_eigenspace_iff.mp
      (map_mem_eigenspace_of_mul_eq hga (Module.End.mem_eigenspace_iff.mpr hva))
  have hgbv : a (b (g v)) = g (b v) := by
    have h := LinearMap.congr_fun hgb v
    simp only [Module.End.mul_apply] at h
    exact h.symm
  have h1 : ζ ^ (p.1 : ℕ) • a (g v) = ζ ^ (p.2 : ℕ) • g v := by
    calc ζ ^ (p.1 : ℕ) • a (g v) = a (ζ ^ (p.1 : ℕ) • g v) := (map_smul a _ _).symm
      _ = a (b (g v)) := by rw [hbgv]
      _ = g (b v) := hgbv
      _ = g (ζ ^ (p.2 : ℕ) • v) := by rw [hvb]
      _ = ζ ^ (p.2 : ℕ) • g v := map_smul g _ _
  have hne : ζ ^ (p.1 : ℕ) ≠ 0 := pow_ne_zero _ (hζ.ne_zero (by norm_num))
  have hk := singer3_pow_sub hζ p.1 p.2
  have h2 : a (g v) = ζ ^ ((p.2 - p.1 : Fin 3) : ℕ) • g v := by
    refine smul_right_injective V hne ?_
    dsimp only
    rw [h1, smul_smul, ← hk]
  exact ⟨h2, hbgv⟩

theorem singer3_finrank_eq {ζ : E} (hζ : IsPrimitiveRoot ζ 3) [FiniteDimensional E V]
    {a b g : Module.End E V} (hga : g * a = b * g) (hgb : g * b = a * b * g)
    (hginj : Function.Injective g) (p : Fin 3 × Fin 3) (hp : p ≠ (0, 0)) :
    finrank E (singer3Eig ζ a b p) = finrank E (singer3Eig ζ a b (1, 0)) := by
  obtain ⟨n, rfl⟩ := singer3Shift_reach p hp
  exact finrank_iterate_eq_of_cycle (singer3Eig ζ a b) singer3Shift hginj
    (singer3_map hζ hga hgb) (1, 0) (N := 8) (by norm_num) singer3Shift_iterate_eight n

theorem singer3_exists_ne_bot {ζ : E} [FiniteDimensional E V] {a b : Module.End E V}
    (hspan : ⨆ p, singer3Eig ζ a b p = ⊤) (ha1 : a ≠ 1) :
    ∃ p : Fin 3 × Fin 3, p.1 ≠ 0 ∧ singer3Eig ζ a b p ≠ ⊥ := by
  by_contra h
  push_neg at h
  apply ha1
  have hle : (⨆ p, singer3Eig ζ a b p) ≤ a.eigenspace 1 := by
    refine iSup_le fun p => ?_
    by_cases hp : p.1 = 0
    · have h1 : ζ ^ (p.1 : ℕ) = 1 := by simp [hp]
      have hle' : singer3Eig ζ a b p ≤ a.eigenspace (ζ ^ (p.1 : ℕ)) := inf_le_left
      rwa [h1] at hle'
    · rw [h p hp]
      exact bot_le
  rw [hspan] at hle
  ext v
  have hv : v ∈ a.eigenspace (1 : E) := hle Submodule.mem_top
  rw [Module.End.mem_eigenspace_iff, one_smul] at hv
  rw [Module.End.one_apply]
  exact hv

end Singer3

theorem eight_le_finrank_of_singer3 {E V : Type*} [Field E] [IsAlgClosed E] [AddCommGroup V]
    [Module E V] [FiniteDimensional E V] (hE : ringChar E ≠ 3) (a b g : Module.End E V)
    (ha : a ^ 3 = 1) (hb : b ^ 3 = 1) (hab : a * b = b * a) (ha1 : a ≠ 1) (hg : IsUnit g)
    (hga : g * a = b * g) (hgb : g * b = a * b * g) : 8 ≤ finrank E V := by
  have hm3 : ((3 : ℕ) : E) ≠ 0 :=
    CharP.cast_ne_zero_of_ne_of_prime (R := E) (p := ringChar E) Nat.prime_three hE
  obtain ⟨ζ, hζ⟩ := exists_isPrimitiveRoot_of_isAlgClosed hm3
  have hab' : Commute a b := hab
  have ha' : a.IsFinitelySemisimple := singer3_isFinitelySemisimple hm3 ha
  have hb' : b.IsFinitelySemisimple := singer3_isFinitelySemisimple hm3 hb
  have hginj : Function.Injective g := ((Module.End.isUnit_iff _).mp hg).1
  have hspan := singer3_iSup_eq_top hζ hab' ha' hb' ha hb
  have hsum := singer3_sum_finrank (singer3_iSupIndep hζ hab' ha' hb') hspan
  have hd : 1 ≤ finrank E (singer3Eig ζ a b (1, 0)) := by
    obtain ⟨p0, hp0, hne⟩ := singer3_exists_ne_bot hspan ha1
    have hp0' : p0 ≠ (0, 0) := by
      intro h
      apply hp0
      rw [h]
    rw [← singer3_finrank_eq hζ hga hgb hginj p0 hp0']
    exact Submodule.one_le_finrank_iff.mpr hne
  have hsub : ∑ p ∈ Finset.univ.erase (0, 0), finrank E (singer3Eig ζ a b p) ≤
      ∑ p, finrank E (singer3Eig ζ a b p) :=
    Finset.sum_le_sum_of_subset (Finset.erase_subset _ _)
  have hconst : ∑ p ∈ Finset.univ.erase (0, 0), finrank E (singer3Eig ζ a b p) =
      8 * finrank E (singer3Eig ζ a b (1, 0)) := by
    rw [Finset.sum_const_nat (fun p hp => singer3_finrank_eq hζ hga hgb hginj p
      (Finset.ne_of_mem_erase hp)), Finset.card_erase_of_mem (Finset.mem_univ _),
      Finset.card_univ, Fintype.card_prod, Fintype.card_fin]
  omega

theorem eight_le_card_of_singer3 {F : Type} [Field F] (hF : ringChar F ≠ 3) {ι : Type}
    [Fintype ι] [DecidableEq ι] (a b g : Matrix ι ι F) (ha : a ^ 3 = 1) (hb : b ^ 3 = 1)
    (hab : a * b = b * a) (ha1 : a ≠ 1) (hg : IsUnit g) (hga : g * a = b * g)
    (hgb : g * b = a * b * g) : 8 ≤ Fintype.card ι := by
  obtain ⟨E, _, _, φ, hinj, hchar⟩ := exists_algClosed_ringHom F ι
  have hE : ringChar E ≠ 3 := by rw [hchar]; exact hF
  have key := eight_le_finrank_of_singer3 (E := E) (V := ι → E) hE (φ a) (φ b) (φ g)
    (by rw [← map_pow, ha, map_one]) (by rw [← map_pow, hb, map_one])
    (by rw [← map_mul φ a b, ← map_mul φ b a, hab])
    (fun h => ha1 (hinj (by rw [map_one]; exact h))) (hg.map φ)
    (by rw [← map_mul φ g a, ← map_mul φ b g, hga])
    (by rw [← map_mul φ g b, hgb, map_mul φ (a * b) g, map_mul φ a b])
  rwa [Module.finrank_fintype_fun_eq_card] at key

end CFSG.ComponentClassification.CatFC.KGHS3
