module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec10L107bAux
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixIII.Basic

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup

variable {G : Type} [Group G]

structure Sec11Perm (A M : Subgroup G) (Alt : Subgroup (Equiv.Perm (Fin 6)))
    (φ : (Fin 6 → ZMod 2) → G) : Prop where
  mem : ∀ v, φ v ∈ A
  mul : ∀ v w, φ (v + w) = φ v * φ w
  ker : ∀ v, φ v = 1 ↔ v = 0 ∨ v = fun _ => 1
  surj : ∀ a ∈ A, ∃ v, φ v = a
  act : ∀ m ∈ M, ∃ σ ∈ Alt, ∀ v, m * φ v * m⁻¹ = φ (permVec σ v)
  act_surj : ∀ σ ∈ Alt, ∃ m ∈ M, ∀ v, m * φ v * m⁻¹ = φ (permVec σ v)

theorem sec11_permVec_single (σ : Equiv.Perm (Fin 6)) (i : Fin 6) :
    permVec σ (Pi.single i (1 : ZMod 2)) = Pi.single (σ i) (1 : ZMod 2) := by
  funext j
  unfold permVec
  simp only [Function.comp_apply, Pi.single_apply]
  by_cases h : j = σ i
  · have h' : σ.symm j = i := (Equiv.symm_apply_eq σ).mpr h
    simp [h, h']
  · have h' : σ.symm j ≠ i := fun hh => h ((Equiv.symm_apply_eq σ).mp hh)
    simp [h, h']

theorem sec11_permVec_add (σ : Equiv.Perm (Fin 6)) (v w : Fin 6 → ZMod 2) :
    permVec σ (v + w) = permVec σ v + permVec σ w := by
  funext i
  simp only [permVec, Function.comp_apply, Pi.add_apply]

theorem sec11_permVec_eq_zero_iff (σ : Equiv.Perm (Fin 6)) (v : Fin 6 → ZMod 2) :
    permVec σ v = 0 ↔ v = 0 := by
  constructor
  · intro h
    funext i
    have := congrFun h (σ i)
    simpa [permVec] using this
  · rintro rfl
    rfl

theorem sec11_permVec_eq_one_iff (σ : Equiv.Perm (Fin 6)) (v : Fin 6 → ZMod 2) :
    permVec σ v = (fun _ => 1) ↔ v = fun _ => 1 := by
  constructor
  · intro h
    funext i
    have := congrFun h (σ i)
    simpa [permVec] using this
  · rintro rfl
    rfl

theorem sec11_vec_add_self (v : Fin 6 → ZMod 2) : v + v = 0 := by
  funext i
  simp only [Pi.add_apply, Pi.zero_apply]
  exact CharTwo.add_self_eq_zero _

theorem sec11_single_add_cases :
    ∀ i j : Fin 6, (Pi.single i (1 : ZMod 2) + Pi.single j (1 : ZMod 2) = (0 : Fin 6 → ZMod 2) ∨
      Pi.single i (1 : ZMod 2) + Pi.single j (1 : ZMod 2) = fun _ => (1 : ZMod 2)) → i = j := by
  decide +kernel

namespace Sec11Perm

variable {A M : Subgroup G} {Alt : Subgroup (Equiv.Perm (Fin 6))} {φ : (Fin 6 → ZMod 2) → G}

theorem map_zero (h : Sec11Perm A M Alt φ) : φ 0 = 1 := (h.ker 0).2 (Or.inl rfl)

theorem sq (h : Sec11Perm A M Alt φ) (v : Fin 6 → ZMod 2) : φ v * φ v = 1 := by
  rw [← h.mul, sec11_vec_add_self, h.map_zero]

theorem inv_eq (h : Sec11Perm A M Alt φ) (v : Fin 6 → ZMod 2) : (φ v)⁻¹ = φ v :=
  inv_eq_of_mul_eq_one_right (h.sq v)

theorem comm (h : Sec11Perm A M Alt φ) (v w : Fin 6 → ZMod 2) : φ v * φ w = φ w * φ v := by
  rw [← h.mul, ← h.mul, add_comm]

theorem eq_iff (h : Sec11Perm A M Alt φ) (v w : Fin 6 → ZMod 2) :
    φ v = φ w ↔ v + w = 0 ∨ v + w = fun _ => 1 := by
  rw [← h.ker, h.mul]
  constructor
  · intro hvw
    rw [hvw, h.sq]
  · intro h1
    have h2 : φ v = (φ w)⁻¹ := eq_inv_of_mul_eq_one_left h1
    rw [h2, h.inv_eq]

theorem single_inj (h : Sec11Perm A M Alt φ) {i j : Fin 6}
    (hij : φ (Pi.single i 1) = φ (Pi.single j 1)) : i = j := by
  exact sec11_single_add_cases i j ((h.eq_iff _ _).1 hij)

theorem perm_unique (h : Sec11Perm A M Alt φ) {σ σ' : Equiv.Perm (Fin 6)}
    (hσ : ∀ v, φ (permVec σ v) = φ (permVec σ' v)) : σ = σ' := by
  ext i
  have h1 := hσ (Pi.single i 1)
  rw [sec11_permVec_single, sec11_permVec_single] at h1
  exact congrArg Fin.val (h.single_inj h1)

open Classical in
noncomputable def rho (h : Sec11Perm A M Alt φ) (m : G) : Equiv.Perm (Fin 6) :=
  if hm : m ∈ M then Classical.choose (h.act m hm) else 1

theorem rho_spec (h : Sec11Perm A M Alt φ) {m : G} (hm : m ∈ M) :
    h.rho m ∈ Alt ∧ ∀ v, m * φ v * m⁻¹ = φ (permVec (h.rho m) v) := by
  unfold rho
  rw [dif_pos hm]
  exact Classical.choose_spec (h.act m hm)

theorem rho_mem (h : Sec11Perm A M Alt φ) {m : G} (hm : m ∈ M) : h.rho m ∈ Alt :=
  (h.rho_spec hm).1

theorem conj_apply (h : Sec11Perm A M Alt φ) {m : G} (hm : m ∈ M) (v : Fin 6 → ZMod 2) :
    m * φ v * m⁻¹ = φ (permVec (h.rho m) v) :=
  (h.rho_spec hm).2 v

theorem rho_eq (h : Sec11Perm A M Alt φ) {m : G} (hm : m ∈ M) (σ : Equiv.Perm (Fin 6))
    (hσ : ∀ v, m * φ v * m⁻¹ = φ (permVec σ v)) : h.rho m = σ :=
  h.perm_unique fun v => by rw [← h.conj_apply hm, hσ]

theorem rho_mul (h : Sec11Perm A M Alt φ) {m n : G} (hm : m ∈ M) (hn : n ∈ M) :
    h.rho (m * n) = h.rho m * h.rho n := by
  refine h.rho_eq (M.mul_mem hm hn) _ fun v => ?_
  calc m * n * φ v * (m * n)⁻¹ = m * (n * φ v * n⁻¹) * m⁻¹ := by group
    _ = φ (permVec (h.rho m * h.rho n) v) := by
      rw [h.conj_apply hn, h.conj_apply hm]
      rfl

theorem rho_one (h : Sec11Perm A M Alt φ) : h.rho 1 = 1 :=
  h.rho_eq M.one_mem 1 fun v => by simp [permVec_one]

@[expose] noncomputable def rhoHom (h : Sec11Perm A M Alt φ) : ↥M →* Equiv.Perm (Fin 6) where
  toFun m := h.rho m
  map_one' := h.rho_one
  map_mul' m n := h.rho_mul m.2 n.2

theorem rhoHom_apply (h : Sec11Perm A M Alt φ) (m : ↥M) : h.rhoHom m = h.rho m := rfl

theorem range_rhoHom (h : Sec11Perm A M Alt φ) : h.rhoHom.range = Alt := by
  ext σ
  constructor
  · rintro ⟨m, rfl⟩
    exact h.rho_mem m.2
  · intro hσ
    obtain ⟨m, hm, hact⟩ := h.act_surj σ hσ
    exact ⟨⟨m, hm⟩, h.rho_eq hm σ hact⟩

theorem rho_eq_one_iff (h : Sec11Perm A M Alt φ) {m : G} (hm : m ∈ M) :
    h.rho m = 1 ↔ ∀ a ∈ A, m * a * m⁻¹ = a := by
  constructor
  · intro h1 a ha
    obtain ⟨v, rfl⟩ := h.surj a ha
    rw [h.conj_apply hm, h1, permVec_one]
  · intro hc
    exact h.rho_eq hm 1 fun v => by rw [hc _ (h.mem v), permVec_one]

theorem conj_single (h : Sec11Perm A M Alt φ) {m : G} (hm : m ∈ M) (k : Fin 6) :
    m * φ (Pi.single k 1) * m⁻¹ = φ (Pi.single (h.rho m k) 1) := by
  rw [h.conj_apply hm, sec11_permVec_single]

end Sec11Perm

end CFSG.OddStandard.SmallF3.Omega
