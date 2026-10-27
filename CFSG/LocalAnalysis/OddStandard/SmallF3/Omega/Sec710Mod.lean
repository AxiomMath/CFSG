module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec710Perm

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup
open scoped CharTwo

variable {G : Type} [Group G]

private lemma sec710_isEvenVec_add {n : ℕ} {v w : Fin n → ZMod 2} (hv : IsEvenVec v)
    (hw : IsEvenVec w) : IsEvenVec (v + w) := by
  unfold IsEvenVec at *
  simp only [Pi.add_apply]
  rw [Finset.sum_add_distrib, hv, hw, add_zero]

theorem sec710_map_zero {φ : (Fin 5 → ZMod 2) → G} {B H : Subgroup G}
    (h : IsPermModuleVia IsEvenVec φ B H ⊤) : φ 0 = 1 := by
  have hz : IsEvenVec (0 : Fin 5 → ZMod 2) := by unfold IsEvenVec; simp
  have hmul : φ 0 * φ 0 = φ 0 := by
    simpa using (h.1 0 0 hz hz).symm
  exact mul_eq_right.mp hmul

theorem sec710_wt4_mem {φ : (Fin 5 → ZMod 2) → G} {B H : Subgroup G}
    (h : IsPermModuleVia IsEvenVec φ B H ⊤) (i : Fin 5) : φ (wt4 i) ∈ B := by
  exact (h.2.2.1 (φ (wt4 i))).mpr ⟨wt4 i, isEvenVec_wt4 i, rfl⟩

theorem sec710_wt4_inj {φ : (Fin 5 → ZMod 2) → G} {B H : Subgroup G}
    (h : IsPermModuleVia IsEvenVec φ B H ⊤) {i j : Fin 5} (hij : φ (wt4 i) = φ (wt4 j)) :
    i = j := by
  exact wt4_injective (h.2.1 (wt4 i) (wt4 j) (isEvenVec_wt4 i) (isEvenVec_wt4 j) hij)

theorem sec710_closure_wt4 {φ : (Fin 5 → ZMod 2) → G} {B H : Subgroup G}
    (h : IsPermModuleVia IsEvenVec φ B H ⊤) :
    B = Subgroup.closure (Set.range fun i : Fin 5 => φ (wt4 i)) := by
  apply le_antisymm
  · intro x hx
    obtain ⟨v, hv, rfl⟩ := (h.2.2.1 x).mp hx
    have hv_mem : v ∈ AddSubgroup.closure (Set.range wt4) :=
      sec710_evenVec_mem_closure_wt4 hv
    exact (AddSubgroup.closure_induction
      (p := fun u _ => IsEvenVec u ∧
        φ u ∈ Subgroup.closure (Set.range fun i : Fin 5 => φ (wt4 i)))
      (fun u hu => by
        obtain ⟨i, rfl⟩ := hu
        exact ⟨isEvenVec_wt4 i, Subgroup.subset_closure ⟨i, rfl⟩⟩)
      ⟨by unfold IsEvenVec; simp, by
        rw [sec710_map_zero h]; exact Subgroup.one_mem _⟩
      (fun a b _ _ iha ihb => ⟨sec710_isEvenVec_add iha.1 ihb.1, by
        rw [h.1 a b iha.1 ihb.1]; exact Subgroup.mul_mem _ iha.2 ihb.2⟩)
      (fun a _ iha => by rw [CharTwo.neg_eq a]; exact iha)
      hv_mem).2
  · apply (Subgroup.closure_le _).mpr
    rintro x ⟨i, rfl⟩
    exact sec710_wt4_mem h i

theorem sec710_equiv_E16 {φ : (Fin 5 → ZMod 2) → G} {B H : Subgroup G}
    (h : IsPermModuleVia IsEvenVec φ B H ⊤) : Nonempty (↥B ≃* E16) := by
  classical
  let v : ↥B → (Fin 5 → ZMod 2) := fun b => Classical.choose ((h.2.2.1 (b : G)).mp b.2)
  have hv_spec : ∀ b : ↥B, IsEvenVec (v b) ∧ φ (v b) = (b : G) := fun b =>
    Classical.choose_spec ((h.2.2.1 (b : G)).mp b.2)
  let ψ : ↥B →* E16 := MonoidHom.mk' (fun b => toE16 (v b)) (fun b c => by
    have hb := (hv_spec b).1
    have hc := (hv_spec c).1
    have hbc : IsEvenVec (v b + v c) := sec710_isEvenVec_add hb hc
    have hφ : φ (v b + v c) = (b * c : ↥B) := by
      rw [h.1 (v b) (v c) hb hc, (hv_spec b).2, (hv_spec c).2]
      rfl
    have heq : v (b * c) = v b + v c :=
      h.2.1 (v (b * c)) (v b + v c) (hv_spec (b * c)).1 hbc (by
        rw [(hv_spec (b * c)).2, hφ])
    show toE16 (v (b * c)) = toE16 (v b) * toE16 (v c)
    rw [heq, toE16_add])
  have hψ_inj : Function.Injective (fun b : ↥B => toE16 (v b)) := by
    intro b c hbc
    apply Subtype.ext
    have heq : v b = v c := toE16_injOn_even (hv_spec b).1 (hv_spec c).1 hbc
    rw [← (hv_spec b).2, ← (hv_spec c).2, heq]
  have hψ_surj : Function.Surjective (fun b : ↥B => toE16 (v b)) := by
    intro u
    obtain ⟨v', hv', hv'u⟩ := exists_even_toE16 u
    let b : ↥B := ⟨φ v', (h.2.2.1 (φ v')).mpr ⟨v', hv', rfl⟩⟩
    refine ⟨b, ?_⟩
    have hvb : v b = v' := by
      apply h.2.1 (v b) v'
      · exact (hv_spec b).1
      · exact hv'
      · rw [(hv_spec b).2]
    show toE16 (v b) = u
    rw [hvb, hv'u]
  exact ⟨MulEquiv.ofBijective ψ ⟨hψ_inj, hψ_surj⟩⟩

theorem sec710_exists_rho {φ : (Fin 5 → ZMod 2) → G} {B N M : Subgroup G}
    (h : IsPermModuleVia IsEvenVec φ B N ⊤)
    (hM : ∀ m ∈ M, ∀ i : Fin 5, ∃ j : Fin 5, m * φ (wt4 i) * m⁻¹ = φ (wt4 j)) :
    ∃ ρ : ↥M →* Equiv.Perm (Fin 5), ∀ (m : ↥M) (i : Fin 5),
      (m : G) * φ (wt4 i) * (m : G)⁻¹ = φ (wt4 (ρ m i)) := by
  classical
  let f : ↥M → Fin 5 → Fin 5 := fun m i => Classical.choose (hM (m : G) m.2 i)
  have hf_spec : ∀ (m : ↥M) (i : Fin 5),
      (m : G) * φ (wt4 i) * (m : G)⁻¹ = φ (wt4 (f m i)) := fun m i =>
    Classical.choose_spec (hM (m : G) m.2 i)
  have hf_inj : ∀ m : ↥M, Function.Injective (f m) := by
    intro m i j hij
    apply sec710_wt4_inj h
    have h1 : (m : G) * φ (wt4 i) * (m : G)⁻¹ = φ (wt4 (f m j)) := by
      rw [hf_spec m i, hij]
    have h2 : (m : G) * φ (wt4 j) * (m : G)⁻¹ = φ (wt4 (f m j)) := hf_spec m j
    have h3 : (m : G) * φ (wt4 i) * (m : G)⁻¹
        = (m : G) * φ (wt4 j) * (m : G)⁻¹ := by rw [h1, h2]
    exact mul_left_cancel (mul_right_cancel h3)
  have hf_bij : ∀ m : ↥M, Function.Bijective (f m) := fun m =>
    (Finite.injective_iff_bijective).mp (hf_inj m)
  have hmul : ∀ (m m' : ↥M) (i : Fin 5), f (m * m') i = f m (f m' i) := by
    intro m m' i
    apply sec710_wt4_inj h
    have h1 : ((m * m' : ↥M) : G) * φ (wt4 i) * (((m * m' : ↥M) : G))⁻¹
        = φ (wt4 (f m (f m' i))) := by
      calc ((m * m' : ↥M) : G) * φ (wt4 i) * (((m * m' : ↥M) : G))⁻¹
          = (m : G) * ((m' : G) * φ (wt4 i) * (m' : G)⁻¹) * (m : G)⁻¹ := by
            rw [Subgroup.coe_mul, mul_inv_rev]; group
        _ = (m : G) * φ (wt4 (f m' i)) * (m : G)⁻¹ := by rw [hf_spec m' i]
        _ = φ (wt4 (f m (f m' i))) := hf_spec m (f m' i)
    have h2 := hf_spec (m * m') i
    rw [← h2]
    exact h1
  let ρ : ↥M →* Equiv.Perm (Fin 5) :=
    MonoidHom.mk' (fun m => Equiv.ofBijective (f m) (hf_bij m)) (fun m m' => by
      apply Equiv.ext
      intro i
      rw [Equiv.Perm.mul_apply]
      simp only [Equiv.coe_ofBijective]
      exact hmul m m' i)
  refine ⟨ρ, fun m i => ?_⟩
  show (m : G) * φ (wt4 i) * (m : G)⁻¹ = φ (wt4 (f m i))
  exact hf_spec m i

theorem sec710_rho_eq_one_iff {φ : (Fin 5 → ZMod 2) → G} {B N M : Subgroup G}
    (h : IsPermModuleVia IsEvenVec φ B N ⊤) {ρ : ↥M →* Equiv.Perm (Fin 5)}
    (hρ : ∀ (m : ↥M) (i : Fin 5), (m : G) * φ (wt4 i) * (m : G)⁻¹ = φ (wt4 (ρ m i)))
    (m : ↥M) : ρ m = 1 ↔ ∀ b ∈ B, (m : G) * b = b * (m : G) := by
  constructor
  · intro h1
    have hcomm : ∀ i : Fin 5, (m : G) * φ (wt4 i) = φ (wt4 i) * (m : G) := by
      intro i
      have hi : ρ m i = i := by rw [h1]; rfl
      have hh := hρ m i
      rw [hi] at hh
      calc (m : G) * φ (wt4 i)
          = (m : G) * φ (wt4 i) * (m : G)⁻¹ * (m : G) := by group
        _ = φ (wt4 i) * (m : G) := by rw [hh]
    intro b hb
    rw [sec710_closure_wt4 h] at hb
    have hC : Subgroup.closure (Set.range fun i : Fin 5 => φ (wt4 i)) ≤
        Subgroup.centralizer ({(m : G)} : Set G) := by
      apply (Subgroup.closure_le _).mpr
      rintro x ⟨i, rfl⟩
      exact Subgroup.mem_centralizer_singleton_iff.mpr (hcomm i).symm
    exact (Subgroup.mem_centralizer_singleton_iff.mp (hC hb)).symm
  · intro hb
    apply Equiv.ext
    intro i
    apply sec710_wt4_inj h
    have hcomm := hb (φ (wt4 i)) (sec710_wt4_mem h i)
    have hh : (m : G) * φ (wt4 i) * (m : G)⁻¹ = φ (wt4 i) := by
      rw [hcomm]; group
    rw [← hρ m i]
    exact hh

theorem sec710_rho_surj {φ : (Fin 5 → ZMod 2) → G} {B N M : Subgroup G}
    (h : IsPermModuleVia IsEvenVec φ B N ⊤) {ρ : ↥M →* Equiv.Perm (Fin 5)}
    (hρ : ∀ (m : ↥M) (i : Fin 5), (m : G) * φ (wt4 i) * (m : G)⁻¹ = φ (wt4 (ρ m i)))
    (hNM : N ≤ M) (σ : Equiv.Perm (Fin 5)) : ∃ n : ↥M, (n : G) ∈ N ∧ ρ n = σ := by
  obtain ⟨n, hnN, hnσ⟩ := h.2.2.2.2 σ (Subgroup.mem_top σ)
  refine ⟨⟨n, hNM hnN⟩, hnN, ?_⟩
  apply Equiv.ext
  intro i
  apply sec710_wt4_inj h
  have h1 : (↑(⟨n, hNM hnN⟩ : ↥M) : G) * φ (wt4 i) * (↑(⟨n, hNM hnN⟩ : ↥M) : G)⁻¹
      = φ (wt4 (σ i)) := by
    have hh := hnσ (wt4 i) (isEvenVec_wt4 i)
    rwa [permVec_wt4] at hh
  have h2 := hρ ⟨n, hNM hnN⟩ i
  rw [← h2]
  exact h1

end CFSG.OddStandard.SmallF3.Omega
