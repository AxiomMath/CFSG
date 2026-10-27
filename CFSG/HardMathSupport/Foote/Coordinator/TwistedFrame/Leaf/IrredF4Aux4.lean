module

public import CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.Detect.F4.LA

public noncomputable section

namespace CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame.IrredF4Aux

open CFSG.Blueprint CFSG.Blueprint.Chevalley
open CFSG.HardMathSupport.Foote.Coordinator.SplitFrame CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.DetectF4

theorem actFun_single_smul {L : Type} [Field L]
    (a1 a2 : (Fin Tag.F4.rank → ℤ) → (Fin Tag.F4.rank → ℤ) → ℤ) (γ μ : Fin Tag.F4.rank → ℤ)
    (t c : L) :
    actFun a1 a2 γ t (Pi.single μ c : (Fin Tag.F4.rank → ℤ) → L) =
      Pi.single μ c + t • (Pi.single (μ + γ) ((a1 γ μ : L) * c) : (Fin Tag.F4.rank → ℤ) → L) +
        t ^ 2 • (Pi.single (μ + 2 • γ) ((a2 γ μ : L) * c) : (Fin Tag.F4.rank → ℤ) → L) := by
  funext ν
  have e1 := Words.coeff_single_shift (K := L) (a1 γ) γ μ ν c
  have e2 := Words.coeff_single_shift (K := L) (a2 γ) (2 • γ) μ ν c
  simp only [actFun, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  linear_combination t * e1 + t ^ 2 * e2

theorem step_mem {L : Type} [Field L] (h2 : (2 : L) ≠ 0) (hL : ∃ t : L, t ≠ 0 ∧ t ≠ 1)
    {a1 a2 : (Fin Tag.F4.rank → ℤ) → (Fin Tag.F4.rank → ℤ) → ℤ} (h1 : Adm1 a1)
    (N : Submodule L ((Fin Tag.F4.rank → ℤ) → L))
    (hstab : ∀ γ ∈ f4ShortList, ∀ t : L, ∀ v ∈ N, actFun a1 a2 γ t v ∈ N)
    {γ ν : Fin Tag.F4.rank → ℤ} (hγ : γ ∈ f4ShortList) (hν : ν ∈ mRoots)
    (hs : ν + γ ∈ rootFinset .F4)
    (hN : ∀ c : L, (Pi.single ν c : (Fin Tag.F4.rank → ℤ) → L) ∈ N) (c : L) :
    (Pi.single (ν + γ) c : (Fin Tag.F4.rank → ℤ) → L) ∈ N := by
  obtain ⟨t₀, ht0, ht1⟩ := hL
  have ha : (a1 γ ν : L) ≠ 0 :=
    Words.a1_ne_zero_odd h2 h1 hγ (List.mem_append_left _ hν)
      ((Words.mem_rootFinset_F4 _).1 (by rwa [add_comm]))
  have hX : ∀ t d : L,
      t • (Pi.single (ν + γ) ((a1 γ ν : L) * d) : (Fin Tag.F4.rank → ℤ) → L) +
        t ^ 2 • (Pi.single (ν + 2 • γ) ((a2 γ ν : L) * d) : (Fin Tag.F4.rank → ℤ) → L) ∈ N := by
    intro t d
    have h := N.sub_mem (hstab γ hγ t _ (hN d)) (hN d)
    rwa [actFun_single_smul, add_assoc, add_sub_cancel_left] at h
  have hw : ∀ d : L, (t₀ ^ 2 - t₀) •
      (Pi.single (ν + γ) ((a1 γ ν : L) * d) : (Fin Tag.F4.rank → ℤ) → L) ∈ N := by
    intro d
    have h := N.sub_mem (N.smul_mem (t₀ ^ 2) (hX 1 d)) (hX t₀ d)
    convert h using 1
    module
  have hne : t₀ ^ 2 - t₀ ≠ 0 := by
    have : t₀ ^ 2 - t₀ = t₀ * (t₀ - 1) := by ring
    rw [this]
    exact mul_ne_zero ht0 (sub_ne_zero.2 ht1)
  have h3 := hw ((a1 γ ν : L)⁻¹ * c)
  rw [mul_inv_cancel_left₀ ha] at h3
  have h4 := N.smul_mem (t₀ ^ 2 - t₀)⁻¹ h3
  rwa [smul_smul, inv_mul_cancel₀ hne, one_smul] at h4

@[expose] def nbrs (ν : Fin Tag.F4.rank → ℤ) : List (Fin Tag.F4.rank → ℤ) :=
  (f4ShortList.map fun γ => ν + γ).filter fun x => decide (x ∈ rootFinset .F4)

@[expose] def reach : ℕ → (Fin Tag.F4.rank → ℤ) → List (Fin Tag.F4.rank → ℤ)
  | 0, ν => [ν]
  | k + 1, ν => (reach k ν).flatMap fun x => x :: nbrs x

theorem mem_nbrs {ν x : Fin Tag.F4.rank → ℤ} :
    x ∈ nbrs ν ↔ (∃ γ ∈ f4ShortList, ν + γ = x) ∧ x ∈ rootFinset .F4 := by
  simp only [nbrs, List.mem_filter, List.mem_map, decide_eq_true_eq]

theorem reach_good {P : (Fin Tag.F4.rank → ℤ) → Prop} (hP : ∀ x, P x → ∀ y ∈ nbrs x, P y) :
    ∀ (k : ℕ) (ν : Fin Tag.F4.rank → ℤ), P ν → ∀ x ∈ reach k ν, P x
  | 0, ν, h, x, hx => by
    rw [reach, List.mem_singleton] at hx
    subst hx
    exact h
  | k + 1, ν, h, x, hx => by
    rw [reach, List.mem_flatMap] at hx
    obtain ⟨y, hy, hxy⟩ := hx
    have hy' := reach_good hP k ν h y hy
    rcases List.mem_cons.1 hxy with rfl | hxy
    · exact hy'
    · exact hP y hy' x hxy

theorem component_reach :
    ∀ ν ∈ mRoots, ∀ ν' ∈ mRoots, ν' 1 = ν 1 → ν' ∈ reach 2 ν := by decide +kernel

theorem mRoots_one : ∀ ν ∈ mRoots, ν 1 = 1 ∨ ν 1 = 2 := by decide +kernel

theorem irreducible_core {L : Type} [Field L] (h2 : (2 : L) ≠ 0) (hL : ∃ t : L, t ≠ 0 ∧ t ≠ 1)
    {a1 a2 : (Fin Tag.F4.rank → ℤ) → (Fin Tag.F4.rank → ℤ) → ℤ} (h1 : Adm1 a1) (h2' : Adm2 a2)
    (N : Submodule L ((Fin Tag.F4.rank → ℤ) → L))
    (hsupp : ∀ v ∈ N, ∀ ν, v ν ≠ 0 → ν ∈ mRoots)
    (hstab : ∀ γ ∈ f4ShortList, ∀ t : L, ∀ v ∈ N, actFun a1 a2 γ t v ∈ N)
    (S : ((Fin Tag.F4.rank → ℤ) → L) → ((Fin Tag.F4.rank → ℤ) → L)) (hS : ∀ v ∈ N, S v ∈ N)
    (hSe : ∀ ν ∈ mRoots, ∀ c : L, c ≠ 0 → ∃ ν' ∈ mRoots, ν' 1 ≠ ν 1 ∧
      ∃ c' : L, c' ≠ 0 ∧ S (Pi.single ν c) = Pi.single ν' c')
    (hne : N ≠ ⊥) : ∀ ν ∈ mRoots, ∀ c : L, (Pi.single ν c : (Fin Tag.F4.rank → ℤ) → L) ∈ N := by
  have hscale : ∀ (ν : Fin Tag.F4.rank → ℤ) (e : L), e ≠ 0 →
      (Pi.single ν e : (Fin Tag.F4.rank → ℤ) → L) ∈ N →
      ∀ c : L, (Pi.single ν c : (Fin Tag.F4.rank → ℤ) → L) ∈ N := by
    intro ν e he hm c
    have h := N.smul_mem (c * e⁻¹) hm
    rwa [← Pi.single_smul', smul_eq_mul, mul_assoc, inv_mul_cancel₀ he, mul_one] at h
  have hcomp : ∀ ν₀ ∈ mRoots, (∀ c : L, (Pi.single ν₀ c : (Fin Tag.F4.rank → ℤ) → L) ∈ N) →
      ∀ ν ∈ mRoots, ν 1 = ν₀ 1 →
        ∀ c : L, (Pi.single ν c : (Fin Tag.F4.rank → ℤ) → L) ∈ N := by
    intro ν₀ hν₀ hN ν hν h1ν c
    have hP : ∀ x, (x ∈ mRoots ∧ ∀ c : L, (Pi.single x c : (Fin Tag.F4.rank → ℤ) → L) ∈ N) →
        ∀ y ∈ nbrs x,
          (y ∈ mRoots ∧ ∀ c : L, (Pi.single y c : (Fin Tag.F4.rank → ℤ) → L) ∈ N) := by
      rintro x ⟨hx, hxN⟩ y hy
      obtain ⟨⟨γ, hγ, rfl⟩, hyr⟩ := mem_nbrs.1 hy
      refine ⟨?_, fun c => step_mem h2 hL h1 N hstab hγ hx hyr hxN c⟩
      have := (add_mem_mRoots γ hγ x hx).1 (by rwa [add_comm] at hyr)
      rwa [add_comm] at this
    exact (reach_good hP 2 ν₀ ⟨hν₀, hN⟩ ν (component_reach ν₀ hν₀ ν hν h1ν)).2 c
  obtain ⟨v, hvN, hv0⟩ := (Submodule.ne_bot_iff N).1 hne
  obtain ⟨ν₀, hν₀, e, he, hmem⟩ := LA_core hL h1 h2' (N : Set ((Fin Tag.F4.rank → ℤ) → L))
    (fun c hc c' hc' => N.add_mem hc hc') (fun c hc => N.neg_mem hc) hsupp hstab ⟨v, hvN, hv0⟩
  have hN₀ := hscale ν₀ e he hmem
  obtain ⟨ν', hν', hne1, c', hc', hSν⟩ := hSe ν₀ hν₀ 1 one_ne_zero
  have hmem' : (Pi.single ν' c' : (Fin Tag.F4.rank → ℤ) → L) ∈ N := by
    rw [← hSν]
    exact hS _ (hN₀ 1)
  have hN' := hscale ν' c' hc' hmem'
  intro ν hν c
  by_cases hν1 : ν 1 = ν₀ 1
  · exact hcomp ν₀ hν₀ hN₀ ν hν hν1 c
  · have hν1' : ν 1 = ν' 1 := by
      have ha := mRoots_one ν hν
      have hb := mRoots_one ν₀ hν₀
      have hc := mRoots_one ν' hν'
      omega
    exact hcomp ν' hν' hN' ν hν hν1' c

end CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame.IrredF4Aux
