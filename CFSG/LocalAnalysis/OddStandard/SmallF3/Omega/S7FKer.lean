module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.S7FFrameLem
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec12L121PL

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup

variable {G : Type} [Group G]

@[expose] def s7fU (B : Subgroup G) (u : Fin 5 → G) : Subgroup G :=
  Subgroup.closure ((B : Set G) ∪ {z | ∃ i j, z = u i * u j})

theorem le_s7fU (B : Subgroup G) (u : Fin 5 → G) : B ≤ s7fU B u :=
  fun _ hb => Subgroup.subset_closure (Or.inl hb)

theorem mul_mem_s7fU (B : Subgroup G) (u : Fin 5 → G) (i j : Fin 5) : u i * u j ∈ s7fU B u :=
  Subgroup.subset_closure (Or.inr ⟨i, j, rfl⟩)

namespace S7FFrame

variable {t : G} {B E H : Subgroup G} {φ : (Fin 5 → ZMod 2) → G}

theorem s7fU_le (F : S7FFrame t B E H φ) {u : Fin 5 → G} (hu : ∀ i, u i ∈ E) :
    s7fU B u ≤ E := by
  rw [s7fU, Subgroup.closure_le]
  rintro x (hx | ⟨i, j, rfl⟩)
  · exact F.B_le hx
  · exact E.mul_mem (hu i) (hu j)

theorem s7fU_ker (F : S7FFrame t B E H φ) {u : Fin 5 → G} (hu : ∀ i, u i ∈ E)
    (hκu : ∀ i, s7fKap t (u i) = φ (wvec i)) :
    ∀ x ∈ s7fU B u, s7fKap t x = 1 → x ∈ B := by
  classical
  have h0ev : IsEvenVec (0 : Fin 5 → ZMod 2) := by simp [IsEvenVec]
  have hφ0 : φ 0 = 1 := by
    have h00 : φ 0 = φ 0 * φ 0 := by simpa using F.perm.1 0 0 h0ev h0ev
    exact mul_eq_left.mp h00.symm
  have hBex : ∀ b : G, b ∈ B → ∃ v : Fin 5 → ZMod 2, IsEvenVec v ∧ φ v = b :=
    fun b hb => F.mem_B_iff.mp hb
  choose! ξ hξ using hBex
  have hφmem : ∀ {v : Fin 5 → ZMod 2}, IsEvenVec v → φ v ∈ B :=
    fun hv => F.mem_B_iff.mpr ⟨_, hv, rfl⟩
  have hξφ : ∀ {v : Fin 5 → ZMod 2}, IsEvenVec v → ξ (φ v) = v := fun {v} hv =>
    F.perm.2.1 _ _ (hξ _ (hφmem hv)).1 hv (hξ _ (hφmem hv)).2
  have heven_add : ∀ {v w : Fin 5 → ZMod 2}, IsEvenVec v → IsEvenVec w →
      IsEvenVec (v + w) := by
    intro v w hv hw
    unfold IsEvenVec at hv hw ⊢
    simp only [Pi.add_apply, Finset.sum_add_distrib, hv, hw, add_zero]
  have hξ1 : ξ 1 = 0 := by simpa [hφ0] using hξφ h0ev
  have hξ_mul : ∀ {b b' : G}, b ∈ B → b' ∈ B → ξ (b * b') = ξ b + ξ b' := by
    intro b b' hb hb'
    have hmem : b * b' ∈ B := B.mul_mem hb hb'
    have hsum : IsEvenVec (ξ b + ξ b') := heven_add (hξ b hb).1 (hξ b' hb').1
    have hφs : φ (ξ b + ξ b') = b * b' := by
      rw [F.perm.1 (ξ b) (ξ b') (hξ b hb).1 (hξ b' hb').1, (hξ b hb).2, (hξ b' hb').2]
    exact F.perm.2.1 (ξ (b * b')) (ξ b + ξ b') (hξ (b * b') hmem).1 hsum
      (by rw [(hξ (b * b') hmem).2, hφs])
  have hκ1 : s7fKap t (1 : G) = 1 := by unfold s7fKap; group
  let ψ : ↥E →* Multiplicative (Fin 5 → ZMod 2) :=
    { toFun := fun e => Multiplicative.ofAdd (ξ (s7fKap t (e : G)))
      map_one' := by
        change Multiplicative.ofAdd (ξ (s7fKap t (1 : G))) = 1
        rw [hκ1, hξ1]
        rfl
      map_mul' := fun e e' => by
        change Multiplicative.ofAdd (ξ (s7fKap t ((e : G) * (e' : G)))) =
          Multiplicative.ofAdd (ξ (s7fKap t (e : G))) *
            Multiplicative.ofAdd (ξ (s7fKap t (e' : G)))
        rw [F.kap_mul e.2 e'.2, hξ_mul (F.kap_mem _ e.2) (F.kap_mem _ e'.2)]
        rfl }
  let N : Subgroup ↥E := B.subgroupOf E
  have hNmem : ∀ n : ↥E, n ∈ N ↔ (n : G) ∈ B := fun n => Subgroup.mem_subgroupOf
  haveI hNnormal : N.Normal := by
    refine ⟨fun n hn g => ?_⟩
    rw [hNmem] at hn ⊢
    have hconj : (g : G) * (n : G) * (g : G)⁻¹ = (n : G) := by
      rw [F.comm_B _ g.2 _ hn]
      group
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    rwa [hconj]
  have hNker : N ≤ ψ.ker := by
    intro n hn
    change Multiplicative.ofAdd (ξ (s7fKap t (n : G))) = 1
    rw [F.kap_B ((hNmem n).1 hn), hξ1]
    rfl
  let ℓ : (↥E ⧸ N) → Fin 5 → ZMod 2 :=
    fun x => Multiplicative.toAdd (QuotientGroup.lift N ψ hNker x)
  have hℓ : ∀ x y : ↥E ⧸ N, ℓ (x * y) = ℓ x + ℓ y := by
    intro x y
    change Multiplicative.toAdd (QuotientGroup.lift N ψ hNker (x * y)) =
      Multiplicative.toAdd (QuotientGroup.lift N ψ hNker x) +
        Multiplicative.toAdd (QuotientGroup.lift N ψ hNker y)
    rw [map_mul, toAdd_mul]
  let q : Fin 5 → ↥E ⧸ N := fun i => QuotientGroup.mk (⟨u i, hu i⟩ : ↥E)
  have hq : ∀ i, ℓ (q i) = wvec i := by
    intro i
    change Multiplicative.toAdd
      (QuotientGroup.lift N ψ hNker (QuotientGroup.mk (⟨u i, hu i⟩ : ↥E))) = wvec i
    rw [QuotientGroup.lift_mk]
    change ξ (s7fKap t (u i)) = wvec i
    rw [hκu i]
    exact hξφ (wvec_even i)
  have hsq : ∀ x : ↥E ⧸ N, x * x = 1 := by
    intro x
    refine QuotientGroup.induction_on x (fun a => ?_)
    rw [← QuotientGroup.mk_mul, QuotientGroup.eq_one_iff]
    exact (hNmem (a * a)).2 (F.sq_mem _ a.2)
  have hcomm : ∀ x y : ↥E ⧸ N, x * y = y * x := by
    intro x y
    refine QuotientGroup.induction_on x (fun a => ?_)
    refine QuotientGroup.induction_on y (fun b => ?_)
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq]
    refine (hNmem _).2 ?_
    simpa [Subgroup.coe_mul, Subgroup.coe_inv] using F.comm_mod a.2 b.2
  let H' : Subgroup (↥E ⧸ N) := Subgroup.closure {z | ∃ i j, z = q i * q j}
  let K : Subgroup G := (H'.comap (QuotientGroup.mk' N)).map E.subtype
  have hUK : s7fU B u ≤ K := by
    rw [s7fU, Subgroup.closure_le]
    rintro y (hy | ⟨i, j, rfl⟩)
    · refine Subgroup.mem_map.mpr ⟨⟨y, F.B_le hy⟩, Subgroup.mem_comap.mpr ?_, rfl⟩
      rw [QuotientGroup.mk'_apply, (QuotientGroup.eq_one_iff _).mpr ((hNmem _).2 hy)]
      exact H'.one_mem
    · refine Subgroup.mem_map.mpr ⟨⟨u i, hu i⟩ * ⟨u j, hu j⟩, Subgroup.mem_comap.mpr ?_, rfl⟩
      rw [map_mul]
      exact Subgroup.subset_closure ⟨i, j, rfl⟩
  intro x hx hκx
  obtain ⟨y, hyH, rfl⟩ := Subgroup.mem_map.mp (hUK hx)
  have hℓy : ℓ (QuotientGroup.mk y) = 0 := by
    change Multiplicative.toAdd (QuotientGroup.lift N ψ hNker (QuotientGroup.mk y)) = 0
    rw [QuotientGroup.lift_mk]
    change ξ (s7fKap t (y : G)) = 0
    have hκy : s7fKap t (y : G) = 1 := hκx
    rw [hκy, hξ1]
  have h1 := sec121_closure_pairs hcomm hsq q ℓ hℓ hq (QuotientGroup.mk y) hyH hℓy
  exact (hNmem y).1 ((QuotientGroup.eq_one_iff _).mp h1)

end S7FFrame

end CFSG.OddStandard.SmallF3.Omega
