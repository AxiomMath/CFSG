module

public import CFSG.ClassicalInvolution.ModelFacts.ClassicalIsFundamentalOrthLift
public import CFSG.ClassicalInvolution.ModelFacts.ClassicalIsFundamentalLift

public section

namespace CFSG.ClassicalInvolution.Balance.StrongBalance.Orth

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.ModelFacts
open scoped commutatorElement

variable {K Γ : Type*} [Group K] [Group Γ] (θ : K →* Γ)

theorem le_of_map_le_of_isPerfect (hker : θ.ker ≤ Subgroup.center K) {L L' : Subgroup K}
    (hL : ⁅L, L⁆ = L) (hL' : ⁅L', L'⁆ = L') (h : L.map θ ≤ L'.map θ) : L ≤ L' := by
  calc L = ⁅L, L⁆ := hL.symm
    _ ≤ L' := by
      refine Subgroup.commutator_le.mpr fun x hx y hy => ?_
      obtain ⟨x', hx', hxx'⟩ := h (Subgroup.mem_map_of_mem θ hx)
      obtain ⟨y', hy', hyy'⟩ := h (Subgroup.mem_map_of_mem θ hy)
      have hcx : x'⁻¹ * x ∈ Subgroup.center K := hker (by
        rw [MonoidHom.mem_ker, map_mul, map_inv, hxx', inv_mul_cancel])
      have hcy : y'⁻¹ * y ∈ Subgroup.center K := hker (by
        rw [MonoidHom.mem_ker, map_mul, map_inv, hyy', inv_mul_cancel])
      have hx2 : x = x' * (x'⁻¹ * x) := by group
      have hy2 : y = y' * (y'⁻¹ * y) := by group
      rw [hx2, hy2, commutatorElement_mul_central hcx hcy]
      rw [← hL']
      exact Subgroup.commutator_mem_commutator hx' hy'

@[expose] def perfLift (C : Subgroup K) (N : Subgroup Γ) : Subgroup K :=
  ⁅N.comap θ ⊓ C, N.comap θ ⊓ C⁆

variable {θ}

theorem perfLift_le (C : Subgroup K) (N : Subgroup Γ) : perfLift θ C N ≤ C :=
  (Subgroup.commutator_le_of_le le_rfl le_rfl).trans inf_le_right

theorem perfLift_le_comap (C : Subgroup K) (N : Subgroup Γ) : perfLift θ C N ≤ N.comap θ :=
  (Subgroup.commutator_le_of_le le_rfl le_rfl).trans inf_le_left

theorem map_perfLift_aux {C : Subgroup K} {N : Subgroup Γ} (hN : N ≤ C.map θ) :
    (N.comap θ ⊓ C).map θ = N := by
  refine le_antisymm ?_ ?_
  · rintro _ ⟨c, hc, rfl⟩
    exact hc.1
  · intro n hn
    obtain ⟨c, hc, rfl⟩ := hN hn
    exact ⟨c, ⟨hn, hc⟩, rfl⟩

theorem map_perfLift {C : Subgroup K} {N : Subgroup Γ} (hN : N ≤ C.map θ)
    (hNp : ⁅N, N⁆ = N) : (perfLift θ C N).map θ = N := by
  unfold perfLift
  rw [Subgroup.map_commutator, map_perfLift_aux hN, hNp]

theorem perfLift_perfect (hker : θ.ker ≤ Subgroup.center K) {C : Subgroup K} {N : Subgroup Γ}
    (hN : N ≤ C.map θ) (hNp : ⁅N, N⁆ = N) :
    ⁅perfLift θ C N, perfLift θ C N⁆ = perfLift θ C N := by
  refine le_antisymm (Subgroup.commutator_le_of_le le_rfl le_rfl) ?_
  set R : Subgroup K := N.comap θ ⊓ C with hR
  have hmap : (perfLift θ C N).map θ = N := map_perfLift hN hNp
  unfold perfLift
  refine Subgroup.commutator_le.mpr fun x hx y hy => ?_
  have hdec : ∀ r ∈ R, ∃ p ∈ ⁅R, R⁆, p⁻¹ * r ∈ Subgroup.center K := by
    intro r hr
    have : θ r ∈ (⁅R, R⁆).map θ := by
      have h1 : θ r ∈ N := hr.1
      rw [← hmap] at h1
      exact h1
    obtain ⟨p, hp, hpr⟩ := this
    refine ⟨p, hp, hker ?_⟩
    rw [MonoidHom.mem_ker, map_mul, map_inv, hpr, inv_mul_cancel]
  obtain ⟨p₁, hp₁, hc₁⟩ := hdec x hx
  obtain ⟨p₂, hp₂, hc₂⟩ := hdec y hy
  have hx2 : x = p₁ * (p₁⁻¹ * x) := by group
  have hy2 : y = p₂ * (p₂⁻¹ * y) := by group
  rw [hx2, hy2, commutatorElement_mul_central hc₁ hc₂]
  exact Subgroup.commutator_mem_commutator hp₁ hp₂


theorem perfLift_eq_of_perfect (hker : θ.ker ≤ Subgroup.center K) {C : Subgroup K} {N : Subgroup Γ}
    (hN : N ≤ C.map θ) (hNp : ⁅N, N⁆ = N) {L : Subgroup K}
    (hL : ⁅L, L⁆ = L) (hLN : L.map θ = N) : L = perfLift θ C N :=
  eq_of_map_eq_of_isPerfect θ hker hL (perfLift_perfect hker hN hNp)
    (hLN.trans (map_perfLift hN hNp).symm)

theorem perfLift_mono (hker : θ.ker ≤ Subgroup.center K) {C : Subgroup K} {N N' : Subgroup Γ}
    (hN : N ≤ C.map θ) (hNp : ⁅N, N⁆ = N)
    (hN' : N' ≤ C.map θ) (hN'p : ⁅N', N'⁆ = N')
    (h : N ≤ N') : perfLift θ C N ≤ perfLift θ C N' :=
  le_of_map_le_of_isPerfect θ hker (perfLift_perfect hker hN hNp) (perfLift_perfect hker hN' hN'p)
    (by rw [map_perfLift hN hNp, map_perfLift hN' hN'p]; exact h)

theorem map_conj_perfLift_eq (hker : θ.ker ≤ Subgroup.center K) {C : Subgroup K} {N : Subgroup Γ}
    (hN : N ≤ C.map θ) (hNp : ⁅N, N⁆ = N) {c : K}
    (hc : N.map (MulAut.conj (θ c)).toMonoidHom = N) :
    (perfLift θ C N).map (MulAut.conj c).toMonoidHom = perfLift θ C N := by
  have hperf : ⁅(perfLift θ C N).map (MulAut.conj c).toMonoidHom,
      (perfLift θ C N).map (MulAut.conj c).toMonoidHom⁆ =
        (perfLift θ C N).map (MulAut.conj c).toMonoidHom := by
    rw [← Subgroup.map_commutator, perfLift_perfect hker hN hNp]
  refine perfLift_eq_of_perfect hker hN hNp hperf ?_ |>.symm ▸ rfl
  rw [Subgroup.map_map]
  have : θ.comp (MulAut.conj c).toMonoidHom = (MulAut.conj (θ c)).toMonoidHom.comp θ := by
    ext x
    simp
  rw [this, ← Subgroup.map_map, map_perfLift hN hNp, hc]

theorem isSubnormal_perfLift (hker : θ.ker ≤ Subgroup.center K) {C : Subgroup K} {N N' : Subgroup Γ}
    (hN : N ≤ C.map θ) (hNp : ⁅N, N⁆ = N)
    (hN' : N' ≤ C.map θ) (hN'p : ⁅N', N'⁆ = N')
    (hle : N' ≤ N) (hnormal : ∀ g ∈ N, ∀ n ∈ N', g * n * g⁻¹ ∈ N')
    (hstable : ∀ c ∈ C,
      N.map (MulAut.conj (θ c)).toMonoidHom = N) :
    IsSubnormal (perfLift θ C N') C := by
  have h1 : perfLift θ C N' ≤ perfLift θ C N := perfLift_mono hker hN' hN'p hN hNp hle
  have h2 : perfLift θ C N ≤ C := perfLift_le C N
  refine isSubnormal_trans (M := perfLift θ C N) ?_ ?_
  · refine isSubnormal_of_normal_subgroupOf h1 ?_
    rw [Subgroup.normal_subgroupOf_iff h1]
    intro ρ r hρ hr
    have hrN : θ r ∈ N := perfLift_le_comap C N hr
    have hc : N'.map (MulAut.conj (θ r)).toMonoidHom = N' := by
      refine le_antisymm ?_ ?_
      · rintro _ ⟨n, hn, rfl⟩
        exact hnormal _ hrN n hn
      · intro n hn
        refine ⟨(θ r)⁻¹ * n * θ r, ?_, by
          show θ r * ((θ r)⁻¹ * n * θ r) * (θ r)⁻¹ = n
          group⟩
        have := hnormal (θ r)⁻¹ (N.inv_mem hrN) n hn
        simpa using this
    have := map_conj_perfLift_eq hker hN' hN'p hc
    rw [← this]
    exact ⟨ρ, hρ, rfl⟩
  · refine isSubnormal_of_normal_subgroupOf h2 ?_
    rw [Subgroup.normal_subgroupOf_iff h2]
    intro ρ c hρ hc
    have := map_conj_perfLift_eq hker hN hNp (c := c) (hstable c hc)
    rw [← this]
    exact ⟨ρ, hρ, rfl⟩

end CFSG.ClassicalInvolution.Balance.StrongBalance.Orth
