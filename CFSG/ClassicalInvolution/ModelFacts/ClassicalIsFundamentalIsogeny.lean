module

public import CFSG.LieType.Steinberg.Isogeny.E6
public import CFSG.LieType.Steinberg.Isogeny.E7
public import CFSG.ClassicalInvolution.ModelFacts.ClassicalIsFundamentalOrthLift

public section

namespace CFSG.ClassicalInvolution.ModelFacts

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.LieType.Steinberg.Minuscule CFSG.LieType.Steinberg.Isogeny CFSG.LieType.Universal

section Lift

variable {K C : Type*} [Group K] [Group C]

theorem eq_map_conj_of_map_eq_central (θ : K →* C) (hθ : Function.Surjective θ)
    (hker : θ.ker ≤ Subgroup.center K) {R : Subgroup K} (hR : ⁅R, R⁆ = R) {L : Subgroup K}
    (hL : ⁅L, L⁆ = L) {c : C}
    (h : L.map θ = (R.map θ).map (MulAut.conj c).toMonoidHom) :
    ∃ g : K, θ g = c ∧ L = R.map (MulAut.conj g).toMonoidHom := by
  obtain ⟨g, hg⟩ := hθ c
  refine ⟨g, hg, ?_⟩
  have hLc : ⁅R.map (MulAut.conj g).toMonoidHom, R.map (MulAut.conj g).toMonoidHom⁆ =
      R.map (MulAut.conj g).toMonoidHom := by
    rw [← Subgroup.map_commutator, hR]
  have hmap : L.map θ = (R.map (MulAut.conj g).toMonoidHom).map θ := by
    rw [h, Subgroup.map_map, Subgroup.map_map]
    congr 1
    ext x
    simp [map_mul, map_inv, hg]
  exact eq_of_map_eq_of_isPerfect θ hker hL hLc hmap

end Lift

section RootGroupImage

variable (k : Type) [Field k] [Finite k]

theorem map_e6Isogeny_rootGroup {γ : Fin (Tag.rank .E6) → ℤ} (hγ : IsRoot .E6 γ) :
    (e6Data_valid.rootGroup k γ).map (e6Isogeny k) =
      rootGroup (rootOperatorFamily .E6) k γ := by
  ext g
  constructor
  · rintro ⟨x, hx, rfl⟩
    obtain ⟨c, rfl⟩ := (e6Data_valid.mem_rootGroup k).1 hx
    rw [e6Isogeny_xm k hγ c, yPar]
    exact xPar_mem hγ _
  · intro hg
    obtain ⟨c, rfl⟩ := (mem_rootGroup_iff hγ g).1 hg
    refine ⟨e6Data_valid.xm k γ
      ((relSignOr (rootOperatorFamily .E6) e6AdjData_valid γ : k) * c),
      e6Data_valid.xm_mem_rootGroup k _ _, ?_⟩
    rw [e6Isogeny_xm k hγ, yPar, ← mul_assoc, relSignOr_mul_self, one_mul]

theorem map_e7Isogeny_rootGroup {γ : Fin (Tag.rank .E7) → ℤ} (hγ : IsRoot .E7 γ) :
    (e7Data_valid.rootGroup k γ).map (e7Isogeny k) =
      rootGroup (rootOperatorFamily .E7) k γ := by
  have hsq : (e7Eps γ : k) * (e7Eps γ : k) = 1 := by
    rcases e7Eps_eq_one_or γ with h | h <;> rw [h] <;> simp
  ext g
  constructor
  · rintro ⟨x, hx, rfl⟩
    obtain ⟨c, rfl⟩ := (e7Data_valid.mem_rootGroup k).1 hx
    rw [e7Isogeny_xm k γ c]
    exact xPar_mem hγ _
  · intro hg
    obtain ⟨c, rfl⟩ := (mem_rootGroup_iff hγ g).1 hg
    refine ⟨e7Data_valid.xm k γ ((e7Eps γ : k) * c), e7Data_valid.xm_mem_rootGroup k _ _, ?_⟩
    rw [e7Isogeny_xm k, ← mul_assoc, hsq, one_mul]

end RootGroupImage

section TwoInvolutions

variable {τ : Tag} {D : MinData τ} (hV : D.Valid) (k : Type*) [Field k]

theorem exists_two_involutions_minGroup (h2 : (2 : k) ≠ 0) {i j : Fin τ.rank} (hij : i ≠ j) :
    ∃ y₁ y₂ : hV.minGroup k, orderOf y₁ = 2 ∧ orderOf y₂ = 2 ∧ y₁ ≠ y₂ := by
  have hinv : ∀ l : Fin τ.rank, orderOf (hV.hm k l (-1)) = 2 := by
    intro l
    have hsq : hV.hm k l (-1) ^ 2 = 1 := by
      rw [pow_two, ← hV.hm_mul, neg_mul_neg, one_mul, hV.hm_one]
    refine orderOf_eq_prime hsq ?_
    intro h1
    obtain ⟨a, ha⟩ := hV.exists_wt_eq_one l
    have h3 := congrArg (fun g => hV.endo k g) h1
    simp only [MinData.Valid.endo_hm, MinData.Valid.endo_one] at h3
    have h4 := congrArg (fun f : Module.End k (Fin D.d →₀ k) => f (Finsupp.single a 1) a) h3
    simp only [D.hDiag_single, ha, Finsupp.smul_apply, Finsupp.single_eq_same, smul_eq_mul,
      Module.End.one_apply] at h4
    apply h2
    have : ((-1 : kˣ) ^ (1 : ℤ) : kˣ) = -1 := by simp
    rw [this, Units.val_neg, Units.val_one] at h4
    linear_combination -h4
  refine ⟨hV.hm k i (-1), hV.hm k j (-1), hinv i, hinv j, fun h => ?_⟩
  have hdisj := (hV.torus_iSupIndep k).pairwiseDisjoint hij
  have h1 : hV.hm k i (-1) = 1 := Subgroup.disjoint_def.1 hdisj (hV.hm_mem_torus k i (-1))
    (h ▸ hV.hm_mem_torus k j (-1))
  have := hinv i
  rw [h1, orderOf_one] at this
  omega

end TwoInvolutions

end CFSG.ClassicalInvolution.ModelFacts
