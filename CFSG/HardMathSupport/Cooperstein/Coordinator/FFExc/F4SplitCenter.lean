module

public import CFSG.HardMathSupport.Cooperstein.Coordinator.FFExc.F4SplitMoves
public import CFSG.HardMathSupport.Cooperstein.Coordinator.FFExc.F4SplitSplitting

public noncomputable section

set_option linter.unusedSectionVars false

namespace CFSG.HardMathSupport.Cooperstein.Coordinator.FFExc

open CFSG.Blueprint.Chevalley CFSG.LieType.Steinberg.Minuscule Matrix

variable (hV : e6Data.Valid) {K : Type*} [Field K] [CharP K 2]

theorem coe_E (k : ℕ) (hk : k < 72) (v : Fin e6Data.d →₀ K) :
    ⇑(e6Data.E K k v) = (Em2 k).map (cast2 K) *ᵥ ⇑v := by
  have := LinearMap.toMatrix_mulVec_repr Finsupp.basisSingleOne Finsupp.basisSingleOne
    (e6Data.E K k) v
  rw [toMatrix_E k hk] at this
  simpa [Finsupp.basisSingleOne_repr] using this.symm

theorem Em2_apply (k : ℕ) (i j : Ix) :
    Em2 k i j = if tgt k j = i.val + 1 then 1 else 0 := rfl

theorem E_single (k : ℕ) (hk : k < 72) (p a : Fin e6Data.d) (h : tgt k p = a.val + 1) :
    e6Data.E K k (Finsupp.single p 1) = Finsupp.single a 1 := by
  ext i
  rw [coe_E k hk, Finsupp.single_eq_pi_single, Matrix.mulVec_single_one]
  simp only [Finsupp.single_apply]
  by_cases hi : a = i
  · subst hi; simp [Em2_apply, h]
  · have : ¬ tgt k p = i.val + 1 := fun h' => hi (Fin.ext (by omega))
    simp [Em2_apply, this, hi]

theorem E_zero_v0 : e6Data.E K 0 (v0 K) = Finsupp.single (⟨10, by decide⟩ : Fin e6Data.d) 1 := by
  ext i
  rw [coe_E 0 (by decide), coe_v0, s3K, map_mulVec', Em2_start, Finsupp.single_eq_pi_single]
  by_cases hi : (⟨10, by decide⟩ : Fin e6Data.d) = i
  · subst hi; simp
  · simp [Ne.symm hi]

theorem endo_comm_E {z : hV.minGroup K} (hz : z ∈ Subgroup.center (hV.minGroup K)) (k : ℕ)
    (hk : k < 72) (v : Fin e6Data.d →₀ K) :
    hV.endo K z (e6Data.E K k v) = e6Data.E K k (hV.endo K z v) := by
  have h := Subgroup.mem_center_iff.1 hz (hV.xm K (e6root k) 1)
  have h2 := congrArg (fun g => hV.endo K g v) h
  simp only [MinData.Valid.endo_mul, Module.End.mul_apply, MinData.Valid.endo_xm] at h2
  have e : e6Data.rootOp K (e6root k) = e6Data.E K k :=
    MinData.rootOp_root (show k < Tag.E6.rootCertificate.roots.length from hk)
  rw [e] at h2
  simp only [LinearMap.add_apply, Module.End.one_apply, one_smul,
    map_add] at h2
  exact (add_left_cancel h2).symm

theorem eq_one_of_mem_center_of_mem_F4in27 {z : hV.minGroup K}
    (hz : z ∈ Subgroup.center (hV.minGroup K)) (hzF : z ∈ F4in27 hV K) : z = 1 := by
  have hv0 := endo_v0 hV hzF
  have key : ∀ a < e6Data.d, ∀ h : a < e6Data.d,
      hV.endo K z (Finsupp.single ⟨a, h⟩ (1 : K)) = Finsupp.single ⟨a, h⟩ 1 := by
    refine wtree_reach (fun a => ∀ h : a < e6Data.d,
      hV.endo K z (Finsupp.single ⟨a, h⟩ (1 : K)) = Finsupp.single ⟨a, h⟩ 1) ?_ ?_
    · intro h
      have := endo_comm_E hV hz 0 (by decide) (v0 K)
      rw [E_zero_v0, hv0, E_zero_v0] at this
      exact this
    · intro a p k hmem hp h
      obtain ⟨ha, hp', hk, htg⟩ := wtree_step _ hmem
      have hE := E_single (K := K) k hk ⟨p, hp'⟩ ⟨a, h⟩ htg
      have := endo_comm_E hV hz k hk (Finsupp.single ⟨p, hp'⟩ 1)
      rw [hE, hp hp'] at this
      rw [this, hE]
  have hone : hV.endo K z = 1 := by
    refine (Finsupp.basisSingleOne (R := K)).ext fun a => ?_
    rw [Finsupp.coe_basisSingleOne, Module.End.one_apply]
    exact key a.val a.2 a.2
  exact hV.endo_injective K (by rw [hone]; rfl)

end CFSG.HardMathSupport.Cooperstein.Coordinator.FFExc
