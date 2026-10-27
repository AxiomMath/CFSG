module

public import CFSG.CGT.PushingUpLit.CGT6.EmbNatBase

public section

namespace CFSG.CGT.PushingUpLit.CGT6

open CFSG CFSG.Quasithin

private def nmWt (m : ℕ) (u : G6.PermMod m) : ZMod 2 := ∑ i, Multiplicative.toAdd u i

private def nmConst (m : ℕ) (a : ZMod 2) : G6.PermMod m := Multiplicative.ofAdd fun _ => a

private lemma nmWt_mul {m : ℕ} (u v : G6.PermMod m) : nmWt m (u * v) = nmWt m u + nmWt m v := by
  simp [nmWt, Finset.sum_add_distrib]

private lemma nmWt_permAct {m : ℕ} (σ : Equiv.Perm (Fin m)) (u : G6.PermMod m) :
    nmWt m (G6.permAct m σ u) = nmWt m u := by
  simp only [nmWt, G6.permAct_apply]
  exact Equiv.sum_comp σ⁻¹ fun i => Multiplicative.toAdd u i

private lemma nmConst_add {m : ℕ} (a b : ZMod 2) :
    nmConst m (a + b) = nmConst m a * nmConst m b := rfl

private lemma nmConst_zero {m : ℕ} : nmConst m 0 = 1 := rfl

private lemma nmConst_mul_self {m : ℕ} (a : ZMod 2) : nmConst m a * nmConst m a = 1 := by
  rw [← nmConst_add, CharTwo.add_self_eq_zero, nmConst_zero]

private lemma nmWt_const {m : ℕ} (hm : Odd m) (a : ZMod 2) : nmWt m (nmConst m a) = a := by
  have h : ((m : ℕ) : ZMod 2) = 1 := ZMod.natCast_eq_one_iff_odd.mpr hm
  simp [nmWt, nmConst, h]

private lemma permAct_nmConst {m : ℕ} (σ : Equiv.Perm (Fin m)) (a : ZMod 2) :
    G6.permAct m σ (nmConst m a) = nmConst m a := rfl

private lemma nmShift_mem {m : ℕ} (hm : Odd m) (u : G6.PermMod m) :
    u * nmConst m (nmWt m u) ∈ G6.coreMod m := by
  rw [G6.mem_coreMod]
  change nmWt m (u * nmConst m (nmWt m u)) = 0
  rw [nmWt_mul, nmWt_const hm, CharTwo.add_self_eq_zero]

private def nmProj {m : ℕ} (hm : Odd m) : G6.PermMod m →* ↥(G6.coreMod m) :=
  MonoidHom.mk' (fun u => ⟨u * nmConst m (nmWt m u), nmShift_mem hm u⟩) fun u v => by
    apply Subtype.ext
    simp only [nmWt_mul, nmConst_add, Subgroup.coe_mul]
    exact mul_mul_mul_comm _ _ _ _

private lemma nmProj_coe {m : ℕ} (hm : Odd m) (u : G6.PermMod m) :
    ((nmProj hm u : ↥(G6.coreMod m)) : G6.PermMod m) = u * nmConst m (nmWt m u) := rfl

private lemma nmProj_of_mem {m : ℕ} (hm : Odd m) {u : G6.PermMod m} (hu : u ∈ G6.coreMod m) :
    nmProj hm u = ⟨u, hu⟩ := by
  apply Subtype.ext
  have h0 : nmWt m u = 0 := hu
  rw [nmProj_coe, h0, nmConst_zero, mul_one]

private lemma nmProj_surjective {m : ℕ} (hm : Odd m) : Function.Surjective (nmProj hm) :=
  fun x => ⟨x.1, nmProj_of_mem hm x.2⟩

private lemma nmProj_const {m : ℕ} (hm : Odd m) (a : ZMod 2) : nmProj hm (nmConst m a) = 1 := by
  apply Subtype.ext
  rw [nmProj_coe, nmWt_const hm, nmConst_mul_self]
  rfl

private lemma nmConst_mem_zpowers {m : ℕ} (a : ZMod 2) :
    nmConst m a ∈ Subgroup.zpowers (G6.allOnes m) := by
  fin_cases a
  · exact one_mem _
  · exact Subgroup.mem_zpowers _

private lemma nmProj_ker {m : ℕ} (hm : Odd m) :
    (nmProj hm).ker = Subgroup.zpowers (G6.allOnes m) := by
  apply le_antisymm
  · intro u hu
    have h1 : u * nmConst m (nmWt m u) = 1 := congrArg Subtype.val (MonoidHom.mem_ker.mp hu)
    have h2 : u = nmConst m (nmWt m u) :=
      (mul_eq_one_iff_eq_inv.mp h1).trans (inv_eq_of_mul_eq_one_right (nmConst_mul_self _))
    rw [h2]
    exact nmConst_mem_zpowers _
  · rw [Subgroup.zpowers_le]
    exact MonoidHom.mem_ker.mpr (nmProj_const hm 1)

private lemma nmProj_permAct {m : ℕ} (hm : Odd m) (σ : Equiv.Perm (Fin m)) (u : G6.PermMod m) :
    nmProj hm (G6.permAct m σ u) = G6.coreAct m σ (nmProj hm u) := by
  apply Subtype.ext
  rw [G6.coreAct_coe, nmProj_coe, nmProj_coe, map_mul, nmWt_permAct, permAct_nmConst]

theorem natSectionWith_of_orbitHom {V : Type} [CommGroup V] {m : ℕ} (hm : Odd m)
    {X : Subgroup (MulAut V)} (θ : X ≃* alternatingGroup (Fin m)) {W : Subgroup V}
    (Φ : G6.PermMod m →* V) (hrange : Φ.range = W)
    (hker : Φ.ker = Subgroup.zpowers (G6.allOnes m))
    (hequiv : ∀ (x : X) (u : G6.PermMod m), (x : MulAut V) (Φ u) =
      Φ (G6.permAct m ((θ x : alternatingGroup (Fin m)) : Equiv.Perm (Fin m)) u)) :
    IsNatSectionWith (altAct m) θ W ⊥ := by
  subst hrange
  have hle : Φ.rangeRestrict.ker ≤ (nmProj hm).ker := by
    rw [MonoidHom.ker_rangeRestrict, hker, nmProj_ker]
  let β : ↥Φ.range →* ↥(G6.coreMod m) :=
    Φ.rangeRestrict.liftOfSurjective Φ.rangeRestrict_surjective ⟨nmProj hm, hle⟩
  have hβ : ∀ u, β (Φ.rangeRestrict u) = nmProj hm u := fun u => by
    simp [β]
  refine ⟨?_, β, ?_, ?_, ?_⟩
  · intro x hx p hp
    obtain ⟨u, rfl⟩ := hp
    exact ⟨_, (hequiv ⟨x, hx⟩ u).symm⟩
  · intro y
    obtain ⟨u, rfl⟩ := nmProj_surjective hm y
    exact ⟨Φ.rangeRestrict u, hβ u⟩
  · rw [Subgroup.bot_subgroupOf]
    ext p
    rw [MonoidHom.mem_ker, Subgroup.mem_bot]
    constructor
    · intro hp
      obtain ⟨u, rfl⟩ := Φ.rangeRestrict_surjective p
      rw [hβ] at hp
      have hu : u ∈ Φ.ker := by
        rw [hker, ← nmProj_ker hm]
        exact hp
      exact Subtype.ext hu
    · rintro rfl
      exact map_one β
  · intro x p hp
    obtain ⟨u, rfl⟩ := Φ.rangeRestrict_surjective p
    have hx : (⟨(x : MulAut V) (Φ.rangeRestrict u : V), hp⟩ : ↥Φ.range) =
        Φ.rangeRestrict (G6.permAct m ((θ x : alternatingGroup (Fin m)) :
          Equiv.Perm (Fin m)) u) :=
      Subtype.ext (hequiv x u)
    rw [hx, hβ, hβ, nmProj_permAct]
    rfl

end CFSG.CGT.PushingUpLit.CGT6
