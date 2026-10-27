module

public import CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.N3LinAlgB
public import CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.N3Q8D8

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.N3

theorem zmod_smul_eq_val {q : ℕ} [NeZero q] {V : Type*} [AddCommGroup V] [Module (ZMod q) V]
    (c : ZMod q) (x : V) : c • x = c.val • x := by
  conv_lhs => rw [← ZMod.natCast_zmod_val c]
  exact Nat.cast_smul_eq_nsmul (ZMod q) c.val x

theorem exists_lin_map (q : ℕ) {E : Type} [CommGroup E] [Module (ZMod q) (Additive E)] :
    ∃ L : MulAut E →* Module.End (ZMod q) (Additive E),
      ∀ (g : MulAut E) (e : E), L g (Additive.ofMul e) = Additive.ofMul (g e) := by
  let lin : MulAut E → Module.End (ZMod q) (Additive E) := fun g =>
    AddMonoidHom.toZModLinearMap q (AddMonoidHom.mk'
      (fun v : Additive E => Additive.ofMul (g (Additive.toMul v))) (fun v w => by simp))
  refine ⟨{ toFun := lin, map_one' := ?_, map_mul' := ?_ }, fun g e => ?_⟩
  · ext v
    simp [lin]
  · intro g h
    ext v
    simp [lin]
  · simp [lin]

theorem scalar_of_commute_Q8D8_aux {q : ℕ} (hq : q.Prime) (hq2 : q ≠ 2) {E : Type}
    [cg : CommGroup E] [Finite E] (hexp : ∀ e : E, e ^ q = 1)
    (hcard : Nat.card E = q ^ 4) {S : Subgroup (MulAut E)} {z i j r t : MulAut E}
    (hF : Q8D8Facts S z) (hG : Q8D8Gens S z i j r t) {g : MulAut E}
    (hg : ∀ s ∈ S, g * s = s * g) : ∃ k : ℕ, ∀ e : E, g e = e ^ k := by
  haveI : Fact q.Prime := ⟨hq⟩
  haveI : NeZero q := ⟨hq.ne_zero⟩
  have hV : ∀ x : Additive E, q • x = 0 := by
    intro x
    have h1 := ofMul_pow q x.toMul
    rw [ofMul_toMul, hexp] at h1
    exact h1.symm.trans ofMul_one
  obtain ⟨hmod⟩ : ∃ m : Module (ZMod q) (Additive E), True :=
    ⟨AddCommGroup.zmodModule hV, trivial⟩
  haveI : FiniteDimensional (ZMod q) (Additive E) :=
    Module.finite_iff_finite.mpr inferInstance
  have h2 : (2 : ZMod q) ≠ 0 := by
    intro h
    have h' : ((2 : ℕ) : ZMod q) = 0 := by exact_mod_cast h
    rw [ZMod.natCast_eq_zero_iff] at h'
    exact hq2 ((Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).mp h')
  have hcardV : Nat.card (Additive E) = q ^ 4 := (Nat.card_congr Additive.toMul).trans hcard
  have hpow : Nat.card (Additive E) = q ^ Module.finrank (ZMod q) (Additive E) := by
    rw [Module.natCard_eq_pow_finrank (K := ZMod q) (V := Additive E), Nat.card_zmod]
  have hdim : Module.finrank (ZMod q) (Additive E) = 4 := by
    have h4 : q ^ Module.finrank (ZMod q) (Additive E) = q ^ 4 := by
      rw [← hpow, hcardV]
    exact Nat.pow_right_injective hq.two_le h4
  obtain ⟨L, hL⟩ := exists_lin_map (E := E) q
  have hZ1 : L z ≠ 1 := by
    intro h
    apply hF.z_ne_one
    apply MulEquiv.ext
    intro e
    have h1 : L z (Additive.ofMul e) = (1 : Module.End (ZMod q) (Additive E)) (Additive.ofMul e) := by
      rw [h]
    rw [hL, Module.End.one_apply] at h1
    exact Additive.ofMul.injective h1
  have hzc : ∀ s ∈ S, z * s = s * z := (hF.center_iff z hF.z_mem).mpr (Or.inr rfl)
  have hQ : Q8D8Op (L i) (L j) (L r) (L t) (L z) :=
    { zz := by simpa only [map_mul, map_one] using congrArg L hF.z_mul_self
      ii := by simpa only [map_mul] using congrArg L hG.ii
      jj := by simpa only [map_mul] using congrArg L hG.jj
      rr := by simpa only [map_mul] using congrArg L hG.rr
      tt := by simpa only [map_mul, map_one] using congrArg L hG.tt
      ij := by simpa only [map_mul] using congrArg L hG.ij
      tr := by simpa only [map_mul] using congrArg L hG.tr
      ir := by simpa only [map_mul] using congrArg L hG.ir
      it := by simpa only [map_mul] using congrArg L hG.it
      jr := by simpa only [map_mul] using congrArg L hG.jr
      jt := by simpa only [map_mul] using congrArg L hG.jt
      zi := by simpa only [map_mul] using congrArg L (hzc i hG.i_mem)
      zj := by simpa only [map_mul] using congrArg L (hzc j hG.j_mem)
      zr := by simpa only [map_mul] using congrArg L (hzc r hG.r_mem)
      zt := by simpa only [map_mul] using congrArg L (hzc t hG.t_mem) }
  have hgi : L g * L i = L i * L g := by
    simpa only [map_mul] using congrArg L (hg i hG.i_mem)
  have hgj : L g * L j = L j * L g := by
    simpa only [map_mul] using congrArg L (hg j hG.j_mem)
  have hgr : L g * L r = L r * L g := by
    simpa only [map_mul] using congrArg L (hg r hG.r_mem)
  have hgt : L g * L t = L t * L g := by
    simpa only [map_mul] using congrArg L (hg t hG.t_mem)
  obtain ⟨a, ha⟩ := (la_scalar h2 hdim hQ hZ1).2 (L g) hgi hgj hgr hgt
  refine ⟨a.val, fun e => ?_⟩
  apply Additive.ofMul.injective
  rw [← hL g e, ha, LinearMap.smul_apply, Module.End.one_apply, zmod_smul_eq_val,
    ofMul_pow]

theorem scalar_of_commute_Q8D8 {q : ℕ} (hq : q.Prime) (hq2 : q ≠ 2) {E : Type} [Group E]
    [Finite E] (hcomm : ∀ a b : E, a * b = b * a) (hexp : ∀ e : E, e ^ q = 1)
    (hcard : Nat.card E = q ^ 4) {S : Subgroup (MulAut E)} {z i j r t : MulAut E}
    (hF : Q8D8Facts S z) (hG : Q8D8Gens S z i j r t) {g : MulAut E}
    (hg : ∀ s ∈ S, g * s = s * g) : ∃ k : ℕ, ∀ e : E, g e = e ^ k :=
  scalar_of_commute_Q8D8_aux (cg := { (inferInstance : Group E) with mul_comm := hcomm })
    hq hq2 hexp hcard hF hG hg

end CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.N3
