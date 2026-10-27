module

public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofBurgE1G2Three
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofBurgE1ReeTrace
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofBurgE1D4Galois

public noncomputable section

namespace CFSG.ComponentClassification.CatLeafProof

open CFSG Subgroup CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Ree
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)

theorem frobeniusEquiv_three_pow_apply {K : Type} [Field K] [Finite K] [CharP K 3] (n : ℕ)
    (c : K) : ((frobeniusEquiv K 3) ^ n) c = c ^ 3 ^ n := by
  induction n generalizing c with
  | zero => rw [pow_zero, pow_zero, pow_one]; rfl
  | succ n ih =>
    rw [pow_succ]
    show ((frobeniusEquiv K 3) ^ n) (frobeniusEquiv K 3 c) = _
    rw [ih, frobeniusEquiv_apply, frobenius_def, ← pow_mul, ← pow_succ']

theorem pow_natCard_pow_eq_self {K : Type} [Field K] [Finite K] (c : K) (m : ℕ) :
    c ^ Nat.card K ^ m = c := by
  induction m with
  | zero => rw [pow_zero, pow_one]
  | succ m ih => rw [pow_succ, pow_mul, ih, pow_natCard_eq_self]

theorem exists_eq_conj_of_fixes_reeTorus
    {K : Type} [Field K] [Finite K] [CharP K ReeTag.G2.prime] (a : ℕ)
    (hK : Nat.card K = 3 ^ (2 * a + 1)) (β : MulAut (adjointGroup ReeTag.G2.tag K))
    (hβ : Odd (orderOf β))
    (hT : ∀ s : Kˣ, β (ReeTag.G2.reeTorus a ReeTag.g2I0 s) = ReeTag.G2.reeTorus a ReeTag.g2I0 s) :
    ∃ g : adjointGroup ReeTag.G2.tag K, β = MulAut.conj g := by
  obtain ⟨g, n, hgn⟩ := G2_three_eq_conj_frobenius_of_odd (by omega) hK β hβ
  have : CharP K 3 := ‹CharP K ReeTag.G2.prime›
  set σ := (frobeniusEquiv K 3) ^ n with hσdef
  have hFrx : ∀ x : adjointGroup ReeTag.G2.tag K,
      ((ReeTag.G2.finiteFrobeniusAut K ^ n) x : ModGL ReeTag.G2.tag K) =
        Units.map (entrywiseHom σ.toRingHom) (x : ModGL ReeTag.G2.tag K) :=
    fun x => coe_G2_finiteFrobeniusAut_pow n x
  have hexpr : ∀ x : adjointGroup ReeTag.G2.tag K, (β x : ModGL ReeTag.G2.tag K) =
      (g : ModGL ReeTag.G2.tag K) * Units.map (entrywiseHom σ.toRingHom)
        (x : ModGL ReeTag.G2.tag K) * (g : ModGL ReeTag.G2.tag K)⁻¹ := by
    intro x
    rw [hgn, MulAut.mul_apply, MulAut.conj_apply, Subgroup.coe_mul, Subgroup.coe_mul,
      Subgroup.coe_inv, hFrx]
  have hσpow : ∀ c : K, σ c = c ^ 3 ^ (n % (2 * a + 1)) := by
    intro c
    have e : 3 ^ n = Nat.card K ^ (n / (2 * a + 1)) * 3 ^ (n % (2 * a + 1)) := by
      rw [hK, ← pow_mul, ← pow_add, Nat.div_add_mod]
    rw [hσdef, frobeniusEquiv_three_pow_apply, e, pow_mul, pow_natCard_pow_eq_self]
  have htr : ∀ s : Kˣ, ∑ k, σ (zpowChar K (g2TorusExp (3 ^ a) k) s) =
      ∑ k, zpowChar K (g2TorusExp (3 ^ a) k) s := by
    intro s
    have h1 : LinearMap.trace K (RootModule ReeTag.G2.tag K)
        ((β (ReeTag.G2.reeTorus a ReeTag.g2I0 s) : ModGL ReeTag.G2.tag K) :
          Module.End K (RootModule ReeTag.G2.tag K)) =
        σ (LinearMap.trace K (RootModule ReeTag.G2.tag K)
          (((ReeTag.G2.reeTorus a ReeTag.g2I0 s : adjointGroup ReeTag.G2.tag K) :
            ModGL ReeTag.G2.tag K) : Module.End K (RootModule ReeTag.G2.tag K))) :=
      trace_apply_of_G2_expression β g σ hexpr _
    rw [hT s, trace_reeTorus_G2, map_add, map_ofNat, map_sum] at h1
    exact (add_left_cancel h1).symm
  have hn : n % (2 * a + 1) = 0 := by
    by_contra hn0
    exact g2TorusExp_frobenius_absurd hK (Nat.mod_lt _ (by omega)) hn0 σ hσpow htr
  have hσ1 : σ = 1 := RingEquiv.ext fun c => by
    rw [hσpow, hn, pow_zero, pow_one]
    rfl
  have hFr : ReeTag.G2.finiteFrobeniusAut K ^ n = 1 := by
    refine MulEquiv.ext fun x => Subtype.ext ?_
    rw [hFrx, hσ1]
    exact Units.ext (entrywise_id _)
  exact ⟨g, by rw [hgn, hFr, mul_one]⟩

theorem burgE1ReeCosetInput_holds
    :
    ∀ (K : Type) [Field K] [Finite K] [CharP K ReeTag.G2.prime] (a : ℕ),
      Nat.card K = 3 ^ (2 * a + 1) → ∀ β : MulAut (adjointGroup ReeTag.G2.tag K),
        Odd (orderOf β) → ReeTag.G2.finiteReeAut K a * β = β * ReeTag.G2.finiteReeAut K a →
          (∀ x ∈ fixedSubgroup (ReeTag.G2.finiteReeAut K a), β x = x) → β = 1 := by
  intro K _ _ _ a hK β hβ hcomm hfix
  have hmem : ∀ s : Kˣ, ReeTag.G2.reeTorus a ReeTag.g2I0 s ∈
      fixedSubgroup (ReeTag.G2.finiteReeAut K a) := fun s => by
    show ReeTag.G2.finiteReeAut K a _ = _
    rw [ReeTag.finiteReeAut_eq_reeAut]
    exact (mem_reeFixed ReeTag.G2 K a).1 (ReeTag.G2.reeTorus_mem_reeFixed a hK (by decide) s)
  obtain ⟨g, hβg⟩ := exists_eq_conj_of_fixes_reeTorus a hK β hβ fun s => hfix _ (hmem s)
  have hFg : ReeTag.G2.finiteReeAut K a g = g := by
    have hc : g⁻¹ * ReeTag.G2.finiteReeAut K a g ∈
        Subgroup.center (adjointGroup ReeTag.G2.tag K) := by
      rw [Subgroup.mem_center_iff]
      intro y
      have h1 := DFunLike.congr_fun hcomm ((ReeTag.G2.finiteReeAut K a).symm y)
      rw [hβg, MulAut.mul_apply, MulAut.mul_apply, MulAut.conj_apply, MulAut.conj_apply,
        map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply] at h1
      calc y * (g⁻¹ * ReeTag.G2.finiteReeAut K a g) = g⁻¹ * (g * y * g⁻¹) *
            ReeTag.G2.finiteReeAut K a g := by group
        _ = g⁻¹ * (ReeTag.G2.finiteReeAut K a g * y * (ReeTag.G2.finiteReeAut K a g)⁻¹) *
            ReeTag.G2.finiteReeAut K a g := by rw [h1]
        _ = g⁻¹ * ReeTag.G2.finiteReeAut K a g * y := by group
    rw [center_adjointGroup_eq_bot, Subgroup.mem_bot] at hc
    exact (inv_mul_eq_one.1 hc).symm
  have hgΓ : (g : ModGL ReeTag.G2.tag K) ∈ ReeTag.G2.reeGamma K a :=
    Subgroup.mem_map.2 ⟨g, hFg, rfl⟩
  have hcen : (⟨_, hgΓ⟩ : ReeTag.G2.reeGamma K a) ∈
      Subgroup.center (ReeTag.G2.reeGamma K a) := by
    rw [Subgroup.mem_center_iff]
    rintro ⟨y, x, hx, rfl⟩
    have h1 := hfix x hx
    rw [hβg, MulAut.conj_apply, mul_inv_eq_iff_eq_mul] at h1
    refine Subtype.ext ?_
    have h2 := congrArg (fun z : adjointGroup ReeTag.G2.tag K => (z : ModGL ReeTag.G2.tag K)) h1
    simp only [Subgroup.coe_mul] at h2
    exact h2.symm
  rw [ReeTag.center_reeGamma_G2_eq_bot hK, Subgroup.mem_bot] at hcen
  have hg1 : (g : ModGL ReeTag.G2.tag K) = 1 := congrArg Subtype.val hcen
  rw [hβg, show g = 1 from Subtype.ext hg1, map_one]

end CFSG.ComponentClassification.CatLeafProof
