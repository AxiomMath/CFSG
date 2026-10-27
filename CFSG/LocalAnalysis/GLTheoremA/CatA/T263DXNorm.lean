module

import CFSG.LargeExtraspecial.S5Comp
public import CFSG.CGT.PushingUpLit.Transport
public import CFSG.ClassicalInvolution.Basic
public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma53
public import CFSG.LocalAnalysis.GLTheoremA.P55.I336.ClassTwo
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.LocalAnalysis.SeitzReduction.EPilotPosition
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels
public import CFSG.Yardstones.Md0ec50421ce4.Definitions

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T263.DX

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.LocalAnalysis.GLTheoremA

section NormHom

variable {Ω : Type*} [Group Ω]

private theorem exists_norm_hom {ι : Type} [Fintype ι] [DecidableEq ι] {J X : Subgroup Ω}
    (ψ : ι → Ω) (σ : Equiv.Perm ι) {e : Ω} (i₀ : ι)
    (hcomm : ∀ i j, i ≠ j → ∀ a ∈ J, ∀ b ∈ J,
      (ψ i * a * (ψ i)⁻¹) * (ψ j * b * (ψ j)⁻¹) = (ψ j * b * (ψ j)⁻¹) * (ψ i * a * (ψ i)⁻¹))
    (hX : ∀ i, ∀ a ∈ J, ψ i * a * (ψ i)⁻¹ ∈ X) (hσ : ∀ i, e * ψ i = ψ (σ i)) (h0 : ψ i₀ = 1) :
    ∃ N : J →* Ω, (∀ j, N j ∈ X) ∧ (∀ j, e * N j * e⁻¹ = N j) ∧
      (∀ g : Ω, (∀ i, g * ψ i = ψ i * g) → ∀ j j' : J, (j' : Ω) = g * j * g⁻¹ →
        g * N j * g⁻¹ = N j') ∧
      (∀ j : J, N j = 1 → ∀ k : J, k * j = j * k) := by
  let φ : ι → (J →* Ω) := fun i => (MulAut.conj (ψ i)).toMonoidHom.comp J.subtype
  have hφ : ∀ i (a : J), φ i a = ψ i * a * (ψ i)⁻¹ := fun i a => rfl
  have hφc : Pairwise fun i j => ∀ x y : J, Commute (φ i x) (φ j y) := fun i j hij x y => by
    simp only [hφ]
    exact hcomm i j hij x x.2 y y.2
  have hφp : ∀ j : J, Pairwise (Function.onFun Commute fun i => φ i j) :=
    fun j i k hik => hφc hik j j
  let Φ : (ι → J) →* Ω := MonoidHom.noncommPiCoprod (N := fun _ => J) φ hφc
  let N : J →* Ω := Φ.comp (MonoidHom.pi fun _ => MonoidHom.id J)
  have hN : ∀ j : J, N j = Finset.univ.noncommProd (fun i => φ i j)
      ((hφp j).set_pairwise _) := fun j => rfl
  have hN1 : ∀ j : J, N j ∈ X := fun j => by
    rw [hN]
    exact Subgroup.noncommProd_mem X _ (fun i _ => hX i j j.2)
  have hN3 : ∀ g : Ω, (∀ i, g * ψ i = ψ i * g) → ∀ j j' : J, (j' : Ω) = g * j * g⁻¹ →
      g * N j * g⁻¹ = N j' := by
    intro g hg j j' hj'
    rw [hN, hN]
    refine (Finset.map_noncommProd Finset.univ (fun i => φ i j) _
      (MulAut.conj g).toMonoidHom).trans ?_
    refine Finset.noncommProd_congr rfl (fun i _ => ?_) _
    have hcg : MulAut.conj g (ψ i) = ψ i := by
      simp only [MulAut.conj_apply, mul_inv_eq_iff_eq_mul]
      exact hg i
    simp only [hφ, MulEquiv.coe_toMonoidHom, map_mul, map_inv, hcg, hj', MulAut.conj_apply]
  have hN2 : ∀ j : J, e * N j * e⁻¹ = N j := by
    let T : (ι → J) →* (ι → J) := MonoidHom.pi fun i => Pi.evalMonoidHom (fun _ => J) (σ.symm i)
    have hT : (MulAut.conj e).toMonoidHom.comp Φ = Φ.comp T := by
      apply MonoidHom.pi_ext
      intro i y
      have hTy : T (Pi.mulSingle i y) = Pi.mulSingle (σ i) y := by
        funext k
        simp only [T, MonoidHom.pi_apply, Pi.evalMonoidHom_apply, Pi.mulSingle_apply,
          Equiv.symm_apply_eq]
      simp only [MonoidHom.comp_apply, hTy, MonoidHom.noncommPiCoprod_mulSingle, Φ,
        MulEquiv.coe_toMonoidHom, MulAut.conj_apply, hφ, ← hσ]
      group
    intro j
    exact DFunLike.congr_fun hT (fun _ => j)
  have hN4 : ∀ j : J, N j = 1 → ∀ k : J, k * j = j * k := by
    intro j hj k
    have hs := Finset.mul_noncommProd_erase Finset.univ (Finset.mem_univ i₀) (fun i => φ i j)
      ((hφp j).set_pairwise _)
    set R := (Finset.univ.erase i₀).noncommProd (fun i => φ i j) ((hφp j).set_pairwise _)
    have hRc : Commute (k : Ω) R := by
      refine Finset.noncommProd_commute _ _ _ _ (fun x hx => ?_)
      have hx' : x ≠ i₀ := Finset.ne_of_mem_erase hx
      have := hφc (Ne.symm hx') k j
      simpa [hφ, h0] using this
    rw [← hN j, hj] at hs
    have hj0 : φ i₀ j = j := by simp [hφ, h0]
    rw [hj0] at hs
    have hR' : R = (j : Ω)⁻¹ := eq_inv_of_mul_eq_one_right hs
    rw [hR'] at hRc
    exact Subtype.ext (Commute.inv_right_iff.mp hRc).eq
  exact ⟨N, hN1, hN2, hN3, hN4⟩

end NormHom

section Aux

variable {Ω : Type*} [Group Ω]

theorem isComponentOf_map_conj_of_mem_normalizer {K A : Subgroup Ω}
    (hA : IsComponentOf A K) {g : Ω} (hg : g ∈ Subgroup.normalizer (K : Set Ω)) :
    IsComponentOf (A.map (MulAut.conj g).toMonoidHom) K := by
  have hK : K.map (MulAut.conj g).toMonoidHom = K := Subgroup.mem_normalizer_iff_map_conj_eq.mp hg
  refine ⟨?_, ?_, ?_⟩
  · rw [← hK]
    exact Subgroup.map_mono hA.1
  · have := CFSG.ClassicalInvolution.isSubnormal_map_conj hA.2.1 g
    rwa [hK] at this
  · exact CFSG.ComponentClassification.Components.quasisimple_of_equiv
      (A.equivMapOfInjective _ (MulAut.conj g).injective).symm hA.2.2

private theorem mem_normalizer_of_map_conj_eq {J : Subgroup Ω} {a b : Ω}
    (h : J.map (MulAut.conj a).toMonoidHom = J.map (MulAut.conj b).toMonoidHom) :
    b⁻¹ * a ∈ Subgroup.normalizer (J : Set Ω) := by
  have key : ∀ {a b : Ω}, J.map (MulAut.conj a).toMonoidHom = J.map (MulAut.conj b).toMonoidHom →
      ∀ x ∈ J, b⁻¹ * a * x * (b⁻¹ * a)⁻¹ ∈ J := by
    intro a b h x hx
    have hmem : a * x * a⁻¹ ∈ J.map (MulAut.conj b).toMonoidHom := by
      rw [← h]
      exact Subgroup.mem_map_of_mem _ hx
    obtain ⟨y, hy, hyx⟩ := hmem
    have hyx' : b * y * b⁻¹ = a * x * a⁻¹ := hyx
    have : b⁻¹ * a * x * (b⁻¹ * a)⁻¹ = y := by
      have hy' : y = b⁻¹ * (a * x * a⁻¹) * b := by rw [← hyx']; group
      rw [hy']
      group
    rw [this]
    exact hy
  rw [Subgroup.mem_normalizer_iff]
  intro x
  refine ⟨key h x, fun hx => ?_⟩
  have := key h.symm _ hx
  simpa [mul_assoc] using this

private theorem zpow_not_mem_of_not_dvd {p : ℕ} (hp : p.Prime) {K : Subgroup Ω} {e : Ω}
    (hepow : e ^ p = 1) (heK : e ∉ K) {m : ℤ} (hm : ¬ (p : ℤ) ∣ m) : e ^ m ∉ K := by
  intro hmK
  obtain ⟨a, b, hab⟩ := (Nat.prime_iff_prime_int.mp hp).coprime_iff_not_dvd.mpr hm
  apply heK
  have hab' : (p : ℤ) * a + m * b = 1 := by linarith
  have : e = (e ^ m) ^ b := by
    calc e = e ^ ((p : ℤ) * a + m * b) := by rw [hab', zpow_one]
      _ = (e ^ p) ^ a * (e ^ m) ^ b := by
          rw [zpow_add, zpow_mul, zpow_mul, zpow_natCast]
      _ = (e ^ m) ^ b := by rw [hepow, one_zpow, one_mul]
  rw [this]
  exact K.zpow_mem hmK b

private theorem eq_of_pow_val_mem {p : ℕ} [Fact p.Prime] {K : Subgroup Ω} {e : Ω}
    (hepow : e ^ p = 1) (heK : e ∉ K) {i j : ZMod p}
    (h : (e ^ j.val)⁻¹ * e ^ i.val ∈ K) : i = j := by
  by_contra hne
  refine zpow_not_mem_of_not_dvd (Fact.out : p.Prime) hepow heK
    (m := (i.val : ℤ) - j.val) ?_ ?_
  · intro hdvd
    apply hne
    have := (ZMod.intCast_eq_intCast_iff_dvd_sub (j.val : ℤ) (i.val : ℤ) p).mpr hdvd
    simpa using this.symm
  · have : e ^ ((i.val : ℤ) - j.val) = (e ^ j.val)⁻¹ * e ^ i.val := by
      rw [zpow_sub, zpow_natCast, zpow_natCast]
      exact (Commute.pow_pow_self e _ _).inv_right.eq
    rw [this]
    exact h

end Aux

section CentralCover

theorem central_cover {J D : Type*} [Group J] [Group D] (hJ : CFSG.IsQuasisimple J)
    (π : J →* D) (hπ : Function.Surjective π) (hker : π.ker ≤ Subgroup.center J) :
    (∀ x : J, π x ∈ Subgroup.center D → x ∈ Subgroup.center J) ∧ CFSG.IsQuasisimple D ∧
      Nonempty (D ⧸ Subgroup.center D ≃* J ⧸ Subgroup.center J) := by
  haveI : Group.IsPerfect J := hJ.1
  haveI : IsSimpleGroup (J ⧸ Subgroup.center J) := hJ.2.1
  have hkey : ∀ x : J, π x ∈ Subgroup.center D → x ∈ Subgroup.center J := by
    intro x hx
    have hc : (QuotientGroup.mk x : J ⧸ Subgroup.center J) ∈
        Subgroup.center (J ⧸ Subgroup.center J) := by
      rw [Subgroup.mem_center_iff]
      intro g
      obtain ⟨q, rfl⟩ := QuotientGroup.mk_surjective g
      rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq]
      refine hker ?_
      rw [MonoidHom.mem_ker]
      have hc : π q * π x = π x * π q := Subgroup.mem_center_iff.mp hx (π q)
      simp only [map_mul, map_inv]
      rw [hc, inv_mul_cancel]
    rw [Group.IsPerfect.center_quotient_center_eq_bot J, Subgroup.mem_bot] at hc
    exact (QuotientGroup.eq_one_iff x).mp hc
  let ψ : J →* D ⧸ Subgroup.center D := (QuotientGroup.mk' (Subgroup.center D)).comp π
  have hψsurj : Function.Surjective ψ := (QuotientGroup.mk'_surjective _).comp hπ
  have hψker : ψ.ker = Subgroup.center J := by
    ext x
    rw [MonoidHom.mem_ker]
    show (π x : D ⧸ Subgroup.center D) = 1 ↔ _
    rw [QuotientGroup.eq_one_iff]
    constructor
    · exact hkey x
    · intro hx
      refine Subgroup.mem_center_iff.mpr (fun g' => ?_)
      obtain ⟨g, rfl⟩ := hπ g'
      rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.mp hx g]
  have he : J ⧸ Subgroup.center J ≃* D ⧸ Subgroup.center D :=
    (QuotientGroup.quotientMulEquivOfEq hψker).symm.trans
      (QuotientGroup.quotientKerEquivOfSurjective ψ hψsurj)
  refine ⟨hkey, ⟨Group.IsPerfect.ofSurjective hπ, he.symm.isSimpleGroup, ?_⟩, ⟨he.symm⟩⟩
  obtain ⟨a, b, hab⟩ := hJ.2.2
  exact ⟨he a, he b, fun h => hab (he.injective (by rw [map_mul, map_mul]; exact h))⟩

end CentralCover

section ExistsNorm

variable {Ω : Type*} [Group Ω] [Finite Ω]

theorem exists_norm {p : ℕ} (hp : p.Prime) {X J : Subgroup Ω} {e : Ω}
    (hJ : IsComponentOf J X) (hepow : e ^ p = 1) (heX : e ∈ Subgroup.normalizer (X : Set Ω))
    (heJ : e ∉ Subgroup.normalizer (J : Set Ω)) :
    ∃ N : J →* Ω, (∀ j, N j ∈ X) ∧ (∀ j, e * N j * e⁻¹ = N j) ∧
      (∀ g : Ω, g * e = e * g → ∀ j j' : J, (j' : Ω) = g * j * g⁻¹ → g * N j * g⁻¹ = N j') ∧
      (∀ j : J, N j = 1 → ∀ k : J, k * j = j * k) := by
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : Fact (1 < p) := ⟨hp.one_lt⟩
  let ψ : ZMod p → Ω := fun i => e ^ i.val
  have hcompI : ∀ i, IsComponentOf (J.map (MulAut.conj (ψ i)).toMonoidHom) X := fun i =>
    isComponentOf_map_conj_of_mem_normalizer hJ (Subgroup.pow_mem _ heX _)
  have hne : ∀ i j, i ≠ j →
      J.map (MulAut.conj (ψ i)).toMonoidHom ≠ J.map (MulAut.conj (ψ j)).toMonoidHom := by
    intro i j hij h
    exact hij (eq_of_pow_val_mem (K := Subgroup.normalizer (J : Set Ω)) hepow heJ
      (mem_normalizer_of_map_conj_eq h))
  have hcomm : ∀ i j, i ≠ j → ∀ a ∈ J, ∀ b ∈ J,
      (ψ i * a * (ψ i)⁻¹) * (ψ j * b * (ψ j)⁻¹) = (ψ j * b * (ψ j)⁻¹) * (ψ i * a * (ψ i)⁻¹) :=
    fun i j hij a ha b hb =>
      CFSG.LargeExtraspecial.S5.mul_comm_of_isComponentOf_ne (hcompI i) (hcompI j) (hne i j hij)
        (Subgroup.mem_map_of_mem _ ha) (Subgroup.mem_map_of_mem _ hb)
  have hX : ∀ i, ∀ a ∈ J, ψ i * a * (ψ i)⁻¹ ∈ X := fun i a ha =>
    (hcompI i).1 (Subgroup.mem_map_of_mem _ ha)
  have hσ : ∀ i : ZMod p, e * ψ i = ψ (Equiv.addRight (1 : ZMod p) i) := by
    intro i
    show e * e ^ i.val = e ^ (i + 1).val
    rw [ZMod.val_add, ZMod.val_one, ← pow_eq_pow_mod _ hepow, pow_succ']
  obtain ⟨N, hN1, hN2, hN3, hN4⟩ := exists_norm_hom (J := J) (X := X) ψ
    (Equiv.addRight (1 : ZMod p)) (e := e) 0 hcomm hX hσ (by simp [ψ])
  refine ⟨N, hN1, hN2, fun g hg j j' hjj' => hN3 g (fun i => ?_) j j' hjj', hN4⟩
  exact ((Commute.pow_right (show Commute g e from hg) i.val).eq)

end ExistsNorm

end CFSG.LocalAnalysis.GLTheoremA.T263.DX
