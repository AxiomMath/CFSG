module

public import CFSG.LocalAnalysis.ComponentInitial.BinaryBilinearExtension
public import CFSG.LocalAnalysis.ComponentInitial.BasicFacts
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.ElementaryAbelian

public section

namespace CFSG.LocalAnalysis.ComponentInitial

open BinExt

variable (K : Type*) [Field K] [Module (ZMod 2) K]

theorem zmod2_cases (c : ZMod 2) : c = 0 ∨ c = 1 := by
  revert c
  decide

@[expose] noncomputable def suzukiTwistBilin (φ : K ≃+* K) : K →ₗ[ZMod 2] K →ₗ[ZMod 2] K :=
  LinearMap.mk₂ (ZMod 2) (fun x y => x * φ y) (fun x x' y => add_mul _ _ _)
    (fun c x y => by rcases zmod2_cases c with rfl | rfl <;> simp)
    (fun x y y' => by rw [map_add, mul_add])
    (fun c x y => by rcases zmod2_cases c with rfl | rfl <;> simp)

theorem suzukiTwistBilin_apply (φ : K ≃+* K) (x y : K) : suzukiTwistBilin K φ x y = x * φ y :=
  rfl

abbrev SuzukiA (φ : K ≃+* K) : Type _ := BinExt (suzukiTwistBilin K φ)

variable {K}

instance [Finite K] (φ : K ≃+* K) : Finite (SuzukiA K φ) :=
  Finite.of_equiv (K × K) ⟨fun p => ⟨p.1, p.2⟩, fun x => (x.fst, x.snd), fun _ => rfl, fun _ => rfl⟩

theorem suzuki_two_A_model {n : ℕ} (hn : 1 ≤ n) (hK : Nat.card K = 2 ^ n) (φ : K ≃+* K) :
    CharP K 2 ∧ (∀ x y : K, suzukiTwistBilin K φ x y = x * φ y) ∧
    (∀ x y : SuzukiA K φ, x * y = ⟨x.fst + y.fst, x.snd + y.snd + x.fst * φ y.fst⟩) ∧
    (1 : SuzukiA K φ) = ⟨0, 0⟩ ∧
    ((centerSub (suzukiTwistBilin K φ) : Set (SuzukiA K φ)) = {x | x.fst = 0}) ∧
    (∀ z : K, iotaHom (suzukiTwistBilin K φ) (Multiplicative.ofAdd z) = ⟨0, z⟩) ∧
    ∀ x : SuzukiA K φ, piHom (suzukiTwistBilin K φ) x = Multiplicative.ofAdd x.fst :=
  ⟨finite_field_prime_power_characteristic Nat.prime_two hn hK, fun _ _ => rfl, fun _ _ => rfl,
    rfl, Set.ext fun _ => mem_centerSub, fun _ => rfl, fun _ => rfl⟩

theorem finrank_eq_of_card [Finite K] {n : ℕ} (hK : Nat.card K = 2 ^ n) :
    Module.finrank (ZMod 2) K = n := by
  have : Fintype K := Fintype.ofFinite K
  have h := Module.card_eq_pow_finrank (K := ZMod 2) (V := K)
  rw [ZMod.card, ← Nat.card_eq_fintype_card, hK] at h
  exact (Nat.pow_right_injective le_rfl h).symm

theorem suzuki_two_A_model_structure [Finite K] {n : ℕ} (hn : 1 ≤ n) (hK : Nat.card K = 2 ^ n)
    (φ : K ≃+* K) :
    Nat.card (SuzukiA K φ) = 2 ^ (2 * n) ∧
    centerSub (suzukiTwistBilin K φ) ≤ Subgroup.center (SuzukiA K φ) ∧
    CFSG.IsElementaryAbelian 2 (centerSub (suzukiTwistBilin K φ)) ∧
    Nat.card (centerSub (suzukiTwistBilin K φ)) = 2 ^ n ∧
    Function.Surjective (piHom (suzukiTwistBilin K φ)) ∧
    (piHom (suzukiTwistBilin K φ)).ker = centerSub (suzukiTwistBilin K φ) ∧
    Nonempty (SuzukiA K φ ⧸ centerSub (suzukiTwistBilin K φ) ≃* Multiplicative K) ∧
    (∀ x : SuzukiA K φ, x ^ 2 = ⟨0, x.fst * φ x.fst⟩) ∧
    (∀ x y : SuzukiA K φ, x⁻¹ * y⁻¹ * x * y = ⟨0, x.fst * φ y.fst + y.fst * φ x.fst⟩) ∧
    (∀ x : SuzukiA K φ, x ∉ centerSub (suzukiTwistBilin K φ) → orderOf x = 4) ∧
    (centerSub (suzukiTwistBilin K φ)).Characteristic ∧
    (φ ≠ 1 → Subgroup.center (SuzukiA K φ) = centerSub (suzukiTwistBilin K φ) ∧
      ∃ x y : SuzukiA K φ, x * y ≠ y * x) ∧
    (φ = 1 → (∀ x y : SuzukiA K φ, x * y = y * x) ∧
      Nonempty (SuzukiA K φ ≃* Multiplicative (Fin n → ZMod 4))) := by
  have hchar : CharP K 2 := finite_field_prime_power_characteristic Nat.prime_two hn hK
  have hdim := finrank_eq_of_card hK
  have : FiniteDimensional (ZMod 2) K := Module.Finite.of_finite
  obtain ⟨-, hcard, -, -, hinjι, hrange, -, hWc, -, hsurj, hker, hquot, h4, hsq, hcomm, hcen,
    hcharW⟩ := binary_bilinear_extension_group (suzukiTwistBilin K φ)
  have h2 : (2 : K) = 0 := by exact_mod_cast CharP.cast_eq_zero K 2
  have hsq0 : ∀ u : K, suzukiTwistBilin K φ u u = 0 → u = 0 := fun u hu => by
    rw [suzukiTwistBilin_apply] at hu
    rcases mul_eq_zero.1 hu with h | h
    · exact h
    · exact (map_eq_zero_iff φ φ.injective).1 h
  obtain ⟨hset, hW⟩ := hcharW hsq0
  have hWcard : Nat.card (centerSub (suzukiTwistBilin K φ)) = 2 ^ n := by
    rw [← hrange, ← Nat.card_congr (MonoidHom.ofInjective hinjι).toEquiv]
    exact hK
  have helem : CFSG.IsElementaryAbelian 2 (centerSub (suzukiTwistBilin K φ)) := by
    refine { toIsMulCommutative := ⟨⟨fun a b => Subtype.ext ?_⟩⟩
             exponent_dvd_p := Monoid.exponent_dvd_of_forall_pow_eq_one fun g => Subtype.ext ?_ }
    · exact (Subgroup.mem_center_iff.1 (hWc a.2) b).symm
    · have hg : (g : SuzukiA K φ) ^ 2 = 1 := by
        have : (g : SuzukiA K φ) ∈ {x : SuzukiA K φ | x ^ 2 = 1} := by
          rw [hset]
          exact g.2
        exact this
      simpa using hg
  have hord : ∀ x : SuzukiA K φ, x ∉ centerSub (suzukiTwistBilin K φ) → orderOf x = 4 := by
    intro x hx
    have hx2 : ¬ x ^ 2 ^ 1 = 1 := by
      intro h
      apply hx
      rw [← SetLike.mem_coe, ← hset]
      simpa using h
    have := orderOf_eq_prime_pow (p := 2) hx2 (by simpa using h4 x)
    simpa using this
  refine ⟨by rw [hcard, hdim, two_mul], hWc, helem, hWcard, hsurj, hker, hquot, hsq, hcomm, hord,
    hW, fun hφ => ?_, fun hφ => ?_⟩
  ·
    have hZ : Subgroup.center (SuzukiA K φ) = centerSub (suzukiTwistBilin K φ) := by
      refine le_antisymm (fun x hx => ?_) hWc
      rw [mem_centerSub]
      by_contra hx0
      rw [← SetLike.mem_coe, hcen] at hx
      have hx1 := hx 1
      simp only [suzukiTwistBilin_apply, map_one, mul_one, one_mul] at hx1
      have hφx : φ x.fst = x.fst := by linear_combination hx1 - x.fst * h2
      apply hφ
      refine RingEquiv.ext fun y => ?_
      have hy := hx y
      simp only [suzukiTwistBilin_apply, hφx] at hy
      have : x.fst * (φ y - y) = 0 := by linear_combination hy - y * x.fst * h2
      show φ y = y
      exact sub_eq_zero.1 ((mul_eq_zero.1 this).resolve_left hx0)
    refine ⟨hZ, ⟨⟨1, 0⟩, ?_⟩⟩
    by_contra h
    push Not at h
    have hmem : (⟨1, 0⟩ : SuzukiA K φ) ∈ Subgroup.center (SuzukiA K φ) :=
      Subgroup.mem_center_iff.2 fun y => (h y).symm
    rw [hZ, mem_centerSub] at hmem
    exact one_ne_zero hmem
  ·
    subst hφ
    have hab : ∀ x y : SuzukiA K 1, x * y = y * x := fun x y => by
      rw [← mul_inv_eq_one, show x * y * (y * x)⁻¹ = x * y * x⁻¹ * y⁻¹ by group]
      have := hcomm x⁻¹ y⁻¹
      rw [inv_inv, inv_inv] at this
      rw [this]
      ext
      · rfl
      · change (x⁻¹).fst * (y⁻¹).fst + (y⁻¹).fst * (x⁻¹).fst = 0
        rw [mul_comm]
        linear_combination (y⁻¹).fst * (x⁻¹).fst * h2
    refine ⟨hab, ?_⟩
    let _ : CommGroup (SuzukiA K 1) :=
      { (inferInstance : Group (SuzukiA K 1)) with mul_comm := hab }
    let e := Module.finBasisOfFinrankEq (ZMod 2) K hdim
    let a : Fin n → SuzukiA K 1 := fun i => ⟨e i, 0⟩
    have ha4 : ∀ i, a i ^ 4 = 1 := fun i => h4 _
    let F : Multiplicative (Fin n → ZMod 4) →* SuzukiA K 1 :=
      { toFun := fun c => ∏ i, a i ^ (c.toAdd i).val
        map_one' := by simp
        map_mul' := fun c d => by
          rw [← Finset.prod_mul_distrib]
          refine Finset.prod_congr rfl fun i _ => ?_
          rw [toAdd_mul, Pi.add_apply, ZMod.val_add, ← pow_add, ← pow_eq_pow_mod _ (ha4 i)] }
    have hFpi : ∀ c, (F c).fst = ∑ i, ((c.toAdd i).val : ZMod 2) • e i := by
      intro c
      have h := congrArg Multiplicative.toAdd (map_prod (piHom (suzukiTwistBilin K 1))
        (fun i => a i ^ (c.toAdd i).val) Finset.univ)
      simp only [toAdd_prod, map_pow, toAdd_pow] at h
      change (piHom (suzukiTwistBilin K 1) (F c)).toAdd = _
      rw [show F c = ∏ i, a i ^ (c.toAdd i).val from rfl, h]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Nat.cast_smul_eq_nsmul]
      rfl
    have hFinj : Function.Injective F := by
      rw [injective_iff_map_eq_one]
      intro c hc
      have hev : ∀ i, ((c.toAdd i).val : ZMod 2) = 0 := by
        have h0 : ∑ i, ((c.toAdd i).val : ZMod 2) • e i = 0 := by rw [← hFpi, hc]; rfl
        intro i
        have := congrArg (fun v => e.repr v i) h0
        simpa [Finsupp.single_apply] using this
      let d : Multiplicative (Fin n → ZMod 4) :=
        Multiplicative.ofAdd fun i => if c.toAdd i = 0 then 0 else 1
      have hcd : c = d * d := by
        refine Multiplicative.toAdd.injective (funext fun i => ?_)
        have hi := hev i
        simp only [d, toAdd_mul, toAdd_ofAdd, Pi.add_apply]
        generalize c.toAdd i = x at hi ⊢
        revert x
        decide
      have hd2 : F d * F d = 1 := by rw [← map_mul, ← hcd, hc]
      have hfst : (F d).fst * (F d).fst = 0 := by
        have := hsq (F d)
        rw [sq, hd2] at this
        have h' := congrArg BinExt.snd this
        change (0 : K) = (F d).fst * (F d).fst at h'
        exact h'.symm
      have hfst0 : (F d).fst = 0 := mul_self_eq_zero.1 hfst
      rw [hFpi] at hfst0
      refine Multiplicative.toAdd.injective (funext fun i => ?_)
      have hi := congrArg (fun v => e.repr v i) hfst0
      simp only [map_sum, map_smul, Module.Basis.repr_self, Finsupp.smul_single, smul_eq_mul,
        mul_one, Finsupp.coe_finsetSum, Finset.sum_apply, Finsupp.single_apply] at hi
      rw [Finset.sum_ite_eq' Finset.univ i] at hi
      simp only [Finset.mem_univ, ite_true, map_zero, Finsupp.coe_zero, Pi.zero_apply] at hi
      have hci := hev i
      simp only [d, toAdd_ofAdd] at hi
      change c.toAdd i = 0
      generalize c.toAdd i = x at hi hci ⊢
      revert x
      decide
    have hcardF : Nat.card (Multiplicative (Fin n → ZMod 4)) = Nat.card (SuzukiA K 1) := by
      rw [hcard, hdim, Nat.card_eq_fintype_card, Fintype.card_multiplicative, Fintype.card_fun,
        ZMod.card, Fintype.card_fin, show (4 : ℕ) = 2 ^ 2 from rfl, ← pow_mul, two_mul]
    have hbij : Function.Bijective F :=
      (Function.Injective.bijective_of_nat_card_le hFinj hcardF.ge)
    exact ⟨(MulEquiv.ofBijective F hbij).symm⟩

end CFSG.LocalAnalysis.ComponentInitial
