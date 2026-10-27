module

public import CFSG.GroupTheory.WreathThree
import all CFSG.GroupTheory.WreathThree

public section

namespace CFSG.GroupTheory.WreathThree

open scoped Pointwise

variable {G : Type*} [Group G]

private abbrev WQ : Type := Multiplicative (ZMod 3)

private abbrev WD (n : ℕ) : Type := Multiplicative (ZMod (3 ^ n))

variable {S : Subgroup G} {y : G}

private noncomputable def yPow (hy : y ^ 3 = 1) (hy1 : y ≠ 1) :
    WQ →* Subgroup.zpowers y where
  toFun q := ⟨y ^ q.toAdd.val, (Subgroup.zpowers y).pow_mem (Subgroup.mem_zpowers y) _⟩
  map_one' := by
    apply Subtype.ext
    simp
  map_mul' q r := by
    apply Subtype.ext
    have hord : orderOf y = 3 := orderOf_eq_prime hy hy1
    have hval : (q * r).toAdd.val = (q.toAdd.val + r.toAdd.val) % 3 := by
      change (q.toAdd + r.toAdd).val = _
      rw [ZMod.val_add]
    have hrew : y ^ (q * r).toAdd.val = y ^ q.toAdd.val * y ^ r.toAdd.val := by
      rw [hval]
      set a := q.toAdd.val
      set b := r.toAdd.val
      change y ^ ((a + b) % 3) = y ^ a * y ^ b
      rw [show 3 = orderOf y from hord.symm, pow_mod_orderOf, pow_add]
    simpa using hrew

private noncomputable def conjBase (h : IsWreathThree S y) (hy : y ^ 3 = 1)
    (hy1 : y ≠ 1) (q : WQ) : MulAut (base S y) where
  toFun x := ⟨(yPow hy hy1 q : G) * (x : G) * (yPow hy hy1 q : G)⁻¹, by
    have hg : (yPow hy hy1 q : G) ∈ Subgroup.normalizer (base S y : Set G) :=
      Subgroup.zpowers_le.mpr (mem_normalizer_base h) (yPow hy hy1 q).2
    exact (Subgroup.mem_normalizer_iff.mp hg (x : G)).mp x.2⟩
  invFun x := ⟨(yPow hy hy1 q : G)⁻¹ * (x : G) * (yPow hy hy1 q : G), by
    have hg : (yPow hy hy1 q : G) ∈ Subgroup.normalizer (base S y : Set G) :=
      Subgroup.zpowers_le.mpr (mem_normalizer_base h) (yPow hy hy1 q).2
    have hgi : (yPow hy hy1 q : G)⁻¹ ∈ Subgroup.normalizer (base S y : Set G) :=
      (Subgroup.normalizer (base S y : Set G)).inv_mem hg
    simpa using (Subgroup.mem_normalizer_iff.mp hgi (x : G)).mp x.2⟩
  left_inv x := Subtype.ext (by group)
  right_inv x := Subtype.ext (by group)
  map_mul' x z := by
    apply Subtype.ext
    simp only [Subgroup.coe_mul]
    group

@[simp] private theorem conjBase_coe (h : IsWreathThree S y) (hy : y ^ 3 = 1)
    (hy1 : y ≠ 1) (q : WQ) (x : base S y) :
    ((conjBase h hy hy1 q x : base S y) : G) =
      (yPow hy hy1 q : G) * (x : G) * (yPow hy hy1 q : G)⁻¹ := rfl

private noncomputable def conjBaseHom (h : IsWreathThree S y) (hy : y ^ 3 = 1)
    (hy1 : y ≠ 1) (q : WQ) : base S y →* base S y :=
  (conjBase h hy hy1 q).toMonoidHom

@[simp] private theorem conjBaseHom_coe (h : IsWreathThree S y) (hy : y ^ 3 = 1)
    (hy1 : y ≠ 1) (q : WQ) (x : base S y) :
    ((conjBaseHom h hy hy1 q x : base S y) : G) =
      (yPow hy hy1 q : G) * (x : G) * (yPow hy hy1 q : G)⁻¹ := rfl

private noncomputable def factorS (h : IsWreathThree S y) (hy : y ^ 3 = 1)
    (hy1 : y ≠ 1) (q : WQ) : S →* base S y :=
  (conjBase h hy hy1 q).toMonoidHom.comp (Subgroup.inclusion (le_base_left S y))

private noncomputable def factorD (h : IsWreathThree S y) (hy : y ^ 3 = 1)
    (hy1 : y ≠ 1) (n : ℕ) (e : WD n ≃* S) (q : WQ) : WD n →* base S y :=
  (factorS h hy hy1 q).comp e.toMonoidHom

@[simp] private theorem factorD_coe (h : IsWreathThree S y) (hy : y ^ 3 = 1)
    (hy1 : y ≠ 1) (n : ℕ) (e : WD n ≃* S) (q : WQ) (d : WD n) :
    ((factorD h hy hy1 n e q d : base S y) : G) =
      (yPow hy hy1 q : G) * (e d : G) * (yPow hy hy1 q : G)⁻¹ := by
  rfl

private noncomputable def baseProd (h : IsWreathThree S y) (hy : y ^ 3 = 1)
    (hy1 : y ≠ 1) (n : ℕ) (e : WD n ≃* S) (f : WQ → WD n) : base S y :=
  letI : IsMulCommutative (base S y) := isMulCommutative_base h
  letI : CommGroup (base S y) := IsMulCommutative.instCommGroup
  ∏ i : WQ, factorD h hy hy1 n e i (f i)

private noncomputable def phiG (h : IsWreathThree S y) (hy : y ^ 3 = 1)
    (hy1 : y ≠ 1) (n : ℕ) (e : WD n ≃* S) (w : WD n ≀ᵣ WQ) : G :=
  (baseProd h hy hy1 n e w.left : G) * (yPow hy hy1 w.right : G)

private theorem conjBase_factor (h : IsWreathThree S y) (hy : y ^ 3 = 1)
    (hy1 : y ≠ 1) (n : ℕ) (e : WD n ≃* S) (q i : WQ) (d : WD n) :
    conjBaseHom h hy hy1 q (factorD h hy hy1 n e i d) =
      factorD h hy hy1 n e (q * i) d := by
  apply Subtype.ext
  rw [conjBaseHom_coe, factorD_coe, factorD_coe, map_mul (yPow hy hy1) q i]
  simp only [Subgroup.coe_mul]
  group

private theorem baseProd_mul (h : IsWreathThree S y) (hy : y ^ 3 = 1)
    (hy1 : y ≠ 1) (n : ℕ) (e : WD n ≃* S) (f g : WQ → WD n) (q : WQ) :
    baseProd h hy hy1 n e (f * fun x => g (q⁻¹ * x)) =
      baseProd h hy hy1 n e f * conjBaseHom h hy hy1 q (baseProd h hy hy1 n e g) := by
  letI : IsMulCommutative (base S y) := isMulCommutative_base h
  letI : CommGroup (base S y) := IsMulCommutative.instCommGroup
  simp only [baseProd, Pi.mul_apply, map_mul]
  rw [Finset.prod_mul_distrib]
  congr 1
  rw [map_prod (conjBaseHom h hy hy1 q)
    (fun i => factorD h hy hy1 n e i (g i)) Finset.univ]
  exact Fintype.prod_equiv (Equiv.mulLeft q⁻¹)
    (fun i => factorD h hy hy1 n e i (g (q⁻¹ * i)))
    (fun j => conjBaseHom h hy hy1 q (factorD h hy hy1 n e j (g j)))
    (by
      intro j
      show factorD h hy hy1 n e j (g (q⁻¹ * j)) =
        conjBaseHom h hy hy1 q (factorD h hy hy1 n e (q⁻¹ * j) (g (q⁻¹ * j)))
      rw [conjBase_factor]
      exact congrArg (fun z => factorD h hy hy1 n e z (g (q⁻¹ * j)))
        (mul_inv_cancel_left q j).symm)

private theorem phiG_one (h : IsWreathThree S y) (hy : y ^ 3 = 1) (hy1 : y ≠ 1)
    (n : ℕ) (e : WD n ≃* S) : phiG h hy hy1 n e 1 = 1 := by
  simp [phiG, baseProd]

private theorem phiG_mul (h : IsWreathThree S y) (hy : y ^ 3 = 1) (hy1 : y ≠ 1)
    (n : ℕ) (e : WD n ≃* S) (a b : WD n ≀ᵣ WQ) :
    phiG h hy hy1 n e (a * b) = phiG h hy hy1 n e a * phiG h hy hy1 n e b := by
  have hbm : baseProd h hy hy1 n e (a.left * fun x => b.left (a.right⁻¹ * x)) =
      baseProd h hy hy1 n e a.left *
        conjBaseHom h hy hy1 a.right (baseProd h hy hy1 n e b.left) :=
    baseProd_mul h hy hy1 n e a.left b.left a.right
  calc
    phiG h hy hy1 n e (a * b) =
        ((baseProd h hy hy1 n e (a.left * fun x => b.left (a.right⁻¹ * x)) :
            base S y) : G) * (yPow hy hy1 (a.right * b.right) : G) := by
      simp only [phiG, RegularWreathProduct.mul_left, RegularWreathProduct.mul_right]
      rfl
    _ = (((baseProd h hy hy1 n e a.left : base S y) *
          conjBaseHom h hy hy1 a.right (baseProd h hy hy1 n e b.left) : base S y) : G) *
        (yPow hy hy1 (a.right * b.right) : G) :=
      congrArg (fun z : base S y => ((z : G) * (yPow hy hy1 (a.right * b.right) : G))) hbm
    _ = phiG h hy hy1 n e a * phiG h hy hy1 n e b := by
      simp only [phiG, map_mul, Subgroup.coe_mul, conjBaseHom_coe]
      group

private theorem phiG_mem (h : IsWreathThree S y) (hy : y ^ 3 = 1) (hy1 : y ≠ 1)
    (n : ℕ) (e : WD n ≃* S) (w : WD n ≀ᵣ WQ) :
    phiG h hy hy1 n e w ∈ base S y ⊔ Subgroup.zpowers y := by
  rw [phiG]
  exact Subgroup.mul_mem_sup (baseProd h hy hy1 n e w.left).2 (yPow hy hy1 w.right).2

private noncomputable def phiHom (h : IsWreathThree S y) (hy : y ^ 3 = 1) (hy1 : y ≠ 1)
    (n : ℕ) (e : WD n ≃* S) : (WD n ≀ᵣ WQ) →* G where
  toFun := phiG h hy hy1 n e
  map_one' := phiG_one h hy hy1 n e
  map_mul' := phiG_mul h hy hy1 n e

private noncomputable def phi (h : IsWreathThree S y) (hy : y ^ 3 = 1) (hy1 : y ≠ 1)
    (n : ℕ) (e : WD n ≃* S) :
    (WD n ≀ᵣ WQ) →* ↥(base S y ⊔ Subgroup.zpowers y) :=
  (phiHom h hy hy1 n e).codRestrict _ (fun w => phiG_mem h hy hy1 n e w)

@[simp] private theorem phi_apply (h : IsWreathThree S y) (hy : y ^ 3 = 1)
    (hy1 : y ≠ 1) (n : ℕ) (e : WD n ≃* S) (w : WD n ≀ᵣ WQ) :
    ((phi h hy hy1 n e w : ↥(base S y ⊔ Subgroup.zpowers y)) : G) =
      phiG h hy hy1 n e w := rfl



private theorem phiG_single (h : IsWreathThree S y) (hy : y ^ 3 = 1) (hy1 : y ≠ 1)
    (n : ℕ) (e : WD n ≃* S) (i : WQ) (d : WD n) :
    phiG h hy hy1 n e ⟨Pi.mulSingle i d, 1⟩ = (factorD h hy hy1 n e i d : G) := by
  have hprod : baseProd h hy hy1 n e (Pi.mulSingle i d) =
      factorD h hy hy1 n e i d := by
    letI : IsMulCommutative (base S y) := isMulCommutative_base h
    letI : CommGroup (base S y) := IsMulCommutative.instCommGroup
    rw [baseProd, Finset.prod_eq_single i]
    · simp
    · intro b _ hb
      rw [Pi.mulSingle_eq_of_ne hb, map_one]
    · intro hi
      exact absurd (Finset.mem_univ i) hi
  simp only [phiG, hprod, Subgroup.coe_mul, Subgroup.coe_one, one_mul]
  simp

private theorem phiG_range (h : IsWreathThree S y) (hy : y ^ 3 = 1) (hy1 : y ≠ 1)
    (n : ℕ) (e : WD n ≃* S) :
    (phiHom h hy hy1 n e).range = (base S y ⊔ Subgroup.zpowers y : Subgroup G) := by
  let q1 : WQ := Multiplicative.ofAdd (1 : ZMod 3)
  let q2 : WQ := Multiplicative.ofAdd (2 : ZMod 3)
  have hq1 : (yPow hy hy1 q1 : G) = y := by
    change y ^ (Multiplicative.toAdd q1).val = y
    rw [show Multiplicative.toAdd q1 = (1 : ZMod 3) from rfl,
      show (1 : ZMod 3).val = 1 from by decide, pow_one]
  have hq2 : (yPow hy hy1 q2 : G) = y ^ 2 := by
    change y ^ (Multiplicative.toAdd q2).val = y ^ 2
    rw [show Multiplicative.toAdd q2 = (2 : ZMod 3) from rfl,
      show (2 : ZMod 3).val = 2 from by decide]
  apply le_antisymm
  · rintro _ ⟨w, rfl⟩
    exact phiG_mem h hy hy1 n e w
  · apply sup_le
    · rw [base]
      apply sup_le
      · apply sup_le
        · intro s hs
          refine ⟨⟨Pi.mulSingle (1 : WQ) (e.symm ⟨s, hs⟩), 1⟩, ?_⟩
          change phiG h hy hy1 n e ⟨Pi.mulSingle (1 : WQ) (e.symm ⟨s, hs⟩), 1⟩ = s
          rw [phiG_single]
          change (yPow hy hy1 (1 : WQ) : G) * ((e (e.symm ⟨s, hs⟩) : S) : G) *
            (yPow hy hy1 (1 : WQ) : G)⁻¹ = s
          simp
        · intro z hz
          rw [Subgroup.mem_map] at hz
          obtain ⟨s, hs, rfl⟩ := hz
          refine ⟨⟨Pi.mulSingle q1 (e.symm ⟨s, hs⟩), 1⟩, ?_⟩
          change phiG h hy hy1 n e ⟨Pi.mulSingle q1 (e.symm ⟨s, hs⟩), 1⟩ =
            y * (s : G) * y⁻¹
          rw [phiG_single]
          change (yPow hy hy1 q1 : G) * ((e (e.symm ⟨s, hs⟩) : S) : G) *
            (yPow hy hy1 q1 : G)⁻¹ = y * (s : G) * y⁻¹
          simp [hq1]
      · intro z hz
        rw [Subgroup.mem_map] at hz
        obtain ⟨s, hs, rfl⟩ := hz
        refine ⟨⟨Pi.mulSingle q2 (e.symm ⟨s, hs⟩), 1⟩, ?_⟩
        change phiG h hy hy1 n e ⟨Pi.mulSingle q2 (e.symm ⟨s, hs⟩), 1⟩ =
          y ^ 2 * (s : G) * (y ^ 2)⁻¹
        rw [phiG_single]
        change (yPow hy hy1 q2 : G) * ((e (e.symm ⟨s, hs⟩) : S) : G) *
          (yPow hy hy1 q2 : G)⁻¹ = y ^ 2 * (s : G) * (y ^ 2)⁻¹
        simp [hq2]
    · rw [Subgroup.zpowers_le]
      refine ⟨⟨1, q1⟩, ?_⟩
      change phiG h hy hy1 n e ⟨1, q1⟩ = y
      simp [phiG, baseProd, hq1]

private theorem phi_surjective (h : IsWreathThree S y) (hy : y ^ 3 = 1) (hy1 : y ≠ 1)
    (n : ℕ) (e : WD n ≃* S) : Function.Surjective (phi h hy hy1 n e) := by
  intro p
  have hp : (p : G) ∈ (phiHom h hy hy1 n e).range := by
    rw [phiG_range h hy hy1 n e]
    exact p.2
  obtain ⟨w, hw⟩ := MonoidHom.mem_range.mp hp
  exact ⟨w, Subtype.ext hw⟩

private theorem card_WD (n : ℕ) : Nat.card (WD n) = 3 ^ n := by
  haveI : NeZero (3 ^ n) := ⟨pow_ne_zero n (by norm_num)⟩
  rw [Nat.card_eq_fintype_card, Fintype.card_multiplicative, ZMod.card]

private theorem card_WQ : Nat.card WQ = 3 := by
  rw [Nat.card_eq_fintype_card, Fintype.card_multiplicative, ZMod.card]

private theorem card_wreath (n : ℕ) :
    Nat.card (WD n ≀ᵣ WQ) = 3 ^ (3 * n + 1) := by
  haveI : NeZero (3 ^ n) := ⟨pow_ne_zero n (by norm_num)⟩
  rw [RegularWreathProduct.card, card_WD, card_WQ, ← pow_mul, ← pow_succ]
  congr 1
  omega

private theorem card_P [Finite G] (h : IsWreathThree S y) (hy : y ^ 3 = 1) (n : ℕ)
    (hcard : Nat.card S = 3 ^ n) :
    Nat.card ↥(base S y ⊔ Subgroup.zpowers y) = 3 ^ (3 * n + 1) := by
  rw [card_sup_zpowers h hy, h.card_base, hcard, ← pow_mul, ← pow_succ']
  congr 1
  omega

theorem exists_mulEquiv_regularWreathProduct [Finite G] {S : Subgroup G} {y : G}
    (h : IsWreathThree S y) (hy : y ^ 3 = 1) :
    ∃ n : ℕ, 1 ≤ n ∧ Nat.card S = 3 ^ n ∧
      Nonempty (↥(base S y ⊔ Subgroup.zpowers y) ≃*
        (Multiplicative (ZMod (3 ^ n)) ≀ᵣ Multiplicative (ZMod 3))) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI : Finite S := Subtype.finite
  obtain ⟨n, hcard⟩ := IsPGroup.exists_card_eq h.isPGroup
  have hn : 1 ≤ n := by
    have hn0 : n ≠ 0 := by
      rintro rfl
      have h1 : Nat.card S = 1 := by simpa using hcard
      exact h.ne_bot (Subgroup.card_eq_one.mp h1)
    omega
  have hy1 : y ≠ 1 := fun h1 => not_mem_base h (h1 ▸ (base S y).one_mem)
  let e : WD n ≃* S :=
    (MulEquiv.cast (M := fun k => Multiplicative (ZMod k)) hcard.symm).trans
      (zmodCyclicMulEquiv h.isCyclic)
  haveI : NeZero (3 ^ n) := ⟨pow_ne_zero n (by norm_num)⟩
  haveI : Fintype (WD n) := inferInstance
  haveI : Fintype WQ := inferInstance
  haveI : Fintype (WD n ≀ᵣ WQ) :=
    Fintype.ofEquiv ((WQ → WD n) × WQ)
      (RegularWreathProduct.equivProd (WD n) WQ).symm
  haveI : Finite ↥(base S y ⊔ Subgroup.zpowers y) := Subtype.finite
  haveI : Fintype ↥(base S y ⊔ Subgroup.zpowers y) := Fintype.ofFinite _
  have hcardDom : Nat.card (WD n ≀ᵣ WQ) = 3 ^ (3 * n + 1) := card_wreath n
  have hcardP : Nat.card ↥(base S y ⊔ Subgroup.zpowers y) = 3 ^ (3 * n + 1) :=
    card_P h hy n hcard
  have hbij : Function.Bijective (phi h hy hy1 n e) := by
    refine (Fintype.bijective_iff_surjective_and_card (phi h hy hy1 n e)).mpr
      ⟨phi_surjective h hy hy1 n e, ?_⟩
    rw [← Nat.card_eq_fintype_card (α := WD n ≀ᵣ WQ),
      ← Nat.card_eq_fintype_card (α := ↥(base S y ⊔ Subgroup.zpowers y)),
      hcardDom, hcardP]
  refine ⟨n, hn, hcard, ?_⟩
  exact ⟨(MulEquiv.ofBijective (phi h hy hy1 n e) hbij).symm⟩

end CFSG.GroupTheory.WreathThree

end
