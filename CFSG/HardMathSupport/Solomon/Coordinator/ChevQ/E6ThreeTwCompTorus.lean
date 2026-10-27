module

public import CFSG.HardMathSupport.Lang.TwE6Step3.LangTorus
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeTwLineDefs


public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.RankThree.E6 CFSG.RankThree.Lattice
  CFSG.RankThree.PartOne.KE6 CFSG.HardMathSupport.Lang.SeitzPlane
  CFSG.HardMathSupport.Lang.TwE6Step3

set_option linter.unusedSectionVars false

section Group

variable {G : Type*} [CommGroup G]

theorem twCompTor_pow_sq_add_one {x y z : G} {q : ℕ} (h1 : y * x ^ q = 1)
    (h2 : z * y ^ q = 1) (h3 : z * y * x = 1) : x ^ (q ^ 2 + 1) = x ^ q := by
  have h : y ^ q * x ^ (q * q) = 1 := by
    have h' := congrArg (fun t => t ^ q) h1
    simpa only [mul_pow, ← pow_mul, one_pow] using h'
  have hz : z = x ^ (q * q) := by
    calc z = z * (y ^ q * x ^ (q * q)) := by rw [h, mul_one]
      _ = (z * y ^ q) * x ^ (q * q) := (mul_assoc _ _ _).symm
      _ = x ^ (q * q) := by rw [h2, one_mul]
  calc x ^ (q ^ 2 + 1) = x ^ (q * q) * x := by rw [sq, pow_succ]
    _ = z * x := by rw [hz]
    _ = z * x * (y * x ^ q) := by rw [h1, mul_one]
    _ = (z * y * x) * x ^ q := by ac_rfl
    _ = x ^ q := by rw [h3, one_mul]

theorem twCompTor_pow_three_of_sq {x : G} {s : ℕ} (h9 : x ^ 9 = 1)
    (h : x ^ ((3 * s + 2) ^ 2 + 1) = x ^ (3 * s + 2)) : x ^ 3 = 1 := by
  have e : (3 * s + 2) ^ 2 + 1 = 9 * (s * s + s) + (3 * s + 2 + 3) := by ring
  rw [e, pow_add x (9 * (s * s + s)) (3 * s + 2 + 3), pow_mul, h9, one_pow, one_mul,
    pow_add x (3 * s + 2) 3] at h
  have h' : x ^ (3 * s + 2) * x ^ 3 = x ^ (3 * s + 2) * 1 := by rw [h, mul_one]
  exact mul_left_cancel h'

theorem twCompTor_eq_of_pow_three {x y : G} {s : ℕ} (hx : x ^ 3 = 1)
    (h : y * x ^ (3 * s + 2) = 1) : y = x := by
  have e : x ^ (3 * s + 2) = x ^ 2 := by
    rw [pow_add, pow_mul, hx, one_pow, one_mul]
  rw [e] at h
  have h' : x * x ^ 2 = 1 := by rw [← pow_succ']; exact hx
  exact mul_right_cancel (h.trans h'.symm)

theorem twCompTor_eq_of_inv_mul_inv {a x : G} (hx : x ^ 3 = 1) (h : a⁻¹ * x⁻¹ = x) : x = a := by
  have h1 : a⁻¹ = x * x := by
    calc a⁻¹ = a⁻¹ * x⁻¹ * x := (inv_mul_cancel_right _ _).symm
      _ = x * x := by rw [h]
  have h2 : (x * x)⁻¹ = x := inv_eq_of_mul_eq_one_right (by rw [← pow_three']; exact hx)
  rw [← h1, inv_inv] at h2
  exact h2.symm

end Group

section RootChar

variable {Ω : Type} [Field Ω]

theorem twCompTor_rootChar_pow_eq_one {n : ℕ} {b : Fin Tag.E6.rank → Ωˣ}
    (hb : ∀ i, b i ^ n = 1) (v : Fin Tag.E6.rank → ℤ) : rootChar b v ^ n = 1 := by
  rw [rootChar, ← Finset.prod_pow]
  refine Finset.prod_eq_one fun i _ => ?_
  rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hb i, one_zpow]

theorem twCompTor_rootChar_single (b : Fin Tag.E6.rank → Ωˣ) (j : Fin Tag.E6.rank) :
    rootChar b (Pi.single j 1) = b j := by
  simpa using rootChar_nsmul_single b j 1

theorem twCompTor_rootChar_neg_mul (b : Fin Tag.E6.rank → Ωˣ) (v : Fin Tag.E6.rank → ℤ) :
    rootChar b (-v) * rootChar b v = 1 := by
  rw [← rootChar_add, neg_add_cancel, rootChar_zero]

theorem twCompTor_rootChar_vec (b : Fin Tag.E6.rank → Ωˣ) (a₀ a₁ a₂ a₃ a₄ a₅ : ℤ) :
    rootChar b ![a₀, a₁, a₂, a₃, a₄, a₅] =
      b 0 ^ a₀ * b 1 ^ a₁ * b 2 ^ a₂ * b 3 ^ a₃ * b 4 ^ a₄ * b 5 ^ a₅ := by
  change ∏ i : Fin 6, b i ^ (![a₀, a₁, a₂, a₃, a₄, a₅] : Fin 6 → ℤ) i = _
  rw [Fin.prod_univ_six]
  rfl

theorem twCompTor_rootDiagUnit_pow (b : Fin Tag.E6.rank → Ωˣ) (n : ℕ) :
    rootDiagUnit Tag.E6 b ^ n = rootDiagUnit Tag.E6 (b ^ n) :=
  (map_pow (rootDiagUnitHom Tag.E6 Ω) b n).symm

end RootChar

section Diag

variable {Ω : Type} [Field Ω]

theorem twCompTor_pow_eq_one_of {b : Fin Tag.E6.rank → Ωˣ} {n : ℕ}
    (h : rootDiagUnit Tag.E6 b ^ n = 1) (i : Fin Tag.E6.rank) : b i ^ n = 1 := by
  rw [twCompTor_rootDiagUnit_pow] at h
  have h' : b ^ n = 1 := rootDiagUnit_injective (h.trans rootDiagUnit_one.symm)
  simpa using congrFun h' i

theorem twCompTor_rootDiagUnit_pow_eq_one {b : Fin Tag.E6.rank → Ωˣ} {n : ℕ}
    (h : ∀ i, b i ^ n = 1) : rootDiagUnit Tag.E6 b ^ n = 1 := by
  rw [twCompTor_rootDiagUnit_pow, show b ^ n = 1 from funext fun i => by simpa using h i]
  exact rootDiagUnit_one

end Diag

section Theta

variable {Ω : Type} [Field Ω] {Fr : Ω →+* Ω} {q : ℕ}


theorem twCompTor_rootChar_fixed (hFr : ∀ c, Fr c = c ^ q) {b : Fin Tag.E6.rank → Ωˣ}
    (hθ : tw6Theta Ω Fr (rootDiagUnit Tag.E6 b) = rootDiagUnit Tag.E6 b)
    (v : Fin Tag.E6.rank → ℤ) :
    rootChar b (e6T3W • v) * rootChar b v ^ q = 1 := by
  obtain ⟨b', hb', hchar⟩ := tw6ThetaConj_rootDiagUnit hFr 1 b
  have h1 : tw6ThetaConj Ω Fr 1 (rootDiagUnit Tag.E6 b) =
      tw6Theta Ω Fr (rootDiagUnit Tag.E6 b) := by
    rw [tw6ThetaConj_apply, canonicalRep_one, inv_one, one_mul, mul_one, one_mul, mul_one]
  have hbb : b' = b := rootDiagUnit_injective (hb'.symm.trans (h1.trans hθ))
  have h2 := hchar (e6T3W • v)
  rw [hbb] at h2
  simp only [inv_one, mul_one, one_mul, inv_smul_smul] at h2
  rw [h2, ← mul_pow, twCompTor_rootChar_neg_mul, one_pow]

theorem twCompTor_rootChar_pow_sq (hFr : ∀ c, Fr c = c ^ q) {b : Fin Tag.E6.rank → Ωˣ}
    (hθ : tw6Theta Ω Fr (rootDiagUnit Tag.E6 b) = rootDiagUnit Tag.E6 b)
    (v : Fin Tag.E6.rank → ℤ) : rootChar b v ^ (q ^ 2 + 1) = rootChar b v ^ q := by
  have h3 : rootChar b (e6T3W • e6T3W • v) * rootChar b (e6T3W • v) * rootChar b v = 1 := by
    rw [← rootChar_add, ← rootChar_add, e6T3_lattice, rootChar_zero]
  exact twCompTor_pow_sq_add_one (twCompTor_rootChar_fixed hFr hθ v)
    (twCompTor_rootChar_fixed hFr hθ (e6T3W • v)) h3

theorem twTheta_torus_pow_three_of_pow_nine (hFr : ∀ c, Fr c = c ^ q) (h3 : 3 ∣ q + 1)
    {d : ModGL Tag.E6 Ω} (hd : d ∈ torusGroup Tag.E6 Ω) (hθ : tw6Theta Ω Fr d = d)
    (h9 : d ^ 9 = 1) : d ^ 3 = 1 := by
  obtain ⟨b, rfl⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup hd
  obtain ⟨s, hs⟩ : ∃ s, q = 3 * s + 2 := by
    obtain ⟨t, ht⟩ := h3
    exact ⟨t - 1, by omega⟩
  have hb9 := twCompTor_pow_eq_one_of h9
  have hb3 : ∀ i, b i ^ 3 = 1 := fun i => by
    rw [← twCompTor_rootChar_single b i]
    refine twCompTor_pow_three_of_sq (s := s) (twCompTor_rootChar_pow_eq_one hb9 _) ?_
    have := twCompTor_rootChar_pow_sq hFr hθ (Pi.single i 1)
    rwa [hs] at this
  exact twCompTor_rootDiagUnit_pow_eq_one hb3

theorem twCompTor_rootChar_eq_of_pow_three (hFr : ∀ c, Fr c = c ^ q) (h3 : 3 ∣ q + 1)
    {b : Fin Tag.E6.rank → Ωˣ} (hb3 : ∀ i, b i ^ 3 = 1)
    (hθ : tw6Theta Ω Fr (rootDiagUnit Tag.E6 b) = rootDiagUnit Tag.E6 b)
    (v : Fin Tag.E6.rank → ℤ) : rootChar b (e6T3W • v) = rootChar b v := by
  obtain ⟨s, hs⟩ : ∃ s, q = 3 * s + 2 := by
    obtain ⟨t, ht⟩ := h3
    exact ⟨t - 1, by omega⟩
  have h := twCompTor_rootChar_fixed hFr hθ v
  rw [hs] at h
  exact twCompTor_eq_of_pow_three (twCompTor_rootChar_pow_eq_one hb3 v) h

theorem twCompTor_smul_single_two :
    e6T3W • (Pi.single 2 1 : Fin Tag.E6.rank → ℤ) = Pi.single 3 1 := by
  rw [← weylMatrix_mulVec, weylMatrix_e6T3W]
  decide +kernel

theorem twCompTor_smul_single_four :
    e6T3W • (Pi.single 4 1 : Fin Tag.E6.rank → ℤ) = ![0, -1, 0, -1, -1, 0] := by
  rw [← weylMatrix_mulVec, weylMatrix_e6T3W, Matrix.mulVec_single_one]
  funext j
  fin_cases j <;> rfl

theorem twCompTor_smul_single_five :
    e6T3W • (Pi.single 5 1 : Fin Tag.E6.rank → ℤ) = ![-1, 0, -1, -1, -1, -1] := by
  rw [← weylMatrix_mulVec, weylMatrix_e6T3W, Matrix.mulVec_single_one]
  funext j
  fin_cases j <;> rfl

theorem twTheta_torus_card_three_le (hFr : ∀ c, Fr c = c ^ q) (h3 : 3 ∣ q + 1) :
    Nat.card {d : ModGL Tag.E6 Ω //
      d ∈ torusGroup Tag.E6 Ω ∧ tw6Theta Ω Fr d = d ∧ d ^ 3 = 1} ≤ 27 := by
  classical
  let g : rootsOfUnity 3 Ω × rootsOfUnity 3 Ω × rootsOfUnity 3 Ω → ModGL Tag.E6 Ω := fun z =>
    rootDiagUnit Tag.E6 ![(z.1 : Ωˣ), (z.2.1 : Ωˣ), (z.2.2 : Ωˣ), (z.2.2 : Ωˣ),
      (z.2.1 : Ωˣ) * (z.2.2 : Ωˣ), (z.1 : Ωˣ) * (z.2.1 : Ωˣ)]
  have hex : ∀ d : {d : ModGL Tag.E6 Ω //
      d ∈ torusGroup Tag.E6 Ω ∧ tw6Theta Ω Fr d = d ∧ d ^ 3 = 1}, ∃ z, g z = d.1 := by
    rintro ⟨d, hd, hθ, hd3⟩
    obtain ⟨b, rfl⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup hd
    have hb3 := twCompTor_pow_eq_one_of hd3
    have hφ := twCompTor_rootChar_eq_of_pow_three hFr h3 hb3 hθ
    have e2 : b 3 = b 2 := by
      have := hφ (Pi.single 2 1)
      rwa [twCompTor_smul_single_two, twCompTor_rootChar_single, twCompTor_rootChar_single] at this
    have e4 : b 4 = b 1 * b 3 := by
      have := hφ (Pi.single 4 1)
      rw [twCompTor_smul_single_four, twCompTor_rootChar_vec, twCompTor_rootChar_single] at this
      simp only [zpow_zero, zpow_neg, zpow_one, one_mul, mul_one] at this
      exact twCompTor_eq_of_inv_mul_inv (hb3 4) (by rwa [mul_inv])
    have e5 : b 5 = b 0 * b 2 * b 3 * b 4 := by
      have := hφ (Pi.single 5 1)
      rw [twCompTor_smul_single_five, twCompTor_rootChar_vec, twCompTor_rootChar_single] at this
      simp only [zpow_zero, zpow_neg, zpow_one, one_mul, mul_one] at this
      exact twCompTor_eq_of_inv_mul_inv (hb3 5) (by rwa [mul_inv, mul_inv, mul_inv])
    have e4' : b 4 = b 1 * b 2 := by rw [e4, e2]
    have e5' : b 5 = b 0 * b 1 := by
      calc b 5 = b 0 * b 2 * b 2 * (b 1 * b 2) := by rw [e5, e2, e4']
        _ = b 0 * b 1 * (b 2 * (b 2 * b 2)) := by ac_rfl
        _ = b 0 * b 1 * b 2 ^ 3 := by rw [pow_three]
        _ = b 0 * b 1 := by rw [hb3 2, mul_one]
    refine ⟨(⟨b 0, (mem_rootsOfUnity 3 _).2 (hb3 0)⟩, ⟨b 1, (mem_rootsOfUnity 3 _).2 (hb3 1)⟩,
      ⟨b 2, (mem_rootsOfUnity 3 _).2 (hb3 2)⟩), ?_⟩
    show rootDiagUnit Tag.E6 _ = rootDiagUnit Tag.E6 b
    congr 1
    funext i
    fin_cases i
    · rfl
    · rfl
    · rfl
    · exact e2.symm
    · exact e4'.symm
    · exact e5'.symm
  choose f hf using hex
  have hinj : Function.Injective f := fun d₁ d₂ h => Subtype.ext (by rw [← hf d₁, ← hf d₂, h])
  calc Nat.card {d : ModGL Tag.E6 Ω //
        d ∈ torusGroup Tag.E6 Ω ∧ tw6Theta Ω Fr d = d ∧ d ^ 3 = 1}
      ≤ Nat.card (rootsOfUnity 3 Ω × rootsOfUnity 3 Ω × rootsOfUnity 3 Ω) :=
        Nat.card_le_card_of_injective f hinj
    _ = Nat.card (rootsOfUnity 3 Ω) * (Nat.card (rootsOfUnity 3 Ω) *
        Nat.card (rootsOfUnity 3 Ω)) := by rw [Nat.card_prod, Nat.card_prod]
    _ ≤ 3 * (3 * 3) := by
      have h := card_rootsOfUnity Ω 3
      exact Nat.mul_le_mul h (Nat.mul_le_mul h h)
    _ = 27 := by norm_num

end Theta

section Blocks

variable {Ω : Type} [Field Ω]

theorem twRootChar_mem_zpowers_of_forall {ω : Ωˣ} (hω3 : ω ^ 3 = 1) (hω1 : ω ≠ 1)
    {b : Fin Tag.E6.rank → Ωˣ} (hb : ∀ i, ∀ α ∈ twE6FrameS i, rootChar b α = 1) :
    rootDiagUnit Tag.E6 b ∈ Subgroup.zpowers (rootDiagUnit Tag.E6 (twLineChar ω)) := by
  have m1 : (![0, 0, 1, 0, 0, 0] : Fin Tag.E6.rank → ℤ) ∈ twE6FrameS 0 :=
    show (![0, 0, 1, 0, 0, 0] : Fin Tag.E6.rank → ℤ) ∈ twE6FrameL 0 from
      List.mem_cons_self
  have m2 : (![0, 0, 0, 1, 0, 0] : Fin Tag.E6.rank → ℤ) ∈ twE6FrameS 0 :=
    show (![0, 0, 0, 1, 0, 0] : Fin Tag.E6.rank → ℤ) ∈ twE6FrameL 0 from
      List.mem_cons_of_mem _ List.mem_cons_self
  have m3 : (![0, 0, 0, 0, 0, 1] : Fin Tag.E6.rank → ℤ) ∈ twE6FrameS 1 :=
    show (![0, 0, 0, 0, 0, 1] : Fin Tag.E6.rank → ℤ) ∈ twE6FrameL 1 from
      List.mem_cons_self
  have m4 : (![1, 0, 1, 1, 1, 0] : Fin Tag.E6.rank → ℤ) ∈ twE6FrameS 1 :=
    show (![1, 0, 1, 1, 1, 0] : Fin Tag.E6.rank → ℤ) ∈ twE6FrameL 1 from
      List.mem_cons_of_mem _ List.mem_cons_self
  have m5 : (![1, 1, 1, 1, 0, 0] : Fin Tag.E6.rank → ℤ) ∈ twE6FrameS 2 :=
    show (![1, 1, 1, 1, 0, 0] : Fin Tag.E6.rank → ℤ) ∈ twE6FrameL 2 from
      List.mem_cons_of_mem _ List.mem_cons_self
  have m6 : (![0, 1, 1, 2, 2, 1] : Fin Tag.E6.rank → ℤ) ∈ twE6FrameS 2 :=
    show (![0, 1, 1, 2, 2, 1] : Fin Tag.E6.rank → ℤ) ∈ twE6FrameL 2 from
      List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)
  have r1 := hb 0 _ m1
  have r2 := hb 0 _ m2
  have r3 := hb 1 _ m3
  have r4 := hb 1 _ m4
  have r5 := hb 2 _ m5
  have r6 := hb 2 _ m6
  rw [twCompTor_rootChar_vec] at r1 r2 r3 r4 r5 r6
  simp only [zpow_zero, zpow_one, one_mul, mul_one] at r1 r2 r3 r4 r5
  have h2 : b 2 = 1 := r1
  have h3 : b 3 = 1 := r2
  have h5 : b 5 = 1 := r3
  simp [h2, h3, h5] at r4 r5 r6
  have h41 : b 4 = b 1 := mul_left_cancel (r4.trans r5.symm)
  have hζ3 : b 1 ^ 3 = 1 := by
    rw [h41] at r6
    rw [pow_succ']
    exact r6
  have h0 : b 0 = b 1 ^ 2 := by
    have h01 : b 0 = (b 1)⁻¹ := eq_inv_of_mul_eq_one_left r5
    rw [h01]
    refine inv_eq_of_mul_eq_one_right ?_
    rw [← pow_succ']
    exact hζ3
  have hprim : IsPrimitiveRoot ω 3 := by
    have := IsPrimitiveRoot.orderOf ω
    rwa [orderOf_eq_prime hω3 hω1] at this
  obtain ⟨k, -, hk⟩ := hprim.eq_pow_of_mem_rootsOfUnity ((mem_rootsOfUnity 3 (b 1)).2 hζ3)
  have hbk : b = twLineChar ω ^ k := by
    funext i
    rw [Pi.pow_apply]
    fin_cases i
    · show b 0 = (ω ^ 2) ^ k
      rw [h0, ← hk, ← pow_mul, ← pow_mul, mul_comm]
    · show b 1 = ω ^ k
      exact hk.symm
    · show b 2 = 1 ^ k
      rw [one_pow]; exact h2
    · show b 3 = 1 ^ k
      rw [one_pow]; exact h3
    · show b 4 = ω ^ k
      rw [h41]; exact hk.symm
    · show b 5 = 1 ^ k
      rw [one_pow]; exact h5
  rw [hbk, ← twCompTor_rootDiagUnit_pow]
  exact Subgroup.pow_mem _ (Subgroup.mem_zpowers _) k

end Blocks

section Commute

variable {Ω : Type} [Field Ω]


theorem twCompTor_isRoot_of_mem_frame {i : Fin 3} {α : Fin Tag.E6.rank → ℤ}
    (hα : α ∈ twE6FrameS i) : IsRoot Tag.E6 α := by
  have h : ∀ j : Fin 3, ∀ β ∈ twE6FrameL j, β ∈ rootFinset .E6 := by decide +kernel
  exact mem_rootFinset.1 (h i α hα)

theorem twTorus_mem_zpowers_of_commute {ω : Ωˣ} (hω3 : ω ^ 3 = 1) (hω1 : ω ≠ 1)
    {m : ModGL Tag.E6 Ω} (hm : m ∈ torusGroup Tag.E6 Ω)
    (hc : ∀ i, ∀ y ∈ rootSpan Tag.E6 Ω (twE6FrameS i), m * y = y * m) :
    m ∈ Subgroup.zpowers (rootDiagUnit Tag.E6 (twLineChar ω)) := by
  obtain ⟨b, rfl⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup hm
  refine twRootChar_mem_zpowers_of_forall hω3 hω1 fun i α hα => ?_
  have hroot := twCompTor_isRoot_of_mem_frame hα
  have h := hc i _ (pinnedX_mem_rootSpan (K := Ω) hα 1)
  have h2 := rootDiagUnit_conj_pinnedX b hroot (1 : Ω)
  have h3 : rootDiagUnit Tag.E6 b * pinnedX Tag.E6 Ω α 1 * (rootDiagUnit Tag.E6 b)⁻¹ =
      pinnedX Tag.E6 Ω α 1 := by
    rw [h, mul_assoc, mul_inv_cancel, mul_one]
  rw [h3] at h2
  have h4 := pinnedX_injective Tag.E6 Ω α h2
  exact Units.ext (by simpa using h4.symm)

end Commute

end CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three
