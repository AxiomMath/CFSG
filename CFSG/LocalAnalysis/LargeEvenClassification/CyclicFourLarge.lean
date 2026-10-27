module

public import CFSG.LocalAnalysis.LargeEvenClassification.CyclicFourScalarFree
public import CFSG.LocalAnalysis.LargeEvenClassification.CyclicFourReplacement
public import CFSG.LocalAnalysis.LargeEvenClassification.LargeExponentFourGenerators
public import CFSG.LocalAnalysis.LargeEvenClassification.AbelianCoordinates

public section

namespace CFSG.LargeEvenClassification.Helpers

@[expose] def powerKernelEquivOfMulEquiv {A B : Type*} [CommGroup A] [CommGroup B]
    (e : A ≃* B) (k : ℕ) :
    (powMonoidHom k : A →* A).ker ≃* (powMonoidHom k : B →* B).ker where
  toFun x := ⟨e x.val, by
    change (e x.val) ^ k = 1
    rw [← map_pow, show x.val ^ k = 1 from x.property, map_one]⟩
  invFun x := ⟨e.symm x.val, by
    change (e.symm x.val) ^ k = 1
    rw [← map_pow, show x.val ^ k = 1 from x.property, map_one]⟩
  left_inv x := Subtype.ext (e.symm_apply_apply x.val)
  right_inv x := Subtype.ext (e.apply_symm_apply x.val)
  map_mul' x y := Subtype.ext (map_mul e x.val y.val)

@[expose] def prodPowerKernelEquiv (A B : Type*) [CommGroup A] [CommGroup B] (k : ℕ) :
    (powMonoidHom k : A × B →* A × B).ker ≃*
      (powMonoidHom k : A →* A).ker × (powMonoidHom k : B →* B).ker where
  toFun x := (⟨x.val.1, congrArg Prod.fst (show x.val ^ k = 1 from x.property)⟩,
    ⟨x.val.2, congrArg Prod.snd (show x.val ^ k = 1 from x.property)⟩)
  invFun x := ⟨(x.1.val, x.2.val), Prod.ext x.1.property x.2.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl

theorem power_kernel_card_embedding_le {A B : Type*} [CommGroup A] [CommGroup B]
    [Finite B] (f : A →* B) (hf : Function.Injective f) (k : ℕ) :
    Nat.card (powMonoidHom k : A →* A).ker ≤ Nat.card (powMonoidHom k : B →* B).ker := by
  let embedding : (powMonoidHom k : A →* A).ker → (powMonoidHom k : B →* B).ker :=
    fun x => ⟨f x.val, by
      change (f x.val) ^ k = 1
      rw [← map_pow, show x.val ^ k = 1 from x.property, map_one]⟩
  apply Nat.card_le_card_of_injective embedding
  intro x y h
  apply Subtype.ext
  exact hf (congrArg Subtype.val h)

theorem cyclic_pair_power_kernel_card (m n k : ℕ) [NeZero m] [NeZero n] :
    Nat.card (powMonoidHom k :
      Multiplicative (ZMod m) × Multiplicative (ZMod n) →*
        Multiplicative (ZMod m) × Multiplicative (ZMod n)).ker =
        Nat.gcd m k * Nat.gcd n k := by
  rw [Nat.card_congr (prodPowerKernelEquiv _ _ k).toEquiv, Nat.card_prod,
    IsCyclic.card_powMonoidHom_ker, IsCyclic.card_powMonoidHom_ker]
  simp only [Nat.card_congr Multiplicative.ofAdd.symm, Nat.card_zmod]

set_option maxHeartbeats 1000000 in
theorem rank_two_abelian_overgroup_large_coordinates {R M : Type*}
    [CommGroup R] [CommGroup M] [Finite M]
    (hpM : IsPGroup 2 M) (hrank : pGeneratorRank 2 M ≤ 2)
    (embedding : R →* M) (hinjective : Function.Injective embedding)
    (upper : ℕ) (hupper : 3 ≤ upper)
    (coordinates : R ≃* Multiplicative (ZMod (2 ^ upper)) × Multiplicative (ZMod 8)) :
    ∃ c d : ℕ, d ≤ c ∧ 3 ≤ d ∧
      Nonempty (M ≃* Multiplicative (ZMod (2 ^ c)) × Multiplicative (ZMod (2 ^ d))) := by
  let : NeZero (2 ^ upper) := ⟨pow_ne_zero _ (by decide)⟩
  have hRcard : Nat.card (powMonoidHom 8 : R →* R).ker = 64 := by
    rw [Nat.card_congr (powerKernelEquivOfMulEquiv coordinates 8).toEquiv,
      cyclic_pair_power_kernel_card,
      Nat.gcd_eq_right (show 8 ∣ 2 ^ upper from Nat.pow_dvd_pow 2 hupper)]
    norm_num
  have hMcard := power_kernel_card_embedding_le embedding hinjective 8
  rw [hRcard] at hMcard
  rcases commutative_pGroup_rank_two_coordinates Nat.prime_two hpM hrank with
    hcyclic | ⟨c, d, _, hordered, ⟨e⟩⟩
  · let : IsCyclic M := hcyclic
    rw [IsCyclic.card_powMonoidHom_ker] at hMcard
    have hbound := Nat.gcd_le_right (Nat.card M) (by decide : 0 < 8)
    omega
  · refine ⟨c, d, hordered, ?_, ⟨e⟩⟩
    let : NeZero (2 ^ c) := ⟨pow_ne_zero _ (by decide)⟩
    let : NeZero (2 ^ d) := ⟨pow_ne_zero _ (by decide)⟩
    by_contra hsmall
    have hd : d ≤ 2 := by omega
    rw [Nat.card_congr (powerKernelEquivOfMulEquiv e 8).toEquiv,
      cyclic_pair_power_kernel_card] at hMcard
    have hc := Nat.gcd_le_right (2 ^ c) (by decide : 0 < 8)
    have hdp := Nat.pow_le_pow_right (by decide : 0 < 2) hd
    have hds := Nat.gcd_le_left 8 (by positivity : 0 < 2 ^ d)
    norm_num at hc hdp hds
    nlinarith

@[expose] noncomputable def cyclicFourAddCoordinates {A : Type*} [CommGroup A] (n : ℕ)
    (coordinates : A ≃* Multiplicative (ZMod (2 ^ (n + 4))) × Multiplicative (ZMod 4)) :
    Additive A ≃+ CyclicFourSpace n :=
  (rankTwoAddCoordinates (lower := 2) coordinates).trans
    (AddEquiv.prodCongr
      (ZMod.ringEquivCongr (show 2 ^ (n + 4) = 2 ^ (n + 2) * 4 by
        rw [show n + 4 = (n + 2) + 2 by omega, pow_add]; rfl)).toAddEquiv
      (AddEquiv.refl _))

theorem cyclicFourDelta_occurrence {S : Type*} [Group S]
    (A : Subgroup S) [A.Normal] (hcommutative : IsMulCommutative A) (n : ℕ)
    (coordinates : A ≃* Multiplicative (ZMod (2 ^ (n + 4))) × Multiplicative (ZMod 4)) :
    let _ : CommGroup A := { (inferInstance : Group A) with mul_comm := @mul_comm' _ _ hcommutative }
    cyclicFourDelta n ∈
      ((cyclicFourAutomorphismEquiv hcommutative n (cyclicFourAddCoordinates n coordinates)).toMonoidHom.comp
        (MulAut.conjNormal (H := A))).range →
    ∃ t : S, ∀ a : A, MulAut.conjNormal (H := A) t a = a ^ (1 + 2 ^ (n + 3)) := by
  dsimp only
  let : CommGroup A := { (inferInstance : Group A) with mul_comm := @mul_comm' _ _ hcommutative }
  intro h
  obtain ⟨t, ht⟩ := h
  refine ⟨t, ?_⟩
  intro a
  apply Additive.ofMul.injective
  apply (cyclicFourAddCoordinates n coordinates).injective
  rw [cyclicFourAutomorphismEquiv_apply]
  change (((cyclicFourAutomorphismEquiv hcommutative n (cyclicFourAddCoordinates n coordinates))
    (MulAut.conjNormal (H := A) t)).val) _ = _
  rw [show cyclicFourAutomorphismEquiv hcommutative n (cyclicFourAddCoordinates n coordinates)
    (MulAut.conjNormal (H := A) t) = cyclicFourDelta n from ht, cyclicFourDelta_apply]
  have hmap := map_nsmul (cyclicFourAddCoordinates n coordinates) (1 + 2 ^ (n + 3)) (Additive.ofMul a)
  change _ = (cyclicFourAddCoordinates n coordinates) ((1 + 2 ^ (n + 3)) • Additive.ofMul a)
  rw [hmap]
  apply Prod.ext
  · change (1 + ((2 ^ (n + 3) : ℕ) : ZMod (2 ^ (n + 2) * 4))) *
      ((cyclicFourAddCoordinates n coordinates) (Additive.ofMul a)).1 =
        (1 + 2 ^ (n + 3)) • ((cyclicFourAddCoordinates n coordinates) (Additive.ofMul a)).1
    rw [nsmul_eq_mul, Nat.cast_add, Nat.cast_one]
  · change _ = (1 + 2 ^ (n + 3)) • ((cyclicFourAddCoordinates n coordinates) (Additive.ofMul a)).2
    rw [add_nsmul, one_nsmul]
    have hzero : (2 ^ (n + 3) : ℕ) •
        ((cyclicFourAddCoordinates n coordinates) (Additive.ofMul a)).2 = 0 := by
      rw [nsmul_eq_mul]
      have hcast : ((2 ^ (n + 3) : ℕ) : ZMod 4) = 0 :=
        (ZMod.natCast_eq_zero_iff _ _).mpr (Nat.pow_dvd_pow 2 (by omega : 2 ≤ n + 3))
      rw [hcast, zero_mul]
    rw [hzero, add_zero]

theorem rank_two_cyclic_times_four_large_four_generators {S : Type*} [Group S] [Finite S]
    (hpgroup : IsPGroup 2 S) (A : Subgroup S) [A.Normal]
    (hcommutative : IsMulCommutative A)
    (hselfCentralizing : Subgroup.centralizer (A : Set S) = A)
    (hnoEight : ∀ E : Subgroup S, E.Normal → CFSG.Open.IsElemAbelian 2 E → Nat.card E ≠ 8)
    (n : ℕ) (coordinates : A ≃* Multiplicative (ZMod (2 ^ (n + 4))) × Multiplicative (ZMod 4))
    (U : Subgroup S) : ∃ X : Finset U, Subgroup.closure (X : Set U) = ⊤ ∧ X.card ≤ 4 := by
  classical
  let : CommGroup A := { (inferInstance : Group A) with mul_comm := @mul_comm' _ _ hcommutative }
  let e := cyclicFourAddCoordinates n coordinates
  by_cases hdelta : cyclicFourDelta n ∈
      ((cyclicFourAutomorphismEquiv hcommutative n e).toMonoidHom.comp (MulAut.conjNormal (H := A))).range
  · obtain ⟨R, hRnormal, hRcommutative, ⟨r⟩⟩ := rank_two_cyclic_times_four_normal_replacement
      hpgroup A hcommutative hselfCentralizing hnoEight n coordinates
      (cyclicFourDelta_occurrence A hcommutative n coordinates hdelta)
    obtain ⟨M, hRM, hmaximal⟩ := Finite.exists_le_maximal
      (p := fun M : Subgroup S => M.Normal ∧ IsMulCommutative M) ⟨hRnormal, hRcommutative⟩
    let : M.Normal := hmaximal.1.1
    have hMcommutative := hmaximal.1.2
    let : CommGroup M := { (inferInstance : Group M) with mul_comm := @mul_comm' _ _ hMcommutative }
    let : CommGroup R := { (inferInstance : Group R) with mul_comm := @mul_comm' _ _ hRcommutative }
    have hMcentral := maximal_abelian_normal_selfCentralizing Nat.prime_two hpgroup M
      hMcommutative (fun L hnormal hcomm hle => hmaximal.2 ⟨hnormal, hcomm⟩ hle)
    obtain ⟨X, hX, hcard⟩ := no_normal_eight_abelian_normal_two_generators hpgroup hnoEight M hMcommutative
    have hMrank := (pGeneratorRank_le_generators Nat.prime_two (hpgroup.to_subgroup M) X hX).trans hcard
    obtain ⟨c, d, hordered, hlarge, ⟨m⟩⟩ := rank_two_abelian_overgroup_large_coordinates
      (hpgroup.to_subgroup M) hMrank (Subgroup.inclusion hRM) (Subgroup.inclusion_injective hRM)
      (n + 3) (by omega) r
    exact rank_two_large_exponent_four_generators hpgroup M hMcommutative hMcentral hnoEight c d hordered hlarge m U
  · exact rank_two_cyclic_times_four_scalar_free_four_generators hpgroup A hcommutative
      hselfCentralizing hnoEight n e hdelta U

theorem rank_two_cyclic_times_four_large_ambient_four_generators {S : Type*} [Group S] [Finite S]
    (hpgroup : IsPGroup 2 S) (A : Subgroup S) [A.Normal]
    (hcommutative : IsMulCommutative A)
    (hselfCentralizing : Subgroup.centralizer (A : Set S) = A)
    (hnoEight : ∀ E : Subgroup S, E.Normal → CFSG.Open.IsElemAbelian 2 E → Nat.card E ≠ 8)
    (n : ℕ) (coordinates : A ≃* Multiplicative (ZMod (2 ^ (n + 4))) × Multiplicative (ZMod 4))
    (U : Subgroup S) : ∃ X : Finset S, X.card ≤ 4 ∧ Subgroup.closure (X : Set S) = U := by
  classical
  obtain ⟨X, hX, hcard⟩ := rank_two_cyclic_times_four_large_four_generators hpgroup A hcommutative
    hselfCentralizing hnoEight n coordinates U
  refine ⟨X.image U.subtype, Finset.card_image_le.trans hcard, ?_⟩
  rw [Finset.coe_image, ← MonoidHom.map_closure, hX, Subgroup.map_top]
  exact U.range_subtype

end CFSG.LargeEvenClassification.Helpers
