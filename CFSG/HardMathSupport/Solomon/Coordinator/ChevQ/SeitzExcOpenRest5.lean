module

public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.SeitzExcOpenRest5Frame
public import CFSG.LieType.SeitzGeneration.ExcHigh.E8FiveSplit
public import CFSG.HardMathSupport.Curtis.UnitaryLevi.ExcF4W

public noncomputable section

namespace CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.SeitzExcOpenRest5

open CFSG.Open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.SeitzGeneration
  CFSG.LieType.SeitzGeneration.ExcHigh CFSG.LieType.SeitzGeneration.ExcHighThree TauCeti
  CFSG.RankThree.PartOne.KE CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.SeitzExcOpenRest4
open CFSG.RankThree.E6 (charVal)

set_option linter.unusedSectionVars false

namespace Aux

theorem geomSum_mod_three {q : ℕ} (hq : q % 3 = 1) (n s : ℕ) :
    CFSG.Timmesfeld.ExceptionalOrders.geomSum n s q % 3 = n % 3 := by
  unfold CFSG.Timmesfeld.ExceptionalOrders.geomSum
  have h : ∀ i ∈ Finset.range n, q ^ (s * i) % 3 = 1 := fun i _ => by
    rw [Nat.pow_mod, hq, one_pow]
    norm_num
  rw [Finset.sum_nat_mod, Finset.sum_congr rfl h, Finset.sum_const, Finset.card_range,
    smul_eq_mul, mul_one]

theorem not_three_dvd_index_E7 {q : ℕ} (hq : q % 3 = 1) :
    ¬ 3 ∣ CFSG.Timmesfeld.ExceptionalOrders.geomSum 2 5 q *
      CFSG.Timmesfeld.ExceptionalOrders.geomSum 2 9 q *
        CFSG.Timmesfeld.ExceptionalOrders.geomSum 14 1 q := by
  intro h
  have h1 := geomSum_mod_three hq 2 5
  have h2 := geomSum_mod_three hq 2 9
  have h3 := geomSum_mod_three hq 14 1
  rw [Nat.dvd_iff_mod_eq_zero, Nat.mul_mod, Nat.mul_mod
    (CFSG.Timmesfeld.ExceptionalOrders.geomSum 2 5 q), h1, h2, h3] at h
  norm_num at h

end Aux

section E7One

theorem normalizesRGroup_E7_of_mod_three {K : Type} [Field K] [Finite K]
    (hK : Nat.card K % 3 = 1) {E₀ : Subgroup (adjointGroup .E7 K)} (hE₀ : IsPGroup 3 E₀) :
    NormalizesRGroup (ringChar K) E₀ := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI : Fintype (WeylGroup .E7) := Fintype.ofFinite _
  have hr : ∃ n, Nat.card K = ringChar K ^ n := by
    haveI : Fintype K := Fintype.ofFinite K
    obtain ⟨n, -, hn⟩ := FiniteField.card K (ringChar K)
    exact ⟨n, by rw [Nat.card_eq_fintype_card, hn]⟩
  have hidx : ¬ 3 ∣ (parabolicSubgroup .E7 K
      (CFSG.Timmesfeld.ExceptionalOrders.maskSet .E7 63)).relIndex (adjointGroup .E7 K) := by
    rw [relIndex_parabolicSubgroup_E7]
    exact Aux.not_three_dvd_index_E7 hK
  have hEp : IsPGroup 3 (E₀.map (MulAut.conj : adjointGroup .E7 K →* MulAut (adjointGroup .E7 K))) :=
    hE₀.map _
  have hin : E₀.map (MulAut.conj : adjointGroup .E7 K →* MulAut (adjointGroup .E7 K)) ≤
      (MulAut.conj : adjointGroup .E7 K →* MulAut (adjointGroup .E7 K)).range :=
    Subgroup.map_le_range _ _
  obtain ⟨R, hR0, hRr, hR⟩ := exists_normalized_of_not_dvd_relIndex (MulEquiv.refl _) hr
    maskSet_E7_ne_univ hidx hEp hin
  exact ⟨R, hR0, hRr, fun x hx => hR (MulAut.conj x) ⟨x, hx, rfl⟩⟩

theorem threeToralCubeRest_E7_one (K : Type) [Field K] [Finite K] (hK : Nat.card K % 3 = 1)
    (E₀ : Subgroup (adjointGroup .E7 K)) (hc : Nat.card E₀ = 3 ^ 3)
    (hN : ¬ NormalizesRGroup (ringChar K) E₀) : False :=
  hN (normalizesRGroup_E7_of_mod_three hK (IsPGroup.of_card hc))

end E7One

section Split

theorem normalizesRGroup_of_native' {τ : Tag} {K : Type} [Field K]
    {E₀ : Subgroup (adjointGroup τ K)} (h : NormalizesRNative τ K E₀) :
    NormalizesRGroup (ringChar K) E₀ := by
  obtain ⟨R, hR1, hRp, hRn⟩ := h
  exact ⟨R, hR1, hRp, fun x hx => (map_conj_eq_iff_mem_normalizer R x).2 (hRn hx)⟩

theorem f4_normalizesRNative_of_split_datum {K : Type} [Field K] [Finite K]
    {E₀ : Subgroup (adjointGroup Tag.F4 K)} (D : LangPlaneData Tag.F4 K E₀)
    (hw : D.w = 1) : NormalizesRNative Tag.F4 K E₀ := by
  obtain ⟨w, Fr, hFr, g0, hg0C, hg0, c, hc⟩ := D
  subst hw
  rw [CFSG.LieType.Chevalley.canonicalRep_one, mul_one] at hg0
  rw [CFSG.LieType.Chevalley.canonicalRep_one] at hc
  have hbij : Function.Bijective Fr := by
    refine ⟨Fr.injective, fun c => ?_⟩
    obtain ⟨z, hz⟩ := IsAlgClosed.exists_pow_nat_eq c (Nat.card_pos (α := K))
    exact ⟨z, by rw [hFr z, hz]⟩
  obtain ⟨γ, hγ, hγg⟩ := Subgroup.mem_map.1
    (CFSG.RankThree.Chevalley.mem_map_adjointGroup_of_frobenius_fixed (τ := Tag.F4) (Or.inr rfl)
      Fr hFr hbij hg0C hg0)
  obtain ⟨g', hg'⟩ : ∃ g' : adjointGroup Tag.F4 K, (g' : ModGL Tag.F4 K) = γ := ⟨⟨γ, hγ⟩, rfl⟩
  have hg'B : baseChangeGL (algebraMap K (AlgebraicClosure K)) (g' : ModGL Tag.F4 K) = g0 := by
    rw [hg']
    exact hγg
  obtain ⟨α, hα⟩ : ∃ α : Fin Tag.F4.rank → ℤ, IsRoot Tag.F4 α :=
    ⟨_, IsRoot.basis ⟨0, by decide⟩⟩
  obtain ⟨k, hk⟩ : ∃ k : adjointGroup Tag.F4 K, k = g'⁻¹ * c := ⟨_, rfl⟩
  have hrat : ∀ x ∈ E₀, ∃ b : Fin Tag.F4.rank → Kˣ,
      ((k * x * k⁻¹ : adjointGroup Tag.F4 K) : ModGL Tag.F4 K) = rootDiagUnit Tag.F4 b := by
    intro x hx
    obtain ⟨t, ht, htb⟩ := Subgroup.mem_map.1 (hc x hx)
    have htb' : g0 * t * g0⁻¹ = baseChangeGL (algebraMap K (AlgebraicClosure K))
          ((c * x * c⁻¹ : adjointGroup Tag.F4 K) : ModGL Tag.F4 K) :=
      htb
    have e : ((k * x * k⁻¹ : adjointGroup Tag.F4 K) : ModGL Tag.F4 K) =
        (g' : ModGL Tag.F4 K)⁻¹ * ((c * x * c⁻¹ : adjointGroup Tag.F4 K) : ModGL Tag.F4 K) *
          (g' : ModGL Tag.F4 K) := by
      rw [hk]
      simp only [mul_inv_rev, inv_inv, Subgroup.coe_mul, Subgroup.coe_inv]
      group
    have hyb : baseChangeGL (algebraMap K (AlgebraicClosure K))
        ((k * x * k⁻¹ : adjointGroup Tag.F4 K) : ModGL Tag.F4 K) = t := by
      rw [e, map_mul, map_mul, map_inv, hg'B, ← htb']
      group
    have ht' := mem_twistedTorusOf.1 ht
    have hT : baseChangeGL (algebraMap K (AlgebraicClosure K))
        ((k * x * k⁻¹ : adjointGroup Tag.F4 K) : ModGL Tag.F4 K) ∈
          torusGroup Tag.F4 (AlgebraicClosure K) := by
      rw [hyb]
      exact ht'.1
    have hF : Units.map (entrywiseHom Fr)
        (baseChangeGL (algebraMap K (AlgebraicClosure K))
          ((k * x * k⁻¹ : adjointGroup Tag.F4 K) : ModGL Tag.F4 K)) =
        baseChangeGL (algebraMap K (AlgebraicClosure K))
          ((k * x * k⁻¹ : adjointGroup Tag.F4 K) : ModGL Tag.F4 K) := by
      rw [hyb]
      simpa using ht'.2
    exact e8Split_rational_of_torus Tag.F4 Fr hFr hT hF
  refine e8Split_normalizesRIn_of_conj (ringChar K) E₀
    ((rootSubgroup Tag.F4 K α).subgroupOf (adjointGroup Tag.F4 K)) k ?_ ?_ ?_
  · refine ⟨⟨pinnedX Tag.F4 K α 1, pinnedX_mem_adjointGroup α 1⟩, ?_, ?_⟩
    · rw [Subgroup.mem_subgroupOf]
      exact mem_rootSubgroup.2 ⟨1, rfl⟩
    · intro h
      have h1 : pinnedX Tag.F4 K α (1 : K) ≠ 1 := by
        intro h1
        have h0 : pinnedX Tag.F4 K α (1 : K) = pinnedX Tag.F4 K α 0 := by
          rw [h1, pinnedX_zero]
        exact one_ne_zero (pinnedX_injective Tag.F4 K α h0)
      exact h1 (congrArg Subtype.val h)
  · intro u hu
    rw [Subgroup.mem_subgroupOf] at hu
    apply Subtype.ext
    rw [Subgroup.coe_pow, Subgroup.coe_one]
    exact e8Split_pow_ringChar Tag.F4 α hu
  · intro x hx m
    obtain ⟨b, hb⟩ := hrat x hx
    exact e8Split_mem_U_iff_conj Tag.F4 hα hb m

end Split

section F4Weyl

open CFSG.HardMathSupport.Curtis.UnitaryLevi

namespace Aux

theorem charVal_single' {τ : Tag} {R : Type*} [CommRing R] (z : Fin τ.rank → R) (k : Fin τ.rank) :
    charVal z (Pi.single k 1 : Fin τ.rank → ℤ) = z k := by
  unfold charVal
  rw [Finset.sum_eq_single k (fun i _ hi => by simp [Pi.single_apply, hi])
    (fun h => absurd (Finset.mem_univ k) h)]
  simp

theorem mem_dualWeylStabilizer_iff_single {τ : Tag} {R : Type*} [CommRing R]
    {z : Fin τ.rank → R} {w : WeylGroup τ} :
    w ∈ dualWeylStabilizer z ↔ ∀ k, charVal z (w • (Pi.single k 1 : Fin τ.rank → ℤ)) = z k := by
  constructor
  · intro h k
    rw [h, charVal_single']
  · intro h x
    rw [charVal_smul_eq_sum]
    simp only [h]
    rfl

theorem pow_mod_three_of_cube {G : Type*} [Monoid G] {g : G} (h : g ^ 3 = 1) (n : ℕ) :
    g ^ n = g ^ (n % 3) := by
  conv_lhs => rw [← Nat.mod_add_div n 3]
  rw [pow_add, pow_mul, h, one_pow, mul_one]

theorem exists_pow_eq_of_pow_three {L : Type} [Field L] {ζ : Lˣ} (hζ : orderOf ζ = 3) {b : Lˣ}
    (hb : b ^ 3 = 1) : ∃ n : ℕ, b = ζ ^ n := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hprim : IsPrimitiveRoot ((ζ : Lˣ) : L) 3 :=
    IsPrimitiveRoot.coe_units_iff.2 (IsPrimitiveRoot.iff_orderOf.2 hζ)
  have hi : ((b : Lˣ) : L) ^ 3 = 1 := by
    rw [← Units.val_pow_eq_pow_val, hb, Units.val_one]
  obtain ⟨n, -, hn⟩ := hprim.eq_pow_of_pow_eq_one hi
  exact ⟨n, Units.ext (by rw [Units.val_pow_eq_pow_val]; exact hn.symm)⟩

theorem card_fix_wordW_le (l : List (Fin Tag.F4.rank))
    (h : (Finset.univ.filter (fun z : Fin Tag.F4.rank → ZMod 3 =>
      ∀ k : Fin Tag.F4.rank, charVal z (((l.map (Smat Tag.F4)).prod).mulVec (Pi.single k 1)) =
        z k)).card ≤ 9) :
    Nat.card {z : Fin Tag.F4.rank → ZMod 3 // wordW Tag.F4 l ∈ dualWeylStabilizer z} ≤ 9 := by
  classical
  have e : {z : Fin Tag.F4.rank → ZMod 3 // wordW Tag.F4 l ∈ dualWeylStabilizer z} ≃
      {z : Fin Tag.F4.rank → ZMod 3 // ∀ k : Fin Tag.F4.rank,
        charVal z (((l.map (Smat Tag.F4)).prod).mulVec (Pi.single k 1)) = z k} :=
    Equiv.subtypeEquivRight fun z => by
      rw [mem_dualWeylStabilizer_iff_single]
      simp only [wordW_smul]
  rw [Nat.card_congr e, Nat.card_eq_fintype_card, Fintype.card_subtype]
  convert h

theorem card_fix_QF4_le {s : WeylGroup Tag.F4} (hs : s ∈ QF4) (hs1 : s ≠ 1) :
    Nat.card {z : Fin Tag.F4.rank → ZMod 3 // s ∈ dualWeylStabilizer z} ≤ 9 := by
  obtain ⟨i, j, rfl⟩ := mem_QF4 hs
  rw [pow_mod_three_of_cube wa_cube i, pow_mod_three_of_cube wb_cube j] at hs1 ⊢
  have hi : i % 3 < 3 := Nat.mod_lt _ (by norm_num)
  have hj : j % 3 < 3 := Nat.mod_lt _ (by norm_num)
  generalize i % 3 = i' at hi hs1 ⊢
  generalize j % 3 = j' at hj hs1 ⊢
  have key : wa ^ i' * wb ^ j' =
      wordW Tag.F4 ((List.replicate i' laF).flatten ++ (List.replicate j' lbF).flatten) := by
    rw [wordW_append, wordW_replicate, wordW_replicate]
    rfl
  rw [key]
  interval_cases i' <;> interval_cases j'
  · exact absurd (by simp) hs1
  all_goals exact card_fix_wordW_le _ (by decide +kernel)

end Aux

theorem f4_cube_stab_eq_one {L : Type} [Field L] (A : Subgroup (Fin Tag.F4.rank → Lˣ))
    (hA : Nat.card A = 3 ^ 3) (hA3 : ∀ a ∈ A, a ^ 3 = 1)
    (hreg : ∀ α, IsRoot Tag.F4 α → ∃ a ∈ A, rootChar a α ≠ 1)
    {y : WeylGroup Tag.F4} (hy : ∀ a ∈ A, ∀ v, rootChar a (y • v) = rootChar a v) : y = 1 := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI : Finite A := Nat.finite_of_card_ne_zero (by rw [hA]; norm_num)
  obtain ⟨a₀, ha₀A, ha₀1⟩ : ∃ a ∈ A, a ≠ 1 := by
    by_contra h
    push Not at h
    have hbot : A = ⊥ := (Subgroup.eq_bot_iff_forall A).2 h
    rw [hbot, Subgroup.card_bot] at hA
    norm_num at hA
  obtain ⟨i₀, hi₀⟩ : ∃ i, a₀ i ≠ 1 := by
    by_contra h
    push Not at h
    exact ha₀1 (funext h)
  have hζ : orderOf (a₀ i₀) = 3 :=
    orderOf_eq_prime (by simpa using congrFun (hA3 a₀ ha₀A) i₀) hi₀
  have hexp : ∀ a : Fin Tag.F4.rank → Lˣ, ∃ e : Fin Tag.F4.rank → ℕ,
      a ∈ A → ∀ i, a i = a₀ i₀ ^ e i := by
    intro a
    by_cases ha : a ∈ A
    · have : ∀ i, ∃ n : ℕ, a i = a₀ i₀ ^ n := fun i =>
        Aux.exists_pow_eq_of_pow_three hζ (by simpa using congrFun (hA3 a ha) i)
      choose e he using this
      exact ⟨e, fun _ => he⟩
    · exact ⟨0, fun h => absurd h ha⟩
  choose e he using hexp
  set col : (Fin Tag.F4.rank → Lˣ) → Fin Tag.F4.rank → ZMod 3 := fun a i => (e a i : ZMod 3)
    with hcol
  have hchar : ∀ a ∈ A, ∀ l l' : Fin Tag.F4.rank → ℤ,
      rootChar a l = rootChar a l' ↔ charVal (col a) l = charVal (col a) l' :=
    fun a ha l l' => rootChar_eq_rootChar_iff hζ (e a) a (he a ha) l l'
  obtain ⟨a1, ha1, a2, ha2, a3, ha3, hgen⟩ :=
    SeitzExcOpenRest3.exists_three_gen_of_card_cube Nat.prime_three A hA hA3
  have hcl : ∀ H : Subgroup (Fin Tag.F4.rank → Lˣ), a1 ∈ H → a2 ∈ H → a3 ∈ H → A ≤ H := by
    intro H h1 h2 h3
    rw [hgen]
    exact (Subgroup.closure_le H).2 (by rintro _ (rfl | rfl | rfl) <;> assumption)
  set U := dualWeylStabilizer (col a1) ⊓ dualWeylStabilizer (col a2) ⊓
    dualWeylStabilizer (col a3) with hUdef
  have hfix : ∀ u ∈ U, ∀ a ∈ A, ∀ v, rootChar a (u • v) = rootChar a v := by
    intro u hu
    let H : Subgroup (Fin Tag.F4.rank → Lˣ) :=
      ⨅ v : Fin Tag.F4.rank → ℤ, (rootCharHom (L := L) (u • v)).eqLocus (rootCharHom v)
    have hmemH : ∀ a, a ∈ H ↔ ∀ v, rootChar a (u • v) = rootChar a v := by
      intro a
      simp only [H, Subgroup.mem_iInf]
      rfl
    have h1 : a1 ∈ H := (hmemH a1).2 fun v => (hchar a1 ha1 _ _).2 (hu.1.1 v)
    have h2 : a2 ∈ H := (hmemH a2).2 fun v => (hchar a2 ha2 _ _).2 (hu.1.2 v)
    have h3 : a3 ∈ H := (hmemH a3).2 fun v => (hchar a3 ha3 _ _).2 (hu.2 v)
    intro a ha
    exact (hmemH a).1 (hcl H h1 h2 h3 ha)
  have hU : U = ⊥ := by
    by_cases h3 : 3 ∣ Nat.card U
    · exfalso
      obtain ⟨u, hu⟩ := exists_prime_orderOf_dvd_card' (G := U) 3 h3
      have hu'3 : (u : WeylGroup Tag.F4) ^ 3 = 1 := by
        have : u ^ 3 = 1 := by rw [← hu]; exact pow_orderOf_eq_one u
        exact congrArg Subtype.val this
      have hu'1 : (u : WeylGroup Tag.F4) ≠ 1 := fun h => by
        have : u = 1 := Subtype.ext h
        rw [this, orderOf_one] at hu
        norm_num at hu
      obtain ⟨g, hg⟩ := exists_conj_mem_QF4 (u : WeylGroup Tag.F4) hu'3
      have hs1 : g * (u : WeylGroup Tag.F4) * g⁻¹ ≠ 1 := fun h => hu'1 (by
        have e : (u : WeylGroup Tag.F4) = g⁻¹ * (g * (u : WeylGroup Tag.F4) * g⁻¹) * g := by group
        rw [e, h]
        group)
      have hcard := Aux.card_fix_QF4_le hg hs1
      let T : (Fin Tag.F4.rank → ZMod 3) → Fin Tag.F4.rank → ZMod 3 :=
        fun z k => charVal z (g⁻¹ • (Pi.single k 1 : Fin Tag.F4.rank → ℤ))
      have hT : ∀ z (x : Fin Tag.F4.rank → ℤ), charVal (T z) x = charVal z (g⁻¹ • x) := by
        intro z x
        rw [charVal_smul_eq_sum z g⁻¹ x]
        rfl
      have hTfix : ∀ a ∈ A, g * (u : WeylGroup Tag.F4) * g⁻¹ ∈ dualWeylStabilizer (T (col a)) := by
        intro a ha x
        rw [hT, hT]
        have e1 : g⁻¹ • ((g * (u : WeylGroup Tag.F4) * g⁻¹) • x) =
            (u : WeylGroup Tag.F4) • (g⁻¹ • x) := by
          rw [mul_smul, mul_smul, inv_smul_smul]
        rw [e1]
        exact (hchar a ha _ _).1 (hfix u u.2 a ha (g⁻¹ • x))
      have hinj : Function.Injective (fun a : A =>
          (⟨T (col a), hTfix a a.2⟩ :
            {z : Fin Tag.F4.rank → ZMod 3 // g * (u : WeylGroup Tag.F4) * g⁻¹ ∈
              dualWeylStabilizer z})) := by
        intro a b hab
        have h1 : T (col a) = T (col b) := congrArg Subtype.val hab
        have h2 : col a = col b := by
          funext i
          have := congrArg (fun z => charVal z (g • (Pi.single i 1 : Fin Tag.F4.rank → ℤ))) h1
          simp only [hT, inv_smul_smul, Aux.charVal_single'] at this
          exact this
        apply Subtype.ext
        funext i
        rw [he a a.2 i, he b b.2 i]
        have h3 : e a i % 3 = e b i % 3 :=
          (ZMod.natCast_eq_natCast_iff' _ _ _).1 (congrFun h2 i)
        calc a₀ i₀ ^ e a i = a₀ i₀ ^ (e a i % orderOf (a₀ i₀)) := (pow_mod_orderOf _ _).symm
          _ = a₀ i₀ ^ (e b i % orderOf (a₀ i₀)) := by rw [hζ, h3]
          _ = a₀ i₀ ^ e b i := pow_mod_orderOf _ _
      have := Nat.card_le_card_of_injective _ hinj
      rw [hA] at this
      omega
    · have hle := SeitzExcOpenRest3.inf3_dualWeylStabilizer_le_closure_of_card
        (col a1) (col a2) (col a3) h3
      have hempty : {s | ∃ α ∈ rootKernel (col a1) ∩ rootKernel (col a2) ∩ rootKernel (col a3),
          s = rootReflection α} = (∅ : Set (WeylGroup Tag.F4)) := by
        ext s
        simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
        rintro ⟨α, ⟨⟨⟨hα, h1⟩, ⟨-, h2⟩⟩, ⟨-, h3'⟩⟩, -⟩
        obtain ⟨a, haA, hane⟩ := hreg α hα
        apply hane
        have hk : ∀ b ∈ A, charVal (col b) α = 0 → b ∈ (rootCharHom (L := L) α).ker := by
          intro b hb hz
          show rootChar b α = 1
          have := (hchar b hb α 0).2 (by rw [hz]; simp [charVal])
          rwa [rootChar_zero] at this
        exact hcl _ (hk a1 ha1 h1) (hk a2 ha2 h2) (hk a3 ha3 h3') haA
      rw [hempty, Subgroup.closure_empty] at hle
      exact le_bot_iff.1 hle
  have hyU : y ∈ U := ⟨⟨fun v => (hchar a1 ha1 _ _).1 (hy a1 ha1 v),
    fun v => (hchar a2 ha2 _ _).1 (hy a2 ha2 v)⟩, fun v => (hchar a3 ha3 _ _).1 (hy a3 ha3 v)⟩
  rw [hU] at hyU
  exact Subgroup.mem_bot.1 hyU

end F4Weyl

section F4Datum

namespace Aux

theorem rootChar_inv' {τ : Tag} {L : Type} [Field L] (a : Fin τ.rank → Lˣ) (v : Fin τ.rank → ℤ) :
    rootChar a⁻¹ v = (rootChar a v)⁻¹ := by
  simp only [rootChar, Pi.inv_apply, inv_zpow, Finset.prod_inv_distrib]

theorem rootChar_neg' {τ : Tag} {L : Type} [Field L] (a : Fin τ.rank → Lˣ) (v : Fin τ.rank → ℤ) :
    rootChar a (-v) = (rootChar a v)⁻¹ := by
  refine eq_inv_of_mul_eq_one_left ?_
  rw [← rootChar_add, neg_add_cancel, rootChar_zero]

end Aux

theorem diagMap_mem_twistedTorus {τ : Tag} {K : Type} [Field K] [Finite K]
    {A : Subgroup (adjointGroup τ K)} (D : LangPlaneData τ K A) {x : adjointGroup τ K}
    (hx : x ∈ A) :
    diagMap D x ∈ twistedTorusOf (canonicalRep (coxeterSystem τ) (AlgebraicClosure K) D.w)
      (Units.map (entrywiseHom D.Fr)) := by
  obtain ⟨t, ht, hte⟩ := D.hc x hx
  have : diagMap D x = t := by
    rw [diagMap_apply, ← hte]
    simp [MulAut.conj_apply, mul_assoc]
  rw [this]
  exact ht

theorem eq_bot_of_neg_datum_of_mod_three_eq_one {τ : Tag} {K : Type} [Field K] [Finite K]
    (hK : Nat.card K % 3 = 1) {E₀ : Subgroup (adjointGroup τ K)} (hE₀p : ∀ x ∈ E₀, x ^ 3 = 1)
    (D : LangPlaneData τ K E₀) (hw : ∀ u : Fin τ.rank → ℤ, D.w • u = -u) : E₀ = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  rw [Subgroup.mem_bot]
  obtain ⟨a, ha⟩ := exists_rootDiagUnit_of_mem_torusGroup (diagMap_mem_torusGroup D hx)
  have hT := (mem_twistedTorusOf.1 (diagMap_mem_twistedTorus D hx)).2
  rw [← ha, CFSG.HardMathSupport.Timmesfeld.CrossChar.units_map_entrywiseHom_rootDiagUnit] at hT
  have htw := (rootDiagUnit_eq_conj_canonicalRep_iff a _ D.w).1 hT.symm
  have ha3 : a ^ 3 = 1 := by
    apply CFSG.LieType.Chevalley.rootDiagUnit_injective (τ := τ)
    change rootDiagUnitHom τ (AlgebraicClosure K) (a ^ 3) = rootDiagUnitHom τ _ 1
    rw [map_pow, map_one]
    show rootDiagUnit τ a ^ 3 = 1
    rw [ha, ← map_pow, hE₀p x hx, map_one]
  have hai3 : ∀ i, a i ^ 3 = 1 := fun i => by simpa using congrFun ha3 i
  have hFa : (fun i => Units.map D.Fr.toMonoidHom (a i)) = a := by
    funext i
    have e : Units.map D.Fr.toMonoidHom (a i) = a i ^ Nat.card K := Units.ext (by simp [D.hFr])
    rw [e, Aux.pow_mod_three_of_cube (hai3 i), hK, pow_one]
  have hsingle : ∀ i, rootChar a (Pi.single i 1 : Fin τ.rank → ℤ) = a i := fun i => by
    simpa using rootChar_nsmul_single a i 1
  have hai : ∀ i, a i = 1 := by
    intro i
    have h1 := htw (Pi.single i 1)
    rw [hw, Aux.rootChar_neg', hFa, hsingle] at h1
    have h2 : a i * a i = 1 := by
      calc a i * a i = a i * (a i)⁻¹ := by rw [h1]
        _ = 1 := mul_inv_cancel _
    calc a i = a i * (a i * a i) := by rw [h2, mul_one]
      _ = a i ^ 3 := (pow_three (a i)).symm
      _ = 1 := hai3 i
  apply diagMap_injective D
  rw [map_one, ← ha, show a = 1 from funext hai]
  exact map_one (rootDiagUnitHom τ (AlgebraicClosure K))

theorem f4_regular_datum_w {K : Type} [Field K] [Finite K]
    {E₀ : Subgroup (adjointGroup Tag.F4 K)} (hE₀ : IsElemAbelian 3 E₀) (hc : Nat.card E₀ = 3 ^ 3)
    (D : LangPlaneData Tag.F4 K E₀) (hreg : ∀ α, IsRoot Tag.F4 α → ¬ D.Kills α) :
    (Nat.card K % 3 = 1 → D.w = 1) ∧
      (Nat.card K % 3 = 2 → D.w = CFSG.HardMathSupport.Timmesfeld.CrossChar.f4Neg) := by
  classical
  set A : Subgroup (Fin Tag.F4.rank → (AlgebraicClosure K)ˣ) :=
    (E₀.map (diagMap D)).comap (rootDiagUnitHom Tag.F4 (AlgebraicClosure K)) with hAdef
  have hinj : Function.Injective (rootDiagUnitHom Tag.F4 (AlgebraicClosure K)) :=
    CFSG.LieType.Chevalley.rootDiagUnit_injective
  have hrange : E₀.map (diagMap D) ≤ (rootDiagUnitHom Tag.F4 (AlgebraicClosure K)).range := by
    rintro _ ⟨x, hx, rfl⟩
    obtain ⟨a, ha⟩ := exists_rootDiagUnit_of_mem_torusGroup (diagMap_mem_torusGroup D hx)
    exact ⟨a, ha⟩
  have hAmap : A.map (rootDiagUnitHom Tag.F4 (AlgebraicClosure K)) = E₀.map (diagMap D) :=
    Subgroup.map_comap_eq_self hrange
  have hA : Nat.card A = 3 ^ 3 := by
    rw [← Subgroup.card_map_of_injective hinj, hAmap,
      Subgroup.card_map_of_injective (diagMap_injective D), hc]
  have hmemA : ∀ a, a ∈ A ↔ ∃ x ∈ E₀, diagMap D x = rootDiagUnit Tag.F4 a := fun a =>
    Subgroup.mem_comap.trans Subgroup.mem_map
  have hA3 : ∀ a ∈ A, a ^ 3 = 1 := by
    intro a ha
    obtain ⟨x, hx, hxa⟩ := (hmemA a).1 ha
    apply hinj
    rw [map_pow, map_one]
    show rootDiagUnit Tag.F4 a ^ 3 = 1
    rw [← hxa, ← map_pow, hE₀.2 x hx, map_one]
  have hreg' : ∀ α, IsRoot Tag.F4 α → ∃ a ∈ A, rootChar a α ≠ 1 := by
    intro α hα
    by_contra h
    push Not at h
    apply hreg α hα
    intro x hx
    obtain ⟨a, ha⟩ := exists_rootDiagUnit_of_mem_torusGroup (diagMap_mem_torusGroup D hx)
    exact ⟨a, by rw [ha, diagMap_apply], h a ((hmemA a).2 ⟨x, hx, ha.symm⟩)⟩
  have htw : ∀ a ∈ A, ∀ v, rootChar a (D.w • v) =
      rootChar (fun i => Units.map D.Fr.toMonoidHom (a i)) v := by
    intro a ha v
    obtain ⟨x, hx, hxa⟩ := (hmemA a).1 ha
    have hT := (mem_twistedTorusOf.1 (diagMap_mem_twistedTorus D hx)).2
    rw [hxa, CFSG.HardMathSupport.Timmesfeld.CrossChar.units_map_entrywiseHom_rootDiagUnit] at hT
    exact (rootDiagUnit_eq_conj_canonicalRep_iff a _ D.w).1 hT.symm v
  have hFra : ∀ a ∈ A, ∀ i, Units.map D.Fr.toMonoidHom (a i) = a i ^ Nat.card K := fun a _ i =>
    Units.ext (by simp [D.hFr])
  have hcube : ∀ a ∈ A, ∀ i, a i ^ 3 = 1 := fun a ha i => by
    simpa using congrFun (hA3 a ha) i
  constructor
  · intro hK
    have hFa : ∀ a ∈ A, (fun i => Units.map D.Fr.toMonoidHom (a i)) = a := by
      intro a ha
      funext i
      rw [hFra a ha i, Aux.pow_mod_three_of_cube (hcube a ha i), hK, pow_one]
    exact f4_cube_stab_eq_one A hA hA3 hreg' fun a ha v => by rw [htw a ha v, hFa a ha]
  · intro hK
    have hFa : ∀ a ∈ A, (fun i => Units.map D.Fr.toMonoidHom (a i)) = a⁻¹ := by
      intro a ha
      funext i
      rw [hFra a ha i, Aux.pow_mod_three_of_cube (hcube a ha i), hK, Pi.inv_apply]
      refine eq_inv_of_mul_eq_one_left ?_
      rw [← pow_succ, hcube a ha i]
    have hneg : ∀ u : Fin Tag.F4.rank → ℤ,
        (CFSG.HardMathSupport.Timmesfeld.CrossChar.f4Neg)⁻¹ • u = -u := fun u => by
      rw [inv_smul_eq_iff, CFSG.HardMathSupport.Timmesfeld.CrossChar.f4Neg_smul, neg_neg]
    have hy := f4_cube_stab_eq_one A hA hA3 hreg'
      (y := (CFSG.HardMathSupport.Timmesfeld.CrossChar.f4Neg)⁻¹ * D.w) fun a ha v => by
        rw [mul_smul, hneg, Aux.rootChar_neg', htw a ha v, hFa a ha, Aux.rootChar_inv', inv_inv]
    exact (inv_mul_eq_one.1 hy).symm

theorem threeToralCubeRest_F4_one (K : Type) [Field K] [Finite K] (hK : Nat.card K % 3 = 1)
    (E₀ : Subgroup (adjointGroup .F4 K)) (hE₀ : IsElemAbelian 3 E₀) (hc : Nat.card E₀ = 3 ^ 3)
    (hN : ¬ NormalizesRGroup (ringChar K) E₀) (D : LangPlaneData .F4 K E₀)
    (hreg : ∀ α : Fin Tag.F4.rank → ℤ, IsRoot .F4 α → ¬ D.Kills α) : False :=
  hN (normalizesRGroup_of_native'
    (f4_normalizesRNative_of_split_datum D ((f4_regular_datum_w hE₀ hc D hreg).1 hK)))

end F4Datum

section Residual

@[expose] def E7NonToralTwoRest : Prop :=
  ∀ (K : Type) [Field K] [Finite K], Nat.card K % 3 = 2 → ThreeScope LieTypeIndex.E7 K →
    ∀ E₀ : Subgroup (adjointGroup .E7 K), IsElemAbelian 3 E₀ → Nat.card E₀ = 3 ^ 3 →
      ¬ NormalizesRGroup (ringChar K) E₀ → IsEmpty (LangPlaneData .E7 K E₀) → HyperGen 3 ⊤ E₀

@[expose] def SeitzThreeResidual5 : Prop :=
  ThreeNonToralCubeRest .F4 LieTypeIndex.F4 ∧
    SeitzGoodInnerExcThreeE6 ∧ SeitzGoodInnerExcThreeTwE6 ∧
    ((∀ (K : Type) [Field K] [Finite K], Nat.card K % 3 = 2 → ThreeScope LieTypeIndex.E7 K → ∀ E₀ :
        Subgroup (adjointGroup .E7 K), IsElemAbelian 3 E₀ → Nat.card E₀ = 3 ^ 3 → ¬ NormalizesRGroup
        (ringChar K) E₀ → ∀ D : LangPlaneData .E7 K E₀, (∀ α : Fin Tag.E7.rank → ℤ, IsRoot .E7 α → ¬
        D.Kills α) → HyperGen 3 ⊤ E₀) ∧ E7NonToralTwoRest) ∧
    ((∀ (K : Type) [Field K] [Finite K], ¬ 3 ∣ Nat.card K → ThreeScope LieTypeIndex.E8 K → ∀ E₀ :
        Subgroup (adjointGroup .E8 K), IsElemAbelian 3 E₀ → Nat.card E₀ = 3 ^ 3 → ¬ NormalizesRGroup
        (ringChar K) E₀ → ∀ D : LangPlaneData .E8 K E₀, (∀ α : Fin Tag.E8.rank → ℤ, IsRoot .E8 α → ¬
        D.Kills α) → D.w ≠ 1 → (∃ u : Fin Tag.E8.rank → ℤ, D.w • u ≠ -u) → HyperGen 3 ⊤
        E₀) ∧ ThreeNonToralCubeRest .E8 LieTypeIndex.E8)

end Residual

section Reduction

theorem mod_three_cases {n : ℕ} (h : ¬ 3 ∣ n) : n % 3 = 1 ∨ n % 3 = 2 := by omega

theorem threeToralCubeRest_F4 : ThreeToralCubeRest .F4 LieTypeIndex.F4 := by
  intro K _ _ hK3 hs E₀ hE₀ hc hN D hreg
  rcases mod_three_cases hK3 with h1 | h2
  · exact (threeToralCubeRest_F4_one K h1 E₀ hE₀ hc hN D hreg).elim
  · have hw := (f4_regular_datum_w hE₀ hc D hreg).2 h2
    exact hyperGen_F4_of_neg_datum h2 hs hE₀ hc D fun u => by
      rw [hw]
      exact CFSG.HardMathSupport.Timmesfeld.CrossChar.f4Neg_smul u

theorem seitzThreeResidual4_of_residual5 (h : SeitzThreeResidual5) : SeitzThreeResidual4 := by
  obtain ⟨hF4n, hE6, hTw, ⟨hE7t, hE7n⟩, ⟨hE8t, hE8n⟩⟩ := h
  refine ⟨⟨threeToralCubeRest_F4, hF4n⟩, hE6, hTw, ⟨?_, ?_⟩, ⟨?_, hE8n⟩⟩
  · intro K _ _ hK3 hs E₀ hE₀ hc hN D hreg
    rcases mod_three_cases hK3 with h1 | h2
    · exact (threeToralCubeRest_E7_one K h1 E₀ hc hN).elim
    · exact hE7t K h2 hs E₀ hE₀ hc hN D hreg
  · intro K _ _ hK3 hs E₀ hE₀ hc hN hD
    rcases mod_three_cases hK3 with h1 | h2
    · exact (threeToralCubeRest_E7_one K h1 E₀ hc hN).elim
    · exact hE7n K h2 hs E₀ hE₀ hc hN hD
  · intro K _ _ hK3 hs E₀ hE₀ hc hN D hreg
    by_cases hw : D.w = 1
    · exact (hN (normalizesRGroup_of_native' (e8_normalizesRNative_of_split_datum D hw))).elim
    by_cases hneg : ∀ u : Fin Tag.E8.rank → ℤ, D.w • u = -u
    · rcases mod_three_cases hK3 with h1 | h2
      · have hbot := eq_bot_of_neg_datum_of_mod_three_eq_one h1 hE₀.2 D hneg
        rw [hbot, Subgroup.card_bot] at hc
        norm_num at hc
      · exact hyperGen_E8_of_neg_datum h2 hs hE₀ hc D hneg
    · push Not at hneg
      exact hE8t K hK3 hs E₀ hE₀ hc hN D hreg hw hneg

end Reduction

end CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.SeitzExcOpenRest5

end
