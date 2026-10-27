module

public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.F4LocalOne
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.SmallQThreeFactsTwoF

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.ChevQ

open CFSG.Open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.HardMathSupport.Timmesfeld.Torality CFSG.HardMathSupport.Timmesfeld.Steinberg
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.LieType.AlgebraicGroups CFSG.RankThree.Chevalley CFSG.RankThree.Classical
  CFSG.RankThree.PartOne.KE CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.HardMathSupport.Timmesfeld.CrossChar.SmallQ3 CFSG.HardMathSupport.Timmesfeld.SporadicBalance
  CFSG.ComponentClassification.OuterAutomorphisms CFSG.LieType.Ree
  CFSG.HardMathSupport.Solomon.LocalBalance

set_option linter.unusedSectionVars false

namespace F4EightOuterFixAux

section Abstract

theorem eq_one_of_pow_three_of_eq_inv {G : Type*} [Group G] {u : G} (h3 : u ^ 3 = 1)
    (h2 : u = u⁻¹) : u = 1 := by
  have h : u * u = 1 := by
    calc u * u = u⁻¹ * u := by rw [← h2]
      _ = 1 := inv_mul_cancel u
  calc u = u * u * u := by rw [h, one_mul]
    _ = u ^ 3 := by rw [pow_succ, pow_two]
    _ = 1 := h3

theorem fix_of_cube {G : Type*} [Group G] {σ : MulAut G} (hσ : σ ^ 2 = 1) {A C : Subgroup G}
    (hA : ∀ a ∈ A, σ a = a) (hC : ∀ y, y ∈ C ↔ ∀ a ∈ A, a * y = y * a)
    (hCC : ∀ x ∈ C, ∀ y ∈ C, x * y = y * x) (hcube : ∀ y ∈ C, y ^ 3 ∈ A)
    (hord : ∀ u ∈ C, u ^ 3 = 1 → u ∈ A) : ∀ y ∈ C, σ y = y := by
  intro y hy
  have hσσ : σ (σ y) = y := by
    have := congrArg (fun f : MulAut G => f y) hσ
    simpa [pow_two] using this
  have hσy : σ y ∈ C := by
    rw [hC]
    intro a ha
    have h1 := (hC y).1 hy a ha
    have h2 : σ (a * y) = σ (y * a) := by rw [h1]
    rw [map_mul, map_mul, hA a ha] at h2
    exact h2
  have hcomm : Commute (σ y) y⁻¹ := hCC (σ y) hσy y⁻¹ (C.inv_mem hy)
  have huC : σ y * y⁻¹ ∈ C := C.mul_mem hσy (C.inv_mem hy)
  have hu3 : (σ y * y⁻¹) ^ 3 = 1 := by
    rw [hcomm.mul_pow, inv_pow, ← map_pow, hA _ (hcube y hy), mul_inv_cancel]
  have huA : σ y * y⁻¹ ∈ A := hord _ huC hu3
  have hσu : σ (σ y * y⁻¹) = (σ y * y⁻¹)⁻¹ := by
    rw [map_mul, map_inv, hσσ, mul_inv_rev, inv_inv]
  have hu2 : σ y * y⁻¹ = (σ y * y⁻¹)⁻¹ := (hA _ huA).symm.trans hσu
  have hu1 : σ y * y⁻¹ = 1 := eq_one_of_pow_three_of_eq_inv hu3 hu2
  exact mul_inv_eq_one.1 hu1

end Abstract

section Port

variable {τ : Tag} {L : Type} [Field L] [CharP L 2]

theorem iterateFrobenius_three_apply (c : L) : iterateFrobenius L 2 3 c = c ^ 8 := by
  rw [iterateFrobenius_def]
  norm_num

theorem entrywise_eight_rootDiagUnit (a : Fin τ.rank → Lˣ) :
    Units.map (entrywiseHom (iterateFrobenius L 2 3)) (rootDiagUnit τ a) =
      rootDiagUnit τ a ^ 8 := by
  change baseChangeGL (iterateFrobenius L 2 3) (rootDiagUnit τ a) = _
  rw [baseChangeGL_rootDiagUnit]
  have h : (fun i => Units.map (iterateFrobenius L 2 3).toMonoidHom (a i)) = a ^ 8 := by
    funext i
    apply Units.ext
    change iterateFrobenius L 2 3 (a i : L) = ((a ^ 8) i : L)
    rw [iterateFrobenius_three_apply, Pi.pow_apply, Units.val_pow_eq_pow_val]
  rw [h]
  exact map_pow (rootDiagUnitHom τ L) a 8

variable {w₀ : WeylGroup τ}

theorem twFrob_rootDiagUnit8 (hw₀ : ∀ u : Fin τ.rank → ℤ, w₀ • u = -u) (a : Fin τ.rank → Lˣ) :
    canonicalRep (coxeterSystem τ) L w₀ *
        Units.map (entrywiseHom (iterateFrobenius L 2 3)) (rootDiagUnit τ a) *
      (canonicalRep (coxeterSystem τ) L w₀)⁻¹ = (rootDiagUnit τ a)⁻¹ ^ 8 := by
  rw [entrywise_eight_rootDiagUnit, ← conj_pow, canonicalRep_conj_rootDiagUnit_of_neg hw₀]

section Fusion

variable [IsAlgClosed L]

theorem exists_conj_dV_twModel8
    (halg : letI := ZMod.algebra L 2; Algebra.IsAlgebraic (ZMod 2) L)
    (hmon : MonomialToralAt τ 3) (hw₀ : ∀ u : Fin τ.rank → ℤ, w₀ • u = -u)
    (hLang : ∀ a : Fin τ.rank → Lˣ, (∀ i, a i ^ 3 = 1) → ∀ c ∈ toralCentralizer τ L a,
      ∃ z ∈ toralCentralizer τ L a,
        z⁻¹ * frobTwistGL τ L 2 3 (canonicalRep (coxeterSystem τ) L w₀) z = c)
    {ω : Lˣ} (hω : orderOf ω = 3) {s : ModGL τ L}
    (hs : s ∈ twModel (canonicalRep (coxeterSystem τ) L w₀) (iterateFrobenius L 2 3))
    (hs3 : s ^ 3 = 1) :
    ∃ u ∈ twModel (canonicalRep (coxeterSystem τ) L w₀) (iterateFrobenius L 2 3),
      ∃ x : Fin τ.rank → ZMod 3, u * s * u⁻¹ = dV ω x := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hnG : canonicalRep (coxeterSystem τ) L w₀ ∈ adjointGroup τ L :=
    canonicalRep_mem_adjointGroup _ L _
  set F := frobTwistGL τ L 2 3 (canonicalRep (coxeterSystem τ) L w₀) with hF
  have hFapp : ∀ g, F g = canonicalRep (coxeterSystem τ) L w₀ *
      Units.map (entrywiseHom (iterateFrobenius L 2 3)) g *
        (canonicalRep (coxeterSystem τ) L w₀)⁻¹ := fun g => rfl
  have hFG : ∀ g ∈ adjointGroup τ L, F g ∈ adjointGroup τ L := fun g hg =>
    mul_mem (mul_mem hnG (entrywiseFrobGL_mem 2 3 hg)) (inv_mem hnG)
  have hsG : s ∈ adjointGroup τ L := hs.1
  have hFs : F s = s := hs.2
  have hfin : ((Subgroup.zpowers s : Subgroup (ModGL τ L)) : Set (ModGL τ L)).Finite :=
    (finite_zpowers).2 (isOfFinOrder_iff_pow_eq_one.2 ⟨3, by norm_num, hs3⟩)
  have hexp : ∀ x ∈ Subgroup.zpowers s, x ^ 3 = 1 := by
    rintro _ ⟨k, rfl⟩
    simp only
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hs3, one_zpow]
  have hzle : Subgroup.zpowers s ≤ adjointGroup τ L := by
    rw [Subgroup.zpowers_le]
    exact hsG
  obtain ⟨c₁, hc₁, hc₁m⟩ := exists_conj_le_monomial_bar (ℓ := 2) (p := 3) (by norm_num) halg
    hzle hfin hexp
  have hmn := hc₁m s (Subgroup.mem_zpowers s)
  have hn3 : (c₁ * s * c₁⁻¹) ^ 3 = 1 := by
    rw [conj_pow, hs3, mul_one, mul_inv_cancel]
  have hL3 : ringChar L ≠ 3 := by
    rw [ringChar.eq L 2]
    norm_num
  obtain ⟨c₂, hc₂, hc₂t⟩ := exists_conj_mem_torusGroup_of_mem_monomial hmon hL3 hmn hn3
  obtain ⟨h, hh⟩ : ∃ h, h = c₂ * c₁ := ⟨_, rfl⟩
  obtain ⟨t, ht⟩ : ∃ t, t = h * s * h⁻¹ := ⟨_, rfl⟩
  have ht' : t = c₂ * (c₁ * s * c₁⁻¹) * c₂⁻¹ := by rw [ht, hh]; group
  have htT : t ∈ torusGroup τ L := ht' ▸ hc₂t
  obtain ⟨a, ha⟩ := torusGroup_le_range_rootDiagUnitHom htT
  have hta : t = rootDiagUnit τ a := ha.symm
  have ht3 : t ^ 3 = 1 := by rw [ht, conj_pow, hs3, mul_one, mul_inv_cancel]
  have ha3 : ∀ i, a i ^ 3 = 1 := by
    have h1 : rootDiagUnitHom τ L (a ^ 3) = rootDiagUnitHom τ L 1 := by
      rw [map_pow, map_one]
      change (rootDiagUnit τ a) ^ 3 = 1
      rw [← hta, ht3]
    have h2 := CFSG.HardMathSupport.Timmesfeld.CrossChar.rootDiagUnit_injective (τ := τ) (K := L) h1
    intro i
    have := congrFun h2 i
    simpa using this
  have hFt : F t = t := by
    rw [hFapp, hta, twFrob_rootDiagUnit8 hw₀ a, inv_pow]
    have hd3 : rootDiagUnit τ a ^ 3 = 1 := by rw [← hta, ht3]
    refine inv_eq_of_mul_eq_one_right ?_
    rw [← pow_succ, show 8 + 1 = 3 * 3 by norm_num, pow_mul, hd3, one_pow]
  obtain ⟨y, hy⟩ : ∃ y, y = h⁻¹ := ⟨_, rfl⟩
  have hyG : y ∈ adjointGroup τ L := hy ▸ inv_mem (hh ▸ mul_mem hc₂ hc₁)
  have hsy : s = y * t * y⁻¹ := by rw [ht, hy]; group
  have hFsy : F y * t * (F y)⁻¹ = s := by
    have := congrArg F hsy
    rw [map_mul, map_mul, map_inv, hFt, hFs] at this
    exact this.symm
  have h1 : F y * t * (F y)⁻¹ = y * t * y⁻¹ := hFsy.trans hsy
  have hcc : y⁻¹ * F y ∈ toralCentralizer τ L a := by
    rw [mem_toralCentralizer]
    refine ⟨mul_mem (inv_mem hyG) (hFG y hyG), ?_⟩
    have h2 : (y⁻¹ * F y) * t = t * (y⁻¹ * F y) := by
      calc (y⁻¹ * F y) * t = y⁻¹ * (F y * t * (F y)⁻¹) * y * (y⁻¹ * F y) := by group
        _ = y⁻¹ * (y * t * y⁻¹) * y * (y⁻¹ * F y) := by rw [h1]
        _ = t * (y⁻¹ * F y) := by group
    rw [← hta]
    calc t * (y⁻¹ * F y) * t⁻¹ = (y⁻¹ * F y) * t * t⁻¹ := by rw [h2]
      _ = y⁻¹ * F y := by group
  obtain ⟨z, hz, hzc⟩ := hLang a ha3 _ hcc
  have hzc' : z⁻¹ * F z = y⁻¹ * F y := hzc
  obtain ⟨hzG, hzt⟩ := mem_toralCentralizer.1 hz
  obtain ⟨u, hu⟩ : ∃ u, u = y * z⁻¹ := ⟨_, rfl⟩
  have hFu : F u = u := by
    have hFz : F z = z * (y⁻¹ * F y) := by rw [← hzc']; group
    rw [hu, map_mul, map_inv, hFz]
    group
  have huG : u ∈ adjointGroup τ L := hu ▸ mul_mem hyG (inv_mem hzG)
  have hut : u * t * u⁻¹ = s := by
    have hzt' : z * t = t * z := by
      have h3 : t * z * t⁻¹ = z := by rw [hta]; exact hzt
      calc z * t = (t * z * t⁻¹) * t := by rw [h3]
        _ = t * z := by group
    rw [hsy, hu]
    calc y * z⁻¹ * t * (y * z⁻¹)⁻¹ = y * (z⁻¹ * (t * z)) * y⁻¹ := by group
      _ = y * (z⁻¹ * (z * t)) * y⁻¹ := by rw [hzt']
      _ = y * t * y⁻¹ := by group
  have huW : u ∈ twModel (canonicalRep (coxeterSystem τ) L w₀) (iterateFrobenius L 2 3) :=
    ⟨huG, hFu⟩
  have hω3 : ω ^ 3 = 1 := by rw [← hω]; exact pow_orderOf_eq_one ω
  choose m hm using fun i => exists_eq_pow_of_pow_three hω (ha3 i)
  set x : Fin τ.rank → ZMod 3 := fun i => (m i : ZMod 3) with hx
  have hax : torV ω x = a := by
    funext i
    rw [hm i, torV, hx, ZMod.val_natCast]
    conv_rhs => rw [← Nat.mod_add_div (m i) 3]
    rw [pow_add, pow_mul, hω3, one_pow, mul_one]
  refine ⟨u⁻¹, inv_mem huW, x, ?_⟩
  change u⁻¹ * s * u⁻¹⁻¹ = rootDiagUnit τ (torV ω x)
  rw [hax, ← hta, ← hut]
  group

theorem exists_torV_eq {ω : Lˣ} (hω : orderOf ω = 3) {b : Fin τ.rank → Lˣ}
    (hb : ∀ i, b i ^ 3 = 1) : ∃ x : Fin τ.rank → ZMod 3, torV ω x = b := by
  have hω3 : ω ^ 3 = 1 := by rw [← hω]; exact pow_orderOf_eq_one ω
  choose m hm using fun i => exists_eq_pow_of_pow_three hω (hb i)
  refine ⟨fun i => (m i : ZMod 3), ?_⟩
  funext i
  rw [hm i, torV, ZMod.val_natCast]
  conv_rhs => rw [← Nat.mod_add_div (m i) 3]
  rw [pow_add, pow_mul, hω3, one_pow, mul_one]

theorem dV_mem_twModel8 (htorL : ∀ a : Fin τ.rank → Lˣ, rootDiagUnit τ a ∈ torusGroup τ L)
    (hw₀ : ∀ u : Fin τ.rank → ℤ, w₀ • u = -u) {ω : Lˣ} (hω3 : ω ^ 3 = 1)
    (x : Fin τ.rank → ZMod 3) :
    dV ω x ∈ twModel (canonicalRep (coxeterSystem τ) L w₀) (iterateFrobenius L 2 3) :=
  twistedTorus_le_twModel _ _ ((mem_twistedTorus_of_neg htorL hw₀
    (fun c => iterateFrobenius_three_apply c)).2
    ⟨torV ω x, rfl, fun i => by
      show (ω ^ (x i).val) ^ (8 + 1) = 1
      rw [← pow_mul, show (x i).val * (8 + 1) = 3 * (3 * (x i).val) by ring, pow_mul, hω3,
        one_pow]⟩)

end Fusion

section Main

theorem exists_map_le_ree (K : Type) [Field K] [Finite K] [CharP K ReeTag.F4.prime]
    (hK : Nat.card K = 2 ^ 3) {σ : MulAut ↥(adjointGroup ReeTag.F4.tag K)} (hσ2 : σ ^ 2 = 1)
    (hσi : σ ∉ (MulAut.conj : ↥(adjointGroup ReeTag.F4.tag K) →*
      MulAut ↥(adjointGroup ReeTag.F4.tag K)).range)
    {H : Subgroup ↥(adjointGroup ReeTag.F4.tag K)} (hH : ∀ g ∈ H, σ g = g) :
    ∃ ψ : MulAut ↥(adjointGroup ReeTag.F4.tag K),
      H.map ψ.toMonoidHom ≤ ReeTag.F4.finiteReeFixedGroup K 1 := by
  obtain ⟨ψ, hψ, -⟩ := even_F4_all_outer_involutions_canonical (f := 3) (by norm_num) K hK σ hσ2
    hσi
  obtain ⟨-, -, -, -, -, -, hodd⟩ := even_F4_exact_automorphism_normal_form (f := 3) (by norm_num)
    K hK
  obtain ⟨-, -, hFIX⟩ := hodd 1 (by norm_num)
  refine ⟨ψ, ?_⟩
  rintro _ ⟨g, hg, rfl⟩
  refine (hFIX _).2 ?_
  have hσg : σ g = g := hH g hg
  rw [← hψ]
  change ψ (σ (ψ⁻¹ (ψ g))) = ψ g
  rw [MulAut.inv_apply_self, hσg]

theorem exists_torus_data (K : Type) [Field K] [Finite K] (hK : Nat.card K = 2 ^ 3)
    (s : ↥(adjointGroup Tag.F4 K)) (hs3 : orderOf s = 3) :
    ∃ E T : Subgroup ↥(adjointGroup Tag.F4 K), IsElemAbelian 3 E ∧ Nat.card E = 3 ^ 4 ∧ s ∈ E ∧
      Nat.card T = 9 ^ 4 ∧ (∀ t ∈ T, ∀ a ∈ E, t * a = a * t) ∧
      ∀ σ : MulAut ↥(adjointGroup Tag.F4 K), σ ^ 2 = 1 →
        (∀ a ∈ E, σ a = a) → ∀ g ∈ T, σ g = g := by
  classical
  have hchar : CharP K 2 := finite_field_prime_power_characteristic Nat.prime_two (by norm_num) hK
  haveI : CharP K 2 := hchar
  haveI : CharP K ReeTag.F4.prime := hchar
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : CharP (AlgebraicClosure K) 2 :=
    charP_of_injective_algebraMap (algebraMap K (AlgebraicClosure K)).injective 2
  obtain ⟨Fr, hFr, g0, hg0C, hg0⟩ := exists_lang_data Tag.F4 K f4Neg
  have hFr2 : Fr = iterateFrobenius (AlgebraicClosure K) 2 3 :=
    RingHom.ext fun c => by rw [hFr, hK, iterateFrobenius_three_apply]; norm_num
  subst hFr2
  set L := AlgebraicClosure K with hL
  set n := canonicalRep (coxeterSystem Tag.F4) L f4Neg with hn
  set W := twModel n (iterateFrobenius L 2 3) with hW
  haveI : Finite W := finite_twModelF4 K L hFr hg0C hg0
  let e : adjointGroup Tag.F4 K ≃* W := twModelEquivF4 K L hFr hg0C hg0
  have htorL : ∀ a : Fin Tag.F4.rank → Lˣ, rootDiagUnit Tag.F4 a ∈ torusGroup Tag.F4 L :=
    rootDiagUnit_mem_torusGroup_of_unimodular exists_mul_cartan_F4.choose_spec
  have hFr8 : ∀ c : L, iterateFrobenius L 2 3 c = c ^ 8 := fun c => iterateFrobenius_three_apply c
  obtain ⟨ω, hω, -⟩ := exists_orderOf_eq_of_dvd_add_one K (L := L) (N := 3)
    (by rw [hK]; norm_num)
  have hω3 : ω ^ 3 = 1 := by rw [← hω]; exact pow_orderOf_eq_one ω
  have hG : ∀ x, dV (τ := Tag.F4) ω x ∈ W := dV_mem_twModel8 htorL f4Neg_smul hω3
  have hLang : ∀ a : Fin Tag.F4.rank → Lˣ, (∀ i, a i ^ 3 = 1) → ∀ c ∈ toralCentralizer Tag.F4 L a,
      ∃ z ∈ toralCentralizer Tag.F4 L a, z⁻¹ * frobTwistGL Tag.F4 L 2 3 n z = c :=
    fun a ha3 c hc =>
    toral_centralizer_Lang_F4_three 2 L (by norm_num) a ha3 3 (by norm_num)
      (canonicalRep_mem_adjointGroup _ _ _) (s := 2) (by norm_num)
      (canonicalRep_conj_rootDiagUnit_sq f4Neg_smul ha3) c hc
  have hfus : ∀ s ∈ W, s ^ 3 = 1 → ∃ u ∈ W, ∃ x : Fin Tag.F4.rank → ZMod 3,
      u * s * u⁻¹ = dV ω x := fun s hs hs3 =>
    exists_conj_dV_twModel8 (isAlgebraic_zmod_algebraicClosure_of_finite K 2)
      (monomialToralAt_three_of_block a2BlockToral_F4) f4Neg_smul hLang hω hs hs3
  have hcert : Native.hypOK Tag.F4 = true := Certificates.certificate13666.1
  have hs3' : s ^ 3 = 1 := by rw [← hs3]; exact pow_orderOf_eq_one s
  have hes3 : ((e s : W) : ModGL Tag.F4 L) ^ 3 = 1 := by
    have h1 : (e s) ^ 3 = 1 := by rw [← map_pow, hs3', map_one]
    have := congrArg (fun m : W => (m : ModGL Tag.F4 L)) h1
    simpa using this
  obtain ⟨u, huW, x, hux⟩ := hfus _ (e s).2 hes3
  set uW : W := ⟨u, huW⟩ with huW'
  set φt : W ≃* adjointGroup Tag.F4 K := (MulAut.conj uW⁻¹).trans e.symm with hφt
  have hφt_symm : ∀ y, ((φt.symm y : W) : ModGL Tag.F4 L) =
      u * (e y : ModGL Tag.F4 L) * u⁻¹ := fun y => by
    simp [hφt, huW']
  have htx : φt.symm s = dG hG x := Subtype.ext ((hφt_symm s).trans hux)
  set AW : Subgroup W := (dGHom hω3 hG).range with hAW
  have hAWcomm : ∀ a ∈ AW, ∀ b ∈ AW, a * b = b * a := by
    rintro _ ⟨y, rfl⟩ _ ⟨z, rfl⟩
    rw [← map_mul, ← map_mul, mul_comm]
  have hxAW : dG hG x ∈ AW := ⟨Multiplicative.ofAdd x, dGHom_ofAdd hω3 hG x⟩
  have hdAW : ∀ z, dG hG z ∈ AW := fun z => ⟨Multiplicative.ofAdd z, dGHom_ofAdd hω3 hG z⟩
  have hAW3 : ∀ y₀ ∈ AW, y₀ ^ 3 = 1 := by
    rintro _ ⟨z, rfl⟩
    apply Subtype.ext
    change (dV ω z.toAdd) ^ 3 = 1
    exact dV_pow_three hω3 z.toAdd
  have hAWcard : Nat.card AW = 3 ^ 4 := by
    have hinj : Function.Injective (dGHom hω3 hG) := by
      intro a b hab
      have h1 := congrArg Subtype.val hab
      rw [← ofAdd_toAdd a, ← ofAdd_toAdd b, dGHom_ofAdd, dGHom_ofAdd] at h1
      have h2 := dV_injective (τ := Tag.F4) hω h1
      rw [← ofAdd_toAdd a, ← ofAdd_toAdd b, h2]
    rw [hAW, MonoidHom.range_eq_map, Subgroup.card_map_of_injective hinj, Subgroup.card_top,
      Nat.card_eq_fintype_card]
    simp [Fintype.card_multiplicative, Fintype.card_pi, ZMod.card]
    rfl
  set C : Subgroup W := Subgroup.centralizer (AW : Set W) with hCdef
  have hC : ∀ y, y ∈ C ↔ ∀ a ∈ AW, a * y = y * a := fun y => Subgroup.mem_centralizer_iff
  have hCtor : ∀ y ∈ C, ∃ b : Fin Tag.F4.rank → Lˣ,
      (y : ModGL Tag.F4 L) = rootDiagUnit Tag.F4 b ∧ ∀ i, b i ^ 9 = 1 := by
    intro y hy
    have hcomm : ∀ z : Fin Tag.F4.rank → ZMod 3, Commute (dV ω z) (y : ModGL Tag.F4 L) := by
      intro z
      have h1 := (hC y).1 hy _ (hdAW z)
      exact congrArg Subtype.val h1
    have hyT : (y : ModGL Tag.F4 L) ∈ torusGroup Tag.F4 L :=
      mem_torusGroup_of_commute_dV hω hcert y.2.1 hcomm
    obtain ⟨b, hb, hb9⟩ := (mem_twistedTorus_of_neg htorL f4Neg_smul hFr8).1
      (mem_twistedTorus.2 ⟨hyT, y.2.2⟩)
    exact ⟨b, hb, fun i => hb9 i⟩
  have hCC : ∀ x ∈ C, ∀ y ∈ C, x * y = y * x := by
    intro x hx y hy
    obtain ⟨a, ha, -⟩ := hCtor x hx
    obtain ⟨b, hb, -⟩ := hCtor y hy
    apply Subtype.ext
    change (x : ModGL Tag.F4 L) * y = y * x
    rw [ha, hb]
    exact ((Commute.all a b).map (rootDiagUnitHom Tag.F4 L)).eq
  have hcube : ∀ y ∈ C, y ^ 3 ∈ AW := by
    intro y hy
    obtain ⟨b, hb, hb9⟩ := hCtor y hy
    have hb3 : ∀ i, (b ^ 3) i ^ 3 = 1 := fun i => by
      rw [Pi.pow_apply, ← pow_mul]
      exact hb9 i
    obtain ⟨z, hz⟩ := exists_torV_eq hω hb3
    refine ⟨Multiplicative.ofAdd z, Subtype.ext ?_⟩
    rw [dGHom_ofAdd hω3 hG z]
    change dV ω z = (y : ModGL Tag.F4 L) ^ 3
    rw [dV, hz, hb]
    exact map_pow (rootDiagUnitHom Tag.F4 L) b 3
  have hord : ∀ u' ∈ C, u' ^ 3 = 1 → u' ∈ AW := by
    intro u' hu' hu3'
    obtain ⟨b, hb, hb9⟩ := hCtor u' hu'
    have hb3 : ∀ i, b i ^ 3 = 1 := by
      have h2 : (u' : ModGL Tag.F4 L) ^ 3 = 1 := by
        have := congrArg (fun m : W => (m : ModGL Tag.F4 L)) hu3'
        simpa using this
      have h1 : rootDiagUnitHom Tag.F4 L (b ^ 3) = rootDiagUnitHom Tag.F4 L 1 := by
        rw [map_pow, map_one]
        change (rootDiagUnit Tag.F4 b) ^ 3 = 1
        rw [← hb]
        exact h2
      have h3 := CFSG.HardMathSupport.Timmesfeld.CrossChar.rootDiagUnit_injective
        (τ := Tag.F4) (K := L) h1
      intro i
      have := congrFun h3 i
      simpa using this
    obtain ⟨z, hz⟩ := exists_torV_eq hω hb3
    refine ⟨Multiplicative.ofAdd z, Subtype.ext ?_⟩
    rw [dGHom_ofAdd hω3 hG z]
    change dV ω z = (u' : ModGL Tag.F4 L)
    rw [dV, hz, hb]
  obtain ⟨ζ, hζ, hζpow⟩ := exists_orderOf_eq_of_dvd_add_one K (L := L) (N := 9)
    (by rw [hK]; norm_num)
  have hζ' : ζ ^ (8 + 1) = 1 := by
    rw [hK] at hζpow
    simpa using hζpow
  obtain ⟨H₀, hH₀T, hH₀card⟩ := exists_le_twistedTorus_card htorL f4Neg_smul hFr8 hζ'
  have hH₀W : H₀ ≤ W := hH₀T.trans (twistedTorus_le_twModel n _)
  set HW : Subgroup W := H₀.subgroupOf W with hHW
  have hHWcard : Nat.card HW = 9 ^ 4 := by
    rw [hHW, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hH₀W).toEquiv, hH₀card, hζ]
    rfl
  have hHWC : HW ≤ C := by
    intro h hh
    rw [hC]
    intro a ha
    obtain ⟨b, hb, -⟩ := (mem_twistedTorus_of_neg htorL f4Neg_smul hFr8).1
      (hH₀T (Subgroup.mem_subgroupOf.1 hh))
    obtain ⟨zz, rfl⟩ := ha
    apply Subtype.ext
    change (dV ω zz.toAdd) * (h : ModGL Tag.F4 L) = (h : ModGL Tag.F4 L) * dV ω zz.toAdd
    rw [hb]
    exact ((Commute.all (torV ω zz.toAdd) b).map (rootDiagUnitHom Tag.F4 L)).eq
  refine ⟨AW.map φt.toMonoidHom, HW.map φt.toMonoidHom, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · refine ⟨⟨⟨fun a b => ?_⟩⟩, fun y hy => ?_⟩
    · obtain ⟨a₀, ha₀, ha⟩ := Subgroup.mem_map.1 a.2
      obtain ⟨b₀, hb₀, hb⟩ := Subgroup.mem_map.1 b.2
      apply Subtype.ext
      change (a : ↥(adjointGroup Tag.F4 K)) * b = b * a
      rw [← ha, ← hb, ← map_mul, ← map_mul, hAWcomm a₀ ha₀ b₀ hb₀]
    · obtain ⟨y₀, hy₀, rfl⟩ := Subgroup.mem_map.1 hy
      rw [← map_pow, hAW3 y₀ hy₀, map_one]
  · rw [Subgroup.card_map_of_injective (f := φt.toMonoidHom) φt.injective, hAWcard]
  · exact ⟨dG hG x, hxAW, by rw [MulEquiv.coe_toMonoidHom, ← htx, MulEquiv.apply_symm_apply]⟩
  · rw [Subgroup.card_map_of_injective (f := φt.toMonoidHom) φt.injective, hHWcard]
  · rintro _ ⟨t, ht, rfl⟩ _ ⟨a, ha, rfl⟩
    have h1 := (hC t).1 (hHWC ht) a ha
    change φt t * φt a = φt a * φt t
    rw [← map_mul, ← map_mul, h1.symm]
  · intro σ hσ2 hσfix g hg
    obtain ⟨y, hy, rfl⟩ := hg
    set σW : MulAut W := MulAut.congr φt.symm σ with hσWdef
    have hσW : ∀ y, σW y = φt.symm (σ (φt y)) := fun y => by
      simp [hσWdef, MulAut.congr_apply]
    have hσW2 : σW ^ 2 = 1 := by rw [hσWdef, ← map_pow, hσ2, map_one]
    have hσWfix : ∀ a ∈ AW, σW a = a := by
      intro a ha
      rw [hσW, hσfix (φt a) ⟨a, ha, rfl⟩]
      simp
    have hfixC := fix_of_cube hσW2 hσWfix hC hCC hcube hord
    have h1 := hfixC y (hHWC hy)
    rw [hσW] at h1
    have h2 := congrArg φt h1
    simpa using h2

theorem noOuterFixesCentralizer_eight (K : Type) [Field K] [Finite K] (hK : Nat.card K = 2 ^ 3) :
    NoOuterFixesCentralizer 3 ↥(adjointGroup Tag.F4 K) := by
  classical
  intro σ hσ2 hσi s hs3
  by_contra hcon
  push Not at hcon
  have hchar : CharP K 2 := finite_field_prime_power_characteristic Nat.prime_two (by norm_num) hK
  haveI : CharP K ReeTag.F4.prime := hchar
  obtain ⟨E, T, hEel, hEcard, hsE, hTcard, -, hT⟩ := exists_torus_data K hK s hs3
  have hEfix : ∀ a ∈ E, σ a = a := fun a ha => hcon a (by
    have := hEel.1.is_comm.comm (⟨s, hsE⟩ : E) ⟨a, ha⟩
    exact congrArg Subtype.val this)
  obtain ⟨ψ, hle⟩ := exists_map_le_ree K hK hσ2 hσi (hT σ hσ2 hEfix)
  have hdvd := Subgroup.card_dvd_of_le hle
  have hcm : Nat.card (T.map ψ.toMonoidHom) = Nat.card T :=
    Subgroup.card_map_of_injective ψ.injective
  rw [hcm, hTcard] at hdvd
  have hR : Nat.card (ReeTag.F4.finiteReeFixedGroup K 1) = Nat.card (ReeTag.F4.reeGamma K 1) :=
    (Subgroup.card_map_of_injective (adjointGroup ReeTag.F4.tag K).subtype_injective).symm
  have hK' : Nat.card K = 2 ^ (2 * 1 + 1) := by rw [hK]
  have hordR := (CFSG.RankThree.LargeReeOrder.large_Ree_exact_native_order_and_prime_factor_exhaustion
    1 K hK').1
  rw [hR, hordR] at hdvd
  norm_num at hdvd

end Main

end Port

end F4EightOuterFixAux

section Final

theorem f4EightNoOuterFixes_holds : F4LocalOneAux.F4EightNoOuterFixes :=
  fun K _ _ hK => F4EightOuterFixAux.noOuterFixesCentralizer_eight K hK

end Final

end CFSG.HardMathSupport.Solomon.Coordinator.ChevQ
