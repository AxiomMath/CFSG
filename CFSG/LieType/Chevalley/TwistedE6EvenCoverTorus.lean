module

public import CFSG.LieType.Chevalley.TwistedE6EvenCoverArith
public import CFSG.LieType.Chevalley.ExceptionalLargeEvenCoverHeight
public import CFSG.LieType.Chevalley.GraphFixedHighestRoot

public noncomputable section

namespace CFSG.LieType.Chevalley.TwistedE6Cover

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.LieType.Chevalley.ExceptionalCover

theorem prod_zpow_eq_zpow_sum {G ι : Type*} [CommGroup G] (a : G) (s : Finset ι) (f : ι → ℤ) :
    ∏ i ∈ s, a ^ f i = a ^ ∑ i ∈ s, f i := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih => rw [Finset.prod_insert hi, Finset.sum_insert hi, ih, zpow_add]

theorem list_prod_mulSingle_apply {ι M : Type*} [DecidableEq ι] [CommMonoid M] {l : List ι}
    (hl : l.Nodup) (x : M) (i : ι) :
    (l.map fun j => (Pi.mulSingle j x : ι → M)).prod i = if i ∈ l then x else 1 := by
  induction l with
  | nil => simp
  | cons j l ih =>
    rw [List.map_cons, List.prod_cons, Pi.mul_apply, ih hl.tail]
    by_cases hij : i = j
    · subst hij
      have hn : i ∉ l := (List.nodup_cons.1 hl).1
      simp [hn]
    · simp [hij]

variable {K : Type} [Field K] (σ : K →+* K)

@[expose] def fixField : Subfield K :=
  RingHom.eqLocusField σ (RingHom.id K)

variable {σ}

theorem mem_fixField {c : K} : c ∈ fixField σ ↔ σ c = c :=
  RingHom.mem_eqLocusField

theorem pow_apply_of_mem_fixField {c : K} (hc : c ∈ fixField σ) (k : ℕ) : (σ ^ k) c = c := by
  induction k with
  | zero => rfl
  | succ k ih => rw [pow_succ', RingHom.coe_mul, Function.comp_apply, ih, mem_fixField.1 hc]

theorem fixField_le_orbitField (a : Fin TwistTag.E6.foldedTag.rank) :
    fixField σ ≤ orbitField TwistTag.E6 K σ a := fun _ hc =>
  mem_orbitField.2 (pow_apply_of_mem_fixField hc _)

variable (σ) in
@[expose] def fixUnit : (fixField σ)ˣ →* Kˣ :=
  Units.map (fixField σ).subtype.toMonoidHom

theorem coe_fixUnit (u : (fixField σ)ˣ) : (fixUnit σ u : K) = ((u : fixField σ) : K) :=
  rfl

variable (σ) in
@[expose] def torusLift :
    (Fin TwistTag.E6.foldedTag.rank → (fixField σ)ˣ) →* (Fin TwistTag.E6.tag.rank → Kˣ) where
  toFun t i := fixUnit σ (t (TwistTag.E6.orbitIndex i))
  map_one' := by
    funext i
    simp
  map_mul' t t' := by
    funext i
    simp

theorem torusLift_apply (t : Fin TwistTag.E6.foldedTag.rank → (fixField σ)ˣ)
    (i : Fin TwistTag.E6.tag.rank) : torusLift σ t i = fixUnit σ (t (TwistTag.E6.orbitIndex i)) :=
  rfl

variable (σ) in
@[expose] def fixedTorus :
    (Fin TwistTag.E6.foldedTag.rank → (fixField σ)ˣ) →* ModGL TwistTag.E6.tag K :=
  (torusVec TwistTag.E6.tag K).comp (torusLift σ)

theorem fixedTorus_apply
    (t : Fin TwistTag.E6.foldedTag.rank → (fixField σ)ˣ) :
    fixedTorus σ t = torusVec TwistTag.E6.tag K (torusLift σ t) :=
  rfl

theorem torusLift_mulSingle (a : Fin TwistTag.E6.foldedTag.rank) (u : (fixField σ)ˣ) :
    torusLift σ (Pi.mulSingle a u) =
      ((TwistTag.E6.orbitWord a).map fun j => Pi.mulSingle j (fixUnit σ u)).prod := by
  funext i
  rw [list_prod_mulSingle_apply (TwistTag.E6.nodup_orbitWord a), torusLift_apply]
  by_cases hi : TwistTag.E6.orbitIndex i = a
  · have hi' : i ∈ TwistTag.E6.orbitWord a :=
      (TwistTag.E6.mem_orbitWord).2 ((TwistTag.E6.mem_orbit_iff).2 hi)
    rw [ite_eq_left hi', hi, Pi.mulSingle_eq_same]
  · have hi' : i ∉ TwistTag.E6.orbitWord a := fun h =>
      hi ((TwistTag.E6.mem_orbit_iff).1 ((TwistTag.E6.mem_orbitWord).1 h))
    rw [ite_eq_right hi', Pi.mulSingle_eq_of_ne hi, map_one]

theorem fixedTorus_mulSingle
    (a : Fin TwistTag.E6.foldedTag.rank) (u : (fixField σ)ˣ) :
    fixedTorus σ (Pi.mulSingle a u) = (orbitH TwistTag.E6 K σ a
      (Units.map (Subfield.inclusion (fixField_le_orbitField a)).toMonoidHom u) :
        ModGL TwistTag.E6.tag K) := by
  rw [fixedTorus_apply, torusLift_mulSingle, map_list_prod, List.map_map, coe_orbitH_eq]
  refine congrArg List.prod (List.map_congr_left fun j hj => ?_)
  rw [Function.comp_apply, torusVec_mulSingle]
  congr 1
  obtain ⟨k, hk, rfl⟩ := TwistTag.E6.exists_eq_perm_pow_orbitMin ((TwistTag.E6.mem_orbitWord).1 hj)
  rw [orbitUnitParam_pow TwistTag.E6 σ _ hk]
  refine Units.ext ?_
  change ((u : fixField σ) : K) = (σ ^ k) ((u : fixField σ) : K)
  rw [pow_apply_of_mem_fixField (u : fixField σ).2]

theorem fixedTorus_mem_graphFixedRootGroup
    (t : Fin TwistTag.E6.foldedTag.rank → (fixField σ)ˣ) :
    fixedTorus σ t ∈ graphFixedRootGroup TwistTag.E6 K σ := by
  classical
  rw [← Finset.univ_prod_mulSingle t]
  refine Finset.prod_induction _ (fun x => fixedTorus σ x ∈ graphFixedRootGroup TwistTag.E6 K σ)
    (fun x y hx hy => by rw [map_mul]; exact mul_mem hx hy) (by rw [map_one]; exact one_mem _)
    fun a _ => ?_
  rw [fixedTorus_mulSingle]
  exact orbitH_mem_graphFixedRootGroup TwistTag.E6 σ a _

theorem fixedTorus_mem_twistedFixedGroup
    (t : Fin TwistTag.E6.foldedTag.rank → (fixField σ)ˣ) :
    fixedTorus σ t ∈ twistedFixedGroup TwistTag.E6 K σ :=
  graphFixedRootGroup_le TwistTag.E6 K σ (fixedTorus_mem_graphFixedRootGroup t)

variable (σ) in
@[expose] def foldChar (β : Fin TwistTag.E6.tag.rank → ℤ) :
    (Fin TwistTag.E6.foldedTag.rank → (fixField σ)ˣ) →* (fixField σ)ˣ where
  toFun t := ∏ a, t a ^ foldCoord β a
  map_one' := by simp
  map_mul' t t' := by
    simp only [Pi.mul_apply, mul_zpow]
    exact Finset.prod_mul_distrib

theorem foldChar_apply (β : Fin TwistTag.E6.tag.rank → ℤ)
    (t : Fin TwistTag.E6.foldedTag.rank → (fixField σ)ˣ) :
    foldChar σ β t = ∏ a, t a ^ foldCoord β a :=
  rfl

theorem foldChar_mulSingle (β : Fin TwistTag.E6.tag.rank → ℤ) (a : Fin TwistTag.E6.foldedTag.rank)
    (u : (fixField σ)ˣ) : foldChar σ β (Pi.mulSingle a u) = u ^ foldCoord β a := by
  classical
  rw [foldChar_apply, Finset.prod_eq_single a]
  · rw [Pi.mulSingle_eq_same]
  · intro b _ hb
    rw [Pi.mulSingle_eq_of_ne hb, one_zpow]
  · intro ha
    exact absurd (Finset.mem_univ a) ha

theorem rootChar_torusLift (β : Fin TwistTag.E6.tag.rank → ℤ)
    (t : Fin TwistTag.E6.foldedTag.rank → (fixField σ)ˣ) :
    rootChar K β (torusLift σ t) = fixUnit σ (foldChar σ β t) := by
  classical
  rw [rootChar_apply, foldChar_apply]
  have e1 : ∀ i, torusLift σ t i ^ cartanCoord β i =
      fixUnit σ (t (TwistTag.E6.orbitIndex i) ^ cartanCoord β i) := fun i => by
    rw [torusLift_apply, map_zpow]
  simp only [e1]
  rw [← map_prod (fixUnit σ)]
  congr 1
  rw [← Finset.prod_fiberwise Finset.univ TwistTag.E6.orbitIndex]
  refine Finset.prod_congr rfl fun a _ => ?_
  have hfib : Finset.univ.filter (fun i => TwistTag.E6.orbitIndex i = a) = TwistTag.E6.orbit a := by
    ext i
    simp [TwistTag.E6.mem_orbit_iff]
  rw [foldCoord, ← prod_zpow_eq_zpow_sum, ← hfib]
  refine Finset.prod_congr rfl fun i hi => ?_
  rw [(Finset.mem_filter.1 hi).2]

theorem fixedTorus_conj_pinnedX
    {β : Fin TwistTag.E6.tag.rank → ℤ}
    (hβ : IsRoot TwistTag.E6.tag β) (t : Fin TwistTag.E6.foldedTag.rank → (fixField σ)ˣ) (c : K) :
    fixedTorus σ t * pinnedX TwistTag.E6.tag K β c * (fixedTorus σ t)⁻¹ =
      pinnedX TwistTag.E6.tag K β (((foldChar σ β t : fixField σ) : K) * c) := by
  rw [fixedTorus_apply, torusVec_conj_pinnedX hβ, rootChar_torusLift, coe_fixUnit]

theorem foldChar_of_mem_diagramOrbit
    {α β : Fin TwistTag.E6.tag.rank → ℤ}
    (hα : IsRoot TwistTag.E6.tag α) (hβ : β ∈ TwistTag.E6.diagramOrbit α) :
    foldChar σ β = foldChar σ α :=
  MonoidHom.ext fun t => by
    rw [foldChar_apply, foldChar_apply, foldCoord_of_mem_diagramOrbit hα hβ]

theorem card_orbit_le_order (a : Fin TwistTag.E6.foldedTag.rank) :
    (TwistTag.E6.orbit a).card ≤ TwistTag.E6.order := by
  revert a
  decide

theorem canonicalRep_conj_orbitX_charTwo
    (h2 : (2 : K) = 0) (w : WeylGroup TwistTag.E6.tag)
    (a : Fin TwistTag.E6.foldedTag.rank) (c : orbitField TwistTag.E6 K σ a) :
    canonicalRep (coxeterSystem TwistTag.E6.tag) K w *
        (orbitX TwistTag.E6 K σ a c : ModGL TwistTag.E6.tag K) *
        (canonicalRep (coxeterSystem TwistTag.E6.tag) K w)⁻¹ =
      ((List.range (TwistTag.E6.orbit a).card).map fun k =>
        pinnedX TwistTag.E6.tag K
          (w • Pi.single ((TwistTag.E6.perm ^ k) (TwistTag.E6.orbitMin a)) 1)
          ((σ ^ k) (c : K))).prod := by
  rw [coe_orbitX, ← MulAut.conj_apply, map_list_prod, List.map_map]
  refine congrArg List.prod (List.map_congr_left fun k _ => ?_)
  rw [Function.comp_apply, MulAut.conj_apply, ← pinnedX_single,
    canonicalRep_mul_pinnedX_mul_inv_of_two h2 w (isRoot_single _ _)]

theorem fixedTorus_conj_orbitConj
    (h2 : (2 : K) = 0) {w : WeylGroup TwistTag.E6.tag}
    (hw : w ∈ relWeylTwist TwistTag.E6) (a : Fin TwistTag.E6.foldedTag.rank)
    (t : Fin TwistTag.E6.foldedTag.rank → (fixField σ)ˣ) (c : orbitField TwistTag.E6 K σ a) :
    fixedTorus σ t * (canonicalRep (coxeterSystem TwistTag.E6.tag) K w *
        (orbitX TwistTag.E6 K σ a c : ModGL TwistTag.E6.tag K) *
        (canonicalRep (coxeterSystem TwistTag.E6.tag) K w)⁻¹) * (fixedTorus σ t)⁻¹ =
      canonicalRep (coxeterSystem TwistTag.E6.tag) K w *
        (orbitX TwistTag.E6 K σ a
          (Subfield.inclusion (fixField_le_orbitField a)
            (foldChar σ (w • Pi.single (TwistTag.E6.orbitMin a) 1) t : fixField σ) * c) :
          ModGL TwistTag.E6.tag K) *
        (canonicalRep (coxeterSystem TwistTag.E6.tag) K w)⁻¹ := by
  rw [canonicalRep_conj_orbitX_charTwo h2, canonicalRep_conj_orbitX_charTwo h2, ← MulAut.conj_apply,
    map_list_prod, List.map_map]
  refine congrArg List.prod (List.map_congr_left fun k hk => ?_)
  have hk' : k < TwistTag.E6.order := (List.mem_range.1 hk).trans_le (card_orbit_le_order a)
  have hroot : IsRoot TwistTag.E6.tag (w • Pi.single (TwistTag.E6.orbitMin a) 1) :=
    IsRoot.smul (isRoot_single _ _) w
  have hmem : w • (Pi.single ((TwistTag.E6.perm ^ k) (TwistTag.E6.orbitMin a)) 1 :
      Fin TwistTag.E6.tag.rank → ℤ) ∈
      TwistTag.E6.diagramOrbit (w • Pi.single (TwistTag.E6.orbitMin a) 1) :=
    Finset.mem_image.2 ⟨k, Finset.mem_range.2 hk', by
      rw [TwistTag.E6.permLattice_pow_smul hw, permLattice_single]⟩
  rw [Function.comp_apply, MulAut.conj_apply,
    fixedTorus_conj_pinnedX (IsRoot.smul (isRoot_single _ _) w),
    foldChar_of_mem_diagramOrbit hroot hmem]
  congr 1
  change _ = (σ ^ k) (((foldChar σ _ t : fixField σ) : K) * (c : K))
  rw [map_mul, pow_apply_of_mem_fixField (foldChar σ _ t : fixField σ).2]

theorem form_eq_zero_of_chars {k : Type*} [Field k] [Finite k] [CharP k 2] {f : ℕ} (hf : 1 ≤ f)
    (hk : Nat.card k = 2 ^ f) {T : Type*} (χ ψ : T → kˣ)
    (hnd : ∀ i j : ℕ, i < f → j < f → ∃ t, χ t ^ 2 ^ i * ψ t ^ 2 ^ j ≠ 1)
    (F : k → k → ZMod 2) (hF₁ : ∀ c₁ c₂ d, F (c₁ + c₂) d = F c₁ d + F c₂ d)
    (hF₂ : ∀ c d₁ d₂, F c (d₁ + d₂) = F c d₁ + F c d₂)
    (hFT : ∀ t c d, F ((χ t : k) * c) ((ψ t : k) * d) = F c d) :
    ∀ c d, F c d = 0 := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let ι : ZMod 2 →+* k := ZMod.castHom (dvd_refl 2) k
  have hι : Function.Injective ι := ι.injective
  let G : k →+ k →+ k := AddMonoidHom.mk'
    (fun c => AddMonoidHom.mk' (fun d => ι (F c d)) fun d₁ d₂ => by rw [hF₂, map_add])
    fun c₁ c₂ => by
      ext d
      simp only [AddMonoidHom.mk'_apply, AddMonoidHom.add_apply]
      rw [hF₁, map_add]
  have hG : ∀ c d, G c d = ι (F c d) := fun _ _ => rfl
  obtain ⟨-, h2, -⟩ := CFSG.LocalAnalysis.ComponentInitial.finite_field_linearized_map_bases
    Nat.prime_two hf hk
  obtain ⟨A, hA, hAuniq⟩ := h2 G
  have hcoef : ∀ (t : T) (i j : Fin f),
      A i j * ((χ t : k) ^ 2 ^ (i : ℕ) * (ψ t : k) ^ 2 ^ (j : ℕ)) = A i j := by
    intro t
    have huniq := hAuniq
      (fun i j => A i j * ((χ t : k) ^ 2 ^ (i : ℕ) * (ψ t : k) ^ 2 ^ (j : ℕ))) fun x y => by
      have h1 : G x y = G ((χ t : k) * x) ((ψ t : k) * y) := by
        rw [hG, hG, hFT]
      rw [h1, hA]
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
      rw [mul_pow, mul_pow]
      ring
    intro i j
    exact congrFun (congrFun huniq i) j
  have hA0 : ∀ i j, A i j = 0 := by
    intro i j
    by_contra hne
    obtain ⟨t, ht⟩ := hnd i j i.2 j.2
    refine ht (Units.val_eq_one.1 ?_)
    rw [Units.val_mul, Units.val_pow_eq_pow_val, Units.val_pow_eq_pow_val]
    exact (mul_eq_left₀ hne).1 (hcoef t i j)
  intro c d
  have h0 : G c d = 0 := by
    rw [hA]
    simp [hA0]
  exact hι (by rw [map_zero, ← hG]; exact h0)

variable [Finite K]

theorem exists_orderOf_fixField : ∃ g : (fixField σ)ˣ, orderOf g = Nat.card (fixField σ) - 1 := by
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := (fixField σ)ˣ)
  exact ⟨g, by rw [orderOf_eq_card_of_forall_mem_zpowers hg, Nat.card_units]⟩

omit [Finite K] in
theorem odd_card_torusParam {f : ℕ} (hf : 1 ≤ f) (hk : Nat.card (fixField σ) = 2 ^ f) :
    Odd (Nat.card (Fin TwistTag.E6.foldedTag.rank → (fixField σ)ˣ)) := by
  rw [Nat.card_pi, Finset.prod_const, Finset.card_univ, Fintype.card_fin, Nat.card_units, hk]
  refine Odd.pow ⟨2 ^ (f - 1) - 1, ?_⟩
  have h1 : 1 ≤ 2 ^ (f - 1) := Nat.one_le_two_pow
  have h2 : 2 ^ f = 2 * 2 ^ (f - 1) := by
    rw [← pow_succ']
    congr 1
    omega
  omega

theorem exists_foldChar_ne_one {f : ℕ} (hk : Nat.card (fixField σ) = 2 ^ f)
    {β : Fin TwistTag.E6.tag.rank → ℤ} (h : ∃ a, ¬ (2 ^ f - 1 : ℤ) ∣ foldCoord β a) :
    ∃ t, foldChar σ β t ≠ 1 := by
  obtain ⟨a, ha⟩ := h
  obtain ⟨g, hg⟩ := exists_orderOf_fixField (σ := σ)
  refine ⟨Pi.mulSingle a g, fun h1 => ha ?_⟩
  rw [foldChar_mulSingle, ← orderOf_dvd_iff_zpow_eq_one, hg, hk] at h1
  have e : ((2 ^ f - 1 : ℕ) : ℤ) = 2 ^ f - 1 := by
    rw [Nat.cast_sub Nat.one_le_two_pow, Nat.cast_pow, Nat.cast_ofNat, Nat.cast_one]
  rw [← e]
  exact h1

theorem exists_foldChar_pow_mul_ne_one {f : ℕ} (hk : Nat.card (fixField σ) = 2 ^ f)
    {α β : Fin TwistTag.E6.tag.rank → ℤ}
    (h : ∀ i j : ℕ, i < f → j < f →
      ¬ ∀ a, (2 ^ f - 1 : ℤ) ∣ 2 ^ i * foldCoord α a + 2 ^ j * foldCoord β a)
    (i j : ℕ) (hi : i < f) (hj : j < f) :
    ∃ t, foldChar σ α t ^ 2 ^ i * foldChar σ β t ^ 2 ^ j ≠ 1 := by
  by_contra hall
  have hall' : ∀ t, foldChar σ α t ^ 2 ^ i * foldChar σ β t ^ 2 ^ j = 1 := fun t => by
    by_contra h'
    exact hall ⟨t, h'⟩
  obtain ⟨g, hg⟩ := exists_orderOf_fixField (σ := σ)
  refine h i j hi hj fun a => ?_
  have h1 := hall' (Pi.mulSingle a g)
  rw [foldChar_mulSingle, foldChar_mulSingle, ← zpow_natCast, ← zpow_natCast, ← zpow_mul,
    ← zpow_mul, ← zpow_add, ← orderOf_dvd_iff_zpow_eq_one, hg, hk] at h1
  have e : ((2 ^ f - 1 : ℕ) : ℤ) = 2 ^ f - 1 := by
    rw [Nat.cast_sub Nat.one_le_two_pow, Nat.cast_pow, Nat.cast_ofNat, Nat.cast_one]
  rw [← e]
  convert h1 using 1
  push_cast
  ring

omit [Finite K] in
theorem heightQuot_prod_comp_smul_eq_one
    {τ : Tag} {T : Type*} [Group T] [Fintype T]
    (φ : T →* (Fin τ.rank → Kˣ))
    (hχ : ∀ β : Fin τ.rank → ℤ, IsRoot τ β → 0 < height β → (rootChar K β).comp φ ≠ 1) {h : ℤ}
    (q : HeightQuot τ K h) : ∏ t : T, heightQuotSmul h (φ t) q = 1 := by
  induction q using heightQuot_induction with
  | hgen α hα c =>
    have hsum : ∑ t : T, (rootChar K α (φ t) : K) = 0 := by
      refine sum_hom_units_eq_zero ((Units.coeHom K).comp ((rootChar K α).comp φ)) fun h1 => ?_
      refine hχ α hα.1 hα.2.1 (MonoidHom.ext fun t => Units.ext ?_)
      exact DFunLike.congr_fun h1 t
    simp only [heightQuotSmul_rootElt]
    rw [← map_prod, ← ofAdd_sum, ← Finset.sum_mul, hsum, zero_mul, ofAdd_zero, map_one]
  | hone => simp
  | hmul q q' hq hq' => simp only [map_mul, Finset.prod_mul_distrib, hq, hq', mul_one]
  | hinv q hq => simp only [map_inv, Finset.prod_inv_distrib, hq, inv_one]

omit [Finite K] in
theorem mem_heightSeries_succ_of_forall_comp
    [CharP K 2] {τ : Tag} {T : Type*} [Group T]
    [Finite T] (hT : Odd (Nat.card T)) (φ : T →* (Fin τ.rank → Kˣ))
    (hχ : ∀ β : Fin τ.rank → ℤ, IsRoot τ β → 0 < height β → (rootChar K β).comp φ ≠ 1) {h : ℤ}
    {x : ModGL τ K} (hx : x ∈ heightSeries τ K h)
    (hfix : ∀ t : T,
      (torusVec τ K (φ t) * x * (torusVec τ K (φ t))⁻¹)⁻¹ * x ∈ heightSeries τ K (h + 1)) :
    x ∈ heightSeries τ K (h + 1) := by
  classical
  have := Fintype.ofFinite T
  set q : HeightQuot τ K h := QuotientGroup.mk ⟨x, hx⟩ with hq
  have hsmul : ∀ t, heightQuotSmul h (φ t) q = q := fun t => by
    rw [hq, heightQuotSmul_mk, QuotientGroup.eq, Subgroup.mem_subgroupOf]
    exact hfix t
  have hprod := heightQuot_prod_comp_smul_eq_one φ hχ q
  simp only [hsmul, Finset.prod_const, Finset.card_univ] at hprod
  obtain ⟨k, hk⟩ := hT
  rw [← Nat.card_eq_fintype_card, hk, pow_succ, pow_mul, heightQuot_sq_eq_one, one_pow,
    one_mul] at hprod
  rw [hq, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf] at hprod
  exact hprod

end CFSG.LieType.Chevalley.TwistedE6Cover
