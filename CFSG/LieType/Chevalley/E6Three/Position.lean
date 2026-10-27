module

public import CFSG.LieType.Chevalley.E6Three.ModelPairs
public import CFSG.LieType.Chevalley.MaxTorusPart
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.E6ThreeBlock
public import CFSG.LocalAnalysis.StandardType.GGSixBstarExcFramesTorus
public import CFSG.LocalAnalysis.StandardType.GGSixBstarExcFramesHalfMaxToral

public section

set_option autoImplicit false

namespace CFSG.LieType.Chevalley.E6Three.Position

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.StandardType.TableBExc
  CFSG.StandardType.TableBExc.Three CFSG.StandardType.TableBExc.E6Three
  CFSG.HardMathSupport.Timmesfeld.Steinberg CFSG.HardMathSupport.Timmesfeld.Torality
  CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.StandardType.TwE6HyperplaneTypes
  CFSG.LieType.Chevalley.MaxTorusPart CFSG.LieType.Chevalley.E6Three.ModelKernel
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

section Model

theorem exists_coord_of_mem_range {w : WeylGroup .E6} (hw : w ∈ modelHomE6.range) :
    ∃ q : Coord, mW q = w := by
  obtain ⟨y, rfl⟩ := hw
  exact ⟨(Multiplicative.toAdd y.left, Multiplicative.toAdd y.right), rfl⟩

theorem mW_injective : Function.Injective mW := by
  intro q r h
  have h' := modelHomE6_injective h
  exact Prod.ext (Multiplicative.ofAdd.injective (congrArg SemidirectProduct.left h'))
    (Multiplicative.ofAdd.injective (congrArg SemidirectProduct.right h'))

theorem isPlanes_or_reflections {q : Coord} (h3 : mW q ^ 3 = 1) :
    isPlanes q = true ∨ ∃ R : List (List (Fin Tag.E6.rank) × Fin Tag.E6.rank),
      mW q = (R.map fun p => (coxeterSystem .E6).wordProd p.1 * simple .E6 p.2 *
        ((coxeterSystem .E6).wordProd p.1)⁻¹).prod ∧
      ∀ e : Fin Tag.E6.rank → ZMod 3, (∀ u, triPairing e (mW q • u) = triPairing e u) →
        ∀ p ∈ R, triPairing e ((coxeterSystem .E6).wordProd p.1 • Pi.single p.2 1) = 0 := by
  have hcheck := modelCert_check q.1 q.2
  rw [mW_eq] at h3 ⊢
  unfold isPlanes
  generalize modelCert q.1 q.2 = M at hcheck ⊢
  cases M with
  | refl R =>
    right
    refine ⟨R.map fun r => (r.u, r.i), ?_, fun e he p hp => ?_⟩
    · rw [wordProd_eq_of_check_refl hcheck, List.map_map]
      rfl
    · obtain ⟨r, hr, rfl⟩ := List.mem_map.1 hp
      exact triPairing_eq_zero_of_check_refl hcheck he hr
  | nine i => exact absurd h3 (pow_three_ne_one_of_check_nine hcheck)
  | planes cols f P s jk cs => exact Or.inl rfl

theorem wordProd_eq_prod_simple (ω : List (Fin Tag.E6.rank)) :
    (coxeterSystem .E6).wordProd ω = ((ω.map fun i => (([] : List (Fin Tag.E6.rank)), i)).map
      fun p => (coxeterSystem .E6).wordProd p.1 * simple .E6 p.2 *
        ((coxeterSystem .E6).wordProd p.1)⁻¹).prod := by
  induction ω with
  | nil => simp
  | cons i ω ih =>
    rw [CoxeterSystem.wordProd_cons, ih, List.map_cons, List.map_cons, List.prod_cons,
      CoxeterSystem.wordProd_nil, one_mul, inv_one, mul_one]

set_option maxRecDepth 4000 in
theorem exists_solve_two : ∀ s₁ t₁ s₂ t₂ : ZMod 3,
    (∀ a b : ZMod 3, a * s₁ + b * s₂ = 0 → a * t₁ + b * t₂ = 0 → a = 0 ∧ b = 0) →
      ∀ s t : ZMod 3, ∃ a b : ZMod 3, a * s₁ + b * s₂ = s ∧ a * t₁ + b * t₂ = t := by
  decide +kernel

end Model

section Characters

variable {τ : Tag} {L : Type} [Field L]

theorem rootDiagUnit_zetaVec_zero (ζ : Lˣ) (hζ : ζ ^ 3 = 1) :
    rootDiagUnit τ (zetaVec ζ hζ 0) = 1 := by
  have h : zetaVec (τ := τ) ζ hζ 0 = 1 := by
    funext i
    simp [zetaVec]
  rw [h, rootDiagUnit_one]

theorem rootDiagUnit_zetaVec_add (ζ : Lˣ) (hζ : ζ ^ 3 = 1) (x y : Fin τ.rank → ZMod 3) :
    rootDiagUnit τ (zetaVec ζ hζ (x + y)) =
      rootDiagUnit τ (zetaVec ζ hζ x) * rootDiagUnit τ (zetaVec ζ hζ y) := by
  rw [CFSG.StandardType.ExcFrames.zetaVec_add, rootDiagUnit_mul]

theorem rootDiagUnit_zetaVec_nsmul (ζ : Lˣ) (hζ : ζ ^ 3 = 1) (x : Fin τ.rank → ZMod 3) (n : ℕ) :
    rootDiagUnit τ (zetaVec ζ hζ (n • x)) = rootDiagUnit τ (zetaVec ζ hζ x) ^ n := by
  induction n with
  | zero => rw [zero_nsmul, pow_zero, rootDiagUnit_zetaVec_zero]
  | succ n ih => rw [succ_nsmul, rootDiagUnit_zetaVec_add, ih, pow_succ]

theorem rootDiagUnit_zetaVec_smul (ζ : Lˣ) (hζ : ζ ^ 3 = 1) (x : Fin τ.rank → ZMod 3)
    (a : ZMod 3) :
    rootDiagUnit τ (zetaVec ζ hζ (a • x)) = rootDiagUnit τ (zetaVec ζ hζ x) ^ a.val := by
  rw [← rootDiagUnit_zetaVec_nsmul, ← Nat.cast_smul_eq_nsmul (ZMod 3), ZMod.natCast_zmod_val]


theorem rootDiagUnit_zetaVec_injective {ζ : Lˣ} (hζo : orderOf ζ = 3) (hζ : ζ ^ 3 = 1) :
    Function.Injective fun x : Fin τ.rank → ZMod 3 => rootDiagUnit τ (zetaVec ζ hζ x) :=
  fun _ _ h => zetaVec_injective hζo hζ (CFSG.LieType.Chevalley.rootDiagUnit_injective h)

theorem canonicalRep_conj_zetaVec (ζ : Lˣ) (hζ : ζ ^ 3 = 1) (ω : List (Fin τ.rank))
    (z : Fin τ.rank → ZMod 3) :
    canonicalRep (coxeterSystem τ) L ((coxeterSystem τ).wordProd ω) *
        rootDiagUnit τ (zetaVec ζ hζ z) *
        (canonicalRep (coxeterSystem τ) L ((coxeterSystem τ).wordProd ω))⁻¹ =
      rootDiagUnit τ (zetaVec ζ hζ (triAct ω z)) := by
  rw [canonicalRep_conj_rootDiagUnit, weylTuple_zetaVec_triAct]

theorem card_inf_torus_mul_card_range {F : Subgroup (ModGL τ L)}
    (hFN : F ≤ monomialSubgroup τ L) :
    Nat.card ↥(F ⊓ torusGroup τ L) *
      Nat.card ((weylQuotientHom τ L).comp (Subgroup.inclusion hFN)).range = Nat.card F := by
  rw [← Subgroup.card_ker_mul_card_range ((weylQuotientHom τ L).comp (Subgroup.inclusion hFN))]
  congr 1
  exact Nat.card_congr
    { toFun := fun u => ⟨⟨u, (Subgroup.mem_inf.1 u.2).1⟩, MonoidHom.mem_ker.2
        (weylQuotientHom_eq (mapsRootLines_of_mem_torusGroup (Subgroup.mem_inf.1 u.2).2))⟩
      invFun := fun x => ⟨x.1, x.1.2,
        mem_torusGroup_of_weylQuotientHom_eq_one (hFN x.1.2) (MonoidHom.mem_ker.1 x.2)⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }

end Characters

section Procedure

variable
  {L : Type} [Field L] [CharP L 2]

theorem not_reflections_of_max [IsAlgClosed L] {ζ : Lˣ} (hζ : IsPrimitiveRoot ζ 3)
    {F : Subgroup (ModGL .E6 L)} [Finite F] (hexp : ∀ x ∈ F, x ^ 3 = 1)
    (hmax : ∀ g ∈ adjointGroup .E6 L, ¬ Nat.card ↥(F ⊓ torusGroup .E6 L) <
      Nat.card ↥(F.map (MulAut.conj g).toMonoidHom ⊓ torusGroup .E6 L))
    {ι : Type} (e : ι → Fin Tag.E6.rank → ZMod 3)
    (he : ∀ u ∈ F ⊓ torusGroup .E6 L, ∃ i, rootDiagUnit .E6 (zetaVec ζ hζ.pow_eq_one (e i)) = u)
    {n : ModGL .E6 L} (hnF : n ∈ F) (hnT : n ∉ torusGroup .E6 L)
    (hnN : n ∈ monomialSubgroup .E6 L) (R : List (List (Fin Tag.E6.rank) × Fin Tag.E6.rank))
    (hR : weylQuotientHom .E6 L ⟨n, hnN⟩ = (R.map fun p => (coxeterSystem .E6).wordProd p.1 *
      simple .E6 p.2 * ((coxeterSystem .E6).wordProd p.1)⁻¹).prod)
    (hR0 : ∀ p ∈ R, ∀ i,
      triPairing (e i) ((coxeterSystem .E6).wordProd p.1 • Pi.single p.2 1) = 0) :
    False := by
  have hζo : orderOf ζ = 3 := hζ.eq_orderOf.symm
  have hL3 : ringChar L ≠ 3 := by rw [ringChar.eq L 2]; norm_num
  have hwK : weylQuotientHom .E6 L ⟨n, hnN⟩ ∈
      kernelWeylGroup (familyChar fun i => zetaVec ζ hζ.pow_eq_one (e i)) := by
    rw [hR]
    exact prod_mem_kernelWeylGroup hζo hζ.pow_eq_one e R hR0
  obtain ⟨g, hg, hlt⟩ := exists_conj_card_torus_lt_of_mem_kernelWeylGroup
    monomialToralAt_E6_three hL3 (fun i => zetaVec ζ hζ.pow_eq_one (e i)) he hnF hnT hnN
    (hexp n hnF) hwK
  exact hmax g hg hlt

theorem card_inf_torus_ne_one [IsAlgClosed L] {ζ : Lˣ} (hζ : IsPrimitiveRoot ζ 3)
    {F : Subgroup (ModGL .E6 L)} [Finite F] (hexp : ∀ x ∈ F, x ^ 3 = 1)
    (hFN : ∀ x ∈ F, x ∈ monomialSubgroup .E6 L)
    (hFS : ∀ x ∈ F, ∀ hx : x ∈ monomialSubgroup .E6 L,
      weylQuotientHom .E6 L ⟨x, hx⟩ ∈ modelHomE6.range)
    (hFT : ¬ F ≤ torusGroup .E6 L)
    (hmax : ∀ g ∈ adjointGroup .E6 L, ¬ Nat.card ↥(F ⊓ torusGroup .E6 L) <
      Nat.card ↥(F.map (MulAut.conj g).toMonoidHom ⊓ torusGroup .E6 L)) :
    Nat.card ↥(F ⊓ torusGroup .E6 L) ≠ 1 := by
  intro h1
  obtain ⟨n, hnF, hnT⟩ : ∃ n ∈ F, n ∉ torusGroup .E6 L := by
    by_contra h
    exact hFT fun x hx => by_contra fun hxT => h ⟨x, hx, hxT⟩
  obtain ⟨q, hq⟩ := exists_coord_of_mem_range (hFS n hnF (hFN n hnF))
  have hbot := Subgroup.eq_bot_of_card_eq _ h1
  refine not_reflections_of_max hζ hexp hmax (fun _ : Unit => 0) (fun u hu => ⟨(), ?_⟩) hnF hnT
    (hFN n hnF) ((modelWordE6 q.1 q.2).map fun i => ([], i)) ?_ fun _ _ _ => ?_
  · rw [hbot, Subgroup.mem_bot] at hu
    rw [hu]
    exact rootDiagUnit_zetaVec_zero ζ _
  · rw [← hq, mW_eq]
    exact wordProd_eq_prod_simple _
  · simp [triPairing]

theorem card_inf_torus_ne_three [IsAlgClosed L] {ζ : Lˣ} (hζ : IsPrimitiveRoot ζ 3)
    {F : Subgroup (ModGL .E6 L)} [Finite F] (hcomm : ∀ x ∈ F, ∀ y ∈ F, x * y = y * x)
    (hexp : ∀ x ∈ F, x ^ 3 = 1) (hcard : Nat.card F = 3 ^ 3)
    (hFN : ∀ x ∈ F, x ∈ monomialSubgroup .E6 L)
    (hFS : ∀ x ∈ F, ∀ hx : x ∈ monomialSubgroup .E6 L,
      weylQuotientHom .E6 L ⟨x, hx⟩ ∈ modelHomE6.range)
    (hmax : ∀ g ∈ adjointGroup .E6 L, ¬ Nat.card ↥(F ⊓ torusGroup .E6 L) <
      Nat.card ↥(F.map (MulAut.conj g).toMonoidHom ⊓ torusGroup .E6 L)) :
    Nat.card ↥(F ⊓ torusGroup .E6 L) ≠ 3 := by
  intro hU
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have h3 : ζ ^ 3 = 1 := hζ.pow_eq_one
  have hζo : orderOf ζ = 3 := hζ.eq_orderOf.symm
  have : Finite ↥(F ⊓ torusGroup .E6 L) := Finite.of_injective _ (Subgroup.inclusion_injective
    (inf_le_left : F ⊓ torusGroup .E6 L ≤ F))
  obtain ⟨u₁, hu₁U, hu₁⟩ : ∃ u ∈ F ⊓ torusGroup .E6 L, u ≠ 1 := by
    by_contra h
    push Not at h
    rw [(Subgroup.eq_bot_iff_forall _).2 h, Subgroup.card_bot] at hU
    norm_num at hU
  obtain ⟨x₀, rfl⟩ := exists_zetaVec_of_mem_torusGroup hζo h3 (Subgroup.mem_inf.1 hu₁U).2
    (hexp _ (Subgroup.mem_inf.1 hu₁U).1)
  have hx₀ : x₀ ≠ 0 := fun h => hu₁ (by rw [h]; exact rootDiagUnit_zetaVec_zero ζ h3)
  have hx₀F := (Subgroup.mem_inf.1 hu₁U).1
  have hline : ∀ u ∈ F ⊓ torusGroup .E6 L,
      ∃ a : ZMod 3, rootDiagUnit .E6 (zetaVec ζ h3 (a • x₀)) = u := by
    have hinj : Function.Injective fun a : ZMod 3 => rootDiagUnit .E6 (zetaVec ζ h3 (a • x₀)) := by
      intro a a' h
      have h1 : a • x₀ = a' • x₀ := rootDiagUnit_zetaVec_injective hζo h3 h
      rw [← sub_eq_zero, ← sub_smul, smul_eq_zero] at h1
      exact sub_eq_zero.1 (h1.resolve_right hx₀)
    have hsub : Set.range (fun a : ZMod 3 => rootDiagUnit .E6 (zetaVec ζ h3 (a • x₀))) ⊆
        ((F ⊓ torusGroup .E6 L : Subgroup (ModGL .E6 L)) : Set (ModGL .E6 L)) := by
      rintro _ ⟨a, rfl⟩
      change rootDiagUnit .E6 (zetaVec ζ h3 (a • x₀)) ∈ F ⊓ torusGroup .E6 L
      rw [rootDiagUnit_zetaVec_smul]
      exact pow_mem hu₁U _
    have heq := Set.eq_of_subset_of_ncard_le hsub (by
      rw [Set.ncard_range_of_injective hinj, Nat.card_zmod, ← Nat.card_coe_set_eq]
      exact hU.le) (Set.finite_coe_iff.1 (inferInstanceAs (Finite ↥(F ⊓ torusGroup .E6 L))))
    intro u hu
    have hu' : u ∈ ((F ⊓ torusGroup .E6 L : Subgroup (ModGL .E6 L)) : Set (ModGL .E6 L)) := hu
    rw [← heq] at hu'
    exact hu'
  have hFN' : F ≤ monomialSubgroup .E6 L := fun x hx => hFN x hx
  set ψ := (weylQuotientHom .E6 L).comp (Subgroup.inclusion hFN') with hψ
  have hψcard : Nat.card ψ.range = 9 := by
    have h := card_inf_torus_mul_card_range hFN'
    rw [hU, hcard] at h
    have h' : 3 * Nat.card ψ.range = 3 * 9 := h.trans (by norm_num)
    exact Nat.eq_of_mul_eq_mul_left (by norm_num) h'
  obtain ⟨n₁, hn₁F, hn₁T⟩ : ∃ n ∈ F, n ∉ torusGroup .E6 L := by
    by_contra h
    push Not at h
    have := Subgroup.card_le_of_le (show F ≤ F ⊓ torusGroup .E6 L from fun x hx => ⟨hx, h x hx⟩)
    rw [hU, hcard] at this
    norm_num at this
  have hpow : ∀ m (hm : m ∈ F), ψ ⟨m, hm⟩ ^ 3 = 1 := by
    intro m hm
    rw [← map_pow]
    have : (⟨m, hm⟩ : F) ^ 3 = 1 := Subtype.ext (hexp m hm)
    rw [this, map_one]
  obtain ⟨w₂, hw₂R, hw₂Z⟩ : ∃ w ∈ ψ.range, w ∉ Subgroup.zpowers (ψ ⟨n₁, hn₁F⟩) := by
    by_contra h
    push Not at h
    have h1 := Subgroup.card_le_of_le (show ψ.range ≤ Subgroup.zpowers (ψ ⟨n₁, hn₁F⟩) from
      fun w hw => h w hw)
    rw [hψcard, Nat.card_zpowers] at h1
    have h2 := orderOf_le_of_pow_eq_one (by norm_num) (hpow n₁ hn₁F)
    omega
  obtain ⟨⟨n₂, hn₂F⟩, rfl⟩ := MonoidHom.mem_range.1 hw₂R
  obtain ⟨q₁, hq₁⟩ := exists_coord_of_mem_range (hFS n₁ hn₁F (hFN n₁ hn₁F))
  obtain ⟨q₂, hq₂⟩ := exists_coord_of_mem_range (hFS n₂ hn₂F (hFN n₂ hn₂F))
  change mW q₁ = ψ ⟨n₁, hn₁F⟩ at hq₁
  change mW q₂ = ψ ⟨n₂, hn₂F⟩ at hq₂
  have hfix : ∀ m (hm : m ∈ F), ∀ v, triPairing x₀ (ψ ⟨m, hm⟩ • v) = triPairing x₀ v :=
    fun m hm v => triPairing_weylQuotientHom_smul hζo h3 (hFN m hm) (hcomm _ hx₀F m hm) v
  have hplanes : ∀ m (hm : m ∈ F), m ∉ torusGroup .E6 L → ∀ q : Coord, mW q = ψ ⟨m, hm⟩ →
      isPlanes q = true := by
    intro m hm hmT q hq
    rcases isPlanes_or_reflections (q := q) (by rw [hq]; exact hpow m hm) with h | ⟨R, hR, hR0⟩
    · exact h
    · refine (not_reflections_of_max hζ hexp hmax (fun a : ZMod 3 => a • x₀) hline hm hmT
        (hFN m hm) R (by change ψ ⟨m, hm⟩ = _; rw [← hq]; exact hR) fun p hp a => ?_).elim
      rw [triPairing_smul_left, hR0 x₀ (fun v => by rw [hq]; exact hfix m hm v) p hp, mul_zero]
  have hn₂T : n₂ ∉ torusGroup .E6 L := fun h => hw₂Z (by
    have : ψ ⟨n₂, hn₂F⟩ = 1 := weylQuotientHom_eq (mapsRootLines_of_mem_torusGroup h)
    rw [this]
    exact one_mem _)
  have hc : qmul q₁ q₂ = qmul q₂ q₁ := mW_injective (by
    rw [mW_qmul, mW_qmul, hq₁, hq₂, ← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (hcomm n₁ hn₁F n₂ hn₂F))
  have hne₁ : q₂ ≠ qone := fun h => hw₂Z (by rw [← hq₂, h, mW_qone]; exact one_mem _)
  have hne₂ : q₂ ≠ q₁ := fun h => hw₂Z (by rw [← hq₂, h, hq₁]; exact Subgroup.mem_zpowers _)
  have hne₃ : q₂ ≠ qmul q₁ q₁ := fun h => hw₂Z (by
    rw [← hq₂, h, mW_qmul, hq₁]
    exact mul_mem (Subgroup.mem_zpowers _) (Subgroup.mem_zpowers _))
  obtain ⟨a, b, hab, R, hR, hR0⟩ := exists_reflections_of_order_nine
    (hplanes n₁ hn₁F hn₁T q₁ hq₁) (hplanes n₂ hn₂F hn₂T q₂ hq₂) hc hne₁ hne₂ hne₃ hx₀
    (fun v => by rw [hq₁]; exact hfix n₁ hn₁F v) (fun v => by rw [hq₂]; exact hfix n₂ hn₂F v)
  have hnF : n₁ ^ a * n₂ ^ b ∈ F := mul_mem (pow_mem hn₁F a) (pow_mem hn₂F b)
  have hψn : ψ ⟨n₁ ^ a * n₂ ^ b, hnF⟩ = mW (qp q₁ q₂ a b) := by
    rw [mW_qp, hq₁, hq₂, ← map_pow, ← map_pow, ← map_mul]
    rfl
  have hnT : n₁ ^ a * n₂ ^ b ∉ torusGroup .E6 L := fun h => hab (mW_injective (by
    rw [← hψn, mW_qone]
    exact weylQuotientHom_eq (mapsRootLines_of_mem_torusGroup h)))
  exact not_reflections_of_max hζ hexp hmax (fun a : ZMod 3 => a • x₀) hline hnF hnT
    (hFN _ hnF) R (by change ψ ⟨_, hnF⟩ = _; rw [hψn]; exact hR)
    fun p hp a' => by rw [triPairing_smul_left, hR0 p hp, mul_zero]

theorem exists_position_of_card_inf_torus_nine [IsAlgClosed L] {ζ : Lˣ}
    (hζ : IsPrimitiveRoot ζ 3) {F : Subgroup (ModGL .E6 L)} [Finite F]
    (hcomm : ∀ x ∈ F, ∀ y ∈ F, x * y = y * x) (hexp : ∀ x ∈ F, x ^ 3 = 1)
    (hcard : Nat.card F = 3 ^ 3) (hFN : ∀ x ∈ F, x ∈ monomialSubgroup .E6 L)
    (hFS : ∀ x ∈ F, ∀ hx : x ∈ monomialSubgroup .E6 L,
      weylQuotientHom .E6 L ⟨x, hx⟩ ∈ modelHomE6.range)
    (hmax : ∀ g ∈ adjointGroup .E6 L, ¬ Nat.card ↥(F ⊓ torusGroup .E6 L) <
      Nat.card ↥(F.map (MulAut.conj g).toMonoidHom ⊓ torusGroup .E6 L))
    (hU : Nat.card ↥(F ⊓ torusGroup .E6 L) = 3 ^ 2) :
    ∃ (ω : List (Fin Tag.E6.rank)) (k : Fin 5),
      (∀ u, u ∈ F.map (MulAut.conj (canonicalRep (coxeterSystem .E6) L
          ((coxeterSystem .E6).wordProd ω))).toMonoidHom ⊓ torusGroup .E6 L ↔
        ∃ z, PositionMem k z ∧ u = rootDiagUnit .E6 (zetaVec ζ hζ.pow_eq_one z)) ∧
      ∃ n ∈ F, ∃ hn : n ∈ monomialSubgroup .E6 L,
        (coxeterSystem .E6).wordProd ω * weylQuotientHom .E6 L ⟨n, hn⟩ *
          ((coxeterSystem .E6).wordProd ω)⁻¹ = (coxeterSystem .E6).wordProd (positionWord k) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have h3 : ζ ^ 3 = 1 := hζ.pow_eq_one
  have hζo : orderOf ζ = 3 := hζ.eq_orderOf.symm
  have : Finite ↥(F ⊓ torusGroup .E6 L) := Finite.of_injective _ (Subgroup.inclusion_injective
    (inf_le_left : F ⊓ torusGroup .E6 L ≤ F))
  obtain ⟨u₁, hu₁U, hu₁⟩ : ∃ u ∈ F ⊓ torusGroup .E6 L, u ≠ 1 := by
    by_contra h
    push Not at h
    rw [(Subgroup.eq_bot_iff_forall _).2 h, Subgroup.card_bot] at hU
    norm_num at hU
  obtain ⟨x₀, rfl⟩ := exists_zetaVec_of_mem_torusGroup hζo h3 (Subgroup.mem_inf.1 hu₁U).2
    (hexp _ (Subgroup.mem_inf.1 hu₁U).1)
  obtain ⟨u₂, hu₂U, hu₂⟩ : ∃ u ∈ F ⊓ torusGroup .E6 L,
      u ∉ Subgroup.zpowers (rootDiagUnit .E6 (zetaVec ζ h3 x₀)) := by
    by_contra h
    push Not at h
    have heq : F ⊓ torusGroup .E6 L = Subgroup.zpowers (rootDiagUnit .E6 (zetaVec ζ h3 x₀)) :=
      le_antisymm (fun u hu => h u hu) (Subgroup.zpowers_le.2 hu₁U)
    rw [heq, Nat.card_zpowers] at hU
    have h2 := orderOf_le_of_pow_eq_one (by norm_num : 0 < 3) (hexp _ (Subgroup.mem_inf.1 hu₁U).1)
    omega
  obtain ⟨y₀, rfl⟩ := exists_zetaVec_of_mem_torusGroup hζo h3 (Subgroup.mem_inf.1 hu₂U).2
    (hexp _ (Subgroup.mem_inf.1 hu₂U).1)
  have hx₀F := (Subgroup.mem_inf.1 hu₁U).1
  have hy₀F := (Subgroup.mem_inf.1 hu₂U).1
  have hind : ∀ a b : ZMod 3, a • x₀ + b • y₀ = 0 → a = 0 ∧ b = 0 := by
    intro a b hab
    by_cases hb : b = 0
    · subst hb
      rw [zero_smul, add_zero, smul_eq_zero] at hab
      refine ⟨hab.resolve_right fun h => hu₁ ?_, rfl⟩
      rw [h]
      exact rootDiagUnit_zetaVec_zero ζ h3
    · exfalso
      apply hu₂
      have hy : y₀ = (-(b⁻¹ * a)) • x₀ := by
        have e : b • y₀ = -(a • x₀) := eq_neg_of_add_eq_zero_right hab
        calc y₀ = b⁻¹ • (b • y₀) := by rw [smul_smul, inv_mul_cancel₀ hb, one_smul]
          _ = (-(b⁻¹ * a)) • x₀ := by rw [e, smul_neg, smul_smul, neg_smul]
      rw [hy, rootDiagUnit_zetaVec_smul]
      exact Subgroup.pow_mem _ (Subgroup.mem_zpowers _) _
  have hmem : ∀ a b : ZMod 3,
      rootDiagUnit .E6 (zetaVec ζ h3 (a • x₀ + b • y₀)) ∈ F ⊓ torusGroup .E6 L := by
    intro a b
    rw [rootDiagUnit_zetaVec_add, rootDiagUnit_zetaVec_smul, rootDiagUnit_zetaVec_smul]
    exact mul_mem (pow_mem hu₁U _) (pow_mem hu₂U _)
  have hplane : ∀ u ∈ F ⊓ torusGroup .E6 L, ∃ p : ZMod 3 × ZMod 3,
      rootDiagUnit .E6 (zetaVec ζ h3 (p.1 • x₀ + p.2 • y₀)) = u := by
    have hinj : Function.Injective fun p : ZMod 3 × ZMod 3 =>
        rootDiagUnit .E6 (zetaVec ζ h3 (p.1 • x₀ + p.2 • y₀)) := by
      intro p p' h
      have h1 : p.1 • x₀ + p.2 • y₀ = p'.1 • x₀ + p'.2 • y₀ :=
        rootDiagUnit_zetaVec_injective hζo h3 h
      have h2 : (p.1 - p'.1) • x₀ + (p.2 - p'.2) • y₀ = 0 := by
        rw [sub_smul, sub_smul, sub_add_sub_comm, h1, sub_self]
      obtain ⟨e1, e2⟩ := hind _ _ h2
      exact Prod.ext (sub_eq_zero.1 e1) (sub_eq_zero.1 e2)
    have hsub : Set.range (fun p : ZMod 3 × ZMod 3 =>
        rootDiagUnit .E6 (zetaVec ζ h3 (p.1 • x₀ + p.2 • y₀))) ⊆
          ((F ⊓ torusGroup .E6 L : Subgroup (ModGL .E6 L)) : Set (ModGL .E6 L)) := by
      rintro _ ⟨p, rfl⟩
      exact hmem p.1 p.2
    have heq := Set.eq_of_subset_of_ncard_le hsub (by
      rw [Set.ncard_range_of_injective hinj, Nat.card_prod, Nat.card_zmod, ← Nat.card_coe_set_eq]
      exact (hU.trans (by norm_num)).le)
      (Set.finite_coe_iff.1 (inferInstanceAs (Finite ↥(F ⊓ torusGroup .E6 L))))
    intro u hu
    have hu' : u ∈ ((F ⊓ torusGroup .E6 L : Subgroup (ModGL .E6 L)) : Set (ModGL .E6 L)) := hu
    rw [← heq] at hu'
    exact hu'
  obtain ⟨n, hnF, hnT⟩ : ∃ n ∈ F, n ∉ torusGroup .E6 L := by
    by_contra h
    push Not at h
    have := Subgroup.card_le_of_le (show F ≤ F ⊓ torusGroup .E6 L from fun x hx => ⟨hx, h x hx⟩)
    rw [hU, hcard] at this
    norm_num at this
  have hnN := hFN n hnF
  obtain ⟨q, hq⟩ := exists_coord_of_mem_range (hFS n hnF hnN)
  have hw3 : (coxeterSystem .E6).wordProd (modelWordE6 q.1 q.2) ^ 3 = 1 := by
    rw [← mW_eq q, hq]
    exact weylQuotientHom_pow_eq_one hnN (hexp n hnF)
  have hx : ∀ v, triPairing x₀ ((coxeterSystem .E6).wordProd (modelWordE6 q.1 q.2) • v) =
      triPairing x₀ v := fun v => by
    rw [← mW_eq q, hq]
    exact triPairing_weylQuotientHom_smul hζo h3 hnN (hcomm _ hx₀F n hnF) v
  have hy : ∀ v, triPairing y₀ ((coxeterSystem .E6).wordProd (modelWordE6 q.1 q.2) • v) =
      triPairing y₀ v := fun v => by
    rw [← mW_eq q, hq]
    exact triPairing_weylQuotientHom_smul hζo h3 hnN (hcomm _ hy₀F n hnF) v
  rcases exists_reflections_or_position hw3 hx hy hind with ⟨R, hR, hR0⟩ | ⟨k, ω, hω, hxk, hyk⟩
  · refine (not_reflections_of_max hζ hexp hmax (fun p : ZMod 3 × ZMod 3 => p.1 • x₀ + p.2 • y₀)
      hplane hnF hnT hnN R (by rw [← hq, mW_eq]; exact hR) fun r hr p => ?_).elim
    change triPairing (p.1 • x₀ + p.2 • y₀) _ = 0
    rw [triPairing_add_left, triPairing_smul_left, triPairing_smul_left, (hR0 r hr).1,
      (hR0 r hr).2, mul_zero, mul_zero, add_zero]
  refine ⟨ω, k, ?_, n, hnF, hnN, by rw [← hq, mW_eq]; exact hω⟩
  set nω := canonicalRep (coxeterSystem .E6) L ((coxeterSystem .E6).wordProd ω) with hnω
  have hnωN : nω ∈ monomialSubgroup .E6 L := canonicalRep_mem_monomialSubgroup L _
  have hconj : ∀ z, nω * rootDiagUnit .E6 (zetaVec ζ h3 z) * nω⁻¹ =
      rootDiagUnit .E6 (zetaVec ζ h3 (triAct ω z)) := canonicalRep_conj_zetaVec ζ h3 ω
  have hωinj : ∀ z, triAct ω z = 0 → z = 0 := by
    intro z hz
    have h := hconj z
    rw [hz, rootDiagUnit_zetaVec_zero] at h
    have h' : rootDiagUnit .E6 (zetaVec ζ h3 z) = 1 := by
      have e : rootDiagUnit .E6 (zetaVec ζ h3 z) =
          nω⁻¹ * (nω * rootDiagUnit .E6 (zetaVec ζ h3 z) * nω⁻¹) * nω := by group
      rw [e, h]
      group
    exact rootDiagUnit_zetaVec_injective hζo h3 (h'.trans (rootDiagUnit_zetaVec_zero ζ h3).symm)
  obtain ⟨s₁, t₁, hs₁⟩ := hxk
  obtain ⟨s₂, t₂, hs₂⟩ := hyk
  have hcomb : ∀ a b : ZMod 3, triAct ω (a • x₀ + b • y₀) =
      (a * s₁ + b * s₂) • positionBasis k 0 + (a * t₁ + b * t₂) • positionBasis k 1 := by
    intro a b
    rw [triAct_add, triAct_smul, triAct_smul, hs₁, hs₂]
    funext i
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring
  have hnd : ∀ a b : ZMod 3, a * s₁ + b * s₂ = 0 → a * t₁ + b * t₂ = 0 → a = 0 ∧ b = 0 := by
    intro a b h1 h2
    refine hind a b (hωinj _ ?_)
    rw [hcomb, h1, h2, zero_smul, zero_smul, add_zero]
  intro u
  constructor
  · rintro ⟨⟨m, hm, rfl⟩, hmT⟩
    have hmT' : m ∈ torusGroup .E6 L := by
      have h := (Subgroup.mem_normalizer_iff.1
        (mem_normalizer_torusGroup_of_mem_monomialSubgroup (inv_mem hnωN)) _).1 hmT
      change nω⁻¹ * (nω * m * nω⁻¹) * nω⁻¹⁻¹ ∈ torusGroup .E6 L at h
      rwa [show nω⁻¹ * (nω * m * nω⁻¹) * nω⁻¹⁻¹ = m by group] at h
    obtain ⟨⟨a, b⟩, rfl⟩ := hplane m ⟨hm, hmT'⟩
    exact ⟨triAct ω (a • x₀ + b • y₀), ⟨_, _, hcomb a b⟩, hconj _⟩
  · rintro ⟨z, ⟨s, t, rfl⟩, rfl⟩
    obtain ⟨a, b, ha, hb⟩ := exists_solve_two s₁ t₁ s₂ t₂ hnd s t
    refine ⟨⟨rootDiagUnit .E6 (zetaVec ζ h3 (a • x₀ + b • y₀)), (Subgroup.mem_inf.1 (hmem a b)).1,
      ?_⟩, rootDiagUnit_mem_torusGroup _⟩
    change nω * _ * nω⁻¹ = _
    rw [hconj, hcomb, ha, hb]

theorem exists_position_of_max [IsAlgClosed L] {ζ : Lˣ} (hζ : IsPrimitiveRoot ζ 3)
    {F : Subgroup (ModGL .E6 L)} [Finite F] (hcomm : ∀ x ∈ F, ∀ y ∈ F, x * y = y * x)
    (hexp : ∀ x ∈ F, x ^ 3 = 1) (hcard : Nat.card F = 3 ^ 3)
    (hFN : ∀ x ∈ F, x ∈ monomialSubgroup .E6 L)
    (hFS : ∀ x ∈ F, ∀ hx : x ∈ monomialSubgroup .E6 L,
      weylQuotientHom .E6 L ⟨x, hx⟩ ∈ modelHomE6.range)
    (hFT : ¬ F ≤ torusGroup .E6 L)
    (hmax : ∀ g ∈ adjointGroup .E6 L, ¬ Nat.card ↥(F ⊓ torusGroup .E6 L) <
      Nat.card ↥(F.map (MulAut.conj g).toMonoidHom ⊓ torusGroup .E6 L)) :
    ∃ g ∈ adjointGroup .E6 L, ∃ k : Fin 5,
      (∀ x ∈ F.map (MulAut.conj g).toMonoidHom, x ∈ monomialSubgroup .E6 L) ∧
      (∀ u, u ∈ F.map (MulAut.conj g).toMonoidHom ⊓ torusGroup .E6 L ↔
        ∃ z, PositionMem k z ∧ u = rootDiagUnit .E6 (zetaVec ζ hζ.pow_eq_one z)) ∧
      ∃ n ∈ F.map (MulAut.conj g).toMonoidHom, ∃ hn : n ∈ monomialSubgroup .E6 L,
        weylQuotientHom .E6 L ⟨n, hn⟩ = (coxeterSystem .E6).wordProd (positionWord k) := by
  have hdvd : Nat.card ↥(F ⊓ torusGroup .E6 L) ∣ 3 ^ 3 :=
    hcard ▸ Subgroup.card_dvd_of_le inf_le_left
  obtain ⟨m, hm, hUm⟩ := (Nat.dvd_prime_pow Nat.prime_three).1 hdvd
  interval_cases m
  · exact (card_inf_torus_ne_one hζ hexp hFN hFS hFT hmax (by simpa using hUm)).elim
  · exact (card_inf_torus_ne_three hζ hcomm hexp hcard hFN hFS hmax (by simpa using hUm)).elim
  · obtain ⟨ω, k, hpos, n, hnF, hnN, hω⟩ :=
      exists_position_of_card_inf_torus_nine hζ hcomm hexp hcard hFN hFS hmax hUm
    set nω := canonicalRep (coxeterSystem .E6) L ((coxeterSystem .E6).wordProd ω) with hnω
    have hnωN : nω ∈ monomialSubgroup .E6 L := canonicalRep_mem_monomialSubgroup L _
    refine ⟨nω, canonicalRep_mem_adjointGroup _ L _, k, ?_, hpos, nω * n * nω⁻¹, ⟨n, hnF, rfl⟩,
      mul_mem (mul_mem hnωN hnN) (inv_mem hnωN), ?_⟩
    · rintro _ ⟨x, hx, rfl⟩
      exact mul_mem (mul_mem hnωN (hFN x hx)) (inv_mem hnωN)
    · have e : (⟨nω * n * nω⁻¹, mul_mem (mul_mem hnωN hnN) (inv_mem hnωN)⟩ :
          monomialSubgroup .E6 L) = ⟨nω, hnωN⟩ * ⟨n, hnN⟩ * ⟨nω, hnωN⟩⁻¹ := rfl
      rw [e, map_mul, map_mul, map_inv, weylQuotientHom_eq (mapsRootLines_canonicalRep _), hω]
  · have h : F ⊓ torusGroup .E6 L = F :=
      Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [hcard, hUm])
    exact (hFT (h ▸ inf_le_right)).elim

theorem exists_conj_position_of_not_toral [IsAlgClosed L]
    (halg : letI := ZMod.algebra L 2; Algebra.IsAlgebraic (ZMod 2) L)
    {ζ : Lˣ} (hζ : IsPrimitiveRoot ζ 3) {E : Subgroup (ModGL .E6 L)} [Finite E]
    (hEG : E ≤ adjointGroup .E6 L) (hcomm : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x)
    (hexp : ∀ x ∈ E, x ^ 3 = 1) (hcard : Nat.card E = 3 ^ 3)
    (hnt : ¬ ∃ g ∈ adjointGroup .E6 L, ∀ x ∈ E, g * x * g⁻¹ ∈ torusGroup .E6 L) :
    ∃ g ∈ adjointGroup .E6 L, ∃ k : Fin 5,
      (∀ x ∈ E.map (MulAut.conj g).toMonoidHom, x ∈ monomialSubgroup .E6 L) ∧
      (∀ u, u ∈ E.map (MulAut.conj g).toMonoidHom ⊓ torusGroup .E6 L ↔
        ∃ z, PositionMem k z ∧ u = rootDiagUnit .E6 (zetaVec ζ hζ.pow_eq_one z)) ∧
      ∃ n ∈ E.map (MulAut.conj g).toMonoidHom, ∃ hn : n ∈ monomialSubgroup .E6 L,
        weylQuotientHom .E6 L ⟨n, hn⟩ = (coxeterSystem .E6).wordProd (positionWord k) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hidx : ¬ 3 ∣ modelHomE6.range.index := by
    rw [CFSG.StandardType.NoOffExc.index_eq_of_card card_range_modelHomE6
      CFSG.StandardType.NoOffExc.card_weyl_E6 (show 81 * 640 = 51840 by norm_num) (by norm_num)]
    norm_num
  obtain ⟨g₀, hg₀G, hmax⟩ := exists_max_card_inf_torus E
  have := finite_map_conj E g₀
  obtain ⟨c, hcG, hcN, hcS, hcle⟩ := exists_conj_monomial_sylow (ℓ := 2) (p := 3) (by norm_num)
    halg hidx (map_conj_le hEG hg₀G) (map_conj_comm hcomm g₀) (map_conj_pow_eq_one hexp g₀)
  rw [map_conj_map_conj] at hcN hcS hcle
  have hg₁G : c * g₀ ∈ adjointGroup .E6 L := mul_mem hcG hg₀G
  have := finite_map_conj E (c * g₀)
  obtain ⟨g, hgG, k, hN, hT, n, hn, hnN, hw⟩ := exists_position_of_max hζ
    (map_conj_comm hcomm _) (map_conj_pow_eq_one hexp _)
    ((Subgroup.card_map_of_injective (MulAut.conj (c * g₀)).injective).trans hcard) hcN hcS
    (fun h => hnt ⟨c * g₀, hg₁G, fun x hx => h ⟨x, hx, rfl⟩⟩)
    (fun g hg hlt => by
      rw [map_conj_map_conj] at hlt
      have := hmax _ (mul_mem hg hg₁G)
      omega)
  rw [map_conj_map_conj] at hN hT hn
  exact ⟨g * (c * g₀), mul_mem hgG hg₁G, k, hN, hT, n, hn, hnN, hw⟩

end Procedure

section OriginalField


theorem exists_conj_position_inndiag_image_of_not_toral {K : Type} [Field K] [Finite K] [CharP K 2]
    (A : Subgroup (ModGL .E6 K)) (hAI : A ≤ CFSG.StandardType.RecipeExcLang.inndiagGroup .E6 K)
    (hA : CFSG.Open.IsElemAbelian 3 A) (hcard : Nat.card A = 3 ^ 3)
    (hnt : ¬ CFSG.StandardType.ExcFramesHalf.IsToralSubgroup .E6 (AlgebraicClosure K)
      (A.map (baseChangeGL (algebraMap K (AlgebraicClosure K)))))
    (ζ : (AlgebraicClosure K)ˣ) (hζ : IsPrimitiveRoot ζ 3) :
    ∃ g ∈ adjointGroup .E6 (AlgebraicClosure K), ∃ k : Fin 5,
      (∀ x ∈ (A.map (baseChangeGL (algebraMap K (AlgebraicClosure K)))).map
          (MulAut.conj g).toMonoidHom, x ∈ monomialSubgroup .E6 (AlgebraicClosure K)) ∧
      (∀ u, u ∈ (A.map (baseChangeGL (algebraMap K (AlgebraicClosure K)))).map
          (MulAut.conj g).toMonoidHom ⊓ torusGroup .E6 (AlgebraicClosure K) ↔
        ∃ z, PositionMem k z ∧ u = rootDiagUnit .E6 (zetaVec ζ hζ.pow_eq_one z)) ∧
      ∃ n ∈ (A.map (baseChangeGL (algebraMap K (AlgebraicClosure K)))).map
          (MulAut.conj g).toMonoidHom, ∃ hn : n ∈ monomialSubgroup .E6 (AlgebraicClosure K),
        weylQuotientHom .E6 (AlgebraicClosure K) ⟨n, hn⟩ =
          (coxeterSystem .E6).wordProd (positionWord k) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : CharP (AlgebraicClosure K) 2 :=
    charP_of_injective_algebraMap (algebraMap K (AlgebraicClosure K)).injective 2
  have : Finite (ModGL .E6 K) := finite_modGL
  set f := baseChangeGL (τ := .E6) (algebraMap K (AlgebraicClosure K)) with hf
  have hfi : Function.Injective f := baseChangeGL_injective _
  have : Finite ↥(A.map f) := Finite.of_surjective (fun x : A => (⟨f x, x, x.2, rfl⟩ : A.map f))
    (by rintro ⟨_, x, hx, rfl⟩; exact ⟨⟨x, hx⟩, rfl⟩)
  have hEB : CFSG.Open.IsElemAbelian 3 (A.map f) := hA.map f
  have hEG : A.map f ≤ adjointGroup .E6 (AlgebraicClosure K) := by
    rintro _ ⟨a, ha, rfl⟩
    exact CFSG.StandardType.RecipeExcLang.baseChangeGL_mem_adjointGroup_of_mem_inndiag _ (hAI ha)
  have hcomm : ∀ x ∈ A.map f, ∀ y ∈ A.map f, x * y = y * x := by
    let := hEB.1
    intro x hx y hy
    exact congrArg Subtype.val (mul_comm' (⟨x, hx⟩ : A.map f) ⟨y, hy⟩)
  exact exists_conj_position_of_not_toral (isAlgebraic_zmod_algebraicClosure_of_finite K 2) hζ hEG
    hcomm hEB.2 ((Subgroup.card_map_of_injective hfi).trans hcard)
    fun ⟨g, hg, h⟩ => hnt ⟨g⁻¹, inv_mem hg, fun x hx => by rw [inv_inv]; exact h x hx⟩

theorem exists_conj_position_original_image_of_not_toral {K : Type} [Field K] [Finite K]
    [CharP K 2] (A : Subgroup (adjointGroup .E6 K)) (hA : CFSG.Open.IsElemAbelian 3 A)
    (hcard : Nat.card A = 3 ^ 3)
    (hnt : ¬ CFSG.StandardType.ExcFramesHalf.IsToralSubgroup .E6 (AlgebraicClosure K)
      (A.map ((baseChangeGL (algebraMap K (AlgebraicClosure K))).comp
        (adjointGroup .E6 K).subtype)))
    (ζ : (AlgebraicClosure K)ˣ) (hζ : IsPrimitiveRoot ζ 3) :
    ∃ g ∈ adjointGroup .E6 (AlgebraicClosure K), ∃ k : Fin 5,
      (∀ x ∈ (A.map ((baseChangeGL (algebraMap K (AlgebraicClosure K))).comp
          (adjointGroup .E6 K).subtype)).map (MulAut.conj g).toMonoidHom,
        x ∈ monomialSubgroup .E6 (AlgebraicClosure K)) ∧
      (∀ u, u ∈ (A.map ((baseChangeGL (algebraMap K (AlgebraicClosure K))).comp
          (adjointGroup .E6 K).subtype)).map (MulAut.conj g).toMonoidHom ⊓
            torusGroup .E6 (AlgebraicClosure K) ↔
        ∃ z, PositionMem k z ∧ u = rootDiagUnit .E6 (zetaVec ζ hζ.pow_eq_one z)) ∧
      ∃ n ∈ (A.map ((baseChangeGL (algebraMap K (AlgebraicClosure K))).comp
          (adjointGroup .E6 K).subtype)).map (MulAut.conj g).toMonoidHom,
        ∃ hn : n ∈ monomialSubgroup .E6 (AlgebraicClosure K),
          weylQuotientHom .E6 (AlgebraicClosure K) ⟨n, hn⟩ =
            (coxeterSystem .E6).wordProd (positionWord k) := by
  have e : A.map ((baseChangeGL (algebraMap K (AlgebraicClosure K))).comp
      (adjointGroup .E6 K).subtype) =
        (A.map (adjointGroup .E6 K).subtype).map
          (baseChangeGL (algebraMap K (AlgebraicClosure K))) := by rw [Subgroup.map_map]
  rw [e] at hnt ⊢
  exact exists_conj_position_inndiag_image_of_not_toral _
    (by
      rintro _ ⟨a, -, rfl⟩
      exact CFSG.StandardType.RecipeExcLang.adjointGroup_le_inndiagGroup a.2)
    (hA.map _) ((Subgroup.card_map_of_injective (adjointGroup .E6 K).subtype_injective).trans hcard)
    hnt ζ hζ

end OriginalField

section CImage

variable {L : Type} [Field L]

theorem positionBasis_independent : ∀ (k : Fin 5) (s t : ZMod 3),
    s • positionBasis k 0 + t • positionBasis k 1 = 0 → s = 0 ∧ t = 0 := by
  decide +kernel

theorem card_inf_torus_of_position {ζ : Lˣ} (hζ : IsPrimitiveRoot ζ 3)
    {E : Subgroup (ModGL .E6 L)} {k : Fin 5}
    (hT : ∀ u, u ∈ E ⊓ torusGroup .E6 L ↔
      ∃ z, PositionMem k z ∧ u = rootDiagUnit .E6 (zetaVec ζ hζ.pow_eq_one z)) :
    Nat.card ↥(E ⊓ torusGroup .E6 L) = 3 ^ 2 := by
  have hζo : orderOf ζ = 3 := hζ.eq_orderOf.symm
  have hinj : Function.Injective fun p : ZMod 3 × ZMod 3 => rootDiagUnit .E6
      (zetaVec ζ hζ.pow_eq_one (p.1 • positionBasis k 0 + p.2 • positionBasis k 1)) := by
    intro p p' h
    have h1 := rootDiagUnit_zetaVec_injective hζo hζ.pow_eq_one h
    have h2 : (p.1 - p'.1) • positionBasis k 0 + (p.2 - p'.2) • positionBasis k 1 = 0 := by
      rw [sub_smul, sub_smul, sub_add_sub_comm]
      exact sub_eq_zero.2 h1
    obtain ⟨e1, e2⟩ := positionBasis_independent k _ _ h2
    exact Prod.ext (sub_eq_zero.1 e1) (sub_eq_zero.1 e2)
  have hset : ((E ⊓ torusGroup .E6 L : Subgroup (ModGL .E6 L)) : Set (ModGL .E6 L)) =
      Set.range fun p : ZMod 3 × ZMod 3 => rootDiagUnit .E6
        (zetaVec ζ hζ.pow_eq_one (p.1 • positionBasis k 0 + p.2 • positionBasis k 1)) := by
    ext u
    change u ∈ E ⊓ torusGroup .E6 L ↔ _
    rw [hT u]
    constructor
    · rintro ⟨z, ⟨s, t, rfl⟩, rfl⟩
      exact ⟨(s, t), rfl⟩
    · rintro ⟨⟨s, t⟩, rfl⟩
      exact ⟨_, ⟨s, t, rfl⟩, rfl⟩
  have h9 : Nat.card ↥(E ⊓ torusGroup .E6 L) = Nat.card (ZMod 3 × ZMod 3) := by
    rw [← SetLike.coe_sort_coe, Nat.card_coe_set_eq, hset, Set.ncard_range_of_injective hinj]
  rw [h9, Nat.card_prod, Nat.card_zmod]
  norm_num

theorem zpowers_cE6_iff_of_position {ζ : Lˣ} (hζ : IsPrimitiveRoot ζ 3)
    {E : Subgroup (ModGL .E6 L)} (hcard : Nat.card E = 3 ^ 3) {k : Fin 5} (hk : k.val < 3)
    (hEM : E ≤ monomialSubgroup .E6 L)
    (hT : ∀ u, u ∈ E ⊓ torusGroup .E6 L ↔
      ∃ z, PositionMem k z ∧ u = rootDiagUnit .E6 (zetaVec ζ hζ.pow_eq_one z))
    {n : ModGL .E6 L} (hn : n ∈ E)
    (hw : weylQuotientHom .E6 L ⟨n, hEM hn⟩ = (coxeterSystem .E6).wordProd (positionWord k)) :
    ∀ w, w ∈ Subgroup.zpowers cE6 ↔ ∃ e, ∃ he : e ∈ E, weylQuotientHom .E6 L ⟨e, hEM he⟩ = w := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hc : weylQuotientHom .E6 L ⟨n, hEM hn⟩ = cE6 := by
    rw [hw, positionWord, if_pos hk]
    rfl
  set ψ := (weylQuotientHom .E6 L).comp (Subgroup.inclusion hEM) with hψ
  have hψcard : Nat.card ψ.range = 3 := by
    have h := card_inf_torus_mul_card_range hEM
    rw [card_inf_torus_of_position hζ hT, hcard] at h
    have h' : 9 * Nat.card ψ.range = 9 * 3 := h.trans (by norm_num)
    exact Nat.eq_of_mul_eq_mul_left (by norm_num) h'
  have hcR : cE6 ∈ ψ.range := ⟨⟨n, hn⟩, hc⟩
  have hR : ψ.range = Subgroup.zpowers cE6 := by
    refine (Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.2 hcR) ?_).symm
    rw [hψcard, Nat.card_zpowers, orderOf_eq_prime cE6_pow_three cE6_ne_one]
  intro w
  rw [← hR]
  constructor
  · rintro ⟨⟨e, he⟩, rfl⟩
    exact ⟨e, he, rfl⟩
  · rintro ⟨e, he, rfl⟩
    exact ⟨⟨e, he⟩, rfl⟩

end CImage

end CFSG.LieType.Chevalley.E6Three.Position
