module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.S267BadExcTorusLift
public import CFSG.LieType.SeitzGeneration.ExcTorusCatTw
import CFSG.RankThree.Chevalley.SteinbergBTE6HighestRootGraph
import CFSG.RankThree.PartTwo.Sec11.KS11Lie5ProofWeyl
import CFSG.LieType.Steinberg.CentralExt.GriessTwistedE6
import CFSG.LocalAnalysis.GLTheoremA.CatA.S267ModelGenA

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S267.BadExc

open CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.RankThree.PartOne.KE
open scoped Matrix

section Tuples

variable {L : Type} [Field L] {n : ℕ}

@[expose] def twoTorsionTuples (L : Type) [Field L] (n : ℕ) : Subgroup (Fin n → Lˣ) where
  carrier := {a | ∀ i, a i ^ 2 = 1}
  mul_mem' {a b} ha hb i := by rw [Pi.mul_apply, mul_pow, ha i, hb i, one_mul]
  one_mem' i := by rw [Pi.one_apply, one_pow]
  inv_mem' {a} ha i := by rw [Pi.inv_apply, inv_pow, ha i, inv_one]

theorem mem_twoTorsionTuples {a : Fin n → Lˣ} : a ∈ twoTorsionTuples L n ↔ ∀ i, a i ^ 2 = 1 :=
  Iff.rfl

theorem card_twoTorsionTuples (h2 : (2 : L) ≠ 0) : Nat.card (twoTorsionTuples L n) = 2 ^ n := by
  classical
  have hne : (-1 : Lˣ) ≠ 1 := by
    intro h
    have h' := congrArg Units.val h
    rw [Units.val_neg, Units.val_one] at h'
    apply h2
    linear_combination -h'
  have hpm : ∀ x : Lˣ, x ^ 2 = 1 → x = 1 ∨ x = -1 := by
    intro x hx
    have h := (mul_self_eq_one_iff (a := (x : L))).1 (by
      rw [← sq, ← Units.val_pow_eq_pow_val, hx, Units.val_one])
    rcases h with h | h
    · exact Or.inl (Units.ext h)
    · exact Or.inr (Units.ext (by rw [h, Units.val_neg, Units.val_one]))
  have hsgn : ∀ b : Bool, ((if b then (1 : Lˣ) else -1) ^ 2) = 1 := fun b => by
    cases b <;> simp
  let e : twoTorsionTuples L n ≃ (Fin n → Bool) :=
    { toFun := fun a i => decide ((a : Fin n → Lˣ) i = 1)
      invFun := fun b => ⟨fun i => if b i then 1 else -1, fun i => hsgn (b i)⟩
      left_inv := fun a => by
        apply Subtype.ext
        funext i
        rcases hpm _ (a.2 i) with h | h
        · simp [h]
        · simp [h, hne]
      right_inv := fun b => by
        funext i
        cases hb : b i <;> simp [hb, hne] }
  rw [Nat.card_congr e, Nat.card_fun, Nat.card_eq_fintype_card, Fintype.card_bool, Nat.card_fin]

theorem twoTorsionTuples_le_fixedCharTuples {τ : Tag} {Fr : L →+* L} {q : ℕ} (hq : Odd q)
    (hFr : ∀ c, Fr c = c ^ q) :
    twoTorsionTuples L τ.rank ≤ fixedCharTuples (-1 : Matrix (Fin τ.rank) (Fin τ.rank) ℤ) Fr := by
  intro a ha u
  have hsq : rootChar a u ^ 2 = 1 := by
    rw [rootChar, ← Finset.prod_pow]
    refine Finset.prod_eq_one fun i _ => ?_
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, ha i, one_zpow]
  have hinv : (rootChar a u)⁻¹ = rootChar a u := by
    rw [inv_eq_iff_mul_eq_one, ← sq, hsq]
  have hneg : rootChar a ((-1 : Matrix (Fin τ.rank) (Fin τ.rank) ℤ) *ᵥ u) = (rootChar a u)⁻¹ := by
    rw [Matrix.neg_mulVec, Matrix.one_mulVec, rootChar, rootChar, ← Finset.prod_inv_distrib]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [Pi.neg_apply, zpow_neg]
  have hFix : Units.map Fr.toMonoidHom (rootChar a u) = rootChar a u := by
    refine Units.ext ?_
    change Fr ((rootChar a u : Lˣ) : L) = ((rootChar a u : Lˣ) : L)
    rw [hFr]
    obtain ⟨k, rfl⟩ := hq
    have hsq' : ((rootChar a u : Lˣ) : L) ^ 2 = 1 := by
      rw [← Units.val_pow_eq_pow_val, hsq, Units.val_one]
    rw [pow_succ, pow_mul, hsq', one_pow, one_mul]
  rw [hneg, hinv, hFix]

end Tuples

section Two


theorem exists_elemAbelian_two_pow_six_twistedE6 {ℓ f : ℕ} (hℓ : ℓ.Prime) (hℓ2 : ℓ ≠ 2)
    (hf : 1 ≤ f) (K : Type) [Field K] (hK : Nat.card K = (ℓ ^ f) ^ 2) (σ : K ≃+* K)
    (hσ : ∀ c, σ c = c ^ (ℓ ^ f)) :
    ∃ V : Subgroup ↥(twistedE6RootGroup K σ), IsElemAbelian 2 V ∧ Nat.card V = 2 ^ 6 := by
  classical
  have : Fact ℓ.Prime := ⟨hℓ⟩
  have hK0 : Nat.card K ≠ 0 := by
    rw [hK]
    exact pow_ne_zero _ (pow_ne_zero _ hℓ.ne_zero)
  have : Finite K := Nat.finite_of_card_ne_zero hK0
  have : Fintype K := Fintype.ofFinite K
  have : CharP K ℓ := charP_of_card_eq_prime_pow (f := f * 2)
    (by rw [← Nat.card_eq_fintype_card, hK, ← pow_mul])
  have : Finite (ModGL TwistTag.E6.tag K) := finite_modGL
  let L := AlgebraicClosure K
  have : CharP L ℓ := charP_of_injective_algebraMap (algebraMap K L).injective ℓ
  have : IsAlgClosed L := IsAlgClosure.isAlgClosed K
  let Fr : L →+* L := iterateFrobenius L ℓ f
  have hFr : ∀ c, Fr c = c ^ (ℓ ^ f) := fun c => iterateFrobenius_def ℓ f c
  have h2 : (2 : L) ≠ 0 := by
    intro h
    have h' : ((2 : ℕ) : L) = 0 := by exact_mod_cast h
    rw [CharP.cast_eq_zero_iff L ℓ] at h'
    exact hℓ2 ((Nat.prime_dvd_prime_iff_eq hℓ Nat.prime_two).1 h')
  have hodd : Odd (ℓ ^ f) := (hℓ.eq_two_or_odd'.resolve_left hℓ2).pow
  set v := CFSG.RankThree.Chevalley.e6HRReflProd with hvdef
  have hv : ∀ x, v • x =
      (-1 : Matrix (Fin TwistTag.E6.tag.rank) (Fin TwistTag.E6.tag.rank) ℤ) *ᵥ
        permLattice TwistTag.E6.perm x := fun x => by
    rw [CFSG.RankThree.Chevalley.e6HRReflProd_smul, Matrix.neg_mulVec, Matrix.one_mulVec]
  obtain ⟨g0, hg0C, hg0⟩ := lang_conjugator_twisted K (ℓ := ℓ) (f := f) hf L v
  obtain ⟨-, -, hder, ⟨k, hk⟩, -, -, -⟩ :=
    CFSG.RankThree.Classical2.twisted_E6_full_rational_fixed_group_order hℓ hf K hK σ.toRingHom hσ
      L Fr hFr
  set R' := twistedFixedGroup TwistTag.E6 L Fr with hR'
  set C' := (graphFixedRootGroup TwistTag.E6 K σ.toRingHom).map
    (baseChangeGL (algebraMap K L)) with hC'
  have hnormal : (C'.subgroupOf R').Normal := by
    have e : C'.subgroupOf R' = ⁅(⊤ : Subgroup R'), ⊤⁆ := by
      have h1 : ⁅R', R'⁆ = Subgroup.map R'.subtype ⁅(⊤ : Subgroup R'), ⊤⁆ := by
        rw [Subgroup.map_commutator, ← MonoidHom.range_eq_map R'.subtype, Subgroup.range_subtype]
      rw [← hder, h1]
      exact Subgroup.comap_map_eq_self_of_injective (Subgroup.subtype_injective _) _
    rw [e]
    infer_instance
  let ι : twistedE6RootGroup K σ →* ModGL TwistTag.E6.tag L :=
    (baseChangeGL (algebraMap K L)).comp (twistedE6RootGroup K σ).subtype
  have hrange : ι.range = C' := by
    change ((baseChangeGL (algebraMap K L)).comp (twistedE6RootGroup K σ).subtype).range = _
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
  have hι : Function.Injective ι :=
    (baseChangeGL_injective _).comp (Subgroup.subtype_injective _)
  have hT0 := twistedTorus_E6_eq_map (L := L) Fr v _ hv
  set A := twoTorsionTuples L TwistTag.E6.tag.rank with hA
  have hAfix := twoTorsionTuples_le_fixedCharTuples (τ := TwistTag.E6.tag) hodd hFr
  set V₀ := A.map (rootDiagUnitHom TwistTag.E6.tag L) with hV₀
  have hV₀T : V₀ ≤ twistedTorusOf (canonicalRep (coxeterSystem TwistTag.E6.tag) L v)
      (twistHom TwistTag.E6 L Fr) := by
    rw [hT0]
    exact Subgroup.map_mono hAfix
  set V₁ := V₀.map (MulAut.conj g0).toMonoidHom with hV₁
  have hAcard : Nat.card A = 2 ^ 6 := card_twoTorsionTuples h2
  have hrinj : Function.Injective (rootDiagUnitHom TwistTag.E6.tag L) :=
    CFSG.RankThree.PartTwo.Sec11.KS11Lie5Proof.rootDiagUnit_injective'
  have hV₁card : Nat.card V₁ = 2 ^ 6 := by
    rw [hV₁, Subgroup.card_map_of_injective (MulAut.conj g0).injective, hV₀,
      Subgroup.card_map_of_injective hrinj, hAcard]
  have hV₁fin : Finite V₁ := Nat.finite_of_card_ne_zero (by rw [hV₁card]; positivity)
  have hV₁R : V₁ ≤ R' := by
    rintro _ ⟨y, hy, rfl⟩
    have hyT := hV₀T hy
    have hyC := twistedTorusOf_le_adjointGroup _ _ hyT
    have hyfix := (mem_twistedTorusOf.1 hyT).2
    refine (mem_twistedFixedGroup_iff_twistHom _ _ _).2
      ⟨mul_mem (mul_mem hg0C hyC) (inv_mem hg0C), ?_⟩
    change twistHom TwistTag.E6 L Fr (g0 * y * g0⁻¹) = g0 * y * g0⁻¹
    rw [map_mul, map_mul, map_inv, hg0]
    calc g0 * canonicalRep (coxeterSystem TwistTag.E6.tag) L v * twistHom TwistTag.E6 L Fr y *
          (g0 * canonicalRep (coxeterSystem TwistTag.E6.tag) L v)⁻¹ =
        g0 * (canonicalRep (coxeterSystem TwistTag.E6.tag) L v * twistHom TwistTag.E6 L Fr y *
          (canonicalRep (coxeterSystem TwistTag.E6.tag) L v)⁻¹) * g0⁻¹ := by group
      _ = g0 * y * g0⁻¹ := by rw [hyfix]
  have hsq : ∀ x ∈ V₁, x ^ 2 = 1 := by
    rintro _ ⟨_, ⟨a, ha, rfl⟩, rfl⟩
    rw [← map_pow, ← map_pow]
    have : a ^ 2 = 1 := funext fun i => by rw [Pi.pow_apply, ha i, Pi.one_apply]
    rw [this, map_one, map_one]
  have hV₁p : IsPGroup 2 V₁ := fun x => ⟨1, Subtype.ext (by
    rw [pow_one, Subgroup.coe_pow, Subgroup.coe_one]
    exact hsq x x.2)⟩
  have hV₁C : V₁ ≤ C' :=
    le_of_isPGroup_of_index_eq_pow hV₁R Nat.prime_two Nat.prime_three (by norm_num) hk hV₁p
  have hV₁range : V₁ ≤ ι.range := hrange ▸ hV₁C
  have hmap : (V₁.comap ι).map ι = V₁ := by
    rw [Subgroup.map_comap_eq, inf_eq_right.2 hV₁range]
  refine ⟨V₁.comap ι, ⟨⟨⟨fun x y => Subtype.ext (hι ?_)⟩⟩, fun x hx => hι ?_⟩, ?_⟩
  ·
    have hx := x.2
    have hy := y.2
    obtain ⟨_, ⟨a, -, rfl⟩, hxa⟩ := Subgroup.mem_comap.1 hx
    obtain ⟨_, ⟨b, -, rfl⟩, hyb⟩ := Subgroup.mem_comap.1 hy
    change ι ((x : twistedE6RootGroup K σ) * y) = ι (y * x)
    rw [map_mul, map_mul, ← hxa, ← hyb, ← map_mul, ← map_mul, ← map_mul, ← map_mul, mul_comm a b]
  · rw [map_pow, map_one]
    exact hsq _ (Subgroup.mem_comap.1 hx)
  · rw [← Subgroup.card_map_of_injective hι, hmap, hV₁card]

theorem exists_twoLocal_rootSpan_graphFixed {t : TwistTag}
    (ht : t.tag = .D4 ∨ t.tag = .E6 ∨ t.tag = .E7 ∨ t.tag = .E8) {K : Type} [Field K] {ℓ : ℕ}
    [CharP K ℓ] (h2 : (2 : K) ≠ 0) {σ : K →+* K} (hσ : Function.Surjective σ) {r : ℕ}
    (hr : ∀ a, Nat.card (orbitField t K σ a) = r ^ (t.orbit a).card) {k : ℕ}
    {α : Fin k → Fin t.tag.rank → ℤ} {i₀ : Fin t.tag.rank} {γ : Fin t.tag.rank → ℤ}
    (hck : RootSpanCheck t.tag α i₀ γ) (hρ : ∀ i, ∃ j, permLattice t.perm (α i) = α j)
    (hi₀ : CFSG.RankThree.PartOne.torusWord t.tag K {i₀} ∈ graphFixedRootGroup t K σ) :
    ∃ U E : Subgroup ↥(graphFixedRootGroup t K σ), IsPGroup 2 U ∧ U ≠ ⊥ ∧
      E ≤ Subgroup.normalizer (U : Set ↥(graphFixedRootGroup t K σ)) ∧ IsElemAbelian ℓ E ∧
        Nat.card E = r ^ k := by
  classical
  have hroot : ∀ i, IsRoot t.tag (α i) := fun i => RootOps.isRootB_iff.1 (hck.1 i)
  have hinj : Function.Injective α := fun i j h => by
    by_contra hij
    exact (hck.2.2.1 i j hij).1 h
  set S : Set (Fin t.tag.rank → ℤ) := Set.range α with hSdef
  have hS : ∀ β ∈ S, IsRoot t.tag β ∧ 0 < height β := by
    rintro _ ⟨i, rfl⟩
    exact ⟨hroot i, hck.2.1 i⟩
  have hclosed : ∀ β ∈ S, ∀ β' ∈ S, ∀ a b : ℕ, 1 ≤ a → 1 ≤ b →
      IsRoot t.tag (a • β + b • β') → a • β + b • β' ∈ S := by
    rintro _ ⟨i, rfl⟩ _ ⟨j, rfl⟩ a b ha hb hr
    exact absurd hr (not_isRoot_nsmul_add_nsmul_of_check ht hck i j ha hb)
  have hSρ : ∀ β ∈ S, permLattice t.perm β ∈ S := by
    rintro _ ⟨i, rfl⟩
    obtain ⟨j, hj⟩ := hρ i
    exact ⟨j, hj.symm⟩
  have hcardΓ : Nat.card ↥(rootSpan t.tag K S ⊓ twistedFixedGroup t K σ) = r ^ k := by
    rw [CFSG.Timmesfeld.ExceptionalOrders.card_rootSpan_inf_twistedFixedGroup hσ hr hS hSρ
      hclosed, Set.ncard_range_of_injective hinj, Nat.card_fin]
  set E₀ := rootSpan t.tag K S with hE₀def
  have hE₀ : E₀ = Subgroup.closure (⋃ i, Set.range (pinnedX t.tag K (α i))) := by
    rw [hE₀def, rootSpan, Subgroup.closure_iUnion]
    apply le_antisymm
    · refine iSup₂_le fun β hβ => ?_
      obtain ⟨i, rfl⟩ := hβ
      exact le_iSup (fun i => rootSubgroup t.tag K (α i)) i
    · exact iSup_le fun i => le_iSup₂ (f := fun β (_ : β ∈ S) => rootSubgroup t.tag K β) (α i)
        ⟨i, rfl⟩
  have hgen : ∀ x ∈ ⋃ i, Set.range (pinnedX t.tag K (α i)),
      ∀ y ∈ ⋃ i, Set.range (pinnedX t.tag K (α i)), Commute x y := by
    intro x hx y hy
    obtain ⟨i, c, rfl⟩ := Set.mem_iUnion.1 hx
    obtain ⟨j, d, rfl⟩ := Set.mem_iUnion.1 hy
    by_cases hij : i = j
    · subst hij
      change pinnedX t.tag K (α i) c * pinnedX t.tag K (α i) d =
        pinnedX t.tag K (α i) d * pinnedX t.tag K (α i) c
      rw [← pinnedX_add, ← pinnedX_add, add_comm]
    · obtain ⟨hne, hsum⟩ := hck.2.2.1 i j hij
      have hne' : α i ≠ -α j := by
        intro h
        have h1 := hck.2.1 i
        have h2 := hck.2.1 j
        rw [h] at h1
        simp only [height, Pi.neg_apply, Finset.sum_neg_distrib] at h1 h2
        omega
      have hnr : ¬ IsRoot t.tag (α i + α j) := fun h => by
        rw [← RootOps.isRootB_iff, hsum] at h
        exact Bool.false_ne_true h
      exact (simply_laced_root_commutator_unit t.tag ht (hroot i) (hroot j) hne hne').2 hnr K _
        (mem_rootSubgroup.2 ⟨c, rfl⟩) _ (mem_rootSubgroup.2 ⟨d, rfl⟩)
  have hcomm₁ : ∀ x ∈ ⋃ i, Set.range (pinnedX t.tag K (α i)),
      ∀ y ∈ Subgroup.closure (⋃ i, Set.range (pinnedX t.tag K (α i))), Commute x y := by
    intro x hx y hy
    induction hy using Subgroup.closure_induction with
    | mem y hy => exact hgen x hx y hy
    | one => exact Commute.one_right x
    | mul y z _ _ hy hz => exact hy.mul_right hz
    | inv y _ hy => exact hy.inv_right
  have hcomm : ∀ x ∈ E₀, ∀ y ∈ E₀, Commute x y := by
    intro x hx y hy
    rw [hE₀] at hx hy
    induction hx using Subgroup.closure_induction with
    | mem x hx => exact hcomm₁ x hx y hy
    | one => exact Commute.one_left y
    | mul x z _ _ hx hz => exact hx.mul_left hz
    | inv x _ hx => exact hx.inv_left
  have hpow : ∀ x ∈ E₀, x ^ ℓ = 1 := by
    intro x hx
    rw [hE₀] at hx
    induction hx using Subgroup.closure_induction with
    | mem x hx =>
      obtain ⟨i, c, rfl⟩ := Set.mem_iUnion.1 hx
      have hn : ∀ n : ℕ, pinnedX t.tag K (α i) c ^ n = pinnedX t.tag K (α i) ((n : K) * c) := by
        intro n
        induction n with
        | zero => simp [pinnedX_zero]
        | succ n ih => rw [pow_succ, ih, ← pinnedX_add]; push_cast; ring_nf
      rw [hn, CharP.cast_eq_zero, zero_mul, pinnedX_zero]
    | one => exact one_pow ℓ
    | mul x y hx hy hxq hyq =>
      have hxy : Commute x y := by
        rw [← hE₀] at hx hy
        exact hcomm x hx y hy
      rw [hxy.mul_pow, hxq, hyq, one_mul]
    | inv x hx hxq => rw [inv_pow, hxq, inv_one]
  have hle : E₀ ⊓ twistedFixedGroup t K σ ≤ graphFixedRootGroup t K σ :=
    (inf_le_inf_right _ (rootSpan_le_posUnipotent hS)).trans
      (graphFixedPosUnipotent_le_graphFixedRootGroup t K σ)
  set w : ModGL t.tag K := CFSG.RankThree.PartOne.torusWord t.tag K {i₀} with hwdef
  have hw2 : w ^ 2 = 1 := CFSG.RankThree.PartOne.torusWord_sq _
  have hw1 : w ≠ 1 := CFSG.RankThree.PartOne.torusWord_ne_one_of_odd {i₀}
    (RootOps.isRootB_iff.1 hck.2.2.2.2.1) (by simpa using hck.2.2.2.2.2) h2
  have hwc : ∀ x ∈ E₀, Commute w x := by
    intro x hx
    rw [hE₀] at hx
    induction hx using Subgroup.closure_induction with
    | mem x hx =>
      obtain ⟨i, c, rfl⟩ := Set.mem_iUnion.1 hx
      exact CFSG.RankThree.PartOne.torusWord_commute_pinnedX_of_even {i₀} (hroot i) c
        (by simpa using hck.2.2.2.1 i)
    | one => exact Commute.one_right w
    | mul x y _ _ hx hy => exact hx.mul_right hy
    | inv x _ hx => exact hx.inv_right
  set w' : ↥(graphFixedRootGroup t K σ) := ⟨w, hi₀⟩
  have hw'2 : w' ^ 2 = 1 := Subtype.ext (by simp [w', hw2])
  have hw'1 : w' ≠ 1 := fun h => hw1 (congrArg Subtype.val h)
  refine ⟨Subgroup.zpowers w', (E₀ ⊓ twistedFixedGroup t K σ).subgroupOf
      (graphFixedRootGroup t K σ),
    CFSG.LocalAnalysis.GLTheoremA.S267.ModelGen.isPGroup_two_zpowers_of_sq hw'2,
    CFSG.LocalAnalysis.GLTheoremA.S267.ModelGen.zpowers_ne_bot_of_ne_one hw'1, ?_, ?_, ?_⟩
  · intro e he
    refine CFSG.LocalAnalysis.GLTheoremA.S267.ModelGen.mem_normalizer_of_forall_comm
      fun u hu => ?_
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 hu
    have hc : e * w' = w' * e :=
      Subtype.ext (hwc _ (Subgroup.mem_subgroupOf.1 he).1).eq.symm
    exact (Commute.zpow_right hc n).eq
  · refine ⟨⟨⟨fun a b => Subtype.ext (Subtype.ext ?_)⟩⟩, fun x hx => Subtype.ext ?_⟩
    · exact hcomm _ (Subgroup.mem_subgroupOf.1 a.2).1 _ (Subgroup.mem_subgroupOf.1 b.2).1
    · exact hpow _ (Subgroup.mem_subgroupOf.1 hx).1
  · rw [← hcardΓ]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv

@[expose] def twE6WitnessRoots : Fin 5 → Fin TwistTag.E6.tag.rank → ℤ :=
  ![![0, 0, 0, 0, 0, 1], ![1, 0, 0, 0, 0, 0], ![0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 1],
    ![1, 0, 1, 0, 0, 0]]

theorem rootSpanCheck_twE6Witness :
    RootSpanCheck TwistTag.E6.tag twE6WitnessRoots ⟨1, by decide⟩ ![0, 0, 0, 1, 0, 0] := by
  unfold RootSpanCheck twE6WitnessRoots
  decide +kernel

theorem permLattice_twE6Witness (i : Fin 5) :
    ∃ j, permLattice TwistTag.E6.perm (twE6WitnessRoots i) = twE6WitnessRoots j := by
  have h : ∀ i : Fin 5, ∃ j : Fin 5, ∀ k : Fin TwistTag.E6.tag.rank,
      twE6WitnessRoots i (TwistTag.E6.perm.symm k) = twE6WitnessRoots j k := by
    unfold twE6WitnessRoots
    decide
  obtain ⟨j, hj⟩ := h i
  exact ⟨j, funext hj⟩

theorem exists_twoLocal_rootSpan_twistedE6 {ℓ f : ℕ} (hℓ : ℓ.Prime) (hℓ2 : ℓ ≠ 2) (hf : 1 ≤ f)
    (K : Type) [Field K] (hK : Nat.card K = (ℓ ^ f) ^ 2) (σ : K ≃+* K)
    (hσ : ∀ c, σ c = c ^ (ℓ ^ f)) :
    ∃ U E : Subgroup ↥(twistedE6RootGroup K σ), IsPGroup 2 U ∧ U ≠ ⊥ ∧
      E ≤ Subgroup.normalizer (U : Set ↥(twistedE6RootGroup K σ)) ∧ IsElemAbelian ℓ E ∧
        Nat.card E = ℓ ^ (5 * f) := by
  have hK2f : Nat.card K = ℓ ^ (2 * f) := by rw [hK, ← pow_mul, mul_comm]
  haveI : CharP K ℓ :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic hℓ (by omega) hK2f
  have h2 : (2 : K) ≠ 0 := Ring.two_ne_zero (by rw [ringChar.eq K ℓ]; exact hℓ2)
  have hneg : ∀ g : orbitField TwistTag.E6 K σ.toRingHom ⟨3, by decide⟩ →+* K,
      Units.map g.toMonoidHom (-1) = -1 := fun g =>
    Units.ext (by
      change g (((-1 : (orbitField TwistTag.E6 K σ.toRingHom ⟨3, by decide⟩)ˣ) :
        orbitField TwistTag.E6 K σ.toRingHom ⟨3, by decide⟩)) = ((-1 : Kˣ) : K)
      rw [Units.val_neg, Units.val_one, Units.val_neg, Units.val_one, map_neg, map_one])
  have hw : CFSG.RankThree.PartOne.torusWord TwistTag.E6.tag K {⟨1, by decide⟩} =
      torusElt TwistTag.E6.tag K ⟨1, by decide⟩ (-1) := by
    rw [CFSG.RankThree.PartOne.torusWord_eq_list_prod, List.ofFn_eq_map,
      list_prod_torusElt_eq_rootDiagUnit, torusElt_eq_rootDiagUnit]
    congr 1
    funext l
    unfold cartanChar
    rw [Finset.prod_eq_single ⟨1, by decide⟩ (fun j _ hj => by simp [hj])
      (fun h => absurd (Finset.mem_univ _) h)]
    simp
  have hi₀ : CFSG.RankThree.PartOne.torusWord TwistTag.E6.tag K {⟨1, by decide⟩} ∈
      twistedE6RootGroup K σ := by
    have hmem := orbitH_mem_graphFixedRootGroup TwistTag.E6 σ.toRingHom ⟨3, by decide⟩ (-1)
    rw [coe_orbitH, show (TwistTag.E6.orbit ⟨3, by decide⟩).card = 1 by decide,
      show TwistTag.E6.orbitMin ⟨3, by decide⟩ = ⟨1, by decide⟩ by decide,
      show List.range 1 = [0] from rfl] at hmem
    simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one, pow_zero,
      Equiv.Perm.one_apply, RingHom.one_def, RingHom.id_comp] at hmem
    rw [hneg] at hmem
    rw [hw]
    exact hmem
  obtain ⟨U, E, hU, hUne, hEU, hE, hEc⟩ := exists_twoLocal_rootSpan_graphFixed
    (Or.inr (Or.inl rfl)) h2 σ.surjective
    (CFSG.Timmesfeld.ExceptionalOrders.card_orbitField (t := TwistTag.E6) hℓ hf hK hσ)
    rootSpanCheck_twE6Witness permLattice_twE6Witness hi₀
  exact ⟨U, E, hU, hUne, hEU, hE, by rw [hEc, ← pow_mul, mul_comm]⟩

end Two

section Cat


open CFSG.Blueprint.Multiplier CFSG.LieType.SeitzGeneration CFSG.TauCetiBridge

theorem five_le_twoLocalRank_cat_twistedE6 (Q : TauCeti.PrimePower)
    (hv : (TauCeti.LieTypeIndex.twistedE6 Q).Valid) (hQ2 : Q.p ≠ 2) {X : Type} [Group X]
    [Finite X] (φ : X →* (TauCeti.CFSGIndex.lie ⟨.twistedE6 Q, hv⟩).Group)
    (hφ : Function.Surjective φ) : 5 ≤ GLATwoLocalRank Q.p X := by
  obtain ⟨K, _, σ, hK, hσ, ⟨ec⟩⟩ := CFSG.LieType.SeitzGeneration.exists_catEquiv_twistedE6 Q hv
  obtain ⟨hfin, hsimp⟩ :=
    CFSG.HardMathSupport.Timmesfeld.CrossChar.finite_isSimpleGroup_cat_twistedE6 hv
  haveI := hfin
  haveI := hsimp
  have hmodel : CFSG.Models.LieModel (Cat ⟨.twistedE6 Q, hv⟩) .twistedE6 0 Q.p Q.exponent :=
    ⟨⟨Q.prime_p, Q.exponent_pos, rfl⟩,
      Or.inr ⟨rfl, ⟨.twistedE6 Q, hv⟩, ⟨rfl, rfl⟩, ⟨MulEquiv.refl _⟩⟩⟩
  have hq3 : 3 ≤ Q.p ^ Q.exponent :=
    (lt_of_le_of_ne Q.prime_p.two_le (Ne.symm hQ2)).trans_le
      (Nat.le_self_pow Q.exponent_pos.ne' _)
  obtain ⟨hperf, ⟨eM⟩⟩ :=
    CFSG.LieType.Steinberg.CentralExt.GriessExceptional.twistedE6_row hmodel hq3
  have hM : ¬ Q.p ∣ Nat.card (CFSG.Open.griessHopfMultiplier (Cat ⟨.twistedE6 Q, hv⟩)) := by
    rw [Nat.card_congr eM.toEquiv]
    have hex : exceptionalOrders .twistedE6 0 Q.p Q.exponent = (1, 1) := by
      unfold exceptionalOrders
      split <;> simp_all
    simp only [generic, exceptional, hex, Nat.card_prod, Nat.card_congr Multiplicative.toAdd,
      Nat.card_zmod, genericOrders, mul_one]
    intro h
    have h1 : Q.p ∣ Q.p ^ Q.exponent + 1 := h.trans (Nat.gcd_dvd_right _ _)
    have h0 : Q.p ∣ Q.p ^ Q.exponent := dvd_pow_self _ Q.exponent_pos.ne'
    exact Q.prime_p.not_dvd_one ((Nat.dvd_add_right h0).1 h1)
  have hnc := exists_ne_comm_of_perfect hperf
  obtain ⟨V, hVe, hVc⟩ :=
    exists_elemAbelian_two_pow_six_twistedE6 Q.prime_p hQ2 Q.exponent_pos K hK σ hσ
  obtain ⟨U, E, hU, hUne, hEU, hE, hEc⟩ :=
    exists_twoLocal_rootSpan_twistedE6 Q.prime_p hQ2 Q.exponent_pos K hK σ hσ
  obtain ⟨hU', hUne', hEU', hE', hEc'⟩ :=
    CFSG.HardMathSupport.Solomon.Coordinator.i1020_map_witness ec.symm.toMonoidHom
      ec.symm.injective hU hEU hE hEc
  refine le_twoLocalRank_of_witnesses hnc Q.prime_p hQ2 hM
    ⟨V.map ec.symm.toMonoidHom, CFSG.SectionRank.isElemAbelian_map hVe _, ?_⟩
    ⟨_, _, hU', hUne' hUne, hEU', hE', 5 * Q.exponent, by have := Q.exponent_pos; omega, hEc'⟩
    φ hφ
  rw [Subgroup.card_map_of_injective ec.symm.injective, hVc]

end Cat

end CFSG.LocalAnalysis.GLTheoremA.S267.BadExc

end
