module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.S267HqRankLift
public import CFSG.LieType.Steinberg.CentralExt.GriessExceptional
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcInnerBridge
public import CFSG.RankThree.PartOne.S11c.TorusWords
public import CFSG.Timmesfeld.Orders.ExceptionalTorus
import CFSG.LocalAnalysis.GLTheoremA.CatA.S267ModelGenA
public import CFSG.RankThree.Lattice.SteinbergBIListMatrix

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S267.BadExc

open CFSG.Open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley

theorem neg_one_pow_eq_pow_mod_two' {G : Type*} [Monoid G] [HasDistribNeg G] (n : ℕ) :
    (-1 : G) ^ n = (-1 : G) ^ (n % 2) := by
  conv_lhs => rw [← Nat.mod_add_div n 2, pow_add, pow_mul, neg_one_sq, one_pow, mul_one]

@[expose] def zmodTwoSign (K : Type*) [Field K] : Multiplicative (ZMod 2) →* Kˣ where
  toFun x := (-1 : Kˣ) ^ (Multiplicative.toAdd x).val
  map_one' := by simp
  map_mul' x y := by
    simp only [toAdd_mul]
    rw [ZMod.val_add, ← pow_add, neg_one_pow_eq_pow_mod_two' (n := _ + _)]

theorem zmodTwoSign_ofAdd {K : Type*} [Field K] (x : ZMod 2) :
    zmodTwoSign K (Multiplicative.ofAdd x) = (-1 : Kˣ) ^ x.val := rfl

theorem zmodTwoSign_zpow {K : Type*} [Field K] (x : ZMod 2) (a : ℤ) :
    zmodTwoSign K (Multiplicative.ofAdd x) ^ a =
      zmodTwoSign K (Multiplicative.ofAdd ((a : ZMod 2) * x)) := by
  rw [← map_zpow, ← ofAdd_zsmul, zsmul_eq_mul]

theorem zmodTwoSign_eq_one_iff {K : Type*} [Field K] (h2 : (2 : K) ≠ 0) (x : ZMod 2) :
    zmodTwoSign K (Multiplicative.ofAdd x) = 1 ↔ x = 0 := by
  rw [zmodTwoSign_ofAdd]
  constructor
  · intro h
    by_contra hx
    have h1 : x.val = 1 := by
      have := ZMod.val_lt x
      have := (ZMod.val_ne_zero x).2 hx
      omega
    rw [h1, pow_one] at h
    have h' := congrArg (fun u : Kˣ => (u : K)) h
    simp only [Units.val_neg, Units.val_one] at h'
    exact h2 (by linear_combination -h')
  · rintro rfl
    simp

@[expose] def torusSign (K : Type*) [Field K] {m n : ℕ} (J : Fin m → Fin n) :
    Multiplicative (Fin m → ZMod 2) →* (Fin n → Kˣ) where
  toFun s j := zmodTwoSign K (Multiplicative.ofAdd
    (∑ i, if J i = j then Multiplicative.toAdd s i else 0))
  map_one' := by
    funext j
    simp
  map_mul' s t := by
    funext j
    simp only [Pi.mul_apply, ← map_mul, ← ofAdd_add, toAdd_mul, Pi.add_apply,
      ← Finset.sum_add_distrib]
    congr 2
    refine Finset.sum_congr rfl fun i _ => ?_
    split_ifs <;> simp

section Torus


theorem exists_elemAbelian_two_torus {τ : Tag} {K : Type} [Field K] (h2 : (2 : K) ≠ 0) {m : ℕ}
    (J : Fin m → Fin τ.rank)
    (hJ : ∀ s : Fin m → ZMod 2, (∀ k, ∑ i, ((τ.cartan (J i) k : ℤ) : ZMod 2) * s i = 0) → s = 0) :
    ∃ V : Subgroup ↥(adjointGroup τ K), IsElemAbelian 2 V ∧ Nat.card V = 2 ^ m := by
  classical
  have hmem : ∀ t : Fin τ.rank → Kˣ,
      ((CFSG.LieType.Chevalley.torusCoordHom τ K t : torusGroup τ K) : ModGL τ K) ∈
        adjointGroup τ K := by
    intro t
    rw [coe_torusCoordHom]
    refine Subgroup.list_prod_mem _ fun x hx => ?_
    obtain ⟨i, rfl⟩ := List.mem_ofFn.1 hx
    exact torusElt_mem_adjointGroup i _
  let Φ : Multiplicative (Fin m → ZMod 2) →* ↥(adjointGroup τ K) :=
    (((torusGroup τ K).subtype.comp (CFSG.LieType.Chevalley.torusCoordHom τ K)).comp
      (torusSign K J)).codRestrict _ fun s => hmem (torusSign K J s)
  have hinj : Function.Injective Φ := by
    rw [injective_iff_map_eq_one]
    intro s hs
    have h0 : ((Φ s : adjointGroup τ K) : ModGL τ K) = 1 := by
      rw [hs]
      rfl
    have h1 : CFSG.LieType.Chevalley.torusCoordHom τ K (torusSign K J s) = 1 := Subtype.ext h0
    rw [CFSG.Timmesfeld.ExceptionalOrders.torusCoordHom_eq_one_iff] at h1
    have hk : ∀ k, ∑ i, ((τ.cartan (J i) k : ℤ) : ZMod 2) * Multiplicative.toAdd s i = 0 := by
      intro k
      have h := congrFun h1 k
      rw [CFSG.Timmesfeld.ExceptionalOrders.zpowMatrix_apply, Pi.one_apply] at h
      have e1 : ∏ l, torusSign K J s l ^ τ.cartan l k = zmodTwoSign K (Multiplicative.ofAdd
          (∑ l, ((τ.cartan l k : ℤ) : ZMod 2) *
            ∑ i, if J i = l then Multiplicative.toAdd s i else 0)) := by
        simp only [torusSign, MonoidHom.coe_mk, OneHom.coe_mk, zmodTwoSign_zpow]
        rw [ofAdd_sum, map_prod]
      have e2 : ∑ l, ((τ.cartan l k : ℤ) : ZMod 2) *
          (∑ i, if J i = l then Multiplicative.toAdd s i else 0) =
          ∑ i, ((τ.cartan (J i) k : ℤ) : ZMod 2) * Multiplicative.toAdd s i := by
        simp only [Finset.mul_sum, mul_ite, mul_zero]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [Finset.sum_ite_eq]
        simp
      rw [e1, e2] at h
      exact (zmodTwoSign_eq_one_iff h2 _).1 h
    have h0 := hJ _ hk
    exact h0
  refine ⟨Φ.range, ⟨⟨⟨fun a b => ?_⟩⟩, fun x hx => ?_⟩, ?_⟩
  · obtain ⟨x, hx⟩ := a.2
    obtain ⟨y, hy⟩ := b.2
    apply Subtype.ext
    rw [Subgroup.coe_mul, Subgroup.coe_mul, ← hx, ← hy, ← map_mul, ← map_mul, mul_comm]
  · obtain ⟨y, rfl⟩ := hx
    rw [← map_pow]
    have : y ^ 2 = 1 := by
      obtain ⟨a, rfl⟩ : ∃ a : Fin m → ZMod 2, Multiplicative.ofAdd a = y :=
        ⟨Multiplicative.toAdd y, rfl⟩
      rw [← ofAdd_nsmul, ← ofAdd_zero]
      congr 1
      funext i
      simp only [Pi.smul_apply, nsmul_eq_mul, Nat.cast_ofNat, Pi.zero_apply]
      have : (2 : ZMod 2) = 0 := rfl
      rw [this, zero_mul]
    rw [this, map_one]
  · rw [MonoidHom.range_eq_map, Subgroup.card_map_of_injective hinj, Subgroup.card_top,
      Nat.card_congr Multiplicative.toAdd, Nat.card_fun, Nat.card_zmod, Nat.card_fin]

end Torus

@[expose] def RootSpanCheck (τ : Tag) {k : ℕ} (α : Fin k → Fin τ.rank → ℤ) (i₀ : Fin τ.rank)
    (γ : Fin τ.rank → ℤ) : Prop :=
  (∀ i, RootOps.isRootB τ (α i) = true) ∧ (∀ i, 0 < height (α i)) ∧
    (∀ i j, i ≠ j → α i ≠ α j ∧ RootOps.isRootB τ (α i + α j) = false) ∧
    (∀ i, (∑ l, τ.cartan i₀ l * α i l) % 2 = 0) ∧ RootOps.isRootB τ γ = true ∧
    (∑ l, τ.cartan i₀ l * γ l) % 2 = 1

instance (τ : Tag) {k : ℕ} (α : Fin k → Fin τ.rank → ℤ) (i₀ : Fin τ.rank)
    (γ : Fin τ.rank → ℤ) : Decidable (RootSpanCheck τ α i₀ γ) := by
  unfold RootSpanCheck
  infer_instance

section RootSpan


theorem not_isRoot_nsmul_add_nsmul_of_check {τ : Tag}
    (hτ : τ = .D4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8) {k : ℕ} {α : Fin k → Fin τ.rank → ℤ}
    {i₀ : Fin τ.rank} {γ : Fin τ.rank → ℤ} (hck : RootSpanCheck τ α i₀ γ) (i j : Fin k)
    {a b : ℕ} (ha : 1 ≤ a) (hb : 1 ≤ b) : ¬ IsRoot τ (a • α i + b • α j) := by
  have hroot : ∀ i, IsRoot τ (α i) := fun i => RootOps.isRootB_iff.1 (hck.1 i)
  intro hr
  by_cases hij : i = j
  · subst hij
    rw [← add_smul] at hr
    have h := rootForm_self hτ hr
    rw [Matrix.mulVec_smul, dotProduct_smul, smul_dotProduct, rootForm_self hτ (hroot i)] at h
    simp only [nsmul_eq_mul, Nat.cast_add] at h
    have hab : (2 : ℤ) ≤ (a : ℤ) + b := by omega
    nlinarith
  · obtain ⟨hne, hsum⟩ := hck.2.2.1 i j hij
    have hne' : α i ≠ -α j := by
      intro h
      have h1 := hck.2.1 i
      have h2 := hck.2.1 j
      rw [h] at h1
      simp only [height, Pi.neg_apply, Finset.sum_neg_distrib] at h1 h2
      omega
    have hnr : ¬ IsRoot τ (α i + α j) := fun h => by
      rw [← RootOps.isRootB_iff, hsum] at h
      exact Bool.false_ne_true h
    have hcp := (commPairs_eq_of_simplyLaced hτ (hroot i) (hroot j) hne hne').2 hnr
    have hmem := (mem_commPairs_iff_of_isRoot (hroot i) (hroot j) hne hne' (a, b)).2
      ⟨by omega, by omega, hr⟩
    rw [hcp] at hmem
    exact List.not_mem_nil hmem

theorem exists_twoLocal_rootSpan {τ : Tag} (hτ : τ = .E6 ∨ τ = .E7 ∨ τ = .E8) {K : Type}
    [Field K] [Finite K] {q f : ℕ} (hq : q.Prime) [CharP K q] (hK : Nat.card K = q ^ f)
    (h2 : (2 : K) ≠ 0) {k : ℕ} {α : Fin k → Fin τ.rank → ℤ} {i₀ : Fin τ.rank}
    {γ : Fin τ.rank → ℤ} (hck : RootSpanCheck τ α i₀ γ) :
    ∃ U E : Subgroup ↥(adjointGroup τ K), IsPGroup 2 U ∧ U ≠ ⊥ ∧
      E ≤ Subgroup.normalizer (U : Set ↥(adjointGroup τ K)) ∧ IsElemAbelian q E ∧
        Nat.card E = q ^ (f * k) := by
  classical
  have hτ' : τ = .D4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8 := Or.inr hτ
  have hroot : ∀ i, IsRoot τ (α i) := fun i => RootOps.isRootB_iff.1 (hck.1 i)
  have hinj : Function.Injective α := fun i j h => by
    by_contra hij
    exact (hck.2.2.1 i j hij).1 h
  set S : Set (Fin τ.rank → ℤ) := Set.range α with hSdef
  have hS : ∀ β ∈ S, IsRoot τ β ∧ 0 < height β := by
    rintro _ ⟨i, rfl⟩
    exact ⟨hroot i, hck.2.1 i⟩
  have hclosed : ∀ β ∈ S, ∀ β' ∈ S, ∀ a b : ℕ, 1 ≤ a → 1 ≤ b → IsRoot τ (a • β + b • β') →
      a • β + b • β' ∈ S := by
    rintro _ ⟨i, rfl⟩ _ ⟨j, rfl⟩ a b ha hb hr
    exact absurd hr (not_isRoot_nsmul_add_nsmul_of_check hτ' hck i j ha hb)
  have hcard : Nat.card (rootSpan τ K S) = q ^ (f * k) := by
    rw [card_rootSpan hS hclosed, hK, Set.ncard_range_of_injective hinj, Nat.card_fin, pow_mul]
  set E₀ := rootSpan τ K S with hE₀def
  have hE₀ : E₀ = Subgroup.closure (⋃ i, Set.range (pinnedX τ K (α i))) := by
    rw [hE₀def, rootSpan, Subgroup.closure_iUnion]
    apply le_antisymm
    · refine iSup₂_le fun β hβ => ?_
      obtain ⟨i, rfl⟩ := hβ
      exact le_iSup (fun i => rootSubgroup τ K (α i)) i
    · exact iSup_le fun i => le_iSup₂ (f := fun β (_ : β ∈ S) => rootSubgroup τ K β) (α i) ⟨i, rfl⟩
  have hle : E₀ ≤ adjointGroup τ K := iSup₂_le fun β _ => rootSubgroup_le_adjointGroup β
  have hgen : ∀ x ∈ ⋃ i, Set.range (pinnedX τ K (α i)), ∀ y ∈ ⋃ i, Set.range (pinnedX τ K (α i)),
      Commute x y := by
    intro x hx y hy
    obtain ⟨i, c, rfl⟩ := Set.mem_iUnion.1 hx
    obtain ⟨j, d, rfl⟩ := Set.mem_iUnion.1 hy
    by_cases hij : i = j
    · subst hij
      change pinnedX τ K (α i) c * pinnedX τ K (α i) d = pinnedX τ K (α i) d * pinnedX τ K (α i) c
      rw [← pinnedX_add, ← pinnedX_add, add_comm]
    · obtain ⟨hne, hsum⟩ := hck.2.2.1 i j hij
      have hne' : α i ≠ -α j := by
        intro h
        have h1 := hck.2.1 i
        have h2 := hck.2.1 j
        rw [h] at h1
        simp only [height, Pi.neg_apply, Finset.sum_neg_distrib] at h1 h2
        omega
      have hnr : ¬ IsRoot τ (α i + α j) := fun h => by
        rw [← RootOps.isRootB_iff, hsum] at h
        exact Bool.false_ne_true h
      exact (simply_laced_root_commutator_unit τ hτ' (hroot i) (hroot j) hne hne').2 hnr K _
        (mem_rootSubgroup.2 ⟨c, rfl⟩) _ (mem_rootSubgroup.2 ⟨d, rfl⟩)
  have hcomm₁ : ∀ x ∈ ⋃ i, Set.range (pinnedX τ K (α i)),
      ∀ y ∈ Subgroup.closure (⋃ i, Set.range (pinnedX τ K (α i))), Commute x y := by
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
  have hpow : ∀ x ∈ E₀, x ^ q = 1 := by
    intro x hx
    rw [hE₀] at hx
    induction hx using Subgroup.closure_induction with
    | mem x hx =>
      obtain ⟨i, c, rfl⟩ := Set.mem_iUnion.1 hx
      have hn : ∀ n : ℕ, pinnedX τ K (α i) c ^ n = pinnedX τ K (α i) ((n : K) * c) := by
        intro n
        induction n with
        | zero => simp [pinnedX_zero]
        | succ n ih => rw [pow_succ, ih, ← pinnedX_add]; push_cast; ring_nf
      rw [hn, CharP.cast_eq_zero, zero_mul, pinnedX_zero]
    | one => exact one_pow q
    | mul x y hx hy hxq hyq =>
      have hxy : Commute x y := by
        rw [← hE₀] at hx hy
        exact hcomm x hx y hy
      rw [hxy.mul_pow, hxq, hyq, one_mul]
    | inv x hx hxq => rw [inv_pow, hxq, inv_one]
  set t : ModGL τ K := CFSG.RankThree.PartOne.torusWord τ K {i₀} with htdef
  have htmem : t ∈ adjointGroup τ K := CFSG.RankThree.PartOne.torusWord_mem_adjointGroup _
  have ht2 : t ^ 2 = 1 := CFSG.RankThree.PartOne.torusWord_sq _
  have ht1 : t ≠ 1 := CFSG.RankThree.PartOne.torusWord_ne_one_of_odd {i₀}
    (RootOps.isRootB_iff.1 hck.2.2.2.2.1) (by simpa using hck.2.2.2.2.2) h2
  have htc : ∀ x ∈ E₀, Commute t x := by
    intro x hx
    rw [hE₀] at hx
    induction hx using Subgroup.closure_induction with
    | mem x hx =>
      obtain ⟨i, c, rfl⟩ := Set.mem_iUnion.1 hx
      exact CFSG.RankThree.PartOne.torusWord_commute_pinnedX_of_even {i₀} (hroot i) c
        (by simpa using hck.2.2.2.1 i)
    | one => exact Commute.one_right t
    | mul x y _ _ hx hy => exact hx.mul_right hy
    | inv x _ hx => exact hx.inv_right
  set t' : ↥(adjointGroup τ K) := ⟨t, htmem⟩
  have ht'2 : t' ^ 2 = 1 := Subtype.ext (by simp [t', ht2])
  have ht'1 : t' ≠ 1 := fun h => ht1 (congrArg Subtype.val h)
  refine ⟨Subgroup.zpowers t', E₀.subgroupOf (adjointGroup τ K),
    CFSG.LocalAnalysis.GLTheoremA.S267.ModelGen.isPGroup_two_zpowers_of_sq ht'2,
    CFSG.LocalAnalysis.GLTheoremA.S267.ModelGen.zpowers_ne_bot_of_ne_one ht'1, ?_, ?_, ?_⟩
  · intro e he
    refine CFSG.LocalAnalysis.GLTheoremA.S267.ModelGen.mem_normalizer_of_forall_comm
      fun u hu => ?_
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 hu
    have hc : e * t' = t' * e := Subtype.ext (htc _ (Subgroup.mem_subgroupOf.1 he)).eq.symm
    exact (Commute.zpow_right hc n).eq
  · refine ⟨⟨⟨fun a b => Subtype.ext (Subtype.ext ?_)⟩⟩, fun x hx => Subtype.ext ?_⟩
    · exact hcomm _ (Subgroup.mem_subgroupOf.1 a.2) _ (Subgroup.mem_subgroupOf.1 b.2)
    · exact hpow _ (Subgroup.mem_subgroupOf.1 hx)
  · rw [← hcard]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv

end RootSpan

theorem le_twoLocalRank_of_witnesses {F : Type} [Group F] [Finite F] [IsSimpleGroup F]
    (hnc : ∃ a b : F, a * b ≠ b * a) {q n : ℕ} (hq : q.Prime) (hq2 : q ≠ 2)
    (hM : ¬ q ∣ Nat.card (CFSG.Open.griessHopfMultiplier F))
    (hV : ∃ V : Subgroup F, IsElemAbelian 2 V ∧ Nat.card V = 2 ^ (n + 1))
    (hW : ∃ U E : Subgroup F, IsPGroup 2 U ∧ U ≠ ⊥ ∧ E ≤ Subgroup.normalizer (U : Set F) ∧
      IsElemAbelian q E ∧ ∃ r, n ≤ r ∧ Nat.card E = q ^ r)
    {X : Type} [Group X] [Finite X] (φ : X →* F) (hφ : Function.Surjective φ) :
    n ≤ GLATwoLocalRank q X := by
  obtain ⟨V, hVe, hVc⟩ := hV
  obtain ⟨U, E, hU, hUne, hEU, hE, r, hnr, hEc⟩ := hW
  have hF : n ≤ GLATwoLocalRank q F := hnr.trans
    (CFSG.LocalAnalysis.GLTheoremA.S267.HqRank.le_twoLocalRank_of_witness hq hU hUne hEU hE hEc)
  exact CFSG.LocalAnalysis.GLTheoremA.S267.HqRank.le_twoLocalRank_of_surj hnc hq hq2 hVe hVc
    (CFSG.LocalAnalysis.GLTheoremA.S267.HqRank.twoLocalRank_cover_of_multiplier hnc hq hM hF) φ hφ

theorem le_twoLocalRank_of_torus_witness {F : Type} [Group F] [Finite F] [IsSimpleGroup F]
    (hnc : ∃ a b : F, a * b ≠ b * a) {τ : Tag} {K : Type} [Field K]
    (e : F ≃* ↥(adjointGroup τ K)) {q n : ℕ} (hq : q.Prime) (hq2 : q ≠ 2)
    (hM : ¬ q ∣ Nat.card (CFSG.Open.griessHopfMultiplier F))
    (hV : ∃ V : Subgroup ↥(adjointGroup τ K), IsElemAbelian 2 V ∧ Nat.card V = 2 ^ (n + 1))
    (hW : ∃ U E : Subgroup ↥(adjointGroup τ K), IsPGroup 2 U ∧ U ≠ ⊥ ∧
      E ≤ Subgroup.normalizer (U : Set ↥(adjointGroup τ K)) ∧ IsElemAbelian q E ∧
        ∃ r, n ≤ r ∧ Nat.card E = q ^ r)
    {X : Type} [Group X] [Finite X] (φ : X →* F) (hφ : Function.Surjective φ) :
    n ≤ GLATwoLocalRank q X := by
  obtain ⟨V, hVe, hVc⟩ := hV
  obtain ⟨U, E, hU, hUne, hEU, hE, r, hnr, hEc⟩ := hW
  obtain ⟨hU', hUne', hEU', hE', hEc'⟩ :=
    CFSG.HardMathSupport.Solomon.Coordinator.i1020_map_witness e.symm.toMonoidHom
      e.symm.injective hU hEU hE hEc
  refine le_twoLocalRank_of_witnesses hnc hq hq2 hM
    ⟨V.map e.symm.toMonoidHom, CFSG.SectionRank.isElemAbelian_map hVe _, ?_⟩
    ⟨_, _, hU', hUne' hUne, hEU', hE', r, hnr, hEc'⟩ φ hφ
  rw [Subgroup.card_map_of_injective e.symm.injective, hVc]

theorem exists_ne_comm_of_perfect {G : Type*} [Group G] [Nontrivial G]
    (hperf : commutator G = ⊤) : ∃ a b : G, a * b ≠ b * a := by
  by_contra hcon
  push Not at hcon
  have hbot : commutator G = ⊥ := by
    rw [commutator_def, Subgroup.commutator_eq_bot_iff_le_centralizer]
    intro x _
    rw [Subgroup.mem_centralizer_iff]
    intro y _
    exact hcon y x
  rw [hperf] at hbot
  exact top_ne_bot hbot

section Cat

open CFSG.Blueprint.Multiplier CFSG.LieType.SeitzGeneration CFSG.TauCetiBridge

theorem seven_le_twoLocalRank_cat_E8 (Q : TauCeti.PrimePower)
    (hv : (TauCeti.LieTypeIndex.E8 Q).Valid) (hQ2 : Q.p ≠ 2) {X : Type} [Group X] [Finite X]
    (φ : X →* (TauCeti.CFSGIndex.lie ⟨.E8 Q, hv⟩).Group) (hφ : Function.Surjective φ) :
    7 ≤ GLATwoLocalRank Q.p X := by
  obtain ⟨K, _, _, hK, hKc, ⟨e⟩⟩ := exists_catEquiv_adjointGroup Even.chevalleyBridgesAll.e8 Q hv
  obtain ⟨hfin, hsimp⟩ := CFSG.HardMathSupport.Timmesfeld.CrossChar.finite_isSimpleGroup_cat_E8 hv
  haveI := hfin
  haveI := hsimp
  have hmodel : CFSG.Models.LieModel (Cat ⟨.E8 Q, hv⟩) .E8 0 Q.p Q.exponent :=
    ⟨⟨Q.prime_p, Q.exponent_pos, rfl⟩, Or.inr ⟨rfl, ⟨.E8 Q, hv⟩, ⟨rfl, rfl⟩, ⟨MulEquiv.refl _⟩⟩⟩
  obtain ⟨hperf, ⟨eM⟩⟩ := CFSG.LieType.Steinberg.CentralExt.GriessExceptional.e8_row hmodel
  have hM : ¬ Q.p ∣ Nat.card (CFSG.Open.griessHopfMultiplier (Cat ⟨.E8 Q, hv⟩)) := by
    rw [Nat.card_congr eM.toEquiv]
    have hex : exceptionalOrders .E8 0 Q.p Q.exponent = (1, 1) := rfl
    simp only [generic, exceptional, hex, Nat.card_prod, Nat.card_congr Multiplicative.toAdd,
      Nat.card_zmod, genericOrders]
    exact Q.prime_p.not_dvd_one
  have hnc := exists_ne_comm_of_perfect hperf
  have h2 : (2 : K) ≠ 0 := Ring.two_ne_zero (by rw [ringChar.eq K Q.p]; exact hQ2)
  have hKq : Nat.card K = Q.p ^ Q.exponent := hK.trans (TauCeti.PrimePower.card_def Q)
  obtain ⟨U, E, hU, hUne, hEU, hE, hEc⟩ := exists_twoLocal_rootSpan (Or.inr (Or.inr rfl))
    Q.prime_p hKq h2 (k := 7)
    (α := ![![0, 0, 0, 0, 0, 0, 0, 1], ![0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0],
      ![1, 0, 0, 0, 0, 0, 0, 0], ![0, 1, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 1, 1],
      ![0, 0, 0, 1, 1, 1, 0, 0]]) (i₀ := 0) (γ := ![0, 0, 1, 0, 0, 0, 0, 0])
    (by unfold RootSpanCheck; decide +kernel)
  exact le_twoLocalRank_of_torus_witness hnc e Q.prime_p hQ2 hM
    (exists_elemAbelian_two_torus h2 (J := id) (by decide +kernel))
    ⟨U, E, hU, hUne, hEU, hE, Q.exponent * 7, by have := Q.exponent_pos; omega, hEc⟩ φ hφ

theorem five_le_twoLocalRank_cat_E7 (Q : TauCeti.PrimePower)
    (hv : (TauCeti.LieTypeIndex.E7 Q).Valid) (hQ2 : Q.p ≠ 2) {X : Type} [Group X] [Finite X]
    (φ : X →* (TauCeti.CFSGIndex.lie ⟨.E7 Q, hv⟩).Group) (hφ : Function.Surjective φ) :
    5 ≤ GLATwoLocalRank Q.p X := by
  obtain ⟨K, _, _, hK, hKc, ⟨e⟩⟩ := exists_catEquiv_adjointGroup Even.chevalleyBridgesAll.e7 Q hv
  obtain ⟨hfin, hsimp⟩ := CFSG.HardMathSupport.Timmesfeld.CrossChar.finite_isSimpleGroup_cat_E7 hv
  haveI := hfin
  haveI := hsimp
  have hmodel : CFSG.Models.LieModel (Cat ⟨.E7 Q, hv⟩) .E7 0 Q.p Q.exponent :=
    ⟨⟨Q.prime_p, Q.exponent_pos, rfl⟩, Or.inr ⟨rfl, ⟨.E7 Q, hv⟩, ⟨rfl, rfl⟩, ⟨MulEquiv.refl _⟩⟩⟩
  obtain ⟨hperf, ⟨eM⟩⟩ := CFSG.LieType.Steinberg.CentralExt.GriessExceptional.e7_row hmodel
  have hM : ¬ Q.p ∣ Nat.card (CFSG.Open.griessHopfMultiplier (Cat ⟨.E7 Q, hv⟩)) := by
    rw [Nat.card_congr eM.toEquiv]
    have hex : exceptionalOrders .E7 0 Q.p Q.exponent = (1, 1) := rfl
    simp only [generic, exceptional, hex, Nat.card_prod, Nat.card_congr Multiplicative.toAdd,
      Nat.card_zmod, genericOrders, mul_one]
    intro h
    have h2' : Q.p ∣ 2 := h.trans (Nat.gcd_dvd_left _ _)
    exact hQ2 ((Nat.prime_dvd_prime_iff_eq Q.prime_p Nat.prime_two).1 h2')
  have hnc := exists_ne_comm_of_perfect hperf
  have h2 : (2 : K) ≠ 0 := Ring.two_ne_zero (by rw [ringChar.eq K Q.p]; exact hQ2)
  have hKq : Nat.card K = Q.p ^ Q.exponent := hK.trans (TauCeti.PrimePower.card_def Q)
  obtain ⟨U, E, hU, hUne, hEU, hE, hEc⟩ := exists_twoLocal_rootSpan (Or.inr (Or.inl rfl))
    Q.prime_p hKq h2 (k := 5)
    (α := ![![0, 0, 0, 0, 0, 0, 1], ![0, 0, 0, 0, 1, 0, 0], ![0, 1, 0, 0, 0, 0, 0],
      ![1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 1, 1]]) (i₀ := 0) (γ := ![0, 0, 1, 0, 0, 0, 0])
    (by unfold RootSpanCheck; decide +kernel)
  exact le_twoLocalRank_of_torus_witness hnc e Q.prime_p hQ2 hM
    (exists_elemAbelian_two_torus h2 (J := Fin.castSucc) (by decide +kernel))
    ⟨U, E, hU, hUne, hEU, hE, Q.exponent * 5, by have := Q.exponent_pos; omega, hEc⟩ φ hφ

theorem five_le_twoLocalRank_cat_E6 (Q : TauCeti.PrimePower)
    (hv : (TauCeti.LieTypeIndex.E6 Q).Valid) (hQ2 : Q.p ≠ 2) {X : Type} [Group X] [Finite X]
    (φ : X →* (TauCeti.CFSGIndex.lie ⟨.E6 Q, hv⟩).Group) (hφ : Function.Surjective φ) :
    5 ≤ GLATwoLocalRank Q.p X := by
  obtain ⟨K, _, _, hK, hKc, ⟨e⟩⟩ := exists_catEquiv_adjointGroup Even.chevalleyBridgesAll.e6 Q hv
  obtain ⟨hfin, hsimp⟩ := CFSG.HardMathSupport.Timmesfeld.CrossChar.finite_isSimpleGroup_cat_E6 hv
  haveI := hfin
  haveI := hsimp
  have hmodel : CFSG.Models.LieModel (Cat ⟨.E6 Q, hv⟩) .E6 0 Q.p Q.exponent :=
    ⟨⟨Q.prime_p, Q.exponent_pos, rfl⟩, Or.inr ⟨rfl, ⟨.E6 Q, hv⟩, ⟨rfl, rfl⟩, ⟨MulEquiv.refl _⟩⟩⟩
  obtain ⟨hperf, ⟨eM⟩⟩ := CFSG.LieType.Steinberg.CentralExt.GriessExceptional.e6_row hmodel
  have hM : ¬ Q.p ∣ Nat.card (CFSG.Open.griessHopfMultiplier (Cat ⟨.E6 Q, hv⟩)) := by
    rw [Nat.card_congr eM.toEquiv]
    have hex : exceptionalOrders .E6 0 Q.p Q.exponent = (1, 1) := rfl
    simp only [generic, exceptional, hex, Nat.card_prod, Nat.card_congr Multiplicative.toAdd,
      Nat.card_zmod, genericOrders, mul_one]
    intro h
    have h3 : Q.p ∣ 3 := h.trans (Nat.gcd_dvd_left _ _)
    have hp3 : Q.p = 3 := (Nat.prime_dvd_prime_iff_eq Q.prime_p Nat.prime_three).1 h3
    have h1 : Q.p ∣ Q.p ^ Q.exponent - 1 := h.trans (Nat.gcd_dvd_right _ _)
    have h0 : Q.p ∣ Q.p ^ Q.exponent := dvd_pow_self _ Q.exponent_pos.ne'
    have hpos : 1 ≤ Q.p ^ Q.exponent := Nat.one_le_pow _ _ Q.prime_p.pos
    have := Nat.dvd_sub h0 h1
    rw [Nat.sub_sub_self hpos] at this
    exact Q.prime_p.not_dvd_one this
  have hnc := exists_ne_comm_of_perfect hperf
  have h2 : (2 : K) ≠ 0 := Ring.two_ne_zero (by rw [ringChar.eq K Q.p]; exact hQ2)
  have hKq : Nat.card K = Q.p ^ Q.exponent := hK.trans (TauCeti.PrimePower.card_def Q)
  obtain ⟨U, E, hU, hUne, hEU, hE, hEc⟩ := exists_twoLocal_rootSpan (Or.inl rfl)
    Q.prime_p hKq h2 (k := 5)
    (α := ![![0, 0, 0, 0, 0, 1], ![0, 0, 0, 1, 0, 0], ![1, 0, 0, 0, 0, 0],
      ![0, 1, 0, 1, 0, 0], ![0, 0, 0, 1, 1, 1]]) (i₀ := 0) (γ := ![0, 0, 1, 0, 0, 0])
    (by unfold RootSpanCheck; decide +kernel)
  exact le_twoLocalRank_of_torus_witness hnc e Q.prime_p hQ2 hM
    (exists_elemAbelian_two_torus h2 (J := id) (by decide +kernel))
    ⟨U, E, hU, hUne, hEU, hE, Q.exponent * 5, by have := Q.exponent_pos; omega, hEc⟩ φ hφ

end Cat

end CFSG.LocalAnalysis.GLTheoremA.S267.BadExc

end
