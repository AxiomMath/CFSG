module

public import CFSG.Goldschmidt.Steps.G2Lin
public import CFSG.Goldschmidt.StatementsG
public import CFSG.Goldschmidt.Statements
public import CFSG.Goldschmidt.StatementsH
public import CFSG.LocalAnalysis.ComponentClassification.DisjointSolvableKernels
public import CFSG.LocalAnalysis.ComponentClassification.LayerMultiplication
public import CFSG.LocalAnalysis.ComponentClassification.MinimalBCenter
public import CFSG.LocalAnalysis.ComponentClassification.OrdinaryComponentJoins
public import CFSG.LocalAnalysis.ComponentClassification.TwoLayer
public import CFSG.LocalAnalysis.ComponentClassification.UniversalOrbitBlock
public import CFSG.LocalAnalysis.LargeEvenClassification.C8FourSubgroupExhaustion
public import CFSG.LocalAnalysis.LargeEvenClassification.C8FourSubgroupRanks
public import CFSG.LocalAnalysis.LargeEvenClassification.CyclicCongruenceCut
public import CFSG.LocalAnalysis.LargeEvenClassification.CyclicFourLarge
public import CFSG.LocalAnalysis.LargeEvenClassification.CyclicTwoFourGenerators
public import CFSG.LocalAnalysis.LargeEvenClassification.MacWilliamsReduction
public import CFSG.LocalAnalysis.LargeEvenClassification.SmallCfourFullObstruction
public import CFSG.LocalAnalysis.LargeEvenClassification.SmallCfourProperSubgroups
public import CFSG.LocalAnalysis.RankTwoShapes.AlperinFusion
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.IV.theorem_3_3
public import CFSG.Walter.Bender1970.S3.Setup
public import CFSG.Walter.JRFacts
public import Certificates.Certificate1
public import Certificates.Certificate10
public import Certificates.Certificate100
public import Certificates.Certificate101
public import Certificates.Certificate102
public import Certificates.Certificate103
public import Certificates.Certificate104
public import Certificates.Certificate105
public import Certificates.Certificate106
public import Certificates.Certificate107
public import Certificates.Certificate108
public import Certificates.Certificate109
public import Certificates.Certificate11
public import Certificates.Certificate12
public import Certificates.Certificate2
public import Certificates.Certificate3
public import Certificates.Certificate4
public import Certificates.Certificate42
public import Certificates.Certificate43
public import Certificates.Certificate44
public import Certificates.Certificate5
public import Certificates.Certificate6
public import Certificates.Certificate7
public import Certificates.Certificate8
public import Certificates.Certificate9
public import Certificates.Certificate96
public import Certificates.Certificate97
public import Certificates.Certificate98
public import Certificates.Certificate99

public section

namespace CFSG.Goldschmidt.G2

open CFSG.Open
open scoped Pointwise commutatorElement

variable {G : Type*} [Group G]

section ConjSub

theorem conjSub_conjSub (a b : G) (H : Subgroup G) :
    conjSub a (conjSub b H) = conjSub (b * a) H := by
  ext x
  simp only [mem_conjSub, mul_inv_rev, mul_assoc]

theorem conjSub_one (H : Subgroup G) : conjSub (1 : G) H = H := by
  ext x
  simp [mem_conjSub]

theorem conjSub_inf (g : G) (H K : Subgroup G) :
    conjSub g (H ⊓ K) = conjSub g H ⊓ conjSub g K := by
  ext x
  simp [mem_conjSub]

theorem conjSub_eq_of_mem_normalizer {g : G} {H : Subgroup G}
    (hg : g ∈ Subgroup.normalizer (H : Set G)) : conjSub g H = H := by
  ext x
  rw [mem_conjSub]
  exact ((Subgroup.mem_normalizer_iff.mp hg) x).symm

theorem conjSub_mono (g : G) {H K : Subgroup G} (hHK : H ≤ K) : conjSub g H ≤ conjSub g K :=
  fun _ hx => mem_conjSub.mpr (hHK (mem_conjSub.mp hx))

end ConjSub

section Rep

variable (A : Subgroup G) [hA : Fact (IsElemAbelian 2 A)]

scoped instance instCommGroupA : CommGroup A :=
  @IsMulCommutative.instCommGroup _ _ hA.out.1

theorem sq_eq_one' (a : A) : a ^ 2 = 1 := Subtype.ext (by simpa using hA.out.2 a a.2)

scoped instance instModuleA : Module (ZMod 2) (Additive A) :=
  AddCommGroup.zmodModule fun x => by
    have := sq_eq_one' A (Additive.toMul x)
    apply Additive.toMul.injective
    simpa [toMul_nsmul] using this

@[expose] def sub (H : Subgroup G) : Submodule (ZMod 2) (Additive A) :=
  AddSubgroup.toZModSubmodule 2
    { carrier := {v | ((Additive.toMul v : A) : G) ∈ H}
      add_mem' := fun {a b} ha hb => by simpa using H.mul_mem ha hb
      zero_mem' := by simp
      neg_mem' := fun {a} ha => by simpa using H.inv_mem ha }

variable {A}

theorem mem_sub {H : Subgroup G} {v : Additive A} :
    v ∈ sub A H ↔ ((Additive.toMul v : A) : G) ∈ H := Iff.rfl

@[expose] def subOf (S : Submodule (ZMod 2) (Additive A)) : Subgroup G where
  carrier := {g | ∃ hg : g ∈ A, Additive.ofMul (⟨g, hg⟩ : A) ∈ S}
  mul_mem' := by
    rintro a b ⟨ha, ha'⟩ ⟨hb, hb'⟩
    exact ⟨A.mul_mem ha hb, S.add_mem ha' hb'⟩
  one_mem' := ⟨A.one_mem, S.zero_mem⟩
  inv_mem' := by
    rintro a ⟨ha, ha'⟩
    exact ⟨A.inv_mem ha, S.neg_mem ha'⟩

theorem mem_subOf {S : Submodule (ZMod 2) (Additive A)} {g : G} :
    g ∈ subOf S ↔ ∃ hg : g ∈ A, Additive.ofMul (⟨g, hg⟩ : A) ∈ S := Iff.rfl

theorem subOf_le (S : Submodule (ZMod 2) (Additive A)) : subOf S ≤ A := fun _ ⟨hg, _⟩ => hg

theorem ofMul_mem_iff {S : Submodule (ZMod 2) (Additive A)} (a : A) :
    Additive.ofMul a ∈ S ↔ (a : G) ∈ subOf S :=
  ⟨fun h => ⟨a.2, h⟩, fun ⟨_, h⟩ => h⟩

theorem mem_iff_mem_subOf {S : Submodule (ZMod 2) (Additive A)} (v : Additive A) :
    v ∈ S ↔ ((Additive.toMul v : A) : G) ∈ subOf S :=
  ⟨fun h => ⟨(Additive.toMul v : A).2, h⟩, fun ⟨_, h⟩ => h⟩

theorem card_subOf (S : Submodule (ZMod 2) (Additive A)) : Nat.card (subOf S) = Nat.card S :=
  Nat.card_congr
    { toFun := fun g => ⟨Additive.ofMul ⟨g.1, g.2.1⟩, g.2.2⟩
      invFun := fun v => ⟨((Additive.toMul v.1 : A) : G), (Additive.toMul v.1 : A).2, v.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }

theorem card_sub (H : Subgroup G) : Nat.card (sub A H) = Nat.card (A ⊓ H : Subgroup G) :=
  Nat.card_congr
    { toFun := fun v => ⟨((Additive.toMul v.1 : A) : G), (Additive.toMul v.1 : A).2, v.2⟩
      invFun := fun x => ⟨Additive.ofMul ⟨x, x.2.1⟩, x.2.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }

omit hA in
theorem card_additive : Nat.card (Additive A) = Nat.card A :=
  Nat.card_congr Additive.toMul

theorem sub_eq_sub_iff {H K : Subgroup G} : sub A H = sub A K ↔ A ⊓ H = A ⊓ K := by
  constructor
  · intro h
    ext x
    simp only [Subgroup.mem_inf]
    constructor
    · rintro ⟨hxA, hx⟩
      refine ⟨hxA, ?_⟩
      have := (SetLike.ext_iff.mp h (Additive.ofMul ⟨x, hxA⟩)).mp hx
      simpa [mem_sub] using this
    · rintro ⟨hxA, hx⟩
      refine ⟨hxA, ?_⟩
      have := (SetLike.ext_iff.mp h (Additive.ofMul ⟨x, hxA⟩)).mpr hx
      simpa [mem_sub] using this
  · intro h
    ext v
    rw [mem_sub, mem_sub]
    have := SetLike.ext_iff.mp h ((Additive.toMul v : A) : G)
    simp only [Subgroup.mem_inf] at this
    exact ⟨fun hv => (this.mp ⟨(Additive.toMul v : A).2, hv⟩).2,
      fun hv => (this.mpr ⟨(Additive.toMul v : A).2, hv⟩).2⟩

theorem sub_eq_bot_iff {H : Subgroup G} : sub A H = ⊥ ↔ A ⊓ H = ⊥ := by
  have : sub A (⊥ : Subgroup G) = ⊥ := by
    ext v
    rw [mem_sub, Subgroup.mem_bot, Submodule.mem_bot]
    constructor
    · intro hv
      apply Additive.toMul.injective
      exact Subtype.ext hv
    · rintro rfl
      rfl
  rw [← this, sub_eq_sub_iff, inf_bot_eq]

theorem sub_inf (H K : Subgroup G) : sub A (H ⊓ K) = sub A H ⊓ sub A K := by
  ext v
  simp [mem_sub, Submodule.mem_inf]

theorem sub_inf_self (H : Subgroup G) : sub A (A ⊓ H) = sub A H := by
  ext v
  simp only [mem_sub, Subgroup.mem_inf, and_iff_right_iff_imp]
  exact fun _ => (Additive.toMul v : A).2

variable {X : Subgroup G}

@[expose] def conjAut (hX : X ≤ Subgroup.normalizer (A : Set G)) (x : X) : A ≃* A where
  toFun a := ⟨(x : G) * a * (x : G)⁻¹, (Subgroup.mem_normalizer_iff.mp (hX x.2) a).mp a.2⟩
  invFun a := ⟨(x : G)⁻¹ * a * (x : G), by
    simpa using (Subgroup.mem_normalizer_iff.mp (hX (X.inv_mem x.2)) a).mp a.2⟩
  left_inv a := Subtype.ext (by simp [mul_assoc])
  right_inv a := Subtype.ext (by simp [mul_assoc])
  map_mul' a b := Subtype.ext (by simp [mul_assoc])

@[expose] def conjRep (hX : X ≤ Subgroup.normalizer (A : Set G)) :
    X →* (Additive A ≃ₗ[ZMod 2] Additive A) where
  toFun x := AddEquiv.toLinearEquiv (MulEquiv.toAdditive (conjAut hX x))
    (fun c v => ZMod.map_smul (MulEquiv.toAdditive (conjAut hX x)) c v)
  map_one' := LinearEquiv.ext fun v => by
    apply Additive.toMul.injective
    apply Subtype.ext
    simp [conjAut]
  map_mul' a b := LinearEquiv.ext fun v => by
    apply Additive.toMul.injective
    apply Subtype.ext
    simp [conjAut, mul_assoc]

variable (hX : X ≤ Subgroup.normalizer (A : Set G))

theorem conjRep_apply (x : X) (v : Additive A) :
    ((Additive.toMul (conjRep hX x v) : A) : G) = (x : G) * (Additive.toMul v : A) * (x : G)⁻¹ :=
  rfl

theorem conjRep_inv_apply (x : X) (v : Additive A) :
    ((Additive.toMul ((conjRep hX x)⁻¹ v) : A) : G) =
      (x : G)⁻¹ * (Additive.toMul v : A) * (x : G) := by
  rw [← map_inv, conjRep_apply]
  simp

theorem conjRep_smul_sub (x : X) (H : Subgroup G) :
    conjRep hX x • sub A H = sub A (conjSub (x : G)⁻¹ H) := by
  ext v
  rw [CFSG.QuasithinUnique.ONan.mem_smul_iff, mem_sub, mem_sub, conjRep_inv_apply, mem_conjSub,
    inv_inv]

theorem ker_conjRep : (conjRep hX).ker = (X ⊓ Subgroup.centralizer (A : Set G)).subgroupOf X := by
  ext x
  rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, Subgroup.mem_inf]
  simp only [x.2, true_and]
  constructor
  · intro h1
    rw [Subgroup.mem_centralizer_iff]
    intro a ha
    have := congrArg (fun f : Additive A ≃ₗ[ZMod 2] Additive A =>
      ((Additive.toMul (f (Additive.ofMul ⟨a, ha⟩)) : A) : G)) h1
    simp only [conjRep_apply, LinearEquiv.coe_one, id, toMul_ofMul] at this
    calc a * (x : G) = (x : G) * a * (x : G)⁻¹ * x := by rw [this]
      _ = x * a := by group
  · intro h1
    apply LinearEquiv.ext
    intro v
    apply Additive.toMul.injective
    apply Subtype.ext
    rw [conjRep_apply, LinearEquiv.coe_one, id]
    have := Subgroup.mem_centralizer_iff.mp h1 _ (Additive.toMul v : A).2
    rw [← this]
    group

theorem conjRep_eq_one_iff (x : X) :
    conjRep hX x = 1 ↔ (x : G) ∈ Subgroup.centralizer (A : Set G) := by
  rw [← MonoidHom.mem_ker, ker_conjRep, Subgroup.mem_subgroupOf, Subgroup.mem_inf]
  simp [x.2]

theorem fixSp_conjRep (y : X) :
    fixSp (conjRep hX y) = sub A (Subgroup.centralizer ({(y : G)} : Set G)) := by
  ext v
  rw [mem_fixSp, mem_sub, Subgroup.mem_centralizer_singleton_iff]
  constructor
  · intro h1
    have := congrArg (fun w => ((Additive.toMul w : A) : G)) h1
    simp only [conjRep_apply] at this
    calc ((Additive.toMul v : A) : G) * y =
          (y : G) * (Additive.toMul v : A) * (y : G)⁻¹ * y := by rw [this]
      _ = (y : G) * (Additive.toMul v : A) := by group
  · intro h1
    apply Additive.toMul.injective
    apply Subtype.ext
    rw [conjRep_apply, ← h1]
    group

theorem comSp_le_sub (y : X) :
    comSp (conjRep hX y) ≤ sub A ⁅A, Subgroup.zpowers (y : G)⁆ := by
  intro v hv
  obtain ⟨u, rfl⟩ := mem_comSp.mp hv
  rw [mem_sub, sub_eq_add, toMul_add, Subgroup.coe_mul, conjRep_apply]
  have h1 : ⁅(y : G), ((Additive.toMul u : A) : G)⁆ ∈ ⁅Subgroup.zpowers (y : G), A⁆ :=
    Subgroup.commutator_mem_commutator (Subgroup.mem_zpowers _) (Additive.toMul u : A).2
  rw [Subgroup.commutator_comm] at h1
  have hc : ⁅(y : G), ((Additive.toMul u : A) : G)⁆ =
      (y : G) * (Additive.toMul u : A) * (y : G)⁻¹ * (Additive.toMul u : A) := by
    rw [commutatorElement_def]
    congr 1
    have := sq_eq_one' A (Additive.toMul u)
    rw [eq_comm, ← mul_eq_one_iff_eq_inv, ← pow_two]
    exact congrArg Subtype.val this
  rw [hc] at h1
  exact h1

theorem conjRep_pow (y : X) (k : ℕ) : conjRep hX (y ^ k) = conjRep hX y ^ k := map_pow _ _ _

end Rep

section ONan

variable {A X : Subgroup G} {y : G} (h : ONanHyp A X y) [Fact (IsElemAbelian 2 A)]
include h

theorem linHyp_of_onanHyp [Finite G] : LinHyp (conjRep h.le).range (conjRep h.le ⟨y, h.mem⟩) where
  mem := ⟨⟨y, h.mem⟩, rfl⟩
  odd := by
    have h1 : orderOf (conjRep h.le ⟨y, h.mem⟩) ∣ orderOf (⟨y, h.mem⟩ : X) := orderOf_map_dvd _ _
    rw [Subgroup.orderOf_mk] at h1
    exact Odd.of_dvd_nat h.odd h1
  ne_one := by
    rw [Ne, conjRep_eq_one_iff]
    exact h.not_mem
  fixSp_ne_bot := by
    rw [fixSp_conjRep, Ne, sub_eq_bot_iff]
    exact h.ne_bot
  trans := by
    intro b hb c hc hb0 hc0
    have hb' := comSp_le_sub h.le _ hb
    have hc' := comSp_le_sub h.le _ hc
    rw [mem_sub] at hb' hc'
    have hb1 : ((Additive.toMul b : A) : G) ≠ 1 := fun h1 => hb0 (by
      apply Additive.toMul.injective
      exact Subtype.ext h1)
    have hc1 : ((Additive.toMul c : A) : G) ≠ 1 := fun h1 => hc0 (by
      apply Additive.toMul.injective
      exact Subtype.ext h1)
    obtain ⟨k, hk⟩ := h.trans _ hb' _ hc' hb1 hc1
    have h1 : (conjRep h.le ⟨y, h.mem⟩ ^ k)⁻¹ b = c := by
      apply Additive.toMul.injective
      apply Subtype.ext
      rw [← conjRep_pow, conjRep_inv_apply]
      simpa using hk
    obtain ⟨k', hk'⟩ := exists_pow_eq_of_mem_zpowers
      (Subgroup.inv_mem _ (Subgroup.npow_mem_zpowers (conjRep h.le ⟨y, h.mem⟩) k))
    exact ⟨k', by rw [hk']; exact h1⟩
  ti := by
    rintro _ ⟨x, rfl⟩ hne
    rw [fixSp_conjRep, conjRep_smul_sub] at hne ⊢
    rw [← sub_inf, sub_eq_bot_iff]
    rw [Ne, sub_eq_sub_iff] at hne
    have hxA : conjSub (x : G)⁻¹ A = A := conjSub_eq_of_mem_normalizer (h.le (X.inv_mem x.2))
    have hne' : conjSub (x : G)⁻¹ (A ⊓ Subgroup.centralizer ({y} : Set G)) ≠
        A ⊓ Subgroup.centralizer ({y} : Set G) := by
      rwa [conjSub_inf, hxA]
    have := h.ti _ (X.inv_mem x.2) hne'
    rw [conjSub_inf, hxA] at this
    rw [← this]
    ext g
    simp only [Subgroup.mem_inf]
    tauto

theorem irreducible_of_onanHyp : ∀ S : Submodule (ZMod 2) (Additive A),
    (∀ x ∈ (conjRep h.le).range, ∀ v ∈ S, x v ∈ S) → S = ⊥ ∨ S = ⊤ := by
  intro S hS
  have hconj : ∀ x ∈ X, ∀ g ∈ subOf S, x * g * x⁻¹ ∈ subOf S := by
    rintro x hx g ⟨hgA, hgS⟩
    have := hS _ ⟨⟨x, hx⟩, rfl⟩ _ hgS
    exact ⟨_, this⟩
  have hnorm : X ≤ Subgroup.normalizer (subOf S : Set G) := by
    intro x hx
    rw [Subgroup.mem_normalizer_iff]
    intro g
    refine ⟨hconj x hx g, fun hg => ?_⟩
    have := hconj x⁻¹ (X.inv_mem hx) _ hg
    simpa [mul_assoc] using this
  rcases h.irreducible (subOf S) (subOf_le S) hnorm with h0 | h0
  · left
    rw [Submodule.eq_bot_iff]
    intro v hv
    have := (mem_iff_mem_subOf v).mp hv
    rw [h0, Subgroup.mem_bot] at this
    apply Additive.toMul.injective
    exact Subtype.ext this
  · right
    rw [Submodule.eq_top_iff']
    intro v
    rw [mem_iff_mem_subOf, h0]
    exact (Additive.toMul v : A).2

theorem transitive_iff_of_onanHyp :
    (∀ b ∈ A, ∀ c ∈ A, b ≠ 1 → c ≠ 1 → ∃ x ∈ X, x⁻¹ * b * x = c) ↔
      ∀ v w : Additive A, v ≠ 0 → w ≠ 0 → ∃ x ∈ (conjRep h.le).range, x v = w := by
  constructor
  · intro ht v w hv hw
    have hv1 : ((Additive.toMul v : A) : G) ≠ 1 := fun h1 => hv (by
      apply Additive.toMul.injective
      exact Subtype.ext h1)
    have hw1 : ((Additive.toMul w : A) : G) ≠ 1 := fun h1 => hw (by
      apply Additive.toMul.injective
      exact Subtype.ext h1)
    obtain ⟨x, hx, hxvw⟩ := ht _ (Additive.toMul v : A).2 _ (Additive.toMul w : A).2 hv1 hw1
    refine ⟨(conjRep h.le ⟨x, hx⟩)⁻¹, ⟨⟨x, hx⟩⁻¹, map_inv (conjRep h.le) ⟨x, hx⟩⟩, ?_⟩
    apply Additive.toMul.injective
    apply Subtype.ext
    rw [conjRep_inv_apply]
    exact hxvw
  · intro ht b hb c hc hb1 hc1
    have hb0 : Additive.ofMul (⟨b, hb⟩ : A) ≠ 0 := fun h0 =>
      hb1 (congrArg Subtype.val (ofMul_eq_zero.mp h0))
    have hc0 : Additive.ofMul (⟨c, hc⟩ : A) ≠ 0 := fun h0 =>
      hc1 (congrArg Subtype.val (ofMul_eq_zero.mp h0))
    obtain ⟨_, ⟨x, rfl⟩, hxbc⟩ := ht _ _ hb0 hc0
    refine ⟨(x : G)⁻¹, X.inv_mem x.2, ?_⟩
    have := congrArg (fun v => ((Additive.toMul v : A) : G)) hxbc
    simp only [conjRep_apply] at this
    simpa using this

omit [Fact (IsElemAbelian 2 A)] in
theorem exists_zpow_of_mem_sup {g : G}
    (hg : g ∈ Subgroup.zpowers y ⊔ Subgroup.centralizer (A : Set G)) :
    ∃ j : ℤ, (y ^ j)⁻¹ * g ∈ Subgroup.centralizer (A : Set G) := by
  have hyN : ∀ j : ℤ, ∀ c ∈ Subgroup.centralizer (A : Set G),
      y ^ j * c * (y ^ j)⁻¹ ∈ Subgroup.centralizer (A : Set G) := by
    intro j c hc
    have hyj : y ^ j ∈ Subgroup.normalizer (A : Set G) := Subgroup.zpow_mem _ (h.le h.mem) j
    rw [Subgroup.mem_centralizer_iff]
    intro a ha
    have ha' : (y ^ j)⁻¹ * a * y ^ j ∈ A := by
      have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hyj) a).mp ha
      simpa using this
    have := Subgroup.mem_centralizer_iff.mp hc _ ha'
    calc a * (y ^ j * c * (y ^ j)⁻¹) = y ^ j * (((y ^ j)⁻¹ * a * y ^ j) * c) * (y ^ j)⁻¹ := by
          group
      _ = y ^ j * (c * ((y ^ j)⁻¹ * a * y ^ j)) * (y ^ j)⁻¹ := by rw [this]
      _ = y ^ j * c * (y ^ j)⁻¹ * a := by group
  let T : Subgroup G :=
    { carrier := {g | ∃ j : ℤ, (y ^ j)⁻¹ * g ∈ Subgroup.centralizer (A : Set G)}
      mul_mem' := by
        rintro a b ⟨j, hj⟩ ⟨j', hj'⟩
        refine ⟨j + j', ?_⟩
        have h1 := hyN (-j') _ hj
        have h2 := Subgroup.mul_mem _ h1 hj'
        convert h2 using 1
        rw [zpow_add, zpow_neg]
        group
      one_mem' := ⟨0, by simp⟩
      inv_mem' := by
        rintro a ⟨j, hj⟩
        refine ⟨-j, ?_⟩
        have h1 := hyN j _ (Subgroup.inv_mem _ hj)
        convert h1 using 1
        rw [zpow_neg]
        group }
  have hle : Subgroup.zpowers y ⊔ Subgroup.centralizer (A : Set G) ≤ T := by
    refine sup_le (Subgroup.zpowers_le.mpr ⟨1, by simp⟩) fun c hc => ⟨0, ?_⟩
    simpa using hc
  exact hle hg

theorem normalizes_of_onanHyp
    (hN : ∀ x ∈ X, conjSub x (A ⊓ Subgroup.centralizer ({y} : Set G)) =
        A ⊓ Subgroup.centralizer ({y} : Set G) →
      x⁻¹ * y * x ∈ Subgroup.zpowers y ⊔ Subgroup.centralizer (A : Set G)) :
    ∀ x ∈ (conjRep h.le).range, x • fixSp (conjRep h.le ⟨y, h.mem⟩) =
        fixSp (conjRep h.le ⟨y, h.mem⟩) →
      x * conjRep h.le ⟨y, h.mem⟩ * x⁻¹ ∈ Subgroup.zpowers (conjRep h.le ⟨y, h.mem⟩) := by
  rintro _ ⟨x, rfl⟩ hx
  rw [fixSp_conjRep, conjRep_smul_sub, sub_eq_sub_iff] at hx
  have hxA : conjSub (x : G)⁻¹ A = A := conjSub_eq_of_mem_normalizer (h.le (X.inv_mem x.2))
  have hW : conjSub (x : G)⁻¹ (A ⊓ Subgroup.centralizer ({y} : Set G)) =
      A ⊓ Subgroup.centralizer ({y} : Set G) := by
    rwa [conjSub_inf, hxA]
  have hmem := hN _ (X.inv_mem x.2) hW
  rw [inv_inv] at hmem
  obtain ⟨j, hj⟩ := exists_zpow_of_mem_sup h hmem
  set g : X := x * ⟨y, h.mem⟩ * x⁻¹ with hg
  have hyj : (⟨y, h.mem⟩ : X) ^ j * ((⟨y, h.mem⟩ : X) ^ j)⁻¹ * g = g := by group
  have hc : conjRep h.le (((⟨y, h.mem⟩ : X) ^ j)⁻¹ * g) = 1 := by
    rw [conjRep_eq_one_iff]
    simpa [hg] using hj
  have : conjRep h.le g = conjRep h.le ⟨y, h.mem⟩ ^ j := by
    rw [← hyj, mul_assoc, map_mul, hc, mul_one, map_zpow]
  rw [← map_inv, ← map_mul, ← map_mul, ← hg, this]
  exact Subgroup.zpow_mem_zpowers _ j

theorem index_ne_two_of_onanHyp
    (hI : ∀ X₀ : Subgroup G, X₀ ≤ X → X ⊓ Subgroup.centralizer (A : Set G) ≤ X₀ →
      (X₀.subgroupOf X).index ≠ 2) :
    ∀ X₀ : Subgroup (Additive A ≃ₗ[ZMod 2] Additive A), X₀ ≤ (conjRep h.le).range →
      (X₀.subgroupOf (conjRep h.le).range).index ≠ 2 := by
  intro X₀ _ hidx
  apply hI ((X₀.comap (conjRep h.le)).map X.subtype) (Subgroup.map_subtype_le _)
  · intro c hc
    obtain ⟨hcX, hcA⟩ := Subgroup.mem_inf.mp hc
    refine ⟨⟨c, hcX⟩, ?_, rfl⟩
    show conjRep h.le ⟨c, hcX⟩ ∈ X₀
    rw [(conjRep_eq_one_iff h.le ⟨c, hcX⟩).mpr hcA]
    exact X₀.one_mem
  · have hsub : ((X₀.comap (conjRep h.le)).map X.subtype).subgroupOf X =
        X₀.comap (conjRep h.le) :=
      Subgroup.comap_map_eq_self_of_injective X.subtype_injective _
    rw [hsub]
    have hcomap : X₀.comap (conjRep h.le) =
        (X₀.subgroupOf (conjRep h.le).range).comap (conjRep h.le).rangeRestrict := by
      ext x
      simp [Subgroup.mem_subgroupOf]
    rw [hcomap, Subgroup.index_comap_of_surjective _ (conjRep h.le).rangeRestrict_surjective]
    exact hidx

theorem index_eq_card_of_onanHyp :
    ((X ⊓ Subgroup.centralizer (A : Set G)).subgroupOf X).index =
      Nat.card (conjRep h.le).range := by
  rw [← ker_conjRep, Subgroup.index_ker]

theorem exists_commutator_of_onanHyp {x₁ x₂ : Additive A ≃ₗ[ZMod 2] Additive A}
    (hx₁ : x₁ ∈ (conjRep h.le).range) (hx₂ : x₂ ∈ (conjRep h.le).range)
    (hne : x₁ * x₂ ≠ x₂ * x₁) :
    ∃ g₁ ∈ X, ∃ g₂ ∈ X, g₁ * g₂ * g₁⁻¹ * g₂⁻¹ ∉ Subgroup.centralizer (A : Set G) := by
  obtain ⟨g₁, rfl⟩ := hx₁
  obtain ⟨g₂, rfl⟩ := hx₂
  refine ⟨g₁, g₁.2, g₂, g₂.2, fun hc => hne ?_⟩
  have h1 := (conjRep_eq_one_iff h.le (g₁ * g₂ * g₁⁻¹ * g₂⁻¹)).mpr (by simpa using hc)
  simp only [map_mul, map_inv] at h1
  have h2 : conjRep h.le g₁ * conjRep h.le g₂ =
      (conjRep h.le g₁ * conjRep h.le g₂ * (conjRep h.le g₁)⁻¹ * (conjRep h.le g₂)⁻¹) *
        (conjRep h.le g₂ * conjRep h.le g₁) := by group
  rw [h2, h1, one_mul]

end ONan

end CFSG.Goldschmidt.G2
