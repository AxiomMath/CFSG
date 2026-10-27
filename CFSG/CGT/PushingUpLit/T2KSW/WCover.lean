module

public import CFSG.CGT.PushingUpLit.T2KSW.RD

public section

namespace CFSG.CGT.PushingUpLit.T2KSW

open CFSG CFSG.RankThree.PartOne CFSG.ShultStronglyClosedTI CFSG.CGT.PushingUpLit
  CFSG.CGT.PushingUpLit.T2K CFSG.Quasithin.JonesParshall
open scoped commutatorElement

namespace Aux

open Matrix


theorem eq_zero_or_one_or_of_card_four {F : Type} [Field F] [Finite F] [CharP F 2]
    (hcard : Nat.card F = 4) {ω : F} (h0 : ω ≠ 0) (h1 : ω ≠ 1) (x : F) :
    x = 0 ∨ x = 1 ∨ x = ω ∨ x = 1 + ω := by
  have : Fintype F := Fintype.ofFinite F
  have hc : Fintype.card F = 4 := by rw [← Nat.card_eq_fintype_card]; exact hcard
  have h2 : (2 : F) = 0 := CharP.cast_eq_zero F 2
  have hpow : ∀ y : F, y ^ 4 = y := fun y => by
    have := FiniteField.pow_card y
    rwa [hc] at this
  have hne : ∀ y : F, y ≠ 1 → y + 1 ≠ 0 := fun y hy hy0 => hy (by
    have := eq_neg_of_add_eq_zero_left hy0
    rwa [CharTwo.neg_eq] at this)
  have hω : ω ^ 2 + ω + 1 = 0 := by
    have h : ω * ((ω + 1) * (ω ^ 2 + ω + 1)) = 0 := by
      linear_combination hpow ω + (ω ^ 3 + ω ^ 2 + ω) * h2
    rcases mul_eq_zero.1 h with h | h
    · exact absurd h h0
    rcases mul_eq_zero.1 h with h | h
    · exact absurd h (hne ω h1)
    · exact h
  have h : x * ((x + 1) * ((x + ω) * (x + ω + 1))) = 0 := by
    linear_combination hpow x + (x ^ 3 + x ^ 2 + x + x * (x + 1) * (ω * x - 1)) * h2 +
      (x * (x + 1)) * hω
  rcases mul_eq_zero.1 h with h | h
  · exact Or.inl h
  rcases mul_eq_zero.1 h with h | h
  · refine Or.inr (Or.inl ?_)
    have := eq_neg_of_add_eq_zero_left h
    rwa [CharTwo.neg_eq] at this
  rcases mul_eq_zero.1 h with h | h
  · refine Or.inr (Or.inr (Or.inl ?_))
    have := eq_neg_of_add_eq_zero_left h
    rwa [CharTwo.neg_eq] at this
  · refine Or.inr (Or.inr (Or.inr ?_))
    have h' : x + (ω + 1) = 0 := by rw [← add_assoc]; exact h
    have := eq_neg_of_add_eq_zero_left h'
    rwa [CharTwo.neg_eq, add_comm] at this

@[expose] def wMat (F : Type) [Field F] [CharP F 2] : SL2 F :=
  ⟨!![0, 1; 1, 0], by
    rw [det_fin_two_of]
    have : (2 : F) = 0 := CharP.cast_eq_zero F 2
    linear_combination (-1 : F) * this⟩

theorem wMat_coe (F : Type) [Field F] [CharP F 2] :
    ((wMat F : SL2 F) : Matrix (Fin 2) (Fin 2) F) = !![0, 1; 1, 0] := rfl

theorem wMat_mul_self (F : Type) [Field F] [CharP F 2] : wMat F * wMat F = 1 := by
  apply Subtype.ext
  change !![(0 : F), 1; 1, 0] * !![0, 1; 1, 0] = 1
  rw [mul_fin_two]
  simp [one_fin_two]

theorem wMat_ne_one (F : Type) [Field F] [CharP F 2] : wMat F ≠ 1 := by
  intro h
  have := congrArg (fun g : SL2 F => (g : Matrix (Fin 2) (Fin 2) F) 0 0) h
  simp [wMat_coe] at this

theorem tMat_pow_three {F : Type} [Field F] {c : F} (hc : c ≠ 0) (h3 : c ^ 3 = 1) :
    tMat c hc ^ 3 = 1 := by
  apply Subtype.ext
  have e : ((tMat c hc ^ 3 : SL2 F) : Matrix (Fin 2) (Fin 2) F) = !![c ^ 3, 0; 0, (c⁻¹) ^ 3] := by
    simp only [pow_succ, pow_zero, one_mul, Matrix.SpecialLinearGroup.coe_mul, tMat_coe,
      mul_fin_two]
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  rw [e, h3]
  change _ = (1 : Matrix (Fin 2) (Fin 2) F)
  rw [one_fin_two]
  congr 2
  rw [inv_pow, h3, inv_one]

theorem wMat_mul_tMat_mul_wMat (F : Type) [Field F] [CharP F 2] {c : F} (hc : c ≠ 0) :
    wMat F * tMat c hc * wMat F = (tMat c hc)⁻¹ := by
  rw [eq_inv_iff_mul_eq_one]
  apply Subtype.ext
  change !![(0 : F), 1; 1, 0] * !![c, 0; 0, c⁻¹] * !![0, 1; 1, 0] * !![c, 0; 0, c⁻¹] = 1
  rw [mul_fin_two, mul_fin_two, mul_fin_two, one_fin_two]
  have h1 : c⁻¹ * c = 1 := inv_mul_cancel₀ hc
  have h2 : c * c⁻¹ = 1 := mul_inv_cancel₀ hc
  ext i j
  fin_cases i <;> fin_cases j <;> simp [h1, h2]

theorem exists_fixed_of_three {α : Type*} [Finite α] (σ : α → α) (hσ : ∀ x, σ (σ (σ x)) = x)
    (hα : ¬ 3 ∣ Nat.card α) : ∃ x, σ x = x := by
  classical
  have : Fintype α := Fintype.ofFinite α
  have : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  let f : Function.End α := σ
  have hf : f ^ 3 ^ 1 = 1 := by
    funext x
    show σ (σ (σ x)) = x
    exact hσ x
  have hmod := Equiv.Perm.card_fixedPoints_modEq (p := 3) (n := 1) hf
  by_contra hne
  push Not at hne
  have h0 : Fintype.card f.fixedPoints = 0 := by
    rw [Fintype.card_eq_zero_iff]
    exact ⟨fun ⟨x, hx⟩ => hne x hx⟩
  rw [h0] at hmod
  exact hα (by rw [Nat.card_eq_fintype_card]; exact (Nat.modEq_zero_iff_dvd.1 hmod))

theorem exists_fixed_in_coset {G : Type} [Group G] [Finite G] {X : Subgroup G} (hX : IsPGroup 2 X)
    (x₀ : G) (σ : G → G) (hσ : ∀ x, σ (σ (σ x)) = x)
    (hmaps : ∀ x, x₀⁻¹ * x ∈ X → x₀⁻¹ * σ x ∈ X) : ∃ x, x₀⁻¹ * x ∈ X ∧ σ x = x := by
  classical
  let α := {x : G // x₀⁻¹ * x ∈ X}
  let τ : α → α := fun x => ⟨σ x, hmaps x x.2⟩
  have hτ : ∀ x, τ (τ (τ x)) = x := fun x => Subtype.ext (hσ x)
  have hcard : Nat.card α = Nat.card X := by
    refine Nat.card_congr
      { toFun := fun x => ⟨x₀⁻¹ * x, x.2⟩
        invFun := fun w => ⟨x₀ * w, by simp⟩
        left_inv := fun x => Subtype.ext (by simp)
        right_inv := fun w => Subtype.ext (by simp) }
  have hα : ¬ 3 ∣ Nat.card α := by
    obtain ⟨k, hk⟩ := (IsPGroup.iff_card (p := 2)).1 hX
    rw [hcard, hk]
    intro h3
    have := Nat.Prime.dvd_of_dvd_pow (by norm_num : Nat.Prime 3) h3
    omega
  obtain ⟨x, hx⟩ := exists_fixed_of_three τ hτ hα
  exact ⟨x, x.2, congrArg Subtype.val hx⟩

theorem exists_ne_zero_one {F : Type} [Field F] [Finite F] (hcard : Nat.card F = 4) :
    ∃ ω : F, ω ≠ 0 ∧ ω ≠ 1 := by
  classical
  by_contra hcon
  push Not at hcon
  have : Fintype F := Fintype.ofFinite F
  have h2 : Fintype.card F ≤ Fintype.card Bool := by
    refine Fintype.card_le_of_injective (fun x : F => decide (x = 0)) ?_
    intro x y hxy
    have hx := hcon x
    have hy := hcon y
    by_cases hx0 : x = 0
    · by_cases hy0 : y = 0
      · rw [hx0, hy0]
      · simp [hx0, hy0] at hxy
    · by_cases hy0 : y = 0
      · simp [hx0, hy0] at hxy
      · rw [hx hx0, hy hy0]
  rw [← Nat.card_eq_fintype_card, hcard] at h2
  simp at h2


end Aux

section Cover

variable {K : Type} [Field K] [Finite K] [CharP K 2] {E : Type} [Group E]
  {η : E →* Matrix.SpecialLinearGroup (Fin 2) K}

theorem cover_ker_eq_of_ne_one [Finite E] [Group.IsPerfect E] (hcard : Nat.card K = 4)
    (hsurj : Function.Surjective η) (hcentral : η.ker ≤ Subgroup.center E)
    (hp : IsPGroup 2 η.ker) {a b : E} (ha : a ∈ η.ker) (hb : b ∈ η.ker) (ha1 : a ≠ 1)
    (hb1 : b ≠ 1) : a = b := by
  classical
  have hcard' : Nat.card K = 2 ^ 2 := by rw [hcard]; norm_num
  set κ : K → K → E := fun x y => (linearCoverCommutator η hsurj x y : E) with hκ
  have κ0l : ∀ t, κ 0 t = 1 := fun t => cover_commutator_zero_left hsurj hcentral t
  have κ0r : ∀ s, κ s 0 = 1 := fun s => cover_commutator_zero_right hsurj hcentral s
  have κsq : ∀ s t, κ s t * κ s t = 1 := fun s t => by
    rw [← pow_two]
    exact cover_commutator_sq hsurj hcentral s t
  have κal : ∀ x x' y, κ (x + x') y = κ x y * κ x' y := fun x x' y => by
    have := congrArg (fun c : η.ker => (c : E))
      (linearCoverCommutator_add_left η hsurj hcentral x x' y)
    simpa using this
  have κar : ∀ x y y', κ x (y + y') = κ x y * κ x y' := fun x y y' => by
    have := congrArg (fun c : η.ker => (c : E))
      (linearCoverCommutator_add_right η hsurj hcentral x y y')
    simpa using this
  have κdiag : ∀ x, κ x x = 1 := fun x => by
    have := linearCoverCommutator_eq_of_lifts η hsurj hcentral
      (a := linearCoverRootLift η hsurj x) (b := linearCoverRootLift η hsurj x) (x := x) (y := x)
      (linearCoverRootLift_image η hsurj x) (linearCoverRootLift_image η hsurj x)
    rw [hκ]
    simp only
    rw [this, commutatorElement_self]
  have κcomm : ∀ s t, κ s t * κ t s = 1 := fun s t => by
    have h1 := κdiag (s + t)
    rw [κal, κar, κar, κdiag, κdiag, one_mul, mul_one] at h1
    exact h1
  have κsymm : ∀ s t, κ t s = κ s t := fun s t =>
    mul_left_cancel (a := κ s t) ((κcomm s t).trans (κsq s t).symm)
  obtain ⟨ω, hω0, hω1⟩ := Aux.exists_ne_zero_one hcard
  set c : E := κ 1 ω with hc
  have hcc : c * c = 1 := κsq 1 ω
  have hω1' : κ ω 1 = c := κsymm 1 ω
  have hall : ∀ s t, κ s t = 1 ∨ κ s t = c := by
    intro s t
    rcases Aux.eq_zero_or_one_or_of_card_four hcard hω0 hω1 s with rfl | rfl | rfl | rfl <;>
    rcases Aux.eq_zero_or_one_or_of_card_four hcard hω0 hω1 t with rfl | rfl | rfl | rfl <;>
    simp [κ0l, κ0r, κdiag, κal, κar, hω1', ← hc]
  let Z₂ : Subgroup E :=
    { carrier := {z | z = 1 ∨ z = c}
      one_mem' := Or.inl rfl
      mul_mem' := by
        rintro a b (rfl | rfl) (rfl | rfl) <;> simp [hcc]
      inv_mem' := by
        rintro a (rfl | rfl)
        · simp
        · exact Or.inr (inv_eq_of_mul_eq_one_right hcc) }
  have heq := linearCover_sylow_derived_eq_kernel 2 hcard' η hsurj hcentral hp
  have hle : (commutator (linearCoverPreimageSylow 2 hcard' η hsurj hp : Subgroup E)).map
      (linearCoverPreimageSylow 2 hcard' η hsurj hp : Subgroup E).subtype ≤ Z₂ := by
    apply Subgroup.map_le_iff_le_comap.mpr
    rw [commutator_def, Subgroup.commutator_le]
    intro x _ y _
    obtain ⟨sx, hsx⟩ := x.property
    obtain ⟨sy, hsy⟩ := y.property
    have hc' := linearCoverCommutator_eq_of_lifts η hsurj hcentral (x := sx.toAdd) (y := sy.toAdd)
      (a := (x : E)) (b := (y : E)) hsx.symm hsy.symm
    show ⁅(x : E), (y : E)⁆ ∈ Z₂
    rw [← hc']
    exact hall _ _
  have hker : ∀ z ∈ η.ker, z = 1 ∨ z = c := fun z hz => by
    have hz' : z ∈ (commutator (linearCoverPreimageSylow 2 hcard' η hsurj hp : Subgroup E)).map
        (linearCoverPreimageSylow 2 hcard' η hsurj hp : Subgroup E).subtype := by
      rw [heq]
      exact hz
    exact hle hz'
  rcases hker a ha with h | h
  · exact absurd h ha1
  rcases hker b hb with h' | h'
  · exact absurd h' hb1
  rw [h, h']

end Cover

variable {G : Type} [Group G] [Finite G] {L M T : Subgroup G} {n : ℕ}

theorem inv_mul_mem_blockU_of_two (h : NatBlock L 2) {a b : G} (ha : a ∈ oTwoIn L)
    (hb : b ∈ oTwoIn L) (ha' : a ∉ blockU L) (hb' : b ∉ blockU L) : a⁻¹ * b ∈ blockU L := by
  classical
  let D := h.natData
  let N : Subgroup ↥L := (blockU L).subgroupOf L
  have hN : N.Normal := Subgroup.normal_subgroupOf_of_le_normalizer (le_normalizer_blockU L)
  have hperf : Group.IsPerfect ↥L := Subgroup.isPerfect_iff.2 h.perfect
  have hNker : N ≤ D.φ.ker := by
    intro x hx
    exact (D.φ_ker x).2 (blockU_le_oTwoIn L hx)
  let η : (↥L ⧸ N) →* Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 2) :=
    QuotientGroup.lift N D.φ hNker
  have hη : ∀ l : ↥L, η (QuotientGroup.mk l) = D.φ l := fun l => rfl
  have hsurj : Function.Surjective η := by
    intro g
    obtain ⟨l, hl⟩ := D.φ_surj g
    exact ⟨QuotientGroup.mk l, by rw [hη, hl]⟩
  have hker : ∀ z : ↥L ⧸ N, η z = 1 → ∃ l : ↥L, (l : G) ∈ oTwoIn L ∧ QuotientGroup.mk l = z := by
    intro z hz
    obtain ⟨l, rfl⟩ := QuotientGroup.mk_surjective z
    rw [hη] at hz
    exact ⟨l, (D.φ_ker l).1 hz, rfl⟩
  have hcentral : η.ker ≤ Subgroup.center (↥L ⧸ N) := by
    intro z hz
    obtain ⟨l, hlO, rfl⟩ := hker z hz
    refine Subgroup.mem_center_iff.2 fun g => ?_
    obtain ⟨l', rfl⟩ := QuotientGroup.mk_surjective g
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq]
    show ((l' * l)⁻¹ * (l * l') : ↥L) ∈ N
    rw [Subgroup.mem_subgroupOf]
    have h1 : ⁅(l : G)⁻¹, (l' : G)⁻¹⁆ ∈ ⁅oTwoIn L, L⁆ :=
      Subgroup.commutator_mem_commutator (inv_mem hlO) (inv_mem l'.2)
    have e : (((l' * l)⁻¹ * (l * l') : ↥L) : G) = ⁅(l : G)⁻¹, (l' : G)⁻¹⁆ := by
      simp only [commutatorElement_def, Subgroup.coe_mul, Subgroup.coe_inv, mul_inv_rev, inv_inv]
      group
    rw [e]
    exact h1
  have hp : IsPGroup 2 η.ker := by
    intro g
    obtain ⟨l, hlO, hl⟩ := hker g.1 g.2
    obtain ⟨k, hk⟩ := isPGroup_oTwoIn L ⟨(l : G), hlO⟩
    refine ⟨k, Subtype.ext ?_⟩
    have hk' : ((l : G)) ^ 2 ^ k = 1 := congrArg Subtype.val hk
    have hk'' : l ^ 2 ^ k = 1 := Subtype.ext hk'
    show (g.1) ^ 2 ^ k = 1
    rw [← hl, ← QuotientGroup.mk_pow, hk'']
    rfl
  have hq : Nat.card (GaloisField 2 2) = 4 := by
    rw [GaloisField.card 2 2 (by norm_num)]
    norm_num
  have hma : (QuotientGroup.mk (⟨a, oTwoIn_le L ha⟩ : ↥L) : ↥L ⧸ N) ∈ η.ker :=
    (D.φ_ker _).2 ha
  have hmb : (QuotientGroup.mk (⟨b, oTwoIn_le L hb⟩ : ↥L) : ↥L ⧸ N) ∈ η.ker :=
    (D.φ_ker _).2 hb
  have hne : ∀ x : ↥L, (x : G) ∉ blockU L → (QuotientGroup.mk x : ↥L ⧸ N) ≠ 1 := fun x hx h1 =>
    hx (Subgroup.mem_subgroupOf.1 ((QuotientGroup.eq_one_iff x).1 h1))
  have := cover_ker_eq_of_ne_one hq hsurj hcentral hp hma hmb (hne _ ha') (hne _ hb')
  rw [QuotientGroup.eq] at this
  exact Subgroup.mem_subgroupOf.1 this

theorem inv_mul_mem_blockU_of_ne (h : NatBlock L n) {a b : G} (ha : a ∈ oTwoIn L)
    (hb : b ∈ oTwoIn L) (ha' : a ∉ blockU L) (hb' : b ∉ blockU L) : a⁻¹ * b ∈ blockU L := by
  rcases Nat.lt_or_ge n 3 with hn | hn
  · obtain rfl : n = 2 := by have := h.two_le; omega
    exact inv_mul_mem_blockU_of_two h ha hb ha' hb'
  · exact absurd (h.oTwoIn_eq_blockU_of_three_le hn ▸ ha) ha'

theorem card_oTwoIn_le_two_mul (h : NatBlock L n) :
    Nat.card (oTwoIn L) ≤ 2 * Nat.card (blockU L) := by
  classical
  by_cases hWV : oTwoIn L ≤ blockU L
  · rw [le_antisymm hWV (blockU_le_oTwoIn L)]
    have : 0 < Nat.card (blockU L) := Nat.card_pos
    omega
  · obtain ⟨a, haW, haV⟩ := Set.not_subset.1 hWV
    set H : Subgroup ↥(oTwoIn L) := (blockU L).subgroupOf (oTwoIn L) with hH
    have hidx : H.index = 2 := by
      rw [Subgroup.index_eq_two_iff]
      refine ⟨⟨a, haW⟩, fun b => ?_⟩
      have hmem : ∀ x : ↥(oTwoIn L), x ∈ H ↔ (x : G) ∈ blockU L := fun x => Iff.rfl
      by_cases hb : (b : G) ∈ blockU L
      · refine Or.inr ⟨(hmem b).2 hb, fun hp => haV ?_⟩
        have hp' : (b : G) * a ∈ blockU L := (hmem _).1 hp
        have := mul_mem (inv_mem hb) hp'
        simpa using this
      · refine Or.inl ⟨?_, fun hb' => hb ((hmem b).1 hb')⟩
        have h1 : (b : G)⁻¹ ∈ oTwoIn L := inv_mem b.2
        have h2 : (b : G)⁻¹ ∉ blockU L := fun h3 => hb (by simpa using inv_mem h3)
        have := inv_mul_mem_blockU_of_ne h h1 haW h2 haV
        rw [hmem]
        simpa using this
    have h1 := Subgroup.index_mul_card H
    have h2 : Nat.card H = Nat.card (blockU L) :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe (blockU_le_oTwoIn L)).toEquiv
    rw [hidx, h2] at h1
    exact h1.symm.le

omit [Finite G] in
theorem wleVE_of_eq (hWV : oTwoIn L = blockU L) : oTwoIn L ≤ blockU L ⊔ Ec L T :=
  hWV.le.trans le_sup_left

theorem wleVE_of_three_le (h : NatBlock L n) (hn : 3 ≤ n) : oTwoIn L ≤ blockU L ⊔ Ec L T :=
  wleVE_of_eq (h.oTwoIn_eq_blockU_of_three_le hn)

theorem wleVE_iff_of_sylow (h : NatBlock L n) (hLM : L ≤ M)
    (hMN : M ≤ Subgroup.normalizer (L : Set G)) (hT : CFSG.ABGLocalTools.IsSylowOf 2 T M)
    (hne : oTwoIn L ≠ blockU L) :
    oTwoIn L ≤ blockU L ⊔ Ec L T ↔ ¬ (L ⊓ Subgroup.centralizer (L : Set G) ≤ blockU L) := by
  constructor
  · intro hWVE hZ
    obtain ⟨w, hw, hwV⟩ : ∃ w ∈ oTwoIn L, w ∉ blockU L := by
      by_contra hcon
      push Not at hcon
      exact hne (le_antisymm hcon (blockU_le_oTwoIn L))
    have hVn : blockU L ≤ Subgroup.normalizer (Ec L T : Set G) :=
      (NatBlock.blockU_le_sylow hLM hMN hT).trans (le_normalizer_Ec hMN hT.le)
    obtain ⟨v, hv, e, he, rfl⟩ := (Aux.mem_sup_iff_mul hVn).1 (hWVE hw)
    have heV : e ∈ blockU L := hZ ⟨oTwoIn_le L (by
      have := (oTwoIn L).mul_mem ((oTwoIn L).inv_mem (blockU_le_oTwoIn L hv)) hw
      simpa using this), he.2⟩
    exact hwV (mul_mem hv heV)
  · intro hZ w hw
    obtain ⟨z, ⟨hzL, hzC⟩, hzV⟩ := Set.not_subset.1 hZ
    have hzW : z ∈ oTwoIn L := h.center_le ⟨hzL, hzC⟩
    have hzE : z ∈ Ec L T := ⟨NatBlock.oTwoIn_le_sylow hLM hMN hT hzW, hzC⟩
    by_cases hwV : w ∈ blockU L
    · exact Subgroup.mem_sup_left hwV
    · have hv := inv_mul_mem_blockU_of_ne h hzW hw hzV hwV
      have e : w = z * (z⁻¹ * w) := by group
      rw [e, sup_comm]
      exact Subgroup.mul_mem_sup hzE hv

theorem wleVE_iff (hs : Sec4 G L M T n) (hE1 : FooteNonsolvableSimple)
    (hne : oTwoIn L ≠ blockU L) :
    oTwoIn L ≤ blockU L ⊔ Ec L T ↔ ¬ (L ⊓ Subgroup.centralizer (L : Set G) ≤ blockU L) :=
  wleVE_iff_of_sylow hs.hyp.natBlock hs.hyp.le (hs.hyp.normal hE1) hs.sylow hne

theorem exists_inverting_pair (h : NatBlock L 2) :
    ∃ r f : G, r ∈ L ∧ f ∈ L ∧ r ^ 3 = 1 ∧ f * r * f⁻¹ = r⁻¹ ∧ f⁻¹ * r * f = r⁻¹ ∧
      f ∉ oTwoIn L ∧ f ^ 2 ∈ oTwoIn L ∧ ∀ v ∈ blockU L, r * v * r⁻¹ = v → v ∈ blockZ L := by
  classical
  set D := h.natData with hD
  have hcard : Nat.card (Fq 2) = 4 := by
    rw [GaloisField.card 2 2 (by norm_num)]
    norm_num
  obtain ⟨c, hc0, hc1⟩ := Aux.exists_ne_zero_one hcard
  have hc3 : c ^ 3 = 1 := by
    have : Fintype (Fq 2) := Fintype.ofFinite _
    have hc : Fintype.card (Fq 2) = 4 := by rw [← Nat.card_eq_fintype_card]; exact hcard
    have h4 : c ^ 4 = c := by
      have := FiniteField.pow_card c
      rwa [hc] at this
    apply mul_left_cancel₀ hc0
    rw [mul_one, ← pow_succ']
    exact h4
  have hc1' : c⁻¹ ≠ 1 := fun h1 => hc1 (by simpa using h1)
  set dg : SL2 (Fq 2) := tMat c hc0 with hdg
  have hdg3 : dg ^ 3 = 1 := Aux.tMat_pow_three hc0 hc3
  obtain ⟨t₀, ht₀⟩ := D.φ_surj dg
  obtain ⟨f₁, hf₁⟩ := D.φ_surj (Aux.wMat (Fq 2))
  have ht3 : (t₀ : G) ^ 3 ∈ oTwoIn L := by
    refine (D.φ_ker ⟨(t₀ : G) ^ 3, L.pow_mem t₀.2 3⟩).1 ?_
    have e : (⟨(t₀ : G) ^ 3, L.pow_mem t₀.2 3⟩ : ↥L) = t₀ ^ 3 := rfl
    rw [e, map_pow, ht₀, hdg3]
  obtain ⟨k, hk⟩ := isPGroup_oTwoIn L ⟨(t₀ : G) ^ 3, ht3⟩
  have hk' : ((t₀ : G) ^ 3) ^ 2 ^ k = 1 := congrArg Subtype.val hk
  have hrL : (t₀ : G) ^ 4 ^ k ∈ L := L.pow_mem t₀.2 _
  have hr3 : ((t₀ : G) ^ 4 ^ k) ^ 3 = 1 := by
    have e : (4 : ℕ) ^ k = 2 ^ k * 2 ^ k := by rw [← mul_pow]; norm_num
    calc ((t₀ : G) ^ 4 ^ k) ^ 3 = (((t₀ : G) ^ 3) ^ 2 ^ k) ^ 2 ^ k := by
          rw [e, ← pow_mul, ← pow_mul, ← pow_mul]
          congr 1
          ring
      _ = 1 := by rw [hk', one_pow]
  have hpow : dg ^ 4 ^ k = dg := by
    have h1 : 4 ^ k % 3 = 1 := by
      rw [Nat.pow_mod]
      norm_num
    calc dg ^ 4 ^ k = dg ^ (3 * (4 ^ k / 3) + 4 ^ k % 3) := by rw [Nat.div_add_mod]
      _ = dg := by rw [h1, pow_add, pow_mul, hdg3, one_pow, one_mul, pow_one]
  have hφr : D.φ ⟨(t₀ : G) ^ 4 ^ k, hrL⟩ = dg := by
    have e : (⟨(t₀ : G) ^ 4 ^ k, hrL⟩ : ↥L) = t₀ ^ 4 ^ k := rfl
    rw [e, map_pow, ht₀, hpow]
  generalize (t₀ : G) ^ 4 ^ k = r at hrL hr3 hφr
  have hrrr : r * r * r = 1 := by rw [← pow_three']; exact hr3
  have hCV : ∀ v ∈ blockU L, r * v * r⁻¹ = v → v ∈ blockZ L := by
    intro v hv hrv
    have h1 := D.ψe_conj hrL hv
    rw [hrv, hφr, hdg, tMat_coe] at h1
    have e0 := congrFun h1 0
    have e1 := congrFun h1 1
    rw [mulVec_two_zero] at e0
    rw [mulVec_two_one] at e1
    simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_fin_one, Matrix.empty_val', zero_mul, add_zero, zero_add] at e0 e1
    refine (D.ψe_eq_zero_iff hv).1 (funext fun i => ?_)
    fin_cases i
    · have : (1 - c) * D.ψe v 0 = 0 := by linear_combination e0
      exact (mul_eq_zero.1 this).resolve_left (sub_ne_zero.2 (Ne.symm hc1))
    · have : (1 - c⁻¹) * D.ψe v 1 = 0 := by linear_combination e1
      exact (mul_eq_zero.1 this).resolve_left (sub_ne_zero.2 (Ne.symm hc1'))
  have hwinv : (Aux.wMat (Fq 2))⁻¹ = Aux.wMat (Fq 2) :=
    inv_eq_of_mul_eq_one_right (Aux.wMat_mul_self _)
  have hw : Aux.wMat (Fq 2) * dg * Aux.wMat (Fq 2) = dg⁻¹ :=
    Aux.wMat_mul_tMat_mul_wMat (Fq 2) hc0
  have hu : (f₁ : G)⁻¹ * r * f₁ * r ∈ oTwoIn L := by
    have hmem : (f₁ : G)⁻¹ * r * f₁ * r ∈ L :=
      L.mul_mem (L.mul_mem (L.mul_mem (L.inv_mem f₁.2) hrL) f₁.2) hrL
    refine (D.φ_ker ⟨_, hmem⟩).1 ?_
    have e : (⟨(f₁ : G)⁻¹ * r * f₁ * r, hmem⟩ : ↥L) = f₁⁻¹ * ⟨r, hrL⟩ * f₁ * ⟨r, hrL⟩ := rfl
    rw [e]
    simp only [map_mul, map_inv, hf₁, hφr, hwinv]
    rw [hw, inv_mul_cancel]
  obtain ⟨f, hfW, hfix⟩ := Aux.exists_fixed_in_coset (X := oTwoIn L) (isPGroup_oTwoIn L)
    (f₁ : G) (fun x => r * x * r)
    (fun x => by
      calc r * (r * (r * x * r) * r) * r = (r * r * r) * x * (r * r * r) := by group
        _ = x := by rw [hrrr]; group)
    (fun x hx => by
      have e : (f₁ : G)⁻¹ * (r * x * r) =
          ((f₁ : G)⁻¹ * r * f₁ * r) * (r⁻¹ * ((f₁ : G)⁻¹ * x) * r) := by group
      rw [e]
      have := conj_mem_oTwoIn (Subgroup.le_normalizer (L.inv_mem hrL)) hx
      rw [inv_inv] at this
      exact mul_mem hu this)
  have hfL : f ∈ L := by
    have := L.mul_mem f₁.2 (oTwoIn_le L hfW)
    simpa using this
  have hφf : D.φ ⟨f, hfL⟩ = Aux.wMat (Fq 2) := by
    have e : (⟨f, hfL⟩ : ↥L) = f₁ * ⟨(f₁ : G)⁻¹ * f, oTwoIn_le L hfW⟩ := by
      apply Subtype.ext
      simp
    rw [e, map_mul, hf₁, (D.φ_ker _).2 hfW, mul_one]
  refine ⟨r, f, hrL, hfL, hr3, ?_, ?_, ?_, ?_, hCV⟩
  · have h1 : f * r = r⁻¹ * f := by
      have := congrArg (fun x => r⁻¹ * x) hfix
      simpa [mul_assoc] using this
    calc f * r * f⁻¹ = r⁻¹ * f * f⁻¹ := by rw [h1]
      _ = r⁻¹ := by group
  · have h1 : f⁻¹ * r * f * r = 1 := by
      calc f⁻¹ * r * f * r = f⁻¹ * (r * f * r) := by group
        _ = f⁻¹ * f := by rw [hfix]
        _ = 1 := by group
    exact mul_eq_one_iff_eq_inv.1 h1
  · intro hfW'
    have := (D.φ_ker ⟨f, hfL⟩).2 hfW'
    rw [hφf] at this
    exact Aux.wMat_ne_one (Fq 2) this
  · refine (D.φ_ker ⟨f ^ 2, L.pow_mem hfL 2⟩).1 ?_
    have e : (⟨f ^ 2, L.pow_mem hfL 2⟩ : ↥L) = ⟨f, hfL⟩ * ⟨f, hfL⟩ := Subtype.ext (pow_two f)
    rw [e, map_mul, hφf, Aux.wMat_mul_self]


theorem oTwoIn_comm (h : NatBlock L n) {a b : G} (ha : a ∈ oTwoIn L) (hb : b ∈ oTwoIn L) :
    a * b = b * a := by
  by_cases haV : a ∈ blockU L
  · exact blockU_comm_of_short h.short a haV b hb
  by_cases hbV : b ∈ blockU L
  · exact (blockU_comm_of_short h.short b hbV a ha).symm
  have hv : a⁻¹ * b ∈ blockU L := inv_mul_mem_blockU_of_ne h ha hb haV hbV
  have hva : (a⁻¹ * b) * a = a * (a⁻¹ * b) := blockU_comm_of_short h.short _ hv a ha
  calc a * b = a * (a * (a⁻¹ * b)) := by group
    _ = a * ((a⁻¹ * b) * a) := by rw [hva]
    _ = b * a := by group

theorem Qc_centralizes_oTwoIn (h : NatBlock L n) (hLM : L ≤ M)
    (hMN : M ≤ Subgroup.normalizer (L : Set G)) {u : G}
    (hu : u ∈ M ⊓ Subgroup.centralizer (blockU L : Set G)) :
    ∀ w ∈ oTwoIn L, w * u = u * w := by
  classical
  intro w₀ hw₀
  by_cases hWV : oTwoIn L ≤ blockU L
  · exact Subgroup.mem_centralizer_iff.1 hu.2 w₀ (hWV hw₀)
  have hn : n = 2 := by
    by_contra hn
    have h2 := h.two_le
    exact hWV (le_of_eq (h.oTwoIn_eq_blockU_of_three_le (by omega)))
  subst hn
  obtain ⟨r, f, hrL, hfL, hr3, hfr, hfr', hfW, hf2W, hCV⟩ := exists_inverting_pair h
  have hf2V : f ^ 2 ∉ blockU L := fun h2 =>
    hWV (le_of_eq (h.oTwoIn_eq_blockU_of_sq_mem hfL hfW h2))
  have hrrr : r * r * r = 1 := by rw [← pow_three']; exact hr3
  obtain ⟨u₁, hu₁W, hu₁r⟩ := Aux.exists_fixed_in_coset (X := oTwoIn L) (isPGroup_oTwoIn L) u
    (fun x => r * x * r⁻¹)
    (fun x => by
      calc r * (r * (r * x * r⁻¹) * r⁻¹) * r⁻¹ = (r * r * r) * x * (r * r * r)⁻¹ := by group
        _ = x := by rw [hrrr]; group)
    (fun x hx => by
      have e : u⁻¹ * (r * x * r⁻¹) = (u⁻¹ * r * u * r⁻¹) * (r * (u⁻¹ * x) * r⁻¹) := by group
      rw [e]
      have h1 : u⁻¹ * r * u * r⁻¹ ∈ oTwoIn L := blockU_le_oTwoIn L (h.delta_mem hMN hu hrL)
      exact mul_mem h1 (conj_mem_oTwoIn (Subgroup.le_normalizer hrL) hx))
  have hw'V : ∀ v ∈ blockU L, v * u₁ = u₁ * v := by
    intro v hv
    have e : u₁ = u * (u⁻¹ * u₁) := by group
    rw [e]
    have h1 := Subgroup.mem_centralizer_iff.1 hu.2 v hv
    have h2 : v * (u⁻¹ * u₁) = (u⁻¹ * u₁) * v :=
      blockU_comm_of_short h.short v hv _ hu₁W
    calc v * (u * (u⁻¹ * u₁)) = (v * u) * (u⁻¹ * u₁) := by group
      _ = (u * v) * (u⁻¹ * u₁) := by rw [h1]
      _ = u * (v * (u⁻¹ * u₁)) := by group
      _ = u * ((u⁻¹ * u₁) * v) := by rw [h2]
      _ = (u * (u⁻¹ * u₁)) * v := by group
  have hu₁ : u₁ ∈ M ⊓ Subgroup.centralizer (blockU L : Set G) := by
    have e : u₁ = u * (u⁻¹ * u₁) := by group
    refine ⟨?_, Subgroup.mem_centralizer_iff.2 hw'V⟩
    rw [e]
    exact M.mul_mem hu.1 (hLM (oTwoIn_le L hu₁W))
  have hur : u₁ * r = r * u₁ := by
    have h1 : r * u₁ * r⁻¹ = u₁ := hu₁r
    calc u₁ * r = (r * u₁ * r⁻¹) * r := by rw [h1]
      _ = r * u₁ := by group
  have hur' : u₁⁻¹ * r * u₁ = r := by
    calc u₁⁻¹ * r * u₁ = u₁⁻¹ * (r * u₁) := by group
      _ = u₁⁻¹ * (u₁ * r) := by rw [hur]
      _ = r := by group
  have hur'' : u₁ * r⁻¹ * u₁⁻¹ = r⁻¹ := by
    calc u₁ * r⁻¹ * u₁⁻¹ = (u₁ * r * u₁⁻¹)⁻¹ := by group
      _ = r⁻¹ := by rw [hur]; group
  have hvV : u₁ * f * u₁⁻¹ * f⁻¹ ∈ blockU L := h.comm_centralizer_mem_blockU hMN hu₁ f hfL
  have hg_inv : (u₁ * f * u₁⁻¹) * r * (u₁ * f * u₁⁻¹)⁻¹ = r⁻¹ := by
    calc (u₁ * f * u₁⁻¹) * r * (u₁ * f * u₁⁻¹)⁻¹
        = u₁ * f * (u₁⁻¹ * r * u₁) * f⁻¹ * u₁⁻¹ := by group
      _ = u₁ * (f * r * f⁻¹) * u₁⁻¹ := by rw [hur']; group
      _ = u₁ * r⁻¹ * u₁⁻¹ := by rw [hfr]
      _ = r⁻¹ := hur''
  have hvr0 : (u₁ * f * u₁⁻¹ * f⁻¹) * r * (u₁ * f * u₁⁻¹ * f⁻¹)⁻¹ = r := by
    calc (u₁ * f * u₁⁻¹ * f⁻¹) * r * (u₁ * f * u₁⁻¹ * f⁻¹)⁻¹
        = (u₁ * f * u₁⁻¹) * (f⁻¹ * r * f) * (u₁ * f * u₁⁻¹)⁻¹ := by group
      _ = (u₁ * f * u₁⁻¹) * r⁻¹ * (u₁ * f * u₁⁻¹)⁻¹ := by rw [hfr']
      _ = ((u₁ * f * u₁⁻¹) * r * (u₁ * f * u₁⁻¹)⁻¹)⁻¹ := by group
      _ = r := by rw [hg_inv]; group
  have hvr : r * (u₁ * f * u₁⁻¹ * f⁻¹) * r⁻¹ = u₁ * f * u₁⁻¹ * f⁻¹ := by
    have h1 : (u₁ * f * u₁⁻¹ * f⁻¹) * r = r * (u₁ * f * u₁⁻¹ * f⁻¹) := by
      have := congrArg (fun x => x * (u₁ * f * u₁⁻¹ * f⁻¹)) hvr0
      simpa [mul_assoc] using this
    calc r * (u₁ * f * u₁⁻¹ * f⁻¹) * r⁻¹ = ((u₁ * f * u₁⁻¹ * f⁻¹) * r) * r⁻¹ := by rw [h1]
      _ = u₁ * f * u₁⁻¹ * f⁻¹ := by group
  have hvZ : u₁ * f * u₁⁻¹ * f⁻¹ ∈ blockZ L := hCV _ hvV hvr
  have hvc : f * (u₁ * f * u₁⁻¹ * f⁻¹) = (u₁ * f * u₁⁻¹ * f⁻¹) * f :=
    Subgroup.mem_centralizer_iff.1 (NatBlock.blockZ_le_centralizer L hvZ) f hfL
  have hv2 : (u₁ * f * u₁⁻¹ * f⁻¹) * (u₁ * f * u₁⁻¹ * f⁻¹) = 1 := by
    rw [← pow_two]
    exact h.sq_eq_one_of_mem_blockU hvV
  have hcomm_f2 : u₁ * f ^ 2 = f ^ 2 * u₁ := by
    have h1 : u₁ * f ^ 2 * u₁⁻¹ = f ^ 2 := by
      calc u₁ * f ^ 2 * u₁⁻¹ = (u₁ * f * u₁⁻¹) ^ 2 := by rw [conj_pow]
        _ = ((u₁ * f * u₁⁻¹ * f⁻¹) * f) ^ 2 := by group
        _ = (u₁ * f * u₁⁻¹ * f⁻¹) * (f * (u₁ * f * u₁⁻¹ * f⁻¹)) * f := by rw [pow_two]; group
        _ = (u₁ * f * u₁⁻¹ * f⁻¹) * ((u₁ * f * u₁⁻¹ * f⁻¹) * f) * f := by rw [hvc]
        _ = ((u₁ * f * u₁⁻¹ * f⁻¹) * (u₁ * f * u₁⁻¹ * f⁻¹)) * (f * f) := by group
        _ = f ^ 2 := by rw [hv2, one_mul, pow_two]
    exact mul_inv_eq_iff_eq_mul.1 h1
  have hu₁w : ∀ w ∈ oTwoIn L, w * u₁ = u₁ * w := by
    intro w hw
    by_cases hwV : w ∈ blockU L
    · exact hw'V w hwV
    obtain ⟨v', hv'V, hwv⟩ : ∃ v' ∈ blockU L, w = f ^ 2 * v' :=
      ⟨(f ^ 2)⁻¹ * w, inv_mul_mem_blockU_of_two h hf2W hw hf2V hwV, by group⟩
    rw [hwv]
    calc f ^ 2 * v' * u₁ = f ^ 2 * (v' * u₁) := by group
      _ = f ^ 2 * (u₁ * v') := by rw [hw'V v' hv'V]
      _ = (f ^ 2 * u₁) * v' := by group
      _ = (u₁ * f ^ 2) * v' := by rw [hcomm_f2]
      _ = u₁ * (f ^ 2 * v') := by group
  have hw'W : u⁻¹ * u₁ ∈ oTwoIn L := hu₁W
  have e : u = u₁ * (u⁻¹ * u₁)⁻¹ := by group
  calc w₀ * u = w₀ * (u₁ * (u⁻¹ * u₁)⁻¹) := by rw [← e]
    _ = (w₀ * u₁) * (u⁻¹ * u₁)⁻¹ := by group
    _ = (u₁ * w₀) * (u⁻¹ * u₁)⁻¹ := by rw [hu₁w w₀ hw₀]
    _ = u₁ * (w₀ * (u⁻¹ * u₁)⁻¹) := by group
    _ = u₁ * ((u⁻¹ * u₁)⁻¹ * w₀) := by rw [oTwoIn_comm h hw₀ (inv_mem hw'W)]
    _ = (u₁ * (u⁻¹ * u₁)⁻¹) * w₀ := by group
    _ = u * w₀ := by rw [← e]

theorem Dc_centralizes_oTwoIn_of_sylow (h : NatBlock L n) (hLM : L ≤ M)
    (hMN : M ≤ Subgroup.normalizer (L : Set G)) (hT : CFSG.ABGLocalTools.IsSylowOf 2 T M) :
    ∀ w ∈ oTwoIn L, ∀ d ∈ Dc L T, w * d = d * w := fun w hw _ hd =>
  Qc_centralizes_oTwoIn h hLM hMN ⟨hT.le hd.1, hd.2⟩ w hw

theorem Dc_centralizes_oTwoIn (hs : Sec4 G L M T n) (hE1 : FooteNonsolvableSimple) :
    ∀ w ∈ oTwoIn L, ∀ d ∈ Dc L T, w * d = d * w :=
  Dc_centralizes_oTwoIn_of_sylow hs.hyp.natBlock hs.hyp.le (hs.hyp.normal hE1) hs.sylow

end CFSG.CGT.PushingUpLit.T2KSW
