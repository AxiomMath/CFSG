module

public import CFSG.GH74.Uniqueness.SU.SU2Defs

public section

open Subgroup Pointwise

namespace CFSG.GH74.Uniqueness.SU.SU2

section Omega

variable {X : Type} [Group X] (V : Type) [Group V] [MulDistribMulAction X V]

@[expose] def omega (Y : Subgroup X) : Set (Subgroup V) := MulAction.orbit X (fixSub V Y)

variable {V}

theorem mem_omega_iff {Y : Subgroup X} {W : Subgroup V} :
    W ∈ omega V Y ↔ ∃ x : X, x • fixSub V Y = W := MulAction.mem_orbit_iff

theorem fixSub_mem_omega (Y : Subgroup X) : fixSub V Y ∈ omega V Y :=
  mem_omega_iff.2 ⟨1, one_smul _ _⟩

theorem smul_mem_omega {Y : Subgroup X} {A : Subgroup V} (hA : A ∈ omega V Y) (x : X) :
    x • A ∈ omega V Y := by
  obtain ⟨g, rfl⟩ := mem_omega_iff.1 hA
  exact mem_omega_iff.2 ⟨x * g, mul_smul x g _⟩

theorem exists_ne_one_of_ne_bot {G : Type*} [Group G] {H : Subgroup G} (h : H ≠ ⊥) :
    ∃ w ∈ H, w ≠ 1 := by
  by_contra hcon
  exact h ((Subgroup.eq_bot_iff_forall _).2 fun w hw => by_contra fun h' => hcon ⟨w, hw, h'⟩)

@[expose] noncomputable def pr (Y : Subgroup X) (v : V) : V :=
  Classical.epsilon fun c => c ∈ fixSub V Y ∧ v * c⁻¹ ∈ commSub V Y

namespace GOPair

variable {Y : Subgroup X}

theorem pr_spec [Finite X] (hGO : GOPair V Y) (v : V) :
    pr Y v ∈ fixSub V Y ∧ v * (pr Y v)⁻¹ ∈ commSub V Y :=
  Classical.epsilon_spec (p := fun c => c ∈ fixSub V Y ∧ v * c⁻¹ ∈ commSub V Y)
    (hGO.exists_decomp v)

theorem pr_eq_of_pr_mul [Finite X] (hGO : GOPair V Y) {w w' : V} (h : pr Y w = pr Y w') :
    w * w'⁻¹ ∈ commSub V Y := by
  have h1 := (hGO.pr_spec w).2
  have h2 := (hGO.pr_spec w').2
  have : w * w'⁻¹ = (w * (pr Y w)⁻¹) * (w' * (pr Y w')⁻¹)⁻¹ := by
    rw [← h]; group
  rw [this]
  exact (commSub V Y).mul_mem h1 ((commSub V Y).inv_mem h2)

theorem omega_ne_bot (hGO : GOPair V Y) {W : Subgroup V} (hW : W ∈ omega V Y) : W ≠ ⊥ := by
  obtain ⟨x, rfl⟩ := mem_omega_iff.1 hW
  intro h
  apply hGO.fixSub_ne_bot
  have : fixSub V Y = x⁻¹ • (x • fixSub V Y) := by rw [inv_smul_smul]
  rw [this, h, Subgroup.smul_bot]

theorem card_eq_of_mem_omega {W : Subgroup V} (hW : W ∈ omega V Y) :
    Nat.card W = Nat.card (fixSub V Y) := by
  obtain ⟨x, rfl⟩ := mem_omega_iff.1 hW
  exact (Nat.card_congr (Subgroup.equivSMul x (fixSub V Y)).toEquiv).symm

theorem ti (hGO : GOPair V Y) {A B : Subgroup V} (hA : A ∈ omega V Y) (hB : B ∈ omega V Y) {v : V}
    (hvA : v ∈ A) (hvB : v ∈ B) (hv : v ≠ 1) : A = B := by
  obtain ⟨x₁, rfl⟩ := mem_omega_iff.1 hA
  obtain ⟨x₂, rfl⟩ := mem_omega_iff.1 hB
  by_contra hne
  have h := hGO.inter_trivial x₁ x₂ hne
  have hmem : v ∈ x₁ • fixSub V Y ⊓ x₂ • fixSub V Y := ⟨hvA, hvB⟩
  rw [h] at hmem
  exact hv hmem

theorem inf_eq_bot_of_ne (hGO : GOPair V Y) {A B : Subgroup V} (hA : A ∈ omega V Y)
    (hB : B ∈ omega V Y) (hne : A ≠ B) : A ⊓ B = ⊥ := by
  rw [eq_bot_iff]
  intro v hv
  by_contra hv1
  exact hne (hGO.ti hA hB hv.1 hv.2 hv1)

theorem smul_eq_of_smul_mem (hGO : GOPair V Y) {W : Subgroup V} (hW : W ∈ omega V Y) {x : X}
    {w : V} (hw : w ∈ W) (hw1 : w ≠ 1) (hxw : x • w ∈ W) : x • W = W := by
  have hxW : x • W ∈ omega V Y := smul_mem_omega hW x
  have hmem : x • w ∈ x • W := Subgroup.smul_mem_pointwise_smul w x W hw
  have hne : x • w ≠ 1 := by
    intro h
    apply hw1
    have : x • w = x • (1 : V) := by rw [smul_one]; exact h
    exact MulAction.injective x this
  exact hGO.ti hxW hW hmem hxw hne

theorem inf_fixSub_eq_bot (hGO : GOPair V Y) {W : Subgroup V} (hW : W ∈ omega V Y)
    (hne : W ≠ fixSub V Y) : W ⊓ fixSub V Y = ⊥ :=
  hGO.inf_eq_bot_of_ne hW (fixSub_mem_omega Y) hne

theorem typeA_cover (hGO : GOPair V Y) {W : Subgroup V} (hW : W ∈ omega V Y)
    (hWV : W ≤ commSub V Y) {v : V} (hv : v ∈ commSub V Y) (hv1 : v ≠ 1) :
    ∃ y ∈ Y, v ∈ y • W := by
  obtain ⟨w₀, hw₀, hw₀1⟩ := exists_ne_one_of_ne_bot (hGO.omega_ne_bot hW)
  obtain ⟨y, hy, hyw⟩ := hGO.transitive w₀ (hWV hw₀) hw₀1 v hv hv1
  exact ⟨y, hy, hyw ▸ Subgroup.smul_mem_pointwise_smul w₀ y W hw₀⟩

theorem typeA_trans (hGO : GOPair V Y) {W : Subgroup V} (hW : W ∈ omega V Y)
    (hWV : W ≤ commSub V Y) {w w' : V} (hw : w ∈ W) (hw' : w' ∈ W) (hw1 : w ≠ 1)
    (hw1' : w' ≠ 1) : ∃ y ∈ Y, y • W = W ∧ y • w = w' := by
  obtain ⟨y, hy, hyw⟩ := hGO.transitive w (hWV hw) hw1 w' (hWV hw') hw1'
  exact ⟨y, hy, hGO.smul_eq_of_smul_mem hW hw hw1 (hyw ▸ hw'), hyw⟩

theorem typeA_conj (hGO : GOPair V Y) {W A : Subgroup V} (hW : W ∈ omega V Y)
    (hWV : W ≤ commSub V Y) (hA : A ∈ omega V Y) (hAV : A ≤ commSub V Y) :
    ∃ y ∈ Y, A = y • W := by
  obtain ⟨a, ha, ha1⟩ := exists_ne_one_of_ne_bot (hGO.omega_ne_bot hA)
  obtain ⟨y, hy, hya⟩ := hGO.typeA_cover hW hWV (hAV ha) ha1
  exact ⟨y, hy, hGO.ti hA (smul_mem_omega hW y) ha hya ha1⟩

theorem mem_commSub_of_pr_eq_one [Finite X] (hGO : GOPair V Y) {v : V} (h : pr Y v = 1) :
    v ∈ commSub V Y := by
  have := (hGO.pr_spec v).2
  rwa [h, inv_one, mul_one] at this

theorem typeB_card_eq [Finite X] [Finite V] (hGO : GOPair V Y) {W : Subgroup V} (hW : W ∈ omega V Y)
    (hne : W ≠ fixSub V Y) (hWV : ¬ W ≤ commSub V Y) :
    Nat.card ↥(Y ⊓ MulAction.stabilizer X W) = Nat.card ↥(W ⊓ commSub V Y) := by
  have hW0 := hGO.inf_fixSub_eq_bot hW hne
  obtain ⟨w₀, hw₀W, hw₀V⟩ := IsConcreteLE.not_le_iff_exists.1 hWV
  obtain ⟨c₀, hc₀, hp₀'⟩ := hGO.exists_decomp w₀
  obtain ⟨p₀, hp₀def⟩ : ∃ p₀ : V, p₀ = w₀ * c₀⁻¹ := ⟨_, rfl⟩
  have hp₀ : p₀ ∈ commSub V Y := hp₀def ▸ hp₀'
  have hw₀eq : w₀ = p₀ * c₀ := by rw [hp₀def]; simp
  have hw01 : w₀ ≠ 1 := fun h => hw₀V (h ▸ one_mem _)
  have hcW : ∀ c ∈ fixSub V Y, c ∈ W → c = 1 := fun c hc hcW => by
    have : c ∈ W ⊓ fixSub V Y := ⟨hcW, hc⟩
    rw [hW0] at this; exact this
  have hc₀1 : c₀ ≠ 1 := by
    intro h
    apply hw₀V
    have : p₀ = w₀ := by rw [hp₀def, h, inv_one, mul_one]
    rw [← this]; exact hp₀
  have hp₀1 : p₀ ≠ 1 := by
    intro h
    have : w₀ = c₀ := by rw [hw₀eq, h, one_mul]
    exact hc₀1 (hcW c₀ hc₀ (this ▸ hw₀W))
  have hψmem : ∀ y : ↥(Y ⊓ MulAction.stabilizer X W), ((y : X) • p₀) * p₀⁻¹ ∈ W ⊓ commSub V Y := by
    intro y
    have hyY : (y : X) ∈ Y := y.2.1
    have hyW : (y : X) • W = W := MulAction.mem_stabilizer_iff.1 y.2.2
    refine ⟨?_, smul_mul_inv_mem_commSub hyY p₀⟩
    have h1 : (y : X) • w₀ ∈ W := by
      have h := Subgroup.smul_mem_pointwise_smul w₀ (y : X) W hw₀W
      rwa [hyW] at h
    have h2 : (y : X) • w₀ = ((y : X) • p₀) * c₀ := by
      rw [hw₀eq, smul_mul', hc₀ y hyY]
    have h3 : ((y : X) • p₀) * p₀⁻¹ = ((y : X) • w₀) * w₀⁻¹ := by
      rw [h2, hw₀eq, mul_inv_rev, mul_assoc, mul_inv_cancel_left]
    rw [h3]
    exact W.mul_mem h1 (W.inv_mem hw₀W)
  have hψinj : Function.Injective (fun y : ↥(Y ⊓ MulAction.stabilizer X W) =>
      (⟨((y : X) • p₀) * p₀⁻¹, hψmem y⟩ : ↥(W ⊓ commSub V Y))) := by
    intro y y' h
    have h1 : ((y : X) • p₀) * p₀⁻¹ = ((y' : X) • p₀) * p₀⁻¹ := congrArg Subtype.val h
    have h2 := mul_right_cancel h1
    exact Subtype.ext (hGO.eq_of_smul_eq y.2.1 y'.2.1 hp₀ hp₀1 h2)
  have hφ : ∀ z : ↥(W ⊓ commSub V Y), ∃ y : ↥(Y ⊓ MulAction.stabilizer X W),
      (y : X) • p₀ = (z : V) * p₀ := by
    intro z
    have hzW : (z : V) ∈ W := z.2.1
    have hzp : (z : V) * p₀ ∈ commSub V Y := mul_mem z.2.2 hp₀
    have hzp1 : (z : V) * p₀ ≠ 1 := by
      intro h
      have h1 : (z : V) * w₀ = c₀ := by rw [hw₀eq, ← mul_assoc, h, one_mul]
      exact hc₀1 (hcW c₀ hc₀ (h1 ▸ mul_mem hzW hw₀W))
    obtain ⟨y, hy, hyp⟩ := hGO.transitive p₀ hp₀ hp₀1 _ hzp hzp1
    have h2 : y • w₀ = (z : V) * w₀ := by
      rw [hw₀eq, smul_mul', hyp, hc₀ y hy, mul_assoc]
    have h3 : y • W = W :=
      hGO.smul_eq_of_smul_mem hW hw₀W hw01 (h2 ▸ mul_mem hzW hw₀W)
    exact ⟨⟨y, hy, MulAction.mem_stabilizer_iff.2 h3⟩, hyp⟩
  choose φ hφ using hφ
  have hφinj : Function.Injective φ := by
    intro z z' h
    have h1 : (z : V) * p₀ = (z' : V) * p₀ := by rw [← hφ z, ← hφ z', h]
    exact Subtype.ext (mul_right_cancel h1)
  exact le_antisymm (Nat.card_le_card_of_injective _ hψinj) (Nat.card_le_card_of_injective _ hφinj)

theorem typeB_inf_eq_bot [Finite X] [Finite V] (hGO : GOPair V Y) {W : Subgroup V} (hW : W ∈ omega V Y)
    (hne : W ≠ fixSub V Y) (hWV : ¬ W ≤ commSub V Y) : W ⊓ commSub V Y = ⊥ := by
  have h := hGO.typeB_card_eq hW hne hWV
  obtain ⟨a, ha⟩ := hGO.exists_card_pow (W ⊓ commSub V Y)
  have hdvd : Nat.card ↥(Y ⊓ MulAction.stabilizer X W) ∣ Nat.card Y :=
    Subgroup.card_dvd_of_le inf_le_left
  have hodd : Odd (Nat.card ↥(Y ⊓ MulAction.stabilizer X W)) := hGO.odd_card.of_dvd_nat hdvd
  rw [h, ha] at hodd
  have : a = 0 := by
    by_contra h0
    exact (Nat.not_even_iff_odd.2 hodd) (Nat.even_pow.2 ⟨even_two, h0⟩)
  rw [Subgroup.eq_bot_iff_card, ha, this, pow_zero]

theorem typeB_stab_trivial [Finite X] [Finite V] (hGO : GOPair V Y) {W : Subgroup V} (hW : W ∈ omega V Y)
    (hne : W ≠ fixSub V Y) (hWV : ¬ W ≤ commSub V Y) {y : X} (hy : y ∈ Y) (hyW : y • W = W) :
    y = 1 := by
  have h := hGO.typeB_card_eq hW hne hWV
  rw [hGO.typeB_inf_eq_bot hW hne hWV, Subgroup.card_bot] at h
  have hbot : Y ⊓ MulAction.stabilizer X W = ⊥ := (Subgroup.eq_bot_iff_card _).2 h
  have : y ∈ Y ⊓ MulAction.stabilizer X W := ⟨hy, MulAction.mem_stabilizer_iff.2 hyW⟩
  rw [hbot] at this
  exact this

theorem typeB_cover [Finite X] [Finite V] (hGO : GOPair V Y) {W : Subgroup V} (hW : W ∈ omega V Y)
    (hne : W ≠ fixSub V Y) (hWV : ¬ W ≤ commSub V Y) {d : V} (hd0 : d ∉ fixSub V Y)
    (hd1 : d ∉ commSub V Y) : ∃ y ∈ Y, d ∈ y • W := by
  have hW0 := hGO.inf_fixSub_eq_bot hW hne
  have hZ := hGO.typeB_inf_eq_bot hW hne hWV
  let f : W → fixSub V Y := fun w => ⟨pr Y (w : V), (hGO.pr_spec (w : V)).1⟩
  have hfinj : Function.Injective f := by
    intro a b hab
    have hab' : pr Y (a : V) = pr Y (b : V) := congrArg Subtype.val hab
    have h1 := hGO.pr_eq_of_pr_mul hab'
    have : (a : V) * (b : V)⁻¹ ∈ W ⊓ commSub V Y := ⟨W.mul_mem a.2 (W.inv_mem b.2), h1⟩
    rw [hZ] at this
    exact Subtype.ext (mul_inv_eq_one.1 this)
  have hfbij : Function.Bijective f :=
    hfinj.bijective_of_nat_card_le (card_eq_of_mem_omega hW).ge
  obtain ⟨w, hw⟩ := hfbij.2 ⟨pr Y d, (hGO.pr_spec d).1⟩
  have hwpr : pr Y (w : V) = pr Y d := congrArg Subtype.val hw
  set c := pr Y d with hcdef
  have hc : c ∈ fixSub V Y := (hGO.pr_spec d).1
  have hpd : d * c⁻¹ ∈ commSub V Y := (hGO.pr_spec d).2
  have hpw : (w : V) * c⁻¹ ∈ commSub V Y := by
    have := (hGO.pr_spec (w : V)).2
    rwa [hwpr] at this
  have hc1 : c ≠ 1 := fun h => hd1 (hGO.mem_commSub_of_pr_eq_one h)
  have hpd1 : d * c⁻¹ ≠ 1 := fun h => hd0 (by rw [mul_inv_eq_one.1 h]; exact hc)
  have hpw1 : (w : V) * c⁻¹ ≠ 1 := by
    intro h
    have hwc : (w : V) = c := mul_inv_eq_one.1 h
    have : c ∈ W ⊓ fixSub V Y := ⟨hwc ▸ w.2, hc⟩
    rw [hW0] at this
    exact hc1 this
  obtain ⟨y, hy, hyp⟩ := hGO.transitive _ hpw hpw1 _ hpd hpd1
  refine ⟨y, hy, ?_⟩
  have : y • (w : V) = d := by
    have hweq : (w : V) = ((w : V) * c⁻¹) * c := by simp
    rw [hweq, smul_mul', hyp, hc y hy]
    simp
  rw [← this]
  exact Subgroup.smul_mem_pointwise_smul _ y W w.2

theorem typeB_conj [Finite X] [Finite V] (hGO : GOPair V Y) {W A : Subgroup V} (hW : W ∈ omega V Y)
    (hne : W ≠ fixSub V Y) (hWV : ¬ W ≤ commSub V Y) (hA : A ∈ omega V Y)
    (hAne : A ≠ fixSub V Y) (hAV : ¬ A ≤ commSub V Y) : ∃ y ∈ Y, A = y • W := by
  obtain ⟨a, ha, ha1⟩ := exists_ne_one_of_ne_bot (hGO.omega_ne_bot hA)
  have ha0 : a ∉ fixSub V Y := fun h => ha1 (by
    have : a ∈ A ⊓ fixSub V Y := ⟨ha, h⟩
    rw [hGO.inf_fixSub_eq_bot hA hAne] at this; exact this)
  have ha1' : a ∉ commSub V Y := fun h => ha1 (by
    have : a ∈ A ⊓ commSub V Y := ⟨ha, h⟩
    rw [hGO.typeB_inf_eq_bot hA hAne hAV] at this; exact this)
  obtain ⟨y, hy, hya⟩ := hGO.typeB_cover hW hne hWV ha0 ha1'
  exact ⟨y, hy, hGO.ti hA (smul_mem_omega hW y) ha hya ha1⟩

end GOPair

end Omega

end CFSG.GH74.Uniqueness.SU.SU2
