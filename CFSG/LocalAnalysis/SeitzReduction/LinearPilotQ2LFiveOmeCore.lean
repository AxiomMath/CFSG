module

public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.ComponentInitial.LinearHigherInvariant
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.LocalAnalysis.SeitzReduction.EPilotPosition
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotQ2LFiveOmeBlock

public section

namespace CFSG.SeitzReduction.LinearPilot

open Subgroup Matrix
open CFSG.LocalAnalysis.ComponentInitial (LinearFlag.unitriangular)

section Data

variable {G : Type*} [Group G] {F : Type*} [Field F]

structure IsFieldModuleData (N W₁ S₀ : Subgroup G) (p : G → SpecialLinearGroup (Fin 4) F)
    (b : G → Fin 4 → F) : Prop where
  wOne_le : W₁ ≤ N
  le_normalizer : N ≤ normalizer (W₁ : Set G)
  sZero_le : S₀ ≤ N
  map_mul : ∀ x ∈ N, ∀ y ∈ N, p (x * y) = p x * p y
  surj : ∀ M, ∃ x ∈ N, p x = M
  eq_one_iff : ∀ x ∈ N, p x = 1 ↔ x ∈ W₁
  mem_sZero_iff : ∀ x ∈ N, x ∈ S₀ ↔ p x ∈ LinearFlag.unitriangular 4 F
  add : ∀ v ∈ W₁, ∀ w ∈ W₁, b (v * w) = b v + b w
  inj : ∀ v ∈ W₁, ∀ w ∈ W₁, b v = b w → v = w
  surjB : ∀ r, ∃ w ∈ W₁, b w = r
  act : ∀ x ∈ N, ∀ w ∈ W₁,
    b (x * w * x⁻¹) = b w ᵥ* ((p x)⁻¹ : SpecialLinearGroup (Fin 4) F)

variable {N W₁ S₀ : Subgroup G} {p : G → SpecialLinearGroup (Fin 4) F} {b : G → Fin 4 → F}

theorem IsFieldModuleData.map_one (h : IsFieldModuleData N W₁ S₀ p b) : p 1 = 1 :=
  (h.eq_one_iff 1 (one_mem N)).2 (one_mem W₁)

theorem IsFieldModuleData.map_inv (h : IsFieldModuleData N W₁ S₀ p b) {x : G} (hx : x ∈ N) :
    p x⁻¹ = (p x)⁻¹ := by
  have h1 := h.map_mul x hx x⁻¹ (inv_mem hx)
  rw [mul_inv_cancel, h.map_one] at h1
  exact (eq_inv_of_mul_eq_one_right h1.symm)

theorem IsFieldModuleData.b_one (h : IsFieldModuleData N W₁ S₀ p b) : b 1 = 0 := by
  have h1 := h.add 1 (one_mem W₁) 1 (one_mem W₁)
  rw [one_mul] at h1
  have h2 : b 1 + b 1 = b 1 + 0 := by rw [add_zero, ← h1]
  exact (add_left_cancel h2)

theorem IsFieldModuleData.b_inv (h : IsFieldModuleData N W₁ S₀ p b) {w : G} (hw : w ∈ W₁) :
    b w⁻¹ = -b w := by
  have h1 := h.add w⁻¹ (inv_mem hw) w hw
  rw [inv_mul_cancel, h.b_one] at h1
  exact eq_neg_of_add_eq_zero_left h1.symm

theorem IsFieldModuleData.exists_mem_sZero (h : IsFieldModuleData N W₁ S₀ p b)
    {u : SpecialLinearGroup (Fin 4) F} (hu : u ∈ LinearFlag.unitriangular 4 F) :
    ∃ x ∈ S₀, p x = u := by
  obtain ⟨x, hxN, hx⟩ := h.surj u
  exact ⟨x, (h.mem_sZero_iff x hxN).2 (hx ▸ hu), hx⟩

end Data

section Position

variable {G : Type*} [Group G] {F : Type*} [Field F]
variable {N W₁ W₂ S₀ : Subgroup G} {p : G → SpecialLinearGroup (Fin 4) F} {b : G → Fin 4 → F}

theorem IsFieldModuleData.exists_conj_eq_vecMul (h : IsFieldModuleData N W₁ S₀ p b)
    (hS₀W₂ : S₀ ≤ normalizer (W₂ : Set G)) {z : G} (hz : z ∈ W₁ ⊓ W₂)
    {u : SpecialLinearGroup (Fin 4) F} (hu : u ∈ LinearFlag.unitriangular 4 F) :
    ∃ z' ∈ W₁ ⊓ W₂, b z' = b z ᵥ* (u : Matrix (Fin 4) (Fin 4) F) := by
  obtain ⟨x, hxS, hxu⟩ := h.exists_mem_sZero (inv_mem hu)
  have hxN := h.sZero_le hxS
  refine ⟨x * z * x⁻¹, mem_inf.2 ⟨(mem_normalizer_iff.1 (h.le_normalizer hxN) z).1
    (mem_inf.1 hz).1, (mem_normalizer_iff.1 (hS₀W₂ hxS) z).1 (mem_inf.1 hz).2⟩, ?_⟩
  rw [h.act x hxN z (mem_inf.1 hz).1, hxu, inv_inv]

theorem vecMul_transvection_eq_add_single {n : ℕ} {i j : Fin n} (hij : i ≠ j) (a : F) (r : Fin n → F) :
    r ᵥ* ((SpecialLinearGroup.transvection hij a : SpecialLinearGroup (Fin n) F) :
      Matrix (Fin n) (Fin n) F) = r + Pi.single j (r i * a) := by
  funext k
  rw [SpecialLinearGroup.transvection_coe, Matrix.vecMul_add, Matrix.vecMul_one, Pi.add_apply,
    Pi.add_apply]
  congr 1
  simp only [vecMul, dotProduct, single_apply, mul_ite, mul_zero]
  rw [Finset.sum_eq_single i]
  · by_cases hk : j = k
    · subst hk
      simp
    · simp [hk, Ne.symm hk]
  · intro l _ hl
    simp [Ne.symm hl]
  · simp

theorem IsFieldModuleData.apply_castSucc_eq_zero [Finite G] (h : IsFieldModuleData N W₁ S₀ p b)
    (hF : Nat.card F = 4) (hS₀W₂ : S₀ ≤ normalizer (W₂ : Set G))
    (hZ : Nat.card (W₁ ⊓ W₂ : Subgroup G) ≤ 4) {z : G} (hz : z ∈ W₁ ⊓ W₂) (j : Fin 3) :
    b z j.castSucc = 0 := by
  have : Finite F := Nat.finite_of_card_ne_zero (by omega)
  by_contra hv
  have hlt : j.castSucc < Fin.last 3 := Fin.castSucc_lt_last j
  have hall : ∀ a : F, ∃ z' ∈ W₁ ⊓ W₂, b z' = Pi.single (Fin.last 3) a := by
    intro a
    obtain ⟨z₁, hz₁, hb₁⟩ := h.exists_conj_eq_vecMul hS₀W₂ hz
      (CFSG.LocalAnalysis.ComponentInitial.LinearFlag.transvection_mem_unitriangular hlt
        ((b z j.castSucc)⁻¹ * a))
    refine ⟨z⁻¹ * z₁, mul_mem (inv_mem hz) hz₁, ?_⟩
    rw [h.add _ (inv_mem (mem_inf.1 hz).1) _ (mem_inf.1 hz₁).1, h.b_inv (mem_inf.1 hz).1, hb₁,
      vecMul_transvection_eq_add_single, ← mul_assoc, mul_inv_cancel₀ hv, one_mul]
    abel
  choose g hgZ hgb using hall
  let f : Option F → (W₁ ⊓ W₂ : Subgroup G) := fun o => o.elim ⟨z, hz⟩ fun a => ⟨g a, hgZ a⟩
  have hf : Function.Injective f := by
    have hne : ∀ a : F, b z ≠ Pi.single (Fin.last 3) a := fun a hza => hv (by
      rw [hza, Pi.single_apply, ite_eq_right_iff.2 fun h => absurd h hlt.ne])
    have hb : ∀ o, b (f o : G) = o.elim (b z) fun a : F => (Pi.single (Fin.last 3) a : Fin 4 → F) := by
      rintro (_ | a)
      · rfl
      · exact hgb a
    intro o o' hoo
    have h1 := congrArg (fun y : (W₁ ⊓ W₂ : Subgroup G) => b (y : G)) hoo
    simp only [hb] at h1
    rcases o with _ | a <;> rcases o' with _ | a'
    · rfl
    · exact absurd h1 (hne a')
    · exact absurd h1.symm (hne a)
    · have h2 := congrFun h1 (Fin.last 3)
      simp only [Option.elim, Pi.single_eq_same] at h2
      rw [h2]
  have h5 := Nat.card_le_card_of_injective f hf
  rw [Finite.card_option, hF] at h5
  omega

theorem IsFieldModuleData.isColRadical [Finite G] (h : IsFieldModuleData N W₁ S₀ p b)
    (hF : Nat.card F = 4) (hW₂S₀ : W₂ ≤ S₀) (hS₀W₂ : S₀ ≤ normalizer (W₂ : Set G))
    (hZ : Nat.card (W₁ ⊓ W₂ : Subgroup G) ≤ 4) {w : G} (hw : w ∈ W₂) :
    IsColRadical (p w : Matrix (Fin 4) (Fin 4) F) := by
  have hwS := hW₂S₀ hw
  have hwN := h.sZero_le hwS
  refine ⟨fun i j => ?_, ((h.mem_sZero_iff w hwN).1 hwS).2 _⟩
  obtain ⟨w₁, hw₁, hb₁⟩ := h.surjB (Pi.single i 1)
  have hw₁S : w₁ ∈ S₀ := (h.mem_sZero_iff w₁ (h.wOne_le hw₁)).2
    (by rw [(h.eq_one_iff w₁ (h.wOne_le hw₁)).2 hw₁]; exact one_mem _)
  have hv : w⁻¹ * w₁ * w⁻¹⁻¹ ∈ W₁ :=
    (mem_normalizer_iff.1 (h.le_normalizer (inv_mem hwN)) w₁).1 hw₁
  have hzW₂ : w₁⁻¹ * (w⁻¹ * w₁ * w⁻¹⁻¹) ∈ W₂ := by
    have h1 : w₁⁻¹ * w⁻¹ * w₁⁻¹⁻¹ ∈ W₂ :=
      (mem_normalizer_iff.1 (hS₀W₂ (inv_mem hw₁S)) w⁻¹).1 (inv_mem hw)
    have h2 := mul_mem h1 hw
    rwa [show w₁⁻¹ * w⁻¹ * w₁⁻¹⁻¹ * w = w₁⁻¹ * (w⁻¹ * w₁ * w⁻¹⁻¹) by group] at h2
  have hz : w₁⁻¹ * (w⁻¹ * w₁ * w⁻¹⁻¹) ∈ W₁ ⊓ W₂ := mem_inf.2 ⟨mul_mem (inv_mem hw₁) hv, hzW₂⟩
  have h0 := h.apply_castSucc_eq_zero hF hS₀W₂ hZ hz j
  rw [h.add _ (inv_mem hw₁) _ hv, h.b_inv hw₁, h.act _ (inv_mem hwN) _ hw₁,
    h.map_inv hwN, inv_inv, hb₁, Pi.add_apply, Pi.neg_apply, single_one_vecMul] at h0
  have h1 : (p w : Matrix (Fin 4) (Fin 4) F) i j.castSucc =
      (Pi.single i (1 : F) : Fin 4 → F) j.castSucc := by
    change (p w : Matrix (Fin 4) (Fin 4) F).row i j.castSucc = _
    linear_combination h0
  rw [h1]
  by_cases hij : i = j.castSucc
  · subst hij
    rw [Pi.single_eq_same, one_apply_eq]
  · rw [Pi.single_eq_of_ne (Ne.symm hij), one_apply_ne hij]

theorem IsFieldModuleData.wTwo_count [Finite G] (h : IsFieldModuleData N W₁ S₀ p b)
    (hF : Nat.card F = 4) (hW₂S₀ : W₂ ≤ S₀) (hS₀W₂ : S₀ ≤ normalizer (W₂ : Set G))
    (hW₂c : Nat.card W₂ = 2 ^ 8) (hZ : Nat.card (W₁ ⊓ W₂ : Subgroup G) ≤ 4) :
    (∀ s : Fin 3 → F, ∃ w ∈ W₂, colRadVec (p w : Matrix (Fin 4) (Fin 4) F) = s) ∧
      Nat.card (W₁ ⊓ W₂ : Subgroup G) = 4 ∧
      ∀ a : F, ∃ z ∈ W₁ ⊓ W₂, b z = Pi.single (Fin.last 3) a := by
  have : Finite F := Nat.finite_of_card_ne_zero (by omega)
  have hcol := fun {w : G} (hw : w ∈ W₂) => h.isColRadical hF hW₂S₀ hS₀W₂ hZ hw
  have hW₂N : W₂ ≤ N := hW₂S₀.trans h.sZero_le
  let f : W₂ →* Multiplicative (Fin 3 → F) :=
    { toFun := fun w => Multiplicative.ofAdd (colRadVec (p w : Matrix (Fin 4) (Fin 4) F))
      map_one' := by
        change Multiplicative.ofAdd (colRadVec (p 1 : Matrix (Fin 4) (Fin 4) F)) = 1
        rw [h.map_one, Matrix.SpecialLinearGroup.coe_one]
        have h0 : colRadVec (1 : Matrix (Fin 4) (Fin 4) F) = 0 := by
          funext i
          rw [colRadVec, one_apply_ne (Fin.castSucc_lt_last i).ne, Pi.zero_apply]
        rw [h0]
        rfl
      map_mul' := fun x y => by
        change Multiplicative.ofAdd (colRadVec (p (x * y : G) : Matrix (Fin 4) (Fin 4) F)) =
          Multiplicative.ofAdd (colRadVec (p x : Matrix (Fin 4) (Fin 4) F) +
            colRadVec (p y : Matrix (Fin 4) (Fin 4) F))
        rw [h.map_mul _ (hW₂N x.2) _ (hW₂N y.2), Matrix.SpecialLinearGroup.coe_mul,
          ((hcol x.2).mul (hcol y.2)).2] }
  have hker : ∀ w : W₂, w ∈ f.ker ↔ (w : G) ∈ W₁ := by
    intro w
    rw [MonoidHom.mem_ker]
    change Multiplicative.ofAdd (colRadVec (p w : Matrix (Fin 4) (Fin 4) F)) = 1 ↔ _
    rw [← h.eq_one_iff _ (hW₂N w.2)]
    constructor
    · intro h1
      exact Subtype.ext ((hcol w.2).eq_one (congrArg Multiplicative.toAdd h1))
    · intro h1
      rw [h1, Matrix.SpecialLinearGroup.coe_one]
      have h0 : colRadVec (1 : Matrix (Fin 4) (Fin 4) F) = 0 := by
        funext i
        rw [colRadVec, one_apply_ne (Fin.castSucc_lt_last i).ne, Pi.zero_apply]
      rw [h0]
      rfl
  have hcardker : Nat.card f.ker = Nat.card (W₁ ⊓ W₂ : Subgroup G) := by
    have hk : f.ker = W₁.subgroupOf W₂ := by
      ext w
      rw [hker, mem_subgroupOf]
    rw [hk, ← Subgroup.card_map_of_injective W₂.subtype_injective, Subgroup.subgroupOf_map_subtype,
      inf_comm]
  have hcardF : Nat.card (Multiplicative (Fin 3 → F)) = 4 ^ 3 := by
    change Nat.card (Fin 3 → F) = 4 ^ 3
    rw [Nat.card_fun, hF, Nat.card_eq_fintype_card, Fintype.card_fin]
  have hrange : Nat.card f.range ≤ 4 ^ 3 := hcardF ▸ Subgroup.card_le_card_group _
  have hmul := Subgroup.card_ker_mul_card_range f
  rw [hcardker, hW₂c] at hmul
  have hZ4 : Nat.card (W₁ ⊓ W₂ : Subgroup G) = 4 := by
    have h1 : 2 ^ 8 ≤ Nat.card (W₁ ⊓ W₂ : Subgroup G) * 4 ^ 3 := by
      rw [← hmul]
      exact Nat.mul_le_mul_left _ hrange
    omega
  have htop : f.range = ⊤ := by
    apply Subgroup.eq_top_of_card_eq
    rw [hcardF]
    rw [hZ4] at hmul
    omega
  refine ⟨fun s => ?_, hZ4, fun a => ?_⟩
  · obtain ⟨w, hw⟩ := (MonoidHom.range_eq_top.1 htop) (Multiplicative.ofAdd s)
    exact ⟨w, w.2, congrArg Multiplicative.toAdd hw⟩
  ·
    let g : (W₁ ⊓ W₂ : Subgroup G) → F := fun z => b z (Fin.last 3)
    have hbz : ∀ z : (W₁ ⊓ W₂ : Subgroup G), b z = Pi.single (Fin.last 3) (g z) := by
      intro z
      funext k
      induction k using Fin.lastCases with
      | last => rw [Pi.single_eq_same]
      | cast j =>
        rw [h.apply_castSucc_eq_zero hF hS₀W₂ hZ z.2 j]
        exact (Pi.single_eq_of_ne (M := fun _ : Fin 4 => F) (Fin.castSucc_lt_last j).ne _).symm
    have hg : Function.Injective g := by
      intro z z' hzz
      apply Subtype.ext
      apply h.inj _ (mem_inf.1 z.2).1 _ (mem_inf.1 z'.2).1
      rw [hbz z, hbz z', hzz]
    have hgb : Function.Bijective g :=
      (Nat.bijective_iff_injective_and_card g).2 ⟨hg, by rw [hZ4, hF]⟩
    obtain ⟨z, hz⟩ := hgb.2 a
    exact ⟨z, z.2, by rw [hbz z, hz]⟩

end Position

end CFSG.SeitzReduction.LinearPilot
