module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec12L129JWr
public import CFSG.GroupTheory.ElemAbelianClosure
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec12L129JG

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Open

private theorem sec12W_inv_eq_self (a : Multiplicative (ZMod 2)) : a⁻¹ = a := by
  rcases sec12W_two_pts a with rfl | rfl
  · exact inv_one
  · exact inv_eq_of_mul_eq_one_right (by decide)

private theorem sec12W_comm_left_one {D : Type} [Group D] {x w : WrZ2 D} (hw : w.right = 1)
    (hxs : x.right = Multiplicative.ofAdd 1) (hcomm : w * x = x * w) :
    w.left (Multiplicative.ofAdd 1) = (x.left 1)⁻¹ * w.left 1 * x.left 1 := by
  have h := congrArg (fun z : WrZ2 D => z.left 1) hcomm
  rw [RegularWreathProduct.mul_left, RegularWreathProduct.mul_left] at h
  change w.left 1 * x.left (w.right⁻¹ * 1) = x.left 1 * w.left (x.right⁻¹ * 1) at h
  have hwr : w.right⁻¹ * 1 = 1 := by
    rw [hw]
    exact (congrArg (fun a : Multiplicative (ZMod 2) => a * 1) inv_one).trans (one_mul 1)
  have hxr : x.right⁻¹ * 1 = Multiplicative.ofAdd 1 := by
    rw [hxs, sec12W_inv_eq_self]
    exact mul_one _
  rw [hwr, hxr] at h
  have h2 : (x.left 1)⁻¹ * (w.left 1 * x.left 1) = w.left (Multiplicative.ofAdd 1) := by
    rw [h, ← mul_assoc, inv_mul_cancel, one_mul]
  calc w.left (Multiplicative.ofAdd 1)
      = (x.left 1)⁻¹ * (w.left 1 * x.left 1) := h2.symm
    _ = (x.left 1)⁻¹ * w.left 1 * x.left 1 := (mul_assoc _ _ _).symm

private theorem sec12W_card_subgroupOf {G : Type*} [Group G] (H K : Subgroup G) :
    Nat.card (H.subgroupOf K) = Nat.card (K ⊓ H : Subgroup G) :=
  Nat.card_congr
    { toFun := fun x => ⟨x.1.1, x.1.2, x.2⟩
      invFun := fun y => ⟨⟨y.1, y.2.1⟩, y.2.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }

private theorem sec12W_two_pow_eq_sixteen {n : ℕ} (h1 : 8 < 2 ^ n) (h2 : 2 ^ n ≤ 16) :
    2 ^ n = 16 := by
  have hgt : 3 < n :=
    (Nat.pow_lt_pow_iff_right (by norm_num : 1 < (2:ℕ))).mp (show (8 : ℕ) < 2 ^ n from h1)
  have hle : n ≤ 4 :=
    (Nat.pow_le_pow_iff_right (by norm_num : 1 < (2:ℕ))).mp (show 2 ^ n ≤ (16 : ℕ) from h2)
  have hn : n = 4 := by omega
  rw [hn]
  norm_num

private theorem sec12W_two_pow_ge_256 {n : ℕ} (h : 128 < 2 ^ n) : 256 ≤ 2 ^ n := by
  have hn : 7 < n :=
    (Nat.pow_lt_pow_iff_right (by norm_num : 1 < (2:ℕ))).mp (show (128 : ℕ) < 2 ^ n from h)
  have h8 : 2 ^ 8 ≤ 2 ^ n :=
    (Nat.pow_le_pow_iff_right (by norm_num : 1 < (2:ℕ))).mpr (show 8 ≤ n by omega)
  simpa using h8

theorem sec12W_elemAb {D : Type} [Group D] [Finite D] (B : Subgroup D) (hB : Nat.card B = 16)
    (h16 : ∀ P : Subgroup D, IsElemAbelian 2 P → Nat.card P ≤ 16)
    (hBeq : ∀ P : Subgroup D, IsElemAbelian 2 P → Nat.card P = 16 → P = B)
    {X : Subgroup (WrZ2 D)} (hX : IsElemAbelian 2 X) :
    Nat.card X ≤ 128 ∨ X = sec12W_base B := by
  let K : Subgroup (WrZ2 D) :=
    (RegularWreathProduct.rightHom : WrZ2 D →* Multiplicative (ZMod 2)).ker
  have hZ2card : Nat.card (Multiplicative (ZMod 2)) = 2 := by
    rw [Nat.card_congr (Multiplicative.toAdd : Multiplicative (ZMod 2) ≃ ZMod 2),
      Nat.card_zmod]
  by_cases hXK : X ≤ K
  ·
    let P1 : Subgroup D := (X.subgroupOf K).map (sec12W_proj (1 : Multiplicative (ZMod 2)))
    let Ps : Subgroup D := (X.subgroupOf K).map (sec12W_proj (Multiplicative.ofAdd 1))
    have hX'' : IsElemAbelian 2 (X.subgroupOf K) := hX.subgroupOf K
    have hP1 : IsElemAbelian 2 P1 := hX''.map _
    have hPs : IsElemAbelian 2 Ps := hX''.map _
    have hP1le : Nat.card P1 ≤ 16 := h16 P1 hP1
    have hPsle : Nat.card Ps ≤ 16 := h16 Ps hPs
    have hXcard : Nat.card (X.subgroupOf K) = Nat.card X :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hXK).toEquiv
    have hle_prod : Nat.card X ≤ Nat.card P1 * Nat.card Ps := by
      rw [← hXcard, ← Nat.card_prod]
      refine Nat.card_le_card_of_injective
        (fun w : X.subgroupOf K =>
          (⟨sec12W_proj (1 : Multiplicative (ZMod 2)) w,
              Subgroup.mem_map_of_mem (sec12W_proj (1 : Multiplicative (ZMod 2))) w.2⟩,
            ⟨sec12W_proj (Multiplicative.ofAdd 1) w,
              Subgroup.mem_map_of_mem (sec12W_proj (Multiplicative.ofAdd 1)) w.2⟩)) ?_
      intro a b hab
      apply Subtype.ext
      apply Subtype.ext
      apply sec12W_ext
      · exact MonoidHom.mem_ker.mp a.1.2
      · exact MonoidHom.mem_ker.mp b.1.2
      · have h := congrArg (fun z : P1 × Ps => (z.1 : D)) hab
        simpa [sec12W_proj_apply] using h
      · have h := congrArg (fun z : P1 × Ps => (z.2 : D)) hab
        simpa [sec12W_proj_apply] using h
    rcases le_or_gt (Nat.card X) 128 with hle128 | hlt128
    · exact Or.inl hle128
    · right
      obtain ⟨n1, hn1⟩ := sec12J_card_two_pow hP1
      obtain ⟨ns, hns⟩ := sec12J_card_two_pow hPs
      have hprod_gt : 128 < Nat.card P1 * Nat.card Ps := lt_of_lt_of_le hlt128 hle_prod
      have hP1gt : 8 < Nat.card P1 := by
        by_contra h
        push Not at h
        have : Nat.card P1 * Nat.card Ps ≤ 8 * 16 := Nat.mul_le_mul h hPsle
        omega
      have hPsgt : 8 < Nat.card Ps := by
        by_contra h
        push Not at h
        have : Nat.card P1 * Nat.card Ps ≤ 16 * 8 := Nat.mul_le_mul hP1le h
        omega
      have hP1card : Nat.card P1 = 16 :=
        hn1.trans (sec12W_two_pow_eq_sixteen (hn1 ▸ hP1gt) (hn1 ▸ hP1le))
      have hPscard : Nat.card Ps = 16 :=
        hns.trans (sec12W_two_pow_eq_sixteen (hns ▸ hPsgt) (hns ▸ hPsle))
      have hP1B : P1 = B := hBeq P1 hP1 hP1card
      have hPsB : Ps = B := hBeq Ps hPs hPscard
      have hXbase : X ≤ sec12W_base B := by
        intro w hw
        rw [mem_sec12W_base]
        refine ⟨MonoidHom.mem_ker.mp (hXK hw), fun x => ?_⟩
        rcases sec12W_two_pts x with rfl | rfl
        · have hmem : sec12W_proj (1 : Multiplicative (ZMod 2))
              (⟨w, hXK hw⟩ : ↥K) ∈ P1 :=
            Subgroup.mem_map_of_mem _ (show (⟨w, hXK hw⟩ : ↥K) ∈ X.subgroupOf K from hw)
          rw [sec12W_proj_apply, hP1B] at hmem
          exact hmem
        · have hmem : sec12W_proj (Multiplicative.ofAdd 1)
              (⟨w, hXK hw⟩ : ↥K) ∈ Ps :=
            Subgroup.mem_map_of_mem _ (show (⟨w, hXK hw⟩ : ↥K) ∈ X.subgroupOf K from hw)
          rw [sec12W_proj_apply, hPsB] at hmem
          exact hmem
      have hbasecard : Nat.card (sec12W_base B) ≤ 256 := by
        have h := sec12W_card_base_le (D := D) B
        rw [hB] at h
        omega
      have hXge : 256 ≤ Nat.card X := by
        obtain ⟨n, hn⟩ := sec12J_card_two_pow hX
        rw [hn] at hlt128 ⊢
        exact sec12W_two_pow_ge_256 hlt128
      exact Subgroup.eq_of_le_of_card_ge hXbase (hbasecard.trans hXge)
  ·
    rw [IsConcreteLE.not_le_iff_exists] at hXK
    obtain ⟨x0, hx0X, hx0K⟩ := hXK
    have hx0right : x0.right ≠ 1 := by
      intro h
      exact hx0K (show x0 ∈ K from MonoidHom.mem_ker.mpr h)
    have hx0s : x0.right = Multiplicative.ofAdd 1 := by
      rcases sec12W_two_pts x0.right with h | h
      · exact absurd h hx0right
      · exact h
    let P1 : Subgroup D := (X.subgroupOf K).map (sec12W_proj (1 : Multiplicative (ZMod 2)))
    have hP1 : IsElemAbelian 2 P1 := (hX.subgroupOf K).map _
    have hinj : Function.Injective
        (fun w : X.subgroupOf K =>
          (⟨sec12W_proj (1 : Multiplicative (ZMod 2)) w,
            Subgroup.mem_map_of_mem (sec12W_proj (1 : Multiplicative (ZMod 2))) w.2⟩ : P1)) := by
      intro a b hab
      apply Subtype.ext
      apply Subtype.ext
      apply sec12W_ext
      · exact MonoidHom.mem_ker.mp a.1.2
      · exact MonoidHom.mem_ker.mp b.1.2
      · have h := congrArg (fun z : P1 => (z : D)) hab
        simpa [sec12W_proj_apply] using h
      · have hab' : a.1.1.left 1 = b.1.1.left 1 := by
          have h := congrArg (fun z : P1 => (z : D)) hab
          simpa [sec12W_proj_apply] using h
        have haf := sec12W_comm_left_one (x := x0) (w := a.1.1)
          (MonoidHom.mem_ker.mp a.1.2) hx0s (hX.comm a.2 hx0X)
        have hbf := sec12W_comm_left_one (x := x0) (w := b.1.1)
          (MonoidHom.mem_ker.mp b.1.2) hx0s (hX.comm b.2 hx0X)
        rw [haf, hbf, hab']
    have hcardX'' : Nat.card (X.subgroupOf K) ≤ 16 :=
      (Nat.card_le_card_of_injective _ hinj).trans (h16 P1 hP1)
    have hcard_inf : Nat.card (X ⊓ K : Subgroup (WrZ2 D)) ≤ 16 := by
      rw [show (X ⊓ K : Subgroup (WrZ2 D)) = K ⊓ X from inf_comm X K,
        ← sec12W_card_subgroupOf X K]
      exact hcardX''
    refine Or.inl ?_
    have hcardX : Nat.card X = Nat.card (X ⊓ K : Subgroup (WrZ2 D)) *
        Nat.card (X.map (RegularWreathProduct.rightHom : WrZ2 D →* Multiplicative (ZMod 2))) :=
      (sec12J_card_inf_ker_mul
        (RegularWreathProduct.rightHom : WrZ2 D →* Multiplicative (ZMod 2)) X).symm
    rw [hcardX]
    have hmap_le : Nat.card (X.map
        (RegularWreathProduct.rightHom : WrZ2 D →* Multiplicative (ZMod 2))) ≤ 2 :=
      calc Nat.card (X.map (RegularWreathProduct.rightHom : WrZ2 D →* Multiplicative (ZMod 2)))
          ≤ Nat.card (Multiplicative (ZMod 2)) := Subgroup.card_le_card_group _
        _ = 2 := hZ2card
    have := Nat.mul_le_mul hcard_inf hmap_le
    omega

end CFSG.OddStandard.SmallF3.Omega
