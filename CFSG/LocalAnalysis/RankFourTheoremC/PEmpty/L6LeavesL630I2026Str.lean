module

public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesL630AutQ8D8Center
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesL630Group

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L630.I2026

open CFSG.LocalAnalysis.RankThreeTheoremC (smallRankIsQ8D8)
open CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L630.AutQ8D8

theorem quat_sq (x : QuaternionGroup 2) : x * x = 1 ∨ x * x = QuaternionGroup.a 2 := by
  revert x
  decide

theorem quat_comm (x y : QuaternionGroup 2) :
    x * y * x⁻¹ * y⁻¹ = 1 ∨ x * y * x⁻¹ * y⁻¹ = QuaternionGroup.a 2 := by
  revert x y
  decide

theorem dih_sq (x : DihedralGroup 4) : x * x = 1 ∨ x * x = DihedralGroup.r 2 := by
  revert x
  decide

theorem dih_comm (x y : DihedralGroup 4) :
    x * y * x⁻¹ * y⁻¹ = 1 ∨ x * y * x⁻¹ * y⁻¹ = DihedralGroup.r 2 := by
  revert x y
  decide

theorem quat_rel :
    (QuaternionGroup.a 1 : QuaternionGroup 2) * QuaternionGroup.a 1 = QuaternionGroup.a 2 ∧
    (QuaternionGroup.xa 0 : QuaternionGroup 2) * QuaternionGroup.xa 0 = QuaternionGroup.a 2 ∧
    (QuaternionGroup.xa 0 : QuaternionGroup 2) * QuaternionGroup.a 1 =
      QuaternionGroup.a 2 * (QuaternionGroup.a 1 * QuaternionGroup.xa 0) ∧
    (QuaternionGroup.a 2 : QuaternionGroup 2) * QuaternionGroup.a 2 = 1 := by
  decide

theorem dih_rel :
    (DihedralGroup.r 1 : DihedralGroup 4) * DihedralGroup.r 1 = DihedralGroup.r 2 ∧
    (DihedralGroup.sr 0 : DihedralGroup 4) * DihedralGroup.sr 0 = 1 ∧
    (DihedralGroup.sr 0 : DihedralGroup 4) * DihedralGroup.r 1 =
      DihedralGroup.r 2 * (DihedralGroup.r 1 * DihedralGroup.sr 0) := by
  decide

theorem quat_closure :
    Subgroup.closure ({QuaternionGroup.a 1, QuaternionGroup.xa 0} :
      Set (QuaternionGroup 2)) = ⊤ := by
  rw [eq_top_iff]
  intro x _
  have hA : ∀ k : ℕ, (QuaternionGroup.a (k : ZMod (2 * 2)) : QuaternionGroup 2) ∈
      Subgroup.closure ({QuaternionGroup.a 1, QuaternionGroup.xa 0} :
        Set (QuaternionGroup 2)) := by
    intro k
    rw [← QuaternionGroup.a_one_pow]
    exact Subgroup.pow_mem _ (Subgroup.subset_closure (by simp)) k
  have hX : (QuaternionGroup.xa 0 : QuaternionGroup 2) ∈
      Subgroup.closure ({QuaternionGroup.a 1, QuaternionGroup.xa 0} :
        Set (QuaternionGroup 2)) :=
    Subgroup.subset_closure (by simp)
  cases x with
  | a i => simpa using hA i.val
  | xa i =>
    have h1 := Subgroup.mul_mem _ hX (hA i.val)
    rw [QuaternionGroup.xa_mul_a] at h1
    simpa using h1

theorem dih_closure :
    Subgroup.closure ({DihedralGroup.r 1, DihedralGroup.sr 0} : Set (DihedralGroup 4)) = ⊤ := by
  rw [eq_top_iff]
  intro x _
  have hA : ∀ k : ℕ, (DihedralGroup.r (k : ZMod 4) : DihedralGroup 4) ∈
      Subgroup.closure ({DihedralGroup.r 1, DihedralGroup.sr 0} : Set (DihedralGroup 4)) := by
    intro k
    rw [← DihedralGroup.r_one_pow]
    exact Subgroup.pow_mem _ (Subgroup.subset_closure (by simp)) k
  have hX : (DihedralGroup.sr 0 : DihedralGroup 4) ∈
      Subgroup.closure ({DihedralGroup.r 1, DihedralGroup.sr 0} : Set (DihedralGroup 4)) :=
    Subgroup.subset_closure (by simp)
  cases x with
  | r i => simpa using hA i.val
  | sr i =>
    have h1 := Subgroup.mul_mem _ hX (hA i.val)
    rw [DihedralGroup.sr_mul_r] at h1
    simpa using h1

theorem exists_mul_of_comm_sup {G : Type*} [Group G] {A B : Subgroup G}
    (hcomm : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a) {s : G} (hs : s ∈ A ⊔ B) :
    ∃ a ∈ A, ∃ b ∈ B, s = a * b := by
  rw [Subgroup.sup_eq_closure] at hs
  refine Subgroup.closure_induction ?_ ?_ ?_ ?_ hs
  · rintro y (h | h)
    · exact ⟨y, h, 1, B.one_mem, (mul_one y).symm⟩
    · exact ⟨1, A.one_mem, y, h, (one_mul y).symm⟩
  · exact ⟨1, A.one_mem, 1, B.one_mem, (mul_one 1).symm⟩
  · rintro _ _ _ _ ⟨a₁, ha₁, b₁, hb₁, rfl⟩ ⟨a₂, ha₂, b₂, hb₂, rfl⟩
    refine ⟨a₁ * a₂, A.mul_mem ha₁ ha₂, b₁ * b₂, B.mul_mem hb₁ hb₂, ?_⟩
    calc a₁ * b₁ * (a₂ * b₂) = a₁ * (b₁ * a₂) * b₂ := by simp only [mul_assoc]
      _ = a₁ * (a₂ * b₁) * b₂ := by rw [hcomm a₂ ha₂ b₁ hb₁]
      _ = a₁ * a₂ * (b₁ * b₂) := by simp only [mul_assoc]
  · rintro _ _ ⟨a, ha, b, hb, rfl⟩
    refine ⟨a⁻¹, A.inv_mem ha, b⁻¹, B.inv_mem hb, ?_⟩
    rw [mul_inv_rev]
    exact (hcomm a⁻¹ (A.inv_mem ha) b⁻¹ (B.inv_mem hb)).symm

@[expose] def prodHom {G : Type*} [Group G] {A B : Subgroup G}
    (hcomm : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a) : (↥A × ↥B) →* G where
  toFun p := (p.1 : G) * (p.2 : G)
  map_one' := by simp
  map_mul' := by
    rintro ⟨a₁, b₁⟩ ⟨a₂, b₂⟩
    simp only [Prod.mk_mul_mk, Subgroup.coe_mul, mul_assoc]
    rw [← mul_assoc (a₂ : G) (b₁ : G) (b₂ : G), hcomm (a₂ : G) a₂.2 (b₁ : G) b₁.2]
    simp only [mul_assoc]

theorem prodHom_apply {G : Type*} [Group G] {A B : Subgroup G}
    (hcomm : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a) (p : ↥A × ↥B) :
    prodHom hcomm p = (p.1 : G) * (p.2 : G) :=
  rfl

theorem coe_symm_mul {G R : Type*} [Group G] [Group R] {A : Subgroup G} (e : ↥A ≃* R)
    (p q : R) : ((e.symm p : ↥A) : G) * ((e.symm q : ↥A) : G) = ((e.symm (p * q) : ↥A) : G) := by
  rw [map_mul, Subgroup.coe_mul]

structure QDPres {G : Type*} [Group G] (S : Subgroup G) (α β γ δ z : G) : Prop where
  α_mem : α ∈ S
  β_mem : β ∈ S
  γ_mem : γ ∈ S
  δ_mem : δ ∈ S
  z_mem : z ∈ S
  αα : α * α = z
  ββ : β * β = z
  γγ : γ * γ = z
  δδ : δ * δ = 1
  zz : z * z = 1
  βα : β * α = z * (α * β)
  δγ : δ * γ = z * (γ * δ)
  αγ : α * γ = γ * α
  αδ : α * δ = δ * α
  βγ : β * γ = γ * β
  βδ : β * δ = δ * β
  z_ne : z ≠ 1
  z_central : ∀ s ∈ S, z * s = s * z
  gen : S = Subgroup.closure ({α, β, γ, δ} : Set G)
  card : Nat.card S = 32
  center : ∀ s ∈ S, (∀ t ∈ S, s * t = t * s) → s = 1 ∨ s = z
  sq : ∀ s ∈ S, s * s = 1 ∨ s * s = z
  comm : ∀ s ∈ S, ∀ t ∈ S, s * t * s⁻¹ * t⁻¹ = 1 ∨ s * t * s⁻¹ * t⁻¹ = z

theorem exists_pres {G : Type} [Group G] {S : Subgroup G} (hS : smallRankIsQ8D8 S) :
    ∃ α β γ δ z : G, QDPres S α β γ δ z := by
  have hS' : smallRankIsQ8D8 (⊤ : Subgroup ↥S) :=
    smallRankIsQ8D8_of_map S.subtype S.subtype_injective (by
      rw [show (⊤ : Subgroup ↥S).map S.subtype = S by
        rw [← MonoidHom.range_eq_map, Subgroup.range_subtype]]
      exact hS)
  obtain ⟨A₂, B₂, ⟨eA₂⟩, ⟨eB₂⟩, hcomm₂, hsup₂, hAB₂⟩ := hS'
  have hcard : Nat.card ↥S = 32 := natCard_eq_thirtyTwo eA₂ eB₂ hcomm₂ hsup₂ hAB₂
  obtain ⟨A, B, ⟨eA⟩, ⟨eB⟩, hcomm, hsup, hAB⟩ := hS
  have hAS : A ≤ S := hsup ▸ le_sup_left
  have hBS : B ≤ S := hsup ▸ le_sup_right
  obtain ⟨c, hc1⟩ := exists_ne_one_of_natCard_eq_two hAB
  have hcA : (c : G) ∈ A := (Subgroup.mem_inf.mp c.2).1
  have hcB : (c : G) ∈ B := (Subgroup.mem_inf.mp c.2).2
  have hc1' : (c : G) ≠ 1 := fun h => hc1 (Subtype.ext h)
  let cA : ↥A := ⟨c, hcA⟩
  let cB : ↥B := ⟨c, hcB⟩
  have hcA1 : cA ≠ 1 := fun h => hc1' (congrArg Subtype.val h)
  have hcB1 : cB ≠ 1 := fun h => hc1' (congrArg Subtype.val h)
  have hcAcent : ∀ y : ↥A, y * cA = cA * y := fun y =>
    Subtype.ext (hcomm (y : G) y.2 (c : G) hcB)
  have hcBcent : ∀ y : ↥B, y * cB = cB * y := fun y =>
    Subtype.ext (hcomm (c : G) hcA (y : G) y.2).symm
  have hcA2 : eA cA = QuaternionGroup.a 2 := by
    rcases quaternion_central_eq (eA cA) (central_transfer eA cA hcAcent) with h | h
    · exact absurd (eA.injective (by rw [h, map_one])) hcA1
    · exact h
  have hcB2 : eB cB = DihedralGroup.r 2 := by
    rcases dihedral_central_eq (eB cB) (central_transfer eB cB hcBcent) with h | h
    · exact absurd (eB.injective (by rw [h, map_one])) hcB1
    · exact h
  have hsA : eA.symm (QuaternionGroup.a 2) = cA := eA.symm_apply_eq.mpr hcA2.symm
  have hsB : eB.symm (DihedralGroup.r 2) = cB := eB.symm_apply_eq.mpr hcB2.symm
  have hzA : ((eA.symm (QuaternionGroup.a 2) : ↥A) : G) = (c : G) := by rw [hsA]
  have hzB : ((eB.symm (DihedralGroup.r 2) : ↥B) : G) = (c : G) := by rw [hsB]
  obtain ⟨qa1, qa2, qa3, qa4⟩ := quat_rel
  obtain ⟨db1, db2, db3⟩ := dih_rel
  have hclA : Subgroup.closure ({((eA.symm (QuaternionGroup.a 1) : ↥A) : G),
      ((eA.symm (QuaternionGroup.xa 0) : ↥A) : G)} : Set G) = A := by
    let f : QuaternionGroup 2 →* G := A.subtype.comp eA.symm.toMonoidHom
    have h1 := MonoidHom.map_closure f ({QuaternionGroup.a 1, QuaternionGroup.xa 0} :
      Set (QuaternionGroup 2))
    rw [quat_closure, Set.image_pair] at h1
    have h2 : (⊤ : Subgroup (QuaternionGroup 2)).map f = A := by
      rw [← MonoidHom.range_eq_map]
      ext x
      constructor
      · rintro ⟨q, rfl⟩
        exact (eA.symm q).2
      · intro hx
        exact ⟨eA ⟨x, hx⟩, by simp [f]⟩
    rw [h2] at h1
    exact h1.symm
  have hclB : Subgroup.closure ({((eB.symm (DihedralGroup.r 1) : ↥B) : G),
      ((eB.symm (DihedralGroup.sr 0) : ↥B) : G)} : Set G) = B := by
    let f : DihedralGroup 4 →* G := B.subtype.comp eB.symm.toMonoidHom
    have h1 := MonoidHom.map_closure f ({DihedralGroup.r 1, DihedralGroup.sr 0} :
      Set (DihedralGroup 4))
    rw [dih_closure, Set.image_pair] at h1
    have h2 : (⊤ : Subgroup (DihedralGroup 4)).map f = B := by
      rw [← MonoidHom.range_eq_map]
      ext x
      constructor
      · rintro ⟨q, rfl⟩
        exact (eB.symm q).2
      · intro hx
        exact ⟨eB ⟨x, hx⟩, by simp [f]⟩
    rw [h2] at h1
    exact h1.symm
  have hgen : S = Subgroup.closure ({((eA.symm (QuaternionGroup.a 1) : ↥A) : G),
      ((eA.symm (QuaternionGroup.xa 0) : ↥A) : G), ((eB.symm (DihedralGroup.r 1) : ↥B) : G),
      ((eB.symm (DihedralGroup.sr 0) : ↥B) : G)} : Set G) := by
    calc S = A ⊔ B := hsup.symm
      _ = Subgroup.closure ({((eA.symm (QuaternionGroup.a 1) : ↥A) : G),
          ((eA.symm (QuaternionGroup.xa 0) : ↥A) : G)} : Set G) ⊔
          Subgroup.closure ({((eB.symm (DihedralGroup.r 1) : ↥B) : G),
          ((eB.symm (DihedralGroup.sr 0) : ↥B) : G)} : Set G) := by rw [hclA, hclB]
      _ = Subgroup.closure (({((eA.symm (QuaternionGroup.a 1) : ↥A) : G),
          ((eA.symm (QuaternionGroup.xa 0) : ↥A) : G)} : Set G) ∪
          {((eB.symm (DihedralGroup.r 1) : ↥B) : G),
          ((eB.symm (DihedralGroup.sr 0) : ↥B) : G)}) := (Subgroup.closure_union _ _).symm
      _ = _ := by
        congr 1
        ext x
        simp only [Set.mem_union, Set.mem_insert_iff, Set.mem_singleton_iff]
        tauto
  have hsqA : ∀ a ∈ A, a * a = 1 ∨ a * a = (c : G) := by
    intro a ha
    have h1 : ((eA.symm (eA ⟨a, ha⟩) : ↥A) : G) = a := by simp
    rw [← h1, coe_symm_mul eA]
    rcases quat_sq (eA ⟨a, ha⟩) with h | h
    · left
      rw [h, map_one]
      rfl
    · right
      rw [h, hzA]
  have hsqB : ∀ b ∈ B, b * b = 1 ∨ b * b = (c : G) := by
    intro b hb
    have h1 : ((eB.symm (eB ⟨b, hb⟩) : ↥B) : G) = b := by simp
    rw [← h1, coe_symm_mul eB]
    rcases dih_sq (eB ⟨b, hb⟩) with h | h
    · left
      rw [h, map_one]
      rfl
    · right
      rw [h, hzB]
  have hcommA : ∀ a ∈ A, ∀ a' ∈ A, a * a' * a⁻¹ * a'⁻¹ = 1 ∨ a * a' * a⁻¹ * a'⁻¹ = (c : G) := by
    intro a ha a' ha'
    have e1 : ((eA.symm (eA ⟨a, ha⟩) : ↥A) : G) = a := by simp
    have e2 : ((eA.symm (eA ⟨a', ha'⟩) : ↥A) : G) = a' := by simp
    have h3 : a * a' * a⁻¹ * a'⁻¹ =
        ((eA.symm (eA ⟨a, ha⟩ * eA ⟨a', ha'⟩ * (eA ⟨a, ha⟩)⁻¹ * (eA ⟨a', ha'⟩)⁻¹) : ↥A) : G) := by
      simp only [map_mul, map_inv, Subgroup.coe_mul, Subgroup.coe_inv, MulEquiv.symm_apply_apply]
    rw [h3]
    rcases quat_comm (eA ⟨a, ha⟩) (eA ⟨a', ha'⟩) with h | h
    · left
      rw [h, map_one]
      rfl
    · right
      rw [h, hzA]
  have hcommB : ∀ b ∈ B, ∀ b' ∈ B, b * b' * b⁻¹ * b'⁻¹ = 1 ∨ b * b' * b⁻¹ * b'⁻¹ = (c : G) := by
    intro b hb b' hb'
    have h3 : b * b' * b⁻¹ * b'⁻¹ =
        ((eB.symm (eB ⟨b, hb⟩ * eB ⟨b', hb'⟩ * (eB ⟨b, hb⟩)⁻¹ * (eB ⟨b', hb'⟩)⁻¹) : ↥B) : G) := by
      simp only [map_mul, map_inv, Subgroup.coe_mul, Subgroup.coe_inv, MulEquiv.symm_apply_apply]
    rw [h3]
    rcases dih_comm (eB ⟨b, hb⟩) (eB ⟨b', hb'⟩) with h | h
    · left
      rw [h, map_one]
      rfl
    · right
      rw [h, hzB]
  have hzz : (c : G) * (c : G) = 1 := by
    rw [← hzA, coe_symm_mul eA, qa4, map_one]
    rfl
  have hz_central : ∀ s ∈ S, (c : G) * s = s * (c : G) := by
    intro s hs
    obtain ⟨a, ha, b, hb, rfl⟩ := exists_mul_of_comm_sup hcomm (hsup ▸ hs)
    have h1 : (c : G) * a = a * (c : G) := by
      have := hcAcent ⟨a, ha⟩
      exact (congrArg Subtype.val this).symm
    have h2 : (c : G) * b = b * (c : G) := hcomm (c : G) hcA b hb
    calc (c : G) * (a * b) = (c * a) * b := by rw [mul_assoc]
      _ = (a * c) * b := by rw [h1]
      _ = a * (c * b) := by rw [mul_assoc]
      _ = a * (b * c) := by rw [h2]
      _ = a * b * c := by rw [mul_assoc]
  refine ⟨((eA.symm (QuaternionGroup.a 1) : ↥A) : G), ((eA.symm (QuaternionGroup.xa 0) : ↥A) : G),
    ((eB.symm (DihedralGroup.r 1) : ↥B) : G), ((eB.symm (DihedralGroup.sr 0) : ↥B) : G),
    (c : G), ?_⟩
  exact
    { α_mem := hAS (eA.symm _).2
      β_mem := hAS (eA.symm _).2
      γ_mem := hBS (eB.symm _).2
      δ_mem := hBS (eB.symm _).2
      z_mem := hAS hcA
      αα := by rw [coe_symm_mul eA, qa1, hzA]
      ββ := by rw [coe_symm_mul eA, qa2, hzA]
      γγ := by rw [coe_symm_mul eB, db1, hzB]
      δδ := by rw [coe_symm_mul eB, db2, map_one]; rfl
      zz := hzz
      βα := by
        rw [← hzA, coe_symm_mul eA, coe_symm_mul eA, coe_symm_mul eA, qa3]
      δγ := by
        rw [← hzB, coe_symm_mul eB, coe_symm_mul eB, coe_symm_mul eB, db3]
      αγ := hcomm _ (eA.symm _).2 _ (eB.symm _).2
      αδ := hcomm _ (eA.symm _).2 _ (eB.symm _).2
      βγ := hcomm _ (eA.symm _).2 _ (eB.symm _).2
      βδ := hcomm _ (eA.symm _).2 _ (eB.symm _).2
      z_ne := hc1'
      z_central := hz_central
      gen := hgen
      card := hcard
      center := by
        intro s hs hsc
        obtain ⟨a, ha, b, hb, rfl⟩ := exists_mul_of_comm_sup hcomm (hsup ▸ hs)
        have hac : ∀ a' ∈ A, a' * a = a * a' := by
          intro a' ha'
          have h1 : a' * (a * b) = a * b * a' := (hsc a' (hAS ha')).symm
          have h2 : b * a' = a' * b := (hcomm a' ha' b hb).symm
          have h3 : a' * a * b = a * a' * b := by
            calc a' * a * b = a' * (a * b) := by rw [mul_assoc]
              _ = a * b * a' := h1
              _ = a * (b * a') := by rw [mul_assoc]
              _ = a * (a' * b) := by rw [h2]
              _ = a * a' * b := by rw [mul_assoc]
          exact mul_right_cancel h3
        have hbc : ∀ b' ∈ B, b' * b = b * b' := by
          intro b' hb'
          have h1 : b' * (a * b) = a * b * b' := (hsc b' (hBS hb')).symm
          have h3 : a * (b' * b) = a * (b * b') := by
            calc a * (b' * b) = a * b' * b := by rw [mul_assoc]
              _ = b' * a * b := by rw [hcomm a ha b' hb']
              _ = b' * (a * b) := by rw [mul_assoc]
              _ = a * b * b' := h1
              _ = a * (b * b') := by rw [mul_assoc]
          exact mul_left_cancel h3
        have haZ : a = 1 ∨ a = (c : G) := by
          have hcen : ∀ y : ↥A, y * ⟨a, ha⟩ = ⟨a, ha⟩ * y := fun y =>
            Subtype.ext (hac y y.2)
          rcases quaternion_central_eq (eA ⟨a, ha⟩) (central_transfer eA ⟨a, ha⟩ hcen) with h | h
          · left
            have : (⟨a, ha⟩ : ↥A) = 1 := eA.injective (by rw [h, map_one])
            exact congrArg Subtype.val this
          · right
            have : (⟨a, ha⟩ : ↥A) = cA := eA.injective (by rw [h, hcA2])
            exact congrArg Subtype.val this
        have hbZ : b = 1 ∨ b = (c : G) := by
          have hcen : ∀ y : ↥B, y * ⟨b, hb⟩ = ⟨b, hb⟩ * y := fun y =>
            Subtype.ext (hbc y y.2)
          rcases dihedral_central_eq (eB ⟨b, hb⟩) (central_transfer eB ⟨b, hb⟩ hcen) with h | h
          · left
            have : (⟨b, hb⟩ : ↥B) = 1 := eB.injective (by rw [h, map_one])
            exact congrArg Subtype.val this
          · right
            have : (⟨b, hb⟩ : ↥B) = cB := eB.injective (by rw [h, hcB2])
            exact congrArg Subtype.val this
        rcases haZ with h1 | h1 <;> rcases hbZ with h2 | h2 <;> simp [h1, h2, hzz]
      sq := by
        intro s hs
        obtain ⟨a, ha, b, hb, rfl⟩ := exists_mul_of_comm_sup hcomm (hsup ▸ hs)
        have hba : b * a = a * b := (hcomm a ha b hb).symm
        have h : a * b * (a * b) = (a * a) * (b * b) := by
          calc a * b * (a * b) = a * (b * a) * b := by simp only [mul_assoc]
            _ = a * (a * b) * b := by rw [hba]
            _ = a * a * (b * b) := by simp only [mul_assoc]
        rw [h]
        rcases hsqA a ha with h1 | h1 <;> rcases hsqB b hb with h2 | h2 <;>
          simp [h1, h2, hzz]
      comm := by
        intro s hs t ht
        obtain ⟨a, ha, b, hb, rfl⟩ := exists_mul_of_comm_sup hcomm (hsup ▸ hs)
        obtain ⟨a', ha', b', hb', rfl⟩ := exists_mul_of_comm_sup hcomm (hsup ▸ ht)
        have h : a * b * (a' * b') * (a * b)⁻¹ * (a' * b')⁻¹ =
            (a * a' * a⁻¹ * a'⁻¹) * (b * b' * b⁻¹ * b'⁻¹) := by
          have h1 := (prodHom hcomm).map_mul
          have key : ∀ p q : ↥A × ↥B, prodHom hcomm p * prodHom hcomm q *
              (prodHom hcomm p)⁻¹ * (prodHom hcomm q)⁻¹ =
              prodHom hcomm (p * q * p⁻¹ * q⁻¹) := by
            intro p q
            simp only [map_mul, map_inv]
          have := key (⟨a, ha⟩, ⟨b, hb⟩) (⟨a', ha'⟩, ⟨b', hb'⟩)
          simpa [prodHom_apply] using this
        rw [h]
        rcases hcommA a ha a' ha' with h1 | h1 <;> rcases hcommB b hb b' hb' with h2 | h2 <;>
          simp [h1, h2, hzz] }

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L630.I2026
