module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.G2Three.FrameDefs
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44EndSymp

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open Subgroup CFSG.OddStandard.HigherRank.G2Three.Sec1
open scoped commutatorElement IsMulCommutative

private lemma commutator_mul_of_mem_ker_left {G J : Type*} [Group G] [Group J] {π : G →* J}
    (hker : ∀ u ∈ π.ker, ∀ x : G, u * x = x * u) {u : G} (hu : u ∈ π.ker) (x y : G) :
    ⁅u * x, y⁆ = ⁅x, y⁆ := by
  rw [commutatorElement_mul_left_eq_conj_mul]
  have h1 : ⁅u, y⁆ = 1 := commutatorElement_eq_one_iff_mul_comm.mpr (hker u hu y)
  have h2 : u * ⁅x, y⁆ * u⁻¹ = ⁅x, y⁆ := by
    rw [hker u hu ⁅x, y⁆]
    group
  rw [h2, h1, mul_one]

private lemma commutator_mul_of_mem_ker_right {G J : Type*} [Group G] [Group J] {π : G →* J}
    (hker : ∀ u ∈ π.ker, ∀ x : G, u * x = x * u) {u : G} (hu : u ∈ π.ker) (x y : G) :
    ⁅x, u * y⁆ = ⁅x, y⁆ := by
  rw [commutatorElement_mul_right_eq_mul_conj]
  have h1 : ⁅x, u⁆ = 1 := commutatorElement_eq_one_iff_mul_comm.mpr (hker u hu x).symm
  have h2 : u * ⁅x, y⁆ * u⁻¹ = ⁅x, y⁆ := by
    rw [hker u hu ⁅x, y⁆]
    group
  rw [h1, one_mul, h2]

private lemma commutator_eq_of_eq_map {G J : Type*} [Group G] [Group J] {π : G →* J}
    (hker : ∀ u ∈ π.ker, ∀ x : G, u * x = x * u) {x x' y y' : G}
    (hx : π x = π x') (hy : π y = π y') : ⁅x, y⁆ = ⁅x', y'⁆ := by
  obtain ⟨u, hu, hux⟩ : ∃ u ∈ π.ker, x' = u * x := by
    refine ⟨x' * x⁻¹, ?_, by group⟩
    rw [MonoidHom.mem_ker, map_mul, map_inv, hx]
    group
  obtain ⟨v, hv, hvy⟩ : ∃ v ∈ π.ker, y' = v * y := by
    refine ⟨y' * y⁻¹, ?_, by group⟩
    rw [MonoidHom.mem_ker, map_mul, map_inv, hy]
    group
  rw [hux, hvy]
  exact ((commutator_mul_of_mem_ker_left hker hu x (v * y)).trans
    (commutator_mul_of_mem_ker_right hker hv x y)).symm

private lemma central_conj_eq {G : Type*} [Group G] {m : G} (hmc : ∀ x : G, m * x = x * m)
    {a : G} (ha : a = 1 ∨ a = m) (g : G) : g * a * g⁻¹ = a := by
  rcases ha with rfl | rfl
  · simp
  · rw [← hmc g]
    group

private lemma ite_mul_eq_add {G : Type*} [Group G] [DecidableEq G] {m : G}
    (hm1 : m ≠ 1) (hm2 : m * m = 1)
    (a b : G) (ha : a = 1 ∨ a = m) (hb : b = 1 ∨ b = m) :
    (if a * b = 1 then (0 : ZMod 2) else 1) =
      (if a = 1 then 0 else 1) + (if b = 1 then 0 else 1) := by
  rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
  · simp
  · simp [hm1]
  · simp [hm1]
  · rw [hm2]
    simp [hm1, show (1 : ZMod 2) + 1 = 0 by decide]

theorem l2_symp_basis {G J : Type} [Group G] [Group J] (π : G →* J)
    (hπ : Function.Surjective π) {A : Subgroup J} (hE : IsE 4 ↥A) {m : G}
    (hmc : ∀ x : G, m * x = x * m) (hm1 : m ≠ 1) (hm2 : m * m = 1)
    (hker : ∀ u ∈ π.ker, ∀ x : G, u * x = x * u)
    (hcomm : ∀ x y : G, π x ∈ A → π y ∈ A → ⁅x, y⁆ = 1 ∨ ⁅x, y⁆ = m)
    (hnd : ∀ x : G, π x ∈ A → π x ≠ 1 → ∃ y : G, π y ∈ A ∧ ⁅x, y⁆ = m) :
    ∃ a₁ b₁ a₂ b₂ : G, π a₁ ∈ A ∧ π b₁ ∈ A ∧ π a₂ ∈ A ∧ π b₂ ∈ A ∧
      ⁅a₁, b₁⁆ = m ∧ ⁅a₂, b₂⁆ = m ∧ ⁅a₁, a₂⁆ = 1 ∧ ⁅a₁, b₂⁆ = 1 ∧ ⁅b₁, a₂⁆ = 1 ∧
      ⁅b₁, b₂⁆ = 1 ∧
      ∀ y : G, π y ∈ A → y ∈ Subgroup.closure ({a₁, b₁, a₂, b₂} ∪ (π.ker : Set G)) := by
  classical
  have hAB := hE.1
  have hpowA : ∀ x : ↥A, x ^ 2 = 1 := fun x => hAB.2 x (Subgroup.mem_top x)
  haveI : IsMulCommutative ↥A := by
    rw [isMulCommutative_iff]
    intro a b
    haveI : IsMulCommutative ↥(⊤ : Subgroup ↥A) := hAB.1
    have h := mul_comm' (⟨a, Subgroup.mem_top a⟩ : ↥(⊤ : Subgroup ↥A))
      (⟨b, Subgroup.mem_top b⟩ : ↥(⊤ : Subgroup ↥A))
    simpa using congrArg Subtype.val h
  haveI : IsElementaryAbelian 2 ↥A :=
    { toIsMulCommutative := inferInstance
      exponent_dvd_p := Monoid.exponent_dvd_of_forall_pow_eq_one hpowA }
  haveI : Finite ↥A := Nat.finite_of_card_ne_zero (by rw [hE.2]; decide)
  let lift : ↥A → G := fun u => Classical.choose (hπ u)
  have hlift : ∀ u : ↥A, π (lift u) = (u : J) := fun u => Classical.choose_spec (hπ u)
  have hmem : ∀ u : ↥A, π (lift u) ∈ A := fun u => by
    rw [hlift u]
    exact u.2
  let b : ↥A → ↥A → ZMod 2 := fun u v => if ⁅lift u, lift v⁆ = 1 then 0 else 1
  have hbdef : ∀ u v : ↥A, b u v = (if ⁅lift u, lift v⁆ = 1 then (0 : ZMod 2) else 1) :=
    fun u v => rfl
  have hmul : ∀ u v : ↥A, π (lift u * lift v) = ((u * v : ↥A) : J) := by
    intro u v
    rw [map_mul, hlift u, hlift v]
    rfl
  have hb_comm : ∀ u v : ↥A, b u v = 1 ↔ ⁅lift u, lift v⁆ = m := by
    intro u v
    constructor
    · intro h
      rcases hcomm (lift u) (lift v) (hmem u) (hmem v) with h1 | hm
      · rw [hbdef u v, if_pos h1] at h
        exact absurd h (zero_ne_one : (0 : ZMod 2) ≠ 1)
      · exact hm
    · intro hm
      rw [hbdef u v]
      exact if_neg (by rw [hm]; exact hm1)
  have hb_zero : ∀ u v : ↥A, b u v = 0 ↔ ⁅lift u, lift v⁆ = 1 := by
    intro u v
    constructor
    · intro h
      by_contra hne
      have h1 : b u v = 1 := by
        rw [hbdef u v]
        exact if_neg hne
      rw [h1] at h
      exact one_ne_zero h
    · intro h1
      rw [hbdef u v]
      exact if_pos h1
  have hb1 : ∀ u v t : ↥A, b (u * v) t = b u t + b v t := by
    intro u v t
    have hwell : ⁅lift (u * v), lift t⁆ = ⁅lift u * lift v, lift t⁆ :=
      commutator_eq_of_eq_map hker ((hlift (u * v)).trans (hmul u v).symm) rfl
    have hexp : ⁅lift u * lift v, lift t⁆ = ⁅lift v, lift t⁆ * ⁅lift u, lift t⁆ := by
      rw [commutatorElement_mul_left_eq_conj_mul]
      rw [central_conj_eq hmc (hcomm _ _ (hmem v) (hmem t)) (lift u)]
    have hchi := ite_mul_eq_add hm1 hm2 ⁅lift v, lift t⁆ ⁅lift u, lift t⁆
      (hcomm _ _ (hmem v) (hmem t)) (hcomm _ _ (hmem u) (hmem t))
    have hmain : b (u * v) t =
        (if ⁅lift v, lift t⁆ = 1 then (0 : ZMod 2) else 1) +
        (if ⁅lift u, lift t⁆ = 1 then (0 : ZMod 2) else 1) := by
      rw [hbdef (u * v) t, hwell, hexp]
      exact hchi
    rw [hmain]
    simp only [hbdef]
    exact add_comm _ _
  have hb2 : ∀ u v t : ↥A, b u (v * t) = b u v + b u t := by
    intro u v t
    have hwell : ⁅lift u, lift (v * t)⁆ = ⁅lift u, lift v * lift t⁆ :=
      commutator_eq_of_eq_map hker rfl ((hlift (v * t)).trans (hmul v t).symm)
    have hexp : ⁅lift u, lift v * lift t⁆ = ⁅lift u, lift v⁆ * ⁅lift u, lift t⁆ := by
      rw [commutatorElement_mul_right_eq_mul_conj]
      rw [show ⁅lift u, lift v⁆ * lift v * ⁅lift u, lift t⁆ * (lift v)⁻¹
          = ⁅lift u, lift v⁆ * (lift v * ⁅lift u, lift t⁆ * (lift v)⁻¹) by group]
      rw [central_conj_eq hmc (hcomm _ _ (hmem u) (hmem t)) (lift v)]
    have hchi := ite_mul_eq_add hm1 hm2 ⁅lift u, lift v⁆ ⁅lift u, lift t⁆
      (hcomm _ _ (hmem u) (hmem v)) (hcomm _ _ (hmem u) (hmem t))
    have hmain : b u (v * t) =
        (if ⁅lift u, lift v⁆ = 1 then (0 : ZMod 2) else 1) +
        (if ⁅lift u, lift t⁆ = 1 then (0 : ZMod 2) else 1) := by
      rw [hbdef u (v * t), hwell, hexp]
      exact hchi
    calc b u (v * t)
        = (if ⁅lift u, lift v⁆ = 1 then (0 : ZMod 2) else 1) +
          (if ⁅lift u, lift t⁆ = 1 then (0 : ZMod 2) else 1) := hmain
      _ = b u v + b u t := by simp only [hbdef]
  have hb3 : ∀ u : ↥A, b u u = 0 := by
    intro u
    rw [hbdef u u]
    simp
  have hb4 : ∀ u : ↥A, (∀ v : ↥A, b u v = 0) → u = 1 := by
    intro u hu
    by_contra hne
    have hne' : (u : J) ≠ 1 := fun h => hne (Subtype.ext h)
    have hpi : π (lift u) ≠ 1 := by rwa [hlift u]
    obtain ⟨y, hyA, hy⟩ := hnd (lift u) (hmem u) hpi
    let v : ↥A := ⟨π y, hyA⟩
    have hv : ⁅lift u, lift v⁆ = m := by
      have h1 : ⁅lift u, lift v⁆ = ⁅lift u, y⁆ :=
        commutator_eq_of_eq_map hker rfl (show π (lift v) = π y from hlift v)
      rw [h1, hy]
    have hv1 : b u v = 1 := by
      rw [hbdef u v]
      exact if_neg (by rw [hv]; exact hm1)
    have h0 := hu v
    rw [hv1] at h0
    exact one_ne_zero h0
  have hcard16 : Nat.card ↥A = 16 := by rw [hE.2]; decide
  obtain ⟨bs, hbs⟩ :=
    CFSG.RankThree.PartTwo.Sec4.Census.exists_basis_antidiag hcard16 b hb1 hb2 hb3 hb4
  let a₁ : G := lift (Additive.toMul (bs 0))
  let b₁ : G := lift (Additive.toMul (bs 3))
  let a₂ : G := lift (Additive.toMul (bs 1))
  let b₂ : G := lift (Additive.toMul (bs 2))
  have hb03 : b (Additive.toMul (bs 0)) (Additive.toMul (bs 3)) = 1 := by rw [hbs 0 3]; decide
  have hb12 : b (Additive.toMul (bs 1)) (Additive.toMul (bs 2)) = 1 := by rw [hbs 1 2]; decide
  have hb01 : b (Additive.toMul (bs 0)) (Additive.toMul (bs 1)) = 0 := by rw [hbs 0 1]; decide
  have hb02 : b (Additive.toMul (bs 0)) (Additive.toMul (bs 2)) = 0 := by rw [hbs 0 2]; decide
  have hb31 : b (Additive.toMul (bs 3)) (Additive.toMul (bs 1)) = 0 := by rw [hbs 3 1]; decide
  have hb32 : b (Additive.toMul (bs 3)) (Additive.toMul (bs 2)) = 0 := by rw [hbs 3 2]; decide
  let S : Subgroup G := Subgroup.closure ({a₁, b₁, a₂, b₂} ∪ (π.ker : Set G))
  have hkerS : (π.ker : Set G) ⊆ S := by
    intro x hx
    show x ∈ Subgroup.closure ({a₁, b₁, a₂, b₂} ∪ (π.ker : Set G))
    exact Subgroup.subset_closure (Or.inr hx)
  have ha₁S : a₁ ∈ S := by
    show a₁ ∈ Subgroup.closure ({a₁, b₁, a₂, b₂} ∪ (π.ker : Set G))
    exact Subgroup.subset_closure (Or.inl (by simp))
  have hb₁S : b₁ ∈ S := by
    show b₁ ∈ Subgroup.closure ({a₁, b₁, a₂, b₂} ∪ (π.ker : Set G))
    exact Subgroup.subset_closure (Or.inl (by simp))
  have ha₂S : a₂ ∈ S := by
    show a₂ ∈ Subgroup.closure ({a₁, b₁, a₂, b₂} ∪ (π.ker : Set G))
    exact Subgroup.subset_closure (Or.inl (by simp))
  have hb₂S : b₂ ∈ S := by
    show b₂ ∈ Subgroup.closure ({a₁, b₁, a₂, b₂} ∪ (π.ker : Set G))
    exact Subgroup.subset_closure (Or.inl (by simp))
  let T' : Subgroup ↥A :=
    { carrier := {u | lift u ∈ S}
      one_mem' := by
        show lift 1 ∈ S
        exact hkerS (MonoidHom.mem_ker.mpr (hlift 1))
      mul_mem' := by
        intro u v hu hv
        show lift (u * v) ∈ S
        have hmem_ker : lift (u * v) * (lift u * lift v)⁻¹ ∈ π.ker := by
          rw [MonoidHom.mem_ker, map_mul, map_inv, map_mul, hlift (u * v), hlift u, hlift v]
          simp
        have heq : lift (u * v) =
            (lift (u * v) * (lift u * lift v)⁻¹) * (lift u * lift v) := by group
        rw [heq]
        exact mul_mem (hkerS hmem_ker) (mul_mem hu hv)
      inv_mem' := by
        intro u hu
        show lift u⁻¹ ∈ S
        have hmem_ker : lift u⁻¹ * lift u ∈ π.ker := by
          rw [MonoidHom.mem_ker, map_mul, hlift u⁻¹, hlift u]
          simp
        have heq : lift u⁻¹ = (lift u⁻¹ * lift u) * (lift u)⁻¹ := by group
        rw [heq]
        exact mul_mem (hkerS hmem_ker) (inv_mem hu) }
  have hspan : Submodule.span (ZMod 2) (Set.range bs) ≤
      AddSubgroup.toZModSubmodule (n := 2) (Subgroup.toAddSubgroup T') := by
    rw [Submodule.span_le]
    rintro x ⟨i, rfl⟩
    change bs i ∈ Subgroup.toAddSubgroup T'
    rw [Additive.mem_toAddSubgroup]
    show lift (Additive.toMul (bs i)) ∈ S
    fin_cases i
    · simpa [a₁] using ha₁S
    · simpa [a₂] using ha₂S
    · simpa [b₂] using hb₂S
    · simpa [b₁] using hb₁S
  rw [Module.Basis.span_eq] at hspan
  have hgen : ∀ u : ↥A, lift u ∈ S := by
    intro u
    have hmem1 : Additive.ofMul u ∈ Subgroup.toAddSubgroup T' :=
      hspan Submodule.mem_top
    have hmem2 : u ∈ T' := by
      simpa using (Additive.mem_toAddSubgroup T' (Additive.ofMul u)).mp hmem1
    show lift u ∈ S
    exact hmem2
  refine ⟨a₁, b₁, a₂, b₂, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa [a₁] using hmem (Additive.toMul (bs 0))
  · simpa [b₁] using hmem (Additive.toMul (bs 3))
  · simpa [a₂] using hmem (Additive.toMul (bs 1))
  · simpa [b₂] using hmem (Additive.toMul (bs 2))
  · simpa [a₁, b₁] using (hb_comm (Additive.toMul (bs 0)) (Additive.toMul (bs 3))).mp hb03
  · simpa [a₂, b₂] using (hb_comm (Additive.toMul (bs 1)) (Additive.toMul (bs 2))).mp hb12
  · simpa [a₁, a₂] using (hb_zero (Additive.toMul (bs 0)) (Additive.toMul (bs 1))).mp hb01
  · simpa [a₁, b₂] using (hb_zero (Additive.toMul (bs 0)) (Additive.toMul (bs 2))).mp hb02
  · simpa [b₁, a₂] using (hb_zero (Additive.toMul (bs 3)) (Additive.toMul (bs 1))).mp hb31
  · simpa [b₁, b₂] using (hb_zero (Additive.toMul (bs 3)) (Additive.toMul (bs 2))).mp hb32
  · intro y hy
    let u : ↥A := ⟨π y, hy⟩
    have hker_y : y * (lift u)⁻¹ ∈ π.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hlift u]
      simp [u]
    have heq : y = (y * (lift u)⁻¹) * lift u := by group
    rw [heq]
    show (y * (lift u)⁻¹) * lift u ∈ S
    exact mul_mem (hkerS hker_y) (hgen u)

end CFSG.OddStandard.HigherRank.YamadaG23
