module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.ExceptionalEightPlaneStructure

public section

namespace CFSG.ProperTwoGeneratedCore.ExceptionalEight

variable {Y : Type*} [Group Y]

@[expose] def planeD (B : Subgroup Y) (c₁ c₂ : Y) : Subgroup Y :=
  Subgroup.centralizer (B : Set Y) ⊓ Subgroup.centralizer ({c₁, c₂} : Set Y)

structure PlaneLifts (B : Subgroup Y) (b₁ b₂ u₀ c₁ c₂ : Y) : Prop where
  c₁_mem : c₁ ∈ Subgroup.centralizer (B : Set Y)
  c₂_mem : c₂ ∈ Subgroup.centralizer (B : Set Y)
  tau₁ : planeTau u₀ c₁ = b₁
  tau₂ : planeTau u₀ c₂ = b₂
  comm : c₁ * c₂ = c₂ * c₁

theorem mem_planeD_iff {B : Subgroup Y} {c₁ c₂ x : Y} :
    x ∈ planeD B c₁ c₂ ↔
      x ∈ Subgroup.centralizer (B : Set Y) ∧ c₁ * x = x * c₁ ∧ c₂ * x = x * c₂ := by
  rw [planeD, Subgroup.mem_inf, Subgroup.mem_centralizer_iff (s := ({c₁, c₂} : Set Y))]
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff, forall_eq_or_imp, forall_eq]

theorem planeD_le_centralizer (B : Subgroup Y) (c₁ c₂ : Y) :
    planeD B c₁ c₂ ≤ Subgroup.centralizer (B : Set Y) := inf_le_left

namespace PlaneHyp

variable {U B : Subgroup Y} {b₁ b₂ u₀ c₁ c₂ : Y} [U.Normal] [IsElementaryAbelian 2 U]
  (h : PlaneHyp U B b₁ b₂ u₀) (hl : PlaneLifts B b₁ b₂ u₀ c₁ c₂)
include h hl

omit [U.Normal] in
theorem B_le_planeD : B ≤ planeD B c₁ c₂ := by
  intro b hb
  rw [mem_planeD_iff]
  exact ⟨le_centralizer_of_le h.le hb, (Subgroup.mem_centralizer_iff.mp hl.c₁_mem b hb).symm,
    (Subgroup.mem_centralizer_iff.mp hl.c₂_mem b hb).symm⟩

omit [U.Normal] [IsElementaryAbelian 2 U] h in
theorem c₁_mem_planeD : c₁ ∈ planeD B c₁ c₂ :=
  mem_planeD_iff.mpr ⟨hl.c₁_mem, rfl, hl.comm.symm⟩

omit [U.Normal] [IsElementaryAbelian 2 U] h in
theorem c₂_mem_planeD : c₂ ∈ planeD B c₁ c₂ :=
  mem_planeD_iff.mpr ⟨hl.c₂_mem, hl.comm, rfl⟩

theorem planeD_inf_U : planeD B c₁ c₂ ⊓ U = B := by
  apply le_antisymm
  · rintro x ⟨hxD, hxU⟩
    by_contra hxB
    obtain ⟨-, hc₁x, -⟩ := mem_planeD_iff.mp hxD
    have hc := h.conj_of_not_mem hl.c₁_mem hxU hxB
    rw [hc₁x, mul_inv_cancel_right, hl.tau₁] at hc
    exact h.b₁_ne_one (left_eq_mul.mp hc)
  · exact le_inf (h.B_le_planeD hl) h.le

theorem mem_B_of_mem_planeD {x : Y} (hxD : x ∈ planeD B c₁ c₂) (hτ : planeTau u₀ x = 1) :
    x ∈ B := by
  rw [← h.planeD_inf_U hl]
  exact ⟨hxD, (h.planeTau_eq_one_iff (planeD_le_centralizer B c₁ c₂ hxD)).mp hτ⟩

theorem planeD_decomp {x : Y} (hx : x ∈ planeD B c₁ c₂) :
    ∃ b ∈ B, x = b ∨ x = c₁ * b ∨ x = c₂ * b ∨ x = c₁ * c₂ * b := by
  have hxC := planeD_le_centralizer B c₁ c₂ hx
  have hD₁ := c₁_mem_planeD hl
  have hD₂ := c₂_mem_planeD hl
  have hτ1 : planeTau u₀ (1 : Y) = 1 := h.planeTau_of_mem_U U.one_mem
  have key : ∀ d ∈ planeD B c₁ c₂, planeTau u₀ d = planeTau u₀ x →
      d⁻¹ * x ∈ B := by
    intro d hd hτ
    refine h.mem_B_of_mem_planeD hl (Subgroup.mul_mem _ (Subgroup.inv_mem _ hd) hx) ?_
    have hdC := planeD_le_centralizer B c₁ c₂ hd
    have h1 := h.planeTau_mul (Subgroup.inv_mem _ hdC) hdC
    rw [inv_mul_cancel, hτ1] at h1
    rw [h.planeTau_mul (Subgroup.inv_mem _ hdC) hxC, ← hτ]
    exact h1.symm
  have hxd : ∀ d : Y, x = d * (d⁻¹ * x) := fun d => by group
  rcases h.mem_B_cases (h.planeTau_mem hxC) with hτ | hτ | hτ | hτ
  · exact ⟨_, key 1 (Subgroup.one_mem _) (hτ1.trans hτ.symm), Or.inl (by group)⟩
  · exact ⟨_, key c₁ hD₁ (hl.tau₁.trans hτ.symm), Or.inr (Or.inl (hxd c₁))⟩
  · exact ⟨_, key c₂ hD₂ (hl.tau₂.trans hτ.symm), Or.inr (Or.inr (Or.inl (hxd c₂)))⟩
  · refine ⟨_, key (c₁ * c₂) (Subgroup.mul_mem _ hD₁ hD₂) ?_, Or.inr (Or.inr (Or.inr
      (hxd (c₁ * c₂))))⟩
    rw [h.planeTau_mul hl.c₁_mem hl.c₂_mem, hl.tau₁, hl.tau₂, hτ]

theorem planeD_comm {x y : Y} (hx : x ∈ planeD B c₁ c₂) (hy : y ∈ planeD B c₁ c₂) :
    x * y = y * x := by
  obtain ⟨hxC, hx₁, hx₂⟩ := mem_planeD_iff.mp hx
  obtain ⟨b, hb, hyd⟩ := h.planeD_decomp hl hy
  have hxb : x * b = b * x := ((Subgroup.mem_centralizer_iff.mp hxC) b hb).symm
  rcases hyd with hyd | hyd | hyd | hyd <;> rw [hyd]
  · exact hxb
  · rw [← mul_assoc, ← hx₁, mul_assoc, hxb, ← mul_assoc]
  · rw [← mul_assoc, ← hx₂, mul_assoc, hxb, ← mul_assoc]
  · rw [← mul_assoc, ← mul_assoc, ← hx₁, mul_assoc c₁, ← hx₂, mul_assoc, mul_assoc, hxb]
    group

theorem isMulCommutative_planeD : IsMulCommutative (planeD B c₁ c₂) :=
  ⟨⟨fun a b => Subtype.ext (h.planeD_comm hl a.2 b.2)⟩⟩

theorem exists_planeD_of_tau {b : Y} (hb : b ∈ B) :
    ∃ d ∈ planeD B c₁ c₂, planeTau u₀ d = b := by
  rcases h.mem_B_cases hb with rfl | rfl | rfl | rfl
  · exact ⟨1, Subgroup.one_mem _, h.planeTau_of_mem_U U.one_mem⟩
  · exact ⟨c₁, c₁_mem_planeD hl, hl.tau₁⟩
  · exact ⟨c₂, c₂_mem_planeD hl, hl.tau₂⟩
  · refine ⟨c₁ * c₂, Subgroup.mul_mem _ (c₁_mem_planeD hl) (c₂_mem_planeD hl), ?_⟩
    rw [h.planeTau_mul hl.c₁_mem hl.c₂_mem, hl.tau₁, hl.tau₂]

theorem card_planeD : Nat.card (planeD B c₁ c₂) = 16 := by
  let f : planeD B c₁ c₂ →* B :=
    h.tauHom.comp (Subgroup.inclusion (planeD_le_centralizer B c₁ c₂))
  have hf : ∀ d : planeD B c₁ c₂, ((f d : B) : Y) = planeTau u₀ d := fun d => rfl
  have hsurj : Function.Surjective f := by
    intro b
    obtain ⟨d, hd, hτ⟩ := h.exists_planeD_of_tau hl b.2
    exact ⟨⟨d, hd⟩, Subtype.ext hτ⟩
  have hker : f.ker = B.subgroupOf (planeD B c₁ c₂) := by
    ext d
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    constructor
    · intro h1
      exact h.mem_B_of_mem_planeD hl d.2 (by rw [← hf]; exact congrArg Subtype.val h1)
    · intro h1
      apply Subtype.ext
      rw [hf]
      exact h.planeTau_of_mem_U (h.le h1)
  rw [Subgroup.card_eq_card_quotient_mul_card_subgroup f.ker,
    Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective f hsurj).toEquiv, h.card_B, hker,
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe (h.B_le_planeD hl)).toEquiv, h.card_B]

theorem planeD_sup_U : planeD B c₁ c₂ ⊔ U = Subgroup.centralizer (B : Set Y) := by
  apply le_antisymm
  · exact sup_le (planeD_le_centralizer B c₁ c₂) h.U_le_centralizer
  · intro y hy
    obtain ⟨d, hd, hτ⟩ := h.exists_planeD_of_tau hl (h.planeTau_mem hy)
    have hdC := planeD_le_centralizer B c₁ c₂ hd
    have hτ1 : planeTau u₀ (1 : Y) = 1 := h.planeTau_of_mem_U U.one_mem
    have hdy : d⁻¹ * y ∈ U := by
      refine (h.planeTau_eq_one_iff (Subgroup.mul_mem _ (Subgroup.inv_mem _ hdC) hy)).mp ?_
      have h1 := h.planeTau_mul (Subgroup.inv_mem _ hdC) hdC
      rw [inv_mul_cancel, hτ1] at h1
      rw [h.planeTau_mul (Subgroup.inv_mem _ hdC) hy, ← hτ]
      exact h1.symm
    rw [show y = d * (d⁻¹ * y) by group]
    exact Subgroup.mul_mem_sup hd hdy

theorem relIndex_planeD : (planeD B c₁ c₂).relIndex (Subgroup.centralizer (B : Set Y)) = 2 := by
  have hcard := ((planeD B c₁ c₂).subgroupOf (Subgroup.centralizer (B : Set Y))).index_mul_card
  rw [h.card_C, Nat.card_congr (Subgroup.subgroupOfEquivOfLe
    (planeD_le_centralizer B c₁ c₂)).toEquiv, h.card_planeD hl] at hcard
  rw [Subgroup.relIndex]
  omega

theorem comm_iff_of_not_mem_planeD {y d : Y} (hy : y ∈ Subgroup.centralizer (B : Set Y))
    (hyD : y ∉ planeD B c₁ c₂) (hd : d ∈ planeD B c₁ c₂) : y * d = d * y ↔ d ∈ B := by
  have hyCU : y ∈ planeD B c₁ c₂ ⊔ U := by rw [h.planeD_sup_U hl]; exact hy
  obtain ⟨d₀, hd₀, x, hx, rfl⟩ := Subgroup.mem_sup_of_normal_right.mp hyCU
  have hxB : x ∉ B := by
    intro hxB
    exact hyD (Subgroup.mul_mem _ hd₀ (h.B_le_planeD hl hxB))
  have hdC := planeD_le_centralizer B c₁ c₂ hd
  have hdd₀ := h.planeD_comm hl hd₀ hd
  have hc := h.conj_of_not_mem hdC hx hxB
  constructor
  · intro hcomm
    have hxd : x * d = d * x := by
      have : d₀ * (x * d) = d₀ * (d * x) := by
        calc d₀ * (x * d) = d₀ * x * d := by group
          _ = d * (d₀ * x) := hcomm
          _ = d₀ * (d * x) := by rw [← mul_assoc, ← hdd₀, mul_assoc]
      exact mul_left_cancel this
    rw [← hxd, mul_inv_cancel_right] at hc
    exact h.mem_B_of_mem_planeD hl hd (left_eq_mul.mp hc)
  · intro hdB
    have hxd : x * d = d * x := mul_comm_of_mem hx (h.le hdB) |>.trans rfl
    calc d₀ * x * d = d₀ * (d * x) := by rw [mul_assoc, hxd]
      _ = d * (d₀ * x) := by rw [← mul_assoc, hdd₀, mul_assoc]

theorem eq_planeD_of_abelian [Finite Y] {A : Subgroup Y}
    (hAC : A ≤ Subgroup.centralizer (B : Set Y)) (hA : IsMulCommutative A)
    (hA16 : Nat.card A = 16) : A = planeD B c₁ c₂ := by
  suffices hle : A ≤ planeD B c₁ c₂ by
    exact Subgroup.eq_of_le_of_card_ge hle (by rw [hA16, h.card_planeD hl])
  intro y hyA
  by_contra hyD
  have hinf : planeD B c₁ c₂ ⊓ A ≤ B := by
    rintro d ⟨hdD, hdA⟩
    have hcomm : y * d = d * y :=
      congrArg Subtype.val ((hA.is_comm).comm (⟨y, hyA⟩ : A) ⟨d, hdA⟩)
    exact (h.comm_iff_of_not_mem_planeD hl (hAC hyA) hyD hdD).mp hcomm
  have hrel : (planeD B c₁ c₂).relIndex A ≤ 2 := by
    rw [← h.relIndex_planeD hl]
    exact Subgroup.relIndex_le_of_le_right hAC (by rw [h.relIndex_planeD hl]; omega)
  have hcard := ((planeD B c₁ c₂).subgroupOf A).index_mul_card
  rw [hA16, ← Subgroup.inf_subgroupOf_right,
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_right).toEquiv] at hcard
  have hle : Nat.card (planeD B c₁ c₂ ⊓ A : Subgroup Y) ≤ 4 := by
    have : Finite B := Nat.finite_of_card_ne_zero (by rw [h.card_B]; omega)
    rw [← h.card_B]
    exact Subgroup.card_le_of_le hinf
  have hidx : ((planeD B c₁ c₂ ⊓ A).subgroupOf A).index ≤ 2 := by
    rw [Subgroup.inf_subgroupOf_right]
    exact hrel
  nlinarith

omit [U.Normal] [IsElementaryAbelian 2 U] h hl in
theorem conj_mem_centralizer {n y : Y} (hn : n ∈ Subgroup.normalizer (B : Set Y))
    (hy : y ∈ Subgroup.centralizer (B : Set Y)) :
    n * y * n⁻¹ ∈ Subgroup.centralizer (B : Set Y) := by
  rw [Subgroup.mem_centralizer_iff]
  intro b hb
  have hb' : n⁻¹ * b * n ∈ B := by
    have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hn) b).mp hb
    rwa [inv_inv] at this
  have hc := (Subgroup.mem_centralizer_iff.mp hy) _ hb'
  calc b * (n * y * n⁻¹) = n * ((n⁻¹ * b * n) * y) * n⁻¹ := by group
    _ = n * (y * (n⁻¹ * b * n)) * n⁻¹ := by rw [hc]
    _ = n * y * n⁻¹ * b := by group

theorem conj_mem_planeD [Finite Y] {n d : Y} (hn : n ∈ Subgroup.normalizer (B : Set Y))
    (hd : d ∈ planeD B c₁ c₂) : n * d * n⁻¹ ∈ planeD B c₁ c₂ := by
  let A : Subgroup Y := (planeD B c₁ c₂).map (MulAut.conj n).toMonoidHom
  have hAC : A ≤ Subgroup.centralizer (B : Set Y) := by
    rintro _ ⟨x, hx, rfl⟩
    exact conj_mem_centralizer hn (planeD_le_centralizer B c₁ c₂ hx)
  have hAab : IsMulCommutative A := by
    refine ⟨⟨fun a b => Subtype.ext ?_⟩⟩
    obtain ⟨x, hx, hxa⟩ := a.2
    obtain ⟨y, hy, hyb⟩ := b.2
    simp only [Subgroup.coe_mul]
    rw [← hxa, ← hyb, ← map_mul, ← map_mul, h.planeD_comm hl hx hy]
  have hA16 : Nat.card A = 16 := by
    rw [Subgroup.card_map_of_injective (MulAut.conj n).injective, h.card_planeD hl]
  have hA := h.eq_planeD_of_abelian hl hAC hAab hA16
  rw [← hA]
  exact ⟨d, hd, rfl⟩

omit [U.Normal] [IsElementaryAbelian 2 U] h hl in
theorem planeD_le_normalizer : planeD B c₁ c₂ ≤ Subgroup.normalizer (B : Set Y) :=
  (planeD_le_centralizer B c₁ c₂).trans centralizer_le_normalizer

theorem normal_planeD_subgroupOf_normalizer [Finite Y] :
    ((planeD B c₁ c₂).subgroupOf (Subgroup.normalizer (B : Set Y))).Normal := by
  refine ⟨fun d hd n => ?_⟩
  rw [Subgroup.mem_subgroupOf] at hd ⊢
  exact h.conj_mem_planeD hl n.2 hd

theorem characteristic_planeD [Finite Y] :
    ((planeD B c₁ c₂).subgroupOf (Subgroup.centralizer (B : Set Y))).Characteristic := by
  set C := Subgroup.centralizer (B : Set Y) with hC
  set D' := (planeD B c₁ c₂).subgroupOf C with hD'
  rw [Subgroup.characteristic_iff_map_eq]
  intro φ
  let A : Subgroup Y := (D'.map φ.toMonoidHom).map C.subtype
  have hAC : A ≤ C := Subgroup.map_subtype_le _
  have hAab : IsMulCommutative A := by
    refine ⟨⟨fun a b => Subtype.ext ?_⟩⟩
    obtain ⟨x, ⟨x', hx', hxx⟩, hxa⟩ := a.2
    obtain ⟨y, ⟨y', hy', hyy⟩, hyb⟩ := b.2
    simp only [Subgroup.coe_mul]
    rw [← hxa, ← hyb, ← hxx, ← hyy, ← map_mul, ← map_mul, ← map_mul, ← map_mul]
    congr 2
    exact Subtype.ext (h.planeD_comm hl hx' hy')
  have hA16 : Nat.card A = 16 := by
    rw [Subgroup.card_map_of_injective C.subtype_injective,
      Subgroup.card_map_of_injective φ.injective,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe (planeD_le_centralizer B c₁ c₂)).toEquiv,
      h.card_planeD hl]
  have hA := h.eq_planeD_of_abelian hl hAC hAab hA16
  calc D'.map φ.toMonoidHom = ((D'.map φ.toMonoidHom).map C.subtype).comap C.subtype :=
        (Subgroup.comap_map_eq_self_of_injective C.subtype_injective _).symm
    _ = D' := by rw [show (D'.map φ.toMonoidHom).map C.subtype = planeD B c₁ c₂ from hA]; rfl

end PlaneHyp

end CFSG.ProperTwoGeneratedCore.ExceptionalEight
