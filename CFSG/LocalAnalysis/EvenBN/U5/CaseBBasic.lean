module

public import CFSG.LocalAnalysis.EvenBN.U5.CaseBInputs
public import CFSG.LocalAnalysis.EvenBN.U5.CaseBGeneric

public noncomputable section

namespace CFSG.LocalAnalysis.EvenBN.U5

open Subgroup CFSG.Open CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
open CFSG.ABGLocalTools (IsSylowOf)
open CFSG.EvenSmallLie.UnitarySix.YamadaD (oTwo le_oTwo oTwo_le le_normalizer_oTwo isPGroup_oTwo)
open scoped MatrixGroups

section Generic

variable {G : Type*} [Group G] [Finite G]

theorem normalizer_le_normalizer_sup_closure (D N : Subgroup G) :
    normalizer (D : Set G) ≤ normalizer ((D ⊔
      closure {x | ∃ g ∈ normalizer (D : Set G), ∃ n ∈ N, x = g * n * g⁻¹} : Subgroup G) :
        Set G) := by
  intro y hy
  refine mem_normalizer_fintype fun x hx => ?_
  have hmap : (D ⊔ closure {x | ∃ g ∈ normalizer (D : Set G), ∃ n ∈ N, x = g * n * g⁻¹}).map
      (MulAut.conj y).toMonoidHom ≤
      D ⊔ closure {x | ∃ g ∈ normalizer (D : Set G), ∃ n ∈ N, x = g * n * g⁻¹} := by
    rw [Subgroup.map_sup, MonoidHom.map_closure]
    refine sup_le_sup (map_conj_eq_of_mem_normalizer hy).le (closure_mono ?_)
    rintro _ ⟨_, ⟨g, hg, n, hn, rfl⟩, rfl⟩
    refine ⟨y * g, mul_mem hy hg, n, hn, ?_⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    group
  exact hmap ⟨x, hx, rfl⟩

omit [Finite G] in
theorem le_sup_closure (D N : Subgroup G) :
    N ≤ D ⊔ closure {x | ∃ g ∈ normalizer (D : Set G), ∃ n ∈ N, x = g * n * g⁻¹} :=
  fun n hn => mem_sup_right (subset_closure ⟨1, one_mem _, n, hn, by group⟩)

omit [Finite G] in
theorem sup_closure_le_normalizer {D N : Subgroup G} (hN : N ≤ normalizer (D : Set G)) :
    D ⊔ closure {x | ∃ g ∈ normalizer (D : Set G), ∃ n ∈ N, x = g * n * g⁻¹} ≤
      normalizer (D : Set G) :=
  sup_le le_normalizer ((closure_le _).2 fun _ ⟨_, hg, _, hn, hx⟩ =>
    hx ▸ mul_mem (mul_mem hg (hN hn)) (inv_mem hg))

end Generic

namespace Data

variable {G : Type} [Group G] [Finite G] {f : ℕ} {K : Type} [Field K]
  {h : UnitaryFieldData 2 f K} {d : Data G h}

theorem B₆_eq_oTwo_caseB (d : Data G h) :
    d.B₆ = oTwo (normalizer ((d.F ⊔ d.B₃ : Subgroup G) : Set G)) :=
  Common.pCore_map_eq_oTwo _

theorem normalizer_le_normalizer_B₆ (d : Data G h) :
    normalizer ((d.F ⊔ d.B₃ : Subgroup G) : Set G) ≤ normalizer (d.B₆ : Set G) := by
  rw [B₆_eq_oTwo_caseB]
  exact le_normalizer_oTwo _

theorem isPGroup_B₆_caseB (d : Data G h) : IsPGroup 2 d.B₆ := by
  rw [B₆_eq_oTwo_caseB]
  exact isPGroup_oTwo _

theorem Hyp.F_sup_B₃_le_B₆ (hd : d.Hyp) : d.F ⊔ d.B₃ ≤ d.B₆ := by
  rw [B₆_eq_oTwo_caseB]
  refine le_oTwo le_normalizer (fun x hx => hx) ?_
  rw [← hd.B₅_eq_F_sup_B₃]
  exact d.isPGroup_B₅

omit [Finite G] in
theorem t_mem_normalizer_F_sup_B₃ (d : Data G h) :
    d.t ∈ normalizer ((d.F ⊔ d.B₃ : Subgroup G) : Set G) :=
  le_normalizer (mem_sup_right (mem_sup_left (mem_zpowers _)))

theorem mem_normalizer_zpowers_t {n : G} (hn : n ∈ centralizer ({d.t} : Set G)) :
    n ∈ normalizer ((zpowers d.t : Subgroup G) : Set G) := by
  have e : n * d.t * n⁻¹ = d.t := by
    rw [mem_centralizer_singleton_iff.1 hn, mul_inv_cancel_right]
  refine mem_normalizer_fintype fun x hx => ?_
  obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 hx
  rw [← conj_zpow, e]
  exact zpow_mem (mem_zpowers _) k

theorem Hyp.N₁_le_normalizer_B₃ (hd : d.Hyp) : d.N₁ ≤ normalizer (d.B₃ : Set G) := fun _ hn =>
  Common.mem_normalizer_sup (mem_normalizer_zpowers_t (hd.N₁_le hn).2) (d.N₁_le_normalizer_A₃ hn)

theorem mem_normalizer_of_mem_centralizer' {H : Subgroup G} {g : G}
    (hg : g ∈ centralizer (H : Set G)) : g ∈ normalizer (H : Set G) :=
  mem_normalizer_fintype fun x hx => by
    rw [← mem_centralizer_iff.1 hg x hx, mul_inv_cancel_right]
    exact hx

theorem t_mem_normalizer_B₆ (d : Data G h) : d.t ∈ normalizer (d.B₆ : Set G) :=
  d.normalizer_le_normalizer_B₆ d.t_mem_normalizer_F_sup_B₃

theorem mem_normalizer_D {g : G} (h₁ : g ∈ normalizer (d.B₆ : Set G))
    (h₂ : g ∈ normalizer (d.I₁ : Set G)) : g ∈ normalizer (d.D : Set G) := by
  refine mem_normalizer_fintype fun x hx => ?_
  have : g * x * g⁻¹ ∈ (⁅d.B₆, d.I₁⁆ : Subgroup G).map (MulAut.conj g).toMonoidHom := ⟨x, hx, rfl⟩
  rwa [map_commutator, map_conj_eq_of_mem_normalizer h₁, map_conj_eq_of_mem_normalizer h₂] at this

theorem Hyp.t_mem_normalizer_D (hd : d.Hyp) : d.t ∈ normalizer (d.D : Set G) :=
  mem_normalizer_D d.t_mem_normalizer_B₆
    (mem_normalizer_of_mem_centralizer' hd.t_mem_centralizer_I₁)

theorem Hyp.N₁_le_normalizer_F_sup_B₃ (hd : d.Hyp) :
    d.N₁ ≤ normalizer ((d.F ⊔ d.B₃ : Subgroup G) : Set G) := fun _ hn =>
  Common.mem_normalizer_sup (d.N₁_le_normalizer_F hn) (hd.N₁_le_normalizer_B₃ hn)

theorem Hyp.N₁_le_normalizer_D (hd : d.Hyp) : d.N₁ ≤ normalizer (d.D : Set G) := fun _ hn =>
  mem_normalizer_D (d.normalizer_le_normalizer_B₆ (hd.N₁_le_normalizer_F_sup_B₃ hn))
    (mem_normalizer_of_mem_centralizer' (d.N₁_le_centralizer_I₁ hn))

omit [Finite G] in
theorem D_le_L₁ (d : Data G h) : d.D ≤ d.L₁ := le_sup_left

omit [Finite G] in
theorem N₁_le_L₁ (d : Data G h) : d.N₁ ≤ d.L₁ := le_sup_closure _ _

theorem Hyp.L₁_le_normalizer_D (hd : d.Hyp) : d.L₁ ≤ normalizer (d.D : Set G) :=
  sup_closure_le_normalizer hd.N₁_le_normalizer_D

theorem normalizer_D_le_normalizer_L₁ (d : Data G h) :
    normalizer (d.D : Set G) ≤ normalizer (d.L₁ : Set G) :=
  normalizer_le_normalizer_sup_closure _ _

theorem Hyp.t_mem_normalizer_L₁ (hd : d.Hyp) : d.t ∈ normalizer (d.L₁ : Set G) :=
  d.normalizer_D_le_normalizer_L₁ hd.t_mem_normalizer_D

omit [Finite G] in
theorem E_le_L₂ (d : Data G h) : d.E ≤ d.L₂ := le_sup_left

omit [Finite G] in
theorem N₂_le_L₂ (d : Data G h) : d.N₂ ≤ d.L₂ := le_sup_closure _ _

theorem L₂_le_normalizer_E (d : Data G h) : d.L₂ ≤ normalizer (d.E : Set G) :=
  sup_closure_le_normalizer d.N₂_le_normalizer_E

theorem normalizer_E_le_normalizer_L₂ (d : Data G h) :
    normalizer (d.E : Set G) ≤ normalizer (d.L₂ : Set G) :=
  normalizer_le_normalizer_sup_closure _ _

theorem Hyp.t_mem_normalizer_E_caseB (hGMS : GMSK.GMSUnitarySharpKRankOneStatement)
    (hd : d.Hyp) :
    d.t ∈ normalizer (d.E : Set G) :=
  hd.normalizer_B₄_le_normalizer_E hGMS (le_normalizer hd.t_mem_B₄)

omit [Finite G] in
theorem Kc_eq_normalClosureIn (d : Data G h) (X : Subgroup G) :
    d.Kc X = normalClosureIn d.L₁ X := rfl

omit [Finite G] in
theorem N₁_le_M₁ (d : Data G h) : d.N₁ ≤ d.M₁ := le_normalClosureIn d.N₁_le_centralizer_I₁

omit [Finite G] in
theorem M₁_le_centralizer_I₁ (d : Data G h) : d.M₁ ≤ centralizer (d.I₁ : Set G) :=
  normalClosureIn_le_self _ _

theorem centralizer_I₁_le_normalizer_M₁ (d : Data G h) :
    centralizer (d.I₁ : Set G) ≤ normalizer (d.M₁ : Set G) :=
  le_normalizer_normalClosureIn _ _

theorem Hyp.t_mem_normalizer_M₁ (hd : d.Hyp) : d.t ∈ normalizer (d.M₁ : Set G) :=
  d.centralizer_I₁_le_normalizer_M₁ hd.t_mem_centralizer_I₁

omit [Finite G] in
theorem I₁_le_I (d : Data G h) : d.I₁ ≤ d.I := d.pull_mono (torusEq_le _)

omit [Finite G] in
theorem I₂_le_I (d : Data G h) : d.I₂ ≤ d.I := d.pull_mono (torusEq_le _)

omit [Finite G] in
theorem I_le_centralizer_I₁ (d : Data G h) : d.I ≤ centralizer (d.I₁ : Set G) := fun _ hi =>
  mem_centralizer_iff.2 fun _ hj => d.I_comm (d.I₁_le_I hj) hi

theorem I_le_normalizer_M₁ (d : Data G h) : d.I ≤ normalizer (d.M₁ : Set G) :=
  d.I_le_centralizer_I₁.trans d.centralizer_I₁_le_normalizer_M₁

theorem Hyp.P_le_L₂ (hGMS : GMSK.GMSUnitarySharpKRankOneStatement) (hd : d.Hyp) :
    d.P ≤ d.L₂ := by
  have h2 := (d.sec2_1_two hd.two_le).2.2.2.2.2.2.2.2.2.2.1.1
  rw [h2]
  refine sup_le ((hd.A₂_le_E hGMS).trans d.E_le_L₂) ?_
  have e : d.P ⊓ centralizer (d.I₂ : Set G) =
      d.pull (hypUnitriangular h 2 1 ⊓ centralizer (I₂sub h : Set (hypSU h 2 1))) :=
    (d.pull_U_inf_centralizer (torusEq_le _)).symm
  rw [e, U_inf_centralizer_I₂ hd.two_le]
  exact (d.pull_mono patSub_sI₂_le_N₂sub).trans d.N₂_le_L₂

structure CaseBHyp (d : Data G h) : Prop where
  hyp : d.Hyp
  gms : GMSK.GMSUnitarySharpKRankOneStatement
  sec3_8 : d.Sec3_8
  sec3_9_one : d.Sec3_9_one
  sec3_9_two : d.Sec3_9_two
  sec3_9_three : d.Sec3_9_three
  sec3_10_one : d.Sec3_10_one
  sec3_10_two : d.Sec3_10_two
  sec3_11 : d.Sec3_11
  sec3_12 : d.Sec3_12
  sec3_13_one : d.Sec3_13_one
  caseB : ¬ d.M₂Linear

structure CaseBData (d : Data G h) where
  S : Subgroup G
  S_syl : IsSylowOf 2 S d.L₂
  P_le_S : d.P ≤ S
  k : Type
  [instField : Field k]
  [instFintype : Fintype k]
  card_k : Fintype.card k = (2 ^ f) ^ 2
  ψ : d.M₁ ≃* SL(2, k) × SL(2, k)
  α : d.N₁ ≃* SL(2, k)
  diag : ∀ (a : d.N₁) (x : d.M₁), (x : G) = a → ψ x = (α a, α a)
  swap : ∀ (x y : d.M₁) (y₁ y₂ : SL(2, k)), (y : G) = d.t⁻¹ * x * d.t →
    ψ x = (y₁, y₂) → ψ y = (y₂, y₁)

attribute [instance] CaseBData.instField CaseBData.instFintype

theorem CaseBHyp.nonempty_caseBData (hB : d.CaseBHyp) : Nonempty d.CaseBData := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨k, _, _, hk, ψ, α, hdiag, hswap⟩ := hB.sec3_11
  have hPL := hB.hyp.P_le_L₂ hB.gms
  have hP2 : IsPGroup 2 (d.P.subgroupOf d.L₂) := d.isPGroup_P.comap_subtype
  obtain ⟨Q, hQ⟩ := hP2.exists_le_sylow
  refine ⟨⟨(Q : Subgroup d.L₂).map d.L₂.subtype, ⟨Q, rfl⟩, fun x hx => ⟨⟨x, hPL hx⟩, hQ hx, rfl⟩,
    k, hk, ψ, α, hdiag, hswap⟩⟩

theorem Hyp.t_inv' (hd : d.Hyp) : d.t⁻¹ = d.t := inv_eq_of_mul_eq_one_right hd.t_mul_t

omit [Finite G] in
theorem normalizer_le_normalizer_centerIn (D : Subgroup G) :
    normalizer (D : Set G) ≤ normalizer (CFSG.centerIn D : Set G) := fun _ hg =>
  Common.mem_normalizer_inf hg (normalizer_le_normalizer_centralizer D hg)

namespace CaseBHyp

variable (hB : d.CaseBHyp)
include hB

theorem L₁_eq : d.L₁ = d.D ⊔ d.M₁ := hB.sec3_9_three.1

theorem M₁_le_L₁ : d.M₁ ≤ d.L₁ := hB.L₁_eq ▸ le_sup_right

theorem centerIn_D : CFSG.centerIn d.D = d.F := by
  obtain ⟨c⟩ := hB.nonempty_caseBData
  exact (hB.sec3_9_two c.S c.S_syl c.P_le_S).2.2.2.1

theorem F_le_D : d.F ≤ d.D := by
  rw [← hB.centerIn_D]
  exact inf_le_left

theorem D_le_centralizer_F : d.D ≤ centralizer (d.F : Set G) := by
  rw [← hB.centerIn_D]
  intro x hx
  exact mem_centralizer_iff.2 fun z hz =>
    (mem_centralizer_iff.1 (Subgroup.mem_inf.1 hz).2 x hx).symm

theorem mul_self_mem_F : ∀ x ∈ d.D, x * x ∈ d.F := by
  obtain ⟨c⟩ := hB.nonempty_caseBData
  exact (hB.sec3_9_two c.S c.S_syl c.P_le_S).2.2.2.2

theorem L₁_le_normalizer_F : d.L₁ ≤ normalizer (d.F : Set G) := by
  rw [← hB.centerIn_D]
  exact hB.hyp.L₁_le_normalizer_D.trans (normalizer_le_normalizer_centerIn _)

theorem F_le_L₁ : d.F ≤ d.L₁ := hB.F_le_D.trans d.D_le_L₁

end CaseBHyp

namespace CaseBData

variable (c : d.CaseBData)

@[expose] def X : Subgroup G := Common.prodFactorOne c.ψ

@[expose] def Y : Subgroup G := Common.prodFactorTwo c.ψ

@[expose] def Kc : Subgroup G := d.Kc c.X

@[expose] def Qc : Subgroup G := c.S ⊓ c.Kc

@[expose] def W₂ : Subgroup G := d.E ⊓ c.Kc

@[expose] def φX : c.X ≃* SL(2, c.k) := Common.prodFactorOneEquiv c.ψ

@[expose] def φY : c.Y ≃* SL(2, c.k) := Common.prodFactorTwoEquiv c.ψ

omit [Finite G] in
theorem X_le_M₁ : c.X ≤ d.M₁ := Common.prodFactorOne_le c.ψ

omit [Finite G] in
theorem Y_le_M₁ : c.Y ≤ d.M₁ := Common.prodFactorTwo_le c.ψ

omit [Finite G] in
theorem X_sup_Y : c.X ⊔ c.Y = d.M₁ := Common.prodFactorOne_sup_prodFactorTwo c.ψ

omit [Finite G] in
theorem X_inf_Y : c.X ⊓ c.Y = ⊥ := Common.prodFactorOne_inf_prodFactorTwo c.ψ

omit [Finite G] in
theorem X_le_centralizer_Y : c.X ≤ centralizer (c.Y : Set G) :=
  Common.prodFactorOne_le_centralizer c.ψ

omit [Finite G] in
theorem Y_le_centralizer_X : c.Y ≤ centralizer (c.X : Set G) :=
  Common.prodFactorTwo_le_centralizer c.ψ

omit [Finite G] in
theorem M₁_le_normalizer_X : d.M₁ ≤ normalizer (c.X : Set G) :=
  Common.le_normalizer_prodFactorOne c.ψ

omit [Finite G] in
theorem M₁_le_normalizer_Y : d.M₁ ≤ normalizer (c.Y : Set G) :=
  Common.le_normalizer_prodFactorTwo c.ψ

omit [Finite G] in
theorem card_k_eq : Nat.card c.k = 2 ^ (2 * f) := by
  rw [Nat.card_eq_fintype_card, c.card_k, ← pow_mul, mul_comm]

theorem map_conj_t_X (hd : d.Hyp) : c.X.map (MulAut.conj d.t).toMonoidHom = c.Y := by
  have ht := hd.t_mem_normalizer_M₁
  apply le_antisymm
  · rintro _ ⟨x, hx, rfl⟩
    have := Common.conj_mem_prodFactorTwo_of_swap c.ψ ht c.swap hx
    change d.t * x * d.t⁻¹ ∈ Common.prodFactorTwo c.ψ
    rw [hd.t_inv'] at this ⊢
    exact this
  · intro y hy
    refine ⟨d.t⁻¹ * y * d.t, Common.conj_mem_prodFactorOne_of_swap c.ψ ht c.swap hy, ?_⟩
    change d.t * (d.t⁻¹ * y * d.t) * d.t⁻¹ = y
    group

theorem map_conj_t_Y (hd : d.Hyp) : c.Y.map (MulAut.conj d.t).toMonoidHom = c.X := by
  rw [← c.map_conj_t_X hd, Subgroup.map_map]
  conv_rhs => rw [← Subgroup.map_id c.X]
  congr 1
  ext x
  change d.t * (d.t * x * d.t⁻¹) * d.t⁻¹ = x
  rw [hd.t_inv']
  calc d.t * (d.t * x * d.t) * d.t = (d.t * d.t) * x * (d.t * d.t) := by group
    _ = x := by rw [hd.t_mul_t, one_mul, mul_one]

theorem commutator_X (hd : d.Hyp) : ⁅c.X, c.X⁆ = c.X := by
  have h4 : 4 ≤ Nat.card c.k := by
    rw [c.card_k_eq]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ (2 * f) := Nat.pow_le_pow_right (by norm_num) (by have := hd.two_le; omega)
  have := CFSG.ClassicalModels.specialLinear_isPerfect_two_of_four_le_card c.k h4
  exact Subgroup.isPerfect_iff.1 (Group.IsPerfect.ofSurjective (f := c.φX.symm.toMonoidHom)
    c.φX.symm.surjective)

variable {c} (hB : d.CaseBHyp)
include hB

theorem S_eq : c.S = d.E ⊔ d.D := (hB.sec3_9_one c.S c.S_syl c.P_le_S).1

theorem D_le_S : d.D ≤ c.S := (c.S_eq hB).symm ▸ le_sup_right

theorem E_le_S : d.E ≤ c.S := (c.S_eq hB).symm ▸ le_sup_left

theorem isSylowOf_S_L₁ : IsSylowOf 2 c.S d.L₁ :=
  (hB.sec3_10_two c.S c.S_syl c.P_le_S).2.2.2.2.2.2.1

theorem S_le_L₁ : c.S ≤ d.L₁ := (c.isSylowOf_S_L₁ hB).le

theorem isSylowOf_S_M₁ : IsSylowOf 2 (c.S ⊓ d.M₁) d.M₁ :=
  (hB.sec3_10_two c.S c.S_syl c.P_le_S).1.2

theorem t_mem_normalizer_S : d.t ∈ normalizer (c.S : Set G) := by
  rw [c.S_eq hB]
  exact Common.mem_normalizer_sup (hB.hyp.t_mem_normalizer_E_caseB hB.gms)
    hB.hyp.t_mem_normalizer_D

end CaseBData

end Data

end CFSG.LocalAnalysis.EvenBN.U5
