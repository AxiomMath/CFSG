module

public import CFSG.CGT.M24S.ExtraspecialCoord

public section

namespace CFSG.CGT.M24S

open Matrix GL4

variable {G : Type} [Group G] {T H : Subgroup G} {z : G}

namespace NatCoord

variable (c : NatCoord T H z)

theorem mat_mulVec_e0 {x : G} (hx : x ∈ H ⊓ Subgroup.centralizer ({z} : Set G)) :
    c.mat x *ᵥ e0 = e0 :=
  (c.mem_centralizer_iff hx.1).1 hx.2

noncomputable def blkHom :
    ↥(H ⊓ Subgroup.centralizer ({z} : Set G)) →* Matrix (Fin 3) (Fin 3) (ZMod 2) where
  toFun x := blk (c.mat x)
  map_one' := by
    rw [OneMemClass.coe_one, c.mat_one, blk_one]
  map_mul' x y := by
    rw [Subgroup.coe_mul, c.mat_mul x.2.1 y.2.1, blk_mul _ _ (c.mat_mulVec_e0 x.2)]

noncomputable def σ : ↥(H ⊓ Subgroup.centralizer ({z} : Set G)) →* GL (Fin 3) (ZMod 2) :=
  c.blkHom.toHomUnits

theorem coe_σ (x : ↥(H ⊓ Subgroup.centralizer ({z} : Set G))) :
    ((c.σ x : GL (Fin 3) (ZMod 2)) : Matrix (Fin 3) (Fin 3) (ZMod 2)) = blk (c.mat x) := by
  unfold σ blkHom
  rfl

noncomputable def E : Subgroup G :=
  c.σ.ker.map (H ⊓ Subgroup.centralizer ({z} : Set G)).subtype

theorem mem_E_iff {x : G} : x ∈ c.E ↔ x ∈ H ∧ c.mat x *ᵥ e0 = e0 ∧ blk (c.mat x) = 1 := by
  constructor
  · intro hx
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.1 hx
    refine ⟨y.2.1, c.mat_mulVec_e0 y.2, ?_⟩
    show blk (c.mat (y : G)) = 1
    rw [← c.coe_σ, MonoidHom.mem_ker.1 hy, Units.val_one]
  · rintro ⟨hx, h1, h2⟩
    refine Subgroup.mem_map.2 ⟨⟨x, hx, (c.mem_centralizer_iff hx).2 h1⟩, ?_, rfl⟩
    exact MonoidHom.mem_ker.2 (Units.ext h2)

theorem E_le : c.E ≤ H ⊓ Subgroup.centralizer ({z} : Set G) :=
  Subgroup.map_subtype_le _

theorem T_le_E : T ≤ c.E := fun t ht => by
  have h1 : c.mat t = 1 := (c.mat_eq_one_iff (c.le ht)).2 ht
  exact (c.mem_E_iff).2 ⟨c.le ht, by rw [h1, one_mulVec], by rw [h1, blk_one]⟩

theorem mem_H_of_mem_E {x : G} (hx : x ∈ c.E) : x ∈ H :=
  ((c.mem_E_iff).1 hx).1

theorem mulVec_e0_of_mem_E {x : G} (hx : x ∈ c.E) : c.mat x *ᵥ e0 = e0 :=
  ((c.mem_E_iff).1 hx).2.1

theorem blk_of_mem_E {x : G} (hx : x ∈ c.E) : blk (c.mat x) = 1 :=
  ((c.mem_E_iff).1 hx).2.2

theorem mat_eq_mk4_of_mem_E {x : G} (hx : x ∈ c.E) : c.mat x = mk4 (top (c.mat x)) 1 := by
  conv_lhs => rw [eq_mk4 _ (c.mulVec_e0_of_mem_E hx), c.blk_of_mem_E hx]

theorem exists_mem_E (a : Fin 3 → ZMod 2) : ∃ x ∈ c.E, c.mat x = mk4 a 1 := by
  obtain ⟨x, hx, hxa⟩ := c.exists_mat_eq (mk4 a 1) (by rw [det_mk4, det_one])
  refine ⟨x, (c.mem_E_iff).2 ⟨hx, ?_, ?_⟩, hxa⟩
  · rw [hxa, mk4_mulVec_e0]
  · rw [hxa, blk_mk4]

theorem exists_mem_cent (B : Matrix (Fin 3) (Fin 3) (ZMod 2)) (hB : B.det = 1) :
    ∃ x ∈ H ⊓ Subgroup.centralizer ({z} : Set G), blk (c.mat x) = B := by
  obtain ⟨x, hx, hxB⟩ := c.exists_mat_eq (mk4 0 B) (by rw [det_mk4, hB])
  refine ⟨x, ⟨hx, (c.mem_centralizer_iff hx).2 ?_⟩, ?_⟩
  · rw [hxB, mk4_mulVec_e0]
  · rw [hxB, blk_mk4]

theorem subgroupOf_E :
    c.E.subgroupOf (H ⊓ Subgroup.centralizer ({z} : Set G)) = c.σ.ker :=
  Subgroup.comap_map_eq_self_of_injective (Subgroup.subtype_injective _) _

theorem normal_E : (c.E.subgroupOf (H ⊓ Subgroup.centralizer ({z} : Set G))).Normal :=
  c.subgroupOf_E ▸ c.σ.normal_ker

theorem card_vec (n : ℕ) : Nat.card (Multiplicative (Fin n → ZMod 2)) = 2 ^ n := by
  rw [Nat.card_congr Multiplicative.toAdd, Nat.card_fun, Nat.card_zmod, Nat.card_eq_fintype_card,
    Fintype.card_fin]

include c in
theorem card_T : Nat.card T = 16 := by
  rw [Nat.card_congr c.ψ.toEquiv, card_vec]
  norm_num

noncomputable def τ : c.E →* Multiplicative (Fin 3 → ZMod 2) where
  toFun x := Multiplicative.ofAdd (top (c.mat x))
  map_one' := by
    rw [OneMemClass.coe_one, c.mat_one, top_one, ofAdd_zero]
  map_mul' x y := by
    rw [Subgroup.coe_mul, c.mat_mul (c.mem_H_of_mem_E x.2) (c.mem_H_of_mem_E y.2),
      top_mul _ _ (c.mulVec_e0_of_mem_E x.2), c.blk_of_mem_E y.2, vecMul_one, add_comm,
      ofAdd_add]

theorem τ_apply (x : c.E) : c.τ x = Multiplicative.ofAdd (top (c.mat x)) := by
  unfold τ
  rfl

theorem τ_surjective : Function.Surjective c.τ := by
  intro a
  obtain ⟨x, hx, hxa⟩ := c.exists_mem_E (Multiplicative.toAdd a)
  refine ⟨⟨x, hx⟩, ?_⟩
  rw [τ_apply, hxa, top_mk4, ofAdd_toAdd]

theorem ker_τ : c.τ.ker = T.subgroupOf c.E := by
  ext x
  rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, τ_apply]
  have hx := x.2
  constructor
  · intro h
    have h1 : top (c.mat x) = 0 := ofAdd_eq_one.1 h
    rw [← c.mat_eq_one_iff (c.mem_H_of_mem_E hx), c.mat_eq_mk4_of_mem_E hx, h1, mk4_zero_one]
  · intro h
    rw [(c.mat_eq_one_iff (c.mem_H_of_mem_E hx)).2 h, top_one, ofAdd_zero]

theorem card_E : Nat.card c.E = 2 ^ 7 := by
  rw [Subgroup.card_eq_card_quotient_mul_card_subgroup c.τ.ker,
    Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective c.τ c.τ_surjective).toEquiv,
    c.ker_τ, Nat.card_congr (Subgroup.subgroupOfEquivOfLe c.T_le_E).toEquiv, c.card_T, card_vec]
  norm_num

end NatCoord

end CFSG.CGT.M24S
