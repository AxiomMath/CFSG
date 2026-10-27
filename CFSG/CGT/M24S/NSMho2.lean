module

public import CFSG.CGT.M24S.NSMho
public import CFSG.CGT.M24S.NSTypeA

public section

namespace CFSG.CGT.M24S.NSB

open Matrix GL4 CFSG.CGT.M24S.NSSecond CFSG.CGT.Timmesfeld75

variable {G : Type} [Group G] {T H : Subgroup G} {t : G} {c : NatCoord T H t}

theorem card_row_zero : Fintype.card {u : Fin 3 → ZMod 2 // u 0 = 0} = 4 := by
  decide

theorem add_swap_of_eq {a b p q : Fin 3 → ZMod 2} (h : b + p = a + q) : a + p = b + q := by
  calc a + p = a + p + (b + b) := by rw [vec_add_self, add_zero]
    _ = (b + p) + (a + b) := by abel
    _ = (a + q) + (a + b) := by rw [h]
    _ = (a + a) + (b + q) := by abel
    _ = b + q := by rw [vec_add_self, zero_add]

theorem IsCaseB.top_apply_zero {x e : G} (hx : IsCaseB c x) (he : e ∈ c.E)
    (hex : e * x = x * e) : top (c.mat e) 0 = 0 := by
  have h1 := top_conj c hx.1 he
  rw [show x * e * x⁻¹ = e by rw [← hex, mul_inv_cancel_right], hx.inv_eq, hx.2.2.1] at h1
  exact (vecMul_ℓ₀_eq_iff _).1 h1.symm

theorem IsCaseB.card_centralizer_E {x : G} (hx : IsCaseB c x) :
    Nat.card (c.E ⊓ Subgroup.centralizer ({x} : Set G) : Subgroup G) = 16 := by
  let κb : ↥(c.E ⊓ Subgroup.centralizer ({x} : Set G)) →* Multiplicative (Fin 3 → ZMod 2) :=
    c.τ.comp (Subgroup.inclusion inf_le_left)
  have hκ : ∀ e, κb e = Multiplicative.ofAdd (top (c.mat e)) := fun e =>
    c.τ_apply (Subgroup.inclusion inf_le_left e)
  have hle : T ⊓ Subgroup.centralizer ({x} : Set G) ≤ c.E ⊓ Subgroup.centralizer ({x} : Set G) :=
    inf_le_inf_right _ c.T_le_E
  have hker : κb.ker = (T ⊓ Subgroup.centralizer ({x} : Set G)).subgroupOf
      (c.E ⊓ Subgroup.centralizer ({x} : Set G)) := by
    ext e
    rw [MonoidHom.mem_ker, hκ, ofAdd_eq_one, Subgroup.mem_subgroupOf, Subgroup.mem_inf]
    exact ⟨fun h => ⟨mem_T_of_top_eq_zero c e.2.1 h, e.2.2⟩,
      fun h => top_eq_zero_of_mem_T c h.1⟩
  let f : ↥κb.range → {u : Fin 3 → ZMod 2 // u 0 = 0} := fun m =>
    ⟨Multiplicative.toAdd m.1, by
      obtain ⟨e, he⟩ := m.2
      rw [← he, hκ, toAdd_ofAdd]
      exact hx.top_apply_zero e.2.1 (Subgroup.mem_centralizer_singleton_iff.1 e.2.2)⟩
  have hf : Function.Bijective f := by
    refine ⟨fun m m' h => Subtype.ext (Multiplicative.toAdd.injective
      (congrArg (fun z : {u : Fin 3 → ZMod 2 // u 0 = 0} => z.1) h)), fun u => ?_⟩
    have hcomm : mk4 u.1 1 * c.mat x = c.mat x * mk4 u.1 1 := by
      rw [hx.mat_eq, mk4_mul, mk4_mul, (vecMul_ℓ₀_eq_iff _).2 u.2, vecMul_one, one_mul,
        mul_one, add_comm]
    obtain ⟨g, hg, hgm⟩ := hx.exists_lift_of_commute (by rw [det_mk4, det_one])
      (mk4_mulVec_e0 _ _) hcomm
    have hgE : g ∈ c.E :=
      mem_E_of_blk_eq_one c ⟨hg.1.1, hg.2⟩ (by rw [hgm, blk_mk4])
    refine ⟨⟨κb ⟨g, hgE, hg.1.2⟩, ⟨_, rfl⟩⟩, Subtype.ext ?_⟩
    change Multiplicative.toAdd (κb ⟨g, hgE, hg.1.2⟩) = u.1
    rw [hκ, toAdd_ofAdd, hgm, top_mk4]
  have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup κb.ker
  rw [Nat.card_congr (QuotientGroup.quotientKerEquivRange κb).toEquiv,
    Nat.card_congr (Equiv.ofBijective f hf),
    Nat.card_eq_fintype_card (α := {u : Fin 3 → ZMod 2 // u 0 = 0}), card_row_zero, hker,
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv, hx.card_centralizer_T] at h1
  rw [h1]

theorem IsCaseB.blk_commute {x g : G} (hx : IsCaseB c x)
    (hg : g ∈ H ⊓ Subgroup.centralizer ({x} : Set G) ⊓ Subgroup.centralizer ({t} : Set G)) :
    blk (c.mat g) * ℓ₀ = ℓ₀ * blk (c.mat g) := by
  have hgK : g ∈ H ⊓ Subgroup.centralizer ({t} : Set G) := ⟨hg.1.1, hg.2⟩
  have hgx : g * x = x * g := Subgroup.mem_centralizer_singleton_iff.1 hg.1.2
  rw [← hx.2.2.1, ← blk_mul_of_mem c hgK hx.1.1, ← blk_mul_of_mem c hx.1 hg.1.1, hgx]

theorem IsCaseB.card_P {x : G} (hx : IsCaseB c x) :
    Nat.card (H ⊓ Subgroup.centralizer ({x} : Set G) ⊓ Subgroup.centralizer ({t} : Set G) :
      Subgroup G) = 2 ^ 7 := by
  set P := H ⊓ Subgroup.centralizer ({x} : Set G) ⊓ Subgroup.centralizer ({t} : Set G) with hP
  have hPK : P ≤ H ⊓ Subgroup.centralizer ({t} : Set G) := fun g hg => ⟨hg.1.1, hg.2⟩
  let σP : ↥P →* GL (Fin 3) (ZMod 2) := c.σ.comp (Subgroup.inclusion hPK)
  have hσ : ∀ g : ↥P, ((σP g : GL (Fin 3) (ZMod 2)) : Matrix (Fin 3) (Fin 3) (ZMod 2)) =
      blk (c.mat g) := fun g => c.coe_σ (Subgroup.inclusion hPK g)
  have hle : c.E ⊓ Subgroup.centralizer ({x} : Set G) ≤ P := fun e he =>
    ⟨⟨c.mem_H_of_mem_E he.1, he.2⟩, (c.E_le he.1).2⟩
  have hker : σP.ker = (c.E ⊓ Subgroup.centralizer ({x} : Set G)).subgroupOf P := by
    ext g
    rw [MonoidHom.mem_ker, ← Units.val_eq_one, hσ, Subgroup.mem_subgroupOf, Subgroup.mem_inf]
    exact ⟨fun h => ⟨mem_E_of_blk_eq_one c (hPK g.2) h, g.2.1.2⟩,
      fun h => c.blk_of_mem_E h.1⟩
  let f : ↥σP.range → {B : Matrix (Fin 3) (Fin 3) (ZMod 2) // InU3 B} := fun m =>
    ⟨(m.1 : Matrix (Fin 3) (Fin 3) (ZMod 2)), by
      obtain ⟨g, hg⟩ := m.2
      rw [← hg, hσ]
      exact inU3_of_commute _ (hx.blk_commute g.2) (det_blk_ne_zero c (hPK g.2))⟩
  have hf : Function.Bijective f := by
    refine ⟨fun m m' h => Subtype.ext (Units.ext
      (congrArg (fun z : {B : Matrix (Fin 3) (Fin 3) (ZMod 2) // InU3 B} => z.1) h)),
      fun B => ?_⟩
    obtain ⟨hBℓ, hB1⟩ := commute_of_inU3 _ B.2
    obtain ⟨b, hb⟩ := exists_top_of_inU3 _ hx.2.2.2 _ B.2
    have hcomm : mk4 b B.1 * c.mat x = c.mat x * mk4 b B.1 := by
      rw [hx.mat_eq, mk4_mul, mk4_mul, hBℓ, add_swap_of_eq hb]
    obtain ⟨g, hg, hgm⟩ := hx.exists_lift_of_commute (by rw [det_mk4, hB1])
      (mk4_mulVec_e0 _ _) hcomm
    refine ⟨⟨σP ⟨g, hg⟩, ⟨_, rfl⟩⟩, Subtype.ext ?_⟩
    change ((σP ⟨g, hg⟩ : GL (Fin 3) (ZMod 2)) : Matrix (Fin 3) (Fin 3) (ZMod 2)) = B.1
    rw [hσ, hgm, blk_mk4]
  have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup σP.ker
  rw [Nat.card_congr (QuotientGroup.quotientKerEquivRange σP).toEquiv,
    Nat.card_congr (Equiv.ofBijective f hf),
    Nat.card_eq_fintype_card (α := {B : Matrix (Fin 3) (Fin 3) (ZMod 2) // InU3 B}), card_inU3,
    hker, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv,
    hx.card_centralizer_E] at h1
  rw [h1]
  norm_num

end CFSG.CGT.M24S.NSB
