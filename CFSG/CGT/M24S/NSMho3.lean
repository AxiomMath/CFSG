module

public import CFSG.CGT.M24S.NSMho2

public section

namespace CFSG.CGT.M24S.NSB

open Matrix GL4 CFSG.CGT.M24S.NSSecond CFSG.CGT.Timmesfeld75

variable {G : Type} [Group G] {T H : Subgroup G} {t : G} {c : NatCoord T H t}

theorem ℓ₀_mul_self : ℓ₀ * ℓ₀ = 1 := by decide

@[expose] def pEll (c : NatCoord T H t) (x : G) : Subgroup G where
  carrier := {g | g ∈ H ⊓ Subgroup.centralizer ({x} : Set G) ⊓
    Subgroup.centralizer ({t} : Set G) ∧ (blk (c.mat g) = 1 ∨ blk (c.mat g) = ℓ₀)}
  one_mem' := ⟨one_mem _, Or.inl (by rw [c.mat_one, blk_one])⟩
  mul_mem' {g g'} hg hg' := by
    refine ⟨mul_mem hg.1 hg'.1, ?_⟩
    rw [blk_mul_of_mem c ⟨hg.1.1.1, hg.1.2⟩ hg'.1.1.1]
    rcases hg.2 with h | h <;> rcases hg'.2 with h' | h' <;> rw [h, h']
    · exact Or.inl (mul_one 1)
    · exact Or.inr (one_mul ℓ₀)
    · exact Or.inr (mul_one ℓ₀)
    · exact Or.inl ℓ₀_mul_self
  inv_mem' {g} hg := by
    refine ⟨inv_mem hg.1, ?_⟩
    have hgK : g ∈ H ⊓ Subgroup.centralizer ({t} : Set G) := ⟨hg.1.1.1, hg.1.2⟩
    have h2 : blk (c.mat g) * blk (c.mat g) = 1 := by
      rcases hg.2 with h | h <;> rw [h]
      · exact mul_one 1
      · exact ℓ₀_mul_self
    rw [blk_inv_of_sq c hgK h2]
    exact hg.2

theorem IsCaseB.commutator_le {x : G} (hx : IsCaseB c x) :
    ⁅H ⊓ Subgroup.centralizer ({x} : Set G) ⊓ Subgroup.centralizer ({t} : Set G),
      H ⊓ Subgroup.centralizer ({x} : Set G) ⊓ Subgroup.centralizer ({t} : Set G)⁆ ≤
      pEll c x := by
  rw [Subgroup.commutator_le]
  intro p hp q hq
  have hpK : p ∈ H ⊓ Subgroup.centralizer ({t} : Set G) := ⟨hp.1.1, hp.2⟩
  have hqK : q ∈ H ⊓ Subgroup.centralizer ({t} : Set G) := ⟨hq.1.1, hq.2⟩
  have hU := commute_or_of_inU3 _ _
    (inU3_of_commute _ (hx.blk_commute hp) (det_blk_ne_zero c hpK))
    (inU3_of_commute _ (hx.blk_commute hq) (det_blk_ne_zero c hqK))
  refine ⟨?_, ?_⟩
  · rw [commutatorElement_def]
    exact mul_mem (mul_mem (mul_mem hp hq) (inv_mem hp)) (inv_mem hq)
  · rw [commutatorElement_def, blk_mul_of_mem c (mul_mem (mul_mem hpK hqK) (inv_mem hpK))
      (H.inv_mem hqK.1), blk_mul_of_mem c (mul_mem hpK hqK) (H.inv_mem hpK.1),
      blk_mul_of_mem c hpK hqK.1]
    rcases hU with h | h <;> rw [h]
    · left
      rw [mul_assoc (blk (c.mat q)), blk_mul_inv c hpK, mul_one, blk_mul_inv c hqK]
    · right
      rw [mul_assoc ℓ₀, mul_assoc ℓ₀, mul_assoc (blk (c.mat q)), blk_mul_inv c hpK, mul_one,
        blk_mul_inv c hqK, mul_one]

theorem IsCaseB.sq_of_mem_pEll {x g : G} (hx : IsCaseB c x) (hg : g ∈ pEll c x) :
    g ^ 2 = 1 ∨ g ^ 2 = t := by
  have hgK : g ∈ H ⊓ Subgroup.centralizer ({t} : Set G) := ⟨hg.1.1.1, hg.1.2⟩
  rcases hg.2 with h | h
  · exact c.sq_eq_one_or_eq_z (mem_E_of_blk_eq_one c hgK h)
  · have hgx : g * x = x * g := Subgroup.mem_centralizer_singleton_iff.1 hg.1.1.2
    have hgxE : g * x ∈ c.E := mem_E_of_blk_eq_one c (mul_mem hgK hx.1)
      (by rw [blk_mul_of_mem c hgK hx.1.1, h, hx.2.2.1, ℓ₀_mul_self])
    have h1 : (g * x) ^ 2 = g ^ 2 := by
      calc (g * x) ^ 2 = g * (x * g) * x := by rw [pow_two]; group
        _ = g * g * (x * x) := by rw [← hgx]; group
        _ = g ^ 2 := by rw [← pow_two x, hx.2.1, mul_one, pow_two]
    rw [← h1]
    exact c.sq_eq_one_or_eq_z hgxE

theorem IsCaseB.sqDerivedEq [Finite G] (hN : NaturalSL T H 4 1) (hns : ¬ HasComplement T H)
    {x : G} (hx : IsCaseB c x) :
    SqDerivedEq (H ⊓ Subgroup.centralizer ({x} : Set G) ⊓ Subgroup.centralizer ({t} : Set G))
      t := by
  refine ⟨fun y hy => hx.sq_of_mem_pEll (hx.commutator_le hy), ?_⟩
  have he1 : vecMul ![0, 1, 0] ℓ₀ = ![0, 1, 0] := by decide
  have hce : mk4 ![0, 1, 0] 1 * c.mat x = c.mat x * mk4 ![0, 1, 0] 1 := by
    rw [hx.mat_eq, mk4_mul, mk4_mul, he1, vecMul_one, one_mul, mul_one, add_comm]
  obtain ⟨e, heP, hem⟩ := hx.exists_lift_of_commute (by rw [det_mk4, det_one])
    (mk4_mulVec_e0 _ _) hce
  have heE : e ∈ c.E := mem_E_of_blk_eq_one c ⟨heP.1.1, heP.2⟩ (by rw [hem, blk_mk4])
  obtain ⟨hBℓ, hB1⟩ := commute_of_inU3 _ inU3_lv_e₁
  obtain ⟨b, hb⟩ := exists_top_of_inU3 _ hx.2.2.2 _ inU3_lv_e₁
  have hcl : mk4 b (lv ![0, 1, 0] v₀) * c.mat x = c.mat x * mk4 b (lv ![0, 1, 0] v₀) := by
    rw [hx.mat_eq, mk4_mul, mk4_mul, hBℓ, add_swap_of_eq hb]
  obtain ⟨l, hlP, hlm⟩ := hx.exists_lift_of_commute (by rw [det_mk4, hB1])
    (mk4_mulVec_e0 _ _) hcl
  have hlB : blk (c.mat l) = lv ![0, 1, 0] v₀ := by rw [hlm, blk_mk4]
  have hmem := Subgroup.commutator_mem_commutator heP hlP
  rw [commutatorElement_def] at hmem
  exact ⟨_, hmem, sq_commutator_eq_t c hN hns (k := ![0, 1, 0]) (f := v₀) (by decide)
    (by decide) (by decide) ⟨hlP.1.1, hlP.2⟩ hlB heE (by rw [hem, top_mk4]; decide)⟩

theorem caseB_core [Finite G] (hTH : T ≤ H) (hN : NaturalSL T H 4 1)
    (hns : ¬ HasComplement T H) {x t₁ : G} (hxH : x ∈ H) (hx2 : x ^ 2 = 1)
    (hnot : ¬ CentreTransvecting T t₁ x) (ht₁ : t₁ ∈ T) (ht₁1 : t₁ ≠ 1)
    (hs : ∃ s ∈ T, t₁ = s * (x * s * x⁻¹)) :
    Nat.card (H ⊓ Subgroup.centralizer ({x} : Set G) ⊓ Subgroup.centralizer ({t₁} : Set G) :
      Subgroup G) = 2 ^ 7 ∧
    SqDerivedEq (H ⊓ Subgroup.centralizer ({x} : Set G) ⊓ Subgroup.centralizer ({t₁} : Set G))
      t₁ ∧
    Nat.card (T ⊓ Subgroup.centralizer ({x} : Set G) : Subgroup G) = 4 ∧
    ∀ s' ∈ T, s' * x = x * s' → ∃ r ∈ T, s' = r * (x * r * x⁻¹) := by
  obtain ⟨c₀⟩ := nonempty_natCoord hTH hN ht₁ ht₁1
  obtain ⟨s, hsT, hts⟩ := hs
  have hxx : x * x = 1 := by rw [← pow_two]; exact hx2
  have hcs : x * s * x⁻¹ ∈ T := c₀.conj_mem hxH hsT
  have hxt : x * t₁ = t₁ * x := by
    have h1 : x * t₁ * x⁻¹ = t₁ := by
      rw [hts, show x * (s * (x * s * x⁻¹)) * x⁻¹ =
        (x * s * x⁻¹) * ((x * x) * s * (x * x)⁻¹) by group, hxx, one_mul, inv_one, mul_one,
        commute_of_mem_T c₀ hcs hsT]
    calc x * t₁ = x * t₁ * x⁻¹ * x := by group
      _ = t₁ * x := by rw [h1]
  have hxK : x ∈ H ⊓ Subgroup.centralizer ({t₁} : Set G) :=
    ⟨hxH, Subgroup.mem_centralizer_singleton_iff.2 hxt⟩
  have hblk2 : blk (c₀.mat x) * blk (c₀.mat x) = 1 := by
    rw [← blk_mul_of_mem c₀ hxK hxH, hxx, c₀.mat_one, blk_one]
  have hblk1 : blk (c₀.mat x) ≠ 1 := fun h =>
    hnot (centreTransvecting_of_mem_E c₀ (mem_E_of_blk_eq_one c₀ hxK h))
  obtain ⟨c, hcB⟩ := exists_coord_blk c₀ hxK hblk2 hblk1
  have hfix := c.mat_mulVec_e0 hxK
  have ha2 : top (c.mat x) + vecMul (top (c.mat x)) ℓ₀ = 0 := by
    have h := top_mul (c.mat x) (c.mat x) hfix
    rw [← c.mat_mul hxH hxH, hxx, c.mat_one, top_one, hcB] at h
    exact h.symm
  have hv : e0 = c.vec s + c.mat x *ᵥ c.vec s :=
    c.vec_z.symm.trans ((congrArg c.vec hts).trans
      (by rw [c.vec_mul hsT hcs, c.vec_conj hxH hsT]))
  have haw : ∃ w : Fin 3 → ZMod 2, top (c.mat x) ⬝ᵥ w = 1 ∧ w + ℓ₀ *ᵥ w = 0 := by
    refine ⟨tail (c.vec s), ?_, ?_⟩
    · have h0 := congrFun hv 0
      rw [Pi.add_apply, mulVec_apply_zero _ hfix, show e0 0 = 1 from Pi.single_eq_same 0 1,
        ← add_assoc, zmod_two_add_self, zero_add] at h0
      exact h0.symm
    · have h1 := congrArg tail hv
      rw [GL4.tail_add, tail_mulVec _ hfix, hcB, NSSecond.tail_e0] at h1
      exact h1.symm
  have hcase : IsCaseB c x := ⟨hxK, hx2, hcB, top_eq_of_rank_two _ ha2 haw⟩
  exact ⟨hcase.card_P, hcase.sqDerivedEq hN hns, hcase.card_centralizer_T,
    fun s' hs' hs'x => hcase.exists_eq_commutator hs' hs'x⟩

end CFSG.CGT.M24S.NSB
