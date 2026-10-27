module

public import CFSG.GH74.GLS.LU.Local.FiveStdRepX1

public section

open Subgroup CFSG CFSG.Blueprint CFSG.Assembly.LowTwoRank CFSG.GH74.GLS CFSG.GH74.GLS.LU.Local

open scoped Pointwise

namespace CFSG.GH74.GLS.LU.Local.Five

open CFSG.GH74.GLS.LU.Local.FiveStd CFSG.GH74.GLS.LU.Local.Five.FiveStdRep

namespace FiveStdX1

theorem goodX1_spec {t u a b : E} {H0 : List E} {g : E} (h : goodX1 t u a b H0 g = true) :
    normAll [a, b] [g] (powers g 5) = true ∧ conjE u g = invE g ∧ commE g (conjE t g) = true ∧
    (ppE g (conjE t g) 5 5).Nodup ∧
    eqL (Cs.filter fun c => normG c [conjE t g] (powers (conjE t g) 5))
      (prod3 (powers (conjE t g) 5) K1l H0) = true ∧
    eqL (Cs.filter fun c => cenG c [conjE t g]) (prod2 (powers (conjE t g) 5) K1l) = true ∧
    eqL (Cs.filter fun c => normG c [g, conjE t g] (ppE g (conjE t g) 5 5))
      (prod3 (ppE g (conjE t g) 5 5) H0 [oneE, t]) = true ∧
    (∀ x ∈ ppE g (conjE t g) 5 5, x = oneE ∨ normAll [a, b] [x] (powers x 5) = false ∨
      eqL (powers x 5) (powers g 5) = true ∨ eqL (powers x 5) (powers (conjE t g) 5) = true) ∧
    ((ppE g (conjE t g) 5 5).filter fun x => commE x t).length = 5 := by
  unfold goodX1 at h
  simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true, nodupL_iff, Bool.or_eq_true, Bool.not_eq_true'] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩ := h
  refine ⟨h1, h2, h3, h4, h5, h6, h7, fun x hx => ?_, h9⟩
  rcases h8 x hx with h | (h | h) | h
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr (Or.inl h))
  · exact Or.inr (Or.inr (Or.inr h))

theorem checkX1_spec {t : E} {Syl : List (E × E × List E)} {good : List E} {w : E}
    (h : checkX1 t Syl good w = true) :
    commE w (conjE t w) = true ∧ ∃ g ∈ good, eqL (closureL [g, w]) K1l = true ∧
      ∀ q ∈ Syl, ∃ v ∈ ppE w (conjE t w) 4 4, eqL q.2.2 (conjLL v (ppE g (conjE t g) 5 5)) = true := by
  unfold checkX1 at h
  simpa only [Bool.and_eq_true, List.any_eq_true, List.all_eq_true] using h

theorem checkW_spec {t u a b : E} (h : checkW t u a b = true) :
    ∀ w ∈ WlOf u,
      checkX1 t (sylInv a b) (X1cands.filter fun g => goodX1 t u a b (ppE a b 4 4) g) w = true := by
  unfold checkW at h
  simpa only [List.all_eq_true] using h

theorem mem_sylInv {a b : E} {q : E × E × List E} :
    q ∈ sylInv a b ↔ q ∈ Syl36 ∧ normAll [a, b] [q.1, q.2.1] q.2.2 = true := by
  unfold sylInv
  rw [List.mem_filter]

theorem mem_good {t u a b : E} {H0 : List E} {g : E} :
    g ∈ X1cands.filter (fun g => goodX1 t u a b H0 g) ↔ g ∈ X1cands ∧ goodX1 t u a b H0 g = true := by
  rw [List.mem_filter]

theorem zpowers_le_closure_list {G : Type} [Group G] {ι : E → G} (L : List E) {x : E} (hx : x ∈ L) :
    ι x ∈ closure (ι '' {y | y ∈ L}) :=
  Subgroup.subset_closure ⟨x, hx, rfl⟩

theorem sup3_of_coe_eq_D {G : Type} [Group G] {N P Q R : Subgroup G} {D : Set G}
    (h : (N : Set G) = (P : Set G) * (Q : Set G) * D) (h1 : (1 : G) ∈ D) (hD : D ⊆ (R : Set G))
    (hRN : R ≤ N) : N = P ⊔ Q ⊔ R := by
  apply le_antisymm
  · intro g hg
    have : g ∈ (P : Set G) * (Q : Set G) * D := by rw [← h]; exact hg
    obtain ⟨_, ⟨x, hx, y, hy, rfl⟩, w, hw, rfl⟩ := Set.mem_mul.1 this
    exact Subgroup.mul_mem_sup (Subgroup.mul_mem_sup hx hy) (hD hw)
  · refine sup_le (sup_le ?_ ?_) hRN
    · intro x hx
      have : x * 1 * 1 ∈ (P : Set G) * (Q : Set G) * D :=
        Set.mul_mem_mul (Set.mul_mem_mul hx Q.one_mem) h1
      rw [mul_one, mul_one, ← h] at this
      exact this
    · intro y hy
      have : 1 * y * 1 ∈ (P : Set G) * (Q : Set G) * D :=
        Set.mul_mem_mul (Set.mul_mem_mul P.one_mem hy) h1
      rw [one_mul, mul_one, ← h] at this
      exact this

variable {G : Type} [Group G] (st : FiveStdSetting G)

structure GoodCtx (tE uE a b g : E) (H' : Subgroup G) : Prop where
  base : baseCheck = true
  ht : validE tE = true
  hu : validE uE = true
  ha : validE a = true
  hb : validE b = true
  hH' : (H' : Set G) = S st.ι (ppE a b 4 4)
  hg : g ∈ X1cands
  hgood : goodX1 tE uE a b (ppE a b 4 4) g = true

namespace GoodCtx

variable {st} {tE uE a b g : E} {H' : Subgroup G} (c : GoodCtx st tE uE a b g H')

include c

theorem g_facts : validE g = true ∧ st.ι g ∈ st.K₁ ∧ orderOf (st.ι g) = 5 := by
  obtain ⟨hgK, hg5⟩ := FiveStdBase.X1cands_spec c.hg
  obtain ⟨-, hV1, -⟩ := baseCheck_spec c.base
  have hv := hV1 g hgK
  refine ⟨hv, ?_, st.model.orderOf_of_ordE hv hg5 (by norm_num)⟩
  have : st.ι g ∈ ((st.K₁ : Subgroup G) : Set G) := by
    rw [st.hK₁]
    exact mem_S.2 ⟨g, hgK, rfl⟩
  exact this

theorem gv : validE g = true := c.g_facts.1

theorem gK : st.ι g ∈ st.K₁ := c.g_facts.2.1

theorem g5 : st.ι g ^ 5 = 1 := by
  have := pow_orderOf_eq_one (st.ι g)
  rwa [c.g_facts.2.2] at this

theorem g2v : validE (conjE tE g) = true := st.model.valid_conjE c.ht c.gv

theorem ι2 : st.ι (conjE tE g) = st.ι tE * st.ι g * (st.ι tE)⁻¹ := st.model.map_conjE c.ht c.gv

theorem g25 : st.ι (conjE tE g) ^ 5 = 1 := by
  rw [c.ι2, conj_pow, c.g5, mul_one, mul_inv_cancel]

theorem comm : st.ι g * st.ι (conjE tE g) = st.ι (conjE tE g) * st.ι g :=
  (st.model.commE_iff c.gv c.g2v).1 (goodX1_spec c.hgood).2.2.1

theorem XB_eq : XB (st.ι tE) (zpowers (st.ι g)) = zpowers (st.ι (conjE tE g)) := by
  rw [c.ι2]
  exact cjL_zpowers _ _

theorem XX_eq : XX (st.ι tE) (zpowers (st.ι g)) = zpowers (st.ι g) ⊔ zpowers (st.ι (conjE tE g)) := by
  rw [← c.XB_eq]

theorem XX_coe : ((zpowers (st.ι g) ⊔ zpowers (st.ι (conjE tE g)) : Subgroup G) : Set G) =
    S st.ι (ppE g (conjE tE g) 5 5) :=
  coe_sup_zpowers_eq_S st.model c.gv c.g2v c.comm c.g5 c.g25

theorem aH : st.ι a ∈ H' := by
  have : st.ι a ∈ S st.ι (ppE a b 4 4) := by
    rw [st.model.S_ppE c.ha c.hb]
    exact ⟨1, by norm_num, 0, by norm_num, by simp⟩
  rw [← c.hH'] at this
  exact this

theorem bH : st.ι b ∈ H' := by
  have : st.ι b ∈ S st.ι (ppE a b 4 4) := by
    rw [st.model.S_ppE c.ha c.hb]
    exact ⟨0, by norm_num, 1, by norm_num, by simp⟩
  rw [← c.hH'] at this
  exact this

theorem H_le {N : Subgroup G} (ha : st.ι a ∈ N) (hb : st.ι b ∈ N) : H' ≤ N := by
  intro x hx
  have hx' : x ∈ S st.ι (ppE a b 4 4) := by rw [← c.hH']; exact hx
  rw [st.model.S_ppE c.ha c.hb] at hx'
  obtain ⟨i, -, j, -, rfl⟩ := hx'
  exact N.mul_mem (N.pow_mem ha i) (N.pow_mem hb j)

theorem clause_u : ∀ x ∈ zpowers (st.ι g), st.ι uE * x * (st.ι uE)⁻¹ = x⁻¹ := by
  have h1 : st.ι uE * st.ι g * (st.ι uE)⁻¹ = (st.ι g)⁻¹ := by
    have := congrArg st.ι (goodX1_spec c.hgood).2.1
    rwa [st.model.map_conjE c.hu c.gv, st.model.map_inv _ c.gv] at this
  intro x hx
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hx
  rw [← conj_zpow, h1, inv_zpow]

end GoodCtx

section Fin

variable [Finite G]

namespace GoodCtx

variable {st} {tE uE a b g : E} {H' : Subgroup G} (c : GoodCtx st tE uE a b g H')

include c

theorem g_coe : ((zpowers (st.ι g) : Subgroup G) : Set G) = S st.ι (powers g 5) :=
  coe_zpowers_eq_S st.model c.gv c.g5

theorem g2_coe : ((zpowers (st.ι (conjE tE g)) : Subgroup G) : Set G) = S st.ι (powers (conjE tE g) 5) :=
  coe_zpowers_eq_S st.model c.g2v c.g25

theorem clause_inv : ∀ h ∈ H', cjL h (zpowers (st.ι g)) = zpowers (st.ι g) := by
  have hn := (goodX1_spec c.hgood).1
  unfold normAll at hn
  rw [List.all_eq_true] at hn
  have hK : zpowers (st.ι g) ≤ closure (st.ι '' {x | x ∈ [g]}) :=
    Subgroup.zpowers_le.2 (zpowers_le_closure_list [g] (by simp))
  have hna : st.ι a ∈ normalizer ((zpowers (st.ι g) : Subgroup G) : Set G) :=
    (normG_iff_normalizer st.model c.ha (V_cons c.gv V_nil) (st.model.V_powers c.gv 5) c.g_coe
      (by simp) hK).1 (hn a (by simp))
  have hnb : st.ι b ∈ normalizer ((zpowers (st.ι g) : Subgroup G) : Set G) :=
    (normG_iff_normalizer st.model c.hb (V_cons c.gv V_nil) (st.model.V_powers c.gv 5) c.g_coe
      (by simp) hK).1 (hn b (by simp))
  intro h hh
  rw [repCj_eq_iff]
  exact c.H_le hna hnb hh

end GoodCtx

end Fin

end FiveStdX1

end CFSG.GH74.GLS.LU.Local.Five
