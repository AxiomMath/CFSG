module

public import CFSG.GH74.GLS.LU.Local.FiveStdRepX1c
public import CFSG.GH74.GLS.LU.Local.FiveStdRepA2

public section

open Subgroup CFSG CFSG.Blueprint CFSG.Assembly.LowTwoRank CFSG.GH74.GLS CFSG.GH74.GLS.LU.Local

open scoped Pointwise

namespace CFSG.GH74.GLS.LU.Local.Five

open CFSG.GH74.GLS.LU.Local.FiveStd CFSG.GH74.GLS.LU.Local.Five.FiveStdRep

namespace FiveStdX1

variable {G : Type} [Group G] [Finite G] {st : FiveStdSetting G} {tE uE a b g : E} {H' : Subgroup G}
  (c : GoodCtx st tE uE a b g H')

namespace GoodCtx

include c

omit [Finite G] in
theorem clause_closure {wE : E} (hwv : validE wE = true) (hwK : st.ι wE ∈ st.K₁)
    (hcl : eqL (closureL [g, wE]) K1l = true) :
    Subgroup.closure ((zpowers (st.ι g) : Set G) ∪ {st.ι wE}) = st.K₁ := by
  obtain ⟨-, hV1, -⟩ := baseCheck_spec c.base
  apply le_antisymm
  · rw [Subgroup.closure_le]
    rintro x (hx | hx)
    · exact Subgroup.zpowers_le.2 c.gK hx
    · rw [Set.mem_singleton_iff.1 hx]
      exact hwK
  · intro k hk
    obtain ⟨hVcl, hsub⟩ := st.model.closureL_sub (V_cons c.gv (V_cons hwv V_nil))
    have hEq := (st.model.eqL_iff hVcl hV1).1 hcl
    have hk' : k ∈ S st.ι K1l := by
      rw [← st.hK₁]
      exact hk
    rw [← hEq] at hk'
    obtain ⟨x, hx, rfl⟩ := mem_S.1 hk'
    refine Subgroup.closure_mono ?_ (hsub x hx)
    rintro _ ⟨y, hy, rfl⟩
    rcases List.mem_cons.1 hy with rfl | hy
    · exact Or.inl (Subgroup.mem_zpowers _)
    · rw [List.mem_singleton.1 hy]
      exact Or.inr rfl

theorem clause_sylow (hs : sylCover = true) {wE : E} (hwv : validE wE = true)
    (hq : ∀ q ∈ sylInv a b, ∃ v ∈ ppE wE (conjE tE wE) 4 4,
      eqL q.2.2 (conjLL v (ppE g (conjE tE g) 5 5)) = true) :
    ∀ R : Subgroup G, IsSylowIn 5 R (Cz st.z) → (∀ h ∈ H', cjL h R = R) →
      ∃ w ∈ zpowers (st.ι wE) ⊔ zpowers (st.ι tE * st.ι wE * (st.ι tE)⁻¹),
        R = cjL w (XX (st.ι tE) (zpowers (st.ι g))) := by
  intro R hR hRinv
  obtain ⟨-, hV1, hV2, -⟩ := baseCheck_spec c.base
  obtain ⟨q, hq36, hRq⟩ := FiveStdSetting.sylow_cover st c.base hs R hR
  obtain ⟨gx, hgx, gy, hgy, rfl⟩ := FiveStdBase.mem_Syl36.1 hq36
  obtain ⟨hgxK, -⟩ := FiveStdBase.X1cands_spec hgx
  obtain ⟨hgyK, -⟩ := FiveStdBase.Y1cands_spec hgy
  have hvgx : validE gx = true := hV1 gx hgxK
  have hvgy : validE gy = true := hV2 gy hgyK
  have hVq : V (ppE gx gy 5 5) := st.model.V_ppE hvgx hvgy 5 5
  have hRq' : (R : Set G) = S st.ι (ppE gx gy 5 5) := hRq
  have hgxS : st.ι gx ∈ S st.ι (ppE gx gy 5 5) := by
    rw [st.model.S_ppE hvgx hvgy]
    exact ⟨1, by norm_num, 0, by norm_num, by simp⟩
  have hgyS : st.ι gy ∈ S st.ι (ppE gx gy 5 5) := by
    rw [st.model.S_ppE hvgx hvgy]
    exact ⟨0, by norm_num, 1, by norm_num, by simp⟩
  have hnorm : normAll [a, b] [gx, gy] (ppE gx gy 5 5) = true := by
    rw [st.model.normAll_iff (V_cons c.ha (V_cons c.hb V_nil)) (V_cons hvgx (V_cons hvgy V_nil)) hVq]
    intro h hh x hx
    have hhH : st.ι h ∈ H' := by
      rcases List.mem_cons.1 hh with rfl | hh
      · exact c.aH
      · rw [List.mem_singleton.1 hh]
        exact c.bH
    have hxS : st.ι x ∈ S st.ι (ppE gx gy 5 5) := by
      rcases List.mem_cons.1 hx with rfl | hx
      · exact hgxS
      · rw [List.mem_singleton.1 hx]
        exact hgyS
    have hxR : st.ι x ∈ R := by
      rw [← SetLike.mem_coe, hRq']
      exact hxS
    have h1 := repCj_mem_self (g := st.ι h) hxR
    rw [hRinv _ hhH, ← SetLike.mem_coe, hRq'] at h1
    exact h1
  have hqSyl : (gx, gy, ppE gx gy 5 5) ∈ sylInv a b := mem_sylInv.2 ⟨hq36, hnorm⟩
  obtain ⟨v, hvW, hveq⟩ := hq _ hqSyl
  have hVXX : V (ppE g (conjE tE g) 5 5) := st.model.V_ppE c.gv c.g2v 5 5
  have hw2v : validE (conjE tE wE) = true := st.model.valid_conjE c.ht hwv
  have hvv : validE v = true := (st.model.V_ppE hwv hw2v 4 4) v hvW
  have hSeq := (st.model.eqL_iff hVq (st.model.V_conjLL hvv hVXX)).1 hveq
  rw [st.model.S_conjLL hvv hVXX] at hSeq
  refine ⟨st.ι v, ?_, ?_⟩
  · have hmem : st.ι v ∈ S st.ι (ppE wE (conjE tE wE) 4 4) := mem_S.2 ⟨v, hvW, rfl⟩
    rw [st.model.S_ppE hwv hw2v] at hmem
    obtain ⟨i, -, j, -, hij⟩ := hmem
    rw [hij, st.model.map_conjE c.ht hwv]
    exact Subgroup.mul_mem_sup (Subgroup.pow_mem _ (Subgroup.mem_zpowers _) i)
      (Subgroup.pow_mem _ (Subgroup.mem_zpowers _) j)
  · rw [c.XX_eq]
    ext x
    have hxR : x ∈ R ↔ ∃ y ∈ S st.ι (ppE g (conjE tE g) 5 5), x = st.ι v * y * (st.ι v)⁻¹ := by
      rw [← SetLike.mem_coe, hRq', hSeq]
      exact Iff.rfl
    have hXXmem : ∀ y, y ∈ S st.ι (ppE g (conjE tE g) 5 5) ↔
        y ∈ zpowers (st.ι g) ⊔ zpowers (st.ι (conjE tE g)) := fun y => by
      rw [← c.XX_coe]
      exact Iff.rfl
    rw [hxR, repCj_mem]
    constructor
    · rintro ⟨y, hy, rfl⟩
      have : (st.ι v)⁻¹ * (st.ι v * y * (st.ι v)⁻¹) * st.ι v = y := by group
      rw [this]
      exact (hXXmem y).1 hy
    · intro hx
      exact ⟨(st.ι v)⁻¹ * x * st.ι v, (hXXmem _).2 hx, by group⟩

end GoodCtx

end FiveStdX1

namespace FiveStdSetting

variable {G : Type} [Group G] [Finite G] (st : FiveStdSetting G)

open FiveStdX1

theorem rep_X1 (hb : baseCheck = true) (hs : sylCover = true) {tE uE : E} (hp : pairCond tE uE = true)
    (hr : checkRep tE uE = true) :
    ∀ (H' : Subgroup G) (w' : G), IsTorus st.z (st.ι uE) st.K₁ st.K₂ H' →
      (w' ∈ st.K₁ ∧ w' * w' = st.z ∧ w' * st.ι uE * w'⁻¹ = st.ι uE * st.z) →
      ∃ X₁' : Subgroup G, X₁' ≤ st.K₁ ∧ Nat.card ↥X₁' = 5 ∧ (∀ h ∈ H', cjL h X₁' = X₁') ∧
        Subgroup.closure ((X₁' : Set G) ∪ {w'}) = st.K₁ ∧ (∀ x ∈ X₁', st.ι uE * x * (st.ι uE)⁻¹ = x⁻¹) ∧
        normalizer ((XB (st.ι tE) X₁' : Subgroup G) : Set G) ⊓ Cz st.z = XB (st.ι tE) X₁' ⊔ st.K₁ ⊔ H' ∧
        centralizer ((XB (st.ι tE) X₁' : Subgroup G) : Set G) ⊓ Cz st.z = XB (st.ι tE) X₁' ⊔ st.K₁ ∧
        normalizer ((XX (st.ι tE) X₁' : Subgroup G) : Set G) ⊓ Cz st.z =
          XX (st.ι tE) X₁' ⊔ H' ⊔ zpowers (st.ι tE) ∧
        (∀ R : Subgroup G, IsSylowIn 5 R (Cz st.z) → (∀ h ∈ H', cjL h R = R) →
          ∃ w ∈ zpowers w' ⊔ zpowers (st.ι tE * w' * (st.ι tE)⁻¹), R = cjL w (XX (st.ι tE) X₁')) ∧
        (∀ A : Subgroup G, A ≤ XX (st.ι tE) X₁' → Nat.card ↥A = 5 → (∀ h ∈ H', cjL h A = A) →
          A = X₁' ∨ A = XB (st.ι tE) X₁') ∧
        Nat.card ↥(XZ (st.ι tE) X₁') = 5 := by
  intro H' w' hH' ⟨hwK, hww, hwu⟩
  obtain ⟨ht, hu⟩ := pairCond_valid hb hp
  obtain ⟨a, b, hab, hP, hW, -⟩ := checkRep_spec hr
  obtain ⟨-, hV1, -⟩ := baseCheck_spec hb
  have hz := validE_zE hb
  obtain ⟨haP, hbP, -⟩ := mem_tpOf_iff.1 hab
  have hva : validE a = true := V_PlOf uE a haP
  have hvb : validE b = true := V_PlOf uE b hbP
  have hHS := torus_set_eq st hb hu hab hP hH'
  have hwS : w' ∈ S st.ι K1l := by
    rw [← st.hK₁]
    exact hwK
  obtain ⟨wE, hwE, rfl⟩ := mem_S.1 hwS
  have hwv : validE wE = true := hV1 wE hwE
  have hww' : mulE wE wE = zE := by
    apply st.model.inj _ _ (st.model.valid_mul wE wE hwv hwv) hz
    rw [st.model.map_mul wE wE hwv hwv]
    exact hww
  have hwu' : conjE wE uE = mulE uE zE := by
    apply st.model.inj _ _ (st.model.valid_conjE hwv hu) (st.model.valid_mul uE zE hu hz)
    rw [st.model.map_conjE hwv hu, st.model.map_mul uE zE hu hz]
    exact hwu
  have hwmem : wE ∈ WlOf uE := mem_WlOf_iff.2 ⟨hwE, hww', hwu'⟩
  obtain ⟨-, g, hgood, hcl, hq⟩ := checkX1_spec (checkW_spec hW wE hwmem)
  obtain ⟨hgX, hggood⟩ := mem_good.1 hgood
  have c : GoodCtx st tE uE a b g H' := ⟨hb, ht, hu, hva, hvb, hHS, hgX, hggood⟩
  exact ⟨zpowers (st.ι g), Subgroup.zpowers_le.2 c.gK, by rw [Nat.card_zpowers, c.g_facts.2.2], c.clause_inv,
    c.clause_closure hwv hwK hcl, c.clause_u, c.clause_normXB, c.clause_cenXB, c.clause_normXX,
    c.clause_sylow hs hwv hq, c.clause_inv_sub, c.clause_card⟩

end FiveStdSetting

end CFSG.GH74.GLS.LU.Local.Five
