module

public import CFSG.Quasithin.H13.L32AC38h
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.L32AC37b

public section

namespace CFSG.Quasithin.H13.L32A.C

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.LieType.BorelTits
open CFSG.Quasithin.Vol2.Ch10.SecF.C10E4

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G] {T L V H : Subgroup G}

namespace Ctx38

variable {b c : G} (C : Ctx38 T L V H b c)
include C

theorem false_of_e9_fix_F4 (h1222 : Stmt12_2_2_F4) (h1332 : Stmt13_3_2_F4) (h1334 : A6.Stmt13_3_4_F4)
    (h4 : Lemma14_7_4_two_three_F4) {V₂ : Subgroup G} (hV2 : A6.IsV2 T V V₂)
    (hW : C.Wt = tildeOf (fsuV1 T V) (conjClosure V H))
    {e₁ e₂ : MulAut (IntMod C.Wt C.hUe)} (he₁ : e₁ ∈ C.ψ.range) (he₂ : e₂ ∈ C.ψ.range)
    (h31 : e₁ ^ 3 = 1) (h32 : e₂ ^ 3 = 1) (hc : Commute e₁ e₂)
    (hind : ∀ a b : ZMod 3, e₁ ^ a.val * e₂ ^ b.val = 1 → a = 0 ∧ b = 0)
    {a : G} (ha : a ∈ V₂) (haV : a ∉ fsuV1 T V)
    (hfix₁ : e₁ (IntMod.mk C.hUe ⟨_, C.tilde_mem_Wt hW (le_conjClosure V H (hV2.2.1 ha))⟩) =
      IntMod.mk C.hUe ⟨_, C.tilde_mem_Wt hW (le_conjClosure V H (hV2.2.1 ha))⟩)
    (hfix₂ : e₂ (IntMod.mk C.hUe ⟨_, C.tilde_mem_Wt hW (le_conjClosure V H (hV2.2.1 ha))⟩) =
      IntMod.mk C.hUe ⟨_, C.tilde_mem_Wt hW (le_conjClosure V H (hV2.2.1 ha))⟩) : False := by
  have hMod := stmtL32NModule_of_inputs_F4 h1332 h1334
  have : IsMulCommutative ↥V := (hMod G T L V C.S.hyp.hyp C.S.hyp.fsu).1.1
  have S14 := Hyp147.set14_F4 C.S.hyp h1222 h1332 h1334 hV2
  set N := Subgroup.normalizer (fsuV1 T V : Set G) with hN
  have haU : a ∈ conjClosure V H := le_conjClosure V H (hV2.2.1 ha)
  have haN : a ∈ N := C.HN (C.UH haU)
  set at' := secMk N (fsuV1 T V) ⟨a, haN⟩ with hat

  have hcm : ∀ g : ↥H, C.ψ g (IntMod.mk C.hUe ⟨_, C.tilde_mem_Wt hW haU⟩) =
      IntMod.mk C.hUe ⟨_, C.tilde_mem_Wt hW haU⟩ →
      (g : G) ∈ centralizerMod (fsuV1 T V) H V₂ := by
    intro g hg
    have hgt : secMk N (fsuV1 T V) ⟨g, C.HN g.2⟩ * at' *
        (secMk N (fsuV1 T V) ⟨g, C.HN g.2⟩)⁻¹ = at' := by
      have h1 := congrArg IntMod.val hg
      rw [C.ψ_apply_val] at h1
      exact h1
    refine mem_centralizerMod.mpr ⟨g.2, C.HN g.2, fun u hu => ?_⟩
    have huN : u ∈ N := C.VN (hV2.2.1 hu)
    have hut : secMk N (fsuV1 T V) ⟨u, huN⟩ = 1 ∨ secMk N (fsuV1 T V) ⟨u, huN⟩ = at' := by
      rcases S14.mem_V2_F4 ha haV hu with h | h
      · left
        exact secMk_eq_one_iff.mpr h
      · right
        have h1 : at' * secMk N (fsuV1 T V) ⟨u, huN⟩ = 1 := by
          rw [hat, ← map_mul]
          exact secMk_eq_one_iff.mpr h
        have h2 : at' * at' = 1 := by
          rw [hat, ← map_mul]
          exact secMk_eq_one_iff.mpr (by
            show a * a ∈ fsuV1 T V
            rw [S14.mul_self_V_F4 (hV2.2.1 ha)]
            exact one_mem _)
        calc secMk N (fsuV1 T V) ⟨u, huN⟩ = (at' * at') * secMk N (fsuV1 T V) ⟨u, huN⟩ := by
              rw [h2, one_mul]
          _ = at' * (at' * secMk N (fsuV1 T V) ⟨u, huN⟩) := mul_assoc _ _ _
          _ = at' := by rw [h1, mul_one]
    have hfixu : secMk N (fsuV1 T V) ⟨g, C.HN g.2⟩ * secMk N (fsuV1 T V) ⟨u, huN⟩ *
        (secMk N (fsuV1 T V) ⟨g, C.HN g.2⟩)⁻¹ = secMk N (fsuV1 T V) ⟨u, huN⟩ := by
      rcases hut with h | h
      · rw [h, mul_one, mul_inv_cancel]
      · rw [h]
        exact hgt
    have h3 : secMk N (fsuV1 T V) (⟨g, C.HN g.2⟩ * ⟨u, huN⟩ * ⟨g, C.HN g.2⟩⁻¹ * ⟨u, huN⟩⁻¹) =
        1 := by
      rw [map_mul, map_mul, map_mul, map_inv, map_inv, hfixu, mul_inv_cancel]
    exact secMk_eq_one_iff.mp h3

  have hlift : ∀ {e : MulAut (IntMod C.Wt C.hUe)}, e ∈ C.ψ.range → e ^ 3 = 1 →
      e (IntMod.mk C.hUe ⟨_, C.tilde_mem_Wt hW haU⟩) = IntMod.mk C.hUe ⟨_, C.tilde_mem_Wt hW haU⟩ →
      ∃ g : ↥H, C.ψ g = e ∧ (g : G) ∈ Subgroup.centralizer (V₂ : Set G) := by
    intro e he h3 hfe
    obtain ⟨g, hge, hodd⟩ := C.exists_odd_lift he h3
    refine ⟨g, hge, oTwoUpper_le_centralizer_F4 C.S h1332 h1334 hV2
      (mem_oTwoUpper_of_odd (hcm g (by rw [hge]; exact hfe)) hodd)⟩
  obtain ⟨g₁, hg₁, hg₁C⟩ := hlift he₁ h31 hfix₁
  obtain ⟨g₂, hg₂, hg₂C⟩ := hlift he₂ h32 hfix₂

  set A := Subgroup.centralizer (V₂ : Set G) ⊓ H with hA
  let φ : ↥A →* MulAut (IntMod C.Wt C.hUe) := C.ψ.comp (Subgroup.inclusion inf_le_right)
  have hker2 : IsPGroup 2 φ.ker := by
    rintro ⟨k, hk⟩
    have hkQ : ((k : ↥A) : G) ∈ pCoreOf 2 H :=
      C.mem_pCoreOf_of_ψ hW (k : ↥A).2.2 hk
    obtain ⟨m, hm⟩ := (pCoreOf_isPGroup 2 H) ⟨_, hkQ⟩
    refine ⟨m, Subtype.ext (Subtype.ext ?_)⟩
    have := congrArg Subtype.val hm
    simpa using this

  let E9 : Multiplicative (ZMod 3 × ZMod 3) →* MulAut (IntMod C.Wt C.hUe) :=
    { toFun := fun x => e₁ ^ (Multiplicative.toAdd x).1.val * e₂ ^ (Multiplicative.toAdd x).2.val
      map_one' := by simp
      map_mul' := fun x y => by
        simp only [toAdd_mul, Prod.fst_add, Prod.snd_add]
        rw [Lin.pow_val_add3 h31, Lin.pow_val_add3 h32]
        have h1 : Commute (e₁ ^ (Multiplicative.toAdd y).1.val)
            (e₂ ^ (Multiplicative.toAdd x).2.val) := hc.pow_pow _ _
        calc e₁ ^ (Multiplicative.toAdd x).1.val * e₁ ^ (Multiplicative.toAdd y).1.val *
              (e₂ ^ (Multiplicative.toAdd x).2.val * e₂ ^ (Multiplicative.toAdd y).2.val)
            = e₁ ^ (Multiplicative.toAdd x).1.val * (e₁ ^ (Multiplicative.toAdd y).1.val *
                e₂ ^ (Multiplicative.toAdd x).2.val) * e₂ ^ (Multiplicative.toAdd y).2.val := by
              simp only [mul_assoc]
          _ = e₁ ^ (Multiplicative.toAdd x).1.val * (e₂ ^ (Multiplicative.toAdd x).2.val *
                e₁ ^ (Multiplicative.toAdd y).1.val) * e₂ ^ (Multiplicative.toAdd y).2.val := by
              rw [h1.eq]
          _ = _ := by simp only [mul_assoc] }
  have hE9inj : Function.Injective E9 := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro x hx
    obtain ⟨h1, h2⟩ := hind _ _ (MonoidHom.mem_ker.mp hx)
    rw [Subgroup.mem_bot]
    apply Multiplicative.toAdd.injective
    rw [toAdd_one]
    ext
    · exact h1
    · exact h2
  have hcard : Nat.card E9.range = 9 := by
    rw [Nat.card_congr (MonoidHom.ofInjective hE9inj).symm.toEquiv,
      Nat.card_congr Multiplicative.toAdd, Nat.card_prod, Nat.card_zmod]
  have hEc : ∀ x ∈ E9.range, ∀ y ∈ E9.range, x * y = y * x := by
    rintro _ ⟨x, rfl⟩ _ ⟨y, rfl⟩
    rw [← map_mul, ← map_mul, mul_comm]
  have hE3 : ∀ x ∈ E9.range, x ^ 3 = 1 := by
    rintro _ ⟨x, rfl⟩
    rw [← map_pow]
    have : x ^ 3 = 1 := by
      apply Multiplicative.toAdd.injective
      rw [toAdd_pow, toAdd_one]
      obtain ⟨p, q⟩ := Multiplicative.toAdd x
      ext <;> simp only [Prod.smul_mk, Prod.fst_zero, Prod.snd_zero] <;> revert p q <;> decide
    rw [this, map_one]
  have hEr : E9.range ≤ φ.range := by
    rintro _ ⟨x, rfl⟩
    refine ⟨⟨(g₁ : G), hg₁C, g₁.2⟩ ^ (Multiplicative.toAdd x).1.val *
      ⟨(g₂ : G), hg₂C, g₂.2⟩ ^ (Multiplicative.toAdd x).2.val, ?_⟩
    rw [map_mul, map_pow, map_pow]
    show C.ψ _ ^ _ * C.ψ _ ^ _ = _
    have e1 : Subgroup.inclusion (inf_le_right : A ≤ H) ⟨(g₁ : G), hg₁C, g₁.2⟩ = g₁ := rfl
    have e2 : Subgroup.inclusion (inf_le_right : A ≤ H) ⟨(g₂ : G), hg₂C, g₂.2⟩ = g₂ := rfl
    rw [e1, e2, hg₁, hg₂]
    rfl
  obtain ⟨P, hP, hP9⟩ := exists_e9_of_hom φ hker2 hEr hcard hEc hE3
  have h2r := two_le_pRank_of_injective (Subgroup.inclusion (inf_le_left : A ≤
    Subgroup.centralizer (V₂ : Set G))) (Subgroup.inclusion_injective _) hP hP9
  have h1r := (h4 _ T L V V₂ C.S.hyp hV2).2.2.2.2
  have h2r' : 2 ≤ CFSG.pRank 3 ↥(Subgroup.centralizer (V₂ : Set G)) := h2r
  omega

end Ctx38

end CFSG.Quasithin.H13.L32A.C
