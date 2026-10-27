module

public import CFSG.GH74.Generic.BProg.B2.GenLocL4OutAbs2
public import CFSG.GH74.Generic.BProg.B2.GenLocL4OutSel
public import CFSG.GH74.Generic.BProg.B2.GenLocL4OutSplit

public section

open CFSG CFSG.GH74 Subgroup Matrix
open scoped MatrixGroups

namespace CFSG.GH74.Generic.BProg.B2.GenLocL4Out

section Helpers

variable {F : Type} [Field F]

theorem isInnerDiag4_one : IsInnerDiag4 (1 : MulAut SL(4, F)) := ⟨1, fun g => by simp⟩

theorem not_isInnerDiag4_mul {φ ψ : MulAut SL(4, F)} (hφ : ¬ IsInnerDiag4 φ) (hψ : IsInnerDiag4 ψ) :
    ¬ IsInnerDiag4 (ψ * φ) := by
  intro h
  apply hφ
  have := isInnerDiag4_mul (isInnerDiag4_inv hψ) h
  simpa using this

theorem lift_unique {φ : MulAut SL(4, F)} {g h : GL (Fin 4) F} (hg : InnerLift φ g) (hh : InnerLift φ h) :
    ∃ c : F, c ≠ 0 ∧ (g : Matrix (Fin 4) (Fin 4) F) = c • (h : Matrix (Fin 4) (Fin 4) F) := by
  have hcomm : ∀ x : SL(4, F), (x : Matrix (Fin 4) (Fin 4) F) * (((h⁻¹ : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) * g) =
      (((h⁻¹ : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) * g) * (x : Matrix (Fin 4) (Fin 4) F) := by
    intro x
    have e := (hg x).symm.trans (hh x)
    have h1 : ((h⁻¹ : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) * (h : Matrix (Fin 4) (Fin 4) F) = 1 := coe_inv_mul h
    have h2 : ((g⁻¹ : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) * (g : Matrix (Fin 4) (Fin 4) F) = 1 := coe_inv_mul g
    calc (x : Matrix (Fin 4) (Fin 4) F) * (((h⁻¹ : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) * g)
        = ((h⁻¹ : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) * ((h : Matrix (Fin 4) (Fin 4) F) * x *
            ((h⁻¹ : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F)) * g := by
          simp only [Matrix.mul_assoc]
          rw [← Matrix.mul_assoc ((h⁻¹ : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) (h : Matrix (Fin 4) (Fin 4) F), h1,
            Matrix.one_mul]
      _ = ((h⁻¹ : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) * ((g : Matrix (Fin 4) (Fin 4) F) * x *
            ((g⁻¹ : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F)) * g := by rw [e]
      _ = _ := by
          simp only [Matrix.mul_assoc]
          rw [h2, Matrix.mul_one]
  obtain ⟨c, hc⟩ := GenLocL4Ext.exists_scalar_of_commute_sl (fun x => hcomm x)
  refine ⟨c, ?_, ?_⟩
  · intro h0
    rw [h0, zero_smul] at hc
    have hd := congrArg Matrix.det hc
    rw [Matrix.det_mul, Matrix.det_zero] at hd
    have hh0 : (h : Matrix (Fin 4) (Fin 4) F).det ≠ 0 := ((Matrix.isUnit_iff_isUnit_det _).1 h.isUnit).ne_zero
    have hg0 : (g : Matrix (Fin 4) (Fin 4) F).det ≠ 0 := ((Matrix.isUnit_iff_isUnit_det _).1 g.isUnit).ne_zero
    have hhi : ((h⁻¹ : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F).det ≠ 0 :=
      ((Matrix.isUnit_iff_isUnit_det _).1 (h⁻¹).isUnit).ne_zero
    exact (mul_ne_zero hhi hg0) hd
  · calc (g : Matrix (Fin 4) (Fin 4) F) = (h : Matrix (Fin 4) (Fin 4) F) * (((h⁻¹ : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) * g) := by
          rw [← Matrix.mul_assoc, coe_mul_inv h, Matrix.one_mul]
      _ = c • (h : Matrix (Fin 4) (Fin 4) F) := by rw [hc, Matrix.mul_smul, Matrix.mul_one]

theorem sq_eq_one_of_lifts {G H : Matrix (Fin 4) (Fin 4) F} {c μ : F} (hGH : G * H = c • (H * G))
    (hH : H * H = μ • (1 : Matrix (Fin 4) (Fin 4) F)) (hμ : μ ≠ 0) (hG : G.det ≠ 0) : c * c = 1 := by
  have h1 : G * (H * H) = μ • G := by rw [hH, Matrix.mul_smul, Matrix.mul_one]
  have h2 : G * (H * H) = (c * c * μ) • G := by
    calc G * (H * H) = (G * H) * H := by rw [Matrix.mul_assoc]
      _ = c • (H * G * H) := by rw [hGH, Matrix.smul_mul]
      _ = c • (H * (G * H)) := by rw [Matrix.mul_assoc]
      _ = c • (H * (c • (H * G))) := by rw [hGH]
      _ = (c * c) • ((H * H) * G) := by rw [Matrix.mul_smul, smul_smul, ← Matrix.mul_assoc]
      _ = (c * c * μ) • G := by rw [hH, Matrix.smul_mul, Matrix.one_mul, smul_smul]
  have h3 : (μ * (1 - c * c)) • G = 0 := by
    have : μ • G - (c * c * μ) • G = 0 := by rw [← h1, ← h2, sub_self]
    rw [← this, ← sub_smul]
    congr 1
    ring
  rcases smul_eq_zero.1 h3 with h | h
  · rcases mul_eq_zero.1 h with h' | h'
    · exact absurd h' hμ
    · linear_combination -h'
  · exfalso
    apply hG
    rw [h, Matrix.det_zero]

end Helpers

section GroupHelpers

variable {F : Type} [Field F] {A : Type} [Group A]

theorem mem_gamma_single [Finite A] (hA : CFSG.IsElementaryAbelian 2 A) (hcard : Nat.card A ≤ 4)
    (α : A →* MulAut SL(4, F)) {a : A} (ha : a ≠ 1) (x : SL(4, F)) (hx : α a x = x) : x ∈ gammaAct α := by
  have ha2 : a * a = 1 := WeakSigGen.mul_self_eq_one_of_isElementaryAbelian hA a
  refine mem_gamma_of_card hA α {a} ?_ x (by simpa using hx)
  have h2 : Nat.card ↥(Subgroup.zpowers a) = 2 := card_zpowers_of_sq a ha ha2
  rw [Subgroup.zpowers_eq_closure] at h2
  omega

theorem mem_gamma_pair [Finite A] (hA : CFSG.IsElementaryAbelian 2 A) (hcard : Nat.card A ≤ 8)
    (α : A →* MulAut SL(4, F)) {a b : A} (ha : a ≠ 1) (hb : b ≠ 1) (hab : a ≠ b) (x : SL(4, F))
    (hxa : α a x = x) (hxb : α b x = x) : x ∈ gammaAct α := by
  have ha2 : a * a = 1 := WeakSigGen.mul_self_eq_one_of_isElementaryAbelian hA a
  have hb2 : b * b = 1 := WeakSigGen.mul_self_eq_one_of_isElementaryAbelian hA b
  refine mem_gamma_of_card hA α {a, b} ?_ x ?_
  · have := four_le_card_closure_pair a b ha hb hab ha2 hb2
    omega
  · intro c hc
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hc
    rcases hc with rfl | rfl
    · exact hxa
    · exact hxb

@[expose] def innerSub (α : A →* MulAut SL(4, F)) : Subgroup A where
  carrier := {a | IsInnerDiag4 (α a)}
  mul_mem' := fun {a b} ha hb => by
    show IsInnerDiag4 (α (a * b))
    rw [map_mul]
    exact isInnerDiag4_mul ha hb
  one_mem' := by
    show IsInnerDiag4 (α 1)
    rw [map_one]
    exact isInnerDiag4_one
  inv_mem' := fun {a} ha => by
    show IsInnerDiag4 (α a⁻¹)
    rw [map_inv]
    exact isInnerDiag4_inv ha

theorem mem_innerSub {α : A →* MulAut SL(4, F)} {a : A} : a ∈ innerSub α ↔ IsInnerDiag4 (α a) := Iff.rfl

theorem innerSub_cover [Finite F] (hF4 : Nat.card F % 4 = 3) [Finite A] (hA : CFSG.IsElementaryAbelian 2 A)
    (α : A →* MulAut SL(4, F)) (hsect : SectionalTwoRankLE ↥(innJoin α) 4) {u : A} (hu : ¬ IsInnerDiag4 (α u)) :
    ∀ b : A, b ∈ innerSub α ∨ b * u ∈ innerSub α := by
  intro b
  by_cases hb : IsInnerDiag4 (α b)
  · exact Or.inl hb
  · right
    obtain ⟨B1, h1, -, -⟩ := graph_minus_of_sectional hF4 hA α b hb hsect
    obtain ⟨B2, h2, -, -⟩ := graph_minus_of_sectional hF4 hA α u hu hsect
    rw [mem_innerSub, map_mul]
    exact ⟨_, innerLift_graph_mul (u := α b) (v := α u) h1 h2⟩

theorem card_le_two_mul_innerSub [Finite F] (hF4 : Nat.card F % 4 = 3) [Finite A]
    (hA : CFSG.IsElementaryAbelian 2 A) (α : A →* MulAut SL(4, F))
    (hsect : SectionalTwoRankLE ↥(innJoin α) 4) {u : A} (hu : ¬ IsInnerDiag4 (α u)) :
    Nat.card A ≤ 2 * Nat.card ↥(innerSub α) := by
  have hidx := GenLocL4Ext.index_le_two_of_cover (innerSub α) u (innerSub_cover hF4 hA α hsect hu)
  have h := Subgroup.card_mul_index (innerSub α)
  have : Nat.card ↥(innerSub α) * (innerSub α).index ≤ Nat.card ↥(innerSub α) * 2 := Nat.mul_le_mul_left _ hidx
  omega

theorem exists_ne_one_of_one_lt [Finite A] (H : Subgroup A) (h : 1 < Nat.card H) : ∃ a : A, a ∈ H ∧ a ≠ 1 := by
  have h1 : H ≠ ⊥ := fun hb => by
    rw [hb] at h
    simp at h
  obtain ⟨a, ha⟩ := (Subgroup.ne_bot_iff_exists_ne_one).1 h1
  exact ⟨a, a.2, fun h => ha (Subtype.ext h)⟩

theorem exists_two_ne_one [Finite A] (H : Subgroup A) (h : 2 < Nat.card H) :
    ∃ a b : A, a ∈ H ∧ b ∈ H ∧ a ≠ 1 ∧ b ≠ 1 ∧ a ≠ b := by
  obtain ⟨a, ha, ha1⟩ := exists_ne_one_of_one_lt H (by omega)
  have hlt : ({1, a} : Set A).ncard < (H : Set A).ncard := by
    rw [Set.ncard_pair (Ne.symm ha1)]
    have : (H : Set A).ncard = Nat.card ↥H := (Nat.card_coe_set_eq _).symm
    omega
  obtain ⟨b, hb, hb2⟩ := Set.exists_mem_notMem_of_ncard_lt_ncard hlt (Set.toFinite _)
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or] at hb2
  exact ⟨a, b, ha, hb, ha1, hb2.1, fun h => hb2.2 h.symm⟩

end GroupHelpers

section Classes

@[expose] def ClassExt (F : Type) [Field F] [Finite F] : Prop :=
  Nat.card F % 4 = 3 → 7 ≤ Nat.card F →
  ∀ (B g : Matrix (Fin 4) (Fin 4) F), Bᵀ = B → B.det ≠ 0 → ¬ IsSquare B.det → g * g = (-1 : F) • (1 : Matrix (Fin 4) (Fin 4) F) →
    g * B = B * gᵀ → ∀ Γ : Subgroup SL(4, F),
      (∀ x : SL(4, F), (x : Matrix (Fin 4) (Fin 4) F) * g = g * (x : Matrix (Fin 4) (Fin 4) F) → x ∈ Γ) →
      (∀ x : SL(4, F), (x : Matrix (Fin 4) (Fin 4) F) * B * (x : Matrix (Fin 4) (Fin 4) F)ᵀ = B → x ∈ Γ) →
      (∀ x : SL(4, F), (x : Matrix (Fin 4) (Fin 4) F) * (g * B) * (x : Matrix (Fin 4) (Fin 4) F)ᵀ = g * B → x ∈ Γ) →
      Γ = ⊤

end Classes

section Rank2

variable {F : Type} [Field F] [Finite F] {A : Type} [Group A]

theorem rank2_main (hF4 : Nat.card F % 4 = 3) (h7 : 7 ≤ Nat.card F) (hExt : ClassExt F) [Finite A]
    (hA : CFSG.IsElementaryAbelian 2 A) (hcard : Nat.card A = 4) (α : A →* MulAut SL(4, F))
    (hinj : Function.Injective α) (hsect : SectionalTwoRankLE ↥(innJoin α) 4) {u : A}
    (hu : ¬ IsInnerDiag4 (α u)) : gammaAct α = ⊤ := by
  have hu1 : u ≠ 1 := fun h => hu (by rw [h, map_one]; exact isInnerDiag4_one)
  have hin := card_le_two_mul_innerSub hF4 hA α hsect hu
  obtain ⟨t, ht, ht1⟩ := exists_ne_one_of_one_lt (innerSub α) (by omega)
  have htin : IsInnerDiag4 (α t) := ht
  have ht2 : t * t = 1 := WeakSigGen.mul_self_eq_one_of_isElementaryAbelian hA t
  have hα2 : α t * α t = 1 := by rw [← map_mul, ht2, map_one]
  obtain ⟨g, hg⟩ := htin
  have hout' : ¬ IsInnerDiag4 (α (t * u)) := by
    rw [map_mul]
    exact not_isInnerDiag4_mul hu ⟨g, hg⟩
  have htu1 : t * u ≠ 1 := fun h => hout' (by rw [h, map_one]; exact isInnerDiag4_one)
  obtain ⟨B, hB, hBt, hBd⟩ := graph_minus_of_sectional hF4 hA α u hu hsect
  obtain ⟨B', hB', hB't, hB'd⟩ := graph_minus_of_sectional hF4 hA α (t * u) hout' hsect
  rw [map_mul] at hB'
  obtain ⟨⟨μ, hμ, hgg⟩, hgB, hdetg⟩ := type_data (show GraphForm (α u) B from hB) hBt hBd hg hα2
    (show GraphForm (α t * α u) B' from hB') hB't hB'd
  have hnsc : ∀ c : F, (g : Matrix (Fin 4) (Fin 4) F) ≠ c • (1 : Matrix (Fin 4) (Fin 4) F) := fun c hc =>
    ht1 (hinj (by rw [map_one]; exact eq_one_of_innerLift_scalar hg c hc))
  have hBdet0 : (B : Matrix (Fin 4) (Fin 4) F).det ≠ 0 := ((Matrix.isUnit_iff_isUnit_det _).1 B.isUnit).ne_zero
  have hfixB : ∀ x : SL(4, F), (x : Matrix (Fin 4) (Fin 4) F) * B * (x : Matrix (Fin 4) (Fin 4) F)ᵀ = B →
      x ∈ gammaAct α := fun x hx =>
    mem_gamma_single hA (by omega) α hu1 x
      (graphEq_fix (coe_mul_inv B) (show GraphForm (α u) B from hB).graphEq x hx)
  have hfixg : ∀ x : SL(4, F), (x : Matrix (Fin 4) (Fin 4) F) * g = g * (x : Matrix (Fin 4) (Fin 4) F) →
      x ∈ gammaAct α := fun x hx => mem_gamma_single hA (by omega) α ht1 x (innerLift_fix hg x hx)
  have hfixgB : ∀ x : SL(4, F), (x : Matrix (Fin 4) (Fin 4) F) * (g * B) * (x : Matrix (Fin 4) (Fin 4) F)ᵀ =
      g * B → x ∈ gammaAct α := fun x hx => by
    have hMi : (g : Matrix (Fin 4) (Fin 4) F) * B * (((B⁻¹ : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) *
        ((g⁻¹ : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F)) = 1 := by
      calc (g : Matrix (Fin 4) (Fin 4) F) * B * (((B⁻¹ : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) *
          ((g⁻¹ : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F))
          = g * (B * ((B⁻¹ : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F)) * ((g⁻¹ : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) := by
            simp only [Matrix.mul_assoc]
        _ = 1 := by rw [coe_mul_inv B, Matrix.mul_one, coe_mul_inv g]
    have := graphEq_fix hMi (graphEq_inner_mul (show GraphForm (α u) B from hB) hg) x hx
    refine mem_gamma_single hA (by omega) α htu1 x ?_
    rw [map_mul]
    exact this
  by_cases hsq : IsSquare μ
  · obtain ⟨ν, hν0, hεε, hεdet⟩ := split_norm hF4 hμ hgg hdetg hsq
    have hgε : (g : Matrix (Fin 4) (Fin 4) F) = ν • (ν⁻¹ • (g : Matrix (Fin 4) (Fin 4) F)) := by
      rw [smul_smul, mul_inv_cancel₀ hν0, one_smul]
    refine gen_split hF4 h7 B (ν⁻¹ • (g : Matrix (Fin 4) (Fin 4) F)) hBt hBdet0 hεε ?_ ?_ hεdet ?_ (gammaAct α)
      (fun x hx => hfixg x (by rw [hgε, Matrix.mul_smul, Matrix.smul_mul, hx])) hfixB
    · intro h
      exact hnsc ν (by rw [hgε, h])
    · intro h
      exact hnsc (-ν) (by rw [hgε, h]; simp)
    · rw [Matrix.smul_mul, hgB, Matrix.transpose_smul, Matrix.mul_smul]
  · obtain ⟨l, hl0, hii⟩ := ext_norm hF4 hμ hgg hsq
    refine hExt hF4 h7 B (l • (g : Matrix (Fin 4) (Fin 4) F)) hBt hBdet0 hBd hii ?_ (gammaAct α) ?_ hfixB ?_
    · rw [Matrix.smul_mul, hgB, Matrix.transpose_smul, Matrix.mul_smul]
    · intro x hx
      refine hfixg x ?_
      have := hx
      rw [Matrix.mul_smul, Matrix.smul_mul] at this
      exact (smul_right_injective _ hl0) this
    · intro x hx
      refine hfixgB x ?_
      rw [Matrix.smul_mul, Matrix.mul_smul, Matrix.smul_mul] at hx
      exact smul_right_injective _ hl0 hx

end Rank2

section LiftDataSec

variable {F : Type} [Field F] {A : Type} [Group A]

structure LiftData (α : A →* MulAut SL(4, F)) (B : Matrix (Fin 4) (Fin 4) F) (a : A) where
  g : GL (Fin 4) F
  lift : InnerLift (α a) g
  μ : F
  μ_ne : μ ≠ 0
  sq : (g : Matrix (Fin 4) (Fin 4) F) * g = μ • (1 : Matrix (Fin 4) (Fin 4) F)
  comp : (g : Matrix (Fin 4) (Fin 4) F) * B = B * (g : Matrix (Fin 4) (Fin 4) F)ᵀ
  detsq : IsSquare (g : Matrix (Fin 4) (Fin 4) F).det

theorem exists_liftData [Finite F] (hF4 : Nat.card F % 4 = 3) [Finite A] (hA : CFSG.IsElementaryAbelian 2 A)
    (α : A →* MulAut SL(4, F)) (hsect : SectionalTwoRankLE ↥(innJoin α) 4) {u a : A}
    (hu : ¬ IsInnerDiag4 (α u)) (ha : IsInnerDiag4 (α a)) {B : GL (Fin 4) F} (hB : GraphForm (α u) B)
    (hBt : (B : Matrix (Fin 4) (Fin 4) F)ᵀ = B) (hBd : ¬ IsSquare (B : Matrix (Fin 4) (Fin 4) F).det) :
    Nonempty (LiftData α (B : Matrix (Fin 4) (Fin 4) F) a) := by
  have ha2 : a * a = 1 := WeakSigGen.mul_self_eq_one_of_isElementaryAbelian hA a
  have hα2 : α a * α a = 1 := by rw [← map_mul, ha2, map_one]
  obtain ⟨g, hg⟩ := ha
  have hout' : ¬ IsInnerDiag4 (α (a * u)) := by
    rw [map_mul]
    exact not_isInnerDiag4_mul hu ⟨g, hg⟩
  obtain ⟨B', hB', hB't, hB'd⟩ := graph_minus_of_sectional hF4 hA α (a * u) hout' hsect
  rw [map_mul] at hB'
  obtain ⟨⟨μ, hμ, hgg⟩, hgB, hdetg⟩ := type_data hB hBt hBd hg hα2 (show GraphForm (α a * α u) B' from hB') hB't hB'd
  exact ⟨⟨g, hg, μ, hμ, hgg, hgB, hdetg⟩⟩

def LiftData.mul {α : A →* MulAut SL(4, F)} {B : Matrix (Fin 4) (Fin 4) F} {a b : A} (da : LiftData α B a)
    (db : LiftData α B b) (h : (da.g : Matrix (Fin 4) (Fin 4) F) * db.g = db.g * da.g) : LiftData α B (a * b) where
  g := da.g * db.g
  lift := by rw [map_mul]; exact innerLift_mul da.lift db.lift
  μ := da.μ * db.μ
  μ_ne := mul_ne_zero da.μ_ne db.μ_ne
  sq := by
    rw [Units.val_mul]
    have hsa := da.sq
    have hsb := db.sq
    have hh := h
    set ga : Matrix (Fin 4) (Fin 4) F := (da.g : Matrix (Fin 4) (Fin 4) F)
    set gb : Matrix (Fin 4) (Fin 4) F := (db.g : Matrix (Fin 4) (Fin 4) F)
    calc ga * gb * (ga * gb) = ga * (gb * ga) * gb := by simp only [Matrix.mul_assoc]
      _ = ga * (ga * gb) * gb := by rw [← hh]
      _ = (ga * ga) * (gb * gb) := by simp only [Matrix.mul_assoc]
      _ = (da.μ * db.μ) • (1 : Matrix (Fin 4) (Fin 4) F) := by
          rw [hsa, hsb, Matrix.smul_mul, Matrix.one_mul, smul_smul]
  comp := by
    rw [Units.val_mul]
    have hca := da.comp
    have hcb := db.comp
    have hh := h
    set ga : Matrix (Fin 4) (Fin 4) F := (da.g : Matrix (Fin 4) (Fin 4) F)
    set gb : Matrix (Fin 4) (Fin 4) F := (db.g : Matrix (Fin 4) (Fin 4) F)
    calc ga * gb * B = ga * (gb * B) := by rw [Matrix.mul_assoc]
      _ = ga * (B * gbᵀ) := by rw [hcb]
      _ = (ga * B) * gbᵀ := by rw [Matrix.mul_assoc]
      _ = B * gaᵀ * gbᵀ := by rw [hca]
      _ = B * (gb * ga)ᵀ := by rw [Matrix.transpose_mul, Matrix.mul_assoc]
      _ = B * (ga * gb)ᵀ := by rw [hh]
  detsq := by
    rw [Units.val_mul, Matrix.det_mul]
    exact da.detsq.mul db.detsq

theorem LiftData.comm [Finite F] (hF2 : (2 : F) ≠ 0) {α : A →* MulAut SL(4, F)} {B : Matrix (Fin 4) (Fin 4) F}
    {a b : A} (da : LiftData α B a) (db : LiftData α B b) (hab : a * b = b * a) (hBt : Bᵀ = B)
    (hBd : ¬ IsSquare B.det) :
    (da.g : Matrix (Fin 4) (Fin 4) F) * db.g = db.g * da.g := by
  have h1 : InnerLift (α (a * b)) (da.g * db.g) := by rw [map_mul]; exact innerLift_mul da.lift db.lift
  have h2 : InnerLift (α (a * b)) (db.g * da.g) := by rw [hab, map_mul]; exact innerLift_mul db.lift da.lift
  obtain ⟨c, hc0, hc⟩ := lift_unique h1 h2
  rw [Units.val_mul, Units.val_mul] at hc
  have hdga : (da.g : Matrix (Fin 4) (Fin 4) F).det ≠ 0 :=
    ((Matrix.isUnit_iff_isUnit_det _).1 da.g.isUnit).ne_zero
  have hdgb : (db.g : Matrix (Fin 4) (Fin 4) F).det ≠ 0 :=
    ((Matrix.isUnit_iff_isUnit_det _).1 db.g.isUnit).ne_zero
  have hcc := sq_eq_one_of_lifts hc db.sq db.μ_ne hdga
  have e1 := da.comp
  have e2 := db.comp
  have hsa := da.detsq
  have hsb := db.detsq
  set ga : Matrix (Fin 4) (Fin 4) F := (da.g : Matrix (Fin 4) (Fin 4) F)
  set gb : Matrix (Fin 4) (Fin 4) F := (db.g : Matrix (Fin 4) (Fin 4) F)
  rcases mul_self_eq_one_iff.1 hcc with rfl | rfl
  · simpa using hc
  · exfalso
    have hc' : gb * ga = -(ga * gb) := by rw [hc, neg_one_smul, neg_neg]
    have hskew : (ga * gb * B)ᵀ = -(ga * gb * B) := by
      have step1 : (ga * gb * B)ᵀ = B * (gbᵀ * gaᵀ) := by
        rw [Matrix.transpose_mul, Matrix.transpose_mul, hBt]
      have step2 : B * (gbᵀ * gaᵀ) = gb * (ga * B) := by
        rw [← Matrix.mul_assoc, ← e2, Matrix.mul_assoc, ← e1]
      rw [step1, step2, ← Matrix.mul_assoc, hc', Matrix.neg_mul]
    have hsq := isSquare_det_of_skew hF2 _ hskew
    rw [Matrix.det_mul, Matrix.det_mul] at hsq
    apply hBd
    have := IsSquare.div hsq (hsa.mul hsb)
    have e : ga.det * gb.det * B.det / (ga.det * gb.det) = B.det := by
      field_simp
    rwa [e] at this

end LiftDataSec

section Classes2

@[expose] def ClassDb (F : Type) [Field F] [Finite F] : Prop :=
  Nat.card F % 4 = 3 → 7 ≤ Nat.card F →
  ∀ (B g h : Matrix (Fin 4) (Fin 4) F), Bᵀ = B → B.det ≠ 0 → ¬ IsSquare B.det →
    g * g = 1 → h * h = 1 → g * h = h * g → g.det = 1 → h.det = 1 → g ≠ 1 → g ≠ -1 → h ≠ 1 → h ≠ -1 →
    h ≠ g → h ≠ -g → g * B = B * gᵀ → h * B = B * hᵀ → ∀ Γ : Subgroup SL(4, F),
      (∀ x : SL(4, F), (x : Matrix (Fin 4) (Fin 4) F) * g = g * (x : Matrix (Fin 4) (Fin 4) F) →
        (x : Matrix (Fin 4) (Fin 4) F) * h = h * (x : Matrix (Fin 4) (Fin 4) F) → x ∈ Γ) →
      (∀ x : SL(4, F), (x : Matrix (Fin 4) (Fin 4) F) * g = g * (x : Matrix (Fin 4) (Fin 4) F) →
        (x : Matrix (Fin 4) (Fin 4) F) * B * (x : Matrix (Fin 4) (Fin 4) F)ᵀ = B → x ∈ Γ) →
      (∀ x : SL(4, F), (x : Matrix (Fin 4) (Fin 4) F) * g = g * (x : Matrix (Fin 4) (Fin 4) F) →
        (x : Matrix (Fin 4) (Fin 4) F) * (h * B) * (x : Matrix (Fin 4) (Fin 4) F)ᵀ = h * B → x ∈ Γ) →
      (∀ x : SL(4, F), (x : Matrix (Fin 4) (Fin 4) F) * h = h * (x : Matrix (Fin 4) (Fin 4) F) →
        (x : Matrix (Fin 4) (Fin 4) F) * B * (x : Matrix (Fin 4) (Fin 4) F)ᵀ = B → x ∈ Γ) → Γ = ⊤

@[expose] def ClassDa (F : Type) [Field F] [Finite F] : Prop :=
  Nat.card F % 4 = 3 → 7 ≤ Nat.card F →
  ∀ (B X i : Matrix (Fin 4) (Fin 4) F), Bᵀ = B → B.det ≠ 0 → ¬ IsSquare B.det →
    X * X = 1 → X.det = 1 → X ≠ 1 → X ≠ -1 → i * i = (-1 : F) • (1 : Matrix (Fin 4) (Fin 4) F) → X * i = i * X →
    X * B = B * Xᵀ → i * B = B * iᵀ → ∀ Γ : Subgroup SL(4, F),
      (∀ x : SL(4, F), (x : Matrix (Fin 4) (Fin 4) F) * X = X * (x : Matrix (Fin 4) (Fin 4) F) →
        (x : Matrix (Fin 4) (Fin 4) F) * B * (x : Matrix (Fin 4) (Fin 4) F)ᵀ = B → x ∈ Γ) →
      (∀ x : SL(4, F), (x : Matrix (Fin 4) (Fin 4) F) * X = X * (x : Matrix (Fin 4) (Fin 4) F) →
        (x : Matrix (Fin 4) (Fin 4) F) * (i * B) * (x : Matrix (Fin 4) (Fin 4) F)ᵀ = i * B → x ∈ Γ) →
      (∀ x : SL(4, F), (x : Matrix (Fin 4) (Fin 4) F) * i = i * (x : Matrix (Fin 4) (Fin 4) F) →
        (x : Matrix (Fin 4) (Fin 4) F) * B * (x : Matrix (Fin 4) (Fin 4) F)ᵀ = B → x ∈ Γ) → Γ = ⊤

variable {F : Type} [Field F] {A : Type} [Group A]

theorem eq_of_lift_smul {s t : MulAut SL(4, F)} {g h : GL (Fin 4) F} (hs : InnerLift s g) (ht : InnerLift t h)
    {c : F} (hc : c ≠ 0) (hg : (g : Matrix (Fin 4) (Fin 4) F) = c • (h : Matrix (Fin 4) (Fin 4) F)) : s = t := by
  apply MulEquiv.ext
  intro x
  apply Subtype.ext
  have hginv : ((g⁻¹ : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) =
      c⁻¹ • ((h⁻¹ : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) := by
    refine Units.inv_eq_of_mul_eq_one_right ?_
    rw [hg, Matrix.smul_mul, Matrix.mul_smul, smul_smul, mul_inv_cancel₀ hc, one_smul, coe_mul_inv h]
  rw [hs x, ht x, hg, hginv, Matrix.smul_mul, Matrix.smul_mul, Matrix.mul_smul, smul_smul, mul_inv_cancel₀ hc, one_smul]

theorem fix_au {α : A →* MulAut SL(4, F)} {u a : A} {B : GL (Fin 4) F} (hB : GraphForm (α u) B)
    (da : LiftData α (B : Matrix (Fin 4) (Fin 4) F) a) (x : SL(4, F))
    (hx : (x : Matrix (Fin 4) (Fin 4) F) * ((da.g : Matrix (Fin 4) (Fin 4) F) * B) * (x : Matrix (Fin 4) (Fin 4) F)ᵀ =
      (da.g : Matrix (Fin 4) (Fin 4) F) * B) : α (a * u) x = x := by
  have hMi : (da.g : Matrix (Fin 4) (Fin 4) F) * B * (((B⁻¹ : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) *
      ((da.g⁻¹ : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F)) = 1 := by
    calc (da.g : Matrix (Fin 4) (Fin 4) F) * B * (((B⁻¹ : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) *
        ((da.g⁻¹ : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F))
        = da.g * (B * ((B⁻¹ : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F)) *
          ((da.g⁻¹ : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) := by simp only [Matrix.mul_assoc]
      _ = 1 := by rw [coe_mul_inv B, Matrix.mul_one, coe_mul_inv da.g]
  have := graphEq_fix hMi (graphEq_inner_mul hB da.lift) x hx
  rw [map_mul]
  exact this

end Classes2

section Rank3

variable {F : Type} [Field F] {A : Type} [Group A]

theorem comm_smul_of_comm {x M : Matrix (Fin 4) (Fin 4) F} (c : F) (h : x * M = M * x) :
    x * (c • M) = (c • M) * x := by
  rw [Matrix.mul_smul, Matrix.smul_mul, h]

theorem form_smul_of_form {x M : Matrix (Fin 4) (Fin 4) F} (c : F) (h : x * M * xᵀ = M) :
    x * (c • M) * xᵀ = c • M := by
  rw [Matrix.mul_smul, Matrix.smul_mul, h]

theorem ne_of_inner_outer {α : A →* MulAut SL(4, F)} {a u : A} (ha : IsInnerDiag4 (α a))
    (hu : ¬ IsInnerDiag4 (α u)) : a ≠ u := fun h => hu (h ▸ ha)

theorem outer_mul_ne_one {α : A →* MulAut SL(4, F)} {a u : A} (ha : IsInnerDiag4 (α a))
    (hu : ¬ IsInnerDiag4 (α u)) : a * u ≠ 1 := fun h => by
  have := not_isInnerDiag4_mul hu ha
  rw [← map_mul, h, map_one] at this
  exact this isInnerDiag4_one

theorem inner_ne_outer_mul {α : A →* MulAut SL(4, F)} {a b u : A} (ha : IsInnerDiag4 (α a))
    (hb : IsInnerDiag4 (α b)) (hu : ¬ IsInnerDiag4 (α u)) : a ≠ b * u := fun h => by
  have := not_isInnerDiag4_mul hu hb
  rw [← map_mul, ← h] at this
  exact this ha

theorem one_ne_outer {α : A →* MulAut SL(4, F)} {u : A} (hu : ¬ IsInnerDiag4 (α u)) : u ≠ 1 :=
  fun h => hu (by rw [h, map_one]; exact isInnerDiag4_one)

theorem rank3_Db_apply [Finite F] (hDb : ClassDb F) (hF4 : Nat.card F % 4 = 3) (h7 : 7 ≤ Nat.card F) [Finite A]
    (hA : CFSG.IsElementaryAbelian 2 A) (hcard : Nat.card A = 8) (α : A →* MulAut SL(4, F))
    (hinj : Function.Injective α) {u t s : A} (hu : ¬ IsInnerDiag4 (α u)) (ht1 : t ≠ 1) (hs1 : s ≠ 1) (hts : t ≠ s)
    {B : GL (Fin 4) F} (hB : GraphForm (α u) B) (hBt : (B : Matrix (Fin 4) (Fin 4) F)ᵀ = B)
    (hBd : ¬ IsSquare (B : Matrix (Fin 4) (Fin 4) F).det) (htin : IsInnerDiag4 (α t)) (hsin : IsInnerDiag4 (α s))
    (dt : LiftData α (B : Matrix (Fin 4) (Fin 4) F) t) (ds : LiftData α (B : Matrix (Fin 4) (Fin 4) F) s)
    (hcomm : (dt.g : Matrix (Fin 4) (Fin 4) F) * ds.g = ds.g * dt.g)
    (hμt : IsSquare dt.μ) (hμs : IsSquare ds.μ) : gammaAct α = ⊤ := by
  have hu1 := one_ne_outer hu
  have hBdet0 : (B : Matrix (Fin 4) (Fin 4) F).det ≠ 0 := ((Matrix.isUnit_iff_isUnit_det _).1 B.isUnit).ne_zero
  have hnsc_t : ∀ c : F, (dt.g : Matrix (Fin 4) (Fin 4) F) ≠ c • (1 : Matrix (Fin 4) (Fin 4) F) := fun c hc =>
    ht1 (hinj (by rw [map_one]; exact eq_one_of_innerLift_scalar dt.lift c hc))
  have hnsc_s : ∀ c : F, (ds.g : Matrix (Fin 4) (Fin 4) F) ≠ c • (1 : Matrix (Fin 4) (Fin 4) F) := fun c hc =>
    hs1 (hinj (by rw [map_one]; exact eq_one_of_innerLift_scalar ds.lift c hc))
  obtain ⟨νt, hνt0, hεt2, hεtdet⟩ := split_norm hF4 dt.μ_ne dt.sq dt.detsq hμt
  obtain ⟨νs, hνs0, hεs2, hεsdet⟩ := split_norm hF4 ds.μ_ne ds.sq ds.detsq hμs
  have hgt : (dt.g : Matrix (Fin 4) (Fin 4) F) = νt • (νt⁻¹ • (dt.g : Matrix (Fin 4) (Fin 4) F)) := by
    rw [smul_smul, mul_inv_cancel₀ hνt0, one_smul]
  have hgs : (ds.g : Matrix (Fin 4) (Fin 4) F) = νs • (νs⁻¹ • (ds.g : Matrix (Fin 4) (Fin 4) F)) := by
    rw [smul_smul, mul_inv_cancel₀ hνs0, one_smul]
  have hcomm' : (νt⁻¹ • (dt.g : Matrix (Fin 4) (Fin 4) F)) * (νs⁻¹ • (ds.g : Matrix (Fin 4) (Fin 4) F)) =
      (νs⁻¹ • (ds.g : Matrix (Fin 4) (Fin 4) F)) * (νt⁻¹ • (dt.g : Matrix (Fin 4) (Fin 4) F)) := by
    simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul, hcomm, mul_comm]
  have hBt' : ∀ (c : F) (g : Matrix (Fin 4) (Fin 4) F), g * (B : Matrix (Fin 4) (Fin 4) F) =
      (B : Matrix (Fin 4) (Fin 4) F) * gᵀ → (c • g) * (B : Matrix (Fin 4) (Fin 4) F) =
      (B : Matrix (Fin 4) (Fin 4) F) * (c • g)ᵀ := fun c g h => by
    rw [Matrix.smul_mul, h, Matrix.transpose_smul, Matrix.mul_smul]
  have hne1 : νs⁻¹ • (ds.g : Matrix (Fin 4) (Fin 4) F) ≠ νt⁻¹ • (dt.g : Matrix (Fin 4) (Fin 4) F) := by
    intro h
    have hg : (ds.g : Matrix (Fin 4) (Fin 4) F) = (νs * νt⁻¹) • (dt.g : Matrix (Fin 4) (Fin 4) F) := by
      calc (ds.g : Matrix (Fin 4) (Fin 4) F) = νs • (νs⁻¹ • (ds.g : Matrix (Fin 4) (Fin 4) F)) := hgs
        _ = νs • (νt⁻¹ • (dt.g : Matrix (Fin 4) (Fin 4) F)) := by rw [h]
        _ = _ := by rw [smul_smul]
    exact hts (hinj (eq_of_lift_smul ds.lift dt.lift (mul_ne_zero hνs0 (inv_ne_zero hνt0)) hg)).symm
  have hne2 : νs⁻¹ • (ds.g : Matrix (Fin 4) (Fin 4) F) ≠ -(νt⁻¹ • (dt.g : Matrix (Fin 4) (Fin 4) F)) := by
    intro h
    have hg : (ds.g : Matrix (Fin 4) (Fin 4) F) = (-(νs * νt⁻¹)) • (dt.g : Matrix (Fin 4) (Fin 4) F) := by
      calc (ds.g : Matrix (Fin 4) (Fin 4) F) = νs • (νs⁻¹ • (ds.g : Matrix (Fin 4) (Fin 4) F)) := hgs
        _ = νs • (-(νt⁻¹ • (dt.g : Matrix (Fin 4) (Fin 4) F))) := by rw [h]
        _ = _ := by rw [smul_neg, smul_smul, neg_smul]
    exact hts (hinj (eq_of_lift_smul ds.lift dt.lift (neg_ne_zero.2 (mul_ne_zero hνs0 (inv_ne_zero hνt0))) hg)).symm
  have fixT : ∀ x : SL(4, F), (x : Matrix (Fin 4) (Fin 4) F) * (νt⁻¹ • (dt.g : Matrix (Fin 4) (Fin 4) F)) =
      (νt⁻¹ • (dt.g : Matrix (Fin 4) (Fin 4) F)) * (x : Matrix (Fin 4) (Fin 4) F) → α t x = x := fun x hx =>
    innerLift_fix dt.lift x (by rw [hgt]; exact comm_smul_of_comm νt hx)
  have fixS : ∀ x : SL(4, F), (x : Matrix (Fin 4) (Fin 4) F) * (νs⁻¹ • (ds.g : Matrix (Fin 4) (Fin 4) F)) =
      (νs⁻¹ • (ds.g : Matrix (Fin 4) (Fin 4) F)) * (x : Matrix (Fin 4) (Fin 4) F) → α s x = x := fun x hx =>
    innerLift_fix ds.lift x (by rw [hgs]; exact comm_smul_of_comm νs hx)
  have fixU : ∀ x : SL(4, F), (x : Matrix (Fin 4) (Fin 4) F) * (B : Matrix (Fin 4) (Fin 4) F) *
      (x : Matrix (Fin 4) (Fin 4) F)ᵀ = B → α u x = x := fun x hx =>
    graphEq_fix (coe_mul_inv B) hB.graphEq x hx
  have fixSU : ∀ x : SL(4, F), (x : Matrix (Fin 4) (Fin 4) F) * ((νs⁻¹ • (ds.g : Matrix (Fin 4) (Fin 4) F)) *
      (B : Matrix (Fin 4) (Fin 4) F)) * (x : Matrix (Fin 4) (Fin 4) F)ᵀ =
      (νs⁻¹ • (ds.g : Matrix (Fin 4) (Fin 4) F)) * (B : Matrix (Fin 4) (Fin 4) F) → α (s * u) x = x := fun x hx =>
    fix_au hB ds x (by
      have e : (ds.g : Matrix (Fin 4) (Fin 4) F) * (B : Matrix (Fin 4) (Fin 4) F) =
          νs • ((νs⁻¹ • (ds.g : Matrix (Fin 4) (Fin 4) F)) * (B : Matrix (Fin 4) (Fin 4) F)) := by
        rw [Matrix.smul_mul, smul_smul, mul_inv_cancel₀ hνs0, one_smul]
      rw [e]
      exact form_smul_of_form νs hx)
  refine hDb hF4 h7 (B : Matrix (Fin 4) (Fin 4) F) (νt⁻¹ • (dt.g : Matrix (Fin 4) (Fin 4) F))
    (νs⁻¹ • (ds.g : Matrix (Fin 4) (Fin 4) F)) hBt hBdet0 hBd hεt2 hεs2 hcomm' hεtdet hεsdet ?_ ?_ ?_ ?_ hne1 hne2
    (hBt' _ _ dt.comp) (hBt' _ _ ds.comp) (gammaAct α) ?_ ?_ ?_ ?_
  · exact fun h => hnsc_t νt (by rw [hgt, h])
  · exact fun h => hnsc_t (-νt) (by rw [hgt, h]; simp)
  · exact fun h => hnsc_s νs (by rw [hgs, h])
  · exact fun h => hnsc_s (-νs) (by rw [hgs, h]; simp)
  · exact fun x hxt hxs => mem_gamma_pair hA (by omega) α ht1 hs1 hts x (fixT x hxt) (fixS x hxs)
  · exact fun x hxt hxB => mem_gamma_pair hA (by omega) α ht1 hu1 (ne_of_inner_outer htin hu) x (fixT x hxt) (fixU x hxB)
  · exact fun x hxt hxM => mem_gamma_pair hA (by omega) α ht1 (outer_mul_ne_one hsin hu)
      (inner_ne_outer_mul htin hsin hu) x (fixT x hxt) (fixSU x hxM)
  · exact fun x hxs hxB => mem_gamma_pair hA (by omega) α hs1 hu1 (ne_of_inner_outer hsin hu) x (fixS x hxs) (fixU x hxB)

theorem comm_smul_cancel {x M : Matrix (Fin 4) (Fin 4) F} {c : F} (hc : c ≠ 0)
    (h : x * (c • M) = (c • M) * x) : x * M = M * x := by
  rw [Matrix.mul_smul, Matrix.smul_mul] at h
  exact smul_right_injective _ hc h

theorem form_smul_cancel {x M : Matrix (Fin 4) (Fin 4) F} {c : F} (hc : c ≠ 0)
    (h : x * (c • M) * xᵀ = c • M) : x * M * xᵀ = M := by
  rw [Matrix.mul_smul, Matrix.smul_mul] at h
  exact smul_right_injective _ hc h

theorem rank3_Da_apply [Finite F] (hDa : ClassDa F) (hF4 : Nat.card F % 4 = 3) (h7 : 7 ≤ Nat.card F) [Finite A]
    (hA : CFSG.IsElementaryAbelian 2 A) (hcard : Nat.card A = 8) (α : A →* MulAut SL(4, F))
    (hinj : Function.Injective α) {u a b : A} (hu : ¬ IsInnerDiag4 (α u)) (ha1 : a ≠ 1) (hb1 : b ≠ 1)
    {B : GL (Fin 4) F} (hB : GraphForm (α u) B) (hBt : (B : Matrix (Fin 4) (Fin 4) F)ᵀ = B)
    (hBd : ¬ IsSquare (B : Matrix (Fin 4) (Fin 4) F).det) (hain : IsInnerDiag4 (α a)) (hbin : IsInnerDiag4 (α b))
    (da : LiftData α (B : Matrix (Fin 4) (Fin 4) F) a) (db : LiftData α (B : Matrix (Fin 4) (Fin 4) F) b)
    (hcomm : (da.g : Matrix (Fin 4) (Fin 4) F) * db.g = db.g * da.g)
    (hμa : IsSquare da.μ) (hμb : ¬ IsSquare db.μ) : gammaAct α = ⊤ := by
  have hu1 := one_ne_outer hu
  have hBdet0 : (B : Matrix (Fin 4) (Fin 4) F).det ≠ 0 := ((Matrix.isUnit_iff_isUnit_det _).1 B.isUnit).ne_zero
  have hnsc_a : ∀ c : F, (da.g : Matrix (Fin 4) (Fin 4) F) ≠ c • (1 : Matrix (Fin 4) (Fin 4) F) := fun c hc =>
    ha1 (hinj (by rw [map_one]; exact eq_one_of_innerLift_scalar da.lift c hc))
  obtain ⟨νa, hνa0, hX2, hXdet⟩ := split_norm hF4 da.μ_ne da.sq da.detsq hμa
  obtain ⟨l, hl0, hi2⟩ := ext_norm hF4 db.μ_ne db.sq hμb
  have hga : (da.g : Matrix (Fin 4) (Fin 4) F) = νa • (νa⁻¹ • (da.g : Matrix (Fin 4) (Fin 4) F)) := by
    rw [smul_smul, mul_inv_cancel₀ hνa0, one_smul]
  have hBt' : ∀ (c : F) (g : Matrix (Fin 4) (Fin 4) F), g * (B : Matrix (Fin 4) (Fin 4) F) =
      (B : Matrix (Fin 4) (Fin 4) F) * gᵀ → (c • g) * (B : Matrix (Fin 4) (Fin 4) F) =
      (B : Matrix (Fin 4) (Fin 4) F) * (c • g)ᵀ := fun c g h => by
    rw [Matrix.smul_mul, h, Matrix.transpose_smul, Matrix.mul_smul]
  have hcomm' : (νa⁻¹ • (da.g : Matrix (Fin 4) (Fin 4) F)) * (l • (db.g : Matrix (Fin 4) (Fin 4) F)) =
      (l • (db.g : Matrix (Fin 4) (Fin 4) F)) * (νa⁻¹ • (da.g : Matrix (Fin 4) (Fin 4) F)) := by
    simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul, hcomm, mul_comm]
  have fixA : ∀ x : SL(4, F), (x : Matrix (Fin 4) (Fin 4) F) * (νa⁻¹ • (da.g : Matrix (Fin 4) (Fin 4) F)) =
      (νa⁻¹ • (da.g : Matrix (Fin 4) (Fin 4) F)) * (x : Matrix (Fin 4) (Fin 4) F) → α a x = x := fun x hx =>
    innerLift_fix da.lift x (by rw [hga]; exact comm_smul_of_comm νa hx)
  have fixB : ∀ x : SL(4, F), (x : Matrix (Fin 4) (Fin 4) F) * (l • (db.g : Matrix (Fin 4) (Fin 4) F)) =
      (l • (db.g : Matrix (Fin 4) (Fin 4) F)) * (x : Matrix (Fin 4) (Fin 4) F) → α b x = x := fun x hx =>
    innerLift_fix db.lift x (comm_smul_cancel hl0 hx)
  have fixU : ∀ x : SL(4, F), (x : Matrix (Fin 4) (Fin 4) F) * (B : Matrix (Fin 4) (Fin 4) F) *
      (x : Matrix (Fin 4) (Fin 4) F)ᵀ = B → α u x = x := fun x hx =>
    graphEq_fix (coe_mul_inv B) hB.graphEq x hx
  have fixBU : ∀ x : SL(4, F), (x : Matrix (Fin 4) (Fin 4) F) * ((l • (db.g : Matrix (Fin 4) (Fin 4) F)) *
      (B : Matrix (Fin 4) (Fin 4) F)) * (x : Matrix (Fin 4) (Fin 4) F)ᵀ =
      (l • (db.g : Matrix (Fin 4) (Fin 4) F)) * (B : Matrix (Fin 4) (Fin 4) F) → α (b * u) x = x := fun x hx =>
    fix_au hB db x (by
      rw [Matrix.smul_mul] at hx
      exact form_smul_cancel hl0 hx)
  refine hDa hF4 h7 (B : Matrix (Fin 4) (Fin 4) F) (νa⁻¹ • (da.g : Matrix (Fin 4) (Fin 4) F))
    (l • (db.g : Matrix (Fin 4) (Fin 4) F)) hBt hBdet0 hBd hX2 hXdet ?_ ?_ hi2 hcomm'
    (hBt' _ _ da.comp) (hBt' _ _ db.comp) (gammaAct α) ?_ ?_ ?_
  · exact fun h => hnsc_a νa (by rw [hga, h])
  · exact fun h => hnsc_a (-νa) (by rw [hga, h]; simp)
  · exact fun x hxa hxB => mem_gamma_pair hA (by omega) α ha1 hu1 (ne_of_inner_outer hain hu) x (fixA x hxa) (fixU x hxB)
  · exact fun x hxa hxM => mem_gamma_pair hA (by omega) α ha1 (outer_mul_ne_one hbin hu)
      (inner_ne_outer_mul hain hbin hu) x (fixA x hxa) (fixBU x hxM)
  · exact fun x hxb hxB => mem_gamma_pair hA (by omega) α hb1 hu1 (ne_of_inner_outer hbin hu) x (fixB x hxb) (fixU x hxB)

theorem rank3_main [Finite F] (hDb : ClassDb F) (hDa : ClassDa F) (hF4 : Nat.card F % 4 = 3) (h7 : 7 ≤ Nat.card F)
    [Finite A] (hA : CFSG.IsElementaryAbelian 2 A) (hcard : Nat.card A = 8) (α : A →* MulAut SL(4, F))
    (hinj : Function.Injective α) (hsect : SectionalTwoRankLE ↥(innJoin α) 4) {u : A}
    (hu : ¬ IsInnerDiag4 (α u)) : gammaAct α = ⊤ := by
  have hF2 : (2 : F) ≠ 0 := Ring.two_ne_zero (ringChar_ne_two_of_card_mod hF4)
  have hin := card_le_two_mul_innerSub hF4 hA α hsect hu
  obtain ⟨t, s, ht, hs, ht1, hs1, hts⟩ := exists_two_ne_one (innerSub α) (by omega)
  have htin : IsInnerDiag4 (α t) := ht
  have hsin : IsInnerDiag4 (α s) := hs
  obtain ⟨B, hB, hBt, hBd⟩ := graph_minus_of_sectional hF4 hA α u hu hsect
  have hB' : GraphForm (α u) B := hB
  obtain ⟨dt⟩ := exists_liftData hF4 hA α hsect hu htin hB' hBt hBd
  obtain ⟨ds⟩ := exists_liftData hF4 hA α hsect hu hsin hB' hBt hBd
  have hcommA : t * s = s * t := by
    have := hA
    exact mul_comm' t s
  have hcomm := LiftData.comm hF2 dt ds hcommA hBt hBd
  by_cases hμt : IsSquare dt.μ
  · by_cases hμs : IsSquare ds.μ
    · exact rank3_Db_apply hDb hF4 h7 hA hcard α hinj hu ht1 hs1 hts hB' hBt hBd htin hsin dt ds hcomm hμt hμs
    · exact rank3_Da_apply hDa hF4 h7 hA hcard α hinj hu ht1 hs1 hB' hBt hBd htin hsin dt ds hcomm hμt hμs
  · by_cases hμs : IsSquare ds.μ
    · exact rank3_Da_apply hDa hF4 h7 hA hcard α hinj hu hs1 ht1 hB' hBt hBd hsin htin ds dt hcomm.symm hμs hμt
    · have hts1 : t * s ≠ 1 := fun h => hts (by
        have ht2 : t * t = 1 := WeakSigGen.mul_self_eq_one_of_isElementaryAbelian hA t
        exact (mul_left_cancel (h.trans ht2.symm)).symm)
      have hcomm2 : ((dt.mul ds hcomm).g : Matrix (Fin 4) (Fin 4) F) * dt.g =
          dt.g * (dt.mul ds hcomm).g := by
        show ((dt.g * ds.g : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) * dt.g =
          dt.g * ((dt.g * ds.g : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F)
        simp only [Units.val_mul, Matrix.mul_assoc]
        rw [← hcomm]
      have hμts : IsSquare (dt.mul ds hcomm).μ := isSquare_mul_of_not_isSquare hμt hμs
      have htsin : IsInnerDiag4 (α (t * s)) := by
        rw [map_mul]
        exact isInnerDiag4_mul htin hsin
      exact rank3_Da_apply hDa hF4 h7 hA hcard α hinj hu hts1 ht1 hB' hBt hBd htsin htin (dt.mul ds hcomm) dt
        hcomm2 hμts hμt

end Rank3

section Main

variable {F : Type} [Field F] [Finite F]

theorem gammaAct_sl4_outer_of_classes (hExt : ClassExt F) (hDb : ClassDb F) (hDa : ClassDa F)
    (hF4 : Nat.card F % 4 = 3) (h7 : 7 ≤ Nat.card F) {A : Type} [Group A] [Finite A]
    (α : A →* MulAut SL(4, F)) (hA : IsRank23 A) (hout : ∃ a : A, ¬ IsInnerDiag4 (α a))
    (hsect : SectionalTwoRankLE ↥(innJoin α) 4) : gammaAct α = ⊤ := by
  by_cases hex : ∃ E : Subgroup A, pRank 2 A - 1 ≤ pRank 2 ↥E ∧ E ≤ α.ker
  · obtain ⟨E, hE, hk⟩ := hex
    exact gammaAct_eq_top_of_le_ker α hE hk
  · simp only [not_exists, not_and] at hex
    obtain ⟨hR, hg, -⟩ := range_reduction α hA hex
    rw [hg]
    have hfin : Finite ↥α.range := Finite.of_surjective _ α.rangeRestrict_surjective
    obtain ⟨a, ha⟩ := hout
    have hsectD : SectionalTwoRankLE ↥(innJoin α.range.subtype) 4 := by
      have : innJoin α.range.subtype = innJoin α := by
        unfold innJoin
        rw [Subgroup.range_subtype]
      rw [this]
      exact hsect
    have huD : ¬ IsInnerDiag4 (α.range.subtype ⟨α a, a, rfl⟩) := ha
    have hcard := GenLocBasic.card_eq_two_pow_pRank_type hR.1
    rcases hR.2 with h2 | h3
    · exact rank2_main hF4 h7 hExt hR.1 (by rw [hcard, h2]; norm_num) α.range.subtype
        Subtype.val_injective hsectD huD
    · exact rank3_main hDb hDa hF4 h7 hR.1 (by rw [hcard, h3]; norm_num) α.range.subtype
        Subtype.val_injective hsectD huD

end Main

end CFSG.GH74.Generic.BProg.B2.GenLocL4Out
