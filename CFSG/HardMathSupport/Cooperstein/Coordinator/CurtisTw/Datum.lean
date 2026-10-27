module

public import CFSG.HardMathSupport.Cooperstein.Coordinator.CurtisTw.Elements
public import CFSG.HardMathSupport.Cooperstein.Coordinator.CurtisTw.HeckeDeg
public import CFSG.Quasithin.Background.SmithCurtisDatum
public import CFSG.LieType.Chevalley.GraphFixedSylowOpposition
public import CFSG.Timmesfeld.Orders.ExceptionalTwistedBruhat

set_option linter.unusedSectionVars false

public noncomputable section

namespace CFSG.HardMathSupport.Cooperstein.Coordinator.CurtisTw

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.Quasithin.SmithCurtis
  CFSG.Timmesfeld.ExceptionalOrders
open scoped Pointwise


variable {t : TwistTag} {K : Type} [Field K] {σ : K →+* K}

theorem isPGroup_graphFixedNegUnipotent_subgroupOf [Finite K] (p : ℕ) [CharP K p]
    (D : LongestData t) :
    IsPGroup p ((graphFixedNegUnipotent t K σ).subgroupOf (graphFixedRootGroup t K σ)) := by
  have hmap : (posUnipotent t.tag K).map
      (MulAut.conj (canonicalRep (coxeterSystem t.tag) K D.w)).toMonoidHom =
        negUnipotent t.tag K := by
    unfold posUnipotent negUnipotent
    rw [(canonical_weyl_root_transport t.tag K).1 D.w _ (fun α h => h.1), D.image_smul_posRoots]
  have h1 : IsPGroup p (negUnipotent t.tag K) := by
    rw [← hmap]
    exact (isPGroup_posUnipotent p t.tag).of_equiv
      (Subgroup.equivMapOfInjective _ _ (MulAut.conj _).injective)
  exact (h1.to_le (inf_le_left : graphFixedNegUnipotent t K σ ≤ _)).of_equiv
    (Subgroup.subgroupOfEquivOfLe (graphFixedNegUnipotent_le_graphFixedRootGroup t K σ)).symm

theorem cover_graphFixedRootGroup (D : LongestData t) (hσ : Function.Surjective σ)
    {g : ModGL t.tag K} (hg : g ∈ graphFixedRootGroup t K σ) :
    ∃ l ∈ graphFixedNegUnipotent t K σ, ∃ v : ↥(relWeylTwist t),
      ∃ h ∈ graphFixedRootTorus t K σ, ∃ u ∈ graphFixedPosUnipotent t K σ,
        g = l * canonicalRep (coxeterSystem t.tag) K (v : WeylGroup t.tag) * (h * u) := by
  set n₁ := canonicalRep (coxeterSystem t.tag) K D.w with hn₁_def
  have hmon : ∀ {w : WeylGroup t.tag}, w ∈ relWeylTwist t →
      canonicalRep (coxeterSystem t.tag) K w ∈ graphFixedRootGroup t K σ := fun hw =>
    graphFixedRootMonomial_le t K σ (canonicalRep_mem_graphFixedRootMonomial t K σ hw)
  have hΓ : ∀ {w : WeylGroup t.tag}, w ∈ relWeylTwist t →
      canonicalRep (coxeterSystem t.tag) K w ∈ twistedFixedGroup t K σ := fun hw =>
    canonicalRep_mem_twistedFixedGroup t K σ ((mem_relWeylTwist t).1 hw)
  have hn₁ : n₁ ∈ graphFixedRootGroup t K σ := hmon D.mem
  have hg' : n₁⁻¹ * g ∈ (graphFixedRootGroup t K σ : Set (ModGL t.tag K)) :=
    mul_mem (inv_mem hn₁) hg
  rw [graphFixedRootGroup_eq_iUnion hσ] at hg'
  obtain ⟨v, hv⟩ := Set.mem_iUnion.1 hg'
  obtain ⟨b, hb, b', hb', hbb⟩ := mem_graphFixedRootBruhatCell.1 hv
  have hb2 : b ∈ (graphFixedRootTorus t K σ : Set (ModGL t.tag K)) *
      (graphFixedPosUnipotent t K σ : Set (ModGL t.tag K)) := by
    rw [← graphFixedRootBorel_eq_mul hσ]
    exact hb
  have hb'2 : b' ∈ (graphFixedRootTorus t K σ : Set (ModGL t.tag K)) *
      (graphFixedPosUnipotent t K σ : Set (ModGL t.tag K)) := by
    rw [← graphFixedRootBorel_eq_mul hσ]
    exact hb'
  obtain ⟨h₀, hh₀, u₀, hu₀, rfl⟩ := hb2
  obtain ⟨h₁, hh₁, u₁, hu₁, rfl⟩ := hb'2
  obtain ⟨k, hk, hkn⟩ := canonicalRep_mul_mem (R := K) D.w (v : WeylGroup t.tag)
  set n' := canonicalRep (coxeterSystem t.tag) K (D.w * (v : WeylGroup t.tag)) with hn'_def
  have hvw : D.w * (v : WeylGroup t.tag) ∈ relWeylTwist t := mul_mem D.mem v.2
  have hnorm : ∀ {w : WeylGroup t.tag}, w ∈ relWeylTwist t →
      ∀ {h : ModGL t.tag K}, h ∈ graphFixedRootTorus t K σ →
        canonicalRep (coxeterSystem t.tag) K w * h *
          (canonicalRep (coxeterSystem t.tag) K w)⁻¹ ∈ graphFixedRootTorus t K σ :=
    fun hw h hh => (Subgroup.mem_normalizer_iff.mp
      (canonicalRep_mem_normalizer_graphFixedRootTorus (σ := σ) hw) h).mp hh
  set H₀ := n₁ * h₀ * n₁⁻¹ with hH₀_def
  have hH₀ : H₀ ∈ graphFixedRootTorus t K σ := hnorm D.mem hh₀
  set L₀ := n₁ * u₀ * n₁⁻¹ with hL₀_def
  have hL₀ : L₀ ∈ graphFixedNegUnipotent t K σ := (conj_mem_negUnipotent_iff D u₀).2 hu₀
  have hkT : k ∈ graphFixedRootTorus t K σ := by
    have hk' : k = n₁ * canonicalRep (coxeterSystem t.tag) K (v : WeylGroup t.tag) * n'⁻¹ := by
      rw [hkn]
      group
    refine Subgroup.mem_inf.2 ⟨Subgroup.mem_inf.2 ⟨hk, ?_⟩, ?_⟩
    · rw [hk']
      exact mul_mem (mul_mem (hΓ D.mem) (hΓ v.2)) (inv_mem (hΓ hvw))
    · rw [hk']
      exact mul_mem (mul_mem hn₁ (hmon v.2)) (inv_mem (hmon hvw))
  have hHk : n'⁻¹ * (H₀ * k) * n' ∈ graphFixedRootTorus t K σ :=
    inv_conj_mem_of_mem_normalizer (S := graphFixedRootTorus t K σ)
      (canonicalRep_mem_normalizer_graphFixedRootTorus (σ := σ) hvw) (mul_mem hH₀ hkT)
  have hl : H₀ * L₀ * H₀⁻¹ ∈ graphFixedNegUnipotent t K σ :=
    torus_conj_mem_rootSpan_inf σ (S := {α | IsRoot t.tag α ∧ height α < 0})
      (fun α h => h.1) hH₀ hL₀
  refine ⟨H₀ * L₀ * H₀⁻¹, hl, ⟨D.w * (v : WeylGroup t.tag), hvw⟩,
    n'⁻¹ * (H₀ * k) * n' * h₁, mul_mem hHk hh₁, u₁, hu₁, ?_⟩
  have hg2 : g = n₁ * (h₀ * u₀ * canonicalRep (coxeterSystem t.tag) K (v : WeylGroup t.tag) *
      (h₁ * u₁)) := by
    rw [hbb]
    group
  have e2 : n₁ * (h₀ * u₀ * canonicalRep (coxeterSystem t.tag) K (v : WeylGroup t.tag) *
      (h₁ * u₁)) = H₀ * L₀ * (n₁ * canonicalRep (coxeterSystem t.tag) K (v : WeylGroup t.tag)) *
        (h₁ * u₁) := by
    simp only [H₀, L₀]
    group
  rw [hg2, e2, hkn]
  show _ = H₀ * L₀ * H₀⁻¹ * n' * (n'⁻¹ * (H₀ * k) * n' * h₁ * u₁)
  group

theorem Xg_conj_V (a : Fin t.foldedTag.rank) {x v : ModGL t.tag K} (hx : x ∈ Xg t K σ a)
    (hv : v ∈ graphFixedSimpleComplement t K σ a) :
    x * v * x⁻¹ ∈ graphFixedSimpleComplement t K σ a := by
  have hN := graphFixedSimpleComplement_subgroupOf_normal (K := K) (σ := σ) a
  have hxU := Xg_le a hx
  have hvU := graphFixedSimpleComplement_le a hv
  exact Subgroup.mem_subgroupOf.1
    (hN.conj_mem ⟨v, hvU⟩ (Subgroup.mem_subgroupOf.2 hv) ⟨x, hxU⟩)

theorem Yg_conj_Qg (D : LongestData t) (a : Fin t.foldedTag.rank) {y q : ModGL t.tag K}
    (hy : y ∈ Yg t K σ a) (hq : q ∈ Qg t K σ a) : y * q * y⁻¹ ∈ Qg t K σ a := by
  set n₀ := canonicalRep (coxeterSystem t.tag) K D.w
  have hx : n₀⁻¹ * y * n₀ ∈ Xg t K σ a := by
    refine (conj_mem_Yg_iff D a _).1 ?_
    have e : n₀ * (n₀⁻¹ * y * n₀) * n₀⁻¹ = y := by group
    rw [e]
    exact hy
  have hv : n₀⁻¹ * q * n₀ ∈ graphFixedSimpleComplement t K σ a := by
    refine (conj_mem_Qg_iff D a _).1 ?_
    have e : n₀ * (n₀⁻¹ * q * n₀) * n₀⁻¹ = q := by group
    rw [e]
    exact hq
  have h := Xg_conj_V a hx hv
  have h2 := (conj_mem_Qg_iff D a _).2 h
  have e : n₀ * (n₀⁻¹ * y * n₀ * (n₀⁻¹ * q * n₀) * (n₀⁻¹ * y * n₀)⁻¹) * n₀⁻¹ = y * q * y⁻¹ := by
    group
  rw [e] at h2
  exact h2

theorem Xg_conj_Qg (D : LongestData t) (a : Fin t.foldedTag.rank) {x q : ModGL t.tag K}
    (hx : x ∈ Xg t K σ a) (hq : q ∈ Qg t K σ a) : x * q * x⁻¹ ∈ Qg t K σ a := by
  set n := canonicalRep (coxeterSystem t.tag) K (t.orbitReflection a)
  have hy : n⁻¹ * x * n ∈ Yg t K σ a := by
    refine (conj_simple_mem_Xg_iff (σ := σ) a _).1 ?_
    have e : n * (n⁻¹ * x * n) * n⁻¹ = x := by group
    rw [e]
    exact hx
  have hq' : n⁻¹ * q * n ∈ Qg t K σ a := by
    refine (conj_simple_mem_Qg_iff (σ := σ) a _).1 ?_
    have e : n * (n⁻¹ * q * n) * n⁻¹ = q := by group
    rw [e]
    exact hq
  have h := Yg_conj_Qg D a hy hq'
  have h2 := (conj_simple_mem_Qg_iff (σ := σ) a _).2 h
  have e : n * (n⁻¹ * x * n * (n⁻¹ * q * n) * (n⁻¹ * x * n)⁻¹) * n⁻¹ = x * q * x⁻¹ := by
    group
  rw [e] at h2
  exact h2

theorem exists_neg_decomposition (D : LongestData t) (hσ : Function.Surjective σ)
    (a : Fin t.foldedTag.rank) {l : ModGL t.tag K} (hl : l ∈ graphFixedNegUnipotent t K σ) :
    ∃ y ∈ Yg t K σ a, ∃ q ∈ Qg t K σ a, l = y * q := by
  set n₀ := canonicalRep (coxeterSystem t.tag) K D.w
  have hg : n₀⁻¹ * l * n₀ ∈ graphFixedPosUnipotent t K σ := by
    refine (conj_mem_negUnipotent_iff D _).1 ?_
    have e : n₀ * (n₀⁻¹ * l * n₀) * n₀⁻¹ = l := by group
    rw [e]
    exact hl
  obtain ⟨c, v, hv, e⟩ := exists_orbitX_mul_eq hσ a hg
  refine ⟨n₀ * (orbitX t K σ a c : ModGL t.tag K) * n₀⁻¹,
    (conj_mem_Yg_iff D a _).2 (orbitX_mem_Xg a c), n₀ * v * n₀⁻¹,
    (conj_mem_Qg_iff D a _).2 hv, ?_⟩
  have e2 : l = n₀ * (n₀⁻¹ * l * n₀) * n₀⁻¹ := by group
  rw [e2, ← e]
  group

variable (p : ℕ) [Finite K] [CharP K p] (D : LongestData t) (hσ : Function.Surjective σ) {q : ℕ}
  (hq : ∀ a, Nat.card (orbitField t K σ a) = q ^ (t.orbit a).card)

@[expose] def twistedDatum :
    CurtisDatum ↥(graphFixedRootGroup t K σ) (relCs t) p where
  U := (graphFixedPosUnipotent t K σ).subgroupOf (graphFixedRootGroup t K σ)
  L := (graphFixedNegUnipotent t K σ).subgroupOf (graphFixedRootGroup t K σ)
  H := (graphFixedRootTorus t K σ).subgroupOf (graphFixedRootGroup t K σ)
  X a := (Xg t K σ a).subgroupOf (graphFixedRootGroup t K σ)
  Y a := (Yg t K σ a).subgroupOf (graphFixedRootGroup t K σ)
  Us a := (graphFixedSimpleComplement t K σ a).subgroupOf (graphFixedRootGroup t K σ)
  Q a := (Qg t K σ a).subgroupOf (graphFixedRootGroup t K σ)
  n a := nC t K σ a
  nW w := nWC t K σ w
  phi a := torusPart t K σ a
  psi a := torusPart t K σ a
  isPGroup_U := isPGroup_graphFixedPosUnipotent_subgroupOf p
  isPGroup_L := isPGroup_graphFixedNegUnipotent_subgroupOf p D
  U_inf_L := by
    refine eq_bot_iff.2 fun x hx => ?_
    obtain ⟨h1, h2⟩ := Subgroup.mem_inf.1 hx
    have h : (x : ModGL t.tag K) ∈
        graphFixedPosUnipotent t K σ ⊓ graphFixedNegUnipotent t K σ := Subgroup.mem_inf.2 ⟨h1, h2⟩
    rw [graphFixedPosUnipotent_inf_graphFixedNegUnipotent, Subgroup.mem_bot] at h
    exact Subgroup.mem_bot.2 (Subtype.ext h)
  H_comm a ha b hb := Subtype.ext (graphFixedRootTorus_mul_comm ha hb)
  H_normU h hh u hu := conj_mem_subgroupOf
    ((Subgroup.mem_normalizer_iff.mp
      (graphFixedRootTorus_le_normalizer_graphFixedPosUnipotent hh) u).mp hu)
  H_normU' h hh u hu := conj_inv_mem_subgroupOf
    (inv_conj_mem_of_mem_normalizer (graphFixedRootTorus_le_normalizer_graphFixedPosUnipotent hh) hu)
  H_normL h hh l hl := conj_mem_subgroupOf
    (torus_conj_mem_rootSpan_inf σ (S := {α | IsRoot t.tag α ∧ height α < 0}) (fun α h => h.1)
      hh hl)
  H_normX a h hh x hx := conj_mem_subgroupOf
    (torus_conj_mem_rootSpan_inf σ (fun α hα => (simpleOrbitRoots_pos a α hα).1) hh hx)
  H_normQ a h hh q hq := conj_mem_subgroupOf
    (torus_conj_mem_rootSpan_inf σ (fun α hα => hα.1.1) hh hq)
  X_le a x hx := Xg_le a hx
  X_ne_bot a := by
    intro h
    have hx : xC t K σ a 1 ∈ (Xg t K σ a).subgroupOf (graphFixedRootGroup t K σ) :=
      orbitX_mem_Xg a 1
    rw [h, Subgroup.mem_bot] at hx
    exact orbitX_one_ne_one (K := K) (σ := σ) a (congrArg Subtype.val hx)
  U_eq a u hu := by
    obtain ⟨c, v, hv, e⟩ := exists_orbitX_mul_eq hσ a hu
    exact ⟨xC t K σ a c, orbitX_mem_Xg a c,
      ⟨v, graphFixedPosUnipotent_le_graphFixedRootGroup t K σ (graphFixedSimpleComplement_le a hv)⟩,
      hv, Subtype.ext e.symm⟩
  Us_le a v hv := graphFixedSimpleComplement_le a hv
  X_normUs a x hx v hv := conj_mem_subgroupOf (Xg_conj_V a hx hv)
  n_normUs a v hv := conj_mem_subgroupOf
    ((Subgroup.mem_normalizer_iff.1
      (canonicalRep_orbitReflection_mem_normalizer_graphFixedSimpleComplement (σ := σ) a) v).1 hv)
  n_normUs' a v hv := conj_inv_mem_subgroupOf
    (inv_conj_mem_of_mem_normalizer
      (canonicalRep_orbitReflection_mem_normalizer_graphFixedSimpleComplement (σ := σ) a) hv)
  Y_le a y hy := Yg_le a hy
  Q_le a q hq := Qg_le a hq
  L_le a l hl := by
    obtain ⟨y, hy, q, hq, e⟩ := exists_neg_decomposition D hσ a hl
    have hl' : l = ⟨y, graphFixedNegUnipotent_le_graphFixedRootGroup t K σ (Yg_le a hy)⟩ *
        ⟨q, graphFixedNegUnipotent_le_graphFixedRootGroup t K σ (Qg_le a hq)⟩ := Subtype.ext e
    rw [hl']
    exact mul_mem (Subgroup.mem_sup_left hy) (Subgroup.mem_sup_right hq)
  X_normQ a x hx q hq := conj_mem_subgroupOf (Xg_conj_Qg D a hx hq)
  Y_normQ a y hy q hq := conj_mem_subgroupOf (Yg_conj_Qg D a hy hq)
  n_normQ a q hq := conj_mem_subgroupOf ((conj_simple_mem_Qg_iff (σ := σ) a _).2 hq)
  n_conjX a x hx := conj_mem_subgroupOf ((conj_simple_mem_Yg_iff (σ := σ) a _).2 hx)
  n_conjY a y hy := conj_mem_subgroupOf ((conj_simple_mem_Xg_iff (σ := σ) a _).2 hy)
  n_sq a := compatTorus_le_graphFixedRootTorus σ
    (canonicalRep_orbitReflection_sq_mem_compatTorus σ a)
  n_normH a h hh := conj_mem_subgroupOf
    ((Subgroup.mem_normalizer_iff.1
      (canonicalRep_mem_normalizer_graphFixedRootTorus (σ := σ) (t.orbitReflection_mem a)) _).1 hh)
  phi_mem a x hx hx1 := by
    obtain ⟨c, hc⟩ := exists_unit_of_mem_Xg hx hx1
    rw [torusPart_eq hc]
    exact hC_mem a _
  psi_mem a x hx hx1 := by
    obtain ⟨c, hc⟩ := exists_unit_of_mem_Xg hx hx1
    rw [torusPart_eq hc]
    exact hC_mem a _
  phi_spec a x hx hx1 := by
    obtain ⟨c, hc⟩ := exists_unit_of_mem_Xg hx hx1
    rw [torusPart_eq hc]
    refine ⟨yC t K σ a ((c⁻¹ : (orbitField t K σ a)ˣ) : orbitField t K σ a), yC_mem a _,
      xC t K σ a (-((c⁻¹ : (orbitField t K σ a)ˣ) : orbitField t K σ a)), xC_mem a _, ?_⟩
    have hx' : x = xC t K σ a (c : orbitField t K σ a) := Subtype.ext hc
    rw [hx']
    exact xC_mul_nC a c
  psi_spec a x hx hx1 := by
    obtain ⟨c, hc⟩ := exists_unit_of_mem_Xg hx hx1
    rw [torusPart_eq hc]
    refine ⟨xC t K σ a (-((c⁻¹ : (orbitField t K σ a)ˣ) : orbitField t K σ a)),
      orbitX_mem_Xg a _,
      xC t K σ a (-((c⁻¹ : (orbitField t K σ a)ˣ) : orbitField t K σ a)), xC_mem a _, ?_⟩
    have hx' : x = xC t K σ a (c : orbitField t K σ a) := Subtype.ext hc
    rw [hx']
    exact nC_mul_xC_mul_nC a c
  bruhatY a y hy hy1 := by
    obtain ⟨c, hc⟩ := exists_unit_of_mem_Yg hy hy1
    refine ⟨hC t K σ a (-c⁻¹), hC_mem a _,
      xC t K σ a ((c⁻¹ : (orbitField t K σ a)ˣ) : orbitField t K σ a), orbitX_mem_Xg a _,
      xC t K σ a ((c⁻¹ : (orbitField t K σ a)ˣ) : orbitField t K σ a), orbitX_mem_Xg a _, ?_⟩
    have hy' : y = yC t K σ a (c : orbitField t K σ a) := Subtype.ext hc
    rw [hy']
    exact yC_eq a c
  nW_one := Subtype.ext (canonicalRep_one _ K)
  nW_simple_mul w a h := by
    have hl := length_orbitReflection_mul_of_relCs a w h
    have hc : canonicalRep (coxeterSystem t.tag) K (t.orbitReflection a * (w : WeylGroup t.tag)) =
        canonicalRep (coxeterSystem t.tag) K (t.orbitReflection a) *
          canonicalRep (coxeterSystem t.tag) K (w : WeylGroup t.tag) :=
      canonicalRep_mul_of_length_eq (by rw [hl, length_orbitReflection, add_comm])
    refine Subtype.ext ?_
    show canonicalRep (coxeterSystem t.tag) K
        ((((relCs t).simple a * w : ↥(relWeylTwist t)) : WeylGroup t.tag)) = _
    rw [show ((((relCs t).simple a * w : ↥(relWeylTwist t)) : WeylGroup t.tag)) =
      t.orbitReflection a * (w : WeylGroup t.tag) by rw [relCs_simple]; rfl]
    exact hc
  nW_conj w a h x hx := by
    have hpos := (relCs_length_simple_mul_iff a w).1 h
    exact conj_inv_mem_subgroupOf (canonicalRep_inv_mul_mul_mem_graphFixedPosUnipotent
      (σ := σ) w.2 (S := simpleOrbitRoots t a) (fun α hα => (simpleOrbitRoots_pos a α hα).1)
      (by rintro _ ⟨i, hi, rfl⟩; exact hpos i hi) hx)
  heckeDeg_mul w a h := by
    have hl := length_orbitReflection_mul_of_relCs a w h
    have hU : graphFixedPosUnipotent t K σ ≤ graphFixedRootGroup t K σ :=
      graphFixedPosUnipotent_le_graphFixedRootGroup t K σ
    rw [heckeDeg_subgroupOf' hU, heckeDeg_subgroupOf' hU, heckeDeg_subgroupOf' hU]
    show heckeDeg _ (canonicalRep (coxeterSystem t.tag) K (t.orbitReflection a)) *
        heckeDeg _ (canonicalRep (coxeterSystem t.tag) K (w : WeylGroup t.tag)) =
      heckeDeg _ (canonicalRep (coxeterSystem t.tag) K
        ((((relCs t).simple a * w : ↥(relWeylTwist t)) : WeylGroup t.tag)))
    rw [show ((((relCs t).simple a * w : ↥(relWeylTwist t)) : WeylGroup t.tag)) =
      t.orbitReflection a * (w : WeylGroup t.tag) by rw [relCs_simple]; rfl,
      heckeDeg_graphFixedPosUnipotent hσ hq (t.orbitReflection_mem a),
      heckeDeg_graphFixedPosUnipotent hσ hq w.2,
      heckeDeg_graphFixedPosUnipotent hσ hq (mul_mem (t.orbitReflection_mem a) w.2), hl,
      length_orbitReflection, ← pow_add, add_comm]
  cover g := by
    obtain ⟨l, hl, v, h, hh, u, hu, e⟩ := cover_graphFixedRootGroup D hσ g.2
    exact ⟨⟨l, graphFixedNegUnipotent_le_graphFixedRootGroup t K σ hl⟩, hl, v,
      ⟨h, graphFixedRootTorus_le t K σ hh⟩, hh,
      ⟨u, graphFixedPosUnipotent_le_graphFixedRootGroup t K σ hu⟩, hu, Subtype.ext e⟩

end CFSG.HardMathSupport.Cooperstein.Coordinator.CurtisTw
