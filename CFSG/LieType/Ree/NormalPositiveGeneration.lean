module

public import CFSG.LieType.Ree.FixedTwoCellParabolics
public import CFSG.LieType.Ree.G2PrimeFieldWords
public import CFSG.LieType.Simplicity.Torus
public import CFSG.LieType.Chevalley.RankOneCentralImage

public noncomputable section

namespace CFSG.LieType.Ree

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open scoped Pointwise

namespace ReeTag

section Torus

variable {τ : Tag} {K : Type} [Field K] [Finite K]

theorem pow_card_of_mem_torusGroup
    {h : ModGL τ K} (hh : h ∈ torusGroup τ K) :
    h ^ Nat.card K = h := by
  have hcomm := (triangular_borel_structure.{0, 0} τ K).1
  induction hh using Subgroup.closure_induction with
  | mem x hx =>
    obtain ⟨⟨i, u⟩, rfl⟩ := hx
    have h1 : u ^ (Nat.card K - 1) = 1 := by
      rw [← Nat.card_units]
      exact pow_card_eq_one'
    have hu : u ^ Nat.card K = u := by
      calc u ^ Nat.card K = u ^ (Nat.card K - 1 + 1) := by rw [Nat.sub_add_cancel Nat.card_pos]
        _ = u := by rw [pow_succ, h1, one_mul]
    change (torusEltHom τ K i u) ^ Nat.card K = torusEltHom τ K i u
    rw [← map_pow, hu]
  | one => rw [one_pow]
  | mul x y hx hy ihx ihy => rw [Commute.mul_pow (hcomm x hx y hy), ihx, ihy]
  | inv x _ ih => rw [inv_pow, ih]

end Torus

section Inversion

variable {t : ReeTag} {K : Type} [Field K] [Finite K]

omit [Finite K] in
theorem mem_nativeData_H_of_mem_torusGroup
    [Finite K] {h : ModGL t.tag K}
    (hh : h ∈ torusGroup t.tag K) :
    (⟨h, torusGroup_le_adjointGroup t K hh⟩ : adjointGroup t.tag K) ∈ (nativeData t.tag K).H := by
  have hle : (torusGroup t.tag K).subgroupOf (adjointGroup t.tag K) ≤ (nativeData t.tag K).H := by
    rw [torusSub_eq_closure, Subgroup.closure_le]
    rintro _ ⟨⟨i, u⟩, rfl⟩
    exact torusElement_mem_H _ i u
  exact hle (Subgroup.mem_subgroupOf.2 hh)

theorem canonicalRep_longest_conj_torus
    {w₀ : WeylGroup t.tag}
    (hw₀ : ∀ w, (coxeterSystem t.tag).length w ≤ (coxeterSystem t.tag).length w₀)
    {h : ModGL t.tag K} (hh : h ∈ torusGroup t.tag K) :
    canonicalRep (coxeterSystem t.tag) K w₀ * h * (canonicalRep (coxeterSystem t.tag) K w₀)⁻¹ =
      h⁻¹ := by
  have hw : ∀ α : Root t.tag, (w₀ • α).1 = -α.1 := fun α => by
    rw [coe_smul_root]
    exact smul_longest hw₀ α.1
  exact congrArg Subtype.val
    (CFSG.LieType.Simplicity.nrep_conj_of_mem_H hw (mem_nativeData_H_of_mem_torusGroup hh))

end Inversion

section Closure

variable {t : ReeTag} {K : Type} [Field K] [Finite K] [CharP K t.prime] {a : ℕ}

variable (t K a) in
@[expose] def reeNormalPos :
    Subgroup (ModGL t.tag K) :=
  Subgroup.closure {x | ∃ g ∈ t.reeGamma K a, ∃ u ∈ t.reeFixedPosUnipotent K a, g * u * g⁻¹ = x}

theorem reeNormalPos_le :
    t.reeNormalPos K a ≤ t.reeGamma K a := by
  refine (Subgroup.closure_le _).2 ?_
  rintro _ ⟨g, hg, u, hu, rfl⟩
  exact mul_mem (mul_mem hg (reeFixedBorel_le_reeGamma (reeFixedPosUnipotent_le_reeFixedBorel hu)))
    (inv_mem hg)

theorem reeFixedPosUnipotent_le_reeNormalPos :
    t.reeFixedPosUnipotent K a ≤ t.reeNormalPos K a := fun u hu =>
  Subgroup.subset_closure ⟨1, one_mem _, u, hu, by rw [one_mul, inv_one, mul_one]⟩

theorem conj_mem_reeNormalPos
    {γ : ModGL t.tag K} (hγ : γ ∈ t.reeGamma K a)
    {x : ModGL t.tag K} (hx : x ∈ t.reeNormalPos K a) : γ * x * γ⁻¹ ∈ t.reeNormalPos K a := by
  induction hx using Subgroup.closure_induction with
  | mem x hx =>
    obtain ⟨g, hg, u, hu, rfl⟩ := hx
    exact Subgroup.subset_closure ⟨γ * g, mul_mem hγ hg, u, hu, by group⟩
  | one => rw [mul_one, mul_inv_cancel]; exact one_mem _
  | mul x y _ _ hx hy =>
    rw [show γ * (x * y) * γ⁻¹ = (γ * x * γ⁻¹) * (γ * y * γ⁻¹) by group]
    exact mul_mem hx hy
  | inv x _ hx =>
    rw [show γ * x⁻¹ * γ⁻¹ = (γ * x * γ⁻¹)⁻¹ by group]
    exact inv_mem hx

theorem reeGamma_le_normalizer_reeNormalPos :
    t.reeGamma K a ≤ Subgroup.normalizer (t.reeNormalPos K a : Set (ModGL t.tag K)) := by
  intro γ hγ
  rw [Subgroup.mem_normalizer_iff]
  intro x
  refine ⟨fun hx => conj_mem_reeNormalPos hγ hx, fun hx => ?_⟩
  have h := conj_mem_reeNormalPos (inv_mem hγ) hx
  rwa [show γ⁻¹ * (γ * x * γ⁻¹) * γ⁻¹⁻¹ = x by group] at h

theorem reeFixedTorus_le_normalizer_reeNormalPos :
    t.reeFixedTorus K a ≤ Subgroup.normalizer (t.reeNormalPos K a : Set (ModGL t.tag K)) :=
  inf_le_right.trans reeGamma_le_normalizer_reeNormalPos

theorem canonicalRep_fixedOrbitElement_mem_sup
    (j : Fin t.fixedOrbitCount) :
    canonicalRep (coxeterSystem t.tag) K (t.fixedOrbitElement j) ∈
      t.reeFixedTorus K a ⊔ t.reeNormalPos K a := by
  obtain ⟨u, hu, hu1⟩ := exists_ne_one_mem_reeFixedOrbitUnipotent (K := K) (a := a) j
  have hnΓ : canonicalRep (coxeterSystem t.tag) K (t.fixedOrbitElement j) ∈ t.reeGamma K a :=
    (canonicalRep_mem_reeFixedMonomial t K a (fixedOrbitElement_mem j)).2
  have huU := reeFixedOrbitUnipotent_le_reeFixedPosUnipotent j hu
  have huB := reeFixedPosUnipotent_le_reeFixedBorel huU
  have hyR : canonicalRep (coxeterSystem t.tag) K (t.fixedOrbitElement j) * u *
      (canonicalRep (coxeterSystem t.tag) K (t.fixedOrbitElement j))⁻¹ ∈ t.reeNormalPos K a :=
    Subgroup.subset_closure ⟨_, hnΓ, u, huU, rfl⟩
  have hyP : canonicalRep (coxeterSystem t.tag) K (t.fixedOrbitElement j) * u *
      (canonicalRep (coxeterSystem t.tag) K (t.fixedOrbitElement j))⁻¹ ∈
        ((t.reeGamma K a ⊓ parabolicSubgroup t.tag K (t.fixedOrbitSet j) :
          Subgroup (ModGL t.tag K)) : Set (ModGL t.tag K)) := by
    have hnP := canonicalRep_fixedOrbitElement_mem_reeGamma_inf (K := K) (a := a) j
    exact mul_mem (mul_mem hnP (reeFixedBorel_le_reeGamma_inf_parabolicSubgroup j huB))
      (inv_mem hnP)
  rw [coe_reeGamma_inf_parabolicSubgroup] at hyP
  have hBS : t.reeFixedBorel K a ≤ t.reeFixedTorus K a ⊔ t.reeNormalPos K a := by
    rw [reeFixedBorel_eq_sup]
    exact sup_le_sup_left reeFixedPosUnipotent_le_reeNormalPos _
  rcases hyP with hyB | hyD
  · have hU := canonicalRep_conj_mem_reeFixedNegUnipotent (fixedOrbitElement_mem j)
      (fun _ hα => height_fixedOrbitElement_smul_neg hα) hu
    have h₁ : canonicalRep (coxeterSystem t.tag) K (t.fixedOrbitElement j) * u *
        (canonicalRep (coxeterSystem t.tag) K (t.fixedOrbitElement j))⁻¹ ∈
          t.reeFixedBorel K a ⊓ t.reeFixedNegUnipotent K a := Subgroup.mem_inf.2 ⟨hyB, hU⟩
    rw [reeFixedBorel_inf_reeFixedNegUnipotent, Subgroup.mem_bot, mul_inv_eq_one,
      mul_eq_left] at h₁
    exact absurd h₁ hu1
  · obtain ⟨b, hb, b', hb', hbb⟩ := mem_reeFixedBruhatCell.1 hyD
    have e : canonicalRep (coxeterSystem t.tag) K (t.fixedOrbitElement j) =
        b⁻¹ * (canonicalRep (coxeterSystem t.tag) K (t.fixedOrbitElement j) * u *
          (canonicalRep (coxeterSystem t.tag) K (t.fixedOrbitElement j))⁻¹) * b'⁻¹ := by
      rw [← hbb]
      group
    rw [e]
    exact mul_mem (mul_mem (inv_mem (hBS hb)) (Subgroup.mem_sup_right hyR))
      (inv_mem (hBS hb'))

theorem reeGamma_le_sup
    : t.reeGamma K a ≤ t.reeFixedTorus K a ⊔ t.reeNormalPos K a := by
  rw [reeGamma_eq_sup_closure]
  refine sup_le ?_ ((Subgroup.closure_le _).2 ?_)
  · rw [reeFixedBorel_eq_sup]
    exact sup_le_sup_left reeFixedPosUnipotent_le_reeNormalPos _
  · rintro _ ⟨j, rfl⟩
    exact canonicalRep_fixedOrbitElement_mem_sup j

theorem mul_self_mem_reeNormalPos
    {w₀ : WeylGroup t.tag}
    (hw₀ : ∀ w, (coxeterSystem t.tag).length w ≤ (coxeterSystem t.tag).length w₀)
    {h : ModGL t.tag K} (hh : h ∈ t.reeFixedTorus K a) : h * h ∈ t.reeNormalPos K a := by
  have hnΓ : canonicalRep (coxeterSystem t.tag) K w₀ ∈ t.reeGamma K a :=
    (canonicalRep_mem_reeFixedMonomial t K a (longest_mem_relWeylRee hw₀)).2
  have hn : canonicalRep (coxeterSystem t.tag) K w₀ ∈
      ((t.reeFixedTorus K a ⊔ t.reeNormalPos K a : Subgroup (ModGL t.tag K)) :
        Set (ModGL t.tag K)) := reeGamma_le_sup hnΓ
  rw [Subgroup.coe_mul_of_left_le_normalizer_right _ _
    reeFixedTorus_le_normalizer_reeNormalPos] at hn
  obtain ⟨h₀, hh₀, r, hr, hn⟩ := hn
  have hinv := canonicalRep_longest_conj_torus (K := K) hw₀ (Subgroup.mem_inf.1 hh).1
  rw [← hn] at hinv
  have hc : h₀⁻¹ * h⁻¹ = h⁻¹ * h₀⁻¹ := by
    rw [← mul_inv_rev, ← mul_inv_rev, reeFixedTorus_mul_comm hh₀ hh]
  have key : (h * h)⁻¹ = h₀ * (r * (h * r⁻¹ * h⁻¹)) * h₀⁻¹ := by
    calc (h * h)⁻¹ = h⁻¹ * h⁻¹ := mul_inv_rev h h
      _ = h₀ * r * h * (h₀ * r)⁻¹ * h⁻¹ := by rw [hinv]
      _ = h₀ * r * h * r⁻¹ * (h₀⁻¹ * h⁻¹) := by group
      _ = h₀ * r * h * r⁻¹ * (h⁻¹ * h₀⁻¹) := by rw [hc]
      _ = h₀ * (r * (h * r⁻¹ * h⁻¹)) * h₀⁻¹ := by group
  have hΓh := (Subgroup.mem_inf.1 hh).2
  have hΓh₀ := (Subgroup.mem_inf.1 hh₀).2
  have hmem : (h * h)⁻¹ ∈ t.reeNormalPos K a := by
    rw [key]
    exact conj_mem_reeNormalPos hΓh₀ (mul_mem hr (conj_mem_reeNormalPos hΓh (inv_mem hr)))
  exact inv_mem_iff.1 hmem

end Closure

section G2

variable {K : Type} [Field K]

abbrev g2I0 : Fin G2.tag.rank := ⟨0, by decide⟩

abbrev g2I1 : Fin G2.tag.rank := ⟨1, by decide⟩

theorem G2_torus_eq
    {h : ModGL G2.tag K} (hh : h ∈ torusGroup G2.tag K) :
    ∃ s t : Kˣ, h = torusElt G2.tag K g2I0 s * torusElt G2.tag K g2I1 t := by
  induction hh using Subgroup.closure_induction with
  | mem x hx =>
    obtain ⟨⟨i, u⟩, rfl⟩ := hx
    fin_cases i
    · exact ⟨u, 1, by rw [torusElt_one, mul_one]⟩
    · exact ⟨1, u, by rw [torusElt_one, one_mul]⟩
  | one => exact ⟨1, 1, by rw [torusElt_one, torusElt_one, mul_one]⟩
  | mul x y _ _ hx hy =>
    obtain ⟨s, t, rfl⟩ := hx
    obtain ⟨s', t', rfl⟩ := hy
    refine ⟨s * s', t * t', ?_⟩
    rw [torusElt_mul, torusElt_mul]
    exact Commute.mul_mul_mul_comm (torusElt_mul_comm (τ := G2.tag) (R := K) g2I1 g2I0 t s') _ _
  | inv x _ hx =>
    obtain ⟨s, t, rfl⟩ := hx
    refine ⟨s⁻¹, t⁻¹, ?_⟩
    have hinv : ∀ (i : Fin G2.tag.rank) (u : Kˣ),
        (torusElt G2.tag K i u)⁻¹ = torusElt G2.tag K i u⁻¹ := fun i u =>
      (map_inv (torusEltHom G2.tag K i) u).symm
    rw [mul_inv_rev, hinv, hinv]
    exact torusElt_mul_comm (τ := G2.tag) (R := K) g2I1 g2I0 t⁻¹ s⁻¹

theorem g2Root23_isRoot
    : IsRoot G2.tag g2Root23 :=
  RootOps.isRootB_iff.1 (by decide +kernel)

theorem g2Root12_isRoot
    : IsRoot G2.tag g2Root12 :=
  RootOps.isRootB_iff.1 (by decide +kernel)

theorem G2_torusPair_apply (s t : Kˣ) :
    ((torusElt G2.tag K g2I0 s * torusElt G2.tag K g2I1 t : ModGL G2.tag K) :
        Module.End K (RootModule G2.tag K)) (rootVec G2.tag K g2Root23) =
      (s : K) • rootVec G2.tag K g2Root23 ∧
    ((torusElt G2.tag K g2I0 s * torusElt G2.tag K g2I1 t : ModGL G2.tag K) :
        Module.End K (RootModule G2.tag K)) (rootVec G2.tag K g2Root12) =
      (t : K) • rootVec G2.tag K g2Root12 := by
  have e1 : ∑ j, G2.tag.cartan g2I0 j * g2Root23 j = 1 := by decide
  have e2 : ∑ j, G2.tag.cartan g2I1 j * g2Root23 j = 0 := by decide
  have e3 : ∑ j, G2.tag.cartan g2I0 j * g2Root12 j = 0 := by decide
  have e4 : ∑ j, G2.tag.cartan g2I1 j * g2Root12 j = 1 := by decide
  constructor
  · rw [Units.val_mul, Module.End.mul_apply, torusElt_rootVec _ _ g2Root23_isRoot, map_smul,
      torusElt_rootVec _ _ g2Root23_isRoot, e1, e2, smul_smul]
    simp
  · rw [Units.val_mul, Module.End.mul_apply, torusElt_rootVec _ _ g2Root12_isRoot, map_smul,
      torusElt_rootVec _ _ g2Root12_isRoot, e3, e4, smul_smul]
    simp

theorem G2_torusPair_inj
    {s t s' t' : Kˣ}
    (h : torusElt G2.tag K g2I0 s * torusElt G2.tag K g2I1 t =
      torusElt G2.tag K g2I0 s' * torusElt G2.tag K g2I1 t') : s = s' ∧ t = t' := by
  have hv : ∀ {α : Fin G2.tag.rank → ℤ} (hα : IsRoot G2.tag α), rootVec G2.tag K α ≠ 0 :=
    fun hα => by
      rw [rootVec_eq_single_of_isRoot hα]
      exact Finsupp.single_ne_zero.2 one_ne_zero
  have h23 := congrArg (fun g : ModGL G2.tag K =>
    (g : Module.End K (RootModule G2.tag K)) (rootVec G2.tag K g2Root23)) h
  have h12 := congrArg (fun g : ModGL G2.tag K =>
    (g : Module.End K (RootModule G2.tag K)) (rootVec G2.tag K g2Root12)) h
  simp only [(G2_torusPair_apply _ _).1, (G2_torusPair_apply _ _).2] at h23 h12
  exact ⟨Units.ext (smul_left_injective K (hv g2Root23_isRoot) h23),
    Units.ext (smul_left_injective K (hv g2Root12_isRoot) h12)⟩

variable [Finite K] [CharP K G2.prime] {a : ℕ}

theorem G2_reeFixedTorus_sq_eq_one
    {g : ModGL G2.tag K} (hg : g ∈ G2.reeFixedTorus K a)
    (h2 : g * g = 1) :
    g = 1 ∨ g = torusElt G2.tag K g2I0 (-1) * torusElt G2.tag K g2I1 (-1) := by
  obtain ⟨hgH, hgΓ⟩ := Subgroup.mem_inf.1 hg
  obtain ⟨s, t, rfl⟩ := G2_torus_eq hgH
  have hsq : (torusElt G2.tag K g2I0 s * torusElt G2.tag K g2I1 t) *
      (torusElt G2.tag K g2I0 s * torusElt G2.tag K g2I1 t) =
        torusElt G2.tag K g2I0 (s * s) * torusElt G2.tag K g2I1 (t * t) := by
    rw [torusElt_mul, torusElt_mul]
    exact Commute.mul_mul_mul_comm (torusElt_mul_comm (τ := G2.tag) (R := K) g2I1 g2I0 t s) _ _
  rw [hsq, show (1 : ModGL G2.tag K) = torusElt G2.tag K g2I0 1 * torusElt G2.tag K g2I1 1 by
    rw [torusElt_one, torusElt_one, mul_one]] at h2
  obtain ⟨hs, ht⟩ := G2_torusPair_inj h2
  have hga : torusElt G2.tag K g2I0 s * torusElt G2.tag K g2I1 t ∈ adjointGroup G2.tag K :=
    mul_mem (torusElt_mem_adjointGroup _ _) (torusElt_mem_adjointGroup _ _)
  have hF := finiteReeAut_eq_of_mem_reeGamma hgΓ hga
  have e : (⟨_, hga⟩ : adjointGroup G2.tag K) =
      torusElement G2.tag K g2I0 s * torusElement G2.tag K g2I1 t := rfl
  have hp0 : G2.perm g2I0 = g2I1 := by decide
  have hp1 : G2.perm g2I1 = g2I0 := by decide
  rw [e, map_mul, finiteReeAut_eq_reeAut, reeAut_torusElement, reeAut_torusElement, hp0,
    hp1] at hF
  have hF' : torusElt G2.tag K g2I0 (t ^ G2.relationExponent a g2I1) *
      torusElt G2.tag K g2I1 (s ^ G2.relationExponent a g2I0) =
        torusElt G2.tag K g2I0 s * torusElt G2.tag K g2I1 t :=
    (torusElt_mul_comm (τ := G2.tag) (R := K) g2I0 g2I1 _ _).trans hF
  obtain ⟨-, hts⟩ := G2_torusPair_inj hF'
  have hodd : Odd (G2.relationExponent a g2I0) := by
    rw [relationExponent, ite_eq_left (by decide)]
    exact Odd.pow (by decide)
  obtain ⟨k, hk⟩ := hodd
  have hss : s ^ G2.relationExponent a g2I0 = s := by
    rw [hk, pow_succ, pow_mul, sq, hs, one_pow, one_mul]
  rw [hss] at hts
  subst hts
  have hs' : (s : K) * s = 1 := by rw [← Units.val_mul, hs, Units.val_one]
  rcases mul_self_eq_one_iff.1 hs' with h1 | h1
  · left
    rw [show s = 1 from Units.ext h1, torusElt_one, torusElt_one, mul_one]
  · right
    rw [show s = -1 from Units.ext (by rw [h1, Units.val_neg, Units.val_one])]

end G2

theorem exists_three_pow_eq : ∀ a : ℕ, ∃ k, 3 ^ (2 * a + 1) = 4 * k + 3
  | 0 => ⟨0, rfl⟩
  | n + 1 => by
    obtain ⟨k, hk⟩ := exists_three_pow_eq n
    exact ⟨9 * k + 6, by rw [show 2 * (n + 1) + 1 = 2 * n + 1 + 2 by ring, pow_add, hk]; ring⟩

theorem reeFixedTorus_le_reeNormalPos
    (t : ReeTag) (a : ℕ) (K : Type) [Field K] [Finite K]
    [CharP K t.prime] (hK : Nat.card K = t.prime ^ (2 * a + 1)) :
    t.reeFixedTorus K a ≤ t.reeNormalPos K a := by
  obtain ⟨w₀, hw₀⟩ := Finite.exists_max (coxeterSystem t.tag).length
  intro h hh
  have hsq := mul_self_mem_reeNormalPos hw₀ hh
  have hq := pow_card_of_mem_torusGroup (Subgroup.mem_inf.1 hh).1
  cases t with
  | F4 =>
    have e : h = (h * h) ^ 2 ^ (2 * a) := by
      conv_lhs => rw [← hq, hK]
      rw [← sq, ← pow_mul, ← pow_succ']
      rfl
    rw [e]
    exact pow_mem hsq _
  | G2 =>
    obtain ⟨k, hk⟩ := exists_three_pow_eq a
    have hq' : h ^ (4 * k + 3) = h := by
      rw [← hk]
      exact (congrArg (h ^ ·) hK).symm.trans hq
    have hm : h ^ (2 * k + 1) * h ^ (2 * k + 1) = 1 := by
      rw [← pow_add, show 2 * k + 1 + (2 * k + 1) = 4 * k + 2 by ring]
      refine mul_left_cancel (a := h) ?_
      rw [← pow_succ', mul_one]
      exact hq'
    have hmem : h ^ (2 * k + 1) ∈ G2.reeNormalPos K a := by
      rcases G2_reeFixedTorus_sq_eq_one (pow_mem hh _) hm with h1 | h1
      · rw [h1]
        exact one_mem _
      · obtain ⟨⟨hu0, hu1, hu2⟩, -, hd, -⟩ := ree_G2_prime_field_words K a hw₀
        have hnΓ : canonicalRep (coxeterSystem G2.tag) K w₀ ∈ G2.reeGamma K a :=
          (canonicalRep_mem_reeFixedMonomial G2 K a (longest_mem_relWeylRee hw₀)).2
        have hv : ∀ u ∈ G2.reeFixedPosUnipotent K a,
            canonicalRep (coxeterSystem G2.tag) K w₀ * u *
              (canonicalRep (coxeterSystem G2.tag) K w₀)⁻¹ ∈ G2.reeNormalPos K a :=
          fun u hu => Subgroup.subset_closure ⟨_, hnΓ, u, hu, rfl⟩
        have hu : ∀ u ∈ G2.reeFixedPosUnipotent K a, u ∈ G2.reeNormalPos K a :=
          fun u hu => reeFixedPosUnipotent_le_reeNormalPos hu
        rw [h1, hd]
        exact mul_mem (mul_mem (mul_mem (mul_mem (mul_mem (hu _ hu0) (hv _ hu0)) (hv _ hu0))
          (hv _ hu1)) (hu _ hu2)) (hv _ hu1)
    have e : h = h ^ (2 * k + 1) * ((h * h) ^ k)⁻¹ := by
      rw [← sq, ← pow_mul, eq_mul_inv_iff_mul_eq, ← pow_succ']
    rw [e]
    exact mul_mem hmem (inv_mem (pow_mem hsq _))

theorem ree_normal_positive_generation
    (t : ReeTag) (a : ℕ) (K : Type) [Field K] [Finite K]
    [CharP K t.prime] (hK : Nat.card K = t.prime ^ (2 * a + 1)) :
    Subgroup.closure {x | ∃ g ∈ t.reeGamma K a, ∃ u ∈ t.reeFixedPosUnipotent K a,
      g * u * g⁻¹ = x} = t.reeGamma K a := by
  change t.reeNormalPos K a = t.reeGamma K a
  refine le_antisymm reeNormalPos_le fun g hg => ?_
  have hle : t.reeFixedTorus K a ⊔ t.reeNormalPos K a ≤ t.reeNormalPos K a :=
    sup_le (reeFixedTorus_le_reeNormalPos t a K hK) le_rfl
  exact hle (reeGamma_le_sup hg)

end ReeTag

end CFSG.LieType.Ree
