module

public import CFSG.LieType.Ree.FixedTwoCellParabolics

public noncomputable section

namespace CFSG.LieType.Ree

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open scoped Pointwise

namespace ReeTag

variable {t : ReeTag} {K : Type} [Field K] [Finite K] [CharP K t.prime] {a : ℕ}

omit [Finite K] [CharP K t.prime] in
theorem list_prod_map_fixedOrbitElement_mem
    (ω : List (Fin t.fixedOrbitCount)) :
    (ω.map t.fixedOrbitElement).prod ∈ t.relWeylRee :=
  Subgroup.list_prod_mem _ fun x hx => by
    obtain ⟨j, -, rfl⟩ := List.mem_map.1 hx
    exact fixedOrbitElement_mem j

theorem exists_canonicalRep_inv_mul_eq
    {x y : WeylGroup t.tag} (hx : x ∈ t.relWeylRee)
    (hy : y ∈ t.relWeylRee) :
    ∃ h ∈ t.reeFixedTorus K a, (canonicalRep (coxeterSystem t.tag) K x)⁻¹ *
      canonicalRep (coxeterSystem t.tag) K y =
        canonicalRep (coxeterSystem t.tag) K (x⁻¹ * y) * h := by
  have hxy : x⁻¹ * y ∈ t.relWeylRee := mul_mem (inv_mem hx) hy
  let m : t.reeFixedMonomial K a :=
    (⟨_, canonicalRep_mem_reeFixedMonomial t K a hxy⟩ : t.reeFixedMonomial K a)⁻¹ *
      ((⟨_, canonicalRep_mem_reeFixedMonomial t K a hx⟩ : t.reeFixedMonomial K a)⁻¹ *
        ⟨_, canonicalRep_mem_reeFixedMonomial t K a hy⟩)
  have hm : m ∈ (t.reeFixedWeylHom K a).ker := by
    rw [MonoidHom.mem_ker]
    simp only [m, map_mul, map_inv, reeFixedWeylHom_canonicalRep t K a hx,
      reeFixedWeylHom_canonicalRep t K a hy, reeFixedWeylHom_canonicalRep t K a hxy]
    group
  rw [reeFixedWeylHom_ker] at hm
  refine ⟨(m : ModGL t.tag K), Subgroup.mem_subgroupOf.1 hm, ?_⟩
  simp only [m, Subgroup.coe_mul, Subgroup.coe_inv]
  group

theorem canonicalRep_fixedOrbitElement_mem_of_neg
    {A : Subgroup (ModGL t.tag K)}
    (hBA : t.reeFixedBorel K a ≤ A) {w : WeylGroup t.tag} (hw : w ∈ t.relWeylRee)
    (hwA : (t.reeFixedBorel K a).map
      (MulAut.conj (canonicalRep (coxeterSystem t.tag) K w)).toMonoidHom ≤ A)
    {j : Fin t.fixedOrbitCount} (hneg : ∀ α ∈ t.fixedOrbitRoots j, height (w⁻¹ • α) < 0) :
    canonicalRep (coxeterSystem t.tag) K (t.fixedOrbitElement j) ∈ A := by
  obtain ⟨u, hu, hu1⟩ := exists_ne_one_mem_reeFixedOrbitUnipotent (K := K) (a := a) j
  have hnΓ : canonicalRep (coxeterSystem t.tag) K (t.fixedOrbitElement j) ∈ t.reeGamma K a :=
    (canonicalRep_mem_reeFixedMonomial t K a (fixedOrbitElement_mem j)).2
  have hnwΓ : canonicalRep (coxeterSystem t.tag) K w ∈ t.reeGamma K a :=
    (canonicalRep_mem_reeFixedMonomial t K a hw).2
  have huB : u ∈ t.reeFixedBorel K a :=
    reeFixedPosUnipotent_le_reeFixedBorel (reeFixedOrbitUnipotent_le_reeFixedPosUnipotent j hu)
  have hyΓ : canonicalRep (coxeterSystem t.tag) K (t.fixedOrbitElement j) * u *
      (canonicalRep (coxeterSystem t.tag) K (t.fixedOrbitElement j))⁻¹ ∈ t.reeGamma K a :=
    mul_mem (mul_mem hnΓ (Subgroup.mem_inf.1 hu).2) (inv_mem hnΓ)
  have hyS : canonicalRep (coxeterSystem t.tag) K (t.fixedOrbitElement j) * u *
      (canonicalRep (coxeterSystem t.tag) K (t.fixedOrbitElement j))⁻¹ ∈
        rootSpan t.tag K (Neg.neg '' t.fixedOrbitRoots j) := by
    have hmap := (canonical_weyl_root_transport t.tag K).1 (t.fixedOrbitElement j)
      (t.fixedOrbitRoots j) fun α hα => (mem_fixedOrbitRoots_iff.1 hα).1
    rw [image_fixedOrbitRoots] at hmap
    rw [← hmap]
    exact ⟨u, (Subgroup.mem_inf.1 hu).1, rfl⟩
  have hyA : canonicalRep (coxeterSystem t.tag) K (t.fixedOrbitElement j) * u *
      (canonicalRep (coxeterSystem t.tag) K (t.fixedOrbitElement j))⁻¹ ∈ A := by
    apply hwA
    have hS : ∀ α ∈ (fun α => -(w⁻¹ • α)) '' t.fixedOrbitRoots j, IsRoot t.tag α := by
      rintro _ ⟨β, hβ, rfl⟩
      exact IsRoot.neg (IsRoot.smul (mem_fixedOrbitRoots_iff.1 hβ).1 w⁻¹)
    have hwS : (fun α => w • α) '' ((fun α => -(w⁻¹ • α)) '' t.fixedOrbitRoots j) =
        Neg.neg '' t.fixedOrbitRoots j := by
      rw [Set.image_image]
      exact Set.image_congr fun x _ => by rw [smul_neg, smul_inv_smul]
    have hmap := (canonical_weyl_root_transport t.tag K).1 w _ hS
    rw [hwS] at hmap
    rw [← hmap] at hyS
    obtain ⟨x, hxS, hx⟩ := hyS
    have hx' : canonicalRep (coxeterSystem t.tag) K w * x *
        (canonicalRep (coxeterSystem t.tag) K w)⁻¹ =
          canonicalRep (coxeterSystem t.tag) K (t.fixedOrbitElement j) * u *
            (canonicalRep (coxeterSystem t.tag) K (t.fixedOrbitElement j))⁻¹ := hx
    have hxΓ : x ∈ t.reeGamma K a := by
      have e : x = (canonicalRep (coxeterSystem t.tag) K w)⁻¹ *
          (canonicalRep (coxeterSystem t.tag) K (t.fixedOrbitElement j) * u *
            (canonicalRep (coxeterSystem t.tag) K (t.fixedOrbitElement j))⁻¹) *
          canonicalRep (coxeterSystem t.tag) K w := by
        rw [← hx']
        group
      rw [e]
      exact mul_mem (mul_mem (inv_mem hnwΓ) hyΓ) hnwΓ
    have hxU : x ∈ posUnipotent t.tag K := by
      refine rootSpan_le_posUnipotent (fun α hα => ⟨hS α hα, ?_⟩) hxS
      obtain ⟨β, hβ, rfl⟩ := hα
      rw [height_neg]
      have := hneg β hβ
      omega
    exact ⟨x, reeFixedPosUnipotent_le_reeFixedBorel (Subgroup.mem_inf.2 ⟨hxU, hxΓ⟩), hx⟩
  have hyP : canonicalRep (coxeterSystem t.tag) K (t.fixedOrbitElement j) * u *
      (canonicalRep (coxeterSystem t.tag) K (t.fixedOrbitElement j))⁻¹ ∈
        ((t.reeGamma K a ⊓ parabolicSubgroup t.tag K (t.fixedOrbitSet j) :
          Subgroup (ModGL t.tag K)) : Set (ModGL t.tag K)) := by
    have hnP := canonicalRep_fixedOrbitElement_mem_reeGamma_inf (K := K) (a := a) j
    exact mul_mem (mul_mem hnP (reeFixedBorel_le_reeGamma_inf_parabolicSubgroup j huB))
      (inv_mem hnP)
  rw [coe_reeGamma_inf_parabolicSubgroup] at hyP
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
    exact mul_mem (mul_mem (inv_mem (hBA hb)) hyA) (inv_mem (hBA hb'))

theorem canonicalRep_mem_of_reduced
    {A : Subgroup (ModGL t.tag K)}
    (hBA : t.reeFixedBorel K a ≤ A) :
    ∀ (ω : List (Fin t.fixedOrbitCount)) {w : WeylGroup t.tag},
      (ω.map t.fixedOrbitElement).prod = w → ω.length = t.fixedRelLength w →
      (t.reeFixedBorel K a).map
          (MulAut.conj (canonicalRep (coxeterSystem t.tag) K w)).toMonoidHom ≤ A →
      ∀ j ∈ ω, canonicalRep (coxeterSystem t.tag) K (t.fixedOrbitElement j) ∈ A
  | [], _, _, _, _, j, hj => absurd hj List.not_mem_nil
  | i :: ω, w, hω, hred, hwA, j, hj => by
    have hw : w ∈ t.relWeylRee := hω ▸ list_prod_map_fixedOrbitElement_mem (i :: ω)
    have hwv : w = t.fixedOrbitElement i * (ω.map t.fixedOrbitElement).prod := by
      rw [← hω, List.map_cons, List.prod_cons]
    have hzw : t.fixedOrbitElement i * w = (ω.map t.fixedOrbitElement).prod := by
      rw [hwv, ← mul_assoc, fixedOrbitElement_mul_self, one_mul]
    rw [List.length_cons] at hred
    have hneg : ∀ α ∈ t.fixedOrbitRoots i, height (w⁻¹ • α) < 0 := by
      rcases fixedOrbitRoots_sign (inv_mem hw) i with h | h
      · have h1 := (lengths_fixedOrbitElement_mul_of_pos hw h).1
        rw [hzw] at h1
        have h2 := fixedRelLength_le (t := t) (ω := ω) rfl
        omega
      · exact h
    have hi := canonicalRep_fixedOrbitElement_mem_of_neg hBA hw hwA hneg
    have hvred : ω.length = t.fixedRelLength (ω.map t.fixedOrbitElement).prod := by
      have h1 := (lengths_fixedOrbitElement_mul_of_neg hw hneg).1
      rw [hzw] at h1
      omega
    have hvA : (t.reeFixedBorel K a).map (MulAut.conj (canonicalRep (coxeterSystem t.tag) K
        (ω.map t.fixedOrbitElement).prod)).toMonoidHom ≤ A := by
      obtain ⟨h, hh, hm⟩ := exists_canonicalRep_inv_mul_eq (K := K) (a := a)
        (fixedOrbitElement_mem i) hw
      rw [fixedOrbitElement_inv, hzw] at hm
      have hv : canonicalRep (coxeterSystem t.tag) K (ω.map t.fixedOrbitElement).prod =
          (canonicalRep (coxeterSystem t.tag) K (t.fixedOrbitElement i))⁻¹ *
            canonicalRep (coxeterSystem t.tag) K w * h⁻¹ :=
        eq_mul_inv_of_mul_eq hm.symm
      rintro _ ⟨b, hb, rfl⟩
      have hhB := reeFixedTorus_le_reeFixedBorel hh
      have hb' : h⁻¹ * b * h ∈ t.reeFixedBorel K a := mul_mem (mul_mem (inv_mem hhB) hb) hhB
      have hc : canonicalRep (coxeterSystem t.tag) K w * (h⁻¹ * b * h) *
          (canonicalRep (coxeterSystem t.tag) K w)⁻¹ ∈ A := hwA ⟨_, hb', rfl⟩
      have e : (MulAut.conj (canonicalRep (coxeterSystem t.tag) K
          (ω.map t.fixedOrbitElement).prod)).toMonoidHom b =
            (canonicalRep (coxeterSystem t.tag) K (t.fixedOrbitElement i))⁻¹ *
              (canonicalRep (coxeterSystem t.tag) K w * (h⁻¹ * b * h) *
                (canonicalRep (coxeterSystem t.tag) K w)⁻¹) *
              canonicalRep (coxeterSystem t.tag) K (t.fixedOrbitElement i) := by
        change canonicalRep (coxeterSystem t.tag) K (ω.map t.fixedOrbitElement).prod * b *
            (canonicalRep (coxeterSystem t.tag) K (ω.map t.fixedOrbitElement).prod)⁻¹ = _
        rw [hv]
        group
      rw [e]
      exact mul_mem (mul_mem (inv_mem hi) hc) hi
    rcases List.mem_cons.1 hj with rfl | hj
    · exact hi
    · exact canonicalRep_mem_of_reduced hBA ω rfl hvred hvA j hj

theorem ree_reduced_word_Borel_extraction
    (t : ReeTag) (a : ℕ) (K : Type) [Field K] [Finite K]
    [CharP K t.prime] (A : Subgroup (ModGL t.tag K)) (hBA : t.reeFixedBorel K a ≤ A)
    {w : WeylGroup t.tag}
    (hwA : (t.reeFixedBorel K a).map
      (MulAut.conj (canonicalRep (coxeterSystem t.tag) K w)).toMonoidHom ≤ A)
    (ω : List (Fin t.fixedOrbitCount)) (hω : (ω.map t.fixedOrbitElement).prod = w)
    (hred : ω.length = t.fixedRelLength w) :
    ∀ j ∈ ω, canonicalRep (coxeterSystem t.tag) K (t.fixedOrbitElement j) ∈ A :=
  canonicalRep_mem_of_reduced hBA ω hω hred hwA

end ReeTag

end CFSG.LieType.Ree
