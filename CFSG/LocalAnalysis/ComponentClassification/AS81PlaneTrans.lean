module

public import CFSG.LocalAnalysis.ComponentClassification.AS81Plane
public import CFSG.LocalAnalysis.ComponentClassification.AS81AffinePlane

public section

namespace CFSG.ComponentClassification.AS81

open Subgroup CFSG.Open CFSG.ABGLocalTools CFSG.ComponentClassification.AschbacherTightEmbedding
open CFSG.ComponentClassification.RankTwoStandard

variable {G : Type} [Group G] [Finite G]

section Frame

variable {A R : Subgroup G} {g : G} {E F : Subgroup G}

theorem inf_eq_bot_of_mem_pointsIn_frame (h11 : Step11)
    {d : L34E16Cert} (hE16 : RankTwoL3Four.HypII.l34CheckWE16 d = true)
    (hF : Frame G A A R g E F) (hL : TypeL34 (rankTwoQuot A))
    (hodd : Odd (Nat.card (center ↥A))) : ∀ Q ∈ pointsIn R E, Q ≠ R → Q ⊓ A = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hB := hF.base
  have hR := hF.sylowR
  have hNK := AS76b.normalizer_centralizer_eq hB.hyp.standard
  have hcomm : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hF.elemE.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  rintro Q ⟨hQE, x, rfl⟩ hQR
  have hxc : rightConjugate R x ≤ centralizer (R : Set G) := fun y hy =>
    mem_centralizer_iff.mpr fun z hz => hcomm z (hF.R_le_E hz) y (hQE hy)
  have hxN : x ∉ normalizer (A : Set G) := by
    intro hx
    apply hQR
    have hxK : x ∈ normalizer (centralizer (A : Set G) : Set G) := hNK ▸ hx
    have hRx : IsSylowOf 2 (rightConjugate R x) (centralizer (A : Set G)) := by
      have := AschbacherTheorem3.isSylowOf_rightConjugate hR x
      rwa [(rightConjugate_eq_self_iff _ x).mpr hxK] at this
    have hN : rightConjugate R x ≤ normalizer (R : Set G) :=
      hxc.trans (Subgroup.centralizer_le_normalizer _)
    have h2 := hR.isPGroup.to_sup_of_normal_left' hRx.isPGroup hN
    have h1 := hR.eq_of_le le_sup_left (sup_le hR.le hRx.le) h2
    have h3 := hRx.eq_of_le le_sup_right (sup_le hR.le hRx.le) h2
    rw [← h3, h1]
  exact (step13L34_of h11 hE16 G A hB hL R hR x hxN hxc).2.2 hodd

theorem mem_normalizer_of_mem_inf (hF : Frame G A A R g E F) {n : G}
    (hn : n ∈ A ⊓ normalizer ((E ⊓ A : Subgroup G) : Set G)) : n ∈ normalizer (E : Set G) := by
  have hRA : R ≤ centralizer (A : Set G) := hF.sylowR.le
  rw [eq_inf_sup_of_le_sup hRA hF.R_le_E hF.E_le]
  exact mem_normalizer_sup hn.2 (Subgroup.centralizer_le_normalizer _
    (mem_centralizer_iff.mpr fun r hr => (mem_centralizer_iff.mp (hRA hr) n hn.1).symm))

theorem mem_normalizer_of_mem_inf_conj {d : L34E16Cert}
    (hE16 : RankTwoL3Four.HypII.l34CheckWE16 d = true) (hF : Frame G A A R g E F)
    (hL : TypeL34 (rankTwoQuot A)) {n : G}
    (hn : n ∈ rightConjugate A g ⊓ normalizer ((E ⊓ rightConjugate A g : Subgroup G) : Set G)) :
    n ∈ normalizer (E : Set G) := by
  have hKg : rightConjugate (centralizer (A : Set G)) g =
      centralizer (rightConjugate A g : Set G) := AschbacherTheorem3.rightConjugate_centralizer A g
  have hRgA : rightConjugate R g ≤ centralizer (rightConjugate A g : Set G) :=
    hKg ▸ AschbacherTheorem3.rightConjugate_le_rightConjugate hF.sylowR.le g
  have hRgE : rightConjugate R g ≤ E := (hF.inf_eq ▸ le_sup_right).trans inf_le_left
  rw [eq_inf_sup_of_le_sup hRgA hRgE (le_sup_of_frame hE16 hF hL)]
  exact mem_normalizer_sup hn.2 (Subgroup.centralizer_le_normalizer _
    (mem_centralizer_iff.mpr fun r hr => (mem_centralizer_iff.mp (hRgA hr) n hn.1).symm))

theorem rightConjugate_ne_of_frame (hF : Frame G A A R g E F) : rightConjugate R g ≠ R := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hstd := hF.base.hyp.standard
  have hKte := AS76b.tightlyEmbedded_centralizer hstd
  have hNK := AS76b.normalizer_centralizer_eq hstd
  have hRA : R ≤ centralizer (A : Set G) := hF.sylowR.le
  have hR1 : R ≠ ⊥ := AS76b.isSylowOf_ne_bot_of_even hF.sylowR hKte.1
  have hgK : g ∉ normalizer (centralizer (A : Set G) : Set G) := hNK ▸ hF.not_mem
  intro h
  have hRRg := two_subgroup_inf_conjugate_eq_bot _ (R ⊓ rightConjugate R g) hKte
    (hF.sylowR.isPGroup.to_le inf_le_left) g hgK
    (inf_le_right.trans (AschbacherTheorem3.rightConjugate_le_rightConjugate hRA g))
  rw [inf_eq_left.mpr (inf_le_left.trans hRA), h, inf_idem] at hRRg
  exact hR1 hRRg

theorem exists_pointsAction_eq_pair (h11 : Step11)
    {d : L34E16Cert} (hE16 : RankTwoL3Four.HypII.l34CheckWE16 d = true)
    (hF : Frame G A A R g E F) (hL : TypeL34 (rankTwoQuot A))
    (hodd : Odd (Nat.card (center ↥A))) {p₁ p₂ q₁ q₂ : ↥(pointsIn R E)} (hp : p₁ ≠ p₂)
    (hq : q₁ ≠ q₂) :
    ∃ n : ↥(normalizer (E : Set G)), pointsAction R E n p₁ = q₁ ∧ pointsAction R E n p₂ = q₂ := by
  obtain ⟨-, -, h16, htA, htAg⟩ := step15_points h11 hE16 hF hL hodd
  have hRA : R ≤ centralizer (A : Set G) := hF.sylowR.le
  have hRgE : rightConjugate R g ≤ E := (hF.inf_eq ▸ le_sup_right).trans inf_le_left
  set pR : ↥(pointsIn R E) := ⟨R, self_mem_pointsIn hF.R_le_E⟩
  set pRg : ↥(pointsIn R E) := ⟨rightConjugate R g, hRgE, g, rfl⟩
  have hKg : rightConjugate (centralizer (A : Set G)) g =
      centralizer (rightConjugate A g : Set G) := AschbacherTheorem3.rightConjugate_centralizer A g
  have hRgA : rightConjugate R g ≤ centralizer (rightConjugate A g : Set G) :=
    hKg ▸ AschbacherTheorem3.rightConjugate_le_rightConjugate hRA g
  have hfixR : ∀ a, ∀ ha : a ∈ A ⊓ normalizer ((E ⊓ A : Subgroup G) : Set G),
      pointsAction R E ⟨a, mem_normalizer_of_mem_inf hF ha⟩ pR = pR := fun a ha => by
    apply Subtype.ext
    rw [coe_pointsAction_apply]
    exact (rightConjugate_eq_self_iff R _).mpr (Subgroup.centralizer_le_normalizer _
      (mem_centralizer_iff.mpr fun r hr =>
        (mem_centralizer_iff.mp (hRA hr) _ (A.inv_mem ha.1)).symm))
  have hpA : ∀ p : ↥(pointsIn R E), p ≠ pR → ∃ a, ∃ ha : a ∈ A ⊓ normalizer ((E ⊓ A : Subgroup G) :
      Set G), pointsAction R E ⟨a, mem_normalizer_of_mem_inf hF ha⟩ pRg = p := fun p hp => by
    obtain ⟨a, ha, hpa⟩ := htA p p.2 (fun h => hp (Subtype.ext h))
    exact ⟨a, ha, Subtype.ext (by rw [coe_pointsAction_apply]; exact hpa.symm)⟩
  have hpAg : ∀ p : ↥(pointsIn R E), p ≠ pRg → ∃ b, ∃ hb : b ∈ rightConjugate A g ⊓
      normalizer ((E ⊓ rightConjugate A g : Subgroup G) : Set G),
      pointsAction R E ⟨b, mem_normalizer_of_mem_inf_conj hE16 hF hL hb⟩ pR = p := fun p hp => by
    obtain ⟨b, hb, hpb⟩ := htAg p p.2 (fun h => hp (Subtype.ext h))
    exact ⟨b, hb, Subtype.ext (by rw [coe_pointsAction_apply]; exact hpb.symm)⟩
  have hpRpRg : pR ≠ pRg := fun h => rightConjugate_ne_of_frame hF (congrArg Subtype.val h).symm
  obtain ⟨Q₁, hQ₁, -, -, -, -, hQ₁R, -, hQ₁Rg, -, -⟩ := exists_four_points h11 hE16 hF hL hodd
  set p₃ : ↥(pointsIn R E) := ⟨Q₁, hQ₁⟩
  have hp₃R : p₃ ≠ pR := fun h => hQ₁R (congrArg Subtype.val h)
  have hp₃Rg : p₃ ≠ pRg := fun h => hQ₁Rg (congrArg Subtype.val h)
  have htoR : ∀ p : ↥(pointsIn R E), ∃ n : ↥(normalizer (E : Set G)),
      pointsAction R E n p = pR := by
    intro p
    by_cases hp1 : p = pR
    · exact ⟨1, by rw [hp1, map_one]; rfl⟩
    by_cases hp2 : p = pRg
    · obtain ⟨a, ha, hpa⟩ := hpA p₃ hp₃R
      obtain ⟨b, hb, hpb⟩ := hpAg p₃ hp₃Rg
      refine ⟨(⟨b, mem_normalizer_of_mem_inf_conj hE16 hF hL hb⟩ :
        ↥(normalizer (E : Set G)))⁻¹ * ⟨a, mem_normalizer_of_mem_inf hF ha⟩, ?_⟩
      rw [map_mul, Equiv.Perm.mul_apply, hp2, hpa, map_inv, Equiv.Perm.inv_eq_iff_eq]
      exact hpb.symm
    · obtain ⟨b, hb, hpb⟩ := hpAg p hp2
      refine ⟨(⟨b, mem_normalizer_of_mem_inf_conj hE16 hF hL hb⟩ :
        ↥(normalizer (E : Set G)))⁻¹, ?_⟩
      rw [map_inv, Equiv.Perm.inv_eq_iff_eq]
      exact hpb.symm
  have hpair : ∀ p₁ p₂ : ↥(pointsIn R E), p₁ ≠ p₂ → ∃ n : ↥(normalizer (E : Set G)),
      pointsAction R E n p₁ = pR ∧ pointsAction R E n p₂ = pRg := by
    intro p₁ p₂ hp
    obtain ⟨n₁, hn₁⟩ := htoR p₁
    have hne : pointsAction R E n₁ p₂ ≠ pR := fun h =>
      hp ((pointsAction R E n₁).injective (hn₁.trans h.symm))
    obtain ⟨a, ha, hpa⟩ := hpA _ hne
    refine ⟨(⟨a, mem_normalizer_of_mem_inf hF ha⟩ : ↥(normalizer (E : Set G)))⁻¹ * n₁, ?_, ?_⟩
    · rw [map_mul, Equiv.Perm.mul_apply, hn₁, map_inv, Equiv.Perm.inv_eq_iff_eq]
      exact (hfixR a ha).symm
    · rw [map_mul, Equiv.Perm.mul_apply, map_inv, Equiv.Perm.inv_eq_iff_eq]
      exact hpa.symm
  obtain ⟨np, hnp₁, hnp₂⟩ := hpair p₁ p₂ hp
  obtain ⟨nq, hnq₁, hnq₂⟩ := hpair q₁ q₂ hq
  refine ⟨nq⁻¹ * np, ?_, ?_⟩
  · rw [map_mul, Equiv.Perm.mul_apply, hnp₁, map_inv, Equiv.Perm.inv_eq_iff_eq]
    exact hnq₁.symm
  · rw [map_mul, Equiv.Perm.mul_apply, hnp₂, map_inv, Equiv.Perm.inv_eq_iff_eq]
    exact hnq₂.symm

theorem ncard_pointLine (h11 : Step11) {d : L34E16Cert}
    (hE16 : RankTwoL3Four.HypII.l34CheckWE16 d = true) (hF : Frame G A A R g E F)
    (hL : TypeL34 (rankTwoQuot A)) (hodd : Odd (Nat.card (center ↥A)))
    {p q : ↥(pointsIn R E)} (hpq : p ≠ q) : (pointLine R E p q).ncard = 4 := by
  have hRgE : rightConjugate R g ≤ E := (hF.inf_eq ▸ le_sup_right).trans inf_le_left
  set pR : ↥(pointsIn R E) := ⟨R, self_mem_pointsIn hF.R_le_E⟩
  set pRg : ↥(pointsIn R E) := ⟨rightConjugate R g, hRgE, g, rfl⟩
  have hpRpRg : pR ≠ pRg := fun h => rightConjugate_ne_of_frame hF (congrArg Subtype.val h).symm
  obtain ⟨n, hn₁, hn₂⟩ := exists_pointsAction_eq_pair h11 hE16 hF hL hodd hpq hpRpRg
  have himg := image_pointLine n p q
  rw [hn₁, hn₂] at himg
  have h1 : (pointLine R E p q).ncard = (pointLine R E pR pRg).ncard := by
    rw [← himg, Set.ncard_image_of_injective _ (pointsAction R E n).injective]
  rw [h1]
  have hRA1 : R ⊓ A = ⊥ := inf_eq_bot_of_odd_center hF.sylowR.le hF.sylowR.isPGroup hodd
  refine le_antisymm (ncard_pointLine_le (AS76b.tightlyEmbedded_centralizer hF.base.hyp.standard)
    hF.sylowR hF.elemE hF.R_le_E hF.E_le hRA1
    (inf_eq_bot_of_mem_pointsIn_frame h11 hE16 hF hL hodd) hF.cardE hF.cardR hpRpRg) ?_
  obtain ⟨Q₁, hQ₁, Q₂, hQ₂, hQ₁le, hQ₂le, hQ₁R, hQ₂R, hQ₁Rg, hQ₂Rg, hQ₁₂⟩ :=
    exists_four_points h11 hE16 hF hL hodd
  set p₁ : ↥(pointsIn R E) := ⟨Q₁, hQ₁⟩
  set p₂ : ↥(pointsIn R E) := ⟨Q₂, hQ₂⟩
  have hsub : ({pR, pRg, p₁, p₂} : Set ↥(pointsIn R E)) ⊆ pointLine R E pR pRg := by
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    show (x : Subgroup G) ≤ R ⊔ rightConjugate R g
    rcases hx with rfl | rfl | rfl | rfl
    · exact le_sup_left
    · exact le_sup_right
    · exact hF.inf_eq ▸ hQ₁le
    · exact hF.inf_eq ▸ hQ₂le
  have hne : ∀ {a b : ↥(pointsIn R E)}, (a : Subgroup G) ≠ b → a ≠ b := fun h e => h (e ▸ rfl)
  have hcard4 : ({pR, pRg, p₁, p₂} : Set ↥(pointsIn R E)).ncard = 4 := by
    rw [Set.ncard_insert_of_notMem, Set.ncard_insert_of_notMem, Set.ncard_pair (hne hQ₁₂)]
    · simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
      exact ⟨hne (Ne.symm hQ₁Rg), hne (Ne.symm hQ₂Rg)⟩
    · simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
      exact ⟨hpRpRg, hne (Ne.symm hQ₁R), hne (Ne.symm hQ₂R)⟩
  rw [← hcard4]
  exact Set.ncard_le_ncard hsub

theorem isAffinePlane_points (h11 : Step11) {d : L34E16Cert}
    (hE16 : RankTwoL3Four.HypII.l34CheckWE16 d = true) (hF : Frame G A A R g E F)
    (hL : TypeL34 (rankTwoQuot A)) (hodd : Odd (Nat.card (center ↥A))) :
    IsAffinePlane ↥(pointsIn R E) (linesOf (pointLine R E)) := by
  have hKte := AS76b.tightlyEmbedded_centralizer hF.base.hyp.standard
  have hcomm : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hF.elemE.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  have hne : ∀ {a b : ↥(pointsIn R E)}, a ≠ b → (a : Subgroup G) ≠ b := fun h e =>
    h (Subtype.ext e)
  refine isAffinePlane_of_line (fun p q _ =>
    ⟨(le_sup_left : (p : Subgroup G) ≤ _ ⊔ (q : Subgroup G)),
      (le_sup_right : (q : Subgroup G) ≤ (p : Subgroup G) ⊔ _)⟩) ?_
    (fun p q hpq => ncard_pointLine h11 hE16 hF hL hodd hpq) ?_
  ·
    intro p q r s hpq hrs hr hs
    have hle : (r : Subgroup G) ⊔ s ≤ (p : Subgroup G) ⊔ q := sup_le hr hs
    have heq : (r : Subgroup G) ⊔ s = (p : Subgroup G) ⊔ q := by
      refine Subgroup.eq_of_le_of_card_ge hle ?_
      rw [card_sup_of_mem_pointsIn hKte hF.sylowR hcomm p.2 q.2 (hne hpq),
        card_sup_of_mem_pointsIn hKte hF.sylowR hcomm r.2 s.2 (hne hrs)]
    ext x
    simp only [pointLine, Set.mem_ofPred_eq]
    rw [heq]
  · obtain ⟨-, -, h16, -, -⟩ := step15_points h11 hE16 hF hL hodd
    exact h16

theorem exists_translations (h11 : Step11) {d : L34E16Cert}
    (hE16 : RankTwoL3Four.HypII.l34CheckWE16 d = true) (hOW : OstromWagnerAG24)
    (hF : Frame G A A R g E F) (hL : TypeL34 (rankTwoQuot A))
    (hodd : Odd (Nat.card (center ↥A))) :
    ∃ T : Subgroup (Equiv.Perm ↥(pointsIn R E)), T ≤ (pointsAction R E).range ∧
      (pointsAction R E).range ≤ normalizer (T : Set (Equiv.Perm ↥(pointsIn R E))) ∧
      IsElemAbelian 2 T ∧ Nat.card T = 16 ∧ ∀ p q : ↥(pointsIn R E), ∃ t ∈ T, t p = q := by
  obtain ⟨-, -, h16, -, -⟩ := step15_points h11 hE16 hF hL hodd
  refine hOW ↥(pointsIn R E) (linesOf (pointLine R E))
    (isAffinePlane_points h11 hE16 hF hL hodd) h16 (pointsAction R E).range ?_ ?_
  · rintro _ ⟨n, rfl⟩ ℓ ⟨p, q, hpq, rfl⟩
    refine ⟨pointsAction R E n p, pointsAction R E n q,
      fun h => hpq ((pointsAction R E n).injective h), ?_⟩
    exact image_pointLine n p q
  · intro p₁ p₂ q₁ q₂ hp hq
    obtain ⟨n, hn₁, hn₂⟩ := exists_pointsAction_eq_pair h11 hE16 hF hL hodd hp hq
    exact ⟨pointsAction R E n, ⟨n, rfl⟩, hn₁, hn₂⟩

end Frame

end CFSG.ComponentClassification.AS81
