module

public import CFSG.LocalAnalysis.ComponentClassification.AS81Sec2Planes

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.ComponentClassification.AS81

open Subgroup CFSG.Open CFSG.ABGLocalTools CFSG.ComponentClassification.AschbacherTightEmbedding
open CFSG.ComponentClassification.RankTwoStandard
open scoped Pointwise

variable {G : Type} [Group G] [Finite G]

namespace Sec2

@[expose] def conjSetStab (Ps : Set (Subgroup G)) : Subgroup G where
  carrier := {n | ∀ V, V ∈ Ps ↔ rightConjugate V n ∈ Ps}
  mul_mem' {a b} ha hb V := by
    rw [ha V, hb (rightConjugate V a), rightConjugate_mul]
  one_mem' V := by rw [rightConjugate_one]
  inv_mem' {a} ha V := by
    rw [ha (rightConjugate V a⁻¹), rightConjugate_mul, inv_mul_cancel, rightConjugate_one]

omit [Finite G] in
theorem mem_conjSetStab {Ps : Set (Subgroup G)} {n : G} :
    n ∈ conjSetStab Ps ↔ ∀ V, V ∈ Ps ↔ rightConjugate V n ∈ Ps :=
  Iff.rfl

omit [Finite G] in
theorem le_conjSetStab {Ps : Set (Subgroup G)} {X : Subgroup G}
    (h : ∀ n ∈ X, ∀ V ∈ Ps, rightConjugate V n ∈ Ps) : X ≤ conjSetStab Ps := fun n hn V =>
  ⟨h n hn V, fun hV => by
    have := h n⁻¹ (X.inv_mem hn) _ hV
    rwa [rightConjugate_mul, mul_inv_cancel, rightConjugate_one] at this⟩

omit [Finite G] in
theorem conjSet_subset_of_le_conjSetStab {Ps : Set (Subgroup G)} {X V : Subgroup G}
    (hX : X ≤ conjSetStab Ps) (hV : V ∈ Ps) : conjSet V X ⊆ Ps := by
  rintro W ⟨n, hn, rfl⟩
  exact (hX hn V).mp hV

omit [Finite G] in
theorem card_conjSet_eq_relIndex (V X : Subgroup G) :
    Nat.card (conjSet V X) = (normalizer (V : Set G)).relIndex X := by
  let _ : MulAction G (Subgroup G) := MulAction.compHom (Subgroup G) (MulAut.conj : G →* MulAut G)
  let _ : MulAction ↥X (Subgroup G) := MulAction.compHom (Subgroup G) X.subtype
  have hsmul : ∀ p : ↥X, p • V = rightConjugate V (p : G)⁻¹ := fun p => by
    rw [rightConjugate, inv_inv]
    rfl
  have horbit : MulAction.orbit ↥X V = conjSet V X := by
    ext W
    rw [MulAction.mem_orbit_iff]
    constructor
    · rintro ⟨p, rfl⟩
      exact ⟨(p : G)⁻¹, X.inv_mem p.2, hsmul p⟩
    · rintro ⟨q, hq, rfl⟩
      refine ⟨⟨q⁻¹, X.inv_mem hq⟩, ?_⟩
      rw [hsmul]
      simp
  have hstab : MulAction.stabilizer ↥X V = (normalizer (V : Set G)).subgroupOf X := by
    ext p
    rw [MulAction.mem_stabilizer_iff, mem_subgroupOf, hsmul, rightConjugate_eq_self_iff]
    exact ⟨fun h => by simpa using inv_mem h, inv_mem⟩
  rw [← horbit, Nat.card_congr (MulAction.orbitEquivQuotientStabilizer ↥X V),
    ← (MulAction.stabilizer ↥X V).index_eq_card, hstab]
  rfl

omit [Finite G] in
theorem conjSet_eq_of_mem_conjSet {V W X : Subgroup G} (hV : V ∈ conjSet W X) :
    conjSet V X = conjSet W X := by
  obtain ⟨q, hq, rfl⟩ := hV
  ext U
  constructor
  · rintro ⟨p, hp, rfl⟩
    exact ⟨q * p, mul_mem hq hp, rightConjugate_mul W q p⟩
  · rintro ⟨p, hp, rfl⟩
    refine ⟨q⁻¹ * p, mul_mem (inv_mem hq) hp, ?_⟩
    rw [rightConjugate_mul, ← mul_assoc, mul_inv_cancel, one_mul]

end Sec2

@[expose] def sec2Fam (A E F : Subgroup G) (x : G) : Set (Subgroup G) :=
  insert (sec2F0 A E x) (conjSet F (sec2P E))

section Frame

variable {A R : Subgroup G} {g : G} {E F : Subgroup G}

variable (h11 : Step11)
  {d : L34E16Cert} (hE16 : RankTwoL3Four.HypII.l34CheckWE16 d = true)
  (hF : Frame G A A R g E F) (hL : TypeL34 (rankTwoQuot A)) (hodd : Odd (Nat.card (center ↥A)))

include h11 hE16 hF hL hodd

theorem F_inf_sec2P_inf_le {x : G} (hx : x ∈ sec2P F) (hxS : x ∉ sec2S A R E F) :
    F ⊓ (sec2P E ⊓ sec2S A R E F) ≤ E := by
  rcases le_or_le_of_isElemAbelian h11 hE16 hF hL hodd hx hxS inf_le_right
    (AS76b.IsElemAbelian.mono hF.elemF inf_le_left) with h | h
  · exact h
  · exfalso
    have hEF : E ⊓ F ≤ E ⊓ F ⊓ A := fun y hy => by
      have h1 : y ∈ sec2F0 A E x ⊓ E :=
        ⟨h ⟨hy.2, le_sec2P_inf_sec2S h11 hE16 hF hL hodd hx hxS hy.1⟩, hy.1⟩
      rw [sec2F0_inf_eq h11 hE16 hF hL hodd hx hxS] at h1
      exact ⟨hy, h1.2⟩
    have h1 := card_le_of_le hEF
    rw [hF.card_inf, ← hF.sec2Z_eq, hF.card_sec2Z hodd] at h1
    omega

theorem sec2F0_le_sec2P_inf_sec2S {x : G} (hx : x ∈ sec2P F) (hxS : x ∉ sec2S A R E F) :
    sec2F0 A E x ≤ sec2P E ⊓ sec2S A R E F := by
  rw [sec2P_inf_sec2S_eq h11 hE16 hF hL hodd hx hxS]
  exact le_sup_right

theorem sec2F0_inf_F_eq {x : G} (hx : x ∈ sec2P F) (hxS : x ∉ sec2S A R E F) :
    sec2F0 A E x ⊓ F = sec2Z A E F := by
  have hF0PS := sec2F0_le_sec2P_inf_sec2S h11 hE16 hF hL hodd hx hxS
  refine le_antisymm (fun f hf => ?_) (le_inf ?_ ?_)
  · have hfE := F_inf_sec2P_inf_le h11 hE16 hF hL hodd hx hxS ⟨hf.2, hF0PS hf.1⟩
    have h1 : f ∈ sec2F0 A E x ⊓ E := ⟨hf.1, hfE⟩
    rw [sec2F0_inf_eq h11 hE16 hF hL hodd hx hxS] at h1
    rw [hF.sec2Z_eq]
    exact ⟨⟨hfE, hf.2⟩, h1.2⟩
  · rw [← inf_inf_rightConjugate_inf_eq h11 hE16 hF hL hodd hx hxS]
    exact inf_le_left.trans le_sup_left
  · rw [hF.sec2Z_eq]
    exact inf_le_left.trans inf_le_right

theorem card_inf_E_of_mem_sec2Fam {x : G} (hx : x ∈ sec2P F) (hxS : x ∉ sec2S A R E F)
    {V : Subgroup G} (hV : V ∈ sec2Fam A E F x) : Nat.card (V ⊓ E : Subgroup G) = 16 := by
  rcases hV with rfl | ⟨p, hp, rfl⟩
  · rw [sec2F0_inf_eq h11 hE16 hF hL hodd hx hxS, card_inf_left hF hodd]
  · have hpE := (rightConjugate_eq_self_iff E p).mpr (Sec2.sec2P_le E hp)
    rw [← congrArg (rightConjugate F p ⊓ ·) hpE, ← AschbacherTheorem3.rightConjugate_inf,
      rightConjugate_card, inf_comm, hF.card_inf]

theorem eq_or_inf_E_eq_of_mem_sec2Fam {h : G} (hh : h ∈ sec2P E)
    (hhS : h ∉ sec2S A R E F) {V : Subgroup G} (hV : V ∈ sec2Fam A F E h) :
    V = E ∨ V ⊓ E = sec2Z A E F := by
  have hSc := sec2S_comm h11 hE16 hF hL hodd
  rcases hV with rfl | ⟨y, hy, rfl⟩
  · right
    rw [sec2F0_inf_F_eq h11 hE16 hF.symm hL hodd hh (hSc ▸ hhS), sec2Z_comm]
  · by_cases hyS : y ∈ sec2S A R E F
    · left
      exact (rightConjugate_eq_self_iff E y).mpr (sec2S_le_normalizer_left hF hL hodd hyS)
    · right
      exact (rightConjugate_inf_eq_and_sec2S_eq h11 hE16 hF hL hodd hy hyS).1

theorem not_mem_sec2Fam_of_mem_sec2Fam {x : G} (hx : x ∈ sec2P F) (hxS : x ∉ sec2S A R E F)
    {h : G} (hh : h ∈ sec2P E) (hhS : h ∉ sec2S A R E F) {V : Subgroup G}
    (hV : V ∈ sec2Fam A E F x) : V ∉ sec2Fam A F E h := fun hV' => by
  have h16 := card_inf_E_of_mem_sec2Fam h11 hE16 hF hL hodd hx hxS hV
  rcases eq_or_inf_E_eq_of_mem_sec2Fam h11 hE16 hF hL hodd hh hhS hV' with rfl | h1
  · rw [inf_idem, hF.cardE] at h16
    omega
  · rw [h1, hF.card_sec2Z hodd] at h16
    omega

theorem sec2Fam_subset_planes {x : G} (hx : x ∈ sec2P F) (hxS : x ∉ sec2S A R E F)
    (h4 : 4 ^ 4 ≤ Nat.card (conjClosure (E ⊓ A) (sec2P F))) :
    sec2Fam A E F x ⊆ {V | V ∈ planes E F ∧ V ≤ sec2S A R E F} := by
  rintro V (rfl | ⟨p, hp, rfl⟩)
  · exact ⟨sec2F0_mem_planes h11 hE16 hF hL hodd hx hxS h4,
      (sec2F0_le_sec2P_inf_sec2S h11 hE16 hF hL hodd hx hxS).trans inf_le_right⟩
  · refine ⟨⟨p, Or.inr rfl⟩, ?_⟩
    rw [← (rightConjugate_eq_self_iff _ p).mpr (sec2P_le_normalizer_sec2S h11 hE16 hF hL hodd hp)]
    exact AschbacherTheorem3.rightConjugate_le_rightConjugate le_sup_left p

theorem planes_sec2S_eq_union {x : G} (hx : x ∈ sec2P F) (hxS : x ∉ sec2S A R E F) {h : G}
    (hh : h ∈ sec2P E) (hhS : h ∉ sec2S A R E F)
    (h4 : 4 ^ 4 ≤ Nat.card (conjClosure (E ⊓ A) (sec2P F)))
    (h4' : 4 ^ 4 ≤ Nat.card (conjClosure (F ⊓ A) (sec2P E))) :
    {V | V ∈ planes E F ∧ V ≤ sec2S A R E F} = sec2Fam A E F x ∪ sec2Fam A F E h := by
  have hSc := sec2S_comm h11 hE16 hF hL hodd
  refine Set.Subset.antisymm (fun V ⟨hV, hVS⟩ => ?_) (Set.union_subset
    (sec2Fam_subset_planes h11 hE16 hF hL hodd hx hxS h4) fun V hV => ?_)
  · rcases mem_planes_sec2S_cases h11 hE16 hF hL hodd hV hVS hx hxS hh hhS with
      (rfl | rfl | ⟨p, hp, rfl⟩) | (rfl | rfl | ⟨y, hy, rfl⟩)
    · exact Or.inr (Or.inr ⟨1, one_mem _, (rightConjugate_one V).symm⟩)
    · exact Or.inl (Set.mem_insert _ _)
    · exact Or.inl (Or.inr ⟨p, hp, rfl⟩)
    · exact Or.inl (Or.inr ⟨1, one_mem _, (rightConjugate_one V).symm⟩)
    · exact Or.inr (Set.mem_insert _ _)
    · exact Or.inr (Or.inr ⟨y, hy, rfl⟩)
  · obtain ⟨hV', hVS'⟩ :=
      sec2Fam_subset_planes h11 hE16 hF.symm hL hodd hh (hSc ▸ hhS) h4' hV
    rw [planes_comm] at hV'
    exact ⟨hV', hSc ▸ hVS'⟩

theorem sec2P_le_conjSetStab_sec2Fam {x : G} (hx : x ∈ sec2P F) (hxS : x ∉ sec2S A R E F) :
    sec2P E ≤ Sec2.conjSetStab (sec2Fam A E F x) := by
  refine Sec2.le_conjSetStab fun p hp V hV => ?_
  rcases hV with rfl | ⟨q, hq, rfl⟩
  · rw [(rightConjugate_eq_self_iff _ p).mpr
      (sec2P_le_normalizer_sec2F0 h11 hE16 hF hL hodd hx hxS hp)]
    exact Set.mem_insert _ _
  · exact Or.inr ⟨q * p, mul_mem hq hp, rightConjugate_mul F q p⟩

theorem sec2H_le_conjSetStab_planes :
    sec2H E F ≤ Sec2.conjSetStab {V | V ∈ planes E F ∧ V ≤ sec2S A R E F} := by
  have hHS : sec2H E F ≤ normalizer (sec2S A R E F : Set G) :=
    sup_le (sec2P_le_normalizer_sec2S h11 hE16 hF hL hodd)
      (sec2P_F_le_normalizer_sec2S h11 hE16 hF hL hodd)
  refine Sec2.le_conjSetStab fun n hn V ⟨hV, hVS⟩ => ⟨rightConjugate_mem_planes hV n, ?_⟩
  rw [← (rightConjugate_eq_self_iff _ n).mpr (hHS hn)]
  exact AschbacherTheorem3.rightConjugate_le_rightConjugate hVS n

theorem sec2P_le_conjSetStab_sec2Fam_symm {x : G} (hx : x ∈ sec2P F)
    (hxS : x ∉ sec2S A R E F) {h : G} (hh : h ∈ sec2P E) (hhS : h ∉ sec2S A R E F)
    (h4 : 4 ^ 4 ≤ Nat.card (conjClosure (E ⊓ A) (sec2P F)))
    (h4' : 4 ^ 4 ≤ Nat.card (conjClosure (F ⊓ A) (sec2P E))) :
    sec2P E ≤ Sec2.conjSetStab (sec2Fam A F E h) := by
  have hU := planes_sec2S_eq_union h11 hE16 hF hL hodd hx hxS hh hhS h4 h4'
  have hPl := sec2H_le_conjSetStab_planes h11 hE16 hF hL hodd (A := A) (R := R) (g := g)
  have hPF := sec2P_le_conjSetStab_sec2Fam h11 hE16 hF hL hodd hx hxS
  refine Sec2.le_conjSetStab fun p hp V hV => ?_
  have hVpl : V ∈ {V | V ∈ planes E F ∧ V ≤ sec2S A R E F} := hU ▸ Or.inr hV
  have h1 := (hPl (mem_sup_left hp) V).mp hVpl
  rw [hU] at h1
  rcases h1 with h1 | h1
  · exfalso
    have h2 := (hPF hp V).mpr h1
    exact not_mem_sec2Fam_of_mem_sec2Fam h11 hE16 hF hL hodd hx hxS hh hhS h2 hV
  · exact h1

theorem sec2H_le_conjSetStab_sec2Fam {x : G} (hx : x ∈ sec2P F)
    (hxS : x ∉ sec2S A R E F) {h : G} (hh : h ∈ sec2P E) (hhS : h ∉ sec2S A R E F)
    (h4 : 4 ^ 4 ≤ Nat.card (conjClosure (E ⊓ A) (sec2P F)))
    (h4' : 4 ^ 4 ≤ Nat.card (conjClosure (F ⊓ A) (sec2P E))) :
    sec2H E F ≤ Sec2.conjSetStab (sec2Fam A E F x) ∧
      sec2H E F ≤ Sec2.conjSetStab (sec2Fam A F E h) := by
  have hSc := sec2S_comm h11 hE16 hF hL hodd
  exact ⟨sup_le (sec2P_le_conjSetStab_sec2Fam h11 hE16 hF hL hodd hx hxS)
      (sec2P_le_conjSetStab_sec2Fam_symm h11 hE16 hF.symm hL hodd hh (hSc ▸ hhS) hx
        (hSc ▸ hxS) h4' h4),
    sup_le (sec2P_le_conjSetStab_sec2Fam_symm h11 hE16 hF hL hodd hx hxS hh hhS h4 h4')
      (sec2P_le_conjSetStab_sec2Fam h11 hE16 hF.symm hL hodd hh (hSc ▸ hhS))⟩

theorem conjSet_F_sec2H_eq {x : G} (hx : x ∈ sec2P F) (hxS : x ∉ sec2S A R E F) {h : G}
    (hh : h ∈ sec2P E) (hhS : h ∉ sec2S A R E F)
    (h4 : 4 ^ 4 ≤ Nat.card (conjClosure (E ⊓ A) (sec2P F)))
    (h4' : 4 ^ 4 ≤ Nat.card (conjClosure (F ⊓ A) (sec2P E))) :
    conjSet F (sec2H E F) = sec2Fam A E F x := by
  obtain ⟨hH𝓕, -⟩ := sec2H_le_conjSetStab_sec2Fam h11 hE16 hF hL hodd hx hxS hh hhS h4 h4'
  have hF𝓕 : F ∈ sec2Fam A E F x := Or.inr ⟨1, one_mem _, (rightConjugate_one F).symm⟩
  refine Set.Subset.antisymm (Sec2.conjSet_subset_of_le_conjSetStab hH𝓕 hF𝓕) ?_
  rintro V (rfl | ⟨p, hp, rfl⟩)
  · by_contra hno
    have hfix : ∀ y ∈ sec2P F, rightConjugate (sec2F0 A E x) y = sec2F0 A E x := by
      intro y hy
      rcases (hH𝓕 (mem_sup_right hy) _).mp (Set.mem_insert _ _) with h1 | ⟨p, hp, h1⟩
      · exact h1
      · exfalso
        apply hno
        refine ⟨p * y⁻¹, mul_mem (mem_sup_left hp) (inv_mem (mem_sup_right hy)), ?_⟩
        rw [← rightConjugate_mul, ← h1, rightConjugate_mul, mul_inv_cancel, rightConjugate_one]
    have hle : conjClosure (E ⊓ A) (sec2P F) ≤ sec2F0 A E x := iSup_le fun y => by
      rw [← hfix y y.2]
      exact AschbacherTheorem3.rightConjugate_le_rightConjugate
        (le_sup_left : E ⊓ A ≤ sec2F0 A E x) y
    have h64 := card_le_of_le hle
    rw [card_sec2F0 h11 hE16 hF hL hodd hx hxS] at h64
    omega
  · exact ⟨p, mem_sup_left hp, rfl⟩

theorem conjSet_E_sec2H_eq {x : G} (hx : x ∈ sec2P F) (hxS : x ∉ sec2S A R E F) {h : G}
    (hh : h ∈ sec2P E) (hhS : h ∉ sec2S A R E F)
    (h4 : 4 ^ 4 ≤ Nat.card (conjClosure (E ⊓ A) (sec2P F)))
    (h4' : 4 ^ 4 ≤ Nat.card (conjClosure (F ⊓ A) (sec2P E))) :
    conjSet E (sec2H E F) = sec2Fam A F E h := by
  have hSc := sec2S_comm h11 hE16 hF hL hodd
  rw [show sec2H E F = sec2H F E from sup_comm _ _]
  exact conjSet_F_sec2H_eq h11 hE16 hF.symm hL hodd hh (hSc ▸ hhS) hx (hSc ▸ hxS) h4' h4

theorem F_not_le_sec2P_of_frame : ¬ F ≤ sec2P E := by
  intro hFP
  obtain ⟨hD, T, hT⟩ := exists_pointsData h11 hE16 hF hL hodd
  have h1 : sec2P E ⊓ normalizer (R : Set G) = E :=
    sec2P_inf_normalizer_eq hD hT (mem_of_mem_centralizer_of_frame hF hL hodd)
      (isPGroup_two_of_isElemAbelian hF.elemE)
  have hFR : F ≤ normalizer (R : Set G) := fun f hf => centralizer_le_normalizer _
    (mem_centralizer_iff.mpr fun r hr =>
      congrArg Subtype.val (hF.elemF.1.is_comm.comm ⟨r, hF.R_le_F hr⟩ ⟨f, hf⟩))
  have hFE : F ≤ E := h1 ▸ le_inf hFP hFR
  exact hF.ne (eq_of_le_of_card_ge hFE (by rw [hF.cardE, hF.cardF])).symm

theorem ncard_sec2Fam {x : G} (hx : x ∈ sec2P F) (hxS : x ∉ sec2S A R E F) :
    (sec2Fam A E F x).ncard = 5 := by
  have hnot : sec2F0 A E x ∉ conjSet F (sec2P E) := by
    rintro ⟨p, hp, hp'⟩
    apply F_not_le_sec2P_of_frame h11 hE16 hF hL hodd
    have h1 : rightConjugate F p ≤ sec2P E :=
      hp' ▸ (sec2F0_le_sec2P_inf_sec2S h11 hE16 hF hL hodd hx hxS).trans inf_le_left
    have h2 := AschbacherTheorem3.rightConjugate_le_rightConjugate h1 p⁻¹
    rwa [rightConjugate_mul, mul_inv_cancel, rightConjugate_one,
      (rightConjugate_eq_self_iff _ _).mpr (le_normalizer (inv_mem hp))] at h2
  rw [sec2Fam, Set.ncard_insert_of_notMem hnot, ← Nat.card_coe_set_eq,
    card_conjSet_sec2P h11 hE16 hF hL hodd]

theorem relIndex_centralizerMod_sec2P :
    (centralizerMod (sec2P E) (R ⊔ sec2Z A E F) (sec2Z A E F)).relIndex (sec2P E) = 4 := by
  obtain ⟨hEC, hCidx, -⟩ := centralizerMod_facts h11 hE16 hF hL hodd
  have hPq := isElemQuot_sec2P h11 hE16 hF hL hodd
  have h := relIndex_mul_relIndex E _ (sec2P E) hEC fun c hc => (mem_centralizerMod.mp hc).1
  rw [hCidx, hPq.2.1] at h
  omega

theorem sec2P_inf_normalizer_sec2F0_symm_eq {h : G} (hh : h ∈ sec2P E)
    (hhS : h ∉ sec2S A R E F) (h4' : 4 ^ 4 ≤ Nat.card (conjClosure (F ⊓ A) (sec2P E))) :
    sec2P E ⊓ normalizer (sec2F0 A F h : Set G) =
      centralizerMod (sec2P E) (R ⊔ sec2Z A E F) (sec2Z A E F) := by
  have hSc := sec2S_comm h11 hE16 hF hL hodd
  have hhS' : h ∉ sec2S A R F E := hSc ▸ hhS
  set C := centralizerMod (sec2P E) (R ⊔ sec2Z A E F) (sec2Z A E F) with hCdef
  set F₀' := sec2F0 A F h with hF₀'
  set M := sec2P E ⊓ normalizer (F₀' : Set G) with hM
  have hCP : C ≤ sec2P E := fun c hc => (mem_centralizerMod.mp hc).1
  have hF₀'S : F₀' ≤ sec2S A R E F :=
    hSc ▸ (sec2F0_le_sec2P_inf_sec2S h11 hE16 hF.symm hL hodd hh hhS').trans inf_le_right
  have hZF₀' : sec2Z A E F ≤ F₀' := by
    rw [hF.sec2Z_eq]
    have h1 : E ⊓ F ⊓ A ≤ F ⊓ A := fun z hz => ⟨hz.1.2, hz.2⟩
    exact h1.trans le_sup_left
  have hCM : C ≤ M := le_inf hCP ((le_sup_right : C ≤ sec2S A R E F).trans
    (sec2S_le_normalizer_of_sec2Z_le h11 hE16 hF hL hodd hZF₀' hF₀'S))
  have hMP : ¬ sec2P E ≤ M := fun hle => by
    have h1 : conjClosure (F ⊓ A) (sec2P E) ≤ F₀' := iSup_le fun p => by
      rw [← (rightConjugate_eq_self_iff F₀' p).mpr (hle p.2).2]
      exact AschbacherTheorem3.rightConjugate_le_rightConjugate (le_sup_left : F ⊓ A ≤ F₀') p
    have h64 := card_le_of_le h1
    rw [card_sec2F0 h11 hE16 hF.symm hL hodd hh hhS'] at h64
    omega
  obtain ⟨y, hyA, hyE, hyF, hyEF, hyfix⟩ := exists_torus_sec2 hF hL hodd
  have hyP := Sec2.normalizer_le_normalizer_sec2P E hyE
  have hyC := (mem_normalizer_sec2S_of_mem hF hyA hyE hyF).2.1
  have hyF₀' := mem_normalizer_sec2F0_of_mem h11 hE16 hF.symm hL hodd hyA hyF hyE hh hhS'
  have hyM : ∀ p ∈ M, y * p * y⁻¹ ∈ M := fun p hp =>
    ⟨(mem_normalizer_iff.mp hyP p).mp hp.1,
      (normalizer (F₀' : Set G)).mul_mem ((normalizer (F₀' : Set G)).mul_mem hyF₀' hp.2)
        ((normalizer (F₀' : Set G)).inv_mem hyF₀')⟩
  have hidx := relIndex_mul_relIndex C M (sec2P E) hCM inf_le_left
  rw [relIndex_centralizerMod_sec2P h11 hE16 hF hL hodd] at hidx
  have hMP1 : M.relIndex (sec2P E) ≠ 1 := fun h1 => hMP (relIndex_eq_one.mp h1)
  have hCM2 : C.relIndex M ≠ 2 := by
    intro h2
    obtain ⟨p, hpM, hpC⟩ : ∃ p ∈ M, p ∉ C := by
      by_contra hno
      push Not at hno
      have h1 : C.relIndex M = 1 := relIndex_eq_one.mpr hno
      omega
    have hq := hyM p hpM
    have hqC : y * p * y⁻¹ ∉ C := fun hq' => hpC (by
      have := (mem_normalizer_iff.mp (inv_mem hyC) _).mp hq'
      simpa [mul_assoc] using this)
    have hidx2 : (C.subgroupOf M).index = 2 := h2
    have hmem := (mul_mem_iff_of_index_two hidx2 (a := (⟨p, hpM⟩ : ↥M)⁻¹)
      (b := ⟨y * p * y⁻¹, hq⟩)).mpr (iff_of_false
        (fun h' => hpC (mem_subgroupOf.mp (by simpa using (C.subgroupOf M).inv_mem h')))
        (fun h' => hqC h'))
    exact hpC (mem_centralizerMod_of_conj_mem h11 hE16 hF hL hodd hyA hyE hyEF hyfix hpM.1 hmem)
  have h1 : C.relIndex M = 1 := by
    have hpos : 0 < M.relIndex (sec2P E) := Nat.pos_of_ne_zero fun h0 => by
      rw [h0, mul_zero] at hidx
      omega
    have hle : C.relIndex M ≤ 2 := by
      by_contra hgt
      push Not at hgt
      have : 3 * 2 ≤ C.relIndex M * M.relIndex (sec2P E) :=
        Nat.mul_le_mul hgt (by omega)
      omega
    have hpos' : 0 < C.relIndex M := Nat.pos_of_ne_zero fun h0 => by
      rw [h0, zero_mul] at hidx
      omega
    omega
  exact le_antisymm (relIndex_eq_one.mp h1) hCM

theorem conjSet_E_sec2H_eq_insert {x : G} (hx : x ∈ sec2P F) (hxS : x ∉ sec2S A R E F) {h : G}
    (hh : h ∈ sec2P E) (hhS : h ∉ sec2S A R E F)
    (h4 : 4 ^ 4 ≤ Nat.card (conjClosure (E ⊓ A) (sec2P F)))
    (h4' : 4 ^ 4 ≤ Nat.card (conjClosure (F ⊓ A) (sec2P E))) :
    conjSet E (sec2H E F) = insert E (conjSet (rightConjugate E x) (sec2P E)) := by
  have hSc := sec2S_comm h11 hE16 hF hL hodd
  rw [conjSet_E_sec2H_eq h11 hE16 hF hL hodd hx hxS hh hhS h4 h4']
  set 𝓔 := sec2Fam A F E h with h𝓔
  have hE𝓔 : E ∈ 𝓔 := Or.inr ⟨1, one_mem _, (rightConjugate_one E).symm⟩
  have h5 : 𝓔.ncard = 5 := ncard_sec2Fam h11 hE16 hF.symm hL hodd hh (hSc ▸ hhS)
  have hF₀'E : sec2F0 A F h ⊓ E = sec2Z A E F := by
    rw [sec2F0_inf_F_eq h11 hE16 hF.symm hL hodd hh (hSc ▸ hhS), sec2Z_comm]
  have hsub : conjSet (sec2F0 A F h) (sec2P E) ⊆ 𝓔 \ {E} := by
    rintro V ⟨p, hp, rfl⟩
    refine ⟨Sec2.conjSet_subset_of_le_conjSetStab
      (sec2P_le_conjSetStab_sec2Fam_symm h11 hE16 hF hL hodd hx hxS hh hhS h4 h4')
      (Set.mem_insert _ _) ⟨p, hp, rfl⟩, fun hpE => ?_⟩
    have hEp : sec2F0 A F h = E := by
      have h1 : rightConjugate (rightConjugate (sec2F0 A F h) p) p⁻¹ = rightConjugate E p⁻¹ := by
        rw [hpE]
      rwa [rightConjugate_mul, mul_inv_cancel, rightConjugate_one,
        (rightConjugate_eq_self_iff E p⁻¹).mpr (Sec2.sec2P_le E (inv_mem hp))] at h1
    have h1 := hF₀'E
    rw [hEp, inf_idem] at h1
    have h2 := hF.cardE
    rw [h1, hF.card_sec2Z hodd] at h2
    omega
  have hcard : (conjSet (sec2F0 A F h) (sec2P E)).ncard = 4 := by
    rw [← Nat.card_coe_set_eq, Sec2.card_conjSet_eq_relIndex, ← inf_relIndex_left,
      sec2P_inf_normalizer_sec2F0_symm_eq h11 hE16 hF hL hodd hh hhS h4',
      relIndex_centralizerMod_sec2P h11 hE16 hF hL hodd]
  have heq : conjSet (sec2F0 A F h) (sec2P E) = 𝓔 \ {E} :=
    Set.eq_of_subset_of_ncard_le hsub (by rw [Set.ncard_sdiff_singleton_of_mem hE𝓔, h5, hcard])
  have hEx : rightConjugate E x ∈ 𝓔 \ {E} := by
    refine ⟨Or.inr ⟨x, hx, rfl⟩, fun hxE => hxS ?_⟩
    have h1 : x ∈ (sec2P F ⊔ sec2S A R F E) ⊓ normalizer (E : Set G) :=
      ⟨mem_sup_left hx, (rightConjugate_eq_self_iff E x).mp hxE⟩
    rw [sec2P_sup_sec2S_inf_normalizer h11 hE16 hF.symm hL hodd, hSc] at h1
    exact h1
  rw [← heq] at hEx
  rw [Sec2.conjSet_eq_of_mem_conjSet hEx, heq, Set.insert_sdiff_singleton,
    Set.insert_eq_of_mem hE𝓔]

theorem planes_sec2S_eq_conjSet_union {x : G} (hx : x ∈ sec2P F) (hxS : x ∉ sec2S A R E F)
    {h : G} (hh : h ∈ sec2P E) (hhS : h ∉ sec2S A R E F)
    (h4 : 4 ^ 4 ≤ Nat.card (conjClosure (E ⊓ A) (sec2P F)))
    (h4' : 4 ^ 4 ≤ Nat.card (conjClosure (F ⊓ A) (sec2P E))) :
    {V | V ∈ planes E F ∧ V ≤ sec2S A R E F} =
      conjSet F (sec2H E F) ∪ conjSet E (sec2H E F) := by
  rw [planes_sec2S_eq_union h11 hE16 hF hL hodd hx hxS hh hhS h4 h4',
    conjSet_F_sec2H_eq h11 hE16 hF hL hodd hx hxS hh hhS h4 h4',
    conjSet_E_sec2H_eq h11 hE16 hF hL hodd hx hxS hh hhS h4 h4']

theorem inf_F_eq_of_mem_sec2Fam {x : G} (hx : x ∈ sec2P F) (hxS : x ∉ sec2S A R E F)
    {V : Subgroup G} (hV : V ∈ sec2Fam A E F x) (hVF : V ≠ F) : V ⊓ F = sec2Z A E F := by
  rcases hV with rfl | ⟨p, hp, rfl⟩
  · exact sec2F0_inf_F_eq h11 hE16 hF hL hodd hx hxS
  · have hpC : p ∉ centralizerMod (sec2P E) (R ⊔ sec2Z A E F) (sec2Z A E F) := fun hpC =>
      hVF ((rightConjugate_eq_self_iff F p).mpr
        (sec2S_le_normalizer h11 hE16 hF hL hodd (mem_sup_right hpC)))
    rw [inf_comm]
    exact (sec2S_eq_sup_rightConjugate h11 hE16 hF hL hodd hp hpC).1

theorem sec2H_le_normalizer_sec2Z : sec2H E F ≤ normalizer (sec2Z A E F : Set G) := by
  intro n hn
  rw [← centerIn_sec2S_eq h11 hE16 hF hL hodd]
  exact mem_normalizer_centerIn ((sup_le (sec2P_le_normalizer_sec2S h11 hE16 hF hL hodd)
    (sec2P_F_le_normalizer_sec2S h11 hE16 hF hL hodd)) hn)

theorem inf_eq_sec2Z_and_card_inf {x : G} (hx : x ∈ sec2P F) (hxS : x ∉ sec2S A R E F) {h : G}
    (hh : h ∈ sec2P E) (hhS : h ∉ sec2S A R E F)
    (h4 : 4 ^ 4 ≤ Nat.card (conjClosure (E ⊓ A) (sec2P F)))
    (h4' : 4 ^ 4 ≤ Nat.card (conjClosure (F ⊓ A) (sec2P E))) {V : Subgroup G}
    (hV : V ∈ conjSet F (sec2H E F)) :
    (∀ W ∈ conjSet F (sec2H E F), V ≠ W → V ⊓ W = sec2Z A E F) ∧
      ∀ W ∈ conjSet E (sec2H E F), Nat.card (V ⊓ W : Subgroup G) = 16 := by
  have hSc := sec2S_comm h11 hE16 hF hL hodd
  have hFH := conjSet_F_sec2H_eq h11 hE16 hF hL hodd hx hxS hh hhS h4 h4'
  have hEH := conjSet_E_sec2H_eq h11 hE16 hF hL hodd hx hxS hh hhS h4 h4'
  obtain ⟨η, hη, rfl⟩ := hV
  have hconj : ∀ W : Subgroup G,
      rightConjugate F η ⊓ W = rightConjugate (F ⊓ rightConjugate W η⁻¹) η := fun W => by
    rw [AschbacherTheorem3.rightConjugate_inf, rightConjugate_mul, inv_mul_cancel,
      rightConjugate_one]
  refine ⟨fun W hW hne => ?_, fun W hW => ?_⟩
  · obtain ⟨θ, hθ, rfl⟩ := hW
    have hW' : rightConjugate (rightConjugate F θ) η⁻¹ ∈ conjSet F (sec2H E F) :=
      ⟨θ * η⁻¹, mul_mem hθ (inv_mem hη), rightConjugate_mul F θ η⁻¹⟩
    have hne' : rightConjugate (rightConjugate F θ) η⁻¹ ≠ F := fun h' => hne (by
      calc rightConjugate F η = rightConjugate (rightConjugate (rightConjugate F θ) η⁻¹) η := by
            rw [h']
        _ = rightConjugate F θ := by
            rw [rightConjugate_mul, rightConjugate_mul, inv_mul_cancel, mul_one])
    rw [hFH] at hW'
    rw [hconj, inf_comm, inf_F_eq_of_mem_sec2Fam h11 hE16 hF hL hodd hx hxS hW' hne',
      (rightConjugate_eq_self_iff _ η).mpr (sec2H_le_normalizer_sec2Z h11 hE16 hF hL hodd hη)]
  · obtain ⟨θ, hθ, rfl⟩ := hW
    have hW' : rightConjugate (rightConjugate E θ) η⁻¹ ∈ conjSet E (sec2H E F) :=
      ⟨θ * η⁻¹, mul_mem hθ (inv_mem hη), rightConjugate_mul E θ η⁻¹⟩
    rw [hEH] at hW'
    rw [hconj, rightConjugate_card, inf_comm]
    exact card_inf_E_of_mem_sec2Fam h11 hE16 hF.symm hL hodd hh (hSc ▸ hhS) hW'

theorem image_conjSet_sec2H_eq_or {x : G} (hx : x ∈ sec2P F) (hxS : x ∉ sec2S A R E F) {h : G}
    (hh : h ∈ sec2P E) (hhS : h ∉ sec2S A R E F)
    (h4 : 4 ^ 4 ≤ Nat.card (conjClosure (E ⊓ A) (sec2P F)))
    (h4' : 4 ^ 4 ≤ Nat.card (conjClosure (F ⊓ A) (sec2P E))) {n : G}
    (hn : n ∈ normalizer (sec2S A R E F : Set G)) :
    (fun V => rightConjugate V n) '' conjSet F (sec2H E F) = conjSet F (sec2H E F) ∨
      (fun V => rightConjugate V n) '' conjSet F (sec2H E F) = conjSet E (sec2H E F) := by
  have hSc := sec2S_comm h11 hE16 hF hL hodd
  have hU := planes_sec2S_eq_conjSet_union h11 hE16 hF hL hodd hx hxS hh hhS h4 h4'
  have hFH := conjSet_F_sec2H_eq h11 hE16 hF hL hodd hx hxS hh hhS h4 h4'
  have hEH := conjSet_E_sec2H_eq h11 hE16 hF hL hodd hx hxS hh hhS h4 h4'
  set 𝓕 := conjSet F (sec2H E F) with h𝓕
  set 𝓔 := conjSet E (sec2H E F) with h𝓔
  have hdisj : ∀ V ∈ 𝓕, V ∉ 𝓔 := fun V hV hV' => by
    rw [hFH] at hV
    rw [hEH] at hV'
    exact not_mem_sec2Fam_of_mem_sec2Fam h11 hE16 hF hL hodd hx hxS hh hhS hV hV'
  have h𝓕5 : 𝓕.ncard = 5 := by rw [hFH]; exact ncard_sec2Fam h11 hE16 hF hL hodd hx hxS
  have h𝓔5 : 𝓔.ncard = 5 := by
    rw [hEH]
    exact ncard_sec2Fam h11 hE16 hF.symm hL hodd hh (hSc ▸ hhS)
  have hF𝓕 : F ∈ 𝓕 := ⟨1, one_mem _, (rightConjugate_one F).symm⟩
  have hnZ : n ∈ normalizer (sec2Z A E F : Set G) := by
    rw [← centerIn_sec2S_eq h11 hE16 hF hL hodd]
    exact mem_normalizer_centerIn hn
  have hnP : ∀ V ∈ 𝓕 ∪ 𝓔, rightConjugate V n ∈ 𝓕 ∪ 𝓔 := fun V hV => by
    rw [← hU] at hV ⊢
    refine ⟨rightConjugate_mem_planes hV.1 n, ?_⟩
    rw [← (rightConjugate_eq_self_iff _ n).mpr hn]
    exact AschbacherTheorem3.rightConjugate_le_rightConjugate hV.2 n
  have hinj : Function.Injective (fun V : Subgroup G => rightConjugate V n) := fun V W hVW => by
    have h1 : rightConjugate (rightConjugate V n) n⁻¹ = rightConjugate (rightConjugate W n) n⁻¹ :=
      by simp only at hVW; rw [hVW]
    rwa [rightConjugate_mul, rightConjugate_mul, mul_inv_cancel, rightConjugate_one,
      rightConjugate_one] at h1
  have hZ : ∀ V ∈ 𝓕, V ≠ F → rightConjugate V n ⊓ rightConjugate F n = sec2Z A E F :=
    fun V hV hVF => by
      rw [← AschbacherTheorem3.rightConjugate_inf,
        (inf_eq_sec2Z_and_card_inf h11 hE16 hF hL hodd hx hxS hh hhS h4 h4' hV).1 F hF𝓕 hVF,
        (rightConjugate_eq_self_iff _ n).mpr hnZ]
  have hcross : ∀ V ∈ 𝓕, ∀ W ∈ 𝓔, Nat.card (V ⊓ W : Subgroup G) = 16 := fun V hV W hW =>
    (inf_eq_sec2Z_and_card_inf h11 hE16 hF hL hodd hx hxS hh hhS h4 h4' hV).2 W hW
  have hZ4 := hF.card_sec2Z hodd
  have himage : ((fun V => rightConjugate V n) '' 𝓕).ncard = 5 := by
    rw [Set.ncard_image_of_injective _ hinj, h𝓕5]
  rcases hnP F (Or.inl hF𝓕) with hFn | hFn
  · left
    refine Set.eq_of_subset_of_ncard_le ?_ (by rw [himage, h𝓕5])
    rintro _ ⟨V, hV, rfl⟩
    rcases hnP V (Or.inl hV) with h1 | h1
    · exact h1
    · exfalso
      by_cases hVF : V = F
      · subst hVF
        exact hdisj _ hFn h1
      · have h2 := hcross _ hFn _ h1
        rw [inf_comm, hZ V hV hVF, hZ4] at h2
        omega
  · right
    refine Set.eq_of_subset_of_ncard_le ?_ (by rw [himage, h𝓔5])
    rintro _ ⟨V, hV, rfl⟩
    rcases hnP V (Or.inl hV) with h1 | h1
    · exfalso
      by_cases hVF : V = F
      · subst hVF
        exact hdisj _ h1 hFn
      · have h2 := hcross _ h1 _ hFn
        rw [hZ V hV hVF, hZ4] at h2
        omega
    · exact h1

end Frame

end CFSG.ComponentClassification.AS81
