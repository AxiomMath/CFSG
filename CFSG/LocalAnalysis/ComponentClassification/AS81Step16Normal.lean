module

public import CFSG.LocalAnalysis.ComponentClassification.AS81Step16Radical
public import CFSG.LocalAnalysis.ComponentClassification.AS81Step16Outer
public import CFSG.LocalAnalysis.ComponentClassification.AS81Step16Kernel

public section

namespace CFSG.ComponentClassification.AS81

open Subgroup CFSG.Open CFSG.ABGLocalTools CFSG.ComponentClassification.AschbacherTightEmbedding
open CFSG.ComponentClassification.RankTwoStandard

variable {G : Type} [Group G] [Finite G] {A R : Subgroup G} {g : G} {E F : Subgroup G}

section Points

theorem rightConjugate_mem_pointsIn_frame (hF : Frame G A A R g E F) :
    rightConjugate R g ∈ pointsIn R E ∧ rightConjugate R g ≤ E ⊓ F ∧ rightConjugate R g ≠ R := by
  have hV : rightConjugate R g ≤ E ⊓ F := by rw [hF.inf_eq]; exact le_sup_right
  refine ⟨⟨hV.trans inf_le_left, g, rfl⟩, hV, fun h => ?_⟩
  have h1 : E ⊓ F = R := by rw [hF.inf_eq, h, sup_idem]
  have := card_inf_of_frame hF
  rw [h1, hF.cardR] at this
  omega

theorem exists_three_points {d : L34E16Cert}
    (hE16 : RankTwoL3Four.HypII.l34CheckWE16 d = true) (h11 : Step11)
    (hF : Frame G A A R g E F) (hL : TypeL34 (rankTwoQuot A))
    (h2 : Nat.card (pointsIn R (E ⊓ F)) = 2) :
    ∃ Q₁ ∈ pointsIn R E, ∃ Q₂ ∈ pointsIn R E, ∃ Q₃ ∈ pointsIn R E,
      Q₁ ≠ R ∧ Q₂ ≠ R ∧ Q₃ ≠ R ∧ Q₁ ≠ rightConjugate R g ∧ Q₂ ≠ rightConjugate R g ∧
        Q₃ ≠ rightConjugate R g ∧ Q₁ ≠ Q₂ ∧ Q₁ ≠ Q₃ ∧ Q₂ ≠ Q₃ := by
  obtain ⟨hP, -, hPR⟩ := rightConjugate_mem_pointsIn_frame hF
  have h6 := card_pointsIn_eq_six hE16 h11 hF hL h2
  have hsub : ({R, rightConjugate R g} : Set (Subgroup G)) ⊆ pointsIn R E := by
    rintro X (rfl | rfl)
    · exact self_mem_pointsIn hF.R_le_E
    · exact hP
  have hcard : (pointsIn R E \ {R, rightConjugate R g}).ncard = 4 := by
    rw [Set.ncard_sdiff hsub, Set.ncard_pair hPR.symm, ← Nat.card_coe_set_eq, h6]
  obtain ⟨Q₁, Q₂, Q₃, hQ₁, hQ₂, hQ₃, h₁₂, h₁₃, h₂₃⟩ :=
    (Set.two_lt_ncard_iff (s := pointsIn R E \ {R, rightConjugate R g}) (Set.toFinite _)).mp
      (by omega)
  simp only [Set.mem_sdiff, Set.mem_insert_iff, Set.mem_singleton_iff, not_or] at hQ₁ hQ₂ hQ₃
  exact ⟨Q₁, hQ₁.1, Q₂, hQ₂.1, Q₃, hQ₃.1, hQ₁.2.1, hQ₂.2.1, hQ₃.2.1, hQ₁.2.2, hQ₂.2.2, hQ₃.2.2,
    h₁₂, h₁₃, h₂₃⟩

theorem mem_centralizer_of_fix_points {d : L34E16Cert}
    (hE16 : RankTwoL3Four.HypII.l34CheckWE16 d = true) (h11 : Step11)
    (hF : Frame G A A R g E F) (hL : TypeL34 (rankTwoQuot A))
    (h2 : Nat.card (pointsIn R (E ⊓ F)) = 2) {k : G}
    (hk : ∀ Q ∈ pointsIn R E, k ∈ normalizer (Q : Set G)) {r : G} (hr : r ∈ R) (hr1 : r ≠ 1)
    (hkr : k * r * k⁻¹ = r) : k ∈ centralizer (E : Set G) := by
  have hKte := AS76b.tightlyEmbedded_centralizer hF.base.hyp.standard
  have hcommE : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (hF.elemE.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  have hE2 : ∀ x ∈ E, x * x = 1 := fun x hx => by rw [← sq]; exact hF.elemE.2 x hx
  have hcard : ∀ Q ∈ pointsIn R E, Nat.card Q = 4 := by
    rintro Q ⟨-, x, rfl⟩
    rw [rightConjugate_card, hF.cardR]
  obtain ⟨hP, hPV, hPR⟩ := rightConjugate_mem_pointsIn_frame hF
  set P := rightConjugate R g
  have hR : R ∈ pointsIn R E := self_mem_pointsIn hF.R_le_E
  obtain ⟨Q₁, hQ₁, Q₂, hQ₂, Q₃, hQ₃, h₁R, h₂R, h₃R, h₁P, h₂P, h₃P, h₁₂, h₁₃, h₂₃⟩ :=
    exists_three_points hE16 h11 hF hL h2
  have hT : ∀ X ∈ pointsIn R E, ∀ Y ∈ pointsIn R E, X ≠ R → Y ≠ R → X ≠ Y →
      X ⊓ (R ⊔ Y) = ⊥ := fun X hX Y hY hXR hYR hXY =>
    inf_sup_eq_bot_of_card_two hE16 h11 hF hL h2 hX hY hXR hYR hXY
  have hF' := frame_at_point hE16 hF hL hPV hPR
  have h2' : Nat.card (pointsIn P (E ⊓ F)) = 2 := by rw [pointsIn_rightConjugate]; exact h2
  have hT' : ∀ X ∈ pointsIn R E, ∀ Y ∈ pointsIn R E, X ≠ P → Y ≠ P → X ≠ Y →
      X ⊓ (P ⊔ Y) = ⊥ := fun X hX Y hY hXP hYP hXY =>
    inf_sup_eq_bot_of_card_two hE16 h11 hF' (typeL34_rightConjugate g hL) h2'
      ((pointsIn_rightConjugate R E g).symm ▸ hX) ((pointsIn_rightConjugate R E g).symm ▸ hY)
      hXP hYP hXY
  have h₁ : R ⊓ P = ⊥ := inf_eq_bot_of_mem_pointsIn hKte hF.sylowR hcommE hR hP hPR.symm
  exact mem_centralizer_of_normalizes hcommE hE2 hF.cardE hF.R_le_E hP.1 hQ₁.1 hQ₂.1 hQ₃.1
    hF.cardR (hcard P hP) (hcard Q₁ hQ₁) (hcard Q₂ hQ₂) (hcard Q₃ hQ₃) h₁
    (hT Q₁ hQ₁ P hP h₁R hPR h₁P) (hT' Q₂ hQ₂ Q₁ hQ₁ h₂P h₁P h₁₂.symm)
    (hT Q₂ hQ₂ P hP h₂R hPR h₂P) (hT' Q₃ hQ₃ Q₁ hQ₁ h₃P h₁P h₁₃.symm)
    (hT Q₃ hQ₃ P hP h₃R hPR h₃P) (hT' Q₂ hQ₂ Q₃ hQ₃ h₂P h₃P h₂₃)
    (hT Q₂ hQ₂ Q₁ hQ₁ h₂R h₁R h₁₂.symm) (hk R hR) (hk P hP) (hk Q₁ hQ₁) (hk Q₂ hQ₂)
    (hk Q₃ hQ₃) hr hr1 hkr

end Points

theorem exists_torus_conj {d : L34E16Cert}
    (hE16 : RankTwoL3Four.HypII.l34CheckWE16 d = true) (h11 : Step11)
    (hF : Frame G A A R g E F) (hL : TypeL34 (rankTwoQuot A))
    (heven : Even (Nat.card (center ↥A))) (h2 : Nat.card (pointsIn R (E ⊓ F)) = 2) :
    ∃ y ∈ rightConjugate A g, y ∈ normalizer (E : Set G) ∧ y ∈ normalizer (R : Set G) ∧
      ∀ r ∈ R, r ≠ 1 → y * r * y⁻¹ ≠ r := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hKte := AS76b.tightlyEmbedded_centralizer hF.base.hyp.standard
  have hcommE : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (hF.elemE.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  have hRA := le_of_card_pointsIn_inf_eq_two hE16 h11 hF hL heven h2
  obtain ⟨hP, hPV, hPR⟩ := rightConjugate_mem_pointsIn_frame hF
  set P := rightConjugate R g
  have hF' := frame_at_point hE16 hF hL hPV hPR
  have hL' := typeL34_rightConjugate g hL
  obtain ⟨y, hyA, ⟨n, hn⟩, hyEF, hyC, -⟩ := exists_torus_frame h11 hF' hL'
  have hPA : P ≤ rightConjugate A g := AschbacherTheorem3.rightConjugate_le_rightConjugate hRA g
  have hS : IsSylowOf 2 (E ⊔ F) (rightConjugate A g) := by
    have h := hF'.sylow
    rwa [sup_eq_left.mpr hPA] at h
  have hP4 : Nat.card P = 4 := by rw [rightConjugate_card, hF.cardR]
  have hperm : ∀ X : Subgroup G, (X = E ∨ X = F) →
      rightConjugate X y = E ∨ rightConjugate X y = F := by
    intro X hX
    have hXle : X ≤ E ⊔ F := by
      rcases hX with rfl | rfl
      exacts [le_sup_left, le_sup_right]
    have hXe : IsElemAbelian 2 X := by
      rcases hX with rfl | rfl
      exacts [hF.elemE, hF.elemF]
    have hXc : Nat.card X = 64 := by
      rcases hX with rfl | rfl
      exacts [hF.cardE, hF.cardF]
    have hle : rightConjugate X y ≤ E ⊔ F := by
      have h1 := AschbacherTheorem3.rightConjugate_le_rightConjugate hXle y
      rwa [(rightConjugate_eq_self_iff _ y).mpr hyEF] at h1
    exact eq_or_eq_of_component h11 hF'.base hL' hF'.sylowR hPA hP4 hS le_sup_left le_sup_right
      hle hF.elemE hF.elemF (AS76b.isElemAbelian_rightConjugate hXe y) hF.cardE hF.cardF
      (by rw [rightConjugate_card, hXc]) hF.ne
  have hpow : (y ^ 2) ^ ((3 ^ n + 1) / 2) = y := by
    have hodd : Odd (3 ^ n) := Odd.pow (by decide)
    obtain ⟨m, hm⟩ := hodd
    have h1 : (3 ^ n + 1) / 2 = m + 1 := by omega
    rw [h1, ← pow_mul]
    have h2 : 2 * (m + 1) = 3 ^ n + 1 := by omega
    rw [h2, pow_succ, hn, one_mul]
  have hyE : y ∈ normalizer (E : Set G) := by
    rcases hperm E (Or.inl rfl) with h | h
    · exact (rightConjugate_eq_self_iff E y).mp h
    · exfalso
      have hFy : rightConjugate F y = E := by
        rcases hperm F (Or.inr rfl) with h' | h'
        · exact h'
        · exfalso
          apply hF.ne
          have h3 := congrArg (fun X => rightConjugate X y⁻¹) (h.trans h'.symm)
          simp only [rightConjugate_mul, mul_inv_cancel, rightConjugate_one] at h3
          exact h3
      have hy2 : y ^ 2 ∈ normalizer (E : Set G) := by
        rw [← rightConjugate_eq_self_iff, sq, ← rightConjugate_mul, h, hFy]
      have hyE' : y ∈ normalizer (E : Set G) := hpow ▸ pow_mem hy2 _
      rw [(rightConjugate_eq_self_iff E y).mpr hyE'] at h
      exact hF.ne h
  set V := E ⊓ F with hVdef
  have hVab : ∀ a ∈ V, ∀ b ∈ V, a * b = b * a := fun a ha b hb => hcommE a ha.1 b hb.1
  have hRV : R ∈ pointsIn R V := self_mem_pointsIn (le_inf hF.R_le_E hF.R_le_F)
  have hPV' : P ∈ pointsIn R V := ⟨hPV, g, rfl⟩
  have hpts : ∀ Q ∈ pointsIn R V, Q = R ∨ Q = P := by
    intro Q hQ
    by_contra hQ'
    push Not at hQ'
    have hsub : ({R, P, Q} : Set (Subgroup G)) ⊆ pointsIn R V := by
      rintro X (rfl | rfl | rfl)
      · exact hRV
      · exact hPV'
      · exact hQ
    have h1 := Set.ncard_le_ncard hsub (Set.toFinite _)
    rw [Set.ncard_insert_of_notMem (by simp [hPR.symm, hQ'.1.symm]), Set.ncard_pair hQ'.2.symm,
      ← Nat.card_coe_set_eq, h2] at h1
    omega
  have hyP : y ∈ normalizer (P : Set G) :=
    Subgroup.centralizer_le_normalizer _ (mem_centralizer_iff.mpr fun r hr =>
      (mem_centralizer_iff.mp (hF'.sylowR.le hr) y hyA).symm)
  have hyV : y ∈ normalizer (V : Set G) := by
    rw [hVdef, hF.inf_eq_center]
    exact mem_normalizer_centerIn hyEF
  have hyR : y ∈ normalizer (R : Set G) := by
    rw [← rightConjugate_eq_self_iff]
    have hmem : rightConjugate R y ∈ pointsIn R V := by
      refine ⟨?_, y, rfl⟩
      have h1 := AschbacherTheorem3.rightConjugate_le_rightConjugate hRV.1 y
      rwa [(rightConjugate_eq_self_iff V y).mpr hyV] at h1
    rcases hpts _ hmem with h | h
    · exact h
    · exfalso
      apply hPR
      have h1 := congrArg (fun Q => rightConjugate Q y⁻¹) h
      simp only [rightConjugate_mul, mul_inv_cancel, rightConjugate_one] at h1
      rw [h1, (rightConjugate_eq_self_iff _ _).mpr (inv_mem hyP)]
  refine ⟨y, hyA, hyE, hyR, fun r hr hr1 hyr => hr1 ?_⟩
  have hcomm : y * r = r * y := by
    calc y * r = y * r * y⁻¹ * y := by group
      _ = r * y := by rw [hyr]
  have hrP := hyC r (le_inf hF.R_le_E hF.R_le_F hr) hcomm
  have h1 : r ∈ R ⊓ P := ⟨hr, hrP⟩
  rwa [inf_eq_bot_of_mem_pointsIn hKte hF.sylowR hVab hRV hPV' hPR.symm, mem_bot] at h1

theorem radical_at_point {d : L34E16Cert}
    (hE16 : RankTwoL3Four.HypII.l34CheckWE16 d = true) (h11 : Step11)
    (hF : Frame G A A R g E F) (hL : TypeL34 (rankTwoQuot A)) (hRA : R ≤ A) {x : G}
    (hx : rightConjugate R x ≤ E) :
    rightConjugate A x ⊓ normalizer (E : Set G) ≤
        ⁅rightConjugate A x ⊓ normalizer (E : Set G),
          rightConjugate A x ⊓ normalizer (E : Set G)⁆ ⊔ centralizer (E : Set G) ∧
      (rightConjugate A x ⊓ centralizer (E : Set G)).relIndex
        (rightConjugate A x ⊓ normalizer (E : Set G)) = 60 := by
  have hB' := base_rightConjugate hF.base hL x
  have hL' := typeL34_rightConjugate x hL
  have hR' : IsSylowOf 2 (rightConjugate R x) (centralizer (rightConjugate A x : Set G)) := by
    rw [← AschbacherTheorem3.rightConjugate_centralizer]
    exact AschbacherTheorem3.isSylowOf_rightConjugate hF.sylowR x
  have hRA' := AschbacherTheorem3.rightConjugate_le_rightConjugate hRA x
  have hR4' : Nat.card (rightConjugate R x) = 4 := by rw [rightConjugate_card, hF.cardR]
  have hEA' : E ≤ rightConjugate A x := by
    have h := le_sup_rightConjugate hE16 hF.base hL hF.sylowR hF.elemR hF.cardR hF.elemE
      hF.cardE hx
    rwa [sup_eq_left.mpr hRA'] at h
  obtain ⟨-, h1, h2⟩ := radical_of_component h11 hB' hL' hR' hRA' hR4' hEA' hF.elemE hF.cardE
  exact ⟨h1, h2⟩


section Action

variable (R E) [Fintype ↥(pointsIn R E)] [DecidableEq ↥(pointsIn R E)]

theorem exists_pointsAction_eq (h6 : Nat.card (pointsIn R E) = 6) {X : Subgroup G}
    (hXN : X ≤ normalizer (E : Set G)) (P : ↥(pointsIn R E))
    (hXP : ∀ x (hx : x ∈ X), pointsAction R E ⟨x, hXN hx⟩ P = P)
    (hXalt : ∀ x (hx : x ∈ X),
      pointsAction R E ⟨x, hXN hx⟩ ∈ alternatingGroup ↥(pointsIn R E))
    (hXker : ∀ x (hx : x ∈ X), pointsAction R E ⟨x, hXN hx⟩ = 1 →
      x ∈ centralizer (E : Set G))
    (hidx : (X ⊓ centralizer (E : Set G)).relIndex X = 60)
    {σ : Equiv.Perm ↥(pointsIn R E)} (hσ : σ ∈ alternatingGroup ↥(pointsIn R E))
    (hσP : σ P = P) : ∃ x, ∃ hx : x ∈ X, pointsAction R E ⟨x, hXN hx⟩ = σ := by
  have hker : (pointsAction R E).ker ⊓ X.subgroupOf (normalizer (E : Set G)) =
      (centralizer (E : Set G)).subgroupOf (normalizer (E : Set G)) ⊓
        X.subgroupOf (normalizer (E : Set G)) := by
    ext x
    simp only [mem_inf, MonoidHom.mem_ker, mem_subgroupOf]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨hXker x h2 h1, h2⟩
    · rintro ⟨h1, h2⟩
      exact ⟨pointsAction_eq_one_of_mem_centralizer h1, h2⟩
  have hcardX : Nat.card ((X.subgroupOf (normalizer (E : Set G))).map (pointsAction R E)) =
      60 := by
    rw [← Subgroup.relIndex_ker, ← inf_relIndex_right, hker, inf_relIndex_right,
      relIndex_subgroupOf hXN, ← inf_relIndex_left, hidx]
  have h3 : 3 ≤ Nat.card ↥(pointsIn R E) := by rw [h6]; norm_num
  have : Nontrivial ↥(pointsIn R E) := Finite.one_lt_card_iff_nontrivial.mp (by omega)
  have : MulAction.IsPretransitive (alternatingGroup ↥(pointsIn R E)) ↥(pointsIn R E) :=
    alternatingGroup.isPretransitive_of_three_le_card _ h3
  have hidxS := MulAction.index_stabilizer_of_transitive (alternatingGroup ↥(pointsIn R E)) P
  have hcardAlt : Nat.card (alternatingGroup ↥(pointsIn R E)) = 360 := by
    rw [nat_card_alternatingGroup, h6]
    rfl
  have hcardSt : Nat.card ((MulAction.stabilizer (alternatingGroup ↥(pointsIn R E)) P).map
      (alternatingGroup ↥(pointsIn R E)).subtype) = 60 := by
    rw [card_map_of_injective (alternatingGroup _).subtype_injective]
    have h := (MulAction.stabilizer (alternatingGroup ↥(pointsIn R E)) P).index_mul_card
    rw [hidxS, hcardAlt, h6] at h
    omega
  have hmemSt : ∀ τ : Equiv.Perm ↥(pointsIn R E), τ ∈ alternatingGroup ↥(pointsIn R E) →
      τ P = P → τ ∈ (MulAction.stabilizer (alternatingGroup ↥(pointsIn R E)) P).map
        (alternatingGroup ↥(pointsIn R E)).subtype := fun τ hτ hτP => ⟨⟨τ, hτ⟩, hτP, rfl⟩
  have hle : (X.subgroupOf (normalizer (E : Set G))).map (pointsAction R E) ≤
      (MulAction.stabilizer (alternatingGroup ↥(pointsIn R E)) P).map
        (alternatingGroup ↥(pointsIn R E)).subtype := by
    rintro _ ⟨x, hx, rfl⟩
    exact hmemSt _ (hXalt x hx) (hXP x hx)
  have heq := Subgroup.eq_of_le_of_card_ge hle (by rw [hcardSt, hcardX])
  obtain ⟨x, hx, hxσ⟩ := heq ▸ hmemSt σ hσ hσP
  exact ⟨x, hx, hxσ⟩

end Action

section Main

omit [Finite G] in
theorem commutator_subgroupOf {H K : Subgroup G} (hHK : H ≤ K) :
    ⁅H, H⁆.subgroupOf K = ⁅H.subgroupOf K, H.subgroupOf K⁆ := by
  apply Subgroup.map_injective K.subtype_injective
  have hc : ⁅H, H⁆ ≤ K := (Subgroup.commutator_le.mpr fun a ha b hb => by
    rw [commutatorElement_def]
    exact H.mul_mem (H.mul_mem (H.mul_mem ha hb) (H.inv_mem ha)) (H.inv_mem hb)).trans hHK
  rw [subgroupOf_map_subtype, map_commutator, subgroupOf_map_subtype, inf_eq_left.mpr hc,
    inf_eq_left.mpr hHK]

theorem exists_normal_perfect {d : L34E16Cert}
    (hE16 : RankTwoL3Four.HypII.l34CheckWE16 d = true) (h11 : Step11)
    (hF : Frame G A A R g E F) (hL : TypeL34 (rankTwoQuot A))
    (heven : Even (Nat.card (center ↥A))) (h2 : Nat.card (pointsIn R (E ⊓ F)) = 2) :
    ∃ L : Subgroup G, centralizer (E : Set G) ≤ L ∧ L ≤ normalizer (E : Set G) ∧
      normalizer (E : Set G) ≤ normalizer (L : Set G) ∧
      ⁅L, L⁆ ⊔ centralizer (E : Set G) = L ∧ (centralizer (E : Set G)).relIndex L = 1080 := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hRA := le_of_card_pointsIn_inf_eq_two hE16 h11 hF hL heven h2
  have h6 := card_pointsIn_eq_six hE16 h11 hF hL h2
  have : Fintype ↥(pointsIn R E) := Fintype.ofFinite _
  obtain ⟨hP, hPV, hPR⟩ := rightConjugate_mem_pointsIn_frame hF
  have hR : R ∈ pointsIn R E := self_mem_pointsIn hF.R_le_E
  have hCN : centralizer (E : Set G) ≤ normalizer (E : Set G) :=
    Subgroup.centralizer_le_normalizer _
  set L : Subgroup G := centralizer (E : Set G) ⊔
    ⨆ (x : G) (_ : rightConjugate R x ≤ E), rightConjugate A x ⊓ normalizer (E : Set G)
    with hLdef
  have hCL : centralizer (E : Set G) ≤ L := le_sup_left
  have hcompL : ∀ x : G, rightConjugate R x ≤ E →
      rightConjugate A x ⊓ normalizer (E : Set G) ≤ L := fun x hx =>
    le_sup_of_le_right (le_iSup₂_of_le x hx le_rfl)
  have hLN : L ≤ normalizer (E : Set G) := sup_le hCN (iSup₂_le fun x _ => inf_le_right)
  have hAL : A ⊓ normalizer (E : Set G) ≤ L := by
    have h := hcompL 1 (by rw [rightConjugate_one]; exact hF.R_le_E)
    rwa [rightConjugate_one] at h
  have hAgL : rightConjugate A g ⊓ normalizer (E : Set G) ≤ L := hcompL g hP.1
  have hnormL : normalizer (E : Set G) ≤ normalizer (L : Set G) := by
    intro n hn
    have hle : rightConjugate L n ≤ L := by
      unfold rightConjugate
      rw [Subgroup.map_le_iff_le_comap]
      refine sup_le (fun c hc => ?_) (iSup₂_le fun x hx a ha => ?_)
      · refine hCL ?_
        have := conj_mem_centralizer (inv_mem hn) hc
        simpa [MulAut.conj_apply] using this
      · rw [mem_comap]
        have hxn : rightConjugate R (x * n) ≤ E := by
          rw [← rightConjugate_mul]
          have h1 := AschbacherTheorem3.rightConjugate_le_rightConjugate hx n
          rwa [(rightConjugate_eq_self_iff E n).mpr hn] at h1
        refine hcompL (x * n) hxn (Subgroup.mem_inf.mpr ⟨?_, ?_⟩)
        · rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, mem_rightConjugate_iff]
          have h1 := (mem_rightConjugate_iff A x a).mp ha.1
          convert h1 using 1
          group
        · rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
          exact mul_mem (mul_mem (inv_mem hn) ha.2) hn
    exact (rightConjugate_eq_self_iff L n).mp
      (Subgroup.eq_of_le_of_card_ge hle (by rw [rightConjugate_card]))
  have hcommL : ⁅L, L⁆ ≤ L := Subgroup.commutator_le.mpr fun a ha b hb => by
    rw [commutatorElement_def]
    exact L.mul_mem (L.mul_mem (L.mul_mem ha hb) (L.inv_mem ha)) (L.inv_mem hb)
  have hperf : ⁅L, L⁆ ⊔ centralizer (E : Set G) = L := by
    refine le_antisymm (sup_le hcommL hCL) (sup_le le_sup_right (iSup₂_le fun x hx => ?_))
    exact (radical_at_point hE16 h11 hF hL hRA hx).1.trans
      (sup_le_sup_right (Subgroup.commutator_mono (hcompL x hx) (hcompL x hx)) _)
  have hLalt : ∀ x (hx : x ∈ L), pointsAction R E ⟨x, hLN hx⟩ ∈
      alternatingGroup ↥(pointsIn R E) := by
    set ψ : ↥(normalizer (E : Set G)) →* ℤˣ := Equiv.Perm.sign.comp (pointsAction R E)
    have hL' : L.subgroupOf (normalizer (E : Set G)) ≤ ψ.ker := by
      have heq : L.subgroupOf (normalizer (E : Set G)) =
          ⁅L.subgroupOf (normalizer (E : Set G)), L.subgroupOf (normalizer (E : Set G))⁆ ⊔
            (centralizer (E : Set G)).subgroupOf (normalizer (E : Set G)) := by
        conv_lhs => rw [← hperf]
        rw [Subgroup.subgroupOf_sup (hcommL.trans hLN) hCN, commutator_subgroupOf hLN]
      rw [heq]
      refine sup_le ((Subgroup.commutator_mono le_top le_top).trans
        (Abelianization.commutator_subset_ker ψ)) fun c hc => ?_
      rw [MonoidHom.mem_ker, MonoidHom.coe_comp, Function.comp_apply,
        pointsAction_eq_one_of_mem_centralizer hc, map_one]
    intro x hx
    have h := hL' (show (⟨x, hLN hx⟩ : ↥(normalizer (E : Set G))) ∈
      L.subgroupOf (normalizer (E : Set G)) from hx)
    rw [MonoidHom.mem_ker] at h
    exact Equiv.Perm.mem_alternatingGroup.mpr h
  have hF' := frame_at_point hE16 hF hL hPV hPR
  have hL' := typeL34_rightConjugate g hL
  have h2' : Nat.card (pointsIn (rightConjugate R g) (E ⊓ F)) = 2 := by
    rw [pointsIn_rightConjugate]
    exact h2
  have hfixR : ∀ k : G, (∀ Q ∈ pointsIn R E, k ∈ normalizer (Q : Set G)) → ∀ r ∈ R, r ≠ 1 →
      k * r * k⁻¹ = r → k ∈ centralizer (E : Set G) := fun k hk r hr hr1 hkr =>
    mem_centralizer_of_fix_points hE16 h11 hF hL h2 hk hr hr1 hkr
  have hfixP : ∀ k : G, (∀ Q ∈ pointsIn R E, k ∈ normalizer (Q : Set G)) →
      ∀ r ∈ rightConjugate R g, r ≠ 1 → k * r * k⁻¹ = r → k ∈ centralizer (E : Set G) :=
    fun k hk r hr hr1 hkr => mem_centralizer_of_fix_points hE16 h11 hF' hL' h2'
      (by rwa [pointsIn_rightConjugate]) hr hr1 hkr
  have hne1 : ∀ {X : Subgroup G}, Nat.card X = 4 → ∃ r ∈ X, r ≠ 1 := by
    intro X hX
    by_contra h
    push Not at h
    have : X = ⊥ := (Subgroup.eq_bot_iff_forall X).mpr h
    rw [this, Subgroup.card_bot] at hX
    omega
  have hP4 : Nat.card (rightConjugate R g) = 4 := by rw [rightConjugate_card, hF.cardR]
  set pR : ↥(pointsIn R E) := ⟨R, hR⟩
  set pP : ↥(pointsIn R E) := ⟨rightConjugate R g, hP⟩
  have hpRP : pR ≠ pP := fun h => hPR (congrArg Subtype.val h).symm
  have hstabR : ∀ σ ∈ alternatingGroup ↥(pointsIn R E), σ pR = pR →
      ∃ a, ∃ ha : a ∈ A ⊓ normalizer (E : Set G), pointsAction R E ⟨a, ha.2⟩ = σ := by
    intro σ hσ hσR
    have hidx : (A ⊓ normalizer (E : Set G) ⊓ centralizer (E : Set G)).relIndex
        (A ⊓ normalizer (E : Set G)) = 60 := by
      have h := (radical_at_point hE16 h11 hF hL hRA
        (by rw [rightConjugate_one]; exact hF.R_le_E : rightConjugate R 1 ≤ E)).2
      rw [rightConjugate_one] at h
      rwa [inf_assoc, inf_eq_right.mpr hCN]
    obtain ⟨a, ha, hσa⟩ := exists_pointsAction_eq R E h6 (X := A ⊓ normalizer (E : Set G))
      inf_le_right pR (fun a ha => Subtype.ext (by
        rw [coe_pointsAction_apply]
        exact (rightConjugate_eq_self_iff R _).mpr (Subgroup.centralizer_le_normalizer _
          (mem_centralizer_iff.mpr fun r hr =>
            (mem_centralizer_iff.mp (hF.sylowR.le hr) _ (inv_mem ha.1)).symm))))
      (fun a ha => hLalt a (hAL ha))
      (fun a ha h1 => by
        obtain ⟨r, hr, hr1⟩ := hne1 hF.cardR
        refine hfixR a (mem_normalizer_of_pointsAction_eq_one h1) r hr hr1 ?_
        rw [mem_centralizer_iff.mp (hF.sylowR.le hr) a ha.1, mul_inv_cancel_right])
      hidx hσ hσR
    exact ⟨a, ha, hσa⟩
  have hstabP : ∀ σ ∈ alternatingGroup ↥(pointsIn R E), σ pP = pP →
      ∃ a, ∃ ha : a ∈ rightConjugate A g ⊓ normalizer (E : Set G),
        pointsAction R E ⟨a, ha.2⟩ = σ := by
    intro σ hσ hσP
    have hPA : rightConjugate R g ≤ centralizer (rightConjugate A g : Set G) := hF'.sylowR.le
    have hidx : (rightConjugate A g ⊓ normalizer (E : Set G) ⊓ centralizer (E : Set G)).relIndex
        (rightConjugate A g ⊓ normalizer (E : Set G)) = 60 := by
      have h := (radical_at_point hE16 h11 hF hL hRA hP.1).2
      rwa [inf_assoc, inf_eq_right.mpr hCN]
    obtain ⟨a, ha, hσa⟩ := exists_pointsAction_eq R E h6
      (X := rightConjugate A g ⊓ normalizer (E : Set G)) inf_le_right pP
      (fun a ha => Subtype.ext (by
        rw [coe_pointsAction_apply]
        exact (rightConjugate_eq_self_iff _ _).mpr (Subgroup.centralizer_le_normalizer _
          (mem_centralizer_iff.mpr fun r hr =>
            (mem_centralizer_iff.mp (hPA hr) _ (inv_mem ha.1)).symm))))
      (fun a ha => hLalt a (hAgL ha))
      (fun a ha h1 => by
        obtain ⟨r, hr, hr1⟩ := hne1 hP4
        refine hfixP a (mem_normalizer_of_pointsAction_eq_one h1) r hr hr1 ?_
        rw [mem_centralizer_iff.mp (hPA hr) a ha.1, mul_inv_cancel_right])
      hidx hσ hσP
    exact ⟨a, ha, hσa⟩
  have hcard6 : Fintype.card ↥(pointsIn R E) = 6 := by rw [← Nat.card_eq_fintype_card, h6]
  have hfour : ∀ a b c : ↥(pointsIn R E), ∃ d, d ≠ a ∧ d ≠ b ∧ d ≠ c := by
    intro a b c
    by_contra h
    push Not at h
    have hsub : (Finset.univ : Finset ↥(pointsIn R E)) ⊆ {a, b, c} := fun d _ => by
      by_cases hda : d = a
      · simp [hda]
      by_cases hdb : d = b
      · simp [hdb]
      simp [h d hda hdb]
    have := Finset.card_le_card hsub
    rw [Finset.card_univ, hcard6] at this
    have h3 := Finset.card_le_three (a := a) (b := b) (c := c)
    omega
  have hswap : ∀ a b c : ↥(pointsIn R E), a ≠ b → b ≠ c →
      Equiv.swap a b * Equiv.swap b c ∈ alternatingGroup ↥(pointsIn R E) := fun a b c hab hbc =>
    Equiv.Perm.mul_mem_alternatingGroup_of_isSwap ⟨a, b, hab, rfl⟩ ⟨b, c, hbc, rfl⟩
  have hL1 : ∀ Q : ↥(pointsIn R E), Q ≠ pP →
      ∃ x, ∃ hx : x ∈ L, pointsAction R E ⟨x, hLN hx⟩ pR = Q := by
    intro Q hQP
    by_cases hQR : Q = pR
    · refine ⟨1, L.one_mem, ?_⟩
      rw [hQR]
      exact congrFun (congrArg DFunLike.coe (map_one (pointsAction R E))) pR
    obtain ⟨X, hXR, hXQ, hXP⟩ := hfour pR Q pP
    obtain ⟨a, ha, hσa⟩ := hstabP (Equiv.swap pR Q * Equiv.swap Q X)
      (hswap pR Q X (Ne.symm hQR) (Ne.symm hXQ)) (by
        rw [Equiv.Perm.mul_apply, Equiv.swap_apply_of_ne_of_ne hQP.symm hXP.symm,
          Equiv.swap_apply_of_ne_of_ne hpRP.symm hQP.symm])
    refine ⟨a, hAgL ha, ?_⟩
    rw [hσa, Equiv.Perm.mul_apply, Equiv.swap_apply_of_ne_of_ne (Ne.symm hQR) hXR.symm,
      Equiv.swap_apply_left]
  have hL2 : ∀ Q : ↥(pointsIn R E), ∃ x, ∃ hx : x ∈ L, pointsAction R E ⟨x, hLN hx⟩ pR = Q := by
    intro Q
    by_cases hQP : Q = pP
    · obtain ⟨X, hXR, hXP, -⟩ := hfour pR pP pP
      obtain ⟨x, hx, hxX⟩ := hL1 X hXP
      obtain ⟨Z, hZR, hZX, hZP⟩ := hfour pR X pP
      obtain ⟨a, ha, hσa⟩ := hstabR (Equiv.swap X pP * Equiv.swap pP Z)
        (hswap X pP Z hXP (Ne.symm hZP)) (by
          rw [Equiv.Perm.mul_apply, Equiv.swap_apply_of_ne_of_ne hpRP (Ne.symm hZR),
            Equiv.swap_apply_of_ne_of_ne (Ne.symm hXR) hpRP])
      refine ⟨a * x, L.mul_mem (hAL ha) hx, ?_⟩
      have e : (⟨a * x, hLN (L.mul_mem (hAL ha) hx)⟩ : ↥(normalizer (E : Set G))) =
          ⟨a, ha.2⟩ * ⟨x, hLN hx⟩ := rfl
      rw [e, map_mul, Equiv.Perm.mul_apply, hxX, hσa, Equiv.Perm.mul_apply,
        Equiv.swap_apply_of_ne_of_ne hXP hZX.symm, Equiv.swap_apply_left, hQP]
    · exact hL1 Q hQP
  have hM : (L.subgroupOf (normalizer (E : Set G))).map (pointsAction R E) =
      alternatingGroup ↥(pointsIn R E) := by
    refine le_antisymm (by rintro _ ⟨x, hx, rfl⟩; exact hLalt x hx) fun σ hσ => ?_
    obtain ⟨x, hx, hxσ⟩ := hL2 (σ pR)
    have hτ : (pointsAction R E ⟨x, hLN hx⟩)⁻¹ * σ ∈ alternatingGroup ↥(pointsIn R E) :=
      mul_mem (inv_mem (hLalt x hx)) hσ
    obtain ⟨a, ha, hσa⟩ := hstabR _ hτ (by
      rw [Equiv.Perm.mul_apply, ← hxσ]
      exact Equiv.symm_apply_apply _ _)
    refine ⟨⟨x, hLN hx⟩ * ⟨a, ha.2⟩, L.mul_mem hx (hAL ha), ?_⟩
    rw [map_mul, hσa, mul_inv_cancel_left]
  obtain ⟨y, hyA, hyE, hyR, hyfree⟩ := exists_torus_conj hE16 h11 hF hL heven h2
  have hyL : y ∈ L := hAgL ⟨hyA, hyE⟩
  obtain ⟨a, ha, hay⟩ := hstabR _ (hLalt y hyL) (Subtype.ext (by
    rw [coe_pointsAction_apply]
    exact (rightConjugate_eq_self_iff R _).mpr (inv_mem hyR)))
  have hkL : y * a⁻¹ ∈ L := L.mul_mem hyL (L.inv_mem (hAL ha))
  have hkρ : pointsAction R E ⟨y * a⁻¹, hLN hkL⟩ = 1 := by
    have e : (⟨y * a⁻¹, hLN hkL⟩ : ↥(normalizer (E : Set G))) =
        ⟨y, hyE⟩ * (⟨a, ha.2⟩)⁻¹ := rfl
    rw [e, map_mul, map_inv, ← hay, mul_inv_cancel]
  have hkC : y * a⁻¹ ∉ centralizer (E : Set G) := by
    intro hk
    obtain ⟨r, hr, hr1⟩ := hne1 hF.cardR
    apply hyfree r hr hr1
    have h1 : y * a⁻¹ * r = r * (y * a⁻¹) := (mem_centralizer_iff.mp hk r (hF.R_le_E hr)).symm
    have h2 : a⁻¹ * r = r * a⁻¹ := (mem_centralizer_iff.mp (hF.sylowR.le hr) _ (inv_mem ha.1))
    calc y * r * y⁻¹ = y * a⁻¹ * (a * r * a⁻¹) * (y * a⁻¹)⁻¹ := by group
      _ = y * a⁻¹ * r * (y * a⁻¹)⁻¹ := by
          rw [show a * r * a⁻¹ = r by rw [mul_assoc, ← h2, ← mul_assoc, mul_inv_cancel, one_mul]]
      _ = r := by rw [h1, mul_inv_cancel_right]
  set K : Subgroup G := (pointsAction R E).ker.map (normalizer (E : Set G)).subtype with hKdef
  have hKpts : ∀ k ∈ K, ∀ Q ∈ pointsIn R E, k ∈ normalizer (Q : Set G) := by
    rintro _ ⟨k, hk, rfl⟩ Q hQ
    exact mem_normalizer_of_pointsAction_eq_one hk Q hQ
  have hCK : centralizer (E : Set G) ≤ K := fun c hc =>
    ⟨⟨c, hCN hc⟩, pointsAction_eq_one_of_mem_centralizer hc, rfl⟩
  have hk3 : (centralizer (E : Set G)).relIndex (L ⊓ K) = 3 := by
    have hH : L ⊓ K ≤ normalizer (R : Set G) := fun h hh => hKpts h hh.2 R hR
    have hCR : centralizer (E : Set G) ⊓ (L ⊓ K) ≤ centralizer (R : Set G) := fun c hc =>
      mem_centralizer_iff.mpr fun r hr => mem_centralizer_iff.mp hc.1 r (hF.R_le_E hr)
    rcases relIndex_eq_one_or_three hF.elemR hF.cardR hH hCR (fun h hh r hr hr1 hhr =>
        hfixR h (hKpts h hh.2) r hr hr1 hhr) with h1 | h3
    · exfalso
      rw [Subgroup.relIndex_eq_one] at h1
      exact hkC (h1 ⟨hkL, ⟨y * a⁻¹, hLN hkL⟩, hkρ, rfl⟩)
    · exact h3
  have hKL : K.relIndex L = 360 := by
    rw [← relIndex_subgroupOf hLN]
    have hK' : K.subgroupOf (normalizer (E : Set G)) = (pointsAction R E).ker :=
      comap_map_eq_self_of_injective (normalizer (E : Set G)).subtype_injective _
    rw [hK', Subgroup.relIndex_ker, hM]
    have : Nontrivial ↥(pointsIn R E) := Finite.one_lt_card_iff_nontrivial.mp (by omega)
    rw [nat_card_alternatingGroup, h6]
    rfl
  have hidx : (centralizer (E : Set G)).relIndex L = 1080 := by
    have h := Subgroup.relIndex_mul_relIndex (centralizer (E : Set G)) (L ⊓ K) L
      (le_inf hCL hCK) inf_le_left
    rw [hk3, inf_relIndex_left, hKL] at h
    omega
  exact ⟨L, hCL, hLN, hnormL, hperf, hidx⟩

end Main

end CFSG.ComponentClassification.AS81
