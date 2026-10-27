module

public import CFSG.LocalAnalysis.ComponentClassification.AS81Sec2F0
public import CFSG.LocalAnalysis.ComponentClassification.AS81Step16Count

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.ComponentClassification.AS81

open Subgroup CFSG.Open CFSG.ABGLocalTools CFSG.ComponentClassification.AschbacherTightEmbedding
open CFSG.ComponentClassification.RankTwoStandard

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem rightConjugate_mem_planes {E F V : Subgroup G} (hV : V ∈ planes E F) (k : G) :
    rightConjugate V k ∈ planes E F := by
  obtain ⟨h, rfl | rfl⟩ := hV
  · exact ⟨h * k, Or.inl (rightConjugate_mul E h k)⟩
  · exact ⟨h * k, Or.inr (rightConjugate_mul F h k)⟩

section Frame

variable {A R : Subgroup G} {g : G} {E F : Subgroup G}

theorem card_le_of_isElemAbelian_le_sup_sylow_frame (h11 : Step11) (hF : Frame G A A R g E F)
    (hL : TypeL34 (rankTwoQuot A)) (hodd : Odd (Nat.card (center ↥A))) {R' : Subgroup G}
    (hR' : IsSylowOf 2 R' (centralizer (A : Set G))) (hR'4 : Nat.card R' = 4) {D : Subgroup G}
    (hD : IsElemAbelian 2 D) (hDAR : D ≤ A ⊔ R') : Nat.card D ≤ 64 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hRA : R' ≤ centralizer (A : Set G) := hR'.le
  have hRA1 : R' ⊓ A = ⊥ := inf_eq_bot_of_odd_center hRA hR'.isPGroup hodd
  obtain ⟨c⟩ := l34Cover_of_base h11 hF.base hL
  have hker : Nat.card c.π.ker = 1 := by
    rw [card_ker_eq_card_inf c hR', hRA1, card_bot]
  obtain ⟨T, hT, hDT⟩ := AschbacherTheorem3.exists_isSylowOf_le
    ((isPGroup_two_of_isElemAbelian hD).to_le inf_le_left) (inf_le_right : D ⊓ A ≤ A)
  have h16 : Nat.card (D ⊓ A : Subgroup G) ≤ 16 := by
    have := card_le_of_isSylowOf c hT hDT (AS76b.IsElemAbelian.mono hD inf_le_left)
    rwa [hker, mul_one] at this
  have hDN : D ≤ normalizer (A : Set G) := hDAR.trans (sup_le_normalizer_left hRA)
  have h1 := card_sup_mul_card_inf (H := A) (R := D) hDN
  have h2 := card_sup_mul_card_inf (H := A) (R := R') (hRA.trans (centralizer_le_normalizer _))
  rw [inf_comm A R', hRA1, card_bot, mul_one, hR'4] at h2
  rw [inf_comm A D] at h1
  have h3 : Nat.card (A ⊔ D : Subgroup G) ≤ Nat.card (A ⊔ R' : Subgroup G) :=
    card_le_of_le (sup_le le_sup_left hDAR)
  have key : Nat.card A * Nat.card D ≤ Nat.card A * 64 := by
    rw [← h1]
    calc Nat.card (A ⊔ D : Subgroup G) * Nat.card (D ⊓ A : Subgroup G)
        ≤ Nat.card A * 4 * 16 := Nat.mul_le_mul (h3.trans h2.le) h16
      _ = Nat.card A * 64 := by ring
  exact Nat.le_of_mul_le_mul_left key Nat.card_pos

theorem mem_planes_of_le_sup_frame (hF : Frame G A A R g E F) (hL : TypeL34 (rankTwoQuot A))
    (hodd : Odd (Nat.card (center ↥A))) {D : Subgroup G} (hD : IsElemAbelian 2 D)
    (hD64 : Nat.card D = 64) (hRD : R ≤ D) (hDAR : D ≤ A ⊔ R) : D ∈ planes E F := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hR := hF.sylowR
  have hRA : R ≤ centralizer (A : Set G) := hR.le
  have hRA1 : R ⊓ A = ⊥ := inf_eq_bot_of_odd_center hRA hR.isPGroup hodd
  obtain ⟨-, hTsyl, -⟩ := sylow_sup_structure hRA hR.isPGroup hF.sylow
  have hDeq := eq_inf_sup_of_le_sup hRA hRD hDAR
  have hDA16 : Nat.card (D ⊓ A : Subgroup G) = 16 := by
    have := card_eq_card_inf_mul hRA hRD hDAR hRA1
    rw [hD64, hF.cardR] at this
    omega
  obtain ⟨a, haA, hle⟩ := AschbacherTheorem3.exists_rightConjugate_le_of_isSylowOf hTsyl
    ((isPGroup_two_of_isElemAbelian hD).to_le inf_le_left) inf_le_right
  have hEeq := eq_inf_sup_of_le_sup hRA hF.R_le_E hF.E_le
  have hFeq := eq_inf_sup_of_le_sup hRA hF.R_le_F hF.F_le
  have hne : E ⊓ A ≠ F ⊓ A := fun h => hF.ne (by rw [hEeq, hFeq, h])
  have hRa : rightConjugate R a = R := (rightConjugate_eq_self_iff R a).mpr
    (centralizer_le_normalizer _ (mem_centralizer_iff.mpr fun r hr =>
      (mem_centralizer_iff.mp (hRA hr) a haA).symm))
  have hconj : ∀ V : Subgroup G, rightConjugate (D ⊓ A) a = V ⊓ A → V = (V ⊓ A) ⊔ R →
      D = rightConjugate V a⁻¹ := fun V hV hVeq => by
    have hDa : rightConjugate D a = V := by
      conv_lhs => rw [hDeq]
      rw [rightConjugate_sup', hV, hRa, ← hVeq]
    rw [← hDa, rightConjugate_mul, mul_inv_cancel, rightConjugate_one]
  rcases Sec2.eq_or_eq_of_card_sixteen hF.quasisimple hL hodd hTsyl hle
    (AS76b.isElemAbelian_rightConjugate (AS76b.IsElemAbelian.mono hD inf_le_left) a)
    (by rw [rightConjugate_card, hDA16])
    (inf_le_inf_right A le_sup_left) (AS76b.IsElemAbelian.mono hF.elemE inf_le_left)
    (card_inf_left hF hodd)
    (inf_le_inf_right A le_sup_right) (AS76b.IsElemAbelian.mono hF.elemF inf_le_left)
    (card_inf_left hF.symm hodd) hne with h | h
  · exact ⟨a⁻¹, Or.inl (hconj E h hEeq)⟩
  · exact ⟨a⁻¹, Or.inr (hconj F h hFeq)⟩

theorem exists_rightConjugate_le_of_mem_inf_frame (h11 : Step11)
    {d : L34E16Cert} (hE16 : RankTwoL3Four.HypII.l34CheckWE16 d = true)
    (hF : Frame G A A R g E F) (hL : TypeL34 (rankTwoQuot A)) (hodd : Odd (Nat.card (center ↥A)))
    {D : Subgroup G} (hD : IsElemAbelian 2 D) (hD64 : Nat.card D = 64) {u : G} (huR : u ∈ R)
    (huD : u ∈ D) (hu1 : u ≠ 1) :
    ∃ c ∈ centralizer (A : Set G), rightConjugate R c ≤ D ∧ D ≤ A ⊔ rightConjugate R c := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hstd := hF.base.hyp.standard
  have hKte := AS76b.tightlyEmbedded_centralizer hstd
  have hNK := AS76b.normalizer_centralizer_eq hstd
  have hR := hF.sylowR
  set K := centralizer (A : Set G) with hK
  have hRA : R ≤ K := hR.le
  have hDc : ∀ a ∈ D, ∀ b ∈ D, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (hD.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  have hD2 := isPGroup_two_of_isElemAbelian hD
  have hDNK : D ≤ normalizer (K : Set G) := fun d hd =>
    RankTwoSporadic.mem_normalizer_of_commute_of_tightlyEmbedded hKte (hRA huR) hu1
      (hF.elemR.2 u huR) (hDc d hd u huD)
  have hDN : D ≤ normalizer (A : Set G) := hNK ▸ hDNK
  obtain ⟨e₀⟩ := PSL3Four.nonempty_equiv_of_stated (↥A ⧸ center ↥A) hL
  have hle := le_sup_centralizer_of_sixteen_le hE16 hF.quasisimple.1 e₀ hR hDN hD
    (by rw [hF.cardR, hD64])
  obtain ⟨X, hX, hDX⟩ := AschbacherTheorem3.exists_isSylowOf_le hD2 (le_sup_left : D ≤ D ⊔ K)
  have hR' : IsSylowOf 2 (X ⊓ K) K :=
    hX.inf_of_le_normalizer le_sup_right (sup_le hDNK le_normalizer)
  have hDR' : D ≤ normalizer ((X ⊓ K : Subgroup G) : Set G) := fun d hd =>
    inf_normalizer_le_normalizer_inf ⟨le_normalizer (hDX hd), hDNK hd⟩
  have hDAR' := le_sup_of_le_sup_normalizer hR' hD2 hDR' hle
  obtain ⟨c, hcK, hc⟩ := AschbacherTheorem3.exists_rightConjugate_eq_of_isSylowOf hR' hR
  set R' := X ⊓ K with hR'def
  have hR'e : IsElemAbelian 2 R' := hc ▸ AS76b.isElemAbelian_rightConjugate hF.elemR c
  have hR'4 : Nat.card R' = 4 := by rw [← hc, rightConjugate_card, hF.cardR]
  have hDC : D ≤ centralizer (R' : Set G) := hDAR'.trans (sup_le
    (le_centralizer_iff.mp hR'.le)
    fun r hr => mem_centralizer_iff.mpr fun s hs =>
      congrArg Subtype.val (hR'e.1.is_comm.comm ⟨s, hs⟩ ⟨r, hr⟩))
  have hDR'e := isElemAbelian_sup_of_le_centralizer hD hR'e hDC
  have hcard := card_le_of_isElemAbelian_le_sup_sylow_frame h11 hF hL hodd hR' hR'4 hDR'e
    (sup_le hDAR' le_sup_right)
  have hsup : D ⊔ R' = D := (eq_of_le_of_card_ge le_sup_left (by rw [hD64]; exact hcard)).symm
  exact ⟨c, hcK, hc ▸ hsup ▸ le_sup_right, hc ▸ hDAR'⟩

theorem mem_planes_of_mem_inf_frame (h11 : Step11)
    {d : L34E16Cert} (hE16 : RankTwoL3Four.HypII.l34CheckWE16 d = true)
    (hF : Frame G A A R g E F) (hL : TypeL34 (rankTwoQuot A)) (hodd : Odd (Nat.card (center ↥A)))
    {D : Subgroup G} (hD : IsElemAbelian 2 D) (hD64 : Nat.card D = 64) {u : G} (huR : u ∈ R)
    (huD : u ∈ D) (hu1 : u ≠ 1) : D ∈ planes E F := by
  obtain ⟨c, hcK, hR'D, hDAR'⟩ :=
    exists_rightConjugate_le_of_mem_inf_frame h11 hE16 hF hL hodd hD hD64 huR huD hu1
  have hAc : rightConjugate A c⁻¹ = A := (rightConjugate_eq_self_iff A c⁻¹).mpr
    (centralizer_le_normalizer _ (inv_mem hcK))
  have hR'c : rightConjugate (rightConjugate R c) c⁻¹ = R := by
    rw [rightConjugate_mul, mul_inv_cancel, rightConjugate_one]
  have hmem : rightConjugate D c⁻¹ ∈ planes E F := by
    refine mem_planes_of_le_sup_frame hF hL hodd (AS76b.isElemAbelian_rightConjugate hD c⁻¹)
      (by rw [rightConjugate_card, hD64]) ?_ ?_
    · rw [← hR'c]
      exact AschbacherTheorem3.rightConjugate_le_rightConjugate hR'D c⁻¹
    · have := AschbacherTheorem3.rightConjugate_le_rightConjugate hDAR' c⁻¹
      rwa [rightConjugate_sup', hAc, hR'c] at this
  have h := rightConjugate_mem_planes hmem c
  rwa [rightConjugate_mul, inv_mul_cancel, rightConjugate_one] at h

theorem mem_planes_of_mem_rightConjugate (h11 : Step11)
    {d : L34E16Cert} (hE16 : RankTwoL3Four.HypII.l34CheckWE16 d = true)
    (hF : Frame G A A R g E F) (hL : TypeL34 (rankTwoQuot A)) (hodd : Odd (Nat.card (center ↥A)))
    {D : Subgroup G} (hD : IsElemAbelian 2 D) (hD64 : Nat.card D = 64) {k u : G}
    (hu : u ∈ rightConjugate R k) (huD : u ∈ D) (hu1 : u ≠ 1) : D ∈ planes E F := by
  have hmem : rightConjugate D k⁻¹ ∈ planes E F := by
    refine mem_planes_of_mem_inf_frame h11 hE16 hF hL hodd
      (AS76b.isElemAbelian_rightConjugate hD k⁻¹) (by rw [rightConjugate_card, hD64])
      ((mem_rightConjugate_iff R k u).mp hu) ?_ (fun h => hu1 ?_)
    · rw [mem_rightConjugate_iff]
      simpa [mul_assoc] using huD
    · have := congrArg (fun z => k⁻¹ * z * k) h
      simpa [mul_assoc] using this
  have h := rightConjugate_mem_planes hmem k
  rwa [rightConjugate_mul, inv_mul_cancel, rightConjugate_one] at h

variable (h11 : Step11)
  {d : L34E16Cert} (hE16 : RankTwoL3Four.HypII.l34CheckWE16 d = true)
  (hF : Frame G A A R g E F) (hL : TypeL34 (rankTwoQuot A)) (hodd : Odd (Nat.card (center ↥A)))
  {x : G} (hx : x ∈ sec2P F) (hxS : x ∉ sec2S A R E F)

include h11 hE16 hF hL hodd hx hxS

theorem exists_mem_rightConjugate_inf_sec2P_not_mem
    (h4 : 4 ^ 4 ≤ Nat.card (conjClosure (E ⊓ A) (sec2P F))) :
    ∃ x' ∈ sec2P F, x' ∉ sec2S A R E F ∧
      ∃ y ∈ rightConjugate E x' ⊓ sec2P E, y ∉ rightConjugate A x' := by
  by_contra hno
  push Not at hno
  obtain ⟨hD, -⟩ := exists_pointsData h11 hE16 hF hL hodd
  have hSN := (sec2S_le_normalizer_left hF hL hodd).trans hD.normalizer_le_normalizer
  have hle : conjClosure (E ⊓ A) (sec2P F) ≤ sec2F0 A E x := by
    refine iSup_le fun p => ?_
    by_cases hpS : (p : G) ∈ sec2S A R E F
    · rw [(rightConjugate_eq_self_iff _ _).mpr (hSN hpS)]
      exact le_sup_left
    · have hsub : rightConjugate E p ⊓ sec2P E ≤ rightConjugate (E ⊓ A) p := fun z hz => by
        rw [mem_rightConjugate_iff]
        exact ⟨(mem_rightConjugate_iff E p z).mp hz.1,
          (mem_rightConjugate_iff A p z).mp (hno p p.2 hpS z hz)⟩
      have heq : rightConjugate E p ⊓ sec2P E = rightConjugate (E ⊓ A) p :=
        eq_of_le_of_card_ge hsub (by
          rw [rightConjugate_card, card_inf_left hF hodd,
            card_rightConjugate_inf h11 hE16 hF hL hodd p.2 hpS])
      rw [← heq, ← sec2F0_eq_sec2F0 h11 hE16 hF hL hodd hx hxS p.2 hpS]
      exact le_sup_right
  have h64 := card_le_of_le hle
  rw [card_sec2F0 h11 hE16 hF hL hodd hx hxS] at h64
  omega

theorem sec2F0_mem_planes (h4 : 4 ^ 4 ≤ Nat.card (conjClosure (E ⊓ A) (sec2P F))) :
    sec2F0 A E x ∈ planes E F := by
  obtain ⟨x', hx', hxS', y, hy, hyA⟩ :=
    exists_mem_rightConjugate_inf_sec2P_not_mem h11 hE16 hF hL hodd hx hxS h4
  obtain ⟨hD, -⟩ := exists_pointsData h11 hE16 hF hL hodd
  have hyE : x' * y * x'⁻¹ ∈ E := (mem_rightConjugate_iff E x' y).mp hy.1
  obtain ⟨Q, hQ, hyQ⟩ := hD.cover _ hyE fun h => hyA ((mem_rightConjugate_iff A x' y).mpr h.2)
  obtain ⟨-, k, rfl⟩ := hQ
  have hyU : y ∈ rightConjugate R (k * x') := by
    rw [← rightConjugate_mul]
    exact (mem_rightConjugate_iff _ x' y).mpr hyQ
  have hyF : y ∈ sec2F0 A E x := by
    rw [← sec2F0_eq_sec2F0 h11 hE16 hF hL hodd hx hxS hx' hxS']
    exact mem_sup_right hy
  exact mem_planes_of_mem_rightConjugate h11 hE16 hF hL hodd
    (isElemAbelian_sec2F0 (x := x) h11 hE16 hF hL hodd)
    (card_sec2F0 h11 hE16 hF hL hodd hx hxS) hyU hyF
    fun h => hyA (h ▸ (rightConjugate A x').one_mem)

end Frame

end CFSG.ComponentClassification.AS81
