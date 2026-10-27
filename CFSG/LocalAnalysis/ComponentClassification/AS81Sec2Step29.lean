module

public import CFSG.LocalAnalysis.ComponentClassification.AS81Sec2Step23
public import CFSG.LocalAnalysis.ComponentClassification.AS81Sec2Step29Pts

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.ComponentClassification.AS81

open Subgroup CFSG.Open CFSG.ABGLocalTools CFSG.ComponentClassification.AschbacherTightEmbedding
open CFSG.ComponentClassification.RankTwoStandard

variable {G : Type} [Group G] [Finite G]

section Frame

variable {A R : Subgroup G} {g : G} {E F : Subgroup G}

theorem mem_of_mem_normalizer_inf_centralizer (hF : Frame G A A R g E F)
    (hL : TypeL34 (rankTwoQuot A)) (hodd : Odd (Nat.card (center ↥A))) {q : G}
    (hqR : q ∈ normalizer (R : Set G)) (hqC : q ∈ centralizer ((E ⊓ A : Subgroup G) : Set G))
    {m : ℕ} (hq : q ^ 2 ^ m = 1) : q ∈ E := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hstd := hF.base.hyp.standard
  have hKte := AS76b.tightlyEmbedded_centralizer hstd
  have hNK := AS76b.normalizer_centralizer_eq hstd
  have hR := hF.sylowR
  have hRA : R ≤ centralizer (A : Set G) := hR.le
  have hqK : q ∈ normalizer (centralizer (A : Set G) : Set G) := by
    by_contra hqK
    have hodd' := hKte.2 q hqK
    have hle : R ≤ centralizer (A : Set G) ⊓ rightConjugate (centralizer (A : Set G)) q := by
      refine le_inf hRA fun r hr => ?_
      rw [mem_rightConjugate_iff]
      exact hRA ((mem_normalizer_iff.mp hqR r).mp hr)
    have hdvd := Subgroup.card_dvd_of_le hle
    rw [hF.cardR] at hdvd
    exact (Nat.not_even_iff_odd.mpr hodd')
      (even_iff_two_dvd.mpr ((by norm_num : 2 ∣ 4).trans hdvd))
  have hqA : q ∈ normalizer (A : Set G) := hNK ▸ hqK
  have hHe : IsElemAbelian 2 (E ⊓ A) := AS76b.IsElemAbelian.mono hF.elemE inf_le_left
  obtain ⟨h, hh, hd⟩ := exists_mem_inv_mul_mem_centralizer hstd.1 hL hodd inf_le_right hHe
    (card_inf_left hF hodd) hqA fun h hh =>
      mul_inv_eq_iff_eq_mul.mpr (mem_centralizer_iff.mp hqC h hh).symm
  rcases m with _ | m
  · rw [pow_zero, pow_one] at hq
    rw [hq]
    exact E.one_mem
  have hhc : Commute h⁻¹ q :=
    (show Commute h q from mem_centralizer_iff.mp hqC h hh).inv_left
  have hh2 : h⁻¹ ^ 2 ^ (m + 1) = 1 := by
    have : h⁻¹ ^ 2 = 1 := by rw [inv_pow, hHe.2 h hh, inv_one]
    rw [pow_succ, pow_mul', this, one_pow]
  have hd2 : (h⁻¹ * q) ^ 2 ^ (m + 1) = 1 := by rw [hhc.mul_pow, hh2, hq, one_mul]
  have hdR : h⁻¹ * q ∈ normalizer (R : Set G) :=
    mul_mem (centralizer_le_normalizer _ (mem_centralizer_iff.mpr fun r hr =>
      (mem_centralizer_iff.mp (hRA hr) h⁻¹ (A.inv_mem hh.2)).symm)) hqR
  have hQ : IsPGroup 2 ↥(R ⊔ zpowers (h⁻¹ * q)) :=
    hR.isPGroup.to_sup_of_normal_left' (AS76b.isPGroup_zpowers_of_pow_eq_one hd2)
      (zpowers_le.mpr hdR)
  have heq := hR.eq_of_le le_sup_left (sup_le hRA (zpowers_le.mpr hd)) hQ
  have hdR' : h⁻¹ * q ∈ R := by
    have := (le_sup_right : zpowers (h⁻¹ * q) ≤ R ⊔ zpowers (h⁻¹ * q)) (mem_zpowers _)
    rwa [heq] at this
  have : q = h * (h⁻¹ * q) := by group
  rw [this]
  exact E.mul_mem hh.1 (hF.R_le_E hdR')

variable (h11 : Step11)
  {d : L34E16Cert} (hE16 : RankTwoL3Four.HypII.l34CheckWE16 d = true)
  (hF : Frame G A A R g E F) (hL : TypeL34 (rankTwoQuot A)) (hodd : Odd (Nat.card (center ↥A)))

include h11 hE16 hF hL hodd

theorem mem_sec2P_of_pow_two {q : G} (hqE : q ∈ normalizer (E : Set G))
    (hqC : q ∈ centralizer ((E ⊓ A : Subgroup G) : Set G)) {m : ℕ} (hq : q ^ 2 ^ m = 1) :
    q ∈ sec2P E := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hD, -⟩ := exists_pointsData h11 hE16 hF hL hodd
  have htr := exists_mem_sec2P_rightConjugate_eq h11 hE16 hF hL hodd
  obtain ⟨p, hp, hpq⟩ := htr _ (rightConjugate_mem_pointsIn hD.self_mem hqE)
  have hqpR : q * p⁻¹ ∈ normalizer (R : Set G) := by
    rw [← rightConjugate_eq_self_iff, ← rightConjugate_mul, ← hpq, rightConjugate_mul,
      mul_inv_cancel, rightConjugate_one]
  have hqP : q ∈ normalizer (sec2P E : Set G) := Sec2.normalizer_le_normalizer_sec2P E hqE
  have hQ2 : IsPGroup 2 ↥(sec2P E ⊔ zpowers q) :=
    (Sec2.isPGroup_sec2P E).to_sup_of_normal_left' (AS76b.isPGroup_zpowers_of_pow_eq_one hq)
      (zpowers_le.mpr hqP)
  obtain ⟨k, hk⟩ := hQ2 ⟨q * p⁻¹, mul_mem (mem_sup_right (mem_zpowers q))
    (mem_sup_left (inv_mem hp))⟩
  have hk' : (q * p⁻¹) ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
  have hPC := sec2P_le_centralizer_inf h11 hE16 hF hL hodd
  have hqpC : q * p⁻¹ ∈ centralizer ((E ⊓ A : Subgroup G) : Set G) :=
    mul_mem hqC (inv_mem (hPC hp))
  have h1 := mem_of_mem_normalizer_inf_centralizer hF hL hodd hqpR hqpC hk'
  have : q = (q * p⁻¹) * p := by group
  rw [this]
  exact mul_mem (le_sec2P_of_frame hF h1) hp

theorem rightConjugate_inf_eq_of_points {W : Subgroup G} (hDW : PointsData R W (W ⊓ A))
    (hW16 : Nat.card (W ⊓ A : Subgroup G) = 16) {j : G} (hjP : rightConjugate W j ≤ sec2P E)
    (hEAW : E ⊓ A ≤ rightConjugate W j) : rightConjugate (W ⊓ A) j = E ⊓ A := by
  refine (eq_of_le_of_card_ge (fun e he => ?_)
    (by rw [rightConjugate_card, hW16, card_inf_left hF hodd])).symm
  have heW : j * e * j⁻¹ ∈ W := (mem_rightConjugate_iff W j e).mp (hEAW he)
  rw [mem_rightConjugate_iff]
  by_contra hnot
  obtain ⟨Q, hQ, heQ⟩ := hDW.cover _ heW hnot
  obtain ⟨hQW, q, rfl⟩ := hQ
  have hle : rightConjugate R (q * j) ≤ sec2P E := by
    rw [← rightConjugate_mul]
    exact (AschbacherTheorem3.rightConjugate_le_rightConjugate hQW j).trans hjP
  have hmem : e ∈ rightConjugate R (q * j) ⊓ (E ⊓ A) := by
    refine Subgroup.mem_inf.mpr ⟨?_, he⟩
    rw [← rightConjugate_mul, mem_rightConjugate_iff]
    exact heQ
  rw [rightConjugate_inf_inf_eq_bot h11 hE16 hF hL hodd hle, mem_bot] at hmem
  rw [hmem, mul_one, mul_inv_cancel] at hnot
  exact hnot (Subgroup.one_mem _)

theorem sec2P_le_rightConjugate_of_points {W : Subgroup G}
    (hmem : ∀ {q : G}, q ∈ normalizer (W : Set G) →
      q ∈ centralizer ((W ⊓ A : Subgroup G) : Set G) → ∀ {m : ℕ}, q ^ 2 ^ m = 1 → q ∈ sec2P W)
    {j : G} (hEAj : rightConjugate (W ⊓ A) j = E ⊓ A)
    (hPN : sec2P E ≤ normalizer (rightConjugate W j : Set G)) :
    sec2P E ≤ rightConjugate (sec2P W) j := by
  have hPC := sec2P_le_centralizer_inf h11 hE16 hF hL hodd
  intro q hq
  rw [mem_rightConjugate_iff]
  obtain ⟨m, hm⟩ := Sec2.isPGroup_sec2P E ⟨q, hq⟩
  have hm' : (j * q * j⁻¹) ^ 2 ^ m = 1 := by
    have : q ^ 2 ^ m = 1 := by simpa using congrArg Subtype.val hm
    rw [conj_pow, this, mul_one, mul_inv_cancel]
  refine hmem ?_ ?_ hm'
  · have hqN := hPN hq
    rw [← AschbacherTheorem3.rightConjugate_normalizer, mem_rightConjugate_iff] at hqN
    exact hqN
  · rw [mem_centralizer_iff]
    intro a ha
    have ha' : j⁻¹ * a * j ∈ E ⊓ A := by
      rw [← hEAj, mem_rightConjugate_iff]
      simpa [mul_assoc] using ha
    have hc := mem_centralizer_iff.mp (hPC hq) _ ha'
    calc a * (j * q * j⁻¹) = j * ((j⁻¹ * a * j) * q) * j⁻¹ := by group
      _ = j * (q * (j⁻¹ * a * j)) * j⁻¹ := by rw [hc]
      _ = j * q * j⁻¹ * a := by group

section Plane

variable {x : G} (hx : x ∈ sec2P F) (hxS : x ∉ sec2S A R E F)

include hx hxS

theorem rightConjugate_eq_of_mem_normalizer_inf_centralizer {n : G}
    (hnE : n ∈ normalizer (E : Set G)) (hnC : n ∈ centralizer ((E ⊓ A : Subgroup G) : Set G))
    {V : Subgroup G} (hV : V ∈ planes E F) (hVP : V ≤ sec2P E) : rightConjugate V n = V := by
  rcases eq_or_exists_of_mem_planes h11 hE16 hF hL hodd hx hxS hV hVP with rfl | ⟨m, hm, rfl⟩
  · exact (rightConjugate_eq_self_iff _ n).mpr hnE
  obtain ⟨hD, -⟩ := exists_pointsData h11 hE16 hF hL hodd
  have htr := exists_mem_sec2P_rightConjugate_eq h11 hE16 hF hL hodd
  obtain ⟨p, hp, hpn⟩ := htr _ (rightConjugate_mem_pointsIn hD.self_mem hnE)
  obtain ⟨n₁, hn₁⟩ : ∃ n₁, n₁ = n * p⁻¹ := ⟨_, rfl⟩
  have hn : n = n₁ * p := by rw [hn₁]; group
  have hn₁R : n₁ ∈ normalizer (R : Set G) := by
    rw [hn₁, ← rightConjugate_eq_self_iff, ← rightConjugate_mul, ← hpn, rightConjugate_mul,
      mul_inv_cancel, rightConjugate_one]
  have hn₁E : n₁ ∈ normalizer (E : Set G) := hn₁ ▸ mul_mem hnE (inv_mem (Sec2.sec2P_le E hp))
  have hPC := sec2P_le_centralizer_inf h11 hE16 hF hL hodd
  have hn₁C : n₁ ∈ centralizer ((E ⊓ A : Subgroup G) : Set G) :=
    hn₁ ▸ mul_mem hnC (inv_mem (hPC hp))
  obtain ⟨hmE, hmR⟩ := mem_normalizer_of_mem_inf_normalizer hF hm
  have hZm : rightConjugate (sec2Z A E F) m ≤ E ⊓ A := by
    have h1 : sec2Z A E F ≤ E ⊓ A := by
      rw [hF.sec2Z_eq]
      exact le_inf (inf_le_left.trans inf_le_left) inf_le_right
    have h2 := AschbacherTheorem3.rightConjugate_le_rightConjugate h1 m
    rwa [(rightConjugate_eq_self_iff _ m).mpr hm.2] at h2
  have hZn : rightConjugate (rightConjugate (sec2Z A E F) m) n₁ =
      rightConjugate (sec2Z A E F) m :=
    (rightConjugate_eq_self_iff _ n₁).mpr (centralizer_le_normalizer _
      (mem_centralizer_iff.mpr fun z hz => mem_centralizer_iff.mp hn₁C z (hZm hz)))
  have hLine : rightConjugate (E ⊓ F) (m * n₁) = rightConjugate (E ⊓ F) m := by
    rw [← rightConjugate_mul, ← hF.sup_sec2Z, rightConjugate_sup', rightConjugate_sup', hZn,
      (rightConjugate_eq_self_iff R m).mpr hmR, (rightConjugate_eq_self_iff R n₁).mpr hn₁R]
  have hCC : rightConjugate (centralizerMod (sec2P E) (R ⊔ sec2Z A E F) (sec2Z A E F))
      (m * n₁) =
      rightConjugate (centralizerMod (sec2P E) (R ⊔ sec2Z A E F) (sec2Z A E F)) m := by
    ext q
    rw [mem_rightConjugate_centralizerMod_iff h11 hE16 hF hL hodd (mul_mem hmE hn₁E)
      (mul_mem hmR hn₁R), mem_rightConjugate_centralizerMod_iff h11 hE16 hF hL hodd hmE hmR,
      hLine]
  have hF0C : sec2F0 A E x ≤ centralizerMod (sec2P E) (R ⊔ sec2Z A E F) (sec2Z A E F) := by
    rw [centralizerMod_eq_sup_sec2F0 h11 hE16 hF hL hodd hx hxS]
    exact le_sup_right
  have hle : rightConjugate (sec2F0 A E x) (m * n₁) ≤
      rightConjugate (centralizerMod (sec2P E) (R ⊔ sec2Z A E F) (sec2Z A E F)) m :=
    hCC ▸ AschbacherTheorem3.rightConjugate_le_rightConjugate hF0C (m * n₁)
  have hF0e := isElemAbelian_sec2F0 (x := x) h11 hE16 hF hL hodd
  have hF064 := card_sec2F0 h11 hE16 hF hL hodd hx hxS
  rcases le_or_le_of_le_rightConjugate h11 hE16 hF hL hodd hx hxS hmE
      (AS76b.isElemAbelian_rightConjugate hF0e _) hle with h | h
  · exact absurd (eq_of_le_of_card_ge h (by rw [hF.cardE, rightConjugate_card, hF064]))
      (rightConjugate_sec2F0_ne h11 hE16 hF hL hodd hx hxS (mul_mem hmE hn₁E))
  have heq : rightConjugate (sec2F0 A E x) (m * n₁) = rightConjugate (sec2F0 A E x) m :=
    eq_of_le_of_card_ge h (by rw [rightConjugate_card, rightConjugate_card])
  rw [hn, ← rightConjugate_mul, rightConjugate_mul (sec2F0 A E x) m n₁, heq]
  apply (rightConjugate_eq_self_iff _ p).mpr
  rw [← AschbacherTheorem3.rightConjugate_normalizer, mem_rightConjugate_iff]
  have hmP := Sec2.normalizer_le_normalizer_sec2P E hmE
  exact sec2P_le_normalizer_sec2F0 h11 hE16 hF hL hodd hx hxS
    ((mem_normalizer_iff.mp hmP p).mp hp)

theorem exists_mem_normalizer_rightConjugate_eq_of_ne {V W : Subgroup G} (hV : V ∈ planes E F)
    (hVP : V ≤ sec2P E) (hVE : V ≠ E) (hW : W ∈ planes E F) (hWP : W ≤ sec2P E) (hWE : W ≠ E) :
    ∃ h ∈ normalizer (E : Set G), rightConjugate V h = W := by
  rcases eq_or_exists_of_mem_planes h11 hE16 hF hL hodd hx hxS hV hVP with h | ⟨m, hm, rfl⟩
  · exact absurd h hVE
  rcases eq_or_exists_of_mem_planes h11 hE16 hF hL hodd hx hxS hW hWP with h | ⟨m', hm', rfl⟩
  · exact absurd h hWE
  obtain ⟨hmE, -⟩ := mem_normalizer_of_mem_inf_normalizer hF hm
  obtain ⟨hm'E, -⟩ := mem_normalizer_of_mem_inf_normalizer hF hm'
  exact ⟨m⁻¹ * m', mul_mem (inv_mem hmE) hm'E, by rw [rightConjugate_mul, mul_inv_cancel_left]⟩

end Plane

section Sylow

variable {x : G} (hx : x ∈ sec2P F) (hxS : x ∉ sec2S A R E F)
  (h4 : 4 ^ 4 ≤ Nat.card (conjClosure (E ⊓ A) (sec2P F)))

include hx hxS h4

theorem isSylowOf_sec2P_centralizer :
    IsSylowOf 2 (sec2P E) (centralizer ((E ⊓ A : Subgroup G) : Set G)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hPC := sec2P_le_centralizer_inf h11 hE16 hF hL hodd
  have hP2 := Sec2.isPGroup_sec2P E
  obtain ⟨S₀, hS₀, hPS₀⟩ := AschbacherTheorem3.exists_isSylowOf_le hP2 hPC
  by_contra hns
  have hne : sec2P E ≠ S₀ := fun h => hns (h ▸ hS₀)
  have hlt : (sec2P E).subgroupOf S₀ < ⊤ := by
    refine lt_of_le_of_ne le_top fun h => hne (le_antisymm hPS₀ fun s hs => ?_)
    have : (⟨s, hs⟩ : ↥S₀) ∈ (sec2P E).subgroupOf S₀ := h ▸ mem_top _
    exact this
  have hS₀2 : IsPGroup 2 S₀ := hS₀.isPGroup
  have : Group.IsNilpotent ↥S₀ := hS₀2.isNilpotent
  obtain ⟨⟨g, hgS⟩, hgN, hgP⟩ :=
    IsConcreteLE.exists_of_lt (Group.normalizerCondition_of_isNilpotent (G := ↥S₀) _ hlt)
  have hgP' : g ∉ sec2P E := fun h => hgP (mem_subgroupOf.mpr h)
  have hgNP : g ∈ normalizer (sec2P E : Set G) := by
    refine Sec2.mem_normalizer_of_forall_conj_mem fun y hy => ?_
    have h1 := (mem_normalizer_iff.mp hgN ⟨y, hPS₀ hy⟩).mp (mem_subgroupOf.mpr hy)
    rw [mem_subgroupOf] at h1
    simpa using h1
  have hgC : g ∈ centralizer ((E ⊓ A : Subgroup G) : Set G) := hS₀.le hgS
  obtain ⟨k, hk⟩ := hS₀2 ⟨g, hgS⟩
  have hk' : g ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
  have hgE : g ∉ normalizer (E : Set G) := fun h =>
    hgP' (mem_sec2P_of_pow_two h11 hE16 hF hL hodd h hgC hk')
  obtain ⟨hD, -⟩ := exists_pointsData h11 hE16 hF hL hodd
  have hNEH := hD.normalizer_le_normalizer
  set Ps := {V | V ∈ planes E F ∧ V ≤ sec2P E} with hPs
  set I := normalizer (sec2P E : Set G) ⊓ centralizer ((E ⊓ A : Subgroup G) : Set G) with hIdef
  have hstab : ∀ n ∈ normalizer (sec2P E : Set G), ∀ V ∈ Ps, rightConjugate V n ∈ Ps :=
    fun n hn V hV => ⟨rightConjugate_mem_planes hV.1 n, by
      rw [← (rightConjugate_eq_self_iff _ n).mpr hn]
      exact AschbacherTheorem3.rightConjugate_le_rightConjugate hV.2 n⟩
  have hIstab : I ≤ Sec2.conjSetStab Ps := Sec2.le_conjSetStab fun n hn => hstab n hn.1
  set ρ := Sec2.conjPermHom hIstab with hρ
  have hρapp : ∀ (z : ↥I) (V : ↥Ps),
      ((ρ z V : ↥Ps) : Subgroup G) = rightConjugate V (z : G)⁻¹ :=
    fun z V => Sec2.conjPermHom_apply hIstab z V
  have hconjI : ∀ h ∈ normalizer (E : Set G), ∀ k ∈ I, h⁻¹ * k * h ∈ I := by
    intro h hh k hk
    have hhP := Sec2.normalizer_le_normalizer_sec2P E hh
    refine Subgroup.mem_inf.mpr ⟨mul_mem (mul_mem (inv_mem hhP) (Subgroup.mem_inf.mp hk).1) hhP,
      mem_centralizer_iff.mpr fun a ha => ?_⟩
    have ha' : h * a * h⁻¹ ∈ E ⊓ A := (mem_normalizer_iff.mp (hNEH hh) a).mp ha
    have hc := mem_centralizer_iff.mp (Subgroup.mem_inf.mp hk).2 _ ha'
    calc a * (h⁻¹ * k * h) = h⁻¹ * ((h * a * h⁻¹) * k) * h := by group
      _ = h⁻¹ * (k * (h * a * h⁻¹)) * h := by rw [hc]
      _ = h⁻¹ * k * h * a := by group
  have hρ1 : ∀ z : ↥I, ρ z = 1 ↔ ∀ V ∈ Ps, rightConjugate V (z : G)⁻¹ = V := by
    intro z
    constructor
    · intro h V hV
      have := congrArg (fun σ : Equiv.Perm ↥Ps => ((σ ⟨V, hV⟩ : ↥Ps) : Subgroup G)) h
      simpa [hρapp] using this
    · intro h
      refine Equiv.ext fun V => Subtype.ext ?_
      rw [hρapp]
      exact h V V.2
  have hE : E ∈ Ps := ⟨⟨1, Or.inl (rightConjugate_one E).symm⟩, le_sec2P_of_frame hF⟩
  set e : ↥Ps := ⟨E, hE⟩ with he
  have hfixE : ∀ z : ↥I, ρ z e = e → ρ z = 1 := by
    intro z hz
    have hz' : rightConjugate E (z : G)⁻¹ = E := by
      have := congrArg Subtype.val hz
      rwa [hρapp] at this
    have hzE : (z : G)⁻¹ ∈ normalizer (E : Set G) := (rightConjugate_eq_self_iff E _).mp hz'
    rw [hρ1]
    intro V hV
    exact rightConjugate_eq_of_mem_normalizer_inf_centralizer h11 hE16 hF hL hodd hx hxS hzE
      (inv_mem z.2.2) hV.1 hV.2
  have hreg : ∀ z w : ↥I, ρ z e = ρ w e → ρ z = ρ w := by
    intro z w hzw
    have h1 : ρ (w⁻¹ * z) e = e := by
      rw [map_mul, map_inv, Equiv.Perm.mul_apply, hzw]
      exact Equiv.symm_apply_apply (ρ w) e
    have h2 := hfixE _ h1
    rw [map_mul, map_inv, inv_mul_eq_one] at h2
    exact h2.symm
  have hgI : g ∈ I := ⟨hgNP, hgC⟩
  have hV₀ : rightConjugate E g ∈ Ps := hstab g hgNP E hE
  have hV₀E : rightConjugate E g ≠ E := fun h => hgE ((rightConjugate_eq_self_iff E g).mp h)
  have htrans : ∀ V : ↥Ps, ∃ z : ↥I, ρ z e = V := by
    intro V
    by_cases hVE : (V : Subgroup G) = E
    · exact ⟨1, Subtype.ext (by rw [map_one, Equiv.Perm.one_apply]; exact hVE.symm)⟩
    obtain ⟨h, hh, hhV⟩ := exists_mem_normalizer_rightConjugate_eq_of_ne h11 hE16 hF hL hodd hx
      hxS hV₀.1 hV₀.2 hV₀E V.2.1 V.2.2 hVE
    refine ⟨⟨h⁻¹ * g⁻¹ * h, hconjI h hh g⁻¹ (inv_mem hgI)⟩, Subtype.ext ?_⟩
    rw [hρapp]
    have hEh : rightConjugate E h⁻¹ = E := (rightConjugate_eq_self_iff E h⁻¹).mpr (inv_mem hh)
    show rightConjugate E (h⁻¹ * g⁻¹ * h)⁻¹ = V
    rw [show (h⁻¹ * g⁻¹ * h)⁻¹ = h⁻¹ * g * h by group, ← rightConjugate_mul,
      ← rightConjugate_mul, hEh, hhV]
  have hcard6 : Nat.card ρ.range = 6 := by
    rw [← ncard_planes_sec2P h11 hE16 hF hL hodd hx hxS h4]
    refine Nat.card_congr (Equiv.ofBijective (fun σ : ↥ρ.range => (σ : Equiv.Perm ↥Ps) e)
      ⟨?_, ?_⟩)
    · rintro ⟨σ, z, rfl⟩ ⟨τ, w, rfl⟩ h
      exact Subtype.ext (hreg z w h)
    · intro V
      obtain ⟨z, hz⟩ := htrans V
      exact ⟨⟨ρ z, z, rfl⟩, hz⟩
  obtain ⟨σ₂, hσ₂⟩ :=
    exists_prime_orderOf_dvd_card' (G := ↥ρ.range) 2 (by rw [hcard6]; norm_num)
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨σ₃, hσ₃⟩ :=
    exists_prime_orderOf_dvd_card' (G := ↥ρ.range) 3 (by rw [hcard6]; norm_num)
  obtain ⟨z₂, hz₂⟩ := σ₂.2
  obtain ⟨z₃, hz₃⟩ := σ₃.2
  have ho₂ : orderOf (ρ z₂) = 2 := by rw [hz₂, Subgroup.orderOf_coe, hσ₂]
  have ho₃ : orderOf (ρ z₃) = 3 := by rw [hz₃, Subgroup.orderOf_coe, hσ₃]
  have hmove : ∀ z : ↥I, orderOf (ρ z) ≠ 1 → ((ρ z e : ↥Ps) : Subgroup G) ≠ E := by
    intro z hz h
    exact hz (orderOf_eq_one_iff.mpr (hfixE z (Subtype.ext h)))
  obtain ⟨h, hh, hhV⟩ := exists_mem_normalizer_rightConjugate_eq_of_ne h11 hE16 hF hL hodd hx hxS
    (ρ z₂ e).2.1 (ρ z₂ e).2.2 (hmove z₂ (by rw [ho₂]; norm_num))
    (ρ z₃ e).2.1 (ρ z₃ e).2.2 (hmove z₃ (by rw [ho₃]; norm_num))
  set z' : ↥I := ⟨h⁻¹ * z₂ * h, hconjI h hh _ z₂.2⟩ with hz'
  have hz'e : ρ z' e = ρ z₃ e := by
    apply Subtype.ext
    rw [← hhV, hρapp, hρapp]
    have hEh : rightConjugate E h⁻¹ = E := (rightConjugate_eq_self_iff E h⁻¹).mpr (inv_mem hh)
    show rightConjugate E (h⁻¹ * z₂ * h)⁻¹ = rightConjugate (rightConjugate E (z₂ : G)⁻¹) h
    rw [show (h⁻¹ * (z₂ : G) * h)⁻¹ = h⁻¹ * (z₂ : G)⁻¹ * h by group, ← rightConjugate_mul,
      ← rightConjugate_mul, hEh]
  have hz'eq := hreg z' z₃ hz'e
  have hhstab : ∀ V ∈ Ps, rightConjugate V h ∈ Ps :=
    hstab h (Sec2.normalizer_le_normalizer_sec2P E hh)
  have hhstab' : ∀ V ∈ Ps, rightConjugate V h⁻¹ ∈ Ps :=
    hstab h⁻¹ (Sec2.normalizer_le_normalizer_sec2P E (inv_mem hh))
  have hord : orderOf (ρ z') = orderOf (ρ z₂) := by
    rw [orderOf_eq_orderOf_iff]
    intro n
    rw [← map_pow, ← map_pow, hρ1, hρ1]
    have hpow : ((z' ^ n : ↥I) : G) = h⁻¹ * ((z₂ ^ n : ↥I) : G) * h := by
      have := map_pow (MulAut.conj h⁻¹) (z₂ : G) n
      simp only [MulAut.conj_apply, inv_inv] at this
      simp only [SubgroupClass.coe_pow, hz']
      exact this.symm
    rw [hpow]
    set w := ((z₂ ^ n : ↥I) : G)
    have hinv : (h⁻¹ * w * h)⁻¹ = h⁻¹ * w⁻¹ * h := by group
    rw [hinv]
    constructor
    · intro H V hV
      have h1 := H _ (hhstab V hV)
      rw [rightConjugate_mul, ← mul_assoc, ← mul_assoc, mul_inv_cancel, one_mul,
        ← rightConjugate_mul] at h1
      have h2 := congrArg (fun U => rightConjugate U h⁻¹) h1
      simpa only [rightConjugate_inv_rightConjugate] using h2
    · intro H V hV
      have h1 := H _ (hhstab' V hV)
      rw [← rightConjugate_mul, ← rightConjugate_mul, h1, rightConjugate_rightConjugate_inv]
  rw [hz'eq, ho₃, ho₂] at hord
  norm_num at hord

theorem exists_mem_normalizer_rightConjugate_eq {V₁ V₂ : Subgroup G} (hV₁ : V₁ ∈ planes E F)
    (hV₁P : V₁ ≤ sec2P E) (hV₂ : V₂ ∈ planes E F) (hV₂P : V₂ ≤ sec2P E) :
    ∃ n ∈ normalizer (sec2P E : Set G), rightConjugate V₁ n = V₂ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hstab : ∀ n ∈ normalizer (sec2P E : Set G), ∀ V ∈ planes E F, V ≤ sec2P E →
      rightConjugate V n ∈ planes E F ∧ rightConjugate V n ≤ sec2P E :=
    fun n hn V hV hVP => ⟨rightConjugate_mem_planes hV n, by
      rw [← (rightConjugate_eq_self_iff _ n).mpr hn]
      exact AschbacherTheorem3.rightConjugate_le_rightConjugate hVP n⟩
  have hF0pl := sec2F0_mem_planes h11 hE16 hF hL hodd hx hxS h4
  have hF0P := sec2F0_le_sec2P hF x
  have hEAF0 := inf_le_of_mem_planes_of_le h11 hE16 hF hL hodd hF0pl hF0P
  have hF0E : sec2F0 A E x ≠ E := by
    have h := rightConjugate_sec2F0_ne h11 hE16 hF hL hodd hx hxS (Subgroup.one_mem _)
    rwa [rightConjugate_one] at h
  have hP1024 := card_sec2P_of_frame h11 hE16 hF hL hodd
  have hPN := sec2P_le_normalizer_sec2F0 h11 hE16 hF hL hodd hx hxS
  have hmove : ∃ k ∈ normalizer (sec2P E : Set G), rightConjugate E k ≠ E := by
    obtain ⟨j, hj | hj⟩ := hF0pl
    · obtain ⟨hD, -⟩ := exists_pointsData h11 hE16 hF hL hodd
      have hEAj := rightConjugate_inf_eq_of_points h11 hE16 hF hL hodd hD
        (card_inf_left hF hodd) (hj ▸ hF0P) (hj ▸ hEAF0)
      have hle := sec2P_le_rightConjugate_of_points h11 hE16 hF hL hodd
        (fun hq hqC _ hm => mem_sec2P_of_pow_two h11 hE16 hF hL hodd hq hqC hm) hEAj (hj ▸ hPN)
      have heq : sec2P E = rightConjugate (sec2P E) j :=
        eq_of_le_of_card_ge hle (by rw [rightConjugate_card])
      exact ⟨j, (rightConjugate_eq_self_iff _ j).mp heq.symm, hj ▸ hF0E⟩
    · obtain ⟨hDF, -⟩ := exists_pointsData h11 hE16 hF.symm hL hodd
      have hEAj := rightConjugate_inf_eq_of_points h11 hE16 hF hL hodd hDF
        (card_inf_left hF.symm hodd) (hj ▸ hF0P) (hj ▸ hEAF0)
      have hle := sec2P_le_rightConjugate_of_points h11 hE16 hF hL hodd
        (fun hq hqC _ hm => mem_sec2P_of_pow_two h11 hE16 hF.symm hL hodd hq hqC hm) hEAj
        (hj ▸ hPN)
      have heq : sec2P E = rightConjugate (sec2P F) j :=
        eq_of_le_of_card_ge hle (by
          rw [rightConjugate_card, card_sec2P_of_frame h11 hE16 hF.symm hL hodd, hP1024])
      have hNF0 : ∀ n ∈ normalizer (rightConjugate F j : Set G),
          n ∈ normalizer (sec2P E : Set G) := by
        intro n hn
        rw [← AschbacherTheorem3.rightConjugate_normalizer, mem_rightConjugate_iff] at hn
        rw [heq, ← AschbacherTheorem3.rightConjugate_normalizer, mem_rightConjugate_iff]
        exact Sec2.normalizer_le_normalizer_sec2P F hn
      obtain ⟨x', hx', hx'C⟩ := exists_mem_sec2P_not_mem_centralizerMod h11 hE16 hF hL hodd
      have hx'S : x' ∉ sec2S A R F E := by
        rw [sec2S_comm h11 hE16 hF hL hodd]
        intro hS
        exact hx'C (by rw [← sec2S_inf_sec2P h11 hE16 hF hL hodd]; exact ⟨hS, hx'⟩)
      have hform : ∀ V ∈ planes E F, V ≤ sec2P E → V ≠ rightConjugate F j →
          ∃ m ∈ normalizer (F : Set G),
            rightConjugate V j⁻¹ = rightConjugate (sec2F0 A F x') m := by
        intro V hV hVP hVF
        have hV' : rightConjugate V j⁻¹ ∈ planes F E := by
          rw [planes_comm]
          exact rightConjugate_mem_planes hV j⁻¹
        have hV'P : rightConjugate V j⁻¹ ≤ sec2P F := by
          have := AschbacherTheorem3.rightConjugate_le_rightConjugate hVP j⁻¹
          rwa [heq, rightConjugate_inv_rightConjugate] at this
        rcases eq_or_exists_of_mem_planes h11 hE16 hF.symm hL hodd hx' hx'S hV' hV'P with
          h | ⟨m, hm, hm'⟩
        · exact absurd (by rw [← h, rightConjugate_rightConjugate_inv]) hVF
        · exact ⟨m, (mem_normalizer_of_mem_inf_normalizer hF.symm hm).1, hm'⟩
      have h5 := ncard_planes_ne h11 hE16 hF hL hodd hx hxS h4
      obtain ⟨V, ⟨hV, hVP, hVE⟩, hVF0⟩ :=
        Set.exists_ne_of_one_lt_ncard (by rw [h5]; norm_num) (sec2F0 A E x)
      obtain ⟨m, hm, hmE⟩ := hform E ⟨1, Or.inl (rightConjugate_one E).symm⟩
        (le_sec2P_of_frame hF) (fun h => hF0E (hj.trans h.symm))
      obtain ⟨m', hm', hm'V⟩ := hform V hV hVP (fun h => hVF0 (h.trans hj.symm))
      refine ⟨j⁻¹ * (m⁻¹ * m') * j, hNF0 _ ?_, ?_⟩
      · rw [← AschbacherTheorem3.rightConjugate_normalizer, mem_rightConjugate_iff]
        simpa [mul_assoc] using mul_mem (inv_mem hm) hm'
      · have h1 : rightConjugate E (j⁻¹ * (m⁻¹ * m') * j) = V := by
          rw [show j⁻¹ * (m⁻¹ * m') * j = j⁻¹ * ((m⁻¹ * m') * j) by group, ← rightConjugate_mul,
            ← rightConjugate_mul, hmE, rightConjugate_mul (sec2F0 A F x') m (m⁻¹ * m'),
            mul_inv_cancel_left, ← hm'V, rightConjugate_rightConjugate_inv]
        rw [h1]
        exact hVE
  have hall : ∀ V ∈ planes E F, V ≤ sec2P E →
      ∃ n ∈ normalizer (sec2P E : Set G), rightConjugate E n = V := by
    intro V hV hVP
    by_cases hVE : V = E
    · exact ⟨1, Subgroup.one_mem _, by rw [rightConjugate_one, hVE]⟩
    obtain ⟨k, hk, hkE⟩ := hmove
    obtain ⟨hk1, hk2⟩ := hstab k hk E ⟨1, Or.inl (rightConjugate_one E).symm⟩
      (le_sec2P_of_frame hF)
    obtain ⟨h, hh, hhV⟩ := exists_mem_normalizer_rightConjugate_eq_of_ne h11 hE16 hF hL hodd
      hx hxS hk1 hk2 hkE hV hVP hVE
    exact ⟨k * h, mul_mem hk (Sec2.normalizer_le_normalizer_sec2P E hh),
      by rw [← rightConjugate_mul, hhV]⟩
  obtain ⟨n₁, hn₁, rfl⟩ := hall V₁ hV₁ hV₁P
  obtain ⟨n₂, hn₂, rfl⟩ := hall V₂ hV₂ hV₂P
  exact ⟨n₁⁻¹ * n₂, mul_mem (inv_mem hn₁) hn₂, by rw [rightConjugate_mul, mul_inv_cancel_left]⟩

end Sylow

end Frame

theorem step29_of (h11 : Step11)
    {d : L34E16Cert} (hE16 : RankTwoL3Four.HypII.l34CheckWE16 d = true)
    (h22iv : Step22iv) : Step29 := by
  intro G _ _ A R g E F hS x hx hxS
  have hF := hS.frame
  have hL := hS.type
  have hodd := hS.odd
  have h4 : 4 ^ 4 ≤ Nat.card (conjClosure (E ⊓ A) (sec2P F)) :=
    h22iv G A R g F E ⟨hF.symm, hL, hodd, hS.below⟩
  exact ⟨planes_sec2P_eq h11 hE16 hF hL hodd hx hxS h4,
    ncard_planes_sec2P h11 hE16 hF hL hodd hx hxS h4,
    isSylowOf_sec2P_centralizer h11 hE16 hF hL hodd hx hxS h4,
    fun V₁ hV₁ V₂ hV₂ => exists_mem_normalizer_rightConjugate_eq h11 hE16 hF hL hodd hx hxS h4
      hV₁.1 hV₁.2 hV₂.1 hV₂.2⟩

end CFSG.ComponentClassification.AS81
