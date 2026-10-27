module

public import CFSG.LocalAnalysis.ComponentClassification.AS81Step17
public import CFSG.GroupTheory.ABGLocalTools.CoreLemmas

public section

namespace CFSG.ComponentClassification.AS81

open Subgroup CFSG.Open CFSG.ABGLocalTools CFSG.ComponentClassification.AschbacherTightEmbedding
open CFSG.ComponentClassification.RankTwoStandard CFSG.ComponentClassification.RankTwoL3Four

variable {G : Type} [Group G] [Finite G]

theorem quasisimple_normal_le_center_or_eq_top {H : Type*} [Group H]
    (hH : CFSG.Open.IsQuasisimple H) {N : Subgroup H} (hN : N.Normal) :
    N ≤ center H ∨ N = ⊤ := by
  obtain ⟨hp, hs⟩ := hH
  have := hN.map (QuotientGroup.mk' (center H)) (QuotientGroup.mk'_surjective _)
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (N.map (QuotientGroup.mk' (center H))) with
    h | h
  · left
    rwa [Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk'] at h
  · right
    have hsup : N ⊔ center H = ⊤ := by
      have := Subgroup.comap_map_eq (QuotientGroup.mk' (center H)) N
      rw [h, Subgroup.comap_top, QuotientGroup.ker_mk'] at this
      exact this.symm
    have hZ : ⁅center H, center H⁆ = ⊥ :=
      Subgroup.commutator_eq_bot_iff_le_centralizer.mpr (Subgroup.center_le_centralizer _)
    have hmap : (⊤ : Subgroup H).map (QuotientGroup.mk' N) =
        (center H).map (QuotientGroup.mk' N) := by
      rw [← hsup, Subgroup.map_sup, QuotientGroup.map_mk'_self, bot_sup_eq]
    have hcomm : commutator H ≤ N := by
      rw [_root_.commutator_def, ← QuotientGroup.ker_mk' N, ← Subgroup.map_eq_bot_iff,
        Subgroup.map_commutator, hmap, ← Subgroup.map_commutator, hZ, Subgroup.map_bot]
    exact eq_top_iff.mpr (hp ▸ hcomm)

omit [Finite G] in
theorem commutator_self_eq_of_perfect {A : Subgroup G} (hA : commutator ↥A = ⊤) : ⁅A, A⁆ = A := by
  have h := Subgroup.map_commutator (⊤ : Subgroup ↥A) ⊤ A.subtype
  rw [← commutator_def, hA, ← MonoidHom.range_eq_map, range_subtype] at h
  exact h.symm

theorem rightConjugate_eq_of_le_normalizer {A : Subgroup G}
    (hstd : standardComponentIsStandard A) {n : G}
    (h₁ : rightConjugate A n ≤ normalizer (A : Set G))
    (h₂ : A ≤ normalizer (rightConjugate A n : Set G)) : rightConjugate A n = A := by
  set B := rightConjugate A n with hB
  have hq : CFSG.Open.IsQuasisimple ↥A := hstd.1
  have hIA : ((A ⊓ B).subgroupOf A).Normal := by
    refine (normal_subgroupOf_iff_le_normalizer inf_le_left).mpr fun a ha => ?_
    rw [mem_normalizer_iff]
    intro x
    rw [mem_inf, mem_inf, mem_normalizer_iff.mp (le_normalizer ha) x,
      mem_normalizer_iff.mp (h₂ ha) x]
  have hAB : ⁅A, B⁆ ≤ A ⊓ B := by
    rw [commutator_le]
    intro a ha b hb
    rw [commutatorElement_def]
    refine ⟨?_, ?_⟩
    · have e : a * b * a⁻¹ * b⁻¹ = a * (b * a⁻¹ * b⁻¹) := by group
      rw [e]
      exact A.mul_mem ha ((mem_normalizer_iff.mp (h₁ hb) _).mp (A.inv_mem ha))
    · exact B.mul_mem ((mem_normalizer_iff.mp (h₂ ha) b).mp hb) (B.inv_mem hb)
  rcases quasisimple_normal_le_center_or_eq_top hq hIA with hZ | hZ
  · exfalso
    have hC : A ⊓ B ≤ centralizer (A : Set G) := by
      intro x hx
      rw [mem_centralizer_iff]
      intro a ha
      have := mem_center_iff.mp (hZ (show (⟨x, hx.1⟩ : ↥A) ∈ (A ⊓ B).subgroupOf A from hx))
        ⟨a, ha⟩
      exact congrArg Subtype.val this
    have h1 : ⁅⁅A, B⁆, A⁆ = ⊥ := commutator_eq_bot_iff_le_centralizer.mpr (hAB.trans hC)
    have h2 : ⁅⁅B, A⁆, A⁆ = ⊥ := by
      rw [commutator_comm B A]
      exact h1
    have h3 : ⁅⁅A, A⁆, B⁆ = ⊥ := commutator_commutator_eq_bot_of_rotate h1 h2
    rw [commutator_self_eq_of_perfect hq.1] at h3
    exact hstd.2.2.2.2 n⁻¹ h3
  · have hle : A ≤ B := fun a ha => by
      have : (⟨a, ha⟩ : ↥A) ∈ (A ⊓ B).subgroupOf A := hZ ▸ mem_top _
      exact this.2
    exact (eq_of_le_of_card_ge hle (by rw [hB, rightConjugate_card])).symm

theorem mem_normalizer_of_rightConjugate_le {A M : Subgroup G}
    (hstd : standardComponentIsStandard A) {n : G} (hM : M ≤ normalizer (A : Set G))
    (h₁ : rightConjugate A n ≤ M) (h₂ : rightConjugate A n⁻¹ ≤ M) :
    n ∈ normalizer (A : Set G) := by
  have hA : A ≤ normalizer (rightConjugate A n : Set G) := by
    have := rightConjugate_le_normalizer_rightConjugate (h₂.trans hM) n
    rwa [rightConjugate_mul, inv_mul_cancel, rightConjugate_one] at this
  exact (rightConjugate_eq_self_iff A n).mp
    (rightConjugate_eq_of_le_normalizer hstd (h₁.trans hM) hA)

omit [Finite G] in
theorem exists_not_mem_normalizer {A N : Subgroup G} (h : ¬ (A.subgroupOf N).Normal) :
    ∃ n ∈ N, n ∉ normalizer (A : Set G) := by
  by_contra hcon
  push Not at hcon
  apply h
  refine ⟨fun a ha x => ?_⟩
  rw [mem_subgroupOf] at ha ⊢
  have := (mem_normalizer_iff.mp (hcon x x.2) a).mp ha
  simpa using this

section Frame

variable {A R : Subgroup G} {g : G} {E F : Subgroup G}

theorem oddCoreIn_centralizer_le_of_frame (h4 : AS76b.Asc75Theorem4) (h34 : AS76b.Asc08Lemma34)
    (hF : Frame G A A R g E F) (hL : TypeL34 (rankTwoQuot A)) {z : G} (hz : z ∈ E) :
    AS76b.oddCoreIn (centralizer ({z} : Set G)) ≤ AS76b.oddCoreIn (centralizer (A : Set G)) ∧
      AS76b.oddCoreIn (centralizer (A : Set G)) ∈ oddNStar E := by
  have hB := hF.base
  have hstd := hB.hyp.standard
  have hFs := (h34 G A hB.hyp31).2
  have hKn := not_normal_centralizer hstd hB.hyp.not_normal
  set W := AS76b.oddCoreIn (centralizer ({z} : Set G)) with hWdef
  have hP : Odd (Nat.card W) ∧ E ≤ normalizer (W : Set G) := by
    refine ⟨AS76b.odd_card_oddCoreIn _, fun e he => AS76b.le_normalizer_oddCoreIn _ ?_⟩
    rw [mem_centralizer_singleton_iff]
    exact congrArg Subtype.val (hF.elemE.1.is_comm.comm ⟨e, he⟩ ⟨z, hz⟩)
  obtain ⟨X', hWX', hX'⟩ := Finite.exists_le_maximal
    (p := fun Y : Subgroup G => Odd (Nat.card Y) ∧ E ≤ normalizer (Y : Set G)) hP
  have hX'eq := eq_oddCoreIn_of_mem_oddNStar h4 hstd hFs hKn hL hF.sylowR hF.elemR hF.cardR
    hF.elemE hF.cardE hF.R_le_E hF.E_le (X := X') hX'
  exact ⟨hX'eq ▸ hWX', hX'eq ▸ hX'⟩

theorem rankTwoHyp_normalizer_of_frame (h4 : AS76b.Asc75Theorem4) (h34 : AS76b.Asc08Lemma34)
    {d : L34E16Cert}
    (hE16 : RankTwoL3Four.HypII.l34CheckWE16 d = true) (hF : Frame G A A R g E F)
    (hL : TypeL34 (rankTwoQuot A)) {z : G} (hz : z ∈ E)
    (hW : AS76b.oddCoreIn (centralizer ({z} : Set G)) ≠ ⊥) :
    normalizer (AS76b.oddCoreIn (centralizer ({z} : Set G)) : Set G) ≠ ⊤ ∧
      A ≤ centralizer (AS76b.oddCoreIn (centralizer ({z} : Set G)) : Set G) ∧
      centralizer ({z} : Set G) ≤
        normalizer (AS76b.oddCoreIn (centralizer ({z} : Set G)) : Set G) ∧
      RankTwoHypNF ↥(normalizer (AS76b.oddCoreIn (centralizer ({z} : Set G)) : Set G))
        (A.subgroupOf (normalizer (AS76b.oddCoreIn (centralizer ({z} : Set G)) : Set G))) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hB := hF.base
  have hstd := hB.hyp.standard
  set K := centralizer (A : Set G) with hKdef
  set W := AS76b.oddCoreIn (centralizer ({z} : Set G)) with hWdef
  set X := AS76b.oddCoreIn K with hXdef
  obtain ⟨hWX, hX⟩ := oddCoreIn_centralizer_le_of_frame h4 h34 hF hL hz
  have hX1 : X ≠ ⊥ := fun h => hW (le_bot_iff.mp (h ▸ hWX))
  obtain ⟨-, -, hAX, hH⟩ := step17a_of_frame h4 h34 hE16 hF hL X hX hX1
  obtain ⟨n, hnX, hnA⟩ := exists_not_mem_normalizer hH.not_normal
  have hXK : X ≤ K := AS76b.oddCoreIn_le K
  have hACX : A ≤ centralizer (X : Set G) := le_centralizer_iff.mp hXK
  have hACW : A ≤ centralizer (W : Set G) := hACX.trans (centralizer_le hWX)
  have hCzW : centralizer ({z} : Set G) ≤ normalizer (W : Set G) :=
    AS76b.le_normalizer_oddCoreIn _
  have hRz : R ≤ centralizer ({z} : Set G) := fun r hr => by
    rw [mem_centralizer_singleton_iff]
    exact congrArg Subtype.val (hF.elemE.1.is_comm.comm ⟨r, hF.R_le_E hr⟩ ⟨z, hz⟩)
  have hRN : R ≤ normalizer (W : Set G) := hRz.trans hCzW
  set N := normalizer (W : Set G) with hNdef
  have hAN : A ≤ N := hACW.trans (centralizer_le_normalizer _)
  refine ⟨fun htop => ?_, hACW, hCzW, ?_⟩
  · have hn : W.Normal := normalizer_eq_top_iff.mp htop
    have hle : W ≤ standardComponentOddCore G := le_sSup ⟨hn, AS76b.odd_card_oddCoreIn _⟩
    rw [hB.oddCore] at hle
    exact hW (le_bot_iff.mp hle)
  have heven : Even (Nat.card (centralizer (A : Set G) ⊓ N : Subgroup G)) := by
    have h4' : 4 ∣ Nat.card (K ⊓ N : Subgroup G) := by
      rw [← hF.cardR]
      exact Subgroup.card_dvd_of_le (le_inf hF.sylowR.le hRN)
    exact even_iff_two_dvd.mpr ((by norm_num : 2 ∣ 4).trans h4')
  have hstd₁ := GMS78.standard_subgroupOf hstd hAN heven
  have hnn : ¬ (A.subgroupOf N).Normal := by
    intro hn
    have hNA : N ≤ normalizer (A : Set G) := fun m hm => by
      refine AS76b.mem_normalizer_of_map_conj_le ?_
      rintro _ ⟨a, ha, rfl⟩
      have h1 := hn.conj_mem ⟨a, hAN ha⟩ (mem_subgroupOf.mpr ha) ⟨m, hm⟩
      rw [mem_subgroupOf] at h1
      simpa using h1
    have hCN : centralizer (X : Set G) ≤ normalizer (A : Set G) :=
      ((centralizer_le hWX).trans (centralizer_le_normalizer _)).trans hNA
    have hXn : ∀ m ∈ normalizer (X : Set G), rightConjugate A m ≤ centralizer (X : Set G) := by
      intro m hm
      have h1 := AschbacherTheorem3.rightConjugate_le_rightConjugate hACX m
      rwa [← AS76b.centralizer_rightConjugate, (rightConjugate_eq_self_iff X m).mpr hm] at h1
    exact hnA (mem_normalizer_of_rightConjugate_le hstd hCN (hXn n hnX) (hXn n⁻¹ (inv_mem hnX)))
  have hrank : 2 ≤ Open.pRank 2 (centralizer ((A.subgroupOf N : Subgroup ↥N) : Set ↥N)) := by
    refine CFSG.SectionRank.le_pRank one_lt_two (E := R.subgroupOf N) ?_
      (isElemAbelian_subgroupOf hF.elemR N) ?_
    · intro x hx
      rw [mem_centralizer_iff]
      intro y hy
      exact Subtype.ext (mem_centralizer_iff.mp (hF.sylowR.le (mem_subgroupOf.mp hx)) y
        (mem_subgroupOf.mp hy))
    · rw [show (2 : ℕ) ^ 2 = 4 by norm_num, ← hF.cardR]
      exact Nat.card_congr (subgroupOfEquivOfLe hRN).toEquiv
  exact ⟨hstd₁, hnn, hrank⟩

end Frame

section Closure

variable {N : Subgroup G}

abbrev closureIn (A N : Subgroup G) : Subgroup G :=
  (rankTwoX (A.subgroupOf N)).map N.subtype

omit [Finite G] in
theorem le_closureIn {A : Subgroup G} (hAN : A ≤ N) : A ≤ closureIn A N := fun a ha =>
  ⟨⟨a, hAN ha⟩, subset_normalClosure (mem_subgroupOf.mpr ha), rfl⟩

omit [Finite G] in
theorem rightConjugate_le_closureIn {A : Subgroup G} (hAN : A ≤ N) {n : G} (hn : n ∈ N) :
    rightConjugate A n ≤ closureIn A N := by
  rintro _ ⟨a, ha, rfl⟩
  refine ⟨⟨n, hn⟩⁻¹ * ⟨a, hAN ha⟩ * ⟨n, hn⟩⁻¹⁻¹, ?_, ?_⟩
  · exact (normalClosure_normal).conj_mem _ (subset_normalClosure (mem_subgroupOf.mpr ha)) _
  · simp

omit [Finite G] in
theorem le_normalizer_closureIn (A N : Subgroup G) :
    N ≤ normalizer (closureIn A N : Set G) := by
  have h := Subgroup.le_normalizer_map (H := rankTwoX (A.subgroupOf N)) N.subtype
  rw [Subgroup.normalizer_eq_top, ← MonoidHom.range_eq_map, Subgroup.range_subtype] at h
  exact h

theorem odd_card_centralizer_closureIn {A : Subgroup G} (hstd : standardComponentIsStandard A)
    (hAN : A ≤ N) (hnn : ¬ (A.subgroupOf N).Normal) :
    Odd (Nat.card (centralizer (closureIn A N : Set G))) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hK := AS76b.tightlyEmbedded_centralizer hstd
  have hNK := AS76b.normalizer_centralizer_eq hstd
  obtain ⟨n, hn, hnA⟩ := exists_not_mem_normalizer hnn
  refine Nat.odd_iff.mpr (Nat.two_dvd_ne_zero.mp fun h2 => ?_)
  obtain ⟨y, hy⟩ := exists_prime_orderOf_dvd_card' (G := ↥(centralizer (closureIn A N : Set G)))
    2 h2
  have hy2 : (y : G) ^ 2 = 1 := by
    have := pow_orderOf_eq_one y
    rw [hy] at this
    exact congrArg Subtype.val this
  have hy1 : (y : G) ≠ 1 := fun h => by
    have : y = 1 := Subtype.ext h
    rw [this, orderOf_one] at hy
    exact absurd hy (by norm_num)
  have hyK : (y : G) ∈ centralizer (A : Set G) :=
    centralizer_le (le_closureIn hAN) y.2
  have hLN : closureIn A N ≤ normalizer (A : Set G) := by
    intro c hc
    rw [← hNK]
    exact RankTwoSporadic.mem_normalizer_of_commute_of_tightlyEmbedded hK hyK hy1 hy2
      (mem_centralizer_iff.mp y.2 c hc)
  exact hnA (mem_normalizer_of_rightConjugate_le hstd hLN (rightConjugate_le_closureIn hAN hn)
    (rightConjugate_le_closureIn hAN (inv_mem hn)))

end Closure

theorem mem_centralizer_of_mem_normalizer_sylow {S' : Subgroup G} {z : G}
    (hzS : z ∈ centerIn S') (hz : orderOf z = 2) (hZ : Nat.card (centerIn S') = 2) {m : G}
    (hm : m ∈ normalizer (S' : Set G)) : m ∈ centralizer ({z} : Set G) := by
  have hZeq : centerIn S' = zpowers z := by
    refine (eq_of_le_of_card_ge (zpowers_le.mpr hzS) ?_).symm
    rw [hZ, Nat.card_zpowers, hz]
  have hmz : m * z * m⁻¹ ∈ centerIn S' := by
    refine ⟨(mem_normalizer_iff.mp hm z).mp hzS.1, mem_centralizer_iff.mpr fun s hs => ?_⟩
    have hs' : m⁻¹ * s * m ∈ S' := by
      have := (mem_normalizer_iff.mp (inv_mem hm) s).mp hs
      simpa using this
    have h1 := mem_centralizer_iff.mp hzS.2 _ hs'
    calc s * (m * z * m⁻¹) = m * ((m⁻¹ * s * m) * z) * m⁻¹ := by group
      _ = m * (z * (m⁻¹ * s * m)) * m⁻¹ := by rw [h1]
      _ = m * z * m⁻¹ * s := by group
  rw [hZeq] at hmz
  obtain ⟨k, hk⟩ := mem_zpowers_iff.mp hmz
  have hk' : z ^ (k % 2) = m * z * m⁻¹ := by
    rw [← hk]
    have := zpow_mod_orderOf z k
    rw [hz] at this
    exact_mod_cast this
  have hzz : m * z * m⁻¹ = z := by
    rcases Int.emod_two_eq_zero_or_one k with h | h
    · exfalso
      rw [h, zpow_zero] at hk'
      have h1 : m⁻¹ * (m * z * m⁻¹) * m = z := by group
      rw [← hk', mul_one, inv_mul_cancel] at h1
      rw [← h1, orderOf_one] at hz
      exact absurd hz (by norm_num)
    · rw [h, zpow_one] at hk'
      exact hk'.symm
  rw [mem_centralizer_singleton_iff]
  calc m * z = m * z * m⁻¹ * m := by group
    _ = z * m := by rw [hzz]

omit [Finite G] in
theorem rightConjugate_top (g : G) : rightConjugate (⊤ : Subgroup G) g = ⊤ :=
  (rightConjugate_eq_self_iff ⊤ g).mpr (by
    rw [mem_normalizer_iff]
    intro x
    simp)

theorem mem_centerIn_of_le_centralizer {S' : Subgroup G} {z : G} (hS' : IsSylowOf 2 S' ⊤)
    (hz : orderOf z = 2) (hSz : S' ≤ centralizer ({z} : Set G)) : z ∈ centerIn S' := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hzC : z ∈ centralizer (S' : Set G) := mem_centralizer_iff.mpr fun s hs =>
    mem_centralizer_singleton_iff.mp (hSz hs)
  have h2 : IsPGroup 2 (zpowers z) := IsPGroup.of_card (n := 1) (by
    rw [Nat.card_zpowers, hz, pow_one])
  have hP : IsPGroup 2 ↥(S' ⊔ zpowers z) :=
    hS'.isPGroup.to_sup_of_normal_left' h2 (zpowers_le.mpr (centralizer_le_normalizer _ hzC))
  have heq := hS'.eq_of_le le_sup_left le_top hP
  have hzS : z ∈ S' := by
    have := (le_sup_right : zpowers z ≤ S' ⊔ zpowers z) (mem_zpowers z)
    rwa [heq] at this
  exact ⟨hzS, hzC⟩

theorem rightConjugate_eq_of_sylow_le {L : Subgroup G} {z : G} (hz : orderOf z = 2)
    (hzL : centralizer ({z} : Set G) ≤ normalizer (L : Set G))
    (hZ : ∀ S' : Subgroup G, IsSylowOf 2 S' ⊤ → S' ≤ centralizer ({z} : Set G) →
      Nat.card (centerIn S') = 2)
    {g : G} {S' : Subgroup G} (hS' : IsSylowOf 2 S' ⊤) (hSz : S' ≤ centralizer ({z} : Set G))
    (hSL' : S' ≤ normalizer (rightConjugate L g : Set G)) : rightConjugate L g = L := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set L' := rightConjugate L g with hL'
  have hSL : S' ≤ normalizer (L : Set G) := hSz.trans hzL
  have h1 : IsSylowOf 2 S' (normalizer (L' : Set G)) := hS'.of_le hSL' le_top
  have h2 : IsSylowOf 2 (rightConjugate S' g) (normalizer (L' : Set G)) := by
    have h := AschbacherTheorem3.isSylowOf_rightConjugate hS' g
    rw [rightConjugate_top] at h
    exact h.of_le (rightConjugate_le_normalizer_rightConjugate hSL g) le_top
  obtain ⟨k, hkL, hk⟩ := IsSylowOf.exists_mem_conj h1 h2
  have hgk : g * k ∈ normalizer (S' : Set G) := by
    rw [← rightConjugate_eq_self_iff, ← rightConjugate_mul]
    ext x
    rw [mem_rightConjugate_iff, hk]
    constructor
    · intro h
      simpa [mul_assoc] using h
    · intro h
      simpa [mul_assoc] using h
  have hgkz := mem_centralizer_of_mem_normalizer_sylow (mem_centerIn_of_le_centralizer hS' hz hSz)
    hz (hZ S' hS' hSz) hgk
  have hLm : rightConjugate L (g * k) = L := (rightConjugate_eq_self_iff L _).mpr (hzL hgkz)
  rw [← rightConjugate_mul, ← hL', (rightConjugate_eq_self_iff L' k).mpr hkL] at hLm
  exact hLm

omit [Finite G] in
theorem centralizer_singleton_conj (z c : G) :
    centralizer ({c⁻¹ * z * c} : Set G) = rightConjugate (centralizer ({z} : Set G)) c := by
  ext x
  rw [mem_rightConjugate_iff, mem_centralizer_singleton_iff, mem_centralizer_singleton_iff]
  constructor
  · intro h
    calc c * x * c⁻¹ * z = c * (x * (c⁻¹ * z * c)) * c⁻¹ := by group
      _ = c * ((c⁻¹ * z * c) * x) * c⁻¹ := by rw [h]
      _ = z * (c * x * c⁻¹) := by group
  · intro h
    calc x * (c⁻¹ * z * c) = c⁻¹ * (c * x * c⁻¹ * z) * c := by group
      _ = c⁻¹ * (z * (c * x * c⁻¹)) * c := by rw [h]
      _ = c⁻¹ * z * c * x := by group

omit [Finite G] in
theorem false_of_pElement {L : Subgroup G} {z : G}
    (hCL : Odd (Nat.card (centralizer (L : Set G))))
    (hzL : centralizer ({z} : Set G) ≤ normalizer (L : Set G)) {c : G} {p : ℕ} (hp : p.Prime)
    (hpz : ¬ p ∣ (centralizer ({z} : Set G) ⊓ centralizer (L : Set G)).relIndex
      (centralizer ({z} : Set G)))
    {u : G} (huL : u ∈ L) (hut : u ∈ centralizer ({c⁻¹ * z * c} : Set G)) {k : ℕ}
    (hu : u ^ p ^ k = 1)
    (huN : ∀ N : Subgroup G, N ≤ L ⊓ centralizer ({c⁻¹ * z * c} : Set G) →
      L ⊓ centralizer ({c⁻¹ * z * c} : Set G) ≤ normalizer (N : Set G) → Odd (Nat.card N) →
      u ∉ N) : False := by
  set Ct := centralizer ({c⁻¹ * z * c} : Set G) with hCtdef
  set L'' := rightConjugate L c with hL''
  have hCt : Ct = rightConjugate (centralizer ({z} : Set G)) c := centralizer_singleton_conj z c
  have hCtL : Ct ≤ normalizer (L'' : Set G) := by
    rw [hCt]
    exact rightConjugate_le_normalizer_rightConjugate hzL c
  have hCL'' : centralizer (L'' : Set G) = rightConjugate (centralizer (L : Set G)) c :=
    AS76b.centralizer_rightConjugate L c
  set D := L ⊓ Ct with hD
  have hDN : D ≤ normalizer ((D ⊓ centralizer (L'' : Set G) : Subgroup G) : Set G) := by
    intro d hd
    rw [mem_normalizer_iff]
    intro x
    have hd1 : d ∈ normalizer (D : Set G) := le_normalizer hd
    have hd2 : d ∈ normalizer (centralizer (L'' : Set G) : Set G) :=
      CFSG.BenderSuzuki.normalizer_le_normalizer_centralizer _ (hCtL hd.2)
    exact ⟨fun h => ⟨(mem_normalizer_iff.mp hd1 x).mp h.1, (mem_normalizer_iff.mp hd2 x).mp h.2⟩,
      fun h => ⟨(mem_normalizer_iff.mp hd1 x).mpr h.1, (mem_normalizer_iff.mp hd2 x).mpr h.2⟩⟩
  have hodd : Odd (Nat.card (D ⊓ centralizer (L'' : Set G) : Subgroup G)) := by
    have h1 : Odd (Nat.card (centralizer (L'' : Set G))) := by
      rw [hCL'', rightConjugate_card]
      exact hCL
    exact h1.of_dvd_nat (card_dvd_of_le inf_le_right)
  have huD : u ∈ D := ⟨huL, hut⟩
  have hu'' : u ∉ centralizer (L'' : Set G) := fun h => huN _ inf_le_left hDN hodd ⟨huD, h⟩
  set K := Ct ⊓ centralizer (L'' : Set G) with hK
  have hKn : (K.subgroupOf Ct).Normal := by
    refine (normal_subgroupOf_iff_le_normalizer inf_le_left).mpr fun x hx => ?_
    rw [mem_normalizer_iff]
    intro y
    have h1 : x ∈ normalizer (Ct : Set G) := le_normalizer hx
    have h2 : x ∈ normalizer (centralizer (L'' : Set G) : Set G) :=
      CFSG.BenderSuzuki.normalizer_le_normalizer_centralizer _ (hCtL hx)
    exact ⟨fun h => ⟨(mem_normalizer_iff.mp h1 y).mp h.1, (mem_normalizer_iff.mp h2 y).mp h.2⟩,
      fun h => ⟨(mem_normalizer_iff.mp h1 y).mpr h.1, (mem_normalizer_iff.mp h2 y).mpr h.2⟩⟩
  set q := QuotientGroup.mk' (K.subgroupOf Ct) with hq
  have hq1 : q ⟨u, hut⟩ ≠ 1 := by
    rw [hq, QuotientGroup.mk'_apply, Ne, QuotientGroup.eq_one_iff, mem_subgroupOf]
    exact fun h => hu'' h.2
  have hpdvd : p ∣ (K.subgroupOf Ct).index := by
    have hord : orderOf (q ⟨u, hut⟩) ∣ p ^ k := by
      rw [orderOf_dvd_iff_pow_eq_one, ← map_pow]
      have : (⟨u, hut⟩ : ↥Ct) ^ p ^ k = 1 := Subtype.ext (by simpa using hu)
      rw [this, map_one]
    obtain ⟨i, -, hie⟩ := (Nat.dvd_prime_pow hp).mp hord
    have hi0 : i ≠ 0 := by
      rintro rfl
      rw [pow_zero, orderOf_eq_one_iff] at hie
      exact hq1 hie
    have h1 : p ∣ orderOf (q ⟨u, hut⟩) := by
      rw [hie]
      exact dvd_pow_self p hi0
    exact h1.trans (orderOf_dvd_natCard _)
  apply hpz
  have hidx : (K.subgroupOf Ct).index =
      (centralizer ({z} : Set G) ⊓ centralizer (L : Set G)).relIndex
        (centralizer ({z} : Set G)) := by
    change K.relIndex Ct = _
    have hKeq : K = (centralizer ({z} : Set G) ⊓ centralizer (L : Set G)).map
        (MulAut.conj c⁻¹).toMonoidHom := by
      rw [hK, hCt, hCL'', rightConjugate, rightConjugate,
        Subgroup.map_inf_eq _ _ _ (MulAut.conj c⁻¹).injective]
    rw [hKeq, hCt, rightConjugate,
      relIndex_map_map_of_injective _ _ (MulAut.conj c⁻¹).injective]
  rw [← hidx]
  exact hpdvd

end CFSG.ComponentClassification.AS81
