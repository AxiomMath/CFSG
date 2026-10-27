module

public import CFSG.LocalAnalysis.ComponentClassification.AS81Sec3Step17
public import CFSG.LocalAnalysis.ComponentClassification.AS81Sec3Step34

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.ComponentClassification.AS81

open Subgroup CFSG.Open CFSG.ABGLocalTools CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.ComponentClassification.UnbalancedCatalog CFSG.ComponentClassification.RankTwoExceptional
open CFSG.ComponentClassification.AschbacherTightEmbedding
open CFSG.ComponentClassification.RankTwoStandard

section Core


variable {G : Type} [Group G] [Finite G] {A A₁ R : Subgroup G} {g : G} {E F : Subgroup G} {x : G}

namespace Sec3

theorem exists_centralizer_inf_A (hS : Sec3Setting G A A₁ R g E F x) :
    ∃ D : Subgroup G, D ≤ A ⊓ centralizer ((E ⊓ A : Subgroup G) : Set G) ∧
      A ⊓ centralizer ((E ⊓ A : Subgroup G) : Set G) ≤ normalizer (D : Set G) ∧
      Nat.card D = 2 ^ 10 ∧ ⁅D, zpowers x⁆ = D ∧
      Nat.card (A ⊓ centralizer ((E ⊓ A : Subgroup G) : Set G) : Subgroup G) = 2 ^ 10 * 3 := by
  set C := A ⊓ centralizer ((E ⊓ A : Subgroup G) : Set G) with hCdef
  obtain ⟨Kf, _, _, _, hKf, f, hM⟩ := exists_sec3Model hS
  have hAK : ∀ w ∈ A, w ∈ centralizer (A : Set G) → w = 1 := by
    intro w hwA hwK
    have hw : (⟨w, hwA⟩ : A) ∈ center A := mem_center_iff.mpr fun a =>
      Subtype.ext (mem_centralizer_iff.mp hwK a a.2)
    rw [hS.center_eq, mem_bot] at hw
    exact congrArg Subtype.val hw
  have hD₀C : g2ShortParabolicRadical Kf ≤ adjointGroup .G2 Kf :=
    G2.g2ShortParabolicRadical_le_adjointGroup
  have hHrC : g2TorusR Kf ≤ adjointGroup .G2 Kf := G2.g2TorusR_le_adjointGroup
  have hfC : ((g2ShortParabolicRadical Kf ⊔ g2TorusR Kf).subgroupOf
      (adjointGroup .G2 Kf)).map f ≤ C := by
    rintro _ ⟨c, hc, rfl⟩
    refine ⟨by rw [← hM.range_eq]; exact ⟨c, rfl⟩, mem_centralizer_iff.mpr fun w hw => ?_⟩
    rw [← hM.E_eq] at hw
    obtain ⟨z, hz, rfl⟩ := hw
    have h1 := mem_centralizer_iff.mp (G2.g2D0Hr_le_centralizer hKf (mem_subgroupOf.mp hc)) _
      (mem_subgroupOf.mp hz)
    rw [← map_mul, ← map_mul]
    exact congrArg f (Subtype.ext h1)
  have hCeq : C = ((g2ShortParabolicRadical Kf ⊔ g2TorusR Kf).subgroupOf
      (adjointGroup .G2 Kf)).map f := by
    refine le_antisymm (fun a ha => ?_) hfC
    obtain ⟨k, hk, c, hc, hac⟩ :=
      Sec3Model.exists_mul_of_mem_normalizer hKf hM (le_normalizer ha.1) ha.2
    have hcA : c ∈ A := (hfC hc).1
    have hkA : k ∈ A := by
      have e : k = a * c⁻¹ := by rw [hac]; group
      rw [e]
      exact mul_mem ha.1 (inv_mem hcA)
    rw [hac, hAK k hkA hk, one_mul]
    exact hc
  refine ⟨((g2ShortParabolicRadical Kf).subgroupOf (adjointGroup .G2 Kf)).map f,
    (Sec3.tr_mono le_sup_left).trans hfC, ?_, ?_, ?_, ?_⟩
  ·
    rw [hCeq]
    rintro _ ⟨c, hc, rfl⟩
    refine AS76b.mem_normalizer_of_map_conj_le ?_
    rintro _ ⟨_, ⟨d, hd, rfl⟩, rfl⟩
    have hcN : (c : ModGL .G2 Kf) ∈ normalizer (g2ShortParabolicRadical Kf : Set (ModGL .G2 Kf)) :=
      G2.g2Para_le_normalizer ((sup_le (le_sup_left.trans le_sup_left) le_sup_right :
        g2ShortParabolicRadical Kf ⊔ g2TorusR Kf ≤ G2.g2Para Kf) (mem_subgroupOf.mp hc))
    refine ⟨c * d * c⁻¹, mem_subgroupOf.mpr ?_, ?_⟩
    · simp only [coe_mul, coe_inv]
      exact (mem_normalizer_iff.mp hcN d).mp (mem_subgroupOf.mp hd)
    · simp [MulAut.conj_apply]
  · rw [card_map_of_injective hM.inj,
      Nat.card_congr (subgroupOfEquivOfLe hD₀C).toEquiv, G2.card_g2ShortParabolicRadical, hKf]
    norm_num
  · rw [← hM.x_eq, ← Sec3.tr_commutator hD₀C hHrC,
      G2.commutator_g2ShortParabolicRadical_g2TorusR hKf]
  · rw [hCeq, card_map_of_injective hM.inj, ← G2.card_g2D0Hr hKf]
    exact Nat.card_congr (subgroupOfEquivOfLe G2.g2D0Hr_le_adjointGroup).toEquiv


theorem oddCoreIn_centralizer_le_of_mem (h17 : Step17G24Odd) (hS : Sec3Setting G A A₁ R g E F x)
    {z : G} (hzE : z ∈ E) (hzA : z ∈ A) :
    AS76b.oddCoreIn (centralizer ({z} : Set G)) ≤ AS76b.oddCoreIn (centralizer (A : Set G)) := by
  have hFr := hS.frame
  have hstd := hS.base.hyp.standard
  have hNK := AS76b.normalizer_centralizer_eq hstd
  set W := AS76b.oddCoreIn (centralizer ({z} : Set G)) with hWdef
  set O := AS76b.oddCoreIn (centralizer (A : Set G)) with hOdef
  set C := A ⊓ centralizer ((E ⊓ A : Subgroup G) : Set G) with hCdef
  obtain ⟨D, hDC, hCD, hDcard, hDx, hCcard⟩ := Sec3.exists_centralizer_inf_A hS
  have hP : Odd (Nat.card W) ∧ E ≤ normalizer (W : Set G) := by
    refine ⟨AS76b.odd_card_oddCoreIn _, fun e he => AS76b.le_normalizer_oddCoreIn _ ?_⟩
    rw [mem_centralizer_singleton_iff]
    exact congrArg Subtype.val (hFr.elemE.1.is_comm.comm ⟨e, he⟩ ⟨z, hzE⟩)
  obtain ⟨X, hWX, hX⟩ := Finite.exists_le_maximal
    (p := fun Y : Subgroup G => Odd (Nat.card Y) ∧ E ≤ normalizer (Y : Set G)) hP
  obtain ⟨hsyl, hXeq⟩ := h17 G A A₁ R g E F x hS X hX
  have hXo : Odd (Nat.card X) := hX.prop.1
  have hAO : A ≤ normalizer (O : Set G) := by
    rw [hOdef]
    refine le_trans ?_ (AS76b.normalizer_le_normalizer_oddCoreIn _)
    rw [hNK]
    exact le_normalizer
  have hCz : C ≤ centralizer ({z} : Set G) := fun c hc =>
    mem_centralizer_singleton_iff.mpr (mem_centralizer_iff.mp hc.2 z ⟨hzE, hzA⟩).symm
  have hCW : C ≤ normalizer (W : Set G) := hCz.trans (AS76b.le_normalizer_oddCoreIn _)
  have hCY : C ≤ normalizer ((W ⊔ O : Subgroup G) : Set G) := by
    intro c hc
    refine AS76b.mem_normalizer_of_map_conj_le ?_
    rw [Subgroup.map_sup]
    refine sup_le_sup ?_ ?_
    · rintro _ ⟨w, hw, rfl⟩
      exact (mem_normalizer_iff.mp (hCW hc) w).mp hw
    · rintro _ ⟨o, ho, rfl⟩
      exact (mem_normalizer_iff.mp (hAO hc.1) o).mp ho
  set T₃ := (W ⊔ O) ⊓ A with hT₃def
  have hCT : C ≤ normalizer (T₃ : Set G) := by
    intro c hc
    rw [mem_normalizer_iff]
    intro y
    exact and_congr (mem_normalizer_iff.mp (hCY hc) y) (mem_normalizer_iff.mp
      (le_normalizer hc.1) y)
  have hOX : O ≤ X := by
    rw [hXeq]
    exact le_sup_right
  have hT₃X : T₃ ≤ X ⊓ A := inf_le_inf_right A (sup_le hWX hOX)
  have hT₃C : T₃ ≤ C := hT₃X.trans hsyl.le
  by_contra hWO
  have hT₃1 : T₃ ≠ ⊥ := by
    intro hbot
    apply hWO
    intro w hw
    have hwX : w ∈ ((X ⊓ A ⊔ O : Subgroup G) : Set G) := by
      rw [← hXeq]
      exact hWX hw
    rw [coe_mul_of_left_le_normalizer_right (X ⊓ A) O (inf_le_right.trans hAO),
      Set.mem_mul] at hwX
    obtain ⟨c, hc, k, hk, rfl⟩ := hwX
    have hcT : c ∈ T₃ := by
      refine ⟨?_, hc.2⟩
      have := mul_mem (mem_sup_left hw : c * k ∈ W ⊔ O) (inv_mem (mem_sup_right hk : k ∈ W ⊔ O))
      rwa [mul_inv_cancel_right] at this
    rw [hbot, mem_bot] at hcT
    rw [hcT, one_mul]
    exact hk
  have hT₃3 : Nat.card T₃ = 3 := by
    have hdvd : Nat.card T₃ ∣ 2 ^ 10 * 3 := hCcard ▸ Subgroup.card_dvd_of_le hT₃C
    have hodd : Odd (Nat.card T₃) :=
      hXo.of_dvd_nat (Subgroup.card_dvd_of_le (hT₃X.trans inf_le_left))
    have hcop : Nat.Coprime (Nat.card T₃) (2 ^ 10) :=
      Nat.Coprime.pow_right 10 (Nat.coprime_two_right.mpr hodd)
    have h3 : Nat.card T₃ ∣ 3 := (Nat.Coprime.dvd_mul_left hcop).mp hdvd
    have hne1 : Nat.card T₃ ≠ 1 := fun h1 => hT₃1 (Subgroup.eq_bot_of_card_eq _ h1)
    rcases (Nat.dvd_prime Nat.prime_three).mp h3 with h | h
    · exact absurd h hne1
    · exact h
  have hxZ : x ∈ centerIn A₁ := by rw [hS.center_A₁]; exact mem_zpowers x
  have hxA : x ∈ A := hS.le hxZ.1
  have hRK : R ≤ centralizer (A : Set G) := hS.sylowR.le
  have hA₁x : A₁ ≤ centralizer ({x} : Set G) := fun a ha =>
    mem_centralizer_singleton_iff.mpr (mem_centralizer_iff.mp hxZ.2 a ha)
  have hRx : R ≤ centralizer ({x} : Set G) := fun r hr =>
    mem_centralizer_singleton_iff.mpr (mem_centralizer_iff.mp (hRK hr) x hxA).symm
  have hEx : E ≤ centralizer ({x} : Set G) := hFr.E_le.trans (sup_le hA₁x hRx)
  have hxC : x ∈ C := ⟨hxA, mem_centralizer_iff.mpr fun e he =>
    mem_centralizer_singleton_iff.mp (hEx he.1)⟩
  have hxT : x ∈ T₃ := by
    have hxN : zpowers x ≤ normalizer (T₃ : Set G) := zpowers_le.mpr (hCT hxC)
    have h := card_sup_mul_card_inf hxN
    have hx3 : Nat.card (zpowers x) = 3 := by rw [Nat.card_zpowers, hS.order_x]
    rw [hT₃3, hx3] at h
    have h9 : Nat.card (T₃ ⊔ zpowers x : Subgroup G) ∣ 9 := ⟨_, h.symm⟩
    have hle : T₃ ⊔ zpowers x ≤ C := sup_le hT₃C (zpowers_le.mpr hxC)
    have hdvd : Nat.card (T₃ ⊔ zpowers x : Subgroup G) ∣ 2 ^ 10 * 3 :=
      hCcard ▸ Subgroup.card_dvd_of_le hle
    have h3 : Nat.card (T₃ ⊔ zpowers x : Subgroup G) ∣ 3 :=
      Nat.dvd_gcd h9 hdvd |>.trans (by norm_num)
    have heq : T₃ ⊔ zpowers x = T₃ := (eq_of_le_of_card_ge le_sup_left (by
      rw [hT₃3]; exact Nat.le_of_dvd (by norm_num) h3)).symm
    rw [← heq]
    exact mem_sup_right (mem_zpowers x)
  have hDT : D ⊓ T₃ = ⊥ :=
    disjoint_iff.mp (Subgroup.disjoint_of_coprime_natCard (by rw [hDcard, hT₃3]; norm_num))
  have hcomm : ∀ d ∈ D, ∀ t ∈ T₃, d * t = t * d := by
    intro d hd t ht
    have h1 : d * t * d⁻¹ * t⁻¹ ∈ D ⊓ T₃ := by
      refine mem_inf.mpr ⟨?_, mul_mem ((mem_normalizer_iff.mp (hCT (hDC hd)) t).mp ht)
        (inv_mem ht)⟩
      rw [show d * t * d⁻¹ * t⁻¹ = d * (t * d⁻¹ * t⁻¹) by group]
      exact mul_mem hd ((mem_normalizer_iff.mp (hCD (hT₃C ht)) d⁻¹).mp (inv_mem hd))
    rw [hDT, mem_bot] at h1
    calc d * t = d * t * d⁻¹ * t⁻¹ * (t * d) := by group
      _ = t * d := by rw [h1, one_mul]
  have hDx1 : ⁅D, zpowers x⁆ = ⊥ := by
    rw [commutator_eq_bot_iff_le_centralizer]
    intro d hd
    rw [mem_centralizer_iff]
    intro y hy
    exact (hcomm d hd y (zpowers_le.mpr hxT hy)).symm
  rw [hDx] at hDx1
  rw [hDx1, Subgroup.card_bot] at hDcard
  norm_num at hDcard

end Sec3

end Core

namespace Sec3Suz

variable {G : Type} [Group G] [Finite G] {A A₁ R : Subgroup G} {g : G} {E F : Subgroup G} {x : G}

variable {Zs P T Q B₀ : Subgroup G} {z₀ y : G}

theorem mem_A₁_of_forall_not_mem (hSz : Sec3Suz G A A₁ R g E F x Zs P T Q B₀ z₀ y) {z : G}
    (hzE : z ∈ E) (hz : ∀ h : G, z ∉ rightConjugate R h) : z ∈ A₁ := by
  by_contra hzA
  obtain ⟨p, -, hp⟩ := hSz.P_cover z hzE hzA
  exact hz p hp

theorem exists_mem_not_mem_normalizer (hSz : Sec3Suz G A A₁ R g E F x Zs P T Q B₀ z₀ y) :
    ∃ p ∈ P, p ∉ normalizer (A : Set G) := by
  have hS := hSz.setting
  have hFr := hS.frame
  have hNK := AS76b.normalizer_centralizer_eq hS.base.hyp.standard
  have hRK : R ≤ centralizer (A : Set G) := hS.sylowR.le
  obtain ⟨-, -, -, -, hE16, -⟩ := Sec3.frame_inf_A₁ hS
  have hEA : E ⊓ A₁ ≠ ⊥ := fun hb => by
    rw [hb, Subgroup.card_bot] at hE16
    norm_num at hE16
  have hR1 : R ≠ ⊥ := fun hb => by
    have := hFr.cardR
    rw [hb, Subgroup.card_bot] at this
    norm_num at this
  obtain ⟨⟨a, ha⟩, ha1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hEA
  obtain ⟨⟨r, hr⟩, hr1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hR1
  have ha1' : a ≠ 1 := fun h => ha1 (Subtype.ext h)
  have hr1' : r ≠ 1 := fun h => hr1 (Subtype.ext h)
  have haE : a ∈ E := (mem_inf.mp ha).1
  have haA₁ : a ∈ A₁ := (mem_inf.mp ha).2
  have heE : a * r ∈ E := mul_mem haE (hFr.R_le_E hr)
  have heA : a * r ∉ A₁ := by
    intro h
    have hrA : r ∈ R ⊓ A := by
      refine ⟨hr, hS.le ?_⟩
      have := mul_mem (inv_mem haA₁) h
      rwa [inv_mul_cancel_left] at this
    rw [Sec3.R_inf_A hS, mem_bot] at hrA
    exact hr1' hrA
  obtain ⟨p, hpP, hpR⟩ := hSz.P_cover _ heE heA
  refine ⟨p, hpP, fun hpN => ha1' ?_⟩
  have hpK : p⁻¹ ∈ normalizer (centralizer (A : Set G) : Set G) := by
    rw [hNK]
    exact inv_mem hpN
  have heK : a * r ∈ centralizer (A : Set G) := by
    have h1 := (mem_normalizer_iff.mp hpK _).mp (hRK ((mem_rightConjugate_iff _ _ _).mp hpR))
    rwa [show p⁻¹ * (p * (a * r) * p⁻¹) * p⁻¹⁻¹ = a * r by group] at h1
  have haK : a ∈ centralizer (A : Set G) := by
    have := mul_mem heK (inv_mem (hRK hr))
    rwa [mul_inv_cancel_right] at this
  have haZ : (⟨a, hS.le haA₁⟩ : A) ∈ center A := mem_center_iff.mpr fun b =>
    Subtype.ext (mem_centralizer_iff.mp haK b b.2)
  rw [hS.center_eq, mem_bot] at haZ
  exact congrArg Subtype.val haZ

end Sec3Suz

section Core


variable {G : Type} [Group G] [Finite G] {A A₁ R : Subgroup G} {g : G} {E F : Subgroup G} {x : G}

theorem rankTwoHyp_normalizer_of_sec3Suz (h17 : Step17G24Odd) {Zs P T Q B₀ : Subgroup G}
    {z₀ y : G} (hSz : Sec3Suz G A A₁ R g E F x Zs P T Q B₀ z₀ y) {z : G} (hzE : z ∈ E)
    (hz : ∀ h : G, z ∉ rightConjugate R h)
    (hW : AS76b.oddCoreIn (centralizer ({z} : Set G)) ≠ ⊥) :
    normalizer (AS76b.oddCoreIn (centralizer ({z} : Set G)) : Set G) ≠ ⊤ ∧
      A ≤ centralizer (AS76b.oddCoreIn (centralizer ({z} : Set G)) : Set G) ∧
      centralizer ({z} : Set G) ≤
        normalizer (AS76b.oddCoreIn (centralizer ({z} : Set G)) : Set G) ∧
      RankTwoHypNF ↥(normalizer (AS76b.oddCoreIn (centralizer ({z} : Set G)) : Set G))
        (A.subgroupOf (normalizer (AS76b.oddCoreIn (centralizer ({z} : Set G)) : Set G))) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hS := hSz.setting
  have hFr := hS.frame
  have hB := hS.base
  have hstd := hB.hyp.standard
  set K := centralizer (A : Set G) with hKdef
  set W := AS76b.oddCoreIn (centralizer ({z} : Set G)) with hWdef
  set X := AS76b.oddCoreIn K with hXdef
  have hzA₁ := hSz.mem_A₁_of_forall_not_mem hzE hz
  have hWX : W ≤ X := Sec3.oddCoreIn_centralizer_le_of_mem h17 hS hzE (hS.le hzA₁)
  have hXK : X ≤ K := AS76b.oddCoreIn_le K
  have hACX : A ≤ centralizer (X : Set G) := le_centralizer_iff.mp hXK
  have hACW : A ≤ centralizer (W : Set G) := hACX.trans (centralizer_le hWX)
  have hCzW : centralizer ({z} : Set G) ≤ normalizer (W : Set G) :=
    AS76b.le_normalizer_oddCoreIn _
  have hRz : R ≤ centralizer ({z} : Set G) := fun r hr => by
    rw [mem_centralizer_singleton_iff]
    exact congrArg Subtype.val (hFr.elemE.1.is_comm.comm ⟨r, hFr.R_le_E hr⟩ ⟨z, hzE⟩)
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
      rw [← hFr.cardR]
      exact Subgroup.card_dvd_of_le (le_inf hS.sylowR.le hRN)
    exact even_iff_two_dvd.mpr ((by norm_num : 2 ∣ 4).trans h4')
  have hstd₁ := GMS78.standard_subgroupOf hstd hAN heven
  have hnn : ¬ (A.subgroupOf N).Normal := by
    intro hn
    obtain ⟨p, hpP, hpA⟩ := hSz.exists_mem_not_mem_normalizer
    have hpz : p ∈ centralizer ({z} : Set G) := mem_centralizer_singleton_iff.mpr
      (mem_centralizer_iff.mp (hSz.P_cent hpP) z ⟨hzE, hzA₁⟩).symm
    apply hpA
    refine AS76b.mem_normalizer_of_map_conj_le ?_
    rintro _ ⟨a, ha, rfl⟩
    have h1 := hn.conj_mem ⟨a, hAN ha⟩ (mem_subgroupOf.mpr ha) ⟨p, hCzW hpz⟩
    rw [mem_subgroupOf] at h1
    simpa using h1
  have hrank : 2 ≤ Open.pRank 2 (centralizer ((A.subgroupOf N : Subgroup ↥N) : Set ↥N)) := by
    refine CFSG.SectionRank.le_pRank one_lt_two (E := R.subgroupOf N) ?_
      (isElemAbelian_subgroupOf hS.elemR N) ?_
    · intro w hw
      rw [mem_centralizer_iff]
      intro v hv
      exact Subtype.ext (mem_centralizer_iff.mp (hS.sylowR.le (mem_subgroupOf.mp hw)) v
        (mem_subgroupOf.mp hv))
    · rw [show (2 : ℕ) ^ 2 = 4 by norm_num, ← hFr.cardR]
      exact Nat.card_congr (subgroupOfEquivOfLe hRN).toEquiv
  exact ⟨hstd₁, hnn, hrank⟩

end Core

end CFSG.ComponentClassification.AS81
