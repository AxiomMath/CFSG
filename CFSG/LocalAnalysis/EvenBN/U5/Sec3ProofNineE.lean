module

public import CFSG.LocalAnalysis.EvenBN.U5.CaseBSharedPartsB
public import CFSG.LocalAnalysis.EvenBN.U5.CaseBBasic
public import CFSG.LocalAnalysis.EvenBN.U5.Sec3B6Four
public import CFSG.LocalAnalysis.EvenBN.TwoF4.CoprimeProduct
public import CFSG.LocalAnalysis.EvenBN.U5.Sec3M1Nine

public noncomputable section

namespace CFSG.LocalAnalysis.EvenBN.U5

open Subgroup CFSG.Open CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
open CFSG.Blueprint
open CFSG.ABGLocalTools (IsSylowOf)
open CFSG.LocalAnalysis.EvenBN.Common.NormalizerQuotient
open scoped MatrixGroups commutatorElement

namespace Data

variable {G : Type} [Group G] [Finite G] {f : ℕ} {K : Type} [Field K]
  {h : UnitaryFieldData 2 f K} {d : Data G h}

theorem Hyp.sec39e_I₁_le_normalizer_B₆ (hGMS : GMSK.GMSUnitarySharpKRankOneStatement)
    (hd : d.Hyp) : d.I₁ ≤ normalizer (d.B₆ : Set G) := fun i hi =>
  d.normalizer_le_normalizer_B₆ (hd.normalizer_B₁_le_normalizer_FB₃ hGMS
    (hd.I_le_normalizer_B₁ (d.I₁_le_I hi)).1)

theorem Hyp.sec39e_D_le_B₆ (hGMS : GMSK.GMSUnitarySharpKRankOneStatement) (hd : d.Hyp) :
    d.D ≤ d.B₆ :=
  Subgroup.le_normalizer_iff_commutator_le_left.1 (hd.sec39e_I₁_le_normalizer_B₆ hGMS)

theorem Hyp.sec39e_I₁_le_normalizer_F (hGMS : GMSK.GMSUnitarySharpKRankOneStatement)
    (hd : d.Hyp) : d.I₁ ≤ normalizer (d.F : Set G) := fun i hi =>
  hd.normalizer_FB₃_le_normalizer_F hGMS (hd.normalizer_B₁_le_normalizer_FB₃ hGMS
    (hd.I_le_normalizer_B₁ (d.I₁_le_I hi)).1)

theorem Hyp.sec39e_I₁_le_normalizer_A₃ (hd : d.Hyp) : d.I₁ ≤ normalizer (d.A₃ : Set G) :=
  fun i hi => hd.normalizer_B₁_le_normalizer_A₃ (hd.I_le_normalizer_B₁ (d.I₁_le_I hi)).1

theorem Hyp.sec39e_I₁_le_normalizer_A₁ (hd : d.Hyp) : d.I₁ ≤ normalizer (d.A₁ : Set G) :=
  fun i hi => hd.normalizer_B₁_le_normalizer_A₁ (hd.I_le_normalizer_B₁ (d.I₁_le_I hi)).1

theorem sec39e_eq_bot_of_odd {X : Subgroup G} (h2 : IsPGroup 2 X) (ho : Odd (Nat.card X)) :
    X = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.1 h2
  rw [hk] at ho
  have hk0 : k = 0 := by
    by_contra hk0
    exact (Nat.not_even_iff_odd.2 ho) (by
      rw [Nat.even_pow]
      exact ⟨even_two, hk0⟩)
  rw [hk0, pow_zero] at hk
  exact Subgroup.eq_bot_of_card_eq X hk

theorem Hyp.sec39e_fpf (hGMS : GMSK.GMSUnitarySharpKRankOneStatement) (hd : d.Hyp) {a : G}
    (ha : a ∈ d.A₃) (hfix : ∀ i ∈ d.I₁, i * a * i⁻¹ * a⁻¹ ∈ d.A₁) : a ∈ d.A₁ := by
  by_contra hna
  have hNF : ∀ x ∈ d.A₃, x ∈ normalizer (d.F : Set G) := fun x hx =>
    hd.FA₃_le_normalizer_F hGMS (mem_sup_right hx)
  have key : ∀ a' ∈ d.A₃, ∀ i ∈ d.I₁, i * a' * i⁻¹ * a'⁻¹ ∈ d.A₁ := by
    intro a' ha' i hi
    by_cases h1 : a' ∈ d.A₁
    · exact mul_mem ((mem_normalizer_iff.1 (hd.sec39e_I₁_le_normalizer_A₁ hi) a').1 h1)
        (inv_mem h1)
    · have hF_A₃ : d.F ⊓ d.A₃ = d.A₁ := hd.F_inf_A₃ hGMS
      have hiN : i ∈ normalizer (d.F : Set G) := hd.sec39e_I₁_le_normalizer_F hGMS hi
      have hpa1 : proj d.F ⟨a, hNF a ha⟩ ≠ 1 := fun e => hna (by
        rw [← hF_A₃]; exact mem_inf.2 ⟨proj_eq_one_iff.1 e, ha⟩)
      have hpa'1 : proj d.F ⟨a', hNF a' ha'⟩ ≠ 1 := fun e => h1 (by
        rw [← hF_A₃]; exact mem_inf.2 ⟨proj_eq_one_iff.1 e, ha'⟩)
      obtain ⟨g, hg, hga⟩ := hd.exists_AB_conj hGMS (proj_mem_bar (mem_sup_right ha))
        (proj_mem_bar (mem_sup_right ha')) hpa1 hpa'1
      obtain ⟨n, hnN, rfl⟩ := exists_proj_of_mem_bar hg
      have hpn : proj d.F ⟨i, hiN⟩ * proj d.F n * (proj d.F ⟨i, hiN⟩)⁻¹ = proj d.F n := by
        rw [← map_inv, ← map_mul, ← map_mul]
        have : (⟨i, hiN⟩ * n * ⟨i, hiN⟩⁻¹ : normalizer (d.F : Set G)) = n :=
          Subtype.ext (by
            simp only [coe_mul, coe_inv]
            rw [mem_centralizer_iff.1 (d.N₁_le_centralizer_I₁ hnN) i hi, mul_inv_cancel_right])
        rw [this]
      have hpn' : proj d.F ⟨i, hiN⟩ * (proj d.F n)⁻¹ * (proj d.F ⟨i, hiN⟩)⁻¹ =
          (proj d.F n)⁻¹ := by
        calc proj d.F ⟨i, hiN⟩ * (proj d.F n)⁻¹ * (proj d.F ⟨i, hiN⟩)⁻¹
            = (proj d.F ⟨i, hiN⟩ * proj d.F n * (proj d.F ⟨i, hiN⟩)⁻¹)⁻¹ := by group
          _ = (proj d.F n)⁻¹ := by rw [hpn]
      have hfa : proj d.F ⟨i, hiN⟩ * proj d.F ⟨a, hNF a ha⟩ * (proj d.F ⟨i, hiN⟩)⁻¹ =
          proj d.F ⟨a, hNF a ha⟩ := by
        rw [← map_inv, ← map_mul, ← map_mul, proj_eq_proj_iff]
        have hw := hfix i hi
        have hc : (i * a * i⁻¹ * a⁻¹)⁻¹ * a = a * (i * a * i⁻¹ * a⁻¹)⁻¹ :=
          d.A₁_commute_A₃ _ (inv_mem hw) a ha
        have e : (i * a * i⁻¹)⁻¹ * a = (i * a * i⁻¹ * a⁻¹)⁻¹ := by
          calc (i * a * i⁻¹)⁻¹ * a = a⁻¹ * ((i * a * i⁻¹ * a⁻¹)⁻¹ * a) := by group
            _ = a⁻¹ * (a * (i * a * i⁻¹ * a⁻¹)⁻¹) := by rw [hc]
            _ = (i * a * i⁻¹ * a⁻¹)⁻¹ := by group
        simp only [coe_mul, coe_inv]
        rw [e]
        exact inv_mem (hd.A₁_le_F hw)
      have hfa' : proj d.F ⟨i, hiN⟩ * proj d.F ⟨a', hNF a' ha'⟩ *
          (proj d.F ⟨i, hiN⟩)⁻¹ = proj d.F ⟨a', hNF a' ha'⟩ := by
        rw [← hga]
        calc proj d.F ⟨i, hiN⟩ * (proj d.F n * proj d.F ⟨a, hNF a ha⟩ * (proj d.F n)⁻¹) *
              (proj d.F ⟨i, hiN⟩)⁻¹
            = (proj d.F ⟨i, hiN⟩ * proj d.F n * (proj d.F ⟨i, hiN⟩)⁻¹) *
              (proj d.F ⟨i, hiN⟩ * proj d.F ⟨a, hNF a ha⟩ * (proj d.F ⟨i, hiN⟩)⁻¹) *
              (proj d.F ⟨i, hiN⟩ * (proj d.F n)⁻¹ * (proj d.F ⟨i, hiN⟩)⁻¹) := by group
          _ = proj d.F n * proj d.F ⟨a, hNF a ha⟩ * (proj d.F n)⁻¹ := by
            rw [hpn, hpn', hfa]
      have hmem : (i * a' * i⁻¹)⁻¹ * a' ∈ d.F := by
        rw [← map_inv, ← map_mul, ← map_mul, proj_eq_proj_iff] at hfa'
        simpa using hfa'
      have hmem2 : (i * a' * i⁻¹)⁻¹ * a' ∈ d.A₃ :=
        mul_mem (inv_mem ((mem_normalizer_iff.1 (hd.sec39e_I₁_le_normalizer_A₃ hi) a').1 ha')) ha'
      have hz : (i * a' * i⁻¹)⁻¹ * a' ∈ d.A₁ := by
        rw [← hF_A₃]; exact mem_inf.2 ⟨hmem, hmem2⟩
      have hc := d.A₁_commute_A₃ _ (inv_mem hz) a' ha'
      have e : i * a' * i⁻¹ * a'⁻¹ = ((i * a' * i⁻¹)⁻¹ * a')⁻¹ := by
        calc i * a' * i⁻¹ * a'⁻¹ = a' * (a'⁻¹ * (i * a' * i⁻¹)) * a'⁻¹ := by group
          _ = a' * ((i * a' * i⁻¹)⁻¹ * a')⁻¹ * a'⁻¹ := by group
          _ = ((i * a' * i⁻¹)⁻¹ * a')⁻¹ * a' * a'⁻¹ := by rw [← hc]
          _ = ((i * a' * i⁻¹)⁻¹ * a')⁻¹ := by group
      rw [e]
      exact inv_mem hz
  have hI : ∀ i ∈ d.I₁, i ∈ d.B₃ := fun i hi =>
    hd.mem_B₃_of_commutator_mem_A₁ (hd.I_le_normalizer_B₁ (d.I₁_le_I hi))
      fun a' ha' => key a' ha' i hi
  have h2 : IsPGroup 2 d.I₁ := IsPGroup.to_le hd.isPGroup_B₃ (fun i hi => hI i hi)
  have hbot : d.I₁ = ⊥ := sec39e_eq_bot_of_odd h2
    (Odd.of_dvd_nat d.odd_card_I (Subgroup.card_dvd_of_le d.I₁_le_I))
  apply hd.centralizer_I₁_ne_top
  rw [hbot]
  simp

theorem Hyp.sec39e_cB₆ (hGMS : GMSK.GMSUnitarySharpKRankOneStatement) (hd : d.Hyp) {c : G}
    (hc : c ∈ d.B₆) (hfix : ∀ i ∈ d.I₁, i * c * i⁻¹ = c) :
    c ∈ d.F ∨ ∃ y ∈ d.F, c = d.t * y := by
  obtain ⟨ψ, -, hker, -, hequi⟩ := hd.exists_B₆_hom hGMS
  have hF_A₃ : d.F ⊓ d.A₃ = d.A₁ := hd.F_inf_A₃ hGMS
  have hIN : ∀ i ∈ d.I₁, i ∈ normalizer (d.B₃ : Set G) ⊓ centralizer ({d.t} : Set G) :=
    fun i hi => ⟨hd.normalizer_B₁_le (hd.I_le_normalizer_B₁ (d.I₁_le_I hi)).1,
      (hd.I_le_normalizer_B₁ (d.I₁_le_I hi)).2⟩
  have hA₃N : ∀ i ∈ d.I₁, ∀ a ∈ d.A₃, i * a * i⁻¹ ∈ d.A₃ := fun i hi a ha =>
    (mem_normalizer_iff.1 (hd.sec39e_I₁_le_normalizer_A₃ hi) a).1 ha
  obtain ⟨a, ha⟩ := QuotientGroup.mk_surjective (ψ ⟨c, hc⟩)
  have haA₁ : (a : G) ∈ d.A₁ := by
    refine hd.sec39e_fpf hGMS a.2 fun i hi => ?_
    have hs : i * c * i⁻¹ ∈ d.B₆ := by rw [hfix i hi]; exact hc
    have h1 := hequi i (hIN i hi) ⟨c, hc⟩ a hs (hA₃N i hi a a.2) ha.symm
    have h2 : (⟨i * c * i⁻¹, hs⟩ : d.B₆) = ⟨c, hc⟩ := Subtype.ext (hfix i hi)
    rw [h2, ← ha] at h1
    have h3 := QuotientGroup.eq.1 h1
    rw [mem_subgroupOf] at h3
    have h4 : (a : G)⁻¹ * (i * a * i⁻¹) ∈ d.A₁ := h3
    have hc4 := d.A₁_commute_A₃ _ h4 a a.2
    have e : i * (a : G) * i⁻¹ * (a : G)⁻¹ = (a : G)⁻¹ * (i * a * i⁻¹) := by
      calc i * (a : G) * i⁻¹ * (a : G)⁻¹ = (a : G) * ((a : G)⁻¹ * (i * a * i⁻¹)) * (a : G)⁻¹ := by
            group
        _ = ((a : G)⁻¹ * (i * a * i⁻¹)) * (a : G) * (a : G)⁻¹ := by rw [← hc4]
        _ = (a : G)⁻¹ * (i * a * i⁻¹) := by group
    rw [e]
    exact h4
  have hψ1 : ψ ⟨c, hc⟩ = 1 := by
    rw [← ha, QuotientGroup.eq_one_iff, mem_subgroupOf]
    exact haA₁
  have hcFB : c ∈ d.F ⊔ d.B₃ := by
    have : (⟨c, hc⟩ : d.B₆) ∈ ψ.ker := hψ1
    rw [hker, mem_subgroupOf] at this
    exact this
  obtain ⟨y, hy, a'', ha'', hc'⟩ := hd.exists_of_mem_FB₃ hcFB
  have htN : d.t ∈ normalizer (d.F : Set G) := hd.t_mem_normalizer_F
  have htinv : d.t⁻¹ = d.t := hd.t_inv'
  have hiyN : ∀ i ∈ d.I₁, i * y * i⁻¹ ∈ d.F := fun i hi =>
    (mem_normalizer_iff.1 (hd.sec39e_I₁_le_normalizer_F hGMS hi) y).1 hy
  have hit : ∀ i ∈ d.I₁, i * d.t * i⁻¹ = d.t := fun i hi => by
    rw [mem_centralizer_singleton_iff.1 (hIN i hi).2, mul_inv_cancel_right]
  have htF : ∀ x ∈ d.F, d.t⁻¹ * x * d.t ∈ d.F := fun x hx => by
    have := (mem_normalizer_iff.1 (inv_mem htN) x).1 hx
    simpa [inv_inv] using this
  have ha''A₁ : a'' ∈ d.A₁ := by
    refine hd.sec39e_fpf hGMS ha'' fun i hi => ?_
    have hfi := hfix i hi
    rw [← hF_A₃]
    refine mem_inf.2 ⟨?_, mul_mem (hA₃N i hi a'' ha'') (inv_mem ha'')⟩
    rcases hc' with hc' | hc'
    · rw [hc'] at hfi
      have e : i * a'' * i⁻¹ * a''⁻¹ = (i * y * i⁻¹)⁻¹ * y := by
        calc i * a'' * i⁻¹ * a''⁻¹
            = (i * y * i⁻¹)⁻¹ * (i * (y * a'') * i⁻¹) * a''⁻¹ := by group
          _ = (i * y * i⁻¹)⁻¹ * (y * a'') * a''⁻¹ := by rw [hfi]
          _ = (i * y * i⁻¹)⁻¹ * y := by group
      rw [e]
      exact mul_mem (inv_mem (hiyN i hi)) hy
    · rw [hc'] at hfi
      have h5 : i * (y * (d.t * a'')) * i⁻¹ = (i * y * i⁻¹) * d.t * (i * a'' * i⁻¹) := by
        calc i * (y * (d.t * a'')) * i⁻¹
            = (i * y * i⁻¹) * (i * d.t * i⁻¹) * (i * a'' * i⁻¹) := by group
          _ = (i * y * i⁻¹) * d.t * (i * a'' * i⁻¹) := by rw [hit i hi]
      have e : i * a'' * i⁻¹ * a''⁻¹ = d.t⁻¹ * ((i * y * i⁻¹)⁻¹ * y) * d.t := by
        calc i * a'' * i⁻¹ * a''⁻¹
            = d.t⁻¹ * (i * y * i⁻¹)⁻¹ * ((i * y * i⁻¹) * d.t * (i * a'' * i⁻¹)) * a''⁻¹ := by
              group
          _ = d.t⁻¹ * (i * y * i⁻¹)⁻¹ * (y * (d.t * a'')) * a''⁻¹ := by rw [← h5, hfi]
          _ = d.t⁻¹ * ((i * y * i⁻¹)⁻¹ * y) * d.t := by group
      rw [e]
      exact htF _ (mul_mem (inv_mem (hiyN i hi)) hy)
  have hA₁F : a'' ∈ d.F := hd.A₁_le_F ha''A₁
  rcases hc' with hc' | hc'
  · left
    rw [hc']
    exact mul_mem hy hA₁F
  · right
    refine ⟨d.t⁻¹ * (y * a'') * d.t, htF _ (mul_mem hy hA₁F), ?_⟩
    rw [hc']
    have hta : a'' * d.t = d.t * a'' := hd.comm_t (d.A₃_le_P.trans d.P_le_L ha'')
    calc y * (d.t * a'') = y * (a'' * d.t) := by rw [hta]
      _ = d.t * (d.t⁻¹ * (y * a'') * d.t) := by group

theorem Hyp.sec39e_B₆_eq (hGMS : GMSK.GMSUnitarySharpKRankOneStatement) (hd : d.Hyp)
    (hF : d.F ≤ d.D) {s : G} (hs : s ∈ d.B₆) : s ∈ d.D ∨ ∃ x ∈ d.D, s = d.t * x := by
  have hodd : Odd (Nat.card d.I₁) :=
    Odd.of_dvd_nat d.odd_card_I (Subgroup.card_dvd_of_le d.I₁_le_I)
  obtain ⟨c, hc, e, he, rfl⟩ :=
    CFSG.LocalAnalysis.EvenBN.TwoF4.exists_mul_inf_centralizer_commutator
      (hd.sec39e_I₁_le_normalizer_B₆ hGMS)
      (CFSG.LocalAnalysis.EvenBN.TwoF4.isSolvable_of_isPGroup Nat.prime_two d.isPGroup_B₆)
      (coprime_card_of_odd hodd d.isPGroup_B₆) hs
  have hcB : c ∈ d.B₆ := (mem_inf.1 hc).1
  have hfix : ∀ i ∈ d.I₁, i * c * i⁻¹ = c := fun i hi => by
    rw [mem_centralizer_iff.1 (mem_inf.1 hc).2 i hi, mul_inv_cancel_right]
  rcases hd.sec39e_cB₆ hGMS hcB hfix with h1 | ⟨y, hy, rfl⟩
  · exact Or.inl (mul_mem (hF h1) he)
  · exact Or.inr ⟨y * e, mul_mem (hF hy) he, by group⟩

theorem sec39e_know (hp : d.CaseHyp) (k : d.Know92) :
    CFSG.centerIn d.D = d.F ∧ ∀ x ∈ d.D, x * x ∈ d.F := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hPL := hp.hyp.P_le_L₂ hp.gms
  have hP2 : IsPGroup 2 (d.P.subgroupOf d.L₂) := d.isPGroup_P.comap_subtype
  obtain ⟨Q, hQ⟩ := hP2.exists_le_sylow
  have h2 := k.s9_2 ((Q : Subgroup d.L₂).map d.L₂.subtype) ⟨Q, rfl⟩
    (fun x hx => ⟨⟨x, hPL hx⟩, hQ hx, rfl⟩)
  exact ⟨h2.2.2.2.1, h2.2.2.2.2⟩

theorem sec39e_F_le_D (hZ : CFSG.centerIn d.D = d.F) : d.F ≤ d.D := by
  rw [← hZ]
  exact inf_le_left

theorem sec39e_comm_F (hZ : CFSG.centerIn d.D = d.F) {x y : G} (hx : x ∈ d.F) (hy : y ∈ d.D) :
    y * x = x * y := by
  have hx' : x ∈ CFSG.centerIn d.D := by rw [hZ]; exact hx
  exact mem_centralizer_iff.1 (mem_inf.1 hx').2 y hy

theorem sec39e_elemAbMod_D (hZ : CFSG.centerIn d.D = d.F) (hS : ∀ x ∈ d.D, x * x ∈ d.F) :
    ElemAbMod d.F d.D := by
  refine ⟨hS, fun x hx y hy => ?_⟩
  have h1 := hS x hx
  have h2 := hS y hy
  have h3 := hS (x * y) (mul_mem hx hy)
  have hca : (x * x)⁻¹ * y = y * (x * x)⁻¹ :=
    (sec39e_comm_F hZ (inv_mem h1) hy).symm
  have e : x * y * x⁻¹ * y⁻¹ = ((x * y) * (x * y)) * ((x * x)⁻¹ * (y * y)⁻¹) := by
    calc x * y * x⁻¹ * y⁻¹ = x * y * x * ((x * x)⁻¹ * y) * (y * y)⁻¹ := by group
      _ = x * y * x * (y * (x * x)⁻¹) * (y * y)⁻¹ := by rw [hca]
      _ = ((x * y) * (x * y)) * ((x * x)⁻¹ * (y * y)⁻¹) := by group
  show x * y * x⁻¹ * y⁻¹ ∈ d.F
  rw [e]
  exact mul_mem h3 (mul_mem (inv_mem h1) (inv_mem h2))

theorem Hyp.sec39e_not_B₆_le (hGMS : GMSK.GMSUnitarySharpKRankOneStatement) (hd : d.Hyp) :
    ¬ d.B₆ ≤ d.F ⊔ d.B₃ := by
  intro hle
  have h1 := Subgroup.card_le_of_le hle
  rw [hd.card_B₆ hGMS] at h1
  have hpos : 0 < Nat.card (d.F ⊔ d.B₃ : Subgroup G) := Nat.card_pos
  have h4 : 4 ≤ 2 ^ f := hd.four_le
  have h5 : 4 ^ 4 ≤ (2 ^ f) ^ 4 := Nat.pow_le_pow_left h4 4
  have h6 : 1 < (2 ^ f) ^ 4 := by omega
  exact absurd h1 (not_le.2 (lt_mul_of_one_lt_left hpos h6))

theorem Hyp.sec39e_t_not_mem_D (hGMS : GMSK.GMSUnitarySharpKRankOneStatement) (hd : d.Hyp)
    (hZ : CFSG.centerIn d.D = d.F) (hS : ∀ x ∈ d.D, x * x ∈ d.F) : d.t ∉ d.D := by
  intro htD
  have hF := sec39e_F_le_D hZ
  have hE := sec39e_elemAbMod_D hZ hS
  refine hd.sec39e_not_B₆_le hGMS fun s hs => ?_
  have hsD : s ∈ d.D := by
    rcases hd.sec39e_B₆_eq hGMS hF hs with h | ⟨x, hx, rfl⟩
    · exact h
    · exact mul_mem htD hx
  refine hd.mem_FB₃_of_mem_B₆ hGMS hs ?_
  have h1 := hE.2 d.t htD s⁻¹ (inv_mem hsD)
  have e : (s * d.t)⁻¹ * (d.t * s) = d.t * s⁻¹ * d.t⁻¹ * s⁻¹⁻¹ := by
    rw [mul_inv_rev, hd.t_inv']
    group
  rw [e]
  exact h1

theorem Hyp.sec39e_mem_FB₃_of_D (hGMS : GMSK.GMSUnitarySharpKRankOneStatement) (hd : d.Hyp)
    (hZ : CFSG.centerIn d.D = d.F) (hS : ∀ x ∈ d.D, x * x ∈ d.F) {Y : Subgroup G}
    (hY : ElemAbMod d.F Y) {x₀ z : G} (hx₀ : x₀ ∈ d.D) (hz : z ∈ d.D) (hzY : z ∈ Y)
    (hyY : d.t * x₀ ∈ Y) : z ∈ d.F ⊔ d.B₃ := by
  have hE := sec39e_elemAbMod_D hZ hS
  have htN : d.t ∈ normalizer (d.F : Set G) := hd.t_mem_normalizer_F
  have hz' : z ∈ d.B₆ := hd.sec39e_D_le_B₆ hGMS hz
  have hzN : z ∈ normalizer (d.F : Set G) := hd.B₆_le_normalizer_F hGMS hz'
  have hc1 : z * (d.t * x₀) * z⁻¹ * (d.t * x₀)⁻¹ ∈ d.F := hY.2 z hzY _ hyY
  have hc2 : z * x₀ * z⁻¹ * x₀⁻¹ ∈ d.F := hE.2 z hz x₀ hx₀
  have hc3 : d.t * (z * x₀ * z⁻¹ * x₀⁻¹) * d.t⁻¹ ∈ d.F := (mem_normalizer_iff.1 htN _).1 hc2
  have hc4 : z * d.t * z⁻¹ * d.t⁻¹ ∈ d.F := by
    have e : z * d.t * z⁻¹ * d.t⁻¹ = (z * (d.t * x₀) * z⁻¹ * (d.t * x₀)⁻¹) *
        (d.t * (z * x₀ * z⁻¹ * x₀⁻¹) * d.t⁻¹)⁻¹ := by group
    rw [e]
    exact mul_mem hc1 (inv_mem hc3)
  refine hd.mem_FB₃_of_mem_B₆ hGMS hz' ?_
  have hc5 := (mem_normalizer_iff.1 (inv_mem hzN) _).1 hc4
  rw [hd.t_inv'] at hc5
  have e2 : (z * d.t)⁻¹ * (d.t * z) = z⁻¹ * (z * d.t * z⁻¹ * d.t) * z⁻¹⁻¹ := by
    rw [mul_inv_rev, hd.t_inv']
    group
  rw [e2]
  exact hc5

theorem Hyp.sec39e_mem_FB₃_of_tD (hGMS : GMSK.GMSUnitarySharpKRankOneStatement) (hd : d.Hyp)
    (hZ : CFSG.centerIn d.D = d.F) (hS : ∀ x ∈ d.D, x * x ∈ d.F) {x₁ : G} (hx₁ : x₁ ∈ d.D)
    (hsq : (d.t * x₁) * (d.t * x₁) ∈ d.F) : d.t * x₁ ∈ d.F ⊔ d.B₃ := by
  have hx₁B : x₁ ∈ d.B₆ := hd.sec39e_D_le_B₆ hGMS hx₁
  have hcomm : x₁ * ((d.t * x₁) * (d.t * x₁))⁻¹ = ((d.t * x₁) * (d.t * x₁))⁻¹ * x₁ :=
    sec39e_comm_F hZ (inv_mem hsq) hx₁
  have e3 : (x₁ * d.t)⁻¹ * (d.t * x₁) = x₁ * ((d.t * x₁) * (d.t * x₁))⁻¹ * x₁ := by
    simp only [mul_inv_rev, hd.t_inv', inv_inv]
    group
  have hx₁FB : x₁ ∈ d.F ⊔ d.B₃ := by
    refine hd.mem_FB₃_of_mem_B₆ hGMS hx₁B ?_
    rw [e3, hcomm, mul_assoc]
    exact mul_mem (inv_mem hsq) (hS x₁ hx₁)
  exact mul_mem d.t_mem_FB₃ hx₁FB

theorem Hyp.sec39e_le_or_le (hGMS : GMSK.GMSUnitarySharpKRankOneStatement) (hd : d.Hyp)
    (hZ : CFSG.centerIn d.D = d.F) (hS : ∀ x ∈ d.D, x * x ∈ d.F) {Y : Subgroup G}
    (hYB : Y ≤ d.B₆) (hY : ElemAbMod d.F Y) : Y ≤ d.D ∨ Y ≤ d.F ⊔ d.B₃ := by
  by_cases hYD : Y ≤ d.D
  · exact Or.inl hYD
  · right
    have hF := sec39e_F_le_D hZ
    obtain ⟨y, hyY, hyD⟩ := SetLike.not_le_iff_exists.1 hYD
    obtain ⟨x₀, hx₀, rfl⟩ : ∃ x₀ ∈ d.D, y = d.t * x₀ := by
      rcases hd.sec39e_B₆_eq hGMS hF (hYB hyY) with h | h
      · exact absurd h hyD
      · exact h
    intro z hz
    rcases hd.sec39e_B₆_eq hGMS hF (hYB hz) with hzD | ⟨x₁, hx₁, rfl⟩
    · exact hd.sec39e_mem_FB₃_of_D hGMS hZ hS hY hx₀ hzD hz hyY
    · exact hd.sec39e_mem_FB₃_of_tD hGMS hZ hS hx₁ (hY.1 _ hz)

theorem Hyp.sec39e_not_FB₃_le_D (hGMS : GMSK.GMSUnitarySharpKRankOneStatement) (hd : d.Hyp)
    (hZ : CFSG.centerIn d.D = d.F) (hS : ∀ x ∈ d.D, x * x ∈ d.F) : ¬ d.F ⊔ d.B₃ ≤ d.D :=
  fun h => hd.sec39e_t_not_mem_D hGMS hZ hS (h d.t_mem_FB₃)

theorem Hyp.sec39e_not_D_le_FB₃ (hGMS : GMSK.GMSUnitarySharpKRankOneStatement) (hd : d.Hyp)
    (hZ : CFSG.centerIn d.D = d.F) (hS : ∀ x ∈ d.D, x * x ∈ d.F) : ¬ d.D ≤ d.F ⊔ d.B₃ :=
  fun h => hd.sec39e_not_B₆_le hGMS fun s hs => by
    rcases hd.sec39e_B₆_eq hGMS (sec39e_F_le_D hZ) hs with h1 | ⟨x, hx, rfl⟩
    · exact h h1
    · exact mul_mem d.t_mem_FB₃ (h hx)

theorem Hyp.sec39e_maximal (hGMS : GMSK.GMSUnitarySharpKRankOneStatement) (hd : d.Hyp)
    (hZ : CFSG.centerIn d.D = d.F) (hS : ∀ x ∈ d.D, x * x ∈ d.F) (X : Subgroup G) :
    Maximal (fun Y : Subgroup G => d.F ≤ Y ∧ Y ≤ d.B₆ ∧ ElemAbMod d.F Y) X ↔
      X = d.F ⊔ d.B₃ ∨ X = d.D := by
  have hDmem : d.F ≤ d.D ∧ d.D ≤ d.B₆ ∧ ElemAbMod d.F d.D :=
    ⟨sec39e_F_le_D hZ, hd.sec39e_D_le_B₆ hGMS, sec39e_elemAbMod_D hZ hS⟩
  have hBmem : d.F ≤ d.F ⊔ d.B₃ ∧ d.F ⊔ d.B₃ ≤ d.B₆ ∧ ElemAbMod d.F (d.F ⊔ d.B₃) :=
    ⟨le_sup_left, hd.FB₃_le_B₆ hGMS, hd.elemAbMod_F_FB₃⟩
  constructor
  · rintro ⟨⟨hXF, hXB, hXE⟩, hmax⟩
    rcases hd.sec39e_le_or_le hGMS hZ hS hXB hXE with h | h
    · exact Or.inr (le_antisymm h (hmax hDmem h))
    · exact Or.inl (le_antisymm h (hmax hBmem h))
  · rintro (rfl | rfl)
    · refine ⟨hBmem, fun Y hY hle => ?_⟩
      rcases hd.sec39e_le_or_le hGMS hZ hS hY.2.1 hY.2.2 with h | h
      · exact absurd (hle.trans h) (hd.sec39e_not_FB₃_le_D hGMS hZ hS)
      · exact h
    · refine ⟨hDmem, fun Y hY hle => ?_⟩
      rcases hd.sec39e_le_or_le hGMS hZ hS hY.2.1 hY.2.2 with h | h
      · exact h
      · exact absurd (hle.trans h) (hd.sec39e_not_D_le_FB₃ hGMS hZ hS)

theorem sec39e_mem_of_comm_mem {A : Subgroup G} {s s' : G} (hs : s ∈ normalizer (A : Set G))
    (hs' : s' ∈ normalizer (A : Set G)) (h : s * s' * s⁻¹ * s'⁻¹ ∈ A) :
    (s * s')⁻¹ * (s' * s) ∈ A := by
  have h1 := proj_mul_comm_of_commutator_mem (A := A) (x := ⟨s, hs⟩) (y := ⟨s', hs'⟩) h
  have h2 : proj A (⟨s, hs⟩ * ⟨s', hs'⟩) = proj A (⟨s', hs'⟩ * ⟨s, hs⟩) := by
    rw [map_mul, map_mul]
    exact h1
  have := proj_eq_proj_iff.1 h2
  simpa using this

theorem sec39e_comm_cancel {A : Subgroup G} {x w t s : G}
    (hx : x ∈ normalizer (A : Set G)) (hw : w ∈ normalizer (A : Set G))
    (ht : t ∈ normalizer (A : Set G)) (hs : s ∈ normalizer (A : Set G)) (hxwt : x = w * t)
    (h1 : x * s * x⁻¹ * s⁻¹ ∈ A) (h2 : s * w * s⁻¹ * w⁻¹ ∈ A) : s * t * s⁻¹ * t⁻¹ ∈ A := by
  have c1 := proj_mul_comm_of_commutator_mem (A := A) (x := ⟨x, hx⟩) (y := ⟨s, hs⟩) h1
  have c2 := proj_mul_comm_of_commutator_mem (A := A) (x := ⟨s, hs⟩) (y := ⟨w, hw⟩) h2
  have hpx : proj A ⟨x, hx⟩ = proj A ⟨w, hw⟩ * proj A ⟨t, ht⟩ := by
    rw [← map_mul]
    congr 1
    exact Subtype.ext hxwt
  have hpt : proj A ⟨t, ht⟩ = (proj A ⟨w, hw⟩)⁻¹ * proj A ⟨x, hx⟩ := by
    rw [hpx]
    group
  have c3 : Commute (proj A ⟨s, hs⟩) (proj A ⟨t, ht⟩) := by
    rw [hpt]
    exact (Commute.inv_right c2).mul_right c1.symm
  have h3 : proj A ⁅(⟨s, hs⟩ : normalizer (A : Set G)), ⟨t, ht⟩⁆ = 1 := by
    rw [map_commutatorElement]
    exact commutatorElement_eq_one_iff_mul_comm.2 c3
  simpa [commutatorElement_def] using proj_eq_one_iff.1 h3

theorem Hyp.sec39e_comm_F_B₆ (hGMS : GMSK.GMSUnitarySharpKRankOneStatement) (hd : d.Hyp)
    (hZ : CFSG.centerIn d.D = d.F) {x s : G} (hx : x ∈ d.F) (hs : s ∈ d.B₆) :
    x * s * x⁻¹ * s⁻¹ ∈ d.A₁ := by
  rcases hd.sec39e_B₆_eq hGMS (sec39e_F_le_D hZ) hs with h | ⟨y, hy, rfl⟩
  · have hc := sec39e_comm_F hZ hx h
    rw [← hc]
    simp
  · have hcy : y * x⁻¹ = x⁻¹ * y := sec39e_comm_F hZ (inv_mem hx) hy
    have e : x * (d.t * y) * x⁻¹ * (d.t * y)⁻¹ = x * d.t * x⁻¹ * d.t⁻¹ := by
      calc x * (d.t * y) * x⁻¹ * (d.t * y)⁻¹ = x * d.t * (y * x⁻¹) * y⁻¹ * d.t⁻¹ := by group
        _ = x * d.t * (x⁻¹ * y) * y⁻¹ * d.t⁻¹ := by rw [hcy]
        _ = x * d.t * x⁻¹ * d.t⁻¹ := by group
    rw [e]
    have htN : d.t ∈ normalizer (d.F : Set G) := hd.t_mem_normalizer_F
    have hzF : x * d.t * x⁻¹ * d.t⁻¹ ∈ d.F := by
      have h1 := (mem_normalizer_iff.1 htN x⁻¹).1 (inv_mem hx)
      have : x * d.t * x⁻¹ * d.t⁻¹ = x * (d.t * x⁻¹ * d.t⁻¹) := by group
      rw [this]
      exact mul_mem hx h1
    have ht2 : d.t * d.t = 1 := hd.t_mul_t
    have ht2' : d.t⁻¹ * d.t⁻¹ = 1 := by rw [← mul_inv_rev, ht2, inv_one]
    have hz2 := hd.mul_self_eq_one_of_mem_F hGMS hzF
    have hzt : d.t * (x * d.t * x⁻¹ * d.t⁻¹) * d.t⁻¹ = x * d.t * x⁻¹ * d.t⁻¹ := by
      have h1 : d.t * (x * d.t * x⁻¹ * d.t⁻¹) * d.t⁻¹ = (d.t * x * d.t⁻¹) * x⁻¹ := by
        calc d.t * (x * d.t * x⁻¹ * d.t⁻¹) * d.t⁻¹
            = (d.t * x * d.t⁻¹) * (d.t * d.t) * x⁻¹ * (d.t⁻¹ * d.t⁻¹) := by group
          _ = (d.t * x * d.t⁻¹) * x⁻¹ := by rw [ht2, ht2']; simp
      have h2 : (d.t * x * d.t⁻¹) * x⁻¹ = (x * d.t * x⁻¹ * d.t⁻¹)⁻¹ := by group
      rw [h1, h2]
      exact (inv_eq_of_mul_eq_one_right hz2)
    rw [← hd.F_inf_centralizer_t hGMS]
    refine mem_inf.2 ⟨hzF, mem_centralizer_singleton_iff.2 ?_⟩
    calc x * d.t * x⁻¹ * d.t⁻¹ * d.t = (d.t * (x * d.t * x⁻¹ * d.t⁻¹) * d.t⁻¹) * d.t := by
          rw [hzt]
      _ = d.t * (x * d.t * x⁻¹ * d.t⁻¹) := by group

theorem Hyp.sec39e_A₁_le_center (hGMS : GMSK.GMSUnitarySharpKRankOneStatement) (hd : d.Hyp)
    (hZ : CFSG.centerIn d.D = d.F) : d.A₁ ≤ CFSG.centerIn d.B₆ := fun a ha => by
  have haF := hd.A₁_le_F ha
  refine mem_inf.2 ⟨hd.sec39e_D_le_B₆ hGMS (sec39e_F_le_D hZ haF),
    mem_centralizer_iff.2 fun s hs => ?_⟩
  rcases hd.sec39e_B₆_eq hGMS (sec39e_F_le_D hZ) hs with h | ⟨x, hx, rfl⟩
  · exact sec39e_comm_F hZ haF h
  · have h1 := sec39e_comm_F hZ haF hx
    have h2 : a * d.t = d.t * a := hd.comm_t (d.A₁_le_P.trans d.P_le_L ha)
    calc d.t * x * a = d.t * (x * a) := by group
      _ = d.t * (a * x) := by rw [h1]
      _ = (d.t * a) * x := by group
      _ = (a * d.t) * x := by rw [h2]
      _ = a * (d.t * x) := by group

theorem Hyp.sec39e_center_le_F (hGMS : GMSK.GMSUnitarySharpKRankOneStatement) (hd : d.Hyp) :
    CFSG.centerIn d.B₆ ≤ d.F := by
  intro z hz
  have hzB : z ∈ d.B₆ := (mem_inf.1 hz).1
  have hzc : ∀ s ∈ d.B₆, s * z = z * s := fun s hs =>
    mem_centralizer_iff.1 (mem_inf.1 hz).2 s hs
  have htB : d.t ∈ d.B₆ := hd.FB₃_le_B₆ hGMS d.t_mem_FB₃
  have hBN := hd.B₆_le_normalizer_F hGMS
  have hzFB : z ∈ d.F ⊔ d.B₃ := by
    refine hd.mem_FB₃_of_mem_B₆ hGMS hzB (sec39e_mem_of_comm_mem (hBN hzB) (hBN htB) ?_)
    have e : z * d.t * z⁻¹ * d.t⁻¹ = 1 := by
      rw [← hzc d.t htB]
      group
    rw [e]
    exact one_mem _
  obtain ⟨y, hy, a, ha, hz'⟩ := hd.exists_of_mem_FB₃ hzFB
  have haB : ∀ b ∈ d.A₃, b ∈ d.B₆ := fun b hb =>
    hd.FB₃_le_B₆ hGMS (mem_sup_right (d.A₃_le_B₃ hb))
  rcases hz' with rfl | rfl
  · have haA₁ : a ∈ d.A₁ := by
      refine mem_A₁_of_commute d ha fun b hb => ?_
      have h1 := hzc b (haB b hb)
      have h2 : y * b = b * y := mem_centralizer_iff.1 (hd.A₃_le_centralizer_F hb) y hy
      have : y * (b * a) = y * (a * b) := by
        calc y * (b * a) = (y * b) * a := by group
          _ = (b * y) * a := by rw [h2]
          _ = b * (y * a) := by group
          _ = (y * a) * b := h1
          _ = y * (a * b) := by group
      exact mul_left_cancel this
    exact mul_mem hy (hd.A₁_le_F haA₁)
  · exfalso
    apply hd.t_not_mem_centralizer_F hGMS
    have hta : d.t * a ∈ centralizer (d.F : Set G) := by
      refine mem_centralizer_iff.2 fun f hf => ?_
      have h1 := hzc f (hd.FB₃_le_B₆ hGMS (mem_sup_left hf))
      have h2 : f * y = y * f := hd.F_comm hGMS f hf y hy
      have : y * (f * (d.t * a)) = y * ((d.t * a) * f) := by
        calc y * (f * (d.t * a)) = (y * f) * (d.t * a) := by group
          _ = (f * y) * (d.t * a) := by rw [h2]
          _ = f * (y * (d.t * a)) := by group
          _ = (y * (d.t * a)) * f := h1
          _ = y * ((d.t * a) * f) := by group
      exact mul_left_cancel this
    have ha' : a ∈ centralizer (d.F : Set G) := hd.A₃_le_centralizer_F ha
    have e : d.t = (d.t * a) * a⁻¹ := by group
    rw [e]
    exact mul_mem hta (inv_mem ha')

theorem Hyp.sec39e_le_F_of_comm (hGMS : GMSK.GMSUnitarySharpKRankOneStatement) (hd : d.Hyp)
    {x : G} (hxB : x ∈ d.B₆) (hx2 : x * x = 1)
    (hxc : ∀ s ∈ d.B₆, x * s * x⁻¹ * s⁻¹ ∈ d.F) : x ∈ d.F := by
  have hBN := hd.B₆_le_normalizer_F hGMS
  have htB : d.t ∈ d.B₆ := hd.FB₃_le_B₆ hGMS d.t_mem_FB₃
  have hxFB : x ∈ d.F ⊔ d.B₃ := hd.mem_FB₃_of_mem_B₆ hGMS hxB
    (sec39e_mem_of_comm_mem (hBN hxB) (hBN htB) (hxc d.t htB))
  obtain ⟨y, hy, a, ha, hx'⟩ := hd.exists_of_mem_FB₃ hxFB
  have hya : ∀ b ∈ d.A₃, y * b = b * y := fun b hb =>
    mem_centralizer_iff.1 (hd.A₃_le_centralizer_F hb) y hy
  rcases hx' with rfl | rfl
  · have hy2 : y * y = 1 := hd.mul_self_eq_one_of_mem_F hGMS hy
    have ha2 : a * a = 1 := by
      have e : (y * a) * (y * a) = (y * y) * (a * a) := by
        calc (y * a) * (y * a) = y * (a * y) * a := by group
          _ = y * (y * a) * a := by rw [← hya a ha]
          _ = (y * y) * (a * a) := by group
      rw [e, hy2, one_mul] at hx2
      exact hx2
    have haA₁ : a ∈ d.A₁ := by
      have : a ∈ closure {g | g ∈ d.A₃ ∧ g * g = 1} := subset_closure ⟨ha, ha2⟩
      rwa [d.sec2_2_three.1] at this
    exact mul_mem hy (hd.A₁_le_F haA₁)
  · exfalso
    apply hd.sec39e_not_B₆_le hGMS
    intro s hs
    have hw : y * a ∈ d.F ⊔ d.A₃ := mul_mem (mem_sup_left hy) (mem_sup_right ha)
    have hwN : y * a ∈ normalizer (d.F : Set G) := hd.FA₃_le_normalizer_F hGMS hw
    have hxwt : y * (d.t * a) = (y * a) * d.t := by
      have hta : a * d.t = d.t * a := hd.comm_t (d.A₃_le_P.trans d.P_le_L ha)
      calc y * (d.t * a) = y * (a * d.t) := by rw [hta]
        _ = (y * a) * d.t := by group
    have h2 : s * (y * a) * s⁻¹ * (y * a)⁻¹ ∈ d.F := hd.commutator_B₆_FA₃_mem_F hGMS hs hw
    have h3 := sec39e_comm_cancel (hBN hxB) hwN (hBN htB) (hBN hs) hxwt (hxc s hs) h2
    exact hd.mem_FB₃_of_mem_B₆ hGMS hs (sec39e_mem_of_comm_mem (hBN hs) (hBN htB) h3)

theorem Hyp.sec39e_normalizer_le_F (hGMS : GMSK.GMSUnitarySharpKRankOneStatement) (hd : d.Hyp)
    (hZ : CFSG.centerIn d.D = d.F) {g : G} (hg : g ∈ normalizer (d.B₆ : Set G)) :
    g ∈ normalizer (d.F : Set G) := by
  refine mem_normalizer_fintype fun x hx => ?_
  have hxB : x ∈ d.B₆ := hd.sec39e_D_le_B₆ hGMS (sec39e_F_le_D hZ hx)
  refine hd.sec39e_le_F_of_comm hGMS ((mem_normalizer_iff.1 hg x).1 hxB) ?_ ?_
  · calc g * x * g⁻¹ * (g * x * g⁻¹) = g * (x * x) * g⁻¹ := by group
      _ = 1 := by rw [hd.mul_self_eq_one_of_mem_F hGMS hx]; simp
  · intro s hs
    have hs' : g⁻¹ * s * g ∈ d.B₆ := by
      have := (mem_normalizer_iff.1 (inv_mem hg) s).1 hs
      simpa using this
    have h1 : x * (g⁻¹ * s * g) * x⁻¹ * (g⁻¹ * s * g)⁻¹ ∈ CFSG.centerIn d.B₆ :=
      hd.sec39e_A₁_le_center hGMS hZ (hd.sec39e_comm_F_B₆ hGMS hZ hx hs')
    have h2 := conj_mem_centerIn hg h1
    have e : g * x * g⁻¹ * s * (g * x * g⁻¹)⁻¹ * s⁻¹ =
        g * (x * (g⁻¹ * s * g) * x⁻¹ * (g⁻¹ * s * g)⁻¹) * g⁻¹ := by group
    rw [e]
    exact hd.sec39e_center_le_F hGMS h2

theorem sec39e_conj_pred {B F : Subgroup G} {g : G} (hg : g ∈ normalizer (B : Set G))
    (hgF : g ∈ normalizer (F : Set G)) {Y : Subgroup G}
    (hY : F ≤ Y ∧ Y ≤ B ∧ ElemAbMod F Y) :
    F ≤ Y.map (MulAut.conj g).toMonoidHom ∧ Y.map (MulAut.conj g).toMonoidHom ≤ B ∧
      ElemAbMod F (Y.map (MulAut.conj g).toMonoidHom) := by
  have hF : F.map (MulAut.conj g).toMonoidHom = F := map_conj_eq_of_mem_normalizer hgF
  have hB : B.map (MulAut.conj g).toMonoidHom = B := map_conj_eq_of_mem_normalizer hg
  refine ⟨?_, ?_, ?_⟩
  · calc F = F.map (MulAut.conj g).toMonoidHom := hF.symm
      _ ≤ Y.map (MulAut.conj g).toMonoidHom := Subgroup.map_mono hY.1
  · calc Y.map (MulAut.conj g).toMonoidHom ≤ B.map (MulAut.conj g).toMonoidHom :=
          Subgroup.map_mono hY.2.1
      _ = B := hB
  · have := hY.2.2.map_conj g
    rwa [hF] at this

theorem Hyp.sec39e_card_B₆ (hGMS : GMSK.GMSUnitarySharpKRankOneStatement) (hd : d.Hyp)
    (hZ : CFSG.centerIn d.D = d.F) (hS : ∀ x ∈ d.D, x * x ∈ d.F) :
    Nat.card d.B₆ = 2 * Nat.card d.D := by
  have hF := sec39e_F_le_D hZ
  have htD : zpowers d.t ≤ normalizer (d.D : Set G) := zpowers_le.2 hd.t_mem_normalizer_D
  have hsup : d.D ⊔ zpowers d.t = d.B₆ := by
    refine le_antisymm (sup_le (hd.sec39e_D_le_B₆ hGMS) (zpowers_le.2
      (hd.FB₃_le_B₆ hGMS d.t_mem_FB₃))) fun s hs => ?_
    rcases hd.sec39e_B₆_eq hGMS hF hs with h | ⟨x, hx, rfl⟩
    · exact mem_sup_left h
    · exact mul_mem (mem_sup_right (mem_zpowers _)) (mem_sup_left hx)
  have hinf : d.D ⊓ zpowers d.t = ⊥ := by
    refine eq_bot_iff.2 fun x hx => ?_
    obtain ⟨k, hk⟩ := mem_zpowers_iff.1 (mem_inf.1 hx).2
    rcases zpow_eq_one_or_eq_of_mul_self hd.t_mul_t k with h1 | h1
    · rw [← hk, h1]
      exact one_mem _
    · exact absurd (h1 ▸ hk ▸ (mem_inf.1 hx).1) (hd.sec39e_t_not_mem_D hGMS hZ hS)
  have := CFSG.LocalAnalysis.EvenBN.Common.card_sup_mul_card_inf_eq htD
  rw [hsup, hinf, Subgroup.card_bot, mul_one, hd.card_zpowers_t] at this
  rw [this, mul_comm]

theorem Hyp.sec39e_card_FB₃_lt (hGMS : GMSK.GMSUnitarySharpKRankOneStatement) (hd : d.Hyp)
    (hZ : CFSG.centerIn d.D = d.F) (hS : ∀ x ∈ d.D, x * x ∈ d.F) :
    Nat.card (d.F ⊔ d.B₃ : Subgroup G) < Nat.card d.D := by
  have h1 := hd.sec39e_card_B₆ hGMS hZ hS
  rw [hd.card_B₆ hGMS] at h1
  have hpos : 0 < Nat.card (d.F ⊔ d.B₃ : Subgroup G) := Nat.card_pos
  have h4 : 4 ≤ 2 ^ f := hd.four_le
  have h5 : 4 ^ 4 ≤ (2 ^ f) ^ 4 := Nat.pow_le_pow_left h4 4
  generalize (2 ^ f) ^ 4 = Q at h1 h5
  nlinarith

theorem Hyp.sec39e_normalizer_le (hGMS : GMSK.GMSUnitarySharpKRankOneStatement) (hd : d.Hyp)
    (hZ : CFSG.centerIn d.D = d.F) (hS : ∀ x ∈ d.D, x * x ∈ d.F) {g : G}
    (hg : g ∈ normalizer (d.B₆ : Set G)) :
    g ∈ normalizer ((d.F ⊔ d.B₃ : Subgroup G) : Set G) := by
  have hgF := hd.sec39e_normalizer_le_F hGMS hZ hg
  have hPFB : d.F ≤ d.F ⊔ d.B₃ ∧ d.F ⊔ d.B₃ ≤ d.B₆ ∧ ElemAbMod d.F (d.F ⊔ d.B₃) :=
    ⟨le_sup_left, hd.FB₃_le_B₆ hGMS, hd.elemAbMod_F_FB₃⟩
  have hPD : d.F ≤ d.D ∧ d.D ≤ d.B₆ ∧ ElemAbMod d.F d.D :=
    ⟨sec39e_F_le_D hZ, hd.sec39e_D_le_B₆ hGMS, sec39e_elemAbMod_D hZ hS⟩
  have hY := sec39e_conj_pred hg hgF hPFB
  rcases hd.sec39e_le_or_le hGMS hZ hS hY.2.1 hY.2.2 with h | h
  · exfalso
    have hD' := sec39e_conj_pred (inv_mem hg) (inv_mem hgF) hPD
    have hFBD' : d.F ⊔ d.B₃ ≤ d.D.map (MulAut.conj g⁻¹).toMonoidHom := fun z hz =>
      ⟨g * z * g⁻¹, h ⟨z, hz, rfl⟩, by
        show g⁻¹ * (g * z * g⁻¹) * g⁻¹⁻¹ = z
        group⟩
    have hcard : Nat.card (d.D.map (MulAut.conj g⁻¹).toMonoidHom) = Nat.card d.D :=
      Subgroup.card_map_of_injective (MulAut.conj g⁻¹).injective
    rcases hd.sec39e_le_or_le hGMS hZ hS hD'.2.1 hD'.2.2 with h' | h'
    · have heq : d.D.map (MulAut.conj g⁻¹).toMonoidHom = d.D :=
        Subgroup.eq_of_le_of_card_ge h' hcard.ge
      exact hd.sec39e_not_FB₃_le_D hGMS hZ hS (heq ▸ hFBD')
    · have := Subgroup.card_le_of_le h'
      rw [hcard] at this
      exact absurd (hd.sec39e_card_FB₃_lt hGMS hZ hS) (not_lt.2 this)
  · exact mem_normalizer_fintype fun z hz => h ⟨z, hz, rfl⟩

theorem Hyp.sec39e_card_D (hGMS : GMSK.GMSUnitarySharpKRankOneStatement) (hd : d.Hyp)
    (hZ : CFSG.centerIn d.D = d.F) (hS : ∀ x ∈ d.D, x * x ∈ d.F) :
    Nat.card d.D = (2 ^ f) ^ 16 := by
  have h1 := hd.sec39e_card_B₆ hGMS hZ hS
  rw [hd.card_B₆ hGMS, hd.card_FB₃ hGMS] at h1
  have h2 : (2 ^ f) ^ 4 * (2 * (2 ^ f) ^ 12) = 2 * (2 ^ f) ^ 16 := by ring
  rw [h2] at h1
  exact (Nat.eq_of_mul_eq_mul_left (by norm_num : 0 < 2) h1).symm

theorem Hyp.sec39e_A₁_inf_centralizer_I₁ (hd : d.Hyp) {a : G} (ha : a ∈ d.A₁)
    (hc : a ∈ centralizer (d.I₁ : Set G)) : a = 1 := by
  have h := (d.sec2_1_two hd.two_le).2.2.2.2.2.2.2.2.2.2.2.2
  have : a ∈ d.A₃ ⊓ (d.P ⊓ centralizer (d.I₁ : Set G)) :=
    mem_inf.2 ⟨d.A₁_le_A₃ ha, mem_inf.2 ⟨d.A₁_le_P ha, hc⟩⟩
  rw [h] at this
  exact mem_bot.1 this

theorem Hyp.sec39e_F_inf_centralizer_I₁ (hGMS : GMSK.GMSUnitarySharpKRankOneStatement)
    (hd : d.Hyp) (hZ : CFSG.centerIn d.D = d.F) {x : G} (hx : x ∈ d.F)
    (hc : x ∈ centralizer (d.I₁ : Set G)) : x = 1 := by
  have htB : d.t ∈ d.B₆ := hd.FB₃_le_B₆ hGMS d.t_mem_FB₃
  have hz := hd.sec39e_comm_F_B₆ hGMS hZ hx htB
  have hzc : x * d.t * x⁻¹ * d.t⁻¹ ∈ centralizer (d.I₁ : Set G) := by
    refine mem_centralizer_iff.2 fun i hi => ?_
    have h1 : Commute i x := mem_centralizer_iff.1 hc i hi
    have h2 : Commute i d.t :=
      mem_centralizer_singleton_iff.1 (hd.I_le_normalizer_B₁ (d.I₁_le_I hi)).2
    exact (((h1.mul_right h2).mul_right h1.inv_right).mul_right h2.inv_right).eq
  have hz1 := hd.sec39e_A₁_inf_centralizer_I₁ hz hzc
  have hxt : x * d.t = d.t * x := by
    have : x * d.t * x⁻¹ * d.t⁻¹ = 1 := hz1
    calc x * d.t = (x * d.t * x⁻¹ * d.t⁻¹) * (d.t * x) := by group
      _ = d.t * x := by rw [this, one_mul]
  have hxA₁ : x ∈ d.A₁ := by
    rw [← hd.F_inf_centralizer_t hGMS]
    exact mem_inf.2 ⟨hx, mem_centralizer_singleton_iff.2 hxt⟩
  exact hd.sec39e_A₁_inf_centralizer_I₁ hxA₁ hc

theorem Hyp.sec39e_D_inf_centralizer_I₁ (hGMS : GMSK.GMSUnitarySharpKRankOneStatement)
    (hd : d.Hyp) (hZ : CFSG.centerIn d.D = d.F) (hS : ∀ x ∈ d.D, x * x ∈ d.F) :
    d.D ⊓ centralizer (d.I₁ : Set G) = ⊥ := by
  refine eq_bot_iff.2 fun x hx => ?_
  obtain ⟨hxD, hxc⟩ := mem_inf.1 hx
  have hfix : ∀ i ∈ d.I₁, i * x * i⁻¹ = x := fun i hi => by
    rw [mem_centralizer_iff.1 hxc i hi, mul_inv_cancel_right]
  rcases hd.sec39e_cB₆ hGMS (hd.sec39e_D_le_B₆ hGMS hxD) hfix with h | ⟨y, hy, rfl⟩
  · exact mem_bot.2 (hd.sec39e_F_inf_centralizer_I₁ hGMS hZ h hxc)
  · exfalso
    apply hd.sec39e_t_not_mem_D hGMS hZ hS
    have e : d.t = (d.t * y) * y⁻¹ := by group
    rw [e]
    exact mul_mem hxD (inv_mem (sec39e_F_le_D hZ hy))

theorem sec39e_of_hyp (hp : d.CaseHyp) (k : d.Know92) : d.Sec39e := by
  obtain ⟨hZ, hS⟩ := sec39e_know hp k
  exact ⟨fun X => hp.hyp.sec39e_maximal hp.gms hZ hS X,
    le_antisymm (fun _ hg => hp.hyp.sec39e_normalizer_le hp.gms hZ hS hg)
      d.normalizer_le_normalizer_B₆,
    hp.hyp.sec39e_t_not_mem_D hp.gms hZ hS, hp.hyp.sec39e_card_D hp.gms hZ hS,
    hp.hyp.sec39e_D_inf_centralizer_I₁ hp.gms hZ hS⟩

end Data

namespace CaseBParts

theorem sec39e : Sec39eStatement :=
  fun _ _ _ _ _ _ _ _ hp k => Data.sec39e_of_hyp hp k

end CaseBParts

end CFSG.LocalAnalysis.EvenBN.U5
