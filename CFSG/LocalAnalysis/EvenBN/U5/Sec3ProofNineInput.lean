module

public import CFSG.LocalAnalysis.EvenBN.U5.Sec3ProofNineE

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

theorem Hyp.sec39i_A₃_le_B₆ (hGMS : GMSK.GMSUnitarySharpKRankOneStatement) (hd : d.Hyp) :
    d.A₃ ≤ d.B₆ := fun b hb => hd.FB₃_le_B₆ hGMS (mem_sup_right (d.A₃_le_B₃ hb))

theorem Hyp.sec39i_A₃_le_D (hGMS : GMSK.GMSUnitarySharpKRankOneStatement) (hd : d.Hyp)
    (hF : d.F ≤ d.D) : d.A₃ ≤ d.D := by
  intro a ha
  have hodd : Odd (Nat.card d.I₁) :=
    Odd.of_dvd_nat d.odd_card_I (Subgroup.card_dvd_of_le d.I₁_le_I)
  have h2 : IsPGroup 2 d.A₃ := IsPGroup.to_le d.isPGroup_P d.A₃_le_P
  obtain ⟨c, hc, e, he, rfl⟩ :=
    CFSG.LocalAnalysis.EvenBN.TwoF4.exists_mul_inf_centralizer_commutator
      (hd.sec39e_I₁_le_normalizer_A₃) 
      (CFSG.LocalAnalysis.EvenBN.TwoF4.isSolvable_of_isPGroup Nat.prime_two h2)
      (coprime_card_of_odd hodd h2) ha
  have hcA : c ∈ d.A₃ := (mem_inf.1 hc).1
  have hcA₁ : c ∈ d.A₁ := by
    refine hd.sec39e_fpf hGMS hcA fun i hi => ?_
    have : i * c * i⁻¹ * c⁻¹ = 1 := by
      rw [mem_centralizer_iff.1 (mem_inf.1 hc).2 i hi]
      group
    rw [this]
    exact one_mem _
  have heD : e ∈ d.D := Subgroup.commutator_mono (hd.sec39i_A₃_le_B₆ hGMS) le_rfl he
  exact mul_mem (hF (hd.A₁_le_F hcA₁)) heD

theorem Hyp.sec39i_inf_L_FB₃ (hGMS : GMSK.GMSUnitarySharpKRankOneStatement) (hd : d.Hyp)
    {x : G} (hxL : x ∈ d.L) (hx : x ∈ d.F ⊔ d.B₃) : x ∈ d.A₃ := by
  obtain ⟨y, hy, a, ha, hx'⟩ := hd.exists_of_mem_FB₃ hx
  have haL : a ∈ d.L := d.A₃_le_P.trans d.P_le_L ha
  have hFC : ∀ z ∈ d.F, z ∈ d.L → z ∈ d.A₁ := fun z hz hzL => by
    rw [← hd.F_inf_centralizer_t hGMS]
    exact mem_inf.2 ⟨hz, mem_centralizer_singleton_iff.2 (hd.comm_t hzL)⟩
  rcases hx' with rfl | rfl
  · have hyL : y ∈ d.L := by
      have := mul_mem hxL (inv_mem haL)
      simpa using this
    exact mul_mem (d.A₁_le_A₃ (hFC y hy hyL)) ha
  · exfalso
    have hytL : y * d.t ∈ d.L := by
      have := mul_mem hxL (inv_mem haL)
      have e : y * (d.t * a) * a⁻¹ = y * d.t := by group
      rwa [e] at this
    have hc := hd.comm_t hytL
    have hyt : y * d.t = d.t * y := by
      have h1 : (y * d.t) * d.t = d.t * (y * d.t) := hc
      have h2 : d.t * d.t = 1 := hd.t_mul_t
      calc y * d.t = y * d.t * (d.t * d.t) := by rw [h2, mul_one]
        _ = (y * d.t * d.t) * d.t := by group
        _ = (d.t * (y * d.t)) * d.t := by rw [h1]
        _ = d.t * y * (d.t * d.t) := by group
        _ = d.t * y := by rw [h2, mul_one]
    have hyA₁ : y ∈ d.A₁ := by
      rw [← hd.F_inf_centralizer_t hGMS]
      exact mem_inf.2 ⟨hy, mem_centralizer_singleton_iff.2 hyt⟩
    have hyL : y ∈ d.L := d.A₁_le_P.trans d.P_le_L hyA₁
    have htL : d.t ∈ d.L := by
      have := mul_mem (inv_mem hyL) hytL
      simpa using this
    exact hd.t_not_mem_L htL

theorem Hyp.sec39i_conj_N₁ (hGMS : GMSK.GMSUnitarySharpKRankOneStatement) (hd : d.Hyp) {c : G}
    (hc : c ∈ normalizer (d.B₃ : Set G) ⊓ centralizer ({d.t} : Set G)) {n : G}
    (hn : n ∈ d.N₁) : ∃ n' ∈ d.N₁, n'⁻¹ * (c * n * c⁻¹) ∈ d.A₃ := by
  have hcFB : c ∈ normalizer ((d.F ⊔ d.B₃ : Subgroup G) : Set G) :=
    hd.normalizer_B₁_le_normalizer_FB₃ hGMS (hd.normalizer_B₃_le hc.1)
  have hcF : c ∈ normalizer (d.F : Set G) := hd.normalizer_FB₃_le_normalizer_F hGMS hcFB
  have hnF : n ∈ normalizer (d.F : Set G) := hd.N₁_le_normalizer_F hGMS hn
  have hct : c * d.t = d.t * c := mem_centralizer_singleton_iff.1 hc.2
  have htN : d.t ∈ normalizer (d.F : Set G) := hd.t_mem_normalizer_F
  have hx : proj d.F ⟨c, hcF⟩ ∈ HB d ⊓ centralizer ({hd.tB} : Set (Bar d.F)) := by
    refine mem_inf.2 ⟨proj_mem_bar hcFB, mem_centralizer_singleton_iff.2 ?_⟩
    rw [← map_mul, ← map_mul]
    exact congrArg _ (Subtype.ext hct)
  have hg : proj d.F ⟨n, hnF⟩ ∈ AB d := proj_mem_bar hn
  obtain ⟨g', hg', hact⟩ := hd.normalizes_AB hGMS _ hx _ hg
  obtain ⟨⟨n', hn'F⟩, hn'N, rfl⟩ := exists_proj_of_mem_bar hg'
  refine ⟨n', hn'N, ?_⟩
  have hnt : ∀ {m : G}, m ∈ d.N₁ → m * d.t = d.t * m := fun hm =>
    mem_centralizer_singleton_iff.1 (hd.N₁_le hm).2
  have hcomm : ∀ {m : G} (hm : m ∈ d.N₁) (hmF : m ∈ normalizer (d.F : Set G)),
      proj d.F ⟨m, hmF⟩ * hd.tB = hd.tB * proj d.F ⟨m, hmF⟩ := fun hm hmF => by
    rw [← map_mul, ← map_mul]
    exact congrArg _ (Subtype.ext (hnt hm))
  set x : Bar d.F := proj d.F ⟨c, hcF⟩ with hxdef
  set g : Bar d.F := proj d.F ⟨n, hnF⟩ with hgdef
  set p' : Bar d.F := proj d.F ⟨n', hn'F⟩ with hp'def
  have hxt : x * hd.tB = hd.tB * x := mem_centralizer_singleton_iff.1 (mem_inf.1 hx).2
  have hgt : g * hd.tB = hd.tB * g := hcomm hn hnF
  have hp't : p' * hd.tB = hd.tB * p' := hcomm hn'N hn'F
  have hxH : x ∈ HB d := (mem_inf.1 hx).1
  have hgH : g ∈ HB d := bar_mono hd.N₁_le_normalizer_F_sup_B₃ hg
  have hp'H : p' ∈ HB d := proj_mem_bar (hd.N₁_le_normalizer_F_sup_B₃ hn'N)
  have hk : p'⁻¹ * (x * g * x⁻¹) ∈ BB d := by
    refine hd.kernel_bar_le hGMS (mem_inf.2 ⟨mem_inf.2 ⟨?_, ?_⟩, ?_⟩)
    · exact mul_mem (inv_mem hp'H) (mul_mem (mul_mem hxH hgH) (inv_mem hxH))
    · refine mem_centralizer_iff.2 fun w hw => ?_
      have e : p'⁻¹ * (x * g * x⁻¹) * w = w * (p'⁻¹ * (x * g * x⁻¹)) := by
        calc p'⁻¹ * (x * g * x⁻¹) * w
            = p'⁻¹ * (x * g * x⁻¹ * w * (x * g * x⁻¹)⁻¹) * (x * g * x⁻¹) := by group
          _ = p'⁻¹ * (p' * w * p'⁻¹) * (x * g * x⁻¹) := by rw [hact w hw]
          _ = w * (p'⁻¹ * (x * g * x⁻¹)) := by group
      exact e.symm
    · have hcx : Commute x hd.tB := hxt
      have hcg : Commute g hd.tB := hgt
      have hcp : Commute p' hd.tB := hp't
      exact mem_centralizer_singleton_iff.2
        (hcp.inv_left.mul_left ((hcx.mul_left hcg).mul_left hcx.inv_left)).eq
  have hprod : p'⁻¹ * (x * g * x⁻¹) =
      proj d.F ((⟨n', hn'F⟩ : normalizer (d.F : Set G))⁻¹ *
        (⟨c, hcF⟩ * ⟨n, hnF⟩ * (⟨c, hcF⟩ : normalizer (d.F : Set G))⁻¹)) := by
    simp only [map_mul, map_inv, hxdef, hgdef, hp'def]
  rw [hprod] at hk
  have hk' := (mem_bar_iff le_sup_left _).1 hk
  have hk'' : n'⁻¹ * (c * n * c⁻¹) ∈ d.F ⊔ d.B₃ := by simpa using hk'
  have hcL : c ∈ normalizer (d.L : Set G) := hd.centralizer_le_normalizer hc.2
  have hL : n'⁻¹ * (c * n * c⁻¹) ∈ d.L :=
    mul_mem (inv_mem (d.pull_le_L _ hn'N))
      ((mem_normalizer_iff.1 hcL n).1 (d.pull_le_L _ hn))
  exact hd.sec39i_inf_L_FB₃ hGMS hL hk''

theorem Hyp.sec39i_proj_comm (hGMS : GMSK.GMSUnitarySharpKRankOneStatement) (hd : d.Hyp)
    {δ : G} (hδ : δ ∈ d.B₆) {y : Bar d.F} (hy : y ∈ YB d) :
    proj d.F ⟨δ, hd.B₆_le_normalizer_F hGMS hδ⟩ * y =
      y * proj d.F ⟨δ, hd.B₆_le_normalizer_F hGMS hδ⟩ := by
  obtain ⟨⟨a, haF⟩, haX, rfl⟩ := exists_proj_of_mem_bar hy
  exact proj_mul_comm_of_commutator_mem (hd.commutator_B₆_FA₃_mem_F hGMS hδ haX)

theorem Hyp.sec39i_mem_FB₃_of_two (hGMS : GMSK.GMSUnitarySharpKRankOneStatement) (hd : d.Hyp)
    (hZ : CFSG.centerIn d.D = d.F) {c : G}
    (hc : c ∈ normalizer (d.B₃ : Set G) ⊓ centralizer ({d.t} : Set G))
    (hcD : c ∈ normalizer (d.D : Set G)) (hc2 : IsPGroup 2 (zpowers c))
    (hcn : ∀ n ∈ d.N₁, (c * n)⁻¹ * (n * c) ∈ d.D) : c ∈ d.F ⊔ d.B₃ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hDB : d.D ≤ d.B₆ := hd.sec39e_D_le_B₆ hGMS
  have hcFB : c ∈ normalizer ((d.F ⊔ d.B₃ : Subgroup G) : Set G) :=
    hd.normalizer_B₁_le_normalizer_FB₃ hGMS (hd.normalizer_B₃_le hc.1)
  have hcF : c ∈ normalizer (d.F : Set G) := hd.normalizer_FB₃_le_normalizer_F hGMS hcFB
  have hcFA : c ∈ normalizer ((d.F ⊔ d.A₃ : Subgroup G) : Set G) :=
    hd.normalizer_FB₃_le_normalizer_FA₃ hGMS hcFB
  have hFA₃B : d.F ⊔ d.A₃ ≤ d.B₆ :=
    sup_le (le_sup_left.trans (hd.FB₃_le_B₆ hGMS)) (hd.sec39i_A₃_le_B₆ hGMS)
  have hne : ¬ d.F ⊔ d.A₃ ≤ d.F := by
    intro h
    have hA : d.A₃ ≤ d.A₁ := by
      intro a ha
      rw [← hd.F_inf_A₃ hGMS]
      exact mem_inf.2 ⟨h (mem_sup_right ha), ha⟩
    have h1 := Subgroup.card_le_of_le hA
    rw [d.card_A₃, d.card_A₁] at h1
    have h4 : 4 ≤ 2 ^ f := hd.four_le
    have : (2 ^ f) ^ 4 < (2 ^ f) ^ 8 := Nat.pow_lt_pow_right (by omega) (by norm_num)
    omega
  obtain ⟨x, hxH, hxN, hxfix⟩ :=
    CFSG.LocalAnalysis.EvenBN.Common.exists_mem_forall_conj_mem_of_isPGroup (p := 2) hc2
      (IsPGroup.to_le d.isPGroup_B₆ hFA₃B) le_sup_left hne (zpowers_le.2 hcFA)
      (zpowers_le.2 hcF) (hd.FA₃_le_normalizer_F hGMS)
  have hxc := hxfix c (mem_zpowers c)
  have hxN' : x ∈ normalizer (d.F : Set G) := hd.FA₃_le_normalizer_F hGMS hxH
  have hyY : proj d.F ⟨x, hxN'⟩ ∈ YB d := proj_mem_bar hxH
  have hy1 : proj d.F ⟨x, hxN'⟩ ≠ 1 := fun e => hxN (proj_eq_one_iff.1 e)
  have hcy : proj d.F ⟨c, hcF⟩ * proj d.F ⟨x, hxN'⟩ * (proj d.F ⟨c, hcF⟩)⁻¹ =
      proj d.F ⟨x, hxN'⟩ := by
    rw [← map_inv, ← map_mul, ← map_mul]
    symm
    rw [proj_eq_proj_iff]
    simpa using hxc
  have hall : ∀ w ∈ YB d, proj d.F ⟨c, hcF⟩ * w * (proj d.F ⟨c, hcF⟩)⁻¹ = w := by
    intro w hw
    by_cases hw1 : w = 1
    · rw [hw1]
      group
    · obtain ⟨g, hg, hgy⟩ := hd.exists_AB_conj hGMS hyY hw hy1 hw1
      obtain ⟨⟨n, hnF⟩, hnN, rfl⟩ := exists_proj_of_mem_bar hg
      have hδ₀ := hcn n hnN
      have hδD : c * ((c * n)⁻¹ * (n * c))⁻¹ * c⁻¹ ∈ d.D :=
        (mem_normalizer_iff.1 hcD _).1 (inv_mem hδ₀)
      have hδN : c * ((c * n)⁻¹ * (n * c))⁻¹ * c⁻¹ ∈ normalizer (d.F : Set G) :=
        hd.B₆_le_normalizer_F hGMS (hDB hδD)
      have hconj : proj d.F ⟨c, hcF⟩ * proj d.F ⟨n, hnF⟩ * (proj d.F ⟨c, hcF⟩)⁻¹ =
          proj d.F ⟨n, hnF⟩ * proj d.F ⟨_, hδN⟩ := by
        rw [← map_inv, ← map_mul, ← map_mul, ← map_mul]
        congr 1
        apply Subtype.ext
        simp only [coe_mul, coe_inv]
        group
      have hδy := hd.sec39i_proj_comm hGMS (hDB hδD) hyY
      calc proj d.F ⟨c, hcF⟩ * w * (proj d.F ⟨c, hcF⟩)⁻¹
          = (proj d.F ⟨c, hcF⟩ * proj d.F ⟨n, hnF⟩ * (proj d.F ⟨c, hcF⟩)⁻¹) *
            (proj d.F ⟨c, hcF⟩ * proj d.F ⟨x, hxN'⟩ * (proj d.F ⟨c, hcF⟩)⁻¹) *
            (proj d.F ⟨c, hcF⟩ * proj d.F ⟨n, hnF⟩ * (proj d.F ⟨c, hcF⟩)⁻¹)⁻¹ := by
            rw [← hgy]; group
        _ = (proj d.F ⟨n, hnF⟩ * proj d.F ⟨_, hδN⟩) * proj d.F ⟨x, hxN'⟩ *
            (proj d.F ⟨n, hnF⟩ * proj d.F ⟨_, hδN⟩)⁻¹ := by rw [hconj, hcy]
        _ = proj d.F ⟨n, hnF⟩ * (proj d.F ⟨_, hδN⟩ * proj d.F ⟨x, hxN'⟩ *
            (proj d.F ⟨_, hδN⟩)⁻¹) * (proj d.F ⟨n, hnF⟩)⁻¹ := by group
        _ = proj d.F ⟨n, hnF⟩ * proj d.F ⟨x, hxN'⟩ * (proj d.F ⟨n, hnF⟩)⁻¹ := by
            rw [hδy]; group
        _ = w := hgy
  have hcBB : proj d.F ⟨c, hcF⟩ ∈ BB d := by
    refine hd.kernel_bar_le hGMS (mem_inf.2 ⟨mem_inf.2 ⟨proj_mem_bar hcFB, ?_⟩, ?_⟩)
    · refine mem_centralizer_iff.2 fun w hw => ?_
      have := hall w hw
      calc w * proj d.F ⟨c, hcF⟩ = (proj d.F ⟨c, hcF⟩ * w * (proj d.F ⟨c, hcF⟩)⁻¹) *
            proj d.F ⟨c, hcF⟩ := by rw [this]
        _ = proj d.F ⟨c, hcF⟩ * w := by group
    · refine mem_centralizer_singleton_iff.2 ?_
      rw [← map_mul, ← map_mul]
      exact congrArg _ (Subtype.ext (mem_centralizer_singleton_iff.1 hc.2))
  exact (mem_bar_iff le_sup_left ⟨c, hcF⟩).1 hcBB

theorem sec39i_normalizer_D_ne_top (hp : d.CaseHyp) (he : d.Sec39e) :
    normalizer (d.D : Set G) ≠ ⊤ := by
  intro htop
  haveI hD : d.D.Normal := normalizer_eq_top_iff.1 htop
  haveI hsimple : IsSimpleGroup G := hp.hyp.setting.std.simple
  have hD2 : IsPGroup 2 d.D := IsPGroup.to_le d.isPGroup_B₆ (hp.hyp.sec39e_D_le_B₆ hp.gms)
  have hcard := he.card_D
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal d.D with hb | ht
  · rw [hb, Subgroup.card_bot] at hcard
    have : (1 : ℕ) < (2 ^ f) ^ 16 := by
      have : 1 < 2 ^ f := Nat.one_lt_two_pow (by have := hp.hyp.two_le; omega)
      exact Nat.one_lt_pow (by norm_num) this
    omega
  · have hG2 : IsPGroup 2 G := by
      rw [ht] at hD2
      exact hD2.of_equiv Subgroup.topEquiv
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    haveI : Nontrivial G := hsimple.toNontrivial
    haveI : Nontrivial (center G) := hG2.center_nontrivial
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (center G) with hc | hc
    · obtain ⟨z, hz⟩ := exists_ne (1 : center G)
      exact hz (Subtype.ext (Subgroup.mem_bot.1 (hc.le z.2)))
    · obtain ⟨a, b, hab⟩ := hp.hyp.setting.std.nonab
      have : a ∈ center G := by rw [hc]; exact mem_top a
      exact hab ((Subgroup.mem_center_iff.1 this b).symm)

theorem sec39i_kgroup (hp : d.CaseHyp) (he : d.Sec39e) :
    CFSG.SectionRank.IsKGroupCat (Bar d.D) :=
  (CFSG.QuasithinUnique.isKGroupCat_of_kProper hp.hyp.setting.std.kProper
    (sec39i_normalizer_D_ne_top hp he)).quotient _

theorem sec39i_order_two (hp : d.CaseHyp) (he : d.Sec39e)
    (ht : d.t ∈ normalizer (d.D : Set G)) : orderOf (proj d.D ⟨d.t, ht⟩) = 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have ht2 : d.t ^ 2 = 1 := by
    have := pow_orderOf_eq_one d.t
    rwa [hp.hyp.t_two] at this
  refine orderOf_eq_prime ?_ ?_
  · rw [← map_pow]
    have : (⟨d.t, ht⟩ : normalizer (d.D : Set G)) ^ 2 = 1 := Subtype.ext (by simpa using ht2)
    rw [this, map_one]
  · intro h1
    exact he.t_not_mem_D (proj_eq_one_iff.1 h1)

theorem sec39i_centralizes (hp : d.CaseHyp) (ht : d.t ∈ normalizer (d.D : Set G)) :
    proj d.D ⟨d.t, ht⟩ ∈ centralizer ((bar d.D d.N₁ : Subgroup (Bar d.D)) : Set (Bar d.D)) := by
  refine mem_centralizer_iff.2 fun y hy => ?_
  obtain ⟨⟨n, hnD⟩, hnN, rfl⟩ := exists_proj_of_mem_bar hy
  rw [← map_mul, ← map_mul]
  exact congrArg _ (Subtype.ext (mem_centralizer_singleton_iff.1 (hp.hyp.N₁_le hnN).2))

theorem sec39i_field (hp : d.CaseHyp) :
    ∃ (k : Type) (_ : Field k) (_ : Fintype k), Fintype.card k = 2 ^ (2 * f) ∧
      Nonempty (↥(bar d.D d.N₁) ≃* SL(2, k)) := by
  have hd := hp.hyp
  have : CharP K 2 := h.charP
  have hfin := h.finite
  letI : Fintype K := Fintype.ofFinite K
  have hcard : Fintype.card K = 2 ^ (2 * f) := by rw [← Nat.card_eq_fintype_card, h.card]
  refine ⟨K, inferInstance, inferInstance, hcard, ?_⟩
  have h4 : 4 ≤ Fintype.card K := by
    rw [hcard]
    have h2 := hd.two_le
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ (2 * f) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hSL : IsSimpleGroup (SL(2, K)) :=
    GMSK.sl2_isSimpleGroup (CharTwo.two_eq_zero (R := K)) h4
  haveI hsimple : IsSimpleGroup d.N₁ := d.N₁equiv.symm.isSimpleGroup
  let φ : d.N₁ →* Bar d.D := (proj d.D).comp (Subgroup.inclusion hd.N₁_le_normalizer_D)
  have hker : φ.ker = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal φ.ker with h1 | h1
    · exact h1
    · exfalso
      have hND : d.N₁ ≤ d.D := fun n hn => by
        have : (⟨n, hn⟩ : d.N₁) ∈ φ.ker := by rw [h1]; trivial
        exact proj_eq_one_iff.1 (MonoidHom.mem_ker.1 this)
      have h2 : IsPGroup 2 d.N₁ :=
        IsPGroup.to_le (IsPGroup.to_le d.isPGroup_B₆ (hd.sec39e_D_le_B₆ hp.gms)) hND
      haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
      haveI : Nontrivial d.N₁ := hsimple.toNontrivial
      haveI : Nontrivial (center d.N₁) := h2.center_nontrivial
      rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (center d.N₁) with hc | hc
      · obtain ⟨z, hz⟩ := exists_ne (1 : center d.N₁)
        exact hz (Subtype.ext (Subgroup.mem_bot.1 (hc.le z.2)))
      · obtain ⟨x, y, hxy⟩ := GMSK.sl2_exists_mul_ne (K := K)
        have hxc : d.N₁equiv x ∈ center d.N₁ := by rw [hc]; exact mem_top _
        apply hxy
        apply d.N₁equiv.injective
        rw [map_mul, map_mul]
        exact (Subgroup.mem_center_iff.1 hxc (d.N₁equiv y)).symm
  have hinj : Function.Injective φ := (MonoidHom.ker_eq_bot_iff φ).1 hker
  have hrange : bar d.D d.N₁ = φ.range := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact ⟨⟨(y : G), hy⟩, rfl⟩
    · rintro ⟨n, rfl⟩
      exact ⟨Subgroup.inclusion hd.N₁_le_normalizer_D n, n.2, rfl⟩
  exact ⟨(MulEquiv.subgroupCongr hrange).trans
    ((MonoidHom.ofInjective hinj).symm.trans d.N₁equiv.symm)⟩

theorem Hyp.sec39i_B₆_le_normalizer_D (hGMS : GMSK.GMSUnitarySharpKRankOneStatement)
    (hd : d.Hyp) (hF : d.F ≤ d.D) : d.B₆ ≤ normalizer (d.D : Set G) := fun s hs => by
  rcases hd.sec39e_B₆_eq hGMS hF hs with h | ⟨y, hy, rfl⟩
  · exact le_normalizer h
  · exact mul_mem hd.t_mem_normalizer_D (le_normalizer hy)

theorem Hyp.sec39i_mem_normalizer_B₆ (hGMS : GMSK.GMSUnitarySharpKRankOneStatement)
    (hd : d.Hyp) (hF : d.F ≤ d.D) {x : G} (hxD : x ∈ normalizer (d.D : Set G))
    (hxt : (x * d.t)⁻¹ * (d.t * x) ∈ d.D) : x ∈ normalizer (d.B₆ : Set G) := by
  have htB : d.t ∈ d.B₆ := hd.FB₃_le_B₆ hGMS d.t_mem_FB₃
  have hDB : d.D ≤ d.B₆ := hd.sec39e_D_le_B₆ hGMS
  refine mem_normalizer_fintype fun s hs => ?_
  rw [SetLike.mem_coe] at hs ⊢
  rcases hd.sec39e_B₆_eq hGMS hF hs with h | ⟨y, hy, rfl⟩
  · exact hDB ((mem_normalizer_iff.1 hxD s).1 h)
  · have hδ : x * ((x * d.t)⁻¹ * (d.t * x))⁻¹ * x⁻¹ ∈ d.D :=
      (mem_normalizer_iff.1 hxD _).1 (inv_mem hxt)
    have e : x * (d.t * y) * x⁻¹ =
        d.t * ((x * ((x * d.t)⁻¹ * (d.t * x))⁻¹ * x⁻¹) * (x * y * x⁻¹)) := by group
    rw [e]
    exact mul_mem htB (hDB (mul_mem hδ ((mem_normalizer_iff.1 hxD y).1 hy)))

theorem Hyp.sec39i_mem_normalizer_N₁D (hd : d.Hyp) {g : G} (hgD : g ∈ normalizer (d.D : Set G))
    (h : ∀ n ∈ d.N₁, g * n * g⁻¹ ∈ d.N₁ ⊔ d.D) :
    g ∈ normalizer ((d.N₁ ⊔ d.D : Subgroup G) : Set G) := by
  refine mem_normalizer_fintype fun z hz => ?_
  rw [SetLike.mem_coe, ← SetLike.mem_coe, coe_mul_of_left_le_normalizer_right _ _
    hd.N₁_le_normalizer_D] at hz
  obtain ⟨n, hn, e, he, rfl⟩ := hz
  rw [SetLike.mem_coe]
  have e1 : g * (n * e) * g⁻¹ = (g * n * g⁻¹) * (g * e * g⁻¹) := by group
  rw [e1]
  exact mul_mem (h n hn) (mem_sup_right ((mem_normalizer_iff.1 hgD e).1 he))

theorem Hyp.sec39i_normalizes (hGMS : GMSK.GMSUnitarySharpKRankOneStatement) (hd : d.Hyp)
    (hZ : CFSG.centerIn d.D = d.F) (he : d.Sec39e) {x : G} (hxD : x ∈ normalizer (d.D : Set G))
    (hxt : (x * d.t)⁻¹ * (d.t * x) ∈ d.D) :
    x ∈ normalizer ((d.N₁ ⊔ d.D : Subgroup G) : Set G) := by
  have hF := sec39e_F_le_D hZ
  have hxB := hd.sec39i_mem_normalizer_B₆ hGMS hF hxD hxt
  have hxFB : x ∈ normalizer ((d.F ⊔ d.B₃ : Subgroup G) : Set G) := by
    rw [← he.normalizer_eq]; exact hxB
  obtain ⟨c, hc, s, hs, rfl⟩ := hd.exists_mul_B₆_of_mem_normalizer hGMS hxFB
  have hsD : s ∈ normalizer (d.D : Set G) := hd.sec39i_B₆_le_normalizer_D hGMS hF hs
  have hcD : c ∈ normalizer (d.D : Set G) := by
    have := mul_mem hxD (inv_mem hsD)
    simpa using this
  have hA₃D : d.A₃ ≤ d.D := hd.sec39i_A₃_le_D hGMS hF
  refine mul_mem ?_ ?_
  · refine hd.sec39i_mem_normalizer_N₁D hcD fun n hn => ?_
    obtain ⟨n', hn', ha⟩ := hd.sec39i_conj_N₁ hGMS hc hn
    have e : c * n * c⁻¹ = n' * (n'⁻¹ * (c * n * c⁻¹)) := by group
    rw [e]
    exact mul_mem (mem_sup_left hn') (mem_sup_right (hA₃D ha))
  · rcases hd.sec39e_B₆_eq hGMS hF hs with h1 | ⟨y, hy, rfl⟩
    · exact le_normalizer (mem_sup_right h1)
    · have htN : d.t ∈ normalizer ((d.N₁ ⊔ d.D : Subgroup G) : Set G) := by
        refine hd.sec39i_mem_normalizer_N₁D hd.t_mem_normalizer_D fun n hn => ?_
        have hnt : n * d.t = d.t * n := mem_centralizer_singleton_iff.1 (hd.N₁_le hn).2
        have : d.t * n * d.t⁻¹ = n := by rw [← hnt, mul_inv_cancel_right]
        rw [this]
        exact mem_sup_left hn
      exact mul_mem htN (le_normalizer (mem_sup_right hy))

theorem sec39i_normal (hp : d.CaseHyp) (k : d.Know92) (he : d.Sec39e)
    (ht : d.t ∈ normalizer (d.D : Set G)) :
    ((bar d.D d.N₁).subgroupOf
      (centralizer ({proj d.D ⟨d.t, ht⟩} : Set (Bar d.D)))).Normal := by
  obtain ⟨hZ, -⟩ := sec39e_know hp k
  have hHK : bar d.D d.N₁ ≤ centralizer ({proj d.D ⟨d.t, ht⟩} : Set (Bar d.D)) := fun y hy =>
    mem_centralizer_singleton_iff.2 (mem_centralizer_iff.1 (sec39i_centralizes hp ht) y hy)
  rw [Subgroup.normal_subgroupOf_iff_le_normalizer hHK]
  intro kk hkk
  obtain ⟨⟨x, hxD⟩, rfl⟩ := proj_surjective (A := d.D) kk
  have hcomm : proj d.D ⟨x, hxD⟩ * proj d.D ⟨d.t, ht⟩ =
      proj d.D ⟨d.t, ht⟩ * proj d.D ⟨x, hxD⟩ := mem_centralizer_singleton_iff.1 hkk
  have hxt : (x * d.t)⁻¹ * (d.t * x) ∈ d.D := by
    rw [← map_mul, ← map_mul, proj_eq_proj_iff] at hcomm
    simpa using hcomm
  have hnorm := hp.hyp.sec39i_normalizes hp.gms hZ he hxD hxt
  refine mem_normalizer_fintype fun a ha => ?_
  obtain ⟨⟨n, hnD⟩, hnN, rfl⟩ := exists_proj_of_mem_bar (SetLike.mem_coe.1 ha)
  have hxn : x * n * x⁻¹ ∈ d.N₁ ⊔ d.D := (mem_normalizer_iff.1 hnorm n).1 (mem_sup_left hnN)
  rw [← SetLike.mem_coe, coe_mul_of_left_le_normalizer_right _ _
    hp.hyp.N₁_le_normalizer_D] at hxn
  obtain ⟨n₂, hn₂, e₂, he₂, hxe⟩ := hxn
  have hn₂N : n₂ ∈ normalizer (d.D : Set G) := hp.hyp.N₁_le_normalizer_D hn₂
  have hkey : proj d.D ⟨x, hxD⟩ * proj d.D ⟨n, hnD⟩ * (proj d.D ⟨x, hxD⟩)⁻¹ =
      proj d.D ⟨n₂, hn₂N⟩ := by
    rw [← map_inv, ← map_mul, ← map_mul, proj_eq_proj_iff]
    simp only [coe_mul, coe_inv]
    rw [← hxe]
    simpa using he₂
  rw [SetLike.mem_coe, hkey]
  exact proj_mem_bar hn₂

theorem sec39i_rank_of_rank_centralizer {H : Type*} [Group H] [Finite H] {A : Subgroup H}
    {t : H} (ht : orderOf t = 2) (htA : t ∈ centralizer (A : Set H))
    (hrank : ∀ R : Subgroup H, R ≤ centralizer (A : Set H) ⊓ centralizer ({t} : Set H) →
      IsPGroup 2 R → Nat.card R ≤ 2) :
    ∀ P : Subgroup H, P ≤ centralizer (A : Set H) → IsPGroup 2 P → Nat.card P ≤ 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro P hP hP2
  set C := centralizer (A : Set H) with hC
  have htC : zpowers t ≤ C := zpowers_le.2 htA
  have hz2 : IsPGroup 2 (zpowers t) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, ht, pow_one])
  obtain ⟨Q, hQ⟩ := (hz2.of_equiv (subgroupOfEquivOfLe htC).symm).exists_le_sylow
  set Q' : Subgroup H := (Q : Subgroup ↥C).map C.subtype with hQ'
  have hQ'2 : IsPGroup 2 Q' := Q.isPGroup'.map _
  have htQ' : t ∈ Q' := ⟨⟨t, htC (mem_zpowers t)⟩, hQ (mem_subgroupOf.2 (mem_zpowers t)), rfl⟩
  have hQ'C : Q' ≤ C := map_subtype_le _
  have ht1 : t ≠ 1 := by
    intro h1
    rw [h1, orderOf_one] at ht
    omega
  have htt : t * t = 1 := by
    have := pow_orderOf_eq_one t
    rwa [ht, sq] at this
  have hQcard : Nat.card Q' ≤ 2 := by
    have hR := hrank (Q' ⊓ centralizer ({t} : Set H)) (inf_le_inf_right _ hQ'C)
      (IsPGroup.to_le hQ'2 inf_le_left)
    haveI : Nontrivial Q' := ⟨⟨⟨t, htQ'⟩, 1, fun h => ht1 (congrArg Subtype.val h)⟩⟩
    haveI : Nontrivial (center Q') := hQ'2.center_nontrivial
    obtain ⟨z, hz⟩ := exists_ne (1 : center Q')
    have hzc : ((z : Q') : H) * t = t * ((z : Q') : H) := by
      have := Subgroup.mem_center_iff.1 z.2 ⟨t, htQ'⟩
      exact (congrArg Subtype.val this).symm
    have hzR : ((z : Q') : H) ∈ Q' ⊓ centralizer ({t} : Set H) :=
      mem_inf.2 ⟨(z : Q').2, mem_centralizer_singleton_iff.2 hzc⟩
    have hzt : zpowers t ≤ Q' ⊓ centralizer ({t} : Set H) :=
      zpowers_le.2 (mem_inf.2 ⟨htQ', mem_centralizer_singleton_iff.2 rfl⟩)
    have hzpow : zpowers t = Q' ⊓ centralizer ({t} : Set H) := by
      refine Subgroup.eq_of_le_of_card_ge hzt ?_
      rw [Nat.card_zpowers, ht]
      exact hR
    rw [← hzpow] at hzR
    obtain ⟨m, hm⟩ := mem_zpowers_iff.1 hzR
    have hz1 : ((z : Q') : H) = t := by
      rcases zpow_eq_one_or_eq_of_mul_self htt m with h1 | h1
      · exfalso
        apply hz
        apply Subtype.ext
        apply Subtype.ext
        rw [← hm, h1]
        rfl
      · rw [← hm, h1]
    have hQc : Q' ≤ Q' ⊓ centralizer ({t} : Set H) := fun q hq =>
      mem_inf.2 ⟨hq, mem_centralizer_singleton_iff.2 (by
        have := Subgroup.mem_center_iff.1 z.2 ⟨q, hq⟩
        have h2 := congrArg Subtype.val this
        rw [Subgroup.coe_mul, Subgroup.coe_mul] at h2
        simp only [Subgroup.coe_mk] at h2
        rw [hz1] at h2
        exact h2)⟩
    exact (Subgroup.card_le_of_le hQc).trans hR
  have hP' : IsPGroup 2 (P.subgroupOf C) := hP2.of_equiv (subgroupOfEquivOfLe hP).symm
  obtain ⟨Q₂, hPQ₂⟩ := hP'.exists_le_sylow
  have e1 : Nat.card (Q₂ : Subgroup ↥C) = Nat.card (Q : Subgroup ↥C) := by
    rw [Sylow.card_eq_multiplicity, Sylow.card_eq_multiplicity]
  have e2 : Nat.card Q' = Nat.card (Q : Subgroup ↥C) := by
    rw [hQ', card_map_of_injective C.subtype_injective]
  have e3 : Nat.card P = Nat.card (P.subgroupOf C) :=
    (Nat.card_congr (subgroupOfEquivOfLe hP).toEquiv).symm
  have e4 := Subgroup.card_le_of_le hPQ₂
  omega

theorem sec39i_rank_core' (hp : d.CaseHyp) (k : d.Know92) (he : d.Sec39e)
    (ht : d.t ∈ normalizer (d.D : Set G)) (R : Subgroup (Bar d.D))
    (hR : R ≤ centralizer ((bar d.D d.N₁ : Subgroup (Bar d.D)) : Set (Bar d.D)) ⊓
      centralizer ({proj d.D ⟨d.t, ht⟩} : Set (Bar d.D)))
    (hR2 : IsPGroup 2 R) (htR : proj d.D ⟨d.t, ht⟩ ∈ R) : Nat.card R ≤ 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hZ, hS⟩ := sec39e_know hp k
  have hd := hp.hyp
  have hF := sec39e_F_le_D hZ
  have hDB : d.D ≤ d.B₆ := hd.sec39e_D_le_B₆ hp.gms
  have hD2 : IsPGroup 2 d.D := IsPGroup.to_le d.isPGroup_B₆ hDB
  have hRtN : lift R ≤ normalizer (d.D : Set G) := lift_le_normalizer R
  have hDRt : d.D ≤ lift R := le_lift R
  have hRt2 : IsPGroup 2 (lift R) := isPGroup_lift hD2 hR2
  have htRt : d.t ∈ lift R := mem_lift_of_proj_mem (x := ⟨d.t, ht⟩) htR
  have hRB : lift R ≤ d.B₆ := by
    intro r hr
    obtain ⟨hrD, hrR⟩ := mem_lift_iff.1 hr
    have hrt : proj d.D ⟨r, hrD⟩ * proj d.D ⟨d.t, ht⟩ =
        proj d.D ⟨d.t, ht⟩ * proj d.D ⟨r, hrD⟩ :=
      mem_centralizer_singleton_iff.1 (mem_inf.1 (hR hrR)).2
    have hrt' : (r * d.t)⁻¹ * (d.t * r) ∈ d.D := by
      rw [← map_mul, ← map_mul, proj_eq_proj_iff] at hrt
      simpa using hrt
    have hrB₆ := hd.sec39i_mem_normalizer_B₆ hp.gms hF hrD hrt'
    have hrFB : r ∈ normalizer ((d.F ⊔ d.B₃ : Subgroup G) : Set G) := by
      rw [← he.normalizer_eq]
      exact hrB₆
    obtain ⟨c, hc, s, hs, rfl⟩ := hd.exists_mul_B₆_of_mem_normalizer hp.gms hrFB
    have hsRt : s ∈ lift R := by
      rcases hd.sec39e_B₆_eq hp.gms hF hs with h1 | ⟨y, hy, rfl⟩
      · exact hDRt h1
      · exact mul_mem htRt (hDRt hy)
    have hcRt : c ∈ lift R := by
      have := mul_mem hr (inv_mem hsRt)
      simpa using this
    have hcD : c ∈ normalizer (d.D : Set G) := hRtN hcRt
    have hc2 : IsPGroup 2 (zpowers c) := IsPGroup.to_le hRt2 (zpowers_le.2 hcRt)
    have hcn : ∀ n ∈ d.N₁, (c * n)⁻¹ * (n * c) ∈ d.D := by
      intro n hn
      have hnD : n ∈ normalizer (d.D : Set G) := hd.N₁_le_normalizer_D hn
      have hcomm : proj d.D ⟨n, hnD⟩ * proj d.D ⟨c, hcD⟩ =
          proj d.D ⟨c, hcD⟩ * proj d.D ⟨n, hnD⟩ :=
        mem_centralizer_iff.1 (mem_inf.1 (hR (mem_lift_iff.1 hcRt).2)).1 _ (proj_mem_bar hn)
      rw [← map_mul, ← map_mul, proj_eq_proj_iff] at hcomm
      have := inv_mem hcomm
      simpa [mul_inv_rev] using this
    have hcFB' := hd.sec39i_mem_FB₃_of_two hp.gms hZ hc hcD hc2 hcn
    exact mul_mem (hd.FB₃_le_B₆ hp.gms hcFB') hs
  have h1 := Subgroup.card_le_of_le hRB
  rw [card_lift, hd.sec39e_card_B₆ hp.gms hZ hS] at h1
  have hpos : 0 < Nat.card d.D := Nat.card_pos
  exact Nat.le_of_mul_le_mul_right h1 hpos

theorem sec39i_rank_core (hp : d.CaseHyp) (k : d.Know92) (he : d.Sec39e)
    (ht : d.t ∈ normalizer (d.D : Set G)) (R : Subgroup (Bar d.D))
    (hR : R ≤ centralizer ((bar d.D d.N₁ : Subgroup (Bar d.D)) : Set (Bar d.D)) ⊓
      centralizer ({proj d.D ⟨d.t, ht⟩} : Set (Bar d.D)))
    (hR2 : IsPGroup 2 R) : Nat.card R ≤ 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hord := sec39i_order_two hp he ht
  have hz2 : IsPGroup 2 (zpowers (proj d.D ⟨d.t, ht⟩)) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hord, pow_one])
  have htR : zpowers (proj d.D ⟨d.t, ht⟩) ≤ normalizer (R : Set (Bar d.D)) := by
    refine zpowers_le.2 (mem_normalizer_fintype fun r hr => ?_)
    have hc : r * proj d.D ⟨d.t, ht⟩ = proj d.D ⟨d.t, ht⟩ * r :=
      mem_centralizer_singleton_iff.1 (mem_inf.1 (hR hr)).2
    rw [← hc, mul_inv_cancel_right]
    exact hr
  have hR'2 : IsPGroup 2 (zpowers (proj d.D ⟨d.t, ht⟩) ⊔ R : Subgroup (Bar d.D)) :=
    IsPGroup.to_sup_of_normal_right' hz2 hR2 htR
  have hR'le : zpowers (proj d.D ⟨d.t, ht⟩) ⊔ R ≤
      centralizer ((bar d.D d.N₁ : Subgroup (Bar d.D)) : Set (Bar d.D)) ⊓
        centralizer ({proj d.D ⟨d.t, ht⟩} : Set (Bar d.D)) :=
    sup_le (zpowers_le.2 (mem_inf.2 ⟨sec39i_centralizes hp ht,
      mem_centralizer_singleton_iff.2 rfl⟩)) hR
  exact (Subgroup.card_le_of_le le_sup_right).trans
    (sec39i_rank_core' hp k he ht _ hR'le hR'2 (mem_sup_left (mem_zpowers _)))

theorem sec39_input (hp : d.CaseHyp) (k : d.Know92) (he : d.Sec39e) : d.Sec39Input :=
  ⟨hp.hyp.t_mem_normalizer_D, sec39i_kgroup hp he, sec39i_field hp,
    sec39i_order_two hp he hp.hyp.t_mem_normalizer_D,
    sec39i_centralizes hp hp.hyp.t_mem_normalizer_D,
    sec39i_normal hp k he hp.hyp.t_mem_normalizer_D,
    sec39i_rank_of_rank_centralizer (sec39i_order_two hp he hp.hyp.t_mem_normalizer_D)
      (sec39i_centralizes hp hp.hyp.t_mem_normalizer_D)
      fun R hR hR2 => sec39i_rank_core hp k he hp.hyp.t_mem_normalizer_D R hR hR2⟩

end Data

namespace CaseBParts

theorem sec39Input : Sec39InputStatement :=
  fun _ _ _ _ _ _ _ _ hp k he => Data.sec39_input hp k he

end CaseBParts

end CFSG.LocalAnalysis.EvenBN.U5
