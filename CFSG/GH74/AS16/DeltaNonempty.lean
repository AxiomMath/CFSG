module

public import CFSG.GH74.AS16.Delta
public import CFSG.GH74.Uniqueness.Statements
import CFSG.StronglyEmbedded.BenderUnitaryBorel
import CFSG.Models.BenderSuzuki
public import CFSG.Adapters.QiuzhenLegacy.BenderSuzuki.BenderLinearBorel
public import CFSG.Adapters.QiuzhenLegacy.BenderSuzuki.BenderSuzukiBorel

public section

namespace CFSG.GH74.AS16

open Subgroup CFSG CFSG.ComponentClassification.AschbacherTightEmbedding
  CFSG.ComponentClassification.LiteratureLocal.TightCommuting CFSG.ABGLocalTools
  CFSG.GH74.Uniqueness CFSG.Open
open scoped Pointwise

variable {G : Type} [Group G] [Finite G]

theorem mul_self_eq_one_of_orderOf_eq_two {M : Type*} [Group M] {u : M} (h : orderOf u = 2) :
    u * u = 1 := by
  rw [← pow_two, ← h]
  exact pow_orderOf_eq_one u

theorem isPGroup_zpowers_of_mul_self {M : Type*} [Group M] {u : M} (h : u * u = 1) :
    IsPGroup 2 (zpowers u) := by
  intro ⟨g, hg⟩
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hg
  refine ⟨1, ?_⟩
  apply Subtype.ext
  show (u ^ k) ^ (2 ^ 1) = 1
  rw [pow_one, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul]
  simp [pow_two, h]

theorem isSolvable_normalizer_of_cyclic {S D : Subgroup G} (hS2 : IsPGroup 2 S)
    (hD : IsCyclic D) (hSD : S ⊔ D = normalizer (S : Set G)) :
    Group.IsSolvable ↥(normalizer (S : Set G)) := by
  set N := normalizer (S : Set G) with hN
  have hSN : S ≤ N := le_normalizer
  have hDN : D ≤ N := hSD ▸ le_sup_right
  have hnorm : (S.subgroupOf N).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hSN).mpr le_rfl
  have hS' : Group.IsSolvable ↥(S.subgroupOf N) := by
    have h2 : IsPGroup 2 ↥(S.subgroupOf N) := hS2.comap_subtype
    have := h2.isNilpotent
    infer_instance
  have hQ : Group.IsSolvable (↥N ⧸ S.subgroupOf N) := by
    refine Group.isSolvable_of_comm ?_
    have hrep : ∀ q : ↥N ⧸ S.subgroupOf N, ∃ d : ↥D,
        (QuotientGroup.mk' (S.subgroupOf N)) ⟨(d : G), hDN d.2⟩ = q := by
      intro q
      obtain ⟨n, rfl⟩ := QuotientGroup.mk_surjective q
      have hn : (n : G) ∈ ((S ⊔ D : Subgroup G) : Set G) := by
        rw [hSD]
        exact n.2
      rw [Subgroup.coe_mul_of_right_le_normalizer_left S D hDN] at hn
      obtain ⟨s, hs, d, hd, hnd⟩ := hn
      refine ⟨⟨d, hd⟩, ?_⟩
      have hnd' : s * d = (n : G) := hnd
      show (QuotientGroup.mk' (S.subgroupOf N)) ⟨d, hDN hd⟩ =
        (QuotientGroup.mk' (S.subgroupOf N)) n
      rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq]
      show (d : G)⁻¹ * (n : G) ∈ S
      have h1 : (d : G)⁻¹ * (n : G) = d⁻¹ * s * d⁻¹⁻¹ := by
        rw [← hnd', inv_inv]
        group
      rw [h1]
      exact (mem_normalizer_iff.mp ((normalizer (S : Set G)).inv_mem (hDN hd)) s).mp hs
    intro a b
    obtain ⟨d₁, rfl⟩ := hrep a
    obtain ⟨d₂, rfl⟩ := hrep b
    rw [← map_mul, ← map_mul]
    congr 1
    apply Subtype.ext
    have := hD
    have hcomm : (d₁ : G) * d₂ = d₂ * d₁ := congrArg Subtype.val (mul_comm' d₁ d₂)
    exact hcomm
  exact Group.isSolvable_of_ker_le_range (S.subgroupOf N).subtype
    (QuotientGroup.mk' (S.subgroupOf N)) (by rw [QuotientGroup.ker_mk', Subgroup.range_subtype])

theorem bender_borel_data (h : CFSG.BenderSuzuki.IsBenderGroup G) (S : Sylow 2 G) :
    CFSG.Open.fusionStronglyEmbedded (normalizer ((S : Subgroup G) : Set G)) ∧
      Group.IsSolvable ↥(normalizer ((S : Subgroup G) : Set G)) := by
  obtain ⟨q, k, hB⟩ : ∃ q k : ℕ, CFSG.Open.fusionBenderBorel G q k := by
    rcases h with ⟨n, hn, e⟩ | ⟨n, hn, e⟩ | ⟨n, hn, e⟩
    · have : Finite (CFSG.Theory.Comparator.PSL2Model n) := Finite.of_surjective e e.surjective
      exact ⟨_, _, (bender_psl2_borel_full n hn).map_mulEquiv e.symm⟩
    · have hmodel : CFSG.Theory.Comparator.SzModel n = Sz n := CFSG.Models.benderSzModel_eq_sz n
      let e' : G ≃* Sz n := e.trans (MulEquiv.subgroupCongr hmodel)
      have : Finite (Sz n) := Finite.of_surjective e' e'.surjective
      exact ⟨_, _, (bender_suzuki_borel_full n hn).map_mulEquiv e'.symm⟩
    · have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
      have hmodel : CFSG.Theory.Comparator.PSU3Model n = PSU3 2 n :=
          CFSG.Models.benderPSU3Model_eq_psu3 n
      let e' : G ≃* PSU3 2 n := e.trans (MulEquiv.subgroupCongr hmodel)
      have : Finite (PSU3 2 n) := Finite.of_surjective e' e'.surjective
      exact ⟨_, _, (bender_psu3_borel_full n hn).map_mulEquiv e'.symm⟩
  obtain ⟨hSE, ⟨D, hDcyc, -, -, hSD⟩, -⟩ := hB S
  exact ⟨hSE, isSolvable_normalizer_of_cyclic S.isPGroup' hDcyc hSD⟩

theorem delta_nonempty (hZD : S_CorZD) (hs : IsSimpleGroup G) (hnonab : ∃ a b : G, a * b ≠ b * a)
    {L : Subgroup G} (hS : IsStandardSubgroup L) :
    ∃ K' : Subgroup G, InDelta (centralizer (L : Set G)) K' := by
  by_contra hno
  push Not at hno
  set C : Subgroup G := centralizer (L : Set G) with hC
  have hCtight : TightlyEmbedded C := standard_tight hS
  obtain ⟨z, hzC, hz2⟩ := exists_involution_of_even hCtight.1
  have hLz : ∀ l ∈ L, l * z = z * l := fun l hl => mem_centralizer_iff.mp hzC l hl
  have hΔ : ∀ h : G, h ∉ normalizer (C : Set G) → ∀ x : G, orderOf x = 2 →
      x ∈ rightConjugate C h → x ∈ normalizer (C : Set G) → False := by
    intro h hh x hx2 hxh hxN
    apply hno (rightConjugate C h)
    refine ⟨⟨h⁻¹, ?_⟩, fun heq => hh ((rightConjugate_eq_self_iff C h).mp heq), ?_⟩
    · rw [map_conj_eq_rightConjugate, inv_inv]
    · have hmem : x ∈ rightConjugate C h ⊓ normalizer (C : Set G) := ⟨hxh, hxN⟩
      have := Subgroup.orderOf_dvd_natCard _ hmem
      rw [hx2] at this
      exact even_iff_two_dvd.mpr this
  have hstep1 : ∀ x : G, orderOf x = 2 → (∃ h : G, h * x * h⁻¹ ∈ C) → x ∈ normalizer (C : Set G) →
      x ∈ C := by
    rintro x hx2 ⟨h, hh⟩ hxN
    by_cases hhn : h ∈ normalizer (C : Set G)
    · have hconj : rightConjugate C h = C := (rightConjugate_eq_self_iff C h).mpr hhn
      have hxh : x ∈ rightConjugate C h := (mem_rightConjugate_iff C h x).mpr hh
      rw [hconj] at hxh
      exact hxh
    · exact (hΔ h hhn x hx2 ((mem_rightConjugate_iff C h x).mpr hh) hxN).elim
  let Z : Set G := {x | orderOf x = 2 ∧ ∃ h : G, h * x * h⁻¹ ∈ C}
  have hzZ : z ∈ Z := ⟨hz2, 1, by simpa using hzC⟩
  have hZinv : IsInvariantInvolutionSet Z := by
    refine ⟨fun x hx => hx.1, fun x hx g => ⟨?_, ?_⟩⟩
    · calc orderOf (g⁻¹ * x * g) = orderOf ((MulAut.conj g⁻¹) x) := by simp
        _ = orderOf x := (MulAut.conj g⁻¹).orderOf_eq x
        _ = 2 := hx.1
    · obtain ⟨h, hh⟩ := hx.2
      refine ⟨h * g, ?_⟩
      have : (h * g) * (g⁻¹ * x * g) * (h * g)⁻¹ = h * x * h⁻¹ := by group
      rw [this]
      exact hh
  have hMtop : normalizer (C : Set G) ≠ ⊤ := by
    intro htop
    have hnormal : C.Normal := Subgroup.normalizer_eq_top_iff.mp htop
    have hcenter : center G = ⊥ := by
      have : (center G).Normal := inferInstance
      rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (center G) with h | h
      · exact h
      · exfalso
        obtain ⟨a, b, hab⟩ := hnonab
        exact hab ((Subgroup.mem_center_iff.mp (h ▸ mem_top a)) b).symm
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal C with h | h
    · have hcard : Nat.card C = 1 := by rw [h]; exact Subgroup.card_bot
      have := hCtight.1
      rw [hcard] at this
      exact absurd this (by decide)
    · have hL1 : ∀ l ∈ L, l = 1 := by
        intro l hl
        have hcent : l ∈ center G := by
          rw [Subgroup.mem_center_iff]
          intro g
          have : g ∈ C := h ▸ mem_top g
          exact (mem_centralizer_iff.mp this l hl).symm
        rw [hcenter, mem_bot] at hcent
        exact hcent
      have : Nontrivial ↥L := LocalCores.isQuasisimple_nontrivial hS.1
      obtain ⟨a, ha⟩ := exists_ne (1 : ↥L)
      exact ha (Subtype.ext (hL1 a a.2))
  have hPD : IsProductDisconnected Z (normalizer (C : Set G)) := by
    refine ⟨hMtop, ⟨z, hzZ, le_normalizer hzC⟩, ?_, ?_⟩
    · intro x hx hxM g
      have hxC : x ∈ C := hstep1 x hx.1 hx.2 hxM
      constructor
      · intro hgx
        have hxg : g⁻¹ * x * g ∈ Z := hZinv.2 x hx g
        have hw : g⁻¹ * x * g ∈ C := hstep1 _ hxg.1 hxg.2 hgx
        by_contra hgM
        have hgi : g⁻¹ ∉ normalizer (C : Set G) := fun h' =>
          hgM (by simpa using (normalizer (C : Set G)).inv_mem h')
        exact hΔ g⁻¹ hgi x hx.1 ((mem_rightConjugate_iff C g⁻¹ x).mpr (by simpa using hw)) hxM
      · intro hgM
        have : g⁻¹ * x * g⁻¹⁻¹ ∈ C :=
          (mem_normalizer_iff.mp ((normalizer (C : Set G)).inv_mem hgM) x).mp hxC
        exact le_normalizer (by simpa using this)
    · rintro u ⟨hu2, x, hxZ, y, hyZ, hxy, rfl⟩ huM
      obtain ⟨hx2, h, hh⟩ := hxZ
      have hx'2 : orderOf (h * x * h⁻¹) = 2 := by
        calc orderOf (h * x * h⁻¹) = orderOf ((MulAut.conj h) x) := by simp
          _ = orderOf x := (MulAut.conj h).orderOf_eq x
          _ = 2 := hx2
      have hx'y' : (h * x * h⁻¹) * (h * y * h⁻¹) = (h * y * h⁻¹) * (h * x * h⁻¹) := by
        calc (h * x * h⁻¹) * (h * y * h⁻¹) = h * (x * y) * h⁻¹ := by group
          _ = h * (y * x) * h⁻¹ := by rw [hxy]
          _ = (h * y * h⁻¹) * (h * x * h⁻¹) := by group
      have hy'N : h * y * h⁻¹ ∈ normalizer (C : Set G) := by
        have hsq : (h * x * h⁻¹) * (h * x * h⁻¹) = 1 := mul_self_eq_one_of_orderOf_eq_two hx'2
        have hne : zpowers (h * x * h⁻¹) ≠ ⊥ :=
          zpowers_ne_bot_of_ne_one (fun h1 => by rw [h1, orderOf_one] at hx'2; omega)
        exact normalizer_two_subgroup_le C _ hCtight (isPGroup_zpowers_of_mul_self hsq)
          (zpowers_le.mpr hh) hne (mem_normalizer_zpowers_of_commute hx'y'.symm)
      have hy'Z : h * y * h⁻¹ ∈ Z := by
        have := hZinv.2 y hyZ h⁻¹
        simpa using this
      have hy'C : h * y * h⁻¹ ∈ C := hstep1 _ hy'Z.1 hy'Z.2 hy'N
      have hu'C : h * (x * y) * h⁻¹ ∈ C := by
        have : h * (x * y) * h⁻¹ = (h * x * h⁻¹) * (h * y * h⁻¹) := by group
        rw [this]
        exact C.mul_mem hh hy'C
      have huC : x * y ∈ C := hstep1 (x * y) hu2 ⟨h, hu'C⟩ huM
      intro g hg
      have hsq : (x * y) * (x * y) = 1 := mul_self_eq_one_of_orderOf_eq_two hu2
      have hne : zpowers (x * y) ≠ ⊥ :=
        zpowers_ne_bot_of_ne_one (fun h1 => by rw [h1, orderOf_one] at hu2; omega)
      exact normalizer_two_subgroup_le C _ hCtight (isPGroup_zpowers_of_mul_self hsq)
        (zpowers_le.mpr huC) hne (mem_normalizer_zpowers_of_commute (mem_centralizer_singleton_iff.mp hg))
  obtain ⟨hB, S, hMS⟩ := hZD G hs hnonab Z (normalizer (C : Set G)) hZinv hPD
  obtain ⟨hSE, hsolv⟩ := bender_borel_data hB S
  have hzsq : z * z = 1 := mul_self_eq_one_of_orderOf_eq_two hz2
  obtain ⟨P, hzP⟩ := IsPGroup.exists_le_sylow (isPGroup_zpowers_of_mul_self hzsq)
  obtain ⟨y, hy⟩ := MulAction.exists_smul_eq G S P
  have hzP' : z ∈ (y • S : Sylow 2 G).toSubgroup := by
    rw [hy]
    exact hzP (mem_zpowers z)
  rw [Sylow.smul_def] at hzP'
  change z ∈ MulAut.conj y • (S : Subgroup G) at hzP'
  rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem, MulAut.smul_def, MulAut.conj_inv_apply] at hzP'
  set i := y⁻¹ * z * y with hi
  have hiS : i ∈ (S : Subgroup G) := hzP'
  have hi2 : orderOf i = 2 := by
    calc orderOf i = orderOf ((MulAut.conj y⁻¹) z) := by simp [hi]
      _ = orderOf z := (MulAut.conj y⁻¹).orderOf_eq z
      _ = 2 := hz2
  have hiM : i ∈ normalizer ((S : Subgroup G) : Set G) := le_normalizer hiS
  have hCi : ∀ g : G, g * i = i * g → g ∈ normalizer ((S : Subgroup G) : Set G) := by
    intro g hgi
    by_contra hg
    obtain ⟨-, -, hodd⟩ := hSE
    have h1 := hodd g hg
    have hgig : g * i * g⁻¹ = i := by rw [hgi]; group
    have hmem : i ∈ normalizer ((S : Subgroup G) : Set G) ⊓
        (normalizer ((S : Subgroup G) : Set G)).map (MulAut.conj g⁻¹).toMonoidHom :=
      ⟨hiM, (mem_rightConjugate_iff _ g i).mpr (by rw [hgig]; exact hiM)⟩
    have h2 := Subgroup.orderOf_dvd_natCard _ hmem
    rw [hi2] at h2
    exact (Nat.not_even_iff_odd.mpr h1) (even_iff_two_dvd.mpr h2)
  have hLM : ∀ l ∈ L, y⁻¹ * l * y ∈ normalizer ((S : Subgroup G) : Set G) := by
    intro l hl
    apply hCi
    calc (y⁻¹ * l * y) * i = y⁻¹ * (l * z) * y := by simp only [hi]; group
      _ = y⁻¹ * (z * l) * y := by rw [hLz l hl]
      _ = i * (y⁻¹ * l * y) := by simp only [hi]; group
  let f : ↥L →* ↥(normalizer ((S : Subgroup G) : Set G)) :=
    MonoidHom.mk' (fun l => ⟨y⁻¹ * l * y, hLM l l.2⟩) (by
      intro a b
      apply Subtype.ext
      show y⁻¹ * ((a : G) * b) * y = (y⁻¹ * a * y) * (y⁻¹ * b * y)
      group)
  have hf : Function.Injective f := by
    intro a b hab
    have h1 : y⁻¹ * (a : G) * y = y⁻¹ * (b : G) * y := congrArg Subtype.val hab
    apply Subtype.ext
    simpa using h1
  have := hsolv
  have hLsolv : Group.IsSolvable ↥L := Group.isSolvable_of_isSolvable_injective hf
  have : Nontrivial ↥L := LocalCores.isQuasisimple_nontrivial hS.1
  have hlt := Group.IsSolvable.commutator_lt_top_of_nontrivial ↥L
  have hperf : commutator ↥L = ⊤ := by
    have := hS.1.1
    rwa [Group.isPerfect_def] at this
  exact hlt.ne hperf

end CFSG.GH74.AS16
