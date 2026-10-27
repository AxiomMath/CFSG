module

public import CFSG.LocalAnalysis.GLTheoremA.CatB.H301CoverDefs
public import CFSG.HardMathSupport.Timmesfeld.Coordinator.LocalThreeSporadicRank
public import CFSG.LocalAnalysis.GLTheoremA.CatB.H301Lift4

public section

namespace CFSG.LocalAnalysis.GLTheoremA.H301

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremA
  CFSG.LocalAnalysis.GLTheoremA.S8 CFSG.LocalAnalysis.GLTheoremB
open CFSG.HardMathSupport.Solomon.LocalBalance (barAut)
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)

section Aut

variable {K : Type} [Group K]

theorem centralizer_range_mulAut_conj_of_perfect
    (hperf : ⁅(⊤ : Subgroup K), (⊤ : Subgroup K)⁆ = ⊤) :
    Subgroup.centralizer ((MulAut.conj : K →* MulAut K).range : Set (MulAut K)) = ⊥ := by
  haveI : Group.IsPerfect K := ⟨hperf⟩
  rw [eq_bot_iff]
  intro α hα
  rw [Subgroup.mem_bot]
  have hcen : ∀ k : K, k⁻¹ * α k ∈ Subgroup.center K := by
    intro k
    rw [Subgroup.mem_center_iff]
    intro g
    have h1 := Subgroup.mem_centralizer_iff.1 hα (MulAut.conj k) ⟨k, rfl⟩
    have h3 : k * g * k⁻¹ = α k * g * (α k)⁻¹ := by
      have h2 := congrArg (fun f : MulAut K => f (α.symm g)) h1
      simp only [MulAut.mul_apply, MulAut.conj_apply, map_mul, map_inv,
        MulEquiv.apply_symm_apply] at h2
      exact h2
    calc g * (k⁻¹ * α k) = k⁻¹ * (k * g * k⁻¹) * α k := by group
      _ = k⁻¹ * (α k * g * (α k)⁻¹) * α k := by rw [h3]
      _ = k⁻¹ * α k * g := by group
  have hid := CFSG.ComponentClassification.PerfectAutomorphisms.hom_eq_id_of_central_displacement
    α.toMonoidHom hcen
  ext k
  exact congrArg (fun f : K →* K => f k) hid

theorem eq_map_conj_of_coverMax [Finite K] (hperf : ⁅(⊤ : Subgroup K), (⊤ : Subgroup K)⁆ = ⊤)
    {A₀ R : Subgroup K}
    (hmax : ∀ (A : Type) [Group A] [Finite A] (ι : K ⧸ Subgroup.center K →* A),
      Function.Injective ι → ι.range.Normal → Subgroup.centralizer (ι.range : Set A) = ⊥ →
      ∀ R' : Subgroup A, IsPGroup 2 R' →
        (A₀.map (centerQuot K)).map ι ≤ Subgroup.normalizer (R' : Set A) →
        (R.map (centerQuot K)).map ι ≤ R' → R' = (R.map (centerQuot K)).map ι)
    (R'' : Subgroup (MulAut K)) (hR''2 : IsPGroup 2 R'')
    (hN : A₀.map (MulAut.conj : K →* MulAut K) ≤ Subgroup.normalizer (R'' : Set (MulAut K)))
    (hRR : R.map (MulAut.conj : K →* MulAut K) ≤ R'') :
    R'' = R.map (MulAut.conj : K →* MulAut K) := by
  haveI : Finite (MulAut K) := finite_mulAut
  have hker : Subgroup.center K = (MulAut.conj : K →* MulAut K).ker := by
    apply le_antisymm
    · intro z hz
      rw [MonoidHom.mem_ker]
      ext y
      rw [MulAut.conj_apply, MulAut.one_apply, ← Subgroup.mem_center_iff.1 hz y,
        mul_inv_cancel_right]
    · intro k hk
      rw [Subgroup.mem_center_iff]
      intro g
      have h := congrArg (fun f : MulAut K => f g) (MonoidHom.mem_ker.1 hk)
      simp only [MulAut.conj_apply, MulAut.one_apply] at h
      calc g * k = k * g * k⁻¹ * k := by rw [h]
        _ = k * g := by group
  set ι : K ⧸ Subgroup.center K →* MulAut K :=
    QuotientGroup.lift (Subgroup.center K) MulAut.conj hker.le
  have hι : ι.comp (centerQuot K) = MulAut.conj := QuotientGroup.lift_comp_mk' _ _ _
  have hmap : ∀ Y : Subgroup K, (Y.map (centerQuot K)).map ι = Y.map MulAut.conj := by
    intro Y
    rw [Subgroup.map_map, hι]
  have hinj : Function.Injective ι := (QuotientGroup.injective_lift_iff _ _ _).2 hker
  have hrange : ι.range = (MulAut.conj : K →* MulAut K).range := by
    rw [← hι, MonoidHom.range_comp, MonoidHom.range_eq_top.2 (QuotientGroup.mk'_surjective _),
      ← MonoidHom.range_eq_map]
  have hn : ι.range.Normal := by
    rw [hrange]
    exact range_mulAut_conj_normal
  have hc : Subgroup.centralizer (ι.range : Set (MulAut K)) = ⊥ := by
    rw [hrange]
    exact centralizer_range_mulAut_conj_of_perfect hperf
  have h := hmax (MulAut K) ι hinj hn hc R'' hR''2 (by rw [hmap]; exact hN)
    (by rw [hmap]; exact hRR)
  rwa [hmap] at h

end Aut

variable {G : Type} [Group G] [Finite G]

theorem card_outer_pQuot_le_two
    (hOut : CFSG.HardMathSupport.Timmesfeld.Coordinator.SporadicOuterLeTwo) {p : ℕ}
    (hp : p.Prime) {X L : Subgroup G} (hL : GLAPComponent p X L) {row : Row}
    (hrow : RowL row p L) : Nat.card (Outer (PQuot p L)) ≤ 2 := by
  obtain ⟨-, hcat, -⟩ := hrow
  haveI : Group.IsPerfect (PQuot p L) := ⟨(isQuasisimple_pQuot_of_glaPComponent hp hL).1⟩
  obtain ⟨hsimple, a, b, hab⟩ := chev_pSimple_simple_nonabelian hp hL
  obtain ⟨i, hi, ⟨f⟩⟩ := hcat
  have hi' : i = .sporadic row.name := hi
  subst hi'
  haveI : Finite (MulAut (PSimple p L)) := finite_mulAut
  have h2 : Nat.card (Outer (PSimple p L)) ≤ 2 :=
    hOut (PSimple p L) hsimple ⟨a, b, hab⟩ row.name ⟨f⟩
  exact (Nat.card_le_card_of_injective _
    (CFSG.ComponentClassification.OuterAutomorphisms.centerQuotient_outer_injective
      (PQuot p L))).trans h2

private theorem map_barAut_eq_map_conj_of_le {p : ℕ} {L Y : Subgroup G} (hY : Y ≤ L) :
    (Y.subgroupOf (Subgroup.normalizer (L : Set G))).map (barAut p L) =
      (lImg p L Y).map (MulAut.conj : PQuot p L →* MulAut (PQuot p L)) := by
  ext α
  constructor
  · rintro ⟨⟨y, hyN⟩, hy, rfl⟩
    have hyL : y ∈ L := hY hy
    refine ⟨pQuotHom p L ⟨y, hyL⟩, ⟨⟨y, hyL⟩, hy, rfl⟩, ?_⟩
    exact (barAut_of_mem hyL).symm
  · rintro ⟨_, ⟨⟨y, hyL⟩, hy, rfl⟩, rfl⟩
    exact ⟨⟨y, Subgroup.le_normalizer hyL⟩, hy, barAut_of_mem hyL⟩

theorem eq_of_le_of_map_barAut_of_odd {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {x : G}
    {L : Subgroup G} (hx : orderOf x = p) (hL : GLAPComponent p (cx x) L)
    (hXL : cx x ≤ Subgroup.normalizer (L : Set G))
    (hZodd : Odd (Nat.card (Subgroup.center (PQuot p L))))
    (hodd : Odd (Nat.card (GLAPPrimeCoreOf p (cx x))))
    (hrk1 : ∀ A : Subgroup G, IsElemAbelian p A → A ≤ cx x → (∀ a ∈ A, CentMod p L a) →
      Nat.card A ≤ p)
    {R A₀ : Subgroup G} (hRL : R ≤ L) (hAL : A₀ ≤ L)
    (hmax : ∀ R'' : Subgroup (MulAut (PQuot p L)), IsPGroup 2 R'' →
      (lImg p L A₀).map MulAut.conj ≤ Subgroup.normalizer (R'' : Set (MulAut (PQuot p L))) →
      (lImg p L R).map MulAut.conj ≤ R'' → R'' = (lImg p L R).map MulAut.conj)
    {R' : Subgroup G} (hR'X : R' ≤ cx x) (hR'2 : IsPGroup 2 R')
    (hAN : A₀ ≤ Subgroup.normalizer (R' : Set G)) (hRR' : R ≤ R') : R' = R := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set NL : Subgroup G := Subgroup.normalizer (L : Set G) with hNL
  have hR'N : R' ≤ NL := hR'X.trans hXL
  set Rb : Subgroup (MulAut (PQuot p L)) := (R'.subgroupOf NL).map (barAut p L) with hRb
  have hRb2 : IsPGroup 2 Rb := by
    refine IsPGroup.map ?_ _
    exact hR'2.of_equiv (Subgroup.subgroupOfEquivOfLe hR'N).symm
  have hAnorm : (lImg p L A₀).map MulAut.conj ≤ Subgroup.normalizer (Rb : Set _) := by
    rw [← map_barAut_eq_map_conj_of_le hAL]
    refine le_trans ?_ (Subgroup.le_normalizer_map (barAut p L))
    refine Subgroup.map_mono ?_
    rw [← Subgroup.subgroupOf_normalizer_eq hR'N]
    intro a ha
    exact hAN ha
  have hRle : (lImg p L R).map MulAut.conj ≤ Rb := by
    rw [← map_barAut_eq_map_conj_of_le hRL]
    exact Subgroup.map_mono fun r hr => hRR' hr
  have heq := hmax Rb hRb2 hAnorm hRle
  rw [← map_barAut_eq_map_conj_of_le hRL] at heq
  refine le_antisymm (fun r' hr' => ?_) hRR'
  have hmem : barAut p L ⟨r', hR'N hr'⟩ ∈ (R.subgroupOf NL).map (barAut p L) := by
    rw [← heq]
    exact ⟨⟨r', hR'N hr'⟩, hr', rfl⟩
  obtain ⟨⟨r, hrN⟩, hr, hrr'⟩ := hmem
  have hrR : r ∈ R := hr
  have hrR' : r ∈ R' := hRR' hrR
  set g : G := r⁻¹ * r' with hg
  have hgN : g ∈ NL := NL.mul_mem (NL.inv_mem hrN) (hR'N hr')
  have hβ : barAut p L ⟨g, hgN⟩ = 1 := by
    have e : (⟨g, hgN⟩ : NL) = (⟨r, hrN⟩ : NL)⁻¹ * ⟨r', hR'N hr'⟩ := rfl
    rw [e, map_mul, map_inv, hrr', inv_mul_cancel]
  have hcm : CentMod p L g := (chev_barAut_eq_one_iff_centMod hgN).1 hβ
  have hgR' : g ∈ R' := R'.mul_mem (R'.inv_mem hrR') hr'
  obtain ⟨k, hk⟩ := hR'2 ⟨g, hgR'⟩
  have hk' : g ^ (2 ^ k) = 1 := by simpa using congrArg Subtype.val hk
  have hgO := mem_pPrimeCoreOf_of_centMod_two hp hp2 hx hL hZodd hrk1 (hR'X hgR') ⟨k, hk'⟩ hcm
  have hg1 : g = 1 := eq_one_of_two_pow_of_odd hodd hgO hk'
  have : r' = r := by
    have h1 : r⁻¹ * r' = 1 := hg1
    calc r' = r * (r⁻¹ * r') := by group
      _ = r := by rw [h1, mul_one]
  rw [this]
  exact hrR

end CFSG.LocalAnalysis.GLTheoremA.H301
