module

public import CFSG.LocalAnalysis.GLTheoremA.CatB.H301Struct
public import CFSG.LocalAnalysis.GLTheoremA.CatB.H301Lift1

public section

namespace CFSG.LocalAnalysis.GLTheoremA.H301

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremA
  CFSG.LocalAnalysis.GLTheoremA.S8 CFSG.LocalAnalysis.GLTheoremB
open CFSG.HardMathSupport.Solomon.LocalBalance (barAut barAut_mk)

section Aut

variable {K : Type} [Group K]

theorem mulAut_conj_injective (hZ : Subgroup.center K = ⊥) :
    Function.Injective (MulAut.conj : K →* MulAut K) := by
  rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
  intro k hk
  rw [← hZ, Subgroup.mem_center_iff]
  intro g
  have h := congrArg (fun f : MulAut K => f g) (MonoidHom.mem_ker.1 hk)
  simp only [MulAut.conj_apply, MulAut.one_apply] at h
  calc g * k = k * g * k⁻¹ * k := by rw [h]
    _ = k * g := by group

theorem centralizer_range_mulAut_conj (hZ : Subgroup.center K = ⊥) :
    Subgroup.centralizer ((MulAut.conj : K →* MulAut K).range : Set (MulAut K)) = ⊥ := by
  rw [eq_bot_iff]
  intro α hα
  rw [Subgroup.mem_bot]
  have hk : ∀ k : K, α k = k := by
    intro k
    have h1 := Subgroup.mem_centralizer_iff.1 hα (MulAut.conj k) ⟨k, rfl⟩
    have h2 : MulAut.conj (α k) = MulAut.conj k := by
      ext g
      have h3 := congrArg (fun f : MulAut K => f (α.symm g)) h1
      simp only [MulAut.mul_apply, MulAut.conj_apply, map_mul, map_inv,
        MulEquiv.apply_symm_apply] at h3
      simp only [MulAut.conj_apply]
      exact h3.symm
    exact mulAut_conj_injective hZ h2
  ext k
  exact hk k

theorem range_mulAut_conj_normal : (MulAut.conj : K →* MulAut K).range.Normal :=
  CFSG.ComponentClassification.OuterAutomorphisms.inner_normal K

theorem finite_mulAut [Finite K] : Finite (MulAut K) :=
  Finite.of_injective (fun f : MulAut K => (f : K → K)) fun _ _ h => MulEquiv.ext (congrFun h)

end Aut

variable {G : Type} [Group G] [Finite G]

theorem barAut_of_mem {p : ℕ} {L : Subgroup G} {l : G} (hl : l ∈ L) :
    barAut p L ⟨l, Subgroup.le_normalizer hl⟩ = MulAut.conj (pQuotHom p L ⟨l, hl⟩) := by
  ext q
  induction q using QuotientGroup.induction_on with
  | H y =>
    rw [barAut_mk, MulAut.conj_apply]
    show (QuotientGroup.mk _ : PQuot p L) =
      QuotientGroup.mk ⟨l, hl⟩ * QuotientGroup.mk y * (QuotientGroup.mk ⟨l, hl⟩)⁻¹
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul]
    congr 1

private theorem map_barAut_eq_map_conj {p : ℕ} {L Y : Subgroup G} (hY : Y ≤ L) :
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

theorem eq_one_of_two_pow_of_odd {O : Subgroup G} (hO : Odd (Nat.card O)) {g : G} (hg : g ∈ O)
    {k : ℕ} (hk : g ^ (2 ^ k) = 1) : g = 1 := by
  have h1 : orderOf (⟨g, hg⟩ : O) ∣ Nat.card O := orderOf_dvd_natCard _
  have h2 : orderOf (⟨g, hg⟩ : O) ∣ 2 ^ k :=
    orderOf_dvd_of_pow_eq_one (Subtype.ext (by simpa using hk))
  have hcop : Nat.Coprime (2 ^ k) (Nat.card O) :=
    Nat.Coprime.pow_left k (Nat.coprime_two_left.2 hO)
  have h3 : orderOf (⟨g, hg⟩ : O) = 1 := Nat.Coprime.eq_one_of_dvd (hcop.coprime_dvd_left h2) h1
  have h4 : (⟨g, hg⟩ : O) = 1 := orderOf_eq_one_iff.1 h3
  exact congrArg Subtype.val h4

theorem eq_of_le_of_map_barAut {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {x : G} {L : Subgroup G}
    (hx : orderOf x = p) (hL : GLAPComponent p (cx x) L)
    (hXL : cx x ≤ Subgroup.normalizer (L : Set G)) (hZ : Subgroup.center (PQuot p L) = ⊥)
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
    rw [← map_barAut_eq_map_conj hAL]
    refine le_trans ?_ (Subgroup.le_normalizer_map (barAut p L))
    refine Subgroup.map_mono ?_
    rw [← Subgroup.subgroupOf_normalizer_eq hR'N]
    intro a ha
    exact hAN ha
  have hRle : (lImg p L R).map MulAut.conj ≤ Rb := by
    rw [← map_barAut_eq_map_conj hRL]
    exact Subgroup.map_mono fun r hr => hRR' hr
  have heq := hmax Rb hRb2 hAnorm hRle
  rw [← map_barAut_eq_map_conj hRL] at heq
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
  have hZodd : Odd (Nat.card (Subgroup.center (PQuot p L))) := by
    rw [hZ, Subgroup.card_bot]
    exact odd_one
  have hgO := mem_pPrimeCoreOf_of_centMod_two hp hp2 hx hL hZodd hrk1 (hR'X hgR') ⟨k, hk'⟩ hcm
  have hg1 : g = 1 := eq_one_of_two_pow_of_odd hodd hgO hk'
  have : r' = r := by
    have h1 : r⁻¹ * r' = 1 := hg1
    calc r' = r * (r⁻¹ * r') := by group
      _ = r := by rw [h1, mul_one]
  rw [this]
  exact hrR

end CFSG.LocalAnalysis.GLTheoremA.H301
