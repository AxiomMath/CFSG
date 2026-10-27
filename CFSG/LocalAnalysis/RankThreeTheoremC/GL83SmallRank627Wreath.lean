module

public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83SmallRank627Defs
public import CFSG.LocalAnalysis.RankThreeTheoremC.WreathThompson
public import CFSG.Assembly.QuasithinDefs
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProper
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProperGroups
public import CFSG.LocalAnalysis.ComponentClassification.Helpers
public import CFSG.LocalAnalysis.RankThreeEvenClassification.ComponentCore
public import CFSG.Quasithin.Background.Basic
public import CFSG.RankThree.GroupTheory.SteinbergBYSectionNineResidual
public import CFSG.RankThree.GroupTheory.SteinbergCEQuaternionDihedral
public import CFSG.RankThree.LocalRank.SelectorCases
public import CFSG.RankThree.PartOne.Assembly

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers Subgroup

variable {G : Type} [Group G] [Finite G]

local notation "Z₃" => Multiplicative (ZMod 3)

local notation "W₃" => Z₃ ≀ᵣ Z₃

private abbrev wreathGen : Z₃ := Multiplicative.ofAdd 1

private theorem wreath_pow_three_left (v : W₃) (q : Z₃) :
    (v ^ 3).left q = v.left q * v.left (v.right⁻¹ * q) * v.left ((v.right * v.right)⁻¹ * q) := by
  rw [pow_succ, pow_succ, pow_one]
  rfl

private theorem wreath_exists_coboundary (f f' : Z₃ → Z₃)
    (hf : ∀ q, f q * f (wreathGen⁻¹ * q) * f ((wreathGen * wreathGen)⁻¹ * q) = 1)
    (hf' : ∀ q, f' q * f' (wreathGen⁻¹ * q) * f' ((wreathGen * wreathGen)⁻¹ * q) = 1) :
    ∃ g : Z₃ → Z₃, ∀ q, g q * f q * (g (wreathGen⁻¹ * q))⁻¹ = f' q := by
  revert f f'
  decide +kernel

private theorem wreath_norm_eq_one {v : W₃} (hr : v.right = wreathGen) (h3 : v ^ 3 = 1)
    (q : Z₃) :
    v.left q * v.left (wreathGen⁻¹ * q) * v.left ((wreathGen * wreathGen)⁻¹ * q) = 1 := by
  have h := wreath_pow_three_left v q
  rw [h3, hr] at h
  exact h.symm

private theorem wreath_conj_of_coboundary {w w' : W₃} (hr : w.right = wreathGen)
    (hr' : w'.right = wreathGen) {g : Z₃ → Z₃}
    (hg : ∀ q, g q * w.left q * (g (wreathGen⁻¹ * q))⁻¹ = w'.left q) :
    (⟨g, 1⟩ : W₃) * w * (⟨g, 1⟩ : W₃)⁻¹ = w' := by
  refine RegularWreathProduct.ext (funext fun q => ?_) ?_
  · have e1 : ∀ q : Z₃, (1 : Z₃)⁻¹ * q = q := by decide
    have e2 : ∀ q : Z₃, (1 : Z₃) * ((1 * wreathGen)⁻¹ * q) = wreathGen⁻¹ * q := by decide
    show g q * w.left ((1 : Z₃)⁻¹ * q) * (g (1 * ((1 * w.right)⁻¹ * q)))⁻¹ = w'.left q
    rw [e1, hr, e2]
    exact hg q
  · show (1 : Z₃) * w.right * (1 : Z₃)⁻¹ = w'.right
    rw [hr, hr']
    decide

private theorem wreath_exists_conj_of_right_eq {w w' : W₃} (hr : w.right = wreathGen)
    (hr' : w'.right = wreathGen) (h3 : w ^ 3 = 1) (h3' : w' ^ 3 = 1) :
    ∃ u : W₃, u * w * u⁻¹ = w' := by
  obtain ⟨g, hg⟩ := wreath_exists_coboundary w.left w'.left (wreath_norm_eq_one hr h3)
    (wreath_norm_eq_one hr' h3')
  exact ⟨⟨g, 1⟩, wreath_conj_of_coboundary hr hr' hg⟩

private theorem wreath_exists_conj_or_inv {w w' : W₃} (hw : w.right ≠ 1) (hw' : w'.right ≠ 1)
    (h3 : w ^ 3 = 1) (h3' : w' ^ 3 = 1) :
    ∃ u : W₃, u * w * u⁻¹ = w' ∨ u * w * u⁻¹ = w'⁻¹ := by
  have hnf : ∀ v : W₃, v.right ≠ 1 → v ^ 3 = 1 →
      ∃ v' : W₃, (v' = v ∨ v' = v⁻¹) ∧ v'.right = wreathGen ∧ v' ^ 3 = 1 := by
    intro v hv h3v
    have hcases : ∀ r : Z₃, r ≠ 1 → r = wreathGen ∨ r⁻¹ = wreathGen := by decide
    rcases hcases v.right hv with h | h
    · exact ⟨v, Or.inl rfl, h, h3v⟩
    · exact ⟨v⁻¹, Or.inr rfl, h, by rw [inv_pow, h3v, inv_one]⟩
  obtain ⟨v, hv, hvr, hv3⟩ := hnf w hw h3
  obtain ⟨v', hv', hv'r, hv'3⟩ := hnf w' hw' h3'
  obtain ⟨u, hu⟩ := wreath_exists_conj_of_right_eq hvr hv'r hv3 hv'3
  refine ⟨u, ?_⟩
  rcases hv with rfl | rfl <;> rcases hv' with rfl | rfl
  · exact Or.inl hu
  · exact Or.inr hu
  · right
    rw [← hu]
    group
  · left
    rw [← inv_inv w', ← hu]
    group

omit [Finite G] in
private theorem zpowers_eq_map_conj_of {x y g : G}
    (h : g * x * g⁻¹ = y ∨ g * x * g⁻¹ = y⁻¹) :
    zpowers y = (zpowers x).map (MulAut.conj g).toMonoidHom := by
  rw [MonoidHom.map_zpowers]
  have hc : (MulAut.conj g).toMonoidHom x = g * x * g⁻¹ := MulAut.conj_apply g x
  rw [hc]
  rcases h with h | h
  · rw [h]
  · rw [h, zpowers_inv]

omit [Finite G] in
private theorem wreath_card_le_of_isMulCommutative {P : Subgroup G} (e : P ≃* W₃)
    {B : Subgroup G} (hBP : B ≤ P) (hB : IsMulCommutative B) : Nat.card B ≤ 27 := by
  let ι : W₃ →* G := P.subtype.comp e.symm.toMonoidHom
  have hιinj : Function.Injective ι := P.subtype_injective.comp e.symm.injective
  have hιsurj : ∀ b ∈ P, ∃ w, ι w = b := fun b hb => ⟨e ⟨b, hb⟩, by simp [ι]⟩
  have hcomap : Nat.card (B.comap ι) = Nat.card B := by
    have hrange : B ≤ ι.range := fun b hb => hιsurj b (hBP hb)
    calc Nat.card (B.comap ι) = Nat.card ((B.comap ι).map ι) :=
          (Subgroup.card_map_of_injective hιinj).symm
      _ = Nat.card B := by rw [Subgroup.map_comap_eq_self hrange]
  have := Subgroup.comap_injective_isMulCommutative B hιinj
  rw [← hcomap]
  by_cases hle : B.comap ι ≤ (RegularWreathProduct.rightHom : W₃ →* Z₃).ker
  · rw [← wreath_card_ker]
    exact Subgroup.card_le_of_le hle
  · have := wreath_card_le_nine_of_not_le_ker (X := B.comap ι) inferInstance hle
    omega

omit [Finite G] in
private theorem wreath_map_ker_le_thompsonSubgroup {P : Subgroup G} (e : P ≃* W₃) :
    (RegularWreathProduct.rightHom : W₃ →* Z₃).ker.map (P.subtype.comp e.symm.toMonoidHom) ≤
      thompsonSubgroup P := by
  let ι : W₃ →* G := P.subtype.comp e.symm.toMonoidHom
  have hιinj : Function.Injective ι := P.subtype_injective.comp e.symm.injective
  have hιP : ∀ w, ι w ∈ P := fun w => (e.symm w).2
  have hA₀c : IsMulCommutative (RegularWreathProduct.rightHom : W₃ →* Z₃).ker :=
    wreath_ker_isElemAbelian.1
  have hA₁P : (RegularWreathProduct.rightHom : W₃ →* Z₃).ker.map ι ≤ P := by
    rintro _ ⟨a, _, rfl⟩
    exact hιP a
  have hA₁c : IsMulCommutative ((RegularWreathProduct.rightHom : W₃ →* Z₃).ker.map ι) :=
    Subgroup.map_isMulCommutative _ ι
  have hA₁card : Nat.card ((RegularWreathProduct.rightHom : W₃ →* Z₃).ker.map ι) = 27 :=
    (Subgroup.card_map_of_injective hιinj).trans wreath_card_ker
  rw [CFSG.Open.thompsonSubgroup_eq_iSup]
  exact le_iSup_of_le _ (le_iSup_of_le hA₁P (le_iSup_of_le hA₁c
    (le_iSup_of_le (fun B hBP hB => (wreath_card_le_of_isMulCommutative e hBP hB).trans
      hA₁card.ge) le_rfl)))

set_option linter.unusedSectionVars false in
set_option linter.unusedVariables false in
theorem exists_conj_zpowers_of_not_mem_thompsonSubgroup {P : Subgroup G}
    (e : P ≃* (Multiplicative (ZMod 3) ≀ᵣ Multiplicative (ZMod 3))) {x y : G}
    (hxP : x ∈ P) (hx1 : x ≠ 1) (hx3 : x ^ 3 = 1) (hxJ : x ∉ thompsonSubgroup P)
    (hyP : y ∈ P) (hy1 : y ≠ 1) (hy3 : y ^ 3 = 1) (hyJ : y ∉ thompsonSubgroup P) :
    ∃ g ∈ P, zpowers y = (zpowers x).map (MulAut.conj g).toMonoidHom := by
  let ι : W₃ →* G := P.subtype.comp e.symm.toMonoidHom
  have hιP : ∀ w, ι w ∈ P := fun w => (e.symm w).2
  have hι : ∀ {z : G} (hzP : z ∈ P), ι (e ⟨z, hzP⟩) = z := fun hzP => by simp [ι]
  have key : ∀ {z : G} (hzP : z ∈ P), z ∉ thompsonSubgroup P → z ^ 3 = 1 →
      (e ⟨z, hzP⟩).right ≠ 1 ∧ e ⟨z, hzP⟩ ^ 3 = 1 := by
    intro z hzP hzJ hz3
    refine ⟨fun h => hzJ ?_, ?_⟩
    · exact wreath_map_ker_le_thompsonSubgroup e ⟨e ⟨z, hzP⟩, MonoidHom.mem_ker.mpr h, hι hzP⟩
    · have hz : (⟨z, hzP⟩ : P) ^ 3 = 1 := Subtype.ext hz3
      rw [← map_pow, hz, map_one]
  obtain ⟨hw1, hw3⟩ := key hxP hxJ hx3
  obtain ⟨hw1', hw3'⟩ := key hyP hyJ hy3
  obtain ⟨u, hu⟩ := wreath_exists_conj_or_inv hw1 hw1' hw3 hw3'
  refine ⟨ι u, hιP u, zpowers_eq_map_conj_of ?_⟩
  rcases hu with hu | hu
  · left
    simpa [hι hxP, hι hyP] using congrArg ι hu
  · right
    simpa [hι hxP, hι hyP] using congrArg ι hu

theorem not_mem_thompsonSubgroup_of_not_centralizer_le (hp : 3 ∈ rankThreeSigmaA G)
    (hS : Setting G) {P : Sylow 3 G} {M : Subgroup G} (hM : IsCoreMaxLocal 3 P M)
    (hempty : ∀ y : G, ¬ IsLargeObstruction 3 M y)
    (e : (P : Subgroup G) ≃* (Multiplicative (ZMod 3) ≀ᵣ Multiplicative (ZMod 3))) {x : G}
    (hxP : x ∈ (P : Subgroup G)) (hx1 : x ≠ 1) (hx3 : x ^ 3 = 1)
    (hxM : ¬ centralizer ({x} : Set G) ≤ M) : x ∉ thompsonSubgroup (P : Subgroup G) := by
  intro hxJ
  exact hempty x ⟨(sylow_le_of_isCoreMaxLocal hS hp hM).1 hxP, hx1, hx3,
    (three_le_pRank_inf_centralizer_of_mem_thompsonSubgroup e hxJ).trans
      (pRank_mono 3 (by norm_num) inf_le_right), hxM⟩

theorem exists_conj_zpowers_of_smallRankPoint (hS : Setting G) {P : Sylow 3 G} {M : Subgroup G}
    (hsit : SmallRankSituation G 3 P M)
    (e : (P : Subgroup G) ≃* (Multiplicative (ZMod 3) ≀ᵣ Multiplicative (ZMod 3))) {x x₀ : G}
    (hx : SmallRankPoint P M x) (hx₀P : x₀ ∈ (P : Subgroup G)) (hx₀1 : x₀ ≠ 1)
    (hx₀3 : x₀ ^ 3 = 1) (hx₀M : ¬ centralizer ({x₀} : Set G) ≤ M) :
    ∃ g ∈ (P : Subgroup G), zpowers x₀ = (zpowers x).map (MulAut.conj g).toMonoidHom :=
  exists_conj_zpowers_of_not_mem_thompsonSubgroup e hx.mem hx.ne_one hx.pow_eq_one
    (not_mem_thompsonSubgroup_of_not_centralizer_le hsit.mem_sigmaA hS hsit.isCoreMaxLocal
      hsit.largeObstruction_empty e hx.mem hx.ne_one hx.pow_eq_one hx.not_centralizer_le)
    hx₀P hx₀1 hx₀3
    (not_mem_thompsonSubgroup_of_not_centralizer_le hsit.mem_sigmaA hS hsit.isCoreMaxLocal
      hsit.largeObstruction_empty e hx₀P hx₀1 hx₀3 hx₀M)

set_option linter.unusedSectionVars false in
theorem rankThreeIsQ8CentralCyclic_map {H : Subgroup G} {m : ℕ}
    (h : rankThreeIsQ8CentralCyclic H m) (φ : MulAut G) :
    rankThreeIsQ8CentralCyclic (H.map φ.toMonoidHom) m := by
  obtain ⟨A, B, ⟨eA⟩, hB, hBcard, hcomm, hAB, hinf⟩ := h
  have hinj : Function.Injective φ.toMonoidHom := φ.injective
  refine ⟨A.map φ.toMonoidHom, B.map φ.toMonoidHom,
    ⟨(A.equivMapOfInjective φ.toMonoidHom hinj).symm.trans eA⟩, ?_, ?_, ?_, ?_, ?_⟩
  · exact (B.equivMapOfInjective φ.toMonoidHom hinj).isCyclic.mp hB
  · rw [Subgroup.card_map_of_injective hinj, hBcard]
  · rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    rw [← map_mul, ← map_mul, hcomm a ha b hb]
  · rw [← Subgroup.map_sup, hAB]
  · rw [← Subgroup.map_inf _ _ _ hinj, Subgroup.card_map_of_injective hinj, hinf]

end CFSG.LocalAnalysis.RankThreeTheoremC
