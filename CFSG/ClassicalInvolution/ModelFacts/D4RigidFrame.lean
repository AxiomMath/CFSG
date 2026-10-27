module

public import CFSG.ClassicalInvolution.RouteD.GapsFrPair
public import CFSG.ClassicalInvolution.RouteD.ExoticD4Model
public import CFSG.ClassicalInvolution.ModelFacts.D4RigidWeights
public import Certificates.Certificate45
public import Certificates.Certificate46
public import Certificates.Certificate47
public import Certificates.Certificate48
public import Certificates.Certificate49
public import Certificates.Certificate50
public import Certificates.Certificate51
public import Certificates.Certificate52
public import Certificates.Certificate53
public import Certificates.Certificate54
public import Certificates.Certificate55
public import Certificates.Certificate56
public import Certificates.Certificate57
public import Certificates.Certificate58
public import Certificates.Certificate59
public import Certificates.Certificate60
public import Certificates.Certificate61
public import Certificates.Certificate62
public import Certificates.Certificate63
public import Certificates.Certificate64
public import Certificates.Certificate65
public import Certificates.Certificate66
public import Certificates.Certificate67
public import Certificates.Certificate68
public import Certificates.Certificate69
public import Certificates.Certificate70
public import Certificates.Certificate71
public import Certificates.Certificate72
public import Certificates.Certificate73
public import Certificates.Certificate74
public import Certificates.Certificate75
public import Certificates.Certificate76
public import Certificates.Certificate77
public import Certificates.Certificate78
public import Certificates.Certificate79
public import Certificates.Certificate80
public import Certificates.Certificate81
public import Certificates.Certificate113
public import Certificates.Certificate114
public import Certificates.Certificate115
public import Certificates.Certificate116
public import Certificates.Certificate117
public import Certificates.Certificate118
public import Certificates.Certificate119
public import Certificates.Certificate120
public import Certificates.Certificate121
public import Certificates.Certificate122
public import Certificates.Certificate123
public import CFSG.ClassicalInvolution.ModelFacts.OrthAutDiagC

public section

namespace CFSG.ClassicalInvolution.ModelFacts.D4Rigid

open CFSG.ClassicalInvolution.Models.OrthogonalPairs CFSG.ClassicalGroups.Orthogonal QuadraticMap
open CFSG.LieType.Universal.Spin CFSG.Assembly.LowTwoRank
open CFSG.ClassicalInvolution.Generic (Commutes conjSub fundamentalSubgroups mem_conjSub_iff
  commutes_conjSub_iff)
open CFSG.ClassicalInvolution.WeakCT (LinearBlockStandardPair)
open CFSG.ClassicalInvolution.RouteD.Gaps
open CFSG.ClassicalInvolution.RouteD (ne_of_linearBlockStandardPair
  not_commutes_of_linearBlockStandardPair conjSub_mem_fundamentalSubgroups)
open scoped MatrixGroups commutatorElement

section Pair

variable {K V : Type} [Field K] [Finite K] [AddCommGroup V] [Module K V]
  {Q : QuadraticForm K V}

theorem adj_data_of_linear (hodd : Odd (Nat.card K)) {c l : Subgroup (V ≃ₗ[K] V)}
    {ic il : V ≃ₗ[K] V} (hc : IsFundamental Q c ic) (hl : IsFundamental Q l il)
    (hlin : ∃ W, LinearBlockStandardPair K W c l) :
    ic * il = il * ic ∧ il ∈ Subgroup.normalizer (c : Set (V ≃ₗ[K] V)) ∧
      il ∉ Subgroup.centralizer (c : Set (V ≃ₗ[K] V)) := by
  have h2 := IsFundamental.two_ne_zero_of_odd hodd
  obtain ⟨W, hW⟩ := hlin
  have hord : ∀ {L : Subgroup (V ≃ₗ[K] V)} {i : V ≃ₗ[K] V}, IsFundamental Q L i →
      orderOf i = 2 := fun {L i} h =>
    orderOf_eq_prime (by rw [pow_two]; exact h.mul_self) (IsFundamental.ne_one hodd h)
  have hcomm : ic * il = il * ic :=
    standardPair_involutions_commute h2 hW hc.mem hl.mem (hord hc) (hord hl)
  have hne : c ≠ l := ne_of_linearBlockStandardPair hW
  refine ⟨hcomm, ?_, fun hcent => not_commutes_of_linearBlockStandardPair hW
    ((IsFundamental.commute_iff hodd hc hl hcomm hne).mpr hcent)⟩
  have hN := conjSub_eq_of_standardPair h2 hW hl.mem (hord hl)
  have hmul : il * il = 1 := hl.mul_self
  have hinv : il⁻¹ = il := inv_eq_of_mul_eq_one_right hmul
  rw [Subgroup.mem_normalizer_iff]
  intro x
  have h := Subgroup.ext_iff.mp hN x
  rw [mem_conjSub_iff, hinv] at h
  rw [hinv]
  exact h.symm

end Pair

section Pair4

variable {p f : ℕ} [Fact p.Prime]

theorem exists_spin_pair_four (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f)
    {R₀ R₁ : Subgroup (spinGroup (quadPlus 4 (GaloisField p f)))}
    (hR₀ : R₀ ∈ fundamentalSubgroups .POmegaPlus (plusDatum 4 (GaloisField p f) (by omega)))
    (hR₁ : R₁ ∈ fundamentalSubgroups .POmegaPlus (plusDatum 4 (GaloisField p f) (by omega)))
    (hlin : ∃ W, LinearBlockStandardPair (GaloisField p f) W R₀ R₁) :
    ∃ x : spinGroup (quadPlus 4 (GaloisField p f)),
      R₀ = ((rootSL2 (plusFrame 4 (GaloisField p f) (by omega)) 0 1 (by omega) (by omega)
        (by omega) true false).map (MulAut.conj x).toMonoidHom) ∧
      R₁ = ((rootSL2 (plusFrame 4 (GaloisField p f) (by omega)) 1 2 (by omega) (by omega)
        (by omega) true false).map (MulAut.conj x).toMonoidHom) := by
  classical
  have hm3 : 3 ≤ 4 := by norm_num
  obtain ⟨hf0, hK⟩ := CFSG.ClassicalInvolution.RouteD.card_galoisField_of_four_le
    (p := p) (f := f) (by omega)
  have hodd : Odd (Nat.card (GaloisField p f)) := by
    rw [hK]
    exact (Nat.Prime.odd_of_ne_two Fact.out hp2).pow
  have h2 : (2 : GaloisField p f) ≠ 0 := two_ne_zero_galoisField f hp2
  have : Invertible (2 : GaloisField p f) := invertibleOfNonzero h2
  have hQ : (quadPlus 4 (GaloisField p f)).Nondegenerate :=
    QuadraticMap.nondegenerate_polar_iff.mp (nondegenerate_polarBilin_quadPlus 4 (GaloisField p f))
  have cq := centralQuot_plus hp2 (le_refl 4) hm3 hq
  obtain ⟨i₀, hi₀⟩ := cq.map_mem _ hR₀
  obtain ⟨i₁, hi₁⟩ := cq.map_mem _ hR₁
  let L : ℕ → Subgroup ((Fin 4 ⊕ Fin 4 → GaloisField p f) ≃ₗ[GaloisField p f]
      (Fin 4 ⊕ Fin 4 → GaloisField p f)) :=
    fun a => (if a = 0 then R₀ else R₁).map (spinAction (quadPlus 4 (GaloisField p f)))
  have hL0 : L 0 = R₀.map (spinAction (quadPlus 4 (GaloisField p f))) := by simp [L]
  have hL1 : L 1 = R₁.map (spinAction (quadPlus 4 (GaloisField p f))) := by simp [L]
  let i : ℕ → ((Fin 4 ⊕ Fin 4 → GaloisField p f) ≃ₗ[GaloisField p f]
      (Fin 4 ⊕ Fin 4 → GaloisField p f)) := fun a => if a = 0 then i₀ else i₁
  have hi : ∀ a < 2, IsFundamental (quadPlus 4 (GaloisField p f)) (L a) (i a) := by
    intro a ha
    by_cases h0 : a = 0
    · subst h0
      simpa [L, i] using hi₀
    · simpa [L, i, h0] using hi₁
  obtain ⟨W, hW⟩ := hlin
  have hlinV : ∃ W', LinearBlockStandardPair (GaloisField p f) W'
      (R₀.map (spinAction (quadPlus 4 (GaloisField p f))))
      (R₁.map (spinAction (quadPlus 4 (GaloisField p f)))) :=
    ⟨_, linearBlockStandardPair_map _ cq.ker_le hW⟩
  obtain ⟨cm, N, C⟩ := adj_data_of_linear hodd hi₀ hi₁ hlinV
  have hVchain : VChain (quadPlus 4 (GaloisField p f)) 2 L i := by
    refine ⟨hi, fun a ha => ?_, fun a ha => ?_, fun a ha => ?_, fun a ha => ?_,
      fun a b hab hb => by omega⟩
    · have : a = 0 := by omega
      subst this
      simpa [i] using cm
    · have : a = 0 := by omega
      subst this
      simpa [L, i] using N
    · have : a = 0 := by omega
      subst this
      simpa [L, i] using C
    · have : a = 0 := by omega
      subst this
      have := hasSingularVector_of_linearPair hp2 (by omega) hi₀ hi₁ cm N C hlinV
      simpa [i] using this
  obtain ⟨pp, horth, hpl, hLp⟩ := exists_chain_pairs true hodd hVchain (le_refl 2)
  obtain ⟨x, hx⟩ := exists_spin_prefix hodd hQ (plusFrame 4 (GaloisField p f) hm3) (k := 3)
    (by omega) (P := pp) (fun a b ha hb hab => horth a b (by omega) (by omega) hab)
  have hnode : ∀ a (ha : a < 2), L a = ((rootSL2 (plusFrame 4 (GaloisField p f) hm3) a (a + 1)
      (by omega) (by omega) (by omega) true false).map (MulAut.conj x).toMonoidHom).map
        (spinAction (quadPlus 4 (GaloisField p f))) := by
    intro a ha
    have := La_range_eq_of_pairs (plusFrame 4 (GaloisField p f) hm3) (a := a) (b := a + 1)
      (by omega) (by omega) (by omega) true false x
      (orth_swapPair (horth a (a + 1) ha.le (by omega) (by omega))) (hx a (by omega))
      ⟨(hx (a + 1) (by omega)).2, (hx (a + 1) (by omega)).1⟩
    rw [hLp a ha]
    exact this
  have hperf := rootSL2_map_conj_perfect (p := p) (f := f) (m := 4) (by omega)
    (plusFrame 4 (GaloisField p f) hm3) (x := x)
  refine ⟨x, ?_, ?_⟩
  · exact eq_of_map_eq_of_isPerfect _ cq.ker_le
      (cq.perf _ hR₀) (hperf 0 1 (by omega) (by omega) (by omega) true false)
      (by rw [← hL0]; exact hnode 0 (by omega))
  · exact eq_of_map_eq_of_isPerfect _ cq.ker_le
      (cq.perf _ hR₁) (hperf 1 2 (by omega) (by omega) (by omega) true false)
      (by rw [← hL1]; exact hnode 1 (by omega))

end Pair4

section Std

theorem commutes_range_of_gens {F : Type} [Field F] {S : Type} [Group S]
    (ρ₁ ρ₂ : Matrix.SpecialLinearGroup (Fin 2) F →* S)
    (huu : ∀ a b, Commute (ρ₁ (upperSL2 a)) (ρ₂ (upperSL2 b)))
    (hul : ∀ a b, Commute (ρ₁ (upperSL2 a)) (ρ₂ (lowerSL2 b)))
    (hlu : ∀ a b, Commute (ρ₁ (lowerSL2 a)) (ρ₂ (upperSL2 b)))
    (hll : ∀ a b, Commute (ρ₁ (lowerSL2 a)) (ρ₂ (lowerSL2 b))) :
    Commutes ρ₁.range ρ₂.range := by
  rintro _ ⟨M, rfl⟩ _ ⟨N, rfl⟩
  obtain ⟨a, b, c, d, rfl⟩ := exists_eq_lowerSL2_mul_upperSL2_mul_lowerSL2_mul_upperSL2 M
  obtain ⟨a', b', c', d', rfl⟩ := exists_eq_lowerSL2_mul_upperSL2_mul_lowerSL2_mul_upperSL2 N
  have key : ∀ g : S, Commute g (ρ₂ (lowerSL2 a')) → Commute g (ρ₂ (upperSL2 b')) →
      Commute g (ρ₂ (lowerSL2 c')) → Commute g (ρ₂ (upperSL2 d')) →
      Commute g (ρ₂ (lowerSL2 a') * ρ₂ (upperSL2 b') * ρ₂ (lowerSL2 c') * ρ₂ (upperSL2 d')) :=
    fun g h₁ h₂ h₃ h₄ => ((h₁.mul_right h₂).mul_right h₃).mul_right h₄
  simp only [map_mul]
  exact ((((key _ (hll a a') (hlu a b') (hll a c') (hlu a d')).mul_left
    (key _ (hul b a') (huu b b') (hul b c') (huu b d'))).mul_left
    (key _ (hll c a') (hlu c b') (hll c c') (hlu c d'))).mul_left
    (key _ (hul d a') (huu d b') (hul d c') (huu d d'))).eq

variable {F : Type} [Field F]

@[expose] noncomputable def stdSL2 (F : Type) [Field F] :
    Fin 4 → Subgroup (spinGroup (quadPlus 4 F))
  | 0 => ((fr F).longSL2 ne01 true false).range
  | 1 => ((fr F).longSL2 ne01 true true).range
  | 2 => ((fr F).longSL2 ne23 true false).range
  | 3 => ((fr F).longSL2 ne23 true true).range

theorem commutes_std_zero_one : Commutes (stdSL2 F 0) (stdSL2 F 1) := by
  refine commutes_range_of_gens _ _ (fun a b => ?_) (fun a b => ?_) (fun a b => ?_)
    (fun a b => ?_)
  · rw [HypFrame.longSL2_upperSL2, HypFrame.longSL2_upperSL2]
    exact (fr F).commute_longRoot_longRoot_left ne01 ne01 true false true a b
  · rw [HypFrame.longSL2_upperSL2, HypFrame.longSL2_lowerSL2]
    show Commute ((fr F).longRoot ne01 true false (.ofAdd a))
      ((fr F).longRoot ne10 false false (.ofAdd b))
    rw [(fr F).longRoot_swap ne10 false false b]
    exact (fr F).commute_longRoot_longRoot_right ne01 ne01 true false false a (-b)
  · rw [HypFrame.longSL2_lowerSL2, HypFrame.longSL2_upperSL2]
    show Commute ((fr F).longRoot ne10 true false (.ofAdd a))
      ((fr F).longRoot ne01 true true (.ofAdd b))
    rw [(fr F).longRoot_swap ne01 true true b]
    exact (fr F).commute_longRoot_longRoot_left ne10 ne10 true false true a (-b)
  · rw [HypFrame.longSL2_lowerSL2, HypFrame.longSL2_lowerSL2]
    exact (fr F).commute_longRoot_longRoot_right ne10 ne10 true false false a b

theorem commutes_std_zero_two : Commutes (stdSL2 F 0) (stdSL2 F 2) := by
  refine commutes_range_of_gens _ _ (fun a b => ?_) (fun a b => ?_) (fun a b => ?_)
    (fun a b => ?_)
  · rw [HypFrame.longSL2_upperSL2, HypFrame.longSL2_upperSL2]
    exact (fr F).commute_longRoot_longRoot_of_disjoint (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) _ _ _ _ a b
  · rw [HypFrame.longSL2_upperSL2, HypFrame.longSL2_lowerSL2]
    exact (fr F).commute_longRoot_longRoot_of_disjoint (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) _ _ _ _ a b
  · rw [HypFrame.longSL2_lowerSL2, HypFrame.longSL2_upperSL2]
    exact (fr F).commute_longRoot_longRoot_of_disjoint (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) _ _ _ _ a b
  · rw [HypFrame.longSL2_lowerSL2, HypFrame.longSL2_lowerSL2]
    exact (fr F).commute_longRoot_longRoot_of_disjoint (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) _ _ _ _ a b

theorem commutes_std_zero_three : Commutes (stdSL2 F 0) (stdSL2 F 3) := by
  refine commutes_range_of_gens _ _ (fun a b => ?_) (fun a b => ?_) (fun a b => ?_)
    (fun a b => ?_)
  · rw [HypFrame.longSL2_upperSL2, HypFrame.longSL2_upperSL2]
    exact (fr F).commute_longRoot_longRoot_of_disjoint (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) _ _ _ _ a b
  · rw [HypFrame.longSL2_upperSL2, HypFrame.longSL2_lowerSL2]
    exact (fr F).commute_longRoot_longRoot_of_disjoint (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) _ _ _ _ a b
  · rw [HypFrame.longSL2_lowerSL2, HypFrame.longSL2_upperSL2]
    exact (fr F).commute_longRoot_longRoot_of_disjoint (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) _ _ _ _ a b
  · rw [HypFrame.longSL2_lowerSL2, HypFrame.longSL2_lowerSL2]
    exact (fr F).commute_longRoot_longRoot_of_disjoint (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) _ _ _ _ a b

end Std

section Normal

variable {p f : ℕ} [Fact p.Prime]

theorem longSL2_range_mem_fund (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f) {i j : Fin 4} (hij : i ≠ j)
    (s t : Bool) :
    ((fr (GaloisField p f)).longSL2 hij s t).range ∈
      fundamentalSubgroups .POmegaPlus (plusDatum 4 (GaloisField p f) (by norm_num)) := by
  have hm3 : 3 ≤ 4 := by norm_num
  have cq := centralQuot_plus hp2 (le_refl 4) hm3 hq
  have hmem : ((fr (GaloisField p f)).longSL2 hij s t).range.map
      (spinAction (quadPlus 4 (GaloisField p f))) ∈ fundSet (quadPlus 4 (GaloisField p f)) := by
    rw [ModelFacts.map_longSL2_range]
    exact ⟨_, IsFundamental.of_frame _⟩
  obtain ⟨R, hR, hRπ⟩ := cq.surj _ hmem
  obtain ⟨-, hK⟩ := CFSG.ClassicalInvolution.RouteD.card_galoisField_of_four_le
    (p := p) (f := f) (by omega)
  have hperf : Group.IsPerfect SL(2, GaloisField p f) :=
    CFSG.ClassicalInvolution.sl2_isPerfect (by omega)
  have h1 : ⁅((fr (GaloisField p f)).longSL2 hij s t).range,
      ((fr (GaloisField p f)).longSL2 hij s t).range⁆ =
      ((fr (GaloisField p f)).longSL2 hij s t).range :=
    Subgroup.isPerfect_iff.mp (Group.IsPerfect.range _)
  have : R = ((fr (GaloisField p f)).longSL2 hij s t).range :=
    eq_of_map_eq_of_isPerfect _ cq.ker_le (cq.perf R hR) h1 hRπ
  exact this ▸ hR

theorem stdSL2_mem_fund (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f) (i : Fin 4) :
    stdSL2 (GaloisField p f) i ∈
      fundamentalSubgroups .POmegaPlus (plusDatum 4 (GaloisField p f) (by norm_num)) := by
  fin_cases i
  · exact longSL2_range_mem_fund hp2 hq _ _ _
  · exact longSL2_range_mem_fund hp2 hq _ _ _
  · exact longSL2_range_mem_fund hp2 hq _ _ _
  · exact longSL2_range_mem_fund hp2 hq _ _ _

theorem exists_normal_position (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f)
    {R : Fin 4 → Subgroup (spinGroup (quadPlus 4 (GaloisField p f)))}
    (hR : ∀ i, R i ∈ fundamentalSubgroups .POmegaPlus
      (plusDatum 4 (GaloisField p f) (by norm_num)))
    (hinj : Function.Injective R) (hcomm : ∀ i j, i ≠ j → Commutes (R i) (R j))
    {R₅ : Subgroup (spinGroup (quadPlus 4 (GaloisField p f)))}
    (h5 : R₅ ∈ fundamentalSubgroups .POmegaPlus (plusDatum 4 (GaloisField p f) (by norm_num)))
    (hlin : ∃ W, LinearBlockStandardPair (GaloisField p f) W (R 0) R₅) :
    ∃ x : spinGroup (quadPlus 4 (GaloisField p f)),
      R₅ = ((fr (GaloisField p f)).longSL2 ne12 true false).range.map (MulAut.conj x).toMonoidHom ∧
      R 0 = (stdSL2 (GaloisField p f) 0).map (MulAut.conj x).toMonoidHom ∧
      ∀ j : Fin 4, ∃ i : Fin 4,
        (stdSL2 (GaloisField p f) j).map (MulAut.conj x).toMonoidHom = R i := by
  have hm3 : 3 ≤ 4 := by norm_num
  obtain ⟨x, h0, h1⟩ := exists_spin_pair_four hp2 hq (hR 0) h5 hlin
  have e0 : (stdSL2 (GaloisField p f) 0).map (MulAut.conj x).toMonoidHom = R 0 := h0.symm
  refine ⟨x, h1, h0, fun j => ?_⟩
  by_cases hj : j = 0
  · exact ⟨0, by rw [hj]; exact e0⟩
  have cq := centralQuot_plus hp2 (le_refl 4) hm3 hq
  have hclique :=
    CFSG.ClassicalInvolution.RouteD.Exotic.cliqueFour_fund_spin hp2 hq hm3 cq.perf
  obtain ⟨F₄, d1, d2, d3, k1, k2, k3, hall⟩ := hclique ⟨R 0, hR 0⟩ ⟨R 1, hR 1⟩ ⟨R 2, hR 2⟩
    (fun h => absurd (hinj (congrArg Subtype.val h)) (by decide))
    (fun h => absurd (hinj (congrArg Subtype.val h)) (by decide))
    (fun h => absurd (hinj (congrArg Subtype.val h)) (by decide))
    (hcomm 0 1 (by decide)) (hcomm 0 2 (by decide)) (hcomm 1 2 (by decide))
  have h3 : (⟨R 3, hR 3⟩ : ↥(fundamentalSubgroups .POmegaPlus
      (plusDatum 4 (GaloisField p f) hm3))) = F₄ := by
    rcases hall ⟨R 3, hR 3⟩ (hcomm 0 3 (by decide)) with h | h | h
    · exact absurd (hinj (congrArg Subtype.val h)) (by decide)
    · exact absurd (hinj (congrArg Subtype.val h)) (by decide)
    · exact h
  have hstd : ∀ j : Fin 4, j ≠ 0 → Commutes (stdSL2 (GaloisField p f) 0)
      (stdSL2 (GaloisField p f) j) := by
    intro j hj
    fin_cases j
    · exact absurd rfl hj
    · exact commutes_std_zero_one
    · exact commutes_std_zero_two
    · exact commutes_std_zero_three
  have hmem : conjSub x (stdSL2 (GaloisField p f) j) ∈ fundamentalSubgroups .POmegaPlus
      (plusDatum 4 (GaloisField p f) hm3) :=
    conjSub_mem_fundamentalSubgroups (stdSL2_mem_fund hp2 hq j) x
  have hadj : Commutes (R 0) (conjSub x (stdSL2 (GaloisField p f) j)) := by
    rw [← e0]
    exact (hstd j hj).conjSub x
  rcases hall ⟨conjSub x (stdSL2 (GaloisField p f) j), hmem⟩ hadj with h | h | h
  · exact ⟨1, congrArg Subtype.val h⟩
  · exact ⟨2, congrArg Subtype.val h⟩
  · exact ⟨3, (congrArg Subtype.val h).trans (congrArg Subtype.val h3).symm⟩

end Normal

end CFSG.ClassicalInvolution.ModelFacts.D4Rigid
