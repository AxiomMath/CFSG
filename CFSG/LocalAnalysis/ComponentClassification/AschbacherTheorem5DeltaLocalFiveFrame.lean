module

public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTheorem5DeltaLocalFiveLift
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTheorem3Transport
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTheorem5DeltaLocalFiveStar
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTheorem5DeltaLocalSeven

public section

open CFSG.Open
open CFSG.ComponentClassification.AschbacherTightEmbedding
open CFSG.ABGLocalTools

namespace CFSG.ComponentClassification.AschbacherTheorem5

namespace DeltaLocal.Five

open SectionSix SectionSix.BarTools

variable {G : Type} [Group G] [Finite G] {D : Subgroup G} {r : ℕ}
  {Abar : Fin r → Subgroup (D ⧸ aschbacherThm5OddCore D)}

theorem ti_bar (hC : Counterexample G D r Abar) {i : Fin r} {g : G} {E : Subgroup G}
    (hEZ : E ≤ rightConjugate (zStar D Abar) g) (hEH : E ≤ Subgroup.normalizer (D : Set G))
    (hE2 : IsPGroup 2 E) {x : Bar D} (hx : x ∈ bar D (aschbacherThm5Preimage D (Abar i)))
    (hxH : x ∉ bar D ((aschbacherThm5Preimage D (Abar i) ⊓
      rightConjugate (Subgroup.normalizer (D : Set G)) g) ⊔ E)) :
    bar D E ⊓ rightConjugate (bar D E) x = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨x₀, hx₀A, rfl⟩ := (mem_bar_iff D _ x).mp hx
  rw [← bar_rightConjugate]
  by_contra hne
  have h2 : IsPGroup 2 (bar D E ⊓ bar D (rightConjugate E x₀) : Subgroup (Bar D)) :=
    (isPGroup_bar hE2).to_le inf_le_left
  obtain ⟨wb, hwb, hwb2⟩ := exists_orderOf_eq_two h2 hne
  obtain ⟨w, hwE, rfl⟩ := (mem_bar_iff D E wb).mp hwb.1
  obtain ⟨w', hw'E, hw'w⟩ := (mem_bar_iff D (rightConjugate E x₀) _).mp hwb.2
  have hwmem : (w : G) ∈ rightConjugate E x₀ ⊔ aschbacherThm5Core D := by
    have hmem : (w' : G)⁻¹ * w ∈ aschbacherThm5Core D := by
      have h1 : toBar D (w'⁻¹ * w) = 1 := by rw [map_mul, map_inv, hw'w, inv_mul_cancel]
      exact (toBar_eq_one_iff D _).mp h1
    have := Subgroup.mul_mem_sup hw'E hmem
    simpa using this
  obtain ⟨n, hn⟩ := hE2 ⟨w, hwE⟩
  have hwn : (w : G) ^ (2 ^ n) = 1 := by
    have := congrArg Subtype.val hn
    simpa using this
  obtain ⟨o, ho, hRo⟩ := le_rightConjugate_of_le_sup_core
    (rightConjugate_le_normalizer hEH x₀) (isPGroup_zpowers_of_pow hwn)
    (Subgroup.zpowers_le.mpr hwmem)
  rw [rightConjugate_mul] at hRo
  have hwy := hRo (Subgroup.mem_zpowers (w : G))
  rw [mem_rightConjugate_iff] at hwy
  have hoH : o ∈ Subgroup.normalizer (D : Set G) := core_le_normalizer D ho
  have hw1 : (w : G) ≠ 1 := by
    intro h
    rw [show w = 1 from Subtype.ext h, map_one, orderOf_one] at hwb2
    omega
  have hyHg : (x₀ : G) * o ∈ rightConjugate (Subgroup.normalizer (D : Set G)) g := by
    refine mem_conj_normalizer_of_zStar hC g (t := (x₀ * o) * w * (x₀ * o)⁻¹) (y := x₀ * o)
      (hEZ hwy) ?_ ⟨n, ?_⟩ ?_
    · rw [show ((x₀ : G) * o)⁻¹ * ((x₀ * o) * w * (x₀ * o)⁻¹) * (x₀ * o) = w by group]
      exact hEZ hwE
    · rw [conj_pow, hwn]
      group
    · intro h
      apply hw1
      calc (w : G) = ((x₀ : G) * o)⁻¹ * ((x₀ * o) * w * (x₀ * o)⁻¹) * (x₀ * o) := by group
        _ = 1 := by rw [h]; group
  have hyN : (x₀ : G) * o ∈ Subgroup.normalizer (D : Set G) := Subgroup.mul_mem _ x₀.2 hoH
  have hyA : (x₀ : G) * o ∈ aschbacherThm5Preimage D (Abar i) :=
    Subgroup.mul_mem _ hx₀A (core_le_preimage D _ ho)
  apply hxH
  have hxy : toBar D x₀ = toBar D ⟨(x₀ : G) * o, hyN⟩ := by
    have h1 : toBar D ⟨o, hoH⟩ = 1 := (toBar_eq_one_iff D _).mpr ho
    have hsplit : (⟨(x₀ : G) * o, hyN⟩ : Subgroup.normalizer (D : Set G)) = x₀ * ⟨o, hoH⟩ := rfl
    rw [hsplit, map_mul, h1, mul_one]
  rw [hxy]
  exact bar_mono D le_sup_left (toBar_mem_bar D (h := ⟨(x₀ : G) * o, hyN⟩) ⟨hyA, hyHg⟩)

theorem exists_of_lemma_4_9 (hin : SectionSixInputs) (hC : Counterexample G D r Abar)
    (i : Fin r) {g : G} {E : Subgroup G} (hEZ : E ≤ rightConjugate (zStar D Abar) g)
    (hEH : E ≤ Subgroup.normalizer (D : Set G)) (hE2 : IsPGroup 2 E)
    (hEA : E ≤ Subgroup.normalizer (aschbacherThm5Preimage D (Abar i) : Set G))
    (hodd : Odd (Nat.card (rightConjugate (zStar D Abar) g ⊓
      aschbacherThm5Preimage D (Abar i) : Subgroup G)))
    (hrank : 2 ≤ CFSG.Open.pRank 2 E)
    {m : ℕ} {K : Fin m → Subgroup (Bar D)} (hK : ∀ l, IsComponentOf (K l) ⊤)
    (hcomm : ∀ l l', l ≠ l' → ∀ x ∈ K l, ∀ y ∈ K l', x * y = y * x)
    (hgen : ⨆ l, K l = bar D (aschbacherThm5Preimage D (Abar i))) (l : Fin m)
    (hKE : bar D E ≤ Subgroup.normalizer (K l : Set (Bar D)))
    (hKH : ¬ K l ≤ bar D ((aschbacherThm5Preimage D (Abar i) ⊓
      rightConjugate (Subgroup.normalizer (D : Set G)) g) ⊔ E))
    (hZ : CFSG.Open.pRank 2 (AschbacherTheorem3.centerOf (K l) ⊓
      Subgroup.centralizer (bar D E : Set (Bar D))) ≤ CFSG.Open.pRank 2 (bar D E)) :
    ∃ a ∈ K l, (∃ k : ℕ, a ^ (2 ^ k) = 1) ∧
      a ∈ Subgroup.centralizer (bar D E : Set (Bar D)) ∧
      a ∉ AschbacherTheorem3.centerOf (K l) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set A := aschbacherThm5Preimage D (Abar i) with hAdef
  set Hg := rightConjugate (Subgroup.normalizer (D : Set G)) g with hHgdef
  set P := rightConjugate (zStar D Abar) g ⊓ A with hPdef
  have hAH : A ≤ Subgroup.normalizer (D : Set G) := (preimage_le D _).trans Subgroup.le_normalizer
  have hOA : aschbacherThm5Core D ≤ A := core_le_preimage D _
  have hPH : P ≤ Subgroup.normalizer (D : Set G) := inf_le_right.trans hAH
  have hZg : rightConjugate (zStar D Abar) g ≤ Hg :=
    AschbacherTheorem3.rightConjugate_le_rightConjugate zStar_le_normalizer g
  have hHgN : Hg ≤ Subgroup.normalizer (rightConjugate (zStar D Abar) g : Set G) :=
    AschbacherTheorem3.rightConjugate_le_normalizer (normalizer_le_normalizer_zStar hC.hyp) g
  have hEA0 : E ⊓ A = ⊥ :=
    two_subgroup_of_odd_eq_bot _ P (hE2.to_le inf_le_left) hodd (inf_le_inf_right A hEZ)
  have hPE : P ⊓ E = ⊥ :=
    two_subgroup_of_odd_eq_bot _ P (hE2.to_le inf_le_right) hodd inf_le_left
  have hEP : E ≤ Subgroup.normalizer (P : Set G) := fun e he =>
    Subgroup.inf_normalizer_le_normalizer_inf ⟨Subgroup.le_normalizer (hEZ he), hEA he⟩
  have hE1 : E ≠ ⊥ := by
    intro h
    obtain ⟨F, hFE, -, hF4⟩ := CFSG.SectionRank.exists_isElemAbelian_card_of_le_pRank (p := 2) hrank
    rw [h, le_bot_iff] at hFE
    rw [hFE, Subgroup.card_bot] at hF4
    norm_num at hF4
  have hF : AschbacherTheorem3.Frame (bar D A) (bar D E) :=
    ⟨bar_le_normalizer hEA hAH, by
      rw [← bar_inf_of_core_le hOA, hEA0, bar, Subgroup.bot_subgroupOf, Subgroup.map_bot],
      isPGroup_bar hE2⟩
  obtain ⟨S, hSF⟩ := hF.exists_sylowFrame
  have hQH : P ⊔ E ≤ (A ⊓ Hg) ⊔ E :=
    sup_le_sup_right (le_inf inf_le_right (inf_le_left.trans hZg)) E
  have hnorm : (A ⊓ Hg) ⊔ E ≤ Subgroup.normalizer ((P ⊔ E : Subgroup G) : Set G) := by
    refine sup_le (fun a ha => ?_) (le_sup_right.trans Subgroup.le_normalizer)
    have haA : a ∈ A := ha.1
    have haHg : a ∈ Hg := ha.2
    apply AschbacherToolkit.mem_normalizer_of_conj_le
    have hle : P ⊔ E ≤ (P ⊔ E).comap (MulAut.conj a).toMonoidHom := by
      refine sup_le (fun p hp => ?_) (fun e he => ?_)
      · rw [Subgroup.mem_comap]
        show a * p * a⁻¹ ∈ P ⊔ E
        exact Subgroup.mem_sup_left ⟨(Subgroup.mem_normalizer_iff.mp (hHgN haHg) p).mp hp.1,
          (Subgroup.mem_normalizer_iff.mp (Subgroup.le_normalizer haA) p).mp hp.2⟩
      · rw [Subgroup.mem_comap]
        show a * e * a⁻¹ ∈ P ⊔ E
        have h1 : a * e * a⁻¹ * e⁻¹ ∈ P := by
          refine ⟨Subgroup.mul_mem _ ((Subgroup.mem_normalizer_iff.mp (hHgN haHg) e).mp
            (hEZ he)) (Subgroup.inv_mem _ (hEZ he)), ?_⟩
          have h2 := (Subgroup.mem_normalizer_iff.mp (hEA he) a⁻¹).mp (Subgroup.inv_mem _ haA)
          have h3 := Subgroup.mul_mem _ haA h2
          rwa [show a * (e * a⁻¹ * e⁻¹) = a * e * a⁻¹ * e⁻¹ by group] at h3
        have := Subgroup.mul_mem_sup h1 he
        simpa using this
    exact fun y hy => hle hy
  have hHyp : AschbacherTheorem3.Hyp43 (bar D A) (bar D E) (bar D (P ⊔ E))
      (bar D ((A ⊓ Hg) ⊔ E)) :=
    { le := bar_mono D hQH
      le_normalizer := bar_le_normalizer hnorm (sup_le hPH hEH)
      le_sup := by
        rw [← bar_sup hAH hEH]
        exact bar_mono D (sup_le_sup_right inf_le_left E)
      sylow := isSylowOf_bar (isSylowOf_sup_of_odd hEP hodd hE2 hPE) (sup_le hPH hEH)
      inf_eq_bot := fun _ hx hxH => ti_bar hC hEZ hEH hE2 hx hxH }
  have hT1 : bar D E ≠ ⊥ := fun h => hE1 ((bar_eq_bot_iff_of_isPGroup hE2 hEH).mp h)
  have hsolv : Group.IsSolvable (bar D (P ⊔ E)) := by
    have : Group.IsSolvable (P ⊔ E : Subgroup G) := isSolvable_sup_of_odd hEP hodd hE2 hPE
    have : Group.IsSolvable ((P ⊔ E).subgroupOf (Subgroup.normalizer (D : Set G))) :=
      Group.isSolvable_of_isSolvable_injective
        (f := (Subgroup.subgroupOfEquivOfLe (sup_le hPH hEH)).toMonoidHom) (MulEquiv.injective _)
    exact Group.isSolvable_of_surjective (f := (toBar D).subgroupMap ((P ⊔ E).subgroupOf _))
      ((toBar D).subgroupMap_surjective _)
  have hrankQ : 1 < CFSG.Open.pRank 2 (bar D (P ⊔ E)) := by
    have h1 := Seven.pRank_le_bar hEH
    have h2 := CFSG.SectionRank.pRank_mono (p := 2) (by norm_num)
      (bar_mono D (le_sup_right : E ≤ P ⊔ E))
    omega
  exact hin.lemma_4_9 (Bar D) (bar D A) (bar D E) S (bar D (P ⊔ E)) (bar D ((A ⊓ Hg) ⊔ E)) (K l)
    hSF hHyp hT1 hsolv (layer_eq_top_of_iSup hK hcomm hgen) (isComponentOf_of_iSup hK hcomm hgen l)
    hKE hrankQ hKH hZ

end DeltaLocal.Five

end CFSG.ComponentClassification.AschbacherTheorem5
