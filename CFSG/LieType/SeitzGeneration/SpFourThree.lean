module

public import CFSG.LieType.SeitzGeneration.SpFourMix
public import CFSG.RankThree.PartOne.CTP.SeitzLift

public section

namespace CFSG.LieType.SeitzGeneration

open CFSG.RankThree.PartOne.CTP CFSG.RankThree.PartOne.KCSpFull CFSG.RankThree.Classical
  CFSG.Assembly.LowTwoRank
open CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag (proj)

variable {K : Type} [Field K]

theorem closure_centralizers_of_planeBlocks [Finite K] (h3 : (3 : K) ≠ 0)
    (hK : ∃ c : K, c ≠ 0 ∧ c ≠ 1) {E : Subgroup (StatedSp 2 K)} {a b : StatedSp 2 K}
    {P₀ P₁ : Submodule K (Fin 2 ⊕ Fin 2 → K)} (hcomm : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x)
    (hexp : ∀ x ∈ E, x ^ 3 = 1) (B : PlaneBlocks E a b P₀ P₁) :
    Subgroup.closure {g : StatedSp 2 K | ∃ x ∈ E, x ≠ 1 ∧ g * x = x * g} = ⊤ := by
  set H : Subgroup (StatedSp 2 K) :=
    Subgroup.closure {g : StatedSp 2 K | ∃ x ∈ E, x ≠ 1 ∧ g * x = x * g} with hH
  have hC₁ : ∀ v ∈ P₁, TransCenter H v := fun v hv t =>
    Subgroup.subset_closure ⟨a, B.ha, B.ha1, commute_spTransvection (B.fix_a v hv) t⟩
  have hC₀ : ∀ v ∈ P₀, TransCenter H v := fun v hv t =>
    Subgroup.subset_closure ⟨b, B.hb, B.hb1, commute_spTransvection (B.fix_b v hv) t⟩
  have hab : a * b ∈ E := E.mul_mem B.ha B.hb
  have hab1 : a * b ≠ 1 := by
    intro h
    apply B.ha1
    refine eq_one_of_spEnd_fix fun v => ?_
    have hv : v ∈ P₀ ⊔ P₁ := by rw [B.sup]; trivial
    obtain ⟨p, hp, p', hp', rfl⟩ := Submodule.mem_sup.1 hv
    have h1 : spEnd (a * b) p = p := by rw [h, spEnd_one_apply]
    rw [spEnd_comp_apply, B.fix_b p hp] at h1
    rw [map_add, h1, B.fix_a p' hp']
  have hcube : (a * b) ^ 3 = 1 := by
    have hc : Commute a b := hcomm a B.ha b B.hb
    rw [hc.mul_pow, hexp a B.ha, hexp b B.hb, one_mul]
  have D : MixData H (a * b) P₀ P₁ :=
    { cube := hcube
      central := fun g hg => Subgroup.subset_closure ⟨a * b, hab, hab1, hg⟩
      center₀ := hC₀
      sup := B.sup
      orth := B.orth
      nd₀ := B.nd₀
      nd₁ := B.nd₁
      rank₀ := B.rank₀
      rank₁ := B.rank₁
      stab₀ := fun v hv => by
        rw [spEnd_comp_apply, B.fix_b v hv]
        exact B.stab_a₀ v hv
      stab₁ := fun v hv => by
        rw [spEnd_comp_apply, B.fix_a _ (B.stab_b₁ v hv)]
        exact B.stab_b₁ v hv
      norm₀ := fun v hv => by
        have h1 : spEnd (a * b) v = spEnd a v := by rw [spEnd_comp_apply, B.fix_b v hv]
        have h2 : spEnd (a * b) (spEnd a v) = spEnd a (spEnd a v) := by
          rw [spEnd_comp_apply, B.fix_b _ (B.stab_a₀ v hv)]
        rw [h1, h2]
        exact B.norm_a v hv
      norm₁ := fun v hv => by
        have h1 : spEnd (a * b) v = spEnd b v := by
          rw [spEnd_comp_apply, B.fix_a _ (B.stab_b₁ v hv)]
        have h2 : spEnd (a * b) (spEnd b v) = spEnd b (spEnd b v) := by
          rw [spEnd_comp_apply, B.fix_a _ (B.stab_b₁ _ (B.stab_b₁ v hv))]
        rw [h1, h2]
        exact B.norm_b v hv }
  obtain ⟨y₀, hy₀, y₁, hy₁, hy₀0, hy₁0, hc⟩ := exists_mixed_center h3 hK D
  have hmix : ∀ y₀' ∈ P₀, ∀ y₁' ∈ P₁, y₀' ≠ 0 → y₁' ≠ 0 → TransCenter H (y₀' + y₁') := by
    intro y₀' hy₀' y₁' hy₁' h0 h1
    have o₀₁ : ∀ x ∈ P₁, ∀ c ∈ P₀, spForm 2 K x c = 0 := fun x hx c hc => by
      rw [← spForm_isAlt.neg_eq c x, B.orth c hc x hx, neg_zero]
    obtain ⟨g₀, hg₀, hg₀y, hg₀fix⟩ := exists_mem_fixing_eq (U := P₀) B.nd₀ hC₀ hy₀ hy₀' hy₀0 h0
    obtain ⟨g₁, hg₁, hg₁y, hg₁fix⟩ := exists_mem_fixing_eq (U := P₁) B.nd₁ hC₁ hy₁ hy₁' hy₁0 h1
    have e₀ : spEnd g₀ y₁ = y₁ := hg₀fix y₁ (o₀₁ y₁ hy₁)
    have e₁ : spEnd g₁ y₀' = y₀' := hg₁fix y₀' (B.orth y₀' hy₀')
    have := hc.map (H.mul_mem hg₁ hg₀)
    rwa [spEnd_comp_apply, map_add, hg₀y, e₀, map_add, e₁, hg₁y] at this
  have hspan : ⨆ i, ![P₀, P₁] i = ⊤ := by
    rw [eq_top_iff]
    intro v _
    have hv : v ∈ P₀ ⊔ P₁ := by rw [B.sup]; trivial
    obtain ⟨p, hp, p', hp', rfl⟩ := Submodule.mem_sup.1 hv
    exact Submodule.add_mem _ (Submodule.mem_iSup_of_mem (0 : Fin 2) hp)
      (Submodule.mem_iSup_of_mem (1 : Fin 2) hp')
  have hall : ∀ v, TransCenter H v := by
    refine transCenter_of_pairs (Vs := ![P₀, P₁]) hspan ?_ ?_ ?_ ?_
    · intro i j hij u hu v hv
      fin_cases i <;> fin_cases j
      · exact absurd rfl hij
      · exact B.orth u hu v hv
      · rw [← spForm_isAlt.neg_eq v u, B.orth v hv u hu, neg_zero]
      · exact absurd rfl hij
    · intro i
      fin_cases i
      · exact B.nd₀
      · exact B.nd₁
    · intro i c hc
      fin_cases i
      · exact hC₀ c hc
      · exact hC₁ c hc
    · intro i j hij y hy y' hy' hy0 hy'0
      fin_cases i <;> fin_cases j
      · exact absurd rfl hij
      · exact hmix y hy y' hy' hy0 hy'0
      · rw [add_comm]
        exact hmix y' hy' y hy hy'0 hy0
      · exact absurd rfl hij
  exact eq_top_of_transCenter hall

theorem closure_centralizers_spFour_three [Finite K] (h3 : (3 : K) ≠ 0)
    (hK : ∃ c : K, c ≠ 0 ∧ c ≠ 1) {E : Subgroup (StatedSp 2 K)}
    (hcomm : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x) (hexp : ∀ x ∈ E, x ^ 3 = 1)
    (hcard : Nat.card E = 9) :
    Subgroup.closure {g : StatedSp 2 K | ∃ x ∈ E, x ≠ 1 ∧ g * x = x * g} = ⊤ := by
  obtain ⟨a, b, P₀, P₁, B⟩ := exists_planeBlocks h3 hcomm hexp hcard
  exact closure_centralizers_of_planeBlocks h3 hK hcomm hexp B

theorem closure_centralizers_psp_four_three [Finite K] (h3 : (3 : K) ≠ 0)
    (hK : ∃ c : K, c ≠ 0 ∧ c ≠ 1) (E : Subgroup (StatedProj (StatedSp 2 K)))
    (hcomm : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x) (hexp : ∀ x ∈ E, x ^ 3 = 1)
    (hcard : Nat.card E = 9) :
    Subgroup.closure {k : StatedProj (StatedSp 2 K) | ∃ x ∈ E, x ≠ 1 ∧ k * x = x * k} = ⊤ := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  refine closure_centralizers_of_lift (proj 2 K)
    (CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher.proj_surjective (r := 2) (K := K))
    ?_ E hcomm hexp ?_
  · intro hd
    have h1 := coprime_card_ker_proj (r := 2) (K := K) (by omega) Nat.prime_three (by omega)
    exact Nat.prime_three.one_lt.ne' (Nat.eq_one_of_dvd_coprimes h1 hd (dvd_refl 3))
  · intro E' hc he hcd _
    exact closure_centralizers_spFour_three h3 hK hc he (hcd.trans hcard)

end CFSG.LieType.SeitzGeneration
