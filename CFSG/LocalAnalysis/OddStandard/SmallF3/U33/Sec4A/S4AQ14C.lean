module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4A.S4AL41Defs
public import CFSG.GH74.GLS.Bg.TwoGroups.L26Abel
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixIII.Basic

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33.S4A

open Subgroup

variable {G : Type} [Group G]

theorem q14_normal_subgroupOf {Q N : Subgroup G} (hN : ∀ q ∈ Q, ∀ n ∈ N, q * n * q⁻¹ ∈ N) :
    (N.subgroupOf Q).Normal :=
  ⟨fun x hx g => by
    rw [Subgroup.mem_subgroupOf] at hx ⊢
    simpa using hN g g.2 x hx⟩

theorem q14_sectionIso_of_equiv {Q N : Subgroup G} [(N.subgroupOf Q).Normal] {K : Type} [Group K]
    (e : ↥Q ⧸ N.subgroupOf Q ≃* K) : Sec4SectionIso Q N K :=
  ⟨e.toMonoidHom.comp (QuotientGroup.mk' _), e.surjective.comp (QuotientGroup.mk'_surjective _),
    by rw [MonoidHom.ker_comp_of_injective _ _ e.injective, QuotientGroup.ker_mk']⟩

theorem q14_map_conj_eq {Q N : Subgroup G} (g : G) (hgQ : g ∈ normalizer (Q : Set G))
    (hgN : g ∈ normalizer (N : Set G)) :
    (N.subgroupOf Q).map (Q.normalizerMonoidHom ⟨g, hgQ⟩).toMonoidHom = N.subgroupOf Q := by
  ext x
  constructor
  · intro hx
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hx
    rw [Subgroup.mem_subgroupOf] at hy ⊢
    exact (Subgroup.mem_normalizer_iff.mp hgN (y : G)).mp hy
  · intro hx
    rw [Subgroup.mem_subgroupOf] at hx
    have hyQ : g⁻¹ * (x : G) * g ∈ Q := (Subgroup.mem_normalizer_iff''.mp hgQ (x : G)).mp x.2
    have hyN : g⁻¹ * (x : G) * g ∈ N := (Subgroup.mem_normalizer_iff''.mp hgN (x : G)).mp hx
    refine Subgroup.mem_map.mpr ⟨⟨g⁻¹ * (x : G) * g, hyQ⟩, Subgroup.mem_subgroupOf.mpr hyN, ?_⟩
    apply Subtype.ext
    show g * (g⁻¹ * (x : G) * g) * g⁻¹ = (x : G)
    group

@[expose] noncomputable def quotConj (Q N : Subgroup G) [(N.subgroupOf Q).Normal] (g : G)
    (hgQ : g ∈ normalizer (Q : Set G)) (hgN : g ∈ normalizer (N : Set G)) :
    MulAut (↥Q ⧸ N.subgroupOf Q) :=
  QuotientGroup.congr (N.subgroupOf Q) (N.subgroupOf Q) (Q.normalizerMonoidHom ⟨g, hgQ⟩)
    (q14_map_conj_eq g hgQ hgN)

theorem quotConj_mk {Q N : Subgroup G} [(N.subgroupOf Q).Normal] {g : G}
    (hgQ : g ∈ normalizer (Q : Set G)) (hgN : g ∈ normalizer (N : Set G)) (q : ↥Q)
    (hq : g * (q : G) * g⁻¹ ∈ Q) :
    quotConj Q N g hgQ hgN (QuotientGroup.mk q) = QuotientGroup.mk ⟨g * q * g⁻¹, hq⟩ :=
  rfl

theorem quotConj_fix_iff {Q N : Subgroup G} [(N.subgroupOf Q).Normal] {g : G}
    (hgQ : g ∈ normalizer (Q : Set G)) (hgN : g ∈ normalizer (N : Set G)) (q : ↥Q) :
    quotConj Q N g hgQ hgN (QuotientGroup.mk q) = QuotientGroup.mk q ↔
      g * (q : G) * g⁻¹ * (q : G)⁻¹ ∈ N := by
  have hq : g * (q : G) * g⁻¹ ∈ Q := (Subgroup.mem_normalizer_iff.mp hgQ q).mp q.2
  rw [quotConj_mk hgQ hgN q hq, QuotientGroup.eq]
  have h1 : (⟨g * (q : G) * g⁻¹, hq⟩ : ↥Q)⁻¹ * q ∈ N.subgroupOf Q ↔
      (⟨g * (q : G) * g⁻¹, hq⟩ : ↥Q) * q⁻¹ ∈ N.subgroupOf Q := by
    constructor
    · intro hmem
      have h2 : q⁻¹ * (⟨g * (q : G) * g⁻¹, hq⟩ : ↥Q) ∈ N.subgroupOf Q := by
        simpa using inv_mem hmem
      exact Subgroup.Normal.mem_comm inferInstance h2
    · intro hmem
      have h2 : q⁻¹ * (⟨g * (q : G) * g⁻¹, hq⟩ : ↥Q) ∈ N.subgroupOf Q :=
        Subgroup.Normal.mem_comm inferInstance hmem
      simpa using inv_mem h2
  rw [h1, Subgroup.mem_subgroupOf]
  rfl

theorem quotConj_pow_three {Q N : Subgroup G} [(N.subgroupOf Q).Normal] {g : G}
    (hgQ : g ∈ normalizer (Q : Set G)) (hgN : g ∈ normalizer (N : Set G)) (hg : g ^ 3 = 1) :
    quotConj Q N g hgQ hgN ^ 3 = 1 := by
  have hφ : (Q.normalizerMonoidHom ⟨g, hgQ⟩) ^ 3 = 1 := by
    rw [← map_pow]
    have h3 : (⟨g, hgQ⟩ : normalizer (Q : Set G)) ^ 3 = 1 := Subtype.ext (by simpa using hg)
    rw [h3, map_one]
  ext x
  induction x using QuotientGroup.induction_on with
  | H q =>
    have e3 : (quotConj Q N g hgQ hgN ^ 3) (QuotientGroup.mk q) =
        QuotientGroup.mk (((Q.normalizerMonoidHom ⟨g, hgQ⟩) ^ 3) q) := rfl
    rw [e3, hφ]
    rfl

theorem q14_quot_E4 {X : Type} [Group X] [Finite X] (hX : Nat.card X = 4) (α : MulAut X)
    (hα : α ^ 3 = 1) (hfix : ∀ x : X, α x = x → x = 1) :
    Nonempty (X ≃* CFSG.GH74.GLS.Bg.TwoGroups.E2 2) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hc : ∀ a b : X, a * b = b * a := by
    intro a b
    haveI := IsPGroup.isMulCommutative_of_card_eq_prime_sq (p := 2) (G := X) (by rw [hX]; norm_num)
    exact mul_comm' a b
  have h2 : ∀ x : X, x * x = 1 := by
    by_contra hcon
    push Not at hcon
    obtain ⟨x, hx⟩ := hcon
    have hdvd : orderOf x ∣ 4 := hX ▸ orderOf_dvd_natCard x
    have hne2 : orderOf x ≠ 2 := by
      intro h2'
      apply hx
      rw [← pow_two, ← h2']
      exact pow_orderOf_eq_one x
    have hne1 : orderOf x ≠ 1 := by
      intro h1
      apply hx
      rw [orderOf_eq_one_iff] at h1
      rw [h1]
      simp
    have h4 : orderOf x = 4 := by
      have hle : orderOf x ≤ 4 := Nat.le_of_dvd (by norm_num) hdvd
      have hpos : 0 < orderOf x := orderOf_pos x
      have hcases : orderOf x = 1 ∨ orderOf x = 2 ∨ orderOf x = 3 ∨ orderOf x = 4 := by omega
      rcases hcases with h | h | h | h
      · exact absurd h hne1
      · exact absurd h hne2
      · rw [h] at hdvd
        omega
      · exact h
    haveI : IsCyclic X := isCyclic_of_orderOf_eq_card x (by rw [h4, hX])
    have hcard : Nat.card (MulAut X) = 2 := by
      rw [IsCyclic.card_mulAut, hX]
      decide
    have hα2 : α ^ 2 = 1 := by
      rw [← hcard]
      exact pow_card_eq_one'
    have hα1 : α = 1 := by
      calc α = α ^ 3 * (α ^ 2)⁻¹ := by group
        _ = 1 := by rw [hα, hα2]; simp
    exact hx (by rw [hfix x (by rw [hα1]; rfl)]; simp)
  exact CFSG.GH74.GLS.Bg.TwoGroups.L26.elemAbelian_equiv hc h2 2 (by rw [hX]; norm_num)

end CFSG.OddStandard.SmallF3.HarrisU33.S4A
