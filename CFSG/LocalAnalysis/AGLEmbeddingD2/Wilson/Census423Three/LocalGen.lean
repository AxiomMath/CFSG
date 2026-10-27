module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.Census423Three.LocalStep

public section

namespace CFSG.AGLEmbeddingD2.Wilson.Census423Three

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.Sec4 CFSG.RankThree.PartTwo.Sec4.Res423Two
open scoped commutatorElement

variable {X : Type} [Group X] [Finite X]

theorem qRes_gen [IsSimpleGroup X] (hR : Rank2 X) {D : Subgroup X}
    (hDc : ∀ x ∈ D, ∀ y ∈ D, x * y = y * x) (hDexp : ∀ x ∈ D, x ^ 3 = 1)
    (hD9 : Nat.card D = 9) (G : ∀ d ∈ D, d ≠ 1 → GoodAt d)
    (S : (⊤ : Subgroup X) ≤ Subgroup.closure
      {x : X | ∃ d ∈ D, d ≠ 1 ∧ x ∈ Subgroup.centralizer ({d} : Set X)}) :
    (⊤ : Subgroup X) ≤ Subgroup.closure {x : X | ∃ d ∈ D, d ≠ 1 ∧ x ∈ qRes d} := by
  set M : Subgroup X := Subgroup.closure {x : X | ∃ d ∈ D, d ≠ 1 ∧ x ∈ qRes d} with hM
  have hMgen : ∀ d ∈ D, d ≠ 1 → ∀ x ∈ qRes d, x ∈ M := fun d hd hd1 x hx =>
    Subgroup.subset_closure ⟨d, hd, hd1, hx⟩
  have hnorm : ∀ n : X, (∀ z ∈ D, n * z * n⁻¹ ∈ D) → n ∈ Subgroup.normalizer (M : Set X) := by
    intro n hn
    have hmap : M.map (MulAut.conj n).toMonoidHom ≤ M := by
      rw [hM, MonoidHom.map_closure, Subgroup.closure_le]
      rintro _ ⟨x, ⟨d, hd, hd1, hx⟩, rfl⟩
      have hd' : n * d * n⁻¹ ∈ D := hn d hd
      have hd1' : n * d * n⁻¹ ≠ 1 := by
        intro h
        apply hd1
        have : n * d * n⁻¹ = 1 := h
        simpa [mul_inv_eq_one] using this
      exact Subgroup.subset_closure ⟨_, hd', hd1', qRes_conj n hx⟩
    refine Subgroup.mem_normalizer_fintype fun m hm => ?_
    exact hmap ⟨m, hm, rfl⟩
  have hC : ∀ d ∈ D, d ≠ 1 → ∀ c ∈ Subgroup.centralizer ({d} : Set X),
      c ∈ Subgroup.normalizer (M : Set X) := by
    intro d hd hd1 c hc
    obtain ⟨e, heD, heQ, hed⟩ := step1 hR hDc hDexp hD9 hd hd1 (G d hd hd1)
    have he1 : e ≠ 1 := fun h => hed (h ▸ Subgroup.one_mem _)
    have hcd : c * d = d * c := Subgroup.mem_centralizer_singleton_iff.mp hc
    have hcQ : c * e * c⁻¹ ∈ qRes d := qRes_normalized hc heQ
    have hce3 : (c * e * c⁻¹) ^ 3 = 1 := by
      rw [conj_pow, hDexp e heD, mul_one, mul_inv_cancel]
    have hce1 : c * e * c⁻¹ ≠ 1 := by
      intro h
      apply he1
      have : c * e * c⁻¹ = 1 := h
      simpa [mul_inv_eq_one] using this
    obtain ⟨g, hgQ, hg⟩ := (G d hd hd1).conj3 _ hcQ e heQ hce1 hce3 he1 (hDexp e heD)
    have hgC : g ∈ Subgroup.centralizer ({d} : Set X) := qRes_le d hgQ
    have hgd : g * d = d * g := Subgroup.mem_centralizer_singleton_iff.mp hgC
    set n : X := g * c with hn
    have hne : n * e * n⁻¹ ∈ D := by
      have h1 : g * (c * e * c⁻¹) * g⁻¹ ∈ Subgroup.zpowers e := by
        rw [← hg]
        exact Subgroup.mem_zpowers _
      have h2 : n * e * n⁻¹ = g * (c * e * c⁻¹) * g⁻¹ := by rw [hn]; group
      rw [h2]
      exact (Subgroup.zpowers_le.mpr heD) h1
    have hnd : n * d * n⁻¹ = d := by
      have h1 : c * d * c⁻¹ = d := by rw [hcd]; group
      have h2 : g * d * g⁻¹ = d := by rw [hgd]; group
      calc n * d * n⁻¹ = g * (c * d * c⁻¹) * g⁻¹ := by rw [hn]; group
        _ = d := by rw [h1, h2]
    have hnD : ∀ z ∈ D, n * z * n⁻¹ ∈ D := by
      intro z hz
      rw [← sup_zpowers_eq hDexp hD9 hd hd1 heD hed] at hz
      have hmap : (Subgroup.zpowers d ⊔ Subgroup.zpowers e).map (MulAut.conj n).toMonoidHom ≤ D := by
        rw [Subgroup.map_sup, MonoidHom.map_zpowers, MonoidHom.map_zpowers]
        refine sup_le ((Subgroup.zpowers_le).mpr ?_) ((Subgroup.zpowers_le).mpr ?_)
        · change n * d * n⁻¹ ∈ D
          rw [hnd]; exact hd
        · exact hne
      exact hmap ⟨z, hz, rfl⟩
    have hnN : n ∈ Subgroup.normalizer (M : Set X) := hnorm n hnD
    have hgN : g ∈ Subgroup.normalizer (M : Set X) :=
      Subgroup.le_normalizer (hMgen d hd hd1 g hgQ)
    have : c = g⁻¹ * n := by rw [hn]; group
    rw [this]
    exact Subgroup.mul_mem _ (Subgroup.inv_mem _ hgN) hnN
  have hN : (⊤ : Subgroup X) ≤ Subgroup.normalizer (M : Set X) := by
    refine S.trans ?_
    rw [Subgroup.closure_le]
    rintro x ⟨d, hd, hd1, hx⟩
    exact hC d hd hd1 x hx
  have hMn : M.Normal := Subgroup.normalizer_eq_top_iff.mp (top_le_iff.mp hN)
  obtain ⟨d, hd, hd1⟩ : ∃ d ∈ D, d ≠ 1 := by
    by_contra hcon
    push Not at hcon
    have hle : D ≤ ⊥ := fun x hx => Subgroup.mem_bot.mpr (hcon x hx)
    have := Subgroup.card_le_of_le hle
    rw [Subgroup.card_bot] at this
    omega
  obtain ⟨q₀, hq₀Q, hq₀1, -⟩ := (G d hd hd1).elt3
  have hMbot : M ≠ ⊥ := by
    intro h
    have := hMgen d hd hd1 q₀ hq₀Q
    rw [h, Subgroup.mem_bot] at this
    exact hq₀1 this
  have := hMn
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal M with h | h
  · exact absurd h hMbot
  · rw [h]

theorem alphaVanishes_of_good [IsSimpleGroup X] (hZ : Subgroup.center X = ⊥) (hR : Rank2 X)
    {D : Subgroup X} (hDc : ∀ x ∈ D, ∀ y ∈ D, x * y = y * x) (hDexp : ∀ x ∈ D, x ^ 3 = 1)
    (hD9 : Nat.card D = 9) (G : ∀ d ∈ D, d ≠ 1 → GoodAt d)
    (S : (⊤ : Subgroup X) ≤ Subgroup.closure
      {x : X | ∃ d ∈ D, d ≠ 1 ∧ x ∈ Subgroup.centralizer ({d} : Set X)}) :
    AlphaVanishes X D := by
  refine alphaVanishes_of_local hZ ?_ ?_ (qRes_gen hR hDc hDexp hD9 G S)
  · intro b hb hb1 x hx y hy
    have hN := (G b hb hb1).rad
      (inSubgroup (aschbacherSolvableCore 3) (Subgroup.centralizer ({b} : Set X)) ⊓ qRes b)
      inf_le_right ?_ ?_ x hx y hy
    · exact hN
    · intro g hg n hn
      refine ⟨conj_mem_inSubgroup_theta' (qRes_le b hg) hn.1, ?_⟩
      exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hg hn.2) (Subgroup.inv_mem _ hg)
    · have := isSolvable_inSubgroup_theta (Subgroup.centralizer ({b} : Set X))
      exact Group.isSolvable_of_isSolvable_injective
        (Subgroup.inclusion_injective (inf_le_left :
          inSubgroup (aschbacherSolvableCore 3) (Subgroup.centralizer ({b} : Set X)) ⊓ qRes b ≤
            inSubgroup (aschbacherSolvableCore 3) (Subgroup.centralizer ({b} : Set X))))
  · intro b hb hb1
    exact step1_le hR hDc hDexp hD9 hb hb1 (G b hb hb1)

end CFSG.AGLEmbeddingD2.Wilson.Census423Three
