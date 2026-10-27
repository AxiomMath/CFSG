module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.Census423Three.AlphaInner
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.Census423Three.GoodGroupGen

public section

namespace CFSG.AGLEmbeddingD2.Wilson.Census423Three

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.Sec4 CFSG.RankThree.PartTwo.Sec4.Res423Two
open scoped commutatorElement

variable {X : Type} [Group X] [Finite X]

@[expose] def ThreeA (b : X) : Prop :=
  CFSG.IsQuasisimple ↥(Subgroup.centralizer ({b} : Set X)) ∧
    ∀ g ∈ Subgroup.centralizer ({b} : Set X),
      (∀ c ∈ Subgroup.centralizer ({b} : Set X), g * c = c * g) → g ^ 3 = 1

@[expose] def ThreeB (b : X) : Prop :=
  ∃ (S : Type) (_ : Group S), GoodGroup S ∧ Nonempty (↥(qRes b) ≃* S)

omit [Finite X] in
theorem map_conj_centralizer (g b : X) :
    (Subgroup.centralizer ({b} : Set X)).map (MulAut.conj g).toMonoidHom =
      Subgroup.centralizer ({g * b * g⁻¹} : Set X) := by
  rw [map_centralizer_singleton]
  rfl

omit [Finite X] in
theorem ThreeA.conj {b : X} (h : ThreeA b) (g : X) : ThreeA (g * b * g⁻¹) := by
  refine ⟨?_, ?_⟩
  · let e : ↥(Subgroup.centralizer ({b} : Set X)) ≃*
        ↥(Subgroup.centralizer ({g * b * g⁻¹} : Set X)) :=
      (Subgroup.equivMapOfInjective _ (MulAut.conj g).toMonoidHom
        (MulAut.conj g).injective).trans
        (MulEquiv.subgroupCongr (map_conj_centralizer g b))
    exact CFSG.LocalCores.isQuasisimple_of_mulEquiv e h.1
  · intro x hx hxc
    have hx' : g⁻¹ * x * g ∈ Subgroup.centralizer ({b} : Set X) := by
      rw [Subgroup.mem_centralizer_singleton_iff] at hx ⊢
      calc g⁻¹ * x * g * b = g⁻¹ * (x * (g * b * g⁻¹)) * g := by group
        _ = g⁻¹ * ((g * b * g⁻¹) * x) * g := by rw [hx]
        _ = b * (g⁻¹ * x * g) := by group
    have h3 := h.2 _ hx' (fun c hc => by
      have hgc : g * c * g⁻¹ ∈ Subgroup.centralizer ({g * b * g⁻¹} : Set X) := by
        rw [← map_conj_centralizer]
        exact ⟨c, hc, rfl⟩
      have := hxc _ hgc
      calc g⁻¹ * x * g * c = g⁻¹ * (x * (g * c * g⁻¹)) * g := by group
        _ = g⁻¹ * ((g * c * g⁻¹) * x) * g := by rw [this]
        _ = c * (g⁻¹ * x * g) := by group)
    have h4 : g⁻¹ * x ^ 3 * g = 1 := by
      have := map_pow (MulAut.conj g⁻¹) x 3
      simp only [MulAut.conj_apply, inv_inv] at this
      rw [this, h3]
    calc x ^ 3 = g * (g⁻¹ * x ^ 3 * g) * g⁻¹ := by group
      _ = 1 := by rw [h4]; group

omit [Finite X] in
noncomputable def qResEquiv (g d : X) : ↥(qRes d) ≃* ↥(qRes (g * d * g⁻¹)) :=
  (Subgroup.equivMapOfInjective _ (MulAut.conj g).toMonoidHom (MulAut.conj g).injective).trans
    (MulEquiv.subgroupCongr (by
      unfold qRes
      rw [map_inSubgroup_perfectResidual (MulAut.conj g), map_centralizer_singleton]
      rfl))

omit [Finite X] in
theorem ThreeB.conj {b : X} (h : ThreeB b) (g : X) : ThreeB (g * b * g⁻¹) := by
  obtain ⟨S, _, hS, ⟨e⟩⟩ := h
  exact ⟨S, inferInstance, hS, ⟨(qResEquiv g b).symm.trans e⟩⟩

theorem goodAt_of_threeB {b : X} (h : ThreeB b) : GoodAt b := by
  obtain ⟨S, _, hS, ⟨e⟩⟩ := h
  exact goodAt_of_goodGroup (hS.of_mulEquiv e.symm)

omit [Finite X] in
theorem qRes_eq_of_threeA {b : X} (h : ThreeA b) : qRes b = Subgroup.centralizer ({b} : Set X) := by
  apply le_antisymm (qRes_le b)
  set C := Subgroup.centralizer ({b} : Set X) with hC
  have hperf : commutator ↥C = ⊤ := h.1.1.commutator_eq_top
  have hder : ∀ n, derivedSeries ↥C n = ⊤ := by
    intro n
    induction n with
    | zero => exact derivedSeries_zero _
    | succ n ih =>
      rw [derivedSeries_succ, ih]
      have : ⁅(⊤ : Subgroup ↥C), ⊤⁆ = commutator ↥C := rfl
      rw [this, hperf]
  have hres : CFSG.perfectResidual ↥C = ⊤ := by
    unfold CFSG.perfectResidual
    simp only [hder, iInf_top]
  intro x hx
  unfold qRes inSubgroup
  rw [hres]
  exact ⟨⟨x, hx⟩, trivial, rfl⟩

theorem h1_of_goodAt {b : X} (G : GoodAt b) :
    ∀ x ∈ inSubgroup (aschbacherSolvableCore 3) (Subgroup.centralizer ({b} : Set X)) ⊓ qRes b,
      ∀ y ∈ qRes b, x * y = y * x := by
  intro x hx y hy
  have hN := G.rad
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

theorem h1_of_threeA {b : X} (h : ThreeA b) :
    ∀ x ∈ inSubgroup (aschbacherSolvableCore 3) (Subgroup.centralizer ({b} : Set X)) ⊓ qRes b,
      ∀ y ∈ qRes b, x * y = y * x := by
  set C := Subgroup.centralizer ({b} : Set X) with hC
  have hQ : qRes b = C := qRes_eq_of_threeA h
  intro x hx y hy
  rw [hQ] at hy
  have hxΘ : x ∈ inSubgroup (aschbacherSolvableCore 3) C := hx.1
  set Θ := inSubgroup (aschbacherSolvableCore 3) C with hΘ
  have hΘC : Θ ≤ C := inSubgroup_theta_le C
  set N : Subgroup ↥C := Θ.subgroupOf C with hN
  have hNn : N.Normal := by
    refine ⟨fun m hm g => ?_⟩
    rw [hN, Subgroup.mem_subgroupOf] at hm ⊢
    simpa using conj_mem_inSubgroup_theta' g.2 hm
  have hs : Group.IsSolvable N := by
    have := isSolvable_inSubgroup_theta C
    exact Group.isSolvable_of_isSolvable_injective
      (f := (Subgroup.subgroupOfEquivOfLe hΘC).toMonoidHom)
      (Subgroup.subgroupOfEquivOfLe hΘC).injective
  have := rad_of_isQuasisimple h.1 hNn hs ⟨x, hΘC hxΘ⟩
    (by rw [hN, Subgroup.mem_subgroupOf]; exact hxΘ) ⟨y, hy⟩
  exact congrArg Subtype.val this

theorem alphaVanishes_of_dichotomy (hZ : Subgroup.center X = ⊥)
    (hOut : ∀ α : MulAut X, ∃ g : X, α = MulAut.conj g) (hR : Rank2 X)
    (hcls : ∀ b : X, orderOf b = 3 →
      ThreeA b ∨ (ThreeB b ∧ ∀ e ∈ qRes b, orderOf e = 3 → ThreeA e))
    {D : Subgroup X} (hDc : ∀ x ∈ D, ∀ y ∈ D, x * y = y * x) (hDexp : ∀ x ∈ D, x ^ 3 = 1)
    (hD9 : Nat.card D = 9) : AlphaVanishes X D := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hord : ∀ b ∈ D, b ≠ 1 → orderOf b = 3 := fun b hb hb1 =>
    orderOf_eq_prime (hDexp b hb) hb1
  obtain ⟨d, hd, hd1⟩ : ∃ d ∈ D, d ≠ 1 := by
    by_contra hcon
    push Not at hcon
    have hle : D ≤ ⊥ := fun x hx => Subgroup.mem_bot.mpr (hcon x hx)
    have := Subgroup.card_le_of_le hle
    rw [Subgroup.card_bot] at this
    omega
  obtain ⟨b₁, hb₁, hb₁1, hA₁⟩ : ∃ b₁ ∈ D, b₁ ≠ 1 ∧ ThreeA b₁ := by
    rcases hcls d (hord d hd hd1) with h | ⟨hB, hA⟩
    · exact ⟨d, hd, hd1, h⟩
    · obtain ⟨e, heD, heQ, hed⟩ := step1 hR hDc hDexp hD9 hd hd1 (goodAt_of_threeB hB)
      have he1 : e ≠ 1 := fun h => hed (h ▸ Subgroup.one_mem _)
      exact ⟨e, heD, he1, hA e heQ (hord e heD he1)⟩
  refine alphaVanishes_of_local_inner hZ hOut (D := D) ?_ ?_ hb₁ hb₁1 ?_
  · intro b hb hb1
    rcases hcls b (hord b hb hb1) with h | ⟨hB, -⟩
    · exact h1_of_threeA h
    · exact h1_of_goodAt (goodAt_of_threeB hB)
  · intro b hb hb1
    rcases hcls b (hord b hb hb1) with h | ⟨hB, -⟩
    · refine le_sup_of_le_right ?_
      rw [qRes_eq_of_threeA h]
      intro x hx
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact hDc x hx b hb
    · exact step1_le hR hDc hDexp hD9 hb hb1 (goodAt_of_threeB hB)
  · intro g hgq h3
    have hQ := qRes_eq_of_threeA hA₁
    have hb₁C : b₁ ∈ Subgroup.centralizer ({b₁} : Set X) :=
      Subgroup.mem_centralizer_singleton_iff.mpr rfl
    rw [hQ] at hgq
    have hgb : g * b₁ * g⁻¹ = b₁ := hgq b₁ hb₁C
    have hgC : g ∈ Subgroup.centralizer ({b₁} : Set X) := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      calc g * b₁ = (g * b₁ * g⁻¹) * g := by group
        _ = b₁ * g := by rw [hgb]
    have hg3 := hA₁.2 g hgC (fun c hc => by
      have := hgq c hc
      calc g * c = (g * c * g⁻¹) * g := by group
        _ = c * g := by rw [this])
    have hdvd : orderOf g ∣ 3 := orderOf_dvd_of_pow_eq_one hg3
    rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h | h
    · exact orderOf_eq_one_iff.mp h
    · exact absurd (by rw [h]) h3

end CFSG.AGLEmbeddingD2.Wilson.Census423Three
