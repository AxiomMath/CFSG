module

public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.OuterHighD4Three

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.OuterHigh3

section Abstract

open CFSG.RankThree.PartOne.CTP CFSG.Open

variable {G : Type*} [Group G]

@[expose] def SylowPairGenAt (α : MulAut G) : Prop :=
  ∀ P : Subgroup G, IsPGroup 3 P → P ≤ fixedSubgroup α →
    Subgroup.closure ((Subgroup.centralizer (P : Set G) : Set G) ∪ (fixedSubgroup α : Set G)) = ⊤

@[expose] def FixedPlanesAt (α : MulAut G) : Prop :=
  ∀ P : Subgroup G, IsElemAbelian 3 P → Nat.card P = 3 ^ 2 → P ≤ fixedSubgroup α →
    fixedSubgroup α ≤
      Subgroup.closure {u : G | u ∈ fixedSubgroup α ∧ ∃ e ∈ P, e ≠ 1 ∧ e * u = u * e}

theorem sylowPairGenAt_congr {α β : MulAut G} (h : fixedSubgroup α = fixedSubgroup β)
    (hα : SylowPairGenAt α) : SylowPairGenAt β := by
  intro P hP hPβ
  rw [← h] at hPβ ⊢
  exact hα P hP hPβ

theorem fixedPlanesAt_congr {α β : MulAut G} (h : fixedSubgroup α = fixedSubgroup β)
    (hα : FixedPlanesAt α) : FixedPlanesAt β := by
  intro P hP hPc hPβ
  rw [← h] at hPβ ⊢
  exact hα P hP hPc hPβ

theorem fixedSubgroup_inv_eq (α : MulAut G) : fixedSubgroup α⁻¹ = fixedSubgroup α := by
  ext g
  rw [mem_fixedSubgroup, mem_fixedSubgroup]
  constructor
  · intro h
    have e := congrArg α h
    rw [MulAut.apply_inv_self G α g] at e
    exact e.symm
  · intro h
    have e := congrArg (fun y => α⁻¹ y) h
    simp only [MulAut.inv_apply_self G α g] at e
    exact e.symm

theorem sylowPairGenAt_conj (ψ : MulAut G) {α : MulAut G} (h : SylowPairGenAt α) :
    SylowPairGenAt (ψ * α * ψ⁻¹) := by
  intro P hP hPα
  rw [fixedSubgroup_conj] at hPα ⊢
  set P' := P.map (ψ⁻¹).toMonoidHom with hP'
  have hP'α : P' ≤ fixedSubgroup α := by
    rintro _ ⟨x, hx, rfl⟩
    obtain ⟨y, hy, rfl⟩ := hPα hx
    show α (ψ⁻¹ (ψ y)) = ψ⁻¹ (ψ y)
    rw [MulAut.inv_apply_self G ψ y]
    exact hy
  have htop := h P' (hP.map _) hP'α
  rw [eq_top_iff, ← Subgroup.map_top_of_surjective ψ.toMonoidHom ψ.surjective, ← htop,
    MonoidHom.map_closure]
  refine Subgroup.closure_mono ?_
  rintro _ ⟨u, hu | hu, rfl⟩
  · left
    rw [SetLike.mem_coe, Subgroup.mem_centralizer_iff] at hu ⊢
    intro p hp
    have h1 := hu (ψ⁻¹ p) ⟨p, hp, rfl⟩
    have h2 := congrArg ψ h1
    rw [map_mul, map_mul, MulAut.apply_inv_self G ψ p] at h2
    exact h2
  · right
    exact ⟨u, hu, rfl⟩

theorem fixedPlanesAt_conj (ψ : MulAut G) {α : MulAut G} (h : FixedPlanesAt α) :
    FixedPlanesAt (ψ * α * ψ⁻¹) := by
  intro P hP hPc hPα
  rw [fixedSubgroup_conj] at hPα ⊢
  set P' := P.map (ψ⁻¹).toMonoidHom with hP'
  have hP'α : P' ≤ fixedSubgroup α := by
    rintro _ ⟨x, hx, rfl⟩
    obtain ⟨y, hy, rfl⟩ := hPα hx
    show α (ψ⁻¹ (ψ y)) = ψ⁻¹ (ψ y)
    rw [MulAut.inv_apply_self G ψ y]
    exact hy
  have hP'c : Nat.card P' = 3 ^ 2 := by
    rw [hP', Subgroup.card_map_of_injective (ψ⁻¹).injective, hPc]
  have hle := h P' (CFSG.Open.IsElemAbelian.map hP (ψ⁻¹).toMonoidHom) hP'c hP'α
  rintro _ ⟨u, hu, rfl⟩
  have hmem := hle hu
  have hmap : (Subgroup.closure {u : G | u ∈ fixedSubgroup α ∧
      ∃ e ∈ P', e ≠ 1 ∧ e * u = u * e}).map ψ.toMonoidHom ≤
      Subgroup.closure {u : G | u ∈ (fixedSubgroup α).map ψ.toMonoidHom ∧
        ∃ e ∈ P, e ≠ 1 ∧ e * u = u * e} := by
    rw [MonoidHom.map_closure]
    refine Subgroup.closure_mono ?_
    rintro _ ⟨v, ⟨hvα, _, ⟨e, heP, rfl⟩, he1, hev⟩, rfl⟩
    refine ⟨⟨v, hvα, rfl⟩, e, heP, fun h1 => he1 ?_, ?_⟩
    · show ψ⁻¹ e = 1
      rw [show e = 1 from h1, map_one]
    · have hev' : ψ⁻¹ e * v = v * ψ⁻¹ e := hev
      have h2 := congrArg ψ hev'
      rw [map_mul, map_mul, MulAut.apply_inv_self G ψ e] at h2
      exact h2
  exact hmap ⟨u, hmem, rfl⟩

theorem exists_conj_le_of_forall_card_le [Finite G] {p : ℕ} [Fact p.Prime] {C Q : Subgroup G}
    (hQC : Q ≤ C) (hQ : IsPGroup p Q)
    (hmax : ∀ R : Subgroup G, IsPGroup p R → R ≤ C → Nat.card R ≤ Nat.card Q)
    {P : Subgroup G} (hPC : P ≤ C) (hP : IsPGroup p P) :
    ∃ c ∈ C, ∀ x ∈ P, c⁻¹ * x * c ∈ Q := by
  classical
  have hcard : ∀ {X : Subgroup G}, X ≤ C → Nat.card (X.subgroupOf C) = Nat.card X :=
    fun hX => Nat.card_congr (Subgroup.subgroupOfEquivOfLe hX).toEquiv
  have hQsyl : Nat.card (Q.subgroupOf C) = p ^ (Nat.card C).factorization p := by
    rw [hcard hQC]
    obtain ⟨S⟩ := (inferInstance : Nonempty (Sylow p C))
    have hS := Sylow.card_eq_multiplicity S
    refine le_antisymm ?_ ?_
    · have hQp' : IsPGroup p (Q.subgroupOf C) := by
        obtain ⟨n, hn⟩ := IsPGroup.iff_card.1 hQ
        exact IsPGroup.of_card (n := n) (by rw [hcard hQC, hn])
      obtain ⟨S', hS'⟩ := hQp'.exists_le_sylow
      have h1 := Subgroup.card_le_of_le hS'
      rw [hcard hQC, Sylow.card_eq_multiplicity] at h1
      exact h1
    · have hR : IsPGroup p ((S : Subgroup C).map C.subtype) := S.isPGroup'.map _
      have h2 := hmax _ hR (Subgroup.map_subtype_le _)
      rw [← hS]
      calc Nat.card (S : Subgroup C) = Nat.card ((S : Subgroup C).map C.subtype) :=
            (Nat.card_congr (Subgroup.equivMapOfInjective _ _ C.subtype_injective).toEquiv)
        _ ≤ Nat.card Q := h2
  have hPp : IsPGroup p (P.subgroupOf C) := by
    obtain ⟨n, hn⟩ := IsPGroup.iff_card.1 hP
    exact IsPGroup.of_card (n := n) (by rw [hcard hPC, hn])
  obtain ⟨S, hS⟩ := hPp.exists_le_sylow
  obtain ⟨c, hc⟩ := MulAction.exists_smul_eq C (Sylow.ofCard _ hQsyl) S
  refine ⟨c, c.2, fun x hx => ?_⟩
  have hxS : (⟨x, hPC hx⟩ : C) ∈ (S : Subgroup C) := hS (by rw [Subgroup.mem_subgroupOf]; exact hx)
  rw [← hc, Sylow.coe_subgroup_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem,
    Sylow.coe_ofCard, Subgroup.mem_subgroupOf] at hxS
  simp only [MulAut.smul_def, map_inv, MulAut.conj_inv_apply] at hxS
  simpa [mul_assoc] using hxS

theorem sylowPairGenAt_of_conj_eq {α β : MulAut G} (ψ : MulAut G) (hβ : SylowPairGenAt β)
    (h : ψ * α * ψ⁻¹ = β ∨ ψ * α * ψ⁻¹ = β⁻¹) : SylowPairGenAt α := by
  have hβ' : SylowPairGenAt (ψ * α * ψ⁻¹) := by
    rcases h with h | h
    · rwa [h]
    · rw [h]
      exact sylowPairGenAt_congr (fixedSubgroup_inv_eq β).symm hβ
  have h' := sylowPairGenAt_conj ψ⁻¹ hβ'
  rwa [show ψ⁻¹ * (ψ * α * ψ⁻¹) * ψ⁻¹⁻¹ = α by group] at h'

theorem fixedPlanesAt_of_conj_eq {α β : MulAut G} (ψ : MulAut G) (hβ : FixedPlanesAt β)
    (h : ψ * α * ψ⁻¹ = β ∨ ψ * α * ψ⁻¹ = β⁻¹) : FixedPlanesAt α := by
  have hβ' : FixedPlanesAt (ψ * α * ψ⁻¹) := by
    rcases h with h | h
    · rwa [h]
    · rw [h]
      exact fixedPlanesAt_congr (fixedSubgroup_inv_eq β).symm hβ
  have h' := fixedPlanesAt_conj ψ⁻¹ hβ'
  rwa [show ψ⁻¹ * (ψ * α * ψ⁻¹) * ψ⁻¹⁻¹ = α by group] at h'

theorem sylowPairGenAt_of_sylow_central [Finite G] {α : MulAut G} {Q : Subgroup G}
    (hQα : Q ≤ fixedSubgroup α) (hQ : IsPGroup 3 Q)
    (hmax : ∀ R : Subgroup G, IsPGroup 3 R → R ≤ fixedSubgroup α → Nat.card R ≤ Nat.card Q)
    {d : G} (hd : ∀ y ∈ Q, y * d = d * y)
    (htop : Subgroup.closure ((fixedSubgroup α : Set G) ∪ {d}) = ⊤) : SylowPairGenAt α := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  intro P hP hPα
  obtain ⟨c, hcα, hcP⟩ := exists_conj_le_of_forall_card_le hQα hQ hmax hPα hP
  have hcα' : α c = c := hcα
  refine CFSG.LieType.SeitzGeneration.ExcWideThree.Parrott.D4Graph.eq_top_of_closure_image
    (MulAut.conj c) htop ?_
  rintro _ ⟨y, hy | hy, rfl⟩
  · right
    have hy' : α y = y := hy
    show α (c * y * c⁻¹) = c * y * c⁻¹
    rw [map_mul, map_mul, map_inv, hcα', hy']
  · left
    rw [Set.mem_singleton_iff] at hy
    subst hy
    rw [SetLike.mem_coe, Subgroup.mem_centralizer_iff]
    intro x hx
    have h := hd _ (hcP x hx)
    rw [MulAut.conj_apply]
    calc x * (c * y * c⁻¹) = c * ((c⁻¹ * x * c) * y) * c⁻¹ := by group
      _ = c * (y * (c⁻¹ * x * c)) * c⁻¹ := by rw [h]
      _ = c * y * c⁻¹ * x := by group

end Abstract

section GraphCube

set_option linter.unusedSectionVars false


open CFSG.LieType.Seitz CFSG.RankThree.PartOne.CTP CFSG.LieType.SeitzGeneration
  CFSG.LieType.SeitzGeneration.ExcWideThree CFSG.LieType.Chevalley CFSG.Blueprint.Chevalley
  CFSG.Open

variable {K : Type} [Field K] [Finite K]

theorem graph_cube_inner_part {E : Subgroup (MulAut ↥(adjointGroup Tag.D4 K))}
    (hE : IsElemAbelian 3 E) (hc : Nat.card E = 3 ^ 3)
    (hG : ∀ β ∈ E, β ∉ (MulAut.conj : ↥(adjointGroup Tag.D4 K) →*
      MulAut ↥(adjointGroup Tag.D4 K)).range → D4ElemType β fun ε σ => ε ≠ 0 ∧ σ = 1)
    {α : MulAut ↥(adjointGroup Tag.D4 K)} (hαE : α ∈ E)
    (hαout : α ∉ (MulAut.conj : ↥(adjointGroup Tag.D4 K) →* MulAut ↥(adjointGroup Tag.D4 K)).range) :
    (E ⊓ (MulAut.conj : ↥(adjointGroup Tag.D4 K) →* MulAut ↥(adjointGroup Tag.D4 K)).range).relIndex
        E = 3 ∧
      IsElemAbelian 3 (E.comap (MulAut.conj : ↥(adjointGroup Tag.D4 K) →*
        MulAut ↥(adjointGroup Tag.D4 K))) ∧
      Nat.card (E.comap (MulAut.conj : ↥(adjointGroup Tag.D4 K) →*
        MulAut ↥(adjointGroup Tag.D4 K))) = 3 ^ 2 ∧
      E.comap (MulAut.conj : ↥(adjointGroup Tag.D4 K) →* MulAut ↥(adjointGroup Tag.D4 K)) ≤
        fixedSubgroup α := by
  classical
  set E₁ := E ⊓ (MulAut.conj : ↥(adjointGroup Tag.D4 K) →*
    MulAut ↥(adjointGroup Tag.D4 K)).range with hE₁
  set P := E.comap (MulAut.conj : ↥(adjointGroup Tag.D4 K) →*
    MulAut ↥(adjointGroup Tag.D4 K)) with hP
  have hα3 : α ^ 3 = 1 := hE.2 α hαE
  obtain ⟨gα, aα, σα, εα, hεα, -, ⟨hεα0, hσα⟩, hαeq⟩ := hG α hαE hαout
  subst hσα
  have nα : HasNF α εα 1 := ⟨gα, aα, hαeq⟩
  have hdec : ∀ u ∈ E, u ∈ E₁ ∨ u * (α * α) ∈ E₁ ∨ u * α ∈ E₁ := by
    intro u hu
    by_cases hin : u ∈ (MulAut.conj : ↥(adjointGroup Tag.D4 K) →*
        MulAut ↥(adjointGroup Tag.D4 K)).range
    · exact Or.inl ⟨hu, hin⟩
    obtain ⟨g, a, σ, ε, hε, -, ⟨hε0, hσ⟩, hueq⟩ := hG u hu hin
    subst hσ
    have nu : HasNF u ε 1 := ⟨g, a, hueq⟩
    by_cases hεε : ε = εα
    · right; left
      have hw : u * (α * α) ∈ E := mul_mem hu (mul_mem hαE hαE)
      have h' := (nu.mul (nα.mul nα)).mod_three
      rw [show (ε + (εα + εα)) % 3 = 0 by omega, mul_one, mul_one] at h'
      exact ⟨hw, mem_inner_of_hasNF_zero_one h' (hE.2 _ hw)⟩
    · right; right
      have hw : u * α ∈ E := mul_mem hu hαE
      have h' := (nu.mul nα).mod_three
      rw [show (ε + εα) % 3 = 0 by omega, mul_one] at h'
      exact ⟨hw, mem_inner_of_hasNF_zero_one h' (hE.2 _ hw)⟩
  have hE₁E : E₁ ≤ E := inf_le_left
  have hsurj : Function.Surjective (fun x : ↥E₁ × Fin 3 =>
      (⟨(x.1 : MulAut ↥(adjointGroup Tag.D4 K)) * α ^ (x.2 : ℕ),
        mul_mem (hE₁E x.1.2) (pow_mem hαE _)⟩ : ↥E)) := by
    rintro ⟨u, hu⟩
    rcases hdec u hu with h | h | h
    · exact ⟨(⟨u, h⟩, 0), Subtype.ext (by simp)⟩
    · refine ⟨(⟨u * (α * α), h⟩, 1), Subtype.ext ?_⟩
      show u * (α * α) * α ^ ((1 : Fin 3) : ℕ) = u
      rw [show ((1 : Fin 3) : ℕ) = 1 from rfl, pow_one, mul_assoc, ← pow_three', hα3, mul_one]
    · refine ⟨(⟨u * α, h⟩, 2), Subtype.ext ?_⟩
      show u * α * α ^ ((2 : Fin 3) : ℕ) = u
      rw [show ((2 : Fin 3) : ℕ) = 2 from rfl, mul_assoc, ← pow_succ', hα3, mul_one]
  have hle27 : 3 ^ 3 ≤ Nat.card E₁ * 3 := by
    have h := Nat.card_le_card_of_surjective _ hsurj
    rwa [Nat.card_prod, Nat.card_eq_fintype_card (α := Fin 3), Fintype.card_fin, hc] at h
  have hE₁ne : E₁ ≠ E := fun h => hαout (h ▸ hαE : α ∈ E₁).2
  have hdvd : Nat.card E₁ ∣ 3 ^ 3 := hc ▸ Subgroup.card_dvd_of_le hE₁E
  have hlt : Nat.card E₁ < 3 ^ 3 := by
    have hle := Subgroup.card_le_of_le hE₁E
    rw [hc] at hle
    rcases hle.lt_or_eq with h | h
    · exact h
    · exact absurd (Subgroup.eq_of_le_of_card_ge hE₁E (by rw [h, hc])) hE₁ne
  have h9 : Nat.card E₁ = 3 ^ 2 := by
    obtain ⟨k, hk, hk'⟩ := (Nat.dvd_prime_pow Nat.prime_three).1 hdvd
    rw [hk'] at hle27 hlt ⊢
    interval_cases k <;> simp_all
  have hrel : E₁.relIndex E = 3 := by
    have h := Subgroup.relIndex_mul_card (H := E₁) (K := E)
    rw [inf_eq_left.2 hE₁E, h9, hc] at h
    omega
  have hPmap : P.map (MulAut.conj : ↥(adjointGroup Tag.D4 K) →* MulAut ↥(adjointGroup Tag.D4 K)) =
      E₁ := by
    rw [hP, Subgroup.map_comap_eq, inf_comm]
  have hPc : Nat.card P = 3 ^ 2 := by
    rw [← h9, ← hPmap, Subgroup.card_map_of_injective conj_injective_D4]
  have hP3 : ∀ k ∈ P, k ^ 3 = 1 := fun k hk =>
    conj_injective_D4 (by rw [map_pow, hE.2 _ hk, map_one])
  refine ⟨hrel, ⟨⟨⟨fun a b => ?_⟩⟩, hP3⟩, hPc, fun k hk => ?_⟩
  · apply Subtype.ext
    apply conj_injective_D4
    have h := CFSG.RankThree.PartTwo.Sec4.E27.comm_of_isElemAbelian hE a.2 b.2
    simpa only [Subgroup.coe_mul, map_mul] using h
  · exact apply_eq_of_comm_conj (CFSG.RankThree.PartTwo.Sec4.E27.comm_of_isElemAbelian hE hαE hk)

theorem fixedSubgroup_d4Graph_one_ne_top :
    fixedSubgroup (CFSG.HardMathSupport.Lang.D4Three.d4Graph K 1) ≠ ⊤ := by
  intro h
  have h0 : adjX Tag.D4 K ⟨0, by decide⟩ 1 ∈
      fixedSubgroup (CFSG.HardMathSupport.Lang.D4Three.d4Graph K 1) := h ▸ Subgroup.mem_top _
  have h1 : CFSG.HardMathSupport.Lang.D4Three.d4Graph K 1 (adjX Tag.D4 K ⟨0, by decide⟩ 1) =
      adjX Tag.D4 K ⟨0, by decide⟩ 1 := h0
  have r0 : CFSG.HardMathSupport.Lang.D4Three.d4Rho (⟨0, by decide⟩ : Fin Tag.D4.rank) =
      ⟨1, by decide⟩ := by decide
  rw [CFSG.HardMathSupport.Lang.D4Three.d4Graph_adjX, pow_one, r0] at h1
  have h2 := congrArg (fun g : adjointGroup Tag.D4 K =>
    rootCoord (FieldGraphFieldPointwise.single_pos
      (⟨0, by decide⟩ : Fin Tag.D4.rank)) (g : ModGL Tag.D4 K)) h1
  simp only [adjX] at h2
  rw [FieldGraphFieldPointwise.rootCoord_single_xUnit,
    FieldGraphFieldPointwise.rootCoord_single_xUnit] at h2
  simp at h2

theorem seitzHyperGamma_eq_top_of_graph_pair {E : Subgroup (MulAut ↥(adjointGroup Tag.D4 K))}
    (hE : IsElemAbelian 3 E) (hc : Nat.card E = 3 ^ 3)
    (hG : ∀ β ∈ E, β ∉ (MulAut.conj : ↥(adjointGroup Tag.D4 K) →*
      MulAut ↥(adjointGroup Tag.D4 K)).range → D4ElemType β fun ε σ => ε ≠ 0 ∧ σ = 1)
    {α : MulAut ↥(adjointGroup Tag.D4 K)} (hαE : α ∈ E)
    (hαout : α ∉ (MulAut.conj : ↥(adjointGroup Tag.D4 K) →* MulAut ↥(adjointGroup Tag.D4 K)).range)
    (hfix : fixedSubgroup α ≤ seitzHyperGamma 3 E) (hpair : SylowPairGenAt α) :
    seitzHyperGamma 3 E = ⊤ := by
  obtain ⟨hrel, hPel, -, hPα⟩ := graph_cube_inner_part hE hc hG hαE hαout
  set P := E.comap (MulAut.conj : ↥(adjointGroup Tag.D4 K) →*
    MulAut ↥(adjointGroup Tag.D4 K)) with hP
  have hPp : IsPGroup 3 P := fun k => ⟨1, by rw [pow_one]; exact Subtype.ext (hPel.2 k k.2)⟩
  have hC : Subgroup.centralizer (P : Set ↥(adjointGroup Tag.D4 K)) ≤ seitzHyperGamma 3 E := by
    refine le_trans ?_
      (CFSG.RankThree.PartTwo.Sec4.Res6L364.fixedPoints_le_seitzHyperGamma inf_le_left hrel)
    intro u hu
    rw [mem_fixedPoints]
    rintro φ ⟨hφE, k, rfl⟩
    have hk : k ∈ P := hφE
    rw [MulAut.conj_apply, Subgroup.mem_centralizer_iff.1 hu k hk, mul_inv_cancel_right]
  rw [eq_top_iff, ← hpair P hPp hPα, Subgroup.closure_le]
  rintro u (hu | hu)
  · exact hC hu
  · exact hfix hu

theorem fixed_le_of_fixedPlanesAt {E : Subgroup (MulAut ↥(adjointGroup Tag.D4 K))}
    (hE : IsElemAbelian 3 E) (hc : Nat.card E = 3 ^ 3)
    (hG : ∀ β ∈ E, β ∉ (MulAut.conj : ↥(adjointGroup Tag.D4 K) →*
      MulAut ↥(adjointGroup Tag.D4 K)).range → D4ElemType β fun ε σ => ε ≠ 0 ∧ σ = 1)
    {α : MulAut ↥(adjointGroup Tag.D4 K)} (hαE : α ∈ E)
    (hαout : α ∉ (MulAut.conj : ↥(adjointGroup Tag.D4 K) →* MulAut ↥(adjointGroup Tag.D4 K)).range)
    (hα : FixedPlanesAt α) : fixedSubgroup α ≤ seitzHyperGamma 3 E := by
  obtain ⟨-, hPel, hP9, hPα⟩ := graph_cube_inner_part hE hc hG hαE hαout
  have hα3 : α ^ 3 = 1 := hE.2 α hαE
  have hα1 : α ≠ 1 := fun h => hαout ⟨1, by rw [h, map_one]⟩
  refine (hα _ hPel hP9 hPα).trans ((Subgroup.closure_le _).2 ?_)
  rintro u ⟨huα, e, heP, he1, heu⟩
  have hconjE : MulAut.conj e ∈ E := heP
  have hnot : MulAut.conj e ∉ Subgroup.zpowers α :=
    CFSG.RankThree.PartTwo.Sec4.E27.conj_not_mem_zpowers conj_injective_D4 hα3
      (fun g h => hαout ⟨g, h.symm⟩) he1
  exact CFSG.RankThree.PartTwo.Sec4.E27.mem_seitzHyperGamma_of_fixed hE (hc.trans (by norm_num))
    hαE hconjE hα1 hnot huα (by rw [MulAut.conj_apply, heu, mul_inv_cancel_right])

theorem fixed_le_of_isG2Type (hS2 : CFSG.AGLEmbeddingD2.KFactSeitzRankTwo) (hK3 : ringChar K ≠ 3)
    (hK5 : 5 ≤ Nat.card K) {E : Subgroup (MulAut ↥(adjointGroup Tag.D4 K))}
    (hE : IsElemAbelian 3 E) (hc : Nat.card E = 3 ^ 3) {α : MulAut ↥(adjointGroup Tag.D4 K)}
    (hαE : α ∈ E) (hα : Parrott.D4Graph.IsG2Type α) : fixedSubgroup α ≤ seitzHyperGamma 3 E := by
  classical
  obtain ⟨ψ, h⟩ := hα
  have hF : fixedSubgroup (ψ * α * ψ⁻¹) =
      fixedSubgroup (CFSG.HardMathSupport.Lang.D4Three.d4Graph K 1) := by
    rcases h with h | h
    · rw [h]
    · rw [h, Parrott.D4Graph.fixedSubgroup_d4Graph_two]
  have : Fintype K := Fintype.ofFinite K
  obtain ⟨n, hℓ, hn⟩ := FiniteField.card K (ringChar K)
  set q : TauCeti.PrimePower := ⟨ringChar K, n, hℓ, n.pos⟩ with hq
  have hK : Nat.card K = q.card := by
    rw [TauCeti.PrimePower.card_def, Nat.card_eq_fintype_card]
    exact hn
  have hv : (TauCeti.LieTypeIndex.G2 q).Valid := by
    simp only [TauCeti.LieTypeIndex.valid_iff, TauCeti.LieTypeIndex.inStandardRange_iff,
      TauCeti.LieTypeIndex.isDuplicateRepresentative_iff]
    refine ⟨?_, not_false⟩
    rw [← hK]
    omega
  obtain ⟨φ⟩ := CFSG.TauCetiBridge.Even.chevalleyBridgesAll.g2 q hv K hK
  have hZ : Subgroup.center ↥(adjointGroup Tag.G2 K) = ⊥ := center_adjointGroup_eq_bot
  have hK3' : 3 ≤ Nat.card K := by omega
  let e₁ : ↥(fixedSubgroup (CFSG.HardMathSupport.Lang.D4Three.d4Graph K 1)) ≃*
      ↥(adjointGroup Tag.G2 K) :=
    CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.fixSubgroupEquivG2 K hK3'
  let e₂ : ↥(adjointGroup Tag.G2 K) ≃* (TauCeti.CFSGIndex.lie ⟨.G2 q, hv⟩).Group :=
    ((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot).symm.trans φ
  have hpd : 3 ≠ (⟨.G2 q, hv⟩ : TauCeti.ValidLieTypeIndex).1.characteristic := by
    simp only [TauCeti.LieTypeIndex.characteristic_G2]
    exact fun h => hK3 h.symm
  have hexc : ¬ CFSG.AGLEmbeddingD2.IsD2SeitzException 3
      (⟨.G2 q, hv⟩ : TauCeti.ValidLieTypeIndex).1 := by
    simp [CFSG.AGLEmbeddingD2.IsD2SeitzException]
  exact fixed_le_of_conj_cat hS2 hE hc fixedSubgroup_d4Graph_one_ne_top ⟨.G2 q, hv⟩ hpd hexc
    (e₁.trans e₂) hF hαE

end GraphCube

section A2Split

set_option linter.unusedSectionVars false


open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.PartOne.CTP
  CFSG.HardMathSupport.Lang.D4Three CFSG.LieType.Steinberg.Adjoint
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.LieType.SeitzGeneration.ExcWideThree CFSG.LieType.SeitzGeneration.ExcWideThree.Parrott.D4Graph

variable {K : Type} [Field K] [Finite K]

theorem sylowPairGenAt_gammaP_HSL (hq : Nat.card K % 3 = 1) (hK4 : 4 ≤ Nat.card K) {ω : Kˣ}
    (hω : orderOf ω = 3) : SylowPairGenAt (gammaP K (HSL ω)) := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Finite (ModGL Tag.D4 K) := finite_modGL
  have : Finite ↥(adjointGroup Tag.D4 K) := Subtype.finite
  have hω3 : ω ^ 3 = 1 := hω ▸ pow_orderOf_eq_one ω
  obtain ⟨ζ, hζ⟩ := exists_orderOf_eq_three_pow (K := K)
  obtain ⟨l, hl⟩ := exists_pow_four_ne_one hq hK4
  set μ := Subgroup.zpowers ζ with hμ
  set e := (Nat.card K - 1).factorization 3 with he
  have hμsq : ∀ u ∈ μ, ∃ b : Kˣ, u = b ^ 2 := mu_sq (Odd.pow (by decide : Odd 3)) hζ
  have hcardμ : Nat.card μ = 3 ^ e := by rw [hμ, Nat.card_zpowers, hζ]
  have hQge : 3 * Nat.card μ ^ 2 ≤ Nat.card (Q0 (K := K) hω3 μ) := by
    rw [card_Q0 hω3 hω μ, mul_comm 3]
    exact Nat.mul_le_mul_right 3 (card_T3fix_ge μ hμsq)
  have hQp : IsPGroup 3 (Q0 (K := K) hω3 μ) := by
    have hdvdT : Nat.card (T3fix (ω := ω) (K := K) μ) ∣ 3 ^ (4 * e) := by
      have h := Subgroup.card_dvd_of_le (inf_le_left : T3fix (ω := ω) (K := K) μ ≤ torusSub μ)
      rwa [card_torusSub μ hμsq, hcardμ, ← pow_mul, mul_comm e 4] at h
    refine IsPGroup.of_card_dvd_pow (n := 4 * e + 1) ?_
    rw [card_Q0 hω3 hω μ, pow_succ]
    exact Nat.mul_dvd_mul_right hdvdT 3
  refine sylowPairGenAt_of_sylow_central (Q0_le_fixed hω3 μ) hQp
    (fun R hR hRC => (card_le_of_isPGroup_fixed_gammaP hq hK4 hω3 hω hζ hR
      (fun y hy => hRC hy)).trans hQge) (fun y hy => ?_)
    (closure_fixedSubgroup_gammaP_HSL_torus hω3 hl)
  have h := Q0_le_centralizer hω3 μ l hy
  rw [Subgroup.mem_centralizer_singleton_iff] at h
  exact h

theorem sylowPairGenAt_gammaP_split (hq : Nat.card K % 3 = 1) (hK4 : 4 ≤ Nat.card K)
    {B : SL2 K} (hB3 : B ^ 3 = 1) (hB1 : B ≠ 1) : SylowPairGenAt (gammaP K B) := by
  have h3 : 3 ∣ Nat.card K - 1 := by have := Nat.card_pos (α := K); omega
  obtain ⟨P, t, hP⟩ := CFSG.RankThree.PartTwo.Sec11.KS11Lie4Proof.exists_conj_HSL_of_three h3 B
    ⟨1, by simpa using hB3⟩
  have ht3 : t ^ 3 = 1 := by
    have h : HSL t ^ 3 = 1 := by rw [← hP, conj_pow, hB3]; group
    apply CFSG.RankThree.PartTwo.Sec11.KS11Lie4Proof.HSLHom_injective
    rw [map_pow, map_one]
    exact h
  have ht1 : t ≠ 1 := by
    intro h1
    apply hB1
    have h : HSL t = 1 := by
      rw [h1]
      ext i j
      fin_cases i <;> fin_cases j <;> simp [HSL]
    have := congrArg (fun A => P⁻¹ * A * P) (hP.trans h)
    simpa [mul_assoc] using this
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have ht : orderOf t = 3 := orderOf_eq_prime ht3 ht1
  refine sylowPairGenAt_of_conj_eq (MulAut.conj (sl2At K ⟨2, by decide⟩ P))
    (sylowPairGenAt_gammaP_HSL hq hK4 ht) (Or.inl ?_)
  rw [conj_gammaP, hP]

end A2Split

section G2Split

set_option linter.unusedSectionVars false


open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.PartOne.CTP
  CFSG.HardMathSupport.Lang.D4Three CFSG.LieType.Steinberg.Adjoint
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.LieType.SeitzGeneration.ExcWideThree CFSG.LieType.SeitzGeneration.ExcWideThree.Parrott.D4Graph

variable {K : Type} [Field K] [Finite K]

theorem one_pow_three_units : (1 : Kˣ) ^ 3 = 1 := one_pow 3

theorem gammaP_HSL_one : gammaP K (HSL (1 : Kˣ)) = d4Graph K 1 := by
  have h1 : HSL (1 : Kˣ) = 1 := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [HSL]
  rw [gammaP, h1, map_one, map_one, one_mul]

theorem yP_one_pow_not_diag {ω' : Kˣ} (hω' : orderOf ω' = 3) {k : ℕ} (hk : k = 1 ∨ k = 2)
    {a : Fin Tag.D4.rank → Kˣ}
    (ha : ((yP (one_pow_three_units (K := K)) ^ k : ↥(adjointGroup Tag.D4 K)) :
      ModGL Tag.D4 K) = rootDiagUnit Tag.D4 a) : False := by
  set h := torusElement Tag.D4 K ⟨2, by decide⟩ ω'
  have hh : (h : ModGL Tag.D4 K) = rootDiagUnit Tag.D4 (fun j => ω' ^ vH j) := by
    rw [coe_torusElement]
    rfl
  have hc := yP_pow_conj_diag (one_pow_three_units (K := K)) k hh
  have hcomm : yP (one_pow_three_units (K := K)) ^ k * h =
      h * yP (one_pow_three_units (K := K)) ^ k := commute_of_diag ha hh
  have hfix : yP (one_pow_three_units (K := K)) ^ k * h *
      (yP (one_pow_three_units (K := K)) ^ k)⁻¹ = h := by rw [hcomm, mul_inv_cancel_right]
  rw [hfix, hh, tupAct_zpow] at hc
  have h0 := congrFun (rootDiagUnit_injective_D4 hc) ⟨0, by decide⟩
  have hmod := (zpow_eq_zpow_iff_modEq).1 h0
  rw [hω'] at hmod
  have hdiv := Int.ModEq.dvd hmod
  rcases hk with rfl | rfl
  · simp only [Nat.mul_one] at hdiv
    exact vS_facts.2.2.2.1 (by omega)
  · simp only [show 4 * 2 = 8 from rfl] at hdiv
    exact vS_facts.2.2.2.2 (by omega)

theorem torusSub_inf_zpowers_yP_one {ω' : Kˣ} (hω' : orderOf ω' = 3) (μ : Subgroup Kˣ) :
    torusSub (K := K) μ ⊓ Subgroup.zpowers (yP (one_pow_three_units (K := K))) = ⊥ := by
  rw [eq_bot_iff]
  rintro x ⟨⟨a, -, hxa⟩, hx⟩
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hx
  rw [Subgroup.mem_bot, yP_zpow_eq]
  rw [yP_zpow_eq] at hxa
  have hlt : (k % 3).toNat < 3 := by
    have := Int.emod_lt_of_pos k (by norm_num : (0 : ℤ) < 3)
    omega
  rcases (by omega : (k % 3).toNat = 0 ∨ (k % 3).toNat = 1 ∨ (k % 3).toNat = 2) with h | h | h
  · rw [h, pow_zero]
  · exact (yP_one_pow_not_diag hω' (Or.inl h) hxa).elim
  · exact (yP_one_pow_not_diag hω' (Or.inr h) hxa).elim

theorem orderOf_yP_one {ω' : Kˣ} (hω' : orderOf ω' = 3) :
    orderOf (yP (one_pow_three_units (K := K))) = 3 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  refine orderOf_eq_prime (yP_pow_three one_pow_three_units) fun h1 => ?_
  have h1' : yP (one_pow_three_units (K := K)) ^ 1 = 1 := by rw [pow_one, h1]
  exact yP_one_pow_not_diag hω' (Or.inl rfl) (a := 1) (by rw [h1', Subgroup.coe_one,
    rootDiagUnit_one])

theorem card_S1_one {ω' : Kˣ} (hω' : orderOf ω' = 3) (μ : Subgroup Kˣ) :
    Nat.card (S1 (K := K) one_pow_three_units μ) = Nat.card (torusSub (K := K) μ) * 3 := by
  rw [S1, card_sup_of_le_normalizer ((Subgroup.zpowers_le).2
    (yP_mem_normalizer one_pow_three_units μ)) (torusSub_inf_zpowers_yP_one hω' μ),
    Nat.card_zpowers, orderOf_yP_one hω']

theorem card_Q0_one {ω' : Kˣ} (hω' : orderOf ω' = 3) (μ : Subgroup Kˣ) :
    Nat.card (Q0 (K := K) one_pow_three_units μ) =
      Nat.card (T3fix (ω := 1) (K := K) μ) * 3 := by
  rw [Q0, card_sup_of_le_normalizer ((Subgroup.zpowers_le).2
    (yP_mem_normalizer_T3fix one_pow_three_units μ)), Nat.card_zpowers, orderOf_yP_one hω']
  rw [eq_bot_iff]
  exact le_trans (inf_le_inf_right _ inf_le_left)
    (le_of_eq (torusSub_inf_zpowers_yP_one hω' μ))

open CFSG.HardMathSupport.Solomon.Coordinator
  CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple in
theorem gammaP_HSL_one_not_inner (hK3 : 3 ≤ Nat.card K) :
    gammaP K (HSL (1 : Kˣ)) ∉ (MulAut.conj : ↥(adjointGroup Tag.D4 K) →*
      MulAut ↥(adjointGroup Tag.D4 K)).range := by
  rw [gammaP_HSL_one]
  rintro ⟨g, hγ⟩
  have hfix : d4Graph K 1 g = g := by
    rw [← hγ, MulAut.conj_apply, mul_inv_cancel_right]
  have hcen : (⟨g, mem_fixSubgroup.2 hfix⟩ : ↥(fixSubgroup (d4Graph K 1))) ∈
      Subgroup.center ↥(fixSubgroup (d4Graph K 1)) := by
    rw [Subgroup.mem_center_iff]
    intro y
    obtain ⟨yv, hyv⟩ := y
    have hy : d4Graph K 1 yv = yv := mem_fixSubgroup.1 hyv
    rw [← hγ, MulAut.conj_apply] at hy
    refine Subtype.ext ?_
    simp only [Subgroup.coe_mul]
    calc yv * g = g * yv * g⁻¹ * g := by rw [hy]
      _ = g * yv := by group
  set Φ := fixSubgroupEquivG2 K hK3
  have hΦ : Φ ⟨g, mem_fixSubgroup.2 hfix⟩ ∈ Subgroup.center ↥(adjointGroup Tag.G2 K) := by
    rw [Subgroup.mem_center_iff]
    intro z
    obtain ⟨w, rfl⟩ := Φ.surjective z
    rw [← map_mul, ← map_mul, (Subgroup.mem_center_iff.1 hcen) w]
  rw [center_adjointGroup_eq_bot, Subgroup.mem_bot] at hΦ
  have hg1 : g = 1 := congrArg Subtype.val (Φ.injective (hΦ.trans (map_one Φ).symm))
  rw [hg1, map_one] at hγ
  apply fixedSubgroup_d4Graph_one_ne_top (K := K)
  rw [← hγ]
  exact (Subgroup.eq_top_iff' _).2 fun x => rfl

theorem card_le_of_isPGroup_fixed_gamma (hq : Nat.card K % 3 = 1) (hK4 : 4 ≤ Nat.card K)
    {ω' : Kˣ} (hω' : orderOf ω' = 3) {ζ : Kˣ}
    (hζ : orderOf ζ = 3 ^ (Nat.card K - 1).factorization 3) {R : Subgroup ↥(adjointGroup Tag.D4 K)}
    (hR : IsPGroup 3 R) (hRα : ∀ x ∈ R, gammaP K (HSL (1 : Kˣ)) x = x) :
    Nat.card R ≤ 3 * Nat.card (Subgroup.zpowers ζ) ^ 2 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set e := (Nat.card K - 1).factorization 3 with he
  set μ := Subgroup.zpowers ζ with hμ
  have hμsq : ∀ u ∈ μ, ∃ b : Kˣ, u = b ^ 2 := mu_sq (Odd.pow (by decide : Odd 3)) hζ
  have hcardμ : Nat.card μ = 3 ^ e := by rw [hμ, Nat.card_zpowers, hζ]
  have hcardT : Nat.card (torusSub (K := K) μ) = (3 ^ e) ^ 4 := by
    rw [card_torusSub μ hμsq, hcardμ]
  have hcardS : Nat.card (S1 (K := K) one_pow_three_units μ) = 3 ^ (4 * e + 1) := by
    rw [card_S1_one hω' μ, hcardT, ← pow_mul, pow_succ, mul_comm e 4]
  have hSsyl : Nat.card (S1 (K := K) one_pow_three_units μ) =
      3 ^ (Nat.card ↥(adjointGroup Tag.D4 K)).factorization 3 := by
    rw [hcardS]
    congr 1
    refine le_antisymm ?_ ?_
    · have hdvd : 3 ^ (4 * e + 1) ∣ Nat.card ↥(adjointGroup Tag.D4 K) := by
        rw [← hcardS]
        exact Subgroup.card_subgroup_dvd_card _
      exact (Nat.prime_three.pow_dvd_iff_le_factorization Nat.card_pos.ne').1 hdvd
    · exact factorization_card_D4_le hq
  have hTS : (torusSub (K := K) μ).relIndex (S1 one_pow_three_units μ) = 3 := by
    have h := Subgroup.relIndex_mul_card (H := torusSub (K := K) μ)
      (K := S1 one_pow_three_units μ)
    rw [inf_eq_left.2 (show torusSub (K := K) μ ≤ S1 one_pow_three_units μ from le_sup_left),
      card_S1_one hω' μ] at h
    have hT0 : Nat.card (torusSub (K := K) μ) ≠ 0 := Nat.card_pos.ne'
    exact Nat.eq_of_mul_eq_mul_right (Nat.pos_of_ne_zero hT0) (h.trans (mul_comm _ _))
  exact card_le_of_isPGroup_of_fixed conj_injective_adj
    (gammaP_pow_three (HSL_pow_three one_pow_three_units)) (gammaP_HSL_one_not_inner (by omega))
    hSsyl (fun x hx => gammaP_HSL_mem_S1 one_pow_three_units μ hx) hTS.le (by rw [hTS]; norm_num)
    (fun s hs j hj hj3 F hF hfix => card_fixed_le one_pow_three_units μ hs hj hj3 hF hfix) hR hRα

theorem sylowPairGenAt_d4Graph_split (hq : Nat.card K % 3 = 1) (hK4 : 4 ≤ Nat.card K) :
    SylowPairGenAt (d4Graph K 1) := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Finite (ModGL Tag.D4 K) := finite_modGL
  have : Finite ↥(adjointGroup Tag.D4 K) := Subtype.finite
  obtain ⟨ω', hω'⟩ : ∃ ω' : Kˣ, orderOf ω' = 3 := by
    refine exists_prime_orderOf_dvd_card' 3 ?_
    rw [card_units_K]
    have := Nat.card_pos (α := K)
    omega
  rw [← gammaP_HSL_one]
  obtain ⟨ζ, hζ⟩ := exists_orderOf_eq_three_pow (K := K)
  obtain ⟨l, hl⟩ := exists_pow_four_ne_one hq hK4
  set μ := Subgroup.zpowers ζ with hμ
  set e := (Nat.card K - 1).factorization 3 with he
  have hμsq : ∀ u ∈ μ, ∃ b : Kˣ, u = b ^ 2 := mu_sq (Odd.pow (by decide : Odd 3)) hζ
  have hcardμ : Nat.card μ = 3 ^ e := by rw [hμ, Nat.card_zpowers, hζ]
  have hQge : 3 * Nat.card μ ^ 2 ≤ Nat.card (Q0 (K := K) one_pow_three_units μ) := by
    rw [card_Q0_one hω' μ, mul_comm 3]
    exact Nat.mul_le_mul_right 3 (card_T3fix_ge μ hμsq)
  have hQp : IsPGroup 3 (Q0 (K := K) one_pow_three_units μ) := by
    have hdvdT : Nat.card (T3fix (ω := 1) (K := K) μ) ∣ 3 ^ (4 * e) := by
      have h := Subgroup.card_dvd_of_le (inf_le_left : T3fix (ω := 1) (K := K) μ ≤ torusSub μ)
      rwa [card_torusSub μ hμsq, hcardμ, ← pow_mul, mul_comm e 4] at h
    refine IsPGroup.of_card_dvd_pow (n := 4 * e + 1) ?_
    rw [card_Q0_one hω' μ, pow_succ]
    exact Nat.mul_dvd_mul_right hdvdT 3
  refine sylowPairGenAt_of_sylow_central (Q0_le_fixed one_pow_three_units μ) hQp
    (fun R hR hRC => (card_le_of_isPGroup_fixed_gamma hq hK4 hω' hζ hR
      (fun y hy => hRC hy)).trans hQge) (fun y hy => ?_)
    (closure_fixedSubgroup_gammaP_HSL_torus one_pow_three_units hl)
  have h := Q0_le_centralizer one_pow_three_units μ l hy
  rw [Subgroup.mem_centralizer_singleton_iff] at h
  exact h

end G2Split

section A2Nonsplit

set_option linter.unusedSectionVars false


open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.PartOne.CTP
  CFSG.HardMathSupport.Lang.D4Three CFSG.LieType.Steinberg.Adjoint
  CFSG.LocalAnalysis.ComponentInitial CFSG.LieType.SeitzGeneration.ExcWideThree.Parrott.D4Graph
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.HardMathSupport.Seitz.G2Anisotropic.Coordinator CFSG.HardMathSupport.Seitz.Proving
  CFSG.LieType.SeitzGeneration.ExcWideThree.Parrott.D4Graph.A2Nonsplit

theorem exists_sylow_frameD_of_ext {K : Type} [Field K] [Finite K] (hq : Nat.card K % 3 = 2)
    (hK4 : 4 ≤ Nat.card K) {K₂ : Type} [Field K₂] [Finite K₂] [Algebra K K₂]
    (hcard : Nat.card K₂ = Nat.card K ^ 2) (σ : K₂ →+* K₂) (hσ : ∀ x, σ x = x ^ Nat.card K) :
    ∃ P : Subgroup ↥(adjointGroup Tag.D4 K), P ≤ fixedSubgroup (gammaP K (orderThreeSL K)) ∧
      IsPGroup 3 P ∧ (∀ y ∈ P, y * frameD K (orderThreeSL K) = frameD K (orderThreeSL K) * y) ∧
      ∀ R : Subgroup ↥(adjointGroup Tag.D4 K), IsPGroup 3 R →
        R ≤ fixedSubgroup (gammaP K (orderThreeSL K)) → Nat.card R ≤ Nat.card P := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨Q, ω, c₀, hQ, hω, hσω, hQc, hc₀⟩ := exists_twist_data hq hcard hσ
  have hω3 : ω ^ 3 = 1 := hω ▸ pow_orderOf_eq_one ω
  have hK₂ : Nat.card K₂ % 3 = 1 := by rw [hcard]; exact sq_mod_three hq
  have hK₂4 : 4 ≤ Nat.card K₂ := by rw [hcard]; nlinarith
  obtain ⟨ζ, hζ⟩ := exists_orderOf_eq_three_pow (K := K₂)
  set e := (Nat.card K₂ - 1).factorization 3 with he
  set μ := Subgroup.zpowers ζ with hμ
  have hμsq : ∀ u ∈ μ, ∃ b : K₂ˣ, u = b ^ 2 := mu_sq (Odd.pow (by decide : Odd 3)) hζ
  have hcardμ : Nat.card μ = 3 ^ e := by rw [hμ, Nat.card_zpowers, hζ]
  have hζq : ζ ^ (Nat.card K + 1) = 1 := by
    rw [← orderOf_dvd_iff_pow_eq_one, hζ]
    have hdvd : 3 ^ e ∣ (Nat.card K - 1) * (Nat.card K + 1) := by
      have h1 : 3 ^ e ∣ Nat.card K₂ - 1 := Nat.ordProj_dvd _ _
      have h2 : Nat.card K₂ - 1 = (Nat.card K - 1) * (Nat.card K + 1) := by
        rw [hcard]
        obtain ⟨m, hm⟩ : ∃ m, Nat.card K = m + 1 := ⟨Nat.card K - 1, by
          have := Nat.card_pos (α := K); omega⟩
        rw [hm, Nat.add_sub_cancel]
        have : (m + 1) ^ 2 = m * (m + 1 + 1) + 1 := by ring
        omega
      rwa [h2] at h1
    have hcop : Nat.Coprime (3 ^ e) (Nat.card K - 1) := by
      apply Nat.Coprime.pow_left
      rw [Nat.Prime.coprime_iff_not_dvd Nat.prime_three]
      omega
    exact hcop.dvd_of_dvd_mul_left hdvd
  have hμq : ∀ u ∈ μ, u ^ (Nat.card K + 1) = 1 := by
    intro u hu
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hu
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hζq, one_zpow]
  have hμσ : ∀ u ∈ μ, Units.map σ.toMonoidHom u = u⁻¹ := by
    intro u hu
    rw [units_frob hσ]
    exact eq_inv_of_mul_eq_one_left (by rw [← pow_succ]; exact hμq u hu)
  have hζe : ζ ^ 3 ^ e = 1 := by rw [← hζ]; exact pow_orderOf_eq_one ζ
  have hμ3 : ∀ u ∈ μ, u ^ 3 ^ e = 1 := by
    intro u hu
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hu
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hζe, one_zpow]
  have hT3ι : T3fix (ω := ω) (K := K₂) μ ≤ (ιTw K Q).range := by
    rintro t ⟨⟨a, ha, hta⟩, -⟩
    have hσt : bcAd σ t = t⁻¹ := by
      apply Subtype.ext
      rw [coe_bcAd_of_eq_rootDiagUnit σ hta, Subgroup.coe_inv, hta, rootDiagUnit_inv]
      congr 1
      funext j
      rw [Pi.inv_apply, hμσ _ (ha j)]
    have htinv : ((t⁻¹ : ↥(adjointGroup Tag.D4 K₂)) : ModGL Tag.D4 K₂) =
        rootDiagUnit Tag.D4 a⁻¹ := by
      rw [Subgroup.coe_inv, hta, rootDiagUnit_inv]
    refine mem_range_ιTw_of_fixed σ hσ hQc (k := e) ?_ ?_
    · rw [hσt, gTw_nSL_conj_diag c₀ htinv, inv_inv]
    · apply Subtype.ext
      rw [Subgroup.coe_pow, hta, ← rootDiagUnit_pow_D4, Subgroup.coe_one, ← rootDiagUnit_one]
      congr 1
      funext j
      rw [Pi.pow_apply, Pi.one_apply, hμ3 _ (ha j)]
  obtain ⟨r, a₁, a₂, hr, hcr⟩ := exists_cocyc_eq_mul_bcAd hcard Nat.card_pos σ hσ hc₀
  have hπ3 : (r * yP hω3) ^ 3 = 1 := mul_yP_pow_three hω3 hr
  have hπnd : r * yP hω3 ∉ T3fix (ω := ω) (K := K₂) μ := by
    rintro ⟨⟨b, -, hb⟩, -⟩
    exact mul_yP_not_diag hω3 hω hr hb
  have hπ1 : r * yP hω3 ≠ 1 := by
    intro h1
    apply hπnd
    rw [h1]
    exact Subgroup.one_mem _
  have hπord : orderOf (r * yP hω3) = 3 := orderOf_eq_prime hπ3 hπ1
  have hπι : r * yP hω3 ∈ (ιTw K Q).range :=
    mem_range_ιTw_of_fixed σ hσ hQc (fixed_mul_yP hω3 hσω hr hcr) (k := 1)
      (by rw [pow_one]; exact hπ3)
  set P' := T3fix (ω := ω) (K := K₂) μ ⊔ Subgroup.zpowers (r * yP hω3) with hP'
  have hcardP' : Nat.card P' = Nat.card (T3fix (ω := ω) (K := K₂) μ) * 3 := by
    rw [hP', card_sup_of_le_normalizer
      ((Subgroup.zpowers_le).2 (mul_yP_mem_normalizer_T3fix hω3 μ hr))
      (inf_zpowers_eq_bot_of_pow_three hπ3 hπnd), Nat.card_zpowers, hπord]
  have hP'ge : 3 * Nat.card μ ^ 2 ≤ Nat.card P' := by
    rw [hcardP', mul_comm 3]
    exact Nat.mul_le_mul_right 3 (card_T3fix_ge (ω := ω) μ hμsq)
  have hP'p : IsPGroup 3 P' := by
    have hdvdT : Nat.card (T3fix (ω := ω) (K := K₂) μ) ∣ 3 ^ (4 * e) := by
      have h := Subgroup.card_dvd_of_le
        (inf_le_left : T3fix (ω := ω) (K := K₂) μ ≤ torusSub μ)
      rwa [card_torusSub μ hμsq, hcardμ, ← pow_mul, mul_comm e 4] at h
    refine IsPGroup.of_card_dvd_pow (n := 4 * e + 1) ?_
    rw [hcardP', pow_succ]
    exact Nat.mul_dvd_mul_right hdvdT 3
  have hP'ι : P' ≤ (ιTw K Q).range := sup_le hT3ι ((Subgroup.zpowers_le).2 hπι)
  have hP'α : P' ≤ fixedSubgroup (gammaP K₂ (HSL ω)) :=
    sup_le inf_le_right ((Subgroup.zpowers_le).2 (gammaP_HSL_mul_yP hω3 hr))
  have hP'd : P' ≤ Subgroup.centralizer
      ({torusElement Tag.D4 K₂ ⟨0, by decide⟩ ω * torusElement Tag.D4 K₂ ⟨1, by decide⟩ ω⁻¹} :
        Set ↥(adjointGroup Tag.D4 K₂)) := by
    refine sup_le ?_ ((Subgroup.zpowers_le).2 ?_)
    · rintro y ⟨⟨a, -, hya⟩, -⟩
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact commute_of_diag hya (coe_dTorus ω)
    · rw [Subgroup.mem_centralizer_singleton_iff]
      exact mul_yP_commute_dTorus hω3 hr ω
  set P := P'.comap (ιTw K Q) with hP
  have hιinj : Function.Injective (ιTw K Q) := ιTw_injective Q
  have hcardP : Nat.card P = Nat.card P' := by
    rw [← Subgroup.card_map_of_injective hιinj, hP, Subgroup.map_comap_eq_self hP'ι]
  have hPp : IsPGroup 3 P := by
    obtain ⟨n, hn⟩ := IsPGroup.iff_card.1 hP'p
    exact IsPGroup.of_card (n := n) (by rw [hcardP, hn])
  have hPC : P ≤ fixedSubgroup (gammaP K (orderThreeSL K)) := by
    intro y hy
    show gammaP K (orderThreeSL K) y = y
    apply hιinj
    rw [ιTw_gammaP hQ y]
    exact hP'α hy
  have hPd : ∀ y ∈ P, Commute y (frameD K (orderThreeSL K)) := by
    intro y hy
    show y * frameD K (orderThreeSL K) = frameD K (orderThreeSL K) * y
    apply hιinj
    rw [map_mul, map_mul, ιTw_frameD hQ]
    exact Subgroup.mem_centralizer_singleton_iff.1 (hP'd hy)
  have hmax : ∀ R : Subgroup ↥(adjointGroup Tag.D4 K), IsPGroup 3 R →
      R ≤ fixedSubgroup (gammaP K (orderThreeSL K)) → Nat.card R ≤ Nat.card P := by
    intro R hR hRC
    have h := card_le_of_isPGroup_fixed_gammaP hK₂ hK₂4 hω3 hω hζ (hR.map (ιTw K Q)) ?_
    · rw [Subgroup.card_map_of_injective hιinj] at h
      rw [hcardP]
      exact h.trans hP'ge
    · rintro y ⟨z, hz, rfl⟩
      rw [← ιTw_gammaP hQ z, show gammaP K (orderThreeSL K) z = z from hRC hz]
  exact ⟨P, hPC, hPp, fun y hy => (hPd y hy).eq, hmax⟩

theorem sylowPairGenAt_orderThreeSL {K : Type} [Field K] [Finite K] (hq : Nat.card K % 3 = 2)
    (hK4 : 4 ≤ Nat.card K) : SylowPairGenAt (gammaP K (orderThreeSL K)) := by
  have : Finite (ModGL Tag.D4 K) := finite_modGL
  have : Finite ↥(adjointGroup Tag.D4 K) := Subtype.finite
  have hK3 : ringChar K ≠ 3 := by
    intro h3
    have := Fintype.ofFinite K
    obtain ⟨n, -, hn⟩ := FiniteField.card K (ringChar K)
    rw [Nat.card_eq_fintype_card, hn, h3] at hq
    have : (3 : ℕ) ^ (n : ℕ) % 3 = 0 := by
      rw [Nat.pow_mod]; simp [Nat.zero_pow n.pos]
    omega
  have := Fintype.ofFinite K
  obtain ⟨n, hp, -⟩ := FiniteField.card K (ringChar K)
  have : Fact (ringChar K).Prime := ⟨hp⟩
  obtain ⟨P, hPC, hPp, hPd, hmax⟩ := exists_sylow_frameD_of_ext hq hK4
    (FiniteField.natCard_extension K (ringChar K) 2)
    (FiniteField.Extension.frob K (ringChar K) 2).toRingEquiv.toRingHom
    (fun y => FiniteField.Extension.frob_apply K (ringChar K) 2)
  refine sylowPairGenAt_of_sylow_central hPC hPp hmax hPd ?_
  exact closure_fixedSubgroup_frameD (A2NonsplitGen.d4GraphA2FrameGen_of
      A2NonsplitGen.frameTopRootsMem_holds A2NonsplitGen.frameClosing_holds) hK3 hK4

theorem sylowPairGenAt_gammaP_nonsplit {K : Type} [Field K] [Finite K] (hq : Nat.card K % 3 = 2)
    (hK4 : 4 ≤ Nat.card K) {B : SL2 K} (hB3 : B ^ 3 = 1) (hB1 : B ≠ 1) :
    SylowPairGenAt (gammaP K B) := by
  have h3 : 3 ∣ Nat.card K + 1 := by omega
  obtain ⟨S, hS'⟩ := exists_conj_eq_orderThreeSL h3 hB3 hB1
  refine sylowPairGenAt_of_conj_eq (MulAut.conj (sl2At K ⟨2, by decide⟩ S))
    (sylowPairGenAt_orderThreeSL hq hK4) (Or.inl ?_)
  rw [conj_gammaP, hS']

end A2Nonsplit

section Assembly

set_option linter.unusedSectionVars false


open CFSG.LieType.Seitz CFSG.RankThree.PartOne.CTP CFSG.LieType.SeitzGeneration
  CFSG.LieType.SeitzGeneration.ExcWideThree CFSG.LieType.Chevalley CFSG.Blueprint.Chevalley
  CFSG.Open CFSG.LieType.SeitzGeneration.ExcWideThree.Parrott.D4Graph

@[expose] def D4GraphA2FixedPlanes : Prop :=
  ∀ (K : Type) [Field K] [Finite K], ringChar K ≠ 3 → 5 ≤ Nat.card K →
    ∀ B : SL2 K, B ^ 3 = 1 → B ≠ 1 → FixedPlanesAt (gammaP K B)

@[expose] def D4GraphG2SylowPair : Prop :=
  ∀ (K : Type) [Field K] [Finite K], ringChar K ≠ 3 → 5 ≤ Nat.card K →
    SylowPairGenAt (CFSG.HardMathSupport.Lang.D4Three.d4Graph K 1)

variable {K : Type} [Field K] [Finite K]

theorem isG2Type_or_isA2Type (hK3 : ringChar K ≠ 3) {α : MulAut ↥(adjointGroup Tag.D4 K)}
    (hα3 : α ^ 3 = 1) (hαT : D4ElemType α fun ε σ => ε ≠ 0 ∧ σ = 1) :
    IsG2Type α ∨ IsA2Type α := by
  classical
  have : Fintype K := Fintype.ofFinite K
  obtain ⟨n, hpr, -⟩ := FiniteField.card K (ringChar K)
  by_cases h2 : ringChar K = 2
  · exact isG2Type_or_isA2Type_of_charTwo K h2 α hα3 hαT
  · have h5 : 5 ≤ ringChar K := by
      have h2' := hpr.two_le
      have h4 : ringChar K ≠ 4 := fun h => by rw [h] at hpr; exact absurd hpr (by norm_num)
      omega
    exact ClassOdd.d4GraphClassOdd_of (ClassOdd.graphShintaniNF_of ClassOdd.threeD4FixedNF_holds)
        ClassOdd.g2ThreeClass_holds K h5 α hα3 hαT

theorem sylowPairGenAt_of_isA2Type (hK3 : ringChar K ≠ 3) (hK4 : 4 ≤ Nat.card K)
    {α : MulAut ↥(adjointGroup Tag.D4 K)} (hα : IsA2Type α) : SylowPairGenAt α := by
  obtain ⟨ψ, B, hB3, hB1, h⟩ := hα
  have hmod := card_mod_three_ne_zero hK3
  have hB : SylowPairGenAt (gammaP K B) := by
    rcases (by omega : Nat.card K % 3 = 1 ∨ Nat.card K % 3 = 2) with h1 | h1
    · exact sylowPairGenAt_gammaP_split h1 hK4 hB3 hB1
    · exact sylowPairGenAt_gammaP_nonsplit h1 hK4 hB3 hB1
  exact sylowPairGenAt_of_conj_eq ψ hB h

theorem sylowPairGenAt_of_isG2Type (hG : D4GraphG2SylowPair) (hK3 : ringChar K ≠ 3)
    (hK5 : 5 ≤ Nat.card K) {α : MulAut ↥(adjointGroup Tag.D4 K)} (hα : IsG2Type α) :
    SylowPairGenAt α := by
  obtain ⟨ψ, h | h⟩ := hα
  · exact sylowPairGenAt_of_conj_eq ψ (hG K hK3 hK5) (Or.inl h)
  · exact sylowPairGenAt_of_conj_eq ψ
      (sylowPairGenAt_congr fixedSubgroup_d4Graph_two.symm (hG K hK3 hK5)) (Or.inl h)

theorem fixedPlanesAt_of_isA2Type (hA : D4GraphA2FixedPlanes) (hK3 : ringChar K ≠ 3)
    (hK5 : 5 ≤ Nat.card K) {α : MulAut ↥(adjointGroup Tag.D4 K)} (hα : IsA2Type α) :
    FixedPlanesAt α := by
  obtain ⟨ψ, B, hB3, hB1, h⟩ := hα
  exact fixedPlanesAt_of_conj_eq ψ (hA K hK3 hK5 B hB3 hB1) h

theorem five_le_card (hK3 : ringChar K ≠ 3) (h2 : Nat.card K ≠ 2) (h4 : Nat.card K ≠ 4) :
    5 ≤ Nat.card K := by
  have h1 : 1 < Nat.card K := Finite.one_lt_card
  by_contra h
  have h3 : Nat.card K = 3 := by omega
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hchar : CharP K 3 :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic Nat.prime_three
      (k := 1) le_rfl (by rw [h3, pow_one])
  exact hK3 (ringChar.eq K 3)

theorem d4ThreeGraphCubes_of (hS2 : CFSG.AGLEmbeddingD2.KFactSeitzRankTwo)
    (hA : D4GraphA2FixedPlanes) (hG : D4GraphG2SylowPair) : D4ThreeGraphCubes := by
  intro K _ _ hK3 h2 h4 E hE hc hout hgr
  have hK5 := five_le_card hK3 h2 h4
  obtain ⟨α, hαE, hαout⟩ : ∃ α ∈ E, α ∉ (MulAut.conj : ↥(adjointGroup Tag.D4 K) →*
      MulAut ↥(adjointGroup Tag.D4 K)).range := by
    by_contra h
    push Not at h
    exact hout h
  have hα3 : α ^ 3 = 1 := hE.2 α hαE
  rcases isG2Type_or_isA2Type hK3 hα3 (hgr α hαE hαout) with hG2 | hA2
  · exact seitzHyperGamma_eq_top_of_graph_pair hE hc hgr hαE hαout
      (fixed_le_of_isG2Type hS2 hK3 hK5 hE hc hαE hG2) (sylowPairGenAt_of_isG2Type hG hK3 hK5 hG2)
  · exact seitzHyperGamma_eq_top_of_graph_pair hE hc hgr hαE hαout
      (fixed_le_of_fixedPlanesAt hE hc hgr hαE hαout (fixedPlanesAt_of_isA2Type hA hK3 hK5 hA2))
      (sylowPairGenAt_of_isA2Type hK3 (by omega) hA2)

@[expose] def D4GraphG2SylowPairNonsplit : Prop :=
  ∀ (K : Type) [Field K] [Finite K], Nat.card K % 3 = 2 → 5 ≤ Nat.card K →
    SylowPairGenAt (CFSG.HardMathSupport.Lang.D4Three.d4Graph K 1)

theorem d4GraphG2SylowPair_of_nonsplit (h : D4GraphG2SylowPairNonsplit) : D4GraphG2SylowPair := by
  intro K _ _ hK3 hK5
  have hmod := card_mod_three_ne_zero hK3
  rcases (by omega : Nat.card K % 3 = 1 ∨ Nat.card K % 3 = 2) with h1 | h1
  · exact sylowPairGenAt_d4Graph_split h1 (by omega)
  · exact h K h1 hK5

theorem d4ThreeGraphCubes_of_residuals (hS2 : CFSG.AGLEmbeddingD2.KFactSeitzRankTwo)
    (hA : D4GraphA2FixedPlanes) (hG : D4GraphG2SylowPairNonsplit) : D4ThreeGraphCubes :=
  d4ThreeGraphCubes_of hS2 hA (d4GraphG2SylowPair_of_nonsplit hG)

theorem seitzGoodOuterHighD4Three_of_residuals (hS2 : CFSG.AGLEmbeddingD2.KFactSeitzRankTwo)
    (hA : D4GraphA2FixedPlanes) (hG : D4GraphG2SylowPairNonsplit) :
    OuterHigh2.SeitzGoodOuterHighD4Three :=
  seitzGoodOuterHighD4Three_of_graphCubes hS2 (d4ThreeGraphCubes_of_residuals hS2 hA hG)

theorem d4EightGraphCubes_of_residuals (hS2 : CFSG.AGLEmbeddingD2.KFactSeitzRankTwo)
    (hA : D4GraphA2FixedPlanes) (hG : D4GraphG2SylowPairNonsplit) :
    OuterFourSeitz.D4EightGraphCubes :=
  d4EightGraphCubes_of_graphCubes (d4ThreeGraphCubes_of_residuals hS2 hA hG)

end Assembly

end CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.OuterHigh3

end
