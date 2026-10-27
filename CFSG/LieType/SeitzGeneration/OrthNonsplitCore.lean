module

public import CFSG.LieType.SeitzGeneration.OrthNonsplitTools
public import CFSG.LieType.SeitzGeneration.OrthCubeSplit
public import CFSG.LieType.SeitzGeneration.ExcPlaneBridge
public import CFSG.LieType.SeitzGeneration.SpAnisoFinal

public noncomputable section

namespace CFSG.LieType.SeitzGeneration

open Module QuadraticMap CFSG.ClassicalGroups.Orthogonal CFSG.RankThree.PartOne.KCOrthogonal
  CFSG.Open OrthBlk OrthNS
open CFSG.RankThree.Classical2 (orthDerived)

section Lift

theorem exists_hyperGen_of_hyperClosure_eq_top {G P : Type*} [Group G] [Group P] {π : G →* P}
    (hπ : Function.Surjective π) {p : ℕ} (hp : p.Prime) (hker : ¬ p ∣ Nat.card π.ker)
    {E : Subgroup G} (hE : IsElemAbelian p E) (hcard : Nat.card E = p ^ 3)
    (htop : hyperClosure p ⊤ E = ⊤) :
    ∃ E' : Subgroup P, IsElemAbelian p E' ∧ Nat.card E' = p ^ 3 ∧ HyperGen p ⊤ E' := by
  have hfp : Fact p.Prime := ⟨hp⟩
  have hdis : Disjoint E π.ker := by
    rw [Subgroup.disjoint_def]
    intro x hx hxk
    by_contra hx1
    have hord : orderOf (⟨x, hxk⟩ : π.ker) = p :=
      orderOf_eq_prime (Subtype.ext (by simpa using hE.2 x hx))
        (fun h => hx1 (congrArg Subtype.val h))
    exact hker (hord ▸ orderOf_dvd_natCard _)
  refine ⟨E.map π, CFSG.PreuniquenessRankFour.Helpers.elementary_abelian_map p hE π, ?_, ?_⟩
  · rw [← hcard]
    refine (Nat.card_congr (Equiv.ofBijective (fun x : E => (⟨π x, x, x.2, rfl⟩ : E.map π))
      ⟨fun a b hab => ?_, fun y => ?_⟩)).symm
    · have h1 : π a = π b := congrArg Subtype.val hab
      have h2 : (a : G) * (b : G)⁻¹ ∈ π.ker := by
        rw [MonoidHom.mem_ker, map_mul, map_inv, h1, mul_inv_cancel]
      have h3 := Subgroup.disjoint_def.mp hdis (E.mul_mem a.2 (E.inv_mem b.2)) h2
      exact Subtype.ext (mul_inv_eq_one.mp h3)
    · obtain ⟨_, x, hx, rfl⟩ := y
      exact ⟨⟨x, hx⟩, rfl⟩
  · intro k _
    obtain ⟨g, rfl⟩ := hπ k
    have hg : g ∈ hyperClosure p ⊤ E := by
      rw [htop]
      exact Subgroup.mem_top g
    exact map_hyperClosure_le_of_lift rfl hdis ⟨g, hg, rfl⟩

end Lift

section Triple

variable {K V : Type} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  {Q : QuadraticForm K V} {p : ℕ}

structure BlockTriple (Q : QuadraticForm K V) (p : ℕ) (S : Fin 3 → Submodule K V)
    (g : Fin 3 → V ≃ₗ[K] V) : Prop where
  reg : ∀ i, PolarNondegOn Q (S i)
  block : ∀ i, IsBlock Q p (S i) (g i)
  orth : ∀ i j, i ≠ j → OrthSep Q (S i) (S j)

omit [FiniteDimensional K V] in
theorem exists_blockTriple {L : List (Submodule K V × (V ≃ₗ[K] V))} (hL : BlockFamily Q p ⊤ L)
    (h3 : 3 ≤ L.length) : ∃ S g, BlockTriple Q p S g := by
  rcases L with _ | ⟨x₀, _ | ⟨x₁, _ | ⟨x₂, rest⟩⟩⟩
  · simp at h3
  · simp at h3
  · simp at h3
  · have hpw := hL.orth
    rw [List.pairwise_cons] at hpw
    obtain ⟨hall, hpw'⟩ := hpw
    rw [List.pairwise_cons] at hpw'
    have h01 := hall x₁ (by simp)
    have h02 := hall x₂ (by simp)
    have h12 := hpw'.1 x₂ (by simp)
    refine ⟨![x₀.1, x₁.1, x₂.1], ![x₀.2, x₁.2, x₂.2], fun i => ?_, fun i => ?_,
      fun i j hij => ?_⟩
    · fin_cases i
      · exact hL.reg x₀ (by simp)
      · exact hL.reg x₁ (by simp)
      · exact hL.reg x₂ (by simp)
    · fin_cases i
      · exact hL.block x₀ (by simp)
      · exact hL.block x₁ (by simp)
      · exact hL.block x₂ (by simp)
    · fin_cases i <;> fin_cases j
      all_goals first
        | exact absurd rfl hij
        | exact h01 | exact h02 | exact h12 | exact h01.symm | exact h02.symm | exact h12.symm

omit [FiniteDimensional K V] in
theorem stab_fixIn_of_commute {a y : V ≃ₗ[K] V} (h : Commute a y) : y ∈ stab (fixIn a ⊤) :=
  mem_stab.mpr fun u hu => ⟨fixIn_stable h (fun _ _ => Submodule.mem_top) u hu,
    fixIn_stable h.inv_right (fun _ _ => Submodule.mem_top) u hu⟩

namespace BlockTriple

variable {S : Fin 3 → Submodule K V} {g : Fin 3 → V ≃ₗ[K] V}

omit [FiniteDimensional K V] in
theorem fix_of_ne (hB : BlockTriple Q p S g) (hpK : (p : K) ≠ 0) {i j : Fin 3} (hij : i ≠ j)
    {n : V} (hn : normOp (g j) p n = 0) : g i n = n :=
  (hB.block i).fix n fun s hs => polar_fixIn_normKer (hB.block j).mem hpK
    ((hB.block j).fix s fun t ht => hB.orth j i hij.symm t ht s hs) hn

theorem commute (hB : BlockTriple Q p S g) (i j : Fin 3) : Commute (g i) (g j) := by
  by_cases hij : i = j
  · subst hij
    exact Commute.refl _
  have b₁ := hB.block i
  have b₂ := hB.block j
  have hsep := hB.orth i j hij
  have hO₁ := TauCeti.QuadraticMap.polar_apply_of_mem_orthogonalGroup b₁.mem
  have hO₂ := TauCeti.QuadraticMap.polar_apply_of_mem_orthogonalGroup b₂.mem
  have F1 : ∀ u ∈ S i, g j u = u := fun u hu => b₂.fix u fun s hs => hsep.symm s hs u hu
  have F2 : ∀ u ∈ S j, g i u = u := fun u hu => b₁.fix u fun s hs => hsep s hs u hu
  refine LinearEquiv.ext fun v => ?_
  obtain ⟨u, hu, w, hw, rfl⟩ := Submodule.mem_sup.mp ((isCompl_perp (hB.reg i)).sup_eq_top ▸
    Submodule.mem_top (x := v))
  have hw' := mem_perp.mp hw
  have h1 : g i w = w := b₁.fix w hw'
  have h2 : g i (g j w) = g j w := b₁.fix _ fun s hs => by
    have := hO₂ s w
    rw [F1 s hs] at this
    rw [this]
    exact hw' s hs
  have h3 : g j (g i u) = g i u := b₂.fix _ fun s hs => by
    have := hO₁ s u
    rw [F2 s hs] at this
    rw [this]
    exact hsep.symm s hs u hu
  have h4 : g j u = u := F1 u hu
  simp only [LinearEquiv.mul_apply, map_add, h1, h2, h3, h4]

omit [FiniteDimensional K V] in
theorem eq_one_of_fix (hB : BlockTriple Q p S g) (hpK : (p : K) ≠ 0) (i : Fin 3)
    {y : V ≃ₗ[K] V} (hU : ∀ u, g i u = u → y u = u)
    (hN : ∀ n, normOp (g i) p n = 0 → y n = n) : y = 1 :=
  LinearEquiv.ext fun v => by
    obtain ⟨c, hc, b, hb, rfl⟩ := exists_add_fixIn_normKer (hB.block i).pow hpK
      (S := ⊤) (fun _ _ => Submodule.mem_top) (Submodule.mem_top (x := v))
    rw [map_add, hU c (mem_fixIn.mp hc).2, hN b (OrthBlk.mem_normKer.mp hb).2]
    rfl

omit [FiniteDimensional K V] in
theorem dvd_of_fix (hB : BlockTriple Q p S g) (hp : p.Prime) (hpK : (p : K) ≠ 0) (i : Fin 3)
    {a : ℤ} (h : ∀ n, normOp (g i) p n = 0 → (g i ^ a) n = n) : (p : ℤ) ∣ a := by
  have : Fact p.Prime := ⟨hp⟩
  have h1 : g i ^ a = 1 := hB.eq_one_of_fix hpK i (fun u hu => zpow_apply_of_fixed hu a) h
  have h2 := orderOf_dvd_iff_zpow_eq_one.mpr h1
  rwa [orderOf_eq_prime (hB.block i).pow (hB.block i).ne] at h2

omit [FiniteDimensional K V] in
theorem zpow_eq_one_of_dvd (hB : BlockTriple Q p S g) (i : Fin 3) {a : ℤ} (h : (p : ℤ) ∣ a) :
    g i ^ a = 1 := by
  obtain ⟨t, rfl⟩ := h
  rw [zpow_mul, zpow_natCast, (hB.block i).pow, one_zpow]

omit [FiniteDimensional K V] in
theorem indep (hB : BlockTriple Q p S g) (hp : p.Prime) (hpK : (p : K) ≠ 0) {a b c : ℤ}
    (h : g 0 ^ a * g 1 ^ b * g 2 ^ c = 1) : (p : ℤ) ∣ a ∧ (p : ℤ) ∣ b ∧ (p : ℤ) ∣ c := by
  have : Fact p.Prime := ⟨hp⟩
  have ha : (p : ℤ) ∣ a := hB.dvd_of_fix hp hpK 0 fun n hn => by
    have h' := DFunLike.congr_fun h n
    rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply,
      zpow_apply_of_fixed (hB.fix_of_ne hpK (by decide : (2 : Fin 3) ≠ 0) hn),
      zpow_apply_of_fixed (hB.fix_of_ne hpK (by decide : (1 : Fin 3) ≠ 0) hn)] at h'
    exact h'
  rw [hB.zpow_eq_one_of_dvd 0 ha, one_mul] at h
  have hb : (p : ℤ) ∣ b := hB.dvd_of_fix hp hpK 1 fun n hn => by
    have h' := DFunLike.congr_fun h n
    rw [LinearEquiv.mul_apply,
      zpow_apply_of_fixed (hB.fix_of_ne hpK (by decide : (2 : Fin 3) ≠ 1) hn)] at h'
    exact h'
  rw [hB.zpow_eq_one_of_dvd 1 hb, one_mul] at h
  refine ⟨ha, hb, ?_⟩
  have h2 := orderOf_dvd_iff_zpow_eq_one.mpr h
  rwa [orderOf_eq_prime (hB.block 2).pow (hB.block 2).ne] at h2

omit [FiniteDimensional K V] in
theorem reg_fixIn (hB : BlockTriple Q p S g) (hQ : (polarBilin Q).Nondegenerate)
    (hpK : (p : K) ≠ 0) (i : Fin 3) : PolarNondegOn Q (fixIn (g i) ⊤) :=
  polarNondegOn_fixIn (hB.block i).mem (hB.block i).pow hpK (polarNondegOn_top hQ)
    fun _ _ => Submodule.mem_top

omit [FiniteDimensional K V] in
theorem reg_normKer (hB : BlockTriple Q p S g) (hQ : (polarBilin Q).Nondegenerate)
    (hpK : (p : K) ≠ 0) (i : Fin 3) : PolarNondegOn Q (OrthBlk.normKer (g i) p ⊤) :=
  polarNondegOn_normKer (hB.block i).mem (hB.block i).pow hpK (polarNondegOn_top hQ)
    fun _ _ => Submodule.mem_top

omit [FiniteDimensional K V] in
theorem normKer_ne_bot (hB : BlockTriple Q p S g) (hpK : (p : K) ≠ 0) (i : Fin 3) :
    OrthBlk.normKer (g i) p ⊤ ≠ ⊥ := fun h =>
  (hB.block i).ne (hB.eq_one_of_fix hpK i (fun _ hu => hu) fun n hn => by
    have : n ∈ OrthBlk.normKer (g i) p ⊤ := OrthBlk.mem_normKer.mpr ⟨Submodule.mem_top, hn⟩
    rw [h, Submodule.mem_bot] at this
    rw [this, map_zero])

theorem four_le_normKer (hB : BlockTriple Q p S g) [Finite K]
    (hQ : (polarBilin Q).Nondegenerate) (hp : p.Prime) (hp2 : p ≠ 2)
    (hpq : ¬ p ∣ Nat.card K ^ 2 - 1) (hpKd : ¬ p ∣ Nat.card K) (hpK : (p : K) ≠ 0) (i : Fin 3) :
    4 ≤ finrank K (OrthBlk.normKer (g i) p ⊤) := by
  refine four_le_finrank_of_fixedPointFree hp hp2 hpq hpKd (hB.reg_normKer hQ hpK i)
    (hB.normKer_ne_bot hpK i) (hB.block i).mem (hB.block i).pow
    (normKer_stable (Commute.refl _) fun _ _ => Submodule.mem_top)
    (normKer_stable (Commute.refl (g i)).inv_right fun _ _ => Submodule.mem_top)
    fun u hu hfix => ?_
  exact Submodule.disjoint_def.mp (disjoint_fixIn_normKer hpK ⊤) u
    (mem_fixIn.mpr ⟨Submodule.mem_top, hfix⟩) hu

omit [FiniteDimensional K V] in
theorem normKer_le_fixIn (hB : BlockTriple Q p S g) (hpK : (p : K) ≠ 0) {i j : Fin 3}
    (hij : i ≠ j) : OrthBlk.normKer (g j) p ⊤ ≤ fixIn (g i) ⊤ :=
  fun _ hn => mem_fixIn.mpr
    ⟨Submodule.mem_top, hB.fix_of_ne hpK hij (OrthBlk.mem_normKer.mp hn).2⟩

omit [FiniteDimensional K V] in
theorem orthSep_normKer (hB : BlockTriple Q p S g) (hpK : (p : K) ≠ 0) {j k : Fin 3}
    (hjk : j ≠ k) : OrthSep Q (OrthBlk.normKer (g j) p ⊤) (OrthBlk.normKer (g k) p ⊤) :=
  fun _ ha _ hb => polar_fixIn_normKer (hB.block k).mem hpK
    (hB.fix_of_ne hpK hjk.symm (OrthBlk.mem_normKer.mp ha).2) (OrthBlk.mem_normKer.mp hb).2

theorem eight_le_fixIn (hB : BlockTriple Q p S g) [Finite K]
    (hQ : (polarBilin Q).Nondegenerate) (hp : p.Prime) (hp2 : p ≠ 2)
    (hpq : ¬ p ∣ Nat.card K ^ 2 - 1) (hpKd : ¬ p ∣ Nat.card K) (hpK : (p : K) ≠ 0)
    {i j k : Fin 3} (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    8 ≤ finrank K (fixIn (g i) ⊤) := by
  have hle : OrthBlk.normKer (g j) p ⊤ ⊔ OrthBlk.normKer (g k) p ⊤ ≤ fixIn (g i) ⊤ :=
    sup_le (hB.normKer_le_fixIn hpK hij) (hB.normKer_le_fixIn hpK hik)
  have hd := (hB.orthSep_normKer hpK hjk).disjoint (hB.reg_normKer hQ hpK j)
  have h1 := Submodule.finrank_mono hle
  rw [finrank_sup_of_disjoint hd] at h1
  have := hB.four_le_normKer hQ hp hp2 hpq hpKd hpK j
  have := hB.four_le_normKer hQ hp hp2 hpq hpKd hpK k
  omega

theorem exists_cube (hB : BlockTriple Q p S g) [Finite K] (hQ : (polarBilin Q).Nondegenerate)
    (hT : ∃ T : Submodule K V, finrank K T = 3 ∧ ∀ x ∈ T, Q x = 0)
    (hE : orthDerived Q = elementaryGroup Q) (hp : p.Prime) (hp2 : p ≠ 2) (hpK : (p : K) ≠ 0) :
    ∃ (G : Fin 3 → elementaryGroup Q) (E : Subgroup (elementaryGroup Q)),
      (∀ i, (G i : V ≃ₗ[K] V) = g i) ∧ IsElemAbelian p E ∧ Nat.card E = p ^ 3 ∧
        ∀ i, G i ∈ E := by
  let G : Fin 3 → elementaryGroup Q := fun i =>
    ⟨g i, mem_elementaryGroup_of_odd_pow hQ hT hE hp hp2 (hB.block i).mem (hB.block i).pow⟩
  have hG : ∀ i, (G i : V ≃ₗ[K] V) = g i := fun i => rfl
  have hc : ∀ i j, Commute (G i) (G j) := fun i j => Subtype.ext (hB.commute i j).eq
  have hGp : ∀ i, G i ^ p = 1 := fun i => Subtype.ext (hB.block i).pow
  obtain ⟨E, hEab, hEcard, -, h0, h1, h2⟩ := exists_cube_of_three hp (hc 0 1) (hc 0 2) (hc 1 2)
    (hGp 0) (hGp 1) (hGp 2) fun a b c h => hB.indep hp hpK (by
      have := congrArg Subtype.val h
      simpa [hG] using this)
  refine ⟨G, E, hG, hEab, hEcard, fun i => ?_⟩
  fin_cases i
  · exact h0
  · exact h1
  · exact h2

end BlockTriple

end Triple

section CaseHigh

variable {K V : Type} [Field K] [Finite K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  {Q : QuadraticForm K V} {p : ℕ}

theorem exists_hyperGen_of_not_rankLE2 {d : TauCeti.ValidLieTypeIndex}
    {π : elementaryGroup Q →* Cat d} (hc : IsOrthogonalCover Q π) (hp : p.Prime) (hp2 : p ≠ 2)
    (hpK : (p : K) ≠ 0) {U : Submodule K V} (hU : PolarNondegOn Q U)
    (h3 : 3 ≤ finrank K (perp Q U))
    (hEU : orthDerived (Q.comp U.subtype) = elementaryGroup (Q.comp U.subtype))
    (hrank : ¬ RankLE2 p (orthDerived (Q.comp U.subtype))) :
    ∃ E' : Subgroup (Cat d), IsElemAbelian p E' ∧ Nat.card E' = p ^ 3 ∧
      HyperGen p (⊤ : Subgroup (Cat d)) E' := by
  obtain ⟨-, E₀, hE₀, hc₀⟩ := exists_isElemAbelian_card_of_not_rankLE2 hp hrank
  have hmem : ∀ x : orthDerived (Q.comp U.subtype),
      ((extU hU).comp (orthDerived (Q.comp U.subtype)).subtype) x ∈ elementaryGroup Q :=
    fun x => eichlerGroupOn_le_elementaryGroup U (extU_mem_eichlerGroupOn hU (hEU ▸ x.2))
  let Ψ : orthDerived (Q.comp U.subtype) →* elementaryGroup Q :=
    ((extU hU).comp (orthDerived (Q.comp U.subtype)).subtype).codRestrict _ hmem
  have hΨ : Function.Injective Ψ := fun a b hab =>
    Subtype.ext (extU_injective hU (congrArg Subtype.val hab))
  obtain ⟨w, hw, hw0, hwQ⟩ := exists_singular_of_three_le_general
    (polarNondegOn_perp hc.nondegenerate hU) h3
  refine exists_hyperGen_of_stable_cube hc hp hp2 hpK
    (CFSG.PreuniquenessRankFour.Helpers.elementary_abelian_map p hE₀ Ψ)
    (by rw [Subgroup.card_map_of_injective hΨ, hc₀]) (W := K ∙ w)
    (fun h0 => hw0 (Submodule.span_singleton_eq_bot.mp h0)) ?_ ?_
  · intro x hx
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hx
    rw [QuadraticMap.map_smul, hwQ, smul_zero]
  · rintro _ ⟨y, -, rfl⟩ x hx
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hx
    change extU hU (y : U ≃ₗ[K] U) (c • w) ∈ K ∙ w
    rw [map_smul, extU_apply_perp hU _ hw]
    exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self w)

end CaseHigh

end CFSG.LieType.SeitzGeneration
