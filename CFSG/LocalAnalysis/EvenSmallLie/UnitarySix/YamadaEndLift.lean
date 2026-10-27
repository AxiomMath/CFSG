module

public import CFSG.LieType.Multipliers.L34Upper

public section

namespace CFSG.EvenSmallLie.UnitarySix.YamadaEnd

open Subgroup CFSG.Blueprint

theorem card_ker_dvd_fortyEight
    {E S : Type} [Group E] [Group S] [Group.IsPerfect E]
    (hS : LieModel S .PSL 3 2 2) (q : E →* S) (hq : Function.Surjective q)
    (hker : q.ker ≤ center E) : Nat.card q.ker ∣ 48 := by
  obtain ⟨-, ⟨e⟩⟩ := CFSG.LieType.Multipliers.L34Upper.multiplier_PSL_three_four S hS
  have hM : Nat.card (CFSG.RankThree.PerfectCover.hopfMultiplier S) = 48 := by
    rw [← Nat.card_congr (CFSG.RankThree.PerfectCover.hopfMultiplierEquivGriess S).toEquiv,
      Nat.card_congr e.toEquiv, Nat.card_congr Multiplicative.toAdd, Nat.card_prod,
      Nat.card_prod]
    simp
  rw [← CFSG.RankThree.PerfectCover.map_hopfMultiplier_hopfLift q hq hker, ← hM]
  exact Subgroup.card_map_dvd _ _

theorem exists_lift
    {A M K : Type} [Group A] [Group M] [Group K] [Finite A] [Finite M]
    [Group.IsPerfect A] (hK : LieModel K .PSL 3 2 2) (χ : A →* K) (hχ : Function.Surjective χ)
    (hχker : χ.ker = center A) (hZ : Nat.card (center A) = 3) (δ : M →* K)
    (hδ : Function.Surjective δ) (hδker : δ.ker ≤ center M) (hodd : Odd (Nat.card δ.ker)) :
    ∃ θ : A →* M, δ.comp θ = χ := by
  set E : Subgroup (A × M) :=
    MonoidHom.eqLocus (χ.comp (MonoidHom.fst A M)) (δ.comp (MonoidHom.snd A M)) with hE
  have hmemE : ∀ x : E, χ (x : A × M).1 = δ (x : A × M).2 := fun x => x.2
  let qE : E →* K := (χ.comp (MonoidHom.fst A M)).comp E.subtype
  let f₁ : E →* A := (MonoidHom.fst A M).comp E.subtype
  have hf₁ : Function.Surjective f₁ := by
    intro a
    obtain ⟨m, hm⟩ := hδ (χ a)
    exact ⟨⟨(a, m), hm.symm⟩, rfl⟩
  have hqE : Function.Surjective qE := hχ.comp hf₁
  have hqE_ker : qE.ker ≤ center E := by
    intro x hx
    rw [MonoidHom.mem_ker] at hx
    have h1 : (x : A × M).1 ∈ center A := hχker ▸ hx
    have h2 : (x : A × M).2 ∈ center M := hδker (by
      rw [MonoidHom.mem_ker, ← hmemE x]
      exact hx)
    rw [mem_center_iff]
    intro y
    exact Subtype.ext (Prod.ext (mem_center_iff.mp h1 _) (mem_center_iff.mp h2 _))
  have hKperf : Group.IsPerfect K := Group.isPerfect_def.2
    (CFSG.LieType.Multipliers.L34Upper.multiplier_PSL_three_four K hK).1
  obtain ⟨-, hDperf, hq⟩ :=
    CFSG.LocalCores.central_extension_derived_of_surjective qE hqE hqE_ker hKperf
  let D := commutator E
  let q : D →* K := qE.comp D.subtype
  let p₁ : D →* A := f₁.comp D.subtype
  have hqp : q = χ.comp p₁ := rfl
  have hp₁ : Function.Surjective p₁ := by
    rw [← MonoidHom.range_eq_top, MonoidHom.range_comp, range_subtype]
    change map f₁ (commutator E) = ⊤
    rw [commutator_def, map_commutator, map_top_of_surjective _ hf₁, ← commutator_def,
      Group.IsPerfect.commutator_eq_top]
  have hq_ker : q.ker ≤ center D := by
    intro x hx
    have hxE : (x : E) ∈ center E := hqE_ker hx
    exact mem_center_iff.mpr fun y => Subtype.ext (mem_center_iff.mp hxE y)
  have hdvd : Nat.card q.ker ∣ 48 := card_ker_dvd_fortyEight hK q hq hq_ker
  have hcard : Nat.card q.ker = Nat.card p₁.ker * 3 := by
    have hk : q.ker = (center A).comap p₁ := by rw [hqp, ← MonoidHom.comap_ker, hχker]
    have h1 := Subgroup.card_mul_index ((center A).comap p₁)
    have h2 := Subgroup.card_mul_index p₁.ker
    have h3 := Subgroup.card_mul_index (center A)
    rw [index_comap_of_surjective _ hp₁] at h1
    rw [Subgroup.index_ker, MonoidHom.range_eq_top.mpr hp₁, card_top] at h2
    rw [hk]
    have hpos : 0 < (center A).index := Nat.pos_of_ne_zero (Subgroup.index_ne_zero_of_finite)
    rw [← hZ]
    apply Nat.eq_of_mul_eq_mul_right hpos
    rw [h1, ← h2, ← h3]
    ring
  have hodd' : Odd (Nat.card p₁.ker) := by
    let g : p₁.ker →* M :=
      (MonoidHom.snd A M).comp (E.subtype.comp (D.subtype.comp p₁.ker.subtype))
    have hg : Function.Injective g := by
      rw [injective_iff_map_eq_one]
      intro x hx
      have h1 : ((x : D) : E).1.1 = 1 := MonoidHom.mem_ker.mp x.2
      exact Subtype.ext (Subtype.ext (Subtype.ext (Prod.ext h1 hx)))
    have hle : g.range ≤ δ.ker := by
      rintro _ ⟨x, rfl⟩
      rw [MonoidHom.mem_ker]
      change δ (((x : D) : E) : A × M).2 = 1
      rw [← hmemE, show (((x : D) : E) : A × M).1 = 1 from MonoidHom.mem_ker.mp x.2, map_one]
    have h1 := Subgroup.card_dvd_of_le hle
    rw [← Nat.card_congr (MonoidHom.ofInjective hg).toEquiv] at h1
    exact Odd.of_dvd_nat hodd h1
  have hone : Nat.card p₁.ker = 1 := by
    rw [hcard] at hdvd
    have h16 : Nat.card p₁.ker ∣ 2 ^ 4 := by
      have : Nat.card p₁.ker * 3 ∣ 16 * 3 := hdvd
      exact Nat.dvd_of_mul_dvd_mul_right (by norm_num) this
    exact (Nat.Coprime.pow_right 4 (Nat.coprime_two_right.2 hodd')).eq_one_of_dvd h16
  have hinj : Function.Injective p₁ := by
    rw [← MonoidHom.ker_eq_bot_iff, ← Subgroup.card_eq_one]
    exact hone
  let e := MulEquiv.ofBijective p₁ ⟨hinj, hp₁⟩
  refine ⟨(MonoidHom.snd A M).comp (E.subtype.comp (D.subtype.comp e.symm.toMonoidHom)), ?_⟩
  ext a
  have h1 : p₁ (e.symm a) = a := e.apply_symm_apply a
  change δ ((((e.symm a : D) : E) : A × M).2) = χ a
  rw [← hmemE]
  exact congrArg χ h1

end CFSG.EvenSmallLie.UnitarySix.YamadaEnd
