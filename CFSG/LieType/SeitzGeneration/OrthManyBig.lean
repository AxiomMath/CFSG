module

public import CFSG.LieType.SeitzGeneration.OrthManyPieces
public import CFSG.LieType.SeitzGeneration.OrthManyRank
public import CFSG.LieType.SeitzGeneration.OrthManyGlue
public import CFSG.LieType.SeitzGeneration.OrthDfourBig

public section

namespace CFSG.LieType.SeitzGeneration

open Module QuadraticMap CFSG.ClassicalGroups.Orthogonal CFSG.RankThree.PartOne.CTP
  CFSG.RankThree.PartOne.KCOrthogonal CFSG.RankThree.Classical CFSG.Open OrthNS OrthBlk
open CFSG.RankThree.Classical2 (orthDerived)

section Restrict

variable {K V : Type} [Field K] [Finite K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  {Q : QuadraticForm K V} {p : ℕ} {E : Subgroup (orthDerived Q)}

omit [Finite K] [FiniteDimensional K V] in
theorem manyBig_eStable_sup {S T : Submodule K V} (hS : EStable E S) (hT : EStable E T) :
    EStable E (S ⊔ T) := by
  intro x hx u hu
  obtain ⟨s, hs, t, ht, rfl⟩ := Submodule.mem_sup.mp hu
  rw [map_add]
  exact Submodule.add_mem_sup (hS x hx s hs) (hT x hx t ht)

omit [Finite K] [FiniteDimensional K V] in
theorem manyBig_mem_stab (hK : KernelLineData Q p E) (hp : 0 < p) {U : Submodule K V}
    (hU : EStable E U) (x : E) : ((x : orthDerived Q) : V ≃ₗ[K] V) ∈ stab U :=
  OrthNS.mem_stab.mpr fun u hu => ⟨hU x x.2 u hu, hU.symm_apply_mem hK hp x.2 hu⟩

omit [Finite K] [FiniteDimensional K V] in
theorem manyBig_orthSep_sup_left {S S' T : Submodule K V} (h : OrthSep Q S T)
    (h' : OrthSep Q S' T) : OrthSep Q (S ⊔ S') T := by
  intro x hx t ht
  obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.mp hx
  rw [polar_add_left, h a ha t ht, h' b hb t ht, add_zero]

theorem manyBig_exists_restrict_hom (hK : KernelLineData Q p E)
    (hp : p.Prime) (hp2 : p ≠ 2) {U : Submodule K V} (hU : PolarNondegOn Q U)
    (hTU : ∃ T : Submodule K U, finrank K T = 3 ∧ ∀ x ∈ T, (Q.comp U.subtype) x = 0)
    (hUst : EStable E U) :
    ∃ ρ : E →* orthDerived (Q.comp U.subtype), ∀ (x : E) (u : U),
      (((ρ x : orthDerived (Q.comp U.subtype)) : U ≃ₗ[K] U) u : V) =
        ((x : orthDerived Q) : V ≃ₗ[K] V) u := by
  have hQU := nondegenerate_comp_subtype hU
  have hst := manyBig_mem_stab hK hp.pos hUst
  let T : E → stab U := fun x => ⟨((x : orthDerived Q) : V ≃ₗ[K] V), hst x⟩
  have hTp : ∀ x : E, T x ^ p = 1 := fun x => Subtype.ext (coe_pow_eq_one hK x)
  have hres : ∀ x : E, res U (T x) ∈ orthDerived (Q.comp U.subtype) := fun x =>
    mem_orthDerived_of_odd_pow hQU hTU (hp.odd_of_ne_two hp2)
      (TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mpr fun u => by
        change Q (((x : orthDerived Q) : V ≃ₗ[K] V) (u : V)) = Q (u : V)
        exact TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mp
          (orthDerived_mem_orthogonalGroup (g := (x : orthDerived Q))) u)
      (by rw [← map_pow, hTp x, map_one])
  exact ⟨MonoidHom.mk' (fun x : E => (⟨res U (T x), hres x⟩ : orthDerived (Q.comp U.subtype)))
    fun x y => Subtype.ext (LinearEquiv.ext fun u => Subtype.ext rfl), fun x u => rfl⟩

end Restrict

section TwoPieces

variable {K V : Type} [Field K] [Finite K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  {Q : QuadraticForm K V} {p : ℕ} {E : Subgroup (orthDerived Q)}

theorem eichler_mem_of_two_pieces (hQ : (polarBilin Q).Nondegenerate)
    (hT : ∃ T : Submodule K V, finrank K T = 3 ∧ ∀ x ∈ T, Q x = 0) (hp : p.Prime) (hp5 : 5 ≤ p)
    (hpl : p ≠ ringChar K) (hK : KernelLineData Q p E) (hNS : OrthNoInvariantSingular Q E)
    (h4 : 4 ≤ orderOf ((Nat.card K : ℕ) : ZMod p)) {P₁ P₂ : Submodule K V}
    (h₁ : IsPiece Q E P₁) (h₂ : IsPiece Q E P₂) (h12 : OrthSep Q P₁ P₂) {M₁ M₂ : Subgroup E}
    (hM₁ : Nat.card M₁ = p) (hM₂ : Nat.card M₂ = p) (hM12 : M₁ ≠ M₂)
    (hk₁ : ∀ x : E, (∀ u ∈ P₁, ((x : orthDerived Q) : V ≃ₗ[K] V) u = u) → x ∈ M₁)
    (hk₂ : ∀ x : E, (∀ u ∈ P₂, ((x : orthDerived Q) : V ≃ₗ[K] V) u = u) → x ∈ M₂)
    (hf₁ : finrank K P₁ = orderOf ((Nat.card K : ℕ) : ZMod p))
    (hf₂ : finrank K P₂ = orderOf ((Nat.card K : ℕ) : ZMod p)) :
    ∀ x ∈ planeFixSpace E ⊔ P₁ ⊔ P₂, ∀ y ∈ planeFixSpace E ⊔ P₁ ⊔ P₂,
      eichler Q x y ∈ orthCentralizerSpan Q E := by
  classical
  have hp2 : p ≠ 2 := by omega
  set U : Submodule K V := planeFixSpace E ⊔ P₁ ⊔ P₂
  have hV0 : PolarNondegOn Q (planeFixSpace E) := polarNondegOn_planeFixSpace hK
  have hP₁U : P₁ ≤ U := le_sup_of_le_left le_sup_right
  have hP₂U : P₂ ≤ U := le_sup_right
  have hU : PolarNondegOn Q U := polarNondegOn_sup (polarNondegOn_sup hV0 h₁.regular
    h₁.orthSep.symm) h₂.regular (manyBig_orthSep_sup_left h₂.orthSep.symm h12)
  have hdisj : Disjoint P₁ P₂ := OrthSep.disjoint h₁.regular h12
  have hdim12 : finrank K ↥(P₁ ⊔ P₂) = finrank K P₁ + finrank K P₂ := by
    have := Submodule.finrank_sup_add_finrank_inf_eq P₁ P₂
    rwa [hdisj.eq_bot, finrank_bot, add_zero] at this
  have hU8 : 8 ≤ finrank K U := by
    have : finrank K ↥(P₁ ⊔ P₂) ≤ finrank K U :=
      Submodule.finrank_mono (sup_le hP₁U hP₂U)
    omega
  have hUle : finrank K U ≤ finrank K (planeFixSpace E) + finrank K P₁ + finrank K P₂ := by
    have h1 : finrank K U ≤ finrank K ↥(planeFixSpace E ⊔ P₁) + finrank K P₂ :=
      Submodule.finrank_add_le_finrank_add_finrank _ _
    have h2 := Submodule.finrank_add_le_finrank_add_finrank (planeFixSpace E) P₁
    omega
  have hV02 := finrank_planeFixSpace_le_two hNS
  have hlt : finrank K U < 3 * orderOf ((Nat.card K : ℕ) : ZMod p) := by omega
  have hV0st : EStable E (planeFixSpace E) :=
    EStable.of_fixed fun x hx u hu => hu _ ⟨x, hx, rfl⟩
  have hUst : EStable E U := manyBig_eStable_sup (manyBig_eStable_sup hV0st h₁.eStable) h₂.eStable
  have hQU := nondegenerate_comp_subtype hU
  have hTU := exists_ts_three_comp hU hU8
  obtain ⟨ρ, hρ⟩ := manyBig_exists_restrict_hom hK hp hp2 hU hTU hUst
  have hfinE : Finite E :=
    Nat.finite_of_card_ne_zero (by rw [hK.card]; exact pow_ne_zero 2 hp.ne_zero)
  have hfix : ∀ x : E, ρ x = 1 → ∀ P : Submodule K V, P ≤ U →
      ∀ u ∈ P, ((x : orthDerived Q) : V ≃ₗ[K] V) u = u := by
    intro x hx P hPU u hu
    have := hρ x ⟨u, hPU hu⟩
    rw [hx] at this
    exact this.symm
  have hinj : Function.Injective ρ := by
    rw [injective_iff_map_eq_one]
    intro x hx
    have h1 : x ∈ M₁ ⊓ M₂ :=
      ⟨hk₁ x (hfix x hx P₁ hP₁U), hk₂ x (hfix x hx P₂ hP₂U)⟩
    rwa [inf_eq_bot_of_card_prime' hp hM₁ hM₂ hM12, Subgroup.mem_bot] at h1
  have hcomm' : ∀ x ∈ ρ.range, ∀ y ∈ ρ.range, x * y = y * x := by
    rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩
    rw [← map_mul, ← map_mul, hK.comm a b]
  have hexp' : ∀ x ∈ ρ.range, x ^ p = 1 := by
    rintro _ ⟨a, rfl⟩
    rw [← map_pow, hK.exp a, map_one]
  have hcard' : Nat.card ρ.range = p ^ 2 :=
    (Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv).symm.trans hK.card
  have haniso : ∀ u ∈ planeFixSpace ρ.range, (Q.comp U.subtype) u = 0 → u = 0 := by
    intro u hu hQu
    have hu0 : (u : V) ∈ planeFixSpace E := by
      refine mem_fixSpace.mpr fun g hg => ?_
      obtain ⟨x, hx, rfl⟩ := hg
      have h1 := mem_fixSpace.mp hu ((ρ ⟨x, hx⟩ : orthDerived (Q.comp U.subtype)) : U ≃ₗ[K] U)
        ⟨ρ ⟨x, hx⟩, ⟨⟨x, hx⟩, rfl⟩, rfl⟩
      have h2 := hρ ⟨x, hx⟩ u
      rw [h1] at h2
      exact h2.symm
    exact Subtype.ext (eq_zero_of_singular_planeFixSpace hNS hu0 hQu)
  have hclos := orthSelfDualTwoBlocks K U (Q.comp U.subtype) hQU hTU (by omega) p hp hp5 hpl
    (rankLE2_of_finrank_lt hQU hp hp2 hpl hlt) ρ.range hcomm' hexp' hcard' haniso
    (hasSelfDualFactor_restrict hK hp hpl hU ρ hρ h₁ hP₁U)
  have hgen : Subgroup.closure {h : orthDerived (Q.comp U.subtype) |
      ∃ x : E, x ≠ 1 ∧ h * ρ x = ρ x * h} = ⊤ := by
    rw [eq_top_iff, ← hclos]
    refine Subgroup.closure_mono ?_
    rintro h ⟨_, ⟨x, rfl⟩, hx1, hh⟩
    exact ⟨x, fun h1 => hx1 (by rw [h1, map_one]), hh⟩
  have hΩ : elementaryGroup Q ≤ orthDerived Q := (orthDerived_eq_and_le_closure hQ hT).1.ge
  have hEU := (orthDerived_eq_and_le_closure hQU hTU).1
  exact eichler_mem_of_restricted_plane hU hEU E (manyBig_mem_stab hK hp.pos hUst) hΩ ρ hρ hgen

end TwoPieces

section Main

theorem closure_eq_top_of_noSingular_big {K V : Type} [Field K] [Finite K] [AddCommGroup V]
    [Module K V] [FiniteDimensional K V] (Q : QuadraticForm K V)
    (hQ : (polarBilin Q).Nondegenerate)
    (hT : ∃ T : Submodule K V, finrank K T = 3 ∧ ∀ x ∈ T, Q x = 0) (hdim : 7 ≤ finrank K V)
    {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) (hpl : p ≠ ringChar K) (E : Subgroup (orthDerived Q))
    (hcomm : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x) (hexp : ∀ x ∈ E, x ^ p = 1)
    (hcard : Nat.card E = p ^ 2) (hNS : OrthNoInvariantSingular Q E)
    (h4 : 4 ≤ orderOf ((Nat.card K : ℕ) : ZMod p)) :
    Subgroup.closure {h : orthDerived Q | ∃ x ∈ E, x ≠ 1 ∧ h * x = x * h} = ⊤ := by
  classical
  have hp2 : p ≠ 2 := by omega
  haveI : Nontrivial V := nontrivial_of_three_singular hT
  obtain ⟨hK, -⟩ := exists_kernelLineData_of_le hQ hp hp2 hpl E hcomm hexp hcard
  obtain ⟨n, P, hP, hPP, -, hPsp⟩ :=
    exists_piece_decomposition hQ hp hp2 hpl E hcomm hexp hcard hNS
  choose M hMc hMP hMk hMf _ _ using fun i => (hP i).exists_line hK hp hp2 hpl
  obtain ⟨i, j, hij⟩ := exists_pieces_diff_lines hK hp hpl hP hPsp (M := M)
    fun i => ⟨hMc i, hMP i⟩
  have hji : j ≠ i := fun h => hij (h ▸ rfl)
  haveI : Nonempty {k : Fin n // k ≠ i} := ⟨⟨j, hji⟩⟩
  have hEΩ : elementaryGroup Q ≤ orthDerived Q := (orthDerived_eq_and_le_closure hQ hT).1.ge
  have hEich : ∀ k : {k : Fin n // k ≠ i}, ∀ x ∈ planeFixSpace E ⊔ P i ⊔ P k,
      ∀ y ∈ planeFixSpace E ⊔ P i ⊔ P k, eichler Q x y ∈ orthCentralizerSpan Q E := by
    intro k
    by_cases hM : M i = M k
    · have hle : planeFixSpace E ⊔ P i ⊔ P k ≤ planeFixSpace E ⊔ lineSpace (M i) := by
        refine sup_le (sup_le le_sup_left ((hMP i).trans le_sup_right)) ?_
        rw [hM]
        exact (hMP k).trans le_sup_right
      exact fun x hx y hy => eichler_mem_span_of_mem_sup hEΩ
        (ne_bot_of_card_prime hp (hMc i)) (hle hx) (hle hy)
    · exact eichler_mem_of_two_pieces hQ hT hp hp5 hpl hK hNS h4 (hP i) (hP k)
        (hPP i k k.2.symm) (hMc i) (hMc k) hM (hMk i) (hMk k) (hMf i) (hMf k)
  have hspan : (⊤ : Submodule K V) ≤
      planeFixSpace E ⊔ P i ⊔ ⨆ k : {k : Fin n // k ≠ i}, P k := by
    refine hPsp.trans (sup_le (le_sup_of_le_left le_sup_left) (iSup_le fun k => ?_))
    by_cases hk : k = i
    · rw [hk]
      exact le_sup_of_le_left le_sup_right
    · exact le_sup_of_le_right (le_iSup (fun k : {k : Fin n // k ≠ i} => P k) ⟨k, hk⟩)
  have hle : elementaryGroup Q ≤ orthCentralizerSpan Q E :=
    elementaryGroup_le_of_pieces hQ (orthCentralizerSpan_le_orthogonalGroup E) (hP i).regular
      (by have := hMf i; omega) (fun k : {k : Fin n // k ≠ i} => P k) (hP i).orthSep
      (fun k => hPP i k k.2.symm) hspan hEich
  exact closure_centralizers_eq_top_of_le E
    ((orthDerived_eq_and_le_closure hQ hT).1.le.trans hle)

end Main

end CFSG.LieType.SeitzGeneration
