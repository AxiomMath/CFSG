module

public import CFSG.HardMathSupport.Curtis.UnitaryLevi.BlockIbAltTwenty
public import CFSG.HardMathSupport.Curtis.UnitaryLevi.PermPerfectCentralizer
public import CFSG.Milestones.AT_alternating_automorphism_permutation
public import CFSG.Alternating.Multipliers.OddKernel
public import CFSG.ThirdParty.QiuzhenCFSG.Theory.AutAlternating
public import CFSG.LocalAnalysis.AGLEmbedding.BlockToralReduceGlue

public section

namespace CFSG.HardMathSupport.Curtis.UnitaryLevi

open CFSG.AGLEmbedding CFSG.AGLEmbedding.ToralReduce CFSG.Open Equiv
open scoped commutatorElement

noncomputable def autAltTenEquiv : Perm (Fin 10) ≃* MulAut (alternatingGroup (Fin 10)) :=
  MulEquiv.ofBijective (MulAut.conjNormal (H := alternatingGroup (Fin 10)))
    ⟨CFSG.GroupTheory.AutAlternating.conjNormal_injective_alternatingGroup 10 (by norm_num),
      fun f => by
        obtain ⟨σ, hσ⟩ := CFSG.Milestones.alternating_automorphism_permutation (n := 10)
          (Or.inr (by norm_num)) f
        refine ⟨σ, MulEquiv.ext fun g => Subtype.ext ?_⟩
        rw [hσ g]
        simp⟩

section Abstract

variable {Y : Type*} [Group Y] {Lb : Subgroup Y}

theorem exists_hom_perm_of_mulEquiv_alt_ten (ι : ↥Lb ≃* alternatingGroup (Fin 10)) :
    ∃ ψ : ↥(Subgroup.normalizer (Lb : Set Y)) →* Perm (Fin 10),
      ∀ n, ψ n = 1 → ∀ l ∈ Lb, l * (n : Y) = n * l := by
  refine ⟨autAltTenEquiv.symm.toMonoidHom.comp
    ((MulAut.congr ι).toMonoidHom.comp Lb.normalizerMonoidHom), fun n hn l hl => ?_⟩
  have h1 : MulAut.congr ι (Lb.normalizerMonoidHom n) = 1 := by
    have := autAltTenEquiv.apply_symm_apply (MulAut.congr ι (Lb.normalizerMonoidHom n))
    rw [← this]
    change autAltTenEquiv (autAltTenEquiv.symm (MulAut.congr ι (Lb.normalizerMonoidHom n))) = 1
    have hn' : autAltTenEquiv.symm (MulAut.congr ι (Lb.normalizerMonoidHom n)) = 1 := hn
    rw [hn', map_one]
  have h2 : Lb.normalizerMonoidHom n = 1 := by
    have := (MulAut.congr ι).injective (h1.trans (map_one _).symm)
    exact this
  have h3 := congrArg (fun f : MulAut ↥Lb => ((f ⟨l, hl⟩ : ↥Lb) : Y)) h2
  have h4 : (n : Y) * l * (n : Y)⁻¹ = l := h3
  calc l * (n : Y) = (n * l * (n : Y)⁻¹) * n := by rw [h4]
    _ = n * l := by group

theorem commutative_of_isPGroup_three_of_card_le {Q : Type*} [Group Q] [Finite Q]
    (hQ : IsPGroup 3 Q) (h : Nat.card Q ≤ 3) (a b : Q) : a * b = b * a := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨j, hj⟩ := (IsPGroup.iff_card).mp hQ
  rcases Nat.lt_or_ge j 2 with hj2 | hj2
  · interval_cases j
    · have : Subsingleton Q := (Nat.card_eq_one_iff_unique.mp (by simpa using hj)).1
      exact Subsingleton.elim _ _
    · have : IsCyclic Q := isCyclic_of_prime_card (p := 3) (by simpa using hj)
      exact (IsCyclic.commGroup (α := Q)).mul_comm a b
  · have : 3 ^ 2 ≤ 3 ^ j := Nat.pow_le_pow_right (by norm_num) hj2
    omega

theorem three_group_of_alt_ten {D X : Subgroup Y} {x : Y}
    (ι : ↥Lb ≃* alternatingGroup (Fin 10)) (hDperf : ⁅D, D⁆ = D)
    (hDN : D ≤ Subgroup.normalizer (Lb : Set Y)) (hxD : x ∈ D)
    (hxC : x ∉ Subgroup.centralizer (Lb : Set Y))
    (hXN : X ≤ Subgroup.normalizer (Lb : Set Y)) (hXD : X ≤ Subgroup.centralizer (D : Set Y))
    (hX : IsPGroup 3 X) :
    (∀ a ∈ X, ∀ b ∈ X, a * b * a⁻¹ * b⁻¹ ∈ Subgroup.centralizer (Lb : Set Y)) ∧
      (X ⊓ Subgroup.centralizer (Lb : Set Y) = ⊥ → Nat.card X ≤ 3) := by
  obtain ⟨ψ, hψ⟩ := exists_hom_perm_of_mulEquiv_alt_ten ι
  let fD : D →* Perm (Fin 10) := ψ.comp (Subgroup.inclusion hDN)
  let fX : X →* Perm (Fin 10) := ψ.comp (Subgroup.inclusion hXN)
  have hperf : Group.IsPerfect D := Subgroup.isPerfect_iff.mpr hDperf
  have hperfR : Group.IsPerfect fD.range := Group.IsPerfect.range fD
  have hH : ⁅fD.range, fD.range⁆ = fD.range := Subgroup.commutator_eq_self
  have hH0 : fD.range ≠ ⊥ := by
    intro hb
    have h1 : fD ⟨x, hxD⟩ = 1 := by
      have hmem : fD ⟨x, hxD⟩ ∈ fD.range := ⟨_, rfl⟩
      rw [hb] at hmem
      exact Subgroup.mem_bot.mp hmem
    apply hxC
    rw [Subgroup.mem_centralizer_iff]
    intro l hl
    exact hψ ⟨x, hDN hxD⟩ h1 l hl
  have hQ : IsPGroup 3 fX.range :=
    IsPGroup.of_surjective hX fX.rangeRestrict (MonoidHom.rangeRestrict_surjective fX)
  have hcomm : ∀ q ∈ fX.range, ∀ h ∈ fD.range, Commute q h := by
    rintro _ ⟨a, rfl⟩ _ ⟨d, rfl⟩
    show fX a * fD d = fD d * fX a
    have hc : (a : Y) * d = d * a := ((Subgroup.mem_centralizer_iff.mp (hXD a.2)) d d.2).symm
    show ψ (Subgroup.inclusion hXN a) * ψ (Subgroup.inclusion hDN d) =
      ψ (Subgroup.inclusion hDN d) * ψ (Subgroup.inclusion hXN a)
    rw [← map_mul, ← map_mul]
    exact congrArg ψ (Subtype.ext hc)
  have hcard := card_le_three_of_perfect_centralizer hH hH0 hQ hcomm
  refine ⟨fun a ha b hb => ?_, fun hXC => ?_⟩
  · have hcm := commutative_of_isPGroup_three_of_card_le hQ hcard
      ⟨fX ⟨a, ha⟩, ⟨_, rfl⟩⟩ ⟨fX ⟨b, hb⟩, ⟨_, rfl⟩⟩
    have hcm' : fX ⟨a, ha⟩ * fX ⟨b, hb⟩ = fX ⟨b, hb⟩ * fX ⟨a, ha⟩ := congrArg Subtype.val hcm
    have h1 : ψ ⟨a * b * a⁻¹ * b⁻¹, hXN (X.mul_mem (X.mul_mem (X.mul_mem ha hb) (X.inv_mem ha))
        (X.inv_mem hb))⟩ = 1 := by
      have hcm'' : ψ (Subgroup.inclusion hXN ⟨a, ha⟩) * ψ (Subgroup.inclusion hXN ⟨b, hb⟩) =
          ψ (Subgroup.inclusion hXN ⟨b, hb⟩) * ψ (Subgroup.inclusion hXN ⟨a, ha⟩) := hcm'
      have e : (⟨a * b * a⁻¹ * b⁻¹, hXN (X.mul_mem (X.mul_mem (X.mul_mem ha hb) (X.inv_mem ha))
          (X.inv_mem hb))⟩ : ↥(Subgroup.normalizer (Lb : Set Y))) =
          Subgroup.inclusion hXN ⟨a, ha⟩ * Subgroup.inclusion hXN ⟨b, hb⟩ *
            (Subgroup.inclusion hXN ⟨a, ha⟩)⁻¹ * (Subgroup.inclusion hXN ⟨b, hb⟩)⁻¹ := rfl
      rw [e, map_mul, map_mul, map_mul, map_inv, map_inv, hcm'']
      group
    rw [Subgroup.mem_centralizer_iff]
    intro l hl
    exact hψ _ h1 l hl
  · have hinj : Function.Injective fX := by
      rw [injective_iff_map_eq_one]
      intro a ha
      have h1 : (a : Y) ∈ X ⊓ Subgroup.centralizer (Lb : Set Y) := by
        refine Subgroup.mem_inf.mpr ⟨a.2, ?_⟩
        rw [Subgroup.mem_centralizer_iff]
        intro l hl
        exact hψ (Subgroup.inclusion hXN a) ha l hl
      rw [hXC, Subgroup.mem_bot] at h1
      exact Subtype.ext h1
    have : Nat.card fX.range = Nat.card X := Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv.symm
    rw [← this]
    exact hcard

end Abstract

section Concrete

variable {G : Type} [Group G] [Finite G] {M S L : Subgroup G}
  {D : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M)} {x : ↥M ⧸ CFSG.pCore 2 ↥M}

theorem nonempty_mulEquiv_alt_ten (h : BlockThreeIbHyp M S L D x) (h6 : NineThreeSix M S L) :
    Nonempty (↥(barM M L) ≃* alternatingGroup (Fin 10)) := by
  obtain ⟨⟨e⟩, -⟩ := nineThreeSix_five h h6
  obtain ⟨-, -, hL, -⟩ := id h
  have hLc := hL.toIsTwoPrimeComponent
  have : Group.IsPerfect ↥(barM M L) := Group.isPerfect_def.mpr hLc.component.2.2.1
  let η : ↥(barM M L) →* alternatingGroup (Fin (8 + 2)) :=
    e.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center ↥(barM M L)))
  have hηs : Function.Surjective η := e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hker : η.ker = Subgroup.center ↥(barM M L) := by
    ext z
    simp only [MonoidHom.mem_ker, η, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom]
    rw [map_eq_one_iff e e.injective, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
  have hodd : Odd (Nat.card η.ker) := by
    rw [hker]; exact odd_card_center_barM hLc
  have h1 := CFSG.Alternating.Multipliers.card_ker_eq_one_of_odd (m := 8) (by norm_num) η hηs
    hker.le hodd
  have hbot : η.ker = ⊥ := Subgroup.eq_bot_of_card_eq _ h1
  exact ⟨MulEquiv.ofBijective η ⟨(MonoidHom.ker_eq_bot_iff η).mp hbot, hηs⟩⟩

theorem le_normalizer_of_blockThreeIbHyp (h : BlockThreeIbHyp M S L D x) :
    D ≤ Subgroup.normalizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M)) := by
  obtain ⟨-, -, -, -, -, -, -, -, -, hDle, -⟩ := id h
  refine hDle.trans (sup_le ?_ (Subgroup.centralizer_le_normalizer _))
  exact (barM_mono inf_le_right : blockPL M S L ≤ barM M L).trans Subgroup.le_normalizer

theorem blockIbRank_nineThreeSix_five (h : BlockThreeIbHyp M S L D x) (h6 : NineThreeSix M S L)
    (E : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M))
    (hEL : E ≤ Subgroup.normalizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M)))
    (_hEP : E ≤ Subgroup.normalizer (blockPL M S L : Set (↥M ⧸ CFSG.pCore 2 ↥M)))
    (hED : E ≤ Subgroup.centralizer (D : Set (↥M ⧸ CFSG.pCore 2 ↥M))) (hEab : IsElemAbelian 3 E)
    (hE9 : Nat.card E = 3 ^ 2) (t : ↥M ⧸ CFSG.pCore 2 ↥M)
    (_ht : t ∈ Subgroup.normalizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M)))
    (_htE : t ∈ Subgroup.normalizer (E : Set (↥M ⧸ CFSG.pCore 2 ↥M)))
    (_htF : ∀ F : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M), F ≤ E → Nat.card F = 3 →
      t ∉ Subgroup.normalizer (F : Set (↥M ⧸ CFSG.pCore 2 ↥M))) :
    E ⊓ Subgroup.centralizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M)) ≠ ⊥ := by
  obtain ⟨ι⟩ := nonempty_mulEquiv_alt_ten h h6
  obtain ⟨-, -, -, -, -, -, -, -, hDp, -, -, -, hxD, -, hxC, -⟩ := id h
  have hE3 : IsPGroup 3 E := fun g => ⟨1, by simpa using Subtype.ext (hEab.2 g g.2)⟩
  intro hbot
  have := (three_group_of_alt_ten ι hDp (le_normalizer_of_blockThreeIbHyp h) hxD hxC hEL hED
    hE3).2 hbot
  rw [hE9] at this
  norm_num at this

theorem blockIbAb_nineThreeSix_five (h : BlockThreeIbHyp M S L D x) (h6 : NineThreeSix M S L)
    (U : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M))
    (hUL : U ≤ Subgroup.normalizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M)))
    (_hUP : U ≤ Subgroup.normalizer (blockPL M S L : Set (↥M ⧸ CFSG.pCore 2 ↥M)))
    (hUD : U ≤ Subgroup.centralizer (D : Set (↥M ⧸ CFSG.pCore 2 ↥M))) (hU3 : IsPGroup 3 U) :
    ∀ a ∈ U, ∀ b ∈ U, a * b * a⁻¹ * b⁻¹ ∈
      Subgroup.centralizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M)) := by
  obtain ⟨ι⟩ := nonempty_mulEquiv_alt_ten h h6
  obtain ⟨-, -, -, -, -, -, -, -, hDp, -, -, -, hxD, -, hxC, -⟩ := id h
  exact (three_group_of_alt_ten ι hDp (le_normalizer_of_blockThreeIbHyp h) hxD hxC hUL hUD hU3).1

theorem blockIbRank_nineThreeSix_or_Seven (h : BlockThreeIbHyp M S L D x)
    (h67 : NineThreeSix M S L ∨ NineThreeSeven M S L)
    (E : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M))
    (hEL : E ≤ Subgroup.normalizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M)))
    (hEP : E ≤ Subgroup.normalizer (blockPL M S L : Set (↥M ⧸ CFSG.pCore 2 ↥M)))
    (hED : E ≤ Subgroup.centralizer (D : Set (↥M ⧸ CFSG.pCore 2 ↥M))) (hEab : IsElemAbelian 3 E)
    (hE9 : Nat.card E = 3 ^ 2) (t : ↥M ⧸ CFSG.pCore 2 ↥M)
    (ht : t ∈ Subgroup.normalizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M)))
    (htE : t ∈ Subgroup.normalizer (E : Set (↥M ⧸ CFSG.pCore 2 ↥M)))
    (htF : ∀ F : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M), F ≤ E → Nat.card F = 3 →
      t ∉ Subgroup.normalizer (F : Set (↥M ⧸ CFSG.pCore 2 ↥M))) :
    E ⊓ Subgroup.centralizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M)) ≠ ⊥ := by
  rcases h67 with h6 | h7
  · exact blockIbRank_nineThreeSix_five h h6 E hEL hEP hED hEab hE9 t ht htE htF
  · exact (false_of_nineThreeSeven h h7).elim

theorem blockIbAb_nineThreeSix_or_Seven (h : BlockThreeIbHyp M S L D x)
    (h67 : NineThreeSix M S L ∨ NineThreeSeven M S L)
    (U : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M))
    (hUL : U ≤ Subgroup.normalizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M)))
    (hUP : U ≤ Subgroup.normalizer (blockPL M S L : Set (↥M ⧸ CFSG.pCore 2 ↥M)))
    (hUD : U ≤ Subgroup.centralizer (D : Set (↥M ⧸ CFSG.pCore 2 ↥M))) (hU3 : IsPGroup 3 U) :
    ∀ a ∈ U, ∀ b ∈ U, a * b * a⁻¹ * b⁻¹ ∈
      Subgroup.centralizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M)) := by
  rcases h67 with h6 | h7
  · exact blockIbAb_nineThreeSix_five h h6 U hUL hUP hUD hU3
  · exact (false_of_nineThreeSeven h h7).elim

end Concrete

end CFSG.HardMathSupport.Curtis.UnitaryLevi
