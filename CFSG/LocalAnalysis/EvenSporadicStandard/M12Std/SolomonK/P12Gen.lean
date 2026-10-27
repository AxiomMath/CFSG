module

public import CFSG.LocalAnalysis.EvenSporadicStandard.M12Std.SolomonK.Defs

public section

namespace CFSG.EvenSporadicStandard.M12Std.SolomonK

open Subgroup

theorem ElemFactsIn.of_mulEquiv {G G' : Type} [Group G] [Group G'] {Q : Subgroup G}
    {Q' : Subgroup G'} (e : Q ≃* Q') (h : ElemFactsIn Q') : ElemFactsIn Q := by
  obtain ⟨hcard, ⟨g', hg'mem, hg'ord⟩, E', hE'le, hE'sq, hE'card, hE'max⟩ := h
  refine ⟨?_, ?_, ?_⟩
  · rw [Nat.card_congr e.toEquiv, hcard]
  · refine ⟨((e.symm ⟨g', hg'mem⟩ : Q) : G), (e.symm ⟨g', hg'mem⟩).2, ?_⟩
    rw [Subgroup.orderOf_coe, MulEquiv.orderOf_eq, Subgroup.orderOf_mk]
    exact hg'ord
  · refine ⟨((E'.subgroupOf Q').map e.symm.toMonoidHom).map Q.subtype, ?_, ?_, ?_, ?_⟩
    · exact Subgroup.map_subtype_le _
    · intro x hx
      obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hx
      obtain ⟨z, hz, rfl⟩ := Subgroup.mem_map.mp hy
      have hz1 : z * z = 1 :=
        Subtype.ext (hE'sq (z : Q') (Subgroup.mem_subgroupOf.mp hz))
      have h1 : e.symm z * e.symm z = 1 := by rw [← map_mul, hz1, map_one]
      simpa using congrArg (Subtype.val : Q → G) h1
    · rw [Subgroup.card_map_of_injective Q.subtype_injective,
        Subgroup.card_map_of_injective e.symm.injective,
        Nat.card_congr (Subgroup.subgroupOfEquivOfLe hE'le).toEquiv, hE'card]
    · intro A hAQ hAsq hAcard
      set A'' : Subgroup Q' := (A.subgroupOf Q).map e.toMonoidHom with hA''
      set A' : Subgroup G' := A''.map Q'.subtype with hA'
      have hA'le : A' ≤ Q' := Subgroup.map_subtype_le A''
      have hA'card : Nat.card A' = Nat.card A := by
        rw [hA', Subgroup.card_map_of_injective Q'.subtype_injective, hA'',
          Subgroup.card_map_of_injective e.injective,
          Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAQ).toEquiv]
      have hA'sq : ∀ x ∈ A', x * x = 1 := by
        intro x hx
        rw [hA', Subgroup.mem_map] at hx
        obtain ⟨y, hy, rfl⟩ := hx
        rw [hA'', Subgroup.mem_map] at hy
        obtain ⟨a, ha, rfl⟩ := hy
        have ha1 : a * a = 1 :=
          Subtype.ext (hAsq (a : Q) (Subgroup.mem_subgroupOf.mp ha))
        have h1 : e a * e a = 1 := by rw [← map_mul, ha1, map_one]
        simpa using congrArg (Subtype.val : Q' → G') h1
      have hA'E' : A' ≤ E' := hE'max A' hA'le hA'sq (hAcard.trans hA'card.ge)
      intro a ha
      have haQ : a ∈ Q := hAQ ha
      have ha'' : e ⟨a, haQ⟩ ∈ A'' :=
        Subgroup.mem_map.mpr ⟨⟨a, haQ⟩, Subgroup.mem_subgroupOf.mpr ha, rfl⟩
      have ha' : ((e ⟨a, haQ⟩ : Q') : G') ∈ A' := Subgroup.mem_map.mpr ⟨_, ha'', rfl⟩
      have hE'mem : ((e ⟨a, haQ⟩ : Q') : G') ∈ E' := hA'E' ha'
      have hmem : e ⟨a, haQ⟩ ∈ E'.subgroupOf Q' := Subgroup.mem_subgroupOf.mpr hE'mem
      have h2 : (e.symm (e ⟨a, haQ⟩) : Q) ∈
          (E'.subgroupOf Q').map e.symm.toMonoidHom :=
        Subgroup.mem_map.mpr ⟨_, hmem, rfl⟩
      have h3 : ((e.symm (e ⟨a, haQ⟩) : Q) : G) ∈
          ((E'.subgroupOf Q').map e.symm.toMonoidHom).map Q.subtype :=
        Subgroup.mem_map.mpr ⟨_, h2, rfl⟩
      simpa using h3

theorem sylowData_elemFactsIn {G : Type} [Group G] [Finite G]
    (h2 : (Nat.card G).factorization 2 = 9) (hD : SylowData G) (S : Sylow 2 G) :
    ElemFactsIn (S : Subgroup G) := by
  obtain ⟨P, E, _, hP, hEP, hEsq, hEcard, hg, hmax, _, _⟩ := hD
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hPfac : ElemFactsIn P := ⟨hP, hg, E, hEP, hEsq, hEcard, hmax⟩
  let P₀ : Sylow 2 G := Sylow.ofCard P (by rw [hP, h2])
  haveI : Finite (Sylow 2 G) := Sylow.finite_of_finiteIndex P₀
  exact ElemFactsIn.of_mulEquiv (Sylow.equiv P₀ S).symm hPfac

theorem sylowData_nine {G : Type} [Group G] [Finite G]
    (h2 : (Nat.card G).factorization 2 = 9) (hD : SylowData G) :
    ∀ E : Subgroup G, (∀ x ∈ E, x * x = 1) → Nat.card E = 2 ^ 6 →
      9 ∣ Nat.card (normalizer (E : Set G)) := by
  obtain ⟨P, E₀, H, hP, _, _, hE₀card, _, hmax, hHnorm, hHcard⟩ := hD
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro E hEsq hEcard
  have hE2 : IsPGroup 2 E := IsPGroup.of_card (n := 6) hEcard
  obtain ⟨S, hES⟩ := hE2.exists_le_sylow
  let P₀ : Sylow 2 G := Sylow.ofCard P (by rw [hP, h2])
  haveI : Finite (Sylow 2 G) := Sylow.finite_of_finiteIndex P₀
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (M := G) P₀ S
  let f : G →* G := MulDistribMulAction.toMonoidEnd (MulAut G) G (MulAut.conj g)
  let f' : G →* G :=
    MulDistribMulAction.toMonoidEnd (MulAut G) G (MulAut.conj g)⁻¹
  have hS : (S : Subgroup G) = P.map f := by
    rw [← hg, Sylow.coe_subgroup_smul, Subgroup.pointwise_smul_def]
    rfl
  have hf_inj : Function.Injective f := by
    intro a b hab
    exact (MulAut.conj g).injective (by simpa [f, MulAut.smul_def] using hab)
  have hf'_inj : Function.Injective f' := by
    intro a b hab
    exact (MulAut.conj g)⁻¹.injective (by simpa [f', MulAut.smul_def] using hab)
  have hcomp : f.comp f' = MonoidHom.id G := by
    ext x
    simp only [MonoidHom.comp_apply, MonoidHom.id_apply, f, f', MulAut.smul_def,
      MulAut.inv_apply]
    exact MulEquiv.apply_symm_apply (MulAut.conj g) x
  have hcomp' : f'.comp f = MonoidHom.id G := by
    ext x
    simp only [MonoidHom.comp_apply, MonoidHom.id_apply, f, f', MulAut.smul_def,
      MulAut.inv_apply]
    exact MulEquiv.symm_apply_apply (MulAut.conj g) x
  let A : Subgroup G := E.map f'
  have hAP : A ≤ P := by
    change E.map f' ≤ P
    have h1 : E.map f' ≤ (P.map f).map f' :=
      Subgroup.map_mono (f := f') (hS ▸ hES)
    rwa [Subgroup.map_map, hcomp', Subgroup.map_id] at h1
  have hA_sq : ∀ x ∈ A, x * x = 1 := by
    intro x hx
    have hx' : x ∈ E.map f' := hx
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hx'
    rw [← map_mul, hEsq y hy, map_one]
  have hA_card : Nat.card A = 2 ^ 6 := by
    change Nat.card (E.map f') = 2 ^ 6
    rw [Subgroup.card_map_of_injective hf'_inj, hEcard]
  have hAle : A ≤ E₀ := hmax A hAP hA_sq hA_card.ge
  have hAeq : A = E₀ :=
    Subgroup.eq_of_le_of_card_ge hAle (by rw [hE₀card, hA_card])
  have hEeq : E = E₀.map f := by
    have h := congrArg (fun K : Subgroup G => K.map f) hAeq
    change (E.map f').map f = E₀.map f at h
    rw [Subgroup.map_map, hcomp, Subgroup.map_id] at h
    exact h
  let H' : Subgroup G := H.map f
  have hH'le : H' ≤ normalizer (E : Set G) := by
    change H.map f ≤ normalizer (E : Set G)
    rw [hEeq]
    exact (Subgroup.map_mono (f := f) hHnorm).trans (Subgroup.le_normalizer_map f)
  have hH'card : Nat.card H' = 9 := by
    change Nat.card (H.map f) = 9
    rw [Subgroup.card_map_of_injective hf_inj, hHcard]
  have hdvd : Nat.card H' ∣ Nat.card (normalizer (E : Set G)) :=
    Subgroup.card_dvd_of_le hH'le
  rwa [hH'card] at hdvd

private theorem factorization_half_factorial_twelve :
    ((12 : ℕ).factorial / 2).factorization 2 = 9 := by
  have h : (12 : ℕ).factorial / 2 = 2 ^ 9 * 467775 := by norm_num
  rw [h, Nat.factorization_mul (by norm_num) (by norm_num), Finsupp.add_apply,
    Nat.factorization_pow_self Nat.prime_two,
    Nat.factorization_eq_zero_of_not_dvd (by norm_num : ¬ 2 ∣ 467775)]

private theorem factorization_half_factorial_thirteen :
    ((13 : ℕ).factorial / 2).factorization 2 = 9 := by
  have h : (13 : ℕ).factorial / 2 = 2 ^ 9 * 6081075 := by norm_num
  rw [h, Nat.factorization_mul (by norm_num) (by norm_num), Finsupp.add_apply,
    Nat.factorization_pow_self Nat.prime_two,
    Nat.factorization_eq_zero_of_not_dvd (by norm_num : ¬ 2 ∣ 6081075)]

theorem card_alt_two_part {n : ℕ} (hn : n = 12 ∨ n = 13) :
    (Nat.card (alternatingGroup (Fin n))).factorization 2 = 9 := by
  rcases hn with rfl | rfl
  · rw [nat_card_alternatingGroup, Nat.card_eq_fintype_card, Fintype.card_fin]
    exact factorization_half_factorial_twelve
  · rw [nat_card_alternatingGroup, Nat.card_eq_fintype_card, Fintype.card_fin]
    exact factorization_half_factorial_thirteen

end CFSG.EvenSporadicStandard.M12Std.SolomonK
