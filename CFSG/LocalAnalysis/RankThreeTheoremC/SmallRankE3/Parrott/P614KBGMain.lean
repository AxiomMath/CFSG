module

public import CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.Parrott.P614Defs
public import CFSG.Goldschmidt.Steps.G3aBorel
import CFSG.LocalAnalysis.QuasithinUnique.RankOneRecognitionCover

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.Parrott.P614

open Subgroup

namespace P614KBG

open CFSG.Goldschmidt.G3a

variable {X : Type} [Group X] [Finite X]

theorem exists_ne_le_normalizer {T : Sylow 2 X} {D : Subgroup X} (h : BorelSetup T D)
    {P : Subgroup X} (hPT : P ≤ normalizer ((T : Subgroup X) : Set X))
    (hp : (Nat.card P).Prime) (hodd : Odd (Nat.card P)) :
    ∃ T₂ : Sylow 2 X, T₂ ≠ T ∧ P ≤ normalizer ((T₂ : Subgroup X) : Set X) := by
  haveI : Fact (Nat.card P).Prime := ⟨hp⟩
  have hPp : IsPGroup (Nat.card P) P := IsPGroup.of_card (n := 1) (pow_one _).symm
  by_contra hcon
  push Not at hcon
  have hfix : MulAction.fixedPoints P (Sylow 2 X) = {T} := by
    ext S
    rw [Subgroup.sylow_mem_fixedPoints_iff, Set.mem_singleton_iff]
    refine ⟨fun hS => ?_, ?_⟩
    · by_contra hST
      exact hcon S hST hS
    · rintro rfl
      exact hPT
  have hone : Nat.card (MulAction.fixedPoints P (Sylow 2 X)) = 1 := by
    rw [hfix]
    exact Nat.card_unique
  have hmod := hPp.card_modEq_card_fixedPoints (Sylow 2 X)
  rw [h.card, hone] at hmod
  have hdvd : Nat.card P ∣ Nat.card (T : Subgroup X) := by
    have h1 := (Nat.modEq_iff_dvd' (by omega)).mp hmod.symm
    simpa using h1
  obtain ⟨n, hn⟩ := T.isPGroup'.exists_card_eq
  rw [hn] at hdvd
  have h2 : Nat.card P = 2 :=
    (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp (hp.dvd_of_dvd_pow hdvd)
  rw [h2] at hodd
  exact Nat.not_even_iff_odd.mpr hodd even_two

theorem isCyclic_normalizer_inf {T : Sylow 2 X} {D : Subgroup X} (h : BorelSetup T D)
    {T₂ : Sylow 2 X} (hne : T₂ ≠ T) :
    IsCyclic ↥(normalizer ((T : Subgroup X) : Set X) ⊓
      normalizer ((T₂ : Subgroup X) : Set X)) := by
  obtain ⟨T', hT'ne, hDT'⟩ := h.exists_fixed
  obtain ⟨t, ht, rfl⟩ := h.exists_smul hT'ne hne
  have htN : t ∈ normalizer ((T : Subgroup X) : Set X) := Subgroup.le_normalizer ht
  have hmem : ∀ e ∈ normalizer ((T : Subgroup X) : Set X) ⊓
      normalizer (((t • T' : Sylow 2 X) : Subgroup X) : Set X), t⁻¹ * e * t ∈ D := by
    intro e he
    obtain ⟨he1, he2⟩ := Subgroup.mem_inf.mp he
    rw [← h.normalizer_inf_eq hT'ne hDT']
    refine Subgroup.mem_inf.mpr ⟨mul_mem (mul_mem (inv_mem htN) he1) htN, ?_⟩
    have he2' : e • (t • T') = t • T' := Sylow.smul_eq_iff_mem_normalizer.mpr he2
    have hfix : (t⁻¹ * e * t) • T' = T' := by
      rw [mul_smul, mul_smul, he2', inv_smul_smul]
    exact Sylow.smul_eq_iff_mem_normalizer.mp hfix
  have : IsCyclic D := h.cyc
  let f : ↥(normalizer ((T : Subgroup X) : Set X) ⊓
      normalizer (((t • T' : Sylow 2 X) : Subgroup X) : Set X)) →* D :=
    MonoidHom.mk' (fun e => ⟨t⁻¹ * e * t, hmem e e.2⟩) (fun a b => Subtype.ext
      (show t⁻¹ * ((a : X) * b) * t = (t⁻¹ * a * t) * (t⁻¹ * b * t) by group))
  refine isCyclic_of_injective f (fun a b hab => Subtype.ext ?_)
  have h1 : t⁻¹ * (a : X) * t = t⁻¹ * (b : X) * t := congrArg Subtype.val hab
  simpa using h1

theorem exists_swap {T : Sylow 2 X} {D : Subgroup X} (h : BorelSetup T D) {T₂ : Sylow 2 X}
    (hne : T₂ ≠ T) : ∃ w : X, w • T = T₂ ∧ w • T₂ = T := by
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq X T₂ T
  have hgT : g • T ≠ T := fun h' => hne (smul_left_cancel g (hg.trans h'.symm))
  obtain ⟨s, hs, hsT⟩ := h.exists_smul hgT hne
  refine ⟨s * g, by rw [mul_smul, hsT], ?_⟩
  rw [mul_smul, hg]
  exact Sylow.smul_eq_iff_mem_normalizer.mpr (Subgroup.le_normalizer hs)

omit [Finite X] in
theorem conj_mem_normalizer_inf {T T₂ : Sylow 2 X} {w : X} (hwT : w • T = T₂)
    (hwT₂ : w • T₂ = T) {e : X}
    (he : e ∈ normalizer ((T : Subgroup X) : Set X) ⊓ normalizer ((T₂ : Subgroup X) : Set X)) :
    w * e * w⁻¹ ∈
      normalizer ((T : Subgroup X) : Set X) ⊓ normalizer ((T₂ : Subgroup X) : Set X) := by
  obtain ⟨he1, he2⟩ := Subgroup.mem_inf.mp he
  have h1 : e • T = T := Sylow.smul_eq_iff_mem_normalizer.mpr he1
  have h2 : e • T₂ = T₂ := Sylow.smul_eq_iff_mem_normalizer.mpr he2
  have hiT : w⁻¹ • T = T₂ := inv_smul_eq_iff.mpr hwT₂.symm
  have hiT₂ : w⁻¹ • T₂ = T := inv_smul_eq_iff.mpr hwT.symm
  have k1 : (w * e * w⁻¹) • T = T := by rw [mul_smul, mul_smul, hiT, h2, hwT₂]
  have k2 : (w * e * w⁻¹) • T₂ = T₂ := by rw [mul_smul, mul_smul, hiT₂, h1, hwT]
  exact Subgroup.mem_inf.mpr ⟨Sylow.smul_eq_iff_mem_normalizer.mp k1,
    Sylow.smul_eq_iff_mem_normalizer.mp k2⟩

omit [Finite X] in
theorem conj_mem_of_isCyclic {E P : Subgroup X} [IsCyclic E] (hPE : P ≤ E) {w : X}
    (hw : ∀ e ∈ E, w * e * w⁻¹ ∈ E) {x : X} (hx : x ∈ P) : w * x * w⁻¹ ∈ P := by
  let σ : E →* E := MonoidHom.mk' (fun e => ⟨w * e * w⁻¹, hw e e.2⟩) (fun a b => Subtype.ext
    (show w * ((a : X) * b) * w⁻¹ = (w * a * w⁻¹) * (w * b * w⁻¹) by group))
  obtain ⟨m, hm⟩ := σ.map_cyclic
  have h1 : w * x * w⁻¹ = x ^ m := congrArg Subtype.val (hm ⟨x, hPE hx⟩)
  rw [h1]
  exact P.zpow_mem hx m

theorem normalizer_sup_eq_top [IsSimpleGroup X] {T : Sylow 2 X} {D : Subgroup X}
    (h : BorelSetup T D) {P : Subgroup X} (hPT : P ≤ normalizer ((T : Subgroup X) : Set X))
    (hp : (Nat.card P).Prime) (hodd : Odd (Nat.card P)) :
    normalizer (P : Set X) ⊔ (T : Subgroup X) = ⊤ := by
  obtain ⟨T₂, hne, hPT₂⟩ := exists_ne_le_normalizer h hPT hp hodd
  haveI := isCyclic_normalizer_inf h hne
  obtain ⟨w, hwT, hwT₂⟩ := exists_swap h hne
  have hPE : P ≤ normalizer ((T : Subgroup X) : Set X) ⊓
      normalizer ((T₂ : Subgroup X) : Set X) := le_inf hPT hPT₂
  have hiT : w⁻¹ • T = T₂ := inv_smul_eq_iff.mpr hwT₂.symm
  have hiT₂ : w⁻¹ • T₂ = T := inv_smul_eq_iff.mpr hwT.symm
  have hwP : w ∈ normalizer (P : Set X) := by
    refine Subgroup.mem_normalizer_iff.mpr fun x => ⟨fun hx =>
      conj_mem_of_isCyclic hPE (fun e he => conj_mem_normalizer_inf hwT hwT₂ he) hx,
      fun hx => ?_⟩
    have h1 := conj_mem_of_isCyclic hPE (fun e he => conj_mem_normalizer_inf hiT hiT₂ he) hx
    have e1 : w⁻¹ * (w * x * w⁻¹) * w⁻¹⁻¹ = x := by group
    rwa [e1] at h1
  by_contra hL
  have hle := h.le_normalizer_of_le
    (le_sup_right : (T : Subgroup X) ≤ normalizer (P : Set X) ⊔ T) hL
  have hwN : w ∈ normalizer ((T : Subgroup X) : Set X) := hle (Subgroup.mem_sup_left hwP)
  exact hne (hwT.symm.trans (Sylow.smul_eq_iff_mem_normalizer.mpr hwN))

end P614KBG

section Holds


theorem kFactBenderGen_holds : KFactBenderGen := by
  intro K _ _ hK T P hT hPT hp hodd
  have hcard : Nat.card T = 2 ^ (Nat.card K).factorization 2 := by
    rw [hT.card_eq, Subgroup.card_top]
  obtain ⟨S, rfl⟩ : ∃ S : Sylow 2 K, (S : Subgroup K) = T :=
    ⟨Sylow.ofCard T hcard, Sylow.coe_ofCard _ _⟩
  haveI : IsSimpleGroup K :=
    CFSG.QuasithinUnique.RankOneRecog.isSimpleGroup_of_fusionIsBenderGroup hK
  obtain ⟨D, hD⟩ := CFSG.Goldschmidt.G3a.exists_borelSetup hK S
  exact P614KBG.normalizer_sup_eq_top hD hPT hp hodd

end Holds

end CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.Parrott.P614
