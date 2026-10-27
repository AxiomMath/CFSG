module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X7SecP3
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X7bTop

public section

namespace CFSG.QuasithinUnique.Setup.X7Sec

open scoped MatrixGroups Matrix IsMulCommutative

open CFSG.QuasithinUnique.Setup.Offender CFSG.QuasithinUnique.Setup.Layer
  CFSG.QuasithinUnique.Setup.X3

section Core

variable {N : Type} [Group N] [Finite N] {W : Type} [AddCommGroup W] [Module (ZMod 2) W] [Finite W]

theorem data_core (ρ : N →* (W ≃ₗ[ZMod 2] W)) (hρ : Function.Injective ρ) (L : Subgroup N)
    [L.Normal] (hLq : CFSG.IsQuasisimple ↥L) (hZ : Subgroup.center ↥L = ⊥) {A : Subgroup N}
    (hAne : A ≠ ⊥) (hAel : CFSG.IsElementaryAbelian 2 ↥A) (hLA : ⁅L, A⁆ = L)
    (hoff : Nat.card W ≤ weight ρ A)
    (hstrict : ∀ D : Subgroup N, ⊥ < D → D < A → weight ρ D < weight ρ A) :
    ∃ (U : Type) (_ : AddCommGroup U) (_ : Module (ZMod 2) U) (_ : Finite U)
      (ρL : ↥L →* (U ≃ₗ[ZMod 2] U)) (A' : Subgroup (U ≃ₗ[ZMod 2] U)),
      Function.Injective ρL ∧ (∀ a ∈ A', ∀ l : ↥L, ∃ l' : ↥L, a * ρL l * a⁻¹ = ρL l') ∧
      CFSG.IsElementaryAbelian 2 ↥A' ∧ A' ≠ ⊥ ∧ X7b.SimpleSummandsStable ρL A' ∧
      Nat.card U ≤ Nat.card A' * Nat.card {u : U // ∀ a ∈ A', a u = u} ∧
      ∀ n : N, ∃ b : U ≃ₗ[ZMod 2] U, ∀ l : ↥L, b * ρL l * b⁻¹ = ρL (MulAut.conjNormal n l) := by
  classical
  have hA2 : ∀ a : N, a ∈ A → a * a = 1 := fun a ha => sq_of_mem ha
  obtain ⟨B, Z, hos⟩ := orbitSemisimpleSection ρ L A hρ hLq hAne hAel hLA hoff hstrict
  obtain ⟨hMA, hoffM⟩ := hos.offender_M
  obtain ⟨𝒰, h𝒰, hfam, hsup⟩ := hos.family
  set Mv : Submodule (ZMod 2) (W ⧸ fixSub ρ L) := B.map (fixSub ρ L).mkQ with hMv
  have hUM : ∀ U ∈ 𝒰, U ≤ Mv := fun U hU => by
    rw [← hsup]
    exact Finset.le_sup (f := id) hU
  have hMN : ∀ n : N, ∀ w ∈ Mv, cvAct ρ L n w ∈ Mv := hos.invariant_M
  have h𝒰ne : 𝒰.Nonempty := by
    by_contra hemp
    rw [Finset.not_nonempty_iff_eq_empty] at hemp
    apply hos.M_ne_bot
    intro b hb
    have hmem : (fixSub ρ L).mkQ b ∈ Mv := ⟨b, hb, rfl⟩
    rw [← hsup, hemp, Finset.sup_empty, Submodule.mem_bot] at hmem
    exact (Submodule.Quotient.mk_eq_zero _).1 hmem
  obtain ⟨U₀, h0⟩ := h𝒰ne
  let bN : N →* (↥Mv ≃ₗ[ZMod 2] ↥Mv) := resHom (cvAct ρ L) Mv hMN
  let ρL : ↥L →* (↥Mv ≃ₗ[ZMod 2] ↥Mv) := bN.comp L.subtype
  have hker : (resSub (cvAct ρ L) A Mv hMA).range = A.map bN := by
    ext g
    constructor
    · rintro ⟨a, rfl⟩
      exact ⟨a, a.2, rfl⟩
    · rintro ⟨a, ha, rfl⟩
      exact ⟨⟨a, ha⟩, rfl⟩
  have hUL : ∀ U ∈ 𝒰, IsNontrivialLSimple (cvAct ρ L) L U := fun U hU => (h𝒰 U hU).1
  refine ⟨↥Mv, inferInstance, inferInstance, inferInstance, ρL, A.map bN, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_⟩
  ·
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    have hKn : (ρL.ker).Normal := MonoidHom.normal_ker ρL
    rcases CFSG.LocalCores.quasisimple_normal_subgroups hLq hKn with htop | hle
    · exfalso
      apply (hUL U₀ h0).2
      intro u hu l hl
      have hmem : (⟨l, hl⟩ : ↥L) ∈ ρL.ker := by rw [htop]; trivial
      have h1 := congrArg (fun g : ↥Mv ≃ₗ[ZMod 2] ↥Mv => g ⟨u, hUM U₀ h0 hu⟩)
        (MonoidHom.mem_ker.1 hmem)
      exact congrArg Subtype.val h1
    · exact hle.trans (le_of_eq hZ)
  ·
    rintro _ ⟨a, ha, rfl⟩ l
    refine ⟨⟨a * (l : N) * a⁻¹, Subgroup.Normal.conj_mem inferInstance _ l.2 a⟩, ?_⟩
    show bN a * bN (l : N) * (bN a)⁻¹ = bN (a * (l : N) * a⁻¹)
    rw [map_mul, map_mul, map_inv]
  ·
    refine isElementaryAbelian_two_of_forall' _ ?_ ?_
    · rintro _ ⟨a, ha, rfl⟩ _ ⟨c, hc, rfl⟩
      rw [← map_mul, ← map_mul, comm_of_mem ha hc]
    · rintro _ ⟨a, ha, rfl⟩
      rw [← map_mul, hA2 a ha, map_one]
  ·
    intro hbot
    obtain ⟨a₀, ha₀, ha₀c⟩ : ∃ a ∈ A, a ∉ Subgroup.centralizer (L : Set N) := by
      by_contra hcon
      push Not at hcon
      exact hos.not_central hcon
    have hmem : bN a₀ ∈ A.map bN := ⟨a₀, ha₀, rfl⟩
    rw [hbot, Subgroup.mem_bot] at hmem
    apply ha₀c
    refine (hos.ker_M a₀ ha₀).1 fun m hm => ?_
    have h1 := congrArg (fun g : ↥Mv ≃ₗ[ZMod 2] ↥Mv => g ⟨m, hm⟩) hmem
    exact congrArg Subtype.val h1
  ·
    obtain ⟨s, hs𝒰, hsind, hssup⟩ := exists_supIndep_subset (σ := cvAct ρ L) (L := L) 𝒰
      (fun U hU => (hUL U hU).1)
    have hsM : ∀ U ∈ s, U ≤ Mv := fun U hU => hUM U (hs𝒰 hU)
    refine ⟨{U // U ∈ s}, fun i => (i.1).comap Mv.subtype, ?_, ?_, fun i => ?_⟩
    ·
      have hind := hsind.independent
      intro i
      rw [Submodule.disjoint_def]
      intro x hxi hxj
      have hx1 : (x : W ⧸ fixSub ρ L) ∈ i.1 := hxi
      have hx2 : (x : W ⧸ fixSub ρ L) ∈ ⨆ j : {U // U ∈ s}, ⨆ (_ : j ≠ i), (j.1 : Submodule _ _) := by
        have hmap : Submodule.map Mv.subtype (⨆ j : {U // U ∈ s}, ⨆ (_ : j ≠ i),
            (j.1).comap Mv.subtype) ≤ ⨆ j : {U // U ∈ s}, ⨆ (_ : j ≠ i), (j.1 : Submodule _ _) := by
          rw [Submodule.map_iSup]
          refine iSup_mono fun j => ?_
          rw [Submodule.map_iSup]
          refine iSup_mono fun hj => ?_
          rw [Submodule.map_comap_subtype]
          exact inf_le_right
        exact hmap ⟨x, hxj, rfl⟩
      have hz := Submodule.disjoint_def.1 (hind i) _ hx1 hx2
      exact Subtype.ext hz
    ·
      have hiSup : (⨆ i : {U // U ∈ s}, (i.1 : Submodule (ZMod 2) (W ⧸ fixSub ρ L))) =
          s.sup id := by
        refine le_antisymm (iSup_le fun i => Finset.le_sup (f := id) i.2) ?_
        exact Finset.sup_le fun U hU =>
          le_iSup (fun i : {U // U ∈ s} => (i.1 : Submodule (ZMod 2) (W ⧸ fixSub ρ L))) ⟨U, hU⟩
      apply Submodule.map_injective_of_injective Mv.injective_subtype
      rw [Submodule.map_iSup, Submodule.map_subtype_top]
      have hcomap : ∀ i : {U // U ∈ s}, Submodule.map Mv.subtype ((i.1).comap Mv.subtype) = i.1 :=
        fun i => by
          rw [Submodule.map_comap_subtype]
          exact inf_eq_right.2 (hsM i.1 i.2)
      simp_rw [hcomap]
      rw [hiSup, hssup, hsup]
    ·
      have hUi := hUL i.1 (hs𝒰 i.2)
      have hAi := (h𝒰 i.1 (hs𝒰 i.2)).2
      have hile : i.1 ≤ Mv := hsM i.1 i.2
      refine ⟨?_, ?_, ?_, ?_, ?_⟩
      · intro hbot
        have hbot' : (i.1).comap Mv.subtype = ⊥ := hbot
        apply hUi.1.2.1
        rw [eq_bot_iff]
        intro u hu
        have hmem : (⟨u, hile hu⟩ : ↥Mv) ∈ (i.1).comap Mv.subtype := hu
        rw [hbot', Submodule.mem_bot] at hmem
        exact (Submodule.mem_bot _).2 (congrArg Subtype.val hmem)
      · obtain ⟨u, hu, hnu⟩ := IsConcreteLE.not_le_iff_exists.1 hUi.2
        have hnu' : ¬ ∀ l ∈ L, cvAct ρ L l u = u := hnu
        push Not at hnu'
        obtain ⟨l, hl, hlu⟩ := hnu'
        refine ⟨⟨u, hile hu⟩, hu, ⟨l, hl⟩, fun h => hlu ?_⟩
        exact congrArg Subtype.val h
      · intro g x hx
        exact hUi.1.1 g g.2 x hx
      · intro W' hW'le hW'inv
        have hinv : Offender.IsInvariant (cvAct ρ L) L (W'.map Mv.subtype) := by
          rintro l hl _ ⟨x, hx, rfl⟩
          exact ⟨ρL ⟨l, hl⟩ x, hW'inv ⟨l, hl⟩ x hx, rfl⟩
        have hle : W'.map Mv.subtype ≤ i.1 := by
          rintro _ ⟨x, hx, rfl⟩
          exact hW'le hx
        have hcomap' : Submodule.map Mv.subtype ((i.1).comap Mv.subtype) = i.1 := by
          rw [Submodule.map_comap_subtype]
          exact inf_eq_right.2 hile
        rcases hUi.1.2.2 _ hinv hle with hbot | hfull
        · left
          apply Submodule.map_injective_of_injective Mv.injective_subtype
          rw [hbot, Submodule.map_bot]
        · right
          apply Submodule.map_injective_of_injective Mv.injective_subtype
          rw [hfull, hcomap']
      · rintro _ ⟨a, ha, rfl⟩ x hx
        exact hAi a ha x hx
  ·
    have h1 : Nat.card ↥(fixSub (MonoidHom.id (↥Mv ≃ₗ[ZMod 2] ↥Mv))
        (resSub (cvAct ρ L) A Mv hMA).range) =
        Nat.card {u : ↥Mv // ∀ a ∈ (resSub (cvAct ρ L) A Mv hMA).range, a u = u} :=
      Nat.card_congr (Equiv.subtypeEquivRight fun u => Iff.rfl)
    unfold weight at hoffM
    rw [h1] at hoffM
    rw [← hker]
    exact hoffM
  ·
    intro n
    refine ⟨bN n, fun l => ?_⟩
    show bN n * bN (l : N) * (bN n)⁻¹ = bN ((MulAut.conjNormal n l : ↥L) : N)
    rw [MulAut.conjNormal_apply, map_mul, map_mul, map_inv]

end Core

end CFSG.QuasithinUnique.Setup.X7Sec
