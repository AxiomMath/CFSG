module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Zassenhaus.PartA.S7Abs
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Zassenhaus.PartA.S7SwapMain
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Zassenhaus.PartA.S7SwapT

public section

namespace CFSG.EvenSporadicStandard.HSStd.Zassenhaus.PartA

open Subgroup CFSG.EvenSporadicStandard.HSStd CFSG.Blueprint
open scoped commutatorElement

local notation "A6" => alternatingGroup (Fin 6)

@[expose] def LieModelSimpleU43 : Prop :=
  ∀ (N : Type) [Group N], LieModel N .PSU 4 3 1 → IsSimpleGroup N

theorem s7_abstract
    (hHs : Harris311) (hU : U43Config) (hL : HarrisL39L43NoD8) (hCov : U43CoverOrbit)
    (hSimp : LieModelSimpleU43)
    {T X : Type} [Group T] [Finite T] [Group X] [Finite X] (κ : T →* X)
    (hκ : Function.Surjective κ) (hKT : CFSG.SectionRank.IsKGroupCat T)
    (hO : Open.fusionOddCore X = ⊥) {t : T} (ht2 : t * t = 1)
    (ht : orderOf (κ t) = 2)
    (e : ↥(centralizer ({κ t} : Set X)) ≃* Multiplicative (ZMod 2) × MulAut A6)
    {y c k : T} (hy3 : orderOf y = 3) (hS : SigmaConfig (κ t) (κ y) (κ c) (κ k))
    (F A : Subgroup T) [F.Normal] [A.Normal] (hker : κ.ker ≤ F ⊔ A) (hF : Nat.card F ≤ 4)
    (hFA : F ≤ centralizer (A : Set T)) (hAab : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a)
    (hinv : ∀ a ∈ A, t * a * t⁻¹ = a⁻¹)
    (J : Subgroup T) (hJ : ⁅J, J⁆ = J) (hyJ : y ∈ J)
    (hJX : J.map κ ≤ centralizerDerived (κ t))
    (hB : ∃ D₁ : Subgroup X, D₁ ≤ centralizer
        ({κ y, κ c, κ t * κ c * (κ t)⁻¹, κ k, κ t * κ k * (κ t)⁻¹} : Set X) ∧
      Nat.card ↥((centralizer ({y} : Set T)).map κ) ≤ Nat.card D₁ * 72) :
    ∃ E : Subgroup T, E.Normal ∧ ⁅E, E⁆ = E ∧ J ≤ E ∧ E ≤ centralizer (F : Set T) ∧
      E ≤ centralizer (A : Set T) ∧ (∀ g ∈ E, t * g * t⁻¹ ∈ E) ∧
      ∃ f : ↥E →* A6 × A6, Function.Surjective f ∧ f.ker ≤ center ↥E ∧
        ∀ (x : ↥E) (hx : t * (x : T) * t⁻¹ ∈ E), (f x).2 = 1 →
          (f ⟨t * (x : T) * t⁻¹, hx⟩).1 = 1 := by
  obtain ⟨hB0, hcases⟩ := harris_cases hHs hU hL (hKT.of_surjective κ hκ) hO ht e hS
  obtain ⟨N, hNdef⟩ : ∃ N : Subgroup X, N = normalClosureOf (centralizerDerived (κ t)) :=
    ⟨_, rfl⟩
  rw [← hNdef] at hB0 hcases
  haveI hNn : N.Normal := by
    rw [hNdef]; unfold normalClosureOf; infer_instance
  have hLN : centralizerDerived (κ t) ≤ N := by
    rw [hNdef]; exact Subgroup.subset_normalClosure
  have hNperf : ⁅N, N⁆ = N := by
    apply le_antisymm (commutator_le_self_of_subgroup N)
    have h1 : normalClosureOf (centralizerDerived (κ t)) ≤ ⁅N, N⁆ := by
      unfold normalClosureOf
      apply Subgroup.normalClosure_le_normal
      intro x hx
      have hx' : x ∈ ⁅centralizerDerived (κ t), centralizerDerived (κ t)⁆ := by
        rw [lhat_perfect e]; exact hx
      exact Subgroup.commutator_mono hLN hLN hx'
    calc N = normalClosureOf (centralizerDerived (κ t)) := hNdef
      _ ≤ ⁅N, N⁆ := h1
  obtain ⟨E, hEP, hEp, hmax⟩ := exists_perfect_core (N.comap κ)
  have hEN : E.map κ = N := map_perfectCore_eq κ hκ hNperf hEP hmax
  have hconj : ∀ g : T, ∀ x ∈ N.comap κ, g * x * g⁻¹ ∈ N.comap κ := by
    intro g x hx
    have hx' : κ x ∈ N := hx
    show κ (g * x * g⁻¹) ∈ N
    rw [map_mul, map_mul, map_inv]
    exact hNn.conj_mem _ hx' _
  haveI hEnorm : E.Normal :=
    ⟨fun n hn g => conj_le_perfectCore hEp hEP hmax (hconj g) hn⟩
  have htE : ∀ g ∈ E, t * g * t⁻¹ ∈ E := fun g hg =>
    conj_le_perfectCore hEp hEP hmax (hconj t) hg
  have hJP : J ≤ N.comap κ := fun x hx =>
    hLN (hJX ⟨x, hx, rfl⟩)
  have hJE : J ≤ E := hmax J hJP hJ
  have hEF : E ≤ centralizer (F : Set T) := perfect_le_centralizer_of_card_le_four F hF E hEp
  have hN' : ∀ M : Subgroup X, M.Normal → M ≤ E.map κ →
      (∀ g ∈ E, κ (t * g * t⁻¹ * g⁻¹) ∈ M) → M = E.map κ := by
    rcases hcases with hA66 | ⟨hU4, -, -⟩
    · intro M hMn hMle hcomm
      rw [hEN] at hMle ⊢
      obtain ⟨φ⟩ := hA66
      refine swap_normal_eq ht e N hNdef hB0 φ M hMle ?_
      intro g hg
      rw [← hEN] at hg
      obtain ⟨g', hg', rfl⟩ := hg
      have := hcomm g' hg'
      simpa [commutatorElement_def] using this
    · intro M hMn hMle hcomm
      rw [hEN] at hMle ⊢
      haveI : IsSimpleGroup ↥N := hSimp ↥N hU4
      haveI : (M.subgroupOf N).Normal := inferInstance
      rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (M.subgroupOf N) with h | h
      · exfalso
        have hM1 : ∀ m ∈ M, m = 1 := by
          intro m hm
          have : (⟨m, hMle hm⟩ : ↥N) ∈ M.subgroupOf N := hm
          rw [h] at this
          exact congrArg Subtype.val (Subgroup.mem_bot.1 this)
        have htc : κ t ∈ centralizer (N : Set X) := by
          rw [mem_centralizer_iff]
          intro g hg
          rw [← hEN] at hg
          obtain ⟨g', hg', rfl⟩ := hg
          have h1 := hM1 _ (hcomm g' hg')
          rw [map_mul, map_mul, map_mul, map_inv, map_inv] at h1
          have h2 : κ t * κ g' * (κ t)⁻¹ * (κ g')⁻¹ = 1 := h1
          have h3 : κ t * κ g' = κ g' * κ t := by
            calc κ t * κ g' = (κ t * κ g' * (κ t)⁻¹ * (κ g')⁻¹) * (κ g' * κ t) := by group
              _ = κ g' * κ t := by rw [h2, one_mul]
          exact h3.symm
        rw [hB0] at htc
        have : κ t = 1 := Subgroup.mem_bot.1 htc
        rw [this, orderOf_one] at ht
        omega
      · apply le_antisymm hMle
        intro n hn
        have : (⟨n, hn⟩ : ↥N) ∈ M.subgroupOf N := by rw [h]; exact Subgroup.mem_top _
        exact this
  have hEA : E ≤ centralizer (A : Set T) :=
    le_centralizer_of_inverted κ hκ A F hker hFA hAab ht2 hinv E hN'
  have hcentral : ∀ a ∈ E, κ a = 1 → ∀ b ∈ E, a * b = b * a := by
    intro a ha hka b hb
    have haFA : a ∈ F ⊔ A := hker hka
    have hFAb : F ⊔ A ≤ centralizer ({b} : Set T) := by
      apply sup_le
      · intro f hf
        rw [mem_centralizer_singleton_iff]
        exact mem_centralizer_iff.1 (hEF hb) f hf
      · intro f hf
        rw [mem_centralizer_singleton_iff]
        exact (mem_centralizer_iff.1 (hEA hb) f hf)
    have := mem_centralizer_singleton_iff.1 (hFAb haFA)
    exact this
  refine ⟨E, hEnorm, hEp, hJE, hEF, hEA, htE, ?_⟩
  rcases hcases with hA66 | ⟨hU4, hy1944, hSig3⟩
  ·
    obtain ⟨iso⟩ := hA66
    let ψ : ↥E →* ↥N := (κ.comp E.subtype).codRestrict N (fun x => by
      rw [← hEN]; exact ⟨x.1, x.2, rfl⟩)
    have hψ : Function.Surjective ψ := by
      intro n
      have : (n : X) ∈ E.map κ := by rw [hEN]; exact n.2
      obtain ⟨x, hx, hxn⟩ := this
      exact ⟨⟨x, hx⟩, Subtype.ext hxn⟩
    refine ⟨iso.toMonoidHom.comp ψ, iso.surjective.comp hψ, ?_, ?_⟩
    · intro x hx
      rw [Subgroup.mem_center_iff]
      intro g
      have h1 : ψ x = 1 := by
        have : iso (ψ x) = 1 := hx
        exact iso.injective (by rw [this, map_one])
      have h2 : κ x.1 = 1 := congrArg Subtype.val h1
      exact Subtype.ext (hcentral x.1 x.2 h2 g.1 g.2).symm
    · intro x hx hx2
      have hx' : κ t * ((ψ x : ↥N) : X) * (κ t)⁻¹ ∈ N := by
        have h1 : κ (t * (x : T) * t⁻¹) ∈ N := by
          rw [← hEN]; exact ⟨_, hx, rfl⟩
        rwa [map_mul, map_mul, map_inv] at h1
      have key := swap_factors ht e N hNdef iso (ψ x) hx2 hx'
      have heq : ψ ⟨t * (x : T) * t⁻¹, hx⟩ = ⟨κ t * ((ψ x : ↥N) : X) * (κ t)⁻¹, hx'⟩ := by
        apply Subtype.ext
        show κ (t * (x : T) * t⁻¹) = _
        rw [map_mul, map_mul, map_inv]
        rfl
      show (iso (ψ ⟨t * (x : T) * t⁻¹, hx⟩)).1 = 1
      rw [heq]
      exact key
  ·
    exfalso
    have hyE : y ∈ E := hJE hyJ
    have hyL : κ y ∈ centralizerDerived (κ t) := hS.2.1
    have hmapE : ∀ x : T, x ∈ E → κ x ∈ N := fun x hx => by rw [← hEN]; exact ⟨x, hx, rfl⟩
    have hLie : LieModel ↥(E.map κ) .PSU 4 3 1 := by rw [hEN]; exact hU4
    have hcentE : centralizer ((E.map κ : Subgroup X) : Set X) = ⊥ := by rw [hEN]; exact hB0
    have horb := hCov T X κ hκ E hEp hcentral hLie hcentE t ht ⟨e⟩ y hyE hy3 hyL hy1944
    have hbound := card_centralizer_le_orbit_mul κ hκ y
    rw [hy1944] at hbound
    obtain ⟨D₁, hD₁, hBD⟩ := hB
    have hD3 : Nat.card D₁ ≤ 3 := by
      have := Subgroup.card_le_of_le hD₁
      rwa [hSig3] at this
    have hcard : Nat.card ↥((centralizer ({y} : Set T)).map κ) ≤ 216 := by
      calc _ ≤ Nat.card D₁ * 72 := hBD
        _ ≤ 3 * 72 := Nat.mul_le_mul_right _ hD3
        _ = 216 := by norm_num
    have horb' : (coverOrbit κ y).ncard ≤ 8 := horb
    have : 1944 ≤ 8 * 216 :=
      hbound.trans (Nat.mul_le_mul horb' hcard)
    omega

end CFSG.EvenSporadicStandard.HSStd.Zassenhaus.PartA
