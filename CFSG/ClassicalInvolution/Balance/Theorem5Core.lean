module

public import CFSG.ClassicalInvolution.Balance.BootstrapAlphaDelta
public import CFSG.ClassicalInvolution.Balance.BootstrapDelta
public import CFSG.ClassicalInvolution.Balance.BootstrapClosure
import CFSG.GroupTheory.CentralizerMap

public section

namespace CFSG.ClassicalInvolution.Balance.Theorem5

open CFSG.Open CFSG.Assembly.Dichotomy CFSG.ClassicalInvolution.Balance
  CFSG.ClassicalInvolution.Balance.Bootstrap CFSG.ComponentClassification
  CFSG.ClassicalInvolution.Generic
open scoped commutatorElement

section Equivariance

variable {G : Type} [Group G]

theorem uCore_map (g : G) (F : Subgroup G) :
    (uCore F).map (MulAut.conj g).toMonoidHom = uCore (F.map (MulAut.conj g).toMonoidHom) := by
  set e : G ≃* G := MulAut.conj g with he
  apply le_antisymm
  · rw [Subgroup.map_le_iff_le_comap]
    refine iSup₂_le fun f hf => iSup_le fun hf1 => ?_
    intro x hx
    have hx' : e x ∈ (involutionOddCore f).map e.toMonoidHom := Subgroup.mem_map_of_mem _ hx
    rw [involutionOddCore_map] at hx'
    exact involutionOddCore_le_uCore (Subgroup.mem_map_of_mem _ hf)
      (fun h => hf1 (e.injective (by simpa using h))) hx'
  · refine iSup₂_le fun f' hf' => iSup_le fun hf'1 => ?_
    obtain ⟨f, hf, rfl⟩ := Subgroup.mem_map.mp hf'
    have hf1 : f ≠ 1 := fun h => hf'1 (by simp [h])
    change involutionOddCore (e f) ≤ _
    rw [← involutionOddCore_map e f]
    exact Subgroup.map_mono (involutionOddCore_le_uCore hf hf1)

theorem normalClosureIn_map (g : G) (H L : Subgroup G) :
    (normalClosureIn H L).map (MulAut.conj g).toMonoidHom =
      normalClosureIn (H.map (MulAut.conj g).toMonoidHom) (L.map (MulAut.conj g).toMonoidHom) := by
  set e : G ≃* G := MulAut.conj g with he
  apply le_antisymm
  · rw [Subgroup.map_le_iff_le_comap]
    refine iSup₂_le fun h hh => ?_
    intro x hx
    have h1 : e x ∈ (L.map (MulAut.conj h).toMonoidHom).map e.toMonoidHom :=
      Subgroup.mem_map_of_mem _ hx
    rw [Subgroup.map_map] at h1
    have h2 : (e.toMonoidHom.comp (MulAut.conj h).toMonoidHom) =
        ((MulAut.conj (g * h * g⁻¹)).toMonoidHom).comp e.toMonoidHom := by
      ext y
      simp [he, mul_assoc]
    rw [h2, ← Subgroup.map_map] at h1
    exact (le_iSup₂ (f := fun (h' : G) (_ : h' ∈ H.map e.toMonoidHom) =>
      (L.map e.toMonoidHom).map (MulAut.conj h').toMonoidHom) (g * h * g⁻¹)
      (Subgroup.mem_map.mpr ⟨h, hh, by simp [he]⟩)) h1
  · refine iSup₂_le fun h' hh' => ?_
    obtain ⟨h, hh, rfl⟩ := Subgroup.mem_map.mp hh'
    rw [Subgroup.map_map]
    have h2 : (MulAut.conj (e h)).toMonoidHom.comp e.toMonoidHom =
        e.toMonoidHom.comp (MulAut.conj h).toMonoidHom := by
      ext y
      simp [he, mul_assoc]
    change Subgroup.map ((MulAut.conj (e h)).toMonoidHom.comp e.toMonoidHom) L ≤ _
    rw [h2, ← Subgroup.map_map]
    exact Subgroup.map_mono (le_iSup₂ (f := fun (h : G) (_ : h ∈ H) =>
      L.map (MulAut.conj h).toMonoidHom) h hh)

theorem alphaCore_map (g : G) (F : Subgroup G) :
    (alphaCore F).map (MulAut.conj g).toMonoidHom =
      alphaCore (F.map (MulAut.conj g).toMonoidHom) := by
  unfold alphaCore
  rw [normalClosureIn_map, Subgroup.map_sup, Subgroup.map_commutator, uCore_map, deltaCore_map]

end Equivariance

section Frame

variable {G : Type} [Group G] {A A' F : Subgroup G}

@[expose] def alphaFrame (A : Subgroup G) : Subgroup G :=
  ⨆ F ∈ signalizerFunctorEk 2 2 A, alphaCore F

theorem alphaCore_le_alphaFrame (hF : F ∈ signalizerFunctorEk 2 2 A) :
    alphaCore F ≤ alphaFrame A :=
  le_iSup₂ (f := fun (F : Subgroup G) (_ : F ∈ signalizerFunctorEk 2 2 A) => alphaCore F) F hF

theorem map_mem_signalizerFunctorEk (g : G) (hF : F ∈ signalizerFunctorEk 2 2 A) :
    F.map (MulAut.conj g).toMonoidHom ∈
      signalizerFunctorEk 2 2 (A.map (MulAut.conj g).toMonoidHom) := by
  refine ⟨Subgroup.map_mono hF.1, ?_⟩
  rw [Subgroup.card_map_of_injective (MulAut.conj g).injective]
  exact hF.2

theorem alphaFrame_map (g : G) (A : Subgroup G) :
    (alphaFrame A).map (MulAut.conj g).toMonoidHom =
      alphaFrame (A.map (MulAut.conj g).toMonoidHom) := by
  apply le_antisymm
  · rw [Subgroup.map_le_iff_le_comap]
    refine iSup₂_le fun F hF => ?_
    intro x hx
    have hx' : (MulAut.conj g) x ∈ (alphaCore F).map (MulAut.conj g).toMonoidHom :=
      Subgroup.mem_map_of_mem _ hx
    rw [alphaCore_map] at hx'
    exact alphaCore_le_alphaFrame (map_mem_signalizerFunctorEk g hF) hx'
  · refine iSup₂_le fun F' hF' => ?_
    obtain ⟨F, hF, rfl⟩ := exists_map_four g hF'
    rw [← alphaCore_map]
    exact Subgroup.map_mono (alphaCore_le_alphaFrame hF)

variable [Finite G]

theorem alphaFrame_eq_alphaCore (h : RankThreeBalance A) (hF : F ∈ signalizerFunctorEk 2 2 A) :
    alphaFrame A = alphaCore F := by
  refine le_antisymm (iSup₂_le fun F' hF' => ?_) (alphaCore_le_alphaFrame hF)
  exact (alphaCore_eq_alphaCore h hF'.1 (by rw [hF'.2]; norm_num) hF.1
    (by rw [hF.2]; norm_num)).le

theorem exists_mem_signalizerFunctorEk (h : RankThreeBalance A) :
    ∃ F, F ∈ signalizerFunctorEk 2 2 A :=
  CFSG.SignalizerFunctor.Helpers.signalizerFunctorEk_nonempty 2 2 Nat.prime_two A h.elem
    (by rw [h.card]; norm_num)

theorem odd_card_alphaFrame (h : RankThreeBalance A) : Odd (Nat.card (alphaFrame A)) := by
  obtain ⟨F₀, hF₀⟩ := exists_mem_signalizerFunctorEk h
  obtain ⟨d, hdF₀, hd1⟩ := exists_ne_one_of_card_eq_two_pow (n := 2) (by norm_num)
    (hF₀.2 : Nat.card F₀ = 2 ^ 2)
  obtain ⟨hodd, -⟩ := deltaStar_isCompletion h.elem (by rw [h.card]) h.weak
  have hαW : alphaCore F₀ ≤ deltaStarCompletion A :=
    (alphaCore_le_uCore (comm_of_mem_subgroup h hF₀.1) hdF₀ hd1).trans
      (uCore_le_completion hF₀.1)
  rw [alphaFrame_eq_alphaCore h hF₀]
  exact hodd.of_dvd_nat (Subgroup.card_dvd_of_le hαW)

theorem alphaFrame_eq_of_shareFour (hA : RankThreeBalance A) (hA' : RankThreeBalance A')
    (h : ShareFour A A') : alphaFrame A = alphaFrame A' := by
  obtain ⟨F, hF, hF'⟩ := h
  rw [alphaFrame_eq_alphaCore hA hF, alphaFrame_eq_alphaCore hA' hF']

end Frame

section Conjugates

variable {G : Type} [Group G] {A : Subgroup G}

theorem isElemAbelian_two_map {A : Subgroup G} (hA : IsElemAbelian 2 A) (g : G) :
    IsElemAbelian 2 (A.map (MulAut.conj g).toMonoidHom) := by
  refine ⟨⟨⟨fun x y => ?_⟩⟩, ?_⟩
  · apply Subtype.ext
    have hx := mem_conjSub_iff.mp x.2
    have hy := mem_conjSub_iff.mp y.2
    have h := congrArg Subtype.val (hA.1.is_comm.comm (⟨_, hx⟩ : A) ⟨_, hy⟩)
    simp only [Subgroup.coe_mul] at h ⊢
    have h2 : g * ((g⁻¹ * x.1 * g) * (g⁻¹ * y.1 * g)) * g⁻¹ =
        g * ((g⁻¹ * y.1 * g) * (g⁻¹ * x.1 * g)) * g⁻¹ := by rw [h]
    simpa [mul_assoc] using h2
  · intro x hx
    have hx' := mem_conjSub_iff.mp hx
    have h := hA.2 _ hx'
    have : (g⁻¹ * x * g) ^ 2 = g⁻¹ * x ^ 2 * g := by simp only [pow_two]; group
    rw [this] at h
    have h3 : x ^ 2 = g * (g⁻¹ * x ^ 2 * g) * g⁻¹ := by group
    rw [h3, h]
    group


theorem weakBalanced_map (h : WeakBalanced A) (g : G) :
    WeakBalanced (A.map (MulAut.conj g).toMonoidHom) := by
  intro a' ha' ha'1 b' hb' hb'1
  obtain ⟨a, ha, rfl⟩ := Subgroup.mem_map.mp ha'
  obtain ⟨b, hb, rfl⟩ := Subgroup.mem_map.mp hb'
  have ha1 : a ≠ 1 := fun h1 => ha'1 (by simp [h1])
  have hb1 : b ≠ 1 := fun h1 => hb'1 (by simp [h1])
  have h2 := Subgroup.map_mono (f := (MulAut.conj g).toMonoidHom) (h a ha ha1 b hb hb1)
  rw [Subgroup.map_commutator, Subgroup.map_inf _ _ (f := (MulAut.conj g).toMonoidHom)
    (MulAut.conj g).injective, involutionOddCore_map, involutionOddCore_map,
    centralizer_singleton_map] at h2
  simpa using h2

theorem rankThreeBalance_map (h : RankThreeBalance A) (g : G) :
    RankThreeBalance (A.map (MulAut.conj g).toMonoidHom) :=
  ⟨isElemAbelian_two_map h.elem g, by
    rw [Subgroup.card_map_of_injective (MulAut.conj g).injective]
    exact h.card, weakBalanced_map h.weak g, twoBalancedWrt_map h.two g⟩

end Conjugates

section Propagation

variable {G : Type} [Group G] [Finite G] {A : Subgroup G}

theorem normal_alphaFrame_of_connected {𝒯 : Set (Subgroup G)}
    (hinv : ∀ A ∈ 𝒯, ∀ g : G, A.map (MulAut.conj g).toMonoidHom ∈ 𝒯)
    (hbal : ∀ A ∈ 𝒯, RankThreeBalance A)
    (hconn : ∀ A ∈ 𝒯, ∀ A' ∈ 𝒯,
      Relation.ReflTransGen (fun X Y => X ∈ 𝒯 ∧ Y ∈ 𝒯 ∧ ShareFour X Y) A A') :
    ∀ A ∈ 𝒯, (alphaFrame A).Normal :=
  normal_of_constant_on_connected alphaFrame ShareFour hinv (fun A _ g => alphaFrame_map g A)
    (fun A hA A' hA' hAA' => alphaFrame_eq_of_shareFour (hbal A hA) (hbal A' hA') hAA') hconn

theorem alphaFrame_eq_bot_of_connected {𝒯 : Set (Subgroup G)}
    (hO : componentClassificationOddCore G = ⊥)
    (hinv : ∀ A ∈ 𝒯, ∀ g : G, A.map (MulAut.conj g).toMonoidHom ∈ 𝒯)
    (hbal : ∀ A ∈ 𝒯, RankThreeBalance A)
    (hconn : ∀ A ∈ 𝒯, ∀ A' ∈ 𝒯,
      Relation.ReflTransGen (fun X Y => X ∈ 𝒯 ∧ Y ∈ 𝒯 ∧ ShareFour X Y) A A') :
    ∀ A ∈ 𝒯, alphaFrame A = ⊥ := by
  intro A hA
  have hle := OddCore.maximal G (alphaFrame A) (normal_alphaFrame_of_connected hinv hbal hconn A hA)
    (odd_card_alphaFrame (hbal A hA))
  rw [hO] at hle
  exact le_bot_iff.mp hle

theorem deltaCore_eq_bot_of_connected_frames {𝒯 : Set (Subgroup G)}
    (hO : componentClassificationOddCore G = ⊥)
    (hinv : ∀ A ∈ 𝒯, ∀ g : G, A.map (MulAut.conj g).toMonoidHom ∈ 𝒯)
    (hbal : ∀ A ∈ 𝒯, RankThreeBalance A)
    (hconn : ∀ A ∈ 𝒯, ∀ A' ∈ 𝒯,
      Relation.ReflTransGen (fun X Y => X ∈ 𝒯 ∧ Y ∈ 𝒯 ∧ ShareFour X Y) A A') :
    ∀ A ∈ 𝒯, ∀ F ∈ signalizerFunctorEk 2 2 A, deltaCore F = ⊥ := by
  intro A hA F hF
  have h1 := deltaCore_le_alphaCore (F := F)
  rw [← alphaFrame_eq_alphaCore (hbal A hA) hF,
    alphaFrame_eq_bot_of_connected hO hinv hbal hconn A hA] at h1
  exact le_bot_iff.mp h1

theorem alphaCore_eq_bot_of_connected_frames {𝒯 : Set (Subgroup G)}
    (hO : componentClassificationOddCore G = ⊥)
    (hinv : ∀ A ∈ 𝒯, ∀ g : G, A.map (MulAut.conj g).toMonoidHom ∈ 𝒯)
    (hbal : ∀ A ∈ 𝒯, RankThreeBalance A)
    (hconn : ∀ A ∈ 𝒯, ∀ A' ∈ 𝒯,
      Relation.ReflTransGen (fun X Y => X ∈ 𝒯 ∧ Y ∈ 𝒯 ∧ ShareFour X Y) A A') :
    ∀ A ∈ 𝒯, ∀ F ∈ signalizerFunctorEk 2 2 A, alphaCore F = ⊥ := by
  intro A hA F hF
  rw [← alphaFrame_eq_alphaCore (hbal A hA) hF]
  exact alphaFrame_eq_bot_of_connected hO hinv hbal hconn A hA

theorem deltaCore_eq_bot_of_alphaCore_eq_bot {A F₀ : Subgroup G} (h : RankThreeBalance A)
    (hF₀ : F₀ ∈ signalizerFunctorEk 2 2 A) (hα : alphaCore F₀ = ⊥) :
    ∀ F ∈ signalizerFunctorEk 2 2 A, deltaCore F = ⊥ := by
  intro F hF
  have h1 := deltaCore_le_alphaCore (F := F)
  rw [← alphaFrame_eq_alphaCore h hF, alphaFrame_eq_alphaCore h hF₀, hα] at h1
  exact le_bot_iff.mp h1

end Propagation

section Vertex

variable {G : Type} [Group G]

theorem centralizer_le_normalizer_alphaCore (F : Subgroup G) :
    Subgroup.centralizer (F : Set G) ≤ Subgroup.normalizer (alphaCore F : Set G) := by
  intro c hc
  have hcF : ∀ f ∈ F, c * f = f * c := fun f hf =>
    (Subgroup.mem_centralizer_iff.mp hc f hf).symm
  have hcF' : ∀ f ∈ F, c⁻¹ * f = f * c⁻¹ := fun f hf => by
    have := hcF f hf
    calc c⁻¹ * f = c⁻¹ * (f * c) * c⁻¹ := by group
      _ = c⁻¹ * (c * f) * c⁻¹ := by rw [this]
      _ = f * c⁻¹ := by group
  rw [Subgroup.mem_normalizer_iff]
  intro y
  refine ⟨fun hy => conj_mem_alphaCore hcF hy, fun hy => ?_⟩
  have := conj_mem_alphaCore hcF' hy
  simpa [mul_assoc] using this

variable [Finite G] {A : Subgroup G}

theorem rankTwoSpan_le_normalizer_alphaFrame (h : RankThreeBalance A) :
    rankTwoSpan A ≤ Subgroup.normalizer (alphaFrame A : Set G) := by
  refine iSup₂_le fun F hF => ?_
  rw [alphaFrame_eq_alphaCore h hF]
  exact centralizer_le_normalizer_alphaCore F

theorem centralizingLayer_le_normalizer_alphaFrame {Ω : Set (Subgroup G)} (hΩ : ConjInvariant Ω)
    (h : RankThreeBalance A) {a : G} (ha : a ∈ A) (hgen : CentralizerGenerationModOTwo Ω A a) :
    centralizingLayer Ω {a} ≤ Subgroup.normalizer (alphaFrame A : Set G) :=
  (centralizingLayer_le_rankTwoSpan hΩ h.elem (by rw [h.card]) ha hgen).trans
    (rankTwoSpan_le_normalizer_alphaFrame h)

omit [Finite G] in
theorem alphaFrame_map_of_mem_normalizer {y : G}
    (hy : y ∈ Subgroup.normalizer (alphaFrame A : Set G)) :
    alphaFrame (A.map (MulAut.conj y).toMonoidHom) = alphaFrame A := by
  rw [← alphaFrame_map]
  ext x
  rw [Subgroup.mem_map_equiv, MulAut.conj_symm_apply]
  have := Subgroup.mem_normalizer_iff.mp hy (y⁻¹ * x * y)
  have e : y * (y⁻¹ * x * y) * y⁻¹ = x := by group
  rwa [e] at this

omit [Finite G] in
theorem shareFour_map_of_mem_centralizer {F : Subgroup G} (hF : F ∈ signalizerFunctorEk 2 2 A)
    {y : G} (hy : y ∈ Subgroup.centralizer (F : Set G)) :
    ShareFour A (A.map (MulAut.conj y).toMonoidHom) := by
  refine ⟨F, hF, ?_⟩
  have hc : ∀ f ∈ F, y * f = f * y := fun f hf =>
    (Subgroup.mem_centralizer_iff.mp hy f hf).symm
  have hFy : F.map (MulAut.conj y).toMonoidHom = F := by
    ext x
    rw [Subgroup.mem_map_equiv, MulAut.conj_symm_apply]
    constructor
    · intro hx
      have h1 := hc _ hx
      have e1 : y * (y⁻¹ * x * y) = x * y := by group
      rw [e1] at h1
      have h2 : x = y⁻¹ * x * y := mul_right_cancel h1
      rwa [← h2] at hx
    · intro hx
      have h1 := hc _ hx
      have e : y⁻¹ * x * y = x := by
        calc y⁻¹ * x * y = y⁻¹ * (x * y) := by group
          _ = y⁻¹ * (y * x) := by rw [h1]
          _ = x := by group
      rw [e]
      exact hx
  rw [← hFy]
  exact map_mem_signalizerFunctorEk y hF

omit [Finite G] in
theorem shareFour_map {X Y : Subgroup G} (h : ShareFour X Y) (g : G) :
    ShareFour (X.map (MulAut.conj g).toMonoidHom) (Y.map (MulAut.conj g).toMonoidHom) := by
  obtain ⟨F, hFX, hFY⟩ := h
  exact ⟨F.map (MulAut.conj g).toMonoidHom, map_mem_signalizerFunctorEk g hFX,
    map_mem_signalizerFunctorEk g hFY⟩

omit [Finite G] in
theorem reflTransGen_shareFour_map_of_mem_rankTwoSpan {𝒯 : Set (Subgroup G)}
    (hinv : ∀ A ∈ 𝒯, ∀ g : G, A.map (MulAut.conj g).toMonoidHom ∈ 𝒯) {A : Subgroup G}
    (hA : A ∈ 𝒯) {x : G} (hx : x ∈ rankTwoSpan A) :
    Relation.ReflTransGen (fun X Y => X ∈ 𝒯 ∧ Y ∈ 𝒯 ∧ ShareFour X Y) A
      (A.map (MulAut.conj x).toMonoidHom) := by
  set r : Subgroup G → Subgroup G → Prop := fun X Y => X ∈ 𝒯 ∧ Y ∈ 𝒯 ∧ ShareFour X Y with hr
  have hsymm : ∀ X Y, r X Y → r Y X := fun X Y h => ⟨h.2.1, h.1, h.2.2.symm⟩
  have hmapchain : ∀ (g : G) {B C : Subgroup G}, Relation.ReflTransGen r B C →
      Relation.ReflTransGen r (B.map (MulAut.conj g).toMonoidHom)
        (C.map (MulAut.conj g).toMonoidHom) := by
    intro g B C h
    induction h with
    | refl => exact .refl
    | tail _ hbc ih =>
      exact ih.tail ⟨hinv _ hbc.1 g, hinv _ hbc.2.1 g, shareFour_map hbc.2.2 g⟩
  have hmap_map : ∀ (a b : G) (B : Subgroup G),
      (B.map (MulAut.conj a).toMonoidHom).map (MulAut.conj b).toMonoidHom =
        B.map (MulAut.conj (b * a)).toMonoidHom := by
    intro a b B
    rw [Subgroup.map_map]
    congr 1
    ext y
    simp [mul_assoc]
  have hmap_one : A.map (MulAut.conj (1 : G)).toMonoidHom = A := by
    ext y
    simp
  let H : Subgroup G :=
    { carrier := {x | Relation.ReflTransGen r A (A.map (MulAut.conj x).toMonoidHom)}
      one_mem' := by
        show Relation.ReflTransGen r A (A.map (MulAut.conj (1 : G)).toMonoidHom)
        rw [hmap_one]
      mul_mem' := fun {x y} hx hy => by
        show Relation.ReflTransGen r A (A.map (MulAut.conj (x * y)).toMonoidHom)
        rw [← hmap_map y x A]
        exact hx.trans (hmapchain x hy)
      inv_mem' := fun {x} hx => by
        show Relation.ReflTransGen r A (A.map (MulAut.conj x⁻¹).toMonoidHom)
        have h1 := hmapchain x⁻¹ (show Relation.ReflTransGen r A (A.map (MulAut.conj x).toMonoidHom)
          from hx)
        rw [hmap_map x x⁻¹ A, inv_mul_cancel, hmap_one] at h1
        exact reflTransGen_symm_of_symm hsymm h1 }
  have hle : rankTwoSpan A ≤ H := by
    refine iSup₂_le fun F hF y hy => ?_
    show Relation.ReflTransGen r A (A.map (MulAut.conj y).toMonoidHom)
    exact .single ⟨hA, hinv A hA y, shareFour_map_of_mem_centralizer hF hy⟩
  exact hle hx

omit [Finite G] in
@[expose] def frameConjugates (A : Subgroup G) : Set (Subgroup G) :=
  {X | ∃ g : G, X = A.map (MulAut.conj g).toMonoidHom}

omit [Finite G] in
theorem frameConjugates_inv (A : Subgroup G) :
    ∀ X ∈ frameConjugates A, ∀ g : G, X.map (MulAut.conj g).toMonoidHom ∈ frameConjugates A := by
  rintro X ⟨h, rfl⟩ g
  refine ⟨g * h, ?_⟩
  rw [Subgroup.map_map]
  congr 1
  ext y
  simp [mul_assoc]

omit [Finite G] in
theorem rankThreeBalance_of_mem_frameConjugates {A : Subgroup G} (h : RankThreeBalance A) :
    ∀ X ∈ frameConjugates A, RankThreeBalance X := by
  rintro X ⟨g, rfl⟩
  exact rankThreeBalance_map h g

omit [Finite G] in
theorem connected_conjClass_of_rankTwoSpan_eq_top {A : Subgroup G} (htop : rankTwoSpan A = ⊤) :
    ∀ B ∈ frameConjugates A, ∀ B' ∈ frameConjugates A,
      Relation.ReflTransGen
        (fun X Y => X ∈ frameConjugates A ∧ Y ∈ frameConjugates A ∧ ShareFour X Y) B B' := by
  have hinv := frameConjugates_inv A
  have hA : A ∈ frameConjugates A := ⟨1, by ext y; simp⟩
  have hsymm : ∀ X Y, (X ∈ frameConjugates A ∧ Y ∈ frameConjugates A ∧ ShareFour X Y) →
      (Y ∈ frameConjugates A ∧ X ∈ frameConjugates A ∧ ShareFour Y X) :=
    fun X Y h => ⟨h.2.1, h.1, h.2.2.symm⟩
  have hreach : ∀ B ∈ frameConjugates A, Relation.ReflTransGen
      (fun X Y => X ∈ frameConjugates A ∧ Y ∈ frameConjugates A ∧ ShareFour X Y) A B := by
    rintro B ⟨g, rfl⟩
    exact reflTransGen_shareFour_map_of_mem_rankTwoSpan hinv hA (htop ▸ Subgroup.mem_top g)
  intro B hB B' hB'
  exact (reflTransGen_symm_of_symm hsymm (hreach B hB)).trans (hreach B' hB')

end Vertex

end CFSG.ClassicalInvolution.Balance.Theorem5
