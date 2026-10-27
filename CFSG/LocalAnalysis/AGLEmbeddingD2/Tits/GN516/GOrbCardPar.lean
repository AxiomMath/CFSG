module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.MsideParabolicEscape.MinParK
import Mathlib.Tactic.Group
public import CFSG.CharacterTheory.Semidihedral.DihedralQuaternion
public import CFSG.LinearAlgebra.LinearGroups.ProjectiveSimple
public import CFSG.Open.Defs

public section

namespace CFSG.AGLEmbeddingD2.Tits.GN516.CardPar

open CFSG.LieType.Universal CFSG.LieType.CurtisTits CFSG.LieType.RootSystem
  CFSG.LieType.Steinberg CFSG.AGLEmbeddingD2.Tits.MsideParabolicEscape.MinPar

variable {K : Type*} [Group K] [Finite K] {D : UniversalRootDatum K} {n : Fin D.rank → K}
  {H : Fin D.rank → Subgroup K}
  (hct : IsCTGroupDatum (coxeterMatrix D.isFiniteType).toCoxeterSystem
    (weylAction D.isFiniteType) D.roots D.rootGroup n H) (hext : SteinbergExtras D n H)

set_option hygiene false in
local notation "cs" => (coxeterMatrix D.isFiniteType).toCoxeterSystem

private theorem cpSingleMem (i : Fin D.rank) : (Pi.single i 1 : Fin D.rank → ℤ) ∈ D.roots :=
  (RootSystem.ofCartan D.isFiniteType D.divisible).single_mem i

private theorem cpNegSingleMem (i : Fin D.rank) :
    (-Pi.single i 1 : Fin D.rank → ℤ) ∈ D.roots :=
  (RootSystem.ofCartan D.isFiniteType D.divisible).neg_mem _ (cpSingleMem i)

private theorem cpSimpleSingle (i : Fin D.rank) :
    weylAction D.isFiniteType ((cs).simple i) (Pi.single i 1 : Fin D.rank → ℤ) =
      -Pi.single i 1 :=
  weylAction_simple_single D.isFiniteType i

private theorem cpSimpleNeg (i : Fin D.rank) :
    weylAction D.isFiniteType ((cs).simple i) (-Pi.single i 1 : Fin D.rank → ℤ) =
      Pi.single i 1 := by
  rw [map_neg, cpSimpleSingle, neg_neg]

private theorem cpBorelMulCell (i : Fin D.rank) {b g : K} (hb : b ∈ borel D H)
    (hg : g ∈ bruhatCell hct 1 ∪ bruhatCell hct ((cs).simple i)) :
    b * g ∈ bruhatCell hct 1 ∪ bruhatCell hct ((cs).simple i) := by
  rcases hg with hg | hg
  · exact Or.inl (mul_mem_bruhatCell hct hb hg)
  · exact Or.inr (mul_mem_bruhatCell hct hb hg)

include hct hext in
private theorem cpNMulCell (i : Fin D.rank) {g : K}
    (hg : g ∈ bruhatCell hct 1 ∪ bruhatCell hct ((cs).simple i)) :
    n i * g ∈ bruhatCell hct 1 ∪ bruhatCell hct ((cs).simple i) := by
  rcases hg with hg | hg
  · have h := n_mul_mem_bruhatCell hct hext hg i
    rw [mul_one] at h
    exact h
  · have h := n_mul_mem_bruhatCell hct hext hg i
    rw [(cs).simple_mul_simple_self, Set.union_comm] at h
    exact h

include hct hext in
private theorem cpMulCell (i : Fin D.rank) {g g' : K}
    (hg : g ∈ bruhatCell hct 1 ∪ bruhatCell hct ((cs).simple i))
    (hg' : g' ∈ bruhatCell hct 1 ∪ bruhatCell hct ((cs).simple i)) :
    g * g' ∈ bruhatCell hct 1 ∪ bruhatCell hct ((cs).simple i) := by
  rcases hg with hg | hg
  · rw [bruhatCell_one hct] at hg
    exact cpBorelMulCell hct i hg hg'
  · obtain ⟨b₁, hb₁, b₂, hb₂, rfl⟩ := hg
    rw [nrep_simple hct i]
    have e : b₁ * n i * b₂ * g' = b₁ * (n i * (b₂ * g')) := by simp only [mul_assoc]
    rw [e]
    exact cpBorelMulCell hct i hb₁ (cpNMulCell hct hext i (cpBorelMulCell hct i hb₂ hg'))

private theorem cpInvCell (i : Fin D.rank) {g : K}
    (hg : g ∈ bruhatCell hct 1 ∪ bruhatCell hct ((cs).simple i)) :
    g⁻¹ ∈ bruhatCell hct 1 ∪ bruhatCell hct ((cs).simple i) := by
  rcases hg with hg | hg
  · have hb : g ∈ borel D H := by rwa [bruhatCell_one hct] at hg
    exact Or.inl (by rw [bruhatCell_one hct]; exact inv_mem hb)
  · obtain ⟨b₁, hb₁, b₂, hb₂, rfl⟩ := hg
    have hsq : (n i ^ 2)⁻¹ ∈ borel D H := inv_mem (iSup_le_borel (sq_n_mem_iSup hct i))
    refine Or.inr ⟨b₂⁻¹, inv_mem hb₂, (n i ^ 2)⁻¹ * b₁⁻¹, mul_mem hsq (inv_mem hb₁), ?_⟩
    rw [nrep_simple hct i]
    group

private def cpCell (i : Fin D.rank) : Subgroup K where
  carrier := bruhatCell hct 1 ∪ bruhatCell hct ((cs).simple i)
  mul_mem' := fun ha hb => cpMulCell hct hext i ha hb
  one_mem' := Or.inl (by rw [bruhatCell_one hct]; exact one_mem _)
  inv_mem' := fun ha => cpInvCell hct i ha

include hct hext in
private theorem cpRankOneLe (i : Fin D.rank) : rankOne D.rootGroup i ≤ cpCell hct hext i := by
  intro g hg
  show g ∈ bruhatCell hct 1 ∪ bruhatCell hct ((cs).simple i)
  rcases hext.rankOne_bruhat i g hg with ⟨h, hh, u, hu, rfl⟩ | ⟨u, hu, h, hh, v, hv, rfl⟩
  · left
    rw [bruhatCell_one hct]
    exact mul_mem (iSup_le_borel (le_iSup H i hh))
      (rootGroup_le_borel (cpSingleMem i) (ht_single_pos i) hu)
  · right
    refine ⟨u, rootGroup_le_borel (cpSingleMem i) (ht_single_pos i) hu, h * v,
      mul_mem (iSup_le_borel (le_iSup H i hh))
        (rootGroup_le_borel (cpSingleMem i) (ht_single_pos i) hv), ?_⟩
    rw [nrep_simple hct i]
    simp only [mul_assoc]

include hct hext in
private theorem cpParJLe (i : Fin D.rank) : parJ D H {i} ≤ cpCell hct hext i := by
  unfold parJ
  refine sup_le ?_ (iSup₂_le fun j hj => ?_)
  · intro g hg
    show g ∈ bruhatCell hct 1 ∪ bruhatCell hct ((cs).simple i)
    exact Or.inl (by rw [bruhatCell_one hct]; exact hg)
  · rw [Set.mem_singleton_iff.1 hj]
    exact cpRankOneLe hct hext i

include hct hext in
private theorem cpNotMemBorel (i : Fin D.rank) : n i ∉ borel D H := by
  intro hn
  apply not_map_conj_n_borel_le hct hext i
  rintro _ ⟨b, hb, rfl⟩
  exact mul_mem (mul_mem hn hb) (inv_mem hn)

include hct hext in
private theorem cpNegInfBorel (i : Fin D.rank) {y : K}
    (hy : y ∈ D.rootGroup (-Pi.single i 1)) (hyB : y ∈ borel D H) : y = 1 := by
  have hyL : y ∈ rankOne D.rootGroup i := Subgroup.mem_sup_right hy
  rcases hext.rankOne_bruhat i y hyL with ⟨h, hh, u, hu, rfl⟩ | ⟨u, hu, h, hh, v, hv, he⟩
  · have hHN : h ∈ Subgroup.normalizer (D.rootGroup (-Pi.single i 1) : Set K) := by
      refine Subgroup.mem_normalizer_iff.2 fun x => ⟨fun hx => hct.H_conj_mem i _
        (cpNegSingleMem i) h hh x hx, fun hx => ?_⟩
      have h2 := hct.H_conj_mem i _ (cpNegSingleMem i) h⁻¹ (inv_mem hh) _ hx
      rwa [show h⁻¹ * (h * x * h⁻¹) * h⁻¹⁻¹ = x by group] at h2
    have hu_N : u ∈ Subgroup.normalizer (D.rootGroup (-Pi.single i 1) : Set K) := by
      have h3 := mul_mem (inv_mem hHN) (Subgroup.le_normalizer hy)
      rwa [inv_mul_cancel_left] at h3
    have hu1 : u = 1 := hext.eq_one_of_mem_normalizer i u hu hu_N
    rw [hu1, mul_one] at hy ⊢
    have hT : n i * h * (n i)⁻¹ ∈ ⨆ k, H k := conj_n_mem_iSup hct i (le_iSup H i hh)
    have hX : n i * h * (n i)⁻¹ ∈ D.rootGroup (Pi.single i 1) := by
      have h4 := hct.conj_mem i _ (cpNegSingleMem i) h hy
      rwa [cpSimpleNeg] at h4
    have hU : n i * h * (n i)⁻¹ ∈ posUnipotent D :=
      rootGroup_le_posUnipotent (cpSingleMem i) (ht_single_pos i) hX
    have htor : (⨆ k, H k) ⊓ posUnipotent D = ⊥ := hext.torus_inf_posPart
    have hbot : n i * h * (n i)⁻¹ = 1 := by
      have hmem : n i * h * (n i)⁻¹ ∈ (⨆ k, H k) ⊓ posUnipotent D :=
        Subgroup.mem_inf.2 ⟨hT, hU⟩
      rw [htor, Subgroup.mem_bot] at hmem
      exact hmem
    calc h = (n i)⁻¹ * (n i * h * (n i)⁻¹) * n i := by group
      _ = 1 := by rw [hbot]; group
  · exfalso
    apply cpNotMemBorel hct hext i
    have hu' : u ∈ borel D H := rootGroup_le_borel (cpSingleMem i) (ht_single_pos i) hu
    have hv' : v ∈ borel D H := rootGroup_le_borel (cpSingleMem i) (ht_single_pos i) hv
    have hh' : h ∈ borel D H := iSup_le_borel (le_iSup H i hh)
    have e : n i = u⁻¹ * y * v⁻¹ * h⁻¹ := by rw [he]; group
    rw [e]
    exact mul_mem (mul_mem (mul_mem (inv_mem hu') hyB) (inv_mem hv')) (inv_mem hh')

include hct hext in
private theorem cpInj (i : Fin D.rank) {b b' x x' : K} (hb : b ∈ borel D H)
    (hb' : b' ∈ borel D H) (hx : x ∈ D.rootGroup (Pi.single i 1))
    (hx' : x' ∈ D.rootGroup (Pi.single i 1)) (he : b * n i * x = b' * n i * x') :
    b = b' ∧ x = x' := by
  have hz : b'⁻¹ * b = n i * (x' * x⁻¹) * (n i)⁻¹ := by
    calc b'⁻¹ * b = (b'⁻¹ * (b * n i * x)) * x⁻¹ * (n i)⁻¹ := by group
      _ = (b'⁻¹ * (b' * n i * x')) * x⁻¹ * (n i)⁻¹ := by rw [he]
      _ = n i * (x' * x⁻¹) * (n i)⁻¹ := by group
  have hY : b'⁻¹ * b ∈ D.rootGroup (-Pi.single i 1) := by
    rw [hz]
    have h1 := hct.conj_mem i _ (cpSingleMem i) (x' * x⁻¹) (mul_mem hx' (inv_mem hx))
    rwa [cpSimpleSingle] at h1
  have h1 : b'⁻¹ * b = 1 := cpNegInfBorel hct hext i hY (mul_mem (inv_mem hb') hb)
  have hbb : b = b' := (inv_mul_eq_one.1 h1).symm
  rw [← hbb, mul_assoc, mul_assoc] at he
  exact ⟨hbb, mul_left_cancel (mul_left_cancel he)⟩

include hct hext in
private theorem cpNMulBorel (i : Fin D.rank) {c : K} (hc : c ∈ borel D H) :
    ∃ b' ∈ borel D H, ∃ x ∈ D.rootGroup (Pi.single i 1), n i * c = b' * n i * x := by
  obtain ⟨b', hb', x, hx, he⟩ := exists_n_mul_mul_nrep hct hext ((cs).not_isLeftDescent_one i) hc
  refine ⟨b', hb', x, ?_, ?_⟩
  · simpa using hx
  · simpa only [nrep_one hct, mul_one, nrep_simple hct i] using he

include hct hext in
private theorem cpParJForm (i : Fin D.rank) {g : K} (hg : g ∈ parJ D H {i}) :
    g ∈ borel D H ∨ ∃ b ∈ borel D H, ∃ x ∈ D.rootGroup (Pi.single i 1),
      g = b * n i * x := by
  have hc : g ∈ bruhatCell hct 1 ∪ bruhatCell hct ((cs).simple i) := cpParJLe hct hext i hg
  rcases hc with hc | hc
  · exact Or.inl (by rwa [bruhatCell_one hct] at hc)
  · obtain ⟨b₁, hb₁, b₂, hb₂, rfl⟩ := hc
    obtain ⟨b', hb', x, hx, he⟩ := cpNMulBorel hct hext i hb₂
    refine Or.inr ⟨b₁ * b', mul_mem hb₁ hb', x, hx, ?_⟩
    rw [nrep_simple hct i]
    calc b₁ * n i * b₂ = b₁ * (n i * b₂) := by group
      _ = b₁ * (b' * n i * x) := by rw [he]
      _ = b₁ * b' * n i * x := by group

include hct hext in
theorem card_parJ_singleton (i : Fin D.rank) :
    Nat.card ↥(parJ D H {i}) =
      Nat.card ↥(borel D H) * (1 + Nat.card ↥(D.rootGroup (Pi.single i 1))) := by
  have hmemP : ∀ (b : ↥(borel D H)) (x : ↥(D.rootGroup (Pi.single i 1))),
      (b : K) * n i * (x : K) ∈ parJ D H {i} := fun b x =>
    mul_mem (mul_mem (borel_le_parJ _ b.2)
      (rankOne_le_parJ (Set.mem_singleton i) (hct.n_mem i)))
      (rankOne_le_parJ (Set.mem_singleton i) (Subgroup.mem_sup_left x.2))
  let f : ↥(borel D H) ⊕ (↥(borel D H) × ↥(D.rootGroup (Pi.single i 1))) →
      ↥(parJ D H {i}) :=
    Sum.elim (fun b => ⟨b.1, borel_le_parJ _ b.2⟩)
      (fun p => ⟨(p.1 : K) * n i * (p.2 : K), hmemP p.1 p.2⟩)
  have hf : Function.Bijective f := by
    refine ⟨?_, ?_⟩
    · rintro (b | ⟨b, x⟩) (b' | ⟨b', x'⟩) he
      · have he₁ := congrArg Subtype.val he
        have he₂ : (b : K) = (b' : K) := he₁
        exact congrArg Sum.inl (Subtype.ext he₂)
      · exfalso
        have hv₁ := congrArg Subtype.val he
        have hv : (b : K) = (b' : K) * n i * (x' : K) := hv₁
        apply cpNotMemBorel hct hext i
        have e : n i = (b' : K)⁻¹ * (b : K) * (x' : K)⁻¹ := by rw [hv]; group
        rw [e]
        exact mul_mem (mul_mem (inv_mem b'.2) b.2)
          (inv_mem (rootGroup_le_borel (cpSingleMem i) (ht_single_pos i) x'.2))
      · exfalso
        have hv₁ := congrArg Subtype.val he
        have hv : (b : K) * n i * (x : K) = (b' : K) := hv₁
        apply cpNotMemBorel hct hext i
        have e : n i = (b : K)⁻¹ * (b' : K) * (x : K)⁻¹ := by rw [← hv]; group
        rw [e]
        exact mul_mem (mul_mem (inv_mem b.2) b'.2)
          (inv_mem (rootGroup_le_borel (cpSingleMem i) (ht_single_pos i) x.2))
      · have he₁ := congrArg Subtype.val he
        have he' : (b : K) * n i * (x : K) = (b' : K) * n i * (x' : K) := he₁
        obtain ⟨h1, h2⟩ := cpInj hct hext i b.2 b'.2 x.2 x'.2 he'
        rw [Subtype.ext h1, Subtype.ext h2]
    · rintro ⟨g, hg⟩
      rcases cpParJForm hct hext i hg with hgB | ⟨b, hb, x, hx, rfl⟩
      · exact ⟨Sum.inl ⟨g, hgB⟩, rfl⟩
      · exact ⟨Sum.inr (⟨b, hb⟩, ⟨x, hx⟩), rfl⟩
  have hcard := Nat.card_eq_of_bijective f hf
  rw [Nat.card_sum, Nat.card_prod] at hcard
  rw [← hcard, mul_add, mul_one]

include hct hext in
theorem card_parJ_ne_of_card_rootGroup_ne {i j : Fin D.rank}
    (h : Nat.card ↥(D.rootGroup (Pi.single i 1)) ≠ Nat.card ↥(D.rootGroup (Pi.single j 1))) :
    Nat.card ↥(parJ D H {i}) ≠ Nat.card ↥(parJ D H {j}) := by
  rw [card_parJ_singleton hct hext, card_parJ_singleton hct hext]
  intro e
  have hB : 0 < Nat.card ↥(borel D H) := Nat.card_pos
  exact h (by
    have := Nat.eq_of_mul_eq_mul_left hB e
    omega)

end CFSG.AGLEmbeddingD2.Tits.GN516.CardPar
