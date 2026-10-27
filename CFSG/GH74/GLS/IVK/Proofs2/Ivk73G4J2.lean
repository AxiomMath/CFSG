module

public import CFSG.GH74.GLS.IVK.Proofs2.Ivk73G4FamOf
public import CFSG.GH74.Generic.S45.LSporWit
public import CFSG.RankThree.PartOne.KS.J2
public import Certificates.Certificate5157
public import Certificates.Certificate5150
public import CFSG.GH74.Generic.S45.LEvSporJ2Spec

public section

namespace CFSG.GH74.GLS.IVK

open Subgroup CFSG CFSG.ABGLocalTools Blueprint CFSG.Sporadic.Th CFSG.Sporadic.Th.Native
  CFSG.Sporadic.Schreier CFSG.Sporadic.Schreier.Native CFSG.Sporadic.SmallOddCore
  CFSG.Sporadic.SmallOddCore.Native CFSG.GH74.Generic.S45 CFSG.GH74.Generic.S45.EvSpor
open CFSG.ComponentClassification.OuterAutomorphisms (inner Outer)
open scoped commutatorElement

section Counts

variable {n : ℕ}

theorem card_centCount {Q : CFSG.Certificates.RawSchreierDatum n} (hn : n < 2 ^ 32)
    (hQ : CFSG.Certificates.ValidSchreier Q) {a b : Table} {ag bg : Equiv.Perm (Fin n)}
    (ha : Rep n a ag) (hb : Rep n b bg) :
    Nat.card {x : Q.originalSubgroup // x * ag = ag * x ∧ x * bg = bg * x} =
      countProducts n (fun g => commTT n g a && commTT n g b) (levelTables Q) (idT n) := by
  classical
  have hf : ∀ T g, Rep n T g → ((fun g => commTT n g a && commTT n g b) T = true ↔
      (g * ag = ag * g ∧ g * bg = bg * g)) := fun T g hT => by
    simp only [Bool.and_eq_true]
    rw [commTT_iff hT ha, commTT_iff hT hb]
  have h := countProducts_spec (P := fun x : Equiv.Perm (Fin n) =>
    x * ag = ag * x ∧ x * bg = bg * x) hf (forall₂_levelTables hn Q)
    (Rep.idT (G := Equiv.Perm (Fin n)) hn)
  simp only [one_mul, List.map_id'] at h
  rw [h]
  exact card_subtype_eq_countP Q.originalSubgroup (enumeration Q) (enumeration_nodup Q hQ)
    (mem_enumeration_iff Q hQ)
    (fun x : Equiv.Perm (Fin n) => x * ag = ag * x ∧ x * bg = bg * x)

theorem card_centCountOuter {Q : CFSG.Certificates.RawSchreierDatum n} (hn : n < 2 ^ 32)
    (hQ : CFSG.Certificates.ValidSchreier Q) {a b w : Table} {ag bg wg : Equiv.Perm (Fin n)}
    (ha : Rep n a ag) (hb : Rep n b bg) (hw : Rep n w wg) :
    Nat.card {x : Q.originalSubgroup // x * wg * ag = ag * (x * wg) ∧ x * wg * bg = bg * (x * wg)} =
      countProducts n (fun g => commTT n (compT n g w) a && commTT n (compT n g w) b)
        (levelTables Q) (idT n) := by
  classical
  have hf : ∀ T g, Rep n T g → ((fun g => commTT n (compT n g w) a && commTT n (compT n g w) b) T = true ↔
      (g * wg * ag = ag * (g * wg) ∧ g * wg * bg = bg * (g * wg))) := fun T g hT => by
    simp only [Bool.and_eq_true]
    rw [commTT_iff (Rep.compT hT hw) ha, commTT_iff (Rep.compT hT hw) hb]
  have h := countProducts_spec (P := fun x : Equiv.Perm (Fin n) =>
    x * wg * ag = ag * (x * wg) ∧ x * wg * bg = bg * (x * wg)) hf (forall₂_levelTables hn Q)
    (Rep.idT (G := Equiv.Perm (Fin n)) hn)
  simp only [one_mul, List.map_id'] at h
  rw [h]
  exact card_subtype_eq_countP Q.originalSubgroup (enumeration Q) (enumeration_nodup Q hQ)
    (mem_enumeration_iff Q hQ)
    (fun x : Equiv.Perm (Fin n) => x * wg * ag = ag * (x * wg) ∧ x * wg * bg = bg * (x * wg))

end Counts

theorem j2_levelTables :
    levelTables j2Chain = Certificates.IvkCent.j2ChainTbls :=
  CFSG.ComponentClassification.J2Cover.levelTables_eq j2ChainArrays
    (CFSG.Certificates.chainCheckFacts PairJ2.chain_check.1)

theorem j2_cent_Kb :
    (∀ x ∈ j2R, (∀ a ∈ Subgroup.closure (tp 315 '' {x | x ∈ j2KbGens.toArray}), x * a = a * x) →
        x ∈ j2P) ∧
      Nat.card ↥(j2P ⊓ Subgroup.centralizer
        ((Subgroup.closure (tp 315 '' {x | x ∈ j2KbGens.toArray}) : Subgroup (Equiv.Perm (Fin 315)))
          : Set (Equiv.Perm (Fin 315)))) = 12 := by
  have hn : (315 : ℕ) < 2 ^ 32 := by norm_num
  obtain ⟨hreps, -, -, -, -, hKb, -, -, -, -, -, -, -, -⟩ := Certificates.certificate5150
  obtain ⟨hrepU, -, -⟩ := j2_reps hreps
  obtain ⟨-, -, -, hA, hB⟩ := j2_Kb_facts hKb
  obtain ⟨h1, h2⟩ := Certificates.certificate5157
  set KB : Subgroup (Equiv.Perm (Fin 315)) := Subgroup.closure (tp 315 '' {x | x ∈ j2KbGens.toArray})
    with hKB
  have haM : tp 315 j2KbA ∈ KB := Subgroup.subset_closure ⟨j2KbA, by simp [j2KbGens], rfl⟩
  have hbM : tp 315 j2KbB ∈ KB := Subgroup.subset_closure ⟨j2KbB, by simp [j2KbGens], rfl⟩
  have hgens : ∀ x : Equiv.Perm (Fin 315), x * tp 315 j2KbA = tp 315 j2KbA * x →
      x * tp 315 j2KbB = tp 315 j2KbB * x → ∀ a ∈ KB, x * a = a * x := by
    intro x hxa hxb
    have hle : KB ≤ Subgroup.centralizer ({x} : Set (Equiv.Perm (Fin 315))) := by
      rw [hKB, Subgroup.closure_le]
      rintro _ ⟨y, hy, rfl⟩
      have hy' : y ∈ j2KbGens := List.mem_toArray.mp hy
      simp only [j2KbGens, List.mem_cons, List.not_mem_nil, or_false] at hy'
      rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff]
      rcases hy' with rfl | rfl
      · exact hxa.symm
      · exact hxb.symm
    intro a ha
    exact (Subgroup.mem_centralizer_singleton_iff.1 (hle ha)).symm
  obtain ⟨hU2, -, -, -, -, hRmem, -⟩ :=
    CFSG.Sporadic.SmallOddCore.ctuc_j2_normalizing_involution_permutation_model
  constructor
  ·
    intro x hxR hxc
    by_contra hxP
    have hxu : x * j2u ∈ j2P := ((hRmem x).1 hxR).resolve_left hxP
    have hUU : j2u * j2u = 1 := by rw [← sq, hU2]
    have hpx : x * j2u * j2u = x := by rw [mul_assoc, hUU, mul_one]
    have hc0 : Nat.card {y : j2Chain.originalSubgroup //
        y * tp 315 j2OuterTbl * tp 315 j2KbA = tp 315 j2KbA * (y * tp 315 j2OuterTbl) ∧
          y * tp 315 j2OuterTbl * tp 315 j2KbB = tp 315 j2KbB * (y * tp 315 j2OuterTbl)} = 0 := by
      rw [card_centCountOuter hn j2Chain_valid.1 hA hB hrepU, j2_levelTables]
      exact h2
    have hempty : IsEmpty {y : j2Chain.originalSubgroup //
        y * tp 315 j2OuterTbl * tp 315 j2KbA = tp 315 j2KbA * (y * tp 315 j2OuterTbl) ∧
          y * tp 315 j2OuterTbl * tp 315 j2KbB = tp 315 j2KbB * (y * tp 315 j2OuterTbl)} := by
      rcases Nat.card_eq_zero.1 hc0 with h | h
      · exact h
      · exact absurd h (not_infinite_iff_finite.2 inferInstance)
    refine hempty.false ⟨⟨x * j2u, by rw [← j2P_eq_original]; exact hxu⟩, ?_, ?_⟩
    · show x * j2u * j2u * tp 315 j2KbA = tp 315 j2KbA * (x * j2u * j2u)
      rw [hpx]
      exact hxc _ haM
    · show x * j2u * j2u * tp 315 j2KbB = tp 315 j2KbB * (x * j2u * j2u)
      rw [hpx]
      exact hxc _ hbM
  · have hc1 : Nat.card {y : j2Chain.originalSubgroup //
        y * tp 315 j2KbA = tp 315 j2KbA * y ∧ y * tp 315 j2KbB = tp 315 j2KbB * y} = 12 := by
      rw [card_centCount hn j2Chain_valid.1 hA hB, j2_levelTables]
      exact h1
    rw [← hc1]
    refine Nat.card_congr
      { toFun := fun y => ⟨⟨y.1, by rw [← j2P_eq_original]; exact (Subgroup.mem_inf.1 y.2).1⟩,
          (Subgroup.mem_centralizer_iff.1 (Subgroup.mem_inf.1 y.2).2 _ haM).symm,
          (Subgroup.mem_centralizer_iff.1 (Subgroup.mem_inf.1 y.2).2 _ hbM).symm⟩
        invFun := fun z => ⟨z.1.1, Subgroup.mem_inf.2 ⟨by rw [j2P_eq_original]; exact z.1.2,
          fun a ha => (hgens z.1.1 z.2.1 z.2.2 a ha).symm⟩⟩
        left_inv := fun y => rfl
        right_inv := fun z => rfl }

theorem j2_model :
    Ivk73Model j2P j2R (Subgroup.closure (tp 315 '' {x | x ∈ j2KbGens.toArray}))
      (tp 315 j2Row2B.rep) := by
  obtain ⟨hreps, hC2A, hC2B, hcent5, -, hKb, hder, hnorm, hE16, -, -, -, -, -⟩ :=
    Certificates.certificate5150
  obtain ⟨-, hrepA, hrepB⟩ := j2_reps hreps
  obtain ⟨hEB, hinvB⟩ := j2_C2B_enums hC2B
  obtain ⟨hMenum, hMcard, hMP, hA, hB⟩ := j2_Kb_facts hKb
  have hdc := derivedIn_spec hEB hMenum hinvB hder
  have hrB := j2_rows_spec.1 j2Row2B j2Row2B_mem
  refine
    { autModel := j2_autModel
      card_le := CFSG.RankThree.PartOne.j2_card_le
      tX_mem := j2_row_mem_P j2Row2B_mem j2Row2B_outer
      tX_ord := hrB.2.1
      card_A := hMcard
      card_cent := hrB.2.2.2.2.trans j2Row2B_centOrder
      derived := fun x hx y hy => hdc x hx y hy
      classes := ?_ }
  intro t htP ht2
  rcases j2_cover t htP ht2 with ⟨g, hg, hgt⟩ | ⟨g, hg, hgt⟩
  · right
    have hrA := j2_rows_spec.1 j2Row2A j2Row2A_mem
    have hCA : j2C j2Row2A = centralizerIn j2P (tp 315 j2Row2A.rep) := hrA.2.2.2.1
    have hperf : ⁅centralizerIn j2P (tp 315 j2Row2A.rep), centralizerIn j2P (tp 315 j2Row2A.rep)⁆ =
        centralizerIn j2P (tp 315 j2Row2A.rep) := by
      have hw := perfWit_of_all perfWit_j2_2A j2Row2A j2Row2A_mem j2Row2A_centOrder
      rw [← hCA]
      exact (perfWitOK_spec (by norm_num) hw).1
    have hperf' := GHInv.commutator_centralizerIn_conj hg hperf
    rw [← hgt] at hperf'
    have hcls : t ∈ CFSG.Sporadic.Schreier.conjClass j2P (tp 315 j2Row2A.rep) := ⟨g, hg, hgt⟩
    have hcard : Nat.card ↥(centralizerIn j2P t) = 1920 := by
      rw [GHInv.card_centralizerIn_eq_of_mem_conjClass j2P hcls]
      exact hrA.2.2.2.2.trans j2Row2A_centOrder
    exact GHInv.NoU2Comp.of_perfect (Subgroup.isPerfect_iff.2 hperf') (Or.inl hcard)
  · exact Or.inl ⟨g, Subgroup.mem_sup_left hg, hgt⟩

theorem ivk73_j2 :
    Ivk73Fam (fun X _ => NativeSporadic.IsSporadic X .J2) := by
  intro N _ _ L K Q h hL
  obtain ⟨e⟩ := hL
  have e' : ↥L ≃* NativeSporadic.J2 := e
  let θ : ↥L ≃* ↥j2P := e'.trans j2PermEquiv
  obtain ⟨hcentOut, hcent12⟩ := j2_cent_Kb
  obtain ⟨hcardN, hKbar, hb1, -⟩ := h.of_model j2_model θ (b₁ := 4) (b₂ := Nat.card ↥j2P)
    (fun S hSR hSc hSp => by
      have hSP : S ≤ j2P := fun s hs => hcentOut s (hSR hs) (fun a ha => hSc a ha s hs)
      have hSC : S ≤ j2P ⊓ Subgroup.centralizer
          ((Subgroup.closure (tp 315 '' {x | x ∈ j2KbGens.toArray}) : Subgroup (Equiv.Perm (Fin 315)))
            : Set (Equiv.Perm (Fin 315))) := by
        refine le_inf hSP fun s hs => ?_
        rw [Subgroup.mem_centralizer_iff]
        exact fun a ha => (hSc a ha s hs).symm
      have hdvd : Nat.card ↥S ∣ 12 := hcent12 ▸ Subgroup.card_dvd_of_le hSC
      obtain ⟨k, hk⟩ := (IsPGroup.iff_card).1 hSp
      rw [hk] at hdvd ⊢
      rcases k with _ | _ | _ | k
      · norm_num
      · norm_num
      · norm_num
      · exfalso
        have h8 : 8 ∣ 12 := (Dvd.intro _ (by ring : 8 * 2 ^ k = 2 ^ (k + 1 + 1 + 1))).trans hdvd
        omega)
    (fun S hSP _ => Subgroup.card_le_of_le hSP)
  obtain ⟨hQel, hQ4⟩ := h.Q_row hb1
  exact ⟨hQel, hQ4, Or.inr (Or.inl ⟨hKbar, ⟨e⟩, h.index_row hcardN⟩)⟩

end CFSG.GH74.GLS.IVK
