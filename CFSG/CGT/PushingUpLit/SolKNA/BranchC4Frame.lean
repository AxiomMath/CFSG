module

public import CFSG.CGT.PushingUpLit.SolKNA.BranchC4Defs
public import CFSG.RankThree.GF2n.Basic
import CFSG.LocalAnalysis.ComponentClassification.AS76bSec3Config
import CFSG.LocalAnalysis.ComponentClassification.Asc76XLemma25
import CFSG.LocalAnalysis.ComponentClassification.AschbacherTheorem5TransitiveQuotient

public section

namespace CFSG.CGT.PushingUpLit.SolKNA

set_option linter.unusedSectionVars false

open CFSG.ComponentClassification.AschbacherTightEmbedding
open CFSG.CGT.Timmesfeld75 (conjSubgroup mem_conjSubgroup)
open CFSG.RankThree.GF2n (card_conjSubgroup conjSubgroup_eq_self_iff le_normalizer_of_comm)

variable {G : Type} [Group G]

namespace C4Aux

theorem conjSubgroup_mono {g : G} {A B : Subgroup G} (h : A ≤ B) :
    conjSubgroup g A ≤ conjSubgroup g B :=
  Subgroup.map_mono h

theorem rightConjugate_inv_eq (Q : Subgroup G) (g : G) :
    rightConjugate Q g⁻¹ = conjSubgroup g Q := by
  simp only [rightConjugate, conjSubgroup, inv_inv]

theorem exists_ne_one_of_one_lt_card {S : Subgroup G} (h : 1 < Nat.card ↥S) :
    ∃ u ∈ S, u ≠ 1 := by
  by_contra hcon
  have : S = ⊥ := (Subgroup.eq_bot_iff_forall S).mpr fun u hu =>
    by_contra fun h => hcon ⟨u, hu, h⟩
  rw [this, Subgroup.card_bot] at h
  exact lt_irrefl _ h

theorem normalizer_of_tight [Finite G] {K : Subgroup G} (hK : TightlyEmbedded K)
    (h2 : IsPGroup 2 K) {x r : G} (hr : r ∈ K) (hr1 : r ≠ 1) (hx : x * r * x⁻¹ ∈ K) :
    x ∈ Subgroup.normalizer (K : Set G) := by
  by_contra hxN
  have hodd := hK.2 x hxN
  have hmem : r ∈ K ⊓ rightConjugate K x := ⟨hr, (mem_rightConjugate_iff K x r).mpr hx⟩
  have hbot : K ⊓ rightConjugate K x = ⊥ :=
    two_subgroup_of_odd_eq_bot (K ⊓ rightConjugate K x) (K ⊓ rightConjugate K x)
      h2.to_inf_left hodd le_rfl
  rw [hbot, Subgroup.mem_bot] at hmem
  exact hr1 hmem

theorem exists_ne_one_of_ne_bot {S : Subgroup G} (h : S ≠ ⊥) : ∃ u ∈ S, u ≠ 1 := by
  by_contra hcon
  exact h ((Subgroup.eq_bot_iff_forall S).mpr fun u hu => by_contra fun h' => hcon ⟨u, hu, h'⟩)

end C4Aux

open C4Aux

structure C4Data (R T W Z P : Subgroup G) (c x : G) : Prop where
  A : AData R T W
  Z_eq : Z = R ⊓ Subgroup.normalizer (T : Set G)
  P_eq : P = Z ⊔ T
  tight : TightlyEmbedded R
  card_T : Nat.card ↥T = 4
  c_mem : c ∈ Z
  c_ne : c ≠ 1
  sq : ∀ h ∈ W ⊓ R, h ∉ Z → h * h = c
  x_norm : x ∈ Subgroup.normalizer (P : Set G)
  x_not : x ∉ Subgroup.normalizer (R : Set G)

namespace C4Data

variable [Finite G] {R T W Z P : Subgroup G} {c x : G} (D : C4Data R T W Z P c x)
include D

theorem card_Z : Nat.card ↥Z = 4 := by
  have := D.A.card_N_eq
  rwa [← D.Z_eq, D.card_T] at this

theorem Z_le_H : Z ≤ W ⊓ R := by
  rw [D.Z_eq]
  exact D.A.N_le_H

theorem Z_le_R : Z ≤ R := D.Z_le_H.trans inf_le_right

theorem Z_le_P : Z ≤ P := by
  rw [D.P_eq]
  exact le_sup_left

theorem card_H : Nat.card ↥(W ⊓ R) = 16 := by
  rw [D.A.card_H, D.card_T]
  norm_num

theorem card_R : Nat.card ↥R = 32 := by
  rw [D.A.card_R, D.card_H]

theorem card_P : Nat.card ↥P = 16 := by
  have h1 := D.A.card_P
  rw [← D.Z_eq, ← D.P_eq, D.card_T] at h1
  exact h1

theorem P_le_normalizer_R : P ≤ Subgroup.normalizer (R : Set G) := by
  rw [D.P_eq]
  exact sup_le (D.Z_le_R.trans Subgroup.le_normalizer) D.A.T_norm

theorem P_le_normalizer_H : P ≤ Subgroup.normalizer ((W ⊓ R : Subgroup G) : Set G) := by
  rw [D.P_eq]
  refine sup_le (D.Z_le_H.trans Subgroup.le_normalizer) fun t ht => ?_
  exact D.A.S_le_normalizer_H (Subgroup.mem_sup_right ht)

theorem H_le_normalizer_P : W ⊓ R ≤ Subgroup.normalizer (P : Set G) := by
  have h := D.A.W_le_normalizer_P
  rw [← D.Z_eq, ← D.P_eq] at h
  exact inf_le_left.trans h

theorem not_R_le_normalizer_P : ¬ R ≤ Subgroup.normalizer (P : Set G) := by
  have h := D.A.not_R_le_normalizer_P
  rwa [← D.Z_eq, ← D.P_eq] at h

theorem P_sq {p : G} (hp : p ∈ P) : p * p = 1 := by
  rw [D.P_eq, D.Z_eq] at hp
  exact D.A.P_sq hp

theorem P_comm {p q : G} (hp : p ∈ P) (hq : q ∈ P) : p * q = q * p :=
  comm_of_sq_eq_one (fun _ hx => D.P_sq hx) hp hq

theorem Z_sq {z : G} (hz : z ∈ Z) : z * z = 1 :=
  D.P_sq (D.Z_le_P hz)

theorem conj_mem_P {p : G} (hp : p ∈ P) : x * p * x⁻¹ ∈ P :=
  (Subgroup.mem_normalizer_iff.mp D.x_norm p).mp hp

theorem Zx_le_P : conjSubgroup x Z ≤ P := by
  intro u hu
  have hz : x⁻¹ * u * x ∈ Z := mem_conjSubgroup.mp hu
  have := D.conj_mem_P (D.Z_le_P hz)
  have e : x * (x⁻¹ * u * x) * x⁻¹ = u := by group
  rwa [e] at this

theorem inf_conj_R : R ⊓ conjSubgroup x R = ⊥ := by
  rw [eq_bot_iff]
  intro u hu
  by_contra hu1
  have hu1' : u ≠ 1 := fun h => hu1 (Subgroup.mem_bot.mpr h)
  have h1 : x⁻¹ * u * x ∈ R := mem_conjSubgroup.mp hu.2
  have hN : x⁻¹ ∈ Subgroup.normalizer (R : Set G) :=
    normalizer_of_tight D.tight D.A.two_R hu.1 hu1' (by simpa using h1)
  exact D.x_not ((Subgroup.normalizer (R : Set G)).inv_mem_iff.mp hN)

theorem inf_conj_Z : Z ⊓ conjSubgroup x Z = ⊥ := by
  rw [eq_bot_iff]
  calc Z ⊓ conjSubgroup x Z ≤ R ⊓ conjSubgroup x R :=
        inf_le_inf D.Z_le_R (conjSubgroup_mono D.Z_le_R)
    _ = ⊥ := D.inf_conj_R
    _ ≤ ⊥ := le_rfl

theorem card_Zx : Nat.card ↥(conjSubgroup x Z) = 4 := by
  rw [card_conjSubgroup]
  exact D.card_Z

theorem Z_sup_Zx : Z ⊔ conjSubgroup x Z = P := by
  have hle : Z ⊔ conjSubgroup x Z ≤ P := sup_le D.Z_le_P D.Zx_le_P
  have hZx : conjSubgroup x Z ≤ Subgroup.normalizer (Z : Set G) :=
    le_normalizer_of_comm fun u hu z hz => D.P_comm (D.Zx_le_P hu) (D.Z_le_P hz)
  have hcard := CFSG.ComponentClassification.AschbacherTheorem3.card_sup_of_le_normalizer
    hZx D.inf_conj_Z
  rw [D.card_Z, D.card_Zx] at hcard
  exact Subgroup.eq_of_le_of_card_ge hle (by rw [D.card_P, hcard])

theorem cent_Zx {r : G} (hr : r ∈ R) (h : ∀ u ∈ conjSubgroup x Z, r * u = u * r) : r ∈ Z := by
  obtain ⟨u, hu, hu1⟩ := exists_ne_one_of_one_lt_card (S := conjSubgroup x Z)
    (by rw [D.card_Zx]; norm_num)
  have huP : u ∈ P := D.Zx_le_P hu
  have hP := D.P_eq
  have hZ := D.Z_eq
  subst hP hZ
  obtain ⟨n, hn, t, ht, rfl⟩ := D.A.exists_mul_NT huP
  by_cases ht1 : t = 1
  · exfalso
    subst ht1
    have hmem : n * 1 ∈ (R ⊓ Subgroup.normalizer (T : Set G)) ⊓
        conjSubgroup x (R ⊓ Subgroup.normalizer (T : Set G)) := ⟨by simpa using hn, hu⟩
    rw [D.inf_conj_Z, Subgroup.mem_bot] at hmem
    exact hu1 hmem
  · exact D.A.cent_R_le hn ht ht1 hr (h _ hu)

theorem not_conj_R_le_normalizer : ¬ conjSubgroup x R ≤ Subgroup.normalizer (R : Set G) := by
  intro hle
  have hTE : TightlyEmbedded (conjSubgroup x R) := by
    rw [← rightConjugate_inv_eq]
    exact CFSG.ComponentClassification.AS76b.tightlyEmbedded_rightConjugate D.tight x⁻¹
  have h2 : IsPGroup 2 (conjSubgroup x R) := D.A.two_R.map (MulAut.conj x).toMonoidHom
  have hS : IsPGroup 2 (R ⊔ conjSubgroup x R : Subgroup G) :=
    D.A.two_R.to_sup_of_normal_left' h2 hle
  have hTES : TightlyEmbedded ((conjSubgroup x R).subgroupOf (R ⊔ conjSubgroup x R)) :=
    (CFSG.ComponentClassification.AschbacherTheorem5.SectionSix.tightlyEmbedded_subgroupOf_iff
      (le_sup_right : conjSubgroup x R ≤ R ⊔ conjSubgroup x R)).mpr
      ⟨hTE.1, fun g _ hg => hTE.2 g hg⟩
  have hcomm := CFSG.ComponentClassification.Asc76X.asc76Lemma23 G (R ⊔ conjSubgroup x R)
    (conjSubgroup x R) R hS le_sup_right hTES le_sup_left hle
    (by rw [card_conjSubgroup]) (by rw [inf_comm]; exact D.inf_conj_R)
  have hcent := Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcomm
  have hRZ : R ≤ Z := fun r hr => D.cent_Zx hr fun u hu =>
    Subgroup.mem_centralizer_iff.mp (hcent (conjSubgroup_mono D.Z_le_R hu)) r hr
  have := Subgroup.card_le_of_le hRZ
  rw [D.card_R, D.card_Z] at this
  omega

end C4Data

end CFSG.CGT.PushingUpLit.SolKNA
