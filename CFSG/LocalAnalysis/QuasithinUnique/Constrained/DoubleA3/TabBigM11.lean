module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.DoubleA3.TabBigKlein
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.L239InspM11
import Mathlib.Tactic.Group
public import Certificates.Certificate110
public import CFSG.CGT.Timmesfeld75.L2Pair
public import CFSG.CGT.Timmesfeld75.ListWCBasic
public import CFSG.ClassicalGroups
public import CFSG.LinearAlgebra.LinearGroups.CoordinateData
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTightEmbeddingAction
public import CFSG.LocalAnalysis.ComponentClassification.BlockMutualRanks
public import CFSG.LocalAnalysis.ComponentClassification.InvolutionGeneratedSubgroup
public import CFSG.LocalAnalysis.ComponentClassification.OrbitBlockConjugation
public import CFSG.LocalAnalysis.ComponentClassification.SylowTwoImageLifting
public import CFSG.LocalAnalysis.ComponentClassification.TwoActionProperEmbedding
public import CFSG.LocalAnalysis.ComponentInitial.LinearFlagElation
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.DoubleA3.Lemma32B
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.DoubleA3.Lemma32S
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.DoubleA3.Lemma37
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_20

public section

namespace CFSG.QuasithinUnique.DoubleA3

open Equiv CFSG.QuasithinUnique.Unc25G2

namespace TabBigM11

local notation "𝓜" => CFSG.Blueprint.NativeSporadic.M11

set_option maxRecDepth 100000

@[expose] def allProd : List (Perm (Fin 11)) :=
  (wordPermsT CFSG.Sporadic.Bridge.M11.witnesses0).flatMap fun t₀ =>
    (wordPermsT CFSG.Sporadic.Bridge.M11.witnesses1).flatMap fun t₁ =>
      (wordPermsT CFSG.Sporadic.Bridge.M11.witnesses2).flatMap fun t₂ =>
        (wordPermsT CFSG.Sporadic.Bridge.M11.witnesses3).map fun t₃ => t₀ * (t₁ * (t₂ * t₃))

@[expose] def Cm : List (Perm (Fin 11)) := allProd.filter fun x => decide (x * pA = pA * x)

theorem length_Cm : Cm.length = 48 := by decide +kernel

@[expose] def kleinOKm : Bool :=
  Cm.all (fun b => decide (b * b ≠ 1) || decide (b = 1) || decide (b = pA) ||
    Cm.all (fun x => decide (x * b ≠ b * x) || decide (x = 1) || decide (x = pA) ||
      decide (x = b) || decide (x = pA * b)))

theorem kleinOKm_true : kleinOKm = true := by
  decide +kernel

theorem klein_check_M11 :
    ∀ b ∈ Cm, b * b = 1 → b ≠ 1 → b ≠ pA →
      ∀ x ∈ Cm, x * b = b * x → x = 1 ∨ x = pA ∨ x = b ∨ x = pA * b := by
  intro b hb hb2 hb1 hbu x hx hxb
  have h := kleinOKm_true
  unfold kleinOKm at h
  rw [List.all_eq_true] at h
  have h1 := h b hb
  simp only [Bool.or_eq_true, decide_eq_true_eq, List.all_eq_true] at h1
  rcases h1 with ((h1 | h1) | h1) | h1
  · exact absurd hb2 h1
  · exact absurd h1 hb1
  · exact absurd h1 hbu
  · rcases h1 x hx with (((h2 | h2) | h2) | h2) | h2
    · exact absurd hxb h2
    · exact Or.inl h2
    · exact Or.inr (Or.inl h2)
    · exact Or.inr (Or.inr (Or.inl h2))
    · exact Or.inr (Or.inr (Or.inr h2))

theorem mem_Cm
    {x : Perm (Fin 11)} (hx : x ∈ 𝓜) (hc : x * pA = pA * x) : x ∈ Cm := by
  obtain ⟨t₀, ht₀, t₁, ht₁, t₂, ht₂, t₃, ht₃, rfl⟩ := level0 hx
  rw [← wordPermsT_eq] at ht₀ ht₁ ht₂ ht₃
  unfold Cm allProd
  rw [List.mem_filter]
  refine ⟨?_, decide_eq_true hc⟩
  simp only [List.mem_flatMap, List.mem_map]
  exact ⟨t₀, ht₀, t₁, ht₁, t₂, ht₂, t₃, ht₃, rfl⟩

theorem kleinSC_M11_gA
    {b g : ↥𝓜} (hb2 : b * b = 1) (hb1 : b ≠ 1) (hbu : b ≠ gA)
    (hbc : b * gA = gA * b) (hgu : g * gA = gA * g) (hgb : g * b = b * g) :
    g = 1 ∨ g = gA ∨ g = b ∨ g = gA * b := by
  have hb2' : (b : Perm (Fin 11)) * b = 1 := congrArg Subtype.val hb2
  have hb1' : (b : Perm (Fin 11)) ≠ 1 := fun h => hb1 (Subtype.ext h)
  have hbu' : (b : Perm (Fin 11)) ≠ pA := fun h => hbu (Subtype.ext h)
  have hbc' : (b : Perm (Fin 11)) * pA = pA * b := congrArg Subtype.val hbc
  have hgu' : (g : Perm (Fin 11)) * pA = pA * g := congrArg Subtype.val hgu
  have hgb' : (g : Perm (Fin 11)) * b = b * g := congrArg Subtype.val hgb
  rcases klein_check_M11 (b : Perm (Fin 11)) (mem_Cm b.2 hbc') hb2' hb1' hbu' (g : Perm (Fin 11))
    (mem_Cm g.2 hgu') hgb' with h | h | h | h
  · exact Or.inl (Subtype.ext h)
  · exact Or.inr (Or.inl (Subtype.ext h))
  · exact Or.inr (Or.inr (Or.inl (Subtype.ext h)))
  · exact Or.inr (Or.inr (Or.inr (Subtype.ext h)))

theorem mem_of_mem_wordPermsT
    {W : List (Fin 11 × List (ℕ × Bool))} {t : Perm (Fin 11)}
    (ht : t ∈ wordPermsT W) : t ∈ 𝓜 := by
  rw [wordPermsT_eq] at ht
  obtain ⟨w, -, rfl⟩ := mem_wordPerms.mp ht
  exact CFSG.Sporadic.Bridge.M11.nativeWord_mem _

theorem of_mem_Cm
    {x : Perm (Fin 11)} (hx : x ∈ Cm) : x ∈ 𝓜 ∧ x * pA = pA * x := by
  unfold Cm allProd at hx
  obtain ⟨hx, hc⟩ := List.mem_filter.mp hx
  simp only [List.mem_flatMap, List.mem_map] at hx
  obtain ⟨t₀, ht₀, t₁, ht₁, t₂, ht₂, t₃, ht₃, rfl⟩ := hx
  exact ⟨Subgroup.mul_mem _ (mem_of_mem_wordPermsT ht₀) (Subgroup.mul_mem _
    (mem_of_mem_wordPermsT ht₁) (Subgroup.mul_mem _ (mem_of_mem_wordPermsT ht₂)
      (mem_of_mem_wordPermsT ht₃))), of_decide_eq_true hc⟩

theorem nodup_Cm : Cm.Nodup := by
  decide +kernel

theorem card_centralizer_gA
    : Nat.card (Subgroup.centralizer ({gA} : Set ↥𝓜)) = 48 := by
  have e : (Subgroup.centralizer ({gA} : Set ↥𝓜)) ≃ {x : Perm (Fin 11) // x ∈ Cm.toFinset} :=
    { toFun := fun g => ⟨(g.1 : Perm (Fin 11)), List.mem_toFinset.mpr (mem_Cm g.1.2
        (congrArg Subtype.val
          (Subgroup.mem_centralizer_iff.mp g.2 gA (Set.mem_singleton gA)).symm))⟩
      invFun := fun x => ⟨⟨x.1, (of_mem_Cm (List.mem_toFinset.mp x.2)).1⟩,
        Subgroup.mem_centralizer_iff.mpr (by
          rintro h rfl
          exact Subtype.ext (of_mem_Cm (List.mem_toFinset.mp x.2)).2.symm)⟩
      left_inv := fun g => rfl
      right_inv := fun x => rfl }
  rw [Nat.card_congr e, Nat.card_eq_finsetCard, List.toFinset_card_of_nodup nodup_Cm, length_Cm]

end TabBigM11

open TabBigM11

theorem kleinSC_M11 : KleinSC ↥CFSG.Blueprint.NativeSporadic.M11 := by
  intro V hV4 hV2 g hg
  obtain ⟨t, htV, ht1, b, hbV, hb1, hbt⟩ := exists_two_ne_one_of_card_four hV2 hV4
  have ht2 : t * t = 1 := hV2 t htV
  obtain ⟨c, hc⟩ := CFSG.QuasithinUnique.Vol2Native.L239.M11Insp.exists_conj ht2 ht1
  have hbtc : b * t = t * b := comm_of_sq_eq_one hV2 hbV htV
  have hgt : g * t = t * g := hg t htV
  have hgb : g * b = b * g := hg b hbV
  have hu : c⁻¹ * t * c = gA := by rw [← hc]; group
  have hb2 : (c⁻¹ * b * c) * (c⁻¹ * b * c) = 1 := by
    calc (c⁻¹ * b * c) * (c⁻¹ * b * c) = c⁻¹ * (b * b) * c := by group
      _ = 1 := by rw [hV2 b hbV]; group
  have hb1' : c⁻¹ * b * c ≠ 1 := by
    intro h
    apply hb1
    calc b = c * (c⁻¹ * b * c) * c⁻¹ := by group
      _ = 1 := by rw [h]; group
  have hbu' : c⁻¹ * b * c ≠ gA := by
    intro h
    apply hbt
    rw [← hu] at h
    calc b = c * (c⁻¹ * b * c) * c⁻¹ := by group
      _ = c * (c⁻¹ * t * c) * c⁻¹ := by rw [h]
      _ = t := by group
  have hbc' : (c⁻¹ * b * c) * gA = gA * (c⁻¹ * b * c) := by
    rw [← hu]
    calc c⁻¹ * b * c * (c⁻¹ * t * c) = c⁻¹ * (b * t) * c := by group
      _ = c⁻¹ * (t * b) * c := by rw [hbtc]
      _ = c⁻¹ * t * c * (c⁻¹ * b * c) := by group
  have hgu' : (c⁻¹ * g * c) * gA = gA * (c⁻¹ * g * c) := by
    rw [← hu]
    calc c⁻¹ * g * c * (c⁻¹ * t * c) = c⁻¹ * (g * t) * c := by group
      _ = c⁻¹ * (t * g) * c := by rw [hgt]
      _ = c⁻¹ * t * c * (c⁻¹ * g * c) := by group
  have hgb' : (c⁻¹ * g * c) * (c⁻¹ * b * c) = (c⁻¹ * b * c) * (c⁻¹ * g * c) := by
    calc c⁻¹ * g * c * (c⁻¹ * b * c) = c⁻¹ * (g * b) * c := by group
      _ = c⁻¹ * (b * g) * c := by rw [hgb]
      _ = c⁻¹ * b * c * (c⁻¹ * g * c) := by group
  rcases kleinSC_M11_gA hb2 hb1' hbu' hbc' hgu' hgb' with h | h | h | h
  · have : g = 1 := by
      calc g = c * (c⁻¹ * g * c) * c⁻¹ := by group
        _ = 1 := by rw [h]; group
    rw [this]; exact V.one_mem
  · have : g = t := by
      calc g = c * (c⁻¹ * g * c) * c⁻¹ := by group
        _ = c * (c⁻¹ * t * c) * c⁻¹ := by rw [h, hu]
        _ = t := by group
    rw [this]; exact htV
  · have : g = b := by
      calc g = c * (c⁻¹ * g * c) * c⁻¹ := by group
        _ = c * (c⁻¹ * b * c) * c⁻¹ := by rw [h]
        _ = b := by group
    rw [this]; exact hbV
  · have : g = t * b := by
      calc g = c * (c⁻¹ * g * c) * c⁻¹ := by group
        _ = c * ((c⁻¹ * t * c) * (c⁻¹ * b * c)) * c⁻¹ := by rw [h, hu]
        _ = t * b := by group
    rw [this]; exact V.mul_mem htV hbV

theorem kleinSC_of_m11 {X : Type} [Group X]
    (h : Nonempty (X ≃* CFSG.Blueprint.NativeSporadic.Carrier .M11)) : KleinSC X := by
  obtain ⟨e⟩ := h
  exact KleinSC.of_mulEquiv e kleinSC_M11

theorem card_dvd_of_m11 {X : Type} [Group X]
    (h : Nonempty (X ≃* CFSG.Blueprint.NativeSporadic.Carrier .M11)) : 16 ∣ Nat.card X := by
  obtain ⟨e⟩ := h
  rw [Nat.card_congr e.toEquiv]
  have h48 : 48 ∣ Nat.card ↥CFSG.Blueprint.NativeSporadic.M11 := by
    rw [← card_centralizer_gA]
    exact Subgroup.card_subgroup_dvd_card _
  exact (by norm_num : 16 ∣ 48).trans h48

end CFSG.QuasithinUnique.DoubleA3
