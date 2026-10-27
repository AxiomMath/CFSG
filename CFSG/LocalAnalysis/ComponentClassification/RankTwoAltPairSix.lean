module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoAltSixC
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoAltPair

public section

namespace CFSG.ComponentClassification.RankTwoAlt

open Equiv Equiv.Perm Subgroup CFSG.Open CFSG.ABGLocalTools
  CFSG.ComponentClassification.AschbacherTightEmbedding CFSG.ComponentClassification.AS76b
  CFSG.ComponentClassification.RankTwoSporadic CFSG.ComponentClassification.RankTwoClassical
  CFSG.Quasithin.SteinbergCB

variable {G : Type} [Group G] {A R T : Subgroup G} {g : G}

namespace SixPair

variable (np : SixPair A R T g)
include np

theorem map_rootV_A : ((rootV 6).map np.ψA.symm.toMonoidHom).map A.subtype = T := by
  ext x
  constructor
  · rintro ⟨_, ⟨v, hv, rfl⟩, rfl⟩
    exact (np.mem_T _).mpr (by rw [MulEquiv.coe_toMonoidHom, MulEquiv.apply_symm_apply]; exact hv)
  · intro hx
    exact ⟨⟨x, np.le_A hx⟩, ⟨np.ψA ⟨x, np.le_A hx⟩, (np.mem_T _).mp hx, by
      rw [MulEquiv.coe_toMonoidHom, MulEquiv.symm_apply_apply]⟩, rfl⟩

theorem map_rootV_B :
    ((rootV 6).map np.ψB.symm.toMonoidHom).map (rightConjugate A g).subtype = R := by
  ext x
  constructor
  · rintro ⟨_, ⟨v, hv, rfl⟩, rfl⟩
    exact (np.mem_R _).mpr (by rw [MulEquiv.coe_toMonoidHom, MulEquiv.apply_symm_apply]; exact hv)
  · intro hx
    exact ⟨⟨x, np.le_B hx⟩, ⟨np.ψB ⟨x, np.le_B hx⟩, (np.mem_R _).mp hx, by
      rw [MulEquiv.coe_toMonoidHom, MulEquiv.symm_apply_apply]⟩, rfl⟩

theorem actAut_swap_ψB {z w : G} (hz : z ∈ normalizer (rightConjugate A g⁻¹ : Set G))
    (hw : g⁻¹ * z * g = w) (a : ↥A) (ha : w * a * w⁻¹ ∈ A) :
    actAut np.swap.ψB ⟨z, hz⟩ (np.ψA a) = np.ψA ⟨w * a * w⁻¹, ha⟩ := by
  subst hw
  have hb : np.swap.ψB ((conjEquiv A g⁻¹).symm a) = np.ψA a := by
    rw [SixPair.swap_ψB, MulEquiv.apply_symm_apply]
  rw [← hb, actAut_apply, SixPair.swap_ψB]
  congr 1
  apply Subtype.ext
  rw [conjEquiv_apply]
  show g⁻¹ * (z * (g⁻¹⁻¹ * (a : G) * g⁻¹) * z⁻¹) * g⁻¹⁻¹ = g⁻¹ * z * g * a * (g⁻¹ * z * g)⁻¹
  group

variable [Finite G] (hc : Sec3 A R T g)
include hc

theorem actA_of_stabO (y : ↥(rightConjugate A g)) (hs : StabO (np.ψB y : Perm (Fin 6))) :
    (y : G) ∈ normalizer (A : Set G) ∧ ∀ a : ↥A, ∃ ha : (y : G) * a * (y : G)⁻¹ ∈ A,
      (np.ψA ⟨_, ha⟩ : Perm (Fin 6)) =
        restrictO (np.ψB y : Perm (Fin 6)) * np.ψA a * (restrictO (np.ψB y : Perm (Fin 6)))⁻¹ := by
  have hs' : StabO (np.swap.ψA (conjEquiv A g y) : Perm (Fin 6)) := by
    rw [SixPair.swap_ψA, MulEquiv.symm_apply_apply]
    exact hs
  obtain ⟨hxB, hact⟩ := np.swap.actAut_of_stabO hc.swap (conjEquiv A g y) hs'
  have hw : g⁻¹ * ((conjEquiv A g y : ↥A) : G) * g = y := by
    rw [conjEquiv_apply]
    group
  have hyA : (y : G) ∈ normalizer (A : Set G) := by
    have h := (mem_normalizer_rightConjugate_iff A g⁻¹ _).mp hxB
    rwa [inv_inv, hw] at h
  refine ⟨hyA, fun a => ⟨(mem_normalizer_iff.mp hyA a).mp a.2, ?_⟩⟩
  have key := np.actAut_swap_ψB hxB hw a ((mem_normalizer_iff.mp hyA a).mp a.2)
  rw [hact, SixPair.swap_ψA, MulEquiv.symm_apply_apply] at key
  have := congrArg Subtype.val key
  rw [conjPerm_apply] at this
  exact this.symm

theorem actA_of_mem_centralizer {k : G} (hk : k ∈ centralizer (rightConjugate A g : Set G)) :
    k ∈ normalizer (A : Set G) ∧ ∃ π : Perm (Fin 6), (∀ i : Fin 6, 4 ≤ (i : ℕ) → π i = i) ∧
      ∀ a : ↥A, ∃ ha : k * a * k⁻¹ ∈ A, (np.ψA ⟨_, ha⟩ : Perm (Fin 6)) = π * np.ψA a * π⁻¹ := by
  have hk' : g * k * g⁻¹ ∈ centralizer (A : Set G) := by
    rw [centralizer_rightConjugate, mem_rightConjugate_iff] at hk
    exact hk
  obtain ⟨f, hf45, hfact, -⟩ := np.swap.exists_hom_K hc.swap
  obtain ⟨hk'B, hk'act⟩ := hfact ⟨g * k * g⁻¹, hk'⟩
  have hw : g⁻¹ * (g * k * g⁻¹) * g = k := by group
  have hkA : k ∈ normalizer (A : Set G) := by
    have h := (mem_normalizer_rightConjugate_iff A g⁻¹ _).mp hk'B
    rwa [inv_inv, hw] at h
  refine ⟨hkA, f ⟨g * k * g⁻¹, hk'⟩, fun i hi => ?_, fun a =>
    ⟨(mem_normalizer_iff.mp hkA a).mp a.2, ?_⟩⟩
  · rcases (show (i : ℕ) = 4 ∨ (i : ℕ) = 5 by have := i.isLt; omega) with h | h
    · rw [show i = 4 from Fin.ext h]
      exact (hf45 _).1
    · rw [show i = 5 from Fin.ext h]
      exact (hf45 _).2
  · have key := np.actAut_swap_ψB hk'B hw a ((mem_normalizer_iff.mp hkA a).mp a.2)
    rw [hk'act] at key
    have := congrArg Subtype.val key
    rw [conjPerm_apply] at this
    exact this.symm

end SixPair

theorem altPair_of_sec3_six [Finite G] (hc : Sec3 A R T g)
    (h32 : Lemma32) (h4 : Asc75Theorem4) (h34 : Asc08Lemma34) (h2 : Asc76Theorem2)
    (e : ↥A ≃* alternatingGroup (Fin 6)) : AltPair 6 A (rightConjugate A g) := by
  obtain ⟨np⟩ := exists_sixPair hc h32 h4 h34 h2 e
  have hKt := tightlyEmbedded_centralizer_of_standard hc.hyp.standard
  have hgK : g ∉ normalizer (Subgroup.centralizer (A : Set G) : Set G) := by
    rw [normalizer_centralizer_eq hc.hyp.standard]
    exact hc.not_mem
  refine ⟨⟨np.ψA, np.ψB, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_, ?_⟩
  ·
    rw [np.map_rootV_A, centralizer_rightConjugate]
    exact hc.sylowT
  ·
    rw [np.map_rootV_B]
    exact hc.sylowR
  ·
    rintro _ ⟨_, ⟨z, hz, rfl⟩, rfl⟩
    exact np.YT_le hc _ (by rw [MulEquiv.coe_toMonoidHom, MulEquiv.apply_symm_apply]; exact hz)
  ·
    rintro _ ⟨_, ⟨z, hz, rfl⟩, rfl⟩
    exact np.YR_le hc _ (by rw [MulEquiv.coe_toMonoidHom, MulEquiv.apply_symm_apply]; exact hz)
  ·
    intro x hx b
    obtain ⟨hxB, hact⟩ := np.actAut_of_stabO hc x (stabO_of_lt (by decide) hx)
    have hb : (x : G) * b * (x : G)⁻¹ ∈ rightConjugate A g := (mem_normalizer_iff.mp hxB b).mp b.2
    refine ⟨hb, ?_⟩
    have := actAut_apply np.ψB ⟨x, hxB⟩ b
    rw [hact] at this
    rw [← this, conjPerm_apply]
  ·
    intro y hy
    obtain ⟨-, hact⟩ := np.actA_of_stabO hc y (stabO_of_lt (by decide) hy)
    refine ⟨restrictO (np.ψB y : Perm (Fin 6)), fun i hi =>
      restrictO_apply_of_lt (stabO_of_lt (by decide) hy) hi, hact⟩
  ·
    refine ⟨1, fun i _ => rfl, fun y hy a => ?_⟩
    obtain ⟨ha, h⟩ := (np.actA_of_stabO hc y (stabO_of_lt (by decide) hy)).2 a
    refine ⟨ha, ?_⟩
    rw [h, one_mul, inv_one, mul_one]
  ·
    intro k hk
    obtain ⟨f, hf45, hfact, -⟩ := np.exists_hom_K hc
    obtain ⟨hkB, hkact⟩ := hfact ⟨k, hk⟩
    refine ⟨hkB, f ⟨k, hk⟩, fun i hi => ?_, fun b => ⟨(mem_normalizer_iff.mp hkB b).mp b.2, ?_⟩⟩
    · rcases (show (i : ℕ) = 4 ∨ (i : ℕ) = 5 by have := i.isLt; omega) with h | h
      · rw [show i = 4 from Fin.ext h]
        exact (hf45 _).1
      · rw [show i = 5 from Fin.ext h]
        exact (hf45 _).2
    · have := actAut_apply np.ψB ⟨k, hkB⟩ b
      rw [hkact] at this
      rw [← this, conjPerm_apply]
  ·
    intro k hk
    exact np.actA_of_mem_centralizer hc hk
  ·
    have h := hKt.2 g hgK
    rwa [← centralizer_rightConjugate] at h
  ·
    refine sup_le (np.normalizer_le_inf hc) ?_
    intro y hy
    have hyA : g * y * g⁻¹ ∈ normalizer (A : Set G) :=
      (mem_normalizer_rightConjugate_iff A g y).mp hy
    have h := np.swap.normalizer_le_inf hc.swap hyA
    have hQ : rightConjugate (Subgroup.centralizer (A : Set G) ⊓
        Subgroup.centralizer (rightConjugate A g⁻¹ : Set G)) g =
        Subgroup.centralizer (A : Set G) ⊓ Subgroup.centralizer (rightConjugate A g : Set G) := by
      ext z
      rw [mem_rightConjugate_iff, Subgroup.mem_inf, Subgroup.mem_inf,
        centralizer_rightConjugate A g⁻¹, mem_rightConjugate_iff, centralizer_rightConjugate A g,
        mem_rightConjugate_iff (Subgroup.centralizer (A : Set G)) g z]
      have e : g⁻¹ * (g * z * g⁻¹) * g⁻¹⁻¹ = z := by group
      rw [e]
      exact and_comm
    rw [← hQ, mem_normalizer_rightConjugate_iff]
    exact h
  ·
    intro t ht ht2 ht1
    have h := Lemma39.centralizer_le_normalizer_rightConjugate hc.hyp 1 (t := t)
      (by rw [rightConjugate_one]; exact ht) ht1 (by rw [sq]; exact ht2)
    rwa [rightConjugate_one] at h
  ·
    intro t ht ht2 ht1
    rw [centralizer_rightConjugate] at ht
    exact Lemma39.centralizer_le_normalizer_rightConjugate hc.hyp g ht ht1 (by rw [sq]; exact ht2)

end CFSG.ComponentClassification.RankTwoAlt
