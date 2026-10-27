module

public import Certificates.Certificate442005
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec10PkBasic
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec10TypeDict

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint CFSG.GH74.KGroups CFSG.Sporadic.Schreier
  CFSG.ComponentClassification.CatFactsSmall.PSp43 CFSG.ClassicalInvolution.Q3.TA3.Check

local notation "P45" => Equiv.Perm (Fin 45)

namespace Ty

abbrev KAl : List P45 := Certificates.OmegaTypes.kaList ()

abbrev KBl : List P45 := Certificates.OmegaPk.kbList Pk.gz KAl

theorem mem_KAl {x : P45} : x ∈ KAl ↔ x ∈ Pk.KA := by
  rw [Pk.mem_KA]
  simp only [Certificates.OmegaTypes.kaList, List.mem_map]
  constructor
  · rintro ⟨A, -, rfl⟩
    exact ⟨A, rfl⟩
  · rintro ⟨A, rfl⟩
    exact ⟨A, Pk.mem_Sl A, rfl⟩

theorem mem_KBl {x : P45} : x ∈ KBl ↔ x ∈ Pk.KB := by
  rw [Pk.mem_KB]
  simp only [Certificates.OmegaPk.kbList, List.mem_map, mem_KAl, Pk.mem_KA, tab_eq]
  constructor
  · rintro ⟨y, ⟨A, rfl⟩, rfl⟩
    exact ⟨A, rfl⟩
  · rintro ⟨A, rfl⟩
    exact ⟨_, ⟨A, rfl⟩, rfl⟩

theorem mem_KAs {x : P45} :
    x ∈ Certificates.OmegaTypes.KAs ↔ x ∈ Pk.KA := mem_KAl

theorem mem_KBs {x : P45} :
    x ∈ Certificates.OmegaTypes.KBs ↔ x ∈ Pk.KB := mem_KBl

theorem invC_iff {n : ℕ} {x : P45} :
    Certificates.OmegaTypes.InvC n x ↔ InvCent n x := by
  rw [Certificates.OmegaTypes.InvC, InvCent, centCount, card_inf_centralizer QA45 QA45_ok]

theorem rowA :
    InvCent 1152 Pk.tA :=
  invC_iff.1 Certificates.certificate442005.rowA

theorem rowB :
    InvCent 192 Pk.tB :=
  invC_iff.1 Certificates.certificate442005.rowB

theorem card218c {a b : P45}
    (ha : InvCent 1152 a) (hb : InvCent 1152 b) (hab : a ≠ b) (hc : a * b = b * a) :
    InvCent 192 (b * a) :=
  invC_iff.1 (Certificates.certificate442005.c a b (invC_iff.2 ha) (invC_iff.2 hb) hab hc)

theorem card218d
    {u : P45} (hu : InvCent 192 u) (hc : u * Pk.tA = Pk.tA * u) :
    ((∀ k ∈ Pk.KA, u * k * u⁻¹ ∈ Pk.KA) ∧ (∀ k ∈ Pk.KB, u * k * u⁻¹ ∈ Pk.KB) ∧
        (∃ k ∈ Pk.KA, k * u * k⁻¹ = u * Pk.tA) ∧ ∃ k ∈ Pk.KB, k * u * k⁻¹ = u * Pk.tA) ∨
      ((∀ k ∈ Pk.KA, u * k * u⁻¹ ∈ Pk.KB) ∧ (∀ k ∈ Pk.KB, u * k * u⁻¹ ∈ Pk.KA) ∧
        InvCent 1152 (u * Pk.tA)) := by
  rcases Certificates.certificate442005.d u (invC_iff.2 hu) hc with
    ⟨h1, h2, ⟨k1, hk1, e1⟩, k2, hk2, e2⟩ | ⟨h1, h2, h3⟩
  · refine Or.inl ⟨fun k hk => mem_KAs.1 (h1 k (mem_KAs.2 hk)),
      fun k hk => mem_KBs.1 (h2 k (mem_KBs.2 hk)), ⟨k1, mem_KAs.1 hk1, e1⟩,
      ⟨k2, mem_KBs.1 hk2, e2⟩⟩
  · exact Or.inr ⟨fun k hk => mem_KBs.1 (h1 k (mem_KAs.2 hk)),
      fun k hk => mem_KAs.1 (h2 k (mem_KBs.2 hk)), invC_iff.1 h3⟩

theorem card218e
    {u : P45} (hu : InvCent 96 u)
    (h1 : ∀ k ∈ Pk.KA, u * k * u⁻¹ ∈ Pk.KB) (h2 : ∀ k ∈ Pk.KB, u * k * u⁻¹ ∈ Pk.KA) :
    u * Pk.tA = Pk.tA * u ∧ InvCent 1440 (u * Pk.tA) := by
  obtain ⟨hc, h⟩ := Certificates.certificate442005.e u (invC_iff.2 hu)
    (fun k hk => mem_KBs.2 (h1 k (mem_KAs.1 hk))) (fun k hk => mem_KAs.2 (h2 k (mem_KBs.1 hk)))
  exact ⟨hc, invC_iff.1 h⟩

theorem card218f
    {s u : P45} (hs : InvCent 96 s ∨ InvCent 192 s) (hu : u ∈ QA45.originalSubgroup)
    (huu : u * u = 1) (hu1 : u ≠ 1) (hus : u ≠ s)
    (hY : ∀ g ∈ QP45.originalSubgroup, g * s = s * g → g ^ 405 = 1 → u * g = g * u) :
    InvCent 1152 u ∨ InvCent 1440 u := by
  rcases Certificates.certificate442005.f s u (hs.imp invC_iff.2 invC_iff.2) hu huu hu1 hus
    hY with h | h
  · exact Or.inl (invC_iff.1 h)
  · exact Or.inr (invC_iff.1 h)

end Ty

end CFSG.OddStandard.SmallF3.Omega
