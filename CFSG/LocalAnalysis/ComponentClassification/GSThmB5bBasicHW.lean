module

public import CFSG.LocalAnalysis.ComponentClassification.GSThmB58SubHypW
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB5bBasic

public section

namespace CFSG.ComponentClassification.GSThmB

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer

namespace Hyp52W

variable {H : Type} [Group H] [Finite H] (h : Hyp52W H)

abbrev W : Subgroup H := normalizer (h.B : Set H)

abbrev D : Subgroup H := h.S ⊓ h.J

abbrev V : Subgroup H := layerIn (normalizer (h.B : Set H))

theorem isPGroup_S : IsPGroup 2 h.S := by
  obtain ⟨P₀, hP₀⟩ := h.S_sylow
  have h1 : IsPGroup 2 ((P₀ : Subgroup _).map
      (centralizer ({h.a} : Set H) ⊓ normalizer (h.J : Set H)).subtype) := P₀.isPGroup'.map _
  rwa [hP₀, map_subgroupOf_eq_of_le h.S_le] at h1

theorem comm_a {s : H} (hs : s ∈ h.S) : s * h.a = h.a * s :=
  mem_centralizer_singleton_iff.mp (mem_inf.mp (h.S_le hs)).1

theorem S_le_normalizer : h.S ≤ normalizer (h.J : Set H) := fun _ hs => (mem_inf.mp (h.S_le hs)).2

theorem a_mem_coreActionKernel : h.a ∈ coreActionKernel h.J :=
  GSLit.mem_coreActionKernel_of_le_centralizer h.J_le

theorem a_mem_S : h.a ∈ h.S := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set M := centralizer ({h.a} : Set H) ⊓ normalizer (h.J : Set H) with hM
  have haM : h.a ∈ M := mem_inf.mpr ⟨mem_centralizer_singleton_iff.mpr rfl,
    (mem_coreActionKernel.mp h.a_mem_coreActionKernel).1⟩
  have ha2 : IsPGroup 2 (zpowers h.a) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, h.orderOf_a, pow_one])
  have hnorm : zpowers h.a ≤ normalizer (h.S : Set H) := by
    refine (zpowers_le.mpr ?_).trans (centralizer_le_normalizer _)
    rw [mem_centralizer_iff]
    intro s hs
    exact h.comm_a hs
  have hR : IsPGroup 2 ↥(zpowers h.a ⊔ h.S) := ha2.to_sup_of_normal_right' h.isPGroup_S hnorm
  have hRM : zpowers h.a ⊔ h.S ≤ M := sup_le (zpowers_le.mpr haM) h.S_le
  obtain ⟨P₀, hP₀⟩ := h.S_sylow
  have hle : (P₀ : Subgroup M) ≤ (zpowers h.a ⊔ h.S).subgroupOf M := by
    rw [hP₀]
    exact fun y hy => mem_subgroupOf.mpr (mem_sup_right (mem_subgroupOf.mp hy))
  have heq := P₀.is_maximal' (Q := (zpowers h.a ⊔ h.S).subgroupOf M) hR.comap_subtype hle
  have h1 : (⟨h.a, haM⟩ : M) ∈ (zpowers h.a ⊔ h.S).subgroupOf M :=
    mem_subgroupOf.mpr (mem_sup_left (mem_zpowers h.a))
  rw [heq, hP₀] at h1
  exact mem_subgroupOf.mp h1

theorem a_mem_P : h.a ∈ h.P := mem_inf.mpr ⟨h.a_mem_S, h.a_mem_coreActionKernel⟩

theorem x_comm_a : h.x * h.a = h.a * h.x := h.comm_a h.x_mem

theorem P_le_S : h.P ≤ h.S := inf_le_left

theorem D_le_S : h.D ≤ h.S := inf_le_left

theorem D_le_J : h.D ≤ h.J := inf_le_right

theorem B_le_P : h.B ≤ h.P := h.B_le

theorem B_le_S : h.B ≤ h.S := h.B_le_P.trans h.P_le_S

theorem S_inf_oddCore_eq_bot : h.S ⊓ (pPrimeCore 2 h.J).map h.J.subtype = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine eq_bot_of_isPGroup_two_of_coprime (h.isPGroup_S.to_le inf_le_left) ?_
  have hc : Nat.Coprime 2 (Nat.card ↥((pPrimeCore 2 h.J).map h.J.subtype)) := by
    rw [Subgroup.card_map_of_injective h.J.subtype_injective]
    exact CFSG.pPrimeCore_coprime_card
  exact Nat.Coprime.coprime_dvd_right (Subgroup.card_dvd_of_le inf_le_right) hc

theorem isQuasisimple_J : IsQuasisimple (OddBar h.J) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact ((CatalogueBPrimeJoin.pComponent_subgroupOf_iff 2 h.J _ h.J_le).1
    h.isPComponent_J).2.2

theorem isQuasisimple_K : IsQuasisimple (OddBar h.K) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact ((CatalogueBPrimeJoin.pComponent_subgroupOf_iff 2 h.K _ h.isPComponent_K.1).1
    h.isPComponent_K.2).2.2

theorem B_le_coreActionKernel : h.B ≤ coreActionKernel h.J := h.B_le.trans inf_le_right

theorem isPGroup_B : IsPGroup 2 h.B := h.isPGroup_S.to_le h.B_le_S

theorem V_eq_K (hKa : conjugate h.K h.a = h.K) : h.V = h.K := by
  rw [Hyp52W.V, ← h.layer_eq_K, hKa, sup_idem]

theorem B_le_T : h.B ≤ h.T := by
  intro y hy
  have h1 := h.B_le hy
  exact mem_inf.mpr ⟨mem_inf.mpr ⟨(mem_inf.mp h1).1, le_normalizer hy⟩, h1⟩

instance B_subgroupOf_T_normal : (h.B.subgroupOf h.T).Normal :=
  (normal_subgroupOf_iff_le_normalizer h.B_le_T).mpr fun _ hy => (mem_inf.mp (mem_inf.mp hy).1).2

end Hyp52W

end CFSG.ComponentClassification.GSThmB
