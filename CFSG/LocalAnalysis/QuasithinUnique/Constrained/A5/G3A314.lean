module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.G3Delta5
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Vol2NativeBasicBase
public import CFSG.Quasithin.Background.A3Structure313SL2

public section

namespace CFSG.QuasithinUnique.A5.G3

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.QuasithinUnique.Vol2Native

@[expose] def A314J4NoDelta5 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (Λ B T : Subgroup G),
    IsSporadic .J4 ↥Λ → IsSylowTwoOf T Λ → B ≤ Λ → T ≤ Subgroup.normalizer (B : Set G) →
    ¬ IsDelta5Group ↥B

theorem card_of_isElemAbelianOfRank {V : Type*} [Group V] {p n : ℕ}
    (h : IsElemAbelianOfRank p n V) : Nat.card V = p ^ n := by
  obtain ⟨e⟩ := h
  rw [Nat.card_congr e.toEquiv, Nat.card_congr (Multiplicative.toAdd : Multiplicative (Fin n →
    ZMod p) ≃ (Fin n → ZMod p)), Nat.card_pi]
  simp [Nat.card_zmod]

theorem card_isSL2_five {X : Type} [Group X] (h : IsSL2 5 X) : Nat.card X = 120 := by
  rw [A313.IsSL2.card_eq (by norm_num) h]
  norm_num

section Reduction

variable {G : Type} [Group G] [Finite G]

theorem injective_modO2 {C L : Subgroup G} (hLC : L ≤ C)
    (hOZ : pCoreOf 2 C ≤ Subgroup.centralizer (C : Set G)) (hZ : blockZ L = ⊥)
    (hQU : blockQ L = blockU L) :
    Function.Injective ((QuotientGroup.mk' (CFSG.pCore 2 ↥C)).comp (Subgroup.inclusion hLC)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [injective_iff_map_eq_one]
  intro x hx
  have h1 : Subgroup.inclusion hLC x ∈ CFSG.pCore 2 ↥C := (QuotientGroup.eq_one_iff _).mp hx
  have hxO : (x : G) ∈ pCoreOf 2 C := (mem_pCore_iff_mem_pCoreOf _).mp h1
  have hxc : (x : G) ∈ Subgroup.centralizer (C : Set G) := hOZ hxO
  have hN2 : IsPGroup 2 ↥(pCoreOf 2 C ⊓ L) :=
    (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 C).to_le inf_le_left
  have hNn : ((pCoreOf 2 C ⊓ L).subgroupOf L).Normal := by
    rw [Subgroup.normal_subgroupOf_iff inf_le_right]
    intro n l hn hl
    have hn' : n ∈ pCoreOf 2 C := hn.1
    have := Subgroup.mem_centralizer_iff.mp (hOZ hn') l (hLC hl)
    rw [show l * n * l⁻¹ = n by rw [this]; simp]
    exact hn
  have hxQ : (x : G) ∈ pCoreOf 2 L :=
    CFSG.LieType.BorelTits.le_pCoreOf 2 inf_le_right hNn hN2 ⟨hxO, x.2⟩
  have hxU : (x : G) ∈ blockU L := by rw [← hQU]; exact hxQ
  have hxL : (x : G) ∈ Subgroup.centralizer (L : Set G) :=
    Subgroup.mem_centralizer_iff.mpr fun l hl => by
      have := Subgroup.mem_centralizer_iff.mp hxc l (hLC hl)
      exact this
  have hxZ : (x : G) ∈ blockZ L := ⟨hxU, hxL⟩
  rw [hZ] at hxZ
  exact Subtype.ext (Subgroup.mem_bot.mp hxZ)

omit [Finite G] in
theorem map_normalizes {C L S : Subgroup G} (hSN : S ≤ Subgroup.normalizer (L : Set G)) :
    (S.subgroupOf C).map (QuotientGroup.mk' (CFSG.pCore 2 ↥C)) ≤
      Subgroup.normalizer ((modO2Image C L : Subgroup (↥C ⧸ CFSG.pCore 2 ↥C)) :
        Set (↥C ⧸ CFSG.pCore 2 ↥C)) := by
  have one_dir : ∀ s : ↥C, (s : G) ∈ Subgroup.normalizer (L : Set G) →
      ∀ h ∈ modO2Image C L, QuotientGroup.mk' (CFSG.pCore 2 ↥C) s * h *
        (QuotientGroup.mk' (CFSG.pCore 2 ↥C) s)⁻¹ ∈ modO2Image C L := by
    intro s hs h hh
    obtain ⟨l, hl, rfl⟩ := hh
    refine ⟨s * l * s⁻¹, ?_, by simp⟩
    have hl' : (l : G) ∈ L := Subgroup.mem_subgroupOf.mp hl
    have := (Subgroup.mem_normalizer_iff.mp hs (l : G)).mp hl'
    exact Subgroup.mem_subgroupOf.mpr (by simpa using this)
  rintro _ ⟨s, hs, rfl⟩
  have hs' : (s : G) ∈ Subgroup.normalizer (L : Set G) := hSN (Subgroup.mem_subgroupOf.mp hs)
  rw [Subgroup.mem_normalizer_iff]
  intro h
  refine ⟨one_dir s hs' h, fun hh => ?_⟩
  have hsi : ((s⁻¹ : ↥C) : G) ∈ Subgroup.normalizer (L : Set G) := by
    simpa using Subgroup.inv_mem _ hs'
  have := one_dir s⁻¹ hsi _ hh
  simpa [map_inv, mul_assoc] using this

end Reduction

end CFSG.QuasithinUnique.A5.G3
