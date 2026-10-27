module

public import CFSG.LocalAnalysis.ComponentClassification.Sol78Cited
public import CFSG.Goldschmidt75.CorollaryB1

public section

namespace CFSG.ComponentClassification.SolMax

open CFSG Subgroup

namespace Sig27

variable {G : Type} [Group G] [Finite G]

theorem mem_normalizer_of_conj_mem {H : Subgroup G} {g : G}
    (h : ∀ x ∈ H, g * x * g⁻¹ ∈ H) : g ∈ normalizer (H : Set G) := by
  have hle : H.map (MulAut.conj g).toMonoidHom ≤ H := by
    rintro _ ⟨x, hx, rfl⟩
    exact h x hx
  have heq : H.map (MulAut.conj g).toMonoidHom = H :=
    Subgroup.eq_of_le_of_card_ge hle
      (le_of_eq (card_map_of_injective (MulAut.conj g).injective).symm)
  rw [mem_normalizer_iff]
  intro x
  constructor
  · intro hx
    exact h x hx
  · intro hx
    rw [← heq] at hx
    obtain ⟨y, hy, hyx⟩ := hx
    have hxy : x = y := by
      have h1 : g * y * g⁻¹ = g * x * g⁻¹ := hyx
      simpa using h1.symm
    rwa [hxy]

theorem exists_sylow_le_normalizer {S : Subgroup G} (hS2 : IsPGroup 2 S)
    (hSC : IsStronglyClosedIn (normalizer (S : Set G)) (S : Set G)) :
    ∃ T : Sylow 2 G, S ≤ T ∧ (T : Subgroup G) ≤ normalizer (S : Set G) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set N := normalizer (S : Set G) with hNdef
  have key : ∀ R : Subgroup G, S ≤ R → R ≤ N → ∀ x : G, x ∈ normalizer (R : Set G) → x ∈ N := by
    intro R hSR hRN x hx
    refine mem_normalizer_of_conj_mem fun a ha => ?_
    have hR : x * a * x⁻¹ ∈ R := (mem_normalizer_iff.mp hx a).mp (hSR ha)
    have h := hSC.2 a ha x⁻¹ (by rw [inv_inv]; exact hRN hR)
    rwa [inv_inv] at h
  obtain ⟨P₀, hP₀⟩ := (hS2.comap_subtype (K := N)).exists_le_sylow
  set P : Subgroup G := (P₀ : Subgroup N).map N.subtype with hPdef
  have hP2 : IsPGroup 2 P := P₀.isPGroup'.map N.subtype
  have hSP : S ≤ P := fun s hs => ⟨⟨s, le_normalizer hs⟩, hP₀ hs, rfl⟩
  have hPN : P ≤ N := map_subtype_le _
  have hmax : ∀ R : Subgroup G, IsPGroup 2 R → P ≤ R → R ≤ N → R ≤ P := by
    intro R hR hPR hRN r hr
    have h2 : (P₀ : Subgroup N) ≤ R.subgroupOf N := fun y hy => hPR ⟨y, hy, rfl⟩
    have h3 := P₀.is_maximal' (hR.comap_subtype (K := N)) h2
    have h4 : (⟨r, hRN hr⟩ : N) ∈ R.comap N.subtype := hr
    rw [h3] at h4
    exact ⟨_, h4, rfl⟩
  obtain ⟨T, hPT⟩ := hP2.exists_le_sylow
  refine ⟨T, hSP.trans hPT, ?_⟩
  set H₀ : Subgroup ↥(T : Subgroup G) := P.subgroupOf T with hH₀def
  have hnorm : normalizer (H₀ : Set ↥(T : Subgroup G)) ≤ H₀ := by
    intro x hx
    have hxP : (x : G) ∈ normalizer (P : Set G) := by
      refine mem_normalizer_of_conj_mem fun p hp => ?_
      have h1 := (mem_normalizer_iff.mp hx ⟨p, hPT hp⟩).mp hp
      exact h1
    have hxN : (x : G) ∈ N := key P hSP hPN x hxP
    have hR2 : IsPGroup 2 ↥(P ⊔ zpowers (x : G)) :=
      T.isPGroup'.to_le (sup_le hPT (zpowers_le.mpr x.2))
    exact hmax _ hR2 le_sup_left (sup_le hPN (zpowers_le.mpr hxN))
      (mem_sup_right (mem_zpowers _))
  have hnil : Group.IsNilpotent ↥(T : Subgroup G) := T.isPGroup'.isNilpotent
  have hnc := Group.normalizerCondition_of_isNilpotent (G := ↥(T : Subgroup G))
  rw [normalizerCondition_iff_only_full_group_self_normalizing] at hnc
  have hH₀ : H₀ = ⊤ := hnc H₀ (le_antisymm hnorm le_normalizer)
  intro y hy
  have h1 : (⟨y, hy⟩ : ↥(T : Subgroup G)) ∈ H₀ := by rw [hH₀]; exact mem_top _
  exact hPN h1

end Sig27

theorem stronglyClosedResidualInput_holds :
    Sol78.StronglyClosedResidualInput := by
  intro G _ _ S hS2 hSC
  obtain ⟨T, hST, hTN⟩ := Sig27.exists_sylow_le_normalizer hS2 hSC
  have hfs : Open.fusionStronglyClosed (S : Set G) T := fun a ha g hg => hSC.2 a ha g (hTN hg)
  have h := Goldschmidt75.corollaryB1 T hST hfs
  rwa [Goldschmidt.goldschmidtOddCore_eq_pPrimeCore] at h

end CFSG.ComponentClassification.SolMax
