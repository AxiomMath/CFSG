module

public import CFSG.LocalAnalysis.ComponentClassification.FooteMarkedFamily
import CFSG.GroupTheory.PerfectCentralExtensionUnique

public section

namespace CFSG.ComponentClassification.FooteMarked

open CFSG Subgroup

variable {G : Type*} [Group G] [Finite G]

theorem eq_of_le_of_isQuasisimple {M K : Subgroup G} (hMK : M ≤ K)
    (hK : CFSG.IsQuasisimple ↥K) (hKO : Nontrivial (↥K ⧸ pPrimeCore 2 ↥K))
    (hcard : Nat.card (↥K ⧸ pPrimeCore 2 ↥K) ≤ Nat.card (↥M ⧸ pPrimeCore 2 ↥M)) : M = K := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let O : Subgroup ↥K := pPrimeCore 2 ↥K
  have hOnorm : O.Normal := pPrimeCore_normal (p := 2) (G := ↥K)
  haveI : O.Normal := hOnorm
  have hOcop : Nat.Coprime 2 (Nat.card O) := pPrimeCore_coprime_card (p := 2) (G := ↥K)
  have hOcenter : O ≤ Subgroup.center ↥K := by
    rcases CFSG.LocalCores.quasisimple_normal_subgroups hK hOnorm with htop | hle
    · exfalso
      have hKO' : Nontrivial (↥K ⧸ O) := hKO
      haveI : Subsingleton (↥K ⧸ O) := by
        rw [htop]
        exact QuotientGroup.subsingleton_quotient_top
      exact not_nontrivial_iff_subsingleton.mpr inferInstance hKO'
    · exact hle
  let ψ : ↥M →* ↥K ⧸ O := (QuotientGroup.mk' O).comp (Subgroup.inclusion hMK)
  have hker_odd : Nat.Coprime 2 (Nat.card ψ.ker) := by
    have hmap_le : (ψ.ker).map (Subgroup.inclusion hMK) ≤ O := by
      rw [Subgroup.map_le_iff_le_comap]
      intro y hy
      rw [Subgroup.mem_comap]
      exact (QuotientGroup.eq_one_iff _).mp (MonoidHom.mem_ker.mp hy)
    have hdvd : Nat.card ψ.ker ∣ Nat.card O := by
      rw [← Subgroup.card_map_of_injective (Subgroup.inclusion_injective hMK) (K := ψ.ker)]
      exact Subgroup.card_dvd_of_le hmap_le
    exact Nat.Coprime.of_dvd_right hdvd hOcop
  have hker_normal : ψ.ker.Normal := MonoidHom.normal_ker ψ
  have hker_le : ψ.ker ≤ pPrimeCore 2 ↥M :=
    le_sSup ⟨hker_normal, hker_odd⟩
  haveI : ψ.ker.Normal := hker_normal
  have hMquot_le : Nat.card (↥M ⧸ pPrimeCore 2 ↥M) ≤ Nat.card (↥M ⧸ ψ.ker) := by
    haveI : ψ.ker.FiniteIndex := Subgroup.finiteIndex_of_finite
    calc Nat.card (↥M ⧸ pPrimeCore 2 ↥M) = (pPrimeCore 2 ↥M).index :=
          (Subgroup.index_eq_card (pPrimeCore 2 ↥M)).symm
      _ ≤ ψ.ker.index := Subgroup.index_antitone hker_le
      _ = Nat.card (↥M ⧸ ψ.ker) := Subgroup.index_eq_card ψ.ker
  have hchain : Nat.card (↥K ⧸ O) ≤ Nat.card ψ.range := by
    calc Nat.card (↥K ⧸ O) ≤ Nat.card (↥M ⧸ pPrimeCore 2 ↥M) := hcard
      _ ≤ Nat.card (↥M ⧸ ψ.ker) := hMquot_le
      _ = ψ.ker.index := (Subgroup.index_eq_card ψ.ker).symm
      _ = Nat.card ψ.range := Subgroup.index_ker ψ
  have hrange : ψ.range = ⊤ := Subgroup.eq_top_of_le_card (H := ψ.range) hchain
  have hsup : M.subgroupOf K ⊔ O = ⊤ := by
    refine eq_top_iff.mpr ?_
    intro x _
    have hx : (QuotientGroup.mk' O) x ∈ ψ.range := by
      rw [hrange]
      exact Subgroup.mem_top _
    obtain ⟨m, hm⟩ := MonoidHom.mem_range.mp hx
    have hm' : (QuotientGroup.mk' O) (Subgroup.inclusion hMK m) = (QuotientGroup.mk' O) x := hm
    have hmem : (Subgroup.inclusion hMK m)⁻¹ * x ∈ O := by
      have h1 : (QuotientGroup.mk' O) ((Subgroup.inclusion hMK m)⁻¹ * x) = 1 := by
        rw [map_mul, map_inv, hm', inv_mul_cancel]
      exact (QuotientGroup.eq_one_iff _).mp h1
    have hmemM : Subgroup.inclusion hMK m ∈ M.subgroupOf K :=
      Subgroup.mem_subgroupOf.mpr m.property
    have hmul : Subgroup.inclusion hMK m * ((Subgroup.inclusion hMK m)⁻¹ * x) = x := by
      group
    rw [← hmul]
    exact Subgroup.mul_mem_sup hmemM hmem
  haveI : Group.IsPerfect ↥K := hK.1
  have htop : M.subgroupOf K = ⊤ :=
    CFSG.GroupTheory.eq_top_of_sup_le_center_of_isPerfect hOcenter hsup
  exact le_antisymm hMK (Subgroup.subgroupOf_eq_top.mp htop)

theorem exists_isMarkedChoice {S : Set (Subgroup G)} {T : Type*} [Group T]
    (h : ∃ X : Subgroup G, Balanced S T X) : ∃ N : Subgroup G, IsMarkedChoice S T N := by
  classical
  haveI : Finite (Subgroup G) :=
    Finite.of_injective (fun K : Subgroup G => (K : Set G)) SetLike.coe_injective
  obtain ⟨X₀, hX₀⟩ := h
  obtain ⟨N₁, hN₁, hN₁max⟩ :=
    Set.exists_max_image {X : Subgroup G | Balanced S T X} (markedCount S T)
      (Set.toFinite _) ⟨X₀, hX₀⟩
  obtain ⟨N₂, hN₂, hN₂max⟩ :=
    Set.exists_max_image
      {X : Subgroup G | Balanced S T X ∧ markedCount S T X = markedCount S T N₁}
      (fun X => CFSG.Open.twoRank ↥(wholeKernel S T X))
      (Set.toFinite _) ⟨N₁, hN₁, rfl⟩
  obtain ⟨N₃, hN₃, hN₃max⟩ :=
    Set.exists_max_image
      {X : Subgroup G | Balanced S T X ∧ markedCount S T X = markedCount S T N₁ ∧
        CFSG.Open.twoRank ↥(wholeKernel S T X) = CFSG.Open.twoRank ↥(wholeKernel S T N₂)}
      (fun X => 2 ^ (Nat.card (wholeKernel S T X)).factorization 2)
      (Set.toFinite _) ⟨N₂, hN₂.1, hN₂.2, rfl⟩
  refine ⟨N₃, hN₃.1, ?_, ?_, ?_⟩
  · intro X hX
    simpa [hN₃.2.1] using hN₁max X hX
  · intro X hX hcount
    have hXB : X ∈ {X : Subgroup G | Balanced S T X ∧ markedCount S T X = markedCount S T N₁} :=
      ⟨hX, by rw [hcount, hN₃.2.1]⟩
    simpa [hN₃.2.2] using hN₂max X hXB
  · intro X hX hcount hrank
    refine hN₃max X ⟨hX, ?_, ?_⟩
    · rw [hcount, hN₃.2.1]
    · rw [hrank, hN₃.2.2]

end CFSG.ComponentClassification.FooteMarked
