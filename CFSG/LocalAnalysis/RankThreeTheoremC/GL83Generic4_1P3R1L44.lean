module

public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic4_1P3M11Defs
public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic4_1P3Shadow
import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic4_1P3R1L44b
import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic4_1P3R1L44c
import CFSG.LocalAnalysis.RankThreeTheoremC.GenericCaseSetup
import CFSG.LocalAnalysis.RankThreeTheoremC.InvariantTwoConstrained
public import CFSG.LocalAnalysis.ABGTheoremB.Basic
public import CFSG.LocalAnalysis.AGLEmbeddingD2.PairMaximal

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers CFSG.ABGLocalTools CFSG.AGLEmbedding Subgroup

variable {G : Type} [Group G] [Finite G]

theorem m11_not_two_dvd_card (hS : Setting G) (hU0 : FullCoreLocal G) (hD1 : TheoremD1 G)
    (hKM : CFSG.AGLEmbeddingD2.KFactM11Three)
    (hp : 3 ∈ rankThreeSigmaA G) {P : Sylow 3 G} {M : Subgroup G} (hM : IsCoreMaxLocal 3 P M)
    {x : G} (hgen : IsGenericPoint 3 P M x) {J : Subgroup G} (hJ : IsM11Normal M x J)
    (hD3 : IsPGroup 3 (reducedCentralizerOfJ x J)) :
    ¬ 2 ∣ Nat.card ↥(GLBPrimeCore 3 M ⊓ centralizer ({x} : Set G)) := by
  obtain ⟨Sbar, -, hsh⟩ := exists_genericShadow3 hS hU0 hp rfl hM hgen
  set C : Subgroup G := centralizer ({x} : Set G)
  set O : Subgroup C := primeComplementCore (G := C) 3
  set π : C →* C ⧸ O := QuotientGroup.mk' O
  set Γ : Subgroup (C ⧸ O) := ((C ⊓ M).subgroupOf C).map π
  have hJC : J ≤ C := hJ.le_centralizer
  have hCJ : C ≤ normalizer (J : Set G) := hJ.centralizer_le
  set L : Subgroup (C ⧸ O) := (J.subgroupOf C).map π
  have hLn : L.Normal :=
    ((Subgroup.normal_subgroupOf_iff_le_normalizer hJC).mpr hCJ).map π
      (QuotientGroup.mk'_surjective O)
  obtain ⟨Q, hQ, ψ, hψ, hker, ⟨eQ⟩⟩ := hJ.iso
  obtain ⟨eL⟩ := l44_nonempty_mulEquiv_map hJC hCJ ψ hψ hker
  obtain ⟨hout, hsyl⟩ := hKM ↥L ⟨eL.trans eQ⟩
  have hdec := l44_decomp L hout
  have hD3' : IsPGroup 3 ↥(centralizer (L : Set (C ⧸ O))) := hD3
  have hDS : centralizer (L : Set (C ⧸ O)) ≤ (Sbar : Subgroup (C ⧸ O)) :=
    hD3'.le_sylow_of_normal Sbar
  have hΓ : Γ ≠ ⊤ := hsh.ne_top
  have hNΓ : normalizer ((Sbar : Subgroup (C ⧸ O)) : Set (C ⧸ O)) ≤ Γ :=
    hsh.normalizer_le _ le_rfl (by rw [hsh.rank_eq]; norm_num)
  obtain ⟨T, hT⟩ := CFSG.Walter.exists_sylow_map_eq_inf_of_isSubnormal Sbar hLn.isSubnormal
  obtain ⟨-, hCT, hmaxT⟩ := hsyl T
  have hC' : ∀ ℓ ∈ L, (∀ s ∈ (Sbar : Subgroup (C ⧸ O)) ⊓ L, ℓ * s = s * ℓ) →
      ℓ ∈ (Sbar : Subgroup (C ⧸ O)) := by
    intro ℓ hℓ hcomm
    have h1 : (⟨ℓ, hℓ⟩ : L) ∈ centralizer ((T : Subgroup L) : Set L) := by
      rw [mem_centralizer_iff]
      intro t ht
      refine Subtype.ext (hcomm t ?_).symm
      rw [← hT]
      exact ⟨t, ht, rfl⟩
    have h2 : ℓ ∈ (Sbar : Subgroup (C ⧸ O)) ⊓ L := by
      rw [← hT]
      exact ⟨⟨ℓ, hℓ⟩, hCT h1, rfl⟩
    exact h2.1
  have hmax' : ∀ Z : Subgroup (C ⧸ O), Z ≤ L →
      L ⊓ normalizer (((Sbar : Subgroup (C ⧸ O)) ⊓ L : Subgroup (C ⧸ O)) : Set (C ⧸ O)) ≤ Z →
      Z ≤ L ⊓ normalizer (((Sbar : Subgroup (C ⧸ O)) ⊓ L : Subgroup (C ⧸ O)) : Set (C ⧸ O)) ∨
        L ≤ Z := by
    intro Z hZL hNZ
    have hle : normalizer (T : Set L) ≤ Z.subgroupOf L := by
      intro n hn
      have h1 := Subgroup.le_normalizer_map L.subtype ⟨n, hn, rfl⟩
      rw [hT] at h1
      exact hNZ ⟨n.2, h1⟩
    rcases hmaxT (Z.subgroupOf L) hle with h | h
    · refine Or.inl fun z hz => ⟨hZL hz, ?_⟩
      have h2 : (⟨z, hZL hz⟩ : L) ∈ Z.subgroupOf L := hz
      rw [h] at h2
      have h3 := Subgroup.le_normalizer_map L.subtype ⟨⟨z, hZL hz⟩, h2, rfl⟩
      rwa [hT] at h3
    · exact Or.inr fun l hl => (h ▸ mem_top (⟨l, hl⟩ : L) : (⟨l, hl⟩ : L) ∈ Z.subgroupOf L)
  set E : Subgroup (C ⧸ O) := ((GLBPrimeCore 3 M ⊓ C).subgroupOf C).map π
  have hEΓ : E ≤ Γ := by
    refine Subgroup.map_mono fun c hc => ?_
    have hc' := Subgroup.mem_subgroupOf.mp hc
    exact Subgroup.mem_subgroupOf.mpr ⟨hc'.2, glbPrimeCore_le 3 M hc'.1⟩
  have hEn : ∀ g ∈ Γ, ∀ e ∈ E, g * e * g⁻¹ ∈ E := by
    rintro g ⟨m, hm, rfl⟩ e ⟨c, hc, rfl⟩
    refine ⟨m * c * m⁻¹, ?_, by simp only [map_mul, map_inv]⟩
    have hm' := Subgroup.mem_subgroupOf.mp hm
    have hc' := Subgroup.mem_subgroupOf.mp hc
    exact Subgroup.mem_subgroupOf.mpr ⟨(Subgroup.mem_normalizer_iff.mp
      (le_normalizer_glbPrimeCore 3 M hm'.2) (c : G)).mp hc'.1, (m * c * m⁻¹).2⟩
  have hE3 : ∀ e ∈ E, Nat.Coprime 3 (orderOf e) := by
    rintro e ⟨c, hc, rfl⟩
    have hcM : (c : G) ∈ GLBPrimeCore 3 M := (Subgroup.mem_subgroupOf.mp hc).1
    have h1 : orderOf (π c) ∣ orderOf (c : G) := by
      rw [Subgroup.orderOf_coe]
      exact orderOf_map_dvd π c
    have h2 : orderOf (c : G) ∣ Nat.card (GLBPrimeCore 3 M) := by
      have h3 := orderOf_dvd_natCard (⟨c, hcM⟩ : GLBPrimeCore 3 M)
      rwa [Subgroup.orderOf_mk] at h3
    exact (glbPrimeCore_coprime 3 M).coprime_dvd_right (h1.trans h2)
  have hEbot : E = ⊥ :=
    l44_eq_bot hdec hDS Sbar.isPGroup' hΓ hNΓ hC' hmax' hEΓ hEn hE3
  intro hdvd
  obtain ⟨c, hc⟩ := exists_prime_orderOf_dvd_card' 2 hdvd
  have hcC : (c : G) ∈ C := c.2.2
  have h1 : π ⟨c, hcC⟩ = 1 := by
    have h2 : π ⟨c, hcC⟩ ∈ E := ⟨⟨c, hcC⟩, Subgroup.mem_subgroupOf.mpr c.2, rfl⟩
    rw [hEbot] at h2
    exact mem_bot.mp h2
  have hcO : (c : G) ∈ GLBPrimeCore 3 C :=
    (mk'_primeComplementCore_eq_one_iff 3 (⟨c, hcC⟩ : C)).mp h1
  have hcP : (c : G) ∈ CFSG.ABGTheoremB.pPrimeCoreIn 3 C := glbPrimeCore_le_pPrimeCoreIn 3 C hcO
  refine odd_card_pPrimeCoreIn_of_not_le hS hD1 hp hM hgen.2.2.2.ge hgen.2.1.2.2.2.2 ?_
  have h3 := orderOf_dvd_natCard (⟨c, hcP⟩ : CFSG.ABGTheoremB.pPrimeCoreIn 3 C)
  rwa [Subgroup.orderOf_mk, Subgroup.orderOf_coe, hc] at h3

end CFSG.LocalAnalysis.RankThreeTheoremC
