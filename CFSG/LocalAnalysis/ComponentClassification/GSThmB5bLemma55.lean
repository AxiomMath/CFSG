module

public import CFSG.LocalAnalysis.ComponentClassification.GSThmB5bTable
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB5bZStar
import CFSG.Adapters.StatedPSLTwo
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB5bBasic

public section

namespace CFSG.ComponentClassification.GSThmB

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer

theorem center_eq_bot_of_isSimpleGroup_of_isQuasisimple {G : Type*} [Group G] [IsSimpleGroup G]
    (hq : IsQuasisimple G) : center G = ⊥ := by
  rcases (inferInstance : (center G).Normal).eq_bot_or_eq_top with h | h
  · exact h
  · exfalso
    obtain ⟨-, -, a, b, hab⟩ := hq
    apply hab
    have : Subsingleton (G ⧸ center G) := by
      rw [h]
      exact QuotientGroup.subsingleton_quotient_top
    exact Subsingleton.elim _ _

theorem center_eq_bot_of_mulEquiv_alternating {G : Type*} [Group G] {n : ℕ} (hn : 4 ≤ n)
    (e : G ≃* alternatingGroup (Fin n)) : center G = ⊥ := by
  rw [eq_bot_iff]
  intro y hy
  have hcen : e y ∈ center (alternatingGroup (Fin n)) := by
    rw [Subgroup.mem_center_iff]
    intro z
    obtain ⟨w, rfl⟩ := e.surjective z
    rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.mp hy w]
  rw [alternatingGroup.center_eq_bot (by simpa using hn)] at hcen
  have : e y = e 1 := by rw [map_one]; exact mem_bot.mp hcen
  exact mem_bot.mpr (e.injective this)

theorem isSimpleGroup_of_lieModel_psl_two {X : Type} [Group X] {p f : ℕ}
    (hL : Blueprint.LieModel X .PSL 2 p f) : IsSimpleGroup X :=
  CFSG.Blueprint.LieModel.isSimpleGroup_psl_two hL

namespace Hyp52

variable {H : Type} [Group H] [Finite H] (h : Hyp52 H)

theorem conj_mem_D_inf_P {s y : H} (hs : s ∈ h.S) (hy : y ∈ h.D ⊓ h.P) :
    s * y * s⁻¹ ∈ h.D ⊓ h.P := by
  obtain ⟨hyD, hyP⟩ := mem_inf.mp hy
  have hsN := h.S_le_normalizer hs
  refine mem_inf.mpr ⟨mem_inf.mpr ⟨mul_mem (mul_mem hs (h.D_le_S hyD)) (inv_mem hs),
    (mem_normalizer_iff.mp hsN y).mp (h.D_le_J hyD)⟩, mem_inf.mpr ⟨mul_mem (mul_mem hs
      (h.P_le_S hyP)) (inv_mem hs), ?_⟩⟩
  have := GSThmB.conj_mem_coreActionKernel (inv_mem hsN) (mem_inf.mp hyP).2
  rwa [inv_inv] at this

theorem D_inf_P_le_B_of_suz (hB6 : SylowKernelStatement) (hCF : CFProp24c)
    (hJ : Blueprint.LieModel (ZStarBar h.J) .PSL 3 2 2) (hKa : conjugate h.K h.a = h.K)
    (hZ : center (OddBar h.K) ≠ ⊥)
    (hSuz : Nonempty (ZStarBar h.K ≃* Blueprint.NativeSporadic.Suz)) : h.D ⊓ h.P ≤ h.B := by
  have hle := (hCF H h hJ hKa hZ hSuz).2
  set JB := GSLit.fixedLayer h.J h.B with hJB
  have hcore := (GSLit.fixedLayer_sup_pPrimeCore h.isQuasisimple_J h.B_le_coreActionKernel
    h.isPGroup_B).2
  intro y hy
  obtain ⟨hyD, hyP⟩ := mem_inf.mp hy
  have hy2 := h.orderOf_eq_two_pow_of_mem_S (h.D_le_S hyD)
  have hyCB : y ∈ centralizer (h.B : Set H) := mem_centralizer_iff.mpr fun b hb =>
    (h.D_comm_P hyD (h.B_le_P hb)).symm
  have hyJB : y ∈ JB := by
    rw [hJB, GSLit.fixedLayer_eq_closure h.isQuasisimple_J h.B_le_coreActionKernel
      h.isPGroup_B]
    exact subset_closure ⟨mem_inf.mpr ⟨h.D_le_J hyD, hyCB⟩, hy2⟩
  have hyC : y ∈ coreActionKernel JB := by
    refine mem_coreActionKernel.mpr ⟨le_normalizer hyJB, fun j hj => ?_⟩
    have hjJ : j ∈ h.J := (mem_inf.mp (GSLit.fixedLayer_le_inf _ _ hj)).1
    have h1 := (mem_coreActionKernel.mp (mem_inf.mp hyP).2).2 j hjJ
    have h2 : j⁻¹ * y⁻¹ * j * y ∈ JB :=
      mul_mem (mul_mem (mul_mem (inv_mem hj) (inv_mem hyJB)) hj) hyJB
    rw [hcore]
    exact mem_inf.mpr ⟨h2, h1⟩
  have hyZ : y ∈ (Open.fusionZStar ↥JB).map JB.subtype := by
    rw [map_fusionZStar_eq]
    exact mem_inf.mpr ⟨hyJB, hyC⟩
  have hyZK := hle hyZ
  rw [map_fusionZStar_eq] at hyZK
  have hyCV : y ∈ coreActionKernel h.V := by
    rw [h.V_eq_K hKa]
    exact (mem_inf.mp hyZK).2
  have hyW : y ∈ h.W := (mem_inf.mp (h.D_le_Q hyD)).2
  obtain ⟨hBV, hsyl⟩ := hB6 H h
  exact mem_of_sylow_of_mem_normalizer hsyl hBV hyCV hyW hy2

theorem not_suz (hB6 : SylowKernelStatement) (hCF : CFProp24c) :
    ¬ (Blueprint.LieModel (ZStarBar h.J) .PSL 3 2 2 ∧ conjugate h.K h.a = h.K ∧
      center (OddBar h.K) ≠ ⊥ ∧ Nonempty (ZStarBar h.K ≃* Blueprint.NativeSporadic.Suz)) := by
  rintro ⟨hJ, hKa, hZ, hSuz⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hDPB := h.D_inf_P_le_B_of_suz hB6 hCF hJ hKa hZ hSuz
  have hbot : ∀ y ∈ h.D ⊓ h.P, y = 1 := by
    intro y hy
    have hyx : y ∈ conjugate h.B h.x := by
      rw [mem_conjugate_iff]
      exact hDPB (h.conj_mem_D_inf_P h.x_mem hy)
    have := h.inf_conjugate_x ▸ mem_inf.mpr ⟨hDPB hy, hyx⟩
    exact mem_bot.mp this
  obtain ⟨heven, -⟩ := hCF H h hJ hKa hZ hSuz
  obtain ⟨hsup, hcore⟩ := GSLit.fixedLayer_sup_pPrimeCore h.isQuasisimple_J
    h.B_le_coreActionKernel h.isPGroup_B
  set JB := GSLit.fixedLayer h.J h.B with hJB
  obtain ⟨t, ht⟩ := exists_prime_orderOf_dvd_card' (G := Open.fusionZStar ↥JB) 2
    (even_iff_two_dvd.mp heven)
  set t' : H := ((t : ↥JB) : H) with ht'
  have ht'2 : orderOf t' = 2 := by
    rw [ht', Subgroup.orderOf_coe, Subgroup.orderOf_coe, ht]
  have ht'Z : t' ∈ JB ⊓ coreActionKernel JB := by
    rw [← map_fusionZStar_eq]
    exact mem_map_of_mem _ t.2
  obtain ⟨ht'JB, ht'C⟩ := mem_inf.mp ht'Z
  have ht'J : t' ∈ h.J := (mem_inf.mp (GSLit.fixedLayer_le_inf _ _ ht'JB)).1
  have ht'CJ : t' ∈ coreActionKernel h.J := by
    refine mem_coreActionKernel_of_sup (fun j hj => (mem_inf.mp
      (GSLit.fixedLayer_le_inf _ _ hj)).1) hsup (le_normalizer ht'J) fun j hj => ?_
    have h1 := (mem_coreActionKernel.mp ht'C).2 j hj
    rw [hcore] at h1
    exact (mem_inf.mp h1).2
  have hM : t' ∈ centralizer ({h.a} : Set H) ⊓ normalizer (h.J : Set H) :=
    mem_inf.mpr ⟨h.J_le ht'J, le_normalizer ht'J⟩
  have h2 : IsPGroup 2 (zpowers t') :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, ht'2, pow_one])
  obtain ⟨m, hm, hmS⟩ := exists_conjugate_le_of_sylow h.S_sylow (zpowers_le.mpr hM) h2
  have hmN : m ∈ normalizer (h.J : Set H) := (mem_inf.mp hm).2
  have hu : m⁻¹ * t' * m ∈ h.D ⊓ h.P := by
    have huS : m⁻¹ * t' * m ∈ h.S := hmS (by
      rw [mem_conjugate_iff, show m * (m⁻¹ * t' * m) * m⁻¹ = t' by group]
      exact mem_zpowers t')
    refine mem_inf.mpr ⟨mem_inf.mpr ⟨huS, ?_⟩, mem_inf.mpr ⟨huS,
      GSThmB.conj_mem_coreActionKernel hmN ht'CJ⟩⟩
    have := (mem_normalizer_iff.mp (inv_mem hmN) t').mp ht'J
    rwa [inv_inv] at this
  have h1 := hbot _ hu
  have : t' = 1 := by
    calc t' = m * (m⁻¹ * t' * m) * m⁻¹ := by group
      _ = 1 := by rw [h1]; group
  rw [this, orderOf_one] at ht'2
  exact absurd ht'2 (by norm_num)

theorem center_eq_bot (hB1 : ConjFixStatement) (hB6 : SylowKernelStatement)
    (hCF23 : CFProp23Fusion) (hCF24 : CFProp24c) : center (OddBar h.J) = ⊥ := by
  have hq := h.isQuasisimple_J
  have lie : ∀ {p f : ℕ}, Blueprint.LieModel (OddBar h.J) .PSL 2 p f →
      center (OddBar h.J) = ⊥ := fun hL => by
    have := isSimpleGroup_of_lieModel_psl_two hL
    exact center_eq_bot_of_isSimpleGroup_of_isQuasisimple hq
  rcases h.table hB1 hCF23 with ⟨n, hn, ⟨e⟩, -⟩ | ⟨hJ | hJ, -⟩ | h3 |
      ⟨p, f, -, -, -, hJ, -⟩ | ⟨p, f, -, -, -, -, hJ, -⟩ | ⟨p, f, -, -, -, -, hJ, -⟩ |
      ⟨p, f, -, -, -, hJ, -⟩
  · exact center_eq_bot_of_mulEquiv_alternating (by omega) e
  · exact lie hJ
  · exact lie hJ
  · exact absurd h3 (h.not_suz hB6 hCF24)
  · exact lie hJ
  · exact lie hJ
  · exact lie hJ
  · exact lie hJ

end Hyp52

end CFSG.ComponentClassification.GSThmB
