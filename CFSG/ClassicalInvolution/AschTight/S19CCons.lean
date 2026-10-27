module

public import CFSG.ClassicalInvolution.AschTight.S19CFus
public import CFSG.ClassicalInvolution.AschTight.S19CSec
public import CFSG.ClassicalInvolution.AschTight.S19CSwap
public import CFSG.ClassicalInvolution.AschTight.S19CGood
public import CFSG.ClassicalInvolution.AschTight.S19CMod

public section

namespace CFSG.ClassicalInvolution.Disconnected.AschTight.S19C

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.RankThreeCoreUniqueness CFSG.RankThreeCoreUniqueness.Helpers
  CFSG.ClassicalInvolution.Disconnected.AschTight.S1911

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G] [IsSimpleGroup G]
  {K : Subgroup G} {z : G} {S : Sylow 2 G} {W L : Subgroup G} {t : G} {V : Subgroup G}

theorem fusion_of_t_involution (hM1 : FactM1) (hL3 : C19_16FusL3GraphTmp p f)
    (hd : Sec19DataT p f K z S W L t V) (h9 : p ^ f ≠ 9) {b : G} (hbS : b ∈ (S : Subgroup G))
    (hb2 : b * b = 1) (hbX : b ∉ sec19X K z ⊔ centralizerModOdd ⊤ K)
    (hbt : b ∈ Subgroup.centralizer ({t} : Set G)) {u : G} {k : ℕ} (hk : 2 ≤ k)
    (hu : Subgroup.zpowers u = K ⊓ W) (huo : orderOf u = 2 ^ (k + 1))
    (hbact : (∀ x ∈ K ⊓ W, b * x * b⁻¹ = x ^ ((2 : ℤ) ^ k + 1)) ∨
      ∀ x ∈ K ⊓ W, b * x * b⁻¹ = x ^ ((2 : ℤ) ^ k - 1))
    (g : G) (hg : g * z * g⁻¹ ∈ Subgroup.centralizer ({b} : Set G)) :
    ∃ c ∈ Subgroup.centralizer ({b} : Set G), c * z * c⁻¹ = g * z * g⁻¹ := by
  have hd0 := hd.toSec19Data
  obtain ⟨e₀, -, h5, hzA, hmem, hsec⟩ :=
    sectionLieType_fieldInvolution' hd h9 hbS hb2 hbX hbt hk hu huo hbact
  obtain ⟨c, hc⟩ := fusion_of_sectionType' hM1 hd0 h5 hzA hmem (hypOmegaMod_conjFamily hd0 hzA hmem)
    (dEdgeless_conjFamily hd0 h5 hzA hmem) hsec (hL3 G K z S W hd0 h9 b hbS hb2 hbX e₀)
    ⟨g * z * g⁻¹, hg⟩ ⟨g, rfl⟩
  exact ⟨c, c.2, (congrArg Subtype.val hc).symm⟩

theorem c19_16FNe9_of' (hInv : S1916.C19_16InvTmp p f) (hM1 : FactM1)
    (hL3 : C19_16FusL3GraphTmp p f) : C19_16FNe9Tmp p f := by
  intro G _ _ _ K z S W hd hq
  by_contra hS
  obtain ⟨a₀, ha₀S, ha₀2, ha₀X⟩ := hInv G K z S W hd hq hS
  obtain ⟨a₁, ha₁S, ha₁2, ha₁X, Q, hQS, hQa, hQnc, hQ8, hQcard⟩ :=
    exists_good_involution hd hq ha₀S ha₀2 ha₀X
  obtain ⟨W₀, hd₀, -, -, η, hη, hηS, -, hW₀⟩ := S1916.exists_invariant_W hd
  obtain ⟨L, t, hdT, -⟩ := S1916.exists_good_data hd₀ hη hηS hW₀
  obtain ⟨u, k, hk, hu, huo, hact, r, hrR, hrU, hra⟩ :=
    exists_modular hdT ha₁S ha₁X hQS hQa hQnc hQ8 hQcard
  obtain ⟨b, hbS, hb2, hbX, hbt, hbact⟩ :=
    exists_t_involution hdT ha₁S ha₁2 ha₁X hu huo hact hrR hrU hra
  have hfus := fusion_of_t_involution hM1 hL3 hdT hq hbS hb2 hbX hbt hk hu huo hbact
  have hCz := hd.hSz
  refine S1916.false_of_transfer hd.tight.branch.nonabelian S
    (P := (S : Subgroup G) ⊓ (sec19X K z ⊔ centralizerModOdd ⊤ K))
    (fun s hs => S1916.mem_normalizer_inf (Subgroup.le_normalizer hs)
      (S1916.mem_normalizer_sup_cStar hd (hCz hs)))
    (fun x hx y hy => ⟨S.mul_mem (S.mul_mem (S.mul_mem hx hy) (S.inv_mem hx)) (S.inv_mem hy),
      S1916.commutator_mem_sup_cStar hd (hCz hx) (hCz hy)⟩) hbS (fun h => hbX h.2) hb2 ?_
  intro g hg
  have hgz : (g⁻¹ * b * g) * z = z * (g⁻¹ * b * g) :=
    (Subgroup.mem_centralizer_singleton_iff.mp (hCz hg))
  have hzC : g * z * g⁻¹ ∈ Subgroup.centralizer ({b} : Set G) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    calc g * z * g⁻¹ * b = g * (z * (g⁻¹ * b * g)) * g⁻¹ := by group
      _ = g * ((g⁻¹ * b * g) * z) * g⁻¹ := by rw [hgz]
      _ = b * (g * z * g⁻¹) := by group
  obtain ⟨c, hcC, hcz⟩ := hfus g hzC
  have hca : c * b = b * c := Subgroup.mem_centralizer_singleton_iff.mp hcC
  set d := c⁻¹ * g with hd'
  have hdz : d ∈ Subgroup.centralizer ({z} : Set G) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    calc d * z = c⁻¹ * (g * z * g⁻¹) * g := by rw [hd']; group
      _ = c⁻¹ * (c * z * c⁻¹) * g := by rw [hcz]
      _ = z * d := by rw [hd']; group
  have hb' : g⁻¹ * b * g = d⁻¹ * b * d := by
    have h1 : c * b * c⁻¹ = b := by rw [hca, mul_inv_cancel_right]
    calc g⁻¹ * b * g = g⁻¹ * (c * b * c⁻¹) * g := by rw [h1]
      _ = d⁻¹ * b * d := by rw [hd']; group
  refine ⟨S.mul_mem (S.inv_mem hg) hbS, ?_⟩
  have h2 := S1916.commutator_mem_sup_cStar hd (Subgroup.inv_mem _ hdz)
    (Subgroup.inv_mem _ (hCz hbS))
  have e : (g⁻¹ * b * g)⁻¹ * b = d⁻¹ * b⁻¹ * d⁻¹⁻¹ * b⁻¹⁻¹ := by
    rw [hb']
    group
  rw [e]
  exact h2

end CFSG.ClassicalInvolution.Disconnected.AschTight.S19C
