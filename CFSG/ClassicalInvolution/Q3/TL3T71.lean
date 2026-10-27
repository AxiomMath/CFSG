module

public import CFSG.ClassicalInvolution.Q3.TL3T55
public import CFSG.ClassicalInvolution.Q3.TL3T68
public import CFSG.ClassicalInvolution.Q3.TL3T78

public section

namespace CFSG.ClassicalInvolution.Q3.TC.Thin

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Q3.TC.Graph
open CFSG.ClassicalInvolution.Q3.AE CFSG.ClassicalInvolution.Q3.AE.Wr
open CFSG.ComponentClassification.PresentationLocal Amalg

section Assembly

variable {G : Type} [Group G] {m : ℕ}

@[expose] def altAct (σ : alternatingGroup (Fin m)) (μ : Subgroup (AEQ m)) : Subgroup (AEQ m) :=
  permAct (σ : Equiv.Perm (Fin m)) μ

theorem altAct_mul (σ τ : alternatingGroup (Fin m)) (μ : Subgroup (AEQ m)) :
    altAct (σ * τ) μ = altAct σ (altAct τ μ) := permAct_mul _ _ _

theorem altAct_one (μ : Subgroup (AEQ m)) : altAct (1 : alternatingGroup (Fin m)) μ = μ :=
  permAct_one μ

theorem altAct_inv_altAct (σ : alternatingGroup (Fin m)) (μ : Subgroup (AEQ m)) :
    altAct σ⁻¹ (altAct σ μ) = μ := by
  rw [← altAct_mul, inv_mul_cancel, altAct_one]

theorem conjSub_comm_conjSub {H : Type*} [Group H] {x y : H} (h : x * y = y * x)
    (Z : Subgroup H) : conjSub x (conjSub y Z) = conjSub y (conjSub x Z) := by
  rw [← conjSub_mul, ← conjSub_mul, h]

open Classical in
@[expose] noncomputable def transMem (f : alternatingGroup (Fin m) →* G) (μ₀ : Subgroup (AEQ m))
    (M₀ : Subgroup G) (μ : Subgroup (AEQ m)) : Subgroup G :=
  if h : ∃ σ : alternatingGroup (Fin m), altAct σ μ₀ = μ then conjSub (f h.choose) M₀ else ⊥

theorem transMem_altAct {f : alternatingGroup (Fin m) →* G} {μ₀ : Subgroup (AEQ m)}
    {M₀ : Subgroup G}
    (hstab : ∀ σ : alternatingGroup (Fin m), altAct σ μ₀ = μ₀ → conjSub (f σ) M₀ = M₀)
    (σ : alternatingGroup (Fin m)) :
    transMem f μ₀ M₀ (altAct σ μ₀) = conjSub (f σ) M₀ := by
  have h : ∃ σ' : alternatingGroup (Fin m), altAct σ' μ₀ = altAct σ μ₀ := ⟨σ, rfl⟩
  unfold transMem
  rw [dif_pos h]
  have h1 : altAct (σ⁻¹ * h.choose) μ₀ = μ₀ := by
    rw [altAct_mul, h.choose_spec, altAct_inv_altAct]
  have h2 := hstab _ h1
  have h3 : f h.choose = f σ * f (σ⁻¹ * h.choose) := by rw [← map_mul, mul_inv_cancel_left]
  rw [h3, conjSub_mul, h2]

end Assembly

variable {G : Type} [Group G] [Finite G] {IH : ℕ → Prop} {Ω : Set (Subgroup G)}
  {K J : Subgroup G} {n : ℕ}

theorem CSetting.exists_moved_member (hS : CSetting 3 IH Ω K J) (hn : 5 ≤ n)
    (I : AEIdent (orbOf (TC.nbrAdj Ω) K J) n) :
    ∀ L ∈ Ω, ∃ u : G, IsUniqueInvolution L u ∧ ∃ M ∈ Ω, conjSub u M ≠ M := by
  classical
  have hC := hS.toCHyp
  have hD := hS.cex.toThmDHyp
  have hn5 : 5 ≤ n := hn
  have hH := hC.aeCoverHyp_orb' hn5 I
  have hJπ : J ∈ orbOf (TC.nbrAdj Ω) K J := mem_orbOf_self K J
  have hJΩ : J ∈ Ω := hC.orb_subset_omega hJπ
  obtain ⟨⟨u₀, hu₀⟩, -⟩ := hD.hyp.omega1 J hJΩ
  obtain ⟨α, hα, b, hlabJ⟩ := I.label J hJπ
  have hz := I.map_eq_zBar hn5 hJπ (hH.card J hJπ) hlabJ hu₀
  obtain ⟨x, hx⟩ : αᶜ.Nonempty :=
    Finset.card_pos.mp (by rw [Finset.card_compl, Fintype.card_fin, hα]; omega)
  obtain ⟨t3, ht3, hct3⟩ : ∃ t3 ⊆ α, t3.card = 3 :=
    Finset.exists_subset_card_eq (by rw [hα]; norm_num)
  have hxα : x ∉ α := Finset.mem_compl.mp hx
  have hxt3 : x ∉ t3 := fun h => hxα (ht3 h)
  have hβc : (insert x t3).card = 4 := by rw [Finset.card_insert_of_notMem hxt3, hct3]
  obtain ⟨M₁, hM₁, hlabM₁⟩ := I.label_surj (insert x t3) hβc true
  have hodd : ∑ y ∈ insert x t3, (zOf (emb α hα)).vec y = 1 := by
    have h0 : (zOf (emb α hα)).vec x = 0 := by
      rw [zOf_vec_apply]
      exact if_neg (by
        rw [range_emb]
        exact fun h => hxα (Finset.mem_coe.mp h))
    have h1 : ∀ y ∈ t3, (zOf (emb α hα)).vec y = 1 := by
      intro y hy
      rw [zOf_vec_apply]
      exact if_pos (by rw [range_emb]; exact Finset.mem_coe.mpr (ht3 hy))
    rw [Finset.sum_insert hxt3, h0, Finset.sum_congr rfl h1, Finset.sum_const, hct3, zero_add]
    decide
  have hmove : conjSub u₀ M₁ ≠ M₁ := by
    intro h
    have h1 := TL4.AECov.map_conjSub_eq I M₁ ⟨u₀, le_pSpan hJπ hu₀.mem⟩
    rw [h, hz, hlabM₁] at h1
    have h2 : conjSub (zBar α hα) (memBar (insert x t3) hβc true) =
        memBar (insert x t3) hβc false :=
      TL4.AECov.conjSub_memBar_of_odd (w := zOf (emb α hα)) (zOf_perm _) _ hβc true hodd
    rw [h2] at h1
    exact memBar_true_ne_false hn5 _ hβc h1
  intro L hL
  obtain ⟨g, hg⟩ := hS.cex.trans J hJΩ L hL
  refine ⟨g * u₀ * g⁻¹, hg ▸ hu₀.conj g, conjSub g M₁, hS.cex.hyp.conjInvariant g M₁
    (hC.orb_subset_omega hM₁), fun h => hmove ?_⟩
  rw [← conjSub_mul, show g * u₀ * g⁻¹ * g = g * u₀ by group, conjSub_mul] at h
  exact conjSub_injective g h

end CFSG.ClassicalInvolution.Q3.TC.Thin
