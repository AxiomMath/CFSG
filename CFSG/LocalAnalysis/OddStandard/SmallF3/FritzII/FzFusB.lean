module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.FritzII.FzFusP
public import CFSG.LocalAnalysis.OddStandard.SmallF3.FritzII.FzFusDefs

public section

namespace CFSG.OddStandard.SmallF3.FritzII

open Subgroup CFSG.OddStandard.SmallF3.HarrisU33
  CFSG.ComponentClassification.AschbacherTheorem5.DeltaLocal

section

variable {G : Type} [Group G] [Finite G] {t : G} {L S T₂ : Subgroup G}
  {x₁ x₂ lam rho tau a₁₂ a₂₂ a₃₂ : G}

theorem exists_conj_sylow_transport {T : Subgroup G} (hT : FzSylow T) {z i c₀ : G}
    (hz : T ≤ centralizer ({z} : Set G)) (hc₀ : c₀ * z * c₀⁻¹ = i) {D : Subgroup G} (hDT : D ≤ T)
    (hDi : D ≤ centralizer ({i} : Set G)) :
    ∃ g : G, g * i * g⁻¹ = z ∧ ∀ d ∈ D, g * d * g⁻¹ ∈ T := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set C := centralizer ({z} : Set G)
  have hTC : IsPGroup 2 (T.subgroupOf C) :=
    hT.1.comap_of_injective C.subtype Subtype.val_injective
  have hidx : ¬ 2 ∣ (T.subgroupOf C).index := by
    intro h2; apply hT.2
    rw [← Subgroup.relIndex_mul_index hz]
    exact Dvd.dvd.mul_right h2 _
  let SC : Sylow 2 C := hTC.toSylow hidx
  have hmemC : ∀ d ∈ D, c₀⁻¹ * d * c₀ ∈ C := fun d hd => by
    have hdi : d * i = i * d := mem_centralizer_singleton_iff.mp (hDi hd)
    rw [mem_centralizer_singleton_iff]
    have hz' : z = c₀⁻¹ * i * c₀ := by rw [← hc₀]; group
    rw [hz']
    calc c₀⁻¹ * d * c₀ * (c₀⁻¹ * i * c₀) = c₀⁻¹ * (d * i) * c₀ := by group
      _ = c₀⁻¹ * (i * d) * c₀ := by rw [hdi]
      _ = c₀⁻¹ * i * c₀ * (c₀⁻¹ * d * c₀) := by group
  let E : Subgroup C := (D.map (MulAut.conj c₀⁻¹).toMonoidHom).subgroupOf C
  have hE : IsPGroup 2 E :=
    ((hT.1.to_le hDT).map _).comap_of_injective C.subtype Subtype.val_injective
  obtain ⟨Q, hQ⟩ := hE.exists_le_sylow
  obtain ⟨k, rfl⟩ := MulAction.exists_smul_eq C SC Q
  have hk : (k : G) * z = z * k := mem_centralizer_singleton_iff.mp k.2
  refine ⟨(k : G)⁻¹ * c₀⁻¹, ?_, fun d hd => ?_⟩
  · have hz' : z = c₀⁻¹ * i * c₀ := by rw [← hc₀]; group
    calc (k : G)⁻¹ * c₀⁻¹ * i * ((k : G)⁻¹ * c₀⁻¹)⁻¹ = (k : G)⁻¹ * (c₀⁻¹ * i * c₀) * k := by group
      _ = (k : G)⁻¹ * (k * z) := by rw [← hz', mul_assoc, hk]
      _ = z := by group
  · have he : (⟨c₀⁻¹ * d * c₀, hmemC d hd⟩ : C) ∈ E := by
      rw [Subgroup.mem_subgroupOf]
      exact ⟨d, hd, by simp [MulAut.conj_apply]⟩
    have hQe := hQ he
    rw [Sylow.coe_subgroup_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem] at hQe
    have hmem : (MulAut.conj k)⁻¹ • (⟨c₀⁻¹ * d * c₀, hmemC d hd⟩ : C) ∈ T.subgroupOf C := by
      simpa [SC] using hQe
    rw [Subgroup.mem_subgroupOf] at hmem
    have h1 : (((MulAut.conj k)⁻¹ • (⟨c₀⁻¹ * d * c₀, hmemC d hd⟩ : C) : C) : G) =
        (k : G)⁻¹ * c₀⁻¹ * d * ((k : G)⁻¹ * c₀⁻¹)⁻¹ := by
      rw [MulAut.smul_def, MulAut.conj_inv_apply]; simp; group
    rw [← h1]; exact hmem

theorem le_centralizer_z₃ (hs : FzSpShape t x₁ x₂ lam T₂ a₁₂ a₂₂ a₃₂) (ht : t ^ 2 = 1)
    (htu : t * (x₁ * x₂) = (x₁ * x₂) * t) :
    T₂ ≤ centralizer ({(x₁ * x₂) ^ 2} : Set G) := by
  set a := (x₁ * x₂)⁻¹ * t
  have hza : (x₁ * x₂) ^ 2 = (a ^ 2)⁻¹ := by
    have htu' : t * (x₁ * x₂)⁻¹ = (x₁ * x₂)⁻¹ * t := by
      calc t * (x₁ * x₂)⁻¹ = (x₁ * x₂)⁻¹ * ((x₁ * x₂) * t) * (x₁ * x₂)⁻¹ := by group
        _ = (x₁ * x₂)⁻¹ * (t * (x₁ * x₂)) * (x₁ * x₂)⁻¹ := by rw [htu]
        _ = (x₁ * x₂)⁻¹ * t := by group
    have ht' : t * t = 1 := by rw [← pow_two]; exact ht
    simp only [a, pow_two]
    calc (x₁ * x₂) * (x₁ * x₂) = ((x₁ * x₂)⁻¹ * ((t * (x₁ * x₂)⁻¹) * t))⁻¹ := by
          rw [htu', mul_assoc (x₁ * x₂)⁻¹ t, ht']; group
      _ = ((x₁ * x₂)⁻¹ * t * ((x₁ * x₂)⁻¹ * t))⁻¹ := by group
  have key : ∀ w : G, Commute w a → w ∈ centralizer ({(x₁ * x₂) ^ 2} : Set G) := fun w hw => by
    rw [mem_centralizer_singleton_iff, hza]
    exact ((hw.pow_right 2).inv_right).eq
  obtain ⟨-, hq, -, -⟩ := hs.quat₃
  rw [hs.gen, closure_le]
  intro w hw
  rw [SetLike.mem_coe]
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hw
  rcases hw with h | h | h | h | h | h | h <;> rw [h]
  · exact key _ (hs.comm₁₃ _ (Set.mem_insert _ _) _ (Set.mem_insert _ _))
  · exact key _ (hs.comm₁₃ _ (Set.mem_insert_of_mem _ rfl) _ (Set.mem_insert _ _))
  · exact key _ (hs.comm₂₃ _ (Set.mem_insert _ _) _ (Set.mem_insert _ _))
  · exact key _ (hs.comm₂₃ _ (Set.mem_insert_of_mem _ rfl) _ (Set.mem_insert _ _))
  · exact key _ (Commute.refl _)
  · rw [mem_centralizer_singleton_iff, hza, ← hq]
    exact (((Commute.refl a₃₂).pow_right 2).inv_right).eq
  · exact key _ hs.lam_comm₃.1

theorem fz722c_of (h : FzNoPointedEmbedZ3) : Fz722c := by
  intro G _ _ t L S T₂ x₁ x₂ lam rho tau a₁₂ a₂₂ a₃₂ hs i hi hi2 hiZ hconj
  have hc := hs.ctx
  have htW : t ∈ ctxW t x₁ x₂ := mem_sup_left hc.hyp.mem_twoCore
  have hx₁W : x₁ ∈ ctxW t x₁ x₂ := mem_sup_right (subset_closure (by simp))
  have hx₂W : x₂ ∈ ctxW t x₁ x₂ := mem_sup_right (subset_closure (by simp))
  have ht : t ^ 2 = 1 := by rw [← hc.hyp.ord_t]; exact pow_orderOf_eq_one t
  have h1 := fzFus_commute_of_mem_ctxW hc htW hx₁W
  have h2 := fzFus_commute_of_mem_ctxW hc htW hx₂W
  have h12 := fzFus_commute_of_mem_ctxW hc hx₁W hx₂W
  have htu := fzFus_commute_of_mem_ctxW hc htW (mul_mem hx₁W hx₂W)
  obtain ⟨c₀, hc₀⟩ := isConj_iff.mp hconj
  obtain ⟨g, hg, hgD⟩ := exists_conj_sylow_transport hs.sylow
    (le_centralizer_z₃ hs.shape ht htu) hc₀ (D := T₂ ⊓ centralizer ({i} : Set G)) inf_le_left
    inf_le_right
  refine h G t x₁ x₂ lam T₂ a₁₂ a₂₂ a₃₂ hs.shape ht h1 h2 h12 i hi hi2 hiZ g hg ?_
  intro c hcT hci
  exact hgD c ⟨hcT, mem_centralizer_singleton_iff.mpr hci⟩
end

end CFSG.OddStandard.SmallF3.FritzII
