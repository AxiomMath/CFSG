module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4A.S4AB1A
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4A.S4AGenRank

public section

namespace CFSG.OddStandard.SmallF3.FritzII

open Subgroup CFSG.OddStandard.SmallF3.HarrisU33

variable {G : Type} [Group G] [Finite G] {t : G} {L S : Subgroup G} {x₁ x₂ lam rho : G}

theorem fzc_sy2_twoCore_eq (h : Ctx0 t L S x₁ x₂ lam rho) (hK : Nat.card (twoCore t) = 2) :
    twoCore t = zpowers t := by
  refine (Subgroup.eq_of_le_of_card_ge (H := zpowers t) (K := twoCore t)
    (Subgroup.zpowers_le.mpr h.hyp.mem_twoCore) ?_).symm
  rw [hK, Nat.card_zpowers, h.hyp.ord_t]

theorem fzc_sy2_twoCore_cases (h : Ctx0 t L S x₁ x₂ lam rho) (hK : Nat.card (twoCore t) = 2) :
    ∀ k ∈ twoCore t, k = 1 ∨ k = t := by
  intro k hk
  rw [fzc_sy2_twoCore_eq h hK] at hk
  exact S4A.pt_eq_one_or_of_mem_zpowers h.hyp.ord_t hk

theorem fzc_sy2_t_sq (h : Ctx0 t L S x₁ x₂ lam rho) : t ^ 2 = 1 := by
  simpa [h.hyp.ord_t] using pow_orderOf_eq_one t

theorem fzc_sy2_t_mem (h : Ctx0 t L S x₁ x₂ lam rho) : t ∈ ctxW t x₁ x₂ :=
  Subgroup.mem_sup_left h.hyp.mem_twoCore

theorem fzc_sy2_t_notin_E (h : Ctx0 t L S x₁ x₂ lam rho) : t ∉ baseGrp x₁ x₂ := by
  intro ht
  have hmem : t ∈ twoCore t ⊓ baseGrp x₁ x₂ := ⟨h.hyp.mem_twoCore, ht⟩
  rw [S4A.pt_inf_base h, Subgroup.mem_bot] at hmem
  have h1 : orderOf t = 1 := orderOf_eq_one_iff.mpr hmem
  rw [h.hyp.ord_t] at h1
  norm_num at h1

theorem fzc_sy2_W_comm (h : Ctx0 t L S x₁ x₂ lam rho) :
    ∀ a ∈ ctxW t x₁ x₂, ∀ b ∈ ctxW t x₁ x₂, a * b = b * a := by
  intro a ha b hb
  exact congrArg Subtype.val (isMulCommutative_iff.mp h.abelian_W ⟨a, ha⟩ ⟨b, hb⟩)

theorem fzc_sy2_card_W (h : Ctx0 t L S x₁ x₂ lam rho) (hK : Nat.card (twoCore t) = 2) :
    Nat.card (ctxW t x₁ x₂) = 32 := by
  rw [S4A.pt_card_W h, hK]
  norm_num

theorem fzc_sy2_W_split (h : Ctx0 t L S x₁ x₂ lam rho) (hK : Nat.card (twoCore t) = 2) :
    ∀ w ∈ ctxW t x₁ x₂, w ∈ baseGrp x₁ x₂ ∨ t * w ∈ baseGrp x₁ x₂ := by
  have htt : t * t = 1 := S4A.t_mul_self h.hyp
  intro w hw
  obtain ⟨p, hp, b, hb, rfl⟩ := (mem_sup_iff_of_commute (S4A.pt_comm_base h)).mp hw
  rcases fzc_sy2_twoCore_cases h hK p hp with h1 | h1
  · left
    rw [h1, one_mul]
    exact hb
  · right
    have h2 : t * (t * b) = b := by rw [← mul_assoc, htt, one_mul]
    rw [h1, h2]
    exact hb

theorem fzc_sy2_E_sq (h : Ctx0 t L S x₁ x₂ lam rho) :
    ∀ e ∈ baseGrp x₁ x₂, e ^ 2 ∈ fourGrp x₁ x₂ := by
  intro e he
  rw [WreathRel.fourGrp_eq_mho h.wreath]
  exact Subgroup.subset_closure ⟨e, he, rfl⟩

theorem fzc_sy2_E_invol (h : Ctx0 t L S x₁ x₂ lam rho) :
    ∀ e ∈ baseGrp x₁ x₂, e ^ 2 = 1 → e ∈ fourGrp x₁ x₂ := by
  intro e he he2
  rw [(WreathRel.fourGrp_eq_omega h.wreath).1]
  exact Subgroup.subset_closure ⟨he, he2⟩

theorem fzc_sy2_Z_sqrt (h : Ctx0 t L S x₁ x₂ lam rho) :
    ∀ z ∈ fourGrp x₁ x₂, ∃ e ∈ baseGrp x₁ x₂, e ^ 2 = z := by
  have hEcomm : IsMulCommutative (baseGrp x₁ x₂) := (h.wreath.baseGrp_eq).1
  have hmemE : ∀ a ∈ baseGrp x₁ x₂, ∀ b ∈ baseGrp x₁ x₂, a * b = b * a := by
    intro a ha b hb
    exact congrArg Subtype.val (isMulCommutative_iff.mp hEcomm ⟨a, ha⟩ ⟨b, hb⟩)
  intro z hz
  rw [fourGrp] at hz
  refine Subgroup.closure_induction
    (p := fun x _ => ∃ e ∈ baseGrp x₁ x₂, e ^ 2 = x) ?_ ?_ ?_ ?_ hz
  · intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl
    · exact ⟨x₁, Subgroup.subset_closure (by simp), rfl⟩
    · exact ⟨x₁ * x₂, Subgroup.mul_mem _
        (Subgroup.subset_closure (by simp)) (Subgroup.subset_closure (by simp)), rfl⟩
  · exact ⟨1, Subgroup.one_mem _, by simp⟩
  · intro a b _ _ iha ihb
    obtain ⟨ea, hea, rfl⟩ := iha
    obtain ⟨eb, heb, rfl⟩ := ihb
    exact ⟨ea * eb, Subgroup.mul_mem _ hea heb,
      (show Commute ea eb from hmemE ea hea eb heb).mul_pow 2⟩
  · intro a _ iha
    obtain ⟨ea, hea, rfl⟩ := iha
    exact ⟨ea⁻¹, Subgroup.inv_mem _ hea, by rw [inv_pow]⟩

theorem fzc_sy2_rho_nrm_W (h : Ctx0 t L S x₁ x₂ lam rho) :
    ∀ w ∈ ctxW t x₁ x₂, rho * w * rho⁻¹ ∈ ctxW t x₁ x₂ :=
  fun w hw => (Subgroup.mem_normalizer_iff.mp h.rho_normalizes w).mp hw

theorem fzc_sy2_rho_nrm_E (h : Ctx0 t L S x₁ x₂ lam rho) :
    ∀ e ∈ baseGrp x₁ x₂, rho * e * rho⁻¹ ∈ baseGrp x₁ x₂ := by
  have hWmap_le : (ctxW t x₁ x₂).map (MulAut.conj rho) ≤ ctxW t x₁ x₂ := by
    rw [Subgroup.map_le_iff_le_comap]
    intro w hw
    simpa [MulAut.conj_apply] using fzc_sy2_rho_nrm_W h w hw
  have hWmap_eq : (ctxW t x₁ x₂).map (MulAut.conj rho) = ctxW t x₁ x₂ := by
    refine le_antisymm hWmap_le ?_
    intro w hw
    refine Subgroup.mem_map.mpr ⟨rho⁻¹ * w * rho, ?_, ?_⟩
    · simpa [MulAut.conj_apply] using
        (Subgroup.mem_normalizer_iff.mp
          ((Subgroup.normalizer ((ctxW t x₁ x₂ : Subgroup G) : Set G)).inv_mem
            h.rho_normalizes) w).mp hw
    · change rho * (rho⁻¹ * w * rho) * rho⁻¹ = w
      group
  have hzpmap : (zpowers rho).map (MulAut.conj rho) = zpowers rho := by
    rw [MonoidHom.map_zpowers]
    congr 1
    change rho * rho * rho⁻¹ = rho
    group
  have hmap : (baseGrp x₁ x₂).map (MulAut.conj rho) = baseGrp x₁ x₂ := by
    have h1 := congrArg
      (fun K : Subgroup G => K.map (MulAut.conj rho : G →* G)) h.comm_rho.symm
    rw [h1, Subgroup.map_commutator, hWmap_eq, hzpmap, h.comm_rho]
  intro e he
  have hmem : (MulAut.conj rho) e ∈ baseGrp x₁ x₂ := by
    rw [← hmap]
    exact Subgroup.mem_map.mpr ⟨e, he, rfl⟩
  simpa [MulAut.conj_apply] using hmem

theorem fzc_sy2_rho_t (h : Ctx0 t L S x₁ x₂ lam rho) : rho * t * rho⁻¹ = t := by
  have ht : t ∈ ctxW t x₁ x₂ ⊓ centralizer ({rho} : Set G) := by
    rw [h.cent_rho]
    exact h.hyp.mem_twoCore
  have h1 : t * rho = rho * t := Subgroup.mem_centralizer_singleton_iff.mp ht.2
  rw [← h1]
  group

theorem fzc_sy2_W_rank (h : Ctx0 t L S x₁ x₂ lam rho) : S4A.RankLE (ctxW t x₁ x₂) 3 := by
  haveI := h.hyp.isCyclic
  have hcomm12 : ∀ u ∈ zpowers x₁, ∀ v ∈ zpowers x₂, u * v = v * u := by
    intro u hu v hv
    obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp hu
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hv
    exact ((show Commute x₁ x₂ from h.wreath.comm).zpow_zpow m n).eq
  have hB : S4A.RankLE (baseGrp x₁ x₂) 2 := by
    have := S4A.RankLE.sup hcomm12 (S4A.RankLE.of_isCyclic (K := zpowers x₁))
      (S4A.RankLE.of_isCyclic (K := zpowers x₂))
    rw [← (h.wreath.baseGrp_eq).2.1] at this
    exact this
  exact S4A.RankLE.sup (S4A.pt_comm_base h) S4A.RankLE.of_isCyclic hB

end CFSG.OddStandard.SmallF3.FritzII
