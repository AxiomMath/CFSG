module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4A.S4AGenB
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4A.S4ARemXA

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33.S4A

open Subgroup

variable {G : Type} [Group G] [Finite G] {t : G} {L S : Subgroup G} {x₁ x₂ lam rho tau : G}

private lemma conj_conj_eq_of_commute {G : Type*} [Group G] {a b x : G}
    (h : a * b = b * a) : a * (b * x * b⁻¹) * a⁻¹ = b * (a * x * a⁻¹) * b⁻¹ := by
  have hinv : b⁻¹ * a⁻¹ = a⁻¹ * b⁻¹ := by rw [← mul_inv_rev, h, mul_inv_rev]
  calc a * (b * x * b⁻¹) * a⁻¹
      = (a * b) * x * (b⁻¹ * a⁻¹) := by group
    _ = (b * a) * x * (a⁻¹ * b⁻¹) := by rw [h, hinv]
    _ = b * (a * x * a⁻¹) * b⁻¹ := by group

private lemma conj_eq_self_of_relations {G : Type*} [Group G] {a w β u v : G}
    (haw : a * w = w * a) (hw : w * β * w⁻¹ = u * β) (ha : a * β * a⁻¹ = v * β)
    (hwv : w * v = v * w) (huv : u * v = v * u) : a * u * a⁻¹ = u := by
  have hmain : (a * u * a⁻¹) * (v * β) = v * (u * β) := by
    calc (a * u * a⁻¹) * (v * β)
        = a * (u * β) * a⁻¹ := by rw [← ha]; group
      _ = a * (w * β * w⁻¹) * a⁻¹ := by rw [hw]
      _ = w * (a * β * a⁻¹) * w⁻¹ := conj_conj_eq_of_commute haw
      _ = w * (v * β) * w⁻¹ := by rw [ha]
      _ = (w * v * w⁻¹) * (w * β * w⁻¹) := by group
      _ = v * (u * β) := by
          rw [show w * v * w⁻¹ = v from by rw [hwv]; group, hw]
  have h1 : (a * u * a⁻¹) * v = v * u := by
    have h' := congrArg (fun x : G => x * β⁻¹) hmain
    calc (a * u * a⁻¹) * v
        = ((a * u * a⁻¹) * (v * β)) * β⁻¹ := by group
      _ = (v * (u * β)) * β⁻¹ := by rw [h']
      _ = v * u := by group
  have h2 : (a * u * a⁻¹) * v = u * v := by rw [h1]; exact huv.symm
  exact mul_right_cancel h2

private lemma conj_mul_eq_of_commute {G : Type*} [Group G] {a b β u v : G}
    (ha : a * β * a⁻¹ = u * β) (hb : b * β * b⁻¹ = v * β) (hav : a * v = v * a)
    (huv : u * v = v * u) : (a * b) * β * (a * b)⁻¹ * β⁻¹ = u * v := by
  have hmain : (a * b) * β * (a * b)⁻¹ = (v * u) * β := by
    calc (a * b) * β * (a * b)⁻¹
        = a * (b * β * b⁻¹) * a⁻¹ := by group
      _ = a * (v * β) * a⁻¹ := by rw [hb]
      _ = (a * v * a⁻¹) * (a * β * a⁻¹) := by group
      _ = v * (u * β) := by
          rw [show a * v * a⁻¹ = v from by rw [hav]; group, ha]
      _ = (v * u) * β := by group
  calc (a * b) * β * (a * b)⁻¹ * β⁻¹
      = ((v * u) * β) * β⁻¹ := by rw [hmain]
    _ = v * u := by group
    _ = u * v := huv.symm

theorem exists_u_centralizes_E (h : Ctx t L S x₁ x₂ lam rho tau) (h43 : twoCore t = zpowers t)
    (h44 : tau ^ 2 = 1) {𝒮 E : Subgroup G} (hS𝒮 : S ≤ 𝒮) (hC : invCent t ⊓ 𝒮 = S)
    (hE𝒮 : E ≤ 𝒮) (hEn : (E.subgroupOf 𝒮).Normal) (hEe : CFSG.Open.IsElemAbelian 2 E)
    (hEc : Nat.card E = 8) (hES : ¬ E ≤ S) (hEF : E ⊓ S = fourGrp x₁ x₂) :
    ∃ u : G, (u = tau ∨ u = t * tau) ∧ ∀ e ∈ E, u * e * u⁻¹ = e := by
  set F : Subgroup G := fourGrp x₁ x₂ with hF_def
  set X : Subgroup G := ctxX t tau x₁ x₂ with hX_def
  have hF_eq : F = E ⊓ S := hF_def.trans hEF.symm
  have hF_le_E : F ≤ E := by rw [hF_eq]; exact inf_le_left
  have hF_le_S : F ≤ S := by rw [hF_eq]; exact inf_le_right
  have hcardF : Nat.card F = 4 := by
    rw [hF_def]; exact (WreathRel.fourGrp_eq_omega h.wreath).2.2
  haveI hFcommI : IsMulCommutative F := by
    rw [hF_def]; exact (WreathRel.fourGrp_eq_omega h.wreath).2.1.1
  have hFcomm : ∀ a ∈ F, ∀ b ∈ F, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (mul_comm' (⟨a, ha⟩ : ↥F) ⟨b, hb⟩)
  have hF_le_X : F ≤ X := by
    rw [hF_def, hX_def, fourGrp]
    refine (Subgroup.closure_le (K := ctxX t tau x₁ x₂)).mpr ?_
    intro a ha
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha
    rcases ha with rfl | rfl
    · exact Subgroup.subset_closure (by simp)
    · exact Subgroup.subset_closure (by simp)
  haveI hXcommI : IsMulCommutative X := by
    rw [hX_def]; exact (ctxX_elemAbelian_of h h44).1.1
  have hXcomm : ∀ a ∈ X, ∀ b ∈ X, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (mul_comm' (⟨a, ha⟩ : ↥X) ⟨b, hb⟩)
  have ht_S : t ∈ S := by rw [h.S_eq]; exact Subgroup.mem_sup_left h.hyp.mem_twoCore
  have htau_S : tau ∈ S := h.tau_mem
  have hlam_S : lam ∈ S := by
    have hmem : lam ∈ S ⊓ L := by
      rw [h.toCtx0.inf_eq]; exact Subgroup.subset_closure (by simp)
    exact hmem.1
  have ht_X : t ∈ X := by rw [hX_def]; exact Subgroup.subset_closure (by simp)
  have htau_X : tau ∈ X := by rw [hX_def]; exact Subgroup.subset_closure (by simp)
  obtain ⟨β, hβE, hβS⟩ : ∃ β, β ∈ E ∧ β ∉ S := by
    by_contra hne
    refine hES ?_
    intro x hxE
    by_contra hxS
    exact hne ⟨x, hxE, hxS⟩
  have hβ𝒮 : β ∈ 𝒮 := hE𝒮 hβE
  have hβ_not_cent : β ∉ invCent t := by
    intro hβc
    have hmem : β ∈ invCent t ⊓ 𝒮 := ⟨hβc, hβ𝒮⟩
    rw [hC] at hmem
    exact hβS hmem
  have hβ_nt : β * t ≠ t * β := fun hh => hβ_not_cent (mem_invCent_iff.mpr hh)
  have hβinvE : β⁻¹ ∈ E := Subgroup.inv_mem E hβE
  have hβinv_notS : β⁻¹ ∉ S := by
    intro hmem
    exact hβS (by simpa using Subgroup.inv_mem S hmem)
  have hβ_notF : β ∉ F := fun hmem => hβS (hF_le_S hmem)
  have hβinv_notF : β⁻¹ ∉ F := fun hmem => hβinv_notS (hF_le_S hmem)
  have hidx : (F.subgroupOf E).index = 2 := by
    have hcardmul := Subgroup.card_mul_index (H := F.subgroupOf E)
    have hEq : Nat.card (F.subgroupOf E) = Nat.card F :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hF_le_E).toEquiv
    have hEc' : Nat.card ↥E = 8 := hEc
    rw [hEq, hcardF, hEc'] at hcardmul
    omega
  have hout : ∀ a b : G, a ∈ E → b ∈ E → a ∉ F → b ∉ F → a * b ∈ F := by
    intro a b haE hbE haF hbF
    have h := (Subgroup.mul_mem_iff_of_index_two hidx (a := ⟨a, haE⟩) (b := ⟨b, hbE⟩)).mpr
      (iff_of_false (fun h => haF (Subgroup.mem_subgroupOf.mp h))
        (fun h => hbF (Subgroup.mem_subgroupOf.mp h)))
    exact Subgroup.mem_subgroupOf.mp h
  have hconj_E : ∀ g ∈ S, g * β * g⁻¹ ∈ E := by
    intro g hgS
    have hg𝒮 : g ∈ 𝒮 := hS𝒮 hgS
    have hmem := hEn.conj_mem (⟨β, hβ𝒮⟩ : ↥𝒮)
      (by simpa [Subgroup.mem_subgroupOf] using hβE) (⟨g, hg𝒮⟩ : ↥𝒮)
    simpa [Subgroup.mem_subgroupOf] using hmem
  set c : G → G := fun g => g * β * g⁻¹ * β⁻¹ with hc_def
  have hc_mem : ∀ g ∈ S, c g ∈ F := by
    intro g hgS
    have hgβE : g * β * g⁻¹ ∈ E := hconj_E g hgS
    have hgβ_notS : g * β * g⁻¹ ∉ S := by
      intro hmem
      refine hβS ?_
      have h2 : g⁻¹ * (g * β * g⁻¹) * g ∈ S :=
        Subgroup.mul_mem S (Subgroup.mul_mem S (Subgroup.inv_mem S hgS) hmem) hgS
      have heq : g⁻¹ * (g * β * g⁻¹) * g = β := by group
      rwa [heq] at h2
    have hgβ_notF : g * β * g⁻¹ ∉ F := fun hmem => hgβ_notS (hF_le_S hmem)
    have hmem := hout (g * β * g⁻¹) β⁻¹ hgβE hβinvE hgβ_notF hβinv_notF
    simpa only [hc_def] using hmem
  have hc_eq : ∀ g ∈ S, g * β * g⁻¹ = c g * β := by
    intro g hgS
    simp only [hc_def]
    group
  have hx₁4 : x₁ ^ 4 = 1 := by rw [← h.wreath.ord_x₁]; exact pow_orderOf_eq_one x₁
  have hlam_y : lam * x₁ ^ 2 * lam⁻¹ = x₁ ^ 2 * (x₁ * x₂) ^ 2 := by
    have hcomm : Commute x₁ x₂ := h.wreath.comm
    have hz : (x₁ * x₂) ^ 2 = x₁ ^ 2 * x₂ ^ 2 := hcomm.mul_pow 2
    have hyz : x₁ ^ 2 * (x₁ * x₂) ^ 2 = x₂ ^ 2 := by
      rw [hz, ← mul_assoc, ← pow_add, show (2 : ℕ) + 2 = 4 from rfl, hx₁4, one_mul]
    have h1 : lam * x₁ ^ 2 * lam⁻¹ = x₂ ^ 2 := by
      rw [← conj_pow (a := lam) (b := x₁) (i := 2), h.wreath.conj_x₁]
    rw [h1, ← hyz]
  have hlam_z : lam * (x₁ * x₂) ^ 2 * lam⁻¹ = (x₁ * x₂) ^ 2 := by
    have hzZ : (x₁ * x₂) ^ 2 ∈ S ⊓ centralizer (S : Set G) :=
      h.center_ge (Subgroup.subset_closure (by simp))
    have hcomm : lam * (x₁ * x₂) ^ 2 = (x₁ * x₂) ^ 2 * lam :=
      (Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp hzZ).2) lam hlam_S
    rw [hcomm]; group
  have hlam_yz : lam * (x₁ ^ 2 * (x₁ * x₂) ^ 2) * lam⁻¹ = x₁ ^ 2 := by
    have h1 : lam * (x₁ ^ 2 * (x₁ * x₂) ^ 2) * lam⁻¹ =
        (lam * x₁ ^ 2 * lam⁻¹) * (lam * (x₁ * x₂) ^ 2 * lam⁻¹) := by group
    rw [h1, hlam_y, hlam_z, mul_assoc, (z_mul_self_ne_one h.toCtx0).1, mul_one]
  have hfix : ∀ f ∈ F, lam * f * lam⁻¹ = f → f = 1 ∨ f = (x₁ * x₂) ^ 2 := by
    intro f hf hconj
    have hf' : f ∈ closure {x₁ ^ 2, (x₁ * x₂) ^ 2} := hf
    rcases mem_closure_pair_cases (a := x₁ ^ 2) (b := (x₁ * x₂) ^ 2)
        (y_commute_z h.wreath) (y_mul_self_ne_one h.wreath).1
        (z_mul_self_ne_one h.toCtx0).1 hf' with rfl | rfl | rfl | rfl
    · exact Or.inl rfl
    · exfalso
      have h1 : x₁ ^ 2 = x₁ ^ 2 * (x₁ * x₂) ^ 2 := hconj.symm.trans hlam_y
      have h2 : x₁ ^ 2 * x₁ ^ 2 = x₁ ^ 2 * (x₁ ^ 2 * (x₁ * x₂) ^ 2) :=
        congrArg (fun w => x₁ ^ 2 * w) h1
      rw [← mul_assoc, (y_mul_self_ne_one h.wreath).1, one_mul] at h2
      exact (z_mul_self_ne_one h.toCtx0).2 h2.symm
    · exact Or.inr rfl
    · exfalso
      have h1 : x₁ ^ 2 * (x₁ * x₂) ^ 2 = x₁ ^ 2 := hconj.symm.trans hlam_yz
      have h2 : x₁ ^ 2 * (x₁ ^ 2 * (x₁ * x₂) ^ 2) = x₁ ^ 2 * x₁ ^ 2 :=
        congrArg (fun w => x₁ ^ 2 * w) h1
      rw [← mul_assoc, (y_mul_self_ne_one h.wreath).1, one_mul] at h2
      exact (z_mul_self_ne_one h.toCtx0).2 h2
  have hc_lam_fix : ∀ g, g ∈ S → g ∈ X → lam * g = g * lam → lam * c g * lam⁻¹ = c g := by
    intro g hgS hgX hglam
    exact conj_eq_self_of_relations hglam (hc_eq g hgS) (hc_eq lam hlam_S)
      (hXcomm g hgX (c lam) (hF_le_X (hc_mem lam hlam_S)))
      (hFcomm (c g) (hc_mem g hgS) (c lam) (hc_mem lam hlam_S))
  have hlam_t : lam * t = t * lam := mem_invCent_iff.mp (h.toCtx0.le_invCent hlam_S)
  have hlam_tau : lam * tau = tau * lam := h.tau_lam.symm
  have hct_ne_one : c t ≠ 1 := by
    intro hc1
    have htβ : t * β * t⁻¹ = β := by
      have h' := hc1
      simp only [hc_def] at h'
      exact mul_inv_eq_one.mp h'
    have hcomm : t * β = β * t := mul_inv_eq_iff_eq_mul.mp htβ
    exact hβ_nt hcomm.symm
  have hct : c t = (x₁ * x₂) ^ 2 := by
    rcases hfix (c t) (hc_mem t ht_S) (hc_lam_fix t ht_S ht_X hlam_t) with h1 | h1
    · exact absurd h1 hct_ne_one
    · exact h1
  have hctau : c tau = 1 ∨ c tau = (x₁ * x₂) ^ 2 :=
    hfix (c tau) (hc_mem tau htau_S) (hc_lam_fix tau htau_S htau_X hlam_tau)
  have hc_mul : c (t * tau) = c t * c tau := by
    have hmain := conj_mul_eq_of_commute (a := t) (b := tau) (β := β) (u := c t) (v := c tau)
      (hc_eq t ht_S) (hc_eq tau htau_S)
      (hXcomm t ht_X (c tau) (hF_le_X (hc_mem tau htau_S)))
      (hFcomm (c t) (hc_mem t ht_S) (c tau) (hc_mem tau htau_S))
    have hleft : c (t * tau) = (t * tau) * β * (t * tau)⁻¹ * β⁻¹ := by simp only [hc_def]
    rw [hleft, hmain]
  have key : ∀ u : G, (u = tau ∨ u = t * tau) → c u = 1 → ∀ e ∈ E, u * e * u⁻¹ = e := by
    intro u hu hcu e heE
    have huX : u ∈ X := by
      rcases hu with rfl | rfl
      · exact htau_X
      · exact Subgroup.mul_mem X ht_X htau_X
    have huβ : u * β * u⁻¹ = β := by
      have h' := hcu
      simp only [hc_def] at h'
      exact mul_inv_eq_one.mp h'
    have hu_cent_F : ∀ f ∈ F, u * f * u⁻¹ = f := by
      intro f hf
      have hcomm : u * f = f * u := hXcomm u huX f (hF_le_X hf)
      rw [hcomm]; group
    by_cases heF : e ∈ F
    · exact hu_cent_F e heF
    · have hf : β⁻¹ * e ∈ F := hout β⁻¹ e hβinvE heE hβinv_notF heF
      have he_eq : e = β * (β⁻¹ * e) := by group
      rw [he_eq]
      calc u * (β * (β⁻¹ * e)) * u⁻¹
          = (u * β * u⁻¹) * (u * (β⁻¹ * e) * u⁻¹) := by group
        _ = β * (β⁻¹ * e) := by rw [huβ, hu_cent_F _ hf]
  rcases hctau with h1 | h1
  · exact ⟨tau, Or.inl rfl, key tau (Or.inl rfl) h1⟩
  · have hc_ttau_one : c (t * tau) = 1 := by
      rw [hc_mul, hct, h1, (z_mul_self_ne_one h.toCtx0).1]
    exact ⟨t * tau, Or.inr rfl, key (t * tau) (Or.inr rfl) hc_ttau_one⟩

end CFSG.OddStandard.SmallF3.HarrisU33.S4A
