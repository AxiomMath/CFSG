module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4A.S4AConcl
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4A.S4ARemFusB
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4A.S4AL44A

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33.S4A

open Subgroup

variable {G : Type} [Group G] [Finite G] {t : G} {L S : Subgroup G} {x₁ x₂ lam rho tau : G}

private lemma mem_zpowers_eq_one_or_eq {z g : G} (hz : z * z = 1) (hg : g ∈ zpowers z) :
    g = 1 ∨ g = z := by
  let H : Subgroup G :=
    { carrier := {g : G | g = 1 ∨ g = z}
      one_mem' := Or.inl rfl
      mul_mem' := by
        intro a b ha hb
        rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
        · exact Or.inl (by simp)
        · exact Or.inr (by simp)
        · exact Or.inr (by simp)
        · exact Or.inl (by rw [hz])
      inv_mem' := by
        intro a ha
        rcases ha with rfl | rfl
        · exact Or.inl (by simp)
        · exact Or.inr (by rw [inv_eq_of_mul_eq_one_right hz]) }
  exact (Subgroup.zpowers_le.mpr (show z ∈ H from Or.inr rfl)) hg

private lemma twoCore_sq_eq_one (h : Ctx t L S x₁ x₂ lam rho tau)
    (h43 : twoCore t = zpowers t) {p : G} (hp : p ∈ twoCore t) : p * p = 1 := by
  rcases mem_zpowers_eq_one_or_eq (t_mul_self h.hyp) (h43 ▸ hp) with h1 | h1
  · rw [h1]; simp
  · rw [h1]; exact t_mul_self h.hyp

private lemma twoCore_eq_one_or_t (h : Ctx t L S x₁ x₂ lam rho tau)
    (h43 : twoCore t = zpowers t) {p : G} (hp : p ∈ twoCore t) : p = 1 ∨ p = t :=
  mem_zpowers_eq_one_or_eq (t_mul_self h.hyp) (h43 ▸ hp)

private lemma twoCore_commute_invCent (h : Ctx t L S x₁ x₂ lam rho tau)
    (h43 : twoCore t = zpowers t) {p g : G} (hp : p ∈ twoCore t) (hg : g ∈ invCent t) :
    p * g = g * p := by
  rcases twoCore_eq_one_or_t h h43 hp with h1 | h1
  · rw [h1, one_mul, mul_one]
  · rw [h1]; exact (mem_invCent_iff.mp hg).symm

private lemma mul_sq_eq_of_commute {p a tau : G} (hp : p * p = 1) (hpa : p * a = a * p)
    (hpt : p * tau = tau * p) (hta : tau * a * tau⁻¹ = a⁻¹) :
    (p * a * tau) ^ 2 = tau ^ 2 := by
  have htp : tau * p = p * tau := hpt.symm
  have hap : a * p = p * a := hpa.symm
  have hta' : tau * a = a⁻¹ * tau := by
    calc
      tau * a = (tau * a * tau⁻¹) * tau := by group
      _ = a⁻¹ * tau := by rw [hta]
  calc
    (p * a * tau) ^ 2 = p * a * tau * (p * a * tau) := by rw [pow_two]
    _ = p * a * (tau * p) * a * tau := by group
    _ = p * a * (p * tau) * a * tau := by rw [htp]
    _ = p * (a * p) * tau * a * tau := by group
    _ = p * (p * a) * tau * a * tau := by rw [hap]
    _ = p * p * a * (tau * a) * tau := by group
    _ = p * p * a * (a⁻¹ * tau) * tau := by rw [hta']
    _ = p * p * (a * a⁻¹) * (tau * tau) := by group
    _ = tau ^ 2 := by rw [hp, pow_two]; group

private lemma mul_tau_sq_eq {p tau : G} (hp : p * p = 1) (hpt : p * tau = tau * p) :
    (p * tau) ^ 2 = tau ^ 2 := by
  have htp : tau * p = p * tau := hpt.symm
  calc
    (p * tau) ^ 2 = p * tau * (p * tau) := by rw [pow_two]
    _ = p * (tau * p) * tau := by group
    _ = p * (p * tau) * tau := by rw [htp]
    _ = p * p * (tau * tau) := by group
    _ = tau ^ 2 := by rw [hp, pow_two]; group

theorem lemma4_4_of (h : Ctx t L S x₁ x₂ lam rho tau) (h42 : 2 ∣ S.index)
    (h43 : twoCore t = zpowers t) : Lemma4_4Concl t tau := by
  have hbase_le_L : baseGrp x₁ x₂ ≤ L := by
    rw [baseGrp]
    refine (Subgroup.closure_le L).mpr ?_
    intro a ha
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha
    rcases ha with rfl | rfl
    · exact (generators_mem_L h.toCtx0).1
    · exact (generators_mem_L h.toCtx0).2.1
  have hPA : ∀ p ∈ twoCore t, ∀ a ∈ baseGrp x₁ x₂, p * a = a * p :=
    fun p hp a ha => twoCore_commute h.hyp p hp a (hbase_le_L ha)
  have htau_inv : tau ∈ invCent t := h.toCtx0.le_invCent h.tau_mem
  have h_inv_on_A : ∀ a ∈ baseGrp x₁ x₂, tau * a * tau⁻¹ = a⁻¹ := by
    haveI : IsMulCommutative (baseGrp x₁ x₂) := (WreathRel.baseGrp_eq h.wreath).1
    let K : Subgroup G :=
      { carrier := {a : G | a ∈ baseGrp x₁ x₂ ∧ tau * a * tau⁻¹ = a⁻¹}
        one_mem' := ⟨one_mem _, by simp⟩
        mul_mem' := by
          rintro a b ⟨ha, ha'⟩ ⟨hb, hb'⟩
          refine ⟨mul_mem ha hb, ?_⟩
          have hcomm : a⁻¹ * b⁻¹ = b⁻¹ * a⁻¹ :=
            congrArg Subtype.val (mul_comm' (⟨a⁻¹, inv_mem ha⟩ : baseGrp x₁ x₂)
              ⟨b⁻¹, inv_mem hb⟩)
          calc
            tau * (a * b) * tau⁻¹ = (tau * a * tau⁻¹) * (tau * b * tau⁻¹) := by group
            _ = a⁻¹ * b⁻¹ := by rw [ha', hb']
            _ = b⁻¹ * a⁻¹ := hcomm
            _ = (a * b)⁻¹ := by rw [mul_inv_rev]
        inv_mem' := by
          rintro a ⟨ha, ha'⟩
          refine ⟨inv_mem ha, ?_⟩
          have h1 : (tau * a * tau⁻¹)⁻¹ = tau * a⁻¹ * tau⁻¹ := by
            rw [mul_inv_rev, mul_inv_rev, inv_inv, mul_assoc]
          rw [← h1]
          exact congrArg (fun x : G => x⁻¹) ha' }
    have hK : baseGrp x₁ x₂ ≤ K := by
      rw [baseGrp]
      refine (Subgroup.closure_le K).mpr ?_
      intro a ha
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha
      rcases ha with rfl | rfl
      · exact ⟨Subgroup.subset_closure (by simp), h.tau_x₁⟩
      · exact ⟨Subgroup.subset_closure (by simp), h.tau_x₂⟩
    intro a ha
    exact (hK ha).2
  have hW_sq : ∀ w ∈ ctxW t x₁ x₂, (w * tau) ^ 2 = tau ^ 2 := by
    intro w hw
    rw [ctxW] at hw
    obtain ⟨p, hp, a, ha, rfl⟩ := (mem_sup_iff_of_commute hPA).mp hw
    exact mul_sq_eq_of_commute (twoCore_sq_eq_one h h43 hp) (hPA p hp a ha)
      (twoCore_commute_invCent h h43 hp htau_inv) (h_inv_on_A a ha)
  have hcard_W : Nat.card (ctxW t x₁ x₂) = 32 := by
    have hPcard : Nat.card (twoCore t) = 2 := by
      rw [h43, Nat.card_zpowers, h.hyp.ord_t]
    have hAcard : Nat.card (baseGrp x₁ x₂) = 16 := (WreathRel.baseGrp_eq h.wreath).2.2
    have hinf : twoCore t ⊓ baseGrp x₁ x₂ = ⊥ := by
      apply eq_bot_iff.mpr
      intro x hx
      have hxL : x ∈ twoCore t ⊓ L := ⟨hx.1, hbase_le_L hx.2⟩
      have h' := hxL
      rw [h.hyp.twoCore_inf, Subgroup.mem_bot] at h'
      simpa using h'
    rw [ctxW, card_sup_of_commute hPA hinf, hPcard, hAcard]
  have hW_le_S : ctxW t x₁ x₂ ≤ S := by
    rw [ctxW]
    refine sup_le ?_ ?_
    · rw [h.S_eq]; exact le_sup_left
    · have hbase_wreath : baseGrp x₁ x₂ ≤ wreathGrp x₁ x₂ lam := by
        rw [baseGrp, wreathGrp]
        exact Subgroup.closure_mono (by
          intro a ha
          simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha ⊢
          tauto)
      exact le_trans hbase_wreath (by rw [← h.toCtx0.inf_eq]; exact inf_le_left)
  have hne_tau_sq : tau ^ 2 ≠ t := by
    intro htau
    obtain ⟨n, hn, hnt⟩ := exists_swap_of_l42 h h42
    let f : G → G := fun w => n * (w * tau) * n⁻¹
    have hf_inj : Function.Injective f := by
      intro u v huv
      change n * (u * tau) * n⁻¹ = n * (v * tau) * n⁻¹ at huv
      have h1 : n * (u * tau) = n * (v * tau) := mul_right_cancel huv
      have h2 : u * tau = v * tau := mul_left_cancel h1
      exact mul_right_cancel h2
    have hf_mem : ∀ w ∈ ctxW t x₁ x₂, f w ∈ {s : G | s ∈ S ∧ s ^ 2 = t * (x₁ * x₂) ^ 2} := by
      intro w hw
      have hwtauS : w * tau ∈ S := S.mul_mem (hW_le_S hw) h.tau_mem
      refine ⟨((Subgroup.mem_set_normalizer_iff.mp hn) (w * tau)).mp hwtauS, ?_⟩
      show (n * (w * tau) * n⁻¹) ^ 2 = t * (x₁ * x₂) ^ 2
      calc
        (n * (w * tau) * n⁻¹) ^ 2 = n * (w * tau) ^ 2 * n⁻¹ := by rw [conj_pow]
        _ = n * tau ^ 2 * n⁻¹ := by rw [hW_sq w hw]
        _ = n * t * n⁻¹ := by rw [htau]
        _ = t * (x₁ * x₂) ^ 2 := hnt
    set R : Set G := f '' (ctxW t x₁ x₂ : Set G) with hRdef
    have hRcard : R.ncard = 32 := by
      rw [hRdef, Set.ncard_image_of_injective (ctxW t x₁ x₂ : Set G) hf_inj,
        ← Nat.card_coe_set_eq]
      exact hcard_W
    have hRsub : R ⊆ {s : G | s ∈ S ∧ s ^ 2 = t * (x₁ * x₂) ^ 2} := by
      rintro s ⟨w, hw, rfl⟩
      exact hf_mem w hw
    have hle8 : R.ncard ≤ 8 :=
      (Set.ncard_le_ncard hRsub).trans (ncard_sq_roots_tz_le h h43 htau)
    omega
  have htau_sq : tau ^ 2 = 1 := by
    have hmem : tau ^ 2 ∈ twoCore t := h.tau_sq_mem
    have hsq : (tau ^ 2) ^ 2 = 1 := by
      rw [pow_two]
      exact twoCore_sq_eq_one h h43 hmem
    rcases h.hyp.eq_one_or_eq (tau ^ 2) hmem hsq with h1 | h1
    · exact h1
    · exact absurd h1 hne_tau_sq
  have hsquare_ne : ∀ g : G, g ^ 2 ≠ t := by
    intro g hg
    have hg_inv : g ∈ invCent t := by
      rw [mem_invCent_iff]
      calc
        g * t = g * g ^ 2 := by rw [hg]
        _ = g ^ 2 * g := by group
        _ = t * g := by rw [hg]
    have hg_not_mem : g ∉ twoCore t ⊔ L := by
      intro hgF
      obtain ⟨p, hp, l, hl, hgl⟩ :=
        (mem_sup_iff_of_commute (twoCore_commute h.hyp)).mp hgF
      have hp2 : p * p = 1 := twoCore_sq_eq_one h h43 hp
      have hpl : p * l = l * p := twoCore_commute h.hyp p hp l hl
      have hsq : g ^ 2 = l * l := by
        rw [hgl, pow_two]
        calc
          (p * l) * (p * l) = p * (l * p) * l := by group
          _ = p * (p * l) * l := by rw [hpl]
          _ = p * p * (l * l) := by group
          _ = l * l := by rw [hp2]; group
      have htL : t ∈ L := by
        rw [← hg, hsq]
        exact Subgroup.mul_mem L hl hl
      exact t_not_mem_L h.hyp htL
    obtain ⟨h', hh'inv, p, hp, hconj⟩ :=
      h.invol_outer g hg_inv hg_not_mem (by rw [hg]; exact h.hyp.mem_twoCore)
    have hp2 : p * p = 1 := twoCore_sq_eq_one h h43 hp
    have hpt : p * tau = tau * p := twoCore_commute_invCent h h43 hp htau_inv
    have hp_tau_sq : (p * tau) ^ 2 = tau ^ 2 := mul_tau_sq_eq hp2 hpt
    have hleft : (p * tau) ^ 2 = t := by
      rw [← hconj]
      calc
        (h' * g * h'⁻¹) ^ 2 = h' * g ^ 2 * h'⁻¹ := by rw [conj_pow]
        _ = h' * t * h'⁻¹ := by rw [hg]
        _ = t := by
          have hcomm : h' * t = t * h' := mem_invCent_iff.mp hh'inv
          rw [hcomm]; group
    exact hne_tau_sq (hp_tau_sq.symm.trans hleft)
  exact ⟨htau_sq, hsquare_ne⟩

end CFSG.OddStandard.SmallF3.HarrisU33.S4A
