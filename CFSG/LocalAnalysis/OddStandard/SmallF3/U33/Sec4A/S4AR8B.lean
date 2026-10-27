module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4A.S4ANbA

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33.S4A

open Subgroup
open scoped Pointwise commutatorElement

section Gen

variable {G : Type} [Group G] [Finite G] {t : G} {L S : Subgroup G} {x₁ x₂ lam rho : G}

theorem n4_rho_mem_N (h : L41GPh1 t L S x₁ x₂ lam rho) : rho ∈ l41N t x₁ x₂ :=
  n4_K_le_N h (Subgroup.subset_closure (by simp))

theorem n4_rho_inv_mem_N (h : L41GPh1 t L S x₁ x₂ lam rho) : rho⁻¹ ∈ l41N t x₁ x₂ :=
  Subgroup.inv_mem _ (n4_rho_mem_N h)

theorem mem_map_conj {g x : G} {E : Subgroup G} :
    x ∈ E.map (MulAut.conj g).toMonoidHom ↔ ∃ e ∈ E, g * e * g⁻¹ = x := by
  simp only [Subgroup.mem_map, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]

theorem comm_conj_left (g e w : G) : ⁅g * e * g⁻¹, w⁆ = g * ⁅e, g⁻¹ * w * g⁻¹⁻¹⁆ * g⁻¹ := by
  simp only [commutatorElement_def]
  group

theorem n4_gen_O (h : L41GPh3 t L S x₁ x₂ lam rho) {K : Subgroup G}
    (hWK : ctxW t x₁ x₂ ≤ K) (hKO : K ≤ l41O2 t x₁ x₂) {q : G} (hqK : q ∈ K)
    (hqW : q ∉ ctxW t x₁ x₂) (hρq : rho * q * rho⁻¹ ∈ K) : K = l41O2 t x₁ x₂ := by
  have hcardO := n4_card_O2 h
  have hdvd1 : Nat.card (ctxW t x₁ x₂) ∣ Nat.card K := Subgroup.card_dvd_of_le hWK
  have hdvd2 : Nat.card K ∣ Nat.card (l41O2 t x₁ x₂) := Subgroup.card_dvd_of_le hKO
  obtain ⟨a, ha⟩ := hdvd1
  have hWpos : 0 < Nat.card (ctxW t x₁ x₂) := Nat.card_pos
  have hKpos : 0 < Nat.card K := Nat.card_pos
  have hadvd : a ∣ 4 := by
    rw [ha, hcardO, mul_comm 4] at hdvd2
    exact Nat.dvd_of_mul_dvd_mul_left hWpos hdvd2
  have ha4 : a ≤ 4 := Nat.le_of_dvd (by norm_num) hadvd
  interval_cases a
  · simp at ha
    omega
  · exfalso
    have hK : ctxW t x₁ x₂ = K := Subgroup.eq_of_le_of_card_ge hWK (by omega)
    exact hqW (hK ▸ hqK)
  · exfalso
    have hrel : (ctxW t x₁ x₂).relIndex K = 2 := by
      have h1 := Subgroup.relIndex_mul_card (H := ctxW t x₁ x₂) (K := K)
      rw [inf_eq_left.mpr hWK] at h1
      apply Nat.eq_of_mul_eq_mul_right hWpos
      rw [h1, ha]
      ring
    have hρN : rho ∈ l41N t x₁ x₂ := n4_rho_mem_N h.toL41GPh1
    rcases mem_or_mem_or_mul_mem_of_relIndex_two hWK hrel hρq (Subgroup.inv_mem K hqK) with
      h1 | h1 | h1
    · apply hqW
      have := n4_conj_W h.toL41GPh1 (n4_rho_inv_mem_N h.toL41GPh1) h1
      have e : rho⁻¹ * (rho * q * rho⁻¹) * rho⁻¹⁻¹ = q := by group
      rwa [e] at this
    · exact hqW (by simpa using Subgroup.inv_mem _ h1)
    · apply hqW
      refine n4_O_comm_rho h (hKO hqK) ?_
      have := Subgroup.inv_mem _ h1
      have e : (rho * q * rho⁻¹ * q⁻¹)⁻¹ = q * rho * q⁻¹ * rho⁻¹ := by group
      rwa [e] at this
  · omega
  · exact Subgroup.eq_of_le_of_card_ge hKO (by omega)

theorem n4_O_eq_join (h : L41GPh3 t L S x₁ x₂ lam rho) {E : Subgroup G}
    (hEO : E ≤ l41O2 t x₁ x₂) (hEW : ¬ E ≤ ctxW t x₁ x₂) :
    ctxW t x₁ x₂ ⊔ E ⊔ E.map (MulAut.conj rho).toMonoidHom = l41O2 t x₁ x₂ := by
  have hρN : rho ∈ l41N t x₁ x₂ := n4_rho_mem_N h.toL41GPh1
  obtain ⟨e₀, he₀E, he₀W⟩ := SetLike.not_le_iff_exists.mp hEW
  refine n4_gen_O h (q := e₀) (le_sup_left.trans le_sup_left) ?_
    (Subgroup.mem_sup_left (Subgroup.mem_sup_right he₀E)) he₀W
    (Subgroup.mem_sup_right (mem_map_conj.mpr ⟨e₀, he₀E, rfl⟩))
  refine sup_le (sup_le (n4_W_le_O h) hEO) ?_
  intro x hx
  obtain ⟨e, he, rfl⟩ := mem_map_conj.mp hx
  exact pCoreOf_two_conj_mem hρN (hEO he)

end Gen

section ModF

variable {G : Type} [Group G]

private def modCent (N F : Subgroup G) (hF : ∀ n ∈ N, ∀ f ∈ F, n * f * n⁻¹ ∈ F) (X : Set G) :
    Subgroup G where
  carrier := {q | q ∈ N ∧ ∀ w ∈ X, ⁅q, w⁆ ∈ F}
  one_mem' := ⟨N.one_mem, fun w _ => by simp⟩
  mul_mem' := by
    rintro a b ⟨haN, ha⟩ ⟨hbN, hb⟩
    refine ⟨N.mul_mem haN hbN, fun w hw => ?_⟩
    have e : ⁅a * b, w⁆ = (a * ⁅b, w⁆ * a⁻¹) * ⁅a, w⁆ := by
      simp only [commutatorElement_def]
      group
    rw [e]
    exact F.mul_mem (hF a haN _ (hb w hw)) (ha w hw)
  inv_mem' := by
    rintro a ⟨haN, ha⟩
    refine ⟨N.inv_mem haN, fun w hw => ?_⟩
    have e : ⁅a⁻¹, w⁆ = a⁻¹ * ⁅a, w⁆⁻¹ * a := by
      simp only [commutatorElement_def]
      group
    rw [e]
    have := hF a⁻¹ (N.inv_mem haN) _ (F.inv_mem (ha w hw))
    simpa using this

private theorem mem_modCent {N F : Subgroup G} {hF : ∀ n ∈ N, ∀ f ∈ F, n * f * n⁻¹ ∈ F}
    {X : Set G} {q : G} : q ∈ modCent N F hF X ↔ q ∈ N ∧ ∀ w ∈ X, ⁅q, w⁆ ∈ F := Iff.rfl

private def sqSub (O F : Subgroup G) (hF : ∀ n ∈ O, ∀ f ∈ F, n * f * n⁻¹ ∈ F)
    (hab : ∀ a ∈ O, ∀ b ∈ O, ⁅a, b⁆ ∈ F) : Subgroup G where
  carrier := {q | q ∈ O ∧ q * q ∈ F}
  one_mem' := ⟨O.one_mem, by simpa using F.one_mem⟩
  mul_mem' := by
    rintro a b ⟨haO, ha⟩ ⟨hbO, hb⟩
    refine ⟨O.mul_mem haO hbO, ?_⟩
    have hc : ⁅b, a⁆ ∈ F := hab b hbO a haO
    have e : a * b * (a * b) = (a * ⁅b, a⁆ * a⁻¹) * (a * a) * (b * b) := by
      simp only [commutatorElement_def]
      group
    rw [e]
    exact F.mul_mem (F.mul_mem (hF a haO _ hc) ha) hb
  inv_mem' := by
    rintro a ⟨haO, ha⟩
    refine ⟨O.inv_mem haO, ?_⟩
    have e : a⁻¹ * a⁻¹ = (a * a)⁻¹ := by group
    rw [e]
    exact F.inv_mem ha

private theorem mem_sqSub {O F : Subgroup G} {hF : ∀ n ∈ O, ∀ f ∈ F, n * f * n⁻¹ ∈ F}
    {hab : ∀ a ∈ O, ∀ b ∈ O, ⁅a, b⁆ ∈ F} {q : G} :
    q ∈ sqSub O F hF hab ↔ q ∈ O ∧ q * q ∈ F := Iff.rfl

end ModF

section Mod

variable {G : Type} [Group G] [Finite G] {t : G} {L S : Subgroup G} {x₁ x₂ lam rho : G}

theorem n4_O_norm_F (h : L41GPh3 t L S x₁ x₂ lam rho) :
    ∀ n ∈ l41O2 t x₁ x₂, ∀ f ∈ fourGrp x₁ x₂, n * f * n⁻¹ ∈ fourGrp x₁ x₂ :=
  fun n hn f hf => (n4_normal_F2 h).2 n (pCoreOf_two_le _ hn) f hf

theorem n4_O_cent_W (h : L41GPh6 t L S x₁ x₂ lam rho) {q : G} (hq : q ∈ l41O2 t x₁ x₂)
    {w : G} (hw : w ∈ ctxW t x₁ x₂) : ⁅q, w⁆ ∈ fourGrp x₁ x₂ := by
  obtain ⟨E, hEO, -, -, -, -, hEW, -, hEc⟩ := h.e8
  haveI : IsMulCommutative (ctxW t x₁ x₂) := h.abelian_W
  have hF : ∀ n ∈ l41N t x₁ x₂, ∀ f ∈ fourGrp x₁ x₂, n * f * n⁻¹ ∈ fourGrp x₁ x₂ :=
    (n4_normal_F2 h.toL41GPh3).2
  have hρN : rho ∈ l41N t x₁ x₂ := n4_rho_mem_N h.toL41GPh1
  have hJ := n4_O_eq_join h.toL41GPh3 hEO hEW
  have hle : ctxW t x₁ x₂ ⊔ E ⊔ E.map (MulAut.conj rho).toMonoidHom ≤
      modCent (l41N t x₁ x₂) (fourGrp x₁ x₂) hF (ctxW t x₁ x₂ : Set G) := by
    refine sup_le (sup_le ?_ ?_) ?_
    · intro a ha
      refine mem_modCent.mpr ⟨n4_W_le_N h.toL41GPh1 ha, fun w hw => ?_⟩
      have hcomm : a * w = w * a := congrArg Subtype.val (mul_comm' (⟨a, ha⟩ : ctxW t x₁ x₂)
        ⟨w, hw⟩)
      rw [commutatorElement_def, hcomm]
      simp
    · intro e he
      exact mem_modCent.mpr ⟨pCoreOf_two_le _ (hEO he), fun w hw =>
        hEc e he w (n4_W_le_V h.toL41GPh1 hw)⟩
    · intro x hx
      obtain ⟨e, he, rfl⟩ := mem_map_conj.mp hx
      refine mem_modCent.mpr ⟨?_, fun w hw => ?_⟩
      · exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hρN (pCoreOf_two_le _ (hEO he)))
          (Subgroup.inv_mem _ hρN)
      · rw [comm_conj_left]
        have hw' : rho⁻¹ * w * rho⁻¹⁻¹ ∈ ctxW t x₁ x₂ :=
          n4_conj_W h.toL41GPh1 (n4_rho_inv_mem_N h.toL41GPh1) hw
        exact hF rho hρN _ (hEc e he _ (n4_W_le_V h.toL41GPh1 hw'))
  rw [hJ] at hle
  exact (mem_modCent.mp (hle hq)).2 w hw

theorem n4_O_comm (h : L41GPh6 t L S x₁ x₂ lam rho) {a b : G} (ha : a ∈ l41O2 t x₁ x₂)
    (hb : b ∈ l41O2 t x₁ x₂) : ⁅a, b⁆ ∈ fourGrp x₁ x₂ := by
  obtain ⟨E, hEO, -, -, -, -, hEW, -, hEc⟩ := h.e8
  have hF : ∀ n ∈ l41N t x₁ x₂, ∀ f ∈ fourGrp x₁ x₂, n * f * n⁻¹ ∈ fourGrp x₁ x₂ :=
    (n4_normal_F2 h.toL41GPh3).2
  have hρN : rho ∈ l41N t x₁ x₂ := n4_rho_mem_N h.toL41GPh1
  have hJ := n4_O_eq_join h.toL41GPh3 hEO hEW
  have hOV : l41O2 t x₁ x₂ ≤ l41V S t x₁ x₂ := le_sup_left
  have hle : ctxW t x₁ x₂ ⊔ E ⊔ E.map (MulAut.conj rho).toMonoidHom ≤
      modCent (l41N t x₁ x₂) (fourGrp x₁ x₂) hF (l41O2 t x₁ x₂ : Set G) := by
    refine sup_le (sup_le ?_ ?_) ?_
    · intro a ha
      refine mem_modCent.mpr ⟨n4_W_le_N h.toL41GPh1 ha, fun q hq => ?_⟩
      have := Subgroup.inv_mem _ (n4_O_cent_W h hq ha)
      rwa [commutatorElement_inv] at this
    · intro e he
      exact mem_modCent.mpr ⟨pCoreOf_two_le _ (hEO he), fun q hq => hEc e he q (hOV hq)⟩
    · intro x hx
      obtain ⟨e, he, rfl⟩ := mem_map_conj.mp hx
      refine mem_modCent.mpr ⟨?_, fun q hq => ?_⟩
      · exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hρN (pCoreOf_two_le _ (hEO he)))
          (Subgroup.inv_mem _ hρN)
      · rw [comm_conj_left]
        have hq' : rho⁻¹ * q * rho⁻¹⁻¹ ∈ l41O2 t x₁ x₂ :=
          pCoreOf_two_conj_mem (n4_rho_inv_mem_N h.toL41GPh1) hq
        exact hF rho hρN _ (hEc e he _ (hOV hq'))
  rw [hJ] at hle
  exact (mem_modCent.mp (hle ha)).2 b hb

theorem n4_O_sq (h : L41GPh6 t L S x₁ x₂ lam rho) {q : G} (hq : q ∈ l41O2 t x₁ x₂) :
    q * q ∈ fourGrp x₁ x₂ := by
  obtain ⟨E, hEO, -, hEe, -, -, hEW, -, -⟩ := h.e8
  have hρN : rho ∈ l41N t x₁ x₂ := n4_rho_mem_N h.toL41GPh1
  have hJ := n4_O_eq_join h.toL41GPh3 hEO hEW
  have hP : twoCore t = zpowers t := h.p2
  have hle : ctxW t x₁ x₂ ⊔ E ⊔ E.map (MulAut.conj rho).toMonoidHom ≤
      sqSub (l41O2 t x₁ x₂) (fourGrp x₁ x₂) (n4_O_norm_F h.toL41GPh3)
        (fun _ ha _ hb => n4_O_comm h ha hb) := by
    refine sup_le (sup_le ?_ ?_) ?_
    · intro w hw
      refine mem_sqSub.mpr ⟨n4_W_le_O h.toL41GPh3 hw, ?_⟩
      obtain ⟨p, hp, b, hb, rfl⟩ := (mem_sup_iff_of_commute (pt_comm_base h.toCtx0)).mp hw
      have hpb : p * b = b * p := pt_comm_base h.toCtx0 p hp b hb
      have hpp : p * p = 1 := by
        rw [hP] at hp
        rcases pt_eq_one_or_of_mem_zpowers h.hyp.ord_t hp with h1 | h1
        · rw [h1, one_mul]
        · rw [h1]
          exact t_mul_self h.hyp
      have hbb : b * b ∈ fourGrp x₁ x₂ := by
        rw [← pow_two, h.wreath.fourGrp_eq_mho]
        exact Subgroup.subset_closure ⟨b, hb, rfl⟩
      have e : p * b * (p * b) = (p * p) * (b * b) := by
        calc p * b * (p * b) = p * (b * p) * b := by group
          _ = p * (p * b) * b := by rw [hpb]
          _ = (p * p) * (b * b) := by group
      rw [e, hpp, one_mul]
      exact hbb
    · intro e he
      refine mem_sqSub.mpr ⟨hEO he, ?_⟩
      have : e * e = 1 := by
        rw [← pow_two]
        exact hEe.2 e he
      rw [this]
      exact Subgroup.one_mem _
    · intro x hx
      obtain ⟨e, he, rfl⟩ := mem_map_conj.mp hx
      refine mem_sqSub.mpr ⟨pCoreOf_two_conj_mem hρN (hEO he), ?_⟩
      have h1 : e * e = 1 := by
        rw [← pow_two]
        exact hEe.2 e he
      have : rho * e * rho⁻¹ * (rho * e * rho⁻¹) = 1 := by
        calc rho * e * rho⁻¹ * (rho * e * rho⁻¹) = rho * (e * e) * rho⁻¹ := by group
          _ = 1 := by rw [h1]; group
      rw [this]
      exact Subgroup.one_mem _
  rw [hJ] at hle
  exact (mem_sqSub.mp (hle hq)).2

end Mod

end CFSG.OddStandard.SmallF3.HarrisU33.S4A
