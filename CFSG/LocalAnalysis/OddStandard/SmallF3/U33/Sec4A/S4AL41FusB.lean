module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4A.S4AL41FusA
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4A.S4AL43A
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4A.S4AGenB
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4A.S4AC0C

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33.S4A

open Subgroup
open scoped Pointwise

variable {G : Type} [Group G] [Finite G] {t : G} {L S : Subgroup G} {x₁ x₂ lam rho : G}

theorem mem_zpowers_cases_of_mul_self {z g : G} (hz : z * z = 1) (hg : g ∈ zpowers z) :
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

theorem l41_orbit_NS (h : L41GPh1 t L S x₁ x₂ lam rho) (h2 : 2 ∣ S.index) :
    conjIn (normalizer (S : Set G)) t = t • (zpowers ((x₁ * x₂) ^ 2) : Set G) := by
  ext u
  constructor
  · rintro ⟨k, hk, hku⟩
    rw [← hku]
    rcases l41_conj_t_cases h hk with h1 | h1
    · rw [h1]
      exact Set.mem_smul_set.mpr ⟨1, Subgroup.one_mem _, by simp⟩
    · rw [h1]
      exact Set.mem_smul_set.mpr ⟨(x₁ * x₂) ^ 2, Subgroup.mem_zpowers _, by simp⟩
  · intro hu
    obtain ⟨w, hw, hwu⟩ := Set.mem_smul_set.mp hu
    rw [← hwu]
    rcases mem_zpowers_cases_of_mul_self (z_mul_self_ne_one h.toCtx0).1 hw with hw1 | hwz
    · rw [hw1]
      exact ⟨1, Subgroup.one_mem _, by simp⟩
    · rw [hwz]
      exact l41_exists_swap h h2

theorem l41_conj_t_mul (h : L41GPh2 t L S x₁ x₂ lam rho) {u c : G} (hcL : c ∈ L)
    (hcz : c * (x₁ * x₂) ^ 2 * c⁻¹ = u) : ∃ g : G, g * t * g⁻¹ = t * u := by
  obtain ⟨n, -, hn⟩ := l41_exists_swap h.toL41GPh1 h.sylow
  have hct : c * t = t * c := mem_invCent_iff.mp (L_le_invCent h.hyp hcL)
  refine ⟨c * n, ?_⟩
  calc c * n * t * (c * n)⁻¹ = c * (n * t * n⁻¹) * c⁻¹ := by group
    _ = c * (t * (x₁ * x₂) ^ 2) * c⁻¹ := by rw [hn]
    _ = (c * t) * (x₁ * x₂) ^ 2 * c⁻¹ := by group
    _ = (t * c) * (x₁ * x₂) ^ 2 * c⁻¹ := by rw [hct]
    _ = t * (c * (x₁ * x₂) ^ 2 * c⁻¹) := by group
    _ = t * u := by rw [hcz]

theorem exists_conj_z_of_mem_fourGrp (h : Ctx0 t L S x₁ x₂ lam rho) {v : G}
    (hv : v ∈ fourGrp x₁ x₂) (hv1 : v ≠ 1) : ∃ c ∈ L, c * (x₁ * x₂) ^ 2 * c⁻¹ = v := by
  have hv' : v ∈ closure {x₁ ^ 2, (x₁ * x₂) ^ 2} := hv
  rcases mem_closure_pair_cases (a := x₁ ^ 2) (b := (x₁ * x₂) ^ 2)
    (y_commute_z h.wreath) (y_mul_self_ne_one h.wreath).1 (z_mul_self_ne_one h).1 hv' with
    h1 | h1 | h1 | h1
  · exact absurd h1 hv1
  · rw [h1]
    exact h.invol_L (x₁ ^ 2) (y_z_mem_L h).1 (y_mul_self_ne_one h.wreath).1
      (y_mul_self_ne_one h.wreath).2
  · exact ⟨1, L.one_mem, by rw [h1]; group⟩
  · rw [h1]
    exact h.invol_L (x₁ ^ 2 * (x₁ * x₂) ^ 2)
      (L.mul_mem (y_z_mem_L h).1 (y_z_mem_L h).2)
      (yz_mul_self_ne_one h.wreath).1 (yz_mul_self_ne_one h.wreath).2

theorem l41_conj_t_mul_four (h : L41GPh2 t L S x₁ x₂ lam rho) {f : G}
    (hf : f ∈ fourGrp x₁ x₂) : ∃ g : G, g * t * g⁻¹ = t * f := by
  by_cases hf1 : f = 1
  · exact ⟨1, by simp [hf1]⟩
  · obtain ⟨c, hcL, hcz⟩ := exists_conj_z_of_mem_fourGrp h.toCtx0 hf hf1
    exact l41_conj_t_mul h hcL hcz

theorem l41_false_of_conj_eq_of_conj_z (h : L41GPh1 t L S x₁ x₂ lam rho) {v c : G}
    (hcL : c ∈ L) (hcv : c * (x₁ * x₂) ^ 2 * c⁻¹ = v) {g : G}
    (hconj : g * t * g⁻¹ = v) : False :=
  l41_not_conj_z h ⟨c⁻¹ * g, by
    calc (c⁻¹ * g) * t * (c⁻¹ * g)⁻¹
        = c⁻¹ * (g * t * g⁻¹) * c := by group
      _ = c⁻¹ * v * c := by rw [hconj]
      _ = c⁻¹ * (c * (x₁ * x₂) ^ 2 * c⁻¹) * c := by rw [← hcv]
      _ = (x₁ * x₂) ^ 2 := by group⟩

theorem l41_tG_inf_four (h : L41GPh1 t L S x₁ x₂ lam rho) :
    ∀ g : G, ∀ v ∈ fourGrp x₁ x₂, g * t * g⁻¹ ≠ v := by
  intro g v hv hconj
  have hv' : v ∈ closure {x₁ ^ 2, (x₁ * x₂) ^ 2} := hv
  have hcases := mem_closure_pair_cases (a := x₁ ^ 2) (b := (x₁ * x₂) ^ 2)
    (y_commute_z h.wreath) (y_mul_self_ne_one h.wreath).1
    (z_mul_self_ne_one h.toCtx0).1 hv'
  rcases hcases with h1 | h1 | h1 | h1
  ·
    rw [h1] at hconj
    exact t_ne_one h.hyp (by
      calc t = g⁻¹ * (g * t * g⁻¹) * g := by group
        _ = 1 := by rw [hconj]; group)
  ·
    rw [h1] at hconj
    obtain ⟨c, hcL, hcz⟩ := h.invol_L (x₁ ^ 2) (y_z_mem_L h.toCtx0).1
      (y_mul_self_ne_one h.wreath).1 (y_mul_self_ne_one h.wreath).2
    exact l41_false_of_conj_eq_of_conj_z h hcL hcz hconj
  ·
    rw [h1] at hconj
    exact l41_not_conj_z h ⟨g, hconj⟩
  ·
    rw [h1] at hconj
    obtain ⟨c, hcL, hcz⟩ := h.invol_L (x₁ ^ 2 * (x₁ * x₂) ^ 2)
      (L.mul_mem (y_z_mem_L h.toCtx0).1 (y_z_mem_L h.toCtx0).2)
      (yz_mul_self_ne_one h.wreath).1 (yz_mul_self_ne_one h.wreath).2
    exact l41_false_of_conj_eq_of_conj_z h hcL hcz hconj

theorem pow_four_mem_twoCore_of_mem_ctxW_ctx0 (h : Ctx0 t L S x₁ x₂ lam rho) {w : G}
    (hw : w ∈ ctxW t x₁ x₂) : w ^ 4 ∈ twoCore t := by
  haveI : IsMulCommutative (ctxW t x₁ x₂) := h.abelian_W
  have hbase_le_W : baseGrp x₁ x₂ ≤ ctxW t x₁ x₂ := le_sup_right
  have hcommW : ∀ a ∈ ctxW t x₁ x₂, ∀ b ∈ ctxW t x₁ x₂, a * b = b * a := by
    intro a ha b hb
    simpa using congrArg Subtype.val
      (mul_comm' (⟨a, ha⟩ : ctxW t x₁ x₂) (⟨b, hb⟩ : ctxW t x₁ x₂))
  have hbase_le_L : baseGrp x₁ x₂ ≤ L := by
    obtain ⟨hx₁, hx₂, -⟩ := generators_mem_L h
    refine (Subgroup.closure_le (K := L)).mpr ?_
    intro g hg
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
    rcases hg with rfl | rfl
    · exact hx₁
    · exact hx₂
  have hbase_pow : ∀ b ∈ baseGrp x₁ x₂, b ^ 4 = 1 := by
    intro b hb
    change b ∈ closure ({x₁, x₂} : Set G) at hb
    refine Subgroup.closure_induction (p := fun b _ => b ^ 4 = 1) ?_ ?_ ?_ ?_ hb
    · intro y hy
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
      rcases hy with rfl | rfl
      · rw [← h.wreath.ord_x₁, pow_orderOf_eq_one]
      · rw [← h.wreath.ord_x₂, pow_orderOf_eq_one]
    · simp
    · intro x y hx hy ihx ihy
      have hxW : x ∈ ctxW t x₁ x₂ := hbase_le_W (show x ∈ baseGrp x₁ x₂ from hx)
      have hyW : y ∈ ctxW t x₁ x₂ := hbase_le_W (show y ∈ baseGrp x₁ x₂ from hy)
      have hc : Commute x y := hcommW x hxW y hyW
      rw [hc.mul_pow 4, ihx, ihy, mul_one]
    · intro x hx ihx
      simpa [ihx] using inv_pow x 4
  have hcomm_P_B : ∀ a ∈ twoCore t, ∀ b ∈ baseGrp x₁ x₂, a * b = b * a :=
    fun a ha b hb => twoCore_commute h.hyp a ha b (hbase_le_L hb)
  obtain ⟨q, hq, b, hb, hwb⟩ := (mem_sup_iff_of_commute hcomm_P_B).mp hw
  have hc : Commute q b := hcomm_P_B q hq b hb
  rw [hwb, hc.mul_pow 4, hbase_pow b hb, mul_one]
  exact Subgroup.pow_mem (twoCore t) hq 4

theorem wreathGrp_le_L (h : Ctx0 t L S x₁ x₂ lam rho) : wreathGrp x₁ x₂ lam ≤ L := by
  rw [← h.inf_eq]
  exact inf_le_right

theorem l41_not_conj_T (h : L41GPh1 t L S x₁ x₂ lam rho) :
    ∀ u ∈ wreathGrp x₁ x₂ lam, ∀ g : G, g * t * g⁻¹ ≠ u := by
  intro u hu g hgu
  have hu2 : u * u = 1 := by
    rw [← hgu]
    calc g * t * g⁻¹ * (g * t * g⁻¹) = g * (t * t) * g⁻¹ := by group
      _ = 1 := by rw [t_mul_self h.hyp]; group
  have hu1 : u ≠ 1 := by
    intro h1
    rw [h1] at hgu
    exact t_ne_one h.hyp (by
      calc t = g⁻¹ * (g * t * g⁻¹) * g := by group
        _ = 1 := by rw [hgu]; group)
  obtain ⟨c, hcL, hcz⟩ := h.invol_L u (wreathGrp_le_L h.toCtx0 hu) hu2 hu1
  exact l41_false_of_conj_eq_of_conj_z h hcL hcz hgu

theorem l41_conj_tu (h : L41GPh2 t L S x₁ x₂ lam rho) :
    ∀ u ∈ wreathGrp x₁ x₂ lam, u * u = 1 → u ≠ 1 → ∃ g : G, g * t * g⁻¹ = t * u := by
  intro u hu hu2 hu1
  obtain ⟨c, hcL, hcz⟩ := h.invol_L u (wreathGrp_le_L h.toCtx0 hu) hu2 hu1
  exact l41_conj_t_mul h hcL hcz

theorem l41_card_P_le (h : L41GPh2 t L S x₁ x₂ lam rho) : Nat.card (twoCore t) ≤ 4 := by
  rcases card_twoCore_cases h.hyp with h2c | h4 | h8
  · omega
  · omega
  · exfalso
    obtain ⟨p, hp, hp4⟩ := exists_fourth_root_of_eight_le_card h.hyp h8
    obtain ⟨n, hn, hnt⟩ := l41_exists_swap h.toL41GPh1 h.sylow
    have hpW : p ∈ ctxW t x₁ x₂ := Subgroup.mem_sup_left hp
    have hnW : n ∈ normalizer ((ctxW t x₁ x₂ : Subgroup G) : Set G) := h.basic.norm_S_le n hn
    have hwW : n * p * n⁻¹ ∈ ctxW t x₁ x₂ := ((Subgroup.mem_set_normalizer_iff).mp hnW p).mp hpW
    have hw4 : (n * p * n⁻¹) ^ 4 ∈ twoCore t :=
      pow_four_mem_twoCore_of_mem_ctxW_ctx0 h.toCtx0 hwW
    have htz : (n * p * n⁻¹) ^ 4 = t * (x₁ * x₂) ^ 2 := by
      rw [conj_pow, hp4, hnt]
    have htz_mem : t * (x₁ * x₂) ^ 2 ∈ twoCore t := by
      rwa [htz] at hw4
    have hz_mem : (x₁ * x₂) ^ 2 ∈ twoCore t := by
      have hmem : t⁻¹ * (t * (x₁ * x₂) ^ 2) ∈ twoCore t :=
        Subgroup.mul_mem (twoCore t) (Subgroup.inv_mem (twoCore t) h.hyp.mem_twoCore) htz_mem
      simpa using hmem
    have hz_inf : (x₁ * x₂) ^ 2 ∈ twoCore t ⊓ L := ⟨hz_mem, (y_z_mem_L h.toCtx0).2⟩
    rw [h.hyp.twoCore_inf, Subgroup.mem_bot] at hz_inf
    exact (z_mul_self_ne_one h.toCtx0).2 hz_inf

theorem mem_ctxE_cases (h : Ctx0 t L S x₁ x₂ lam rho) {a : G} (ha : a ∈ ctxE t x₁ x₂) :
    ∃ f ∈ fourGrp x₁ x₂, a = f ∨ a = t * f := by
  have ht2 : t * t = 1 := t_mul_self h.hyp
  have hFL : fourGrp x₁ x₂ ≤ L := by
    refine (Subgroup.closure_le (K := L)).mpr ?_
    intro g hg
    rcases hg with hg | hg
    · rw [hg]; exact (y_z_mem_L h).1
    · rw [Set.mem_singleton_iff.mp hg]; exact (y_z_mem_L h).2
  have htc : ∀ f ∈ fourGrp x₁ x₂, t * f = f * t := fun f hf =>
    (mem_invCent_iff.mp (L_le_invCent h.hyp (hFL hf))).symm
  have hy : x₁ ^ 2 ∈ fourGrp x₁ x₂ := Subgroup.subset_closure (by simp)
  have hz : (x₁ * x₂) ^ 2 ∈ fourGrp x₁ x₂ := Subgroup.subset_closure (by simp)
  have ha' : a ∈ closure ({t, x₁ ^ 2, (x₁ * x₂) ^ 2} : Set G) := ha
  refine Subgroup.closure_induction
    (p := fun a _ => ∃ f ∈ fourGrp x₁ x₂, a = f ∨ a = t * f) ?_ ?_ ?_ ?_ ha'
  · intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with hx | hx | hx
    · exact ⟨1, Subgroup.one_mem _, Or.inr (by rw [hx, mul_one])⟩
    · exact ⟨x, hx ▸ hy, Or.inl rfl⟩
    · exact ⟨x, hx ▸ hz, Or.inl rfl⟩
  · exact ⟨1, Subgroup.one_mem _, Or.inl rfl⟩
  · intro x y _ _ hx hy'
    obtain ⟨f₁, hf₁, hx1 | hx1⟩ := hx <;> obtain ⟨f₂, hf₂, hy1 | hy1⟩ := hy'
    · exact ⟨f₁ * f₂, Subgroup.mul_mem _ hf₁ hf₂, Or.inl (by rw [hx1, hy1])⟩
    · refine ⟨f₁ * f₂, Subgroup.mul_mem _ hf₁ hf₂, Or.inr ?_⟩
      rw [hx1, hy1, ← mul_assoc, ← mul_assoc, ← htc f₁ hf₁]
    · exact ⟨f₁ * f₂, Subgroup.mul_mem _ hf₁ hf₂, Or.inr (by rw [hx1, hy1, mul_assoc])⟩
    · refine ⟨f₁ * f₂, Subgroup.mul_mem _ hf₁ hf₂, Or.inl ?_⟩
      rw [hx1, hy1]
      calc t * f₁ * (t * f₂) = t * (f₁ * t) * f₂ := by group
        _ = t * (t * f₁) * f₂ := by rw [← htc f₁ hf₁]
        _ = (t * t) * f₁ * f₂ := by group
        _ = f₁ * f₂ := by rw [ht2, one_mul]
  · intro x _ hx
    obtain ⟨f, hf, hx1 | hx1⟩ := hx
    · exact ⟨f⁻¹, Subgroup.inv_mem _ hf, Or.inl (by rw [hx1])⟩
    · refine ⟨f⁻¹, Subgroup.inv_mem _ hf, Or.inr ?_⟩
      have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht2
      rw [hx1, mul_inv_rev, htinv]
      have hfi : t * f⁻¹ = f⁻¹ * t := htc f⁻¹ (Subgroup.inv_mem _ hf)
      exact hfi.symm

theorem l41_tG_A (h : L41GPh2 t L S x₁ x₂ lam rho) :
    ∀ a ∈ ctxE t x₁ x₂, (∃ g : G, g * t * g⁻¹ = a) ↔ ∃ f ∈ fourGrp x₁ x₂, a = t * f := by
  intro a ha
  constructor
  · rintro ⟨g, hg⟩
    obtain ⟨f, hf, hfa | hfa⟩ := mem_ctxE_cases h.toCtx0 ha
    · exact absurd (hg.trans hfa) (l41_tG_inf_four h.toL41GPh1 g f hf)
    · exact ⟨f, hf, hfa⟩
  · rintro ⟨f, hf, rfl⟩
    exact l41_conj_t_mul_four h hf

theorem l41_zG_A (h : L41GPh2 t L S x₁ x₂ lam rho) :
    ∀ a ∈ ctxE t x₁ x₂, (∃ g : G, g * (x₁ * x₂) ^ 2 * g⁻¹ = a) ↔
      a ∈ fourGrp x₁ x₂ ∧ a ≠ 1 := by
  intro a ha
  constructor
  · rintro ⟨g, hg⟩
    have ha1 : a ≠ 1 := by
      intro h1
      rw [h1] at hg
      exact (z_mul_self_ne_one h.toCtx0).2 (by
        calc (x₁ * x₂) ^ 2 = g⁻¹ * (g * (x₁ * x₂) ^ 2 * g⁻¹) * g := by group
          _ = 1 := by rw [hg]; group)
    obtain ⟨f, hf, hfa | hfa⟩ := mem_ctxE_cases h.toCtx0 ha
    · exact ⟨hfa ▸ hf, ha1⟩
    · exfalso
      obtain ⟨m, hm⟩ := l41_conj_t_mul_four h hf
      refine l41_not_conj_z h.toL41GPh1 ⟨g⁻¹ * m, ?_⟩
      calc (g⁻¹ * m) * t * (g⁻¹ * m)⁻¹ = g⁻¹ * (m * t * m⁻¹) * g := by group
        _ = g⁻¹ * (t * f) * g := by rw [hm]
        _ = g⁻¹ * (g * (x₁ * x₂) ^ 2 * g⁻¹) * g := by rw [← hfa, ← hg]
        _ = (x₁ * x₂) ^ 2 := by group
  · rintro ⟨hf, hf1⟩
    obtain ⟨c, -, hcz⟩ := exists_conj_z_of_mem_fourGrp h.toCtx0 hf hf1
    exact ⟨c, hcz⟩

theorem l41_fusion_of (hc : L41GPh2 t L S x₁ x₂ lam rho) : L41Fusion t S x₁ x₂ lam :=
  { not_conj_z := fun g hg => S4A.l41_not_conj_z hc.toL41GPh1 ⟨g, hg⟩
    not_conj_T := S4A.l41_not_conj_T hc.toL41GPh1
    conj_tu := S4A.l41_conj_tu hc
    orbit_NS := S4A.l41_orbit_NS hc.toL41GPh1 hc.sylow
    card_P_le := S4A.l41_card_P_le hc
    tG_A := S4A.l41_tG_A hc
    zG_A := S4A.l41_zG_A hc }

end CFSG.OddStandard.SmallF3.HarrisU33.S4A

namespace CFSG.OddStandard.SmallF3.HarrisU33

theorem l41_fusion_holds : L41FusionStmt := fun hc => S4A.l41_fusion_of hc.toG

end CFSG.OddStandard.SmallF3.HarrisU33
