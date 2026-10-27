module

public import CFSG.HardMathSupport.Solomon.Coordinator.I23_26MCPi
public import CFSG.HardMathSupport.Solomon.Coordinator.I23_26MCE

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB
open scoped commutatorElement

variable {Y : Type*} [Group Y] [Finite Y] {K E : Subgroup Y}

@[expose] def mcM (K E : Subgroup Y) : Subgroup Y :=
  ⨆ (e : Y) (_ : e ∈ E) (_ : e ≠ 1),
    GLAPLayer 3 (mcPi K E ⊓ Subgroup.centralizer ({e} : Set Y))

@[expose] def mcGen (K E : Subgroup Y) : Set Y :=
  {d | ∃ e ∈ E, ∃ g ∈ E, g ^ 3 = 1 ∧ GLBConj g K ≠ K ∧ ∃ k ∈ GLBConj e K, d = mcD g k}

@[expose] def mcT (K E : Subgroup Y) : Subgroup Y := Subgroup.closure (mcGen K E)

theorem mc_three_conj {K : Subgroup Y} (e : Y)
    (h3 : 3 ∣ Nat.card (↥K ⧸ Subgroup.center ↥K)) :
    3 ∣ Nat.card (↥(GLBConj e K) ⧸ Subgroup.center ↥(GLBConj e K)) := by
  let φ : ↥K ≃* ↥(GLBConj e K) :=
    K.equivMapOfInjective (MulAut.conj e⁻¹).toMonoidHom (MulAut.conj e⁻¹).injective
  have hc : (Subgroup.center ↥K).map (φ : ↥K →* ↥(GLBConj e K)) =
      Subgroup.center ↥(GLBConj e K) := Subgroup.map_center_eq φ
  have := Nat.card_congr
    (QuotientGroup.congr (Subgroup.center ↥K) (Subgroup.center ↥(GLBConj e K)) φ hc).toEquiv
  rw [← this]
  exact h3

theorem mc_gen_mem_pi {d : Y} (hd : d ∈ mcGen K E) : d ∈ mcPi K E := by
  obtain ⟨e, he, g, hg, hg3, hgK, k, hk, rfl⟩ := hd
  unfold mcD
  have h1 : k ∈ mcPi K E := mc_le_pi he hk
  have h2 : g⁻¹ * k * g ∈ mcPi K E := by
    have : g⁻¹ * k * g ∈ GLBConj (e * g) K := by
      rw [← mc_conj_conj]; exact mc_mem_conj hk
    exact mc_le_pi (E.mul_mem he hg) this
  have h3 : g * k * g⁻¹ ∈ mcPi K E := by
    have : g * k * g⁻¹ ∈ GLBConj (e * g⁻¹) K := by
      rw [← mc_conj_conj]; exact mc_mem_conj_inv hk
    exact mc_le_pi (E.mul_mem he (E.inv_mem hg)) this
  exact (mcPi K E).mul_mem ((mcPi K E).mul_mem h1 h2) h3

theorem mc_T_le_pi : mcT K E ≤ mcPi K E :=
  (Subgroup.closure_le _).2 fun _ hd => mc_gen_mem_pi hd

theorem mc_hT (hK : IsComponentOf K ⊤) (hEc : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a) {g : Y}
    (hg : g ∈ E) (hg3 : g ^ 3 = 1) (hgK : GLBConj g K ≠ K) {e : Y} (he : e ∈ E) :
    (mcT K E).subgroupOf (mcPi K E) ⊔ mcA K E e = ⊤ := by
  rw [eq_top_iff]
  intro q _
  obtain ⟨k, hk, a, haP, hac, hq⟩ := mc_pi_decomp hK he q.2
  have hKe := mc_isComponentOf_gLBConj hK e
  have hne : GLBConj g (GLBConj e K) ≠ GLBConj e K := mc_moves hEc he hg hgK
  have hdgen : mcD g k ∈ mcGen K E := ⟨e, he, g, hg, hg3, hgK, k, hk, rfl⟩
  have hdT : mcD g k ∈ mcT K E := Subgroup.subset_closure hdgen
  have hdP : mcD g k ∈ mcPi K E := mc_gen_mem_pi hdgen
  have ha0 : (mcD g k)⁻¹ * k ∈ mcPi K E :=
    (mcPi K E).mul_mem ((mcPi K E).inv_mem hdP) (mc_le_pi he hk)
  have ha0c : ∀ y ∈ GLBConj e K, y * ((mcD g k)⁻¹ * k) = ((mcD g k)⁻¹ * k) * y :=
    fun y hy => mcD_inv_mul_comm hKe hg3 hne hk hy
  have hx : (⟨mcD g k, hdP⟩ : ↥(mcPi K E)) ∈ (mcT K E).subgroupOf (mcPi K E) := hdT
  have hz : (⟨(mcD g k)⁻¹ * k, ha0⟩ * ⟨a, haP⟩ : ↥(mcPi K E)) ∈ mcA K E e :=
    (mcA K E e).mul_mem (mem_mcA.2 ha0c) (mem_mcA.2 hac)
  have hqeq : q = ⟨mcD g k, hdP⟩ * (⟨(mcD g k)⁻¹ * k, ha0⟩ * ⟨a, haP⟩ : ↥(mcPi K E)) := by
    apply Subtype.ext
    show (q : Y) = mcD g k * (((mcD g k)⁻¹ * k) * a)
    rw [hq]; group
  rw [hqeq]
  exact Subgroup.mul_mem_sup hx hz

theorem mc_exists_not_mem (hK : IsComponentOf K ⊤) (hE1 : (1 : Y) ∈ E) {g : Y} (hg : g ∈ E)
    (hg3 : g ^ 3 = 1) (hgK : GLBConj g K ≠ K) :
    ∃ t ∈ (mcT K E).subgroupOf (mcPi K E), t ∉ mcA K E 1 := by
  have hK1 : GLBConj 1 K = K := gLBConj_one K
  obtain ⟨u, v, huv⟩ := mc_exists_noncomm hK.2.2
  have hu : (u : Y) ∈ GLBConj 1 K := by rw [hK1]; exact u.2
  have hv : (v : Y) ∈ GLBConj 1 K := by rw [hK1]; exact v.2
  have hgen : mcD g (u : Y) ∈ mcGen K E := ⟨1, hE1, g, hg, hg3, hgK, u, hu, rfl⟩
  have hdP : mcD g (u : Y) ∈ mcPi K E := mc_gen_mem_pi hgen
  refine ⟨⟨mcD g (u : Y), hdP⟩, Subgroup.subset_closure hgen, fun hmem => ?_⟩
  rw [mem_mcA] at hmem
  have hKe : IsComponentOf (GLBConj 1 K) ⊤ := mc_isComponentOf_gLBConj hK 1
  have hne : GLBConj g (GLBConj 1 K) ≠ GLBConj 1 K := by
    rw [hK1]; exact hgK
  have h1 : (v : Y) * mcD g (u : Y) = mcD g (u : Y) * v := hmem v hv
  have h2 := mcD_inv_mul_comm hKe hg3 hne hu hv
  apply huv
  apply Subtype.ext
  show (u : Y) * v = v * u
  calc (u : Y) * v = (mcD g (u : Y)) * ((mcD g (u : Y))⁻¹ * u) * v := by group
    _ = (mcD g (u : Y)) * (((mcD g (u : Y))⁻¹ * u) * v) := by group
    _ = (mcD g (u : Y)) * (v * ((mcD g (u : Y))⁻¹ * u)) := by rw [← h2]
    _ = (mcD g (u : Y) * v) * ((mcD g (u : Y))⁻¹ * u) := by group
    _ = (v * mcD g (u : Y)) * ((mcD g (u : Y))⁻¹ * u) := by rw [h1]
    _ = v * u := by group

theorem mc_gen_conj (hEc : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a) {a : Y} (ha : a ∈ E) {d : Y}
    (hd : d ∈ mcGen K E) : a * d * a⁻¹ ∈ mcGen K E := by
  obtain ⟨e, he, g, hg, hg3, hgK, k, hk, rfl⟩ := hd
  refine ⟨e * a⁻¹, E.mul_mem he (E.inv_mem ha), g, hg, hg3, hgK, a * k * a⁻¹, ?_, ?_⟩
  · rw [mem_gLBConj]
    have : e * a⁻¹ * (a * k * a⁻¹) * (e * a⁻¹)⁻¹ = e * k * e⁻¹ := by group
    rw [this]
    exact mem_gLBConj.1 hk
  · exact mcD_conj (hEc a ha g hg)

theorem mc_T_conj (hEc : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a) {a : Y} (ha : a ∈ E) {y : Y}
    (hy : y ∈ mcT K E) : a * y * a⁻¹ ∈ mcT K E := by
  induction hy using Subgroup.closure_induction with
  | mem x hx => exact Subgroup.subset_closure (mc_gen_conj hEc ha hx)
  | one => simp
  | mul x z _ _ hx hz =>
    have e : a * (x * z) * a⁻¹ = (a * x * a⁻¹) * (a * z * a⁻¹) := by group
    rw [e]; exact (mcT K E).mul_mem hx hz
  | inv x _ hx =>
    have e : a * x⁻¹ * a⁻¹ = (a * x * a⁻¹)⁻¹ := by group
    rw [e]; exact (mcT K E).inv_mem hx

theorem mc_le_T_of_conj (hEc : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a) {e : Y} (he : e ∈ E)
    (h : GLBConj e K ≤ mcT K E) : K ≤ mcT K E := by
  intro k hk
  have h1 : e⁻¹ * k * e ∈ mcT K E := h (mc_mem_conj hk)
  have := mc_T_conj hEc he h1
  have e2 : e * (e⁻¹ * k * e) * e⁻¹ = k := by group
  rwa [e2] at this

theorem mc_T_le_M (hK : IsComponentOf K ⊤) (hEc : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a)
    (h3 : 3 ∣ Nat.card (↥K ⧸ Subgroup.center ↥K)) : mcT K E ≤ mcM K E := by
  refine (Subgroup.closure_le _).2 ?_
  rintro d ⟨e, he, g, hg, hg3, hgK, k, hk, rfl⟩
  have hKe := mc_isComponentOf_gLBConj hK e
  have hne : GLBConj g (GLBConj e K) ≠ GLBConj e K := mc_moves hEc he hg hgK
  have h3e := mc_three_conj (K := K) e h3
  obtain ⟨D, hDq, hD3, hDmem, hDg⟩ := mc_diag_exists hKe hg3 hne h3e
  have hg1 : g ≠ 1 := by
    rintro rfl
    exact hgK (gLBConj_one K)
  have hDS : D ≤ mcPi K E ⊓ Subgroup.centralizer ({g} : Set Y) := by
    intro x hx
    obtain ⟨k', hk', rfl⟩ := (hDmem x).1 hx
    refine Subgroup.mem_inf.2 ⟨mc_gen_mem_pi ⟨e, he, g, hg, hg3, hgK, k', hk', rfl⟩, ?_⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    have := hDg _ hx
    calc mcD g k' * g = g * (g⁻¹ * mcD g k' * g) := by group
      _ = g * mcD g k' := by rw [this]
  have hnormal : (D.subgroupOf (mcPi K E ⊓ Subgroup.centralizer ({g} : Set Y))).Normal := by
    rw [Subgroup.normal_subgroupOf_iff hDS]
    intro x c hx hc
    obtain ⟨k', hk', rfl⟩ := (hDmem x).1 hx
    obtain ⟨hcP, hcg⟩ := Subgroup.mem_inf.1 hc
    have hcg' : c * g = g * c := Subgroup.mem_centralizer_singleton_iff.1 hcg
    rw [mcD_conj hcg']
    refine (hDmem _).2 ⟨c * k' * c⁻¹, ?_, rfl⟩
    have := Subgroup.mem_normalizer_iff.1 (mc_pi_le_normalizer hK e hcP) k'
    exact this.1 hk'
  have hcomp := mc_glaPComponent_three hDS hnormal hDq hD3
  have hDle : D ≤ GLAPLayer 3 (mcPi K E ⊓ Subgroup.centralizer ({g} : Set Y)) := le_sSup hcomp
  have hDM : D ≤ mcM K E :=
    hDle.trans (le_iSup₂_of_le g hg (le_iSup_of_le hg1 le_rfl))
  exact hDM ((hDmem _).2 ⟨k, hk, rfl⟩)

end CFSG.HardMathSupport.Solomon.Coordinator
