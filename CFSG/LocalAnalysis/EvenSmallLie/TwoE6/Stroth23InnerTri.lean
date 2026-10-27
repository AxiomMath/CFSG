module

public import CFSG.LocalAnalysis.EvenSmallLie.TwoE6.Stroth23InnerChar
import CFSG.Monster.B.GSide.TriangleHom1782

public section


attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.EvenSmallLie.TwoE6.Stroth23Inner

open Subgroup CFSG.Monster CFSG.Monster.B CFSG.Monster.B.GSide CFSG.Monster.B.TwoA
  CFSG.Monster.B.TwoA.Amalgam

theorem commute_inv_mul_of_conj_eq {X : Type*} [Group X] {w k₀ k : X}
    (h : k₀ * k * k₀⁻¹ = w * k * w⁻¹) : Commute (w⁻¹ * k₀) k := by
  calc w⁻¹ * k₀ * k = w⁻¹ * (k₀ * k * k₀⁻¹) * k₀ := by group
    _ = w⁻¹ * (w * k * w⁻¹) * k₀ := by rw [h]
    _ = k * (w⁻¹ * k₀) := by group

theorem mem_HS_of_centralizes (j : Fin 2) {k : Shat} (hk : k ∈ triKer j)
    (hc : ∀ x ∈ triKer j, x ∈ HS → Commute k x) : k ∈ HS := by
  fin_cases j
  · exact mem_HS_of_centralizes_zero hk hc
  · exact mem_HS_of_centralizes_one hk hc

theorem clabelS_mem_triKer_HS (j : Fin 2) {v : CVert}
    (hv : v ∈ ({cv0, cw0, cu j} : Set CVert)) : clabelS v ∈ triKer j ∧ clabelS v ∈ HS := by
  rcases hv with rfl | rfl | rfl
  · exact ⟨clabelS_cv0_mem_triKer j, clabelS_cv0_mem_HS⟩
  · exact ⟨clabelS_cw0_mem_triKer j, clabelS_mem_HS_of_adj cgraph_adj_cv0_cw0⟩
  · exact ⟨clabelS_cu_mem_triKer j, clabelS_mem_HS_of_adj (cgraph_adj_cu j).1⟩

theorem conj_clabelS_of_mem_triKer {j : Fin 2} {w : Shat} (hw : w ∈ triKer j) {v : CVert}
    (hv : v ∈ ({cv0, cw0, cu j} : Set CVert)) : w * clabelS v * w⁻¹ = clabelS v := by
  have h1 : cvMul v w⁻¹ = v := cvMul_inv_of_eq (fix_of_mem_triKer hw hv)
  have h2 := GSide.clabelS_cvMul v w⁻¹
  rw [h1, inv_inv] at h2
  exact h2.symm

structure PhiData {G : Type*} [Group G] (Φ : Shat → G) : Prop where
  mul : ∀ x ∈ HS, ∀ x' ∈ HS, Φ (x * x') = Φ x * Φ x'
  inj : ∀ x ∈ HS, ∀ x' ∈ HS, Φ x = Φ x' → x = x'
  cent : ∀ x : G, Commute x (Φ (clabelS cv0)) → ∃ h ∈ HS, Φ h = x

structure LocalData {G : Type*} [Group G] (Φ : Shat → G) (g : G) (y : Shat) : Prop
    extends PhiData Φ where
  swap0 : cvMul cv0 y = cw0
  swap1 : cvMul cw0 y = cv0
  conj : ∀ q ∈ HS, q ∈ cEdgeFix → g * Φ q * g⁻¹ = Φ (y * q * y⁻¹)

namespace PhiData

variable {G : Type*} [Group G] {Φ : Shat → G}

theorem map_one (hD : PhiData Φ) : Φ 1 = 1 := by
  have h : Φ 1 = Φ 1 * Φ 1 :=
    (congrArg Φ (mul_one (1 : Shat)).symm).trans (hD.mul 1 (one_mem _) 1 (one_mem _))
  exact mul_left_cancel (h.symm.trans (mul_one _).symm)

theorem map_inv (hD : PhiData Φ) {x : Shat} (hx : x ∈ HS) : Φ x⁻¹ = (Φ x)⁻¹ :=
  eq_inv_of_mul_eq_one_left ((hD.mul x⁻¹ (inv_mem hx) x hx).symm.trans
    ((congrArg Φ (inv_mul_cancel x)).trans hD.map_one))

theorem map_conj (hD : PhiData Φ) {t k : Shat} (ht : t ∈ HS) (hk : k ∈ HS) :
    Φ t * Φ k * (Φ t)⁻¹ = Φ (t * k * t⁻¹) := by
  rw [hD.mul _ (mul_mem ht hk) _ (inv_mem ht), hD.mul _ ht _ hk, hD.map_inv ht]

theorem commute_iff (hD : PhiData Φ) {x x' : Shat} (hx : x ∈ HS) (hx' : x' ∈ HS) :
    Commute (Φ x) (Φ x') ↔ Commute x x' := by
  constructor
  · intro h
    refine hD.inj _ (mul_mem hx hx') _ (mul_mem hx' hx) ?_
    rw [hD.mul _ hx _ hx', hD.mul _ hx' _ hx]
    exact h.eq
  · intro h
    show Φ x * Φ x' = Φ x' * Φ x
    rw [← hD.mul _ hx _ hx', ← hD.mul _ hx' _ hx, h.eq]

end PhiData

namespace LocalData

variable {G : Type*} [Group G] {Φ : Shat → G} {g : G} {y : Shat}

theorem inv_mul_mem_cEdgeFix (hD : LocalData Φ g y) {j : Fin 2} {b' : Shat}
    (hb' : IsTriB j b') : y⁻¹ * b' ∈ cEdgeFix :=
  ⟨mem_vStab.2 (by rw [cvMul_mul, cvMul_inv_of_eq hD.swap1, hb'.2.1]),
    mem_vStab.2 (by rw [cvMul_mul, cvMul_inv_of_eq hD.swap0, hb'.1])⟩

theorem transport_b (hD : LocalData Φ g y) {j : Fin 2} {b' : Shat} (hb' : IsTriB j b')
    (hyb : y⁻¹ * b' ∈ HS) :
    ∀ k ∈ {x | x ∈ triKer j ∧ x ∈ HS}, b' * k * b'⁻¹ ∈ {x | x ∈ triKer j ∧ x ∈ HS} ∧
      g * Φ (y⁻¹ * b') * Φ k * (g * Φ (y⁻¹ * b'))⁻¹ = Φ (b' * k * b'⁻¹) := by
  intro k hk
  have hpA := hD.inv_mul_mem_cEdgeFix hb'
  have hq : (y⁻¹ * b') * k * (y⁻¹ * b')⁻¹ ∈ HS := mul_mem (mul_mem hyb hk.2) (inv_mem hyb)
  have hqA : (y⁻¹ * b') * k * (y⁻¹ * b')⁻¹ ∈ cEdgeFix :=
    mul_mem (mul_mem hpA hk.1.1) (inv_mem hpA)
  refine ⟨⟨conj_mem_triKer (mem_triStab_of_isTriB hb') hk.1,
    (conj_mem_HS_iff_of_triKer (Or.inr (swap_mem_cEdgeStab hb'.1 hb'.2.1)) hk.1).2 hk.2⟩, ?_⟩
  calc g * Φ (y⁻¹ * b') * Φ k * (g * Φ (y⁻¹ * b'))⁻¹
      = g * (Φ (y⁻¹ * b') * Φ k * (Φ (y⁻¹ * b'))⁻¹) * g⁻¹ := by group
    _ = g * Φ ((y⁻¹ * b') * k * (y⁻¹ * b')⁻¹) * g⁻¹ := by rw [hD.map_conj hyb hk.2]
    _ = Φ (y * ((y⁻¹ * b') * k * (y⁻¹ * b')⁻¹) * y⁻¹) := hD.conj _ hq hqA
    _ = Φ (b' * k * b'⁻¹) := congrArg Φ (by group)

theorem transport_a (hD : LocalData Φ g y) {j : Fin 2} {a' : Shat} (ha' : IsTriA j a')
    (ha'H : a' ∈ HS) :
    ∀ k ∈ {x | x ∈ triKer j ∧ x ∈ HS}, a' * k * a'⁻¹ ∈ {x | x ∈ triKer j ∧ x ∈ HS} ∧
      Φ a' * Φ k * (Φ a')⁻¹ = Φ (a' * k * a'⁻¹) := fun _ hk =>
  ⟨⟨conj_mem_triKer (mem_triStab_of_isTriA ha') hk.1,
    (conj_mem_HS_iff_of_triKer (Or.inl (HS_le ha'H)) hk.1).2 hk.2⟩, hD.map_conj ha'H hk.2⟩

theorem pow_three_mem_HS (hD : LocalData Φ g y) {j : Fin 2} {a' b' : Shat}
    (ha' : IsTriA j a') (ha'H : a' ∈ HS) (hb' : IsTriB j b') (hyb : y⁻¹ * b' ∈ HS) :
    (a' * b') ^ 3 ∈ HS := by
  obtain ⟨w, hw_def⟩ : ∃ w, (a' * b') ^ 3 = w := ⟨_, rfl⟩
  obtain ⟨κ, hκ_def⟩ : ∃ κ, (Φ a' * (g * Φ (y⁻¹ * b'))) ^ 3 = κ := ⟨_, rfl⟩
  have t3 := transport_conj_pow (transport_conj_mul (hD.transport_a ha' ha'H)
    (hD.transport_b hb' hyb)) 3
  rw [hw_def, hκ_def] at t3
  have hw : w ∈ triKer j := hw_def ▸ mul_pow_three_mem_triKer ha' hb'
  have hfix : ∀ v ∈ ({cv0, cw0, cu j} : Set CVert), Commute κ (Φ (clabelS v)) := by
    intro v hv
    have h1 := (t3 (clabelS v) (clabelS_mem_triKer_HS j hv)).2
    rw [conj_clabelS_of_mem_triKer hw hv] at h1
    exact mul_inv_eq_iff_eq_mul.1 h1
  obtain ⟨k₀, hk₀H, hk₀⟩ := hD.cent κ (hfix cv0 (Or.inl rfl))
  have hk₀v : ∀ v ∈ ({cv0, cw0, cu j} : Set CVert), k₀ ∈ vStab v := fun v hv => by
    have h1 := hfix v hv
    rw [← hk₀] at h1
    exact (commute_clabelS_iff_mem v k₀).1
      ((hD.commute_iff hk₀H (clabelS_mem_triKer_HS j hv).2).1 h1)
  have hk₀K : k₀ ∈ triKer j :=
    ⟨⟨hk₀v cv0 (Or.inl rfl), hk₀v cw0 (Or.inr (Or.inl rfl))⟩, hk₀v (cu j) (Or.inr (Or.inr rfl))⟩
  have hc : ∀ x ∈ triKer j, x ∈ HS → Commute (w⁻¹ * k₀) x := by
    intro x hx hxH
    have h1 := (t3 x ⟨hx, hxH⟩).2
    rw [← hk₀, hD.map_conj hk₀H hxH] at h1
    exact commute_inv_mul_of_conj_eq (hD.inj _ (mul_mem (mul_mem hk₀H hxH) (inv_mem hk₀H)) _
      (t3 x ⟨hx, hxH⟩).1.2 h1)
  have hmem := mem_HS_of_centralizes j (mul_mem (inv_mem hw) hk₀K) hc
  have e : w = k₀ * (w⁻¹ * k₀)⁻¹ := by group
  rw [hw_def, e]
  exact mul_mem hk₀H (inv_mem hmem)

end LocalData

end CFSG.EvenSmallLie.TwoE6.Stroth23Inner
