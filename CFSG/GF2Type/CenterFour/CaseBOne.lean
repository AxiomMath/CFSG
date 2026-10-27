module

public import CFSG.GF2Type.CenterFour.CaseBPsiBasic
public import CFSG.GF2Type.CenterFour.CaseBFusion

public section

namespace CFSG.GF2Type.CenterFour

open Subgroup
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {z : G} {n : ℕ}

private theorem comm_eq_sq_mul_of_involutions {u v : G} (hu : u * u = 1) (hv : v * v = 1) :
    ⁅u, v⁆ = (u * v) ^ 2 := by
  have iu : u⁻¹ = u := inv_eq_of_mul_eq_one_right hu
  have iv : v⁻¹ = v := inv_eq_of_mul_eq_one_right hv
  rw [commutatorElement_def, iu, iv, sq]
  simp only [mul_assoc]

private theorem mul_self_eq_one_of_inv {z₁ δ : G} (h1 : z₁ * z₁ = 1)
    (hinv : z₁ * δ * z₁ = δ⁻¹) : (z₁ * δ) * (z₁ * δ) = 1 := by
  calc (z₁ * δ) * (z₁ * δ) = (z₁ * δ * z₁) * δ := by group
    _ = δ⁻¹ * δ := by rw [hinv]
    _ = 1 := inv_mul_cancel δ

private theorem sq_of_mul_eq {z₁ δ : G} (h1 : z₁ * z₁ = 1) :
    (z₁ * (z₁ * δ)) ^ 2 = δ ^ 2 := by
  rw [← mul_assoc, h1, one_mul]

private theorem fused_mul_psi (g q : G) (hz1 : g⁻¹ * z * g * (g⁻¹ * z * g) = 1) :
    Fused z (g⁻¹ * z * g * psi (g⁻¹ * z * g) q) := by
  have e : g⁻¹ * z * g * psi (g⁻¹ * z * g) q = q * (g⁻¹ * z * g) * q⁻¹ := by
    unfold psi
    calc g⁻¹ * z * g * (g⁻¹ * z * g * (q * (g⁻¹ * z * g) * q⁻¹))
        = (g⁻¹ * z * g * (g⁻¹ * z * g)) * (q * (g⁻¹ * z * g) * q⁻¹) := by group
      _ = q * (g⁻¹ * z * g) * q⁻¹ := by rw [hz1, one_mul]
  refine ⟨g * q⁻¹, ?_⟩
  rw [e]
  group

private theorem card_le_four_of_inter (J K₁ K₂ : Subgroup G)
    (hA : ∀ x ∈ J, ∀ y ∈ J, x ∉ K₁ → y ∉ K₁ → x * y ∈ K₁)
    (hB : ∀ x ∈ J, ∀ y ∈ J, x ∉ K₂ → y ∉ K₂ → x * y ∈ K₂)
    (hC0 : ∀ x ∈ J, x ∈ K₁ → x ∈ K₂ → x = 1) : Nat.card J ≤ 4 := by
  classical
  let f : J → Bool × Bool := fun x => (decide ((x : G) ∈ K₁), decide ((x : G) ∈ K₂))
  have hf : Function.Injective f := by
    intro x y hxy
    simp only [f, Prod.mk.injEq] at hxy
    obtain ⟨e1, e2⟩ := hxy
    rw [decide_eq_decide] at e1 e2
    have hxJ : (x : G) ∈ J := x.2
    have hyJ : (y : G) ∈ J := y.2
    have hmJ : (x : G)⁻¹ * (y : G) ∈ J := J.mul_mem (J.inv_mem hxJ) hyJ
    have hinv : ∀ S : Subgroup G, (x : G) ∉ S → (x : G)⁻¹ ∉ S := fun S hx h =>
      hx (by simpa using S.inv_mem h)
    have hm1 : (x : G)⁻¹ * (y : G) ∈ K₁ := by
      by_cases hx1 : (x : G) ∈ K₁
      · exact K₁.mul_mem (K₁.inv_mem hx1) (e1.mp hx1)
      · exact hA _ (J.inv_mem hxJ) _ hyJ (hinv K₁ hx1) (fun h => hx1 (e1.mpr h))
    have hm2 : (x : G)⁻¹ * (y : G) ∈ K₂ := by
      by_cases hx2 : (x : G) ∈ K₂
      · exact K₂.mul_mem (K₂.inv_mem hx2) (e2.mp hx2)
      · exact hB _ (J.inv_mem hxJ) _ hyJ (hinv K₂ hx2) (fun h => hx2 (e2.mpr h))
    exact Subtype.ext (inv_mul_eq_one.mp (hC0 _ hmJ hm1 hm2))
  have h4 := Nat.card_le_card_of_injective f hf
  simpa using h4

private theorem core_mem_of_fused {u w : G} {m : ℕ} (hCu : Config u m) (hw : Fused u w)
    (hcent : centerAt w ≤ centralizer ({u} : Set G)) : w ∈ coreAt u := by
  obtain ⟨k, rfl⟩ := hw
  rw [centerAt_conj u k] at hcent
  exact (hCu.center_le_iff k).mp hcent

private theorem centerAt_le_centralizer_of_mem {u w : G}
    (hw : w ∈ centralizer (centerAt u : Set G)) : centerAt u ≤ centralizer ({w} : Set G) := by
  intro y hy
  exact Subgroup.mem_centralizer_singleton_iff.mpr (Subgroup.mem_centralizer_iff.mp hw y hy)

private theorem commute_of_mem_R1 (hC : Config z n) {g : G}
    (hH : g⁻¹ * z * g ∈ centralizer ({z} : Set G))
    (hK : g⁻¹ * z * g ∉ centralizer (centerAt z : Set G)) {x y : G}
    (hx : x ∈ coreAt z ⊓ centralizer ({g⁻¹ * z * g} : Set G))
    (hy : y ∈ coreAt z ⊓ centralizer ({g⁻¹ * z * g} : Set G)) : Commute x y := by
  have hE := CaseB.isElemAbelian hC hH hK
  have hxy : x * y ∈ coreAt z ⊓ centralizer ({g⁻¹ * z * g} : Set G) := mul_mem hx hy
  have hx2 : x ^ 2 = 1 := hE.2 x hx
  have hy2 : y ^ 2 = 1 := hE.2 y hy
  have hxy2 : (x * y) ^ 2 = 1 := hE.2 _ hxy
  have hxinv : x⁻¹ = x := inv_eq_of_mul_eq_one_right (by rw [← sq]; exact hx2)
  have hyinv : y⁻¹ = y := inv_eq_of_mul_eq_one_right (by rw [← sq]; exact hy2)
  have h1 : x * y = (x * y)⁻¹ := eq_inv_of_mul_eq_one_left (by rw [← sq]; exact hxy2)
  rw [mul_inv_rev, hxinv, hyinv] at h1
  exact h1

private theorem commute_of_mem_sup (hC : Config z n) {g : G}
    (hH : g⁻¹ * z * g ∈ centralizer ({z} : Set G))
    (hK : g⁻¹ * z * g ∉ centralizer (centerAt z : Set G)) {j : G}
    (hj : j ∈ coreAt z ⊓ centralizer ({g⁻¹ * z * g} : Set G)) {x : G}
    (hx : x ∈ (coreAt z ⊓ centralizer ({g⁻¹ * z * g} : Set G)) ⊔ centerAt z) : Commute j x := by
  have hjQ : j ∈ coreAt z := (Subgroup.mem_inf.mp hj).1
  have hle : (coreAt z ⊓ centralizer ({g⁻¹ * z * g} : Set G)) ⊔ centerAt z ≤
      centralizer ({j} : Set G) := by
    refine sup_le ?_ ?_
    · intro y hy
      exact Subgroup.mem_centralizer_singleton_iff.mpr (commute_of_mem_R1 hC hH hK hy hj)
    · intro y hy
      exact Subgroup.mem_centralizer_singleton_iff.mpr
        (Subgroup.mem_centralizer_iff.mp (hC.core_le_centralizer_center hjQ) y hy)
  exact (Subgroup.mem_centralizer_singleton_iff.mp (hle hx)).symm

private theorem false_of_mem_K (hC : Config z n) {g δ j : G}
    (hH : g⁻¹ * z * g ∈ centralizer ({z} : Set G))
    (hK : g⁻¹ * z * g ∉ centralizer (centerAt z : Set G))
    (hcomm : ⁅g⁻¹ * z * g, g⁻¹ * z * g * δ⁆ = z)
    (hfz : Fused z (g⁻¹ * z * g * δ)) (hfj : Fused z j)
    (hK1 : j ∈ centralizer (centerAt (g⁻¹ * z * g) : Set G))
    (hK2 : j ∈ centralizer (centerAt (g⁻¹ * z * g * δ) : Set G)) : False := by
  have hfjz : Fused j z := hfj.symm
  have hf1 : Fused j (g⁻¹ * z * g) := hfjz.trans (fused_conj z g)
  have hf2 : Fused j (g⁻¹ * z * g * δ) := hfjz.trans hfz
  obtain ⟨h, hh⟩ := hfj
  have hCj : Config j n := by
    rw [← hh]
    exact hC.conj h
  have hz1Q : g⁻¹ * z * g ∈ coreAt j :=
    core_mem_of_fused hCj hf1 (centerAt_le_centralizer_of_mem hK1)
  have hz2Q : g⁻¹ * z * g * δ ∈ coreAt j :=
    core_mem_of_fused hCj hf2 (centerAt_le_centralizer_of_mem hK2)
  have hcj := hCj.comm_eq _ hz1Q _ hz2Q
  rw [hcomm] at hcj
  have hz_ne : z ≠ 1 := by
    intro h1
    have h2 := hC.orderOf_eq
    rw [h1, orderOf_one] at h2
    exact absurd h2 (by norm_num)
  rcases hcj with hz_one | hzj
  · exact hz_ne hz_one
  · rw [← hzj] at hK1
    exact CaseB.not_mem_centralizer_center hC hH hK hK1

theorem CaseB.false_of_exists_not_mem (hC : Config z n) {g : G}
    (hH : g⁻¹ * z * g ∈ centralizer ({z} : Set G))
    (hK : g⁻¹ * z * g ∉ centralizer (centerAt z : Set G))
    (hq : ∃ q ∈ coreAt z,
      psi (g⁻¹ * z * g) q ∉ coreAt z ⊓ centralizer ({g⁻¹ * z * g} : Set G))
    (hJ : ∃ J : Subgroup G, J ≤ coreAt z ⊓ centralizer ({g⁻¹ * z * g} : Set G) ∧
      Nat.card J = 2 ^ n ∧ ∀ j ∈ J, ∃ q ∈ coreAt z, psi (g⁻¹ * z * g) q = j) : False := by
  obtain ⟨q₀, hq₀, hδR⟩ := hq
  obtain ⟨J, hJle, hJcard, hJψ⟩ := hJ
  have hz1sq : (g⁻¹ * z * g) ^ 2 = 1 := by
    have h := pow_orderOf_eq_one (g⁻¹ * z * g)
    rwa [(hC.conj g).orderOf_eq] at h
  have hz1 : g⁻¹ * z * g * (g⁻¹ * z * g) = 1 := by rw [← sq]; exact hz1sq
  have hδZ := CaseB.psi_mem hC hH hK hq₀
  have hδsq := CaseB.sq_eq_of_not_mem hC hH hK hδZ hδR
  have hz2 := mul_self_eq_one_of_inv hz1 (psi_conj (z₁ := g⁻¹ * z * g) (q := q₀) hz1)
  have hcomm : ⁅g⁻¹ * z * g, g⁻¹ * z * g * psi (g⁻¹ * z * g) q₀⁆ = z := by
    rw [comm_eq_sq_mul_of_involutions hz1 hz2, sq_of_mul_eq hz1, hδsq]
  have hfz : Fused z (g⁻¹ * z * g * psi (g⁻¹ * z * g) q₀) := fused_mul_psi g q₀ hz1
  have hJC : ∀ j ∈ J, j ∈ centralizer ({g⁻¹ * z * g} : Set G) :=
    fun j hj => (Subgroup.mem_inf.mp (hJle hj)).2
  have hJK2 : ∀ j ∈ J, j ∈ centralizer ({g⁻¹ * z * g * psi (g⁻¹ * z * g) q₀} : Set G) := by
    intro j hj
    have hδc : Commute j (psi (g⁻¹ * z * g) q₀) :=
      commute_of_mem_sup hC hH hK (hJle hj) hδZ
    exact Subgroup.mem_centralizer_singleton_iff.mpr
      ((show Commute j (g⁻¹ * z * g) from
        Subgroup.mem_centralizer_singleton_iff.mp (hJC j hj)).mul_right hδc)
  have hC2 : Config (g⁻¹ * z * g * psi (g⁻¹ * z * g) q₀) n := by
    obtain ⟨k₂, hk₂⟩ := hfz
    rw [← hk₂]
    exact hC.conj k₂
  have hC0 : ∀ x ∈ J, x ∈ centralizer (centerAt (g⁻¹ * z * g) : Set G) →
      x ∈ centralizer (centerAt (g⁻¹ * z * g * psi (g⁻¹ * z * g) q₀) : Set G) → x = 1 := by
    intro x hx hK1 hK2
    by_contra hx1
    have hfzx : Fused z (g⁻¹ * z * g * x) := by
      obtain ⟨q, -, hqx⟩ := hJψ x hx
      rw [← hqx]
      exact fused_mul_psi g q hz1
    exact false_of_mem_K hC hH hK hcomm hfz
      (CaseB.fused_of_fused_mul hC hH hK (hJle hx) hx1 hfzx) hK1 hK2
  have hA : ∀ x ∈ J, ∀ y ∈ J, x ∉ centralizer (centerAt (g⁻¹ * z * g) : Set G) →
      y ∉ centralizer (centerAt (g⁻¹ * z * g) : Set G) →
      x * y ∈ centralizer (centerAt (g⁻¹ * z * g) : Set G) :=
    fun x hx y hy hxK hyK => (hC.conj g).mul_mem_centralizer (hJC x hx) (hJC y hy) hxK hyK
  have hB : ∀ x ∈ J, ∀ y ∈ J,
      x ∉ centralizer (centerAt (g⁻¹ * z * g * psi (g⁻¹ * z * g) q₀) : Set G) →
      y ∉ centralizer (centerAt (g⁻¹ * z * g * psi (g⁻¹ * z * g) q₀) : Set G) →
      x * y ∈ centralizer (centerAt (g⁻¹ * z * g * psi (g⁻¹ * z * g) q₀) : Set G) :=
    fun x hx y hy hxK hyK => hC2.mul_mem_centralizer (hJK2 x hx) (hJK2 y hy) hxK hyK
  have hcard := card_le_four_of_inter J _ _ hA hB hC0
  rw [hJcard] at hcard
  have h8 : 8 ≤ 2 ^ n := by
    calc (8 : ℕ) = 2 ^ 3 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hC.three_le
  linarith

end CFSG.GF2Type.CenterFour
