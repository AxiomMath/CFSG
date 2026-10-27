module

public import CFSG.LocalAnalysis.EvenSporadicStandard.M12Std.PropA.Model28Facts
public import CFSG.LocalAnalysis.EvenSporadicStandard.M12Std.PropA.AutModel
public import CFSG.Certificates.Kernel.PermCent.OrbGroup
import CFSG.GH74.GLS.Stage1.Thm6.Sec13.S3Gen

public section

namespace CFSG.EvenSporadicStandard.M12Std.PropA

open Equiv Subgroup CFSG.Sporadic.Schreier

variable {M : Type*} [Group M]

theorem mem_sup_zpowers_iff_sq {P : Subgroup M} {u : M} (hu : u * u ∈ P)
    (hn : ∀ p ∈ P, u * p * u⁻¹ ∈ P) {x : M} : x ∈ P ⊔ zpowers u ↔ x ∈ P ∨ x * u ∈ P := by
  have hn' : ∀ p ∈ P, u⁻¹ * p * u ∈ P := by
    intro p hp
    have e : u⁻¹ * p * u = (u * u)⁻¹ * (u * p * u⁻¹) * (u * u) := by group
    rw [e]
    exact P.mul_mem (P.mul_mem (P.inv_mem hu) (hn p hp)) hu
  let K : Subgroup M :=
    { carrier := {x | x ∈ P ∨ x * u ∈ P}
      one_mem' := Or.inl P.one_mem
      mul_mem' := by
        rintro x y (hx | hx) (hy | hy)
        · exact Or.inl (P.mul_mem hx hy)
        · right
          rw [mul_assoc]
          exact P.mul_mem hx hy
        · right
          have e : x * y * u = (x * u) * (u⁻¹ * y * u) := by group
          rw [e]
          exact P.mul_mem hx (hn' y hy)
        · left
          have e : x * y = (x * u) * (u⁻¹ * (y * u) * u) * (u * u)⁻¹ := by group
          rw [e]
          exact P.mul_mem (P.mul_mem hx (hn' _ hy)) (P.inv_mem hu)
      inv_mem' := by
        rintro x (hx | hx)
        · exact Or.inl (P.inv_mem hx)
        · right
          have e : x⁻¹ * u = u * (x * u)⁻¹ * u⁻¹ * (u * u) := by group
          rw [e]
          exact P.mul_mem (hn _ (P.inv_mem hx)) hu }
  have hK : P ⊔ zpowers u = K := by
    apply le_antisymm
    · refine sup_le (fun x hx => Or.inl hx) ?_
      rw [zpowers_le]
      exact Or.inr hu
    · rintro x (hx | hx)
      · exact mem_sup_left hx
      · have e : x = (x * u) * u⁻¹ := by group
        rw [e]
        exact mul_mem (mem_sup_left hx) (inv_mem (mem_sup_right (mem_zpowers u)))
  rw [hK]
  rfl

open CFSG.GH74.GLS.Stage1.Thm6.Sec13 (card_sup_zpowers_sq)

@[expose] noncomputable def iota28 : Perm (Fin 24) →* Perm (Fin 28) :=
  block28.comp (MonoidHom.inl _ _)

theorem iota28_injective : Function.Injective iota28 :=
  block28_injective.comp fun _ _ e => (Prod.ext_iff.1 e).1

theorem D28_eq_map : D28 = D24.map iota28 := by
  have e : D24 = closure {m12A1, m12B1} := by
    change m12D.originalSubgroup = _
    rw [m12D_eq_closure]
    congr 1
    ext g
    simp
  rw [e, MonoidHom.map_closure, Set.image_pair]
  rfl

theorem card_D28 : Nat.card D28 = 95040 := by
  rw [D28_eq_map, Subgroup.card_map_of_injective iota28_injective, card_D24]

theorem mem_D28_iff {y : Perm (Fin 28)} : y ∈ D28 ↔ ∃ p ∈ D24, iota28 p = y := by
  rw [D28_eq_map]
  rfl

theorem pT_comm_D28 : ∀ d ∈ D28, pT * d * pT⁻¹ = d := by
  intro d hd
  obtain ⟨p, -, rfl⟩ := mem_D28_iff.1 hd
  rw [mul_inv_eq_iff_eq_mul]
  simp only [pT, iota28, MonoidHom.comp_apply, MonoidHom.inl_apply, ← map_mul, Prod.mk_mul_mk,
    mul_one, one_mul]

theorem pT_mul_self : pT * pT = 1 := by
  have e : tFour * tFour = 1 := by decide
  simp only [pT, ← map_mul, Prod.mk_mul_mk, mul_one, e]
  exact map_one block28

theorem pT_not_mem_D28 : pT ∉ D28 := by
  intro h
  obtain ⟨p, -, e⟩ := mem_D28_iff.1 h
  have e2 := (Prod.ext_iff.1 (block28_injective e)).2
  have hne : (1 : Perm (Fin 4)) ≠ tFour := by decide
  exact hne e2

@[expose] noncomputable def E28 : Subgroup (Perm (Fin 28)) := D28 ⊔ zpowers pT

theorem pT_conj_D28 : ∀ d ∈ D28, pT * d * pT⁻¹ ∈ D28 := fun d hd => by
  rw [pT_comm_D28 d hd]
  exact hd

theorem mem_E28_iff {y : Perm (Fin 28)} : y ∈ E28 ↔ y ∈ D28 ∨ y * pT ∈ D28 := by
  unfold E28
  rw [mem_sup_zpowers_iff_sq (by rw [pT_mul_self]; exact one_mem _) pT_conj_D28]

theorem card_E28 : Nat.card E28 = 190080 := by
  unfold E28
  rw [card_sup_zpowers_sq (by rw [pT_mul_self]; exact one_mem _) pT_conj_D28 pT_not_mem_D28,
    card_D28]

theorem pG_conj_D28 (b : Bool) :
    ∀ d ∈ D28, pG b * d * (pG b)⁻¹ ∈ D28 := by
  intro d hd
  obtain ⟨p, hp, rfl⟩ := mem_D28_iff.1 hd
  refine mem_D28_iff.2 ⟨m12Sigma * p * m12Sigma⁻¹, sigma_conj_mem p hp, ?_⟩
  simp only [pG, iota28, MonoidHom.comp_apply, MonoidHom.inl_apply, ← map_mul, ← map_inv,
    Prod.mk_mul_mk, Prod.inv_mk, mul_one, mul_inv_cancel]

theorem pG_comm_pT (b : Bool) : pG b * pT = pT * pG b := by
  have ht : (if b then hTwo else hOne) * tFour = tFour * (if b then hTwo else hOne) := by
    cases b <;> decide
  simp only [pG, pT, ← map_mul, Prod.mk_mul_mk, mul_one, one_mul, ht]

theorem pG_mul_self (b : Bool) :
    pG b * pG b = if b then pT else 1 := by
  have hs : m12Sigma * m12Sigma = 1 := sigma_mul_self
  cases b
  · have e : hOne * hOne = 1 := by decide
    simp only [pG, ← map_mul, Prod.mk_mul_mk, hs, Bool.false_eq_true, ↓reduceIte, e]
    exact map_one block28
  · have e : hTwo * hTwo = tFour := by decide
    simp only [pG, pT, ← map_mul, Prod.mk_mul_mk, hs, ↓reduceIte, e]

theorem pG_sq_mem_E28 (b : Bool) : pG b * pG b ∈ E28 := by
  rw [pG_mul_self]
  cases b
  · exact one_mem _
  · exact mem_sup_right (mem_zpowers pT)

theorem pG_conj_E28 (b : Bool) :
    ∀ e ∈ E28, pG b * e * (pG b)⁻¹ ∈ E28 := by
  intro e he
  rw [mem_E28_iff] at he ⊢
  rcases he with he | he
  · exact Or.inl (pG_conj_D28 b e he)
  · right
    have hc : (pG b)⁻¹ * pT = pT * (pG b)⁻¹ := by
      rw [inv_mul_eq_iff_eq_mul, ← mul_assoc, pG_comm_pT, mul_assoc, mul_inv_cancel, mul_one]
    have h1 : pG b * e * (pG b)⁻¹ * pT = pG b * (e * pT) * (pG b)⁻¹ := by
      rw [mul_assoc (pG b * e), hc]
      group
    rw [h1]
    exact pG_conj_D28 b _ he

theorem pG_not_mem_E28 (b : Bool) : pG b ∉ E28 := by
  intro h
  have hσ := sigma_not_mem_D24
  rcases mem_E28_iff.1 h with h | h
  · obtain ⟨p, hp, e⟩ := mem_D28_iff.1 h
    have e2 : p = m12Sigma := by simpa using (Prod.ext_iff.1 (block28_injective e)).1
    apply hσ
    rw [← e2]
    exact hp
  · obtain ⟨p, hp, e⟩ := mem_D28_iff.1 h
    have e' : block28 (p, 1) = block28 (m12Sigma * 1, (if b then hTwo else hOne) * tFour) := by
      rw [← Prod.mk_mul_mk, map_mul]
      exact e
    have e2 : p = m12Sigma := by simpa using (Prod.ext_iff.1 (block28_injective e')).1
    apply hσ
    rw [← e2]
    exact hp

theorem K28_eq (b : Bool) : K28 b = E28 ⊔ zpowers (pG b) := by
  apply le_antisymm
  · unfold K28
    rw [closure_le]
    have hD : D28 ≤ E28 ⊔ zpowers (pG b) := le_trans le_sup_left le_sup_left
    rintro y (rfl | rfl | rfl | rfl)
    · exact hD (subset_closure (by simp))
    · exact hD (subset_closure (by simp))
    · exact mem_sup_right (mem_zpowers _)
    · exact mem_sup_left (mem_sup_right (mem_zpowers _))
  · refine sup_le (sup_le (D28_le_K28 b) ?_) ?_
    · rw [zpowers_le]
      exact subset_closure (by simp)
    · rw [zpowers_le]
      exact subset_closure (by simp)

theorem card_K28 (b : Bool) : Nat.card (K28 b) = 380160 := by
  rw [K28_eq, card_sup_zpowers_sq (pG_sq_mem_E28 b) (pG_conj_E28 b) (pG_not_mem_E28 b),
    card_E28]

theorem D28_conj (b : Bool) :
    ∀ k ∈ K28 b, ∀ d ∈ D28, k * d * k⁻¹ ∈ D28 := by
  have hgen : ∀ k ∈ ({pA, pB, pG b, pT} : Set (Perm (Fin 28))), ∀ d ∈ D28, k * d * k⁻¹ ∈ D28 := by
    rintro k (rfl | rfl | rfl | rfl) d hd
    · exact D28.mul_mem (D28.mul_mem (subset_closure (by simp)) hd)
        (D28.inv_mem (subset_closure (by simp)))
    · exact D28.mul_mem (D28.mul_mem (subset_closure (by simp)) hd)
        (D28.inv_mem (subset_closure (by simp)))
    · exact pG_conj_D28 b d hd
    · exact pT_conj_D28 d hd
  intro k hk
  unfold K28 at hk
  induction hk using Subgroup.closure_induction with
  | mem x hx => exact hgen x hx
  | one =>
    intro d hd
    simpa using hd
  | mul x y _ _ hx hy =>
    intro d hd
    have e : x * y * d * (x * y)⁻¹ = x * (y * d * y⁻¹) * x⁻¹ := by group
    rw [e]
    exact hx _ (hy d hd)
  | inv x _ hx =>
    intro d hd
    obtain ⟨z, hz, e⟩ := CFSG.KC.OrbGroup.surj_of_mapsTo (T := (D28 : Set (Perm (Fin 28))))
      (fun z => x * z * x⁻¹) (fun u v e => by simpa using e) (fun z hz => hx z hz) d hd
    have e2 : x⁻¹ * d * x⁻¹⁻¹ = z := by
      rw [← e]
      group
    rw [e2]
    exact hz

end CFSG.EvenSporadicStandard.M12Std.PropA

end
