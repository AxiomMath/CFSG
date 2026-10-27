module

public import CFSG.Sporadic.Schreier.MathieuOddCoreM12Outer
public import CFSG.Sporadic.SmallOddCore.GroupFacts

public section

namespace CFSG.EvenSporadicStandard.M12Std.PropA

open Equiv Subgroup CFSG.Sporadic.Schreier CFSG.Sporadic.SmallOddCore

noncomputable abbrev D24 : Subgroup (Perm (Fin 24)) := m12D.originalSubgroup

@[expose] noncomputable def AA : Subgroup (Perm (Fin 24)) := D24 ⊔ zpowers m12Sigma

theorem D24_le_AA : D24 ≤ AA := le_sup_left

theorem sigma_mem_AA : m12Sigma ∈ AA :=
  (le_sup_right : zpowers m12Sigma ≤ D24 ⊔ zpowers m12Sigma) (mem_zpowers _)

theorem card_D24 : Nat.card D24 = 95040 := by
  rw [← m12D.orderCertificate_eq_card m12D_check.1, m12D_check.2]

theorem sigma_mul_self : m12Sigma * m12Sigma = 1 :=
  (m12_sigma_check).1

theorem sigma_conj_mem :
    ∀ h ∈ D24, m12Sigma * h * m12Sigma⁻¹ ∈ D24 :=
  m12D_sigma_normalizes

theorem sigma_not_mem_D24 : m12Sigma ∉ D24 := by
  intro h
  exact m12D_sigma_outer m12Sigma⁻¹ (D24.inv_mem h) fun x _ => by simp

theorem card_AA : Nat.card AA = 190080 := by
  have h := card_sup_zpowers (P := D24) (u := m12Sigma) sigma_mul_self sigma_conj_mem
    sigma_not_mem_D24
  show Nat.card ↥(D24 ⊔ zpowers m12Sigma) = 190080
  rw [h, card_D24]

private theorem sigma_inv : m12Sigma⁻¹ = m12Sigma :=
  inv_eq_of_mul_eq_one_right sigma_mul_self

private instance normal_subgroupOf_AA :
    (D24.subgroupOf AA).Normal := by
  rw [Subgroup.normal_subgroupOf_iff_le_normalizer D24_le_AA]
  refine sup_le Subgroup.le_normalizer ?_
  rw [Subgroup.zpowers_le, Subgroup.mem_normalizer_iff]
  intro h
  constructor
  · intro hh
    exact sigma_conj_mem h hh
  · intro hh
    have h2 := sigma_conj_mem (m12Sigma * h * m12Sigma⁻¹) hh
    have heq : m12Sigma * (m12Sigma * h * m12Sigma⁻¹) * m12Sigma⁻¹ = h := by
      rw [sigma_inv]
      calc m12Sigma * (m12Sigma * h * m12Sigma) * m12Sigma
          = (m12Sigma * m12Sigma) * h * (m12Sigma * m12Sigma) := by group
        _ = h := by rw [sigma_mul_self]; group
    rwa [heq] at h2

private noncomputable def conjHom :
    ↥AA →* MulAut ↥D24 :=
  ((MulAut.congr (Subgroup.subgroupOfEquivOfLe D24_le_AA)).toMonoidHom).comp
    (MulAut.conjNormal (H := D24.subgroupOf AA))

private theorem conjHom_apply (a : ↥AA) (d : ↥D24) :
    (((conjHom a) d : ↥D24) : Perm (Fin 24)) =
      (a : Perm (Fin 24)) * d * (a : Perm (Fin 24))⁻¹ := by
  simp [conjHom, MulAut.congr, MulAut.conjNormal_apply]

private theorem conjHom_eq_one
    {a : ↥AA} (ha : conjHom a = 1) : a = 1 := by
  have hcent : ∀ d : ↥D24,
      (a : Perm (Fin 24)) * d * (a : Perm (Fin 24))⁻¹ = d := by
    intro d
    have hd : (conjHom a) d = d := by rw [ha]; rfl
    have := congrArg (fun x : ↥D24 => (x : Perm (Fin 24))) hd
    simpa [conjHom_apply] using this
  have hcomm : ∀ d : ↥D24,
      (a : Perm (Fin 24)) * d = d * (a : Perm (Fin 24)) := by
    intro d
    have := congrArg (fun x : Perm (Fin 24) => x * (a : Perm (Fin 24))) (hcent d)
    simpa [mul_assoc] using this
  have hcomm_inv : ∀ d : ↥D24,
      (a : Perm (Fin 24))⁻¹ * d = d * (a : Perm (Fin 24))⁻¹ := by
    intro d
    have h := congrArg (fun x : Perm (Fin 24) => x⁻¹) (hcomm d⁻¹)
    simp only [mul_inv_rev, inv_inv] at h
    exact h.symm
  rcases (mem_sup_zpowers_iff (P := D24) (u := m12Sigma) sigma_mul_self
    sigma_conj_mem).mp a.2 with haD | haD
  · let aD : ↥D24 := ⟨(a : Perm (Fin 24)), haD⟩
    have hcenter : aD ∈ Subgroup.center ↥D24 := by
      rw [Subgroup.mem_center_iff]
      intro d
      exact (Subtype.ext (hcomm d)).symm
    rw [m12D_center] at hcenter
    have ha1 : aD = 1 := by simpa using hcenter
    have : (a : Perm (Fin 24)) = 1 := congrArg Subtype.val ha1
    exact Subtype.ext (by simpa using this)
  · have hainv : (a : Perm (Fin 24))⁻¹ =
        m12Sigma * ((a : Perm (Fin 24)) * m12Sigma)⁻¹ := by
      rw [mul_inv_rev, sigma_inv, ← mul_assoc, sigma_mul_self, one_mul]
    have hcomm_inv2 : ∀ d : ↥D24,
        (m12Sigma * ((a : Perm (Fin 24)) * m12Sigma)⁻¹) * d =
          d * (m12Sigma * ((a : Perm (Fin 24)) * m12Sigma)⁻¹) := by
      intro d
      have hc := hcomm_inv d
      rwa [hainv] at hc
    have houter := m12D_sigma_outer ((a : Perm (Fin 24)) * m12Sigma)⁻¹
      (D24.inv_mem haD)
    exact (houter fun h hh => hcomm_inv2 ⟨h, hh⟩).elim

private theorem conjHom_injective :
    Function.Injective conjHom := by
  intro a b hab
  have h1 : conjHom (a * b⁻¹) = 1 := by
    rw [map_mul, map_inv, hab, mul_inv_cancel]
  exact mul_inv_eq_one.mp (conjHom_eq_one h1)

theorem exists_aut_equiv :
    ∃ ψ : ↥AA ≃* MulAut ↥D24, ∀ (a : ↥AA) (d : ↥D24),
      (((ψ a) d : ↥D24) : Perm (Fin 24)) = (a : Perm (Fin 24)) * d * (a : Perm (Fin 24))⁻¹ := by
  have hcard : Nat.card (MulAut ↥D24) ≤ Nat.card ↥AA := by
    rw [card_AA]
    calc Nat.card (MulAut ↥D24) ≤ 2 * Nat.card ↥D24 := m12D_mulAut_card
      _ = 190080 := by rw [card_D24]
  let ψ : ↥AA ≃* MulAut ↥D24 :=
    MulEquiv.ofBijective conjHom (conjHom_injective.bijective_of_nat_card_le hcard)
  exact ⟨ψ, fun a d => conjHom_apply a d⟩

end CFSG.EvenSporadicStandard.M12Std.PropA
