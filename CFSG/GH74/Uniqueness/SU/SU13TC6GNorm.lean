module

public import CFSG.GroupTheory.ABGLocalTools.OddInvolution

public section

open Subgroup
open scoped commutatorElement Pointwise

namespace CFSG.GH74.Uniqueness.SU.SU13

namespace TC6N

variable {G : Type*} [Group G]

section ClassTwo

theorem comm_mul_left {Y : Subgroup G}
    (hcl : ∀ a ∈ Y, ∀ b ∈ Y, ∀ c ∈ Y, ⁅a, b⁆ * c = c * ⁅a, b⁆)
    {a a' b : G} (ha : a ∈ Y) (ha' : a' ∈ Y) (hb : b ∈ Y) :
    ⁅a * a', b⁆ = ⁅a', b⁆ * ⁅a, b⁆ := by
  have h := hcl a' ha' b hb a ha
  have e : ⁅a * a', b⁆ = (a * ⁅a', b⁆ * a⁻¹) * ⁅a, b⁆ := by
    simp only [commutatorElement_def]; group
  rw [e, ← h]; group

theorem comm_mul_right {Y : Subgroup G}
    (hcl : ∀ a ∈ Y, ∀ b ∈ Y, ∀ c ∈ Y, ⁅a, b⁆ * c = c * ⁅a, b⁆)
    {a b b' : G} (ha : a ∈ Y) (hb : b ∈ Y) (hb' : b' ∈ Y) :
    ⁅a, b * b'⁆ = ⁅a, b⁆ * ⁅a, b'⁆ := by
  have h := hcl a ha b' hb' b hb
  have e : ⁅a, b * b'⁆ = ⁅a, b⁆ * (b * ⁅a, b'⁆ * b⁻¹) := by
    simp only [commutatorElement_def]; group
  rw [e, ← h]; group

theorem comm_inv_left {Y : Subgroup G}
    (hcl : ∀ a ∈ Y, ∀ b ∈ Y, ∀ c ∈ Y, ⁅a, b⁆ * c = c * ⁅a, b⁆)
    {a b : G} (ha : a ∈ Y) (hb : b ∈ Y) : ⁅a⁻¹, b⁆ = ⁅a, b⁆⁻¹ := by
  have h := comm_mul_left hcl ha (Y.inv_mem ha) hb
  rw [mul_inv_cancel, commutatorElement_one_left] at h
  exact eq_inv_of_mul_eq_one_left h.symm

theorem comm_inv_right {Y : Subgroup G}
    (hcl : ∀ a ∈ Y, ∀ b ∈ Y, ∀ c ∈ Y, ⁅a, b⁆ * c = c * ⁅a, b⁆)
    {a b : G} (ha : a ∈ Y) (hb : b ∈ Y) : ⁅a, b⁻¹⁆ = ⁅a, b⁆⁻¹ := by
  have h := comm_mul_right hcl ha hb (Y.inv_mem hb)
  rw [mul_inv_cancel, commutatorElement_one_right] at h
  exact eq_inv_of_mul_eq_one_right h.symm

theorem comm_inv_inv {Y : Subgroup G}
    (hcl : ∀ a ∈ Y, ∀ b ∈ Y, ∀ c ∈ Y, ⁅a, b⁆ * c = c * ⁅a, b⁆)
    {a b : G} (ha : a ∈ Y) (hb : b ∈ Y) : ⁅a⁻¹, b⁻¹⁆ = ⁅a, b⁆ := by
  rw [comm_inv_left hcl ha (Y.inv_mem hb), comm_inv_right hcl ha hb, inv_inv]

theorem conj_comm (r a b : G) : r * ⁅a, b⁆ * r⁻¹ = ⁅r * a * r⁻¹, r * b * r⁻¹⁆ := by
  simp only [commutatorElement_def]; group

theorem conj_comm_pm {Y : Subgroup G}
    (hcl : ∀ a ∈ Y, ∀ b ∈ Y, ∀ c ∈ Y, ⁅a, b⁆ * c = c * ⁅a, b⁆)
    {r a b : G} (haY : a ∈ Y) (hbY : b ∈ Y) (ha : r * a * r⁻¹ = a) (hb : r * b * r⁻¹ = b⁻¹) :
    r * ⁅a, b⁆ * r⁻¹ = ⁅a, b⁆⁻¹ := by
  rw [conj_comm, ha, hb, comm_inv_right hcl haY hbY]

theorem conj_comm_mp {Y : Subgroup G}
    (hcl : ∀ a ∈ Y, ∀ b ∈ Y, ∀ c ∈ Y, ⁅a, b⁆ * c = c * ⁅a, b⁆)
    {r a b : G} (haY : a ∈ Y) (hbY : b ∈ Y) (ha : r * a * r⁻¹ = a⁻¹) (hb : r * b * r⁻¹ = b) :
    r * ⁅a, b⁆ * r⁻¹ = ⁅a, b⁆⁻¹ := by
  rw [conj_comm, ha, hb, comm_inv_left hcl haY hbY]

theorem conj_comm_mm {Y : Subgroup G}
    (hcl : ∀ a ∈ Y, ∀ b ∈ Y, ∀ c ∈ Y, ⁅a, b⁆ * c = c * ⁅a, b⁆)
    {r a b : G} (haY : a ∈ Y) (hbY : b ∈ Y) (ha : r * a * r⁻¹ = a⁻¹) (hb : r * b * r⁻¹ = b⁻¹) :
    r * ⁅a, b⁆ * r⁻¹ = ⁅a, b⁆ := by
  rw [conj_comm, ha, hb, comm_inv_inv hcl haY hbY]

theorem commutator_comm {Y : Subgroup G}
    (hcl : ∀ a ∈ Y, ∀ b ∈ Y, ∀ c ∈ Y, ⁅a, b⁆ * c = c * ⁅a, b⁆) :
    ∀ u ∈ ⁅Y, Y⁆, ∀ v ∈ ⁅Y, Y⁆, u * v = v * u := by
  have hle : ⁅Y, Y⁆ ≤ centralizer (Y : Set G) := by
    rw [Subgroup.commutator_le]
    intro a ha b hb
    rw [Subgroup.mem_centralizer_iff]
    intro c hc
    exact (hcl a ha b hb c hc).symm
  intro u hu v hv
  exact ((Subgroup.mem_centralizer_iff.mp (hle hu)) v (Subgroup.commutator_le_self Y hv)).symm

theorem conj_mem_commutator {Y : Subgroup G} {r : G}
    (hr : ∀ a ∈ Y, r * a * r⁻¹ ∈ Y) {x : G} (hx : x ∈ ⁅Y, Y⁆) : r * x * r⁻¹ ∈ ⁅Y, Y⁆ := by
  have hle : ⁅Y, Y⁆ ≤ (⁅Y, Y⁆).comap (MulAut.conj r).toMonoidHom := by
    rw [Subgroup.commutator_le]
    intro a ha b hb
    rw [Subgroup.mem_comap]
    have e : (MulAut.conj r).toMonoidHom ⁅a, b⁆ = ⁅r * a * r⁻¹, r * b * r⁻¹⁆ := by simp
    rw [e]
    exact Subgroup.commutator_mem_commutator (hr a ha) (hr b hb)
  have := hle hx
  rw [Subgroup.mem_comap] at this
  simpa using this

end ClassTwo

section Norm

def nu (t z x : G) : G := x * (t * x * t⁻¹) * (z * x * z⁻¹) * ((t * z) * x * (t * z)⁻¹)

theorem nu_one (t z : G) : nu t z 1 = 1 := by simp [nu]

theorem rearr {A : Subgroup G} (hA : ∀ u ∈ A, ∀ v ∈ A, u * v = v * u)
    {c c' β β' γ γ' δ δ' : G} (hc : c ∈ A) (hc' : c' ∈ A) (hβ : β ∈ A) (hβ' : β' ∈ A)
    (hγ : γ ∈ A) (hγ' : γ' ∈ A) (hδ : δ ∈ A) (hδ' : δ' ∈ A) :
    (c * c') * (β * β') * (γ * γ') * (δ * δ') = (c * β * γ * δ) * (c' * β' * γ' * δ') := by
  let _ : CommGroup A :=
    { (inferInstance : Group A) with mul_comm := fun u v => Subtype.ext (hA u u.2 v v.2) }
  have key : ((⟨c, hc⟩ : A) * ⟨c', hc'⟩) * (⟨β, hβ⟩ * ⟨β', hβ'⟩) * (⟨γ, hγ⟩ * ⟨γ', hγ'⟩) *
      (⟨δ, hδ⟩ * ⟨δ', hδ'⟩) = ((⟨c, hc⟩ : A) * ⟨β, hβ⟩ * ⟨γ, hγ⟩ * ⟨δ, hδ⟩) *
        (⟨c', hc'⟩ * ⟨β', hβ'⟩ * ⟨γ', hγ'⟩ * ⟨δ', hδ'⟩) := by
    ac_rfl
  exact congrArg Subtype.val key

theorem nu_mul {A : Subgroup G} (hA : ∀ u ∈ A, ∀ v ∈ A, u * v = v * u) {t z : G}
    (ht : ∀ a ∈ A, t * a * t⁻¹ ∈ A) (hz : ∀ a ∈ A, z * a * z⁻¹ ∈ A) {c c' : G}
    (hc : c ∈ A) (hc' : c' ∈ A) : nu t z (c * c') = nu t z c * nu t z c' := by
  have htz : ∀ a ∈ A, (t * z) * a * (t * z)⁻¹ ∈ A := fun a ha => by
    have e : (t * z) * a * (t * z)⁻¹ = t * (z * a * z⁻¹) * t⁻¹ := by group
    rw [e]; exact ht _ (hz a ha)
  have e1 : t * (c * c') * t⁻¹ = (t * c * t⁻¹) * (t * c' * t⁻¹) := by group
  have e2 : z * (c * c') * z⁻¹ = (z * c * z⁻¹) * (z * c' * z⁻¹) := by group
  have e3 : (t * z) * (c * c') * (t * z)⁻¹ =
      ((t * z) * c * (t * z)⁻¹) * ((t * z) * c' * (t * z)⁻¹) := by group
  unfold nu
  rw [e1, e2, e3]
  exact rearr hA hc hc' (ht c hc) (ht c' hc') (hz c hc) (hz c' hc') (htz c hc) (htz c' hc')

theorem nu_inv {A : Subgroup G} (hA : ∀ u ∈ A, ∀ v ∈ A, u * v = v * u) {t z : G}
    (ht : ∀ a ∈ A, t * a * t⁻¹ ∈ A) (hz : ∀ a ∈ A, z * a * z⁻¹ ∈ A) {c : G}
    (hc : c ∈ A) : nu t z c⁻¹ = (nu t z c)⁻¹ := by
  have h := nu_mul hA ht hz hc (A.inv_mem hc)
  rw [mul_inv_cancel, nu_one] at h
  exact eq_inv_of_mul_eq_one_right h.symm

theorem nu_mul_commutator {Y : Subgroup G}
    (hcl : ∀ a ∈ Y, ∀ b ∈ Y, ∀ c ∈ Y, ⁅a, b⁆ * c = c * ⁅a, b⁆) {t z : G}
    (hYt : ∀ a ∈ Y, t * a * t⁻¹ ∈ Y) (hYz : ∀ a ∈ Y, z * a * z⁻¹ ∈ Y) {c c' : G}
    (hc : c ∈ ⁅Y, Y⁆) (hc' : c' ∈ ⁅Y, Y⁆) : nu t z (c * c') = nu t z c * nu t z c' :=
  nu_mul (commutator_comm hcl) (fun _ ha => conj_mem_commutator hYt ha)
    (fun _ ha => conj_mem_commutator hYz ha) hc hc'

theorem nu_inv_commutator {Y : Subgroup G}
    (hcl : ∀ a ∈ Y, ∀ b ∈ Y, ∀ c ∈ Y, ⁅a, b⁆ * c = c * ⁅a, b⁆) {t z : G}
    (hYt : ∀ a ∈ Y, t * a * t⁻¹ ∈ Y) (hYz : ∀ a ∈ Y, z * a * z⁻¹ ∈ Y) {c : G}
    (hc : c ∈ ⁅Y, Y⁆) : nu t z c⁻¹ = (nu t z c)⁻¹ :=
  nu_inv (commutator_comm hcl) (fun _ ha => conj_mem_commutator hYt ha)
    (fun _ ha => conj_mem_commutator hYz ha) hc

theorem nu_comm_swap {Y : Subgroup G}
    (hcl : ∀ a ∈ Y, ∀ b ∈ Y, ∀ c ∈ Y, ⁅a, b⁆ * c = c * ⁅a, b⁆) {t z : G}
    (hYt : ∀ a ∈ Y, t * a * t⁻¹ ∈ Y) (hYz : ∀ a ∈ Y, z * a * z⁻¹ ∈ Y) {a b : G}
    (ha : a ∈ Y) (hb : b ∈ Y) (h : nu t z ⁅b, a⁆ = 1) : nu t z ⁅a, b⁆ = 1 := by
  rw [← commutatorElement_inv b a, nu_inv_commutator hcl hYt hYz
    (Subgroup.commutator_mem_commutator hb ha), h, inv_one]

end Norm

section Eigen

theorem mul_comm_of_conj_eq {r a : G} (h : r * a * r⁻¹ = a) : a * r = r * a := by
  have : r * a = a * r := by
    calc r * a = r * a * r⁻¹ * r := by group
      _ = a * r := by rw [h]
  exact this.symm

def Eig₁ (t z a : G) : Prop :=
  t * a * t⁻¹ = a ∧ z * a * z⁻¹ = a⁻¹ ∧ (t * z) * a * (t * z)⁻¹ = a⁻¹

def Eig₂ (t z a : G) : Prop :=
  t * a * t⁻¹ = a⁻¹ ∧ z * a * z⁻¹ = a ∧ (t * z) * a * (t * z)⁻¹ = a⁻¹

def Eig₃ (t z a : G) : Prop :=
  t * a * t⁻¹ = a⁻¹ ∧ z * a * z⁻¹ = a⁻¹ ∧ (t * z) * a * (t * z)⁻¹ = a

theorem eig₁_of {t z a : G} (ha_t : t * a * t⁻¹ = a) (ha_z : z * a * z⁻¹ = a⁻¹) :
    Eig₁ t z a := by
  refine ⟨ha_t, ha_z, ?_⟩
  calc (t * z) * a * (t * z)⁻¹ = t * (z * a * z⁻¹) * t⁻¹ := by group
    _ = t * a⁻¹ * t⁻¹ := by rw [ha_z]
    _ = (t * a * t⁻¹)⁻¹ := by group
    _ = a⁻¹ := by rw [ha_t]

theorem eig₂_of {t z a : G} (ha_z : z * a * z⁻¹ = a) (ha_t : t * a * t⁻¹ = a⁻¹) :
    Eig₂ t z a := by
  refine ⟨ha_t, ha_z, ?_⟩
  calc (t * z) * a * (t * z)⁻¹ = t * (z * a * z⁻¹) * t⁻¹ := by group
    _ = t * a * t⁻¹ := by rw [ha_z]
    _ = a⁻¹ := ha_t

theorem eig₃_of {t z a : G} (htt : t * t = 1) (ha_tz : (t * z) * a * (t * z)⁻¹ = a)
    (ha_t : t * a * t⁻¹ = a⁻¹) : Eig₃ t z a := by
  refine ⟨ha_t, ?_, ha_tz⟩
  have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_right htt
  calc z * a * z⁻¹ = t⁻¹ * ((t * z) * a * (t * z)⁻¹) * t := by group
    _ = t⁻¹ * a * t := by rw [ha_tz]
    _ = t * a * t⁻¹ := by rw [htinv]
    _ = a⁻¹ := ha_t

theorem nu_comm_12 {Y : Subgroup G}
    (hcl : ∀ a ∈ Y, ∀ b ∈ Y, ∀ c ∈ Y, ⁅a, b⁆ * c = c * ⁅a, b⁆) {t z a b : G}
    (haY : a ∈ Y) (hbY : b ∈ Y) (ha : Eig₁ t z a) (hb : Eig₂ t z b) : nu t z ⁅a, b⁆ = 1 := by
  obtain ⟨ha1, ha2, ha3⟩ := ha
  obtain ⟨hb1, hb2, hb3⟩ := hb
  unfold nu
  rw [conj_comm_pm hcl haY hbY ha1 hb1, conj_comm_mp hcl haY hbY ha2 hb2,
    conj_comm_mm hcl haY hbY ha3 hb3]
  group

theorem nu_comm_13 {Y : Subgroup G}
    (hcl : ∀ a ∈ Y, ∀ b ∈ Y, ∀ c ∈ Y, ⁅a, b⁆ * c = c * ⁅a, b⁆) {t z a b : G}
    (haY : a ∈ Y) (hbY : b ∈ Y) (ha : Eig₁ t z a) (hb : Eig₃ t z b) : nu t z ⁅a, b⁆ = 1 := by
  obtain ⟨ha1, ha2, ha3⟩ := ha
  obtain ⟨hb1, hb2, hb3⟩ := hb
  unfold nu
  rw [conj_comm_pm hcl haY hbY ha1 hb1, conj_comm_mm hcl haY hbY ha2 hb2,
    conj_comm_mp hcl haY hbY ha3 hb3]
  group

theorem nu_comm_23 {Y : Subgroup G}
    (hcl : ∀ a ∈ Y, ∀ b ∈ Y, ∀ c ∈ Y, ⁅a, b⁆ * c = c * ⁅a, b⁆) {t z a b : G}
    (haY : a ∈ Y) (hbY : b ∈ Y) (ha : Eig₂ t z a) (hb : Eig₃ t z b) : nu t z ⁅a, b⁆ = 1 := by
  obtain ⟨ha1, ha2, ha3⟩ := ha
  obtain ⟨hb1, hb2, hb3⟩ := hb
  unfold nu
  rw [conj_comm_mm hcl haY hbY ha1 hb1, conj_comm_pm hcl haY hbY ha2 hb2,
    conj_comm_mp hcl haY hbY ha3 hb3]
  group

end Eigen

section Decomposition

theorem nu_comm_base {Y : Subgroup G}
    (hcl : ∀ a ∈ Y, ∀ b ∈ Y, ∀ c ∈ Y, ⁅a, b⁆ * c = c * ⁅a, b⁆) {t z : G}
    (hYt : ∀ a ∈ Y, t * a * t⁻¹ ∈ Y) (hYz : ∀ a ∈ Y, z * a * z⁻¹ ∈ Y)
    {S₀ S₁ S₂ S₃ : Set G}
    (hS₀ : ∀ a ∈ S₀, a ∈ Y ∧ ∀ b ∈ Y, a * b = b * a)
    (hS₁ : ∀ a ∈ S₁, a ∈ Y ∧ Eig₁ t z a) (hS₂ : ∀ a ∈ S₂, a ∈ Y ∧ Eig₂ t z a)
    (hS₃ : ∀ a ∈ S₃, a ∈ Y ∧ Eig₃ t z a)
    (hab₁ : ∀ a ∈ Y, ∀ b ∈ Y, a * t = t * a → b * t = t * b → a * b = b * a)
    (hab₂ : ∀ a ∈ Y, ∀ b ∈ Y, a * z = z * a → b * z = z * b → a * b = b * a)
    (hab₃ : ∀ a ∈ Y, ∀ b ∈ Y, a * (t * z) = (t * z) * a → b * (t * z) = (t * z) * b →
      a * b = b * a)
    {a b : G} (ha : a ∈ S₀ ∨ a ∈ S₁ ∨ a ∈ S₂ ∨ a ∈ S₃) (hb : b ∈ S₀ ∨ b ∈ S₁ ∨ b ∈ S₂ ∨ b ∈ S₃) :
    nu t z ⁅a, b⁆ = 1 := by
  have hmemY : ∀ x, (x ∈ S₀ ∨ x ∈ S₁ ∨ x ∈ S₂ ∨ x ∈ S₃) → x ∈ Y := by
    rintro x (h | h | h | h)
    exacts [(hS₀ x h).1, (hS₁ x h).1, (hS₂ x h).1, (hS₃ x h).1]
  have haY := hmemY a ha
  have hbY := hmemY b hb
  have one_of_comm : a * b = b * a → nu t z ⁅a, b⁆ = 1 := fun h => by
    rw [commutatorElement_eq_one_iff_mul_comm.mpr h, nu_one]
  rcases ha with ha | ha | ha | ha
  · exact one_of_comm ((hS₀ a ha).2 b hbY)
  · rcases hb with hb | hb | hb | hb
    · exact one_of_comm ((hS₀ b hb).2 a haY).symm
    · obtain ⟨-, ea⟩ := hS₁ a ha
      obtain ⟨-, eb⟩ := hS₁ b hb
      exact one_of_comm (hab₁ a haY b hbY (mul_comm_of_conj_eq ea.1) (mul_comm_of_conj_eq eb.1))
    · exact nu_comm_12 hcl haY hbY (hS₁ a ha).2 (hS₂ b hb).2
    · exact nu_comm_13 hcl haY hbY (hS₁ a ha).2 (hS₃ b hb).2
  · rcases hb with hb | hb | hb | hb
    · exact one_of_comm ((hS₀ b hb).2 a haY).symm
    · exact nu_comm_swap hcl hYt hYz haY hbY (nu_comm_12 hcl hbY haY (hS₁ b hb).2 (hS₂ a ha).2)
    · obtain ⟨-, ea⟩ := hS₂ a ha
      obtain ⟨-, eb⟩ := hS₂ b hb
      exact one_of_comm
        (hab₂ a haY b hbY (mul_comm_of_conj_eq ea.2.1) (mul_comm_of_conj_eq eb.2.1))
    · exact nu_comm_23 hcl haY hbY (hS₂ a ha).2 (hS₃ b hb).2
  · rcases hb with hb | hb | hb | hb
    · exact one_of_comm ((hS₀ b hb).2 a haY).symm
    · exact nu_comm_swap hcl hYt hYz haY hbY (nu_comm_13 hcl hbY haY (hS₁ b hb).2 (hS₃ a ha).2)
    · exact nu_comm_swap hcl hYt hYz haY hbY (nu_comm_23 hcl hbY haY (hS₂ b hb).2 (hS₃ a ha).2)
    · obtain ⟨-, ea⟩ := hS₃ a ha
      obtain ⟨-, eb⟩ := hS₃ b hb
      exact one_of_comm
        (hab₃ a haY b hbY (mul_comm_of_conj_eq ea.2.2) (mul_comm_of_conj_eq eb.2.2))

theorem forall_of_decomp {Y : Subgroup G} {S₀ S₁ S₂ S₃ : Set G}
    (hdec : (Y : Set G) = S₀ * S₁ * S₂ * S₃) (h₀ : S₀ ⊆ Y) (h₁ : S₁ ⊆ Y) (h₂ : S₂ ⊆ Y)
    (h₃ : S₃ ⊆ Y) {P : G → Prop} (hmul : ∀ x ∈ Y, ∀ y ∈ Y, P x → P y → P (x * y))
    (p₀ : ∀ x ∈ S₀, P x) (p₁ : ∀ x ∈ S₁, P x) (p₂ : ∀ x ∈ S₂, P x) (p₃ : ∀ x ∈ S₃, P x) :
    ∀ x ∈ Y, P x := by
  intro x hx
  have hx' : x ∈ S₀ * S₁ * S₂ * S₃ := by rw [← hdec]; exact hx
  obtain ⟨_, ⟨_, ⟨k₀, hk₀, k₁, hk₁, rfl⟩, k₂, hk₂, rfl⟩, k₃, hk₃, rfl⟩ := hx'
  exact hmul _ (Y.mul_mem (Y.mul_mem (h₀ hk₀) (h₁ hk₁)) (h₂ hk₂)) _ (h₃ hk₃)
    (hmul _ (Y.mul_mem (h₀ hk₀) (h₁ hk₁)) _ (h₂ hk₂)
      (hmul _ (h₀ hk₀) _ (h₁ hk₁) (p₀ _ hk₀) (p₁ _ hk₁)) (p₂ _ hk₂)) (p₃ _ hk₃)

theorem nu_comm_all {Y : Subgroup G}
    (hcl : ∀ a ∈ Y, ∀ b ∈ Y, ∀ c ∈ Y, ⁅a, b⁆ * c = c * ⁅a, b⁆) {t z : G}
    (hYt : ∀ a ∈ Y, t * a * t⁻¹ ∈ Y) (hYz : ∀ a ∈ Y, z * a * z⁻¹ ∈ Y)
    {S₀ S₁ S₂ S₃ : Set G} (hdec : (Y : Set G) = S₀ * S₁ * S₂ * S₃)
    (hS₀ : ∀ a ∈ S₀, a ∈ Y ∧ ∀ b ∈ Y, a * b = b * a)
    (hS₁ : ∀ a ∈ S₁, a ∈ Y ∧ Eig₁ t z a) (hS₂ : ∀ a ∈ S₂, a ∈ Y ∧ Eig₂ t z a)
    (hS₃ : ∀ a ∈ S₃, a ∈ Y ∧ Eig₃ t z a)
    (hab₁ : ∀ a ∈ Y, ∀ b ∈ Y, a * t = t * a → b * t = t * b → a * b = b * a)
    (hab₂ : ∀ a ∈ Y, ∀ b ∈ Y, a * z = z * a → b * z = z * b → a * b = b * a)
    (hab₃ : ∀ a ∈ Y, ∀ b ∈ Y, a * (t * z) = (t * z) * a → b * (t * z) = (t * z) * b →
      a * b = b * a) :
    ∀ a ∈ Y, ∀ b ∈ Y, nu t z ⁅a, b⁆ = 1 := by
  have h₀ : S₀ ⊆ Y := fun x hx => (hS₀ x hx).1
  have h₁ : S₁ ⊆ Y := fun x hx => (hS₁ x hx).1
  have h₂ : S₂ ⊆ Y := fun x hx => (hS₂ x hx).1
  have h₃ : S₃ ⊆ Y := fun x hx => (hS₃ x hx).1
  have hmemY : ∀ x, (x ∈ S₀ ∨ x ∈ S₁ ∨ x ∈ S₂ ∨ x ∈ S₃) → x ∈ Y := by
    rintro x (h | h | h | h)
    exacts [h₀ h, h₁ h, h₂ h, h₃ h]
  have base : ∀ {a b : G}, (a ∈ S₀ ∨ a ∈ S₁ ∨ a ∈ S₂ ∨ a ∈ S₃) →
      (b ∈ S₀ ∨ b ∈ S₁ ∨ b ∈ S₂ ∨ b ∈ S₃) → nu t z ⁅a, b⁆ = 1 := fun ha hb =>
    nu_comm_base hcl hYt hYz hS₀ hS₁ hS₂ hS₃ hab₁ hab₂ hab₃ ha hb
  have stepA : ∀ a, (a ∈ S₀ ∨ a ∈ S₁ ∨ a ∈ S₂ ∨ a ∈ S₃) → ∀ b ∈ Y, nu t z ⁅a, b⁆ = 1 := by
    intro a ha
    have haY := hmemY a ha
    have hmulA : ∀ x ∈ Y, ∀ y ∈ Y, nu t z ⁅a, x⁆ = 1 → nu t z ⁅a, y⁆ = 1 →
        nu t z ⁅a, x * y⁆ = 1 := by
      intro x hx y hy hpx hpy
      rw [comm_mul_right hcl haY hx hy,
        nu_mul_commutator hcl hYt hYz (Subgroup.commutator_mem_commutator haY hx)
          (Subgroup.commutator_mem_commutator haY hy), hpx, hpy, mul_one]
    exact forall_of_decomp hdec h₀ h₁ h₂ h₃ (P := fun b => nu t z ⁅a, b⁆ = 1) hmulA
      (fun x hx => base ha (Or.inl hx)) (fun x hx => base ha (Or.inr (Or.inl hx)))
      (fun x hx => base ha (Or.inr (Or.inr (Or.inl hx))))
      (fun x hx => base ha (Or.inr (Or.inr (Or.inr hx))))
  intro a ha b hb
  have hmulB : ∀ x ∈ Y, ∀ y ∈ Y, nu t z ⁅x, b⁆ = 1 → nu t z ⁅y, b⁆ = 1 →
      nu t z ⁅x * y, b⁆ = 1 := by
    intro x hx y hy hpx hpy
    rw [comm_mul_left hcl hx hy hb,
      nu_mul_commutator hcl hYt hYz (Subgroup.commutator_mem_commutator hy hb)
        (Subgroup.commutator_mem_commutator hx hb), hpx, hpy, mul_one]
  exact forall_of_decomp hdec h₀ h₁ h₂ h₃ (P := fun a => nu t z ⁅a, b⁆ = 1) hmulB
    (fun x hx => stepA x (Or.inl hx) b hb) (fun x hx => stepA x (Or.inr (Or.inl hx)) b hb)
    (fun x hx => stepA x (Or.inr (Or.inr (Or.inl hx))) b hb)
    (fun x hx => stepA x (Or.inr (Or.inr (Or.inr hx))) b hb) a ha

end Decomposition

theorem eq_one_of_nu {Y : Subgroup G} (hY : Odd (Nat.card Y))
    (hcl : ∀ a ∈ Y, ∀ b ∈ Y, ∀ c ∈ Y, ⁅a, b⁆ * c = c * ⁅a, b⁆) {t z : G}
    (hYt : ∀ a ∈ Y, t * a * t⁻¹ ∈ Y) (hYz : ∀ a ∈ Y, z * a * z⁻¹ ∈ Y)
    (hnu : ∀ a ∈ Y, ∀ b ∈ Y, nu t z ⁅a, b⁆ = 1) {s : G} (hs : s ∈ ⁅Y, Y⁆)
    (hst : s * t = t * s) (hsz : s * z = z * s) : s = 1 := by
  let B : Subgroup G :=
    { carrier := {x | x ∈ ⁅Y, Y⁆ ∧ nu t z x = 1}
      mul_mem' := fun {x y} hx hy => ⟨Subgroup.mul_mem _ hx.1 hy.1, by
        rw [nu_mul_commutator hcl hYt hYz hx.1 hy.1, hx.2, hy.2, mul_one]⟩
      one_mem' := ⟨Subgroup.one_mem _, nu_one t z⟩
      inv_mem' := fun {x} hx => ⟨Subgroup.inv_mem _ hx.1, by
        rw [nu_inv_commutator hcl hYt hYz hx.1, hx.2, inv_one]⟩ }
  have hle : ⁅Y, Y⁆ ≤ B := by
    rw [Subgroup.commutator_le]
    intro a ha b hb
    exact ⟨Subgroup.commutator_mem_commutator ha hb, hnu a ha b hb⟩
  have hns : nu t z s = 1 := (hle hs).2
  have hts : t * s * t⁻¹ = s := by rw [← hst]; group
  have hzs : z * s * z⁻¹ = s := by rw [← hsz]; group
  have htzs : (t * z) * s * (t * z)⁻¹ = s := by
    calc (t * z) * s * (t * z)⁻¹ = t * (z * s * z⁻¹) * t⁻¹ := by group
      _ = s := by rw [hzs, hts]
  have h4 : s * s * s * s = 1 := by
    unfold nu at hns
    rwa [hts, hzs, htzs] at hns
  have hs4 : s ^ 4 = 1 := by
    rw [pow_succ, pow_succ, pow_succ, pow_one]; exact h4
  have hsY : s ∈ Y := Subgroup.commutator_le_self Y hs
  have hodd : Odd (orderOf s) := hY.of_dvd_nat (Subgroup.orderOf_dvd_natCard Y hsY)
  have hdvd : orderOf s ∣ 4 := orderOf_dvd_of_pow_eq_one hs4
  have h1 : orderOf s = 1 := by
    obtain ⟨m, hm⟩ := hodd
    have hle4 : orderOf s ≤ 4 := Nat.le_of_dvd (by norm_num) hdvd
    rw [hm] at hdvd hle4 ⊢
    have hm1 : m ≤ 1 := by omega
    interval_cases m
    · rfl
    · omega
  exact orderOf_eq_one_iff.mp h1

end TC6N

theorem eq_one_of_mem_commutator_of_centralizes {G : Type} [Group G] [Finite G]
    {Y T : Subgroup G} [IsKleinFour T] {t z : G}
    (hY : Odd (Nat.card Y)) (hTY : T ≤ normalizer (Y : Set G))
    (ht : t ∈ T) (hz : z ∈ T) (ht1 : t ≠ 1) (hz1 : z ≠ 1) (htz : t ≠ z)
    (hcl : ∀ a ∈ Y, ∀ b ∈ Y, ∀ c ∈ Y, a * b * a⁻¹ * b⁻¹ * c = c * (a * b * a⁻¹ * b⁻¹))
    (hK0 : ∀ a ∈ Y, (∀ r ∈ T, a * r = r * a) → ∀ b ∈ Y, a * b = b * a)
    (hab : ∀ r ∈ T, r ≠ 1 → ∀ a ∈ Y, ∀ b ∈ Y, a * r = r * a → b * r = r * b → a * b = b * a)
    {s : G} (hs : s ∈ ⁅Y, Y⁆) (hst : s * t = t * s) (hsz : s * z = z * s) : s = 1 := by
  have hdec := (CFSG.ABGLocalTools.four_group_T_decomposition hY hTY ht hz ht1 hz1 htz).2
  have htt : t * t = 1 := CFSG.ABGLocalTools.kleinFour_mul_self ht
  have hzz : z * z = 1 := CFSG.ABGLocalTools.kleinFour_mul_self hz
  have htzT : t * z ∈ T := T.mul_mem ht hz
  have htz1 : t * z ≠ 1 := by
    intro h
    apply htz
    rw [mul_eq_one_iff_eq_inv, inv_eq_of_mul_eq_one_right hzz] at h
    exact h
  have hYt : ∀ a ∈ Y, t * a * t⁻¹ ∈ Y := fun a ha =>
    (Subgroup.mem_normalizer_iff.mp (hTY ht) a).mp ha
  have hYz : ∀ a ∈ Y, z * a * z⁻¹ ∈ Y := fun a ha =>
    (Subgroup.mem_normalizer_iff.mp (hTY hz) a).mp ha
  have hcl' : ∀ a ∈ Y, ∀ b ∈ Y, ∀ c ∈ Y, ⁅a, b⁆ * c = c * ⁅a, b⁆ := hcl
  refine TC6N.eq_one_of_nu hY hcl' hYt hYz
    (TC6N.nu_comm_all hcl' hYt hYz hdec ?_ ?_ ?_ ?_ (hab t ht ht1) (hab z hz hz1)
      (hab (t * z) htzT htz1)) hs hst hsz
  · exact fun a ha => ⟨ha.1, fun b hb => hK0 a ha.1
      (fun r hr => (Subgroup.mem_centralizer_iff.mp ha.2 r hr).symm) b hb⟩
  · exact fun a ha => ⟨ha.1, TC6N.eig₁_of ha.2.1 ha.2.2⟩
  · exact fun a ha => ⟨ha.1, TC6N.eig₂_of ha.2.1 ha.2.2⟩
  · exact fun a ha => ⟨ha.1, TC6N.eig₃_of htt ha.2.1 ha.2.2⟩

end CFSG.GH74.Uniqueness.SU.SU13
