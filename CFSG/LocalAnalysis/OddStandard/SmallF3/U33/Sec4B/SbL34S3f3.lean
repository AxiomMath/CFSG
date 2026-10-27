module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbL34S3f2
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbL34S3c2a

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33.L34Z

open Subgroup
open CFSG.OddStandard.SmallF3.HarrisU33.L34

variable {G : Type} [Group G] [Finite G] {t : G} {L S : Subgroup G} {x₁ x₂ lam rho tau : G}


theorem exists_Z_P (ha : Ctx4A t L S x₁ x₂ lam rho tau) (σ : Sig4 t tau x₁ x₂) :
    ∃ A : Subgroup G, fourGrp x₁ x₂ ≤ A ∧ A ≤ ctxPL t tau x₁ x₂ ∧
      4 * Nat.card (fourGrp x₁ x₂) ≤ Nat.card A ∧
      ∀ a ∈ A, ∀ q ∈ ctxPL t tau x₁ x₂, a * q * a⁻¹ * q⁻¹ ∈ fourGrp x₁ x₂ := by
  have hc := ha.toCtx4L.toCtx4Q
  have hP_le_LO : ctxPL t tau x₁ x₂ ≤ ctxLO t tau x₁ x₂ := (normal_ctxPL ha).1
  obtain ⟨xa, hxa⟩ := σ.surj klein4_a
  obtain ⟨xb, hxb⟩ := σ.surj klein4_b
  let a : G := (xa : G)
  let b : G := (xb : G)
  have hka : klein4_a ∈ klein4 := (mem_klein4_iff klein4_a).mpr (Or.inr (Or.inl rfl))
  have hkb : klein4_b ∈ klein4 :=
    (mem_klein4_iff klein4_b).mpr (Or.inr (Or.inr (Or.inl rfl)))
  have haP : a ∈ ctxPL t tau x₁ x₂ := (mem_ctxPL_iff ha σ xa.2).mpr (by
    show σ.φ xa ∈ klein4
    rw [hxa]; exact hka)
  have hbP : b ∈ ctxPL t tau x₁ x₂ := (mem_ctxPL_iff ha σ xb.2).mpr (by
    show σ.φ xb ∈ klein4
    rw [hxb]; exact hkb)
  have haLO : a ∈ ctxLO t tau x₁ x₂ := (Subgroup.mem_inf.mp (by simpa [ctxPL] using haP)).1
  have hbLO : b ∈ ctxLO t tau x₁ x₂ := (Subgroup.mem_inf.mp (by simpa [ctxPL] using hbP)).1
  have haC : a ∈ centralizer ((fourGrp x₁ x₂ : Subgroup G) : Set G) :=
    (Subgroup.mem_inf.mp (by simpa [ctxPL] using haP)).2
  have hbC : b ∈ centralizer ((fourGrp x₁ x₂ : Subgroup G) : Set G) :=
    (Subgroup.mem_inf.mp (by simpa [ctxPL] using hbP)).2
  have haO : ∀ x ∈ ctxO t tau x₁ x₂, a * x * a⁻¹ ∈ ctxO t tau x₁ x₂ := fun x hx =>
    (Subgroup.mem_normalizer_iff.mp haLO x).mp hx
  have hbO : ∀ x ∈ ctxO t tau x₁ x₂, b * x * b⁻¹ ∈ ctxO t tau x₁ x₂ := fun x hx =>
    (Subgroup.mem_normalizer_iff.mp hbLO x).mp hx
  have haV : ∀ v ∈ fourGrp x₁ x₂, a * v * a⁻¹ ∈ fourGrp x₁ x₂ := by
    intro v hv
    have hcomm := Subgroup.mem_centralizer_iff.mp haC v hv
    have heq : a * v * a⁻¹ = v := by rw [← hcomm]; group
    rw [heq]; exact hv
  have hbV : ∀ v ∈ fourGrp x₁ x₂, b * v * b⁻¹ ∈ fourGrp x₁ x₂ := by
    intro v hv
    have hcomm := Subgroup.mem_centralizer_iff.mp hbC v hv
    have heq : b * v * b⁻¹ = v := by rw [← hcomm]; group
    rw [heq]; exact hv
  have ha2 : a * a ∈ ctxO t tau x₁ x₂ := by
    have hker : xa * xa ∈ σ.φ.ker := MonoidHom.mem_ker.mpr (by
      rw [map_mul, hxa, klein4_sq hka])
    rw [σ.ker_eq] at hker
    exact Subgroup.mem_subgroupOf.mp hker
  have hb2 : b * b ∈ ctxO t tau x₁ x₂ := by
    have hker : xb * xb ∈ σ.φ.ker := MonoidHom.mem_ker.mpr (by
      rw [map_mul, hxb, klein4_sq hkb])
    rw [σ.ker_eq] at hker
    exact Subgroup.mem_subgroupOf.mp hker
  have hab : a * b * a⁻¹ * b⁻¹ ∈ ctxO t tau x₁ x₂ := by
    have hcomm_ab : klein4_a * klein4_b = klein4_b * klein4_a := klein4_comm hka hkb
    have hker : xa * xb * xa⁻¹ * xb⁻¹ ∈ σ.φ.ker := MonoidHom.mem_ker.mpr (by
      simp only [map_mul, map_inv, hxa, hxb]
      rw [hcomm_ab]; group)
    rw [σ.ker_eq] at hker
    exact Subgroup.mem_subgroupOf.mp hker
  have hcardO : Nat.card (ctxO t tau x₁ x₂) = 2 ^ 6 * Nat.card (fourGrp x₁ x₂) := by
    rw [hc.card_O, card_fourGrp hc]; norm_num
  have hVn : ∀ o ∈ ctxO t tau x₁ x₂, ∀ v ∈ fourGrp x₁ x₂,
      o * v * o⁻¹ ∈ fourGrp x₁ x₂ := by
    intro o ho v hv
    have hcomm := V_comm_O hc ho hv
    have heq : o * v * o⁻¹ = v := by rw [hcomm]; group
    rw [heq]; exact hv
  have hcommOO : ∀ x ∈ ctxO t tau x₁ x₂, ∀ y ∈ ctxO t tau x₁ x₂,
      x * y * x⁻¹ * y⁻¹ ∈ fourGrp x₁ x₂ := fun x hx y hy => O_comm_le hc hx hy
  have hsq : ∀ x ∈ ctxO t tau x₁ x₂, x * x ∈ fourGrp x₁ x₂ := fun x hx => O_sq_mem_V hc hx
  obtain ⟨A, hVA, hAO, hcardA, hAa, hAb⟩ :=
    exists_subgroup_centralized_mod (ctxO t tau x₁ x₂) (fourGrp x₁ x₂) a b
      (V_le_O hc) hVn hcommOO hsq hcardO haO haV hbO hbV ha2 hb2 hab
  let Qset : Set G := fun q => q ∈ ctxPL t tau x₁ x₂ ∧
    ∀ x ∈ A, x * q * x⁻¹ * q⁻¹ ∈ fourGrp x₁ x₂
  have hone : (1 : G) ∈ Qset := by
    refine ⟨one_mem _, ?_⟩
    intro x hx
    have heq : x * 1 * x⁻¹ * 1⁻¹ = 1 := by group
    rw [heq]; exact one_mem _
  have hmul : ∀ q₁ ∈ Qset, ∀ q₂ ∈ Qset, q₁ * q₂ ∈ Qset := by
    intro q₁ hq₁ q₂ hq₂
    refine ⟨mul_mem hq₁.1 hq₂.1, ?_⟩
    intro x hx
    have h1 : x * q₁ * x⁻¹ * q₁⁻¹ ∈ fourGrp x₁ x₂ := hq₁.2 x hx
    have h2 : x * q₂ * x⁻¹ * q₂⁻¹ ∈ fourGrp x₁ x₂ := hq₂.2 x hx
    have hq₁C : q₁ ∈ centralizer ((fourGrp x₁ x₂ : Subgroup G) : Set G) :=
      (Subgroup.mem_inf.mp (by simpa [ctxPL] using hq₁.1)).2
    have hcomm : (x * q₂ * x⁻¹ * q₂⁻¹) * q₁ = q₁ * (x * q₂ * x⁻¹ * q₂⁻¹) :=
      Subgroup.mem_centralizer_iff.mp hq₁C _ h2
    have hid : x * (q₁ * q₂) * x⁻¹ * (q₁ * q₂)⁻¹
        = (x * q₁ * x⁻¹ * q₁⁻¹) * (q₁ * (x * q₂ * x⁻¹ * q₂⁻¹) * q₁⁻¹) := by group
    rw [hid]
    refine mul_mem h1 ?_
    have heq : q₁ * (x * q₂ * x⁻¹ * q₂⁻¹) * q₁⁻¹ = x * q₂ * x⁻¹ * q₂⁻¹ := by
      rw [← hcomm]; group
    rw [heq]; exact h2
  have hOsub : ∀ o ∈ ctxO t tau x₁ x₂, o ∈ Qset := by
    intro o ho
    refine ⟨O_le_ctxPL ha ho, ?_⟩
    intro x hx
    exact O_comm_le hc (hAO hx) ho
  have ha_mem : a ∈ Qset := by
    refine ⟨haP, ?_⟩
    intro x hx
    have h := hAa x hx
    have heq : x * a * x⁻¹ * a⁻¹ = (a * x * a⁻¹ * x⁻¹)⁻¹ := by group
    rw [heq]; exact inv_mem h
  have hb_mem : b ∈ Qset := by
    refine ⟨hbP, ?_⟩
    intro x hx
    have h := hAb x hx
    have heq : x * b * x⁻¹ * b⁻¹ = (b * x * b⁻¹ * x⁻¹)⁻¹ := by group
    rw [heq]; exact inv_mem h
  have hall : ∀ q ∈ ctxPL t tau x₁ x₂, q ∈ Qset := by
    intro q hqP
    have hqLO : q ∈ ctxLO t tau x₁ x₂ := hP_le_LO hqP
    have hk : σ.φ ⟨q, hqLO⟩ ∈ klein4 := (mem_ctxPL_iff ha σ hqLO).mp hqP
    have key : ∃ w : ↥(ctxLO t tau x₁ x₂),
        (w : G) ∈ Qset ∧ σ.φ w = σ.φ ⟨q, hqLO⟩ := by
      rcases (mem_klein4_iff (σ.φ ⟨q, hqLO⟩)).mp hk with h1 | h2 | h3 | h4
      · exact ⟨1, hone, by rw [map_one, h1]⟩
      · exact ⟨xa, ha_mem, by rw [hxa, h2]⟩
      · exact ⟨xb, hb_mem, by rw [hxb, h3]⟩
      · exact ⟨xa * xb, hmul _ ha_mem _ hb_mem, by rw [map_mul, hxa, hxb, h4]⟩
    obtain ⟨w, hwQ, hwφ⟩ := key
    have hoKer : w⁻¹ * ⟨q, hqLO⟩ ∈ σ.φ.ker :=
      MonoidHom.mem_ker.mpr (by rw [map_mul, map_inv, hwφ, inv_mul_cancel])
    have hoO : ((w⁻¹ * ⟨q, hqLO⟩ : ↥(ctxLO t tau x₁ x₂)) : G) ∈ ctxO t tau x₁ x₂ := by
      rw [σ.ker_eq] at hoKer
      exact Subgroup.mem_subgroupOf.mp hoKer
    have hoQ : ((w⁻¹ * ⟨q, hqLO⟩ : ↥(ctxLO t tau x₁ x₂)) : G) ∈ Qset := hOsub _ hoO
    have hqeq : q = (w : G) * ((w⁻¹ * ⟨q, hqLO⟩ : ↥(ctxLO t tau x₁ x₂)) : G) := by
      have heq_sub : (⟨q, hqLO⟩ : ↥(ctxLO t tau x₁ x₂)) = w * (w⁻¹ * ⟨q, hqLO⟩) := by group
      simpa using congrArg Subtype.val heq_sub
    rw [hqeq]
    exact hmul _ hwQ _ hoQ
  exact ⟨A, hVA, hAO.trans (O_le_ctxPL ha), hcardA, fun x hx q hq => (hall q hq).2 x hx⟩

end CFSG.OddStandard.SmallF3.HarrisU33.L34Z
