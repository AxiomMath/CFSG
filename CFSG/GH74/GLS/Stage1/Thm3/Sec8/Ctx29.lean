module

public import CFSG.GH74.GLS.Stage1.Thm3.Sec8.Ctx25
public import CFSG.GH74.GLS.Stage1.Thm3.Sec8.Ctx27

public section

namespace CFSG.GH74.GLS.Stage1.Thm3.Sec8

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.GH74.GLS.Stage1.Thm2.Recip
  CFSG.GH74.GLS.Stage1.Thm3.Sec4 CFSG.GH74.GLS.Stage1.Thm3.Sec5 CFSG.GH74.GLS.Stage1.Thm3.Sec6
open scoped commutatorElement Pointwise

namespace Setup8

variable {G : Type} [Group G] [Finite G] {z : G} {S K₁ K₂ W₁ W₂ U : Subgroup G} {u h : G}

theorem xdata (hII : II4_4_4_center) (hq : II4_4_quat) (hs : Setup8 G z S K₁ K₂ W₁ W₂ U u h)
    (hk : Nat.card ↥(Vof S K₁ W₂) = 2 ^ (1 + 1)) :
    ∃ x : G, Vof S K₁ W₂ = zpowers x ∧ orderOf x = 4 ∧ orderOf (h⁻¹ * x * h) = 4 ∧
      zpowers x ⊓ zpowers (h⁻¹ * x * h) = ⊥ ∧ z = x * x := by
  obtain ⟨x, hxV, hVx, hxo, hxz⟩ := hs.gen_V₁ hII hq hk
  have hxo4 : orderOf x = 4 := by rw [hxo]; norm_num
  have hx'V : h⁻¹ * x * h ∈ conjugate (Vof S K₁ W₂) h := by
    rw [mem_conjugate_iff]
    have e : h * (h⁻¹ * x * h) * h⁻¹ = x := by group
    rw [e]; exact hxV
  refine ⟨x, hVx, hxo4, ?_, ?_, ?_⟩
  · have := orderOf_conj' h⁻¹ x
    rw [inv_inv] at this
    rw [this, hxo4]
  · have h1 : zpowers x ≤ Vof S K₁ W₂ := Subgroup.zpowers_le.2 hxV
    have h2 : zpowers (h⁻¹ * x * h) ≤ conjugate (Vof S K₁ W₂) h := Subgroup.zpowers_le.2 hx'V
    exact le_bot_iff.1 ((inf_le_inf h1 h2).trans (hs.V₁_inf_V_bot hII hq).le)
  · rw [pow_one, pow_two] at hxz
    exact hxz.symm

theorem conj_comm_psi {d : G} (hdh : d * h = h * d) (g : G) :
    d * (h⁻¹ * g * h) * d⁻¹ = h⁻¹ * (d * g * d⁻¹) * h := by
  have hdd : h⁻¹ * d * h = d := by
    calc h⁻¹ * d * h = h⁻¹ * (d * h) := by group
      _ = h⁻¹ * (h * d) := by rw [hdh]
      _ = d := by group
  calc d * (h⁻¹ * g * h) * d⁻¹ = (h⁻¹ * d * h) * (h⁻¹ * g * h) * (h⁻¹ * d * h)⁻¹ := by rw [hdd]
    _ = h⁻¹ * (d * g * d⁻¹) * h := by group

theorem conj_mem_gen (hII : II4_4_4_center) (hq : II4_4_quat) (hrec : Bg.B_reciprocity)
    (hs : Setup8 G z S K₁ K₂ W₁ W₂ U u h) {x : G} (hVx : Vof S K₁ W₂ = zpowers x) {d : G}
    (hdS : d ∈ S) : d * x * d⁻¹ ∈ zpowers x ⊔ zpowers (h⁻¹ * x * h) := by
  have hxA : x ∈ Aof S K₁ W₂ h := Subgroup.mem_sup_left (hVx ▸ Subgroup.mem_zpowers x)
  exact hs.A_le_gen hII hq hrec hVx (hs.A_normS hII hq hrec hdS hxA)

theorem D_sq (hII : II4_4_4_center) (hq : II4_4_quat) (hrec : Bg.B_reciprocity)
    (hs : Setup8 G z S K₁ K₂ W₁ W₂ U u h) (hk : Nat.card ↥(Vof S K₁ W₂) = 2 ^ (1 + 1)) {d : G}
    (hd : d ∈ Dsub S U h) : d * d = 1 := by
  obtain ⟨x, hVx, hxo, hx'o, hbot, hz⟩ := hs.xdata hII hq hk
  have hdW := ((mem_Dsub_iff).1 hd).1
  have hdh := ((mem_Dsub_iff).1 hd).2
  have hxV : x ∈ Vof S K₁ W₂ := hVx ▸ Subgroup.mem_zpowers x
  have hxA : x ∈ Aof S K₁ W₂ h := Subgroup.mem_sup_left hxV
  have hx'A : h⁻¹ * x * h ∈ Aof S K₁ W₂ h := (hs.A_conj hII hq hrec (k := 1 + 1) hk hxA).2
  have hcomm : x * (h⁻¹ * x * h) = (h⁻¹ * x * h) * x := hs.A_comm hII hq hrec _ hxA _ hx'A
  have hψx : (MulAut.conj h⁻¹) x = h⁻¹ * x * h := by
    show h⁻¹ * x * h⁻¹⁻¹ = h⁻¹ * x * h
    rw [inv_inv]
  have hψrel : x * (h⁻¹ * x * h) * (MulAut.conj h⁻¹) (h⁻¹ * x * h) = 1 := by
    show x * (h⁻¹ * x * h) * (h⁻¹ * (h⁻¹ * x * h) * h⁻¹⁻¹) = 1
    rw [inv_inv]
    exact hs.psi_rel hII hq hrec hk hxV
  have hφψ : (MulAut.conj d) (h⁻¹ * x * h) = (MulAut.conj h⁻¹) ((MulAut.conj d) x) := by
    show d * (h⁻¹ * x * h) * d⁻¹ = h⁻¹ * (d * x * d⁻¹) * h⁻¹⁻¹
    rw [inv_inv]
    exact conj_comm_psi hdh x
  have hzU : z ∈ U := hs.z_mem
  have hφz : (MulAut.conj d) z = z := by
    show d * z * d⁻¹ = z
    have := (Subgroup.mem_centralizer_iff.1 hdW.2) z hzU
    rw [← this]; group
  have hc : (MulAut.conj d) x ∈ zpowers x ⊔ zpowers (h⁻¹ * x * h) :=
    hs.conj_mem_gen hII hq hrec hVx hdW.1
  have hφφ := Basic.phi_sq_trivial hxo hx'o hbot hcomm hz (MulAut.conj d) (MulAut.conj h⁻¹) hψx
    hψrel hφψ hφz hc
  have hφφ' : d * (d * x * d⁻¹) * d⁻¹ = x := hφφ
  have hxfix : (d * d) * x = x * (d * d) := by
    calc (d * d) * x = (d * (d * x * d⁻¹) * d⁻¹) * (d * d) := by group
      _ = x * (d * d) := by rw [hφφ']
  have hx'fix' : d * (d * (h⁻¹ * x * h) * d⁻¹) * d⁻¹ = h⁻¹ * x * h := by
    rw [conj_comm_psi hdh x, conj_comm_psi hdh (d * x * d⁻¹), hφφ']
  have hx'fix : (d * d) * (h⁻¹ * x * h) = (h⁻¹ * x * h) * (d * d) := by
    calc (d * d) * (h⁻¹ * x * h) = (d * (d * (h⁻¹ * x * h) * d⁻¹) * d⁻¹) * (d * d) := by group
      _ = (h⁻¹ * x * h) * (d * d) := by rw [hx'fix']
  have hddA : d * d ∈ Aof S K₁ W₂ h :=
    hs.mem_A_of_fix hII hq hrec hVx (mul_mem hdW.1 hdW.1) hxfix.symm hx'fix.symm
  have hddD : d * d ∈ Dsub S U h := mul_mem hd hd
  have h1 : d * d ∈ Aof S K₁ W₂ h ⊓ Dsub S U h := Subgroup.mem_inf.2 ⟨hddA, hddD⟩
  rw [hs.D_inf_A hII hq hrec hk] at h1
  exact h1

end Setup8

end CFSG.GH74.GLS.Stage1.Thm3.Sec8
