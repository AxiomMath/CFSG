module

public import CFSG.CGT.PushingUpLit.SYMB.FiveMem
public import CFSG.CGT.PushingUpLit.SYMB.FiveStruct

public section

namespace CFSG.CGT.PushingUpLit.SYMB

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.A1b CFSG.QuasithinUnique CFSG.RankThree.PartOne
  CFSG.CGT.PushingUpLit CFSG.CGT.PushingUpLit.BHS CFSG.CGT.PushingUpLit.BHS6
  CFSG.CGT.PushingUpLit.BHS7
open scoped commutatorElement

theorem aux_f3 {M : Type*} [Group M] (x g c : M) (hx : x * x = 1) (hcx : c * x = x * c) :
    ⁅x, g * (c * x) * g⁻¹⁆ =
      (x * g * x⁻¹) * (⁅c, (x * g⁻¹ * x⁻¹ * g)⁻¹⁆ *
        ((x * g⁻¹ * x⁻¹ * g) * (x * g⁻¹ * x⁻¹ * g))⁻¹) * (x * g * x⁻¹)⁻¹ := by
  have hxi : x⁻¹ = x := inv_eq_of_mul_eq_one_right hx
  have hcx2 : ∀ r : M, c * (x * r) = x * (c * r) := fun r => by
    rw [← mul_assoc, hcx, mul_assoc]
  have e1 : ⁅x, g * (c * x) * g⁻¹⁆ =
      x * g * c * x * g⁻¹ * x⁻¹ * g * x⁻¹ * c⁻¹ * g⁻¹ := by
    simp only [commutatorElement_def]
    group
  have e2 : (x * g * x⁻¹) * (⁅c, (x * g⁻¹ * x⁻¹ * g)⁻¹⁆ *
        ((x * g⁻¹ * x⁻¹ * g) * (x * g⁻¹ * x⁻¹ * g))⁻¹) * (x * g * x⁻¹)⁻¹ =
      x * g * x⁻¹ * c * g⁻¹ * x * g * x⁻¹ * c⁻¹ * g⁻¹ := by
    simp only [commutatorElement_def]
    group
  rw [e1, e2]
  simp only [hxi, mul_assoc, hcx2]

variable {Γ : Type} [Group Γ] [Finite Γ] {G T V : Subgroup Γ}
  {φ : ↥G →* Equiv.Perm (Fin 5)} {ψ : ↥V →* ↥(G6.coreMod 5)} {T' : Set (Equiv.Perm (Fin 5))}
  {S : SymSetting G T V 5 φ ψ T'} {E : Subgroup Γ}

theorem comm_conj_mem (h : FiveCase S E) {z : Γ} (hz2 : z * z = 1)
    (hzG : ∀ g ∈ G, g * z = z * g) {x c g : Γ} (hxG : x ∈ G) (hcR : c ∈ kerG G φ) (hgE : g ∈ E)
    (hx2 : x * x = 1) (hcx : c * x = x * c)
    (hh2 : z⁻¹ * ((x * g⁻¹ * x⁻¹ * g) * (x * g⁻¹ * x⁻¹ * g)) ∈ ⁅V, E⁆) :
    z⁻¹ * ⁅x, g * (c * x) * g⁻¹⁆ ∈ ⁅V, E⁆ := by
  set V₁ : Subgroup Γ := ⁅V, E⁆ with hV₁
  have hEG : E ≤ G := h.join.le
  have hgG : g ∈ G := hEG hgE
  have hV₁G : V₁ ≤ G := fun y hy =>
    (mem_kerG.1 (V_le_kerG S (comm_V_E_le_V S hEG hy))).1
  have hzi : ∀ y ∈ G, z⁻¹ * y = y * z⁻¹ := fun y hy => by
    have := hzG y hy
    calc z⁻¹ * y = z⁻¹ * (y * z) * z⁻¹ := by group
      _ = z⁻¹ * (z * y) * z⁻¹ := by rw [this]
      _ = y * z⁻¹ := by group
  set hh : Γ := x * g⁻¹ * x⁻¹ * g with hhdef
  have hhE : hh ∈ E := by
    have h1 : x * g⁻¹ * x⁻¹ ∈ E :=
      (Subgroup.mem_normalizer_iff.mp (h.normal hxG) g⁻¹).mp (E.inv_mem hgE)
    exact E.mul_mem h1 hgE
  have hk : ⁅c, hh⁻¹⁆ ∈ V₁ := h.comm_R_E hcR (E.inv_mem hhE)
  set w : Γ := z⁻¹ * (hh * hh) with hw
  have hwV : w ∈ V₁ := hh2
  have hhh : hh * hh = z * w := by rw [hw]; group
  have hkw : ⁅c, hh⁻¹⁆ * w⁻¹ ∈ V₁ := V₁.mul_mem hk (V₁.inv_mem hwV)
  set θ : Γ := x * g * x⁻¹ with hθ
  have hθG : θ ∈ G := G.mul_mem (G.mul_mem hxG hgG) (G.inv_mem hxG)
  have hz2' : z⁻¹ * z⁻¹ = 1 := by
    have : z⁻¹ = z := inv_eq_of_mul_eq_one_right hz2
    rw [this, hz2]
  have e1 : z⁻¹ * (⁅c, hh⁻¹⁆ * (hh * hh)⁻¹) = ⁅c, hh⁻¹⁆ * w⁻¹ := by
    rw [hhh]
    have hc : z⁻¹ * (⁅c, hh⁻¹⁆ * w⁻¹) = (⁅c, hh⁻¹⁆ * w⁻¹) * z⁻¹ := hzi _ (hV₁G hkw)
    calc z⁻¹ * (⁅c, hh⁻¹⁆ * (z * w)⁻¹) = z⁻¹ * (⁅c, hh⁻¹⁆ * w⁻¹) * z⁻¹ := by group
      _ = (⁅c, hh⁻¹⁆ * w⁻¹) * z⁻¹ * z⁻¹ := by rw [hc]
      _ = (⁅c, hh⁻¹⁆ * w⁻¹) * (z⁻¹ * z⁻¹) := by rw [mul_assoc]
      _ = ⁅c, hh⁻¹⁆ * w⁻¹ := by rw [hz2', mul_one]
  have e2 : z⁻¹ * ⁅x, g * (c * x) * g⁻¹⁆ = θ * (⁅c, hh⁻¹⁆ * w⁻¹) * θ⁻¹ := by
    rw [aux_f3 x g c hx2 hcx]
    calc z⁻¹ * (θ * (⁅c, hh⁻¹⁆ * (hh * hh)⁻¹) * θ⁻¹)
        = (z⁻¹ * θ) * (⁅c, hh⁻¹⁆ * (hh * hh)⁻¹) * θ⁻¹ := by group
      _ = (θ * z⁻¹) * (⁅c, hh⁻¹⁆ * (hh * hh)⁻¹) * θ⁻¹ := by rw [hzi θ hθG]
      _ = θ * (z⁻¹ * (⁅c, hh⁻¹⁆ * (hh * hh)⁻¹)) * θ⁻¹ := by group
      _ = θ * (⁅c, hh⁻¹⁆ * w⁻¹) * θ⁻¹ := by rw [e1]
  rw [e2]
  exact (Subgroup.mem_normalizer_iff.mp (comm_V_E_normal S h.normal hθG) _).mp hkw

end CFSG.CGT.PushingUpLit.SYMB
