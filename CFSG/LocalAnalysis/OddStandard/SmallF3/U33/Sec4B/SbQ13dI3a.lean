module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbQ13c2

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33.S4B

open Subgroup
open scoped Pointwise

variable {G : Type} [Group G] [Finite G] {t : G} {L S : Subgroup G} {x₁ x₂ lam rho tau om : G}

private lemma isMulCommutative_map_of_injective {E : Subgroup G}
    (hE : IsMulCommutative ↥E) (f : G →* G) (hf : Function.Injective f) :
    IsMulCommutative ↥(E.map f) := by
  haveI : IsMulCommutative ↥E := hE
  refine IsMulCommutative.of_comm fun x y => Subtype.ext ?_
  obtain ⟨a, ha, hxa⟩ := Subgroup.mem_map.mp x.2
  obtain ⟨b, hb, hxb⟩ := Subgroup.mem_map.mp y.2
  show (x : G) * (y : G) = (y : G) * (x : G)
  rw [← hxa, ← hxb, ← map_mul, ← map_mul]
  exact congrArg f (congrArg (Subtype.val : ↥E → G)
    (mul_comm' (⟨a, ha⟩ : ↥E) (⟨b, hb⟩ : ↥E)))

private lemma isElemAbelian_map_of_injective {p : ℕ} {E : Subgroup G}
    (hE : CFSG.Open.IsElemAbelian p E) (f : G →* G) (hf : Function.Injective f) :
    CFSG.Open.IsElemAbelian p (E.map f) := by
  refine ⟨isMulCommutative_map_of_injective hE.1 f hf, ?_⟩
  intro x hx
  obtain ⟨a, ha, hxa⟩ := Subgroup.mem_map.mp hx
  rw [← hxa, ← map_pow]
  simpa using congrArg f (hE.2 a ha)

theorem q13d_exists_conj_S (h : Q13Om t L S x₁ x₂ lam rho tau om) (g : G) {D : Subgroup G} (hD :
    IsPGroup 2 ↥D)
    (hDc : D ≤ centralizer ({g * t * g⁻¹} : Set G)) :
    ∃ k : G, ∀ a ∈ D, k * a * k⁻¹ ∈ S := by
  let D' : Subgroup G := D.map (MulAut.conj g⁻¹).toMonoidHom
  have hD'p : IsPGroup 2 D' := by
    change IsPGroup 2 (D.map (MulAut.conj g⁻¹).toMonoidHom)
    exact hD.map (MulAut.conj g⁻¹).toMonoidHom
  have hD'c : D' ≤ invCent t := by
    intro x hx
    obtain ⟨a, ha, rfl⟩ := Subgroup.mem_map.mp hx
    rw [S4A.mem_invCent_iff]
    have hqcomm : a * (g * t * g⁻¹) = (g * t * g⁻¹) * a :=
      Subgroup.mem_centralizer_singleton_iff.mp (hDc ha)
    have hconj : (MulAut.conj g⁻¹) (g * t * g⁻¹) = t := by
      rw [MulAut.conj_apply]; group
    have key : (MulAut.conj g⁻¹) a * t = t * (MulAut.conj g⁻¹) a := by
      have hh := congrArg (MulAut.conj g⁻¹) hqcomm
      simpa only [map_mul, hconj] using hh
    exact key
  obtain ⟨P, hPsylow, hD'P⟩ := exists_isSylowIn_of_le hD'c hD'p
  have hS : IsSylowIn 2 S (invCent t) :=
    ⟨h.c11.le_invCent, h.c11.isPGroup, h.c11.relIndex_odd⟩
  obtain ⟨c, _hcH, hcP⟩ := q13c_sylowIn_conj hS hPsylow
  refine ⟨c⁻¹ * g⁻¹, fun a ha => ?_⟩
  have ha' : (MulAut.conj g⁻¹) a ∈ D' := Subgroup.mem_map.mpr ⟨a, ha, rfl⟩
  have hmem : c⁻¹ * ((MulAut.conj g⁻¹) a) * c ∈ S := (hcP _).mp (hD'P ha')
  have heq : (c⁻¹ * g⁻¹) * a * (c⁻¹ * g⁻¹)⁻¹ = c⁻¹ * ((MulAut.conj g⁻¹) a) * c := by
    rw [MulAut.conj_apply]; group
  rw [heq]; exact hmem

theorem q13d_E16_cent_le (h : Q13Om t L S x₁ x₂ lam rho tau om) {j : G} (hj : ∃ g :
    G, g * t * g⁻¹ = j) {W : Subgroup G}
    (hW : CFSG.Open.IsElemAbelian 2 W) (hWc : Nat.card ↥W = 16)
    (hWj : ∀ w ∈ W, w * j = j * w) {a : G} (haj : a * j = j * a)
    (haW : ∀ w ∈ W, a * w = w * a) (ha2 : IsPGroup 2 ↥(zpowers a ⊔ W)) :
    a ∈ W := by
  obtain ⟨g, hg⟩ := hj
  have hDc : (zpowers a ⊔ W : Subgroup G) ≤ centralizer ({g * t * g⁻¹} : Set G) := by
    rw [hg]
    refine sup_le ?_ ?_
    · exact Subgroup.zpowers_le.mpr (Subgroup.mem_centralizer_singleton_iff.mpr haj)
    · intro w hw
      exact Subgroup.mem_centralizer_singleton_iff.mpr (hWj w hw)
  obtain ⟨k, hk⟩ := q13d_exists_conj_S h g ha2 hDc
  let Y : Subgroup G := W.map (MulAut.conj k).toMonoidHom
  have hYS : Y ≤ S := by
    rintro x ⟨w, hw, rfl⟩
    exact hk w (Subgroup.mem_sup_right hw)
  have hYe : CFSG.Open.IsElemAbelian 2 Y :=
    isElemAbelian_map_of_injective hW (MulAut.conj k).toMonoidHom (MulAut.conj k).injective
  have hYc : Nat.card ↥Y = 16 := by
    change Nat.card ↥(W.map (MulAut.conj k).toMonoidHom) = 16
    rw [Subgroup.card_map_of_injective (MulAut.conj k).injective, hWc]
  have hY : IsE16In S Y := ⟨hYS, hYe, hYc⟩
  have hcent : S ⊓ centralizer (Y : Set G) = Y := (h.c11.l47.1 Y hY).2.2
  have hkaS : (MulAut.conj k) a ∈ S := by
    rw [MulAut.conj_apply]
    exact hk a (Subgroup.mem_sup_left (Subgroup.mem_zpowers a))
  have hkaC : (MulAut.conj k) a ∈ centralizer (Y : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    obtain ⟨w, hw, rfl⟩ := Subgroup.mem_map.mp hy
    change (MulAut.conj k).toMonoidHom w * (MulAut.conj k).toMonoidHom a =
      (MulAut.conj k).toMonoidHom a * (MulAut.conj k).toMonoidHom w
    rw [← map_mul, ← map_mul, haW w hw]
  have hkaY : (MulAut.conj k) a ∈ Y := by
    rw [← hcent]
    exact Subgroup.mem_inf.mpr ⟨hkaS, hkaC⟩
  have hw : (MulAut.conj k).symm ((MulAut.conj k) a) ∈ W :=
    Subgroup.mem_map_equiv.mp hkaY
  have hfin : (MulAut.conj k).symm ((MulAut.conj k) a) = a := by
    rw [MulAut.conj_symm_apply, MulAut.conj_apply]; group
  rwa [hfin] at hw

end CFSG.OddStandard.SmallF3.HarrisU33.S4B
