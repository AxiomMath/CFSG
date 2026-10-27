module

public import CFSG.LargeExtraspecial.S13TwoI
public import CFSG.LargeExtraspecial.S13TwoH

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.S13

open Subgroup Module QuadraticMap CFSG.RankThree.OrthogonalInvolutions
open CFSG.LargeExtraspecial.S4 CFSG.LargeExtraspecial.S6 CFSG.LargeExtraspecial.S10

variable {G : Type*} [Group G] [Finite G] {S : Setting G} {g g₁ : G} {K : Subgroup S.O}

section Four

variable (Y : Hyp13 S g K) {h : S.M} (hg : g₁ = (h : G) * g)
  (hperp : ∀ u ∈ Fbar S g K, ∀ v ∈ Fbar S g₁ K, polar S.q u v = 0)
  (hne : Fbar S g₁ K ≠ Fbar S g K) (hbot : Ebar S g K ⊓ Ebar S g₁ K = ⊥)
include Y hg hperp hne hbot

omit hne in
theorem comm_T₀_T₁ {x y : S.O}
    (hx : x ∈ Ebar S g K ⊓ ptStab S (Fbar S g K ⊔ Fbar S g₁ K))
    (hy : y ∈ Ebar S g₁ K ⊓ ptStab S (Fbar S g K ⊔ Fbar S g₁ K)) : x * y = y * x := by
  have Y₁ : Hyp13 S g₁ K := Y.mul hg
  have hg' : g = ((h⁻¹ : S.M) : G) * g₁ := by rw [hg, Subgroup.coe_inv]; group
  have hperp' : ∀ u ∈ Fbar S g₁ K, ∀ v ∈ Fbar S g K, polar S.q u v = 0 := fun u hu v hv => by
    rw [QuadraticMap.polar_comm]; exact hperp v hv u hu
  have hxM : x ∈ S.Mbar := Hyp13.Ebar_le_Mbar (Subgroup.mem_inf.mp hx).1
  have hyM : y ∈ S.Mbar := Hyp13.Ebar_le_Mbar (Subgroup.mem_inf.mp hy).1
  have h1 : ∀ e ∈ Ebar S g₁ K, x * e * x⁻¹ ∈ Ebar S g₁ K := fun e he =>
    conj_mem_Ebar₁ Y hg hxM (Subgroup.mem_inf.mp hx).2 he
  have hy' : y ∈ ptStab S (Fbar S g₁ K ⊔ Fbar S g K) := by
    rw [sup_comm]; exact (Subgroup.mem_inf.mp hy).2
  have h2 : ∀ e ∈ Ebar S g K, y * e * y⁻¹ ∈ Ebar S g K := fun e he =>
    conj_mem_Ebar₁ Y₁ hg' hyM hy' he
  have hc : x * y * x⁻¹ * y⁻¹ ∈ Ebar S g K ⊓ Ebar S g₁ K := by
    refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
    · have e : x * y * x⁻¹ * y⁻¹ = x * (y * x⁻¹ * y⁻¹) := by group
      rw [e]
      exact mul_mem (Subgroup.mem_inf.mp hx).1 (h2 _ (inv_mem (Subgroup.mem_inf.mp hx).1))
    · exact mul_mem (h1 _ (Subgroup.mem_inf.mp hy).1) (inv_mem (Subgroup.mem_inf.mp hy).1)
  rw [hbot, mem_bot] at hc
  calc x * y = x * y * x⁻¹ * y⁻¹ * (y * x) := by group
    _ = y * x := by rw [hc, one_mul]

theorem exists_comm_eq {x : S.O} (hxE : x ∈ Ebar S g K)
    (hxT : x ∉ Ebar S g K ⊓ ptStab S (Fbar S g K ⊔ Fbar S g₁ K)) {w : S.O}
    (hw : w ∈ Ebar S g K ⊓ ptStab S (Fbar S g K ⊔ Fbar S g₁ K)) :
    ∃ y ∈ Ebar S g₁ K ⊓ ptStab S (Fbar S g K ⊔ Fbar S g₁ K), x * y * x⁻¹ * y⁻¹ = w := by
  set D := Fbar S g K ⊔ Fbar S g₁ K with hD
  set T₀ := Ebar S g K ⊓ ptStab S D with hT₀
  set T₁ := Ebar S g₁ K ⊓ ptStab S D with hT₁
  have Y₁ : Hyp13 S g₁ K := Y.mul hg
  have hg' : g = ((h⁻¹ : S.M) : G) * g₁ := by rw [hg, Subgroup.coe_inv]; group
  have hperp' : ∀ u ∈ Fbar S g₁ K, ∀ v ∈ Fbar S g K, polar S.q u v = 0 := fun u hu v hv => by
    rw [QuadraticMap.polar_comm]; exact hperp v hv u hu
  have hne' : Fbar S g K ≠ Fbar S g₁ K := fun e => hne e.symm
  have hD' : (Fbar S g₁ K ⊔ Fbar S g K : Submodule (ZMod 2) S.Qt) = D := sup_comm _ _
  have hyE : ∀ y ∈ T₁, ∀ e ∈ Ebar S g K, y * e * y⁻¹ ∈ Ebar S g K := by
    intro y hy e he
    have hy' : y ∈ ptStab S (Fbar S g₁ K ⊔ Fbar S g K) := by
      rw [hD']; exact (Subgroup.mem_inf.mp hy).2
    exact conj_mem_Ebar₁ Y₁ hg' (Hyp13.Ebar_le_Mbar (Subgroup.mem_inf.mp hy).1) hy' he
  have hxD := Ebar_le_stab2 Y hperp hxE
  rw [mem_stab2] at hxD
  have hmem : ∀ y ∈ T₁, x * y * x⁻¹ * y⁻¹ ∈ T₀ := by
    intro y hy
    obtain ⟨hy1, hy2⟩ := Subgroup.mem_inf.mp hy
    refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
    · have e : x * y * x⁻¹ * y⁻¹ = x * (y * x⁻¹ * y⁻¹) := by group
      rw [e]
      exact mul_mem hxE (hyE y hy _ (inv_mem hxE))
    · intro d hd
      have hy2' : ∀ d ∈ D, ((y⁻¹ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) d = d := fun d hd =>
        (inv_mem hy2 : y⁻¹ ∈ ptStab S D) d hd
      simp only [Subgroup.coe_mul, LinearEquiv.mul_apply]
      rw [hy2' d hd, hy2 _ (hxD.2.1 d hd)]
      exact apply_inv_apply_O x d
  have hcT : ∀ c ∈ T₀, ∀ a ∈ T₁, a * c = c * a := fun c hc a ha =>
    (comm_T₀_T₁ Y hg hperp hbot hc ha).symm
  let φ : T₁ →* T₀ := MonoidHom.mk'
    (fun y => ⟨x * (y : S.O) * x⁻¹ * (y : S.O)⁻¹, hmem y y.2⟩) (by
    rintro ⟨a, ha⟩ ⟨b, hb⟩
    apply Subtype.ext
    simp only [Subgroup.coe_mul]
    have hb' := hcT _ (hmem b hb) a ha
    calc x * (a * b) * x⁻¹ * (a * b)⁻¹
        = x * a * x⁻¹ * a⁻¹ * (a * (x * b * x⁻¹ * b⁻¹)) * a⁻¹ := by group
      _ = x * a * x⁻¹ * a⁻¹ * ((x * b * x⁻¹ * b⁻¹) * a) * a⁻¹ := by rw [hb']
      _ = x * a * x⁻¹ * a⁻¹ * (x * b * x⁻¹ * b⁻¹) := by group)
  have hinj : Function.Injective φ := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro y hy
    rw [MonoidHom.mem_ker] at hy
    have hy1 : x * (y : S.O) * x⁻¹ * (y : S.O)⁻¹ = 1 := congrArg Subtype.val hy
    have hxy : x * (y : S.O) = y * x := by
      calc x * (y : S.O) = x * y * x⁻¹ * (y : S.O)⁻¹ * (y * x) := by group
        _ = y * x := by rw [hy1, one_mul]
    have hcE : ∀ e ∈ Ebar S g K, (y : S.O) * e = e * y := by
      intro e he
      by_cases heT : e ∈ T₀
      · exact hcT e heT y y.2
      · have hex := mul_mem_of_card_eq_two_mul inf_le_left (card_Ebar_eq_two_mul Y hg hperp hne)
          he hxE heT hxT
        have h1 := hcT _ hex y y.2
        calc (y : S.O) * e = (y : S.O) * (e * x) * x⁻¹ := by group
          _ = e * x * y * x⁻¹ := by rw [h1]
          _ = e * (x * y) * x⁻¹ := by group
          _ = e * (y * x) * x⁻¹ := by rw [hxy]
          _ = e * y := by group
    have hyE1 := (Subgroup.mem_inf.mp y.2).1
    rw [Ebar_mul Y.normal hg, mem_map_cK_iff] at hyE1
    have hρ : S.ρ h ∈ S.Mbar := MonoidHom.mem_range.mpr ⟨h, rfl⟩
    have key := Y.mem_Ebar_of_conj_mem hyE1 hρ (fun e he => by
      have e1 : S.ρ h * ((S.ρ h)⁻¹ * (y : S.O) * S.ρ h) * (S.ρ h)⁻¹ = y := by group
      rw [e1]
      exact hcE e he)
    have e1 : S.ρ h * ((S.ρ h)⁻¹ * (y : S.O) * S.ρ h) * (S.ρ h)⁻¹ = y := by group
    rw [e1] at key
    have hyb : (y : S.O) ∈ Ebar S g K ⊓ Ebar S g₁ K :=
      Subgroup.mem_inf.mpr ⟨key, (Subgroup.mem_inf.mp y.2).1⟩
    rw [hbot, mem_bot] at hyb
    exact (mem_bot).mpr (Subtype.ext hyb)
  have hcard : Nat.card T₁ = Nat.card T₀ := by
    have h1 := card_Ebar_eq_two_mul Y hg hperp hne
    rw [← hD, ← hT₀] at h1
    have h2 := card_Ebar_eq_two_mul Y₁ hg' hperp' hne'
    rw [hD', ← hT₁] at h2
    have h3 : Nat.card (Ebar S g₁ K) = Nat.card (Ebar S g K) := by
      rw [Y₁.card_Ebar, Y.card_Ebar]
    omega
  obtain ⟨y, hy⟩ := ((Nat.bijective_iff_injective_and_card φ).mpr ⟨hinj, hcard⟩).2 ⟨w, hw⟩
  exact ⟨y, y.2, congrArg Subtype.val hy⟩

end Four

end CFSG.LargeExtraspecial.S13
