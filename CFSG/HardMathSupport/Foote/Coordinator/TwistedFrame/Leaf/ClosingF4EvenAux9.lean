module

public import CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame.Leaf.ClosingF4EvenAux8

public noncomputable section

namespace CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame.F4Even

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.SeitzReduction
open CFSG.HardMathSupport.Foote.Coordinator.SplitFrame CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.Heis
open CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.DetectF4

set_option linter.unusedSectionVars false


section Core

open T7

variable {L : Type} [Field L] [CharP L 2] {Fr : L →+* L} {H : Subgroup (ModGL Tag.F4 L)}

theorem w_z0122 : wF4 • z0122 = v0100n := by rw [w_smul_eq]; decide +kernel
theorem w_v0100n : wF4 • v0100n = z0122 := by rw [w_smul_eq]; decide +kernel

theorem sig_n {d₃ d₅ : L} (h35 : Fr d₃ = d₅) (h53 : Fr d₅ = d₃) :
    sigHom Fr (pinnedX Tag.F4 L z0122 d₃ * pinnedX Tag.F4 L v0100n d₅) =
      pinnedX Tag.F4 L z0122 d₃ * pinnedX Tag.F4 L v0100n d₅ := by
  rw [map_mul, sigHom_pinnedX Fr (mem_rootFinset.1 z0122_root),
    sigHom_pinnedX Fr (mem_rootFinset.1 v0100n_root), w_z0122, w_v0100n, h35, h53]
  exact (R5_commute v0100n (by simp [R5]) z0122 (by simp [R5]) d₅ d₃).eq

theorem isW_A3 (E : Elts Fr H) (AD : ActData L) {d₃ d₅ : L} (h35 : Fr d₃ = d₅) (h53 : Fr d₅ = d₃)
    (hn : pinnedX Tag.F4 L z0122 d₃ * pinnedX Tag.F4 L v0100n d₅ ∈ H) {b₀ : L}
    (hb : IsW Fr H (fv Fr rS b₀)) : IsW Fr H (fv Fr rA3 (d₃ * b₀)) := by
  have hA : HasAct (pinnedX Tag.F4 L z0122 d₃ * pinnedX Tag.F4 L v0100n d₅)
      (actFun AD.a1 AD.a2 z0122 d₃ ∘ actFun AD.a1 AD.a2 v0100n d₅) :=
    (AD.hact z0122 z0122_root z0122_deg d₃).mul (AD.hact v0100n v0100n_root v0100n_deg d₅)
  have h := (hb.act hn (sig_n h35 h53) hA).add hb.neg
  convert h using 1
  simp only [Function.comp_apply, A_v_S AD, A_z_S AD]
  unfold fv
  rw [w_rA3, map_mul, h35]
  abel

theorem isW_fv_S (E : Elts Fr H) (hsurj : ∀ n : L, ∃ z, z + Fr z = n) {l : L} (hl : InE Fr l) :
    IsW Fr H (fv Fr rS l) := by
  obtain ⟨z, hz⟩ := hsurj (l * Fr l)
  obtain ⟨hq, hc⟩ := heisCoord_r (Fr := Fr) l z
  exact ⟨_, E.er l z hl hz, hq, sig_r hl hz, hc⟩

theorem core (AD : ActData L) (E : Elts Fr H) (hsurj : ∀ n : L, ∃ z, z + Fr z = n)
    (hζ : ∃ ζ : L, Fr ζ = ζ ∧ ζ ≠ 0 ∧ ζ ≠ 1)
    (hM : ∃ q ∈ H, q ∈ Qθ Tag.F4 L ∧ sigHom Fr q = q ∧
      ((crd (heisCoord Tag.F4 L q)).a1 ≠ 0 ∨ (crd (heisCoord Tag.F4 L q)).a2 ≠ 0 ∨
        (crd (heisCoord Tag.F4 L q)).a3 ≠ 0 ∨ (crd (heisCoord Tag.F4 L q)).b12 ≠ 0 ∨
        (crd (heisCoord Tag.F4 L q)).b13 ≠ 0 ∨ (crd (heisCoord Tag.F4 L q)).b23 ≠ 0)) :
    ∀ q ∈ Qθ Tag.F4 L, sigHom Fr q = q → q ∈ H := by
  obtain ⟨ζ, hζf, hζ0, hζ1⟩ := hζ
  obtain ⟨c, hc⟩ := hsurj 1
  have hP := pcl_Pset AD E
  obtain ⟨q₀, hq₀H, hq₀Q, hq₀s, hne⟩ := hM
  have hx : crd (heisCoord Tag.F4 L q₀) ∈ Pset Fr H :=
    ⟨heisCoord Tag.F4 L q₀, ⟨q₀, hq₀H, hq₀Q, hq₀s, rfl⟩, rfl⟩
  obtain ⟨z, hzP, hzs, hza1, hza2, hza3, hzne⟩ :=
    soc_of_ne hP hζf hζ0 hζ1 hc hx hne
  obtain ⟨l₀, hl₀, hl₀P⟩ := b23_of_soc hP hc hzP hzs hza1 hza2 hza3 hzne
  have hl₀E : InE Fr l₀ := by
    obtain ⟨u, hu, hcrd⟩ := hl₀P
    have := (crd_E (fun ν => hu.sf ν)).2.2.2.2.2.2
    rw [hcrd] at this
    exact this
  have hζE : InE Fr ζ := InE.of_fixed hζf
  have hl₀W := isW_fv_B23 hl₀E hl₀P
  have hl₁P : (⟨0, 0, 0, 0, 0, 0, ζ * l₀⟩ : T7 L) ∈ Pset Fr H := by
    have := hP.smul ζ hζf _ hl₀P
    convert this using 1
    ext <;> simp
  have hl₁E : InE Fr (ζ * l₀) := hζE.mul hl₀E
  have hl₁W := isW_fv_B23 hl₁E hl₁P
  have hv1 := vA_mem E hl₀E hl₀W
  have hv2 := vA_mem E hl₁E hl₁W
  rw [map_mul, hζf] at hv2
  have hn := stepD_mem E (t := 1) hl₀E hζf hζ0 (map_one Fr) hv1 hv2
  have hFF : Fr (Fr l₀) = l₀ := hl₀E
  have h35 : Fr ((Fr l₀) ^ 2 * 1 - (ζ * Fr l₀) ^ 2 * (ζ⁻¹ * 1)) =
      l₀ ^ 2 * 1 - (ζ * l₀) ^ 2 * (ζ⁻¹ * 1) := by
    simp only [map_sub, map_mul, map_pow, map_inv₀, map_one, hζf, hFF]
  have h53 : Fr (l₀ ^ 2 * 1 - (ζ * l₀) ^ 2 * (ζ⁻¹ * 1)) =
      (Fr l₀) ^ 2 * 1 - (ζ * Fr l₀) ^ 2 * (ζ⁻¹ * 1) := by
    simp only [map_sub, map_mul, map_pow, map_inv₀, map_one, hζf]
  have hd3 : (Fr l₀) ^ 2 * 1 - (ζ * Fr l₀) ^ 2 * (ζ⁻¹ * 1) ≠ 0 := by
    have e : (Fr l₀) ^ 2 * 1 - (ζ * Fr l₀) ^ 2 * (ζ⁻¹ * 1) = (Fr l₀) ^ 2 * (1 - ζ) := by
      field_simp
    rw [e]
    refine mul_ne_zero (pow_ne_zero 2 ((map_ne_zero Fr).2 hl₀)) (sub_ne_zero.2 (Ne.symm hζ1))
  have hd3E : InE Fr ((Fr l₀) ^ 2 * 1 - (ζ * Fr l₀) ^ 2 * (ζ⁻¹ * 1)) := by
    unfold InE
    rw [h35, h53]
  have hS : ∀ l, InE Fr l → (⟨l, 0, 0, 0, 0, 0, 0⟩ : T7 L) ∈ Pset Fr H :=
    fun l hl => ⟨fv Fr rS l, isW_fv_S E hsurj hl, crd_fv_rS l⟩
  have hA3 : ∀ l, InE Fr l → (⟨0, 0, 0, l, 0, 0, 0⟩ : T7 L) ∈ Pset Fr H := by
    intro l hl
    have hb := isW_fv_S E hsurj (hl.div hd3E)
    have hW := isW_A3 E AD h35 h53 hn hb
    rw [mul_div_cancel₀ _ hd3] at hW
    exact ⟨fv Fr rA3 l, hW, crd_fv_rA3 l⟩
  have hall := all_of_A3 hP hζf hζ0 hζ1 hc hS hA3
  intro q hq hqs
  have hsf : ∀ ν, heisCoord Tag.F4 L q ν = Fr (heisCoord Tag.F4 L q (wF4⁻¹ • ν)) := by
    intro ν
    have h1 := (sig_Qθ Fr q hq).2
    rw [hqs] at h1
    exact congrFun h1 ν
  have hsupp : Supp (heisCoord Tag.F4 L q) := fun ν hν => (heisCoord_spec Tag.F4 L).support q hq ν hν
  obtain ⟨hE0, hE1, hE2, hE3, hE4, hE5, hE6⟩ := crd_E hsf
  obtain ⟨u, hu, hcrd⟩ := hall (crd (heisCoord Tag.F4 L q)) hE0 hE1 hE2 hE3 hE4 hE5 hE6
  have hueq : u = heisCoord Tag.F4 L q :=
    eq_of_crd (Fr := Fr) (fun ν hν => hu.supp hν) hsupp (fun ν => hu.sf ν) hsf hcrd
  rw [hueq] at hu
  exact mem_of_isW E.eth hu hq hqs rfl

end Core

end CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame.F4Even
