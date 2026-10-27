module

public import CFSG.LocalAnalysis.AGLEmbedding.SUPairModel
import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.SUThreeTwoShape
public import CFSG.GH74.QTGen4.Leaves.F112.PSU32Model
import all CFSG.GH74.QTGen4.Leaves.F112.PSU32Model

public section

namespace CFSG.AGLEmbedding.SUQ

open CFSG.GH74.QTGen4.Leaves.F112

section Mats

variable {K : Type} [Field K] {ω : K}

theorem mat_G_G (hω : ω ^ 2 = ω + 1) (h2 : (2 : K) = 0) :
    (mG ω : Matrix (Fin 3) (Fin 3) K) * mG ω = mP := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [mG, mP, Matrix.mul_apply, Fin.sum_univ_three] <;> grind

theorem mat_G_F (hω : ω ^ 2 = ω + 1) (h2 : (2 : K) = 0) :
    (mG ω : Matrix (Fin 3) (Fin 3) K) * mF ω = (mF ω * mP) * mG ω := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [mG, mF, mP, Matrix.mul_apply, Fin.sum_univ_three] <;> grind

end Mats

section Group

open CFSG.Open

variable {K : Type} [Field K] (o : OmegaData K)

theorem sG_sq : OmegaData.sG o ^ 2 = OmegaData.sP o := by
  apply su_ext
  simp only [mat_pow, OmegaData.sG, OmegaData.sP, mat_suMk, pow_two]
  exact mat_G_G o.hω o.h2

theorem sG_mul_sF :
    OmegaData.sG o * OmegaData.sF o = OmegaData.sF o * OmegaData.sP o * OmegaData.sG o := by
  apply su_ext
  simp only [mat_mul, OmegaData.sG, OmegaData.sF, OmegaData.sP, mat_suMk]
  exact mat_G_F o.hω o.h2

theorem sF_sq : OmegaData.sF o ^ 2 = OmegaData.sP o :=
  CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.SUThreeTwoShape.sF_sq o

end Group

variable {Y : Type} [Group Y] [Finite Y]

open Subgroup CFSG.ComponentClassification.AS76b
open CFSG.AGLEmbedding.SUPair (Heis27 Heis27.of_card map_oUpperTwo)

theorem sq_conj_S {H : Type*} [Group H] {S D F : H} (hFS : F * S = D * F)
    (hFD : F * D = S ^ 2 * F) (hS : S ^ 3 = 1) : F ^ 2 * S * (F ^ 2)⁻¹ = S⁻¹ := by
  have h1 : F * S * F⁻¹ = D := by rw [hFS]; group
  have h2 : F * D * F⁻¹ = S ^ 2 := by rw [hFD]; group
  have hS2 : S ^ 2 = S⁻¹ := by
    rw [eq_inv_iff_mul_eq_one, ← pow_succ, hS]
  calc F ^ 2 * S * (F ^ 2)⁻¹ = F * (F * S * F⁻¹) * F⁻¹ := by rw [sq]; group
    _ = S⁻¹ := by rw [h1, h2, hS2]

theorem sq_conj_D {H : Type*} [Group H] {S D F : H} (hFS : F * S = D * F)
    (hFD : F * D = S ^ 2 * F) (hD : D ^ 3 = 1) : F ^ 2 * D * (F ^ 2)⁻¹ = D⁻¹ := by
  have h1 : F * S * F⁻¹ = D := by rw [hFS]; group
  have h2 : F * D * F⁻¹ = S ^ 2 := by rw [hFD]; group
  have hD2 : D ^ 2 = D⁻¹ := by
    rw [eq_inv_iff_mul_eq_one, ← pow_succ, hD]
  calc F ^ 2 * D * (F ^ 2)⁻¹ = F * (F * D * F⁻¹) * F⁻¹ := by rw [sq]; group
    _ = F * S ^ 2 * F⁻¹ := by rw [h2]
    _ = (F * S * F⁻¹) ^ 2 := by rw [conj_pow]
    _ = D⁻¹ := by rw [h1, hD2]


open CFSG.GH74.QTGen4.Leaves.F112 CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.SUThreeTwoShape in
theorem exists_qdata_of_su {T : Subgroup Y}
    (h : ∃ (K : Type) (_ : Field K) (_ : Finite K), Nat.card K = 4 ∧
      Nonempty (↥T ≃* ↥(CFSG.Open.StatedSU 3 2 K))) :
    ∃ s d z f g : Y, s ∈ T ∧ d ∈ T ∧ f ∈ T ∧ f ^ 4 = 1 ∧
      f ^ 2 * s * (f ^ 2)⁻¹ = s⁻¹ ∧ f ^ 2 * d * (f ^ 2)⁻¹ = d⁻¹ ∧
      (∀ x ∈ T, z * x = x * z) ∧ Heis27 (oUpperTwo T) (zpowers z) ∧
      s ∈ oUpperTwo T ∧ d ∈ oUpperTwo T ∧ s * d ≠ d * s ∧
      g ∈ T ∧ f ^ 2 ≠ 1 ∧ g ^ 2 = f ^ 2 ∧ g * f * g⁻¹ = f⁻¹ ∧ Nat.card T = 216 := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨K, _, _, hK4, ⟨e⟩⟩ := h
  obtain ⟨ω, hω, h2⟩ := exists_omega hK4
  let o : OmegaData K := ⟨ω, hω, h2⟩
  have hrel : Heis3Rel (OmegaData.sS o) (OmegaData.sD o) (sZ o) :=
    ⟨sZ_central o, sZ_cube o, OmegaData.sS_cube o, OmegaData.sD_cube o, sS_mul_sD o⟩
  have hZ1 := sZ_ne_one o
  have hFS := sF_mul_sS o
  have hFD := sF_mul_sD o
  have hF4 := sF_four o
  have hF2 := sF_sq_ne_one o
  have hcard : Nat.card (SUg K) = 216 := card_SUg hK4
  set ι : SUg K →* Y := T.subtype.comp e.symm.toMonoidHom with hι
  have hιinj : Function.Injective ι := T.subtype_injective.comp e.symm.injective
  have hιT : ∀ x : SUg K, ι x ∈ T := fun x => (e.symm x).2
  have hιsurj : ∀ x ∈ T, ∃ y, ι y = x := fun x hx =>
    ⟨e ⟨x, hx⟩, by simp [hι]⟩
  have hord : orderOf (OmegaData.sF o) = 4 := by
    have := orderOf_eq_prime_pow (p := 2) (n := 1) (x := OmegaData.sF o) (by simpa using hF2)
      (by simpa using hF4)
    simpa using this
  haveI := heisSubgroup_normal hcard hrel hZ1 (hrel.F_mem_normalizer hFS hFD) hord
  have hO : oUpperTwo (⊤ : Subgroup (SUg K)) = heisSubgroup hrel := by
    apply le_antisymm
    · exact (closure_le _).mpr fun x hx => odd_mem_heisSubgroup hcard hrel hZ1 hx.2
    · intro x hx
      refine subset_closure ⟨mem_top x, ?_⟩
      have hdvd : orderOf x ∣ 3 := orderOf_dvd_of_pow_eq_one (hrel.cube_of_mem hx)
      exact (by decide : Odd 3).of_dvd_nat hdvd
  have hTmap : (⊤ : Subgroup (SUg K)).map ι = T := by
    apply le_antisymm
    · rintro _ ⟨x, _, rfl⟩
      exact hιT x
    · intro x hx
      obtain ⟨y, rfl⟩ := hιsurj x hx
      exact mem_map_of_mem ι (mem_top y)
  have hOT : oUpperTwo T = (heisSubgroup hrel).map ι := by
    rw [← hO, map_oUpperTwo, hTmap]
  have hOcard : Nat.card (oUpperTwo T) = 27 := by
    rw [hOT, card_map_of_injective hιinj, card_heisSubgroup hcard hrel hZ1]
  set s := ι (OmegaData.sS o)
  set d := ι (OmegaData.sD o)
  set z := ι (sZ o)
  set f := ι (OmegaData.sF o)
  set g := ι (OmegaData.sG o)
  have hsO : s ∈ oUpperTwo T := hOT ▸ mem_map_of_mem ι hrel.S_mem
  have hdO : d ∈ oUpperTwo T := hOT ▸ mem_map_of_mem ι hrel.D_mem
  have hzO : z ∈ oUpperTwo T := hOT ▸ mem_map_of_mem ι hrel.Z_mem
  have hzc : ∀ x ∈ T, z * x = x * z := by
    intro x hx
    obtain ⟨y, rfl⟩ := hιsurj x hx
    rw [← map_mul, ← map_mul, sZ_central o y]
  have hsd : s * d ≠ d * s := by
    intro h
    apply hrel.S_mul_D_ne hZ1
    apply hιinj
    rw [map_mul, map_mul]
    exact h
  have hz3 : orderOf z = 3 := by
    refine orderOf_eq_prime ?_ ?_
    · rw [← map_pow, sZ_cube o, map_one]
    · intro h
      apply hZ1
      apply hιinj
      rw [map_one]
      exact h
  have hTcard : Nat.card T = 216 := by rw [Nat.card_congr e.toEquiv, hcard]
  have hf2 : f ^ 2 ≠ 1 := by
    intro h1
    apply hF2
    apply hιinj
    rw [map_pow, map_one]
    exact h1
  have hg2 : g ^ 2 = f ^ 2 := by rw [← map_pow, ← map_pow, sG_sq, sF_sq]
  have hgf : g * f * g⁻¹ = f⁻¹ := by
    have h1 : OmegaData.sG o * OmegaData.sF o * (OmegaData.sG o)⁻¹ = (OmegaData.sF o)⁻¹ := by
      rw [sG_mul_sF, ← sF_sq]
      have h4 := hF4
      calc OmegaData.sF o * OmegaData.sF o ^ 2 * OmegaData.sG o * (OmegaData.sG o)⁻¹ =
            OmegaData.sF o ^ 3 := by group
        _ = (OmegaData.sF o)⁻¹ := by
            rw [eq_inv_iff_mul_eq_one, ← pow_succ, h4]
    rw [← map_inv, ← map_mul, ← map_mul, h1, map_inv]
  refine ⟨s, d, z, f, g, hιT _, hιT _, hιT _, by rw [← map_pow, hF4, map_one], ?_, ?_, hzc, ?_,
    hsO, hdO, hsd, hιT _, hf2, hg2, hgf, hTcard⟩
  · rw [← map_pow, ← map_inv, ← map_mul, ← map_mul, sq_conj_S hFS hFD (OmegaData.sS_cube o),
      map_inv]
  · rw [← map_pow, ← map_inv, ← map_mul, ← map_mul, sq_conj_D hFS hFD (OmegaData.sD_cube o),
      map_inv]
  · refine Heis27.of_card hOcard (zpowers_le.mpr hzO) (by rw [Nat.card_zpowers, hz3]) ?_ ?_
      ⟨s, hsO, d, hdO, hsd⟩
    · intro w hw a ha
      obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hw
      have ha' : a ∈ T := oUpperTwo_le_self' ha
      exact ((Commute.zpow_left (hzc a ha') k : Commute (z ^ k) a)).eq
    · intro a ha
      rw [hOT] at ha
      obtain ⟨x, hx, rfl⟩ := ha
      rw [← map_pow, hrel.cube_of_mem hx, map_one]
  where
    oUpperTwo_le_self' {X : Subgroup Y} {a : Y} (ha : a ∈ oUpperTwo X) : a ∈ X :=
      (closure_le _).mpr (fun _ hx => hx.1) ha

section Quat

variable {G₀ : Type} [Group G₀] {f g : G₀}

theorem zpow_eq_of_cast (hf4 : f ^ 4 = 1) {m n : ℤ}
    (h : (m : ZMod (2 * 2)) = (n : ZMod (2 * 2))) : f ^ m = f ^ n := by
  have h4 : f ^ (((2 * 2 : ℕ) : ℤ)) = 1 := by norm_num; exact_mod_cast hf4
  rw [zpow_eq_zpow_emod m h4, zpow_eq_zpow_emod n h4]
  congr 1
  exact (ZMod.intCast_eq_intCast_iff' m n (2 * 2)).mp h

theorem mul_zpow_comm (hgf : g * f * g⁻¹ = f⁻¹) (m : ℤ) : g * f ^ m = f ^ (-m) * g := by
  have h : g * f ^ m * g⁻¹ = f ^ (-m) := by
    rw [← conj_zpow, hgf, inv_zpow']
  calc g * f ^ m = g * f ^ m * g⁻¹ * g := by group
    _ = f ^ (-m) * g := by rw [h]

@[expose] def quatFun (f g : G₀) : QuaternionGroup 2 → G₀
  | .a i => f ^ (i.val : ℤ)
  | .xa i => g * f ^ (i.val : ℤ)

@[expose] def quatHom (hf4 : f ^ 4 = 1) (hg2 : g ^ 2 = f ^ 2) (hgf : g * f * g⁻¹ = f⁻¹) :
    QuaternionGroup 2 →* G₀ where
  toFun := quatFun f g
  map_one' := by
    show quatFun f g (.a 0) = 1
    simp [quatFun]
  map_mul' := by
    have hg2' : g * g = f ^ (2 : ℤ) := by rw [← sq, hg2]; norm_cast
    rintro (i | i) (j | j)
    · show f ^ ((i + j).val : ℤ) = f ^ (i.val : ℤ) * f ^ (j.val : ℤ)
      rw [← zpow_add]
      apply zpow_eq_of_cast hf4
      push_cast; simp only [ZMod.natCast_zmod_val]
    · show g * f ^ ((j - i).val : ℤ) = f ^ (i.val : ℤ) * (g * f ^ (j.val : ℤ))
      rw [← mul_assoc, show f ^ (i.val : ℤ) * g = g * f ^ (-(i.val : ℤ)) by
        rw [mul_zpow_comm hgf, neg_neg], mul_assoc, ← zpow_add]
      congr 1
      apply zpow_eq_of_cast hf4
      push_cast; simp only [ZMod.natCast_zmod_val]; ring
    · show g * f ^ ((i + j).val : ℤ) = g * f ^ (i.val : ℤ) * f ^ (j.val : ℤ)
      rw [mul_assoc, ← zpow_add]
      congr 1
      apply zpow_eq_of_cast hf4
      push_cast; simp only [ZMod.natCast_zmod_val]
    · show f ^ (((2 : ℕ) + j - i : ZMod (2 * 2)).val : ℤ) = g * f ^ (i.val : ℤ) * (g * f ^ (j.val : ℤ))
      rw [show g * f ^ (i.val : ℤ) * (g * f ^ (j.val : ℤ)) =
          (g * f ^ (i.val : ℤ) * g) * f ^ (j.val : ℤ) by group, mul_zpow_comm hgf,
        show f ^ (-(i.val : ℤ)) * g * g = f ^ (-(i.val : ℤ)) * (g * g) by group, hg2',
        ← zpow_add, ← zpow_add]
      apply zpow_eq_of_cast hf4
      push_cast; simp only [ZMod.natCast_zmod_val]; ring

theorem quatHom_a (hf4 : f ^ 4 = 1) (hg2 : g ^ 2 = f ^ 2) (hgf : g * f * g⁻¹ = f⁻¹)
    (i : ZMod (2 * 2)) : quatHom hf4 hg2 hgf (.a i) = f ^ (i.val : ℤ) := rfl

theorem quatHom_xa (hf4 : f ^ 4 = 1) (hg2 : g ^ 2 = f ^ 2) (hgf : g * f * g⁻¹ = f⁻¹)
    (i : ZMod (2 * 2)) : quatHom hf4 hg2 hgf (.xa i) = g * f ^ (i.val : ℤ) := rfl

theorem quatHom_injective (hf4 : f ^ 4 = 1) (hf2 : f ^ 2 ≠ 1) (hg2 : g ^ 2 = f ^ 2)
    (hgf : g * f * g⁻¹ = f⁻¹) : Function.Injective (quatHom hf4 hg2 hgf) := by
  rw [injective_iff_map_eq_one]
  have hord : orderOf f = 4 := by
    have := orderOf_eq_prime_pow (p := 2) (n := 1) (x := f) (by simpa using hf2)
      (by simpa using hf4)
    simpa using this
  rintro (i | i) h
  · rw [quatHom_a] at h
    have hd : ((orderOf f : ℕ) : ℤ) ∣ (i.val : ℤ) := orderOf_dvd_iff_zpow_eq_one.mpr h
    rw [hord] at hd
    have hi : i.val = 0 := by
      have := ZMod.val_lt i
      omega
    rw [(ZMod.val_eq_zero i).mp hi]
    rfl
  · rw [quatHom_xa] at h
    exfalso
    have hgi : g = f ^ (-(i.val : ℤ)) := by
      rw [zpow_neg]; exact eq_inv_of_mul_eq_one_left h
    rw [hgi] at hgf
    have h1 : f = f⁻¹ := by
      rw [← hgf]; group
    apply hf2
    rw [sq]
    nth_rw 2 [h1]
    exact mul_inv_cancel f

end Quat

theorem exists_six_roots {Y : Type} [Group Y] [Finite Y] {T A : Subgroup Y} {f g : Y}
    (hfT : f ∈ T) (hgT : g ∈ T) (hf4 : f ^ 4 = 1) (hf2 : f ^ 2 ≠ 1) (hg2 : g ^ 2 = f ^ 2)
    (hgf : g * f * g⁻¹ = f⁻¹) (hAT : A ≤ T) (hA3 : ∀ a ∈ A, a ^ 3 = 1)
    (hAcard : Nat.card A = 27) (hTcard : Nat.card T = 216) :
    ∃ X : Finset Y, X.card = 6 ∧ (∀ x ∈ X, x ∈ T) ∧ (∀ x ∈ X, x ^ 2 = f ^ 2) ∧
      (∀ x ∈ X, x ^ 4 = 1) ∧ (∀ x ∈ X, ∀ x' ∈ X, x' * x⁻¹ ∈ A → x = x') ∧
      Subgroup.closure ((A : Set Y) ∪ (X : Set Y)) = T := by
  classical
  set φ := quatHom hf4 hg2 hgf with hφdef
  have hφ : Function.Injective φ := quatHom_injective hf4 hf2 hg2 hgf
  set Xq : Finset (QuaternionGroup 2) :=
    {.a 1, .a 3, .xa 0, .xa 1, .xa 2, .xa 3} with hXq
  have hXq6 : Xq.card = 6 := by rw [hXq]; decide
  have hsq : ∀ q ∈ Xq, q ^ 2 = .a 2 := by rw [hXq]; decide
  have h4 : ∀ q : QuaternionGroup 2, q ^ 4 = 1 := by decide
  have hall : ∀ q : QuaternionGroup 2, q = 1 ∨ q = .a 2 ∨ q ∈ Xq := by rw [hXq]; decide
  have hφT : ∀ q, φ q ∈ T := by
    rintro (i | i)
    · rw [hφdef, quatHom_a]; exact zpow_mem hfT _
    · rw [hφdef, quatHom_xa]; exact T.mul_mem hgT (zpow_mem hfT _)
  have hφa2 : φ (.a 2) = f ^ 2 := by
    rw [hφdef, quatHom_a]
    have : ((2 : ZMod (2 * 2)).val : ℤ) = ((2 : ℕ) : ℤ) := rfl
    rw [this, zpow_natCast]
  have hmodA : ∀ q q' : QuaternionGroup 2, φ q' * (φ q)⁻¹ ∈ A → q = q' := by
    intro q q' h
    rw [← map_inv, ← map_mul] at h
    have h3 := hA3 _ h
    have h4' : (φ (q' * q⁻¹)) ^ 4 = 1 := by rw [← map_pow, h4, map_one]
    have h1 : φ (q' * q⁻¹) = 1 := by
      calc φ (q' * q⁻¹) = φ (q' * q⁻¹) ^ 4 * (φ (q' * q⁻¹) ^ 3)⁻¹ := by group
        _ = 1 := by rw [h4', h3]; group
    have := hφ (h1.trans (map_one φ).symm)
    exact (mul_inv_eq_one.mp this).symm
  set X := Xq.image φ with hXdef
  refine ⟨X, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hXdef, Finset.card_image_of_injective _ hφ, hXq6]
  · intro x hx
    obtain ⟨q, -, rfl⟩ := Finset.mem_image.mp hx
    exact hφT q
  · intro x hx
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hx
    rw [← map_pow, hsq q hq, hφa2]
  · intro x hx
    obtain ⟨q, -, rfl⟩ := Finset.mem_image.mp hx
    rw [← map_pow, h4, map_one]
  · intro x hx x' hx' h
    obtain ⟨q, -, rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨q', -, rfl⟩ := Finset.mem_image.mp hx'
    rw [hmodA q q' h]
  · set C := Subgroup.closure ((A : Set Y) ∪ (X : Set Y)) with hC
    have hCT : C ≤ T := (Subgroup.closure_le _).mpr (Set.union_subset hAT fun x hx => by
      obtain ⟨q, -, rfl⟩ := Finset.mem_image.mp hx
      exact hφT q)
    have hAC : A ≤ C := fun a ha => Subgroup.subset_closure (Or.inl ha)
    have hXC : ∀ q ∈ Xq, φ q ∈ C := fun q hq =>
      Subgroup.subset_closure (Or.inr (Finset.mem_image_of_mem φ hq))
    have hφC : ∀ q, φ q ∈ C := by
      intro q
      rcases hall q with rfl | rfl | hq
      · rw [map_one]; exact C.one_mem
      · have : (QuaternionGroup.a 2 : QuaternionGroup 2) = .a 1 ^ 2 := by decide
        rw [this, map_pow]
        exact pow_mem (hXC _ (by rw [hXq]; decide)) 2
      · exact hXC q hq
    let ψ : ↥A × QuaternionGroup 2 → ↥C := fun p => ⟨(p.1 : Y) * φ p.2, C.mul_mem (hAC p.1.2) (hφC p.2)⟩
    have hψ : Function.Injective ψ := by
      rintro ⟨a, q⟩ ⟨a', q'⟩ h
      have h' : (a : Y) * φ q = a' * φ q' := congrArg Subtype.val h
      have hq : q = q' := by
        apply hmodA q q'
        have : φ q' * (φ q)⁻¹ = (a' : Y)⁻¹ * a := by
          calc φ q' * (φ q)⁻¹ = (a' : Y)⁻¹ * (a' * φ q') * (φ q)⁻¹ := by group
            _ = (a' : Y)⁻¹ * (a * φ q) * (φ q)⁻¹ := by rw [h']
            _ = (a' : Y)⁻¹ * a := by group
        rw [this]
        exact A.mul_mem (A.inv_mem a'.2) a.2
      subst hq
      have ha : (a : Y) = a' := mul_right_cancel h'
      rw [Subtype.ext ha]
    have hcard : 216 ≤ Nat.card C := by
      have := Nat.card_le_card_of_injective ψ hψ
      rwa [Nat.card_prod, hAcard, Nat.card_eq_fintype_card (α := QuaternionGroup 2),
        QuaternionGroup.card] at this
    exact eq_of_le_of_card_ge hCT (by rw [hTcard]; exact hcard)

end CFSG.AGLEmbedding.SUQ
