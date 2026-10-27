module

public import CFSG.LocalAnalysis.ComponentClassification.GSThmBCatalog7L4Gamma
public import CFSG.LocalAnalysis.ComponentClassification.Sp4RecPairTwo

public noncomputable section

namespace CFSG.ComponentClassification.GSThmB

namespace Catalog7L4

open CFSG Subgroup Matrix CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial LinearFlag
open CFSG.ComponentClassification.CatFactsL4U4.HBlocks
open CFSG.ComponentClassification.CatFactsL4U4.TBlocks

variable {H : Type} [Group H] [Finite H]

theorem false_of_outer_klein (c : Sp4Rec.Config H) {x : H} (hx2 : x ^ 2 = 1) (hx1 : x ≠ 1)
    (hxb : x ≠ c.b) (hxbc : x * c.b = c.b * x) (hxK : ∀ k ∈ c.K, x * k = k * x)
    (hxKa : ∀ k ∈ conjugate c.K c.a, x * k = k * x) : False := by
  classical
  have hb1 : c.b ≠ 1 := by
    intro h
    have := c.orderOf_b
    rw [h, orderOf_one] at this
    exact absurd this (by norm_num)
  have hxo : orderOf x = 2 := orderOf_eq_prime hx2 hx1
  have hX : IsPGroup 2 (zpowers c.b) := IsPGroup.of_card (n := 1) (by
    rw [Nat.card_zpowers, c.orderOf_b, pow_one])
  have hZ : IsPGroup 2 (zpowers x) := IsPGroup.of_card (n := 1) (by
    rw [Nat.card_zpowers, hxo, pow_one])
  have hc' : ∀ k : ℤ, x * c.b ^ k * x⁻¹ = c.b ^ k := fun k => by
    rw [(Commute.zpow_right hxbc k).eq, mul_inv_cancel_right]
  have hZX : zpowers x ≤ normalizer ((zpowers c.b : Subgroup H) : Set H) := by
    rw [zpowers_le, mem_normalizer_iff]
    intro g
    rw [mem_zpowers_iff, mem_zpowers_iff]
    constructor
    · rintro ⟨k, rfl⟩
      exact ⟨k, (hc' k).symm⟩
    · rintro ⟨k, hk⟩
      refine ⟨k, ?_⟩
      have h2 : x * g * x⁻¹ = x * c.b ^ k * x⁻¹ := by rw [← hk, hc' k]
      exact (mul_left_cancel (mul_right_cancel h2)).symm
  set T := zpowers c.b ⊔ zpowers x with hTdef
  have hT : IsPGroup 2 T := IsPGroup.to_sup_of_normal_left' hX hZ hZX
  have hbK : ∀ k ∈ c.K, c.b * k = k * c.b := fun k hk =>
    (mem_centralizer_singleton_iff.mp (c.K_le hk)).symm
  have hbKa : ∀ k ∈ conjugate c.K c.a, c.b * k = k * c.b := fun k hk =>
    (mem_centralizer_singleton_iff.mp (c.conjugate_K_le hk)).symm
  have hTC : T ≤ centralizer ((c.K ⊔ conjugate c.K c.a : Subgroup H) : Set H) :=
    sup_le (Sp4Rec.le_centralizer_sup' (Sp4Rec.zpowers_le_centralizer hbK)
        (Sp4Rec.zpowers_le_centralizer hbKa))
      (Sp4Rec.le_centralizer_sup' (Sp4Rec.zpowers_le_centralizer hxK)
        (Sp4Rec.zpowers_le_centralizer hxKa))
  have hcard := c.sylow_centralizer T hT hTC
  have : Fintype T := Fintype.ofFinite T
  have hbT : c.b ∈ T := mem_sup_left (mem_zpowers c.b)
  have hxT : x ∈ T := mem_sup_right (mem_zpowers x)
  have h3 : ({1, ⟨c.b, hbT⟩, ⟨x, hxT⟩} : Finset T).card = 3 := by
    rw [Finset.card_eq_three]
    refine ⟨1, ⟨c.b, hbT⟩, ⟨x, hxT⟩, ?_, ?_, ?_, rfl⟩
    · intro h
      exact hb1 (congrArg Subtype.val h).symm
    · intro h
      exact hx1 (congrArg Subtype.val h).symm
    · intro h
      exact hxb (congrArg Subtype.val h).symm
  have h4 := Finset.card_le_univ ({1, ⟨c.b, hbT⟩, ⟨x, hxT⟩} : Finset T)
  rw [h3, ← Nat.card_eq_fintype_card] at h4
  omega

theorem mul_conj_mul_inv {P : Type*} [Group P] (α : MulAut P) (z : P) :
    α * MulAut.conj z * α⁻¹ = MulAut.conj (α z) := by
  ext t
  simp only [MulAut.mul_apply, MulAut.conj_apply, map_mul, map_inv, MulAut.apply_inv_self]

theorem false_of_graph [(generalizedFitting H).Normal]
    (c : Sp4Rec.Config H) {k : Type} [Field k]
    [Finite k] (φ : ↥(generalizedFitting H) ≃* projectiveSL 4 k)
    {ρ : H →* MulAut (projectiveSL 4 k)} (hinj : Function.Injective ρ)
    (hρW : ∀ w : ↥(generalizedFitting H), ρ w = MulAut.conj (φ w))
    (hρg : ∀ (g : H) (w : ↥(generalizedFitting H)), ρ g (φ w) = φ (MulAut.conjNormal g w))
    {g₀ : SpecialLinearGroup (Fin 4) k} {b : k} (hb : b ≠ 0) (hb4 : b ^ 4 = 1)
    (hg₀ : (g₀ : Matrix (Fin 4) (Fin 4) k) = X1 b)
    (hφb : φ ⟨c.b, c.b_mem_G⟩ = proj 4 k g₀)
    (hfac : ((c.K.subgroupOf (generalizedFitting H)).map φ.toMonoidHom = factorL k ∧
        ((conjugate c.K c.a).subgroupOf (generalizedFitting H)).map φ.toMonoidHom = factorR k) ∨
      ((c.K.subgroupOf (generalizedFitting H)).map φ.toMonoidHom = factorR k ∧
        ((conjugate c.K c.a).subgroupOf (generalizedFitting H)).map φ.toMonoidHom = factorL k))
    {B : GL (Fin 4) k} (hρa : ρ c.a = conjAut 4 k B * dualAut 4 k)
    (hB : (B : Matrix (Fin 4) (Fin 4) k)ᵀ = B ∨ (B : Matrix (Fin 4) (Fin 4) k)ᵀ = -B) :
    False := by
  classical
  set KP := (c.K.subgroupOf (generalizedFitting H)).map φ.toMonoidHom with hKP
  set KaP := ((conjugate c.K c.a).subgroupOf (generalizedFitting H)).map φ.toMonoidHom with hKaP
  have ha2 : c.a * c.a = 1 := by rw [← pow_two, ← c.orderOf_a, pow_orderOf_eq_one]
  have hmapK : ∀ y ∈ KP, ρ c.a y ∈ KaP := by
    rintro _ ⟨w, hw, rfl⟩
    rw [MulEquiv.coe_toMonoidHom, hρg]
    refine ⟨MulAut.conjNormal c.a w, ?_, rfl⟩
    rw [SetLike.mem_coe, mem_subgroupOf, Sp4Rec.mem_conjugate_iff]
    have hw' : (w : H) ∈ c.K := mem_subgroupOf.mp (SetLike.mem_coe.mp hw)
    have e : c.a * ((MulAut.conjNormal c.a w : generalizedFitting H) : H) * c.a⁻¹ = w := by
      change c.a * (c.a * (w : H) * c.a⁻¹) * c.a⁻¹ = w
      have hai : c.a⁻¹ = c.a := inv_eq_of_mul_eq_one_right ha2
      rw [hai, ← mul_assoc, ← mul_assoc, ha2, one_mul, mul_assoc, ha2, mul_one]
    rw [e]
    exact hw'
  have hmapKa : ∀ y ∈ KaP, ρ c.a y ∈ KP := by
    rintro _ ⟨w, hw, rfl⟩
    rw [MulEquiv.coe_toMonoidHom, hρg]
    refine ⟨MulAut.conjNormal c.a w, ?_, rfl⟩
    rw [SetLike.mem_coe, mem_subgroupOf]
    exact Sp4Rec.mem_conjugate_iff.mp (mem_subgroupOf.mp (SetLike.mem_coe.mp hw))
  have hLR : ∀ y ∈ factorL k, ρ c.a y ∈ factorR k := by
    rcases hfac with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · intro y hy
      rw [← h1] at hy
      rw [← h2]
      exact hmapK y hy
    · intro y hy
      rw [← h2] at hy
      rw [← h1]
      exact hmapKa y hy
  have hRL : ∀ y ∈ factorR k, ρ c.a y ∈ factorL k := by
    rcases hfac with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · intro y hy
      rw [← h2] at hy
      rw [← h1]
      exact hmapKa y hy
    · intro y hy
      rw [← h1] at hy
      rw [← h2]
      exact hmapK y hy
  rw [hρa] at hLR hRL
  obtain ⟨u00, u01, u10, u11⟩ := ul_eq_zero_of_swap (hLR _ ⟨uuSL 1, rfl⟩) (hLR _ ⟨llSL 1, rfl⟩)
  obtain ⟨l22, l23, l32, l33⟩ := lr_eq_zero_of_swap (hRL _ ⟨uuSL 1, rfl⟩) (hRL _ ⟨llSL 1, rfl⟩)
  set Bm := (B : Matrix (Fin 4) (Fin 4) k) with hBm
  set d := Bm 0 2 * Bm 1 3 - Bm 0 3 * Bm 1 2 with hd
  have hdetB : Bm.det = d ^ 2 := by
    rw [det_antiblock u00 u01 u10 u11 l22 l23 l32 l33, antiblock_det_eq hB, pow_two]
  have hd0 : d ≠ 0 := by
    intro h0
    apply det_ne_zero_GL B
    rw [hdetB, h0]
    ring
  set γ := conjAut 4 k (gramGL hd0) * dualAut 4 k with hγ
  obtain ⟨y, hy⟩ := graph_gram_mem_coset hd0 hdetB
  set w := φ.symm y with hw
  set x := c.a * (w : H) with hx
  have hρx : ρ x = γ := by
    rw [hx, map_mul, hρW, hw, MulEquiv.apply_symm_apply, hy, hρa, mul_inv_cancel_left]
  have hx2 : x ^ 2 = 1 := by
    apply hinj
    rw [map_pow, hρx, map_one, hγ]
    exact graph_gram_sq hd0
  have hxG : x ∉ generalizedFitting H := by
    intro hxG
    have h1 : γ ∈ semilinearAutGroup 4 k := by
      rw [← hρx, show x = ((⟨x, hxG⟩ : generalizedFitting H) : H) from rfl, hρW]
      obtain ⟨z, hz⟩ := proj_surjective 4 k (φ ⟨x, hxG⟩)
      rw [← hz, ← LinearFlag.conjAut_toGL]
      exact linearAutGroup_le_semilinearAutGroup (conjAut_mem_linearAutGroup _)
    apply ProjectivePlane.dualAut_not_mem_semilinearAutGroup (K := k) (n := 4) (by norm_num)
    have h2 : dualAut 4 k = (conjAut 4 k (gramGL hd0))⁻¹ * γ := by
      rw [hγ, inv_mul_cancel_left]
    rw [h2]
    exact mul_mem (inv_mem (linearAutGroup_le_semilinearAutGroup
      (conjAut_mem_linearAutGroup _))) h1
  have hx1 : x ≠ 1 := fun h => hxG (h ▸ one_mem _)
  have hxb : x ≠ c.b := fun h => hxG (h ▸ c.b_mem_G)
  have hfixF : ∀ z ∈ factorL k ⊔ factorR k, z ∈ factorL k ∨ z ∈ factorR k → γ z = z := by
    rintro z - (⟨U, rfl⟩ | ⟨W, rfl⟩)
    · exact graph_gram_fixes_bdL hd0 U
    · exact graph_gram_fixes_bdR hd0 W
  have hcomm_of_fix : ∀ g : generalizedFitting H, γ (φ g) = φ g →
      x * (g : H) = (g : H) * x := by
    intro g hg
    have h1 : ρ (x * (g : H) * x⁻¹) = ρ g := by
      rw [map_mul, map_mul, map_inv, hρx, hρW, mul_conj_mul_inv, hg]
    have h2 := hinj h1
    calc x * (g : H) = x * (g : H) * x⁻¹ * x := by group
      _ = (g : H) * x := by rw [h2]
  have hxbc : x * c.b = c.b * x := by
    have := hcomm_of_fix ⟨c.b, c.b_mem_G⟩ (by rw [hφb]; exact graph_gram_fixes_X1 hd0 hb hb4 hg₀)
    exact this
  have hKfix : ∀ g : generalizedFitting H, φ g ∈ factorL k ∨ φ g ∈ factorR k →
      γ (φ g) = φ g := fun g hg =>
    hfixF _ (hg.elim (fun h => mem_sup_left h) (fun h => mem_sup_right h)) hg
  have hKF : ∀ g : generalizedFitting H, (g : H) ∈ c.K → φ g ∈ factorL k ∨ φ g ∈ factorR k := by
    intro g hg
    have hmem : φ g ∈ KP := ⟨g, mem_subgroupOf.mpr hg, rfl⟩
    rcases hfac with ⟨h1, -⟩ | ⟨h1, -⟩
    · exact Or.inl (h1 ▸ hmem)
    · exact Or.inr (h1 ▸ hmem)
  have hKaF : ∀ g : generalizedFitting H, (g : H) ∈ conjugate c.K c.a →
      φ g ∈ factorL k ∨ φ g ∈ factorR k := by
    intro g hg
    have hmem : φ g ∈ KaP := ⟨g, mem_subgroupOf.mpr hg, rfl⟩
    rcases hfac with ⟨-, h2⟩ | ⟨-, h2⟩
    · exact Or.inr (h2 ▸ hmem)
    · exact Or.inl (h2 ▸ hmem)
  refine false_of_outer_klein c hx2 hx1 hxb hxbc (fun g hg => ?_) (fun g hg => ?_)
  · exact hcomm_of_fix ⟨g, c.K_le_G hg⟩ (hKfix _ (hKF ⟨g, c.K_le_G hg⟩ hg))
  · exact hcomm_of_fix ⟨g, c.conjugate_K_le_G hg⟩ (hKfix _ (hKaF ⟨g, c.conjugate_K_le_G hg⟩ hg))

end Catalog7L4

end CFSG.ComponentClassification.GSThmB
