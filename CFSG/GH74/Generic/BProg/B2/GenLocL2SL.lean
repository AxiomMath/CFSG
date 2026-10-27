module

public import CFSG.GH74.Generic.BProg.B2.GenLocL2
public import CFSG.GH74.GLS.IVK.Lifted.SL2Aut
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherFactsL2Cover

public section

namespace CFSG.GH74.Generic.BProg.B2

open CFSG CFSG.GH74 Subgroup CFSG.Blueprint CFSG.GorensteinWalter CFSG.ComponentClassification.AutL2Facts
open scoped MatrixGroups

namespace GenLocL2SL

section Key

variable {K : Type} [Field K] [Finite K]

theorem mk_apply_eq_semilinear (hodd : Odd (Nat.card K)) (h3 : 3 < Nat.card K)
    (φ : MulAut (SL(2, K))) (y : SL(2, K)) :
    QuotientGroup.mk' (Subgroup.center SL(2, K)) (φ y) =
      CFSG.ComponentClassification.CatalogueSchreierLinearTwo.semilinearAction K
        (GLS.IVK.Lifted.gammaOf hodd h3 φ) (QuotientGroup.mk' _ y) := by
  have h1 := GLS.IVK.Lifted.thetaEquiv_gammaOf hodd h3 φ
  rw [← ABGLocalTools.psl2MulAutOf_mk, ← h1]
  show _ = _
  rw [CFSG.ComponentClassification.CatalogueSchreierLinearTwo.semilinearAction_eq_native K
    (ABGLocalTools.isOddPrimePower_card_of_odd hodd) h3]
  rfl

end Key

section Lift

variable {K : Type} [Field K]

theorem eq_of_mk_eq_of_odd {y : SL(2, K)} (hy : Odd (orderOf y)) (φ : MulAut SL(2, K))
    (h : QuotientGroup.mk' (Subgroup.center SL(2, K)) (φ y) = QuotientGroup.mk' _ y) :
    φ y = y := by
  have hz : y⁻¹ * φ y ∈ Subgroup.center SL(2, K) := QuotientGroup.eq.1 h.symm
  set z := y⁻¹ * φ y with hzdef
  have hyz : φ y = y * z := by rw [hzdef]; group
  have hcomm : Commute y z := Subgroup.mem_center_iff.1 hz y
  have hz2 : z * z = 1 := GLS.IVK.Lifted.sq_eq_one_of_mem_center_sl2 hz
  obtain ⟨k, hk⟩ := hy
  have h1 : (φ y) ^ (2 * k + 1) = 1 := by
    rw [← map_pow, ← hk, pow_orderOf_eq_one, map_one]
  rw [hyz, hcomm.mul_pow, ← hk, pow_orderOf_eq_one, one_mul] at h1
  have hzk : z ^ (2 * k + 1) = z := by
    rw [pow_succ, pow_mul, pow_two, hz2, one_pow, one_mul]
  rw [hk, hzk] at h1
  rw [hyz, h1, mul_one]

theorem conj_fix_of_mem_zpowers {s y : SL(2, K)} {n : ℤ}
    (h : QuotientGroup.mk' (Subgroup.center SL(2, K)) s =
      QuotientGroup.mk' (Subgroup.center SL(2, K)) (y ^ n)) :
    MulAut.conj s y = y := by
  have hw : (y ^ n)⁻¹ * s ∈ Subgroup.center SL(2, K) := QuotientGroup.eq.1 h.symm
  set w := (y ^ n)⁻¹ * s with hwdef
  have hs : s = y ^ n * w := by rw [hwdef]; group
  have hcomm : Commute w y := (Subgroup.mem_center_iff.1 hw y).symm
  rw [MulAut.conj_apply, hs]
  have h1 : Commute (y ^ n) y := Commute.zpow_left (Commute.refl y) n
  have h2 : Commute (y ^ n * w) y := h1.mul_left hcomm
  exact h2.mul_inv_cancel

end Lift


section Core

open CFSG.ComponentClassification.AschbacherKnownGroup.FactsL2 in
theorem gammaAct_sl2_core {K : Type} [Field K] [Finite K] {p f : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hK : Nat.card K = p ^ f) (h5 : 5 ≤ p ^ f)
    {A : Type} [Group A] [Finite A] (hA : CFSG.IsElementaryAbelian 2 A) (h4 : Nat.card A = 4)
    (α : A →* MulAut (SL(2, K))) :
    gammaAct α = ⊤ ∨ (p ^ f ∈ ({5, 7, 9} : Finset ℕ) ∧
      α.range ≤ (MulAut.conj : SL(2, K) →* MulAut (SL(2, K))).range) := by
  have : Fact p.Prime := ⟨hp⟩
  have hf1 : 1 ≤ f := by
    rcases Nat.eq_zero_or_pos f with h0 | h0
    · rw [h0, pow_zero] at h5
      omega
    · exact h0
  have hodd : Odd (Nat.card K) := by
    rw [hK]
    exact (hp.odd_of_ne_two hp2).pow
  have h3 : 3 < Nat.card K := by
    rw [hK]
    omega
  have hOPP : IsOddPrimePower (Nat.card K) := isOddPrimePower_of hp hp2 hf1 hK
  obtain ⟨a, b, ha, hb, hab, hall⟩ := GenLocL2.exists_klein_gens hA h4
  by_cases hker : ∃ c : A, c ≠ 1 ∧ α c = 1
  · left
    obtain ⟨c, hc1, hc⟩ := hker
    refine gammaAct_eq_top_of_le_ker α (E := Subgroup.zpowers c)
      (GenLocL2.adm_zpowers hA h4 hc1) ?_
    rw [Subgroup.zpowers_le]
    exact hc
  push Not at hker
  set Φ := GLS.IVK.Lifted.gammaOf hodd h3 with hΦ
  have hinj : Function.Injective Φ := GLS.IVK.Lifted.gammaOf_injective hodd h3
  have hsqA : ∀ c : A, c * c = 1 := fun c => WeakSigGen.mul_self_eq_one_of_isElementaryAbelian hA c
  have hab' : a * b ≠ 1 := by
    intro h
    apply hab
    have h1 : b = a⁻¹ := eq_inv_of_mul_eq_one_right h
    rw [h1, inv_eq_of_mul_eq_one_right (hsqA a)]
  have hβ1 : ∀ c : A, c ≠ 1 → Φ (α c) ≠ 1 := fun c hc h =>
    hker c hc (hinj (by rw [h, map_one]))
  have hβ2 : ∀ c : A, Φ (α c) ^ 2 = 1 := fun c => by
    rw [← map_pow, ← map_pow, pow_two, hsqA c, map_one, map_one]
  have hβne : Φ (α a) ≠ Φ (α b) := by
    intro h
    apply hker (a * b) hab'
    have h1 : α a = α b := hinj h
    rw [map_mul, ← h1, ← map_mul, hsqA a, map_one]
  have hβcomm : Φ (α a) * Φ (α b) = Φ (α b) * Φ (α a) := by
    rw [← map_mul, ← map_mul, ← map_mul, ← map_mul, mul_comm' a b]
  set π : SL(2, K) →* PSL2 K := QuotientGroup.mk' (Subgroup.center SL(2, K)) with hπ
  set H : Subgroup (PSL2 K) := (gammaAct α).map π with hH
  have hmemH : ∀ y : SL(2, K), y ∈ gammaAct α → π y ∈ H := fun y hy => ⟨y, hy, rfl⟩
  have hγ : ∀ γ ∈ ({Φ (α a), Φ (α b), Φ (α a) * Φ (α b)} : Set (PGammaL2 K)),
      ∃ c : A, c ≠ 1 ∧ γ = Φ (α c) := by
    intro γ hγ
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hγ
    rcases hγ with rfl | rfl | rfl
    · exact ⟨a, ha, rfl⟩
    · exact ⟨b, hb, rfl⟩
    · exact ⟨a * b, hab', by rw [map_mul, map_mul]⟩
  have hinv : ∀ γ ∈ ({Φ (α a), Φ (α b), Φ (α a) * Φ (α b)} : Set (PGammaL2 K)), ∀ x ∈ H,
      conjPSL K hOPP h3 γ x ∈ H := by
    intro γ hγ' x hx
    obtain ⟨c, hc1, rfl⟩ := hγ γ hγ'
    obtain ⟨y, hy, rfl⟩ := hx
    rw [GenLocL2.conjPSL_eq_semilinear hOPP h3, ← mk_apply_eq_semilinear hodd h3]
    exact hmemH _ (GenLocL2.smul_mem_gammaAct hA α c hy)
  have hP1 : ∀ γ ∈ ({Φ (α a), Φ (α b), Φ (α a) * Φ (α b)} : Set (PGammaL2 K)), ∀ x : PSL2 K,
      γ * psl2Incl K x = psl2Incl K x * γ → Odd (orderOf x) → x ∈ H := by
    intro γ hγ' x hcomm hxodd
    obtain ⟨c, hc1, rfl⟩ := hγ γ hγ'
    have h1 : CFSG.ComponentClassification.CatalogueSchreierLinearTwo.semilinearAction K
        (Φ (α c)) x = x := (commute_incl_iff _ _).1 hcomm
    obtain ⟨y, hyx, hyodd⟩ := exists_odd_lift (Subgroup.center SL(2, K)) x hxodd
    have h2 : α c y = y := by
      apply eq_of_mk_eq_of_odd hyodd
      rw [mk_apply_eq_semilinear hodd h3]
      rw [← hyx] at h1
      exact h1
    rw [← hyx]
    exact hmemH y (le_gammaAct α (GenLocL2.adm_zpowers hA h4 hc1)
      (GenLocL2.fixedIn_zpowers α h2))
  have hP2 : ∀ γ ∈ ({Φ (α a), Φ (α b), Φ (α a) * Φ (α b)} : Set (PGammaL2 K)), ∀ t : PSL2 K,
      t ^ 2 = 1 → t ≠ 1 → γ = psl2Incl K t → ∀ y : PSL2 K, t ∈ Subgroup.zpowers y → y ∈ H := by
    intro γ hγ' t _ _ hγt y hty
    obtain ⟨c, hc1, rfl⟩ := hγ γ hγ'
    obtain ⟨s, rfl⟩ := QuotientGroup.mk_surjective t
    obtain ⟨y', rfl⟩ := QuotientGroup.mk_surjective y
    have h1 : α c = MulAut.conj s := by
      apply hinj
      rw [GLS.IVK.Lifted.gammaOf_conj]
      exact hγt
    obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.1 hty
    have hn' : QuotientGroup.mk' (Subgroup.center SL(2, K)) s =
        QuotientGroup.mk' (Subgroup.center SL(2, K)) (y' ^ n) := by
      rw [map_zpow]
      exact hn.symm
    have h2 : α c y' = y' := by
      rw [h1]
      exact conj_fix_of_mem_zpowers hn'
    exact hmemH y' (le_gammaAct α (GenLocL2.adm_zpowers hA h4 hc1)
      (GenLocL2.fixedIn_zpowers α h2))
  have hmain := psl2_generation_model (K := K) (p := p) (f := f) hK hOPP h3
    (a := Φ (α a)) (b := Φ (α b)) hβcomm (hβ2 a) (hβ2 b) (hβ1 a ha) (hβ1 b hb) hβne H hinv hP1 hP2
  rcases hmain with htop | ⟨hq, haI, hbI⟩
  · left
    have hcov : gammaAct α ⊔ Subgroup.center SL(2, K) = ⊤ := by
      rw [eq_top_iff]
      intro x _
      have hx : π x ∈ H := htop ▸ Subgroup.mem_top _
      obtain ⟨g, hg, hgx⟩ := hx
      have hc : g⁻¹ * x ∈ Subgroup.center SL(2, K) := QuotientGroup.eq.1 hgx
      have hxg : x = g * (g⁻¹ * x) := by group
      rw [hxg]
      exact Subgroup.mul_mem_sup hg hc
    have hperf : commutator SL(2, K) = ⊤ :=
      (ClassicalModels.specialLinear_isPerfect_two_of_four_le_card K (by omega)).commutator_eq_top
    exact eq_top_of_sup_center_eq_top hperf hcov
  · right
    refine ⟨by rw [← hK]; exact hq, ?_⟩
    have hinner : ∀ c : A, Φ (α c) ∈ (psl2Incl K).range →
        α c ∈ (MulAut.conj : SL(2, K) →* MulAut (SL(2, K))).range := by
      rintro c ⟨x, hx⟩
      obtain ⟨s, rfl⟩ := QuotientGroup.mk_surjective x
      refine ⟨s, hinj ?_⟩
      rw [GLS.IVK.Lifted.gammaOf_conj]
      exact hx
    rintro φ ⟨c, rfl⟩
    rcases hall c with rfl | rfl | rfl | rfl
    · rw [map_one]
      exact one_mem _
    · exact hinner _ haI
    · exact hinner _ hbI
    · rw [map_mul]
      exact mul_mem (hinner _ haI) (hinner _ hbI)

end Core

end GenLocL2SL

section L2SL

variable {A : Type} [Group A] [Finite A]

theorem gammaAct_sl2_rank2 {K : Type} [Field K] [Finite K] {p f : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hK : Nat.card K = p ^ f) (h5 : 5 ≤ p ^ f)
    (α : A →* MulAut (SL(2, K))) (hA : IsRank23 A) (hk : pRank 2 A = 2)
    (hexc : ¬ (p ^ f ∈ ({5, 7, 9} : Finset ℕ) ∧
      α.range ≤ (MulAut.conj : SL(2, K) →* MulAut (SL(2, K))).range)) :
    gammaAct α = ⊤ := by
  have h4 : Nat.card A = 4 := by
    rw [GenLocBasic.card_eq_two_pow_pRank_type hA.1, hk]
    norm_num
  exact (GenLocL2SL.gammaAct_sl2_core hp hp2 hK h5 hA.1 h4 α).resolve_right hexc

end L2SL

end CFSG.GH74.Generic.BProg.B2
