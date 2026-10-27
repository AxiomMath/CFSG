module

public import CFSG.GH74.GLS.Stage1.Thm3.Sec6.L510L2
public import CFSG.GH74.GLS.Stage1.Thm3.Sec6.L510Gamma
public import CFSG.GH74.GLS.Stage1.Thm3.Sec6.L510A7
public import CFSG.GH74.GLS.IVK.Lifted.Outer14

public section

namespace CFSG.GH74.GLS.Stage1.Thm3.Sec6.L510

open Subgroup Matrix CFSG CFSG.GH74.GLS CFSG.GH74.GLS.IVK CFSG.GH74.GLS.IVK.Lifted CFSG.GorensteinWalter
  CFSG.ABGLocalTools CFSG.ABGDGroups CFSG.Assembly.LowTwoRank CFSG.GH74.GLS.Stage1.Thm2.Recip
  CFSG.ComponentClassification.CatalogueSchreierLinearTwo

structure RIface {Q : Type} [Group Q] (M D : Subgroup (MulAut Q)) (r : MulAut Q) : Prop where
  mem : r ∈ M
  ne_one : r ≠ 1
  fAut : ∀ i : ℕ, r ^ i ≠ 1 → IsFAutomorphism Q (r ^ i)
  inn : ∀ i : ℕ, r ^ i ∈ D → r ^ i = 1
  index : (D ⊔ zpowers r).relIndex M ≤ 2
  a7 : IsDoubleCoverOfAlt Q 7 → D ⊔ zpowers r = M
  invol : ∀ φ ∈ M, φ * φ = 1 → φ ≠ 1 → IsFAutomorphism Q φ →
    ∃ d ∈ D, φ = d * r ^ (orderOf r / 2)

theorem l510_unique_invol {X : Type} [Group X] [Finite X] {r r₁ : X} (hr₁ : r₁ ∈ zpowers r)
    (h2 : orderOf r₁ = 2) : r₁ = r ^ (orderOf r / 2) := by
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 hr₁
  have hNpos : 0 < orderOf r := orderOf_pos r
  set N := orderOf r with hN
  have hmod : r ^ (k % (N : ℤ)) = r ^ k := zpow_mod_orderOf r k
  obtain ⟨j, hj⟩ : ∃ j : ℕ, (j : ℤ) = k % (N : ℤ) :=
    ⟨(k % (N : ℤ)).toNat, Int.toNat_of_nonneg (Int.emod_nonneg _ (by exact_mod_cast hNpos.ne'))⟩
  have hr₁j : r₁ = r ^ j := by
    rw [← hk, ← hmod, ← hj, zpow_natCast]
  have hj0 : j ≠ 0 := by
    rintro rfl
    rw [pow_zero] at hr₁j
    rw [hr₁j, orderOf_one] at h2
    omega
  have hjN : j < N := by
    have : (j : ℤ) < N := by
      rw [hj]
      exact Int.emod_lt_of_pos _ (by exact_mod_cast hNpos)
    exact_mod_cast this
  have hord : orderOf r₁ = N / N.gcd j := by
    rw [hr₁j]
    exact orderOf_pow' r hj0
  rw [h2] at hord
  set g := N.gcd j with hg
  have hgN : g ∣ N := Nat.gcd_dvd_left N j
  have hgj : g ∣ j := Nat.gcd_dvd_right N j
  have hN2 : N = 2 * g := by
    have := Nat.div_mul_cancel hgN
    rw [← hord] at this
    omega
  have hgpos : 0 < g := Nat.pos_of_ne_zero (fun h => by rw [h] at hN2; omega)
  obtain ⟨c, hc⟩ := hgj
  have hjg : j = g := by
    have hc0 : c ≠ 0 := fun h => hj0 (by rw [hc, h, mul_zero])
    have hc1 : c < 2 := by
      by_contra hcon
      push Not at hcon
      have : 2 * g ≤ g * c := by nlinarith
      omega
    have : c = 1 := by omega
    rw [hc, this, mul_one]
  rw [hr₁j, hjg]
  congr 1
  omega

theorem fieldPart_ne_one_of_fixedCond {F : Type} [Field F] [Finite F] {Q : Type} [Group Q]
    (hodd : Odd (Nat.card F)) (h3 : 3 < Nat.card F) (e : Q ≃* SpecialLinearGroup (Fin 2) F)
    (φ : MulAut Q) (hφ1 : φ ≠ 1) (hf : FixedCond Q φ) :
    (gammaOf hodd h3 (MulAut.congr e φ)).right ≠ 1 := by
  intro hσ
  have hα1 : MulAut.congr e φ ≠ 1 := fun h =>
    hφ1 ((MulAut.congr e).injective (h.trans (map_one _).symm))
  obtain ⟨G, hG⟩ := eq_slConjugation_of_right_eq_one hodd h3 _ hσ
  apply not_fixedCond_of_comm φ _ hf
  apply comm_fixed_of_congr e φ
  rw [hG]
  exact fixed_comm_of_slConjugation G (hG ▸ hα1)

theorem fieldAutHom_std {F : Type} [Field F] [Finite F] (σ : F ≃+* F) :
    fieldAutHom (L2.equivPSL F).symm σ = psl2FieldAut F σ := by
  have h : toPSL (L2.equivPSL F).symm = MulEquiv.refl (PSL2 F) := by
    ext x
    simp [toPSL]
  rw [fieldAutHom_apply', h]
  ext x
  rfl

section SL2Case

variable {Q : Type} [Group Q] [Finite Q]

theorem exists_rIface_sl (hO : HatOK Q) {F : Type} [Field F] [Finite F]
    (hodd : Odd (Nat.card F)) (h3 : 3 < Nat.card F) (e : Q ≃* SpecialLinearGroup (Fin 2) F)
    (M : Subgroup (MulAut Q)) (hM : IsPGroup 2 ↥M) (P : Sylow 2 Q)
    (hDM : (P : Subgroup Q).map (MulAut.conj : Q →* MulAut Q) ≤ M)
    (φ₀ : MulAut Q) (hφ₀M : φ₀ ∈ M) (hφ₀F : IsFAutomorphism Q φ₀) (hφ₀2 : φ₀ * φ₀ = 1)
    (hφ₀1 : φ₀ ≠ 1) :
    ∃ r, RIface M ((P : Subgroup Q).map (MulAut.conj : Q →* MulAut Q)) r := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hL2 : L2Field F := ⟨hodd, h3⟩
  set D : Subgroup (MulAut Q) := (P : Subgroup Q).map (MulAut.conj : Q →* MulAut Q) with hD
  let ι : MulAut Q →* MulAut (PSL2 F) := psl2AutHom.comp (MulAut.congr e).toMonoidHom
  have hι : Function.Injective ι :=
    (psl2AutHom_injective hodd h3).comp (MulAut.congr e).injective
  let π : Q →* PSL2 F :=
    (QuotientGroup.mk' (Subgroup.center (SpecialLinearGroup (Fin 2) F))).comp e.toMonoidHom
  have hπ : Function.Surjective π := (QuotientGroup.mk'_surjective _).comp e.surjective
  have hιconj : ∀ x : Q, ι (MulAut.conj x) = MulAut.conj (π x) := by
    intro x
    show psl2AutHom (MulAut.congr e (MulAut.conj x)) = _
    rw [congr_conj, psl2AutHom_conj]
    rfl
  let e₀ : PSL2 F ≃* L2 F := (L2.equivPSL F).symm
  let P₀' : Sylow 2 (PSL2 F) := P.mapSurjective hπ
  have hP₀'coe : (P₀' : Subgroup (PSL2 F)) = (P : Subgroup Q).map π := Sylow.coe_mapSurjective _ _
  have hM' : IsPGroup 2 ↥(M.map ι) := hM.of_equiv (Subgroup.equivMapOfInjective M ι hι)
  have hD' : ((P₀' : Subgroup (PSL2 F)).map (MulAut.conj : PSL2 F →* MulAut (PSL2 F))) = D.map ι := by
    rw [hP₀'coe, Subgroup.map_map, hD, Subgroup.map_map]
    congr 1
    exact MonoidHom.ext fun x => (hιconj x).symm
  have hP₀'M : (P₀' : Subgroup (PSL2 F)).map (MulAut.conj : PSL2 F →* MulAut (PSL2 F)) ≤
      M.map ι := by
    rw [hD']
    exact Subgroup.map_mono hDM
  obtain ⟨e', Rm', hRm'M, hRm'F, hDRm', hidx', hinv'⟩ :=
    l2_exists_Rm hL2 e₀ (M.map ι) hM' P₀' hP₀'M
  rw [hD'] at hDRm' hidx' hinv'
  set Rm : Subgroup (MulAut Q) := Rm'.comap ι with hRm
  have hRm'range : Rm' ≤ ι.range := fun x hx => by
    obtain ⟨m, -, rfl⟩ := Subgroup.mem_map.1 (hRm'M hx)
    exact ⟨m, rfl⟩
  have hRmmap : Rm.map ι = Rm' := by
    rw [hRm, Subgroup.map_comap_eq]
    exact inf_eq_right.2 hRm'range
  have hRmM : Rm ≤ M := by
    intro x hx
    obtain ⟨m, hm, hmx⟩ := Subgroup.mem_map.1 (hRm'M (Subgroup.mem_comap.1 hx))
    have : m = x := hι hmx
    exact this ▸ hm
  have hRm'cyc : IsCyclic ↥Rm' := by
    have : IsCyclic ↥(fieldAutSub e') := (ivk_1_2e F hL2 (PSL2 F) e').1
    have h1 : IsCyclic ↥(Rm'.subgroupOf (fieldAutSub e')) := Subgroup.isCyclic _
    exact (Subgroup.subgroupOfEquivOfLe hRm'F).isCyclic.1 h1
  have hRmcyc : IsCyclic ↥Rm :=
    ((Subgroup.equivMapOfInjective Rm ι hι).trans (MulEquiv.subgroupCongr hRmmap)).isCyclic.2 hRm'cyc
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := ↥Rm)
  set r : MulAut Q := (g : MulAut Q) with hr
  have hrRm : r ∈ Rm := g.2
  have hzp : zpowers r = Rm := by
    apply le_antisymm (zpowers_le.2 hrRm)
    intro x hx
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 (hg ⟨x, hx⟩)
    exact Subgroup.mem_zpowers_iff.2 ⟨k, by simpa using congrArg Subtype.val hk⟩
  have hrM : r ∈ M := hRmM hrRm
  have hφ₀ord : orderOf φ₀ = 2 := orderOf_eq_prime (by rw [pow_two]; exact hφ₀2) hφ₀1
  have hιφ₀M : ι φ₀ ∈ M.map ι := Subgroup.mem_map_of_mem ι hφ₀M
  have hιφ₀ord : orderOf (ι φ₀) = 2 := by rw [orderOf_injective ι hι φ₀]; exact hφ₀ord
  have hιfp : fieldProj e₀ (ι φ₀) ≠ 1 := by
    have : ι φ₀ = psl2AutHom (MulAut.congr e φ₀) := rfl
    rw [this, fieldProj_psl2AutHom hodd h3]
    exact fieldPart_ne_one_of_fixedCond hodd h3 e φ₀ hφ₀1 hφ₀F.2.2.2.2
  obtain ⟨r₁', hr₁'Rm', hr₁'2, hall⟩ := hinv' (ι φ₀) hιφ₀M hιφ₀ord hιfp
  have hr₁'Rm'' := hr₁'Rm'
  rw [← hRmmap] at hr₁'Rm''
  obtain ⟨r₁, hr₁Rm, rfl⟩ := Subgroup.mem_map.1 hr₁'Rm''
  have hr₁2 : orderOf r₁ = 2 := by rw [← orderOf_injective ι hι r₁]; exact hr₁'2
  have hr₁eq : r₁ = r ^ (orderOf r / 2) :=
    l510_unique_invol (hzp ▸ hr₁Rm) hr₁2
  have hr₁1 : r₁ ≠ 1 := fun h1 => by rw [h1, orderOf_one] at hr₁2; omega
  refine ⟨r, hrM, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro h1
    apply hr₁1
    rw [hr₁eq, h1, one_pow]
  ·
    intro i _
    have hiRm : r ^ i ∈ Rm := pow_mem hrRm i
    have hiM : r ^ i ∈ M := hRmM hiRm
    have hmemF : ι (r ^ i) ∈ fieldAutSub e' := hRm'F (Subgroup.mem_comap.1 hiRm)
    obtain ⟨σ, hσ⟩ := hmemF
    let ψ : MulAut (PSL2 F) := e'.trans e₀.symm
    have he' : twistEquiv e₀ ψ = e' := by
      ext x
      simp [twistEquiv, ψ]
    have h1 : psl2AutHom (MulAut.congr e (r ^ i)) = ψ⁻¹ * psl2FieldAut F σ * ψ := by
      have h2 : psl2AutHom (MulAut.congr e (r ^ i)) = ι (r ^ i) := rfl
      rw [h2, ← hσ, ← he', fieldAutHom_twist, fieldAutHom_std]
    have hfix : FixedCond Q (r ^ i) :=
      fixedCond_of_congr e (fixedCond_of_twisted_field hodd h3 _ ψ σ h1)
    obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.1 hM) ⟨r ^ i, hiM⟩
    rw [Subgroup.orderOf_mk] at hk
    exact ⟨hO.quasi, hO.kgrp, hO.rank, ⟨k, hk⟩, hfix⟩
  · intro i hi
    have hiRm : r ^ i ∈ Rm := pow_mem hrRm i
    have h1 : ι (r ^ i) ∈ D.map ι ⊓ Rm' := ⟨Subgroup.mem_map_of_mem ι hi, Subgroup.mem_comap.1 hiRm⟩
    rw [hDRm', Subgroup.mem_bot] at h1
    exact hι (by rw [h1, map_one])
  · rw [hzp]
    have h1 := hidx'
    rw [← hRmmap, ← Subgroup.map_sup, Subgroup.relIndex_map_map_of_injective _ _ hι] at h1
    exact h1
  · intro h7
    exact (not_sl2_of_double_cover_alt7 h7
      (e.trans (specialLinearGroupEquivStatedSL 2 F))).elim
  · intro φ hφM hφ2 hφ1 hφF
    have hιφM : ι φ ∈ M.map ι := Subgroup.mem_map_of_mem ι hφM
    have hφord : orderOf φ = 2 := orderOf_eq_prime (by rw [pow_two]; exact hφ2) hφ1
    have hιφord : orderOf (ι φ) = 2 := by rw [orderOf_injective ι hι φ]; exact hφord
    have hιφfp : fieldProj e₀ (ι φ) ≠ 1 := by
      have : ι φ = psl2AutHom (MulAut.congr e φ) := rfl
      rw [this, fieldProj_psl2AutHom hodd h3]
      exact fieldPart_ne_one_of_fixedCond hodd h3 e φ hφ1 hφF.2.2.2.2
    obtain ⟨d', hd', hφd'⟩ := hall (ι φ) hιφM hιφord hιφfp
    obtain ⟨d, hdD, rfl⟩ := Subgroup.mem_map.1 hd'
    refine ⟨d, hdD, ?_⟩
    apply hι
    rw [hφd', map_mul, hr₁eq]

end SL2Case

section Combined

variable {Q : Type} [Group Q] [Finite Q]

theorem exists_rIface (h2A7 : II4_2A7) (hO : HatOK Q)
    (M : Subgroup (MulAut Q)) (hM : IsPGroup 2 ↥M) (P : Sylow 2 Q)
    (hDM : (P : Subgroup Q).map (MulAut.conj : Q →* MulAut Q) ≤ M)
    (φ₀ : MulAut Q) (hφ₀M : φ₀ ∈ M) (hφ₀F : IsFAutomorphism Q φ₀) (hφ₀2 : φ₀ * φ₀ = 1)
    (hφ₀1 : φ₀ ≠ 1) :
    ∃ r, RIface M ((P : Subgroup Q).map (MulAut.conj : Q →* MulAut Q)) r := by
  rcases sl_or_a7 hO.sl2 with ⟨F, _, _, hodd, h3, ⟨e⟩⟩ | h7
  · exact exists_rIface_sl hO hodd h3 e M hM P hDM φ₀ hφ₀M hφ₀F hφ₀2 hφ₀1
  · obtain ⟨hD1, hD2, hD3⟩ := a7_iface h2A7 hO h7 M hM P hDM φ₀ hφ₀M hφ₀F hφ₀2 hφ₀1
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have hord : orderOf φ₀ = 2 := orderOf_eq_prime (by rw [pow_two]; exact hφ₀2) hφ₀1
    have hsq : φ₀ ^ 2 = 1 := by rw [sq]; exact hφ₀2
    refine ⟨φ₀, hφ₀M, hφ₀1, ?_, ?_, ?_, fun _ => hD1, ?_⟩
    · intro i hi
      rcases Nat.even_or_odd' i with ⟨k, hk | hk⟩
      · exfalso
        apply hi
        rw [hk, pow_mul, hsq, one_pow]
      · rw [hk, pow_succ, pow_mul, hsq, one_pow, one_mul]
        exact hφ₀F
    · intro i hi
      have h1 : φ₀ ^ i ∈ (P : Subgroup Q).map (MulAut.conj : Q →* MulAut Q) ⊓ zpowers φ₀ :=
        ⟨hi, (zpowers φ₀).pow_mem (mem_zpowers φ₀) i⟩
      rw [hD2, Subgroup.mem_bot] at h1
      exact h1
    · rw [hD1, Subgroup.relIndex_self]
      norm_num
    · intro φ hφM hφ2 hφ1 hφF
      obtain ⟨d, hd, hφd⟩ := hD3 φ hφM hφ2 hφ1 hφF
      exact ⟨d, hd, by rw [hord]; simpa using hφd⟩

end Combined

end CFSG.GH74.GLS.Stage1.Thm3.Sec6.L510
