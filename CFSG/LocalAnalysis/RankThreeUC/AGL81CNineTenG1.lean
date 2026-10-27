module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81CNineTenDefs
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.LinearThreeEquiv
public import Certificates.Data.ExceptionalSL3

public section

namespace CFSG.LocalAnalysis.RankThreeUC.AGL81C

open Subgroup

section Abstract

variable {Γ B : Type*} [Group Γ] [Finite Γ] [Group B] [Finite B]

theorem oPPrimeHull_top_normal (p : ℕ) : (oPPrimeHull p (⊤ : Subgroup B)).Normal := by
  refine ⟨fun n hn g => ?_⟩
  have h : (oPPrimeHull p (⊤ : Subgroup B)).map (MulAut.conj g).toMonoidHom ≤
      oPPrimeHull p (⊤ : Subgroup B) := by
    rw [oPPrimeHull, MonoidHom.map_closure]
    refine Subgroup.closure_mono ?_
    rintro _ ⟨x, ⟨-, k, hk⟩, rfl⟩
    refine ⟨trivial, k, ?_⟩
    rw [← hk]
    exact orderOf_injective (MulAut.conj g).toMonoidHom (MulAut.conj g).injective x
  exact h ⟨n, hn, rfl⟩

theorem nonempty_mulEquiv_oPPrimeHull (Γ₀ A : Subgroup Γ) (hΓ₀ : Nat.card Γ₀ = 12)
    (h3 : ∀ x : Γ, (∃ k : ℕ, orderOf x = 3 ^ k) → x ∈ Γ₀)
    (φ : A →* B) (hφ : Function.Surjective φ) (hB3 : 3 ∣ Nat.card B)
    (hO : CFSG.pCore 3 B = ⊥) :
    Nonempty (↥(oPPrimeHull 3 (⊤ : Subgroup B)) ≃* ↥Γ₀) := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set W : Subgroup B := oPPrimeHull 3 (⊤ : Subgroup B) with hW
  haveI hWn : W.Normal := oPPrimeHull_top_normal 3
  let φ₀ : ↥(A ⊓ Γ₀) →* B := φ.comp (Subgroup.inclusion inf_le_left)
  have h1 : W ≤ φ₀.range := by
    refine (Subgroup.closure_le _).mpr ?_
    rintro b ⟨-, k, hk⟩
    have hb : IsPGroup 3 (Subgroup.zpowers b) :=
      IsPGroup.of_card (n := k) (by rw [Nat.card_zpowers, hk])
    obtain ⟨P, hbP⟩ := hb.exists_le_sylow
    obtain ⟨PA, rfl⟩ := Sylow.mapSurjective_surjective hφ 3 P
    have hbP' : b ∈ (PA : Subgroup A).map φ := by
      have := hbP (Subgroup.mem_zpowers b)
      rwa [Sylow.coe_mapSurjective] at this
    obtain ⟨a, haP, rfl⟩ := hbP'
    obtain ⟨j, hj⟩ := IsPGroup.iff_orderOf.mp PA.isPGroup' ⟨a, haP⟩
    have haΓ : ((a : A) : Γ) ∈ Γ₀ := by
      refine h3 _ ⟨j, ?_⟩
      rw [Subgroup.orderOf_coe]
      simpa using hj
    exact ⟨⟨(a : Γ), a.2, haΓ⟩, rfl⟩
  have hdomdvd : Nat.card ↥(A ⊓ Γ₀) ∣ 12 := hΓ₀ ▸ Subgroup.card_dvd_of_le inf_le_right
  have h2 : Nat.card φ₀.range ∣ 12 := (Subgroup.card_range_dvd φ₀).trans hdomdvd
  have hWdvd : Nat.card W ∣ 12 := (Subgroup.card_dvd_of_le h1).trans h2
  have h3W : 3 ∣ Nat.card W := by
    obtain ⟨b, hb⟩ := exists_prime_orderOf_dvd_card' 3 hB3
    have hbW : b ∈ W := Subgroup.subset_closure ⟨trivial, 1, by simpa using hb⟩
    have : orderOf (⟨b, hbW⟩ : W) = 3 := by rw [Subgroup.orderOf_mk]; exact hb
    rw [← this]
    exact orderOf_dvd_natCard _
  have h4 : ¬ (Nat.card W = 3 ∨ Nat.card W = 6) := by
    intro hW36
    obtain ⟨P⟩ : Nonempty (Sylow 3 W) := inferInstance
    have hPcard : Nat.card P = 3 := by
      rw [Sylow.card_eq_multiplicity]
      rcases hW36 with h | h <;> rw [h]
      · simp [Nat.Prime.factorization_self Nat.prime_three]
      · have : (6 : ℕ).factorization 3 = 1 := by
          have h6 : (6 : ℕ) = 3 * 2 := by norm_num
          rw [h6, Nat.factorization_mul (by norm_num) (by norm_num)]
          simp [Nat.Prime.factorization_self Nat.prime_three,
            Nat.factorization_eq_zero_of_not_dvd (by norm_num : ¬ 3 ∣ 2)]
        rw [this]
        simp
    have hidx : (P : Subgroup W).index = 1 ∨ (P : Subgroup W).index = 2 := by
      have := Subgroup.card_mul_index (P : Subgroup W)
      rcases hW36 with h | h <;> rw [hPcard, h] at this <;> omega
    have hPn : (P : Subgroup W).Normal := by
      rcases hidx with h | h
      · rw [Subgroup.index_eq_one] at h
        rw [h]
        exact Subgroup.normal_top
      · exact Subgroup.normal_of_index_eq_two h
    haveI : (P : Subgroup W).Characteristic := Sylow.characteristic_of_normal P hPn
    have hPB : ((P : Subgroup W).map W.subtype).Normal := inferInstance
    have hle : (P : Subgroup W).map W.subtype ≤ CFSG.pCore 3 B :=
      le_sSup ⟨hPB, P.isPGroup'.map W.subtype⟩
    rw [hO] at hle
    have h5 : (P : Subgroup W).map W.subtype = ⊥ := le_bot_iff.mp hle
    have h6 : Nat.card ((P : Subgroup W).map W.subtype) = 3 := by
      rw [Subgroup.card_map_of_injective W.subtype_injective]
      exact hPcard
    rw [h5, Subgroup.card_bot] at h6
    omega
  have hW12 : Nat.card W = 12 := by
    have hle : Nat.card W ≤ 12 := Nat.le_of_dvd (by norm_num) hWdvd
    have key : ∀ n : ℕ, n < 13 → n ∣ 12 → 3 ∣ n → ¬ (n = 3 ∨ n = 6) → n = 12 := by decide
    exact key _ (by omega) hWdvd h3W h4
  have hfin : Nat.card φ₀.range = 12 := by
    have h1' := Subgroup.card_dvd_of_le h1
    rw [hW12] at h1'
    exact Nat.dvd_antisymm h2 h1'
  have hWr : W = φ₀.range := Subgroup.eq_of_le_of_card_ge h1 (by rw [hW12, hfin])
  have hdom : Nat.card ↥(A ⊓ Γ₀) = 12 := by
    have h1' := Subgroup.card_range_dvd φ₀
    rw [hfin] at h1'
    exact Nat.dvd_antisymm hdomdvd h1'
  have hker : φ₀.ker = ⊥ := by
    have := Subgroup.card_ker_mul_card_range φ₀
    rw [hdom, hfin] at this
    have h1k : Nat.card φ₀.ker = 1 := by omega
    exact Subgroup.eq_bot_of_card_eq _ h1k
  have hinj : Function.Injective φ₀ := (MonoidHom.ker_eq_bot_iff φ₀).mp hker
  have heq : A ⊓ Γ₀ = Γ₀ :=
    Subgroup.eq_of_le_of_card_ge inf_le_right (by rw [hdom, hΓ₀])
  exact ⟨(MulEquiv.subgroupCongr hWr).trans
    ((MonoidHom.ofInjective hinj).symm.trans (MulEquiv.subgroupCongr heq))⟩

theorem nonempty_mulEquiv_oPPrimeHull_of_hom {X : Type*} [Group X] (Γ₀ : Subgroup Γ)
    (hΓ₀ : Nat.card Γ₀ = 12) (h3 : ∀ x : Γ, (∃ k : ℕ, orderOf x = 3 ^ k) → x ∈ Γ₀)
    (σ : X →* Γ) (π : X →* B) (hπ : Function.Surjective π) (hker : σ.ker ≤ π.ker)
    (hB3 : 3 ∣ Nat.card B) (hO : CFSG.pCore 3 B = ⊥) :
    Nonempty (↥(oPPrimeHull 3 (⊤ : Subgroup B)) ≃* ↥Γ₀) := by
  let φ : σ.range →* B := MonoidHom.liftOfSurjective σ.rangeRestrict σ.rangeRestrict_surjective
    ⟨π, by rwa [MonoidHom.ker_rangeRestrict]⟩
  have hφ : Function.Surjective φ := by
    intro b
    obtain ⟨x, rfl⟩ := hπ b
    exact ⟨σ.rangeRestrict x, MonoidHom.liftOfRightInverse_comp_apply _ _ _ _ x⟩
  exact nonempty_mulEquiv_oPPrimeHull Γ₀ σ.range hΓ₀ h3 φ hφ hB3 hO

theorem map_eq_one_of_map_mem_center {X Γ' : Type*} [Group X] [Group Γ'] {B' : Type*} [Group B']
    (ρ : X →* Γ') (π : X →* B') (hπ : Function.Surjective π) (hker : ρ.ker ≤ π.ker)
    (hB : Subgroup.center B' = ⊥) {x : X} (hx : ρ x ∈ Subgroup.center Γ') : π x = 1 := by
  have hc : π x ∈ Subgroup.center B' := by
    rw [Subgroup.mem_center_iff]
    intro b
    obtain ⟨y, rfl⟩ := hπ b
    have h1 : x * y * x⁻¹ * y⁻¹ ∈ ρ.ker := by
      rw [MonoidHom.mem_ker]
      have h2 : ρ y * ρ x = ρ x * ρ y := Subgroup.mem_center_iff.mp hx (ρ y)
      simp only [map_mul, map_inv]
      calc ρ x * ρ y * (ρ x)⁻¹ * (ρ y)⁻¹ = (ρ y * ρ x) * (ρ x)⁻¹ * (ρ y)⁻¹ := by rw [h2]
        _ = 1 := by group
    have h3 := hker h1
    rw [MonoidHom.mem_ker] at h3
    have h4 : π x * π y * (π x)⁻¹ * (π y)⁻¹ = 1 := by simpa only [map_mul, map_inv] using h3
    exact (mul_inv_eq_iff_eq_mul.mp (mul_inv_eq_one.mp h4)).symm
  rw [hB, Subgroup.mem_bot] at hc
  exact hc

end Abstract

section Z2S4

theorem isPSLType_two_three_of_mulEquiv_alternatingGroup {X : Type} [Group X]
    (e : X ≃* alternatingGroup (Fin 4)) : IsPSLType 2 (ZMod 3) X :=
  ⟨e.trans CFSG.GorensteinWalter.psl2_three_equiv_alternatingGroup.symm⟩

end Z2S4

section GL23

theorem mem_alternatingGroup_of_odd_orderOf {α : Type*} [DecidableEq α] [Fintype α]
    (x : Equiv.Perm α) (hx : Odd (orderOf x)) : x ∈ alternatingGroup α := by
  rw [Equiv.Perm.mem_alternatingGroup]
  have h : Equiv.Perm.sign x ^ orderOf x = 1 := by
    rw [← map_pow, pow_orderOf_eq_one, map_one]
  rcases Int.units_eq_one_or (Equiv.Perm.sign x) with h1 | h1
  · exact h1
  · rw [h1, hx.neg_one_pow] at h
    exact absurd h (by decide)

theorem card_alternatingGroup_four : Nat.card (alternatingGroup (Fin 4)) = 12 := by
  rw [Nat.card_eq_fintype_card, card_alternatingGroup]
  simp [Nat.factorial]

theorem isPSLType_oPPrimeHull_of_hom_GL23 {X B : Type} [Group X] [Group B] [Finite B]
    (ρ : X →* Matrix.GeneralLinearGroup (Fin 2) (ZMod 3)) (π : X →* B)
    (hπ : Function.Surjective π) (hρ : IsPGroup 3 (ρ.ker.map π)) (hB3 : 3 ∣ Nat.card B)
    (hO : CFSG.pCore 3 B = ⊥) (hZ : Subgroup.center B = ⊥) :
    IsPSLType 2 (ZMod 3) ↥(oPPrimeHull 3 (⊤ : Subgroup B)) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hker : ρ.ker ≤ π.ker := by
    have hn : (ρ.ker.map π).Normal := (MonoidHom.normal_ker ρ).map π hπ
    have hle : ρ.ker.map π ≤ CFSG.pCore 3 B := le_sSup ⟨hn, hρ⟩
    rwa [hO, le_bot_iff, Subgroup.map_eq_bot_iff] at hle
  let σ : X →* Equiv.Perm (Fin 4) :=
    (CFSG.GorensteinWalter.pgl2_three_equiv_perm : _ ≃* _).toMonoidHom.comp
      (Matrix.ProjGenLinGroup.mk.comp ρ)
  have hσ : σ.ker ≤ π.ker := by
    intro x hx
    rw [MonoidHom.mem_ker] at hx ⊢
    have h1 : Matrix.ProjGenLinGroup.mk (ρ x) = 1 :=
      (MulEquiv.map_eq_one_iff _).mp hx
    exact map_eq_one_of_map_mem_center ρ π hπ hker hZ (Matrix.ProjGenLinGroup.mk_eq_one.mp h1)
  obtain ⟨e⟩ := nonempty_mulEquiv_oPPrimeHull_of_hom (alternatingGroup (Fin 4))
    card_alternatingGroup_four
    (fun x hx => mem_alternatingGroup_of_odd_orderOf x
      (hx.elim fun k hk => hk ▸ Odd.pow (by decide))) σ π hπ hσ hB3 hO
  exact isPSLType_two_three_of_mulEquiv_alternatingGroup e

end GL23

end CFSG.LocalAnalysis.RankThreeUC.AGL81C
