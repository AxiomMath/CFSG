module

public import CFSG.Quasithin.H13.L32NLem14331f
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.L32NLem14331d

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.QuasithinUnique

namespace L14331

variable {W : Type} [Group W]

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G]

structure CaseI_F4 {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G] (T L V : Subgroup G) (g : G)
    (D : HatModelU (fsuU T V)) (e : G) : Prop where

  h14325 : Lemma14325One_F4

  h1222 : Stmt12_2_2_F4

  h12213 : Stmt12_2_13_F4

  h12810 : Lemma12_8_10_F4

  h12813 : Lemma12_8_13_F4

  hQ : centralizerMod (fsuV1 T V) (l32nH T V) (fsuU T V) = pCoreOf 2 (l32nH T V)

  he : e ∈ centerOf (i128 T L V (fsuV1 T V))

  he1 : e ≠ 1

  he2 : e * e = 1

  hi : Case14323i T L V g D

  hd : Module.finrank (ZMod 2) D.V = 4

end L14331

namespace L14328

open L14331

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G] {T L V V₂ : Subgroup G} [IsMulCommutative ↥V]

namespace Ctx_F4
open Ctx
open CFSG.Quasithin.H13.L14328.Ctx_F4

variable {g z b l : G} (C : Ctx_F4 G T L V V₂ g z b l) (D : HatModelU (fsuU T V)) {e : G}
include C

theorem caseI_a_H_F4 (X : CaseI_F4 T L V g D e) : l⁻¹ * e * l ∈ l32nH T V :=
  L14332.conj_zU_le_F4 X.h12813 C.setting C.gP C.gN (C.conj_mem_zIl_F4 X.he).1

theorem caseI_a_N_F4 (X : CaseI_F4 T L V g D e) :
    l⁻¹ * e * l ∈ Subgroup.normalizer (fsuU T V : Set G) :=
  L14332.l32nH_le_normalizer_fsuU T V (C.caseI_a_H_F4 D X)

theorem caseI_K_H_F4 (X : CaseI_F4 T L V g D e) : kA T V (l⁻¹ * e * l) ≤ l32nH T V :=
  kA_le (C.caseI_a_H_F4 D X)

theorem caseI_K_Z_F4 (X : CaseI_F4 T L V g D e) :
    kA T V (l⁻¹ * e * l) ≤ Subgroup.centralizer (centerOf (fsuU T V) : Set G) :=
  kA_le_centralizer fun _ hw => C.comm_zU_F4 X.h14325 X.h1222 X.h12813 (C.conj_mem_zIl_F4 X.he) hw

theorem caseI_rho_ne_F4 (X : CaseI_F4 T L V g D e) : D.ρ ⟨l⁻¹ * e * l, C.caseI_a_N_F4 D X⟩ ≠ 1 :=
  (C.rho_a_mem_F4 D X.h14325 X.h1222 X.h12213 X.h12810 X.h12813 X.he X.he1 _).2

omit [IsMulCommutative ↥V] C in

theorem caseI_rho_sq_F4 (X : CaseI_F4 T L V g D e)
    (hN : l⁻¹ * e * l ∈ Subgroup.normalizer (fsuU T V : Set G)) :
    D.ρ ⟨l⁻¹ * e * l, hN⟩ * D.ρ ⟨l⁻¹ * e * l, hN⟩ = 1 := by
  rw [← map_mul]
  have : (⟨l⁻¹ * e * l, hN⟩ : ↥(Subgroup.normalizer (fsuU T V : Set G))) *
      ⟨l⁻¹ * e * l, hN⟩ = 1 := Subtype.ext (by
    show l⁻¹ * e * l * (l⁻¹ * e * l) = 1
    rw [show l⁻¹ * e * l * (l⁻¹ * e * l) = l⁻¹ * (e * e) * l by group, X.he2]
    group)
  rw [this, map_one]

theorem caseI_zU_ne_bot_F4 (X : CaseI_F4 T L V g D e) :
    D.img (CFSG.conjugate (centerOf (fsuU T V)) g) ≠ ⊥ := by
  intro h
  have hmem := L128A.HatU.rho_mem_img D (C.conj_mem_zIl_F4 X.he).1 (C.caseI_a_N_F4 D X)
  rw [h, Subgroup.mem_bot] at hmem
  exact C.caseI_rho_ne_F4 D X hmem

theorem caseI_img_kA_F4 (X : CaseI_F4 T L V g D e) :
    D.img (kA T V (l⁻¹ * e * l)) =
      D.img (conjClosure (CFSG.conjugate (centerOf (fsuU T V)) g) (l32nH T V)) := by
  have hZgH := L14332.conj_zU_le_F4 X.h12813 C.setting C.gP C.gN
  have hN := L14332.l32nH_le_normalizer_fsuU T V
  have ha := C.conj_mem_zIl_F4 X.he
  have haN := C.caseI_a_N_F4 D X
  set K := kA T V (l⁻¹ * e * l) with hK
  have hKK' : K ≤ conjClosure (CFSG.conjugate (centerOf (fsuU T V)) g) (l32nH T V) :=
    conjClosure_mono (Subgroup.zpowers_le.mpr ha.1) le_rfl
  apply le_antisymm
  · intro γ hγ
    obtain ⟨k, hk, hkN, rfl⟩ := (L128A.HatU.mem_img D).mp hγ
    exact L128A.HatU.rho_mem_img D (hKK' hk) hkN
  ·
    set S : Subgroup G := ((D.img K).comap D.ρ).map
      (Subgroup.normalizer (fsuU T V : Set G)).subtype with hS
    have hSmem : ∀ {y : G}, y ∈ S → ∀ hyN : y ∈ Subgroup.normalizer (fsuU T V : Set G),
        D.ρ ⟨y, hyN⟩ ∈ D.img K := by
      rintro y ⟨y', hy', rfl⟩ hyN
      exact hy'
    obtain ⟨-, h2, -⟩ := X.hi.zU (C.caseI_zU_ne_bot_F4 D X)
    have hZ2 : ∀ x ∈ CFSG.conjugate (centerOf (fsuU T V)) g,
        ∀ hxN : x ∈ Subgroup.normalizer (fsuU T V : Set G),
        D.ρ ⟨x, hxN⟩ = 1 ∨ D.ρ ⟨x, hxN⟩ = D.ρ ⟨l⁻¹ * e * l, haN⟩ := fun x hx hxN =>
      eq_one_or_eq_of_card_two h2 (L128A.HatU.rho_mem_img D ha.1 haN) (C.caseI_rho_ne_F4 D X)
        (L128A.HatU.rho_mem_img D hx hxN)
    have hK'S : conjClosure (CFSG.conjugate (centerOf (fsuU T V)) g) (l32nH T V) ≤ S := by
      refine conjClosure_le fun h hh x hx => ?_
      have hxH := hZgH hx
      have hy : h * x * h⁻¹ ∈ l32nH T V :=
        (l32nH T V).mul_mem ((l32nH T V).mul_mem hh hxH) ((l32nH T V).inv_mem hh)
      refine ⟨⟨h * x * h⁻¹, hN hy⟩, ?_, rfl⟩
      show D.ρ ⟨h * x * h⁻¹, hN hy⟩ ∈ D.img K
      have e1 : D.ρ ⟨h * x * h⁻¹, hN hy⟩ =
          D.ρ ⟨h, hN hh⟩ * D.ρ ⟨x, hN hxH⟩ * (D.ρ ⟨h, hN hh⟩)⁻¹ := by
        rw [← map_inv, ← map_mul, ← map_mul]
        rfl
      rcases hZ2 x hx (hN hxH) with h1 | h1
      · rw [e1, h1, mul_one, mul_inv_cancel]
        exact (D.img K).one_mem
      · have hcH : h * (l⁻¹ * e * l) * h⁻¹ ∈ l32nH T V :=
          (l32nH T V).mul_mem ((l32nH T V).mul_mem hh (C.caseI_a_H_F4 D X)) ((l32nH T V).inv_mem hh)
        have e2 : D.ρ ⟨h, hN hh⟩ * D.ρ ⟨l⁻¹ * e * l, haN⟩ * (D.ρ ⟨h, hN hh⟩)⁻¹ =
            D.ρ ⟨h * (l⁻¹ * e * l) * h⁻¹, hN hcH⟩ := by
          rw [← map_inv, ← map_mul, ← map_mul]
          rfl
        rw [e1, h1, e2]
        exact L128A.HatU.rho_mem_img D (mem_conjClosure hh (Subgroup.mem_zpowers _)) _
    intro γ hγ
    obtain ⟨k, hk, hkN, rfl⟩ := (L128A.HatU.mem_img D).mp hγ
    exact hSmem (hK'S hk) hkN

theorem caseI_exists_phi_F4 (X : CaseI_F4 T L V g D e) :
    ∃ φ : ↥(D.img (l32nH T V)) ≃* Equiv.Perm (Fin 3) × Equiv.Perm (Fin 3),
      (∀ k ∈ kA T V (l⁻¹ * e * l), ∀ hk : k ∈ l32nH T V,
        (φ (L14332.imgHom D ⟨k, hk⟩)).2 = 1) ∧
      ∀ s : Equiv.Perm (Fin 3), ∃ k ∈ kA T V (l⁻¹ * e * l), ∃ hk : k ∈ l32nH T V,
        (φ (L14332.imgHom D ⟨k, hk⟩)).1 = s := by
  set K := kA T V (l⁻¹ * e * l) with hK
  set Hd := D.img (l32nH T V) with hHd
  have hKH := C.caseI_K_H_F4 D X
  have hN := L14332.l32nH_le_normalizer_fsuU T V
  have haK : l⁻¹ * e * l ∈ K := le_conjClosure _ _ (Subgroup.mem_zpowers _)

  have himg : D.img K ≤ Hd := fun γ hγ => by
    obtain ⟨k, hk, hkN, rfl⟩ := (L128A.HatU.mem_img D).mp hγ
    exact L128A.HatU.rho_mem_img D (hKH hk) hkN
  have hconj : ∀ γ ∈ Hd, ∀ κ ∈ D.img K, γ * κ * γ⁻¹ ∈ D.img K := by
    intro γ hγ κ hκ
    obtain ⟨h, hh, hhN, rfl⟩ := (L128A.HatU.mem_img D).mp hγ
    obtain ⟨k, hk, hkN, rfl⟩ := (L128A.HatU.mem_img D).mp hκ
    have hmem : h * k * h⁻¹ ∈ K := (Subgroup.mem_normalizer_iff.mp (le_normalizer_kA _ hh) k).mp hk
    have e1 : D.ρ ⟨h, hhN⟩ * D.ρ ⟨k, hkN⟩ * (D.ρ ⟨h, hhN⟩)⁻¹ =
        D.ρ ⟨h * k * h⁻¹, hN (hKH hmem)⟩ := by
      rw [← map_inv, ← map_mul, ← map_mul]
      rfl
    rw [e1]
    exact L128A.HatU.rho_mem_img D hmem _
  have hnorm : Hd ≤ Subgroup.normalizer (D.img K : Set (D.V ≃ₗ[ZMod 2] D.V)) := by
    intro γ hγ
    rw [Subgroup.mem_normalizer_iff]
    intro κ
    refine ⟨fun hκ => hconj γ hγ κ hκ, fun hκ => ?_⟩
    have := hconj γ⁻¹ (Hd.inv_mem hγ) _ hκ
    rwa [show γ⁻¹ * (γ * κ * γ⁻¹) * γ⁻¹⁻¹ = κ by group] at this
  have hNn : ((D.img K).subgroupOf Hd).Normal := Subgroup.normal_subgroupOf_of_le_normalizer hnorm
  have h6 : Nat.card ((D.img K).subgroupOf Hd) = 6 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe himg).toEquiv, C.caseI_img_kA_F4 D X]
    obtain ⟨-, -, ⟨ψ⟩, -⟩ := X.hi.zU (C.caseI_zU_ne_bot_F4 D X)
    rw [Nat.card_congr ψ.toEquiv, Nat.card_perm, Nat.card_fin]
    rfl

  obtain ⟨φ₀⟩ := X.hi.iso
  set t : ↥Hd := ⟨D.ρ ⟨l⁻¹ * e * l, C.caseI_a_N_F4 D X⟩,
    L128A.HatU.rho_mem_img D (C.caseI_a_H_F4 D X) _⟩ with ht
  have htK : t ∈ (D.img K).subgroupOf Hd :=
    Subgroup.mem_subgroupOf.mpr (L128A.HatU.rho_mem_img D haK _)
  have ht2 : t * t = 1 := Subtype.ext (by
    show D.ρ ⟨l⁻¹ * e * l, C.caseI_a_N_F4 D X⟩ * D.ρ ⟨l⁻¹ * e * l, C.caseI_a_N_F4 D X⟩ = 1
    exact caseI_rho_sq_F4 D X _)
  have ht1 : t ≠ 1 := fun h => C.caseI_rho_ne_F4 D X (congrArg Subtype.val h)
  obtain ⟨φ, hφ2, hφ1⟩ := exists_mulEquiv_fst φ₀ hNn h6 htK ht2 ht1
  refine ⟨φ, fun k hk hkH => hφ2 _ ?_, fun s => ?_⟩
  · rw [Subgroup.mem_subgroupOf, L14332.imgHom_apply]
    exact L128A.HatU.rho_mem_img D hk _
  · obtain ⟨n, hn, hns⟩ := hφ1 s
    obtain ⟨k, hk, hkN, hkn⟩ := (L128A.HatU.mem_img D).mp (Subgroup.mem_subgroupOf.mp hn)
    refine ⟨k, hk, hKH hk, ?_⟩
    have : L14332.imgHom D ⟨k, hKH hk⟩ = n := Subtype.ext (by
      rw [L14332.imgHom_apply]
      exact hkn)
    rw [this]
    exact hns

theorem eq_one_of_mem_cHat_F4
    (hQ : centralizerMod (fsuV1 T V) (l32nH T V) (fsuU T V) = pCoreOf 2 (l32nH T V))
    {K : Subgroup G} (hKZ : K ≤ Subgroup.centralizer (centerOf (fsuU T V) : Set G))
    {c : G} (hcK : c ∈ K) (hcE : c ∈ l32nCHat T V) (hc : Odd (orderOf c)) : c = 1 := by
  have hU2 : IsPGroup 2 ↥(fsuU T V) := C.S.hH.sylow.1.to_le C.U_T

  have hcU : ∀ u ∈ fsuU T V, c * u * c⁻¹ = u := by
    intro u hu
    set d := c * u * c⁻¹ * u⁻¹ with hd
    have hdZ : d ∈ centerOf (fsuU T V) := hcE.2.2 u hu
    have hcd : c * d * c⁻¹ = d := by
      rw [← Subgroup.mem_centralizer_iff.mp (hKZ hcK) d hdZ, mul_inv_cancel_right]
    have hcu : c * u * c⁻¹ = d * u := by rw [hd]; group
    have h3 := L14332.pow_conj_eq hcd hcu (orderOf c)
    rw [pow_orderOf_eq_one, one_mul, inv_one, mul_one] at h3
    have hdo : d ^ orderOf c = 1 := by
      have : u * u⁻¹ = d ^ orderOf c * u * u⁻¹ := by rw [← h3]
      simpa using this.symm
    obtain ⟨k, hk⟩ := hU2 ⟨d, hdZ.1⟩
    have hd2 : d ^ (2 ^ k) = 1 := by simpa using congrArg Subtype.val hk
    have hd1 : d = 1 := orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes
      (Nat.Coprime.pow_left k (Nat.coprime_two_left.mpr hc))
      (orderOf_dvd_of_pow_eq_one hd2) (orderOf_dvd_of_pow_eq_one hdo))
    rw [hcu, hd1, one_mul]

  have hcQ : c ∈ pCoreOf 2 (l32nH T V) := by
    rw [← hQ]
    refine ⟨hcE.1, hcE.1, fun u hu => ?_⟩
    rw [hcU u hu, mul_inv_cancel]
    exact one_mem _
  obtain ⟨k, hk⟩ := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 (l32nH T V) ⟨c, hcQ⟩
  have hc2 : c ^ (2 ^ k) = 1 := by simpa using congrArg Subtype.val hk
  exact orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes
    (Nat.Coprime.pow_left k (Nat.coprime_two_left.mpr hc))
    (orderOf_dvd_of_pow_eq_one hc2) dvd_rfl)

theorem caseI_exists_chi_F4 (X : CaseI_F4 T L V g D e) :
    ∃ χ : ↥(kA T V (l⁻¹ * e * l) ⊔ T) →* Equiv.Perm (Fin 3), Function.Surjective χ ∧
      ∀ x : ↥(kA T V (l⁻¹ * e * l) ⊔ T), χ x = 1 → ∃ n : ℕ, (x : G) ^ 2 ^ n = 1 := by
  obtain ⟨φ, hφ2, hφ1⟩ := C.caseI_exists_phi_F4 D X
  set K := kA T V (l⁻¹ * e * l) with hK
  have hKH := C.caseI_K_H_F4 D X
  have hTH : T ≤ l32nH T V := C.setting.v1.2.2
  have hKTH : K ⊔ T ≤ l32nH T V := sup_le hKH hTH
  set χ : ↥(K ⊔ T) →* Equiv.Perm (Fin 3) :=
    (MonoidHom.fst _ _).comp (φ.toMonoidHom.comp
      ((L14332.imgHom D).comp (Subgroup.inclusion hKTH))) with hχ
  have hχapp : ∀ x : ↥(K ⊔ T), χ x = (φ (L14332.imgHom D ⟨x, hKTH x.2⟩)).1 := fun _ => rfl
  refine ⟨χ, fun s => ?_, fun x hx => ?_⟩
  · obtain ⟨k, hk, hkH, hks⟩ := hφ1 s
    exact ⟨⟨k, Subgroup.mem_sup_left hk⟩, by rw [hχapp]; exact hks⟩
  · have hT2 : IsPGroup 2 ↥T := C.S.hH.sylow.1
    have hTK : T ≤ Subgroup.normalizer (K : Set G) := hTH.trans (le_normalizer_kA _)
    have hodd : ∀ y ∈ χ.ker, Odd (orderOf y) → y = 1 := by
      intro y hy hyo
      have hyo' : Odd (orderOf (y : G)) := by rwa [Subgroup.orderOf_coe]
      have hyK : (y : G) ∈ K :=
        mem_of_odd_of_mem_sup hT2 hTK y.2 hyo' (pow_orderOf_eq_one _)
      have h2 := hφ2 _ hyK (hKTH y.2)
      have h1 : (φ (L14332.imgHom D ⟨y, hKTH y.2⟩)).1 = 1 := by
        rw [← hχapp]
        exact hy
      have hφy : φ (L14332.imgHom D ⟨y, hKTH y.2⟩) = 1 := Prod.ext h1 h2
      have himg1 : L14332.imgHom D ⟨y, hKTH y.2⟩ = 1 := φ.injective (hφy.trans φ.map_one.symm)
      have hyC : (y : G) ∈ l32nCHat T V := by
        refine (L14332.rho_eq_one_iff_mem (D := D) (hKTH y.2)
          (L14332.l32nH_le_normalizer_fsuU T V (hKTH y.2))).mp ?_
        have := congrArg Subtype.val himg1
        rwa [L14332.imgHom_apply] at this
      exact Subtype.ext (C.eq_one_of_mem_cHat_F4 X.hQ (C.caseI_K_Z_F4 D X) hyK hyC hyo')
    obtain ⟨n, hn⟩ := exists_two_pow_of_odd hodd hx
    exact ⟨n, by simpa using congrArg Subtype.val hn⟩

theorem caseI_quotient_KT_F4 (X : CaseI_F4 T L V g D e) :
    Nonempty (↥(kA T V (l⁻¹ * e * l) ⊔ T) ⧸ CFSG.Open.pCore 2 ↥(kA T V (l⁻¹ * e * l) ⊔ T) ≃*
      Equiv.Perm (Fin 3)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨χ, hs, hker2⟩ := C.caseI_exists_chi_F4 D X
  have hker : CFSG.Open.pCore 2 ↥(kA T V (l⁻¹ * e * l) ⊔ T) = χ.ker := by
    apply le_antisymm
    · have hn : ((CFSG.Open.pCore 2 ↥(kA T V (l⁻¹ * e * l) ⊔ T)).map χ).Normal :=
        Subgroup.Normal.map (CFSG.LieType.BorelTits.pCore_normal 2) _ hs
      have hp : IsPGroup 2 ↥((CFSG.Open.pCore 2 ↥(kA T V (l⁻¹ * e * l) ⊔ T)).map χ) :=
        (CFSG.LieType.BorelTits.pCore_isPGroup 2).map _
      have hbot := eq_bot_of_normal_isPGroup_perm3 hn hp
      intro x hx
      have : χ x ∈ (CFSG.Open.pCore 2 ↥(kA T V (l⁻¹ * e * l) ⊔ T)).map χ :=
        Subgroup.mem_map_of_mem _ hx
      rw [hbot, Subgroup.mem_bot] at this
      exact this
    · refine CFSG.LieType.BorelTits.le_pCore 2 (MonoidHom.normal_ker _) fun x => ?_
      obtain ⟨k, hk⟩ := hker2 _ x.2
      refine ⟨k, Subtype.ext (Subtype.ext ?_)⟩
      simpa using hk
  exact ⟨(QuotientGroup.quotientMulEquivOfEq hker).trans
    (QuotientGroup.quotientKerEquivOfSurjective _ hs)⟩

end Ctx_F4

end L14328

end CFSG.Quasithin.H13
