module

public import CFSG.Quasithin.H13.L32NLem14331c
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.L32NLem14330e
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.L32NLem14331b

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.QuasithinUnique

namespace L14328

open L14331

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G] {T L V V₂ : Subgroup G} [IsMulCommutative ↥V]

namespace Ctx_F4
open Ctx
open CFSG.Quasithin.H13.L14328.Ctx_F4

variable {g z b l : G} (C : Ctx_F4 G T L V V₂ g z b l) (D : HatModelU (fsuU T V))
include C

theorem exists_e_F4 (h14325 : Lemma14325One_F4) (h1222 : Stmt12_2_2_F4) (h12213 : Stmt12_2_13_F4)
    (h12810 : Lemma12_8_10_F4) (h12813 : Lemma12_8_13_F4)
    (hne : centerOf (i128 T L V (fsuV1 T V)) ≠ ⊥) :
    ∃ e ∈ centerOf (i128 T L V (fsuV1 T V)), e ≠ 1 ∧ e * e = 1 := by
  obtain ⟨e, he1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hne
  refine ⟨e, e.2, fun h => he1 (Subtype.ext h), ?_⟩
  have hle := C.card_zI_le_F4 h14325 h1222 h12213 h12810 h12813
  have hpos : 1 < Nat.card ↥(centerOf (i128 T L V (fsuV1 T V))) := by
    rw [Finite.one_lt_card_iff_nontrivial]
    exact ⟨⟨e, 1, he1⟩⟩
  have h2 : Nat.card ↥(centerOf (i128 T L V (fsuV1 T V))) = 2 := by omega
  have := pow_card_eq_one' (G := ↥(centerOf (i128 T L V (fsuV1 T V)))) (x := e)
  rw [h2, pow_two] at this
  exact congrArg Subtype.val this

theorem conj_mem_zIl_F4 {e : G} (he : e ∈ centerOf (i128 T L V (fsuV1 T V))) :
    l⁻¹ * e * l ∈ CFSG.conjugate (centerOf (fsuU T V)) g ⊓
      CFSG.conjugate (centerOf (fsuU T V)) l := by
  rw [← C.zIl_eq_F4, mem_conj_iff, show l * (l⁻¹ * e * l) * l⁻¹ = e by group]
  exact he

theorem false_of_closure_F4 (h14325 : Lemma14325One_F4) (h1222 : Stmt12_2_2_F4)
    (h12813 : Lemma12_8_13_F4)
    (hQ : centralizerMod (fsuV1 T V) (l32nH T V) (fsuU T V) = pCoreOf 2 (l32nH T V))
    (hm3 : CFSG.Open.pRank 3 (⊤ : Subgroup ↥(l32nH T V)) ≤ 2) {e : G}
    (he : e ∈ centerOf (i128 T L V (fsuV1 T V))) (he1 : e ≠ 1)
    (hP : ∀ hN : l⁻¹ * e * l ∈ Subgroup.normalizer (fsuU T V : Set G),
      ClosureProp (D.img (l32nH T V)) (D.ρ ⟨l⁻¹ * e * l, hN⟩)) : False := by
  have := L14332.finite_linearEquiv D
  have ha := C.conj_mem_zIl_F4 he
  have haH : l⁻¹ * e * l ∈ l32nH T V := L14332.conj_zU_le_F4 h12813 C.setting C.gP C.gN ha.1
  have haN := L14332.l32nH_le_normalizer_fsuU T V haH
  set K := kA T V (l⁻¹ * e * l) with hK
  have hKH : K ≤ l32nH T V := kA_le haH
  have hHK : l32nH T V ≤ Subgroup.normalizer (K : Set G) := le_normalizer_kA _
  have hKZ : K ≤ Subgroup.centralizer (centerOf (fsuU T V) : Set G) :=
    kA_le_centralizer fun w hw => C.comm_zU_F4 h14325 h1222 h12813 ha hw
  have heZ : e ∈ centerOf (fsuU T V) := by
    rw [C.zI] at he
    exact he.1

  have hKN : ∀ {k : G}, k ∈ K → k ∈ Subgroup.normalizer (fsuU T V : Set G) := fun hk =>
    L14332.l32nH_le_normalizer_fsuU T V (hKH hk)
  have himg : D.img K ≤ D.img (l32nH T V) := by
    intro γ hγ
    obtain ⟨k, hk, hkN, rfl⟩ := (L128A.HatU.mem_img D).mp hγ
    exact L128A.HatU.rho_mem_img D (hKH hk) hkN
  have hconj : ∀ γ ∈ D.img (l32nH T V), ∀ κ ∈ D.img K, γ * κ * γ⁻¹ ∈ D.img K := by
    intro γ hγ κ hκ
    obtain ⟨h, hh, hhN, rfl⟩ := (L128A.HatU.mem_img D).mp hγ
    obtain ⟨k, hk, hkN, rfl⟩ := (L128A.HatU.mem_img D).mp hκ
    have hmem : h * k * h⁻¹ ∈ K := (Subgroup.mem_normalizer_iff.mp (hHK hh) k).mp hk
    have e1 : D.ρ ⟨h, hhN⟩ * D.ρ ⟨k, hkN⟩ * (D.ρ ⟨h, hhN⟩)⁻¹ =
        D.ρ ⟨h * k * h⁻¹, hKN hmem⟩ := by
      rw [← map_inv, ← map_mul, ← map_mul]
      rfl
    rw [e1]
    exact L128A.HatU.rho_mem_img D hmem (hKN hmem)
  have hnorm : D.img (l32nH T V) ≤ Subgroup.normalizer (D.img K : Set (D.V ≃ₗ[ZMod 2] D.V)) := by
    intro γ hγ
    rw [Subgroup.mem_normalizer_iff]
    intro κ
    refine ⟨fun hκ => hconj γ hγ κ hκ, fun hκ => ?_⟩
    have := hconj γ⁻¹ ((D.img (l32nH T V)).inv_mem hγ) _ hκ
    rwa [show γ⁻¹ * (γ * κ * γ⁻¹) * γ⁻¹⁻¹ = κ by group] at this
  have haK : D.ρ ⟨l⁻¹ * e * l, haN⟩ ∈ D.img K :=
    L128A.HatU.rho_mem_img D (le_conjClosure _ _ (Subgroup.mem_zpowers _)) haN
  obtain ⟨hP1, s₁, hs₁, s₂, hs₂, h₁, h₂, h12, h21⟩ := hP haN (D.img K) himg hnorm haK

  have hK3 := C.not_three_dvd_inf_F4 hQ hKZ
  set f : ↥K →* (D.V ≃ₗ[ZMod 2] D.V) :=
    D.ρ.comp (Subgroup.inclusion fun k hk => hKN hk) with hf
  have hfk : ∀ k : ↥K, f k = 1 ↔ (k : G) ∈ l32nCHat T V := fun k =>
    L14332.rho_eq_one_iff_mem (hKH k.2) (hKN k.2)
  have hker : Nat.card f.ker = Nat.card ↥(K ⊓ l32nCHat T V) := by
    have e1 : f.ker = (K ⊓ l32nCHat T V).subgroupOf K := by
      ext k
      rw [MonoidHom.mem_ker, hfk, Subgroup.mem_subgroupOf]
      exact ⟨fun h => ⟨k.2, h⟩, fun h => h.2⟩
    rw [e1, Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv]
  have hrange : ∀ {s}, s ∈ D.img K → s ∈ f.range := by
    intro s hs
    obtain ⟨k, hk, hkN, rfl⟩ := (L128A.HatU.mem_img D).mp hs
    exact ⟨⟨k, hk⟩, rfl⟩
  obtain ⟨S₀, hS9, hScomm, hS3, hSinj⟩ := exists_lift_e9 f (by rwa [hker]) (hrange hs₁)
    (hrange hs₂) h₁ h₂ h12 h21
  set S : Subgroup G := S₀.map K.subtype with hS
  have hSK : S ≤ K := by
    rintro _ ⟨k, -, rfl⟩
    exact k.2
  have hS9' : Nat.card S = 9 := by
    rw [hS, Subgroup.card_map_of_injective K.subtype_injective, hS9]
  have hScomm' : ∀ x ∈ S, ∀ y ∈ S, x * y = y * x := by
    rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    exact congrArg Subtype.val (hScomm x hx y hy)
  have hS3' : ∀ x ∈ S, x ^ 3 = 1 := by
    rintro _ ⟨x, hx, rfl⟩
    exact congrArg Subtype.val (hS3 x hx)
  have hSN : S ⊓ l32nCHat T V = ⊥ := by
    rw [eq_bot_iff]
    rintro _ ⟨⟨x, hx, rfl⟩, hxE⟩
    exact Subgroup.mem_bot.mpr (congrArg Subtype.val (hSinj x hx ((hfk x).mpr hxE)))

  have hN3 : ¬ 3 ∣ Nat.card ↥(l32nCHat T V) := by
    intro h3N
    obtain ⟨E, hEH, hE, hE27⟩ := exists_e27 hKH (centralizerMod_le_left _ _ _) hHK
      (le_normalizer_cHat D) hK3 hSK hS9' hScomm' hS3' hSN h3N
    have hle := CFSG.SectionRank.le_pRank_of_injective (A := ↥E) (p := 3) (by norm_num)
      (fun x y => hE.1.is_comm.comm x y) (fun x => Subtype.ext (hE.2 x x.2))
      hE27 (Subgroup.inclusion hEH) (Subgroup.inclusion_injective hEH)
      (H := (⊤ : Subgroup ↥(l32nH T V))) le_top
    omega

  obtain ⟨x, hxL, hx3, hxz, hxa⟩ := C.exists_x_F4
  have hxH : x ∈ l32nH T V := C.mem_normalizer_V1_F4 hxz
  have hxK : x ∈ K := by
    refine mem_of_rho_mem D hKH hHK hN3 hxH hx3 (hP1 _ (L128A.HatU.rho_mem_img D hxH _) ?_)
    rw [← map_pow]
    have : (⟨x, L14332.l32nH_le_normalizer_fsuU T V hxH⟩ :
        ↥(Subgroup.normalizer (fsuU T V : Set G))) ^ 3 = 1 := Subtype.ext hx3
    rw [this, map_one]
  have hxe : x * e * x⁻¹ = e := by
    rw [← Subgroup.mem_centralizer_iff.mp (hKZ hxK) e heZ, mul_inv_cancel_right]
  exact he1 (C.eq_one_of_conj_F4 h14325 h1222 he (C.L_le_F4 hxL) hxa hxe)

end Ctx_F4

end L14328

end CFSG.Quasithin.H13
