module

public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87NCDm12Aux
public import Certificates.Kernel.ThCent.Leaves

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Odd87

open Subgroup CFSG CFSG.ABGLocalTools CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.Stage12
  CFSG.GH74.GLS.Stage2.Local CFSG.GH74.GLS.Stage2.Local.P27 CFSG.GH74.GLS.Stage2.Signalizer.L52Two
  CFSG.GH74.GLS.Stage2.Signalizer.Odd87.NCDm12

section Res

variable {G : Type} [Group G] [Finite G]

theorem NCDm12.resEq_of_le_m12 {x : G} {T : Subgroup G}
    (hT : IsSylowOf 2 T (centralizer ({x} : Set G)))
    (hle : oPrimeResidualOf 2 (centralizer ({x} : Set G)) ⊔ pPrimeCoreOf 2 (centralizer ({x} : Set G)) ≤
      pPrimeCoreOf 2 (centralizer ({x} : Set G)) ⊔ Jx x ⊔ T) :
    oPrimeResidualOf 2 (centralizer ({x} : Set G)) ⊔ pPrimeCoreOf 2 (centralizer ({x} : Set G)) =
      pPrimeCoreOf 2 (centralizer ({x} : Set G)) ⊔ Jx x ⊔ T := by
  refine le_antisymm hle (sup_le (sup_le le_sup_right ?_) ?_)
  · exact le_sup_of_le_left (le_oPrimeResidualOf_of_perfect (P34.Jx_le_centralizer x)
      (pLayerOf_two_perfect_P27 _))
  · exact le_sup_of_le_left (le_oPrimeResidualOf_of_isPGroup' hT.le hT.isPGroup)

end Res

section Main

variable {G : Type} [Group G] [Finite G]

theorem fullG_of_m12 {x : G} (hx2 : orderOf x = 2) (hM : M12NonCentral x) : P27.FullG x := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨K, y, q, hKc, hKL2, hq8, hyC, hy2', hPGL, hxy', hRO, -⟩ := hM
  have hq : Odd q := Nat.odd_iff.2 (by omega)
  have hq5 : 5 ≤ q := five_le_of_isL2 hKc hKL2 hq8
  have hKy : ∀ k ∈ K, y * k * y⁻¹ ∈ K := P27M12.normalizes_of_pgl hq hq5 hKL2 hPGL
  have hyK : y ∉ K := not_mem_of_pgl hq hq5 hKL2 hPGL
  have hxy : x * y = y * x := (Subgroup.mem_centralizer_singleton_iff.1 hyC).symm
  have hx2' : x * x = 1 := by
    have := pow_orderOf_eq_one x
    rwa [hx2, pow_two] at this
  have hy2 : y * y = 1 := by
    have := pow_orderOf_eq_one y
    rwa [hy2', pow_two] at this
  have hx1 : x ≠ 1 := fun h => by rw [h, orderOf_one] at hx2; omega
  have hy1 : y ≠ 1 := fun h => by rw [h, orderOf_one] at hy2'; omega
  have hxL : x ∉ K ⊔ zpowers y := by
    intro hx
    have h : x ∈ zpowers x ⊓ (K ⊔ zpowers y) := ⟨Subgroup.mem_zpowers x, hx⟩
    rw [hxy', Subgroup.mem_bot] at h
    exact hx1 h
  have hne : x ≠ y := by
    intro h
    apply hxL
    rw [h]
    exact Subgroup.mem_sup_right (Subgroup.mem_zpowers y)
  have hxC : x ∈ centralizer ({x} : Set G) := Subgroup.mem_centralizer_singleton_iff.2 rfl
  have hKC : K ≤ centralizer ({x} : Set G) := hKc.1
  have hJ : Jx x ≤ pPrimeCoreOf 2 (centralizer ({x} : Set G)) ⊔ K :=
    P27M12.Jx_le_sup hx2' hy2 hxy hKC hyC hKy hRO
  have hKJ : K ≤ Jx x := le_sSup hKc
  have hL2J := P27M12.isL2_Jx hKc hKJ hJ hKL2
  have hT₁C : fourSg x y ≤ centralizer ({x} : Set G) :=
    (Subgroup.closure_le _).2 (Set.insert_subset_iff.2 ⟨hxC, Set.singleton_subset_iff.2 hyC⟩)
  obtain ⟨T, hT, hT₁T⟩ := exists_isSylowOf_ge hT₁C (isPGroup_fourSg hx2' hy2 hxy hx1 hy1 hne)
  have hxT : x ∈ T := hT₁T (x_mem_fourSg x y)
  have hyT : y ∈ T := hT₁T (y_mem_fourSg x y)
  have hle : oPrimeResidualOf 2 (centralizer ({x} : Set G)) ⊔ pPrimeCoreOf 2 (centralizer ({x} : Set G)) ≤
      pPrimeCoreOf 2 (centralizer ({x} : Set G)) ⊔ Jx x ⊔ T := by
    rw [hRO]
    have hO : pPrimeCoreOf 2 (centralizer ({x} : Set G)) ≤
        pPrimeCoreOf 2 (centralizer ({x} : Set G)) ⊔ Jx x ⊔ T := le_sup_left.trans le_sup_left
    have hxle : zpowers x ≤ pPrimeCoreOf 2 (centralizer ({x} : Set G)) ⊔ Jx x ⊔ T :=
      ((Subgroup.zpowers_le).2 hxT).trans le_sup_right
    have hKle : K ≤ pPrimeCoreOf 2 (centralizer ({x} : Set G)) ⊔ Jx x ⊔ T :=
      hKJ.trans (le_sup_right.trans le_sup_left)
    have hyle : zpowers y ≤ pPrimeCoreOf 2 (centralizer ({x} : Set G)) ⊔ Jx x ⊔ T :=
      ((Subgroup.zpowers_le).2 hyT).trans le_sup_right
    exact sup_le (sup_le hO hxle) (sup_le hKle hyle)
  have hres := NCDm12.resEq_of_le_m12 hT hle
  have hTQ : T ≤ pPrimeCoreOf 2 (centralizer ({x} : Set G)) ⊔ zpowers x ⊔ (K ⊔ zpowers y) := by
    rw [← hRO, hres]
    exact le_sup_right
  have hxK : ∀ k ∈ K, x * k = k * x := fun k hk =>
    (Subgroup.mem_centralizer_singleton_iff.1 (hKC hk)).symm
  have hxK' : ∀ k ∈ K, x * k * x⁻¹ ∈ K := fun k hk => by
    have h : x * k * x⁻¹ = k := by rw [hxK k hk]; group
    rwa [h]
  have hxn : x ∈ normalizer ((pPrimeCoreOf 2 (centralizer ({x} : Set G)) ⊔ K : Subgroup G) : Set G) :=
    P27M12.mem_normalizer_of_involution hx2'
      (P27M12.conj_mem_sup (fun o ho => TwoThin.pPrimeCoreOf_normalized _ hxC ho) hxK')
  have hyn : y ∈ normalizer ((pPrimeCoreOf 2 (centralizer ({x} : Set G)) ⊔ K : Subgroup G) : Set G) :=
    P27M12.mem_normalizer_of_involution hy2
      (P27M12.conj_mem_sup (fun o ho => TwoThin.pPrimeCoreOf_normalized _ hyC ho) hKy)
  have hT₁n : fourSg x y ≤
      normalizer ((pPrimeCoreOf 2 (centralizer ({x} : Set G)) ⊔ K : Subgroup G) : Set G) :=
    (Subgroup.closure_le _).2 (Set.insert_subset_iff.2 ⟨hxn, Set.singleton_subset_iff.2 hyn⟩)
  have hsup : (T ⊓ Jx x) ⊔ fourSg x y = T := by
    refine le_antisymm (sup_le inf_le_left hT₁T) fun t ht => ?_
    have hQle : pPrimeCoreOf 2 (centralizer ({x} : Set G)) ⊔ zpowers x ⊔ (K ⊔ zpowers y) ≤
        (pPrimeCoreOf 2 (centralizer ({x} : Set G)) ⊔ K) ⊔ fourSg x y :=
      sup_le (sup_le (le_sup_left.trans le_sup_left)
          (((Subgroup.zpowers_le).2 (x_mem_fourSg x y)).trans le_sup_right))
        (sup_le (le_sup_right.trans le_sup_left)
          (((Subgroup.zpowers_le).2 (y_mem_fourSg x y)).trans le_sup_right))
    have h1 : t ∈ (pPrimeCoreOf 2 (centralizer ({x} : Set G)) ⊔ K) ⊔ fourSg x y := hQle (hTQ ht)
    rw [← SetLike.mem_coe, Subgroup.coe_mul_of_right_le_normalizer_left _ _ hT₁n] at h1
    obtain ⟨m, hm, u, hu, rfl⟩ := Set.mem_mul.1 h1
    have hmT : m ∈ T := by
      have h := T.mul_mem ht (T.inv_mem (hT₁T hu))
      rwa [mul_inv_cancel_right] at h
    have hmNJ : m ∈ pPrimeCoreOf 2 (centralizer ({x} : Set G)) ⊔ Jx x := sup_le_sup_left hKJ _ hm
    have hmJ : m ∈ Jx x :=
      inf_sup_le_of_normalizes (N := pPrimeCoreOf 2 (centralizer ({x} : Set G))) (J := Jx x) (T := T)
        (C := centralizer ({x} : Set G)) (le_normalizer_pPrimeCoreOf_two _) (P34.Jx_le_centralizer x)
        (le_normalizer_pLayerOf _) hT.le (TwoThin.card_pPrimeCoreOf_odd _) hT.isPGroup
        (Subgroup.mem_inf.2 ⟨hmT, hmNJ⟩)
    exact Subgroup.mul_mem_sup ⟨hmT, hmJ⟩ hu
  have hinf : fourSg x y ⊓ Jx x = ⊥ := by
    have h := fourSg_inf_le_bot (N := pPrimeCoreOf 2 (centralizer ({x} : Set G))) (K := K)
      (TwoThin.card_pPrimeCoreOf_odd _)
      (fun k hk => le_normalizer_pPrimeCoreOf_two _ (hKC hk)) hx2' hy2 hxy hxK hKy hyK hxL
    rw [eq_bot_iff]
    intro g hg
    obtain ⟨hg1, hg2⟩ := Subgroup.mem_inf.1 hg
    exact h.le (Subgroup.mem_inf.2 ⟨hg1, hJ hg2⟩)
  exact fullG_of_data hT hx2 hres
    ⟨fourSg x y, hT₁T, hsup, hinf, x_mem_fourSg x y, isDihedral_fourSg hx2' hy2 hxy hx1 hy1 hne⟩
    (isDihedral_inf_Jx hT hq hL2J)

end Main

end CFSG.GH74.GLS.Stage2.Signalizer.Odd87
