module

public import CFSG.CGT.PushingUpLit.T2K.FourFiveD

public section

namespace CFSG.CGT.PushingUpLit.T2K

open CFSG CFSG.RankThree.PartOne CFSG.Open CFSG.Quasithin CFSG.CGT.PushingUpLit.BHS
  CFSG.Quasithin.JonesParshall
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {L M T A : Subgroup G} {n : ℕ}

namespace Hyp45

variable (H : Hyp45 L M T A n)
include H

theorem bGrp_eq (hS : IsElemAbelian 2 (T ⊓ Subgroup.centralizer (L : Set G))) :
    bGrp L A = (T ⊓ Subgroup.centralizer (L : Set G)) ⊔ blockU L := by
  unfold bGrp
  rw [H.inf_centralizer_eq, H.inf_centralizer_L_eq hS]
  apply le_antisymm
  · exact sup_le (sup_le le_sup_left (inf_le_left.trans le_sup_right)) le_sup_right
  · exact sup_le (le_sup_left.trans le_sup_left) le_sup_right

theorem comm_mem_bGrp (hS : IsElemAbelian 2 (T ⊓ Subgroup.centralizer (L : Set G)))
    {p a : G} (hp : p ∈ T ⊓ Subgroup.centralizer (blockU L : Set G)) (ha : a ∈ A) :
    ⁅p, a⁆ ∈ bGrp L A := by
  set l := H.lOf ⟨a, ha⟩ with hl
  have hlL : l ∈ L := H.lOf_mem ⟨a, ha⟩
  have hu : l⁻¹ * a ∈ T ⊓ Subgroup.centralizer (blockU L : Set G) := H.tOf_mem ⟨a, ha⟩
  have hpM : p ∈ M ⊓ Subgroup.centralizer (blockU L : Set G) := ⟨H.sylow.le hp.1, hp.2⟩
  have huM : l⁻¹ * a ∈ M ⊓ Subgroup.centralizer (blockU L : Set G) :=
    ⟨H.sylow.le hu.1, hu.2⟩
  have h1 : ⁅p, l⁆ ∈ blockU L := H.block.comm_centralizer_mem_blockU H.normal hpM l hlL
  have h2 : ⁅p, l⁻¹ * a⁆ ∈ Subgroup.centralizer (L : Set G) :=
    H.block.comm_mem_centralizer H.normal hpM huM
  have h2T : ⁅p, l⁻¹ * a⁆ ∈ T := by
    simp only [commutatorElement_def]
    exact T.mul_mem (T.mul_mem (T.mul_mem hp.1 hu.1) (T.inv_mem hp.1)) (T.inv_mem hu.1)
  have hS' : ⁅p, l⁻¹ * a⁆ ∈ T ⊓ Subgroup.centralizer (L : Set G) := ⟨h2T, h2⟩
  have hlc : l * ⁅p, l⁻¹ * a⁆ * l⁻¹ = ⁅p, l⁻¹ * a⁆ := by
    exact mul_inv_eq_iff_eq_mul.2 (Subgroup.mem_centralizer_iff.1 h2 l hlL)
  have e : ⁅p, a⁆ = ⁅p, l⁆ * (l * ⁅p, l⁻¹ * a⁆ * l⁻¹) := by
    simp only [commutatorElement_def]
    group
  rw [e, hlc, H.bGrp_eq hS]
  exact Subgroup.mul_mem _ (Subgroup.mem_sup_right h1) (Subgroup.mem_sup_left hS')

theorem comm_P_mem_A (hS : IsElemAbelian 2 (T ⊓ Subgroup.centralizer (L : Set G)))
    (hSn : T ≤ Subgroup.normalizer ((T ⊓ Subgroup.centralizer (L : Set G) : Subgroup G) : Set G))
    {p a : G} (hp : p ∈ T ⊓ Subgroup.centralizer (blockU L : Set G)) (ha : a ∈ A) :
    ⁅p, a⁆ ∈ A := by
  classical
  set S : Subgroup G := T ⊓ Subgroup.centralizer (L : Set G) with hSdef
  have hSA : S ≤ A := H.S_le_A hS
  by_cases haV : a ∈ Subgroup.centralizer (blockU L : Set G)
  ·
    have haCV : a ∈ A ⊓ Subgroup.centralizer (blockU L : Set G) := ⟨ha, haV⟩
    rw [H.inf_centralizer_eq] at haCV
    have hcomm : ∀ x ∈ A ⊓ Subgroup.centralizer (L : Set G), ∀ y ∈ blockU L ⊓ A,
        x * y = y * x := fun x hx y hy =>
      (Subgroup.mem_centralizer_iff.1 hx.2 y (blockU_le L hy.1)).symm
    obtain ⟨c, hc, v, hv, rfl⟩ := exists_mul_of_mem_sup' hcomm haCV
    have hcS : c ∈ S := by
      have := H.inf_centralizer_L_eq hS
      rw [this] at hc
      exact hc
    have hpv : p * v = v * p := (Subgroup.mem_centralizer_iff.1 hp.2 v hv.1).symm
    have hvp : v * p⁻¹ = p⁻¹ * v := by
      calc v * p⁻¹ = p⁻¹ * (p * v) * p⁻¹ := by group
        _ = p⁻¹ * (v * p) * p⁻¹ := by rw [hpv]
        _ = p⁻¹ * v := by group
    have e : ⁅p, c * v⁆ = ⁅p, c⁆ := by
      simp only [commutatorElement_def]
      calc p * (c * v) * p⁻¹ * (c * v)⁻¹ = p * c * (v * p⁻¹) * v⁻¹ * c⁻¹ := by group
        _ = p * c * (p⁻¹ * v) * v⁻¹ * c⁻¹ := by rw [hvp]
        _ = p * c * p⁻¹ * c⁻¹ := by group
    rw [e]
    have h1 : p * c * p⁻¹ ∈ S := (Subgroup.mem_normalizer_iff.1 (hSn hp.1) c).1 hcS
    exact hSA (S.mul_mem h1 (S.inv_mem hcS))
  ·
    set b := ⁅p, a⁆ with hb
    have hbB : b ∈ bGrp L A := H.comm_mem_bGrp hS hp ha
    have ha2 : a * a = 1 := by
      have := H.A_isElemAbelian.2 a ha
      rwa [pow_two] at this
    have hai : a⁻¹ = a := inv_eq_of_mul_eq_one_right ha2
    have hb2 : b * b = 1 := by
      have := H.B_isElemAbelian.2 b hbB
      rwa [pow_two] at this
    have hbi : b⁻¹ = b := inv_eq_of_mul_eq_one_right hb2
    have hinv : a * b * a⁻¹ = b⁻¹ := by
      have e1 : a * b * a⁻¹ = a * p * a * p⁻¹ * a⁻¹ * a⁻¹ := by
        rw [hb]; simp only [commutatorElement_def]; group
      have e2 : b⁻¹ = a * p * a⁻¹ * p⁻¹ := by
        rw [hb]; simp only [commutatorElement_def]; group
      rw [e1, e2, hai]
      calc a * p * a * p⁻¹ * a * a = a * p * a * p⁻¹ * (a * a) := by group
        _ = a * p * a * p⁻¹ := by rw [ha2, mul_one]
    have hab : a * b = b * a := by
      have : a * b * a⁻¹ = b := by rw [hinv, hbi]
      exact mul_inv_eq_iff_eq_mul.1 this
    have hcommSV : ∀ x ∈ S, ∀ y ∈ blockU L, x * y = y * x := fun x hx y hy =>
      (Subgroup.mem_centralizer_iff.1 hx.2 y (blockU_le L hy)).symm
    have hbB' : b ∈ S ⊔ blockU L := by rwa [H.bGrp_eq hS] at hbB
    obtain ⟨s, hs, v, hv, hsv⟩ := exists_mul_of_mem_sup' hcommSV hbB'
    have has : a * s = s * a := H.A_comm ha (hSA hs)
    have hav : a * v = v * a := by
      have h1 : a * (s * v) = (s * v) * a := by rw [← hsv]; exact hab
      have h2 : s * (a * v) = s * (v * a) := by
        calc s * (a * v) = (s * a) * v := by group
          _ = (a * s) * v := by rw [has]
          _ = a * (s * v) := by group
          _ = (s * v) * a := h1
          _ = s * (v * a) := by group
      exact mul_left_cancel h2
    obtain ⟨l, hl, hact⟩ := H.acts_as a ha
    have hfix : ((H.rho ⟨a, ha⟩ : Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 n)) :
        Matrix (Fin 2) (Fin 2) (GaloisField 2 n)).mulVec (H.block.natData.ψe v) =
          H.block.natData.ψe v := by
      rw [H.rho_apply_eq (a := ⟨a, ha⟩) hl hact, ← H.block.natData.ψe_conj hl hv]
      have h1 : l * v * l⁻¹ = v := by
        rw [← hact v hv]
        calc a * v * a⁻¹ = (v * a) * a⁻¹ := by rw [hav]
          _ = v := by group
      rw [h1]
    have hvA := H.mem_centralizer_of_fixed_one ha haV hv hfix
    rw [H.centralizer_blockU_eq] at hvA
    rw [hsv]
    exact A.mul_mem (hSA hs) hvA.2

theorem P_le_normalizer (hS : IsElemAbelian 2 (T ⊓ Subgroup.centralizer (L : Set G)))
    (hSn : T ≤ Subgroup.normalizer ((T ⊓ Subgroup.centralizer (L : Set G) : Subgroup G) : Set G)) :
    T ⊓ Subgroup.centralizer (blockU L : Set G) ≤ Subgroup.normalizer (A : Set G) := by
  have hfwd : ∀ q ∈ T ⊓ Subgroup.centralizer (blockU L : Set G), ∀ a ∈ A, q * a * q⁻¹ ∈ A := by
    intro q hq a ha
    have e : q * a * q⁻¹ = ⁅q, a⁆ * a := by simp only [commutatorElement_def]; group
    rw [e]
    exact A.mul_mem (H.comm_P_mem_A hS hSn hq ha) ha
  intro p hp
  rw [Subgroup.mem_normalizer_iff]
  intro a
  refine ⟨hfwd p hp a, fun h => ?_⟩
  have hp' : p⁻¹ ∈ T ⊓ Subgroup.centralizer (blockU L : Set G) :=
    (T ⊓ Subgroup.centralizer (blockU L : Set G)).inv_mem hp
  have := hfwd p⁻¹ hp' _ h
  simpa [mul_assoc] using this

theorem inf_L_le_normalizer (hS : IsElemAbelian 2 (T ⊓ Subgroup.centralizer (L : Set G)))
    (hSn : T ≤ Subgroup.normalizer ((T ⊓ Subgroup.centralizer (L : Set G) : Subgroup G) : Set G)) :
    T ⊓ L ≤ Subgroup.normalizer (A : Set G) := by
  intro r hr
  let D := H.block.natData
  have hφ : D.φ ⟨r, hr.2⟩ ∈ H.rho.range := by
    rw [H.rho_range_eq]
    exact ⟨⟨r, hr.2⟩, Subgroup.mem_subgroupOf.2 hr, rfl⟩
  obtain ⟨a, ha⟩ := hφ
  have hlL := H.lOf_mem a
  have h1 : H.rho a = D.φ ⟨H.lOf a, hlL⟩ := H.rho_apply_eq hlL (H.actsAs_lOf a)
  have h2 : D.φ ⟨r, hr.2⟩ = D.φ ⟨H.lOf a, hlL⟩ := by rw [← ha, h1]
  have h3 : r⁻¹ * H.lOf a ∈ oTwoIn L := by
    refine (D.φ_ker ⟨r⁻¹ * H.lOf a, L.mul_mem (L.inv_mem hr.2) hlL⟩).1 ?_
    have e : (⟨r⁻¹ * H.lOf a, L.mul_mem (L.inv_mem hr.2) hlL⟩ : ↥L) =
        (⟨r, hr.2⟩ : ↥L)⁻¹ * ⟨H.lOf a, hlL⟩ := rfl
    rw [e, map_mul, map_inv, h2, inv_mul_cancel]
  have h4 : r⁻¹ * H.lOf a ∈ Subgroup.centralizer (blockU L : Set G) := by
    have := H.block.inf_centralizer_blockU
    rw [← this] at h3
    exact h3.2
  have h5 := H.tOf_mem a
  have hu : r⁻¹ * (a : G) ∈ T ⊓ Subgroup.centralizer (blockU L : Set G) := by
    refine ⟨T.mul_mem (T.inv_mem hr.1) (H.A_le_T a.2), ?_⟩
    have e : r⁻¹ * (a : G) = (r⁻¹ * H.lOf a) * ((H.lOf a)⁻¹ * (a : G)) := by group
    rw [e]
    exact Subgroup.mul_mem _ h4 h5.2
  have hP := H.P_le_normalizer hS hSn
  have hr' : r = (a : G) * (r⁻¹ * (a : G))⁻¹ := by group
  rw [hr']
  exact Subgroup.mul_mem _ (Subgroup.le_normalizer a.2) (Subgroup.inv_mem _ (hP hu))

theorem T₁_le_normalizer (hS : IsElemAbelian 2 (T ⊓ Subgroup.centralizer (L : Set G)))
    (hSn : T ≤ Subgroup.normalizer ((T ⊓ Subgroup.centralizer (L : Set G) : Subgroup G) : Set G)) :
    (T ⊓ L) ⊔ (T ⊓ Subgroup.centralizer (blockU L : Set G)) ≤ Subgroup.normalizer (A : Set G) :=
  sup_le (H.inf_L_le_normalizer hS hSn) (H.P_le_normalizer hS hSn)

end Hyp45

end CFSG.CGT.PushingUpLit.T2K
