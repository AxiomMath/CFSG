module

public import CFSG.LocalAnalysis.EvenBN.U5.LinS2aBasic
public import CFSG.LocalAnalysis.EvenBN.U5.LinS2aTI
public import CFSG.LocalAnalysis.EvenBN.U5.LinS2aZ

public noncomputable section

namespace CFSG.LocalAnalysis.EvenBN.U5

open Subgroup CFSG.Open CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
open CFSG.Blueprint
open CFSG.ABGLocalTools (IsSylowOf)
open CFSG.LocalAnalysis.EvenBN.Common.NormalizerQuotient
open scoped MatrixGroups

namespace Data

variable {G : Type} [Group G] [Finite G] {f : ℕ} {K : Type} [Field K]
  {h : UnitaryFieldData 2 f K} {d : Data G h}

theorem lin_s39a1_card_Q (hl : d.LinCtx) :
    (2 ^ f) ^ 6 ≤ Nat.card (d.D ⊓ centralizer (d.I₂ : Set G) ⊓ d.M₂ : Subgroup G) := by
  have hd : d.Hyp := hl.hyp
  have hGMS := hl.gms
  obtain ⟨hIB, hID⟩ := hd.s39a1_I_le_normalizer_B₆ hGMS
  obtain ⟨hDB, hBD, -, hfac⟩ := hd.s39a1_D_facts hGMS
  set C₂ : Subgroup G := centralizer (d.I₂ : Set G)
  set Y : Subgroup G := d.B₆ ⊓ C₂
  set Q : Subgroup G := d.D ⊓ C₂ ⊓ d.M₂
  set T : Subgroup G := d.I ⊓ d.N₂
  have hIC : d.I ≤ C₂ := fun x hx =>
    mem_centralizer_iff.2 fun y hy => d.I_comm (d.I₂_le_I hy) hx
  have hTI : T ≤ d.I := inf_le_left
  have hTC : T ≤ C₂ := hTI.trans hIC
  have hTM : T ≤ d.M₂ := inf_le_right.trans d.s39a1_N₂_le_M₂
  have hCN : C₂ ≤ normalizer (d.M₂ : Set G) := d.s39a1_centralizer_le_normalizer_M₂
  have hQY : Q ≤ Y := fun x hx => ⟨hDB hx.1.1, hx.1.2⟩
  have hYQ : Y ≤ normalizer (Q : Set G) := fun y hy =>
    s39a1_cardQ_mem_normalizer_inf
      (s39a1_cardQ_mem_normalizer_inf (hBD hy.1) (le_normalizer hy.2)) (hCN hy.2)
  have hTY : T ≤ normalizer (Y : Set G) := fun x hx =>
    s39a1_cardQ_mem_normalizer_inf (hIB (hTI hx)) (le_normalizer (hTC hx))
  have hTQ : T ≤ normalizer (Q : Set G) := fun x hx =>
    s39a1_cardQ_mem_normalizer_inf
      (s39a1_cardQ_mem_normalizer_inf (hID (hTI hx)) (le_normalizer (hTC hx))) (hCN (hTC hx))
  have hY2 : IsPGroup 2 Y := d.isPGroup_B₆_caseB.to_le inf_le_left
  have hTodd : Odd (Nat.card T) := Odd.of_dvd_nat d.odd_card_I (Subgroup.card_dvd_of_le hTI)
  have hfix : ∀ y ∈ Y, ∀ s ∈ T, y⁻¹ * (s * y * s⁻¹) ∈ Q := by
    intro y hy s hs
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · obtain ⟨c, hc, n, hn, rfl⟩ := hfac y hy.1
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hc
      have hst : Commute s d.t := hd.comm_t (d.pull_le_L _ (hTI hs))
      have hcs : d.t ^ k * s = s * d.t ^ k := (hst.symm.zpow_left k).eq
      have hcs' : (d.t ^ k)⁻¹ * s * d.t ^ k = s := by
        rw [mul_assoc, ← hcs, inv_mul_cancel_left]
      have e : (d.t ^ k * n)⁻¹ * (s * (d.t ^ k * n) * s⁻¹) =
          n⁻¹ * (((d.t ^ k)⁻¹ * s * d.t ^ k) * n * s⁻¹) := by group
      rw [e, hcs']
      exact d.D.mul_mem (d.D.inv_mem hn) ((mem_normalizer_iff.1 (hID (hTI hs)) n).1 hn)
    · exact C₂.mul_mem (C₂.inv_mem hy.2)
        (C₂.mul_mem (C₂.mul_mem (hTC hs) hy.2) (C₂.inv_mem (hTC hs)))
    · have h1 : y⁻¹ * s * y⁻¹⁻¹ ∈ d.M₂ :=
        (mem_normalizer_iff.1 (hCN (C₂.inv_mem hy.2)) s).1 (hTM hs)
      have e : y⁻¹ * (s * y * s⁻¹) = (y⁻¹ * s * y⁻¹⁻¹) * s⁻¹ := by group
      rw [e]
      exact d.M₂.mul_mem h1 (d.M₂.inv_mem (hTM hs))
  have hYT : Y ⊓ centralizer (T : Set G) ≤ zpowers d.t := by
    have hS : d.I₂ ⊔ T ≤ d.I := sup_le d.I₂_le_I hTI
    have hA : d.A₃ ⊓ centralizer ((d.I₂ ⊔ T : Subgroup G) : Set G) = ⊥ := by
      refine eq_bot_iff.2 fun x hx => ?_
      rw [← (d.sec2_1_four hd.two_le).2.1]
      exact ⟨⟨d.A₃_le_P hx.1, centralizer_le (SetLike.coe_subset_coe.2 le_sup_left) hx.2⟩,
        centralizer_le (SetLike.coe_subset_coe.2 le_sup_right) hx.2⟩
    refine le_trans ?_ (hd.s39a1_centralizer_B₆_le hGMS hS hA)
    exact fun x hx => ⟨hx.1.1, s39a1_cardQ_mem_centralizer_sup hx.1.2 hx.2⟩
  have hlift : ∀ y ∈ Y, ∃ c ∈ Y ⊓ centralizer (T : Set G), ∃ n ∈ Q, y = c * n :=
    fun y hy => s39a1_lift hQY hYQ hTY hTQ hY2 hTodd hy (hfix y hy)
  let φ : (Y ⊓ centralizer (T : Set G) : Subgroup G) × Q → Y := fun p =>
    ⟨p.1 * p.2, Y.mul_mem p.1.2.1 (hQY p.2.2)⟩
  have hφ : Function.Surjective φ := by
    rintro ⟨y, hy⟩
    obtain ⟨c, hc, n, hn, rfl⟩ := hlift y hy
    exact ⟨(⟨c, hc⟩, ⟨n, hn⟩), rfl⟩
  have h1 : Nat.card Y ≤ Nat.card (Y ⊓ centralizer (T : Set G) : Subgroup G) * Nat.card Q := by
    rw [← Nat.card_prod]
    exact Nat.card_le_card_of_surjective φ hφ
  have h2 : Nat.card (Y ⊓ centralizer (T : Set G) : Subgroup G) ≤ 2 := by
    rw [← hd.card_zpowers_t]
    exact Subgroup.card_le_of_le hYT
  have h3 : 2 * (2 ^ f) ^ 6 ≤ 2 * Nat.card Q :=
    (hd.s39a1_card_centralizer_B₆ hGMS).trans (h1.trans (Nat.mul_le_mul h2 le_rfl))
  exact Nat.le_of_mul_le_mul_left h3 (by norm_num)

theorem lin_s39a1_sylowE₅ (hl : d.LinCtx) :
    IsSylowOf 2 (d.E ⊓ centralizer (d.I₅ : Set G)) d.M₅ := by
  have hd : d.Hyp := hl.hyp
  have hGMS := hl.gms
  have hX2 : IsPGroup 2 (d.E ⊓ centralizer (d.I₅ : Set G) : Subgroup G) :=
    (hd.s39a1_isPGroup_E hGMS).to_le inf_le_left
  have hXN : d.E ⊓ centralizer (d.I₅ : Set G) ≤ normalizer (d.M₅ : Set G) :=
    inf_le_right.trans d.s39a1_centralizer_le_normalizer_M₅
  have hTM : d.I ⊓ d.N₅ ≤ d.M₅ := inf_le_right.trans d.s39a1_N₅_le_M₅
  have hTC : d.I ⊓ d.N₅ ≤ centralizer (d.I₅ : Set G) :=
    inf_le_right.trans d.s39a1_N₅_le_centralizer_I₅
  have hTX : d.I ⊓ d.N₅ ≤
      normalizer ((d.E ⊓ centralizer (d.I₅ : Set G) : Subgroup G) : Set G) := fun τ hτ =>
    Subgroup.inf_normalizer_le_normalizer_inf
      ⟨hd.s39a1_I_le_normalizer_E hGMS hτ.1, Subgroup.le_normalizer (hTC hτ)⟩
  have hXXM : d.E ⊓ centralizer (d.I₅ : Set G) ≤
      normalizer ((d.E ⊓ centralizer (d.I₅ : Set G) ⊓ d.M₅ : Subgroup G) : Set G) :=
    fun x hx => Subgroup.inf_normalizer_le_normalizer_inf ⟨Subgroup.le_normalizer hx, hXN hx⟩
  have hTXM : d.I ⊓ d.N₅ ≤
      normalizer ((d.E ⊓ centralizer (d.I₅ : Set G) ⊓ d.M₅ : Subgroup G) : Set G) :=
    fun τ hτ => Subgroup.inf_normalizer_le_normalizer_inf
      ⟨hTX hτ, Subgroup.le_normalizer (hTM hτ)⟩
  have hTodd : Odd (Nat.card (d.I ⊓ d.N₅ : Subgroup G)) :=
    Odd.of_dvd_nat d.odd_card_I (Subgroup.card_dvd_of_le inf_le_left)
  have hSI : d.I₅ ⊔ d.I ⊓ d.N₅ ≤ d.I := sup_le d.I₅_le_I inf_le_left
  have hA : d.A₂ ⊓ centralizer ((d.I₅ ⊔ d.I ⊓ d.N₅ : Subgroup G) : Set G) = ⊥ := by
    rw [eq_bot_iff, ← (d.sec2_1_four hd.two_le).2.2.2]
    rintro y ⟨hyA, hyC⟩
    exact ⟨⟨d.A₂_le_P hyA, Subgroup.centralizer_le
      (le_sup_left : d.I₅ ≤ d.I₅ ⊔ d.I ⊓ d.N₅) hyC⟩,
      Subgroup.centralizer_le (le_sup_right : d.I ⊓ d.N₅ ≤ d.I₅ ⊔ d.I ⊓ d.N₅) hyC⟩
  have hE := hd.s39a1_centralizer_E_eq_bot hGMS hSI hA
  have hXM : d.E ⊓ centralizer (d.I₅ : Set G) ≤ d.M₅ := by
    intro x hx
    have hfix : ∀ τ ∈ d.I ⊓ d.N₅,
        x⁻¹ * (τ * x * τ⁻¹) ∈ d.E ⊓ centralizer (d.I₅ : Set G) ⊓ d.M₅ := by
      intro τ hτ
      have h0 : x⁻¹ * (τ * x * τ⁻¹) ∈ d.E ⊓ centralizer (d.I₅ : Set G) :=
        Subgroup.mul_mem _ (Subgroup.inv_mem _ hx)
          ((Subgroup.mem_normalizer_iff.1 (hTX hτ) x).1 hx)
      have h1 : x⁻¹ * τ * x ∈ d.M₅ :=
        (Subgroup.mem_normalizer_iff''.1 (hXN hx) τ).1 (hTM hτ)
      have h2 : x⁻¹ * (τ * x * τ⁻¹) = x⁻¹ * τ * x * τ⁻¹ := by group
      have h3 : x⁻¹ * (τ * x * τ⁻¹) ∈ d.M₅ := by
        rw [h2]
        exact Subgroup.mul_mem _ h1 (Subgroup.inv_mem _ (hTM hτ))
      exact ⟨h0, h3⟩
    obtain ⟨c, hc, n, hn, rfl⟩ := s39a1_lift inf_le_left hXXM hTX hTXM hX2 hTodd hx hfix
    have hc1 : c = 1 := by
      have hcS : c ∈ d.E ⊓ centralizer ((d.I₅ ⊔ d.I ⊓ d.N₅ : Subgroup G) : Set G) := by
        refine ⟨hc.1.1, Subgroup.mem_centralizer_iff.2 fun y hy => ?_⟩
        have hle : d.I₅ ⊔ d.I ⊓ d.N₅ ≤ centralizer ({c} : Set G) := sup_le
          (fun i hi => Subgroup.mem_centralizer_singleton_iff.2
            (Subgroup.mem_centralizer_iff.1 hc.1.2 i hi))
          (fun i hi => Subgroup.mem_centralizer_singleton_iff.2
            (Subgroup.mem_centralizer_iff.1 hc.2 i hi))
        exact Subgroup.mem_centralizer_singleton_iff.1 (hle hy)
      rw [hE] at hcS
      exact hcS
    rw [hc1, one_mul]
    exact hn.2
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨Q, hQ⟩ := (hX2.comap_subtype (K := d.M₅)).exists_le_sylow
  have hQS : IsSylowOf 2 ((Q : Subgroup d.M₅).map d.M₅.subtype) d.M₅ := ⟨Q, rfl⟩
  have hXQ : d.E ⊓ centralizer (d.I₅ : Set G) ≤ (Q : Subgroup d.M₅).map d.M₅.subtype :=
    fun x hx => ⟨⟨x, hXM hx⟩, hQ hx, rfl⟩
  have heq : d.E ⊓ centralizer (d.I₅ : Set G) = (Q : Subgroup d.M₅).map d.M₅.subtype :=
    Subgroup.eq_of_le_of_card_ge hXQ
      ((lin_card_le₅ hl hQS.le hQS.isPGroup).trans (hd.s39a1_card_centralizer_E hGMS))
  rw [heq]
  exact hQS


theorem lin_sec39a1 (hl : d.LinCtx) (k8 : d.Know8) (S : Subgroup G) (hS : IsSylowOf 2 S d.L₂)
    (hP : d.P ≤ S) : d.Sec39a1 S := by
  have hd : d.Hyp := hl.hyp
  have hGMS := hl.gms
  have hL₂ : d.L₂ = d.E ⊔ d.M₂ := k8.s8.1
  obtain ⟨hSH, hA⟩ := lin_sylow₂ hl hL₂ hS
  have hDf := hd.s39a1_D_facts hGMS
  have hQ2 : IsPGroup 2 (d.D ⊓ centralizer (d.I₂ : Set G) ⊓ d.M₂ : Subgroup G) :=
    (d.isPGroup_B₆_caseB.to_le hDf.1).to_le (inf_le_left.trans inf_le_left)
  have hRcard : Nat.card (S ⊓ d.M₂ : Subgroup G) ≤ (2 ^ f) ^ 6 :=
    lin_card_le hl inf_le_right (hS.isPGroup.to_le inf_le_left)
  have hB : d.D ⊓ centralizer (d.I₂ : Set G) ⊓ d.M₂ = S ⊓ centralizer (d.I₂ : Set G) := by
    rw [hSH]
    obtain ⟨z, hzN, hzP, hzA, hz1⟩ := lin_exists_z₂ hd
    have hle : d.D ⊓ centralizer (d.I₂ : Set G) ⊓ d.M₂ ≤ S ⊓ d.M₂ :=
      lin_ti_lift hl hA inf_le_right hQ2
        (z := z) ⟨⟨hDf.2.2.1 hzA, d.N₂_le_centralizer_I₂ hzN⟩, d.s39a1_N₂_le_M₂ hzN⟩
        ⟨hP hzP, d.s39a1_N₂_le_M₂ hzN⟩ hz1
    exact Subgroup.eq_of_le_of_card_ge hle (hRcard.trans (lin_s39a1_card_Q hl))
  have hC := lin_s39a1_sylowE₅ hl
  have hD : d.D ⊓ centralizer (d.I₅ : Set G) ⊓ d.M₅ = d.E ⊓ centralizer (d.I₅ : Set G) := by
    obtain ⟨z, hzN, hzA₂, hzA₃, hzC, hz1⟩ := lin_exists_z₅ hd
    obtain ⟨hM₅, hC₅, -⟩ := hd.s39a1_conj_r
    have hQcard : Nat.card (d.D ⊓ centralizer (d.I₅ : Set G) ⊓ d.M₅ : Subgroup G) =
        Nat.card (d.D ⊓ centralizer (d.I₂ : Set G) ⊓ d.M₂ : Subgroup G) := by
      have e : (d.D ⊓ centralizer (d.I₂ : Set G) ⊓ d.M₂).map (MulAut.conj d.r).toMonoidHom =
          d.D ⊓ centralizer (d.I₅ : Set G) ⊓ d.M₅ := by
        rw [Subgroup.map_inf_eq _ _ _ (MulAut.conj d.r).injective,
          Subgroup.map_inf_eq _ _ _ (MulAut.conj d.r).injective, hM₅, hC₅,
          hd.s39a1_map_conj_r_D hGMS]
      rw [← e, Subgroup.card_map_of_injective (MulAut.conj d.r).injective]
    have hQ2' : IsPGroup 2 (d.D ⊓ centralizer (d.I₅ : Set G) ⊓ d.M₅ : Subgroup G) :=
      (d.isPGroup_B₆_caseB.to_le hDf.1).to_le (inf_le_left.trans inf_le_left)
    have hle : d.D ⊓ centralizer (d.I₅ : Set G) ⊓ d.M₅ ≤ d.E ⊓ centralizer (d.I₅ : Set G) :=
      lin_ti_lift₅ hl hC inf_le_right hQ2'
        (z := z) ⟨⟨hDf.2.2.1 hzA₃, hzC⟩, d.s39a1_N₅_le_M₅ hzN⟩
        ⟨hd.A₂_le_E hGMS hzA₂, hzC⟩ hz1
    refine Subgroup.eq_of_le_of_card_ge hle ?_
    rw [hQcard]
    exact (lin_card_le₅ hl hC.le hC.isPGroup).trans (lin_s39a1_card_Q hl)
  exact ⟨hSH ▸ hA, hB, hC, hD⟩

end Data

end CFSG.LocalAnalysis.EvenBN.U5
