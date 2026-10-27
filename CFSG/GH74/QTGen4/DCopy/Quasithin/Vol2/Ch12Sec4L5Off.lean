module

public import CFSG.Quasithin.Vol2.Ch12Sec4L5Off
public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch12Sec4L5Mbar

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.Quasithin
open scoped IsMulCommutative

variable {G : Type} [Group G]

variable [CFSG.GH74.QTGen4.Finite4 G] {T L V : Subgroup G} {z : G}

namespace Cx5Facts

theorem mem_commutator_of_le_T_F4 [IsMulCommutative ↥V] (h1222 : Stmt12_2_2_F4)
    (h3228 : Stmt3_2_2_eight) (h12210 : Stmt12_2_10_F4) (h1229 : Stmt12_2_9_F4) (hpre : Pre1242_F4)
    (h42 : AsB42) (hcx : Cx1242 G T L V) (hf : Cx5Facts G T L V z)
    (h5 : Nonempty (↥L ⧸ CFSG.pCore 2 ↥L ≃* Matrix.SpecialLinearGroup (Fin 5) (ZMod 2)))
    {A : Subgroup G} (hAT : A ≤ T) (hA : IsElemAbelian 2 A) (hA1 : autOn A V ≠ ⊥)
    (hr : Nat.card ↥V ≤ Nat.card (autOn A V) * Nat.card (fixV (autOn A V))) :
    z ∈ ⁅V, A⁆ := by
  have hyp := hcx.hyp
  have hW2 : ∀ w : ↥V, w ^ 2 = 1 := fun w => Subtype.ext (by simpa using hf.sq w w.2)
  have hAN : A ≤ Subgroup.normalizer (V : Set G) := hAT.trans hf.T_le
  have hX := hf.mbar_eq_F4 h1222 h3228 h12210 h1229 hpre h42 hcx h5
  have hTL : autOn T V ≤ autOn L V := (autOn_mono le_sup_right).trans hX.le
  have hAT' : autOn A V ≤ autOn T V := autOn_mono hAT

  have hA2 : IsA2 (autOn (L ⊔ T) V) (autOn A V) :=
    ⟨autOn_mono (hAT.trans le_sup_right), hA1, isElemAbelian2_autOn' hA⟩
  obtain ⟨B, hBA, hB, -⟩ := B1_4_4_le hW2 hA2 ((rAV_le_one_iff hW2 hA2).2 hr)
  have hBL : B ≤ autOn L V := hB.1.trans hX.le

  have hc := h42 ↥V hW2 (autOn (L ⊔ T) V) (autOn L V) (hf.b4Hyp_F4 h1222 h3228 h12210 hcx h5) B hB
  obtain ⟨-, -, -, -, π, hπ, hrad⟩ := b42Case11_of_card hf.card (hf.card_lbar h5) hc
  have hGam : Nat.card (FFModel.extSq (ZMod 2) 5).Gam = 9999360 := card_statedSL_five_two
  have : Finite (FFModel.extSq (ZMod 2) 5).Gam :=
    Nat.finite_of_card_ne_zero (by rw [hGam]; norm_num)
  have hinj : Function.Injective π :=
    (hπ.1.bijective_of_nat_card_le (le_of_eq (by rw [hGam, hf.card_lbar h5]))).1

  have hTB : ∀ s ∈ autOn T V, ∀ b ∈ B, s * b * s⁻¹ ∈ B := by
    have hTp : IsPGroup 2 ↥((autOn T V).subgroupOf (autOn L V)) :=
      (isPGroup_autOn hyp.sylow.1).comap_subtype
    have hSp : IsPGroup 2 ↥(((autOn T V).subgroupOf (autOn L V)).comap π) :=
      hTp.comap_of_injective π hinj
    have hRS : (B.subgroupOf (autOn L V)).comap π ≤
        ((autOn T V).subgroupOf (autOn L V)).comap π :=
      Subgroup.comap_mono fun x hx =>
        Subgroup.mem_subgroupOf.2 (hAT' (hBA (Subgroup.mem_subgroupOf.1 hx)))
    have hnorm := le_normalizer_of_isEndNodeRadical5 hrad hSp hRS
    intro s hs b hb
    obtain ⟨σ, hσ⟩ : ∃ σ : ↥(CFSG.Assembly.LowTwoRank.StatedSL 5 (ZMod 2)),
        π σ = ⟨s, hTL hs⟩ := hπ.1 _
    obtain ⟨ρ, hρ⟩ : ∃ ρ : ↥(CFSG.Assembly.LowTwoRank.StatedSL 5 (ZMod 2)),
        π ρ = ⟨b, hBL hb⟩ := hπ.1 _
    have hσS : σ ∈ ((autOn T V).subgroupOf (autOn L V)).comap π := by
      show π σ ∈ (autOn T V).subgroupOf (autOn L V)
      rw [hσ]
      exact Subgroup.mem_subgroupOf.2 hs
    have hρR : ρ ∈ (B.subgroupOf (autOn L V)).comap π := by
      show π ρ ∈ B.subgroupOf (autOn L V)
      rw [hρ]
      exact Subgroup.mem_subgroupOf.2 hb
    have h1 := (Subgroup.mem_normalizer_iff.1 (hnorm hσS) ρ).1 hρR
    rw [Subgroup.mem_comap, map_mul, map_mul, map_inv, hσ, hρ] at h1
    exact Subgroup.mem_subgroupOf.1 h1

  have hWB : ∀ τ : MulAut ↥V, (∀ b ∈ B, τ * b * τ⁻¹ ∈ B) → ∀ w ∈ commV B, τ w ∈ commV B := by
    intro τ hτ w hw
    induction hw using Subgroup.closure_induction with
    | mem c hc =>
      obtain ⟨x, hx, v, rfl⟩ := hc
      have h1 : (τ * x * τ⁻¹) (τ v) * (τ v)⁻¹ ∈ commV B :=
        Subgroup.subset_closure ⟨τ * x * τ⁻¹, hτ x hx, τ v, rfl⟩
      have h2 : τ (x v * v⁻¹) = (τ * x * τ⁻¹) (τ v) * (τ v)⁻¹ := by simp
      rw [h2]
      exact h1
    | one => simp
    | mul x y _ _ hx hy => rw [map_mul]; exact (commV B).mul_mem hx hy
    | inv x _ hx => rw [map_inv]; exact (commV B).inv_mem hx

  set W : Subgroup G := (commV B).map V.subtype
  have hWV : W ≤ V := Subgroup.map_subtype_le _
  have hTW : T ≤ Subgroup.normalizer (W : Set G) := by
    have key : ∀ t ∈ T, ∀ x ∈ W, t * x * t⁻¹ ∈ W := by
      intro t ht x hx
      obtain ⟨w, hw, rfl⟩ := hx
      have hτ : conjAct V ⟨t, hf.T_le ht⟩ ∈ autOn T V :=
        Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.2 ht)
      refine ⟨conjAct V ⟨t, hf.T_le ht⟩ w, hWB _ (hTB _ hτ) w hw, ?_⟩
      exact A1b.conjAct_coe V ⟨t, hf.T_le ht⟩ w
    intro t ht
    rw [Subgroup.mem_normalizer_iff]
    intro x
    refine ⟨key t ht x, fun hx => ?_⟩
    have := key t⁻¹ (T.inv_mem ht) _ hx
    simpa [mul_assoc] using this
  have hW1 : W ≠ ⊥ := by
    obtain ⟨⟨b, hbB⟩, hb1⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hB.2.1
    have hb1' : b ≠ 1 := fun h => hb1 (Subtype.ext h)
    obtain ⟨v, hv⟩ : ∃ v : ↥V, b v ≠ v := by
      by_contra h
      push Not at h
      exact hb1' (MulEquiv.ext fun v => h v)
    intro hW
    apply hv
    have h1 : (b v * v⁻¹ : ↥V) ∈ commV B := Subgroup.subset_closure ⟨b, hbB, v, rfl⟩
    have h2 : ((b v * v⁻¹ : ↥V) : G) ∈ W := ⟨_, h1, rfl⟩
    rw [hW, Subgroup.mem_bot] at h2
    exact mul_inv_eq_one.1 (Subtype.ext h2)

  obtain ⟨⟨w, hwW, hwC⟩, hw1⟩ := Subgroup.ne_bot_iff_exists_ne_one.1
    (inf_centralizer_ne_bot_of_isPGroup hyp.sylow.1 (hWV.trans hf.le_T) hTW hW1)
  have hw1' : w ≠ 1 := fun h => hw1 (Subtype.ext h)
  have hwz : w = z := hf.eq_of_mem_centralizer_T (hWV hwW) hwC hw1'
  rw [← hwz, ← map_commV_autOn hAN]
  refine Subgroup.map_mono (Subgroup.closure_mono ?_) hwW
  rintro _ ⟨g, hg, v, hv⟩
  exact ⟨g, hBA hg, v, hv⟩

end Cx5Facts

end CFSG.Quasithin.H13
