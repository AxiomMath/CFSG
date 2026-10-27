module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23R7M1
import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23GOCMain
import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23R8AE
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23R7Y

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
  CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDisc CFSG.ClassicalInvolution.Uniform
  CFSG.ClassicalInvolution.Q3.Q3NL

section Gen

variable {G : Type} [Group G] [Finite G]

theorem comm_of_commutator_mem_odd {N : Subgroup G} (hN : Odd (Nat.card ↥N)) {a ℓ : G}
    (ha2 : a * a = 1) (hk : a * ℓ * a⁻¹ * ℓ⁻¹ ∈ N) (hNa : ∀ o ∈ N, o * a = a * o) :
    a * ℓ = ℓ * a := by
  have hai : a⁻¹ = a := inv_eq_of_mul_eq_one_right ha2
  obtain ⟨b, hb⟩ : ∃ b, b = ℓ * a * ℓ⁻¹ := ⟨_, rfl⟩
  have hkab : a * ℓ * a⁻¹ * ℓ⁻¹ = a * b := by rw [hb, hai]; group
  have hb2 : b * b = 1 := by
    calc b * b = ℓ * (a * a) * ℓ⁻¹ := by rw [hb]; group
      _ = 1 := by rw [ha2]; group
  have hc := hNa _ hk
  rw [hkab] at hc hk
  have h1 : a * b * a = b := by
    calc a * b * a = a * (a * b) := hc
      _ = b := by rw [← mul_assoc, ha2, one_mul]
  have hk2 : (a * b) * (a * b) = 1 := by
    calc (a * b) * (a * b) = (a * b * a) * b := by group
      _ = 1 := by rw [h1, hb2]
  have hk1 : a * b = 1 :=
    eq_one_of_isPGroup_of_mem_odd hN hk (ExactLayer.isPGroup_zpowers_of_sq_eq_one hk2)
  rw [← hkab] at hk1
  have e1 : a * ℓ * a⁻¹ = ℓ := mul_inv_eq_one.mp hk1
  calc a * ℓ = a * ℓ * a⁻¹ * a := by group
    _ = ℓ * a := by rw [e1]

end Gen

section NC

variable {n : ℕ}

theorem p23_e_not_zstar (hT : Thm4RTwinBelow 3 n) (hTwo : P23Two n) (hα : P23Alpha n)
    {Y : Type} [Group Y] [Finite Y] {R : Subgroup Y} {S : Sylow 2 R} {t : Y} {K' W : Subgroup Y}
    {u e g : Y} (hc : P23Cfg n Y R S t K' W u e g)
    (hZ : u * e ∈ zStarOf (Subgroup.centralizer ({u} : Set Y)))
    (hE : ∀ ℓ ∈ Subgroup.centralizer ({t} : Set Y),
      e * ℓ * e⁻¹ * ℓ⁻¹ ∈ oddCoreOf (Subgroup.centralizer ({t} : Set Y))) : False := by
  classical
  have hd := hc.data
  have hC := CoreData.of_S hc.std.perp.core
  have hΩ : HypOmegaGen (Om R) := hC.hyp
  haveI := hc.std.perp.core.simple
  have hz : IsUniqueInvolution (tightCore R) t := Inner.isUniqueInvolution_core hC.datum
  have ht2 : t * t = 1 := hz.sq
  have ht1 : t ≠ 1 := hz.ne_one
  have hWab : ∀ a ∈ W, ∀ b ∈ W, a * b = b * a := Q3CL.Thompson.commutes_of_mem_WSet hΩ hd.hW
  have heW : e ∈ W := (T7K.e_mem_inf hd).1
  have het : e * t = t * e := hWab e heW t hd.hzW
  have hue : u * e = e * u := hWab u hd.huW e heW
  have hue2 : (u * e) * (u * e) = 1 := ue_sq hc
  have hue1 : u * e ≠ 1 := by
    intro h
    apply ht1
    have e1 : t = g⁻¹ * (g * t * g⁻¹) * g := by group
    rw [e1, hd.hgt, h]; group
  have het' : e ≠ t := fun h => e_not_mem_sup hc (h ▸ Subgroup.mem_sup_left hz.mem)
  have hu_ue : u ≠ u * e := by
    intro h
    apply hd.he1
    have e1 : e = u⁻¹ * (u * e) := by group
    rw [e1, ← h, inv_mul_cancel]
  have huue : u * (u * e) = u * e * u := by
    calc u * (u * e) = u * (e * u) := by rw [hue]
      _ = u * e * u := (mul_assoc _ _ _).symm
  have hc2 : IsPGroup 2 (Subgroup.zpowers u) := ExactLayer.isPGroup_zpowers_of_sq_eq_one hd.hu2
  obtain ⟨J₁, -, hJ₁, -, hτ₁, -, -⟩ := R56.u_trans_or_pair hT hc
  obtain ⟨htC, htY, -⟩ := TwinDisc.isUniqueInvolution_secImg hΩ hc2 hJ₁ hτ₁
  have hlay : u * e ∈ rLayer (Om R) u :=
    TwinDisc.coreHull_map_le_rLayer hΩ hc2 (Subgroup.mem_map.mpr ⟨⟨u * e, htC⟩, htY, rfl⟩)
  have hYT : YType R u e := Or.inl (T7T.mem_zStarOf_of_le (rLayer_le_centralizer _ u) hZ hlay)
  obtain ⟨hodd, hαA⟩ := hα Y R S t K' W u e g hc hYT
  have hueB : u * e ∈ Subgroup.closure ({u * e, u, t} : Set Y) := Subgroup.subset_closure (by simp)
  have huB : u ∈ Subgroup.closure ({u * e, u, t} : Set Y) := Subgroup.subset_closure (by simp)
  have htB : t ∈ Subgroup.closure ({u * e, u, t} : Set Y) := Subgroup.subset_closure (by simp)
  have heB : e ∈ Subgroup.closure ({u * e, u, t} : Set Y) := by
    have e1 : u⁻¹ * (u * e) = e := by group
    have h := Subgroup.mul_mem _ (Subgroup.inv_mem _ huB) hueB
    rwa [e1] at h
  have hA1 : alphaOf (Subgroup.closure ({e, t} : Set Y)) =
      alphaOf (Subgroup.closure ({u, t} : Set Y)) :=
    hαA _ ((Subgroup.closure_le _).mpr (Set.insert_subset_iff.mpr
      ⟨heB, Set.singleton_subset_iff.mpr htB⟩))
      (T7A.isElemAbelian2_closure_pair hd.he2 ht2 hd.he1 ht1 het' het)
  have hA2 : alphaOf (Subgroup.closure ({u * e, u} : Set Y)) =
      alphaOf (Subgroup.closure ({u, t} : Set Y)) :=
    hαA _ ((Subgroup.closure_le _).mpr (Set.insert_subset_iff.mpr
      ⟨hueB, Set.singleton_subset_iff.mpr huB⟩))
      (T7A.isElemAbelian2_closure_pair hue2 hd.hu2 hue1 hd.hu1 (fun h => hu_ue h.symm)
        huue.symm)
  have hinv : (u * e)⁻¹ = u * e := inv_eq_of_mul_eq_one_right hue2
  have hUc : ∀ ℓ ∈ Subgroup.centralizer ({u} : Set Y),
      u * e * ℓ * (u * e)⁻¹ * ℓ⁻¹ ∈ oddCoreOf (Subgroup.centralizer ({u} : Set Y)) := by
    intro ℓ hℓ
    have h1 := ((C25V.mem_zStarOf_iff' _).mp hZ).2 ℓ⁻¹ (Subgroup.inv_mem _ hℓ)
    rw [hinv, inv_inv] at h1
    rw [hinv]
    exact h1
  have hNu : Subgroup.centralizer ({u} : Set Y) ≤
      Subgroup.normalizer (alphaOf (Subgroup.closure ({u, t} : Set Y)) : Set Y) := by
    intro ℓ hℓ
    rw [← hA2]
    refine T7B.mem_normalizer_alphaOf_of_commutator hue2 huue hℓ (hUc ℓ hℓ) ?_
    rw [Set.pair_comm]
    exact oddCoreOf_centralizer_le_normalizer_alphaOf hue2 hd.hu1 huue
  have hNt : Subgroup.centralizer ({t} : Set Y) ≤
      Subgroup.normalizer (alphaOf (Subgroup.closure ({u, t} : Set Y)) : Set Y) := by
    intro ℓ hℓ
    rw [← hA1]
    refine T7B.mem_normalizer_alphaOf_of_commutator hd.he2 het.symm hℓ (hE ℓ hℓ) ?_
    rw [Set.pair_comm]
    exact oddCoreOf_centralizer_le_normalizer_alphaOf hd.he2 ht1 het.symm
  have hG := hTwo Y R S t K' W u e g hc
  have hα1 := p23_alpha_eq_bot hc hG hodd ⟨hNu, hNt⟩
  have hOt : ∀ o ∈ oddCoreOf (Subgroup.centralizer ({t} : Set Y)), o * e = e * o := by
    intro o ho
    have h := commutator_oddCore_le_alphaOf ht1 (Subgroup.closure ({e, t} : Set Y))
      (Subgroup.subset_closure (by simp)) (Subgroup.commutator_mem_commutator ho
        (Subgroup.subset_closure (by simp) : e ∈ Subgroup.closure ({e, t} : Set Y)))
    rw [hA1, hα1, Subgroup.mem_bot] at h
    exact commutatorElement_eq_one_iff_mul_comm.mp h
  have hOu : ∀ o ∈ oddCoreOf (Subgroup.centralizer ({u} : Set Y)), o * (u * e) = u * e * o := by
    intro o ho
    have h := commutator_oddCore_le_alphaOf hd.hu1 (Subgroup.closure ({u * e, u} : Set Y))
      (Subgroup.subset_closure (by simp)) (Subgroup.commutator_mem_commutator ho
        (Subgroup.subset_closure (by simp) : u * e ∈ Subgroup.closure ({u * e, u} : Set Y)))
    rw [hA2, hα1, Subgroup.mem_bot] at h
    exact commutatorElement_eq_one_iff_mul_comm.mp h
  have hcen : ∀ ℓ : Y, e * ℓ = ℓ * e →
      ℓ ∈ Subgroup.normalizer ((Subgroup.zpowers e : Subgroup Y) : Set Y) := by
    intro ℓ hℓ
    apply Subgroup.centralizer_le_normalizer
    rw [Subgroup.mem_centralizer_iff]
    rintro _ ⟨k, rfl⟩
    exact (Commute.zpow_left hℓ k).eq
  have hXV : Subgroup.centralizer ({u} : Set Y) ⊔ Subgroup.centralizer ({t} : Set Y) ≤
      Subgroup.normalizer ((Subgroup.zpowers e : Subgroup Y) : Set Y) := by
    refine sup_le (fun ℓ hℓ => hcen ℓ ?_) (fun ℓ hℓ => hcen ℓ ?_)
    · have h1 : u * e * ℓ = ℓ * (u * e) :=
        comm_of_commutator_mem_odd (oddCoreOf_odd_natCard _) hue2 (hUc ℓ hℓ) hOu
      have h2 : ℓ * u = u * ℓ := Subgroup.mem_centralizer_singleton_iff.mp hℓ
      have e1 : e = u * (u * e) := by rw [← mul_assoc, hd.hu2, one_mul]
      rw [e1]
      calc u * (u * e) * ℓ = u * (u * e * ℓ) := by group
        _ = u * ℓ * (u * e) := by rw [h1]; group
        _ = ℓ * (u * (u * e)) := by rw [← h2]; group
    · exact comm_of_commutator_mem_odd (oddCoreOf_odd_natCard _) hd.he2 (hE ℓ hℓ) hOt
  exact ne_top_of_le_normalizer hc.std.perp.core.nonab (Subgroup.zpowers_ne_bot.mpr hd.he1)
    (ExactLayer.isPGroup_zpowers_of_sq_eq_one hd.he2) hXV hG

theorem p23E7NC_proved (hT : Thm4RTwinBelow 3 n) (hTwo : P23Two n) (hα : P23Alpha n) :
    P23E7NC n := by
  intro _ _ Y _ _ R S t K' W u e g hc _ _ hZ xe hxe hall
  refine p23_e_not_zstar hT hTwo hα hc hZ fun ℓ hℓ => ?_
  have h1 : F7I.piC _ (xe * ⟨ℓ, hℓ⟩ * xe⁻¹ * (⟨ℓ, hℓ⟩ : ↥(Subgroup.centralizer ({t} : Set Y)))⁻¹) =
      1 := by
    rw [map_mul, map_mul, map_mul, map_inv, map_inv, ← hall (F7I.piC _ ⟨ℓ, hℓ⟩)]
    group
  have h2 := (QuotientGroup.eq_one_iff _).mp h1
  rw [← hxe]
  exact mem_oddCoreOf_iff.mpr ⟨_, h2⟩

end NC

section E7

variable {n : ℕ}

theorem p23E7Y_of_not9_cen3 (hT : Thm4RTwinBelow 3 n)
    (hT4 : TwinThmE.T4Supply) (hmodel : TwinDisc.ExitE4.E4ModelDStar)
    (hD4 : TwinCentRes.ModelFactD42) (hMu : P23E4Mu n) (hTwo : P23Two n) (hα : P23Alpha n)
    (hN9 : P23E7Not9 n) (hC3 : P23E7Cen3 n) : P23E7Y n :=
  p23E7Y_of_e8 hT hT4 hmodel hD4 hMu
    (p23E7E8_of_nc p23E7Odd_proved hN9 (p23E7NC_proved hT hTwo hα) hC3) GOC.goldOutCyc

end E7

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23
