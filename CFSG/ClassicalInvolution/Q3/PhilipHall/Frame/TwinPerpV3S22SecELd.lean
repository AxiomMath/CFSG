module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3S22SecELc
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87G2ThreeMax

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3.SecEL

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.TL4
open CFSG.Blueprint

section Abstract

variable {X Y : Type} [Group X] [Group Y]

theorem sup_centralizer_eq_top_of_mulEquiv (e : X ≃* Y) {a b : X}
    (h : Subgroup.centralizer ({e a} : Set Y) ⊔ Subgroup.centralizer ({e b} : Set Y) = ⊤) :
    Subgroup.centralizer ({a} : Set X) ⊔ Subgroup.centralizer ({b} : Set X) = ⊤ := by
  have := congrArg (Subgroup.map e.symm.toMonoidHom) h
  rw [Subgroup.map_sup, CFSG.GH74.GLS.IVK.GHInv.map_centralizer_singleton' e.symm (e a),
    CFSG.GH74.GLS.IVK.GHInv.map_centralizer_singleton' e.symm (e b), MulEquiv.symm_apply_apply,
    MulEquiv.symm_apply_apply] at this
  rw [this]
  exact Subgroup.map_top_of_surjective _ e.symm.surjective

theorem sup_centralizer_eq_top_of_coatom [IsSimpleGroup X]
    (hmax : ∀ z : X, z * z = 1 → z ≠ 1 → IsCoatom (Subgroup.centralizer ({z} : Set X)))
    (hconj : ∀ a b : X, a * a = 1 → a ≠ 1 → b * b = 1 → b ≠ 1 → ∃ g : X, g * a * g⁻¹ = b)
    {a b : X} (ha2 : a * a = 1) (ha1 : a ≠ 1) (hb2 : b * b = 1) (hb1 : b ≠ 1) (hba : b ≠ a) :
    Subgroup.centralizer ({a} : Set X) ⊔ Subgroup.centralizer ({b} : Set X) = ⊤ := by
  have hma := hmax a ha2 ha1
  have hmb := hmax b hb2 hb1
  by_contra hne
  have hle : Subgroup.centralizer ({b} : Set X) ≤ Subgroup.centralizer ({a} : Set X) := by
    rcases hma.le_iff.mp (le_sup_left : Subgroup.centralizer ({a} : Set X) ≤
        Subgroup.centralizer ({a} : Set X) ⊔ Subgroup.centralizer ({b} : Set X)) with h | h
    · exact absurd h hne
    · rw [← h]
      exact le_sup_right
  have heq : Subgroup.centralizer ({a} : Set X) = Subgroup.centralizer ({b} : Set X) := by
    rcases hmb.le_iff.mp hle with h | h
    · exact absurd h hma.1
    · exact h
  obtain ⟨g, hg⟩ := hconj a b ha2 ha1 hb2 hb1
  have h1 : ∀ x : X, g * x * g⁻¹ ∈ Subgroup.centralizer ({b} : Set X) ↔
      x ∈ Subgroup.centralizer ({a} : Set X) := by
    intro x
    rw [Subgroup.mem_centralizer_singleton_iff, Subgroup.mem_centralizer_singleton_iff, ← hg]
    constructor
    · intro h
      have h2 : g * (x * a) * g⁻¹ = g * (a * x) * g⁻¹ :=
        calc g * (x * a) * g⁻¹ = g * x * g⁻¹ * (g * a * g⁻¹) := by group
          _ = g * a * g⁻¹ * (g * x * g⁻¹) := h
          _ = g * (a * x) * g⁻¹ := by group
      exact mul_left_cancel (mul_right_cancel h2)
    · intro h
      calc g * x * g⁻¹ * (g * a * g⁻¹) = g * (x * a) * g⁻¹ := by group
        _ = g * (a * x) * g⁻¹ := by rw [h]
        _ = g * a * g⁻¹ * (g * x * g⁻¹) := by group
  have hconjN : ∀ x : X, x ∈ Subgroup.centralizer ({a} : Set X) ↔
      g * x * g⁻¹ ∈ Subgroup.centralizer ({a} : Set X) := by
    intro x
    rw [← h1 x, heq]
  have hgN : g ∈ Subgroup.normalizer ((Subgroup.centralizer ({a} : Set X) : Subgroup X) : Set X) :=
    Subgroup.mem_normalizer_iff.mpr hconjN
  rcases hma.le_iff.mp (Subgroup.le_normalizer : Subgroup.centralizer ({a} : Set X) ≤
      Subgroup.normalizer ((Subgroup.centralizer ({a} : Set X) : Subgroup X) : Set X)) with hN | hN
  · have hnorm : (Subgroup.centralizer ({a} : Set X)).Normal := Subgroup.normalizer_eq_top_iff.mp hN
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.centralizer ({a} : Set X)) with h | h
    · exact ha1 (Subgroup.mem_bot.mp (h ▸ Subgroup.mem_centralizer_singleton_iff.mpr rfl))
    · exact hma.1 h
  · have hgC : g ∈ Subgroup.centralizer ({a} : Set X) := hN ▸ hgN
    have hcomm : g * a = a * g := Subgroup.mem_centralizer_singleton_iff.mp hgC
    apply hba
    rw [← hg, hcomm]
    group

end Abstract

section U3

theorem lie3U3_pairGen {Y : Type} [Group Y] (hl : LieModel Y .PSU 3 3 1) {a b : Y} (ha2 : a * a = 1)
    (ha1 : a ≠ 1) (hb2 : b * b = 1) (hb1 : b ≠ 1) (hba : b ≠ a) (hab : a * b = b * a) :
    Subgroup.centralizer ({a} : Set Y) ⊔ Subgroup.centralizer ({b} : Set Y) = ⊤ := by
  have hao : orderOf a = 2 := orderOf_eq_prime (by rw [pow_two]; exact ha2) ha1
  have hbo : orderOf b = 2 := orderOf_eq_prime (by rw [pow_two]; exact hb2) hb1
  obtain ⟨hp, hf, K, _, _, hK, ⟨e₀⟩⟩ := CFSG.GH74.Generic.lieModel_psu_data hl
  have h : LocalAnalysis.ComponentInitial.UnitaryFieldData 3 1 K :=
    ⟨hp, hf, by rw [hK, ← pow_mul, mul_comm]⟩
  refine sup_centralizer_eq_top_of_mulEquiv e₀ ?_
  exact E3C269G.sup_centralizer_eq_top_psu3 h (by norm_num)
    (by rw [MulEquiv.orderOf_eq]; exact hao) (by rw [MulEquiv.orderOf_eq]; exact hbo)
    (by rw [← map_mul, ← map_mul, hab]) (fun h' => hba (e₀.injective h').symm)

end U3

section Models


theorem lie3G2_centMax {Y : Type} [Group Y] [Finite Y]
    (hl : LieModel Y .G2 0 3 1) (hnab : ∃ a b : Y, a * b ≠ b * a) {z : Y} (hz2 : z * z = 1)
    (hz1 : z ≠ 1) : IsCoatom (Subgroup.centralizer ({z} : Set Y)) := by
  have hs : IsSimpleGroup Y := (CFSG.LieType.Catalog.lieModel_finite_simple Y _ _ _ _ hl).2.2
  have hne : (MulAut.conj z : MulAut Y) ≠ 1 := by
    intro h1
    have hc : z ∈ Subgroup.center Y := by
      rw [Subgroup.mem_center_iff]
      intro g
      have h2 := DFunLike.congr_fun h1 g
      simp only [MulAut.conj_apply, MulAut.one_apply] at h2
      calc g * z = (z * g * z⁻¹) * z := by rw [h2]
        _ = z * g := by group
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center Y) with h | h
    · rw [h, Subgroup.mem_bot] at hc
      exact hz1 hc
    · obtain ⟨a, b, hab⟩ := hnab
      exact hab (Subgroup.mem_center_iff.mp (h ▸ Subgroup.mem_top b) a)
  have key := CFSG.GH74.GLS.Stage2.Signalizer.Odd87.g2ThreeMax_of_cert Y hl (MulAut.conj z)
    (by rw [← map_mul, hz2, map_one]) hne
  have heq : (MulAut.conj z : MulAut Y).toMonoidHom.eqLocus (MonoidHom.id Y) =
      Subgroup.centralizer ({z} : Set Y) := by
    ext g
    rw [Subgroup.mem_centralizer_singleton_iff]
    constructor
    · intro h
      have h' : z * g * z⁻¹ = g := h
      calc g * z = (z * g * z⁻¹) * z := by rw [h']
        _ = z * g := by group
    · intro h
      show z * g * z⁻¹ = g
      calc z * g * z⁻¹ = (g * z) * z⁻¹ := by rw [h]
        _ = g := by group
  rwa [heq] at key


theorem lie3G2_isConj {Y : Type} [Group Y] (hl : LieModel Y .G2 0 3 1) {a b : Y} (ha : orderOf a = 2)
    (hb : orderOf b = 2) : ∃ g : Y, g * a * g⁻¹ = b := by
  obtain ⟨g, hg⟩ := isConj_iff.1 (CFSG.GH74.GLS.IVK.Proofs2.Ivk47ab.ivk_4_7a_G2_aux Nat.prime_three
    (by norm_num) hl a b ha hb)
  exact ⟨g, hg⟩

theorem lie3G2_pairGen {Y : Type} [Group Y] [Finite Y]
    (hl : LieModel Y .G2 0 3 1) (hnab : ∃ a b : Y, a * b ≠ b * a) {a b : Y} (ha2 : a * a = 1)
    (ha1 : a ≠ 1) (hb2 : b * b = 1) (hb1 : b ≠ 1) (hba : b ≠ a) :
    Subgroup.centralizer ({a} : Set Y) ⊔ Subgroup.centralizer ({b} : Set Y) = ⊤ := by
  have hs : IsSimpleGroup Y := (CFSG.LieType.Catalog.lieModel_finite_simple Y _ _ _ _ hl).2.2
  refine sup_centralizer_eq_top_of_coatom (fun z hz2 hz1 => lie3G2_centMax hl hnab hz2 hz1)
    (fun a b ha2 ha1 hb2 hb1 => lie3G2_isConj hl (orderOf_eq_prime (by rw [pow_two]; exact ha2) ha1)
      (orderOf_eq_prime (by rw [pow_two]; exact hb2) hb1)) ha2 ha1 hb2 hb1 hba

theorem lie3D4_pairGen {Y : Type} [Group Y] [Finite Y] (hl : LieModel Y .trialityD4 0 3 1) {a b : Y}
    (ha2 : a * a = 1) (ha1 : a ≠ 1) (hb2 : b * b = 1) (hb1 : b ≠ 1) (hba : b ≠ a)
    (hab : a * b = b * a) :
    Subgroup.centralizer ({a} : Set Y) ⊔ Subgroup.centralizer ({b} : Set Y) = ⊤ := by
  have hp : Nat.Prime 3 := Nat.prime_three
  have : Fact (Nat.Prime 3) := ⟨hp⟩
  have hs : IsSimpleGroup Y := (CFSG.LieType.Catalog.lieModel_finite_simple Y _ _ _ _ hl).2.2
  have hch : (StatedLieTag.trialityD4) ∈ chevalleyExceptionalTags := by decide
  have hadm : StatedLieAdmissible .trialityD4 0 3 1 :=
    (CFSG.ClassicalInvolution.Upgrade.chevalleyExceptionalModel_of_lieModel hch hl).1
  obtain ⟨ψ, hψs, hψk⟩ := CFSG.ClassicalInvolution.Upgrade.lieModelCentralCover .trialityD4 0 3 1
    hp (by norm_num) trivial hadm Y hl
  have hZ := center_modelUniv_d4_three hp
  have hψi : Function.Injective ψ := by
    rw [← MonoidHom.ker_eq_bot_iff]
    exact le_bot_iff.mp (hψk.trans hZ.le)
  let e : (modelUniv .trialityD4 0 3 1 hp).K ≃* Y := MulEquiv.ofBijective ψ ⟨hψi, hψs⟩
  refine sup_centralizer_eq_top_of_mulEquiv e.symm ?_
  exact G2D4Models.sup_centralizer_eq_top_model_td4 (p := 3) (by norm_num) hadm
    (u := e.symm a) (v := e.symm b) (by rw [← map_mul, ha2, map_one]) (by rw [← map_mul, hb2, map_one])
    (fun h => ha1 (e.symm.injective (h.trans (map_one e.symm).symm)))
    (fun h => hb1 (e.symm.injective (h.trans (map_one e.symm).symm)))
    (fun h => hba (e.symm.injective h).symm) (by rw [← map_mul, ← map_mul, hab])

theorem lie3S3Gen_proved : Lie3S3Gen := by
  intro Y _ _ hnab hl a b ha2 ha1 hb2 hb1 hba hab
  rcases hl with h | h | h
  · exact lie3U3_pairGen h ha2 ha1 hb2 hb1 hba hab
  · exact lie3G2_pairGen h hnab ha2 ha1 hb2 hb1 hba
  · exact lie3D4_pairGen h ha2 ha1 hb2 hb1 hba hab

end Models

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3.SecEL

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3

open CFSG.ClassicalInvolution.Q3.TL4

section Main


theorem secEdgelessConcl163_proved {n : ℕ} (hcit : CIT3Below n) (hP : TightBelowRPlus 3 n) :
    SecEdgelessConcl163 n :=
  secEdgelessConcl163_of hcit hP SecEL.lie3S3Gen_proved

end Main

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3
