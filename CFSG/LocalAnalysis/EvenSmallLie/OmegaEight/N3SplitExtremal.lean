module

public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.N3SplitBasic
public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.N3SplitModel

public section

namespace CFSG.EvenSmallLie.OmegaEight.N3Split

open Subgroup Matrix CFSG.EvenSmallLie.OmegaEight.Stage2
open scoped Pointwise

variable {G : Type*} [Group G]

theorem centralizer_conj (g t : G) :
    centralizer ({g * t * g⁻¹} : Set G) =
      (centralizer ({t} : Set G)).map (MulAut.conj g).toMonoidHom := by
  ext x
  constructor
  · intro hx
    rw [mem_centralizer_singleton_iff] at hx
    refine ⟨g⁻¹ * x * g, mem_centralizer_singleton_iff.2 ?_, by simp [mul_assoc]⟩
    calc g⁻¹ * x * g * t = g⁻¹ * (x * (g * t * g⁻¹)) * g := by group
      _ = g⁻¹ * ((g * t * g⁻¹) * x) * g := by rw [hx]
      _ = t * (g⁻¹ * x * g) := by group
  · rintro ⟨y, hy, rfl⟩
    have hy' : y * t = t * y := mem_centralizer_singleton_iff.1 hy
    rw [mem_centralizer_singleton_iff]
    simp only [MulEquiv.toMonoidHom_eq_coe, MonoidHom.coe_ofClass, MulAut.conj_apply]
    calc g * y * g⁻¹ * (g * t * g⁻¹) = g * (y * t) * g⁻¹ := by group
      _ = g * (t * y) * g⁻¹ := by rw [hy']
      _ = g * t * g⁻¹ * (g * y * g⁻¹) := by group

theorem eq_map_of_smul_eq {K A B : Subgroup G} (hA : A ≤ K) (hB : B ≤ K) {c : K}
    (hc : MulAut.conj c • (B.subgroupOf K) = A.subgroupOf K) :
    A = B.map (MulAut.conj (c : G)).toMonoidHom := by
  ext x
  constructor
  · intro hx
    have h1 : (⟨x, hA hx⟩ : K) ∈ MulAut.conj c • (B.subgroupOf K) := by
      rw [hc]
      exact Subgroup.mem_subgroupOf.2 hx
    rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem] at h1
    have h2 : (c : G)⁻¹ * x * c ∈ B := by
      have := Subgroup.mem_subgroupOf.1 h1
      simpa [MulAut.smul_def, MulAut.conj_symm_apply] using this
    refine ⟨(c : G)⁻¹ * x * c, h2, ?_⟩
    simp only [MulEquiv.toMonoidHom_eq_coe, MonoidHom.coe_ofClass, MulAut.conj_apply]
    group
  · rintro ⟨y, hy, rfl⟩
    have h1 : MulAut.conj c • (⟨y, hB hy⟩ : K) ∈ MulAut.conj c • (B.subgroupOf K) :=
      Subgroup.smul_mem_pointwise_smul _ _ _ (Subgroup.mem_subgroupOf.2 hy)
    rw [hc] at h1
    have := Subgroup.mem_subgroupOf.1 h1
    simpa [MulAut.smul_def] using this

section Hyp

variable {M : Model} {t : G} {TH W : Subgroup G} {φ : W ≃* Multiplicative (Fin 12 → ZMod 2)}
  {a : G}

theorem exists_extremal_of_odd [Finite G] (h : Stage2Hyp M t TH W φ) {T : Subgroup G}
    (hT2 : IsPGroup 2 T) {u g : G} (hu : u = g * t * g⁻¹)
    (hodd : Odd (T.relIndex (centralizer ({u} : Set G)))) :
    ∃ g' : G, u = g' * t * g'⁻¹ ∧
      T ⊓ centralizer ({u} : Set G) = TH.map (MulAut.conj g').toMonoidHom := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set K := centralizer ({u} : Set G) with hK
  set P := T ⊓ K with hP
  set P' := TH.map (MulAut.conj g).toMonoidHom with hP'
  have hKeq : K = (centralizer ({t} : Set G)).map (MulAut.conj g).toMonoidHom := by
    rw [hK, hu, centralizer_conj]
  have hP'K : P' ≤ K := by
    rw [hKeq]
    exact map_mono h.TH_le
  have hPK : P ≤ K := inf_le_right
  have hS : IsPGroup 2 (P.subgroupOf K) :=
    (hT2.to_le inf_le_left).of_equiv (Subgroup.subgroupOfEquivOfLe hPK).symm
  have hS' : IsPGroup 2 (P'.subgroupOf K) :=
    (h.TH_pgroup.map _).of_equiv (Subgroup.subgroupOfEquivOfLe hP'K).symm
  have hi : ¬ 2 ∣ (P.subgroupOf K).index := by
    have e : (P.subgroupOf K).index = T.relIndex K := by
      rw [Subgroup.relIndex, hP]
      congr 1
      ext x
      simp [Subgroup.mem_subgroupOf]
    rw [e]
    exact Nat.not_even_iff_odd.2 hodd ∘ even_iff_two_dvd.2
  have hi' : ¬ 2 ∣ (P'.subgroupOf K).index := by
    have e : (P'.subgroupOf K).index = (TH.subgroupOf (centralizer ({t} : Set G))).index := by
      have h1 := relIndex_map_map_of_injective (f := (MulAut.conj g).toMonoidHom) TH
        (centralizer ({t} : Set G)) (MulAut.conj g).injective
      rw [← hKeq] at h1
      exact h1
    rw [e]
    exact h.TH_index
  obtain ⟨c, hc⟩ := MulAction.exists_smul_eq K (hS'.toSylow hi') (hS.toSylow hi)
  refine ⟨c * g, ?_, ?_⟩
  · have hcu : (c : G) * u * (c : G)⁻¹ = u := by
      have := mem_centralizer_singleton_iff.1 c.2
      rw [this, mul_inv_cancel_right]
    rw [← hcu, hu]
    group
  · have h1 := congrArg (fun S : Sylow 2 K => (S : Subgroup K)) hc
    simp only [Sylow.coe_subgroup_smul, IsPGroup.toSylow_coe] at h1
    have h2 := eq_map_of_smul_eq hPK hP'K h1
    rw [h2, hP', Subgroup.map_map]
    congr 1
    ext y
    simp [mul_assoc]

theorem card_center_le [Finite G] (hX : SplitExtra t TH W a) {P : Subgroup G} {g : G}
    (hP : P = TH.map (MulAut.conj g).toMonoidHom) :
    Nat.card ↥(P ⊓ centralizer (P : Set G)) ≤ 4 := by
  classical
  have hsub : ∀ z ∈ P ⊓ centralizer (P : Set G),
      z ∈ ({g * g⁻¹, g * a * g⁻¹, g * t * g⁻¹, g * (t * a) * g⁻¹} : Finset G) := by
    rintro z ⟨hzP, hzc⟩
    rw [hP] at hzP
    obtain ⟨y, hy, rfl⟩ := hzP
    have hyc : ∀ x ∈ TH, y * x = x * y := by
      intro x hx
      have h1 : (MulAut.conj g).toMonoidHom x ∈ P := by
        rw [hP]
        exact ⟨x, hx, rfl⟩
      have h2 := mem_centralizer_iff.1 hzc _ h1
      simp only [MulEquiv.toMonoidHom_eq_coe, MonoidHom.coe_ofClass, MulAut.conj_apply] at h2
      have h3 : g * (x * y) * g⁻¹ = g * (y * x) * g⁻¹ := by
        calc g * (x * y) * g⁻¹ = g * x * g⁻¹ * (g * y * g⁻¹) := by group
          _ = g * y * g⁻¹ * (g * x * g⁻¹) := h2
          _ = g * (y * x) * g⁻¹ := by group
      exact (mul_left_cancel (mul_right_cancel h3)).symm
    simp only [MulEquiv.toMonoidHom_eq_coe, MonoidHom.coe_ofClass, MulAut.conj_apply,
      Finset.mem_insert, Finset.mem_singleton]
    rcases hX.center y hy hyc with rfl | rfl | rfl | rfl
    · left; group
    · right; left; rfl
    · right; right; left; rfl
    · right; right; right; rfl
  have hle : Nat.card ↥(P ⊓ centralizer (P : Set G)) ≤
      ({g * g⁻¹, g * a * g⁻¹, g * t * g⁻¹, g * (t * a) * g⁻¹} : Finset G).card := by
    rw [← Nat.card_eq_finsetCard]
    refine Nat.card_le_card_of_injective (fun z => ⟨z.1, hsub z.1 z.2⟩) ?_
    intro x y e
    exact Subtype.ext (congrArg Subtype.val e :)
  exact hle.trans Finset.card_le_four

theorem isCand_of_extremal [Finite G] (h : Stage2Hyp M t TH W φ) (hF : SplitFacts M)
    (hX : SplitExtra t TH W a) {T : Subgroup G} (hTN : T ≤ NW W) (hT2 : IsPGroup 2 T)
    (hWT : W ≤ T) {u g : G} (hu : u = g * t * g⁻¹) (huT : u ∈ T)
    (hC : T ⊓ centralizer ({u} : Set G) = TH.map (MulAut.conj g).toMonoidHom) :
    IsCand (rhoImg W φ T) (rhoG W φ u) := by
  have huN : u ∈ NW W := hTN huT
  have hfix := card_fixM_le' h hF hu huN
  have hu2 : rhoG W φ u * rhoG W φ u = 1 := by
    rw [← rhoG_mul huN huN, hu, h.conj_mul_self g, rhoG_one]
  set S := rhoImg W φ T with hS
  set P := T ⊓ centralizer ({u} : Set G) with hP
  have hPN : P ≤ NW W := inf_le_left.trans hTN
  have hcardP : Nat.card P = 2 ^ 14 := by
    rw [hC, Subgroup.card_map_of_injective (MulAut.conj g).injective, card_TH h,
      hF.card_TC, hF.card_fixM_tbar]
    norm_num
  have hρP : rhoImg W φ P ≤ S ⊓ centralizer ({rhoG W φ u} : Set GL12) := by
    intro y hy
    obtain ⟨c, hc, rfl⟩ := (mem_rhoImg hPN).1 hy
    refine ⟨(mem_rhoImg hTN).2 ⟨c, hc.1, rfl⟩, mem_centralizer_singleton_iff.2 ?_⟩
    have hcu : c * u = u * c := mem_centralizer_singleton_iff.1 hc.2
    rw [← rhoG_mul (hPN hc) huN, ← rhoG_mul huN (hPN hc), hcu]
  have hPW : P ⊓ centralizer (W : Set G) ≤ W ⊓ centralizer ({u} : Set G) :=
    fun x hx => ⟨inf_centralizer_le_W hT2 h.sylow_W ⟨hx.1.1, hx.2⟩, hx.1.2⟩
  refine ⟨hu2, ?_, hfix, ?_, ?_⟩
  · intro e
    rw [e, card_fixM_one] at hfix
    norm_num at hfix
  · have h1 := card_eq_card_rhoImg_mul (φ := φ) hPN
    rw [hcardP] at h1
    have h2 : Nat.card ↥(P ⊓ centralizer (W : Set G)) ≤ Nat.card (fixM (rhoG W φ u : Mat12)) :=
      (Subgroup.card_le_of_le hPW).trans (card_inf_centralizer_W φ huN).le
    have h3 : Nat.card (rhoImg W φ P) ≤
        Nat.card ↥(S ⊓ centralizer ({rhoG W φ u} : Set GL12)) := Subgroup.card_le_of_le hρP
    rw [h1]
    exact Nat.mul_le_mul h3 h2
  ·
    set ZZ : Subgroup G := P ⊓ centralizer (P : Set G) with hZZ
    have hZZ4 := card_center_le hX hC
    have huZ : u ∈ ZZ := by
      refine ⟨⟨huT, mem_centralizer_singleton_iff.2 rfl⟩, mem_centralizer_iff.2 fun x hx => ?_⟩
      exact (mem_centralizer_singleton_iff.1 hx.2)
    have huW : u ∉ W := by
      intro huW'
      have e : rhoG W φ u = 1 := rhoG_W huW'
      rw [e, card_fixM_one] at hfix
      norm_num at hfix
    have hZW : Nat.card ↥(ZZ ⊓ W) ≤ 2 := by
      have hidx : (ZZ ⊓ W).relIndex ZZ ≠ 1 := by
        intro e
        rw [Subgroup.relIndex_eq_one] at e
        exact huW (e huZ).2
      have hmul := Subgroup.relIndex_mul_card (H := ZZ ⊓ W) (K := ZZ)
      rw [inf_of_le_left inf_le_left] at hmul
      have hpos : 0 < (ZZ ⊓ W).relIndex ZZ := Nat.pos_of_ne_zero
        (Subgroup.isFiniteRelIndex_of_finiteIndex (H := ZZ ⊓ W) (K := ZZ)).relIndex_ne_zero
      have h2 : 2 ≤ (ZZ ⊓ W).relIndex ZZ := by omega
      have : 2 * Nat.card ↥(ZZ ⊓ W) ≤ 4 := by
        calc 2 * Nat.card ↥(ZZ ⊓ W) ≤ (ZZ ⊓ W).relIndex ZZ * Nat.card ↥(ZZ ⊓ W) :=
              Nat.mul_le_mul_right _ h2
          _ = Nat.card ZZ := hmul
          _ ≤ 4 := hZZ4
      omega
    refine le_trans ?_ hZW
    refine Nat.card_le_card_of_injective (fun v => ⟨φ.symm (Multiplicative.ofAdd v.1), ?_⟩) ?_
    · set w := φ.symm (Multiplicative.ofAdd v.1) with hw
      have hwv : Multiplicative.toAdd (φ w) = v.1 := by simp [hw]
      have hwu : u * (w : G) * u⁻¹ = w := by
        have := (mem_fixM_rhoG_iff (φ := φ) huN w).1 (by rw [hwv]; exact v.2.1)
        exact this
      have hwP : (w : G) ∈ P := by
        refine ⟨hWT w.2, mem_centralizer_singleton_iff.2 ?_⟩
        calc (w : G) * u = u * w * u⁻¹ * u := by rw [hwu]
          _ = u * w := by group
      refine ⟨⟨hwP, mem_centralizer_iff.2 fun x hx => ?_⟩, w.2⟩
      have hxS : rhoG W φ x ∈ S := (mem_rhoImg hTN).2 ⟨x, hx.1, rfl⟩
      have hxu : rhoG W φ x * rhoG W φ u = rhoG W φ u * rhoG W φ x := by
        have hxu' : x * u = u * x := mem_centralizer_singleton_iff.1 hx.2
        rw [← rhoG_mul (hTN hx.1) huN, ← rhoG_mul huN (hTN hx.1), hxu']
      have hfixx := v.2.2 _ hxS hxu
      rw [← hwv] at hfixx
      have := (mem_fixM_rhoG_iff (φ := φ) (hTN hx.1) w).1 hfixx
      calc x * (w : G) = x * w * x⁻¹ * x := by group
        _ = w * x := by rw [this]
    · intro v₁ v₂ e
      have e' := congrArg Subtype.val e
      simp only at e'
      have := φ.symm.injective (Subtype.ext e' : (φ.symm (Multiplicative.ofAdd v₁.1) : W) =
        φ.symm (Multiplicative.ofAdd v₂.1))
      exact Subtype.ext (Multiplicative.ofAdd.injective this)

end Hyp

end CFSG.EvenSmallLie.OmegaEight.N3Split
