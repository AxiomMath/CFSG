module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Harada.L27.YData
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Harada.L27.YComponentsB
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Harada.L27.YSwap
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Harada.L27.FpfInvolution
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Harada.L27.RadicalLemmas

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Harada.L27

open Subgroup CFSG.Open

private theorem exists_factor {G : Type*} [Group G] {F : Subgroup G} {v : G}
    (hcomm : ∀ f ∈ F, f * v = v * f) {t : G} (ht : t ∈ F ⊔ Subgroup.zpowers v) :
    ∃ f ∈ F, ∃ k : ℤ, f * v ^ k = t := by
  have hcomm' : ∀ f ∈ F, ∀ k : ℤ, Commute f (v ^ k) :=
    fun f hf k => (show Commute f v from hcomm f hf).zpow_right k
  have ht' : t ∈ Subgroup.closure ((F : Set G) ∪ (Subgroup.zpowers v : Set G)) := by
    rw [← Subgroup.sup_eq_closure]
    exact ht
  refine Subgroup.closure_induction (p := fun x _ => ∃ f ∈ F, ∃ k : ℤ, f * v ^ k = x)
    ?_ ?_ ?_ ?_ ht'
  · rintro x (hx | hx)
    · exact ⟨x, hx, 0, by simp⟩
    · obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hx
      exact ⟨1, F.one_mem, k, by rw [one_mul, hk]⟩
  · exact ⟨1, F.one_mem, 0, by simp⟩
  · rintro x y hx hy ⟨f, hf, k, rfl⟩ ⟨g, hg, l, rfl⟩
    refine ⟨f * g, F.mul_mem hf hg, k + l, ?_⟩
    calc (f * g) * v ^ (k + l) = (f * g) * (v ^ k * v ^ l) := by rw [zpow_add]
      _ = f * (g * v ^ k) * v ^ l := by group
      _ = f * (v ^ k * g) * v ^ l := by rw [(hcomm' g hg k).eq]
      _ = (f * v ^ k) * (g * v ^ l) := by group
  · rintro x hx ⟨f, hf, k, rfl⟩
    refine ⟨f⁻¹, F.inv_mem hf, -k, ?_⟩
    have hc : Commute f⁻¹ (v ^ (-k)) := by
      have h1 := (hcomm' f hf k).inv_inv
      rwa [← zpow_neg] at h1
    calc f⁻¹ * v ^ (-k) = v ^ (-k) * f⁻¹ := hc.eq
      _ = (v ^ k)⁻¹ * f⁻¹ := by rw [zpow_neg]
      _ = (f * v ^ k)⁻¹ := (mul_inv_rev f (v ^ k)).symm

private theorem card_centralizer_equiv {H K : Type*} [Group H] [Group K] (φ : H ≃* K) (h : H) :
    Nat.card (Subgroup.centralizer ({h} : Set H)) =
      Nat.card (Subgroup.centralizer ({φ h} : Set K)) := by
  refine Nat.card_congr ?_
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro x
    exact ⟨φ x.1, by
      rw [Subgroup.mem_centralizer_singleton_iff]
      rw [← map_mul, ← map_mul, Subgroup.mem_centralizer_singleton_iff.mp x.2]⟩
  · intro y
    exact ⟨φ.symm y.1, by
      rw [Subgroup.mem_centralizer_singleton_iff]
      apply φ.injective
      simp only [map_mul]
      rw [φ.apply_symm_apply, Subgroup.mem_centralizer_singleton_iff.mp y.2]⟩
  · intro x
    apply Subtype.ext
    simp
  · intro y
    apply Subtype.ext
    simp

theorem not_normalizes_of_eq {Y : Type*} [Group Y] {F T₂ : Subgroup Y} {v : Y}
    (eF : F ≃* alternatingGroup (Fin 5)) (e₂ : T₂ ≃* alternatingGroup (Fin 5))
    (hcomm : ∀ a ∈ F, ∀ b ∈ T₂, a * b = b * a) (hv2 : v * v = 1) (hv1 : v ≠ 1)
    (hFv : ∀ f ∈ F, f * v = v * f)
    (hC : ∀ g : Y, g * v = v * g → g ∈ F ⊔ Subgroup.zpowers v)
    (hv₂ : ∀ t ∈ T₂, v * t * v⁻¹ ∈ T₂) : False := by
  have hkey : ∀ t ∈ T₂, t * v = v * t → t = 1 ∨ t = v := by
    intro t htT htv
    obtain ⟨f, hf, k, hk⟩ := exists_factor hFv (hC t htv)
    have hf_eq : f = t * v ^ (-k) := by
      rw [← hk, mul_assoc, ← zpow_add, add_neg_cancel, zpow_zero, mul_one]
    have hfcomm : ∀ a ∈ F, a * f = f * a := by
      intro a ha
      have h1 : Commute a t := hcomm a ha t htT
      have h2 : Commute a (v ^ (-k)) := (show Commute a v from hFv a ha).zpow_right (-k)
      rw [hf_eq]
      exact h1.mul_right h2
    have hf1 : f = 1 := eq_one_of_forall_comm_of_equiv_a5 F eF hf hfcomm
    have ht : t = v ^ k := by rw [← hk, hf1, one_mul]
    rw [ht]
    have h2z : v ^ (2 : ℤ) = 1 := by
      rw [show (2 : ℤ) = ((2 : ℕ) : ℤ) by norm_num, zpow_natCast, pow_two, hv2]
    obtain ⟨m, hm⟩ := Int.even_or_odd' k
    rcases hm with hm | hm
    · left
      rw [hm, zpow_mul, h2z, one_zpow]
    · right
      rw [hm, zpow_add, zpow_mul, h2z, one_zpow, one_mul, zpow_one]
  by_cases hvT : v ∈ T₂
  ·
    let z : T₂ := ⟨v, hvT⟩
    have hz2 : z * z = 1 := by ext; simpa using hv2
    have hw_ne : e₂ z ≠ 1 := by
      intro h
      have hz : z = 1 := e₂.injective (by rw [h, map_one])
      exact hv1 (congrArg Subtype.val hz)
    have hw2 : e₂ z * e₂ z = 1 := by
      rw [← map_mul, hz2, map_one]
    have h4 : Nat.card (Subgroup.centralizer ({z} : Set T₂)) = 4 := by
      rw [card_centralizer_equiv e₂ z]
      exact card_centralizer_involution_a5 (e₂ z) hw_ne hw2
    have hCle : Subgroup.centralizer ({z} : Set T₂) ≤ Subgroup.zpowers z := by
      intro y hy
      have hyc : y * z = z * y := Subgroup.mem_centralizer_singleton_iff.mp hy
      have hyv : (y : Y) * v = v * (y : Y) := by
        simpa using congrArg Subtype.val hyc
      rcases hkey (y : Y) y.2 hyv with h | h
      · have hy1 : y = 1 := Subtype.ext h
        rw [hy1]
        exact Subgroup.one_mem _
      · have hyz : y = z := Subtype.ext h
        rw [hyz]
        exact Subgroup.mem_zpowers z
    haveI : Fintype T₂ := Fintype.ofEquiv (alternatingGroup (Fin 5)) e₂.toEquiv.symm
    have hbound : Nat.card (Subgroup.centralizer ({z} : Set T₂)) ≤ 2 := by
      have h1 : Nat.card (Subgroup.centralizer ({z} : Set T₂)) ≤ Nat.card (Subgroup.zpowers z) :=
        Subgroup.card_le_of_le hCle
      have h2 : Nat.card (Subgroup.zpowers z) ≤ 2 := by
        rw [Nat.card_eq_fintype_card]
        exact card_zpowers_le z (by norm_num) (by rw [pow_two]; exact hz2)
      omega
    omega
  ·
    haveI : Fintype T₂ := Fintype.ofEquiv (alternatingGroup (Fin 5)) e₂.toEquiv.symm
    let N : Subgroup Y := Subgroup.normalizer (T₂ : Set Y)
    have hT₂N : T₂ ≤ N := Subgroup.le_normalizer
    have hvN : v ∈ N := by
      rw [Subgroup.mem_normalizer_iff]
      intro h
      constructor
      · exact hv₂ h
      · intro hh
        have h2 := hv₂ (v * h * v⁻¹) hh
        have h3 : v * (v * h * v⁻¹) * v⁻¹ = h := by
          calc v * (v * h * v⁻¹) * v⁻¹ = (v * v) * h * (v * v)⁻¹ := by group
            _ = h := by rw [hv2]; group
        rwa [h3] at h2
    haveI : (T₂.subgroupOf N).Normal := by
      show (T₂.subgroupOf (Subgroup.normalizer (T₂ : Set Y))).Normal
      infer_instance
    haveI : Finite (T₂.subgroupOf N) :=
      Finite.of_injective (Subgroup.subgroupOfEquivOfLe hT₂N).toFun
        (Subgroup.subgroupOfEquivOfLe hT₂N).injective
    have hv' : (⟨v, hvN⟩ : N) * ⟨v, hvN⟩ = 1 := by ext; simpa using hv2
    have hC' : ∀ s ∈ T₂.subgroupOf N, (⟨v, hvN⟩ : N) * s = s * ⟨v, hvN⟩ → s = 1 := by
      intro s hs hvs
      have hsT : (s : Y) ∈ T₂ := Subgroup.mem_subgroupOf.mp hs
      have hval : (s : Y) * v = v * (s : Y) := by
        have h := congrArg (fun t : N => (t : Y)) hvs
        simpa using h.symm
      rcases hkey (s : Y) hsT hval with h | h
      · exact Subtype.ext h
      · exact absurd (h ▸ hsT) hvT
    have hcommS : ∀ a ∈ T₂.subgroupOf N, ∀ b ∈ T₂.subgroupOf N, a * b = b * a :=
      (normal_fpf_involution hv' hC').2.1
    have hcommT : ∀ a ∈ T₂, ∀ b ∈ T₂, a * b = b * a := by
      intro a ha b hb
      let ψ : (T₂.subgroupOf N) ≃* T₂ := Subgroup.subgroupOfEquivOfLe hT₂N
      have hxy : ψ.symm ⟨a, ha⟩ * ψ.symm ⟨b, hb⟩ =
          ψ.symm ⟨b, hb⟩ * ψ.symm ⟨a, ha⟩ := by
        apply Subtype.ext
        simpa using hcommS (ψ.symm ⟨a, ha⟩) (ψ.symm ⟨a, ha⟩).2
          (ψ.symm ⟨b, hb⟩) (ψ.symm ⟨b, hb⟩).2
      have h2 := congrArg ψ hxy
      simp only [map_mul, MulEquiv.apply_symm_apply] at h2
      simpa using h2
    obtain ⟨x, hx3⟩ := exists_orderOf_eq_three_a5
    have hx_ne : x ≠ 1 := by
      rintro rfl
      rw [orderOf_one] at hx3
      exact (by norm_num : (1 : ℕ) ≠ 3) hx3
    let y : T₂ := e₂.symm x
    have hy_ne : y ≠ 1 := by
      intro hy
      have h : x = 1 := by
        have := congrArg e₂ hy
        simpa [y] using this
      exact hx_ne h
    have hycomm : ∀ f ∈ T₂, f * (y : Y) = (y : Y) * f := by
      intro f hf
      exact hcommT f hf y y.2
    have hy1 : (y : Y) = 1 := eq_one_of_forall_comm_of_equiv_a5 T₂ e₂ y.2 hycomm
    exact hy_ne (Subtype.ext hy1)

theorem v_conj_eq {Y : Type} [Group Y] [Finite Y] {P F : Subgroup Y} {v : Y}
    (h : FinalData Y P F v) {T₁ T₂ : Subgroup Y} (hT : TwoA5 Y T₁ T₂) (hF : F ≤ T₁ ⊔ T₂) :
    T₁.map (MulAut.conj v).toMonoidHom = T₂ := by
  obtain ⟨eF⟩ := h.F_iso
  obtain ⟨e₁⟩ := component_equiv_a5 h.free hT.comp₁ hT.card₁
  obtain ⟨e₂⟩ := component_equiv_a5 h.free hT.comp₂ hT.card₂
  have hcomm : ∀ a ∈ T₁, ∀ b ∈ T₂, a * b = b * a :=
    component_commute_of_ne hT.comp₁ hT.comp₂ hT.ne
  have hdisj : T₁ ⊓ T₂ = ⊥ := component_inf_eq_bot h.free hT.comp₁ hT.comp₂ hT.ne
  have hcomp : IsComponentOf (T₁.map (MulAut.conj v).toMonoidHom) ⊤ :=
    isComponentOf_map_conj hT.comp₁ v
  rcases hT.only _ hcomp with h1 | h1
  · exfalso
    have hc₂ : T₂.map (MulAut.conj v).toMonoidHom = T₂ := by
      have hcomp₂ : IsComponentOf (T₂.map (MulAut.conj v).toMonoidHom) ⊤ :=
        isComponentOf_map_conj hT.comp₂ v
      rcases hT.only _ hcomp₂ with h2 | h2
      · exact absurd (Subgroup.map_injective (f := (MulAut.conj v).toMonoidHom)
          (MulAut.conj v).injective (by rw [h1, h2])) hT.ne
      · exact h2
    have hv₁ : ∀ t ∈ T₁, v * t * v⁻¹ ∈ T₁ := by
      intro t ht
      have hmem : (MulAut.conj v) t ∈ T₁.map (MulAut.conj v).toMonoidHom :=
        Subgroup.mem_map_of_mem _ ht
      rw [h1] at hmem
      simpa [MulAut.conj_apply] using hmem
    have hv₂ : ∀ t ∈ T₂, v * t * v⁻¹ ∈ T₂ := by
      intro t ht
      have hmem : (MulAut.conj v) t ∈ T₂.map (MulAut.conj v).toMonoidHom :=
        Subgroup.mem_map_of_mem _ ht
      rw [hc₂] at hmem
      simpa [MulAut.conj_apply] using hmem
    rcases eq_or_inf_eq_bot_of_le_sup hcomm hF eF hT.card₁ hT.card₂ with hF₁ | hF₂ | hdiag
    · exact not_normalizes_of_eq eF e₂
        (fun a ha b hb => hcomm a (hF₁ ▸ ha) b hb) h.v_sq h.v_ne_one h.F_comm h.centralizer_le hv₂
    · exact not_normalizes_of_eq eF e₁
        (fun a ha b hb => (hcomm b hb a (hF₂ ▸ ha)).symm) h.v_sq h.v_ne_one h.F_comm
        h.centralizer_le hv₁
    · have hFcard : Nat.card F = 60 := by
        rw [Nat.card_congr eF.toEquiv, card_alternatingGroup_five]
      have hcent := centralizes_of_diagonal hcomm hdisj hF hdiag.1 hdiag.2 hT.card₁ hT.card₂
        hFcard hv₁ hv₂ h.F_comm
      have hle : T₁ ⊔ T₂ ≤ Subgroup.centralizer ({v} : Set Y) := by
        apply sup_le
        · intro t ht
          exact Subgroup.mem_centralizer_singleton_iff.mpr (hcent.1 t ht)
        · intro t ht
          exact Subgroup.mem_centralizer_singleton_iff.mpr (hcent.2 t ht)
      have hcard_sup : Nat.card ↥(T₁ ⊔ T₂) = 3600 := by
        rw [card_sup_pair h.free hT.comp₁ hT.comp₂ hT.ne, hT.card₁, hT.card₂]
      have hcard_le : Nat.card ↥(T₁ ⊔ T₂) ≤ Nat.card ↥(Subgroup.centralizer ({v} : Set Y)) :=
        Subgroup.card_le_of_le hle
      have h120 : Nat.card ↥(Subgroup.centralizer ({v} : Set Y)) ≤ 120 :=
        card_centralizer_le_one_twenty F eF h.v_sq h.F_comm h.centralizer_le
      omega
  · exact h1

end CFSG.EvenSporadicStandard.HNRecog.Harada.L27
