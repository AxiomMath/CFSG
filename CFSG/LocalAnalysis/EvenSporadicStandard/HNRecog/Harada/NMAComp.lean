module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Harada.NMAKey
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Harada.NMAOrder

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Harada

open Subgroup CFSG.EvenSporadicStandard.HNRecog.HaradaLA

variable {G : Type} [Group G] [Finite G] {t z z₁ : G} {ι : Elem2 6 →* G} {zv : V6}
  {R0 F : Subgroup G} {n : G}

private lemma coordElt_injective (hι : Function.Injective ι) :
    Function.Injective (coordElt ι) := by
  intro u v huv
  have h : Multiplicative.ofAdd u = Multiplicative.ofAdd v := hι huv
  simpa using congrArg Multiplicative.toAdd h

private lemma add_self_eq_zero_V6 (v : V6) : v + v = 0 := by
  funext i
  exact CharTwo.add_self_eq_zero (v i)

private theorem not_isMulCommutative_five :
    ¬ IsMulCommutative (alternatingGroup (Fin 5)) := by
  rw [alternatingGroup.isMulCommutative_iff_card_le_three, Nat.card_eq_fintype_card,
    Fintype.card_fin]
  norm_num

@[expose] def Fconj (n : G) (F : Subgroup G) : Subgroup G :=
  F.map (MulAut.conj n).toMonoidHom

theorem mem_Fconj {x : G} : x ∈ Fconj n F ↔ ∃ f ∈ F, n * f * n⁻¹ = x := by
  rw [Fconj, Subgroup.mem_map]
  constructor
  · rintro ⟨f, hf, hfx⟩
    exact ⟨f, hf, by simpa [MulAut.conj_apply] using hfx⟩
  · rintro ⟨f, hf, rfl⟩
    exact ⟨f, hf, by simp [MulAut.conj_apply]⟩

theorem Fconj_le_K (h : Setting25 G t z z₁ ι zv R0 F) (hn : n ∈ normalizer (ι.range : Set G))
    (hnz : n * z₁ * n⁻¹ = z) : Fconj n F ≤ Kgrp ι z := by
  intro x hx
  rw [Kgrp, Subgroup.mem_inf]
  rw [mem_Fconj] at hx
  obtain ⟨f, hf, hnf⟩ := hx
  have hfN : f ∈ normalizer (ι.range : Set G) := h.hD2.F_le_normalizer hf
  have hfz : f * z₁ = z₁ * f :=
    Subgroup.mem_centralizer_singleton_iff.mp (h.hD2.F_le hf).2
  refine ⟨?_, ?_⟩
  · rw [← hnf]
    exact mul_mem (mul_mem hn hfN) (inv_mem hn)
  · rw [← hnf, ← hnz]
    exact Subgroup.mem_centralizer_singleton_iff.mpr (by
      calc (n * f * n⁻¹) * (n * z₁ * n⁻¹) = n * (f * z₁) * n⁻¹ := by group
        _ = n * (z₁ * f) * n⁻¹ := by rw [hfz]
        _ = (n * z₁ * n⁻¹) * (n * f * n⁻¹) := by group)

theorem Fconj_equiv (h : Setting25 G t z z₁ ι zv R0 F) :
    Nonempty (↥(Fconj n F) ≃* alternatingGroup (Fin 5)) := by
  obtain ⟨e⟩ := h.hD2.F_iso
  exact ⟨(Subgroup.equivMapOfInjective F (MulAut.conj n).toMonoidHom
    (MulAut.conj n).injective).symm.trans e⟩

theorem card_Fconj (h : Setting25 G t z z₁ ι zv R0 F) : Nat.card (Fconj n F) = 60 := by
  obtain ⟨e⟩ := Fconj_equiv (n := n) h
  calc Nat.card (Fconj n F) = Nat.card (alternatingGroup (Fin 5)) := Nat.card_congr e.toEquiv
    _ = 60 := by
        rw [nat_card_alternatingGroup, Nat.card_eq_fintype_card, Fintype.card_fin]
        norm_num

theorem Fconj_inf_range (h : Setting25 G t z z₁ ι zv R0 F)
    (hn : n ∈ normalizer (ι.range : Set G)) : Fconj n F ⊓ ι.range = ⊥ := by
  have hFK : Fconj n F ≤ normalizer (ι.range : Set G) := by
    intro x hx
    rw [mem_Fconj] at hx
    obtain ⟨f, hf, hnf⟩ := hx
    rw [← hnf]
    exact mul_mem (mul_mem hn (h.hD2.F_le_normalizer hf)) (inv_mem hn)
  obtain ⟨e⟩ := Fconj_equiv (n := n) h
  haveI : IsSimpleGroup ↥(Fconj n F) := e.isSimpleGroup
  have hnorm : ((Fconj n F ⊓ ι.range).subgroupOf (Fconj n F)).Normal := by
    have h1 : (Fconj n F ⊓ ι.range).subgroupOf (Fconj n F) =
        (ι.range ⊓ Fconj n F).subgroupOf (Fconj n F) := by rw [inf_comm]
    rw [h1, Subgroup.inf_subgroupOf_right]
    exact Subgroup.normal_subgroupOf_of_le_normalizer hFK
  have hsimple := (Subgroup.isSimpleGroup_iff (H := Fconj n F)).mp inferInstance
  rcases hsimple.2 (Fconj n F ⊓ ι.range) inf_le_left hnorm with hbot | htop
  · exact hbot
  · exfalso
    have hle : Fconj n F ≤ ι.range := by
      intro x hx
      have : x ∈ Fconj n F ⊓ ι.range := by rw [htop]; exact hx
      exact (Subgroup.mem_inf.mp this).2
    have hcomm : IsMulCommutative ↥(Fconj n F) := by
      refine IsMulCommutative.of_comm fun a b => ?_
      apply Subtype.ext
      obtain ⟨α, hα⟩ := MonoidHom.mem_range.mp (hle a.2)
      obtain ⟨β, hβ⟩ := MonoidHom.mem_range.mp (hle b.2)
      show a.1 * b.1 = b.1 * a.1
      calc a.1 * b.1 = ι (α * β) := by rw [← hα, ← hβ, map_mul]
        _ = ι (β * α) := by rw [mul_comm]
        _ = b.1 * a.1 := by rw [map_mul, hβ, hα]
    exact not_isMulCommutative_five
      (Function.Surjective.isMulCommutative (f := e) e.surjective hcomm)

theorem Fconj_eichActs_eq_one (h : Setting25 G t z z₁ ι zv R0 F)
    (hn : n ∈ normalizer (ι.range : Set G)) (hnz : n * z₁ * n⁻¹ = z) {f : G}
    (hf : f ∈ Fconj n F) (hE : ∃ u : V6, EichActs ι zv f u) : f = 1 := by
  let S : Subgroup ↥(Fconj n F) :=
    { carrier := {x | ∃ u : V6, EichActs ι zv (x : G) u}
      mul_mem' := by
        rintro x y ⟨u, hu⟩ ⟨v, hv⟩
        exact ⟨u + v, hu.mul hv⟩
      one_mem' := ⟨0, EichActs.one zv⟩
      inv_mem' := by
        rintro x ⟨u, hu⟩
        exact ⟨u, hu.inv⟩ }
  have hSnorm : S.Normal := by
    refine ⟨fun x hx g => ?_⟩
    obtain ⟨u, hu⟩ := hx
    have hgK : g.1 ∈ Kgrp ι z := Fconj_le_K h hn hnz g.2
    obtain ⟨p, hpOm, hpz, hpacts⟩ := h.exists_acts_of_mem_K hgK
    exact ⟨p u, EichActs.conj hpacts (omegaMinus_le_orthMinus hpOm) hpz hu⟩
  obtain ⟨e⟩ := Fconj_equiv (n := n) h
  haveI : IsSimpleGroup ↥(Fconj n F) := e.isSimpleGroup
  haveI : S.Normal := hSnorm
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal S with hbot | htop
  · have hfS : (⟨f, hf⟩ : ↥(Fconj n F)) ∈ S := hE
    rw [hbot] at hfS
    exact Subtype.ext_iff.mp (Subgroup.mem_bot.mp hfS)
  · exfalso
    have hcomm : IsMulCommutative ↥(Fconj n F) := by
      refine IsMulCommutative.of_comm fun a b => ?_
      have haS : a ∈ S := by rw [htop]; exact Subgroup.mem_top a
      have hbS : b ∈ S := by rw [htop]; exact Subgroup.mem_top b
      obtain ⟨u, hu⟩ := haS
      obtain ⟨v, hv⟩ := hbS
      have hmem_range : a.1 * b.1 * a.1⁻¹ * b.1⁻¹ ∈ ι.range :=
        EichActs.comm_mem_range h.centralizer_le h.hD2.qm_zv hu hv
      have hmem_prod : a.1 * b.1 * a.1⁻¹ * b.1⁻¹ ∈ Fconj n F :=
        mul_mem (mul_mem (mul_mem a.2 b.2) (inv_mem a.2)) (inv_mem b.2)
      have hmem_inf : a.1 * b.1 * a.1⁻¹ * b.1⁻¹ ∈ Fconj n F ⊓ ι.range :=
        ⟨hmem_prod, hmem_range⟩
      rw [Fconj_inf_range h hn] at hmem_inf
      have hone : a.1 * b.1 * a.1⁻¹ * b.1⁻¹ = 1 := Subgroup.mem_bot.mp hmem_inf
      apply Subtype.ext
      show a.1 * b.1 = b.1 * a.1
      have h_eq : (a.1 * b.1) * (b.1 * a.1)⁻¹ = 1 := by
        rw [mul_inv_rev, ← mul_assoc]
        exact hone
      exact mul_inv_eq_one.mp h_eq
    exact not_isMulCommutative_five
      (Function.Surjective.isMulCommutative (f := e) e.surjective hcomm)

theorem conj_t_mem_range (h : Setting25 G t z z₁ ι zv R0 F)
    (hn : n ∈ normalizer (ι.range : Set G)) : n * t * n⁻¹ ∈ ι.range := by
  obtain ⟨g, hg⟩ := exists_acts h.injective_ι hn
  rw [← h.ι_tv, hg tv]
  exact MonoidHom.mem_range.mpr ⟨Multiplicative.ofAdd (g tv), rfl⟩

theorem conj_t_not_mem_Cgrp (h : Setting25 G t z z₁ ι zv R0 F)
    (hn : n ∈ normalizer (ι.range : Set G)) (hnz : n * z₁ * n⁻¹ = z) :
    n * t * n⁻¹ ∉ Cgrp ι zv := by
  intro hmem
  obtain ⟨v, hvz, hlam, _⟩ := h.coords_z₁
  obtain ⟨g, hg⟩ := exists_acts h.injective_ι hn
  have hgOm : g ∈ OmegaMinus := by
    have : g ∈ inducedGroup ι := ⟨n, hn, hg⟩
    rwa [h.omega] at this
  have hgv : g v = zv :=
    coordElt_injective (ι := ι) h.injective_ι (by
      rw [← hg v, hvz, hnz, ← h.coord_z])
  have hnt : n * t * n⁻¹ = coordElt ι (g tv) := by
    rw [← h.ι_tv, hg tv]
  rw [hnt] at hmem
  have hbil0 : bil (g tv) zv = 0 := (coordElt_mem_Cgrp (w := zv) h.injective_ι).mp hmem
  have hbil1 : bil (g tv) zv = 1 := by
    rw [← hgv, bil_apply_of_mem_omegaMinus hgOm tv v, bil_comm tv v, ← lam_eq_bil v, hlam]
  rw [hbil0] at hbil1
  exact one_ne_zero hbil1.symm

theorem conj_t_sq (h : Setting25 G t z z₁ ι zv R0 F) : (n * t * n⁻¹) ^ 2 = 1 := by
  have ht2 : t ^ 2 = 1 := by
    rw [pow_two, ← h.ι_tv, ← coordElt_add, add_self_eq_zero_V6, coordElt_zero]
  have hconj : (n * t * n⁻¹) ^ 2 = n * t ^ 2 * n⁻¹ := by
    change ((MulAut.conj n) t) ^ 2 = n * t ^ 2 * n⁻¹
    rw [← map_pow, MulAut.conj_apply]
  rw [hconj, ht2]
  group

theorem conj_t_comm_Fconj (h : Setting25 G t z z₁ ι zv R0 F) {f : G} (hf : f ∈ Fconj n F) :
    (n * t * n⁻¹) * f = f * (n * t * n⁻¹) := by
  rw [mem_Fconj] at hf
  obtain ⟨f₀, hf₀, hff⟩ := hf
  have hft : f₀ * t = t * f₀ :=
    Subgroup.mem_centralizer_singleton_iff.mp (h.hD2.F_le hf₀).1
  rw [← hff]
  calc (n * t * n⁻¹) * (n * f₀ * n⁻¹) = n * (t * f₀) * n⁻¹ := by group
    _ = n * (f₀ * t) * n⁻¹ := by rw [hft]
    _ = (n * f₀ * n⁻¹) * (n * t * n⁻¹) := by group

end CFSG.EvenSporadicStandard.HNRecog.Harada
