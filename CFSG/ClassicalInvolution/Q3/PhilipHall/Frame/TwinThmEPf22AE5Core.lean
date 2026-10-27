module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThmEWAe5Exit
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDiscExitUAE5Lab
public import CFSG.ClassicalInvolution.Q3.TL3T61

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.TC.Thin

namespace TwinThmEW

namespace Ae5Q8

open CFSG.ClassicalInvolution.Q3.AE Wr
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThmE.Ae5Model
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThmEW.Ae5Mod

theorem exists_even_perm_pair : ∀ m q a b : Fin 5, m ≠ q → a ≠ b →
    ∃ σ : Equiv.Perm (Fin 5), Equiv.Perm.sign σ = 1 ∧ σ m = a ∧ σ q = b := by
  decide +kernel

theorem ite_miss_add : ∀ a b y : Fin 5, a ≠ b →
    ((if y ∈ miss a then (1 : ZMod 2) else 0) + (if y ∈ miss b then 1 else 0) =
      if (y = a ∨ y = b) then 1 else 0) := by
  decide +kernel

theorem zBar_mul_eq_embed_w0 (ι' : Fin 4 ↪ Fin 5) :
    zBar (miss (ι' 0)) (card_miss _) * zBar (miss (ι' 1)) (card_miss _) =
      mkQ 5 (embed ι' w0) := by
  unfold zBar
  rw [← map_mul]
  congr 1
  have hne : ι' 0 ≠ ι' 1 := fun h => absurd (ι'.injective h) (by decide)
  refine Wr.ext (funext fun y => ?_) ?_
  · rw [mul_vec, zOf_perm]
    show (zOf (emb (miss (ι' 0)) (card_miss _))).vec y +
        (zOf (emb (miss (ι' 1)) (card_miss _))).vec ((1 : Equiv.Perm (Fin 5)).symm y) =
      (embed ι' w0).vec y
    have e1 : (1 : Equiv.Perm (Fin 5)).symm y = y := rfl
    have hr : ∀ a : Fin 5, y ∈ Set.range (emb (miss a) (card_miss a)) ↔ y ∈ miss a := by
      intro a
      rw [range_emb]
      exact Finset.mem_coe
    rw [e1]
    simp only [zOf_vec_apply, hr]
    have h2 := ite_miss_add (ι' 0) (ι' 1) y hne
    have h3 : (embed ι' w0).vec y = if (y = ι' 0 ∨ y = ι' 1) then 1 else 0 := by
      by_cases h : y = ι' 0 ∨ y = ι' 1
      · rw [if_pos h]; exact (embed_w0_vec_eq_one_iff ι' y).mpr h
      · rw [if_neg h]
        have : (embed ι' w0).vec y ≠ 1 := fun h1 => h ((embed_w0_vec_eq_one_iff ι' y).mp h1)
        generalize (embed ι' w0).vec y = r at this ⊢
        revert r; decide
    rw [h3, ← h2]
  · rw [mul_perm, zOf_perm, zOf_perm, embed_perm]
    have : w0.perm = 1 := rfl
    rw [this, embedPerm_one]
    rfl

theorem exists_conj_zBar_prod {m q : Fin 5} (hmq : m ≠ q) (ι' : Fin 4 ↪ Fin 5) :
    ∃ g ∈ aeSub 5, mkQ 5 g * (zBar (miss m) (card_miss m) * zBar (miss q) (card_miss q)) *
      (mkQ 5 g)⁻¹ = mkQ 5 (embed ι' w0) := by
  have hne : ι' 0 ≠ ι' 1 := fun h => absurd (ι'.injective h) (by decide)
  obtain ⟨σ, hsgn, hσm, hσq⟩ := exists_even_perm_pair m q (ι' 0) (ι' 1) hmq hne
  refine ⟨ofPerm σ, ⟨?_, hsgn⟩, ?_⟩
  · unfold wsum
    simp [ofPerm]
  · have h1 := zBar_conj_miss (ofPerm σ) m
    have h2 := zBar_conj_miss (ofPerm σ) q
    have e : (ofPerm σ).perm = σ := rfl
    rw [e, hσm] at h1
    rw [e, hσq] at h2
    calc mkQ 5 (ofPerm σ) * (zBar (miss m) (card_miss m) * zBar (miss q) (card_miss q)) *
          (mkQ 5 (ofPerm σ))⁻¹ =
        (mkQ 5 (ofPerm σ) * zBar (miss m) (card_miss m) * (mkQ 5 (ofPerm σ))⁻¹) *
          (mkQ 5 (ofPerm σ) * zBar (miss q) (card_miss q) * (mkQ 5 (ofPerm σ))⁻¹) := by group
      _ = _ := by rw [h1, h2, zBar_mul_eq_embed_w0]

section Core

variable {X : Type} [Group X] [Finite X] {Φ : Set (Subgroup X)}

theorem ae5_ker_bot (hS : TwinDisc.Q8Section X Φ) (I : AEIdent Φ 5)
    {K K' : Subgroup X} (hK : K ∈ Φ) (hK' : K' ∈ Φ) (hne : K' ≠ K) {z : X}
    (hzK : IsUniqueInvolution K z) (hzK' : IsUniqueInvolution K' z) : I.φ.ker = ⊥ := by
  have hn5 : 5 ≤ 5 := le_refl 5
  have hk := TwinDisc.AE5.ker_pGroupN hS I
  have h2 := TwinDisc.AE5.members_twoN hn5 hS I
  have h8 := TwinDisc.AE5.members_card8 hn5 hS I
  have hgenΦ : pSpan Φ = ⊤ := TwinDisc.AE5.hgen_of hS
  have hinj : ∀ L ∈ Φ, ∀ L' ∈ Φ,
      (L.subgroupOf (pSpan Φ)).map I.φ = (L'.subgroupOf (pSpan Φ)).map I.φ → L = L' :=
    fun L hL L' hL' h => TwinDisc.AE5.same_of_image_n hn5 hS I hL hL' h
  have hconj : ∀ L ∈ Φ, ∀ x ∈ pSpan Φ, conjSub x L ∈ Φ :=
    fun L hL x _ => hS.hyp.conjInvariant x L hL
  have htrans : ∀ L ∈ Φ, ∀ L' ∈ Φ, ∃ x ∈ pSpan Φ, conjSub x L = L' := by
    intro L hL L' hL'
    obtain ⟨g, hg⟩ := TwinDisc.AE5.trans_of_aeIdent hn5 hS I L hL L' hL'
    exact ⟨g, by rw [hgenΦ]; exact Subgroup.mem_top g, hg⟩
  obtain ⟨δ, hδ, c, hlab⟩ := I.label K hK
  obtain ⟨γ, hγ, c', hlab'⟩ := I.label K' hK'
  have e1 := I.map_eq_zBar hn5 hK (h8 K hK) hlab hzK
  have e2 := I.map_eq_zBar hn5 hK' (h8 K' hK') hlab' hzK'
  have hγδ : γ = δ := AE.eq_of_zBar_eq (by norm_num) (e2.symm.trans e1)
  subst hγδ
  have hc' : c' = !c := by
    by_contra hcc
    have : c' = c := by cases c <;> cases c' <;> simp_all
    subst this
    exact hne (hinj K' hK' K hK (hlab'.trans hlab.symm))
  subst hc'
  have hz₀ : ∀ u u' : X, IsUniqueInvolution K u → IsUniqueInvolution K' u' → u = u' := by
    intro u u' hu hu'
    rw [hu.eq hzK, hu'.eq hzK']
  have hH : TL4.AECoverHyp I :=
    { ker_two := hk
      card := h8
      conj_mem := hconj
      label_inj := hinj
      twin_comm := by
        intro α h L hL L' hL' hl hl'
        refine aeIdent_comm_of_map_comm hS.hyp h2 (subset_refl Φ) I hk hL hL' ?_ ?_
        · intro e
          subst e
          rw [hl] at hl'
          exact AE.memBar_true_ne_false hn5 α h hl'
        · rw [hl, hl']
          exact memBar_twin_comm α h true
      twin_z := I.twin_z_of_trans hn5 (by norm_num) hconj hinj htrans hK hK' hlab hlab' hz₀ }
  exact TL4.aeCoverOddKer_proved X Φ 5 I hn5 (by decide) hH

theorem ae5_core (hS : TwinDisc.Q8Section X Φ) (I : AEIdent Φ 5)
    {K K' : Subgroup X} (hK : K ∈ Φ) (hK' : K' ∈ Φ) (hne : K' ≠ K) {z : X}
    (hzK : IsUniqueInvolution K z) (hzK' : IsUniqueInvolution K' z)
    {J : Subgroup X} (hJ : J ∈ Φ) {t : X} (htJ : IsUniqueInvolution J t) (hzt : z * t ≠ 1)
    (P : Sylow 2 X) :
    ∃ s ∈ (P : Subgroup X), conjSub s K = K' ∧
      ∀ x₀ ∈ K, x₀ * x₀ = z → ∃ g : X, g * (z * t) * g⁻¹ = x₀ * (s * x₀ * s⁻¹) := by
  classical
  have hn5 : 5 ≤ 5 := le_refl 5
  have hker := ae5_ker_bot hS I hK hK' hne hzK hzK'
  have F := TwinDisc.AE5.q8Fam_of_aeIdent_n hn5 hS I
  set ψ : X →* AE.AEQ 5 := psiOfF F I with hψdef
  have hinjφ : Function.Injective I.φ := (MonoidHom.ker_eq_bot_iff _).mp hker
  have hψinj : Function.Injective ψ := fun a b hab => congrArg Subtype.val (hinjφ hab)
  obtain ⟨m, b, hKl⟩ := psi_label F I hK
  obtain ⟨m', b', hK'l⟩ := psi_label F I hK'
  have hψz : ψ z = AE.zBar (miss m) (card_miss m) := psi_zimg F I hK hKl hzK
  have hψz' : ψ z = AE.zBar (miss m') (card_miss m') := psi_zimg F I hK' hK'l hzK'
  obtain rfl : m = m' :=
    (miss_inj (AE.eq_of_zBar_eq (by norm_num) (hψz'.symm.trans hψz))).symm
  have hzne : ψ z ≠ 1 := by rw [hψz]; exact AE.zBar_ne_one (le_refl 5) _ _
  have hbb : b ≠ b' := by
    intro h
    subst h
    exact hne (psi_inj F I hK' hK (by rw [hKl, hK'l]))
  have hb' : b' = !b := by cases b <;> cases b' <;> simp_all
  set ι := AE.emb (miss m) (card_miss m) with hι
  have hιrange : Set.range ι = ↑(miss m) := AE.range_emb _ _
  have hmι : m ∉ Set.range ι := by
    rw [hιrange]; simp [miss]
  set e := AE.twinVec ι m with he
  have he_ae : e ∈ AE.aeSub 5 := (AE.twinVec_mem ι hmι ⊤).1
  have he_ev : e ∈ evenVec 5 := mem_evenVec.mpr ⟨rfl, he_ae.1⟩
  have heR : AE.mkQ 5 e ∈ ψ.range := by
    have hmem : AE.mkQ 5 e ∈ I.φ.range := by
      rw [I.range_eq]; exact ⟨e, he_ae, rfl⟩
    obtain ⟨⟨y, hy⟩, hy'⟩ := hmem
    exact ⟨y, hy'⟩
  obtain ⟨s, hsP, hsψ⟩ := exists_mem_sylow_evenVec ψ P he_ev heR
  have hKs : conjSub s K = K' := by
    have hKsΩ : conjSub s K ∈ Φ := hS.hyp.conjInvariant s K hK
    refine psi_inj F I hKsΩ hK' ?_
    have h1 : (conjSub s K).map ψ = (K.map ψ).map (MulAut.conj (ψ s)).toMonoidHom := by
      show (K.map (MulAut.conj s).toMonoidHom).map ψ = _
      rw [Subgroup.map_map, Subgroup.map_map]
      congr 1
      refine MonoidHom.ext fun x => ?_
      simp [MulAut.conj_apply]
    rw [h1, hKl, hsψ, map_conj_memBar_not ι hmι (miss m) (card_miss m) hι b, hK'l, hb']
  refine ⟨s, hsP, hKs, ?_⟩
  intro x₀ hx₀K hx₀sq
  obtain ⟨k, hkmem, hkψ⟩ : ∃ k ∈ AE.kList ++ AE.kStarList, ψ x₀ = AE.mkQ 5 (AE.embed ι k) := by
    have hx₀m : ψ x₀ ∈ K.map ψ := ⟨x₀, hx₀K, rfl⟩
    rw [hKl] at hx₀m
    obtain ⟨kh, hkh, hkhψ⟩ := hx₀m
    cases b
    · obtain ⟨k, hk, rfl⟩ : kh ∈ AE.memKStar ι := hkh
      exact ⟨k, List.mem_append_right _ hk, hkhψ.symm⟩
    · obtain ⟨k, hk, rfl⟩ : kh ∈ AE.memK ι := hkh
      exact ⟨k, List.mem_append_left _ hk, hkhψ.symm⟩
  have hzbar2 : AE.zBar (miss m) (card_miss m) * AE.zBar (miss m) (card_miss m) = 1 :=
    AE.zBar_mul_self _ _
  have hψsq : ψ x₀ * ψ x₀ = ψ z := by rw [← map_mul, hx₀sq]
  have hk1 : k ≠ 1 := by
    rintro rfl
    apply hzne
    rw [← hψsq, hkψ, map_one, map_one, one_mul]
  have hkz : k ≠ AE.zQ := by
    rintro rfl
    apply hzne
    rw [← hψsq, hkψ]
    have : AE.mkQ 5 (AE.embed ι AE.zQ) = AE.zBar (miss m) (card_miss m) := rfl
    rw [this]
    exact hzbar2
  set y₀ : X := s * x₀ * s⁻¹ with hy₀
  have hψy₀ : ψ y₀ = AE.mkQ 5 (AE.embed ι (e0 * k * e0)) := by
    have hinv : e⁻¹ = e := inv_eq_of_mul_eq_one_right (AE.twinVec_mul_self ι m)
    rw [hy₀, map_mul, map_mul, map_inv, hsψ, hkψ, ← map_inv, hinv, ← map_mul, ← map_mul]
    congr 1
    exact AE.twinVec_conj_embed ι hmι k
  obtain ⟨hperm, π, hπ⟩ := e0Prod k hkmem hk1 hkz
  have hψa : ψ (x₀ * y₀) = AE.mkQ 5 (AE.embed (permEmb ι π) w0) := by
    rw [embed_eq_embed_permEmb ι π _ hperm hπ, map_mul, hkψ, hψy₀, ← map_mul, ← map_mul]
  obtain ⟨q, c, hJl⟩ := psi_label F I hJ
  have hψt : ψ t = AE.zBar (miss q) (card_miss q) := psi_zimg F I hJ hJl htJ
  have hmq : m ≠ q := by
    intro h
    subst h
    apply hzt
    apply hψinj
    rw [map_mul, hψz, hψt, map_one]
    exact hzbar2
  obtain ⟨g', hg'ae, hg'⟩ := exists_conj_zBar_prod hmq (permEmb ι π)
  have hg'R : AE.mkQ 5 g' ∈ ψ.range := by
    have hmem : AE.mkQ 5 g' ∈ I.φ.range := by
      rw [I.range_eq]; exact ⟨g', hg'ae, rfl⟩
    obtain ⟨⟨y, hy⟩, hy'⟩ := hmem
    exact ⟨y, hy'⟩
  obtain ⟨g, hg⟩ := hg'R
  refine ⟨g, hψinj ?_⟩
  rw [map_mul, map_mul, map_inv, hg, map_mul, hψz, hψt, hg', hψa]

end Core

end Ae5Q8

end TwinThmEW

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
