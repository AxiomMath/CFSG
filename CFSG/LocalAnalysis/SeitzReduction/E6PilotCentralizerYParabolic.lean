module

public import CFSG.LocalAnalysis.SeitzReduction.E6PilotCentralizerYParabolicBasic

public section

namespace CFSG.SeitzReduction.E6Pilot

open Subgroup CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Steinberg.Adjoint

local instance e6CentralizerYParabolicNeZeroRank : NeZero Tag.E6.rank := ⟨by decide⟩

theorem list_prod_map_eq_filter_mul {G ι : Type*} [Group G] (f : ι → G) (p : ι → Bool) :
    ∀ L : List ι, (∀ a ∈ L, ∀ b ∈ L, Commute (f a) (f b)) →
      (L.map f).prod = ((L.filter p).map f).prod * ((L.filter (fun a => !p a)).map f).prod
  | [], _ => by simp
  | a :: L, hc => by
    have hc' : ∀ x ∈ L, ∀ y ∈ L, Commute (f x) (f y) := fun x hx y hy =>
      hc x (List.mem_cons_of_mem _ hx) y (List.mem_cons_of_mem _ hy)
    have ih := list_prod_map_eq_filter_mul f p L hc'
    by_cases hp : p a = true
    · simp only [List.filter_cons, hp, ↓reduceIte, Bool.not_true, List.map_cons,
        List.prod_cons, ih, mul_assoc]
      simp
    · have hp' : p a = false := by simpa using hp
      have hcomm : Commute (f a) ((L.filter p).map f).prod :=
        Commute.list_prod_right _ _ fun x hx => by
          obtain ⟨b, hb, rfl⟩ := List.mem_map.1 hx
          exact hc a List.mem_cons_self b (List.mem_cons_of_mem _ (List.mem_of_mem_filter hb))
      simp only [List.filter_cons, hp', Bool.not_false, Bool.false_eq_true, ↓reduceIte,
        List.map_cons, List.prod_cons, ih]
      rw [← mul_assoc, hcomm.eq, mul_assoc]

theorem yLevel_check :
    (∀ i : Fin Tag.E6.rank, ¬(i ≠ 0 ∧ i ≠ 5) → iform (Pi.single i 1) yLamAS = 1) ∧
    (∀ i : Fin Tag.E6.rank, (i ≠ 0 ∧ i ≠ 5) → reflect .E6 i yLamAS = yLamAS) ∧
    (∀ γ ∈ rootFinset .E6, height γ < 0 → iform γ yLamAS ≤ 0) ∧
    yLamAS = yAlphaAS + yBetaAS ∧ iform yAlphaAS yBetaAS = 0 := by
  decide +kernel


theorem mem_parabolicWeylGroup_nodes16_of_smul :
    ∀ (n : ℕ) (w : WeylGroup .E6), (coxeterSystem .E6).length w = n → w • yLamAS = yLamAS →
      w ∈ parabolicWeylGroup .E6 nodes16 := by
  intro n
  induction n with
  | zero =>
    intro w hw _
    rw [CoxeterSystem.length_eq_zero_iff] at hw
    subst hw
    exact one_mem _
  | succ n ih =>
    intro w hw hfix
    have hw1 : w ≠ 1 := fun h => by
      rw [h, CoxeterSystem.length_one] at hw
      omega
    obtain ⟨i, hroot, hneg⟩ := (weyl_exchange_condition .E6).2.2.2 w hw1
    have hiJ : i ∈ nodes16 := by
      by_contra hi
      have h1 : iform (w • (Pi.single i 1 : Fin Tag.E6.rank → ℤ)) yLamAS = 1 := by
        rw [← hfix, iform_smul]
        exact yLevel_check.1 i hi
      have h2 := yLevel_check.2.2.1 _ (mem_rootFinset.2 hroot) hneg
      omega
    have hlen : (coxeterSystem .E6).length (w * simple .E6 i) = n := by
      have := ((weyl_exchange_condition .E6).2.1 w i).1.2 ⟨hroot, hneg⟩
      omega
    have hsi : simple .E6 i ∈ parabolicWeylGroup .E6 nodes16 :=
      Subgroup.subset_closure ⟨i, hiJ, rfl⟩
    have hfix' : (w * simple .E6 i) • yLamAS = yLamAS := by
      rw [mul_smul, simple_smul, yLevel_check.2.1 i hiJ, hfix]
    have hmem := ih _ hlen hfix'
    have e : w = w * simple .E6 i * simple .E6 i := by
      rw [mul_assoc, CoxeterSystem.simple_mul_simple_self, mul_one]
    rw [e]
    exact mul_mem hmem hsi

section Weyl

variable {K : Type} [Field K]


theorem yU5_closed {S : Set (Fin Tag.E6.rank → ℤ)} (hS : S ⊆ {ζ | ζ ∈ yU5}) :
    ∀ ζ ∈ S, ∀ ζ' ∈ S, ∀ a b : ℕ, 1 ≤ a → 1 ≤ b → IsRoot .E6 (a • ζ + b • ζ') →
      a • ζ + b • ζ' ∈ S := by
  intro ζ hζ ζ' hζ' a b ha hb hr
  exfalso
  have h1 := (yU5_check.1 ζ (hS hζ)).2.2
  have h2 := (yU5_check.1 ζ' (hS hζ')).2.2
  have h3 := yU5_check.2.2.2.2.2 _ (mem_rootFinset.2 hr)
  rw [iform_add_left, ← natCast_zsmul, ← natCast_zsmul, iform_smul_left, iform_smul_left, h1,
    h2] at h3
  omega

theorem commute_pinnedX_smul_yU5 [CharP K 2] (w : WeylGroup .E6) (c : (Fin Tag.E6.rank → ℤ) → K) :
    ∀ a ∈ yU5, ∀ b ∈ yU5,
      Commute (pinnedX .E6 K (w • a) (c a)) (pinnedX .E6 K (w • b) (c b)) := by
  intro a ha b hb
  have hra := mem_rootFinset.1 (yU5_check.1 a ha).1
  have hrb := mem_rootFinset.1 (yU5_check.1 b hb).1
  have h := (classD4_commute_pinnedX (R := K) e6_simplyLaced hra hrb
    (yU5_check.2.2.1 a ha b hb) (c a) (c b)).map
      (MulAut.conj (canonicalRep (coxeterSystem .E6) K w))
  simp only [MulAut.conj_apply] at h
  rwa [canonicalRep_mul_pinnedX_mul_inv_of_charTwo w hra,
    canonicalRep_mul_pinnedX_mul_inv_of_charTwo w hrb] at h

theorem smul_mem_yU5_of_conj [CharP K 2] (w : WeylGroup .E6) (c : (Fin Tag.E6.rank → ℤ) → K)
    (hα : c yAlphaAS ≠ 0) (hβ : c yBetaAS ≠ 0)
    (h : canonicalRep (coxeterSystem .E6) K w * (yU5.map fun ζ => pinnedX .E6 K ζ (c ζ)).prod *
      (canonicalRep (coxeterSystem .E6) K w)⁻¹ ∈ rootSpan .E6 K {ζ | ζ ∈ yU5}) :
    w • yAlphaAS ∈ yU5 ∧ w • yBetaAS ∈ yU5 := by
  set n := canonicalRep (coxeterSystem .E6) K w with hn
  set f : (Fin Tag.E6.rank → ℤ) → ModGL .E6 K := fun ζ => pinnedX .E6 K (w • ζ) (c ζ) with hf
  have hroots : ∀ ζ ∈ yU5, IsRoot .E6 ζ := fun ζ hζ => mem_rootFinset.1 (yU5_check.1 ζ hζ).1
  have hpos : ∀ ζ ∈ yU5, IsRoot .E6 ζ ∧ 0 < height ζ := fun ζ hζ =>
    ⟨hroots ζ hζ, (yU5_check.1 ζ hζ).2.1⟩
  have hX := canonicalRep_mul_list_prod_mul_inv_of_charTwo w hroots c
  rw [hX] at h
  have hU5pos : rootSpan .E6 K {ζ | ζ ∈ yU5} ≤ posUnipotent .E6 K :=
    rootSpan_mono (fun ζ hζ => hpos ζ hζ)
  have hα5 : yAlphaAS ∈ yU5 := by simp [yU5]
  have hβ5 : yBetaAS ∈ yU5 := by simp [yU5]
  set p : (Fin Tag.E6.rank → ℤ) → Bool := fun ζ => decide (0 < height (w • ζ)) with hp
  have hsplit := list_prod_map_eq_filter_mul f p yU5 (commute_pinnedX_smul_yU5 w c)
  set P := ((yU5.filter p).map f).prod with hP
  set N := ((yU5.filter fun ζ => !p ζ).map f).prod with hN
  have hPpos : P ∈ posUnipotent .E6 K := list_prod_mem fun x hx => by
    obtain ⟨ζ, hζ, rfl⟩ := List.mem_map.1 hx
    obtain ⟨hζ5, hζp⟩ := List.mem_filter.1 hζ
    exact pinnedX_mem_rootSpan (S := {α | IsRoot .E6 α ∧ 0 < height α})
      ⟨IsRoot.smul (hroots ζ hζ5) w, by simpa [hp] using hζp⟩ _
  have hNneg : N ∈ negUnipotent .E6 K := list_prod_mem fun x hx => by
    obtain ⟨ζ, hζ, rfl⟩ := List.mem_map.1 hx
    obtain ⟨hζ5, hζp⟩ := List.mem_filter.1 hζ
    have hr := IsRoot.smul (hroots ζ hζ5) w
    have h0 : ¬ 0 < height (w • ζ) := by simpa [hp] using hζp
    exact pinnedX_mem_rootSpan (S := {α | IsRoot .E6 α ∧ height α < 0})
      ⟨hr, by have := hr.height_ne_zero; omega⟩ _
  have hN1 : N = 1 := by
    have hNP : N = P⁻¹ * (yU5.map f).prod := by rw [hsplit]; group
    have hNB : N ∈ borelGroup .E6 K ⊓ negUnipotent .E6 K :=
      mem_inf.2 ⟨mem_sup_right (hNP ▸ mul_mem (inv_mem hPpos) (hU5pos h)), hNneg⟩
    rwa [borelGroup_inf_negUnipotent, mem_bot] at hNB
  have hneg0 : ∀ ζ ∈ yU5.filter (fun ζ => !p ζ), c ζ = 0 := by
    have hsub : ∀ ζ ∈ yU5.filter (fun ζ => !p ζ), IsRoot .E6 ζ ∧ 0 < height ζ := fun ζ hζ =>
      hpos ζ (List.mem_filter.1 hζ).1
    have hN' := canonicalRep_mul_list_prod_mul_inv_of_charTwo w (fun ζ hζ => (hsub ζ hζ).1) c
    rw [← hn, ← hN, hN1, mul_inv_eq_one, mul_eq_left] at hN'
    refine pinnedX_list_prod_injective (R := K) _ ((yU5_check.2.1).filter _) hsub c
      (fun _ => 0) ?_
    rw [hN']
    simp only [pinnedX_zero, List.map_const', List.prod_replicate, one_pow]
  have hpα : p yAlphaAS = true := by
    by_contra hc
    exact hα (hneg0 _ (List.mem_filter.2 ⟨hα5, by simpa using hc⟩))
  have hpβ : p yBetaAS = true := by
    by_contra hc
    exact hβ (hneg0 _ (List.mem_filter.2 ⟨hβ5, by simpa using hc⟩))
  have hPeq : P = (yU5.map f).prod := by rw [hsplit, hN1, mul_one]
  set L1 := yU5.filter p with hL1
  set q : (Fin Tag.E6.rank → ℤ) → Bool := fun ζ => decide (w • ζ ∈ yU5) with hq
  have hL1sub : ∀ ζ ∈ L1, ζ ∈ yU5 := fun ζ hζ => (List.mem_filter.1 hζ).1
  have hsplit' := list_prod_map_eq_filter_mul f q L1 (fun a ha b hb =>
    commute_pinnedX_smul_yU5 w c a (hL1sub a ha) b (hL1sub b hb))
  set Pin := ((L1.filter q).map f).prod with hPin
  set Pout := ((L1.filter fun ζ => !q ζ).map f).prod with hPout
  have hPin : Pin ∈ rootSpan .E6 K {ζ | ζ ∈ yU5} := list_prod_mem fun x hx => by
    obtain ⟨ζ, hζ, rfl⟩ := List.mem_map.1 hx
    exact pinnedX_mem_rootSpan (S := {ζ | ζ ∈ yU5}) (by simpa [hq] using (List.mem_filter.1 hζ).2) _
  have hPout : Pout ∈ rootSpan .E6 K {ζ | ζ ∈ yU5} := by
    have e : Pout = Pin⁻¹ * (yU5.map f).prod := by rw [← hPeq, hP, hsplit']; group
    rw [e]
    exact mul_mem (inv_mem hPin) h
  set l := (L1.filter fun ζ => !q ζ).map (w • ·) with hl
  have hl0 := eq_zero_of_list_prod_mem_rootSpan_annih (K := K) (T := {ζ | ζ ∈ yU5})
    (fun ζ hζ => hpos ζ hζ) (yU5_closed le_rfl) (l := l)
    ((((yU5_check.2.1).filter _).filter _).map (MulAction.injective w))
    (fun γ hγ => by
      obtain ⟨ζ, hζ, rfl⟩ := List.mem_map.1 hγ
      have hζ1 := (List.mem_filter.1 hζ).1
      exact ⟨IsRoot.smul (hroots ζ (hL1sub ζ hζ1)) w,
        by simpa [hp] using (List.mem_filter.1 hζ1).2⟩)
    (fun γ hγ => by
      obtain ⟨ζ, hζ, rfl⟩ := List.mem_map.1 hγ
      simpa [hq] using (List.mem_filter.1 hζ).2)
    (fun γ => c (w⁻¹ • γ)) (by
      rw [hl, List.map_map]
      have e : ((fun γ => pinnedX .E6 K γ (c (w⁻¹ • γ))) ∘ (w • ·)) = f := by
        funext ζ
        simp [hf]
      rw [e]
      exact hPout)
  have hout : ∀ ζ ∈ L1.filter (fun ζ => !q ζ), c ζ = 0 := fun ζ hζ => by
    have := hl0 (w • ζ) (List.mem_map.2 ⟨ζ, hζ, rfl⟩)
    simpa using this
  have hqα : q yAlphaAS = true := by
    by_contra hc
    exact hα (hout _ (List.mem_filter.2 ⟨List.mem_filter.2 ⟨hα5, hpα⟩, by simpa using hc⟩))
  have hqβ : q yBetaAS = true := by
    by_contra hc
    exact hβ (hout _ (List.mem_filter.2 ⟨List.mem_filter.2 ⟨hβ5, hpβ⟩, by simpa using hc⟩))
  exact ⟨by simpa [hq] using hqα, by simpa [hq] using hqβ⟩

theorem smul_yLamAS_of_mem_yU5 {w : WeylGroup .E6} (hα : w • yAlphaAS ∈ yU5)
    (hβ : w • yBetaAS ∈ yU5) : w • yLamAS = yLamAS := by
  have h0 : iform (w • yAlphaAS) (w • yBetaAS) = 0 := by
    rw [iform_smul]; exact yLevel_check.2.2.2.2
  rw [yLevel_check.2.2.2.1, smul_add]
  rcases yU5_check.2.2.2.2.1 _ hα _ hβ h0 with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · rw [h1, h2]
  · rw [h1, h2, add_comm]

end Weyl

theorem yRadicalAS_check :
    ∀ γ ∈ rootFinset .E6, 0 < iform γ yLamAS →
      0 ≤ iform γ yAlphaAS ∧ 0 ≤ iform γ yBetaAS := by
  decide +kernel

section Main

variable {K : Type} [Field K]


theorem mem_parabolicSubgroup_nodes16_of_commute [CharP K 2] {g : ModGL .E6 K}
    (hg : g ∈ adjointGroup .E6 K)
    (hc : g * (e6ASRep K 1 : ModGL .E6 K) = (e6ASRep K 1 : ModGL .E6 K) * g) :
    g ∈ parabolicSubgroup .E6 K nodes16 := by
  have hg' : g ∈ ⋃ w, bruhatCell .E6 K w := by
    rw [← adjointGroup_eq_iUnion_bruhatCell]
    exact hg
  obtain ⟨w, hw⟩ := Set.mem_iUnion.1 hg'
  have hw' := hw
  obtain ⟨b, hb, b', hb', rfl⟩ := mem_bruhatCell.1 hw'
  set n := canonicalRep (coxeterSystem .E6) K w with hn
  set y := (e6ASRep K 1 : ModGL .E6 K) with hy
  obtain ⟨l', m', hl', hm', h', hh', e'⟩ := exists_conj_e6ASRep_one_of_mem_borelGroup hb'
  obtain ⟨l, m, -, -, h, hh, e⟩ := exists_conj_e6ASRep_one_of_mem_borelGroup (inv_mem hb)
  have hnd5 := yU5_check.2.1
  have hndH : yHigh.Nodup := (List.nodup_cons.1 (List.nodup_cons.1 hnd5).2).2
  have hαH : yAlphaAS ∉ yHigh := fun hm =>
    (List.nodup_cons.1 hnd5).1 (List.mem_cons_of_mem _ hm)
  have hβH : yBetaAS ∉ yHigh := (List.nodup_cons.1 (List.nodup_cons.1 hnd5).2).1
  have hαβ : yAlphaAS ≠ yBetaAS := fun he =>
    (List.nodup_cons.1 hnd5).1 (he ▸ List.mem_cons_self)
  obtain ⟨-, hsurj, -⟩ := CFSG.LieType.Ree.list_prod_pinnedX_bijective (K := K)
    (S := {ζ | ζ ∈ yHigh})
    (fun ζ hζ => ⟨mem_rootFinset.1 (yU5_check.1 ζ (mem_yU5_of_mem_yHigh hζ)).1,
      (yU5_check.1 ζ (mem_yU5_of_mem_yHigh hζ)).2.1⟩)
    (yU5_closed fun ζ hζ => mem_yU5_of_mem_yHigh hζ) hndH rfl
  obtain ⟨d, hd⟩ := hsurj h' hh'
  set c : (Fin Tag.E6.rank → ℤ) → K := fun ζ =>
    if ζ = yAlphaAS then l' else if ζ = yBetaAS then m' else d ζ with hcdef
  have hcα : c yAlphaAS = l' := by simp [hcdef]
  have hcβ : c yBetaAS = m' := by simp [hcdef, Ne.symm hαβ]
  have hcH : (yHigh.map fun ζ => pinnedX .E6 K ζ (c ζ)) = yHigh.map fun ζ => pinnedX .E6 K ζ (d ζ) :=
    List.map_congr_left fun ζ hζ => by
      have h1 : ζ ≠ yAlphaAS := fun he => hαH (he ▸ hζ)
      have h2 : ζ ≠ yBetaAS := fun he => hβH (he ▸ hζ)
      simp [hcdef, h1, h2]
  have hcprod : (yU5.map fun ζ => pinnedX .E6 K ζ (c ζ)).prod = b' * y * b'⁻¹ := by
    rw [e']
    simp only [yU5, List.map_cons, List.prod_cons, hcα, hcβ]
    rw [hcH, hd, mul_assoc]
  have hkey : n * (b' * y * b'⁻¹) * n⁻¹ = b⁻¹ * y * b⁻¹⁻¹ := by
    have h1 : b * n * b' * y * (b * n * b')⁻¹ = y := by rw [hc]; group
    calc n * (b' * y * b'⁻¹) * n⁻¹ = b⁻¹ * (b * n * b' * y * (b * n * b')⁻¹) * b := by group
      _ = b⁻¹ * y * b⁻¹⁻¹ := by rw [h1]; group
  have hU5 : ∀ {ζ}, ζ ∈ yU5 → ∀ x : K, pinnedX .E6 K ζ x ∈ rootSpan .E6 K {ζ | ζ ∈ yU5} :=
    fun hζ x => pinnedX_mem_rootSpan (S := {ζ | ζ ∈ yU5}) hζ x
  have hmem : b⁻¹ * y * b⁻¹⁻¹ ∈ rootSpan .E6 K {ζ | ζ ∈ yU5} := by
    rw [e]
    refine mul_mem (mul_mem (hU5 (by simp [yU5]) l) (hU5 (by simp [yU5]) m)) ?_
    exact rootSpan_mono (fun ζ hζ => mem_yU5_of_mem_yHigh hζ) hh
  obtain ⟨hwα, hwβ⟩ := smul_mem_yU5_of_conj w c (by rw [hcα]; exact hl') (by rw [hcβ]; exact hm')
    (by rw [hcprod, ← hn, hkey]; exact hmem)
  have hwJ := mem_parabolicWeylGroup_nodes16_of_smul _ w rfl (smul_yLamAS_of_mem_yU5 hwα hwβ)
  have hmemP : b * n * b' ∈ (parabolicSubgroup .E6 K nodes16 : Set (ModGL .E6 K)) := by
    rw [(standard_parabolic_cells .E6 K).1 nodes16]
    exact Set.mem_biUnion hwJ hw
  exact hmemP

theorem parabolicRadical_nodes16_le_centralizer :
    parabolicRadical .E6 K nodes16 ≤
      centralizer ({(e6ASRep K 1 : ModGL .E6 K)} : Set (ModGL .E6 K)) := by
  rw [parabolicRadical, parabolicRadicalRoots_nodes16]
  refine iSup₂_le fun γ hγ => (closure_le _).2 ?_
  rintro _ ⟨x, rfl⟩
  rw [SetLike.mem_coe, mem_centralizer_singleton_iff, coe_e6ASRep_one_eq]
  obtain ⟨h1, h2⟩ := yRadicalAS_check γ (mem_rootFinset.2 hγ.1) hγ.2
  have hα := mem_rootFinset.1 (yU5_check.1 yAlphaAS (by simp [yU5])).1
  have hβ := mem_rootFinset.1 (yU5_check.1 yBetaAS (by simp [yU5])).1
  exact ((classD4_commute_pinnedX e6_simplyLaced hγ.1 hα h1 x 1).mul_right
    (classD4_commute_pinnedX e6_simplyLaced hγ.1 hβ h2 x 1)).eq

theorem centralizer_e6ASRep_one_le [CharP K 2] :
    centralizer ({(e6ASRep K 1 : ModGL .E6 K)} : Set (ModGL .E6 K)) ⊓ adjointGroup .E6 K ≤
      parabolicRadical .E6 K nodes16 ⊔ (parabolicLevi .E6 K nodes16 ⊓
        centralizer ({(e6ASRep K 1 : ModGL .E6 K)} : Set (ModGL .E6 K))) := by
  intro g hg
  obtain ⟨hgC, hgG⟩ := mem_inf.1 hg
  have hgc : g * (e6ASRep K 1 : ModGL .E6 K) = (e6ASRep K 1 : ModGL .E6 K) * g :=
    mem_centralizer_singleton_iff.1 hgC
  have hgP := mem_parabolicSubgroup_nodes16_of_commute hgG hgc
  obtain ⟨⟨q, l⟩, ⟨hq, hl, rfl⟩, -⟩ :=
    (parabolic_root_radical_Levi_factors .E6 K nodes16).2.2.2.2.2.2.1 _ hgP
  have hqc := parabolicRadical_nodes16_le_centralizer hq
  have hlc : l ∈ centralizer ({(e6ASRep K 1 : ModGL .E6 K)} : Set (ModGL .E6 K)) := by
    have e : l = q⁻¹ * (q * l) := by group
    rw [e]
    exact mul_mem (inv_mem hqc) hgC
  exact mul_mem (mem_sup_left hq) (mem_sup_right (mem_inf.2 ⟨hl, hlc⟩))

theorem centralizer_e6Rep_one_le [CharP K 2] :
    centralizer ({(e6Rep K 1 : ModGL .E6 K)} : Set (ModGL .E6 K)) ⊓ adjointGroup .E6 K ≤
      rootSpan .E6 K yRadicalRoots ⊔ (parabolicLevi .E6 K nodes16 ⊓
        centralizer ({(e6ASRep K 1 : ModGL .E6 K)} : Set (ModGL .E6 K))).map
          (MulAut.conj (e6RepConj K 1 : ModGL .E6 K)).toMonoidHom := by
  intro g hg
  set n := (e6RepConj K 1 : ModGL .E6 K) with hn
  obtain ⟨hgC, hgG⟩ := mem_inf.1 hg
  have hyD : (e6Rep K 1 : ModGL .E6 K) = n * (e6ASRep K 1 : ModGL .E6 K) * n⁻¹ :=
    (congrArg Subtype.val (e6RepConj_mul_e6ASRep_mul_inv (K := K) 1)).symm
  have hg' : n⁻¹ * g * n ∈ centralizer ({(e6ASRep K 1 : ModGL .E6 K)} : Set (ModGL .E6 K)) ⊓
      adjointGroup .E6 K := by
    refine mem_inf.2 ⟨mem_centralizer_singleton_iff.2 ?_,
      mul_mem (mul_mem (inv_mem (e6RepConj K 1).2) hgG) (e6RepConj K 1).2⟩
    have h1 := mem_centralizer_singleton_iff.1 hgC
    rw [hyD] at h1
    calc n⁻¹ * g * n * (e6ASRep K 1 : ModGL .E6 K)
        = n⁻¹ * (g * (n * (e6ASRep K 1 : ModGL .E6 K) * n⁻¹)) * n := by group
      _ = n⁻¹ * (n * (e6ASRep K 1 : ModGL .E6 K) * n⁻¹ * g) * n := by rw [h1]
      _ = (e6ASRep K 1 : ModGL .E6 K) * (n⁻¹ * g * n) := by group
  have h2 := centralizer_e6ASRep_one_le hg'
  have h3 : g ∈ (parabolicRadical .E6 K nodes16 ⊔ (parabolicLevi .E6 K nodes16 ⊓
      centralizer ({(e6ASRep K 1 : ModGL .E6 K)} : Set (ModGL .E6 K)))).map
        (MulAut.conj n).toMonoidHom :=
    ⟨n⁻¹ * g * n, h2, by simp [MulAut.conj_apply]; group⟩
  rwa [Subgroup.map_sup, ← rootSpan_yRadicalRoots_eq_map] at h3

end Main

end CFSG.SeitzReduction.E6Pilot
