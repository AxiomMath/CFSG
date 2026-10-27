module

public import CFSG.GH74.GLS.IVK.L2.Lemma12hc
public import CFSG.GH74.GLS.IVK.L2.ExistNotation
public import CFSG.LocalAnalysis.ComponentInitial.FieldNineAlternatingSix
public import CFSG.GH74.GLS.Stage1.Thm3.Sec5.Transport
public import CFSG.Assembly.GL83LieDefs
public import CFSG.GH74.GLS.IVK.Proofs2.Lemma15a

public section

namespace CFSG.GH74.GLS.C3.Layer1.Bk

open Subgroup CFSG CFSG.GH74.GLS CFSG.GH74.GLS.IVK CFSG.GorensteinWalter
open scoped commutatorElement

theorem exists_L2_nine_equiv {H : Type} [Group H] (e : H ≃* alternatingGroup (Fin 6)) :
    ∃ (F : Type) (_ : Field F) (_ : Finite F) (_ : H ≃* L2 F), Nat.card F = 9 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let _ : Fintype (GaloisField 3 2) := Fintype.ofFinite _
  have hc' : Nat.card (GaloisField 3 2) = 9 := by
    rw [GaloisField.card 3 2 (by norm_num)]; norm_num
  have hc : Fintype.card (GaloisField 3 2) = 9 := by
    rw [← Nat.card_eq_fintype_card]; exact hc'
  obtain ⟨e6⟩ := LocalAnalysis.ComponentInitial.unique_field_nine_projective_linear_alternating_six_isomorphism
    (GaloisField 3 2) hc
  exact ⟨GaloisField 3 2, inferInstance, inferInstance,
    e.trans (e6.symm.trans (L2.equivPSL (GaloisField 3 2)).symm), hc'⟩

theorem card_fieldAutSub_nine {F : Type} [Field F] [Finite F] (hF : L2Field F) (hF9 : Nat.card F = 9)
    {H : Type} [Group H] [Finite H] (e : H ≃* L2 F) : Nat.card ↥(fieldAutSub e) = 2 := by
  obtain ⟨-, -, hcard⟩ := ivk_1_2e F hF H e
  exact hcard 3 2 Nat.prime_three (by rw [hF9]; norm_num)

theorem decomp_of_not_innDiag {F : Type} [Field F] [Finite F] (hF : L2Field F) (hF9 : Nat.card F = 9)
    {H : Type} [Group H] [Finite H] (e : H ≃* L2 F) {ρ : MulAut H}
    (hdiag : ρ ∉ innDiagSub e) (hρ2 : ρ ^ 2 = 1) :
    ∃ c ∈ innAut H, ∃ g ∈ fieldAutSub e, orderOf g = 2 ∧ ρ = c * g := by
  have : (innDiagSub e).Normal := innDiagSub_normal e
  have htop := innDiagSub_sup_fieldAutSub e
  have hρtop : ρ ∈ innDiagSub e ⊔ fieldAutSub e := htop ▸ Subgroup.mem_top ρ
  obtain ⟨d, hd, g, hg, hdg⟩ := Subgroup.mem_sup_of_normal_left.1 hρtop
  have hg1 : g ≠ 1 := by
    intro h1
    apply hdiag
    rw [← hdg, h1, mul_one]
    exact hd
  have hF2 := card_fieldAutSub_nine hF hF9 e
  have hg2 : orderOf g = 2 := by
    have hdvd : orderOf g ∣ 2 := hF2 ▸ Subgroup.orderOf_dvd_natCard _ hg
    rcases (Nat.dvd_prime Nat.prime_two).1 hdvd with h | h
    · exact absurd (orderOf_eq_one_iff.1 h) hg1
    · exact h
  have hρ1 : ρ ≠ 1 := fun h => hdiag (h ▸ Subgroup.one_mem _)
  obtain ⟨N⟩ := exists_notation hF e
  have hFp : IsPGroup 2 ↥(fieldAutSub e) := IsPGroup.of_card (n := 1) (by rw [hF2]; norm_num)
  have hFT : fieldAutSub e ≤ (N.T : Subgroup (MulAut H)) := by
    have h1 := IsPGroup.inf_normalizer_sylow hFp N.T
    have h2 : fieldAutSub e ⊓ normalizer ((N.T : Subgroup (MulAut H)) : Set (MulAut H)) =
        fieldAutSub e := inf_eq_left.2 N.T_inv
    have h3 : fieldAutSub e ⊓ (N.T : Subgroup (MulAut H)) = fieldAutSub e := h1.symm.trans h2
    exact inf_eq_left.1 h3
  have hgR : g ∈ (N.T : Subgroup (MulAut H)) ⊓ fieldAutSub e := ⟨hFT hg, hg⟩
  have hdg2 : orderOf (d * g) = 2 := by rw [hdg]; exact orderOf_eq_prime hρ2 hρ1
  obtain ⟨a, ha, hconj⟩ := ivk_1_2h_c F hF H e N g hgR hg2 d hd hdg2
  have hdiagN : innAut H ⊔ Subgroup.zpowers N.t = innDiagSub e := (ivk_1_2d F hF H e N).1
  obtain ⟨-, -, -, hcomm⟩ := ivk_1_2a_struct F hF H e N
  have hc : ⁅g, a⁻¹⁆ ∈ innAut H := hcomm g hg a⁻¹ (hdiagN ▸ Subgroup.inv_mem _ ha)
  refine ⟨⁅a⁻¹, g⁆, ?_, g, hg, hg2, ?_⟩
  · rw [← commutatorElement_inv]
    exact inv_mem hc
  · have h1 : a * (d * g) * a⁻¹ = g := hconj
    rw [← hdg]
    have h2 : d * g = a⁻¹ * g * a := by
      calc d * g = a⁻¹ * (a * (d * g) * a⁻¹) * a := by group
        _ = a⁻¹ * g * a := by rw [h1]
    rw [h2, commutatorElement_def]
    group

theorem involution_cases_L2_nine {F : Type} [Field F] [Finite F] (hF : L2Field F)
    (hF9 : Nat.card F = 9) {H : Type} [Group H] [Finite H] (e : H ≃* L2 F)
    (Sig : Subgroup (MulAut H)) (hInn : innAut H ≤ Sig)
    (hf : ∀ f ∈ fieldAutSub e, orderOf f = 2 → f ∈ Sig)
    {ρ : MulAut H} (hρ2 : ρ ^ 2 = 1) :
    ρ ∈ Sig ∨ (3 ≤ Nat.card ↥(xu ρ) ∧ Odd (Nat.card ↥(xu ρ))) := by
  by_cases hdiag : ρ ∈ innDiagSub e
  · by_cases hin : ρ ∈ innAut H
    · exact Or.inl (hInn hin)
    · have hρ1 : ρ ≠ 1 := fun h => hin (h ▸ Subgroup.one_mem _)
      have hord : orderOf ρ = 2 := orderOf_eq_prime hρ2 hρ1
      obtain ⟨-, hodd, h3, -⟩ := Proofs2.xu_outer_data hF e hdiag hin hord
      exact Or.inr ⟨h3, hodd⟩
  · left
    obtain ⟨c, hc, g, hg, hg2, rfl⟩ := decomp_of_not_innDiag hF hF9 e hdiag hρ2
    exact Sig.mul_mem (hInn hc) (hf g hg hg2)

@[expose] noncomputable def swapAut : MulAut (alternatingGroup (Fin 6)) :=
  MulAut.conjNormal (H := alternatingGroup (Fin 6)) (Equiv.swap (0 : Fin 6) 1)

theorem swapAut_sq : swapAut ^ 2 = 1 := by
  unfold swapAut
  rw [← map_pow, sq, Equiv.swap_mul_self, map_one]

theorem swapAut_not_inner :
    swapAut ∉ (MulAut.conj : alternatingGroup (Fin 6) →* MulAut (alternatingGroup (Fin 6))).range := by
  rintro ⟨a, ha⟩
  have h1 : MulAut.conjNormal (H := alternatingGroup (Fin 6)) (a : Equiv.Perm (Fin 6)) =
      MulAut.conjNormal (H := alternatingGroup (Fin 6)) (Equiv.swap (0 : Fin 6) 1) := by
    rw [MulAut.conjNormal_val]
    exact ha
  have h2 := CFSG.GroupTheory.AutAlternating.conjNormal_injective_alternatingGroup 6 (by norm_num) h1
  have h3 : (Equiv.swap (0 : Fin 6) 1) ∈ alternatingGroup (Fin 6) := h2 ▸ a.2
  rw [Equiv.Perm.mem_alternatingGroup, Equiv.Perm.sign_swap (by decide)] at h3
  exact absurd h3 (by decide)

theorem exists_order_four_fixed :
    ∃ g : alternatingGroup (Fin 6), orderOf g = 4 ∧ swapAut g = g := by
  let c : Equiv.Perm (Fin 6) := Equiv.swap 0 1 * (Equiv.swap 2 3 * Equiv.swap 3 4 * Equiv.swap 4 5)
  have hc : c ∈ alternatingGroup (Fin 6) := by
    rw [Equiv.Perm.mem_alternatingGroup]
    decide
  refine ⟨⟨c, hc⟩, ?_, ?_⟩
  · have h4 : ((⟨c, hc⟩ : alternatingGroup (Fin 6)) ^ 4 = 1) := by
      apply Subtype.ext
      show c ^ 4 = 1
      decide
    have h2 : ¬ ((⟨c, hc⟩ : alternatingGroup (Fin 6)) ^ 2 = 1) := by
      intro h
      have := congrArg Subtype.val h
      revert this
      show ¬ (c ^ 2 = 1)
      decide
    exact orderOf_eq_prime_pow (p := 2) (n := 1) (by simpa using h2) (by simpa using h4)
  · apply Subtype.ext
    unfold swapAut
    rw [MulAut.conjNormal_apply]
    show Equiv.swap (0 : Fin 6) 1 * c * (Equiv.swap (0 : Fin 6) 1)⁻¹ = c
    decide

theorem card_fixedSubgroup_of_outer_nine {F : Type} [Field F] [Finite F] (hF : L2Field F)
    (hF9 : Nat.card F = 9) {H : Type} [Group H] [Finite H] (e : H ≃* L2 F) {v : MulAut H}
    (hv : v ∈ innDiagSub e) (hv' : v ∉ innAut H) (hv2 : orderOf v = 2) :
    Nat.card ↥(fixedSubgroup H v) = 10 := by
  have hmod : (Nat.card F : ℤ) ≡ 1 [ZMOD 4] := by rw [hF9]; decide
  obtain ⟨-, ⟨k, hk, hk2, ⟨φ⟩⟩, -⟩ :=
    ivk_1_3b F hF H e 1 (Or.inl rfl) hmod 10 (by rw [hF9]; norm_num) v hv hv' hv2
  have : NeZero k := ⟨by omega⟩
  rw [Nat.card_congr φ.toEquiv, Nat.card_eq_fintype_card, DihedralGroup.card]
  omega

theorem eq_of_orderOf_two_of_card_two {G : Type} [Group G] [Finite G] {S : Subgroup G}
    (hS : Nat.card ↥S = 2)
    {g f : G} (hg : g ∈ S) (hf : f ∈ S) (hg2 : orderOf g = 2) (hf2 : orderOf f = 2) : f = g := by
  have hzp : Subgroup.zpowers g = S :=
    Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.2 hg) (by rw [Nat.card_zpowers, hg2, hS])
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 (hzp ▸ hf)
  have h1 : g ^ (k % (orderOf g : ℤ)) = g ^ k := zpow_mod_orderOf g k
  rw [hg2] at h1
  simp only [Nat.cast_ofNat] at h1
  rcases Int.emod_two_eq_zero_or_one k with h | h
  · rw [h] at h1
    simp at h1
    rw [← h1] at hf2
    simp at hf2
  · rw [h] at h1
    simpa using h1.symm

theorem alt6_involution_cases {H : Type} [Group H] [Finite H] (e : H ≃* alternatingGroup (Fin 6))
    {ρ : MulAut H} (hρ2 : ρ ^ 2 = 1) :
    (∃ σ : Equiv.Perm (Fin 6),
        MulAut.congr e ρ = MulAut.conjNormal (H := alternatingGroup (Fin 6)) σ) ∨
      (3 ≤ Nat.card ↥(xu ρ) ∧ Odd (Nat.card ↥(xu ρ))) := by
  obtain ⟨F, _, _, e', hF9⟩ := exists_L2_nine_equiv e
  have hF : L2Field F := ⟨by rw [hF9]; decide, by rw [hF9]; norm_num⟩
  let SigH : Subgroup (MulAut H) :=
    (MulAut.conjNormal (H := alternatingGroup (Fin 6)) :
      Equiv.Perm (Fin 6) →* MulAut (alternatingGroup (Fin 6))).range.comap
      (MulAut.congr e).toMonoidHom
  have hmem : ∀ φ : MulAut H, φ ∈ SigH ↔ ∃ σ : Equiv.Perm (Fin 6),
      MulAut.conjNormal (H := alternatingGroup (Fin 6)) σ = MulAut.congr e φ := fun φ => Iff.rfl
  have hconjcongr : ∀ h : H, MulAut.congr e (MulAut.conj h) = MulAut.conj (e h) := by
    intro h
    ext x
    simp [MulAut.congr_apply, MulAut.conj_apply]
  have hInn : innAut H ≤ SigH := by
    rintro _ ⟨h, rfl⟩
    refine (hmem _).2 ⟨((e h : alternatingGroup (Fin 6)) : Equiv.Perm (Fin 6)), ?_⟩
    rw [MulAut.conjNormal_val, hconjcongr]
  have hf : ∀ f ∈ fieldAutSub e', orderOf f = 2 → f ∈ SigH := by
    intro f hfF hf2
    let sH : MulAut H := (MulAut.congr e).symm swapAut
    have hcs : MulAut.congr e sH = swapAut := MulEquiv.apply_symm_apply _ _
    have hsH_mem : sH ∈ SigH := (hmem _).2 ⟨_, by rw [hcs]; rfl⟩
    have hsH2 : sH ^ 2 = 1 := by
      show ((MulAut.congr e).symm swapAut) ^ 2 = 1
      rw [← map_pow, swapAut_sq, map_one]
    have hsH1 : sH ≠ 1 := by
      intro h1
      have : swapAut = 1 := by rw [← hcs, h1, map_one]
      exact swapAut_not_inner ⟨1, by simpa using this.symm⟩
    have hsH_inn : sH ∉ innAut H := by
      rintro ⟨h, hh⟩
      apply swapAut_not_inner
      refine ⟨e h, ?_⟩
      rw [← hcs, ← hh, hconjcongr]
    have hsH_diag : sH ∉ innDiagSub e' := by
      intro hd
      have hord : orderOf sH = 2 := orderOf_eq_prime hsH2 hsH1
      have hcard := card_fixedSubgroup_of_outer_nine hF hF9 e' hd hsH_inn hord
      obtain ⟨g, hg4, hgfix⟩ := exists_order_four_fixed
      have hfix := Stage1.Thm3.Sec5.fixedSubgroup_congr e sH
      have hgmem : g ∈ fixedSubgroup (alternatingGroup (Fin 6)) (MulAut.congr e sH) := by
        rw [hcs]
        exact hgfix
      rw [hfix] at hgmem
      obtain ⟨g', hg', hg'e⟩ := hgmem
      have hg'4 : orderOf g' = 4 := by
        rw [← hg4, ← hg'e]
        exact (MulEquiv.orderOf_eq e g').symm
      have hdvd : orderOf (⟨g', hg'⟩ : ↥(fixedSubgroup H sH)) ∣ Nat.card ↥(fixedSubgroup H sH) :=
        orderOf_dvd_natCard _
      rw [hcard, Subgroup.orderOf_mk, hg'4] at hdvd
      omega
    obtain ⟨c, hc, g, hg, hg2, hsHeq⟩ := decomp_of_not_innDiag hF hF9 e' hsH_diag hsH2
    have hgS : g ∈ SigH := by
      have : g = c⁻¹ * sH := by rw [hsHeq]; group
      rw [this]
      exact SigH.mul_mem (SigH.inv_mem (hInn hc)) hsH_mem
    have hF2 := card_fieldAutSub_nine hF hF9 e'
    rw [eq_of_orderOf_two_of_card_two hF2 hg hfF hg2 hf2]
    exact hgS
  rcases involution_cases_L2_nine hF hF9 e' SigH hInn hf hρ2 with h | h
  · obtain ⟨σ, hσ⟩ := (hmem ρ).1 h
    exact Or.inl ⟨σ, hσ.symm⟩
  · exact Or.inr h

theorem index_conjNormal_range_alt6 :
    ((MulAut.conjNormal (H := alternatingGroup (Fin 6)) :
      Equiv.Perm (Fin 6) →* MulAut (alternatingGroup (Fin 6))).range).index = 2 := by
  obtain ⟨F, _, _, e', hF9⟩ := exists_L2_nine_equiv (MulEquiv.refl (alternatingGroup (Fin 6)))
  have hF : L2Field F := ⟨by rw [hF9]; decide, by rw [hF9]; norm_num⟩
  have h360 : Nat.card (alternatingGroup (Fin 6)) = 360 := by
    rw [Nat.card_eq_fintype_card, card_alternatingGroup]
    simp [Nat.factorial]
  have hAut : Nat.card (MulAut (alternatingGroup (Fin 6))) = 1440 := by
    rw [card_mulAut_eq e', card_innDiagSub e' hF, card_fieldAutSub_nine hF hF9 e', h360]
  have hSig : Nat.card ↥((MulAut.conjNormal (H := alternatingGroup (Fin 6)) :
      Equiv.Perm (Fin 6) →* MulAut (alternatingGroup (Fin 6))).range) = 720 := by
    rw [← Nat.card_congr (MonoidHom.ofInjective
      (CFSG.GroupTheory.AutAlternating.conjNormal_injective_alternatingGroup 6 (by norm_num))).toEquiv]
    rw [Nat.card_eq_fintype_card, Fintype.card_perm, Fintype.card_fin]
    rfl
  have h := Subgroup.card_mul_index ((MulAut.conjNormal (H := alternatingGroup (Fin 6)) :
      Equiv.Perm (Fin 6) →* MulAut (alternatingGroup (Fin 6))).range)
  rw [hSig, hAut] at h
  omega

end CFSG.GH74.GLS.C3.Layer1.Bk
