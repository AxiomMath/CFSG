module

public import CFSG.Quasithin.Vol2.Ch5Sec2M23GxNorm
public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch5Sec2M23ME16

public section

namespace CFSG.Quasithin.H13

open CFSG.ComponentClassification.WittDesign CFSG.Monster.B.Classical.Plane CFSG.Fischer
  CFSG.EvenSmallLie.UnitarySix.MathieuExt CFSG.LocalAnalysis.ComponentInitial CFSG.Open
  CFSG.Blueprint CFSG.QuasithinUnique
open scoped MatrixGroups Matrix

variable {G : Type} [Group G]

theorem exists_rho_normalized_F4 [CFSG.GH74.QTGen4.Finite4 G]
    (h526 : Stmt5_2_6_F4) (h527 : Stmt5_2_7_F4) (h1284 : Lemma128Four) (hSz : Stmt5_2_8_Sz_F4)
    (hU4 : Stmt5_2_8_U4_F4) (hsp : Stmt5_2_8_special_F4) (hQ : Stmt5_2_8_Q_F4)
    (hset : Stmt5_2_10_setting_F4) (hfus : M23Fusion3_F4) (h515 : Stmt5_2_15_F4) (h516 : Stmt5_2_16_F4)
    {T M L V H B D L₂ M2 : Subgroup G} {n : ℕ} {π : ↥M2 →* Equiv.Perm (Fin 7)}
    (hyp : Hyp5_2_4 G T M L V H B D L₂ n) (hM23 : IsOfTypeM23 M L H B D T)
    (hS : IsM23Setting T H M2 π) :
    ∃ (ρ : ↥(m23Gx T M L H B D) →* Equiv.Perm (Fin 21)) (t₁ : G) (A : GL (Fin 3) F4)
      (ht₁ : t₁ ∈ m23Gx T M L H B D),
      Function.Injective ρ ∧ t₁ ∈ T ∧ t₁ ∉ m23G0 M L H B D ∧
      (∀ g : G, g ∈ m23Gx T M L H B D → g ∈ m23G0 M L H B D ∨ g * t₁⁻¹ ∈ m23G0 M L H B D) ∧
      (∀ (g : G) (hg : g ∈ m23Gx T M L H B D), g ∈ m23G0 M L H B D → ρ ⟨g, hg⟩ ∈ P0) ∧
      ρ ⟨t₁, ht₁⟩ = planePerm (semΓ A frobF4) ∧ (A : Matrix (Fin 3) (Fin 3) F4).det = 1 ∧
      (∀ (g : G) (hg : g ∈ m23Gx T M L H B D), g ∈ pCoreOf 2 M2 → ρ ⟨g, hg⟩ ∈ Ea) ∧
      (∀ (g : G) (hg : g ∈ m23Gx T M L H B D), g ∈ pCoreOf 2 L → ρ ⟨g, hg⟩ ∈ Ec) ∧
      Nat.card ↥(m23Gx T M L H B D) = 40320 := by
  classical
  have h := hyp.toHyp5_0_1
  set K := oTwoUpper H with hKdef
  set G0 := m23G0 M L H B D with hG0def
  have hLG0 : L ≤ G0 := le_sup_left.trans (le_sup_left.trans le_sup_left)
  have hKG0 : K ≤ G0 := le_sup_right.trans le_sup_right
  have hDL : D ≤ L := hyp.notation59.2.1.1.trans inf_le_left
  have hG0LK : G0 = L ⊔ K := by
    apply le_antisymm
    · exact sup_le (sup_le (sup_le le_sup_left (inf_le_right.trans le_sup_left))
        (inf_le_right.trans le_sup_right))
        (sup_le (sup_le (hDL.trans le_sup_left) (inf_le_right.trans le_sup_left)) le_sup_right)
    · exact sup_le hLG0 hKG0

  obtain ⟨-, hTN, hidx, F, hFf, hFfin, hF4, e, t₁, A, σ, ht₁T, hσ, hrel⟩ :=
    h516 G T M L V H B D L₂ n hyp hM23
  have : Fintype F := Fintype.ofFinite F
  have : CharP F 2 :=
    charP_of_card_eq_prime_pow (f := 2) (by rw [← Nat.card_eq_fintype_card, hF4]; norm_num)
  set κ : F ≃+* F4 := FiniteField.ringEquivOfCardEq (K := F) (K' := F4)
    (by rw [← Nat.card_eq_fintype_card, hF4, F4.card]) with hκ

  obtain ⟨s, s', hs1, hs2, ht2, ht1, hss, htt, hst⟩ :=
    exists_involutions_m23_of_F4 hset hfus h515 hyp hM23
  have hG1par := mem_maximalParabolics_of_isAmalgamOfGroup hM23.1 hs1 hs2 ht2 ht1 hss htt hst
  obtain ⟨-, -, h16, -, hcardL⟩ := setting_L_facts_F4 h526 h1284 hSz hU4 hsp hQ hyp hM23 hS
  have hcardG1 := card_eq_960_of_isAmalgamOfGroup hM23.1
  have hLG1 : L = L ⊔ (sec52S M H ⊓ L) ⊔ (B ⊓ K) :=
    Subgroup.eq_of_le_of_card_ge (le_sup_left.trans le_sup_left) (by rw [hcardG1, hcardL])
  have hLpar : L.subgroupOf G0 ∈ LinearFlag.maximalParabolics ↥G0 2 := by
    rw [hLG1]
    exact hG1par

  obtain ⟨e', A', W, hW1, heL, hrel'⟩ := exists_point_type e hLpar A σ hrel
  set ψ₀ : ↥G0 →* Equiv.Perm (Fin 21) :=
    pslPerm.comp ((pslCoord κ).toMonoidHom.comp e'.toMonoidHom) with hψ₀
  have hψ₀inj : Function.Injective ψ₀ := injective_pslCoord_comp κ e'
  have hψ₀r : ψ₀.range = P0 := range_pslCoord_comp κ e'
  have hind₀ := induces_pslCoord κ e' A' hσ hrel'
  obtain ⟨q, hq⟩ := exists_fixed_point_of_projStabilizer κ hW1
  have hψ₀L : ∀ x : ↥G0, (x : G) ∈ L → ψ₀ x q = q := by
    intro x hxL
    apply hq
    rw [← heL]
    exact ⟨x, Subgroup.mem_subgroupOf.mpr hxL, rfl⟩

  obtain ⟨hTLK, hUTL, hVTL, hTL64⟩ :=
    inf_L_facts_of_setting_F4 h526 h527 h1284 hSz hU4 hsp hQ hyp hM23 hS
  set SG : Subgroup ↥G0 := (T ⊓ L).subgroupOf G0 with hSG
  have hSG64 : Nat.card ↥(SG.map ψ₀) = 64 := by
    rw [Subgroup.card_map_of_injective hψ₀inj,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe (inf_le_right.trans hLG0)).toEquiv, hTL64]
  obtain ⟨p, hpP, hp⟩ := exists_conj_eq_of_card (P := P0) card_range_pslPerm
    (by rw [← hψ₀r]; exact Subgroup.map_le_range _ _) U3_le_P0 hSG64 card_U3
  obtain ⟨M₁, -, rfl⟩ := exists_GL_of_mem_P0 hpP
  set p₁ := planePerm (semΓ M₁ (RingEquiv.refl F4)) with hp₁
  set ψ₁ : ↥G0 →* Equiv.Perm (Fin 21) := (MulAut.conj p₁).toMonoidHom.comp ψ₀ with hψ₁
  have hψ₁apply : ∀ x, ψ₁ x = p₁ * ψ₀ x * p₁⁻¹ := fun x => rfl
  have hψ₁inj : Function.Injective ψ₁ := (MulAut.conj p₁).injective.comp hψ₀inj
  have hψ₁r : ψ₁.range = P0 := range_conj_eq_P0 hψ₀r M₁
  have hind₁ := induces_conj hind₀ M₁
  have hU3 : ∀ u ∈ U3, ∃ x : ↥G0, (x : G) ∈ T ⊓ L ∧ ψ₁ x = u := by
    intro u hu
    obtain ⟨_, ⟨x, hx, rfl⟩, hux⟩ := hp u hu
    exact ⟨x, Subgroup.mem_subgroupOf.mp hx, by rw [hψ₁apply, hux]⟩

  have hpq : p₁ q = 5 := by
    rw [← fix_Ec_iff]
    intro a b
    obtain ⟨x, hxTL, hx⟩ := hU3 _ (Ec_le_U3 ⟨a, b, rfl⟩)
    rw [← hx, hψ₁apply]
    have e1 : p₁⁻¹ (p₁ q) = q := by simp
    simp only [Equiv.Perm.mul_apply]
    rw [e1, hψ₀L x hxTL.2]
  have hψ₁L : ∀ x : ↥G0, (x : G) ∈ L → ψ₁ x 5 = 5 := by
    intro x hxL
    rw [← hpq, hψ₁apply]
    have e1 : p₁⁻¹ (p₁ q) = q := by simp
    simp only [Equiv.Perm.mul_apply]
    rw [e1, hψ₀L x hxL]

  have hle_TL : ∀ E : Subgroup (Equiv.Perm (Fin 21)), E ≤ U3 →
      (E.comap ψ₁).map G0.subtype ≤ T ⊓ L := by
    rintro E hE _ ⟨x, hx, rfl⟩
    obtain ⟨y, hyTL, hy⟩ := hU3 _ (hE hx)
    rw [hψ₁inj hy] at hyTL
    exact hyTL
  obtain ⟨hWa2, hWac, hWa16⟩ := comap_elemAbelian_facts hψ₁inj hψ₁r (Ea_le_U3.trans U3_le_P0)
    Ea_sq (fun p hp q hq => Ea_comm p q hp hq) card_Ea
  obtain ⟨hWc2, hWcc, hWc16⟩ := comap_elemAbelian_facts hψ₁inj hψ₁r (Ec_le_U3.trans U3_le_P0)
    Ec_sq (fun p hp q hq => Ec_comm p q hp hq) card_Ec
  have hWa := eq_or_eq_of_isElemAbelian_of_le_inf_L_F4 h526 h527 h1284 hSz hU4 hsp hQ hyp hM23 hS
    (hle_TL Ea Ea_le_U3) hWa2 hWac hWa16
  have hWc := eq_or_eq_of_isElemAbelian_of_le_inf_L_F4 h526 h527 h1284 hSz hU4 hsp hQ hyp hM23 hS
    (hle_TL Ec Ec_le_U3) hWc2 hWcc hWc16
  have hmemW : ∀ (E : Subgroup (Equiv.Perm (Fin 21))) (x : ↥G0),
      (x : G) ∈ (E.comap ψ₁).map G0.subtype → ψ₁ x ∈ E := by
    rintro E x ⟨y, hy, hyx⟩
    rw [show x = y from Subtype.ext hyx.symm]
    exact hy
  have hne : (Ea.comap ψ₁).map G0.subtype ≠ (Ec.comap ψ₁).map G0.subtype := by
    intro hE
    apply Ea_ne_Ec
    refine Subgroup.eq_of_le_of_card_ge (fun p hp => ?_) (by rw [card_Ea, card_Ec])
    obtain ⟨x, rfl⟩ : p ∈ ψ₁.range := hψ₁r ▸ Ea_le_U3.trans U3_le_P0 hp
    exact hmemW Ec x (hE ▸ ⟨x, hp, rfl⟩)

  obtain ⟨-, -, hQeq, -, -⟩ := setting_K_facts_F4 h526 h1284 hSz hU4 hsp hQ hyp hM23 hS
  have hKU : ∀ k ∈ K, ∀ u ∈ pCoreOf 2 M2, k * u * k⁻¹ ∈ pCoreOf 2 M2 := by
    intro k hk u hu
    have hKN : K ≤ Subgroup.normalizer (pCoreOf 2 K : Set G) :=
      Subgroup.le_normalizer.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 K)
    rw [← hQeq] at hu ⊢
    exact (Subgroup.mem_normalizer_iff.mp (hKN hk) u).mp hu
  have hgood : (Ea.comap ψ₁).map G0.subtype = pCoreOf 2 M2 ∧
      (Ec.comap ψ₁).map G0.subtype = pCoreOf 2 L := by
    rcases hWa with hWa | hWa
    · rcases hWc with hWc | hWc
      · exact absurd (hWa.trans hWc.symm) hne
      · exact ⟨hWa, hWc⟩
    · exfalso
      have hWcU : (Ec.comap ψ₁).map G0.subtype = pCoreOf 2 M2 := by
        rcases hWc with hWc | hWc
        · exact hWc
        · exact absurd (hWa.trans hWc.symm) hne

      have hψ₁K : ∀ x : ↥G0, (x : G) ∈ K → ψ₁ x 5 = 5 := by
        intro k hkK
        apply apply_five_of_normalizes_Ec
        intro p' hp'
        obtain ⟨u, rfl⟩ : p' ∈ ψ₁.range := hψ₁r ▸ Ec_le_U3.trans U3_le_P0 hp'
        have huU : (u : G) ∈ pCoreOf 2 M2 := hWcU ▸ ⟨u, hp', rfl⟩
        have hkuU := hKU k hkK u huU
        rw [← map_inv, ← map_mul, ← map_mul]
        apply hmemW Ec
        rw [hWcU]
        exact hkuU

      have hall : G0 ≤ ((MulAction.stabilizer (Equiv.Perm (Fin 21)) (5 : Fin 21)).comap
          ψ₁).map G0.subtype := by
        refine (le_of_eq hG0LK).trans (sup_le (fun l hl => ⟨⟨l, hLG0 hl⟩, ?_, rfl⟩)
          (fun k hk => ⟨⟨k, hKG0 hk⟩, ?_, rfl⟩))
        · exact hψ₁L _ hl
        · exact hψ₁K _ hk
      obtain ⟨g, hg⟩ : lowPerm ∈ ψ₁.range := hψ₁r ▸ lowPerm_mem_P0
      obtain ⟨g', hg', hgg'⟩ := hall g.2
      rw [show g = g' from Subtype.ext hgg'.symm] at hg
      apply lowPerm_apply_five
      rw [← hg]
      exact hg'

  set A₁ : GL (Fin 3) F4 := M₁ * Matrix.GeneralLinearGroup.map κ.toRingHom A' *
    Matrix.GeneralLinearGroup.map (frobF4 : F4 →+* F4) M₁⁻¹ with hA₁
  set d : F4ˣ := Matrix.GeneralLinearGroup.det A₁ with hd
  set pD := planePerm (semΓ (diagGL d) (RingEquiv.refl F4)) with hpD
  set ψ₂ : ↥G0 →* Equiv.Perm (Fin 21) := (MulAut.conj pD).toMonoidHom.comp ψ₁ with hψ₂
  have hψ₂apply : ∀ x, ψ₂ x = pD * ψ₁ x * pD⁻¹ := fun x => rfl
  have hψ₂inj : Function.Injective ψ₂ := (MulAut.conj pD).injective.comp hψ₁inj
  have hψ₂r : ψ₂.range = P0 := range_conj_eq_P0 hψ₁r (diagGL d)
  have hind₂ := induces_conj hind₁ (diagGL d)
  set A₂ : GL (Fin 3) F4 := diagGL d * A₁ *
    Matrix.GeneralLinearGroup.map (frobF4 : F4 →+* F4) (diagGL d)⁻¹ with hA₂
  have hdetA₂ : (A₂ : Matrix (Fin 3) (Fin 3) F4).det = 1 := by
    have hD : Matrix.GeneralLinearGroup.det (diagGL d) = d := Units.ext (det_diagGL d)
    have hfrob : Units.map ((frobF4 : F4 →+* F4) : F4 →* F4) d = d * d :=
      Units.ext (by simp [frobF4_apply])
    have hu : Matrix.GeneralLinearGroup.det A₂ = 1 := by
      rw [hA₂, map_mul, map_mul, Matrix.GeneralLinearGroup.map_det, map_inv, hD, map_inv, hfrob,
        ← hd]
      group
    have := congrArg Units.val hu
    rwa [Matrix.GeneralLinearGroup.val_det_apply] at this

  obtain ⟨ρ, ht₁GT, hρinj, ht₁G0, hsplit, hρG0, hρt, hcard⟩ :=
    exists_rho_of_induces hTN hidx hψ₂inj hψ₂r ht₁T A₂ hind₂
  refine ⟨ρ, t₁, A₂, ht₁GT, hρinj, ht₁T, ht₁G0, hsplit, ?_, hρt, hdetA₂, ?_, ?_, hcard⟩
  · intro g hg hgG0
    rw [hρG0 g hgG0, ← hψ₂r]
    exact ⟨_, rfl⟩
  · intro g hg hgU
    have hgG0 : g ∈ G0 := hKG0 (hQeq ▸ CFSG.LieType.BorelTits.pCoreOf_le 2 K |>.trans le_rfl <|
      hQeq.symm ▸ hgU)
    rw [hρG0 g hgG0, hψ₂apply]
    obtain ⟨b, c, hbc⟩ := hmemW Ea ⟨g, hgG0⟩ (hgood.1 ▸ hgU)
    rw [hbc, conj_diag_uniPerm, mul_zero]
    exact ⟨_, _, rfl⟩
  · intro g hg hgV
    have hgG0 : g ∈ G0 := hLG0 (CFSG.LieType.BorelTits.pCoreOf_le 2 L hgV)
    rw [hρG0 g hgG0, hψ₂apply]
    obtain ⟨a, b, hab⟩ := hmemW Ec ⟨g, hgG0⟩ (hgood.2 ▸ hgV)
    rw [hab, conj_diag_uniPerm]
    exact ⟨_, _, rfl⟩

end CFSG.Quasithin.H13
