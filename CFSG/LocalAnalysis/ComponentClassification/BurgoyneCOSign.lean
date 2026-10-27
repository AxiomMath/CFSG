module

public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneCOIdent
public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneCOType
public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneOThree

public noncomputable section

namespace CFSG.ComponentClassification.Burgoyne.C

open Matrix CFSG Subgroup CFSG.Assembly.LowTwoRank
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
open CFSG.ComponentClassification.Burgoyne.Proj
open CFSG.ComponentClassification.Burgoyne.O
open CFSG.ComponentClassification.Burgoyne.PSL (diagGL coe_diagGL signMat)
open scoped MatrixGroups commutatorElement

variable {K : Type} [Field K] {d : ℕ} {w : Fin d → K} (hw : ∀ i, w i ≠ 0)

theorem card_omegaR_eq_three {n : ℕ} (hn : n = 3) [Finite K] (hK : ringChar K ≠ 2)
    (hK3 : Nat.card K ≠ 3) (R : GL (Fin n) K) (hR : (R : Matrix (Fin n) (Fin n) K)ᵀ = R) :
    Nat.card (omegaR R) * 2 = Nat.card SL(2, K) := by
  subst hn
  exact card_omegaR_three hK hK3 R hR

theorem three_le_card_of_isQuasisimple_blockP {I : Finset (Fin d)} (hIc : Iᶜ.Nonempty)
    (h2 : (2 : K) ≠ 0) (hq : IsQuasisimple (blockP K hw I)) : 3 ≤ I.card := by
  by_contra h
  obtain ⟨e⟩ := nonempty_projBlock_equiv hw h2 hIc (le_refl (omegaI hw I))
  rw [← blockP_eq_projBlock] at e
  have hs := isSolvable_omegaR_of_le_two (by omega : I.card ≤ 2) (wRes_ne_zero hw I)
  have hs' : Group.IsSolvable (blockP K hw I) :=
    Group.isSolvable_of_isSolvable_injective (f := e.toMonoidHom) e.injective
  have : Group.IsPerfect (blockP K hw I) := hq.1
  have : Nontrivial (blockP K hw I) := by
    by_contra hnt
    rw [not_nontrivial_iff_subsingleton] at hnt
    exact hq.2.2.elim fun a ha => ha.elim fun b hb => hb (Subsingleton.elim _ _)
  exact Group.IsPerfect.not_isSolvable _ hs'

theorem oIsoBlock_mono {T I : Finset (Fin d)} (hTI : T ⊆ I) :
    oIsoBlock K hw T ≤ oIsoBlock K hw I := by
  intro g hg
  rw [mem_oIsoBlock_iff] at hg ⊢
  exact ⟨hg.1, fun i j hij => hg.2 i j (hij.imp (fun h hi => h (hTI hi)) (fun h hj => h (hTI hj)))⟩

theorem card_lt_blockP [Finite K] (hK : ringChar K ≠ 2) (hK3 : Nat.card K ≠ 3)
    {I : Finset (Fin d)} (hIc : Iᶜ.Nonempty) (h4 : 4 ≤ I.card) (hNF : BlockNF w I) :
    Nat.card SL(2, K) < Nat.card (blockP K hw I) * 2 := by
  have h2 : (2 : K) ≠ 0 := Ring.two_ne_zero hK
  obtain ⟨I₀, hI₀, h3, hI₀w, -⟩ := hNF
  obtain ⟨a, ha, k, hk, hak⟩ := Finset.one_lt_card.1 (by omega : 1 < I₀.card)
  obtain ⟨T, haT, hTI, hT3⟩ := Finset.exists_subsuperset_card_eq
    (s := {a}) (t := I.erase k) (n := 3)
    (Finset.singleton_subset_iff.2 (Finset.mem_erase.2 ⟨hak, hI₀ ha⟩)) (by simp)
    (by rw [Finset.card_erase_of_mem (hI₀ hk)]; omega)
  have hTI' : T ⊆ I := hTI.trans (Finset.erase_subset k I)
  have hkT : k ∉ T := fun h => (Finset.mem_erase.1 (hTI h)).1 rfl
  have hTc : Tᶜ.Nonempty := ⟨k, Finset.mem_compl.2 hkT⟩
  have hle : blockP K hw T ≤ blockP K hw I :=
    map_mono fun g hg => commutator_mono (oIsoBlock_mono hw hTI') (oIsoBlock_mono hw hTI') hg
  have hs := signGL_pair_mem_oBlock hw (hI₀ ha) (hI₀ hk) hak (hI₀w a ha k hk)
  have hsΩ := oBlock_le_matrixDerived hw h2 I hs
  have hne : blockP K hw T ≠ blockP K hw I := by
    intro heq
    have hmem : projH _ (⟨signGL K {a, k}, hsΩ⟩ : matrixDerived (oQ (diagGL hw))) ∈
        blockP K hw T := heq ▸ ⟨⟨signGL K {a, k}, hsΩ⟩, hs, rfl⟩
    obtain ⟨g, hg, hge⟩ := hmem
    replace hg : (g : GL (Fin d) K) ∈ oBlock K hw T := hg
    have hgI : g ∈ (oBlock K hw I).subgroupOf (matrixDerived (oQ (diagGL hw))) :=
      commutator_mono (oIsoBlock_mono hw hTI') (oIsoBlock_mono hw hTI') hg
    have hsI : (⟨signGL K {a, k}, hsΩ⟩ : matrixDerived (oQ (diagGL hw))) ∈
        (oBlock K hw I).subgroupOf (matrixDerived (oQ (diagGL hw))) := hs
    have h1 := projH_injOn_oBlock hw hIc (mul_mem (inv_mem hgI) hsI)
      (by rw [map_mul, map_inv, hge, inv_mul_cancel])
    have hgs : g = ⟨signGL K {a, k}, hsΩ⟩ := (inv_mul_eq_one.1 h1)
    have hkk := ((mem_oIsoBlock_iff hw).1 (oBlock_le_oIsoBlock hw _ hg)).2 k k (Or.inl hkT)
    rw [hgs, ite_eq_left rfl] at hkk
    change signMat K {a, k} k k = 1 at hkk
    rw [signMat_apply_self, ite_eq_left (by simp)] at hkk
    exact Ring.two_ne_zero hK (by linear_combination -hkk)
  have hlt : Nat.card (blockP K hw T) < Nat.card (blockP K hw I) :=
    Subgroup.card_lt_of_lt (lt_of_le_of_ne hle hne)
  obtain ⟨e⟩ := nonempty_projBlock_equiv hw h2 hTc (le_refl (omegaI hw T))
  rw [← blockP_eq_projBlock] at e
  have hcard := card_omegaR_eq_three hT3 hK hK3 (diagGL (wRes_ne_zero hw T))
    (by rw [coe_diagGL]; exact diagonal_transpose _)
  rw [← Nat.card_congr e.toEquiv] at hcard
  omega

theorem comp_cases_of_le_blockP [Finite K] (hK : ringChar K ≠ 2) (J I : Finset (Fin d))
    (hI : I = J ∨ I = Jᶜ) (hJ : signGL K J ∈ matrixDerived (oQ (diagGL hw))) (hIc : Iᶜ.Nonempty)
    {L : Subgroup (StatedProj (matrixDerived (oQ (diagGL hw))))}
    (hLH : L ≤ centralizer ({projH _ ⟨signGL K J, hJ⟩} : Set _))
    (hL : IsPComponent 2 (L.subgroupOf (centralizer ({projH _ ⟨signGL K J, hJ⟩} : Set _))))
    (hLI : L ≤ blockP K hw I) :
    (L = blockP K hw I ∧ IsQuasisimple (blockP K hw I)) ∨
      (I.card = 4 ∧ Nat.card K ≠ 3 ∧ IsQuasisimple L ∧ Nonempty (L ≃* SL(2, K))) := by
  rcases blockP_cases hw hK I hIc with hs | hq | ⟨h4, hK3, L₁, L₂, hsup, hL₁, hL₂, hn₁, hn₂, hq₁,
      hq₂, e₁, e₂⟩
  · exact (not_le_of_isSolvable hLH hL hs hLI).elim
  · exact Or.inl ⟨eq_of_le_of_isQuasisimple hLI (blockP_le_centralizer hw J I hI hJ) hL hq, hq⟩
  · obtain ⟨hP₁H, hP₁s⟩ := isSubnormal_projBlock hw hK J I hI hJ hL₁ hn₁
    obtain ⟨hP₂H, hP₂s⟩ := isSubnormal_projBlock hw hK J I hI hJ hL₂ hn₂
    rw [hsup] at hLI
    rcases le_or_le_of_le_sup hLH hL hP₁H hP₂H hP₁s hP₂s hLI with h | h
    · have := eq_of_le_of_isQuasisimple h hP₁H hL hq₁
      rw [this]
      exact Or.inr ⟨h4, hK3, hq₁, e₁⟩
    · have := eq_of_le_of_isQuasisimple h hP₂H hL hq₂
      rw [this]
      exact Or.inr ⟨h4, hK3, hq₂, e₂⟩

theorem orth_sign_propC [Finite K] (hK : ringChar K ≠ 2) (hd : 7 ≤ d) (J : Finset (Fin d))
    (hJ : signGL K J ∈ matrixDerived (oQ (diagGL hw))) (hJne : J.Nonempty) (hJcne : Jᶜ.Nonempty)
    (hNF : 3 ≤ J.card → BlockNF w J) (hNFc : 3 ≤ Jᶜ.card → BlockNF w Jᶜ)
    {R₁ R₂ : Subgroup (StatedProj (matrixDerived (oQ (diagGL hw))))} {p n : ℕ} [Fact p.Prime]
    (hC : PropCData (projH _ ⟨signGL K J, hJ⟩) R₁ R₂ p n) :
    d = 7 ∧ Nat.card K = p ^ n ∧ ∃ I : Finset (Fin d), (I = J ∨ I = Jᶜ) ∧ I.card = 4 ∧
      R₂ ≤ blockP K hw I ∧ R₁ ≤ blockP K hw Iᶜ := by
  have h2 : (2 : K) ≠ 0 := Ring.two_ne_zero hK
  have hGF : ringChar (GaloisField p n) ≠ 2 := ringChar_galoisField_ne_two hC.p_ne_two
  have hGF2 : (2 : GaloisField p n) ≠ 0 := two_ne_zero_galoisField hC.p_ne_two
  have hcardGF : Nat.card (GaloisField p n) = p ^ n := GaloisField.card p n hC.n_pos.ne'
  set x := projH _ (⟨signGL K J, hJ⟩ : matrixDerived (oQ (diagGL hw))) with hx
  have hblock : ∀ {L : Subgroup (StatedProj (matrixDerived (oQ (diagGL hw))))},
      L ≤ centralizer ({x} : Set _) → IsPComponent 2 (L.subgroupOf (centralizer ({x} : Set _))) →
      ∃ I, (I = J ∨ I = Jᶜ) ∧ L ≤ blockP K hw I := by
    intro L hLH hL
    have hsup := le_blockP_sup_of_perfect hw hK J hJ hLH (commutator_eq_of_isPComponent hLH hL)
    rcases le_or_le_of_le_sup hLH hL (blockP_le_centralizer hw J J (Or.inl rfl) hJ)
      (blockP_le_centralizer hw J Jᶜ (Or.inr rfl) hJ) (isSubnormal_blockP hw hK J J (Or.inl rfl) hJ)
      (isSubnormal_blockP hw hK J Jᶜ (Or.inr rfl) hJ) hsup with h | h
    · exact ⟨J, Or.inl rfl, h⟩
    · exact ⟨Jᶜ, Or.inr rfl, h⟩
  have hIc : ∀ {I : Finset (Fin d)}, (I = J ∨ I = Jᶜ) → Iᶜ.Nonempty := by
    rintro I (rfl | rfl)
    · exact hJcne
    · rwa [compl_compl]
  have hNF' : ∀ {I : Finset (Fin d)}, (I = J ∨ I = Jᶜ) → 3 ≤ I.card → BlockNF w I := by
    rintro I (rfl | rfl)
    · exact hNF
    · exact hNFc
  obtain ⟨e₁⟩ := hC.iso₁
  obtain ⟨e₂⟩ := hC.iso₂
  have hR12 : R₁ ≠ R₂ := by
    intro h
    subst h
    have h1 := Nat.card_congr e₁.toEquiv
    rw [Nat.card_congr e₂.toEquiv, ← card_PSL_mul_two hGF] at h1
    have hpos : 0 < Nat.card PSL(2, GaloisField p n) := Nat.card_pos
    omega
  obtain ⟨I₂, hI₂, hR₂I⟩ := hblock hC.le₂ hC.comp₂
  have hsI := sign_mem_oBlock_of_mem_blockP hw J I₂ hI₂ hJ (hIc hI₂) (hR₂I hC.mem)
  have heven := even_card_of_sign_mem_oBlock hw hK hsI
  rcases comp_cases_of_le_blockP hw hK J I₂ hI₂ hJ (hIc hI₂) hC.le₂ hC.comp₂ hR₂I with
    ⟨hR₂e, hq₂⟩ | ⟨h4, hK3, hq₂, ⟨f₂⟩⟩
  ·
    exfalso
    have h3 := three_le_card_of_isQuasisimple_blockP hw (hIc hI₂) h2 hq₂
    have h4 : 4 ≤ I₂.card := by
      obtain ⟨k, hk⟩ := heven
      omega
    obtain ⟨I₀, hI₀, h3', hI₀w, -⟩ := hNF' hI₂ h3
    obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.1 (by omega : 1 < I₀.card)
    have hs := signGL_pair_mem_oBlock hw (hI₀ ha) (hI₀ hb) hab (hI₀w a ha b hb)
    have hsΩ := oBlock_le_matrixDerived hw h2 I₂ hs
    set y := projH _ (⟨signGL K {a, b}, hsΩ⟩ : matrixDerived (oQ (diagGL hw))) with hy
    have hyR₂ : y ∈ R₂ := hR₂e ▸ ⟨⟨signGL K {a, b}, hsΩ⟩, hs, rfl⟩
    have hab2 : ({a, b} : Finset (Fin d)).card = 2 := Finset.card_pair hab
    have hpc : ({a, b} : Finset (Fin d))ᶜ.Nonempty := by
      rw [← Finset.card_pos]
      have := card_compl_add ({a, b} : Finset (Fin d))
      omega
    have hy2 := orderOf_projH_sign hw hK hsΩ ⟨a, by simp⟩ hpc
    have hxy : x * y = y * x := by
      rw [hx, hy, ← map_mul, ← map_mul]
      congr 1
      exact Subtype.ext (Units.ext (by
        simp only [Subgroup.coe_mul, Units.val_mul, coe_signGL]
        exact signMat_mul_comm J {a, b}))
    have heq := eq_of_involutions hGF2 e₂ (a := ⟨x, hC.mem⟩) (b := ⟨y, hyR₂⟩)
      (by rw [Subgroup.orderOf_mk]; exact hC.orderOf_eq) (by rw [Subgroup.orderOf_mk]; exact hy2)
      (Subtype.ext hxy)
    have hxy' : x = y := congrArg Subtype.val heq
    rcases eq_or_eq_compl_of_projH_sign_eq hw hK hJ hsΩ hxy' with h | h
    ·
      rcases hI₂ with rfl | rfl
      · rw [← h, hab2] at h4; omega
      · exact Finset.mem_compl.1 (hI₀ ha) (h ▸ by simp)
    ·
      rcases hI₂ with rfl | rfl
      · exact Finset.mem_compl.1 (h ▸ (by simp : a ∈ ({a, b} : Finset (Fin d)))) (hI₀ ha)
      · rw [← h, hab2] at h4; omega
  have hO₂ : pPrimeCore 2 R₂ = ⊥ := pPrimeCore_eq_bot_of_center hq₂
    (a := ⟨x, hC.mem⟩) (by rw [Subgroup.orderOf_mk]; exact hC.orderOf_eq) (by
      intro z hz
      have hz' : f₂ z ∈ center SL(2, K) := by
        rw [mem_center_iff]
        intro g
        obtain ⟨g', rfl⟩ := f₂.surjective g
        rw [← map_mul, ← map_mul, (mem_center_iff.1 hz g')]
      apply f₂.injective
      rw [map_pow, sq_eq_one_of_mem_center_SL hz', map_one])
  have hcardK : Nat.card K = p ^ n := by
    have h1 := card_eq_card_pPrimeCore_mul (R := R₂)
    rw [Nat.card_congr e₂.toEquiv] at h1
    rw [hO₂, Subgroup.card_bot, one_mul, Nat.card_congr f₂.toEquiv] at h1
    rw [← hcardGF]
    exact card_eq_of_card_SL_eq h1
  obtain ⟨I₁, hI₁, hR₁I⟩ := hblock hC.le₁ hC.comp₁
  rcases comp_cases_of_le_blockP hw hK J I₁ hI₁ hJ (hIc hI₁) hC.le₁ hC.comp₁ hR₁I with
    ⟨hR₁e, hq₁⟩ | ⟨-, -, -, ⟨f₁⟩⟩
  ·
    have hI12 : I₁ = I₂ᶜ := by
      rcases hI₁ with rfl | rfl <;> rcases hI₂ with h | h
      · exact absurd (hR₁e.trans (eq_of_le_of_isQuasisimple (hR₂I.trans (h ▸ le_rfl))
          (blockP_le_centralizer hw _ _ (Or.inl rfl) hJ) hC.comp₂ hq₁).symm) hR12
      · rw [h, compl_compl]
      · rw [h]
      · exact absurd (hR₁e.trans (eq_of_le_of_isQuasisimple (hR₂I.trans (h ▸ le_rfl))
          (blockP_le_centralizer hw _ _ (Or.inr rfl) hJ) hC.comp₂ hq₁).symm) hR12
    have hcompl := card_compl_add I₂
    have h3 := three_le_card_of_isQuasisimple_blockP hw (hIc hI₁) h2 hq₁
    rcases Nat.lt_or_ge I₁.card 4 with h4' | h4'
    · refine ⟨by rw [hI12] at h3 h4'; omega, hcardK, I₂, hI₂, h4, hR₂I, hI12 ▸ hR₁I⟩
    · exfalso
      obtain ⟨I₀, hI₀, h3', hI₀w, -⟩ := hNF' hI₁ h3
      obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.1 (by omega : 1 < I₀.card)
      have hs := signGL_pair_mem_oBlock hw (hI₀ ha) (hI₀ hb) hab (hI₀w a ha b hb)
      have hsΩ := oBlock_le_matrixDerived hw h2 I₁ hs
      have hpc : ({a, b} : Finset (Fin d))ᶜ.Nonempty := by
        rw [← Finset.card_pos]
        have := card_compl_add ({a, b} : Finset (Fin d))
        have := Finset.card_pair hab
        omega
      have hy2 := orderOf_projH_sign hw hK hsΩ ⟨a, by simp⟩ hpc
      have hO₁ : pPrimeCore 2 R₁ = ⊥ := by
        subst hR₁e
        exact pPrimeCore_eq_bot_of_center hq₁ (a := ⟨_, ⟨⟨signGL K {a, b}, hsΩ⟩, hs, rfl⟩⟩)
          (by rw [← Subgroup.orderOf_coe]; exact hy2)
          (fun z hz => sq_eq_one_of_mem_center_blockP hw hK (hIc hI₁) (hNF' hI₁ h3) hz)
      have hcard₁ : Nat.card R₁ = Nat.card PSL(2, GaloisField p n) := by
        have h1 := card_eq_card_pPrimeCore_mul (R := R₁)
        rw [Nat.card_congr e₁.toEquiv] at h1
        rw [hO₁, Subgroup.card_bot, one_mul] at h1
        exact h1
      have hlt := card_lt_blockP hw hK hK3 (hIc hI₁) h4' (hNF' hI₁ h3)
      have hSL : Nat.card SL(2, K) = Nat.card SL(2, GaloisField p n) := by
        rw [GorensteinWalter.sl2_card_formula, GorensteinWalter.sl2_card_formula, hcardK,
          hcardGF]
      rw [hSL, ← card_PSL_mul_two hGF, ← hcard₁, hR₁e] at hlt
      omega
  · exact (not_SL_of_PSL hGF (by rw [hcardK, hcardGF]) f₁ e₁).elim

end CFSG.ComponentClassification.Burgoyne.C
