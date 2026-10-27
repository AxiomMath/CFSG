module

public import CFSG.LocalAnalysis.OddStandard.AltStdCycTwoTwoExGlue
public import CFSG.LocalAnalysis.OddStandard.AltStdSecOverBase
public import CFSG.LocalAnalysis.OddStandard.AltStdSecOverSwap

public section

namespace CFSG.OddStandard.AltStdCycTwo.Two.Exact

open Subgroup Equiv Equiv.Perm AltStdBal AltStdSec AltStdSec.Wreath

variable {G : Type} [Group G] [Finite G] {L Q : Subgroup G} {n : ℕ} {z u : G}

section CaseII

theorem swapData_of_caseII_of_cent (T : Shape G L Q n z u) (θ : L ≃* alternatingGroup (Fin n))
    (hC : centralizer (L : Set G) ⊓ centralizer ({z} : Set G) = Q)
    (hII : CaseII θ T.hn (L ⊔ zpowers u) z) : Nonempty (SwapData z n) := by
  have hbij := rhoSwap_bijective T θ
  have hSN := T.le_normalizer
  let ι : Perm (Fin n) ≃* (L ⊔ zpowers u : Subgroup G) :=
    (MulEquiv.ofBijective (rhoSwap T θ) hbij).symm
  have key : ∀ (x : (L ⊔ zpowers u : Subgroup G)) (τ : Perm (Fin n)),
      ι τ = x ↔ τ = rhoSwap T θ x := fun x τ => MulEquiv.symm_apply_eq _
  refine ⟨⟨L ⊔ zpowers u, ι, centralizer_eq_of_cent T hC, T.zpowers_inf, ?_⟩⟩
  ext a
  rw [hII a]
  constructor
  · rintro ⟨haS, haN, hsw⟩
    refine ⟨rhoSwap T θ ⟨a, haS⟩, hsw, ?_⟩
    exact congrArg Subtype.val ((key ⟨a, haS⟩ _).2 rfl).symm
  · rintro ⟨τ, hτ, rfl⟩
    refine ⟨(ι τ).2, hSN (ι τ).2, ?_⟩
    have h1 : rho θ T.hn ⟨(ι τ : G), hSN (ι τ).2⟩ = τ := ((key (ι τ) τ).1 rfl).symm
    rw [h1]
    exact hτ

theorem false_of_caseII_or_of_cent (T : Shape G L Q n z u) (θ : L ≃* alternatingGroup (Fin n))
    (hC : centralizer (L : Set G) ⊓ centralizer ({z} : Set G) = Q)
    (hII : CaseII θ T.hn (L ⊔ zpowers u) z ∨ CaseII θ T.hn (L ⊔ zpowers (u * z)) z) : False := by
  have := T.std.simple
  rcases hII with h1 | h1
  · obtain ⟨D⟩ := swapData_of_caseII_of_cent T θ hC h1
    exact false_of_swapData T.std.nonab T.hn T.cyc.order D
  · obtain ⟨D⟩ := swapData_of_caseII_of_cent T.mul_z θ hC h1
    exact false_of_swapData T.std.nonab T.hn T.cyc.order D

end CaseII

section Unique

theorem caseIIIAt_of_wreathPair_of_exact
    (htri : ExactShapeTrichotomy) (hS : StandardSetting G L) (hex : ExactShape z L n)
    (e : L ≃* alternatingGroup (Fin n)) (hn : 12 ≤ n) {H : Subgroup G}
    (hH : WreathPair L z n H) {S : Finset (Fin n)} (hS3 : S.card = 3) : CaseIIIAt e z S := by
  classical
  have ht : z ∈ centralizer (corr (X := G) e (altSub S) : Set G) :=
    t_mem_centralizer_corr (X := G) e hex (altSub S)
  have hSc : 5 ≤ n - S.card := by omega
  have hsec := exactShape_section_three hex e hS3 hSc ht
  have hKcat : CFSG.SectionRank.IsKGroupCat (Sec G (corr (X := G) e (altSub S))) :=
    isKGroupCat_sec (isKGroupCat_of_kProper hS.kProper)
      (centralizer_ne_top_of_exists_ne_one hS (exists_ne_one_of_card_ge_three e (by omega)))
  have hO := oddCore_sec_eq_bot (corr (X := G) e (altSub S))
  obtain ⟨f₁, f₂, hf₁, hf₂, hcomm, hswap⟩ := exists_sec_pair e (by omega) hH hS3 ht
  obtain ⟨eB⟩ := exists_equiv_corr_altSub (X := G) e Sᶜ
  have hm : Sᶜ.card = n - S.card := card_compl_fin S
  have hcardB : Nat.card ↥(corr (X := G) e (altSub Sᶜ)) = (n - S.card).factorial / 2 := by
    rw [card_eq_of_equiv_alt (by omega) eB, hm]
  have hcen : center ↥(corr (X := G) e (altSub Sᶜ)) = ⊥ := center_eq_bot_of_alt (by omega) eB
  let Φ := f₁.noncommCoprod f₂ (fun a b => hcomm a b)
  have hΦ : Function.Injective Φ := by
    rw [injective_iff_map_eq_one]
    rintro ⟨a, b⟩ hab
    have hab' : f₁ a * f₂ b = 1 := hab
    have h2b : f₁ a = f₂ b⁻¹ := by
      rw [map_inv]
      exact eq_inv_of_mul_eq_one_left hab'
    have hacen : a ∈ center ↥(corr (X := G) e (altSub Sᶜ)) := by
      rw [Subgroup.mem_center_iff]
      intro g
      apply hf₁
      rw [map_mul, map_mul, h2b]
      exact hcomm g b⁻¹
    rw [hcen, Subgroup.mem_bot] at hacen
    have hb1 : f₂ b = 1 := by
      have := hab'
      rw [hacen, map_one, one_mul] at this
      exact this
    exact Prod.ext hacen (hf₂ (hb1.trans (map_one f₂).symm))
  have hdvd : (n - S.card).factorial / 2 * ((n - S.card).factorial / 2) ∣
      Nat.card (Sec G (corr (X := G) e (altSub S))) := by
    have := Subgroup.card_dvd_of_injective Φ hΦ
    rwa [Nat.card_prod, hcardB] at this
  rcases htri _ _ _ (n - S.card) (by omega) hKcat hO hsec with h1 | h2 | h3 | h4
  · exfalso
    have hff : ∀ b, f₂ b = f₁ b := by
      intro b
      rw [hswap b]
      have := Subgroup.mem_center_iff.1 h1 (f₁ b)
      rw [← this]
      exact mul_inv_cancel_right _ _
    obtain ⟨a, b, hab⟩ := exists_noncomm_of_alt (by omega) eB
    apply hab
    apply hf₁
    rw [map_mul, map_mul]
    have := hcomm a b
    rwa [hff b] at this
  · exact ⟨ht, h2⟩
  · exfalso
    obtain ⟨e', -⟩ := h3
    have hc : Nat.card (Sec G (corr (X := G) e (altSub S))) = (n - S.card + 2).factorial := by
      rw [← Nat.card_congr e'.toEquiv, Nat.card_eq_fintype_card, Fintype.card_perm,
        Fintype.card_fin]
    rw [hc] at hdvd
    exact not_dvd_sq_factorial_div_two_of_perm (by omega) hdvd
  · exfalso
    obtain ⟨hm10, W, -, hWi, -, ⟨eW⟩⟩ := h4
    have hcardW : Nat.card (Sec G (corr (X := G) e (altSub S))) = 546061824000000 := by
      have h1 := Subgroup.card_mul_index W
      rw [hWi, Nat.card_congr eW.toEquiv, CFSG.Sporadic.HN.card_HN] at h1
      omega
    rw [hcardW, hm10] at hdvd
    revert hdvd
    norm_num [Nat.factorial]

theorem wreathPair_unique_of_exact (htri : ExactShapeTrichotomy)
    (hS : StandardSetting G L) (hex : ExactShape z L n) (hn : 12 ≤ n) {H₁ H₂ : Subgroup G}
    (h₁ : WreathPair L z n H₁) (h₂ : WreathPair L z n H₂) :
    H₂ = H₁ ∨ H₂ = H₁.map (MulAut.conj z).toMonoidHom := by
  obtain ⟨e⟩ := hex.iso
  let S₀ : Finset (Fin n) := {⟨0, by omega⟩, ⟨1, by omega⟩, ⟨2, by omega⟩}
  have hS₀ : S₀.card = 3 := by
    simp only [S₀]
    rw [Finset.card_insert_of_notMem, Finset.card_pair]
    · simp [Fin.ext_iff]
    · simp [Fin.ext_iff]
  exact wreath_unique_of_caseIII_root hex e (by omega) hS₀
    (caseIIIAt_of_wreathPair_of_exact htri hS hex e hn h₁ hS₀) h₁ h₂

end Unique

section Over

theorem centralizer_le_subStab_of_cent
    (htri : ExactShapeTrichotomy) (T : Shape G L Q n z u)
    (hC : centralizer (L : Set G) ⊓ centralizer ({z} : Set G) = Q) (hn : 12 ≤ n)
    {H : Subgroup G} (hH : WreathPair L z n H) :
    centralizer ({z} : Set G) ≤ subStab ({H, cjSub z H} : Set (Subgroup G)) := by
  intro x hx
  have hz2 := T.cyc.mul_self
  have hxz : x * z = z * x := mem_centralizer_singleton_iff.1 hx
  have hxL : cjSub x L = L := cjSub_eq_of_mem_normalizer (cent_le_normalizer T.std T.cyc hx)
  have hzx : x * z * x⁻¹ = z := by rw [hxz]; group
  have hH₂ : WreathPair L z n (cjSub x H) := by
    have := hH.conjugate x⁻¹
    simp only [inv_inv] at this
    have e1 : CFSG.conjugate L x⁻¹ = cjSub x L := by simp [CFSG.conjugate, cjSub]
    have e2 : CFSG.conjugate H x⁻¹ = cjSub x H := by simp [CFSG.conjugate, cjSub]
    rw [e1, e2, hzx, hxL] at this
    exact this
  have hne : H ≠ cjSub z H := hH.ne_cjSub (by omega)
  have hu := wreathPair_unique_of_exact htri T.std (exactShape_of_cent T.toBase hC) hn hH hH₂
  rw [mem_subStab_pair_iff hne]
  have hxz' : cjSub x (cjSub z H) = cjSub z (cjSub x H) := by
    rw [← cjSub_mul, ← cjSub_mul, hxz]
  rcases hu with h1 | h1
  · left
    refine ⟨h1, ?_⟩
    rw [hxz', h1]
  · right
    have h1' : cjSub x H = cjSub z H := h1
    refine ⟨h1', ?_⟩
    rw [hxz', h1', ← cjSub_mul, hz2, cjSub_one]

theorem false_of_conj_fixes_of_cent (T : Shape G L Q n z u) (θ : L ≃* alternatingGroup (Fin n))
    (hC : centralizer (L : Set G) ⊓ centralizer ({z} : Set G) = Q) (hn : 11 ≤ n)
    {H : Subgroup G} (hH : WreathPair L z n H) (g : G)
    (hwH : cjSub (g⁻¹ * z * g) H = H)
    (hwH' : cjSub (g⁻¹ * z * g) (cjSub z H) = cjSub z H) : False := by
  have hz2 := T.cyc.mul_self
  have hw2 : (g⁻¹ * z * g) * (g⁻¹ * z * g) = 1 := by
    calc (g⁻¹ * z * g) * (g⁻¹ * z * g) = g⁻¹ * (z * z) * g := by group
      _ = 1 := by rw [hz2]; group
  by_cases hD : ∃ a ∈ H, ∃ b ∈ cjSub z H, g⁻¹ * z * g = a * b
  · obtain ⟨a, ha, b, ⟨b₀, hb₀, rfl⟩, hab⟩ := hD
    obtain ⟨e⟩ := hH.iso
    have hc : WConfig H z := hH.wconfig (by omega) hz2
    have hJ : J (g⁻¹ * z * g) :=
      hc.J_of_mem_prodSub e (by omega) (le_refl H)
        ⟨a, ha, b₀, hb₀, by simpa [Phi, MulAut.conj_apply] using hab⟩ hw2
    exact not_J_z T.std θ T.hn T.cyc T.card ((J_conj g⁻¹).1 (by rw [inv_inv]; exact hJ))
  · push Not at hD
    exact false_of_fixes_pair hn hH hw2 (fun a ha b hb => hD a ha b hb) hwH hwH'
      (by rw [card_centralizer_conj, card_centralizer_eq_of_cent T hC])

theorem mem_subStab_of_swap_of_cent (htri : ExactShapeTrichotomy)
    (T : Shape G L Q n z u) (θ : L ≃* alternatingGroup (Fin n))
    (hC : centralizer (L : Set G) ⊓ centralizer ({z} : Set G) = Q) (hn : 12 ≤ n)
    {H : Subgroup G} (hH : WreathPair L z n H) {g : G}
    (hg1 : cjSub (g⁻¹ * z * g) H = cjSub z H) (hg2 : cjSub (g⁻¹ * z * g) (cjSub z H) = H) :
    g ∈ subStab ({H, cjSub z H} : Set (Subgroup G)) := by
  have hz2 := T.cyc.mul_self
  set w := g⁻¹ * z * g with hw
  have hw2 : w * w = 1 := by
    calc w * w = g⁻¹ * (z * z) * g := by rw [hw]; group
      _ = 1 := by rw [hz2]; group
  have hS' : StandardSetting G (CFSG.conjugate L g) :=
    ⟨T.std.simple, T.std.nonab, T.std.kProper,
      Solomon75.standardComponentIsStandard_conjugate g T.std.standard⟩
  have hex' : ExactShape w (CFSG.conjugate L g) n := by
    have h1 := exactShape_map (exactShape_of_cent T.toBase hC) (MulAut.conj g⁻¹)
    rw [MulAut.conj_apply, inv_inv] at h1
    exact h1
  obtain ⟨eH⟩ := hH.iso
  have hcardL : Nat.card (CFSG.conjugate L g) ≤ Nat.card H := by
    rw [card_conjugate_eq, Nat.card_congr θ.toEquiv, Nat.card_congr eH.toEquiv]
  have hcomm : ⁅centralizer ({w} : Set G), centralizer ({w} : Set G)⁆ ≤ CFSG.conjugate L g :=
    commutator_centralizer_conj_le (commutator_centralizer_le_of_cent T.toBase θ hC) g
  have hHw : WreathPair (CFSG.conjugate L g) w n H :=
    wreathPair_of_swap hH (by omega) hw2 hg1 hcomm hcardL
  have hHg : WreathPair (CFSG.conjugate L g) w n (CFSG.conjugate H g) := hH.conjugate g
  have hu := wreathPair_unique_of_exact htri hS' hex' hn hHw hHg
  have hne : H ≠ cjSub z H := hH.ne_cjSub (by omega)
  have key : cjSub g⁻¹ H = H ∨ cjSub g⁻¹ H = cjSub z H := by
    rcases hu with h1 | h1
    · exact Or.inl h1
    · right
      have : cjSub g⁻¹ H = cjSub w H := h1
      rw [this, hg1]
  have hgz : g⁻¹ * z = w * g⁻¹ := by rw [hw]; group
  have hconj : cjSub g⁻¹ (cjSub z H) = cjSub w (cjSub g⁻¹ H) := by
    rw [← cjSub_mul, ← cjSub_mul, hgz]
  have hmem : g⁻¹ ∈ subStab ({H, cjSub z H} : Set (Subgroup G)) := by
    rw [mem_subStab_pair_iff hne]
    rcases key with k1 | k1
    · left
      refine ⟨k1, ?_⟩
      rw [hconj, k1, hg1]
    · right
      refine ⟨k1, ?_⟩
      rw [hconj, k1, hg2]
  simpa using Subgroup.inv_mem _ hmem

theorem wreathOvergroup_of_cent (htri : ExactShapeTrichotomy)
    (T : Shape G L Q n z u) (θ : L ≃* alternatingGroup (Fin n))
    (hC : centralizer (L : Set G) ⊓ centralizer ({z} : Set G) = Q) (hn : 12 ≤ n) :
    ∀ H : Subgroup G, WreathPair L z n H →
      ∃ (M : Subgroup G) (hCM : centralizer ({z} : Set G) ≤ M)
        (χ : M →* Multiplicative (ZMod 2)),
        (∀ g : G, g⁻¹ * z * g ∈ M → ∃ m ∈ M, g⁻¹ * z * g = m⁻¹ * z * m) ∧
          χ ⟨z, hCM (mem_centralizer_singleton_iff.2 rfl)⟩ ≠ 1 := by
  intro H hH
  have hne : H ≠ cjSub z H := hH.ne_cjSub (by omega)
  have hCM := centralizer_le_subStab_of_cent htri T hC hn hH
  refine ⟨subStab ({H, cjSub z H} : Set (Subgroup G)), hCM, pairChar H (cjSub z H) hne, ?_, ?_⟩
  · intro g hg
    rcases (mem_subStab_pair_iff hne).1 hg with ⟨hg1, hg2⟩ | ⟨hg1, hg2⟩
    · exact (false_of_conj_fixes_of_cent T θ hC (by omega) hH g hg1 hg2).elim
    · exact ⟨g, mem_subStab_of_swap_of_cent htri T θ hC hn hH hg1 hg2, rfl⟩
  · intro h1
    have h2 := (pairChar_eq_one_iff hne).1 h1
    exact hH.cjSub_ne (by omega) h2

theorem false_of_dichotomy_of_cent (htri : ExactShapeTrichotomy)
    (T : Shape G L Q n z u) (θ : L ≃* alternatingGroup (Fin n))
    (hC : centralizer (L : Set G) ⊓ centralizer ({z} : Set G) = Q) (hn : 12 ≤ n)
    (hdich : CaseII θ T.hn (L ⊔ zpowers u) z ∨ CaseII θ T.hn (L ⊔ zpowers (u * z)) z ∨
      ∃ H : Subgroup G, WreathPair L z n H) : False := by
  rcases hdich with h1 | h1 | ⟨H, hH⟩
  · exact false_of_caseII_or_of_cent T θ hC (Or.inl h1)
  · exact false_of_caseII_or_of_cent T θ hC (Or.inr h1)
  · obtain ⟨M, hCM, χ, hfus, hχ⟩ := wreathOvergroup_of_cent htri T θ hC hn H hH
    have := T.std.simple
    exact false_of_fixedPoint_thompson T.std.nonab T.cyc.order hCM hfus
      (A := Multiplicative (ZMod 2))
      ((Nat.card_congr Multiplicative.toAdd).trans (Nat.card_zmod 2)) χ hχ

end Over

end CFSG.OddStandard.AltStdCycTwo.Two.Exact
