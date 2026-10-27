module

public import CFSG.LocalAnalysis.ComponentClassification.GSThmB5bL34Tools
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB5bSmallInv
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB5bLemma513
public import CFSG.LocalAnalysis.ComponentClassification.GSThmBCatalog5L34

public section

namespace CFSG.ComponentClassification.GSThmB

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
open scoped Pointwise commutatorElement

theorem lieModel_of_mulEquiv_ne_zero {G G' : Type} [Group G] [Group G'] (e : G ≃* G')
    {t : Assembly.LowTwoRank.StatedLieTag} {n p f : ℕ} (hn : n ≠ 0)
    (h : Blueprint.LieModel G t n p f) : Blueprint.LieModel G' t n p f := by
  rcases h with ⟨ht, hm⟩ | ⟨h0, -⟩ | ⟨h0, -⟩ | ⟨h0, -⟩
  · exact Or.inl ⟨ht, SectionRank.statedClassicalModel_of_mulEquiv e.symm hm⟩
  all_goals exact absurd h0 hn

theorem comap_center_congr {Y : Type*} [Group Y] {N₁ N₂ : Subgroup Y} [N₁.Normal] [N₂.Normal]
    (h : N₁ = N₂) :
    (center (Y ⧸ N₁)).comap (QuotientGroup.mk' N₁) =
      (center (Y ⧸ N₂)).comap (QuotientGroup.mk' N₂) := by
  subst h
  rfl

theorem nonempty_quotient_center_equiv_zStarBar {H : Type} [Group H] (K : Subgroup H) :
    Nonempty ((OddBar K) ⧸ center (OddBar K) ≃* ZStarBar K) := by
  set N := pPrimeCore 2 ↥K with hN
  set M : Subgroup ↥K := (center (↥K ⧸ N)).comap (QuotientGroup.mk' N) with hM
  have hMeq : Open.fusionZStar ↥K = M :=
    comap_center_congr (fusionOddCore_eq_pPrimeCore ↥K)
  have hNM : N ≤ M := by
    intro y hy
    show QuotientGroup.mk' N y ∈ center (↥K ⧸ N)
    rw [QuotientGroup.mk'_apply, (QuotientGroup.eq_one_iff y).mpr hy]
    exact one_mem _
  have hMN : M.Normal := by rw [← hMeq]; infer_instance
  have hmap : M.map (QuotientGroup.mk' N) = center (↥K ⧸ N) :=
    map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective N) _
  exact ⟨(QuotientGroup.quotientMulEquivOfEq hmap.symm).trans
    ((QuotientGroup.quotientQuotientEquivQuotient N M hNM).trans
      (QuotientGroup.quotientMulEquivOfEq hMeq.symm))⟩

namespace Hyp59

variable {H : Type} [Group H] [Finite H] (h : Hyp59 H)

theorem false_of_row514 (hB1 : ConjFixStatement) (hB6 : SylowKernelStatement)
    (hB7 : EmbedsTQuotStatement) (hCF23 : CFProp23Fusion) (hCF24 : CFProp24c)
    (hCFc : CFProp23Center) (hST : SuzukiTausskyInput) (hP23 : CFProp23L34)
    (hRank : CFL34CoverRank) (hOut : CFL34CoverOut) (hAut : CFAutL2Rank)
    (hT : Nat.card (↥h.T ⧸ h.B.subgroupOf h.T) = 2) (hrow : h.Row514) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hJ, hKa, hZK, hL34⟩ := hrow
  have hZJ := h.toHyp52.center_eq_bot hB1 hB6 hCF23 hCF24
  have hDP := h.toHyp52.D_inf_P_eq_bot hZJ
  obtain ⟨b, hBb, hb, -, hTab, -⟩ := h.index_two_structure hB7 hT
  have hbB : b ∈ h.B := hBb ▸ mem_zpowers b
  have hbP : b ∈ h.P := h.toHyp52.B_le_P hbB
  have hB2 : Nat.card h.B = 2 := by rw [hBb, Nat.card_zpowers, hb]
  have hb2 : b * b = 1 := by rw [← pow_two, ← hb, pow_orderOf_eq_one]
  have ha2 : h.a * h.a = 1 := by rw [← pow_two, ← h.orderOf_a, pow_orderOf_eq_one]
  have hxb := h.conj_x_b hBb hb hTab
  have haSS := h.a_mem_commutator_of_index_two hB7 hT
  have hCN := h.centralizer_b_le hBb hb hKa
  have hZ2 := h.card_center_oddBar_K hB6 hKa hB2 hZK
  have hKB : ∀ {k : H}, k ∈ h.K → k * b = b * k := fun hk =>
    (mem_centralizer_iff.mp ((h.toHyp52.K_le_layer_W.trans h.toHyp52.V_le_centralizer_B) hk) b
      hbB).symm
  obtain ⟨z, hzD, hzS, hz2⟩ := h.toHyp52.exists_involution_D_center
  obtain ⟨g, hgK, y, hyB, hgy⟩ :=
    hP23 H h.toHyp52 ⟨hJ, hKa, hZK, hL34⟩ z hzD hzS hz2
  have hgb : g * b = b * g := hKB hgK
  have hza : z * h.a = h.a * z := h.toHyp52.comm_a (h.toHyp52.D_le_S hzD)
  have hgy' : g⁻¹ * h.a * g = h.a * z * b := by
    rw [hBb] at hyB
    by_cases hy1 : y = 1
    · exfalso
      rw [hy1, mul_one] at hgy
      have hzJ : z ∈ h.J := h.toHyp52.D_le_J hzD
      have hmem : g⁻¹ * h.a * g ∈ h.J ⊔ zpowers h.a := by
        rw [hgy]
        exact mul_mem (mem_sup_right (mem_zpowers _)) (mem_sup_left hzJ)
      have hnot : g⁻¹ * h.a * g ∉ zpowers h.a := by
        rw [hgy]
        intro hm
        have hz : z ∈ zpowers h.a := by
          have := mul_mem (inv_mem (mem_zpowers h.a)) hm
          rwa [inv_mul_cancel_left] at this
        have hzP : z ∈ h.D ⊓ h.P := mem_inf.mpr ⟨hzD, zpowers_le.mpr h.toHyp52.a_mem_P hz⟩
        rw [hDP, mem_bot] at hzP
        rw [hzP, orderOf_one] at hz2
        exact absurd hz2 (by norm_num)
      have hPP := h.toHyp52.inf_conjugate_P_eq_bot hB1 hB6 hCF23 hCF24 hCFc cfSmallInv hmem hnot
      have hbg : b ∈ conjugate h.P g := by
        rw [mem_conjugate_iff, hgb, mul_inv_cancel_right]
        exact hbP
      have := hPP ▸ mem_inf.mpr ⟨hbP, hbg⟩
      have hb1 : b = 1 := mem_bot.mp this
      rw [hb1, orderOf_one] at hb
      exact absurd hb (by norm_num)
    · rwa [eq_of_mem_zpowers_of_orderOf_eq_two hb hyB hy1] at hgy
  set c := h.x * g with hc
  have hcb : c⁻¹ * b * c = h.a * z := by
    have hgb' : g⁻¹ * b * g = b := by rw [mul_assoc, ← hgb, ← mul_assoc, inv_mul_cancel, one_mul]
    calc c⁻¹ * b * c = g⁻¹ * (h.x⁻¹ * b * h.x) * g := by rw [hc]; group
      _ = (g⁻¹ * h.a * g) * (g⁻¹ * b * g) := by rw [hxb]; group
      _ = h.a * z := by rw [hgy', hgb', mul_assoc (h.a * z), hb2, mul_one]
  have hbc : b = c * (h.a * z) * c⁻¹ := by rw [← hcb]; group
  set a' := c * h.a * c⁻¹ with ha'
  have hcomm : ∀ s : H, s * (h.a * z) = (h.a * z) * s → (c * s * c⁻¹) * b = b * (c * s * c⁻¹) := by
    intro s hs
    rw [hbc]
    calc c * s * c⁻¹ * (c * (h.a * z) * c⁻¹) = c * (s * (h.a * z)) * c⁻¹ := by group
      _ = c * ((h.a * z) * s) * c⁻¹ := by rw [hs]
      _ = c * (h.a * z) * c⁻¹ * (c * s * c⁻¹) := by group
  have hSaz : ∀ s ∈ h.S, s * (h.a * z) = (h.a * z) * s := by
    intro s hs
    have h1 : s * h.a = h.a * s := h.toHyp52.comm_a hs
    have h2 : s * z = z * s := hzS s hs
    calc s * (h.a * z) = (s * h.a) * z := by group
      _ = h.a * (s * z) := by rw [h1]; group
      _ = h.a * z * s := by rw [h2]; group
  have haaz : h.a * (h.a * z) = (h.a * z) * h.a := by rw [mul_assoc, ← hza]
  have ha'N : a' ∈ normalizer (h.K : Set H) :=
    hCN (mem_centralizer_singleton_iff.mpr (hcomm _ haaz))
  set S' : Subgroup H := h.S.map (MulAut.conj c).toMonoidHom with hS'
  have hS'N : S' ≤ normalizer (h.K : Set H) := by
    rintro _ ⟨s, hs, rfl⟩
    exact hCN (mem_centralizer_singleton_iff.mpr (hcomm s (hSaz s hs)))
  have ha'SS : a' ∈ ⁅S', S'⁆ := by
    rw [hS', ← map_commutator]
    exact ⟨h.a, haSS, by rw [ha']; rfl⟩
  have hperf : Group.IsPerfect (OddBar h.K) := h.toHyp52.isQuasisimple_K.1
  obtain ⟨eZ⟩ := nonempty_quotient_center_equiv_zStarBar h.K
  have hLie : Blueprint.LieModel ((OddBar h.K) ⧸ center (OddBar h.K)) .PSL 3 2 2 :=
    lieModel_of_mulEquiv_ne_zero eZ.symm (by norm_num) hL34
  set a'' : ↥(normalizer (h.K : Set H)) := ⟨a', ha'N⟩ with ha''
  have ha'2 : (a'' : H) * a'' = 1 := by
    show c * h.a * c⁻¹ * (c * h.a * c⁻¹) = 1
    calc c * h.a * c⁻¹ * (c * h.a * c⁻¹) = c * (h.a * h.a) * c⁻¹ := by group
      _ = 1 := by rw [ha2]; group
  by_cases hinn : oddBarConj h.K a'' ∈ (MulAut.conj : OddBar h.K →* MulAut (OddBar h.K)).range
  ·
    obtain ⟨l, hl⟩ := hinn
    have hsq : a'' * a'' = 1 := Subtype.ext ha'2
    have hl2 : l ^ 2 ∈ center (OddBar h.K) := by
      rw [Subgroup.mem_center_iff]
      intro w
      have h1 : MulAut.conj (l ^ 2) = 1 := by
        rw [map_pow, hl, ← map_pow, pow_two, hsq, map_one]
      have h2 := congrArg (fun φ : MulAut (OddBar h.K) => φ w) h1
      simp only [MulAut.conj_apply, MulAut.one_apply] at h2
      calc w * l ^ 2 = (l ^ 2 * w * (l ^ 2)⁻¹) * l ^ 2 := by rw [h2]
        _ = l ^ 2 * w := by group
    obtain ⟨E, hEl, hE2, hE32⟩ := hRank (OddBar h.K) hperf hZ2 hLie l hl2
    have hEfix : ∀ e ∈ E, oddBarConj h.K a'' e = e := by
      intro e he
      rw [← hl, MulAut.conj_apply]
      have := mem_centralizer_singleton_iff.mp (hEl he)
      rw [← this, mul_inv_cancel_right]
    obtain ⟨E₁, -, hE₁C, hE₁2, hE₁card⟩ := exists_elementary_lift ha'2 hE2 hEfix
    set E₂ : Subgroup H := E₁.map (MulAut.conj c⁻¹).toMonoidHom with hE₂
    have hE₂C : E₂ ≤ centralizer ({h.a} : Set H) := by
      rintro _ ⟨e, he, rfl⟩
      have h1 := mem_centralizer_singleton_iff.mp (hE₁C he)
      rw [mem_centralizer_singleton_iff]
      show c⁻¹ * e * c⁻¹⁻¹ * h.a = h.a * (c⁻¹ * e * c⁻¹⁻¹)
      have h2 : e * (c * h.a * c⁻¹) = (c * h.a * c⁻¹) * e := h1
      calc c⁻¹ * e * c⁻¹⁻¹ * h.a = c⁻¹ * (e * (c * h.a * c⁻¹)) * c := by group
        _ = c⁻¹ * ((c * h.a * c⁻¹) * e) * c := by rw [h2]
        _ = h.a * (c⁻¹ * e * c⁻¹⁻¹) := by group
    have hE₂2 : ∀ e ∈ E₂, e ^ 2 = 1 := by
      rintro _ ⟨e, he, rfl⟩
      rw [← map_pow, hE₁2 e he, map_one]
    have hE₂p : IsPGroup 2 E₂ := fun e => ⟨1, Subtype.ext (by
      rw [pow_one, SubgroupClass.coe_pow, OneMemClass.coe_one]; exact hE₂2 _ e.2)⟩
    have hE₂card : Nat.card E₂ = 32 := by
      rw [hE₂, Subgroup.card_map_of_injective (MulAut.conj c⁻¹).injective, hE₁card, hE32]
    obtain ⟨-, hSyl⟩ := h.toHyp52.S_sylow_centralizer hB1 hB6 hCF23 hCF24 hCFc
    obtain ⟨m, -, hmS⟩ := exists_conjugate_le_of_sylow hSyl hE₂C hE₂p
    have h16 := h.card_le_sixteen hB7 hST hT (hAut (OddBar h.J) hJ) hmS (by
      intro e he
      rw [mem_conjugate_iff] at he
      have := hE₂2 _ he
      have h4 : m * e ^ 2 * m⁻¹ = 1 := by rw [← conj_pow]; exact this
      calc e ^ 2 = m⁻¹ * (m * e ^ 2 * m⁻¹) * m := by group
        _ = 1 := by rw [h4]; group)
    have hcard : Nat.card (conjugate E₂ m) = 32 := by
      rw [← hE₂card]
      exact card_map_of_injective (MulAut.conj m⁻¹).injective
    omega
  ·
    apply hinn
    set I : Subgroup (MulAut (OddBar h.K)) := (MulAut.conj : OddBar h.K →* _).range with hI
    set S'' : Subgroup ↥(normalizer (h.K : Set H)) := S'.subgroupOf (normalizer (h.K : Set H))
      with hS''
    have hS''2 : IsPGroup 2 S'' := by
      have h1 : IsPGroup 2 S' := h.toHyp52.isPGroup_S.map _
      exact h1.comap_subtype
    have hR2 : IsPGroup 2 (S''.map (oddBarConj h.K)) := hS''2.map _
    have hRinn := hOut (OddBar h.K) hperf hZ2 hLie (S''.map (oddBarConj h.K)) hR2
    have hle : ⁅S', S'⁆ ≤ (I.comap (oddBarConj h.K)).map (normalizer (h.K : Set H)).subtype := by
      rw [commutator_le]
      intro s hs t ht
      refine ⟨⁅(⟨s, hS'N hs⟩ : ↥(normalizer (h.K : Set H))), ⟨t, hS'N ht⟩⁆, ?_, rfl⟩
      rw [SetLike.mem_coe, mem_comap, map_commutatorElement]
      exact hRinn _ ⟨_, (mem_subgroupOf.mpr hs : (⟨s, hS'N hs⟩ : ↥(normalizer _)) ∈ S''), rfl⟩
        _ ⟨_, (mem_subgroupOf.mpr ht : (⟨t, hS'N ht⟩ : ↥(normalizer _)) ∈ S''), rfl⟩
    obtain ⟨n, hn, hna⟩ := hle ha'SS
    have : n = a'' := Subtype.ext hna
    rw [← this]
    exact hn

end Hyp59

end CFSG.ComponentClassification.GSThmB
