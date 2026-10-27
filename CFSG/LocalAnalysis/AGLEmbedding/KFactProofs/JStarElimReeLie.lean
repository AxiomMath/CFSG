module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.JStarElimLieGeneric
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.JStarElimLieProfile
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ReeAut
public import CFSG.LocalAnalysis.AGLEmbedding.UnitaryFacts
public import CFSG.LocalAnalysis.AGLEmbedding.CaseTwoDefs

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.LieType.Ree

theorem reeTarget_facts
    

    {d₀ : TauCeti.ValidLieTypeIndex} (hd₀ : IsReeGTwoIndex 3 d₀) :
    ∃ a : ℕ, 1 ≤ a ∧ d₀.1.fieldExponent = 2 * a + 1 ∧
      Nonempty (CatGroup d₀ ≃* ↥(ReeTag.G2.reeGamma (GaloisField 3 (2 * a + 1)) a)) ∧
      commutator (CatGroup d₀) = ⊤ := by
  obtain ⟨a, ha, hfe, ⟨eT⟩⟩ := ReeModel.exists_equiv_reeGamma hd₀ ⟨MulEquiv.refl _⟩
  refine ⟨a, ha, hfe, ⟨eT⟩, ?_⟩
  have hK : Nat.card (GaloisField 3 (2 * a + 1)) = 3 ^ (2 * a + 1) :=
    GaloisField.card 3 (2 * a + 1) (by omega)
  have hperf := (ReeTag.ree_generic_fixed_group_perfect .G2 a ha (GaloisField 3 (2 * a + 1)) hK).2.1
  have : Group.IsPerfect ↥(ReeTag.G2.reeGamma (GaloisField 3 (2 * a + 1)) a) :=
    Group.isPerfect_def.mpr hperf
  have : Group.IsPerfect (CatGroup d₀) :=
    Group.IsPerfect.ofSurjective (f := eT.symm.toMonoidHom) eT.symm.surjective
  exact Group.isPerfect_def.mp this


theorem kFactJStarElimReeLie_of (hSch : KFactCatalogSchreier) (hRee : KFactReeOrder)
    (hKU2 : KFactUnitarySylowStructure)
    

    : KFactJStarElimReeLie := by
  intro d₀ hd₀ L _ _ hs d hd hnR ⟨e⟩ hdata
  have hn3 : 3 ≤ d₀.1.fieldExponent := hd₀.three_le_fieldExponent
  obtain ⟨a₀, ha₀, hfe, ⟨eT⟩, hperf⟩ := reeTarget_facts hd₀
  have hTfin : Finite (CatGroup d₀) := by
    obtain ⟨A, J, -, -, -, φ, hφ, -⟩ := hdata
    exact Finite.of_surjective φ hφ
  have hcardT := hRee (CatGroup d₀) d₀ hd₀ ⟨MulEquiv.refl _⟩
  generalize hn : d₀.1.fieldExponent = n at *
  have hT3 : 3 ^ (3 * n) ∣ Nat.card (CatGroup d₀) := by
    rw [hcardT]
    exact Dvd.dvd.mul_right (Dvd.dvd.mul_right (by rw [← pow_mul, mul_comm]) _) _
  have hTnc : ∃ a b : CatGroup d₀, a * b ≠ b * a := by
    by_contra hcon
    push Not at hcon
    have : IsMulCommutative (CatGroup d₀) := ⟨⟨hcon⟩⟩
    have : Group.IsPerfect (CatGroup d₀) := Group.isPerfect_def.mpr hperf
    have hnt : Nontrivial (CatGroup d₀) := by
      refine Finite.one_lt_card_iff_nontrivial.mp ?_
      have h1 := Nat.le_of_dvd Nat.card_pos hT3
      have h2 : 1 < 3 ^ (3 * n) := Nat.one_lt_pow (by omega) (by norm_num)
      omega
    exact Group.IsPerfect.not_isMulCommutative (CatGroup d₀) ‹_›
  have hcat : Open.IsCatalogGroup L :=
    isCatalogGroup_of_list (p := 3) (by norm_num) (Or.inl ⟨d, hd, ⟨e⟩⟩)
  obtain ⟨hdvd, hp⟩ :=
    hdata.orderTest_of_schreier_perfect hperf hTnc (fun hnc => hSch L hs hnc hcat)
  rcases lieListProfile hRee (p := 3) (by norm_num) hd e with
    ⟨m, hm, -, hN⟩ | ⟨a, ha, hUd, -, hN⟩ | ⟨-, -, -, hRd, -, -⟩ | hN | ⟨-, hN, -, -, -⟩ | ⟨h35, -⟩
  ·
    rw [hN, hcardT] at hdvd
    exact not_ree_order_dvd_psl hn3 hm hdvd (hp m (by rw [hN]; exact Dvd.intro _ rfl))
  ·
    have hLa : 3 ^ (3 * a) ∣ Nat.card L := by
      rw [hN]
      have := pow_dvd_ordTwistedA_two (3 ^ a) (Nat.one_le_pow _ _ (by norm_num))
      rwa [← pow_mul, mul_comm] at this
    have hpb := hp (3 * a) hLa
    rw [hN, hcardT] at hdvd
    have han : a = n := eq_of_ree_order_dvd_ordTwistedA_two hn3 ha hdvd hpb
    subst han
    have hnc₀ : ∃ x y : L, x * y ≠ y * x := nonabelian_of_simple_of_sq_dvd Nat.prime_three
      ((pow_dvd_pow 3 (by omega : 2 ≤ 3 * a)).trans hLa)
    have hZ : Subgroup.center L = ⊥ := center_bot_of_simple_nonab hnc₀
    obtain ⟨U, D, D₀, hDU, ⟨f⟩, hcard⟩ := hdata.exists_inner_copy hZ hLa
    have hD3 : ∀ x ∈ D, x ^ 3 = 1 := by
      have hDp : IsPGroup 3 D := U.isPGroup'.to_le hDU
      have hD0p : IsPGroup 3 D₀ := hDp.of_equiv f.symm
      obtain ⟨Q, hQ⟩ := hD0p.exists_le_sylow
      have hexp := (hKU2 L 3 d (by norm_num) hUd ⟨e⟩ Q).2.2.1
      intro x hx
      have hy : (f.symm ⟨x, hx⟩ : L) ^ 3 = 1 := hexp _ (hQ (f.symm ⟨x, hx⟩).2)
      have hy' : (f.symm ⟨x, hx⟩) ^ 3 = 1 := Subtype.ext hy
      have := congrArg f hy'
      rw [map_pow, MulEquiv.apply_symm_apply, map_one] at this
      simpa using congrArg Subtype.val this
    have hK : Nat.card (GaloisField 3 (2 * a₀ + 1)) = 3 ^ (2 * a₀ + 1) :=
      GaloisField.card 3 (2 * a₀ + 1) (by omega)
    have hbound := (ReeModel.card_le_of_pow_three_le_sylow hK eT U D hDU hD3).1
    rw [← hfe] at hbound
    have hU3 : 3 ^ (3 * a) ∣ Nat.card U := U.pow_dvd_card_of_pow_dvd_card hT3
    have hUle := Nat.le_of_dvd Nat.card_pos hU3
    have h1 : 3 ^ (3 * a) * Nat.card U ∣ 3 ^ (3 * a) * (a * Nat.card D) := by
      have : Nat.card U * 3 ^ (3 * a) = 3 ^ (3 * a) * Nat.card U := mul_comm _ _
      rw [this] at hcard
      calc 3 ^ (3 * a) * Nat.card U ∣ 3 ^ (3 * a) * a * Nat.card D := hcard
        _ = 3 ^ (3 * a) * (a * Nat.card D) := by ring
    have h2 : Nat.card U ∣ a * Nat.card D :=
      Nat.dvd_of_mul_dvd_mul_left (pow_pos (by norm_num) _) h1
    have h3 : Nat.card U ≤ a * Nat.card D := Nat.le_of_dvd (by
      have := Nat.card_pos (α := D)
      have := (show 0 < a by omega)
      positivity) h2
    have h4 : 3 ^ (3 * a) ≤ a * (3 ^ a) ^ 2 := by
      calc 3 ^ (3 * a) ≤ Nat.card U := hUle
        _ ≤ a * Nat.card D := h3
        _ ≤ a * (3 ^ a) ^ 2 := Nat.mul_le_mul_left _ hbound
    have h5 : 3 ^ (3 * a) = 3 ^ a * (3 ^ a) ^ 2 := by
      rw [← pow_mul, ← pow_add]; ring_nf
    have h6 : a < 3 ^ a := Nat.lt_pow_self (by norm_num)
    rw [h5] at h4
    have h7 : 0 < (3 ^ a) ^ 2 := by positivity
    nlinarith
  · exact absurd hRd hnR
  · have h4 := le_of_pow_dvd_ordBC_two Nat.prime_three (hN ▸ hT3.trans hdvd)
    omega
  · exact not_three_pow_dvd_chev_three hN hn3 (hT3.trans hdvd)
  · omega

end CFSG.AGLEmbedding
