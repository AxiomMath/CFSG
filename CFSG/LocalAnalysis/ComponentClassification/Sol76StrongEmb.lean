module

public import CFSG.LocalAnalysis.ComponentClassification.Sol78NoStrongEmb
public import CFSG.LocalAnalysis.ComponentClassification.FooteLitElemAb
public import CFSG.LocalAnalysis.ComponentInitial.FourGroupCommuting

public section

namespace CFSG.ComponentClassification.Sol76

open CFSG Subgroup

variable {K : Type*} [Group K]

@[expose] def FourGroupAdj (B C : Subgroup K) : Prop :=
  IsKleinFour B ∧ IsKleinFour C ∧ B ≤ centralizer (C : Set K)

variable [Finite K]

omit [Finite K] in
theorem centralizer_le_of_isStronglyEmbedded {M : Subgroup K} (hM : IsStronglyEmbedded M)
    {s : K} (hs : orderOf s = 2) (hsM : s ∈ M) : centralizer ({s} : Set K) ≤ M := by
  intro g hg
  by_contra hgM
  have hodd := hM.2.2 g hgM
  have hsc : s ∈ conjugate M g := by
    rw [SolAltLit.mem_conjugate_iff_conj, show g * s * g⁻¹ = s by
      rw [mem_centralizer_singleton_iff.mp hg, mul_assoc, mul_inv_cancel, mul_one]]
    exact hsM
  have h1 := orderOf_dvd_natCard (⟨s, hsM, hsc⟩ : ↥(M ⊓ conjugate M g))
  have h0 : orderOf (⟨s, hsM, hsc⟩ : ↥(M ⊓ conjugate M g)) = 2 :=
    (orderOf_injective _ (M ⊓ conjugate M g).subtype_injective _).symm.trans hs
  rw [h0] at h1
  exact (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr h1)

theorem exists_orderOf_eq_two_of_isKleinFour {V : Subgroup K} (hV : IsKleinFour V) :
    ∃ v ∈ V, orderOf v = 2 := by
  have : Nontrivial V := Finite.one_lt_card_iff_nontrivial.mp (by rw [hV.card_four]; norm_num)
  obtain ⟨v, hv⟩ := exists_ne (1 : V)
  have hv1 : (v : K) ≠ 1 := fun h => hv (Subtype.ext h)
  exact ⟨v, v.2, orderOf_eq_prime (FooteLit.sq_eq_one_of_isKleinFour hV v.2) hv1⟩

omit [Finite K] in
theorem isKleinFour_conjugate {V : Subgroup K} (hV : IsKleinFour V) (g : K) :
    IsKleinFour (conjugate V g) := by
  refine FooteLit.isKleinFour_of_card_eq_four ?_ fun x hx => ?_
  · rw [conjugate, Subgroup.card_map_of_injective (MulAut.conj g⁻¹).injective, hV.card_four]
  · obtain ⟨v, hv, rfl⟩ := hx
    rw [← map_pow, FooteLit.sq_eq_one_of_isKleinFour hV hv, map_one]

theorem exists_isKleinFour_of_two_le_pRank (h2 : 2 ≤ CFSG.pRank 2 K) :
    ∃ V : Subgroup K, IsKleinFour V := by
  classical
  rw [SectionRank.pRank_eq_open_pRank_top] at h2
  obtain ⟨E, -, hE, hEcard⟩ := SectionRank.exists_pRank one_lt_two (⊤ : Subgroup K)
  have h4 : 2 < Nat.card E := by
    rw [hEcard]
    calc 2 < 2 ^ 2 := by norm_num
      _ ≤ 2 ^ CFSG.Open.pRank 2 (⊤ : Subgroup K) := Nat.pow_le_pow_right (by norm_num) h2
  have := Fintype.ofFinite ↥E
  rw [Nat.card_eq_fintype_card] at h4
  obtain ⟨a, b, c, hab, hac, hbc⟩ := Fintype.two_lt_card_iff.mp h4
  obtain ⟨x, y, hx1, hy1, hxy⟩ : ∃ x y : E, x ≠ 1 ∧ y ≠ 1 ∧ x ≠ y := by
    by_cases ha : a = 1
    · exact ⟨b, c, fun h => hab (ha.trans h.symm), fun h => hac (ha.trans h.symm), hbc⟩
    · by_cases hb : b = 1
      · exact ⟨a, c, ha, fun h => hbc (hb.trans h.symm), hac⟩
      · exact ⟨a, b, ha, hb, hab⟩
  have hsq : ∀ z ∈ E, z * z = 1 := fun z hz => by rw [← sq]; exact hE.2 z hz
  have hcomm : (x : K) * y = y * x := congrArg Subtype.val (hE.1.is_comm.comm x y)
  have hx1' : (x : K) ≠ 1 := fun h => hx1 (Subtype.ext h)
  have hy1' : (y : K) ≠ 1 := fun h => hy1 (Subtype.ext h)
  have hxy' : (x : K) ≠ y := fun h => hxy (Subtype.ext h)
  refine ⟨LocalAnalysis.ComponentInitial.FourGroup.kleinFourOf (x : K) y (hsq _ x.2)
    (hsq _ y.2) hcomm, FooteLit.isKleinFour_of_card_eq_four
      (LocalAnalysis.ComponentInitial.FourGroup.card_kleinFourOf hx1' hy1' hxy') fun z hz => ?_⟩
  have hzE : z ∈ E := LocalAnalysis.ComponentInitial.FourGroup.kleinFourOf_le x.2 y.2 hz
  exact hE.2 z hzE

theorem isTwoDisconnected_of_isStronglyEmbedded {M : Subgroup K} (hM : IsStronglyEmbedded M)
    (h2 : 2 ≤ CFSG.pRank 2 K) : FooteLit.IsTwoDisconnected K := by
  classical
  obtain ⟨V₀, hV₀⟩ := exists_isKleinFour_of_two_le_pRank h2
  obtain ⟨v, hvV, hv2⟩ := exists_orderOf_eq_two_of_isKleinFour hV₀
  obtain ⟨⟨s, hsM⟩, hs2⟩ := exists_prime_orderOf_dvd_card' (G := M) 2
    (even_iff_two_dvd.mp hM.2.1)
  rw [Subgroup.orderOf_mk] at hs2
  obtain ⟨g, hg⟩ := isConj_iff.mp (Sol78.isConj_of_isStronglyEmbedded hM hs2 hv2)
  set V := conjugate V₀ g with hV
  have hVK : IsKleinFour V := isKleinFour_conjugate hV₀ g
  have hsV : s ∈ V := by
    rw [hV, SolAltLit.mem_conjugate_iff_conj, hg]
    exact hvV
  have hVM : V ≤ M := by
    intro w hw
    refine centralizer_le_of_isStronglyEmbedded hM hs2 hsM ?_
    rw [mem_centralizer_singleton_iff]
    have : IsMulCommutative V := hVK.isMulCommutative
    exact congrArg Subtype.val (this.is_comm.comm ⟨w, hw⟩ ⟨s, hsV⟩)
  have hstep : ∀ B C : Subgroup K, B ≤ M → FourGroupAdj B C → C ≤ M := by
    rintro B C hBM ⟨hB, -, hBC⟩
    obtain ⟨b, hbB, hb2⟩ := exists_orderOf_eq_two_of_isKleinFour hB
    intro c hc
    refine centralizer_le_of_isStronglyEmbedded hM hb2 (hBM hbB) ?_
    rw [mem_centralizer_singleton_iff]
    exact (mem_centralizer_iff.mp (hBC hbB)) c hc
  obtain ⟨x, hxM⟩ : ∃ x : K, x ∉ M := by
    by_contra h
    push Not at h
    exact hM.1 (eq_top_iff.mpr fun y _ => h y)
  refine ⟨V, conjugate V x, hVK, isKleinFour_conjugate hVK x, fun hchain => ?_⟩
  have hreach : ∀ C : Subgroup K, Relation.ReflTransGen FourGroupAdj V C → C ≤ M := by
    intro C hC
    induction hC with
    | refl => exact hVM
    | tail _ hBC ih => exact hstep _ _ ih hBC
  have hxV : conjugate V x ≤ M := hreach _ hchain
  obtain ⟨w, hwV, hw2⟩ := exists_orderOf_eq_two_of_isKleinFour (isKleinFour_conjugate hVK x)
  have hwc : w ∈ conjugate M x := by
    rw [SolAltLit.mem_conjugate_iff_conj]
    rw [SolAltLit.mem_conjugate_iff_conj] at hwV
    exact hVM hwV
  have h1 := orderOf_dvd_natCard (⟨w, hxV hwV, hwc⟩ : ↥(M ⊓ conjugate M x))
  have h0 : orderOf (⟨w, hxV hwV, hwc⟩ : ↥(M ⊓ conjugate M x)) = 2 :=
    (orderOf_injective _ (M ⊓ conjugate M x).subtype_injective _).symm.trans hw2
  rw [h0] at h1
  exact (Nat.not_even_iff_odd.mpr (hM.2.2 x hxM)) (even_iff_two_dvd.mpr h1)

theorem isTwoDisconnected_of_hasStronglyEmbedded (h : FooteLit.HasStronglyEmbedded K)
    (h2 : 2 ≤ CFSG.pRank 2 K) : FooteLit.IsTwoDisconnected K := by
  obtain ⟨M, hM⟩ := h
  exact isTwoDisconnected_of_isStronglyEmbedded hM h2

omit [Finite K] in
theorem map_conjugate_mulEquiv {K' : Type*} [Group K'] (e : K ≃* K') (M : Subgroup K) (a : K) :
    (conjugate M a).map e.toMonoidHom = conjugate (M.map e.toMonoidHom) (e a) := by
  rw [conjugate, conjugate, Subgroup.map_map, Subgroup.map_map]
  congr 1
  ext x
  simp

omit [Finite K] in
theorem hasStronglyEmbedded_of_mulEquiv {K' : Type*} [Group K'] (e : K ≃* K')
    (h : FooteLit.HasStronglyEmbedded K) : FooteLit.HasStronglyEmbedded K' := by
  obtain ⟨M, hMtop, hMeven, hMg⟩ := h
  refine ⟨M.map e.toMonoidHom, ?_, ?_, fun g hg => ?_⟩
  · intro htop
    apply hMtop
    have := congrArg (Subgroup.comap e.toMonoidHom) htop
    rwa [Subgroup.comap_map_eq_self_of_injective e.injective, Subgroup.comap_top] at this
  · rwa [Subgroup.card_map_of_injective e.injective]
  · obtain ⟨a, rfl⟩ := e.surjective g
    have ha : a ∉ M := fun haM => hg ⟨a, haM, rfl⟩
    have hmap : (M ⊓ conjugate M a).map e.toMonoidHom =
        M.map e.toMonoidHom ⊓ conjugate (M.map e.toMonoidHom) (e a) := by
      rw [Subgroup.map_inf_eq _ _ _ e.injective, map_conjugate_mulEquiv]
    rw [← hmap, Subgroup.card_map_of_injective e.injective]
    exact hMg a ha

end CFSG.ComponentClassification.Sol76
