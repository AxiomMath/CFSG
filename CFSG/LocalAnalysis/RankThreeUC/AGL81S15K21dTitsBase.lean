module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15K21dStmt
public import CFSG.Quasithin.H13.NQCatBNG2
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanParabHub

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15

namespace K21dTitsProof

open CFSG.Quasithin.H13 CFSG.QuasithinUnique

theorem isSylowTwoOf_of_isSylowOf_two {S : Type} [Group S] [Finite S] {U : Subgroup S}
    (h : CFSG.ABGLocalTools.IsSylowOf 2 U ⊤) : IsSylowTwoOf U ⊤ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact CFSG.ABGLocalTools.isSylowOf_iff.1 h

theorem eq_one_of_cube_of_inv_sq_mem {S : Type} [Group S] {U : Subgroup S} (hU : IsPGroup 2 U)
    {e : S} (h3 : e ^ 3 = 1) (hmem : e⁻¹ * e⁻¹ ∈ U) : e = 1 := by
  have hee : e⁻¹ * e⁻¹ = e := by
    calc e⁻¹ * e⁻¹ = e⁻¹ * e⁻¹ * e ^ 3 := by rw [h3, mul_one]
      _ = e := by group
  rw [hee] at hmem
  obtain ⟨k, hk⟩ := hU ⟨e, hmem⟩
  have hk' : e ^ 2 ^ k = 1 := congrArg Subtype.val hk
  have hcop : Nat.Coprime (2 ^ k) 3 := Nat.Coprime.pow_left _ (by norm_num)
  exact orderOf_eq_one_iff.1 (Nat.eq_one_of_dvd_coprimes hcop (orderOf_dvd_of_pow_eq_one hk')
    (orderOf_dvd_of_pow_eq_one h3))

theorem k21dGeomAt_of_solvOver {S : Type} [Group S] [Finite S]
    (h : ∀ U : Subgroup S, CFSG.ABGLocalTools.IsSylowOf 2 U ⊤ → NQCat.SolvOver S U) :
    K21dGeomAt S := by
  intro U D E hU hUD hD hED hE hE9 ⟨u, hu, hinv⟩
  exfalso
  have hU2 : IsSylowTwoOf U ⊤ := isSylowTwoOf_of_isSylowOf_two hU
  have hDN : D ≤ Subgroup.normalizer (U : Set S) := h U hU D hUD hD
  have hEne : E ≠ ⊥ := fun hb => by rw [hb] at hE9; simp at hE9
  obtain ⟨⟨e, he⟩, hne⟩ := (Subgroup.ne_bot_iff_exists_ne_one).1 hEne
  have he1 : e ≠ 1 := fun h1 => hne (Subtype.ext h1)
  refine he1 (eq_one_of_cube_of_inv_sq_mem hU2.2.1 (hE.2 e he) ?_)
  have hc : e * u⁻¹ * e⁻¹ ∈ U :=
    (Subgroup.mem_normalizer_iff.1 (hDN (hED he)) u⁻¹).1 (inv_mem hu.1)
  have h2 := mul_mem hu.1 hc
  have h3 : u * (e * u⁻¹ * e⁻¹) = e⁻¹ * e⁻¹ := by
    calc u * (e * u⁻¹ * e⁻¹) = (u * e * u⁻¹) * e⁻¹ := by group
      _ = e⁻¹ * e⁻¹ := by rw [hinv e he]
  rwa [h3] at h2

section BorelTits

open CFSG.LieType.Universal CFSG.LieType.CurtisTits CFSG.LieType.RootSystem CFSG.LieType.Steinberg
  CFSG.AGLEmbedding.ParabHub

theorem solvOver_of_borelQuotient {K Y : Type} [Group K] [Finite K] [Group Y] [Finite Y]
    {D : UniversalRootDatum K} {n : Fin D.rank → K} {H : Fin D.rank → Subgroup K} {π : K →* Y}
    {M : ℕ} (h : BorelQuotient D n H π M)
    (hL : ∀ i, ¬ Group.IsSolvable (rankOne D.rootGroup i)) {U : Subgroup Y}
    (hU : IsSylowTwoOf U ⊤) : NQCat.SolvOver Y U := by
  obtain ⟨T, rfl⟩ := KG22.exists_sylow_of_isSylowTwoOf hU
  obtain ⟨π', hπ', hker, hT⟩ := h.exists_conj_eq T
  rw [hT]
  exact NQCat.BN.solvOver_map_of_ker_le_center π' hπ'
    (fun z hz => h.ker_central z (hker ▸ hz))
    (borel_le_normalizer_posUnipotent h.ct)
    fun A hUA hA => NQCat.BN.le_borel_of_isSolvable h.ct h.extras hL hUA hA

theorem not_isSolvable_of_sl2_hom {F : Type} [Field F] [Finite F] [CharP F 2]
    (hF4 : 4 ≤ Nat.card F) {G : Type} [Group G]
    (φ : Matrix.SpecialLinearGroup (Fin 2) F →* G) (hφ : Function.Injective φ) :
    ¬ Group.IsSolvable G := by
  intro hG
  have hK4 := Vol2Native.A312L.exists_finset_card_four hF4
  have := Vol2Native.A312L.sl2_isSimple hK4
  obtain ⟨a, b, hab⟩ := Vol2Native.A312L.sl2_nonabelian hK4
  have hs : Group.IsSolvable (Matrix.SpecialLinearGroup (Fin 2) F) :=
    Group.isSolvable_of_isSolvable_injective hφ
  exact hab (IsSimpleGroup.comm_iff_isSolvable.mpr hs a b)

theorem rankOne_not_solvable_of_hasSL2Node {K : Type} [Group K] {D : UniversalRootDatum K}
    {i : Fin D.rank} {F : Type} [Field F] [Finite F] [CharP F 2] (hF4 : 4 ≤ Nat.card F)
    (h : HasSL2Node D i F) : ¬ Group.IsSolvable (rankOne D.rootGroup i) := by
  obtain ⟨φ, hφ, hx, hy⟩ := h
  have hrange : ∀ A, φ A ∈ rankOne D.rootGroup i := by
    have hle : Subgroup.closure (Set.range (sl2Upper (k := F)) ∪ Set.range sl2Lower) ≤
        (rankOne D.rootGroup i).comap φ := by
      rw [Subgroup.closure_le]
      rintro _ (⟨c, rfl⟩ | ⟨c, rfl⟩)
      · exact le_sup_left (b := D.rootGroup (-Pi.single i 1)) (hx c)
      · exact le_sup_right (a := D.rootGroup (Pi.single i 1)) (hy c)
    exact fun A => hle (Sp.mem_closure_sl2 A)
  exact not_isSolvable_of_sl2_hom hF4 (φ.codRestrict _ hrange)
    (fun a b hab => hφ (congrArg Subtype.val hab))

end BorelTits

section Numerics

theorem two_le_exponent_of_p_two {Q : TauCeti.PrimePower} (hQ : Q.p = 2) (h2 : Q.card ≠ 2) :
    2 ≤ Q.exponent := by
  by_contra hlt
  have he : Q.exponent = 1 := by have := Q.exponent_pos; omega
  exact h2 (by rw [TauCeti.PrimePower.card_def, hQ, he]; norm_num)

theorem four_le_card_of_p_two {Q : TauCeti.PrimePower} (hQ : Q.p = 2) (h2 : Q.card ≠ 2) :
    4 ≤ Q.card := by
  have h := two_le_exponent_of_p_two hQ h2
  rw [TauCeti.PrimePower.card_def, hQ]
  calc 4 = 2 ^ 2 := by norm_num
    _ ≤ 2 ^ Q.exponent := Nat.pow_le_pow_right (by norm_num) h

theorem card_ne_two_of_valid_G2 {Q : TauCeti.PrimePower}
    (hv : (TauCeti.LieTypeIndex.G2 Q).Valid) : Q.card ≠ 2 := by
  have h3 : 3 ≤ Q.card :=
    (TauCeti.LieTypeIndex.inStandardRange_iff _).1 ((TauCeti.LieTypeIndex.valid_iff _).1 hv).1
  omega

theorem card_ne_two_of_valid_B2 {Q : TauCeti.PrimePower}
    (hv : (TauCeti.LieTypeIndex.B 2 Q).Valid) : Q.card ≠ 2 := fun h2 =>
  ((TauCeti.LieTypeIndex.inStandardRange_iff _).1
    ((TauCeti.LieTypeIndex.valid_iff _).1 hv).1).2 ⟨rfl, h2⟩

theorem card_ne_two_of_valid_A3 {Q : TauCeti.PrimePower}
    (hv : (TauCeti.LieTypeIndex.A 3 Q).Valid) : Q.card ≠ 2 := fun h2 =>
  ((TauCeti.LieTypeIndex.valid_iff _).1 hv).2
    ((TauCeti.LieTypeIndex.isDuplicateRepresentative_iff _).2 (Or.inr (Or.inr ⟨rfl, h2⟩)))

end Numerics

end K21dTitsProof

end CFSG.LocalAnalysis.RankThreeUC.S15
