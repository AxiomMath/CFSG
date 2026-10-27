module

public import CFSG.LocalAnalysis.ComponentClassification.CTUSol76SigPairs
public import CFSG.LocalAnalysis.ComponentClassification.CTUSol76SigL39G

public section

namespace CFSG.ComponentClassification.Sol76.Sig

open CFSG Subgroup CFSG.LocalCores CFSG.ComponentClassification.FooteLit
  CFSG.ComponentClassification.UnbalancedLayer CFSG.ComponentClassification.Sol76T13

variable {G : Type} [Group G] [Finite G] {N : Subgroup G}

theorem exists_conj_le_of_sup_odd {M₀ M O : Subgroup G} (hM₀M : M₀ ≤ M)
    (hM₀O : M₀ ≤ normalizer (O : Set G)) (hO : Odd (Nat.card O)) (hsup : M₀ ⊔ O = M)
    {A : Subgroup G} (hAM : A ≤ M) (hA : IsPGroup 2 A) :
    ∃ m ∈ M, A.map (MulAut.conj m).toMonoidHom ≤ M₀ := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hprod := AS81.card_sup_mul_card_inf_of_le_normalizer_left hM₀O
  rw [hsup] at hprod
  set T := M₀.subgroupOf M with hT
  have hTcard : Nat.card T = Nat.card M₀ := by
    rw [hT, ← Subgroup.card_map_of_injective M.subtype_injective, Subgroup.subgroupOf_map_subtype,
      inf_eq_left.mpr hM₀M]
  have hidx := T.card_mul_index
  have hpos : 0 < Nat.card M₀ := Nat.card_pos
  have hdvd : T.index ∣ Nat.card O := by
    refine ⟨Nat.card (M₀ ⊓ O : Subgroup G), ?_⟩
    have h1 : Nat.card M₀ * T.index = Nat.card M := by
      rw [← hTcard, hidx]
    have h2 : Nat.card M₀ * (T.index * Nat.card (M₀ ⊓ O : Subgroup G)) =
        Nat.card M₀ * Nat.card O := by
      rw [← mul_assoc, h1, hprod]
    exact (Nat.eq_of_mul_eq_mul_left hpos h2).symm
  have hodd : ¬ 2 ∣ T.index := fun h => by
    obtain ⟨k, hk⟩ := Odd.of_dvd_nat hO hdvd
    omega
  have hA' : IsPGroup 2 (A.comap M.subtype) := hA.comap_of_injective M.subtype M.subtype_injective
  obtain ⟨g, hg⟩ := CFSG.RankThree.PartOne.KF1514B.exists_conj_le_of_not_dvd_index hodd hA'
  refine ⟨(g : G), g.2, ?_⟩
  rintro _ ⟨a, ha, rfl⟩
  have hmem : (MulAut.conj g).toMonoidHom (⟨a, hAM ha⟩ : ↥M) ∈ T :=
    hg ⟨⟨a, hAM ha⟩, ha, rfl⟩
  rw [hT, mem_subgroupOf] at hmem
  simpa [MulAut.conj_apply] using hmem

omit [Finite G] in
theorem isKleinFour_map_conj {A : Subgroup G} (hA : IsKleinFour A) (g : G) :
    IsKleinFour (A.map (MulAut.conj g).toMonoidHom) := by
  refine isKleinFour_of_card_eq_four ?_ fun x hx => ?_
  · rw [Subgroup.card_map_of_injective (MulAut.conj g).injective, hA.card_four]
  · obtain ⟨v, hv, rfl⟩ := hx
    rw [← map_pow, sq_eq_one_of_isKleinFour hA hv, map_one]

omit [Finite G] in
theorem map_conj_map_conj_inv (A : Subgroup G) (g : G) :
    (A.map (MulAut.conj g⁻¹).toMonoidHom).map (MulAut.conj g).toMonoidHom = A := by
  have h : (MulAut.conj g).toMonoidHom.comp (MulAut.conj g⁻¹).toMonoidHom = MonoidHom.id G := by
    ext x
    simp [MulAut.conj_apply, mul_assoc]
  rw [Subgroup.map_map, h, Subgroup.map_id]

omit [Finite G] in
theorem map_conj_eq_of_mem_centralizer {U : Subgroup G} {g : G}
    (hg : g ∈ centralizer (U : Set G)) : U.map (MulAut.conj g).toMonoidHom = U := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    show g * y * g⁻¹ ∈ U
    have hgy : g * y = y * g := ((mem_centralizer_iff.mp hg) y hy).symm
    rw [hgy, mul_inv_cancel_right]
    exact hy
  · intro hx
    refine ⟨x, hx, ?_⟩
    show g * x * g⁻¹ = x
    have hgx : g * x = x * g := ((mem_centralizer_iff.mp hg) x hx).symm
    rw [hgx, mul_inv_cancel_right]

theorem exists_conj_le_inf_centralizer {K'' S U : Subgroup G} (hS2 : IsPGroup 2 S)
    (hU2 : IsPGroup 2 U) (hSU : S ≤ centralizer (U : Set G))
    (hSUQ : S ⊔ U ≤ coreActionKernel K'') {T : Subgroup G}
    (hT : T ≤ K'' ⊓ centralizer (U : Set G)) (hT2 : IsPGroup 2 T) :
    ∃ m ∈ K'' ⊓ centralizer (U : Set G),
      T.map (MulAut.conj m).toMonoidHom ≤ K'' ⊓ centralizer ((S ⊔ U : Subgroup G) : Set G) := by
  have hcov := inf_centralizer_sup_oddCoreIn_eq (isPGroup_sup_of_le_centralizer hS2 hU2 hSU) hSUQ
  set M₀ := K'' ⊓ centralizer ((S ⊔ U : Subgroup G) : Set G) with hM₀
  set O := oddCoreIn K'' ⊓ centralizer (U : Set G) with hO
  have hCU : centralizer ((S ⊔ U : Subgroup G) : Set G) ≤ centralizer (U : Set G) :=
    centralizer_le (by exact_mod_cast le_sup_right)
  have hM₀M : M₀ ≤ K'' ⊓ centralizer (U : Set G) := inf_le_inf_left _ hCU
  have hM₀O : M₀ ≤ normalizer (O : Set G) := fun x hx =>
    mem_normalizer_inf (le_normalizer_oddCoreIn K'' hx.1) (le_normalizer (hCU hx.2))
  have hOodd : Odd (Nat.card O) := Nat.coprime_two_left.mp
    (Nat.Coprime.coprime_dvd_right (card_dvd_of_le inf_le_left) (coprime_card_oddCoreIn K''))
  have hsup : M₀ ⊔ O = K'' ⊓ centralizer (U : Set G) := by
    refine le_antisymm (sup_le hM₀M (inf_le_inf_right _ (map_subtype_le _))) fun x hx => ?_
    have hxK : x ∈ oddCoreIn K'' ⊔ M₀ := by rw [sup_comm, hcov]; exact hx.1
    obtain ⟨o, ho, k, hk, rfl⟩ := exists_mul_of_mem_sup_normalizer
      (inf_le_left.trans (le_normalizer_oddCoreIn K'')) hxK
    have hoU : o ∈ centralizer (U : Set G) := by
      have e : o = o * k * k⁻¹ := by group
      rw [e]
      exact mul_mem hx.2 (inv_mem (hCU hk.2))
    exact mul_mem (mem_sup_right ⟨ho, hoU⟩) (mem_sup_left hk)
  exact exists_conj_le_of_sup_odd hM₀M hM₀O hOodd hsup hT hT2

theorem wGroup_eq_of_hub (hq : QuasisimpleTwoPartInput)
    (hR1 : Lemma32ConditionTwoInputFor simpleAmbient) (hG : SimpleAmbient G)
    (hN : IsSolomonChoice N) {K K' K'' : Subgroup G} (hK : K ∈ kStarComponents N)
    (hK' : K' ∈ kStarComponents N) (hne : K ≠ K') (hK'' : K'' ∈ kStarComponents N)
    (hK''K : K'' ≠ K) (hK''K' : K'' ≠ K') {U W : Subgroup G} (hU : IsKleinFour U)
    (hUK' : U ≤ K') (hK''W : K'' ≤ normalizer (W : Set G)) {S₀ : Subgroup G}
    (hS₀ : IsKleinFour S₀) (hS₀X : S₀ ≤ K ⊓ centralizer (U : Set G)) (hW : wGroup S₀ U = W) :
    (∀ T : Subgroup G, IsKleinFour T → T ≤ K'' ⊓ centralizer (U : Set G) → wGroup T U = W) ∧
      ∀ S : Subgroup G, IsKleinFour S → S ≤ K ⊓ centralizer (U : Set G) → wGroup S U = W := by
  have hU2 := isPGroup_of_isKleinFour hU
  have hUQ'' : U ≤ coreActionKernel K'' := hUK'.trans (le_coreActionKernel_of_ne hK'' hK' hK''K')
  have hKQ'' : K ≤ coreActionKernel K'' := le_coreActionKernel_of_ne hK'' hK hK''K
  have hK''Q' : K'' ≤ coreActionKernel K' := le_coreActionKernel_of_ne hK' hK'' hK''K'.symm
  have hT : ∀ T : Subgroup G, IsKleinFour T → T ≤ K'' ⊓ centralizer (U : Set G) →
      wGroup T U = W := by
    intro T hT hTX
    obtain ⟨m, hm, hmT⟩ := exists_conj_le_inf_centralizer (isPGroup_of_isKleinFour hS₀) hU2
      (hS₀X.trans inf_le_right) (sup_le (hS₀X.trans (inf_le_left.trans hKQ'')) hUQ'') hTX
      (isPGroup_of_isKleinFour hT)
    set Tm := T.map (MulAut.conj m).toMonoidHom with hTm
    have hTm4 := isKleinFour_map_conj hT m
    have hCU : centralizer ((S₀ ⊔ U : Subgroup G) : Set G) ≤ centralizer (U : Set G) :=
      centralizer_le (by exact_mod_cast le_sup_right)
    have hCS : centralizer ((S₀ ⊔ U : Subgroup G) : Set G) ≤ centralizer (S₀ : Set G) :=
      centralizer_le (by exact_mod_cast le_sup_left)
    have h1 : wGroup Tm U = wGroup S₀ U :=
      wGroup_eq_of_commute hq hR1 hG hN hK hK' hne hU hUK' hTm4
        ((hmT.trans inf_le_left).trans hK''Q') ((hmT.trans inf_le_right).trans hCU) hS₀
        (hS₀X.trans inf_le_left) (hS₀X.trans inf_le_right) ((hmT.trans inf_le_right).trans hCS)
    have hUm : U.map (MulAut.conj m⁻¹).toMonoidHom = U :=
      map_conj_eq_of_mem_centralizer (inv_mem hm.2)
    have hWm : W.map (MulAut.conj m⁻¹).toMonoidHom = W :=
      mem_normalizer_iff_map_conj_eq.mp (inv_mem (hK''W hm.1))
    have h2 : (wGroup Tm U).map (MulAut.conj m⁻¹).toMonoidHom =
        (wGroup S₀ U).map (MulAut.conj m⁻¹).toMonoidHom := by rw [h1]
    rw [map_wGroup, hUm, hW, hWm, hTm] at h2
    have h3 : (T.map (MulAut.conj m).toMonoidHom).map (MulAut.conj m⁻¹).toMonoidHom = T := by
      have := map_conj_map_conj_inv T m⁻¹
      rwa [inv_inv] at this
    rwa [h3] at h2
  refine ⟨hT, fun S hS hSX => ?_⟩
  have hSU2 := isPGroup_sup_of_le_centralizer (isPGroup_of_isKleinFour hS) hU2
    (hSX.trans inf_le_right)
  have hrank := two_le_pRank_inf_centralizer hK'' hSU2
    (sup_le (hSX.trans (inf_le_left.trans hKQ'')) hUQ'')
  obtain ⟨t, htY, ht2⟩ := exists_orderOf_eq_two_of_pRank ((by norm_num : 1 ≤ 2).trans hrank)
  obtain ⟨T, hTY, hT4, -⟩ := exists_isKleinFour_mem hrank htY ht2
  have hCU : centralizer ((S ⊔ U : Subgroup G) : Set G) ≤ centralizer (U : Set G) :=
    centralizer_le (by exact_mod_cast le_sup_right)
  have hCS : centralizer ((S ⊔ U : Subgroup G) : Set G) ≤ centralizer (S : Set G) :=
    centralizer_le (by exact_mod_cast le_sup_left)
  have hTX : T ≤ K'' ⊓ centralizer (U : Set G) := hTY.trans (inf_le_inf_left _ hCU)
  rw [← hT T hT4 hTX]
  exact (wGroup_eq_of_commute hq hR1 hG hN hK hK' hne hU hUK' hT4
    ((hTY.trans inf_le_left).trans hK''Q') (hTX.trans inf_le_right) hS (hSX.trans inf_le_left)
    (hSX.trans inf_le_right) ((hTY.trans inf_le_right).trans hCS)).symm

@[expose] def GoodFourFor (K W U : Subgroup G) : Prop :=
  ∀ S : Subgroup G, IsKleinFour S → S ≤ K ⊓ centralizer (U : Set G) → wGroup S U = W

theorem exists_isKleinFour_inf_centralizer {K : Subgroup G} (hK : K ∈ kStarComponents N)
    {X : Subgroup G} (hX2 : IsPGroup 2 X)
    (hXQ : X ≤ coreActionKernel K) :
    ∃ S : Subgroup G, IsKleinFour S ∧ S ≤ K ⊓ centralizer (X : Set G) := by
  have hrank := two_le_pRank_inf_centralizer hK hX2 hXQ
  obtain ⟨s, hsY, hs2⟩ := exists_orderOf_eq_two_of_pRank ((by norm_num : 1 ≤ 2).trans hrank)
  obtain ⟨S, hSY, hS, -⟩ := exists_isKleinFour_mem hrank hsY hs2
  exact ⟨S, hS, hSY⟩

theorem goodFour_of_mem_inf (hq : QuasisimpleTwoPartInput)
    (hR1 : Lemma32ConditionTwoInputFor simpleAmbient) (hG : SimpleAmbient G)
    (hN : IsSolomonChoice N) {K K' K'' : Subgroup G} (hK : K ∈ kStarComponents N)
    (hK' : K' ∈ kStarComponents N) (hne : K ≠ K') (hK'' : K'' ∈ kStarComponents N)
    (hK''K : K'' ≠ K) (hK''K' : K'' ≠ K') {W : Subgroup G}
    (hK''W : K'' ≤ normalizer (W : Set G)) {U U' : Subgroup G} (hU : IsKleinFour U)
    (hUK' : U ≤ K') (hU' : IsKleinFour U') (hU'K' : U' ≤ K')
    (hUU' : IsPGroup 2 (U ⊔ U' : Subgroup G)) {u : G} (hu : u ∈ U) (hu' : u ∈ U')
    (hu1 : u ≠ 1) (hgood : GoodFourFor K W U) : GoodFourFor K W U' := by
  have h32 := lemma32FullFor_simple_of_twoPart hq hR1
  have hK'Q : K' ≤ coreActionKernel K := le_coreActionKernel_of_ne hK hK' hne
  obtain ⟨S, hS, hSX⟩ := exists_isKleinFour_inf_centralizer hK hUU'
    (sup_le (hUK'.trans hK'Q) (hU'K'.trans hK'Q))
  have hSK : S ≤ K := hSX.trans inf_le_left
  have hSU : S ≤ centralizer (U : Set G) :=
    (hSX.trans inf_le_right).trans (centralizer_le (by exact_mod_cast le_sup_left))
  have hSU' : S ≤ centralizer (U' : Set G) :=
    (hSX.trans inf_le_right).trans (centralizer_le (by exact_mod_cast le_sup_right))
  have hW : wGroup S U' = W := by
    rw [wGroup_eq_wGroup_zpowers h32 hG hN hK hK' hne hU' hU'K' hS hSK hSU' hu' hu1,
      ← wGroup_eq_wGroup_zpowers h32 hG hN hK hK' hne hU hUK' hS hSK hSU hu hu1]
    exact hgood S hS (le_inf hSK hSU)
  exact (wGroup_eq_of_hub hq hR1 hG hN hK hK' hne hK'' hK''K hK''K' hU' hU'K' hK''W hS
    (le_inf hSK hSU') hW).2

theorem exists_isKleinFour_mem_center {P X : Subgroup G} (hX : IsKleinFour X) (hXP : X ≤ P)
    {z : G} (hzP : z ∈ P) (hz2 : orderOf z = 2) (hzc : ∀ q ∈ P, z * q = q * z) :
    ∃ Z : Subgroup G, IsKleinFour Z ∧ Z ≤ P ∧ z ∈ Z ∧ ∃ x ∈ X, x ∈ Z ∧ x ≠ 1 := by
  by_cases hzX : z ∈ X
  · exact ⟨X, hX, hXP, hzX, z, hzX, hzX, fun h => by rw [h, orderOf_one] at hz2; norm_num at hz2⟩
  · obtain ⟨x, hxX, hx1⟩ := exists_mem_ne_one_of_isKleinFour hX
    have hx2 := orderOf_eq_two_of_isKleinFour hX hxX hx1
    have hxz : x ≠ z := fun h => hzX (h ▸ hxX)
    refine ⟨closure {x, z}, UnbalancedGS.ReciprocalFusion.isKleinFour_closure_pair hx2 hz2
      (hzc x (hXP hxX)).symm hxz, ?_, subset_closure (Set.mem_insert_of_mem x rfl), x, hxX,
      subset_closure (Set.mem_insert x _), hx1⟩
    rw [closure_le]
    rintro y (rfl | rfl)
    · exact hXP hxX
    · exact hzP

theorem exists_central_involution_of_isPGroup {Q : Subgroup G} (hQ : IsPGroup 2 Q)
    (hne : Q ≠ ⊥) : ∃ q ∈ Q, orderOf q = 2 ∧ ∀ q' ∈ Q, q * q' = q' * q := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hnt : Nontrivial Q := (Subgroup.nontrivial_iff_ne_bot Q).2 hne
  have hZ := hQ.center_nontrivial
  have hZ2 : IsPGroup 2 (Subgroup.center Q) := hQ.to_subgroup _
  obtain ⟨n, hn, hcard⟩ := hZ2.nontrivial_iff_card.1 hZ
  have hdvd : 2 ∣ Nat.card (Subgroup.center Q) := by
    rw [hcard]
    exact dvd_pow_self 2 (by omega)
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' 2 hdvd
  refine ⟨((x : Q) : G), (x : Q).2, ?_, ?_⟩
  · rw [Subgroup.orderOf_coe, Subgroup.orderOf_coe, hx]
  · intro q' hq'
    have := Subgroup.mem_center_iff.1 x.2 ⟨q', hq'⟩
    exact congrArg Subtype.val this.symm

theorem goodFour_of_le_pGroup (hq : QuasisimpleTwoPartInput)
    (hR1 : Lemma32ConditionTwoInputFor simpleAmbient) (hG : SimpleAmbient G)
    (hN : IsSolomonChoice N) {K K' K'' : Subgroup G} (hK : K ∈ kStarComponents N)
    (hK' : K' ∈ kStarComponents N) (hne : K ≠ K') (hK'' : K'' ∈ kStarComponents N)
    (hK''K : K'' ≠ K) (hK''K' : K'' ≠ K') {W : Subgroup G}
    (hK''W : K'' ≤ normalizer (W : Set G)) {P : Subgroup G} (hP2 : IsPGroup 2 P)
    (hPK' : P ≤ K') {U U' : Subgroup G} (hU : IsKleinFour U) (hUP : U ≤ P)
    (hU' : IsKleinFour U') (hU'P : U' ≤ P) (hgood : GoodFourFor K W U) : GoodFourFor K W U' := by
  have hPne : P ≠ ⊥ := fun h => by
    have h4 := hU.card_four
    rw [show U = ⊥ from eq_bot_iff.mpr (h ▸ hUP), card_bot] at h4
    norm_num at h4
  obtain ⟨z, hzP, hz2, hzc⟩ := exists_central_involution_of_isPGroup hP2 hPne
  have hz1 : z ≠ 1 := fun h => by rw [h, orderOf_one] at hz2; norm_num at hz2
  have hstep : ∀ {X Y : Subgroup G}, IsKleinFour X → X ≤ P → IsKleinFour Y → Y ≤ P →
      ∀ {y : G}, y ∈ X → y ∈ Y → y ≠ 1 → GoodFourFor K W X → GoodFourFor K W Y :=
    fun {X Y} hX hXP hY hYP {y} hyX hyY hy1 hgX =>
      goodFour_of_mem_inf hq hR1 hG hN hK hK' hne hK'' hK''K hK''K' hK''W hX (hXP.trans hPK') hY
        (hYP.trans hPK') (hP2.to_le (sup_le hXP hYP)) hyX hyY hy1 hgX
  obtain ⟨Z, hZ, hZP, hzZ, x, hxU, hxZ, hx1⟩ := exists_isKleinFour_mem_center hU hUP hzP hz2 hzc
  obtain ⟨Z', hZ', hZ'P, hzZ', x', hxU', hxZ', hx'1⟩ :=
    exists_isKleinFour_mem_center hU' hU'P hzP hz2 hzc
  have h1 := hstep hU hUP hZ hZP hxU hxZ hx1 hgood
  have h2 := hstep hZ hZP hZ' hZ'P hzZ hzZ' hz1 h1
  exact hstep hZ' hZ'P hU' hU'P hxZ' hxU' hx'1 h2

theorem goodFour_map_conj {K K' : Subgroup G} (hK : K ∈ kStarComponents N)
    (hK' : K' ∈ kStarComponents N) (hne : K ≠ K') {W U : Subgroup G}
    (hgood : GoodFourFor K W U) {k : G} (hkK' : k ∈ K') (hkW : k ∈ normalizer (W : Set G)) :
    GoodFourFor K W (U.map (MulAut.conj k).toMonoidHom) := by
  intro S' hS' hS'X
  set S := S'.map (MulAut.conj k⁻¹).toMonoidHom with hS
  have hkN : k⁻¹ ∈ normalizer (K : Set G) :=
    (le_coreActionKernel_of_ne hK hK' hne (inv_mem hkK')).1
  have hKk : K.map (MulAut.conj k⁻¹).toMonoidHom = K := mem_normalizer_iff_map_conj_eq.mp hkN
  have hCk : (centralizer ((U.map (MulAut.conj k).toMonoidHom : Subgroup G) : Set G)).map
      (MulAut.conj k⁻¹).toMonoidHom = centralizer (U : Set G) := by
    rw [← map_centralizer (MulAut.conj k) U]
    have := map_conj_map_conj_inv (centralizer (U : Set G)) k⁻¹
    rwa [inv_inv] at this
  have hSX : S ≤ K ⊓ centralizer (U : Set G) := le_inf
    (by rw [← hKk]; exact map_mono (hS'X.trans inf_le_left))
    (by rw [← hCk]; exact map_mono (hS'X.trans inf_le_right))
  have h1 := hgood S (isKleinFour_map_conj hS' k⁻¹) hSX
  have hSS' : S.map (MulAut.conj k).toMonoidHom = S' := map_conj_map_conj_inv S' k
  have hWk : W.map (MulAut.conj k).toMonoidHom = W := mem_normalizer_iff_map_conj_eq.mp hkW
  rw [← hSS', ← map_wGroup, h1, hWk]

theorem exists_pGroup_conj_le {K' V U : Subgroup G} (hVK' : V ≤ K') (hV2 : IsPGroup 2 V)
    (hUK' : U ≤ K') (hU2 : IsPGroup 2 U) :
    ∃ P : Subgroup G, P ≤ K' ∧ IsPGroup 2 P ∧ V ≤ P ∧
      ∃ k ∈ K', U.map (MulAut.conj k).toMonoidHom ≤ P := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨Q, hQ⟩ := (hV2.comap_of_injective K'.subtype K'.subtype_injective).exists_le_sylow
  refine ⟨(Q : Subgroup ↥K').map K'.subtype, map_subtype_le _, Q.isPGroup'.map _, ?_, ?_⟩
  · intro v hv
    exact ⟨⟨v, hVK' hv⟩, hQ hv, rfl⟩
  · obtain ⟨g, hg⟩ := CFSG.RankThree.PartOne.KF1514B.exists_conj_le_of_not_dvd_index
      (Sylow.not_dvd_index Q) (hU2.comap_of_injective K'.subtype K'.subtype_injective)
    refine ⟨(g : G), g.2, ?_⟩
    rintro _ ⟨u, hu, rfl⟩
    have hmem := hg ⟨⟨u, hUK' hu⟩, hu, rfl⟩
    exact ⟨_, hmem, by simp [MulAut.conj_apply]⟩

theorem goodFour_of_le (hq : QuasisimpleTwoPartInput)
    (hR1 : Lemma32ConditionTwoInputFor simpleAmbient) (hG : SimpleAmbient G)
    (hN : IsSolomonChoice N) {K K' K'' : Subgroup G} (hK : K ∈ kStarComponents N)
    (hK' : K' ∈ kStarComponents N) (hne : K ≠ K') (hK'' : K'' ∈ kStarComponents N)
    (hK''K : K'' ≠ K) (hK''K' : K'' ≠ K') {W : Subgroup G}
    (hK''W : K'' ≤ normalizer (W : Set G)) (hK'W : K' ≤ normalizer (W : Set G))
    {V : Subgroup G} (hV : IsKleinFour V) (hVK' : V ≤ K') (hgood : GoodFourFor K W V)
    {U : Subgroup G} (hU : IsKleinFour U) (hUK' : U ≤ K') : GoodFourFor K W U := by
  obtain ⟨P, hPK', hP2, hVP, k, hkK', hUk⟩ :=
    exists_pGroup_conj_le hVK' (isPGroup_of_isKleinFour hV) hUK' (isPGroup_of_isKleinFour hU)
  have h1 := goodFour_of_le_pGroup hq hR1 hG hN hK hK' hne hK'' hK''K hK''K' hK''W hP2 hPK' hV
    hVP (isKleinFour_map_conj hU k) hUk hgood
  have h2 := goodFour_map_conj hK hK' hne h1 (inv_mem hkK') (inv_mem (hK'W hkK'))
  have h3 : (U.map (MulAut.conj k).toMonoidHom).map (MulAut.conj k⁻¹).toMonoidHom = U := by
    have := map_conj_map_conj_inv U k⁻¹
    rwa [inv_inv] at this
  rwa [h3] at h2

theorem exists_sigPair_of_le_of_third (hq : QuasisimpleTwoPartInput)
    (hR1 : Lemma32ConditionTwoInputFor simpleAmbient) (hG : SimpleAmbient G)
    (hN : IsSolomonChoice N) {Ka Kb Kc : Subgroup G} (hKa : Ka ∈ kStarComponents N)
    (hKb : Kb ∈ kStarComponents N) (hab : Ka ≠ Kb) (hKc : Kc ∈ kStarComponents N)
    (hca : Kc ≠ Ka) (hcb : Kc ≠ Kb) {U X : Subgroup G} (hU : IsKleinFour U) (hUKb : U ≤ Kb)
    (hX : IsKleinFour X) (hXY : X ≤ Ka ⊓ centralizer (U : Set G)) :
    ∃ A : Subgroup G, SigPair N Ka Kb U A ∧ X ≤ A ∧ wGroup A U = wGroup X U := by
  classical
  have hXK : X ≤ Ka := hXY.trans inf_le_left
  have hXU : X ≤ centralizer (U : Set G) := hXY.trans inf_le_right
  have hS2 := isPGroup_sup_of_le_centralizer (isPGroup_of_isKleinFour hX)
    (isPGroup_of_isKleinFour hU) hXU
  have hSQ : X ⊔ U ≤ coreActionKernel Kc :=
    sup_le (hXK.trans (le_coreActionKernel_of_ne hKc hKa hca))
      (hUKb.trans (le_coreActionKernel_of_ne hKc hKb hcb))
  obtain ⟨t, htY, ht2, htQ⟩ := exists_orderOf_eq_two_not_mem_coreActionKernel hq hG hKc.1 hKc.2
    inf_le_left (inf_centralizer_sup_oddCoreIn_eq hS2 hSQ)
  have htK : t ∈ Kc := htY.1
  have htX : t ∉ X := fun h => htQ (le_coreActionKernel_of_ne hKc hKa hca (hXK h))
  have htS : t ∈ centralizer ((X ⊔ U : Subgroup G) : Set G) := htY.2
  have htcX : t ∈ centralizer (X : Set G) := centralizer_le (by exact_mod_cast le_sup_left) htS
  have htU : t ∈ centralizer (U : Set G) := centralizer_le (by exact_mod_cast le_sup_right) htS
  obtain ⟨hAe, hA8⟩ := isElemAbelian_sup_zpowers_two (isElemAbelian_of_isKleinFour hX) ht2 htX htcX
  have hAQ : X ⊔ zpowers t ≤ coreActionKernel Kb :=
    sup_le (hXK.trans (le_coreActionKernel_of_ne hKb hKa (Ne.symm hab)))
      (zpowers_le.mpr (mem_coreActionKernel_of_ne hKc hKb hcb htK))
  have hAU : X ⊔ zpowers t ≤ centralizer (U : Set G) := sup_le hXU (zpowers_le.mpr htU)
  have hAN : X ⊔ zpowers t ≤ N := sup_le (hXK.trans hKa.1.1) (zpowers_le.mpr (hKc.1.1 htK))
  refine ⟨X ⊔ zpowers t, ⟨hKa, hKb, hab, hU, hUKb, hAQ, hAU, hAe, by rw [hA8, hX.card_four],
    hAN, X, hX, le_sup_left, hXK⟩, le_sup_left, ?_⟩
  exact (wGroup_eq_of_le_of_mem hq hR1 hG hN hKa hKb hab hU hUKb hAQ hAU hAe hX le_sup_left hXK hX
    le_sup_left).symm

theorem isGoodFor_of_third (hq : QuasisimpleTwoPartInput)
    (hR1 : Lemma32ConditionTwoInputFor simpleAmbient) (hG : SimpleAmbient G)
    (hN : IsSolomonChoice N) {K K' V B : Subgroup G} (hP : SigPair N K K' V B)
    (hKH : ∀ K'' ∈ kStarComponents N, K'' ≤ normalizer (wGroup B V : Set G))
    {K₃ : Subgroup G} (hK₃ : K₃ ∈ kStarComponents N) (hK₃K : K₃ ≠ K) (hK₃K' : K₃ ≠ K')
    {K'' : Subgroup G} (hK'' : K'' ∈ kStarComponents N) {x : G} (hx : x ∈ K'')
    (hx2 : orderOf x = 2) : IsGoodFor N (wGroup B V) x := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hK, hK', hne, hV, hVK', hBQ, hBV, hB, hB8, hBN, E, hE, hEB, hEK⟩ := hP
  have hx1 : x ≠ 1 := fun h => by rw [h, orderOf_one] at hx2; norm_num at hx2
  have hWE : wGroup E V = wGroup B V :=
    wGroup_eq_of_le_of_mem hq hR1 hG hN hK hK' hne hV hVK' hBQ hBV hB hE hEB hEK hE hEB
  have hgoodV : GoodFourFor K (wGroup B V) V :=
    (wGroup_eq_of_hub hq hR1 hG hN hK hK' hne hK₃ hK₃K hK₃K' hV hVK' (hKH K₃ hK₃) hE
      (le_inf hEK (hEB.trans hBV)) hWE).2
  have hgood : ∀ U : Subgroup G, IsKleinFour U → U ≤ K' → GoodFourFor K (wGroup B V) U :=
    fun U hU hUK' => goodFour_of_le hq hR1 hG hN hK hK' hne hK₃ hK₃K hK₃K' (hKH K₃ hK₃)
      (hKH K' hK') hV hVK' hgoodV hU hUK'
  have hK'Q : K' ≤ coreActionKernel K := le_coreActionKernel_of_ne hK hK' hne
  by_cases hK''K' : K'' = K'
  ·
    subst hK''K'
    obtain ⟨U, hUK', hU, hxU⟩ :=
      exists_isKleinFour_mem (two_le_pRank_of_mem_solomonKStar hK''.2) hx hx2
    obtain ⟨S, hS, hSX⟩ := exists_isKleinFour_inf_centralizer hK
      (isPGroup_of_isKleinFour hU) (hUK'.trans hK'Q)
    obtain ⟨A, hPA, -, hWA⟩ :=
      exists_sigPair_of_le_of_third hq hR1 hG hN hK hK'' hne hK₃ hK₃K hK₃K' hU hUK' hS hSX
    exact ⟨hx1, K, K'', U, A, hPA, hWA.trans (hgood U hU hUK' S hS hSX), Or.inr hxU⟩
  have hxz : IsPGroup 2 (zpowers x) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hx2, pow_one])
  obtain ⟨U, hU, hUY⟩ := exists_isKleinFour_inf_centralizer hK' hxz
    (zpowers_le.mpr (mem_coreActionKernel_of_ne hK'' hK' hK''K' hx))
  have hUK' : U ≤ K' := hUY.trans inf_le_left
  have hUx : U ≤ centralizer ({x} : Set G) := by
    have h := hUY.trans inf_le_right
    rwa [centralizer_zpowers_eq] at h
  have hxY : x ∈ K'' ⊓ centralizer (U : Set G) := mem_inf.mpr ⟨hx, mem_centralizer_iff.mpr
    fun u hu => mem_centralizer_singleton_iff.mp (hUx hu)⟩
  have hUQ'' : U ≤ coreActionKernel K'' := hUK'.trans (le_coreActionKernel_of_ne hK'' hK' hK''K')
  obtain ⟨X, hXY, hX, hxX⟩ := exists_isKleinFour_mem
    (two_le_pRank_inf_centralizer hK'' (isPGroup_of_isKleinFour hU) hUQ'') hxY hx2
  have hWX : wGroup X U = wGroup B V := by
    by_cases hK''K : K'' = K
    · subst hK''K
      exact hgood U hU hUK' X hX hXY
    · obtain ⟨S₀, hS₀, hS₀X⟩ := exists_isKleinFour_inf_centralizer hK
        (isPGroup_of_isKleinFour hU) (hUK'.trans hK'Q)
      exact (wGroup_eq_of_hub hq hR1 hG hN hK hK' hne hK'' hK''K hK''K' hU hUK' (hKH K'' hK'')
        hS₀ hS₀X (hgood U hU hUK' S₀ hS₀ hS₀X)).1 X hX hXY
  obtain ⟨Kc, hKc, hcK'', hcK'⟩ : ∃ Kc ∈ kStarComponents N, Kc ≠ K'' ∧ Kc ≠ K' := by
    by_cases hK''K : K'' = K
    · exact ⟨K₃, hK₃, hK''K ▸ hK₃K, hK₃K'⟩
    · exact ⟨K, hK, Ne.symm hK''K, hne⟩
  obtain ⟨A, hPA, hXA, hWA⟩ :=
    exists_sigPair_of_le_of_third hq hR1 hG hN hK'' hK' hK''K' hKc hcK'' hcK' hU hUK' hX hXY
  exact ⟨hx1, K'', K', U, A, hPA, hWA.trans hWX, Or.inl (hXA hxX)⟩

theorem exists_third_kStar_of_ncard_ne_two {K K' : Subgroup G} (hK : K ∈ kStarComponents N)
    (hK' : K' ∈ kStarComponents N) (hne : K ≠ K') (h2 : (kStarComponents N).ncard ≠ 2) :
    ∃ K'' ∈ kStarComponents N, K'' ≠ K ∧ K'' ≠ K' := by
  classical
  by_contra hc
  push Not at hc
  have hsub : kStarComponents N ⊆ {K, K'} := fun J hJ => by
    by_cases hJK : J = K
    · exact Or.inl hJK
    · exact Or.inr (hc J hJ hJK)
  have hle := Set.ncard_le_ncard hsub (Set.toFinite _)
  rw [Set.ncard_pair hne] at hle
  have hge : 2 ≤ (kStarComponents N).ncard := by
    rw [← Set.ncard_pair hne]
    exact Set.ncard_le_ncard (Set.insert_subset hK (Set.singleton_subset_iff.mpr hK'))
      (Set.toFinite _)
  omega

@[expose] def GoodInvolutionsTwoFor : Prop :=
  ∀ (G : Type) [Group G] [Finite G], SimpleAmbient G → ∀ N : Subgroup G, IsSolomonChoice N →
    (kStarComponents N).ncard = 2 →
    ∀ K K' V B : Subgroup G, SigPair N K K' V B → wGroup B V ≠ ⊥ →
      (∀ K'' ∈ kStarComponents N, K'' ≤ normalizer (wGroup B V : Set G)) →
      ∀ K'' ∈ kStarComponents N, ∀ x ∈ K'', orderOf x = 2 →
        ∃ g ∈ normalizer (wGroup B V : Set G), IsGoodFor N (wGroup B V) (g⁻¹ * x * g)

theorem goodInvolutionsFor_of_two (hq : QuasisimpleTwoPartInput)
    (hR1 : Lemma32ConditionTwoInputFor simpleAmbient) (h : GoodInvolutionsTwoFor) :
    GoodInvolutionsFor := by
  intro G _ _ hG N hN K K' V B hP hW hKH K'' hK'' x hx hx2
  by_cases h2 : (kStarComponents N).ncard = 2
  · exact h G hG N hN h2 K K' V B hP hW hKH K'' hK'' x hx hx2
  obtain ⟨K₃, hK₃, hK₃K, hK₃K'⟩ := exists_third_kStar_of_ncard_ne_two hP.1 hP.2.1 hP.2.2.1 h2
  refine ⟨1, one_mem _, ?_⟩
  rw [inv_one, one_mul, mul_one]
  exact isGoodFor_of_third hq hR1 hG hN hP hKH hK₃ hK₃K hK₃K' hK'' hx hx2

theorem lemma315bInputFor_simple_of_two (hq : QuasisimpleTwoPartInput)
    (hR1 : Lemma32ConditionTwoInputFor simpleAmbient) (hF : False316CoverFor simpleAmbient)
    (h39 : Lemma39For) (hgood : GoodInvolutionsTwoFor) (hsingle : SingleComponentExcludedFor)
    (hpair : SigPairExistsTwoFor) : Lemma315bInputFor simpleAmbient :=
  lemma315bInputFor_simple_of_good hq hR1 hF h39 (goodInvolutionsFor_of_two hq hR1 hgood) hsingle
    (sigPairExistsFor_of_two hq hpair)

theorem le_normalizer_wGroup_of_third (hq : QuasisimpleTwoPartInput)
    (hR1 : Lemma32ConditionTwoInputFor simpleAmbient) (hG : SimpleAmbient G)
    (hN : IsSolomonChoice N) {K K' V B : Subgroup G} (hP : SigPair N K K' V B)
    {K₃ : Subgroup G} (hK₃ : K₃ ∈ kStarComponents N) (hK₃K : K₃ ≠ K) (hK₃K' : K₃ ≠ K') :
    K ≤ normalizer (wGroup B V : Set G) := by
  obtain ⟨hK, hK', hne, hV, hVK', hBQ, hBV, hB, hB8, hBN, E, hE, hEB, hEK⟩ := hP
  have hWE : wGroup E V = wGroup B V :=
    wGroup_eq_of_le_of_mem hq hR1 hG hN hK hK' hne hV hVK' hBQ hBV hB hE hEB hEK hE hEB
  have hK₃W := le_normalizer_wGroup_of_ne_of_mem hq hR1 hG hN hK hK' hne hV hVK' hBQ hBV hB hB8 hE
    hEB hEK hBN hK₃ hK₃K hK₃K'
  have hEX : E ≤ K ⊓ centralizer (V : Set G) := le_inf hEK (hEB.trans hBV)
  have hfree := (wGroup_eq_of_hub hq hR1 hG hN hK hK' hne hK₃ hK₃K hK₃K' hV hVK' hK₃W hE hEX
    hWE).2
  have hVQ : V ≤ coreActionKernel K := hVK'.trans (le_coreActionKernel_of_ne hK hK' hne)
  rw [← inf_centralizer_sup_oddCoreIn_eq (isPGroup_of_isKleinFour hV) hVQ]
  refine sup_le ?_ ?_
  · intro g hg
    have hVg : V.map (MulAut.conj g).toMonoidHom = V := map_conj_eq_of_mem_centralizer hg.2
    have hEgX : E.map (MulAut.conj g).toMonoidHom ≤ K ⊓ centralizer (V : Set G) := by
      rintro _ ⟨e, he, rfl⟩
      exact mul_mem (mul_mem hg (hEX he)) (inv_mem hg)
    have key : (wGroup B V).map (MulAut.conj g).toMonoidHom = wGroup B V := by
      rw [← hWE, map_wGroup, hVg, hWE]
      exact hfree _ (isKleinFour_map_conj hE g) hEgX
    exact mem_normalizer_iff_map_conj_eq.mpr key
  · exact (oddCoreIn_le_of_isTwoComponentIn hK.1).trans
      (oddCoreIn_le_normalizer_wGroup_of_mem hq hR1 hG hN hK hK' hne hV hVK' hBQ hBV hB hB8 hE hEB
        hEK hBN)

@[expose] def Lemma39RestFor : Prop :=
  ∀ (G : Type) [Group G] [Finite G], SimpleAmbient G → ∀ N : Subgroup G, IsSolomonChoice N →
    ∀ K K' V B : Subgroup G, SigPair N K K' V B → wGroup B V ≠ ⊥ →
      ((kStarComponents N).ncard = 2 →
        (∀ E : Subgroup G, IsKleinFour E → E ≤ B → E ≤ K →
          ¬ ∀ F : Subgroup G, IsKleinFour F → F ≤ K ⊓ centralizer (V : Set G) →
            Relation.ReflTransGen (CommFourIn (K ⊓ centralizer (V : Set G))) E F) →
        K ≤ normalizer (wGroup B V : Set G)) ∧
      ((∀ E : Subgroup G, IsKleinFour E → E ≤ B → E ≤ K →
          ¬ (CFSG.Assembly.involutionGraph ↥(K' ⊓ centralizer (E : Set G))).Preconnected) →
        K' ≤ normalizer (wGroup B V : Set G))

theorem lemma39For_of_rest (hq : QuasisimpleTwoPartInput)
    (hR1 : Lemma32ConditionTwoInputFor simpleAmbient) (h : Lemma39RestFor) : Lemma39For := by
  intro G _ _ hG N hN K K' V B hP hW K'' hK''
  have hP' := hP
  obtain ⟨hK, hK', hne, hV, hVK', hBQ, hBV, hB, hB8, hBN, E₀, hE₀, hE₀B, hE₀K⟩ := hP'
  by_cases hK''K : K'' = K
  · rw [hK''K]
    by_cases h2 : (kStarComponents N).ncard = 2
    · by_cases hc : ∃ E : Subgroup G, IsKleinFour E ∧ E ≤ B ∧ E ≤ K ∧
          ∀ F : Subgroup G, IsKleinFour F → F ≤ K ⊓ centralizer (V : Set G) →
            Relation.ReflTransGen (CommFourIn (K ⊓ centralizer (V : Set G))) E F
      · obtain ⟨E, hE, hEB, hEK, hconn⟩ := hc
        exact le_normalizer_wGroup_of_twoConnected_of_mem hq hR1 hG hN hK hK' hne hV hVK' hBQ hBV
          hB hB8 hE hEB hEK hBN hconn
      · exact (h G hG N hN K K' V B hP hW).1 h2 fun E hE hEB hEK hconn =>
          hc ⟨E, hE, hEB, hEK, hconn⟩
    · obtain ⟨K₃, hK₃, hK₃K, hK₃K'⟩ := exists_third_kStar_of_ncard_ne_two hK hK' hne h2
      exact le_normalizer_wGroup_of_third hq hR1 hG hN hP hK₃ hK₃K hK₃K'
  by_cases hK''K' : K'' = K'
  · rw [hK''K']
    by_cases hc : ∃ E : Subgroup G, IsKleinFour E ∧ E ≤ B ∧ E ≤ K ∧
        (CFSG.Assembly.involutionGraph ↥(K' ⊓ centralizer (E : Set G))).Preconnected
    · obtain ⟨E, hE, hEB, hEK, hconn⟩ := hc
      exact le_normalizer_wGroup_of_preconnected_of_mem hq hR1 hG hN hK hK' hne hV hVK' hBQ hBV hB
        hB8 hE hEB hEK hconn
    · exact (h G hG N hN K K' V B hP hW).2 fun E hE hEB hEK hconn => hc ⟨E, hE, hEB, hEK, hconn⟩
  · exact le_normalizer_wGroup_of_ne_of_mem hq hR1 hG hN hK hK' hne hV hVK' hBQ hBV hB hB8 hE₀ hE₀B
      hE₀K hBN hK'' hK''K hK''K'

theorem lemma315bInputFor_simple_of_residues (hq : QuasisimpleTwoPartInput)
    (hR1 : Lemma32ConditionTwoInputFor simpleAmbient) (hF : False316CoverFor simpleAmbient)
    (h39 : Lemma39RestFor) (hgood : GoodInvolutionsTwoFor) (hsingle : SingleComponentExcludedFor)
    (hpair : SigPairExistsTwoFor) : Lemma315bInputFor simpleAmbient :=
  lemma315bInputFor_simple_of_two hq hR1 hF (lemma39For_of_rest hq hR1 h39) hgood hsingle hpair

end CFSG.ComponentClassification.Sol76.Sig
