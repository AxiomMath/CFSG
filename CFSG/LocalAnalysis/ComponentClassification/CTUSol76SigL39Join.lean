module

public import CFSG.LocalAnalysis.ComponentClassification.CTUSol76SigGoodJoin
public import CFSG.LocalAnalysis.ComponentClassification.Sol76SigLift
public import CFSG.LocalAnalysis.ComponentClassification.Sol76SigGammaCore
public import CFSG.LocalAnalysis.ComponentClassification.Sol76SigGammaLift

public section

namespace CFSG.ComponentClassification.Sol76.Sig

open CFSG Subgroup CFSG.ComponentClassification.FooteLit
  CFSG.ComponentClassification.UnbalancedLayer CFSG.ComponentClassification.Sol76T13

section Conj

variable {X : Type} [Group X]

private theorem map_conj_map_conj_l39 (E : Subgroup X) (g h : X) :
    (E.map (MulAut.conj h).toMonoidHom).map (MulAut.conj g).toMonoidHom =
      E.map (MulAut.conj (g * h)).toMonoidHom := by
  rw [Subgroup.map_map]
  congr 1
  ext x
  simp only [MonoidHom.coe_comp, Function.comp_apply, MulEquiv.coe_toMonoidHom,
    MulAut.conj_apply]
  group

private theorem map_conj_one_l39 (E : Subgroup X) :
    E.map (MulAut.conj (1 : X)).toMonoidHom = E := by
  ext x
  simp

private theorem map_conj_of_mem_l39 {D : Subgroup X} {d : X} (hd : d ∈ D) :
    D.map (MulAut.conj d).toMonoidHom = D := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    exact mul_mem (mul_mem hd hy) (inv_mem hd)
  · intro hx
    refine ⟨d⁻¹ * x * d, mul_mem (mul_mem (inv_mem hd) hx) hd, ?_⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    group

private theorem le_normalizer_of_normal_l39 {O : Subgroup X} (hO : O.Normal) (E : Subgroup X) :
    E ≤ normalizer (O : Set X) := fun a _ => mem_normalizer_iff.mpr fun y =>
  ⟨fun hy => hO.conj_mem y hy a, fun hy => by
    have h1 := hO.conj_mem _ hy a⁻¹
    have e : a⁻¹ * (a * y * a⁻¹) * a⁻¹⁻¹ = y := by group
    rwa [e] at h1⟩

end Conj

section Lift

variable {Y Q : Type} [Group Y] [Finite Y] [Group Q]

theorem exists_ker_conj_eq (ψ : Y →* Q) (hker : Odd (Nat.card ψ.ker)) {D₁ D : Subgroup Y}
    (hD₁ : IsKleinFour D₁) (hD : IsKleinFour D) (h : D₁.map ψ = D.map ψ) :
    ∃ c ∈ ψ.ker, D₁.map (MulAut.conj c).toMonoidHom = D := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hD₁M : D₁ ≤ D ⊔ ψ.ker := by
    intro d hd
    have hdD : ψ d ∈ D.map ψ := by
      rw [← h]
      exact mem_map_of_mem ψ hd
    obtain ⟨d', hd'D, hd'⟩ := hdD
    have e : d = d' * (d'⁻¹ * d) := by group
    rw [e]
    refine mul_mem (mem_sup_left hd'D) (mem_sup_right ?_)
    rw [MonoidHom.mem_ker, map_mul, map_inv, hd', inv_mul_cancel]
  obtain ⟨m, hmM, hm⟩ := exists_conj_le_of_sup_odd le_sup_left
    (le_normalizer_of_normal_l39 (MonoidHom.normal_ker ψ) D) hker rfl hD₁M
    (isPGroup_of_isKleinFour hD₁)
  obtain ⟨d, hdD, k, hk, rfl⟩ := mem_sup_of_normal_right.mp hmM
  refine ⟨k, hk, ?_⟩
  have heq : D₁.map (MulAut.conj (d * k)).toMonoidHom = D :=
    Subgroup.eq_of_le_of_card_ge hm (by
      rw [Subgroup.card_map_of_injective (MulAut.conj (d * k)).injective, hD₁.card_four,
        hD.card_four])
  have h2 := congrArg (fun X : Subgroup Y => X.map (MulAut.conj d⁻¹).toMonoidHom) heq
  rwa [map_conj_map_conj_l39, ← mul_assoc, inv_mul_cancel, one_mul,
    map_conj_of_mem_l39 (inv_mem hdD)] at h2

theorem exists_elemAbelian_eight_lift (ψ : Y →* Q) (hψ : Function.Surjective ψ)
    (hker : Odd (Nat.card ψ.ker)) {Ab : Subgroup Q} (hAb : CFSG.Open.IsElemAbelian 2 Ab)
    (hAb8 : Nat.card Ab = 8) : ∃ A : Subgroup Y, CFSG.Open.IsElemAbelian 2 A ∧ Nat.card A = 8 := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hAb2 : IsPGroup 2 Ab := IsPGroup.of_card (n := 3) (by rw [hAb8]; norm_num)
  obtain ⟨P, hP2, -, hPmap⟩ := exists_pSubgroup_lift_of_surjective ψ hψ (A₀ := ⊥)
    IsPGroup.of_bot hAb2 (by rw [Subgroup.map_bot]; exact bot_le)
  have hinj := CFSG.RankThree.OddKernel.injective_restrict_of_odd ψ hker hP2
  have hinjP : ∀ a ∈ P, ∀ b ∈ P, ψ a = ψ b → a = b := fun a ha b hb hab =>
    congrArg Subtype.val (hinj (a₁ := ⟨a, ha⟩) (a₂ := ⟨b, hb⟩) hab)
  have hsq : ∀ x ∈ P, x ^ 2 = 1 := fun x hx => by
    refine hinjP _ (pow_mem hx 2) 1 (one_mem P) ?_
    rw [map_pow, map_one]
    exact hAb.2 (ψ x) (by rw [← hPmap]; exact mem_map_of_mem ψ hx)
  have hcomm : ∀ a ∈ P, ∀ b ∈ P, a * b = b * a := fun a ha b hb => by
    have h1 : (a * b) * (a * b) = 1 := by rw [← sq]; exact hsq _ (mul_mem ha hb)
    have ha' : a⁻¹ = a := inv_eq_of_mul_eq_one_right (by rw [← sq]; exact hsq a ha)
    have hb' : b⁻¹ = b := inv_eq_of_mul_eq_one_right (by rw [← sq]; exact hsq b hb)
    calc a * b = (a * b)⁻¹ := (inv_eq_of_mul_eq_one_right h1).symm
      _ = b⁻¹ * a⁻¹ := mul_inv_rev a b
      _ = b * a := by rw [ha', hb']
  refine ⟨P, ⟨⟨⟨fun a b => Subtype.ext (hcomm a a.2 b b.2)⟩⟩, hsq⟩, ?_⟩
  have he : P.map ψ = (⊤ : Subgroup P).map (ψ.comp P.subtype) := by
    rw [← Subgroup.map_map, ← MonoidHom.range_eq_map, Subgroup.range_subtype]
  rw [← Subgroup.card_top (G := P), ← Subgroup.card_map_of_injective hinj, ← he, hPmap, hAb8]

theorem reflTransGen_of_twoConnected_quot (ψ : Y →* Q) (hψ : Function.Surjective ψ)
    (hker : Odd (Nat.card ψ.ker)) (hQ : ¬ IsTwoDisconnected Q) {A : Subgroup Y}
    (hA : CFSG.Open.IsElemAbelian 2 A) (hA8 : Nat.card A = 8) {E F : Subgroup Y}
    (hE : IsKleinFour E) (hF : IsKleinFour F) : Relation.ReflTransGen (CommFourAdj Y) E F := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hsq : ∀ a ∈ A, a * a = 1 := fun a ha => by rw [← sq]; exact hA.2 a ha
  have hAc : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a := fun a ha b hb => by
    have h1 := hsq (a * b) (mul_mem ha hb)
    have ha' : a⁻¹ = a := inv_eq_of_mul_eq_one_right (hsq a ha)
    have hb' : b⁻¹ = b := inv_eq_of_mul_eq_one_right (hsq b hb)
    calc a * b = (a * b)⁻¹ := (inv_eq_of_mul_eq_one_right h1).symm
      _ = b⁻¹ * a⁻¹ := mul_inv_rev a b
      _ = b * a := by rw [ha', hb']
  have hAr3 : 3 ≤ CFSG.Open.pRank 2 A := by
    refine le_csSup ⟨Nat.card Y, fun j hj => ?_⟩ ⟨A, le_rfl, hA, by rw [hA8]; norm_num⟩
    obtain ⟨F, -, -, hF⟩ := hj
    have h1 : j < 2 ^ j := Nat.lt_pow_self (by norm_num)
    have h2 : Nat.card F ≤ Nat.card Y := Subgroup.card_le_card_group F
    omega
  have hAr : 2 ≤ CFSG.Open.pRank 2 A := by omega
  obtain ⟨s, hsA, hs2⟩ := exists_orderOf_eq_two_of_pRank ((by norm_num : 1 ≤ 2).trans hAr)
  obtain ⟨E₀, hE₀A, hE₀, -⟩ := exists_isKleinFour_mem hAr hsA hs2
  let L : Subgroup Y :=
    { carrier := {g | Relation.ReflTransGen (CommFourAdj Y) E₀
        (E₀.map (MulAut.conj g).toMonoidHom)}
      one_mem' := by
        show Relation.ReflTransGen _ E₀ (E₀.map (MulAut.conj (1 : Y)).toMonoidHom)
        exact (congrArg (Relation.ReflTransGen (CommFourAdj Y) E₀) (map_conj_one_l39 E₀)).mpr
          Relation.ReflTransGen.refl
      mul_mem' := fun {g h} hg hh => by
        show Relation.ReflTransGen _ E₀ (E₀.map (MulAut.conj (g * h)).toMonoidHom)
        rw [← map_conj_map_conj_l39 E₀ g h]
        exact hg.trans (reflTransGen_commFourAdj_map_conj hh g)
      inv_mem' := fun {g} hg => by
        show Relation.ReflTransGen _ E₀ (E₀.map (MulAut.conj g⁻¹).toMonoidHom)
        have h := reflTransGen_commFourAdj_map_conj hg g⁻¹
        rw [map_conj_map_conj_l39 E₀ g⁻¹ g, inv_mul_cancel, map_conj_one_l39 E₀] at h
        exact reflTransGen_commFourAdj_symm h }
  have hkerL : ψ.ker ≤ L := by
    refine le_of_forall_inf_centralizer_le hker
      (le_normalizer_of_normal_l39 (MonoidHom.normal_ker ψ) A) hA hA8 fun H hHA hH => ?_
    rintro c ⟨-, hc⟩
    show Relation.ReflTransGen (CommFourAdj Y) E₀ (E₀.map (MulAut.conj c).toMonoidHom)
    have hE₀H : CommFourAdj Y E₀ H := ⟨hE₀, hH, fun e he => mem_centralizer_iff.mpr fun h hh =>
      hAc h (hHA hh) e (hE₀A he)⟩
    have hHc : H.map (MulAut.conj c).toMonoidHom = H := by
      ext x
      constructor
      · rintro ⟨y, hy, rfl⟩
        have hyc : c * y = y * c := (mem_centralizer_iff.mp hc y hy).symm
        simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
        rw [hyc, mul_assoc, mul_inv_cancel, mul_one]
        exact hy
      · intro hx
        refine ⟨x, hx, ?_⟩
        have hxc : c * x = x * c := (mem_centralizer_iff.mp hc x hx).symm
        simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
        rw [hxc, mul_assoc, mul_inv_cancel, mul_one]
    have h1 := reflTransGen_commFourAdj_map_conj (Relation.ReflTransGen.single hE₀H) c
    rw [hHc] at h1
    exact (Relation.ReflTransGen.single hE₀H).trans (reflTransGen_commFourAdj_symm h1)
  have hjoin : ∀ D : Subgroup Y, IsKleinFour D →
      Relation.ReflTransGen (CommFourAdj Y) E₀ D := by
    intro D hD
    have hc : Relation.ReflTransGen (CommFourAdj Q) (E₀.map ψ) (D.map ψ) := by
      by_contra hn
      exact hQ ⟨_, _, isKleinFour_map_of_odd_ker ψ hker hE₀,
        isKleinFour_map_of_odd_ker ψ hker hD, hn⟩
    obtain ⟨D₁, hD₁, hD₁map, hE₀D₁⟩ := exists_lift_reflTransGen_commFourAdj ψ hψ hker hE₀ hc
    obtain ⟨c, hcK, hcD⟩ := exists_ker_conj_eq ψ hker hD₁ hD hD₁map
    have h1 := reflTransGen_commFourAdj_map_conj hE₀D₁ c
    rw [hcD] at h1
    have h2 : Relation.ReflTransGen (CommFourAdj Y) E₀ (E₀.map (MulAut.conj c).toMonoidHom) :=
      hkerL hcK
    exact h2.trans h1
  exact (reflTransGen_commFourAdj_symm (hjoin E hE)).trans (hjoin F hF)

end Lift

variable {G : Type} [Group G] [Finite G] {N K : Subgroup G}

theorem reflTransGen_commFourIn_of_twoConnected {U : Subgroup G} (hU2 : IsPGroup 2 U)
    (hUQ : U ≤ coreActionKernel K) (hc : ¬ IsTwoDisconnected (coreQuot K))
    (h3 : 3 ≤ CFSG.Open.pRank 2 K) {E F : Subgroup G} (hE : IsKleinFour E)
    (hEX : E ≤ K ⊓ centralizer (U : Set G)) (hF : IsKleinFour F)
    (hFX : F ≤ K ⊓ centralizer (U : Set G)) :
    Relation.ReflTransGen (CommFourIn (K ⊓ centralizer (U : Set G))) E F := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set X := K ⊓ centralizer (U : Set G) with hXdef
  have hψs := coverQuot_surjective hU2 hUQ
  have hker := coverQuot_ker_odd (K := K) U
  have h3top : 3 ≤ CFSG.Open.pRank 2 (⊤ : Subgroup (coreQuot K)) := by
    rw [← SectionRank.pRank_eq_open_pRank_top, FooteLit.pRank_quotient_pPrimeCore, pRank_coe_eq]
    exact h3
  obtain ⟨Ab, -, hAb, hAb8⟩ :=
    CFSG.SectionRank.exists_isElemAbelian_card_of_le_pRank (p := 2) h3top
  obtain ⟨A, hA, hA8⟩ := exists_elemAbelian_eight_lift (coverQuot K U) hψs hker hAb
    (by rw [hAb8]; norm_num)
  have h := reflTransGen_commFourIn_of_subtype (reflTransGen_of_twoConnected_quot (coverQuot K U)
    hψs hker hc hA hA8 (isKleinFour_subgroupOf hE hEX) (isKleinFour_subgroupOf hF hFX))
  rwa [Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hEX, Subgroup.subgroupOf_map_subtype,
    inf_eq_left.mpr hFX] at h

theorem not_kDisc_of_twoConnected {K' V B : Subgroup G} (hP : SigPair N K K' V B)
    (hc : ¬ IsTwoDisconnected (coreQuot K)) (h3 : 3 ≤ CFSG.Open.pRank 2 K) :
    ¬ ∀ U E : Subgroup G, IsKleinFour U → U ≤ K' ⊓ centralizer (B : Set G) → IsKleinFour E →
      E ≤ B → E ≤ K →
      ¬ ∀ F : Subgroup G, IsKleinFour F → F ≤ K ⊓ centralizer (U : Set G) →
        Relation.ReflTransGen (CommFourIn (K ⊓ centralizer (U : Set G))) E F := by
  intro hdisc
  obtain ⟨hK, hK', hne, -, -, hBQ, -, hB, -, -, E, hE, hEB, hEK⟩ := hP
  have hB2 : IsPGroup 2 B := CFSG.SignalizerFunctor.Helpers.elementary_abelian_isPGroup 2 B hB
  obtain ⟨U, hU, hUY⟩ := exists_isKleinFour_inf_centralizer hK' hB2 hBQ
  have hUQ : U ≤ coreActionKernel K :=
    (hUY.trans inf_le_left).trans (le_coreActionKernel_of_ne hK hK' hne)
  have hEX : E ≤ K ⊓ centralizer (U : Set G) := le_inf hEK fun e he =>
    mem_centralizer_iff.mpr fun u hu => ((mem_centralizer_iff.mp (hUY hu).2) e (hEB he)).symm
  exact hdisc U E hU hUY hE hEB hEK fun F hF hFX =>
    reflTransGen_commFourIn_of_twoConnected (isPGroup_of_isKleinFour hU) hUQ hc h3 hE hEX hF hFX

@[expose] def Lemma39TwoDiscIAt (R : SigOrientation) : Prop :=
  ∀ (G : Type) [Group G] [Finite G], SimpleAmbient G → ∀ N : Subgroup G, IsSolomonChoice N →
    (kStarComponents N).ncard = 2 →
    ∀ K K' V B : Subgroup G, SigPair N K K' V B → R G N K K' → wGroup B V ≠ ⊥ →
      (K' ≤ normalizer (wGroup B V : Set G) →
        (CFSG.Open.pRank 2 K ≤ 2 ∨
          (IsTwoDisconnected (coreQuot K) ∧ IsSolomonI (coreQuot K))) →
        (∀ U E : Subgroup G, IsKleinFour U → U ≤ K' ⊓ centralizer (B : Set G) → IsKleinFour E →
          E ≤ B → E ≤ K →
          ¬ ∀ F : Subgroup G, IsKleinFour F → F ≤ K ⊓ centralizer (U : Set G) →
            Relation.ReflTransGen (CommFourIn (K ⊓ centralizer (U : Set G))) E F) →
        K ≤ normalizer (wGroup B V : Set G)) ∧
      ((∃ M : Subgroup (coreQuot K'), Assembly.Dichotomy.dichotomyStronglyEmbedded M) →
        (∀ E : Subgroup G, IsKleinFour E → E ≤ B → E ≤ K →
          ¬ (CFSG.Assembly.involutionGraph ↥(K' ⊓ centralizer (E : Set G))).Preconnected) →
        K' ≤ normalizer (wGroup B V : Set G))

section Certified

theorem not_isTwoDisconnected_coreQuot_of_not_isSolomonI (hBig : QuasisimpleBigCenterRankThree)
    (hSJ : QuasisimpleSylowFourJoinedSCN) (hG : SimpleAmbient G) (hK : K ∈ kStarComponents N)
    (h3 : 3 ≤ CFSG.Open.pRank 2 K) (hI : ¬ IsSolomonI (coreQuot K)) :
    ¬ IsTwoDisconnected (coreQuot K) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hO : pPrimeCore 2 (coreQuot K) = ⊥ :=
    CFSG.pPrimeCore_quotient_pPrimeCore_eq_bot (G := ↥K) 2
  have hq := isQuasisimple_quotient_of_isPComponent hK.1.1 hK.1.2
  have hcat :=
    catalog_coreQuotient_of_mem_solomonKStar (kStarKProper_of_simpleAmbient hG) hK.1 hK.2
  have h3' : 3 ≤ CFSG.Open.twoRank (coreQuot K) := by
    show 3 ≤ CFSG.Open.pRank 2 (⊤ : Subgroup (↥K ⧸ pPrimeCore 2 ↥K))
    rw [← SectionRank.pRank_eq_open_pRank_top, FooteLit.pRank_quotient_pPrimeCore,
      pRank_coe_eq]
    exact h3
  have h3'' : 3 ≤ CFSG.pRank 2 (coreQuot K) := by
    rw [FooteLit.pRank_quotient_pPrimeCore, pRank_coe_eq]
    exact h3
  obtain ⟨T⟩ : Nonempty (Sylow 2 (coreQuot K)) := inferInstance
  have hΓ := gamma_eq_top_of_not_isSolomonI hBig hq hO hcat
    (R12.isPGroup_center_of_pPrimeCore_eq_bot hO) h3' hI T
  exact not_isTwoDisconnected_of_gamma_eq_top T (fun E F hE hES hF hFS =>
    sylowFourJoined_of_SCN hSJ hq hO hcat h3'' T hE hES hF hFS) hΓ

theorem lemma39TwoDiscSEAt_of_I (hBig : QuasisimpleBigCenterRankThree)
    (hSJ : QuasisimpleSylowFourJoinedSCN) {R : SigOrientation} (h : Lemma39TwoDiscIAt R) :
    Lemma39TwoDiscSEAt R := by
  intro G _ _ hG N hN h2 K K' V B hP hR hW
  obtain ⟨h1, h2'⟩ := h G hG N hN h2 K K' V B hP hR hW
  refine ⟨fun hK'H hdisc => ?_, h2'⟩
  by_cases hr : CFSG.Open.pRank 2 K ≤ 2
  · exact h1 hK'H (Or.inl hr) hdisc
  have h3 : 3 ≤ CFSG.Open.pRank 2 K := by omega
  by_cases hc : IsTwoDisconnected (coreQuot K)
  · by_cases hI : IsSolomonI (coreQuot K)
    · exact h1 hK'H (Or.inr ⟨hc, hI⟩) hdisc
    · exact (not_isTwoDisconnected_coreQuot_of_not_isSolomonI hBig hSJ hG hP.1 h3 hI hc).elim
  · exact (not_kDisc_of_twoConnected hP hc h3 hdisc).elim

end Certified

end CFSG.ComponentClassification.Sol76.Sig
