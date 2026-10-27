module

public import CFSG.Quasithin.H13.A5W1620Tb
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.A5W1622r

public section

namespace CFSG.Quasithin.H13.A5

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin

namespace Setting

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G] {T L V : Subgroup G} (S : Setting G T L V)

theorem kbar_center_cases_F4 (h1222 : Stmt12_2_2_F4)
    (h517 : Stmt5_1_7_one_F4) (hF : CharTwo (Subgroup.centralizer ({S.v12} : Set G)))
    (h36 : A36ForSQTK) (h37 : Vol2Native.A37ForSQTKCat) (h38 : Vol2Native.A38ForSQTKCat)
    {K : Subgroup G} (hK : K ∈ cComp (Subgroup.centralizer ({S.v12} : Set G)))
    (hYz : S.InYz K) (hT : S.Tv ≤ Subgroup.normalizer (K : Set G))
    (hN : Nat.card (↥(S.plus K) ⧸ Subgroup.center ↥(S.plus K)) = 360 ∨
      Nat.card (↥(S.plus K) ⧸ Subgroup.center ↥(S.plus K)) = 2520 ∨
      Nat.card (↥(S.plus K) ⧸ Subgroup.center ↥(S.plus K)) = 6048) :
    Subgroup.center (↥K ⧸ CFSG.pCore 2 ↥K) = ⊥ ∨
      Nat.card (Subgroup.center (↥K ⧸ CFSG.pCore 2 ↥K)) = 3 := by
  have hLv := S.Lv_le_normalizer_of_mem_cComp_F4 h1222 h517 h37 h38 hK
  obtain ⟨π, hπ⟩ := S.exists_kbar_plus_F4 h1222 h517 hF hYz.1 hT hLv
  have hq := S.isQuasisimple_plus_F4 h1222 h517 hF hYz hT
  set Gv := Subgroup.centralizer ({S.v12} : Set G) with hGv
  obtain ⟨ψ, hψs, hψk⟩ := exists_modO2_surjection hK
  let eX : ↥K ⧸ CFSG.pCore 2 ↥K ≃* ↥(modO2Image Gv K) :=
    (QuotientGroup.quotientMulEquivOfEq hψk.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective ψ hψs)
  let πX : ↥(modO2Image Gv K) →* ↥(S.plus K) := π.comp eX.symm.toMonoidHom
  have hπX : Function.Surjective πX := hπ.comp eX.symm.surjective
  have hcen : Nat.card (Subgroup.center (↥K ⧸ CFSG.pCore 2 ↥K)) =
      Nat.card (Subgroup.center ↥(modO2Image Gv K)) :=
    Nat.card_congr (Subgroup.centerCongr eX).toEquiv
  have hA := lemma_1_2_1_four S.h13.qtke S.h13.simple S.h13.nonabelian h36
    (S.pCoreOf_Gv_ne_bot_F4 h1222 h517 hF) hK
  rcases hA with ⟨hcomp, hsimp, -⟩ | ⟨-, h3, -⟩ | h3 | h4
  ·
    left
    have hZ : Subgroup.center ↥(modO2Image Gv K) = ⊥ := by
      rcases hsimp.eq_bot_or_eq_top_of_normal (Subgroup.center ↥(modO2Image Gv K)) with h | h
      · exact h
      · exfalso
        obtain ⟨-, -, a, b, hab⟩ := hcomp.1
        apply hab
        obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective a
        obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective b
        rw [(QuotientGroup.eq_one_iff a).mpr (h ▸ Subgroup.mem_top a),
          (QuotientGroup.eq_one_iff b).mpr (h ▸ Subgroup.mem_top b)]
    rw [hZ, Subgroup.card_bot] at hcen
    exact Subgroup.card_eq_one.mp hcen
  ·
    right
    rw [hcen, h3]
  ·
    exfalso
    obtain ⟨p, hp, hp3, -, ⟨eF⟩, hnat⟩ := h3
    obtain ⟨-, ψ₃, hψ₃s, hψ₃k, -⟩ := hnat
    have hFs : Group.IsSolvable ↥(CFSG.fittingSubgroup ↥(modO2Image Gv K)) := by
      have : IsMulCommutative (Multiplicative (Fin 2 → ZMod p)) := inferInstance
      exact Group.isSolvable_of_surjective (f := eF.symm.toMonoidHom) eF.symm.surjective
    have hp5 : 5 ≤ p := by
      have h4 : p ≠ 4 := fun h => by rw [h] at hp; norm_num at hp
      omega
    obtain ⟨c, hc1, hc2, hcard⟩ := card_of_sl2_quotient hq πX hπX hFs hp hp5 ψ₃ hψ₃s hψ₃k
    have h168 := (prime_eq_seven_of_sl2 hp hp3 hc1 hc2 (Or.inr hN) hcard).1
    rcases hN with h | h | h <;> omega
  ·
    exfalso
    obtain ⟨-, hnil, ⟨e5⟩, -⟩ := h4
    have hFs : Group.IsSolvable ↥(CFSG.fittingSubgroup ↥(modO2Image Gv K)) := inferInstance
    let ψ₄ := e5.toMonoidHom.comp (QuotientGroup.mk' (CFSG.fittingSubgroup ↥(modO2Image Gv K)))
    have hψ₄ : Function.Surjective ψ₄ := e5.surjective.comp (QuotientGroup.mk'_surjective _)
    have hψ₄k : ψ₄.ker = CFSG.fittingSubgroup ↥(modO2Image Gv K) := by
      ext x
      simp [ψ₄]
    obtain ⟨c, hc1, hc2, hcard⟩ := card_of_sl2_quotient hq πX hπX hFs Nat.prime_five le_rfl ψ₄
      hψ₄ hψ₄k
    rcases hN with h | h | h <;> rw [h] at hcard <;> omega

theorem Lv_le_of_exclusion_F4 (h1222 : Stmt12_2_2_F4)
    (h517 : Stmt5_1_7_one_F4) (hF318 : A318Facts) (h36 : A36ForSQTK)
    (h37 : Vol2Native.A37ForSQTKCat) (h38 : Vol2Native.A38ForSQTKCat)
    (hF : CharTwo (Subgroup.centralizer ({S.v12} : Set G))) {K : Subgroup G}
    (hK : K ∈ cComp (Subgroup.centralizer ({S.v12} : Set G))) (hYz : S.InYz K)
    (hT : S.Tv ≤ Subgroup.normalizer (K : Set G))
    (hq : CFSG.IsQuasisimple (↥K ⧸ CFSG.pCore 2 ↥K)) {X : Type} [Group X] [Finite X]
    (hX : A318Exclusion X) (e : ↥(S.plus K) ⧸ Subgroup.center ↥(S.plus K) ≃* X)
    (hcard : Nat.card X = 360 ∨ Nat.card X = 2520 ∨ Nat.card X = 6048) : S.Lv ≤ K := by
  have hLv := S.Lv_le_normalizer_of_mem_cComp_F4 h1222 h517 h37 h38 hK
  obtain ⟨π, hπ⟩ := S.exists_kbar_plus_F4 h1222 h517 hF hYz.1 hT hLv
  have hqP := S.isQuasisimple_plus_F4 h1222 h517 hF hYz hT
  have hnt : Nontrivial ↥(S.plus K) := by
    obtain ⟨a, b, hab⟩ := hqP.2.2
    obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective a
    obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective b
    exact ⟨⟨a, b, fun h => hab (by rw [h])⟩⟩
  have hker := ker_le_center_of_isQuasisimple hq π hπ hnt
  have : Group.IsPerfect (↥K ⧸ CFSG.pCore 2 ↥K) := hq.1
  let eA : (↥K ⧸ CFSG.pCore 2 ↥K) ⧸ Subgroup.center (↥K ⧸ CFSG.pCore 2 ↥K) ≃* X :=
    (centerQuotEquiv π hπ hker).trans e
  have hN : Nat.card (↥(S.plus K) ⧸ Subgroup.center ↥(S.plus K)) = Nat.card X :=
    Nat.card_congr e.toEquiv
  have hGv : SQTKGroup ↥(Subgroup.centralizer ({S.v12} : Set G)) :=
    sqtkGroup_of_pCoreOf_ne_bot S.h13.qtke S.h13.simple S.h13.nonabelian
      (S.pCoreOf_Gv_ne_bot_F4 h1222 h517 hF)
  have h38' : A38ForSQTK := a38ForSQTK_of_cat h38
  refine S.Lv_le_of_eq_oPrime_or_theta ?_
  rcases S.kbar_center_cases_F4 h1222 h517 hF h36 h37 h38 hK hYz hT (hN ▸ hcard) with hZ | hZ3
  ·
    left
    exact eq_oPrimeResidualOf_three_of_exclusion hF318 h36 h38' hGv hK hq
      ((quotCenterEquivOfEqBot hZ).symm.trans eA) hX
  ·
    exact eq_oPrime_or_theta_of_center_three hF318 h36 h38' hGv hK hq hZ3 hX eA
      (fun q hq2 => sl3_su3_card_ne hq2 (by rcases hcard with h | h | h <;> rw [h] <;> norm_num))

theorem Lv_le_of_rankTwo_F4
    (h1222 : Stmt12_2_2_F4) (h517 : Stmt5_1_7_one_F4)
    (hF318 : A318Facts) (h36 : A36ForSQTK) (h37 : Vol2Native.A37ForSQTKCat)
    (h38 : Vol2Native.A38ForSQTKCat) (hKF : KnownFacts15122Types)
    (hF : CharTwo (Subgroup.centralizer ({S.v12} : Set G))) {K : Subgroup G}
    (hK : K ∈ cComp (Subgroup.centralizer ({S.v12} : Set G))) (hYz : S.InYz K)
    (hT : S.Tv ≤ Subgroup.normalizer (K : Set G))
    (hq : CFSG.IsQuasisimple (↥K ⧸ CFSG.pCore 2 ↥K))
    (h : IsAlt 6 ↥(S.plus K) ∨
      (∃ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = 2 ∧
        Nonempty (↥(S.plus K) ≃* ↥⁅CFSG.Open.quasithinG2 F, CFSG.Open.quasithinG2 F⁆)) ∨
      IsHat ↥(S.plus K) ↥(alternatingGroup (Fin 6)) ∨ IsAlt 7 ↥(S.plus K)) : S.Lv ≤ K := by
  rcases h with h6 | h2 | hh | h7
  ·
    obtain ⟨e6⟩ := id h6
    have hZ := SBc11.center_eq_bot_of_list (Or.inr (Or.inl h6))
    exact S.Lv_le_of_exclusion_F4 h1222 h517 hF318 h36 h37 h38 hF hK hYz hT hq hKF.alt6
      ((quotCenterEquivOfEqBot hZ).trans e6)
      (Or.inl (SBc11.card_of_isAlt_six ⟨MulEquiv.refl _⟩))
  ·
    have hU := SBd8.trioIsPSU33 h2
    have hZ := SBc11.center_eq_bot_of_list (Or.inr (Or.inr hU))
    exact S.Lv_le_of_exclusion_F4 h1222 h517 hF318 h36 h37 h38 hF hK hYz hT hq (hKF.u33 _ hU)
      (quotCenterEquivOfEqBot hZ) (Or.inr (Or.inr (SBc11.card_of_isPSU_three_three hU)))
  ·
    obtain ⟨-, -, ⟨e6⟩⟩ := hh
    exact S.Lv_le_of_exclusion_F4 h1222 h517 hF318 h36 h37 h38 hF hK hYz hT hq hKF.alt6 e6
      (Or.inl (SBc11.card_of_isAlt_six ⟨MulEquiv.refl _⟩))
  ·
    obtain ⟨e7⟩ := id h7
    have hs7 : IsSimpleGroup (alternatingGroup (Fin 7)) :=
      alternatingGroup.isSimpleGroup (by simp)
    have hsP : IsSimpleGroup ↥(S.plus K) := e7.isSimpleGroup
    have hZ : Subgroup.center ↥(S.plus K) = ⊥ := by
      rcases hsP.eq_bot_or_eq_top_of_normal (Subgroup.center ↥(S.plus K)) with hc | hc
      · exact hc
      · exfalso
        obtain ⟨-, -, a, b, hab⟩ := S.isQuasisimple_plus_F4 h1222 h517 hF hYz hT
        apply hab
        obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective a
        obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective b
        rw [(QuotientGroup.eq_one_iff a).mpr (hc ▸ Subgroup.mem_top a),
          (QuotientGroup.eq_one_iff b).mpr (hc ▸ Subgroup.mem_top b)]
    have h2520 : Nat.card (alternatingGroup (Fin 7)) = 2520 := by
      rw [nat_card_alternatingGroup, Nat.card_eq_fintype_card, Fintype.card_fin]
      norm_num [Nat.factorial]
    exact S.Lv_le_of_exclusion_F4 h1222 h517 hF318 h36 h37 h38 hF hK hYz hT hq hKF.alt7
      ((quotCenterEquivOfEqBot hZ).trans e7) (Or.inr (Or.inl h2520))

end Setting

end CFSG.Quasithin.H13.A5
