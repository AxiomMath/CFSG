module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitLemma36Inputs
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit415Setup

public noncomputable section

namespace CFSG.ComponentClassification.HarrisLit

open CFSG Subgroup
open scoped MatrixGroups

namespace L36

theorem inClosure_mono {F F' : (Y : Type) → [Group Y] → Prop}
    (h : ∀ (Y : Type) [Group Y], F Y → F' Y) {X : Type} [Group X] (hX : InClosure F X) :
    InClosure F' X := by
  induction hX with
  | base hY => exact InClosure.base (h _ hY)
  | blowup _ hcat hb ih => exact InClosure.blowup ih hcat hb

theorem isOfType_chev_of_harrisF {p : ℕ} {K : Type*} [Group K] (h : IsOfType (HarrisF p) K) :
    IsOfType (InClosure (IsSimpleChevalleyOver p)) K := by
  obtain ⟨h2, Y, _, hY, he⟩ := h
  refine ⟨h2, Y, inferInstance, inClosure_mono (fun Y' _ hY' => ?_) hY, he⟩
  obtain ⟨n, -, hn⟩ := hY'
  exact ⟨.PSL, 2, n, hn⟩

theorem pPrimeCore_eq_bot {Y : Type} [Group Y] [Finite Y] (hq : IsQuasisimple Y)
    (hZ : IsPGroup 2 ↥(center Y)) : pPrimeCore 2 Y = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hn : (pPrimeCore 2 Y).Normal := pPrimeCore_normal
  rcases LocalAnalysis.ComponentInitial.quasisimple_normal_subgroups hq hn with h | h
  · exfalso
    have hodd : Odd (Nat.card Y) := by
      have h1 := pPrimeCore_coprime_card (p := 2) (G := Y)
      rw [h, card_top] at h1
      exact Nat.coprime_two_left.mp h1
    have hsolv := CFSG.FeitThompson.isSolvable_of_odd_natCard _ hodd
    have : Group.IsPerfect Y := hq.1
    have := LocalCores.isQuasisimple_nontrivial hq
    exact Group.IsPerfect.not_isSolvable Y hsolv
  · rw [eq_bot_iff]
    intro x hx
    rw [mem_bot]
    have hxZ := h hx
    obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.mp hZ) ⟨x, hxZ⟩
    rw [Subgroup.orderOf_mk] at hk
    have hdvd : orderOf x ∣ Nat.card (pPrimeCore 2 Y) := Subgroup.orderOf_dvd_natCard _ hx
    have hodd : Odd (Nat.card (pPrimeCore 2 Y)) :=
      Nat.coprime_two_left.mp pPrimeCore_coprime_card
    have h1 := hodd.of_dvd_nat hdvd
    rw [hk] at h1
    rcases k with _ | k
    · rw [pow_zero, orderOf_eq_one_iff] at hk
      exact hk
    · exfalso
      rw [pow_succ] at h1
      exact (Nat.not_odd_iff_even.mpr (Even.mul_left even_two _)) h1

theorem single_of_lieModel_layerIn {G : Type} [Group G] [Finite G] {C : Subgroup G} {p m : ℕ}
    (hp2 : p ≠ 2) (hL : Blueprint.LieModel ↥(GSThmB.layerIn C) .PSL 2 p m) :
    IsTwoComponentIn (GSThmB.layerIn C) C ∧
      (∀ K' : Subgroup G, IsTwoComponentIn K' C → K' = GSThmB.layerIn C) ∧
      Blueprint.LieModel (↥(GSThmB.layerIn C) ⧸ pPrimeCore 2 ↥(GSThmB.layerIn C)) .PSL 2 p m := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set P := pLayer ↥C 2 with hPdef
  have hEC : GSThmB.layerIn C ≤ C := map_subtype_le P
  have hEP : (GSThmB.layerIn C).subgroupOf C = P := subgroupOf_map_subtype_eq P
  obtain ⟨hs, hnab⟩ := L415.simple_nonabelian_of_lieModel hL
  have heven := even_card_of_lieModel_psl2 hp2 hL
  have hOE : pPrimeCore 2 ↥(GSThmB.layerIn C) = ⊥ := by
    have : (pPrimeCore 2 ↥(GSThmB.layerIn C)).Normal := pPrimeCore_normal
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (pPrimeCore 2 ↥(GSThmB.layerIn C)) with h | h
    · exact h
    · exfalso
      have h1 := pPrimeCore_coprime_card (p := 2) (G := ↥(GSThmB.layerIn C))
      rw [h, card_top] at h1
      exact (Nat.not_even_iff_odd.mpr (Nat.coprime_two_left.mp h1)) heven
  let eP : ↥P ≃* ↥(GSThmB.layerIn C) := P.equivMapOfInjective C.subtype C.subtype_injective
  have : IsSimpleGroup ↥P := eP.isSimpleGroup
  have hall : ∀ J : Subgroup ↥C, IsPComponent 2 J → J = P := by
    intro J hJ
    have hJP : J ≤ P := le_sSup (s := {L : Subgroup ↥C | IsPComponent 2 L}) hJ
    have hJsub : J.IsSubnormal := hJ.choose_spec.2.1
    have hsn := GorensteinWalter.isSubnormal_subgroupOf_of_subnormal_of_le hJP hJsub
    rcases Subgroup.IsSubnormal.eq_bot_or_top_of_isSimpleGroup inferInstance hsn with h | h
    · exfalso
      have hJn := CatalogueBAlternating.pComponent_nontrivial hJ
      apply (Subgroup.nontrivial_iff_ne_bot J).mp hJn
      rw [eq_bot_iff]
      intro x hx
      have h1 : (⟨x, hJP hx⟩ : ↥P) ∈ J.subgroupOf P := hx
      rw [h, mem_bot] at h1
      exact (mem_bot).mpr (congrArg Subtype.val h1)
    · refine le_antisymm hJP fun x hx => ?_
      have h1 : (⟨x, hx⟩ : ↥P) ∈ J.subgroupOf P := by rw [h]; trivial
      exact h1
  have hPc : IsPComponent 2 P := by
    by_contra hno
    have hbot : P = ⊥ := by
      rw [hPdef, pLayer, eq_bot_iff]
      refine sSup_le fun J hJ => ?_
      exact absurd (hall J hJ ▸ hJ) hno
    have hEbot : GSThmB.layerIn C = ⊥ := by
      change P.map C.subtype = ⊥
      rw [hbot, Subgroup.map_bot]
    obtain ⟨a, b, hab⟩ := hnab
    apply hab
    have ha := (Subgroup.eq_bot_iff_forall _).mp hEbot (a : G) a.2
    have hb := (Subgroup.eq_bot_iff_forall _).mp hEbot (b : G) b.2
    exact Subtype.ext (by simp only [Subgroup.coe_mul, ha, hb])
  refine ⟨(isTwoComponentIn_iff hEC).mpr (hEP ▸ hPc), fun K' hK' => ?_, ?_⟩
  · have h1 := hall _ ((isTwoComponentIn_iff hK'.1).mp hK')
    rw [← hEP] at h1
    have h2 := (Subgroup.subgroupOf_inj).mp h1
    rwa [inf_of_le_left hK'.1, inf_of_le_left hEC] at h2
  · exact lieModel_psl2_of_mulEquiv
      ((QuotientGroup.quotientMulEquivOfEq hOE).trans QuotientGroup.quotientBot) hL

theorem sq_ne_one_of_genFitting {Y : Type} [Group Y] [Finite Y]
    (hZ2 : Nat.card ↥(center Y) = 2) {τ : MulAut Y} (hτ : orderOf τ = 2)
    (hF : Nonempty (↥(generalizedFitting ↥(fixedPoints τ)) ≃*
      Multiplicative (ZMod 4) × ↥(alternatingGroup (Fin 6))))
    (e : Y) (he : MulAut.conj e = τ) : e ^ 2 ≠ 1 := by
  intro he2
  obtain ⟨φ⟩ := hF
  have hconj : ∀ y : Y, τ y = e * y * e⁻¹ := fun y => by rw [← he]; rfl
  have hcen : ∀ (c : Y) (hcC : c ∈ fixedPoints τ), (∀ y ∈ fixedPoints τ, c * y = y * c) →
      ∃ hcF : (⟨c, hcC⟩ : ↥(fixedPoints τ)) ∈ generalizedFitting ↥(fixedPoints τ),
        (φ ⟨_, hcF⟩).2 = 1 := by
    intro c hcC hc
    have hcF : (⟨c, hcC⟩ : ↥(fixedPoints τ)) ∈ generalizedFitting ↥(fixedPoints τ) :=
      centralizer_generalizedFitting_le ↥(fixedPoints τ)
        (mem_centralizer_iff.mpr fun y _ => Subtype.ext (hc y y.2).symm)
    refine ⟨hcF, ?_⟩
    have hZ6 : center ↥(alternatingGroup (Fin 6)) = ⊥ :=
      alternatingGroup.center_eq_bot (by simp)
    have hmem : (φ ⟨_, hcF⟩).2 ∈ center ↥(alternatingGroup (Fin 6)) := by
      rw [mem_center_iff]
      intro g
      have h1 : φ.symm (1, g) * ⟨_, hcF⟩ = ⟨_, hcF⟩ * φ.symm (1, g) := by
        apply Subtype.ext
        apply Subtype.ext
        exact (hc _ (φ.symm (1, g) : ↥(fixedPoints τ)).2).symm
      have h2 := congrArg φ h1
      rw [map_mul, map_mul, MulEquiv.apply_symm_apply] at h2
      exact congrArg Prod.snd h2
    rw [hZ6, mem_bot] at hmem
    exact hmem
  have heC : e ∈ fixedPoints τ := by
    rw [mem_fixedPoints, hconj]
    group
  have hec : ∀ y ∈ fixedPoints τ, e * y = y * e := by
    intro y hy
    have h1 : e * y * e⁻¹ = y := by rw [← hconj]; exact hy
    calc e * y = e * y * e⁻¹ * e := by group
      _ = y * e := by rw [h1]
  obtain ⟨c₀, hc₀Z, hc₀1⟩ : ∃ c₀ ∈ center Y, c₀ ≠ 1 := by
    by_contra h
    push Not at h
    have : center Y = ⊥ := by
      rw [eq_bot_iff]
      intro x hx
      exact (mem_bot).mpr (h x hx)
    rw [this, card_bot] at hZ2
    norm_num at hZ2
  have hc₀2 : c₀ ^ 2 = 1 := by
    have h1 := Subgroup.orderOf_dvd_natCard (center Y) hc₀Z
    rw [hZ2] at h1
    exact orderOf_dvd_iff_pow_eq_one.mp h1
  have hc₀C : c₀ ∈ fixedPoints τ := by
    rw [mem_fixedPoints, hconj, mem_center_iff.mp hc₀Z e]
    group
  have hc₀c : ∀ y ∈ fixedPoints τ, c₀ * y = y * c₀ := fun y _ => (mem_center_iff.mp hc₀Z y).symm
  obtain ⟨heF, he2'⟩ := hcen e heC hec
  obtain ⟨hc₀F, hc₀2'⟩ := hcen c₀ hc₀C hc₀c
  have he1 : e ≠ 1 := by
    intro h
    rw [h, map_one] at he
    rw [← he, orderOf_one] at hτ
    norm_num at hτ
  have hinv : ∀ x y : Multiplicative (ZMod 4), x ^ 2 = 1 → x ≠ 1 → y ^ 2 = 1 → y ≠ 1 → x = y := by
    decide
  have hφe : (φ ⟨_, heF⟩) ^ 2 = 1 := by
    rw [← map_pow]
    have : (⟨⟨e, heC⟩, heF⟩ : ↥(generalizedFitting ↥(fixedPoints τ))) ^ 2 = 1 :=
      Subtype.ext (Subtype.ext he2)
    rw [this, map_one]
  have hφc : (φ ⟨_, hc₀F⟩) ^ 2 = 1 := by
    rw [← map_pow]
    have : (⟨⟨c₀, hc₀C⟩, hc₀F⟩ : ↥(generalizedFitting ↥(fixedPoints τ))) ^ 2 = 1 :=
      Subtype.ext (Subtype.ext hc₀2)
    rw [this, map_one]
  have hne1 : ∀ (c : Y) (hcC : c ∈ fixedPoints τ)
      (hcF : (⟨c, hcC⟩ : ↥(fixedPoints τ)) ∈ generalizedFitting ↥(fixedPoints τ)),
      c ≠ 1 → (φ ⟨_, hcF⟩).2 = 1 → (φ ⟨_, hcF⟩).1 ≠ 1 := by
    intro c hcC hcF hc1 h2 h1
    apply hc1
    have h3 : φ ⟨_, hcF⟩ = 1 := Prod.ext h1 h2
    have h4 := congrArg Subtype.val (congrArg Subtype.val (φ.injective (h3.trans (map_one φ).symm)))
    exact h4
  have heq1 := hinv _ _ (congrArg Prod.fst hφe) (hne1 e heC heF he1 he2')
    (congrArg Prod.fst hφc) (hne1 c₀ hc₀C hc₀F hc₀1 hc₀2')
  have heq : φ ⟨_, heF⟩ = φ ⟨_, hc₀F⟩ := Prod.ext heq1 (by rw [he2', hc₀2'])
  have hec₀ : e = c₀ := congrArg Subtype.val (congrArg Subtype.val (φ.injective heq))
  have hτ1 : τ = 1 := by
    rw [← he, hec₀]
    ext y
    simp [MulAut.conj_apply, (mem_center_iff.mp hc₀Z y).symm]
  rw [hτ1, orderOf_one] at hτ
  norm_num at hτ

end L36

theorem harris36NonsimpleInput_of_printed (h : Harris81Lemma36NonsimpleInput) :
    Harris36NonsimpleInput := by
  intro Y _ _ hq hns hZ p m hp hp2 hm h16 hF hnM τ hτ hK
  have hO := L36.pPrimeCore_eq_bot hq hZ
  obtain ⟨hKc, huniq, hKL⟩ := L36.single_of_lieModel_layerIn hp2 hK
  rcases h Y hq hO p hp hp2 (L36.isOfType_chev_of_harrisF hF) τ hτ m hm h16 _ hKc huniq hKL hns
    hnM with ⟨hJ2, hZ2, hout⟩ | ⟨hHS, hZ2, hFst, hin⟩ | ⟨hL34, hZ16, hout⟩ | ⟨k, hmk, hL⟩
  · exact Or.inl ⟨hJ2, hZ2, hout⟩
  · exact Or.inr (Or.inl ⟨hHS, hZ2, hin, fun e he => L36.sq_ne_one_of_genFitting hZ2 hτ hFst e he⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨hL34, hZ16, hout⟩))
  · exact Or.inr (Or.inr (Or.inr ⟨k, by omega, hL⟩))

end CFSG.ComponentClassification.HarrisLit
