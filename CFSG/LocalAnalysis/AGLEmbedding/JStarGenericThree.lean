module

public import CFSG.LocalAnalysis.AGLEmbedding.JStarGenericFacts
public import CFSG.LocalAnalysis.AGLEmbedding.CaseThreeFamiliesAux
public import CFSG.LocalAnalysis.ComponentClassification.BMCaseGeneric

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.PreuniquenessRankFour.Helpers
open CFSG.RankThreeCoreUniqueness.Helpers
open scoped commutatorElement
open CFSG.ComponentClassification.OuterAutomorphisms

open CFSG.ComponentClassification in
theorem JStarHypOf.center_quotient_action {Y : Type} [Group Y] [Finite Y] {p B : ℕ}
    [Fact p.Prime] {Rb : Sylow p Y} {Y₀ Jt Xt : Subgroup Y} {L : Type} [Group L] [Finite L]
    {φ : Jt →* L} (h : JStarHypOf p Rb Y₀ Jt Xt L B φ) (hT : JStarTargetBase p B L)
    {K : Subgroup Y} (hK : IsComponentOf K ⊤)
    (huniq : ∀ L' : Subgroup Y, IsComponentOf L' ⊤ → L' = K)
    (hcent : ∀ c ∈ (Rb : Subgroup Y) ⊓ Subgroup.centralizer (K : Set Y), orderOf c = p →
      c ∈ (Subgroup.center K).map K.subtype) :
    ∃ ρ : Y →* MulAut (K ⧸ Subgroup.center K),
      (∀ k : K, ρ k = MulAut.conj (QuotientGroup.mk' (Subgroup.center K) k)) ∧
      ρ.ker ≤ Subgroup.centralizer (K : Set Y) ∧
      IsPGroup p (Subgroup.centralizer (K : Set Y)) ∧ Jt ⊓ ρ.ker = ⊥ ∧
      JStarElimDataOf (K ⧸ Subgroup.center K) p B L := by
  have hp : p.Prime := Fact.out
  have hKn : K.Normal := normal_of_forall_isComponentOf_eq hK huniq
  have : Group.IsPerfect K := ⟨hK.2.2.1⟩
  have hmem : ∀ c ∈ Subgroup.centralizer (K : Set Y), orderOf c = p → c ∈ K :=
    fun c hc hcp => mem_of_mem_centralizer_of_orderOf_eq Rb hKn
      (fun c hc hcp => Subgroup.map_subtype_le _ (hcent c hc hcp)) hc hcp
  have hCp : IsPGroup p (Subgroup.centralizer (K : Set Y)) :=
    isPGroup_centralizer_of_forall_mem hp h.ne_two h.red.core_eq_bot hKn hmem
  let ρ : Y →* MulAut (K ⧸ Subgroup.center K) :=
    (PerfectAutomorphisms.centerQuotientHom K).comp MulAut.conjNormal
  have hρK : ∀ k : K, ρ k = MulAut.conj (QuotientGroup.mk' (Subgroup.center K) k) := by
    intro k
    rw [← OuterAutomorphisms.centerQuotient_conj]
    refine congrArg (PerfectAutomorphisms.centerQuotientHom K) ?_
    ext x
    simp [MulAut.conjNormal_apply, MulAut.conj_apply]
  have hker : ρ.ker ≤ Subgroup.centralizer (K : Set Y) := by
    intro y hy
    have h1 : MulAut.conjNormal y = (1 : MulAut K) :=
      PerfectAutomorphisms.centerQuotientHom_injective K (hy.trans (map_one _).symm)
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    have h2 := congrArg Subtype.val (DFunLike.congr_fun h1 ⟨x, hx⟩)
    simp only [MulAut.conjNormal_apply, MulAut.one_apply] at h2
    calc x * y = y * x * y⁻¹ * y := by rw [h2]
      _ = y * x := by group
  have hkerp : IsPGroup p ρ.ker := hCp.to_le hker
  have hinj : Jt ⊓ ρ.ker = ⊥ := by
    refine h.eq_bot_of_isPGroup hT inf_le_left ?_ (hkerp.to_le inf_le_right)
    exact (le_inf Subgroup.le_normalizer (by rw [Subgroup.normalizer_eq_top]; exact le_top)).trans
      Subgroup.inf_normalizer_le_normalizer_inf
  refine ⟨ρ, hρK, hker, hCp, hinj, ?_⟩
  have hinj' : Function.Injective (ρ.comp Jt.subtype) := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro x hx
    have hx' : (x : Y) ∈ Jt ⊓ ρ.ker := ⟨x.2, hx⟩
    rw [hinj, Subgroup.mem_bot] at hx'
    exact Subgroup.mem_bot.mpr (Subtype.ext hx')
  let e : Jt ≃* (ρ.comp Jt.subtype).range := MonoidHom.ofInjective hinj'
  refine ⟨ρ.range, (ρ.comp Jt.subtype).range, ?_, ?_, ?_, φ.comp e.symm.toMonoidHom,
    h.surj.comp e.symm.surjective, ?_⟩
  · rintro _ ⟨l, rfl⟩
    obtain ⟨k, rfl⟩ := QuotientGroup.mk'_surjective (Subgroup.center K) l
    exact ⟨k, hρK k⟩
  · rintro _ ⟨x, rfl⟩
    exact ⟨x, rfl⟩
  · intro S hS hSp
    calc Nat.card S = Nat.card ((S.comap ρ).map ρ) := by rw [Subgroup.map_comap_eq_self hS]
      _ ∣ Nat.card (S.comap ρ) := Subgroup.card_map_dvd _ _
      _ ∣ B := h.card_dvd _ (hSp.comap_of_ker_isPGroup ρ hkerp)
  · have hc : Nat.card (φ.comp e.symm.toMonoidHom).ker = Nat.card φ.ker :=
      Nat.card_congr (e.symm.toEquiv.subtypeEquiv fun _ => Iff.rfl)
    rw [hc]
    exact h.coprime

theorem le_of_isPerfect_of_isSolvable_quotient {Y : Type*} [Group Y] {J N : Subgroup Y}
    [N.Normal] (hJ : Group.IsPerfect J) (hQ : Group.IsSolvable (Y ⧸ N)) : J ≤ N := by
  intro j hj
  obtain ⟨k, hk⟩ := hQ.solvable
  have hmem : (⟨j, hj⟩ : J) ∈ derivedSeries J k := by
    rw [Group.IsPerfect.derivedSeries_eq_top]
    exact Subgroup.mem_top _
  have h2 := map_derivedSeries_le_derivedSeries ((QuotientGroup.mk' N).comp J.subtype) k
    ⟨_, hmem, rfl⟩
  rw [hk, Subgroup.mem_bot] at h2
  exact (QuotientGroup.eq_one_iff j).mp h2

open CFSG.ComponentClassification.OuterAutomorphisms in
theorem isSolvable_outer_congr {A B : Type*} [Group A] [Group B] (e : A ≃* B)
    (h : Group.IsSolvable (Outer B)) : Group.IsSolvable (Outer A) := by
  have hmap : (inner A).map (MulAut.congr e : MulAut A ≃* MulAut B).toMonoidHom = inner B := by
    ext β
    constructor
    · rintro ⟨_, ⟨a, rfl⟩, rfl⟩
      refine ⟨e a, ?_⟩
      ext b
      simp [MulAut.congr, MulAut.conj_apply]
    · rintro ⟨b, rfl⟩
      refine ⟨MulAut.conj (e.symm b), ⟨e.symm b, rfl⟩, ?_⟩
      ext x
      simp [MulAut.congr, MulAut.conj_apply]
  have : (inner A).Normal := inner_normal A
  have : (inner B).Normal := inner_normal B
  let f : Outer A ≃* Outer B := QuotientGroup.congr (inner A) (inner B) (MulAut.congr e) hmap
  exact Group.isSolvable_of_isSolvable_injective (f := f.toMonoidHom) f.injective

open CFSG.ComponentClassification.OuterAutomorphisms in
theorem jStarOfIII (hP1L : KFactP1ThreeLie) (hP1A : KFactP1ThreeAlt)
    (hP1S : KFactP1ThreeSpor) : StmtJStarOfIII := by
  intro Y _ _ p B _ Rb Y₀ Jt Xt L _ _ φ hT hE h K hK huniq hnc hcent
  have hp : p.Prime := Fact.out
  have hKn : K.Normal := normal_of_forall_isComponentOf_eq hK huniq
  obtain ⟨ρ, hρK, hker, hCp, hinj, hdata⟩ := h.center_quotient_action hT hK huniq hcent
  have hmem : ∀ c ∈ Subgroup.centralizer (K : Set Y), orderOf c = p → c ∈ K :=
    fun c hc hcp => mem_of_mem_centralizer_of_orderOf_eq Rb hKn
      (fun c hc hcp => Subgroup.map_subtype_le _ (hcent c hc hcp)) hc hcp
  have hKs : IsSimpleGroup (K ⧸ Subgroup.center K) := hK.2.2.2
  have hnab := ComponentClassification.Helpers.quasisimple_central_quotient_nonabelian K hK.2.2
  have hlist : (∃ d : TauCeti.ValidLieTypeIndex, P1ThreeLieList p d ∧
        Nonempty (K ⧸ Subgroup.center K ≃* (TauCeti.CFSGIndex.lie d).Group)) ∨
      Nonempty (K ⧸ Subgroup.center K ≃* alternatingGroup (Fin (3 * p))) ∨
      (∃ s : TauCeti.SporadicName, P1ThreeSporList p s ∧
        Nonempty (K ⧸ Subgroup.center K ≃* (TauCeti.CFSGIndex.sporadic s).Group)) := by
    obtain ⟨i, ⟨e⟩⟩ := h.catalog.isCatalogGroup_center_quotient hK
    cases i with
    | cyclic q hq => exact (not_nonempty_mulEquiv_zmod hnab ⟨e⟩).elim
    | alternating m hm =>
      obtain rfl := hP1A p Y Rb Y₀ h.red h.catalog K hK huniq hnc hcent m hm ⟨e⟩
      exact Or.inr (Or.inl ⟨e⟩)
    | lie d => exact Or.inl ⟨d, hP1L p Y Rb Y₀ h.red h.catalog K hK huniq hnc hcent d ⟨e⟩, ⟨e⟩⟩
    | sporadic s =>
      exact Or.inr (Or.inr ⟨s, hP1S p Y Rb Y₀ h.red h.catalog K hK huniq hnc hcent s ⟨e⟩, ⟨e⟩⟩)
  obtain ⟨eL⟩ := hE _ hKs hlist hdata
  have hρKr : K.map ρ =
      CFSG.ComponentClassification.OuterAutomorphisms.inner (K ⧸ Subgroup.center K) := by
    ext α
    constructor
    · rintro ⟨k, hk, rfl⟩
      exact ⟨_, (hρK ⟨k, hk⟩).symm⟩
    · rintro ⟨x, rfl⟩
      obtain ⟨k, rfl⟩ := QuotientGroup.mk'_surjective (Subgroup.center K) x
      exact ⟨k, k.2, hρK k⟩
  have hZK : Subgroup.center (K ⧸ Subgroup.center K) = ⊥ :=
    CFSG.ComponentClassification.BMCase.center_eq_bot_of_isSimpleGroup hnab
  have hcardInn :
      Nat.card (CFSG.ComponentClassification.OuterAutomorphisms.inner (K ⧸ Subgroup.center K)) =
        Nat.card (K ⧸ Subgroup.center K) := by
    have hinjc : Function.Injective (MulAut.conj : K ⧸ Subgroup.center K →* MulAut _) := by
      rw [← MonoidHom.ker_eq_bot_iff]
      ext x
      simp only [MonoidHom.mem_ker, Subgroup.mem_bot]
      constructor
      · intro hx
        have : x ∈ Subgroup.center (K ⧸ Subgroup.center K) := by
          rw [Subgroup.mem_center_iff]
          intro y
          have := congrArg (fun f : MulAut _ => f y) hx
          simp only [MulAut.conj_apply, MulAut.one_apply] at this
          calc y * x = x * y * x⁻¹ * x := by rw [this]
            _ = x * y := by group
        rwa [hZK, Subgroup.mem_bot] at this
      · rintro rfl
        exact map_one _
    exact Nat.card_congr (MonoidHom.ofInjective hinjc).symm.toEquiv
  have hOut : Group.IsSolvable (Outer (K ⧸ Subgroup.center K)) :=
    isSolvable_outer_congr eL hT.outer_solvable
  have hJperf : Group.IsPerfect (Jt.map ρ) := by
    rw [Subgroup.isPerfect_iff, ← Subgroup.map_commutator, (h.commutator_eq hT)]
  have : (CFSG.ComponentClassification.OuterAutomorphisms.inner (K ⧸ Subgroup.center K)).Normal :=
    CFSG.ComponentClassification.OuterAutomorphisms.inner_normal _
  have hJinn : Jt.map ρ ≤ K.map ρ := hρKr ▸ le_of_isPerfect_of_isSolvable_quotient hJperf hOut
  have hJKC : ∀ j ∈ Jt, ∃ k ∈ K, k⁻¹ * j ∈ Subgroup.centralizer (K : Set Y) := by
    intro j hj
    obtain ⟨k, hk, hkj⟩ := hJinn ⟨j, hj, rfl⟩
    refine ⟨k, hk, hker ?_⟩
    rw [MonoidHom.mem_ker, map_mul, map_inv, hkj, inv_mul_cancel]
  have hJK : Jt ≤ K := by
    set π := QuotientGroup.mk' K
    have hJC : Jt.map π ≤ (Subgroup.centralizer (K : Set Y)).map π := by
      rintro _ ⟨j, hj, rfl⟩
      obtain ⟨k, hk, hkc⟩ := hJKC j hj
      refine ⟨k⁻¹ * j, hkc, ?_⟩
      have hk1 : π k = 1 := (QuotientGroup.eq_one_iff k).mpr hk
      rw [map_mul, map_inv, hk1, inv_one, one_mul]
    have hJp : IsPGroup p (Jt.map π) := (hCp.map π).to_le hJC
    have hJpp : Group.IsPerfect (Jt.map π) := by
      rw [Subgroup.isPerfect_iff, ← Subgroup.map_commutator, (h.commutator_eq hT)]
    have hbot : Jt.map π = ⊥ := by
      by_contra hne
      have : Nontrivial (Jt.map π) := (Subgroup.nontrivial_iff_ne_bot _).mpr hne
      exact Group.IsPerfect.not_isNilpotent (Jt.map π) hJp.isNilpotent
    intro j hj
    have : π j = 1 := by
      have := Subgroup.mem_map_of_mem π hj
      rwa [hbot, Subgroup.mem_bot] at this
    exact (QuotientGroup.eq_one_iff j).mp this
  have hinj' : Function.Injective (ρ.comp Jt.subtype) := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro x hx
    have hx' : (x : Y) ∈ Jt ⊓ ρ.ker := ⟨x.2, hx⟩
    rw [hinj, Subgroup.mem_bot] at hx'
    exact Subgroup.mem_bot.mpr (Subtype.ext hx')
  have hcardJ : Nat.card (Jt.map ρ) = Nat.card Jt := by
    rw [← Subgroup.range_subtype Jt, ← MonoidHom.range_comp, Subgroup.range_subtype]
    exact Nat.card_congr (MonoidHom.ofInjective hinj').symm.toEquiv
  have hJL : Nat.card L ≤ Nat.card Jt :=
    Nat.le_of_dvd Nat.card_pos (Subgroup.card_dvd_of_surjective (f := φ) h.surj)
  have hLK : Nat.card L = Nat.card (K ⧸ Subgroup.center K) := (Nat.card_congr eL.toEquiv).symm
  have hρJK : Jt.map ρ = K.map ρ := by
    refine Subgroup.eq_of_le_of_card_ge hJinn ?_
    rw [hρKr, hcardInn, hcardJ, ← hLK]
    exact hJL
  have hKJZ : ∀ k ∈ K, ∃ j ∈ Jt, j⁻¹ * k ∈ Subgroup.centralizer (K : Set Y) := by
    intro k hk
    obtain ⟨j, hj, hjk⟩ : ρ k ∈ Jt.map ρ := hρJK ▸ ⟨k, hk, rfl⟩
    refine ⟨j, hj, hker ?_⟩
    rw [MonoidHom.mem_ker, map_mul, map_inv, hjk, inv_mul_cancel]
  have hKJ : K ≤ Jt := by
    have hKK : ⁅K, K⁆ = K := by
      have := hK.2.2.1
      rw [← Subgroup.isPerfect_iff]
      exact ⟨this⟩
    rw [← hKK, Subgroup.commutator_le]
    intro k₁ hk₁ k₂ hk₂
    obtain ⟨j₁, hj₁, hz₁⟩ := hKJZ k₁ hk₁
    obtain ⟨j₂, hj₂, hz₂⟩ := hKJZ k₂ hk₂
    set z₁ := j₁⁻¹ * k₁
    set z₂ := j₂⁻¹ * k₂
    have hk₁' : k₁ = j₁ * z₁ := by simp [z₁]
    have hk₂' : k₂ = j₂ * z₂ := by simp [z₂]
    have hc₁ : ∀ x ∈ K, x * z₁ = z₁ * x := fun x hx => Subgroup.mem_centralizer_iff.mp hz₁ x hx
    have hc₂ : ∀ x ∈ K, x * z₂ = z₂ * x := fun x hx => Subgroup.mem_centralizer_iff.mp hz₂ x hx
    have hz₁K : z₁ ∈ K := K.mul_mem (K.inv_mem (hJK hj₁)) hk₁
    have e1 : ⁅k₁, k₂⁆ = ⁅j₁, j₂⁆ := by
      rw [commutatorElement_def, commutatorElement_def, hk₁', hk₂']
      have h12 := hc₂ z₁ hz₁K
      have hj1 := hc₂ j₁ (hJK hj₁)
      have hj2 := hc₁ j₂ (hJK hj₂)
      calc j₁ * z₁ * (j₂ * z₂) * (j₁ * z₁)⁻¹ * (j₂ * z₂)⁻¹
          = j₁ * (z₁ * j₂) * z₂ * z₁⁻¹ * j₁⁻¹ * z₂⁻¹ * j₂⁻¹ := by group
        _ = j₁ * (j₂ * z₁) * z₂ * z₁⁻¹ * j₁⁻¹ * z₂⁻¹ * j₂⁻¹ := by rw [hj2]
        _ = j₁ * j₂ * (z₁ * z₂) * z₁⁻¹ * j₁⁻¹ * z₂⁻¹ * j₂⁻¹ := by group
        _ = j₁ * j₂ * (z₂ * z₁) * z₁⁻¹ * j₁⁻¹ * z₂⁻¹ * j₂⁻¹ := by rw [h12]
        _ = j₁ * j₂ * z₂ * j₁⁻¹ * z₂⁻¹ * j₂⁻¹ := by group
        _ = j₁ * j₂ * (z₂ * j₁⁻¹) * z₂⁻¹ * j₂⁻¹ := by group
        _ = j₁ * j₂ * (j₁⁻¹ * z₂) * z₂⁻¹ * j₂⁻¹ := by
          rw [show z₂ * j₁⁻¹ = j₁⁻¹ * z₂ from (hc₂ j₁⁻¹ (K.inv_mem (hJK hj₁))).symm]
        _ = j₁ * j₂ * j₁⁻¹ * j₂⁻¹ := by group
    rw [e1, commutatorElement_def]
    exact Jt.mul_mem (Jt.mul_mem (Jt.mul_mem hj₁ hj₂) (Jt.inv_mem hj₁)) (Jt.inv_mem hj₂)
  obtain rfl : Jt = K := le_antisymm hJK hKJ
  have hcardEq : Nat.card Jt = Nat.card L := by
    have h1 : Nat.card (Jt.map ρ) = Nat.card (Jt ⧸ Subgroup.center Jt) := by
      rw [hρKr, hcardInn]
    rw [← hcardJ, h1, hLK]
  have hZ : Subgroup.center Jt = ⊥ := by
    have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup (Subgroup.center Jt)
    rw [hcardEq, hLK] at h1
    have h2 : Nat.card (Subgroup.center Jt) = 1 := by
      have hpos : 0 < Nat.card (Jt ⧸ Subgroup.center Jt) := Nat.card_pos
      nlinarith
    exact Subgroup.eq_bot_of_card_eq _ h2
  refine ⟨hKn, ⟨MulEquiv.ofBijective φ ((Nat.bijective_iff_surjective_and_card φ).mpr
    ⟨h.surj, hcardEq⟩)⟩, ?_⟩
  exact centralizer_eq_bot_of_forall_mem hp h.ne_two h.red.core_eq_bot hKn hmem hZ

end CFSG.AGLEmbedding
