module

public import CFSG.LocalAnalysis.GLTheoremA.S4S.KData
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanThreeCoverSpor
public import CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator.M12CoverRow
public import CFSG.GH74.KGroups.TwoM12Syl3
public import CFSG.RankThree.PartTwo.Toolkit.M12Clause

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4


private theorem nonempty_native_of_catalogIs {S : Type} [Group S] (h : catalogIs S isM12) :
    Nonempty (S ≃* ↥CFSG.Blueprint.NativeSporadic.M12) := by
  obtain ⟨i, hi, ⟨f⟩⟩ := h
  cases i with
  | cyclic p hp => exact (hi : False).elim
  | alternating n hn => exact (hi : False).elim
  | lie j => exact (hi : False).elim
  | sporadic s =>
    have hs : s = TauCeti.SporadicName.M12 := hi
    subst hs
    obtain ⟨b⟩ := CFSG.Sporadic.Bridge.M12.nonempty_mulEquiv
    exact ⟨f.trans b.symm⟩

private theorem card_le_nine_mulAut_native
    (R : Subgroup (MulAut ↥CFSG.Blueprint.NativeSporadic.M12)) (hR : IsElemAbelian 3 R) :
    Nat.card R ≤ 9 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hGcard : Nat.card (MulAut ↥CFSG.Blueprint.NativeSporadic.M12) = 190080 :=
    CFSG.ComponentClassification.M12Cover.card_mulAut
  have : Finite (MulAut ↥CFSG.Blueprint.NativeSporadic.M12) :=
    Nat.finite_of_card_ne_zero (by rw [hGcard]; norm_num)
  have hcomm : ∀ a ∈ R, ∀ b ∈ R, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (hR.1.is_comm.comm (⟨a, ha⟩ : R) ⟨b, hb⟩)
  have hp : IsPGroup 3 R := by
    intro r
    refine ⟨1, ?_⟩
    apply Subtype.ext
    simpa using hR.2 (r : MulAut ↥CFSG.Blueprint.NativeSporadic.M12) r.2
  obtain ⟨k, hk⟩ := hp.exists_card_eq
  have hdvd : Nat.card R ∣ 190080 := hGcard ▸ Subgroup.card_subgroup_dvd_card R
  rw [hk] at hdvd ⊢
  by_contra hlt
  push Not at hlt
  have hk3 : 3 ≤ k := by
    by_contra hk3
    push Not at hk3
    interval_cases k <;> simp at hlt
  have hk3' : k = 3 := by
    by_contra hne
    have h4 : 4 ≤ k := by omega
    have h81 : 3 ^ 4 ∣ 190080 := (pow_dvd_pow 3 h4).trans hdvd
    exact absurd h81 (by norm_num)
  subst hk3'
  exact CFSG.GH74.KGroups.TwoM12.no_abelian_order_27 R hcomm (by rw [hk]; norm_num)

private theorem clause2 {S : Type} [Group S] (h : catalogIs S isM12) :
    ∀ D : Subgroup (MulAut S), IsElemAbelian 3 D → Nat.card D ≤ 9 := by
  obtain ⟨e⟩ := nonempty_native_of_catalogIs h
  intro D hD
  have hcard : Nat.card (D.map (MulAut.congr e).toMonoidHom) = Nat.card D :=
    Subgroup.card_map_of_injective (MulAut.congr e).injective
  rw [← hcard]
  apply card_le_nine_mulAut_native
  refine ⟨?_, ?_⟩
  · haveI := hD.1
    infer_instance
  · intro x hx
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.1 hx
    rw [← map_pow, hD.2 y hy, map_one]

private theorem clause1 {S : Type} [Group S] (h : catalogIs S isM12) :
    ∀ (E : Type) [Group E] [Finite E], CFSG.Open.IsQuasisimple E →
      IsPGroup 3 (Subgroup.center E) → Nonempty ((E ⧸ Subgroup.center E) ≃* S) →
      Subgroup.center E = ⊥ := by
  obtain ⟨b⟩ := nonempty_native_of_catalogIs h
  intro E _ _ hq hZ ⟨e⟩
  by_contra hne
  exact CFSG.AGLEmbedding.KFactProofs.ThreeCover.false_of_not_dvd_multiplier hq hZ hne
    (e.trans b : (E ⧸ Subgroup.center E) ≃* CFSG.Blueprint.NativeSporadic.Carrier .M12)
    (by
      rw [CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator.nativeRow_M12]
      decide)

private theorem clause3 {S : Type} [Group S] [Finite S] (h : catalogIs S isM12) :
    ∃ D U : Subgroup S, IsElemAbelian 3 D ∧ Nat.card D = 9 ∧ U ≠ ⊥ ∧ IsPGroup 2 U ∧
      D ≤ Subgroup.normalizer (U : Set S) := by
  obtain ⟨e⟩ := nonempty_native_of_catalogIs h
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨P⟩ := (Sylow.nonempty : Nonempty (Sylow 3 S))
  obtain ⟨hext, -, -, -, -, -, hnine, E, F, A, A', hset, -, -, -, -, -, -, -, -, -, -, -, hNa, -⟩ :=
    CFSG.RankThree.PartTwo.Toolkit.m12ThreeLocalData S ⟨e⟩ P
  obtain ⟨-, -, -, hcardZ⟩ := hext
  have hZcard : Nat.card ((Subgroup.center (P : Subgroup S)).map (P : Subgroup S).subtype) = 3 := by
    rw [Subgroup.card_map_of_injective (P : Subgroup S).subtype_injective]
    exact hcardZ
  have hAmem : A ≤ (P : Subgroup S) ∧ Nat.card A = 9 := by
    have hmem : A ∈ ({E, F, A, A'} : Set (Subgroup S)) := by simp
    rw [← hset] at hmem
    exact hmem
  obtain ⟨hAle, hA9⟩ := hAmem
  obtain ⟨hAel, hZA⟩ := hnine A hAle hA9
  haveI := hAel
  have hcomm : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val ((inferInstance : IsMulCommutative ↥A).is_comm.comm
      (⟨x, hx⟩ : A) ⟨y, hy⟩)
  have hAZ : ∃ a ∈ A, a ∉ (Subgroup.center (P : Subgroup S)).map (P : Subgroup S).subtype := by
    by_contra hcon
    push Not at hcon
    have hc := Subgroup.card_le_of_le (show A ≤ (Subgroup.center (P : Subgroup S)).map
      (P : Subgroup S).subtype from hcon)
    omega
  obtain ⟨a, haA, haZ⟩ := hAZ
  obtain ⟨ψ⟩ := hNa a haA haZ
  set N : Subgroup S := Subgroup.normalizer ((Subgroup.zpowers a : Subgroup S) : Set S) with hNdef
  haveI hKN : (alternatingGroup.kleinFour (Fin 4)).Normal :=
    alternatingGroup.normal_kleinFour (by simp)
  obtain ⟨W, hW⟩ : ∃ W : Subgroup (Equiv.Perm (Fin 3) × alternatingGroup (Fin 4)),
      W = (⊥ : Subgroup (Equiv.Perm (Fin 3))).prod (alternatingGroup.kleinFour (Fin 4)) :=
    ⟨_, rfl⟩
  have hWN : W.Normal := by
    rw [hW]
    infer_instance
  have hWcard : Nat.card W = 4 := by
    rw [hW, Nat.card_congr (Subgroup.prodEquiv _ _).toEquiv, Nat.card_prod, Subgroup.card_bot,
      alternatingGroup.kleinFour_card_of_card_eq_four (by simp)]
  obtain ⟨U1, hU1⟩ : ∃ U1 : Subgroup N, U1 = W.map ψ.symm.toMonoidHom := ⟨_, rfl⟩
  have hU1N : U1.Normal := by
    rw [hU1]
    exact Subgroup.Normal.map hWN ψ.symm.toMonoidHom ψ.symm.surjective
  have hU1card : Nat.card U1 = 4 := by
    rw [hU1, Subgroup.card_map_of_injective (f := ψ.symm.toMonoidHom) ψ.symm.injective, hWcard]
  have hUcard : Nat.card (U1.map N.subtype) = 4 := by
    rw [Subgroup.card_subtype, hU1card]
  refine ⟨A, U1.map N.subtype, ?_, hA9, ?_, ?_, ?_⟩
  · exact ⟨inferInstance, fun x hx => CFSG.elemPow_eq_one_of_isElementaryAbelian x hx⟩
  · intro hbot
    rw [hbot, Subgroup.card_bot] at hUcard
    norm_num at hUcard
  · exact IsPGroup.of_card (n := 2) (by rw [hUcard]; norm_num)
  · have hUN : U1.map N.subtype ≤ N := Subgroup.map_subtype_le U1
    have hsub : (U1.map N.subtype).subgroupOf N = U1 := by
      ext x
      rw [Subgroup.mem_subgroupOf, Subgroup.mem_map]
      constructor
      · rintro ⟨y, hy, hyx⟩
        have hxy : y = x := Subtype.ext hyx
        exact hxy ▸ hy
      · intro hx
        exact ⟨x, hx, rfl⟩
    have hnorm : ((U1.map N.subtype).subgroupOf N).Normal := by
      rw [hsub]
      exact hU1N
    have hNle : N ≤ Subgroup.normalizer ((U1.map N.subtype : Subgroup S) : Set S) :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer hUN).1 hnorm
    have hzA : Subgroup.zpowers a ≤ A := Subgroup.zpowers_le.2 haA
    have hAN : A ≤ N := fun d hd =>
      Subgroup.centralizer_le_normalizer ((Subgroup.zpowers a : Subgroup S) : Set S)
        (Subgroup.mem_centralizer_iff.2 fun y hy => hcomm y (hzA hy) d hd)
    intro d hd
    exact hNle (hAN hd)

theorem kdM12_holds : KDM12 := by
  intro S _ _ hcat
  exact ⟨clause1 hcat, clause2 hcat, clause3 hcat⟩

end CFSG.LocalAnalysis.GLTheoremA
