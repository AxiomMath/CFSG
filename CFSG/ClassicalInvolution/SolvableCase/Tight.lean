module

public import CFSG.ClassicalInvolution.Reduction
public import CFSG.ClassicalInvolution.SolvableCase.SL2Three
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.Fitting.Centralizer

public section

namespace CFSG.ClassicalInvolution

open CFSG CFSG.Open
open CFSG.ClassicalInvolution.QuaternionStructure
open scoped MatrixGroups

@[expose] def oddTwoCore (J : Type*) [Group J] : Subgroup J :=
  (pCore 2 (J ⧸ oddCore J)).comap (QuotientGroup.mk' (oddCore J))

variable {J : Type*} [Group J]

theorem mem_oddTwoCore_iff {x : J} :
    x ∈ oddTwoCore J ↔ (x : J ⧸ oddCore J) ∈ pCore 2 (J ⧸ oddCore J) := Iff.rfl

instance oddTwoCore_normal : (oddTwoCore J).Normal := Subgroup.Normal.comap inferInstance _

theorem oddCore_le_oddTwoCore : oddCore J ≤ oddTwoCore J := fun x hx => by
  rw [mem_oddTwoCore_iff, (QuotientGroup.eq_one_iff x).mpr hx]
  exact one_mem _

instance oddTwoCore_characteristic : (oddTwoCore J).Characteristic := by
  rw [Subgroup.characteristic_iff_comap_eq]
  intro φ
  have hO : (oddCore J).map φ.toMonoidHom = oddCore J := by
    have : (oddCore J).Characteristic := by
      rw [oddCore_eq_pPrimeCore_two]; infer_instance
    exact (Subgroup.characteristic_iff_map_eq.mp this) φ
  let φ' : J ⧸ oddCore J ≃* J ⧸ oddCore J := QuotientGroup.congr _ _ φ hO
  ext x
  have hx : ((φ.toMonoidHom x : J) : J ⧸ oddCore J) = φ' x := rfl
  have hc : (pCore 2 (J ⧸ oddCore J)).comap φ'.toMonoidHom = pCore 2 (J ⧸ oddCore J) :=
    Subgroup.characteristic_iff_comap_eq.mp inferInstance φ'
  rw [Subgroup.mem_comap, mem_oddTwoCore_iff, mem_oddTwoCore_iff, hx]
  exact (Set.ext_iff.mp (congrArg SetLike.coe hc) (x : J ⧸ oddCore J))

theorem oddTwoCore_quotient_isPGroup [Finite J] :
    IsPGroup 2 (oddTwoCore J ⧸ oddCore (oddTwoCore J)) := by
  let K : Subgroup J := oddTwoCore J
  let π : J →* J ⧸ oddCore J := QuotientGroup.mk' (oddCore J)
  have hπ : Function.Surjective π := QuotientGroup.mk'_surjective _
  let θ : K →* pCore 2 (J ⧸ oddCore J) := (π.comp K.subtype).codRestrict _ (fun x => x.2)
  have hθ : Function.Surjective θ := by
    intro y
    obtain ⟨x, hx⟩ := hπ (y : J ⧸ oddCore J)
    refine ⟨⟨x, ?_⟩, Subtype.ext hx⟩
    change π x ∈ pCore 2 (J ⧸ oddCore J)
    rw [hx]
    exact y.2
  have hker : θ.ker = (oddCore J).subgroupOf K := by
    ext x
    change (θ x = 1) ↔ _
    rw [Subgroup.mem_subgroupOf, ← QuotientGroup.eq_one_iff (x : J)]
    exact Subtype.ext_iff
  have hO : oddCore K = θ.ker := (oddCore_eq_subgroupOf K oddCore_le_oddTwoCore).trans hker.symm
  exact (pCore_isPGroup (p := 2) (G := J ⧸ oddCore J)).of_equiv
    ((QuotientGroup.quotientMulEquivOfEq hO).trans (QuotientGroup.quotientKerEquivOfSurjective θ hθ)).symm

theorem nonempty_mulEquiv_sylow_of_normal_odd_index {G : Type*} [Group G] [Finite G]
    (L : Subgroup G) [L.Normal] (hL : Odd L.index) (T : Sylow 2 L) (P : Sylow 2 G) :
    Nonempty ((T : Subgroup L) ≃* (P : Subgroup G)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hPL := sylow_le_of_normal_of_odd_index L hL P
  exact ⟨(Sylow.equiv T (P.subtype hPL)).trans (Subgroup.subgroupOfEquivOfLe hPL)⟩

private theorem natCard_sylow_of_natCard_eq_24 {Y : Type*} [Group Y] [Finite Y]
    (h : Nat.card Y = 24) (P : Sylow 2 Y) : Nat.card (P : Subgroup Y) = 8 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨a, ha⟩ := P.isPGroup'.exists_card_eq
  have hidx := Subgroup.card_mul_index (P : Subgroup Y)
  have hodd : ¬ 2 ∣ (P : Subgroup Y).index := P.not_dvd_index
  rw [ha, h] at hidx
  have ha4 : a < 5 := by
    by_contra hcon
    push Not at hcon
    have : 2 ^ 5 ≤ 2 ^ a := Nat.pow_le_pow_right (by norm_num) hcon
    have : 0 < (P : Subgroup Y).index := Nat.pos_of_ne_zero (fun h0 => by simp [h0] at hidx)
    nlinarith
  rw [ha]
  interval_cases a <;> simp at hidx ⊢ <;> omega

theorem sylow_eq_pCore_of_mulEquiv_sl2Three {Y : Type*} [Group Y] (eY : Y ≃* SL(2, ZMod 3))
    (P : Sylow 2 Y) : (P : Subgroup Y) = pCore 2 Y := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Finite Y := Finite.of_equiv _ eY.symm.toEquiv
  have hY : Nat.card Y = 24 := by rw [Nat.card_congr eY.toEquiv, natCard_sl2Three]
  let N : Subgroup Y := sl2ThreeQ.map eY.symm.toMonoidHom
  have hNn : N.Normal := Subgroup.Normal.map sl2ThreeQ_normal eY.symm.toMonoidHom eY.symm.surjective
  have hNcard : Nat.card N = 8 := by
    have h : Nat.card N = Nat.card sl2ThreeQ :=
      (Nat.card_congr (MulEquiv.subgroupMap eY.symm sl2ThreeQ).toEquiv).symm
    rw [h, natCard_sl2ThreeQ]
  have hN2 : IsPGroup 2 N := IsPGroup.of_card (n := 3) (by rw [hNcard]; norm_num)
  have hNle : N ≤ pCore 2 Y := le_sSup ⟨hNn, hN2⟩
  have hle : pCore 2 Y ≤ P := fitting_pCore_le_sylow P
  have hPcard := natCard_sylow_of_natCard_eq_24 hY P
  have hNP : N = P := Subgroup.eq_of_le_of_card_ge (hNle.trans hle) (by rw [hPcard, hNcard])
  exact le_antisymm (hNP ▸ hNle) hle

theorem nonempty_mulEquiv_sl2Three_of_witness {G : Type*} [Group G] [Finite G] {J : Subgroup G}
    (hw : classicalInvolutionWitness J) (hs : Group.IsSolvable J) :
    Nonempty (J ⧸ classicalInvolutionOddCore J ≃* SL(2, ZMod 3)) := by
  have hq : Group.IsSolvable (J ⧸ classicalInvolutionOddCore J) :=
    Group.isSolvable_of_surjective (QuotientGroup.mk'_surjective _)
  rcases hw with ⟨p, n, hp, hp2, hn, ⟨e⟩⟩ | ⟨hqs, -, -⟩
  · have hodd : Odd (Nat.card (GaloisField p n)) := by
      rw [GaloisField.card p n hn.ne']
      exact (hp.out.odd_of_ne_two hp2).pow
    have hsl : Group.IsSolvable SL(2, GaloisField p n) :=
      Group.isSolvable_of_isSolvable_injective (f := e.symm.toMonoidHom) e.symm.injective
    obtain ⟨f⟩ := nonempty_mulEquiv_sl2Three_of_isSolvable hodd hsl
    exact ⟨e.trans f⟩
  · exfalso
    obtain ⟨hperf, hsimple⟩ := hqs
    have hnt : Nontrivial (J ⧸ classicalInvolutionOddCore J) :=
      (QuotientGroup.mk'_surjective (Subgroup.center (J ⧸ classicalInvolutionOddCore J))).nontrivial
    exact (Group.IsSolvable.commutator_lt_top_of_nontrivial _).ne hperf

theorem tight_solvable_data {G : Type} [Group G] [Finite G] {z : G} (hz : orderOf z = 2)
    {J : Subgroup G} (hzJ : z ∈ J) (hJ : IsSubnormal J (Subgroup.centralizer ({z} : Set G)))
    (S : Sylow 2 J)
    (hS : ∃ r : ℕ, 3 ≤ r ∧ Nonempty ((S : Subgroup J) ≃* QuaternionGroup (2 ^ (r - 2))))
    (hw : classicalInvolutionWitness J) (hs : Group.IsSolvable J)
    (hTE : classicalInvolutionTightlyEmbedded J) :
    ∃ (R : Subgroup G) (S' : Sylow 2 R),
      (∃ r : ℕ, 3 ≤ r ∧ Nonempty ((S' : Subgroup R) ≃* QuaternionGroup (2 ^ (r - 2)))) ∧
      z ∈ (S' : Subgroup R).map R.subtype ∧
      R ≤ Subgroup.centralizer ({z} : Set G) ∧
      (R.subgroupOf (Subgroup.centralizer ({z} : Set G))).Normal ∧
      IsPGroup 2 (R ⧸ classicalInvolutionOddCore R) ∧
      Nonempty ((R ⧸ classicalInvolutionOddCore R) ≃* QuaternionGroup 2) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hcent : J ≤ Subgroup.centralizer ({z} : Set G) := isSubnormal_le hJ
  have hCN : Subgroup.centralizer ({z} : Set G) ≤ Subgroup.normalizer (J : Set G) :=
    (tightlyEmbedded_iff_centralizer_le_normalizer hzJ hz hcent S hS).mp hTE
  obtain ⟨eJ⟩ := nonempty_mulEquiv_sl2Three_of_witness hw hs
  have hRJodd : Odd (oddTwoCore J).index := by
    obtain ⟨P0⟩ : Nonempty (Sylow 2 (J ⧸ oddCore J)) := inferInstance
    have h1 : (oddTwoCore J).index = (pCore 2 (J ⧸ oddCore J)).index :=
      Subgroup.index_comap_of_surjective _ (QuotientGroup.mk'_surjective _)
    have hP0 : (P0 : Subgroup (J ⧸ oddCore J)) = pCore 2 (J ⧸ oddCore J) :=
      sylow_eq_pCore_of_mulEquiv_sl2Three eJ P0
    have h2 : ¬ 2 ∣ (oddTwoCore J).index := by
      rw [h1, ← hP0]
      exact P0.not_dvd_index
    exact Nat.odd_iff.mpr (by omega)
  let φ : oddTwoCore J ≃* (oddTwoCore J).map J.subtype :=
    Subgroup.equivMapOfInjective (oddTwoCore J) J.subtype J.subtype_injective
  obtain ⟨S'⟩ : Nonempty (Sylow 2 ((oddTwoCore J).map J.subtype)) := inferInstance
  let S'' : Sylow 2 (oddTwoCore J) := S'.mapSurjective (f := φ.symm.toMonoidHom) φ.symm.surjective
  obtain ⟨r, hr3, ⟨eS⟩⟩ := hS
  obtain ⟨e2⟩ := nonempty_mulEquiv_sylow_of_normal_odd_index (oddTwoCore J) hRJodd S'' S
  have e1 : (S' : Subgroup ((oddTwoCore J).map J.subtype)) ≃* (S'' : Subgroup (oddTwoCore J)) :=
    MulEquiv.subgroupMap φ.symm (S' : Subgroup ((oddTwoCore J).map J.subtype))
  have hS' : ∃ r : ℕ, 3 ≤ r ∧ Nonempty ((S' : Subgroup ((oddTwoCore J).map J.subtype)) ≃*
      QuaternionGroup (2 ^ (r - 2))) := ⟨r, hr3, ⟨(e1.trans e2).trans eS⟩⟩
  have hRC : (oddTwoCore J).map J.subtype ≤ Subgroup.centralizer ({z} : Set G) :=
    (Subgroup.map_subtype_le _).trans hcent
  have h2grp : IsPGroup 2 (((oddTwoCore J).map J.subtype) ⧸
      classicalInvolutionOddCore ((oddTwoCore J).map J.subtype)) := by
    have hO : (oddCore (oddTwoCore J)).map φ.toMonoidHom = oddCore ((oddTwoCore J).map J.subtype) :=
      oddCore_map_mulEquiv φ
    exact (oddTwoCore_quotient_isPGroup (J := J)).of_equiv (QuotientGroup.congr _ _ φ hO)
  have hr : r = 3 := by
    have hY : Nat.card (J ⧸ classicalInvolutionOddCore J) = 24 := by
      rw [Nat.card_congr eJ.toEquiv, natCard_sl2Three]
    obtain ⟨P⟩ : Nonempty (Sylow 2 (J ⧸ oddCore J)) := inferInstance
    obtain ⟨f⟩ := sylow_oddCore_quotient_equiv S P
    have hS8 : Nat.card (S : Subgroup J) = 8 := by
      rw [← Nat.card_congr f.toEquiv]
      exact natCard_sylow_of_natCard_eq_24 hY P
    have : NeZero (2 ^ (r - 2)) := ⟨pow_ne_zero _ two_ne_zero⟩
    have h4 : 4 * 2 ^ (r - 2) = 4 * 2 := by
      rw [← QuaternionGroup.card, ← Nat.card_eq_fintype_card, ← Nat.card_congr eS.toEquiv, hS8]
    have h5 : 2 ^ (r - 2) = 2 ^ 1 := by
      have := Nat.eq_of_mul_eq_mul_left (by norm_num : 0 < 4) h4
      simpa using this
    have := Nat.pow_right_injective (le_refl 2) h5
    omega
  obtain ⟨eQ⟩ := nonempty_mulEquiv_sylow_of_isPGroup_oddCore_quotient h2grp S'
  subst hr
  refine ⟨(oddTwoCore J).map J.subtype, S', hS', ?_, hRC, ?_, h2grp, ?_⟩
  · obtain ⟨hP2, hP1⟩ := sylow_map_isPGroup_ne_bot S' hS'
    exact (unique_involution_of_quaternion_sylow hzJ hz hcent S ⟨3, hr3, ⟨eS⟩⟩).2 _
      ((Subgroup.map_subtype_le _).trans (Subgroup.map_subtype_le _)) hP2 hP1
  · rw [Subgroup.normal_subgroupOf_iff hRC]
    rintro _ c ⟨rJ, hrJ, rfl⟩ hc
    let α : MulAut J := Subgroup.normalizerMonoidHom J ⟨c, hCN hc⟩
    have hα : α rJ ∈ oddTwoCore J := by
      have := Subgroup.characteristic_iff_map_eq.mp (oddTwoCore_characteristic (J := J)) α
      rw [← this]
      exact ⟨rJ, hrJ, rfl⟩
    exact ⟨α rJ, hα, rfl⟩
  · exact ⟨eQ.trans ((e1.trans e2).trans eS)⟩

abbrev PartOneSolvableTight : Prop :=
  PartOneUnder fun _ J => Group.IsSolvable J ∧ classicalInvolutionTightlyEmbedded J

abbrev PartOneSolvableNonTight : Prop :=
  PartOneUnder fun _ J => Group.IsSolvable J ∧ ¬ classicalInvolutionTightlyEmbedded J

theorem partOneSolvable_of_tight_of_nonTight (ht : PartOneSolvableTight)
    (hn : PartOneSolvableNonTight) : PartOneSolvable := by
  intro G _ _ _ hnab z hz J hzJ hJ S hS hw hsolv
  by_cases hTE : classicalInvolutionTightlyEmbedded J
  · exact ht G hnab z hz J hzJ hJ S hS hw ⟨hsolv, hTE⟩
  · exact hn G hnab z hz J hzJ hJ S hS hw ⟨hsolv, hTE⟩

@[expose] def M12NoSolvableTightClassical : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup (genFittingFStar G)],
    Blueprint.NativeSporadic.IsSporadic (genFittingFStar G) .M12 →
    ∀ (z : G), orderOf z = 2 → ∀ (J : Subgroup G), z ∈ J →
    IsSubnormal J (Subgroup.centralizer ({z} : Set G)) → ∀ (S : Sylow 2 J),
    (∃ r : ℕ, 3 ≤ r ∧ Nonempty ((S : Subgroup J) ≃* QuaternionGroup (2 ^ (r - 2)))) →
    classicalInvolutionWitness J → Group.IsSolvable J →
    classicalInvolutionTightlyEmbedded J → False

theorem partOneSolvableTight_of_normalOddByQuaternion (hB : NormalOddByQuaternion)
    (hM : M12NoSolvableTightClassical) : PartOneSolvableTight := by
  intro G _ _ _ hnab z hz J hzJ hJ S hS hw hsolvTE
  obtain ⟨hsolv, hTE⟩ := hsolvTE
  obtain ⟨R, S', hS', hzS', hRC, hRn, h2grp, -⟩ := tight_solvable_data hz hzJ hJ S hS hw hsolv hTE
  rcases hB G hnab R S' hS' z hzS' hz hRC hRn h2grp trivial with h | h | h
  · exact Or.inl h
  · exact Or.inr h
  · exact (hM G h z hz J hzJ hJ S hS hw hsolv hTE).elim

end CFSG.ClassicalInvolution
