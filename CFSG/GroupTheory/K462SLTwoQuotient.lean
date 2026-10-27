module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenDefs
public import CFSG.GH74.Uniqueness.SU.SU5Q8D8
public import CFSG.Quasithin.Vol2.Ch8Sec2L827XSL2Matrix
public import CFSG.Timmesfeld.RankOne.SL2
public import CFSG.GH74.Uniqueness.SU.KI1r4L82
public import CFSG.Adapters.LieModelSimple
public import CFSG.Timmesfeld.Orders.Distinct
public import CFSG.LocalAnalysis.SectionRank.AmbientRank
public import CFSG.CharacterTheory.PSL2Table.Basic
public import CFSG.RankThree.PartTwo.Sec21.Hering233iSL2
public import CFSG.Quasithin.SteinbergBNQTFEPlaneActorsCore
public import CFSG.Adapters.StatedClassicalSmallOrders
public import CFSG.CharacterTheory.Semidihedral.OddFieldSL2

public section

namespace CFSG.GroupTheory

open CFSG.Blueprint (LieModel)
open CFSG.LocalAnalysis.UniquenessCase.PartTwo (IsSLn)
open CFSG.Quasithin (IsAlt IsExt)
open CFSG.GH74.Uniqueness.SU.SU5 (IsQ8D8)

theorem card_of_isSLn_two {S : Type} [Group S] [Finite S] {m : ℕ}
    (h : IsSLn S 2 m) :
    Nat.card S = 2 ^ m * ((2 ^ m) ^ 2 - 1) := by
  obtain ⟨K, hKf, hKfin, hKcard, ⟨e⟩⟩ := h
  letI : Field K := hKf
  letI : Finite K := hKfin
  calc Nat.card S = Nat.card ↥(CFSG.Open.StatedSL 2 K) := Nat.card_congr e.toEquiv
    _ = Nat.card K * (Nat.card K ^ 2 - 1) := CFSG.Open.StatedAPI.card_statedSL_two K
    _ = 2 ^ m * ((2 ^ m) ^ 2 - 1) := by rw [hKcard]

private def upperUnipotentImage {S K : Type} [Group S] [Field K]
    (eSL : S ≃* Matrix.SpecialLinearGroup (Fin 2) K) : Subgroup S :=
  (CFSG.Timmesfeld.upperUnipotent K).map eSL.symm.toMonoidHom

private theorem card_upperUnipotentImage {S K : Type} [Group S] [Field K] [Finite K]
    (eSL : S ≃* Matrix.SpecialLinearGroup (Fin 2) K) :
    Nat.card ↥(upperUnipotentImage eSL) = Nat.card K := by
  rw [upperUnipotentImage, Subgroup.card_map_of_injective eSL.symm.injective,
    CFSG.Timmesfeld.RankOne.card_upperUnipotent]

private theorem upperUnipotent_comm {F : Type} [Field F] :
    ∀ u ∈ CFSG.Timmesfeld.upperUnipotent F,
      ∀ v ∈ CFSG.Timmesfeld.upperUnipotent F, u * v = v * u := by
  intro u hu v hv
  obtain ⟨s, rfl⟩ := (CFSG.Timmesfeld.RankOne.mem_upperUnipotent_iff F).mp hu
  obtain ⟨t, rfl⟩ := (CFSG.Timmesfeld.RankOne.mem_upperUnipotent_iff F).mp hv
  rw [CFSG.Timmesfeld.RankOne.upperElt_mul, CFSG.Timmesfeld.RankOne.upperElt_mul,
    add_comm]

private theorem exists_unique_involution_sl2_odd {H F : Type} [Group H] [Field F] [Finite F]
    (hFodd : Odd (Nat.card F))
    (e : H ≃* Matrix.SpecialLinearGroup (Fin 2) F) :
    ∃ z : H, z * z = 1 ∧ z ≠ 1 ∧ ∀ x : H, x * x = 1 → x = 1 ∨ x = z := by
  have h2 : (2 : F) ≠ 0 :=
    CFSG.Semidihedral.OddFieldSL2.two_ne_zero_of_odd_card F hFodd
  let z : H := e.symm (-1)
  have hz2 : z * z = 1 := by
    apply e.injective
    simp [z]
  have hz1 : z ≠ 1 := by
    intro hz
    have h1 : (-1 : Matrix.SpecialLinearGroup (Fin 2) F) = 1 := by
      calc (-1 : Matrix.SpecialLinearGroup (Fin 2) F) = e z :=
            (e.apply_symm_apply (-1)).symm
        _ = e 1 := by rw [hz]
        _ = 1 := map_one e
    exact CFSG.PSL2Table.neg_one_ne_one_SL h2 h1
  refine ⟨z, hz2, hz1, fun x hx => ?_⟩
  have hx' : e x * e x = 1 := by rw [← map_mul, hx, map_one]
  rcases CFSG.RankThree.PartTwo.Sec21.Hering233i.sl2_eq_one_or_neg_one_of_mul_self
    h2 hx' with h | h
  · exact Or.inl (e.injective (by rw [h, map_one]))
  · exact Or.inr (e.injective (by rw [h, (e.apply_symm_apply (-1)).symm]))

private theorem exists_upperUnipotent_image_isElemAbelian {S : Type} [Group S] [Finite S]
    {m : ℕ} (hm4 : 4 ≤ m) (hS : IsSLn S 2 m) :
    ∃ U : Subgroup S, IsPGroup 2 U ∧ Nat.card U = 2 ^ m ∧
      (∀ x ∈ U, x * x = 1) ∧ IsMulCommutative U := by
  obtain ⟨K, hKfield, hKfinite, hKcard, ⟨eS⟩⟩ := hS
  letI : Field K := hKfield
  letI : Finite K := hKfinite
  letI : Fintype K := Fintype.ofFinite K
  have hKeven : Fintype.card K % 2 = 0 := by
    rw [Fintype.card_eq_nat_card, hKcard]
    exact Nat.dvd_iff_mod_eq_zero.mp (dvd_pow_self 2 (by omega))
  have hKchar : ringChar K = 2 :=
    (FiniteField.even_card_iff_char_two (F := K)).mpr hKeven
  letI : CharP K 2 := hKchar ▸ ringChar.charP K
  let eSL : S ≃* Matrix.SpecialLinearGroup (Fin 2) K :=
    eS.trans (CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL 2 K).symm
  let U : Subgroup S := upperUnipotentImage eSL
  have hUcard : Nat.card ↥U = 2 ^ m := by
    change Nat.card ↥(upperUnipotentImage eSL) = 2 ^ m
    rw [card_upperUnipotentImage, hKcard]
  have hUsq : ∀ x ∈ U, x * x = 1 := by
    intro x hx
    obtain ⟨u, hu, rfl⟩ := Subgroup.mem_map.mp hx
    have hu' : u * u = 1 := by
      obtain ⟨t, rfl⟩ := (CFSG.Timmesfeld.RankOne.mem_upperUnipotent_iff K).mp hu
      rw [CFSG.Timmesfeld.RankOne.upperElt_mul, CharTwo.add_self_eq_zero,
        CFSG.Timmesfeld.RankOne.upperElt_zero]
    rw [← map_mul, hu', map_one]
  have hUcomm : IsMulCommutative ↥U := by
    refine ⟨⟨fun x y => ?_⟩⟩
    obtain ⟨u, hu, hux⟩ := Subgroup.mem_map.mp x.2
    obtain ⟨v, hv, hvy⟩ := Subgroup.mem_map.mp y.2
    apply Subtype.ext
    simp only [Subgroup.coe_mul]
    rw [← hux, ← hvy, ← map_mul, ← map_mul, upperUnipotent_comm u hu v hv]
  exact ⟨U, IsPGroup.of_card (n := m) hUcard, hUcard, hUsq, hUcomm⟩

private theorem not_two_dvd_index_of_isSLn_two {S : Type} [Group S] [Finite S]
    {U : Subgroup S} {m : ℕ} (hm4 : 4 ≤ m)
    (hScard : Nat.card S = 2 ^ m * ((2 ^ m) ^ 2 - 1))
    (hUcard : Nat.card U = 2 ^ m) : ¬ 2 ∣ U.index := by
  intro h2U
  have hmul : Nat.card U * U.index = Nat.card S := Subgroup.card_mul_index U
  rw [hUcard, hScard] at hmul
  have hidx : U.index = (2 ^ m) ^ 2 - 1 :=
    Nat.eq_of_mul_eq_mul_left (by positivity : 0 < 2 ^ m) hmul
  have hodd : Odd ((2 ^ m) ^ 2 - 1) :=
    CFSG.Timmesfeld.Orders.odd_pow_sub_one (f := m) (a := 2) (by omega) (by norm_num)
  exact hodd.not_two_dvd_nat (hidx ▸ h2U)

private theorem exists_sylow_lift {H S : Type} [Group H] [Finite H] [Group S] [Finite S]
    {U : Subgroup S} (hU2 : IsPGroup 2 U) (hUindex : ¬ 2 ∣ U.index)
    (f : H →* S) (hf : Function.Surjective f) :
    ∃ (P : Sylow 2 H) (g : ↥(P : Subgroup H) →* ↥U),
      Function.Surjective g ∧ (P : Subgroup H).map f = U := by
  let Us : Sylow 2 S := hU2.toSylow hUindex
  have hUs : (Us : Subgroup S) = U := IsPGroup.toSylow_coe hU2 hUindex
  obtain ⟨P, hP⟩ := Sylow.mapSurjective_surjective hf 2 Us
  let Psub : Subgroup H := (P : Subgroup H)
  have hPmap : Psub.map f = U := by
    calc Psub.map f = (Sylow.mapSurjective (p := 2) hf P : Subgroup S) :=
          (Sylow.coe_mapSurjective hf (p := 2) P).symm
      _ = Us := by rw [hP]
      _ = U := hUs
  let g : ↥Psub →* ↥U := (f.comp Psub.subtype).codRestrict U (fun p => by
    have hp : f (p : H) ∈ Psub.map f := Subgroup.mem_map_of_mem f p.2
    rwa [hPmap] at hp)
  have hgsurj : Function.Surjective g := by
    intro u
    have hu : (u : S) ∈ Psub.map f := by rw [hPmap]; exact u.2
    obtain ⟨p, hp, hfp⟩ := Subgroup.mem_map.mp hu
    exact ⟨⟨p, hp⟩, Subtype.ext hfp⟩
  exact ⟨P, g, hgsurj, hPmap⟩

private theorem false_of_pRank_le_one_of_abelian_quotient {P U : Type} [Group P] [Finite P]
    [Group U] [Finite U] (hP : IsPGroup 2 P) (hrank : CFSG.pRank 2 P ≤ 1)
    (hUcomm : IsMulCommutative U) (hUsq : ∀ x : U, x * x = 1)
    (f : P →* U) (hf : Function.Surjective f) {m : ℕ}
    (hUcard : Nat.card U = 2 ^ m) (hm4 : 4 ≤ m) : False := by
  haveI : IsMulCommutative U := hUcomm
  have h16 : 16 ≤ 2 ^ m := by
    calc 16 = 2 ^ 4 := by norm_num
      _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm4
  rcases (CFSG.LocalAnalysis.ComponentInitial.pgroup_rank_one_classification
    Nat.prime_two hP).mp hrank with hcyc | ⟨-, n, hn, ⟨eQ⟩⟩
  · haveI : IsCyclic P := hcyc
    haveI : IsCyclic U := isCyclic_of_surjective f hf
    have hle2 := CFSG.GH74.Uniqueness.SU.K.R4.L82.card_le_two_of_cyclic_sq hUsq
    rw [hUcard] at hle2
    omega
  · have h2n : 2 ≤ 2 ^ (n - 2) := by
      calc 2 = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ (n - 2) := Nat.pow_le_pow_right (by norm_num) (by omega)
    haveI : NeZero (2 ^ (n - 2)) := ⟨by positivity⟩
    have hcommidx : (commutator P).index ≤ 4 :=
      CFSG.GH74.Uniqueness.SU.K.R4.L82.index_commutator_le_four
        (n := 2 ^ (n - 2)) h2n eQ
    have hkerle : commutator P ≤ f.ker := Abelianization.commutator_subset_ker f
    have h1 : f.ker.index ≤ (commutator P).index := Subgroup.index_antitone hkerle
    have h2 : f.ker.index = Nat.card U := by
      rw [Subgroup.index_ker]
      rw [MonoidHom.range_eq_top.mpr hf, Subgroup.card_top]
    have hUle : Nat.card U ≤ 4 := by
      calc Nat.card U = f.ker.index := h2.symm
        _ ≤ (commutator P).index := h1
        _ ≤ 4 := hcommidx
    rw [hUcard] at hUle
    omega

theorem false_of_sl2_odd_surjective {H S : Type} [Group H] [Finite H] [Group S] [Finite S]
    {m : ℕ} (hm4 : 4 ≤ m) (hS : IsSLn S 2 m)
    (hH : ∃ (F : Type) (_ : Field F) (_ : Finite F), Odd (Nat.card F) ∧
      Nonempty (H ≃* Matrix.SpecialLinearGroup (Fin 2) F))
    (f : H →* S) (hf : Function.Surjective f) : False := by
  obtain ⟨F, hFfield, hFfinite, hFodd, ⟨e⟩⟩ := hH
  letI : Field F := hFfield
  letI : Finite F := hFfinite
  obtain ⟨z, hz2, hz1, hinv⟩ := exists_unique_involution_sl2_odd hFodd e
  obtain ⟨U, hU2, hUcard, hUsq, hUcomm⟩ :=
    exists_upperUnipotent_image_isElemAbelian hm4 hS
  have hScard : Nat.card S = 2 ^ m * ((2 ^ m) ^ 2 - 1) := card_of_isSLn_two hS
  have hUindex : ¬ 2 ∣ U.index :=
    not_two_dvd_index_of_isSLn_two hm4 hScard hUcard
  obtain ⟨P, g, hgsurj, hPmap⟩ := exists_sylow_lift hU2 hUindex f hf
  have hzorder : ∀ x : H, orderOf x = 2 → x = z := by
    intro x hx
    have hx2 : x * x = 1 := by
      rw [← pow_two, ← hx]
      exact pow_orderOf_eq_one x
    rcases hinv x hx2 with h | h
    · rw [h] at hx
      norm_num at hx
    · exact h
  have hrankTop : CFSG.Open.pRank 2 (⊤ : Subgroup H) ≤ 1 := by
    rw [← CFSG.SectionRank.pRank_eq_open_pRank_top 2 H]
    exact CFSG.Quasithin.SteinbergBN.PlaneActors.pRank_two_le_one z hzorder
  have hrank : CFSG.pRank 2 ↥(P : Subgroup H) ≤ 1 := by
    rw [CFSG.SectionRank.pRank_coe_eq_openPRank]
    exact (CFSG.SectionRank.pRank_mono (by norm_num) (le_top)).trans hrankTop
  exact false_of_pRank_le_one_of_abelian_quotient P.isPGroup' hrank hUcomm
    (fun x => Subtype.ext (hUsq x x.2)) g hgsurj hUcard hm4

private theorem false_of_card_eq_of_lieModel_psl_two {H S : Type} [Group H] [Finite H]
    [Group S] [Finite S] {m n : ℕ} (hm4 : 4 ≤ m) (hme : Even m) (hS : IsSLn S 2 m)
    (hn : Odd n) (hH : LieModel H .PSL 2 2 n) (hcard : Nat.card H = Nat.card S) : False := by
  rw [CFSG.Open.StatedAPI.card_of_statedClassicalModel_psl_two_two
        (hH.statedClassicalModel (t := .PSL) (n := 2) (p := 2) (f := n) (by decide)),
      card_of_isSLn_two hS] at hcard
  have hn0 : 0 < n := by
    obtain ⟨k, hk⟩ := hn
    omega
  have hoddn : Odd ((2 ^ n) ^ 2 - 1) :=
    CFSG.Timmesfeld.Orders.odd_pow_sub_one (f := n) (a := 2) hn0 (by norm_num)
  have hoddm : Odd ((2 ^ m) ^ 2 - 1) :=
    CFSG.Timmesfeld.Orders.odd_pow_sub_one (f := m) (a := 2) (by omega) (by norm_num)
  have hne_n : (2 ^ n) ^ 2 - 1 ≠ 0 := by
    have h2 : 1 < 2 ^ n :=
      Nat.one_lt_pow (n := n) (a := 2) (Nat.pos_iff_ne_zero.mp hn0) (by norm_num)
    have h4 : 1 < (2 ^ n) ^ 2 := by
      calc 1 < 2 ^ n := h2
        _ ≤ (2 ^ n) ^ 2 := Nat.le_self_pow (by norm_num) _
    exact Nat.sub_ne_zero_of_lt h4
  have hne_m : (2 ^ m) ^ 2 - 1 ≠ 0 := by
    have h2 : 1 < 2 ^ m :=
      Nat.one_lt_pow (n := m) (a := 2) (Nat.pos_iff_ne_zero.mp (by omega : 0 < m))
        (by norm_num)
    have h4 : 1 < (2 ^ m) ^ 2 := by
      calc 1 < 2 ^ m := h2
        _ ≤ (2 ^ m) ^ 2 := Nat.le_self_pow (by norm_num) _
    exact Nat.sub_ne_zero_of_lt h4
  have hval := congrArg (padicValNat 2) hcard
  rw [Nat.maxPowDiv.base_pow_mul (p := 2) (n := (2 ^ n) ^ 2 - 1) (by norm_num) hne_n n,
      Nat.maxPowDiv.base_pow_mul (p := 2) (n := (2 ^ m) ^ 2 - 1) (by norm_num) hne_m m,
      padicValNat.eq_zero_of_not_dvd hoddn.not_two_dvd_nat,
      padicValNat.eq_zero_of_not_dvd hoddm.not_two_dvd_nat] at hval
  have hnm : n = m := by omega
  subst hnm
  exact (Nat.not_odd_iff_even.mpr hme) hn

private theorem sixteen_le_card_of_isSLn_two {S : Type} [Group S] [Finite S] {m : ℕ}
    (hm4 : 4 ≤ m) (hS : IsSLn S 2 m) : 16 ≤ Nat.card S := by
  rw [card_of_isSLn_two hS]
  have h16 : 16 ≤ 2 ^ m := by
    calc 16 = 2 ^ 4 := by norm_num
      _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm4
  have h255 : 255 ≤ (2 ^ m) ^ 2 - 1 := by
    have h256 : 256 ≤ (2 ^ m) ^ 2 := by
      calc 256 = 16 ^ 2 := by norm_num
        _ ≤ (2 ^ m) ^ 2 := Nat.pow_le_pow_left h16 2
    omega
  calc 16 = 16 * 1 := by norm_num
    _ ≤ 2 ^ m * ((2 ^ m) ^ 2 - 1) := Nat.mul_le_mul h16 (by omega)

theorem false_of_lieModel_psl_odd_surjective {H S : Type} [Group H] [Finite H]
    [Group S] [Finite S] {m n : ℕ} (hm4 : 4 ≤ m) (hme : Even m) (hS : IsSLn S 2 m)
    (hn : Odd n) (hH : LieModel H .PSL 2 2 n)
    (f : H →* S) (hf : Function.Surjective f) : False := by
  haveI : IsSimpleGroup H :=
    CFSG.Blueprint.LieModel.isSimpleGroup_of_mem_classicalTags (t := .PSL) (n := 2) (p := 2)
      (f := n) (by decide) hH
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal f.ker with hbot | htop
  · have hinj : Function.Injective f := (MonoidHom.ker_eq_bot_iff f).mp hbot
    have hbij : Function.Bijective f := ⟨hinj, hf⟩
    exact false_of_card_eq_of_lieModel_psl_two hm4 hme hS hn hH
      (Nat.card_congr (Equiv.ofBijective f hbij))
  · have hsub : Subsingleton S := by
      refine ⟨fun x y => ?_⟩
      obtain ⟨a, rfl⟩ := hf x
      obtain ⟨b, rfl⟩ := hf y
      have ha : f a = 1 :=
        MonoidHom.mem_ker.mp (by rw [htop]; exact Subgroup.mem_top a)
      have hb : f b = 1 :=
        MonoidHom.mem_ker.mp (by rw [htop]; exact Subgroup.mem_top b)
      rw [ha, hb]
    have hle1 : Nat.card S ≤ 1 := Finite.card_le_one_iff_subsingleton.mpr hsub
    have hge : 16 ≤ Nat.card S := sixteen_le_card_of_isSLn_two hm4 hS
    omega

theorem false_of_isExt_q8d8_alt_five_surjective {H S : Type} [Group H] [Finite H]
    [Group S] [Finite S] {m : ℕ} (hm4 : 4 ≤ m) (hS : IsSLn S 2 m)
    (hH : IsExt H (fun V _ => IsQ8D8 (⊤ : Subgroup V)) (fun Y _ => IsAlt 5 Y))
    (f : H →* S) (hf : Function.Surjective f) : False := by
  obtain ⟨V, hVn, hVq8, hValt⟩ := hH
  letI : V.Normal := hVn
  have hVcard : Nat.card ↥V = 32 := by
    simpa [Subgroup.card_top] using (hVq8.facts).1
  have hValt' : Nonempty (H ⧸ V ≃* alternatingGroup (Fin 5)) := hValt
  obtain ⟨eA⟩ := hValt'
  have hQcard : Nat.card (H ⧸ V) = 60 := by
    rw [Nat.card_congr eA.toEquiv,
      CFSG.Quasithin.H13.L827X.SL2Orb.card_alternatingGroup_fin_five]
  have hHcard : Nat.card H = 1920 := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup V, hQcard, hVcard]
  have h16 : 16 ≤ 2 ^ m := by
    calc 16 = 2 ^ 4 := by norm_num
      _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm4
  have h255 : 255 ≤ (2 ^ m) ^ 2 - 1 := by
    have h256 : 256 ≤ (2 ^ m) ^ 2 := by
      calc 256 = 16 ^ 2 := by norm_num
        _ ≤ (2 ^ m) ^ 2 := Nat.pow_le_pow_left h16 2
    omega
  have hge : 4080 ≤ Nat.card S := by
    rw [card_of_isSLn_two hS]
    calc 4080 = 16 * 255 := by norm_num
      _ ≤ 2 ^ m * ((2 ^ m) ^ 2 - 1) := Nat.mul_le_mul h16 h255
  have hle := Nat.card_le_card_of_surjective f hf
  omega

theorem not_surjective_of_k462_alternative {H S : Type} [Group H] [Finite H]
    [Group S] [Finite S] {m : ℕ} (hm4 : 4 ≤ m) (hme : Even m) (hS : IsSLn S 2 m)
    (hH : (∃ (F : Type) (_ : Field F) (_ : Finite F), Odd (Nat.card F) ∧
        Nonempty (H ≃* Matrix.SpecialLinearGroup (Fin 2) F)) ∨
      (∃ n : ℕ, Odd n ∧ LieModel H .PSL 2 2 n) ∨
      IsExt H (fun V _ => IsQ8D8 (⊤ : Subgroup V)) (fun Y _ => IsAlt 5 Y))
    (f : H →* S) (hf : Function.Surjective f) : False := by
  rcases hH with h1 | h2 | h3
  · exact false_of_sl2_odd_surjective hm4 hS h1 f hf
  · obtain ⟨n, hn, hL⟩ := h2
    exact false_of_lieModel_psl_odd_surjective hm4 hme hS hn hL f hf
  · exact false_of_isExt_q8d8_alt_five_surjective hm4 hS h3 f hf

end CFSG.GroupTheory
