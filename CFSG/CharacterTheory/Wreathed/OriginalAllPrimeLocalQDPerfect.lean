module

public import CFSG.CharacterTheory.Wreathed.OriginalAllPrimeLocalQDBasic
public import CFSG.ThirdParty.QiuzhenCFSG.Glauberman.DicksonClassification
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PGL2DerivedSubgroup

public section

namespace CFSG.Wreathed.OriginalAllPrime.LocalQD

open CFSG.Semidihedral.ProjectiveSL2Cover

theorem perfect_even_mul_sq_sub_one (t : ℕ) : Even (t * (t ^ 2 - 1)) := by
  rcases Nat.even_or_odd t with h | h
  · exact h.mul_right _
  · exact (Nat.Odd.sub_odd h.pow odd_one).mul_left _

theorem perfect_mul_sq_sub_one_lt {a b : ℕ} (ha : 1 ≤ a) (hab : a < b) :
    a * (a ^ 2 - 1) < b * (b ^ 2 - 1) := by
  have h1 : a ^ 2 - 1 < b ^ 2 - 1 :=
    Nat.sub_lt_sub_right (Nat.one_le_pow _ _ ha) (Nat.pow_lt_pow_left hab two_ne_zero)
  exact Nat.mul_lt_mul_of_le_of_lt hab.le h1 (by omega)

theorem perfect_eq_of_mul_sq_sub_one_eq {a b : ℕ} (ha : 1 ≤ a) (hb : 1 ≤ b)
    (h : a * (a ^ 2 - 1) = b * (b ^ 2 - 1)) : a = b := by
  rcases lt_trichotomy a b with hab | hab | hab
  · exact absurd h (perfect_mul_sq_sub_one_lt ha hab).ne
  · exact hab
  · exact absurd h (perfect_mul_sq_sub_one_lt hb hab).ne'

theorem perfect_card_le_one {G : Type*} [Group G] [Finite G] [Group.IsPerfect G]
    [IsMulCommutative G] : Nat.card G ≤ 1 :=
  Finite.card_le_one_iff_subsingleton.mpr inferInstance

theorem perfect_isMulCommutative_of_sup_eq_top {G : Type*} [Group G] [Group.IsPerfect G]
    {N C : Subgroup G} [N.Normal] [IsMulCommutative N] [IsMulCommutative C]
    (h : N ⊔ C = ⊤) : IsMulCommutative G := by
  have hle : commutator G ≤ N :=
    Subgroup.Normal.commutator_le_of_self_sup_commutative_eq_top h inferInstance
  rw [Group.IsPerfect.commutator_eq_top, top_le_iff] at hle
  refine isMulCommutative_iff.mpr fun a b => ?_
  have ha : a ∈ N := by rw [hle]; exact Subgroup.mem_top a
  have hb : b ∈ N := by rw [hle]; exact Subgroup.mem_top b
  exact congrArg Subtype.val (mul_comm' (⟨a, ha⟩ : N) ⟨b, hb⟩)

theorem perfect_pgl2_not_isPerfect {K : Type*} [Field K] [Finite K]
    (hK : CFSG.GorensteinWalter.IsOddPrimePower (Nat.card K)) :
    ¬ Group.IsPerfect (Matrix.ProjGenLinGroup (Fin 2) K) := by
  intro hperf
  have hle := CFSG.GorensteinWalter.pgl2_commutator_le_psl2_range K
  rw [hperf.commutator_eq_top, top_le_iff] at hle
  have h1 : Nat.card (Matrix.ProjGenLinGroup (Fin 2) K) ≤
      Nat.card (Matrix.ProjectiveSpecialLinearGroup (Fin 2) K) := by
    rw [← Subgroup.card_top (G := Matrix.ProjGenLinGroup (Fin 2) K), ← hle]
    exact Nat.card_le_card_of_surjective _ (MonoidHom.rangeRestrict_surjective _)
  rw [CFSG.GorensteinWalter.pgl2_card_formula, CFSG.GorensteinWalter.psl2_card_formula K hK]
    at h1
  have hq : 1 < Nat.card K := Finite.one_lt_card
  have hpos : 0 < Nat.card K * (Nat.card K ^ 2 - 1) := by
    apply Nat.mul_pos (by omega)
    have : 4 ≤ Nat.card K ^ 2 := by nlinarith
    omega
  have := Nat.div_lt_self hpos (by norm_num : 1 < 2)
  omega

theorem perfect_eq_bot_of_map_eq_bot {F : Type} [Field F] (hF2 : ringChar F ≠ 2)
    {B : Subgroup (Matrix.SpecialLinearGroup (Fin 2) F)} {L : Subgroup B}
    (hL : Odd (Nat.card L)) (hmap : L.map ((nativeQuotient F).subgroupMap B) = ⊥) : L = ⊥ := by
  rw [Subgroup.map_eq_bot_iff] at hmap
  rw [eq_bot_iff]
  intro x hx
  have hx1 : (nativeQuotient F).subgroupMap B x = 1 := MonoidHom.mem_ker.mp (hmap hx)
  have hxk : (x : Matrix.SpecialLinearGroup (Fin 2) F) ∈ (nativeQuotient F).ker :=
    MonoidHom.mem_ker.mpr (congrArg Subtype.val hx1)
  rw [nativeQuotient_ker, ← center_eq_zpowers_minusIdentity] at hxk
  have hsq : (⟨x, hx⟩ : L) ^ 2 = 1 := by
    apply Subtype.ext
    apply Subtype.ext
    exact (sq_eq_one_iff_mem_center hF2 _).mpr hxk
  have hord : orderOf (⟨x, hx⟩ : L) = 1 :=
    Nat.eq_one_of_dvd_coprimes (Nat.coprime_two_left.mpr hL) (orderOf_dvd_of_pow_eq_one hsq)
      (orderOf_dvd_natCard _)
  exact Subgroup.mem_bot.mpr (congrArg Subtype.val (orderOf_eq_one_iff.mp hord))

theorem perfect_card_facts {F : Type} [Field F] [Finite F] (hF2 : ringChar F ≠ 2)
    {B : Subgroup (Matrix.SpecialLinearGroup (Fin 2) F)}
    {F' : Type*} [Field F'] [Finite F'] (hF' : 7 ≤ Nat.card F')
    (ν : B →* Matrix.SpecialLinearGroup (Fin 2) F') (hν : Function.Surjective ν) :
    Nat.card B = Nat.card ν.ker * (Nat.card F' * (Nat.card F' ^ 2 - 1)) ∧
      Nat.card B = 2 * Nat.card (B.map (nativeQuotient F)) ∧
      336 ≤ Nat.card F' * (Nat.card F' ^ 2 - 1) := by
  have hBk : Nat.card B = Nat.card ν.ker * (Nat.card F' * (Nat.card F' ^ 2 - 1)) := by
    rw [← CFSG.GorensteinWalter.sl2_card_formula F', Subgroup.card_ker_mul_card_of_surjective hν]
  refine ⟨hBk, card_eq_two_mul_card_map hF2 ?_, ?_⟩
  · rw [hBk]
    exact (perfect_even_mul_sq_sub_one _).mul_left _
  · have h49 : 49 ≤ Nat.card F' ^ 2 := by nlinarith
    calc 336 = 7 * (49 - 1) := by norm_num
      _ ≤ _ := Nat.mul_le_mul hF' (Nat.sub_le_sub_right h49 1)

theorem perfect_card_eq_of_mulEquiv_psl2 {F : Type} [Field F] [Finite F] (hF2 : ringChar F ≠ 2)
    {B : Subgroup (Matrix.SpecialLinearGroup (Fin 2) F)}
    {F' : Type*} [Field F'] [Finite F'] (hF' : 7 ≤ Nat.card F')
    (ν : B →* Matrix.SpecialLinearGroup (Fin 2) F') (hν : Function.Surjective ν)
    (hker : Odd (Nat.card ν.ker)) {K : Type*} [Field K] [Finite K]
    (hK : CFSG.GorensteinWalter.IsOddPrimePower (Nat.card K))
    (e : B.map (nativeQuotient F) ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 2) K) :
    Nat.card F' = Nat.card K := by
  obtain ⟨hBk, hB2, hbig⟩ := perfect_card_facts hF2 hF' ν hν
  have hkerpos : 0 < Nat.card ν.ker := Finite.card_pos
  have hHK : Nat.card (B.map (nativeQuotient F)) = Nat.card K * (Nat.card K ^ 2 - 1) / 2 := by
    rw [Nat.card_congr e.toEquiv]
    exact CFSG.GorensteinWalter.psl2_card_formula K hK
  have hHbig : 168 ≤ Nat.card (B.map (nativeQuotient F)) := by nlinarith
  have hq4 : 4 ≤ Nat.card K := by
    by_contra hlt
    have hle : Nat.card K ≤ 3 := by omega
    have : Nat.card K * (Nat.card K ^ 2 - 1) ≤ 24 :=
      (Nat.mul_le_mul hle (Nat.sub_le_sub_right (Nat.pow_le_pow_left hle 2) 1)).trans
        (by norm_num)
    omega
  have : IsSimpleGroup (Matrix.ProjectiveSpecialLinearGroup (Fin 2) K) :=
    Matrix.ProjectiveSpecialLinearGroup.rank_two_simple hq4
  have : IsSimpleGroup (B.map (nativeQuotient F)) := e.isSimpleGroup
  have : (ν.ker.map ((nativeQuotient F).subgroupMap B)).Normal :=
    Subgroup.Normal.map inferInstance _ ((nativeQuotient F).subgroupMap_surjective B)
  rcases Subgroup.Normal.eq_bot_or_eq_top (ν.ker.map ((nativeQuotient F).subgroupMap B)) with
    hbot | htop
  · have hinj : Function.Injective ν :=
      (MonoidHom.ker_eq_bot_iff ν).mp (perfect_eq_bot_of_map_eq_bot hF2 hker hbot)
    have hBeq := Nat.card_eq_of_bijective ν ⟨hinj, hν⟩
    rw [CFSG.GorensteinWalter.sl2_card_formula] at hBeq
    have h2 := Nat.two_mul_div_two_of_even (perfect_even_mul_sq_sub_one (Nat.card K))
    exact perfect_eq_of_mul_sq_sub_one_eq (by omega) (by omega) (by omega)
  · have hdvd := Subgroup.card_map_dvd ν.ker ((nativeQuotient F).subgroupMap B)
    rw [htop, Subgroup.card_top] at hdvd
    have := Nat.mul_le_mul (Nat.le_of_dvd hkerpos hdvd) hbig
    omega

theorem exists_card_eq_pow_of_perfect
    {F : Type} [Field F] [Finite F] {p f : ℕ} (hp : p.Prime)
    (hpodd : Odd p) (hcard : Nat.card F = p ^ f)
    {B : Subgroup (Matrix.SpecialLinearGroup (Fin 2) F)} (hB : Group.IsPerfect B)
    {F' : Type} [Field F'] [Finite F'] (hF' : 7 ≤ Nat.card F')
    (ν : B →* Matrix.SpecialLinearGroup (Fin 2) F') (hν : Function.Surjective ν)
    (hker : Odd (Nat.card ν.ker)) :
    ∃ m : ℕ, m ≠ 0 ∧ m ∣ f ∧ Nat.card F' = p ^ m := by
  have : Fact p.Prime := ⟨hp⟩
  have hF2 : ringChar F ≠ 2 := ringChar_ne_two_of_card hpodd hcard
  obtain ⟨hBk, hB2, hbig⟩ := perfect_card_facts hF2 hF' ν hν
  have hkerpos : 0 < Nat.card ν.ker := Finite.card_pos
  have hHbig : 168 ≤ Nat.card (B.map (nativeQuotient F)) := by nlinarith
  have hHperf : Group.IsPerfect (B.map (nativeQuotient F)) := Group.IsPerfect.map _
  rcases CFSG.Glauberman.Dickson.huppert_II_8_27_dickson_psl2_subgroup_classification hcard
      (B.map (nativeQuotient F)) with
    hEA | ⟨z, -, -, hcyc⟩ | ⟨z, -, -, ⟨e⟩⟩ | ⟨-, ⟨e⟩⟩ | ⟨-, ⟨e⟩⟩ | ⟨-, ⟨e⟩⟩ |
    ⟨m, t, -, -, N, C, hN, hNab, -, hC, -, -, hNC⟩ | ⟨m, hm, hmf, ⟨e⟩⟩ | ⟨m, hm, -, ⟨e⟩⟩
  · have := perfect_card_le_one (G := B.map (nativeQuotient F))
    omega
  · have := perfect_card_le_one (G := B.map (nativeQuotient F))
    omega
  · exact absurd (Group.IsPerfect.ofSurjective (f := e.toMonoidHom) e.surjective)
      (dihedralGroup_not_isPerfect z)
  · have h1 := Subgroup.card_le_card_group (alternatingGroup (Fin 4))
    rw [Nat.card_perm, Nat.card_fin] at h1
    have h2 : Nat.factorial 4 = 24 := rfl
    have h3 : Nat.card (B.map (nativeQuotient F)) = Nat.card (alternatingGroup (Fin 4)) :=
      Nat.card_congr e.toEquiv
    omega
  · have h1 : Nat.card (B.map (nativeQuotient F)) = Nat.card (Equiv.Perm (Fin 4)) :=
      Nat.card_congr e.toEquiv
    rw [Nat.card_perm, Nat.card_fin] at h1
    have h2 : Nat.factorial 4 = 24 := rfl
    omega
  · have h1 := Subgroup.card_le_card_group (alternatingGroup (Fin 5))
    rw [Nat.card_perm, Nat.card_fin] at h1
    have h2 : Nat.factorial 5 = 120 := rfl
    have h3 : Nat.card (B.map (nativeQuotient F)) = Nat.card (alternatingGroup (Fin 5)) :=
      Nat.card_congr e.toEquiv
    omega
  · have := perfect_isMulCommutative_of_sup_eq_top hNC
    have := perfect_card_le_one (G := B.map (nativeQuotient F))
    omega
  · have hK : Nat.card (GaloisField p m) = p ^ m := GaloisField.card p m hm
    have hKodd : CFSG.GorensteinWalter.IsOddPrimePower (Nat.card (GaloisField p m)) :=
      ⟨p, m, hp, hpodd, Nat.one_le_iff_ne_zero.mpr hm, hK⟩
    exact ⟨m, hm, hmf, (perfect_card_eq_of_mulEquiv_psl2 hF2 hF' ν hν hker hKodd e).trans hK⟩
  · have hKodd : CFSG.GorensteinWalter.IsOddPrimePower (Nat.card (GaloisField p m)) :=
      ⟨p, m, hp, hpodd, Nat.one_le_iff_ne_zero.mpr hm, GaloisField.card p m hm⟩
    exact absurd (Group.IsPerfect.ofSurjective (f := e.toMonoidHom) e.surjective)
      (perfect_pgl2_not_isPerfect hKodd)

theorem card_dvd_of_perfect
    {F : Type} [Field F] [Finite F] {p f : ℕ} (hp : p.Prime)
    (hpodd : Odd p) (hf : 1 ≤ f) (hcard : Nat.card F = p ^ f)
    {B : Subgroup (Matrix.SpecialLinearGroup (Fin 2) F)} (hB : Group.IsPerfect B)
    {F' : Type} [Field F'] [Finite F'] (hF' : 7 ≤ Nat.card F')
    (ν : B →* Matrix.SpecialLinearGroup (Fin 2) F') (hν : Function.Surjective ν)
    (hker : Odd (Nat.card ν.ker)) :
    Nat.card F' ∣ p ^ f := by
  obtain ⟨m, -, hmf, hm⟩ := exists_card_eq_pow_of_perfect hp hpodd hcard hB hF' ν hν hker
  rw [hm]
  exact pow_dvd_pow p (Nat.le_of_dvd (by omega) hmf)

end CFSG.Wreathed.OriginalAllPrime.LocalQD
