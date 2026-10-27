module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitInputs
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PSL2DihedralSylow
public import CFSG.LocalAnalysis.SectionRank.OddCover.PSL2
public import CFSG.LocalAnalysis.ComponentInitial.AlternatingFourGroup
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBSmallReeTorus

public section

namespace CFSG.ComponentClassification.HarrisLit

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
open CFSG.Assembly.LowTwoRank (projectiveSpecialLinearGroupEquivStatedProj)

section PSL

variable (K : Type) [Field K] [Finite K]

theorem dihedral_commuting_involutions {m : ℕ} (hm : 1 ≤ m) :
    orderOf (DihedralGroup.r (1 : ZMod (2 ^ m)) ^ 2 ^ (m - 1)) = 2 ∧
      orderOf (DihedralGroup.sr (0 : ZMod (2 ^ m))) = 2 ∧
      DihedralGroup.r (1 : ZMod (2 ^ m)) ^ 2 ^ (m - 1) * DihedralGroup.sr 0 =
        DihedralGroup.sr 0 * DihedralGroup.r (1 : ZMod (2 ^ m)) ^ 2 ^ (m - 1) ∧
      DihedralGroup.r (1 : ZMod (2 ^ m)) ^ 2 ^ (m - 1) ≠ DihedralGroup.sr 0 := by
  have h2 : 2 * 2 ^ (m - 1) = 2 ^ m := by rw [← pow_succ', Nat.sub_add_cancel hm]
  refine ⟨?_, DihedralGroup.orderOf_sr 0, ?_, ?_⟩
  · rw [orderOf_pow_of_dvd (pow_ne_zero _ two_ne_zero) ?_, DihedralGroup.orderOf_r_one,
      Nat.pow_div (Nat.sub_le m 1) two_pos, show m - (m - 1) = 1 by omega, pow_one]
    rw [DihedralGroup.orderOf_r_one]
    exact pow_dvd_pow 2 (Nat.sub_le m 1)
  · rw [DihedralGroup.r_one_pow, DihedralGroup.r_mul_sr, DihedralGroup.sr_mul_r]
    congr 1
    rw [zero_sub, zero_add, neg_eq_iff_add_eq_zero, ← two_mul]
    have h3 : (2 : ZMod (2 ^ m)) * ((2 ^ (m - 1) : ℕ) : ZMod (2 ^ m)) =
        ((2 * 2 ^ (m - 1) : ℕ) : ZMod (2 ^ m)) := by push_cast; ring
    rw [h3, h2, ZMod.natCast_self]
  · rw [DihedralGroup.r_one_pow]
    intro h
    cases h

theorem two_le_pRank_psl2 (hodd : GorensteinWalter.IsOddPrimePower (Nat.card K)) :
    2 ≤ Open.pRank 2 (⊤ : Subgroup (Matrix.ProjectiveSpecialLinearGroup (Fin 2) K)) := by
  obtain ⟨S⟩ := (inferInstance :
    Nonempty (Sylow 2 (Matrix.ProjectiveSpecialLinearGroup (Fin 2) K)))
  obtain ⟨m, hm, ⟨eS⟩⟩ := GorensteinWalter.psl2_odd_hasDihedralSylowTwo_model K hodd S
  obtain ⟨ha, hb, hab, hne⟩ := dihedral_commuting_involutions hm
  set a := DihedralGroup.r (1 : ZMod (2 ^ m)) ^ 2 ^ (m - 1)
  set b := DihedralGroup.sr (0 : ZMod (2 ^ m))
  obtain ⟨V, -, hV, hVcard⟩ :=
    CFSG.LocalAnalysis.ComponentInitial.AlternatingFourGroup.exists_elementary_four_of_commute
      (x := ((eS.symm a : ↥S) : Matrix.ProjectiveSpecialLinearGroup (Fin 2) K))
      (y := ((eS.symm b : ↥S) : Matrix.ProjectiveSpecialLinearGroup (Fin 2) K))
      (by rw [Subgroup.orderOf_coe, MulEquiv.orderOf_eq, ha])
      (by rw [Subgroup.orderOf_coe, MulEquiv.orderOf_eq, hb])
      (by rw [← Subgroup.coe_mul, ← Subgroup.coe_mul, ← map_mul, ← map_mul, hab])
      (fun h => hne (eS.symm.injective (Subtype.ext h)))
  exact SectionRank.le_pRank one_lt_two le_top
    ((SectionRank.isElementaryAbelian_iff_isElemAbelian 2 V).mp hV)
    (by rw [hVcard]; norm_num)

theorem pRank_psl2_le_two (hodd : GorensteinWalter.IsOddPrimePower (Nat.card K))
    (h8 : (Nat.card (Matrix.ProjectiveSpecialLinearGroup (Fin 2) K)).factorization 2 = 3) :
    Open.pRank 2 (⊤ : Subgroup (Matrix.ProjectiveSpecialLinearGroup (Fin 2) K)) ≤ 2 := by
  refine SectionRank.pRank_le one_lt_two fun E _ hE => ?_
  have hexp : ∀ x : E, x ^ 2 = 1 := fun x =>
    Subtype.ext (by rw [Subgroup.coe_pow, hE.2 x x.2, Subgroup.coe_one])
  have hE2 : IsPGroup 2 E := IsPGroup.of_exponent_dvd_pow (n := 1)
    (by rw [pow_one]; exact Monoid.exponent_dvd_of_forall_pow_eq_one hexp)
  obtain ⟨n, hn⟩ := hE2.exists_card_eq
  have hdvd : 2 ^ n ∣ Nat.card (Matrix.ProjectiveSpecialLinearGroup (Fin 2) K) :=
    hn ▸ E.card_subgroup_dvd_card
  have hn3 : n ≤ 3 := by
    rw [← h8]
    exact (Nat.prime_two.pow_dvd_iff_le_factorization Nat.card_pos.ne').mp hdvd
  rcases Nat.lt_or_ge n 3 with hlt | hge
  · rw [hn]
    exact Nat.pow_le_pow_right two_pos (by omega)
  · exfalso
    have hn' : n = 3 := le_antisymm hn3 hge
    let S : Sylow 2 (Matrix.ProjectiveSpecialLinearGroup (Fin 2) K) :=
      Sylow.ofCard E (by rw [hn, hn', h8])
    obtain ⟨m, -, ⟨eS⟩⟩ := GorensteinWalter.psl2_odd_hasDihedralSylowTwo_model K hodd S
    have hcard : 2 * 2 ^ m = 8 := by
      have h1 := Nat.card_congr eS.toEquiv
      rw [DihedralGroup.nat_card] at h1
      rw [← h1]
      change Nat.card E = 8
      rw [hn, hn']
      norm_num
    have hm4 : 2 ^ m = 4 := by omega
    have hord : orderOf (eS.symm (DihedralGroup.r 1)) = 4 := by
      rw [MulEquiv.orderOf_eq, DihedralGroup.orderOf_r_one, hm4]
    have hsq : eS.symm (DihedralGroup.r 1) ^ 2 = 1 := by
      apply Subtype.ext
      rw [Subgroup.coe_pow, Subgroup.coe_one]
      exact hE.2 _ (eS.symm (DihedralGroup.r 1)).2
    have := orderOf_dvd_of_pow_eq_one hsq
    rw [hord] at this
    norm_num at this

end PSL

namespace Config

variable {X : Type} [Group X] {t : X} {L : Subgroup X} {p f : ℕ}

theorem exists_psl2 (h : Config t L p f) :
    ∃ (K : Type) (_ : Field K) (_ : Finite K), Nat.card K = p ^ f ∧
      Nonempty (Bar L ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 2) K) := by
  rcases h.lieModel with ⟨-, hm⟩ | ⟨h0, -⟩ | ⟨h0, -⟩ | ⟨h0, -⟩
  · obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := hm
    exact ⟨K, inferInstance, inferInstance, hK,
      ⟨e.trans (projectiveSpecialLinearGroupEquivStatedProj 2 K).symm⟩⟩
  all_goals exact absurd h0 (by norm_num)

theorem isOddPrimePower (h : Config t L p f) {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = p ^ f) : GorensteinWalter.IsOddPrimePower (Nat.card K) :=
  ⟨p, f, h.prime, h.prime.odd_of_ne_two h.ne_two, h.one_le, hK⟩

theorem isSimpleGroup_bar (h : Config t L p f) : IsSimpleGroup (Bar L) := by
  obtain ⟨K, _, _, hK, ⟨e⟩⟩ := h.exists_psl2
  have h5 := h.five_le
  have : IsSimpleGroup (Matrix.ProjectiveSpecialLinearGroup (Fin 2) K) :=
    BenderSuzuki.External.huppert_II_6_13 2 le_rfl (Or.inr (by omega)) (Or.inr (by omega))
  exact e.isSimpleGroup

theorem nonabelian_bar (h : Config t L p f) : ∃ a b : Bar L, a * b ≠ b * a := by
  obtain ⟨K, _, _, hK, ⟨e⟩⟩ := h.exists_psl2
  have h5 := h.five_le
  obtain ⟨x, y, hxy⟩ :=
    CatalogueBSmallRee.projectiveSpecialLinear_two_nonabelian K (by omega) (by omega)
  exact ⟨e.symm x, e.symm y, fun hc => hxy (by simpa using congrArg e hc)⟩

theorem card_bar (h : Config t L p f) :
    Nat.card (Bar L) = p ^ f * (((p ^ f) ^ 2 - 1) / 2) := by
  obtain ⟨K, _, _, hK, ⟨e⟩⟩ := h.exists_psl2
  rw [Nat.card_congr e.toEquiv]
  exact SectionRank.OddCover.card_psl_two h.prime h.ne_two hK

theorem two_le_pRank_bar [Finite X] (h : Config t L p f) :
    2 ≤ Open.pRank 2 (⊤ : Subgroup (Bar L)) := by
  obtain ⟨K, _, _, hK, ⟨e⟩⟩ := h.exists_psl2
  rw [SectionRank.pRank_top_eq_of_mulEquiv one_lt_two e]
  exact two_le_pRank_psl2 K (h.isOddPrimePower hK)

theorem pRank_bar_eq_two [Finite X] (h : Config t L p f)
    (h8 : (Nat.card (Bar L)).factorization 2 = 3) : CFSG.pRank 2 (Bar L) = 2 := by
  obtain ⟨K, _, _, hK, ⟨e⟩⟩ := h.exists_psl2
  have hodd := h.isOddPrimePower hK
  rw [SectionRank.pRank_eq_open_pRank_top, SectionRank.pRank_top_eq_of_mulEquiv one_lt_two e]
  exact le_antisymm (pRank_psl2_le_two K hodd (by rwa [← Nat.card_congr e.toEquiv]))
    (two_le_pRank_psl2 K hodd)

theorem factorization_card_bar (h : Config t L p f) (h9 : p ^ f % 16 = 9) :
    (Nat.card (Bar L)).factorization 2 = 3 := by
  rw [h.card_bar]
  obtain ⟨k, hk⟩ : ∃ k, p ^ f = 16 * k + 9 := ⟨p ^ f / 16, by omega⟩
  have hsq : ((p ^ f) ^ 2 - 1) / 2 = 2 ^ 3 * (16 * k ^ 2 + 18 * k + 5) := by
    rw [hk]
    have : (16 * k + 9) ^ 2 = 2 * (2 ^ 3 * (16 * k ^ 2 + 18 * k + 5)) + 1 := by ring
    rw [this, Nat.add_sub_cancel, Nat.mul_div_cancel_left _ two_pos]
  have hq : ¬ 2 ∣ p ^ f := by omega
  have hm : ¬ 2 ∣ 16 * k ^ 2 + 18 * k + 5 := by omega
  rw [hsq, Nat.factorization_mul (by omega) (by positivity), Finsupp.add_apply,
    Nat.factorization_eq_zero_of_not_dvd hq, zero_add,
    Nat.factorization_mul (by positivity) (by omega), Finsupp.add_apply,
    Nat.factorization_eq_zero_of_not_dvd hm, add_zero, Nat.Prime.factorization_pow Nat.prime_two,
    Finsupp.single_eq_same]

theorem center_bar_eq_bot (h : Config t L p f) : center (Bar L) = ⊥ := by
  have := h.isSimpleGroup_bar
  rcases (inferInstance : (center (Bar L)).Normal).eq_bot_or_eq_top with hb | ht
  · exact hb
  · exfalso
    obtain ⟨a, b, hab⟩ := h.nonabelian_bar
    have ha : a ∈ center (Bar L) := by rw [ht]; exact mem_top a
    exact hab ((mem_center_iff.mp ha b).symm)

theorem not_mem [Finite X] (h : Config t L p f) : t ∉ L := by
  intro htL
  set t' : L := ⟨t, htL⟩ with ht'
  have hcent : t' ∈ center L := by
    rw [mem_center_iff]
    intro g
    apply Subtype.ext
    exact mem_centralizer_singleton_iff.mp (h.le_centralizer g.2)
  have hcentq : (QuotientGroup.mk t' : Bar L) ∈ center (Bar L) := by
    rw [mem_center_iff]
    intro q
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective q
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, mem_center_iff.mp hcent g]
  rw [h.center_bar_eq_bot, mem_bot, QuotientGroup.eq_one_iff] at hcentq
  have hdvd : orderOf t' ∣ Nat.card (pPrimeCore 2 L) :=
    Subgroup.orderOf_dvd_natCard (pPrimeCore 2 L) hcentq
  rw [ht', Subgroup.orderOf_mk, h.orderOf_eq] at hdvd
  have hcop : Nat.Coprime 2 (Nat.card (pPrimeCore 2 L)) := pPrimeCore_coprime_card
  exact absurd (Nat.Coprime.eq_one_of_dvd hcop hdvd) (by norm_num)

end Config

end CFSG.ComponentClassification.HarrisLit
