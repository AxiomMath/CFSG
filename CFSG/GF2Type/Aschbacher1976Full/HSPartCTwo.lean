module

public import CFSG.GF2Type.Aschbacher1976Full.HSInterfaces
public import CFSG.GF2Type.Aschbacher1976Full.HSPartCGen

public section

namespace CFSG.GF2Type.Aschbacher1976Full.HS.PartC

open CFSG CFSG.Blueprint CFSG.GF2Type.CenterFour Subgroup

variable {G : Type} [Group G] [Finite G]

theorem exists_injective_iota (hEmb : EmbedStmt) {z : G} (hz : orderOf z = 2)
    (hZ4 : IsZ4Star z 2) (hF2 : IsPGroup 2 (Fz z)) :
    ∃ ι : Qbar z →* Equiv.Perm (Fin 6), Function.Injective ι := by
  obtain ⟨ι₀, hker⟩ := hEmb hZ4 hz hF2
  refine ⟨QuotientGroup.lift _ ι₀ (le_of_eq hker.symm), ?_⟩
  rw [injective_iff_map_eq_one]
  intro q hq
  obtain ⟨h, rfl⟩ := qmk_surjective z q
  have hh : h ∈ ι₀.ker := by
    rw [MonoidHom.mem_ker]
    simpa [qmk] using hq
  rw [hker] at hh
  exact (qmk_eq_one_iff z h).mpr (Subgroup.mem_subgroupOf.mp hh)

theorem O2_quotient_trivial {z : G} (hF2 : IsPGroup 2 (Fz z)) :
    ∀ N : Subgroup (Qbar z), N.Normal → IsPGroup 2 N → N = ⊥ := by
  intro N hN hN2
  have hker : IsPGroup 2 ↥(qmk z).ker := by
    rw [ker_qmk]
    exact hF2.comap_subtype
  have hpre : IsPGroup 2 ↥(N.comap (qmk z)) := IsPGroup.comap_of_ker_isPGroup hN2 (qmk z) hker
  have hle : (N.comap (qmk z)).map (Hz z).subtype ≤ Fz z := by
    apply Width.le_Fz_of_normal_two hF2
    · rintro _ ⟨h, -, rfl⟩
      exact h.2
    · rintro g hg _ ⟨h, hh, rfl⟩
      refine ⟨⟨g, hg⟩ * h * ⟨g, hg⟩⁻¹, ?_, rfl⟩
      have hh' : qmk z h ∈ N := hh
      show qmk z (⟨g, hg⟩ * h * ⟨g, hg⟩⁻¹) ∈ N
      rw [map_mul, map_mul, map_inv]
      exact hN.conj_mem _ hh' _
    · exact hpre.map _
  rw [eq_bot_iff]
  intro n hn
  obtain ⟨h, rfl⟩ := qmk_surjective z n
  have hF : (h : G) ∈ Fz z := hle ⟨h, hn, rfl⟩
  rw [(qmk_eq_one_iff z h).mpr hF]
  exact one_mem _

section Product

variable {z : G} {Z A : Subgroup G}

theorem TI_Z (hD : Width.Z4Data z 2 Z A) (hz : orderOf z = 2) (hF2 : IsPGroup 2 (Fz z)) :
    ∀ g : G, conjugate Z g = Z ∨ Z ⊓ conjugate Z g = ⊥ := by
  intro g
  rcases Width.conj_pair_eq_or_disjoint hD hz hF2 1 g with h | h
  · rw [Width.conjugate_one'] at h
    exact Or.inl h.symm
  · rw [Width.conjugate_one'] at h
    exact Or.inr h

theorem orderOf_yBar_mul_ne_four (hD : Width.Z4Data z 2 Z A) (hz : orderOf z = 2)
    (hF2 : IsPGroup 2 (Fz z)) (hti : HSTI z) {u u' : G} (hu : u ∈ Dinv z) (hu' : u' ∈ Dinv z) :
    orderOf (yBar z u * yBar z u') ≠ 4 := by
  intro h4
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨y, hy⟩ := exists_gen_H hD hz hF2 hu
  obtain ⟨y', hy'⟩ := exists_gen_H hD hz hF2 hu'
  have ha : yBar z u = qmk z y := yBar_eq hD hz hF2 hti hu hy
  have ha' : yBar z u' = qmk z y' := yBar_eq hD hz hF2 hti hu' hy'
  set a := yBar z u with ha_def
  set a' := yBar z u' with ha'_def
  have ha2 : a * a = 1 := by rw [← pow_two]; exact yBar_sq hD hz hF2 hti hu
  have ha'2 : a' * a' = 1 := by rw [← pow_two]; exact yBar_sq hD hz hF2 hti hu'
  have hai : a⁻¹ = a := inv_eq_of_mul_eq_one_left ha2
  have ha'i : a'⁻¹ = a' := inv_eq_of_mul_eq_one_left ha'2
  have hao : orderOf a = 2 := orderOf_yBar hD hz hF2 hti hu
  set c := a * a' with hc
  have hac : a * c * a⁻¹ = c⁻¹ := by
    rw [hc, mul_inv_rev, ha'i, hai]
    calc a * (a * a') * a = (a * a) * a' * a := by simp only [mul_assoc]
      _ = a' * a := by rw [ha2, one_mul]
  have hnorm : zpowers a ≤ Subgroup.normalizer (zpowers c : Set (Qbar z)) := by
    rw [zpowers_le, Subgroup.mem_normalizer_iff]
    intro h
    constructor
    · intro hh
      obtain ⟨i, rfl⟩ := mem_zpowers_iff.mp hh
      refine mem_zpowers_iff.mpr ⟨-i, ?_⟩
      rw [← conj_zpow, hac, inv_zpow, zpow_neg]
    · intro hh
      obtain ⟨i, hi⟩ := mem_zpowers_iff.mp hh
      refine mem_zpowers_iff.mpr ⟨-i, ?_⟩
      calc c ^ (-i) = (c⁻¹) ^ i := by rw [zpow_neg, inv_zpow]
        _ = (a * c * a⁻¹) ^ i := by rw [hac]
        _ = a * c ^ i * a⁻¹ := conj_zpow
        _ = a⁻¹ * c ^ i * a := by rw [hai]
        _ = a⁻¹ * (a * h * a⁻¹) * a := by rw [hi]
        _ = h := by group
  have hP1 : IsPGroup 2 ↥(zpowers a) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hao]; norm_num)
  have hP2 : IsPGroup 2 ↥(zpowers c) :=
    IsPGroup.of_card (n := 2) (by rw [Nat.card_zpowers, h4]; norm_num)
  have hS := IsPGroup.to_sup_of_normal_right' hP1 hP2 hnorm
  have hker : IsPGroup 2 ↥(qmk z).ker := by
    rw [ker_qmk]
    exact hF2.comap_subtype
  have hS0 : IsPGroup 2 ↥(((zpowers a ⊔ zpowers c).comap (qmk z)).map (Hz z).subtype) :=
    (IsPGroup.comap_of_ker_isPGroup hS (qmk z) hker).map _
  have hay : (y : G) ∈ ((zpowers a ⊔ zpowers c).comap (qmk z)).map (Hz z).subtype := by
    refine ⟨y, Subgroup.mem_comap.mpr ?_, rfl⟩
    rw [← ha]
    exact mem_sup_left (mem_zpowers a)
  have hay' : (y' : G) ∈ ((zpowers a ⊔ zpowers c).comap (qmk z)).map (Hz z).subtype := by
    refine ⟨y', Subgroup.mem_comap.mpr ?_, rfl⟩
    rw [← ha']
    have : a' = a * c := by rw [hc, ← mul_assoc, ha2, one_mul]
    rw [this]
    exact Subgroup.mul_mem _ (mem_sup_left (mem_zpowers a)) (mem_sup_right (mem_zpowers c))
  obtain ⟨g, hg⟩ := exists_conj hu.1
  obtain ⟨g', hg'⟩ := exists_conj hu'.1
  have hZu : ZF u = conjugate Z g := by rw [hg]; exact ZF_conj hD hz hF2 g
  have hZu' : ZF u' = conjugate Z g' := by rw [hg']; exact ZF_conj hD hz hF2 g'
  have hle : conjugate Z g ≤ ((zpowers a ⊔ zpowers c).comap (qmk z)).map (Hz z).subtype := by
    rw [← hZu, hy]
    exact zpowers_le.mpr hay
  have hle' : conjugate Z g' ≤ ((zpowers a ⊔ zpowers c).comap (qmk z)).map (Hz z).subtype := by
    rw [← hZu', hy']
    exact zpowers_le.mpr hay'
  have hZ2 : IsPGroup 2 ↥Z := IsPGroup.of_card (n := 2) (by rw [hD.card_Z]; norm_num)
  have hcomm := CFSG.GF2Type.Aschbacher1976Common.commute_of_conjugate_le hD.cyc hZ2
    (by rw [hD.card_Z]) (TI_Z hD hz hF2) hS0 hle hle' (y : G)
    (by rw [← hZu, hy]; exact mem_zpowers _) (y' : G) (by rw [← hZu', hy']; exact mem_zpowers _)
  have hyy' : y * y' = y' * y := Subtype.ext hcomm
  have hcom : a * a' = a' * a := by
    rw [ha, ha', ← map_mul, ← map_mul, hyy']
  have hsq : (a * a') ^ 2 = 1 := by
    rw [(Commute.mul_pow (hcom : Commute a a')), pow_two, pow_two, ha2, ha'2, one_mul]
  have := orderOf_dvd_of_pow_eq_one hsq
  rw [h4] at this
  omega

end Product

end CFSG.GF2Type.Aschbacher1976Full.HS.PartC
