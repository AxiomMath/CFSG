module

public import CFSG.GroupTheory.ABGDGroups.LinearStructure
public import CFSG.ThirdParty.QiuzhenCFSG.Glauberman.DicksonClassification
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PGL2LowTorus
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PGL2OuterInvolutionFusion
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.CardSupOfDisjointNormalizer
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PGammaL2PureSemilinear
public import CFSG.LocalAnalysis.RankThreeEvenClassification.CoprimeAmbientCentralizerGeneration

public noncomputable section

namespace CFSG.ABGDGroups

open CFSG.GorensteinWalter (PGammaL2 PSL2 PGL2 IsOddPrimePower pGammaL2PSLRange
  pGammaL2PGLRange mem_pGammaL2PSLRange_iff card_sup_eq_mul_of_disjoint_of_le_normalizer)

section Involutions

variable {F : Type} [Field F] [Finite F]

theorem psl2_eq_one_of_commute_of_orderOf_eq_prime_pow {p f : ℕ} [Fact p.Prime]
    (hcard : Nat.card F = p ^ f) (hp2 : p ≠ 2) {t u : PSL2 F} (ht : orderOf t = 2) {k : ℕ}
    (hu : orderOf u = p ^ k) (hc : t * u = u * t) : u = 1 := by
  classical
  by_contra hu1
  have hp : p.Prime := Fact.out
  have hk : k ≠ 0 := by
    rintro rfl
    rw [pow_zero, orderOf_eq_one_iff] at hu
    exact hu1 hu
  have hpk : Odd (p ^ k) := (hp.odd_of_ne_two hp2).pow
  obtain ⟨P⟩ : Nonempty (Sylow p (PSL2 F)) := inferInstance
  obtain ⟨U, S, -, -, -, -, hpart⟩ :=
    CFSG.Glauberman.Dickson.huppert_II_8_5_a_psl2_cover hcard P
  have hcomm : Commute u t := hc.symm
  have ht2 : t ^ 2 = 1 := by
    have h := pow_orderOf_eq_one t
    rwa [ht] at h
  have hyt : (u * t) ^ (p ^ k) = t := by
    rw [hcomm.mul_pow, ← hu, pow_orderOf_eq_one, one_mul, hu]
    obtain ⟨j, hj⟩ := hpk
    rw [hj, pow_succ, pow_mul, ht2, one_pow, one_mul]
  have hyu : (u * t) ^ 2 = u ^ 2 := by
    rw [hcomm.mul_pow, ht2, mul_one]
  have hu2 : u ^ 2 ≠ 1 := by
    intro h
    have h' := orderOf_dvd_of_pow_eq_one h
    rw [hu] at h'
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp ((dvd_pow_self p hk).trans h'))
  have hy1 : u * t ≠ 1 := by
    intro h
    rw [h, one_pow] at hyu
    exact hu2 hyu.symm
  obtain ⟨X, ⟨hyX, hXmem⟩, -⟩ := hpart (u * t) hy1
  have htX : t ∈ X := hyt ▸ X.pow_mem hyX _
  have hu2X : u ^ 2 ∈ X := hyu ▸ X.pow_mem hyX _
  have hup : IsPGroup p (Subgroup.zpowers u) := by
    apply IsPGroup.of_card (n := k)
    rw [Nat.card_zpowers, hu]
  obtain ⟨Q, hQ⟩ := hup.exists_le_sylow
  have huQ : u ∈ (Q : Subgroup (PSL2 F)) := hQ (Subgroup.mem_zpowers u)
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (PSL2 F) P Q
  have hQmem : ∃ g : PSL2 F,
      (Q : Subgroup (PSL2 F)) = (P : Subgroup (PSL2 F)).map (MulAut.conj g).toMonoidHom :=
    ⟨g, by rw [← hg]; rfl⟩
  have hXQ : X = Q :=
    (hpart (u ^ 2) hu2).unique ⟨hu2X, hXmem⟩ ⟨(Q : Subgroup (PSL2 F)).pow_mem huQ 2,
      Or.inl hQmem⟩
  have htQ : t ∈ (Q : Subgroup (PSL2 F)) := hXQ ▸ htX
  obtain ⟨n, hn⟩ := Q.isPGroup' ⟨t, htQ⟩
  have h2 : 2 ∣ p ^ n := by
    rw [← ht, ← Subgroup.orderOf_mk t htQ]
    exact orderOf_dvd_of_pow_eq_one hn
  exact hp2 ((Nat.prime_dvd_prime_iff_eq Nat.prime_two hp).mp
    (Nat.prime_two.dvd_of_dvd_pow h2)).symm

theorem card_sup_zpowers_of_inverts {G : Type*} [Group G] [Finite G] {U : Subgroup G} {w : G}
    (hwU : w ∉ U) (hw : w * w = 1) (hinv : ∀ x ∈ U, w * x * w⁻¹ = x⁻¹) :
    Nat.card (U ⊔ Subgroup.zpowers w : Subgroup G) = Nat.card U * 2 := by
  have hw1 : w ≠ 1 := fun h => hwU (h ▸ U.one_mem)
  have hord : orderOf w = 2 := orderOf_eq_prime (by rw [sq]; exact hw) hw1
  have hnorm : Subgroup.zpowers w ≤ Subgroup.normalizer (U : Set G) := by
    rw [Subgroup.zpowers_le]
    apply Subgroup.mem_normalizer_fintype
    intro x hx
    rw [hinv x hx]
    exact U.inv_mem hx
  have hdisj : Disjoint U (Subgroup.zpowers w) := by
    rw [Subgroup.disjoint_def]
    intro x hxU hxw
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hxw
    have hk : w ^ k = w ^ (k % 2) := by
      rw [← zpow_mod_orderOf, hord]
      rfl
    rw [hk] at hxU ⊢
    rcases Int.emod_two_eq_zero_or_one k with h | h
    · rw [h, zpow_zero]
    · rw [h, zpow_one] at hxU
      exact absurd hxU hwU
  rw [card_sup_eq_mul_of_disjoint_of_le_normalizer U _ hnorm hdisj, Nat.card_zpowers, hord]

theorem pgl2_eq_one_of_commute_of_orderOf_eq_prime_pow (hF : IsOddPrimePower (Nat.card F))
    (h3 : 3 < Nat.card F) {p f : ℕ} [Fact p.Prime] (hcard : Nat.card F = p ^ f) (hp2 : p ≠ 2)
    {t u : PGL2 F} (ht : orderOf t = 2) {k : ℕ} (hu : orderOf u = p ^ k)
    (huJ : u ∈ (Matrix.ProjectiveSpecialLinearGroup.toPGL (n := Fin 2) (R := F)).range)
    (hc : t * u = u * t) : u = 1 := by
  set toPGL := Matrix.ProjectiveSpecialLinearGroup.toPGL (n := Fin 2) (R := F)
  have hinj : Function.Injective toPGL := Matrix.ProjectiveSpecialLinearGroup.toPGL_injective
  have hp : p.Prime := Fact.out
  have hJ : commutator (PGL2 F) = toPGL.range :=
    CFSG.GorensteinWalter.pgl2_commutator_eq_psl2_range_of_card_gt_three F hF h3
  by_cases htJ : t ∈ toPGL.range
  ·
    obtain ⟨t', rfl⟩ := htJ
    obtain ⟨u', rfl⟩ := huJ
    have h := psl2_eq_one_of_commute_of_orderOf_eq_prime_pow hcard hp2
      (t := t') (u := u') (by rw [← orderOf_injective toPGL hinj t']; exact ht)
      (by rw [← orderOf_injective toPGL hinj u']; exact hu) (hinj (by rw [map_mul, map_mul, hc]))
    rw [h, map_one]
  ·
    obtain ⟨U, s, -, w, -, -, hUcard, -, hsJ, hs1, hss, -, -, -, -, -, hwU, hww, hwinv, hcent⟩ :=
      CFSG.GorensteinWalter.pgl2_low_two_part_torus_reflection_data F hF h3
    have ht1 : t ≠ 1 := by
      rintro rfl
      rw [orderOf_one] at ht
      exact absurd ht (by norm_num)
    have htI : CFSG.BenderSuzuki.PFAppendixIII.IsInvolution t :=
      ⟨ht1, by have h := pow_orderOf_eq_one t; rwa [ht] at h⟩
    have hsI : CFSG.BenderSuzuki.PFAppendixIII.IsInvolution s := ⟨hs1, by rw [sq]; exact hss⟩
    have hconj := CFSG.GorensteinWalter.pgl2_outer_involutions_conjugate F hF h3 htI hsI
      (by rwa [hJ]) hsJ
    obtain ⟨g, hg⟩ := isConj_iff.mp hconj
    have hmem : g * u * g⁻¹ ∈ Subgroup.centralizer ({s} : Set (PGL2 F)) := by
      rw [Subgroup.mem_centralizer_singleton_iff, ← hg]
      calc g * u * g⁻¹ * (g * t * g⁻¹) = g * (u * t) * g⁻¹ := by group
        _ = g * (t * u) * g⁻¹ := by rw [hc]
        _ = g * t * g⁻¹ * (g * u * g⁻¹) := by group
    rw [hcent] at hmem
    have hdvd := Subgroup.orderOf_dvd_natCard _ hmem
    rw [card_sup_zpowers_of_inverts hwU hww hwinv, ← MulAut.conj_apply, MulEquiv.orderOf_eq,
      hu] at hdvd
    by_contra hu1
    have hk : k ≠ 0 := by
      rintro rfl
      rw [pow_zero, orderOf_eq_one_iff] at hu
      exact hu1 hu
    have hpq : p ∣ Nat.card F := by
      rw [hcard]
      obtain ⟨p', f', hp', -, hf', hq'⟩ := hF
      have : f ≠ 0 := by
        rintro rfl
        rw [hcard, pow_zero] at hq'
        exact absurd hq' (Nat.one_lt_pow (by omega) hp'.one_lt).ne
      exact dvd_pow_self p this
    have hpU := ((dvd_pow_self p hk).trans hdvd)
    rcases (Nat.Prime.dvd_mul hp).mp hpU with h | h
    · rcases hUcard with h' | h'
      · rw [h'] at h
        have h1 : p ∣ Nat.card F - (Nat.card F - 1) := Nat.dvd_sub hpq h
        rw [Nat.sub_sub_self (by omega)] at h1
        exact hp.one_lt.ne' (Nat.dvd_one.mp h1)
      · rw [h'] at h
        have h1 : p ∣ Nat.card F + 1 - Nat.card F := Nat.dvd_sub h hpq
        rw [Nat.add_sub_cancel_left] at h1
        exact hp.one_lt.ne' (Nat.dvd_one.mp h1)
    · exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp h)

end Involutions

section OddSubgroups

variable {F : Type} [Field F] [Finite F]

private theorem two_dvd_card_psl2_of_isOddPrimePower {F' : Type} [Field F'] [Finite F']
    (hF' : IsOddPrimePower (Nat.card F')) : 2 ∣ Nat.card (PSL2 F') := by
  obtain ⟨P⟩ : Nonempty (Sylow 2 (PSL2 F')) := inferInstance
  obtain ⟨m, -, ⟨e⟩⟩ := CFSG.GorensteinWalter.psl2_odd_hasDihedralSylowTwo_model F' hF' P
  have hP : Nat.card (P : Subgroup (PSL2 F')) = 2 * 2 ^ m := by
    rw [Nat.card_congr e.toEquiv, DihedralGroup.nat_card]
  exact (Dvd.intro _ hP.symm).trans (Subgroup.card_subgroup_dvd_card _)

theorem psl2_odd_isCyclic_or_exists_pSubgroup {p f : ℕ} [Fact p.Prime]
    (hcard : Nat.card F = p ^ f) (hp2 : p ≠ 2) (K₀ : Subgroup (PSL2 F))
    (hK₀ : Odd (Nat.card K₀)) :
    IsCyclic K₀ ∨ ∃ N : Subgroup (PSL2 F), N ≤ K₀ ∧ N ≠ ⊥ ∧ IsPGroup p N ∧
      ∀ x ∈ K₀, ∀ k : ℕ, orderOf x = p ^ k → x ∈ N := by
  classical
  have hp : p.Prime := Fact.out
  have hpodd : Odd p := hp.odd_of_ne_two hp2
  have heven : ∀ n : ℕ, Nat.card K₀ = 2 * n → False := fun n h => by
    rw [h] at hK₀
    exact (Nat.not_even_iff_odd.mpr hK₀) (even_two_mul n)
  have hGF : ∀ m : ℕ, m ≠ 0 → IsOddPrimePower (Nat.card (GaloisField p m)) := fun m hm =>
    ⟨p, m, hp, hpodd, Nat.pos_of_ne_zero hm, GaloisField.card p m hm⟩
  rcases CFSG.Glauberman.Dickson.huppert_II_8_27_dickson_psl2_subgroup_classification hcard K₀ with
    helem | ⟨z, -, -, hcyc⟩ | ⟨z, -, hcard2, -⟩ | ⟨-, ⟨e⟩⟩ | ⟨-, ⟨e⟩⟩ | ⟨-, ⟨e⟩⟩ |
      ⟨m, t, ht, -, N, C, hNn, -, hNcard, hCcyc, hCcard, hdisj, hsup⟩ | ⟨m, hm, -, ⟨e⟩⟩ |
      ⟨m, hm, -, ⟨e⟩⟩
  ·
    by_cases hbot : K₀ = ⊥
    · left
      rw [hbot]
      infer_instance
    · exact Or.inr ⟨K₀, le_rfl, hbot, CFSG.IsElementaryAbelian.isPGroup p K₀,
        fun x hx _ _ => hx⟩
  · exact Or.inl hcyc
  · exact (heven z hcard2).elim
  · refine (heven 6 ?_).elim
    rw [Nat.card_congr e.toEquiv, nat_card_alternatingGroup, Nat.card_eq_fintype_card,
      Fintype.card_fin]
    decide
  · refine (heven 12 ?_).elim
    rw [Nat.card_congr e.toEquiv, Nat.card_perm, Nat.card_eq_fintype_card, Fintype.card_fin]
    decide
  · refine (heven 30 ?_).elim
    rw [Nat.card_congr e.toEquiv, nat_card_alternatingGroup, Nat.card_eq_fintype_card,
      Fintype.card_fin]
    decide
  ·
    have hNC : N.IsComplement' C := Subgroup.isComplement'_of_disjoint_and_mul_eq_univ hdisj
      (by rw [← Subgroup.normal_mul, hsup, Subgroup.coe_top])
    by_cases hm0 : m = 0
    · left
      have hN : N = ⊥ := by
        rw [← Subgroup.card_eq_one, hNcard, hm0, pow_zero]
      have hC : C = ⊤ := by rwa [hN, bot_sup_eq] at hsup
      have : IsCyclic (⊤ : Subgroup K₀) := hC ▸ hCcyc
      exact Subgroup.topEquiv.isCyclic.mp this
    · right
      refine ⟨N.map K₀.subtype, Subgroup.map_subtype_le N, ?_, ?_, ?_⟩
      · rw [Ne, Subgroup.map_eq_bot_iff_of_injective _ K₀.subtype_injective, ← Ne,
          ← Subgroup.one_lt_card_iff_ne_bot, hNcard]
        exact Nat.one_lt_pow hm0 hp.one_lt
      · apply IsPGroup.of_card (n := m)
        rw [Subgroup.card_map_of_injective K₀.subtype_injective, hNcard]
      · intro x hx k hk
        refine ⟨⟨x, hx⟩, ?_, rfl⟩
        apply (QuotientGroup.eq_one_iff (N := N) _).mp
        rw [← orderOf_eq_one_iff]
        have h1 : orderOf (⟨x, hx⟩ : K₀) = p ^ k := by rw [Subgroup.orderOf_mk, hk]
        have h2 : orderOf ((⟨x, hx⟩ : K₀) : K₀ ⧸ N) ∣ p ^ k := by
          rw [← h1]
          exact orderOf_map_dvd (QuotientGroup.mk' N) _
        have h3 : orderOf ((⟨x, hx⟩ : K₀) : K₀ ⧸ N) ∣ t := by
          rw [← hCcard, ← hNC.symm.index_eq_card]
          exact orderOf_dvd_natCard _
        have hcop : Nat.Coprime (p ^ k) t := by
          apply Nat.Coprime.pow_left
          rw [Nat.Prime.coprime_iff_not_dvd hp]
          intro hpt
          have hpm : p ∣ p ^ m := dvd_pow_self p hm0
          have h' := Nat.dvd_sub hpm (hpt.trans ht)
          rw [Nat.sub_sub_self (Nat.one_le_pow _ _ hp.pos)] at h'
          exact hp.one_lt.ne' (Nat.dvd_one.mp h')
        exact Nat.eq_one_of_dvd_coprimes hcop h2 h3
  · refine (heven (Nat.card (PSL2 (GaloisField p m)) / 2) ?_).elim
    rw [Nat.card_congr e.toEquiv]
    exact (Nat.mul_div_cancel' (two_dvd_card_psl2_of_isOddPrimePower (hGF m hm))).symm
  · refine (heven (Nat.card (PGL2 (GaloisField p m)) / 2) ?_).elim
    rw [Nat.card_congr e.toEquiv]
    refine (Nat.mul_div_cancel' ?_).symm
    have hinj := Matrix.ProjectiveSpecialLinearGroup.toPGL_injective (n := Fin 2)
      (R := GaloisField p m)
    exact (two_dvd_card_psl2_of_isOddPrimePower (hGF m (by omega))).trans
      (Subgroup.card_dvd_of_injective _ hinj)

theorem pgl2_isCyclic_of_odd_of_kleinFour_le_normalizer
    (hF : IsOddPrimePower (Nat.card F))
    {K₁ : Subgroup (PGL2 F)}
    (hK₁J : K₁ ≤ (Matrix.ProjectiveSpecialLinearGroup.toPGL (n := Fin 2) (R := F)).range)
    (hK₁ : Odd (Nat.card K₁)) {T₁ : Subgroup (PGL2 F)} (hT₁ : IsKleinFour T₁)
    (hT₁K : T₁ ≤ Subgroup.normalizer (K₁ : Set (PGL2 F))) : IsCyclic K₁ := by
  classical
  set toPGL := Matrix.ProjectiveSpecialLinearGroup.toPGL (n := Fin 2) (R := F)
  have hinj : Function.Injective toPGL := Matrix.ProjectiveSpecialLinearGroup.toPGL_injective
  have hF' := hF
  obtain ⟨p, f, hp, hpodd, hf, hcard⟩ := hF'
  have : Fact p.Prime := ⟨hp⟩
  have hp2 : p ≠ 2 := fun h => by
    rw [h] at hpodd
    exact absurd hpodd (by decide)
  set K₀ := K₁.comap toPGL
  have hK₀K₁ : K₀.map toPGL = K₁ := Subgroup.map_comap_eq_self hK₁J
  let e : K₀ ≃* K₁ := (K₀.equivMapOfInjective toPGL hinj).trans (MulEquiv.subgroupCongr hK₀K₁)
  have hK₀ : Odd (Nat.card K₀) := by rwa [Nat.card_congr e.toEquiv]
  suffices IsCyclic K₀ from e.isCyclic.mp this
  by_cases h3 : Nat.card F = 3
  ·
    have h12 : Nat.card (PSL2 F) = 12 := by
      rw [CFSG.GorensteinWalter.psl2_card_formula F hF, h3]
      norm_num
    have hdvd : Nat.card K₀ ∣ 3 * 4 := by
      rw [show 3 * 4 = 12 by norm_num, ← h12]
      exact Subgroup.card_subgroup_dvd_card K₀
    have hcop : Nat.Coprime (Nat.card K₀) 4 := by
      rw [show (4 : ℕ) = 2 ^ 2 by norm_num]
      exact (Nat.coprime_two_right.mpr hK₀).pow_right 2
    rcases (Nat.dvd_prime Nat.prime_three).mp (hcop.dvd_of_dvd_mul_right hdvd) with h | h
    · have : Subsingleton K₀ := (Nat.card_eq_one_iff_unique.mp h).1
      exact isCyclic_of_subsingleton
    · have : Fact (Nat.Prime (Nat.card K₀)) := ⟨h ▸ Nat.prime_three⟩
      exact isCyclic_of_prime_card rfl
  have h3' : 3 < Nat.card F := by
    have : Odd (Nat.card F) := by rw [hcard]; exact hpodd.pow
    have h1 : 1 < Nat.card F := Finite.one_lt_card
    obtain ⟨j, hj⟩ := this
    omega
  rcases psl2_odd_isCyclic_or_exists_pSubgroup hcard hp2 K₀ hK₀ with hcyc | ⟨N, hNK, hN1, hNp,
    hNall⟩
  · exact hcyc
  exfalso
  set N₁ := N.map toPGL
  have hN₁p : IsPGroup p N₁ := hNp.map toPGL
  have hpow : ∀ x : PSL2 F, x ∈ N → ∃ k : ℕ, orderOf x = p ^ k := fun x hx => by
    obtain ⟨k, hk⟩ := hNp ⟨x, hx⟩
    obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow hp).mp (orderOf_dvd_of_pow_eq_one hk)
    exact ⟨j, by rw [← Subgroup.orderOf_mk x hx, hj]⟩
  have hTN : T₁ ≤ Subgroup.normalizer (N₁ : Set (PGL2 F)) := by
    intro t ht
    apply Subgroup.mem_normalizer_fintype
    rintro _ ⟨n, hn, rfl⟩
    have h1 : t * toPGL n * t⁻¹ ∈ K₁ :=
      (Subgroup.mem_normalizer_iff.mp (hT₁K ht) _).mp (hK₀K₁ ▸ ⟨n, hNK hn, rfl⟩)
    rw [← hK₀K₁] at h1
    obtain ⟨m, hm, hmeq⟩ := h1
    obtain ⟨k, hk⟩ := hpow n hn
    have hmk : orderOf m = p ^ k := by
      rw [← orderOf_injective toPGL hinj m, hmeq, ← MulAut.conj_apply, MulEquiv.orderOf_eq,
        orderOf_injective toPGL hinj n, hk]
    exact ⟨m, hNall m hm k hmk, hmeq⟩
  have hN₁odd : ¬ 2 ∣ Nat.card N₁ := by
    obtain ⟨k, hk⟩ := hN₁p.exists_card_eq
    rw [hk]
    exact fun h => hp2 ((Nat.prime_dvd_prime_iff_eq Nat.prime_two hp).mp
      (Nat.prime_two.dvd_of_dvd_pow h)).symm
  have hT₁pow : ∀ v : T₁, v ^ 2 = 1 := fun v => by
    have h := Monoid.pow_exponent_eq_one v
    rwa [hT₁.exponent_two] at h
  have hgen := CFSG.RankThreeEvenClassification.Helpers.coprime_centralizer_generation_of_plane 2
    Nat.prime_two T₁ N₁ hT₁pow hT₁.card_four hN₁odd hTN
  have hN₁ne : N₁ ≠ ⊥ := by
    rwa [Ne, Subgroup.map_eq_bot_iff_of_injective _ hinj]
  obtain ⟨v, hv1, hne⟩ : ∃ v : T₁, v ≠ 1 ∧
      N₁ ⊓ Subgroup.centralizer ({(v : PGL2 F)} : Set (PGL2 F)) ≠ ⊥ := by
    by_contra h
    push Not at h
    apply hN₁ne
    rw [hgen]
    exact iSup₂_eq_bot.mpr h
  obtain ⟨x, ⟨⟨n, hn, rfl⟩, hxC⟩, hx1⟩ := (Subgroup.bot_or_exists_ne_one _).resolve_left hne
  obtain ⟨k, hk⟩ := hpow n hn
  have hv2 : orderOf (v : PGL2 F) = 2 := by
    rw [Subgroup.orderOf_coe]
    exact orderOf_eq_prime (hT₁pow v) hv1
  have hc := Subgroup.mem_centralizer_singleton_iff.mp hxC
  have hn1 := pgl2_eq_one_of_commute_of_orderOf_eq_prime_pow hF h3' hcard hp2 hv2
    (by rw [orderOf_injective toPGL hinj n]; exact hk) ⟨n, rfl⟩ hc.symm
  exact hx1 hn1

end OddSubgroups

section PGLStar

variable {F : Type} [Field F] [Finite F]

theorem mem_pGammaL2PSLRange_of_mem_pGLStar (hF : IsOddPrimePower (Nat.card F))
    {x : PGammaL2 F} (hx : x ∈ pGammaL2PGLStar F) (h2 : orderOf x = 2) :
    x ∈ pGammaL2PSLRange F := by
  obtain ⟨-, hxL⟩ := hx
  by_cases hσ : x.right = 1
  · obtain ⟨y, hy⟩ := hxL.mpr hσ
    rw [mem_pGammaL2PSLRange_iff]
    refine ⟨y, SemidirectProduct.ext ?_ ?_⟩
    · rw [SemidirectProduct.left_inl, hy]
    · rw [SemidirectProduct.right_inl, hσ]
  · exfalso
    obtain ⟨C, hC⟩ := CFSG.GorensteinWalter.projective_semilinear_involution_conj_inr hF x h2 hσ
    have hx' : x = SemidirectProduct.inl C * SemidirectProduct.inr x.right *
        (SemidirectProduct.inl C)⁻¹ := by
      rw [← hC]
      group
    have hΦ : pGammaL2DetClass F hF x = 1 := by
      rw [hx', map_mul, map_mul, map_inv, mul_comm (pGammaL2DetClass F hF _),
        mul_inv_cancel_right, pGammaL2DetClass_apply, SemidirectProduct.left_inr, map_one]
    exact hσ (hxL.mp ((left_mem_range_toPGL_iff hF x).mpr hΦ))

end PGLStar

end CFSG.ABGDGroups
