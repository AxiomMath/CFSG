module

public import CFSG.LocalAnalysis.GH72.A7Local

public section

namespace CFSG.GH72

open Subgroup
open scoped MatrixGroups
open CFSG.ABGLocalTools (IsSylowOf)
open CFSG.GorensteinWalter (PSL2 PGL2 IsOddPrimePower HasDihedralSylowTwo)

section OddCore

variable {X : Type*} [Group X] [Finite X]

theorem le_oddCore_of_normal_of_odd {M : Type*} [Group M] {N : Subgroup M} (hN : N.Normal)
    (hodd : Odd (Nat.card N)) : N ≤ CFSG.oddCore M :=
  le_sSup ⟨hN, hodd⟩

theorem commutator_eq_bot_of_odd_card {L E : Subgroup X} (hO : CFSG.oddCore L = ⊥)
    (hEL : E ≤ normalizer (L : Set X)) (hodd : Odd (Nat.card (⁅E, L⁆ : Subgroup X))) :
    ⁅E, L⁆ = ⊥ := by
  have hle : ⁅E, L⁆ ≤ L := le_normalizer_iff_commutator_le_right.mp hEL
  have hN : L ≤ normalizer ((⁅E, L⁆ : Subgroup X) : Set X) := by
    rw [Subgroup.commutator_comm E L]
    exact Subgroup.normalizer_commutator_ge_left L E
  have hnormal : ((⁅E, L⁆ : Subgroup X).subgroupOf L).Normal := normal_subgroupOf_of_le_normalizer hN
  have hcard : Odd (Nat.card ((⁅E, L⁆ : Subgroup X).subgroupOf L)) := by
    rwa [Nat.card_congr (subgroupOfEquivOfLe hle).toEquiv]
  have h := le_oddCore_of_normal_of_odd hnormal hcard
  rw [hO, le_bot_iff, subgroupOf_eq_bot] at h
  exact (inf_eq_left.mpr hle).symm.trans (disjoint_iff.mp h)

theorem le_centralizer_of_odd_of_le_normalizer {L E : Subgroup X} (hO : CFSG.oddCore L = ⊥)
    (hEL : E ≤ normalizer (L : Set X)) (hLE : L ≤ normalizer (E : Set X))
    (hE : Odd (Nat.card E)) : E ≤ centralizer (L : Set X) := by
  have hle : ⁅E, L⁆ ≤ E := by
    rw [Subgroup.commutator_comm E L]
    exact le_normalizer_iff_commutator_le_right.mp hLE
  have hodd : Odd (Nat.card (⁅E, L⁆ : Subgroup X)) := hE.of_dvd_nat (Subgroup.card_dvd_of_le hle)
  exact Subgroup.commutator_eq_bot_iff_le_centralizer.mp (commutator_eq_bot_of_odd_card hO hEL hodd)

theorem sup_inf_centralizer_eq_bot {J U : Subgroup X} (hJn : J.Normal) (hJUn : (J ⊔ U).Normal)
    (hZ : center J = ⊥) (hUJ : U ≤ normalizer (J : Set X)) (hU : Odd (Nat.card U))
    (hO : CFSG.oddCore X = ⊥) : (J ⊔ U) ⊓ centralizer (J : Set X) = ⊥ := by
  haveI := hJn
  haveI := hJUn
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hNodd : Odd (Nat.card ↥((J ⊔ U) ⊓ centralizer (J : Set X))) := by
    by_contra heven
    rw [Nat.not_odd_iff_even, even_iff_two_dvd] at heven
    obtain ⟨⟨x, hxN⟩, hx2⟩ := exists_prime_orderOf_dvd_card' 2 heven
    rw [Subgroup.orderOf_mk] at hx2
    have hxJ : x ∈ J := by
      have hmk : QuotientGroup.mk' J x ∈ U.map (QuotientGroup.mk' J) := by
        have h := mem_map_of_mem (QuotientGroup.mk' J) hxN.1
        rwa [Subgroup.map_sup, QuotientGroup.map_mk'_self, bot_sup_eq] at h
      have hodd' : Odd (Nat.card (U.map (QuotientGroup.mk' J))) :=
        hU.of_dvd_nat (Subgroup.card_map_dvd _ _)
      have h1 : orderOf (QuotientGroup.mk' J x) ∣ 2 := hx2 ▸ orderOf_map_dvd _ x
      have h2 := Subgroup.orderOf_dvd_natCard _ hmk
      have h3 := Nat.eq_one_of_dvd_coprimes (Nat.coprime_two_left.mpr hodd') h1 h2
      rwa [orderOf_eq_one_iff, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h3
    have hxZ : (⟨x, hxJ⟩ : J) ∈ center J :=
      mem_center_iff.mpr fun j => Subtype.ext (mem_centralizer_iff.mp hxN.2 j j.2)
    rw [hZ, mem_bot] at hxZ
    have hx1 : x = 1 := congrArg Subtype.val hxZ
    rw [hx1, orderOf_one] at hx2
    norm_num at hx2
  exact le_bot_iff.mp ((le_oddCore_of_normal_of_odd inferInstance hNodd).trans hO.le)

theorem oddCore_eq_bot_of_mulEquiv {L M : Type*} [Group L] [Group M] [Finite L] (e : L ≃* M)
    (h : ∀ N : Subgroup M, N.Normal → Odd (Nat.card N) → N = ⊥) : CFSG.oddCore L = ⊥ := by
  have hO : Odd (Nat.card (CFSG.oddCore L)) := CFSG.ABGDGroups.odd_card_oddCore L
  have hmap := h ((CFSG.oddCore L).map e.toMonoidHom)
    ((CFSG.oddCore_normal L).map e.toMonoidHom e.surjective)
    (by rwa [card_map_of_injective e.injective])
  exact (map_eq_bot_iff_of_injective _ e.injective).mp hmap

theorem pgl2_eq_bot_of_normal_of_odd {F : Type} [Field F] [Finite F]
    (hF : IsOddPrimePower (Nat.card F)) (N : Subgroup (PGL2 F)) (hN : N.Normal)
    (hodd : Odd (Nat.card N)) : N = ⊥ := by
  set g := Matrix.ProjectiveSpecialLinearGroup.toPGL (n := Fin 2) (R := F)
  have hg : Function.Injective g := Matrix.ProjectiveSpecialLinearGroup.toPGL_injective
  have hNJ : N ≤ g.range := le_of_index_eq_two_of_odd (pgl2_index_range_toPGL hF) hodd
  haveI : (N.comap g).Normal := hN.comap g
  have h := CFSG.ABGDGroups.eq_bot_of_normal_of_odd_card_psl2 hF (N.comap g)
    (by rwa [card_comap_of_le_range g hg hNJ])
  rw [← map_comap_eq_self hNJ, h, Subgroup.map_bot]

theorem isOddPrimePower_card_galoisField {p k : ℕ} [hp : Fact p.Prime] (hp2 : p ≠ 2)
    (hq : 3 ≤ p ^ k) : IsOddPrimePower (Nat.card (GaloisField p k)) := by
  have hk : k ≠ 0 := by
    rintro rfl
    rw [pow_zero] at hq
    omega
  exact ⟨p, k, hp.out, hp.out.odd_of_ne_two hp2, Nat.one_le_iff_ne_zero.mpr hk,
    GaloisField.card p k hk⟩

theorem oddCore_eq_bot_of_isL2PGL2OrA7OrV4 {L : Type*} [Group L] [Finite L]
    (hL : IsL2PGL2OrA7OrV4 L) : CFSG.oddCore L = ⊥ := by
  rcases hL with (⟨⟨e⟩⟩ | ⟨p, k, hp, hp2, hq, ⟨e⟩⟩) | ⟨p, k, hp, hp2, hq, ⟨e⟩⟩ | hV
  · refine oddCore_eq_bot_of_mulEquiv e fun N hN hodd => ?_
    haveI : IsSimpleGroup (alternatingGroup (Fin 7)) := alternatingGroup.isSimpleGroup (by simp)
    haveI := hN
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal N with h | h
    · exact h
    · rw [h, card_top, CFSG.ABGDGroups.card_alternatingGroup_fin_seven] at hodd
      exact absurd hodd (by decide)
  · refine oddCore_eq_bot_of_mulEquiv e fun N hN hodd => ?_
    haveI := hN
    exact CFSG.ABGDGroups.eq_bot_of_normal_of_odd_card_psl2
      (isOddPrimePower_card_galoisField hp2 (by omega)) N hodd
  · exact oddCore_eq_bot_of_mulEquiv e fun N hN hodd =>
      pgl2_eq_bot_of_normal_of_odd (isOddPrimePower_card_galoisField hp2 hq) N hN hodd
  · have hO : Odd (Nat.card (CFSG.oddCore L)) := CFSG.ABGDGroups.odd_card_oddCore L
    have hdvd : Nat.card (CFSG.oddCore L) ∣ 2 ^ 2 := by
      rw [show (2 : ℕ) ^ 2 = 4 by norm_num, ← hV.card_four]
      exact Subgroup.card_subgroup_dvd_card _
    have h1 : Nat.card (CFSG.oddCore L) = 1 :=
      Nat.eq_one_of_dvd_coprimes ((Nat.coprime_two_right.mpr hO).pow_right 2).symm hdvd
        (dvd_refl _)
    exact Subgroup.card_eq_one.mp h1

end OddCore

section FourGroup

variable {X : Type*} [Group X] [Finite X]

theorem range_subtype_comp_symm {M : Type*} [Group M] {L : Subgroup X} (e : L ≃* M) :
    (L.subtype.comp e.symm.toMonoidHom).range = L := by
  ext x
  constructor
  · rintro ⟨y, rfl⟩
    exact (e.symm y).2
  · intro hx
    exact ⟨e ⟨x, hx⟩, by simp⟩

theorem mul_comm_of_isCyclic {R : Subgroup X} (hR : IsCyclic R) {x y : X} (hx : x ∈ R)
    (hy : y ∈ R) : x * y = y * x := by
  letI := IsCyclic.commGroup (α := R)
  exact congrArg Subtype.val (mul_comm (⟨x, hx⟩ : R) ⟨y, hy⟩)

theorem eq_bot_of_le_of_isKleinFour {L K : Subgroup X} (hL : IsKleinFour L) (hKL : K ≤ L)
    (hK : Odd (Nat.card K)) : K = ⊥ := by
  have hdvd : Nat.card K ∣ 2 ^ 2 := by
    rw [show (2 : ℕ) ^ 2 = 4 by norm_num, ← hL.card_four]
    exact Subgroup.card_dvd_of_le hKL
  exact Subgroup.card_eq_one.mp
    (Nat.eq_one_of_dvd_coprimes ((Nat.coprime_two_right.mpr hK).pow_right 2).symm hdvd (dvd_refl _))

theorem isCyclic_and_exists_le_centralizer_of_odd
    {L V K : Subgroup X} (hL : IsL2PGL2OrA7OrV4 L)
    (hV : IsKleinFour V) (hVL : V ≤ L) (hKL : K ≤ L) (hK : Odd (Nat.card K))
    (hVK : V ≤ normalizer (K : Set X)) :
    IsCyclic K ∧ ∃ a ∈ V, a ≠ 1 ∧ K ≤ centralizer ({a} : Set X) := by
  rcases hL with (⟨⟨e⟩⟩ | ⟨p, k, hp, hp2, hq, ⟨e⟩⟩) | ⟨p, k, hp, hp2, hq, ⟨e⟩⟩ | hL4
  · exact isCyclic_and_exists_le_centralizer_of_aSeven e hV hVL hKL hK hVK
  ·
    have hF := isOddPrimePower_card_galoisField hp2 (by omega : 3 ≤ p ^ k)
    set f : PSL2 (GaloisField p k) →* X := L.subtype.comp e.symm.toMonoidHom with hfdef
    have hf : Function.Injective f := L.subtype_injective.comp e.symm.injective
    have hfr : f.range = L := range_subtype_comp_symm e
    set g := Matrix.ProjectiveSpecialLinearGroup.toPGL (n := Fin 2) (R := GaloisField p k)
    have hg : Function.Injective g := Matrix.ProjectiveSpecialLinearGroup.toPGL_injective
    have hKr : K ≤ f.range := hfr ▸ hKL
    have hVr : V ≤ f.range := hfr ▸ hVL
    have hK₁J : (K.comap f).map g ≤ g.range := map_le_range _ _
    have hK₁ : Odd (Nat.card ((K.comap f).map g)) := by
      rwa [card_map_of_injective hg, card_comap_of_le_range f hf hKr]
    have hT₁ : IsKleinFour ((V.comap f).map g) :=
      CFSG.ABGDGroups.isKleinFour_map_of_injective hg (isKleinFour_comap f hf hV hVr)
    have hT₁K : (V.comap f).map g ≤ normalizer (((K.comap f).map g : Subgroup _) : Set _) :=
      (map_mono (comap_le_normalizer_comap f hVK)).trans (le_normalizer_map g)
    have hcyc₁ :=
      CFSG.ABGDGroups.pgl2_isCyclic_of_odd_of_kleinFour_le_normalizer hF hK₁J hK₁ hT₁ hT₁K
    refine ⟨isCyclic_of_isCyclic_comap f hf hKr
      (((K.comap f).equivMapOfInjective g hg).isCyclic.mpr hcyc₁), ?_⟩
    obtain ⟨_, ⟨y, hy, rfl⟩, hx1, hKx⟩ :=
      CFSG.ABGDGroups.pgl2_exists_le_centralizer_of_odd hF hK₁J hK₁ hT₁ hT₁K
    refine ⟨f y, hy, fun h => hx1 (by rw [show y = 1 from hf (h.trans (map_one f).symm),
      map_one]), ?_⟩
    intro z hz
    obtain ⟨z', rfl⟩ := hKr hz
    have h := mem_centralizer_singleton_iff.mp (hKx ⟨z', hz, rfl⟩)
    rw [mem_centralizer_singleton_iff, ← map_mul, ← map_mul]
    exact congrArg f (hg (by rw [map_mul, map_mul, h]))
  ·
    have hF := isOddPrimePower_card_galoisField hp2 hq
    set f : PGL2 (GaloisField p k) →* X := L.subtype.comp e.symm.toMonoidHom with hfdef
    have hf : Function.Injective f := L.subtype_injective.comp e.symm.injective
    have hfr : f.range = L := range_subtype_comp_symm e
    have hKr : K ≤ f.range := hfr ▸ hKL
    have hVr : V ≤ f.range := hfr ▸ hVL
    have hK' : Odd (Nat.card (K.comap f)) := by rwa [card_comap_of_le_range f hf hKr]
    have hK'J := le_of_index_eq_two_of_odd (pgl2_index_range_toPGL hF) hK'
    have hV' := isKleinFour_comap f hf hV hVr
    have hV'K' := comap_le_normalizer_comap f hVK
    refine ⟨isCyclic_of_isCyclic_comap f hf hKr
      (CFSG.ABGDGroups.pgl2_isCyclic_of_odd_of_kleinFour_le_normalizer hF hK'J hK' hV' hV'K'), ?_⟩
    obtain ⟨y, hy, hy1, hKy⟩ := CFSG.ABGDGroups.pgl2_exists_le_centralizer_of_odd hF hK'J hK' hV' hV'K'
    refine ⟨f y, hy, fun h => hy1 (hf (h.trans (map_one f).symm)), ?_⟩
    intro z hz
    obtain ⟨z', rfl⟩ := hKr hz
    have h := mem_centralizer_singleton_iff.mp (hKy (show z' ∈ K.comap f from hz))
    rw [mem_centralizer_singleton_iff, ← map_mul, ← map_mul, h]
  ·
    have hbot := eq_bot_of_le_of_isKleinFour hL4 hKL hK
    obtain ⟨a, ha, ha1, -⟩ := exists_mem_kleinFour_ne hV (one_mem V)
    subst hbot
    exact ⟨inferInstance, a, ha, ha1, bot_le⟩

theorem isCyclic_of_odd_of_kleinFour_le_normalizer
    {L V : Subgroup X} (hL : IsL2PGL2OrA7OrV4 L)
    (hV : IsKleinFour V) (hVL : V ≤ L) {K : Subgroup X} (hKL : K ≤ L) (hK : Odd (Nat.card K))
    (hVK : V ≤ normalizer (K : Set X)) : IsCyclic K :=
  (isCyclic_and_exists_le_centralizer_of_odd hL hV hVL hKL hK hVK).1

theorem exists_le_centralizer_of_odd_of_kleinFour_le_normalizer
    {L V : Subgroup X} (hL : IsL2PGL2OrA7OrV4 L)
    (hV : IsKleinFour V) (hVL : V ≤ L) {K : Subgroup X} (hKL : K ≤ L) (hK : Odd (Nat.card K))
    (hVK : V ≤ normalizer (K : Set X)) : ∃ a ∈ V, a ≠ 1 ∧ K ≤ centralizer ({a} : Set X) :=
  (isCyclic_and_exists_le_centralizer_of_odd hL hV hVL hKL hK hVK).2

theorem exists_isCyclic_forall_odd_mem_inf_centralizer {L : Subgroup X}
    (hL : IsL2PGL2OrA7OrV4 L) {a : X} (haL : a ∈ L) (ha : orderOf a = 2) :
    ∃ R : Subgroup X, R ≤ L ⊓ centralizer ({a} : Set X) ∧ IsCyclic R ∧
      ∀ x ∈ L ⊓ centralizer ({a} : Set X), Odd (orderOf x) → x ∈ R := by
  rcases hL with (⟨⟨e⟩⟩ | ⟨p, k, hp, hp2, hq, ⟨e⟩⟩) | ⟨p, k, hp, hp2, hq, ⟨e⟩⟩ | hL4
  · obtain ⟨U, hU, hUc, hodd⟩ := exists_card_eq_three_forall_odd_mem_of_aSeven e haL ha
    haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    exact ⟨U, hU, isCyclic_of_prime_card hUc, hodd⟩
  · have hF := isOddPrimePower_card_galoisField hp2 (by omega : 3 ≤ p ^ k)
    have ht : orderOf (e ⟨a, haL⟩) = 2 := by
      rw [MulEquiv.orderOf_eq, Subgroup.orderOf_mk]
      exact ha
    have hft : (L.subtype.comp e.symm.toMonoidHom) (e ⟨a, haL⟩) = a := by simp
    obtain ⟨R, hR, hRc, hodd⟩ := psl2_exists_isCyclic_forall_odd_mem hF ht
    obtain ⟨h1, h2, h3⟩ := exists_isCyclic_forall_odd_mem_map (L.subtype.comp e.symm.toMonoidHom)
      (L.subtype_injective.comp e.symm.injective) hR hRc hodd
    rw [range_subtype_comp_symm e, hft] at h1 h3
    exact ⟨_, h1, h2, h3⟩
  · have hF := isOddPrimePower_card_galoisField hp2 hq
    have ht : orderOf (e ⟨a, haL⟩) = 2 := by
      rw [MulEquiv.orderOf_eq, Subgroup.orderOf_mk]
      exact ha
    have hft : (L.subtype.comp e.symm.toMonoidHom) (e ⟨a, haL⟩) = a := by simp
    obtain ⟨R, hR, hRc, hodd⟩ := pgl2_exists_isCyclic_forall_odd_mem hF ht
    obtain ⟨h1, h2, h3⟩ := exists_isCyclic_forall_odd_mem_map (L.subtype.comp e.symm.toMonoidHom)
      (L.subtype_injective.comp e.symm.injective) hR hRc hodd
    rw [range_subtype_comp_symm e, hft] at h1 h3
    exact ⟨_, h1, h2, h3⟩
  · refine ⟨⊥, bot_le, inferInstance, fun x hx hodd => ?_⟩
    have hz : zpowers x = ⊥ := eq_bot_of_le_of_isKleinFour hL4 (zpowers_le.mpr hx.1)
      (by rwa [Nat.card_zpowers])
    rw [← hz]
    exact mem_zpowers x

theorem exists_isSylowOf_inf_centralizer_forall_le {L : Subgroup X} (hL : IsL2PGL2OrA7OrV4 L)
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {a : X} (haL : a ∈ L) (ha : orderOf a = 2) :
    ∃ P : Subgroup X, IsSylowOf p P (L ⊓ centralizer ({a} : Set X)) ∧
      ∀ R : Subgroup X, R ≤ L ⊓ centralizer ({a} : Set X) → IsPGroup p R → R ≤ P := by
  obtain ⟨R, hR, hRc, hodd⟩ := exists_isCyclic_forall_odd_mem_inf_centralizer hL haL ha
  exact exists_isSylowOf_forall_le_of_odd_mem hR (fun x hx y hy => mul_comm_of_isCyclic hRc hx hy)
    hodd hp hp2

theorem odd_card_of_isPGroup {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {Q : Subgroup X}
    (hQ : IsPGroup p Q) : Odd (Nat.card Q) := by
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨n, hn⟩ := hQ.exists_card_eq
  rw [hn]
  exact (hp.odd_of_ne_two hp2).pow

theorem exists_isSylowOf_of_isMaxInvIn
    {L V : Subgroup X} (hL : IsL2PGL2OrA7OrV4 L) (hV : IsKleinFour V) (hVL : V ≤ L) {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) {Q : Subgroup X} (hQ : IsMaxInvIn p V L Q) :
    ∃ a ∈ V, a ≠ 1 ∧ IsSylowOf p Q (L ⊓ centralizer ({a} : Set X)) ∧
      ∀ R : Subgroup X, R ≤ L ⊓ centralizer ({a} : Set X) → IsPGroup p R → R ≤ Q := by
  obtain ⟨hQL, hQp, hVQ, hmax⟩ := hQ
  obtain ⟨a, ha, ha1, hQa⟩ := exists_le_centralizer_of_odd_of_kleinFour_le_normalizer hL hV hVL
    hQL (odd_card_of_isPGroup hp hp2 hQp) hVQ
  have ha2 : orderOf a = 2 := orderOf_eq_prime (sq_eq_one_of_mem_kleinFour hV ha) ha1
  obtain ⟨P, hP, hPall⟩ := exists_isSylowOf_inf_centralizer_forall_le hL hp hp2 (hVL ha) ha2
  have hQP : Q ≤ P := hPall Q (le_inf hQL hQa) hQp
  have hVP : V ≤ normalizer (P : Set X) := fun v hv => by
    apply mem_normalizer_fintype
    intro y hy
    have hle : P.map (MulAut.conj v).toMonoidHom ≤ L ⊓ centralizer ({a} : Set X) := by
      rintro _ ⟨z, hz, rfl⟩
      have hz' := hP.le hz
      have hva : Commute v a := mul_comm_of_mem_kleinFour hV hv ha
      have hza : Commute z a := mem_centralizer_singleton_iff.mp hz'.2
      refine ⟨L.mul_mem (L.mul_mem (hVL hv) hz'.1) (L.inv_mem (hVL hv)), ?_⟩
      exact mem_centralizer_singleton_iff.mpr ((hva.mul_left hza).mul_left hva.inv_left).eq
    exact hPall _ hle (hP.isPGroup.map _) ⟨y, hy, rfl⟩
  have hPQ : P = Q := hmax P (hP.le.trans inf_le_left) hP.isPGroup hVP hQP
  subst hPQ
  exact ⟨a, ha, ha1, hP, hPall⟩

theorem normalizer_inf_centralizer_le_normalizer_of_isMaxInvIn
    {L V : Subgroup X} (hL : IsL2PGL2OrA7OrV4 L)
    (hV : IsKleinFour V) (hVL : V ≤ L) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {Q : Subgroup X}
    (hQ : IsMaxInvIn p V L Q) :
    normalizer (L : Set X) ⊓ centralizer (V : Set X) ≤ normalizer (Q : Set X) := by
  obtain ⟨a, ha, -, hQsyl, hQall⟩ := exists_isSylowOf_of_isMaxInvIn hL hV hVL hp hp2 hQ
  rintro g ⟨hgL, hgV⟩
  apply mem_normalizer_fintype
  intro y hy
  have hle : Q.map (MulAut.conj g).toMonoidHom ≤ L ⊓ centralizer ({a} : Set X) := by
    rintro _ ⟨z, hz, rfl⟩
    have hz' := hQsyl.le hz
    have hga : Commute g a := (mem_centralizer_iff.mp hgV a ha).symm
    have hza : Commute z a := mem_centralizer_singleton_iff.mp hz'.2
    refine ⟨(mem_normalizer_iff.mp hgL z).mp hz'.1, ?_⟩
    exact mem_centralizer_singleton_iff.mpr ((hga.mul_left hza).mul_left hga.inv_left).eq
  exact hQall _ hle (hQsyl.isPGroup.map _) ⟨y, hy, rfl⟩

theorem hasDihedralSylowTwo_of_isL2OrA7 {L : Type*} [Group L] [Finite L] {qmin : ℕ}
    (hq : 3 ≤ qmin) (hL : IsL2OrA7 L qmin) : HasDihedralSylowTwo L := by
  rcases hL with ⟨⟨e⟩⟩ | ⟨p, k, hp, hp2, hpk, ⟨e⟩⟩
  · exact CFSG.GorensteinWalter.hasDihedralSylowTwo_of_mulEquiv e
      CFSG.GorensteinWalter.hasDihedralSylowTwo_alternatingGroupSeven
  · exact CFSG.GorensteinWalter.hasDihedralSylowTwo_of_mulEquiv e
      (CFSG.GorensteinWalter.psl2_odd_hasDihedralSylowTwo_model _
        (isOddPrimePower_card_galoisField hp2 (by omega)))

theorem exists_mem_normalizer_sq_not_mem_centralizer_of_isL2OrA7 {L V : Subgroup X}
    (hL : IsL2OrA7 L 5) (hV : IsKleinFour V) (hVL : V ≤ L) :
    ∃ g ∈ L ⊓ normalizer (V : Set X), g ^ 2 ∉ centralizer (V : Set X) := by
  haveI : IsSimpleGroup L := isSimpleGroup_of_isL2OrA7 le_rfl hL
  have h4 : 4 < Nat.card L := by
    have := sixty_le_card_of_isL2OrA7 le_rfl hL
    omega
  have hZ : IsKleinFour (V.subgroupOf L) :=
    ⟨by rw [Nat.card_congr (subgroupOfEquivOfLe hVL).toEquiv]; exact hV.card_four,
      by rw [Monoid.exponent_eq_of_mulEquiv (subgroupOfEquivOfLe hVL)]; exact hV.exponent_two⟩
  obtain ⟨g, hg, hg2⟩ := exists_mem_normalizer_sq_not_mem_centralizer h4
    (hasDihedralSylowTwo_of_isL2OrA7 (by norm_num) hL) hZ
  refine ⟨g, ⟨g.2, ?_⟩, ?_⟩
  · apply mem_normalizer_fintype
    intro v hv
    have hv' : (⟨v, hVL hv⟩ : L) ∈ V.subgroupOf L := hv
    exact (mem_normalizer_iff.mp hg _).mp hv'
  · intro h
    apply hg2
    rw [mem_centralizer_iff] at h ⊢
    intro z hz
    exact Subtype.ext (h z hz)

theorem exists_conj_eq_of_mem_kleinFour {L V : Subgroup X} (hL : IsL2OrA7 L 5)
    (hV : IsKleinFour V) (hVL : V ≤ L) {a b : X} (ha : a ∈ V) (ha1 : a ≠ 1) (hb : b ∈ V)
    (hb1 : b ≠ 1) : ∃ g ∈ L ⊓ normalizer (V : Set X), g * a * g⁻¹ = b := by
  obtain ⟨g, ⟨hgL, hgN⟩, hg2⟩ := exists_mem_normalizer_sq_not_mem_centralizer_of_isL2OrA7 hL hV hVL
  obtain ⟨k, hk⟩ := exists_pow_conj_eq_of_sq_not_mem_centralizer hV hgN hg2 ha ha1 hb hb1
  exact ⟨g ^ k, ⟨L.pow_mem hgL k, Subgroup.pow_mem _ hgN k⟩, hk⟩

theorem exists_three_element_mem_normalizer_kleinFour {L V : Subgroup X} (hL : IsL2OrA7 L 5)
    (hV : IsKleinFour V) (hVL : V ≤ L) :
    ∃ u ∈ L ⊓ normalizer (V : Set X), (∃ n : ℕ, orderOf u = 3 ^ n) ∧
      ∀ a ∈ V, a ≠ 1 → u * a * u⁻¹ ≠ a := by
  obtain ⟨g, ⟨hgL, hgN⟩, hg2⟩ := exists_mem_normalizer_sq_not_mem_centralizer_of_isL2OrA7 hL hV hVL
  obtain ⟨m, hm3, hfix⟩ := exists_pow_three_element_of_sq_not_mem_centralizer hV hgN hg2
  exact ⟨g ^ m, ⟨L.pow_mem hgL m, Subgroup.pow_mem _ hgN m⟩, hm3, hfix⟩

theorem exists_conj_eq_of_isPGroup_ne_bot
    {L V : Subgroup X} (hL : IsL2PGL2OrA7OrV4 L) (hV : IsKleinFour V) (hVL : V ≤ L) {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) {a b : X} (ha : a ∈ V) (ha1 : a ≠ 1) (hb : b ∈ V) (hb1 : b ≠ 1)
    (hab : a ≠ b) {Pa Pb : Subgroup X} (hPa : Pa ≤ L ⊓ centralizer ({a} : Set X))
    (hPap : IsPGroup p Pa) (hPa1 : Pa ≠ ⊥) (hPb : Pb ≤ L ⊓ centralizer ({b} : Set X))
    (hPbp : IsPGroup p Pb) (hPb1 : Pb ≠ ⊥) :
    ∃ g ∈ L ⊓ normalizer (V : Set X), g * a * g⁻¹ = b := by
  haveI : Fact p.Prime := ⟨hp⟩
  rcases hL with (hL7 | hLpsl) | ⟨r, k, hr, hr2, hq, ⟨e⟩⟩ | hL4
  · exact exists_conj_eq_of_mem_kleinFour (Or.inl hL7) hV hVL ha ha1 hb hb1
  · exact exists_conj_eq_of_mem_kleinFour (Or.inr hLpsl) hV hVL ha ha1 hb hb1
  · have hF := isOddPrimePower_card_galoisField hr2 hq
    set f : PGL2 (GaloisField r k) →* X := L.subtype.comp e.symm.toMonoidHom with hfdef
    have hf : Function.Injective f := L.subtype_injective.comp e.symm.injective
    have hfr : f.range = L := range_subtype_comp_symm e
    set g₀ := Matrix.ProjectiveSpecialLinearGroup.toPGL (n := Fin 2) (R := GaloisField r k)
    have hg₀ : Function.Injective g₀ := Matrix.ProjectiveSpecialLinearGroup.toPGL_injective
    set J := g₀.range with hJdef
    have hJ : J.index = 2 := pgl2_index_range_toPGL hF
    have hVr : V ≤ f.range := hfr ▸ hVL
    have hV' : IsKleinFour (V.comap f) := isKleinFour_comap f hf hV hVr
    obtain ⟨a', ha'f⟩ := hVr ha
    obtain ⟨b', hb'f⟩ := hVr hb
    have ha' : a' ∈ V.comap f := by show f a' ∈ V; rw [ha'f]; exact ha
    have hb' : b' ∈ V.comap f := by show f b' ∈ V; rw [hb'f]; exact hb
    have ha'1 : a' ≠ 1 := fun h => ha1 (by rw [← ha'f, h, map_one])
    have hb'1 : b' ≠ 1 := fun h => hb1 (by rw [← hb'f, h, map_one])
    have hab' : a' ≠ b' := fun h => hab (by rw [← ha'f, ← hb'f, h])
    have ha'2 : orderOf a' = 2 := orderOf_eq_prime (sq_eq_one_of_mem_kleinFour hV' ha') ha'1
    have hb'2 : orderOf b' = 2 := orderOf_eq_prime (sq_eq_one_of_mem_kleinFour hV' hb') hb'1
    have hdvd : ∀ (x' : PGL2 (GaloisField r k)) (P : Subgroup X),
        P ≤ L ⊓ centralizer ({f x'} : Set X) → IsPGroup p P → P ≠ ⊥ →
        p ∣ Nat.card ↥(J ⊓ centralizer ({x'} : Set (PGL2 (GaloisField r k)))) := by
      intro x' P hP hPp hP1
      have hPr : P ≤ f.range := hfr ▸ (hP.trans inf_le_left)
      have hP' : Odd (Nat.card (P.comap f)) := by
        rw [card_comap_of_le_range f hf hPr]
        exact odd_card_of_isPGroup hp hp2 hPp
      have hP'J : P.comap f ≤ J := le_of_index_eq_two_of_odd hJ hP'
      have hP'C : P.comap f ≤ centralizer ({x'} : Set (PGL2 (GaloisField r k))) := fun y hy => by
        have h := mem_centralizer_singleton_iff.mp (hP hy).2
        rw [mem_centralizer_singleton_iff]
        apply hf
        rw [map_mul, map_mul]
        exact h
      have hpP' : p ∣ Nat.card (P.comap f) := by
        rw [card_comap_of_le_range f hf hPr]
        obtain ⟨n, hn⟩ := hPp.exists_card_eq
        have hn0 : n ≠ 0 := by
          rintro rfl
          rw [pow_zero] at hn
          exact hP1 (Subgroup.card_eq_one.mp hn)
        rw [hn]
        exact dvd_pow_self p hn0
      exact hpP'.trans (Subgroup.card_dvd_of_le (le_inf hP'J hP'C))
    have hpa := hdvd a' Pa (ha'f ▸ hPa) hPap hPa1
    have hpb := hdvd b' Pb (hb'f ▸ hPb) hPbp hPb1
    obtain ⟨ε, hε, hε1⟩ := exists_modEq_four_of_odd (odd_of_isOddPrimePower hF)
    have hnot : ¬ ((p : ℤ) ∣ (Nat.card (GaloisField r k) : ℤ) - ε ∧
        (p : ℤ) ∣ (Nat.card (GaloisField r k) : ℤ) + ε) := by
      rintro ⟨h1, h2⟩
      have h3 : (p : ℤ) ∣ 2 := by
        have := dvd_sub h2 h1
        rcases hε1 with rfl | rfl
        · simpa using this
        · have h' : (p : ℤ) ∣ -2 := by convert this using 1; ring
          exact (dvd_neg).mp h'
      have h4 : p ∣ 2 := by exact_mod_cast h3
      exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp h4)
    by_cases haJ : a' ∈ J <;> by_cases hbJ : b' ∈ J
    ·
      have hV'J : V.comap f ≤ J := fun z hz => by
        rcases mem_kleinFour_cases hV' ha' hb' ha'1 hb'1 hab' hz with rfl | rfl | rfl | rfl
        · exact one_mem _
        · exact haJ
        · exact hbJ
        · exact J.mul_mem haJ hbJ
      have hq5 : 5 ≤ r ^ k := by
        by_contra hlt
        have hq3 : Nat.card (GaloisField r k) = 3 := by
          have hodd := odd_of_isOddPrimePower hF
          rw [GaloisField.card r k (by rintro rfl; rw [pow_zero] at hq; omega)] at hodd ⊢
          obtain ⟨j, hj⟩ := hodd
          omega
        have hεm : ε = -1 := by
          rw [hq3] at hε
          rcases hε1 with rfl | rfl
          · exact absurd hε (by decide)
          · rfl
        have hc := pgl2_card_inf_centralizer_of_mem hF hε hε1 ha'2 haJ
        rw [hq3, hεm] at hc
        have h4 : p ∣ 2 ^ 2 := by
          have : Nat.card ↥(J ⊓ centralizer ({a'} : Set (PGL2 (GaloisField r k)))) = 2 ^ 2 := by
            have : ((Nat.card ↥(J ⊓ centralizer ({a'} : Set (PGL2 (GaloisField r k)))) : ℕ) : ℤ) =
              ((2 ^ 2 : ℕ) : ℤ) := by rw [hc]; norm_num
            exact_mod_cast this
          rw [← this]
          exact hpa
        exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp (hp.dvd_of_dvd_pow h4))
      have hL' : IsL2OrA7 (J.map f) 5 := Or.inr ⟨r, k, hr, hr2, hq5,
        ⟨(J.equivMapOfInjective f hf).symm.trans (MonoidHom.ofInjective hg₀).symm⟩⟩
      have hVL' : V ≤ J.map f := fun v hv => by
        obtain ⟨v', rfl⟩ := hVr hv
        exact ⟨v', hV'J hv, rfl⟩
      obtain ⟨g, ⟨hgL', hgN⟩, hgab⟩ := exists_conj_eq_of_mem_kleinFour hL' hV hVL' ha ha1 hb hb1
      have hJL : J.map f ≤ L := hfr ▸ map_le_range f J
      exact ⟨g, ⟨hJL hgL', hgN⟩, hgab⟩
    · exfalso
      exact hnot ⟨by
          rw [← pgl2_card_inf_centralizer_of_mem hF hε hε1 ha'2 haJ]
          exact_mod_cast hpa,
        by
          rw [← pgl2_card_inf_centralizer_of_not_mem hF hε hε1 hb'2 hbJ]
          exact_mod_cast hpb⟩
    · exfalso
      exact hnot ⟨by
          rw [← pgl2_card_inf_centralizer_of_mem hF hε hε1 hb'2 hbJ]
          exact_mod_cast hpb,
        by
          rw [← pgl2_card_inf_centralizer_of_not_mem hF hε hε1 ha'2 haJ]
          exact_mod_cast hpa⟩
    ·
      have hu'J : a' * b' ∈ J := (Subgroup.mul_mem_iff_of_index_two hJ).mpr
        (iff_of_false haJ hbJ)
      have hu' : a' * b' ∈ V.comap f := (V.comap f).mul_mem ha' hb'
      have hu'1 : a' * b' ≠ 1 := fun h => hab' (by
        have h2 : a' * a' = 1 := by rw [← sq]; exact sq_eq_one_of_mem_kleinFour hV' ha'
        calc a' = a' * (a' * b') := by rw [h, mul_one]
          _ = b' := by rw [← mul_assoc, h2, one_mul])
      obtain ⟨g', hg'N, hg'a⟩ :=
        pgl2_exists_mem_normalizer_conj_eq_mul hF hV' hu' hu'1 hu'J ha' ha'1 haJ
      have hb'eq : a' * b' * a' = b' := by
        have h2 : a' * a' = 1 := by rw [← sq]; exact sq_eq_one_of_mem_kleinFour hV' ha'
        rw [mul_assoc, mul_comm_of_mem_kleinFour hV' hb' ha', ← mul_assoc, h2, one_mul]
      refine ⟨f g', ⟨hfr ▸ ⟨g', rfl⟩, ?_⟩, ?_⟩
      · apply mem_normalizer_fintype
        intro v hv
        obtain ⟨v', rfl⟩ := hVr hv
        have hv' : v' ∈ V.comap f := hv
        have := (mem_normalizer_iff.mp hg'N v').mp hv'
        rw [← map_inv, ← map_mul, ← map_mul]
        exact this
      · rw [← ha'f, ← hb'f, ← map_inv, ← map_mul, ← map_mul, hg'a, hb'eq]
  · exact absurd (eq_bot_of_le_of_isKleinFour hL4 (hPa.trans inf_le_left)
      (odd_card_of_isPGroup hp hp2 hPap)) hPa1

theorem exists_conj_eq_of_isMaxInvIn
    {L V : Subgroup X}
    (hL : IsL2PGL2OrA7OrV4 L) (hV : IsKleinFour V) (hVL : V ≤ L) {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) {Q₁ Q₂ : Subgroup X} (h₁ : IsMaxInvIn p V L Q₁) (h₂ : IsMaxInvIn p V L Q₂) :
    ∃ g ∈ L ⊓ normalizer (V : Set X), Q₁.map (MulAut.conj g).toMonoidHom = Q₂ := by
  by_cases hQ : Q₁ = Q₂
  · refine ⟨1, one_mem _, ?_⟩
    rw [hQ, map_one]
    exact Subgroup.map_id Q₂
  have hQ₁1 : Q₁ ≠ ⊥ := fun h =>
    hQ (h₁.2.2.2 Q₂ h₂.1 h₂.2.1 h₂.2.2.1 (h ▸ bot_le)).symm
  have hQ₂1 : Q₂ ≠ ⊥ := fun h =>
    hQ (h₂.2.2.2 Q₁ h₁.1 h₁.2.1 h₁.2.2.1 (h ▸ bot_le))
  obtain ⟨a, ha, ha1, hQ₁s, -⟩ := exists_isSylowOf_of_isMaxInvIn hL hV hVL hp hp2 h₁
  obtain ⟨b, hb, hb1, hQ₂s, hQ₂all⟩ := exists_isSylowOf_of_isMaxInvIn hL hV hVL hp hp2 h₂
  have hab : a ≠ b := by
    rintro rfl
    exact hQ (h₁.2.2.2 Q₂ h₂.1 h₂.2.1 h₂.2.2.1 (hQ₂all Q₁ hQ₁s.le h₁.2.1)).symm
  obtain ⟨g, ⟨hgL, hgN⟩, hgab⟩ := exists_conj_eq_of_isPGroup_ne_bot hL hV hVL hp hp2 ha ha1 hb hb1
    hab hQ₁s.le h₁.2.1 hQ₁1 hQ₂s.le h₂.2.1 hQ₂1
  refine ⟨g, ⟨hgL, hgN⟩, ?_⟩
  have hle : Q₁.map (MulAut.conj g).toMonoidHom ≤ L ⊓ centralizer ({b} : Set X) := by
    rintro _ ⟨z, hz, rfl⟩
    have hz' := hQ₁s.le hz
    refine ⟨L.mul_mem (L.mul_mem hgL hz'.1) (L.inv_mem hgL), ?_⟩
    change g * z * g⁻¹ ∈ centralizer ({b} : Set X)
    rw [mem_centralizer_singleton_iff, ← hgab]
    have hza := mem_centralizer_singleton_iff.mp hz'.2
    calc g * z * g⁻¹ * (g * a * g⁻¹) = g * (z * a) * g⁻¹ := by group
      _ = g * (a * z) * g⁻¹ := by rw [hza]
      _ = g * a * g⁻¹ * (g * z * g⁻¹) := by group
  have h12 : Q₁.map (MulAut.conj g).toMonoidHom ≤ Q₂ := hQ₂all _ hle (h₁.2.1.map _)
  have h21 : Q₂.map (MulAut.conj g⁻¹).toMonoidHom = Q₁ := by
    refine h₁.2.2.2 _ ?_ (h₂.2.1.map _) ?_ ?_
    · rintro _ ⟨z, hz, rfl⟩
      exact L.mul_mem (L.mul_mem (L.inv_mem hgL) (h₂.1 hz)) (L.inv_mem (L.inv_mem hgL))
    · intro v hv
      apply mem_normalizer_fintype
      rintro _ ⟨z, hz, rfl⟩
      have hw : g * v * g⁻¹ ∈ V := (mem_normalizer_iff.mp hgN v).mp hv
      have hwz := (mem_normalizer_iff.mp (h₂.2.2.1 hw) z).mp hz
      refine ⟨_, hwz, ?_⟩
      change g⁻¹ * (g * v * g⁻¹ * z * (g * v * g⁻¹)⁻¹) * g⁻¹⁻¹ = v * (g⁻¹ * z * g⁻¹⁻¹) * v⁻¹
      group
    · intro y hy
      refine ⟨g * y * g⁻¹, h12 ⟨y, hy, rfl⟩, ?_⟩
      change g⁻¹ * (g * y * g⁻¹) * g⁻¹⁻¹ = y
      group
  rw [← h21, map_map]
  convert Subgroup.map_id Q₂
  ext z
  change g * (g⁻¹ * z * g⁻¹⁻¹) * g⁻¹ = z
  group

end FourGroup

end CFSG.GH72
