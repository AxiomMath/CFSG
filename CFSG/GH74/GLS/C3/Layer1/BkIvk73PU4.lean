module

public import CFSG.GH74.GLS.C3.Layer1.BkIvk73Std
public import CFSG.GH74.GLS.Stage1.Thm4.Pure
public import CFSG.RankThree.Coprime.InvolutionFixedRankBound

public section

namespace CFSG.GH74.GLS.C3.Layer1.Bk

namespace PU4

open Subgroup CFSG CFSG.ABGLocalTools CFSG.GH74.GLS
open scoped commutatorElement

section A5

open Equiv

@[expose] def a5c0 : alternatingGroup (Fin 5) :=
  ⟨swap 0 1 * swap 2 3, Perm.mem_alternatingGroup.mpr (by decide)⟩

theorem a5_exists_conj_c0 : ∀ g : alternatingGroup (Fin 5), g * g = 1 → g ≠ 1 →
    ∃ σ : alternatingGroup (Fin 5), σ * g * σ⁻¹ = a5c0 := by
  decide +kernel

theorem a5_pow_cases : ∀ g : alternatingGroup (Fin 5), g ^ 2 = 1 ∨ g ^ 3 = 1 ∨ g ^ 5 = 1 := by
  decide +kernel

theorem a5_sq_eq_one_of_two_power {g : alternatingGroup (Fin 5)} {m : ℕ} (h : g ^ 2 ^ m = 1) :
    g ^ 2 = 1 := by
  have hd2 : orderOf g ∣ 2 ^ m := orderOf_dvd_of_pow_eq_one h
  rcases a5_pow_cases g with h2 | h3 | h5
  · exact h2
  · have hd1 : orderOf g ∣ 3 := orderOf_dvd_of_pow_eq_one h3
    have hcop : Nat.Coprime 3 (2 ^ m) := Nat.Coprime.pow_right m (by norm_num)
    have h1 := Nat.eq_one_of_dvd_coprimes hcop hd1 hd2
    rw [orderOf_eq_one_iff] at h1
    rw [h1]
    simp
  · have hd1 : orderOf g ∣ 5 := orderOf_dvd_of_pow_eq_one h5
    have hcop : Nat.Coprime 5 (2 ^ m) := Nat.Coprime.pow_right m (by norm_num)
    have h1 := Nat.eq_one_of_dvd_coprimes hcop hd1 hd2
    rw [orderOf_eq_one_iff] at h1
    rw [h1]
    simp

end A5

section KLevel

variable {K : Type} [Group K] [Finite K]

theorem odd_card_pPrimeCore : Odd (Nat.card (pPrimeCore 2 K)) :=
  Nat.coprime_two_left.mp pPrimeCore_coprime_card

omit [Finite K] in
theorem sq_eq_one_of_orderOf_two {w : K} (hw : orderOf w = 2) : w * w = 1 := by
  rw [← pow_two, ← hw]
  exact pow_orderOf_eq_one w

theorem mk_ne_one_of_orderOf_two {w : K} (hw : orderOf w = 2) :
    QuotientGroup.mk' (pPrimeCore 2 K) w ≠ 1 := by
  intro h1
  have hwO : w ∈ pPrimeCore 2 K := (QuotientGroup.eq_one_iff w).1 h1
  have h2 : orderOf w ∣ Nat.card (pPrimeCore 2 K) := by
    have := Subgroup.orderOf_dvd_natCard (pPrimeCore 2 K) hwO
    simpa [Subgroup.orderOf_coe] using this
  rw [hw] at h2
  exact (Nat.not_even_iff_odd.2 odd_card_pPrimeCore) (even_iff_two_dvd.2 h2)

theorem exists_conj_of_involutions_kbar (e : (K ⧸ pPrimeCore 2 K) ≃* alternatingGroup (Fin 5))
    {h z : K} (hh : orderOf h = 2) (hz : orderOf z = 2) : ∃ g : K, g * z * g⁻¹ = h := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set O := pPrimeCore 2 K with hO
  set π : K →* K ⧸ O := QuotientGroup.mk' O with hπ
  have hinv : ∀ w : K, orderOf w = 2 → e (π w) * e (π w) = 1 ∧ e (π w) ≠ 1 := fun w hw => by
    refine ⟨?_, fun h1 => mk_ne_one_of_orderOf_two hw (e.injective (by rw [h1, map_one]))⟩
    rw [← map_mul, ← map_mul, sq_eq_one_of_orderOf_two hw, map_one, map_one]
  obtain ⟨σh, hσh⟩ := a5_exists_conj_c0 _ (hinv h hh).1 (hinv h hh).2
  obtain ⟨σz, hσz⟩ := a5_exists_conj_c0 _ (hinv z hz).1 (hinv z hz).2
  obtain ⟨g₁, hg₁⟩ := QuotientGroup.mk'_surjective O (e.symm (σh⁻¹ * σz))
  have hg₁' : e (π g₁) = σh⁻¹ * σz := by
    have : π g₁ = e.symm (σh⁻¹ * σz) := hg₁
    rw [this, MulEquiv.apply_symm_apply]
  have hπeq : π (g₁ * z * g₁⁻¹) = π h := by
    apply e.injective
    have hh' : e (π h) = σh⁻¹ * a5c0 * σh := by rw [← hσh]; group
    have hz' : e (π z) = σz⁻¹ * a5c0 * σz := by rw [← hσz]; group
    rw [map_mul, map_mul, map_inv, map_mul, map_mul, map_inv, hg₁', hz', hh']
    group
  have hord' : orderOf (g₁ * z * g₁⁻¹) = 2 := by
    have := (MulAut.conj g₁).orderOf_eq z
    simpa [MulAut.conj_apply, hz] using this
  have hcoset : (g₁ * z * g₁⁻¹)⁻¹ * h ∈ O := QuotientGroup.eq.1 hπeq
  obtain ⟨c, hc⟩ := isConj_iff.1
    (CFSG.GH74.GLS.Stage1.Thm4.isConj_of_mem_coset (N := O) odd_card_pPrimeCore hord' hh hcoset)
  refine ⟨c * g₁, ?_⟩
  calc c * g₁ * z * (c * g₁)⁻¹ = c * (g₁ * z * g₁⁻¹) * c⁻¹ := by group
    _ = h := hc

theorem exists_four_group (e : (K ⧸ pPrimeCore 2 K) ≃* alternatingGroup (Fin 5)) :
    ∃ P : Subgroup K, Nat.card P = 4 ∧ ∀ p ∈ P, p * p = 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨P⟩ := (inferInstance : Nonempty (Sylow 2 K))
  set O := pPrimeCore 2 K with hO
  have hcardK : Nat.card K = 60 * Nat.card O := by
    have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup O
    have h2 : Nat.card (K ⧸ O) = 60 := by
      rw [Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card, card_alternatingGroup]
      norm_num [Nat.factorial]
    rw [h1, h2]
  have hv : (Nat.card K).factorization 2 = 2 := by
    have hodd : Odd (15 * Nat.card O) := (by decide : Odd 15).mul odd_card_pPrimeCore
    have h0 : 15 * Nat.card O ≠ 0 := hodd.pos.ne'
    have h2 : (15 * Nat.card O).factorization 2 = 0 :=
      Nat.factorization_eq_zero_of_not_dvd (by
        have := Nat.odd_iff.1 hodd
        omega)
    rw [hcardK, show 60 * Nat.card O = 2 ^ 2 * (15 * Nat.card O) by ring,
      Nat.factorization_mul (by positivity) h0, Finsupp.add_apply,
      Nat.Prime.factorization_pow Nat.prime_two, h2]
    simp
  refine ⟨(P : Subgroup K), ?_, ?_⟩
  · rw [Sylow.card_eq_multiplicity, hv]
    norm_num
  · intro p hp
    obtain ⟨m, hm⟩ := P.isPGroup' ⟨p, hp⟩
    have hpm : p ^ 2 ^ m = 1 := congrArg Subtype.val hm
    have h1 : (e (QuotientGroup.mk' O p)) ^ 2 = 1 := by
      apply a5_sq_eq_one_of_two_power (m := m)
      rw [← map_pow, ← map_pow, hpm, map_one, map_one]
    have h2 : p ^ 2 ∈ O := by
      have h4 : e (QuotientGroup.mk' O (p ^ 2)) = e 1 := by
        rw [map_pow, map_pow, h1, map_one]
      exact (QuotientGroup.eq_one_iff (p ^ 2)).1 (e.injective h4)
    have h3 : p ^ 2 ∈ (P : Subgroup K) ⊓ O := ⟨pow_mem hp 2, h2⟩
    rw [CFSG.GH74.GLS.Stage1.Thm4.inf_eq_bot_of_odd P.isPGroup' odd_card_pPrimeCore,
      Subgroup.mem_bot] at h3
    rw [← pow_two]
    exact h3

theorem two_le_pRank_of_kbar (e : (K ⧸ pPrimeCore 2 K) ≃* alternatingGroup (Fin 5)) :
    2 ≤ pRank 2 K := by
  obtain ⟨P, hcard, hsq⟩ := exists_four_group e
  have hcomm : ∀ u ∈ P, ∀ v ∈ P, u * v = v * u := by
    intro u hu v hv
    have h1 := hsq u hu
    have h2 := hsq v hv
    have h3 := hsq (u * v) (P.mul_mem hu hv)
    have hui : u⁻¹ = u := inv_eq_of_mul_eq_one_right h1
    have hvi : v⁻¹ = v := inv_eq_of_mul_eq_one_right h2
    have hwi : (u * v)⁻¹ = u * v := inv_eq_of_mul_eq_one_right h3
    rw [mul_inv_rev, hui, hvi] at hwi
    exact hwi.symm
  have hE := C3.Layer1.Back.isElementaryAbelian_of_forall hcomm hsq
  exact CFSG.RankThree.Coprime.le_pRank_of_isElementaryAbelian one_lt_two hE (k := 2)
    (by rw [hcard]; norm_num)

theorem eq_top_of_perfect_of_odd_quotient (hK : Group.IsPerfect K) (C : Subgroup K) [C.Normal]
    (hodd : Odd (Nat.card (K ⧸ C))) : C = ⊤ := by
  have hsolv : Group.IsSolvable (K ⧸ C) := CFSG.FeitThompson.isSolvable_of_odd_natCard _ hodd
  have hperf : Group.IsPerfect (K ⧸ C) := Group.IsPerfect.ofSurjective (QuotientGroup.mk'_surjective C)
  by_contra hne
  have : Nontrivial (K ⧸ C) := by
    rw [QuotientGroup.nontrivial_iff]
    exact hne
  exact Group.IsPerfect.not_isSolvable (K ⧸ C) hsolv

end KLevel

section GLevel

variable {G : Type} [Group G] [Finite G]

abbrev WC (x : G) : Subgroup G := pPrimeCoreOf 2 (centralizer ({x} : Set G))

abbrev RN (x : G) : Subgroup G := pPrimeCoreOf 2 (NW x)

theorem WC_le_RN (x : G) : WC x ≤ RN x := by
  refine le_pPrimeCoreOf_of_normal (show WC x ≤ NW x from Subgroup.le_normalizer) ?_
    (TwoThin.card_pPrimeCoreOf_odd _)
  intro g hg y hy
  exact (Subgroup.mem_normalizer_iff.1 hg y).1 hy

omit [Finite G] in
theorem mem_normalizer_RN {x n : G} (hn : n ∈ NW x) : n ∈ normalizer ((RN x : Subgroup G) : Set G) :=
  TwoThin.mem_normalizer_pPrimeCoreOf (Subgroup.le_normalizer hn)

theorem RN_inf_centralizer_le (x : G) : RN x ⊓ centralizer ({x} : Set G) ≤ WC x := by
  refine le_pPrimeCoreOf_of_normal inf_le_right ?_ ?_
  · intro g hg y hy
    have hgN : g ∈ NW x := centralizer_le_NW x hg
    exact ⟨(Subgroup.mem_normalizer_iff.1 (mem_normalizer_RN hgN) y).1 hy.1,
      (centralizer ({x} : Set G)).mul_mem ((centralizer ({x} : Set G)).mul_mem hg hy.2)
        ((centralizer ({x} : Set G)).inv_mem hg)⟩
  · exact Odd.of_dvd_nat (TwoThin.card_pPrimeCoreOf_odd (NW x))
      (Subgroup.card_dvd_of_le inf_le_left)

theorem RN_inf_centralizer (x : G) : RN x ⊓ centralizer ({x} : Set G) = WC x :=
  le_antisymm (RN_inf_centralizer_le x) (le_inf (WC_le_RN x) (TwoThin.pPrimeCoreOf_le _))

omit [Finite G] in
theorem map_conj_eq_of_mem_normalizer {A : Subgroup G} {n : G} (hn : n ∈ normalizer (A : Set G)) :
    A.map (MulAut.conj n).toMonoidHom = A := by
  ext y
  rw [mem_map_conjHom_iff]
  simpa using (Subgroup.mem_normalizer_iff.1 (Subgroup.inv_mem _ hn) y).symm

omit [Finite G] in
theorem RN_inf_centralizer_conj {x n : G} (hn : n ∈ NW x) (y : G) :
    RN x ⊓ centralizer ({n * y * n⁻¹} : Set G) =
      (RN x ⊓ centralizer ({y} : Set G)).map (MulAut.conj n).toMonoidHom := by
  ext u
  rw [mem_map_conjHom_iff, Subgroup.mem_inf, Subgroup.mem_inf,
    Subgroup.mem_centralizer_singleton_iff, Subgroup.mem_centralizer_singleton_iff]
  have hnR := mem_normalizer_RN hn
  have h1 : u ∈ RN x ↔ n⁻¹ * u * n ∈ RN x := by
    simpa using Subgroup.mem_normalizer_iff.1 (Subgroup.inv_mem _ hnR) u
  have h2 : u * (n * y * n⁻¹) = n * y * n⁻¹ * u ↔ n⁻¹ * u * n * y = y * (n⁻¹ * u * n) := by
    constructor
    · intro h
      calc n⁻¹ * u * n * y = n⁻¹ * (u * (n * y * n⁻¹)) * n := by group
        _ = n⁻¹ * (n * y * n⁻¹ * u) * n := by rw [h]
        _ = y * (n⁻¹ * u * n) := by group
    · intro h
      calc u * (n * y * n⁻¹) = n * (n⁻¹ * u * n * y) * n⁻¹ := by group
        _ = n * (y * (n⁻¹ * u * n)) * n⁻¹ := by rw [h]
        _ = n * y * n⁻¹ * u := by group
  rw [h1, h2]

theorem RN_inf_centralizer_z {x a : G} (haN : a ∈ NW x) :
    RN x ⊓ centralizer ({a * x * a⁻¹} : Set G) = WC x := by
  rw [RN_inf_centralizer_conj haN, RN_inf_centralizer]
  exact map_conj_eq_of_mem_normalizer (A := WC x) haN

theorem RN_inf_centralizer_of_involution {x a h : G} {K : Subgroup G} (hKN : K ≤ NW x)
    (haN : a ∈ NW x) (hx2 : orderOf x = 2) (hzK : a * x * a⁻¹ ∈ K)
    (e : (↥K ⧸ pPrimeCore 2 ↥K) ≃* alternatingGroup (Fin 5)) (hhK : h ∈ K) (hh2 : orderOf h = 2) :
    RN x ⊓ centralizer ({h} : Set G) = WC x := by
  have hz2 : orderOf (a * x * a⁻¹) = 2 := by
    have := (MulAut.conj a).orderOf_eq x
    simpa [MulAut.conj_apply, hx2] using this
  obtain ⟨g, hg⟩ := exists_conj_of_involutions_kbar e (h := ⟨h, hhK⟩)
    (z := ⟨a * x * a⁻¹, hzK⟩) (by rw [Subgroup.orderOf_mk]; exact hh2)
    (by rw [Subgroup.orderOf_mk]; exact hz2)
  have hgh : (g : G) * (a * x * a⁻¹) * (g : G)⁻¹ = h := congrArg Subtype.val hg
  rw [← hgh, RN_inf_centralizer_conj (hKN g.2), RN_inf_centralizer_z haN]
  exact map_conj_eq_of_mem_normalizer (A := WC x) (hKN g.2)

theorem RN_le_WC {x a : G} {K : Subgroup G} (hKN : K ≤ NW x) (haN : a ∈ NW x)
    (hx2 : orderOf x = 2) (hzK : a * x * a⁻¹ ∈ K)
    (e : (↥K ⧸ pPrimeCore 2 ↥K) ≃* alternatingGroup (Fin 5)) : RN x ≤ WC x := by
  obtain ⟨P, hPcard, hPsq⟩ := exists_four_group e
  set P₀ : Subgroup G := P.map K.subtype with hP₀
  have hP₀sq : ∀ m : P₀, m ^ 2 = 1 := by
    rintro ⟨_, ⟨p, hp, rfl⟩⟩
    apply Subtype.ext
    have := hPsq p hp
    simpa [pow_two] using congrArg Subtype.val this
  have hP₀card : Nat.card P₀ = 2 ^ 2 := by
    rw [hP₀, Subgroup.card_map_of_injective K.subtype_injective, hPcard]
    norm_num
  have hP₀norm : P₀ ≤ normalizer ((RN x : Subgroup G) : Set G) := by
    intro m hm
    obtain ⟨p, -, rfl⟩ := hm
    exact mem_normalizer_RN (hKN p.2)
  have hnd : ¬ 2 ∣ Nat.card (RN x) := fun hd =>
    (Nat.not_even_iff_odd.2 (TwoThin.card_pPrimeCoreOf_odd (NW x))) (even_iff_two_dvd.2 hd)
  have hgen := CFSG.RankThreeEvenClassification.Helpers.coprime_centralizer_generation_of_plane 2
    Nat.prime_two P₀ (RN x) hP₀sq hP₀card hnd hP₀norm
  refine hgen.le.trans (iSup_le fun m => iSup_le fun hm => ?_)
  have hmK : (m : G) ∈ K := by
    obtain ⟨p, -, hp⟩ := m.2
    rw [← hp]
    exact p.2
  have hm2 : orderOf (m : G) = 2 := by
    have hsq : (m : G) * (m : G) = 1 := by
      have := hP₀sq m
      simpa [pow_two] using congrArg Subtype.val this
    have h1 : (m : G) ≠ 1 := fun h => hm (Subtype.ext h)
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    exact orderOf_eq_prime (by rw [pow_two]; exact hsq) h1
  exact (RN_inf_centralizer_of_involution hKN haN hx2 hzK e hmK hm2).le

theorem K_le_centralizer_RN {x a : G} {K : Subgroup G} (hKN : K ≤ NW x) (haN : a ∈ NW x)
    (hx2 : orderOf x = 2) (hzK : a * x * a⁻¹ ∈ K) (hKq : IsQuasisimple ↥K)
    (e : (↥K ⧸ pPrimeCore 2 ↥K) ≃* alternatingGroup (Fin 5)) :
    K ≤ centralizer ((RN x : Subgroup G) : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hR : RN x = WC x := le_antisymm (RN_le_WC hKN haN hx2 hzK e) (WC_le_RN x)
  have hinv : ∀ w : ↥K, orderOf w = 2 → (w : G) ∈ centralizer ((RN x : Subgroup G) : Set G) := by
    intro w hw
    have hw2 : orderOf (w : G) = 2 := by rw [Subgroup.orderOf_coe]; exact hw
    have h1 := RN_inf_centralizer_of_involution hKN haN hx2 hzK e w.2 hw2
    rw [Subgroup.mem_centralizer_iff]
    intro r hr
    have hr' : r ∈ RN x ⊓ centralizer ({(w : G)} : Set G) := by
      rw [h1, ← hR]
      exact hr
    exact Subgroup.mem_centralizer_singleton_iff.1 hr'.2
  let C : Subgroup ↥K := (centralizer ((RN x : Subgroup G) : Set G)).comap K.subtype
  have hCn : C.Normal := by
    refine ⟨fun c hc k => ?_⟩
    show ((k * c * k⁻¹ : ↥K) : G) ∈ centralizer ((RN x : Subgroup G) : Set G)
    rw [Subgroup.mem_centralizer_iff]
    intro r hr
    have hr' : (k : G)⁻¹ * r * (k : G) ∈ RN x := by
      simpa using (Subgroup.mem_normalizer_iff.1
        (Subgroup.inv_mem _ (mem_normalizer_RN (hKN k.2))) r).1 hr
    have hc' : (c : G) ∈ centralizer ((RN x : Subgroup G) : Set G) := hc
    have := Subgroup.mem_centralizer_iff.1 hc' _ hr'
    calc r * ((k * c * k⁻¹ : ↥K) : G) = (k : G) * ((k : G)⁻¹ * r * (k : G) * (c : G)) * (k : G)⁻¹ := by
          simp only [Subgroup.coe_mul, Subgroup.coe_inv]; group
      _ = (k : G) * ((c : G) * ((k : G)⁻¹ * r * (k : G))) * (k : G)⁻¹ := by rw [this]
      _ = ((k * c * k⁻¹ : ↥K) : G) * r := by
          simp only [Subgroup.coe_mul, Subgroup.coe_inv]; group
  have hCtop : C = ⊤ := by
    set O := pPrimeCore 2 ↥K with hO
    have hz2 : orderOf (⟨a * x * a⁻¹, hzK⟩ : ↥K) = 2 := by
      rw [Subgroup.orderOf_mk]
      have := (MulAut.conj a).orderOf_eq x
      simpa [MulAut.conj_apply, hx2] using this
    have hzC : (⟨a * x * a⁻¹, hzK⟩ : ↥K) ∈ C := hinv _ hz2
    have hsimple : IsSimpleGroup (alternatingGroup (Fin 5)) :=
      alternatingGroup.isSimpleGroup (by simp)
    have hsimpleK : IsSimpleGroup (↥K ⧸ O) := e.isSimpleGroup_congr.2 hsimple
    have hDtop : C ⊔ O = ⊤ := by
      have hDn : (C ⊔ O).Normal := inferInstance
      have hmapn : ((C ⊔ O).map (QuotientGroup.mk' O)).Normal :=
        Subgroup.Normal.map hDn _ (QuotientGroup.mk'_surjective O)
      have := hmapn
      rcases hsimpleK.eq_bot_or_eq_top_of_normal ((C ⊔ O).map (QuotientGroup.mk' O)) with hb | ht
      · exfalso
        have hmem : QuotientGroup.mk' O ⟨a * x * a⁻¹, hzK⟩ ∈ (C ⊔ O).map (QuotientGroup.mk' O) :=
          Subgroup.mem_map_of_mem _ (Subgroup.mem_sup_left hzC)
        rw [hb, Subgroup.mem_bot] at hmem
        exact mk_ne_one_of_orderOf_two hz2 hmem
      · rw [eq_top_iff]
        intro k _
        have hk : QuotientGroup.mk' O k ∈ (C ⊔ O).map (QuotientGroup.mk' O) := ht ▸ Subgroup.mem_top _
        obtain ⟨d, hd, hdk⟩ := hk
        have h1 : d⁻¹ * k ∈ O := QuotientGroup.eq.1 hdk
        have : k = d * (d⁻¹ * k) := by group
        rw [this]
        exact (C ⊔ O).mul_mem hd (Subgroup.mem_sup_right h1)
    have hodd : Odd (Nat.card (↥K ⧸ C)) := by
      have hsurj : Function.Surjective ((QuotientGroup.mk' C).comp O.subtype) := by
        intro y
        obtain ⟨k, rfl⟩ := QuotientGroup.mk'_surjective C y
        have hk : k ∈ (↑(C ⊔ O) : Set ↥K) := by rw [hDtop]; exact Subgroup.mem_top k
        rw [Subgroup.mul_normal C O] at hk
        obtain ⟨c, hc, o, ho, rfl⟩ := hk
        refine ⟨⟨o, ho⟩, ?_⟩
        have hc1 : QuotientGroup.mk' C c = 1 := (QuotientGroup.eq_one_iff c).2 hc
        show QuotientGroup.mk' C o = QuotientGroup.mk' C (c * o)
        rw [map_mul, hc1, one_mul]
      exact Odd.of_dvd_nat odd_card_pPrimeCore
        (Subgroup.card_dvd_of_surjective (f := (QuotientGroup.mk' C).comp O.subtype) hsurj)
    exact eq_top_of_perfect_of_odd_quotient hKq.1 C hodd
  intro k hk
  have : (⟨k, hk⟩ : ↥K) ∈ C := hCtop ▸ Subgroup.mem_top _
  exact this

end GLevel

section Hat

variable {G : Type} [Group G] [Finite G]

theorem commutator_conj_eq_bot_of_isComponent {Y : Type} [Group Y] [Finite Y] {K : Subgroup Y}
    {g xx : Y} (hK : IsComponent K) (hZ : ∀ y ∈ K, (∀ k ∈ K, k * y = y * k) → y = 1)
    (hxC : xx ∈ centralizer (K : Set Y)) (hx1 : xx ≠ 1) (hgx : g * xx * g⁻¹ ∈ K) :
    ⁅K, K.map (MulAut.conj g⁻¹).toMonoidHom⁆ = ⊥ := by
  set K' : Subgroup Y := K.map (MulAut.conj g⁻¹).toMonoidHom with hK'def
  have hK' : IsComponent K' := CFSG.LocalCores.isComponent_map_mulEquiv _ hK
  have hxK' : xx ∈ K' := by
    rw [hK'def, mem_map_conjHom_iff]
    simpa using hgx
  rcases CFSG.LocalCores.distinct_components_commute hK hK' with heq | hcomm
  · exfalso
    have hxK : xx ∈ K := heq ▸ hxK'
    exact hx1 (hZ xx hxK fun k hk => Subgroup.mem_centralizer_iff.1 hxC k hk)
  · exact hcomm

omit [Finite G] in
theorem commutator_le_RN {x a : G} {K : Subgroup G} (hKN : K ≤ NW x) (haN : a ∈ NW x)
    (hhat : ⁅toNWbar x K, (toNWbar x K).map (MulAut.conj (piO ↥(NW x) ⟨a, haN⟩)⁻¹).toMonoidHom⁆ = ⊥) :
    ⁅K, K.map (MulAut.conj a⁻¹).toMonoidHom⁆ ≤ RN x := by
  rw [Subgroup.commutator_le]
  rintro k hk _ ⟨k₂, hk₂, rfl⟩
  have hkN : k ∈ NW x := hKN hk
  have hk₂N : k₂ ∈ NW x := hKN hk₂
  have hl : (MulAut.conj a⁻¹).toMonoidHom k₂ = a⁻¹ * k₂ * a := by simp
  have hlN : a⁻¹ * k₂ * a ∈ NW x :=
    (NW x).mul_mem ((NW x).mul_mem ((NW x).inv_mem haN) hk₂N) haN
  rw [hl]
  have h1 : piO ↥(NW x) ⟨k, hkN⟩ ∈ toNWbar x K := ⟨⟨k, hkN⟩, hk, rfl⟩
  have hπl : piO ↥(NW x) ⟨a⁻¹ * k₂ * a, hlN⟩ = (piO ↥(NW x) ⟨a, haN⟩)⁻¹ *
      piO ↥(NW x) ⟨k₂, hk₂N⟩ * piO ↥(NW x) ⟨a, haN⟩ := by
    rw [← map_inv, ← map_mul, ← map_mul]
    rfl
  have h2 : piO ↥(NW x) ⟨a⁻¹ * k₂ * a, hlN⟩ ∈
      (toNWbar x K).map (MulAut.conj (piO ↥(NW x) ⟨a, haN⟩)⁻¹).toMonoidHom := by
    rw [mem_map_conjHom_iff, hπl]
    have : (piO ↥(NW x) ⟨a, haN⟩)⁻¹⁻¹ * ((piO ↥(NW x) ⟨a, haN⟩)⁻¹ * piO ↥(NW x) ⟨k₂, hk₂N⟩ *
        piO ↥(NW x) ⟨a, haN⟩) * (piO ↥(NW x) ⟨a, haN⟩)⁻¹ = piO ↥(NW x) ⟨k₂, hk₂N⟩ := by group
    rw [this]
    exact ⟨⟨k₂, hk₂N⟩, hk₂, rfl⟩
  have h3 := Subgroup.commutator_mem_commutator h1 h2
  rw [hhat, Subgroup.mem_bot] at h3
  have h4 : piO ↥(NW x) ⁅(⟨k, hkN⟩ : ↥(NW x)), ⟨a⁻¹ * k₂ * a, hlN⟩⁆ = 1 := by
    rw [map_commutatorElement]
    exact h3
  have h5 : ⁅(⟨k, hkN⟩ : ↥(NW x)), ⟨a⁻¹ * k₂ * a, hlN⟩⁆ ∈ pPrimeCore 2 ↥(NW x) :=
    (QuotientGroup.eq_one_iff _).1 h4
  exact ⟨_, h5, rfl⟩

end Hat

end PU4

open Subgroup CFSG CFSG.ABGLocalTools CFSG.GH74.GLS
open scoped commutatorElement

theorem b_ivk_7_3_A57_std_of_PU4_core
    (hPU4 : B_cor_PU4)
    {G : Type} [Group G] [Finite G]
    (hks : IsKProperSimple G)
    {x : G} {K T Q S : Subgroup G} {a : G}
    (h : IsAConfigW 5 x K T Q S a)
    (hz : a * x * a⁻¹ ∈ T ⊓ K) (haN : a ∈ NW x)
    (hcomp : IsComponent (toNWbar x K)) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hKN : K ≤ NW x := h.K_le_C.trans (centralizer_le_NW x)
  have hxN : x ∈ NW x := centralizer_le_NW x (mem_centralizer_singleton_iff.2 rfl)
  have hKq : IsQuasisimple ↥K := isQuasisimple_of_isCompIn' h.terminal.2.1
  obtain ⟨ekbar⟩ := h.kbar
  have hzK : a * x * a⁻¹ ∈ K := hz.2
  have hKstd : IsStandardSubgroup K :=
    hPU4 G hks x K h.x_order h.twoTerminal.1.2.2 (PU4.two_le_pRank_of_kbar ekbar) h.terminal
  obtain ⟨hZ, -, -⟩ := exists_conj_data (Or.inl rfl) h hz haN
  have hxC : piO ↥(NW x) ⟨x, hxN⟩ ∈
      centralizer ((toNWbar x K : Subgroup (NWbar x)) : Set (NWbar x)) := by
    rw [Subgroup.mem_centralizer_iff]
    rintro _ ⟨k, hk, rfl⟩
    have h1 : (k : G) * x = x * (k : G) := mem_centralizer_singleton_iff.1 (h.K_le_C hk)
    show piO ↥(NW x) k * piO ↥(NW x) ⟨x, hxN⟩ = piO ↥(NW x) ⟨x, hxN⟩ * piO ↥(NW x) k
    rw [← map_mul, ← map_mul]
    exact congrArg (piO ↥(NW x)) (Subtype.ext h1)
  have hx1 : piO ↥(NW x) ⟨x, hxN⟩ ≠ 1 := by
    have hx2 : orderOf (⟨x, hxN⟩ : ↥(NW x)) = 2 := by
      rw [Subgroup.orderOf_mk]; exact h.x_order
    intro h1
    have := orderOf_piO_of_orderOf_two hx2
    rw [h1, orderOf_one] at this
    omega
  have hgx : piO ↥(NW x) ⟨a, haN⟩ * piO ↥(NW x) ⟨x, hxN⟩ * (piO ↥(NW x) ⟨a, haN⟩)⁻¹ ∈
      toNWbar x K := by
    have hzN : a * x * a⁻¹ ∈ NW x :=
      (NW x).mul_mem ((NW x).mul_mem haN hxN) ((NW x).inv_mem haN)
    have h1 : piO ↥(NW x) (⟨a, haN⟩ * ⟨x, hxN⟩ * ⟨a, haN⟩⁻¹) =
        piO ↥(NW x) ⟨a, haN⟩ * piO ↥(NW x) ⟨x, hxN⟩ * (piO ↥(NW x) ⟨a, haN⟩)⁻¹ := by
      rw [map_mul, map_mul, map_inv]
    rw [← h1]
    exact ⟨⟨a * x * a⁻¹, hzN⟩, hzK, rfl⟩
  have hhat := PU4.commutator_conj_eq_bot_of_isComponent hcomp hZ hxC hx1 hgx
  have hcomm : ⁅K, K.map (MulAut.conj a⁻¹).toMonoidHom⁆ ≤ PU4.RN x :=
    PU4.commutator_le_RN hKN haN hhat
  have hKR : K ≤ centralizer ((PU4.RN x : Subgroup G) : Set G) :=
    PU4.K_le_centralizer_RN hKN haN h.x_order hzK hKq ekbar
  have hRK : PU4.RN x ≤ centralizer (K : Set G) := Subgroup.le_centralizer_iff.2 hKR
  have hK'R : K.map (MulAut.conj a⁻¹).toMonoidHom ≤ centralizer ((PU4.RN x : Subgroup G) : Set G) := by
    rintro _ ⟨k₂, hk₂, rfl⟩
    rw [Subgroup.mem_centralizer_iff]
    intro r hr
    have hr' : a * r * a⁻¹ ∈ PU4.RN x :=
      (Subgroup.mem_normalizer_iff.1 (PU4.mem_normalizer_RN haN) r).1 hr
    have h1 := Subgroup.mem_centralizer_iff.1 (hKR hk₂) _ hr'
    have hl : (MulAut.conj a⁻¹).toMonoidHom k₂ = a⁻¹ * k₂ * a := by simp
    rw [hl]
    calc r * (a⁻¹ * k₂ * a) = a⁻¹ * ((a * r * a⁻¹) * k₂) * a := by group
      _ = a⁻¹ * (k₂ * (a * r * a⁻¹)) * a := by rw [h1]
      _ = a⁻¹ * k₂ * a * r := by group
  have hbot : ⁅K, K.map (MulAut.conj a⁻¹).toMonoidHom⁆ = ⊥ := by
    have h1 : ⁅⁅K, K.map (MulAut.conj a⁻¹).toMonoidHom⁆, K⁆ = ⊥ :=
      Subgroup.commutator_eq_bot_iff_le_centralizer.2 (hcomm.trans hRK)
    have h2 : ⁅⁅K.map (MulAut.conj a⁻¹).toMonoidHom, K⁆, K⁆ = ⊥ := by
      rw [Subgroup.commutator_comm (K.map (MulAut.conj a⁻¹).toMonoidHom) K]
      exact h1
    have h3 := Subgroup.commutator_commutator_eq_bot_of_rotate h1 h2
    have hKp : ⁅K, K⁆ = K := Subgroup.isPerfect_iff.mp hKq.1
    rwa [hKp] at h3
  exact hKstd.2.2.2.2 a hbot

theorem b_ivk_7_3_A57_std_of_PU4 (hPU4 : B_cor_PU4) : B_ivk_7_3_A57_std := by
  intro G _ _ hG x K T Q S a h _hS' hz haN _hW hcomp
  exact b_ivk_7_3_A57_std_of_PU4_core hPU4 hG.kproper h hz haN hcomp

end CFSG.GH74.GLS.C3.Layer1.Bk
