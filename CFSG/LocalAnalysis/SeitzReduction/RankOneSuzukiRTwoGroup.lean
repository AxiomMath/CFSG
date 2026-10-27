module

public import CFSG.LocalAnalysis.SeitzReduction.RankOneSuzukiRegularStab

public section

namespace CFSG.SeitzReduction.RankOne

open Subgroup CFSG.LocalAnalysis SzPartition

@[expose] def szRGroup {G : Type} [Group G] (L T : Subgroup G) (t : G)
    (E : Subgroup (Equiv.Perm (gmsRootConjugates (szA L T t) (zpowers t)))) : Subgroup G :=
  (E.comap (gmsRootConjugateAction (szA L T t) (zpowers t))).map
    (normalizer (szA L T t : Set G)).subtype

structure SzRData {G : Type} [Group G] (L T R : Subgroup G) (t : G) (f : ℕ) : Prop where
  le_normalizer : R ≤ normalizer (szA L T t : Set G)
  normalizer_le : normalizer (szA L T t : Set G) ≤ normalizer (R : Set G)
  le : T ≤ R
  inf_centralizer : R ⊓ centralizer ({t} : Set G) = T
  card : Nat.card R = 2 * (2 ^ f) ^ 3
  exists_conj : ∀ b ∈ szA₁ (szT₁ L T), ∃ r ∈ R, r * t * r⁻¹ = b * t
  mem_of_isPGroup : ∀ y ∈ normalizer (szA L T t : Set G),
    IsPGroup 2 (R ⊔ zpowers y : Subgroup G) → y ∈ R

variable {G : Type} [Group G]

theorem SzRData.isPGroup {L T R : Subgroup G} {t : G} {f : ℕ} (hR : SzRData L T R t f) :
    IsPGroup 2 R :=
  IsPGroup.of_card (n := 3 * f + 1) (by rw [hR.card, ← pow_mul, ← pow_succ']; ring_nf)

namespace SzStart

variable [Finite G] {L : Subgroup G} {f : ℕ} {t : G} {T : Subgroup G}

theorem szRData_of_regular (h : SzStart G L f t T)
    (hS2 : ∀ S : Sylow 2 (centralizer (L : Set G)), Nat.card S = 2)
    (hT : ¬ ∃ S : Sylow 2 G, (S : Subgroup G) = T)
    {E : Subgroup (Equiv.Perm (gmsRootConjugates (szA L T t) (zpowers t)))}
    (hE : E ≤ (gmsRootConjugateAction (szA L T t) (zpowers t)).range)
    (hEn : (E.subgroupOf (gmsRootConjugateAction (szA L T t) (zpowers t)).range).Normal)
    (hEc : Nat.card E = 2 ^ f)
    (hreg : ∀ Q Z, ∃! e : E, (e : Equiv.Perm (gmsRootConjugates (szA L T t) (zpowers t))) Q = Z) :
    SzRData L T (szRGroup L T t E) t f := by
  have hD := h.partitionData_of_card_sylow hS2 hT
  obtain ⟨hodd, -⟩ := h.stabilizer_odd_dvd_of_card_sylow hS2 hT
  obtain ⟨-, -, hcardT, -, -, -, -, hCA, -⟩ := h.facts_of_card_sylow hS2
  set NA := normalizer (szA L T t : Set G) with hNA
  set φ := gmsRootConjugateAction (szA L T t) (zpowers t) with hφ
  have hker : ∀ l : NA, φ l = 1 ↔ (l : G) ∈ T := h.action_eq_one_iff_of_card_sylow hS2 hT
  have hmem : ∀ x : G, x ∈ szRGroup L T t E ↔ ∃ hx : x ∈ NA, φ ⟨x, hx⟩ ∈ E := by
    intro x
    constructor
    · rintro ⟨l, hl, rfl⟩
      exact ⟨l.2, hl⟩
    · rintro ⟨hx, hxE⟩
      exact ⟨⟨x, hx⟩, hxE, rfl⟩
  have hTNA : T ≤ NA := fun x hx => by
    rw [← hCA] at hx
    exact centralizer_le_normalizer _ hx
  set α : gmsRootConjugates (szA L T t) (zpowers t) :=
    ⟨zpowers t, zpowers_mem_gmsRootConjugates_szA L T t⟩ with hα
  refine ⟨map_subtype_le _, fun n hn => ?_, fun x hx => ?_, ?_, ?_, fun b hb => ?_,
    fun y hy hy2 => ?_⟩
  ·
    refine mem_normalizer_of_forall_inv_mul_mul_mem fun x hx => ?_
    obtain ⟨hxN, hxE⟩ := (hmem x).mp hx
    refine (hmem _).mpr ⟨mul_mem (mul_mem (inv_mem hn) hxN) hn, ?_⟩
    have e : (⟨n⁻¹ * x * n, mul_mem (mul_mem (inv_mem hn) hxN) hn⟩ : NA) =
        (⟨n, hn⟩ : NA)⁻¹ * ⟨x, hxN⟩ * ⟨n, hn⟩ := rfl
    rw [e, map_mul, map_mul, map_inv]
    have key := hEn.conj_mem ⟨φ ⟨x, hxN⟩, hE hxE⟩ (mem_subgroupOf.mpr hxE)
      ⟨(φ ⟨n, hn⟩)⁻¹, inv_mem ⟨⟨n, hn⟩, rfl⟩⟩
    rw [mem_subgroupOf] at key
    simpa using key
  ·
    refine (hmem x).mpr ⟨hTNA hx, ?_⟩
    rw [(hker ⟨x, hTNA hx⟩).mpr hx]
    exact one_mem E
  ·
    refine le_antisymm (fun x hx => ?_) (le_inf (fun x hx => (hmem x).mpr ⟨hTNA hx, by
      rw [(hker ⟨x, hTNA hx⟩).mpr hx]; exact one_mem E⟩) h.le)
    obtain ⟨hxR, hxC⟩ := mem_inf.mp hx
    obtain ⟨hxN, hxE⟩ := (hmem x).mp hxR
    have hfix : φ ⟨x, hxN⟩ α = α := by
      apply Subtype.ext
      change (zpowers t).map (MulAut.conj x).toMonoidHom = zpowers t
      exact (hD.map_conj_zpowers_eq_iff x).mpr (mem_centralizer_singleton_iff.mp hxC)
    obtain ⟨e, -, huniq⟩ := hreg α α
    have h1 : (⟨φ ⟨x, hxN⟩, hxE⟩ : E) = e := huniq _ hfix
    have h2 : (1 : E) = e := huniq _ rfl
    have h3 : φ ⟨x, hxN⟩ = 1 := congrArg Subtype.val (h1.trans h2.symm)
    exact (hker ⟨x, hxN⟩).mp h3
  ·
    have hkerle : φ.ker ≤ E.comap φ := fun l hl => by
      rw [mem_comap, MonoidHom.mem_ker.mp hl]
      exact one_mem E
    have hkerT : φ.ker.map NA.subtype = T := by
      ext x
      constructor
      · rintro ⟨l, hl, rfl⟩
        exact (hker l).mp (MonoidHom.mem_ker.mp hl)
      · intro hx
        exact ⟨⟨x, hTNA hx⟩, MonoidHom.mem_ker.mpr ((hker ⟨x, hTNA hx⟩).mpr hx), rfl⟩
    have hkerc : Nat.card φ.ker = Nat.card T :=
      calc Nat.card φ.ker = Nat.card (φ.ker.map NA.subtype) :=
            (Subgroup.card_map_of_injective NA.subtype_injective).symm
        _ = Nat.card T := by rw [hkerT]
    have h1 := card_eq_card_map_mul_card_ker_of_ker_le φ hkerle
    rw [map_comap_eq, inf_eq_right.mpr hE, hEc, hkerc, hcardT] at h1
    rw [szRGroup, Subgroup.card_map_of_injective NA.subtype_injective, h1]
    ring
  ·
    set β : gmsRootConjugates (szA L T t) (zpowers t) :=
      ⟨zpowers (b * t), hD.mem_iff.mpr ⟨b, hb, rfl⟩⟩ with hβ
    obtain ⟨⟨e, heE⟩, he, -⟩ := hreg α β
    obtain ⟨l, hl⟩ := hE heE
    refine ⟨l, (hmem l).mpr ⟨l.2, by rw [Subtype.coe_eta, hl]; exact heE⟩, ?_⟩
    obtain ⟨c, hc, hct⟩ := hD.exists_conj_t_eq l.2
    have he' : e α = β := he
    have h1 : (zpowers t).map (MulAut.conj (l : G)).toMonoidHom = zpowers (b * t) := by
      rw [← hl] at he'
      exact congrArg Subtype.val he'
    rw [map_conj_zpowers, hct] at h1
    rw [hct, hD.eq_of_zpowers_eq hc hb h1]
  ·
    obtain ⟨⟨e, heE⟩, he, -⟩ := hreg α (φ ⟨y, hy⟩ α)
    obtain ⟨l, hl⟩ := hE heE
    have hlR : (l : G) ∈ szRGroup L T t E :=
      (hmem l).mpr ⟨l.2, by rw [Subtype.coe_eta, hl]; exact heE⟩
    set g := φ (l⁻¹ * ⟨y, hy⟩) with hg
    have hgα : g α = α := by
      have he' : e α = φ ⟨y, hy⟩ α := he
      rw [hg, map_mul, map_inv, hl, Equiv.Perm.mul_apply, ← he']
      exact e.symm_apply_apply α
    have hgS : g ∈ φ.range ⊓ MulAction.stabilizer
        (Equiv.Perm (gmsRootConjugates (szA L T t) (zpowers t))) α :=
      mem_inf.mpr ⟨⟨_, rfl⟩, MulAction.mem_stabilizer_iff.mpr hgα⟩
    obtain ⟨k, hk⟩ := hy2 ⟨(l : G)⁻¹ * y, mul_mem (inv_mem (mem_sup_left hlR))
      (mem_sup_right (mem_zpowers y))⟩
    have hgk : g ^ 2 ^ k = 1 := by
      have hk' : ((l : G)⁻¹ * y) ^ 2 ^ k = 1 := congrArg Subtype.val hk
      have e1 : (l⁻¹ * ⟨y, hy⟩ : NA) ^ 2 ^ k = 1 := Subtype.ext (by simpa using hk')
      rw [hg, ← map_pow, e1, map_one]
    have hord : orderOf g = 1 := by
      have h1 : orderOf g ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one hgk
      have h2 : Odd (orderOf g) := by
        have h3 := orderOf_dvd_natCard (⟨g, hgS⟩ : (φ.range ⊓ MulAction.stabilizer
          (Equiv.Perm (gmsRootConjugates (szA L T t) (zpowers t))) α :
            Subgroup (Equiv.Perm (gmsRootConjugates (szA L T t) (zpowers t)))))
        rw [Subgroup.orderOf_mk] at h3
        exact hodd.of_dvd_nat h3
      obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp h1
      rw [hj] at h2 ⊢
      rcases j with _ | j
      · rfl
      · exact absurd h2 (by
          rw [Nat.not_odd_iff_even, pow_succ]
          exact Nat.even_mul.mpr (Or.inr even_two))
    have hg1 : g = 1 := orderOf_eq_one_iff.mp hord
    refine (hmem y).mpr ⟨hy, ?_⟩
    have e2 : φ ⟨y, hy⟩ = φ l * g := by rw [hg, map_mul, map_inv, mul_inv_cancel_left]
    rw [e2, hg1, mul_one, hl]
    exact heE

end SzStart

end CFSG.SeitzReduction.RankOne
