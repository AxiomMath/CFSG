module

public import CFSG.LocalAnalysis.GH72.Sec4C
public import CFSG.LocalAnalysis.GH72.Sec4A
public import CFSG.LocalAnalysis.GH72.GWTwoExtension
public import CFSG.LocalAnalysis.GH72.RelativeZJAmbient
public import CFSG.LocalAnalysis.GH72.Alignment

public section

namespace CFSG.GH72

open Subgroup
open CFSG.ABGLocalTools (IsSylowOf isSylowOf_iff)

section Generic

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
private theorem mem_normalizer_of_normal {H : Subgroup G} (hH : H.Normal) (g : G) :
    g ∈ normalizer (H : Set G) := by
  rw [normalizer_eq_top_iff.mpr hH]
  exact mem_top g

omit [Finite G] in
private theorem normal_of_forall_map_cj {K : Subgroup G} (h : ∀ g : G, K.map (G4c.cj g) = K) :
    K.Normal :=
  normalizer_eq_top_iff.mp (eq_top_iff.mpr fun g _ => G4c.mem_normalizer_of_map_cj_eq (h g))

theorem normal_O_of_normal {H : Subgroup G} (hH : H.Normal) : (O H).Normal :=
  normal_of_forall_map_cj fun g => by
    rw [G4c.map_cj_O, G4c.map_cj_eq_of_mem_normalizer (mem_normalizer_of_normal hH g)]

theorem normal_O2_of_normal {H : Subgroup G} (hH : H.Normal) : (O2 H).Normal :=
  normal_of_forall_map_cj fun g => by
    rw [G4c.map_cj_O2, G4c.map_cj_eq_of_mem_normalizer (mem_normalizer_of_normal hH g)]

theorem O_eq_bot_of_normal (hO : CFSG.oddCore G = ⊥) {H : Subgroup G} (hH : H.Normal) :
    O H = ⊥ := by
  have h := CFSG.ABGLocalTools.le_oddCore_of_normal (normal_O_of_normal hH) (G4c.odd_card_O H)
  rwa [hO, le_bot_iff] at h

omit [Finite G] in
theorem IsL2OrA7.isAStarFactor {L : Subgroup G} {q : ℕ} (hq : 5 ≤ q) (h : IsL2OrA7 L q) :
    IsAStarFactor L := by
  rcases h with h | ⟨p, k, hp, hp2, hpk, he⟩
  · exact Or.inl h
  · exact Or.inr (Or.inl ⟨p, k, hp, hp2, hq.trans hpk, he⟩)

theorem odd_index_of_sylow_le (S : Sylow 2 G) {K : Subgroup G} (hSK : (S : Subgroup G) ≤ K) :
    Odd K.index := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine Nat.odd_iff.mpr (Nat.two_dvd_ne_zero.mp fun h2 => S.not_dvd_index ?_)
  exact h2.trans (index_dvd_of_le hSK)

omit [Finite G] in
theorem not_normal_of_isDihNonab {P : Subgroup G} (hP : IsDihNonab P)
    (hc : ∀ x ∈ P, ∀ y ∈ P, orderOf x = 2 → orderOf y = 2 → IsConj x y) {z : G} (hzP : z ∈ P)
    (hz2 : orderOf z = 2) (hPz : P ≤ C z) : ¬ P.Normal := by
  intro hn
  have hle : P ≤ centralizer (P : Set G) := by
    refine (isDih_of_isDihNonab hP).le_of_forall_involution fun t ht ht2 => ?_
    obtain ⟨c, rfl⟩ := isConj_iff.mp (hc z hzP t ht hz2 ht2)
    rw [mem_centralizer_iff]
    intro x hx
    have hx' : c⁻¹ * x * c⁻¹⁻¹ ∈ P := hn.conj_mem x hx c⁻¹
    rw [inv_inv] at hx'
    have hcomm : c⁻¹ * x * c * z = z * (c⁻¹ * x * c) := mem_centralizer_singleton_iff.mp (hPz hx')
    calc x * (c * z * c⁻¹) = c * (c⁻¹ * x * c * z) * c⁻¹ := by group
      _ = c * (z * (c⁻¹ * x * c)) * c⁻¹ := by rw [hcomm]
      _ = c * z * c⁻¹ * x := by group
  obtain ⟨x, hx, y, hy, hxy⟩ := hP.exists_mul_ne_mul
  exact hxy (mem_centralizer_iff.mp (hle hy) x hx)

theorem le_or_eq_bot_of_normal (hO : CFSG.oddCore G = ⊥) {P H K : Subgroup G} (hP : IsDih P)
    (hc : ∀ x ∈ P, ∀ y ∈ P, orderOf x = 2 → orderOf y = 2 → IsConj x y)
    (hPH : IsSylowOf 2 P H) (hK : K.Normal) (hKH : K ≤ H) : P ≤ K ∨ K = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_cases hex : ∃ t ∈ P, orderOf t = 2 ∧ t ∈ K
  · obtain ⟨t, htP, ht2, htK⟩ := hex
    refine Or.inl (hP.le_of_forall_involution fun x hx hx2 => ?_)
    obtain ⟨c, rfl⟩ := isConj_iff.mp (hc t htP x hx ht2 hx2)
    exact hK.conj_mem t htK c
  · push Not at hex
    refine Or.inr ?_
    have hodd : Odd (Nat.card K) := by
      by_contra hev
      rw [Nat.not_odd_iff_even, even_iff_two_dvd] at hev
      obtain ⟨k, hk⟩ := exists_prime_orderOf_dvd_card' 2 hev
      have hk2 : orderOf (k : G) = 2 := by rwa [Subgroup.orderOf_coe]
      have hZ : IsPGroup 2 (zpowers (k : G)) :=
        IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hk2, pow_one])
      obtain ⟨h, -, hle⟩ := exists_mem_map_conj_le_of_isSylowOf hPH
        ((zpowers_le.mpr k.2).trans hKH) hZ
      have hmem : h * k * h⁻¹ ∈ P := hle ⟨k, mem_zpowers _, rfl⟩
      have hord : orderOf (h * k * h⁻¹) = 2 := by
        have hsc : SemiconjBy h (k : G) (h * k * h⁻¹) := by
          change h * k = h * k * h⁻¹ * h
          group
        rw [← hk2]
        exact (hsc.orderOf_eq h).symm
      exact hex _ hmem hord (hK.conj_mem _ k.2 h)
    have h := CFSG.ABGLocalTools.le_oddCore_of_normal hK hodd
    rwa [hO, le_bot_iff] at h

theorem exists_isL2OrA7_of_isSylowOf
    (hO : CFSG.oddCore G = ⊥) {P : Subgroup G} (hP : IsDih P)
    (hc : ∀ x ∈ P, ∀ y ∈ P, orderOf x = 2 → orderOf y = 2 → IsConj x y) (hnP : ¬ P.Normal)
    (H : Subgroup G) (hH : H.Normal) (hPH : IsSylowOf 2 P H) :
    ∃ L : Subgroup G, L ≤ H ∧ L.Normal ∧ IsSylowOf 2 P L ∧ IsL2OrA7 L 5 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  induction hn : Nat.card H using Nat.strong_induction_on generalizing H with
  | _ n ih =>
  have red : ∀ K : Subgroup G, K < H → K.Normal → IsSylowOf 2 P K →
      ∃ L : Subgroup G, L ≤ H ∧ L.Normal ∧ IsSylowOf 2 P L ∧ IsL2OrA7 L 5 := by
    intro K hKH hK hPK
    obtain ⟨L, hLK, hL⟩ := ih _ (hn ▸ card_lt_of_lt hKH) K hK hPK rfl
    exact ⟨L, hLK.trans hKH.le, hL⟩
  have hn2 : ¬ IsPGroup 2 H := fun h2 => hnP (hPH.eq_of_le hPH.le le_rfl h2 ▸ hH)
  have hK := normal_O2_of_normal hH
  rcases le_or_eq_bot_of_normal hO hP hc hPH hK (G4c.O2_le H) with hPK | hK1
  swap
  · exfalso
    apply hn2
    obtain ⟨m, hm⟩ := G4c.exists_relIndex_O2 H
    rw [hK1, relIndex_bot_left] at hm
    exact IsPGroup.of_card hm
  by_cases hKH : O2 H = H
  swap
  · exact red _ (lt_of_le_of_ne (G4c.O2_le H) hKH) hK (hPH.of_le hPK (G4c.O2_le H))
  have hOH : CFSG.oddCore H = ⊥ :=
    (map_eq_bot_iff_of_injective _ H.subtype_injective).mp (O_eq_bot_of_normal hO hH)
  have h2H : ∀ N : Subgroup H, N.Normal → N.index ≠ 2 := by
    intro N hN hidx
    have hrel : (N.map H.subtype).relIndex H = 2 ^ 1 := by
      rw [relIndex, subgroupOf, comap_map_eq_self_of_injective H.subtype_injective, hidx,
        pow_one]
    have hle := G4c.O2_le_of_relIndex (map_subtype_le N)
      (CFSG.ABGLocalTools.le_normalizer_map_subtype H N) hrel
    rw [hKH] at hle
    have htop : (⊤ : Subgroup H) ≤ N := by
      rw [← map_le_map_iff_of_injective H.subtype_injective, ← MonoidHom.range_eq_map,
        range_subtype]
      exact hle
    rw [top_le_iff.mp htop, index_top] at hidx
    exact absurd hidx (by norm_num)
  obtain ⟨hodd, hF⟩ :=
    gw_commutator_form hOH h2H (hasDihedralSylowTwo_of_isSylowOf hPH hP)
  have := hH
  have hFH : (⁅H, H⁆ : Subgroup G) ≤ H := G4c.commutator_le_of_le le_rfl le_rfl
  have hPF : P ≤ ⁅H, H⁆ := by
    have h1 : P.subgroupOf H ≤ commutator H :=
      CFSG.pSubgroup_le_of_not_dvd_index Nat.prime_two inferInstance hodd.not_two_dvd_nat
        hPH.isPGroup.comap_subtype
    have h2 := map_mono (f := H.subtype) h1
    rwa [map_subgroupOf_eq_of_le hPH.le, G4c.map_subtype_commutator] at h2
  by_cases hFeq : (⁅H, H⁆ : Subgroup G) = H
  swap
  · exact red _ (lt_of_le_of_ne hFH hFeq) inferInstance (hPH.of_le hPF hFH)
  have hA := isAStarFactor_commutator_of_subgroup H hF
  rw [hFeq] at hA
  refine ⟨H, le_rfl, hH, hPH, ?_⟩
  rcases hA with h7 | hpsl | hV
  · exact Or.inl h7
  · exact Or.inr hpsl
  · exact absurd (IsPGroup.of_card (n := 2) (by rw [hV.card_four]; norm_num)) hn2

theorem isIsolatedIn_sup_zpowers (S : Sylow 2 G) {P Q L : Subgroup G} (hinf : P ⊓ Q = ⊥)
    (hsep : ∀ x ∈ (S : Subgroup G), ∀ y ∈ (S : Subgroup G), orderOf x = 2 → IsConj x y →
      (x ∈ Q ↔ y ∈ Q))
    (hSL : (S : Subgroup G) ⊓ L ≤ P) (hL : L.Normal) {s : G} (hsQ : s ∈ Q)
    (hQS : Q ≤ S) (hs2 : orderOf s = 2) : IsIsolatedIn (L ⊔ zpowers s) s := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine ⟨mem_sup_right (mem_zpowers s), hs2, fun g hg hcomm => ?_⟩
  have hnorm : zpowers s ≤ normalizer (L : Set G) := by
    rw [normalizer_eq_top_iff.mpr hL]
    exact le_top
  obtain ⟨l, hl, n, hn, rfl⟩ :=
    (CFSG.CGT.Foote81L6.mem_sup_iff_of_le_normalizer hnorm).mp hg
  obtain ⟨m, rfl⟩ := mem_zpowers_iff.mp hn
  have hred : l * s ^ m * s * (l * s ^ m)⁻¹ = l * s * l⁻¹ := by group
  rw [hred] at hcomm ⊢
  by_contra hne
  obtain ⟨k, hk⟩ : ∃ k, k = l * s * l⁻¹ * s⁻¹ := ⟨_, rfl⟩
  have hkL : k ∈ L := by
    rw [hk, show l * s * l⁻¹ * s⁻¹ = l * (s * l⁻¹ * s⁻¹) by group]
    exact L.mul_mem hl (hL.conj_mem _ (L.inv_mem hl) s)
  have hk1 : k ≠ 1 := fun h => hne (mul_inv_eq_one.mp (hk ▸ h))
  have hks : Commute k s := hk ▸ hcomm.mul_left (Commute.refl s).inv_left
  have hkk : k ^ 2 = 1 := by
    rw [hk, hcomm.inv_right.mul_pow, conj_pow, inv_pow, ← hs2, pow_orderOf_eq_one]
    group
  have hk2 : orderOf k = 2 := orderOf_eq_prime hkk hk1
  have hR : IsPGroup 2 (zpowers k ⊔ zpowers s : Subgroup G) := by
    refine IsPGroup.to_sup_of_normal_left'
      (IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hk2, pow_one]))
      (IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hs2, pow_one])) ?_
    rw [zpowers_le]
    refine centralizer_le_normalizer _ (mem_centralizer_iff.mpr fun x hx => ?_)
    obtain ⟨j, rfl⟩ := mem_zpowers_iff.mp hx
    exact (hks.zpow_left j).eq
  obtain ⟨c, hc⟩ := exists_map_conj_le_sylow S hR
  have hcS : ∀ x ∈ zpowers k ⊔ zpowers s, c * x * c⁻¹ ∈ (S : Subgroup G) :=
    fun x hx => hc ⟨x, hx, rfl⟩
  have hck : c * k * c⁻¹ ∈ (S : Subgroup G) := hcS k (mem_sup_left (mem_zpowers k))
  have hcs : c * s * c⁻¹ ∈ (S : Subgroup G) := hcS s (mem_sup_right (mem_zpowers s))
  have hsS : s ∈ (S : Subgroup G) := hQS hsQ
  have hcsQ : c * s * c⁻¹ ∈ Q :=
    (hsep s hsS _ hcs hs2 (isConj_iff.mpr ⟨c, rfl⟩)).mp hsQ
  have hcuQ : c * k * c⁻¹ * (c * s * c⁻¹) ∈ Q := by
    refine (hsep s hsS _ ((S : Subgroup G).mul_mem hck hcs) hs2 (isConj_iff.mpr ⟨c * l, ?_⟩)).mp
      hsQ
    rw [hk]
    group
  have hckQ : c * k * c⁻¹ ∈ Q := by
    rw [show c * k * c⁻¹ = c * k * c⁻¹ * (c * s * c⁻¹) * (c * s * c⁻¹)⁻¹ by group]
    exact Q.mul_mem hcuQ (Q.inv_mem hcsQ)
  have hckP : c * k * c⁻¹ ∈ P := hSL (mem_inf.mpr ⟨hck, hL.conj_mem k hkL c⟩)
  have h1 : c * k * c⁻¹ ∈ P ⊓ Q := mem_inf.mpr ⟨hckP, hckQ⟩
  rw [hinf, mem_bot, conj_eq_one_iff] at h1
  exact hk1 h1

theorem mem_centralizer_of_isIsolatedIn {L : Subgroup G} (hL : L.Normal)
    (hsimple : IsSimpleGroup L) (heven : Even (Nat.card L)) {s : G}
    (hs : IsIsolatedIn (L ⊔ zpowers s) s) : s ∈ centralizer (L : Set G) := by
  set H' := L ⊔ zpowers s
  have hN : O H' ⊓ L = ⊥ := by
    have hLN : L ≤ normalizer ((O H' ⊓ L : Subgroup G) : Set G) :=
      le_trans (le_inf ((le_sup_left : L ≤ H').trans (le_normalizer_O H')) le_normalizer)
        inf_normalizer_le_normalizer_inf
    have hn : ((O H' ⊓ L).subgroupOf L).Normal := normal_subgroupOf_of_le_normalizer hLN
    rcases hn.eq_bot_or_eq_top with h | h
    · rw [eq_bot_iff]
      intro x hx
      have hx' : (⟨x, (mem_inf.mp hx).2⟩ : L) ∈ (O H' ⊓ L).subgroupOf L := hx
      rw [h, mem_bot] at hx'
      exact (mem_bot).mpr (congrArg Subtype.val hx')
    · exfalso
      rw [subgroupOf_eq_top] at h
      have hodd : Odd (Nat.card L) := G4c.odd_card_of_le (h.trans inf_le_left) (G4c.odd_card_O H')
      exact (Nat.not_even_iff_odd.mpr hodd) heven
  rw [mem_centralizer_iff]
  intro h hh
  have h1 : h * s * h⁻¹ * s⁻¹ ∈ O H' := hs.conj_mul_inv_mem_O (mem_sup_left hh)
  have h2 : h * s * h⁻¹ * s⁻¹ ∈ L := by
    rw [show h * s * h⁻¹ * s⁻¹ = h * (s * h⁻¹ * s⁻¹) by group]
    exact L.mul_mem hh (hL.conj_mem _ (L.inv_mem hh) s)
  have h3 : h * s * h⁻¹ * s⁻¹ = 1 := by
    have h4 : h * s * h⁻¹ * s⁻¹ ∈ O H' ⊓ L := mem_inf.mpr ⟨h1, h2⟩
    rwa [hN, mem_bot] at h4
  calc h * s = h * s * h⁻¹ * s⁻¹ * (s * h) := by group
    _ = s * h := by rw [h3, one_mul]

theorem not_isSylowOf_of_normal
    (hO : CFSG.oddCore G = ⊥) (hnc : ¬ AStarConclusion G) (S : Sylow 2 G) {P Q : Subgroup G}
    (hmem : ∀ g ∈ (S : Subgroup G), ∃ a ∈ P, ∃ b ∈ Q, g = a * b) (hPS : P ≤ S) (hQS : Q ≤ S)
    (hinf : P ⊓ Q = ⊥) (hP : IsDih P) (hQ : IsDih Q)
    (hcP : ∀ x ∈ P, ∀ y ∈ P, orderOf x = 2 → orderOf y = 2 → IsConj x y)
    (hcQ : ∀ x ∈ Q, ∀ y ∈ Q, orderOf x = 2 → orderOf y = 2 → IsConj x y)
    (hsep : ∀ x ∈ (S : Subgroup G), ∀ y ∈ (S : Subgroup G), orderOf x = 2 → IsConj x y →
      (x ∈ Q ↔ y ∈ Q))
    (hnP : ¬ P.Normal) (hnQ : ¬ Q.Normal) (H : Subgroup G) (hH : H.Normal) :
    ¬ IsSylowOf 2 P H := by
  intro hPH
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨L, -, hL, hPL, hL5⟩ := exists_isL2OrA7_of_isSylowOf hO hP hcP hnP H hH hPH
  have hSL : (S : Subgroup G) ⊓ L ≤ P :=
    (hPL.eq_of_le (le_inf hPS hPL.le) inf_le_right (S.isPGroup'.to_le inf_le_left)).le
  have heven : Even (Nat.card L) := by
    obtain ⟨a, -, ⟨e⟩⟩ := hP
    refine even_iff_two_dvd.mpr ((?_ : 2 ∣ Nat.card P).trans (card_dvd_of_le hPL.le))
    rw [Nat.card_congr e.toEquiv, DihedralGroup.nat_card]
    exact dvd_mul_right 2 _
  have hQC : Q ≤ centralizer (L : Set G) := hQ.le_of_forall_involution fun s hs hs2 =>
    mem_centralizer_of_isIsolatedIn hL (isSimpleGroup_of_isL2OrA7 le_rfl hL5) heven
      (isIsolatedIn_sup_zpowers S hinf hsep hSL hL hs hQS hs2)
  have := hL
  have hCn : (centralizer (L : Set G)).Normal := normal_centralizer
  have hLC : L ⊓ centralizer (L : Set G) = ⊥ := inf_centralizer_eq_bot_of_isL2OrA7 L hL5
  have hSC : (S : Subgroup G) ⊓ centralizer (L : Set G) = Q := by
    refine le_antisymm ?_ (le_inf hQS hQC)
    intro g hg
    obtain ⟨hgS, hgC⟩ := mem_inf.mp hg
    obtain ⟨a, ha, b, hb, rfl⟩ := hmem g hgS
    have haC : a ∈ centralizer (L : Set G) := by
      have h := (centralizer (L : Set G)).mul_mem hgC
        ((centralizer (L : Set G)).inv_mem (hQC hb))
      rwa [mul_inv_cancel_right] at h
    have ha1 : a = 1 := by
      have h : a ∈ L ⊓ centralizer (L : Set G) := mem_inf.mpr ⟨hPL.le ha, haC⟩
      rwa [hLC, mem_bot] at h
    rw [ha1, one_mul]
    exact hb
  have hQC' : IsSylowOf 2 Q (centralizer (L : Set G)) := by
    have hT : IsSylowOf 2 (S : Subgroup G) ⊤ := by
      rw [isSylowOf_iff, relIndex_top_right]
      exact ⟨le_top, S.isPGroup', S.not_dvd_index⟩
    have h := hT.inf_of_le_normalizer le_top (normalizer_eq_top_iff.mpr hCn).ge
    rwa [hSC] at h
  obtain ⟨K, hKC, hK, hQK, hK5⟩ := exists_isL2OrA7_of_isSylowOf hO hQ hcQ hnQ _ hCn hQC'
  refine hnc ⟨L, K, hL, hK, ?_, odd_index_of_sylow_le S fun g hg => ?_,
    hL5.isAStarFactor le_rfl, hK5.isAStarFactor le_rfl⟩
  · exact le_bot_iff.mp (le_trans (inf_le_inf_left L hKC) hLC.le)
  · obtain ⟨a, ha, b, hb, rfl⟩ := hmem g hg
    exact mul_mem (mem_sup_left (hPL.le ha)) (mem_sup_right (hQK.le hb))

end Generic

namespace Sec4Setting

variable {G : Type} [Group G] [Finite G] (𝔖 : Sec4Setting G)

theorem not_normal_S₂ : ¬ 𝔖.S₂.Normal :=
  not_normal_of_isDihNonab 𝔖.decomp.dih₂ 𝔖.fusion.conj₂ 𝔖.hz₂.1 𝔖.hz₂.2.1 𝔖.hz₂.2.2

theorem not_normal_S₁_of_isKleinFour
    (h47 : ∀ {A : Subgroup G}, A ≤ 𝔖.S → IsE16 A →
      QuotIs (𝔖.M₀ A) (O (𝔖.M A)) (fun L _ => IsL2OrA7 L 7) ∧
      CFSG.ABGLocalTools.IsSylowOf 2 𝔖.S₂ (𝔖.M₀ A) ∧
      𝔖.M A = 𝔖.M₀ A ⊔ (𝔖.M A ⊓ normalizer (A : Set G)) ∧
      𝔖.M A = 𝔖.M₀ A ⊔ (𝔖.M A ⊓ normalizer (𝔖.S₂ : Set G)) ∧
      (∀ x ∈ 𝔖.X A, x ≠ 1 → O2 (C x) = (O2 (𝔖.M A) ⊓ O2 (C x)) ⊔ O (C x)) ∧
      (∀ x ∈ 𝔖.X A, x ≠ 1 → ⁅O2 (C x), O2 (C x)⁆ ⊔ O (C x) =
        (𝔖.M₀ A ⊓ ⁅O2 (C x), O2 (C x)⁆) ⊔ O (C x)))
    (hV : IsKleinFour 𝔖.S₁) : ¬ 𝔖.S₁.Normal := by
  intro hn
  have hd := 𝔖.decomp
  obtain ⟨V, hV₂⟩ := hd.isDih₂.exists_four
  have hAS : 𝔖.S₁ ⊔ V ≤ 𝔖.S := sup_le hd.le_left (hV₂.1.trans hd.le_right)
  have hA : IsE16 (𝔖.S₁ ⊔ V) := hd.isE16_sup (IsDih.isFourIn_self_of_isKleinFour hV) hV₂
  have hX : 𝔖.X (𝔖.S₁ ⊔ V) = 𝔖.S₁ := inf_eq_right.mpr le_sup_left
  have hMn : (𝔖.M (𝔖.S₁ ⊔ V)).Normal := by
    have := hn
    change (centralizer (𝔖.X (𝔖.S₁ ⊔ V) : Set G)).Normal
    rw [hX]
    exact normal_centralizer
  have hOM : O (𝔖.M (𝔖.S₁ ⊔ V)) = ⊥ := O_eq_bot_of_normal 𝔖.mc.hyp.1 hMn
  have hM₀n : (𝔖.M₀ (𝔖.S₁ ⊔ V)).Normal := by
    have := normal_O2_of_normal hMn
    have := normal_O_of_normal hMn
    change (⁅O2 (𝔖.M (𝔖.S₁ ⊔ V)), O2 (𝔖.M (𝔖.S₁ ⊔ V))⁆ ⊔ O (𝔖.M (𝔖.S₁ ⊔ V))).Normal
    infer_instance
  obtain ⟨⟨L, _, f, hf, hker, hL⟩, hsyl, -⟩ := h47 hAS hA
  have hinj : Function.Injective f := by
    rw [← MonoidHom.ker_eq_bot_iff, hker, hOM, bot_subgroupOf]
  have h7 : IsL2OrA7 (𝔖.M₀ (𝔖.S₁ ⊔ V)) 7 :=
    isL2OrA7_of_mulEquiv (MulEquiv.ofBijective f ⟨hinj, hf⟩) hL
  have hM₀M : 𝔖.M₀ (𝔖.S₁ ⊔ V) ≤ 𝔖.M (𝔖.S₁ ⊔ V) :=
    sup_le (G4c.commutator_le_of_le (G4c.O2_le _) (G4c.O2_le _)) (G4c.O_le _)
  refine 𝔖.mc.not_concl ⟨𝔖.S₁, 𝔖.M₀ (𝔖.S₁ ⊔ V), hn, hM₀n, ?_, ?_, Or.inr (Or.inr hV),
    h7.isAStarFactor (by norm_num)⟩
  · refine le_bot_iff.mp (le_trans ?_ (inf_centralizer_eq_bot_of_isL2OrA7 _ h7).le)
    refine le_inf inf_le_right fun x hx => mem_centralizer_iff.mpr fun m hm => ?_
    have hxX : x ∈ 𝔖.X (𝔖.S₁ ⊔ V) := mem_inf.mpr ⟨mem_sup_left (mem_inf.mp hx).1, (mem_inf.mp hx).1⟩
    exact (mem_centralizer_iff.mp (hM₀M hm) x hxX).symm
  · exact odd_index_of_sylow_le 𝔖.S (hd.sup_eq ▸ sup_le_sup_left hsyl.le _)

theorem not_normal_S₁
    (h47 : ∀ {A : Subgroup G}, A ≤ 𝔖.S → IsE16 A →
      QuotIs (𝔖.M₀ A) (O (𝔖.M A)) (fun L _ => IsL2OrA7 L 7) ∧
      CFSG.ABGLocalTools.IsSylowOf 2 𝔖.S₂ (𝔖.M₀ A) ∧
      𝔖.M A = 𝔖.M₀ A ⊔ (𝔖.M A ⊓ normalizer (A : Set G)) ∧
      𝔖.M A = 𝔖.M₀ A ⊔ (𝔖.M A ⊓ normalizer (𝔖.S₂ : Set G)) ∧
      (∀ x ∈ 𝔖.X A, x ≠ 1 → O2 (C x) = (O2 (𝔖.M A) ⊓ O2 (C x)) ⊔ O (C x)) ∧
      (∀ x ∈ 𝔖.X A, x ≠ 1 → ⁅O2 (C x), O2 (C x)⁆ ⊔ O (C x) =
        (𝔖.M₀ A ⊓ ⁅O2 (C x), O2 (C x)⁆) ⊔ O (C x))) :
    ¬ 𝔖.S₁.Normal := by
  rcases 𝔖.decomp.dih₁.isKleinFour_or_isDihNonab with hV | hN
  · exact 𝔖.not_normal_S₁_of_isKleinFour h47 hV
  · exact not_normal_of_isDihNonab hN 𝔖.fusion.conj₁ 𝔖.hz₁.1 𝔖.hz₁.2.1 𝔖.hz₁.2.2

theorem prop_4_17_of
    (h47 : ∀ {A : Subgroup G}, A ≤ 𝔖.S → IsE16 A →
      QuotIs (𝔖.M₀ A) (O (𝔖.M A)) (fun L _ => IsL2OrA7 L 7) ∧
      CFSG.ABGLocalTools.IsSylowOf 2 𝔖.S₂ (𝔖.M₀ A) ∧
      𝔖.M A = 𝔖.M₀ A ⊔ (𝔖.M A ⊓ normalizer (A : Set G)) ∧
      𝔖.M A = 𝔖.M₀ A ⊔ (𝔖.M A ⊓ normalizer (𝔖.S₂ : Set G)) ∧
      (∀ x ∈ 𝔖.X A, x ≠ 1 → O2 (C x) = (O2 (𝔖.M A) ⊓ O2 (C x)) ⊔ O (C x)) ∧
      (∀ x ∈ 𝔖.X A, x ≠ 1 → ⁅O2 (C x), O2 (C x)⁆ ⊔ O (C x) =
        (𝔖.M₀ A ⊓ ⁅O2 (C x), O2 (C x)⁆) ⊔ O (C x)))
    (H : Subgroup G) (hH : H.Normal) :
    ¬ CFSG.ABGLocalTools.IsSylowOf 2 𝔖.S₁ H ∧ ¬ CFSG.ABGLocalTools.IsSylowOf 2 𝔖.S₂ H := by
  have hd := 𝔖.decomp
  have hS : ∀ x ∈ (𝔖.S : Subgroup G), x ∈ 𝔖.S₁ ⊔ 𝔖.S₂ := fun x hx => hd.sup_eq ▸ hx
  have hn₁ := 𝔖.not_normal_S₁ h47
  have hn₂ := 𝔖.not_normal_S₂
  refine ⟨not_isSylowOf_of_normal 𝔖.mc.hyp.1 𝔖.mc.not_concl 𝔖.S (fun g hg => hd.mem_iff.mp hg)
      hd.le_left hd.le_right hd.inf_eq hd.dih₁ hd.isDih₂ 𝔖.fusion.conj₁ 𝔖.fusion.conj₂
      (fun x hx y hy hx2 hxy => (𝔖.fusion.separate x (hS x hx) y (hS y hy) hx2 hxy).2)
      hn₁ hn₂ H hH,
    not_isSylowOf_of_normal 𝔖.mc.hyp.1 𝔖.mc.not_concl 𝔖.S (fun g hg => ?_)
      hd.le_right hd.le_left (inf_comm 𝔖.S₂ 𝔖.S₁ ▸ hd.inf_eq) hd.isDih₂ hd.dih₁
      𝔖.fusion.conj₂ 𝔖.fusion.conj₁
      (fun x hx y hy hx2 hxy => (𝔖.fusion.separate x (hS x hx) y (hS y hy) hx2 hxy).1)
      hn₂ hn₁ H hH⟩
  obtain ⟨a, ha, b, hb, rfl⟩ := hd.mem_iff.mp hg
  exact ⟨b, hb, a, ha, hd.comm ha hb⟩

end Sec4Setting

end CFSG.GH72
