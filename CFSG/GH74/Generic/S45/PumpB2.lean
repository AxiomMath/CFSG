module

public import CFSG.GH74.Generic.S45.Final

public section

namespace CFSG.GH74.Generic.S45

open CFSG CFSG.GH74 CFSG.GH74.Generic CFSG.ABGLocalTools Subgroup

section B2

theorem eq_one_of_central_of_simple {W : Type} [Group W] (hs : IsSimpleGroup W)
    (hn : ∃ a b : W, a * b ≠ b * a) {z : W} (hz : ∀ w : W, w * z = z * w) : z = 1 := by
  by_contra hz1
  have := hs
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center W) with hbot | htop
  · have : z ∈ Subgroup.center W := Subgroup.mem_center_iff.2 hz
    rw [hbot] at this
    exact hz1 (Subgroup.mem_bot.1 this)
  · obtain ⟨a, b, hab⟩ := hn
    apply hab
    have : a ∈ Subgroup.center W := by rw [htop]; trivial
    exact (Subgroup.mem_center_iff.1 this b).symm

theorem exists_mem_normalizer_not_centralizer {W : Type} [Group W] [Finite W] (hs : IsSimpleGroup W)
    (hn : ∃ a b : W, a * b ≠ b * a) (Q : Sylow 2 W)
    (hQ : ∀ a ∈ (Q : Subgroup W), ∀ b ∈ (Q : Subgroup W), a * b = b * a) :
    ∃ n ∈ normalizer ((Q : Subgroup W) : Set W), ∃ q ∈ (Q : Subgroup W), n * q ≠ q * n := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_contra hcon
  push Not at hcon
  have hle : normalizer ((Q : Subgroup W) : Set W) ≤ centralizer ((Q : Subgroup W) : Set W) := by
    intro n hn'
    rw [Subgroup.mem_centralizer_iff]
    intro q hq
    exact (hcon n hn' q hq).symm
  obtain ⟨K', hK'n, hK'odd, hK'idx, -⟩ := CFSG.GroupTheory.burnside_normal_complement Q hle
  have hall : ∀ a b : W, a * b = b * a := by
    have := hs
    have := hK'n
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal K' with hbot | htop
    ·
      rw [hbot, Subgroup.index_bot] at hK'idx
      have hQtop : (Q : Subgroup W) = ⊤ := Subgroup.eq_top_of_card_eq _ hK'idx.symm
      intro a b
      exact hQ a (by rw [hQtop]; trivial) b (by rw [hQtop]; trivial)
    ·
      rw [htop, Subgroup.card_top] at hK'odd
      have hodd : Odd (Nat.card W) := Nat.odd_iff.2 (by omega)
      exact (IsSimpleGroup.comm_iff_isSolvable (G := W)).2 (CFSG.FeitThompson.isSolvable_of_odd_natCard W hodd)
  obtain ⟨a, b, hab⟩ := hn
  exact hab (hall a b)

variable {G : Type} [Group G] [Finite G] {x : G} {K : Subgroup (CentralizerBar x)} {T : Subgroup G}

theorem three_le_card_of_distinct {S : Subgroup G} {a b c : G} (ha : a ∈ S) (hb : b ∈ S) (hc : c ∈ S)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) : 3 ≤ Nat.card S := by
  classical
  have h1 : ({a, b, c} : Finset G).card = 3 := by
    rw [Finset.card_insert_of_notMem (by simp [hab, hac]), Finset.card_pair hbc]
  have h2 : ((({a, b, c} : Finset G)) : Set G) ⊆ (S : Set G) := by
    intro g hg
    simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
      Set.mem_singleton_iff] at hg
    rcases hg with rfl | rfl | rfl <;> assumption
  have h3 := Set.ncard_le_ncard h2 (Set.toFinite _)
  rw [Set.ncard_coe_finset, h1] at h3
  have : (S : Set G).ncard = Nat.card S := (Nat.card_coe_set_eq (S : Set G)).symm
  omega

theorem four_le_of_dvd_sixteen : ∀ c : ℕ, c ∣ 16 → 3 ≤ c → 4 ≤ c := by
  intro c h2 h3
  have hle : c ≤ 16 := Nat.le_of_dvd (by norm_num) h2
  interval_cases c <;> omega

theorem S45Conf.exists_normalizing_in_W (h : S45Conf x K T) {v : G} (hvT : v ∈ T) (hvK : v ∈ Pre x K)
    (hv1 : v ≠ 1) (W : Subgroup G)
    (hWY : W ≤ centralizer ({x} : Set G) ⊓ centralizer ({v} : Set G))
    (hWn : (W.subgroupOf (centralizer ({x} : Set G) ⊓ centralizer ({v} : Set G))).Normal)
    (hWs : IsSimpleGroup ↥W) (hWnab : ∃ a b : ↥W, a * b ≠ b * a) :
    4 ≤ Nat.card ↥(T ⊓ W) ∧ ∃ (c : G) (_ : c ∈ W) (hcN : c ∈ normalizer (T : Set G)),
      T.normalizerMonoidHom ⟨c, hcN⟩ ≠ 1 := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set Y : Subgroup G := centralizer ({x} : Set G) ⊓ centralizer ({v} : Set G) with hY
  have hTY : T ≤ Y := by
    intro t ht
    refine Subgroup.mem_inf.2 ⟨?_, ?_⟩
    · rw [Subgroup.mem_centralizer_singleton_iff]
      exact h.comm t ht x h.x_mem
    · rw [Subgroup.mem_centralizer_singleton_iff]
      exact h.comm t ht v hvT
  have hTsyl : IsSylowOf 2 T Y := by
    rw [isSylowOf_iff]
    obtain ⟨-, hp, hndvd⟩ := (isSylowOf_iff).1 h.sylow
    refine ⟨hTY, hp, ?_⟩
    intro hdvd
    apply hndvd
    exact hdvd.trans (Dvd.intro _ (Subgroup.relIndex_mul_relIndex T Y (centralizer ({x} : Set G))
      hTY (inf_le_left : Y ≤ centralizer ({x} : Set G))))
  have hYW : Y ≤ normalizer (W : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hWY).1 hWn
  have hEsyl : IsSylowOf 2 (T ⊓ W) W := hTsyl.inf_of_le_normalizer hWY hYW
  obtain ⟨Q, hQ⟩ := hEsyl.exists_sylow_eq_subgroupOf
  have hQmem : ∀ q : ↥W, q ∈ (Q : Subgroup ↥W) ↔ (q : G) ∈ T := by
    intro q
    rw [hQ, Subgroup.mem_subgroupOf]
    exact ⟨fun hq => hq.1, fun hq => ⟨hq, q.2⟩⟩
  have hQcomm : ∀ a ∈ (Q : Subgroup ↥W), ∀ b ∈ (Q : Subgroup ↥W), a * b = b * a := by
    intro a ha b hb
    apply Subtype.ext
    exact h.comm _ ((hQmem a).1 ha) _ ((hQmem b).1 hb)
  obtain ⟨n, hn, q, hq, hnq⟩ := exists_mem_normalizer_not_centralizer hWs hWnab Q hQcomm
  have hnE : ∀ n' ∈ normalizer ((Q : Subgroup ↥W) : Set ↥W), ∀ e : ↥W, (e : G) ∈ T →
      ((n' * e * n'⁻¹ : ↥W) : G) ∈ T := by
    intro n' hn' e he
    exact (hQmem _).1 ((Subgroup.mem_normalizer_iff.1 hn' e).1 ((hQmem e).2 he))
  set ZT : Subgroup G := T ⊓ centralizer (W : Set G) with hZT
  set E : Subgroup G := T ⊓ W with hE
  have hxnot : x ∉ Pre x K := (h.fusion x h.x_mem).1 ⟨1, by simp⟩
  have hxZ : x ∈ ZT := by
    refine Subgroup.mem_inf.2 ⟨h.x_mem, ?_⟩
    rw [Subgroup.mem_centralizer_iff]
    intro w hw
    exact Subgroup.mem_centralizer_singleton_iff.1 (Subgroup.mem_inf.1 (hWY hw)).1
  have hvZ : v ∈ ZT := by
    refine Subgroup.mem_inf.2 ⟨hvT, ?_⟩
    rw [Subgroup.mem_centralizer_iff]
    intro w hw
    exact Subgroup.mem_centralizer_singleton_iff.1 (Subgroup.mem_inf.1 (hWY hw)).2
  have hx1 : x ≠ 1 := fun h1 => hxnot (h1 ▸ one_mem (Pre x K))
  have hxv : x ≠ v := fun h1 => hxnot (h1 ▸ hvK)
  have hZc3 : 3 ≤ Nat.card ↥ZT := three_le_card_of_distinct (one_mem ZT) hxZ hvZ hx1.symm hv1.symm hxv
  have hT16 : Nat.card ↥T = 16 := h.card
  have hZdvd : Nat.card ↥ZT ∣ 16 := hT16 ▸ Subgroup.card_dvd_of_le (inf_le_left : ZT ≤ T)
  have hZc : 4 ≤ Nat.card ↥ZT := four_le_of_dvd_sixteen _ hZdvd hZc3
  have hq1 : q ≠ 1 := by
    rintro rfl
    exact hnq (by simp)
  have hqE : (q : G) ∈ E := ⟨(hQmem q).1 hq, q.2⟩
  have hnqE : ((n * q * n⁻¹ : ↥W) : G) ∈ E := ⟨hnE n hn q ((hQmem q).1 hq), (n * q * n⁻¹ : ↥W).2⟩
  have hne1 : ((n * q * n⁻¹ : ↥W) : G) ≠ 1 := by
    intro h1
    have : n * q * n⁻¹ = 1 := Subtype.ext h1
    apply hq1
    have h2 : q = n⁻¹ * (n * q * n⁻¹) * n := by group
    rw [h2, this]
    group
  have hqne : (q : G) ≠ ((n * q * n⁻¹ : ↥W) : G) := by
    intro h1
    apply hnq
    have h2 : q = n * q * n⁻¹ := Subtype.ext h1
    calc n * q = n * q * n⁻¹ * n := by group
      _ = q * n := by rw [← h2]
  have hq1' : (q : G) ≠ 1 := fun h1 => hq1 (Subtype.ext h1)
  have hEc3 : 3 ≤ Nat.card ↥E :=
    three_le_card_of_distinct (one_mem E) hqE hnqE hq1'.symm hne1.symm hqne
  have hEdvd : Nat.card ↥E ∣ 16 := hT16 ▸ Subgroup.card_dvd_of_le (inf_le_left : E ≤ T)
  have hEc : 4 ≤ Nat.card ↥E := four_le_of_dvd_sixteen _ hEdvd hEc3
  have hZE : ∀ u ∈ ZT, u ∈ E → u = 1 := by
    intro u hu hE'
    have : (⟨u, hE'.2⟩ : ↥W) = 1 := by
      apply eq_one_of_central_of_simple hWs hWnab
      intro w
      apply Subtype.ext
      exact (Subgroup.mem_centralizer_iff.1 hu.2) (w : G) w.2
    exact congrArg Subtype.val this
  let Φ : ↥ZT × ↥E → ↥T := fun p => ⟨(p.1 : G) * (p.2 : G), mul_mem p.1.2.1 p.2.2.1⟩
  have hinj : Function.Injective Φ := by
    rintro ⟨⟨z, hz⟩, ⟨e, he⟩⟩ ⟨⟨z', hz'⟩, ⟨e', he'⟩⟩ hΦ
    have h1 : z * e = z' * e' := congrArg Subtype.val hΦ
    have hu : z'⁻¹ * z = e' * e⁻¹ := by
      calc z'⁻¹ * z = z'⁻¹ * (z * e) * e⁻¹ := by group
        _ = z'⁻¹ * (z' * e') * e⁻¹ := by rw [h1]
        _ = e' * e⁻¹ := by group
    have hu1 : z'⁻¹ * z = 1 := hZE _ (mul_mem (inv_mem hz') hz) (by rw [hu]; exact mul_mem he' (inv_mem he))
    have hzz : z = z' := (inv_mul_eq_one.1 hu1).symm
    have hee : e = e' := by
      rw [hu1] at hu
      have : e' * e⁻¹ = 1 := hu.symm
      exact (mul_inv_eq_one.1 this).symm
    subst hzz
    subst hee
    rfl
  have hbij : Function.Bijective Φ := by
    apply hinj.bijective_of_nat_card_le
    rw [hT16, Nat.card_prod]
    exact (Nat.mul_le_mul hZc hEc : 4 * 4 ≤ _)
  have hconj : ∀ n' : ↥W, n' ∈ normalizer ((Q : Subgroup ↥W) : Set ↥W) → ∀ t ∈ T,
      (n' : G) * t * (n' : G)⁻¹ ∈ T := by
    intro n' hn' t ht
    obtain ⟨⟨z, e⟩, hze⟩ := hbij.2 ⟨t, ht⟩
    have ht' : t = (z : G) * (e : G) := (congrArg Subtype.val hze).symm
    rw [ht']
    have hz : (n' : G) * (z : G) = (z : G) * (n' : G) :=
      (Subgroup.mem_centralizer_iff.1 z.2.2) (n' : G) n'.2
    have h1 : (n' : G) * ((z : G) * (e : G)) * (n' : G)⁻¹ =
        (z : G) * ((n' : G) * (e : G) * (n' : G)⁻¹) := by
      calc (n' : G) * ((z : G) * (e : G)) * (n' : G)⁻¹
          = ((n' : G) * (z : G)) * (e : G) * (n' : G)⁻¹ := by group
        _ = ((z : G) * (n' : G)) * (e : G) * (n' : G)⁻¹ := by rw [hz]
        _ = (z : G) * ((n' : G) * (e : G) * (n' : G)⁻¹) := by group
    rw [h1]
    have he : (e : G) ∈ T ⊓ W := e.2
    have h3 := hnE n' hn' ⟨(e : G), he.2⟩ he.1
    exact mul_mem z.2.1 (by simpa using h3)
  have hcN : (n : G) ∈ normalizer (T : Set G) := by
    rw [Subgroup.mem_normalizer_iff]
    intro t
    constructor
    · exact hconj n hn t
    · intro ht
      have h3 := hconj (n⁻¹) (inv_mem hn) _ ht
      have h2 : ((n⁻¹ : ↥W) : G) * ((n : G) * t * (n : G)⁻¹) * ((n⁻¹ : ↥W) : G)⁻¹ = t := by
        simp only [Subgroup.coe_inv]
        group
      rwa [h2] at h3
  refine ⟨hEc, (n : G), n.2, hcN, ?_⟩
  intro h1
  apply hnq
  have h2 := congrArg (fun f : MulAut ↥T => ((f ⟨(q : G), (hQmem q).1 hq⟩ : ↥T) : G)) h1
  simp only [MulAut.one_apply] at h2
  have h3 : (n : G) * (q : G) * (n : G)⁻¹ = (q : G) := h2
  apply Subtype.ext
  show (n : G) * (q : G) = (q : G) * (n : G)
  rw [mul_inv_eq_iff_eq_mul] at h3
  exact h3

end B2

end CFSG.GH74.Generic.S45
