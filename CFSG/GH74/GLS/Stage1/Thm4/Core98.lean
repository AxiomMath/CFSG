module

public import CFSG.GH74.GLS.Stage1.Thm4.Closed
public import CFSG.GH74.GLS.Stage1.Thm4.Pure

public section

namespace CFSG.GH74.GLS.Stage1.Thm4

open Subgroup CFSG CFSG.GH74.GLS CFSG.GH74.GLS.Stage1.Thm3

section Core

variable {C : Type} [Group C] [Finite C] {N K S : Subgroup C}

omit [Finite C] in
theorem index_map_mk [N.Normal] (K : Subgroup C) :
    (K.map (QuotientGroup.mk' N)).index = (K ⊔ N).index := by
  rw [Subgroup.index_map, QuotientGroup.ker_mk',
    MonoidHom.range_eq_top_of_surjective _ (QuotientGroup.mk'_surjective N), Subgroup.index_top, mul_one]

theorem sylow_map_mk [N.Normal] (hS : CFSG.ABGLocalTools.IsSylowOf 2 S ⊤) :
    CFSG.ABGLocalTools.IsSylowOf 2 (S.map (QuotientGroup.mk' N)) ⊤ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [CFSG.ABGLocalTools.isSylowOf_iff] at hS ⊢
  refine ⟨le_top, hS.2.1.map _, ?_⟩
  rw [Subgroup.relIndex_top_right, index_map_mk]
  have h1 : ¬ 2 ∣ S.index := by
    have := hS.2.2
    rwa [Subgroup.relIndex_top_right] at this
  intro h2
  exact h1 (h2.trans (Subgroup.index_dvd_of_le le_sup_left))

theorem exists_conj_mem_sylow (hS : CFSG.ABGLocalTools.IsSylowOf 2 S ⊤) {x : C}
    (hx : IsPGroup 2 ↥(zpowers x)) : ∃ g : C, g * x * g⁻¹ ∈ S := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hS' : Sec4.M.Syl2In S ⊤ := (CFSG.ABGLocalTools.isSylowOf_iff).1 hS
  obtain ⟨P, hP, hxP⟩ := Sec4.M.exists_syl2In_ge hx (le_top)
  obtain ⟨c, -, hc⟩ := hS'.exists_conj hP
  refine ⟨c, ?_⟩
  have : x ∈ P := hxP (Subgroup.mem_zpowers x)
  rw [hc, Sec4.M.mem_cj] at this
  exact this

omit [Finite C] in
theorem orderOf_conj_eq' (g x : C) : orderOf (g * x * g⁻¹) = orderOf x := by
  have := orderOf_injective (MulAut.conj g).toMonoidHom (MulAut.conj g).injective x
  simpa only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] using this

theorem core_S_le (hA : IVK_5_1_index) (hD : IVK_5_1d) [N.Normal] [K.Normal] {n : ℕ}
    (hyp : Hyp5B (C ⧸ N) (K.map (QuotientGroup.mk' N)) n) (hN : Odd (Nat.card N))
    (hS : CFSG.ABGLocalTools.IsSylowOf 2 S ⊤) (hinv : ∀ u ∈ S, orderOf u = 2 → u ∈ K) :
    S ≤ K ∧ K ⊔ N = ⊤ := by
  have hle := hA _ _ n hyp
  rw [index_map_mk] at hle
  have hone : (K ⊔ N).index = 1 := by
    by_contra hne
    have hpos : (K ⊔ N).index ≠ 0 := Subgroup.index_ne_zero_of_finite
    have h2 : (K ⊔ N).index = 2 := by omega
    obtain ⟨h, hhK, hh2⟩ := hD _ _ n hyp (by rw [index_map_mk, h2])
    obtain ⟨u, hu2, huh⟩ := exists_involution_lift (QuotientGroup.mk' N)
      (QuotientGroup.mk'_surjective N) (by rw [QuotientGroup.ker_mk']; exact hN) hh2
    have hupg : IsPGroup 2 ↥(zpowers u) :=
      IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hu2]; norm_num)
    obtain ⟨g, hg⟩ := exists_conj_mem_sylow hS hupg
    have hord : orderOf (g * u * g⁻¹) = 2 := by rw [orderOf_conj_eq']; exact hu2
    have hK' := hinv _ hg hord
    have hmem : (QuotientGroup.mk' N) (g * u * g⁻¹) ∈ K.map (QuotientGroup.mk' N) :=
      Subgroup.mem_map_of_mem _ hK'
    rw [map_mul, map_mul, huh, map_inv] at hmem
    have := (hyp.normal).conj_mem _ hmem ((QuotientGroup.mk' N) g)⁻¹
    apply hhK
    simpa [mul_assoc] using this
  have htop : K ⊔ N = ⊤ := Subgroup.index_eq_one.1 hone
  refine ⟨fun s hs => ?_, htop⟩
  obtain ⟨m, hm⟩ := hS.isPGroup ⟨s, hs⟩
  have hm' : s ^ (2 ^ m) = 1 := by
    have := congrArg Subtype.val hm
    simpa using this
  exact mem_of_mem_sup_odd hN hm' (htop ▸ Subgroup.mem_top s)

theorem core_center_two [N.Normal] {n : ℕ} (hyp : Hyp5B (C ⧸ N) (K.map (QuotientGroup.mk' N)) n)
    {zc : C} (hzc : zc ∈ K) (hzK : ∀ k ∈ K, k * zc = zc * k) (hz1 : QuotientGroup.mk' N zc ≠ 1) :
    ∀ y ∈ K.map (QuotientGroup.mk' N), (∀ k ∈ K.map (QuotientGroup.mk' N), k * y = y * k) →
      y = 1 ∨ y = QuotientGroup.mk' N zc := by
  intro y hy hyc
  have hcard : Nat.card (center ↥(K.map (QuotientGroup.mk' N))) = 2 := hyp.cover.2.1
  let a : center ↥(K.map (QuotientGroup.mk' N)) :=
    ⟨⟨y, hy⟩, Subgroup.mem_center_iff.2 fun g => Subtype.ext (hyc g.1 g.2)⟩
  let b : center ↥(K.map (QuotientGroup.mk' N)) :=
    ⟨⟨QuotientGroup.mk' N zc, Subgroup.mem_map_of_mem _ hzc⟩, Subgroup.mem_center_iff.2 fun g => by
      obtain ⟨g, hg⟩ := g
      obtain ⟨k, hk, rfl⟩ := hg
      apply Subtype.ext
      show QuotientGroup.mk' N k * QuotientGroup.mk' N zc = QuotientGroup.mk' N zc * QuotientGroup.mk' N k
      rw [← map_mul, ← map_mul, hzK k hk]⟩
  have hb : b ≠ 1 := by
    intro h
    apply hz1
    have := congrArg (fun x : center ↥(K.map (QuotientGroup.mk' N)) => ((x : ↥(K.map (QuotientGroup.mk' N))) : C ⧸ N)) h
    simpa [b] using this
  obtain ⟨_, -, hy'⟩ := (Nat.card_eq_two_iff' (1 : center ↥(K.map (QuotientGroup.mk' N)))).1 hcard
  by_cases ha : a = 1
  · left
    have := congrArg (fun x : center ↥(K.map (QuotientGroup.mk' N)) => ((x : ↥(K.map (QuotientGroup.mk' N))) : C ⧸ N)) ha
    simpa [a] using this
  · right
    have hab : a = b := (hy' a ha).trans (hy' b hb).symm
    have := congrArg (fun x : center ↥(K.map (QuotientGroup.mk' N)) => ((x : ↥(K.map (QuotientGroup.mk' N))) : C ⧸ N)) hab
    simpa [a, b] using this

theorem core_center (hB : IVK_5_1g) [N.Normal] [K.Normal] {n : ℕ}
    (hyp : Hyp5B (C ⧸ N) (K.map (QuotientGroup.mk' N)) n) (hN : Odd (Nat.card N))
    (hS : CFSG.ABGLocalTools.IsSylowOf 2 S ⊤) {zc : C} (hzc : zc ∈ K) (hzK : ∀ k ∈ K, k * zc = zc * k)
    (hz1 : QuotientGroup.mk' N zc ≠ 1) :
    ∀ w ∈ S, (∀ s ∈ S, s * w = w * s) → orderOf w = 2 →
      QuotientGroup.mk' N w = QuotientGroup.mk' N zc := by
  intro w hwS hwc hw2
  have hT := sylow_map_mk (N := N) hS
  have hB' := hB _ _ n hyp _ hT (QuotientGroup.mk' N w) (Subgroup.mem_map_of_mem _ hwS) (by
    rintro _ ⟨s, hs, rfl⟩
    rw [← map_mul, ← map_mul, hwc s hs])
  have hwne : QuotientGroup.mk' N w ≠ 1 := by
    intro h1
    have hwN : w ∈ N := (QuotientGroup.eq_one_iff w).1 h1
    have : orderOf w ∣ Nat.card N := by
      have := orderOf_dvd_natCard (⟨w, hwN⟩ : N)
      rwa [Subgroup.orderOf_mk] at this
    rw [hw2] at this
    exact (Nat.not_even_iff_odd.2 hN) (even_iff_two_dvd.2 this)
  have hcard : Nat.card (center ↥(K.map (QuotientGroup.mk' N))) = 2 := hyp.cover.2.1
  let a : center ↥(K.map (QuotientGroup.mk' N)) :=
    ⟨⟨QuotientGroup.mk' N w, hB'.1⟩, Subgroup.mem_center_iff.2 fun g =>
      Subtype.ext (hB'.2 g.1 g.2)⟩
  let b : center ↥(K.map (QuotientGroup.mk' N)) :=
    ⟨⟨QuotientGroup.mk' N zc, Subgroup.mem_map_of_mem _ hzc⟩, Subgroup.mem_center_iff.2 fun g => by
      obtain ⟨g, hg⟩ := g
      obtain ⟨k, hk, rfl⟩ := hg
      apply Subtype.ext
      show QuotientGroup.mk' N k * QuotientGroup.mk' N zc = QuotientGroup.mk' N zc * QuotientGroup.mk' N k
      rw [← map_mul, ← map_mul, hzK k hk]⟩
  have ha : a ≠ 1 := by
    intro h
    apply hwne
    have := congrArg (fun x : center ↥(K.map (QuotientGroup.mk' N)) => ((x : ↥(K.map (QuotientGroup.mk' N))) : C ⧸ N)) h
    simpa [a] using this
  have hb : b ≠ 1 := by
    intro h
    apply hz1
    have := congrArg (fun x : center ↥(K.map (QuotientGroup.mk' N)) => ((x : ↥(K.map (QuotientGroup.mk' N))) : C ⧸ N)) h
    simpa [b] using this
  obtain ⟨y, -, hy⟩ := (Nat.card_eq_two_iff' (1 : center ↥(K.map (QuotientGroup.mk' N)))).1 hcard
  have hab : a = b := (hy a ha).trans (hy b hb).symm
  have := congrArg (fun x : center ↥(K.map (QuotientGroup.mk' N)) => ((x : ↥(K.map (QuotientGroup.mk' N))) : C ⧸ N)) hab
  simpa [a, b] using this

theorem core_P_conj (hC : IVK_5_1f) [N.Normal] {n : ℕ}
    (hyp : Hyp5B (C ⧸ N) (K.map (QuotientGroup.mk' N)) n) (hN : Odd (Nat.card N))
    (hS : CFSG.ABGLocalTools.IsSylowOf 2 S ⊤) {zc : C} (hzc : zc ∈ K)
    (hzK : ∀ k ∈ K, k * zc = zc * k) (hz2 : orderOf zc = 2) {t : C} (htP : t ∈ S ⊓ K)
    (ht2 : orderOf t = 2) (htz : t ≠ zc) (hzS : zc ∈ S) :
    ∀ u ∈ S ⊓ K, orderOf u = 2 → u ≠ zc → IsConj u t := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hSp : IsPGroup 2 ↥S := hS.isPGroup
  have hne1 : ∀ x : C, orderOf x = 2 → QuotientGroup.mk' N x ≠ 1 := by
    intro x hx h1
    have hxN : x ∈ N := (QuotientGroup.eq_one_iff x).1 h1
    have : orderOf x ∣ Nat.card N := by
      have := orderOf_dvd_natCard (⟨x, hxN⟩ : N)
      rwa [Subgroup.orderOf_mk] at this
    rw [hx] at this
    exact (Nat.not_even_iff_odd.2 hN) (even_iff_two_dvd.2 this)
  have hz1 : QuotientGroup.mk' N zc ≠ 1 := hne1 zc hz2
  have hnotz : ∀ x ∈ S ⊓ K, orderOf x = 2 → x ≠ zc →
      QuotientGroup.mk' N x ≠ QuotientGroup.mk' N zc := by
    intro x hx hx2 hxz heq
    apply hxz
    have hmem : x⁻¹ * zc ∈ N := QuotientGroup.eq.1 heq
    have hSx : x⁻¹ * zc ∈ S := mul_mem (inv_mem hx.1) hzS
    have : x⁻¹ * zc ∈ S ⊓ N := ⟨hSx, hmem⟩
    rw [inf_eq_bot_of_odd hSp hN] at this
    have h1 : x⁻¹ * zc = 1 := this
    exact (inv_mul_eq_one.1 h1)
  have hnc : ∀ x ∈ S ⊓ K, orderOf x = 2 → x ≠ zc →
      ¬ ∀ k ∈ K.map (QuotientGroup.mk' N), k * QuotientGroup.mk' N x = QuotientGroup.mk' N x * k := by
    intro x hx hx2 hxz hcomm
    rcases core_center_two hyp hzc hzK hz1 _ (Subgroup.mem_map_of_mem _ hx.2) hcomm with h1 | h1
    · exact hne1 x hx2 h1
    · exact hnotz x hx hx2 hxz h1
  intro u huP hu2 huz
  have hord : ∀ x : C, orderOf x = 2 → (hx : x ∈ K) →
      orderOf (⟨QuotientGroup.mk' N x, Subgroup.mem_map_of_mem _ hx⟩ :
        ↥(K.map (QuotientGroup.mk' N))) = 2 := by
    intro x hx2 hx
    have hsq : (⟨QuotientGroup.mk' N x, Subgroup.mem_map_of_mem _ hx⟩ :
        ↥(K.map (QuotientGroup.mk' N))) ^ 2 = 1 := by
      apply Subtype.ext
      simp only [Subgroup.coe_pow, Subgroup.coe_one]
      rw [← map_pow, ← hx2, pow_orderOf_eq_one, map_one]
    have hne : (⟨QuotientGroup.mk' N x, Subgroup.mem_map_of_mem _ hx⟩ :
        ↥(K.map (QuotientGroup.mk' N))) ≠ 1 := by
      intro h1; exact hne1 x hx2 (congrArg Subtype.val h1)
    exact orderOf_eq_prime hsq hne
  have hcen : ∀ x : C, ∀ hx : x ∈ S ⊓ K, orderOf x = 2 → x ≠ zc →
      (⟨QuotientGroup.mk' N x, Subgroup.mem_map_of_mem _ (inf_le_right (a := S) hx)⟩ :
        ↥(K.map (QuotientGroup.mk' N))) ∉ center ↥(K.map (QuotientGroup.mk' N)) := by
    intro x hx hx2 hxz hmem
    apply hnc x hx hx2 hxz
    intro k hk
    have := Subgroup.mem_center_iff.1 hmem ⟨k, hk⟩
    exact congrArg Subtype.val this
  have hkb := hC ↥(K.map (QuotientGroup.mk' N)) n hyp.cover hyp.n_ge hyp.n_le _ _
    (hord u hu2 huP.2) (hord t ht2 htP.2) (hcen u huP hu2 huz) (hcen t htP ht2 htz)
  obtain ⟨cb, hcb⟩ := isConj_iff.1 hkb
  obtain ⟨k, hkK, hk⟩ := cb.2
  have hu' : orderOf (k * u * k⁻¹) = 2 := by rw [orderOf_conj_eq']; exact hu2
  have himg : QuotientGroup.mk' N (k * u * k⁻¹) = QuotientGroup.mk' N t := by
    have := congrArg Subtype.val hcb
    simp only [Subgroup.coe_mul, Subgroup.coe_inv] at this
    rw [map_mul, map_mul, map_inv, hk]
    exact this
  have hconj : IsConj (k * u * k⁻¹) t :=
    isConj_of_mem_coset hN hu' ht2 (QuotientGroup.eq.1 himg)
  exact (isConj_iff.2 ⟨k, rfl⟩).trans hconj

end Core

end CFSG.GH74.GLS.Stage1.Thm4
