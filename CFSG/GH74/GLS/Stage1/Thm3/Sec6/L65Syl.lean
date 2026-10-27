module

public import CFSG.GH74.GLS.Stage1.Thm3.Sec6.L65Ext4

public section

namespace CFSG.GH74.GLS.Stage1.Thm3.Sec6.L65

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.TwoThin CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.GH74.GLS.Stage1.Thm3.Sec4 CFSG.GH74.GLS.Stage1.Thm3.Sec5 CFSG.GH74.GLS.Stage1.Thm2.Recip

theorem sylow_map_of_odd_kernel {Y X : Type} [Group Y] [Finite Y] [Group X] (π : Y →* X)
    (hπ : Function.Surjective π) (hodd : Odd (Nat.card π.ker)) {TY : Subgroup Y}
    (hTY : IsPGroup 2 ↥TY) (hidx : ¬ 2 ∣ TY.index) :
    ∃ e : ↥TY ≃* ↥(TY.map π), (∀ y : ↥TY, ((e y : ↥(TY.map π)) : X) = π (y : Y)) ∧
      IsPGroup 2 ↥(TY.map π) ∧ ¬ 2 ∣ (TY.map π).index := by
  let ρ : ↥TY →* ↥(TY.map π) :=
    (π.comp TY.subtype).codRestrict _ (fun y => ⟨(y : Y), y.2, rfl⟩)
  have hρs : Function.Surjective ρ := by
    rintro ⟨_, ⟨y, hy, rfl⟩⟩
    exact ⟨⟨y, hy⟩, rfl⟩
  have hρi : Function.Injective ρ := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro y hy
    rw [MonoidHom.mem_ker] at hy
    have h1 : π (y : Y) = 1 := congrArg Subtype.val hy
    have h2 : ((y : ↥TY) : Y) ∈ π.ker := h1
    have hd : orderOf ((y : ↥TY) : Y) ∣ Nat.card π.ker := Subgroup.orderOf_dvd_natCard _ h2
    obtain ⟨n, hn⟩ := (IsPGroup.iff_orderOf).1 hTY y
    have hy' : orderOf ((y : ↥TY) : Y) = orderOf y := Subgroup.orderOf_coe y
    rw [hy', hn] at hd
    have hn0 : n = 0 := by
      by_contra hn0
      have h2d : 2 ∣ 2 ^ n := dvd_pow_self 2 hn0
      exact (Nat.not_even_iff_odd.2 hodd) (even_iff_two_dvd.2 (h2d.trans hd))
    rw [hn0, pow_zero, orderOf_eq_one_iff] at hn
    exact hn
  let e : ↥TY ≃* ↥(TY.map π) := MulEquiv.ofBijective ρ ⟨hρi, hρs⟩
  refine ⟨e, fun y => rfl, hTY.map π, ?_⟩
  have hc1 := Subgroup.card_mul_index TY
  have hc2 := Subgroup.card_mul_index (TY.map π)
  have hc3 := Subgroup.card_ker_mul_card_of_surjective hπ
  have hcard : Nat.card ↥(TY.map π) = Nat.card ↥TY := (Nat.card_congr e.toEquiv).symm
  have hpos : 0 < Nat.card ↥TY := Nat.card_pos
  have hkey : TY.index = (TY.map π).index * Nat.card π.ker := by
    have h4 : Nat.card ↥TY * TY.index = Nat.card ↥TY * ((TY.map π).index * Nat.card π.ker) := by
      rw [hc1, ← hc3, ← hc2, hcard]
      ring
    exact Nat.eq_of_mul_eq_mul_left hpos h4
  intro hdvd
  exact hidx (hkey ▸ Dvd.dvd.mul_right hdvd _)

namespace Cfg65

variable {G : Type} [Group G] [Finite G] {z : G} {S K₁ K₂ : Subgroup G} {t : G}

variable (h : Cfg65 G z S K₁ K₂ t) {a b : G} (hAB : AB65 S K₁ a b)

include h hAB

theorem exists_T (hII : II4_4_4_center) (h4hij : IVK_1_4hij_outer)
    (hrec : Bg.B_reciprocity) :
    ∃ T : Subgroup (barQ ↥(centralizer ({t * z} : Set G))), M.Syl2In T ⊤ ∧
      Nonempty (↥(S ⊓ centralizer ({uElt t a} : Set G)) ≃* ↥T) ∧
      ¬ 2 ^ 8 ∣ Nat.card (barQ ↥(centralizer ({t * z} : Set G))) := by
  set u' := uElt t a with hu'
  have hu2 : orderOf u' = 2 :=
    orderOf_eq_prime (by rw [sq]; exact h.u_sq hAB hII) (h.u_ne_one hAB hII)
  have hconj : IsConj (t * z) u' := h.t_fus u' (h.u_mem_P hAB hII) hu2 (h.u_ne_z hAB hII)
  obtain ⟨g, hg⟩ := isConj_iff.1 hconj
  obtain ⟨hsyl, hcardS⟩ := h.u_extremal hAB hII h4hij hrec
  have hC₀2 : IsPGroup 2 ↥(S ⊓ centralizer ({u'} : Set G)) := hsyl.2.1
  have hC₀le := h.C_card_le hII h4hij hAB hrec
  set C₀ := S ⊓ centralizer ({u'} : Set G) with hC₀
  have hCmap : (centralizer ({t * z} : Set G)).map (MulAut.conj g).toMonoidHom =
      centralizer ({u'} : Set G) := by rw [map_centralizer_singleton_conj, hg]
  have hC₀' : C₀.map (MulAut.conj g⁻¹).toMonoidHom ≤ centralizer ({t * z} : Set G) := by
    rintro _ ⟨c, hc, rfl⟩
    have hc' : c ∈ centralizer ({u'} : Set G) := hc.2
    rw [← hCmap] at hc'
    obtain ⟨y, hy, hyc⟩ := hc'
    have : (MulAut.conj g⁻¹).toMonoidHom c = y := by
      rw [← hyc]
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      group
    rw [this]
    exact hy
  let TY : Subgroup ↥(centralizer ({t * z} : Set G)) :=
    (C₀.map (MulAut.conj g⁻¹).toMonoidHom).subgroupOf (centralizer ({t * z} : Set G))
  let e₁ : ↥C₀ ≃* ↥(C₀.map (MulAut.conj g⁻¹).toMonoidHom) :=
    C₀.equivMapOfInjective (MulAut.conj g⁻¹).toMonoidHom (MulAut.conj g⁻¹).injective
  let e₂ : ↥(C₀.map (MulAut.conj g⁻¹).toMonoidHom) ≃* ↥TY :=
    (Subgroup.subgroupOfEquivOfLe hC₀').symm
  let e₃ : ↥C₀ ≃* ↥TY := e₁.trans e₂
  have hTY2 : IsPGroup 2 ↥TY := hC₀2.of_surjective e₃.toMonoidHom e₃.surjective
  obtain ⟨n, m, hn, hm, hcm⟩ := hsyl.card_eq_pow_mul
  have hY : Nat.card ↥(centralizer ({t * z} : Set G)) = Nat.card ↥(centralizer ({u'} : Set G)) := by
    rw [← hCmap, Subgroup.card_map_of_injective (MulAut.conj g).injective]
  have hTYcard : Nat.card ↥TY = Nat.card ↥C₀ := (Nat.card_congr e₃.toEquiv).symm
  have hidx : ¬ 2 ∣ TY.index := by
    have h1 := Subgroup.card_mul_index TY
    rw [hTYcard, hn, hY, hcm] at h1
    have hpos : 0 < 2 ^ n := by positivity
    have : TY.index = m := Nat.eq_of_mul_eq_mul_left hpos h1
    rw [this]
    exact Nat.two_dvd_ne_zero.2 (Nat.odd_iff.1 hm)
  obtain ⟨e, -, hT2, hTidx⟩ := sylow_map_of_odd_kernel (barMk ↥(centralizer ({t * z} : Set G)))
    barMk_surjective odd_card_ker_barMk hTY2 hidx
  refine ⟨TY.map (barMk ↥(centralizer ({t * z} : Set G))), ⟨le_top, hT2, ?_⟩, ⟨e₃.trans e⟩, ?_⟩
  · rw [Subgroup.relIndex_top_right]
    exact hTidx
  · intro h8
    have hc := Subgroup.card_mul_index (TY.map (barMk ↥(centralizer ({t * z} : Set G))))
    have hTc : Nat.card ↥(TY.map (barMk ↥(centralizer ({t * z} : Set G)))) = 2 ^ n := by
      rw [← hn, ← (Nat.card_congr (e₃.trans e).toEquiv)]
    rw [hTc] at hc
    rw [← hc] at h8
    have h9 : 2 ^ 8 ∣ 2 ^ n := Prime.pow_dvd_of_dvd_mul_right Nat.prime_two.prime 8 hTidx h8
    have h10 : 8 ≤ n := (Nat.pow_dvd_pow_iff_le_right (by norm_num : 1 < 2)).1 h9
    have h11 : 2 ^ 8 ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) h10
    rw [← hn] at h11
    omega

end Cfg65

end CFSG.GH74.GLS.Stage1.Thm3.Sec6.L65
