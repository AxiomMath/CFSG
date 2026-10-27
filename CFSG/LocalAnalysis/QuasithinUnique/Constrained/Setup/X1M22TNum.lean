module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X1M22TSyl
public import CFSG.LocalAnalysis.SectionRank.SporadicCover

public section

namespace CFSG.QuasithinUnique.Setup.X1

open CFSG.Sporadic.Schreier CFSG.Sporadic.Mathieu CFSG.Blueprint CFSG.Quasithin
  CFSG.QuasithinUnique.Setup.Family

theorem card_modEq_fix_prime {α : Type} [Finite α] (p : ℕ) [Fact p.Prime] (f : α → α)
    (hf : ∀ a, f^[p] a = a) : Nat.card α ≡ Nat.card {a | f a = a} [MOD p] := by
  classical
  have hfin := Fintype.ofFinite α
  let g : Function.End α := f
  have hpow : ∀ n a, (g ^ n) a = f^[n] a := by
    intro n
    induction n with
    | zero => intro a; rfl
    | succ n ih =>
      intro a
      rw [pow_succ]
      exact (ih (f a)).trans (Function.iterate_succ_apply f n a).symm
  have hg : g ^ p ^ 1 = 1 := by
    funext a
    rw [pow_one, hpow]
    exact hf a
  have h := Equiv.Perm.card_fixedPoints_modEq (p := p) (n := 1) hg
  rw [Nat.card_eq_fintype_card]
  have e : Nat.card {a | f a = a} = Fintype.card g.fixedPoints := by
    rw [Nat.card_eq_fintype_card]
    rfl
  rw [e]
  exact h

section Central

variable {W : Type} [CommGroup W] [Finite W] {L E0 : Subgroup (MulAut W)}

omit [Finite W] in
theorem fixV_zpowers_bot_of_comm (hirr : IsIrrOn L) {c : MulAut W} (hc1 : c ≠ 1)
    (hc : ∀ l ∈ L, l * c = c * l) : fixV (Subgroup.zpowers c) = ⊥ := by
  have hinv : ∀ g ∈ L, ∀ u ∈ fixV (Subgroup.zpowers c), g u ∈ fixV (Subgroup.zpowers c) := by
    intro g hg u hu
    rw [mem_fixV_zpowers] at hu ⊢
    have := congrArg (fun z : MulAut W => z u) (hc g hg)
    simp only [MulAut.mul_apply] at this
    rw [← this, hu]
  rcases hirr.2 (fixV (Subgroup.zpowers c)) hinv with h | h
  · exact h
  · exfalso
    apply hc1
    ext w
    have : w ∈ fixV (Subgroup.zpowers c) := by rw [h]; trivial
    exact (mem_fixV_zpowers.1 this)

theorem no_central_three (hirr : IsIrrOn L) (hE0 : E0 ≤ L) (hU : Nat.card (fixV E0) = 32)
    {ζ : MulAut W} (hcomm : ∀ l ∈ L, l * ζ = ζ * l) (hord : orderOf ζ = 3) : False := by
  have : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  have hζ1 : ζ ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hord
    omega
  have hbot := fixV_zpowers_bot_of_comm hirr hζ1 hcomm
  have hstab : ∀ u ∈ fixV E0, ζ u ∈ fixV E0 := by
    intro u hu x hx
    have := congrArg (fun z : MulAut W => z u) (hcomm x (hE0 hx))
    simp only [MulAut.mul_apply] at this
    rw [this, hu x hx]
  let f : fixV E0 → fixV E0 := fun u => ⟨ζ u, hstab u u.2⟩
  have hpow : ∀ n (a : fixV E0), ((f^[n] a : fixV E0) : W) = (ζ ^ n) a := by
    intro n
    induction n with
    | zero => intro a; rfl
    | succ n ih =>
      intro a
      rw [Function.iterate_succ_apply, ih (f a), pow_succ]
      rfl
  have hf : ∀ a, f^[3] a = a := by
    intro a
    apply Subtype.ext
    have h3 : ζ ^ 3 = 1 := by rw [← hord]; exact pow_orderOf_eq_one ζ
    rw [hpow, h3]
    rfl
  have h := card_modEq_fix_prime 3 f hf
  have hfix : Nat.card {a : fixV E0 | f a = a} = 1 := by
    rw [Nat.card_eq_one_iff_unique]
    refine ⟨⟨fun a b => ?_⟩, ⟨⟨1, Subtype.ext (map_one ζ)⟩⟩⟩
    apply Subtype.ext
    apply Subtype.ext
    have hfix' : ∀ c : {a : fixV E0 | f a = a}, (c.1 : W) = 1 := by
      intro c
      have h1 : ζ (c.1 : W) = c.1 := congrArg Subtype.val c.2
      have h2 : (c.1 : W) ∈ fixV (Subgroup.zpowers ζ) := mem_fixV_zpowers.2 h1
      rw [hbot] at h2
      exact h2
    rw [hfix' a, hfix' b]
  rw [hfix, hU] at h
  simp [Nat.ModEq] at h

end Central

section Numerics

variable {W : Type} [CommGroup W] [Finite W] {L : Subgroup (MulAut W)}

theorem tight_numerics
    (hW : ∀ w : W, w * w = 1) {E : Subgroup (MulAut W)}
    (hq : CFSG.IsQuasisimple ↥L) (hirr : IsIrrOn L) (e : CQ L ≃* S22)
    (hEn : E ≤ Subgroup.normalizer (L : Set (MulAut W))) (hEel : IsElemAbelian2 E)
    (hEcard : Nat.card E = 2 ^ 5) (hidx : (fixV E).index = 2 ^ 5) :
    Nat.card W = 2 ^ 10 ∧ Subgroup.center ↥L = ⊥ := by
  have : Fact (Nat.Prime 11) := ⟨by norm_num⟩
  have hperf : Group.IsPerfect ↥L := hq.1
  have hE0L : E ⊓ L ≤ L := inf_le_right
  have hE0el : IsElemAbelian2 (E ⊓ L) :=
    ⟨fun a ha b hb => hEel.1 a ha.1 b hb.1, fun a ha => hEel.2 a ha.1⟩
  have hE0card : Nat.card ↥(E ⊓ L) = 2 ^ 4 := by
    have h1 := card_le_two_mul_inf hW hperf hirr hEn hEel e m22_center_eq_bot' m22_mulAut_card
    have h2 := card_le_two_pow_of_le hW hirr hE0L hE0el e m22_rank_le
    rw [hEcard] at h1
    norm_num at h1 h2 ⊢
    omega
  have hBcomm := imgSub_comm (hEL := hE0L) (e := e) hE0el
  have hBsq := imgSub_sq (hEL := hE0L) (e := e) hE0el
  have hBcard := card_imgSub hW hirr hE0L hE0el e
  have hB3 : 2 < Nat.card (imgSub L (E ⊓ L) hE0L e) := by
    rw [hBcard, hE0card]; norm_num
  obtain ⟨cs, hcs, hgen⟩ := m22_fullgen _ hBcomm hBsq hB3
  have hL : L ≠ ⊥ := by
    intro h
    have h1 : Nat.card ↥L = 1 := by rw [h]; simp
    have h2 : Nat.card (CQ L) ∣ Nat.card ↥L := Subgroup.card_quotient_dvd_card _
    rw [Nat.card_congr e.toEquiv, m22_card_eq, h1] at h2
    have := Nat.le_of_dvd one_pos h2
    norm_num at this
  have hgen' : Subgroup.closure {y : S22 | ∃ c ∈ cs, ∃ b : ↥L, (b : MulAut W) ∈ (E ⊓ L) ∧
      y = c * e (QuotientGroup.mk b) * c⁻¹} = ⊤ := by
    have hset : {y : S22 | ∃ c ∈ cs, ∃ b : ↥L, (b : MulAut W) ∈ (E ⊓ L) ∧
        y = c * e (QuotientGroup.mk b) * c⁻¹} =
        conjSet cs ((imgSub L (E ⊓ L) hE0L e : Subgroup S22) : Set S22) := by
      ext y
      constructor
      · rintro ⟨c, hc, b, hb, rfl⟩
        exact ⟨c, hc, e (QuotientGroup.mk b), mem_imgSub.2 ⟨⟨b, hb⟩, rfl⟩, rfl⟩
      · rintro ⟨c, hc, t, ht, rfl⟩
        obtain ⟨a, rfl⟩ := mem_imgSub.1 ht
        exact ⟨c, hc, Subgroup.inclusion hE0L a, a.2, rfl⟩
    rw [hset]
    exact hgen
  have hW1 : Nat.card W ≤ (fixV (E ⊓ L)).index ^ 2 := by
    have := card_le_index_pow_of_closure_eq_top hperf hirr hL e (B := E ⊓ L) cs hgen'
    rwa [hcs] at this
  have hidx0 : (fixV (E ⊓ L)).index ≤ 2 ^ 5 := by
    rw [← hidx]
    exact Subgroup.index_antitone (fixV_anti inf_le_left)
  have hWge : 2 ^ orderOf (2 : ZMod 11) ≤ Nat.card W :=
    two_pow_le_card_of_dvd hW e (p := 11) (by norm_num)
      (by rw [m22_card_eq]; exact Dvd.dvd.mul_left (by norm_num) _)
  rw [orderOf_two_zmod_11] at hWge
  have hWcard : Nat.card W = 2 ^ 10 := by
    have h1 : (fixV (E ⊓ L)).index ^ 2 ≤ (2 ^ 5) ^ 2 := Nat.pow_le_pow_left hidx0 2
    have h2 : (2 ^ 5) ^ 2 = 2 ^ 10 := by norm_num
    exact le_antisymm (hW1.trans (h1.trans h2.le)) hWge
  refine ⟨hWcard, ?_⟩
  have hU0 : (fixV (E ⊓ L)).index = 2 ^ 5 := by
    have hgen2 := m22_gen2 _ hBcomm hBsq hB3
    have h := two_pow_le_of_inner_gen hW hE0L e (k := 2) (p := 11) (by norm_num) hgen2
    rw [orderOf_two_zmod_11] at h
    have h5 := two_pow_le_of_pow_le (index_fixV_eq_two_pow hW (E ⊓ L)) h (ρ := 5) (by norm_num)
    omega
  have hUcard : Nat.card (fixV (E ⊓ L)) = 32 := by
    have h := Subgroup.card_mul_index (fixV (E ⊓ L))
    rw [hU0, hWcard] at h
    have h32 : 0 < 2 ^ 5 := by norm_num
    have : Nat.card (fixV (E ⊓ L)) * 2 ^ 5 = 32 * 2 ^ 5 := by rw [h]; norm_num
    exact Nat.eq_of_mul_eq_mul_right h32 this
  have hcommZ : ∀ x : ↥(Subgroup.center ↥L), ∀ l ∈ L,
      l * ((x : ↥L) : MulAut W) = ((x : ↥L) : MulAut W) * l := by
    intro x l hl
    have := Subgroup.mem_center_iff.1 x.2 ⟨l, hl⟩
    exact congrArg Subtype.val this
  have hodd : Odd (Nat.card (Subgroup.center ↥L)) := by
    by_contra hev
    rw [Nat.not_odd_iff_even] at hev
    have h2 : 2 ∣ Nat.card (Subgroup.center ↥L) := even_iff_two_dvd.1 hev
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' 2 h2
    have hxW : orderOf ((x : ↥L) : MulAut W) = 2 := by
      rw [Subgroup.orderOf_coe, Subgroup.orderOf_coe, hx]
    have hodd2 := odd_orderOf_of_commutes hW hirr (hcommZ x)
    rw [hxW] at hodd2
    exact absurd hodd2 (by decide)
  have hZ := (CFSG.SectionRank.four_small_sporadic_odd_cover_step hq hodd (s := .M22)
    (Or.inr (Or.inl rfl)) e).1.1
  rcases hZ with h1 | h3
  · exact Subgroup.card_eq_one.1 h1
  · exfalso
    have h3d : 3 ∣ Nat.card (Subgroup.center ↥L) := by rw [h3]
    have : Fact (Nat.Prime 3) := ⟨by norm_num⟩
    obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' 3 h3d
    have hxW : orderOf ((x : ↥L) : MulAut W) = 3 := by
      rw [Subgroup.orderOf_coe, Subgroup.orderOf_coe, hx]
    exact no_central_three hirr hE0L hUcard (hcommZ x) hxW

end Numerics

end CFSG.QuasithinUnique.Setup.X1
