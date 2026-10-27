module

public import CFSG.GH74.GLS.Stage2.Final.L26.G2Basic

public section

namespace CFSG.GH74.GLS.Stage2.Final.Thm6.L208g2

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage2.Local CFSG.GH74.GLS.Stage2.Final

section Sylow

variable {Y : Type} [Group Y] [Finite Y]

theorem exists_conj_mem_sylow {Sb : Subgroup Y} (hS : CFSG.ABGLocalTools.IsSylowOf 2 Sb ⊤) {y : Y}
    (hy : ∃ k : ℕ, y ^ (2 ^ k) = 1) : ∃ x : Y, x⁻¹ * y * x ∈ Sb := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨-, hSp, hidx⟩ := CFSG.ABGLocalTools.isSylowOf_iff.1 hS
  rw [Subgroup.relIndex_top_right] at hidx
  let Q : Sylow 2 Y := hSp.toSylow hidx
  have hpg : IsPGroup 2 (Subgroup.zpowers y) := by
    obtain ⟨k, hk⟩ := hy
    have h1 : orderOf y ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one hk
    obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 h1
    exact IsPGroup.of_card (n := j) (by rw [Nat.card_zpowers, hj])
  obtain ⟨Q', hQ'⟩ := hpg.exists_le_sylow
  obtain ⟨c, hc⟩ := MulAction.exists_smul_eq Y Q Q'
  have hyQ' : y ∈ (Q' : Subgroup Y) := hQ' (Subgroup.mem_zpowers y)
  rw [← hc, Sylow.coe_subgroup_smul, Subgroup.mem_smul_pointwise_iff_exists] at hyQ'
  obtain ⟨s, hs, hsy⟩ := hyQ'
  refine ⟨c, ?_⟩
  have h1 : (MulAut.conj c) • s = c * s * c⁻¹ := rfl
  have : c⁻¹ * y * c = s := by
    rw [← hsy, h1]; group
  rw [this]
  exact hs

end Sylow

section Factor

structure Pair {Y : Type} [Group Y] (Lk Lk' : Subgroup Y) (r r' : ℕ) : Prop where
  odd : Odd r
  gt : 3 < r
  odd' : Odd r'
  hm : HasSL2Model ↥Lk (fun q => q = r)
  hm' : HasSL2Model ↥Lk' (fun q => q = r')
  comm : ∀ a ∈ Lk, ∀ b ∈ Lk', a * b = b * a
  inf : Nat.card ↥(Lk ⊓ Lk') = 2

structure Factor {Y : Type} [Group Y] [Finite Y] (Sb Rb Lk Lk' : Subgroup Y) (r r' : ℕ) : Prop
    extends Pair Lk Lk' r r' where
  normal : Lk.Normal
  syl : CFSG.ABGLocalTools.IsSylowOf 2 Sb ⊤
  ind : InducedPGL2 Lk Sb r
  Rb_le : Rb ≤ Lk ⊔ Lk'
  Rb_idx : ∀ y ∈ Sb, y ∉ Rb → ∀ s ∈ Sb, s ∈ Rb ∨ y⁻¹ * s ∈ Rb

variable {Y : Type} [Group Y] {Lk Lk' : Subgroup Y} {r r' : ℕ}

theorem Pair.comm' (h : Pair Lk Lk' r r') : ∀ a ∈ Lk', ∀ b ∈ Lk, a * b = b * a :=
  fun a ha b hb => (h.comm b hb a ha).symm

theorem Pair.cen (h : Pair Lk Lk' r r') {a : Y} (ha : a ∈ Lk) (hc : ∀ c ∈ Lk, c * a = a * c) :
    a ∈ Lk' := by
  have hZ : Nat.card (center ↥Lk) = 2 := (sl2_model_facts h.odd (by have := h.gt; omega) h.hm).2.1
  exact central_mem_of_card_inf h.comm hZ h.inf ha hc

theorem Pair.cen' (h : Pair Lk Lk' r r') {a : Y} (ha : a ∈ Lk') (hc : ∀ c ∈ Lk', c * a = a * c) :
    a ∈ Lk := by
  have hZ : Nat.card (center ↥Lk') = 2 := (sl2_model_center_inv h.odd' h.hm').1
  have hinf : Nat.card ↥(Lk' ⊓ Lk) = 2 := by rw [inf_comm]; exact h.inf
  exact central_mem_of_card_inf h.comm' hZ hinf ha hc

theorem Pair.sq_of_mem_inf (h : Pair Lk Lk' r r') {a : Y} (ha : a ∈ Lk ⊓ Lk') : a * a = 1 := by
  have h1 : orderOf (⟨a, ha⟩ : ↥(Lk ⊓ Lk')) ∣ Nat.card ↥(Lk ⊓ Lk') := orderOf_dvd_natCard _
  rw [h.inf] at h1
  have h2 := orderOf_dvd_iff_pow_eq_one.1 h1
  simpa [sq] using congrArg Subtype.val h2

theorem Pair.mem_inf_of_sq (h : Pair Lk Lk' r r') {a : Y} (ha : a ∈ Lk') (ha2 : a * a = 1) :
    a ∈ Lk ⊓ Lk' := by
  by_cases ha1 : a = 1
  · rw [ha1]; exact (Lk ⊓ Lk').one_mem
  · obtain ⟨-, huniq⟩ := sl2_model_center_inv h.odd' h.hm'
    have hne : ∃ w ∈ Lk ⊓ Lk', w ≠ 1 := by
      by_contra hcon
      push Not at hcon
      have : Nat.card ↥(Lk ⊓ Lk') = 1 := by
        rw [Nat.card_eq_one_iff_unique]
        refine ⟨⟨fun x y => Subtype.ext ?_⟩, ⟨1⟩⟩
        rw [hcon x x.2, hcon y y.2]
      rw [h.inf] at this
      omega
    obtain ⟨w, hw, hw1⟩ := hne
    have hww : w * w = 1 := h.sq_of_mem_inf hw
    have ho : ∀ x : Y, x * x = 1 → x ≠ 1 → orderOf x = 2 := fun x hx hx1 =>
      orderOf_eq_prime (by rw [← sq] at hx; exact hx) hx1
    have := huniq a ha w hw.2 (ho a ha2 ha1) (ho w hww hw1)
    rw [this]
    exact hw

theorem Pair.exists_mul (h : Pair Lk Lk' r r') {x : Y} (hx : x ∈ Lk ⊔ Lk') :
    ∃ a ∈ Lk, ∃ b ∈ Lk', x = a * b :=
  L26.exists_mul_of_mem_sup_of_commute h.comm hx

theorem Pair.mem_of_cen (h : Pair Lk Lk' r r') {x : Y} (hx : x ∈ Lk ⊔ Lk')
    (hc : ∀ c ∈ Lk, x * c = c * x) : x ∈ Lk' := by
  obtain ⟨a, ha, b, hb, rfl⟩ := h.exists_mul hx
  have hacen : ∀ c ∈ Lk, c * a = a * c := by
    intro c hc'
    have h3 : (a * b) * c = c * (a * b) := hc c hc'
    have h2 := h.comm c hc' b hb
    have h4 : a * c * b = c * a * b := by
      calc a * c * b = a * (c * b) := by group
        _ = a * (b * c) := by rw [← h2]
        _ = (a * b) * c := by group
        _ = c * (a * b) := h3
        _ = c * a * b := by group
    exact (mul_right_cancel h4).symm
  exact mul_mem (h.cen ha hacen) hb

theorem Pair.not_comm (h : Pair Lk Lk' r r') : ¬ ∀ a ∈ Lk, ∀ b ∈ Lk, a * b = b * a := by
  intro hc
  have hq := (sl2_model_facts h.odd (by have := h.gt; omega) h.hm).1
  have hperf : Group.IsPerfect ↥Lk := hq.1
  have hnt : Nontrivial ↥Lk := CFSG.LocalCores.isQuasisimple_nontrivial hq
  have hsol : Group.IsSolvable ↥Lk :=
    Group.isSolvable_of_comm (fun a b => Subtype.ext (hc a a.2 b b.2))
  exact Group.IsPerfect.not_isSolvable ↥Lk hsol

theorem Pair.not_cen_of_sq (h : Pair Lk Lk' r r') {a : Y} (ha : a ∈ Lk) (ha2 : a * a ≠ 1) :
    ¬ ∀ c ∈ Lk, c * a = a * c := by
  intro hc
  have : a ∈ Lk ⊓ Lk' := ⟨ha, h.cen ha hc⟩
  exact ha2 (h.sq_of_mem_inf this)

end Factor

section F3

variable {Y : Type} [Group Y] [Finite Y] {Sb Rb Lk Lk' : Subgroup Y} {r r' : ℕ}

theorem Factor.mem_inf_of_cen (h : Factor Sb Rb Lk Lk' r r') {y : Y} (hy : y * y = 1)
    (hc : ∀ x ∈ Lk, y * x = x * y) : y ∈ Lk ⊓ Lk' := by
  have := h.normal
  obtain ⟨x, hx⟩ := exists_conj_mem_sylow h.syl (y := y) ⟨1, by simpa [sq] using hy⟩
  set y' := x⁻¹ * y * x with hy'
  have hy'2 : y' * y' = 1 := by
    rw [hy']
    calc x⁻¹ * y * x * (x⁻¹ * y * x) = x⁻¹ * (y * y) * x := by group
      _ = 1 := by rw [hy]; group
  have hy'c : ∀ a ∈ Lk, y' * a = a * y' := by
    intro a ha
    have h1 : x * a * x⁻¹ ∈ Lk := by
      have := (inferInstance : Lk.Normal).conj_mem a ha x
      simpa using this
    have h2 := hc _ h1
    rw [hy']
    calc x⁻¹ * y * x * a = x⁻¹ * (y * (x * a * x⁻¹)) * x := by group
      _ = x⁻¹ * ((x * a * x⁻¹) * y) * x := by rw [h2]
      _ = a * (x⁻¹ * y * x) := by group
  have hy'in : y' ∈ Lk ⊓ Lk' := by
    by_cases hR : y' ∈ Rb
    · have hy'L' : y' ∈ Lk' := h.toPair.mem_of_cen (h.Rb_le hR) (fun c hc' => hy'c c hc')
      exact h.toPair.mem_inf_of_sq hy'L' hy'2
    · exfalso
      have hySb : y' ∈ Sb := hx
      have hS : ∀ s ∈ Sb, s ∈ Rb ∨ y'⁻¹ * s ∈ Rb := h.Rb_idx y' hySb hR
      have hRR : ∀ s ∈ Rb, ∃ a ∈ Lk, ∃ c ∈ centralizer (Lk : Set Y), s = a * c := by
        intro s hs
        obtain ⟨a, ha, b, hb, rfl⟩ := h.toPair.exists_mul (h.Rb_le hs)
        exact ⟨a, ha, b, Subgroup.mem_centralizer_iff.mpr fun g hg => h.comm g hg b hb, rfl⟩
      have hout := L26.not_mem_mul_centralizer_of_inducedPGL2 h.odd h.hm h.ind hS hRR
      exact hout ⟨1, Lk.one_mem, y', Subgroup.mem_centralizer_iff.mpr fun g hg => (hy'c g hg).symm,
        by simp⟩
  have hyLk : y ∈ Lk := by
    have h1 : x * y' * x⁻¹ ∈ Lk := (inferInstance : Lk.Normal).conj_mem y' hy'in.1 x
    have h2 : x * y' * x⁻¹ = y := by rw [hy']; group
    rwa [h2] at h1
  exact ⟨hyLk, h.cen hyLk (fun c hc' => (hc c hc').symm)⟩

end F3

end CFSG.GH74.GLS.Stage2.Final.Thm6.L208g2
