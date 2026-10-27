module

public import CFSG.Walter.Bender1970.S2.Inner
public import CFSG.Assembly.LowTwoRankDefs

public section

namespace CFSG.Goldschmidt.G3b

open CFSG.Open CFSG.Walter CFSG.GorensteinWalter
open scoped MatrixGroups

section ConjQuot

variable {G : Type*} [Group G] (L : Subgroup G) [L.Normal]

theorem center_map_conjNormal (g : G) :
    (Subgroup.center L).map ((MulAut.conjNormal g : L ≃* L) : L →* L) = Subgroup.center L :=
  Subgroup.characteristic_iff_map_eq.mp inferInstance (MulAut.conjNormal g)

noncomputable def conjQuot : G →* MulAut (L ⧸ Subgroup.center L) where
  toFun g := QuotientGroup.congr (Subgroup.center L) (Subgroup.center L) (MulAut.conjNormal g)
    (center_map_conjNormal L g)
  map_one' := by
    ext x
    induction x using QuotientGroup.induction_on with
    | H x =>
      rw [QuotientGroup.congr_mk]
      simp
  map_mul' g h := by
    ext x
    induction x using QuotientGroup.induction_on with
    | H x =>
      rw [MulAut.mul_apply, QuotientGroup.congr_mk, QuotientGroup.congr_mk,
        QuotientGroup.congr_mk]
      congr 1
      ext
      simp [MulAut.conjNormal_apply, mul_assoc]

theorem conjQuot_mk (g : G) (x : L) :
    conjQuot L g (x : L ⧸ Subgroup.center L) =
      ((⟨g * x * g⁻¹, (inferInstance : L.Normal).conj_mem x x.2 g⟩ : L) :
        L ⧸ Subgroup.center L) := by
  change QuotientGroup.congr (Subgroup.center L) (Subgroup.center L) (MulAut.conjNormal g)
    (center_map_conjNormal L g) (x : L ⧸ Subgroup.center L) = _
  rw [QuotientGroup.congr_mk]
  congr 1

theorem conjQuot_eq_one_iff (hL : commutator L = ⊤) (g : G) :
    conjQuot L g = 1 ↔ g ∈ Subgroup.centralizer (L : Set G) := by
  constructor
  · intro h
    apply mem_centralizer_of_commutator_mem_center hL
    intro x hx
    have h1 := congrArg (fun α : MulAut (L ⧸ Subgroup.center L) =>
      α ((⟨x, hx⟩ : L) : L ⧸ Subgroup.center L)) h
    simp only [conjQuot_mk, MulAut.one_apply] at h1
    rw [QuotientGroup.eq] at h1
    set z : L := (⟨g * x * g⁻¹, (inferInstance : L.Normal).conj_mem x hx g⟩ : L)⁻¹ * ⟨x, hx⟩
      with hz
    have hzc : ∀ y : L, y * z = z * y := Subgroup.mem_center_iff.mp h1
    refine ⟨z⁻¹, Subgroup.inv_mem _ h1, ?_⟩
    have hxz : (⟨x, hx⟩ : L) * z⁻¹ = z⁻¹ * ⟨x, hx⟩ := by
      have h3 := hzc (⟨x, hx⟩ : L)
      calc (⟨x, hx⟩ : L) * z⁻¹ = z⁻¹ * (z * ⟨x, hx⟩) * z⁻¹ := by group
        _ = z⁻¹ * (⟨x, hx⟩ * z) * z⁻¹ := by rw [h3]
        _ = z⁻¹ * ⟨x, hx⟩ := by group
    have h5 : (z⁻¹ : L) = ⟨g * x * g⁻¹, (inferInstance : L.Normal).conj_mem x hx g⟩ *
        (⟨x, hx⟩ : L)⁻¹ := by
      calc z⁻¹ = z⁻¹ * ⟨x, hx⟩ * (⟨x, hx⟩ : L)⁻¹ := by group
        _ = ⟨x, hx⟩ * z⁻¹ * (⟨x, hx⟩ : L)⁻¹ := by rw [hxz]
        _ = _ := by rw [hz]; group
    rw [Subgroup.coe_subtype, h5]
    simp [mul_assoc]
  · intro h
    ext x
    induction x using QuotientGroup.induction_on with
    | H x =>
      rw [conjQuot_mk, MulAut.one_apply]
      congr 1
      ext
      simp only
      rw [← Subgroup.mem_centralizer_iff.mp h x x.2, mul_inv_cancel_right]

theorem conjQuot_of_mem {l : G} (hl : l ∈ L) :
    conjQuot L l = MulAut.conj ((⟨l, hl⟩ : L) : L ⧸ Subgroup.center L) := by
  ext x
  induction x using QuotientGroup.induction_on with
  | H x =>
    rw [conjQuot_mk, MulAut.conj_apply, ← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul,
      ← QuotientGroup.mk_mul]
    rfl

theorem mem_sup_centralizer_of_conjQuot_eq_conj (hL : commutator L = ⊤) {g : G} (l : L)
    (h : conjQuot L g = MulAut.conj (l : L ⧸ Subgroup.center L)) :
    g ∈ L ⊔ Subgroup.centralizer (L : Set G) := by
  have hc : (l : G)⁻¹ * g ∈ Subgroup.centralizer (L : Set G) := by
    rw [← conjQuot_eq_one_iff L hL, map_mul, map_inv, h, conjQuot_of_mem L l.2]
    simp
  have : g = (l : G) * ((l : G)⁻¹ * g) := by group
  rw [this]
  exact Subgroup.mul_mem _ (le_sup_left (a := L) l.2) (le_sup_right (a := L) hc)

omit [L.Normal] in
theorem mem_centralizer_of_mk_mem_centralizer (hZ : Odd (Nat.card (Subgroup.center L)))
    {a : G} (ha : a ∈ L) (ha2 : a * a = 1) (x : L)
    (hx : (x : L ⧸ Subgroup.center L) ∈ Subgroup.centralizer
      ({((⟨a, ha⟩ : L) : L ⧸ Subgroup.center L)} : Set (L ⧸ Subgroup.center L))) :
    (x : G) ∈ Subgroup.centralizer ({a} : Set G) :=
  (mem_centralizer_iff_of_inner hZ ha2 ha (fun _ _ => rfl) x).mpr hx

end ConjQuot

section Cyclic

theorem odd_orderOf_pow_two_pow {M : Type*} [Monoid M] {x : M} {N : ℕ}
    (hpos : 0 < orderOf x) (hN : orderOf x ≤ N) : Odd (orderOf (x ^ 2 ^ N)) := by
  obtain ⟨b, m, hm, hbm⟩ := Nat.exists_eq_two_pow_mul_odd hpos.ne'
  have hb : b ≤ N := by
    have h1 : b < 2 ^ b := Nat.lt_two_pow_self
    have h2 : 2 ^ b ≤ orderOf x := by
      rw [hbm]
      exact Nat.le_mul_of_pos_right _ hm.pos
    omega
  apply Odd.of_dvd_nat hm
  apply orderOf_dvd_of_pow_eq_one
  have : 2 ^ N * m = orderOf x * 2 ^ (N - b) := by
    rw [hbm, mul_comm (2 ^ b) m, mul_assoc, ← pow_add, Nat.add_sub_cancel' hb, mul_comm]
  rw [← pow_mul, this, pow_mul, pow_orderOf_eq_one, one_pow]

theorem mem_of_pow_two_pow_mem {G : Type*} [Group G] [Finite G] (M : Subgroup G) {y : G}
    (N : ℕ) (hz : y ^ 2 ^ N ∈ M)
    (h2 : ∀ k : ℕ, IsPGroup 2 (Subgroup.zpowers (y ^ k)) → y ^ k ∈ M) : y ∈ M := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨b, m, hm, hbm⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos y).ne'
  have hw : IsPGroup 2 (Subgroup.zpowers (y ^ m)) := by
    have hdvd : orderOf (y ^ m) ∣ 2 ^ b := by
      apply orderOf_dvd_of_pow_eq_one
      rw [← pow_mul, mul_comm, ← hbm, pow_orderOf_eq_one]
    obtain ⟨c, -, hc⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd
    exact IsPGroup.of_card (n := c) (by rw [Nat.card_zpowers, hc])
  have hwM := h2 m hw
  have hcop : Nat.Coprime m (2 ^ N) := Nat.Coprime.pow_right N (Nat.coprime_two_right.mpr hm)
  obtain ⟨u, v, huv⟩ : ∃ u v : ℤ, (m : ℤ) * u + (2 ^ N : ℕ) * v = 1 := by
    obtain ⟨u, v, huv⟩ := Nat.isCoprime_iff_coprime.mpr hcop
    exact ⟨u, v, by push_cast at huv ⊢; linarith⟩
  have hy : y = (y ^ m) ^ u * (y ^ 2 ^ N) ^ v := by
    rw [← zpow_natCast, ← zpow_natCast, ← zpow_mul, ← zpow_mul, ← zpow_add]
    push_cast at huv ⊢
    rw [huv, zpow_one]
  rw [hy]
  exact M.mul_mem (M.zpow_mem hwM u) (M.zpow_mem hz v)

theorem cyclic_quotient_of_hom {G Q : Type*} [Group G] [Group Q] [Finite G] (Y M : Subgroup G)
    (ψ : Y →* Q) (hcyc : IsCyclic ψ.range) (hodd : ∀ y : Y, Odd (orderOf (ψ y)))
    (hker : ∀ y : Y, ψ y = 1 → (y : G) ∈ M) :
    Odd ((M.subgroupOf Y).index) ∧ ∃ y ∈ Y, Y ≤ Subgroup.zpowers y ⊔ M := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hkerle : ψ.ker ≤ M.subgroupOf Y := fun y hy => Subgroup.mem_subgroupOf.mpr (hker y hy)
  have : Finite ψ.range := Finite.of_surjective ψ.rangeRestrict ψ.rangeRestrict_surjective
  refine ⟨?_, ?_⟩
  · have hdvd : (M.subgroupOf Y).index ∣ ψ.ker.index := Subgroup.index_dvd_of_le hkerle
    rw [Subgroup.index_ker] at hdvd
    apply Odd.of_dvd_nat _ hdvd
    rw [← Nat.not_even_iff_odd, even_iff_two_dvd]
    intro h2
    obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := ψ.range) 2 h2
    obtain ⟨y, hy⟩ := x.2
    have h := hodd y
    rw [hy, Subgroup.orderOf_coe, hx] at h
    exact (Nat.not_odd_iff_even.mpr even_two) h
  · obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := ψ.range)
    obtain ⟨y0, hy0⟩ := g.2
    refine ⟨y0, y0.2, fun y hy => ?_⟩
    obtain ⟨n, hn⟩ := hg ⟨ψ ⟨y, hy⟩, ⟨y, hy⟩, rfl⟩
    have hn' : ψ (y0 ^ n) = ψ ⟨y, hy⟩ := by
      rw [map_zpow, hy0]
      exact congrArg Subtype.val hn
    have h1 : ψ ((y0 ^ n)⁻¹ * ⟨y, hy⟩) = 1 := by rw [map_mul, map_inv, hn', inv_mul_cancel]
    have h2 := hker _ h1
    have : y = ((y0 : G) ^ n) * (((y0 ^ n)⁻¹ * ⟨y, hy⟩ : Y) : G) := by simp
    rw [this]
    exact Subgroup.mul_mem _ (le_sup_left (a := Subgroup.zpowers (y0 : G))
      (Subgroup.zpow_mem_zpowers _ n)) (le_sup_right (a := Subgroup.zpowers (y0 : G)) h2)

end Cyclic

end CFSG.Goldschmidt.G3b
