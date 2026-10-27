module

public import CFSG.CGT.PushingUpLit.CGT6.EmbCbOneFix

public section

namespace CFSG.CGT.PushingUpLit.CGT6

open CFSG CFSG.RankThree.PartOne CFSG.Quasithin CFSG.CGT.PushingUp CFSG.Open Equiv

variable {V : Type} [CommGroup V] [Finite V]

@[expose] def NG (G X : Subgroup (MulAut V)) : Subgroup ↥G where
  carrier := {g | ∀ x ∈ X, (g : MulAut V) * x * (g : MulAut V)⁻¹ ∈ X}
  one_mem' := fun x hx => by simpa using hx
  mul_mem' := fun {a b} ha hb x hx => by
    have h := ha _ (hb x hx)
    simpa [mul_assoc] using h
  inv_mem' := fun {a} ha x hx => by
    simpa using cbo_inv_conj_mem ha x hx

theorem mem_NG {G X : Subgroup (MulAut V)} {g : ↥G} :
    g ∈ NG G X ↔ ∀ x ∈ X, (g : MulAut V) * x * (g : MulAut V)⁻¹ ∈ X := Iff.rfl

@[expose] def QG (G X : Subgroup (MulAut V)) : Subgroup ↥G where
  carrier := {g | ∃ x ∈ X, ∃ q ∈ Subgroup.centralizer (X : Set (MulAut V)),
    (g : MulAut V) = x * q}
  one_mem' := ⟨1, X.one_mem, 1, Subgroup.one_mem _, by simp⟩
  mul_mem' := fun {a b} ⟨x, hx, q, hq, ha⟩ ⟨x', hx', q', hq', hb⟩ =>
    ⟨x * x', X.mul_mem hx hx', q * q', Subgroup.mul_mem _ hq hq', by
      have hqx : q * x' = x' * q := (Subgroup.mem_centralizer_iff.mp hq x' hx').symm
      show (a : MulAut V) * (b : MulAut V) = x * x' * (q * q')
      rw [ha, hb]
      calc x * q * (x' * q') = x * (q * x') * q' := by group
        _ = x * (x' * q) * q' := by rw [hqx]
        _ = x * x' * (q * q') := by group⟩
  inv_mem' := fun {a} ⟨x, hx, q, hq, ha⟩ =>
    ⟨x⁻¹, X.inv_mem hx, q⁻¹, Subgroup.inv_mem _ hq, by
      have hqx : q * x = x * q := (Subgroup.mem_centralizer_iff.mp hq x hx).symm
      show (a : MulAut V)⁻¹ = x⁻¹ * q⁻¹
      rw [ha, mul_inv_rev]
      have : q⁻¹ * x⁻¹ = x⁻¹ * q⁻¹ := by
        calc q⁻¹ * x⁻¹ = (x * q)⁻¹ := by group
          _ = (q * x)⁻¹ := by rw [hqx]
          _ = x⁻¹ * q⁻¹ := by group
      exact this⟩

omit [Finite V] in
theorem mem_QG {G X : Subgroup (MulAut V)} {g : ↥G} :
    g ∈ QG G X ↔ ∃ x ∈ X, ∃ q ∈ Subgroup.centralizer (X : Set (MulAut V)),
      (g : MulAut V) = x * q := Iff.rfl

namespace OneCfg

variable {Y X G T : Subgroup (MulAut V)} {t : MulAut V} {m : ℕ} (c : OneCfg G T Y t m X)

theorem coe_tG : (c.tG : MulAut V) = t := rfl

include c in
theorem tG_mem_NG : c.tG ∈ NG G X := by
  obtain ⟨D⟩ := c.hX.toCbAlg.nonempty_data c.hm c.hodd
  exact D.hn

include c in
theorem odd_index_NG : Odd (NG G X).index := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set P : Subgroup ↥G := Subgroup.zpowers c.tG with hP
  have hPp : IsPGroup 2 ↥P := by
    apply IsPGroup.of_card (n := 1)
    rw [hP, Nat.card_zpowers, c.orderOf_tG, pow_one]
  have hmod := hPp.card_modEq_card_fixedPoints (↥G ⧸ NG G X)
  have hfix : MulAction.fixedPoints ↥P (↥G ⧸ NG G X) = {(↑(1 : ↥G) : ↥G ⧸ NG G X)} := by
    ext z
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective z
    rw [MulAction.mem_fixedPoints, Set.mem_singleton_iff]
    constructor
    · intro hfixed
      have h1 := hfixed ⟨c.tG, Subgroup.mem_zpowers _⟩
      have h2 : (↑(c.tG * g) : ↥G ⧸ NG G X) = ↑g := h1
      rw [QuotientGroup.eq] at h2
      have h3 : g⁻¹ * c.tG * g ∈ NG G X := by
        have htt : c.tG⁻¹ = c.tG := inv_eq_of_mul_eq_one_right (by
          apply Subtype.ext
          show t * t = 1
          rw [← pow_two]; exact c.ht2)
        simpa [mul_inv_rev, htt, mul_assoc] using h2
      have h4 : ∀ x ∈ X, ((g : MulAut V)⁻¹) * x * ((g : MulAut V)⁻¹)⁻¹ ∈ X := by
        refine c.normalizes_X_of_conj_normalizes (h := (g : MulAut V)⁻¹) (G.inv_mem g.2) ?_
        intro x hx
        have e : (((g⁻¹ * c.tG * g : ↥G)) : MulAut V) =
            (g : MulAut V)⁻¹ * t * ((g : MulAut V)⁻¹)⁻¹ := by
          simp [c.coe_tG]
        have := h3 x hx
        rw [mem_NG] at h3
        rw [e] at this
        exact this
      have h5 : g ∈ NG G X := by
        intro x hx
        have := cbo_inv_conj_mem (A := X) (g := (g : MulAut V)⁻¹) h4 x hx
        simpa using this
      rw [QuotientGroup.eq]
      simpa using (NG G X).inv_mem h5
    · intro hz
      rw [QuotientGroup.eq] at hz
      have hg : g ∈ NG G X := by simpa using (NG G X).inv_mem hz
      rintro ⟨s, hs⟩
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hs
      show (↑(c.tG ^ k * g) : ↥G ⧸ NG G X) = ↑g
      rw [QuotientGroup.eq]
      have htN : c.tG ^ k ∈ NG G X := (NG G X).zpow_mem c.tG_mem_NG k
      have h6 : (c.tG ^ k * g)⁻¹ * g = g⁻¹ * (c.tG ^ k)⁻¹ * g := by group
      rw [h6]
      exact (NG G X).mul_mem ((NG G X).mul_mem ((NG G X).inv_mem hg) ((NG G X).inv_mem htN)) hg
  have hcard : Nat.card ↑(MulAction.fixedPoints ↥P (↥G ⧸ NG G X)) = 1 := by
    rw [hfix]; simp
  rw [hcard] at hmod
  have h7 : (NG G X).index % 2 = 1 := hmod
  exact Nat.odd_iff.mpr h7

end OneCfg

end CFSG.CGT.PushingUpLit.CGT6
