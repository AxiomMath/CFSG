module

public import CFSG.Quasithin.Vol2.Ch12Sec4N6F4
public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch12Sec4N6F3

public section

namespace CFSG.Quasithin.H13

namespace N1246

open CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.Quasithin.L3
open scoped IsMulCommutative Pointwise

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G]

namespace Ctx

variable {T L V E : Subgroup G} {z v : G} [IsMulCommutative ↥V]

namespace Cyc

variable {c : Ctx T L V E z v} {g : G} (hg : c.Cyc g)
include hg

theorem false_of_not_le_N_L1_F4 (h12210 : Stmt12_2_10_F4) (hcomm : ⁅pCoreOf 2 (L ⊔ T), L⁆ = V)
    (hL1 : ¬ Subgroup.normalizer (c.R1 : Set G) ≤ Subgroup.normalizer (c.L1 : Set G)) : False := by
  have hgE := hg.NR1_le_NE hg.mem
  have hggE : g * g ∈ Subgroup.normalizer (E : Set G) := Subgroup.mul_mem _ hgE hgE
  have h1E : (1 : G) ∈ Subgroup.normalizer (E : Set G) := Subgroup.one_mem _
  have hgL := hg.not_mem_NL1 hL1
  set K := Subgroup.centralizer (E : Set G) with hK
  obtain ⟨P⟩ : Nonempty (Sylow 3 ↥K) := inferInstance
  set Pg := (P : Subgroup ↥K).map K.subtype with hPg
  have hPK : Pg ≤ K := Subgroup.map_subtype_le _
  have hP3 : IsPGroup 3 Pg := P.isPGroup'.map _
  have hPe := hg.isElemAbelian_F4 h12210 hcomm hPK hP3
  have hP9 : Nat.card Pg ≤ 9 := by
    have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    obtain ⟨k, hk⟩ := hP3.exists_card_eq
    have hk2 := c.le_two_of_elem3 (hPK.trans c.CE_le_M) hPe hk
    rw [hk]
    calc 3 ^ k ≤ 3 ^ 2 := Nat.pow_le_pow_right (by norm_num) hk2
      _ = 9 := by norm_num

  obtain ⟨a, haP, haL, ha3, haV⟩ := hg.exists_elt h1E P
  obtain ⟨b, hbP, hbL, hb3, hbV⟩ := hg.exists_elt hgE P
  obtain ⟨d, hdP, hdL, hd3, hdV⟩ := hg.exists_elt hggE P
  rw [B6.conjSub_one] at haL haV
  by_cases hα : c.L1 ≤ Subgroup.centralizer (B6.conjSub g V : Set G)
  ·
    obtain ⟨h1, h2, h3, h4, h5⟩ := hg.sym hα
    have := card_ge_27 hPe haP hbP hdP ha3 hb3 hd3 haV hbV (hα haL) hdV (h1 haL) (h3 hbL)
    omega
  ·
    obtain ⟨s1, s2, s3, s4, s5⟩ := hg.sym'
    have haVg : a ∉ Subgroup.centralizer (B6.conjSub g V : Set G) := fun h => hα (by
      have := hg.le_of_mem_centralizer h1E hgE (x := a) (by rwa [B6.conjSub_one])
        ha3 (by rwa [B6.conjSub_one]) h
      rwa [B6.conjSub_one] at this)
    have haVgg : a ∉ Subgroup.centralizer (B6.conjSub (g * g) V : Set G) := fun h => hα (s1 (by
      have := hg.le_of_mem_centralizer h1E hggE (x := a) (by rwa [B6.conjSub_one])
        ha3 (by rwa [B6.conjSub_one]) h
      rwa [B6.conjSub_one] at this))
    have hbV0 : b ∉ Subgroup.centralizer (V : Set G) := fun h => hα (s2 (by
      have := hg.le_of_mem_centralizer hgE h1E hbL hb3 hbV (by rwa [B6.conjSub_one])
      rwa [B6.conjSub_one] at this))
    have hbVgg : b ∉ Subgroup.centralizer (B6.conjSub (g * g) V : Set G) := fun h => hα (s3
      (hg.le_of_mem_centralizer hgE hggE hbL hb3 hbV h))
    have hdV0 : d ∉ Subgroup.centralizer (V : Set G) := fun h => hα (s4 (by
      have := hg.le_of_mem_centralizer hggE h1E hdL hd3 hdV (by rwa [B6.conjSub_one])
      rwa [B6.conjSub_one] at this))
    have hdVg : d ∉ Subgroup.centralizer (B6.conjSub g V : Set G) := fun h => hα (s5
      (hg.le_of_mem_centralizer hggE hgE hdL hd3 hdV h))

    have hcard_eq : ∀ h : G, h ∈ Subgroup.normalizer (E : Set G) →
        B6.conjSub h c.L1 ≤ c.L1 → h ∈ Subgroup.normalizer (c.L1 : Set G) := by
      intro h hh hle
      apply mem_normalizer_of_conjSub_eq
      exact Subgroup.eq_of_le_of_card_ge hle (by rw [B6.card_conjSub])
    have hL1N : K ≤ Subgroup.normalizer (c.L1 : Set G) := c.CE_le_N_L1
    have hb_a : b ∉ Subgroup.zpowers a := by
      intro hb
      have hbL1 : b ∈ c.L1 := (Subgroup.zpowers_le.2 haL) hb
      exact hgL (hcard_eq g hgE (hg.conjL1_le_of_mem hgE hL1N hbL hbL1 hb3 hbV))
    have hd_a : d ∉ Subgroup.zpowers a := by
      intro hd
      have hdL1 : d ∈ c.L1 := (Subgroup.zpowers_le.2 haL) hd
      have hggN := hcard_eq (g * g) hggE (hg.conjL1_le_of_mem hggE hL1N hdL hdL1 hd3 hdV)
      apply hgL
      have hg3 := mem_normalizer_of_conjSub_eq hg.cube_conjSub.2
      have := Subgroup.mul_mem _ hg3 (Subgroup.inv_mem _ hggN)
      rwa [show g * g * g * (g * g)⁻¹ = g by group] at this
    have hd_b : d ∉ Subgroup.zpowers b := by
      intro hd
      have hdL1 : d ∈ B6.conjSub g c.L1 := (Subgroup.zpowers_le.2 hbL) hd
      have hN : K ≤ Subgroup.normalizer (B6.conjSub g c.L1 : Set G) := fun k hk =>
        mem_normalizer_of_conjSub_eq (c.CE_conjSub hgE hk).2
      have hle := hg.conjL1_le_of_mem hggE hN hdL hdL1 hd3 hdV
      have heq : B6.conjSub (g * g) c.L1 = B6.conjSub g c.L1 :=
        Subgroup.eq_of_le_of_card_ge hle (by rw [B6.card_conjSub, B6.card_conjSub])
      apply hgL
      apply mem_normalizer_of_conjSub_eq
      rw [B6.conjSub_mul] at heq
      exact (B6.conjSub g).injective heq

    have haP' := Subgroup.zpowers_le.2 haP
    have hbP' := Subgroup.zpowers_le.2 hbP
    have hcommab : ∀ x ∈ Subgroup.zpowers a, ∀ y ∈ Subgroup.zpowers b, x * y = y * x :=
      fun x hx y hy => comm_of_elem hPe (haP' hx) (hbP' hy)
    have hinf : Subgroup.zpowers a ⊓ Subgroup.zpowers b = ⊥ := by
      rw [eq_bot_iff]
      intro x hx
      rw [Subgroup.mem_bot]
      rcases mem_zpowers_three (orderOf_eq_three hb3 hbV) hx.2 with h | h | h
      · exact h
      · exact absurd (h ▸ hx.1) hb_a
      · exfalso
        apply hb_a
        have : b = (b * b) * (b * b) := by
          calc b = (b * b * b) * b := by rw [hb3, one_mul]
            _ = (b * b) * (b * b) := by group
        rw [this, ← h]
        exact Subgroup.mul_mem _ hx.1 hx.1
    have hcab := B2F.card_sup_mul_card_inf_of_commute hcommab
    rw [hinf, Subgroup.card_bot, mul_one, Nat.card_zpowers, Nat.card_zpowers,
      orderOf_eq_three ha3 haV, orderOf_eq_three hb3 hbV] at hcab
    have hPeq : Subgroup.zpowers a ⊔ Subgroup.zpowers b = Pg :=
      Subgroup.eq_of_le_of_card_ge (sup_le haP' hbP') (by rw [hcab]; exact hP9)
    have hdmem : d ∈ (Subgroup.zpowers a : Set G) * (Subgroup.zpowers b : Set G) := by
      rw [← Subgroup.coe_mul_of_left_le_normalizer_right _ _ (fun x hx =>
        Subgroup.centralizer_le_normalizer (Subgroup.zpowers b : Set G)
          (Subgroup.mem_centralizer_iff.2 fun y hy => (hcommab x hx y hy).symm)), hPeq]
      exact hdP
    obtain ⟨α, hα', β, hβ, hdαβ⟩ := hdmem
    have hdαβ' : d = α * β := hdαβ.symm
    have hao := orderOf_eq_three ha3 haV
    have hbo := orderOf_eq_three hb3 hbV

    have hrel : ∀ h ∈ ({1, g, g * g} : Set G), a ∉ Subgroup.centralizer (B6.conjSub h V : Set G) →
        b ∉ Subgroup.centralizer (B6.conjSub h V : Set G) →
        d ∉ Subgroup.centralizer (B6.conjSub h V : Set G) →
        a⁻¹ * b ∈ Subgroup.centralizer (B6.conjSub h V : Set G) ∨
          (a * a)⁻¹ * b ∈ Subgroup.centralizer (B6.conjSub h V : Set G) := by
      intro h hh haC hbC _
      have hhE : h ∈ Subgroup.normalizer (E : Set G) := by
        rcases hh with rfl | rfl | rfl
        · exact h1E
        · exact hgE
        · exact hggE
      rcases hg.idx3_F4 h12210 hhE hPK hP3 haP hbP haC with h | h | h
      · exact absurd h hbC
      · exact Or.inl h
      · exact Or.inr h

    have hα2 : α = a ∨ α = a * a := by
      rcases mem_zpowers_three hao hα' with h | h | h
      · exfalso; apply hd_b; rw [hdαβ', h, one_mul]; exact hβ
      · exact Or.inl h
      · exact Or.inr h
    have hβ2 : β = b ∨ β = b * b := by
      rcases mem_zpowers_three hbo hβ with h | h | h
      · exfalso; apply hd_a; rw [hdαβ', h, mul_one]; exact hα'
      · exact Or.inl h
      · exact Or.inr h

    have hc : a * b = b * a := comm_of_elem hPe haP hbP
    have ha_inv : a⁻¹ = a * a := inv_eq_of_mul_eq_one_right (by rw [← mul_assoc]; exact ha3)
    have haa_inv : (a * a)⁻¹ = a := inv_eq_of_mul_eq_one_right ha3
    have hsq1 : ((a * a)⁻¹ * b) * ((a * a)⁻¹ * b) = a * a * (b * b) := by
      rw [haa_inv]
      calc a * b * (a * b) = a * (b * a) * b := by group
        _ = a * (a * b) * b := by rw [hc]
        _ = a * a * (b * b) := by group
    have hsq2 : (a⁻¹ * b) * (a⁻¹ * b) = a * (b * b) := by
      rw [ha_inv]
      calc a * a * b * (a * a * b) = a * a * (b * a) * a * b := by group
        _ = a * a * (a * b) * a * b := by rw [hc]
        _ = a * a * a * (b * a) * b := by group
        _ = a * a * a * (a * b) * b := by rw [hc]
        _ = (a * a * a) * (a * (b * b)) := by group
        _ = a * (b * b) := by rw [ha3, one_mul]

    have hD : ∀ h ∈ ({1, g, g * g} : Set G),
        a ∉ Subgroup.centralizer (B6.conjSub h V : Set G) →
        b ∉ Subgroup.centralizer (B6.conjSub h V : Set G) →
        d ∉ Subgroup.centralizer (B6.conjSub h V : Set G) →
        ((α = a ∧ β = b) ∨ (α = a * a ∧ β = b * b) →
          a⁻¹ * b ∈ Subgroup.centralizer (B6.conjSub h V : Set G)) ∧
        ((α = a ∧ β = b * b) ∨ (α = a * a ∧ β = b) →
          (a * a)⁻¹ * b ∈ Subgroup.centralizer (B6.conjSub h V : Set G)) := by
      intro h hh haC hbC hdC
      have hr := hrel h hh haC hbC hdC
      refine ⟨fun hcase => hr.resolve_right fun hw => hdC ?_,
        fun hcase => hr.resolve_left fun hu => hdC ?_⟩
      · rcases hcase with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · rw [hdαβ', h1, h2, ← haa_inv]; exact hw
        · rw [hdαβ', h1, h2, ← hsq1]; exact Subgroup.mul_mem _ hw hw
      · rcases hcase with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · rw [hdαβ', h1, h2, ← hsq2]; exact Subgroup.mul_mem _ hu hu
        · rw [hdαβ', h1, h2, ← ha_inv]; exact hu
    have hm1 : (1 : G) ∈ ({1, g, g * g} : Set G) := Or.inl rfl
    have hmg : g ∈ ({1, g, g * g} : Set G) := Or.inr (Or.inl rfl)
    have hmgg : g * g ∈ ({1, g, g * g} : Set G) := Or.inr (Or.inr rfl)
    have haV' : a ∉ Subgroup.centralizer (B6.conjSub 1 V : Set G) := by rwa [B6.conjSub_one]
    have hbV' : b ∉ Subgroup.centralizer (B6.conjSub 1 V : Set G) := by rwa [B6.conjSub_one]
    have hdV' : d ∉ Subgroup.centralizer (B6.conjSub 1 V : Set G) := by rwa [B6.conjSub_one]
    obtain ⟨k0, k0'⟩ := hD 1 hm1 haV' hbV' hdV'
    obtain ⟨k1, k1'⟩ := hD g hmg haVg hbV hdVg
    obtain ⟨k2, k2'⟩ := hD (g * g) hmgg haVgg hbVgg hdV
    rw [B6.conjSub_one] at k0 k0'
    have hfin : ∀ x ∈ Pg, x ∈ Subgroup.centralizer (V : Set G) →
        x ∈ Subgroup.centralizer (B6.conjSub g V : Set G) →
        x ∈ Subgroup.centralizer (B6.conjSub (g * g) V : Set G) → x = 1 := by
      intro x hx h0 h1 h2
      have hx3 : x * x * x = 1 := by rw [← pow_three']; exact hPe.2 x hx
      exact hg.eq_one_of_odd hcomm h0 h1 h2 (odd_orderOf_of_cube hx3)
    have hxP : a⁻¹ * b ∈ Pg := Pg.mul_mem (Pg.inv_mem haP) hbP
    have hyP : (a * a)⁻¹ * b ∈ Pg := Pg.mul_mem (Pg.inv_mem (Pg.mul_mem haP haP)) hbP
    rcases hα2 with hα1 | hα1 <;> rcases hβ2 with hβ1 | hβ1
    · have h1 := hfin _ hxP (k0 (Or.inl ⟨hα1, hβ1⟩)) (k1 (Or.inl ⟨hα1, hβ1⟩))
        (k2 (Or.inl ⟨hα1, hβ1⟩))
      apply hb_a
      rw [show b = a * (a⁻¹ * b) by group, h1, mul_one]
      exact Subgroup.mem_zpowers a
    · have h1 := hfin _ hyP (k0' (Or.inl ⟨hα1, hβ1⟩)) (k1' (Or.inl ⟨hα1, hβ1⟩))
        (k2' (Or.inl ⟨hα1, hβ1⟩))
      apply hb_a
      rw [show b = (a * a) * ((a * a)⁻¹ * b) by group, h1, mul_one]
      exact Subgroup.mul_mem _ (Subgroup.mem_zpowers a) (Subgroup.mem_zpowers a)
    · have h1 := hfin _ hyP (k0' (Or.inr ⟨hα1, hβ1⟩)) (k1' (Or.inr ⟨hα1, hβ1⟩))
        (k2' (Or.inr ⟨hα1, hβ1⟩))
      apply hb_a
      rw [show b = (a * a) * ((a * a)⁻¹ * b) by group, h1, mul_one]
      exact Subgroup.mul_mem _ (Subgroup.mem_zpowers a) (Subgroup.mem_zpowers a)
    · have h1 := hfin _ hxP (k0 (Or.inr ⟨hα1, hβ1⟩)) (k1 (Or.inr ⟨hα1, hβ1⟩))
        (k2 (Or.inr ⟨hα1, hβ1⟩))
      apply hb_a
      rw [show b = a * (a⁻¹ * b) by group, h1, mul_one]
      exact Subgroup.mem_zpowers a

end Cyc

end Ctx

end N1246

end CFSG.Quasithin.H13
