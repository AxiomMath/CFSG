module

public import CFSG.GH74.Generic.S45.GL42

public section

namespace CFSG.GH74.Generic.S45

open Subgroup MulAction

section Prelim

variable {R : Type} [Group R]

theorem card_range_mul_card_ker {G N : Type*} [Group G] [Group N] [Finite G] (h : G →* N) :
    Nat.card h.range * Nat.card h.ker = Nat.card G := by
  have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup h.ker
  have e := Nat.card_congr (QuotientGroup.quotientKerEquivRange h).toEquiv
  rw [← e]
  exact h1.symm

theorem card_le_two_of_forall (S : Subgroup R) (r₀ : R)
    (hS : ∀ x ∈ S, x = 1 ∨ x = r₀) : Nat.card S ≤ 2 := by
  have hsub : (S : Set R) ⊆ {1, r₀} := by
    intro x hx
    rcases hS x hx with h | h
    · exact Or.inl h
    · exact Or.inr h
  have h1 := Set.ncard_le_ncard hsub (Set.toFinite _)
  have h2 : ({1, r₀} : Set R).ncard ≤ 2 := by
    calc ({1, r₀} : Set R).ncard ≤ ({r₀} : Set R).ncard + 1 := Set.ncard_insert_le _ _
      _ = 2 := by rw [Set.ncard_singleton]
  have h3 : (S : Set R).ncard = Nat.card S := (Nat.card_coe_set_eq (S : Set R)).symm
  omega

theorem card_ne_one_ne [Finite R] (r₀ : R) (hr₀ : r₀ ≠ 1) :
    Nat.card {x : R // x ≠ 1 ∧ x ≠ r₀} + 2 = Nat.card R := by
  classical
  have : Fintype R := Fintype.ofFinite R
  rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, Fintype.card_subtype]
  have h : (Finset.univ.filter (fun x : R => x ≠ 1 ∧ x ≠ r₀)) =
      (Finset.univ.erase 1).erase r₀ := by
    ext x; simp [and_comm]
  rw [h, Finset.card_erase_of_mem (by simp [hr₀]), Finset.card_erase_of_mem (by simp)]
  have : 0 < Fintype.card R := Fintype.card_pos
  have h2 : 2 ≤ Fintype.card R := by
    have : ({1, r₀} : Finset R).card ≤ Fintype.card R := Finset.card_le_univ _
    rw [Finset.card_pair (Ne.symm hr₀)] at this
    exact this
  simp only [Finset.card_univ]
  omega

theorem card_ne_one_aux [Finite R] : Nat.card {y : R // y ≠ 1} + 1 = Nat.card R := by
  have : Fintype R := Fintype.ofFinite R
  classical
  rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, Fintype.card_subtype_compl]
  have h1 : Fintype.card {y : R // y = 1} = 1 := Fintype.card_subtype_eq 1
  have h2 : 0 < Fintype.card R := Fintype.card_pos
  rw [h1]
  omega

end Prelim

section AutE8

variable {R : Type} [Group R] [Finite R]

theorem key7' : ∀ c : ℕ, c ∣ 8 → 8 ≡ c [MOD 7] → c = 1 ∨ c = 8 := by
  intro c h2 h1
  have hle : c ≤ 8 := Nat.le_of_dvd (by norm_num) h2
  have hc0 : 0 < c := Nat.pos_of_dvd_of_pos h2 (by norm_num)
  unfold Nat.ModEq at h1
  interval_cases c <;> omega

theorem key5' : ∀ c : ℕ, c ∣ 8 → 8 ≡ c [MOD 5] → c = 8 := by
  intro c h2 h1
  have hle : c ≤ 8 := Nat.le_of_dvd (by norm_num) h2
  have hc0 : 0 < c := Nat.pos_of_dvd_of_pos h2 (by norm_num)
  unfold Nat.ModEq at h1
  interval_cases c <;> omega

theorem fix_seven_eight (hR : Nat.card R = 8) (g : MulAut R) (hg : orderOf g = 7) (t : R)
    (ht : g t = t) : t = 1 := by
  have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  have h1 := card_fixSub_modEq g 7 hg
  rw [hR] at h1
  have h2 : Nat.card ↥(fixSub (zpowers g)) ∣ 8 := hR ▸ Subgroup.card_subgroup_dvd_card _
  rcases key7' _ h2 h1 with h3 | h3
  · have hbot : fixSub (zpowers g) = ⊥ := Subgroup.card_eq_one.1 h3
    have := fix_mem_zpowers ht
    rw [hbot] at this
    exact (Subgroup.mem_bot).1 this
  · exfalso
    have htop : fixSub (zpowers g) = ⊤ := by
      rw [← Subgroup.card_eq_iff_eq_top, hR]
      exact h3
    have : g = 1 := fix_eq_top_imp_one g htop
    rw [this, orderOf_one] at hg
    omega

theorem orderOf_ne_five_eight (hR : Nat.card R = 8) (g : MulAut R) : orderOf g ≠ 5 := by
  intro hg
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have h1 := card_fixSub_modEq g 5 hg
  rw [hR] at h1
  have h2 : Nat.card ↥(fixSub (zpowers g)) ∣ 8 := hR ▸ Subgroup.card_subgroup_dvd_card _
  have h3 := key5' _ h2 h1
  have htop : fixSub (zpowers g) = ⊤ := by
    rw [← Subgroup.card_eq_iff_eq_top, hR]
    exact h3
  have : g = 1 := fix_eq_top_imp_one g htop
  rw [this, orderOf_one] at hg
  omega

theorem exists_ne_one_of_card (hR : Nat.card R = 8) : ∃ r₀ : R, r₀ ≠ 1 := by
  have : Nontrivial R := (Finite.one_lt_card_iff_nontrivial (α := R)).1 (by omega)
  obtain ⟨r, hr⟩ := exists_ne (1 : R)
  exact ⟨r, hr⟩

theorem exists_zpowers_apply_eq (hR : Nat.card R = 8) {a : MulAut R} (ha : orderOf a = 7)
    {r s : R} (hr : r ≠ 1) (hs : s ≠ 1) : ∃ g ∈ zpowers a, g r = s := by
  have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  have hPcard : Nat.card ↥(zpowers a) = 7 := by rw [Nat.card_zpowers, ha]
  have hord7 : ∀ g ∈ zpowers a, g ≠ 1 → orderOf g = 7 := by
    intro g hg hg1
    have h1 : orderOf g ∣ 7 := hPcard ▸ Subgroup.orderOf_dvd_natCard (zpowers a) hg
    exact ((Nat.dvd_prime Fact.out).1 h1).resolve_left (fun h => hg1 (orderOf_eq_one_iff.1 h))
  have hPfree : ∀ g ∈ zpowers a, g ≠ 1 → ∀ t : R, g t = t → t = 1 := fun g hg hg1 t ht =>
    fix_seven_eight hR g (hord7 g hg hg1) t ht
  have h7 : Nat.card {x : R // x ≠ 1} = 7 := by
    have := card_ne_one_aux (R := R)
    omega
  let ψ : ↥(zpowers a) → {x : R // x ≠ 1} := fun g => ⟨(g : MulAut R) r, by
    intro h
    apply hr
    have : (g : MulAut R) r = (g : MulAut R) 1 := by rw [h, map_one]
    exact (g : MulAut R).injective this⟩
  have hinj : Function.Injective ψ := by
    intro g g' hgg
    have h1 : (g : MulAut R) r = (g' : MulAut R) r := congrArg Subtype.val hgg
    have h2 : ((g' : MulAut R)⁻¹ * (g : MulAut R)) r = r := by
      rw [MulAut.mul_apply, h1]
      exact MulAut.inv_apply_self _ _ _
    have hmem : ((g' : MulAut R)⁻¹ * (g : MulAut R)) ∈ zpowers a :=
      mul_mem (inv_mem g'.2) g.2
    by_contra hne
    have hne' : ((g' : MulAut R)⁻¹ * (g : MulAut R)) ≠ 1 := by
      intro h
      apply hne
      apply Subtype.ext
      exact (inv_mul_eq_one.1 h).symm
    exact hr (hPfree _ hmem hne' r h2)
  have hbij : Function.Bijective ψ :=
    hinj.bijective_of_nat_card_le (by rw [h7, hPcard])
  obtain ⟨g, hg⟩ := hbij.2 ⟨s, hs⟩
  exact ⟨(g : MulAut R), g.2, congrArg Subtype.val hg⟩

theorem card_le_21 (hR : Nat.card R = 8) (hsq : ∀ x : R, x * x = 1) {A : Subgroup (MulAut R)}
    {a : MulAut R} (ha : orderOf a = 7) (haA : a ∈ A)
    (hnorm : ∀ f ∈ A, f * a * f⁻¹ ∈ zpowers a) : Nat.card A ≤ 21 := by
  classical
  have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  have hinv : ∀ x : R, x⁻¹ = x := fun x => inv_eq_of_mul_eq_one_right (hsq x)
  have hcomm : ∀ x y : R, x * y = y * x := by
    intro x y
    calc x * y = (x * y)⁻¹ := (hinv _).symm
      _ = y⁻¹ * x⁻¹ := mul_inv_rev x y
      _ = y * x := by rw [hinv, hinv]
  have hPcard : Nat.card ↥(zpowers a) = 7 := by rw [Nat.card_zpowers, ha]
  have hPle : zpowers a ≤ A := by rw [zpowers_le]; exact haA
  have hord7 : ∀ g ∈ zpowers a, g ≠ 1 → orderOf g = 7 := by
    intro g hg hg1
    have h1 : orderOf g ∣ 7 := hPcard ▸ Subgroup.orderOf_dvd_natCard (zpowers a) hg
    exact ((Nat.dvd_prime Fact.out).1 h1).resolve_left (fun h => hg1 (orderOf_eq_one_iff.1 h))
  have hPfree : ∀ g ∈ zpowers a, g ≠ 1 → ∀ t : R, g t = t → t = 1 := fun g hg hg1 t ht =>
    fix_seven_eight hR g (hord7 g hg hg1) t ht
  obtain ⟨r₀, hr₀⟩ := exists_ne_one_of_card hR
  have h7 : Nat.card {x : R // x ≠ 1} = 7 := by
    have := card_ne_one_aux (R := R)
    omega
  have hreg : ∀ s : R, s ≠ 1 → ∃ g ∈ zpowers a, g r₀ = s := fun s hs =>
    exists_zpowers_apply_eq hR ha hr₀ hs
  have hnormP : ∀ f ∈ A, ∀ g ∈ zpowers a, f * g * f⁻¹ ∈ zpowers a := by
    intro f hf g hg
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 hg
    have h : f * a ^ k * f⁻¹ = (f * a * f⁻¹) ^ k := by simp
    rw [h]
    exact zpow_mem (hnorm f hf) k
  have hOrb : (MulAction.orbit ↥A r₀).ncard = 7 := by
    have hOeq : (MulAction.orbit ↥A r₀ : Set R) = {x | x ≠ 1} := by
      ext y
      constructor
      · rintro ⟨f, rfl⟩ h
        apply hr₀
        have : ((f : ↥A) : MulAut R) r₀ = ((f : ↥A) : MulAut R) 1 := by
          rw [map_one]; exact h
        exact ((f : ↥A) : MulAut R).injective this
      · intro hy
        obtain ⟨g, hg, hgy⟩ := hreg y hy
        exact ⟨⟨g, hPle hg⟩, hgy⟩
    rw [hOeq, ← Nat.card_coe_set_eq]
    exact h7
  have hA7 : Nat.card ↥(MulAction.stabilizer ↥A r₀) * 7 = Nat.card ↥A := by
    have h1 := Subgroup.card_mul_index (MulAction.stabilizer ↥A r₀)
    rw [MulAction.index_stabilizer, hOrb] at h1
    exact h1
  have hfree : ∀ f : ↥A, (f : MulAut R) r₀ = r₀ → ∀ s : R, s ≠ 1 → s ≠ r₀ →
      (f : MulAut R) s = s → f = 1 := by
    intro f hfr s hs1 hsr hfs
    obtain ⟨g, hg, hgs⟩ := hreg s hs1
    have hg1 : g ≠ 1 := by
      intro h
      apply hsr
      rw [← hgs, h, MulAut.one_apply]
    have hg'mem : (f : MulAut R) * g * (f : MulAut R)⁻¹ ∈ zpowers a := hnormP f f.2 g hg
    have hfinv : (f : MulAut R)⁻¹ r₀ = r₀ := by
      conv_lhs => rw [← hfr]
      exact MulAut.inv_apply_self _ _ _
    have hg'r : ((f : MulAut R) * g * (f : MulAut R)⁻¹) r₀ = s := by
      simp only [MulAut.mul_apply]
      rw [hfinv, hgs, hfs]
    have hcomm1 : (f : MulAut R) * g * (f : MulAut R)⁻¹ = g := by
      have h1 : (g⁻¹ * ((f : MulAut R) * g * (f : MulAut R)⁻¹)) r₀ = r₀ := by
        rw [MulAut.mul_apply, hg'r, ← hgs]
        exact MulAut.inv_apply_self _ _ _
      have hm : g⁻¹ * ((f : MulAut R) * g * (f : MulAut R)⁻¹) ∈ zpowers a :=
        mul_mem (inv_mem hg) hg'mem
      by_contra hne
      have hne' : g⁻¹ * ((f : MulAut R) * g * (f : MulAut R)⁻¹) ≠ 1 := by
        intro h; apply hne; exact (inv_mul_eq_one.1 h).symm
      exact hr₀ (hPfree _ hm hne' r₀ h1)
    have hfg : (f : MulAut R) * g = g * (f : MulAut R) := by
      have := congrArg (fun u => u * (f : MulAut R)) hcomm1
      simpa [mul_assoc] using this
    have hzg : zpowers g = zpowers a := by
      apply Subgroup.eq_of_le_of_card_ge
      · rw [zpowers_le]; exact hg
      · rw [Nat.card_zpowers, Nat.card_zpowers, ha, hord7 g hg hg1]
    have hafg : a ∈ zpowers g := by rw [hzg]; exact mem_zpowers a
    have hfa : (f : MulAut R) * a = a * (f : MulAut R) := by
      obtain ⟨m, hm⟩ := mem_zpowers_iff.1 hafg
      rw [← hm]
      exact (Commute.zpow_right (show Commute (f : MulAut R) g from hfg) m).eq
    have hfix : ∀ t : R, (f : MulAut R) t = t := by
      intro t
      by_cases ht : t = 1
      · rw [ht, map_one]
      · obtain ⟨h, hh, hht⟩ := hreg t ht
        have hfh : (f : MulAut R) * h = h * (f : MulAut R) := by
          obtain ⟨k, hk⟩ := mem_zpowers_iff.1 hh
          rw [← hk]
          exact (Commute.zpow_right (show Commute (f : MulAut R) a from hfa) k).eq
        have := congrArg (fun u : MulAut R => u r₀) hfh
        simp only [MulAut.mul_apply] at this
        rw [hfr] at this
        rw [← hht]; exact this
    apply Subtype.ext
    exact MulEquiv.ext hfix
  have hD6 : Nat.card ↥(MulAction.stabilizer ↥A r₀) ≤ 6 := by
    obtain ⟨s₁, hs₁1, hs₁r⟩ : ∃ s₁ : R, s₁ ≠ 1 ∧ s₁ ≠ r₀ := by
      have h6 := card_ne_one_ne r₀ hr₀
      have hpos : 0 < Nat.card {x : R // x ≠ 1 ∧ x ≠ r₀} := by omega
      obtain ⟨⟨x, hx⟩⟩ := (Nat.card_pos_iff.1 hpos).1
      exact ⟨x, hx.1, hx.2⟩
    have hmem : ∀ f : ↥(MulAction.stabilizer ↥A r₀), ((f : ↥A) : MulAut R) r₀ = r₀ := fun f =>
      MulAction.mem_stabilizer_iff.1 f.2
    let φ : ↥(MulAction.stabilizer ↥A r₀) → {x : R // x ≠ 1 ∧ x ≠ r₀} := fun f =>
      ⟨((f : ↥A) : MulAut R) s₁, by
        intro h
        apply hs₁1
        have : ((f : ↥A) : MulAut R) s₁ = ((f : ↥A) : MulAut R) 1 := by rw [h, map_one]
        exact ((f : ↥A) : MulAut R).injective this, by
        intro h
        apply hs₁r
        have : ((f : ↥A) : MulAut R) s₁ = ((f : ↥A) : MulAut R) r₀ := by rw [h, hmem f]
        exact ((f : ↥A) : MulAut R).injective this⟩
    have hinj : Function.Injective φ := by
      intro f f' hff
      have h1 : ((f : ↥A) : MulAut R) s₁ = ((f' : ↥A) : MulAut R) s₁ := congrArg Subtype.val hff
      have hf'inv : ((f' : ↥A) : MulAut R)⁻¹ r₀ = r₀ := by
        have := MulAut.inv_apply_self _ ((f' : ↥A) : MulAut R) r₀
        rwa [hmem f'] at this
      have h2 : (((f' : ↥A)⁻¹ * (f : ↥A) : ↥A) : MulAut R) r₀ = r₀ := by
        simp only [Subgroup.coe_mul, Subgroup.coe_inv, MulAut.mul_apply]
        rw [hmem f]
        exact hf'inv
      have h3 : (((f' : ↥A)⁻¹ * (f : ↥A) : ↥A) : MulAut R) s₁ = s₁ := by
        simp only [Subgroup.coe_mul, Subgroup.coe_inv, MulAut.mul_apply]
        rw [h1]
        exact MulAut.inv_apply_self _ _ _
      have h4 := hfree _ h2 s₁ hs₁1 hs₁r h3
      apply Subtype.ext
      exact (inv_mul_eq_one.1 h4).symm
    have := Nat.card_le_card_of_injective φ hinj
    have h6 := card_ne_one_ne r₀ hr₀
    omega
  have hnoinv : ∀ f : ↥A, (f : MulAut R) r₀ = r₀ → f * f = 1 → f = 1 := by
    intro f hfr hff
    by_contra hf1
    have hfix : ∀ x : R, (f : MulAut R) x = x → x = 1 ∨ x = r₀ := by
      intro x hx
      by_contra hcon
      push Not at hcon
      exact hf1 (hfree f hfr x hcon.1 hcon.2 hx)
    have hff' : ∀ x : R, (f : MulAut R) ((f : MulAut R) x) = x := by
      intro x
      have := congrArg (fun u : ↥A => (u : MulAut R) x) hff
      simpa using this
    let hh : R →* R :=
      { toFun := fun x => x * (f : MulAut R) x
        map_one' := by simp
        map_mul' := by
          intro x y
          simp only [map_mul]
          calc x * y * ((f : MulAut R) x * (f : MulAut R) y)
              = x * (y * (f : MulAut R) x) * (f : MulAut R) y := by group
            _ = x * ((f : MulAut R) x * y) * (f : MulAut R) y := by
                rw [hcomm y ((f : MulAut R) x)]
            _ = x * (f : MulAut R) x * (y * (f : MulAut R) y) := by group }
    have hker : ∀ x ∈ hh.ker, x = 1 ∨ x = r₀ := by
      intro x hx
      apply hfix
      have h1 : x * (f : MulAut R) x = 1 := hx
      have h2 : (f : MulAut R) x = x⁻¹ := eq_inv_of_mul_eq_one_right h1
      rw [h2, hinv]
    have hrange : ∀ x ∈ hh.range, x = 1 ∨ x = r₀ := by
      rintro _ ⟨y, rfl⟩
      apply hfix
      show (f : MulAut R) (y * (f : MulAut R) y) = y * (f : MulAut R) y
      rw [map_mul, hff', hcomm]
    have hc1 := card_le_two_of_forall hh.ker r₀ hker
    have hc2 := card_le_two_of_forall hh.range r₀ hrange
    have hc3 := card_range_mul_card_ker hh
    rw [hR] at hc3
    have := Nat.mul_le_mul hc2 hc1
    omega
  have hDodd : ¬ 2 ∣ Nat.card ↥(MulAction.stabilizer ↥A r₀) := by
    intro h2
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    obtain ⟨f, hf⟩ := exists_prime_orderOf_dvd_card'
      (G := ↥(MulAction.stabilizer ↥A r₀)) 2 h2
    have hf2 : f * f = 1 := by
      rw [← pow_two, ← hf]
      exact pow_orderOf_eq_one f
    have hmem : ((f : ↥A) : MulAut R) r₀ = r₀ := MulAction.mem_stabilizer_iff.1 f.2
    have h1 : (f : ↥A) = 1 := by
      apply hnoinv (f : ↥A) hmem
      have := congrArg (fun u : ↥(MulAction.stabilizer ↥A r₀) => (u : ↥A)) hf2
      simpa using this
    have : f = 1 := Subtype.ext h1
    rw [this, orderOf_one] at hf
    omega
  have hD5 : ¬ 5 ∣ Nat.card ↥(MulAction.stabilizer ↥A r₀) := by
    intro h5
    have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
    obtain ⟨f, hf⟩ := exists_prime_orderOf_dvd_card'
      (G := ↥(MulAction.stabilizer ↥A r₀)) 5 h5
    apply orderOf_ne_five_eight hR ((f : ↥A) : MulAut R)
    rw [Subgroup.orderOf_coe, Subgroup.orderOf_coe, hf]
  have hpos : 0 < Nat.card ↥(MulAction.stabilizer ↥A r₀) := Nat.card_pos
  omega

end AutE8

section Order21

theorem mem_zpowers_of_card_21 {G : Type*} [Group G] [Finite G] (hG : Nat.card G = 21) {a c : G}
    (ha : orderOf a = 7) (hc : orderOf c = 7) : c ∈ zpowers a := by
  have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  have hidx : ∀ g : G, orderOf g = 7 → ¬ 7 ∣ (zpowers g).index := by
    intro g hg
    have h1 := Subgroup.card_mul_index (zpowers g)
    rw [Nat.card_zpowers, hg, hG] at h1
    have h3 : (zpowers g).index = 3 := by omega
    rw [h3]; norm_num
  have hPg : ∀ g : G, orderOf g = 7 → IsPGroup 7 ↥(zpowers g) := fun g hg =>
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hg, pow_one])
  let Pa : Sylow 7 G := (hPg a ha).toSylow (hidx a ha)
  let Pc : Sylow 7 G := (hPg c hc).toSylow (hidx c hc)
  have hn : Nat.card (Sylow 7 G) = 1 := by
    have h1 : Nat.card (Sylow 7 G) ≡ 1 [MOD 7] := card_sylow_modEq_one 7 G
    have h2 : Nat.card (Sylow 7 G) ∣ (Pa : Subgroup G).index := Pa.card_dvd_index
    have h3 : (Pa : Subgroup G).index = 3 := by
      have := Subgroup.card_mul_index (zpowers a)
      rw [Nat.card_zpowers, ha, hG] at this
      have h4 : (zpowers a).index = 3 := by omega
      exact h4
    rw [h3] at h2
    have hle : Nat.card (Sylow 7 G) ≤ 3 := Nat.le_of_dvd (by norm_num) h2
    have hpos : 0 < Nat.card (Sylow 7 G) := Nat.pos_of_dvd_of_pos h2 (by norm_num)
    unfold Nat.ModEq at h1
    generalize Nat.card (Sylow 7 G) = n at *
    interval_cases n <;> omega
  have hsub : Subsingleton (Sylow 7 G) := (Nat.card_eq_one_iff_unique.1 hn).1
  have hPP : Pa = Pc := Subsingleton.elim _ _
  have hz : zpowers a = zpowers c := congrArg (fun P : Sylow 7 G => (P : Subgroup G)) hPP
  rw [hz]
  exact mem_zpowers c

theorem mem_zpowers_of_subgroup_card_21 {G : Type*} [Group G] [Finite G] {B : Subgroup G}
    (hB : Nat.card B = 21) {a c : G} (haB : a ∈ B) (hcB : c ∈ B) (ha : orderOf a = 7)
    (hc : orderOf c = 7) : c ∈ zpowers a := by
  have h := mem_zpowers_of_card_21 hB (a := (⟨a, haB⟩ : B)) (c := ⟨c, hcB⟩)
    (by rw [← ha]; exact Subgroup.orderOf_mk a haB) (by rw [← hc]; exact Subgroup.orderOf_mk c hcB)
  obtain ⟨k, hk⟩ := mem_zpowers_iff.1 h
  exact mem_zpowers_iff.2 ⟨k, congrArg Subtype.val hk⟩

theorem orderOf_conj_eq {G : Type*} [Group G] (f b : G) : orderOf (f * b * f⁻¹) = orderOf b := by
  have h := orderOf_injective (MulAut.conj f).toMonoidHom (MulAut.conj f).injective b
  simpa [MulAut.conj_apply] using h

end Order21

end CFSG.GH74.Generic.S45
