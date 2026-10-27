module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Common.Basic
public import CFSG.LocalAnalysis.EvenSporadicStandard.M24Std.FusionControl

public section

namespace CFSG.EvenSporadicStandard

open Subgroup

variable {G : Type*} [Group G]

theorem exists_hom_of_index_two {H : Type*} [Group H] (K : Subgroup H) (hK : K.index = 2) :
    ∃ φ : H →* ℤˣ, ∀ h, φ h = 1 ↔ h ∈ K := by
  have : K.Normal := Subgroup.normal_of_index_eq_two hK
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hcard : Nat.card (H ⧸ K) = 2 := by
    rw [← Subgroup.index_eq_card]
    exact hK
  let e : H ⧸ K ≃* ℤˣ := mulEquivOfPrimeCardEq (p := 2) hcard card_units_int
  refine ⟨e.toMonoidHom.comp (QuotientGroup.mk' K), fun h => ?_⟩
  simp only [MonoidHom.coe_comp, MulEquiv.coe_toMonoidHom, Function.comp_apply,
    QuotientGroup.mk'_apply]
  rw [← map_one e, e.injective.eq_iff]
  exact QuotientGroup.eq_one_iff h

structure WreathPair (z : G) (R S : Subgroup G) : Prop where
  sq : z * z = 1
  comm : ∀ a ∈ R, ∀ b ∈ S, a * b = b * a
  disj : ∀ x ∈ R, x ∈ S → x = 1
  conjR : ∀ a ∈ R, z * a * z⁻¹ ∈ S
  conjS : ∀ b ∈ S, z * b * z⁻¹ ∈ R

namespace WreathPair

variable {z : G} {R S : Subgroup G}

theorem inv_eq (hw : WreathPair z R S) : z⁻¹ = z := inv_eq_of_mul_eq_one_right hw.sq

theorem mul_eq_mul_iff (hw : WreathPair z R S) {r r' s s' : G} (hr : r ∈ R) (hr' : r' ∈ R)
    (hs : s ∈ S) (hs' : s' ∈ S) (h : r * s = r' * s') : r = r' ∧ s = s' := by
  have h1 : r'⁻¹ * r = s' * s⁻¹ := by
    calc r'⁻¹ * r = r'⁻¹ * (r * s) * s⁻¹ := by group
      _ = r'⁻¹ * (r' * s') * s⁻¹ := by rw [h]
      _ = s' * s⁻¹ := by group
  have h2 : r'⁻¹ * r = 1 :=
    hw.disj _ (mul_mem (inv_mem hr') hr) (h1 ▸ mul_mem hs' (inv_mem hs))
  have h3 : r = r' := by
    have := congrArg (r' * ·) h2
    simpa using this
  refine ⟨h3, ?_⟩
  subst h3
  exact mul_left_cancel h

theorem mem_sup (hw : WreathPair z R S) {x : G} :
    x ∈ R ⊔ S ↔ ∃ r ∈ R, ∃ s ∈ S, x = r * s :=
  ⟨fun hx => exists_mul_of_mem_sup_of_le_centralizer
    (fun b hb => mem_centralizer_iff.2 fun a ha => hw.comm a ha b hb) hx,
   by
    rintro ⟨r, hr, s, hs, rfl⟩
    exact Subgroup.mul_mem_sup hr hs⟩

theorem conj_mem (hw : WreathPair z R S) {x : G} (hx : x ∈ R ⊔ S) : z * x * z⁻¹ ∈ R ⊔ S := by
  obtain ⟨r, hr, s, hs, rfl⟩ := hw.mem_sup.1 hx
  have : z * (r * s) * z⁻¹ = (z * r * z⁻¹) * (z * s * z⁻¹) := by group
  rw [this]
  exact mul_mem (Subgroup.mem_sup_right (hw.conjR r hr)) (Subgroup.mem_sup_left (hw.conjS s hs))

theorem eq_of_conj_eq (hw : WreathPair z R S) {r s : G} (hr : r ∈ R) (hs : s ∈ S)
    (h : z * (r * s) * z⁻¹ = r * s) : z * s * z⁻¹ = r ∧ z * r * z⁻¹ = s := by
  have h1 : (z * s * z⁻¹) * (z * r * z⁻¹) = r * s := by
    have hc := hw.comm (z * s * z⁻¹) (hw.conjS s hs) (z * r * z⁻¹) (hw.conjR r hr)
    rw [hc, ← h]
    group
  exact hw.mul_eq_mul_iff (hw.conjS s hs) hr (hw.conjR r hr) hs h1

theorem z_not_mem (hw : WreathPair z R S) (hz1 : z ≠ 1) : z ∉ R ⊔ S := by
  intro hzΛ
  obtain ⟨r, hr, s, hs, hrs⟩ := hw.mem_sup.1 hzΛ
  have hfix : z * (r * s) * z⁻¹ = r * s := by
    rw [← hrs, hw.inv_eq, hw.sq, one_mul]
  obtain ⟨-, h2⟩ := hw.eq_of_conj_eq hr hs hfix
  have h3 : z = r * (z * r * z⁻¹) := by rw [h2]; exact hrs
  have h4 : r * z * r = 1 := by
    calc r * z * r = (r * (z * r * z⁻¹)) * z := by group
      _ = z * z := by rw [← h3]
      _ = 1 := hw.sq
  have hzR : z ∈ R := by
    have : z = r⁻¹ * r⁻¹ := by
      calc z = r⁻¹ * (r * z * r) * r⁻¹ := by group
        _ = r⁻¹ * r⁻¹ := by rw [h4]; group
    rw [this]
    exact mul_mem (inv_mem hr) (inv_mem hr)
  have hzS : z ∈ S := by
    have := hw.conjR z hzR
    have e : z * z * z⁻¹ = z := by rw [hw.sq, one_mul, hw.inv_eq]
    rwa [e] at this
  exact hz1 (hw.disj z hzR hzS)

@[expose] def sub (hw : WreathPair z R S) : Subgroup G where
  carrier := {x | x ∈ R ⊔ S ∨ x * z ∈ R ⊔ S}
  one_mem' := Or.inl (one_mem _)
  mul_mem' := by
    rintro x y (hx | hx) (hy | hy)
    · exact Or.inl (mul_mem hx hy)
    · refine Or.inr ?_
      rw [mul_assoc]
      exact mul_mem hx hy
    · refine Or.inr ?_
      have e : z * y * z⁻¹ = z⁻¹ * y * z := by rw [hw.inv_eq]
      have : x * y * z = (x * z) * (z * y * z⁻¹) := by rw [e]; group
      rw [this]
      exact mul_mem hx (hw.conj_mem hy)
    · refine Or.inl ?_
      have : x * y = (x * z) * (z * (y * z) * z⁻¹) := by
        calc x * y = x * (z * z) * y := by rw [hw.sq, mul_one]
          _ = _ := by group
      rw [this]
      exact mul_mem hx (hw.conj_mem hy)
  inv_mem' := by
    rintro x (hx | hx)
    · exact Or.inl (inv_mem hx)
    · refine Or.inr ?_
      have h1 : z * x⁻¹ = (x * z)⁻¹ := by rw [mul_inv_rev, hw.inv_eq]
      have h2 : x⁻¹ * z = z * (z * x⁻¹) * z⁻¹ := by
        calc x⁻¹ * z = x⁻¹ * z⁻¹ := by rw [hw.inv_eq]
          _ = (z * z) * x⁻¹ * z⁻¹ := by rw [hw.sq, one_mul]
          _ = _ := by group
      rw [h2]
      refine hw.conj_mem ?_
      rw [h1]
      exact inv_mem hx

theorem mem_sub (hw : WreathPair z R S) {x : G} :
    x ∈ hw.sub ↔ x ∈ R ⊔ S ∨ x * z ∈ R ⊔ S := Iff.rfl


theorem diag_mul (hw : WreathPair z R S) {a b : G} (ha : a ∈ R) (hb : b ∈ R) :
    a * b * (z * (a * b) * z⁻¹) = (a * (z * a * z⁻¹)) * (b * (z * b * z⁻¹)) := by
  have hc := hw.comm b hb (z * a * z⁻¹) (hw.conjR a ha)
  calc a * b * (z * (a * b) * z⁻¹) = a * (b * (z * a * z⁻¹)) * (z * b * z⁻¹) := by group
    _ = a * ((z * a * z⁻¹) * b) * (z * b * z⁻¹) := by rw [hc]
    _ = _ := by group

@[expose] def diag (hw : WreathPair z R S) : R →* G :=
  MonoidHom.mk' (fun r : R => (r : G) * (z * (r : G) * z⁻¹)) fun a b => hw.diag_mul a.2 b.2

theorem diag_injective (hw : WreathPair z R S) : Function.Injective hw.diag := by
  rw [injective_iff_map_eq_one]
  intro r hr
  have h : (r : G) * (z * (r : G) * z⁻¹) = 1 * 1 := by
    rw [mul_one]
    exact hr
  exact Subtype.ext (hw.mul_eq_mul_iff r.2 (one_mem R) (hw.conjR r r.2) (one_mem S) h).1

theorem diag_mem (hw : WreathPair z R S) {r : G} (hr : r ∈ R) :
    r * (z * r * z⁻¹) ∈ R ⊔ S :=
  Subgroup.mul_mem_sup hr (hw.conjR r hr)

theorem diag_comm (hw : WreathPair z R S) {r : G} (hr : r ∈ R) :
    z * (r * (z * r * z⁻¹)) = (r * (z * r * z⁻¹)) * z := by
  calc z * (r * (z * r * z⁻¹)) = z * ((z * r * z⁻¹) * r) := by
        rw [hw.comm r hr _ (hw.conjR r hr)]
    _ = (z * z) * r * z⁻¹ * r := by group
    _ = r * z⁻¹ * r := by rw [hw.sq, one_mul]
    _ = r * z * r := by rw [hw.inv_eq]
    _ = (r * (z * r * z⁻¹)) * z := by group

end WreathPair

theorem eq_one_or_eq_of_orderOf_eq_two {x b : G} (hx : orderOf x = 2) (hb : b ∈ zpowers x) :
    b = 1 ∨ b = x := by
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hb
  have h := zpow_mod_orderOf x k
  rw [hx] at h
  rcases Int.emod_two_eq_zero_or_one k with h0 | h1
  · left
    rw [← h]
    simp [h0]
  · right
    rw [← h]
    simp [h1]

theorem false_of_wreath [Finite G] (hG : ∀ ψ : G →* ℤˣ, ψ = 1) {z : G} (hord : orderOf z = 2)
    {R : Subgroup G} {k m : ℕ} (hm : Odd m)
    (hC : Nat.card (centralizer ({z} : Set G)) = 2 ^ (k + 1) * m) (hR : Nat.card R = 2 ^ k)
    (hcomm : ∀ a ∈ R, ∀ b ∈ R, a * (z * b * z⁻¹) = (z * b * z⁻¹) * a)
    (hinter : ∀ a ∈ R, z * a * z⁻¹ ∈ R → a = 1) : False := by
  classical
  have hz : z * z = 1 := by rw [← pow_two, ← hord, pow_orderOf_eq_one]
  have hz1 : z ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hord
    exact absurd hord (by decide)
  have hzi : z⁻¹ = z := inv_eq_of_mul_eq_one_right hz
  have hzz : z⁻¹ * z⁻¹ = 1 := by rw [← mul_inv_rev, hz, inv_one]
  have hconj : ∀ x : G, z * (z * x * z⁻¹) * z⁻¹ = x := fun x => by
    rw [show z * (z * x * z⁻¹) * z⁻¹ = (z * z) * x * (z⁻¹ * z⁻¹) by group, hz, hzz]
    group
  let S : Subgroup G := R.comap (MulAut.conj z).toMonoidHom
  have hS : ∀ x, x ∈ S ↔ z * x * z⁻¹ ∈ R := fun x => by simp [S, Subgroup.mem_comap]
  have hw : WreathPair z R S :=
    { sq := hz
      comm := fun a ha b hb => by
        have hb' : z * b * z⁻¹ ∈ R := (hS b).1 hb
        have := hcomm a ha _ hb'
        rwa [hconj] at this
      disj := fun x hx hxS => hinter x hx ((hS x).1 hxS)
      conjR := fun a ha => (hS _).2 (by rw [hconj]; exact ha)
      conjS := fun b hb => (hS b).1 hb }
  have hzH : z ∈ hw.sub := hw.mem_sub.2 (Or.inr (by rw [hz]; exact one_mem _))
  have hΛH : R ⊔ S ≤ hw.sub := fun x hx => hw.mem_sub.2 (Or.inl hx)
  have hzΛ : z ∉ R ⊔ S := hw.z_not_mem hz1
  have hindex : ((R ⊔ S).subgroupOf hw.sub).index = 2 := by
    rw [Subgroup.index_eq_two_iff]
    refine ⟨⟨z, hzH⟩, fun b => ?_⟩
    by_cases hb : (b : G) ∈ R ⊔ S
    · right
      refine ⟨Subgroup.mem_subgroupOf.2 hb, fun h => hzΛ ?_⟩
      have h' : (b : G) * z ∈ R ⊔ S := Subgroup.mem_subgroupOf.1 h
      have := mul_mem (inv_mem hb) h'
      simpa using this
    · left
      refine ⟨Subgroup.mem_subgroupOf.2 ?_, fun h => hb (Subgroup.mem_subgroupOf.1 h)⟩
      exact (hw.mem_sub.1 b.2).resolve_left hb
  obtain ⟨φ, hφ⟩ := exists_hom_of_index_two _ hindex
  have hφz : φ ⟨z, hzH⟩ = -1 :=
    (Int.units_eq_one_or _).resolve_left fun h =>
      hzΛ (Subgroup.mem_subgroupOf.1 ((hφ _).1 h))
  have hfuse : ∀ y : hw.sub, φ y = -1 → (∃ g : G, g * z * g⁻¹ = y) →
      ∃ h ∈ hw.sub, h * z * h⁻¹ = y := by
    rintro ⟨y, hyH⟩ hφy ⟨g, hg⟩
    have hg' : g * z * g⁻¹ = y := hg
    have hyΛ : y ∉ R ⊔ S := by
      intro hy
      have h1 : φ ⟨y, hyH⟩ = 1 := (hφ _).2 (Subgroup.mem_subgroupOf.2 hy)
      rw [h1] at hφy
      exact absurd hφy (by decide)
    have hyz : y * z ∈ R ⊔ S := (hw.mem_sub.1 hyH).resolve_left hyΛ
    have hy2 : y * y = 1 := by
      rw [← hg']
      calc g * z * g⁻¹ * (g * z * g⁻¹) = g * (z * z) * g⁻¹ := by group
        _ = 1 := by rw [hz]; group
    obtain ⟨r, hr, s, hs, hrs⟩ := hw.mem_sup.1 hyz
    have hy' : y = r * s * z := by
      calc y = (y * z) * z⁻¹ := by group
        _ = (r * s) * z⁻¹ := by rw [hrs]
        _ = r * s * z := by rw [hzi]
    have hr' : z * r * z⁻¹ ∈ S := hw.conjR r hr
    have hs' : z * s * z⁻¹ ∈ R := hw.conjS s hs
    have h5 : r * s * (z * r * z⁻¹) * (z * s * z⁻¹) = 1 := by
      have e : r * s * z * (r * s * z) =
          r * s * (z * r * z⁻¹) * (z * s * z⁻¹) * (z * z) := by group
      rw [hz, mul_one, ← hy', hy2] at e
      exact e.symm
    have h6 : (r * (z * s * z⁻¹)) * (s * (z * r * z⁻¹)) = 1 * 1 := by
      have c1 := hw.comm _ hs' _ hr'
      have c2 := hw.comm _ hs' s hs
      calc (r * (z * s * z⁻¹)) * (s * (z * r * z⁻¹))
          = r * ((z * s * z⁻¹) * s) * (z * r * z⁻¹) := by group
        _ = r * (s * (z * s * z⁻¹)) * (z * r * z⁻¹) := by rw [c2]
        _ = r * s * ((z * s * z⁻¹) * (z * r * z⁻¹)) := by group
        _ = r * s * ((z * r * z⁻¹) * (z * s * z⁻¹)) := by rw [c1]
        _ = 1 * 1 := by
          rw [show r * s * ((z * r * z⁻¹) * (z * s * z⁻¹)) =
            r * s * (z * r * z⁻¹) * (z * s * z⁻¹) by group, h5, mul_one]
    obtain ⟨h7, -⟩ := hw.mul_eq_mul_iff (mul_mem hr hs') (one_mem R)
      (mul_mem hs (hw.conjR r hr)) (one_mem S) h6
    have key : z * s * z⁻¹ = r⁻¹ := eq_inv_of_mul_eq_one_right h7
    refine ⟨r, hΛH (Subgroup.mem_sup_left hr), ?_⟩
    calc r * z * r⁻¹ = r * z⁻¹ * r⁻¹ * (z * z) := by rw [hz, hzi]; group
      _ = r * (z⁻¹ * r⁻¹ * z) * z := by group
      _ = r * (z⁻¹ * (z * s * z⁻¹) * z) * z := by rw [key]
      _ = r * s * z := by group
      _ = y := hy'.symm
  let D : Subgroup G := hw.diag.range
  have hDcard : Nat.card D = 2 ^ k := by
    rw [← hR]
    exact (Nat.card_congr (MonoidHom.ofInjective hw.diag_injective).toEquiv).symm
  have hDz : ∀ d ∈ D, z * d = d * z := by
    rintro _ ⟨r, rfl⟩
    exact hw.diag_comm r.2
  have hDΛ : D ≤ R ⊔ S := by
    rintro _ ⟨r, rfl⟩
    exact hw.diag_mem r.2
  have hzD : zpowers z ≤ centralizer (D : Set G) := by
    rw [Subgroup.zpowers_le]
    exact mem_centralizer_iff.2 fun d hd => (hDz d hd).symm
  have hdisj : Disjoint D (zpowers z) := by
    rw [Subgroup.disjoint_def]
    intro x hxD hxz
    rcases eq_one_or_eq_of_orderOf_eq_two hord hxz with h | h
    · exact h
    · exfalso
      rw [h] at hxD
      exact hzΛ (hDΛ hxD)
  let P : Subgroup G := D ⊔ zpowers z
  have hPcard : Nat.card P = 2 ^ k * 2 := by
    have e := mulEquivProdSup hzD hdisj
    rw [← Nat.card_congr e.toEquiv, Nat.card_prod, Nat.card_zpowers, hord, hDcard]
  have hPC : P ≤ centralizer ({z} : Set G) := by
    refine sup_le ?_ ?_
    · intro d hd
      exact mem_centralizer_iff.2 fun h hh => by
        rw [Set.mem_singleton_iff.1 hh]
        exact hDz d hd
    · exact Subgroup.zpowers_le.2 (mem_centralizer_iff.2 fun h hh => by
        rw [Set.mem_singleton_iff.1 hh])
  have hPH : P ≤ hw.sub := sup_le (hDΛ.trans hΛH) (Subgroup.zpowers_le.2 hzH)
  have hrel : P.relIndex (centralizer ({z} : Set G)) = m := by
    have h1 := Subgroup.card_mul_index (P.subgroupOf (centralizer ({z} : Set G)))
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hPC).toEquiv, hPcard, hC] at h1
    have : 2 ^ k * 2 * (P.subgroupOf (centralizer ({z} : Set G))).index = 2 ^ k * 2 * m := by
      rw [h1, pow_succ]
    exact Nat.eq_of_mul_eq_mul_left (by positivity) this
  have hodd : ¬ 2 ∣ hw.sub.relIndex (centralizer ({z} : Set G)) := by
    intro h2
    have h3 : hw.sub.relIndex (centralizer ({z} : Set G)) ∣ m := by
      rw [← hrel]
      exact Subgroup.relIndex_dvd_of_le_left _ hPH
    exact (Nat.not_even_iff_odd.2 hm) (even_iff_two_dvd.2 (h2.trans h3))
  exact false_of_fusion_control hG hz hw.sub hzH φ hφz hfuse hodd

end CFSG.EvenSporadicStandard
