module

public import CFSG.LocalAnalysis.EvenSporadicStandard.M24Std.GenXTransfer

public section

namespace CFSG.EvenSporadicStandard.M24Std.GenX

open Subgroup CFSG.EvenSporadicStandard

variable {G : Type*} [Group G]

theorem false_of_wreath' [Finite G] {z : G} (hGz : ∀ ψ : G →* ℤˣ, ψ z = 1)
    (hord : orderOf z = 2)
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
  exact false_of_fusion_control' hGz hz hw.sub hzH φ hφz hfuse hodd

end CFSG.EvenSporadicStandard.M24Std.GenX
