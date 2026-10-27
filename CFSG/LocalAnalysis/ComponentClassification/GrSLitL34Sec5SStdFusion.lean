module

public import CFSG.GroupTheory.LocalCores.Components
public import CFSG.GH74.GLS.Bg.Local.Transfer1515

public section

namespace CFSG.ComponentClassification.GrSLit.L34Sec5S

open CFSG Subgroup CFSG.GH74.GLS.Bg.Thompson
open scoped Pointwise

theorem commute_of_conj_eq_mul_of_isComponent {Y : Type*} [Group Y] [Finite Y]
    {K : Subgroup Y} (hK : IsComponent K) {t u x : Y} (htK : K ≤ centralizer ({t} : Set Y))
    (hperf : ∀ L : Subgroup Y, L ≤ centralizer ({t} : Set Y) → ⁅L, L⁆ = L → L ≤ K)
    (huK : u ∈ K) (hconj : x⁻¹ * t * x = u * t) : ∀ k ∈ K, u * k = k * u := by
  have htk : ∀ k ∈ K, t * k = k * t := fun k hk =>
    (mem_centralizer_singleton_iff.mp (htK hk)).symm
  set K' : Subgroup Y := K.map (MulAut.conj x⁻¹).toMonoidHom with hK'
  have hK'c : IsComponent K' := CFSG.LocalCores.isComponent_map_mulEquiv (MulAut.conj x⁻¹) hK
  have hmemK' : ∀ k ∈ K, x⁻¹ * k * x ∈ K' := fun k hk =>
    ⟨k, hk, by simp⟩
  have hK'mem : ∀ k' ∈ K', ∃ k ∈ K, k' = x⁻¹ * k * x := by
    rintro _ ⟨k, hk, rfl⟩
    exact ⟨k, hk, by simp⟩
  have hutK' : ∀ k' ∈ K', (u * t) * k' = k' * (u * t) := by
    intro k' hk'
    obtain ⟨k, hk, rfl⟩ := hK'mem k' hk'
    rw [← hconj]
    calc x⁻¹ * t * x * (x⁻¹ * k * x) = x⁻¹ * (t * k) * x := by group
      _ = x⁻¹ * (k * t) * x := by rw [htk k hk]
      _ = x⁻¹ * k * x * (x⁻¹ * t * x) := by group
  rcases CFSG.LocalCores.distinct_components_commute hK hK'c with heq | hcomm
  ·
    intro k hk
    have h1 : (u * t) * k = k * (u * t) := hutK' k (heq ▸ hk)
    have h2 : t * k = k * t := htk k hk
    calc u * k = (u * t) * k * t⁻¹ := by rw [mul_assoc u t k, h2]; group
      _ = k * (u * t) * t⁻¹ := by rw [h1]
      _ = k * u := by group
  ·
    exfalso
    have hcK' : ∀ k ∈ K, ∀ k' ∈ K', k * k' = k' * k := by
      intro k hk k' hk'
      have := Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcomm hk
      exact (mem_centralizer_iff.mp this k' hk').symm
    have htK' : K' ≤ centralizer ({t} : Set Y) := by
      intro k' hk'
      rw [mem_centralizer_singleton_iff]
      have h1 : (u * t) * k' = k' * (u * t) := hutK' k' hk'
      have h2 : u * k' = k' * u := hcK' u huK k' hk'
      have : t * k' = k' * t := by
        calc t * k' = u⁻¹ * ((u * t) * k') := by group
          _ = u⁻¹ * (k' * (u * t)) := by rw [h1]
          _ = u⁻¹ * (k' * u) * t := by group
          _ = u⁻¹ * (u * k') * t := by rw [h2]
          _ = k' * t := by group
      exact this.symm
    have hperfK' : ⁅K', K'⁆ = K' := Subgroup.isPerfect_iff.mp hK'c.1.1
    have hK'K : K' ≤ K := hperf K' htK' hperfK'
    have hbot : ⁅K', K'⁆ = ⊥ := by
      rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
      intro a ha
      rw [mem_centralizer_iff]
      intro b hb
      exact (hcK' a (hK'K ha) b hb).symm
    have hK'bot : K' = ⊥ := hperfK' ▸ hbot
    obtain ⟨-, -, a, b, hab⟩ := hK'c.1
    apply hab
    have hsub : Subsingleton ↥K' := by
      rw [hK'bot]
      infer_instance
    have : Subsingleton (↥K' ⧸ center ↥K') := by
      constructor
      intro p q
      obtain ⟨p, rfl⟩ := QuotientGroup.mk_surjective p
      obtain ⟨q, rfl⟩ := QuotientGroup.mk_surjective q
      rw [Subsingleton.elim p q]
    exact Subsingleton.elim _ _

theorem exists_mem_centralizer_conj_eq_mul_of_perfect {G : Type*} [Group G] {J Y : Subgroup G}
    {t u z g : G} (hJt : J ≤ centralizer ({t} : Set G))
    (hperf : ∀ L : Subgroup G, L ≤ centralizer ({t} : Set G) → ⁅L, L⁆ = L → L ≤ J)
    (hcls : ∀ a ∈ J, orderOf a = 2 → ∃ j ∈ J, a = j⁻¹ * z * j)
    (hY : ⁅Y, Y⁆ = Y) (hYJ : Y ≤ J) (hYu : Y ≤ centralizer ({u} : Set G)) (hzY : z ∈ Y)
    (hz : orderOf z = 2) (hg : g⁻¹ * t * g = u * t) :
    ∃ x ∈ centralizer ({z} : Set G), x⁻¹ * t * x = u * t := by
  set Y' : Subgroup G := Y.map (MulAut.conj g).toMonoidHom with hY'
  have hY'mem : ∀ y' ∈ Y', ∃ y ∈ Y, y' = g * y * g⁻¹ := by
    rintro _ ⟨y, hy, rfl⟩
    exact ⟨y, hy, by simp [MulAut.conj_apply]⟩
  have ht : t = g * (u * t) * g⁻¹ := by rw [← hg]; group
  have hY't : Y' ≤ centralizer ({t} : Set G) := by
    intro y' hy'
    obtain ⟨y, hy, rfl⟩ := hY'mem y' hy'
    rw [mem_centralizer_singleton_iff]
    have hyu : y * u = u * y := (mem_centralizer_singleton_iff.mp (hYu hy))
    have hyt : y * t = t * y := (mem_centralizer_singleton_iff.mp (hJt (hYJ hy)))
    have hyut : y * (u * t) = (u * t) * y := by
      calc y * (u * t) = (y * u) * t := by group
        _ = (u * y) * t := by rw [hyu]
        _ = u * (y * t) := by group
        _ = u * (t * y) := by rw [hyt]
        _ = (u * t) * y := by group
    rw [ht]
    calc g * y * g⁻¹ * (g * (u * t) * g⁻¹) = g * (y * (u * t)) * g⁻¹ := by group
      _ = g * ((u * t) * y) * g⁻¹ := by rw [hyut]
      _ = g * (u * t) * g⁻¹ * (g * y * g⁻¹) := by group
  have hY'perf : ⁅Y', Y'⁆ = Y' := by
    rw [hY', ← Subgroup.map_commutator, hY]
  have hY'J : Y' ≤ J := hperf Y' hY't hY'perf
  have hgz : g * z * g⁻¹ ∈ J := hY'J ⟨z, hzY, by simp [MulAut.conj_apply]⟩
  have hgzord : orderOf (g * z * g⁻¹) = 2 := by
    rw [show g * z * g⁻¹ = MulAut.conj g z by simp [MulAut.conj_apply], MulEquiv.orderOf_eq, hz]
  obtain ⟨j, hj, hjz⟩ := hcls _ hgz hgzord
  refine ⟨j * g, ?_, ?_⟩
  · rw [mem_centralizer_singleton_iff]
    have h1 : (j * g)⁻¹ * z * (j * g) = z := by
      calc (j * g)⁻¹ * z * (j * g) = g⁻¹ * (j⁻¹ * z * j) * g := by group
        _ = g⁻¹ * (g * z * g⁻¹) * g := by rw [← hjz]
        _ = z := by group
    calc (j * g) * z = (j * g) * ((j * g)⁻¹ * z * (j * g)) := by rw [h1]
      _ = z * (j * g) := by group
  · have hjt : j * t = t * j := (mem_centralizer_singleton_iff.mp (hJt hj))
    calc (j * g)⁻¹ * t * (j * g) = g⁻¹ * (j⁻¹ * (t * j)) * g := by group
      _ = g⁻¹ * (j⁻¹ * (j * t)) * g := by rw [hjt]
      _ = g⁻¹ * t * g := by group
      _ = u * t := hg

theorem commute_of_conj_eq_mul_of_centralizes {G : Type*} [Group G] {X K U : Subgroup G}
    {t u g : G} (hUX : ∀ x ∈ X, ∀ w ∈ U, x * w * x⁻¹ ∈ U)
    (hKX : ∀ x ∈ X, ∀ k ∈ K, ∃ k' ∈ K, ∃ w ∈ U, x * k * x⁻¹ = k' * w)
    (hKU : K ⊓ U = ⊥) (htX : t ∈ X) (htK : ∀ k ∈ K, t * k = k * t) (hgX : g ∈ X)
    (hu : u ∈ K) (hconj : g⁻¹ * t * g = u * t) : ∀ k ∈ K, u * k = k * u := by
  intro k hk
  obtain ⟨k', hk', w, hw, hgk⟩ := hKX g hgX k hk
  set w' := g⁻¹ * (w⁻¹ * (t * w * t⁻¹)) * g with hw'
  have hw'U : w' ∈ U := by
    have h1 : t * w * t⁻¹ ∈ U := hUX t htX w hw
    have h2 : g⁻¹ * (w⁻¹ * (t * w * t⁻¹)) * g⁻¹⁻¹ ∈ U :=
      hUX g⁻¹ (X.inv_mem hgX) _ (U.mul_mem (U.inv_mem hw) h1)
    rwa [inv_inv] at h2
  have hk_eq : k = g⁻¹ * (k' * w) * g := by rw [← hgk]; group
  have htk' : t * k' = k' * t := htK k' hk'
  have hconjk : (g⁻¹ * t * g) * k * (g⁻¹ * t * g)⁻¹ = k * w' := by
    rw [hk_eq, hw']
    calc g⁻¹ * t * g * (g⁻¹ * (k' * w) * g) * (g⁻¹ * t * g)⁻¹
        = g⁻¹ * ((t * k') * w * t⁻¹) * g := by group
      _ = g⁻¹ * ((k' * t) * w * t⁻¹) * g := by rw [htk']
      _ = g⁻¹ * (k' * w) * g * (g⁻¹ * (w⁻¹ * (t * w * t⁻¹)) * g) := by group
  have htk : t * k * t⁻¹ = k := by rw [htK k hk]; group
  have hut : (u * t) * k * (u * t)⁻¹ = u * k * u⁻¹ := by
    calc (u * t) * k * (u * t)⁻¹ = u * (t * k * t⁻¹) * u⁻¹ := by group
      _ = u * k * u⁻¹ := by rw [htk]
  rw [hconj, hut] at hconjk
  have hmemU : k⁻¹ * (u * k * u⁻¹) ∈ U := by
    rw [hconjk]
    simpa using hw'U
  have hmemK : k⁻¹ * (u * k * u⁻¹) ∈ K :=
    K.mul_mem (K.inv_mem hk) (K.mul_mem (K.mul_mem hu hk) (K.inv_mem hu))
  have h1 : k⁻¹ * (u * k * u⁻¹) = 1 := by
    have h := Subgroup.mem_inf.mpr ⟨hmemK, hmemU⟩
    rwa [hKU, Subgroup.mem_bot] at h
  calc u * k = k * (k⁻¹ * (u * k * u⁻¹)) * u := by group
    _ = k * u := by rw [h1, mul_one]

theorem exists_mem_centralizer_conj_of_isExtremalIn {G : Type*} [Group G] [Finite G]
    {P : Subgroup G} {t z g : G} (hzP : z ∈ P) (hzc : ∀ p ∈ P, p * z = z * p)
    (hz : orderOf z = 2) (ht : CFSG.GH74.GLS.Bg.Thompson.IsExtremalIn 2 P t)
    (hZ : ∀ w ∈ P ⊓ centralizer ({t} : Set G),
      (∀ s ∈ P ⊓ centralizer ({t} : Set G), w * s = s * w) → orderOf w = 2 →
        w = z ∨ w = t ∨ w = z * t)
    (hzt : ∀ y : G, y⁻¹ * t * y ≠ z) (hzzt : ∀ y : G, y⁻¹ * (z * t) * y ≠ z)
    (hvP : g⁻¹ * t * g ∈ P) (hv : CFSG.GH74.GLS.Bg.Thompson.IsExtremalIn 2 P (g⁻¹ * t * g)) :
    ∃ x ∈ centralizer ({z} : Set G), x⁻¹ * t * x = g⁻¹ * t * g := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set v := g⁻¹ * t * g with hvdef
  obtain ⟨hAC, hAp, hAidx⟩ := ht
  obtain ⟨hBC, hBp, hBidx⟩ := hv
  set f : G →* G := (MulAut.conj g⁻¹).toMonoidHom with hf
  have hfinj : Function.Injective f := (MulAut.conj g⁻¹).injective
  have hfapp : ∀ y, f y = g⁻¹ * y * g := fun y => by simp [hf]
  have hCt : centralizer ({v} : Set G) = (centralizer ({t} : Set G)).map f := by
    ext y
    constructor
    · intro hy
      refine ⟨g * y * g⁻¹, ?_, by rw [hfapp]; group⟩
      rw [SetLike.mem_coe, mem_centralizer_singleton_iff]
      rw [mem_centralizer_singleton_iff] at hy
      calc g * y * g⁻¹ * t = g * (y * v) * g⁻¹ := by rw [hvdef]; group
        _ = g * (v * y) * g⁻¹ := by rw [hy]
        _ = t * (g * y * g⁻¹) := by rw [hvdef]; group
    · rintro ⟨c, hc, rfl⟩
      rw [SetLike.mem_coe, mem_centralizer_singleton_iff] at hc
      rw [mem_centralizer_singleton_iff]
      rw [hfapp, hvdef]
      calc g⁻¹ * c * g * (g⁻¹ * t * g) = g⁻¹ * (c * t) * g := by group
        _ = g⁻¹ * (t * c) * g := by rw [hc]
        _ = g⁻¹ * t * g * (g⁻¹ * c * g) := by group
  set A : Subgroup G := P ⊓ centralizer ({t} : Set G) with hA
  set C : Subgroup G := centralizer ({v} : Set G) with hC
  set B : Subgroup G := P ⊓ C with hB
  set A' : Subgroup G := A.map f with hA'
  have hA'C : A' ≤ C := by rw [hCt]; exact Subgroup.map_mono hAC
  have hA'p : IsPGroup 2 A' := hAp.map f
  have hA'idx : ¬ 2 ∣ A'.relIndex C := by
    rw [hCt, hA', Subgroup.relIndex_map_map_of_injective _ _ hfinj]
    exact hAidx
  have hA''p : IsPGroup 2 ↥(A'.subgroupOf C) :=
    hA'p.of_equiv (Subgroup.subgroupOfEquivOfLe hA'C).symm
  have hB''p : IsPGroup 2 ↥(B.subgroupOf C) :=
    hBp.of_equiv (Subgroup.subgroupOfEquivOfLe hBC).symm
  obtain ⟨c, hcS⟩ := MulAction.exists_smul_eq (↥C) (hA''p.toSylow hA'idx) (hB''p.toSylow hBidx)
  have hcoe : (MulAut.conj c • (A'.subgroupOf C) : Subgroup ↥C) = B.subgroupOf C := by
    have := congrArg (fun S : Sylow 2 ↥C => (S : Subgroup ↥C)) hcS
    have e1 : ((hA''p.toSylow hA'idx : Sylow 2 ↥C) : Subgroup ↥C) = A'.subgroupOf C :=
      IsPGroup.toSylow_coe hA''p hA'idx
    have e2 : ((hB''p.toSylow hBidx : Sylow 2 ↥C) : Subgroup ↥C) = B.subgroupOf C :=
      IsPGroup.toSylow_coe hB''p hBidx
    simp only [Sylow.coe_subgroup_smul] at this
    rw [e1, e2] at this
    exact this
  have hmemB : ∀ b ∈ B, (c : G)⁻¹ * b * c ∈ A' := by
    intro b hb
    have hb' : (⟨b, hBC hb⟩ : ↥C) ∈ B.subgroupOf C := hb
    rw [← hcoe, Subgroup.mem_pointwise_smul_iff_inv_smul_mem] at hb'
    simpa [MulAut.smul_def, MulAut.conj_inv_apply, Subgroup.mem_subgroupOf] using hb'
  have hmemA : ∀ a ∈ A', (c : G) * a * (c : G)⁻¹ ∈ B := by
    intro a ha
    have ha' : (⟨a, hA'C ha⟩ : ↥C) ∈ A'.subgroupOf C := ha
    have h1 : MulAut.conj c • (⟨a, hA'C ha⟩ : ↥C) ∈ MulAut.conj c • (A'.subgroupOf C) :=
      Subgroup.smul_mem_pointwise_smul _ _ _ ha'
    rw [hcoe] at h1
    simpa [MulAut.smul_def, MulAut.conj_apply, Subgroup.mem_subgroupOf] using h1
  set h : G := g * (c : G)⁻¹ with hh
  have hcv : (c : G) * v = v * c := mem_centralizer_singleton_iff.mp c.2
  have hht : h⁻¹ * t * h = v := by
    calc h⁻¹ * t * h = (c : G) * (g⁻¹ * t * g) * (c : G)⁻¹ := by rw [hh]; group
      _ = (c : G) * v * (c : G)⁻¹ := rfl
      _ = v := by rw [hcv]; group
  have hAB : ∀ a ∈ A, h⁻¹ * a * h ∈ B := by
    intro a ha
    have h1 := hmemA (f a) ⟨a, ha, rfl⟩
    rw [hfapp] at h1
    have h2 : h⁻¹ * a * h = (c : G) * (g⁻¹ * a * g) * (c : G)⁻¹ := by rw [hh]; group
    rw [h2]
    exact h1
  have hBA : ∀ b ∈ B, h * b * h⁻¹ ∈ A := by
    intro b hb
    obtain ⟨a, ha, hae⟩ := hmemB b hb
    have h2 : h * b * h⁻¹ = g * ((c : G)⁻¹ * b * c) * g⁻¹ := by rw [hh]; group
    rw [h2, ← hae, hfapp]
    have h3 : g * (g⁻¹ * a * g) * g⁻¹ = a := by group
    rw [h3]
    exact ha
  have hzB : z ∈ B := ⟨hzP, mem_centralizer_singleton_iff.mpr (hzc v hvP).symm⟩
  set w : G := h * z * h⁻¹ with hw
  have hwA : w ∈ A := hBA z hzB
  have hwc : ∀ s ∈ A, w * s = s * w := by
    intro s hs
    have h1 : h⁻¹ * s * h ∈ P := (hAB s hs).1
    have h2 : (h⁻¹ * s * h) * z = z * (h⁻¹ * s * h) := hzc _ h1
    calc w * s = h * (z * (h⁻¹ * s * h)) * h⁻¹ := by rw [hw]; group
      _ = h * ((h⁻¹ * s * h) * z) * h⁻¹ := by rw [h2]
      _ = s * w := by rw [hw]; group
  have hword : orderOf w = 2 := by
    rw [hw, show h * z * h⁻¹ = MulAut.conj h z by simp [MulAut.conj_apply],
      MulEquiv.orderOf_eq, hz]
  have hzw : h⁻¹ * w * h = z := by rw [hw]; group
  rcases hZ w hwA hwc hword with hwz | hwt | hwzt
  · refine ⟨h, ?_, hht⟩
    rw [mem_centralizer_singleton_iff]
    have : h * z = z * h := by
      calc h * z = (h * z * h⁻¹) * h := by group
        _ = z * h := by rw [← hw, hwz]
    exact this
  · exact absurd (hwt ▸ hzw) (hzt h)
  · exact absurd (hwzt ▸ hzw) (hzzt h)

end CFSG.ComponentClassification.GrSLit.L34Sec5S

end
