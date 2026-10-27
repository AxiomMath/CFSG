module

public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKD291NilpGrp
public import CFSG.LocalAnalysis.ComponentClassification.PerfectAutomorphisms

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.KD291N

open CFSG.Open Subgroup

section Aux

variable {Y : Type} [Group Y] [Finite Y]

theorem eq_one_of_mem_zpowers_of_mem {p : ℕ} [hp : Fact p.Prime] {x : Y} (hx : orderOf x = p)
    {L : Subgroup Y} (hxL : x ∉ L) {b : Y} (hbx : b ∈ zpowers x) (hbL : b ∈ L) : b = 1 := by
  by_contra hb1
  have hbp : b ^ p = 1 := by
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.1 hbx
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, ← hx, pow_orderOf_eq_one,
      one_zpow]
  have hbo : orderOf b = p := orderOf_eq_prime hbp hb1
  have hle : zpowers b ≤ zpowers x := (Subgroup.zpowers_le).2 hbx
  have heq : zpowers b = zpowers x := Subgroup.eq_of_le_of_card_ge hle (by
    rw [Nat.card_zpowers, Nat.card_zpowers, hbo, hx])
  have hxb : x ∈ zpowers b := heq ▸ Subgroup.mem_zpowers x
  exact hxL ((Subgroup.zpowers_le).2 hbL hxb)

theorem mem_zpowers_of_mem_sup {p : ℕ} [hp : Fact p.Prime] {x v : Y} (hx : orderOf x = p)
    {L : Subgroup Y} (hxL : x ∉ L) (hvL : v ∈ L) (hvx : v * x = x * v) {w : Y}
    (hwQ : w ∈ zpowers v ⊔ zpowers x) (hwL : w ∈ L) : w ∈ zpowers v := by
  have hle : zpowers v ≤ normalizer ((zpowers x : Subgroup Y) : Set Y) := by
    rw [zpowers_le]
    refine mem_normalizer_of_conj_mem fun q hq => ?_
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.1 hq
    rw [(Commute.zpow_right (show Commute v x from hvx) j).eq, mul_inv_cancel_right]
    exact hq
  have h := Subgroup.coe_mul_of_left_le_normalizer_right (zpowers v) (zpowers x) hle
  have hw : w ∈ ((zpowers v ⊔ zpowers x : Subgroup Y) : Set Y) := hwQ
  rw [h] at hw
  obtain ⟨a, ha, b, hb, rfl⟩ := Set.mem_mul.1 hw
  have haL : a ∈ L := (Subgroup.zpowers_le).2 hvL ha
  have hbL : b ∈ L := by
    have := mul_mem (inv_mem haL) hwL
    simpa using this
  have hb1 : b = 1 := eq_one_of_mem_zpowers_of_mem hx hxL hb hbL
  rw [hb1, mul_one]
  exact ha

end Aux

section Lift

variable {Y : Type} [Group Y] {S : Type} [Group S] [Group.IsPerfect S] {L : Subgroup Y}

theorem lift_comm_cy {x g : Y} (hg : g * x = x * g) (φ : S →* ↥L)
    (hker : ∀ k ∈ φ.ker, ∀ s : S, k * s = s * k) (cy : S →* S)
    (hcy : ∀ s, x * (φ s : Y) * x⁻¹ = (φ (cy s) : Y)) (Ã : S →* S)
    (hÃ : ∀ s, (φ (Ã s) : Y) = g * (φ s : Y) * g⁻¹) (s : S) : Ã (cy s) = cy (Ã s) := by
  have hmem : ∀ s : S, (cy (Ã s))⁻¹ * Ã (cy s) ∈ φ.ker := by
    intro s
    rw [MonoidHom.mem_ker]
    apply Subtype.ext
    simp only [map_mul, map_inv, Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_one]
    rw [← hcy, hÃ, hÃ, ← hcy]
    have hg' : x * g = g * x := hg.symm
    have key : x * (g * (φ s : Y) * g⁻¹) * x⁻¹ = g * (x * (φ s : Y) * x⁻¹) * g⁻¹ := by
      calc x * (g * (φ s : Y) * g⁻¹) * x⁻¹ = (x * g) * (φ s : Y) * (x * g)⁻¹ := by group
        _ = (g * x) * (φ s : Y) * (g * x)⁻¹ := by rw [hg']
        _ = g * (x * (φ s : Y) * x⁻¹) * g⁻¹ := by group
    rw [key]
    group
  let ε : S →* Subgroup.center S :=
    { toFun := fun s => ⟨(cy (Ã s))⁻¹ * Ã (cy s),
        Subgroup.mem_center_iff.2 fun t => (hker _ (hmem s) t).symm⟩
      map_one' := by
        apply Subtype.ext
        simp
      map_mul' := by
        intro s t
        apply Subtype.ext
        have hc := hker _ (hmem s) ((cy (Ã t))⁻¹)
        change (cy (Ã (s * t)))⁻¹ * Ã (cy (s * t)) =
          ((cy (Ã s))⁻¹ * Ã (cy s)) * ((cy (Ã t))⁻¹ * Ã (cy t))
        calc (cy (Ã (s * t)))⁻¹ * Ã (cy (s * t))
            = (cy (Ã t))⁻¹ * ((cy (Ã s))⁻¹ * Ã (cy s)) * Ã (cy t) := by
              simp only [map_mul, mul_inv_rev, mul_assoc]
          _ = ((cy (Ã s))⁻¹ * Ã (cy s)) * (cy (Ã t))⁻¹ * Ã (cy t) := by rw [hc.symm]
          _ = ((cy (Ã s))⁻¹ * Ã (cy s)) * ((cy (Ã t))⁻¹ * Ã (cy t)) := by rw [mul_assoc] }
  have hε : ε = 1 := CFSG.ComponentClassification.PerfectAutomorphisms.hom_eq_one_of_commutative ε
  have h1 := congrArg (fun f : S →* Subgroup.center S => ((f s : Subgroup.center S) : S)) hε
  simp only [ε, MonoidHom.coe_mk, OneHom.coe_mk, MonoidHom.one_apply,
    OneMemClass.coe_one] at h1
  exact (inv_mul_eq_one.1 h1).symm

end Lift

section Main

variable {Y : Type} [Group Y] [Finite Y] {S : Type} [Group S] [Group.IsPerfect S]

theorem hasNormalPComplement_of_cover {p : ℕ} [hp : Fact p.Prime] (hodd : p ≠ 2) {x : Y}
    (hx : orderOf x = p) (hrank : CFSG.Open.pRank p (centralizer ({x} : Set Y)) ≤ 2)
    (L : Subgroup Y) [L.Normal] (hxL : x ∉ L) (φ : S →* ↥L)
    (hker : ∀ k ∈ φ.ker, ∀ s : S, k * s = s * k) (cy : S →* S)
    (hcy : ∀ s, x * (φ s : Y) * x⁻¹ = (φ (cy s) : Y)) (hcyker : ∀ k ∈ φ.ker, cy k = k)
    (ζ Φ : S) (hζc : ∀ s : S, ζ * s = s * ζ) (hζp : ζ ^ p = 1) (hζ1 : ζ ≠ 1)
    (hcyζ : cy ζ = ζ) (hcyΦ : cy Φ = ζ * Φ) (hΦp : Φ ^ p = 1)
    (hκ : ∀ g ∈ centralizer ({x} : Set Y), ∃ Ã : S →* S,
      (∀ s, (φ (Ã s) : Y) = g * (φ s : Y) * g⁻¹) ∧ Ã ζ = ζ) :
    CFSG.HasNormalPComplement p ↥(centralizer ({x} : Set Y)) := by
  have hxp : x ^ p = 1 := by
    have := pow_orderOf_eq_one x
    rwa [hx] at this
  have hφpow : ∀ (s : S) (n : ℕ), ((φ s : Y)) ^ n = (φ (s ^ n) : Y) := fun s n => by
    rw [map_pow, Subgroup.coe_pow]
  have hφzpow : ∀ (s : S) (n : ℤ), ((φ s : Y)) ^ n = (φ (s ^ n) : Y) := fun s n => by
    rw [map_zpow, Subgroup.coe_zpow]
  obtain ⟨v, hvL, hvx, hvp, hv1, hgood⟩ : ∃ v : Y, v ∈ L ∧ v * x = x * v ∧ v ^ p = 1 ∧ v ≠ 1 ∧
      ∀ g ∈ centralizer ({x} : Set Y), g * v * g⁻¹ ∈ zpowers v → g * v * g⁻¹ = v := by
    by_cases hζφ : φ ζ = 1
    ·
      have hvx : (φ Φ : Y) * x = x * (φ Φ : Y) := by
        have h1 := hcy Φ
        rw [hcyΦ, map_mul, hζφ, one_mul] at h1
        calc (φ Φ : Y) * x = x * (φ Φ : Y) * x⁻¹ * x := by rw [h1]
          _ = x * (φ Φ : Y) := by group
      have hv1 : (φ Φ : Y) ≠ 1 := by
        intro h
        have hΦ : Φ ∈ φ.ker := by
          rw [MonoidHom.mem_ker]
          exact Subtype.ext h
        have h2 := hcyker Φ hΦ
        rw [hcyΦ] at h2
        exact hζ1 (by simpa using h2)
      refine ⟨(φ Φ : Y), (φ Φ).2, hvx, by rw [hφpow, hΦp, map_one, Subgroup.coe_one], hv1, ?_⟩
      intro g hg hgv
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 hgv
      obtain ⟨Ã, hÃ, hÃζ⟩ := hκ g hg
      have hgx : g * x = x * g := mem_centralizer_singleton_iff.1 hg
      have hcomm := lift_comm_cy hgx φ hker cy hcy Ã hÃ
      have h1 : φ (Ã Φ) = φ (Φ ^ k) := by
        apply Subtype.ext
        rw [hÃ, ← hφzpow, hk]
      have hκ1 : (Φ ^ k)⁻¹ * Ã Φ ∈ φ.ker := by
        rw [MonoidHom.mem_ker, map_mul, map_inv, h1, inv_mul_cancel]
      have hcy1 := hcyker _ hκ1
      have hcom : Commute ζ Φ := hζc Φ
      have h2 : cy (Ã Φ) = ζ * Ã Φ := by
        rw [← hcomm, hcyΦ, map_mul, hÃζ]
      have h3 : cy (Ã Φ) = ζ ^ k * Ã Φ := by
        calc cy (Ã Φ) = cy (Φ ^ k * ((Φ ^ k)⁻¹ * Ã Φ)) := by rw [mul_inv_cancel_left]
          _ = cy Φ ^ k * cy ((Φ ^ k)⁻¹ * Ã Φ) := by rw [map_mul, map_zpow]
          _ = (ζ * Φ) ^ k * ((Φ ^ k)⁻¹ * Ã Φ) := by rw [hcyΦ, hcy1]
          _ = ζ ^ k * Φ ^ k * ((Φ ^ k)⁻¹ * Ã Φ) := by rw [hcom.mul_zpow]
          _ = ζ ^ k * Ã Φ := by group
      have h4 : ζ ^ k = ζ := mul_right_cancel (h3.symm.trans h2)
      have h5 : ζ ^ (k - 1) = 1 := by rw [zpow_sub_one, h4, mul_inv_cancel]
      have h6 : (p : ℤ) ∣ k - 1 := by
        have := (orderOf_dvd_iff_zpow_eq_one (x := ζ) (i := k - 1)).2 h5
        rwa [orderOf_eq_prime hζp hζ1] at this
      obtain ⟨m, hm⟩ := h6
      have hk1 : k = 1 + (p : ℤ) * m := by omega
      rw [← hk, hk1, zpow_add, zpow_one, zpow_mul, zpow_natCast, hφpow, hΦp, map_one,
        Subgroup.coe_one, one_zpow, mul_one]
    ·
      have hvx : (φ ζ : Y) * x = x * (φ ζ : Y) := by
        have h1 := hcy ζ
        rw [hcyζ] at h1
        calc (φ ζ : Y) * x = x * (φ ζ : Y) * x⁻¹ * x := by rw [h1]
          _ = x * (φ ζ : Y) := by group
      refine ⟨(φ ζ : Y), (φ ζ).2, hvx, by rw [hφpow, hζp, map_one, Subgroup.coe_one],
        fun h => hζφ (Subtype.ext h), ?_⟩
      intro g hg _
      obtain ⟨Ã, hÃ, hÃζ⟩ := hκ g hg
      rw [← hÃ ζ, hÃζ]
  refine hasNormalPComplement_of_pair hodd hrank hxp hvp hv1 hvx
    (fun hxv => hxL ((Subgroup.zpowers_le).2 hvL hxv)) ?_
  intro g hg hgN
  apply hgood g hg
  have hvQ : v ∈ zpowers v ⊔ zpowers x := Subgroup.mem_sup_left (Subgroup.mem_zpowers v)
  have hw : g * v * g⁻¹ ∈ zpowers v ⊔ zpowers x := (Subgroup.mem_normalizer_iff.1 hgN v).1 hvQ
  have hwL : g * v * g⁻¹ ∈ L := ‹L.Normal›.conj_mem v hvL g
  exact mem_zpowers_of_mem_sup hx hxL hvL hvx hw hwL

end Main

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.KD291N
