module

public import CFSG.GH74.GLS.Stage2.Bender.Thm1.Omega1
public import CFSG.LocalAnalysis.SectionRank.Ccomm.Critical
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.Closed
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.Elem

public section

namespace CFSG.GH74.GLS.Stage2.Bender.Thm1

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage2.Local CFSG.GH74.GLS.Bg
open scoped commutatorElement

section Crit

variable {G : Type} [Group G] {P : Subgroup G}

theorem crit_commutator_mem {D : Subgroup ↥P} (hDP : ⁅(⊤ : Subgroup ↥P), D⁆ ≤ D ⊓ centralizer (D : Set ↥P))
    {x : G} (hx : x ∈ P) {d : G} (hd : d ∈ D.map P.subtype) :
    ⁅x, d⁆ ∈ D.map P.subtype ∧ ⁅x, d⁆ ∈ centralizer ((D.map P.subtype : Subgroup G) : Set G) := by
  obtain ⟨d₀, hd₀, rfl⟩ := hd
  have h1 := hDP (Subgroup.commutator_mem_commutator (Subgroup.mem_top (⟨x, hx⟩ : ↥P)) hd₀)
  have e : ⁅x, (P.subtype d₀ : G)⁆ = P.subtype ⁅(⟨x, hx⟩ : ↥P), d₀⁆ := by
    rw [map_commutatorElement]; rfl
  rw [e]
  refine ⟨⟨_, h1.1, rfl⟩, ?_⟩
  rw [Subgroup.mem_centralizer_iff]
  rintro _ ⟨d₁, hd₁, rfl⟩
  have := Subgroup.mem_centralizer_iff.mp h1.2 d₁ hd₁
  exact congrArg Subtype.val this

theorem crit_centralizer_le {D : Subgroup ↥P} (hDcen : centralizer (D : Set ↥P) = D ⊓ centralizer (D : Set ↥P))
    {x : G} (hx : x ∈ P) (hc : x ∈ centralizer ((D.map P.subtype : Subgroup G) : Set G)) :
    x ∈ D.map P.subtype := by
  have h1 : (⟨x, hx⟩ : ↥P) ∈ centralizer (D : Set ↥P) := by
    rw [Subgroup.mem_centralizer_iff]
    intro d₁ hd₁
    exact Subtype.ext (Subgroup.mem_centralizer_iff.mp hc (P.subtype d₁) ⟨d₁, hd₁, rfl⟩)
  rw [hDcen] at h1
  exact ⟨_, h1.1, rfl⟩

end Crit

section QPMain

variable {G : Type} [Group G] [Finite G]

theorem qp_exists_thm : QP_exists := by
  intro G _ _ z p P hp hp2 hz hPp hzP hnc
  have : Fact p.Prime := ⟨hp⟩
  have hz2 : z * z = 1 := mul_self_eq_one_of_orderOf_two hz
  obtain ⟨⟨D, hD⟩, -⟩ := CFSG.SectionRank.Ccomm.thompson_critical_subgroup (P := ↥P) (p := p) hPp
  obtain ⟨hDchar, -, hDP, hDcen⟩ := hD
  have hD'P : D.map P.subtype ≤ P := Subgroup.map_subtype_le D
  have hcr : ∀ x : G, x ∈ P → ∀ d : G, d ∈ D.map P.subtype →
      ⁅x, d⁆ ∈ D.map P.subtype ∧ ⁅x, d⁆ ∈ centralizer ((D.map P.subtype : Subgroup G) : Set G) :=
    fun x hx d hd => crit_commutator_mem hDP hx hd
  have hcen : ∀ x : G, x ∈ P → x ∈ centralizer ((D.map P.subtype : Subgroup G) : Set G) →
      x ∈ D.map P.subtype := fun x hx hc => crit_centralizer_le hDcen hx hc
  have hDcl : ⁅⁅D.map P.subtype, D.map P.subtype⁆, D.map P.subtype⁆ = ⊥ := by
    rw [Subgroup.commutator_eq_bot_iff_le_centralizer, Subgroup.commutator_le]
    intro d₁ hd₁ d₂ hd₂
    exact (hcr d₁ (hD'P hd₁) d₂ hd₂).2
  obtain ⟨Q, hQ⟩ := exists_omega1 hp hp2 hDcl
  have hQD : Q ≤ D.map P.subtype := fun x hx => ((hQ x).mp hx).1
  have hQP : Q ≤ P := hQD.trans hD'P
  have hzD : z ∈ normalizer ((D.map P.subtype : Subgroup G) : Set G) := by
    have := hDchar
    exact le_normalizer_of_characteristic (L := P) (H := zpowers z) (Subgroup.zpowers_le.mpr hzP) D
      (Subgroup.mem_zpowers z)
  have hQchar : (Q.subgroupOf P).Characteristic := by
    refine ⟨fun φ => ?_⟩
    ext x
    simp only [Subgroup.mem_comap, MulEquiv.coe_toMonoidHom, Subgroup.mem_subgroupOf]
    rw [hQ, hQ]
    have hDx : ∀ y : ↥P, (y : G) ∈ D.map P.subtype ↔ y ∈ D := fun y =>
      Subgroup.mem_map_iff_mem P.subtype_injective
    have hφD : φ x ∈ D ↔ x ∈ D := by
      have h := Subgroup.characteristic_iff_comap_eq.mp hDchar φ
      have : x ∈ D.comap φ.toMonoidHom ↔ x ∈ D := by rw [h]
      exact this
    have hc : ∀ y : ↥P, (y : G) ^ p = 1 ↔ y ^ p = 1 := fun y => by
      rw [← Subgroup.coe_pow]
      exact ⟨fun h => Subtype.ext h, fun h => congrArg Subtype.val h⟩
    have hφp : (φ x) ^ p = 1 ↔ x ^ p = 1 := by
      rw [← map_pow, MulEquiv.map_eq_one_iff]
    rw [hDx, hDx, hc, hc, hφD, hφp]
  have hPQ : P ≤ normalizer (Q : Set G) := by
    have := hQchar
    have h := le_normalizer_of_characteristic (L := P) (H := P) Subgroup.le_normalizer (Q.subgroupOf P)
    rwa [Subgroup.map_subgroupOf_eq_of_le hQP] at h
  refine ⟨Q, hQP, hQchar, fun x hx => ((hQ x).mp hx).2, ?_, ?_, ?_⟩
  · rw [eq_bot_iff, ← hDcl]
    exact Subgroup.commutator_mono (Subgroup.commutator_mono hQD hQD) hQD
  · rw [Subgroup.commutator_le]
    intro q hq x hx
    refine ⟨?_, ?_⟩
    · have hxN := hPQ hx
      have : ⁅q, x⁆ = q * (x * q⁻¹ * x⁻¹) := by simp [commutatorElement_def, mul_assoc]
      rw [this]
      exact Q.mul_mem hq ((mem_normalizer_iff.mp hxN q⁻¹).mp (Q.inv_mem hq))
    · have h1 : ⁅x, q⁆ ∈ centralizer ((D.map P.subtype : Subgroup G) : Set G) := (hcr x hx q (hQD hq)).2
      have h2 : ⁅q, x⁆ = (⁅x, q⁆)⁻¹ := (commutatorElement_inv x q).symm
      rw [h2]
      exact Subgroup.inv_mem _ (Subgroup.centralizer_le (fun y hy => hQD hy) h1)
  · intro hQz
    have hD'z : D.map P.subtype ≤ Cen z := by
      by_contra hD'nc
      obtain ⟨a, haD, ha1, hainv⟩ := exists_inverted hz2 hzD hD'nc
      have haP : a ∈ P := hD'P haD
      obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf (p := p) (G := ↥P)).mp hPp ⟨a, haP⟩
      rw [Subgroup.orderOf_mk] at hk
      have hk0 : k ≠ 0 := by
        rintro rfl
        rw [pow_zero, orderOf_eq_one_iff] at hk
        exact ha1 hk
      have hpd : p ∣ orderOf a := by rw [hk]; exact dvd_pow_self p hk0
      have hord0 : orderOf a ≠ 0 := by rw [hk]; exact pow_ne_zero k hp.ne_zero
      have hbo := orderOf_pow_orderOf_div hord0 hpd
      set b : G := a ^ (orderOf a / p) with hb
      have hbp : b ^ p = 1 := by rw [← hbo]; exact pow_orderOf_eq_one b
      have hb1 : b ≠ 1 := by
        intro h
        rw [h, orderOf_one] at hbo
        exact hp.one_lt.ne hbo
      have hbD : b ∈ D.map P.subtype := Subgroup.pow_mem _ haD _
      have hbQ : b ∈ Q := (hQ b).mpr ⟨hbD, hbp⟩
      have hbz : b * z = z * b := Subgroup.mem_centralizer_singleton_iff.mp (hQz hbQ)
      have hinv : z * b * z⁻¹ = b⁻¹ :=
        inverts_zpowers hainv b (Subgroup.pow_mem _ (Subgroup.mem_zpowers a) _)
      apply ne_inv_of_prime hp hp2 hb1 hbp
      calc b = z * b * z⁻¹ := by rw [← hbz]; group
        _ = b⁻¹ := hinv
    apply hnc
    have hR0 : ⁅⁅P, zpowers z⁆, zpowers z⁆ = ⁅P, zpowers z⁆ :=
      commutator_zpowers_idem hz hp hp2 hPp hzP
    have hRP : ⁅P, zpowers z⁆ ≤ P := commutator_le_left_of_normalizes (Subgroup.zpowers_le.mpr hzP)
    have h3 : ⁅⁅P, zpowers z⁆, D.map P.subtype⁆ = ⊥ := by
      refine Subgroup.commutator_commutator_eq_bot_of_rotate ?_ ?_
      · rw [commutator_comm (zpowers z) _, commutator_zpowers_eq_bot_iff.mpr hD'z, Subgroup.commutator_bot_left]
      · refine commutator_zpowers_eq_bot_iff.mpr ?_
        refine (?_ : ⁅D.map P.subtype, P⁆ ≤ D.map P.subtype).trans hD'z
        rw [Subgroup.commutator_le]
        intro d hd x hx
        have h4 : ⁅d, x⁆ = (⁅x, d⁆)⁻¹ := (commutatorElement_inv x d).symm
        rw [h4]
        exact Subgroup.inv_mem _ (hcr x hx d hd).1
    have hle : ⁅P, zpowers z⁆ ≤ D.map P.subtype := fun r hr =>
      hcen r (hRP hr) (Subgroup.commutator_eq_bot_iff_le_centralizer.mp h3 hr)
    have hbot : ⁅P, zpowers z⁆ = ⊥ := by
      rw [← hR0]
      exact commutator_zpowers_eq_bot_iff.mpr (hle.trans hD'z)
    exact commutator_zpowers_eq_bot_iff.mp hbot

end QPMain

end CFSG.GH74.GLS.Stage2.Bender.Thm1
