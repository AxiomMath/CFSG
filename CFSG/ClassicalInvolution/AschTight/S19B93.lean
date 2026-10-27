module

public import CFSG.ClassicalInvolution.AschTight.S19BC11

public section

namespace CFSG.ClassicalInvolution.Disconnected.AschTight.S19B

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem conjSub_mem_USet {Ω : Set (Subgroup G)} (hΩ : ConjInvariant Ω) {U : Subgroup G}
    (hU : U ∈ USet Ω) (g : G) : conjSub g U ∈ USet Ω := by
  obtain ⟨R, hR, hUR, hcyc, hidx⟩ := hU
  obtain ⟨J, hJ, hRJ⟩ := exists_isSylow2In_of_mem_RSet hR
  refine ⟨conjSub g R, mem_RSet_of_isSylow2In (hΩ g J hJ) (hRJ.conj g), conjSub_mono hUR,
    isCyclic_conjSub hcyc g, ?_⟩
  rw [conjSub, conjSub, Subgroup.relIndex_map_map_of_injective _ _ (MulAut.conj g).injective]
  exact hidx

omit [Finite G] in
theorem exists_zpow_conj_eq_of_odd {t s : G} (ht : t * t = 1) (hs : s * s = 1)
    (hodd : Odd (orderOf (t * s))) : ∃ d ∈ Subgroup.zpowers (t * s), d * t * d⁻¹ = s := by
  have ht' : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht
  have hs' : s⁻¹ = s := inv_eq_of_mul_eq_one_right hs
  obtain ⟨m, hm⟩ := hodd
  have hx2 : (t * s) ^ (m + 1) * (t * s) ^ (m + 1) = t * s := by
    rw [← pow_add, show m + 1 + (m + 1) = orderOf (t * s) + 1 by omega, pow_succ,
      pow_orderOf_eq_one, one_mul]
  have htinv : t * (t * s) * t⁻¹ = (t * s)⁻¹ := by
    rw [mul_inv_rev, hs', ht']
    calc t * (t * s) * t = (t * t) * s * t := by group
      _ = s * t := by rw [ht, one_mul]
  have htk : t * (t * s) ^ (m + 1) * t⁻¹ = ((t * s) ^ (m + 1))⁻¹ := by
    rw [← conj_pow, htinv, inv_pow]
  refine ⟨((t * s) ^ (m + 1))⁻¹, Subgroup.inv_mem _ (Subgroup.npow_mem_zpowers _ _), ?_⟩
  calc ((t * s) ^ (m + 1))⁻¹ * t * ((t * s) ^ (m + 1))⁻¹⁻¹
      = ((t * s) ^ (m + 1))⁻¹ * (t * (t * s) ^ (m + 1) * t⁻¹) * t := by group
    _ = ((t * s) ^ (m + 1) * (t * s) ^ (m + 1))⁻¹ * t := by rw [htk]; group
    _ = (t * s)⁻¹ * t := by rw [hx2]
    _ = s := by rw [mul_inv_rev, hs', ht', mul_assoc, ht, mul_one]

variable {p f : ℕ} [Fact p.Prime] [IsSimpleGroup G] {K : Subgroup G} {z : G} {S : Sylow 2 G}
  {W L : Subgroup G} {t : G} {V : Subgroup G}

omit [IsSimpleGroup G] in
theorem exists_conj_t_of_mem_X (hd : Sec19DataT p f K z S W L t V) {a : G}
    (ha : a ∈ sec19T K z S) {y : G} (hy : y ∈ sec19X K z)
    (hya : y * t * y⁻¹ * a = a * (y * t * y⁻¹)) :
    ∃ d : G, d * a = a * d ∧ d * t * d⁻¹ = y * t * y⁻¹ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hB2 : IsPGroup 2 (Subgroup.zpowers a) :=
    S.isPGroup'.to_le (Subgroup.zpowers_le.mpr ha.1)
  have hBX : Subgroup.zpowers a ≤ centralizerModOdd ⊤ (sec19X K z) :=
    Subgroup.zpowers_le.mpr ha.2
  obtain ⟨o, ho, hc⟩ := exists_mul_mem_centralizer hB2 hBX hy
  have hca : a * (y * o) = (y * o) * a :=
    Subgroup.mem_centralizer_iff.mp hc a (Subgroup.mem_zpowers a)
  have htW : t ∈ W := S1911.mem_W hd
  have hta : t * a = a * t :=
    Subgroup.mem_centralizer_iff.mp (mem_centralizer_W_of_mem_T hd ha) t htW
  have htX : t ∈ sec19X K z := S1911.le_sec19X hd.toSec19Data htW
  have ht2 : t * t = 1 := hd.invL.sq
  have hs₁2 : o⁻¹ * t * o * (o⁻¹ * t * o) = 1 := by
    calc o⁻¹ * t * o * (o⁻¹ * t * o) = o⁻¹ * (t * t) * o := by group
      _ = 1 := by rw [ht2]; group
  have hs₁ : o⁻¹ * t * o = (y * o)⁻¹ * (y * t * y⁻¹) * (y * o) := by group
  have hyoinv : (y * o)⁻¹ * a = a * (y * o)⁻¹ := by
    calc (y * o)⁻¹ * a = (y * o)⁻¹ * (a * (y * o)) * (y * o)⁻¹ := by group
      _ = (y * o)⁻¹ * ((y * o) * a) * (y * o)⁻¹ := by rw [hca]
      _ = a * (y * o)⁻¹ := by group
  have hs₁a : o⁻¹ * t * o * a = a * (o⁻¹ * t * o) := by
    rw [hs₁]
    calc (y * o)⁻¹ * (y * t * y⁻¹) * (y * o) * a
        = (y * o)⁻¹ * (y * t * y⁻¹) * (a * (y * o)) := by rw [mul_assoc _ (y * o) a, ← hca]
      _ = (y * o)⁻¹ * (y * t * y⁻¹ * a) * (y * o) := by group
      _ = (y * o)⁻¹ * (a * (y * t * y⁻¹)) * (y * o) := by rw [hya]
      _ = ((y * o)⁻¹ * a) * (y * t * y⁻¹) * (y * o) := by group
      _ = (a * (y * o)⁻¹) * (y * t * y⁻¹) * (y * o) := by rw [hyoinv]
      _ = a * ((y * o)⁻¹ * (y * t * y⁻¹) * (y * o)) := by group
  have htN : t ∈ Subgroup.normalizer (oddCoreOf (sec19X K z) : Set G) :=
    mem_normalizer_oddCoreOf_of_mem_normalizer (Subgroup.le_normalizer htX)
  have hx₁O : t * (o⁻¹ * t * o) ∈ oddCoreOf (sec19X K z) := by
    have h1 : t * o⁻¹ * t⁻¹ ∈ oddCoreOf (sec19X K z) :=
      (Subgroup.mem_normalizer_iff.mp htN _).mp (Subgroup.inv_mem _ ho)
    have e : t * (o⁻¹ * t * o) = (t * o⁻¹ * t⁻¹) * (t * t) * o := by group
    rw [e, ht2, mul_one]
    exact Subgroup.mul_mem _ h1 ho
  have hodd : Odd (orderOf (t * (o⁻¹ * t * o))) :=
    Odd.of_dvd_nat (oddCoreOf_odd_natCard _) (Subgroup.orderOf_dvd_natCard _ hx₁O)
  obtain ⟨d₀, hd₀, hd₀t⟩ := exists_zpow_conj_eq_of_odd ht2 hs₁2 hodd
  have hx₁a : t * (o⁻¹ * t * o) * a = a * (t * (o⁻¹ * t * o)) := by
    calc t * (o⁻¹ * t * o) * a = t * (o⁻¹ * t * o * a) := by group
      _ = t * (a * (o⁻¹ * t * o)) := by rw [hs₁a]
      _ = (t * a) * (o⁻¹ * t * o) := by group
      _ = (a * t) * (o⁻¹ * t * o) := by rw [hta]
      _ = a * (t * (o⁻¹ * t * o)) := by group
  have hd₀a : d₀ * a = a * d₀ := by
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hd₀
    exact ((Commute.zpow_left hx₁a k)).eq
  refine ⟨(y * o) * d₀, ?_, ?_⟩
  · calc y * o * d₀ * a = y * o * (d₀ * a) := by group
      _ = y * o * (a * d₀) := by rw [hd₀a]
      _ = (y * o * a) * d₀ := by group
      _ = (a * (y * o)) * d₀ := by rw [hca]
      _ = a * (y * o * d₀) := by group
  · calc y * o * d₀ * t * (y * o * d₀)⁻¹ = (y * o) * (d₀ * t * d₀⁻¹) * (y * o)⁻¹ := by group
      _ = (y * o) * (o⁻¹ * t * o) * (y * o)⁻¹ := by rw [hd₀t]
      _ = y * t * y⁻¹ := by group

end CFSG.ClassicalInvolution.Disconnected.AschTight.S19B
