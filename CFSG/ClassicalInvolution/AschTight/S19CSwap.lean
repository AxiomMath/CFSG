module

public import CFSG.ClassicalInvolution.AschTight.S1911C10
public import CFSG.ClassicalInvolution.AschTight.S1911E2a
public import CFSG.ClassicalInvolution.AschTight.S19CData
public import CFSG.ClassicalInvolution.AschTight.Sec7L714A

public section

namespace CFSG.ClassicalInvolution.Disconnected.AschTight.S19C

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G] [IsSimpleGroup G]
  {K : Subgroup G} {z : G} {S : Sylow 2 G} {W L : Subgroup G} {t : G} {V : Subgroup G}

theorem conj_facts_of_mem (hd : Sec19DataT p f K z S W L t V) {r : G}
    (hrR : r ∈ (S : Subgroup G) ⊓ K) (hrU : r ∉ K ⊓ W) :
    (∀ x ∈ K ⊓ W, r * x * r⁻¹ = x⁻¹) ∧ r * r = z ∧ r * t * r⁻¹ = t * z := by
  have hd0 := hd.toSec19Data
  have hWc := S1911.comm_of_mem hd0
  obtain ⟨u₁, K', hu₁, hdK⟩ := exists_dData_K_of hd hrR hrU
  refine ⟨fun x hx => ?_, hdK.sq_r, ?_⟩
  · rw [← hu₁] at hx
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
    rw [← MulAut.conj_apply, map_zpow, MulAut.conj_apply, hdK.conj_u, inv_zpow]
  · obtain ⟨r', hr'R, hr't⟩ := S1911.exists_conj_eq_mul hd
    have htW := S1911.mem_W hd
    rcases hdK.cover r' hr'R with h | ⟨y, hy, rfl⟩
    · exfalso
      have hr'W : r' ∈ W := (hu₁ ▸ h : r' ∈ K ⊓ W).2
      have h1 : r' * t * r'⁻¹ = t := by
        rw [hWc r' hr'W t htW]
        group
      have hz1 : z = 1 := by
        have h2 := hr't.symm.trans h1
        calc z = t⁻¹ * (t * z) := by group
          _ = 1 := by rw [h2, inv_mul_cancel]
      exact (isUniqueInvolution_of_tight hd.tight.toTightBranch).ne_one hz1
    · have hyW : y ∈ W := (hu₁ ▸ hy : y ∈ K ⊓ W).2
      have hrtW : r * t * r⁻¹ ∈ W := (Subgroup.mem_normalizer_iff.mp hdK.r_normW t).mp htW
      rw [← hr't]
      calc r * t * r⁻¹ = y * (r * t * r⁻¹) * y⁻¹ := by rw [hWc y hyW _ hrtW]; group
        _ = y * r * t * (y * r)⁻¹ := by group

theorem exists_t_involution (hd : Sec19DataT p f K z S W L t V) {a : G}
    (haS : a ∈ (S : Subgroup G)) (ha2 : a * a = 1)
    (haX : a ∉ sec19X K z ⊔ centralizerModOdd ⊤ K) {u : G} {k : ℕ}
    (hu : Subgroup.zpowers u = K ⊓ W) (huo : orderOf u = 2 ^ (k + 1))
    (hact : ∀ x ∈ K ⊓ W, a * x * a⁻¹ = x ^ ((2 : ℤ) ^ k + 1)) {r : G}
    (hrR : r ∈ (S : Subgroup G) ⊓ K) (hrU : r ∉ K ⊓ W) (hra : a * r = r * a) :
    ∃ b ∈ (S : Subgroup G), b * b = 1 ∧ b ∉ sec19X K z ⊔ centralizerModOdd ⊤ K ∧
      b ∈ Subgroup.centralizer ({t} : Set G) ∧
      ((∀ x ∈ K ⊓ W, b * x * b⁻¹ = x ^ ((2 : ℤ) ^ k + 1)) ∨
        ∀ x ∈ K ⊓ W, b * x * b⁻¹ = x ^ ((2 : ℤ) ^ k - 1)) := by
  have hd0 := hd.toSec19Data
  have hWc := S1911.comm_of_mem hd0
  have hI := isUniqueInvolution_of_tight hd.tight.toTightBranch
  have htW := S1911.mem_W hd
  have hzW : z ∈ W := Hall196.mem_W_of_sec19DataT hd
  have haz : a * z = z * a := Subgroup.mem_centralizer_singleton_iff.mp (hd.hSz haS)
  rcases S1911.conj_t_eq_or_of_le_normalizer hd (S19B.le_normalizer_W hd) haS with hat | hat
  · refine ⟨a, haS, ha2, haX, ?_, Or.inl hact⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    calc a * t = a * t * a⁻¹ * a := by group
      _ = t * a := by rw [hat]
  obtain ⟨hrinv, hr2, hrt⟩ := conj_facts_of_mem hd hrR hrU
  have huKW : u ∈ K ⊓ W := hu ▸ Subgroup.mem_zpowers u
  have hzu : z = u ^ 2 ^ k := by
    have h := (Sec7.isUniqueInvolution_zpowers huo).unique z (hu ▸ ⟨hI.mem, hzW⟩) hI.sq
    exact h.resolve_left hI.ne_one
  have hu2k : u ^ ((2 : ℤ) ^ k + 1) = u * z := by
    rw [zpow_add_one, show (2 : ℤ) ^ k = ((2 ^ k : ℕ) : ℤ) by push_cast; ring, zpow_natCast, ← hzu,
      hWc _ hzW _ huKW.2]
  have hrz : r * z = z * r := by rw [← hr2, ← mul_assoc]
  have hai : a⁻¹ = a := inv_eq_of_mul_eq_one_right ha2
  have hur : a * (u * r) * a⁻¹ = (u * r)⁻¹ := by
    have h1 : a * (u * r) * a⁻¹ = (a * u * a⁻¹) * (a * r * a⁻¹) := by group
    have h2 : a * r * a⁻¹ = r := by rw [hra]; group
    have h3 : r⁻¹ = r * z := by
      rw [inv_eq_iff_mul_eq_one, ← mul_assoc, hr2, hI.sq]
    have h4 : r⁻¹ * u⁻¹ = u * r⁻¹ := by
      have := hrinv u huKW
      calc r⁻¹ * u⁻¹ = r⁻¹ * (r * u * r⁻¹) := by rw [this]
        _ = u * r⁻¹ := by group
    rw [h1, h2, hact u huKW, hu2k, mul_inv_rev, h4, h3]
    calc u * z * r = u * (z * r) := by group
      _ = u * (r * z) := by rw [hrz]
      _ = u * (r * z) := rfl
  refine ⟨a * (u * r), (S : Subgroup G).mul_mem haS ((S : Subgroup G).mul_mem
    (hd.hWS huKW.2) hrR.1), ?_, ?_, ?_, Or.inr fun x hx => ?_⟩
  · calc a * (u * r) * (a * (u * r)) = (a * (u * r) * a⁻¹) * (u * r) := by
          rw [hai]; group
      _ = 1 := by rw [hur, inv_mul_cancel]
  · intro h
    apply haX
    have hKX := S1911.le_sec19X_member hd0
    have hur' : (u * r)⁻¹ ∈ sec19X K z ⊔ centralizerModOdd ⊤ K :=
      Subgroup.mem_sup_left (hKX (K.inv_mem (K.mul_mem huKW.1 hrR.2)))
    have := (sec19X K z ⊔ centralizerModOdd ⊤ K).mul_mem h hur'
    rwa [mul_inv_cancel_right] at this
  · rw [Subgroup.mem_centralizer_singleton_iff]
    have htz : t * z ∈ W := W.mul_mem htW hzW
    have e1 : (u * r) * t * (u * r)⁻¹ = t * z := by
      calc (u * r) * t * (u * r)⁻¹ = u * (r * t * r⁻¹) * u⁻¹ := by group
        _ = u * (t * z) * u⁻¹ := by rw [hrt]
        _ = t * z := by rw [hWc u huKW.2 _ htz]; group
    have e2 : a * (u * r) * t * (a * (u * r))⁻¹ = t := by
      calc a * (u * r) * t * (a * (u * r))⁻¹ = a * ((u * r) * t * (u * r)⁻¹) * a⁻¹ := by group
        _ = (a * t * a⁻¹) * (a * z * a⁻¹) := by rw [e1]; group
        _ = t * z * z := by rw [hat, show a * z * a⁻¹ = z by rw [haz]; group]
        _ = t := by rw [mul_assoc, hI.sq, mul_one]
    calc a * (u * r) * t = a * (u * r) * t * (a * (u * r))⁻¹ * (a * (u * r)) := by group
      _ = t * (a * (u * r)) := by rw [e2]
  · have hx' : u * r * x * (u * r)⁻¹ = x⁻¹ := by
      calc u * r * x * (u * r)⁻¹ = u * (r * x * r⁻¹) * u⁻¹ := by group
        _ = u * x⁻¹ * u⁻¹ := by rw [hrinv x hx]
        _ = x⁻¹ := by rw [hWc u huKW.2 _ (W.inv_mem hx.2)]; group
    have hxo : x ^ ((2 : ℤ) ^ (k + 1)) = 1 := by
      rw [← hu] at hx
      obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
      rw [← zpow_mul, mul_comm, zpow_mul, show ((2 : ℤ) ^ (k + 1)) = ((2 ^ (k + 1) : ℕ) : ℤ) by
        push_cast; ring, zpow_natCast, ← huo, pow_orderOf_eq_one, one_zpow]
    calc a * (u * r) * x * (a * (u * r))⁻¹ = a * (u * r * x * (u * r)⁻¹) * a⁻¹ := by group
      _ = (a * x * a⁻¹)⁻¹ := by rw [hx']; group
      _ = (x ^ ((2 : ℤ) ^ k + 1))⁻¹ := by rw [hact x hx]
      _ = x ^ ((2 : ℤ) ^ k - 1) * (x ^ ((2 : ℤ) ^ (k + 1)))⁻¹ := by
          rw [← zpow_neg, ← zpow_neg, ← zpow_add]
          congr 1
          ring
      _ = x ^ ((2 : ℤ) ^ k - 1) := by rw [hxo, inv_one, mul_one]

end CFSG.ClassicalInvolution.Disconnected.AschTight.S19C
