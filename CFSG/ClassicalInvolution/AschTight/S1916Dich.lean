module

public import CFSG.ClassicalInvolution.AschTight.S1911C7b
public import CFSG.ClassicalInvolution.AschTight.S1916Ctx

public section

namespace CFSG.ClassicalInvolution.Disconnected.AschTight.S1916

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open scoped commutatorElement

variable {G : Type} [Group G]

theorem conj_eq_or_of_mem {W D : Subgroup G} {t z x : G}
    (hab : ∀ a ∈ W, ∀ b ∈ W, a * b = b * a) (htW : t ∈ W) (ht2 : t * t = 1)
    (hxW : x * t * x⁻¹ ∈ W) (hzD : IsUniqueInvolution D z) (hcD : x * t * x⁻¹ * t⁻¹ ∈ D) :
    x * t * x⁻¹ = t ∨ x * t * x⁻¹ = t * z := by
  set u := x * t * x⁻¹ with hu
  have hut : u * t = t * u := hab _ hxW t htW
  have hti : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht2
  have hu2 : u * u = 1 := by
    calc u * u = x * (t * t) * x⁻¹ := by rw [hu]; group
      _ = 1 := by rw [ht2]; group
  have hdd : u * t⁻¹ * (u * t⁻¹) = 1 := by
    calc u * t⁻¹ * (u * t⁻¹) = u * (t * u) * t := by rw [hti]; group
      _ = u * (u * t) * t := by rw [← hut]
      _ = (u * u) * (t * t) := by group
      _ = 1 := by rw [hu2, ht2, one_mul]
  rcases hzD.unique _ hcD hdd with h | h
  · left
    calc u = u * t⁻¹ * t := by group
      _ = t := by rw [h, one_mul]
  · right
    have h1 : t * u = z := by
      calc t * u = u * t := hut.symm
        _ = u * t⁻¹ := by rw [hti]
        _ = z := h
    calc u = (t * t) * u := by rw [ht2, one_mul]
      _ = t * (t * u) := by group
      _ = t * z := by rw [h1]

theorem mem_of_conj_mem_pair {D : Subgroup G} {t z r₀ x : G} (hr₀ : r₀ ∈ D)
    (hr₀t : r₀ * t * r₀⁻¹ = t * z) (hdich : x * t * x⁻¹ = t ∨ x * t * x⁻¹ = t * z)
    (h1 : x * t = t * x → x ∈ D) (h2 : r₀⁻¹ * x * t = t * (r₀⁻¹ * x) → r₀⁻¹ * x ∈ D) :
    x ∈ D := by
  rcases hdich with h | h
  · refine h1 ?_
    calc x * t = x * t * x⁻¹ * x := by group
      _ = t * x := by rw [h]
  · have e : r₀⁻¹ * x * t = t * (r₀⁻¹ * x) := by
      calc r₀⁻¹ * x * t = r₀⁻¹ * (x * t * x⁻¹) * x := by group
        _ = r₀⁻¹ * (r₀ * t * r₀⁻¹) * x := by rw [h, hr₀t]
        _ = t * (r₀⁻¹ * x) := by group
    have := D.mul_mem hr₀ (h2 e)
    rwa [mul_inv_cancel_left] at this

theorem exists_conj_eq_mul_of_relIndex_two [Finite G] {Q C : Subgroup G} {t z : G}
    (hCQ : C ≤ Q) (hidx : C.relIndex Q = 2) (htQ : t ∈ Subgroup.normalizer (Q : Set G))
    (htC : ∀ c ∈ C, t * c = c * t) (hnc : ∃ b ∈ Q, t * b ≠ b * t)
    (hz : IsUniqueInvolution Q z) (ht2 : t * t = 1) (hzt : t * z = z * t) :
    ∃ q ∈ Q, q * t * q⁻¹ = t * z := by
  obtain ⟨b, hbQ, hbt⟩ := hnc
  have hti : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht2
  have hbC : b ∉ C := fun h => hbt (htC b h)
  have huQ : t * b * t ∈ Q := by
    have := (Subgroup.mem_normalizer_iff.mp htQ b).mp hbQ
    rwa [hti] at this
  have htt : t * (t * b * t) * t = b := by
    calc t * (t * b * t) * t = (t * t) * b * (t * t) := by group
      _ = b := by rw [ht2, one_mul, mul_one]
  have e1 : t * (t * b * t) = b * t := by
    calc t * (t * b * t) = (t * t) * b * t := by group
      _ = b * t := by rw [ht2, one_mul]
  have e2 : t * b * t * t = t * b := by
    calc t * b * t * t = t * b * (t * t) := by group
      _ = t * b := by rw [ht2, mul_one]
  have huC : t * b * t ∉ C := fun h => hbt (e2.symm.trans ((htC _ h).symm.trans e1))
  set d := t * b * t * b⁻¹ with hd
  have hdC : d ∈ C := mul_inv_mem_of_relIndex_two hidx huQ hbQ huC hbC
  have hu : t * b * t = d * b := by rw [hd]; group
  have h3 : b = d * (d * b) := by
    calc b = t * (t * b * t) * t := htt.symm
      _ = t * (d * b) * t := by rw [hu]
      _ = (t * d) * b * t := by group
      _ = (d * t) * b * t := by rw [htC d hdC]
      _ = d * (t * b * t) := by group
      _ = d * (d * b) := by rw [hu]
  have hdd : d * d = 1 := by
    calc d * d = d * (d * b) * b⁻¹ := by group
      _ = b * b⁻¹ := by rw [← h3]
      _ = 1 := mul_inv_cancel b
  have hd1 : d ≠ 1 := by
    intro h
    apply hbt
    rw [h, one_mul] at hu
    calc t * b = t * b * t * t := e2.symm
      _ = b * t := by rw [hu]
  have hdz : d = z := (hz.unique d (hCQ hdC) hdd).resolve_left hd1
  have hbz : b⁻¹ * z * b = z := by
    have := hz.conj_eq (n := b⁻¹) (mem_normalizer_iff_conjSub_eq.mp
      (Subgroup.le_normalizer (Q.inv_mem hbQ)))
    rwa [inv_inv] at this
  have e3 : b⁻¹ * (t * b * t) * t = b⁻¹ * t * b := by
    calc b⁻¹ * (t * b * t) * t = b⁻¹ * t * b * (t * t) := by group
      _ = b⁻¹ * t * b := by rw [ht2, mul_one]
  refine ⟨b⁻¹, Q.inv_mem hbQ, ?_⟩
  calc b⁻¹ * t * b⁻¹⁻¹ = b⁻¹ * t * b := by rw [inv_inv]
    _ = b⁻¹ * (t * b * t) * t := e3.symm
    _ = b⁻¹ * (d * b) * t := by rw [hu]
    _ = (b⁻¹ * d * b) * t := by group
    _ = (b⁻¹ * z * b) * t := by rw [hdz]
    _ = z * t := by rw [hbz]
    _ = t * z := hzt.symm

variable {p f : ℕ} [Fact p.Prime] [Finite G] {K : Subgroup G} {z : G} {S : Sylow 2 G}
  {W L : Subgroup G} {t : G} {Y' : Subgroup G}

theorem Ctx12.mem_cStar_X [IsSimpleGroup G] (c : Ctx12 p f K z S W L t)
    (hY : YPrimeData K z Y' ((S : Subgroup G) ⊓ sec19Y K z)) (hY'Y : Y' ≤ sec19Y K z)
    {a : G} (haS : a ∈ (S : Subgroup G)) (ha : a ∈ centralizerModOdd ⊤ (Y' ⊔ K))
    (hav : ∀ v ∈ L ⊓ W, a * v = v * a) : a ∈ centralizerModOdd ⊤ (sec19X K z) := by
  have hd := c.hd
  have ht := hd.tight
  obtain ⟨v, hvV, hvKY⟩ := c.exists_not_mem
  have hCz : a ∈ Subgroup.centralizer ({z} : Set G) := hd.hSz haS
  have haX : a ∈ Subgroup.normalizer (sec19X K z : Set G) :=
    mem_normalizer_iff_conjSub_eq.mpr (conjSub_sec19X K hCz)
  have hKX : K ≤ sec19X K z := le_sec19X ht.branch.member
  have hYX : sec19Y K z ≤ sec19X K z := sec19Y_le_sec19X K z
  have hXz : sec19X K z ≤ Subgroup.centralizer ({z} : Set G) := sec19X_le_centralizer K z
  have hO1 : oddCoreOf (Y' ⊔ K) ≤ oddCoreOf (sec19X K z) :=
    S1911.oddCoreOf_le_oddCoreOf (sup_le (hY'Y.trans hYX) hKX) fun x hx =>
      mem_normalizer_sup (hY.normal (hXz hx)) ((sd_normalizer_eq hd).ge (hXz hx))
  have hO2 : oddCoreOf (sec19Y K z) ≤ oddCoreOf (sec19X K z) :=
    S1911.oddCoreOf_le_oddCoreOf hYX fun x hx => sd_centralizer_le_normalizer_Y hd (hXz hx)
  have haQ : ∀ q ∈ (S : Subgroup G) ⊓ sec19Y K z, a * q = q * a := fun q hq =>
    commute_of_mem_centralizerModOdd ha (hY.sylow.1.trans le_sup_left)
      (S.isPGroup'.to_le inf_le_left)
      (mem_normalizer_inf_of_mem haS (sd_centralizer_le_normalizer_Y hd hCz)) hq
  refine mem_centralizerModOdd_of_index_two (M := K ⊔ sec19Y K z) c.rel
    (c.W_le_X hvV.2) hvKY haX ?_ (hav v hvV)
  refine commutator_mem_oddCoreOf_of_sup hKX hYX
    (fun k hk => hO1 (ha.2.2.2 k (Subgroup.mem_sup_right hk))) fun y hy => hO2 ?_
  exact c.f1 a (S.isPGroup'.to_le (Subgroup.zpowers_le.mpr haS))
    (sd_centralizer_le_normalizer_Y hd hCz) haQ y hy

end CFSG.ClassicalInvolution.Disconnected.AschTight.S1916
