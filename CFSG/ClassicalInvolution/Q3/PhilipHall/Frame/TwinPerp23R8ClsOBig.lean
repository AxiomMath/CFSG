module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23R8ClsOut
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23R8ClsORel
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23R8ClsONC
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23R8ClsOCount
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23R8ClsOFrame

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23.ClsO

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
  CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDisc CFSG.ClassicalInvolution.Uniform
  CFSG.ClassicalInvolution.Q3.Q3NL


variable {n : ℕ}

theorem p23E8OBig_proved : P23E8OBig n := by
  intro hcit hP Y _ _ R S t K' W u e g hc hno hA5 hA6 Z hZ f hf hnf
  classical
  obtain ⟨y, hyu, hyt, ⟨a, hya⟩, hnm, m, ⟨N₁, hN₁, hmN⟩, hmu, hrel⟩ := exists_y_rel hc hA5
  have hN : Odd (3 ^ a) := Odd.pow (by decide)
  have hd := hc.data
  have hz : IsUniqueInvolution (tightCore R) t :=
    Inner.isUniqueInvolution_core (CoreData.of_S hc.std.perp.core).datum
  have ht1 : t ≠ 1 := hz.ne_one
  have he1 : e ≠ 1 := hd.he1
  have het : e ≠ t := by
    intro h
    apply e_not_mem_sup hc
    rw [h]
    exact Subgroup.mem_sup_left hz.mem
  set C := Subgroup.centralizer ({t} : Set Y) with hCdef
  set O := oddCoreOf C with hOdef
  set Q := tightCore R ⊔ K' with hQdef
  obtain ⟨hO, hOC⟩ := oddCoreOf_normalized C
  obtain ⟨hQC, hQ⟩ := Q_normalized hc
  have hyM : InM C O Q y := y_inM hc hyu hyt hN hya
  have hyC : y ∈ C := Subgroup.mem_centralizer_singleton_iff.mpr hyt
  have hfr : ∀ i : ℕ, ∃ o ∈ O, ∃ n ∈ C ⊓ Subgroup.normalizer (Z : Set Y), y ^ i = o * n :=
    fun i => hZ.frattini (y ^ i) (C.pow_mem hyC i)
  choose o ho nn hnn hy using hfr
  obtain ⟨E, hE⟩ : ∃ E : ℕ → Y, ∀ i, E i = nn i * e * (nn i)⁻¹ := ⟨_, fun _ => rfl⟩
  have hprod : E 0 * E 1 * E 2 = t := E_prod_eq hc hZ hyt hN₁ hmN hmu hrel ho hnn hy hE
  have hnM : ∀ i, InM C O Q (nn i) := by
    intro i
    have h1 : nn i = (o i)⁻¹ * y ^ i := by rw [hy i]; group
    rw [h1]
    exact InM.mul hO (InM.inv hO hQC (InM.of_mem hOC hO hQC (ho i))) (InM.pow hO hyM i)
  obtain ⟨m₀, hm₀, hfeq⟩ := hf
  have hm₀C : m₀ ∈ C := hm₀.1
  have hm₀N : m₀ ∈ Subgroup.normalizer (Z : Set Y) := hm₀.2
  have hm₀t : m₀ * t = t * m₀ := Subgroup.mem_centralizer_singleton_iff.mp hm₀C
  obtain ⟨F, hF⟩ : ∃ F : ℕ → Y, ∀ i, F i = m₀ * E i * m₀⁻¹ := ⟨_, fun _ => rfl⟩
  have heZ : ∀ i, E i ∈ Z := fun i => by
    rw [hE i]
    exact (Subgroup.mem_normalizer_iff.mp (hnn i).2 e).mp hZ.he
  have hfZ : ∀ i, F i ∈ Z := fun i => by
    rw [hF i]
    exact (Subgroup.mem_normalizer_iff.mp hm₀N (E i)).mp (heZ i)
  have hFprod : F 0 * F 1 * F 2 = t := by
    calc F 0 * F 1 * F 2 = m₀ * (E 0 * E 1 * E 2) * m₀⁻¹ := by rw [hF 0, hF 1, hF 2]; group
      _ = m₀ * t * m₀⁻¹ := by rw [hprod]
      _ = t := by rw [hm₀t]; group
  have hconj1 : ∀ c : Y, c * e * c⁻¹ ≠ 1 := by
    intro c h
    apply he1
    calc e = c⁻¹ * (c * e * c⁻¹) * c := by group
      _ = 1 := by rw [h]; group
  have hconjt : ∀ c ∈ C, c * e * c⁻¹ ≠ t := by
    intro c hcC h
    apply het
    have hct : c * t = t * c := Subgroup.mem_centralizer_singleton_iff.mp hcC
    calc e = c⁻¹ * (c * e * c⁻¹) * c := by group
      _ = c⁻¹ * t * c := by rw [h]
      _ = c⁻¹ * (t * c) := by group
      _ = c⁻¹ * (c * t) := by rw [hct]
      _ = t := by group
  have hnC : ∀ i, nn i ∈ C := fun i => (hnn i).1
  have hFc : ∀ i, F i = (m₀ * nn i) * e * (m₀ * nn i)⁻¹ := by
    intro i
    rw [hF i, hE i]
    group
  have hFC : ∀ i, m₀ * nn i ∈ C := fun i => C.mul_mem hm₀C (hnC i)
  have hE2 : E 2 ≠ 1 := by
    rw [hE 2]
    exact hconj1 _
  have h0 : E 0 ≠ 1 ∧ E 0 ≠ t := by
    rw [hE 0]
    exact ⟨hconj1 _, hconjt _ (hnC 0)⟩
  have h1 : E 1 ≠ 1 ∧ E 1 ≠ t ∧ E 1 ≠ E 0 ∧ E 1 ≠ t * E 0 := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [hE 1]
      exact hconj1 _
    · rw [hE 1]
      exact hconjt _ (hnC 1)
    · intro h
      have hn0 : nn 0 = (o 0)⁻¹ := by
        have h0' := hy 0
        rw [pow_zero] at h0'
        exact eq_inv_of_mul_eq_one_right h0'.symm
      have hn1 : nn 1 = (o 1)⁻¹ * y := by
        have h1' := hy 1
        rw [pow_one] at h1'
        rw [h1']
        group
      rw [hE 1, hE 0, hn0, hn1] at h
      apply hnm (o 1 * (o 0)⁻¹) (O.mul_mem (ho 1) (O.inv_mem (ho 0)))
      calc y * e * y⁻¹ = o 1 * ((o 1)⁻¹ * y * e * ((o 1)⁻¹ * y)⁻¹) * (o 1)⁻¹ := by group
        _ = o 1 * ((o 0)⁻¹ * e * ((o 0)⁻¹)⁻¹) * (o 1)⁻¹ := by rw [h]
        _ = (o 1 * (o 0)⁻¹) * e * (o 1 * (o 0)⁻¹)⁻¹ := by group
    · intro h
      have hc0 : E 0 * t = t * E 0 := hZ.comm _ (heZ 0) _ hZ.ht
      have h3 : E 0 * (t * E 0) = t := by
        calc E 0 * (t * E 0) = (E 0 * t) * E 0 := by group
          _ = (t * E 0) * E 0 := by rw [hc0]
          _ = t * (E 0 * E 0) := by group
          _ = t := by rw [hZ.sq _ (heZ 0), mul_one]
      rw [h, h3] at hprod
      apply hE2
      exact mul_left_cancel (a := t) (by rw [hprod, mul_one])
  have hfne : ∀ l : ℕ, l < 3 → F l ≠ 1 ∧ F l ≠ t := by
    intro l _
    rw [hFc l]
    exact ⟨hconj1 _, hconjt _ (hFC l)⟩
  have hfe : ∀ l i : ℕ, l < 3 → i < 3 → F l ≠ E i := by
    intro l i _ _ h
    obtain ⟨x, hx⟩ : ∃ x : Y, x = m₀ * nn l * m₀⁻¹ := ⟨_, rfl⟩
    have hxM : InM C O Q x := by
      rw [hx]
      exact InM.conj hO hQ hm₀C (hnM l)
    have hmmM : InM C O Q (x⁻¹ * nn i) := InM.mul hO (InM.inv hO hQC hxM) (hnM i)
    apply hnf
    unfold P23MOrb
    refine ⟨x⁻¹ * nn i, hmmM.1, hmmM.2, 1, O.one_mem, ?_⟩
    have h' : x * (m₀ * e * m₀⁻¹) * x⁻¹ = nn i * e * (nn i)⁻¹ := by
      rw [← hE i, ← h, hF l, hE l, hx]
      group
    rw [hfeq]
    calc m₀ * e * m₀⁻¹ = x⁻¹ * (x * (m₀ * e * m₀⁻¹) * x⁻¹) * x := by group
      _ = x⁻¹ * (nn i * e * (nn i)⁻¹) * x := by rw [h']
      _ = 1 * ((x⁻¹ * nn i) * e * (x⁻¹ * nn i)⁻¹) * 1⁻¹ := by group
  have hfte : ∀ l i : ℕ, l < 3 → i < 3 → F l ≠ t * E i := by
    intro l i _ _ h
    apply not_conj_e_te hc hA5 hA6 ((m₀ * nn l)⁻¹ * nn i)
    have hnit : nn i * t = t * nn i := Subgroup.mem_centralizer_singleton_iff.mp (hnC i)
    have hcomm : t * (nn i * e * (nn i)⁻¹) = nn i * (t * e) * (nn i)⁻¹ := by
      calc t * (nn i * e * (nn i)⁻¹) = (t * nn i) * e * (nn i)⁻¹ := by group
        _ = (nn i * t) * e * (nn i)⁻¹ := by rw [hnit]
        _ = nn i * (t * e) * (nn i)⁻¹ := by group
    calc e = (m₀ * nn l)⁻¹ * ((m₀ * nn l) * e * (m₀ * nn l)⁻¹) * (m₀ * nn l) := by group
      _ = (m₀ * nn l)⁻¹ * F l * (m₀ * nn l) := by rw [hFc l]
      _ = (m₀ * nn l)⁻¹ * (t * E i) * (m₀ * nn l) := by rw [h]
      _ = (m₀ * nn l)⁻¹ * (t * (nn i * e * (nn i)⁻¹)) * (m₀ * nn l) := by rw [hE i]
      _ = (m₀ * nn l)⁻¹ * (nn i * (t * e) * (nn i)⁻¹) * (m₀ * nn l) := by rw [hcomm]
      _ = ((m₀ * nn l)⁻¹ * nn i) * (t * e) * ((m₀ * nn l)⁻¹ * nn i)⁻¹ := by group
  exact card_ge_32 hZ.comm hZ.sq hZ.ht ht1 E F heZ hfZ hprod hFprod h0 h1 hfne hfe hfte

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23.ClsO
