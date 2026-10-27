module

public import CFSG.LocalAnalysis.EvenSporadicStandard.M24Std.DResCSY

set_option linter.unusedSectionVars false

public section

namespace CFSG.EvenSporadicStandard.M24Std.DRes

open Subgroup CFSG.Open
open scoped commutatorElement

section Heis

variable {Y : Type} [Group Y] [Finite Y] {t : Y} {K : Subgroup Y} {φ : K →* Equiv.Perm (Fin 6)}
  {S1 S2 : Subgroup Y} {π1 : S1 →* alternatingGroup (Fin 6)} {π2 : S2 →* alternatingGroup (Fin 6)}

namespace YSplit

variable (hS : YSplit (P1 φ) t S1 S2 π1 π2)
include hS

theorem inf_le_Z {x : Y} (hx1 : x ∈ S1) (hx2 : x ∈ S2) :
    x ∈ S1 ⊓ fusionOddCore Y ∧ x ∈ S2 ⊓ fusionOddCore Y := by
  constructor
  · have h1 : π1 ⟨x, hx1⟩ = 1 := by
      refine alt6_central fun c => ?_
      obtain ⟨g, rfl⟩ := hS.q1.surj c
      have := hS.comm g g.2 x hx2
      rw [← map_mul, ← map_mul]
      exact congrArg π1 (Subtype.ext this.symm)
    exact (hS.q1.ker _).1 h1
  · have h1 : π2 ⟨x, hx2⟩ = 1 := by
      refine alt6_central fun c => ?_
      obtain ⟨g, rfl⟩ := hS.q2.surj c
      have := hS.comm x hx1 g g.2
      rw [← map_mul, ← map_mul]
      exact congrArg π2 (Subtype.ext this)
    exact (hS.q2.ker _).1 h1

theorem exists_mul {γ : Y} (hγ : γ ∈ P1 φ) : ∃ s ∈ S1, ∃ r ∈ S2, γ = s * r := by
  rw [← hS.sup, ← commProd_eq_sup hS.comm] at hγ
  obtain ⟨s, hs, r, hr, rfl⟩ := mem_commProd.1 hγ
  exact ⟨s, hs, r, hr, rfl⟩

theorem commutator_mul_mul {s s' r r' : Y} (hs : s ∈ S1) (hs' : s' ∈ S1) (hr : r ∈ S2)
    (hr' : r' ∈ S2) : ⁅s * r, s' * r'⁆ = ⁅s, s'⁆ * ⁅r, r'⁆ := by
  have hcomm' : ∀ (m : ↥S1) (n : ↥S2), Commute (S1.subtype m) (S2.subtype n) :=
    fun m n => hS.comm m m.2 n n.2
  let Φ : ↥S1 × ↥S2 →* Y := S1.subtype.noncommCoprod S2.subtype hcomm'
  let x : ↥S1 × ↥S2 := (⟨s, hs⟩, ⟨r, hr⟩)
  let x' : ↥S1 × ↥S2 := (⟨s', hs'⟩, ⟨r', hr'⟩)
  have h1 := map_commutatorElement Φ x x'
  have h2 : ⁅x, x'⁆ = (⁅(⟨s, hs⟩ : ↥S1), ⟨s', hs'⟩⁆, ⁅(⟨r, hr⟩ : ↥S2), ⟨r', hr'⟩⁆) := by
    simp only [commutatorElement_def]
    rfl
  rw [h2] at h1
  simpa [Φ, x, x', MonoidHom.noncommCoprod_apply, commutatorElement_def] using h1.symm

end YSplit

section HeisMain

namespace CYHyp

theorem t_sq (hY : CYHyp t K φ) : t * t = 1 := by
  rw [← sq, ← hY.order, pow_orderOf_eq_one]

variable (hY : CYHyp t K φ) (hS : YSplit (P1 φ) t S1 S2 π1 π2) (hZO : Zk φ ≤ fusionOddCore Y)

include hY hS hZO

theorem xi_mem {s r : Y} (hs : s ∈ S1) (hr : r ∈ S2) (hinv' : t * (s * r) * t⁻¹ = s * r) :
    s⁻¹ * (t * r * t⁻¹) ∈ S1 ⊓ fusionOddCore Y ∧ s⁻¹ * (t * r * t⁻¹) ∈ S2 ⊓ fusionOddCore Y := by
  have h1 : s⁻¹ * (t * r * t⁻¹) ∈ S1 := S1.mul_mem (S1.inv_mem hs) (hS.swap21 r hr)
  have hc := hS.comm (t * r * t⁻¹) (hS.swap21 r hr) (t * s * t⁻¹) (hS.swap12 s hs)
  have h2 : s⁻¹ * (t * r * t⁻¹) = r * (t * s * t⁻¹)⁻¹ := by
    have e1 : (t * s * t⁻¹) * (t * r * t⁻¹) = s * r := by
      rw [← hinv']; group
    have e2 : s⁻¹ * (t * r * t⁻¹) * (t * s * t⁻¹) = r := by
      calc s⁻¹ * (t * r * t⁻¹) * (t * s * t⁻¹) = s⁻¹ * ((t * r * t⁻¹) * (t * s * t⁻¹)) := by
            group
        _ = s⁻¹ * ((t * s * t⁻¹) * (t * r * t⁻¹)) := by rw [hc]
        _ = s⁻¹ * (s * r) := by rw [e1]
        _ = r := by group
    rw [eq_mul_inv_iff_mul_eq]
    exact e2
  have h3 : s⁻¹ * (t * r * t⁻¹) ∈ S2 := by
    rw [h2]
    exact S2.mul_mem hr (S2.inv_mem (hS.swap12 s hs))
  exact hS.inf_le_Z h1 h3

theorem cube_eq_one {s r : Y} (hs : s ∈ S1) (hr : r ∈ S2) (hinv' : t * (s * r) * t⁻¹ = s * r)
    (h3 : (s * r) ^ 3 = 1) : r ^ 3 = 1 := by
  obtain ⟨hξ1, hξ2⟩ := hY.xi_mem hS hZO hs hr hinv'
  have hZ1card := hS.q1.card_Z
  have hZ2card := hS.q2.card_Z
  set ξ := s⁻¹ * (t * r * t⁻¹) with hξ
  have hξ3 : ξ ^ 3 = 1 := orderOf_dvd_iff_pow_eq_one.1
    (hZ1card ▸ Subgroup.orderOf_dvd_natCard (S1 ⊓ fusionOddCore Y) hξ1)
  set a := t * r * t⁻¹ with ha
  have hse : s = a * ξ⁻¹ := by rw [hξ, ha]; group
  have hac : Commute a ξ⁻¹ :=
    hS.q1.central a (hS.swap21 r hr) ξ⁻¹ ((S1 ⊓ fusionOddCore Y).inv_mem hξ1)
  have hs3 : s ^ 3 = t * r ^ 3 * t⁻¹ := by
    rw [hse, hac.mul_pow, inv_pow, hξ3, inv_one, mul_one, ha, conj_pow]
  have hcr : Commute s r := hS.comm s hs r hr
  rw [hcr.mul_pow, hs3] at h3
  set κ := r ^ 3 with hκ
  have hκ2 : κ ∈ S2 := S2.pow_mem hr 3
  have htκ1 : t * κ * t⁻¹ ∈ S1 := hS.swap21 κ hκ2
  have hκ1 : κ ∈ S1 := by
    have : κ = (t * κ * t⁻¹)⁻¹ := eq_inv_of_mul_eq_one_right h3
    rw [this]
    exact S1.inv_mem htκ1
  obtain ⟨hκZ1, hκZ2⟩ := hS.inf_le_Z hκ1 hκ2
  by_contra hne
  have hkne : κ ≠ 1 := hne
  have hle12 : (S1 ⊓ fusionOddCore Y) ⊓ (S2 ⊓ fusionOddCore Y) = S1 ⊓ fusionOddCore Y := by
    refine eq_of_le_of_card_ge inf_le_left ?_
    have hd : Nat.card ((S1 ⊓ fusionOddCore Y) ⊓ (S2 ⊓ fusionOddCore Y) : Subgroup Y) ∣ 3 :=
      hZ1card ▸ Subgroup.card_dvd_of_le inf_le_left
    rcases (Nat.dvd_prime Nat.prime_three).1 hd with h | h
    · exfalso
      have : (S1 ⊓ fusionOddCore Y) ⊓ (S2 ⊓ fusionOddCore Y) = ⊥ := Subgroup.eq_bot_of_card_eq _ h
      have hm : κ ∈ (S1 ⊓ fusionOddCore Y) ⊓ (S2 ⊓ fusionOddCore Y) := ⟨hκZ1, hκZ2⟩
      rw [this, Subgroup.mem_bot] at hm
      exact hkne hm
    · rw [h, hZ1card]
  have hEq : S1 ⊓ fusionOddCore Y = S2 ⊓ fusionOddCore Y := by
    refine le_antisymm ?_ ?_
    · intro x hx
      have : x ∈ (S1 ⊓ fusionOddCore Y) ⊓ (S2 ⊓ fusionOddCore Y) := by rw [hle12]; exact hx
      exact this.2
    · refine eq_of_le_of_card_ge ?_ ?_ |>.symm.le
      · intro x hx
        have : x ∈ (S1 ⊓ fusionOddCore Y) ⊓ (S2 ⊓ fusionOddCore Y) := by rw [hle12]; exact hx
        exact this.2
      · rw [hZ1card, hZ2card]
  have hZkP : Zk φ ≤ P1 φ ⊓ fusionOddCore Y := le_inf (Zk_le_K0.trans K0_le_P1) hZO
  have hZkle : Zk φ ≤ S1 ⊓ fusionOddCore Y := by
    intro w hw
    obtain ⟨a', ha', b', hb', rfl⟩ := hS.ker w (hZkP hw)
    exact (S1 ⊓ fusionOddCore Y).mul_mem ha' (hEq ▸ hb')
  have hZkeq : Zk φ = S1 ⊓ fusionOddCore Y :=
    eq_of_le_of_card_ge hZkle (by rw [hY.card_Zk, hZ1card])
  have hκZk : κ ∈ Zk φ := hZkeq ▸ hκZ1
  have htκ : t * κ * t⁻¹ = κ := by
    have := hY.comm κ (Zk_le_K hκZk)
    rw [← this]
    group
  rw [htκ] at h3
  have hκ3 : κ ^ 3 = 1 := orderOf_dvd_iff_pow_eq_one.1
    (hZ1card ▸ Subgroup.orderOf_dvd_natCard (S1 ⊓ fusionOddCore Y) hκZ1)
  have : κ = 1 := by
    calc κ = κ ^ 3 * (κ * κ)⁻¹ := by group
      _ = 1 := by rw [hκ3, h3]; group
  exact hkne this

theorem heisenberg_pair
    (hHeis : ∃ α ∈ K0 φ, ∃ β ∈ K0 φ, α * α * α = 1 ∧ β * β * β = 1 ∧ ⁅α, β⁆ ∈ Zk φ ∧
      ⁅α, β⁆ ≠ 1) :
    ∃ z1 c d : Y, z1 ∈ S1 ⊓ fusionOddCore Y ∧ z1 ≠ 1 ∧ t * z1 * t⁻¹ ∈ S2 ⊓ fusionOddCore Y ∧
      z1 * (t * z1 * t⁻¹) ∈ Zk φ ∧ z1 * (t * z1 * t⁻¹) ≠ 1 ∧ c ∈ S2 ∧ d ∈ S2 ∧
      c * c * c = 1 ∧ d * d * d = 1 ∧ c * d * c⁻¹ * d⁻¹ = t * z1 * t⁻¹ := by
  obtain ⟨α, hα, β, hβ, hα3, hβ3, hcZ, hc1⟩ := hHeis
  have ht := t_sq hY
  have hOn : (fusionOddCore Y).Normal := inferInstance
  have hinv : ∀ γ ∈ K0 φ, t * γ * t⁻¹ = γ := fun γ hγ => by
    have := mem_centralizer_singleton_iff.1 (hY.K0_le_Gam hγ)
    rw [← this]
    group
  obtain ⟨sα, hsα, rα, hrα, hαe⟩ := hS.exists_mul (K0_le_P1 hα)
  obtain ⟨sβ, hsβ, rβ, hrβ, hβe⟩ := hS.exists_mul (K0_le_P1 hβ)
  have hαt : t * (sα * rα) * t⁻¹ = sα * rα := hαe ▸ hinv α hα
  have hβt : t * (sβ * rβ) * t⁻¹ = sβ * rβ := hβe ▸ hinv β hβ
  have hrα3 : rα ^ 3 = 1 :=
    hY.cube_eq_one hS hZO hsα hrα hαt (by rw [← hαe, pow_three']; exact hα3)
  have hrβ3 : rβ ^ 3 = 1 :=
    hY.cube_eq_one hS hZO hsβ hrβ hβt (by rw [← hβe, pow_three']; exact hβ3)
  obtain ⟨hξα1, hξα2⟩ := hY.xi_mem hS hZO hsα hrα hαt
  obtain ⟨hξβ1, hξβ2⟩ := hY.xi_mem hS hZO hsβ hrβ hβt
  obtain ⟨ξα, hξα⟩ : ∃ ξ, ξ = sα⁻¹ * (t * rα * t⁻¹) := ⟨_, rfl⟩
  obtain ⟨ξβ, hξβ⟩ : ∃ ξ, ξ = sβ⁻¹ * (t * rβ * t⁻¹) := ⟨_, rfl⟩
  rw [← hξα] at hξα1 hξα2
  rw [← hξβ] at hξβ1 hξβ2
  have hsαe : sα = (t * rα * t⁻¹) * ξα⁻¹ := by rw [hξα]; group
  have hsβe : sβ = (t * rβ * t⁻¹) * ξβ⁻¹ := by rw [hξβ]; group
  have hcen1 : ∀ g ∈ S1, ∀ x ∈ S1 ⊓ fusionOddCore Y, g * x = x * g :=
    fun g hg x hx => hS.q1.central g hg x hx
  have hZ1S : S1 ⊓ fusionOddCore Y ≤ S1 := inf_le_left
  have hss : ⁅sα, sβ⁆ = t * ⁅rα, rβ⁆ * t⁻¹ := by
    have hxb : ξα⁻¹ * (t * rβ * t⁻¹) = (t * rβ * t⁻¹) * ξα⁻¹ :=
      (hcen1 _ (hS.swap21 rβ hrβ) ξα⁻¹ ((S1 ⊓ fusionOddCore Y).inv_mem hξα1)).symm
    have hxx : ξα⁻¹ * ξβ⁻¹ = ξβ⁻¹ * ξα⁻¹ :=
      hcen1 _ (hZ1S ((S1 ⊓ fusionOddCore Y).inv_mem hξα1)) ξβ⁻¹
        ((S1 ⊓ fusionOddCore Y).inv_mem hξβ1)
    have hxa : ξβ⁻¹ * (t * rα * t⁻¹) = (t * rα * t⁻¹) * ξβ⁻¹ :=
      (hcen1 _ (hS.swap21 rα hrα) ξβ⁻¹ ((S1 ⊓ fusionOddCore Y).inv_mem hξβ1)).symm
    rw [hsαe, hsβe, commutator_mul_central hxb hxx hxa]
    simp only [commutatorElement_def]
    group
  have hαβ : ⁅α, β⁆ = (t * ⁅rα, rβ⁆ * t⁻¹) * ⁅rα, rβ⁆ := by
    rw [hαe, hβe, hS.commutator_mul_mul hsα hsβ hrα hrβ, hss]
  have hu2 : ⁅rα, rβ⁆ ∈ S2 := by
    simp only [commutatorElement_def]
    exact S2.mul_mem (S2.mul_mem (S2.mul_mem hrα hrβ) (S2.inv_mem hrα)) (S2.inv_mem hrβ)
  have hut : t * ⁅rα, rβ⁆ * t⁻¹ ∈ S1 := hS.swap21 _ hu2
  have hprodO : (t * ⁅rα, rβ⁆ * t⁻¹) * ⁅rα, rβ⁆ ∈ fusionOddCore Y := hαβ ▸ hZO hcZ
  obtain ⟨hutO, huO⟩ := hS.ind _ hut _ hu2 hprodO
  have htt : t * (t * ⁅rα, rβ⁆ * t⁻¹) * t⁻¹ = ⁅rα, rβ⁆ := by
    calc t * (t * ⁅rα, rβ⁆ * t⁻¹) * t⁻¹ = (t * t) * ⁅rα, rβ⁆ * (t * t)⁻¹ := by group
      _ = ⁅rα, rβ⁆ := by rw [ht]; group
  have hune : ⁅rα, rβ⁆ ≠ 1 := by
    intro h
    apply hc1
    rw [hαβ, h]
    group
  refine ⟨t * ⁅rα, rβ⁆ * t⁻¹, rα, rβ, ⟨hut, hutO⟩, ?_, ?_, ?_, ?_, hrα, hrβ, ?_, ?_, ?_⟩
  · intro h
    apply hune
    rw [← htt, h]
    group
  · rw [htt]
    exact ⟨hu2, huO⟩
  · rw [htt, ← hαβ]
    exact hcZ
  · rw [htt, ← hαβ]
    exact hc1
  · rw [pow_three'] at hrα3
    exact hrα3
  · rw [pow_three'] at hrβ3
    exact hrβ3
  · rw [htt]
    rfl

end CYHyp

end HeisMain

end Heis

end CFSG.EvenSporadicStandard.M24Std.DRes
