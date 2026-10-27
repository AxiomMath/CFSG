module

public import CFSG.ClassicalInvolution.Q3.Q3T6RChain
public import CFSG.ClassicalInvolution.Q3.Q3T6XQuot
public import CFSG.CharacterTheory.Semidihedral.Principal.FreeSixCharacterDefectFourSupport
public import CFSG.ClassicalInvolution.Uniform.U4Class

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3T6X

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Hat2A7
  CFSG.ClassicalInvolution.Uniform CFSG.ClassicalInvolution.Uniform.U4
open CFSG.ClassicalInvolution.Q3.Q3T6R (actTriv mem_actTriv_iff actTriv_conj_mem
  exists_three_sq_elements exists_conj_of_twin_pairs)
open scoped commutatorElement



section Chain

variable {F : Type} [Group F] [Finite F]

theorem mem_actTriv_of_chain_min {J : Subgroup F} {t δ z v : F} (hJ : Mem3 J t)
    (hδ2 : δ * δ = 1) (hδt : t * δ = δ * t) (hJδ : J ≠ conjSub δ J) (hvJ : v ∈ J)
    (hvv : v * v = t) (hvδ : δ * v * δ⁻¹ = v * z) (hzt : t * z = z * t) (hz : z ∈ actTriv δ) :
    t ∈ actTriv δ := by
  classical
  have hδi : δ⁻¹ = δ := inv_eq_of_mul_eq_one_right hδ2
  have ht2 : t * t = 1 := hJ.mul_self
  have hJ' : Mem3 (conjSub δ J) t := hJ.conj_of_commute hδt.symm
  set P : Subgroup F := Balance.oddCoreIn (Subgroup.centralizer ({t} : Set F)) with hP
  have hPJ : oddCoreOf J = P :=
    Uniform.oddCoreIn_eq_of_intrinsic hJ.member (hJ.intrinsic solvableType_three)
  have hPJ' : oddCoreOf (conjSub δ J) = P :=
    Uniform.oddCoreIn_eq_of_intrinsic hJ'.member (hJ'.intrinsic solvableType_three)
  obtain ⟨-, -, hcommod⟩ := hJ.twin_facts hJ' hJδ
  have hcomm : ∀ x ∈ J, ∀ y ∈ conjSub δ J, ⁅x, y⁆ ∈ P := fun x hx y hy => by
    have := (hcommod (Subgroup.commutator_mem_commutator hx hy)).1
    rwa [hPJ] at this
  have hPle : P ≤ J := hPJ ▸ oddCoreOf_le_self J
  have hJn : ∀ m ∈ J, m ∈ Subgroup.normalizer (P : Set F) := fun m hm => by
    rw [← hPJ]
    exact AscFusion.mem_normalizer_oddCoreOf_of_mem_normalizer' (Subgroup.le_normalizer hm)
  have hJ'n : ∀ m ∈ conjSub δ J, m ∈ Subgroup.normalizer (P : Set F) := fun m hm => by
    rw [← hPJ']
    exact AscFusion.mem_normalizer_oddCoreOf_of_mem_normalizer' (Subgroup.le_normalizer hm)
  have hPδ : ∀ p ∈ P, δ * p * δ⁻¹ ∈ P := by
    have hδC : δ ∈ Subgroup.centralizer ({t} : Set F) :=
      Subgroup.mem_centralizer_singleton_iff.mpr hδt.symm
    have := Balance.normalizer_oddCoreIn (Subgroup.centralizer ({t} : Set F)) hδC
    intro p hp
    exact (Subgroup.mem_normalizer_iff.mp this p).mp hp
  have hPodd : Odd (Nat.card P) := Balance.odd_card_oddCoreIn _
  obtain ⟨d, hd⟩ : ∃ d : F → F, ∀ g, d g = g * (δ * g * δ⁻¹) := ⟨_, fun _ => rfl⟩
  have hdn : ∀ g ∈ J, d g ∈ Subgroup.normalizer (P : Set F) := fun g hg => by
    rw [hd]
    exact (Subgroup.normalizer (P : Set F)).mul_mem (hJn g hg)
      (hJ'n _ (conj_mem_conjSub hg))
  have hmul : ∀ g ∈ J, ∀ g' ∈ J, ∃ c ∈ P, d (g * g') = c * (d g * d g') := by
    intro g hg g' hg'
    refine ⟨g * ⁅g', δ * g * δ⁻¹⁆ * g⁻¹, ?_, ?_⟩
    · have h1 : ⁅g', δ * g * δ⁻¹⁆ ∈ P := hcomm g' hg' _ (conj_mem_conjSub hg)
      exact (Subgroup.mem_normalizer_iff.mp (hJn g hg) _).mp h1
    · rw [hd, hd, hd]
      simp only [commutatorElement_def]
      group
  have hlift : ∀ g ∈ J, ∃ x : F, x * δ = δ * x ∧ ∃ c ∈ P, x = d g * c := by
    intro g hg
    have hx : (d g)⁻¹ * (δ * d g * δ⁻¹) ∈ P := by
      have e : δ * d g * δ⁻¹ = (δ * g * δ⁻¹) * g := by
        rw [hd, hδi]
        calc δ * (g * (δ * g * δ)) * δ = (δ * g * δ) * g * (δ * δ) := by group
          _ = (δ * g * δ) * g := by rw [hδ2, mul_one]
      have hc1 : ⁅g, δ * g * δ⁻¹⁆ ∈ P := hcomm g hg _ (conj_mem_conjSub hg)
      have e2 : (δ * g * δ⁻¹) * g = ⁅g, δ * g * δ⁻¹⁆⁻¹ * d g := by
        rw [hd]
        simp only [commutatorElement_def]
        group
      have hinv : (d g)⁻¹ ∈ Subgroup.normalizer (P : Set F) :=
        (Subgroup.normalizer (P : Set F)).inv_mem (hdn g hg)
      have h4 := (Subgroup.mem_normalizer_iff.mp hinv _).mp (P.inv_mem hc1)
      have e3 : (d g)⁻¹ * (⁅g, δ * g * δ⁻¹⁆⁻¹ * d g) =
          (d g)⁻¹ * ⁅g, δ * g * δ⁻¹⁆⁻¹ * ((d g)⁻¹)⁻¹ := by group
      rw [e, e2, e3]
      exact h4
    obtain ⟨p, hp, hpfix⟩ := exists_fixed_mul_of_odd hδ2 hPodd hPδ hx
    exact ⟨d g * p, hpfix, p, hp, rfl⟩
  have hNorm : (P.subgroupOf (Subgroup.normalizer (P : Set F))).Normal := inferInstance
  let π : Subgroup.normalizer (P : Set F) →*
      Subgroup.normalizer (P : Set F) ⧸ P.subgroupOf (Subgroup.normalizer (P : Set F)) :=
    QuotientGroup.mk' _
  have hπeq : ∀ a b : Subgroup.normalizer (P : Set F), π a = π b ↔ (a : F)⁻¹ * (b : F) ∈ P := by
    intro a b
    show (QuotientGroup.mk a : Subgroup.normalizer (P : Set F) ⧸
      P.subgroupOf (Subgroup.normalizer (P : Set F))) = QuotientGroup.mk b ↔ _
    rw [QuotientGroup.eq, Subgroup.mem_subgroupOf]
    rfl
  have hπone : ∀ c ∈ P, ∀ hc : c ∈ Subgroup.normalizer (P : Set F), π ⟨c, hc⟩ = 1 := by
    intro c hc hcN
    have : (⟨c, hcN⟩ : Subgroup.normalizer (P : Set F)) ∈
        P.subgroupOf (Subgroup.normalizer (P : Set F)) := Subgroup.mem_subgroupOf.mpr hc
    exact (QuotientGroup.eq_one_iff _).mpr this
  let D : J →* Subgroup.normalizer (P : Set F) ⧸ P.subgroupOf (Subgroup.normalizer (P : Set F)) :=
    { toFun := fun g => π ⟨d g, hdn g g.2⟩
      map_one' := by
        have h1 : d ((1 : J) : F) = 1 := by rw [hd]; simp
        exact hπone _ (by rw [h1]; exact P.one_mem) _
      map_mul' := by
        intro g g'
        obtain ⟨c, hc, hcd⟩ := hmul g g.2 g' g'.2
        rw [← map_mul, hπeq]
        show (d ((g : F) * g'))⁻¹ * (d g * d g') ∈ P
        rw [hcd]
        have hy : d g * d g' ∈ Subgroup.normalizer (P : Set F) :=
          (Subgroup.normalizer (P : Set F)).mul_mem (hdn g g.2) (hdn g' g'.2)
        have := (Subgroup.mem_normalizer_iff.mp
          ((Subgroup.normalizer (P : Set F)).inv_mem hy) c⁻¹).mp (P.inv_mem hc)
        have e : (c * (d g * d g'))⁻¹ * (d g * d g') =
            (d g * d g')⁻¹ * c⁻¹ * ((d g * d g')⁻¹)⁻¹ := by group
        rw [e]
        exact this }
  obtain ⟨a₁, ha₁, a₂, ha₂, h1sq, h2sq, h3sq⟩ := exists_three_sq_elements hJ
  have hdv : d v = t * z := by rw [hd, hvδ, ← mul_assoc, hvv]
  have hDv : π ⟨t * z, hdv ▸ hdn v hvJ⟩ = D ⟨v, hvJ⟩ := by
    show π ⟨t * z, _⟩ = π ⟨d v, _⟩
    congr 1
    exact Subtype.ext hdv.symm
  have hzN : t * z ∈ Subgroup.normalizer (P : Set F) := hdv ▸ hdn v hvJ
  have hDv' : π ⟨t * z, hzN⟩ = D ⟨v, hvJ⟩ := hDv
  have hdt : ∀ g ∈ J, d g * t = t * d g := by
    intro g hg
    have h1 : g * t = t * g := hJ.mul_comm_of_mem hg
    have h2 : (δ * g * δ⁻¹) * t = t * (δ * g * δ⁻¹) :=
      hJ'.mul_comm_of_mem (conj_mem_conjSub hg)
    rw [hd]
    calc g * (δ * g * δ⁻¹) * t = g * ((δ * g * δ⁻¹) * t) := by group
      _ = g * (t * (δ * g * δ⁻¹)) := by rw [h2]
      _ = (g * t) * (δ * g * δ⁻¹) := by group
      _ = (t * g) * (δ * g * δ⁻¹) := by rw [h1]
      _ = t * (g * (δ * g * δ⁻¹)) := by group
  have hkey : ∀ (g : F) (hg : g ∈ J), ∃ x : F, x * δ = δ * x ∧ x * t = t * x ∧
      ∃ hx : x ∈ Subgroup.normalizer (P : Set F), π ⟨x, hx⟩ = D ⟨g, hg⟩ := by
    intro g hg
    obtain ⟨x, hxδ, c, hc, rfl⟩ := hlift g hg
    have hcN : c ∈ Subgroup.normalizer (P : Set F) := Subgroup.le_normalizer hc
    refine ⟨d g * c, hxδ, ?_, (Subgroup.normalizer (P : Set F)).mul_mem (hdn g hg) hcN, ?_⟩
    · have h2 : c * t = t * c := hJ.mul_comm_of_mem (hPle hc)
      calc d g * c * t = d g * (c * t) := by group
        _ = d g * (t * c) := by rw [h2]
        _ = (d g * t) * c := by group
        _ = (t * d g) * c := by rw [hdt g hg]
        _ = t * (d g * c) := by group
    · show π ⟨d g * c, _⟩ = π ⟨d g, _⟩
      rw [hπeq]
      show (d g * c)⁻¹ * (d g) ∈ P
      have e : (d g * c)⁻¹ * d g = c⁻¹ := by group
      rw [e]
      exact P.inv_mem hc
  obtain ⟨g₁, hg₁, hg₁e⟩ := hJ.exists_conj_in_member hvJ ha₁ hvv h1sq
  obtain ⟨g₂, hg₂, hg₂e⟩ := hJ.exists_conj_in_member hvJ ha₂ hvv h2sq
  obtain ⟨g₃, hg₃, hg₃e⟩ := hJ.exists_conj_in_member hvJ (J.mul_mem ha₁ ha₂) hvv h3sq
  obtain ⟨x₁, hx₁δ, hx₁t, hx₁N, hx₁π⟩ := hkey g₁ hg₁
  obtain ⟨x₂, hx₂δ, hx₂t, hx₂N, hx₂π⟩ := hkey g₂ hg₂
  obtain ⟨x₃, hx₃δ, hx₃t, hx₃N, hx₃π⟩ := hkey g₃ hg₃
  have hπu : ∀ (g : F) (hg : g ∈ J) (x : F) (hxN : x ∈ Subgroup.normalizer (P : Set F)),
      π ⟨x, hxN⟩ = D ⟨g, hg⟩ → ∀ hmem : x * (t * z) * x⁻¹ ∈ Subgroup.normalizer (P : Set F),
      π ⟨x * (t * z) * x⁻¹, hmem⟩ =
        D ⟨g * v * g⁻¹, J.mul_mem (J.mul_mem hg hvJ) (J.inv_mem hg)⟩ := by
    intro g hg x hxN hxπ hmem
    have e : (⟨x * (t * z) * x⁻¹, hmem⟩ : Subgroup.normalizer (P : Set F)) =
        ⟨x, hxN⟩ * ⟨t * z, hzN⟩ * ⟨x, hxN⟩⁻¹ := rfl
    have e2 : (⟨g * v * g⁻¹, J.mul_mem (J.mul_mem hg hvJ) (J.inv_mem hg)⟩ : J) =
        ⟨g, hg⟩ * ⟨v, hvJ⟩ * ⟨g, hg⟩⁻¹ := rfl
    rw [e, e2, map_mul, map_mul, map_inv, map_mul, map_mul, map_inv, hxπ, hDv']
  have hu1N : x₁ * (t * z) * x₁⁻¹ ∈ Subgroup.normalizer (P : Set F) :=
    (Subgroup.normalizer (P : Set F)).mul_mem
      ((Subgroup.normalizer (P : Set F)).mul_mem hx₁N hzN)
      ((Subgroup.normalizer (P : Set F)).inv_mem hx₁N)
  have hu2N : x₂ * (t * z) * x₂⁻¹ ∈ Subgroup.normalizer (P : Set F) :=
    (Subgroup.normalizer (P : Set F)).mul_mem
      ((Subgroup.normalizer (P : Set F)).mul_mem hx₂N hzN)
      ((Subgroup.normalizer (P : Set F)).inv_mem hx₂N)
  have hu3N : x₃ * (t * z) * x₃⁻¹ ∈ Subgroup.normalizer (P : Set F) :=
    (Subgroup.normalizer (P : Set F)).mul_mem
      ((Subgroup.normalizer (P : Set F)).mul_mem hx₃N hzN)
      ((Subgroup.normalizer (P : Set F)).inv_mem hx₃N)
  have hπ1 := hπu g₁ hg₁ x₁ hx₁N hx₁π hu1N
  have hπ2 := hπu g₂ hg₂ x₂ hx₂N hx₂π hu2N
  have hπ3 := hπu g₃ hg₃ x₃ hx₃N hx₃π hu3N
  have hb : g₃ * v * g₃⁻¹ = (g₁ * v * g₁⁻¹) * (g₂ * v * g₂⁻¹) := by
    rw [hg₁e, hg₂e]
    exact hg₃e
  have hπrel : π ⟨x₃ * (t * z) * x₃⁻¹, hu3N⟩ =
      π ⟨x₁ * (t * z) * x₁⁻¹, hu1N⟩ * π ⟨x₂ * (t * z) * x₂⁻¹, hu2N⟩ := by
    rw [hπ1, hπ2, hπ3, ← map_mul]
    congr 1
    exact Subtype.ext hb
  have hoP : (x₃ * (t * z) * x₃⁻¹)⁻¹ * ((x₁ * (t * z) * x₁⁻¹) * (x₂ * (t * z) * x₂⁻¹)) ∈ P := by
    refine (hπeq ⟨x₃ * (t * z) * x₃⁻¹, hu3N⟩
      (⟨x₁ * (t * z) * x₁⁻¹, hu1N⟩ * ⟨x₂ * (t * z) * x₂⁻¹, hu2N⟩)).mp ?_
    rw [map_mul]
    exact hπrel
  have hz1 : x₁ * z * x₁⁻¹ ∈ actTriv δ := actTriv_conj_mem hx₁δ hz
  have hz2 : x₂ * z * x₂⁻¹ ∈ actTriv δ := actTriv_conj_mem hx₂δ hz
  have hz3 : x₃ * z * x₃⁻¹ ∈ actTriv δ := actTriv_conj_mem hx₃δ hz
  have hti : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht2
  have hut : ∀ x : F, x * t = t * x → x * (t * z) * x⁻¹ = t * (x * z * x⁻¹) := by
    intro x hx
    have h1 : x * t * x⁻¹ = t := mul_inv_eq_iff_eq_mul.mpr hx
    calc x * (t * z) * x⁻¹ = (x * t * x⁻¹) * (x * z * x⁻¹) := by group
      _ = t * (x * z * x⁻¹) := by rw [h1]
  have hcz : ∀ x : F, x * t = t * x → t * (x * z * x⁻¹) = (x * z * x⁻¹) * t := by
    intro x hx
    have c1 : Commute t x := hx.symm
    have c2 : Commute t z := hzt
    exact ((c1.mul_right c2).mul_right c1.inv_right).eq
  rw [hut x₁ hx₁t, hut x₂ hx₂t, hut x₃ hx₃t] at hoP
  have ht1 : t * (x₁ * z * x₁⁻¹) = (x₁ * z * x₁⁻¹) * t := hcz x₁ hx₁t
  have ht2' : t * (x₂ * z * x₂⁻¹) = (x₂ * z * x₂⁻¹) * t := hcz x₂ hx₂t
  have ht3 : t * (x₃ * z * x₃⁻¹) = (x₃ * z * x₃⁻¹) * t := hcz x₃ hx₃t
  generalize x₁ * z * x₁⁻¹ = z₁ at hz1 ht1 hoP
  generalize x₂ * z * x₂⁻¹ = z₂ at hz2 ht2' hoP
  generalize x₃ * z * x₃⁻¹ = z₃ at hz3 ht3 hoP
  have hoeq : (t * z₃)⁻¹ * ((t * z₁) * (t * z₂)) = (z₃⁻¹ * z₁ * z₂) * t := by
    have e1 : (t * z₁) * (t * z₂) = z₁ * z₂ := by
      calc (t * z₁) * (t * z₂) = t * (z₁ * t) * z₂ := by group
        _ = t * (t * z₁) * z₂ := by rw [← ht1]
        _ = (t * t) * z₁ * z₂ := by group
        _ = z₁ * z₂ := by rw [ht2, one_mul]
    have e2 : (t * z₃)⁻¹ = z₃⁻¹ * t := by rw [mul_inv_rev, hti]
    calc (t * z₃)⁻¹ * ((t * z₁) * (t * z₂)) = z₃⁻¹ * t * (z₁ * z₂) := by rw [e1, e2]
      _ = z₃⁻¹ * (t * z₁) * z₂ := by group
      _ = z₃⁻¹ * (z₁ * t) * z₂ := by rw [ht1]
      _ = z₃⁻¹ * z₁ * (t * z₂) := by group
      _ = z₃⁻¹ * z₁ * (z₂ * t) := by rw [ht2']
      _ = (z₃⁻¹ * z₁ * z₂) * t := by group
  rw [hoeq] at hoP
  have hnN : z₃⁻¹ * z₁ * z₂ ∈ actTriv δ :=
    (actTriv δ).mul_mem ((actTriv δ).mul_mem ((actTriv δ).inv_mem hz3) hz1) hz2
  have hnt : Commute (z₃⁻¹ * z₁ * z₂) t := by
    have c1 : Commute t z₁ := ht1
    have c2 : Commute t z₂ := ht2'
    have c3 : Commute t z₃ := ht3
    exact ((c3.inv_right.mul_right c1).mul_right c2).symm
  have hk : Odd (orderOf ((z₃⁻¹ * z₁ * z₂) * t)) :=
    Odd.of_dvd_nat hPodd (Subgroup.orderOf_dvd_natCard P hoP)
  have hpow : ((z₃⁻¹ * z₁ * z₂) * t) ^ orderOf ((z₃⁻¹ * z₁ * z₂) * t) = 1 :=
    pow_orderOf_eq_one _
  rw [hnt.mul_pow] at hpow
  obtain ⟨j, hj⟩ := hk
  have htk : t ^ orderOf ((z₃⁻¹ * z₁ * z₂) * t) = t := by
    rw [hj, pow_succ, pow_mul, pow_two, ht2, one_pow, one_mul]
  rw [htk] at hpow
  have h5 : t = ((z₃⁻¹ * z₁ * z₂) ^ orderOf ((z₃⁻¹ * z₁ * z₂) * t))⁻¹ :=
    eq_inv_of_mul_eq_one_right hpow
  rw [h5]
  exact (actTriv δ).inv_mem ((actTriv δ).pow_mem hnN _)

@[expose] def BstarOn (F : Type) [Group F] [Finite F] (S : Set F) : Prop :=
  ∀ {J K : Subgroup F} {t z : F}, Mem3 J t → Mem3 K z → t ∈ S → z ∈ S → ∀ {a : F}, a ∈ J →
    orderOf a = 4 → a * z = z * a → t ∈ Subgroup.normalizer (K : Set F)

@[expose] def SymOn (F : Type) [Group F] [Finite F] (S : Set F) : Prop :=
  ∀ {X Y : Subgroup F} {x y : F}, Mem3 X x → Mem3 Y y → x ∈ S → y ∈ S →
    x ∈ Subgroup.normalizer (Y : Set F) → y ∈ Subgroup.normalizer (X : Set F)

theorem fusion_chain_contradiction_min {S : Set F} (hB : BstarOn F S) (hSy : SymOn F S)
    {K J : Subgroup F} {z t : F} (hK : Mem3 K z) (hJ : Mem3 J t) (hne : t ≠ z)
    (hzS : z ∈ S) (htS : t ∈ S) {v : F} (hvJ : v ∈ J) (hv4 : orderOf v = 4)
    (hvz : v * z = z * v) {κ : F} (hκK : κ ∈ K) (hκ2 : κ * κ = z)
    (hκn : (v * v)⁻¹ * κ * (v * v) = κ⁻¹)
    (hcomm : κ * (v⁻¹ * κ * v) = (v⁻¹ * κ * v) * κ) {I : Subgroup F}
    (hI : Mem3 I (κ * (v⁻¹ * κ * v))) (hδS : κ * (v⁻¹ * κ * v) ∈ S) : False := by
  have hJt : IsUniqueInvolution J t := hJ.isUniqueInvolution
  have hz2 : z * z = 1 := hK.mul_self
  have hvv : v * v = t := mul_self_eq_of_orderOf_four hJt hvJ hv4
  have hzt : t * z = z * t := by
    rw [← hvv]
    calc v * v * z = v * (v * z) := by group
      _ = v * (z * v) := by rw [hvz]
      _ = (v * z) * v := by group
      _ = (z * v) * v := by rw [hvz]
      _ = z * (v * v) := by group
  obtain ⟨hδ2, hnδ, hδvδ⟩ := AscFusion.kappa_delta_facts hz2 hvz hκ2 hκn hcomm
  have hκ4 : orderOf κ = 4 :=
    AscFusion.orderOf_eq_four_of_sq_eq hz2 (hK.isUniqueInvolution).ne_one hκ2
  have hκδ : κ * (κ * (v⁻¹ * κ * v)) = (κ * (v⁻¹ * κ * v)) * κ := by
    conv_lhs => rw [hcomm]
    group
  have hzδ : z * (κ * (v⁻¹ * κ * v)) = (κ * (v⁻¹ * κ * v)) * z := by
    have hcκ : Commute z κ := (hK.mul_comm_of_mem hκK).symm
    have hcv : Commute z v := hvz.symm
    exact (hcκ.mul_right ((hcv.inv_right.mul_right hcκ).mul_right hcv)).eq
  set δ : F := κ * (v⁻¹ * κ * v) with hδ
  have hδt : t * δ = δ * t := by rw [← hvv]; exact hnδ
  have hJδ : J ≠ conjSub δ J := by
    intro h
    have h1 : δ * v * δ⁻¹ ∈ conjSub δ J := conj_mem_conjSub hvJ
    rw [← h, hδvδ] at h1
    have h2 : z ∈ J := by
      have := J.mul_mem (J.inv_mem hvJ) h1
      rwa [← mul_assoc, inv_mul_cancel, one_mul] at this
    rcases hJt.unique z h2 hz2 with h3 | h3
    · exact (hK.isUniqueInvolution).ne_one h3
    · exact hne h3.symm
  have hzact : z ∈ actTriv δ := mem_actTriv_iff.mpr ⟨hzδ, fun I' hI' =>
    hB hK hI' hzS hδS hκK hκ4 hκδ⟩
  have htact : t ∈ actTriv δ := mem_actTriv_of_chain_min hJ hδ2 hδt hJδ hvJ hvv hδvδ hzt hzact
  have htI : t ∈ Subgroup.normalizer (I : Set F) := (mem_actTriv_iff.mp htact).2 I hI
  exact hJδ (conjSub_eq_of_mem_normalizer (hSy hJ hI htS hδS htI)).symm

theorem core_four_min {S : Set F} (hS : ∀ x ∈ S, ∀ g : F, g * x * g⁻¹ ∈ S) (hB : BstarOn F S)
    (hSy : SymOn F S) {K : Subgroup F} {z : F} (hK : Mem3 K z) (hzS : z ∈ S) {J : Subgroup F}
    {t : F} (hJ : Mem3 J t) (htS : t ∈ S) (hne : t ≠ z) {v : F} (hvJ : v ∈ J)
    (hv4 : orderOf v = 4) (hvz : v * z = z * v) (hvK : v * v ∈ Subgroup.normalizer (K : Set F)) :
    v ∈ Subgroup.normalizer (K : Set F) := by
  by_contra hv
  have hnt := nontrivAction hK hJ hne hvJ hv4 hvz hvK hv
  obtain ⟨κ, hκK, hκ2, hκn, hcomm⟩ := exists_kappa hK hv4 hvz hv hvK hnt
  obtain ⟨a, haK, b, hbK', ha2, hb2, hab, hat⟩ :=
    exists_twin_product hK hJ hne hvJ hv4 hvz hvK hv
  have hvK'' : conjSub v⁻¹ K ≠ K := conjSub_inv_ne hv
  obtain ⟨hK'mem, -, -, -⟩ := hK.twin_facts_conj (inv_comm_of_comm hvz) hvK''.symm
  have hκ'K' : v⁻¹ * κ * v ∈ conjSub v⁻¹ K := by
    have := conj_mem_conjSub (n := v⁻¹) hκK
    rwa [inv_inv] at this
  have hκ'2 : (v⁻¹ * κ * v) * (v⁻¹ * κ * v) = z := by
    calc (v⁻¹ * κ * v) * (v⁻¹ * κ * v) = v⁻¹ * (κ * κ) * v := by group
      _ = z := by rw [hκ2, conj_eq_of_comm hvz]
  obtain ⟨w, hw⟩ := exists_conj_of_twin_pairs hK hK'mem hvK''.symm haK hκK hbK' hκ'K' ha2 hb2 hab
    hκ2 hκ'2 hcomm
  rw [hat] at hw
  have hI : Mem3 (conjSub w J) (κ * (v⁻¹ * κ * v)) := by
    have := hJ.conj w
    rwa [hw] at this
  have hδS : κ * (v⁻¹ * κ * v) ∈ S := by
    rw [← hw]
    exact hS t htS w
  exact fusion_chain_contradiction_min hB hSy hK hJ hne hzS htS hvJ hv4 hvz hκK hκ2 hκn hcomm hI
    hδS

end Chain

end CFSG.ClassicalInvolution.Q3.Q3T6X
