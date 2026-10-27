module

public import CFSG.LocalAnalysis.EvenSporadicStandard.M24Std.DResCSP1
public import CFSG.LocalAnalysis.EvenSporadicStandard.M24Std.DResCSSchur

public section

namespace CFSG.EvenSporadicStandard.M24Std.DRes

open Subgroup CFSG.Open
open scoped commutatorElement

section Rho

variable {Y : Type} [Group Y] [Finite Y] {t : Y} {K : Subgroup Y} {φ : K →* Equiv.Perm (Fin 6)}

@[expose] noncomputable def rho6
    (e : egaLayer (Yb Y) ≃* alternatingGroup (Fin 6) × alternatingGroup (Fin 6))
    (hP : ∀ p ∈ P1 φ, proj Y p ∈ egaLayer (Yb Y)) :
    ↥(P1 φ) →* alternatingGroup (Fin 6) × alternatingGroup (Fin 6) :=
  e.toMonoidHom.comp (((proj Y).comp (P1 φ).subtype).codRestrict (egaLayer (Yb Y))
    (fun p => hP p p.2))

theorem rho6_apply (e : egaLayer (Yb Y) ≃* alternatingGroup (Fin 6) × alternatingGroup (Fin 6))
    (hP : ∀ p ∈ P1 φ, proj Y p ∈ egaLayer (Yb Y)) (p : ↥(P1 φ)) :
    rho6 e hP p = e ⟨proj Y p, hP p p.2⟩ := rfl

theorem rho6_eq_one_iff
    (e : egaLayer (Yb Y) ≃* alternatingGroup (Fin 6) × alternatingGroup (Fin 6))
    (hP : ∀ p ∈ P1 φ, proj Y p ∈ egaLayer (Yb Y)) (p : ↥(P1 φ)) :
    rho6 e hP p = 1 ↔ (p : Y) ∈ fusionOddCore Y := by
  rw [rho6_apply, ← map_one e, e.injective.eq_iff]
  constructor
  · intro h
    exact (QuotientGroup.eq_one_iff _).1 (congrArg Subtype.val h)
  · intro h
    exact Subtype.ext ((QuotientGroup.eq_one_iff _).2 h)

theorem rho6_conj {f₁ f₂ : MulAut (alternatingGroup (Fin 6))}
    (e : egaLayer (Yb Y) ≃* alternatingGroup (Fin 6) × alternatingGroup (Fin 6))
    (hP : ∀ p ∈ P1 φ, proj Y p ∈ egaLayer (Yb Y)) (hsw : IsSwap6 t e f₁ f₂) (p : ↥(P1 φ)) :
    rho6 e hP ⟨t * p * t⁻¹, (P1_normal).conj_mem (p : Y) p.2 t⟩ =
      (f₁ (rho6 e hP p).2, f₂ (rho6 e hP p).1) := by
  have h1 := hsw.conj ⟨proj Y p, hP p p.2⟩
  show e ⟨proj Y (t * (p : Y) * t⁻¹), hP _ ((P1_normal).conj_mem (p : Y) p.2 t)⟩ =
    (f₁ (e ⟨proj Y p, hP p p.2⟩).2, f₂ (e ⟨proj Y p, hP p p.2⟩).1)
  rw [← h1]
  congr 1

end Rho

structure YSplit {Y : Type} [Group Y] [Finite Y] (P : Subgroup Y) (t : Y) (S1 S2 : Subgroup Y)
    (π1 : S1 →* alternatingGroup (Fin 6)) (π2 : S2 →* alternatingGroup (Fin 6)) : Prop where
  q1 : QuasiData S1 (S1 ⊓ fusionOddCore Y) π1
  q2 : QuasiData S2 (S2 ⊓ fusionOddCore Y) π2
  le1 : S1 ≤ P
  le2 : S2 ≤ P
  sup : S1 ⊔ S2 = P
  comm : ∀ a ∈ S1, ∀ b ∈ S2, a * b = b * a
  swap12 : ∀ a ∈ S1, t * a * t⁻¹ ∈ S2
  swap21 : ∀ a ∈ S2, t * a * t⁻¹ ∈ S1
  ker : ∀ w ∈ P ⊓ fusionOddCore Y, ∃ a ∈ S1 ⊓ fusionOddCore Y, ∃ b ∈ S2 ⊓ fusionOddCore Y,
    w = a * b
  ind : ∀ x ∈ S1, ∀ y ∈ S2, x * y ∈ fusionOddCore Y → x ∈ fusionOddCore Y ∧ y ∈ fusionOddCore Y

section Split

variable {Y : Type} [Group Y] [Finite Y] {t : Y} {K : Subgroup Y} {φ : K →* Equiv.Perm (Fin 6)}

namespace CYHyp

variable (hY : CYHyp t K φ)
include hY

theorem ySplit
    (e : egaLayer (Yb Y) ≃* alternatingGroup (Fin 6) × alternatingGroup (Fin 6)) :
    ∃ (S1 S2 : Subgroup Y) (π1 : S1 →* alternatingGroup (Fin 6))
      (π2 : S2 →* alternatingGroup (Fin 6)), YSplit (P1 φ) t S1 S2 π1 π2 := by
  obtain ⟨f₁, f₂, hsw, hcard, hK0, hGOZ, hZO⟩ := hY.swap e
  have hmap := hY.P1_map_eq e
  have hP : ∀ p ∈ P1 φ, proj Y p ∈ egaLayer (Yb Y) := fun p hp => by
    rw [← hmap]
    exact Subgroup.mem_map_of_mem _ hp
  set ρ := rho6 e hP with hρ
  have hρs : Function.Surjective ρ := by
    intro a
    have : ((e.symm a : egaLayer (Yb Y)) : Yb Y) ∈ (P1 φ).map (proj Y) := by
      rw [hmap]; exact (e.symm a).2
    obtain ⟨p, hp, hpa⟩ := Subgroup.mem_map.1 this
    refine ⟨⟨p, hp⟩, ?_⟩
    rw [hρ, rho6_apply]
    have : (⟨proj Y p, hP p hp⟩ : egaLayer (Yb Y)) = e.symm a := Subtype.ext hpa
    rw [this, MulEquiv.apply_symm_apply]
  have hcentO := hY.P1_le_centralizer e
  have hker : ρ.ker ≤ center ↥(P1 φ) := by
    intro x hx
    have hxO : (x : Y) ∈ fusionOddCore Y := (rho6_eq_one_iff e hP x).1 hx
    refine Subgroup.mem_center_iff.2 fun g => Subtype.ext ?_
    exact (mem_centralizer_iff.1 (hcentO g.2) _ hxO).symm
  have hodd : Odd (Nat.card ρ.ker) := by
    refine Odd.of_dvd_nat (odd_natCard_fusionOddCore Y) ?_
    have hle : ρ.ker.map (P1 φ).subtype ≤ fusionOddCore Y := by
      rintro _ ⟨x, hx, rfl⟩
      exact (rho6_eq_one_iff e hP x).1 hx
    have := Subgroup.card_dvd_of_le hle
    rwa [Subgroup.card_map_of_injective (P1 φ).subtype_injective] at this
  have hperf : commutator ↥(P1 φ) = ⊤ := by
    have : Group.IsPerfect ↥(P1 φ) := Subgroup.isPerfect_iff.2 (P1_perfect hY)
    exact Group.IsPerfect.commutator_eq_top
  set S1' : Subgroup ↥(P1 φ) := schurS1 ρ with hS1'
  set S2' : Subgroup ↥(P1 φ) := schurS2 ρ with hS2'
  set S1 : Subgroup Y := S1'.map (P1 φ).subtype with hS1
  set S2 : Subgroup Y := S2'.map (P1 φ).subtype with hS2
  have hS1P : S1 ≤ P1 φ := Subgroup.map_subtype_le _
  have hS2P : S2 ≤ P1 φ := Subgroup.map_subtype_le _
  have hmem1 : ∀ y ∈ S1, ∃ h : y ∈ P1 φ, (⟨y, h⟩ : ↥(P1 φ)) ∈ S1' := by
    rintro _ ⟨x, hx, rfl⟩
    exact ⟨x.2, hx⟩
  have hmem2 : ∀ y ∈ S2, ∃ h : y ∈ P1 φ, (⟨y, h⟩ : ↥(P1 φ)) ∈ S2' := by
    rintro _ ⟨x, hx, rfl⟩
    exact ⟨x.2, hx⟩
  have hperf1 : ⁅S1, S1⁆ = S1 := by
    rw [hS1, ← Subgroup.map_commutator, schurS1_perfect hρs hker]
  have hperf2 : ⁅S2, S2⁆ = S2 := by
    rw [hS2, ← Subgroup.map_commutator, schurS2_perfect hρs hker]
  have hcomm : ∀ a ∈ S1, ∀ b ∈ S2, a * b = b * a := by
    rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    exact congrArg Subtype.val (commute_schur hρs hker a ha b hb)
  have hsup : S1 ⊔ S2 = P1 φ := by
    rw [hS1, hS2, ← Subgroup.map_sup, sup_schur hperf hρs hker, Subgroup.map_top,
      Subgroup.range_subtype]
  have hZ1 : S1 ⊓ fusionOddCore Y = (S1' ⊓ ρ.ker).map (P1 φ).subtype := by
    ext y
    constructor
    · rintro ⟨hy1, hyO⟩
      obtain ⟨h, hy⟩ := hmem1 y hy1
      exact ⟨⟨y, h⟩, ⟨hy, (rho6_eq_one_iff e hP ⟨y, h⟩).2 hyO⟩, rfl⟩
    · rintro ⟨x, ⟨hx1, hx2⟩, rfl⟩
      exact ⟨⟨x, hx1, rfl⟩, (rho6_eq_one_iff e hP x).1 hx2⟩
  have hZ2 : S2 ⊓ fusionOddCore Y = (S2' ⊓ ρ.ker).map (P1 φ).subtype := by
    ext y
    constructor
    · rintro ⟨hy1, hyO⟩
      obtain ⟨h, hy⟩ := hmem2 y hy1
      exact ⟨⟨y, h⟩, ⟨hy, (rho6_eq_one_iff e hP ⟨y, h⟩).2 hyO⟩, rfl⟩
    · rintro ⟨x, ⟨hx1, hx2⟩, rfl⟩
      exact ⟨⟨x, hx1, rfl⟩, (rho6_eq_one_iff e hP x).1 hx2⟩
  have hc1 : Nat.card (S1 ⊓ fusionOddCore Y : Subgroup Y) ∣ 3 := by
    rw [hZ1, Subgroup.card_map_of_injective (P1 φ).subtype_injective]
    exact card_inf_ker_schurS1 hρs hker hodd
  have hc2 : Nat.card (S2 ⊓ fusionOddCore Y : Subgroup Y) ∣ 3 := by
    rw [hZ2, Subgroup.card_map_of_injective (P1 φ).subtype_injective]
    exact card_inf_ker_schurS2 hρs hker hodd
  have hconj : ∀ p : ↥(P1 φ), ρ ⟨t * p * t⁻¹, (P1_normal).conj_mem (p : Y) p.2 t⟩ =
      (f₁ (ρ p).2, f₂ (ρ p).1) := fun p => rho6_conj e hP hsw p
  let T1y : Subgroup Y := (firstSub6 ρ).map (P1 φ).subtype
  let T2y : Subgroup Y := (secondSub6 ρ).map (P1 φ).subtype
  have hS1T : S1 = ⁅T1y, T1y⁆ := by
    rw [hS1, hS1', schurS1, Subgroup.map_commutator]
  have hS2T : S2 = ⁅T2y, T2y⁆ := by
    rw [hS2, hS2', schurS2, Subgroup.map_commutator]
  have hT12 : T1y.map (MulAut.conj t).toMonoidHom ≤ T2y := by
    rintro _ ⟨_, ⟨p, hp, rfl⟩, rfl⟩
    refine ⟨⟨t * p * t⁻¹, (P1_normal).conj_mem (p : Y) p.2 t⟩, mem_secondSub6.2 ?_, rfl⟩
    rw [hconj]
    show f₁ (ρ p).2 = 1
    rw [mem_firstSub6.1 hp, map_one]
  have hT21 : T2y.map (MulAut.conj t).toMonoidHom ≤ T1y := by
    rintro _ ⟨_, ⟨p, hp, rfl⟩, rfl⟩
    refine ⟨⟨t * p * t⁻¹, (P1_normal).conj_mem (p : Y) p.2 t⟩, mem_firstSub6.2 ?_, rfl⟩
    rw [hconj]
    show f₂ (ρ p).1 = 1
    rw [mem_secondSub6.1 hp, map_one]
  have hswap12 : ∀ a ∈ S1, t * a * t⁻¹ ∈ S2 := by
    intro a ha
    have : S1.map (MulAut.conj t).toMonoidHom ≤ S2 := by
      rw [hS1T, hS2T, Subgroup.map_commutator]
      exact Subgroup.commutator_mono hT12 hT12
    exact this ⟨a, ha, rfl⟩
  have hswap21 : ∀ a ∈ S2, t * a * t⁻¹ ∈ S1 := by
    intro a ha
    have : S2.map (MulAut.conj t).toMonoidHom ≤ S1 := by
      rw [hS1T, hS2T, Subgroup.map_commutator]
      exact Subgroup.commutator_mono hT21 hT21
    exact this ⟨a, ha, rfl⟩
  have hOn : (fusionOddCore Y).Normal := inferInstance
  have hcardle12 : Nat.card (S1 ⊓ fusionOddCore Y : Subgroup Y) ≤
      Nat.card (S2 ⊓ fusionOddCore Y : Subgroup Y) := by
    rw [← Subgroup.card_map_of_injective (f := (MulAut.conj t).toMonoidHom)
      (MulAut.conj t).injective (K := (S1 ⊓ fusionOddCore Y : Subgroup Y))]
    refine Subgroup.card_le_of_le ?_
    rintro _ ⟨a, ha, rfl⟩
    exact ⟨hswap12 a ha.1, hOn.conj_mem a ha.2 t⟩
  have hcardle21 : Nat.card (S2 ⊓ fusionOddCore Y : Subgroup Y) ≤
      Nat.card (S1 ⊓ fusionOddCore Y : Subgroup Y) := by
    rw [← Subgroup.card_map_of_injective (f := (MulAut.conj t).toMonoidHom)
      (MulAut.conj t).injective (K := (S2 ⊓ fusionOddCore Y : Subgroup Y))]
    refine Subgroup.card_le_of_le ?_
    rintro _ ⟨a, ha, rfl⟩
    exact ⟨hswap21 a ha.1, hOn.conj_mem a ha.2 t⟩
  have hker2 : ∀ w ∈ P1 φ ⊓ fusionOddCore Y, ∃ a ∈ S1 ⊓ fusionOddCore Y,
      ∃ b ∈ S2 ⊓ fusionOddCore Y, w = a * b := by
    rintro w ⟨hwP, hwO⟩
    have hk : (⟨w, hwP⟩ : ↥(P1 φ)) ∈ ρ.ker := (rho6_eq_one_iff e hP _).2 hwO
    obtain ⟨a, ha, b, hb, hab⟩ := ker_eq_mul hperf hρs hker hk
    refine ⟨a, ?_, b, ?_, congrArg Subtype.val hab⟩
    · rw [hZ1]; exact ⟨a, ha, rfl⟩
    · rw [hZ2]; exact ⟨b, hb, rfl⟩
  have hZk : Zk φ ≤ P1 φ ⊓ fusionOddCore Y := le_inf (Zk_le_K0.trans K0_le_P1) hZO
  have hc1' : Nat.card (S1 ⊓ fusionOddCore Y : Subgroup Y) = 3 := by
    rcases (Nat.dvd_prime Nat.prime_three).1 hc1 with h1 | h1
    · exfalso
      have h2 : Nat.card (S2 ⊓ fusionOddCore Y : Subgroup Y) = 1 := by
        have := hcardle12
        have h3 : 0 < Nat.card (S2 ⊓ fusionOddCore Y : Subgroup Y) := Nat.card_pos
        have := (Nat.dvd_prime Nat.prime_three).1 hc2
        omega
      have hb1 : S1 ⊓ fusionOddCore Y = ⊥ := Subgroup.eq_bot_of_card_eq _ h1
      have hb2 : S2 ⊓ fusionOddCore Y = ⊥ := Subgroup.eq_bot_of_card_eq _ h2
      have : Zk φ ≤ ⊥ := by
        intro w hw
        obtain ⟨a, ha, b, hb, rfl⟩ := hker2 w (hZk hw)
        rw [hb1, Subgroup.mem_bot] at ha
        rw [hb2, Subgroup.mem_bot] at hb
        rw [ha, hb, mul_one]
        exact one_mem _
      have := Subgroup.card_le_of_le this
      rw [Subgroup.card_bot, hY.card_Zk] at this
      omega
    · exact h1
  have hc2' : Nat.card (S2 ⊓ fusionOddCore Y : Subgroup Y) = 3 := by
    have := hcardle12
    omega
  let π1 : ↥S1 →* alternatingGroup (Fin 6) :=
    (MonoidHom.fst _ _).comp (ρ.comp (inclusion hS1P))
  let π2 : ↥S2 →* alternatingGroup (Fin 6) :=
    (MonoidHom.snd _ _).comp (ρ.comp (inclusion hS2P))
  have q1 : QuasiData S1 (S1 ⊓ fusionOddCore Y) π1 :=
    { perfect := hperf1
      Z_le := inf_le_left
      card_Z := hc1'
      surj := by
        intro c
        obtain ⟨y, hy, hyc⟩ := exists_mem_schurS1 hρs c
        refine ⟨⟨y.1, ⟨y, hy, rfl⟩⟩, ?_⟩
        show (ρ y).1 = c
        rw [hyc]
      ker := by
        intro g
        obtain ⟨h, hg⟩ := hmem1 g g.2
        have h2 : (ρ ⟨g, h⟩).2 = 1 := mem_firstSub6.1 (schurS1_le hg)
        constructor
        · intro h1
          have h1' : (ρ ⟨g, h⟩).1 = 1 := h1
          exact ⟨g.2, (rho6_eq_one_iff e hP _).1 (Prod.ext h1' h2)⟩
        · intro hgO
          have : ρ ⟨g, h⟩ = 1 := (rho6_eq_one_iff e hP _).2 hgO.2
          show (ρ ⟨g, h⟩).1 = 1
          rw [this]
          rfl }
  have q2 : QuasiData S2 (S2 ⊓ fusionOddCore Y) π2 :=
    { perfect := hperf2
      Z_le := inf_le_left
      card_Z := hc2'
      surj := by
        intro c
        obtain ⟨y, hy, hyc⟩ := exists_mem_schurS2 hρs c
        refine ⟨⟨y.1, ⟨y, hy, rfl⟩⟩, ?_⟩
        show (ρ y).2 = c
        rw [hyc]
      ker := by
        intro g
        obtain ⟨h, hg⟩ := hmem2 g g.2
        have h2 : (ρ ⟨g, h⟩).1 = 1 := mem_secondSub6.1 (schurS2_le hg)
        constructor
        · intro h1
          have h1' : (ρ ⟨g, h⟩).2 = 1 := h1
          exact ⟨g.2, (rho6_eq_one_iff e hP _).1 (Prod.ext h2 h1')⟩
        · intro hgO
          have : ρ ⟨g, h⟩ = 1 := (rho6_eq_one_iff e hP _).2 hgO.2
          show (ρ ⟨g, h⟩).2 = 1
          rw [this]
          rfl }
  have hind : ∀ x ∈ S1, ∀ y ∈ S2, x * y ∈ fusionOddCore Y →
      x ∈ fusionOddCore Y ∧ y ∈ fusionOddCore Y := by
    intro x hx y hy hxy
    obtain ⟨h1, hx'⟩ := hmem1 x hx
    obtain ⟨h2, hy'⟩ := hmem2 y hy
    have hxa : (ρ ⟨x, h1⟩).2 = 1 := mem_firstSub6.1 (schurS1_le hx')
    have hyb : (ρ ⟨y, h2⟩).1 = 1 := mem_secondSub6.1 (schurS2_le hy')
    have hprod : ρ ⟨x, h1⟩ * ρ ⟨y, h2⟩ = 1 :=
      (rho6_eq_one_iff e hP ⟨x * y, (P1 φ).mul_mem h1 h2⟩).2 hxy ▸ (map_mul ρ _ _).symm
    have hx1 : (ρ ⟨x, h1⟩).1 = 1 := by
      have := congrArg Prod.fst hprod
      simpa [hyb] using this
    have hy1 : (ρ ⟨y, h2⟩).2 = 1 := by
      have := congrArg Prod.snd hprod
      simpa [hxa] using this
    exact ⟨(rho6_eq_one_iff e hP ⟨x, h1⟩).1 (Prod.ext hx1 hxa),
      (rho6_eq_one_iff e hP ⟨y, h2⟩).1 (Prod.ext hyb hy1)⟩
  exact ⟨S1, S2, π1, π2, ⟨q1, q2, hS1P, hS2P, hsup, hcomm, hswap12, hswap21, hker2, hind⟩⟩

end CYHyp

end Split

end CFSG.EvenSporadicStandard.M24Std.DRes
