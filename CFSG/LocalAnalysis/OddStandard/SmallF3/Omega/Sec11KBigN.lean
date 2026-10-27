module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec11KBigC
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec10Ctx

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup

variable {G : Type} [Group G]

private theorem sec11_secK0_le_centralizer_z (t z : G) :
    secK0 t z ≤ centralizer ({z} : Set G) := by
  rw [secK0, oTwoRes]
  refine (Subgroup.closure_le _).mpr ?_
  rintro x ⟨hx, -⟩
  exact hx.2

private theorem sec11_mem_normalizer_of_conj_mem [Finite G] {V : Subgroup G} {b : G}
    (h : ∀ v ∈ V, b * v * b⁻¹ ∈ V) : b ∈ normalizer (V : Set G) := by
  have hle : V.map (MulAut.conj b).toMonoidHom ≤ V := by
    rintro _ ⟨v, hv, rfl⟩
    exact h v hv
  exact Subgroup.mem_normalizer_iff_map_conj_eq.mpr (Subgroup.eq_of_le_of_card_ge hle
    (Subgroup.card_map_of_injective (MulAut.conj b).injective).ge)

private theorem sec11_odd_card_sup [Finite G] {K H : Subgroup G}
    (hHK : H ≤ normalizer (K : Set G)) (hK : Odd (Nat.card K)) (hH : Odd (Nat.card H)) :
    Odd (Nat.card (K ⊔ H : Subgroup G)) := by
  rw [sup_comm]
  haveI := Subgroup.normal_subgroupOf_of_le_normalizer hHK
  haveI := Subgroup.normal_subgroupOf_sup_of_le_normalizer hHK
  have e := QuotientGroup.quotientInfEquivProdNormalizerQuotient H K hHK
  rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (K.subgroupOf (H ⊔ K)),
    ← Nat.card_congr e.toEquiv,
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe (le_sup_right : K ≤ H ⊔ K)).toEquiv]
  exact (Odd.of_dvd_nat hH (Subgroup.card_quotient_dvd_card _)).mul hK

private theorem sec11_le_oddCore_of_le_centralizer [Finite G] {X : Subgroup G} {z : G}
    (hXH : X ≤ centralizer ({z} : Set G))
    (hXnorm : ∀ h ∈ centralizer ({z} : Set G), h ∈ normalizer (X : Set G)) :
    oddCoreIn X ≤ oddCoreIn (centralizer ({z} : Set G)) := by
  refine le_oddCoreIn_of_normal (le_trans (sec11KB_oddCore_le X) hXH) ?_
    (sec11KB_oddCore_odd X)
  rw [Subgroup.normal_subgroupOf_iff (le_trans (sec11KB_oddCore_le X) hXH)]
  intro n k hn hk
  exact sec11KB_conj_oddCore (hXnorm k hk) hn

theorem sec11KB_K0_conj [Finite G] {t z : G} {X : Subgroup G} (ht2 : t * t = 1) (htX : t ∈ X)
    (hXH : X ≤ centralizer ({z} : Set G))
    (hXnorm : ∀ h ∈ centralizer ({z} : Set G), h ∈ normalizer (X : Set G))
    (hOdd : ∀ h ∈ centralizer ({z} : Set G), Odd (orderOf h) → ∀ x ∈ X,
      h * x * h⁻¹ * x⁻¹ ∈ oddCoreIn X)
    {h : G} (hh : h ∈ centralizer ({z} : Set G)) :
    ∀ k ∈ secK0 t z, h * k * h⁻¹ ∈ oddCoreIn X ⊔ secK0 t z := by
  set S : Subgroup G := oddCoreIn X ⊔ secK0 t z with hS
  have hgen : {y : G | y ∈ centralizer ({t} : Set G) ⊓ centralizer ({z} : Set G) ∧
      Odd (orderOf y)} ⊆ S.comap (MulAut.conj h).toMonoidHom := by
    rintro y ⟨⟨hyt, hyz⟩, hyodd⟩
    refine Subgroup.mem_comap.mpr ?_
    have hwH : h * y * h⁻¹ ∈ centralizer ({z} : Set G) :=
      Subgroup.mul_mem _ (Subgroup.mul_mem _ hh hyz) (Subgroup.inv_mem _ hh)
    have hwN : h * y * h⁻¹ ∈ normalizer (X : Set G) :=
      Subgroup.mul_mem _ (Subgroup.mul_mem _ (hXnorm h hh) (hXnorm y hyz))
        (Subgroup.inv_mem _ (hXnorm h hh))
    have hword : orderOf (h * y * h⁻¹) = orderOf y := by
      rw [← MulAut.conj_apply]
      exact orderOf_injective (MulAut.conj h).toMonoidHom (MulAut.conj h).injective y
    have hwodd : Odd (orderOf (h * y * h⁻¹)) := hword.symm ▸ hyodd
    have hwt : (h * y * h⁻¹) * t * (h * y * h⁻¹)⁻¹ * t⁻¹ ∈ oddCoreIn X :=
      hOdd (h * y * h⁻¹) hwH hwodd t htX
    obtain ⟨o, ho, hoc⟩ := sec11KB_frattini ht2 htX hwN hwt
    have hocH : o⁻¹ * (h * y * h⁻¹) ∈ centralizer ({z} : Set G) :=
      Subgroup.mul_mem _ (Subgroup.inv_mem _ (hXH (sec11KB_oddCore_le X ho))) hwH
    have hocodd : Odd (orderOf (o⁻¹ * (h * y * h⁻¹))) :=
      sec11KB_odd_lift (sec11KB_oddCore_odd X)
        (fun n hn => sec11KB_conj_oddCore hwN hn) hwodd ho
    have hocK0 : o⁻¹ * (h * y * h⁻¹) ∈ secK0 t z := by
      rw [secK0, oTwoRes]
      exact Subgroup.subset_closure ⟨⟨hoc, hocH⟩, hocodd⟩
    have hwS : h * y * h⁻¹ ∈ S := by
      have heq : h * y * h⁻¹ = o * (o⁻¹ * (h * y * h⁻¹)) := by group
      rw [heq]
      exact S.mul_mem (Subgroup.mem_sup_left ho) (Subgroup.mem_sup_right hocK0)
    exact hwS
  intro k hk
  have hk' : k ∈ S.comap (MulAut.conj h).toMonoidHom := by
    rw [secK0, oTwoRes] at hk
    exact (Subgroup.closure_le _).mpr hgen hk
  exact (Subgroup.mem_comap.mp hk')

theorem sec11KB_Ot_le [Finite G] {t z : G} {X : Subgroup G} (ht2 : t * t = 1) (htX : t ∈ X)
    (hXH : X ≤ centralizer ({z} : Set G))
    (hXnorm : ∀ h ∈ centralizer ({z} : Set G), h ∈ normalizer (X : Set G))
    (hOdd : ∀ h ∈ centralizer ({z} : Set G), Odd (orderOf h) → ∀ x ∈ X,
      h * x * h⁻¹ * x⁻¹ ∈ oddCoreIn X)
    (hOt : oddCoreIn (centralizer ({t} : Set G)) ≤ secK0 t z) :
    oddCoreIn (centralizer ({t} : Set G)) ≤ oddCoreIn (centralizer ({z} : Set G)) := by
  let O : Subgroup G := oddCoreIn X
  let C : Subgroup G :=
    { carrier := {c | c ∈ centralizer ({z} : Set G) ∧
        ∀ x ∈ X, c * x * c⁻¹ * x⁻¹ ∈ O}
      one_mem' := by
        refine ⟨Subgroup.one_mem _, ?_⟩
        intro x hx
        simpa using O.one_mem
      mul_mem' := by
        rintro a b ⟨haH, haX⟩ ⟨hbH, hbX⟩
        refine ⟨Subgroup.mul_mem _ haH hbH, ?_⟩
        intro x hx
        have hconj : a * (b * x * b⁻¹ * x⁻¹) * a⁻¹ ∈ O :=
          sec11KB_conj_oddCore (hXnorm a haH) (hbX x hx)
        have hsum := O.mul_mem hconj (haX x hx)
        convert hsum using 1
        group
      inv_mem' := by
        rintro a ⟨haH, haX⟩
        refine ⟨Subgroup.inv_mem _ haH, ?_⟩
        intro x hx
        have hconj : a⁻¹ * (a * x * a⁻¹ * x⁻¹)⁻¹ * a ∈ O := by
          simpa using sec11KB_conj_oddCore (hXnorm a⁻¹ (Subgroup.inv_mem _ haH))
            (O.inv_mem (haX x hx))
        convert hconj using 1
        group }
  have hOleC : O ≤ C := by
    intro o ho
    refine ⟨le_trans (sec11KB_oddCore_le X) hXH ho, ?_⟩
    intro x hx
    have hxox : x * o⁻¹ * x⁻¹ ∈ O := sec11KB_oddCore_norm X hx (O.inv_mem ho)
    have hprod := O.mul_mem ho hxox
    convert hprod using 1
    group
  have hOtleC : oddCoreIn (centralizer ({t} : Set G)) ≤ C := by
    intro a ha
    have haH : a ∈ centralizer ({z} : Set G) := sec11_secK0_le_centralizer_z t z (hOt ha)
    refine ⟨haH, ?_⟩
    intro x hx
    exact hOdd a haH (odd_orderOf_of_mem_oddCoreIn ha) x hx
  let Y : Subgroup G := O ⊔ oddCoreIn (centralizer ({t} : Set G))
  have hYC : Y ≤ C := sup_le hOleC hOtleC
  have hOtNormO : oddCoreIn (centralizer ({t} : Set G)) ≤ normalizer (O : Set G) := by
    intro a ha
    refine sec11_mem_normalizer_of_conj_mem ?_
    intro n hn
    exact sec11KB_conj_oddCore (hXnorm a (sec11_secK0_le_centralizer_z t z (hOt ha))) hn
  have hYodd : Odd (Nat.card Y) := by
    have h := sec11_odd_card_sup hOtNormO (sec11KB_oddCore_odd X)
      (sec11KB_oddCore_odd (centralizer ({t} : Set G)))
    simpa [Y] using h
  have hCYnorm : C ≤ normalizer (Y : Set G) := by
    intro c hc
    refine sec11_mem_normalizer_of_conj_mem ?_
    intro v hv
    obtain ⟨o, ho, hocT⟩ := sec11KB_frattini ht2 htX (hXnorm c hc.1) (hc.2 t htX)
    have hocC : o⁻¹ * c ∈ C := C.mul_mem (C.inv_mem (hOleC ho)) hc
    have hc'H : o⁻¹ * c ∈ centralizer ({z} : Set G) := hocC.1
    have hc'T : o⁻¹ * c ∈ centralizer ({t} : Set G) := hocT
    have hcmap : Y.map (MulAut.conj (o⁻¹ * c)).toMonoidHom ≤ Y := by
      change (O ⊔ oddCoreIn (centralizer ({t} : Set G))).map
        (MulAut.conj (o⁻¹ * c)).toMonoidHom ≤ Y
      rw [Subgroup.map_sup]
      refine sup_le ?_ ?_
      · rintro _ ⟨n, hn, rfl⟩
        exact Subgroup.mem_sup_left (sec11KB_conj_oddCore (hXnorm (o⁻¹ * c) hc'H) hn)
      · rintro _ ⟨n, hn, rfl⟩
        exact Subgroup.mem_sup_right
          (sec11KB_oddCore_norm (centralizer ({t} : Set G)) hc'T hn)
    have hcv : (o⁻¹ * c) * v * (o⁻¹ * c)⁻¹ ∈ Y := hcmap ⟨v, hv, rfl⟩
    have hoY : o ∈ Y := Subgroup.mem_sup_left ho
    have heq : c * v * c⁻¹ = o * ((o⁻¹ * c) * v * (o⁻¹ * c)⁻¹) * o⁻¹ := by group
    rw [heq]
    exact Y.mul_mem (Y.mul_mem hoY hcv) (Y.inv_mem hoY)
  have hYOC : Y ≤ oddCoreIn C := by
    refine le_oddCoreIn_of_normal hYC ?_ hYodd
    rw [Subgroup.normal_subgroupOf_iff_le_normalizer hYC]
    exact hCYnorm
  have hCleH : C ≤ centralizer ({z} : Set G) := fun c hc => hc.1
  have hCH : (C.subgroupOf (centralizer ({z} : Set G))).Normal := by
    rw [Subgroup.normal_subgroupOf_iff hCleH]
    intro c k hc hk
    refine ⟨?_, ?_⟩
    · exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hk hc.1) (Subgroup.inv_mem _ hk)
    · intro x hx
      have hx' : k⁻¹ * x * k ∈ X := by
        have h := (Subgroup.mem_normalizer_iff.mp
          (hXnorm k⁻¹ (Subgroup.inv_mem _ hk)) x).mp hx
        simpa using h
      have hcc := hc.2 (k⁻¹ * x * k) hx'
      have hconj := sec11KB_conj_oddCore (hXnorm k hk) hcc
      convert hconj using 1
      group
  have hCOC : oddCoreIn C ≤ oddCoreIn (centralizer ({z} : Set G)) :=
    oddCoreIn_le_of_normal hCleH hCH
  have hOtY : oddCoreIn (centralizer ({t} : Set G)) ≤ Y := le_sup_right
  exact le_trans (le_trans hOtY hYOC) hCOC

theorem sec11_KBig_core [Finite G] {t z : G} {K1 K2 X : Subgroup G} (ht2 : t * t = 1)
    (htX : t ∈ X) (hXH : X ≤ centralizer ({z} : Set G))
    (hXnorm : ∀ h ∈ centralizer ({z} : Set G), h ∈ normalizer (X : Set G))
    (hK0 : secK0 t z = oddCoreIn (centralizer ({t} : Set G)) ⊔ K1 ⊔ K2)
    (hOdd : ∀ h ∈ centralizer ({z} : Set G), Odd (orderOf h) → ∀ x ∈ X,
      h * x * h⁻¹ * x⁻¹ ∈ oddCoreIn X) :
    centralizer ({z} : Set G) ≤
      normalizer ((K1 ⊔ K2 ⊔ oddCoreIn (centralizer ({z} : Set G)) : Subgroup G) : Set G) := by
  let M : Subgroup G := K1 ⊔ K2 ⊔ oddCoreIn (centralizer ({z} : Set G))
  have hON : oddCoreIn X ≤ oddCoreIn (centralizer ({z} : Set G)) :=
    sec11_le_oddCore_of_le_centralizer hXH hXnorm
  have hKK0 : K1 ⊔ K2 ≤ secK0 t z := by
    rw [hK0]
    exact sup_le (le_trans le_sup_right le_sup_left) le_sup_right
  have hOt : oddCoreIn (centralizer ({t} : Set G)) ≤ secK0 t z := by
    rw [hK0]
    exact le_trans le_sup_left le_sup_left
  have hOtN : oddCoreIn (centralizer ({t} : Set G)) ≤
      oddCoreIn (centralizer ({z} : Set G)) :=
    sec11KB_Ot_le ht2 htX hXH hXnorm hOdd hOt
  have hK0M : secK0 t z ≤ M := by
    rw [hK0]
    refine sup_le (sup_le ?_ ?_) ?_
    · exact le_trans hOtN le_sup_right
    · exact le_trans le_sup_left le_sup_left
    · exact le_trans le_sup_right le_sup_left
  have hOM : oddCoreIn X ⊔ secK0 t z ≤ M :=
    sup_le (le_trans hON le_sup_right) hK0M
  have hmap : ∀ g ∈ centralizer ({z} : Set G), M.map (MulAut.conj g).toMonoidHom ≤ M := by
    intro g hg
    have hA : (K1 ⊔ K2).map (MulAut.conj g).toMonoidHom ≤ M := by
      rintro _ ⟨a, ha, rfl⟩
      exact hOM (sec11KB_K0_conj ht2 htX hXH hXnorm hOdd hg a (hKK0 ha))
    have hN : (oddCoreIn (centralizer ({z} : Set G))).map
        (MulAut.conj g).toMonoidHom ≤ M := by
      rintro _ ⟨n, hn, rfl⟩
      exact Subgroup.mem_sup_right (conj_mem_oddCoreIn (Subgroup.le_normalizer hg) hn)
    change ((K1 ⊔ K2) ⊔ oddCoreIn (centralizer ({z} : Set G))).map
      (MulAut.conj g).toMonoidHom ≤ M
    rw [Subgroup.map_sup]
    exact sup_le hA hN
  intro g hg
  rw [Subgroup.mem_normalizer_iff]
  intro m
  constructor
  · intro hm
    exact hmap g hg ⟨m, hm, rfl⟩
  · intro hm
    have hg' : g⁻¹ ∈ centralizer ({z} : Set G) := Subgroup.inv_mem _ hg
    refine hmap g⁻¹ hg' ⟨g * m * g⁻¹, hm, ?_⟩
    change (MulAut.conj g⁻¹) (g * m * g⁻¹) = m
    rw [MulAut.conj_apply]
    group

end CFSG.OddStandard.SmallF3.Omega
