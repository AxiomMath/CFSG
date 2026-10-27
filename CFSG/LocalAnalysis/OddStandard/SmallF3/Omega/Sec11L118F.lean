module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec11L118A
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec11L117E
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec11L116

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {G : Type} [Group G]

theorem sec11_comm_z_of_isElemAbelianMod {z : G} {U : Subgroup G} (hz2 : z * z = 1)
    (hz1 : z ≠ 1) (hzU : z ∈ U) (hU : IsElemAbelianMod z U) {a : G} (ha : a ∈ U) :
    a * z = z * a := by
  have hc : a * z * a⁻¹ * z⁻¹ ∈ zpowers z := (hU a ha z hzU).1
  rcases sec11_eq_one_or_of_mem_zpowers hz2 hc with h | h
  · have h1 : a * z * a⁻¹ = z := mul_inv_eq_one.mp h
    calc a * z = (a * z * a⁻¹) * a := by group
      _ = z * a := by rw [h1]
  · exfalso
    have h1 : a * z * a⁻¹ = z * z := by
      calc a * z * a⁻¹ = (a * z * a⁻¹ * z⁻¹) * z := by group
        _ = z * z := by rw [h]
    rw [hz2] at h1
    apply hz1
    calc z = a⁻¹ * (a * z * a⁻¹) * a := by group
      _ = 1 := by rw [h1]; group

theorem sec11_le_hatCent {t z : G} {U : Subgroup G} (hz2 : z * z = 1) (hz1 : z ≠ 1)
    (hzU : z ∈ U) (htU : t ∈ U) (hU : IsElemAbelianMod z U) : U ≤ hatCent t z := by
  have key : ∀ b ∈ U, ∀ x ∈ (zpowers t ⊔ zpowers z : Subgroup G),
      b * x * b⁻¹ ∈ (zpowers t ⊔ zpowers z : Subgroup G) := by
    intro b hb x hx
    have hle : (zpowers t ⊔ zpowers z : Subgroup G) ≤
        (zpowers t ⊔ zpowers z : Subgroup G).comap (MulAut.conj b).toMonoidHom := by
      refine sup_le ?_ ?_
      · rw [Subgroup.zpowers_le]
        show b * t * b⁻¹ ∈ zpowers t ⊔ zpowers z
        have hc : b * t * b⁻¹ * t⁻¹ ∈ zpowers z := (hU b hb t htU).1
        have e : b * t * b⁻¹ = (b * t * b⁻¹ * t⁻¹) * t := by group
        rw [e]
        exact Subgroup.mul_mem _ (Subgroup.mem_sup_right hc)
          (Subgroup.mem_sup_left (Subgroup.mem_zpowers t))
      · rw [Subgroup.zpowers_le]
        show b * z * b⁻¹ ∈ zpowers t ⊔ zpowers z
        have hbz : b * z = z * b := sec11_comm_z_of_isElemAbelianMod hz2 hz1 hzU hU hb
        have e : b * z * b⁻¹ = z := by rw [hbz, mul_assoc, mul_inv_cancel, mul_one]
        rw [e]
        exact Subgroup.mem_sup_right (Subgroup.mem_zpowers z)
    exact hle hx
  intro a ha
  refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
  · exact Subgroup.mem_centralizer_singleton_iff.mpr
      (sec11_comm_z_of_isElemAbelianMod hz2 hz1 hzU hU ha)
  · rw [Subgroup.mem_normalizer_iff]
    intro x
    refine ⟨fun hx => key a ha x hx, fun hx => ?_⟩
    have := key a⁻¹ (U.inv_mem ha) _ hx
    simpa [mul_assoc] using this

theorem sec11_fusion_final {t z m u u' v v' : G} (hz2 : z * z = 1) (hzm : m⁻¹ * z * m = z)
    (hu : u = m⁻¹ * v * m) (hu' : u' = m⁻¹ * v' * m) (hv : v = t ∨ v = t * z)
    (hv' : v' = t ∨ v' = t * z) : u' = u ∨ u' = u * z := by
  have hzm' : z * m = m * z := by
    calc z * m = m * (m⁻¹ * z * m) := by group
      _ = m * z := by rw [hzm]
  rw [hu, hu']
  rcases hv with hv | hv <;> rcases hv' with hv' | hv' <;> rw [hv, hv']
  · left; rfl
  · right
    calc m⁻¹ * (t * z) * m = (m⁻¹ * t * m) * (m⁻¹ * z * m) := by group
      _ = (m⁻¹ * t * m) * z := by rw [hzm]
  · right
    calc m⁻¹ * t * m = m⁻¹ * t * m * (z * z) := by rw [hz2, mul_one]
      _ = m⁻¹ * t * (m * z) * z := by group
      _ = m⁻¹ * t * (z * m) * z := by rw [hzm']
      _ = m⁻¹ * (t * z) * m * z := by group
  · left; rfl

theorem sec11_fusion [Finite G] (hp : Asc82Pre11) (h116 : Asc82Lemma116) {t : G}
    {L S : Subgroup G} {z : G} {K1 K2 T R : Subgroup G}
    (hctx : Sec11Ctx G t L S z K1 K2 T R)
    (hLB : ∀ V : Subgroup G, V ≤ T → z ∈ V → IsElemAbelianMod z V →
      Nat.card ↥(secCTQ K1 K2 T ⊔ secQ K1 K2) ≤ Nat.card ↥V →
        V ≤ secCTQ K1 K2 T ⊔ secQ K1 K2)
    (hCW : ∀ w ∈ secCTQ K1 K2 T ⊔ secQ K1 K2, w * t = t * w → w ∈ secW t K1 K2)
    {U : Subgroup G} (hzU : z ∈ U) (hU : IsElemAbelianMod z U)
    (hcard : Nat.card ↥(secCTQ K1 K2 T ⊔ secQ K1 K2) ≤ Nat.card ↥U)
    {h h' : G} (hh : h ∈ centralizer ({z} : Set G)) (hh' : h' ∈ centralizer ({z} : Set G))
    (hu : h⁻¹ * t * h ∈ U) (hu' : h'⁻¹ * t * h' ∈ U)
    (hcomm : (h⁻¹ * t * h) * (h'⁻¹ * t * h') = (h'⁻¹ * t * h') * (h⁻¹ * t * h)) :
    h'⁻¹ * t * h' = h⁻¹ * t * h ∨ h'⁻¹ * t * h' = (h⁻¹ * t * h) * z := by
  obtain ⟨ht2, hz2, htz, ht1, hz1⟩ := sec11_invols hctx.toSec10Ctx
  have hzL : z ∈ L := (hctx.pocket1.2.1 hctx.pocket1.1).1
  have htne : t ≠ z := by
    intro h0
    exact (hp.basic G t L S z hctx.toSec10Z).2.2.1 (by rw [h0]; exact hzL)
  have hhz : h * z * h⁻¹ = z := by
    rw [Subgroup.mem_centralizer_singleton_iff.mp hh, mul_assoc, mul_inv_cancel, mul_one]
  have hconj : ∀ g y : G, (MulAut.conj g).toMonoidHom y = g * y * g⁻¹ := fun g y => rfl
  set U0 : Subgroup G := U.map (MulAut.conj h).toMonoidHom with hU0
  have htU0 : t ∈ U0 := ⟨h⁻¹ * t * h, hu, by rw [hconj]; group⟩
  have hzU0 : z ∈ U0 := ⟨z, hzU, by rw [hconj]; exact hhz⟩
  have hU0el : IsElemAbelianMod z U0 := sec11_isElemAbelianMod_map hhz hU
  have hU0H : U0 ≤ hatCent t z := sec11_le_hatCent hz2 hz1 hzU0 htU0 hU0el
  have hU0p : IsPGroup 2 U0 := sec11_isPGroup_of_isElemAbelianMod hz2 hU0el
  obtain ⟨P0, hP0, hUP0⟩ := exists_isSylow2Of_ge hU0p hU0H
  obtain ⟨a, haH, ha⟩ :=
    IsSylow2Of.exists_conj_mem (h116 G t L S z K1 K2 T R hctx) hP0
  have haz : a * z = z * a :=
    Subgroup.mem_centralizer_singleton_iff.mp (Subgroup.mem_inf.mp haH).1
  have hmz : (a⁻¹ * h) * z * (a⁻¹ * h)⁻¹ = z := by
    calc (a⁻¹ * h) * z * (a⁻¹ * h)⁻¹ = a⁻¹ * (h * z * h⁻¹) * a := by group
      _ = a⁻¹ * z * a := by rw [hhz]
      _ = z := by
        calc a⁻¹ * z * a = a⁻¹ * (z * a) := by group
          _ = a⁻¹ * (a * z) := by rw [haz]
          _ = z := by group
  set U1 : Subgroup G := U.map (MulAut.conj (a⁻¹ * h)).toMonoidHom with hU1
  have hU1T : U1 ≤ T := by
    rintro _ ⟨x, hx, rfl⟩
    have hx0 : h * x * h⁻¹ ∈ P0 := hUP0 ⟨x, hx, rfl⟩
    have hxT := (ha _).mp hx0
    rw [hconj]
    have e : a⁻¹ * h * x * (a⁻¹ * h)⁻¹ = a⁻¹ * (h * x * h⁻¹) * a := by group
    rw [e]
    exact hxT
  have hzU1 : z ∈ U1 := ⟨z, hzU, by rw [hconj]; exact hmz⟩
  have hU1el : IsElemAbelianMod z U1 := sec11_isElemAbelianMod_map hmz hU
  have hcardU1 : Nat.card ↥U1 = Nat.card ↥U :=
    Subgroup.card_map_of_injective (MulAut.conj (a⁻¹ * h)).injective
  have hU1W : U1 ≤ secCTQ K1 K2 T ⊔ secQ K1 K2 :=
    hLB U1 hU1T hzU1 hU1el (by rw [hcardU1]; exact hcard)
  have hv : (a⁻¹ * h) * (h⁻¹ * t * h) * (a⁻¹ * h)⁻¹ = a⁻¹ * t * a := by group
  have hvcases : (a⁻¹ * h) * (h⁻¹ * t * h) * (a⁻¹ * h)⁻¹ = t ∨
      (a⁻¹ * h) * (h⁻¹ * t * h) * (a⁻¹ * h)⁻¹ = t * z := by
    rw [hv]
    have := sec11_hatCent_conj ht2 hz2 htz ht1 htne (Subgroup.inv_mem _ haH)
    simpa only [inv_inv] using this
  have hv'U1 : (a⁻¹ * h) * (h'⁻¹ * t * h') * (a⁻¹ * h)⁻¹ ∈ U1 := ⟨h'⁻¹ * t * h', hu', rfl⟩
  have hv'W := hU1W hv'U1
  have hv'z : (a⁻¹ * h) * (h'⁻¹ * t * h') * (a⁻¹ * h)⁻¹ * z =
      z * ((a⁻¹ * h) * (h'⁻¹ * t * h') * (a⁻¹ * h)⁻¹) :=
    sec11_comm_z_of_isElemAbelianMod hz2 hz1 hzU1 hU1el hv'U1
  have hvv' : (a⁻¹ * h) * (h⁻¹ * t * h) * (a⁻¹ * h)⁻¹ *
        ((a⁻¹ * h) * (h'⁻¹ * t * h') * (a⁻¹ * h)⁻¹) =
      (a⁻¹ * h) * (h'⁻¹ * t * h') * (a⁻¹ * h)⁻¹ *
        ((a⁻¹ * h) * (h⁻¹ * t * h) * (a⁻¹ * h)⁻¹) := by
    calc (a⁻¹ * h) * (h⁻¹ * t * h) * (a⁻¹ * h)⁻¹ *
          ((a⁻¹ * h) * (h'⁻¹ * t * h') * (a⁻¹ * h)⁻¹)
        = (a⁻¹ * h) * ((h⁻¹ * t * h) * (h'⁻¹ * t * h')) * (a⁻¹ * h)⁻¹ := by group
      _ = (a⁻¹ * h) * ((h'⁻¹ * t * h') * (h⁻¹ * t * h)) * (a⁻¹ * h)⁻¹ := by rw [hcomm]
      _ = _ := by group
  generalize hv'def : (a⁻¹ * h) * (h'⁻¹ * t * h') * (a⁻¹ * h)⁻¹ = v' at hv'W hv'z hvv'
  have hv't : v' * t = t * v' := by
    rcases hvcases with hvt | hvt
    · rw [hvt] at hvv'
      exact hvv'.symm
    · rw [hvt] at hvv'
      have h2 : t * v' * z = v' * t * z := by
        calc t * v' * z = t * (v' * z) := by group
          _ = t * (z * v') := by rw [hv'z]
          _ = t * z * v' := by group
          _ = v' * (t * z) := hvv'
          _ = v' * t * z := by group
      exact (mul_right_cancel h2).symm
  have hv'sec : v' ∈ secW t K1 K2 := hCW v' hv'W hv't
  have hmC : (a⁻¹ * h) * z = z * (a⁻¹ * h) := by
    have := hmz
    calc (a⁻¹ * h) * z = ((a⁻¹ * h) * z * (a⁻¹ * h)⁻¹) * (a⁻¹ * h) := by group
      _ = z * (a⁻¹ * h) := by rw [hmz]
  have hn : h' * (a⁻¹ * h)⁻¹ ∈ centralizer ({z} : Set G) := by
    refine Subgroup.mem_centralizer_singleton_iff.mpr ?_
    have h1 : h' * z = z * h' := Subgroup.mem_centralizer_singleton_iff.mp hh'
    calc h' * (a⁻¹ * h)⁻¹ * z = h' * ((a⁻¹ * h)⁻¹ * z * (a⁻¹ * h)) * (a⁻¹ * h)⁻¹ := by group
      _ = h' * z * (a⁻¹ * h)⁻¹ := by
          congr 2
          calc (a⁻¹ * h)⁻¹ * z * (a⁻¹ * h) = (a⁻¹ * h)⁻¹ * (z * (a⁻¹ * h)) := by group
            _ = (a⁻¹ * h)⁻¹ * ((a⁻¹ * h) * z) := by rw [hmC]
            _ = z := by group
      _ = z * h' * (a⁻¹ * h)⁻¹ := by rw [h1]
      _ = z * (h' * (a⁻¹ * h)⁻¹) := by group
  have hconj' : (h' * (a⁻¹ * h)⁻¹)⁻¹ * t * (h' * (a⁻¹ * h)⁻¹) = v' := by
    rw [← hv'def]; group
  have hsc := sec11_strClosed_secW hp hctx.toSec10Ctx hctx.hyp
  have hv'cls : v' = t ∨ v' = t * z := by
    have := hsc (h' * (a⁻¹ * h)⁻¹) hn (by rw [hconj']; exact Subgroup.mem_sup_left hv'sec)
    rwa [hconj'] at this
  have hzm : (a⁻¹ * h)⁻¹ * z * (a⁻¹ * h) = z := by
    calc (a⁻¹ * h)⁻¹ * z * (a⁻¹ * h) = (a⁻¹ * h)⁻¹ * (z * (a⁻¹ * h)) := by group
      _ = (a⁻¹ * h)⁻¹ * ((a⁻¹ * h) * z) := by rw [hmC]
      _ = z := by group
  refine sec11_fusion_final (t := t) (z := z) (m := a⁻¹ * h) hz2 hzm ?_ ?_ hvcases hv'cls
  · group
  · rw [← hv'def]; group

end CFSG.OddStandard.SmallF3.Omega
