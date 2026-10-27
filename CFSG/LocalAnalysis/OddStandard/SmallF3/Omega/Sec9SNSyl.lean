module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec9SNBase
import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec6L68a
import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec10Sylow
import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec3PocketLemmas
import CFSG.GroupTheory.ElementaryAbelianTransport

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {G : Type} [Group G] [Finite G] {t t₀ z g : G} {L S B : Subgroup G}

theorem sec9n_h68 (h68 : Asc82Lemma68) (hB : Asc82Sec8B) (hctx : Sec9Choice G t L S z g B t₀) :
    IsSylow2Of (zpowers t) (centralizer (L : Set G)) ∧
      ConjTwoTransOn (normalizer ((zpowers t ⊔ B : Subgroup G) : Set G)) (cosetSet t B) := by
  have hS : Sec3SettingLB G t L := hctx.toSec3SettingLB
  have hzB : z ∈ B := (hB G t L S z g B hctx.toSec8Base).1
  have hz2 : orderOf z = 2 := hctx.pocket.1
  have hz1 : z ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hz2
    omega
  have hne : g⁻¹ * t * g ≠ t := by
    intro h
    have htz : t * z = t := by rw [← hctx.tz, h]
    exact hz1 (mul_left_cancel (a := t) (by rw [htz, mul_one]))
  have hmem : g⁻¹ * t * g ∈ cosetSet t B := by
    rw [hctx.tz]
    exact ⟨z, hzB, rfl⟩
  have hBg : B ≤ CFSG.conjugate L g := fun x hx => (hctx.choice.le hx).2
  exact h68 G t L hS hctx.omega6m B hctx.B_e16 (fun x hx => (hctx.B_le hx).1) g hne hmem hBg

private theorem sec9n_A8_le_A : (zpowers t ⊔ B : Subgroup G) ≤ Asub9 t t₀ B := by
  rw [Asub9]
  exact sup_le (le_sup_left.trans le_sup_left) le_sup_right

private theorem sec9n_t_mem_A : t ∈ Asub9 t t₀ B :=
  sec9n_A8_le_A (Subgroup.mem_sup_left (Subgroup.mem_zpowers t))

private theorem sec9n_t0_mem_A : t₀ ∈ Asub9 t t₀ B := by
  rw [Asub9]
  exact Subgroup.mem_sup_left (Subgroup.mem_sup_right (Subgroup.mem_zpowers t₀))

private theorem sec9n_mem_normalizer_centralizer {H : Subgroup G} {s : G}
    (hs : s ∈ normalizer (H : Set G)) : s ∈ normalizer (centralizer (H : Set G)) := by
  rw [Subgroup.mem_normalizer_iff] at hs ⊢
  intro c
  rw [Subgroup.mem_centralizer_iff, Subgroup.mem_centralizer_iff]
  constructor
  · intro hc x hx
    have hx' : s⁻¹ * x * s ∈ H := (hs (s⁻¹ * x * s)).mpr (by
      rw [show s * (s⁻¹ * x * s) * s⁻¹ = x by group]; exact hx)
    calc x * (s * c * s⁻¹) = s * ((s⁻¹ * x * s) * c) * s⁻¹ := by group
      _ = s * (c * (s⁻¹ * x * s)) * s⁻¹ := by rw [hc (s⁻¹ * x * s) hx']
      _ = (s * c * s⁻¹) * x := by group
  · intro hc x hx
    have hx' : s * x * s⁻¹ ∈ H := (hs x).mp hx
    have h := hc (s * x * s⁻¹) hx'
    calc x * c = s⁻¹ * ((s * x * s⁻¹) * (s * c * s⁻¹)) * s := by group
      _ = s⁻¹ * ((s * c * s⁻¹) * (s * x * s⁻¹)) * s := by rw [h]
      _ = c * x := by group

private theorem sec9n_commutator_mem_centralizer {y c t : G} {L : Subgroup G}
    (hyN : y ∈ normalizer (L : Set G)) (htN : t ∈ normalizer (L : Set G))
    (hyt : y * t = t * y) (hc : c ∈ centralizer (L : Set G)) :
    (y * c) * t * (y * c)⁻¹ * t⁻¹ ∈ centralizer (L : Set G) := by
  have hu : c * t * c⁻¹ * t⁻¹ ∈ centralizer (L : Set G) := by
    have htNC : t ∈ normalizer (centralizer (L : Set G) : Set G) :=
      sec9n_mem_normalizer_centralizer htN
    have hct : t * c⁻¹ * t⁻¹ ∈ centralizer (L : Set G) :=
      (Subgroup.mem_normalizer_iff.mp htNC c⁻¹).mp (inv_mem hc)
    have he : c * t * c⁻¹ * t⁻¹ = c * (t * c⁻¹ * t⁻¹) := by group
    rw [he]
    exact mul_mem hc hct
  have hyNC : y ∈ normalizer (centralizer (L : Set G) : Set G) :=
    sec9n_mem_normalizer_centralizer hyN
  have hconj : y * (c * t * c⁻¹ * t⁻¹) * y⁻¹ ∈ centralizer (L : Set G) :=
    (Subgroup.mem_normalizer_iff.mp hyNC (c * t * c⁻¹ * t⁻¹)).mp hu
  have heq : (y * c) * t * (y * c)⁻¹ * t⁻¹ =
      y * (c * t * c⁻¹ * t⁻¹) * y⁻¹ := by
    rw [← commutatorElement_def (y * c) t, ← commutatorElement_def c t,
      commutatorElement_mul_left_eq_conj_mul y c t,
      (show Commute y t from hyt).commutator_eq, mul_one]
  rw [heq]
  exact hconj

theorem sec9n_cent_le_normalizer (h36 : Asc82Lemma36) {t : G} {L : Subgroup G}
    (hS : Sec3SettingLB G t L) {A8 : Subgroup G} (ht : t ∈ A8) :
    centralizer (A8 : Set G) ≤ normalizer (L : Set G) := by
  intro c hc
  have hct : c ∈ centralizer ({t} : Set G) :=
    Subgroup.mem_centralizer_singleton_iff.mpr
      ((Subgroup.mem_centralizer_iff.mp hc t ht).symm)
  exact sec9n_mem_normalizer_of_conjugate_eq (conjugate_eq_self_of_lemma36 h36 hS c hct)

theorem sec9n_sylow_of_le {P K H : Subgroup G} (hP : IsSylow2Of P H) (hPK : P ≤ K)
    (hKH : K ≤ H) : IsSylow2Of P K := by
  refine ⟨hPK, hP.2.1, fun h2 => hP.2.2 ?_⟩
  rw [← Subgroup.relIndex_mul_relIndex P K H hPK hKH]
  exact dvd_mul_of_dvd_left h2 _

theorem sec9n_sylow_cent8 (h36 : Asc82Lemma36) (h68 : Asc82Lemma68) (hB : Asc82Sec8B)
    (hT : Asc82Tab9M) (hctx : Sec9Choice G t L S z g B t₀) :
    IsSylow2Of (Asub9 t t₀ B) (centralizer ((zpowers t ⊔ B : Subgroup G) : Set G)) := by
  have hS : Sec3SettingLB G t L := hctx.toSec3SettingLB
  have hLM : IsOm6M L := ⟨hS.component.isQuasisimple, hctx.omega6m⟩
  have hAel : CFSG.Open.IsElemAbelian 2 (Asub9 t t₀ B) := sec9n_A_elem hctx.toSec9Ctx
  have hA2 : IsPGroup 2 (Asub9 t t₀ B) := hAel.isPGroup
  have hA8C : Asub9 t t₀ B ≤ centralizer ((zpowers t ⊔ B : Subgroup G) : Set G) := by
    have hAC : Asub9 t t₀ B ≤ centralizer (Asub9 t t₀ B : Set G) := by
      haveI : IsMulCommutative (Asub9 t t₀ B) := hAel.1
      intro a ha
      exact Subgroup.mem_centralizer_iff.mpr fun a' ha' => setLike_mul_comm ha' ha
    exact hAC.trans (Subgroup.centralizer_le sec9n_A8_le_A)
  obtain ⟨P, hPsyl, hAP⟩ :=
    sec68_exists_sylow_ge (H := centralizer ((zpowers t ⊔ B : Subgroup G) : Set G)) hA2 hA8C
  have hCL : centralizer ((zpowers t ⊔ B : Subgroup G) : Set G) ≤ normalizer (L : Set G) :=
    sec9n_cent_le_normalizer h36 hS (Subgroup.mem_sup_left (Subgroup.mem_zpowers t))
  have hT68 : IsSylow2Of (zpowers t) (centralizer (L : Set G)) := (sec9n_h68 h68 hB hctx).1
  have hPA : P ≤ Asub9 t t₀ B := by
    intro x hxP
    have hxC : x ∈ centralizer ((zpowers t ⊔ B : Subgroup G) : Set G) := hPsyl.1 hxP
    have hxN : x ∈ normalizer (L : Set G) := hCL hxC
    have hxB : ∀ b ∈ B, x * b = b * x := fun b hb =>
      (Subgroup.mem_centralizer_iff.mp hxC b (Subgroup.mem_sup_right hb)).symm
    have hB2 : IsPGroup 2 B := hctx.B_e16.1.isPGroup
    have hBL : B ≤ L := fun b hb => (hctx.B_le hb).1
    obtain ⟨P0, hP0, hBP0⟩ := sec68_exists_sylow_ge (H := L) hB2 hBL
    obtain ⟨b, hbB, c, hcC, hbc⟩ :=
      hT.cent_B_i3 G L hLM P0 hP0 B hBP0 hctx.B_e16 t₀
        (sec9n_t0_mem_normalizer hctx.toSec9Ctx) hctx.t0_B
        (hT.i3_outer G L hLM t₀ (sec9n_t0_mem_normalizer hctx.toSec9Ctx) hctx.t0_type)
        x hxN hxB
    have hbA : b ∈ Asub9 t t₀ B := Subgroup.mem_sup_right hbB
    have hbP : b ∈ P := hAP hbA
    have hQ2 : IsPGroup 2 ↥(P ⊓ centralizer (L : Set G)) := hPsyl.2.1.to_le inf_le_left
    have htP : t ∈ P := hAP sec9n_t_mem_A
    have htC : t ∈ centralizer (L : Set G) := sec9n_t_mem_cent hctx.toSec9Ctx
    have hle : zpowers t ≤ P ⊓ centralizer (L : Set G) :=
      le_inf (zpowers_le.mpr htP) (zpowers_le.mpr htC)
    have hQeq : P ⊓ centralizer (L : Set G) = zpowers t :=
      hT68.eq_of_le inf_le_right hQ2 hle
    have hcA : c ∈ Asub9 t t₀ B := by
      rcases hbc with hbc | hbc
      · have hcP : c ∈ P := by
          have : c = b⁻¹ * x := by rw [hbc]; group
          rw [this]
          exact P.mul_mem (P.inv_mem hbP) hxP
        have hcQ : c ∈ P ⊓ centralizer (L : Set G) := ⟨hcP, hcC⟩
        rw [hQeq] at hcQ
        exact sec9n_A8_le_A (Subgroup.mem_sup_left hcQ)
      · have hbt0P : b * t₀ ∈ P := P.mul_mem hbP (hAP sec9n_t0_mem_A)
        have hcP : c ∈ P := by
          have : c = (b * t₀)⁻¹ * x := by rw [hbc]; group
          rw [this]
          exact P.mul_mem (P.inv_mem hbt0P) hxP
        have hcQ : c ∈ P ⊓ centralizer (L : Set G) := ⟨hcP, hcC⟩
        rw [hQeq] at hcQ
        exact sec9n_A8_le_A (Subgroup.mem_sup_left hcQ)
    rcases hbc with hbc | hbc
    · rw [hbc]
      exact (Asub9 t t₀ B).mul_mem hbA hcA
    · rw [hbc]
      exact (Asub9 t t₀ B).mul_mem ((Asub9 t t₀ B).mul_mem hbA sec9n_t0_mem_A) hcA
  exact le_antisymm hPA hAP ▸ hPsyl

theorem sec9n_sylow_centA (h36 : Asc82Lemma36) (h68 : Asc82Lemma68) (hB : Asc82Sec8B)
    (hT : Asc82Tab9M) (hctx : Sec9Choice G t L S z g B t₀) :
    IsSylow2Of (Asub9 t t₀ B) (centralizer (Asub9 t t₀ B : Set G)) := by
  have hAel : CFSG.Open.IsElemAbelian 2 (Asub9 t t₀ B) := sec9n_A_elem hctx.toSec9Ctx
  have hAC : Asub9 t t₀ B ≤ centralizer (Asub9 t t₀ B : Set G) := by
    haveI : IsMulCommutative (Asub9 t t₀ B) := hAel.1
    intro a ha
    exact Subgroup.mem_centralizer_iff.mpr fun a' ha' => setLike_mul_comm ha' ha
  exact sec9n_sylow_of_le (sec9n_sylow_cent8 h36 h68 hB hT hctx) hAC
    (Subgroup.centralizer_le sec9n_A8_le_A)

theorem sec9n_comm_t0 (h36 : Asc82Lemma36) (hT : Asc82Tab9M)
    (hctx : Sec9Ctx G t L S z g B t₀) {x : G}
    (hx : x ∈ centralizer ((zpowers t ⊔ B : Subgroup G) : Set G))
    (hxt : x * t₀ * x⁻¹ * t₀⁻¹ ∈ B) : x * t₀ = t₀ * x := by
  have hS : Sec3SettingLB G t L := hctx.toSec3SettingLB
  have hLM : IsOm6M L := ⟨hS.component.isQuasisimple, hctx.omega6m⟩
  have ht0N : t₀ ∈ normalizer (L : Set G) := sec9n_t0_mem_normalizer hctx
  have hxN : x ∈ normalizer (L : Set G) :=
    sec9n_cent_le_normalizer h36 hS (Subgroup.mem_sup_left (Subgroup.mem_zpowers t)) hx
  have hxB : ∀ b ∈ B, x * b = b * x := fun b hb =>
    (Subgroup.mem_centralizer_iff.mp hx b (Subgroup.mem_sup_right hb)).symm
  have hB2 : IsPGroup 2 B := hctx.B_e16.1.isPGroup
  have hBL : B ≤ L := fun b hb => (hctx.B_le hb).1
  obtain ⟨P0, hP0, hBP0⟩ := sec68_exists_sylow_ge (H := L) hB2 hBL
  obtain ⟨b, hbB, c, hcC, hbc⟩ :=
    hT.cent_B_i3 G L hLM P0 hP0 B hBP0 hctx.B_e16 t₀ ht0N hctx.t0_B
      (hT.i3_outer G L hLM t₀ ht0N hctx.t0_type) x hxN hxB
  have hbN : b ∈ normalizer (L : Set G) := Subgroup.le_normalizer (hctx.B_le hbB).1
  have hwC : x * t₀ * x⁻¹ * t₀⁻¹ ∈ centralizer (L : Set G) := by
    rcases hbc with hbc | hbc
    · rw [hbc]
      exact sec9n_commutator_mem_centralizer hbN ht0N ((hctx.t0_B b hbB).symm) hcC
    · rw [hbc]
      exact sec9n_commutator_mem_centralizer
        ((Subgroup.normalizer (L : Set G)).mul_mem hbN ht0N) ht0N
        (by
          calc (b * t₀) * t₀ = b * (t₀ * t₀) := by rw [mul_assoc]
            _ = b := by rw [sec9n_t0_sq hctx, mul_one]
            _ = (t₀ * b) * t₀ := by
              rw [hctx.t0_B b hbB, mul_assoc, sec9n_t0_sq hctx, mul_one]
            _ = t₀ * (b * t₀) := by rw [mul_assoc])
        hcC
  have hw1 : x * t₀ * x⁻¹ * t₀⁻¹ = 1 := sec9n_B_inf_cent hctx _ hxt hwC
  have hx' : x * t₀ * x⁻¹ = t₀ := mul_inv_eq_one.mp hw1
  calc x * t₀ = (x * t₀ * x⁻¹) * x := by group
    _ = t₀ * x := by rw [hx']

theorem sec9n_cent_eq (h36 : Asc82Lemma36) (hT : Asc82Tab9M)
    (hctx : Sec9Ctx G t L S z g B t₀) :
    centMod (Asub9 t t₀ B) B ⊓ centralizer (Asub9 t t₀ B : Set G) =
      centMod (Asub9 t t₀ B) B ⊓ centralizer ((zpowers t ⊔ B : Subgroup G) : Set G) := by
  apply le_antisymm
  · exact le_inf inf_le_left (inf_le_right.trans (Subgroup.centralizer_le sec9n_A8_le_A))
  · intro x hx
    obtain ⟨hxM, hxC8⟩ := hx
    refine ⟨hxM, ?_⟩
    have htA8 : t ∈ (zpowers t ⊔ B : Subgroup G) :=
      Subgroup.mem_sup_left (Subgroup.mem_zpowers t)
    have hct : Commute x t :=
      (Subgroup.mem_centralizer_iff.mp hxC8 t htA8).symm
    have hcb : ∀ b ∈ B, Commute x b := fun b hb =>
      (Subgroup.mem_centralizer_iff.mp hxC8 b (Subgroup.mem_sup_right hb)).symm
    have ht0B' : x * t₀ * x⁻¹ * t₀⁻¹ ∈ B := hxM.2 t₀ sec9n_t0_mem_A
    have hct0 : Commute x t₀ := sec9n_comm_t0 h36 hT hctx hxC8 ht0B'
    exact Subgroup.mem_centralizer_iff.mpr fun a ha => by
      obtain ⟨b, hbB, h | h | h | h⟩ := sec9n_mem_A hctx ha
      · rw [h]; exact (hcb b hbB).symm.eq
      · rw [h]; exact (hct.mul_right (hcb b hbB)).symm.eq
      · rw [h]; exact (hct0.mul_right (hcb b hbB)).symm.eq
      · rw [h]; exact (hct.mul_right (hct0.mul_right (hcb b hbB))).symm.eq

end CFSG.OddStandard.SmallF3.Omega
