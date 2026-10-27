module

public import CFSG.LocalAnalysis.OddStandard.SwapPartner.AutProd
public import CFSG.LocalAnalysis.OddStandard.SwapPartner.WPrimeShapeTable
public import CFSG.LocalAnalysis.OddStandard.SwapPartner.AutProdLemmas

public section

namespace CFSG.OddStandard.AltStdSec.SwapPartner

open Subgroup Equiv Equiv.Perm

open scoped commutatorElement

namespace WreathCase

variable {X : Type*} [Group X] {t : X} {Sg V K : Subgroup X}

theorem card_le_altCentCard8_of_isSimpleGroup [Finite X] (H : WreathCase t Sg V K)
    (e : K ⧸ center K ≃* alternatingGroup (Fin 8)) {x : X} (hxN : x ∈ normalizer (K : Set X))
    {D : Subgroup X} (hD : D ≤ CFSG.layer X) (hDx : D ≤ centralizer ({x} : Set X))
    (hDs : IsSimpleGroup D) (hDn : ∃ a ∈ D, ∃ b ∈ D, a * b ≠ b * a) :
    Nat.card D ≤ altCentCard8 (theta H e ⟨x, hxN⟩).1 ∨
      Nat.card D ≤ altCentCard8 (theta H e ⟨x, hxN⟩).2 := by
  let N : Subgroup X := normalizer (K : Set X)
  let y : N := ⟨x, hxN⟩
  let hDN : D ≤ N := hD.trans H.layer_le_normalizer
  let f : D →* Perm (Fin 8) × Perm (Fin 8) := (theta H e).comp (Subgroup.inclusion hDN)
  let P : Subgroup N :=
    ((alternatingGroup (Fin 8)).prod (alternatingGroup (Fin 8))).comap (theta H e)
  have hK : K ≤ P.map (Subgroup.subtype N) := by
    intro k hk
    refine Subgroup.mem_map.mpr ⟨⟨k, Subgroup.le_normalizer hk⟩, ?_, rfl⟩
    rw [Subgroup.mem_comap, Subgroup.mem_prod]
    rw [show theta H e ⟨k, Subgroup.le_normalizer hk⟩ =
        (((e (QuotientGroup.mk ⟨k, hk⟩) : alternatingGroup (Fin 8)) : Perm (Fin 8)), 1)
      from theta_mk_K H e ⟨k, hk⟩]
    exact ⟨(e (QuotientGroup.mk ⟨k, hk⟩) : alternatingGroup (Fin 8)).2, Subgroup.one_mem _⟩
  have hKt : K.map (MulAut.conj t).toMonoidHom ≤ P.map (Subgroup.subtype N) := by
    intro z hz
    obtain ⟨k, hk, hkz⟩ := Subgroup.mem_map.mp hz
    change (MulAut.conj t) k = z at hkz
    rw [MulAut.conj_apply] at hkz
    subst hkz
    refine Subgroup.mem_map.mpr
      ⟨⟨t * k * t⁻¹, H.conj_t_mem_normalizer (Subgroup.le_normalizer hk)⟩, ?_, rfl⟩
    rw [Subgroup.mem_comap, Subgroup.mem_prod]
    rw [show theta H e ⟨t * k * t⁻¹, H.conj_t_mem_normalizer (Subgroup.le_normalizer hk)⟩ =
        (1, ((e (QuotientGroup.mk ⟨k, hk⟩) : alternatingGroup (Fin 8)) : Perm (Fin 8)))
      from theta_mk_map H e ⟨k, hk⟩]
    exact ⟨Subgroup.one_mem _, (e (QuotientGroup.mk ⟨k, hk⟩) : alternatingGroup (Fin 8)).2⟩
  have hsup : CFSG.layer X ≤ P.map (Subgroup.subtype N) := by
    rw [H.layer_eq]
    exact sup_le hK hKt
  have hDmap : D ≤ P.map (Subgroup.subtype N) := hD.trans hsup
  let σ := theta H e y
  let C₁ : Subgroup (Perm (Fin 8)) :=
    alternatingGroup (Fin 8) ⊓ centralizer ({σ.1} : Set (Perm (Fin 8)))
  let C₂ : Subgroup (Perm (Fin 8)) :=
    alternatingGroup (Fin 8) ⊓ centralizer ({σ.2} : Set (Perm (Fin 8)))
  have hfC : ∀ d : D, (f d).1 ∈ C₁ ∧ (f d).2 ∈ C₂ := by
    intro d
    obtain ⟨n, hnP, hn_eq⟩ := Subgroup.mem_map.mp (hDmap d.2)
    have hn_eq' : Subgroup.inclusion hDN d = n :=
      Subtype.ext (by rw [Subgroup.coe_inclusion]; exact hn_eq.symm)
    have hfd : f d = theta H e n := congrArg (theta H e) hn_eq'
    have halt : (theta H e n).1 ∈ alternatingGroup (Fin 8) ∧
        (theta H e n).2 ∈ alternatingGroup (Fin 8) :=
      Subgroup.mem_prod.mp (Subgroup.mem_comap.mp hnP)
    have hdx : d * x = x * d := mem_centralizer_singleton_iff.mp (hDx d.2)
    have hcommN : Subgroup.inclusion hDN d * y = y * Subgroup.inclusion hDN d := by
      apply Subtype.ext
      change (Subgroup.inclusion hDN d : X) * x = x * (Subgroup.inclusion hDN d : X)
      rw [Subgroup.coe_inclusion]
      exact hdx
    have hcomm : f d * theta H e y = theta H e y * f d := by
      change theta H e (Subgroup.inclusion hDN d) * theta H e y =
        theta H e y * theta H e (Subgroup.inclusion hDN d)
      have h := congrArg (theta H e) hcommN
      simpa only [map_mul] using h
    have hcent1 : (f d).1 ∈ centralizer ({σ.1} : Set (Perm (Fin 8))) :=
      mem_centralizer_singleton_iff.mpr (by simpa [σ] using congrArg Prod.fst hcomm)
    have hcent2 : (f d).2 ∈ centralizer ({σ.2} : Set (Perm (Fin 8))) :=
      mem_centralizer_singleton_iff.mpr (by simpa [σ] using congrArg Prod.snd hcomm)
    exact ⟨Subgroup.mem_inf.mpr ⟨by rw [hfd]; exact halt.1, hcent1⟩,
      Subgroup.mem_inf.mpr ⟨by rw [hfd]; exact halt.2, hcent2⟩⟩
  have hf : Function.Injective f := by
    rw [← f.ker_eq_bot_iff]
    rcases Subgroup.Normal.eq_bot_or_eq_top f.ker with hker | hker
    · exact hker
    · exfalso
      obtain ⟨a, ha, b, hb, hab⟩ := hDn
      have hmem : ∀ d : D, (d : X) ∈ centralizer (CFSG.layer X : Set X) := by
        intro d
        have hd : d ∈ f.ker := by rw [hker]; exact Subgroup.mem_top d
        have hd1 : f d = 1 := MonoidHom.mem_ker.mp hd
        have hkerθ : Subgroup.inclusion hDN d ∈ (theta H e).ker := by
          rw [MonoidHom.mem_ker]
          exact hd1
        have h := (mem_ker_theta_iff H e (Subgroup.inclusion hDN d)).mp hkerθ
        simpa only [Subgroup.coe_inclusion] using h
      have hacomm : b * a = a * b :=
        mem_centralizer_iff.mp (hmem ⟨a, ha⟩) b (hD hb)
      exact hab hacomm.symm
  have hC := card_le_of_injective_prod hDs f hf C₁ C₂ hfC
  rcases hC with hC | hC
  · left; simpa [altCentCard8, C₁, σ, y] using hC
  · right; simpa [altCentCard8, C₂, σ, y] using hC

end WreathCase

end CFSG.OddStandard.AltStdSec.SwapPartner
