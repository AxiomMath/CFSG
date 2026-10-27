module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.Splitting
public import Certificates.Certificate14951
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.TC

public section

namespace CFSG.QuasithinUnique.A5

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.QuasithinUnique.DoubleA3
  CFSG.QuasithinUnique.A5.Delta5 CFSG.QuasithinUnique.A5.Action CFSG.QuasithinUnique.A5.Split

namespace StdCfg

variable {G : Type} [Group G] [Finite G] {T M H S L : Subgroup G}

theorem Q_eq_U (C : StdCfg T M H S L) (hTC : blockTC T S L = ⊥) : pCoreOf 2 H = blockU L := by
  rw [C.F.Q_eq, hTC, bot_sup_eq]

@[expose] noncomputable def iotaH (C : StdCfg T M H S L) : Multiplicative (evenWeight 5) →* ↥H :=
  (Subgroup.inclusion C.blockU_le_H).comp C.D.β.symm.toMonoidHom

theorem deltaExt (C : StdCfg T M H S L) (hTC : blockTC T S L = ⊥) :
    DeltaExt C.iotaH C.D.π where
  inj := by
    intro x y h
    have h1 := Subgroup.inclusion_injective C.blockU_le_H h
    exact C.D.β.symm.injective h1
  ι_ker := by
    intro w
    apply (C.hker _).mpr
    have h : ((C.iotaH (Multiplicative.ofAdd w) : ↥H) : G) ∈ blockU L := (C.D.β.symm _).2
    rw [← C.Q_eq_U hTC] at h
    exact h
  ker := by
    intro x hx
    have hxU : (x : G) ∈ blockU L := by
      rw [← C.Q_eq_U hTC]
      exact (C.hker x).mp hx
    refine ⟨Multiplicative.toAdd (C.D.β ⟨x, hxU⟩), ?_⟩
    apply Subtype.ext
    show ((C.D.β.symm (Multiplicative.ofAdd (Multiplicative.toAdd (C.D.β ⟨x, hxU⟩))) :
      ↥(blockU L)) : G) = x
    simp
  conj := by
    intro h w
    have hmem := H_normalizes_U C.hcs C.hj h h.2 ((C.D.β.symm (Multiplicative.ofAdd w) :
      ↥(blockU L)) : G) (C.D.β.symm (Multiplicative.ofAdd w)).2
    have key := C.D.hβ h (C.D.β.symm (Multiplicative.ofAdd w)) ⟨_, hmem⟩ rfl
    have heq : (⟨_, hmem⟩ : ↥(blockU L)) =
        C.D.β.symm (Multiplicative.ofAdd (vact (C.D.π h) w)) := by
      apply C.D.β.injective
      rw [MulEquiv.apply_symm_apply]
      apply Multiplicative.toAdd.injective
      simpa using key
    apply Subtype.ext
    exact congrArg (fun y : ↥(blockU L) => (y : G)) heq
  surj := C.hsurj

theorem Ux_sq (C : StdCfg T M H S L) {x u : G} (hu : u ∈ conjR (blockU L) x) : u * u = 1 := by
  have hu0 : x * u * x⁻¹ ∈ blockU L :=
    (mem_conjSubgroup_iff (A := blockU L) (g := x) (x := u)).mp hu
  have h2 : (x * u * x⁻¹) * (x * u * x⁻¹) = 1 := by
    rw [← pow_two]
    exact C1.blockU_sq (C56.isShort C.hcs) _ hu0
  calc u * u = x⁻¹ * ((x * u * x⁻¹) * (x * u * x⁻¹)) * x := by group
    _ = 1 := by rw [h2]; group

theorem Ux_comm (C : StdCfg T M H S L) {x u u' : G} (hu : u ∈ conjR (blockU L) x)
    (hu' : u' ∈ conjR (blockU L) x) : u * u' = u' * u := by
  have hu0 : x * u * x⁻¹ ∈ blockU L :=
    (mem_conjSubgroup_iff (A := blockU L) (g := x) (x := u)).mp hu
  have hu0' : x * u' * x⁻¹ ∈ blockU L :=
    (mem_conjSubgroup_iff (A := blockU L) (g := x) (x := u')).mp hu'
  have hUQ : blockU L ≤ blockQ L ⊓ Subgroup.centralizer (blockQ L : Set G) :=
    (C56.isShort C.hcs).2.2.1.1
  have hc : (x * u' * x⁻¹) * (x * u * x⁻¹) = (x * u * x⁻¹) * (x * u' * x⁻¹) :=
    Subgroup.mem_centralizer_iff.mp (hUQ hu0).2 _ (hUQ hu0').1
  calc u * u' = x⁻¹ * ((x * u * x⁻¹) * (x * u' * x⁻¹)) * x := by group
    _ = x⁻¹ * ((x * u' * x⁻¹) * (x * u * x⁻¹)) * x := by rw [hc]
    _ = u' * u := by group

theorem exists_Ux_pi (C : StdCfg T M H S L) {x : G} (hxT : x ∈ T) (hxS : x ∉ S)
    {σ : Equiv.Perm (Fin 5)} (hσ : σ ∈ Estd) :
    ∃ (u : G) (hu : u ∈ H), u ∈ conjR (blockU L) x ∧ C.D.π ⟨u, hu⟩ = σ := by
  obtain ⟨r, hr, hπr⟩ := C.hRE' _ hσ
  have hrR := hr
  rw [C.F.R_eq x hxT hxS, ← sup_assoc, ← C.F.Q_eq] at hrR
  have hUxR : conjR (blockU L) x ≤ baum S := by
    rw [C.F.R_eq x hxT hxS]
    exact le_sup_of_le_right le_sup_right
  have hUxH : conjR (blockU L) x ≤ H := hUxR.trans (baum_le_H C.hcs)
  have hnorm : conjR (blockU L) x ≤ Subgroup.normalizer (pCoreOf 2 H : Set G) :=
    hUxH.trans (CFSG.RankThreeCoreUniqueness.Helpers.localGroup_le_normalizer_pCoreOf 2 H)
  have hrR' : r ∈ conjR (blockU L) x ⊔ pCoreOf 2 H := by rwa [sup_comm] at hrR
  obtain ⟨a, ha, b, hb, hab⟩ := C5.mem_sup_of_le_normalizer (x := r) hnorm hrR'
  have haH : a ∈ H := hUxH ha
  have hbH : b ∈ H := CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_le 2 H hb
  refine ⟨a, haH, ha, ?_⟩
  have h1 : C.D.π ⟨b, hbH⟩ = 1 := (C.hker ⟨b, hbH⟩).mpr hb
  have h2 : (⟨r, baum_le_H C.hcs hr⟩ : ↥H) = ⟨a, haH⟩ * ⟨b, hbH⟩ := Subtype.ext hab
  rw [← hπr, h2, map_mul, h1, mul_one]

theorem exists_section_H (C : StdCfg T M H S L)
    (hTC : blockTC T S L = ⊥) :
    ∃ s : Equiv.Perm (Fin 5) →* ↥H, ∀ σ, C.D.π (s σ) = σ := by
  obtain ⟨x, hxT, hxS⟩ := C.exists_mem_T_sdiff
  have hsa : sa ∈ Estd := by
    show Equiv.swap (0 : Fin 5) 1 ∈ Eset
    exact Certificates.certificate14951.1
  have hsb : sb ∈ Estd := by
    show Equiv.swap (2 : Fin 5) 3 ∈ Eset
    exact Certificates.certificate14951.2
  obtain ⟨a, haH, haUx, hπa⟩ := C.exists_Ux_pi hxT hxS hsa
  obtain ⟨b, hbH, hbUx, hπb⟩ := C.exists_Ux_pi hxT hxS hsb
  obtain ⟨c₀, hc₀S, hπc⟩ := C.exists_mem_S_pi ((mem_Dstd _).mpr sc_mem)
  exact (C.deltaExt hTC).exists_section (a := ⟨a, haH⟩) (b := ⟨b, hbH⟩)
    (c₀ := ⟨c₀, C.hcs.sylow.le hc₀S⟩) hπa hπb hπc (Subtype.ext (C.Ux_sq haUx))
    (Subtype.ext (C.Ux_sq hbUx)) (Subtype.ext (C.Ux_comm haUx hbUx))

end StdCfg

end CFSG.QuasithinUnique.A5
