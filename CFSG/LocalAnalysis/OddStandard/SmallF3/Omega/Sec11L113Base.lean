module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec11L117Basic
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec11T
public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec11L112Def

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {G : Type} [Group G] {t : G} {L S : Subgroup G} {z : G} {K1 K2 T : Subgroup G}
  {Alt : Subgroup (Equiv.Perm (Fin 6))} {φ : (Fin 6 → ZMod 2) → G}

theorem sec113_z_eq (hm : Sec11Model t L S z K1 K2 T Alt φ) :
    z = φ (Pi.single (0 : Fin 6) (1 : ZMod 2) + Pi.single (1 : Fin 6) (1 : ZMod 2)) := by
  have h1 : z = t⁻¹ * (t * z) := by group
  rw [h1, hm.tz_eq, hm.t_eq, hm.perm.inv_eq, hm.perm.mul]

theorem sec113_A_le_S [Finite G] (hp : Asc82Pre11) (hctx : Sec10Ctx G t L S z K1 K2) :
    secA t S L ≤ S :=
  sup_le (secB_le_S S L) (Subgroup.zpowers_le.mpr (sec11_t_mem_S hp hctx))

theorem sec113_A_le_T [Finite G] (hp : Asc82Pre11) {R : Subgroup G}
    (hctx : Sec11Ctx G t L S z K1 K2 T R) : secA t S L ≤ T :=
  (sec113_A_le_S hp hctx.toSec10Ctx).trans hctx.S_le

theorem sec113_Q_le_T [Finite G] (hp : Asc82Pre11) {R : Subgroup G}
    (hctx : Sec11Ctx G t L S z K1 K2 T R) : secQ K1 K2 ≤ T :=
  (sec11_Q_facts hp hctx.toSec10Ctx).2.1.trans hctx.S_le

theorem sec113_T_le_M [Finite G] {R : Subgroup G} (hctx : Sec11Ctx G t L S z K1 K2 T R) :
    T ≤ secM t S L :=
  hctx.sylowT.1

theorem sec113_rho_of_mem_A (hm : Sec11Model t L S z K1 K2 T Alt φ) {a : G}
    (ha : a ∈ secA t S L) : hm.perm.rho a = 1 := by
  have haM : a ∈ secM t S L := Subgroup.le_normalizer ha
  rw [hm.perm.rho_eq_one_iff haM]
  intro a' ha'
  obtain ⟨v, rfl⟩ := hm.perm.surj a ha
  obtain ⟨w, rfl⟩ := hm.perm.surj a' ha'
  rw [hm.perm.comm v w]
  group

theorem sec113_conj_single (hm : Sec11Model t L S z K1 K2 T Alt φ) {x : G}
    (hx : x ∈ secM t S L) (k : Fin 6) :
    x * φ (Pi.single k 1) * x⁻¹ = φ (Pi.single (hm.perm.rho x k) 1) :=
  hm.perm.conj_single hx k

theorem sec113_conj_z [Finite G] (hp : Asc82Pre11) {R : Subgroup G}
    (hctx : Sec11Ctx G t L S z K1 K2 T R) {x : G} (hx : x ∈ T) : x * z * x⁻¹ = z := by
  have hTQ := (asc82Step111T_of hp G t L S z K1 K2 T hctx.toSec10Ctx hctx.hyp hctx.sylowT
    hctx.S_le).2.2.2
  have h := sec11_normalizer_Q_le_centralizer_z hp hctx.toSec10Ctx (hTQ hx)
  have h' := Subgroup.mem_centralizer_singleton_iff.mp h
  calc x * z * x⁻¹ = (x * z) * x⁻¹ := rfl
    _ = (z * x) * x⁻¹ := by rw [h']
    _ = z := by group

end CFSG.OddStandard.SmallF3.Omega
