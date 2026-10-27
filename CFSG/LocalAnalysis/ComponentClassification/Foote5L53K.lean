module

public import CFSG.LocalAnalysis.ComponentClassification.Foote5L53H
public import CFSG.LocalAnalysis.ComponentClassification.Foote5L53F
public import CFSG.LocalAnalysis.ComponentClassification.Foote5L53G
public import Certificates.Kernel.ThCent.Leaves

public noncomputable section

namespace CFSG.ComponentClassification.Foote5

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
  CFSG.ComponentClassification.UnbalancedCorr CFSG.ComponentClassification.FooteLit
  CFSG.ABGLocalTools

variable {G : Type} [Group G] {𝕊 : Type} [Group 𝕊]

@[expose] def actCentralizer (A : Subgroup G) (ε : A ⧸ pPrimeCore 2 A ≃* 𝕊) (α : MulAut 𝕊) :
    Subgroup G :=
  ((centralizer ({α} : Set (MulAut 𝕊))).comap (act A ε)).map (normalizer (A : Set G)).subtype

variable {A : Subgroup G} (ε : A ⧸ pPrimeCore 2 A ≃* 𝕊)

theorem mem_actCentralizer {α : MulAut 𝕊} {g : G} :
    g ∈ actCentralizer A ε α ↔
      g ∈ normalizer (A : Set G) ∧ actG A ε g * α = α * actG A ε g := by
  constructor
  · rintro ⟨g', hg', rfl⟩
    refine ⟨g'.2, ?_⟩
    rw [subtype_apply, actG_of_mem ε g'.2]
    exact mem_centralizer_singleton_iff.mp hg'
  · rintro ⟨hg, hc⟩
    refine ⟨⟨g, hg⟩, ?_, rfl⟩
    show act A ε ⟨g, hg⟩ ∈ centralizer ({α} : Set (MulAut 𝕊))
    rw [← actG_of_mem ε hg]
    exact mem_centralizer_singleton_iff.mpr hc

theorem nonempty_actImage_equiv {P : Subgroup G} (hP : P ≤ normalizer (A : Set G))
    (hPC : P ⊓ coreActionKernel A = ⊥) : Nonempty (actImage A ε P ≃* P) := by
  set N := normalizer (A : Set G)
  set φ : ↥(P.subgroupOf N) →* MulAut 𝕊 := (act A ε).comp (P.subgroupOf N).subtype with hφ
  have hrange : φ.range = actImage A ε P := by
    rw [hφ, MonoidHom.range_comp, range_subtype]
    rfl
  have hinj : Function.Injective φ := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro p hp
    have h1 : act A ε (p : N) = 1 := MonoidHom.mem_ker.mp hp
    have h2 : ((p : N) : G) ∈ coreActionKernel A := (act_eq_one_iff ε _).mp h1
    have h3 : ((p : N) : G) ∈ P ⊓ coreActionKernel A := mem_inf.mpr ⟨mem_subgroupOf.mp p.2, h2⟩
    rw [hPC, mem_bot] at h3
    exact mem_bot.mpr (Subtype.ext (Subtype.ext h3))
  exact ⟨((MulEquiv.subgroupCongr hrange).symm.trans (MonoidHom.ofInjective hinj).symm).trans
    (subgroupOfEquivOfLe hP)⟩

theorem nonempty_conjugate_equiv (H : Subgroup G) (g : G) : Nonempty (conjugate H g ≃* H) :=
  ⟨(H.equivMapOfInjective (MulAut.conj g⁻¹).toMonoidHom (MulAut.conj g⁻¹).injective).symm⟩

variable [Finite G]

namespace Sec5

variable {L₀ L Q S T : Subgroup G} {z t : G} (h : Sec5 G L₀ L Q S T z t)
  [Finite 𝕊] (ε : L ⧸ pPrimeCore 2 L ≃* 𝕊) {Lin : Subgroup (MulAut 𝕊)}
include h

omit [Finite 𝕊] in
theorem nonempty_Rbar_equiv : Nonempty ((h.Rbar ε : Subgroup 𝕊) ≃* ↥(S ⊓ L)) := by
  set K := (S ⊓ L).subgroupOf L with hK
  set φ : ↥K →* 𝕊 := (psi L ε).comp K.subtype with hφ
  have hrange : φ.range = (h.Rbar ε : Subgroup 𝕊) := by
    rw [hφ, MonoidHom.range_comp, range_subtype, coe_sylowImage]
  have hinj : Function.Injective φ := by
    intro a b hab
    have h1 := h.eq_of_psi_eq ε (mem_subgroupOf.mp a.2) (mem_subgroupOf.mp b.2) hab
    exact Subtype.ext (Subtype.ext h1)
  exact ⟨((MulEquiv.subgroupCongr hrange).symm.trans (MonoidHom.ofInjective hinj).symm).trans
    (subgroupOfEquivOfLe inf_le_right)⟩

theorem exists_conj_centralizer_R (hD : Foote5AutData 𝕊 Lin) {y : G} (hyS : y ∈ S)
    (hy2 : y * y = 1) (hylin : actG L ε y ∉ Lin) :
    ∃ u : G, IsConj y u ∧ (∀ r ∈ S ⊓ L, u * r = r * u) ∧ actG L ε u ∉ Lin := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hyN := h.S_le hyS
  have hsq : actG L ε y * actG L ε y = 1 := by rw [← actG_mul ε hyN hyN, hy2, actG_one]
  obtain ⟨γ, hγ⟩ := hD.conj_centralizer (h.Rbar ε) _ hylin hsq
  obtain ⟨l, rfl⟩ := psi_surjective ε γ
  have hlN : (l : G) ∈ normalizer (L : Set G) := le_normalizer l.2
  obtain ⟨u₀, hu₀⟩ : ∃ u₀, (l : G) * y * (l : G)⁻¹ = u₀ := ⟨_, rfl⟩
  have hu₀N : u₀ ∈ normalizer (L : Set G) := hu₀ ▸ mul_mem (mul_mem hlN hyN) (inv_mem hlN)
  have hact : actG L ε u₀ =
      MulAut.conj (psi L ε l) * actG L ε y * (MulAut.conj (psi L ε l))⁻¹ := by
    rw [← hu₀, actG_mul ε (mul_mem hlN hyN) (inv_mem hlN), actG_mul ε hlN hyN, actG_inv ε hlN,
      actG_of_mem_self ε l.2]
  have hfix : ∀ ρ ∈ (h.Rbar ε : Subgroup 𝕊), actG L ε u₀ ρ = ρ := by
    rw [hact]
    exact hγ
  have hu₀lin : actG L ε u₀ ∉ Lin := fun h2 => hylin (by
    have h3 := hD.normal.conj_mem _ h2 (MulAut.conj (psi L ε l))⁻¹
    rwa [hact, show (MulAut.conj (psi L ε l))⁻¹ * (MulAut.conj (psi L ε l) * actG L ε y *
      (MulAut.conj (psi L ε l))⁻¹) * (MulAut.conj (psi L ε l))⁻¹⁻¹ = actG L ε y by group] at h3)
  have hRY : S ⊓ L ≤ actCentralizer L ε (actG L ε u₀) := by
    intro r hr
    have hrL := (mem_inf.mp hr).2
    refine (mem_actCentralizer ε).mpr ⟨le_normalizer hrL, ?_⟩
    have h1 := mulAut_mul_conj_mul_inv (actG L ε u₀) (psi L ε ⟨r, hrL⟩)
    rw [hfix _ (h.psi_mem_Rbar ε hr)] at h1
    rw [actG_of_mem_self ε hrL]
    exact (mul_inv_eq_iff_eq_mul.mp h1).symm
  have hu₀Y : u₀ ∈ actCentralizer L ε (actG L ε u₀) := (mem_actCentralizer ε).mpr ⟨hu₀N, rfl⟩
  obtain ⟨P, hP, hRP⟩ := exists_isSylowOf_ge_of_le hRY h.R_sylow.isPGroup
  have hy1 : y ≠ 1 := fun h1 => hylin (by rw [h1, actG_one]; exact one_mem _)
  have hu₀2 : orderOf u₀ = 2 := by
    rw [← hu₀, orderOf_conj']
    exact orderOf_eq_prime (by rw [sq]; exact hy2) hy1
  have hzp : IsPGroup 2 (zpowers u₀) := by
    refine IsPGroup.of_card (n := 1) ?_
    rw [Nat.card_zpowers, pow_one, hu₀2]
  obtain ⟨k, hkY, hk⟩ := exists_conj_le_of_isSylowOf hP (zpowers_le.mpr hu₀Y) hzp
  have hPN : P ≤ normalizer (L : Set G) := fun p hp => ((mem_actCentralizer ε).mp (hP.le hp)).1
  have hkN := ((mem_actCentralizer ε).mp hkY).1
  have hkc := ((mem_actCentralizer ε).mp hkY).2
  have hPL : S ⊓ L = P ⊓ L :=
    (h.R_sylow.eq_of_le (le_inf hRP inf_le_right) inf_le_right
      (hP.isPGroup.to_le inf_le_left)).symm
  obtain ⟨u₁, hu₁⟩ : ∃ u₁, k⁻¹ * u₀ * k = u₁ := ⟨_, rfl⟩
  have hu₁P : u₁ ∈ P := hu₁ ▸ hk u₀ (mem_zpowers u₀)
  have hu₁N : u₁ ∈ normalizer (L : Set G) := hPN hu₁P
  have hact₁ : actG L ε u₁ = actG L ε u₀ := by
    rw [← hu₁, actG_mul ε (mul_mem (inv_mem hkN) hu₀N) hkN, actG_mul ε (inv_mem hkN) hu₀N,
      actG_inv ε hkN, mul_assoc, ← hkc, ← mul_assoc, inv_mul_cancel, one_mul]
  have hu₁R : ∀ r ∈ S ⊓ L, u₁ * r * u₁⁻¹ ∈ S ⊓ L := by
    intro r hr
    rw [hPL] at hr ⊢
    exact mem_inf.mpr ⟨mul_mem (mul_mem hu₁P (mem_inf.mp hr).1) (inv_mem hu₁P),
      (mem_normalizer_iff.mp hu₁N r).mp (mem_inf.mp hr).2⟩
  refine ⟨u₁, isConj_iff.mpr ⟨k⁻¹ * l, by rw [← hu₁, ← hu₀]; group⟩, fun r hr => ?_, ?_⟩
  · have h1 := actG_psi ε hu₁N ⟨r, (mem_inf.mp hr).2⟩
    rw [hact₁, hfix _ (h.psi_mem_Rbar ε hr)] at h1
    have h2 := h.eq_of_psi_eq ε hr (hu₁R r hr) h1
    calc u₁ * r = u₁ * r * u₁⁻¹ * u₁ := by group
      _ = r * u₁ := by rw [← h2]
  · rw [hact₁]
    exact hu₀lin

end Sec5

end CFSG.ComponentClassification.Foote5
