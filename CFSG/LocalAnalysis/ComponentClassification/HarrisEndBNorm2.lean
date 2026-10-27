module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisEndBNorm1
public import CFSG.LocalAnalysis.ComponentClassification.HarrisEndBLayer
public import CFSG.LocalAnalysis.ComponentClassification.HarrisEndLift

public noncomputable section

namespace CFSG.ComponentClassification.HarrisLit

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer CFSG.ABGLocalTools HarrisEnd
open Standing.Setup42 CFSG.ComponentClassification.J2Cover
open scoped commutatorElement

namespace EndB

@[expose] def piSub {Y : Type*} [Group Y] {E : Subgroup Y} (π : ↥E →* P) (A : Subgroup Y) :
    Subgroup (Equiv.Perm (Fin 315)) :=
  ((A.subgroupOf E).map π).map P.subtype

theorem mem_piSub {Y : Type*} [Group Y] {E : Subgroup Y} {π : ↥E →* P} {A : Subgroup Y}
    {s : Equiv.Perm (Fin 315)} :
    s ∈ piSub π A ↔ ∃ a : ↥E, (a : Y) ∈ A ∧ ((π a : P) : Equiv.Perm (Fin 315)) = s := by
  constructor
  · rintro ⟨_, ⟨a, ha, rfl⟩, rfl⟩
    exact ⟨a, ha, rfl⟩
  · rintro ⟨a, ha, rfl⟩
    exact ⟨π a, ⟨a, ha, rfl⟩, rfl⟩

theorem piSub_le_P {Y : Type*} [Group Y] {E : Subgroup Y} (π : ↥E →* P) (A : Subgroup Y) :
    piSub π A ≤ P :=
  map_subtype_le _

theorem isSylowOf_piSub {Y : Type*} [Group Y] [Finite Y] {E : Subgroup Y} (π : ↥E →* P)
    {A B : Subgroup Y} (hAB : IsSylowOf 2 A B) (hBE : B ≤ E) :
    IsSylowOf 2 (piSub π A) (piSub π B) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hAE : A ≤ E := hAB.le.trans hBE
  have h1 : IsSylowOf 2 (A.subgroupOf E) (B.subgroupOf E) := by
    rw [← isSylowOf_map_subtype_iff E, subgroupOf_map_subtype, subgroupOf_map_subtype,
      inf_of_le_left hAE, inf_of_le_left hBE]
    exact hAB
  exact HarrisLit.isSylowOf_map P.subtype (HarrisLit.isSylowOf_map π h1)

theorem twoPart_P :
    twoPart P = 128 := by
  rw [twoPart, card_P, show (604800 : ℕ) = 2 ^ 7 * 4725 by norm_num,
    Nat.factorization_mul (by norm_num) (by norm_num), Finsupp.add_apply,
    Nat.prime_two.factorization_pow, Finsupp.single_eq_same,
    Nat.factorization_eq_zero_of_not_dvd (by norm_num)]
  rfl

theorem card_le_128
    {S' : Subgroup (Equiv.Perm (Fin 315))} (hS' : IsPGroup 2 S') (hS'P : S' ≤ P) :
    Nat.card S' ≤ 128 :=
  twoPart_P ▸ card_le_twoPart hS' hS'P

end EndB

variable {X : Type} [Group X] [Finite X] {t : X} {L : Subgroup X} {p f : ℕ} {S : Subgroup X}
  {w z : X} {V : Subgroup X} {i j : ℕ}

namespace EndB.JLayer

variable {hs : Setting46e t L p f S w z V i j}
  {π : ↥(layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j))) →* P}

theorem theta_eq_of_comm
    (hJ : JLayer hs π) {A : Subgroup (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j))}
    {ζ : Equiv.Perm (Fin 315)} (hζP : ζ ∈ P)
    (hζ : ∀ r ∈ R, (∀ s ∈ piSub π A, r * s = s * r) → r = 1 ∨ r = ζ)
    {g : MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)} (hg : ∀ a ∈ A, g * a = a * g) :
    hJ.theta g = 1 ∨ hJ.theta g = MulAut.conj ⟨ζ, hζP⟩ := by
  set r := rAutEquiv.symm (hJ.theta g) with hr
  have hrθ : rAutEquiv r = hJ.theta g := MulEquiv.apply_symm_apply _ _
  have hrc : ∀ s ∈ piSub π A, (r : Equiv.Perm (Fin 315)) * s = s * r := by
    intro s hs'
    obtain ⟨a, haA, rfl⟩ := mem_piSub.mp hs'
    have h1 : hJ.theta g (π a) = π a := hJ.theta_apply g a a (by rw [hg _ haA]; group)
    rw [← hrθ, rAutEquiv_apply] at h1
    have h2 : (r : Equiv.Perm (Fin 315)) * (π a : Equiv.Perm (Fin 315)) *
        (r : Equiv.Perm (Fin 315))⁻¹ = π a := by
      rw [← rConj_apply, h1]
    calc (r : Equiv.Perm (Fin 315)) * (π a : Equiv.Perm (Fin 315)) =
        ((r : Equiv.Perm (Fin 315)) * (π a : Equiv.Perm (Fin 315)) *
          (r : Equiv.Perm (Fin 315))⁻¹) * r := by group
      _ = (π a : Equiv.Perm (Fin 315)) * r := by rw [h2]
  rcases hζ r r.2 hrc with h | h
  · left
    have : r = 1 := Subtype.ext h
    rw [← hrθ, this, map_one]
  · right
    have : r = ⟨ζ, P_le_R hζP⟩ := Subtype.ext h
    rw [← hrθ, this]
    exact rAutEquiv_of_mem ⟨ζ, hζP⟩

theorem theta_fix_zeta
    (hJ : JLayer hs π) {A : Subgroup (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j))}
    {ζ : Equiv.Perm (Fin 315)} (hζP : ζ ∈ P) (hζ1 : ζ ≠ 1)
    (hζc : ∀ s ∈ piSub π A, ζ * s = s * ζ)
    (hζ : ∀ r ∈ R, (∀ s ∈ piSub π A, r * s = s * r) → r = 1 ∨ r = ζ)
    {g : MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)} (hg : ∀ a ∈ A, g⁻¹ * a * g ∈ A) :
    hJ.theta g ⟨ζ, hζP⟩ = ⟨ζ, hζP⟩ := by
  set r := rAutEquiv.symm (hJ.theta g) with hr
  have hrθ : rAutEquiv r = hJ.theta g := MulEquiv.apply_symm_apply _ _
  have hconj : ∀ s ∈ piSub π A, (r : Equiv.Perm (Fin 315))⁻¹ * s * r ∈ piSub π A := by
    intro s hs'
    obtain ⟨a, haA, rfl⟩ := mem_piSub.mp hs'
    set b : ↥(layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j))) :=
      ⟨g⁻¹ * a * g, by
        have := (inferInstance : (layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j))).Normal)
        have h := this.conj_mem _ a.2 g⁻¹
        rwa [inv_inv] at h⟩ with hb
    have h1 : hJ.theta g (π b) = π a := hJ.theta_apply g b a (by rw [hb]; group)
    rw [← hrθ, rAutEquiv_apply] at h1
    have h2 : (r : Equiv.Perm (Fin 315)) * (π b : Equiv.Perm (Fin 315)) *
        (r : Equiv.Perm (Fin 315))⁻¹ = π a := by
      rw [← rConj_apply, h1]
    have h3 : (r : Equiv.Perm (Fin 315))⁻¹ * (π a : Equiv.Perm (Fin 315)) * r = π b := by
      rw [← h2]; group
    rw [h3]
    exact mem_piSub.mpr ⟨b, hg _ haA, rfl⟩
  have hc : ∀ s ∈ piSub π A, ((r : Equiv.Perm (Fin 315)) * ζ * (r : Equiv.Perm (Fin 315))⁻¹) *
      s = s * (r * ζ * (r : Equiv.Perm (Fin 315))⁻¹) := by
    intro s hs'
    have h1 := hζc _ (hconj s hs')
    calc (r : Equiv.Perm (Fin 315)) * ζ * (r : Equiv.Perm (Fin 315))⁻¹ * s =
        r * (ζ * ((r : Equiv.Perm (Fin 315))⁻¹ * s * r)) * (r : Equiv.Perm (Fin 315))⁻¹ := by
          group
      _ = r * (((r : Equiv.Perm (Fin 315))⁻¹ * s * r) * ζ) * (r : Equiv.Perm (Fin 315))⁻¹ := by
          rw [h1]
      _ = s * (r * ζ * (r : Equiv.Perm (Fin 315))⁻¹) := by group
  have hmem : (r : Equiv.Perm (Fin 315)) * ζ * (r : Equiv.Perm (Fin 315))⁻¹ ∈ R :=
    R.mul_mem (R.mul_mem r.2 (P_le_R hζP)) (R.inv_mem r.2)
  have hfix : (r : Equiv.Perm (Fin 315)) * ζ * (r : Equiv.Perm (Fin 315))⁻¹ = ζ := by
    rcases hζ _ hmem hc with h | h
    · exfalso
      apply hζ1
      calc ζ = (r : Equiv.Perm (Fin 315))⁻¹ * (r * ζ * (r : Equiv.Perm (Fin 315))⁻¹) * r := by
            group
        _ = 1 := by rw [h]; group
    · exact h
  apply Subtype.ext
  rw [← hrθ, rAutEquiv_apply, rConj_apply]
  exact hfix

theorem theta_commutator_eq_one
    (hJ : JLayer hs π) {A : Subgroup (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j))}
    {ζ : Equiv.Perm (Fin 315)} (hζP : ζ ∈ P) (hζ1 : ζ ≠ 1)
    (hζc : ∀ s ∈ piSub π A, ζ * s = s * ζ)
    (hζ : ∀ r ∈ R, (∀ s ∈ piSub π A, r * s = s * r) → r = 1 ∨ r = ζ)
    {c g : MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)} (hc : ∀ a ∈ A, c * a = a * c)
    (hg : ∀ a ∈ A, g⁻¹ * a * g ∈ A) : hJ.theta ⁅c, g⁆ = 1 := by
  rw [map_commutatorElement]
  rcases hJ.theta_eq_of_comm hζP hζ hc with h | h
  · rw [h, commutatorElement_def]
    group
  · have hfix := hJ.theta_fix_zeta hζP hζ1 hζc hζ hg
    have hcomm : MulAut.conj (⟨ζ, hζP⟩ : P) * hJ.theta g =
        hJ.theta g * MulAut.conj (⟨ζ, hζP⟩ : P) := by
      ext x : 1
      simp only [MulAut.mul_apply, MulAut.conj_apply, map_mul, map_inv, hfix]
    rw [h, commutatorElement_def, hcomm]
    group

theorem barOf_oP_le
    (hJ : JLayer hs π) {W : Subgroup X} (hβZ : w ^ (orderOf w / 2) * t ^ i * z ^ j ∈ zW W) :
    barOf (centralizer {w ^ (orderOf w / 2) * t ^ i * z ^ j}) (oP W) ≤
      layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)) := by
  have hle : oP W ≤ preimageOf (centralizer {w ^ (orderOf w / 2) * t ^ i * z ^ j})
      (layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j))) := by
    rw [oP, closure_le]
    rintro x ⟨hxC, hxo⟩
    have hxM : x ∈ centralizer ({w ^ (orderOf w / 2) * t ^ i * z ^ j} : Set X) :=
      mem_centralizer_singleton_iff.mpr (mem_centralizer_iff.mp hxC _ hβZ).symm
    rw [SetLike.mem_coe, mem_preimageOf hxM]
    refine hJ.odd_mem_layer (Odd.of_dvd_nat hxo ?_)
    have := orderOf_map_dvd (QuotientGroup.mk' (pPrimeCore 2
      ↥(centralizer ({w ^ (orderOf w / 2) * t ^ i * z ^ j} : Set X)))) ⟨x, hxM⟩
    rwa [Subgroup.orderOf_mk] at this
  rintro _ ⟨x, hx, rfl⟩
  have h := (mem_preimageOf x.2).mp (hle hx)
  exact h

end EndB.JLayer

theorem Setting46e.exists_zprime (hKC : AutPSL2CentralizerInput)
    (hs : Setting46e t L p f S w z V i j) {W : Subgroup X}
    (hW : IsSylowOf 2 W (centralizer ({w ^ (orderOf w / 2) * t ^ i * z ^ j} : Set X)))
    (hUW : V ⊓ centralizer ({w ^ (orderOf w / 2) * t ^ i * z ^ j} : Set X) ≤ W) :
    ∃ z' : X, z' ∈ EndB.zW W ∧ z' ^ 2 = 1 ∧ ∀ y : X, y ∈ centralizer (EndB.zW W : Set X) ↔
      y ∈ centralizer ({w ^ (orderOf w / 2) * t ^ i * z ^ j} : Set X) ∧ y * z' = z' * y := by
  set β := w ^ (orderOf w / 2) * t ^ i * z ^ j with hβ
  obtain ⟨hβZ, hZle⟩ := Standing.Setup42.center_W hKC hs.setup hs.sylow_V hs.le_V hs.beta hW hUW
  have hβ2 : β ^ 2 = 1 := hs.setup.sq_eq_one_of_mem_X (beta_mem_X i j)
  have hz2 : z ^ 2 = 1 := by rw [← hs.setup.z_order]; exact pow_orderOf_eq_one z
  have hzM : z ∈ centralizer ({β} : Set X) := K_le_centralizer_beta i j hs.lemma45.z_mem.2
  have hβz : β * z = z * β := (mem_centralizer_singleton_iff.mp hzM).symm
  have hcases : ∀ x ∈ EndB.zW W, x = 1 ∨ x = β ∨ x = z ∨ x = β * z :=
    fun x hx => mem_closure_pair hβ2 hz2 hβz (hZle hx)
  by_cases hz : z ∈ EndB.zW W
  · refine ⟨z, hz, hz2, fun y => ⟨fun hy => ⟨?_, ?_⟩, ?_⟩⟩
    · exact mem_centralizer_singleton_iff.mpr (mem_centralizer_iff.mp hy β hβZ).symm
    · exact (mem_centralizer_iff.mp hy z hz).symm
    · rintro ⟨hyM, hyz⟩
      have hyβ : y * β = β * y := mem_centralizer_singleton_iff.mp hyM
      rw [mem_centralizer_iff]
      intro x hx
      rcases hcases x hx with rfl | rfl | rfl | rfl
      · group
      · exact hyβ.symm
      · exact hyz.symm
      · calc β * z * y = β * (z * y) := by group
          _ = β * (y * z) := by rw [hyz]
          _ = (β * y) * z := by group
          _ = (y * β) * z := by rw [hyβ]
          _ = y * (β * z) := by group
  · refine ⟨β, hβZ, hβ2, fun y => ⟨fun hy => ⟨?_, ?_⟩, ?_⟩⟩
    · exact mem_centralizer_singleton_iff.mpr (mem_centralizer_iff.mp hy β hβZ).symm
    · exact (mem_centralizer_iff.mp hy β hβZ).symm
    · rintro ⟨hyM, -⟩
      have hyβ : y * β = β * y := mem_centralizer_singleton_iff.mp hyM
      rw [mem_centralizer_iff]
      intro x hx
      rcases hcases x hx with rfl | rfl | rfl | rfl
      · group
      · exact hyβ.symm
      · exact absurd hx hz
      · exfalso
        apply hz
        have := mul_mem (inv_mem hβZ) hx
        rwa [show β⁻¹ * (β * z) = z by group] at this

end CFSG.ComponentClassification.HarrisLit
