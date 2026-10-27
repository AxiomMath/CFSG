module

public import CFSG.LocalAnalysis.ComponentClassification.GSThmB82CIUClBar
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB7QPUClLinCore

public section

namespace CFSG.ComponentClassification.GSThmB.QPUJ6Cl

open CFSG Subgroup CFSG.Blueprint CFSG.ComponentClassification.CatLeaf
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)

theorem center_eq_bot_of_barData6 {Q : Type} [Group Q] [Finite Q] [IsSimpleGroup Q]
    {E : Subgroup (MulAut Q)} {L : Subgroup Q} {t : Q} {J J₀ : Subgroup Q} {p f : ℕ}
    (h : BarData6 E L t J J₀ p f) : center Q = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (center Q) with hZ | hZ
  · exact hZ
  · exfalso
    obtain ⟨-, -, hq⟩ :=
      (CatalogueBPrimeJoin.pComponent_iff_subnormal_generated_quasisimple 2 _).1 h.hLc
    obtain ⟨a, b, hab⟩ := hq.2.2
    obtain ⟨a', rfl⟩ := QuotientGroup.mk'_surjective (center _) a
    obtain ⟨b', rfl⟩ := QuotientGroup.mk'_surjective (center _) b
    obtain ⟨a'', rfl⟩ := QuotientGroup.mk'_surjective (pPrimeCore 2 _) a'
    obtain ⟨b'', rfl⟩ := QuotientGroup.mk'_surjective (pPrimeCore 2 _) b'
    have hbZ : ((b'' : QPUCl.fixedBy E) : Q) ∈ center Q := hZ ▸ mem_top _
    have hc : a'' * b'' = b'' * a'' :=
      Subtype.ext (Subtype.ext ((mem_center_iff.mp hbZ) ((a'' : QPUCl.fixedBy E) : Q)))
    apply hab
    rw [← map_mul, ← map_mul, ← map_mul, ← map_mul, hc]

theorem exists_component_of_J {Q : Type} [Group Q] [Finite Q]
    (hQ : FixedTwoComponentsQuasisimple Q) (hZ : center Q = ⊥) {t : Q} {J : Subgroup Q}
    {p e : ℕ} (ht2 : t * t = 1) (ht1 : t ≠ 1) (hJt : J ≤ centralizer {t})
    (hJc : IsPComponent 2 (J.subgroupOf (centralizer {t})))
    (hJm : LieModel (↥J ⧸ pPrimeCore 2 ↥J) .PSL 2 p e) :
    ∀ α : MulAut Q, (∀ x, α x = t * x * t⁻¹) →
      orderOf α = 2 ∧ ∃ J' : Subgroup (fixedSubgroup α), IsComponent J' ∧
        (∀ z ∈ J', (∀ y ∈ J', z * y = y * z) → z * z = 1 → z = 1) ∧
        LieModel (↥J' ⧸ center ↥J') .PSL 2 p e := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro α hα
  have hcent : centralizer ({t} : Set Q) = fixedSubgroup α := by
    ext x
    rw [mem_centralizer_singleton_iff]
    change x * t = t * x ↔ α x = x
    rw [hα]
    constructor
    · intro hx
      rw [← hx, mul_inv_cancel_right]
    · intro hx
      calc x * t = t * x * t⁻¹ * t := by rw [hx]
        _ = t * x := by group
  have hα2 : α * α = 1 := MulEquiv.ext fun x => by
    rw [MulAut.mul_apply, hα, hα, MulAut.one_apply]
    calc t * (t * x * t⁻¹) * t⁻¹ = (t * t) * x * (t * t)⁻¹ := by group
      _ = x := by rw [ht2, one_mul, inv_one, mul_one]
  have hα1 : α ≠ 1 := fun h1 => ht1 (by
    have htZ : t ∈ center Q := mem_center_iff.mpr fun g => by
      have hg := congrArg (fun φ : MulAut Q => φ g) h1
      simp only [MulAut.one_apply, hα] at hg
      calc g * t = t * g * t⁻¹ * t := by rw [hg]
        _ = t * g := by group
    rw [hZ] at htZ
    exact mem_bot.mp htZ)
  refine ⟨orderOf_eq_prime (by rw [sq]; exact hα2) hα1, ?_⟩
  let φ : ↥(centralizer ({t} : Set Q)) ≃* ↥(fixedSubgroup α) := MulEquiv.subgroupCongr hcent
  set J' := (J.subgroupOf (centralizer ({t} : Set Q))).map φ.toMonoidHom with hJ'
  have hJ'c : IsPComponent 2 J' :=
    LocalAnalysis.ComponentInitial.isPComponent_map_of_isPComponent 2 φ hJc
  have hq : IsQuasisimple J' := hQ α hα2 hα1 J' hJ'c
  obtain ⟨hsn, -, -⟩ :=
    (CatalogueBPrimeJoin.pComponent_iff_subnormal_generated_quasisimple 2 J').1 hJ'c
  let eJ : ↥J ≃* ↥J' := (Subgroup.subgroupOfEquivOfLe hJt).symm.trans
    ((J.subgroupOf (centralizer ({t} : Set Q))).equivMapOfInjective φ.toMonoidHom φ.injective)
  have hJm' : LieModel (↥J' ⧸ pPrimeCore 2 ↥J') .PSL 2 p e :=
    LieType.CurtisTits.lieModel_of_mulEquiv
      (QuotientGroup.congr _ _ eJ (pPrimeCore_map_iso 2 eJ)) hJm
  have hZO := QPUCl.center_eq_pPrimeCore_of_simple hq (QPUCl.lieModel_psl_two_isSimpleGroup hJm')
  refine ⟨J', ⟨hq, hsn⟩, fun z hz hzc hzz => ?_,
    LieType.CurtisTits.lieModel_of_mulEquiv (QuotientGroup.quotientMulEquivOfEq hZO).symm hJm'⟩
  have hzc' : (⟨z, hz⟩ : J') ∈ center ↥J' :=
    mem_center_iff.mpr fun y => Subtype.ext (hzc y y.2).symm
  exact congrArg Subtype.val
    (QPUCl.eq_one_of_mem_center_of_eq_pPrimeCore hZO hzc' (Subtype.ext hzz))

end CFSG.ComponentClassification.GSThmB.QPUJ6Cl
