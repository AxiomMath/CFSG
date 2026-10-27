module

public import CFSG.LocalAnalysis.ComponentClassification.GSThmB7QPUClL2Card
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafOddB
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofX10SpModel
import CFSG.Adapters.StatedPSLTwo
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB7QPUClBar

public section

namespace CFSG.ComponentClassification.GSThmB.QPUCl

open CFSG Subgroup CFSG.Blueprint CFSG.Assembly.LowTwoRank CFSG.ComponentClassification.CatLeaf
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)

theorem lieModel_psl_two_isSimpleGroup {X : Type} [Group X] {p f : ℕ}
    (h : LieModel X .PSL 2 p f) : IsSimpleGroup X :=
  CFSG.Blueprint.LieModel.isSimpleGroup_psl_two h

theorem center_eq_pPrimeCore_of_simple {L : Type*} [Group L] [Finite L] (hq : IsQuasisimple L)
    (hs : IsSimpleGroup (L ⧸ pPrimeCore 2 L)) : center L = pPrimeCore 2 L := by
  have hOZ : pPrimeCore 2 L ≤ center L := by
    rcases LieType.CurtisTits.le_center_or_eq_top_of_isQuasisimple hq (pPrimeCore 2 L) with h | h
    · exact h
    · exfalso
      have : Subsingleton (L ⧸ pPrimeCore 2 L) := by
        rw [h]
        exact QuotientGroup.subsingleton_quotient_top
      exact (IsSimpleGroup.toNontrivial (G := L ⧸ pPrimeCore 2 L)).exists_pair_ne.elim
        fun x hx => hx.elim fun y hxy => hxy (Subsingleton.elim x y)
  refine le_antisymm (fun z hz => ?_) hOZ
  set φ : L ⧸ pPrimeCore 2 L →* L ⧸ center L := QuotientGroup.map _ _ (MonoidHom.id L) hOZ
  have hφs : Function.Surjective φ := by
    intro y
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective (center L) y
    exact ⟨QuotientGroup.mk x, rfl⟩
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal φ.ker with h | h
  · have h1 : (QuotientGroup.mk z : L ⧸ pPrimeCore 2 L) ∈ φ.ker := by
      rw [MonoidHom.mem_ker]
      exact (QuotientGroup.eq_one_iff z).mpr hz
    rw [h, mem_bot, QuotientGroup.eq_one_iff] at h1
    exact h1
  · exfalso
    obtain ⟨-, hS, -⟩ := hq
    obtain ⟨x, y, hxy⟩ := hS.toNontrivial.exists_pair_ne
    apply hxy
    obtain ⟨x', rfl⟩ := hφs x
    obtain ⟨y', rfl⟩ := hφs y
    have hx : x' ∈ φ.ker := h ▸ mem_top x'
    have hy : y' ∈ φ.ker := h ▸ mem_top y'
    rw [MonoidHom.mem_ker] at hx hy
    rw [hx, hy]

theorem eq_one_of_mem_center_of_eq_pPrimeCore {L : Type*} [Group L] [Finite L]
    (hZO : center L = pPrimeCore 2 L) {z : L} (hz : z ∈ center L) (hzz : z * z = 1) : z = 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hcop := LocalAnalysis.ComponentInitial.coprime_orderOf_of_mem_pPrimeCore (p := 2)
    (hZO ▸ hz)
  have h2 : orderOf z ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [pow_two, hzz])
  exact orderOf_eq_one_iff.mp (Nat.Coprime.eq_one_of_dvd hcop.symm h2)

theorem center_eq_bot_of_barConfig {Q : Type} [Group Q] [Finite Q] [IsSimpleGroup Q]
    {p' f' p f : ℕ} (h : BarConfig Q p' f' p f) : center Q = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨E, L, t, J, J₀, -, -, hLc, -⟩ := h
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (center Q) with hZ | hZ
  · exact hZ
  · exfalso
    obtain ⟨-, -, hq⟩ :=
      (CatalogueBPrimeJoin.pComponent_iff_subnormal_generated_quasisimple 2 _).1 hLc
    obtain ⟨a, b, hab⟩ := hq.2.2
    obtain ⟨a', rfl⟩ := QuotientGroup.mk'_surjective (center _) a
    obtain ⟨b', rfl⟩ := QuotientGroup.mk'_surjective (center _) b
    obtain ⟨a'', rfl⟩ := QuotientGroup.mk'_surjective (pPrimeCore 2 _) a'
    obtain ⟨b'', rfl⟩ := QuotientGroup.mk'_surjective (pPrimeCore 2 _) b'
    have hbZ : ((b'' : fixedBy E) : Q) ∈ center Q := hZ ▸ mem_top _
    have hc : a'' * b'' = b'' * a'' :=
      Subtype.ext (Subtype.ext ((mem_center_iff.mp hbZ) ((a'' : fixedBy E) : Q)))
    apply hab
    rw [← map_mul, ← map_mul, ← map_mul, ← map_mul, hc]

theorem four_mul_le_factorization_of_barConfig {Q : Type} [Group Q] [Finite Q] {p' f' p f : ℕ}
    (hp'2 : p' ≠ 2) (h : BarConfig Q p' f' p f) : 4 * f' ≤ (Nat.card Q).factorization p' := by
  obtain ⟨E, L, t, J, J₀, -, -, -, -, hLm, -⟩ := h
  obtain ⟨-, hfac⟩ := CatLeafProof.X10Lin.lieOrder_of_lieModel_classical
    (Or.inr (Or.inr (Or.inl rfl))) hp'2 (by norm_num) hLm
  have h1 : Nat.card (↥L ⧸ pPrimeCore 2 ↥L) ∣ Nat.card Q :=
    (Subgroup.card_quotient_dvd_card _).trans (Subgroup.card_subgroup_dvd_card L)
  have hle := (Nat.factorization_le_iff_dvd Nat.card_pos.ne' Nat.card_pos.ne').2 h1 p'
  rw [hfac] at hle
  exact hle

theorem exists_component_of_barConfig {Q : Type} [Group Q] [Finite Q]
    (hQ : FixedTwoComponentsQuasisimple Q) (hZ : center Q = ⊥) {p' f' p f : ℕ}
    (h : BarConfig Q p' f' p f) :
    ∃ t : Q, t * t = 1 ∧ t ≠ 1 ∧ ∀ α : MulAut Q, (∀ x, α x = t * x * t⁻¹) →
      orderOf α = 2 ∧ ∃ J' : Subgroup (fixedSubgroup α), IsComponent J' ∧
        (∀ z ∈ J', (∀ y ∈ J', z * y = y * z) → z * z = 1 → z = 1) ∧
        LieModel (↥J' ⧸ center ↥J') .PSL 2 p f := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨E, L, t, J, J₀, -, -, -, -, -, -, ht2, ht1, hJt, hJc, hJm, -⟩ := h
  refine ⟨t, ht2, ht1, fun α hα => ?_⟩
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
  have hJm' : LieModel (↥J' ⧸ pPrimeCore 2 ↥J') .PSL 2 p f :=
    LieType.CurtisTits.lieModel_of_mulEquiv
      (QuotientGroup.congr _ _ eJ (pPrimeCore_map_iso 2 eJ)) hJm
  have hZO := center_eq_pPrimeCore_of_simple hq (lieModel_psl_two_isSimpleGroup hJm')
  refine ⟨J', ⟨hq, hsn⟩, fun z hz hzc hzz => ?_,
    LieType.CurtisTits.lieModel_of_mulEquiv (QuotientGroup.quotientMulEquivOfEq hZO).symm hJm'⟩
  have hzc' : (⟨z, hz⟩ : J') ∈ center ↥J' :=
    mem_center_iff.mpr fun y => Subtype.ext (hzc y y.2).symm
  exact congrArg Subtype.val (eq_one_of_mem_center_of_eq_pPrimeCore hZO hzc' (Subtype.ext hzz))

theorem eq_of_centralModel_of_lieModel {L : Type} [Group L] {p f : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hf : 1 ≤ f) (hL : LieModel (L ⧸ center L) .PSL 2 p f) {t : StatedLieTag}
    {k e : ℕ} (ht : CatLeafProof.X10Lin.IsClassicalTag t)
    (h : CatLeafProof.X10Sp.CentralModel p t k e L) : t = .PSL ∧ k = 2 ∧ e = f :=
  eq_psl2_of_two_lieModels hp hp2 hf ht h.1 h.2 hL

end CFSG.ComponentClassification.GSThmB.QPUCl
