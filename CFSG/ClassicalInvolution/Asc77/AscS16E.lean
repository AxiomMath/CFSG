module

public import CFSG.ClassicalInvolution.Asc77.AscS16R
public import CFSG.ClassicalInvolution.Asc77.AscIHSectI
import CFSG.ClassicalInvolution.AschTight.S19MFund
import CFSG.ClassicalInvolution.AschTight.S19MLift
import CFSG.ClassicalInvolution.AschTight.S19MCenter

public section

namespace CFSG.ClassicalInvolution.Asc77

namespace S16

set_option linter.unusedSectionVars false

open CFSG.Open CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution
  CFSG.ClassicalInvolution.Generic CFSG.LieType.Universal CFSG.ClassicalInvolution.Asc77.FrameVertex
  CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Disconnected.AschTight

section Z2

variable {p f : ℕ} [Fact p.Prime] {X : Type} [Group X] [Finite X] {Φ : Set (Subgroup X)}

theorem false_of_z2_section (hR1 : Z2NoD8 p) (hp : p ≠ 2) (hq : 5 ≤ p ^ f)
    (hS : GenSection p f Φ) (D : OmegaLie p f Φ) (hcard : D.card = 1) (i : Fin D.card)
    (hZ2 : (D.tag i = .PSL ∧ D.rank i = 3 ∧ p ^ f % 4 = 3) ∨
      (D.tag i = .PSU ∧ D.rank i = 3 ∧ p ^ f % 4 = 1))
    {H : Type} [Group H] [Finite H] (ι : X →* H) (hι : Function.Injective ι) (a v : H)
    (ha : ∀ x : X, a * ι x * a⁻¹ ∈ ι.range ∧ a⁻¹ * ι x * a ∈ ι.range)
    (hv : ∀ x : X, v * ι x * v⁻¹ ∈ ι.range ∧ v⁻¹ * ι x * v ∈ ι.range)
    {A : Subgroup X} (hA : A ∈ Φ) {z : X} (hzA : IsUniqueInvolution A z)
    (haA : ∀ x ∈ A, ∃ n ∈ oddCoreOf A, a * ι x * a⁻¹ = ι (n * x))
    (hvA : ∀ x ∈ A, ∃ n ∈ oddCoreOf A, v * ι x * v⁻¹ = ι (n * x))
    (ha2 : a * a = ι z) (hv2 : v * v = 1) (hav : v * a * v⁻¹ = a⁻¹) : False := by
  classical
  have hΦ : HypOmegaMod p f Φ := hS.hyp
  have hG2 : D.tag i ≠ .G2 := by
    rcases hZ2 with ⟨h, -⟩ | ⟨h, -⟩ <;> rw [h] <;> decide
  have hD4 : D.tag i ≠ .trialityD4 := by
    rcases hZ2 with ⟨h, -⟩ | ⟨h, -⟩ <;> rw [h] <;> decide
  have hexp : D.exp i = f := (D.exp_eq i).resolve_right fun h => hD4 h.1
  have hΦex : HypOmega p f Φ := hΦ.toExact (OmegaLie.exactMembers hp hq hΦ D)
  obtain ⟨j, R, hRf, hAR⟩ := D.fundamental A hA
  have hsub : Subsingleton (Fin D.card) := by
    rw [hcard]
    infer_instance
  obtain rfl : i = j := Subsingleton.elim _ _
  have hT6 : AschTight.S1911.IsT6Tag (D.tag i) (D.rank i) := by
    rcases hZ2 with ⟨h, h', -⟩ | ⟨h, h', -⟩
    · exact Or.inl ⟨h, h'⟩
    · exact Or.inr (Or.inl ⟨h, h'⟩)
  obtain ⟨c, hc⟩ := AschTight.S19M.exists_isUniqueInvolution_of_mem_fund hp hT6 (D.admissible i) hRf
  have hfin : Finite (modelUniv (D.tag i) (D.rank i) p (D.exp i) Fact.out).K :=
    ModelFacts.finite_modelUniv hp Fact.out (ih8_isFundTag_mf (D.isFundTag i)) (D.admissible i)
  have hodd : Odd (Nat.card (D.hom i).ker) :=
    AschTight.S19M.odd_natCard_ker (D.ker_le_center i)
      (AschTight.S19M.factM3 p (D.exp i) (Fact.out) hp (D.tag i) (D.rank i) hT6 (D.admissible i))
  have hfinker : Finite (D.hom i).ker := inferInstance
  have hcz : D.hom i c = z := by
    have h1 := AschTight.S19M.isUniqueInvolution_map hodd hc
    rw [← hAR] at h1
    exact h1.eq hzA
  set ψ' : (modelUniv (D.tag i) (D.rank i) p (D.exp i) Fact.out).K →* H := ι.comp (D.hom i)
    with hψ'
  have hker : ψ'.ker ≤ Subgroup.center (modelUniv (D.tag i) (D.rank i) p (D.exp i) Fact.out).K := by
    intro y hy
    apply D.ker_le_center i
    rw [MonoidHom.mem_ker] at hy ⊢
    refine hι ?_
    rw [map_one]
    exact hy
  have hsurj : Function.Surjective (D.hom i) := D.hom_surjective_of_gen hcard hS.gen i
  have hrange : ψ'.range = ι.range := by
    ext y
    simp only [ψ', MonoidHom.mem_range, MonoidHom.comp_apply]
    constructor
    · rintro ⟨s, rfl⟩
      exact ⟨_, rfl⟩
    · rintro ⟨x, rfl⟩
      obtain ⟨s, rfl⟩ := hsurj x
      exact ⟨s, rfl⟩
  have hnorm : ∀ w : H, (∀ x : X, w * ι x * w⁻¹ ∈ ι.range ∧ w⁻¹ * ι x * w ∈ ι.range) →
      w ∈ Subgroup.normalizer (ψ'.range : Set H) := by
    intro w hw
    rw [Subgroup.mem_normalizer_iff]
    intro y
    rw [hrange]
    constructor
    · rintro ⟨x, rfl⟩
      exact (hw x).1
    · intro hy
      obtain ⟨x, hx⟩ := hy
      have : y = w⁻¹ * ι x * w := by
        rw [hx]
        group
      rw [this]
      exact (hw x).2
  have hna : a ∈ Subgroup.normalizer (ψ'.range : Set H) := hnorm a ha
  have hnv : v ∈ Subgroup.normalizer (ψ'.range : Set H) := hnorm v hv
  have hexc : ∀ w : H, (∀ x ∈ A, ∃ n ∈ oddCoreOf A, w * ι x * w⁻¹ = ι (n * x)) →
      ∀ x ∈ A, w * ι x = ι x * w := by
    intro w hh x hx
    obtain ⟨n, hn, hnx⟩ := hh x hx
    rw [oddCoreOf_eq_bot_of_exact hΦex.exact hA, Subgroup.mem_bot] at hn
    rw [hn, one_mul] at hnx
    calc w * ι x = (w * ι x * w⁻¹) * w := by group
      _ = ι x * w := by rw [hnx]
  have hψ'A : ∀ r ∈ R, ψ' r ∈ ι '' (A : Set X) := by
    intro r hr
    refine ⟨D.hom i r, ?_, rfl⟩
    rw [hAR]
    exact Subgroup.mem_map_of_mem _ hr
  have hfix : ∀ w : H, (hw : w ∈ Subgroup.normalizer (ψ'.range : Set H)) →
      (∀ x ∈ A, w * ι x = ι x * w) →
      ∀ r ∈ R, toInducedAutOn ψ'.range ⟨w, hw⟩ * innerHom ψ' r =
        innerHom ψ' r * toInducedAutOn ψ'.range ⟨w, hw⟩ := by
    intro w hw hh r hr
    obtain ⟨s, hs, hsr⟩ := hψ'A r hr
    rw [FrameVertex.innerHom_apply, ← map_mul, ← map_mul]
    congr 1
    refine Subtype.ext ?_
    show w * ψ' r = ψ' r * w
    rw [← hsr]
    exact hh s hs
  have hq' : 5 ≤ p ^ D.exp i := by rw [hexp]; exact hq
  have hZ2' : (D.tag i = .PSL ∧ D.rank i = 3 ∧ p ^ D.exp i % 4 = 3) ∨
      (D.tag i = .PSU ∧ D.rank i = 3 ∧ p ^ D.exp i % 4 = 1) := by
    rw [hexp]
    exact hZ2
  refine hR1 (D.tag i) (D.rank i) (D.exp i) hp hq' (D.admissible i) hZ2' ψ' hker R c hRf hc.mem
    hc.sq hc.ne_one (toInducedAutOn ψ'.range ⟨a, hna⟩) (toInducedAutOn ψ'.range ⟨v, hnv⟩)
    (hfix a hna (hexc a haA)) (hfix v hnv (hexc v hvA)) ?_ ?_ ?_
  · rw [FrameVertex.innerHom_apply, ← map_mul]
    congr 1
    refine Subtype.ext ?_
    show a * a = ψ' c
    simp only [ψ', MonoidHom.comp_apply, hcz]
    exact ha2
  · rw [← map_mul]
    have : (⟨v, hnv⟩ * ⟨v, hnv⟩ : ↥(Subgroup.normalizer (ψ'.range : Set H))) = 1 :=
      Subtype.ext hv2
    rw [this, map_one]
  · rw [← map_inv, ← map_mul, ← map_mul, ← map_inv]
    congr 1
    refine Subtype.ext ?_
    show v * a * v⁻¹ = a⁻¹
    exact hav

end Z2

end S16

end CFSG.ClassicalInvolution.Asc77
