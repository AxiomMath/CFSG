module

public import CFSG.Open.Defs
public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83SmallRank627WreathR
import CFSG.GroupTheory.ElementaryAbelianTransport

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open Subgroup

local notation "W₃" => Multiplicative (ZMod 3) ≀ᵣ Multiplicative (ZMod 3)

private def wreath65Prod : W₃ →* Multiplicative (ZMod 3) where
  toFun w := ∏ x, w.left x
  map_one' := by simp
  map_mul' a b := by
    simp only [RegularWreathProduct.mul_left, Pi.mul_apply, Finset.prod_mul_distrib]
    congr 1
    exact Fintype.prod_equiv (Equiv.mulLeft a.right⁻¹) _ _ (fun _ => rfl)

private def wreath65Abel : W₃ →* Multiplicative (ZMod 3) × Multiplicative (ZMod 3) :=
  (RegularWreathProduct.rightHom : W₃ →* Multiplicative (ZMod 3)).prod wreath65Prod

private theorem wreath65_mem_ker {w : W₃} :
    w ∈ wreath65Abel.ker ↔ w.right = 1 ∧ ∏ x, w.left x = 1 := by
  simp [wreath65Abel, wreath65Prod, MonoidHom.mem_ker, Prod.ext_iff]

private theorem wreath65Abel_surjective : Function.Surjective wreath65Abel := by
  rintro ⟨q, s⟩
  refine ⟨⟨Pi.mulSingle 1 s, q⟩, ?_⟩
  simp [wreath65Abel, wreath65Prod]

private theorem wreath65_card_ker : Nat.card wreath65Abel.ker = 9 := by
  have h := Subgroup.card_ker_mul_card_of_surjective wreath65Abel_surjective
  rw [RegularWreathProduct.card, wreath_card_zmod_three, Nat.card_prod, wreath_card_zmod_three] at h
  omega

section Commutator

open scoped commutatorElement

private theorem wreath65_commutator_apply (f : Multiplicative (ZMod 3) → Multiplicative (ZMod 3))
    (c : Multiplicative (ZMod 3)) :
    ⁅(⟨f, 1⟩ : W₃), (⟨1, c⟩ : W₃)⁆ = (⟨fun x => f x * (f (c⁻¹ * x))⁻¹, 1⟩ : W₃) := by
  refine RegularWreathProduct.ext ?_ ?_
  · funext x
    simp [commutatorElement_def]
    exact mul_one _
  · simp [commutatorElement_def]

private theorem wreath65_exists_diff :
    ∀ g : Multiplicative (ZMod 3) → Multiplicative (ZMod 3), ∏ x, g x = 1 →
    ∃ f : Multiplicative (ZMod 3) → Multiplicative (ZMod 3),
      ∀ x, f x * (f ((Multiplicative.ofAdd (1 : ZMod 3))⁻¹ * x))⁻¹ = g x := by
  decide

private theorem wreath65_ker_le_commutator : wreath65Abel.ker ≤ commutator W₃ := by
  intro w hw
  obtain ⟨hr, hp⟩ := wreath65_mem_ker.1 hw
  obtain ⟨f, hf⟩ := wreath65_exists_diff w.left hp
  have hw' : w = ⁅(⟨f, 1⟩ : W₃), (⟨1, Multiplicative.ofAdd (1 : ZMod 3)⟩ : W₃)⁆ := by
    rw [wreath65_commutator_apply]
    exact RegularWreathProduct.ext (funext fun x => (hf x).symm) hr
  rw [hw']
  exact Subgroup.commutator_mem_commutator (mem_top _) (mem_top _)

end Commutator

private theorem wreath65_commutator_eq : commutator W₃ = wreath65Abel.ker :=
  le_antisymm (Abelianization.commutator_subset_ker _) wreath65_ker_le_commutator

private theorem wreath65_isElemAbelian_of_le {G : Type*} [Group G] {A B : Subgroup G}
    (hBA : B ≤ A) (hA : IsElemAbelian 3 A) : IsElemAbelian 3 B :=
  CFSG.Open.IsElemAbelian.mono hA hBA

theorem exists_wreath_commutator {G : Type} [Group G] {R : Subgroup G}
    (e : R ≃* (Multiplicative (ZMod 3) ≀ᵣ Multiplicative (ZMod 3))) :
    ∃ E : Subgroup G, E ≤ R ∧ IsElemAbelian 3 E ∧ Nat.card E = 27 ∧ (⁅R, R⁆ : Subgroup G) ≤ E ∧
      IsElemAbelian 3 (⁅R, R⁆ : Subgroup G) ∧ Nat.card (⁅R, R⁆ : Subgroup G) = 9 := by
  let ι : W₃ →* G := R.subtype.comp e.symm.toMonoidHom
  have hιinj : Function.Injective ι := R.subtype_injective.comp e.symm.injective
  have hrange : ι.range = R := by
    ext g
    refine ⟨?_, fun hg => ⟨e ⟨g, hg⟩, by simp [ι]⟩⟩
    rintro ⟨w, rfl⟩
    exact (e.symm w).2
  let A₀ : Subgroup W₃ := (RegularWreathProduct.rightHom :
    Multiplicative (ZMod 3) ≀ᵣ Multiplicative (ZMod 3) →* Multiplicative (ZMod 3)).ker
  have hA₀ : IsElemAbelian 3 (A₀.map ι) := by
    have := wreath_ker_isElemAbelian.1
    refine ⟨Subgroup.map_isMulCommutative A₀ ι, ?_⟩
    rintro _ ⟨a, ha, rfl⟩
    rw [← map_pow, wreath_ker_isElemAbelian.2 a ha, map_one]
  have hcomm : (⁅R, R⁆ : Subgroup G) = wreath65Abel.ker.map ι := by
    rw [← hrange, MonoidHom.range_eq_map, ← Subgroup.map_commutator, ← wreath65_commutator_eq]
    rfl
  have hker : wreath65Abel.ker.map ι ≤ A₀.map ι :=
    Subgroup.map_mono fun w hw => (wreath65_mem_ker.1 hw).1
  refine ⟨A₀.map ι, ?_, hA₀, ?_, hcomm ▸ hker, hcomm ▸ wreath65_isElemAbelian_of_le hker hA₀, ?_⟩
  · rintro _ ⟨a, _, rfl⟩
    exact (e.symm a).2
  · exact (Subgroup.card_map_of_injective hιinj).trans wreath_card_ker
  · rw [hcomm]
    exact (Subgroup.card_map_of_injective hιinj).trans wreath65_card_ker

end CFSG.LocalAnalysis.RankThreeTheoremC
