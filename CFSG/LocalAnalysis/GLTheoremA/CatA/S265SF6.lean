module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.S265SF5
import CFSG.GroupTheory.ElementaryAbelianTransport
import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogRigidityCommon
import CFSG.LocalAnalysis.ComponentInitial.LinearHigherFieldInvolution
import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherPrimeFormRealization
import CFSG.LocalAnalysis.StandardType.GGPGLTorality
import CFSG.LocalAnalysis.StandardType.GGTableBUnitaryDvdCodimOne
import CFSG.LocalAnalysis.StandardType.GGTableBUnitaryDvdTorality
import CFSG.RankThree.PartOne.KC.UnitaryCrossPrimeModel
import CFSG.RankThree.PartOne.KC.UnitaryGoodModel
import CFSG.RankThree.PartOne.KC.UnitaryCrossPrimeSetting
import CFSG.RankThree.PartOne.KC.UnitaryGoodSpecial

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S265

open Matrix CFSG.Open CFSG.LocalAnalysis.GLTheoremA CFSG.StandardType
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
  CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open CFSG.RankThree.PartOne.KCUnitaryModel
open CFSG.Assembly (LargeEvenGUSet)
open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup)

namespace SF

variable {m n p : ℕ} {F : Type} [Field F]

theorem card_le_of_nl_primeFormD (hF : UnitaryFieldData 2 m F) (hn : 3 ≤ n) (hp : p.Prime)
    (hq : 3 < 2 ^ m) (hpq : p ∣ 2 ^ m + 1)
    {X : Subgroup (MulAut (primeFormP hF ((1 : GL (Fin n) F) : Matrix (Fin n) (Fin n) F)))}
    (hXD : X ≤ primeFormD hF ((1 : GL (Fin n) F) : Matrix (Fin n) (Fin n) F))
    (hX : IsElemAbelian p X) (hnl : ∀ α ∈ X, α ≠ 1 → GLAPLayer p (fixSubgroup α) = ⊥) :
    Nat.card X ≤ p ^ (n / p + 1) := by
  haveI := hF.finite
  have hp2 := TableBUD.ne_two_of_dvd hF hpq
  have hne : ¬(n = 3 ∧ 2 ^ m = 2) := fun h' => by have := h'.2; omega
  set ρ := primeFormConjHom hF (idGram F n)
  have hXr : X ≤ ρ.range := hXD
  have hk : ρ.rangeRestrict.ker ≤
      ((conjAut n F).comp (primeFormUnitary hF (idGram F n)).subtype).ker := fun A hA => by
    rw [MonoidHom.ker_rangeRestrict, MonoidHom.mem_ker] at hA
    obtain ⟨c, -, hc⟩ := (primeFormConjHom_eq_one_iff_of_ne (by omega) hne A).1 hA
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply, Subgroup.coe_subtype, hc, conjAut_scalar]
  obtain ⟨θ, hθA⟩ : ∃ θ : ρ.range →* MulAut (projectiveSL n F),
      ∀ A, θ (ρ.rangeRestrict A) = conjAut n F A :=
    ⟨ρ.rangeRestrict.liftOfSurjective ρ.rangeRestrict_surjective ⟨_, hk⟩,
      fun A => ρ.rangeRestrict.liftOfRightInverse_comp_apply _ _ ⟨_, hk⟩ A⟩
  have hθinj : Function.Injective θ := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro y hy
    obtain ⟨A, rfl⟩ := ρ.rangeRestrict_surjective y
    rw [MonoidHom.mem_ker, hθA] at hy
    obtain ⟨c, hc⟩ := (CFSG.ComponentClassification.UnbalancedCatalog.conjAut_eq_one_iff
      (by omega) _).1 hy
    have hcn := norm_eq_one_of_scalar_mem_primeFormUnitary hF (n := n) (by omega) 1
      (by rw [hc]; exact A.2)
    rw [Subgroup.mem_bot, ← MonoidHom.mem_ker, MonoidHom.ker_rangeRestrict, MonoidHom.mem_ker]
    exact (primeFormConjHom_eq_one_iff_of_ne (by omega) hne A).2
      ⟨c, (pow_succ_eq_one_iff_norm hF c).2 hcn, hc.symm⟩
  have hX' : IsElemAbelian p ((X.subgroupOf ρ.range).map θ) := (hX.subgroupOf _).map θ
  have hcard : Nat.card ((X.subgroupOf ρ.range).map θ) = Nat.card X := by
    rw [Subgroup.card_map_of_injective hθinj]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hXr).toEquiv
  have hXU : ∀ x ∈ (X.subgroupOf ρ.range).map θ,
      ∃ M ∈ LargeEvenGUSet (Fin n) F (2 ^ m), conjAut n F M = x := by
    rintro _ ⟨y, -, rfl⟩
    obtain ⟨A, rfl⟩ := ρ.rangeRestrict_surjective y
    exact ⟨A, TableBUD.mem_guSet_of_mem_primeFormUnitary hF A.2, (hθA A).symm⟩
  rcases TypeA.PGLTor.toral_or_card_le hp hp2 (TableBUD.dvd_card_sub_one' hF hpq)
      (TypeA.isProjElem_comap (by omega) hX') with htor | hbound
  · obtain ⟨P, hP, hPd⟩ :=
      TableBUD.exists_unitary_diag_of_isToral hF hp hpq (by omega) hX' hXU htor
    exact (card_le_of_unitary_diag_nl hF hn hp hq hpq hXD hX hnl hP fun A hA =>
      hPd A ⟨ρ.rangeRestrict A, hA, hθA A⟩).trans (Nat.le_self_pow (Nat.succ_ne_zero _) p)
  · rw [TypeA.card_comap_eq (by omega) (fun x hx => (hXU x hx).imp fun M hM => hM.2),
      Fintype.card_fin, hcard] at hbound
    exact Nat.le_of_mul_le_mul_right hbound (by have := Finite.one_lt_card (α := F); omega)

theorem card_le_of_nl_unitary (hF : UnitaryFieldData 2 m F) (hn : 4 ≤ n) (hp : p.Prime)
    (hq : 3 < 2 ^ m) (hpq : p ∣ 2 ^ m + 1)
    {X : Subgroup (MulAut (primeFormP hF ((1 : GL (Fin n) F) : Matrix (Fin n) (Fin n) F)))}
    (hX : IsElemAbelian p X) (hnl : ∀ α ∈ X, α ≠ 1 → GLAPLayer p (fixSubgroup α) = ⊥) :
    Nat.card X ≤ p ^ (n / p + 1) :=
  card_le_of_nl_primeFormD hF (by omega) hp hq hpq (le_primeFormD_of_nl hF (by omega) (by omega)
    hp (TableBUD.ne_two_of_dvd hF hpq) hpq hX hnl) hX hnl

end SF

end CFSG.LocalAnalysis.GLTheoremA.S265

end
