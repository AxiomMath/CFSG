module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec3L34GLevels
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec3L34GE
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec3L34GStep
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec3L34Disch

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup

variable {G : Type} [Group G]

theorem l34g_fstarLayer_le_centralizer (y : G) : fstarLayer y ≤ centralizer ({y} : Set G) :=
  iSup₂_le fun _ hJ => hJ.1.1

private theorem l34g_choose_v {X : Subgroup G} {e y : G} (hy : y ∉ centralizer (X : Set G)) :
    (∀ c ∈ centralizer (X : Set G), e ≠ y * c) ∨
      (∀ c ∈ centralizer (X : Set G), e * y ≠ y * c) := by
  by_contra hcon
  push Not at hcon
  obtain ⟨⟨c, hc, hec⟩, ⟨c', hc', hec'⟩⟩ := hcon
  have h1 : y * (c * y) = y * c' := by rw [← hec', hec, mul_assoc]
  have h2 : c * y = c' := mul_left_cancel h1
  apply hy
  have : y = c⁻¹ * c' := by rw [← h2, inv_mul_cancel_left]
  rw [this]
  exact Subgroup.mul_mem _ (Subgroup.inv_mem _ hc) hc'

theorem l34g_level1 [Finite G] (hNF : Asc82FactNoncentralFixed) (hKA : Asc82FactPocketComp)
    (hKB : Asc82FactPocketLift) (hLB : AschLBalance G) (hA2 : AschA2 G) (hP : L34GPocketComm G)
    (hA : L34GLemmaA G) {x y : G} {X K : Subgroup G} (hD : Sec3PocketData x X y K)
    {I : Subgroup G} (hI : IsComponentIn I (centralizer ({y} : Set G))) (hIF : InFStar I) :
    False := by
  have hx : orderOf x = 2 := hD.involution_x
  have hy : orderOf y = 2 := hD.involution_y
  have hxy : x * y = y * x :=
    (Subgroup.mem_centralizer_singleton_iff.mp (hD.component.1 hD.mem)).symm
  obtain ⟨a, haX, hay⟩ := exists_noncomm_of_sl23PocketIn (inFStar_isQuasisimple hD.inFStar)
    (l34g_sl23PocketIn_of_data hD)
  have hyC : y ∉ centralizer (X : Set G) := fun h => hay (Subgroup.mem_centralizer_iff.mp h a haX)
  obtain ⟨e, z, he, hex, hey, heE, hzE, hez⟩ := l34g_exists_e hNF hx hy hxy hI hIF
  have hey_ne : e ≠ y := by
    rintro rfl
    exact hez (Subgroup.mem_centralizer_singleton_iff.mp
      (l34g_fstarLayer_le_centralizer e hzE)).symm
  have hKy : K ≤ centralizer ({y} : Set G) := hD.pocket.2.1.trans inf_le_right
  have hKcomm : fstarLayer y ⊔ zpowers y ≤ centralizer (K : Set G) := by
    refine sup_le ?_ ?_
    · have h := hP x X y K hD
      rwa [Subgroup.commutator_comm, Subgroup.commutator_eq_bot_iff_le_centralizer] at h
    · refine Subgroup.zpowers_le.mpr (Subgroup.mem_centralizer_iff.mpr fun k hk => ?_)
      exact Subgroup.mem_centralizer_singleton_iff.mp (hKy hk)
  have hex' : Commute e x := hex
  have hey' : Commute e y := hey
  have hyx : Commute y x := hxy.symm
  obtain ⟨v, hv, hvx, hvy, hvmem, hvc⟩ : ∃ v : G, orderOf v = 2 ∧ v * x = x * v ∧
      v * y = y * v ∧ v ∈ fstarLayer y ⊔ zpowers y ∧ ∀ c ∈ centralizer (X : Set G), v ≠ y * c := by
    rcases l34g_choose_v hyC (e := e) with h | h
    · exact ⟨e, he, hex, hey, Subgroup.mem_sup_left heE, h⟩
    · haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
      refine ⟨e * y, ?_, (hex'.mul_left hyx).eq, (hey'.mul_left (Commute.refl y)).eq,
        Subgroup.mul_mem _ (Subgroup.mem_sup_left heE)
          (Subgroup.mem_sup_right (Subgroup.mem_zpowers y)), h⟩
      refine orderOf_eq_prime ?_ ?_
      · rw [hey'.mul_pow, pow_two e, pow_two y, sec63P_mul_self he, sec63P_mul_self hy, one_mul]
      · intro h1
        apply hey_ne
        rw [eq_inv_of_mul_eq_one_left h1, sec63P_inv_eq hy]
  have hvK : K ≤ centralizer ({v} : Set G) := fun k hk =>
    Subgroup.mem_centralizer_singleton_iff.mpr (Subgroup.mem_centralizer_iff.mp (hKcomm hvmem) k hk)
  obtain ⟨D, -, -, hcase⟩ := sec3_pocket_level_step hKA hKB hLB hA2 hD hv hvx hvy hvK hvc
  rcases hcase with ⟨-, K', hdat'⟩ | ⟨hne, u₁, -, K₁, -, hdat₁⟩
  · exact hA v y D K' hdat' hvmem
  · exact l34g_levels23 hKB hLB hA2 hP hA hdat₁ hx hvx.symm hne

theorem asc82CommutingPocket_of_facts (hT2 : Asc82Thm2Q) (hC1 : Asc82CommuteStep)
    (hS : Asc82SchurU43) (hCor : Asc82CorIII) (hNF : Asc82FactNoncentralFixed)
    (hKA : Asc82FactPocketComp) (hKB : Asc82FactPocketLift) : Asc82CommutingPocket := by
  intro G _ _ t L hSet x X y K hD I hI hIF _
  exact l34g_level1 hNF hKA hKB hSet.lBalance hSet.toSec3Setting.a2
    (l34g_pocketComm_of_inputs hT2 hC1 hS hSet) (l34g_lemmaA_of_inputs hT2 hC1 hS hCor hSet)
    hD hI hIF

theorem asc82Lemma34_of_facts (hT2 : Asc82Thm2Q) (hC1 : Asc82CommuteStep) (hS : Asc82SchurU43)
    (hCor : Asc82CorIII) (hNF : Asc82FactNoncentralFixed) (hKA : Asc82FactPocketComp)
    (hKB : Asc82FactPocketLift) : Asc82Lemma34a ∧ Asc82Lemma34b ∧ Asc82Lemma34c :=
  asc82Lemma34_of_remaining_inputs hT2 hC1
    (asc82CommutingPocket_of_facts hT2 hC1 hS hCor hNF hKA hKB) hS

end CFSG.OddStandard.SmallF3.Omega
