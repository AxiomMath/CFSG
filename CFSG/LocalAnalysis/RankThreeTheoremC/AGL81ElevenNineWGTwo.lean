module

public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81ElevenNineWAbstract
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.BlockFieldIndexFiveG2
import CFSG.LocalAnalysis.AGLEmbedding.LeviBlockGTwoBlock
import CFSG.LocalAnalysis.AGLEmbedding.LeviBlockGroups

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.FieldIndexW

open Matrix CFSG.Open CFSG.AGLEmbedding CFSG.AGLEmbedding.LeviBlock CFSG.AGLEmbedding.ParabHub
  CFSG.AGLEmbedding.ParabPrime CFSG.LieType.Universal CFSG.LieType.Steinberg
  CFSG.LieType.Steinberg.Adjoint CFSG.LieType.Chevalley CFSG.Blueprint.Chevalley
  CFSG.LieType.CurtisTits
open CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.FieldIndex
open CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.FieldIndexP
open scoped commutatorElement

section LeviOneNode

variable {Y : Type} [Group Y] [Finite Y] {L P : Subgroup Y} [L.Normal]
  {K : Type} [Group K] [Finite K] {D : UniversalRootDatum K}
  {n : Fin D.rank → K} {H : Fin D.rank → Subgroup K} {M : ℕ}

theorem leviInnAtW_of_oneNodeP (p : ℕ) [OddPrime p] (hPL : P ≤ L)
    (hZL : Odd (Nat.card (Subgroup.center ↥L))) (π : K →* ↥L) (h : BorelQuotient D n H π M)
    {i : Fin D.rank} (hBA : borel D H ≤ coverSub π P) (hI : negIndices D (coverSub π P) = {i})
    (hLU : rankOne D.rootGroup i ⊓ posUnipotentExcept D i = ⊥)
    (hT : ∀ k, ∀ t ∈ H k, ∃ c ∈ rankOne D.rootGroup i, ∀ l ∈ rankOne D.rootGroup i,
      t * l * t⁻¹ = c * l * c⁻¹)
    (hq : CFSG.Open.IsQuasisimple ↥(rankOne D.rootGroup i))
    (hZ : Subgroup.center ↥(rankOne D.rootGroup i) = ⊥)
    (hrk : Open.pRank p (wPre P) ≤ 1) : LeviInnAtPW p P := by
  classical
  set A : Subgroup K := coverSub π P
  haveI := normal_posUnipotentExcept_subgroupOf h hBA hI
  set U : Subgroup ↥A := (posUnipotentExcept D i).subgroupOf A with hU
  set Λ : Subgroup ↥A := (rankOne D.rootGroup i).subgroupOf A with hΛ
  set S : Subgroup (↥A ⧸ U) := Λ.map (QuotientGroup.mk' U)
  have hUA := posUnipotentExcept_le_of_borel_le hBA i
  have hLA : rankOne D.rootGroup i ≤ A := rankOne_le_of_mem_negIndices hBA (by rw [hI]; rfl)
  have hU2 : IsPGroup 2 U := (isPGroup_posUnipotentExcept h i).comap_subtype
  have hc : ∀ a b : ↥A, ⁅a, b⁆ ∈ Λ ⊔ U := fun a b => by
    rw [hΛ, hU, ← Subgroup.subgroupOf_sup hLA hUA, Subgroup.mem_subgroupOf]
    simpa [commutatorElement_def] using commutator_mem_of_negIndices_eq h hBA hI a.2 b.2
  have hΛU : Λ ⊓ U = ⊥ := by
    rw [eq_bot_iff]
    rintro x ⟨hx1, hx2⟩
    have hx : (x : K) ∈ rankOne D.rootGroup i ⊓ posUnipotentExcept D i := ⟨hx1, hx2⟩
    rw [hLU, Subgroup.mem_bot] at hx
    exact (Subgroup.mem_bot).2 (Subtype.ext hx)
  obtain ⟨eΛ⟩ := nonempty_mulEquiv_oneBlock U Λ hΛU
  have e : ↥(rankOne D.rootGroup i) ≃* ↥S := (Subgroup.subgroupOfEquivOfLe hLA).symm.trans eΛ
  have hqS : CFSG.Open.IsQuasisimple ↥S := isQuasisimple_of_mulEquiv e hq
  have hZS : Subgroup.center ↥S = ⊥ := by rw [← map_center_mulEquiv e, hZ, Subgroup.map_bot]
  have hoddLU : ¬ 2 ∣ (Λ ⊔ U).index := by
    have hUplus : posUnipotent D ≤ A := (posUnipotent_le_borel (D := D) (H := H)).trans hBA
    have hUp : posUnipotent D ≤ rankOne D.rootGroup i ⊔ posUnipotentExcept D i := by
      rw [posUnipotent_eq_sup h.extras i]
      exact sup_le le_sup_right (le_sup_of_le_left (le_sup_left : _ ≤ rankOne _ i))
    have hsub : (posUnipotent D).subgroupOf A ≤ Λ ⊔ U := by
      rw [hΛ, hU, ← Subgroup.subgroupOf_sup hLA hUA]
      exact Subgroup.subgroupOf_mono A hUp
    intro h2
    refine h.not_dvd_index ?_
    rw [← Subgroup.relIndex_mul_index hUplus]
    exact dvd_mul_of_dvd_left (h2.trans (Subgroup.index_dvd_of_le hsub)) _
  have hodd : Odd ((Subgroup.pi Set.univ (fun _ : Fin 1 => S)).relIndex
      (MonoidHom.pi fun _ : Fin 1 => QuotientGroup.mk' U).range) := by
    have hrange : (MonoidHom.pi fun _ : Fin 1 => QuotientGroup.mk' U).range = ⊤ := by
      rw [eq_top_iff]
      rintro g -
      choose x hx using fun j => QuotientGroup.mk'_surjective U (g j)
      exact ⟨x 0, funext fun j => by
        rw [MonoidHom.pi_apply, Fin.fin_one_eq_zero j]
        exact hx 0⟩
    have hev : Function.Surjective (Pi.evalMonoidHom (fun _ : Fin 1 => ↥A ⧸ U) 0) :=
      fun y => ⟨fun _ => y, rfl⟩
    have hpi : Subgroup.pi Set.univ (fun _ : Fin 1 => S) =
        S.comap (Pi.evalMonoidHom (fun _ : Fin 1 => ↥A ⧸ U) 0) := by
      ext g
      simp only [Subgroup.mem_pi, Subgroup.mem_comap, Pi.evalMonoidHom_apply, Set.mem_univ,
        true_implies]
      exact Fin.forall_fin_one
    have hidx : S.index = (Λ ⊔ U).index := by
      have hmap : S.comap (QuotientGroup.mk' U) = Λ ⊔ U := by
        rw [Subgroup.comap_map_eq, QuotientGroup.ker_mk']
      rw [← hmap]
      exact (Subgroup.index_comap_of_surjective _ (QuotientGroup.mk'_surjective U)).symm
    rw [hrange, Subgroup.relIndex_top_right, hpi, Subgroup.index_comap_of_surjective _ hev, hidx]
    exact Nat.odd_iff.mpr (Nat.two_dvd_ne_zero.mp hoddLU)
  have hρo : Odd (Nat.card π.ker) := by
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    by_contra hev
    rw [Nat.not_odd_iff_even, even_iff_two_dvd] at hev
    obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card' (G := ↥π.ker) 2 hev
    refine h.odd.not_two_dvd_nat (hg ▸ orderOf_dvd_of_pow_eq_one ?_)
    exact Subtype.ext (by simpa using h.ker_pow (g : K) g.2)
  refine leviInnAtW_of_levi_dataP (OddPrime.ne_two p) hPL hZL π h.surj
    (fun z hz => h.ker_central z hz) hρo A rfl
    (G := fun _ : Fin 1 => ↥A ⧸ U) (fun _ => S) (fun _ => innerActOn S)
    (MonoidHom.pi fun _ => QuotientGroup.mk' U) (isPGroup_ker_oneBlock U hU2)
    (pi_le_range_oneBlock U Λ) (commutator_range_oneBlock_le U Λ hc) hodd
    (fun _ => Or.inr (Or.inl ⟨hqS, by rw [hZS, Subgroup.card_bot]; exact odd_one⟩))
    (fun x j => ?_) (fun j _ => blockOK_innerActOnP p S) (fun j E hE _ _ x hπx hβx => ?_)
    (fun j hj => absurd hqS hj) hrk
  · exact innerActOn_oneNode h hBA hI hT x
  · obtain ⟨e', he', he'x⟩ := hβx
    have h1 : QuotientGroup.mk' U x = e' := by
      have := congrFun he'x j
      simpa [MonoidHom.pi_apply] using this.symm
    have hxZ : (x : K) ∈ Subgroup.center K := h.ker_central _ hπx
    have hx_comm : ∀ y : ↥A, x * y = y * x := fun y =>
      Subtype.ext ((Subgroup.mem_center_iff.1 hxZ (y : K)).symm)
    have hcent : (⟨e', hE he'⟩ : ↥S) ∈ Subgroup.center ↥S := by
      rw [Subgroup.mem_center_iff]
      rintro ⟨s, y, -, rfl⟩
      apply Subtype.ext
      show QuotientGroup.mk' U y * e' = e' * QuotientGroup.mk' U y
      rw [← h1, ← map_mul, ← map_mul, hx_comm y]
    rw [hZS, Subgroup.mem_bot] at hcent
    have hmk : QuotientGroup.mk' U x = 1 := by rw [h1]; exact congrArg Subtype.val hcent
    have hxU : (x : K) ∈ posUnipotentExcept D i :=
      Subgroup.mem_subgroupOf.1 ((QuotientGroup.eq_one_iff (N := U) x).1 hmk)
    obtain ⟨r, hr⟩ := isPGroup_posUnipotentExcept h i ⟨(x : K), hxU⟩
    have hr' : (x : K) ^ (2 ^ r) = 1 := by simpa using congrArg Subtype.val hr
    have hM : (x : K) ^ M = 1 := h.ker_pow _ hπx
    have hcop : Nat.Coprime (2 ^ r) M := Nat.Coprime.pow_left r (Nat.coprime_two_left.2 h.odd)
    have hx1 : (x : K) = 1 := orderOf_eq_one_iff.1 (Nat.eq_one_of_dvd_coprimes hcop
      (orderOf_dvd_of_pow_eq_one hr') (orderOf_dvd_of_pow_eq_one hM))
    exact Subtype.ext hx1

end LeviOneNode

theorem leviInnOnPW_g2 (p : ℕ) [OddPrime p]
    (hGA : GriessAllModelsStatement) : LeviInnOnPW p (IsLieOf IdxG2) := by
  intro Y _ _ L P hCP hG hLn _ _ hrk
  haveI := hLn
  obtain ⟨f, hf, ⟨e⟩⟩ := exists_mulEquiv_g2 hGA hCP hG
  obtain ⟨T, hNT, hne, htop⟩ := exists_sylow_le_subgroupOf_of_compParab hCP
  obtain ⟨π', hQ, hBA, i, hI⟩ := exists_single_node_g2 e T hNT hne htop
  haveI : Finite ↥(adjointGroup .G2 (GaloisField 2 f)) := generated_group_finite .G2 _
  have hF : Nat.card (GaloisField 2 f) = 2 ^ f := GaloisField.card 2 f (by omega)
  have h4 : 4 ≤ Nat.card (GaloisField 2 f) := by
    rw [hF]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
  obtain ⟨eL⟩ := nonempty_sl2_mulEquiv_rankOne_g2 (F := GaloisField 2 f) i
  have : IsSimpleGroup (Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 f)) :=
    sl2_isSimpleGroup h4
  have : IsSimpleGroup ↥(rankOne (g2Datum (GaloisField 2 f)).rootGroup i) :=
    eL.symm.isSimpleGroup
  have hnc : ∃ a b : ↥(rankOne (g2Datum (GaloisField 2 f)).rootGroup i), a * b ≠ b * a :=
    ⟨eL (sl2Upper 1 * sl2Lower 1), eL (sl2Upper 1), fun h =>
      sl2_upper_lower_not_commute (eL.injective (by simpa [map_mul] using h))⟩
  obtain ⟨hqs, hZ, -⟩ := sl2Block_facts h4 eL
  exact leviInnAtW_of_oneNodeP p hCP.parab.1 hCP.odd π' hQ hBA hI
    (rankOne_inf_posUnipotentExcept_eq_bot hQ i hnc)
    (fun k t ht => g2_torus_conj_rankOne_inner i k ht) hqs hZ hrk

theorem fieldIndexOnPW_g2 (p : ℕ) [OddPrime p]
    (hGA : GriessAllModelsStatement) : FieldIndexOnPW p (IsLieOf IdxG2) :=
  fieldIndexOnPW_of_outPNice (fun _ _ _ _ _ _ hC _ => outPNiceP_of_idxG2 p hC)
    (leviInnOnPW_g2 p hGA)

end CFSG.LocalAnalysis.RankThreeTheoremC.FieldIndexW
