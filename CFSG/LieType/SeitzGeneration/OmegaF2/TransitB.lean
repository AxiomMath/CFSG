module

public import CFSG.LieType.SeitzGeneration.OmegaF2.TransitA2
public import CFSG.LieType.SeitzGeneration.OmegaF2.Good
public import CFSG.LieType.SeitzGeneration.RootPairOrthTailCenter

public section

namespace CFSG.LieType.SeitzGeneration.OmegaF2

open Matrix QuadraticMap CFSG.ClassicalGroups.Orthogonal
  CFSG.RankThree.PartOne.KCOrthogonalSubfield
  CFSG.LieType.SeitzGeneration.RootPairOrth

variable {K : Type} [Field K] {d : ℕ} {Q : QuadraticForm K (Fin d → K)} {k : Subfield K}
  {Q₀ : QuadraticForm k (Fin d → k)} (S : HypCoord Q)

theorem generationFromLine_of_hypCoord (hk : Nat.card k = 2) (hext : IsExtension k Q₀ Q)
    (hnd : (polarBilin Q).Nondegenerate) (htail : TailAnisotropic S) :
    GenerationFromLine Q k := by
  intro H hH hrat x y hx hy hQx hQy hxy hind hline
  have hrat' : ratEichlerGroup Q k ≤ H := by
    unfold ratEichlerGroup
    refine (Subgroup.closure_le H).mpr ?_
    rintro E ⟨u, w, hu, hw, hQu, hp, rfl⟩
    exact hrat u w hu hw hQu hp
  obtain ⟨h, hh, a, ha, b, hb, hba, hbs, hxa, ε, hε, hyb⟩ :=
    exists_move_plane S hk hext htail hx hy hQx hQy hxy hind
  have hhH : h ∈ H := hrat' hh
  have hhO : h ∈ TauCeti.QuadraticMap.orthogonalGroup Q := ratEichlerGroup_le_orthogonalGroup hh
  have hQa : Q (Pi.single a 1 : Fin d → K) = 0 := S.Q_single a ha
  have hline' : ∀ t : K,
      eichler Q (Pi.single a 1 : Fin d → K) (t • (Pi.single b 1 : Fin d → K)) ∈ H := by
    intro t
    have hc : eichler Q (h x) (h (t • y)) ∈ H := by
      have hm := H.mul_mem (H.mul_mem hhH (hline t)) (H.inv_mem hhH)
      rwa [eichler_conj hhO] at hm
    rw [hxa, map_smul, hyb, smul_add, smul_smul, eichler_add_smul_self hQa] at hc
    exact hc
  have hne : (Pi.single a 1 : Fin d → K) ≠ Pi.single b 1 := by
    intro heq
    have h1 := congrFun heq b
    by_cases hab : b = a
    · exact hba hab
    · rw [Pi.single_apply, if_neg hab, Pi.single_eq_same] at h1
      exact zero_ne_one h1
  exact S.elementaryGroup_le_of_basic_line_T H hnd hH hrat (IsBasicT.single ha hb hbs) hne hline'

private theorem exists_fresh_hyp (S : HypCoord Q) (a b : Fin d) :
    ∃ j ∈ S.hyp, j ≠ a ∧ j ≠ S.star a ∧ j ≠ b ∧ j ≠ S.star b := by
  have h4 : ({a, S.star a, b, S.star b} : Finset (Fin d)).card ≤ 4 := Finset.card_le_four
  have hcard : ({a, S.star a, b, S.star b} : Finset (Fin d)).card < S.hyp.card := by
    have := S.card_hyp
    omega
  obtain ⟨j, hjh, hjs⟩ := Finset.exists_mem_notMem_of_card_lt_card hcard
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hjs
  exact ⟨j, hjh, hjs.1, hjs.2.1, hjs.2.2.1, hjs.2.2.2⟩

private theorem tail_single_mem (S : HypCoord Q) {a b c j : Fin d} (ha : a ∈ S.hyp)
    (hb : b ∈ S.hyp) (hj : j ∈ S.hyp) (hja : j ≠ a) (hjsa : j ≠ S.star a) (hjb : j ≠ b)
    (hjsb : j ≠ S.star b) (hc : c ∉ S.hyp) (hQc : Q (Pi.single c 1 : Fin d → K) = 1) :
    (Pi.single c 1 : Fin d → K) ∈ AddSubgroup.closure {z : Fin d → K | IsRat k z ∧ Q z = 0 ∧
      z (S.star a) = 0 ∧ z (S.star b) = 0} := by
  have hjs := S.star_mem j hj
  have hsj_c : S.star j ≠ c := fun h => hc (h ▸ hjs)
  have hj_c : j ≠ c := fun h => hc (h ▸ hj)
  have hsa_j : S.star a ≠ j := Ne.symm hjsa
  have hsb_j : S.star b ≠ j := Ne.symm hjsb
  have hsa_c : S.star a ≠ c := fun h => hc (h ▸ S.star_mem a ha)
  have hsb_c : S.star b ≠ c := fun h => hc (h ▸ S.star_mem b hb)
  have hsa_sj : S.star a ≠ S.star j := fun h => hja (S.star_injective ha hj h).symm
  have hsb_sj : S.star b ≠ S.star j := fun h => hjb (S.star_injective hb hj h).symm
  have hwa : (Pi.single c 1 : Fin d → K) (S.star j) = 0 := by simp [Pi.single_apply, hsj_c]
  have hwj : (Pi.single c 1 : Fin d → K) j = 0 := by simp [Pi.single_apply, hj_c]
  have hzQ := S.Q_tail hj hwa hwj
  rw [hQc, one_smul] at hzQ
  have hz_rat : IsRat k (Pi.single j 1 + Pi.single c 1 - Pi.single (S.star j) 1 : Fin d → K) :=
    ((isRat_single k j).add (isRat_single k c)).sub (isRat_single k (S.star j))
  have hz_a : (Pi.single j 1 + Pi.single c 1 - Pi.single (S.star j) 1 : Fin d → K) (S.star a) = 0 := by
    simp [Pi.single_apply, hsa_j, hsa_c, hsa_sj]
  have hz_b : (Pi.single j 1 + Pi.single c 1 - Pi.single (S.star j) 1 : Fin d → K) (S.star b) = 0 := by
    simp [Pi.single_apply, hsb_j, hsb_c, hsb_sj]
  have hz_mem := AddSubgroup.subset_closure
    (show (Pi.single j 1 + Pi.single c 1 - Pi.single (S.star j) 1 : Fin d → K) ∈
      {z : Fin d → K | IsRat k z ∧ Q z = 0 ∧ z (S.star a) = 0 ∧ z (S.star b) = 0} from
      ⟨hz_rat, hzQ, hz_a, hz_b⟩)
  have hbj_mem := AddSubgroup.subset_closure
    (show (Pi.single j 1 : Fin d → K) ∈
      {z : Fin d → K | IsRat k z ∧ Q z = 0 ∧ z (S.star a) = 0 ∧ z (S.star b) = 0} from
      ⟨isRat_single k j, S.Q_single j hj, by simp [Pi.single_apply, hsa_j],
        by simp [Pi.single_apply, hsb_j]⟩)
  have hbs_mem := AddSubgroup.subset_closure
    (show (Pi.single (S.star j) 1 : Fin d → K) ∈
      {z : Fin d → K | IsRat k z ∧ Q z = 0 ∧ z (S.star a) = 0 ∧ z (S.star b) = 0} from
      ⟨isRat_single k (S.star j), S.Q_single _ hjs, by simp [Pi.single_apply, hsa_sj],
        by simp [Pi.single_apply, hsb_sj]⟩)
  have key : (Pi.single j 1 + Pi.single c 1 - Pi.single (S.star j) 1 : Fin d → K)
      + -(Pi.single j 1 : Fin d → K) + Pi.single (S.star j) 1 = Pi.single c 1 := by
    abel
  have hmem := add_mem (add_mem hz_mem (neg_mem hbj_mem)) hbs_mem
  rwa [key] at hmem

theorem coord_closure_perp (hk : Nat.card k = 2) (hext : IsExtension k Q₀ Q)
    {a b : Fin d} (ha : a ∈ S.hyp) (hb : b ∈ S.hyp) (hba : b ≠ a) (hbs : b ≠ S.star a)
    {v : Fin d → K} (hv : IsRat k v) (hva : v (S.star a) = 0) (hvb : v (S.star b) = 0) :
    v ∈ AddSubgroup.closure {z : Fin d → K | IsRat k z ∧ Q z = 0 ∧ z (S.star a) = 0 ∧
      z (S.star b) = 0} := by
  have hcoord : ∀ c : Fin d, c ≠ S.star a → c ≠ S.star b →
      (Pi.single c 1 : Fin d → K) ∈ AddSubgroup.closure {z : Fin d → K | IsRat k z ∧ Q z = 0 ∧
        z (S.star a) = 0 ∧ z (S.star b) = 0} := by
    intro c hca hcb
    have hz0a : (Pi.single c 1 : Fin d → K) (S.star a) = 0 := by
      simp [Pi.single_apply, Ne.symm hca]
    have hz0b : (Pi.single c 1 : Fin d → K) (S.star b) = 0 := by
      simp [Pi.single_apply, Ne.symm hcb]
    by_cases hc : c ∈ S.hyp
    · exact AddSubgroup.subset_closure ⟨isRat_single k c, S.Q_single c hc, hz0a, hz0b⟩
    · by_cases hQc : Q (Pi.single c 1 : Fin d → K) = 0
      · exact AddSubgroup.subset_closure ⟨isRat_single k c, hQc, hz0a, hz0b⟩
      · have hQk := Q_isRat_mem hext (isRat_single k c)
        have hQ1 := (eq_zero_or_eq_one_of_card_two' hk hQk).resolve_left hQc
        obtain ⟨j, hj, hja, hjsa, hjb, hjsb⟩ := exists_fresh_hyp S a b
        exact tail_single_mem S ha hb hj hja hjsa hjb hjsb hc hQ1
  have hdec : v = ∑ c : Fin d, v c • (Pi.single c 1 : Fin d → K) := by
    funext i
    simp [Finset.sum_apply, Pi.single_apply]
  rw [hdec]
  apply AddSubgroup.sum_mem
  intro c _
  rcases eq_zero_or_eq_one_of_card_two' hk (hv c) with h0 | h1
  · rw [h0, zero_smul]
    exact zero_mem _
  · rw [h1, one_smul]
    apply hcoord
    · intro hc
      have h0 : v c = 0 := by rw [hc]; exact hva
      rw [h1] at h0
      exact one_ne_zero h0
    · intro hc
      have h0 : v c = 0 := by rw [hc]; exact hvb
      rw [h1] at h0
      exact one_ne_zero h0

theorem rational_perp_mem_closure (hk : Nat.card k = 2) (hext : IsExtension k Q₀ Q)
    (htail : TailAnisotropic S) {x y : Fin d → K} (hx : IsRat k x) (hy : IsRat k y)
    (hQx : Q x = 0) (hQy : Q y = 0) (hxy : polar Q x y = 0) (hind : LinearIndependent K ![x, y])
    {v : Fin d → K} (hv : IsRat k v) (hvx : polar Q v x = 0) (hvy : polar Q v y = 0) :
    v ∈ AddSubgroup.closure {z : Fin d → K | IsRat k z ∧ Q z = 0 ∧ polar Q z x = 0 ∧
      polar Q z y = 0} := by
  obtain ⟨h, hh, a, ha, b, hb, hba, hbs, hxa, ε, hε, hyb⟩ :=
    exists_move_plane S hk hext htail hx hy hQx hQy hxy hind
  have hhO : h ∈ TauCeti.QuadraticMap.orthogonalGroup Q := ratEichlerGroup_le_orthogonalGroup hh
  have hinO : h⁻¹ ∈ TauCeti.QuadraticMap.orthogonalGroup Q :=
    (TauCeti.QuadraticMap.orthogonalGroup Q).inv_mem hhO
  have hhh : ∀ u, h (h⁻¹ u) = u := fun u => by
    show (h * h⁻¹) u = u
    rw [mul_inv_cancel]
    rfl
  have hhh' : ∀ u, h⁻¹ (h u) = u := fun u => by
    show (h⁻¹ * h) u = u
    rw [inv_mul_cancel]
    rfl
  have hpx : polar Q (h v) (Pi.single a 1) = 0 := by
    rw [← hxa, polar_map_of_mem hhO]
    exact hvx
  have hpy : polar Q (h v) (Pi.single b 1 + ε • Pi.single a 1) = 0 := by
    rw [← hyb, polar_map_of_mem hhO]
    exact hvy
  have hpb : polar Q (h v) (Pi.single b 1) = 0 := by
    rw [polar_add_right, polar_smul_right, hpx, smul_zero, add_zero] at hpy
    exact hpy
  have hva' : (h v) (S.star a) = 0 := by
    have := S.polar_single_right ha (h v)
    rw [hpx] at this
    exact this.symm
  have hvb' : (h v) (S.star b) = 0 := by
    have := S.polar_single_right hb (h v)
    rw [hpb] at this
    exact this.symm
  have hv' : IsRat k (h v) := ratEichlerGroup_isRat hext hh hv
  have hcp := coord_closure_perp S hk hext ha hb hba hbs hv' hva' hvb'
  have hW : ∀ z ∈ {z : Fin d → K | IsRat k z ∧ Q z = 0 ∧ z (S.star a) = 0 ∧ z (S.star b) = 0},
      h⁻¹ z ∈ {z : Fin d → K | IsRat k z ∧ Q z = 0 ∧ polar Q z x = 0 ∧ polar Q z y = 0} := by
    rintro z ⟨hzr, hzQ, hza, hzb⟩
    have hpx' : polar Q (h⁻¹ z) x = 0 := by
      rw [← polar_map_of_mem hhO (h⁻¹ z) x, hhh z, hxa, S.polar_single_right ha, hza]
    have hpy' : polar Q (h⁻¹ z) y = 0 := by
      rw [← polar_map_of_mem hhO (h⁻¹ z) y, hhh z, hyb, polar_add_right, polar_smul_right,
        S.polar_single_right hb, S.polar_single_right ha, hzb, hza, smul_zero, add_zero]
    exact ⟨ratEichlerGroup_isRat hext ((ratEichlerGroup Q k).inv_mem hh) hzr,
      (map_of_mem hinO z).trans hzQ, hpx', hpy'⟩
  have hcomap : AddSubgroup.closure {z : Fin d → K | IsRat k z ∧ Q z = 0 ∧ z (S.star a) = 0 ∧
      z (S.star b) = 0} ≤ (AddSubgroup.closure {z : Fin d → K | IsRat k z ∧ Q z = 0 ∧
      polar Q z x = 0 ∧ polar Q z y = 0}).comap
        (h⁻¹ : (Fin d → K) ≃ₗ[K] (Fin d → K)).toLinearMap.toAddMonoidHom := by
    rw [AddSubgroup.closure_le]
    intro z hz
    rw [SetLike.mem_coe, AddSubgroup.mem_comap]
    exact AddSubgroup.subset_closure (hW z hz)
  have hfin : (h⁻¹ : (Fin d → K) ≃ₗ[K] (Fin d → K)) (h v) ∈ AddSubgroup.closure
      {z : Fin d → K | IsRat k z ∧ Q z = 0 ∧ polar Q z x = 0 ∧ polar Q z y = 0} :=
    hcomap hcp
  rwa [hhh'] at hfin

end CFSG.LieType.SeitzGeneration.OmegaF2
