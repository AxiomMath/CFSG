module

public import CFSG.LieType.SeitzGeneration.OmegaF2.TransitA1
public import CFSG.LieType.SeitzGeneration.OmegaF2.Basic

public section

namespace CFSG.LieType.SeitzGeneration.OmegaF2

open Matrix QuadraticMap CFSG.ClassicalGroups.Orthogonal
  CFSG.RankThree.PartOne.KCOrthogonalSubfield
  CFSG.LieType.SeitzGeneration.RootPairOrth

variable {K : Type} [Field K] {d : ℕ} {Q : QuadraticForm K (Fin d → K)} {k : Subfield K}
  {Q₀ : QuadraticForm k (Fin d → k)} (S : HypCoord Q)

private lemma Q_sub_smul_expand (v e : Fin d → K) (c : K) :
    Q (v - c • e) = Q v - c * polar Q v e + c * c * Q e := by
  have h1 : v - c • e = v + (-c) • e := by rw [neg_smul, sub_eq_add_neg]
  rw [h1, QuadraticMap.map_add (⇑Q) v ((-c) • e), QuadraticMap.map_smul,
    QuadraticMap.polar_smul_right]
  simp only [smul_eq_mul]
  ring

private lemma isRat_smul_of_mem {c : K} (hc : c ∈ k) {v : Fin d → K} (hv : IsRat k v) :
    IsRat k (c • v) := fun i => k.mul_mem hc (hv i)

private lemma polar_single_single_eq_zero {a : Fin d} (ha : a ∈ S.hyp) {c : Fin d}
    (hc : c ≠ S.star a) : polar Q (Pi.single a 1 : Fin d → K) (Pi.single c 1) = 0 := by
  rw [S.polar_single a ha, Pi.single_apply, if_neg (fun h => hc h.symm)]

private lemma ne_star_of_ne_star {a b : Fin d} (hb : b ∈ S.hyp) (h : b ≠ S.star a) :
    a ≠ S.star b :=
  fun h' => h (by rw [h', S.star_star b hb])

theorem exists_move_vec (hk : Nat.card k = 2) (hext : IsExtension k Q₀ Q)
    (htail : TailAnisotropic S) {x : Fin d → K} (hx : IsRat k x) (hQx : Q x = 0) (hx0 : x ≠ 0) :
    ∃ h ∈ ratEichlerGroup Q k, ∃ a ∈ S.hyp, h x = Pi.single a 1 := by
  obtain ⟨a, ha, hxa0⟩ : ∃ a ∈ S.hyp, x a ≠ 0 := by
    by_contra hcon
    push_neg at hcon
    exact hx0 (htail x (fun c hc => hcon c hc) hQx)
  have hxa1 : x a = 1 := by
    rcases eq_zero_or_eq_one_of_card_two' hk (hx a) with h0 | h1
    · exact absurd h0 hxa0
    · exact h1
  set T : Finset (Fin d) := Finset.univ.filter (fun c => c ≠ a ∧ c ≠ S.star a) with hTdef
  have hmemT : ∀ c, c ≠ a → c ≠ S.star a → c ∈ T := by
    intro c hca hcs
    rw [hTdef, Finset.mem_filter]
    exact ⟨Finset.mem_univ c, hca, hcs⟩
  have hT : ∀ c ∈ T, c ≠ a ∧ c ≠ S.star a := by
    intro c hc
    rw [hTdef, Finset.mem_filter] at hc
    exact hc.2
  have hu : polar Q (0 : Fin d → K) (Pi.single (S.star a) 1) = 0 ∧
      ∀ c ∈ T, polar Q (0 : Fin d → K) (Pi.single c 1) = 0 :=
    ⟨by simp [QuadraticMap.polar_zero_left], fun _ _ => by simp [QuadraticMap.polar_zero_left]⟩
  obtain ⟨h, hh, _, hzero, hpiv, _⟩ :=
    exists_clear_fix S hext ha T hT 0 hu x hx hxa1
  have hQh : Q (h x) = 0 := (map_of_mem (ratEichlerGroup_le_orthogonalGroup hh) x).trans hQx
  have hsupp : ∀ c, c ≠ a → c ≠ S.star a → (h x) c = 0 := fun c hca hcs =>
    hzero c (hmemT c hca hcs)
  exact ⟨h, hh, a, ha, eq_single_of_support_pair S ha hQh hsupp hpiv⟩

theorem exists_move_perp (hk : Nat.card k = 2) (hext : IsExtension k Q₀ Q)
    (htail : TailAnisotropic S) {a : Fin d} (ha : a ∈ S.hyp) {y : Fin d → K} (hy : IsRat k y)
    (hQy : Q y = 0) (hperp : y (S.star a) = 0)
    (hind : ¬ ∃ c : K, y = c • (Pi.single a 1 : Fin d → K)) :
    ∃ h ∈ ratEichlerGroup Q k, h (Pi.single a 1) = Pi.single a 1 ∧
      ∃ b ∈ S.hyp, b ≠ a ∧ b ≠ S.star a ∧ ∃ ε : K, ε ∈ k ∧
        h y = (Pi.single b 1 : Fin d → K) + ε • (Pi.single a 1 : Fin d → K) := by
  obtain ⟨y', hy'def⟩ : ∃ y' : Fin d → K, y' = y - (y a) • (Pi.single a 1 : Fin d → K) :=
    ⟨_, rfl⟩
  have hy'rat : IsRat k y' := by
    rw [hy'def]
    exact IsRat.sub hy (isRat_smul_of_mem (hy a) (isRat_single k a))
  have hsa0 : (Pi.single a 1 : Fin d → K) (S.star a) = 0 := by
    rw [Pi.single_apply, if_neg (S.star_ne a ha)]
  have hpy : polar Q y (Pi.single a 1 : Fin d → K) = 0 := by
    rw [QuadraticMap.polar_comm, S.polar_single a ha, hperp]
  have hQy' : Q y' = 0 := by
    rw [hy'def, Q_sub_smul_expand, hpy, S.Q_single a ha, hQy]
    ring
  have hy'a : y' a = 0 := by
    rw [hy'def]
    simp
  have hy'sa : y' (S.star a) = 0 := by
    rw [hy'def]
    simp [hperp, hsa0]
  have hex : ∃ b ∈ S.hyp, b ≠ a ∧ b ≠ S.star a ∧ y' b ≠ 0 := by
    by_contra hcon
    push_neg at hcon
    have hy'tail : ∀ c ∈ S.hyp, y' c = 0 := by
      intro c hc
      by_cases hca : c = a
      · rw [hca]
        exact hy'a
      · by_cases hcs : c = S.star a
        · rw [hcs]
          exact hy'sa
        · exact hcon c hc hca hcs
    have hy'0 : y' = 0 := htail y' hy'tail hQy'
    have h2 : y - (y a) • (Pi.single a 1 : Fin d → K) = 0 := by
      rw [← hy'def]
      exact hy'0
    apply hind
    exact ⟨y a, sub_eq_zero.mp h2⟩
  obtain ⟨b, hb, hba, hbs, hy'b0⟩ := hex
  have hy'b1 : y' b = 1 := by
    rcases eq_zero_or_eq_one_of_card_two' hk (hy'rat b) with h0 | h1
    · exact absurd h0 hy'b0
    · exact h1
  have hsb : S.star b ≠ S.star a := fun h =>
    hba (by rw [← S.star_star b hb, h, S.star_star a ha])
  obtain ⟨T, hTdef⟩ : ∃ T : Finset (Fin d), T = Finset.univ.filter
      (fun c => c ≠ a ∧ c ≠ S.star a ∧ c ≠ b ∧ c ≠ S.star b) := ⟨_, rfl⟩
  have hmemT : ∀ c, c ≠ a → c ≠ S.star a → c ≠ b → c ≠ S.star b → c ∈ T := by
    intro c h1 h2 h3 h4
    rw [hTdef, Finset.mem_filter]
    exact ⟨Finset.mem_univ c, h1, h2, h3, h4⟩
  have hTa : ∀ c ∈ T, c ≠ a ∧ c ≠ S.star a := fun c hc => by
    rw [hTdef, Finset.mem_filter] at hc
    exact ⟨hc.2.1, hc.2.2.1⟩
  have hT : ∀ c ∈ T, c ≠ b ∧ c ≠ S.star b := fun c hc => by
    rw [hTdef, Finset.mem_filter] at hc
    exact ⟨hc.2.2.2.1, hc.2.2.2.2⟩
  have hu : polar Q (Pi.single a 1 : Fin d → K) (Pi.single (S.star b) 1) = 0 ∧
      ∀ c ∈ T, polar Q (Pi.single a 1 : Fin d → K) (Pi.single c 1) = 0 :=
    ⟨polar_single_single_eq_zero S ha hsb,
      fun c hc => polar_single_single_eq_zero S ha (hTa c hc).2⟩
  obtain ⟨h, hh, hfix, hzero, hpiv, hrest⟩ :=
    exists_clear_fix S hext hb T hT (Pi.single a 1 : Fin d → K) hu y' hy'rat hy'b1
  have hQh : Q (h y') = 0 := (map_of_mem (ratEichlerGroup_le_orthogonalGroup hh) y').trans hQy'
  have hsupp : ∀ c, c ≠ b → c ≠ S.star b → (h y') c = 0 := by
    intro c hcb hcsb
    by_cases hca : c = a
    · rw [hca, hrest a (fun hm => (hTa a hm).1 rfl) (ne_star_of_ne_star S hb hbs), hy'a]
    · by_cases hcsa : c = S.star a
      · rw [hcsa, hrest (S.star a) (fun hm => (hTa _ hm).2 rfl) (fun h => hsb h.symm), hy'sa]
      · exact hzero c (hmemT c hca hcsa hcb hcsb)
  have hsingle : h y' = (Pi.single b 1 : Fin d → K) :=
    eq_single_of_support_pair S hb hQh hsupp hpiv
  have hy_decomp : y = y' + (y a) • (Pi.single a 1 : Fin d → K) := by
    rw [hy'def, sub_add_cancel]
  have hhy : h y = h y' + (y a) • h (Pi.single a 1 : Fin d → K) := by
    rw [← map_smul, ← map_add, ← hy_decomp]
  refine ⟨h, hh, hfix, b, hb, hba, hbs, y a, hy a, ?_⟩
  rw [hhy, hsingle, hfix]

theorem exists_move_plane (hk : Nat.card k = 2) (hext : IsExtension k Q₀ Q)
    (htail : TailAnisotropic S) {x y : Fin d → K} (hx : IsRat k x) (hy : IsRat k y)
    (hQx : Q x = 0) (hQy : Q y = 0) (hxy : polar Q x y = 0) (hind : LinearIndependent K ![x, y]) :
    ∃ h ∈ ratEichlerGroup Q k, ∃ a ∈ S.hyp, ∃ b ∈ S.hyp, b ≠ a ∧ b ≠ S.star a ∧
      h x = Pi.single a 1 ∧ ∃ ε : K, ε ∈ k ∧
        h y = (Pi.single b 1 : Fin d → K) + ε • (Pi.single a 1 : Fin d → K) := by
  have hpair := LinearIndependent.pair_iff.mp hind
  have hx0 : x ≠ 0 := fun h0 => one_ne_zero (hpair 1 0 (by simp [h0])).1
  obtain ⟨h₁, hh₁, a, ha, hx₁⟩ := exists_move_vec S hk hext htail hx hQx hx0
  have hy₁rat : IsRat k (h₁ y) := ratEichlerGroup_isRat hext hh₁ hy
  have hQy₁ : Q (h₁ y) = 0 := (map_of_mem (ratEichlerGroup_le_orthogonalGroup hh₁) y).trans hQy
  have hperp : (h₁ y) (S.star a) = 0 := by
    have e1 := S.polar_single a ha (h₁ y)
    have e2 := polar_map_of_mem (ratEichlerGroup_le_orthogonalGroup hh₁) x y
    rw [hx₁, hxy] at e2
    rw [← e1]
    exact e2
  have hnot : ¬ ∃ c : K, h₁ y = c • (Pi.single a 1 : Fin d → K) := by
    rintro ⟨c, hc⟩
    have hyc : y = c • x := h₁.injective (by rw [map_smul, hx₁]; exact hc)
    have hc0 := (hpair c (-1) (by rw [hyc]; simp)).2
    exact one_ne_zero (neg_eq_zero.mp hc0)
  obtain ⟨h₂, hh₂, hfix₂, b, hb, hba, hbs, ε, hε, hεeq⟩ :=
    exists_move_perp S hk hext htail ha hy₁rat hQy₁ hperp hnot
  refine ⟨h₂ * h₁, mul_mem hh₂ hh₁, a, ha, b, hb, hba, hbs, ?_, ε, hε, ?_⟩
  · show h₂ (h₁ x) = Pi.single a 1
    rw [hx₁, hfix₂]
  · show h₂ (h₁ y) = _
    exact hεeq

end CFSG.LieType.SeitzGeneration.OmegaF2
