module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.S3AmalgamBound.RankTwoCoverBig
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.S3AmalgamBound.RankTwoCoverE9

public section

namespace CFSG.AGLEmbeddingD2.Tits.S3AmalgamBound

open CFSG.AGLEmbedding.ParabHub CFSG.AGLEmbedding.ParabPrime CFSG.LieType.Universal
  CFSG.LieType.CurtisTits CFSG.LieType.Steinberg CFSG.QuasithinUnique CFSG.Open
  CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData
  CFSG.AGLEmbeddingD2.McLaughlin.TightPairAndPureRank
  CFSG.LocalAnalysis.RankThreeTheoremC

structure OrthSep {K Y : Type*} [Group K] [Group Y] (D : UniversalRootDatum K) (π : K →* Y)
    (i j : Fin D.rank) : Prop where
  cartan : D.cartan i j = 0
  ne : i ≠ j
  elts : ∃ xi ∈ D.rootGroup (Pi.single i 1), ∃ yi ∈ D.rootGroup (-Pi.single i 1),
    ∃ xj ∈ D.rootGroup (Pi.single j 1), ∃ yj ∈ D.rootGroup (-Pi.single j 1),
      orderOf (π (xi * yi)) = 3 ∧ orderOf (π (xj * yj)) = 3 ∧
        π (xj * yj) ∉ Subgroup.zpowers (π (xi * yi)) ∧
        ∀ φ : Y ≃* Y, φ (π (xi * yi)) ≠ π (xi * yi) * π (xj * yj)

variable {W : Type} [Group W] [Finite W] {K : Type} [Group K] [Finite K]
  {D : UniversalRootDatum K} {n : Fin D.rank → K} {H : Fin D.rank → Subgroup K} {M : ℕ}

theorem false_of_orthSep {L A : Subgroup W} (hL : IsComponentOf L ⊤)
    (htrans : ∀ E : Subgroup W, E ≤ A ⊓ L → IsElemAbelian 3 E → Nat.card E = 9 →
      TransitiveOnNonidentity (Subgroup.normalizer (E : Set W)) E)
    {π : K →* ↥L ⧸ Subgroup.center ↥L} (hπ : BorelQuotient D n H π M)
    (hsq : ∀ γ ∈ D.roots, ∀ x ∈ D.rootGroup γ, x ^ 2 = 1) {i j : Fin D.rank}
    (hsep : OrthSep D π i j)
    (hi : (rankOne D.rootGroup i).map π ≤ (A.subgroupOf L).map (QuotientGroup.mk' (Subgroup.center ↥L)))
    (hj : (rankOne D.rootGroup j).map π ≤ (A.subgroupOf L).map (QuotientGroup.mk' (Subgroup.center ↥L))) :
    False := by
  obtain ⟨xi, hxi, yi, hyi, xj, hxj, yj, hyj, hoi, hoj, hnot, hφ⟩ := hsep.elts
  have hroot : ∀ k : Fin D.rank, (Pi.single k 1 : Fin D.rank → ℤ) ∈ D.roots ∧
      (-Pi.single k 1 : Fin D.rank → ℤ) ∈ D.roots := fun k =>
    ⟨(RootSystem.ofCartan D.isFiniteType D.divisible).single_mem k,
      (RootSystem.ofCartan D.isFiniteType D.divisible).neg_mem _
        ((RootSystem.ofCartan D.isFiniteType D.divisible).single_mem k)⟩
  have hLi : ∀ k : Fin D.rank, ∀ x ∈ D.rootGroup (Pi.single k 1), x ∈ rankOne D.rootGroup k :=
    fun k x hx => le_sup_left (b := D.rootGroup (-Pi.single k 1)) hx
  have hLi' : ∀ k : Fin D.rank, ∀ x ∈ D.rootGroup (-Pi.single k 1), x ∈ rankOne D.rootGroup k :=
    fun k x hx => le_sup_right (a := D.rootGroup (Pi.single k 1)) hx
  set q := QuotientGroup.mk' (Subgroup.center ↥L) with hq
  obtain ⟨ai, hai, haiq⟩ := hi ⟨xi, hLi i xi hxi, rfl⟩
  obtain ⟨bi, hbi, hbiq⟩ := hi ⟨yi, hLi' i yi hyi, rfl⟩
  obtain ⟨aj, haj, hajq⟩ := hj ⟨xj, hLi j xj hxj, rfl⟩
  obtain ⟨bj, hbj, hbjq⟩ := hj ⟨yj, hLi' j yj hyj, rfl⟩
  have hsq' : ∀ γ ∈ D.roots, ∀ x ∈ D.rootGroup γ, π x ^ 2 = 1 := fun γ hγ x hx => by
    rw [← map_pow, hsq γ hγ x hx, map_one]
  have hcomm : ∀ x ∈ rankOne D.rootGroup i, ∀ y ∈ rankOne D.rootGroup j, π x * π y = π y * π x :=
    fun x hx y hy => by
      rw [← map_mul, ← map_mul,
        commutes_rankOne_of_cartan_eq_zero hπ.extras hsep.ne hsep.cartan x hx y hy]
  have hxyi : xi * yi ∈ rankOne D.rootGroup i := Subgroup.mul_mem _ (hLi i xi hxi) (hLi' i yi hyi)
  have hxyj : xj * yj ∈ rankOne D.rootGroup j := Subgroup.mul_mem _ (hLi j xj hxj) (hLi' j yj hyj)
  have hui : q (ai * bi) = π (xi * yi) := by rw [map_mul, haiq, hbiq, map_mul]
  have huj : q (aj * bj) = π (xj * yj) := by rw [map_mul, hajq, hbjq, map_mul]
  obtain ⟨ψ, hψ⟩ := exists_aut_of_liftable_pair (L := L) (A := A) hL htrans
    (ai := ai) (bi := bi) (aj := aj) (bj := bj)
    (Subgroup.mem_subgroupOf.1 hai) (Subgroup.mem_subgroupOf.1 hbi)
    (Subgroup.mem_subgroupOf.1 haj) (Subgroup.mem_subgroupOf.1 hbj)
    (by rw [haiq]; exact hsq' _ (hroot i).1 xi hxi) (by rw [hbiq]; exact hsq' _ (hroot i).2 yi hyi)
    (by rw [hajq]; exact hsq' _ (hroot j).1 xj hxj) (by rw [hbjq]; exact hsq' _ (hroot j).2 yj hyj)
    (by rw [hui]; exact hoi) (by rw [huj]; exact hoj)
    (by rw [hui, huj]; exact hcomm _ hxyi _ hxyj)
    (by rw [hbjq, hui]; exact (hcomm _ hxyi _ (hLi' j yj hyj)).symm)
    (by rw [hui, huj]; exact hnot)
  exact hφ ψ (by rw [← hui, ← huj, ← map_mul]; exact hψ)

theorem false_of_pair_in_cover {L A : Subgroup W} (hL : IsComponentOf L ⊤)
    (hA : CFSG.HallHigman.IsPSolvable 3 ↥A)
    (htrans : ∀ E : Subgroup W, E ≤ A ⊓ L → IsElemAbelian 3 E → Nat.card E = 9 →
      TransitiveOnNonidentity (Subgroup.normalizer (E : Set W)) E)
    {π : K →* ↥L ⧸ Subgroup.center ↥L} (hπ : BorelQuotient D n H π M)
    (hsq : ∀ γ ∈ D.roots, ∀ x ∈ D.rootGroup γ, x ^ 2 = 1) {i j : Fin D.rank}
    (hi : (rankOne D.rootGroup i).map π ≤ (A.subgroupOf L).map (QuotientGroup.mk' (Subgroup.center ↥L)))
    (hj : (rankOne D.rootGroup j).map π ≤ (A.subgroupOf L).map (QuotientGroup.mk' (Subgroup.center ↥L)))
    (hcase : OrthSep D π i j ∨
      ¬ CFSG.HallHigman.IsPSolvable 3 ↥((rankOne D.rootGroup i ⊔ rankOne D.rootGroup j).map π)) :
    False := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  rcases hcase with hsep | hns
  · exact false_of_orthSep hL htrans hπ hsq hsep hi hj
  · apply hns
    rw [Subgroup.map_sup]
    exact OrdinaryProofs.PSolvableClosure.isPSolvable_of_le
      (isPSolvable_map_subgroupOf L hA) (sup_le hi hj)

theorem false_of_cover_two {L S₀ A₁ A₂ : Subgroup W} (hL : IsComponentOf L ⊤)
    (hS : IsSylowTwoOf S₀ L) (hcov : CoveredByTwo L S₀ A₁ A₂)
    (h1 : CFSG.HallHigman.IsPSolvable 3 ↥A₁) (h2 : CFSG.HallHigman.IsPSolvable 3 ↥A₂)
    (htrans : ∀ E : Subgroup W, (E ≤ A₁ ⊓ L ∨ E ≤ A₂ ⊓ L) → IsElemAbelian 3 E →
      Nat.card E = 9 → TransitiveOnNonidentity (Subgroup.normalizer (E : Set W)) E)
    {π : K →* ↥L ⧸ Subgroup.center ↥L} (h : BorelQuotient D n H π M)
    (hsq : ∀ γ ∈ D.roots, ∀ x ∈ D.rootGroup γ, x ^ 2 = 1)
    (hfam : ∀ {π' : K →* ↥L ⧸ Subgroup.center ↥L}, BorelQuotient D n H π' M →
      ∀ c : Fin D.rank → Bool, ∃ i j, i ≠ j ∧ c i = c j ∧
        (OrthSep D π' i j ∨
          ¬ CFSG.HallHigman.IsPSolvable 3 ↥((rankOne D.rootGroup i ⊔ rankOne D.rootGroup j).map π'))) :
    False := by
  classical
  obtain ⟨π', hπ', hT⟩ := exists_borelQuotient_conj hS h
  have hnode := cover_of_borelQuotient hS hcov hπ' hT
  set q := QuotientGroup.mk' (Subgroup.center ↥L) with hq
  let c : Fin D.rank → Bool := fun i => decide ((rankOne D.rootGroup i).map π' ≤ (A₁.subgroupOf L).map q)
  obtain ⟨i, j, hij, hc, hcase⟩ := hfam hπ' c
  by_cases hi1 : (rankOne D.rootGroup i).map π' ≤ (A₁.subgroupOf L).map q
  · have hj1 : (rankOne D.rootGroup j).map π' ≤ (A₁.subgroupOf L).map q := by
      have : c j = true := by rw [← hc]; simp [c, hi1]
      simpa [c] using this
    exact false_of_pair_in_cover hL h1 (fun E hE => htrans E (Or.inl hE)) hπ' hsq hi1 hj1 hcase
  · have hi2 : (rankOne D.rootGroup i).map π' ≤ (A₂.subgroupOf L).map q :=
      (hnode i).resolve_left hi1
    have hj1 : ¬ (rankOne D.rootGroup j).map π' ≤ (A₁.subgroupOf L).map q := by
      have : c j = false := by rw [← hc]; simp [c, hi1]
      simpa [c] using this
    have hj2 := (hnode j).resolve_left hj1
    exact false_of_pair_in_cover hL h2 (fun E hE => htrans E (Or.inr hE)) hπ' hsq hi2 hj2 hcase

end CFSG.AGLEmbeddingD2.Tits.S3AmalgamBound
