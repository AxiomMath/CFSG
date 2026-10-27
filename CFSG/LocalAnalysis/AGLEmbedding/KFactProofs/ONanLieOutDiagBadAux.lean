module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanLieOutDiagBadDefs
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanParabPrimeQuot
import CFSG.LieType.Steinberg.CentralExt.UnitaryRankOneLast
import CFSG.LieType.Steinberg.CentralExt.SUTwo
import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanParabThreeSU
import CFSG.LieType.Universal.Unitary.Clause0

public section

namespace CFSG.AGLEmbedding.LieOut

open CFSG.AGLEmbedding.ParabHub CFSG.AGLEmbedding.ParabPrime CFSG.Assembly.LowTwoRank
  CFSG.LieType.Universal CFSG.LieType.Universal.Unitary CFSG.LieType.BorelTits
  CFSG.LieType.CurtisTits CFSG.LieType.RootSystem CFSG.LieType.Steinberg

section BN

variable {K : Type*} [Group K] {D : UniversalRootDatum K} {n : Fin D.rank → K}
  {H : Fin D.rank → Subgroup K}

theorem inversionUnipotent_simple_le (hext : SteinbergExtras D n H) (i : Fin D.rank) :
    inversionUnipotent D ((coxeterMatrix D.isFiniteType).toCoxeterSystem.simple i) ≤
      D.rootGroup (Pi.single i 1) := by
  refine iSup₂_le fun γ hγ => ?_
  obtain ⟨hγr, hpos, hneg⟩ := hγ
  by_cases hmem : γ ∈ (RootSystem.ofCartan D.isFiniteType D.divisible).posExcept i
  · exfalso
    have h1 := (RootSystem.ofCartan D.isFiniteType D.divisible).refl_mem_posExcept hmem
    rw [weylAction_simple] at hneg
    have h2 : 0 < ht ((reflection D.cartan i) γ) := h1.1.2
    omega
  · have hγ' : γ = Pi.single i 1 ∨ γ = 2 • Pi.single i 1 := by
      by_contra hc
      rw [not_or] at hc
      refine hmem ⟨⟨hγr, hpos⟩, ?_⟩
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
      exact hc
    rcases hγ' with rfl | rfl
    · exact le_rfl
    · exact hext.two_smul_le _ ((RootSystem.ofCartan D.isFiniteType D.divisible).single_mem i) hγr

theorem mem_cells_of_mem_borel_sup_rankOne
    (hct : IsCTGroupDatum (coxeterMatrix D.isFiniteType).toCoxeterSystem
      (weylAction D.isFiniteType) D.roots D.rootGroup n H)
    (hext : SteinbergExtras D n H) (i : Fin D.rank) {g : K}
    (hg : g ∈ borel D H ⊔ rankOne D.rootGroup i) :
    g ∈ bruhatCell hct 1 ∪
      bruhatCell hct ((coxeterMatrix D.isFiniteType).toCoxeterSystem.simple i) := by
  set Q : Set K := bruhatCell hct 1 ∪
    bruhatCell hct ((coxeterMatrix D.isFiniteType).toCoxeterSystem.simple i) with hQ
  have h1Q : (1 : K) ∈ Q := Or.inl (by rw [bruhatCell_one]; exact one_mem _)
  have hB : ∀ b ∈ borel D H, ∀ q ∈ Q, b * q ∈ Q := by
    intro b hb q hq
    rcases hq with hq | hq
    · exact Or.inl (mul_mem_bruhatCell hct hb hq)
    · exact Or.inr (mul_mem_bruhatCell hct hb hq)
  have hn : ∀ q ∈ Q, n i * q ∈ Q := by
    intro q hq
    rcases hq with hq | hq
    · have := n_mul_mem_bruhatCell hct hext hq i
      rwa [mul_one] at this
    · have := n_mul_mem_bruhatCell hct hext hq i
      rw [CoxeterSystem.simple_mul_simple_self] at this
      exact this.symm
  have hα := (RootSystem.ofCartan D.isFiniteType D.divisible).single_mem i
  have hXB : D.rootGroup (Pi.single i 1) ≤ borel D H := rootGroup_le_borel hα (ht_single_pos i)
  have hL : ∀ l ∈ rankOne D.rootGroup i, ∀ q ∈ Q, l * q ∈ Q := by
    intro l hl q hq
    rcases hext.rankOne_bruhat i l hl with ⟨h, hh, y, hy, rfl⟩ | ⟨y, hy, h, hh, z, hz, rfl⟩
    · exact hB _ (mul_mem (iSup_le_borel (le_iSup H i hh)) (hXB hy)) q hq
    · have h1 := hB (h * z) (mul_mem (iSup_le_borel (le_iSup H i hh)) (hXB hz)) q hq
      have h2 := hn _ h1
      have e : y * n i * h * z * q = y * (n i * (h * z * q)) := by group
      rw [e]
      exact hB y (hXB hy) _ h2
  have key : ∀ g ∈ borel D H ⊔ rankOne D.rootGroup i, ∀ q ∈ Q, g * q ∈ Q ∧ g⁻¹ * q ∈ Q := by
    intro g hg
    rw [Subgroup.sup_eq_closure] at hg
    refine Subgroup.closure_induction (p := fun g _ => ∀ q ∈ Q, g * q ∈ Q ∧ g⁻¹ * q ∈ Q)
      ?_ ?_ ?_ ?_ hg
    · intro x hx q hq
      rcases hx with hx | hx
      · exact ⟨hB x hx q hq, hB x⁻¹ (inv_mem hx) q hq⟩
      · exact ⟨hL x hx q hq, hL x⁻¹ (inv_mem hx) q hq⟩
    · intro q hq
      simpa using hq
    · intro x y _ _ hx hy q hq
      refine ⟨?_, ?_⟩
      · have := (hx _ (hy q hq).1).1
        simpa [mul_assoc] using this
      · have := (hy _ (hx q hq).2).2
        simpa [mul_assoc] using this
    · intro x _ hx q hq
      exact ⟨(hx q hq).2, by simpa using (hx q hq).1⟩
  simpa using (key g hg 1 h1Q).1

theorem card_map_borel_sup_rankOne_le [Finite K] {Y : Type*} [Group Y] [Finite Y]
    (hct : IsCTGroupDatum (coxeterMatrix D.isFiniteType).toCoxeterSystem
      (weylAction D.isFiniteType) D.roots D.rootGroup n H)
    (hext : SteinbergExtras D n H) (π : K →* Y) (i : Fin D.rank) :
    Nat.card ((borel D H ⊔ rankOne D.rootGroup i).map π) ≤
      Nat.card ((borel D H).map π) * (1 + Nat.card (D.rootGroup (Pi.single i 1))) := by
  classical
  let F : ((borel D H).map π) × Option (D.rootGroup (Pi.single i 1)) → Y := fun p =>
    match p.2 with
    | none => (p.1 : Y)
    | some u => (p.1 : Y) * π (n i) * π (u : K)
  have hsub : ((borel D H ⊔ rankOne D.rootGroup i).map π : Set Y) ⊆ Set.range F := by
    rintro _ ⟨g, hg, rfl⟩
    rcases mem_cells_of_mem_borel_sup_rankOne hct hext i hg with hg1 | hg1
    · rw [bruhatCell_one] at hg1
      exact ⟨(⟨π g, g, hg1, rfl⟩, none), rfl⟩
    · obtain ⟨b, hb, u, hu, rfl⟩ := exists_eq_mul_nrep_mul hct hext hg1
      rw [nrep_simple hct i]
      exact ⟨(⟨π b, b, hb, rfl⟩, some ⟨u, inversionUnipotent_simple_le hext i hu⟩),
        by simp [F, map_mul]⟩
  have h1 : Nat.card ((borel D H ⊔ rankOne D.rootGroup i).map π) ≤ Nat.card (Set.range F) :=
    Nat.card_mono (Set.finite_range F) hsub
  have h2 : Nat.card (Set.range F) ≤
      Nat.card (((borel D H).map π) × Option (D.rootGroup (Pi.single i 1))) :=
    Nat.card_le_card_of_surjective _ (Set.rangeFactorization_surjective (f := F))
  rw [Nat.card_prod, Finite.card_option, add_comm] at h2
  exact h1.trans h2

theorem relIndex_map_borel_le [Finite K] {Y : Type*} [Group Y] [Finite Y]
    (hct : IsCTGroupDatum (coxeterMatrix D.isFiniteType).toCoxeterSystem
      (weylAction D.isFiniteType) D.roots D.rootGroup n H)
    (hext : SteinbergExtras D n H) (π : K →* Y) (i : Fin D.rank) :
    ((borel D H).map π).relIndex ((borel D H).map π ⊔ (rankOne D.rootGroup i).map π) ≤
      1 + Nat.card (D.rootGroup (Pi.single i 1)) := by
  rw [← Subgroup.map_sup]
  have hle : (borel D H).map π ≤ (borel D H ⊔ rankOne D.rootGroup i).map π :=
    Subgroup.map_mono le_sup_left
  have h1 := Subgroup.relIndex_mul_card (H := (borel D H).map π)
    (K := (borel D H ⊔ rankOne D.rootGroup i).map π)
  rw [inf_of_le_left hle] at h1
  have h2 := card_map_borel_sup_rankOne_le hct hext π i
  have hpos : 0 < Nat.card ((borel D H).map π) := Nat.card_pos
  rw [← h1, mul_comm (Nat.card ((borel D H).map π))] at h2
  exact Nat.le_of_mul_le_mul_right h2 hpos

theorem not_dvd_card_map_borel_sup_rankOne [Finite K] {Y : Type*} [Group Y] [Finite Y]
    (hct : IsCTGroupDatum (coxeterMatrix D.isFiniteType).toCoxeterSystem
      (weylAction D.isFiniteType) D.roots D.rootGroup n H)
    (hext : SteinbergExtras D n H) (π : K →* Y) (i : Fin D.rank) {r : ℕ} (hr : r.Prime)
    (hrB : ¬ r ∣ Nat.card ((borel D H).map π))
    (hrX : 1 + Nat.card (D.rootGroup (Pi.single i 1)) < r) :
    ¬ r ∣ Nat.card ↥((borel D H).map π ⊔ (rankOne D.rootGroup i).map π) := by
  intro hd
  have hidx := relIndex_map_borel_le hct hext π i
  have hle : (borel D H).map π ≤ (borel D H).map π ⊔ (rankOne D.rootGroup i).map π :=
    le_sup_left
  have h1 := Subgroup.relIndex_mul_card (H := (borel D H).map π)
    (K := (borel D H).map π ⊔ (rankOne D.rootGroup i).map π)
  rw [inf_of_le_left hle] at h1
  rw [← h1] at hd
  have hpos : 0 < Nat.card ↥((borel D H).map π ⊔ (rankOne D.rootGroup i).map π) := Nat.card_pos
  rw [← h1] at hpos
  rcases hr.dvd_mul.1 hd with h | h
  · have hk : 0 < ((borel D H).map π).relIndex
        ((borel D H).map π ⊔ (rankOne D.rootGroup i).map π) :=
      Nat.pos_of_ne_zero fun h0 => by simp [h0] at hpos
    have := Nat.le_of_dvd hk h
    omega
  · exact hrB h

end BN

section Last

variable {Y : Type} [Group Y] {L J : Subgroup Y} {F : Type} [Field F] [Finite F] [CharP F 2]
  {f : ℕ} {hF : Nat.card F = (2 ^ f) ^ 2} {n : ℕ}

theorem LastNodeOnly.quotImage_eq
    {nW : Fin (rootDatum hF n).rank → SU (unitaryInvolution F 2 f) n}
    {H : Fin (rootDatum hF n).rank → Subgroup (SU (unitaryInvolution F 2 f) n)}
    {π : SU (unitaryInvolution F 2 f) n →* ↥L ⧸ Subgroup.center ↥L} {M : ℕ}
    (hB : BorelQuotient (rootDatum hF n) nW H π M) (h : LastNodeOnly L J hF n π) :
    ∃ i : Fin (n / 2), ¬ i.val + 1 < n / 2 ∧ quotImage L J =
      (borel (rootDatum hF n) H).map π ⊔ (rankOne (rootDatum hF n).rootGroup i).map π := by
  obtain ⟨hBJ0, hshort, i₀, hk₀, hi₀⟩ := h
  have hBJ : (borel (rootDatum hF n) H).map π ≤ quotImage L J := by
    rw [← hB.normalizer_map_posUnipotent]
    exact hBJ0
  have hEq := eq_map_borel_sup_of_le hB.ct hB.extras hB.surj hBJ
  have hsup : (⨆ i ∈ negIndices (rootDatum hF n) ((quotImage L J).comap π),
      (rankOne (rootDatum hF n).rootGroup i).map π) ≤
      (rankOne (rootDatum hF n).rootGroup i₀).map π := by
    refine iSup₂_le fun i hi => ?_
    have hBA : borel (rootDatum hF n) H ≤ (quotImage L J).comap π :=
      fun b hb => hBJ ⟨b, hb, rfl⟩
    have hle := Subgroup.map_le_iff_le_comap.2 (rankOne_le_of_mem_negIndices hBA hi)
    have hik : ¬ i.val + 1 < n / 2 := fun hs => hshort i hs hle
    have hi_lt : i.val < n / 2 := i.isLt
    have hi₀_lt : i₀.val < n / 2 := i₀.isLt
    have : i = i₀ := Fin.ext (by omega)
    subst this
    exact le_rfl
  exact ⟨i₀, hk₀, le_antisymm (hEq.le.trans (sup_le_sup_left hsup _)) (sup_le hBJ hi₀)⟩

theorem LastNodeOnly.not_dvd_card [Finite Y] [Finite (SU (unitaryInvolution F 2 f) n)]
    {nW : Fin (rootDatum hF n).rank → SU (unitaryInvolution F 2 f) n}
    {H : Fin (rootDatum hF n).rank → Subgroup (SU (unitaryInvolution F 2 f) n)}
    {π : SU (unitaryInvolution F 2 f) n →* ↥L ⧸ Subgroup.center ↥L} {M : ℕ}
    (hB : BorelQuotient (rootDatum hF n) nW H π M) (h : LastNodeOnly L J hF n π) {r : ℕ}
    (hr : r.Prime) (hr2 : r ≠ 2) (hrM : ¬ r ∣ M)
    (hX : ∀ i : Fin (n / 2), ¬ i.val + 1 < n / 2 →
      1 + Nat.card ((rootDatum hF n).rootGroup (Pi.single i 1)) < r) :
    ¬ r ∣ Nat.card ↥(quotImage L J) := by
  obtain ⟨i, hi, heq⟩ := h.quotImage_eq hB
  rw [heq]
  refine not_dvd_card_map_borel_sup_rankOne hB.ct hB.extras π i hr (fun hd => hrM ?_) (hX i hi)
  exact dvd_of_dvd_card_map_borel hB.ct hB.extras hB.pGroup π
    (fun t ht => hB.pow_eq_one_of_mem_iSup ht) hr hr2 hd

theorem one_add_card_rootGroup_last_even_lt (hf : f = 2) (he : Even n)
    (hpg : ∀ γ ∈ (rootDatum hF n).roots, IsPGroup 2 ((rootDatum hF n).rootGroup γ))
    {i : Fin (n / 2)} (hk : ¬ i.val + 1 < n / 2) :
    1 + Nat.card ((rootDatum hF n).rootGroup (Pi.single i 1)) < 7 := by
  subst hf
  obtain ⟨ζ, hζ0, hζ⟩ := exists_unitaryInvolution_eq_neg hF
  set e := (rankOneLastEvenEquiv hF he hk).trans (hypEquiv hζ0 hζ).symm
  have hcard : Nat.card ↥(rankOne (rootDatum hF n).rootGroup i) = 60 := by
    have h1 := Nat.card_congr e.toEquiv
    rw [card_sl2, card_fixedSubfield hF] at h1
    exact h1.trans (by norm_num)
  have hroot : (Pi.single i 1 : Fin (rootDatum hF n).rank → ℤ) ∈ (rootDatum hF n).roots :=
    (RootSystem.ofCartan (rootDatum hF n).isFiniteType (rootDatum hF n).divisible).single_mem i
  have hle : (rootDatum hF n).rootGroup (Pi.single i 1) ≤ rankOne (rootDatum hF n).rootGroup i :=
    le_sup_left
  have hdvd : Nat.card ↥((rootDatum hF n).rootGroup (Pi.single i 1)) ∣ 60 :=
    hcard ▸ Subgroup.card_dvd_of_le hle
  obtain ⟨a, ha⟩ := (IsPGroup.iff_card.1 (hpg _ hroot))
  rw [ha] at hdvd ⊢
  have ha2 : a ≤ 2 := by
    by_contra hlt
    have h8 : 2 ^ 3 ∣ 2 ^ a := pow_dvd_pow 2 (by omega)
    have := h8.trans hdvd
    omega
  have : 2 ^ a ≤ 2 ^ 2 := Nat.pow_le_pow_right (by norm_num) ha2
  omega

theorem LastNodeOnly.not_dvd_card_of_seven_le [Finite Y] [Finite (SU (unitaryInvolution F 2 f) n)]
    {nW : Fin (rootDatum hF n).rank → SU (unitaryInvolution F 2 f) n}
    {H : Fin (rootDatum hF n).rank → Subgroup (SU (unitaryInvolution F 2 f) n)}
    {π : SU (unitaryInvolution F 2 f) n →* ↥L ⧸ Subgroup.center ↥L} {M : ℕ}
    (hB : BorelQuotient (rootDatum hF n) nW H π M) (h : LastNodeOnly L J hF n π) (hf : f = 2)
    (he : Even n) {r : ℕ} (hr : r.Prime) (h7 : 7 ≤ r) (hrM : ¬ r ∣ M) :
    ¬ r ∣ Nat.card ↥(quotImage L J) :=
  h.not_dvd_card hB hr (by omega) hrM fun _ hi =>
    lt_of_lt_of_le (one_add_card_rootGroup_last_even_lt hf he hB.pGroup hi) h7

theorem borelQuotient_su_of_surjective (hn : 3 ≤ n) (hnq : (n, 2 ^ f) ≠ (3, 2))
    (π : SU (unitaryInvolution F 2 f) n →* Y) (hπ : Function.Surjective π)
    (hker : π.ker ≤ Subgroup.center (SU (unitaryInvolution F 2 f) n)) :
    ∃ (nW : Fin (rootDatum hF n).rank → SU (unitaryInvolution F 2 f) n)
      (H : Fin (rootDatum hF n).rank → Subgroup (SU (unitaryInvolution F 2 f) n)),
      BorelQuotient (rootDatum hF n) nW H π (Nat.card F - 1) := by
  obtain ⟨ζ, hζ⟩ := exists_traceZero_ne_zero hF
  have h0 := borelQuotient_su hF (by omega) ζ hζ
    (MulEquiv.refl (StatedProj (StatedSU n (2 ^ f) F)))
  have hpow : ∀ z ∈ π.ker, z ^ (Nat.card F - 1) = 1 := by
    intro z hz
    apply h0.ker_pow z
    have hcen := (isQuasisimple_statedSU_of_card hF hn hnq).2
    set ψ := equivStatedSU hF n
    have h1 : ψ z ∈ Subgroup.center ↥(StatedSU n (2 ^ f) F) := by
      rw [← map_center_mulEquiv ψ]
      exact ⟨z, hker hz, rfl⟩
    rw [hcen] at h1
    rw [MonoidHom.mem_ker]
    exact (QuotientGroup.eq_one_iff _).2 h1
  exact ⟨_, _, {
    ct := h0.ct
    extras := h0.extras
    pGroup := h0.pGroup
    surj := hπ
    odd := h0.odd
    torus_pow := h0.torus_pow
    ker_central := fun z hz => hker hz
    ker_pow := hpow }⟩

end Last

end CFSG.AGLEmbedding.LieOut
