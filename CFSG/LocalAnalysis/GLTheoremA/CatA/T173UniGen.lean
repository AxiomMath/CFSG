module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.T173UniStd
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T173UniNorm
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T173UniOmega
public import CFSG.LocalAnalysis.GLTheoremA.CatA.S172CCentTypeSum

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LocalAnalysis.GLTheoremA.T173U

open Polynomial Module QuadraticMap CFSG.ClassicalGroups.Orthogonal CFSG.LieType.SeitzGeneration
  CFSG.RankThree.Classical2 CFSG.RankThree.PartOne.KCOrthogonal CFSG.RankThree.PartOne.KCPrimary
  CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.GroupTheory.WeirSylow CFSG.LocalAnalysis.GLTheoremA
  CFSG.LocalAnalysis.GLTheoremA.S172C.Cent

variable {F : Type} [Field F] [Finite F] [CharP F 2] {V : Type} [AddCommGroup V] [Module F V]
  [FiniteDimensional F V] {Q : QuadraticForm F V} {p : ℕ}

theorem apply_mem_of_mem_frame {m : ℕ} {U : Fin m → Submodule F V} {e : Fin m → ↥(orthDerived Q)}
    {Bb : Subgroup ↥(orthDerived Q)} (hF : IsPlaneFrame Q p U e Bb) {d : ↥(orthDerived Q)} (hd : d ∈ Bb)
    (j : Fin m) {x : V} (hx : x ∈ U j) : (d : V ≃ₗ[F] V) x ∈ U j := by
  have hpow : ∀ k : ℕ, ∀ y ∈ U j, ((e j : V ≃ₗ[F] V) ^ k) y ∈ U j := by
    intro k
    induction k with
    | zero => intro y hy; simpa using hy
    | succ k ih =>
      intro y hy
      rw [pow_succ, LinearEquiv.mul_apply]
      exact ih _ (hF.maps_to j y hy)
  obtain ⟨k, hk⟩ := hF.exists_pow_apply_eq hd j
  rw [hk x hx]
  exact hpow k x hx

theorem finrank_iSup_eq_of_isPlaneSystem {k : ℕ} {U : Fin k → Submodule F V} (hU : IsPlaneSystem Q U) :
    Module.finrank F (⨆ j, U j : Submodule F V) = 2 * k := by
  have h1 := hU.finrank_biSup (Finset.univ : Finset (Fin k))
  have e : (⨆ j ∈ (Finset.univ : Finset (Fin k)), U j) = ⨆ j, U j := by simp
  rw [e] at h1
  simpa [Finset.card_univ, Fintype.card_fin] using h1

theorem specialBlock_le_orthDerived {x : V ≃ₗ[F] V} {h : F[X]}
    (hperf : Group.IsPerfect ↥(specialBlock Q x h)) : specialBlock Q x h ≤ orthDerived Q :=
  specialBlock_le_orthDerived_of_perfect hperf
    ((specialBlock_le_isometryCentralizer h).trans fun _ hg => (Subgroup.mem_inf.mp hg).1)

theorem eichlerGroupOn_le_map_closureIn (hQ : (QuadraticMap.polarBilin Q).Nondegenerate) {n : ℕ}
    (hdim : Module.finrank F V = 2 * n) (hn : 4 ≤ n) (hp : p.Prime) (hp2 : p ≠ 2)
    (hpq : p ∣ Nat.card F + 1) {U : Fin (n - 1) → Submodule F V} {e : Fin (n - 1) → ↥(orthDerived Q)}
    {Bb : Subgroup ↥(orthDerived Q)} (hF : IsPlaneFrame Q p U e Bb) {d : ↥(orthDerived Q)} (hd : d ∈ Bb)
    (hd1 : d ≠ 1) {h : F[X]} (hh : h ∈ primaryFactors (d : V ≃ₗ[F] V).toLinearMap) (hh1 : h ≠ X - 1)
    (hUh : ∀ j, U j ≤ primaryComponent (d : V ≃ₗ[F] V).toLinearMap h)
    (hperf : Group.IsPerfect ↥(specialBlock Q (d : V ≃ₗ[F] V) h))
    (hL : GLALayer (Subgroup.centralizer {d}) =
      (specialBlock Q (d : V ≃ₗ[F] V) h).subgroupOf (orthDerived Q)) :
    eichlerGroupOn Q (⨆ j, U j) ≤ (closureIn (GLALayer (Subgroup.centralizer {d}))
      (Subgroup.normalizer (Bb : Set ↥(orthDerived Q)))).map (orthDerived Q).subtype := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : Finite V := Module.finite_of_finite F
  haveI : Finite (V ≃ₗ[F] V) := Finite.of_injective (fun e : V ≃ₗ[F] V => (e : V → V))
    fun e₁ e₂ h => LinearEquiv.ext (congrFun h)
  have hord : orderOf d = p := orderOf_eq_prime (hF.isElemAbelian.2 d hd) hd1
  have hx : OddOrderIsometry Q p (d : V ≃ₗ[F] V) :=
    oddOrderIsometry_of_orthDerived hp (by rw [ringChar.eq F 2]; exact hp2) hQ d hord
  have hΩO : ∀ g : ↥(orthDerived Q), (g : V ≃ₗ[F] V) ∈ TauCeti.QuadraticMap.orthogonalGroup Q :=
    fun g => orthDerived_le_orthogonalGroup g.2
  refine (eichlerGroupOn_le_iSup_specialBlock (by omega : 3 ≤ n - 1) hF.toIsPlaneSystem hp hp2 hpq hx
    (fun j y hy => apply_mem_of_mem_frame hF hd j hy)
    (fun y hy => hF.apply_eq_of_mem_polarPerp_iSup hd hy) hh hh1 hUh).trans ?_
  refine iSup₂_le fun d' hd' => ?_
  obtain ⟨g, hgN, hg⟩ := exists_mem_normalizer_conj_eq_of_isEvenFlip hQ hdim hn hp hp2 hF hd hd'
  rw [← hg, specialBlock_conj (hΩO g) h]
  rintro _ ⟨s, hs, rfl⟩
  have hsΩ : s ∈ orthDerived Q := specialBlock_le_orthDerived hperf hs
  refine ⟨g * ⟨s, hsΩ⟩ * g⁻¹, ?_, rfl⟩
  have hmem : g * ⟨s, hsΩ⟩ * g⁻¹ ∈ (GLALayer (Subgroup.centralizer {d})).map (MulAut.conj g).toMonoidHom :=
    ⟨⟨s, hsΩ⟩, by rw [hL]; exact Subgroup.mem_subgroupOf.2 hs, by simp [MulAut.conj_apply]⟩
  unfold closureIn
  exact (le_iSup₂_of_le g hgN le_rfl : (GLALayer (Subgroup.centralizer {d})).map
    (MulAut.conj g).toMonoidHom ≤ _) hmem

theorem layer_le_subgroupOf_eichlerGroupOn {n : ℕ} (hn : 4 ≤ n) (hp : p.Prime) (hp2 : p ≠ 2)
    (hpq : p ∣ Nat.card F + 1) (hQ : (QuadraticMap.polarBilin Q).Nondegenerate)
    {U : Fin (n - 1) → Submodule F V} {e : Fin (n - 1) → ↥(orthDerived Q)}
    {Bb : Subgroup ↥(orthDerived Q)} (hF : IsPlaneFrame Q p U e Bb) {d : ↥(orthDerived Q)} (hd : d ∈ Bb)
    (hd1 : d ≠ 1) {h : F[X]} (hh : h ∈ primaryFactors (d : V ≃ₗ[F] V).toLinearMap) (hh1 : h ≠ X - 1)
    (hUh : ∀ j, U j ≤ primaryComponent (d : V ≃ₗ[F] V).toLinearMap h)
    (hperf : Group.IsPerfect ↥(specialBlock Q (d : V ≃ₗ[F] V) h))
    (hL : GLALayer (Subgroup.centralizer {d}) =
      (specialBlock Q (d : V ≃ₗ[F] V) h).subgroupOf (orthDerived Q)) :
    GLALayer (Subgroup.centralizer {d}) ≤ (eichlerGroupOn Q (⨆ j, U j)).subgroupOf (orthDerived Q) := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : Finite V := Module.finite_of_finite F
  haveI : Finite (V ≃ₗ[F] V) := Finite.of_injective (fun e : V ≃ₗ[F] V => (e : V → V))
    fun e₁ e₂ h => LinearEquiv.ext (congrFun h)
  have hord : orderOf d = p := orderOf_eq_prime (hF.isElemAbelian.2 d hd) hd1
  have hx : OddOrderIsometry Q p (d : V ≃ₗ[F] V) :=
    oddOrderIsometry_of_orthDerived hp (by rw [ringChar.eq F 2]; exact hp2) hQ d hord
  intro k hk
  rw [hL] at hk
  exact Subgroup.mem_subgroupOf.2 (specialBlock_le_eichlerGroupOn (by omega : 3 ≤ n - 1) hF.toIsPlaneSystem hp hp2
    hpq hx (fun j y hy => apply_mem_of_mem_frame hF hd j hy)
    (fun y hy => hF.apply_eq_of_mem_polarPerp_iSup hd hy) hh hh1 hUh hperf (Subgroup.mem_subgroupOf.1 hk))

theorem closureIn_layer_eq_eichlerGroupOn (hQ : (QuadraticMap.polarBilin Q).Nondegenerate) {n : ℕ}
    (hdim : Module.finrank F V = 2 * n) (hn : 4 ≤ n) (hp : p.Prime) (hp2 : p ≠ 2)
    (hpq : p ∣ Nat.card F + 1) {U : Fin (n - 1) → Submodule F V} {e : Fin (n - 1) → ↥(orthDerived Q)}
    {Bb : Subgroup ↥(orthDerived Q)} (hF : IsPlaneFrame Q p U e Bb) {d : ↥(orthDerived Q)} (hd : d ∈ Bb)
    (hd1 : d ≠ 1) {h : F[X]} (hh : h ∈ primaryFactors (d : V ≃ₗ[F] V).toLinearMap) (hh1 : h ≠ X - 1)
    (hUh : ∀ j, U j ≤ primaryComponent (d : V ≃ₗ[F] V).toLinearMap h)
    (hL : GLALayer (Subgroup.centralizer {d}) =
      (specialBlock Q (d : V ≃ₗ[F] V) h).subgroupOf (orthDerived Q))
    (hquasi : CFSG.IsQuasisimple ↥(specialBlock Q (d : V ≃ₗ[F] V) h)) :
    closureIn (GLALayer (Subgroup.centralizer {d})) (Subgroup.normalizer (Bb : Set ↥(orthDerived Q))) =
      (eichlerGroupOn Q (⨆ j, U j)).subgroupOf (orthDerived Q) := by
  classical
  have hΩO : ∀ g : ↥(orthDerived Q), (g : V ≃ₗ[F] V) ∈ TauCeti.QuadraticMap.orthogonalGroup Q :=
    fun g => orthDerived_le_orthogonalGroup g.2
  have hKle := layer_le_subgroupOf_eichlerGroupOn hn hp hp2 hpq hQ hF hd hd1 hh hh1 hUh hquasi.1 hL
  refine le_antisymm ?_ ?_
  · unfold closureIn
    refine iSup₂_le fun g hgN => ?_
    rintro _ ⟨k, hk, rfl⟩
    have hkE : (k : V ≃ₗ[F] V) ∈ eichlerGroupOn Q (⨆ j, U j) := Subgroup.mem_subgroupOf.1 (hKle hk)
    refine Subgroup.mem_subgroupOf.2 ?_
    show (g : V ≃ₗ[F] V) * (k : V ≃ₗ[F] V) * (g : V ≃ₗ[F] V)⁻¹ ∈ eichlerGroupOn Q (⨆ j, U j)
    exact conj_mem_eichlerGroupOn (hΩO g)
      (fun x hx => apply_mem_iSup_of_mem_normalizer hF hgN hx) hkE
  · intro x hx
    have hxE : (x : V ≃ₗ[F] V) ∈ eichlerGroupOn Q (⨆ j, U j) := Subgroup.mem_subgroupOf.1 hx
    obtain ⟨y, hy, hyx⟩ := eichlerGroupOn_le_map_closureIn hQ hdim hn hp hp2 hpq hF hd hd1 hh hh1 hUh hquasi.1
      hL hxE
    rw [← Subtype.ext hyx]
    exact hy

theorem catalogIs_pSimple_eichlerGroupOn_even (hQ : (QuadraticMap.polarBilin Q).Nondegenerate) {n : ℕ}
    (hdim : Module.finrank F V = 2 * n) (hn : 4 ≤ n) {U : Fin (n - 1) → Submodule F V}
    (hU : IsPlaneSystem Q U) (hev : Even (n - 1)) (hp : p.Prime) (hp2 : p ≠ 2) (hpq : p ∣ Nat.card F + 1) :
    catalogIs (PSimple p ((eichlerGroupOn Q (⨆ j, U j)).subgroupOf (orthDerived Q)))
      (isOmPA (n - 1) (Nat.card F)) := by
  have hW := polarNondegOn_iSup_of_isPlaneSystem hU
  have hfin := finrank_iSup_eq_of_isPlaneSystem hU
  have hle : eichlerGroupOn Q (⨆ j, U j) ≤ orthDerived Q :=
    (eichlerGroupOn_le fun e _ w _ => eichler_mem_elementaryGroup Q e w).trans
      (le_of_eq (orthDerived_eq_elementaryGroup_of_three_le hQ (by omega : 3 ≤ n) hdim).symm)
  have hplus : IsPlusType (Q.comp (⨆ j, U j : Submodule F V).subtype) := by
    have h1 := (hU.isPlusType_biSup_iff (Finset.univ : Finset (Fin (n - 1)))).2
      (by simpa [Finset.card_univ, Fintype.card_fin] using hev)
    have e : (⨆ j ∈ (Finset.univ : Finset (Fin (n - 1))), U j) = ⨆ j, U j := by simp
    rw [e] at h1
    exact h1
  exact catalogIs_pSimple_subgroupOf_eichlerGroupOn hW (by omega : 3 ≤ n - 1) hfin hle
    (catalogIs_pSimple_top_orthDerived_plus (nondegenerate_comp_subtype hW) (by omega : 3 ≤ n - 1) hfin hplus
      hp hp2 hpq)

theorem catalogIs_pSimple_eichlerGroupOn_odd (hQ : (QuadraticMap.polarBilin Q).Nondegenerate) {n : ℕ}
    (hdim : Module.finrank F V = 2 * n) (hn : 4 ≤ n) {U : Fin (n - 1) → Submodule F V}
    (hU : IsPlaneSystem Q U) (hodd : Odd (n - 1)) (hp : p.Prime) (hp2 : p ≠ 2) (hpq : p ∣ Nat.card F + 1) :
    catalogIs (PSimple p ((eichlerGroupOn Q (⨆ j, U j)).subgroupOf (orthDerived Q)))
      (isOmMA (n - 1) (Nat.card F)) := by
  have hW := polarNondegOn_iSup_of_isPlaneSystem hU
  have hfin := finrank_iSup_eq_of_isPlaneSystem hU
  have hle : eichlerGroupOn Q (⨆ j, U j) ≤ orthDerived Q :=
    (eichlerGroupOn_le fun e _ w _ => eichler_mem_elementaryGroup Q e w).trans
      (le_of_eq (orthDerived_eq_elementaryGroup_of_three_le hQ (by omega : 3 ≤ n) hdim).symm)
  have hminus : ¬ IsPlusType (Q.comp (⨆ j, U j : Submodule F V).subtype) := by
    intro hpl
    have e : (⨆ j ∈ (Finset.univ : Finset (Fin (n - 1))), U j) = ⨆ j, U j := by simp
    have h1 := (hU.isPlusType_biSup_iff (Finset.univ : Finset (Fin (n - 1)))).1 (by rw [e]; exact hpl)
    rw [Finset.card_univ, Fintype.card_fin] at h1
    exact (Nat.not_even_iff_odd.2 hodd) h1
  refine catalogIs_pSimple_subgroupOf_eichlerGroupOn hW (by omega : 3 ≤ n - 1) hfin hle ?_
  by_cases h4 : 4 ≤ n - 1
  · exact catalogIs_pSimple_top_orthDerived_minus (nondegenerate_comp_subtype hW) h4 hfin hminus hp hp2 hpq
  · have key : ∀ m : ℕ, m = 3 → catalogIs (PSimple p (⊤ : Subgroup
        ↥(orthDerived (Q.comp (⨆ j, U j : Submodule F V).subtype)))) (isOmMA m (Nat.card F)) := by
      rintro m rfl
      exact catalogIs_pSimple_top_orthDerived_minus_three (nondegenerate_comp_subtype hW) (by omega) hminus hp
        hp2 hpq
    exact key (n - 1) (by omega)

theorem type126_closureIn_of_fullSupport (hQ : (QuadraticMap.polarBilin Q).Nondegenerate) {n : ℕ}
    (hdim : Module.finrank F V = 2 * n) (hn : 4 ≤ n) (hp : p.Prime) (hp2 : p ≠ 2)
    (hpq : p ∣ Nat.card F + 1) {U : Fin (n - 1) → Submodule F V} {e : Fin (n - 1) → ↥(orthDerived Q)}
    {Bb : Subgroup ↥(orthDerived Q)} (hF : IsPlaneFrame Q p U e Bb) {d : ↥(orthDerived Q)} (hd : d ∈ Bb)
    (hd1 : d ≠ 1) {h : F[X]} (hh : h ∈ primaryFactors (d : V ≃ₗ[F] V).toLinearMap) (hh1 : h ≠ X - 1)
    (hUh : ∀ j, U j ≤ primaryComponent (d : V ≃ₗ[F] V).toLinearMap h)
    (hL : GLALayer (Subgroup.centralizer {d}) =
      (specialBlock Q (d : V ≃ₗ[F] V) h).subgroupOf (orthDerived Q))
    (hquasi : CFSG.IsQuasisimple ↥(specialBlock Q (d : V ≃ₗ[F] V) h)) (hk : 4 ≤ n - 1 ∨ 4 ≤ Nat.card F)
    (hframe : (IsPlusType Q ∧ Odd n ∧ Nat.card F = 2) ∨ (¬ IsPlusType Q ∧ Even n)) :
    Type126 p (⊤ : Subgroup ↥(orthDerived Q)) (GLALayer (Subgroup.centralizer {d}))
      (closureIn (GLALayer (Subgroup.centralizer {d}))
        (Subgroup.normalizer (Bb : Set ↥(orthDerived Q)))) := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : Finite V := Module.finite_of_finite F
  haveI : Finite (V ≃ₗ[F] V) := Finite.of_injective (fun e : V ≃ₗ[F] V => (e : V → V))
    fun e₁ e₂ h => LinearEquiv.ext (congrFun h)
  have hord : orderOf d = p := orderOf_eq_prime (hF.isElemAbelian.2 d hd) hd1
  have hmult := primaryMultiplicity_eq_of_frame hQ hdim hn hp hp2 hpq hF hd hh hh1 hUh
  have hm4 : 4 ≤ n - 1 ∨ ((n - 1 = 2 ∨ n - 1 = 3) ∧ 4 ≤ Nat.card F) := by
    rcases hk with hk | hk
    · exact Or.inl hk
    · by_cases h4 : 4 ≤ n - 1
      · exact Or.inl h4
      · exact Or.inr ⟨Or.inr (by omega), hk⟩
  have hK := catalogIs_pSimple_specialBlock hp hp2 hpq hQ hord hh hh1 hmult hm4
  rw [closureIn_layer_eq_eichlerGroupOn hQ hdim hn hp hp2 hpq hF hd hd1 hh hh1 hUh hL hquasi, hL]
  rcases hframe with ⟨hplus, hodd, hq⟩ | ⟨hminus, hev⟩
  · have hp3 : p = 3 := by
      have h3 : p ∣ 3 := by rw [hq] at hpq; exact hpq
      exact (Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).1 h3
    have hL1 := catalogIs_pSimple_top_orthDerived_plus hQ (by omega : 3 ≤ n) hdim hplus hp hp2 hpq
    have hI := catalogIs_pSimple_eichlerGroupOn_even hQ hdim hn hF.toIsPlaneSystem
      (by obtain ⟨m, hm⟩ := hodd; exact ⟨m, by omega⟩) hp hp2 hpq
    rw [hq] at hL1 hK hI
    subst hp3
    exact Or.inr (Or.inl ⟨rfl, n, hodd, hL1, hK, hI⟩)
  · obtain ⟨f, hf1, hf⟩ := exists_natCard_eq_two_pow F
    have hL1 := catalogIs_pSimple_top_orthDerived_minus hQ hn hdim hminus hp hp2 hpq
    have hI := catalogIs_pSimple_eichlerGroupOn_odd hQ hdim hn hF.toIsPlaneSystem
      (by obtain ⟨m, hm⟩ := hev; exact ⟨m - 1, by omega⟩) hp hp2 hpq
    have hpf : p ∣ 2 ^ f + 1 := by rw [← hf]; exact hpq
    rw [hf] at hL1 hK hI
    exact Or.inr (Or.inr ⟨n, f, hev, hf1, hpf, hL1, hK, hI⟩)

end CFSG.LocalAnalysis.GLTheoremA.T173U

end
