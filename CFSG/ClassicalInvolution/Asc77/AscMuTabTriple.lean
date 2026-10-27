module

public import CFSG.ClassicalInvolution.Asc77.AscMuTabKind
public import CFSG.ClassicalInvolution.Asc77.AscMuTabRoots
public import CFSG.ClassicalInvolution.Asc77.AscIHSectA
public import CFSG.ClassicalInvolution.Asc77.AscIH8Graph

public section

namespace CFSG.ClassicalInvolution.Asc77

open CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.RouteD
  CFSG.LieType.RootSystem CFSG.LieType.Universal CFSG.LieType.Universal.Spin
  CFSG.LieType.Universal.Symplectic
open scoped Matrix

namespace MuTab

section Root

variable {p : ℕ} [Fact p.Prime]

theorem threeOrth_psl {n e : ℕ} (hadm : StatedLieAdmissible .PSL n p e) (hn : 6 ≤ n) :
    ThreeOrth (modelUniv .PSL n p e Fact.out).D := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have hl : ∀ i : Fin (modelUniv .PSL (m + 1) p e Fact.out).D.rank,
      ModelFacts.IsLongestRoot (modelUniv .PSL (m + 1) p e Fact.out).D (Pi.single i 1) :=
    fun i => ModelFacts.isLongestRoot_single .PSL (m + 1) p e Fact.out trivial hadm i trivial
  refine threeOrth_of_nodes _ (a := (⟨0, by omega⟩ : Fin m)) (b := (⟨2, by omega⟩ : Fin m))
    (c := (⟨4, by omega⟩ : Fin m)) (hl _) (hl _) (hl _) ?_ ?_ ?_ <;>
  · show CartanMatrix.A m _ _ = 0
    simp [CartanMatrix.A, Fin.ext_iff]

theorem threeOrth_pOmegaPlus {n e : ℕ} (hadm : StatedLieAdmissible .POmegaPlus n p e)
    (hn : 5 ≤ n) : ThreeOrth (modelUniv .POmegaPlus n p e Fact.out).D := by
  have hl : ∀ i : Fin (modelUniv .POmegaPlus n p e Fact.out).D.rank,
      ModelFacts.IsLongestRoot (modelUniv .POmegaPlus n p e Fact.out).D (Pi.single i 1) :=
    fun i => ModelFacts.isLongestRoot_single .POmegaPlus n p e Fact.out trivial hadm i trivial
  have h3 : 3 ≤ n := by omega
  have h : modelUniv .POmegaPlus n p e Fact.out =
      ⟨spinGroup (quadPlus n (GaloisField p e)), plusDatum n (GaloisField p e) h3⟩ :=
    ModelFacts.modelUniv_POmegaPlus h3
  generalize modelUniv .POmegaPlus n p e Fact.out = L at h hl ⊢
  subst h
  refine threeOrth_of_nodes _ (a := (⟨0, by omega⟩ : Fin n)) (b := (⟨n - 2, by omega⟩ : Fin n))
    (c := (⟨n - 1, by omega⟩ : Fin n)) (hl _) (hl _) (hl _) ?_ ?_ ?_ <;>
  · show cartanD n _ _ = 0
    simp [cartanD, Fin.ext_iff]
    omega

theorem threeOrth_pOmegaOdd {n e : ℕ} (hadm : StatedLieAdmissible .POmegaOdd n p e)
    (hn : 4 ≤ n) : ThreeOrth (modelUniv .POmegaOdd n p e Fact.out).D := by
  have hl : ∀ i : Fin (modelUniv .POmegaOdd n p e Fact.out).D.rank, i.val + 1 < n →
      ModelFacts.IsLongestRoot (modelUniv .POmegaOdd n p e Fact.out).D (Pi.single i 1) :=
    fun i hi => ModelFacts.isLongestRoot_single .POmegaOdd n p e Fact.out trivial hadm i hi
  refine threeOrth_B _ (x := (⟨n - 4, by omega⟩ : Fin n)) (y := (⟨n - 2, by omega⟩ : Fin n))
    (z := (⟨n - 1, by omega⟩ : Fin n)) (hl _ (by show n - 4 + 1 < n; omega))
    (hl _ (by show n - 2 + 1 < n; omega)) ?_ ?_ ?_ ?_ ?_ <;>
  · show cartanB n _ _ = _
    simp [cartanB, Fin.ext_iff] <;> omega

theorem threeOrth_pOmegaMinus {n e : ℕ} (hadm : StatedLieAdmissible .POmegaMinus n p e)
    (hn : 5 ≤ n) : ThreeOrth (modelUniv .POmegaMinus n p e Fact.out).D := by
  have hl : ∀ i : Fin (modelUniv .POmegaMinus n p e Fact.out).D.rank, i.val + 2 < n →
      ModelFacts.IsLongestRoot (modelUniv .POmegaMinus n p e Fact.out).D (Pi.single i 1) :=
    fun i hi => ModelFacts.isLongestRoot_single .POmegaMinus n p e Fact.out trivial hadm i hi
  refine threeOrth_B _ (x := (⟨n - 5, by omega⟩ : Fin (n - 1)))
    (y := (⟨n - 3, by omega⟩ : Fin (n - 1))) (z := (⟨n - 2, by omega⟩ : Fin (n - 1)))
    (hl _ (by show n - 5 + 2 < n; omega)) (hl _ (by show n - 3 + 2 < n; omega)) ?_ ?_ ?_ ?_ ?_ <;>
  · show cartanB (n - 1) _ _ = _
    simp [cartanB, Fin.ext_iff] <;> omega

variable {K : Type} [Group K]

theorem threeOrth_of_cartanC (D : UniversalRootDatum K) (hcart : D.cartan = cartanC D.rank)
    (hdiv : D.divisible = ∅) (hm : 3 ≤ D.rank) : ThreeOrth D := by
  have ha : (⟨D.rank - 3, by omega⟩ : Fin D.rank).val + 3 = D.rank := by
    show D.rank - 3 + 3 = D.rank
    omega
  have hb : (⟨D.rank - 2, by omega⟩ : Fin D.rank).val + 2 = D.rank := by
    show D.rank - 2 + 2 = D.rank
    omega
  have hc : (⟨D.rank - 1, by omega⟩ : Fin D.rank).val + 1 = D.rank := by
    show D.rank - 1 + 1 = D.rank
    omega
  obtain ⟨haa, hbb, hcc, hab, hba, hbc, hcb, hac, hca⟩ := cartanC_entries ha hb hc
  exact threeOrth_tail D (criterion_C D hcart hdiv ha hb hc).1 (by rw [hcart]; exact hcc)
    (by rw [hcart]; exact hcb) (by rw [hcart]; exact hca) (by rw [hcart]; exact hbc)
    (by rw [hcart]; exact hbb) (by rw [hcart]; exact hba) (by rw [hcart]; exact hac)
    (by rw [hcart]; exact hab)

theorem threeOrth_of_cartanBC (D : UniversalRootDatum K) (hcart : D.cartan = (cartanC D.rank)ᵀ)
    (hdiv : D.divisible = {j : Fin D.rank | j.val + 1 = D.rank}) (hm : 3 ≤ D.rank) :
    ThreeOrth D := by
  have ha : (⟨D.rank - 3, by omega⟩ : Fin D.rank).val + 3 = D.rank := by
    show D.rank - 3 + 3 = D.rank
    omega
  have hb : (⟨D.rank - 2, by omega⟩ : Fin D.rank).val + 2 = D.rank := by
    show D.rank - 2 + 2 = D.rank
    omega
  have hc : (⟨D.rank - 1, by omega⟩ : Fin D.rank).val + 1 = D.rank := by
    show D.rank - 1 + 1 = D.rank
    omega
  obtain ⟨haa, hbb, hcc, hab, hba, hbc, hcb, hac, hca⟩ := cartanC_entries ha hb hc
  have eT : ∀ i j, D.cartan i j = cartanC D.rank j i := fun i j => by rw [hcart]; rfl
  exact threeOrth_tailBC D (criterion_BC D hcart hdiv ha hb hc).1 (by rw [eT]; exact hcc)
    (by rw [eT]; exact hbc) (by rw [eT]; exact hac) (by rw [eT]; exact hcb)
    (by rw [eT]; exact hbb) (by rw [eT]; exact hab) (by rw [eT]; exact hca)
    (by rw [eT]; exact hba)

theorem threeOrth_psp {n e : ℕ} (hn : 3 ≤ n) :
    ThreeOrth (modelUniv .PSp n p e Fact.out).D :=
  threeOrth_of_cartanC _ rfl rfl hn

theorem threeOrth_psu_even {n e : ℕ} (hadm : StatedLieAdmissible .PSU n p e) (he : Even n)
    (hn : 6 ≤ n) : ThreeOrth (modelUniv .PSU n p e Fact.out).D := by
  have hf : 1 ≤ e := hadm.2.1
  have h : modelUniv .PSU n p e Fact.out =
      ⟨Unitary.SU (CFSG.LieType.BorelTits.unitaryInvolution (GaloisField p (2 * e)) p e) n,
        Unitary.rootDatum (card_galoisField_two_mul p e hf) n⟩ :=
    ModelFacts.modelUniv_PSU hf
  generalize modelUniv .PSU n p e Fact.out = L at h ⊢
  subst h
  obtain ⟨hc, hd⟩ := ModelFacts.unitary_even he
  exact threeOrth_of_cartanC (Unitary.rootDatum (card_galoisField_two_mul p e hf) n) hc hd
    (by show 3 ≤ n / 2; omega)

theorem threeOrth_psu_odd {n e : ℕ} (hadm : StatedLieAdmissible .PSU n p e) (ho : ¬ Even n)
    (hn : 7 ≤ n) : ThreeOrth (modelUniv .PSU n p e Fact.out).D := by
  have hf : 1 ≤ e := hadm.2.1
  have h : modelUniv .PSU n p e Fact.out =
      ⟨Unitary.SU (CFSG.LieType.BorelTits.unitaryInvolution (GaloisField p (2 * e)) p e) n,
        Unitary.rootDatum (card_galoisField_two_mul p e hf) n⟩ :=
    ModelFacts.modelUniv_PSU hf
  generalize modelUniv .PSU n p e Fact.out = L at h ⊢
  subst h
  obtain ⟨hc, hd⟩ := ModelFacts.unitary_odd ho
  exact threeOrth_of_cartanBC (Unitary.rootDatum (card_galoisField_two_mul p e hf) n) hc hd
    (by show 3 ≤ n / 2; omega)

end Root

section Exceptional

variable {p : ℕ} [Fact p.Prime]

abbrev muTabF4 : Matrix (Fin 4) (Fin 4) ℤ := CFSG.Blueprint.Chevalley.Tag.cartan .F4

theorem muTabF4_tail : muTabF4 1 1 = 2 ∧ muTabF4 1 2 = -1 ∧ muTabF4 1 3 = 0 ∧
    muTabF4 2 1 = -2 ∧ muTabF4 2 2 = 2 ∧ muTabF4 2 3 = -1 ∧ muTabF4 3 1 = 0 ∧
    muTabF4 3 2 = -1 := by
  decide

abbrev muTabE6 : Matrix (Fin 6) (Fin 6) ℤ := CFSG.Blueprint.Chevalley.Tag.cartan .E6

abbrev muTabE7 : Matrix (Fin 7) (Fin 7) ℤ := CFSG.Blueprint.Chevalley.Tag.cartan .E7

abbrev muTabE8 : Matrix (Fin 8) (Fin 8) ℤ := CFSG.Blueprint.Chevalley.Tag.cartan .E8

theorem muTabE6_nodes : muTabE6 0 1 = 0 ∧ muTabE6 0 4 = 0 ∧ muTabE6 1 4 = 0 := by decide

theorem muTabE7_nodes : muTabE7 0 1 = 0 ∧ muTabE7 0 4 = 0 ∧ muTabE7 1 4 = 0 := by decide

theorem muTabE8_nodes : muTabE8 0 1 = 0 ∧ muTabE8 0 4 = 0 ∧ muTabE8 1 4 = 0 := by decide

theorem threeOrth_E6 {e : ℕ} (hadm : StatedLieAdmissible .E6 0 p e) :
    ThreeOrth (modelUniv .E6 0 p e Fact.out).D := by
  obtain ⟨h01, h04, h14⟩ := muTabE6_nodes
  have hl : ∀ i : Fin 6, ModelFacts.IsLongestRoot (modelUniv .E6 0 p e Fact.out).D
      (Pi.single i 1) := fun i => ModelFacts.isLongestRoot_single .E6 0 p e Fact.out trivial hadm i
        trivial
  exact threeOrth_of_nodes _ (a := (0 : Fin 6)) (b := (1 : Fin 6)) (c := (4 : Fin 6)) (hl _)
    (hl _) (hl _) h01 h04 h14

theorem threeOrth_E7 {e : ℕ} (hadm : StatedLieAdmissible .E7 0 p e) :
    ThreeOrth (modelUniv .E7 0 p e Fact.out).D := by
  obtain ⟨h01, h04, h14⟩ := muTabE7_nodes
  have hl : ∀ i : Fin 7, ModelFacts.IsLongestRoot (modelUniv .E7 0 p e Fact.out).D
      (Pi.single i 1) := fun i => ModelFacts.isLongestRoot_single .E7 0 p e Fact.out trivial hadm i
        trivial
  exact threeOrth_of_nodes _ (a := (0 : Fin 7)) (b := (1 : Fin 7)) (c := (4 : Fin 7)) (hl _)
    (hl _) (hl _) h01 h04 h14

theorem threeOrth_E8 {e : ℕ} (hadm : StatedLieAdmissible .E8 0 p e) :
    ThreeOrth (modelUniv .E8 0 p e Fact.out).D := by
  obtain ⟨h01, h04, h14⟩ := muTabE8_nodes
  have hl : ∀ i : Fin 8, ModelFacts.IsLongestRoot (modelUniv .E8 0 p e Fact.out).D
      (Pi.single i 1) := fun i => ModelFacts.isLongestRoot_single .E8 0 p e Fact.out trivial hadm i
        trivial
  exact threeOrth_of_nodes _ (a := (0 : Fin 8)) (b := (1 : Fin 8)) (c := (4 : Fin 8)) (hl _)
    (hl _) (hl _) h01 h04 h14

theorem threeOrth_F4 {e : ℕ} (hadm : StatedLieAdmissible .F4 0 p e) :
    ThreeOrth (modelUniv .F4 0 p e Fact.out).D := by
  obtain ⟨hcc, hcb, hca, hbc, hbb, hba, hac, hab⟩ := muTabF4_tail
  exact threeOrth_tail _ (a := (3 : Fin 4)) (b := (2 : Fin 4)) (c := (1 : Fin 4))
    (ModelFacts.isLongestRoot_single .F4 0 p e Fact.out trivial hadm (1 : Fin 4)
      (by show 1 < 2; omega)) hcc hcb hca hbc hbb hba hac hab

theorem threeOrth_twistedE6 {e : ℕ} (hadm : StatedLieAdmissible .twistedE6 0 p e) :
    ThreeOrth (modelUniv .twistedE6 0 p e Fact.out).D := by
  obtain ⟨hcc, hcb, hca, hbc, hbb, hba, hac, hab⟩ := muTabF4_tail
  exact threeOrth_tail _ (a := (3 : Fin 4)) (b := (2 : Fin 4)) (c := (1 : Fin 4))
    (ModelFacts.isLongestRoot_single .twistedE6 0 p e Fact.out trivial hadm (1 : Fin 4)
      (by show 1 < 2; omega)) hcc hcb hca hbc hbb hba hac hab

end Exceptional


section Large

variable {p : ℕ} [Fact p.Prime]

theorem threeOrth_of_large {π : Bool} {t : StatedLieTag} {k e : ℕ} (hfund : Generic.IsFundTag t)
    (hadm : StatedLieAdmissible t k p e) (hnpsl : ¬ (t = .PSL ∧ k = 2))
    (hlarge : muKind π t k = .large) : ThreeOrth (modelUniv t k p e Fact.out).D := by
  cases t with
  | PSL =>
    have h2 : 2 ≤ k := hadm.2.2.1
    have h2' : k ≠ 2 := fun h => hnpsl ⟨rfl, h⟩
    have h3 : k ≠ 3 := fun h => by subst h; cases π <;> simp [muKind] at hlarge
    have h4 : k ≠ 4 := fun h => by subst h; cases π <;> simp [muKind] at hlarge
    have h5 : k ≠ 5 := fun h => by subst h; cases π <;> simp [muKind] at hlarge
    exact threeOrth_psl hadm (by omega)
  | PSU =>
    have h3 : 3 ≤ k := hadm.2.2.1
    have h3' : k ≠ 3 := fun h => by subst h; cases π <;> simp [muKind] at hlarge
    have h4 : k ≠ 4 := fun h => by subst h; cases π <;> simp [muKind] at hlarge
    have h5 : k ≠ 5 := fun h => by subst h; cases π <;> simp [muKind] at hlarge
    by_cases he : Even k
    · obtain ⟨r, hr⟩ := he
      exact threeOrth_psu_even hadm ⟨r, hr⟩ (by omega)
    · obtain ⟨r, hr⟩ := Nat.not_even_iff_odd.mp he
      exact threeOrth_psu_odd hadm he (by omega)
  | PSp =>
    have h2 : 2 ≤ k := hadm.2.2.1
    have h2' : k ≠ 2 := fun h => by subst h; cases π <;> simp [muKind] at hlarge
    exact threeOrth_psp (by omega)
  | POmegaOdd =>
    have h3 : 3 ≤ k := hadm.2.2.1
    have h3' : k ≠ 3 := fun h => by subst h; cases π <;> simp [muKind] at hlarge
    exact threeOrth_pOmegaOdd hadm (by omega)
  | POmegaPlus =>
    have h4 : 4 ≤ k := hadm.2.2
    have h4' : k ≠ 4 := fun h => by subst h; cases π <;> simp [muKind] at hlarge
    exact threeOrth_pOmegaPlus hadm (by omega)
  | POmegaMinus =>
    have h4 : 4 ≤ k := hadm.2.2
    have h4' : k ≠ 4 := fun h => by subst h; cases π <;> simp [muKind] at hlarge
    exact threeOrth_pOmegaMinus hadm (by omega)
  | G2 =>
    obtain ⟨rfl, -⟩ := hadm.2.2
    cases π <;> simp [muKind] at hlarge
  | trialityD4 =>
    obtain rfl : k = 0 := hadm.2.2
    cases π <;> simp [muKind] at hlarge
  | F4 =>
    obtain rfl : k = 0 := hadm.2.2
    exact threeOrth_F4 hadm
  | E6 =>
    obtain rfl : k = 0 := hadm.2.2
    exact threeOrth_E6 hadm
  | E7 =>
    obtain rfl : k = 0 := hadm.2.2
    exact threeOrth_E7 hadm
  | E8 =>
    obtain rfl : k = 0 := hadm.2.2
    exact threeOrth_E8 hadm
  | twistedE6 =>
    obtain rfl : k = 0 := hadm.2.2
    exact threeOrth_twistedE6 hadm
  | twistedB2 => exact absurd hfund (by simp [Generic.IsFundTag])
  | twistedG2 => exact absurd hfund (by simp [Generic.IsFundTag])
  | twistedF4 => exact absurd hfund (by simp [Generic.IsFundTag])
  | Tits => exact absurd hfund (by simp [Generic.IsFundTag])

end Large

section Fund

variable {p : ℕ} [Fact p.Prime] {t : StatedLieTag} {k e : ℕ}

theorem exists_triple_of_threeOrth (hp2 : p ≠ 2) (hq : 5 ≤ p ^ e) (hfund : Generic.IsFundTag t)
    (hadm : StatedLieAdmissible t k p e) (h : ThreeOrth (modelUniv t k p e Fact.out).D) :
    ∃ R₁ ∈ ModelFund p t k e, ∃ R₂ ∈ ModelFund p t k e, ∃ R₃ ∈ ModelFund p t k e,
      R₁ ≠ R₂ ∧ R₁ ≠ R₃ ∧ R₂ ≠ R₃ ∧ Commutes R₁ R₂ ∧ Commutes R₁ R₃ ∧ Commutes R₂ R₃ := by
  obtain ⟨γ, δ, ε, hγ, hδ, hε, h12, h13, h23⟩ := h
  obtain ⟨_, _, _, hext⟩ := ModelFacts.hasBruhatDatum t k p e Fact.out (ih8_isFundTag_mf hfund) hadm
  have hmem : ∀ {γ : Fin (modelUniv t k p e Fact.out).D.rank → ℤ},
      ModelFacts.IsLongestRoot (modelUniv t k p e Fact.out).D γ →
      ((modelUniv t k p e Fact.out).D.rootGroup γ ⊔
        (modelUniv t k p e Fact.out).D.rootGroup (-γ)) ∈ ModelFund p t k e :=
    fun hγ => ⟨1, _, Or.inl hγ, (conjSub_one _).symm⟩
  have hc : ∀ {γ δ : Fin (modelUniv t k p e Fact.out).D.rank → ℤ},
      ModelFacts.IsLongestRoot (modelUniv t k p e Fact.out).D γ →
      ModelFacts.IsLongestRoot (modelUniv t k p e Fact.out).D δ →
      form (modelUniv t k p e Fact.out).D.isFiniteType (toRat γ) (toRat δ) = 0 →
      Commutes ((modelUniv t k p e Fact.out).D.rootGroup γ ⊔
          (modelUniv t k p e Fact.out).D.rootGroup (-γ))
        ((modelUniv t k p e Fact.out).D.rootGroup δ ⊔
          (modelUniv t k p e Fact.out).D.rootGroup (-δ)) :=
    fun hγ hδ h => commutes_fund_of_orthogonal_of_longest _ hext hγ.1 hδ.1 hγ.2 h
  have hne : ∀ {γ δ : Fin (modelUniv t k p e Fact.out).D.rank → ℤ},
      ModelFacts.IsLongestRoot (modelUniv t k p e Fact.out).D γ →
      ModelFacts.IsLongestRoot (modelUniv t k p e Fact.out).D δ →
      form (modelUniv t k p e Fact.out).D.isFiniteType (toRat γ) (toRat δ) = 0 →
      ((modelUniv t k p e Fact.out).D.rootGroup γ ⊔
          (modelUniv t k p e Fact.out).D.rootGroup (-γ)) ≠
        ((modelUniv t k p e Fact.out).D.rootGroup δ ⊔
          (modelUniv t k p e Fact.out).D.rootGroup (-δ)) :=
    fun hγ hδ h heq => not_commutes_self_modelFund hp2 hfund hq hadm (hmem hγ)
      (fun a ha b hb => hc hγ hδ h a ha b (heq ▸ hb))
  exact ⟨_, hmem hγ, _, hmem hδ, _, hmem hε, hne hγ hδ h12, hne hγ hε h13, hne hδ hε h23,
    hc hγ hδ h12, hc hγ hε h13, hc hδ hε h23⟩

variable {f : ℕ} {G : Type} [Group G] {Ω : Set (Subgroup G)}

theorem shapeTriple_of_datum (M : Ih8Model p f Ω t k e) (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f)
    (hne : Ω.Nonempty) (hG2 : t ≠ .G2) (hD4 : t ≠ .trialityD4)
    (h : ThreeOrth (modelUniv t k p e Fact.out).D) : ShapeTriple Ω := by
  have hq' : 5 ≤ p ^ e := by rw [M.exp_eq_f hD4]; exact hq
  obtain ⟨R₁, h₁, R₂, h₂, R₃, h₃, h12, h13, h23, c12, c13, c23⟩ :=
    exists_triple_of_threeOrth hp2 hq' M.isFundTag M.admissible h
  have hcls := M.fund_subset_cls hne hG2 hD4
  have key : ∀ {R S : Subgroup (modelUniv t k p e Fact.out).K}, R ∈ ModelFund p t k e →
      S ∈ ModelFund p t k e → R ≠ S → R.map M.ψ ≠ S.map M.ψ := fun hR hS hRS h =>
    hRS (ih8_eq_of_map_eq M.ψ M.ker_le_center (M.fund_perfect hp2 hD4 hq _ hR)
      (M.fund_perfect hp2 hD4 hq _ hS) h)
  refine ⟨![R₁.map M.ψ, R₂.map M.ψ, R₃.map M.ψ], ?_, ?_, ?_⟩
  · intro i
    fin_cases i
    · exact M.map_mem (hcls h₁)
    · exact M.map_mem (hcls h₂)
    · exact M.map_mem (hcls h₃)
  · intro i j hij
    fin_cases i <;> fin_cases j
    · rfl
    · exact absurd hij (key h₁ h₂ h12)
    · exact absurd hij (key h₁ h₃ h13)
    · exact absurd hij.symm (key h₁ h₂ h12)
    · rfl
    · exact absurd hij (key h₂ h₃ h23)
    · exact absurd hij.symm (key h₁ h₃ h13)
    · exact absurd hij.symm (key h₂ h₃ h23)
    · rfl
  · intro i j hij a ha b hb
    fin_cases i <;> fin_cases j
    · exact absurd rfl hij
    · exact ih8_commutes_map M.ψ c12 a ha b hb
    · exact ih8_commutes_map M.ψ c13 a ha b hb
    · exact (ih8_commutes_map M.ψ c12).symm a ha b hb
    · exact absurd rfl hij
    · exact ih8_commutes_map M.ψ c23 a ha b hb
    · exact (ih8_commutes_map M.ψ c13).symm a ha b hb
    · exact (ih8_commutes_map M.ψ c23).symm a ha b hb
    · exact absurd rfl hij

theorem shapeTriple_of_large {π : Bool} (M : Ih8Model p f Ω t k e) (hp2 : p ≠ 2)
    (hq : 5 ≤ p ^ f) (hne : Ω.Nonempty) (htop : (⊤ : Subgroup G) ∉ Ω)
    (hlarge : muKind π t k = .large) : ShapeTriple Ω := by
  have hG2 : t ≠ .G2 := by
    rintro rfl
    obtain ⟨rfl, -⟩ := M.admissible.2.2
    cases π <;> simp [muKind] at hlarge
  have hD4 : t ≠ .trialityD4 := by
    rintro rfl
    obtain rfl : k = 0 := M.admissible.2.2
    cases π <;> simp [muKind] at hlarge
  exact shapeTriple_of_datum M hp2 hq hne hG2 hD4
    (threeOrth_of_large (π := π) M.isFundTag M.admissible (M.not_psl_two_sect hp2 hne htop) hlarge)

end Fund

end MuTab

end CFSG.ClassicalInvolution.Asc77
