module

public import CFSG.ClassicalInvolution.RouteD.ExoticD4Graph
public import CFSG.ClassicalInvolution.RouteD.ExoticTwinProofOrthBridge
public import CFSG.ClassicalInvolution.RouteD.GapsOrthD4Centralizer
public import Certificates.Certificate45
public import Certificates.Certificate46
public import Certificates.Certificate47
public import Certificates.Certificate48
public import Certificates.Certificate49
public import Certificates.Certificate50
public import Certificates.Certificate51
public import Certificates.Certificate52
public import Certificates.Certificate53
public import Certificates.Certificate54
public import Certificates.Certificate55
public import Certificates.Certificate56
public import Certificates.Certificate57
public import Certificates.Certificate58
public import Certificates.Certificate59
public import Certificates.Certificate60
public import Certificates.Certificate61
public import Certificates.Certificate62
public import Certificates.Certificate63
public import Certificates.Certificate64
public import Certificates.Certificate65
public import Certificates.Certificate66
public import Certificates.Certificate67
public import Certificates.Certificate68
public import Certificates.Certificate69
public import Certificates.Certificate70
public import Certificates.Certificate71
public import Certificates.Certificate72
public import Certificates.Certificate73
public import Certificates.Certificate74
public import Certificates.Certificate75
public import Certificates.Certificate76
public import Certificates.Certificate77
public import Certificates.Certificate78
public import Certificates.Certificate79
public import Certificates.Certificate80
public import Certificates.Certificate81
public import Certificates.Certificate113
public import Certificates.Certificate114
public import Certificates.Certificate115
public import Certificates.Certificate116
public import Certificates.Certificate117
public import Certificates.Certificate118
public import Certificates.Certificate119
public import Certificates.Certificate120
public import Certificates.Certificate121
public import Certificates.Certificate122
public import Certificates.Certificate123

public section

namespace CFSG.ClassicalInvolution.RouteD.Exotic

open CFSG.ClassicalInvolution.Models.OrthogonalPairs CFSG.ClassicalGroups.Orthogonal QuadraticMap
open CFSG.ClassicalInvolution.Generic CFSG.Assembly.LowTwoRank CFSG.LieType.Universal
open CFSG.LieType.Universal.Spin
open CFSG.ClassicalInvolution.RouteD.Gaps (fundSet orth_or_twin finrank_negSpace
  involution_eq_of_negSpace_eq commutes_symm)

local notation "OFrame" => CFSG.ClassicalInvolution.Models.OrthogonalPairs.Frame

section Geometry

variable {K V : Type} [Field K] [Finite K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  {Q : QuadraticForm K V}

omit [FiniteDimensional K V] in
theorem commutes_of_orth_negSpace (hodd : Odd (Nat.card K)) {L L' : Subgroup (V ≃ₗ[K] V)}
    {i i' : V ≃ₗ[K] V} (h : IsFundamental Q L i) (h' : IsFundamental Q L' i')
    (horth : ∀ x ∈ negSpace i, ∀ y ∈ negSpace i', polar Q x y = 0) : Commutes L L' := by
  have h2 := IsFundamental.two_ne_zero_of_odd hodd
  obtain ⟨F, rfl, rfl⟩ := h
  obtain ⟨F', rfl, rfl⟩ := h'
  rw [negSpace_La_neg_one h2, negSpace_La_neg_one h2] at horth
  rintro _ ⟨A, rfl⟩ _ ⟨B, rfl⟩
  exact Frame.La_comm_of_orth (fun X Y => horth _ ⟨X, rfl⟩ _ ⟨Y, rfl⟩) A B

theorem negSpace_eq_orthogonal (hodd : Odd (Nat.card K)) (hQ : (polarBilin Q).Nondegenerate)
    (hdim : Module.finrank K V = 8) {L L' : Subgroup (V ≃ₗ[K] V)} {i i' : V ≃ₗ[K] V}
    (h : IsFundamental Q L i) (h' : IsFundamental Q L' i')
    (horth : ∀ x ∈ negSpace i, ∀ y ∈ negSpace i', polar Q x y = 0) :
    negSpace i' = LinearMap.BilinForm.orthogonal (polarBilin Q) (negSpace i) := by
  have hle : negSpace i' ≤ LinearMap.BilinForm.orthogonal (polarBilin Q) (negSpace i) := by
    intro y hy
    rw [LinearMap.BilinForm.mem_orthogonal_iff]
    intro x hx
    show polarBilin Q x y = 0
    rw [polarBilin_apply_apply]
    exact horth x hx y hy
  have h4 := finrank_negSpace hodd h
  have h4' := finrank_negSpace hodd h'
  have hperp := LinearMap.BilinForm.finrank_orthogonal hQ (negSpace i)
  exact Submodule.eq_of_le_of_finrank_eq hle (by omega)

theorem commuting_cases (hodd : Odd (Nat.card K)) (hQ : (polarBilin Q).Nondegenerate)
    (hdim : Module.finrank K V = 8) {L L' : Subgroup (V ≃ₗ[K] V)} {i i' : V ≃ₗ[K] V}
    (h : IsFundamental Q L i) (h' : IsFundamental Q L' i') (hc : Commutes L L') :
    i' = i ∨ negSpace i' = LinearMap.BilinForm.orthogonal (polarBilin Q) (negSpace i) :=
  (orth_or_twin hodd h h' hc).symm.imp id (negSpace_eq_orthogonal hodd hQ hdim h h')

theorem exists_k4_of_twin_pair (hodd : Odd (Nat.card K)) (hQ : (polarBilin Q).Nondegenerate)
    (hdim : Module.finrank K V = 8) {Ra Rb Rc : Subgroup (V ≃ₗ[K] V)} {ia ib ic : V ≃ₗ[K] V}
    (ha : IsFundamental Q Ra ia) (hb : IsFundamental Q Rb ib) (hc : IsFundamental Q Rc ic)
    (hab : Ra ≠ Rb) (hib : ib = ia) (hic : ic ≠ ia) (kac : Commutes Ra Rc) :
    ∃ Rd : Subgroup (V ≃ₗ[K] V), IsFundamental Q Rd ic ∧ Rd ≠ Ra ∧ Rd ≠ Rb ∧ Rd ≠ Rc ∧
      Commutes Ra Rd ∧ Commutes Rb Rd ∧ Commutes Rc Rd ∧
      ∀ R' : Subgroup (V ≃ₗ[K] V), (∃ i', IsFundamental Q R' i') →
        (Commutes Ra R' ∨ Commutes Rb R' ∨ Commutes Rc R' ∨ Commutes Rd R') →
          (R' = Ra ∨ R' = Rb ∨ R' = Rc ∨ R' = Rd) := by
  have h2 := IsFundamental.two_ne_zero_of_odd hodd
  subst hib
  obtain ⟨Rd, hd, hdc, hcd, huc⟩ := IsFundamental.exists_twin hodd hc
  obtain ⟨Rb', hb', hb'a, -, hua⟩ := IsFundamental.exists_twin hodd ha
  have hua' : ∀ L : Subgroup (V ≃ₗ[K] V), IsFundamental Q L ib → L = Ra ∨ L = Rb := by
    intro L hL
    have hRb : Rb = Rb' := (hua Rb hb).resolve_left (Ne.symm hab)
    rcases hua L hL with h | h
    · exact Or.inl h
    · exact Or.inr (h.trans hRb.symm)
  have horth : ∀ x ∈ negSpace ib, ∀ y ∈ negSpace ic, polar Q x y = 0 :=
    ((orth_or_twin hodd ha hc kac).resolve_right hic)
  have hnegc : negSpace ic = LinearMap.BilinForm.orthogonal (polarBilin Q) (negSpace ib) :=
    negSpace_eq_orthogonal hodd hQ hdim ha hc horth
  have horth' : ∀ x ∈ negSpace ic, ∀ y ∈ negSpace ib, polar Q x y = 0 := by
    intro x hx y hy
    rw [polar_comm]
    exact horth y hy x hx
  have hnega : negSpace ib = LinearMap.BilinForm.orthogonal (polarBilin Q) (negSpace ic) :=
    negSpace_eq_orthogonal hodd hQ hdim hc ha horth'
  have kad : Commutes Ra Rd := commutes_of_orth_negSpace hodd ha hd horth
  have kbd : Commutes Rb Rd := commutes_of_orth_negSpace hodd hb hd horth
  have kcd : Commutes Rc Rd := fun x hx y hy => (hcd x hx y hy)
  refine ⟨Rd, hd, ?_, ?_, hdc, kad, kbd, kcd, ?_⟩
  · intro h
    have := IsFundamental.involution_unique hodd ha (show IsFundamental Q Ra ic from h ▸ hd)
    exact hic this.symm
  · intro h
    have := IsFundamental.involution_unique hodd hb (show IsFundamental Q Rb ic from h ▸ hd)
    exact hic this.symm
  · rintro R' ⟨i', hR'⟩ hcom
    have hAB : i' = ib → R' = Ra ∨ R' = Rb := fun e => hua' R' (e ▸ hR')
    have hCD : i' = ic → R' = Rc ∨ R' = Rd := fun e => huc R' (e ▸ hR')
    have hcases : ∀ {Rj : Subgroup (V ≃ₗ[K] V)} {ij : V ≃ₗ[K] V}, IsFundamental Q Rj ij →
        Commutes Rj R' → (ij = ib ∨ ij = ic) → R' = Ra ∨ R' = Rb ∨ R' = Rc ∨ R' = Rd := by
      intro Rj ij hj hjR hij
      rcases commuting_cases hodd hQ hdim hj hR' hjR with e | e
      · rcases hij with rfl | rfl
        · exact (hAB e).imp id (fun h => Or.inl h)
        · rcases hCD e with h | h
          · exact Or.inr (Or.inr (Or.inl h))
          · exact Or.inr (Or.inr (Or.inr h))
      · rcases hij with rfl | rfl
        · have := involution_eq_of_negSpace_eq h2 hR' hc (e.trans hnegc.symm)
          rcases hCD this with h | h
          · exact Or.inr (Or.inr (Or.inl h))
          · exact Or.inr (Or.inr (Or.inr h))
        · have := involution_eq_of_negSpace_eq h2 hR' ha (e.trans hnega.symm)
          rcases hAB this with h | h
          · exact Or.inl h
          · exact Or.inr (Or.inl h)
    rcases hcom with hc' | hc' | hc' | hc'
    · exact hcases ha hc' (Or.inl rfl)
    · exact hcases hb hc' (Or.inl rfl)
    · exact hcases hc hc' (Or.inr rfl)
    · exact hcases hd hc' (Or.inr rfl)

omit [FiniteDimensional K V] in
theorem not_commutes_self (hodd : Odd (Nat.card K)) (h4 : 4 ≤ Nat.card K)
    {L : Subgroup (V ≃ₗ[K] V)} {i : V ≃ₗ[K] V} (h : IsFundamental Q L i) : ¬ Commutes L L := by
  intro hc
  have hcomm := IsFundamental.commutator_eq h4 h
  have hbot : L ≤ ⊥ := by
    rw [← hcomm]
    refine Subgroup.commutator_le.mpr fun x hx y hy => ?_
    rw [Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm]
    exact hc x hx y hy
  exact IsFundamental.ne_one hodd h (Subgroup.mem_bot.mp (hbot h.mem))

theorem exists_k4_of_three (hodd : Odd (Nat.card K)) (hQ : (polarBilin Q).Nondegenerate)
    (hdim : Module.finrank K V = 8) {R₁ R₂ R₃ : Subgroup (V ≃ₗ[K] V)}
    (h₁ : ∃ i, IsFundamental Q R₁ i) (h₂ : ∃ i, IsFundamental Q R₂ i)
    (h₃ : ∃ i, IsFundamental Q R₃ i) (n12 : R₁ ≠ R₂) (n13 : R₁ ≠ R₃) (n23 : R₂ ≠ R₃)
    (k12 : Commutes R₁ R₂) (k13 : Commutes R₁ R₃) (k23 : Commutes R₂ R₃) :
    ∃ R₄ : Subgroup (V ≃ₗ[K] V), (∃ i, IsFundamental Q R₄ i) ∧ R₄ ≠ R₁ ∧ R₄ ≠ R₂ ∧ R₄ ≠ R₃ ∧
      Commutes R₁ R₄ ∧ Commutes R₂ R₄ ∧ Commutes R₃ R₄ ∧
      ∀ R' : Subgroup (V ≃ₗ[K] V), (∃ i', IsFundamental Q R' i') →
        (Commutes R₁ R' ∨ Commutes R₂ R' ∨ Commutes R₃ R' ∨ Commutes R₄ R') →
          (R' = R₁ ∨ R' = R₂ ∨ R' = R₃ ∨ R' = R₄) := by
  obtain ⟨i₁, h₁⟩ := h₁
  obtain ⟨i₂, h₂⟩ := h₂
  obtain ⟨i₃, h₃⟩ := h₃
  have three_same : ∀ {Ra Rb Rc : Subgroup (V ≃ₗ[K] V)} {i : V ≃ₗ[K] V},
      IsFundamental Q Ra i → IsFundamental Q Rb i → IsFundamental Q Rc i → Ra ≠ Rb → Ra ≠ Rc →
        Rb ≠ Rc → False := by
    intro Ra Rb Rc i ha hb hc nab nac nbc
    obtain ⟨L', -, -, -, huniq⟩ := IsFundamental.exists_twin hodd ha
    rcases huniq Rb hb with e | e
    · exact nab e.symm
    rcases huniq Rc hc with e' | e'
    · exact nac e'.symm
    exact nbc (e.trans e'.symm)
  by_cases e12 : i₂ = i₁
  · have e3 : i₃ ≠ i₁ := fun e3 =>
      three_same h₁ (e12 ▸ h₂) (e3 ▸ h₃) n12 n13 n23
    obtain ⟨R₄, hd, d1, d2, d3, c1, c2, c3, hall⟩ :=
      exists_k4_of_twin_pair hodd hQ hdim h₁ h₂ h₃ n12 e12 e3 k13
    exact ⟨R₄, ⟨_, hd⟩, d1, d2, d3, c1, c2, c3, hall⟩
  by_cases e13 : i₃ = i₁
  · obtain ⟨R₄, hd, d1, d3, d2, c1, c3, c2, hall⟩ :=
      exists_k4_of_twin_pair hodd hQ hdim h₁ h₃ h₂ n13 e13 e12 k12
    refine ⟨R₄, ⟨_, hd⟩, d1, d2, d3, c1, c2, c3, fun R' hR' hcom => ?_⟩
    have := hall R' hR' (by tauto)
    tauto
  by_cases e23 : i₃ = i₂
  · have e21 : i₁ ≠ i₂ := fun e => e12 e.symm
    obtain ⟨R₄, hd, d2, d3, d1, c2, c3, c1, hall⟩ :=
      exists_k4_of_twin_pair hodd hQ hdim h₂ h₃ h₁ n23 e23 e21 (commutes_symm k12)
    refine ⟨R₄, ⟨_, hd⟩, d1, d2, d3, c1, c2, c3, fun R' hR' hcom => ?_⟩
    have := hall R' hR' (by tauto)
    tauto
  exfalso
  have o12 := (orth_or_twin hodd h₁ h₂ k12).resolve_right e12
  have o13 := (orth_or_twin hodd h₁ h₃ k13).resolve_right e13
  have o23 := (orth_or_twin hodd h₂ h₃ k23).resolve_right e23
  obtain ⟨F₁, rfl, rfl⟩ := h₁
  obtain ⟨F₂, rfl, rfl⟩ := h₂
  obtain ⟨F₃, rfl, rfl⟩ := h₃
  exact false_of_orth_three hdim (span_le_perp_of_negSpace hodd o12)
    (span_le_perp_of_negSpace hodd o13) (span_le_perp_of_negSpace hodd o23)

end Geometry

section Spin

variable {p f : ℕ} [Fact p.Prime]

theorem cliqueFour_fund_spin (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f) (hn3 : 3 ≤ 4)
    (hperf : ∀ R ∈ fundamentalSubgroups .POmegaPlus (plusDatum 4 (GaloisField p f) hn3),
      ⁅R, R⁆ = R) :
    CliqueFour (fun R R' : ↥(fundamentalSubgroups .POmegaPlus
        (plusDatum 4 (GaloisField p f) hn3)) => Commutes R.1 R'.1) := by
  obtain ⟨hodd, h4⟩ := ModelFacts.card_galoisField_facts hp2 hq
  have hker := ker_spinAction_le_center (quadPlus 4 (GaloisField p f))
  have hmap := (fundCorr_plus hp2 hq (le_refl 4)).1
  have hsurj := (fundCorr_plus hp2 hq (le_refl 4)).2
  have hQ := nondegenerate_polarBilin_quadPlus 4 (GaloisField p f)
  have hdim : Module.finrank (GaloisField p f) (Fin 4 ⊕ Fin 4 → GaloisField p f) = 8 := by
    rw [Module.finrank_fintype_fun_eq_card, Fintype.card_sum, Fintype.card_fin]
  have hinj : ∀ {R R' : Subgroup (spinGroup (quadPlus 4 (GaloisField p f)))},
      R ∈ fundamentalSubgroups .POmegaPlus (plusDatum 4 (GaloisField p f) hn3) →
      R' ∈ fundamentalSubgroups .POmegaPlus (plusDatum 4 (GaloisField p f) hn3) →
      R.map (spinAction (quadPlus 4 (GaloisField p f))) =
        R'.map (spinAction (quadPlus 4 (GaloisField p f))) → R = R' :=
    fun hR hR' h => ModelFacts.eq_of_map_eq_of_isPerfect _ hker (hperf _ hR) (hperf _ hR') h
  intro F₁ F₂ F₃ n12 n13 n23 c12 c13 c23
  have hc : ∀ {A B : ↥(fundamentalSubgroups .POmegaPlus (plusDatum 4 (GaloisField p f) hn3))},
      Commutes A.1 B.1 → Commutes (A.1.map (spinAction (quadPlus 4 (GaloisField p f))))
        (B.1.map (spinAction (quadPlus 4 (GaloisField p f)))) :=
    fun {A B} h => (Gaps.commutes_map_iff hker (hperf _ A.2)).mpr h
  have hne : ∀ {A B : ↥(fundamentalSubgroups .POmegaPlus (plusDatum 4 (GaloisField p f) hn3))},
      A ≠ B → A.1.map (spinAction (quadPlus 4 (GaloisField p f))) ≠
        B.1.map (spinAction (quadPlus 4 (GaloisField p f))) :=
    fun {A B} h e => h (Subtype.ext (hinj A.2 B.2 e))
  obtain ⟨R₄', ⟨i₄, h₄⟩, d1, d2, d3, k1, k2, k3, hall⟩ := exists_k4_of_three hodd hQ hdim
    (hmap _ F₁.2) (hmap _ F₂.2) (hmap _ F₃.2) (hne n12) (hne n13) (hne n23) (hc c12) (hc c13)
    (hc c23)
  obtain ⟨R₄, hR₄, hR₄π⟩ := hsurj R₄' ⟨i₄, h₄⟩
  have hfin : ∀ {A : ↥(fundamentalSubgroups .POmegaPlus (plusDatum 4 (GaloisField p f) hn3))},
      Commutes (A.1.map (spinAction (quadPlus 4 (GaloisField p f)))) R₄' → Commutes A.1 R₄ :=
    fun {A} h => (Gaps.commutes_map_iff hker (hperf _ A.2)).mp (hR₄π ▸ h)
  refine ⟨⟨R₄, hR₄⟩, ?_, ?_, ?_, hfin k1, hfin k2, hfin k3, ?_⟩
  · intro h
    exact d1 (hR₄π.symm.trans (by rw [← h]))
  · intro h
    exact d2 (hR₄π.symm.trans (by rw [← h]))
  · intro h
    exact d3 (hR₄π.symm.trans (by rw [← h]))
  · rintro ⟨R', hR'⟩ hcom
    have hcom' := Gaps.commutes_map_iff hker (hperf _ F₁.2) |>.mpr hcom
    rcases hall (R'.map (spinAction (quadPlus 4 (GaloisField p f)))) (hmap R' hR')
      (Or.inl hcom') with e | e | e | e
    · exact absurd (e ▸ hcom') (not_commutes_self hodd h4 (hmap _ F₁.2).choose_spec)
    · exact Or.inl (Subtype.ext (hinj hR' F₂.2 e))
    · exact Or.inr (Or.inl (Subtype.ext (hinj hR' F₃.2 e)))
    · exact Or.inr (Or.inr (Subtype.ext (hinj hR' hR₄ (e.trans hR₄π.symm))))

theorem cliqueFour_fund_plus_four (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f)
    (hadm : StatedLieAdmissible .POmegaPlus 4 p f) :
    CliqueFour (fun R R' : ↥(fundamentalSubgroups .POmegaPlus
        (modelUniv .POmegaPlus 4 p f Fact.out).D) => Commutes R.1 R'.1) := by
  have hn3 : 3 ≤ 4 := by omega
  have hperf : Gaps.FundPerfect .POmegaPlus (modelUniv .POmegaPlus 4 p f Fact.out).D :=
    Gaps.fundPerfect_modelUniv hp2 trivial hadm (by omega)
  have key : ∀ M : LieUniversal, M = ⟨spinGroup (quadPlus 4 (GaloisField p f)),
      plusDatum 4 (GaloisField p f) hn3⟩ → Gaps.FundPerfect .POmegaPlus M.D →
      CliqueFour (fun R R' : ↥(fundamentalSubgroups .POmegaPlus M.D) => Commutes R.1 R'.1) := by
    intro M hM hP
    subst hM
    exact cliqueFour_fund_spin hp2 hq hn3 fun R hR =>
      le_antisymm (Subgroup.commutator_le.mpr fun _ ha _ hb =>
        R.mul_mem (R.mul_mem (R.mul_mem ha hb) (R.inv_mem ha)) (R.inv_mem hb)) (hP R hR)
  exact key _ (ModelFacts.modelUniv_POmegaPlus hn3) hperf

end Spin

end CFSG.ClassicalInvolution.RouteD.Exotic
