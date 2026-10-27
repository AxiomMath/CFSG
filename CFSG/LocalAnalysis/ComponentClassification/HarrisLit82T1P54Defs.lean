module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1P54Frame
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitLemma47Inputs

public noncomputable section

namespace CFSG.ComponentClassification.HarrisLit.T1.P54

open CFSG Subgroup Assembly.LowTwoRank

theorem isSLTwoOver_of_mulEquiv {q : ℕ} {A B : Type} [Group A] [Group B] (e : A ≃* B)
    (h : IsSLTwoOver q A) : IsSLTwoOver q B := by
  obtain ⟨F, i₁, i₂, hF, ⟨eF⟩⟩ := h
  exact ⟨F, i₁, i₂, hF, ⟨e.symm.trans eF⟩⟩

theorem exists_orderOf_eq_two_pow {G : Type*} [Group G] {t : G} (ht : t * t = 1) :
    ∃ k : ℕ, orderOf t = 2 ^ k := by
  have h : orderOf t ∣ 2 ^ 1 := orderOf_dvd_of_pow_eq_one (by rw [pow_one, sq, ht])
  obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp h
  exact ⟨k, hk⟩

@[expose] def Concl (p f : ℕ) (Y : Type) [Group Y] (t : Y) : Prop :=
  ∃ u : Y, orderOf u = 2 ∧ u ∉ Open.fusionZStar Y ∧ ∃ J₁ J₂ : Subgroup Y,
    IsTwoComponentIn J₁ (centralizer {u}) ∧ IsTwoComponentIn J₂ (centralizer {u}) ∧ J₁ ≠ J₂ ∧
    u ∈ J₁ ∧ IsSLTwoOver (p ^ f) (↥J₁ ⧸ pPrimeCore 2 ↥J₁) ∧
    (∃ (τ' : StatedLieTag) (n' : ℕ),
      Blueprint.LieModel (↥J₂ ⧸ Open.fusionZStar ↥J₂) τ' n' p f) ∧
    (t ∈ J₂ ∨ t * u ∈ J₂)

variable {X B : Type} [Group X] [Group B] [Finite X] [Finite B] {φ : X →* B}

theorem Concl.map (hφ : Function.Surjective φ) (hk : ¬ 2 ∣ Nat.card φ.ker) {p f : ℕ} {t : X}
    (h : Concl p f X t) : Concl p f B (φ t) := by
  obtain ⟨u, hu2, huZ, J₁, J₂, hJ₁, hJ₂, hne, huJ, hs, ⟨τ', n', hlie⟩, ht⟩ := h
  have huu : u * u = 1 := by rw [← sq, ← hu2, pow_orderOf_eq_one]
  obtain ⟨⟨e₁⟩, -⟩ := Frame.nonempty_quot_equivs_of_map_eq hk (J := J₁) rfl
  obtain ⟨-, ⟨e₂⟩⟩ := Frame.nonempty_quot_equivs_of_map_eq hk (J := J₂) rfl
  refine ⟨φ u, Frame.orderOf_map_eq_two hk hu2,
    fun h => huZ ((Frame.mem_fusionZStar_iff_map hφ hk).mpr h), J₁.map φ, J₂.map φ,
    Frame.map_twoComponent hφ hk huu hJ₁, Frame.map_twoComponent hφ hk huu hJ₂,
    fun h => hne (Frame.eq_of_map_eq hk hJ₁ hJ₂ h), mem_map_of_mem φ huJ,
    isSLTwoOver_of_mulEquiv e₁ hs, ⟨τ', n', GSThmB.OddQuot.lieModel_of_equiv e₂ hlie⟩, ?_⟩
  rcases ht with ht | ht
  · exact .inl (mem_map_of_mem φ ht)
  · refine .inr ?_
    rw [← map_mul]
    exact mem_map_of_mem φ ht

theorem Concl.of_map (hφ : Function.Surjective φ) (hk : ¬ 2 ∣ Nat.card φ.ker) {p f : ℕ} {t : X}
    (ht : t * t = 1) (htZ : φ t ∈ center B) (h : Concl p f B (φ t)) : Concl p f X t := by
  obtain ⟨b, hb2, hbZ, Y₁, Y₂, hY₁, hY₂, hne, hbY, hs, ⟨τ', n', hlie⟩, htY⟩ := h
  obtain ⟨u, hu2, rfl, hut⟩ := Frame.exists_involution_lift_commute hφ hk ht htZ hb2
  have huu : u * u = 1 := by rw [← sq, ← hu2, pow_orderOf_eq_one]
  obtain ⟨J₁, hJ₁, hJY₁, hmem₁, ⟨e₁⟩, -⟩ := Frame.exists_lift_twoComponent hφ hk huu hY₁
  obtain ⟨J₂, hJ₂, hJY₂, hmem₂, -, ⟨e₂⟩⟩ := Frame.exists_lift_twoComponent hφ hk huu hY₂
  have htu : t ∈ centralizer ({u} : Set X) := mem_centralizer_singleton_iff.mpr hut.symm
  have huc : u ∈ centralizer ({u} : Set X) := mem_centralizer_singleton_iff.mpr rfl
  refine ⟨u, hu2, fun h => hbZ ((Frame.mem_fusionZStar_iff_map hφ hk).mp h), J₁, J₂, hJ₁, hJ₂,
    fun h => hne (by rw [← hJY₁, ← hJY₂, h]), hmem₁ u huc (exists_orderOf_eq_two_pow huu) hbY,
    isSLTwoOver_of_mulEquiv e₁.symm hs, ⟨τ', n', GSThmB.OddQuot.lieModel_of_equiv e₂.symm hlie⟩,
    ?_⟩
  rcases htY with h1 | h1
  · exact .inl (hmem₂ t htu (exists_orderOf_eq_two_pow ht) h1)
  · refine .inr (hmem₂ (t * u) (mul_mem htu huc) (exists_orderOf_eq_two_pow ?_) ?_)
    · calc t * u * (t * u) = t * (u * t) * u := by group
        _ = t * (t * u) * u := by rw [hut]
        _ = 1 := by rw [← mul_assoc, ht, one_mul, huu]
    · rw [map_mul]
      exact h1

@[expose] def HatFor (R : StatedLieTag → ℕ → Prop) : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y], IsQuasisimple Y → IsPGroup 2 (center Y) →
    ∀ p : ℕ, p.Prime → p ≠ 2 → ∀ (τ : StatedLieTag) (n f : ℕ), R τ n →
    Blueprint.LieModel (Y ⧸ center Y) τ n p f → 5 ≤ p ^ f →
    ¬ Blueprint.LieModel (Y ⧸ center Y) .PSL 2 p f →
    (∀ m r : ℕ, 0 < m → 0 < r →
      (Blueprint.LieModel (Y ⧸ center Y) .PSL (2 * m) p r ∨
        Blueprint.LieModel (Y ⧸ center Y) .PSU (2 * m) p r) →
      Nat.card (center Y) = ordProj[2] (Nat.card (Open.griessHopfMultiplier (Y ⧸ center Y)))) →
    ∀ t : Y, orderOf t = 2 → t ∈ center Y → Concl p f Y t

@[expose] def oddR (τ : StatedLieTag) (n : ℕ) : Prop :=
  ((τ = .PSL ∨ τ = .PSU) ∧ Odd n) ∨ τ = .G2 ∨ τ = .F4 ∨ τ = .E6 ∨ τ = .E8 ∨
    τ = .twistedE6 ∨ τ = .trialityD4 ∨ τ = .twistedG2 ∨ τ = .twistedB2 ∨ τ = .twistedF4 ∨
    τ = .Tits

@[expose] def RowOdd : Prop := HatFor oddR

@[expose] def RowB : Prop := HatFor fun τ _ => τ = .POmegaOdd

@[expose] def RowSp : Prop := HatFor fun τ _ => τ = .PSp

@[expose] def RowSL : Prop := HatFor fun τ n => τ = .PSL ∧ Even n

@[expose] def RowSU : Prop := HatFor fun τ n => τ = .PSU ∧ Even n

@[expose] def RowD : Prop := HatFor fun τ _ => τ = .POmegaPlus ∨ τ = .POmegaMinus

@[expose] def RowE7 : Prop := HatFor fun τ _ => τ = .E7

theorem hatFor_of_rows (hO : RowOdd) (hB : RowB) (hSp : RowSp) (hSL : RowSL) (hSU : RowSU)
    (hD : RowD) (hE7 : RowE7) : HatFor fun _ _ => True := by
  intro Y _ _ hq hZ p hp hp2 τ n f _ hlie h5 hpsl hc t ht htZ
  have key : ∀ R : StatedLieTag → ℕ → Prop, HatFor R → R τ n → Concl p f Y t :=
    fun R hR hRτ => hR Y hq hZ p hp hp2 τ n f hRτ hlie h5 hpsl hc t ht htZ
  rcases Nat.even_or_odd n with hn | hn <;> cases τ
  all_goals first
    | exact key _ hB rfl
    | exact key _ hSp rfl
    | exact key _ hSL ⟨rfl, hn⟩
    | exact key _ hSU ⟨rfl, hn⟩
    | exact key _ hD (.inl rfl)
    | exact key _ hD (.inr rfl)
    | exact key _ hE7 rfl
    | exact key _ hO (.inl ⟨.inl rfl, hn⟩)
    | exact key _ hO (.inl ⟨.inr rfl, hn⟩)
    | exact key _ hO (by unfold oddR; simp)

end CFSG.ComponentClassification.HarrisLit.T1.P54
