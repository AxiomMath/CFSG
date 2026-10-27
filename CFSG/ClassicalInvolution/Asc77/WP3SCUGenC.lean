module

public import CFSG.ClassicalInvolution.Asc77.WP3SCUGenB

public section

namespace CFSG.ClassicalInvolution.Asc77

open Matrix CFSG CFSG.Open CFSG.ComponentClassification CFSG.ClassicalInvolution
  CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Generic.DeltaClosure
  CFSG.ClassicalInvolution.Balance CFSG.ClassicalInvolution.Balance.Bootstrap
  CFSG.ClassicalInvolution.Balance.StrongBalance
  CFSG.ClassicalInvolution.Balance.StrongBalance.Unitary
  CFSG.ClassicalInvolution.Asc77.ExactLayer CFSG.ClassicalInvolution.Disconnected
open CFSG.Assembly.LowTwoRank CFSG.LieType.BorelTits CFSG.ClassicalInvolution.Phan
open CFSG.ClassicalInvolution.Models (signOf)

@[expose] def SuPairGen : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (e n : ℕ), p ≠ 2 → 5 ≤ p ^ e → 3 ≤ n →
    (⨆ (i : Fin n) (j : Fin n) (_ : i ≠ j),
      coordBlockSU (GaloisField p (2 * e)) p e ({i, j} : Finset (Fin n))) = ⊤

section Cover

variable {K : Type} [Field K] [Finite K] {n : ℕ} {p f : ℕ} [Fact p.Prime] [CharP K p]
  {X : Type} [Group X]

theorem comm_of_mem_pairBlock {d : Fin n → K} {D : Matrix (Fin n) (Fin n) K}
    (hD : D = diagonal d) {i j : Fin n} (hij : d i = d j) {s : Su K p f n}
    (hs : s ∈ coordBlockSU K p f ({i, j} : Finset (Fin n))) :
    D * ((s : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
      ((s : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) * D := by
  rw [mem_coordBlockSU_iff] at hs
  rw [hD]
  ext a b
  rw [diagonal_mul, mul_diagonal]
  by_cases hab : a ∈ ({i, j} : Finset (Fin n)) ∧ b ∈ ({i, j} : Finset (Fin n))
  · have hda : d a = d i := by
      rcases Finset.mem_insert.mp hab.1 with rfl | h
      · rfl
      · rw [Finset.mem_singleton.mp h]; exact hij.symm
    have hdb : d b = d i := by
      rcases Finset.mem_insert.mp hab.2 with rfl | h
      · rfl
      · rw [Finset.mem_singleton.mp h]; exact hij.symm
    rw [hda, hdb]
    ring
  · have hor : a ∉ ({i, j} : Finset (Fin n)) ∨ b ∉ ({i, j} : Finset (Fin n)) := by tauto
    rw [hs a b hor]
    by_cases h : a = b
    · subst h
      simp
    · simp [h]

theorem mem_of_chart_cover_su
    (hgen : (⨆ (i : Fin n) (j : Fin n) (_ : i ≠ j),
      coordBlockSU K p f ({i, j} : Finset (Fin n))) = ⊤)
    (ψ : Su K p f n →* X) (P₀ : Su K p f n)
    (D₁ D₂ : GUid (unitaryInvolution K p f) n) (σ₁ σ₂ : Fin n → Bool)
    (hD₁ : ((D₁ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
      diagonal fun i => signOf K (σ₁ i))
    (hD₂ : ((D₂ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
      diagonal fun i => signOf K (σ₂ i)) {f₁ f₂ : X}
    (h₁ : ∀ y, f₁ * (ψ.comp (MulAut.conj P₀).toMonoidHom) y * f₁⁻¹ =
      (ψ.comp (MulAut.conj P₀).toMonoidHom) (conjSUid (unitaryInvolution K p f) n D₁ y))
    (h₂ : ∀ y, f₂ * (ψ.comp (MulAut.conj P₀).toMonoidHom) y * f₂⁻¹ =
      (ψ.comp (MulAut.conj P₀).toMonoidHom) (conjSUid (unitaryInvolution K p f) n D₂ y))
    {W : Subgroup X}
    (hW : ∀ x ∈ ψ.range, (x * f₁ = f₁ * x ∨ x * f₂ = f₂ * x ∨ x * (f₁ * f₂) = (f₁ * f₂) * x) →
      x ∈ W) : ψ.range ≤ W := by
  set Ψ := ψ.comp (MulAut.conj P₀).toMonoidHom with hΨ
  have hΨrange : ∀ y, Ψ y ∈ ψ.range := fun y => ⟨P₀ * y * P₀⁻¹, rfl⟩
  have hfix : ∀ (D : GUid (unitaryInvolution K p f) n) (d : Fin n → K) (s : Su K p f n),
      ((D : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = diagonal d →
      ((D : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) * ((s : GL (Fin n) K) :
        Matrix (Fin n) (Fin n) K) = ((s : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
        ((D : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) →
      conjSUid (unitaryInvolution K p f) n D s = s := fun D d s _ hcomm =>
    (fixed_iff_comm (δ := conjSUid (unitaryInvolution K p f) n D) (D := (D : GL (Fin n) K))
      (fun y => coe_conjSUid _ n D y) s).mpr hcomm
  have hpair : ∀ (i j : Fin n), i ≠ j → ∀ s ∈ coordBlockSU K p f ({i, j} : Finset (Fin n)),
      Ψ s ∈ W := by
    intro i j hij s hs
    by_cases e1 : σ₁ i = σ₁ j
    · refine hW _ (hΨrange _) (Or.inl ?_)
      have hc := comm_of_mem_pairBlock hD₁ (by simp [e1]) hs
      have := hfix D₁ _ s hD₁ hc
      have h := h₁ s
      rw [this] at h
      exact (mul_inv_eq_iff_eq_mul.mp h).symm
    · by_cases e2 : σ₂ i = σ₂ j
      · refine hW _ (hΨrange _) (Or.inr (Or.inl ?_))
        have hc := comm_of_mem_pairBlock hD₂ (by simp [e2]) hs
        have := hfix D₂ _ s hD₂ hc
        have h := h₂ s
        rw [this] at h
        exact (mul_inv_eq_iff_eq_mul.mp h).symm
      · refine hW _ (hΨrange _) (Or.inr (Or.inr ?_))
        have hD₃ : (((D₁ * D₂ : GUid (unitaryInvolution K p f) n) : GL (Fin n) K) :
            Matrix (Fin n) (Fin n) K) = diagonal fun a => signOf K (decide (σ₁ a = σ₂ a)) := by
          simp only [Subgroup.coe_mul, Units.val_mul, hD₁, hD₂, diagonal_mul_diagonal]
          congr 1
          funext a
          exact signOf_mul_decide _ _
        have hc := comm_of_mem_pairBlock hD₃ (by rw [Linear.decide_eq_of_ne e1 e2]) hs
        have hfx := hfix (D₁ * D₂) _ s hD₃ hc
        have h3 : (f₁ * f₂) * Ψ s * (f₁ * f₂)⁻¹ = Ψ s := by
          have e : (f₁ * f₂) * Ψ s * (f₁ * f₂)⁻¹ = f₁ * (f₂ * Ψ s * f₂⁻¹) * f₁⁻¹ := by group
          rw [e, h₂ s, h₁, ← MulAut.mul_apply, ← map_mul, hfx]
        exact (mul_inv_eq_iff_eq_mul.mp h3).symm
  have hle : (⨆ (i : Fin n) (j : Fin n) (_ : i ≠ j),
      coordBlockSU K p f ({i, j} : Finset (Fin n))) ≤ W.comap Ψ :=
    iSup_le fun i => iSup_le fun j => iSup_le fun hij s hs => hpair i j hij s hs
  rw [hgen] at hle
  rintro _ ⟨y, rfl⟩
  have : ψ y = Ψ (P₀⁻¹ * y * P₀) := by
    simp only [hΨ, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, map_mul,
      map_inv]
    group
  rw [this]
  exact hle (Subgroup.mem_top _)

end Cover

section Comp

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {c : G}

theorem su_comp_mem_of_diag (hSU : SuPairGen) (hΩ : ConjInvariant Ω) {B : Subgroup G}
    (hB : IsElemAbelian 2 B) (hB8 : Nat.card B = 8) (hcB : c ∈ B) (hc1 : c ≠ 1)
    (hs : SecData p f c (exactFamily Ω c)) (D : LocalLieSystemAt p f (exactFamily Ω c) c)
    (j : Fin D.card) (htag : D.tag j = .PSU) (hp2 : p ≠ 2) (h5 : 5 ≤ p ^ D.exp j)
    (hdiag : ToralActionDiag 2 (D.tag j) (D.rank j) p (D.exp j) Fact.out
      (secComponentHom hs.normalizes D j) (modOdd c B)) (k : (compModel D j).K) :
    secComponentHom hs.normalizes D j k ∈ modOdd c (⨆ F ∈ signalizerFunctorEk 2 2 B,
      (Subgroup.centralizer (F : Set G) ⊓ exactLayer Ω c)) := by
  obtain ⟨ε, P, hP, hact⟩ := hdiag.2.1 htag
  have hn : 3 ≤ D.rank j := by
    have := D.admissible j
    rw [htag] at this
    exact this.2.2.1
  have hK := CFSG.ClassicalInvolution.ModelFacts.UnitaryAut.card_galoisField_two_mul_eq h5
  set ψ' := (secComponentHom hs.normalizes D j).comp ε.symm.toMonoidHom with hψ'
  have hBC : B ≤ Subgroup.centralizer ({c} : Set G) := Lemma52Proof.le_centralizer_of_mem hB hcB
  obtain ⟨e₁, he₁B, e₂, he₂B, he₁1, he₁c, he₂1, he₂c, he₁₂1, he₁₂c⟩ := exists_two_gens (c := c) hB8
  set f₁ : OddQuot c := oddQuotMk c ⟨e₁, hBC he₁B⟩ with hf₁
  set f₂ : OddQuot c := oddQuotMk c ⟨e₂, hBC he₂B⟩ with hf₂
  have hf₁B : f₁ ∈ modOdd c B := oddQuotMk_mem_modOdd he₁B (hBC he₁B)
  have hf₂B : f₂ ∈ modOdd c B := oddQuotMk_mem_modOdd he₂B (hBC he₂B)
  obtain ⟨x₁, hx₁P, hx₁sq, hx₁⟩ := hact f₁ hf₁B
  obtain ⟨x₂, hx₂P, hx₂sq, hx₂⟩ := hact f₂ hf₂B
  obtain ⟨P₀, D₁, D₂, σ₁, σ₂, hD₁, hD₂, hch₁, hch₂⟩ := exists_chart_gu hK hp2 (by omega) ψ'
    hx₁ hx₂ (by rwa [← pow_two]) (by rwa [← pow_two]) (hP x₁ hx₁P x₂ hx₂P)
  have hrange : ψ'.range = (secComponentHom hs.normalizes D j).range :=
    BootRank3.range_comp_symm ε _
  have hcover := mem_of_chart_cover_su (hSU p (D.exp j) (D.rank j) hp2 h5 hn) ψ' P₀ D₁ D₂ σ₁ σ₂
    hD₁ hD₂ hch₁ hch₂
    (W := modOdd c (⨆ F ∈ signalizerFunctorEk 2 2 B,
      (Subgroup.centralizer (F : Set G) ⊓ exactLayer Ω c))) (fun x hx hcomm => by
      have hxJ : x ∈ memberJoin (exactFamily Ω c) c :=
        range_secComponentHom_le_memberJoin hs D j (hrange ▸ hx)
      rcases hcomm with h | h | h
      · exact mem_modOdd_of_commutes_gen hΩ hB hcB hc1 he₁B he₁1 he₁c hxJ fun he => h.symm
      · exact mem_modOdd_of_commutes_gen hΩ hB hcB hc1 he₂B he₂1 he₂c hxJ fun he => h.symm
      · have hmul : oddQuotMk c ⟨e₁ * e₂, hBC (B.mul_mem he₁B he₂B)⟩ = f₁ * f₂ := by
          rw [hf₁, hf₂, ← map_mul]
          rfl
        exact mem_modOdd_of_commutes_gen hΩ hB hcB hc1 (B.mul_mem he₁B he₂B) he₁₂1 he₁₂c hxJ
          fun he => by
            have := h.symm
            rwa [← hmul] at this)
  have hmem : secComponentHom hs.normalizes D j k ∈ ψ'.range := ⟨ε k, by simp [hψ']⟩
  exact hcover hmem

theorem centralizerGenerationStar_of_diagPos (hSU : SuPairGen) (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f)
    (hΩ : ConjInvariant Ω) (hcls : ∀ K ∈ Ω, ∃ z, IsClassicalMember p f K z)
    (hc2 : IsPGroup 2 (Subgroup.zpowers c)) (hne : (tqMembers Ω c).Nonempty) {B : Subgroup G}
    (hB : IsElemAbelian 2 B) (hB8 : Nat.card B = 8) (hcB : c ∈ B) (hc1 : c ≠ 1)
    (hD : ∃ D : LocalLieSystemAt p f (exactFamily Ω c) c, ∀ j : Fin D.card,
      MovedByAll B c (secComponentHom (normalizesLayer_exactFamily hΩ) D j).range →
        (D.tag j = .PSL ∨ D.tag j = .PSU) ∧
          ToralActionDiag 2 (D.tag j) (D.rank j) p (D.exp j) Fact.out
            (secComponentHom (normalizesLayer_exactFamily hΩ) D j) (modOdd c B)) :
    CentralizerGenerationStar Ω B c := by
  obtain ⟨D, hD⟩ := hD
  have hs := secData_exactFamily hΩ hcls hc2 hne
  refine centralizerGenerationStar_of_components hs D fun j k => ?_
  by_cases hmov : MovedByAll B c (secComponentHom hs.normalizes D j).range
  · obtain ⟨htag, hdiag⟩ := hD j hmov
    have hexp : D.exp j = f := by
      rcases D.exp_eq j with h | ⟨h, -⟩
      · exact h
      · rcases htag with h' | h' <;> rw [h'] at h <;> cases h
    rcases htag with htag | htag
    · exact psl_comp_mem_of_diag hΩ hB hB8 hcB hc1 hs D j htag hp2 hdiag k
    · exact su_comp_mem_of_diag hSU hΩ hB hB8 hcB hc1 hs D j htag hp2 (by rw [hexp]; exact hq)
        hdiag k
  · exact notMoved_comp_mem hΩ hB hcB hc1 hs D j hmov k

end Comp

end CFSG.ClassicalInvolution.Asc77
