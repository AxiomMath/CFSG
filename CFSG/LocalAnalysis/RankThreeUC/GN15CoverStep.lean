module

public import CFSG.LocalAnalysis.RankThreeUC.GN15Solv
public import CFSG.LocalAnalysis.RankThreeUC.GN15CoverDiag
public import CFSG.LocalAnalysis.RankThreeUC.GN15CoverK3

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15.GN15

open CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData CFSG.Quasithin CFSG.QuasithinUnique
  CFSG.Open CFSG.AGLEmbeddingD2.Tits.S3AmalgamBound CFSG.AGLEmbeddingD2.Tits.MsideParabolicEscape
open scoped commutatorElement

variable {X : Type} [Group X] [Finite X] {T T₁ T₂ : Subgroup X}

theorem exists_mul_gnKMin_sup_gnDPre (hJ : JOutCentralAt T) (hX : GNSetting X T) (x : X) :
    ∃ y ∈ gnKMin T ⊔ gnDPre T, ∃ n ∈ Subgroup.normalizer (thompsonJ T : Set X), x = y * n := by
  obtain ⟨w, hw, n, hn, rfl⟩ := frattini_of_normal_thompsonJ_le hX (gnWPre_normal hX)
    (thompsonJ_le_gnWPre hX) x
  have hw' := gnWPre_le_sup_normalizer hX (gnWPre_commutator_le hJ hX) hw
  have := gnQPre_sup_gnDPre_normal hX
  have := gnQPre_normal hX
  have hD : (gnDPre T).Normal := gnDPre_normal hX
  have := gnHPre_normal (T := T)
  have := gnKMin_normal (T := T)
  obtain ⟨q, hq, n₁, hn₁, rfl⟩ := Subgroup.mem_sup_of_normal_left.mp hw'
  obtain ⟨q₀, hq₀, d, hd, rfl⟩ := Subgroup.mem_sup_of_normal_left.mp hq
  obtain ⟨h, hh, n₂, hn₂, rfl⟩ :=
    Subgroup.mem_sup_of_normal_left.mp (gnQPre_le_sup_normalizer hX hq₀)
  obtain ⟨k, hk, n₃, hn₃, rfl⟩ :=
    Subgroup.mem_sup_of_normal_left.mp (gnHPre_le_gnKMin_sup_normalizer hX hh)
  refine ⟨k * (n₃ * n₂ * d * (n₃ * n₂)⁻¹), ?_, n₃ * n₂ * n₁ * n, ?_, by group⟩
  · exact mul_mem (Subgroup.mem_sup_left hk)
      (Subgroup.mem_sup_right (hD.conj_mem d hd (n₃ * n₂)))
  · exact mul_mem (mul_mem (mul_mem hn₃ hn₂) hn₁) hn

theorem cover_cases_of_le_sup_gnKThree (hI59 : AGL81I59) (hX : GNSetting X T)
    (hP : IsC118Pair T T₁ T₂) {A B : Subgroup X} (hA : A.Normal) (hB : B.Normal) (hBA : B ≤ A)
    (hCB : gnC T ≤ B) (hAK : A ≤ B ⊔ gnKThree T)
    (hchief : ∀ D : Subgroup X, D.Normal → B ≤ D → D ≤ A → D = B ∨ D = A) :
    (∀ a ∈ A, ∃ k : ℕ, a ^ 2 ^ k ∈ B) ∨ ⁅A, thompsonJ T⁆ ≤ B ∨
      ((∀ a ∈ A, ∃ k : ℕ, a ^ 3 ^ k ∈ B) ∧ ∃ x ∈ A, x ∉ B ∧ (∃ k : ℕ, orderOf x = 3 ^ k) ∧
        (x ∈ Subgroup.centralizer (T₁ : Set X) ∨ x ∈ Subgroup.normalizer (T₂ : Set X))) := by
  have := hB
  have hK₃n : (gnKThree T).Normal := gnKThree_normal
  set A₁ : Subgroup X := A ⊓ gnKThree T with hA₁
  set B₁ : Subgroup X := B ⊓ gnKThree T with hB₁
  have hA₁n : A₁.Normal := inferInstance
  have hB₁n : B₁.Normal := inferInstance
  have hB₁A₁ : B₁ ≤ A₁ := inf_le_inf_right _ hBA
  have hCB₁ : gnC T ≤ B₁ := le_inf hCB gnC_le_gnKThree
  have hdec : ∀ a ∈ A, ∃ a₁ ∈ A₁, ∃ b ∈ B, a = a₁ * b := by
    intro a ha
    obtain ⟨b', hb', k, hk, hbk⟩ := Subgroup.mem_sup_of_normal_left.mp (hAK ha)
    have hkA : k ∈ A := by
      have : k = b'⁻¹ * a := by rw [← hbk]; group
      rw [this]
      exact A.mul_mem (A.inv_mem (hBA hb')) ha
    refine ⟨k, ⟨hkA, hk⟩, k⁻¹ * b' * k, ?_, ?_⟩
    · simpa [mul_assoc] using hB.conj_mem b' hb' k⁻¹
    · rw [← hbk]; group
  have hchief₁ : ∀ D : Subgroup X, D.Normal → B₁ ≤ D → D ≤ A₁ → D = B₁ ∨ D = A₁ := by
    intro D hD hB₁D hDA₁
    have := hD
    rcases hchief (B ⊔ D) inferInstance le_sup_left
      (sup_le hBA (hDA₁.trans inf_le_left)) with h | h
    · left
      refine le_antisymm (fun x hx => ⟨?_, (hDA₁ hx).2⟩) hB₁D
      rw [← h]
      exact Subgroup.mem_sup_right hx
    · right
      refine le_antisymm hDA₁ (fun x hx => ?_)
      obtain ⟨b, hb, d, hd, hbd⟩ := Subgroup.mem_sup_of_normal_left.mp (h ▸ hx.1 : x ∈ B ⊔ D)
      have hbK : b ∈ gnKThree T := by
        have : b = x * d⁻¹ := by rw [← hbd]; group
        rw [this]
        exact (gnKThree T).mul_mem hx.2 ((gnKThree T).inv_mem (hDA₁ hd).2)
      have : x = b * d := hbd.symm
      rw [this]
      exact D.mul_mem (hB₁D ⟨hb, hbK⟩) hd
  rcases cover_cases_of_le_gnKThree hI59 hX hP hA₁n hB₁n hB₁A₁ hCB₁ inf_le_right hchief₁ with
    h | h | ⟨h3, x, hxA, hxB, hxo, hxc⟩
  · left
    intro a ha
    obtain ⟨a₁, ha₁, b, hb, rfl⟩ := hdec a ha
    obtain ⟨k, hk⟩ := h a₁ ha₁
    exact ⟨k, pow_mul_mem_of_pow_mem hB hb hk.1⟩
  · right; left
    rw [Subgroup.commutator_le]
    intro a ha j hj
    obtain ⟨a₁, ha₁, b, hb, rfl⟩ := hdec a ha
    have h1 : ⁅a₁, j⁆ ∈ B := (Subgroup.commutator_le.mp h a₁ ha₁ j hj).1
    have key : ⁅a₁ * b, j⁆ = a₁ * ⁅b, j⁆ * a₁⁻¹ * ⁅a₁, j⁆ := by
      simp only [commutatorElement_def]; group
    rw [key]
    have h2 : ⁅b, j⁆ ∈ B := by
      have : ⁅b, j⁆ = b * (j * b⁻¹ * j⁻¹) := by rw [commutatorElement_def]; group
      rw [this]
      exact B.mul_mem hb (hB.conj_mem _ (B.inv_mem hb) j)
    exact B.mul_mem (hB.conj_mem _ h2 a₁) h1
  · right; right
    refine ⟨fun a ha => ?_, x, hxA.1, fun hxB' => hxB ⟨hxB', hxA.2⟩, hxo, hxc⟩
    obtain ⟨a₁, ha₁, b, hb, rfl⟩ := hdec a ha
    obtain ⟨k, hk⟩ := h3 a₁ ha₁
    exact ⟨k, pow_mul_mem_of_pow_mem hB hb hk.1⟩

omit [Finite X] in
theorem inf_sup_normal_le {A B Y : Subgroup X} (hB : B.Normal) (hBA : B ≤ A) (hY : A ⊓ Y ≤ B) :
    A ⊓ (B ⊔ Y) ≤ B := by
  intro x hx
  obtain ⟨b, hb, y, hy, hby⟩ := Subgroup.mem_sup_of_normal_left.mp hx.2
  have hyA : y ∈ A := by
    have : y = b⁻¹ * x := by rw [← hby]; group
    rw [this]
    exact A.mul_mem (A.inv_mem (hBA hb)) hx.1
  have : x = b * y := hby.symm
  rw [this]
  exact B.mul_mem hb (hY ⟨hyA, hy⟩)

theorem cover_cases_of_chief (hI59 : AGL81I59) (hJ3 : ThreePrimeJCentral) (hJ : JOutCentralAt T)
    (hX : GNSetting X T) (hP : IsC118Pair T T₁ T₂) {A B : Subgroup X} (hA : A.Normal)
    (hB : B.Normal) (hBA : B ≤ A) (hCB : gnC T ≤ B) (hAD : A ⊓ gnDPre T ≤ B)
    (hchief : ∀ D : Subgroup X, D.Normal → B ≤ D → D ≤ A → D = B ∨ D = A) :
    A ≤ B ⊔ (A ⊓ Subgroup.centralizer (T₁ : Set X)) ∨
      A ≤ B ⊔ (A ⊓ Subgroup.normalizer (T₂ : Set X)) ∨
      ((∀ a ∈ A, ∃ k : ℕ, a ^ 3 ^ k ∈ B) ∧ ∃ x ∈ A, x ∉ B ∧ (∃ k : ℕ, orderOf x = 3 ^ k) ∧
        (x ∈ Subgroup.centralizer (T₁ : Set X) ∨ x ∈ Subgroup.normalizer (T₂ : Set X))) := by
  obtain ⟨-, h1Z, -, -, h2B, h2c, -⟩ := id hP
  have hDn : (gnDPre T).Normal := gnDPre_normal hX
  have := gnKMin_normal (T := T)
  have := hA
  have := hB
  have hfinish : ((∀ a ∈ A, ∃ k : ℕ, a ^ 2 ^ k ∈ B) ∨ ⁅A, thompsonJ T⁆ ≤ B) →
      (A ≤ B ⊔ (A ⊓ Subgroup.centralizer (T₁ : Set X)) ∨
        A ≤ B ⊔ (A ⊓ Subgroup.normalizer (T₂ : Set X)) ∨
        ((∀ a ∈ A, ∃ k : ℕ, a ^ 3 ^ k ∈ B) ∧ ∃ x ∈ A, x ∉ B ∧ (∃ k : ℕ, orderOf x = 3 ^ k) ∧
          (x ∈ Subgroup.centralizer (T₁ : Set X) ∨ x ∈ Subgroup.normalizer (T₂ : Set X)))) := by
    rintro (h2 | hc)
    · exact Or.inl (cover_of_two_group hX.sylow h1Z hA hB hBA h2)
    · rcases cover_of_chief_of_commutator_le hX.sylow h1Z h2B h2c hA hB hBA hchief hc with h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
  have hn1 : (B ⊔ (A ⊓ (gnKMin T ⊔ gnDPre T))).Normal := inferInstance
  rcases hchief _ hn1 le_sup_left (sup_le hBA inf_le_left) with h1 | h1
  ·
    have hAY := inf_sup_normal_le hB hBA (le_sup_right.trans h1.le)
    refine hfinish (commutator_le_of_chief_of_decomp hX.sylow.2.1 hA hB inferInstance hBA hchief
      hAY ?_)
    intro a ha
    obtain ⟨y, hy, n, hn, hyn⟩ := exists_mul_gnKMin_sup_gnDPre hJ hX a
    exact ⟨y, Subgroup.mem_sup_right hy, n, hn, hyn⟩
  ·
    have hAKD : A ≤ B ⊔ (gnKMin T ⊔ gnDPre T) := h1 ▸ sup_le_sup_left inf_le_right B
    have hAH : A ≤ B ⊔ gnHPre T :=
      le_sup_gnHPre_of_le_sup_gnKMin_sup_gnDPre hX hA hB hCB hAD hAKD
    have hn2 : (B ⊔ (A ⊓ gnKMin T)).Normal := inferInstance
    rcases hchief _ hn2 le_sup_left (sup_le hBA inf_le_left) with h2 | h2
    ·
      have hAY := inf_sup_normal_le hB hBA (le_sup_right.trans h2.le)
      refine hfinish (commutator_le_of_chief_of_decomp hX.sylow.2.1 hA hB inferInstance hBA
        hchief hAY ?_)
      intro a ha
      obtain ⟨b, hb, h, hh, rfl⟩ := Subgroup.mem_sup_of_normal_left.mp (hAH ha)
      obtain ⟨k, hk, n, hn, rfl⟩ := Subgroup.mem_sup_of_normal_left.mp
        (gnHPre_le_gnKMin_sup_normalizer hX hh)
      exact ⟨b * k, mul_mem (Subgroup.mem_sup_left hb) (Subgroup.mem_sup_right hk), n, hn,
        by group⟩
    ·
      have hAK₃ : A ≤ B ⊔ gnKThree T :=
        h2 ▸ sup_le_sup_left (inf_le_right.trans (gnKMin_le_gnKThree hJ3 hX)) B
      rcases cover_cases_of_le_sup_gnKThree hI59 hX hP hA hB hBA hCB hAK₃ hchief with h | h | h
      · exact hfinish (Or.inl h)
      · exact hfinish (Or.inr h)
      · exact Or.inr (Or.inr h)

end CFSG.LocalAnalysis.RankThreeUC.S15.GN15
