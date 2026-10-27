module

public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81NineThreeListOf
import CFSG.RankThree.PartOne.K159.PerfNormalizer
import CFSG.LocalAnalysis.AGLEmbedding.CaseTwoNTwoAClassAux

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.Hyp111

open CFSG.Open CFSG.AGLEmbedding CFSG.RankThreeCoreUniqueness.Helpers
open scoped commutatorElement

section Abstract

variable {X : Type} [Group X] [Finite X]

theorem eq_or_eq_of_isComponentOf_le_sup {L₀ L₁ J : Subgroup X} (h₀ : IsComponentOf L₀ ⊤)
    (h₁ : IsComponentOf L₁ ⊤) (hne : L₀ ≠ L₁) (hZ₀ : Subgroup.center L₀ = ⊥)
    (hZ₁ : Subgroup.center L₁ = ⊥) (hJ : IsComponentOf J ⊤) (hJle : J ≤ L₀ ⊔ L₁) :
    J = L₀ ∨ J = L₁ := by
  by_contra h
  push Not at h
  obtain ⟨hJ₀, hJ₁⟩ := h
  have hZ := center_sup_eq_bot_of_le_centralizer
    (le_centralizer_of_component_ne h₁ h₀ (Ne.symm hne)) hZ₀ hZ₁
  have hJC : ∀ j ∈ J, ∀ y ∈ L₀ ⊔ L₁, y * j = j * y := by
    intro j hj y hy
    have hc : L₀ ⊔ L₁ ≤ Subgroup.centralizer (J : Set X) :=
      sup_le (le_centralizer_of_component_ne h₀ hJ (Ne.symm hJ₀))
        (le_centralizer_of_component_ne h₁ hJ (Ne.symm hJ₁))
    exact (Subgroup.mem_centralizer_iff.mp (hc hy) j hj).symm
  have hJbot : J = ⊥ := by
    rw [eq_bot_iff]
    intro j hj
    have hjc : (⟨j, hJle hj⟩ : (L₀ ⊔ L₁ : Subgroup X)) ∈ Subgroup.center (L₀ ⊔ L₁ : Subgroup X) :=
      Subgroup.mem_center_iff.mpr fun y => Subtype.ext (hJC j hj y y.2)
    rw [hZ, Subgroup.mem_bot] at hjc
    exact Subgroup.mem_bot.mpr (congrArg Subtype.val hjc)
  have hnt : Nontrivial J := by
    have : Nontrivial (J ⧸ Subgroup.center J) := hJ.2.2.2.toNontrivial
    exact (QuotientGroup.mk'_surjective (Subgroup.center J)).nontrivial
  obtain ⟨x, hx⟩ := exists_ne (1 : J)
  apply hx
  have hx' : (x : X) ∈ (⊥ : Subgroup X) := by
    rw [← hJbot]
    exact x.2
  exact Subtype.ext (Subgroup.mem_bot.mp hx')

end Abstract

variable {G : Type} [Group G] [Finite G]

theorem isSimpleGroup_catalog_of_component (h31 : KFactThreeOne) (hKP : CFSG.Open.IsKProper G)
    {p : ℕ} {P : Sylow p G} {M H₁ R₁ : Subgroup G} (he : D1Escape p P M H₁ R₁) {B N : Subgroup G}
    (hB : IsAGLQ p M B) (hBN : B ≤ N) (hNtop : N ≠ ⊤)
    {L : Subgroup (N ⧸ primeComplementCore (G := N) p)} (hL : IsComponentOf L ⊤)
    (hLX : ¬ L ≤ d1X0 p M N) :
    IsSimpleGroup L ∧ (∃ a b : L, a * b ≠ b * a) ∧ IsCatalogGroup L := by
  obtain ⟨⟨i, -, hi⟩, hZ⟩ := exists_threeOneIndex_of_component h31 hKP he hB hBN hNtop hL hLX
  haveI hs : IsSimpleGroup L := isSimpleGroup_of_center_eq_bot hL hZ
  refine ⟨hs, ?_, ⟨i, hi⟩⟩
  by_contra hab
  push Not at hab
  have hperf : commutator L = ⊤ := hL.2.2.1
  have hbot : commutator L = ⊥ := by
    rw [commutator_def, Subgroup.commutator_eq_bot_iff_le_centralizer]
    intro x _
    rw [Subgroup.mem_centralizer_iff]
    intro y _
    exact hab y x
  obtain ⟨a, b, hne⟩ := exists_pair_ne L
  apply hne
  have ha : a ∈ commutator L := hperf ▸ Subgroup.mem_top a
  have hb : b ∈ commutator L := hperf ▸ Subgroup.mem_top b
  rw [hbot, Subgroup.mem_bot] at ha hb
  rw [ha, hb]

theorem le_sup_centralizer_d1KBar_of_isPerfect (h31 : KFactThreeOne)
    (hSch : KFactCatalogSchreier) (hKP : CFSG.Open.IsKProper G) {p : ℕ} {P : Sylow p G}
    {M H₁ R₁ : Subgroup G} (he : D1Escape p P M H₁ R₁) {B N : Subgroup G} (hB : IsAGLQ p M B)
    (hBN : B ≤ N) (hNtop : N ≠ ⊤) (hK : d1KBar p M N ≠ ⊥)
    {Z : Subgroup (N ⧸ primeComplementCore (G := N) p)} (hZ : Group.IsPerfect Z) :
    Z ≤ d1KBar p M N ⊔ Subgroup.centralizer
      ((d1KBar p M N : Subgroup (N ⧸ primeComplementCore (G := N) p)) :
        Set (N ⧸ primeComplementCore (G := N) p)) := by
  set Y := N ⧸ primeComplementCore (G := N) p
  haveI hKn : (d1KBar p M N).Normal := d1KBar_normal_of_escape he hB hBN hK
  have hout : ∀ L : Subgroup Y, IsComponentOf L ⊤ → ¬ L ≤ d1X0 p M N →
      Group.IsSolvable (CFSG.ComponentClassification.OuterAutomorphisms.Outer L) := by
    intro L hL hLX
    obtain ⟨hs, hnab, hcat⟩ := isSimpleGroup_catalog_of_component h31 hKP he hB hBN hNtop hL hLX
    exact hSch L hs hnab hcat
  obtain ⟨L₀, hL₀, hL₀X, h | ⟨L₁, hL₁, hL₁X, hne, hK₀₁, -, -⟩⟩ :=
    d1KBar_eq_or_eq_sup_of_escape he hB hBN hK
  ·
    rw [h]
    have hN : Z ≤ Subgroup.normalizer ((L₀ : Subgroup Y) : Set Y) := by
      rw [← h, Subgroup.normalizer_eq_top (H := d1KBar p M N)]
      exact le_top
    exact CFSG.RankThree.PartOne.K159.le_sup_centralizer_of_outer_solvable hZ hN (hout L₀ hL₀ hL₀X)
  have hZ₀ := (exists_threeOneIndex_of_component h31 hKP he hB hBN hNtop hL₀ hL₀X).2
  have hZ₁ := (exists_threeOneIndex_of_component h31 hKP he hB hBN hNtop hL₁ hL₁X).2
  have hperm : ∀ (g : Y) (L : Subgroup Y), (L = L₀ ∨ L = L₁) →
      L.map (MulAut.conj g).toMonoidHom = L₀ ∨ L.map (MulAut.conj g).toMonoidHom = L₁ := by
    intro g L hL
    have hLc : IsComponentOf L ⊤ := by rcases hL with rfl | rfl <;> assumption
    have hgc : IsComponentOf (L.map (MulAut.conj g).toMonoidHom) ⊤ :=
      (CFSG.ComponentClassification.LocalComponents.equiv_iff (MulAut.conj g) L).mpr hLc
    have hLK : L ≤ d1KBar p M N := by
      rcases hL with rfl | rfl
      · exact hK₀₁ ▸ le_sup_left
      · exact hK₀₁ ▸ le_sup_right
    have hgK : L.map (MulAut.conj g).toMonoidHom ≤ L₀ ⊔ L₁ := by
      rw [← hK₀₁]
      rintro _ ⟨x, hx, rfl⟩
      exact hKn.conj_mem x (hLK hx) g
    exact eq_or_eq_of_isComponentOf_le_sup hL₀ hL₁ hne hZ₀ hZ₁ hgc hgK
  have hmap : ∀ (k : Y) (A B : Subgroup Y), A.map (MulAut.conj k).toMonoidHom = B →
      (∀ x ∈ A, k * x * k⁻¹ ∈ B) ∧ (∀ x ∈ B, k⁻¹ * x * k ∈ A) := by
    intro k A B e
    refine ⟨fun x hx => e ▸ ⟨x, hx, rfl⟩, fun x hx => ?_⟩
    rw [← e] at hx
    obtain ⟨y, hy, rfl⟩ := hx
    simpa [mul_assoc] using hy
  have hswap : ∀ g : Y, (L₀.map (MulAut.conj g).toMonoidHom = L₀ ∧
        L₁.map (MulAut.conj g).toMonoidHom = L₁) ∨
      (L₀.map (MulAut.conj g).toMonoidHom = L₁ ∧ L₁.map (MulAut.conj g).toMonoidHom = L₀) := by
    intro g
    have hinj : ∀ {A B C : Subgroup Y}, A.map (MulAut.conj g).toMonoidHom = C →
        B.map (MulAut.conj g).toMonoidHom = C → A = B := by
      intro A B C eA eB
      refine le_antisymm (fun x hx => ?_) (fun x hx => ?_)
      · have := (hmap g B C eB).2 _ ((hmap g A C eA).1 x hx)
        simpa [mul_assoc] using this
      · have := (hmap g A C eA).2 _ ((hmap g B C eB).1 x hx)
        simpa [mul_assoc] using this
    rcases hperm g L₀ (Or.inl rfl) with h0 | h0 <;> rcases hperm g L₁ (Or.inr rfl) with h1 | h1
    · exact absurd (hinj h0 h1) hne
    · exact Or.inl ⟨h0, h1⟩
    · exact Or.inr ⟨h0, h1⟩
    · exact absurd (hinj h0 h1) hne
  have hcomm : ∀ g h : Y, ∀ (i : Fin 2), ∀ x ∈ (if i = 0 then L₀ else L₁),
      ⁅g, h⁆ * x * ⁅g, h⁆⁻¹ ∈ (if i = 0 then L₀ else L₁) := by
    intro g h i x hx
    have e : ⁅g, h⁆ * x * ⁅g, h⁆⁻¹ = g * (h * (g⁻¹ * (h⁻¹ * x * h) * g) * h⁻¹) * g⁻¹ := by
      rw [commutatorElement_def]
      group
    rw [e]
    fin_cases i
    · simp only [Fin.zero_eta, Fin.isValue, ↓reduceIte] at hx ⊢
      rcases hswap g with ⟨g0, g1⟩ | ⟨g0, g1⟩ <;> rcases hswap h with ⟨h0, h1⟩ | ⟨h0, h1⟩
      · exact (hmap g _ _ g0).1 _ ((hmap h _ _ h0).1 _
          ((hmap g _ _ g0).2 _ ((hmap h _ _ h0).2 _ hx)))
      · exact (hmap g _ _ g0).1 _ ((hmap h _ _ h1).1 _
          ((hmap g _ _ g1).2 _ ((hmap h _ _ h1).2 _ hx)))
      · exact (hmap g _ _ g1).1 _ ((hmap h _ _ h1).1 _
          ((hmap g _ _ g1).2 _ ((hmap h _ _ h0).2 _ hx)))
      · exact (hmap g _ _ g1).1 _ ((hmap h _ _ h0).1 _
          ((hmap g _ _ g0).2 _ ((hmap h _ _ h1).2 _ hx)))
    · simp only [Fin.mk_one, Fin.isValue, one_ne_zero, ↓reduceIte] at hx ⊢
      rcases hswap g with ⟨g0, g1⟩ | ⟨g0, g1⟩ <;> rcases hswap h with ⟨h0, h1⟩ | ⟨h0, h1⟩
      · exact (hmap g _ _ g1).1 _ ((hmap h _ _ h1).1 _
          ((hmap g _ _ g1).2 _ ((hmap h _ _ h1).2 _ hx)))
      · exact (hmap g _ _ g1).1 _ ((hmap h _ _ h0).1 _
          ((hmap g _ _ g0).2 _ ((hmap h _ _ h0).2 _ hx)))
      · exact (hmap g _ _ g0).1 _ ((hmap h _ _ h0).1 _
          ((hmap g _ _ g0).2 _ ((hmap h _ _ h1).2 _ hx)))
      · exact (hmap g _ _ g0).1 _ ((hmap h _ _ h1).1 _
          ((hmap g _ _ g1).2 _ ((hmap h _ _ h0).2 _ hx)))
  have hZN : ∀ L : Subgroup Y, (L = L₀ ∨ L = L₁) → Z ≤ Subgroup.normalizer (L : Set Y) := by
    intro L hL
    have hperf : ⁅Z, Z⁆ = Z := Subgroup.isPerfect_iff.mp hZ
    rw [← hperf, Subgroup.commutator_le]
    intro g _ h _
    apply Subgroup.mem_normalizer_fintype
    intro x hx
    rcases hL with rfl | rfl
    · exact hcomm g h 0 x hx
    · exact hcomm g h 1 x hx
  have h0 := CFSG.RankThree.PartOne.K159.le_sup_centralizer_of_outer_solvable hZ
    (hZN L₀ (Or.inl rfl)) (hout L₀ hL₀ hL₀X)
  have h1 := CFSG.RankThree.PartOne.K159.le_sup_centralizer_of_outer_solvable hZ
    (hZN L₁ (Or.inr rfl)) (hout L₁ hL₁ hL₁X)
  have h₁₀ := le_centralizer_of_component_ne hL₁ hL₀ (Ne.symm hne)
  have h₀₁ := le_centralizer_of_component_ne hL₀ hL₁ hne
  have hdec : ∀ L : Subgroup Y, ∀ z ∈ L ⊔ Subgroup.centralizer (L : Set Y),
      ∃ a ∈ L, ∃ c ∈ Subgroup.centralizer (L : Set Y), z = a * c := by
    intro L z hz
    have hcomm : ∀ (a : L) (c : Subgroup.centralizer (L : Set Y)),
        Commute (L.subtype a) ((Subgroup.centralizer (L : Set Y)).subtype c) := fun a c =>
      (Subgroup.mem_centralizer_iff.mp c.2 a a.2)
    have hrange : (MonoidHom.noncommCoprod L.subtype
        (Subgroup.centralizer (L : Set Y)).subtype hcomm).range =
        L ⊔ Subgroup.centralizer (L : Set Y) := by
      rw [MonoidHom.noncommCoprod_range, Subgroup.range_subtype, Subgroup.range_subtype]
    obtain ⟨⟨a, c⟩, hac⟩ : z ∈ (MonoidHom.noncommCoprod L.subtype
        (Subgroup.centralizer (L : Set Y)).subtype hcomm).range := hrange ▸ hz
    rw [MonoidHom.noncommCoprod_apply] at hac
    exact ⟨a, a.2, c, c.2, by simpa using hac.symm⟩
  rw [hK₀₁]
  intro z hz
  obtain ⟨a, ha, c, hc, rfl⟩ := hdec L₀ _ (h0 hz)
  obtain ⟨b, hb, d, hd, hbd⟩ := hdec L₁ _ (h1 hz)
  have hab : a⁻¹ * b = b * a⁻¹ :=
    (Subgroup.mem_centralizer_iff.mp (h₀₁ (L₀.inv_mem ha)) b hb).symm
  set e := a⁻¹ * d with he
  have hce : c = b * e := by
    calc c = a⁻¹ * (a * c) := by group
      _ = a⁻¹ * (b * d) := by rw [hbd]
      _ = b * (a⁻¹ * d) := by rw [← mul_assoc, hab, mul_assoc]
  have he₁ : e ∈ Subgroup.centralizer (L₁ : Set Y) :=
    Subgroup.mul_mem _ (h₀₁ (L₀.inv_mem ha)) hd
  have he₀ : e ∈ Subgroup.centralizer (L₀ : Set Y) := by
    have : e = b⁻¹ * c := by rw [hce]; group
    rw [this]
    exact Subgroup.mul_mem _ (Subgroup.inv_mem _ (h₁₀ hb)) hc
  have heC : e ∈ Subgroup.centralizer ((L₀ ⊔ L₁ : Subgroup Y) : Set Y) := by
    have hle : Subgroup.zpowers e ≤ Subgroup.centralizer ((L₀ ⊔ L₁ : Subgroup Y) : Set Y) := by
      rw [Subgroup.le_centralizer_iff]
      refine sup_le ?_ ?_
      · rw [← Subgroup.le_centralizer_iff]
        exact Subgroup.zpowers_le.mpr he₀
      · rw [← Subgroup.le_centralizer_iff]
        exact Subgroup.zpowers_le.mpr he₁
    exact hle (Subgroup.mem_zpowers e)
  rw [hce, ← mul_assoc]
  exact Subgroup.mul_mem _ (Subgroup.mem_sup_left (Subgroup.mul_mem _
    (Subgroup.mem_sup_left ha) (Subgroup.mem_sup_right hb))) (Subgroup.mem_sup_right heC)

end CFSG.LocalAnalysis.RankThreeTheoremC.Hyp111
