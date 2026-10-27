module

public import CFSG.HardMathSupport.Timmesfeld.LocalTwo.LangCount
public import CFSG.RankThree.PartOne.SEITZ3.EvenFromMax
public import CFSG.HardMathSupport.Timmesfeld.LocalTwo.LangRankOneFrame

public section

namespace CFSG.HardMathSupport.Timmesfeld.LocalTwo

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.RankThree.Chevalley
  CFSG.RankThree.Classical CFSG.Timmesfeld.ExceptionalOrders
  CFSG.ComponentClassification.UnbalancedCatalog CFSG.RankThree.PartOne.SEITZ3
  CFSG.HardMathSupport.Timmesfeld.CrossChar

set_option linter.unusedSectionVars false


theorem conj_rootSL2_g2a {L : Type} [Field L] (P B : SL2 L) :
    (rootSL2 .G2 L g2a P⁻¹ * rootSL2 .G2 L g2v P⁻¹) * rootSL2 .G2 L g2a B *
      (rootSL2 .G2 L g2a P⁻¹ * rootSL2 .G2 L g2v P⁻¹)⁻¹ = rootSL2 .G2 L g2a (P⁻¹ * B * P) := by
  have hc := rootSL2_g2v_mul_rootSL2_g2a (L := L) P⁻¹ B
  rw [mul_inv_rev, ← map_inv, ← map_inv, inv_inv]
  calc rootSL2 .G2 L g2a P⁻¹ * rootSL2 .G2 L g2v P⁻¹ * rootSL2 .G2 L g2a B *
        (rootSL2 .G2 L g2v P * rootSL2 .G2 L g2a P)
      = rootSL2 .G2 L g2a P⁻¹ * (rootSL2 .G2 L g2v P⁻¹ * rootSL2 .G2 L g2a B) *
        (rootSL2 .G2 L g2v P * rootSL2 .G2 L g2a P) := by simp only [mul_assoc]
    _ = rootSL2 .G2 L g2a P⁻¹ * (rootSL2 .G2 L g2a B * rootSL2 .G2 L g2v P⁻¹) *
        (rootSL2 .G2 L g2v P * rootSL2 .G2 L g2a P) := by rw [hc]
    _ = rootSL2 .G2 L g2a P⁻¹ * rootSL2 .G2 L g2a B *
        (rootSL2 .G2 L g2v P⁻¹ * rootSL2 .G2 L g2v P) * rootSL2 .G2 L g2a P := by
      simp only [mul_assoc]
    _ = rootSL2 .G2 L g2a (P⁻¹ * B * P) := by
      rw [← map_mul (rootSL2 .G2 L g2v) P⁻¹ P, inv_mul_cancel, map_one, mul_one, ← map_mul,
        ← map_mul]

theorem conj_rootSL2_g2v {L : Type} [Field L] (P B : SL2 L) :
    (rootSL2 .G2 L g2a P⁻¹ * rootSL2 .G2 L g2v P⁻¹) * rootSL2 .G2 L g2v B *
      (rootSL2 .G2 L g2a P⁻¹ * rootSL2 .G2 L g2v P⁻¹)⁻¹ = rootSL2 .G2 L g2v (P⁻¹ * B * P) := by
  have hc := rootSL2_g2v_mul_rootSL2_g2a (L := L) (P⁻¹ * B * P) P⁻¹
  rw [mul_inv_rev, ← map_inv, ← map_inv, inv_inv]
  calc rootSL2 .G2 L g2a P⁻¹ * rootSL2 .G2 L g2v P⁻¹ * rootSL2 .G2 L g2v B *
        (rootSL2 .G2 L g2v P * rootSL2 .G2 L g2a P)
      = rootSL2 .G2 L g2a P⁻¹ * (rootSL2 .G2 L g2v P⁻¹ * rootSL2 .G2 L g2v B *
        rootSL2 .G2 L g2v P) * rootSL2 .G2 L g2a P := by simp only [mul_assoc]
    _ = rootSL2 .G2 L g2a P⁻¹ * rootSL2 .G2 L g2v (P⁻¹ * B * P) * rootSL2 .G2 L g2a P := by
      rw [← map_mul, ← map_mul]
    _ = rootSL2 .G2 L g2v (P⁻¹ * B * P) * rootSL2 .G2 L g2a P⁻¹ * rootSL2 .G2 L g2a P := by
      rw [← hc]
    _ = rootSL2 .G2 L g2v (P⁻¹ * B * P) := by
      rw [mul_assoc, ← map_mul, inv_mul_cancel, map_one, mul_one]

theorem even_G2_generation {X K₂ : Type} [Field X] [Finite X] [CharP X 2] [Field K₂]
    [Algebra X K₂] [Finite K₂] [IsSimpleGroup (adjointGroup Tag.G2 X)] (hmax : MaxSL2SL2G2)
    {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) (hpq : p ∣ Nat.card X + 1) (P : SL2 K₂)
    (g : ModGL Tag.G2 K₂)
    (hgdef : g = rootSL2 .G2 K₂ g2a P⁻¹ * rootSL2 .G2 K₂ g2v P⁻¹)
    {Γ : Subgroup (ModGL Tag.G2 K₂)} (hΓ : Γ = conjEntrywiseImage X g) (S₀ : Sylow p ↥Γ)
    (hS₀ : (S₀ : Subgroup ↥Γ) ≤ (torusGroup .G2 K₂ ⊓ Γ).subgroupOf Γ)
    (hTcomm : ∀ x ∈ torusGroup .G2 K₂, ∀ y ∈ torusGroup .G2 K₂, x * y = y * x)
    {E : Subgroup (ModGL Tag.G2 K₂)}
    (hEmem : ∀ h, h ∈ E ↔ h ∈ torusGroup .G2 K₂ ∧ h ^ p = 1)
    (hEle : E ≤ torusGroup .G2 K₂ ⊓ Γ) (hEcard : Nat.card E = p ^ 2)
    (hρ : ∀ α : Fin Tag.G2.rank → ℤ, IsRoot .G2 α → ∃ P' : GL (Fin 2) K₂,
      (rootRankOneGroup .G2 K₂ α ⊓ Γ).comap (rootSL2 .G2 K₂ α) =
        (Matrix.SpecialLinearGroup.map (algebraMap X K₂)).range.map (conjSL P') ∧
      CFSG.IsQuasisimple ↥(rootRankOneGroup .G2 K₂ α ⊓ Γ))
    (hcent : ∀ a : Fin Tag.G2.rank → K₂ˣ,
      rootDiagUnit .G2 a ∈ torusGroup .G2 K₂ ⊓ Γ → orderOf (rootDiagUnit .G2 a) = p →
      (rootCharKernel a = ∅ → Γ ⊓ Subgroup.centralizer {rootDiagUnit .G2 a} =
        torusGroup .G2 K₂ ⊓ Γ) ∧
      (rootCharKernel a ≠ ∅ → ∃ α : Fin Tag.G2.rank → ℤ, IsRoot .G2 α ∧
        rootCharKernel a = {α, -α} ∧
        ⁅Γ ⊓ Subgroup.centralizer {rootDiagUnit .G2 a},
          Γ ⊓ Subgroup.centralizer {rootDiagUnit .G2 a}⁆ =
          rootRankOneGroup .G2 K₂ α ⊓ Γ)) :
    ⨆ β : {β : Fin Tag.G2.rank → ℤ // IsRoot .G2 β}, rootRankOneGroup .G2 K₂ β.1 ⊓ Γ = Γ := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have : Finite (ModGL Tag.G2 K₂) := finite_modGL
  have hq1 : 1 ≤ Nat.card X := Nat.card_pos
  have hq4 : 4 ≤ Nat.card X := by
    have := Nat.le_of_dvd (Nat.succ_pos _) hpq
    omega
  have hinj : ∀ α, IsRoot Tag.G2 α → Function.Injective (rootSL2 .G2 K₂ α) :=
    fun α _ => rootSL2_injective_of_field α
  let ψ : ModGL Tag.G2 X →* ModGL Tag.G2 K₂ :=
    (MulAut.conj g).toMonoidHom.comp (baseChangeGL (algebraMap X K₂))
  have hψ : Function.Injective ψ :=
    (MulAut.conj g).injective.comp (baseChangeGL_injective (τ := Tag.G2) (algebraMap X K₂))
  let ε : adjointGroup Tag.G2 X ≃* Γ :=
    (Subgroup.equivMapOfInjective (adjointGroup Tag.G2 X) ψ hψ).trans
      (MulEquiv.subgroupCongr hΓ.symm)
  have hε : ∀ k : adjointGroup Tag.G2 X, ((ε k : ↥Γ) : ModGL Tag.G2 K₂) =
      g * baseChangeGL (algebraMap X K₂) (k : ModGL Tag.G2 X) * g⁻¹ := fun k => rfl
  have : IsSimpleGroup ↥Γ := MulEquiv.isSimpleGroup ε.symm
  have hcent' : ∀ a : Fin Tag.G2.rank → K₂ˣ, rootDiagUnit .G2 a ∈ torusGroup .G2 K₂ ⊓ Γ →
      orderOf (rootDiagUnit .G2 a) = p → rootCharKernel a ≠ ∅ →
        ∃ α, IsRoot .G2 α ∧ rootCharKernel a = {α, -α} ∧
          ⁅Γ ⊓ Subgroup.centralizer {rootDiagUnit .G2 a},
            Γ ⊓ Subgroup.centralizer {rootDiagUnit .G2 a}⁆ = rootRankOneGroup .G2 K₂ α ⊓ Γ :=
    fun a h1 h2 hk => (hcent a h1 h2).2 hk
  have hcomp := component_of_rankOneCentralizers hp hpq hinj hEmem hEle hρ hcent'
  have hEpow : ∀ x ∈ E, x ^ p = 1 := fun x hx => ((hEmem x).1 hx).2
  have hEcard' : p < Nat.card E := by
    rw [hEcard]
    nlinarith [hp.two_le]
  set E₁ : Subgroup ↥Γ := E.subgroupOf Γ with hE₁
  have hA : ∀ β, IsRoot .G2 β → ∀ s : ↥Γ, (s : ModGL Tag.G2 K₂) ∈ rootRankOneGroup .G2 K₂ β →
      s ∈ compSet E₁ := by
    intro β hβ s hs
    obtain ⟨a, hdE, hd1, hχ⟩ := exists_rootChar_eq_one hp (fun x hx => (hEle hx).1) hEpow
      hEcard' β
    obtain ⟨L, hRL, hLC, hLq, -, -⟩ := hcomp β hβ a hdE hd1 hχ
    have hLΓ : L ≤ Γ := hLC.trans inf_le_left
    refine ⟨⟨rootDiagUnit .G2 a, (hEle hdE).2⟩, hdE, fun h => hd1 (congrArg Subtype.val h),
      L.subgroupOf Γ, ?_, ?_, hRL ⟨hs, s.2⟩⟩
    · intro y hy
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact Subtype.ext (Subgroup.mem_centralizer_singleton_iff.1 (hLC hy).2)
    · exact CFSG.LocalCores.isQuasisimple_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hLΓ).symm hLq
  set A : Subgroup ↥Γ := (stdA1A1 X).map ε.toMonoidHom with hAdef
  set M : Subgroup ↥Γ := Subgroup.closure (compSet E₁) with hMdef
  have hAM : A ≤ M := by
    rintro _ ⟨u, ⟨⟨B1, B2⟩, rfl⟩, rfl⟩
    have e1 : a1a1Hom X (B1, B2) = a1a1Hom X (B1, 1) * a1a1Hom X (1, B2) := by
      rw [← map_mul]
      simp
    change ε (a1a1Hom X (B1, B2)) ∈ M
    rw [e1, map_mul]
    refine M.mul_mem (Subgroup.subset_closure (hA g2a isRoot_g2a _ ?_))
      (Subgroup.subset_closure (hA g2v isRoot_g2v _ ?_))
    · rw [hε, a1a1Hom_apply_inl, baseChangeGL_rootSL2_of_field, hgdef, conj_rootSL2_g2a]
      exact ⟨_, rfl⟩
    · rw [hε, a1a1Hom_apply_inr, baseChangeGL_rootSL2_of_field, hgdef, conj_rootSL2_g2v]
      exact ⟨_, rfl⟩
  have hE₁p : IsPGroup p ↥E₁ := fun x => ⟨1, by
    rw [pow_one]
    exact Subtype.ext (Subtype.ext (by simpa using hEpow _ x.2))⟩
  have hE₁N : E₁ ≤ Subgroup.normalizer (S₀ : Set ↥Γ) := fun x hx =>
    (Subgroup.centralizer_le_normalizer (S₀ : Set ↥Γ))
      (Subgroup.mem_centralizer_iff.2 fun s hs =>
        Subtype.ext (hTcomm _ (hS₀ hs).1 _ (hEle hx).1))
  have hE₁S : E₁ ≤ (S₀ : Subgroup ↥Γ) := by
    intro x hx
    have h1 := hE₁p.inf_normalizer_sylow S₀
    have h2 : x ∈ E₁ ⊓ Subgroup.normalizer (S₀ : Set ↥Γ) := ⟨hx, hE₁N hx⟩
    rw [h1] at h2
    exact h2.2
  have hnE : ∀ n ∈ Subgroup.normalizer (S₀ : Set ↥Γ), ∀ x ∈ E₁, n * x * n⁻¹ ∈ E₁ := by
    intro n hn x hx
    have h1 : n * x * n⁻¹ ∈ (S₀ : Subgroup ↥Γ) :=
      (Subgroup.mem_normalizer_iff.1 hn x).1 (hE₁S hx)
    have h2 := hS₀ h1
    have hxp : x ^ p = 1 := Subtype.ext (by simpa using hEpow _ hx)
    have h3 : ((n * x * n⁻¹ : ↥Γ) : ModGL Tag.G2 K₂) ^ p = 1 := by
      have : (n * x * n⁻¹) ^ p = 1 := by rw [conj_pow, hxp, mul_one, mul_inv_cancel]
      simpa using congrArg Subtype.val this
    exact (hEmem _).2 ⟨h2.1, h3⟩
  have hNS : ∀ n ∈ Subgroup.normalizer (S₀ : Set ↥Γ),
      n ∈ Subgroup.normalizer (M : Set ↥Γ) := fun n hn =>
    mem_normalizer_closure_compSet (hnE n hn) (hnE n⁻¹ (inv_mem hn))
  have hmax' : ∀ N : Subgroup ↥Γ, A ≤ N → N = A ∨ N = ⊤ := by
    intro N hN
    have h1 : stdA1A1 X ≤ N.comap ε.toMonoidHom := fun y hy => hN ⟨y, hy, rfl⟩
    have h2 := Subgroup.map_comap_eq_self_of_surjective
      (show Function.Surjective ε.toMonoidHom from ε.surjective) N
    rcases hmax X hq4 _ h1 with h | h
    · left
      rw [← h2, h]
    · right
      rw [← h2, h, Subgroup.map_top_of_surjective _ ε.surjective]
  have hcardM : Nat.card (stdA1A1 X) = (Nat.card X * (Nat.card X ^ 2 - 1)) ^ 2 := card_stdA1A1
  have hA1 : A ≠ ⊥ := by
    intro h
    have h0 : stdA1A1 X = ⊥ := by
      rwa [Subgroup.map_eq_bot_iff_of_injective _ ε.injective] at h
    rw [h0, Subgroup.card_bot] at hcardM
    have h16 : 16 ≤ Nat.card X ^ 2 := by nlinarith
    have h15 : 15 ≤ Nat.card X ^ 2 - 1 := by omega
    have h60 : 60 ≤ Nat.card X * (Nat.card X ^ 2 - 1) := by nlinarith
    nlinarith
  have hind : ¬ A.index ≡ 1 [MOD p] := by
    have hcardG : Nat.card (adjointGroup .G2 X) = CFSG.Open.ordG2 (Nat.card X) :=
      card_adjointGroup_G2
    have hidx : (stdA1A1 X).index =
        Nat.card X ^ 4 * ((Nat.card X ^ 2) ^ 2 + Nat.card X ^ 2 + 1) := by
      have h1 := Subgroup.index_mul_card (stdA1A1 X)
      rw [hcardM, hcardG, ordG2_eq_index_mul hq1] at h1
      have hpos : 0 < (Nat.card X * (Nat.card X ^ 2 - 1)) ^ 2 := by
        have : 0 < Nat.card X ^ 2 - 1 := by
          have : 4 ≤ Nat.card X ^ 2 := by nlinarith
          omega
        positivity
      exact Nat.eq_of_mul_eq_mul_right hpos h1
    have hAidx : A.index = (stdA1A1 X).index := Subgroup.index_map_equiv _ ε
    rw [hAidx, hidx]
    exact (not_dvd_and_not_modEq_one hp hp5 hpq).2
  have hMtop : M = ⊤ :=
    eq_top_of_normalizer_le_of_maximal A M hmax' hA1 hind hAM S₀ hNS
  have hRle : (⨆ β : {β : Fin Tag.G2.rank → ℤ // IsRoot .G2 β},
      rootRankOneGroup .G2 K₂ β.1 ⊓ Γ) ≤ Γ := iSup_le fun _ => inf_le_right
  refine le_antisymm hRle fun γ hγ => ?_
  have hγM : (⟨γ, hγ⟩ : ↥Γ) ∈ M := hMtop ▸ Subgroup.mem_top _
  have hMle : M ≤ (⨆ β : {β : Fin Tag.G2.rank → ℤ // IsRoot .G2 β},
      rootRankOneGroup .G2 K₂ β.1 ⊓ Γ).comap Γ.subtype := by
    refine (Subgroup.closure_le _).2 ?_
    rintro s ⟨x, hx, hx1, L, hLC, hLq, hsL⟩
    obtain ⟨a, ha⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup (hEle hx).1
    have hxE : (x : ModGL Tag.G2 K₂) ∈ E := hx
    have hxp : orderOf (x : ModGL Tag.G2 K₂) = p :=
      orderOf_eq_prime ((hEmem _).1 hxE).2 (fun h => hx1 (Subtype.ext h))
    have haT : rootDiagUnit .G2 a ∈ torusGroup .G2 K₂ ⊓ Γ := ha ▸ hEle hxE
    have hap : orderOf (rootDiagUnit .G2 a) = p := ha ▸ hxp
    set L' : Subgroup (ModGL Tag.G2 K₂) := L.map Γ.subtype with hL'
    have hL'q : CFSG.IsQuasisimple ↥L' :=
      CFSG.LocalCores.isQuasisimple_of_mulEquiv
        (L.equivMapOfInjective Γ.subtype Γ.subtype_injective) hLq
    have hL'D : L' ≤ Γ ⊓ Subgroup.centralizer {rootDiagUnit .G2 a} := by
      rintro _ ⟨l, hl, rfl⟩
      refine ⟨l.2, Subgroup.mem_centralizer_singleton_iff.2 ?_⟩
      have h2 := congrArg Subtype.val (Subgroup.mem_centralizer_singleton_iff.1 (hLC hl))
      have hx' : (x : ModGL Tag.G2 K₂) = rootDiagUnit .G2 a := ha
      show (l : ModGL Tag.G2 K₂) * rootDiagUnit .G2 a = rootDiagUnit .G2 a * (l : ModGL Tag.G2 K₂)
      rw [← hx']
      exact h2
    have hsL' : (s : ModGL Tag.G2 K₂) ∈ L' := ⟨s, hsL, rfl⟩
    by_cases hker : rootCharKernel a = ∅
    · exfalso
      have hD := (hcent a haT hap).1 hker
      obtain ⟨-, -, a1, b1, hne⟩ := hL'q
      induction a1 using QuotientGroup.induction_on with | H a1 => ?_
      induction b1 using QuotientGroup.induction_on with | H b1 => ?_
      apply hne
      have ha1 : (a1 : ModGL Tag.G2 K₂) ∈ torusGroup .G2 K₂ := (hD ▸ hL'D a1.2).1
      have hb1 : (b1 : ModGL Tag.G2 K₂) ∈ torusGroup .G2 K₂ := (hD ▸ hL'D b1.2).1
      rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
      exact congrArg _ (Subtype.ext (hTcomm _ ha1 _ hb1))
    · obtain ⟨α, hα, -, hc⟩ := hcent' a haT hap hker
      have hperf : ⁅L', L'⁆ = L' := Subgroup.isPerfect_iff.1 hL'q.1
      rw [← hperf] at hsL'
      have h3 := Subgroup.commutator_mono hL'D hL'D hsL'
      rw [hc] at h3
      exact Subgroup.mem_iSup_of_mem (⟨α, hα⟩ : {β : Fin Tag.G2.rank → ℤ // IsRoot .G2 β}) h3
  exact hMle hγM

end CFSG.HardMathSupport.Timmesfeld.LocalTwo
