module

public import CFSG.LocalAnalysis.ComponentClassification.AschbacherFactsL2Model
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherFactsL2Cover
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherFactsL2Dichotomy

public section

namespace CFSG.ComponentClassification.AschbacherKnownGroup.FactsL2

open CFSG.Open CFSG.GorensteinWalter

theorem fourGroupGeneration_psl2 {Q : Type} [Group Q] [Finite Q] (hQ : HasDihedralSylowTwo Q)
    [IsSimpleGroup Q] {K : Type} [Field K] [Finite K] {p f : ℕ} (hp : p.Prime)
    (hKcard : Nat.card K = p ^ f) (hK : IsOddPrimePower (Nat.card K)) (hcard : 3 < Nat.card K)
    (eL : Q ≃* PSL2 K) {α β : MulAut Q} (hαβ : α * β = β * α) (hα2 : α ^ 2 = 1)
    (hβ2 : β ^ 2 = 1) (hα1 : α ≠ 1) (hβ1 : β ≠ 1) (hne : α ≠ β) (H : Subgroup Q)
    (hinv : ∀ γ ∈ ({α, β, α * β} : Set (MulAut Q)), ∀ x ∈ H, γ x ∈ H)
    (hP1 : ∀ γ ∈ ({α, β, α * β} : Set (MulAut Q)), ∀ x : Q, γ x = x → Odd (orderOf x) →
      x ∈ H)
    (hP2 : ∀ γ ∈ ({α, β, α * β} : Set (MulAut Q)), ∀ t : Q, t ^ 2 = 1 → t ≠ 1 →
      γ = MulAut.conj t → ∀ y : Q, t ∈ Subgroup.zpowers y → y ∈ H) :
    H = ⊤ ∨ (IsSmallDihedralSimple Q ∧ ∃ a b : Q, α = MulAut.conj a ∧ β = MulAut.conj b) := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have hQ' : HasDihedralSylowTwo (⊤ : Subgroup Q) :=
    hasDihedralSylowTwo_of_mulEquiv Subgroup.topEquiv.symm hQ
  have : IsSimpleGroup (⊤ : Subgroup Q) := Subgroup.topEquiv.isSimpleGroup
  have hcen : ∀ x : Q, (∀ y : Q, x * y = y * x) → x = 1 := fun x hx =>
    eq_one_of_mem_center_of_simple_dihedral (L := ⊤) hQ' (x := x) trivial (fun y _ => hx y)
  let c : Q →* MulAut Q := MulAut.conj
  have hcinj : Function.Injective c := by
    rw [injective_iff_map_eq_one]
    intro x hx
    apply hcen x
    intro y
    have := DFunLike.congr_fun hx y
    simp only [c, MulAut.conj_apply, MulAut.one_apply] at this
    calc x * y = x * y * x⁻¹ * x := by group
      _ = y * x := by rw [this]
  let N : Subgroup (MulAut Q) := c.range
  have hconj : ∀ (φ : MulAut Q) (x : Q), φ * c x * φ⁻¹ = c (φ x) := by
    intro φ x
    ext y
    simp [c, MulAut.conj_apply, MulAut.mul_apply]
  have hNn : N.Normal := by
    constructor
    rintro _ ⟨x, rfl⟩ φ
    exact ⟨φ x, (hconj φ x).symm⟩
  let eQ : Q ≃* N := MonoidHom.ofInjective hcinj
  have heQ : ∀ x, (eQ x : MulAut Q) = c x := fun x => MonoidHom.ofInjective_apply hcinj
  let eN : N ≃* PSL2 K := eQ.symm.trans eL
  have hC : Subgroup.centralizer (N : Set (MulAut Q)) = ⊥ := by
    rw [eq_bot_iff]
    intro φ hφ
    rw [Subgroup.mem_bot]
    ext x
    have h1 : c x * φ = φ * c x := (Subgroup.mem_centralizer_iff.mp hφ) (c x) ⟨x, rfl⟩
    have h2 : c (φ x) = c x := by
      rw [← hconj, ← h1]
      group
    exact congrArg (fun y => y) (hcinj h2)
  have hsurj := pGammaL2ToMulAutPSL2_surjective K hKcard hK hcard
  let Ψ := normalPSL2ToPGammaL2 N K hK hcard eN hsurj
  have hΨinj : Function.Injective Ψ := normalPSL2ToPGammaL2_injective N K hK hcard eN hC hsurj
  have hΨc : ∀ x : Q, Ψ (c x) = psl2Incl K (eL x) := by
    intro x
    have h := psl2Action_apply N hK hcard eN hsurj (eQ x)
    rw [heQ] at h
    rw [h, psl2Incl_apply]
    congr 2
    simp [eN]
  have hΨconj : ∀ (γ : MulAut Q) (x : Q), conjPSL K hK hcard (Ψ γ) (eL x) = eL (γ x) := by
    intro γ x
    rw [conjPSL_eq_iff, ← hΨc, ← hΨc, ← map_inv, ← map_mul, ← map_mul, hconj]
  have hS : ∀ γ' ∈ ({Ψ α, Ψ β, Ψ α * Ψ β} : Set (PGammaL2 K)),
      ∃ γ ∈ ({α, β, α * β} : Set (MulAut Q)), Ψ γ = γ' := by
    intro γ' h
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at h
    rcases h with rfl | rfl | rfl
    · exact ⟨α, Set.mem_insert _ _, rfl⟩
    · exact ⟨β, Set.mem_insert_of_mem _ (Set.mem_insert _ _), rfl⟩
    · exact ⟨α * β, Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ rfl), map_mul Ψ α β⟩
  let H' : Subgroup (PSL2 K) := H.map eL.toMonoidHom
  have hmemH' : ∀ x : Q, eL x ∈ H' ↔ x ∈ H := by
    intro x
    constructor
    · rintro ⟨y, hy, hyx⟩
      rwa [eL.injective hyx] at hy
    · intro hx
      exact ⟨x, hx, rfl⟩
  have hmodel := psl2_generation_model hKcard hK hcard (a := Ψ α) (b := Ψ β)
    (by rw [← map_mul, ← map_mul, hαβ]) (by rw [← map_pow, hα2, map_one])
    (by rw [← map_pow, hβ2, map_one]) (fun h => hα1 (hΨinj (h.trans (map_one Ψ).symm)))
    (fun h => hβ1 (hΨinj (h.trans (map_one Ψ).symm))) (fun h => hne (hΨinj h)) H' ?_ ?_ ?_
  · rcases hmodel with h | ⟨hq, ⟨x₁, hx₁⟩, ⟨x₂, hx₂⟩⟩
    · left
      rw [eq_top_iff]
      intro x _
      exact (hmemH' x).mp (h ▸ Subgroup.mem_top _)
    · right
      have hinner : ∀ (γ : MulAut Q) (x : PSL2 K), psl2Incl K x = Ψ γ →
          γ = MulAut.conj (eL.symm x) := by
        intro γ x hx
        apply hΨinj
        rw [← hx]
        change psl2Incl K x = Ψ (c (eL.symm x))
        rw [hΨc, MulEquiv.apply_symm_apply]
      have hf1 : 1 ≤ f := by
        rcases Nat.eq_zero_or_pos f with h | h
        · rw [h, pow_zero] at hKcard
          omega
        · exact h
      refine ⟨Or.inr ⟨p, f, hKcard ▸ hq, ⟨hp, hf1, le_rfl, ?_, ?_⟩, K, inferInstance,
        inferInstance, hKcard, ⟨eL.trans
          (CFSG.Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj 2 K)⟩⟩,
        eL.symm x₁, eL.symm x₂, hinner α x₁ hx₁, hinner β x₂ hx₂⟩
      · intro h
        simp only [Prod.mk.injEq, true_and] at h
        omega
      · intro h
        simp only [Prod.mk.injEq, true_and] at h
        omega
  ·
    intro γ' hγ' x' hx'
    obtain ⟨γ, hγ, rfl⟩ := hS γ' hγ'
    obtain ⟨x, hx, rfl⟩ := hx'
    change conjPSL K hK hcard (Ψ γ) (eL x) ∈ H'
    rw [hΨconj]
    exact (hmemH' _).mpr (hinv γ hγ x hx)
  ·
    intro γ' hγ' x' hcomm hodd
    obtain ⟨γ, hγ, rfl⟩ := hS γ' hγ'
    have hfix := conjPSL_eq_self_of_commute hK hcard hcomm
    rw [← MulEquiv.apply_symm_apply eL x', hΨconj] at hfix
    have hfix' : γ (eL.symm x') = eL.symm x' := eL.injective hfix
    rw [← MulEquiv.apply_symm_apply eL x']
    refine (hmemH' _).mpr (hP1 γ hγ _ hfix' ?_)
    rwa [← MulEquiv.orderOf_eq eL, MulEquiv.apply_symm_apply]
  ·
    intro γ' hγ' t' ht'2 ht'1 hγt y' hy'
    obtain ⟨γ, hγ, rfl⟩ := hS γ' hγ'
    have hγc : γ = MulAut.conj (eL.symm t') := by
      apply hΨinj
      rw [hγt]
      change psl2Incl K t' = Ψ (c (eL.symm t'))
      rw [hΨc, MulEquiv.apply_symm_apply]
    have ht2 : (eL.symm t') ^ 2 = 1 := by rw [← map_pow, ht'2, map_one]
    have ht1 : eL.symm t' ≠ 1 := fun h => ht'1 (by
      rw [← MulEquiv.apply_symm_apply eL t', h, map_one])
    have hzp : eL.symm t' ∈ Subgroup.zpowers (eL.symm y') := by
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hy'
      refine ⟨k, ?_⟩
      change eL.symm y' ^ k = eL.symm t'
      rw [← map_zpow, hk]
    rw [← MulEquiv.apply_symm_apply eL y']
    exact (hmemH' _).mpr (hP2 γ hγ _ ht2 ht1 hγc _ hzp)

theorem fourGroupGenerationCore : FourGroupGenerationCore := by
  intro Q _ _ _ hQ α β hαβ hα2 hβ2 hα1 hβ1 hne H hinv hP1 hP2
  have hQ' : HasDihedralSylowTwo (⊤ : Subgroup Q) :=
    hasDihedralSylowTwo_of_mulEquiv Subgroup.topEquiv.symm hQ
  have : IsSimpleGroup (⊤ : Subgroup Q) := Subgroup.topEquiv.isSimpleGroup
  have hnonab : ∃ x y : Q, x * y ≠ y * x := by
    obtain ⟨x, y, hxy⟩ := exists_ne_comm_of_simple_dihedral hQ'
    exact ⟨x, y, fun h => hxy (Subtype.ext h)⟩
  rcases simple_dihedral_cases hnonab hQ with he | ⟨K, _, _, p, f, hp, hKcard, hK, hcard, ⟨eL⟩⟩
  · obtain ⟨e⟩ := he
    exact fourGroupGeneration_a7 e hαβ hα2 hβ2 hα1 hβ1 hne H hP1
  · exact fourGroupGeneration_psl2 hQ hp hKcard hK hcard eL hαβ hα2 hβ2 hα1 hβ1 hne H hinv hP1
      hP2

theorem dihedral_cover_generation_holds : ∀ (G : Type) [Group G] [Finite G] (L U : Subgroup G),
    Open.IsQuasisimple L → HasDihedralSylowTwo (L ⧸ Subgroup.center L) →
    (Nat.card (Subgroup.center L)).factorization 2 ≤ 1 →
    U ≤ Subgroup.normalizer (L : Set G) → IsFourGroup U → ¬ L ≤ centralizerJoin U L →
    IsSmallDihedralSimple (L ⧸ Subgroup.center L) ∧
      U ≤ L ⊔ Subgroup.centralizer (L : Set G) :=
  dihedral_cover_generation_of_core fourGroupGenerationCore

end CFSG.ComponentClassification.AschbacherKnownGroup.FactsL2
