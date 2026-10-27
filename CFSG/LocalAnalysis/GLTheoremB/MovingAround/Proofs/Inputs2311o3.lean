module

public import CFSG.LieType.SeitzGeneration.ExcHigh.E8Frame
import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Inputs2311k

public section

namespace CFSG.LocalAnalysis.GLTheoremB.MovingAround.Inputs2311o

open CFSG.Open TauCeti CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.RankThree.PartOne

private theorem exists_sign_dvd_of_dvd_phiNat {m p Q : ℕ} (hm : m = 3 ∨ m = 6)
    (hd : p ∣ K128.phiNat m Q) :
    ∃ ε : ℤ, (ε = 1 ∨ ε = -1) ∧ (p : ℤ) ∣ (Q : ℤ) ^ 2 + ε * (Q : ℤ) + 1 := by
  rcases hm with rfl | rfl
  · refine ⟨1, Or.inl rfl, ?_⟩
    simp only [K128.phiNat] at hd
    rw [one_mul]
    exact_mod_cast hd
  · refine ⟨-1, Or.inr rfl, ?_⟩
    simp only [K128.phiNat] at hd
    have hQ : Q ≤ Q ^ 2 := Nat.le_self_pow (by norm_num) Q
    have h := Int.natCast_dvd_natCast.2 hd
    rw [Nat.cast_add, Nat.cast_one, Nat.cast_sub hQ] at h
    push_cast at h
    convert h using 1
    ring

section Generic

open CFSG.LieType.SeitzGeneration.ExcHigh (isElemAbelian_image
  natCard_sup_le_mul_of_commute not_le_normalizer_of_isQuasisimple)

private theorem range_inclusion_comp_symm {G A : Type*} [Group G] [Group A] {X Y : Subgroup G}
    (h : X ≤ Y) (χ : ↥X ≃* A) :
    ((Subgroup.inclusion h).comp χ.symm.toMonoidHom).range = X.subgroupOf Y := by
  rw [MonoidHom.range_comp,
    MonoidHom.range_eq_top_of_surjective χ.symm.toMonoidHom χ.symm.surjective,
    ← MonoidHom.range_eq_map, Subgroup.inclusion_range]

private theorem range_le_closure_rElements {A G : Type*} [Group A] [Group G] (f : A →* G)
    (hf : Function.Injective f) {r : ℕ} (W : Subgroup A)
    (hgen : Subgroup.closure {k : A | ∃ x ∈ W, x ≠ 1 ∧ Commute k x ∧ ∃ n : ℕ, k ^ r ^ n = 1} =
      ⊤) :
    f.range ≤ Subgroup.closure {g : G | g ∈ f.range ∧ (∃ n : ℕ, g ^ r ^ n = 1) ∧
      ∃ x ∈ W.map f, x ≠ 1 ∧ g * x = x * g} := by
  rintro _ ⟨a, rfl⟩
  have ha : a ∈ Subgroup.closure
      {k : A | ∃ x ∈ W, x ≠ 1 ∧ Commute k x ∧ ∃ n : ℕ, k ^ r ^ n = 1} := by
    rw [hgen]
    exact Subgroup.mem_top a
  have hfa := Subgroup.mem_map_of_mem f ha
  rw [MonoidHom.map_closure] at hfa
  refine Subgroup.closure_mono ?_ hfa
  rintro _ ⟨k, ⟨x, hxW, hx1, hkx, n, hkn⟩, rfl⟩
  exact ⟨MonoidHom.mem_range.2 ⟨k, rfl⟩, ⟨n, by rw [← map_pow, hkn, map_one]⟩, f x,
    Subgroup.mem_map_of_mem f hxW, fun h => hx1 (hf (h.trans (map_one f).symm)),
    by rw [← map_mul, hkx.eq, map_mul]⟩

private theorem exists_rFrame_of_embeddings {G A₁ A₂ : Type*} [Group G] [Finite G] [Group A₁]
    [Group A₂] {p r o : ℕ} (f₁ : A₁ →* G) (f₂ : A₂ →* G) (hf₁ : Function.Injective f₁)
    (hf₂ : Function.Injective f₂) (hc : ∀ a ∈ f₁.range, ∀ b ∈ f₂.range, a * b = b * a)
    (hd : Disjoint f₁.range f₂.range)
    (hcl : ∀ H : Subgroup G, f₁.range ⊔ f₂.range ≤ H →
      ¬ H ≤ Subgroup.normalizer ((f₁.range ⊔ f₂.range : Subgroup G) : Set G) → H = ⊤)
    (hnm : ∀ H : Subgroup G,
      H ≤ Subgroup.normalizer ((f₁.range ⊔ f₂.range : Subgroup G) : Set G) →
      Group.IsSolvable ↥(H ⊓ (f₁.range ⊔ f₂.range)) → Group.IsSolvable ↥H)
    (hb₁ : Nat.card ↥f₁.range ≤ o) (hb₂ : Nat.card ↥f₂.range ≤ o)
    (E₁ : Subgroup A₁) (hE₁ : IsElemAbelian p E₁) (hE₁c : Nat.card E₁ = p ^ 2)
    (hg₁ : Subgroup.closure {k : A₁ | ∃ x ∈ E₁, x ≠ 1 ∧ Commute k x ∧ ∃ n : ℕ, k ^ r ^ n = 1} =
      ⊤)
    (E₂ : Subgroup A₂) (hE₂ : IsElemAbelian p E₂) (hE₂c : Nat.card E₂ = p ^ 2)
    (hg₂ : Subgroup.closure {k : A₂ | ∃ x ∈ E₂, x ≠ 1 ∧ Commute k x ∧ ∃ n : ℕ, k ^ r ^ n = 1} =
      ⊤) :
    ∃ V₁ V₂ X₁ X₂ : Subgroup G,
      IsElemAbelian p V₁ ∧ IsElemAbelian p V₂ ∧ Nat.card V₁ = p ^ 2 ∧ Nat.card V₂ = p ^ 2 ∧
      Disjoint V₁ V₂ ∧ (∀ a ∈ V₁, ∀ b ∈ V₂, a * b = b * a) ∧
      (∀ g ∈ X₁, ∀ b ∈ V₂, g * b = b * g) ∧ (∀ g ∈ X₂, ∀ b ∈ V₁, g * b = b * g) ∧
      X₁ ≤ Subgroup.closure {g | g ∈ X₁ ∧ (∃ n : ℕ, g ^ r ^ n = 1) ∧
        ∃ x ∈ V₁, x ≠ 1 ∧ g * x = x * g} ∧
      X₂ ≤ Subgroup.closure {g | g ∈ X₂ ∧ (∃ n : ℕ, g ^ r ^ n = 1) ∧
        ∃ x ∈ V₂, x ≠ 1 ∧ g * x = x * g} ∧
      ∀ H P : Subgroup G, X₁ ⊔ X₂ ≤ H → P ≤ H → CFSG.Open.IsQuasisimple ↥P →
        o ^ 2 < Nat.card ↥P → H = ⊤ := by
  have hV₁ : E₁.map f₁ ≤ f₁.range := Subgroup.map_le_range f₁ E₁
  have hV₂ : E₂.map f₂ ≤ f₂.range := Subgroup.map_le_range f₂ E₂
  refine ⟨E₁.map f₁, E₂.map f₂, f₁.range, f₂.range, isElemAbelian_image f₁ hE₁,
    isElemAbelian_image f₂ hE₂, (Subgroup.card_map_of_injective hf₁).trans hE₁c,
    (Subgroup.card_map_of_injective hf₂).trans hE₂c, hd.mono hV₁ hV₂,
    fun a ha b hb => hc a (hV₁ ha) b (hV₂ hb), fun g hg b hb => hc g hg b (hV₂ hb),
    fun g hg b hb => (hc b (hV₁ hb) g hg).symm, range_le_closure_rElements f₁ hf₁ E₁ hg₁,
    range_le_closure_rElements f₂ hf₂ E₂ hg₂, ?_⟩
  intro H P hXH hPH hQ hPc
  have hlt : Nat.card ↥(f₁.range ⊔ f₂.range) < Nat.card ↥P := by
    refine lt_of_le_of_lt ((natCard_sup_le_mul_of_commute hc).trans ?_) hPc
    rw [sq]
    exact Nat.mul_le_mul hb₁ hb₂
  exact hcl H hXH fun hHN => not_le_normalizer_of_isQuasisimple hQ hnm hlt (hPH.trans hHN)

end Generic

section Certified

set_option linter.unusedSectionVars false


theorem rClosure_graphFixed_threeSix (q : PrimePower) (K : Type) [Field K] [Finite K]
    (hK : Nat.card K = q.card ^ TwistTag.D4.order) (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ q.card)
    {m p : ℕ} (hm : m = 3 ∨ m = 6) (hp : p.Prime) (hp5 : 5 ≤ p)
    (hd : p ∣ K128.phiNat m q.card)
    (E : Subgroup (graphFixedRootGroup TwistTag.D4 K σ.toRingHom))
    (hE : IsElemAbelian p E) (hEc : Nat.card E = p ^ 2) :
    Subgroup.closure {k | ∃ x ∈ E, x ≠ 1 ∧ Commute k x ∧ ∃ n : ℕ, k ^ q.p ^ n = 1} = ⊤ := by
  have hv := LieTypeIndex.valid_trialityD4 q
  obtain ⟨e⟩ := CFSG.LieType.SeitzGeneration.ExcHigh.c0_iso_cat_trialityD4 q hv K hK σ hσ
  haveI := (CFSG.LieType.SeitzGeneration.finite_isSimpleGroup_cat_trialityD4 hv).2
  haveI : IsSimpleGroup (graphFixedRootGroup TwistTag.D4 K σ.toRingHom) :=
    MulEquiv.isSimpleGroup e
  have hK' : Nat.card K = (q.p ^ q.exponent) ^ 3 := by
    rw [hK, PrimePower.card_def]
    rfl
  have hσ' : ∀ c, σ c = c ^ (q.p ^ q.exponent) := fun c => by rw [hσ c, PrimePower.card_def]
  rw [PrimePower.card_def] at hd
  obtain ⟨ε, hε, hpd⟩ := exists_sign_dvd_of_dvd_phiNat hm hd
  have hE' := CFSG.LieType.SeitzGeneration.ExcHigh.c0_isElementaryAbelian_of_isElemAbelian hE
  exact Inputs2311k.rClosure_eq_top_threeSix q.prime_p q.exponent_pos K hK' σ hσ' hε hp
    (by omega) hpd (fun E' hE' hc' => Inputs2311k.closure_cenGen_threeSix_model q.prime_p
      q.exponent_pos K hK' σ hσ' hε hp hp5 hpd E' hE' hc') E hE' hEc

section Frame

open CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame
open CFSG.LieType.SeitzGeneration.ExcHigh (closing_restrict normSolv_restrict
  sup_subgroupOf_adjoint dvd_phiNat_of_orderOf e8Twelve_X₁_iso e8Twelve_X₂_iso
  c0_exists_plane)

private theorem exists_rFrame_adjoint {τ : Tag} {K : Type} [Field K] [Finite K]
    {X₁ X₂ : Subgroup (ModGL τ K)} {A₁ A₂ : Type*} [Group A₁] [Group A₂] {p r o : ℕ}
    (h₁ : X₁ ≤ adjointGroup τ K) (h₂ : X₂ ≤ adjointGroup τ K)
    (hc : ∀ a ∈ X₁, ∀ b ∈ X₂, a * b = b * a)
    (hcl : TwFrameClosing τ K (X₁ ⊔ X₂)) (hnm : TwFrameNormalizerSolvable τ K (X₁ ⊔ X₂))
    (hz : Nat.card ↥(Subgroup.center ↥X₁) = 1) (hb₁ : Nat.card ↥X₁ ≤ o)
    (hb₂ : Nat.card ↥X₂ ≤ o) (χ₁ : ↥X₁ ≃* A₁) (χ₂ : ↥X₂ ≃* A₂)
    (E₁ : Subgroup A₁) (hE₁ : IsElemAbelian p E₁) (hE₁c : Nat.card E₁ = p ^ 2)
    (hg₁ : Subgroup.closure {k : A₁ | ∃ x ∈ E₁, x ≠ 1 ∧ Commute k x ∧ ∃ n : ℕ, k ^ r ^ n = 1} =
      ⊤)
    (E₂ : Subgroup A₂) (hE₂ : IsElemAbelian p E₂) (hE₂c : Nat.card E₂ = p ^ 2)
    (hg₂ : Subgroup.closure {k : A₂ | ∃ x ∈ E₂, x ≠ 1 ∧ Commute k x ∧ ∃ n : ℕ, k ^ r ^ n = 1} =
      ⊤) :
    ∃ V₁ V₂ Y₁ Y₂ : Subgroup ↥(adjointGroup τ K),
      IsElemAbelian p V₁ ∧ IsElemAbelian p V₂ ∧ Nat.card V₁ = p ^ 2 ∧ Nat.card V₂ = p ^ 2 ∧
      Disjoint V₁ V₂ ∧ (∀ a ∈ V₁, ∀ b ∈ V₂, a * b = b * a) ∧
      (∀ g ∈ Y₁, ∀ b ∈ V₂, g * b = b * g) ∧ (∀ g ∈ Y₂, ∀ b ∈ V₁, g * b = b * g) ∧
      Y₁ ≤ Subgroup.closure {g | g ∈ Y₁ ∧ (∃ n : ℕ, g ^ r ^ n = 1) ∧
        ∃ x ∈ V₁, x ≠ 1 ∧ g * x = x * g} ∧
      Y₂ ≤ Subgroup.closure {g | g ∈ Y₂ ∧ (∃ n : ℕ, g ^ r ^ n = 1) ∧
        ∃ x ∈ V₂, x ≠ 1 ∧ g * x = x * g} ∧
      ∀ H P : Subgroup ↥(adjointGroup τ K), Y₁ ⊔ Y₂ ≤ H → P ≤ H →
        CFSG.Open.IsQuasisimple ↥P → o ^ 2 < Nat.card ↥P → H = ⊤ := by
  haveI : Finite (ModGL τ K) := finite_modGL
  have hr₁ := range_inclusion_comp_symm h₁ χ₁
  have hr₂ := range_inclusion_comp_symm h₂ χ₂
  have hsup := sup_subgroupOf_adjoint h₁ h₂ hc
  refine exists_rFrame_of_embeddings ((Subgroup.inclusion h₁).comp χ₁.symm.toMonoidHom)
    ((Subgroup.inclusion h₂).comp χ₂.symm.toMonoidHom)
    ((Subgroup.inclusion_injective h₁).comp χ₁.symm.injective)
    ((Subgroup.inclusion_injective h₂).comp χ₂.symm.injective) ?_ ?_ ?_ ?_ ?_ ?_
    E₁ hE₁ hE₁c hg₁ E₂ hE₂ hE₂c hg₂
  · rw [hr₁, hr₂]
    intro a ha b hb
    exact Subtype.ext (hc _ (Subgroup.mem_subgroupOf.1 ha) _ (Subgroup.mem_subgroupOf.1 hb))
  · rw [hr₁, hr₂, Subgroup.disjoint_def]
    intro x hx₁ hx₂
    have hcen : (⟨(x : ModGL τ K), Subgroup.mem_subgroupOf.1 hx₁⟩ : ↥X₁) ∈
        Subgroup.center ↥X₁ :=
      Subgroup.mem_center_iff.2 fun g => Subtype.ext (hc _ g.2 _ (Subgroup.mem_subgroupOf.1 hx₂))
    rw [Subgroup.card_eq_one.1 hz, Subgroup.mem_bot] at hcen
    have hval := congrArg Subtype.val hcen
    exact Subtype.ext hval
  · rw [hr₁, hr₂, ← hsup]
    exact fun H hH hN => closing_restrict (sup_le h₁ h₂) hcl H hH hN
  · rw [hr₁, hr₂, ← hsup]
    exact fun H hH hs => normSolv_restrict (sup_le h₁ h₂) hnm H hH hs
  · rw [hr₁, Nat.card_congr (Subgroup.subgroupOfEquivOfLe h₁).toEquiv]
    exact hb₁
  · rw [hr₂, Nat.card_congr (Subgroup.subgroupOfEquivOfLe h₂).toEquiv]
    exact hb₂

theorem exists_rFrame_E8 (q : PrimePower) (K : Type) [Field K] [Finite K]
    (hK : Nat.card K = q.card) {p e : ℕ} (hp : p.Prime) (hp7 : 7 ≤ p) (hpq : p ≠ q.p)
    (he3 : e = 3 ∨ e = 6) (he : orderOf ((q.card : ℕ) : ZMod p) = e) :
    ∃ V₁ V₂ X₁ X₂ : Subgroup (adjointGroup Tag.E8 K),
      IsElemAbelian p V₁ ∧ IsElemAbelian p V₂ ∧ Nat.card V₁ = p ^ 2 ∧ Nat.card V₂ = p ^ 2 ∧
      Disjoint V₁ V₂ ∧ (∀ a ∈ V₁, ∀ b ∈ V₂, a * b = b * a) ∧
      (∀ g ∈ X₁, ∀ b ∈ V₂, g * b = b * g) ∧ (∀ g ∈ X₂, ∀ b ∈ V₁, g * b = b * g) ∧
      X₁ ≤ Subgroup.closure {g | g ∈ X₁ ∧ (∃ n : ℕ, g ^ q.p ^ n = 1) ∧
        ∃ x ∈ V₁, x ≠ 1 ∧ g * x = x * g} ∧
      X₂ ≤ Subgroup.closure {g | g ∈ X₂ ∧ (∃ n : ℕ, g ^ q.p ^ n = 1) ∧
        ∃ x ∈ V₂, x ≠ 1 ∧ g * x = x * g} ∧
      ∀ H P : Subgroup (adjointGroup Tag.E8 K), X₁ ⊔ X₂ ≤ H → P ≤ H →
        CFSG.Open.IsQuasisimple ↥P → ordTrialityD4 q.card ^ 2 < Nat.card ↥P → H = ⊤ := by
  haveI : Fact q.p.Prime := ⟨q.prime_p⟩
  have hk : Nat.card K = q.p ^ q.exponent := hK.trans (PrimePower.card_def q)
  obtain ⟨D⟩ := exists_langLevi TwClass.e8Twelve.tag K TwClass.e8Twelve.w
    (TwClass.w_theta TwClass.e8Twelve)
  have hfr := TwCardAux.e8Twelve_frames K D
  have hmin : TwClass.e8Twelve.minQ ≤ Nat.card K := by
    show 2 ≤ Nat.card K
    exact Finite.one_lt_card
  have hd : p ∣ K128.phiNat e q.card := dvd_phiNat_of_orderOf hp he3 he
  have hd' : p ∣ K128.phiNat e (q.p ^ q.exponent) := by rwa [PrimePower.card_def] at hd
  obtain ⟨K₁, _, _, σ₁, hK₁, hσ₁, ⟨χ₁⟩⟩ := e8Twelve_X₁_iso q.exponent_pos hk D
  obtain ⟨K₂, _, _, σ₂, hK₂, hσ₂, ⟨χ₂⟩⟩ := e8Twelve_X₂_iso q.exponent_pos hk D
  obtain ⟨E₁, hE₁, hE₁c⟩ := c0_exists_plane q.exponent_pos K₁ hK₁ σ₁ hσ₁ he3 hp (by omega) hd'
  obtain ⟨E₂, hE₂, hE₂c⟩ := c0_exists_plane q.exponent_pos K₂ hK₂ σ₂ hσ₂ he3 hp (by omega) hd'
  have hg₁ := rClosure_graphFixed_threeSix q K₁ (by rw [hK₁, PrimePower.card_def]; rfl) σ₁
    (fun c => by rw [hσ₁ c, PrimePower.card_def]) he3 hp (by omega) hd E₁ hE₁ hE₁c
  have hg₂ := rClosure_graphFixed_threeSix q K₂ (by rw [hK₂, PrimePower.card_def]; rfl) σ₂
    (fun c => by rw [hσ₂ c, PrimePower.card_def]) he3 hp (by omega) hd E₂ hE₂ hE₂c
  exact exists_rFrame_adjoint (τ := TwClass.e8Twelve.tag) inf_le_left inf_le_left
    (TwCardAux.frame_commute TwClass.e8Twelve D) (twClosing_e8Twelve K D)
    (twNormalizer_e8Twelve K hmin D) hfr.2.2 (hfr.1.trans (congrArg ordTrialityD4 hK)).le
    (hfr.2.1.trans (congrArg ordTrialityD4 hK)).le χ₁ χ₂ E₁ hE₁ hE₁c hg₁ E₂ hE₂ hE₂c hg₂

end Frame

end Certified

end CFSG.LocalAnalysis.GLTheoremB.MovingAround.Inputs2311o
