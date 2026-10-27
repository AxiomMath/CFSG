module

public import CFSG.LocalAnalysis.SeitzReduction.F4PilotPositionFacts
public import CFSG.LocalAnalysis.SeitzReduction.PerfectCentralizer
public import CFSG.GroupTheory.SolvableHallNodes
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotToralCentralizer

public section

namespace CFSG.SeitzReduction.F4Pilot

open Subgroup CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
open scoped Pointwise

section Roots


theorem isRoot_root0122 : IsRoot .F4 root0122 := mem_rootFinset.1 (by decide +kernel)

theorem isRoot_root0121 : IsRoot .F4 root0121 := mem_rootFinset.1 (by decide +kernel)

theorem isRoot_root0110 : IsRoot .F4 root0110 := mem_rootFinset.1 (by decide +kernel)

theorem iform_neg_left (γ δ : Fin (Tag.rank .F4) → ℤ) : iform (-γ) δ = -iform γ δ := by
  simp only [iform, Pi.neg_apply, neg_mul, Finset.sum_neg_distrib]

theorem neg_mem_phi0 {κ : TwoCentral} {γ : Fin (Tag.rank .F4) → ℤ} (hγ : γ ∈ phi0 κ) :
    -γ ∈ phi0 κ :=
  ⟨CFSG.LieType.Chevalley.IsRoot.neg hγ.1, fun δ hδ => by rw [iform_neg_left, hγ.2 δ hδ, neg_zero]⟩

theorem rootR_mem_phi0 (κ : TwoCentral) : rootR ∈ phi0 κ :=
  ⟨isRoot_rootR, by cases κ <;> decide +kernel⟩

end Roots

section Subgroups

variable {K : Type} [Field K]

theorem rootSubgroup_le_rootSpan {S : Set (Fin (Tag.rank .F4) → ℤ)} {γ : Fin (Tag.rank .F4) → ℤ}
    (hγ : γ ∈ S) : rootSubgroup .F4 K γ ≤ rootSpan .F4 K S :=
  le_iSup₂ (f := fun γ (_ : γ ∈ S) => rootSubgroup .F4 K γ) γ hγ

theorem rootSL2_le_levi {κ : TwoCentral} {γ : Fin (Tag.rank .F4) → ℤ} (hγ : γ ∈ phi0 κ) :
    rootSL2 K γ ≤ levi K κ := fun _ hx =>
  mem_subgroupOf.2 (sup_le (rootSubgroup_le_rootSpan hγ)
    (rootSubgroup_le_rootSpan (neg_mem_phi0 hγ)) (mem_subgroupOf.1 hx))

variable (K) in
theorem rootSL2_rootR : rootSL2 K rootR = (rootSL2R K).subgroupOf (adjointGroup .F4 K) := rfl

theorem rootSL2_rootR_le_levi (κ : TwoCentral) : rootSL2 K rootR ≤ levi K κ :=
  rootSL2_le_levi (rootR_mem_phi0 κ)

theorem rootSL2_mem_leviRootSL2s {κ : TwoCentral} {γ : Fin (Tag.rank .F4) → ℤ}
    (hγ : γ ∈ phi0 κ) : rootSL2 K γ ∈ leviRootSL2s K κ := by
  refine ⟨γ, hγ, 1, one_mem _, ?_⟩
  ext x
  simp [Subgroup.mem_map]

theorem xC_mem_C3Levi {γ : Fin (Tag.rank .F4) → ℤ} (hγ : γ ∈ c3LeviRoots) (c : K) :
    xC K γ c ∈ C3Levi K :=
  pinnedX_mem_C3Levi hγ c

theorem yRep_mem_C3Levi (κ : TwoCentral) : yRep K κ ∈ C3Levi K := by
  have h1 : xC K root0122 1 ∈ C3Levi K := xC_mem_C3Levi ⟨isRoot_root0122, rfl⟩ 1
  have h2 : xC K root0121 1 ∈ C3Levi K := xC_mem_C3Levi ⟨isRoot_root0121, rfl⟩ 1
  cases κ
  · exact h1
  · exact h2
  · exact mul_mem h1 h2

theorem yV_mem_C3Levi : yV K ∈ C3Levi K :=
  mul_mem (xC_mem_C3Levi ⟨isRoot_root0110, rfl⟩ 1) (xC_mem_C3Levi ⟨isRoot_root0122, rfl⟩ 1)

end Subgroups

section Abstract

variable {G : Type*} [Group G]

theorem map_centralizer_singleton {A : Type*} [Group A] {φ : A →* G} (hφ : Function.Injective φ)
    (a : A) : (centralizer ({a} : Set A)).map φ = φ.range ⊓ centralizer ({φ a} : Set G) := by
  ext g
  constructor
  · rintro ⟨x, hx, rfl⟩
    rw [mem_inf]
    refine ⟨⟨x, rfl⟩, ?_⟩
    rw [SetLike.mem_coe, mem_centralizer_singleton_iff] at hx
    rw [mem_centralizer_singleton_iff, ← map_mul, ← map_mul, hx]
  · intro hg
    obtain ⟨⟨x, rfl⟩, hx⟩ := mem_inf.1 hg
    refine ⟨x, ?_, rfl⟩
    rw [mem_centralizer_singleton_iff, ← map_mul, ← map_mul] at hx
    rw [SetLike.mem_coe, mem_centralizer_singleton_iff]
    exact hφ hx

theorem mem_normalizer_sup {Q₁ Q₂ : Subgroup G} {m : G} (h₁ : m ∈ normalizer (Q₁ : Set G))
    (h₂ : m ∈ normalizer (Q₂ : Set G)) : m ∈ normalizer ((Q₁ ⊔ Q₂ : Subgroup G) : Set G) := by
  rw [mem_normalizer_iff_map_conj_eq] at h₁ h₂ ⊢
  rw [Subgroup.map_sup, h₁, h₂]

theorem le_of_sup_eq_of_isSimpleGroup [Finite G] {p : ℕ} [Fact p.Prime] {Q₁ M₁ Q₂ : Subgroup G}
    (hQ₁ : IsPGroup p Q₁) (hQ₂ : IsPGroup p Q₂) (hM₁ : IsSimpleGroup M₁)
    (hperf : ⁅Q₁ ⊔ M₁, Q₁ ⊔ M₁⁆ = Q₁ ⊔ M₁) (hM₁N : M₁ ≤ normalizer (Q₁ : Set G))
    (hQ₂le : Q₂ ≤ Q₁ ⊔ M₁) (hQ₂N : Q₁ ⊔ M₁ ≤ normalizer (Q₂ : Set G)) : Q₂ ≤ Q₁ := by
  have hΛN : Q₁ ⊔ M₁ ≤ normalizer (Q₁ : Set G) := sup_le le_normalizer hM₁N
  have hNp : IsPGroup p (Q₁ ⊔ Q₂ : Subgroup G) :=
    hQ₁.to_sup_of_normal_left' hQ₂ (hQ₂le.trans hΛN)
  have hMN : ∀ m ∈ M₁, m ∈ normalizer ((Q₁ ⊔ Q₂ : Subgroup G) : Set G) := fun m hm =>
    mem_normalizer_sup (hM₁N hm) (hQ₂N (mem_sup_right hm))
  have hnorm : ((Q₁ ⊔ Q₂).subgroupOf M₁).Normal := by
    refine ⟨fun n hn m => ?_⟩
    rw [mem_subgroupOf] at hn ⊢
    have := (mem_normalizer_iff.1 (hMN m m.2) n).1 hn
    simpa using this
  have := hM₁
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal ((Q₁ ⊔ Q₂).subgroupOf M₁) with h | h
  · intro x hx
    have hx' : x ∈ ((Q₁ ⊔ M₁ : Subgroup G) : Set G) := hQ₂le hx
    rw [coe_mul_of_right_le_normalizer_left Q₁ M₁ hM₁N] at hx'
    obtain ⟨q, hq, m, hm, rfl⟩ := hx'
    have hmN : m ∈ Q₁ ⊔ Q₂ := by
      have : q⁻¹ * (q * m) ∈ Q₁ ⊔ Q₂ :=
        mul_mem (mem_sup_left (inv_mem hq)) (mem_sup_right hx)
      simpa using this
    have hdisj : Disjoint (Q₁ ⊔ Q₂) M₁ := subgroupOf_eq_bot.1 h
    have hm1 : m = 1 := (disjoint_iff_inf_le.1 hdisj) ⟨hmN, hm⟩
    subst hm1
    simpa using hq
  · exfalso
    have hMle : M₁ ≤ Q₁ ⊔ Q₂ := subgroupOf_eq_top.1 h
    have hΛle : Q₁ ⊔ M₁ ≤ Q₁ ⊔ Q₂ := sup_le le_sup_left hMle
    have : Group.IsNilpotent (Q₁ ⊔ Q₂ : Subgroup G) := hNp.isNilpotent
    have hbot := perfect_eq_bot_of_le (A := Q₁ ⊔ Q₂) inferInstance hperf hΛle
    have hM₁bot : M₁ = ⊥ := le_bot_iff.1 (hbot ▸ le_sup_right)
    have : Nontrivial M₁ := hM₁.toNontrivial
    obtain ⟨a, b, hab⟩ := exists_pair_ne M₁
    apply hab
    have ha : (a : G) = 1 := (eq_bot_iff_forall M₁).1 hM₁bot _ a.2
    have hb : (b : G) = 1 := (eq_bot_iff_forall M₁).1 hM₁bot _ b.2
    exact Subtype.ext (ha.trans hb.symm)

theorem exists_mulEquiv_of_sup_eq {Q M₁ M₂ : Subgroup G} (hsup : Q ⊔ M₁ = Q ⊔ M₂)
    (hQ₁ : Q ⊓ M₁ = ⊥) (hQ₂ : Q ⊓ M₂ = ⊥) (hN₁ : M₁ ≤ normalizer (Q : Set G))
    (hN₂ : M₂ ≤ normalizer (Q : Set G)) :
    ∃ ι : M₁ ≃* M₂, ∀ m : M₁, ((ι m : M₂) : G)⁻¹ * m ∈ Q := by
  set Λ := Q ⊔ M₁ with hΛ
  have hQΛ : Q ≤ Λ := le_sup_left
  have hM₁Λ : M₁ ≤ Λ := le_sup_right
  have hM₂Λ : M₂ ≤ Λ := hsup ▸ le_sup_right
  have hn : (Q.subgroupOf Λ).Normal :=
    (normal_subgroupOf_iff_le_normalizer hQΛ).2 (sup_le le_normalizer hN₁)
  set π := QuotientGroup.mk' (Q.subgroupOf Λ) with hπ
  have key : ∀ {M : Subgroup G} (hMΛ : M ≤ Λ), Q ⊓ M = ⊥ → M ≤ normalizer (Q : Set G) →
      Q ⊔ M = Λ → Function.Bijective (π.comp (inclusion hMΛ)) := by
    intro M hMΛ hQM hNM hQMΛ
    refine ⟨fun a b hab => ?_, fun y => ?_⟩
    · simp only [MonoidHom.coe_comp, Function.comp_apply, hπ, QuotientGroup.mk'_apply,
        QuotientGroup.eq] at hab
      have h1 : ((a : G))⁻¹ * b ∈ Q := by
        have := mem_subgroupOf.1 hab
        simpa using this
      have h2 : ((a : G))⁻¹ * b ∈ Q ⊓ M := ⟨h1, M.mul_mem (M.inv_mem a.2) b.2⟩
      rw [hQM, mem_bot, inv_mul_eq_one] at h2
      exact Subtype.ext h2
    · obtain ⟨l, rfl⟩ := QuotientGroup.mk'_surjective (Q.subgroupOf Λ) y
      have hl : (l : G) ∈ ((Q ⊔ M : Subgroup G) : Set G) := by rw [hQMΛ]; exact l.2
      rw [coe_mul_of_right_le_normalizer_left Q M hNM] at hl
      obtain ⟨q, hq, m, hm, hqm⟩ := hl
      refine ⟨⟨m, hm⟩, ?_⟩
      simp only [MonoidHom.coe_comp, Function.comp_apply, hπ, QuotientGroup.mk'_apply,
        QuotientGroup.eq]
      rw [mem_subgroupOf]
      have : ((inclusion hMΛ ⟨m, hm⟩ : Λ) : G)⁻¹ * l = m⁻¹ * (q * m) := by
        rw [← hqm]
        rfl
      rw [Subgroup.coe_mul, Subgroup.coe_inv, show ((inclusion hMΛ ⟨m, hm⟩ : Λ) : G) = m from rfl,
        ← hqm]
      have hc := (mem_normalizer_iff''.1 (hNM hm) q).1 hq
      simpa [mul_assoc] using hc
  set e₁ := MulEquiv.ofBijective _ (key hM₁Λ hQ₁ hN₁ rfl) with he₁
  set e₂ := MulEquiv.ofBijective _ (key hM₂Λ hQ₂ hN₂ hsup.symm) with he₂
  refine ⟨e₁.trans e₂.symm, fun m => ?_⟩
  have h := e₂.apply_symm_apply (e₁ m)
  rw [he₂, MulEquiv.ofBijective_apply] at h
  rw [he₁, MulEquiv.ofBijective_apply] at h
  simp only [MonoidHom.coe_comp, Function.comp_apply, hπ, QuotientGroup.mk'_apply,
    QuotientGroup.eq] at h
  have h' := mem_subgroupOf.1 h
  simp only [Subgroup.coe_mul, Subgroup.coe_inv, coe_inclusion] at h'
  exact h'

theorem exists_mem_conj_eq_of_complement [Finite G] {p : ℕ} [hp : Fact p.Prime]
    {Q X X₂ : Subgroup G} (hQ : IsPGroup p Q) (hX : ¬ p ∣ Nat.card X)
    (hXN : X ≤ normalizer (Q : Set G)) (hX₂N : X₂ ≤ normalizer (Q : Set G))
    (hQX : Q ⊓ X = ⊥) (hQX₂ : Q ⊓ X₂ = ⊥) (hsup : Q ⊔ X = Q ⊔ X₂) :
    ∃ n ∈ Q, X₂ = X.map (MulAut.conj n⁻¹).toMonoidHom := by
  set F := Q ⊔ X with hF
  have hQF : Q ≤ F := le_sup_left
  have hXF : X ≤ F := le_sup_right
  have hX₂F : X₂ ≤ F := hsup ▸ le_sup_right
  have hNn : (Q.subgroupOf F).Normal :=
    (normal_subgroupOf_iff_le_normalizer hQF).2 (sup_le le_normalizer hXN)
  have hNp : IsPGroup p (Q.subgroupOf F) := hQ.of_equiv (subgroupOfEquivOfLe hQF).symm
  have hNsolv : Group.IsSolvable (Q.subgroupOf F) := by
    have : Group.IsNilpotent (Q.subgroupOf F) := hNp.isNilpotent
    infer_instance
  have hmul : ∀ {Y : Subgroup G} (hYF : Y ≤ F), Y ≤ normalizer (Q : Set G) → Q ⊔ Y = F →
      ((Q.subgroupOf F : Set F) * (Y.subgroupOf F : Set F)) = Set.univ := by
    intro Y hYF hYN hQY
    refine Set.eq_univ_of_forall fun f => ?_
    have hf : (f : G) ∈ ((Q ⊔ Y : Subgroup G) : Set G) := by rw [hQY]; exact f.2
    rw [coe_mul_of_right_le_normalizer_left Q Y hYN] at hf
    obtain ⟨q, hq, y, hy, hqy⟩ := hf
    exact ⟨⟨q, hQF hq⟩, mem_subgroupOf.2 hq, ⟨y, hYF hy⟩, mem_subgroupOf.2 hy,
      Subtype.ext hqy⟩
  have hinf : ∀ {Y : Subgroup G}, Q ⊓ Y = ⊥ → Q.subgroupOf F ⊓ Y.subgroupOf F = ⊥ := by
    intro Y hQY
    rw [eq_bot_iff]
    intro f hf
    have h : (f : G) ∈ Q ⊓ Y := ⟨mem_subgroupOf.1 hf.1, mem_subgroupOf.1 hf.2⟩
    rw [hQY, mem_bot] at h
    exact mem_bot.2 (Subtype.ext h)
  have hNH := hmul hXF hXN rfl
  have hNK := hmul hX₂F hX₂N hsup.symm
  have hNH' := hinf hQX
  have hNK' := hinf hQX₂
  have hcomp : IsComplement' (Q.subgroupOf F) (X.subgroupOf F) :=
    isComplement'_of_disjoint_and_mul_eq_univ (disjoint_iff.2 hNH') hNH
  have hidx : (Q.subgroupOf F).index = Nat.card X := by
    have h1 := hcomp.card_mul_card
    have h2 := (Q.subgroupOf F).card_mul_index
    have hpos : 0 < Nat.card (Q.subgroupOf F) := Nat.card_pos
    have h3 : (Q.subgroupOf F).index = Nat.card (X.subgroupOf F) :=
      Nat.eq_of_mul_eq_mul_left hpos (h2.trans h1.symm)
    rw [h3, Nat.card_congr (subgroupOfEquivOfLe hXF).toEquiv]
  obtain ⟨k, hk⟩ := hNp.exists_card_eq
  have hcop : Nat.Coprime (Nat.card (Q.subgroupOf F)) (Q.subgroupOf F).index := by
    rw [hk, hidx]
    exact Nat.Coprime.pow_left k ((Nat.Prime.coprime_iff_not_dvd hp.out).2 hX)
  obtain ⟨n, hn, hK⟩ := CFSG.SolvableHall.solvable_normal_hall_complement_conjugacy
    (Q.subgroupOf F) hNsolv hcop hNH hNK hNH' hNK'
  refine ⟨n, mem_subgroupOf.1 hn, ?_⟩
  ext g
  constructor
  · intro hg
    have hg' : (⟨g, hX₂F hg⟩ : F) ∈ X₂.subgroupOf F := mem_subgroupOf.2 hg
    rw [hK] at hg'
    obtain ⟨h, hh, hhg⟩ := hg'
    refine ⟨h, mem_subgroupOf.1 hh, ?_⟩
    have := congrArg Subtype.val hhg
    simpa [MulAut.conj_apply] using this
  · rintro ⟨x, hx, rfl⟩
    have hx' : (⟨x, hXF hx⟩ : F) ∈ X.subgroupOf F := mem_subgroupOf.2 hx
    have hmem : (MulAut.conj n⁻¹).toMonoidHom ⟨x, hXF hx⟩ ∈ X₂.subgroupOf F := by
      rw [hK]
      exact ⟨_, hx', rfl⟩
    have := mem_subgroupOf.1 hmem
    simpa [MulAut.conj_apply] using this

end Abstract

end CFSG.SeitzReduction.F4Pilot
