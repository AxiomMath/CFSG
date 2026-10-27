module

public import CFSG.LocalAnalysis.SeitzReduction.F4PilotPositionBasic

public section

namespace CFSG.SeitzReduction.EPilot

open Subgroup
open scoped Pointwise

variable {G : Type*} [Group G]

section Radical

theorem le_of_le_sup_of_forall_normal_isPGroup {p : ℕ} {Q₁ M₁ Q₂ : Subgroup G}
    (hQ₁ : IsPGroup p Q₁) (hQ₂ : IsPGroup p Q₂)
    (hM₁ : ∀ N : Subgroup M₁, N.Normal → IsPGroup p N → N = ⊥)
    (hM₁N : M₁ ≤ normalizer (Q₁ : Set G)) (hQ₂le : Q₂ ≤ Q₁ ⊔ M₁)
    (hQ₂N : Q₁ ⊔ M₁ ≤ normalizer (Q₂ : Set G)) : Q₂ ≤ Q₁ := by
  have hΛN : Q₁ ⊔ M₁ ≤ normalizer (Q₁ : Set G) := sup_le le_normalizer hM₁N
  have hNp : IsPGroup p (Q₁ ⊔ Q₂ : Subgroup G) :=
    hQ₁.to_sup_of_normal_left' hQ₂ (hQ₂le.trans hΛN)
  have hnorm : ((Q₁ ⊔ Q₂).subgroupOf M₁).Normal := by
    refine ⟨fun n hn m => ?_⟩
    rw [mem_subgroupOf] at hn ⊢
    have hm : (m : G) ∈ normalizer ((Q₁ ⊔ Q₂ : Subgroup G) : Set G) :=
      F4Pilot.mem_normalizer_sup (hM₁N m.2) (hQ₂N (mem_sup_right m.2))
    have := (mem_normalizer_iff.1 hm n).1 hn
    simpa using this
  have hbot := hM₁ _ hnorm hNp.comap_subtype
  intro x hx
  have hx' : x ∈ ((Q₁ ⊔ M₁ : Subgroup G) : Set G) := hQ₂le hx
  rw [coe_mul_of_right_le_normalizer_left Q₁ M₁ hM₁N] at hx'
  obtain ⟨q, hq, m, hm, rfl⟩ := hx'
  have hmN : m ∈ Q₁ ⊔ Q₂ := by
    have : q⁻¹ * (q * m) ∈ Q₁ ⊔ Q₂ := mul_mem (mem_sup_left (inv_mem hq)) (mem_sup_right hx)
    simpa using this
  have hm1 : (⟨m, hm⟩ : M₁) ∈ (Q₁ ⊔ Q₂).subgroupOf M₁ := mem_subgroupOf.2 hmN
  rw [hbot, mem_bot] at hm1
  have hm1' : m = 1 := congrArg Subtype.val hm1
  subst hm1'
  simpa using hq

theorem eq_of_sup_eq_of_forall_normal_isPGroup {p : ℕ} {Q₁ M₁ Q₂ M₂ : Subgroup G}
    (hQ₁ : IsPGroup p Q₁) (hQ₂ : IsPGroup p Q₂)
    (hM₁ : ∀ N : Subgroup M₁, N.Normal → IsPGroup p N → N = ⊥)
    (hM₂ : ∀ N : Subgroup M₂, N.Normal → IsPGroup p N → N = ⊥)
    (hM₁N : M₁ ≤ normalizer (Q₁ : Set G)) (hM₂N : M₂ ≤ normalizer (Q₂ : Set G))
    (hΛ : Q₁ ⊔ M₁ = Q₂ ⊔ M₂) : Q₁ = Q₂ :=
  le_antisymm
    (le_of_le_sup_of_forall_normal_isPGroup hQ₂ hQ₁ hM₂ hM₂N (le_sup_left.trans hΛ.le)
      (hΛ.ge.trans (sup_le le_normalizer hM₁N)))
    (le_of_le_sup_of_forall_normal_isPGroup hQ₁ hQ₂ hM₁ hM₁N (le_sup_left.trans hΛ.ge)
      (hΛ.le.trans (sup_le le_normalizer hM₂N)))

theorem forall_normal_isPGroup_eq_bot_of_isSimpleGroup {M : Type*} [Group M] [Finite M]
    {p : ℕ} [Fact p.Prime] [IsSimpleGroup M] (hnab : ∃ a b : M, a * b ≠ b * a)
    (N : Subgroup M) (hN : N.Normal) (hNp : IsPGroup p N) : N = ⊥ := by
  rcases hN.eq_bot_or_eq_top with h | h
  · exact h
  · exfalso
    obtain ⟨a, b, hab⟩ := hnab
    have hMp : IsPGroup p M := by
      rw [h] at hNp
      exact hNp.of_equiv Subgroup.topEquiv
    have : Nontrivial (center M) := hMp.center_nontrivial
    rcases (inferInstance : (center M).Normal).eq_bot_or_eq_top with hZ | hZ
    · obtain ⟨z, hz⟩ := exists_ne (1 : center M)
      apply hz
      have hz' : (z : M) ∈ (⊥ : Subgroup M) := hZ ▸ z.2
      exact Subtype.ext (mem_bot.1 hz')
    · have hb : b ∈ center M := hZ ▸ mem_top b
      exact hab (mem_center_iff.1 hb a)

theorem forall_normal_isPGroup_eq_bot_of_isSimpleGroup_of_perfect [Finite G] {p : ℕ}
    [Fact p.Prime] {Q M : Subgroup G} (hQ : IsPGroup p Q) (hMN : M ≤ normalizer (Q : Set G))
    (hM : IsSimpleGroup M) (hperf : ⁅Q ⊔ M, Q ⊔ M⁆ = Q ⊔ M) (N : Subgroup M) (hN : N.Normal)
    (hNp : IsPGroup p N) : N = ⊥ := by
  rcases hN.eq_bot_or_eq_top with h | h
  · exact h
  · exfalso
    have hMp : IsPGroup p M := by
      rw [h] at hNp
      exact hNp.of_equiv Subgroup.topEquiv
    have hQMp : IsPGroup p (Q ⊔ M : Subgroup G) := hQ.to_sup_of_normal_left' hMp hMN
    have : Group.IsNilpotent (Q ⊔ M : Subgroup G) := hQMp.isNilpotent
    have hbot := perfect_eq_bot_of_le (A := Q ⊔ M) inferInstance hperf le_rfl
    have hMbot : M = ⊥ := le_bot_iff.1 (hbot ▸ le_sup_right)
    obtain ⟨a, b, hab⟩ := exists_pair_ne M
    apply hab
    have ha : (a : G) = 1 := (eq_bot_iff_forall M).1 hMbot _ a.2
    have hb : (b : G) = 1 := (eq_bot_iff_forall M).1 hMbot _ b.2
    exact Subtype.ext (ha.trans hb.symm)

end Radical

section Complements

variable {Q M M' : Subgroup G}

theorem le_normalizer_of_sup_eq (hMN : M ≤ normalizer (Q : Set G)) (hMM' : Q ⊔ M = Q ⊔ M') :
    M' ≤ normalizer (Q : Set G) :=
  le_sup_right.trans (hMM'.ge.trans (sup_le le_normalizer hMN))

noncomputable def mulEquivOfComplements (hMN : M ≤ normalizer (Q : Set G)) (hM : Disjoint Q M)
    (hM' : Disjoint Q M') (hMM' : Q ⊔ M = Q ⊔ M') : M ≃* M' :=
  Classical.choose (F4Pilot.exists_mulEquiv_of_sup_eq hMM' (disjoint_iff.1 hM)
    (disjoint_iff.1 hM') hMN (le_normalizer_of_sup_eq hMN hMM'))

variable (hMN : M ≤ normalizer (Q : Set G)) (hM : Disjoint Q M) (hM' : Disjoint Q M')
  (hMM' : Q ⊔ M = Q ⊔ M')

theorem mulEquivOfComplements_inv_mul_mem (m : M) :
    ((mulEquivOfComplements hMN hM hM' hMM' m : M') : G)⁻¹ * m ∈ Q :=
  Classical.choose_spec (F4Pilot.exists_mulEquiv_of_sup_eq hMM' (disjoint_iff.1 hM)
    (disjoint_iff.1 hM') hMN (le_normalizer_of_sup_eq hMN hMM')) m

theorem mulEquivOfComplements_eq_iff (m : M) (m' : M') :
    mulEquivOfComplements hMN hM hM' hMM' m = m' ↔ (m' : G)⁻¹ * m ∈ Q := by
  constructor
  · rintro rfl
    exact mulEquivOfComplements_inv_mul_mem hMN hM hM' hMM' m
  · intro h
    set ι := mulEquivOfComplements hMN hM hM' hMM' with hι
    have h1 : ((ι m : M') : G)⁻¹ * m ∈ Q := mulEquivOfComplements_inv_mul_mem hMN hM hM' hMM' m
    have h2 : (m' : G)⁻¹ * (ι m : G) ∈ Q ⊓ M' := by
      refine ⟨?_, M'.mul_mem (M'.inv_mem m'.2) (ι m).2⟩
      have e : (m' : G)⁻¹ * (ι m : G) = ((m' : G)⁻¹ * m) * (((ι m : M') : G)⁻¹ * m)⁻¹ := by
        group
      rw [e]
      exact Q.mul_mem h (Q.inv_mem h1)
    rw [disjoint_iff.1 hM', mem_bot, inv_mul_eq_one] at h2
    exact Subtype.ext h2.symm

theorem map_mulEquivOfComplements {J : Subgroup G} (hJ : J ≤ M) :
    ((J.subgroupOf M).map (mulEquivOfComplements hMN hM hM' hMM').toMonoidHom).map M'.subtype =
      (J ⊔ Q) ⊓ M' := by
  set ι := mulEquivOfComplements hMN hM hM' hMM' with hι
  apply le_antisymm
  · rintro _ ⟨_, ⟨j, hj, rfl⟩, rfl⟩
    have hjJ : (j : G) ∈ J := mem_subgroupOf.1 hj
    have h : ((ι j : M') : G)⁻¹ * j ∈ Q := mulEquivOfComplements_inv_mul_mem hMN hM hM' hMM' j
    refine ⟨?_, (ι j).2⟩
    have e : ((ι j : M') : G) = j * ((((ι j : M') : G))⁻¹ * j)⁻¹ := by group
    simp only [MulEquiv.coe_toMonoidHom, coe_subtype]
    rw [e]
    exact mul_mem (mem_sup_left hjJ) (mem_sup_right (inv_mem h))
  · rintro x ⟨hxJQ, hxM'⟩
    have hJN : J ≤ normalizer (Q : Set G) := hJ.trans hMN
    have hx : x ∈ ((Q ⊔ J : Subgroup G) : Set G) := by
      rw [sup_comm]
      exact hxJQ
    rw [coe_mul_of_right_le_normalizer_left Q J hJN] at hx
    obtain ⟨q, hq, j, hj, rfl⟩ := hx
    have hιj : ι ⟨j, hJ hj⟩ = ⟨q * j, hxM'⟩ := by
      rw [hι, mulEquivOfComplements_eq_iff]
      have e : (q * j)⁻¹ * j = j⁻¹ * q⁻¹ * j := by group
      change (q * j)⁻¹ * j ∈ Q
      rw [e]
      exact (mem_normalizer_iff''.1 (hJN hj) q⁻¹).1 (inv_mem hq)
    refine ⟨ι ⟨j, hJ hj⟩, ⟨⟨j, hJ hj⟩, mem_subgroupOf.2 hj, rfl⟩, ?_⟩
    rw [hιj]
    rfl

theorem sup_map_mulEquivOfComplements {X : Subgroup G} (hX : X ≤ M) :
    Q ⊔ ((X.subgroupOf M).map (mulEquivOfComplements hMN hM hM' hMM').toMonoidHom).map
      M'.subtype = Q ⊔ X := by
  rw [map_mulEquivOfComplements hMN hM hM' hMM' hX]
  apply le_antisymm
  · refine sup_le le_sup_left (inf_le_left.trans ?_)
    rw [sup_comm]
  · refine sup_le le_sup_left fun x hx => ?_
    set ι := mulEquivOfComplements hMN hM hM' hMM' with hι
    have h : ((ι ⟨x, hX hx⟩ : M') : G)⁻¹ * x ∈ Q :=
      mulEquivOfComplements_inv_mul_mem hMN hM hM' hMM' ⟨x, hX hx⟩
    have hιx : ((ι ⟨x, hX hx⟩ : M') : G) ∈ (X ⊔ Q) ⊓ M' := by
      refine ⟨?_, (ι ⟨x, hX hx⟩).2⟩
      have e : ((ι ⟨x, hX hx⟩ : M') : G) = x * ((((ι ⟨x, hX hx⟩ : M') : G))⁻¹ * x)⁻¹ := by
        group
      rw [e]
      exact mul_mem (mem_sup_left hx) (mem_sup_right (inv_mem h))
    have e : x = ((ι ⟨x, hX hx⟩ : M') : G) * ((((ι ⟨x, hX hx⟩ : M') : G))⁻¹ * x) := by group
    rw [e]
    exact mul_mem (mem_sup_right hιx) (mem_sup_left h)

end Complements

section Transport

variable [Finite G]

theorem exists_conj_le_inf_sup_of_complements {p : ℕ} [Fact p.Prime]
    {Q M M' J X : Subgroup G} (hQ : IsPGroup p Q) (hMN : M ≤ normalizer (Q : Set G))
    (hM : Disjoint Q M) (hM' : Disjoint Q M') (hMM' : Q ⊔ M = Q ⊔ M') (hJ : J ≤ M)
    (hXJ : X ≤ J) (hX : ¬ p ∣ Nat.card X) :
    ∃ q₀ ∈ Q, X ≤ ((J ⊔ Q) ⊓ M').map (MulAut.conj q₀).toMonoidHom := by
  have hXM : X ≤ M := hXJ.trans hJ
  set X₂ : Subgroup G :=
    ((X.subgroupOf M).map (mulEquivOfComplements hMN hM hM' hMM').toMonoidHom).map M'.subtype
    with hX₂
  have hX₂eq : X₂ = (X ⊔ Q) ⊓ M' := map_mulEquivOfComplements hMN hM hM' hMM' hXM
  have hX₂le : X₂ ≤ (J ⊔ Q) ⊓ M' := by
    rw [hX₂eq]
    exact inf_le_inf_right M' (sup_le_sup_right hXJ Q)
  have hX₂M' : X₂ ≤ M' := hX₂le.trans inf_le_right
  have hM'N : M' ≤ normalizer (Q : Set G) := le_normalizer_of_sup_eq hMN hMM'
  have hQX : Q ⊓ X = ⊥ :=
    le_bot_iff.1 ((inf_le_inf_left Q hXM).trans (disjoint_iff.1 hM).le)
  have hQX₂ : Q ⊓ X₂ = ⊥ :=
    le_bot_iff.1 ((inf_le_inf_left Q hX₂M').trans (disjoint_iff.1 hM').le)
  have hsup : Q ⊔ X = Q ⊔ X₂ := (sup_map_mulEquivOfComplements hMN hM hM' hMM' hXM).symm
  obtain ⟨n, hn, hX₂conj⟩ := F4Pilot.exists_mem_conj_eq_of_complement hQ hX (hXM.trans hMN)
    (hX₂M'.trans hM'N) hQX hQX₂ hsup
  refine ⟨n, hn, fun x hx => ?_⟩
  have hx₂ : n⁻¹ * x * n ∈ X₂ := by
    rw [hX₂conj]
    exact ⟨x, hx, by simp⟩
  refine ⟨n⁻¹ * x * n, hX₂le hx₂, ?_⟩
  change n * (n⁻¹ * x * n) * n⁻¹ = x
  group

theorem exists_conj_le_inf_sup_of_complements_of_odd {Q M M' J X : Subgroup G}
    (hQ : IsPGroup 2 Q) (hMN : M ≤ normalizer (Q : Set G)) (hM : Disjoint Q M)
    (hM' : Disjoint Q M') (hMM' : Q ⊔ M = Q ⊔ M') (hJ : J ≤ M) (hXJ : X ≤ J)
    (hX : Odd (Nat.card X)) :
    ∃ q₀ ∈ Q, X ≤ ((J ⊔ Q) ⊓ M').map (MulAut.conj q₀).toMonoidHom :=
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exists_conj_le_inf_sup_of_complements hQ hMN hM hM' hMM' hJ hXJ
    fun h => (Nat.not_even_iff_odd.2 hX) (even_iff_two_dvd.2 h)

theorem exists_conj_le_inf_sup_of_two_decompositions {p : ℕ} [Fact p.Prime]
    {Q₁ M₁ Q₂ M₂ J X : Subgroup G} (hQ₁ : IsPGroup p Q₁) (hQ₂ : IsPGroup p Q₂)
    (hM₁ : ∀ N : Subgroup M₁, N.Normal → IsPGroup p N → N = ⊥)
    (hM₂ : ∀ N : Subgroup M₂, N.Normal → IsPGroup p N → N = ⊥)
    (hM₁N : M₁ ≤ normalizer (Q₁ : Set G)) (hM₂N : M₂ ≤ normalizer (Q₂ : Set G))
    (hQM₁ : Disjoint Q₁ M₁) (hQM₂ : Disjoint Q₂ M₂) (hΛ : Q₁ ⊔ M₁ = Q₂ ⊔ M₂) (hJ : J ≤ M₁)
    (hXJ : X ≤ J) (hX : ¬ p ∣ Nat.card X) :
    Q₁ = Q₂ ∧ ∃ q₀ ∈ Q₁, X ≤ ((J ⊔ Q₁) ⊓ M₂).map (MulAut.conj q₀).toMonoidHom := by
  have hQ := eq_of_sup_eq_of_forall_normal_isPGroup hQ₁ hQ₂ hM₁ hM₂ hM₁N hM₂N hΛ
  subst hQ
  exact ⟨rfl, exists_conj_le_inf_sup_of_complements hQ₁ hM₁N hQM₁ hQM₂ hΛ hJ hXJ hX⟩

end Transport

section Coordinates

theorem forall_normal_isPGroup_eq_bot_of_mulEquiv {A B : Type*} [Group A] [Group B] {p : ℕ}
    (e : A ≃* B) (hA : ∀ N : Subgroup A, N.Normal → IsPGroup p N → N = ⊥) (N : Subgroup B)
    (hN : N.Normal) (hNp : IsPGroup p N) : N = ⊥ := by
  have h := hA (N.comap e.toMonoidHom) (hN.comap _) (hNp.comap_of_injective _ e.injective)
  rw [eq_bot_iff]
  intro x hx
  have hx' : e.symm x ∈ N.comap e.toMonoidHom := by
    rw [mem_comap]
    simpa using hx
  rw [h, mem_bot] at hx'
  rw [mem_bot, ← e.apply_symm_apply x, hx', map_one]

variable [Finite G]

theorem exists_conj_le_map_of_two_decompositions {p : ℕ} [Fact p.Prime]
    {C C' : Type*} [Group C] [Group C'] {φ : C →* G} {φ' : C' →* G}
    (hφ : Function.Injective φ) (hφ' : Function.Injective φ')
    {Q M : Subgroup C} {Q' M' : Subgroup C'} (hQ : IsPGroup p Q) (hQ' : IsPGroup p Q')
    (hM : ∀ N : Subgroup M, N.Normal → IsPGroup p N → N = ⊥)
    (hM' : ∀ N : Subgroup M', N.Normal → IsPGroup p N → N = ⊥)
    (hMN : M ≤ normalizer (Q : Set C)) (hM'N : M' ≤ normalizer (Q' : Set C'))
    (hQM : Disjoint Q M) (hQM' : Disjoint Q' M') (hΛ : (Q ⊔ M).map φ = (Q' ⊔ M').map φ')
    {J : Subgroup C} (hJ : J ≤ M) {X : Subgroup G} (hXJ : X ≤ J.map φ)
    (hX : ¬ p ∣ Nat.card X) :
    Q.map φ = Q'.map φ' ∧ ∃ ι : M ≃* M', (∀ m : M, (φ' (ι m))⁻¹ * φ m ∈ Q.map φ) ∧
      ∃ q₀ ∈ Q.map φ, X ≤ ((((J.subgroupOf M).map ι.toMonoidHom).map M'.subtype).map φ').map
        (MulAut.conj q₀).toMonoidHom := by
  have hQ₁ : IsPGroup p (Q.map φ) := hQ.map φ
  have hQ₂ : IsPGroup p (Q'.map φ') := hQ'.map φ'
  set eM := M.equivMapOfInjective φ hφ with heM
  set eM' := M'.equivMapOfInjective φ' hφ' with heM'
  have hM₁ := forall_normal_isPGroup_eq_bot_of_mulEquiv eM hM
  have hM₂ := forall_normal_isPGroup_eq_bot_of_mulEquiv eM' hM'
  have hM₁N : M.map φ ≤ normalizer ((Q.map φ : Subgroup G) : Set G) :=
    (map_mono hMN).trans (le_normalizer_map φ)
  have hM₂N : M'.map φ' ≤ normalizer ((Q'.map φ' : Subgroup G) : Set G) :=
    (map_mono hM'N).trans (le_normalizer_map φ')
  have hd₁ : Disjoint (Q.map φ) (M.map φ) := by
    rw [disjoint_iff, ← map_inf_eq _ _ _ hφ, disjoint_iff.1 hQM, Subgroup.map_bot]
  have hd₂ : Disjoint (Q'.map φ') (M'.map φ') := by
    rw [disjoint_iff, ← map_inf_eq _ _ _ hφ', disjoint_iff.1 hQM', Subgroup.map_bot]
  have hΛ' : Q.map φ ⊔ M.map φ = Q'.map φ' ⊔ M'.map φ' := by
    rw [← Subgroup.map_sup, ← Subgroup.map_sup]
    exact hΛ
  have hQeq : Q.map φ = Q'.map φ' :=
    eq_of_sup_eq_of_forall_normal_isPGroup hQ₁ hQ₂ hM₁ hM₂ hM₁N hM₂N hΛ'
  rw [← hQeq] at hd₂ hΛ'
  set ιG := mulEquivOfComplements hM₁N hd₁ hd₂ hΛ' with hιG
  set ι : M ≃* M' := eM.trans (ιG.trans eM'.symm) with hι
  have hιφ : ∀ m : M, φ' (ι m) = (ιG (eM m) : G) := by
    intro m
    have h1 : eM' (ι m) = ιG (eM m) := by
      rw [hι, MulEquiv.trans_apply, MulEquiv.trans_apply, MulEquiv.apply_symm_apply]
    have h2 := congrArg Subtype.val h1
    rwa [heM', coe_equivMapOfInjective_apply] at h2
  have hspec : ∀ m : M, (φ' (ι m))⁻¹ * φ m ∈ Q.map φ := by
    intro m
    rw [hιφ]
    have h := mulEquivOfComplements_inv_mul_mem hM₁N hd₁ hd₂ hΛ' (eM m)
    rwa [heM, coe_equivMapOfInjective_apply] at h
  have hJ₁ : J.map φ ≤ M.map φ := map_mono hJ
  obtain ⟨q₀, hq₀, hXq⟩ :=
    exists_conj_le_inf_sup_of_complements hQ₁ hM₁N hd₁ hd₂ hΛ' hJ₁ hXJ hX
  refine ⟨hQeq, ι, hspec, q₀, hq₀, hXq.trans (map_mono ?_)⟩
  rw [← map_mulEquivOfComplements hM₁N hd₁ hd₂ hΛ' hJ₁]
  rintro _ ⟨_, ⟨z, hz, rfl⟩, rfl⟩
  obtain ⟨j, hj, hjz⟩ := (mem_subgroupOf.1 hz : (z : G) ∈ J.map φ)
  have hz' : z = eM ⟨j, hJ hj⟩ := Subtype.ext (by
    rw [heM, coe_equivMapOfInjective_apply]
    exact hjz.symm)
  refine ⟨(ι ⟨j, hJ hj⟩ : C'), ⟨ι ⟨j, hJ hj⟩, ⟨⟨j, hJ hj⟩, mem_subgroupOf.2 hj, rfl⟩, rfl⟩, ?_⟩
  rw [hιφ, hz']
  rfl

omit [Finite G] in
theorem exists_le_range_inf_centralizer_of_le_conj {C' : Type*} [Group C'] {φ' : C' →* G}
    (hφ' : Function.Injective φ') {J' : Subgroup C'} {X : Subgroup G} {q₀ : G}
    (hq₀ : q₀ ∈ φ'.range) (hX : X ≤ (J'.map φ').map (MulAut.conj q₀).toMonoidHom) :
    ∃ P : Subgroup G, P ≤ φ'.range ⊓ centralizer (X : Set G) ∧
      Nonempty (P ≃* centralizer (J' : Set C')) := by
  refine ⟨((centralizer (J' : Set C')).map φ').map (MulAut.conj q₀).toMonoidHom, le_inf ?_ ?_, ?_⟩
  · rintro _ ⟨_, ⟨c, -, rfl⟩, rfl⟩
    obtain ⟨n', rfl⟩ := hq₀
    exact ⟨n' * c * n'⁻¹, by simp [MulAut.conj_apply]⟩
  · rintro _ ⟨_, ⟨c, hc, rfl⟩, rfl⟩
    rw [mem_centralizer_iff]
    intro x hx
    obtain ⟨_, ⟨j, hj, rfl⟩, hjx⟩ := hX hx
    have hcj := mem_centralizer_iff.1 hc j hj
    have hφc : φ' j * φ' c = φ' c * φ' j := by rw [← map_mul, ← map_mul, hcj]
    rw [← hjx]
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    calc q₀ * φ' j * q₀⁻¹ * (q₀ * φ' c * q₀⁻¹) = q₀ * (φ' j * φ' c) * q₀⁻¹ := by group
      _ = q₀ * (φ' c * φ' j) * q₀⁻¹ := by rw [hφc]
      _ = q₀ * φ' c * q₀⁻¹ * (q₀ * φ' j * q₀⁻¹) := by group
  · exact ⟨(((centralizer (J' : Set C')).map φ').equivMapOfInjective _
      (MulAut.conj q₀).injective).symm.trans
      ((centralizer (J' : Set C')).equivMapOfInjective _ hφ').symm⟩

theorem exists_le_centralizer_mulEquiv_of_two_decompositions {p : ℕ} [Fact p.Prime]
    {C C' : Type*} [Group C] [Group C'] {φ : C →* G} {φ' : C' →* G}
    (hφ : Function.Injective φ) (hφ' : Function.Injective φ')
    {Q M : Subgroup C} {Q' M' : Subgroup C'} (hQ : IsPGroup p Q) (hQ' : IsPGroup p Q')
    (hM : ∀ N : Subgroup M, N.Normal → IsPGroup p N → N = ⊥)
    (hM' : ∀ N : Subgroup M', N.Normal → IsPGroup p N → N = ⊥)
    (hMN : M ≤ normalizer (Q : Set C)) (hM'N : M' ≤ normalizer (Q' : Set C'))
    (hQM : Disjoint Q M) (hQM' : Disjoint Q' M') (hΛ : (Q ⊔ M).map φ = (Q' ⊔ M').map φ')
    {J : Subgroup C} (hJ : J ≤ M) {X : Subgroup G} (hXJ : X ≤ J.map φ)
    (hX : ¬ p ∣ Nat.card X) :
    ∃ ι : M ≃* M', (∀ m : M, (φ' (ι m))⁻¹ * φ m ∈ Q.map φ) ∧
      ∃ P : Subgroup G, P ≤ φ'.range ⊓ centralizer (X : Set G) ∧
        Nonempty (P ≃* centralizer
          ((((J.subgroupOf M).map ι.toMonoidHom).map M'.subtype : Subgroup C') : Set C')) := by
  obtain ⟨hQeq, ι, hspec, q₀, hq₀, hXq⟩ := exists_conj_le_map_of_two_decompositions hφ hφ' hQ
    hQ' hM hM' hMN hM'N hQM hQM' hΛ hJ hXJ hX
  have hq₀' : q₀ ∈ φ'.range := by
    rw [hQeq] at hq₀
    obtain ⟨n, -, rfl⟩ := hq₀
    exact ⟨n, rfl⟩
  exact ⟨ι, hspec, exists_le_range_inf_centralizer_of_le_conj hφ' hq₀' hXq⟩

end Coordinates

end CFSG.SeitzReduction.EPilot
