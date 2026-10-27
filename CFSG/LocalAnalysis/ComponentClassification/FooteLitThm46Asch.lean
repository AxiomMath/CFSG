module

public import CFSG.LocalAnalysis.ComponentClassification.FooteLitThm46Tools
public import CFSG.LocalAnalysis.ComponentClassification.FooteLitGeneration
public import CFSG.LocalAnalysis.ComponentClassification.FooteLitThm46Pair

public section

namespace CFSG.ComponentClassification.FooteLit

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
  CFSG.ComponentClassification.UnbalancedCorr CFSG.ABGLocalTools
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

omit [Finite G] in
theorem aschbacherThm5OddCore_eq (H : Type*) [Group H] :
    Open.aschbacherThm5OddCore H = pPrimeCore 2 H := by
  unfold Open.aschbacherThm5OddCore pPrimeCore
  congr 1
  ext N
  simp only [Set.mem_ofPred_eq, Nat.coprime_two_left]

omit [Finite G] in
theorem aschbacherThm5Core_eq (D : Subgroup G) : Open.aschbacherThm5Core D = oddCoreIn D := by
  unfold Open.aschbacherThm5Core
  rw [aschbacherThm5OddCore_eq]
  rfl

@[expose] noncomputable def footeAbar (D M : Subgroup G) :
    Subgroup (D ⧸ Open.aschbacherThm5OddCore D) :=
  (M.subgroupOf D).map (QuotientGroup.mk' (Open.aschbacherThm5OddCore D))

omit [Finite G] in
theorem preimage_footeAbar {D M : Subgroup G} (hMD : M ≤ D) :
    Open.aschbacherThm5Preimage D (footeAbar D M) = M ⊔ oddCoreIn D := by
  unfold Open.aschbacherThm5Preimage footeAbar
  rw [Subgroup.comap_map_eq, QuotientGroup.ker_mk', Subgroup.map_sup,
    map_subgroupOf_eq_of_le hMD, ← aschbacherThm5Core_eq]
  rfl

noncomputable def footeAbarEquiv {D M : Subgroup G} (hMD : M ≤ D)
    (hOD : oddCoreIn M ≤ oddCoreIn D) (hDO : M ⊓ oddCoreIn D ≤ oddCoreIn M) :
    M ⧸ pPrimeCore 2 M ≃* footeAbar D M :=
  let φ : M →* D ⧸ Open.aschbacherThm5OddCore D :=
    (QuotientGroup.mk' (Open.aschbacherThm5OddCore D)).comp (Subgroup.inclusion hMD)
  have hker : φ.ker = pPrimeCore 2 M := by
    ext m
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
      QuotientGroup.eq_one_iff, aschbacherThm5OddCore_eq, mem_pPrimeCore_iff_mem_oddCoreIn,
      mem_pPrimeCore_iff_mem_oddCoreIn]
    constructor
    · intro hm
      exact hDO (mem_inf.mpr ⟨m.2, hm⟩)
    · intro hm
      exact hOD hm
  have hrange : φ.range = footeAbar D M := by
    unfold footeAbar
    rw [MonoidHom.range_comp, Subgroup.inclusion_range]
  (QuotientGroup.quotientMulEquivOfEq hker.symm).trans
    ((QuotientGroup.quotientKerEquivRange φ).trans (MulEquiv.subgroupCongr hrange))

theorem open_isQuasisimple_footeAbar (h : FooteSec4 G L) {D M : Subgroup G} (hM : IsFooteM L M)
    (hMD : M ≤ D) (hOD : oddCoreIn M ≤ oddCoreIn D) (hDO : M ⊓ oddCoreIn D ≤ oddCoreIn M) :
    Open.IsQuasisimple (footeAbar D M) := by
  obtain ⟨hs, -⟩ := hM.quotient h
  let e := footeAbarEquiv hMD hOD hDO
  have : IsSimpleGroup (footeAbar D M) := e.symm.isSimpleGroup
  obtain ⟨a, b, hab⟩ := hM.exists_mul_ne h
  exact (open_isQuasisimple_of_isSimpleGroup
    ⟨e a, e b, fun h1 => hab (e.injective (by rw [map_mul, map_mul, h1]))⟩).1

structure Thm46Pair (L M₁ M₂ : Subgroup G) : Prop where
  hM₁ : IsFooteM L M₁
  hM₂ : IsFooteM L M₂
  hne : M₁ ≠ M₂
  hc : ⁅M₁, M₂⁆ ≤ oddCoreIn M₁ ⊓ oddCoreIn M₂
  h12 : M₁ ≤ coreActionKernel M₂
  h21 : M₂ ≤ coreActionKernel M₁

namespace Thm46Pair

variable {M₁ M₂ : Subgroup G}

omit [Finite G] in
theorem symm (hp : Thm46Pair L M₁ M₂) : Thm46Pair L M₂ M₁ :=
  ⟨hp.hM₂, hp.hM₁, hp.hne.symm, by rw [commutator_comm, inf_comm]; exact hp.hc, hp.h21, hp.h12⟩

omit [Finite G] in
theorem le_normalizer (hp : Thm46Pair L M₁ M₂) : M₁ ⊔ M₂ ≤ normalizer (M₁ : Set G) :=
  sup_le Subgroup.le_normalizer fun _ hx => (hp.h21 hx).1

theorem odd (h : FooteSec4 G L) (hp : Thm46Pair L M₁ M₂) :
    Odd (Nat.card ↥(coreActionKernel M₁ ⊓ coreActionKernel M₂)) :=
  odd_card_coreActionKernel_inf h hp.hM₁ hp.hM₂ (hp.hc.trans inf_le_left)

theorem oddCoreIn_le (hp : Thm46Pair L M₁ M₂) : oddCoreIn M₁ ≤ oddCoreIn (M₁ ⊔ M₂) := by
  set D := M₁ ⊔ M₂
  have hOD : oddCoreIn M₁ ≤ D := (map_subtype_le _).trans le_sup_left
  have hDN : D ≤ normalizer ((oddCoreIn M₁ : Subgroup G) : Set G) := fun x hx =>
    mem_normalizer_oddCoreIn (hp.le_normalizer hx)
  exact le_oddCoreIn hOD hDN (odd_card_oddCoreIn M₁)

theorem inf_oddCoreIn_le (_hp : Thm46Pair L M₁ M₂) :
    M₁ ⊓ oddCoreIn (M₁ ⊔ M₂) ≤ oddCoreIn M₁ := by
  refine le_oddCoreIn inf_le_left (fun x hx => mem_normalizer_inf' (Subgroup.le_normalizer hx)
    (mem_normalizer_oddCoreIn (Subgroup.le_normalizer
      ((le_sup_left : M₁ ≤ M₁ ⊔ M₂) hx))))
    (Odd.of_dvd_nat (odd_card_oddCoreIn _) (card_dvd_of_le inf_le_right))

theorem inf_oddCoreIn_le' (hp : Thm46Pair L M₁ M₂) :
    M₂ ⊓ oddCoreIn (M₁ ⊔ M₂) ≤ oddCoreIn M₂ := by
  have h1 := hp.symm.inf_oddCoreIn_le
  rwa [sup_comm] at h1

theorem oddCoreIn_le' (hp : Thm46Pair L M₁ M₂) : oddCoreIn M₂ ≤ oddCoreIn (M₁ ⊔ M₂) := by
  have h1 := hp.symm.oddCoreIn_le
  rwa [sup_comm] at h1

theorem map_conj_mem (h : FooteSec4 G L) (hp : Thm46Pair L M₁ M₂) {x : G}
    (hx : x ∈ normalizer ((M₁ ⊔ M₂ : Subgroup G) : Set G)) {M : Subgroup G}
    (hM : M = M₁ ∨ M = M₂) :
    M.map (MulAut.conj x).toMonoidHom = M₁ ∨ M.map (MulAut.conj x).toMonoidHom = M₂ := by
  set D := M₁ ⊔ M₂ with hD
  have hMF : IsFooteM L M := by rcases hM with rfl | rfl; exacts [hp.hM₁, hp.hM₂]
  have hMD : M ≤ D := by rcases hM with rfl | rfl; exacts [le_sup_left, le_sup_right]
  have hDM : D ≤ normalizer (M : Set G) := by
    rcases hM with rfl | rfl
    · exact hp.le_normalizer
    · rw [hD, sup_comm]; exact hp.symm.le_normalizer
  set M' := M.map (MulAut.conj x).toMonoidHom with hM'
  have hM'eq : M' = conjugate M x⁻¹ := by
    rw [hM']
    unfold conjugate
    rw [inv_inv]
  have hM'F : IsFooteM L M' := hM'eq ▸ isFooteM_conjugate h hMF x⁻¹
  have hM'D : M' ≤ D := by
    rw [← map_conj_eq_of_mem_normalizer hx]
    exact map_mono hMD
  have hDM' : D ≤ normalizer (M' : Set G) := by
    intro d hd
    apply mem_normalizer_of_map_conj_eq
    have hd' : x⁻¹ * d * x ∈ D := by
      have h1 := (mem_normalizer_iff.mp (inv_mem hx) d).mp hd
      rwa [inv_inv] at h1
    have h2 := map_conj_eq_of_mem_normalizer (hDM hd')
    rw [hM', Subgroup.map_map, show (MulAut.conj d).toMonoidHom.comp (MulAut.conj x).toMonoidHom =
      (MulAut.conj x).toMonoidHom.comp (MulAut.conj (x⁻¹ * d * x)).toMonoidHom by
        ext y; simp [MulAut.conj_apply]; group, ← Subgroup.map_map, h2]
  have hpair : ∀ N : Subgroup G, N = M₁ ∨ N = M₂ →
      M' = N ∨ M' ≤ coreActionKernel N := by
    intro N hN
    have hNF : IsFooteM L N := by rcases hN with rfl | rfl; exacts [hp.hM₁, hp.hM₂]
    have hND : N ≤ D := by rcases hN with rfl | rfl; exacts [le_sup_left, le_sup_right]
    have hDN : D ≤ normalizer (N : Set G) := by
      rcases hN with rfl | rfl
      · exact hp.le_normalizer
      · rw [hD, sup_comm]; exact hp.symm.le_normalizer
    rcases foote_thm46_pair h hM'F hNF (commutator_le_inf_of_le_normalizer (hM'D.trans hDN)
      (hND.trans hDM')) with h1 | ⟨-, h1, -⟩
    · exact Or.inl h1
    · exact Or.inr h1
  rcases hpair M₁ (Or.inl rfl) with h1 | h1
  · exact Or.inl h1
  rcases hpair M₂ (Or.inr rfl) with h2 | h2
  · exact Or.inr h2
  exfalso
  apply hM'F.not_odd h
  exact Odd.of_dvd_nat (hp.odd h) (card_dvd_of_le (le_inf h1 h2))

omit [Finite G] in
theorem map_conj_mul (M : Subgroup G) (x y : G) :
    M.map (MulAut.conj (x * y)).toMonoidHom =
      (M.map (MulAut.conj y).toMonoidHom).map (MulAut.conj x).toMonoidHom := by
  rw [Subgroup.map_map]
  congr 1
  ext m
  simp [MulAut.conj_apply, mul_assoc]

theorem fix_or_swap (h : FooteSec4 G L) (hp : Thm46Pair L M₁ M₂) {x : G}
    (hx : x ∈ normalizer ((M₁ ⊔ M₂ : Subgroup G) : Set G)) :
    (M₁.map (MulAut.conj x).toMonoidHom = M₁ ∧ M₂.map (MulAut.conj x).toMonoidHom = M₂) ∨
      (M₁.map (MulAut.conj x).toMonoidHom = M₂ ∧ M₂.map (MulAut.conj x).toMonoidHom = M₁) := by
  have hinj : ∀ {A B : Subgroup G}, A.map (MulAut.conj x).toMonoidHom =
      B.map (MulAut.conj x).toMonoidHom → A = B := fun hAB =>
    map_injective (MulAut.conj x).injective hAB
  rcases hp.map_conj_mem h hx (Or.inl rfl) with h1 | h1 <;>
    rcases hp.map_conj_mem h hx (Or.inr rfl) with h2 | h2
  · exact absurd (hinj (h1.trans h2.symm)) hp.hne
  · exact Or.inl ⟨h1, h2⟩
  · exact Or.inr ⟨h1, h2⟩
  · exact absurd (hinj (h1.trans h2.symm)) hp.hne

theorem le_normalizer_of_perfect (h : FooteSec4 G L) (hp : Thm46Pair L M₁ M₂) {Y : Subgroup G}
    (hYN : Y ≤ normalizer ((M₁ ⊔ M₂ : Subgroup G) : Set G)) (hY : ⁅Y, Y⁆ = Y) :
    Y ≤ normalizer (M₁ : Set G) ⊓ normalizer (M₂ : Set G) := by
  set D := M₁ ⊔ M₂ with hD
  have hP : ∀ {x : G}, x ∈ normalizer (M₁ : Set G) ↔
      M₁.map (MulAut.conj x).toMonoidHom = M₁ :=
    ⟨fun hx => map_conj_eq_of_mem_normalizer hx, mem_normalizer_of_map_conj_eq⟩
  have hmul : ∀ x ∈ normalizer (D : Set G), ∀ y ∈ normalizer (D : Set G),
      (x * y ∈ normalizer (M₁ : Set G) ↔
        (x ∈ normalizer (M₁ : Set G) ↔ y ∈ normalizer (M₁ : Set G))) := by
    intro x hx y hy
    rw [hP, hP, hP, map_conj_mul]
    rcases hp.fix_or_swap h hx with ⟨hx1, hx2⟩ | ⟨hx1, hx2⟩ <;>
      rcases hp.fix_or_swap h hy with ⟨hy1, hy2⟩ | ⟨hy1, hy2⟩
    · rw [hy1, hx1]; simp
    · rw [hy1, hx2, hx1]; simp [hp.hne.symm]
    · rw [hy1, hx1]; simp [hp.hne.symm]
    · rw [hy1, hx2, hx1]; simp
  have hcomm : ⁅Y, Y⁆ ≤ normalizer (M₁ : Set G) := by
    rw [commutator_le]
    intro a ha b hb
    have ha' := hYN ha
    have hb' := hYN hb
    rw [commutatorElement_def, show a * b * a⁻¹ * b⁻¹ = a * b * (a⁻¹ * b⁻¹) by group,
      hmul _ (mul_mem ha' hb') _ (mul_mem (inv_mem ha') (inv_mem hb')),
      hmul _ ha' _ hb', hmul _ (inv_mem ha') _ (inv_mem hb'),
      inv_mem_iff (x := a), inv_mem_iff (x := b)]
  have hY₁ : Y ≤ normalizer (M₁ : Set G) := hY ▸ hcomm
  refine le_inf hY₁ fun x hx => ?_
  rcases hp.fix_or_swap h (hYN hx) with ⟨-, hx2⟩ | ⟨hx1, -⟩
  · exact mem_normalizer_of_map_conj_eq hx2
  · exact absurd ((hP.mp (hY₁ hx)).symm.trans hx1) hp.hne

end Thm46Pair

end CFSG.ComponentClassification.FooteLit
