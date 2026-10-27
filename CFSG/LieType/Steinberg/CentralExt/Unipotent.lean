module

public import CFSG.LieType.Steinberg.PartBHalfSpace
public import Mathlib.GroupTheory.PGroup

public section

namespace CFSG.LieType.Steinberg

open CFSG.LieType.Universal CFSG.LieType.RootSystem
open scoped commutatorElement

section Collection

variable {G : Type*} [Group G] {V : Type*} {p : ℕ}

theorem isPGroup_iSup_of_commutator_mem (A : V → Subgroup G) (h : V → ℤ) :
    ∀ {L : List V}, L.Nodup → L.Pairwise (fun a b => h a ≤ h b) →
      (∀ a ∈ L, ∀ b ∈ L, a ≠ b → ∀ x ∈ A a, ∀ y ∈ A b,
        ⁅x, y⁆ ∈ ⨆ c ∈ L, ⨆ (_ : min (h a) (h b) < h c), A c) →
      (∀ v ∈ L, IsPGroup p (A v)) → IsPGroup p ↥(⨆ v ∈ L, A v)
  | [], _, _, _, _ => by
    rw [show (⨆ v ∈ ([] : List V), A v) = ⊥ from iSup₂_eq_bot.2 fun v hv => by simp at hv]
    exact IsPGroup.of_bot
  | a :: L, hnd, hs, hc, hA => by
    obtain ⟨haL, hnd⟩ := List.nodup_cons.1 hnd
    obtain ⟨hah, hs⟩ := List.pairwise_cons.1 hs
    have hdrop : ∀ {m : ℤ}, h a ≤ m →
        ⨆ c ∈ a :: L, ⨆ (_ : m < h c), A c ≤ ⨆ c ∈ L, ⨆ (_ : m < h c), A c := fun hm => by
      rw [iSup_mem_cons]
      exact sup_le (iSup_le fun hlt => absurd hlt (not_lt.2 hm)) le_rfl
    have hc' : ∀ b ∈ L, ∀ c ∈ L, b ≠ c → ∀ x ∈ A b, ∀ y ∈ A c,
        ⁅x, y⁆ ∈ ⨆ d ∈ L, ⨆ (_ : min (h b) (h c) < h d), A d := fun b hb c hc'' hbc x hx y hy =>
      hdrop (le_min (hah b hb) (hah c hc''))
        (hc b (List.mem_cons_of_mem a hb) c (List.mem_cons_of_mem a hc'') hbc x hx y hy)
    have hnorm : A a ≤ Subgroup.normalizer ((⨆ b ∈ L, A b : Subgroup G) : Set G) := by
      refine le_normalizer_of_map_conj_le fun x hx => ?_
      simp only [Subgroup.map_iSup]
      refine iSup₂_le fun b hb => map_conj_le_iff.2 fun y hy => ?_
      have hab : a ≠ b := fun hab => haL (hab ▸ hb)
      have hxy := hdrop (le_of_eq (min_eq_left (hah b hb)).symm)
        (hc a List.mem_cons_self b (List.mem_cons_of_mem a hb) hab x hx y hy)
      have hle : ⨆ c ∈ L, ⨆ (_ : min (h a) (h b) < h c), A c ≤ ⨆ c ∈ L, A c :=
        iSup₂_mono fun d _ => iSup_le fun _ => le_rfl
      have hy' : y ∈ ⨆ b ∈ L, A b := (le_iSup₂ (f := fun b (_ : b ∈ L) => A b) b hb) hy
      have := Subgroup.mul_mem _ (hle hxy) hy'
      rwa [commutatorElement_def, inv_mul_cancel_right] at this
    rw [iSup_mem_cons]
    exact (hA a List.mem_cons_self).to_sup_of_normal_right'
      (isPGroup_iSup_of_commutator_mem A h hnd hs hc' fun v hv =>
        hA v (List.mem_cons_of_mem a hv)) hnorm

end Collection

theorem isPGroup_of_isParametrization {ι : Type*} [Fintype ι] [DecidableEq ι]
    {Φ : RootSystem ι} {K : Type*} [Group K] {X : (ι → ℤ) → Subgroup K} {k : Type*} [Field k]
    {p : ℕ} [CharP k p] {x : (ι → ℤ) → k → K} (hx : IsParametrization (Φ := Φ) X x)
    {γ : ι → ℤ} (hγ : γ ∈ Φ.roots) : IsPGroup p (X γ) := by
  obtain ⟨hmem, hadd, -⟩ := hx γ hγ
  let f : Multiplicative k →* K :=
    MonoidHom.mk' (fun c => x γ c.toAdd) fun a b => hadd a.toAdd b.toAdd
  intro g
  obtain ⟨c, hc⟩ := (hmem g).1 g.2
  refine ⟨1, Subtype.ext ?_⟩
  have h : f (Multiplicative.ofAdd c) ^ p = 1 := by
    rw [← map_pow, ← ofAdd_nsmul, nsmul_eq_mul, CharP.cast_eq_zero, zero_mul, ofAdd_zero,
      map_one]
  rw [pow_one, Subgroup.coe_pow, ← hc]
  exact h

namespace RootSystem

variable {ι : Type*} [Fintype ι] [DecidableEq ι] (Φ : RootSystem ι)

theorem exists_abs_ht_le : ∃ M : ℤ, ∀ γ ∈ Φ.roots, |ht γ| ≤ M := by
  obtain ⟨M, hM⟩ := (Φ.finite_roots.image fun γ => |ht γ|).bddAbove
  exact ⟨M, fun γ hγ => hM ⟨γ, hγ, rfl⟩⟩

variable {Φ} {f : (ι → ℤ) →+ ℤ}

theorem linIndepPair_of_isIndiv {a b : ι → ℤ} (ha : a ∈ Φ.roots) (ha' : Φ.IsIndiv a)
    (hfa : 0 < f a) (hb : b ∈ Φ.roots) (hb' : Φ.IsIndiv b) (hfb : 0 < f b) (hab : a ≠ b) :
    LinIndepPair a b := by
  by_contra h
  rcases Φ.proportional a ha b hb h with h | h | h | h | h | h
  · exact hab h
  · rw [h, map_neg] at hfa
    omega
  · exact ha' b hb h
  · rw [h, map_neg, map_nsmul, nsmul_eq_mul] at hfa
    push_cast at hfa
    omega
  · exact hb' a ha h
  · rw [h, map_neg, map_nsmul, nsmul_eq_mul] at hfb
    push_cast at hfb
    omega

theorem min_lt_of_two_smul {M : ℤ} (hM : ∀ γ ∈ Φ.roots, |ht γ| ≤ M) {a b δ : ι → ℤ}
    (ha : a ∈ Φ.roots) (ha' : Φ.IsIndiv a) (hfa : 0 < f a) (hb : b ∈ Φ.roots)
    (hb' : Φ.IsIndiv b) (hfb : 0 < f b) (hab : a ≠ b) (hδ : δ ∈ Φ.roots) {m n : ℕ}
    (hm : 0 < m) (hn : 0 < n) (h : m • a + n • b = 2 • δ) :
    min ((2 * M + 1) * f a + ht a) ((2 * M + 1) * f b + ht b) <
      (2 * M + 1) * f δ + ht δ := by
  have hf : (m : ℤ) * f a + n * f b = 2 * f δ := by
    have := congrArg f h
    rw [map_add, map_nsmul, map_nsmul, map_nsmul, nsmul_eq_mul, nsmul_eq_mul,
      nsmul_eq_mul] at this
    push_cast at this
    exact this
  have hht : (m : ℤ) * ht a + n * ht b = 2 * ht δ := by
    rw [← ht_nsmul, ← ht_nsmul, ← ht_add, h, ht_two_smul]
  obtain ⟨ha1, ha2⟩ := abs_le.1 (hM a ha)
  obtain ⟨hb1, hb2⟩ := abs_le.1 (hM b hb)
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM a ha)
  have hga : 0 < (2 * M + 1) * f a + ht a := by nlinarith
  have hgb : 0 < (2 * M + 1) * f b + ht b := by nlinarith
  by_contra hle
  rw [not_lt, le_min_iff] at hle
  obtain ⟨h1, h2⟩ := hle
  have hm1 : (1 : ℤ) ≤ m := by exact_mod_cast hm
  have hn1 : (1 : ℤ) ≤ n := by exact_mod_cast hn
  have hg : (m : ℤ) * ((2 * M + 1) * f a + ht a) + n * ((2 * M + 1) * f b + ht b) =
      2 * ((2 * M + 1) * f δ + ht δ) := by
    linear_combination (2 * M + 1) * hf + hht
  have p1 : 0 ≤ ((m : ℤ) - 1) * ((2 * M + 1) * f a + ht a) := mul_nonneg (by linarith) hga.le
  have p2 : 0 ≤ ((n : ℤ) - 1) * ((2 * M + 1) * f b + ht b) := mul_nonneg (by linarith) hgb.le
  have e1 : ((m : ℤ) - 1) * ((2 * M + 1) * f a + ht a) = 0 := le_antisymm (by linarith) p1
  have e2 : ((n : ℤ) - 1) * ((2 * M + 1) * f b + ht b) = 0 := le_antisymm (by linarith) p2
  have hm' : m = 1 := by
    rcases mul_eq_zero.1 e1 with e | e
    · omega
    · omega
  have hn' : n = 1 := by
    rcases mul_eq_zero.1 e2 with e | e
    · omega
    · omega
  subst hm' hn'
  have hgab : (2 * M + 1) * f a + ht a = (2 * M + 1) * f b + ht b := by
    push_cast at hg
    linarith
  have hfab : f a = f b := by
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hlt
    · have : (2 * M + 1) * (f a + 1) ≤ (2 * M + 1) * f b :=
        mul_le_mul_of_nonneg_left (by omega) (by omega)
      linarith
    · have : (2 * M + 1) * (f b + 1) ≤ (2 * M + 1) * f a :=
        mul_le_mul_of_nonneg_left (by omega) (by omega)
      linarith
  have hab' : ht a = ht b := by
    rw [hfab] at hgab
    linarith
  rw [one_nsmul, one_nsmul] at h
  rcases Φ.mem_pos_or_mem_neg ha with hpos | hneg
  · exact Φ.sum_ne_two_smul a ha b hb δ hδ hpos.2 hab' hab ha' hb' h
  · refine Φ.sum_ne_two_smul (-a) (Φ.neg_mem a ha) (-b) (Φ.neg_mem b hb) (-δ) (Φ.neg_mem δ hδ)
      ?_ (by rw [ht_neg, ht_neg, hab']) (neg_injective.ne hab) (Φ.isIndiv_neg.2 ha')
      (Φ.isIndiv_neg.2 hb') (by rw [← neg_add, h, smul_neg])
    rw [ht_neg]
    linarith [hneg.2]

theorem exists_of_mem_openCone_posSet {M : ℤ} (hM : ∀ γ ∈ Φ.roots, |ht γ| ≤ M)
    {a b ε : ι → ℤ} (ha : a ∈ Φ.roots) (ha' : Φ.IsIndiv a) (hfa : 0 < f a) (hb : b ∈ Φ.roots)
    (hb' : Φ.IsIndiv b) (hfb : 0 < f b) (hab : a ≠ b) (hε : ε ∈ openCone Φ.roots a b) :
    ∃ c, (c ∈ posSet Φ.roots f ∧ Φ.IsIndiv c) ∧
      min ((2 * M + 1) * f a + ht a) ((2 * M + 1) * f b + ht b) <
        (2 * M + 1) * f c + ht c ∧ (c = ε ∨ ε = 2 • c) := by
  obtain ⟨hεr, m, n, hm, hn, rfl⟩ := hε
  have hm1 : (1 : ℤ) ≤ m := by exact_mod_cast hm
  have hn1 : (1 : ℤ) ≤ n := by exact_mod_cast hn
  have hfε : f (m • a + n • b) = m * f a + n * f b := by
    rw [map_add, map_nsmul, map_nsmul, nsmul_eq_mul, nsmul_eq_mul]
  have hfε0 : 0 < f (m • a + n • b) := by
    rw [hfε]
    nlinarith
  by_cases hind : Φ.IsIndiv (m • a + n • b)
  · refine ⟨_, ⟨⟨hεr, hfε0⟩, hind⟩, ?_, Or.inl rfl⟩
    obtain ⟨ha1, ha2⟩ := abs_le.1 (hM a ha)
    obtain ⟨hb1, hb2⟩ := abs_le.1 (hM b hb)
    have hga : 0 < (2 * M + 1) * f a + ht a := by nlinarith
    have hgb : 0 < (2 * M + 1) * f b + ht b := by nlinarith
    have hge : (2 * M + 1) * f a + ht a + ((2 * M + 1) * f b + ht b) ≤
        (2 * M + 1) * f (m • a + n • b) + ht (m • a + n • b) := by
      rw [hfε, ht_add, ht_nsmul, ht_nsmul]
      nlinarith
    exact lt_of_lt_of_le (lt_of_le_of_lt (min_le_left _ _) (by linarith)) hge
  · obtain ⟨δ, hδ, hδ', hεδ⟩ := Φ.exists_eq_two_smul hεr hind
    have hfδ : 0 < f δ := by
      have h2 := congrArg f hεδ
      rw [hfε, map_nsmul, nsmul_eq_mul] at h2
      push_cast at h2
      linarith
    exact ⟨δ, ⟨⟨hδ, hfδ⟩, hδ'⟩,
      min_lt_of_two_smul hM ha ha' hfa hb hb' hfb hab hδ hm hn hεδ, Or.inr hεδ⟩

variable (Φ)

theorem isPGroup_iSup_posSet {K : Type*} [Group K] {X : (ι → ℤ) → Subgroup K} {p : ℕ}
    (h2 : ∀ γ ∈ Φ.roots, 2 • γ ∈ Φ.roots → X (2 • γ) ≤ X γ)
    (hcomm : ∀ γ ∈ Φ.roots, ∀ δ ∈ Φ.roots, LinIndepPair γ δ → ∀ x ∈ X γ, ∀ y ∈ X δ,
      ⁅x, y⁆ ∈ ⨆ ε ∈ openCone Φ.roots γ δ, X ε)
    (hX : ∀ γ ∈ Φ.roots, IsPGroup p (X γ)) (f : (ι → ℤ) →+ ℤ) :
    IsPGroup p ↥(⨆ γ ∈ posSet Φ.roots f, X γ) := by
  obtain ⟨M, hM⟩ := Φ.exists_abs_ht_le
  obtain ⟨L, hnd, hmem, hs⟩ := exists_sorted_list
    (Φ.finite_roots.subset fun γ (hγ : γ ∈ posSet Φ.roots f ∧ Φ.IsIndiv γ) => hγ.1.1)
    (fun γ => (2 * M + 1) * f γ + ht γ)
  have hL : ⨆ γ ∈ posSet Φ.roots f, X γ = ⨆ γ ∈ L, X γ := by
    refine le_antisymm (iSup₂_le fun γ hγ => ?_)
      (iSup₂_le fun γ hγ => le_iSup₂_of_le γ ((hmem γ).1 hγ).1 le_rfl)
    by_cases hi : Φ.IsIndiv γ
    · exact le_iSup₂_of_le γ ((hmem γ).2 ⟨hγ, hi⟩) le_rfl
    · obtain ⟨δ, hδ, hδ', rfl⟩ := Φ.exists_eq_two_smul hγ.1 hi
      have hfδ : 0 < f δ := by
        have h0 := hγ.2
        rw [map_nsmul, nsmul_eq_mul] at h0
        push_cast at h0
        linarith
      exact (h2 δ hδ hγ.1).trans (le_iSup₂_of_le δ ((hmem δ).2 ⟨⟨hδ, hfδ⟩, hδ'⟩) le_rfl)
  rw [hL]
  refine isPGroup_iSup_of_commutator_mem X (fun γ => (2 * M + 1) * f γ + ht γ) hnd hs ?_
    fun v hv => hX v ((hmem v).1 hv).1.1
  intro a ha b hb hab x hx y hy
  obtain ⟨⟨haR, hfa⟩, ha'⟩ := (hmem a).1 ha
  obtain ⟨⟨hbR, hfb⟩, hb'⟩ := (hmem b).1 hb
  have hle : ⨆ ε ∈ openCone Φ.roots a b, X ε ≤
      ⨆ c ∈ L, ⨆ (_ : min ((2 * M + 1) * f a + ht a) ((2 * M + 1) * f b + ht b) <
        (2 * M + 1) * f c + ht c), X c := by
    refine iSup₂_le fun ε hε => ?_
    obtain ⟨c, hc, hlt, hcε⟩ :=
      exists_of_mem_openCone_posSet hM haR ha' hfa hbR hb' hfb hab hε
    have hεc : X ε ≤ X c := by
      rcases hcε with rfl | rfl
      · exact le_rfl
      · exact h2 c hc.1.1 hε.1
    exact hεc.trans (le_iSup₂_of_le (f := fun c (_ : c ∈ L) =>
      ⨆ (_ : min ((2 * M + 1) * f a + ht a) ((2 * M + 1) * f b + ht b) <
        (2 * M + 1) * f c + ht c), X c) c ((hmem c).2 hc) (le_iSup_of_le hlt le_rfl))
  exact hle (hcomm a haR b hbR (linIndepPair_of_isIndiv haR ha' hfa hbR hb' hfb hab) x hx y hy)

theorem exists_addHom_pos_of_not_isNegMultiple {α β : ι → ℤ} (hα : α ∈ Φ.roots)
    (hβ : β ∈ Φ.roots) (h : ¬ IsNegMultiple α β) :
    ∃ f : (ι → ℤ) →+ ℤ, 0 < f α ∧ 0 < f β := by
  by_cases hli : LinIndepPair α β
  · exact exists_addHom_pos_pos hli
  rcases Φ.proportional α hα β hβ hli with e | e | e | e | e | e
  · obtain ⟨f, hf⟩ := Φ.exists_addHom_pos hα
    exact ⟨f, hf, e ▸ hf⟩
  · exact absurd ⟨-1, by norm_num, fun j => by rw [e]; simp⟩ h
  · obtain ⟨f, hf⟩ := Φ.exists_addHom_pos hβ
    refine ⟨f, ?_, hf⟩
    rw [e, map_nsmul, nsmul_eq_mul]
    push_cast
    linarith
  · refine absurd ⟨-1 / 2, by norm_num, fun j => ?_⟩ h
    rw [e, Pi.neg_apply, Pi.smul_apply, nsmul_eq_mul]
    push_cast
    ring
  · obtain ⟨f, hf⟩ := Φ.exists_addHom_pos hα
    refine ⟨f, hf, ?_⟩
    rw [e, map_nsmul, nsmul_eq_mul]
    push_cast
    linarith
  · refine absurd ⟨-2, by norm_num, fun j => ?_⟩ h
    rw [e, Pi.neg_apply, Pi.smul_apply, nsmul_eq_mul]
    push_cast
    ring

theorem isPGroup_iSup_cone {K : Type*} [Group K] {X : (ι → ℤ) → Subgroup K} {p : ℕ}
    (h2 : ∀ γ ∈ Φ.roots, 2 • γ ∈ Φ.roots → X (2 • γ) ≤ X γ)
    (hcomm : ∀ γ ∈ Φ.roots, ∀ δ ∈ Φ.roots, LinIndepPair γ δ → ∀ x ∈ X γ, ∀ y ∈ X δ,
      ⁅x, y⁆ ∈ ⨆ ε ∈ openCone Φ.roots γ δ, X ε)
    (hX : ∀ γ ∈ Φ.roots, IsPGroup p (X γ)) {α β : ι → ℤ} (hα : α ∈ Φ.roots)
    (hβ : β ∈ Φ.roots) (h : ¬ IsNegMultiple α β) :
    IsPGroup p ↥(⨆ γ ∈ cone Φ.roots α β, X γ) := by
  obtain ⟨f, hfα, hfβ⟩ := Φ.exists_addHom_pos_of_not_isNegMultiple hα hβ h
  refine (Φ.isPGroup_iSup_posSet h2 hcomm hX f).to_le
    (iSup₂_mono' fun γ hγ => ⟨γ, ?_, le_rfl⟩)
  obtain ⟨hγR, a, b, rfl⟩ := hγ
  refine ⟨hγR, pos_apply_nsmul_add_nsmul hfα hfβ (Nat.pos_of_ne_zero fun h0 => ?_)⟩
  obtain ⟨rfl, rfl⟩ := Nat.add_eq_zero_iff.1 h0
  exact Φ.zero_notMem (by simpa using hγR)

end RootSystem

section RootDatum

variable {K : Type*} [Group K] {D : UniversalRootDatum K} {n : Fin D.rank → K}
  {H : Fin D.rank → Subgroup K} {p : ℕ}

theorem isPGroup_iSup_posSet (hext : SteinbergExtras D n H)
    (hX : ∀ γ ∈ D.roots, IsPGroup p (D.rootGroup γ)) (f : (Fin D.rank → ℤ) →+ ℤ) :
    IsPGroup p ↥(⨆ γ ∈ posSet D.roots f, D.rootGroup γ) :=
  (RootSystem.ofCartan D.isFiniteType D.divisible).isPGroup_iSup_posSet hext.two_smul_le
    hext.commutator_mem hX f

theorem isPGroup_iSup_pos (hext : SteinbergExtras D n H)
    (hX : ∀ γ ∈ D.roots, IsPGroup p (D.rootGroup γ)) :
    IsPGroup p ↥(⨆ γ ∈ {γ | γ ∈ D.roots ∧ 0 < ht γ}, D.rootGroup γ) :=
  isPGroup_iSup_posSet hext hX htHom

theorem isPGroup_iSup_cone (hext : SteinbergExtras D n H)
    (hX : ∀ γ ∈ D.roots, IsPGroup p (D.rootGroup γ)) {α β : Fin D.rank → ℤ}
    (hα : α ∈ D.roots) (hβ : β ∈ D.roots) (h : ¬ IsNegMultiple α β) :
    IsPGroup p ↥(⨆ γ ∈ cone D.roots α β, D.rootGroup γ) :=
  (RootSystem.ofCartan D.isFiniteType D.divisible).isPGroup_iSup_cone hext.two_smul_le
    hext.commutator_mem hX hα hβ h

end RootDatum

end CFSG.LieType.Steinberg
