module

public import CFSG.CGT.Foote82.Setup
public import CFSG.CGT.Foote82.T66.Perm310
import CFSG.Quasithin.Background.C58G64DirectLin
import CFSG.LocalAnalysis.AGLEmbedding.AltBetaGen

public section

namespace CFSG.CGT.Foote82

open CFSG.Open CFSG.Quasithin.G11 CFSG.RankThree.PartTwo

section Lin

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]

private theorem commSpace_zpowers_conj (g x : GLV V) :
    commSpace (Subgroup.zpowers (g * x * g⁻¹)) ⊤ =
      conjSub g (commSpace (Subgroup.zpowers x) ⊤) := by
  rw [CFSG.Quasithin.C58.G64D.commSpace_zpowers_eq_range,
    CFSG.Quasithin.C58.G64D.commSpace_zpowers_eq_range,
    CFSG.Quasithin.C58.G64D.datum_range_dl_conj]

private theorem apply_eq_of_mem_commSpace {a : GLV V} (ha : a * a = 1) {w : V}
    (hw : w ∈ commSpace (Subgroup.zpowers a) ⊤) : a w = w := by
  rw [commSpace_zpowers_top] at hw
  obtain ⟨u, rfl⟩ := hw
  have h1 : a (a u) = u := by
    have := congrArg (fun f : GLV V => f u) ha
    simpa using this
  simp only [LinearMap.sub_apply, LinearMap.id_apply, LinearEquiv.coe_coe, map_sub, h1]
  rw [← neg_sub, CFSG.Quasithin.C58.G64D.datum_neg_eq]

private theorem eq_of_finrank_eq_one {U : Submodule (ZMod 2) V}
    (hU : Module.finrank (ZMod 2) U = 1) {w w' : V} (hw : w ∈ U) (hw' : w' ∈ U) (h0 : w ≠ 0)
    (h0' : w' ≠ 0) : w = w' := by
  obtain ⟨v, -, hv⟩ := finrank_eq_one_iff'.1 hU
  obtain ⟨c, hc⟩ := hv ⟨w, hw⟩
  obtain ⟨c', hc'⟩ := hv ⟨w', hw'⟩
  rcases zmod2_eq_zero_or_one c with rfl | rfl
  · exact absurd (congrArg Subtype.val hc).symm (by simpa using h0)
  rcases zmod2_eq_zero_or_one c' with rfl | rfl
  · exact absurd (congrArg Subtype.val hc').symm (by simpa using h0')
  exact (congrArg Subtype.val hc).symm.trans (congrArg Subtype.val hc')

end Lin

section Perm

open Equiv

private theorem alternatingGroup_le_of_altOn {N : ℕ} (hN : 5 ≤ N) {i j k : Fin N} (hij : i ≠ j)
    (hik : i ≠ k) (hjk : j ≠ k) {H : Subgroup (Perm (Fin N))}
    (hL : altOn {x | x ≠ i ∧ x ≠ j} ≤ H) (hc : swap i j * swap j k ∈ H) :
    alternatingGroup (Fin N) ≤ H := by
  have h3 : ∀ τ : Perm (Fin N), τ.IsThreeCycle → τ i = i → τ j = j → τ ∈ H := by
    intro τ hτ hτi hτj
    apply hL
    refine Subgroup.mem_inf.2 ⟨hτ.mem_alternatingGroup, ?_⟩
    rw [mem_fixingSubgroup_iff]
    intro y hy
    simp only [Set.mem_compl_iff, Set.mem_setOf_eq, not_and_or, not_not] at hy
    rcases hy with rfl | rfl
    · exact hτi
    · exact hτj
  have hex : ∀ s : Finset (Fin N), s.card < N → ∃ m, m ∉ s := by
    intro s hs
    by_contra h
    simp only [not_exists, not_not] at h
    have := Finset.card_le_card (fun x _ => h x : (Finset.univ : Finset (Fin N)) ⊆ s)
    rw [Finset.card_univ, Fintype.card_fin] at this
    omega
  obtain ⟨m, hm⟩ := hex {i, j, k} (lt_of_le_of_lt Finset.card_le_three (by omega))
  obtain ⟨n, hn⟩ := hex {i, j, k, m} (lt_of_le_of_lt Finset.card_le_four (by omega))
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hm hn
  obtain ⟨hmi, hmj, hmk⟩ := hm
  obtain ⟨hni, hnj, hnk, hnm⟩ := hn
  set c := swap i j * swap j k with hcdef
  set ℓ := swap k m * swap m n with hℓdef
  have hℓj : ℓ j = j := by
    rw [hℓdef, Perm.mul_apply, swap_apply_of_ne_of_ne (Ne.symm hmj) (Ne.symm hnj),
      swap_apply_of_ne_of_ne hjk (Ne.symm hmj)]
  have hℓ : ℓ ∈ H := by
    refine h3 ℓ (CFSG.AGLEmbedding.isThreeCycle_swap_mul_swap (Ne.symm hmk) (Ne.symm hnk)
      (Ne.symm hnm)) ?_ hℓj
    rw [hℓdef, Perm.mul_apply, swap_apply_of_ne_of_ne (Ne.symm hmi) (Ne.symm hni),
      swap_apply_of_ne_of_ne hik (Ne.symm hmi)]
  set g := c * ℓ * c with hgdef
  have hg : g ∈ H := H.mul_mem (H.mul_mem hc hℓ) hc
  have hci : c i = j := by
    rw [hcdef, Perm.mul_apply, swap_apply_of_ne_of_ne hij hik, swap_apply_left]
  have hcj : c j = k := by
    rw [hcdef, Perm.mul_apply, swap_apply_left,
      swap_apply_of_ne_of_ne (Ne.symm hik) (Ne.symm hjk)]
  have hcm : c m = m := by
    rw [hcdef, Perm.mul_apply, swap_apply_of_ne_of_ne hmj hmk, swap_apply_of_ne_of_ne hmi hmj]
  have hℓk : ℓ k = m := by
    rw [hℓdef, Perm.mul_apply, swap_apply_of_ne_of_ne (Ne.symm hmk) (Ne.symm hnk),
      swap_apply_left]
  have hgi : g i = k := by
    rw [hgdef, Perm.mul_apply, Perm.mul_apply, hci, hℓj, hcj]
  have hgj : g j = m := by
    rw [hgdef, Perm.mul_apply, Perm.mul_apply, hcj, hℓk, hcm]
  refine CFSG.AGLEmbedding.alternatingGroup_le_of_disjoint (S₁ := {i, j}) (S₂ := {k, m})
    ?_ ?_ ?_ ?_ ?_ (x := n) ?_ ?_
  · intro τ hτ hd
    refine h3 τ hτ ?_ ?_
    · exact Perm.notMem_support.1 (Finset.disjoint_right.1 hd (by simp))
    · exact Perm.notMem_support.1 (Finset.disjoint_right.1 hd (by simp))
  · intro τ hτ hd
    have hτk : τ k = k := Perm.notMem_support.1 (Finset.disjoint_right.1 hd (by simp))
    have hτm : τ m = m := Perm.notMem_support.1 (Finset.disjoint_right.1 hd (by simp))
    have h3' : (g⁻¹ * τ * g).IsThreeCycle := by
      have e := Perm.cycleType_conj (σ := τ) (τ := g⁻¹)
      rw [inv_inv] at e
      unfold Perm.IsThreeCycle
      rw [e]
      exact hτ
    have hmem : g⁻¹ * τ * g ∈ H := by
      refine h3 _ h3' ?_ ?_
      · rw [Perm.mul_apply, Perm.mul_apply, hgi, hτk, Perm.inv_eq_iff_eq]
        exact hgi.symm
      · rw [Perm.mul_apply, Perm.mul_apply, hgj, hτm, Perm.inv_eq_iff_eq]
        exact hgj.symm
    have e : τ = g * (g⁻¹ * τ * g) * g⁻¹ := by group
    rw [e]
    exact H.mul_mem (H.mul_mem hg hmem) (H.inv_mem hg)
  · simp [Finset.disjoint_left, hik, Ne.symm hmi, hjk, Ne.symm hmj]
  · rw [Finset.card_pair hij]; omega
  · rw [Finset.card_pair (Ne.symm hmk)]; omega
  · simp [hni, hnj]
  · simp [hnk, hnm]

end Perm

section Module

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [Finite V] {G : Subgroup (GLV V)}
  {N : ℕ}

private noncomputable def tG (φ : ↥G ≃* Equiv.Perm (Fin N)) : Equiv.Perm (Fin N) →* GLV V :=
  G.subtype.comp φ.symm.toMonoidHom

private theorem tG_apply (φ : ↥G ≃* Equiv.Perm (Fin N)) (σ : Equiv.Perm (Fin N)) :
    tG φ σ = ((φ.symm σ : ↥G) : GLV V) := rfl

private theorem tG_injective (φ : ↥G ≃* Equiv.Perm (Fin N)) : Function.Injective (tG φ) :=
  Subtype.val_injective.comp φ.symm.injective

private theorem tG_apply_self (φ : ↥G ≃* Equiv.Perm (Fin N)) (g : ↥G) :
    tG φ (φ g) = (g : GLV V) := by
  rw [tG_apply, MulEquiv.symm_apply_apply]

private theorem finrank_commSpace_eq_of_isConj (φ : ↥G ≃* Equiv.Perm (Fin N))
    {σ τ : Equiv.Perm (Fin N)} (h : IsConj σ τ) :
    Module.finrank (ZMod 2) ↥(commSpace (Subgroup.zpowers (tG φ τ)) ⊤) =
      Module.finrank (ZMod 2) ↥(commSpace (Subgroup.zpowers (tG φ σ)) ⊤) := by
  obtain ⟨π, rfl⟩ := isConj_iff.1 h
  rw [map_mul, map_mul, map_inv, commSpace_zpowers_conj, finrank_conjSub]

private theorem eq_zero_of_forall_alt (φ : ↥G ≃* Equiv.Perm (Fin N)) (hirr : IsIrr G ⊤)
    {c : Equiv.Perm (Fin N)} (hc : c.IsThreeCycle) {v : V}
    (hv : ∀ g : ↥G, φ g ∈ alternatingGroup (Fin N) → (g : GLV V) v = v) : v = 0 := by
  let F : Submodule (ZMod 2) V :=
    { carrier := {v | ∀ g : ↥G, φ g ∈ alternatingGroup (Fin N) → (g : GLV V) v = v}
      add_mem' := fun {a b} ha hb g hg => by rw [map_add, ha g hg, hb g hg]
      zero_mem' := fun g _ => map_zero _
      smul_mem' := fun c v hv g hg => by rw [map_smul, hv g hg] }
  have hinv : Invariant G F := by
    intro h hh w hw g hg
    have hconj : φ (⟨h, hh⟩⁻¹ * g * ⟨h, hh⟩) ∈ alternatingGroup (Fin N) := by
      rw [map_mul, map_mul, map_inv]
      have := (inferInstance : (alternatingGroup (Fin N)).Normal).conj_mem _ hg (φ ⟨h, hh⟩)⁻¹
      simpa using this
    have e : (g : GLV V) (h w) = h (((⟨h, hh⟩⁻¹ * g * ⟨h, hh⟩ : ↥G) : GLV V) w) := by
      simp [mul_assoc]
    rw [e, hw _ hconj]
  rcases hirr.eq_bot_or_eq hinv le_top with h | h
  · have hvF : v ∈ F := hv
    rw [h] at hvF
    exact (Submodule.mem_bot _).1 hvF
  · exfalso
    have hg : ∀ w : V, tG φ c w = w := fun w => by
      have hw : w ∈ F := h ▸ Submodule.mem_top
      exact hw (φ.symm c) (by simpa using hc.mem_alternatingGroup)
    have h1 : tG φ c = 1 := LinearEquiv.ext hg
    exact hc.ne_one (tG_injective φ (h1.trans (map_one _).symm))

private theorem finrank_commSpace_swap_eq_one (hN : 7 ≤ N) (φ : ↥G ≃* Equiv.Perm (Fin N))
    (hirr : IsIrr G ⊤) {i j : Fin N} (hij : i ≠ j)
    (hα : ∀ g : ↥G, φ g ∈ altOn {k | k ≠ i ∧ k ≠ j} →
      ∀ w ∈ commSpace (Subgroup.zpowers (tG φ (Equiv.swap i j))) ⊤, (g : GLV V) w = w)
    (h3 : ∀ σ : Equiv.Perm (Fin N), σ.IsThreeCycle →
      Module.finrank (ZMod 2) ↥(commSpace (Subgroup.zpowers (tG φ σ)) ⊤) = 2) :
    Module.finrank (ZMod 2) ↥(commSpace (Subgroup.zpowers (tG φ (Equiv.swap i j))) ⊤) = 1 := by
  haveI : Module.Finite (ZMod 2) V := Module.Finite.of_finite
  obtain ⟨k, hki, hkj⟩ : ∃ k : Fin N, k ≠ i ∧ k ≠ j := by
    by_contra h
    simp only [not_exists, not_and, not_not] at h
    have hsub : (Finset.univ : Finset (Fin N)) ⊆ {i, j} := fun x _ => by
      by_cases hx : x = i
      · simp [hx]
      · simp [h x hx]
    have := Finset.card_le_card hsub
    rw [Finset.card_univ, Fintype.card_fin] at this
    have := this.trans Finset.card_le_two
    omega
  have hc3 : (Equiv.swap i j * Equiv.swap j k).IsThreeCycle :=
    CFSG.AGLEmbedding.isThreeCycle_swap_mul_swap hij (Ne.symm hki) (Ne.symm hkj)
  set a := tG φ (Equiv.swap i j) with ha
  set c := tG φ (Equiv.swap i j * Equiv.swap j k) with hcdef
  have haa : a * a = 1 := by rw [ha, ← map_mul, Equiv.swap_mul_self, map_one]
  have hca' : Equiv.swap i j * Equiv.swap j k * Equiv.swap i j =
      Equiv.swap i j * (Equiv.swap i j * Equiv.swap j k)⁻¹ := by
    rw [mul_inv_rev, Equiv.swap_inv, Equiv.swap_inv, mul_assoc]
  have hac' : Equiv.swap i j * (Equiv.swap i j * Equiv.swap j k) =
      (Equiv.swap i j * Equiv.swap j k)⁻¹ * Equiv.swap i j := by
    rw [mul_inv_rev, Equiv.swap_inv, Equiv.swap_inv, ← mul_assoc, Equiv.swap_mul_self, one_mul,
      mul_assoc, Equiv.swap_mul_self, mul_one]
  have hca : c * a = a * c⁻¹ := by
    rw [hcdef, ha, ← map_mul, ← map_inv, ← map_mul, hca']
  have hac : a * c = c⁻¹ * a := by
    rw [hcdef, ha, ← map_mul, ← map_inv, ← map_mul, hac']
  have hc3' : c ^ 3 = 1 := by
    rw [hcdef, ← map_pow, ← hc3.orderOf, pow_orderOf_eq_one, map_one]
  have hcompl := CFSG.Quasithin.C58.G64D.isCompl_range_ker_dl hc3'
  have hW : Module.finrank (ZMod 2) ↥(commSpace (Subgroup.zpowers c) ⊤) = 2 := h3 _ hc3
  have hA : ∀ u : V, c u = u → a u = u := by
    intro u hu
    have hcu : c⁻¹ u = u := by
      conv_lhs => rw [← hu]
      simp
    have hx1 : c (a u - u) = a u - u := by
      have e1 : c (a u) = a (c⁻¹ u) := by
        have := congrArg (fun f : GLV V => f u) hca
        simpa using this
      rw [map_sub, e1, hcu, hu]
    have hx2 : a u - u ∈ commSpace (Subgroup.zpowers a) ⊤ :=
      sub_mem_commSpace (Subgroup.mem_zpowers a) Submodule.mem_top
    have hle : alternatingGroup (Fin N) ≤
        (MulAction.stabilizer (GLV V) (a u - u)).comap (tG φ) := by
      refine alternatingGroup_le_of_altOn (by omega) hij (Ne.symm hki) (Ne.symm hkj) ?_ ?_
      · intro σ hσ
        show tG φ σ • (a u - u) = a u - u
        exact hα (φ.symm σ) (by simpa using hσ) _ hx2
      · show c • (a u - u) = a u - u
        exact hx1
    have hx0 : a u - u = 0 := by
      refine eq_zero_of_forall_alt φ hirr hc3 fun g hg => ?_
      have h1 : tG φ (φ g) • (a u - u) = a u - u := hle hg
      rw [tG_apply_self] at h1
      exact h1
    exact sub_eq_zero.1 hx0
  have hB : ∀ w ∈ commSpace (Subgroup.zpowers c) ⊤, a w ∈ commSpace (Subgroup.zpowers c) ⊤ := by
    intro w hw
    rw [commSpace_zpowers_top] at hw
    obtain ⟨v, rfl⟩ := hw
    have e : a (((c : V →ₗ[ZMod 2] V) - LinearMap.id : V →ₗ[ZMod 2] V) v) =
        c⁻¹ (a v) - a v := by
      have := congrArg (fun f : GLV V => f v) hac
      simp only [LinearEquiv.mul_apply] at this
      simp [this]
    rw [e]
    exact sub_mem_commSpace (Subgroup.inv_mem _ (Subgroup.mem_zpowers c)) Submodule.mem_top
  have hdec : ∀ u : V, ∃ y z, c y = y ∧ z ∈ commSpace (Subgroup.zpowers c) ⊤ ∧ u = y + z := by
    intro u
    have hu : u ∈ LinearMap.range (CFSG.Quasithin.C58.G64D.dl c) ⊔
        LinearMap.ker (CFSG.Quasithin.C58.G64D.dl c) := by
      rw [hcompl.sup_eq_top]; trivial
    obtain ⟨z, hz, y, hy, rfl⟩ := Submodule.mem_sup.1 hu
    refine ⟨y, z, ?_, ?_, add_comm z y⟩
    · exact sub_eq_zero.1 (LinearMap.mem_ker.1 hy)
    · rw [commSpace_zpowers_top]
      exact hz
  have hle : commSpace (Subgroup.zpowers a) ⊤ ≤ commSpace (Subgroup.zpowers c) ⊤ := by
    rw [commSpace_zpowers_top a]
    rintro _ ⟨u, rfl⟩
    obtain ⟨y, z, hy, hz, rfl⟩ := hdec u
    have e : ((a : V →ₗ[ZMod 2] V) - LinearMap.id : V →ₗ[ZMod 2] V) (y + z) = a z - z := by
      simp only [LinearMap.sub_apply, LinearMap.id_apply, LinearEquiv.coe_coe, map_add, hA y hy]
      abel
    rw [e]
    exact Submodule.sub_mem _ (hB z hz) hz
  have ha1 : a ≠ 1 := fun h =>
    hij (Equiv.swap_eq_one_iff.1 (tG_injective φ (h.trans (map_one _).symm)))
  have hne : commSpace (Subgroup.zpowers a) ⊤ ≠ commSpace (Subgroup.zpowers c) ⊤ := by
    intro heq
    apply ha1
    ext u
    obtain ⟨y, z, hy, hz, rfl⟩ := hdec u
    have hz' : a z = z := apply_eq_of_mem_commSpace haa (heq ▸ hz)
    simp [map_add, hA y hy, hz']
  have hlt := Submodule.finrank_lt_finrank_of_lt (lt_of_le_of_ne hle hne)
  have hbot : commSpace (Subgroup.zpowers a) ⊤ ≠ ⊥ := by
    intro h
    apply ha1
    ext u
    have := (commSpace_eq_bot_iff.1 h) a (Subgroup.mem_zpowers a) u Submodule.mem_top
    simpa using this
  have h1 := Submodule.one_le_finrank_iff.2 hbot
  omega

open scoped Classical in
private noncomputable def vec (φ : ↥G ≃* Equiv.Perm (Fin N)) (k l : Fin N) : V :=
  if h : ∃ w ∈ commSpace (Subgroup.zpowers (tG φ (Equiv.swap k l))) ⊤, w ≠ 0 then h.choose
  else 0

private theorem vec_mem (φ : ↥G ≃* Equiv.Perm (Fin N)) (k l : Fin N) :
    vec φ k l ∈ commSpace (Subgroup.zpowers (tG φ (Equiv.swap k l))) ⊤ := by
  unfold vec
  split_ifs with h
  · exact h.choose_spec.1
  · exact Submodule.zero_mem _

private theorem vec_ne_zero (φ : ↥G ≃* Equiv.Perm (Fin N)) {k l : Fin N}
    (h1 : Module.finrank (ZMod 2)
      ↥(commSpace (Subgroup.zpowers (tG φ (Equiv.swap k l))) ⊤) = 1) :
    vec φ k l ≠ 0 := by
  have hex : ∃ w ∈ commSpace (Subgroup.zpowers (tG φ (Equiv.swap k l))) ⊤, w ≠ 0 := by
    obtain ⟨v, hv0, -⟩ := finrank_eq_one_iff'.1 h1
    exact ⟨v, v.2, fun h => hv0 (Subtype.ext h)⟩
  unfold vec
  rw [dif_pos hex]
  exact hex.choose_spec.2

private theorem eq_vec (φ : ↥G ≃* Equiv.Perm (Fin N)) {k l : Fin N}
    (h1 : Module.finrank (ZMod 2)
      ↥(commSpace (Subgroup.zpowers (tG φ (Equiv.swap k l))) ⊤) = 1)
    {w : V} (hw : w ∈ commSpace (Subgroup.zpowers (tG φ (Equiv.swap k l))) ⊤) (hw0 : w ≠ 0) :
    w = vec φ k l :=
  eq_of_finrank_eq_one h1 hw (vec_mem φ k l) hw0 (vec_ne_zero φ h1)

private theorem vec_self (φ : ↥G ≃* Equiv.Perm (Fin N)) (k : Fin N) : vec φ k k = 0 := by
  have h := vec_mem φ k k
  rw [Equiv.swap_self, ← Equiv.Perm.one_def, map_one, commSpace_zpowers_top] at h
  obtain ⟨u, hu⟩ := h
  rw [← hu]
  simp

private theorem vec_comm (φ : ↥G ≃* Equiv.Perm (Fin N)) (k l : Fin N) :
    vec φ k l = vec φ l k := by
  unfold vec
  rw [Equiv.swap_comm]

private theorem apply_vec {φ : ↥G ≃* Equiv.Perm (Fin N)}
    (h1 : ∀ k l : Fin N, k ≠ l →
      Module.finrank (ZMod 2) ↥(commSpace (Subgroup.zpowers (tG φ (Equiv.swap k l))) ⊤) = 1)
    (g : ↥G) (k l : Fin N) :
    (g : GLV V) (vec φ k l) = vec φ (φ g k) (φ g l) := by
  by_cases hkl : k = l
  · subst hkl
    rw [vec_self, vec_self, map_zero]
  have hkl' : φ g k ≠ φ g l := fun h => hkl ((φ g).injective h)
  refine eq_vec φ (h1 _ _ hkl') ?_ ?_
  · have e : tG φ (Equiv.swap (φ g k) (φ g l)) =
        (g : GLV V) * tG φ (Equiv.swap k l) * (g : GLV V)⁻¹ := by
      rw [Equiv.swap_apply_apply, map_mul, map_mul, map_inv, tG_apply_self]
    rw [e, commSpace_zpowers_conj]
    exact apply_mem_conjSub (vec_mem φ k l)
  · intro h0
    apply vec_ne_zero φ (h1 k l hkl)
    have := congrArg (g : GLV V).symm h0
    simpa using this

private theorem vec_add_of_ne {φ : ↥G ≃* Equiv.Perm (Fin N)}
    (h1 : ∀ k l : Fin N, k ≠ l →
      Module.finrank (ZMod 2) ↥(commSpace (Subgroup.zpowers (tG φ (Equiv.swap k l))) ⊤) = 1)
    (h3 : ∀ σ : Equiv.Perm (Fin N), σ.IsThreeCycle →
      Module.finrank (ZMod 2) ↥(commSpace (Subgroup.zpowers (tG φ σ)) ⊤) = 2)
    {k l n : Fin N} (hkl : k ≠ l) (hkn : k ≠ n) (hln : l ≠ n) :
    vec φ k n = vec φ k l + vec φ l n := by
  set x := tG φ (Equiv.swap k l) with hx
  set y := tG φ (Equiv.swap l n) with hy
  have hyv : y (vec φ k l) = vec φ k n := by
    have := apply_vec h1 (φ.symm (Equiv.swap l n)) k l
    rw [MulEquiv.apply_symm_apply, Equiv.swap_apply_of_ne_of_ne hkl hkn,
      Equiv.swap_apply_left] at this
    exact this
  have hmem : vec φ k n - vec φ k l ∈ commSpace (Subgroup.zpowers y) ⊤ := by
    rw [← hyv]
    exact sub_mem_commSpace (Subgroup.mem_zpowers y) Submodule.mem_top
  by_cases h0 : vec φ k n - vec φ k l = 0
  · exfalso
    have hkn' : vec φ k n = vec φ k l := sub_eq_zero.1 h0
    have hx1 : x (vec φ k n) = vec φ l n := by
      have := apply_vec h1 (φ.symm (Equiv.swap k l)) k n
      rw [MulEquiv.apply_symm_apply, Equiv.swap_apply_left,
        Equiv.swap_apply_of_ne_of_ne (Ne.symm hkn) (Ne.symm hln)] at this
      exact this
    have hx2 : x (vec φ k l) = vec φ k l := by
      have := apply_vec h1 (φ.symm (Equiv.swap k l)) k l
      rw [MulEquiv.apply_symm_apply, Equiv.swap_apply_left, Equiv.swap_apply_right,
        vec_comm φ l k] at this
      exact this
    have hln' : vec φ l n = vec φ k l := by rw [← hx1, hkn', hx2]
    have hw0 : vec φ k l ≠ 0 := vec_ne_zero φ (h1 k l hkl)
    have hDx : commSpace (Subgroup.zpowers x) ⊤ ≤ Submodule.span (ZMod 2) {vec φ k l} := by
      intro u hu
      by_cases hu0 : u = 0
      · rw [hu0]; exact Submodule.zero_mem _
      · rw [eq_vec φ (h1 k l hkl) hu hu0]; exact Submodule.mem_span_singleton_self _
    have hDy : commSpace (Subgroup.zpowers y) ⊤ ≤ Submodule.span (ZMod 2) {vec φ k l} := by
      intro u hu
      by_cases hu0 : u = 0
      · rw [hu0]; exact Submodule.zero_mem _
      · rw [eq_vec φ (h1 l n hln) hu hu0, hln']; exact Submodule.mem_span_singleton_self _
    have hxw : ∀ u ∈ Submodule.span (ZMod 2) {vec φ k l},
        x u ∈ Submodule.span (ZMod 2) {vec φ k l} := by
      intro u hu
      obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hu
      rw [map_smul, hx2]
      exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)
    have hDxy : commSpace (Subgroup.zpowers (x * y)) ⊤ ≤
        Submodule.span (ZMod 2) {vec φ k l} := by
      rw [commSpace_zpowers_top]
      rintro _ ⟨u, rfl⟩
      have e : (((x * y : GLV V) : V →ₗ[ZMod 2] V) - LinearMap.id : V →ₗ[ZMod 2] V) u =
          x (y u - u) + (x u - u) := by
        simp only [LinearMap.sub_apply, LinearMap.id_apply, LinearEquiv.coe_coe,
          LinearEquiv.mul_apply, map_sub]
        abel
      rw [e]
      exact Submodule.add_mem _
        (hxw _ (hDy (sub_mem_commSpace (Subgroup.mem_zpowers y) Submodule.mem_top)))
        (hDx (sub_mem_commSpace (Subgroup.mem_zpowers x) Submodule.mem_top))
    have h2 : Module.finrank (ZMod 2) ↥(commSpace (Subgroup.zpowers (x * y)) ⊤) = 2 := by
      have := h3 _ (CFSG.AGLEmbedding.isThreeCycle_swap_mul_swap hkl hkn hln)
      rwa [map_mul] at this
    have := Submodule.finrank_mono hDxy
    rw [h2, finrank_span_singleton hw0] at this
    omega
  · have := eq_vec φ (h1 l n hln) hmem h0
    rw [← this]
    abel

private theorem vec_add {φ : ↥G ≃* Equiv.Perm (Fin N)}
    (h1 : ∀ k l : Fin N, k ≠ l →
      Module.finrank (ZMod 2) ↥(commSpace (Subgroup.zpowers (tG φ (Equiv.swap k l))) ⊤) = 1)
    (h3 : ∀ σ : Equiv.Perm (Fin N), σ.IsThreeCycle →
      Module.finrank (ZMod 2) ↥(commSpace (Subgroup.zpowers (tG φ σ)) ⊤) = 2)
    (k l n : Fin N) : vec φ k n = vec φ k l + vec φ l n := by
  by_cases hkl : k = l
  · subst hkl; rw [vec_self, zero_add]
  by_cases hln : l = n
  · subst hln; rw [vec_self, add_zero]
  by_cases hkn : k = n
  · subst hkn; rw [vec_self, vec_comm φ l k, CFSG.Quasithin.C58.G64D.datum_add_self]
  exact vec_add_of_ne h1 h3 hkl hkn hln

private noncomputable def phiMap (φ : ↥G ≃* Equiv.Perm (Fin N)) (i : Fin N) :
    (Fin N → ZMod 2) →+ V where
  toFun x := ∑ m, x m • vec φ m i
  map_zero' := by simp
  map_add' x y := by simp [add_smul, Finset.sum_add_distrib]

private theorem phiMap_apply (φ : ↥G ≃* Equiv.Perm (Fin N)) (i : Fin N) (x : Fin N → ZMod 2) :
    phiMap φ i x = ∑ m, x m • vec φ m i := rfl

private theorem apply_phiMap {φ : ↥G ≃* Equiv.Perm (Fin N)}
    (h1 : ∀ k l : Fin N, k ≠ l →
      Module.finrank (ZMod 2) ↥(commSpace (Subgroup.zpowers (tG φ (Equiv.swap k l))) ⊤) = 1)
    (h3 : ∀ σ : Equiv.Perm (Fin N), σ.IsThreeCycle →
      Module.finrank (ZMod 2) ↥(commSpace (Subgroup.zpowers (tG φ σ)) ⊤) = 2)
    (i : Fin N) (g : ↥G) {x : Fin N → ZMod 2} (hx : ∑ m, x m = 0) :
    (g : GLV V) (phiMap φ i x) = phiMap φ i (fun m => x ((φ g)⁻¹ m)) := by
  rw [phiMap_apply, phiMap_apply, map_sum]
  simp_rw [map_smul, apply_vec h1 g]
  conv_rhs => rw [← Equiv.sum_comp (φ g)]
  simp only [Equiv.Perm.coe_inv, Equiv.symm_apply_apply]
  have e : ∀ m, vec φ (φ g m) (φ g i) = vec φ (φ g m) i + vec φ i (φ g i) :=
    fun m => vec_add h1 h3 _ i _
  simp_rw [e, smul_add]
  rw [Finset.sum_add_distrib, ← Finset.sum_smul, hx, zero_smul, add_zero]

private theorem phiMap_single_add_single {φ : ↥G ≃* Equiv.Perm (Fin N)}
    (h1 : ∀ k l : Fin N, k ≠ l →
      Module.finrank (ZMod 2) ↥(commSpace (Subgroup.zpowers (tG φ (Equiv.swap k l))) ⊤) = 1)
    (h3 : ∀ σ : Equiv.Perm (Fin N), σ.IsThreeCycle →
      Module.finrank (ZMod 2) ↥(commSpace (Subgroup.zpowers (tG φ σ)) ⊤) = 2)
    (i : Fin N) (k l : Fin N) :
    phiMap φ i (Pi.single k 1 + Pi.single l 1) = vec φ k l := by
  rw [map_add, phiMap_apply, phiMap_apply]
  simp only [Pi.single_apply, ite_smul, one_smul, zero_smul, Finset.sum_ite_eq',
    Finset.mem_univ, if_true]
  rw [vec_add h1 h3 k i l, vec_comm φ i l]

private theorem mem_zmultiples_of_phiMap_eq_zero {φ : ↥G ≃* Equiv.Perm (Fin N)}
    (h1 : ∀ k l : Fin N, k ≠ l →
      Module.finrank (ZMod 2) ↥(commSpace (Subgroup.zpowers (tG φ (Equiv.swap k l))) ⊤) = 1)
    (h3 : ∀ σ : Equiv.Perm (Fin N), σ.IsThreeCycle →
      Module.finrank (ZMod 2) ↥(commSpace (Subgroup.zpowers (tG φ σ)) ⊤) = 2)
    (i : Fin N) {x : Fin N → ZMod 2} (hx : ∑ m, x m = 0) (h0 : phiMap φ i x = 0) :
    x ∈ AddSubgroup.zmultiples (allOnes N) := by
  by_contra hxm
  obtain ⟨k, hk⟩ : ∃ k, x k = 1 := by
    by_contra h
    simp only [not_exists] at h
    apply hxm
    have : x = 0 := funext fun m => (zmod2_eq_zero_or_one (x m)).resolve_right (h m)
    rw [this]
    exact AddSubgroup.zero_mem _
  obtain ⟨l, hl⟩ : ∃ l, x l = 0 := by
    by_contra h
    simp only [not_exists] at h
    apply hxm
    have : x = allOnes N := funext fun m => (zmod2_eq_zero_or_one (x m)).resolve_left (h m)
    rw [this]
    exact AddSubgroup.mem_zmultiples _
  have hkl : k ≠ l := by
    rintro rfl
    rw [hk] at hl
    exact one_ne_zero hl
  have hsw : (fun m => x ((φ (φ.symm (Equiv.swap k l)))⁻¹ m)) - x =
      Pi.single k 1 + Pi.single l 1 := by
    rw [MulEquiv.apply_symm_apply, Equiv.swap_inv]
    funext m
    by_cases hmk : m = k
    · subst hmk
      simp [Pi.single_apply, hkl, hk, hl]
    by_cases hml : m = l
    · subst hml
      simp [Pi.single_apply, hk, hl, Ne.symm hkl]
    · simp [Pi.single_apply, hmk, hml, Equiv.swap_apply_of_ne_of_ne hmk hml]
  have hg := apply_phiMap h1 h3 i (φ.symm (Equiv.swap k l)) hx
  rw [h0, map_zero] at hg
  have h2 : phiMap φ i (Pi.single k 1 + Pi.single l 1) = 0 := by
    rw [← hsw, map_sub, ← hg, h0, sub_zero]
  rw [phiMap_single_add_single h1 h3 i k l] at h2
  exact vec_ne_zero φ (h1 k l hkl) h2

private theorem phiMap_eq_zero_of_mem_zmultiples {φ : ↥G ≃* Equiv.Perm (Fin N)}
    (hirr : IsIrr G ⊤) {c : Equiv.Perm (Fin N)} (hc : c.IsThreeCycle)
    (h1 : ∀ k l : Fin N, k ≠ l →
      Module.finrank (ZMod 2) ↥(commSpace (Subgroup.zpowers (tG φ (Equiv.swap k l))) ⊤) = 1)
    (h3 : ∀ σ : Equiv.Perm (Fin N), σ.IsThreeCycle →
      Module.finrank (ZMod 2) ↥(commSpace (Subgroup.zpowers (tG φ σ)) ⊤) = 2)
    (i : Fin N) {x : Fin N → ZMod 2} (hx : ∑ m, x m = 0)
    (hxm : x ∈ AddSubgroup.zmultiples (allOnes N)) : phiMap φ i x = 0 := by
  obtain ⟨n, rfl⟩ := AddSubgroup.mem_zmultiples_iff.1 hxm
  refine eq_zero_of_forall_alt φ hirr hc fun g _ => ?_
  rw [apply_phiMap h1 h3 i g hx]
  rfl

private theorem exists_phiMap_eq {φ : ↥G ≃* Equiv.Perm (Fin N)} (hirr : IsIrr G ⊤)
    (h1 : ∀ k l : Fin N, k ≠ l →
      Module.finrank (ZMod 2) ↥(commSpace (Subgroup.zpowers (tG φ (Equiv.swap k l))) ⊤) = 1)
    (h3 : ∀ σ : Equiv.Perm (Fin N), σ.IsThreeCycle →
      Module.finrank (ZMod 2) ↥(commSpace (Subgroup.zpowers (tG φ σ)) ⊤) = 2)
    {i j : Fin N} (hij : i ≠ j) (v : V) :
    ∃ x : Fin N → ZMod 2, ∑ m, x m = 0 ∧ phiMap φ i x = v := by
  let U : Submodule (ZMod 2) V :=
    Submodule.span (ZMod 2) (Set.range fun p : Fin N × Fin N => vec φ p.1 p.2)
  have hU : Invariant G U := by
    intro g hg u hu
    have hle : U ≤ U.comap (g : V →ₗ[ZMod 2] V) := by
      rw [Submodule.span_le]
      rintro _ ⟨⟨k, l⟩, rfl⟩
      show g (vec φ k l) ∈ U
      have e := apply_vec h1 ⟨g, hg⟩ k l
      rw [show g (vec φ k l) = ((⟨g, hg⟩ : ↥G) : GLV V) (vec φ k l) from rfl, e]
      exact Submodule.subset_span ⟨(_, _), rfl⟩
    exact hle hu
  have hUtop : U = ⊤ := by
    rcases hirr.eq_bot_or_eq hU le_top with h | h
    · exfalso
      have hmem : vec φ i j ∈ U := Submodule.subset_span ⟨(i, j), rfl⟩
      rw [h] at hmem
      exact vec_ne_zero φ (h1 i j hij) ((Submodule.mem_bot _).1 hmem)
    · exact h
  have hv : v ∈ U := hUtop ▸ Submodule.mem_top
  induction hv using Submodule.span_induction with
  | mem w hw =>
    obtain ⟨⟨k, l⟩, rfl⟩ := hw
    refine ⟨Pi.single k 1 + Pi.single l 1, ?_, phiMap_single_add_single h1 h3 i k l⟩
    simp only [Pi.add_apply, Finset.sum_add_distrib, Finset.sum_pi_single', Finset.mem_univ,
      if_true]
    decide
  | zero => exact ⟨0, by simp, map_zero _⟩
  | add u w _ _ hu hw =>
    obtain ⟨x, hx, rfl⟩ := hu
    obtain ⟨y, hy, rfl⟩ := hw
    exact ⟨x + y, by simp [Finset.sum_add_distrib, hx, hy], map_add _ _ _⟩
  | smul c u _ hu =>
    obtain ⟨x, hx, rfl⟩ := hu
    rcases zmod2_eq_zero_or_one c with rfl | rfl
    · exact ⟨0, by simp, by rw [map_zero, zero_smul]⟩
    · exact ⟨x, hx, by rw [one_smul]⟩

end Module

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]

theorem isAltHeartFor_of_perm {G : Subgroup (GLV V)} {N : ℕ} (hN : 7 ≤ N)
    (φ : ↥G ≃* Equiv.Perm (Fin N)) (hirr : IsIrr G ⊤) {i j : Fin N} (hij : i ≠ j)
    (hα : ∀ g : ↥G, φ g ∈ altOn {k | k ≠ i ∧ k ≠ j} →
      ∀ w ∈ commSpace (Subgroup.zpowers ((φ.symm (Equiv.swap i j) : ↥G) : GLV V)) ⊤,
        (g : GLV V) w = w)
    {c : Equiv.Perm (Fin N)} (hc : c.IsThreeCycle) (hci : c i = i) (hcj : c j = j)
    (hβ : Module.finrank (ZMod 2)
      ↥(commSpace (Subgroup.zpowers ((φ.symm c : ↥G) : GLV V)) ⊤) = 2) :
    IsAltHeartFor (((alternatingGroup (Fin N)).comap φ.toMonoidHom).map G.subtype) N ∧
      ∀ k l : Fin N, k ≠ l → Module.finrank (ZMod 2)
        ↥(commSpace (Subgroup.zpowers ((φ.symm (Equiv.swap k l) : ↥G) : GLV V)) ⊤) = 1 := by
  haveI : Module.Finite (ZMod 2) V := Module.Finite.of_finite
  have h3 : ∀ σ : Equiv.Perm (Fin N), σ.IsThreeCycle →
      Module.finrank (ZMod 2) ↥(commSpace (Subgroup.zpowers (tG φ σ)) ⊤) = 2 := by
    intro σ hσ
    rw [finrank_commSpace_eq_of_isConj φ
      (Equiv.Perm.isConj_iff_cycleType_eq.2 (hc.trans hσ.symm))]
    exact hβ
  have hij1 := finrank_commSpace_swap_eq_one hN φ hirr hij hα h3
  have h1 : ∀ k l : Fin N, k ≠ l →
      Module.finrank (ZMod 2) ↥(commSpace (Subgroup.zpowers (tG φ (Equiv.swap k l))) ⊤) = 1 := by
    intro k l hkl
    rw [finrank_commSpace_eq_of_isConj φ (Equiv.Perm.isConj_swap hij hkl)]
    exact hij1
  refine ⟨?_, h1⟩
  let Φ : CFSG.QuasithinUnique.evenWeight N →+ V :=
    (phiMap φ i).comp (CFSG.QuasithinUnique.evenWeight N).subtype
  have hΦ : ∀ x : CFSG.QuasithinUnique.evenWeight N, Φ x = phiMap φ i x := fun _ => rfl
  have hsum : ∀ x : CFSG.QuasithinUnique.evenWeight N, ∑ m, (x : Fin N → ZMod 2) m = 0 :=
    fun x => x.2
  have hsurj : Function.Surjective Φ := by
    intro v
    obtain ⟨x, hx, rfl⟩ := exists_phiMap_eq hirr h1 h3 hij v
    exact ⟨⟨x, hx⟩, rfl⟩
  have hker : Φ.ker = evenWeightOnes N := by
    ext x
    rw [AddMonoidHom.mem_ker, evenWeightOnes, AddSubgroup.mem_addSubgroupOf, hΦ]
    exact ⟨mem_zmultiples_of_phiMap_eq_zero h1 h3 i (hsum x),
      phiMap_eq_zero_of_mem_zmultiples hirr hc h1 h3 i (hsum x)⟩
  let ψ : V ≃+ altHeart N :=
    (QuotientAddGroup.quotientKerEquivOfSurjective Φ hsurj).symm.trans
      (QuotientAddGroup.quotientAddEquivOfEq hker)
  have hψ : ∀ x : CFSG.QuasithinUnique.evenWeight N, ψ (Φ x) = (x : altHeart N) := by
    intro x
    have e : (QuotientAddGroup.quotientKerEquivOfSurjective Φ hsurj).symm (Φ x) =
        (x : CFSG.QuasithinUnique.evenWeight N ⧸ Φ.ker) := by
      rw [AddEquiv.symm_apply_eq]
      rfl
    show QuotientAddGroup.quotientAddEquivOfEq hker
      ((QuotientAddGroup.quotientKerEquivOfSurjective Φ hsurj).symm (Φ x)) = _
    rw [e, QuotientAddGroup.quotientAddEquivOfEq_mk]
  set K : Subgroup ↥G := (alternatingGroup (Fin N)).comap φ.toMonoidHom
  have hKmap : K.map (φ : ↥G →* Equiv.Perm (Fin N)) = alternatingGroup (Fin N) :=
    Subgroup.map_comap_eq_self_of_surjective φ.surjective _
  let e₁ : ↥K ≃* ↥(K.map G.subtype) := K.equivMapOfInjective G.subtype Subtype.val_injective
  let e₂ : ↥K ≃* ↥(alternatingGroup (Fin N)) :=
    (φ.subgroupMap K).trans (MulEquiv.subgroupCongr hKmap)
  refine ⟨e₁.symm.trans e₂, ψ, ?_⟩
  intro e v x hvx
  have hv : v = Φ x := ψ.injective (hvx.trans (hψ x).symm)
  have hge : ((e₁.symm e : ↥G) : GLV V) = (e : GLV V) := by
    have := Subgroup.coe_equivMapOfInjective_apply K G.subtype Subtype.val_injective (e₁.symm e)
    rw [MulEquiv.apply_symm_apply] at this
    exact this.symm
  have hgφ : ((e₁.symm.trans e₂ e : alternatingGroup (Fin N)) : Equiv.Perm (Fin N)) =
      φ (e₁.symm e : ↥G) := rfl
  rw [← hge, hv, hgφ]
  have e3 : ((e₁.symm e : ↥G) : GLV V) (Φ x) = Φ (evenWeightPerm (φ (e₁.symm e : ↥G)) x) :=
    apply_phiMap h1 h3 i _ (hsum x)
  rw [e3, hψ]

end CFSG.CGT.Foote82
