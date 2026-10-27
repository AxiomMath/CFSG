module


public import CFSG.LocalAnalysis.GLTheoremA.CatA.T173ATwoDefs

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T173A

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.Assembly CFSG.LocalAnalysis.GLTheoremA
open Module
open CFSG.LocalAnalysis.GLTheoremA.S172A.GL (fixSp comSp glue glue_apply_left glue_apply_right
  exists_decomp glue_mul glue_one isCompl_fixSp_comSp quad_of_mem_comSp e_mem_comSp
  eq_zero_of_mem_comSp_fixed inv_apply_of_fix add_self_V neg_V sub_V mem_fixSp mem_comSp
  cent_fix cent_com)

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]

private theorem frame_ext {r : ℕ} {P : Fin r → Submodule (ZMod 2) V} {V0 : Submodule (ZMod 2) V}
    (hint : DirectSum.IsInternal (fun o : Option (Fin r) => o.elim V0 P))
    {f g : V →ₗ[ZMod 2] V} (hV0 : ∀ v ∈ V0, f v = g v)
    (hP : ∀ k v, v ∈ P k → f v = g v) : f = g := by
  refine LinearMap.ext fun x => ?_
  have hx : x ∈ (⨆ o : Option (Fin r), o.elim V0 P) := by
    rw [hint.submodule_iSup_eq_top]; trivial
  refine Submodule.iSup_induction (motive := fun y => f y = g y)
    (fun o : Option (Fin r) => o.elim V0 P) hx ?_ ?_ ?_
  · rintro (_ | k) v hv
    · exact hV0 v hv
    · exact hP k v hv
  · simp
  · intro x y hx hy
    rw [map_add, map_add, hx, hy]

private theorem x_mem_P {x : V ≃ₗ[ZMod 2] V} {P : Submodule (ZMod 2) V}
    (hcom : comSp x = P) {v : V} (hv : v ∈ P) : x v ∈ P := by
  rw [← hcom] at hv ⊢
  exact e_mem_comSp hv

private theorem frame_mul_comm {E : Subgroup (V ≃ₗ[ZMod 2] V)} {r : ℕ}
    {x : Fin r → V ≃ₗ[ZMod 2] V} {P : Fin r → Submodule (ZMod 2) V} {V0 : Submodule (ZMod 2) V}
    (hF : LinTwoStdFrame E x P V0) (a b : Fin r) : x a * x b = x b * x a := by
  obtain ⟨-, hint, -, -, hcom, hV0, hoff⟩ := hF
  apply LinearEquiv.ext
  intro v
  change ((x a * x b : V →ₗ[ZMod 2] V)) v = ((x b * x a : V →ₗ[ZMod 2] V)) v
  refine congrArg (fun f : V →ₗ[ZMod 2] V => f v)
    (frame_ext (P := P) (V0 := V0) (f := (x a * x b : V →ₗ[ZMod 2] V))
      (g := (x b * x a : V →ₗ[ZMod 2] V)) hint ?_ ?_)
  · intro w hw
    show (x a) ((x b) w) = (x b) ((x a) w)
    rw [hV0 b w hw, hV0 a w hw, hV0 b w hw]
  · intro k w hw
    by_cases hab : a = b
    · subst hab; rfl
    · by_cases hak : k = a
      · rw [hak] at hw
        have hxav : x a w ∈ P a := x_mem_P (hcom a) hw
        show (x a) ((x b) w) = (x b) ((x a) w)
        rw [hoff b a (Ne.symm hab) w hw, hoff b a (Ne.symm hab) (x a w) hxav]
      · by_cases hbk : k = b
        · rw [hbk] at hw
          have hxbv : x b w ∈ P b := x_mem_P (hcom b) hw
          show (x a) ((x b) w) = (x b) ((x a) w)
          rw [hoff a b hab w hw, hoff a b hab (x b w) hxbv]
        · show (x a) ((x b) w) = (x b) ((x a) w)
          simp only [hoff b k (Ne.symm hbk) w hw, hoff a k (Ne.symm hak) w hw]

private theorem mem_normalizer_of_conj_mem {G : Type*} [Group G] {E : Subgroup G} {s : G}
    (hs : s * s = 1) (h : ∀ y ∈ E, s * y * s⁻¹ ∈ E) :
    s ∈ Subgroup.normalizer (E : Set G) := by
  have hsinv : s⁻¹ = s := inv_eq_of_mul_eq_one_left hs
  rw [Subgroup.mem_normalizer_iff]
  intro y
  constructor
  · exact h y
  · intro hy
    have hz := h (s * y * s⁻¹) hy
    have heq : s * (s * y * s⁻¹) * s⁻¹ = y := by
      rw [hsinv]
      calc s * (s * y * s) * s = (s * s) * y * (s * s) := by group
        _ = y := by simp [hs]
    rwa [heq] at hz

private theorem conj_mem_iSup_zpowers {G : Type*} [Group G] {ι : Type*} (x : ι → G) {s : G}
    (h : ∀ i, s * x i * s⁻¹ ∈ ⨆ i, Subgroup.zpowers (x i)) :
    ∀ y ∈ ⨆ i, Subgroup.zpowers (x i), s * y * s⁻¹ ∈ ⨆ i, Subgroup.zpowers (x i) := by
  have hmap : (⨆ i, Subgroup.zpowers (x i)).map (MulAut.conj s : G →* G)
      ≤ ⨆ i, Subgroup.zpowers (x i) := by
    rw [Subgroup.map_iSup]
    refine iSup_le fun i => ?_
    rw [MonoidHom.map_zpowers, Subgroup.zpowers_le]
    change s * x i * s⁻¹ ∈ ⨆ i, Subgroup.zpowers (x i)
    exact h i
  intro y hy
  have hconj : (MulAut.conj s : G →* G) y = s * y * s⁻¹ := MulAut.conj_apply s y
  rw [← hconj]
  exact hmap ⟨y, hy, rfl⟩

private theorem ds_surj_on_comSp {g : V ≃ₗ[ZMod 2] V} (hg3 : g ^ 3 = 1) {a : V}
    (ha : a ∈ comSp g) : ∃ u ∈ comSp g, g u - u = a := by
  obtain ⟨w, hw⟩ := mem_comSp.mp ha
  obtain ⟨u, u', rfl⟩ := exists_decomp (isCompl_fixSp_comSp hg3).symm w
  refine ⟨u, u.2, ?_⟩
  rw [← hw, map_add, mem_fixSp.1 u'.2]
  abel

private theorem comSp_le_comSp_mul {g h : V ≃ₗ[ZMod 2] V} (hg3 : g ^ 3 = 1)
    (hcomm : g * h = h * g) (htriv : ∀ v ∈ comSp g, h v = v) :
    comSp g ≤ comSp (g * h) := by
  intro a ha
  obtain ⟨u, hu, rfl⟩ := ds_surj_on_comSp hg3 ha
  refine mem_comSp.mpr ⟨u, ?_⟩
  rw [LinearEquiv.mul_apply, htriv u hu]

private theorem li_pair_of_mem_comSp {x : V ≃ₗ[ZMod 2] V} (h3 : x ^ 3 = 1)
    {Q : Submodule (ZMod 2) V} {v : V} (hv : v ∈ comSp x) (hvQ : v ∈ Q) (hxQ : x v ∈ Q)
    (hvne : v ≠ 0) : LinearIndependent (ZMod 2) ![⟨v, hvQ⟩, (⟨x v, hxQ⟩ : Q)] := by
  rw [LinearIndependent.pair_iff]
  intro s t hst
  have hV : s • v + t • (x v) = 0 := by
    have := congrArg Subtype.val hst
    simpa using this
  have hZ : ∀ c : ZMod 2, c = 0 ∨ c = 1 := by decide
  rcases hZ s with rfl | rfl <;> rcases hZ t with rfl | rfl
  · exact ⟨rfl, rfl⟩
  · exfalso
    have h0 : x v = 0 := by simpa using hV
    exact hvne (x.injective (by rw [h0, map_zero]))
  · exfalso
    exact hvne (by simpa using hV)
  · exfalso
    apply hvne
    have hfix : x v = v := by
      have h2 : x v = -v := eq_neg_of_add_eq_zero_right (by simpa using hV)
      rwa [neg_V] at h2
    exact eq_zero_of_mem_comSp_fixed h3 hv hfix

theorem lin_two_frame_inv {E : Subgroup (V ≃ₗ[ZMod 2] V)} {r : ℕ}
    {x : Fin r → V ≃ₗ[ZMod 2] V} {P : Fin r → Submodule (ZMod 2) V} {V0 : Submodule (ZMod 2) V}
    (hF : LinTwoStdFrame E x P V0) (j : Fin r) :
    ∃ s : V ≃ₗ[ZMod 2] V, s ∈ Subgroup.normalizer (E : Set (V ≃ₗ[ZMod 2] V)) ∧
      s * x j * s⁻¹ = (x j)⁻¹ ∧ (∀ v ∈ V0, s v = v) ∧ ∀ k, k ≠ j → ∀ v ∈ P k, s v = v := by
  have hFc := hF
  obtain ⟨hE, hint, hfr, h3all, hcom, hV0, hoff⟩ := hF
  have h3 : x j ^ 3 = 1 := h3all j
  have hc : IsCompl (comSp (x j)) (fixSp (x j)) := (isCompl_fixSp_comSp h3).symm
  have hfrQ : Module.finrank (ZMod 2) (comSp (x j)) = 2 := by rw [hcom j, hfr j]
  have hne : P j ≠ ⊥ := by
    intro hbot
    have h2 := hfr j
    rw [hbot] at h2
    simp at h2
  obtain ⟨v, hvP, hvne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  have hvQ : v ∈ comSp (x j) := by rw [hcom j]; exact hvP
  have hevQ : x j v ∈ comSp (x j) := e_mem_comSp hvQ
  have hquad : x j (x j v) = v + x j v := by
    have h := quad_of_mem_comSp h3 hvQ
    rw [add_assoc] at h
    have h' : x j (x j v) = -(x j v + v) := eq_neg_of_add_eq_zero_left h
    rw [h', neg_V, add_comm]
  have hli : LinearIndependent (ZMod 2) ![⟨v, hvQ⟩, (⟨x j v, hevQ⟩ : comSp (x j))] :=
    li_pair_of_mem_comSp h3 hvQ hvQ hevQ hvne
  have hcard : Fintype.card (Fin 2) = Module.finrank (ZMod 2) (comSp (x j)) := by
    rw [hfrQ]; simp
  have hspan : Submodule.span (ZMod 2) (Set.range ![⟨v, hvQ⟩, (⟨x j v, hevQ⟩ : comSp (x j))])
      = ⊤ := hli.span_eq_top_of_card_eq_finrank hcard
  let b : Basis (Fin 2) (ZMod 2) (comSp (x j)) := Basis.mk hli hspan.ge
  let g : comSp (x j) ≃ₗ[ZMod 2] comSp (x j) := b.equiv b (Equiv.swap 0 1)
  let s : V ≃ₗ[ZMod 2] V := glue hc g
  have hb0 : b 0 = (⟨v, hvQ⟩ : comSp (x j)) := by
    dsimp only [b]
    rw [Basis.mk_apply]
    simp
  have hb1 : b 1 = (⟨x j v, hevQ⟩ : comSp (x j)) := by
    dsimp only [b]
    rw [Basis.mk_apply]
    simp
  have hg0 : g (b 0) = b 1 := by simp [g]
  have hg1 : g (b 1) = b 0 := by simp [g]
  have hg2 : g * g = 1 := by
    apply b.ext'
    intro i
    fin_cases i <;> simp [g]
  let eQ : comSp (x j) →ₗ[ZMod 2] comSp (x j) :=
    (x j).toLinearMap.restrict (fun a ha => e_mem_comSp ha)
  let eInvQ : comSp (x j) →ₗ[ZMod 2] comSp (x j) :=
    ((x j)⁻¹).toLinearMap.restrict (fun a ha =>
      cent_com (by rw [inv_mul_cancel, mul_inv_cancel]) ha)
  have heQ0 : eQ (b 0) = b 1 := by
    rw [hb0, hb1]
    apply Subtype.ext
    rfl
  have heQ1 : eQ (b 1) = b 0 + b 1 := by
    rw [hb1, hb0]
    apply Subtype.ext
    show x j (x j v) = v + x j v
    exact hquad
  have heInv0 : eInvQ (b 0) = b 0 + b 1 := by
    rw [hb0, hb1]
    apply Subtype.ext
    show (x j)⁻¹ v = v + x j v
    have he2 : (x j)⁻¹ = (x j) ^ 2 := by
      rw [inv_eq_iff_mul_eq_one]
      rw [← pow_succ']
      exact h3
    rw [he2]
    simpa [pow_two, LinearEquiv.mul_apply] using hquad
  have heInv1 : eInvQ (b 1) = b 0 := by
    rw [hb1, hb0]
    apply Subtype.ext
    show (x j)⁻¹ (x j v) = v
    simp
  have hL : g.toLinearMap.comp eQ = eInvQ.comp g.toLinearMap := by
    apply b.ext
    intro i
    fin_cases i
    · show g (eQ (b 0)) = eInvQ (g (b 0))
      rw [heQ0, hg1, hg0, heInv1]
    · show g (eQ (b 1)) = eInvQ (g (b 1))
      rw [heQ1, map_add, hg0, hg1, heInv0]
      exact add_comm _ _
  have hge : ∀ u : comSp (x j), g (eQ u) = eInvQ (g u) := by
    intro u
    have := congrArg (fun f : comSp (x j) →ₗ[ZMod 2] comSp (x j) => f u) hL
    simpa using this
  have hs2 : s * s = 1 := by
    dsimp only [s]
    rw [← glue_mul hc g g, hg2, glue_one]
  have hsinv : s⁻¹ = s := inv_eq_of_mul_eq_one_left hs2
  have hconj : s * x j = (x j)⁻¹ * s := by
    have hgeV : ∀ u : comSp (x j),
        (g (eQ u) : V) = (x j)⁻¹ ((g u : comSp (x j)) : V) := by
      intro u
      have h1 := congrArg Subtype.val (hge u)
      rw [show ((eInvQ (g u) : comSp (x j)) : V)
        = (x j)⁻¹ ((g u : comSp (x j)) : V) from rfl] at h1
      exact h1
    apply LinearEquiv.ext
    intro y
    obtain ⟨u, u', rfl⟩ := exists_decomp hc y
    have hgl : glue hc g (x j (u:V)) = (g (eQ u) : V) :=
      glue_apply_left hc g (eQ u)
    have hgu : glue hc g (u:V) = (g u : V) := glue_apply_left hc g u
    have hgu' : glue hc g (u':V) = (u':V) := glue_apply_right hc g u'
    dsimp only [s]
    simp only [LinearEquiv.mul_apply, map_add]
    rw [hgl, show x j (u':V) = (u':V) from mem_fixSp.1 u'.2, hgu', hgu,
      show (x j)⁻¹ (u':V) = (u':V) from inv_apply_of_fix (mem_fixSp.1 u'.2), hgeV u]
  have hgoal_conj : s * x j * s⁻¹ = (x j)⁻¹ := by
    rw [hsinv, hconj, mul_assoc, hs2, mul_one]
  have hconj_k : ∀ k, k ≠ j → s * x k = x k * s := by
    intro k hkj
    have hcomm_k : x k * x j = x j * x k := frame_mul_comm hFc k j
    apply LinearEquiv.ext
    intro y
    obtain ⟨u, u', rfl⟩ := exists_decomp hc y
    have huP : (u:V) ∈ P j := by rw [← hcom j]; exact u.2
    have hku : x k (u:V) = (u:V) := hoff k j hkj (u:V) huP
    have hku' : x k (u':V) ∈ fixSp (x j) := cent_fix hcomm_k u'.2
    have hkgu : x k ((g u : comSp (x j)) : V) = ((g u : comSp (x j)) : V) := by
      refine hoff k j hkj _ ?_
      rw [← hcom j]; exact (g u).2
    have hgl : glue hc g (u:V) = (g u : V) := glue_apply_left hc g u
    have hgu' : glue hc g (u':V) = (u':V) := glue_apply_right hc g u'
    have hku'' : glue hc g (x k (u':V)) = (x k (u':V)) :=
      glue_apply_right hc g ⟨x k (u':V), hku'⟩
    dsimp only [s]
    simp only [LinearEquiv.mul_apply, map_add]
    rw [hku, hgl, hku'', hgu', hkgu]
  have hmem : ∀ k, s * x k * s⁻¹ ∈ ⨆ m, Subgroup.zpowers (x m) := by
    intro k
    by_cases hkj : k = j
    · rw [hkj, hgoal_conj]
      exact Subgroup.mem_iSup_of_mem j
        ((Subgroup.zpowers (x j)).inv_mem (Subgroup.mem_zpowers (x j)))
    · have hk := hconj_k k hkj
      rw [hk, mul_assoc, mul_inv_cancel, mul_one]
      exact Subgroup.mem_iSup_of_mem k (Subgroup.mem_zpowers (x k))
  refine ⟨s, ?_, hgoal_conj, ?_, ?_⟩
  · exact hE.symm ▸ mem_normalizer_of_conj_mem hs2 (conj_mem_iSup_zpowers x hmem)
  · intro v hv
    dsimp only [s]
    exact glue_apply_right hc g ⟨v, mem_fixSp.mpr (hV0 j v hv)⟩
  · intro k hkj v hv
    dsimp only [s]
    exact glue_apply_right hc g ⟨v, mem_fixSp.mpr (hoff j k (Ne.symm hkj) v hv)⟩

theorem lin_two_frame_swap {E : Subgroup (V ≃ₗ[ZMod 2] V)} {r : ℕ}
    {x : Fin r → V ≃ₗ[ZMod 2] V} {P : Fin r → Submodule (ZMod 2) V} {V0 : Submodule (ZMod 2) V}
    (hF : LinTwoStdFrame E x P V0) (i j : Fin r) (hij : i ≠ j) :
    ∃ σ : V ≃ₗ[ZMod 2] V, σ ∈ Subgroup.normalizer (E : Set (V ≃ₗ[ZMod 2] V)) ∧
      σ * x i * σ⁻¹ = x j ∧ (∀ v ∈ V0, σ v = v) ∧ ∀ k, k ≠ i → k ≠ j → ∀ v ∈ P k, σ v = v := by
  have hFc := hF
  obtain ⟨hE, hint, hfr, h3all, hcom, hV0, hoff⟩ := hF
  set e : V ≃ₗ[ZMod 2] V := x i * x j with he
  have hcomm : x i * x j = x j * x i := frame_mul_comm hFc i j
  have h3e : e ^ 3 = 1 := by
    rw [he, Commute.mul_pow hcomm, h3all i, h3all j, one_mul]
  have hc : IsCompl (comSp e) (fixSp e) := (isCompl_fixSp_comSp h3e).symm
  have hcomm_i : x i * e = e * x i := by
    rw [he]
    calc x i * (x i * x j) = x i * (x j * x i) := by rw [hcomm]
      _ = x i * x j * x i := (mul_assoc _ _ _).symm
  have hcomm_j : x j * e = e * x j := by
    rw [he]
    calc x j * (x i * x j) = (x j * x i) * x j := (mul_assoc _ _ _).symm
      _ = (x i * x j) * x j := by rw [hcomm]
  have hPi_le : P i ≤ comSp e := by
    rw [← hcom i, he]
    exact comSp_le_comSp_mul (h3all i) hcomm
      (fun v hv => by rw [hcom i] at hv; exact hoff j i (Ne.symm hij) v hv)
  have hPj_le : P j ≤ comSp e := by
    rw [← hcom j, he, show x i * x j = x j * x i from hcomm]
    exact comSp_le_comSp_mul (h3all j) hcomm.symm
      (fun v hv => by rw [hcom j] at hv; exact hoff i j hij v hv)
  have hQle : comSp e ≤ P i ⊔ P j := by
    intro x' hx'
    obtain ⟨v, rfl⟩ := mem_comSp.mp hx'
    have h1 : x i (x j v) - x j v ∈ P i := by
      rw [← hcom i]
      exact mem_comSp.mpr ⟨x j v, rfl⟩
    have h2 : x j v - v ∈ P j := by
      rw [← hcom j]
      exact mem_comSp.mpr ⟨v, rfl⟩
    have hsum : x i (x j v) - v = (x i (x j v) - x j v) + (x j v - v) := by abel
    rw [he, LinearEquiv.mul_apply, hsum]
    exact Submodule.add_mem _ (Submodule.mem_sup_left h1) (Submodule.mem_sup_right h2)
  have hQeq : comSp e = P i ⊔ P j := le_antisymm hQle (sup_le hPi_le hPj_le)
  have hPiPj : Disjoint (P i) (P j) := by
    have h := hint.submodule_iSupIndep.pairwiseDisjoint
      (show (some i : Option (Fin r)) ≠ some j from by simp [hij])
    change Disjoint (P i) (P j) at h
    exact h
  have hfix_apply : ∀ w ∈ fixSp e, x i w = w ∧ x j w = w := by
    intro w hw
    have hw' : x i (x j w) = w := by
      have h1 := mem_fixSp.1 hw
      rw [he, LinearEquiv.mul_apply] at h1
      exact h1
    have h1 : x j w - w ∈ P j := by
      rw [← hcom j]; exact mem_comSp.mpr ⟨w, rfl⟩
    have h2 : x i (x j w) - x j w ∈ P i := by
      rw [← hcom i]; exact mem_comSp.mpr ⟨x j w, rfl⟩
    have heq : x j w - w = x i (x j w) - x j w := by
      rw [hw', sub_V, sub_V, add_comm]
    have hboth : x j w - w ∈ P i ⊓ P j := ⟨by rw [heq]; exact h2, h1⟩
    have hzero : x j w - w = 0 :=
      Submodule.disjoint_def.mp hPiPj _ hboth.1 hboth.2
    have hxjw : x j w = w := sub_eq_zero.mp hzero
    have hxiw : x i w = w := by
      calc x i w = x i (x j w) := by rw [hxjw]
        _ = w := hw'
    exact ⟨hxiw, hxjw⟩
  have hfrQ : Module.finrank (ZMod 2) (comSp e) = 4 := by
    have h := Submodule.finrank_sup_add_finrank_inf_eq (P i) (P j)
    rw [hPiPj.eq_bot, finrank_bot, add_zero, hfr i, hfr j] at h
    rw [hQeq, h]
  have hnei : P i ≠ ⊥ := by
    intro hbot
    have h2 := hfr i
    rw [hbot] at h2
    simp at h2
  have hnej : P j ≠ ⊥ := by
    intro hbot
    have h2 := hfr j
    rw [hbot] at h2
    simp at h2
  obtain ⟨v, hvPi, hvne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hnei
  obtain ⟨w, hwPj, hwne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hnej
  have hv_com_i : v ∈ comSp (x i) := by rw [hcom i]; exact hvPi
  have hw_com_j : w ∈ comSp (x j) := by rw [hcom j]; exact hwPj
  have hxivP : x i v ∈ P i := x_mem_P (hcom i) hvPi
  have hxjwP : x j w ∈ P j := x_mem_P (hcom j) hwPj
  have hvQ : v ∈ comSp e := hPi_le hvPi
  have hxivQ : x i v ∈ comSp e := hPi_le hxivP
  have hwQ : w ∈ comSp e := hPj_le hwPj
  have hxjwQ : x j w ∈ comSp e := hPj_le hxjwP
  have hquad_i : x i (x i v) = v + x i v := by
    have h := quad_of_mem_comSp (h3all i) hv_com_i
    rw [add_assoc] at h
    have h' : x i (x i v) = -(x i v + v) := eq_neg_of_add_eq_zero_left h
    rw [h', neg_V, add_comm]
  have hquad_j : x j (x j w) = w + x j w := by
    have h := quad_of_mem_comSp (h3all j) hw_com_j
    rw [add_assoc] at h
    have h' : x j (x j w) = -(x j w + w) := eq_neg_of_add_eq_zero_left h
    rw [h', neg_V, add_comm]
  have hli_i : LinearIndependent (ZMod 2)
      ![⟨v, hvQ⟩, (⟨x i v, hxivQ⟩ : comSp e)] :=
    li_pair_of_mem_comSp (h3all i) hv_com_i hvQ hxivQ hvne
  have hli_j : LinearIndependent (ZMod 2)
      ![⟨w, hwQ⟩, (⟨x j w, hxjwQ⟩ : comSp e)] :=
    li_pair_of_mem_comSp (h3all j) hw_com_j hwQ hxjwQ hwne
  have hdisj_span : Disjoint
      (Submodule.span (ZMod 2) (Set.range ![⟨v, hvQ⟩, (⟨x i v, hxivQ⟩ : comSp e)]))
      (Submodule.span (ZMod 2) (Set.range ![⟨w, hwQ⟩, (⟨x j w, hxjwQ⟩ : comSp e)])) := by
    rw [Submodule.disjoint_def]
    intro y hy hy'
    apply Subtype.ext
    have hyPi : (y:V) ∈ P i := by
      have hle : Submodule.span (ZMod 2)
          (Set.range ![⟨v, hvQ⟩, (⟨x i v, hxivQ⟩ : comSp e)])
          ≤ Submodule.comap (comSp e).subtype (P i) := by
        rw [Submodule.span_le]
        rintro z ⟨m, rfl⟩
        fin_cases m
        · exact hvPi
        · exact hxivP
      exact hle hy
    have hyPj : (y:V) ∈ P j := by
      have hle : Submodule.span (ZMod 2)
          (Set.range ![⟨w, hwQ⟩, (⟨x j w, hxjwQ⟩ : comSp e)])
          ≤ Submodule.comap (comSp e).subtype (P j) := by
        rw [Submodule.span_le]
        rintro z ⟨m, rfl⟩
        fin_cases m
        · exact hwPj
        · exact hxjwP
      exact hle hy'
    exact Submodule.disjoint_def.mp hPiPj (y:V) hyPi hyPj
  have hli : LinearIndependent (ZMod 2)
      (Sum.elim ![⟨v, hvQ⟩, (⟨x i v, hxivQ⟩ : comSp e)]
        ![⟨w, hwQ⟩, (⟨x j w, hxjwQ⟩ : comSp e)]) :=
    LinearIndependent.sum_type hli_i hli_j hdisj_span
  have hcard : Fintype.card (Fin 2 ⊕ Fin 2) = Module.finrank (ZMod 2) (comSp e) := by
    rw [hfrQ]; simp
  have hspan : Submodule.span (ZMod 2)
      (Set.range (Sum.elim ![⟨v, hvQ⟩, (⟨x i v, hxivQ⟩ : comSp e)]
        ![⟨w, hwQ⟩, (⟨x j w, hxjwQ⟩ : comSp e)])) = ⊤ :=
    hli.span_eq_top_of_card_eq_finrank hcard
  let bFam : Fin 2 ⊕ Fin 2 → comSp e :=
    Sum.elim ![⟨v, hvQ⟩, (⟨x i v, hxivQ⟩ : comSp e)]
      ![⟨w, hwQ⟩, (⟨x j w, hxjwQ⟩ : comSp e)]
  let b : Basis (Fin 2 ⊕ Fin 2) (ZMod 2) (comSp e) := Basis.mk hli hspan.ge
  let τ : comSp e ≃ₗ[ZMod 2] comSp e := b.equiv b (Equiv.sumComm (Fin 2) (Fin 2))
  let σ : V ≃ₗ[ZMod 2] V := glue hc τ
  have hb_inl0 : b (Sum.inl 0) = (⟨v, hvQ⟩ : comSp e) := by
    dsimp only [b, bFam]; rw [Basis.mk_apply]; simp
  have hb_inl1 : b (Sum.inl 1) = (⟨x i v, hxivQ⟩ : comSp e) := by
    dsimp only [b, bFam]; rw [Basis.mk_apply]; simp
  have hb_inr0 : b (Sum.inr 0) = (⟨w, hwQ⟩ : comSp e) := by
    dsimp only [b, bFam]; rw [Basis.mk_apply]; simp
  have hb_inr1 : b (Sum.inr 1) = (⟨x j w, hxjwQ⟩ : comSp e) := by
    dsimp only [b, bFam]; rw [Basis.mk_apply]; simp
  have hτ0 : τ (b (Sum.inl 0)) = b (Sum.inr 0) := by simp [τ]
  have hτ1 : τ (b (Sum.inl 1)) = b (Sum.inr 1) := by simp [τ]
  have hτ2 : τ (b (Sum.inr 0)) = b (Sum.inl 0) := by simp [τ]
  have hτ3 : τ (b (Sum.inr 1)) = b (Sum.inl 1) := by simp [τ]
  let xiQ : comSp e →ₗ[ZMod 2] comSp e :=
    (x i).toLinearMap.restrict (fun a ha => cent_com hcomm_i ha)
  let xjQ : comSp e →ₗ[ZMod 2] comSp e :=
    (x j).toLinearMap.restrict (fun a ha => cent_com hcomm_j ha)
  have hxi0 : xiQ (b (Sum.inl 0)) = b (Sum.inl 1) := by
    rw [hb_inl0, hb_inl1]; apply Subtype.ext; rfl
  have hxi1 : xiQ (b (Sum.inl 1)) = b (Sum.inl 0) + b (Sum.inl 1) := by
    rw [hb_inl1, hb_inl0]; apply Subtype.ext
    show x i (x i v) = v + x i v
    exact hquad_i
  have hxi2 : xiQ (b (Sum.inr 0)) = b (Sum.inr 0) := by
    rw [hb_inr0]; apply Subtype.ext
    show x i w = w
    exact hoff i j hij w hwPj
  have hxi3 : xiQ (b (Sum.inr 1)) = b (Sum.inr 1) := by
    rw [hb_inr1]; apply Subtype.ext
    show x i (x j w) = x j w
    exact hoff i j hij (x j w) hxjwP
  have hxj0 : xjQ (b (Sum.inl 0)) = b (Sum.inl 0) := by
    rw [hb_inl0]; apply Subtype.ext
    show x j v = v
    exact hoff j i (Ne.symm hij) v hvPi
  have hxj1 : xjQ (b (Sum.inl 1)) = b (Sum.inl 1) := by
    rw [hb_inl1]; apply Subtype.ext
    show x j (x i v) = x i v
    exact hoff j i (Ne.symm hij) (x i v) hxivP
  have hxj2 : xjQ (b (Sum.inr 0)) = b (Sum.inr 1) := by
    rw [hb_inr0, hb_inr1]; apply Subtype.ext; rfl
  have hxj3 : xjQ (b (Sum.inr 1)) = b (Sum.inr 0) + b (Sum.inr 1) := by
    rw [hb_inr1, hb_inr0]; apply Subtype.ext
    show x j (x j w) = w + x j w
    exact hquad_j
  have hτ_eq : ∀ u : comSp e, τ (xiQ u) = xjQ (τ u) := by
    have hL : τ.toLinearMap.comp xiQ = xjQ.comp τ.toLinearMap := by
      apply b.ext
      intro idx
      rcases idx with m | m <;> fin_cases m
      · show τ (xiQ (b (Sum.inl 0))) = xjQ (τ (b (Sum.inl 0)))
        rw [hxi0, hτ1, hτ0, hxj2]
      · show τ (xiQ (b (Sum.inl 1))) = xjQ (τ (b (Sum.inl 1)))
        rw [hxi1, map_add, hτ0, hτ1, hxj3]
      · show τ (xiQ (b (Sum.inr 0))) = xjQ (τ (b (Sum.inr 0)))
        rw [hxi2, hτ2, hxj0]
      · show τ (xiQ (b (Sum.inr 1))) = xjQ (τ (b (Sum.inr 1)))
        rw [hxi3, hτ3, hxj1]
    intro u
    have := congrArg (fun f : comSp e →ₗ[ZMod 2] comSp e => f u) hL
    simpa using this
  have hτ_eq' : ∀ u : comSp e, τ (xjQ u) = xiQ (τ u) := by
    have hL : τ.toLinearMap.comp xjQ = xiQ.comp τ.toLinearMap := by
      apply b.ext
      intro idx
      rcases idx with m | m <;> fin_cases m
      · show τ (xjQ (b (Sum.inl 0))) = xiQ (τ (b (Sum.inl 0)))
        rw [hxj0, hτ0, hxi2]
      · show τ (xjQ (b (Sum.inl 1))) = xiQ (τ (b (Sum.inl 1)))
        rw [hxj1, hτ1, hxi3]
      · show τ (xjQ (b (Sum.inr 0))) = xiQ (τ (b (Sum.inr 0)))
        rw [hxj2, hτ3, hτ2, hxi0]
      · show τ (xjQ (b (Sum.inr 1))) = xiQ (τ (b (Sum.inr 1)))
        rw [hxj3, map_add, hτ2, hτ3, hxi1]
    intro u
    have := congrArg (fun f : comSp e →ₗ[ZMod 2] comSp e => f u) hL
    simpa using this
  have hτ2inv : τ * τ = 1 := by
    apply b.ext'
    intro idx
    rcases idx with m | m <;> fin_cases m <;> simp [τ]
  have hσ2 : σ * σ = 1 := by
    dsimp only [σ]
    rw [← glue_mul hc τ τ, hτ2inv, glue_one]
  have hconj_i : σ * x i = x j * σ := by
    apply LinearEquiv.ext
    intro y
    obtain ⟨u, u', rfl⟩ := exists_decomp hc y
    have hfixi : x i (u':V) ∈ fixSp e := cent_fix hcomm_i u'.2
    have hgl : glue hc τ (x i (u:V)) = (τ (xiQ u) : V) := glue_apply_left hc τ (xiQ u)
    have hgtu : glue hc τ (u:V) = (τ u : V) := glue_apply_left hc τ u
    have hgu' : glue hc τ (u':V) = (u':V) := glue_apply_right hc τ u'
    have hgxu' : glue hc τ (x i (u':V)) = (x i (u':V)) :=
      glue_apply_right hc τ ⟨x i (u':V), hfixi⟩
    dsimp only [σ]
    simp only [LinearEquiv.mul_apply, map_add]
    rw [hgl, hgxu', hgtu, hgu', congrArg Subtype.val (hτ_eq u),
      (hfix_apply u' u'.2).1, (hfix_apply u' u'.2).2]
    rfl
  have hconj_j : σ * x j = x i * σ := by
    apply LinearEquiv.ext
    intro y
    obtain ⟨u, u', rfl⟩ := exists_decomp hc y
    have hfixj : x j (u':V) ∈ fixSp e := cent_fix hcomm_j u'.2
    have hgl : glue hc τ (x j (u:V)) = (τ (xjQ u) : V) := glue_apply_left hc τ (xjQ u)
    have hgtu : glue hc τ (u:V) = (τ u : V) := glue_apply_left hc τ u
    have hgu' : glue hc τ (u':V) = (u':V) := glue_apply_right hc τ u'
    have hgxu' : glue hc τ (x j (u':V)) = (x j (u':V)) :=
      glue_apply_right hc τ ⟨x j (u':V), hfixj⟩
    dsimp only [σ]
    simp only [LinearEquiv.mul_apply, map_add]
    rw [hgl, hgxu', hgtu, hgu', congrArg Subtype.val (hτ_eq' u),
      (hfix_apply u' u'.2).1, (hfix_apply u' u'.2).2]
    rfl
  have hconj_k : ∀ k, k ≠ i → k ≠ j → σ * x k = x k * σ := by
    intro k hki hkj
    have hcomm_k : x k * e = e * x k := by
      rw [he]
      calc x k * (x i * x j) = (x k * x i) * x j := (mul_assoc _ _ _).symm
        _ = (x i * x k) * x j := by rw [frame_mul_comm hFc k i]
        _ = x i * (x k * x j) := mul_assoc _ _ _
        _ = x i * (x j * x k) := by rw [frame_mul_comm hFc k j]
        _ = (x i * x j) * x k := (mul_assoc _ _ _).symm
    have hker : P i ⊔ P j ≤ LinearMap.ker ((x k).toLinearMap - LinearMap.id) := by
      refine sup_le ?_ ?_
      · intro a ha
        simp only [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply, sub_eq_zero]
        exact hoff k i hki a ha
      · intro a ha
        simp only [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply, sub_eq_zero]
        exact hoff k j hkj a ha
    have konQ : ∀ a : comSp e, x k (a:V) = (a:V) := by
      intro a
      have ha : (a:V) ∈ P i ⊔ P j := by rw [← hQeq]; exact a.2
      have := LinearMap.mem_ker.mp (hker ha)
      simpa [sub_eq_zero] using this
    apply LinearEquiv.ext
    intro y
    obtain ⟨u, u', rfl⟩ := exists_decomp hc y
    have hku : x k (u:V) = (u:V) := konQ u
    have hkgu : x k ((τ u : comSp e) : V) = ((τ u : comSp e) : V) := konQ (τ u)
    have hku' : x k (u':V) ∈ fixSp e := cent_fix hcomm_k u'.2
    have hgl : glue hc τ (u:V) = (τ u : V) := glue_apply_left hc τ u
    have hgu' : glue hc τ (u':V) = (u':V) := glue_apply_right hc τ u'
    have hku'' : glue hc τ (x k (u':V)) = (x k (u':V)) :=
      glue_apply_right hc τ ⟨x k (u':V), hku'⟩
    dsimp only [σ]
    simp only [LinearEquiv.mul_apply, map_add]
    rw [hku, hgl, hku'', hgu', hkgu]
  have hmem : ∀ k, σ * x k * σ⁻¹ ∈ ⨆ m, Subgroup.zpowers (x m) := by
    intro k
    by_cases hki : k = i
    · rw [hki]
      have hconji : σ * x i * σ⁻¹ = x j := by
        rw [hconj_i, mul_assoc, mul_inv_cancel, mul_one]
      rw [hconji]
      exact Subgroup.mem_iSup_of_mem j (Subgroup.mem_zpowers (x j))
    · by_cases hkj : k = j
      · rw [hkj]
        have hconjj : σ * x j * σ⁻¹ = x i := by
          rw [hconj_j, mul_assoc, mul_inv_cancel, mul_one]
        rw [hconjj]
        exact Subgroup.mem_iSup_of_mem i (Subgroup.mem_zpowers (x i))
      · have hk := hconj_k k hki hkj
        rw [hk, mul_assoc, mul_inv_cancel, mul_one]
        exact Subgroup.mem_iSup_of_mem k (Subgroup.mem_zpowers (x k))
  refine ⟨σ, ?_, ?_, ?_, ?_⟩
  · exact hE.symm ▸ mem_normalizer_of_conj_mem hσ2 (conj_mem_iSup_zpowers x hmem)
  · have hconji : σ * x i * σ⁻¹ = x j := by
      rw [hconj_i, mul_assoc, mul_inv_cancel, mul_one]
    exact hconji
  · intro v hv
    dsimp only [σ]
    refine glue_apply_right hc τ ⟨v, ?_⟩
    rw [mem_fixSp, he, LinearEquiv.mul_apply, hV0 j v hv, hV0 i v hv]
  · intro k hki hkj v hv
    dsimp only [σ]
    refine glue_apply_right hc τ ⟨v, ?_⟩
    rw [mem_fixSp, he, LinearEquiv.mul_apply, hoff j k (Ne.symm hkj) v hv,
      hoff i k (Ne.symm hki) v hv]

end CFSG.LocalAnalysis.GLTheoremA.T173A

end
