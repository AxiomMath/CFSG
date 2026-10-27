module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.S172CCentFrame

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LocalAnalysis.GLTheoremA.T173M

open Module QuadraticMap CFSG.RankThree.Classical2 CFSG.GroupTheory.WeirSylow
  CFSG.LocalAnalysis.GLTheoremA.S172C.Cent

variable {F : Type} [Field F] [Finite F] [CharP F 2] {V : Type} [AddCommGroup V] [Module F V]
  [FiniteDimensional F V] {Q : QuadraticForm F V} {p : ℕ}

theorem eq_zero_of_map_eq_zero_of_mem_plane {m : ℕ} {U : Fin m → Submodule F V} (hU : IsPlaneSystem Q U)
    (k : Fin m) {x : V} (hx : x ∈ U k) (hQx : Q x = 0) : x = 0 := by
  by_contra hx0
  refine hU.not_isPlusType k ⟨Submodule.span F {(⟨x, hx⟩ : U k)}, ?_, ?_⟩
  · rw [finrank_span_singleton (fun h => hx0 (congrArg Subtype.val h)), hU.finrank_eq k]
  · intro y hy
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hy
    show Q (c • x) = 0
    rw [QuadraticMap.map_smul, hQx, smul_zero]

theorem iSup_eq_top_of_finrank {m : ℕ} {U : Fin m → Submodule F V} (hU : IsPlaneSystem Q U)
    (hdim : Module.finrank F V = 2 * m) : ⨆ k, U k = ⊤ := by
  have e : (⨆ k ∈ (Finset.univ : Finset (Fin m)), U k : Submodule F V) = ⨆ k, U k := by simp
  rw [← e]
  apply Submodule.eq_top_of_finrank_eq
  rw [hU.finrank_biSup, Finset.card_univ, Fintype.card_fin, hdim]

private theorem inf_sup_le_sup_inf_of_fix_aux1 {g : V ≃ₗ[F] V} {n : ℕ} (hn : Odd n)
    {X : Submodule F V} (hX : ∀ x ∈ X, g x = x) {x : V} (hx : x ∈ X) :
    (∑ m ∈ Finset.range n, (g ^ m) x) = x := by
  have htermX : ∀ m, (g ^ m) x = x := by
    intro m
    induction m with
    | zero => simp
    | succ m ih => rw [pow_succ', LinearEquiv.mul_apply, ih, hX x hx]
  have hcongr : (∑ m ∈ Finset.range n, (g ^ m) x) = ∑ m ∈ Finset.range n, x :=
    Finset.sum_congr rfl fun m _ => htermX m
  have hnF : (n : F) = 1 := by
    rw [CharTwo.natCast_eq_ite, if_neg (Nat.not_even_iff_odd.2 hn)]
  rw [hcongr, Finset.sum_const, Finset.card_range,
    ← Nat.cast_smul_eq_nsmul F n x, hnF, one_smul]

private theorem inf_sup_le_sup_inf_of_fix_aux2 {g : V ≃ₗ[F] V} {n : ℕ} (hgn : g ^ n = 1)
    {Y : Submodule F V} (hY : ∀ y ∈ Y, g y ∈ Y) (hYfree : ∀ y ∈ Y, g y = y → y = 0)
    {y : V} (hy : y ∈ Y) : (∑ m ∈ Finset.range n, (g ^ m) y) = 0 := by
  have htermY : ∀ m, (g ^ m) y ∈ Y := by
    intro m
    induction m with
    | zero => simpa using hy
    | succ m ih => rw [pow_succ', LinearEquiv.mul_apply]; exact hY _ ih
  have htY : (∑ m ∈ Finset.range n, (g ^ m) y) ∈ Y :=
    Submodule.sum_mem _ fun m _ => htermY m
  refine hYfree _ htY ?_
  rw [map_sum]
  have hcongr : (∑ m ∈ Finset.range n, g ((g ^ m) y))
      = ∑ m ∈ Finset.range n, (g ^ (m + 1)) y :=
    Finset.sum_congr rfl fun m _ => by rw [pow_succ', LinearEquiv.mul_apply]
  rw [hcongr]
  have h1 : (∑ m ∈ Finset.range (n + 1), (g ^ m) y)
      = (∑ m ∈ Finset.range n, (g ^ m) y) + y := by
    rw [Finset.sum_range_succ, hgn]; rfl
  have h2 : (∑ m ∈ Finset.range (n + 1), (g ^ m) y)
      = y + ∑ m ∈ Finset.range n, (g ^ (m + 1)) y := by
    rw [Finset.sum_range_succ', add_comm]; rfl
  have h3 : (∑ m ∈ Finset.range n, (g ^ m) y) + y
      = y + ∑ m ∈ Finset.range n, (g ^ (m + 1)) y := by rw [← h1, h2]
  have h5 : y + (∑ m ∈ Finset.range n, (g ^ (m + 1)) y)
      = y + ∑ m ∈ Finset.range n, (g ^ m) y := by rw [← h3, add_comm]
  exact add_left_cancel h5

private theorem inf_sup_le_sup_inf_of_fix_aux3 {g : V ≃ₗ[F] V} {n : ℕ} {W : Submodule F V}
    (hW : ∀ w ∈ W, g w ∈ W) {w : V} (hw : w ∈ W) :
    (∑ m ∈ Finset.range n, (g ^ m) w) ∈ W := by
  have htermW : ∀ m, (g ^ m) w ∈ W := by
    intro m
    induction m with
    | zero => simpa using hw
    | succ m ih => rw [pow_succ', LinearEquiv.mul_apply]; exact hW _ ih
  exact Submodule.sum_mem _ fun m _ => htermW m

theorem inf_sup_le_sup_inf_of_fix {g : V ≃ₗ[F] V} {n : ℕ} (hn : Odd n) (hgn : g ^ n = 1)
    {X Y W : Submodule F V} (hX : ∀ x ∈ X, g x = x) (hY : ∀ y ∈ Y, g y ∈ Y)
    (hYfree : ∀ y ∈ Y, g y = y → y = 0) (hW : ∀ w ∈ W, g w ∈ W) :
    W ⊓ (X ⊔ Y) ≤ (W ⊓ X) ⊔ (W ⊓ Y) := by
  intro w hw
  obtain ⟨x, hx, y, hy, rfl⟩ := Submodule.mem_sup.1 hw.2
  have hsumx := inf_sup_le_sup_inf_of_fix_aux1 hn hX hx
  have hsumy := inf_sup_le_sup_inf_of_fix_aux2 hgn hY hYfree hy
  have hsumW : (∑ m ∈ Finset.range n, (g ^ m) (x + y)) ∈ W :=
    inf_sup_le_sup_inf_of_fix_aux3 hW hw.1
  have hsplit : (∑ m ∈ Finset.range n, (g ^ m) (x + y))
      = (∑ m ∈ Finset.range n, (g ^ m) x) + ∑ m ∈ Finset.range n, (g ^ m) y := by
    have hcongr : (∑ m ∈ Finset.range n, (g ^ m) (x + y))
        = ∑ m ∈ Finset.range n, ((g ^ m) x + (g ^ m) y) :=
      Finset.sum_congr rfl fun m _ => map_add ((g ^ m) : V ≃ₗ[F] V) x y
    rw [hcongr, Finset.sum_add_distrib]
  have hxW : x ∈ W := by
    rw [hsplit, hsumx, hsumy, add_zero] at hsumW
    exact hsumW
  have hyW : y ∈ W := by
    have hyw : y = (x + y) - x := by abel
    rw [hyw]
    exact Submodule.sub_mem _ hw.1 hxW
  exact Submodule.add_mem_sup ⟨hxW, hx⟩ ⟨hyW, hy⟩

theorem le_polarPerp_of_invariant_of_free {g : V ≃ₗ[F] V} {n : ℕ} (hn : Odd n) (hgn : g ^ n = 1)
    {P W : Submodule F V} (hP : IsCompl P (polarPerp Q P)) (haniso : ∀ x ∈ P, Q x = 0 → x = 0)
    (hPmaps : ∀ x ∈ P, g x ∈ P) (hfree : ∀ x ∈ P, g x = x → x = 0)
    (hfix : ∀ x ∈ polarPerp Q P, g x = x) (hTS : ∀ x ∈ W, Q x = 0) (hW : ∀ w ∈ W, g w ∈ W) :
    W ≤ polarPerp Q P := by
  have h := inf_sup_le_sup_inf_of_fix hn hgn hfix hPmaps hfree hW
  rw [hP.symm.sup_eq_top, inf_top_eq] at h
  intro w hw
  obtain ⟨x, hx, y, hy, rfl⟩ := Submodule.mem_sup.1 (h hw)
  have hy0 : y = 0 := haniso y hy.2 (hTS y hy.1)
  rw [hy0, add_zero]
  exact hx.2

private theorem eq_bot_of_separated_aux1 {m : ℕ} {U : Fin m → Submodule F V} {g : V ≃ₗ[F] V}
    {s : Finset (Fin m)} (h : ∀ k ∈ s, ∀ x ∈ U k, g x = x) {x : V}
    (hx : x ∈ ⨆ k ∈ s, U k) : g x = x := by
  revert h x
  refine Finset.induction_on s ?_ ?_
  · intro h x hx
    have hx0 : x = 0 := by simpa using hx
    rw [hx0]
    simp
  · intro a s ha ih h x hx
    rw [Finset.iSup_insert] at hx
    obtain ⟨u, hu, v, hv, rfl⟩ := Submodule.mem_sup.1 hx
    rw [map_add, h a (Finset.mem_insert_self a s) u hu,
      ih (fun k hk => h k (Finset.mem_insert_of_mem hk)) hv]

private theorem eq_bot_of_separated_aux2 {m : ℕ} {U : Fin m → Submodule F V} {g : V ≃ₗ[F] V}
    {s : Finset (Fin m)} (h : ∀ k ∈ s, ∀ x ∈ U k, g x ∈ U k) {x : V}
    (hx : x ∈ ⨆ k ∈ s, U k) : g x ∈ ⨆ k ∈ s, U k := by
  revert h x
  refine Finset.induction_on s ?_ ?_
  · intro h x hx
    have hx0 : x = 0 := by simpa using hx
    rw [hx0, map_zero]
    exact Submodule.zero_mem _
  · intro a s ha ih h x hx
    rw [Finset.iSup_insert] at hx ⊢
    obtain ⟨u, hu, v, hv, rfl⟩ := Submodule.mem_sup.1 hx
    rw [map_add]
    exact Submodule.add_mem_sup (h a (Finset.mem_insert_self a s) u hu)
      (ih (fun k hk => h k (Finset.mem_insert_of_mem hk)) hv)

private theorem eq_bot_of_separated_aux3 {m : ℕ} {U : Fin m → Submodule F V} {g : V ≃ₗ[F] V}
    {s : Finset (Fin m)} (hF : IsPlaneSystem Q U) (hmap : ∀ k ∈ s, ∀ x ∈ U k, g x ∈ U k)
    (hfree : ∀ k ∈ s, ∀ x ∈ U k, g x = x → x = 0) {y : V}
    (hy : y ∈ ⨆ k ∈ s, U k) (hfix : g y = y) : y = 0 := by
  revert hmap hfree y
  refine Finset.induction_on s ?_ ?_
  · intro hmap hfree y hy hfix
    simpa using hy
  · intro a s ha ih hmap hfree y hy hfix
    rw [Finset.iSup_insert] at hy
    obtain ⟨u, hu, v, hv, rfl⟩ := Submodule.mem_sup.1 hy
    rw [map_add] at hfix
    have hmap' : ∀ k ∈ s, ∀ x ∈ U k, g x ∈ U k :=
      fun k hk => hmap k (Finset.mem_insert_of_mem hk)
    have hfree' : ∀ k ∈ s, ∀ x ∈ U k, g x = x → x = 0 :=
      fun k hk => hfree k (Finset.mem_insert_of_mem hk)
    have hgu : g u ∈ U a := hmap a (Finset.mem_insert_self a s) u hu
    have hgv : g v ∈ (⨆ k ∈ s, U k) := eq_bot_of_separated_aux2 hmap' hv
    have hdisj : U a ⊓ (⨆ k ∈ s, U k) = ⊥ := disjoint_iff.1 (hF.disjoint_biSup ha)
    have heq : g u - u = v - g v := by
      rw [sub_eq_sub_iff_add_eq_add]
      exact hfix.trans (add_comm u v)
    have hgu_eq : g u = u := by
      have hmem : g u - u ∈ U a ⊓ (⨆ k ∈ s, U k) := by
        refine ⟨Submodule.sub_mem _ hgu hu, ?_⟩
        rw [heq]
        exact Submodule.sub_mem _ hv hgv
      rw [hdisj] at hmem
      exact sub_eq_zero.1 (by simpa using hmem)
    have hu0 : u = 0 := hfree a (Finset.mem_insert_self a s) u hu hgu_eq
    have hvfix : g v = v := by
      have h0 : v - g v = 0 := by rw [← heq, hgu_eq, sub_self]
      exact (sub_eq_zero.1 h0).symm
    have hv0 : v = 0 := ih hmap' hfree' hv hvfix
    simp [hu0, hv0]

private theorem eq_bot_of_separated_aux4 {m : ℕ} {U : Fin m → Submodule F V} {ρ : Fin m → ↥(orthDerived Q)}
    {T : Subgroup ↥(orthDerived Q)} (hF : IsPlaneFrame Q p U ρ T) {g : ↥(orthDerived Q)}
    (hg : g ∈ T) (k : Fin m) : ∀ x ∈ U k, (g : V ≃ₗ[F] V) x ∈ U k := by
  intro x hx
  obtain ⟨n, hn⟩ := hF.exists_pow_apply_eq hg k
  have hpow : ∀ m : ℕ, (((ρ k : V ≃ₗ[F] V) ^ m) x) ∈ U k := by
    intro m
    induction m with
    | zero => simpa using hx
    | succ m ih => rw [pow_succ', LinearEquiv.mul_apply]; exact hF.maps_to k _ ih
  rw [hn x hx]
  exact hpow n

private theorem eq_bot_of_separated_aux5 {m : ℕ} {U : Fin m → Submodule F V}
    (hF : IsPlaneSystem Q U) {W : Submodule F V} (hTS : ∀ x ∈ W, Q x = 0)
    {s : Finset (Fin m)} (hle : s.card ≤ 1) : W ⊓ (⨆ k ∈ s, U k) ≠ ⊥ → False := by
  intro hs
  by_cases hs0 : s = ∅
  · exact hs (by simp [hs0])
  · obtain ⟨a, ha⟩ := Finset.nonempty_iff_ne_empty.2 hs0
    have hsa : s = {a} := by
      refine Finset.Subset.antisymm ?_ (Finset.singleton_subset_iff.2 ha)
      intro b hb
      rw [Finset.mem_singleton]
      exact Finset.card_le_one.1 hle b hb a ha
    have hs' : W ⊓ U a ≠ ⊥ := by rw [hsa] at hs; simpa using hs
    obtain ⟨x, hx, hx0⟩ := (Submodule.ne_bot_iff (W ⊓ U a)).1 hs'
    exact hx0 (eq_zero_of_map_eq_zero_of_mem_plane hF a hx.2 (hTS x hx.1))

private theorem eq_bot_of_separated_aux6 {m : ℕ} {U : Fin m → Submodule F V}
    {ρ : Fin m → ↥(orthDerived Q)} {T : Subgroup ↥(orthDerived Q)}
    (hF : IsPlaneFrame Q p U ρ T) (hp : p.Prime) (hp2 : p ≠ 2)
    {G : Subgroup ↥(orthDerived Q)} (hGT : G ≤ T) {g : ↥(orthDerived Q)} (hgG : g ∈ G)
    {W : Submodule F V} (hinv : ∀ g ∈ G, ∀ x ∈ W, (g : V ≃ₗ[F] V) x ∈ W)
    {s S₁ S₂ : Finset (Fin m)} (hunion : S₁ ∪ S₂ = s) (hs : W ⊓ (⨆ k ∈ s, U k) ≠ ⊥)
    (hfix2 : ∀ k ∈ S₂, ∀ x ∈ U k, (g : V ≃ₗ[F] V) x = x)
    (hfree1 : ∀ k ∈ S₁, ∀ x ∈ U k, (g : V ≃ₗ[F] V) x = x → x = 0) :
    (W ⊓ (⨆ k ∈ S₂, U k) ≠ ⊥) ∨ (W ⊓ (⨆ k ∈ S₁, U k) ≠ ⊥) := by
  have hsup : (⨆ k ∈ s, U k) = (⨆ k ∈ S₂, U k) ⊔ (⨆ k ∈ S₁, U k) := by
    have h1 : (⨆ k ∈ s, U k) = (⨆ k ∈ S₁, U k) ⊔ (⨆ k ∈ S₂, U k) := by
      rw [← hunion, Finset.iSup_union]
    rw [h1, sup_comm]
  have hsXY : W ⊓ ((⨆ k ∈ S₂, U k) ⊔ (⨆ k ∈ S₁, U k)) ≠ ⊥ := by rw [← hsup]; exact hs
  have hgn : (g : V ≃ₗ[F] V) ^ p = 1 := by
    simpa using congrArg (fun z : ↥(orthDerived Q) => (z : V ≃ₗ[F] V))
      (hF.isElemAbelian.2 g (hGT hgG))
  have hsplit := inf_sup_le_sup_inf_of_fix (hp.odd_of_ne_two hp2) hgn
    (fun x hx => eq_bot_of_separated_aux1 (U := U) (g := (g : V ≃ₗ[F] V)) (s := S₂)
      (fun k hk => hfix2 k hk) hx)
    (fun y hy => eq_bot_of_separated_aux2 (U := U) (g := (g : V ≃ₗ[F] V)) (s := S₁)
      (fun k _ => eq_bot_of_separated_aux4 hF (hGT hgG) k) hy)
    (fun y hy hyfix => eq_bot_of_separated_aux3 (U := U) (g := (g : V ≃ₗ[F] V)) (s := S₁)
      hF.toIsPlaneSystem (fun k _ => eq_bot_of_separated_aux4 hF (hGT hgG) k)
      (fun k hk => hfree1 k hk) hy hyfix)
    (hinv g hgG)
  have hne : (W ⊓ (⨆ k ∈ S₂, U k)) ⊔ (W ⊓ (⨆ k ∈ S₁, U k)) ≠ ⊥ := by
    intro h
    exact hsXY (le_antisymm (hsplit.trans (le_of_eq h)) bot_le)
  by_contra h
  push Not at h
  exact hne (by simp [h.1, h.2])

private theorem eq_bot_of_separated_aux7 {m : ℕ} {U : Fin m → Submodule F V}
    {ρ : Fin m → ↥(orthDerived Q)} {T : Subgroup ↥(orthDerived Q)}
    (hF : IsPlaneFrame Q p U ρ T) (hp : p.Prime) (hp2 : p ≠ 2)
    {G : Subgroup ↥(orthDerived Q)} (hGT : G ≤ T)
    (hsep : ∀ a b : Fin m, a ≠ b → ∃ g ∈ G,
      ((∀ x ∈ U a, (g : V ≃ₗ[F] V) x = x) ↔ ¬ ∀ x ∈ U b, (g : V ≃ₗ[F] V) x = x))
    {W : Submodule F V} (hTS : ∀ x ∈ W, Q x = 0)
    (hinv : ∀ g ∈ G, ∀ x ∈ W, (g : V ≃ₗ[F] V) x ∈ W) (hWne : W ≠ ⊥) :
    ∀ s : Finset (Fin m), W ⊓ (⨆ k ∈ s, U k) ≠ ⊥ → False := by
  classical
  intro s
  refine s.strongInductionOn ?_
  intro s ih hs
  by_cases hle : s.card ≤ 1
  · exact eq_bot_of_separated_aux5 hF.toIsPlaneSystem hTS hle hs
  · push Not at hle
    obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.1 hle
    obtain ⟨g, hgG, hgsep⟩ := hsep a b hab
    let pfix : Fin m → Prop := fun k => ∀ x ∈ U k, (g : V ≃ₗ[F] V) x = x
    have hfree_or : ¬ pfix a ∨ ¬ pfix b := by
      by_contra h; push Not at h; exact hgsep.1 h.1 h.2
    have hfix_or : pfix a ∨ pfix b := by
      by_contra h; push Not at h; exact h.1 (hgsep.mpr h.2)
    let S₂ : Finset (Fin m) := s.filter pfix
    let S₁ : Finset (Fin m) := s.filter fun k => ¬ pfix k
    have hunion : S₁ ∪ S₂ = s := by
      dsimp [S₁, S₂]; rw [Finset.union_comm]; exact Finset.filter_union_filter_not_eq pfix s
    have hS₂sub : S₂ ⊂ s := by
      rw [Finset.ssubset_iff_of_subset (Finset.filter_subset pfix s)]
      rcases hfree_or with h | h
      · exact ⟨a, ha, fun hmem => h (Finset.mem_filter.1 hmem).2⟩
      · exact ⟨b, hb, fun hmem => h (Finset.mem_filter.1 hmem).2⟩
    have hS₁sub : S₁ ⊂ s := by
      rw [Finset.ssubset_iff_of_subset (Finset.filter_subset (fun k => ¬ pfix k) s)]
      rcases hfix_or with h | h
      · exact ⟨a, ha, fun hmem => (Finset.mem_filter.1 hmem).2 h⟩
      · exact ⟨b, hb, fun hmem => (Finset.mem_filter.1 hmem).2 h⟩
    rcases eq_bot_of_separated_aux6 hF hp hp2 hGT hgG hinv hunion hs
      (fun k hk => (Finset.mem_filter.1 hk).2)
      (fun k hk => (hF.apply_eq_or_eq_zero hp (hGT hgG) k).resolve_left
        (Finset.mem_filter.1 hk).2) with hWX | hWY
    · exact ih S₂ hS₂sub hWX
    · exact ih S₁ hS₁sub hWY

theorem eq_bot_of_separated {m : ℕ} {U : Fin m → Submodule F V} {ρ : Fin m → ↥(orthDerived Q)}
    {T : Subgroup ↥(orthDerived Q)} (hF : IsPlaneFrame Q p U ρ T) (hp : p.Prime) (hp2 : p ≠ 2)
    (htop : ⨆ k, U k = ⊤) {G : Subgroup ↥(orthDerived Q)} (hGT : G ≤ T)
    (hsep : ∀ a b : Fin m, a ≠ b → ∃ g ∈ G,
      ((∀ x ∈ U a, (g : V ≃ₗ[F] V) x = x) ↔ ¬ ∀ x ∈ U b, (g : V ≃ₗ[F] V) x = x))
    {W : Submodule F V} (hTS : ∀ x ∈ W, Q x = 0)
    (hinv : ∀ g ∈ G, ∀ x ∈ W, (g : V ≃ₗ[F] V) x ∈ W) : W = ⊥ := by
  classical
  by_contra hWne
  have htop' : (⨆ k ∈ (Finset.univ : Finset (Fin m)), U k) = ⊤ := by
    rw [show (⨆ k ∈ (Finset.univ : Finset (Fin m)), U k) = ⨆ k, U k from by simp, htop]
  refine eq_bot_of_separated_aux7 hF hp hp2 hGT hsep hTS hinv hWne Finset.univ ?_
  rw [htop', inf_top_eq]
  exact hWne

end CFSG.LocalAnalysis.GLTheoremA.T173M

end
