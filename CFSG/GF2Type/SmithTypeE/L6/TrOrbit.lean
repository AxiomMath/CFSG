module

public import CFSG.GF2Type.SmithTypeE.L6.TrOuter
public import CFSG.GF2Type.SmithTypeE.L6.TrConj
public import CFSG.GF2Type.SmithTypeE.LMod.UaCollMain
public import Certificates.Certificate38680
public import Certificates.Certificate38681

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.GF2Type.SmithTypeE.L6

open Subgroup Module CFSG.SmithL6 CFSG.GF2Type.SmithTypeE.LMod
  CFSG.RankThree.OrthogonalInvolutions CFSG.LargeExtraspecial
open CFSG.SmithE (applyCols)
open scoped Matrix

attribute [local irreducible] stabGens elemGens planeImg meetCard dRoot tvIdxTab tvTab tvImg tvList
  planePtsArr flagArr wtArr maskArr annArr collL

theorem orbitFacts :
    collL.size = 651 ∧ (∀ g < 6, trGens[g]! < 1953 ∧ planeImg trGens[g]! 0 = 0) ∧
    (∀ j < 5, (∀ x < 1953, (trLift j)[x]! < 1953 ∧ (trLift j)[(trLift j)[x]!]! = x) ∧
      (∀ p < 1953, ∀ x < 1953,
        (trLift j)[(tvTab[p]!)[x]!]! = (tvTab[(trLift j)[p]!]!)[(trLift j)[x]!]!) ∧
      ∀ p ∈ planePtsArr[0]!, (flagArr[0]!)[(trLift j)[p]!]! = true) ∧
    K.Reach 651 6 (fun v => (trRootMats ()).any fun A => A == collL[v]!)
      (fun g u v => trConjC (trGens.map ucols)[g]! collL[v]! == collL[u]!) :=
  Certificates.certificate38680

theorem candFacts :
    (∀ j < 5, ∀ a < 512, (∀ x < 1953, (trCandT (trLift j) a)[(trCandT (trLift j) a)[x]!]! = x) →
      (∃ x < 1953, (trCandT (trLift j) a)[x]! ≠ x) →
      ∃ k < 5, ∃ G H : Matrix (Fin 6) (Fin 6) (ZMod 2), Hᵀ * G = 1 ∧
        ∀ x < 1953, ∀ y < 1953, tvVec y = G *ᵥ tvVec x → tvForm y = H *ᵥ tvForm x →
          tvVec (Certificates.trRepT k)[y]! = G *ᵥ tvVec (trCandT (trLift j) a)[x]! ∧
            tvForm (Certificates.trRepT k)[y]! = H *ᵥ tvForm (trCandT (trLift j) a)[x]!) ∧
    (∀ k < 5, ∃ P : List (ℕ × ℕ), P.length = 6 ∧
      (∀ p ∈ P, p.1 < 1395 ∧ p.2 < 1395 ∧
        ∀ x < 1953, inPlane p.1 x = true → inPlane p.2 (Certificates.trRepT k)[x]! = true) ∧
      (∀ m, 0 < m → m < 64 → trXorSel (P.map fun p => wt p.2 ^^^ wt p.1) m ≠ 0) ∧
      ((∃ i i', i < 1395 ∧ i' < 1395 ∧
          (∀ x < 1953, inPlane i x = true → inPlane i' (Certificates.trRepT k)[x]! = true) ∧
          fB (wt i') (wt i) = true) ∨
        (∃ i < 1395, ∀ x < 1953, inPlane i x = true → (Certificates.trRepT k)[x]! = x) ∨ k = 3)) ∧
    (∃ bs : List ℕ, bs.length ≤ 8 ∧ ∃ pl : List (ℕ × ℕ),
      (∀ q ∈ pl, q.1 < 1395 ∧ q.2 < 1395 ∧
        (∀ x < 1953, inPlane q.1 x = true → inPlane q.2 (Certificates.trRepT 3)[x]! = true) ∧
        ∃ m, trXorSel bs m = wt q.2 ^^^ wt q.1) ∧
      (∀ t < 20, ∃ m, trXorSel (pl.map fun q => wt q.1) m = 2 ^ t) ∧
      (trFixL (Certificates.trRepT 3)).length % 2 = 1 ∧
      (∃ q₀ ∈ trFixL (Certificates.trRepT 3), ∀ Q : ℕ → Prop, Q q₀ →
        (∀ q ∈ trFixL (Certificates.trRepT 3), ∀ u ∈ trFixL (Certificates.trRepT 3), Q u →
          Q (tvImg q u)) → ∀ v ∈ trFixL (Certificates.trRepT 3), Q v) ∧
      ∃ b6 : List ℕ, b6.length = 6 ∧ (∀ x ∈ b6, x ∈ trFixL (Certificates.trRepT 3)) ∧
        ∀ m, 0 < m → m < 64 → trXorSel (b6.map fun x => (tvPair x).1) m ≠ 0) :=
  Certificates.certificate38681

theorem arr_map_get! {α β : Type} [Inhabited α] [Inhabited β] (f : α → β) (a : Array α) {g : ℕ}
    (hg : g < a.size) : (a.map f)[g]! = f a[g]! := by
  rw [getElem!_pos (a.map f) g (by rw [Array.size_map]; exact hg), Array.getElem_map,
    getElem!_pos a g hg]

@[expose] def permOfInvTab (s : Array ℕ) (h : ∀ x < 1953, s[x]! < 1953 ∧ s[s[x]!]! = x) :
    Equiv.Perm (Fin 1953) where
  toFun x := ⟨s[x.val]!, (h x.1 x.2).1⟩
  invFun x := ⟨s[x.val]!, (h x.1 x.2).1⟩
  left_inv x := Fin.ext (h x.1 x.2).2
  right_inv x := Fin.ext (h x.1 x.2).2

open Classical in
@[expose] noncomputable def liftPerm (j : ℕ) : Equiv.Perm (Fin 1953) :=
  if h : ∀ x < 1953, (trLift j)[x]! < 1953 ∧ (trLift j)[(trLift j)[x]!]! = x then
    permOfInvTab (trLift j) h else 1

theorem isTab_liftPerm {j : ℕ} (h : ∀ x < 1953, (trLift j)[x]! < 1953 ∧
    (trLift j)[(trLift j)[x]!]! = x) : IsTab (trLift j) (liftPerm j) := by
  intro x
  unfold liftPerm
  split
  · rfl
  · rename_i hn
    exact absurd h hn

section Lifts


theorem liftPerm_isTab {j : ℕ} (hj : j < 5) : IsTab (trLift j) (liftPerm j) :=
  isTab_liftPerm (orbitFacts.2.2.1 j hj).1

theorem isTvAut_of_tab {s : Array ℕ} {σ : Equiv.Perm (Fin 1953)} (hs : IsTab s σ)
    (h : ∀ p < 1953, ∀ x < 1953, s[(tvTab[p]!)[x]!]! = (tvTab[s[p]!]!)[s[x]!]!) :
    IsTvAut σ := by
  refine isTvAut_of_apply fun k a => ?_
  apply Fin.ext
  rw [← hs, tvP_apply, ← tvTab_get k.2 a.2, h k.1 k.2 a.1 a.2, hs k, hs a, tvP_apply,
    tvTab_get (σ k).2 (σ a).2]

theorem liftPerm_isTvAut {j : ℕ} (hj : j < 5) : IsTvAut (liftPerm j) :=
  isTvAut_of_tab (liftPerm_isTab hj) (orbitFacts.2.2.1 j hj).2.1

theorem liftPerm_norm {j : ℕ} (hj : j < 5) :
    liftPerm j ∈ normalizer (T6 : Set (Equiv.Perm (Fin 1953))) :=
  (liftPerm_isTvAut hj).mem_normalizer

theorem liftPerm_image {j : ℕ} (hj : j < 5) : ⇑(liftPerm j) '' wPlane 0 = wPlane 0 := by
  refine image_wPlane_eq_of_subset (by norm_num) (by norm_num) fun p hp => ?_
  obtain ⟨k, hk, hkp⟩ := exists_planePtsArr_of_mem (by norm_num) hp
  have hm : p.val ∈ planePtsArr[0]! := by
    rw [← hkp, getElem!_pos _ k (by rw [planePtsArr_size (by norm_num)]; exact hk)]
    exact Array.getElem_mem _
  have h1 := (orbitFacts.2.2.1 j hj).2.2 _ hm
  rw [liftPerm_isTab hj p, flagArr_get (by norm_num) (liftPerm j p).2] at h1
  exact mem_wPlane.2 h1

theorem liftPerm_zero : liftPerm 0 = 1 := by
  ext x
  have := liftPerm_isTab (j := 0) (by norm_num) x
  rw [show trLift 0 = trIdT from rfl] at this
  rw [← this]
  simp [trIdT]

end Lifts

section Mats


theorem colsOf_eq_trColsT {s : Array ℕ} {π : Equiv.Perm (Fin 1953)} (hs : IsTab s π) :
    colsOf π = trColsT s := by
  unfold colsOf trColsT
  congr 1
  funext j
  rw [← hs (gen0 j.val), gen0_val j.2]

theorem colsOf_mul {π ρ : Equiv.Perm (Fin 1953)} (hπ : IsTvAut π)
    (hπW : ⇑π '' wPlane 0 = wPlane 0) (hρ : IsTvAut ρ) (hρW : ⇑ρ '' wPlane 0 = wPlane 0) :
    colsOf (π * ρ) = collMul (colsOf π) (colsOf ρ) := by
  have hmul : IsTvAut (π * ρ) := IsTvAut.mul hπ hρ
  have hmulW : ⇑(π * ρ) '' wPlane 0 = wPlane 0 := by
    rw [Equiv.Perm.coe_mul, Set.image_comp, hρW, hπW]
  apply Array.ext
  · simp [collMul, colsOf_size]
  · intro m hm1 hm2
    have hm : m < 9 := by simpa [colsOf_size] using hm1
    have h1 : (colsOf ρ)[m]! = applyCols (colsOf ρ) (2 ^ m) :=
      (applyCols_pow (by rw [colsOf_size]; exact hm)).symm
    have h3 : (colsOf (π * ρ))[m]! = applyCols (colsOf (π * ρ)) (2 ^ m) :=
      (applyCols_pow (by rw [colsOf_size]; exact hm)).symm
    have key : (collMul (colsOf π) (colsOf ρ))[m]! = (colsOf (π * ρ))[m]! := by
      rw [h3, act_mul hπ hπW hρ hρW, ← h1]
      simp [collMul, getElem!_pos, hm]
    exact (getElem!_pos _ m hm1).symm.trans (key.symm.trans (getElem!_pos _ m hm2))

theorem colsOf_tvP {p : ℕ} (hp : p < 1953) : colsOf (tvP ⟨p, hp⟩) = ucols p := by
  have hs : IsTab (trTvT p) (tvP ⟨p, hp⟩) := by
    intro x
    rw [trTvT, tvP_apply, tvTab_get hp x.2]
  rw [colsOf_eq_trColsT hs]
  unfold trColsT ucols trTvT
  rfl

theorem colsOf_mem_collL {π : Equiv.Perm (Fin 1953)} (hπ : IsTvAut π)
    (hW : ⇑π '' wPlane 0 = wPlane 0) (hsq : π * π = 1) (hne : ∃ p ∈ wPlane 0, π p ≠ p) :
    colsOf π ∈ collL := by
  refine mem_collL (colsOf_size π) (fun k hk => ?_) (fun m hm => ?_) ?_
  · rw [act_pt hπ hW hk]
    have hm : π (pt0 k) ∈ wPlane 0 := by
      rw [← hW]
      exact Set.mem_image_of_mem _ (pt0_mem hk)
    have hlt := pos0_lt_49_of_mem hm
    exact ptTab_true (uaFacts.uco_parts _ hlt).2 ⟨_, hlt, rfl⟩
  · have h1 : (colsOf π)[m]! = applyCols (colsOf π) (2 ^ m) :=
      (applyCols_pow (by rw [colsOf_size]; exact hm)).symm
    rw [h1, ← act_mul hπ hW hπ hW, hsq]
    exact act_one _ (two_pow_lt_512 hm)
  · by_contra hcon
    push Not at hcon
    obtain ⟨p, hp, hpne⟩ := hne
    refine hpne ((colsOf_eq_one_iff hπ hW).1 (fun m hm => ?_) p hp)
    rw [applyCols_pow (by rw [colsOf_size]; exact hm)]
    exact hcon m hm

end Mats

section Reduce


theorem orbit_reduce : ∀ v < 651, ∀ σ : Equiv.Perm (Fin 1953), IsTvAut σ →
    ⇑σ '' wPlane 0 = wPlane 0 → colsOf σ = collL[v]! →
    ∃ y ∈ PA 0, ∃ j, 1 ≤ j ∧ j < 5 ∧ colsOf (y * σ * y⁻¹) = trColsT (trLift j) := by
  obtain ⟨-, hgens, -, ht⟩ := orbitFacts
  intro v hv
  refine ht (fun v => ∀ σ : Equiv.Perm (Fin 1953), IsTvAut σ →
    ⇑σ '' wPlane 0 = wPlane 0 → colsOf σ = collL[v]! →
    ∃ y ∈ PA 0, ∃ j, 1 ≤ j ∧ j < 5 ∧ colsOf (y * σ * y⁻¹) = trColsT (trLift j)) ?_ ?_ v hv
  · intro v _ hr σ hσ hσW hσv
    obtain ⟨A, hA, hAv⟩ := List.any_eq_true.1 hr
    rw [beq_iff_eq] at hAv
    unfold trRootMats at hA
    obtain ⟨j, hj, rfl⟩ := List.mem_map.1 hA
    rw [List.mem_range] at hj
    refine ⟨1, (PA 0).one_mem, j + 1, by omega, by omega, ?_⟩
    rw [one_mul, inv_one, mul_one, hσv, ← hAv]
  · intro g hg u hu v hv he hQ σ hσ hσW hσv
    rw [beq_iff_eq, arr_map_get! ucols trGens (lt_of_lt_of_eq hg rfl)] at he
    obtain ⟨hp, hpW⟩ := hgens g hg
    obtain ⟨p, hpe⟩ : ∃ p, p = trGens[g]! := ⟨_, rfl⟩
    rw [← hpe] at he hp hpW
    have htT : tvP ⟨p, hp⟩ ∈ T6 := tvP_mem _
    have htW : ⇑(tvP ⟨p, hp⟩) '' wPlane 0 = wPlane 0 := by
      rw [image_wPlane_tvP (by norm_num)]
      simp only [hpW]
    have htPA : tvP ⟨p, hp⟩ ∈ PA 0 := mem_PA.2 ⟨htT, htW⟩
    have htv : IsTvAut (tvP ⟨p, hp⟩) := isTvAut_of_mem htT
    have htvi : IsTvAut (tvP ⟨p, hp⟩)⁻¹ := htv.inv
    have htWi : ⇑(tvP ⟨p, hp⟩)⁻¹ '' wPlane 0 = wPlane 0 := image_wPlane_inv htW
    have hσ1 : IsTvAut (tvP ⟨p, hp⟩ * σ * (tvP ⟨p, hp⟩)⁻¹) := (htv.mul hσ).mul htvi
    have hσ1W : ⇑(tvP ⟨p, hp⟩ * σ * (tvP ⟨p, hp⟩)⁻¹) '' wPlane 0 = wPlane 0 := by
      rw [Equiv.Perm.coe_mul, Equiv.Perm.coe_mul, Set.image_comp, Set.image_comp, htWi, hσW, htW]
    have hcols : colsOf (tvP ⟨p, hp⟩ * σ * (tvP ⟨p, hp⟩)⁻¹) = collL[u]! := by
      rw [colsOf_mul (htv.mul hσ) (by rw [Equiv.Perm.coe_mul, Set.image_comp, hσW, htW]) htvi htWi,
        colsOf_mul htv htW hσ hσW, tvP_inv, colsOf_tvP hp, hσv]
      exact he
    obtain ⟨y, hy, j, hj1, hj5, hyj⟩ := hQ _ hσ1 hσ1W hcols
    refine ⟨y * tvP ⟨p, hp⟩, (PA 0).mul_mem hy htPA, j, hj1, hj5, ?_⟩
    rw [show y * tvP ⟨p, hp⟩ * σ * (y * tvP ⟨p, hp⟩)⁻¹ =
      y * (tvP ⟨p, hp⟩ * σ * (tvP ⟨p, hp⟩)⁻¹) * y⁻¹ by group]
    exact hyj

end Reduce

section Cand

variable
  {A : CFSG.LargeExtraspecial.SMod20.V ≃ₗ[ZMod 2] CFSG.LargeExtraspecial.SMod20.V}
  {π : Equiv.Perm (Fin 1953)}

theorem isTab_cand {j : ℕ} (hj : j < 5) (a : ℕ) :
    IsTab (trCandT (trLift j) a) (psi0 a * liftPerm j) := by
  intro x
  rw [trCandT, getElem!_pos _ x.val (by simp), Array.getElem_ofFn]
  simp only
  rw [liftPerm_isTab hj x, Equiv.Perm.mul_apply, psi0_apply]

theorem invConcl_of_cand (h : InvHyp A π) {j : ℕ} (hj : j < 5) {a : ℕ} (ha : a < 512)
    (htab : IsTab (trCandT (trLift j) a) π) : InvConcl A π := by
  obtain ⟨hred, hrep, hout⟩ := candFacts
  have hinvo : ∀ x < 1953, (trCandT (trLift j) a)[(trCandT (trLift j) a)[x]!]! = x := by
    intro x hx
    rw [htab ⟨x, hx⟩, htab (π ⟨x, hx⟩), ← Equiv.Perm.mul_apply, h.mul_self]
    rfl
  have hne : ∃ x < 1953, (trCandT (trLift j) a)[x]! ≠ x := by
    by_contra hcon
    push Not at hcon
    apply h.ne_one
    ext x
    rw [← htab x, hcon x.val x.2]
    rfl
  obtain ⟨k, hk, G, H, hHG, hconj⟩ := hred j hj a ha hinvo hne
  have hr : (Certificates.trRep k).1 < 5 := by interval_cases k <;> decide
  have htabR : IsTab (Certificates.trRepT k)
      (psi0 (Certificates.trRep k).2 * liftPerm (Certificates.trRep k).1) :=
    isTab_cand hr (Certificates.trRep k).2
  obtain ⟨g, hg, hgπ⟩ := exists_conj_of_mat (π := π)
    (π' := psi0 (Certificates.trRep k).2 * liftPerm (Certificates.trRep k).1) hHG
    (fun x y hv hf => by
      have e := hconj x.val x.2 y.val y.2 hv hf
      rw [htabR y, htab x] at e
      exact e)
  apply invConcl_of_conj ⟨g, hg⟩
  have h' := h.conjT ⟨g, hg⟩
  have e : ((⟨g, hg⟩ : T6) : Equiv.Perm (Fin 1953)) * π *
      ((⟨g, hg⟩ : T6) : Equiv.Perm (Fin 1953))⁻¹ =
      psi0 (Certificates.trRep k).2 * liftPerm (Certificates.trRep k).1 := hgπ
  rw [e] at h' ⊢
  obtain ⟨P, hPl, hP, hind, hbr⟩ := hrep k hk
  refine invConcl_of_rep h' htabR hPl hP hind ?_
  rcases hbr with hb | hb | rfl
  · exact Or.inl hb
  · exact Or.inr (Or.inl hb)
  · obtain ⟨bs, hbs, pl, hpl, hum, hodd, horb, b6, hb6l, hb6, hind6⟩ := hout
    exact Or.inr (Or.inr (fp_of_outer h' htabR hbs hpl hum hodd horb hb6l hb6 hind6))

theorem invConcl_of_fix0 (h : InvHyp A π) (hW : ⇑π '' wPlane 0 = wPlane 0) : InvConcl A π := by
  have hπ : IsTvAut π := isTvAut_of_mem_normalizer h.norm
  by_cases hfix : ∀ p ∈ wPlane 0, π p = p
  · obtain ⟨a, ha, he⟩ := mem_UA_zero.1 (mem_UA_of_fix h.norm (by norm_num) hfix)
    have htab : IsTab (trCandT (trLift 0) a) π := by
      have := isTab_cand (j := 0) (by norm_num) a
      rwa [liftPerm_zero, mul_one, he] at this
    exact invConcl_of_cand h (by norm_num) ha htab
  · push Not at hfix
    obtain ⟨p, hp, hpp⟩ := hfix
    have hmem : colsOf π ∈ collL := colsOf_mem_collL hπ hW h.mul_self ⟨p, hp, hpp⟩
    obtain ⟨v, hv, hvI⟩ := Array.mem_iff_getElem.1 hmem
    rw [orbitFacts.1] at hv
    have hvI' : colsOf π = collL[v]! := by rw [getElem!_pos _ v (by rw [orbitFacts.1]; exact hv)]; exact hvI.symm
    obtain ⟨y, hy, j, -, hj5, hyj⟩ := orbit_reduce v hv π hπ hW hvI'
    apply invConcl_of_conj ⟨y, (mem_PA.1 hy).1⟩
    have h'' := h.conjT ⟨y, (mem_PA.1 hy).1⟩
    have hyW : ⇑y '' wPlane 0 = wPlane 0 := (mem_PA.1 hy).2
    have hyT : IsTvAut y := isTvAut_of_mem (mem_PA.1 hy).1
    have hπ'' : IsTvAut (y * π * y⁻¹) := (hyT.mul hπ).mul hyT.inv
    have hW'' : ⇑(y * π * y⁻¹) '' wPlane 0 = wPlane 0 := by
      rw [Equiv.Perm.coe_mul, Equiv.Perm.coe_mul, Set.image_comp, Set.image_comp,
        image_wPlane_inv hyW, hW, hyW]
    have hagree := apply_eq_of_colsOf_eq hπ'' hW'' (liftPerm_isTvAut hj5) (liftPerm_image hj5)
      (fun m _ => by rw [hyj, colsOf_eq_trColsT (liftPerm_isTab hj5)])
    have hρfix : ∀ q ∈ wPlane 0, (y * π * y⁻¹ * (liftPerm j)⁻¹) q = q := by
      intro q hq
      have hq' : (liftPerm j)⁻¹ q ∈ wPlane 0 := by
        rw [← image_wPlane_inv (liftPerm_image hj5)]
        exact ⟨q, hq, rfl⟩
      rw [Equiv.Perm.mul_apply, hagree _ hq', perm_apply_inv_self]
    have hρN : y * π * y⁻¹ * (liftPerm j)⁻¹ ∈ normalizer (T6 : Set (Equiv.Perm (Fin 1953))) :=
      mul_mem h''.norm (inv_mem (liftPerm_norm hj5))
    obtain ⟨a, ha, he⟩ := mem_UA_zero.1 (mem_UA_of_fix hρN (by norm_num) hρfix)
    have htab : IsTab (trCandT (trLift j) a) (y * π * y⁻¹) := by
      have := isTab_cand hj5 a
      rwa [he, inv_mul_cancel_right] at this
    exact invConcl_of_cand h'' hj5 ha htab

theorem involutionFacts : InvolutionFacts := by
  intro A π h
  obtain ⟨i, hi, hfix⟩ := h.exists_fixed_plane
  obtain ⟨g, hg, hgW⟩ := exists_image_wPlane_zero hi
  apply invConcl_of_conj ⟨g⁻¹, T6.inv_mem hg⟩
  refine invConcl_of_fix0 (h.conjT _) ?_
  show ⇑(g⁻¹ * π * g⁻¹⁻¹) '' wPlane 0 = wPlane 0
  rw [inv_inv, Equiv.Perm.coe_mul, Equiv.Perm.coe_mul, Set.image_comp, Set.image_comp, hgW, hfix,
    image_wPlane_inv hgW]

end Cand

end CFSG.GF2Type.SmithTypeE.L6
