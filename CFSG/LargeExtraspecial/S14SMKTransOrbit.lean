module

public import CFSG.LargeExtraspecial.S14SMKTransCand
public import Certificates.Certificate21275
public import Certificates.Certificate21276

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.S14.SMK

open Subgroup Module QuadraticMap CFSG.Open CFSG.Fischer CFSG.SmithE
  CFSG.LargeExtraspecial.SMod20 CFSG.RankThree.OrthogonalInvolutions CFSG.Sporadic.Th
  CFSG.Sporadic.Th.Native CFSG.Fischer.Native

theorem invPairOK_spec {t r : Array ℕ} (h : invPairOK t r = true) {x : ℕ} (hx : x < 693) :
    t[x]! < 693 ∧ r[x]! < 693 ∧ r[t[x]!]! = x ∧ t[r[x]!]! = x := by
  have := (allIn_eq_true.1 h) x (Nat.zero_le _) hx
  simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at this
  exact ⟨this.1.1.1, this.1.1.2, this.1.2, this.2⟩

@[expose] def permOfTab (t r : Array ℕ) (h : invPairOK t r = true) : Equiv.Perm (Fin 693) where
  toFun x := ⟨t[x.val]!, (invPairOK_spec h x.2).1⟩
  invFun x := ⟨r[x.val]!, (invPairOK_spec h x.2).2.1⟩
  left_inv x := Fin.ext (invPairOK_spec h x.2).2.2.1
  right_inv x := Fin.ext (invPairOK_spec h x.2).2.2.2

@[expose] noncomputable def liftPerm (j : ℕ) : Equiv.Perm (Fin 693) :=
  if h : invPairOK (liftTab tvTabs j) (invTab (liftTab tvTabs j)) = true then
    permOfTab _ _ h else 1

theorem isTab_liftPerm {j : ℕ}
    (h : invPairOK (liftTab tvTabs j) (invTab (liftTab tvTabs j)) = true) :
    IsTab (liftTab tvTabs j) (liftPerm j) := by
  intro x
  rw [liftPerm, dite_eq_left h]
  rfl

theorem idTab_get (x : Fin 693) : idTab[x.val]! = x.val := by
  rw [idTab, getElem!_pos _ x.val (by simp), Array.getElem_ofFn]

theorem collI_eq : collI = collInvs collS2 (collMeet collS2) := by unfold collI; rfl


theorem mem_normalizer_of_conj_tvP {s : Equiv.Perm (Fin 693)}
    (hs : ∀ p, s * tvP p * s⁻¹ = tvP (s p)) :
    s ∈ normalizer (T46 : Set (Equiv.Perm (Fin 693))) := by
  have hs' : ∀ p, s⁻¹ * tvP p * s = tvP (s⁻¹ p) := by
    intro p
    have := hs (s⁻¹ p)
    rw [perm_apply_inv_self] at this
    rw [← this]
    group
  have key : ∀ t : Equiv.Perm (Fin 693), (∀ p, t * tvP p * t⁻¹ = tvP (t p)) →
      ∀ g ∈ T46, t * g * t⁻¹ ∈ T46 := by
    intro t ht g hg
    rw [T46_eq_closure] at hg ⊢
    induction hg using Subgroup.closure_induction with
    | mem x hx =>
      obtain ⟨p, rfl⟩ := hx
      rw [ht]
      exact Subgroup.subset_closure ⟨_, rfl⟩
    | one => simp
    | mul x y _ _ hx hy =>
      have := Subgroup.mul_mem _ hx hy
      rwa [show t * x * t⁻¹ * (t * y * t⁻¹) = t * (x * y) * t⁻¹ by group] at this
    | inv x _ hx =>
      have := Subgroup.inv_mem _ hx
      rwa [show (t * x * t⁻¹)⁻¹ = t * x⁻¹ * t⁻¹ by group] at this
  rw [mem_normalizer_iff]
  intro g
  constructor
  · exact key s hs g
  · intro hg
    have := key s⁻¹ (fun p => by rw [inv_inv]; exact hs' p) _ hg
    rwa [show s⁻¹ * (s * g * s⁻¹) * s⁻¹⁻¹ = g by group] at this

theorem conj_tvP_of_normOK {t : Array ℕ} {s : Equiv.Perm (Fin 693)} (hc : IsTab t s)
    (h : normOK tvTabs t = true) (p : Fin 693) : s * tvP p * s⁻¹ = tvP (s p) := by
  rw [mul_inv_eq_iff_eq_mul]
  ext x
  have h1 := (allIn_eq_true.1 ((allIn_eq_true.1 h) p.val (Nat.zero_le _) p.2)) x.val
    (Nat.zero_le _) x.2
  rw [beq_iff_eq, ap_tvTabs, hc, hc, hc, ap_tvTabs] at h1
  rw [Equiv.Perm.mul_apply, Equiv.Perm.mul_apply]
  exact h1



theorem orbitFacts :
    collI.size = 675 ∧ (∀ v < 675, collI[v]!.size = 21 ∧ ∀ k < 21, (collI[v]!)[k]! < 21) ∧
    (∀ j < 5, invPairOK (liftTab tvTabs j) (invTab (liftTab tvTabs j)) = true ∧
      normOK tvTabs (liftTab tvTabs j) = true ∧
      ∀ k < 21, ((uaFlags uaPts)[0]!)[(liftTab tvTabs j)[(uaPts[0]!)[k]!]!]! = true) ∧
    CFSG.SmithL6.K.Reach 675 34
      (fun v => ((List.range 4).map fun j => sArrT uaPts[0]! (liftTab tvTabs (j + 1))).any
        fun r => r == collI[v]!)
      (fun g u v => collComp (collComp (stabWords.map (stabSig tvTabs uaPts[0]!))[g]! collI[u]!)
        (stabWords.map fun w => stabSig tvTabs uaPts[0]! (w.2, w.1))[g]! == collI[v]!) := by
  obtain ⟨h1, h2, h3, h4⟩ := Certificates.certificate21275
  rw [← collI_eq] at h1 h2 h4
  refine ⟨h1, h2, fun j hj => ?_, h4⟩
  obtain ⟨ha, hb, hc⟩ := h3 j hj
  refine ⟨allIn_eq_true.2 fun x _ hx => ?_,
    allIn_eq_true.2 fun p _ hp => allIn_eq_true.2 fun x _ hx => ?_, hc⟩
  · obtain ⟨e1, e2, e3, e4⟩ := ha x hx
    simp only [e1, e2, e3, e4, decide_true, beq_self_eq_true, Bool.and_self]
  · rw [hb p hp x hx, beq_self_eq_true]

theorem liftPerm_isTab {j : ℕ} (hj : j < 5) : IsTab (liftTab tvTabs j) (liftPerm j) :=
  isTab_liftPerm (orbitFacts.2.2.1 j hj).1

theorem liftPerm_norm {j : ℕ} (hj : j < 5) :
    liftPerm j ∈ normalizer (T46 : Set (Equiv.Perm (Fin 693))) :=
  mem_normalizer_of_conj_tvP (conj_tvP_of_normOK (liftPerm_isTab hj)
    (orbitFacts.2.2.1 j hj).2.1)

theorem liftPerm_image {j : ℕ} (hj : j < 5) : ⇑(liftPerm j) '' wPlane 0 = wPlane 0 := by
  refine image_wPlane_eq (by norm_num) (by norm_num) fun k hk => ?_
  have h1 := (orbitFacts.2.2.1 j hj).2.2 k hk
  rw [← wPt_val (by norm_num) hk, liftPerm_isTab hj] at h1
  exact (uaFlags_get (by norm_num) _).1 h1

theorem liftPerm_zero : liftPerm 0 = 1 := by
  ext x
  have := liftPerm_isTab (j := 0) (by norm_num) x
  rw [show liftTab tvTabs 0 = idTab from rfl, idTab_get] at this
  rw [← this]
  rfl

theorem sArr_liftPerm {j : ℕ} (hj : j < 5) :
    sArr 0 (liftPerm j) = sArrT uaPts[0]! (liftTab tvTabs j) := by
  refine Array.ext (by rw [sArr_size, sArrT, Array.size_ofFn]) fun k hk _ => ?_
  have hk' : k < 21 := by rwa [sArr_size] at hk
  rw [sArr_getElem]
  simp only [sArrT, Array.getElem_ofFn]
  rw [← wPt_val (by norm_num) hk', liftPerm_isTab hj]

theorem stabElt_inv {g : ℕ} (hg : g < stabWords.size) :
    (stabElt g)⁻¹ = tvPn stabWords[g]!.2 * tvPn stabWords[g]!.1 := by
  have h1 : tvPn stabWords[g]!.1 * tvPn stabWords[g]!.1 = 1 := by
    rw [tvPn, dite_eq_left (stabWords_lt hg).1, tvP_mul_self]
  have h2 : tvPn stabWords[g]!.2 * tvPn stabWords[g]!.2 = 1 := by
    rw [tvPn, dite_eq_left (stabWords_lt hg).2, tvP_mul_self]
  rw [stabElt, mul_inv_rev, inv_eq_of_mul_eq_one_right h1, inv_eq_of_mul_eq_one_right h2]

theorem map_get! {α β : Type} [Inhabited α] [Inhabited β] (f : α → β) (a : Array α) {g : ℕ}
    (hg : g < a.size) : (a.map f)[g]! = f a[g]! := by
  rw [getElem!_pos (a.map f) g (by rw [Array.size_map]; exact hg), Array.getElem_map,
    getElem!_pos a g hg]

theorem stabAp_rev {g : ℕ} (hg : g < stabWords.size) (x : Fin 693) :
    stabAp tvTabs (stabWords[g]!.2, stabWords[g]!.1) x.val =
      ((stabElt g)⁻¹ x).val := by
  unfold stabAp
  rw [stabElt_inv hg, Equiv.Perm.mul_apply, ap_tvTabs_n (stabWords_lt hg).1,
    ap_tvTabs_n (stabWords_lt hg).2]

theorem sArr_stabElt_inv {g : ℕ} (hg : g < stabWords.size) :
    sArr 0 (stabElt g)⁻¹ = stabSig tvTabs uaPts[0]! (stabWords[g]!.2, stabWords[g]!.1) := by
  refine Array.ext (by rw [sArr_size, stabSig, Array.size_ofFn]) fun k hk _ => ?_
  have hk' : k < 21 := by rwa [sArr_size] at hk
  rw [sArr_getElem]
  simp only [stabSig, Array.getElem_ofFn]
  rw [← wPt_val (by norm_num) hk', stabAp_rev hg]

theorem orbit_reduce : ∀ v < 675, ∀ σ : Equiv.Perm (Fin 693), IsPolarAut σ →
    ⇑σ '' wPlane 0 = wPlane 0 → sArr 0 σ = collI[v]! →
    ∃ y ∈ PA 0, ∃ j, 1 ≤ j ∧ j < 5 ∧
      sArr 0 (y * σ * y⁻¹) = sArrT uaPts[0]! (liftTab tvTabs j) := by
  refine orbitFacts.2.2.2 (fun v => ∀ σ : Equiv.Perm (Fin 693), IsPolarAut σ →
    ⇑σ '' wPlane 0 = wPlane 0 → sArr 0 σ = collI[v]! →
    ∃ y ∈ PA 0, ∃ j, 1 ≤ j ∧ j < 5 ∧
      sArr 0 (y * σ * y⁻¹) = sArrT uaPts[0]! (liftTab tvTabs j)) ?_ ?_
  · intro v _ hr σ _ _ hσ
    obtain ⟨r, hr, hrv⟩ := List.any_eq_true.1 hr
    obtain ⟨j, hj, rfl⟩ := List.mem_map.1 hr
    rw [List.mem_range] at hj
    rw [beq_iff_eq] at hrv
    refine ⟨1, (PA 0).one_mem, j + 1, by omega, by omega, ?_⟩
    rw [one_mul, inv_one, mul_one, hσ, ← hrv]
  · intro g hg u hu v _ he hQ σ hσ hσW hσv
    replace hg : g < stabWords.size := hg
    rw [beq_iff_eq, map_get! _ _ hg, map_get! _ _ hg] at he
    have hsW := stabElt_image hg
    have hsW' := image_wPlane_inv hsW
    have hG : sArr 0 (stabElt g) = stabSig tvTabs uaPts[0]! stabWords[g]! := by
      rw [sArr_stabElt hg, map_get! _ _ hg]
    rw [← hG, ← sArr_stabElt_inv hg] at he
    have hHG : ∀ x < 21, (sArr 0 (stabElt g)⁻¹)[(sArr 0 (stabElt g))[x]!]! = x := by
      intro x hx
      have e := sArr_mul (by norm_num) (stabElt g)⁻¹ hsW
      rw [inv_mul_cancel, sArr_one (by norm_num)] at e
      rw [← collComp_get hx, ← e, collId_get hx]
    have hGlt : ∀ x < 21, (sArr 0 (stabElt g))[x]! < 21 :=
      fun x hx => (sArr_spec (by norm_num) hsW hx).1
    obtain ⟨hIs, hIlt⟩ := orbitFacts.2.1 u hu
    have hσsW : ⇑(σ * stabElt g) '' wPlane 0 = wPlane 0 := by
      rw [Equiv.Perm.coe_mul, Set.image_comp, hsW, hσW]
    have hσ₁ : sArr 0 ((stabElt g)⁻¹ * σ * stabElt g) = collI[u]! := by
      rw [mul_assoc, sArr_mul (by norm_num) _ hσsW, sArr_mul (by norm_num) _ hsW, hσv, ← he]
      refine array_ext_getElem! (collComp_size _ _) hIs fun k hk => ?_
      rw [collComp_get hk, collComp_get hk, collComp_get (hGlt k hk), hHG k hk,
        collComp_get hk, hHG _ (hIlt k hk)]
    have hσ₁P : IsPolarAut ((stabElt g)⁻¹ * σ * stabElt g) :=
      ((isPolarAut_of_mem (stabElt_mem_PA hg).1).inv.mul hσ).mul
        (isPolarAut_of_mem (stabElt_mem_PA hg).1)
    have hσ₁W : ⇑((stabElt g)⁻¹ * σ * stabElt g) '' wPlane 0 = wPlane 0 := by
      rw [Equiv.Perm.coe_mul, Equiv.Perm.coe_mul, Set.image_comp, Set.image_comp, hsW, hσW,
        hsW']
    obtain ⟨y, hy, j, hj1, hj5, hyj⟩ := hQ _ hσ₁P hσ₁W hσ₁
    refine ⟨y * (stabElt g)⁻¹, (PA 0).mul_mem hy ((PA 0).inv_mem (stabElt_mem_PA hg)), j, hj1,
      hj5, ?_⟩
    rw [show y * (stabElt g)⁻¹ * σ * (y * (stabElt g)⁻¹)⁻¹ =
      y * ((stabElt g)⁻¹ * σ * stabElt g) * y⁻¹ by group]
    exact hyj

theorem isTab_cand {j : ℕ} (hj : j < 5) (a : ℕ) :
    IsTab (candT tvTabs uaPts[0]! (liftTab tvTabs j) a) (uaPsi 0 a * liftPerm j) := by
  intro x
  rw [candT, getElem!_pos _ x.val (by simp), Array.getElem_ofFn]
  simp only
  rw [liftPerm_isTab hj x, Equiv.Perm.mul_apply, uaPsi_apply (by norm_num)]

theorem candConcl {j : ℕ} (hj : j < 5) {a : ℕ} (ha : a < 512) {A : SMod20.V ≃ₗ[ZMod 2] SMod20.V}
    {π : Equiv.Perm (Fin 693)} (h : InvHyp A π)
    (hc : IsTab (candT tvTabs uaPts[0]! (liftTab tvTabs j) a) π) : InvConcl A π :=
  Certificates.certificate21276 j hj a ha A π h hc

theorem invConcl_of_fix0 {A : SMod20.V ≃ₗ[ZMod 2] SMod20.V} {π : Equiv.Perm (Fin 693)} (h : InvHyp A π)
    (hW : ⇑π '' wPlane 0 = wPlane 0) : InvConcl A π := by
  have hπ : IsPolarAut π := isPolarAut_of_mem_normalizer h.norm
  by_cases hfix : ∀ p ∈ wPlane 0, π p = p
  · obtain ⟨a, ha, he⟩ := (mem_UA (by norm_num)).1 (mem_UA_of_fix h.norm (by norm_num) hfix)
    have htab : IsTab (candT tvTabs uaPts[0]! (liftTab tvTabs 0) a) π := by
      have := isTab_cand (j := 0) (by norm_num) a
      rwa [liftPerm_zero, mul_one, he] at this
    exact candConcl (by norm_num) ha h htab
  · push Not at hfix
    obtain ⟨p, hp, hpp⟩ := hfix
    have hI := sArr_mem_collI (by norm_num) hπ hW h.mul_self ⟨p, hp, hpp⟩
    obtain ⟨v, hv, hvI⟩ := exists_idx_collI hI
    rw [orbitFacts.1] at hv
    obtain ⟨y, hy, j, -, hj5, hyj⟩ := orbit_reduce v hv π hπ hW hvI.symm
    apply invConcl_of_conj ⟨y, hy.1⟩
    have h'' := h.conjT ⟨y, hy.1⟩
    have hyW : ⇑y '' wPlane 0 = wPlane 0 := mem_stabilizer_wPlane.1 hy.2
    have hW'' : ⇑(y * π * y⁻¹) '' wPlane 0 = wPlane 0 := by
      rw [Equiv.Perm.coe_mul, Equiv.Perm.coe_mul, Set.image_comp, Set.image_comp,
        image_wPlane_inv hyW, hW, hyW]
    have hagree := (sArr_eq_iff (by norm_num) hW'' (liftPerm_image hj5)).1
      (hyj.trans (sArr_liftPerm hj5).symm)
    have hρfix : ∀ q ∈ wPlane 0, (y * π * y⁻¹ * (liftPerm j)⁻¹) q = q := by
      intro q hq
      have hq' : (liftPerm j)⁻¹ q ∈ wPlane 0 := by
        rw [← image_wPlane_inv (liftPerm_image hj5)]
        exact ⟨q, hq, rfl⟩
      rw [Equiv.Perm.mul_apply, hagree _ hq', perm_apply_inv_self]
    have hρN : y * π * y⁻¹ * (liftPerm j)⁻¹ ∈ normalizer (T46 : Set (Equiv.Perm (Fin 693))) :=
      mul_mem h''.norm (inv_mem (liftPerm_norm hj5))
    obtain ⟨a, ha, he⟩ := (mem_UA (by norm_num)).1 (mem_UA_of_fix hρN (by norm_num) hρfix)
    have htab : IsTab (candT tvTabs uaPts[0]! (liftTab tvTabs j) a) (y * π * y⁻¹) := by
      have := isTab_cand hj5 a
      rwa [he, inv_mul_cancel_right] at this
    exact candConcl hj5 ha h'' htab

theorem involutionFacts : InvolutionFacts := by
  intro A π h
  obtain ⟨i, hi, hfix⟩ := h.exists_fixed_plane
  obtain ⟨g, hg, hgW⟩ := exists_image_wPlane_zero hi
  apply invConcl_of_conj ⟨g⁻¹, T46.inv_mem hg⟩
  refine invConcl_of_fix0 (h.conjT _) ?_
  show ⇑(g⁻¹ * π * g⁻¹⁻¹) '' wPlane 0 = wPlane 0
  rw [inv_inv, Equiv.Perm.coe_mul, Equiv.Perm.coe_mul, Set.image_comp, Set.image_comp, hgW, hfix,
    image_wPlane_inv hgW]

end CFSG.LargeExtraspecial.S14.SMK
