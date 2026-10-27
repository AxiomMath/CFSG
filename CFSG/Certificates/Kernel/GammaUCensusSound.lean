
module

public import Certificates.Data.Kernel.GammaUCensusK
public import CFSG.Certificates.Kernel.IdxFourOrbitSound
public import CFSG.GF2Type.Smith1979.GammaU.StepABase

public section

namespace CFSG.KC.GUC

open CFSG.KC.IF4C CFSG.KC.IF4R CFSG.GF2Type.Smith1979.GammaU

@[expose] def pGrp (gs : List Nat) : Subgroup (V12 ≃ₗ[ZMod 2] V12) :=
  Subgroup.closure {U | ∃ g ∈ gs, IsP U g}

@[expose] def lGrp (G n : Nat) : Subgroup (V12 ≃ₗ[ZMod 2] V12) :=
  Subgroup.closure {U | ∃ g < n, IsP U (look G g)}

theorem exists_subP : ∀ (H : List Nat), (∀ g ∈ H, ∃ U, IsP U g) →
    ∀ m, ∃ W ∈ pGrp H, IsP W (subP H m)
  | [], _, _ => ⟨1, Subgroup.one_mem _, IsP.one⟩
  | g :: H, hH, m => by
    obtain ⟨W, hW, hWp⟩ := exists_subP H (fun x hx => hH x (List.mem_cons_of_mem g hx)) (m / 2)
    have hle : pGrp H ≤ pGrp (g :: H) :=
      Subgroup.closure_mono fun U ⟨x, hx, hU⟩ => ⟨x, List.mem_cons_of_mem g hx, hU⟩
    change ∃ W ∈ pGrp (g :: H),
      IsP W (mulP (bif Nat.beq (m % 2) 1 then g else idP) (subP H (m / 2)))
    cases Nat.beq (m % 2) 1
    · exact ⟨1 * W, Subgroup.mul_mem _ (Subgroup.one_mem _) (hle hW), IsP.mul IsP.one hWp⟩
    · obtain ⟨U, hU⟩ := hH g List.mem_cons_self
      exact ⟨U * W, Subgroup.mul_mem _ (Subgroup.subset_closure ⟨g, List.mem_cons_self, hU⟩)
        (hle hW), IsP.mul hU hWp⟩

theorem cjOK_spec {v vi : Nat} {H : List Nat} : ∀ {gs ms : List Nat}, cjOK v vi H gs ms = true →
    ∀ g ∈ gs, ∃ m, mulP v (mulP g vi) = subP H m
  | [], _, _, g, hg => absurd hg List.not_mem_nil
  | x :: gs, [], h, _, _ => by simp [cjOK] at h
  | x :: gs, m :: ms, h, g, hg => by
    change (Nat.beq (mulP v (mulP x vi)) (subP H m) && cjOK v vi H gs ms) = true at h
    rw [Bool.and_eq_true, Nat.beq_eq] at h
    rcases List.mem_cons.1 hg with rfl | hg
    · exact ⟨m, h.1⟩
    · exact cjOK_spec h.2 g hg

theorem map_conj_le_of_cjOK {v vi : Nat} {H gs ms : List Nat} (h : cjOK v vi H gs ms = true)
    (hH : ∀ g ∈ H, ∃ U, IsP U g) {V : V12 ≃ₗ[ZMod 2] V12} (hV : IsP V v) (hVi : IsP V⁻¹ vi) :
    (pGrp gs).map (MulAut.conj V).toMonoidHom ≤ pGrp H := by
  rw [Subgroup.map_le_iff_le_comap]
  refine (Subgroup.closure_le _).2 fun U ⟨g, hg, hU⟩ => ?_
  obtain ⟨m, hm⟩ := cjOK_spec h g hg
  obtain ⟨W, hW, hWp⟩ := exists_subP H hH m
  have hc : IsP (V * U * V⁻¹) (subP H m) := by
    rw [← hm, mul_assoc]
    exact IsP.mul hV (IsP.mul hU hVi)
  change MulAut.conj V U ∈ pGrp H
  rw [MulAut.conj_apply, IsP.inj hc hWp]
  exact hW

theorem isP_inv_mul {A B C : V12 ≃ₗ[ZMod 2] V12} {a ai b bi c ci : Nat} (hA : IsP A a)
    (hB : IsP B b) (hC : IsP C c) (ha : mulP a ai = idP) (hb : mulP b bi = idP)
    (hc : mulP c ci = idP) :
    IsP (C⁻¹ * (A * B)) (mulP ci (mulP a b)) ∧ IsP (C⁻¹ * (A * B))⁻¹ (mulP bi (mulP ai c)) := by
  refine ⟨IsP.mul (IsP.inv hC hc) (IsP.mul hA hB), ?_⟩
  rw [mul_inv_rev, mul_inv_rev, inv_inv, mul_assoc]
  exact IsP.mul (IsP.inv hB hb) (IsP.mul (IsP.inv hA ha) hC)

theorem map_conj_le_iff (A B C : V12 ≃ₗ[ZMod 2] V12) (K M : Subgroup (V12 ≃ₗ[ZMod 2] V12)) :
    K.map (MulAut.conj (C⁻¹ * (A * B))).toMonoidHom ≤ M →
      (K.map (MulAut.conj B).toMonoidHom).map (MulAut.conj A).toMonoidHom ≤
        M.map (MulAut.conj C).toMonoidHom := by
  intro h x hx
  obtain ⟨y, ⟨k, hk, rfl⟩, rfl⟩ := hx
  have hm := h ⟨k, hk, rfl⟩
  refine ⟨(C⁻¹ * (A * B)) * k * (C⁻¹ * (A * B))⁻¹, hm, ?_⟩
  simp only [MonoidHom.coe_coe, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  group

theorem map_conj_le_of_edgeOK {CS CSI FT FTi FC CG X k p : Nat} {ms : List Nat}
    (h : edgeOK CS CSI FT FTi FC CG X k p ms = true)
    (hH : ∀ g ∈ five CG (fld FC X), ∃ U, IsP U g) {A B C : V12 ≃ₗ[ZMod 2] V12}
    (hA : IsP A (look CS k)) (hB : IsP B (look FT p)) (hC : IsP C (look FT X))
    (ha : mulP (look CS k) (look CSI k) = idP) (hb : mulP (look FT p) (look FTi p) = idP)
    (hc : mulP (look FT X) (look FTi X) = idP) :
    ((pGrp (five CG (fld FC p))).map (MulAut.conj B).toMonoidHom).map (MulAut.conj A).toMonoidHom ≤
      (pGrp (five CG (fld FC X))).map (MulAut.conj C).toMonoidHom := by
  obtain ⟨h1, h2⟩ := isP_inv_mul hA hB hC ha hb hc
  exact map_conj_le_iff A B C _ _ (map_conj_le_of_cjOK h hH h1 h2)

section Forest
variable {CS CSI FT FTi FC CG LB DP NC N : Nat}

theorem entOK_spec {X : Nat} {e : List Nat}
    (h : entOK CS CSI FT FTi FC CG LB DP NC N X e = true) :
    (e = [] ∧ fld LB X = X) ∨ ∃ k p ms, e = k :: p :: ms ∧ k < NC ∧ p < N ∧
      fld DP p < fld DP X ∧ fld LB p = fld LB X ∧ edgeOK CS CSI FT FTi FC CG X k p ms = true := by
  match e, h with
  | [], h => exact Or.inl ⟨rfl, by simpa [entOK] using h⟩
  | [k], h => simp [entOK] at h
  | k :: p :: ms, h =>
    change (Nat.blt k NC && Nat.blt p N && Nat.blt (fld DP p) (fld DP X) &&
      Nat.beq (fld LB p) (fld LB X) && edgeOK CS CSI FT FTi FC CG X k p ms) = true at h
    simp only [Bool.and_eq_true, Nat.blt_eq, Nat.beq_eq] at h
    obtain ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩ := h
    exact Or.inr ⟨k, p, ms, rfl, h1, h2, h3, h4, h5⟩

theorem entsOK_spec : ∀ {es : List (List Nat)} {X0 : Nat},
    entsOK CS CSI FT FTi FC CG LB DP NC N es X0 = true →
    ∀ i < es.length, entOK CS CSI FT FTi FC CG LB DP NC N (X0 + i) (es.getD i []) = true
  | [], _, _, i, hi => absurd hi (Nat.not_lt_zero i)
  | e :: es, X0, h, i, hi => by
    change (entOK CS CSI FT FTi FC CG LB DP NC N X0 e &&
      entsOK CS CSI FT FTi FC CG LB DP NC N es (Nat.succ X0)) = true at h
    rw [Bool.and_eq_true] at h
    cases i with
    | zero => exact h.1
    | succ i =>
      have := entsOK_spec h.2 i (by simpa using hi)
      rwa [Nat.succ_add, ← Nat.add_succ] at this

theorem entOK_of_blk {ED : List (List Nat)} {K : Nat} (hK : ED.length ≤ 16 * K)
    (h : ∀ c < K, entsOK CS CSI FT FTi FC CG LB DP NC N (takeN 16 (dropN (Nat.mul 16 c) ED))
      (Nat.mul 16 c) = true) :
    ∀ X < ED.length, entOK CS CSI FT FTi FC CG LB DP NC N X (ED.getD X []) = true := by
  intro X hX
  have hb := h (X / 16) (by omega)
  rw [takeN_eq, dropN_eq] at hb
  have hk : X % 16 < (List.take 16 (List.drop (Nat.mul 16 (X / 16)) ED)).length := by
    simp only [List.length_take, List.length_drop, Nat.mul_eq]
    omega
  have := entsOK_spec hb (X % 16) hk
  have hX' : Nat.mul 16 (X / 16) + X % 16 = X := by
    rw [Nat.mul_eq]
    exact Nat.div_add_mod X 16
  rw [hX'] at this
  simp only [List.getD_eq_getElem?_getD, List.getElem?_take, List.getElem?_drop] at this
  rw [if_pos (Nat.mod_lt X (by norm_num)), hX'] at this
  simpa only [List.getD_eq_getElem?_getD] using this

theorem forest_ind {ED : List (List Nat)}
    (hE : ∀ X < N, entOK CS CSI FT FTi FC CG LB DP NC N X (ED.getD X []) = true)
    (Q : Nat → Prop) (hroot : ∀ X < N, fld LB X = X → Q X)
    (hedge : ∀ X k p ms, X < N → k < NC → p < N → fld LB p = fld LB X →
      edgeOK CS CSI FT FTi FC CG X k p ms = true → Q p → Q X) :
    ∀ X < N, Q X := by
  suffices H : ∀ d, ∀ X < N, fld DP X = d → Q X from fun X hX => H _ X hX rfl
  intro d
  induction d using Nat.strong_induction_on with
  | _ d ih =>
    intro X hX hd
    rcases entOK_spec (hE X hX) with ⟨-, hr⟩ | ⟨k, p, ms, -, hk, hp, hdp, hl, he⟩
    · exact hroot X hX hr
    · exact hedge X k p ms hX hk hp hl he (ih _ (hd ▸ hdp) p hp rfl)

theorem labOK_spec {LB N AR : Nat} {OR : List Nat} (h : labOK LB N OR AR = true) :
    ∀ X < N, fld LB X ∈ OR ∨ fld LB X = AR := by
  intro X hX
  have := (allBelow_iff _ _).1 h X hX
  simpa only [Bool.or_eq_true, memN_iff, Nat.beq_eq] using this

end Forest

theorem cnOK_spec {CS CSI TH : Nat} {L : List Nat} : ∀ {CN : List (List Nat)} {k0 : Nat},
    cnOK CS CSI TH L CN k0 = true → ∀ i < CN.length, ∃ t ms, CN.getD i [] = t :: ms ∧
      cjOK (look CS (k0 + i)) (look CSI (k0 + i)) L L ms = true ∧
      ((t = 32 ∧ mulP (look CS (k0 + i)) TH = mulP TH (look CS (k0 + i))) ∨
        (t < 32 ∧ mulP (mulP (look CS (k0 + i)) TH) (mulP (look CSI (k0 + i)) TH) = subP L t))
  | [], _, _, i, hi => absurd hi (Nat.not_lt_zero i)
  | e :: CN, k0, h, i, hi => by
    have h' : cnOK CS CSI TH L (e :: CN) k0 =
      ((List.rec (motive := fun _ => Bool) false
        (fun t ms _ => cjOK (look CS k0) (look CSI k0) L L ms &&
          ((Nat.beq t 32 && Nat.beq (mulP (look CS k0) TH) (mulP TH (look CS k0))) ||
            (Nat.blt t 32 &&
              Nat.beq (mulP (mulP (look CS k0) TH) (mulP (look CSI k0) TH)) (subP L t)))) e) &&
        cnOK CS CSI TH L CN (Nat.succ k0)) := rfl
    rw [h', Bool.and_eq_true] at h
    cases i with
    | zero =>
      match e, h with
      | [], h => simp at h
      | t :: ms, h =>
        simp only [Bool.and_eq_true, Bool.or_eq_true, Nat.beq_eq, Nat.blt_eq] at h
        exact ⟨t, ms, rfl, h.1.1, by simpa using h.1.2⟩
    | succ i =>
      have := cnOK_spec h.2 i (by simpa using hi)
      rw [Nat.succ_add, ← Nat.add_succ] at this
      simpa using this

theorem candOK_spec {CG FT FTi FC TH i X G : Nat} (h : candOK CG FT FTi FC TH i X G = true) :
    (∀ l < 5, look G l = look CG (5 * i + l)) ∧
      (∀ l < 5, look G (5 + l) =
        mulP (look FT X) (mulP (look CG (5 * fld FC X + l)) (look FTi X))) ∧
      look G 10 = TH := by
  unfold candOK at h
  simp only [Bool.and_eq_true, allBelow_iff, Nat.beq_eq] at h
  exact ⟨fun l hl => h.1.1 l hl, fun l hl => h.1.2 l hl, h.2⟩

section Orbit
variable {G n VT PS N p : Nat} {E : List (List Nat)}

theorem treeOK_spec : ∀ {es : List (List Nat)} {j : Nat}, treeOK G n VT es j = true →
    ∀ i < es.length, (es.getD i []).getD 0 0 < j + i ∧ (es.getD i []).getD 1 0 < n ∧
      ap12 (look G ((es.getD i []).getD 1 0)) (fld VT ((es.getD i []).getD 0 0)) = fld VT (j + i)
  | [], _, _, i, hi => absurd hi (Nat.not_lt_zero i)
  | e :: es, j, h, i, hi => by
    change (Nat.blt (nthD 0 e 0) j && Nat.blt (nthD 0 e 1) n &&
      Nat.beq (ap12 (look G (nthD 0 e 1)) (fld VT (nthD 0 e 0))) (fld VT j) &&
        treeOK G n VT es (Nat.succ j)) = true at h
    simp only [Bool.and_eq_true, Nat.blt_eq, Nat.beq_eq, nthD_eq] at h
    obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h
    cases i with
    | zero => exact ⟨by simpa using h1, by simpa using h2, by simpa using h3⟩
    | succ i =>
      have := treeOK_spec h4 i (by simpa using hi)
      simp only [List.getD_cons_succ]
      rwa [Nat.succ_add, ← Nat.add_succ] at this

theorem orbOK_spec (h : orbOK G n VT PS N p E = true) :
    fld VT 0 = p ∧ E.length + 1 = N ∧ (∀ j < N, fld PS (fld VT j) = j) ∧
      (∀ i < E.length, (E.getD i []).getD 0 0 < 1 + i ∧ (E.getD i []).getD 1 0 < n ∧
        ap12 (look G ((E.getD i []).getD 1 0)) (fld VT ((E.getD i []).getD 0 0)) =
          fld VT (1 + i)) ∧
      ∀ j < N, ∀ g < n, fld PS (ap12 (look G g) (fld VT j)) < N ∧
        fld VT (fld PS (ap12 (look G g) (fld VT j))) = ap12 (look G g) (fld VT j) := by
  unfold orbOK at h
  simp only [Bool.and_eq_true, Nat.beq_eq, allBelow_iff, lenN_eq] at h
  obtain ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩ := h
  refine ⟨h1, by simpa using h2, h3, treeOK_spec h4, fun j hj g hg => ?_⟩
  have := (allBelow_iff _ _).1 (h5 j hj) g hg
  unfold inO at this
  simpa only [Bool.and_eq_true, Nat.blt_eq, Nat.beq_eq] using this

theorem mem_orbit_iff_of_orbOK (h : orbOK G n VT PS N p E = true)
    (hG : ∀ g < n, ∃ U, IsP U (look G g)) (x : V12) :
    x ∈ MulAction.orbit (lGrp G n) (vecOf p) ↔ ∃ j < N, vecOf (fld VT j) = x := by
  obtain ⟨h0, hlen, -, htree, hcl⟩ := orbOK_spec h
  constructor
  · rintro ⟨U, rfl⟩
    have hK : (U : V12 ≃ₗ[ZMod 2] V12) ∈ {W : V12 ≃ₗ[ZMod 2] V12 |
        ∃ j < N, vecOf (fld VT j) = W (vecOf p)} := by
      refine mem_of_closure (K := {W : V12 ≃ₗ[ZMod 2] V12 |
        ∃ j < N, vecOf (fld VT j) = W (vecOf p)}) ⟨0, by omega, by rw [h0]; try rfl⟩ ?_ U.2
      rintro s ⟨g, hg, hs⟩ W ⟨j, hj, hW⟩
      refine ⟨_, (hcl j hj g hg).1, ?_⟩
      rw [(hcl j hj g hg).2, LinearEquiv.mul_apply, ← hW, IsP.apply_code hs]
    obtain ⟨j, hj, hW⟩ := hK
    exact ⟨j, hj, hW⟩
  · rintro ⟨j, hj, rfl⟩
    induction j using Nat.strong_induction_on with
    | _ j ih =>
      cases j with
      | zero => rw [h0]; exact MulAction.mem_orbit_self _
      | succ i =>
        have hi : i < E.length := by omega
        obtain ⟨hq, hg, he⟩ := htree i hi
        obtain ⟨U, hU⟩ := hG _ hg
        obtain ⟨W, hW⟩ := ih ((E.getD i []).getD 0 0) (by omega) (by omega)
        have hUm : U ∈ lGrp G n := Subgroup.subset_closure ⟨_, hg, hU⟩
        refine ⟨⟨U, hUm⟩ * W, ?_⟩
        change W • vecOf p = vecOf (fld VT ((E.getD i []).getD 0 0)) at hW
        change (⟨U, hUm⟩ * W : lGrp G n) • vecOf p = vecOf (fld VT (i + 1))
        rw [mul_smul, hW]
        change U (vecOf (fld VT ((E.getD i []).getD 0 0))) = vecOf (fld VT (i + 1))
        rw [IsP.apply_code hU, he, Nat.add_comm 1 i]

theorem card_orbit_of_orbOK (h : orbOK G n VT PS N p E = true)
    (hG : ∀ g < n, ∃ U, IsP U (look G g)) :
    Nat.card (MulAction.orbit (lGrp G n) (vecOf p)) = N := by
  have hps := (orbOK_spec h).2.2.1
  let f : Fin N → MulAction.orbit (lGrp G n) (vecOf p) := fun j =>
    ⟨vecOf (fld VT j), (mem_orbit_iff_of_orbOK h hG _).2 ⟨j, j.2, rfl⟩⟩
  have hf : Function.Bijective f := by
    refine ⟨fun a b hab => ?_, fun ⟨x, hx⟩ => ?_⟩
    · have h1 : fld VT a = fld VT b :=
        vecOf_inj (CFSG.KC.IF4O.fld_lt _ _) (CFSG.KC.IF4O.fld_lt _ _) (congrArg Subtype.val hab)
      exact Fin.ext ((hps a a.2).symm.trans ((congrArg (fld PS) h1).trans (hps b b.2)))
    · obtain ⟨j, hj, rfl⟩ := (mem_orbit_iff_of_orbOK h hG x).1 hx
      exact ⟨⟨j, hj⟩, rfl⟩
  rw [← Nat.card_eq_of_bijective f hf, Nat.card_eq_fintype_card, Fintype.card_fin]

theorem dvd_card_of_orbOK (h : orbOK G n VT PS N p E = true)
    (hG : ∀ g < n, ∃ U, IsP U (look G g)) : N ∣ Nat.card (lGrp G n) := by
  have hd := Subgroup.index_dvd_card (MulAction.stabilizer (lGrp G n) (vecOf p))
  rw [MulAction.index_stabilizer] at hd
  rw [← card_orbit_of_orbOK h hG]
  rwa [Set.ncard_def] at hd

theorem card_ne_of_orbOK (h : orbOK G n VT PS 768 p E = true)
    (hG : ∀ g < n, ∃ U, IsP U (look G g)) : Nat.card (lGrp G n) ≠ 1152 := by
  intro hc
  have := dvd_card_of_orbOK h hG
  rw [hc] at this
  norm_num at this

end Orbit

end CFSG.KC.GUC

end
