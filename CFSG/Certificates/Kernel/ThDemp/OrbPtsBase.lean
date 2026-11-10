
module

public import CFSG.Certificates.Kernel.ThDemp.OrbStab

@[expose] public section

namespace CFSG.Certificates.ThDemp.Pts

open MulAction CFSG.KC.Th CFSG.KC.Th.BigS CFSG.KC.Th.Spec CFSG.KC.ThDemp
  CFSG.Certificates.ThDemp.Act CFSG.Certificates.ThDemp.Lanes CFSG.Certificates.ThDemp.Batches
  CFSG.Certificates.ThDemp.Key CFSG.Certificates.ThDemp.Stab CFSG.Certificates.ThDemp.Rows
  CFSG.KC.Loop

set_option exponentiation.threshold 2000

local notation "𝕄" g:max =>
  ((Subtype.val g : GL (Fin 248) (ZMod 2)) : Matrix (Fin 248) (Fin 248) (ZMod 2))

variable {J : Subgroup (GL (Fin 248) (ZMod 2))} {D : DempData} {O : OrbData}

def RegJ (D : DempData) (J : Subgroup (GL (Fin 248) (ZMod 2))) : Prop :=
  ∀ r, 0 < r → r < D.nreg → ∃ x : J, 𝕄 x = pkMat (D.RB r)

theorem mem_lgetL : ∀ (l : List (List ℕ)) (i : ℕ) (r : ℕ), r ∈ lgetL l i → ∃ w ∈ l, r ∈ w
  | [], i, r, h => by
    change r ∈ ([] : List ℕ) at h
    simp at h
  | w :: l, 0, r, h => ⟨w, by simp, h⟩
  | w :: l, i + 1, r, h => by
    obtain ⟨w', hw', hr⟩ := mem_lgetL l i r h
    exact ⟨w', by simp [hw'], hr⟩

theorem regBelow_sound {a r : ℕ} (h : regBelow a r = true) : 0 < a ∧ a < r := by
  unfold regBelow at h
  obtain ⟨h1, h2⟩ := Unfold.andB_split h
  exact ⟨Nat.blt_eq.mp h1, Nat.blt_eq.mp h2⟩

theorem word_sound (n : ℕ) : ∀ w : List ℕ, List.rec (motive := fun _ => Bool) true
    (fun r _ ih2 => andB (regBelow r n) ih2) w = true → ∀ r ∈ w, 0 < r ∧ r < n
  | [], _ => by simp
  | a :: t, h => by
    obtain ⟨h3, h4⟩ := Unfold.andB_split h
    intro r hr
    rcases List.mem_cons.mp hr with rfl | hr
    · exact regBelow_sound h3
    · exact word_sound n t h4 r hr

theorem words_sound (n : ℕ) : ∀ ws : List (List ℕ), List.rec (motive := fun _ => Bool) true
    (fun w _ ih => andB (List.rec (motive := fun _ => Bool) true
      (fun r _ ih2 => andB (regBelow r n) ih2) w) ih) ws = true →
    ∀ w ∈ ws, ∀ r ∈ w, 0 < r ∧ r < n
  | [], _ => by simp
  | a :: t, h => by
    obtain ⟨h3, h4⟩ := Unfold.andB_split h
    intro w hw
    rcases List.mem_cons.mp hw with rfl | hw
    · exact word_sound n w h3
    · exact words_sound n t h4 w hw

theorem wordsChk_sound (h : wordsChk D O = true) : ∀ w ∈ O.words, ∀ r ∈ w, 0 < r ∧ r < D.nreg :=
  words_sound D.nreg O.words h

theorem exists_word (hJ : RegJ D J) : ∀ w : List ℕ, (∀ r ∈ w, 0 < r ∧ r < D.nreg) →
    ∃ g : J, 𝕄 g = (w.map fun r => pkMat (D.RB r)).prod
  | [], _ => ⟨1, by simp⟩
  | r :: w, h => by
    obtain ⟨x, hx⟩ := hJ r (h r (by simp)).1 (h r (by simp)).2
    obtain ⟨g, hg⟩ := exists_word hJ w (fun r' hr' => h r' (by simp [hr']))
    exact ⟨x * g, by rw [mat_mul', hx, hg, List.map_cons, List.prod_cons]⟩

theorem wordR_lt (hrm : D.rm = 2 ^ 248 - 1) : ∀ (w : List ℕ) (X : ℕ), X < 2 ^ 1280 →
    wordR D (cR 5) X w < 2 ^ 1280
  | [], X, h => h
  | r :: w, X, _ => by
    have e : wordR D (cR 5) X (r :: w) = wordR D (cR 5) (mulB (cR 5) D.rm X (D.RB r)) w := by
      change strictN _ _ = _
      rw [strictN_eq]
      rfl
    rw [e]
    refine wordR_lt hrm w _ ?_
    rw [hrm]
    exact mulB_lt 5 _ _

theorem pt_lt (hrm : D.rm = 2 ^ 248 - 1) {i : ℕ} (hw : lgetL O.words i ≠ []) :
    pt D O i < 2 ^ 1280 := by
  unfold pt
  obtain ⟨r, w, e⟩ := List.exists_cons_of_ne_nil hw
  rw [e]
  have e2 : wordR D (cR 5) (U0 D) (r :: w) = wordR D (cR 5) (mulB (cR 5) D.rm (U0 D) (D.RB r)) w := by
    change strictN _ _ = _
    rw [strictN_eq]
    rfl
  rw [e2]
  refine wordR_lt hrm w _ ?_
  rw [hrm]
  exact mulB_lt 5 _ _

section


end

theorem inv_mapsTo {X : Type*} [MulAction J X] {S : Set X} (hS : S.Finite) {x : J}
    (h : ∀ W ∈ S, x • W ∈ S) : ∀ W ∈ S, x⁻¹ • W ∈ S := by
  have hb := (hS.injOn_iff_bijOn_of_mapsTo (f := fun W => x • W) h).mp
    (fun a _ b _ e => smul_left_cancel x e)
  intro W hW
  obtain ⟨W', hW', e⟩ := hb.surjOn hW
  rw [← e]
  change x⁻¹ • x • W' ∈ S
  rw [inv_smul_smul]
  exact hW'

theorem keyAt_keys248 (hrm : D.rm = 2 ^ 248 - 1) (S : ℕ) {k : ℕ} (hk : k < 248) :
    keyAt (keys248 D S) k = keyL (2 ^ 248 - 1) (ptAt S k) := by
  rw [keyAt_eq, ptAt_eq]
  unfold keys248
  rw [hrm, lane64_packD (lt_of_lt_of_le hk (by norm_num)), lane_keyB (by norm_num) hk]
  exact Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le (keyL_lt _) (by norm_num))

theorem ptAt_mulB (hrm : D.rm = 2 ^ 248 - 1) (S X : ℕ) {k : ℕ} (hk : k < 248) :
    ptAt (mulB (cR 1240) D.rm S X) k = mulB (rep 1 256 5) (2 ^ 248 - 1) (ptAt S k) X := by
  rw [ptAt_eq, ptAt_eq, hrm, cR_eq]
  exact lane_mulB (m := 248) hk S X

namespace Ctx

variable (C : Ctx D O J) (hrm : D.rm = 2 ^ 248 - 1) (h : orbChk D O = true)
  (h9 : pt D O 9 < 2 ^ 1280) (hP9 : LIL (rowsOf (2 ^ 248 - 1) (pt D O 9)))
include hrm h h9 hP9

theorem orbit_nine :
    orbit C.Dg (sp (pt D O 9)) = (fun k => sp (ptAt (qStack D O) k)) '' ↑(Finset.range 248) ∧
    (∀ k < 248, LIL (rowsOf (2 ^ 248 - 1) (ptAt (qStack D O) k))) := by
  obtain ⟨-, h0, hpar, hedge, -, -⟩ := Facts.orbChk_sound D O h hrm h9
  have hgen : ∀ g < 2, ∃ d : J, d ∈ C.Dg ∧ 𝕄 d = pkMat (gen D g) := fun g hg => C.exists_gen hg
  have hQ' : ∀ k < 248, LIL (rowsOf (2 ^ 248 - 1) (ptAt (qStack D O) k)) ∧
      sp (ptAt (qStack D O) k) ∈ orbit C.Dg (sp (pt D O 9)) := by
    intro k
    induction k using Nat.strong_induction_on with
    | _ k ih =>
      intro hk
      rcases Nat.eq_zero_or_pos k with rfl | hk0
      · rw [h0]
        exact ⟨hP9, mem_orbit_self _⟩
      · obtain ⟨p, hp, g, hg, e⟩ := hpar k hk0 hk
        obtain ⟨d, hd, hdm⟩ := hgen g hg
        obtain ⟨ih1, ih2⟩ := ih p hp (by omega)
        obtain ⟨m, hm⟩ := mem_orbit_iff.mp ih2
        rw [e, hrm, cR_eq]
        refine ⟨lil_mulB (M' := 𝕄 d⁻¹) (by rw [← hdm]; exact mat_mul_inv d) ih1, ?_⟩
        refine mem_orbit_iff.mpr ⟨(⟨d, hd⟩ : C.Dg)⁻¹ * m, ?_⟩
        rw [mul_smul, hm, sp_mulB, ← hdm, ← inv_smul_eq]
        rfl
  refine ⟨Set.Subset.antisymm ?_ ?_, fun k hk => (hQ' k hk).1⟩
  · set S := (fun k => sp (ptAt (qStack D O) k)) '' ↑(Finset.range 248) with hS
    have hfin : S.Finite := Set.Finite.image _ (Finset.finite_toSet _)
    have hgS : ∀ g < 2, ∀ d : J, 𝕄 d = pkMat (gen D g) → ∀ W ∈ S, d⁻¹ • W ∈ S := by
      rintro g hg d hdm W ⟨q, hq, rfl⟩
      have hq' : q < 248 := Finset.mem_range.mp hq
      obtain ⟨j, hj, G, hG⟩ := hedge q hq' g hg
      rw [hrm, cR_eq] at hG
      have hl := lil_mulB (P := ptAt (qStack D O) q) (N := gen D g) (M' := 𝕄 d⁻¹)
        (by rw [← hdm]; exact mat_mul_inv d) (hQ' q hq').1
      have e := sp_eq_of_combChk hG hl (hQ' j hj).1
      refine ⟨j, Finset.mem_range.mpr hj, ?_⟩
      change sp (ptAt (qStack D O) j) = d⁻¹ • sp (ptAt (qStack D O) q)
      rw [inv_smul_eq, hdm, ← sp_mulB, e]
    have hgS' : ∀ g < 2, ∀ d : J, 𝕄 d = pkMat (gen D g) → ∀ W ∈ S, d • W ∈ S := by
      intro g hg d hdm
      have := inv_mapsTo hfin (hgS g hg d hdm)
      simpa only [inv_inv] using this
    have key : ∀ x ∈ C.Dg, ∀ W ∈ S, x • W ∈ S := by
      intro x hx
      induction hx using Subgroup.closure_induction with
      | mem x hx =>
        rcases hx with rfl | hx
        · exact hgS' 0 (by omega) _ C.md₀
        · rw [Set.mem_singleton_iff.mp hx]
          exact hgS' 1 (by omega) _ C.md₁
      | one => exact fun W hW => by rw [one_smul]; exact hW
      | mul x y _ _ hx hy => exact fun W hW => by rw [mul_smul]; exact hx _ (hy W hW)
      | inv x _ hx => exact inv_mapsTo hfin hx
    rintro W ⟨⟨x, hx⟩, rfl⟩
    have h0S : sp (pt D O 9) ∈ S := ⟨0, Finset.mem_range.mpr (by omega), by
      change sp (ptAt (qStack D O) 0) = _
      rw [h0]⟩
    exact key x hx _ h0S
  · rintro W ⟨k, hk, rfl⟩
    exact (hQ' k (Finset.mem_range.mp hk)).2

theorem ncard_orbit_nine : (orbit C.Dg (sp (pt D O 9))).ncard = 248 := by
  obtain ⟨-, -, -, -, hdist, -⟩ := Facts.orbChk_sound D O h hrm h9
  obtain ⟨he, hl⟩ := orbit_nine C hrm h h9 hP9
  rw [he, Set.InjOn.ncard_image, Set.ncard_coe_finset, Finset.card_range]
  intro k hk k' hk' e
  have hk1 := Finset.mem_range.mp hk
  have hk2 := Finset.mem_range.mp hk'
  refine hdist k hk1 k' hk2 ?_
  rw [keyAt_keys248 hrm _ hk1, keyAt_keys248 hrm _ hk2]
  exact Act.keyL_eq (hl k hk1) (hl k' hk2) e

theorem ncard_fix_nine (x : C.Dg) (hx : 𝕄 (x : J) = pkMat (chainEl D O.x5)) :
    {q ∈ orbit C.Dg (sp (pt D O 9)) | x • q = q}.ncard ≤ 3 := by
  classical
  obtain ⟨hfx, -, -, -, -, hfix⟩ := Facts.orbChk_sound D O h hrm h9
  obtain ⟨he, hl⟩ := orbit_nine C hrm h h9 hP9
  have hsub : {q ∈ orbit C.Dg (sp (pt D O 9)) | x • q = q} ⊆
      (fun k => sp (ptAt (qStack D O) k)) '' ↑O.fx5.toFinset := by
    rintro q ⟨hq, hxq⟩
    rw [he] at hq
    obtain ⟨k, hk, rfl⟩ := hq
    have hk' := Finset.mem_range.mp hk
    refine ⟨k, ?_, rfl⟩
    rw [Finset.mem_coe, List.mem_toFinset]
    apply hfix k hk'
    rw [keyAt_keys248 hrm _ hk', keyAt_keys248 hrm _ hk', ptAt_mulB hrm _ _ hk']
    have hfx' : mapM (pkMat (chainEl D O.x5)) (sp (ptAt (qStack D O) k)) =
        sp (ptAt (qStack D O) k) := by
      rw [← hx]
      have h' : ((x : J) : GL (Fin 248) (ZMod 2)) • sp (ptAt (qStack D O) k) =
        sp (ptAt (qStack D O) k) := hxq
      exact (Act.smul_eq_self_iff _ _).mp h'
    have hlx := lil_mulB (P := ptAt (qStack D O) k) (N := chainEl D O.x5) (M' := 𝕄 (x : J)⁻¹)
      (by rw [← hx]; exact mat_mul_inv _) (hl k hk')
    refine (Act.keyL_eq (hl k hk') hlx ?_)
    rw [sp_mulB, hfx']
  refine (Set.ncard_le_ncard hsub (Set.Finite.image _ (Finset.finite_toSet _))).trans ?_
  refine (Set.ncard_image_le (Finset.finite_toSet _)).trans ?_
  rw [Set.ncard_coe_finset]
  exact (List.toFinset_card_le _).trans hfx.le

end Ctx

end CFSG.Certificates.ThDemp.Pts

end
