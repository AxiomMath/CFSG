module

public import CFSG.Certificates.Kernel.Co1.Model
public import CFSG.Certificates.Kernel.LceSTabSound
import CFSG.Certificates.Kernel.Perm16Sound
import Mathlib.GroupTheory.FreeGroup.Basic

public section

namespace CFSG.Certificates.Co1M

open CFSG.KC CFSG.KC.DceS CFSG.KC.Bind CFSG.KC.LceS CFSG.Certificates.LCE

@[expose] noncomputable def lcode (MPT : ℕ → ℕ) (MM l : ℕ) : ℕ :=
  if l % 2 = 0 then MPT (mget MM (l / 2)) else pinv (MPT (mget MM (l / 2)))

@[expose] noncomputable def wcodeL (MPT : ℕ → ℕ) (MM : ℕ) (w : List ℕ) : ℕ :=
  w.foldl (fun acc l => pmul acc (lcode MPT MM l)) idP

open CFSG.KS.P16

private noncomputable def mv (MPT : ℕ → ℕ) (MM g : ℕ) : Equiv.Perm (Fin 16) :=
  perm16 (MPT (mget MM g))

private theorem andB_true {a b : Bool} (h : andB a b = true) : a = true ∧ b = true := by
  cases a <;> cases b <;> simp_all [andB]

private theorem andB_intro {a b : Bool} (ha : a = true) (hb : b = true) : andB a b = true := by
  subst ha hb
  rfl

private theorem rec_and {f : Nat → Bool} : ∀ m,
    Nat.rec (motive := fun _ => Bool) true (fun g ih => andB ih (f g)) m = true →
      ∀ g < m, f g = true
  | 0, _, g, hg => absurd hg (Nat.not_lt_zero g)
  | m + 1, h, g, hg => by
    have h' : andB (Nat.rec (motive := fun _ => Bool) true (fun g ih => andB ih (f g)) m)
        (f m) = true := h
    obtain ⟨h1, h2⟩ := andB_true h'
    rcases Nat.lt_succ_iff_lt_or_eq.1 hg with hg | rfl
    · exact rec_and m h1 g hg
    · exact h2

private theorem nrec_ind {Q : ℕ → ℕ → Prop} {x : ℕ} {s : ℕ → ℕ → ℕ} {N : ℕ} (hx : Q 0 x)
    (hs : ∀ i a, i < N → Q i a → Q (i + 1) (s i a)) :
    ∀ m, m ≤ N → Q m (Nat.rec (motive := fun _ => ℕ) x s m)
  | 0, _ => hx
  | m + 1, hm => hs m _ (by omega) (nrec_ind hx hs m (by omega))

private theorem brec_eq_of {c : Bool} {x : ℕ} (hc : c = true) :
    Bool.rec (motive := fun _ => ℕ) (nat_lit 0) x c = x := by
  subst hc
  rfl

private theorem letV_map {A B : Type*} [Group A] [Group B] (f : A →* B) (y : ℕ → A) (l : ℕ) :
    f (letV y l) = letV (fun g => f (y g)) l := by
  unfold letV
  split_ifs <;> simp

private theorem bval_map {A B : Type*} [Group A] [Group B] (f : A →* B) (y : ℕ → A) (W n : ℕ) :
    f (bval y W n) = bval (fun g => f (y g)) W n := by
  unfold bval
  rw [map_list_prod, List.map_map]
  exact congrArg List.prod (List.map_congr_left fun i _ => letV_map f y _)

private theorem prod_map {A B : Type*} [Group A] [Group B] (f : A →* B) (y : ℕ → A) (w : List ℕ) :
    f (w.map (letV y)).prod = (w.map (letV fun g => f (y g))).prod := by
  rw [map_list_prod, List.map_map]
  exact congrArg List.prod (List.map_congr_left fun i _ => letV_map f y _)

private theorem bval_succ {A : Type*} [Group A] (y : ℕ → A) (W i : ℕ) :
    bval y W (i + 1) = bval y W i * letV y (wLet W i) := by
  unfold bval
  rw [List.range_succ, List.map_append, List.prod_append, List.map_singleton, List.prod_singleton]

private theorem letter_sem {MPT : ℕ → ℕ} {MM ng l : ℕ} (hng : ng < 128)
    (hperm : ∀ g < ng, mget MM g < 255 ∧ isPerm (MPT (mget MM g)) = true) (hl : l < 2 * ng) :
    IsP (lcode MPT MM l) ∧ perm16 (lcode MPT MM l) = letV (mv MPT MM) l := by
  have hg : l / 2 < ng := by omega
  have hP := isP_of_isPerm (hperm _ hg).2
  have h255 : l ≠ 255 := by omega
  unfold lcode letV
  simp only [h255, ↓reduceIte]
  split_ifs with hp
  · exact ⟨hP, rfl⟩
  · exact ⟨isP_pinv hP, perm16_pinv hP⟩

private theorem evalLce_sem {MPT : ℕ → ℕ} {MM ng E : ℕ} (hng : ng < 128)
    (hperm : ∀ g < ng, mget MM g < 255 ∧ isPerm (MPT (mget MM g)) = true)
    (hE : ∀ q < wLen E, wLet (wWord E) q < 2 * ng) :
    IsP (CFSG.KC.Co1M.evalLce MPT MM E) ∧
      perm16 (CFSG.KC.Co1M.evalLce MPT MM E) = bval (mv MPT MM) (wWord E) (wLen E) := by
  unfold CFSG.KC.Co1M.evalLce
  refine nrec_ind (Q := fun i a => IsP a ∧ perm16 a = bval (mv MPT MM) (wWord E) i)
    ⟨isP_idP, by rw [perm16_idP]; unfold bval; rfl⟩ ?_ _ le_rfl
  intro i a hi ⟨ha1, ha2⟩
  dsimp only
  have hl := hE i hi
  have hg : Nat.shiftRight (wLet (wWord E) i) 1 < ng := by
    rw [Nat.shiftRight_eq', Nat.shiftRight_eq_div_pow]
    omega
  have hc : andB (Nat.blt (nat_lit 0) a) (Nat.blt (mget MM (Nat.shiftRight (wLet (wWord E) i) (nat_lit 1)))
      (nat_lit 255)) = true :=
    andB_intro (Nat.blt_eq.mpr (isP_pos ha1)) (Nat.blt_eq.mpr (hperm _ hg).1)
  rw [brec_eq_of hc, bval_succ]
  have hd : Nat.shiftRight (wLet (wWord E) i) (nat_lit 1) = wLet (wWord E) i / 2 := by
    rw [Nat.shiftRight_eq', Nat.shiftRight_eq_div_pow]
  obtain ⟨hL1, hL2⟩ := letter_sem (MPT := MPT) hng hperm hl
  have e : Bool.rec (motive := fun _ => ℕ) (MPT (mget MM (Nat.shiftRight (wLet (wWord E) i) (nat_lit 1))))
      (pinv (MPT (mget MM (Nat.shiftRight (wLet (wWord E) i) (nat_lit 1)))))
      (Nat.beq (Nat.land (wLet (wWord E) i) (nat_lit 1)) (nat_lit 1)) = lcode MPT MM (wLet (wWord E) i) := by
    rw [hd]
    unfold lcode
    have hm : Nat.land (wLet (wWord E) i) (nat_lit 1) = wLet (wWord E) i % 2 := by
      rw [Nat.land_eq]
      exact Nat.and_one_is_mod _
    rw [hm]
    rcases Nat.mod_two_eq_zero_or_one (wLet (wWord E) i) with hp | hp
    · rw [hp]
      rfl
    · rw [hp]
      rfl
  rw [e]
  exact ⟨isP_pmul ha1 hL1, by rw [perm16_pmul ha1 hL1, ha2, hL2]⟩

private theorem wcodeL_sem {MPT : ℕ → ℕ} {MM ng : ℕ} (hng : ng < 128)
    (hperm : ∀ g < ng, mget MM g < 255 ∧ isPerm (MPT (mget MM g)) = true) :
    ∀ (w : List ℕ) (acc : ℕ), (∀ l ∈ w, l < 2 * ng) → IsP acc →
      IsP (w.foldl (fun acc l => pmul acc (lcode MPT MM l)) acc) ∧
        perm16 (w.foldl (fun acc l => pmul acc (lcode MPT MM l)) acc) =
          perm16 acc * (w.map (letV (mv MPT MM))).prod
  | [], acc, _, ha => ⟨ha, by simp⟩
  | l :: w, acc, hw, ha => by
    obtain ⟨hL1, hL2⟩ := letter_sem (MPT := MPT) hng hperm (hw l (by simp))
    obtain ⟨h1, h2⟩ := wcodeL_sem hng hperm w (pmul acc (lcode MPT MM l))
      (fun l' hl' => hw l' (List.mem_cons_of_mem _ hl')) (isP_pmul ha hL1)
    refine ⟨h1, ?_⟩
    rw [List.foldl_cons, h2, perm16_pmul ha hL1, hL2, List.map_cons, List.prod_cons, mul_assoc]

theorem faithful_sound {MPT RT ET : ℕ → ℕ} {MM R ng ne n Gp : ℕ}
    (hng : ng < 128)
    (hperm : ∀ g < ng, mget MM g < 255 ∧ isPerm (MPT (mget MM g)) = true)
    (hRL : ∀ r < R, ∀ q < wLen (RT r), wLet (wWord (RT r)) q < 2 * ng)
    (hrel : CFSG.KC.Co1M.relsOK MPT RT MM R = true)
    (hgen : ∀ k < ne, ∃ g < ng, gk Gp k = MPT (mget MM g))
    (_hgen' : ∀ g < ng, ∃ k < ne, gk Gp k = MPT (mget MM g))
    (henum : Nat.beq (eCnt (enumRun ET Gp ne n (nat_lit 0) n (nat_lit 1))) (Nat.succ n) = true)
    (hbound : ∀ (H : Type) [Group H] (y : ℕ → H),
      (∀ r < R, bval y (wWord (RT r)) (wLen (RT r)) = 1) →
        Finite (Subgroup.closure (y '' {g | g < ng})) ∧ Nat.card (Subgroup.closure (y '' {g | g < ng})) ≤ n)
    {G : Type*} [Group G] (y : ℕ → G) (hy : ∀ r < R, bval y (wWord (RT r)) (wLen (RT r)) = 1)
    (w : List ℕ) (hw : ∀ l ∈ w, l < 2 * ng) (hwc : wcodeL MPT MM w = idP) :
    (w.map (letV y)).prod = 1 := by
  classical
  set m := mv MPT MM with hm
  have hrelM : ∀ r < R, bval m (wWord (RT r)) (wLen (RT r)) = 1 := by
    intro r hr
    have he := Nat.eq_of_beq_eq_true (rec_and _ hrel r hr)
    rw [← (evalLce_sem hng hperm (hRL r hr)).2, he, perm16_idP]
  have hwM : (w.map (letV m)).prod = 1 := by
    have h := (wcodeL_sem hng hperm w idP hw isP_idP).2
    unfold wcodeL at hwc
    rw [hwc, perm16_idP, one_mul] at h
    exact h.symm
  have hgenP : ∀ k < ne, IsP (gk Gp k) := fun k hk => by
    obtain ⟨g, hg, e⟩ := hgen k hk
    rw [e]
    exact isP_of_isPerm (hperm g hg).2
  obtain ⟨hmem, hinj, -⟩ := enum_sound henum hgenP
  set CM := Subgroup.closure (m '' {g | g < ng}) with hCM
  have hsub : Submonoid.closure {x | ∃ k < ne, x = perm16 (gk Gp k)} ≤ CM.toSubmonoid := by
    rw [Submonoid.closure_le]
    rintro x ⟨k, hk, rfl⟩
    obtain ⟨g, hg, e⟩ := hgen k hk
    rw [e]
    exact Subgroup.subset_closure ⟨g, hg, rfl⟩
  have hcardM : n ≤ Nat.card CM := by
    let f : Fin n → CM := fun i => ⟨perm16 (eCode ET 0 i), hsub (hmem i i.isLt).2⟩
    have hf : Function.Injective f := fun i j hij =>
      Fin.ext (hinj i i.isLt j j.isLt
        (perm16_inj (hmem _ i.isLt).1 (hmem _ j.isLt).1 (congrArg Subtype.val hij)))
    have := Nat.card_le_card_of_injective f hf
    rwa [Nat.card_eq_fintype_card, Fintype.card_fin] at this
  let φ : FreeGroup ℕ →* G × Equiv.Perm (Fin 16) := FreeGroup.lift fun g => (y g, m g)
  let ι : FreeGroup ℕ ⧸ φ.ker →* G × Equiv.Perm (Fin 16) := QuotientGroup.kerLift φ
  have hι : Function.Injective ι := QuotientGroup.kerLift_injective φ
  let y' : ℕ → FreeGroup ℕ ⧸ φ.ker := fun g => (QuotientGroup.mk (FreeGroup.of g) : FreeGroup ℕ ⧸ φ.ker)
  have hιy : ∀ g, ι (y' g) = (y g, m g) := fun g => by
    change QuotientGroup.kerLift φ (QuotientGroup.mk (FreeGroup.of g)) = _
    rw [QuotientGroup.kerLift_mk]
    exact FreeGroup.lift_apply_of
  have hfst : ∀ g, (MonoidHom.fst G (Equiv.Perm (Fin 16))).comp ι (y' g) = y g := fun g => by
    rw [MonoidHom.comp_apply, hιy]
    rfl
  have hsnd : ∀ g, (MonoidHom.snd G (Equiv.Perm (Fin 16))).comp ι (y' g) = m g := fun g => by
    rw [MonoidHom.comp_apply, hιy]
    rfl
  have hrelH : ∀ r < R, bval y' (wWord (RT r)) (wLen (RT r)) = 1 := by
    intro r hr
    apply hι
    rw [map_one]
    apply Prod.ext
    · change (MonoidHom.fst G (Equiv.Perm (Fin 16))).comp ι (bval y' (wWord (RT r)) (wLen (RT r))) = 1
      rw [bval_map]
      simp only [hfst]
      exact hy r hr
    · change (MonoidHom.snd G (Equiv.Perm (Fin 16))).comp ι (bval y' (wWord (RT r)) (wLen (RT r))) = 1
      rw [bval_map]
      simp only [hsnd]
      exact hrelM r hr
  obtain ⟨hfin, hcard⟩ := hbound (FreeGroup ℕ ⧸ φ.ker) y' hrelH
  set C := Subgroup.closure (y' '' {g | g < ng}) with hC
  let ψ := (MonoidHom.snd G (Equiv.Perm (Fin 16))).comp ι
  have hmap : C.map ψ = CM := by
    rw [hC, MonoidHom.map_closure, Set.image_image]
    congr 1
  have hsurj := ψ.subgroupMap_surjective C
  have hcard2 : Nat.card C = Nat.card (C.map ψ) := by
    have h1 := Nat.card_le_card_of_surjective _ hsurj
    rw [hmap] at h1 ⊢
    omega
  have hinjC : Function.Injective (ψ.subgroupMap C) :=
    ((Nat.bijective_iff_surjective_and_card _).2 ⟨hsurj, hcard2⟩).1
  have hx : (w.map (letV y')).prod ∈ C := by
    apply Subgroup.list_prod_mem
    intro z hz
    obtain ⟨l, hl, rfl⟩ := List.mem_map.1 hz
    have hg : l / 2 < ng := by have := hw l hl; omega
    have hgen : y' (l / 2) ∈ C := Subgroup.subset_closure ⟨l / 2, hg, rfl⟩
    unfold letV
    split_ifs
    · exact C.one_mem
    · exact hgen
    · exact C.inv_mem hgen
  have hψx : ψ (w.map (letV y')).prod = 1 := by
    have e : (fun g => ψ (y' g)) = m := funext hsnd
    rw [prod_map, e]
    exact hwM
  have h1 : (⟨(w.map (letV y')).prod, hx⟩ : C) = 1 := by
    apply hinjC
    rw [map_one]
    exact Subtype.ext hψx
  have hx1 : (w.map (letV y')).prod = 1 := congrArg Subtype.val h1
  have h2 := prod_map ((MonoidHom.fst G (Equiv.Perm (Fin 16))).comp ι) y' w
  rw [hx1, map_one] at h2
  simp only [hfst] at h2
  exact h2.symm

end CFSG.Certificates.Co1M

end
