module

public import Certificates.Data.Kernel.ElemAbCol
public import CFSG.Certificates.Kernel.Census.E16Proof
public import CFSG.Certificates.Kernel.Census.RestrictSound

public section

namespace CFSG.KC.ElemAbCol

open Subgroup CFSG.KC.Census CFSG.KC.Census.SP CFSG.ComponentClassification.RankTwoSporadic.Cert
open CFSG.RankThree.Native CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Monster.B.Fischer

theorem pcommA_comm (n w a b : Nat) : pcommA n w a b = pcommA n w b a := by
  unfold pcommA
  apply Bool.eq_iff_iff.mpr
  rw [Nat.beq_eq, Nat.beq_eq]
  exact eq_comm

theorem ncPw_spec {n w : Nat} : ∀ {l : List Nat}, ncPw n w l = true → ∀ {a b : Nat}, a ∈ l →
    b ∈ l → a ≠ b → pcommA n w a b = false
  | [], _, _, _, ha, _, _ => absurd ha List.not_mem_nil
  | c :: l, h, a, b, ha, hb, hab => by
    simp only [ncPw, Bool.and_eq_true, List.all_eq_true] at h
    have e : ∀ x ∈ l, pcommA n w c x = false := fun x hx => by simpa using h.1 x hx
    rcases List.mem_cons.1 ha with rfl | ha'
    · rcases List.mem_cons.1 hb with rfl | hb'
      · exact absurd rfl hab
      · exact e b hb'
    · rcases List.mem_cons.1 hb with rfl | hb'
      · rw [pcommA_comm]
        exact e a ha'
      · exact ncPw_spec h.2 ha' hb' hab

theorem card_le_of_colOK {n w K : Nat} {gs : Array Nat} {ps : List Nat} {c : ArrCertP}
    {cls : List (List Nat)} (hn : n < 2 ^ 32) (hw : n ≤ 2 ^ w) (hps : ∀ p ∈ ps, p < n)
    (hg : gs.toList.all (canon1 n w) = true) (hc : c.pts.toList.all (canon1 n w) = true)
    (henum : penumOK n w gs ps c = true) (hcol : colOK n w K c.pts.toList cls = true)
    {B : Subgroup (Equiv.Perm (Fin n))} (hB : B ≤ closure (permsA n (gs.map (unpackP n w))))
    (hcomm : ∀ x ∈ B, ∀ y ∈ B, x * y = y * x) (hsq : ∀ x ∈ B, x * x = 1) :
    Nat.card B ≤ K + 1 := by
  classical
  simp only [colOK, Bool.and_eq_true, Nat.ble_eq, List.all_eq_true] at hcol
  obtain ⟨⟨hK, hnc⟩, hcov⟩ := hcol
  have G : Good n w := by
    have h' := henum
    unfold penumOK at h'
    simp only [Bool.and_eq_true, Nat.blt_eq, Nat.beq_eq] at h'
    obtain ⟨-, ⟨⟨h0, hid⟩, -⟩, -⟩ := h'
    have hv0 := pvalid_pts_of_penumOK henum c.pts[0]! (by
      rw [getElem!_pos c.pts 0 h0]
      exact Array.getElem_mem_toList h0)
    rw [hid] at hv0
    obtain ⟨e1, e2⟩ := pid_good hw hv0
    exact ⟨hn, hw, e1, e2⟩
  have hE := enumOK_of_enumOKK (penumOK_sound hn hw hg hc henum)
  have hrep : ∀ g ∈ closure (permsA n (gs.map (unpackP n w))),
      ∃ p ∈ c.pts.toList, Rep n (unpackP n w p) g := by
    intro g hg'
    obtain ⟨i, hi, hr⟩ := enumOK_exists_rep hps hE hg'
    have hi' : i < c.pts.size := by simpa [ArrCertP.toMain] using hi
    refine ⟨c.pts[i]!, ?_, ?_⟩
    · rw [getElem!_pos c.pts i hi']
      exact Array.getElem_mem_toList hi'
    · have e : (c.toMain n w).pts[i]! = unpackP n w c.pts[i]! := map_get _ _ hi'
      rw [← e]
      exact hr
  have hcan : ∀ p ∈ c.pts.toList, canon1 n w p = true := List.all_eq_true.1 hc
  have hid : Rep n (unpackP n w (pid n w)) 1 := by
    rw [G.pid_eq]
    exact rep_idA
  have hbeq : ∀ {p q : Nat} {g h : Equiv.Perm (Fin n)}, canon1 n w p = true →
      canon1 n w q = true → Rep n (unpackP n w p) g → Rep n (unpackP n w q) h →
      (Nat.beq p q = true ↔ g = h) := fun hp hq hg' hh => by
    rw [← eqA_unpack hp hq]
    exact eqA_iff hg' hh
  have hpc : ∀ {p q : Nat} {g h : Equiv.Perm (Fin n)}, canon1 n w p = true →
      Rep n (unpackP n w p) g → Rep n (unpackP n w q) h →
      Rep n (unpackP n w (pc n w p q)) (g * h) := fun hp hg' hh => by
    rw [pc_eq G hp]
    exact rep_compA hg' hh
  have key : ∀ b ∈ B, b ≠ 1 → ∃ k : Fin cls.length, ∃ p ∈ cls.get k,
      canon1 n w p = true ∧ Rep n (unpackP n w p) b := by
    intro b hb hb1
    obtain ⟨p, hp, hr⟩ := hrep b (hB hb)
    have hcp := hcan p hp
    have h := hcov p hp
    have h1 : Nat.beq p (pid n w) = false := by
      rcases hx : Nat.beq p (pid n w)
      · rfl
      · exact absurd ((hbeq hcp G.pid_canon hr hid).1 hx) hb1
    have h2 : Nat.beq (pc n w p p) (pid n w) = true :=
      (hbeq (pc_canon G _ _) G.pid_canon (hpc hcp hr hr) hid).2 (hsq b hb)
    unfold covd at h
    rw [h1, h2] at h
    simp only [Bool.false_or, Bool.not_true] at h
    obtain ⟨l, hl, hpl⟩ := List.any_eq_true.1 h
    obtain ⟨q, hq, hpq⟩ := List.any_eq_true.1 hpl
    obtain rfl : p = q := Nat.eq_of_beq_eq_true hpq
    obtain ⟨k, rfl⟩ := List.mem_iff_get.1 hl
    exact ⟨k, p, hq, hcp, hr⟩
  let F : B → Fin (cls.length + 1) := fun b =>
    if h : (b : Equiv.Perm (Fin n)) = 1 then 0 else (key b b.2 h).choose.succ
  have hF : Function.Injective F := by
    intro a b hab
    by_cases ha : (a : Equiv.Perm (Fin n)) = 1 <;> by_cases hb : (b : Equiv.Perm (Fin n)) = 1
    · exact Subtype.ext (ha.trans hb.symm)
    · simp only [F, dif_pos ha, dif_neg hb] at hab
      exact absurd hab.symm (Fin.succ_ne_zero _)
    · simp only [F, dif_neg ha, dif_pos hb] at hab
      exact absurd hab (Fin.succ_ne_zero _)
    · simp only [F, dif_neg ha, dif_neg hb, Fin.succ_inj] at hab
      obtain ⟨p, hp, hcp, hrp⟩ := (key a a.2 ha).choose_spec
      obtain ⟨q, hq, hcq, hrq⟩ := (key b b.2 hb).choose_spec
      rw [hab] at hp
      apply Subtype.ext
      by_cases hpq : p = q
      · subst hpq
        exact hrp.unique hrq
      · exfalso
        have h1 := ncPw_spec (hnc _ (List.get_mem _ _)) hp hq hpq
        have h2 : pcommA n w p q = true :=
          (hbeq (pc_canon G _ _) (pc_canon G _ _) (hpc hcp hrp hrq) (hpc hcq hrq hrp)).2
            (hcomm a a.2 b b.2)
        rw [h1] at h2
        exact Bool.false_ne_true h2
  have hcard := Nat.card_le_card_of_injective F hF
  rw [Nat.card_eq_fintype_card (α := Fin (cls.length + 1)), Fintype.card_fin] at hcard
  omega

theorem card_le_of_res {n m N : ℕ} {X : Set (Equiv.Perm (Fin n))} {Y : Set (Equiv.Perm (Fin m))}
    (O : Fin m → Fin n) (hO : Function.Injective O) (hX : ∀ g ∈ X, ∀ i, ∃ j, g (O i) = O j)
    (hY : ∀ σ ∈ Y, ∃ g ∈ X, ∀ i, g (O i) = O (σ i))
    (hcard : Nat.card (closure X) ≤ Nat.card (closure Y))
    (h : ∀ B : Subgroup (Equiv.Perm (Fin m)), B ≤ closure Y →
      (∀ x ∈ B, ∀ y ∈ B, x * y = y * x) → (∀ x ∈ B, x * x = 1) → Nat.card B ≤ N)
    {B : Subgroup (Equiv.Perm (Fin n))} (hB : B ≤ closure X)
    (hcomm : ∀ x ∈ B, ∀ y ∈ B, x * y = y * x) (hsq : ∀ x ∈ B, x * x = 1) :
    Nat.card B ≤ N := by
  have hS : closure X ≤ Restrict.stab O :=
    (closure_le _).2 fun g hg => Restrict.mem_stab_of_maps hO (hX g hg)
  let f : closure X →* Equiv.Perm (Fin m) := (Restrict.resHom hO).comp (inclusion hS)
  have hle : closure Y ≤ f.range := by
    rw [closure_le]
    intro σ hσ
    obtain ⟨g, hg, hgσ⟩ := hY σ hσ
    exact ⟨⟨g, subset_closure hg⟩, Restrict.resHom_eq hO hgσ⟩
  have hinj : Function.Injective f :=
    injective_of_card_le_range f (hcard.trans (card_le_of_le hle))
  have hR : Nat.card (closure X) = Nat.card f.range :=
    Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv
  have heq : closure Y = f.range := eq_of_le_of_card_ge hle (hR ▸ hcard)
  have hc1 : Nat.card ((B.subgroupOf (closure X)).map f) = Nat.card B := by
    rw [Subgroup.card_map_of_injective hinj]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hB).toEquiv
  rw [← hc1]
  refine h _ (by rw [heq]; exact Subgroup.map_le_range f _) ?_ ?_
  · rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (hcomm _ (Subgroup.mem_subgroupOf.1 ha) _ (Subgroup.mem_subgroupOf.1 hb))
  · rintro _ ⟨a, ha, rfl⟩
    rw [← map_mul, ← map_one f]
    congr 1
    exact Subtype.ext (hsq _ (Subgroup.mem_subgroupOf.1 ha))

end CFSG.KC.ElemAbCol
