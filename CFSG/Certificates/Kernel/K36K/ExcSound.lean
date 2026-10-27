module

public import Certificates.Data.Kernel.K36K.Exc
public import CFSG.Certificates.Kernel.CoreD2K.Sound

public section

namespace CFSG.KD.K36K

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.PEnum CFSG.KS.MaxD2 CFSG.KS.K36K
  CFSG.KD.CoreD2K
open CFSG.PSL3Four.Native CFSG.ComponentClassification.PSL3Four

theorem mem_normalizer_closure {X : Type*} [Group X] [Finite X] {S : Set X} {c : X}
    (h : ∀ x ∈ S, c * x * c⁻¹ ∈ Subgroup.closure S) :
    c ∈ Subgroup.normalizer (Subgroup.closure S : Set X) := by
  set Y := Subgroup.closure S with hY
  have hle : Y.map (MulAut.conj c).toMonoidHom ≤ Y := by
    rw [hY, MonoidHom.map_closure, Subgroup.closure_le]
    rintro _ ⟨x, hx, rfl⟩
    exact h x hx
  have heq : Y.map (MulAut.conj c).toMonoidHom = Y :=
    Subgroup.eq_of_le_of_card_ge hle
      (Subgroup.card_map_of_injective (f := (MulAut.conj c).toMonoidHom)
        (MulAut.conj c).injective).ge
  rw [Subgroup.mem_normalizer_iff]
  intro y
  constructor
  · intro hy
    exact hle ⟨y, hy, rfl⟩
  · intro hy
    rw [← heq] at hy
    obtain ⟨x, hx, hxy⟩ := hy
    change c * x * c⁻¹ = c * y * c⁻¹ at hxy
    rwa [← mul_left_cancel (mul_right_cancel hxy)]

section Packed

variable {n w : Nat}

theorem eqYK_sound (hn : szOK n w = true) {p z v l r : Nat} {zz vv ll rr : Equiv.Perm (Fin n)}
    (hz : PR n w z zz) (hv : PR n w v vv) (hl : PR n w l ll) (hr : PR n w r rr)
    (h : eqYK n w p z v l r = true) : ∃ α < p, ∃ β < p, ll = zz ^ α * vv ^ β * rr := by
  unfold eqYK at h
  by_contra hne
  push Not at hne
  have h' := bnot_e h
  rw [← Bool.not_eq_true, PK.allN_iff] at h'
  refine h' fun α hα => PK.allN_iff.2 fun β hβ => ?_
  have hb : Nat.beq l (pcomp n w (mask w) (pcomp n w (mask w) (pw n w z α) (pw n w v β)) r) =
      false := Bool.eq_false_iff.2 fun e => hne α hα β hβ
    ((pr_beq hl (pr_mul (pr_mul (pr_pow hn hz α) (pr_pow hn hv β)) hr)).1 e)
  rw [hb]

theorem normYK_sound (hn : szOK n w = true) {p z v m : Nat} {CT : ℕ → ℕ}
    {zz vv : Equiv.Perm (Fin n)} {c : ℕ → Equiv.Perm (Fin n)} (hz : PR n w z zz)
    (hv : PR n w v vv) (hc : ∀ l < m, PR n w (CT l) (c l)) (h : normYK n w p z v m CT = true) :
    Subgroup.closure {g | ∃ l < m, c l = g} ≤
      Subgroup.normalizer
        (Subgroup.closure ({zz, vv} : Set (Equiv.Perm (Fin n))) : Set (Equiv.Perm (Fin n))) := by
  rw [Subgroup.closure_le]
  rintro _ ⟨l, hl, rfl⟩
  have hl' := PK.allN_iff.1 h l hl
  rw [PK.strictB_eq] at hl'
  obtain ⟨h1, h2⟩ := band_e hl'
  have hmem : ∀ {x : Nat} {xx : Equiv.Perm (Fin n)}, PR n w x xx →
      eqYK n w p z v (pcomp n w (mask w) (CT l) x) (CT l) = true →
        c l * xx * (c l)⁻¹ ∈ Subgroup.closure ({zz, vv} : Set (Equiv.Perm (Fin n))) := by
    intro x xx hx he
    obtain ⟨α, -, β, -, hab⟩ := eqYK_sound hn hz hv (pr_mul (hc l hl) hx) (hc l hl) he
    rw [hab, mul_inv_cancel_right]
    exact Subgroup.mul_mem _ (Subgroup.pow_mem _ (Subgroup.subset_closure (by simp)) _)
      (Subgroup.pow_mem _ (Subgroup.subset_closure (by simp)) _)
  refine mem_normalizer_closure fun x hx => ?_
  rcases hx with rfl | hx
  · exact hmem hz h1
  · rw [Set.mem_singleton_iff] at hx
    subst hx
    exact hmem hv h2

theorem penum_facts (hn : szOK n w = true) {m cnt cap len : Nat}
    {CT CTI T PL POS SRT SRI : ℕ → ℕ} {c : ℕ → Equiv.Perm (Fin n)}
    (hc : ∀ l < m, PR n w (CT l) (c l)) (hh : penumHdK (pidn n w) cnt cap T PL = true)
    (hsl : penumSlK n w (mask w) (n * w) false CT CTI m cnt T PL POS SRT SRI 0 len = true)
    (hlen : cnt ≤ len) :
    (∀ i < cnt, ∃ g ∈ Subgroup.closure {g | ∃ l < m, c l = g}, PR n w (T i) g) ∧
      (∀ g ∈ Subgroup.closure {g | ∃ l < m, c l = g}, ∃ i < cnt, PR n w (T i) g) ∧
      ∀ i < cnt, ∀ j < cnt, T i = T j → i = j := by
  set gens : Array Tab := Array.ofFn (n := m) fun k => unpack n w (CT k.val) with hgens'
  have hgget : ∀ k < m, gens[k]! = unpack n w (CT k) := fun k hk => by
    rw [hgens', getElem!_pos _ k (by simpa using hk), Array.getElem_ofFn]
  have hgsz : gens.size = m := Array.size_ofFn
  have hgOK : GensOK n w m CT gens := ⟨hgsz, fun j hj => ⟨hgget j hj, (hc j hj).1⟩⟩
  have hp : ∀ i < cnt, penumPtK n w (mask w) (n * w) false CT CTI m cnt T PL POS SRT SRI i =
      true := fun i hi =>
    CFSG.KS.BaseMask.penumSl_spec hsl (Nat.zero_le i) (by omega) hi
  have hcan : ∀ i < cnt, Cn n w (T i) := fun i hi => by
    have h := hp i hi
    unfold penumPtK at h
    rw [PK.strictB_eq] at h
    exact (band_e h).1
  obtain ⟨-, henum⟩ := penumK_left_sound hn hgOK hh hp
  have hA : ∀ g ∈ {g | ∃ l < m, c l = g}, ∃ j < gens.size, TabRep gens[j]! g := by
    rintro g ⟨k, hk, rfl⟩
    exact ⟨k, by rw [hgsz]; exact hk, by rw [hgget k hk]; exact (hc k hk).2⟩
  have hgensE : ∀ j < gens.size, ∃ g ∈ {g | ∃ l < m, c l = g}, TabRep gens[j]! g := by
    intro j hj
    rw [hgsz] at hj
    exact ⟨c j, ⟨j, hj, rfl⟩, by rw [hgget j hj]; exact (hc j hj).2⟩
  have hE := enumerates_closure hA hgensE henum
  have hL : (penumRec n w cnt T PL).tabs.toList =
      List.ofFn (fun i : Fin cnt => unpack n w (T i.val)) := by
    simp [penumRec]
  rw [hL] at hE
  refine ⟨fun i hi => ?_, fun g hg => ?_, fun i hi j hj e => ?_⟩
  · obtain ⟨g, hg, hr⟩ := hE.sound _ (List.mem_ofFn.2 ⟨⟨i, hi⟩, rfl⟩)
    exact ⟨g, hg, hcan i hi, hr⟩
  · obtain ⟨t, ht, hr⟩ := hE.complete g hg
    obtain ⟨i, rfl⟩ := List.mem_ofFn.1 ht
    exact ⟨i, i.2, hcan i i.2, hr⟩
  · have hinj := List.nodup_ofFn.1 hE.nodup
    have := @hinj ⟨i, hi⟩ ⟨j, hj⟩ (by simp only [e])
    exact congrArg Fin.val this

theorem centYK_sound (hn : szOK n w = true) {p z v cnt : Nat} {T : ℕ → ℕ}
    {zz vv : Equiv.Perm (Fin n)} (hz : PR n w z zz) (hv : PR n w v vv)
    {N : Subgroup (Equiv.Perm (Fin n))} (hcomp : ∀ g ∈ N, ∃ i < cnt, PR n w (T i) g)
    (h : centYK n w p z v cnt T = true) :
    ∀ k ∈ N, k * zz = zz * k → k * vv = vv * k →
      k ∈ Subgroup.closure ({zz, vv} : Set (Equiv.Perm (Fin n))) := by
  intro k hk h1 h2
  obtain ⟨i, hi, hP⟩ := hcomp k hk
  have hi' := PK.allN_iff.1 h i hi
  rw [PK.strictB_eq] at hi'
  have e1 : Nat.beq (pcomp n w (mask w) (T i) z) (pcomp n w (mask w) z (T i)) = true :=
    (pr_beq (pr_mul hP hz) (pr_mul hz hP)).2 h1
  have e2 : Nat.beq (pcomp n w (mask w) (T i) v) (pcomp n w (mask w) v (T i)) = true :=
    (pr_beq (pr_mul hP hv) (pr_mul hv hP)).2 h2
  rw [e1, e2] at hi'
  obtain ⟨α, -, β, -, hab⟩ := eqYK_sound hn hz hv hP (pr_one hn) hi'
  rw [hab, mul_one]
  exact Subgroup.mul_mem _ (Subgroup.pow_mem _ (Subgroup.subset_closure (by simp)) _)
    (Subgroup.pow_mem _ (Subgroup.subset_closure (by simp)) _)

theorem foldN_count (q : Nat → Bool) (cnt : Nat) :
    foldN cnt (fun i c => nIf(q i, Nat.succ c, c)) (nat_lit 0) =
      ((List.range cnt).filter q).length := by
  rw [PK.foldN_eq]
  induction (List.range cnt) with
  | nil => rfl
  | cons x l ih =>
    rw [List.foldr_cons, ih, List.filter_cons]
    cases q x <;> rfl

theorem cntCK_sound {B u cnt : Nat} {T : ℕ → ℕ} {uu : Equiv.Perm (Fin n)}
    {N : Subgroup (Equiv.Perm (Fin n))} (hu : PR n w u uu)
    (hsnd : ∀ i < cnt, ∃ g ∈ N, PR n w (T i) g) (hinj : ∀ i < cnt, ∀ j < cnt, T i = T j → i = j)
    (h : B ≤ cntCK n w u cnt T) : B ≤ Set.ncard {k | k ∈ N ∧ k * uu = uu * k} := by
  classical
  have hex : ∀ i, ∃ g : Equiv.Perm (Fin n), i < cnt → g ∈ N ∧ PR n w (T i) g := fun i => by
    by_cases hi : i < cnt
    · obtain ⟨g, hg, hP⟩ := hsnd i hi
      exact ⟨g, fun _ => ⟨hg, hP⟩⟩
    · exact ⟨1, fun h => absurd h hi⟩
  choose g hg using hex
  unfold cntCK at h
  rw [foldN_count] at h
  set L := (List.range cnt).filter fun i => strictB (T i) (fun t =>
    Nat.beq (pcomp n w (mask w) t u) (pcomp n w (mask w) u t)) with hLdef
  have hLmem : ∀ i ∈ L, i < cnt ∧
      Nat.beq (pcomp n w (mask w) (T i) u) (pcomp n w (mask w) u (T i)) = true := by
    intro i hi
    rw [hLdef, List.mem_filter, List.mem_range, PK.strictB_eq] at hi
    exact hi
  have hnd : (L.map g).Nodup := by
    refine List.Nodup.map_on (fun i hi j hj e => ?_) (List.nodup_range.filter _)
    have hi' := (hLmem i hi).1
    have hj' := (hLmem j hj).1
    exact hinj i hi' j hj' (Nat.eq_of_beq_eq_true ((pr_beq (hg i hi').2 (hg j hj').2).2 e))
  have hsub : (↑(L.map g).toFinset : Set (Equiv.Perm (Fin n))) ⊆
      {k | k ∈ N ∧ k * uu = uu * k} := by
    intro k hk
    rw [Finset.mem_coe, List.mem_toFinset, List.mem_map] at hk
    obtain ⟨i, hi, rfl⟩ := hk
    obtain ⟨hi1, hi2⟩ := hLmem i hi
    exact ⟨(hg i hi1).1, (pr_beq (pr_mul (hg i hi1).2 hu) (pr_mul hu (hg i hi1).2)).1 hi2⟩
  calc B ≤ L.length := h
    _ = (L.map g).toFinset.card := by rw [List.toFinset_card_of_nodup hnd, List.length_map]
    _ = Set.ncard (↑(L.map g).toFinset : Set (Equiv.Perm (Fin n))) :=
      (Set.ncard_coe_finset _).symm
    _ ≤ _ := Set.ncard_le_ncard hsub (Set.toFinite _)

end Packed

end CFSG.KD.K36K

end
