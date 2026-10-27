module

public import Certificates.Data.Kernel.LocalQT.Six
public import CFSG.Certificates.Kernel.LocalQTSmallSound
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_16FactsSixInputs
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.Aut6Inputs

public section

namespace CFSG.KC.LQT.X6

open Equiv CFSG.KC.LQT.S CFSG.QuasithinUnique.Unc25K1.Six CFSG.KC.Ord

theorem codeS (σ : Perm (Fin 6)) : S.code σ = P.code σ := rfl

theorem keyK_code (σ : Perm (Fin 6)) : keyK (P.code σ) = CFSG.QuasithinUnique.A5.Aut6.key σ := by
  rw [keyK, P.rec_sum (fun i => Nat.mul (P.img (P.code σ) i) (Nat.pow 6 i)) 6,
    CFSG.QuasithinUnique.A5.Aut6.key, ← Fin.sum_univ_eq_sum_range]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [P.img_code (by norm_num)]
  rfl

theorem lookW_eq (T : List (ℕ × List Bool)) (k : ℕ) : lookW T k = (List.lookup k T).getD [] := by
  induction T with
  | nil => rfl
  | cons p T ih =>
    obtain ⟨a, v⟩ := p
    change Bool.rec (motive := fun _ => List Bool) (lookW T k) v (Nat.beq a k) = _
    rw [List.lookup_cons]
    by_cases h : a = k
    · subst h
      rw [Nat.beq_refl]
      simp
    · have h' : Nat.beq a k = false := by
        rw [Bool.eq_false_iff]
        exact fun e => h (P.beq_iff.1 e)
      rw [h', ih, beq_false_of_ne (Ne.symm h)]

theorem evK_code (X Y : Perm (Fin 6)) (w : List Bool) :
    evK (P.code X) (P.code Y) w = P.code (CFSG.QuasithinUnique.A5.Aut6.ev X Y w) := by
  induction w with
  | nil => exact P.code_one
  | cons c w ih =>
    cases c
    · change P.mul 6 (P.code X) (evK _ _ w) = _
      rw [ih, P.code_mul (by norm_num)]
      rfl
    · change P.mul 6 (P.code Y) (evK _ _ w) = _
      rw [ih, P.code_mul (by norm_num)]
      rfl

open CFSG.QuasithinUnique.A5.Aut6 in
theorem phiK_code (T : List (ℕ × List Bool)) (X Y g : Perm (Fin 6)) :
    phiK T (P.code X) (P.code Y) (P.code g) =
      P.code (phi (fun g : Perm (Fin 6) => (List.lookup (key g) T).getD []) X Y g) := by
  rw [phiK, keyK_code, lookW_eq, evK_code]
  rfl

open CFSG.QuasithinUnique.A5.Aut6 in
theorem relK_iff (R : List (List Bool)) (X Y : Perm (Fin 6)) :
    relK R (P.code X) (P.code Y) = true ↔ ∀ r ∈ R, ev X Y r = 1 := by
  induction R with
  | nil => simp [relK]
  | cons r R ih =>
    change andB (Nat.beq (evK _ _ r) (P.one 6)) (relK R _ _) = true ↔ _
    rw [P.andB_iff, ih, evK_code, P.code_one, P.beq_code (by norm_num)]
    simp

theorem flatL_eq (l : List (List ℕ)) : flatL l = l.flatten := by
  induction l with
  | nil => rfl
  | cons c l ih =>
    change List.append c (flatL l) = _
    rw [ih, List.flatten_cons]
    rfl

theorem getW_eq : ∀ (l : List (List ℕ)) (i : ℕ) (hi : i < l.length),
    CFSG.KC.LQT.M.getW l i = l[i]
  | [], _, h => absurd h (by simp)
  | x :: l, 0, _ => rfl
  | x :: l, i + 1, h => by
    change Bool.rec (motive := fun _ => List ℕ) (CFSG.KC.LQT.M.getW l (Nat.sub (i + 1) 1)) x
      (Nat.beq (i + 1) 0) = _
    rw [show Nat.beq (i + 1) 0 = false from rfl, show Nat.sub (i + 1) 1 = i from rfl,
      getW_eq l i (by simpa using h)]
    rfl

open CFSG.QuasithinUnique.A5.Aut6 in
theorem ev_conj (τ X Y : Perm (Fin 6)) (w : List Bool) :
    ev (τ * X * τ⁻¹) (τ * Y * τ⁻¹) w = τ * ev X Y w * τ⁻¹ := by
  induction w with
  | nil => simp [ev]
  | cons c w ih =>
    cases c <;> simp only [ev, ih] <;> group

open CFSG.QuasithinUnique.A5.Aut6 in
theorem s4035k (T : List (ℕ × List Bool)) (R : List (List Bool)) {LA LY : List ℕ}
    {LXs : List (List ℕ)} {CA CB : ℕ} (ha : code ga = CA) (hb : code gb = CB)
    (hk : c4035 T R LA LXs LY CA CB = true)
    (hp : ∀ i < LXs.length, p4035 T R LA LXs LY CA CB i = true) :
    let w := fun g : Perm (Fin 6) => (List.lookup (key g) T).getD []
    (∀ x y : A6, IsCand w x y → IsInv w x y → ¬ IsConj w x y → HasFix w x y)
    ∧ (∀ g : A6, ev ga gb (w (g : Perm (Fin 6))) = (g : Perm (Fin 6))) := by
  intro w
  subst ha hb
  simp only [codeS] at hk hp
  simp only [c4035, S.allBs_cons, S.allBs_nil, P.andB_iff, and_true] at hk
  obtain ⟨k1, k2, k3, k4, k5⟩ := hk
  rw [relK_iff] at k1
  rw [P.allP_iff] at k2 k4 k5
  rw [P.allL_iff] at k3
  have hn6 : (6 : ℕ) ≤ 32 := by norm_num
  have hev : ∀ g : Perm (Fin 6), Perm.sign g = 1 → ev ga gb (w g) = g := by
    intro g hg
    have := k2 g
    rw [P.impB_iff, P.even_code hn6, phiK_code, P.beq_code hn6] at this
    exact this hg
  refine ⟨?_, fun g => hev g (Perm.mem_alternatingGroup.1 g.2)⟩
  intro x y hc hinv hnc
  have hword : ∀ (u : List Bool) (g : Perm (Fin 6)), g ∈ alternatingGroup (Fin 6) →
      phi w x y (g * ev ga gb u) = phi w x y g * ev (x : Perm (Fin 6)) y u := by
    intro u
    induction u with
    | nil => intro g _; simp [ev]
    | cons c u ih =>
      intro g hg
      cases c
      · have e1 := ih (g * ga) (Subgroup.mul_mem _ hg ga'.2)
        have e2 : phi w x y (g * ga) = phi w x y g * x := (hc ⟨g, hg⟩).1
        simp only [ev]
        rw [← mul_assoc, e1, e2, mul_assoc]
      · have e1 := ih (g * gb) (Subgroup.mul_mem _ hg gb'.2)
        have e2 : phi w x y (g * gb) = phi w x y g * y := (hc ⟨g, hg⟩).2
        simp only [ev]
        rw [← mul_assoc, e1, e2, mul_assoc]
  have h1 : phi w x y 1 = 1 := by
    have e := hword (w 1) 1 (Subgroup.one_mem _)
    rw [one_mul, hev 1 (by simp)] at e
    have e' : phi w x y 1 = phi w x y 1 * phi w x y 1 := e
    exact mul_eq_left.1 e'.symm
  have hrel : ∀ u : List Bool, ev ga gb u = 1 → ev (x : Perm (Fin 6)) y u = 1 := by
    intro u hu
    have e := hword u 1 (Subgroup.one_mem _)
    rw [one_mul, hu, h1, one_mul] at e
    exact e.symm
  have hx5 : (x : Perm (Fin 6)) ^ 5 = 1 := by
    have e := hrel [false, false, false, false, false] (by decide)
    have e2 : (x : Perm (Fin 6)) ^ 5 = ev (x : Perm (Fin 6)) y [false, false, false, false, false] := by
      simp [ev, pow_succ, mul_assoc]
    rw [e2, e]
  have hy3 : (y : Perm (Fin 6)) ^ 3 = 1 := by
    have e := hrel [true, true, true] (by decide)
    have e2 : (y : Perm (Fin 6)) ^ 3 = ev (x : Perm (Fin 6)) y [true, true, true] := by
      simp [ev, pow_succ, mul_assoc]
    rw [e2, e]
  have hxs := Perm.mem_alternatingGroup.1 x.2
  have hys := Perm.mem_alternatingGroup.1 y.2
  have hx : P.code (x : Perm (Fin 6)) ∈ LXs.flatten := by
    have e := k4 x
    rw [P.impB_iff, P.andB_iff, P.even_code hn6, powK, P.code_pow hn6, P.code_one,
      P.beq_code hn6, S.memL_iff, flatL_eq] at e
    exact e ⟨hxs, hx5⟩
  have hy : P.code (y : Perm (Fin 6)) ∈ LY := by
    have e := k5 y
    rw [P.impB_iff, P.andB_iff, P.even_code hn6, powK, P.code_pow hn6, P.code_one,
      P.beq_code hn6, S.memL_iff] at e
    exact e ⟨hys, hy3⟩
  obtain ⟨l, hl, hxl⟩ := List.mem_flatten.1 hx
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hl
  have hpi := hp i hi
  rw [p4035, getW_eq _ _ hi, P.allL_iff] at hpi
  have e := hpi _ hxl
  rw [P.allL_iff] at e
  have e2 := e _ hy
  rw [P.impB_iff, relK_iff] at e2
  have hr := e2 fun r hr => hrel r (k1 r hr)
  rcases P.orB_iff.1 hr with hconj | hr2
  · exfalso
    apply hnc
    rw [conjOK, P.letB_eq, P.anyN_iff] at hconj
    obtain ⟨m, -, hm⟩ := hconj
    rw [P.letB_eq, P.andB_iff, P.andB_iff] at hm
    obtain ⟨hperm, hca, hcb⟩ := hm
    obtain ⟨τ, hτ⟩ := P.exists_of_permK hperm
    rw [← hτ, P.conj_code hn6, P.beq_code hn6] at hca hcb
    refine ⟨τ⁻¹, fun g => ?_⟩
    rw [inv_inv]
    change ev (x : Perm (Fin 6)) y (w g) = _
    rw [← hca, ← hcb, ev_conj, hev g (Perm.mem_alternatingGroup.1 g.2)]
  · rcases P.orB_iff.1 hr2 with hfix | hninv
    · rw [P.anyL_iff] at hfix
      obtain ⟨a, ha, hfa⟩ := hfix
      obtain ⟨hpa, hea⟩ := P.andB_iff.1 (k3 a ha)
      obtain ⟨α, rfl⟩ := P.exists_of_permK hpa
      rw [P.even_code hn6] at hea
      rw [P.andB_iff, P.andB_iff, P.notB_iff, P.code_one, P.beq_code hn6, powK, P.code_pow hn6,
        P.beq_code hn6, phiK_code, P.beq_code hn6] at hfa
      exact ⟨⟨α, Perm.mem_alternatingGroup.2 hea⟩, hfa.2.1, hfa.1, hfa.2.2⟩
    · rw [P.anyL_iff] at hninv
      obtain ⟨g, hg, hng⟩ := hninv
      obtain ⟨hpg, heg⟩ := P.andB_iff.1 (k3 g hg)
      obtain ⟨γ, rfl⟩ := P.exists_of_permK hpg
      rw [P.even_code hn6] at heg
      rw [P.notB_iff, phiK_code, phiK_code, P.beq_code hn6] at hng
      exact absurd (hinv ⟨γ, Perm.mem_alternatingGroup.2 heg⟩) hng

end CFSG.KC.LQT.X6

end
