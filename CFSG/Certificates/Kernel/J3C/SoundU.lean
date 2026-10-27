module

public import CFSG.Certificates.Kernel.J3C.Sound
import CFSG.Certificates.Kernel.Spor.RawOrbEval

public section

namespace CFSG.KS.CentReg

open CFSG.KC.Enum CFSG.KS CFSG.KS.PEnum CFSG.KS.TBfs CFSG.KS.PC

section Mem

variable {n root cnt r : Nat} {L : Nat → Nat → Nat} {LV : Nat → Nat}
  {PTS POS PAR LAB TI : Nat → Nat} {σ : Nat → Equiv.Perm (Fin n)}

theorem mem_of_tree (R : Rep n root cnt r L LV PTS POS PAR LAB TI)
    (hσ : ∀ t < r, ∀ x < n, actN (σ (LV t)) x = L (LV t) x)
    {H K : Subgroup (Equiv.Perm (Fin n))} (hH : ∀ t < r, σ (LV t) ∈ H) (hHK : H ≤ K)
    (hfree : ∀ g ∈ K, g (⟨root, root_lt R⟩ : Fin n) = ⟨root, root_lt R⟩ → g = 1)
    {g : Equiv.Perm (Fin n)} (hg : g ∈ K)
    (hp : r32 POS (g (⟨root, root_lt R⟩ : Fin n) : Nat) < cnt) : g ∈ H := by
  have hpt := R.pts_pos (Fin.isLt (g (⟨root, root_lt R⟩ : Fin n))) hp
  have ht := tw_mem R hH _ hp
  have h1 := hfree _ (K.mul_mem (K.inv_mem (hHK ht)) hg) (by
    rw [Equiv.Perm.mul_apply, Equiv.Perm.inv_eq_iff_eq]
    apply Fin.ext
    rw [← actN_fin (tw σ PAR LAB _), tw_pt R hσ _ hp, hpt])
  rw [inv_mul_eq_one] at h1
  rw [← h1]
  exact ht

theorem normK_spec {KL U : Nat → Nat → Nat} {nk nu : Nat}
    (h : normK KL nk U nu POS cnt n root = true) :
    ∀ h < nk, ∀ i < nu, KL (2 * h) (U i (KL (2 * h + 1) root)) < n ∧
      r32 POS (KL (2 * h) (U i (KL (2 * h + 1) root))) < cnt := by
  intro hh hhl i hi
  unfold normK at h
  have h1 := Raw.Orb.allN_iff.1 (Raw.Orb.allN_iff.1 h hh hhl) i hi
  rw [Raw.Orb.strictB_eq, Raw.Orb.bAnd_eq, Bool.and_eq_true, Nat.blt_eq, Nat.blt_eq] at h1
  exact h1

theorem normK_sound (R : Rep n root cnt r L LV PTS POS PAR LAB TI)
    (hσ : ∀ t < r, ∀ x < n, actN (σ (LV t)) x = L (LV t) x)
    {H K : Subgroup (Equiv.Perm (Fin n))} (hH : ∀ t < r, σ (LV t) ∈ H) (hHK : H ≤ K)
    (hfree : ∀ g ∈ K, g (⟨root, root_lt R⟩ : Fin n) = ⟨root, root_lt R⟩ → g = 1)
    {KL U : Nat → Nat → Nat} {nk nu : Nat} {κ υ : Nat → Equiv.Perm (Fin n)}
    (hκ : ∀ h < nk, ∀ x < n, actN (κ h) x = KL (2 * h) x)
    (hκi : ∀ h < nk, ∀ x < n, actN (κ h)⁻¹ x = KL (2 * h + 1) x)
    (hυ : ∀ i < nu, ∀ x < n, actN (υ i) x = U i x)
    (hκK : ∀ h < nk, κ h ∈ K) (hυK : ∀ i < nu, υ i ∈ K)
    (h : normK KL nk U nu POS cnt n root = true) :
    ∀ h < nk, ∀ i < nu, κ h * υ i * (κ h)⁻¹ ∈ H := by
  intro hh hhl i hi
  have hr := root_lt R
  obtain ⟨-, hv⟩ := normK_spec h hh hhl i hi
  have hb1 : KL (2 * hh + 1) root < n := by
    rw [← hκi hh hhl root hr]
    exact actN_lt _ hr
  have hb2 : U i (KL (2 * hh + 1) root) < n := by
    rw [← hυ i hi _ hb1]
    exact actN_lt _ hb1
  have e : actN (κ hh * υ i * (κ hh)⁻¹) root = KL (2 * hh) (U i (KL (2 * hh + 1) root)) := by
    rw [actN_mul, actN_mul, hκi hh hhl root hr, hυ i hi _ hb1, hκ hh hhl _ hb2]
  refine mem_of_tree R hσ hH hHK hfree
    (K.mul_mem (K.mul_mem (hκK hh hhl) (hυK i hi)) (K.inv_mem (hκK hh hhl))) ?_
  rw [← actN_of_lt _ hr, e]
  exact hv

theorem centUK_sound {ucnt ru : Nat} {LU : Nat → Nat → Nat} {LVU : Nat → Nat}
    {PTSU UPOS PARU LABU TIU : Nat → Nat} {σU : Nat → Equiv.Perm (Fin n)}
    (RU : Rep n root ucnt ru LU LVU PTSU UPOS PARU LABU TIU)
    (hσU : ∀ t < ru, ∀ x < n, actN (σU (LVU t)) x = LU (LVU t) x)
    {H K : Subgroup (Equiv.Perm (Fin n))} (hH : ∀ t < ru, σU (LVU t) ∈ H) (hHK : H ≤ K)
    (hfree : ∀ g ∈ K, g (⟨root, root_lt RU⟩ : Fin n) = ⟨root, root_lt RU⟩ → g = 1)
    (R : Rep n root cnt r L LV PTS POS PAR LAB TI)
    (hσ : ∀ t < r, ∀ x < n, actN (σ (LV t)) x = L (LV t) x)
    (hrep : ∀ g ∈ K, ∃ k < cnt, r32 PTS k = (g (⟨root, root_lt R⟩ : Fin n) : Nat) ∧
      g = tw σ PAR LAB k)
    {U : Nat → Nat → Nat} {nu : Nat} {υ : Nat → Equiv.Perm (Fin n)}
    (hυ : ∀ i < nu, ∀ x < n, actN (υ i) x = U i x)
    (h : centUK L PTS PAR LAB cnt U nu UPOS ucnt root = true)
    {g : Equiv.Perm (Fin n)} (hg : g ∈ K) (hc : ∀ i < nu, g * υ i = υ i * g) : g ∈ H := by
  have hr := root_lt R
  obtain ⟨k, hk, hpt, hgk⟩ := hrep g hg
  unfold centUK at h
  have hj := Raw.Orb.allN_iff.1 h k hk
  rw [Raw.Orb.strictB_eq, Raw.Orb.bIf_eq] at hj
  by_cases hu : Nat.blt (r32 UPOS (r32 PTS k)) ucnt = true
  · refine mem_of_tree RU hσU hH hHK hfree hg ?_
    rw [← hpt]
    rw [Nat.blt_eq] at hu
    exact hu
  · exfalso
    have hall : allN nu (fun i => Nat.beq (hd (walkK L PAR LAB k (List.cons (U i root) List.nil)))
        (U i (r32 PTS k))) = true := by
      refine Raw.Orb.allN_iff.2 fun i hi => ?_
      have hq : ∀ x ∈ [U i root], x < n := by
        intro x hx
        rw [List.mem_singleton] at hx
        rw [hx, ← hυ i hi root hr]
        exact actN_lt _ hr
      unfold hd
      rw [walkK_tw R hσ hk hq]
      simp only [List.map_cons, List.map_nil, List.getD_cons_zero, Nat.beq_eq]
      rw [← hυ i hi root hr, ← actN_mul, ← hgk, hc i hi, hgk, actN_mul, tw_pt R hσ k hk,
        hυ i hi _ (R.pt k hk).lt]
    rw [if_neg hu, Raw.Orb.bIf_eq, if_pos hall] at hj
    exact absurd hj (by decide)

end Mem

section Words

variable {n : Nat}

@[expose] noncomputable def wordP (γ : Nat → Equiv.Perm (Fin n)) (w : List Int) :
    Equiv.Perm (Fin n) :=
  (w.map fun z => γ (sgnL z)).prod

variable {G : Nat → Nat → Nat} {γ : Nat → Equiv.Perm (Fin n)} {NL : Nat}

theorem wEval_eq (hγ : ∀ l < NL, ∀ x < n, actN (γ l) x = G l x) :
    ∀ w : List Int, (∀ z ∈ w, sgnL z < NL) → ∀ x < n, wEval G w x = actN (wordP γ w) x := by
  intro w
  induction w with
  | nil =>
    intro _ x _
    unfold wEval wordP
    rw [List.map_nil, List.prod_nil, actN_one]
    rfl
  | cons z w ih =>
    intro hw x hx
    have e : wEval G (z :: w) x = G (sgnL z) (wEval G w x) := rfl
    rw [e, ih (fun y hy => hw y (List.mem_cons_of_mem _ hy)) x hx,
      ← hγ _ (hw z List.mem_cons_self) _ (actN_lt _ hx), ← actN_mul]
    unfold wordP
    rw [List.map_cons, List.prod_cons]

theorem wInvEval_eq (hγi : ∀ l < NL, ∀ x < n, actN (γ l)⁻¹ x = G (Nat.xor l 1) x) :
    ∀ w : List Int, (∀ z ∈ w, sgnL z < NL) → ∀ x < n,
      wInvEval G w x = actN (wordP γ w)⁻¹ x := by
  intro w
  induction w with
  | nil =>
    intro _ x _
    unfold wInvEval wordP
    rw [List.map_nil, List.prod_nil, inv_one, actN_one]
    rfl
  | cons z w ih =>
    intro hw x hx
    have e : wInvEval G (z :: w) x = wInvEval G w (G (Nat.xor (sgnL z) 1) x) := rfl
    have hb : G (Nat.xor (sgnL z) 1) x < n := by
      rw [← hγi _ (hw z List.mem_cons_self) _ hx]
      exact actN_lt _ hx
    rw [e, ih (fun y hy => hw y (List.mem_cons_of_mem _ hy)) _ hb,
      ← hγi _ (hw z List.mem_cons_self) _ hx, ← actN_mul]
    unfold wordP
    rw [List.map_cons, List.prod_cons, mul_inv_rev]

theorem wordP_mem {P : Subgroup (Equiv.Perm (Fin n))} (hγP : ∀ l < NL, γ l ∈ P) {w : List Int}
    (hw : ∀ z ∈ w, sgnL z < NL) : wordP γ w ∈ P := by
  unfold wordP
  refine P.list_prod_mem fun g hg => ?_
  obtain ⟨z, hz, rfl⟩ := List.mem_map.1 hg
  exact hγP _ (hw z hz)

theorem conjW_eq (hγ : ∀ l < NL, ∀ x < n, actN (γ l) x = G l x)
    (hγi : ∀ l < NL, ∀ x < n, actN (γ l)⁻¹ x = G (Nat.xor l 1) x) {a0 : Nat} (ha0 : a0 < NL)
    {w : List Int} (hw : ∀ z ∈ w, sgnL z < NL) {z : Nat} (hz : z < n) :
    conjW G a0 w z = actN (wordP γ w * γ a0 * (wordP γ w)⁻¹) z := by
  unfold conjW
  have h1 := actN_lt (wordP γ w)⁻¹ hz
  rw [wInvEval_eq hγi w hw z hz, ← hγ a0 ha0 _ h1, wEval_eq hγ w hw _ (actN_lt _ h1),
    actN_mul, actN_mul]

end Words

section Cover

variable {n : Nat}

theorem fix2_of_two_level {r0 r1 c0 c1 b0 b1 : Nat} {L0 L1 : Nat → Nat → Nat}
    {LV0 LV1 : Nat → Nat} {PTS0 POS0 PAR0 LAB0 TI0 PTS1 POS1 PAR1 LAB1 TI1 : Nat → Nat}
    {σ0 σ1 : Nat → Equiv.Perm (Fin n)}
    (R0 : Rep n b0 c0 r0 L0 LV0 PTS0 POS0 PAR0 LAB0 TI0)
    (R1 : Rep n b1 c1 r1 L1 LV1 PTS1 POS1 PAR1 LAB1 TI1)
    (hσ0 : ∀ t < r0, ∀ x < n, actN (σ0 (LV0 t)) x = L0 (LV0 t) x)
    (hσ1 : ∀ t < r1, ∀ x < n, actN (σ1 (LV1 t)) x = L1 (LV1 t) x)
    {G : Subgroup (Equiv.Perm (Fin n))} (hG0 : ∀ t < r0, σ0 (LV0 t) ∈ G)
    (hG1 : ∀ t < r1, σ1 (LV1 t) ∈ G ∧
      σ1 (LV1 t) (⟨b0, root_lt R0⟩ : Fin n) = ⟨b0, root_lt R0⟩)
    (hc : Nat.card G ≤ c0 * c1) :
    ∀ g ∈ G, g (⟨b0, root_lt R0⟩ : Fin n) = ⟨b0, root_lt R0⟩ →
      g (⟨b1, root_lt R1⟩ : Fin n) = ⟨b1, root_lt R1⟩ → g = 1 := by
  intro g hg h0 h1
  obtain ⟨-, hrep⟩ := two_level R0 R1 hσ0 hσ1 hG0 hG1 hc
  obtain ⟨j, hj, e, hgj⟩ := hrep g hg h0
  rw [h1] at e
  have hj0 : j = 0 := R1.inj hj R1.hd.cnt_pos (by rw [e, R1.hd.root])
  rw [hgj, hj0, tw_eq, if_neg (fun h => absurd h.1 (Nat.lt_irrefl 0))]

variable {root cnt r : Nat} {L : Nat → Nat → Nat} {LV : Nat → Nat}
  {PTS POS PAR LAB TI : Nat → Nat} {σ : Nat → Equiv.Perm (Fin n)}

theorem coverK_sound (R : Rep n root cnt r L LV PTS POS PAR LAB TI)
    (hσ : ∀ t < r, ∀ x < n, actN (σ (LV t)) x = L (LV t) x)
    {S P : Subgroup (Equiv.Perm (Fin n))}
    (hrep : ∀ s ∈ S, ∃ k < cnt, r32 PTS k = (s (⟨root, root_lt R⟩ : Fin n) : Nat) ∧
      s = tw σ PAR LAB k)
    {G : Nat → Nat → Nat} {γ : Nat → Equiv.Perm (Fin n)} {NL a0 b : Nat} {W : Nat → List Int}
    (hγ : ∀ l < NL, ∀ x < n, actN (γ l) x = G l x)
    (hγi : ∀ l < NL, ∀ x < n, actN (γ l)⁻¹ x = G (Nat.xor l 1) x)
    (hγP : ∀ l < NL, γ l ∈ P) (hW : ∀ j < cnt, ∀ z ∈ W j, sgnL z < NL) (ha0 : a0 < NL)
    (hb : b < n) (hSP : S ≤ P)
    (hP2 : ∀ g ∈ P, g (⟨root, root_lt R⟩ : Fin n) = ⟨root, root_lt R⟩ →
      g (⟨b, hb⟩ : Fin n) = ⟨b, hb⟩ → g = 1)
    (h : coverK L PTS PAR LAB cnt G a0 W root b = true)
    {s : Equiv.Perm (Fin n)} (hs : s ∈ S) (ho : orderOf s = 2) :
    ∃ c ∈ P, s = c * γ a0 * c⁻¹ := by
  have hs2 : s * s = 1 := by rw [← pow_two, ← ho, pow_orderOf_eq_one]
  have hs1 : s ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at ho
    exact absurd ho (by decide)
  have hr := root_lt R
  obtain ⟨k, hk, -, hsk⟩ := hrep s hs
  have hk0 : 0 < k := by
    rcases Nat.eq_zero_or_pos k with h0 | h0
    · exfalso
      apply hs1
      rw [hsk, h0, tw_eq, if_neg (fun h => absurd h.1 (Nat.lt_irrefl 0))]
    · exact h0
  have hy : r32 PTS k < n := (R.pt k hk).lt
  have hss : actN (tw σ PAR LAB k) (r32 PTS k) = root := by
    rw [← tw_pt R hσ k hk, ← actN_mul, ← hsk, hs2, actN_one]
  have hq : ∀ x ∈ [b, r32 PTS k], x < n := by
    intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl
    · exact hb
    · exact hy
  unfold coverK at h
  have hj := Raw.Orb.allN_iff.1 h k hk
  simp only [Raw.Orb.strictB_eq] at hj
  rw [walkK_tw R hσ hk hq] at hj
  have hb0 : Nat.blt 0 k = true := by
    rw [Nat.blt_eq]
    exact hk0
  simp only [List.map_cons, List.map_nil, hd, List.getD_cons_succ, List.getD_cons_zero, hss,
    Nat.beq_refl, hb0, Raw.Orb.bIf_eq, ↓reduceIte] at hj
  have he : conjW G a0 (W k) root = r32 PTS k ∧
      conjW G a0 (W k) b = actN (tw σ PAR LAB k) b := by
    split at hj
    next hc => exact ⟨Nat.eq_of_beq_eq_true hc, Nat.eq_of_beq_eq_true hj⟩
    next => exact absurd hj (by decide)
  obtain ⟨e1, e2⟩ := he
  have hcP := wordP_mem hγP (hW k hk)
  have hgP : wordP γ (W k) * γ a0 * (wordP γ (W k))⁻¹ ∈ P :=
    P.mul_mem (P.mul_mem hcP (hγP a0 ha0)) (P.inv_mem hcP)
  rw [conjW_eq hγ hγi ha0 (hW k hk) hr, ← tw_pt R hσ k hk] at e1
  rw [conjW_eq hγ hγi ha0 (hW k hk) hb] at e2
  refine ⟨wordP γ (W k), hcP, ?_⟩
  have htP : tw σ PAR LAB k ∈ P := hSP (hsk ▸ hs)
  have h1 := hP2 _ (P.mul_mem (P.inv_mem hgP) htP)
    (by
      rw [Equiv.Perm.mul_apply, Equiv.Perm.inv_eq_iff_eq]
      apply Fin.ext
      rw [← actN_of_lt _ hr, ← actN_of_lt _ hr, e1])
    (by
      rw [Equiv.Perm.mul_apply, Equiv.Perm.inv_eq_iff_eq]
      apply Fin.ext
      rw [← actN_of_lt _ hb, ← actN_of_lt _ hb, e2])
  rw [inv_mul_eq_one] at h1
  rw [hsk, h1]

end Cover

end CFSG.KS.CentReg

end
