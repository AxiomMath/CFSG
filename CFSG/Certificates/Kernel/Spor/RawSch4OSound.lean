module

public import CFSG.Certificates.Kernel.Spor.RawSch3GSound
import all CFSG.Certificates.Kernel.Spor.RawSch3GSound

public section

namespace CFSG.KS.Raw.Orb

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Mathieu CFSG.Monster.B.Co2.Native
  CFSG.Monster.B.Co2 CFSG.Certificates.Native

section Core

variable {G : Type*} [Group G]

@[expose] def TW (c : Nat) (t : Nat → G) (W : Set G) : Set G := {g | ∃ a < c, ∃ v ∈ W, g = t a * v}

theorem mem_TW {c : Nat} {t : Nat → G} {W : Set G} {g : G} :
    g ∈ TW c t W ↔ ∃ a < c, ∃ v ∈ W, g = t a * v := Iff.rfl

theorem mulW {c : Nat} {t : Nat → G} {L1 L2 W : Set G}
    (hW : ∀ g ∈ Submonoid.closure L2, ∀ v ∈ W, g * v ∈ W) (hWm : W ⊆ Submonoid.closure L2)
    (h1 : ∀ σ ∈ L1, ∀ a < c, ∃ a' < c, ∃ v ∈ W, σ * t a = t a' * v)
    (m1 : ∀ a < c, t a ∈ Submonoid.closure L1) (inc : L2 ⊆ L1) :
    (∀ g ∈ Submonoid.closure L1, ∀ u ∈ TW c t W, g * u ∈ TW c t W) ∧
      TW c t W ⊆ Submonoid.closure L1 := by
  let M : Submonoid G :=
    { carrier := {g | ∀ u ∈ TW c t W, g * u ∈ TW c t W}
      mul_mem' := fun {x y} hx hy u hu => by
        rw [mul_assoc]
        exact hx _ (hy u hu)
      one_mem' := fun u hu => by rwa [one_mul] }
  have hL : L1 ⊆ M := by
    intro σ hσ u hu
    obtain ⟨a, ha, v, hv, rfl⟩ := mem_TW.1 hu
    obtain ⟨a', ha', v', hv', e⟩ := h1 σ hσ a ha
    exact mem_TW.2 ⟨a', ha', v' * v, hW v' (hWm hv') v hv, by rw [← mul_assoc, e, mul_assoc]⟩
  have hM : Submonoid.closure L1 ≤ M := Submonoid.closure_le.2 hL
  refine ⟨fun g hg => hM hg, fun u hu => ?_⟩
  obtain ⟨a, ha, v, hv, rfl⟩ := mem_TW.1 hu
  exact Submonoid.mul_mem _ (m1 a ha) (Submonoid.closure_mono inc (hWm hv))

theorem one_W : ∀ g ∈ Submonoid.closure (∅ : Set G), ∀ v ∈ ({1} : Set G), g * v ∈ ({1} : Set G) := by
  intro g hg v hv
  rw [Submonoid.closure_empty, Submonoid.mem_bot] at hg
  rw [hg, one_mul]
  exact hv

theorem one_Wm : ({1} : Set G) ⊆ Submonoid.closure (∅ : Set G) := by
  intro v hv
  rw [Set.mem_singleton_iff.1 hv]
  exact Submonoid.one_mem _

theorem mulCS {c0 : Nat} {t0 : Nat → G} {L U : Set G}
    (hU : ∀ u ∈ U, ∀ v ∈ U, u * v ∈ U)
    (h0 : ∀ σ ∈ L, ∀ h < c0, ∃ k < c0, ∃ u ∈ U, σ * t0 h = t0 k * u)
    (hone : (1 : G) ∈ U) {g : G} (hg : g ∈ Submonoid.closure L) :
    ∀ h < c0, ∃ k < c0, ∃ u ∈ U, g * t0 h = t0 k * u := by
  let M : Submonoid G :=
    { carrier := {g | ∀ h < c0, ∀ v ∈ U, ∃ k < c0, ∃ u ∈ U, g * (t0 h * v) = t0 k * u}
      mul_mem' := fun {x y} hx hy h hh v hv => by
        obtain ⟨k, hk, u, hu, e⟩ := hy h hh v hv
        obtain ⟨k', hk', u', hu', e'⟩ := hx k hk u hu
        exact ⟨k', hk', u', hu', by rw [mul_assoc, e, e']⟩
      one_mem' := fun h hh v hv => ⟨h, hh, v, hv, one_mul _⟩ }
  have hL : L ⊆ M := by
    intro σ hσ h hh v hv
    obtain ⟨k, hk, u, hu, e⟩ := h0 σ hσ h hh
    exact ⟨k, hk, u * v, hU u hu v hv, by rw [← mul_assoc, e, mul_assoc]⟩
  have hgM : g ∈ M := Submonoid.closure_le.2 hL hg
  intro h hh
  obtain ⟨k, hk, u, hu, e⟩ := hgM h hh 1 hone
  exact ⟨k, hk, u, hu, by rw [← e, mul_one]⟩

end Core

@[expose] noncomputable def PS (n w : Nat) (TR LR : Nat → Nat) : Nat → Nat → Set (Equiv.Perm (Fin n))
  | _, 0 => {1}
  | l, d + 1 => TW (rcnt (LR l)) (tp n w TR (LR l)) (PS n w TR LR (l + 1) d)

theorem PS_zero {n w : Nat} {TR LR : Nat → Nat} (l : Nat) : PS n w TR LR l 0 = {1} := rfl

theorem PS_succ {n w : Nat} {TR LR : Nat → Nat} (l d : Nat) :
    PS n w TR LR l (d + 1) = TW (rcnt (LR l)) (tp n w TR (LR l)) (PS n w TR LR (l + 1) d) := rfl

theorem mem_PS_of_sift {n w BP E : Nat} {LR TR TRI : Nat → Nat} (hn24 : n < 16777216)
    (hw : n + 1 < 2 ^ w)
    (hP : ∀ l < E, ∀ k < rcnt (LR l), permOK n w (mask w) (n * w) (TR (roff n (n * w) (LR l) + k))
      (TRI (roff n (n * w) (LR l) + k)) = true) :
    ∀ d l, l + d = E → ∀ (G : Nat) (g : Equiv.Perm (Fin n)), PRep n w G g →
      siftK n w (mask w) (n * w) (pidn n w) LR TRI BP d l G = true → g ∈ PS n w TR LR l d := by
  have hn : n < 2 ^ 32 := by omega
  intro d
  induction d with
  | zero =>
    intro l _ G g hG h
    rw [siftK_zero] at h
    obtain ⟨-, he⟩ := (bAnd_iff _ _).1 h
    rw [Nat.eq_of_beq_eq_true he] at hG
    rw [PS_zero, Set.mem_singleton_iff]
    exact prep_unique hG (prep_pidn hn24 hw)
  | succ d ih =>
    intro l hl G g hG h
    rw [siftK_succ] at h
    simp only [strictB_eq, bIf_eq] at h
    split at h
    · rename_i hk
      have hk' := Nat.blt_eq.mp hk
      have hG' := prep_pcomp hn (prep_pp (hP l (by omega) _ hk')).2 hG
      have hm := ih (l + 1) (by omega) _ _ hG' h
      rw [PS_succ, mem_TW]
      exact ⟨_, hk', _, hm, by unfold tp; rw [mul_inv_cancel_left]⟩
    · exact absurd h Bool.false_ne_true

theorem sift_of_mem_PS {n w BP E lo : Nat} {LR TR TRI : Nat → Nat} (hsz : szOK n w = true)
    (hP : ∀ l < E, ∀ k < rcnt (LR l), permOK n w (mask w) (n * w) (TR (roff n (n * w) (LR l) + k))
      (TRI (roff n (n * w) (LR l) + k)) = true)
    (hb : ∀ l < E, pg w (mask w) BP l < n)
    (ht : ∀ l, lo ≤ l → l < E → ∀ a < rcnt (LR l), ∀ hr : pg w (mask w) BP l < n,
      ((tp n w TR (LR l) a) ⟨_, hr⟩ : Nat) = rpt w (mask w) (LR l) a)
    (hq : ∀ l < E, ∀ a < rcnt (LR l),
      rpos w (mask w) (n * w) (LR l) (rpt w (mask w) (LR l) a) = a)
    (hfix : ∀ l d, lo ≤ l → l + (d + 1) = E → ∀ v ∈ PS n w TR LR (l + 1) d, ∀ x : Fin n,
      (x : Nat) = pg w (mask w) BP l → v x = x) :
    ∀ d l, lo ≤ l → l + d = E → ∀ (G : Nat) (u : Equiv.Perm (Fin n)), PRep n w G u →
      G >>> (n * w) = 0 → u ∈ PS n w TR LR l d →
      siftK n w (mask w) (n * w) (pidn n w) LR TRI BP d l G = true := by
  obtain ⟨hn24, hw⟩ := szOK_facts hsz
  have hn : n < 2 ^ 32 := by omega
  have hw0 : 0 < w := PF.w_pos hw
  intro d
  induction d with
  | zero =>
    intro l _ _ G u hG hs hu
    rw [PS_zero, Set.mem_singleton_iff] at hu
    subst hu
    have e : G = pidn n w := PF.eq_of_fields hw0 hs (PF.pidn_shr hn24 hw) (fun x hx => by
      have h1 : pg w (mask w) G x = (((1 : Equiv.Perm (Fin n)) ⟨x, hx⟩ : Fin n) : Nat) :=
        hG ⟨x, hx⟩
      rw [h1, PF.pg_pidn hn24 hw hx]
      rfl)
    rw [siftK_zero, e]
    exact (bAnd_iff _ _).2 ⟨hsz, Nat.beq_refl _⟩
  | succ d ih =>
    intro l hlo hl G u hG hs hu
    rw [PS_succ, mem_TW] at hu
    obtain ⟨a, ha, v, hv, rfl⟩ := hu
    have hbl := hb l (by omega)
    have hvf := hfix l d hlo hl v hv ⟨_, hbl⟩ rfl
    have hpa := hP l (by omega) a ha
    have ept : pg w (mask w) G (pg w (mask w) BP l) = rpt w (mask w) (LR l) a := by
      have h1 : pg w (mask w) G (pg w (mask w) BP l) =
          (((tp n w TR (LR l) a * v) ⟨_, hbl⟩ : Fin n) : Nat) := hG ⟨_, hbl⟩
      rw [h1, Equiv.Perm.mul_apply, hvf]
      exact ht l hlo (by omega) a ha hbl
    rw [siftK_succ]
    simp only [strictB_eq, bIf_eq]
    rw [ept, hq l (by omega) a ha, if_pos (Nat.blt_eq.mpr ha)]
    have hG' := prep_pcomp hn (prep_pp hpa).2 hG
    simp only [tp, inv_mul_cancel_left] at hG'
    exact ih (l + 1) (by omega) (by omega) _ v hG' (PF.pcomp_shr _ _ hn hw0) hv

theorem step_of_schK {n w kS BP E j N CH T d : Nat} {S SI LR TR TRI : Nat → Nat}
    (hn24 : n < 16777216) (hw : n + 1 < 2 ^ w)
    (hpS : allN kS (fun l => permOK n w (mask w) (n * w) (S l) (SI l)) = true)
    (hT : ∀ jj < stCnt T, stAt T jj < kS + kS)
    (hP : ∀ l < E, ∀ k < rcnt (LR l), permOK n w (mask w) (n * w) (TR (roff n (n * w) (LR l) + k))
      (TRI (roff n (n * w) (LR l) + k)) = true)
    (hd : j + 1 + d = E) (hc : rcnt (LR j) ≤ N * CH)
    (hs : ∀ s < N, schK n w (mask w) (n * w) (pidn n w) S SI LR TR TRI kS BP E j T (s * CH) CH =
      true) :
    ∀ σ ∈ LT n w S kS T, ∀ a < rcnt (LR j), ∃ a' < rcnt (LR j), ∃ v ∈ PS n w TR LR (j + 1) d,
      σ * tp n w TR (LR j) a = tp n w TR (LR j) a' * v := by
  have hn : n < 2 ^ 32 := by omega
  rintro σ ⟨jj, hjj, rfl⟩ a ha
  obtain ⟨hk, hsift⟩ := schK_at hc hs ha jj hjj
  have e : Nat.sub E (Nat.succ j) = d := by
    simp only [Nat.sub_eq, Nat.succ_eq_add_one]
    omega
  rw [e] at hsift
  have hPG := prep_pcomp hn (prep_pp (hP j (by omega) _ hk)).2
    (prep_pcomp hn (prep_lp hpS (hT jj hjj)) (prep_pp (hP j (by omega) a ha)).1)
  have hm := mem_PS_of_sift hn24 hw hP d (j + 1) hd _ _ hPG hsift
  exact ⟨_, hk, _, hm, by unfold tp; rw [mul_inv_cancel_left]⟩

theorem tp_zero {n w kS root T R : Nat} {S SI TR TRI : Nat → Nat}
    (hl : levelK n w (mask w) (n * w) (mask (n * w)) (pidn n w) S SI TR TRI kS root T R = true) :
    tp n w TR R 0 = 1 := by
  obtain ⟨hsz, -, hR, h0, -, hperm⟩ := levelK_facts hl
  obtain ⟨hn24, hw⟩ := szOK_facts hsz
  have h1 : PRep n w (TR (roff n (n * w) R + 0)) 1 := by
    rw [Nat.add_zero, h0]
    exact prep_pidn hn24 hw
  exact prep_unique (prep_pp (hperm 0 hR.c_pos)).1 h1

theorem wordK_mem {n w : Nat} (hn24 : n < 16777216) (hw : n + 1 < 2 ^ w) {PS PSI : Nat → Nat}
    {j : Nat} {M : Submonoid (Equiv.Perm (Fin n))}
    (hS : ∀ h < j, ∃ g, PRep n w (PS h) g ∧ PRep n w (PSI h) g⁻¹ ∧ g ∈ M)
    (hinv : ∀ g ∈ M, g⁻¹ ∈ M) : ∀ wd : List Int, lettersK j wd = true →
      ∃ g, PRep n w (wordK n w (mask w) (pidn n w) PS PSI wd) g ∧ g ∈ M
  | [], _ => ⟨1, by rw [wordK_nil]; exact prep_pidn hn24 hw, M.one_mem⟩
  | z :: wd, hl => by
    rw [lettersK_cons, Bool.and_eq_true, Bool.and_eq_true, decide_eq_true_eq,
      decide_eq_true_eq] at hl
    obtain ⟨⟨hc0, hcj⟩, hl⟩ := hl
    obtain ⟨g, hg, hgm⟩ := wordK_mem hn24 hw hS hinv wd hl
    have h32 : n < 2 ^ 32 := by omega
    rw [wordK_cons]
    cases z with
    | ofNat k =>
      have ec : icode (Int.ofNat k) = k + k := rfl
      rw [ec] at hc0 hcj ⊢
      have e1 : Nat.land (k + k) 1 = 0 := by
        change (k + k) &&& 1 = 0
        rw [Nat.and_one_is_mod]
        omega
      have e2 : Nat.shiftRight (k + k) 1 = k := by
        rw [shr_eq]
        omega
      rw [e1, e2]
      obtain ⟨s, hs1, -, hsm⟩ := hS (k - 1) (by omega)
      exact ⟨s * g, prep_pcomp h32 hs1 hg, M.mul_mem hsm hgm⟩
    | negSucc k =>
      have ec : icode (Int.negSucc k) = (k + 1) + (k + 1) + 1 := rfl
      rw [ec] at hc0 hcj ⊢
      have e1 : Nat.land ((k + 1) + (k + 1) + 1) 1 = 1 := by
        change ((k + 1) + (k + 1) + 1) &&& 1 = 1
        rw [Nat.and_one_is_mod]
        omega
      have e2 : Nat.shiftRight ((k + 1) + (k + 1) + 1) 1 = k + 1 := by
        rw [shr_eq]
        omega
      rw [e1, e2]
      obtain ⟨s, -, hs2, hsm⟩ := hS k (by omega)
      exact ⟨s⁻¹ * g, prep_pcomp h32 hs2 hg, M.mul_mem (hinv _ hsm) hgm⟩

theorem gens_mem {n w kS kO nb BP TS : Nat} {S SI : Nat → Nat} {D : List (List Int)}
    (hh : headK n w (mask w) (n * w) (pidn n w) S SI kS kO D nb BP = true)
    (hTO : allN kO (fun j => anyLt (stCnt TS) (fun a => Nat.beq (stAt TS a) j)) = true) :
    ∀ j < kS, pp n w (S j) ∈ Submonoid.closure (LT n w S kS TS) := by
  unfold headK at hh
  simp only [bAnd_eq, Bool.and_eq_true] at hh
  obtain ⟨hsz, _, _, _, hperm, hder, _, _⟩ := hh
  obtain ⟨hn24, hw⟩ := szOK_facts hsz
  have hinvM : ∀ g ∈ Submonoid.closure (LT n w S kS TS), g⁻¹ ∈ Submonoid.closure (LT n w S kS TS) :=
    fun g hg => inv_mem_closure hg
  intro j
  induction j using Nat.strong_induction_on with
  | _ j ih =>
    intro hj
    by_cases hjk : j < kO
    · obtain ⟨a, ha, e⟩ := anyLt_spec (allN_iff.1 hTO j hjk)
      apply Submonoid.subset_closure
      refine ⟨a, ha, ?_⟩
      unfold lp
      rw [Nat.eq_of_beq_eq_true e, if_pos hj]
    · have := allN_iff.1 hder j hj
      rw [bIf_eq, ite_eq_right (by rw [blt_dec]; simpa using hjk), strictB_eq, Bool.and_eq_true,
        beq_dec, decide_eq_true_iff] at this
      obtain ⟨hl, he⟩ := this
      obtain ⟨g, hg, hgm⟩ := wordK_mem hn24 hw (j := j) (M := Submonoid.closure (LT n w S kS TS))
        (fun h hh' => ⟨pp n w (S h), (prep_pp (allN_iff.1 hperm h (by omega))).1,
          (prep_pp (allN_iff.1 hperm h (by omega))).2, ih h hh' (by omega)⟩) hinvM _ hl
      have hSj : PRep n w (wordK n w (mask w) (pidn n w) S SI (dword D kO j)) (pp n w (S j)) := by
        rw [← he]
        exact (prep_pp (allN_iff.1 hperm j hj)).1
      rw [prep_unique hSj hg]
      exact hgm

end CFSG.KS.Raw.Orb

end
