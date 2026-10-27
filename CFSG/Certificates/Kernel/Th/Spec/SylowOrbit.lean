
module

public import CFSG.Certificates.Kernel.Th.Spec.SylowOrbitBase
import all CFSG.Certificates.Kernel.Th.Spec.SylowOrbitBase

public import CFSG.Certificates.Kernel.Th.Spec.FwdRel
public import CFSG.Certificates.Kernel.Th.S.DceS
public import CFSG.Certificates.Kernel.Th.S.SeedS
public import CFSG.Blueprint.NativeSporadic
import CFSG.Certificates.Kernel.Th.Spec.Seed
import CFSG.Certificates.Kernel.Th.Spec.FwdSlp
import CFSG.Certificates.Kernel.Th.Spec.DceMat
import CFSG.Certificates.Kernel.DceLoops
import CFSG.Certificates.Kernel.J4.ChainSound

public section

namespace CFSG.KC.Th.Spec.SylowOrbit

open CFSG.KC.Th CFSG.KC.Th.BigS CFSG.KC.Th.Spec CFSG.KC.Th.Spec.FwdRel

variable {c rm tm0 tm1 tm2 tm3 tm4 tm5 tm6 tm7 up dg ONE : ℕ}

local notation "𝕄" g:max =>
  ((Subtype.val g : GL (Fin 248) (ZMod 2)) : Matrix (Fin 248) (Fin 248) (ZMod 2))

theorem regIn_of_runSlp (hk : constsOK c rm tm0 tm1 tm2 tm3 tm4 tm5 tm6 tm7 up dg ONE = true)
    {J : Subgroup (GL (Fin 248) (ZMod 2))} {RB : ℕ → ℕ} {a b : J} (ha : 𝕄 a = pkMat (RB 1))
    (hb : 𝕄 b = pkMat (RB 2)) {cs : List ℕ} (hpos : 0 < runSlp RB c rm ONE cs 3) :
    ∀ r, 0 < r → r < runSlp RB c rm ONE cs 3 → RegIn (⊤ : Subgroup J) RB r := by
  have hS : ∀ k, 0 < k → k < 3 → RegIn (⊤ : Subgroup J) RB k := by
    intro k hk0 hk3
    obtain rfl | rfl : k = 1 ∨ k = 2 := by omega
    · exact ⟨a, Subgroup.mem_top a, ha⟩
    · exact ⟨b, Subgroup.mem_top b, hb⟩
  exact FwdSlp.runSlp_induct (RegIn (⊤ : Subgroup J) RB)
    (fun _ _ _ hx hy e => regIn_mul hk hx hy e)
    (fun _ _ _ hx _ he e => regIn_pow hk hx he e)
    (fun _ _ hx e => regIn_inv hk hx e) cs 3 hS hpos

theorem block_le (hk : constsOK c rm tm0 tm1 tm2 tm3 tm4 tm5 tm6 tm7 up dg ONE = true)
    {J : Subgroup (GL (Fin 248) (ZMod 2))} {RB : ℕ → ℕ} {PR n p BL b : ℕ}
    (hR : ∀ k < n, RegIn (⊤ : Subgroup J) RB (regAt PR k)) (hft : blkFr BL b ≤ blkTo BL b)
    (htn : blkTo BL b ≤ n) (hb : BlockOK RB rm PR n p BL b) :
    p ^ (blkTo BL b - blkFr BL b) * Nat.card (pcSub J RB PR (blkTo BL b) n) ≤
      Nat.card (pcSub J RB PR (blkFr BL b) n) := by
  haveI : Finite (GL (Fin 248) (ZMod 2)) := inferInstance
  obtain ⟨PT, TC, SC, SS, hPT0, hbase, htree, hsort, hsc⟩ := hb
  have hfix := baseFixed_spec hbase
  have hgood := tree_spec htree
  have hinj := sorted_spec hsort hsc
  have hpt : ∀ k, k < p ^ (blkTo BL b - blkFr BL b) → PT k < 2 ^ 248 := by
    intro k hklt
    rcases Nat.eq_zero_or_pos k with rfl | hk0
    · exact hPT0
    · obtain ⟨par, g, -, -, -, e⟩ := hgood k (by omega) hklt
      have hv := vecB_lt (c := c) (rm := rm) hk (PT par) (RB (regAt PR (g - 1)))
      rwa [e]
  have orb : ∀ k, k < p ^ (blkTo BL b - blkFr BL b) →
      ∃ x ∈ pcSub J RB PR (blkFr BL b) n,
        Matrix.vecMul (pkVec (PT 0)) (𝕄 x) = pkVec (PT k) := by
    intro k
    induction k using Nat.strong_induction_on with
    | _ k ih =>
      intro hklt
      rcases Nat.eq_zero_or_pos k with rfl | hk0
      · exact ⟨1, Subgroup.one_mem _, by rw [mat_one, Matrix.vecMul_one]⟩
      · obtain ⟨par, g, hpar, hfr, hgto, e⟩ := hgood k (by omega) hklt
        obtain ⟨x, hx, hxr⟩ := ih par hpar (by omega)
        have hg1n : g - 1 < n := by omega
        obtain ⟨u, -, hu⟩ := hR (g - 1) hg1n
        refine ⟨x * u, mul_mem hx (Subgroup.subset_closure
          ⟨g - 1, by omega, hg1n, hu⟩), ?_⟩
        rw [mat_mul, ← Matrix.vecMul_vecMul, hxr, hu, ← pkVec_vecB hk, e]
  have orb' : ∀ k, ∃ x ∈ pcSub J RB PR (blkFr BL b) n,
      k < p ^ (blkTo BL b - blkFr BL b) →
        Matrix.vecMul (pkVec (PT 0)) (𝕄 x) = pkVec (PT k) := by
    intro k
    by_cases hklt : k < p ^ (blkTo BL b - blkFr BL b)
    · obtain ⟨x, hx, hxv⟩ := orb k hklt
      exact ⟨x, hx, fun _ => hxv⟩
    · exact ⟨1, Subgroup.one_mem _, fun h => absurd h hklt⟩
  choose x hx hxv using orb'
  let A : CFSG.Certificates.J4Chain.RightAct J (Fin 248 → ZMod 2) :=
    ⟨fun v g => Matrix.vecMul v (𝕄 g), fun v => by rw [mat_one, Matrix.vecMul_one],
      fun v g h => by rw [mat_mul, Matrix.vecMul_vecMul]⟩
  have key := CFSG.Certificates.J4Chain.card_mul_le_of_orbit A (pcSub J RB PR (blkFr BL b) n)
    (pkVec (PT 0)) (p ^ (blkTo BL b - blkFr BL b)) x (fun k _ => hx k) fun k hklt j hjlt e =>
      hinj k hklt j hjlt (pkVec_inj (hpt k hklt) (hpt j hjlt)
        (by
          have e' : Matrix.vecMul (pkVec (PT 0)) (𝕄 (x k)) =
              Matrix.vecMul (pkVec (PT 0)) (𝕄 (x j)) := e
          rw [← hxv k hklt, ← hxv j hjlt]
          exact e'))
  have hle : pcSub J RB PR (blkTo BL b) n ≤
      A.fixSub {pkVec (PT 0)} ⊓ pcSub J RB PR (blkFr BL b) n := by
    refine le_inf ?_ (pcSub_anti hft)
    refine (Subgroup.closure_le _).2 ?_
    rintro g ⟨k, htk, hklt, hg⟩
    refine A.mem_fixSub.2 fun a ha => ?_
    rw [Set.mem_singleton_iff.1 ha]
    change Matrix.vecMul (pkVec (PT 0)) (𝕄 g) = pkVec (PT 0)
    rw [hg, ← pkVec_vecB hk, hfix k hklt htk]
  calc p ^ (blkTo BL b - blkFr BL b) * Nat.card (pcSub J RB PR (blkTo BL b) n)
      ≤ p ^ (blkTo BL b - blkFr BL b) * Nat.card (A.fixSub {pkVec (PT 0)} ⊓
          pcSub J RB PR (blkFr BL b) n : Subgroup J) :=
        Nat.mul_le_mul_left _ (Subgroup.card_le_of_le hle)
    _ ≤ _ := key

theorem pow_le_card_pcSub (hk : constsOK c rm tm0 tm1 tm2 tm3 tm4 tm5 tm6 tm7 up dg ONE = true)
    {J : Subgroup (GL (Fin 248) (ZMod 2))} {RB : ℕ → ℕ} {PR n p BL nb : ℕ}
    (hR : ∀ k < n, RegIn (⊤ : Subgroup J) RB (regAt PR k)) (hbl : blocksOK BL nb n = true)
    (hblk : ∀ b < nb, BlockOK RB rm PR n p BL b) :
    p ^ n ≤ Nat.card (pcSub J RB PR 0 n) := by
  haveI : Finite (GL (Fin 248) (ZMod 2)) := inferInstance
  have hok : andB (Nat.blt (nat_lit 0) (blkAcc BL nb))
      (Nat.beq (Nat.sub (blkAcc BL nb) (nat_lit 1)) n) = true := hbl
  obtain ⟨hok1, hok2⟩ := CFSG.KC.Th.Spec.Dce.andB_iff.1 hok
  have hfin : 0 < blkAcc BL nb ∧ blkAcc BL nb - 1 = n :=
    ⟨Nat.blt_eq.mp hok1, Nat.eq_of_beq_eq_true hok2⟩
  have step : ∀ b ≤ nb, 0 < blkAcc BL b →
      p ^ (blkAcc BL b - 1) * Nat.card (pcSub J RB PR (blkAcc BL b - 1) n) ≤
        Nat.card (pcSub J RB PR 0 n) := by
    intro b
    induction b with
    | zero =>
      intro _ _
      change p ^ (1 - 1) * Nat.card (pcSub J RB PR (1 - 1) n) ≤
        Nat.card (pcSub J RB PR 0 n)
      simp
    | succ b ih =>
      intro hb h
      obtain ⟨h0, hfr, hlt, hacc⟩ := blkAcc_succ (b := b) h
      have ih' := ih (by omega) h0
      have htn : blkTo BL b ≤ n := by
        have hle := blkAcc_le (BL := BL) hfin.1 (show b + 1 ≤ nb by omega)
        rw [hacc] at hle
        omega
      have hblock := block_le hk hR (Nat.le_of_lt hlt) htn (hblk b (by omega))
      rw [hacc, Nat.add_sub_cancel]
      rw [← hfr] at ih'
      calc p ^ blkTo BL b * Nat.card (pcSub J RB PR (blkTo BL b) n)
          = p ^ blkFr BL b * (p ^ (blkTo BL b - blkFr BL b) *
              Nat.card (pcSub J RB PR (blkTo BL b) n)) := by
            rw [← Nat.mul_assoc, ← Nat.pow_add, Nat.add_sub_cancel' hlt.le]
        _ ≤ p ^ blkFr BL b * Nat.card (pcSub J RB PR (blkFr BL b) n) :=
            Nat.mul_le_mul_left _ hblock
        _ ≤ _ := ih'
  have h := step nb le_rfl hfin.1
  rw [hfin.2] at h
  have h1 : 0 < Nat.card (pcSub J RB PR n n) := by
    haveI : Nonempty (pcSub J RB PR n n) := ⟨1⟩
    exact Nat.card_pos
  calc p ^ n = p ^ n * 1 := (Nat.mul_one _).symm
    _ ≤ p ^ n * Nat.card (pcSub J RB PR n n) := Nat.mul_le_mul_left _ h1
    _ ≤ _ := h

theorem pow_le_card_closure (hk : constsOK c rm tm0 tm1 tm2 tm3 tm4 tm5 tm6 tm7 up dg ONE = true)
    {G : Type*} [Group G] {φ : G →* Matrix (Fin 248) (Fin 248) (ZMod 2)}
    (hφ : Function.Injective φ) {RB : ℕ → ℕ} {PR n p BL nb : ℕ} {g : ℕ → G}
    (hg : ∀ k < n, φ (g k) = pkMat (RB (regAt PR k))) (hbl : blocksOK BL nb n = true)
    (hblk : ∀ b < nb, BlockOK RB rm PR n p BL b) :
    p ^ n ≤ Nat.card (Subgroup.closure (g '' Set.Ico 0 n)) := by
  let ψ : G →* GL (Fin 248) (ZMod 2) := φ.toHomUnits
  have hψ : Function.Injective ψ := by
    intro x y h
    apply hφ
    have h' := congrArg (fun u : GL (Fin 248) (ZMod 2) =>
      ((u : GL (Fin 248) (ZMod 2)) : Matrix (Fin 248) (Fin 248) (ZMod 2))) h
    simpa [ψ, MonoidHom.coe_toHomUnits] using h'
  have hmat : ∀ k < n, ((ψ (g k) : GL (Fin 248) (ZMod 2)) :
      Matrix (Fin 248) (Fin 248) (ZMod 2)) = pkMat (RB (regAt PR k)) := by
    intro k hklt
    simpa [ψ, MonoidHom.coe_toHomUnits] using hg k hklt
  have hR : ∀ k < n, RegIn (⊤ : Subgroup ψ.range) RB (regAt PR k) := by
    intro k hklt
    exact ⟨⟨ψ (g k), MonoidHom.mem_range.mpr ⟨g k, rfl⟩⟩, Subgroup.mem_top _,
      hmat k hklt⟩
  have h := pow_le_card_pcSub (J := ψ.range) hk hR hbl hblk
  rw [card_pcSub_eq_closure hψ hmat] at h
  exact h

end CFSG.KC.Th.Spec.SylowOrbit

end
