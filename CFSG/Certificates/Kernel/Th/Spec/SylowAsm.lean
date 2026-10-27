
module

public import CFSG.Certificates.Kernel.Th.Spec.SylowPc
public import CFSG.Certificates.Kernel.Th.S.SeedS
public import CFSG.Blueprint.NativeSporadic
import CFSG.Certificates.Kernel.Th.Spec.Seed
import CFSG.Certificates.Kernel.Th.Spec.SylowOrbitBase
import CFSG.Sporadic.Th.F2Spec

public section

open CFSG.KC.Th CFSG.KC.Th.BigS CFSG.KC.Th.Spec CFSG.Blueprint.NativeSporadic

namespace CFSG.KC.Th.Spec.SylowPc

theorem sylow_andB_iff {a b : Bool} : andB a b = true ↔ a = true ∧ b = true := by
  cases a <;> cases b <;> simp [andB]

theorem pkMat_seed {M : ℕ} {l : List Char} (h : SeedS.decOK M l = true) :
    pkMat M = decode 2 248 1 (String.ofList l) := by
  rw [(decOK_sound h).2, CFSG.Sporadic.Th.rowsMatrix_rowsOf]

variable {c rm tm0 tm1 tm2 tm3 tm4 tm5 tm6 tm7 up dg ONE : ℕ}

theorem sylow_pc_units (hk : constsOK c rm tm0 tm1 tm2 tm3 tm4 tm5 tm6 tm7 up dg ONE = true)
    {sA sB : String} {SA SB : ℕ} {RB PW : ℕ → ℕ} {PR n p pb : ℕ} {Cs1 Cs2 : List ℕ}
    (hSA : pkMat SA = decode 2 248 1 sA) (hSB : pkMat SB = decode 2 248 1 sB)
    (hAA : mulB c rm SA SA = ONE) (hBBB : mulB c rm (mulB c rm SB SB) SB = ONE)
    (h1 : RB 1 = SA) (h2 : RB 2 = SB) (hrun1 : 0 < runSlp RB c rm ONE Cs1 3)
    (hregs : regsIn PR n (runSlp RB c rm ONE Cs1 3) = true)
    (hn : n < 256) (hp : 2 ≤ p) (hpw : pwOK RB PW c rm PR n p = true)
    (hrun2 : runPc RB PW c rm ONE PR n p pb Cs2 1 = n + 1) :
    ∃ g : ℕ → (seedMonoid 2 248 1 sA sB)ˣ,
      (∀ k < n, unitsHom _ (g k) = pkMat (RB (regAt PR k))) ∧
        Nat.card (pcSub g n 0) ∣ p ^ n := by
  set S := seedMonoid 2 248 1 sA sB with hS
  have hAm : decode 2 248 1 sA ∈ S := Submonoid.subset_closure (Set.mem_insert _ _)
  have hBm : decode 2 248 1 sB ∈ S := Submonoid.subset_closure (Set.mem_insert_of_mem _ rfl)
  have hAA' : decode 2 248 1 sA * decode 2 248 1 sA = 1 := by
    rw [← hSA, ← pkMat_mulB hk, hAA, pkMat_one hk]
  have hBBB' : decode 2 248 1 sB * decode 2 248 1 sB * decode 2 248 1 sB = 1 := by
    rw [← hSB, ← pkMat_mulB hk, ← pkMat_mulB hk, hBBB, pkMat_one hk]
  obtain ⟨a, b, ha, hb⟩ := seed_units S hAm hBm hAA' hBBB'
  have hreg := regs_exist (unitsHom S) hk a b (by rw [ha, h1, hSA]) (by rw [hb, h2, hSB]) hrun1
  have hrg := CFSG.KC.Th.Spec.SylowOrbit.regsIn_spec hregs
  have hex : ∀ k < n, ∃ u : Sˣ, unitsHom S u = pkMat (RB (regAt PR k)) :=
    fun k hk' => hreg _ (hrg k hk').1 (hrg k hk').2
  classical
  let g : ℕ → Sˣ := fun k => if h : k < n then Classical.choose (hex k h) else 1
  have hg : ∀ k < n, unitsHom S (g k) = pkMat (RB (regAt PR k)) := by
    intro k hk'
    simp only [g, dif_pos hk']
    exact Classical.choose_spec (hex k hk')
  haveI := unitsHom_finite S
  exact ⟨g, hg, pc_card_dvd (unitsHom S) (unitsHom_injective S) hk hn hp g hg hpw hrun2⟩

theorem dvd_card_of_bounds {G : Type*} [Group G] (P : Subgroup G) {m : ℕ} (hm : 0 < m)
    (hup : Nat.card P ∣ m) (hlow : m ≤ Nat.card P) : m ∣ Nat.card G := by
  have h : Nat.card P = m := Nat.le_antisymm (Nat.le_of_dvd hm hup) hlow
  rw [← h]
  exact Subgroup.card_subgroup_dvd_card P

theorem sylow_sound_of_orbit (hk : constsOK c rm tm0 tm1 tm2 tm3 tm4 tm5 tm6 tm7 up dg ONE = true)
    {sA sB : String} {SA SB : ℕ} {RB PW : ℕ → ℕ} {PR n p pb : ℕ} {Cs1 Cs2 : List ℕ}
    (hSA : pkMat SA = decode 2 248 1 sA) (hSB : pkMat SB = decode 2 248 1 sB)
    (hAA : mulB c rm SA SA = ONE) (hBBB : mulB c rm (mulB c rm SB SB) SB = ONE)
    (h1 : RB 1 = SA) (h2 : RB 2 = SB) (hrun1 : 0 < runSlp RB c rm ONE Cs1 3)
    (hregs : regsIn PR n (runSlp RB c rm ONE Cs1 3) = true)
    (hn : n < 256) (hp : 2 ≤ p) (hpw : pwOK RB PW c rm PR n p = true)
    (hrun2 : runPc RB PW c rm ONE PR n p pb Cs2 1 = n + 1)
    (hlow : ∀ g : ℕ → (seedMonoid 2 248 1 sA sB)ˣ,
      (∀ k < n, unitsHom _ (g k) = pkMat (RB (regAt PR k))) → p ^ n ≤ Nat.card (pcSub g n 0)) :
    p ^ n ∣ Nat.card (seedMonoid 2 248 1 sA sB)ˣ := by
  obtain ⟨g, hg, hup⟩ := sylow_pc_units hk hSA hSB hAA hBBB h1 h2 hrun1 hregs hn hp hpw hrun2
  exact dvd_card_of_bounds (pcSub g n 0) (pow_pos (by omega : 0 < p) n) hup (hlow g hg)

end CFSG.KC.Th.Spec.SylowPc

end
