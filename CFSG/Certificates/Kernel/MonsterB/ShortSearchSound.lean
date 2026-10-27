module

public import CFSG.Certificates.Kernel.MonsterB.KSearchSound
public import Certificates.Data.CFSGNative.MonsterB.Short
public import CFSG.Monster.VisCert.FrameSpec
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Tactic.NormNum.Abs
import Mathlib.Tactic.NormNum.DivMod
import Mathlib.Tactic.NormNum.OfScientific
import Mathlib.Tactic.NormNum.Pow

public section

namespace CFSG.KC.KSearch

open CFSG.Monster.VisCert CFSG.Monster.VisCert.Native CFSG.Monster.B.Short.Native CFSG.KC.Bfs

theorem frameTabs_size : (frameRows.map fastTables).size = 15 := by
  rw [Array.size_map]
  rfl

theorem frameTabs_get {g : ℕ} (hg : g < 15) :
    (frameRows.map fastTables)[g]! = fastTables frameRows[g]! := by
  have h : g < frameRows.size := hg
  rw [getElem!_pos _ g (by rw [Array.size_map]; exact h), getElem!_pos frameRows g h,
    Array.getElem_map]

theorem fastAct_frame {g v : ℕ} (hg : g < 15) (hv : v < 2 ^ 24) :
    fastAct (frameRows.map fastTables)[g]! v = gimg g v := by
  rw [frameTabs_get hg, fastAct_fastTables _ hv]
  rfl

@[expose] abbrev shortF (g v : ℕ) : ℕ := fastAct (frameRows.map fastTables)[g]! v

theorem shortTables_eq : shortTables = ⟨(kRun shortF 15 (1 <<< 24) 12288).1,
    (kRun shortF 15 (1 <<< 24) 12288).2.1, (kRun shortF 15 (1 <<< 24) 12288).2.2.1⟩ := by
  unfold shortTables
  change (match kSearch (frameRows.map fastTables) 12288 with
    | (klev, klab, kpar, _) => (⟨klev, klab, kpar⟩ : ShortTables)) = _
  rw [kSearch_eq]
  generalize hk : kRun (fun g v => fastAct (frameRows.map fastTables)[g]! v)
    (frameRows.map fastTables).size (1 <<< 24) 12288 = r
  have hk' : kRun shortF 15 (1 <<< 24) 12288 = r := by
    rw [← hk, frameTabs_size]
  rw [hk']

theorem parAll_of_all {n chunks : ℕ} {p : ℕ → Bool} (h : ∀ i, p i = true) :
    parAll n chunks p = true := by
  unfold parAll
  rw [List.all_eq_true]
  intro x hx
  obtain ⟨j, -, rfl⟩ := List.mem_map.1 hx
  exact (allFrom_iff p _ _).2 fun k _ => h _

theorem shortCertOK_of_orbit (S : Finset ℕ) (hS : ∀ u, Reach gimg 15 12288 u ↔ u ∈ S)
    (hcard : S.card = 98280) (hD : ∀ u ∈ S, RIn gimg 15 12288 253 u) : shortCertOK = true := by
  have hN : (1 <<< 24 : ℕ) = 2 ^ 24 := by norm_num
  have hFG : ∀ g < 15, ∀ v < 1 <<< 24, shortF g v = gimg g v := fun g hg v hv =>
    fastAct_frame hg (by rw [← hN]; exact hv)
  have hG : ∀ g < 15, ∀ v < 1 <<< 24, gimg g v < 1 <<< 24 := fun g hg v _ => by
    rw [hN]
    exact gimg_lt hg v
  have hseed : (12288 : ℕ) < 1 <<< 24 := by rw [hN]; norm_num
  have hR := reach_congr hseed hG hFG
  obtain ⟨hsz, hne, h1, htree⟩ := kRun_spec (F := shortF) (m := 15) (N := 1 <<< 24)
    (seed := 12288) hseed (fun g hg v hv => by rw [hFG g hg v hv]; exact hG g hg v hv)
    (by norm_num) (by norm_num)
    ⟨S, fun u hu => (hS u).1 ((hR u).1 hu), by rw [hcard, hN]; norm_num⟩
    (fun u hu => rin_congr hseed hG hFG (hD u ((hS u).1 ((hR u).1 hu))))
  unfold shortCertOK shortCheck
  rw [shortTables_eq]
  generalize kRun shortF 15 (1 <<< 24) 12288 = r at hsz hne h1 htree ⊢
  obtain ⟨lev, lab, par, q, qh⟩ := r
  dsimp only at hsz hne h1 htree ⊢
  have hpt : ∀ v, shortPointOK ⟨lev, lab, par⟩ v = true := by
    intro v
    unfold shortPointOK
    dsimp only
    by_cases h0 : rd8 lev v = 0
    · rw [h0]
      rfl
    · rw [if_neg (by simpa using h0)]
      have hv := (hne v).1 h0
      by_cases hl : rd8 lev v = 1
      · rw [if_pos (by simpa using hl)]
        have := ((h1 v hv).1 hl)
        simp only [shortSeed, this, beq_self_eq_true]
      · rw [if_neg (by simpa using hl)]
        have hvs : v ≠ 12288 := fun e => hl ((h1 v hv).2 e)
        obtain ⟨hp, hg, hf, hlev⟩ := htree v hv hvs
        rw [← hFG _ hg _ hp, hf, hlev]
        have hp' : rd32 par v < 2 ^ 24 := by rw [← hN]; exact hp
        simp only [decide_eq_true hp', decide_eq_true hg, beq_self_eq_true, Bool.and_self]
  have hcnt : countBelow (fun v => rd8 lev v != 0) (2 ^ 24) = 98280 := by
    rw [countBelow_eq, ← hcard]
    congr 1
    ext u
    simp only [Finset.mem_filter, Finset.mem_range, bne_iff_ne, ne_eq, ]
    constructor
    · rintro ⟨-, h⟩
      exact (hS u).1 ((hR u).1 ((hne u).1 h))
    · intro hu
      have h := (hne u).2 ((hR u).2 ((hS u).2 hu))
      refine ⟨?_, h⟩
      by_contra hc
      exact h (rd8_of_le (by rw [hsz, hN]; omega))
  rw [Bool.and_eq_true]
  exact ⟨parAll_of_all hpt, by rw [hcnt]; rfl⟩

end CFSG.KC.KSearch

end
