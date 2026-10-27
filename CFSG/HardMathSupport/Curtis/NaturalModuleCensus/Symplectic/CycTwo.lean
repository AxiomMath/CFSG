module

public import CFSG.LocalAnalysis.AGLEmbedding.BlockToralCensusBase
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanParabHub
public import CFSG.LocalAnalysis.ComponentInitial.SymplecticTorusWeylMatrices

public noncomputable section

namespace CFSG.HardMathSupport.Curtis.NaturalModuleCensus.Symplectic

open Matrix CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial
open CFSG.AGLEmbedding.ParabPrime (perfectJoin perfectJoin_le perfectJoin_perfect le_perfectJoin)
open CFSG.AGLEmbedding (CycPerfect)
open CFSG.LocalAnalysis.ComponentInitial.SymplecticTorusWeyl (torusHom)

variable {r : ℕ} {K : Type} [Field K]

theorem false_of_cyc_torus [Finite K] {p : ℕ} (hp : p.Prime) {J : Subgroup (StatedSp r K)}
    (hJ : CycPerfect p J) {d d' : Fin r → Kˣ} (hd : torusHom d ∈ perfectJoin J)
    (hd' : torusHom d' ∈ perfectJoin J) (hdp : d ^ p = 1) (hd'p : d' ^ p = 1) {ω : Kˣ}
    (hω : orderOf ω = p) {x : Fin r} (hx : d x = ω) (hx' : d' x = 1) (hd'1 : d' ≠ 1) : False := by
  classical
  set s : StatedSp r K := torusHom d with hs
  set t : StatedSp r K := torusHom d' with ht
  have hω1 : ω ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hω
    exact hp.one_lt.ne hω
  have hcomm : Commute s t := by
    show s * t = t * s
    rw [hs, ht, ← map_mul, ← map_mul, mul_comm d d']
  have hspow : s ^ p = 1 := by rw [hs, ← map_pow, hdp, map_one]
  have htpow : t ^ p = 1 := by rw [ht, ← map_pow, hd'p, map_one]
  have hS : ({s, t} : Set (StatedSp r K)).Pairwise Commute := by
    intro a ha b hb hab
    rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
    · exact absurd rfl hab
    · exact hcomm
    · exact hcomm.symm
    · exact absurd rfl hab
  set Q : Subgroup (StatedSp r K) := Subgroup.closure {s, t} with hQ
  have hQp : ∀ g ∈ Q, g ^ p = 1 := fun g hg =>
    CFSG.AGLEmbedding.ParabHub.pow_eq_one_of_mem_closure hS
      (fun a ha => by rcases ha with rfl | rfl <;> assumption) hg
  have hsQ : s ∈ Q := Subgroup.subset_closure (by simp)
  have htQ : t ∈ Q := Subgroup.subset_closure (by simp)
  have hQV : Q ≤ perfectJoin J := by
    refine (Subgroup.closure_le _).2 ?_
    rintro a (rfl | rfl)
    · exact hd
    · exact hd'
  have hpg : IsPGroup p Q := fun g => ⟨1, Subtype.ext (by
    simp [hQp g g.2])⟩
  have hcyc : IsCyclic Q := hJ _ (perfectJoin_le J) (perfectJoin_perfect J) Q hQV hpg
  have hs1 : s ≠ 1 := by
    intro h
    have : d = 1 := SymplecticTorusWeyl.torusHom_injective (by rw [← hs, h, map_one])
    apply hω1
    rw [← hx, this]
    rfl
  have hord : orderOf s = p := by
    rcases (Nat.dvd_prime hp).1 (orderOf_dvd_of_pow_eq_one hspow) with h | h
    · exact absurd (orderOf_eq_one_iff.1 h) hs1
    · exact h
  set sQ : Q := ⟨s, hsQ⟩ with hsQdef
  set tQ : Q := ⟨t, htQ⟩ with htQdef
  have hordQ : orderOf sQ = p := by
    rw [← hord, ← Subgroup.orderOf_coe]
  obtain ⟨g, hg⟩ := hcyc.exists_generator
  have hgp : g ^ p = 1 := Subtype.ext (hQp g g.2)
  have hcard : Nat.card Q = p := by
    apply Nat.dvd_antisymm
    · rw [← orderOf_eq_card_of_forall_mem_zpowers hg]
      exact orderOf_dvd_of_pow_eq_one hgp
    · rw [← hordQ]
      exact orderOf_dvd_natCard sQ
  have htop : Subgroup.zpowers sQ = ⊤ := by
    apply Subgroup.eq_top_of_card_eq
    rw [Nat.card_zpowers, hordQ, hcard]
  have htmem : tQ ∈ Subgroup.zpowers sQ := by rw [htop]; trivial
  obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.1 htmem
  have hmG : s ^ m = t := congrArg Subtype.val hm
  have hdm : d' = d ^ m := by
    apply SymplecticTorusWeyl.torusHom_injective
    rw [map_zpow]
    exact hmG.symm
  have hxm : ω ^ m = 1 := by
    have := congrFun hdm x
    rw [hx'] at this
    change 1 = (d x) ^ m at this
    rw [hx] at this
    exact this.symm
  have hpm : (p : ℤ) ∣ m := by
    rw [← hω]
    exact orderOf_dvd_iff_zpow_eq_one.2 hxm
  obtain ⟨k, hk⟩ := hpm
  apply hd'1
  rw [hdm, hk, _root_.zpow_mul, zpow_natCast, hdp, _root_.one_zpow]

end CFSG.HardMathSupport.Curtis.NaturalModuleCensus.Symplectic
