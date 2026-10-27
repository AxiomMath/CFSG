module

public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.ShapeCPrimeCases
public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.Stage1Lin

public section

namespace CFSG.EvenSmallLie.OmegaEight.CPrime

open Subgroup Matrix CFSG.EvenSmallLie.UnitarySix.YamadaPar CFSG.EvenSmallLie.OmegaEight.Stage1

variable {G : Type*} [Group G]

@[expose] def sigmaV (ε : Eps) (w : ℕ) (x : V6) : V6 := toMat 6 6 (reflRows ε w) *ᵥ x + toVec 6 w

theorem reflB_lt (ε : Eps) {v x : ℕ} (hv : v < 64) (hx : x < 64) : reflB ε v x < 64 := by
  unfold reflB
  split_ifs
  · exact Nat.xor_lt_two_pow (n := 6) hx hv
  · rw [Nat.xor_zero]; exact hx

theorem sigmaV_zero (ε : Eps) (w : ℕ) : sigmaV ε w 0 = toVec 6 w := by
  rw [sigmaV, mulVec_zero, zero_add]

theorem sigmaV_add3 (ε : Eps) (w : ℕ) (x y z : V6) :
    sigmaV ε w (x + y + z) = sigmaV ε w x + sigmaV ε w y + sigmaV ε w z := by
  simp only [sigmaV, mulVec_add]
  have h := add_self_V6 (toVec 6 w)
  calc toMat 6 6 (reflRows ε w) *ᵥ x + toMat 6 6 (reflRows ε w) *ᵥ y +
        toMat 6 6 (reflRows ε w) *ᵥ z + toVec 6 w =
      toMat 6 6 (reflRows ε w) *ᵥ x + toMat 6 6 (reflRows ε w) *ᵥ y +
        toMat 6 6 (reflRows ε w) *ᵥ z + (toVec 6 w + toVec 6 w) + toVec 6 w := by
          rw [h, add_zero]
    _ = _ := by abel

section Sigma


theorem sigmaV_eq (ε : Eps) {w : ℕ} (hw : w < 64) (x : V6) :
    sigmaV ε w x = toVec 6 (reflB ε w (vecBits x) ^^^ w) := by
  rw [sigmaV, mulVec_reflRows ε hw, toVec_xor]

theorem mulVec_reflRows_toVec (ε : Eps) {v x : ℕ} (hv : v < 64) (hx : x < 64) :
    toMat 6 6 (reflRows ε v) *ᵥ toVec 6 x = toVec 6 (reflB ε v x) := by
  rw [mulVec_reflRows ε hv, vecBits_toVec hx]

theorem sigma_facts (ε : Eps) {v : ℕ} (hv : v < 64) (hq : qfB ε v = true) :
    coneW ε v < 64 ∧ coneW ε v ≠ 0 ∧ qfB ε (coneW ε v) = false ∧ bfB ε (coneW ε v) v = false ∧
      ∀ x < 64, qfB ε (reflB ε (coneW ε v) x ^^^ coneW ε v) = qfB ε x ∧
        reflB ε (coneW ε v) (reflB ε v x) ^^^ coneW ε v =
          reflB ε v (reflB ε (coneW ε v) x ^^^ coneW ε v) ∧
        reflB ε (coneW ε v) (reflB ε (coneW ε v) x ^^^ coneW ε v) ^^^ coneW ε v = x := by
  have h := (cprimeChecks ε).2.2.1
  simp only [sigmaCheck, List.all_eq_true, List.mem_range, Bool.or_eq_true, Bool.not_eq_true',
    Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, bne_iff_ne, ne_eq] at h
  rcases h v hv with h | ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩
  · rw [hq] at h; exact absurd h (by decide)
  · exact ⟨h1, h2, h3, h4, fun x hx => ⟨(h5 x hx).1.1, (h5 x hx).1.2, (h5 x hx).2⟩⟩

variable {ε : Eps} {v : ℕ} (hv : v < 64) (hq : qfB ε v = true)
include hv hq

theorem sigmaV_invol (x : V6) : sigmaV ε (coneW ε v) (sigmaV ε (coneW ε v) x) = x := by
  obtain ⟨hw, -, -, -, h⟩ := sigma_facts ε hv hq
  rw [sigmaV_eq ε hw, sigmaV_eq ε hw, vecBits_toVec (Nat.xor_lt_two_pow (n := 6)
    (reflB_lt ε hw (vecBits_lt x)) hw), (h _ (vecBits_lt x)).2.2, toVec_vecBits]

theorem qfV_sigmaV (x : V6) : qfV ε (sigmaV ε (coneW ε v) x) = qfV ε x := by
  obtain ⟨hw, -, -, -, h⟩ := sigma_facts ε hv hq
  rw [sigmaV_eq ε hw, qfV_toVec ε (Nat.xor_lt_two_pow (n := 6) (reflB_lt ε hw (vecBits_lt x)) hw),
    (h _ (vecBits_lt x)).1, qfV]

theorem sigmaV_refl (x : V6) :
    sigmaV ε (coneW ε v) (toMat 6 6 (reflRows ε v) *ᵥ x) =
      toMat 6 6 (reflRows ε v) *ᵥ sigmaV ε (coneW ε v) x := by
  obtain ⟨hw, -, -, -, h⟩ := sigma_facts ε hv hq
  have hx := vecBits_lt x
  rw [mulVec_reflRows ε hv, sigmaV_eq ε hw, vecBits_toVec (reflB_lt ε hv hx), sigmaV_eq ε hw,
    mulVec_reflRows ε hv, vecBits_toVec (Nat.xor_lt_two_pow (n := 6) (reflB_lt ε hw hx) hw),
    (h _ hx).2.1]

theorem sigma_mem_affGroup :
    Function.Involutive.toPerm (sigmaV ε (coneW ε v)) (sigmaV_invol hv hq) ∈ affGroup ε :=
  ⟨fun x => qfV_sigmaV hv hq x, fun x y z => sigmaV_add3 ε _ x y z⟩

end Sigma

namespace Setting

variable {ε : Eps} {t : G} {L U Q P : Subgroup G} {a : G} {ψ : V6 → G} {p : Fin 6 → G} {c : G}
  {v₀ : ℕ} (hS : Setting ε t L U Q P a ψ p c v₀)
include hS

theorem false_of_Zset_zeroSet [Finite G]
    (hZ : ∀ v, v ∈ Zset t Q ψ ↔ qfV ε v = 0) : False := by
  classical
  have hZ' : ∀ s, qfV ε s = 0 → s ∈ Zset t Q ψ := fun s hs => (hZ s).2 hs
  have hM : hS.affHom.range ≤ affGroup ε := by
    rintro σ ⟨g, rfl⟩
    refine ⟨fun v => ?_, fun x y z => hS.aff_add3 g.2 x y z⟩
    change qfV ε (aff t ψ g v) = qfV ε v
    have h1 : aff t ψ g v ∈ Zset t Q ψ ↔ v ∈ Zset t Q ψ := by
      refine ⟨fun h => ?_, fun h => hS.aff_mem_Zset hZ' g.2 h⟩
      have h2 := hS.aff_mem_Zset hZ' (inv_mem g.2) h
      rwa [← hS.aff_mul (inv_mem g.2) g.2, inv_mul_cancel, hS.aff_one] at h2
    rw [hZ, hZ] at h1
    rcases qfV_cases ε v with h | h <;> rcases qfV_cases ε (aff t ψ g v) with h' | h'
    · rw [h, h']
    · exact absurd (h1.2 h) (by rw [h']; exact one_ne_zero)
    · exact absurd (h1.1 h') (by rw [h]; exact one_ne_zero)
    · rw [h, h']
  have hcardZ : Nat.card (Zset t Q ψ) = (zeroSet ε).card := by
    have hset : Zset t Q ψ = ↑(zeroSet ε) := by
      ext v
      simp only [hZ, zeroSet, Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq]
    rw [hset, Nat.card_coe_set_eq, Set.ncard_coe_finset]
  have hge : Nat.card (affGroup ε) ≤ Nat.card hS.affHom.range :=
    (card_affGroup_le ε).trans (hcardZ ▸ hS.le_card_range hZ')
  have hEq : hS.affHom.range = affGroup ε := Subgroup.eq_of_le_of_card_ge hM hge
  have hv₀ := hS.data.v₀_lt
  have hq₀ := hS.data.v₀_nonsingular
  obtain ⟨hw, hw0, hwq, -, -⟩ := sigma_facts ε hv₀ hq₀
  have hσ := sigma_mem_affGroup hv₀ hq₀
  rw [← hEq] at hσ
  obtain ⟨g, hg⟩ := hσ
  have hgv : ∀ x, aff t ψ g x = sigmaV ε (coneW ε v₀) x := fun x =>
    congrArg (fun σ : Equiv.Perm V6 => σ x) hg
  have hcomm : ∀ x, aff t ψ g (aff t ψ c x) = aff t ψ c (aff t ψ g x) := fun x => by
    rw [hS.aff_c, hS.aff_c, hgv, hgv, sigmaV_refl hv₀ hq₀]
  rcases hS.square_root g.2 hcomm with h | h <;> rw [hgv, sigmaV_zero] at h
  · apply hw0
    exact toVec_injective hw (by norm_num) (h.trans (by ext i; simp [toVec]))
  · have := toVec_injective hw hv₀ h
    rw [this, hq₀] at hwq
    exact absurd hwq (by decide)

end Setting

end CFSG.EvenSmallLie.OmegaEight.CPrime
