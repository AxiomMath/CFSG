module

public import CFSG.CGT.Foote82.T66.MC2Alt
import CFSG.CGT.Foote82.T66.MC2Perm
public import CFSG.RankThree.PartTwo.Sec19.SimsTheoremCTypes

public section

namespace CFSG.CGT.Foote82

namespace MC2

open CFSG.Open CFSG.Quasithin.G11 CFSG.RankThree.PartTwo Equiv

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]

theorem apply_apply_apply_of_pow_three {W : Type} [AddCommGroup W] [Module (ZMod 2) W]
    {f : GLV W} (hf : f ^ 3 = 1) (v : W) : f (f (f v)) = v := by
  have h := congrArg (fun g : GLV W => g v) hf
  simp only [pow_three] at h
  exact h

variable {G L : Subgroup (GLV V)} {s : GLV V} {ψ : ↥G ≃* alternatingGroup (Fin 11)}
  {F : Set (Fin 11)}

theorem fpf_of_double (h13 : A11DoubleThreeCycle) (h : StdForm G L s) (hd : AltData G L ψ F)
    (hdim : Module.finrank (ZMod 2) (TildeV L) = 4) (x : ↥L) (hx3 : x ^ 3 = 1)
    (hx : (hd.jL x).cycleType = {3, 3}) : ∀ v, rhoT L x v = v → v = 0 := by
  have hcube : ∀ v, (x : GLV V) ((x : GLV V) ((x : GLV V) v)) = v :=
    apply_apply_apply_of_pow_three (by rw [← Subgroup.coe_pow, hx3, Subgroup.coe_one])
  have h4 := h13 V G ψ h.extremal.setup.irr (Subgroup.inclusion hd.le x) hx
  have h4' : 4 ≤ Module.finrank (ZMod 2) ↥(comm1 (rhoT L x)) :=
    h4.trans (finrank_commSpace_le x hcube)
  have hle := Submodule.finrank_le (comm1 (rhoT L x))
  have htop : comm1 (rhoT L x) = ⊤ := Submodule.eq_top_of_finrank_eq (by omega)
  have hρ3 : ∀ v, rhoT L x (rhoT L x (rhoT L x v)) = v :=
    apply_apply_apply_of_pow_three (by rw [← map_pow, hx3, map_one])
  exact fpf_of_comm1_eq_top hρ3 htop

theorem cfix_eq_comm1_of_double (h13 : A11DoubleThreeCycle) (h : StdForm G L s)
    (hd : AltData G L ψ F) (hdim : Module.finrank (ZMod 2) (TildeV L) = 4) {a b : ↥L}
    (ha : a ^ 3 = 1) (hb : b ^ 3 = 1) (hab : a * b = b * a)
    (h1 : (hd.jL (a * b)).cycleType = {3, 3}) (h2 : (hd.jL (a * b * b)).cycleType = {3, 3}) :
    cfix (rhoT L a) = comm1 (rhoT L b) := by
  have hc : Commute a b := hab
  have hab3 : (a * b) ^ 3 = 1 := by rw [hc.mul_pow, ha, hb, one_mul]
  have habb3 : (a * b * b) ^ 3 = 1 := by
    have hc2 : Commute a (b * b) := hc.mul_right hc
    rw [mul_assoc, hc2.mul_pow, ha, one_mul, ← pow_two, ← pow_mul,
      show 2 * 3 = 3 * 2 from rfl, pow_mul, hb, one_pow]
  refine cfix_eq_comm1 (apply_apply_apply_of_pow_three (by rw [← map_pow, ha, map_one]))
    (apply_apply_apply_of_pow_three (by rw [← map_pow, hb, map_one])) (fun v => ?_)
    (fun v hv => fpf_of_double h13 h hd hdim _ hab3 h1 v (by rwa [map_mul]))
    (fun v hv => fpf_of_double h13 h hd hdim _ habb3 h2 v (by rwa [map_mul, map_mul]))
  have := congrArg (fun g : GLV (TildeV L) => g v) (congrArg (rhoT L) hab)
  simp only [map_mul] at this
  exact this

theorem case_a7four_eleven (h13 : A11DoubleThreeCycle) (h : StdForm G L s) (hd : AltData G L ψ F)
    (hF7 : F.ncard = 7) (hdim : Module.finrank (ZMod 2) (TildeV L) = 4) : False := by
  classical
  obtain ⟨p, hp, hpF⟩ := exists_injective_fin (S := F.toFinset) (k := 7)
    (by rw [← Set.ncard_eq_toFinset_card' F, hF7])
  have hpF' : ∀ i, p i ∈ F := fun i => Set.mem_toFinset.1 (hpF i)
  have mk : ∀ i j k : Fin 7, [i, j, k].Nodup → ∃ ℓ : ↥L, hd.jL ℓ = MC2.c3 (p i) (p j) (p k) := by
    intro i j k hn
    have hn' : [p i, p j, p k].Nodup := by simpa using hn.map hp
    simp only [List.nodup_cons, List.mem_cons, List.mem_singleton, not_or, List.not_mem_nil,
      not_false_eq_true, List.nodup_nil, and_true] at hn'
    exact hd.exists_jL_eq (c3_mem_altOn (hpF' i) (hpF' j) (hpF' k) hn'.1.1 hn'.1.2 hn'.2)
  choose! ℓ hℓ using mk
  have hcube : ∀ i j k : Fin 7, [i, j, k].Nodup → ℓ i j k ^ 3 = 1 := by
    intro i j k hn
    have hn' : [p i, p j, p k].Nodup := by simpa using hn.map hp
    simp only [List.nodup_cons, List.mem_cons, List.mem_singleton, not_or, List.not_mem_nil,
      not_false_eq_true, List.nodup_nil, and_true] at hn'
    apply hd.jL_injective
    rw [map_pow, hℓ i j k hn, map_one]
    exact c3_pow_three hn'.1.1 hn'.1.2 hn'.2
  have pair : ∀ i j k i' j' k' : Fin 7, [i, j, k, i', j', k'].Nodup →
      cfix (rhoT L (ℓ i j k)) = comm1 (rhoT L (ℓ i' j' k')) := by
    intro i j k i' j' k' hn
    have hn' : [p i, p j, p k, p i', p j', p k'].Nodup := by simpa using hn.map hp
    have h3 : [i, j, k].Nodup := (List.nodup_append.1 (show ([i, j, k] ++ [i', j', k']).Nodup
      from hn)).1
    have h3' : [i', j', k'].Nodup := (List.nodup_append.1 (show ([i, j, k] ++ [i', j', k']).Nodup
      from hn)).2.1
    have e1 := hℓ i j k h3
    have e2 := hℓ i' j' k' h3'
    refine cfix_eq_comm1_of_double h13 h hd hdim (hcube i j k h3) (hcube i' j' k' h3') ?_ ?_ ?_
    · apply hd.jL_injective
      rw [map_mul, map_mul, e1, e2]
      exact c3_commute hn'
    · rw [map_mul, e1, e2]
      exact cycleType_c3_mul hn'
    · rw [map_mul, map_mul, e1, e2]
      exact cycleType_c3_mul_sq hn'
  have htop := eq_bot_of_chain (e₁ := rhoT L (ℓ 0 1 2)) (e₂ := rhoT L (ℓ 3 4 5))
    (e₃ := rhoT L (ℓ 0 1 6)) (e₄ := rhoT L (ℓ 2 3 4)) (e₅ := rhoT L (ℓ 0 5 6))
    (e₆ := rhoT L (ℓ 1 2 3)) (e₇ := rhoT L (ℓ 4 5 6))
    (apply_apply_apply_of_pow_three (by rw [← map_pow, hcube 4 5 6 (by decide), map_one]))
    (pair 0 1 2 3 4 5 (by decide)) (pair 0 1 6 3 4 5 (by decide)) (pair 0 1 6 2 3 4 (by decide))
    (pair 0 5 6 2 3 4 (by decide)) (pair 0 5 6 1 2 3 (by decide)) (pair 4 5 6 1 2 3 (by decide))
    (pair 0 1 2 4 5 6 (by decide))
  have : Module.finrank (ZMod 2) (TildeV L) = 0 := by
    rw [← finrank_top (ZMod 2) (TildeV L), htop, finrank_bot]
  omega

theorem case_a7four (h13 : A11DoubleThreeCycle) {G L : Subgroup (GLV V)} {s : GLV V}
    (h : StdForm G L s) {m : ℕ} {ψ : ↥G ≃* alternatingGroup (Fin m)} {F : Set (Fin m)}
    (hd : AltData G L ψ F) (hA : IsA7FourModule L) : False := by
  obtain ⟨⟨α, hα⟩, hdim⟩ := hA
  have : Nontrivial (alternatingGroup (Fin 7)) := nontrivial_alt (by norm_num)
  have hcard := hd.card_eq_of_surjective α hα
  rw [CFSG.RankThree.PartTwo.Sec19.SimsTheoremC.card_alternatingGroup_fin (by norm_num)] at hcard
  have hF7 : F.ncard = 7 := factorial_div_two_inj (by have := hd.five_le; omega) (by norm_num) hcard
  have hm : m = 11 := by have := hd.card_add; omega
  subst hm
  exact case_a7four_eleven h13 h hd hF7 hdim

end MC2

end CFSG.CGT.Foote82
