module

import CFSG.LocalAnalysis.GLTheoremA.CatA.S265ATwE6Inv
import CFSG.LocalAnalysis.GLTheoremA.CatA.D4TCore
public import CFSG.LocalAnalysis.GLTheoremA.CatA.S265QCfg
public import CFSG.LocalAnalysis.GLTheoremA.S3.ChevTools

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S265.TE6

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremA


theorem exists_fixed_involution_of_qsCfg_twE6 {Ω : Type} [Group Ω] [Finite Ω]
    {S B T : Subgroup Ω} {x : Ω} {D K : Subgroup Ω} (hc : QSCfg 3 S B T x D K)
    (hS : catalogIs (PSimple 3 S) S9.isTE6two) (hB : Nat.card B = 3 ^ 5)
    (hTB : ¬ (⁅T, B⁆ : Subgroup Ω) ≤ Subgroup.centralizer (S : Set Ω)) :
    ∃ v : PSimple 3 S, v * v = 1 ∧ v ≠ 1 ∧
      ∀ b ∈ B, ∀ hb : b ∈ Subgroup.normalizer (S : Set Ω), chevAut 3 S ⟨b, hb⟩ v = v := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hp : Nat.Prime 3 := Nat.prime_three
  have hSN : ∀ g : Ω, g ∈ Subgroup.normalizer (S : Set Ω) := fun g =>
    (Subgroup.normalizer_eq_top_iff.2 hc.normal) ▸ Subgroup.mem_top g
  have hX4 : 3 ^ 4 ≤
      Nat.card ((B.subgroupOf (Subgroup.normalizer (S : Set Ω))).map (chevAut 3 S)) := by
    have hker : (chevAut 3 S).ker ⊓ B.subgroupOf (Subgroup.normalizer (S : Set Ω)) =
        (Subgroup.zpowers x).subgroupOf (Subgroup.normalizer (S : Set Ω)) := by
      ext ⟨b, hb⟩
      simp only [Subgroup.mem_inf, MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
      refine ⟨fun ⟨h1, hbB⟩ =>
        (hc.centB b hbB).1 ((chevAut_eq_one_iff hp hc.comp hb).1 h1), fun hbx => ?_⟩
      have hbB : b ∈ B := Subgroup.zpowers_le.2 hc.xB hbx
      exact ⟨(chevAut_eq_one_iff hp hc.comp hb).2 ((hc.centB b hbB).2 hbx), hbB⟩
    have h1 := Subgroup.relIndex_mul_card (H := (chevAut 3 S).ker)
      (K := B.subgroupOf (Subgroup.normalizer (S : Set Ω)))
    rw [Subgroup.relIndex_ker, hker,
      D4T.card_subgroupOf_of_le (N := Subgroup.normalizer (S : Set Ω))
        (Y := Subgroup.zpowers x) (fun g _ => hSN g),
      D4T.card_subgroupOf_of_le (N := Subgroup.normalizer (S : Set Ω)) (Y := B)
        (fun g _ => hSN g),
      Nat.card_zpowers, orderOf_eq_prime (hc.elem.2 x hc.xB) hc.x1, hB] at h1
    norm_num at h1 ⊢
    omega
  have hO : GLAPPrimeCoreOf 3 S = ⊥ := by
    show (GLAPPrimeCore 3 ↥S).map S.subtype = ⊥
    rw [hc.core, Subgroup.map_bot]
  have hU : ∃ u ∈ (⁅T, B⁆ : Subgroup Ω), ∃ hu : u ∈ Subgroup.normalizer (S : Set Ω),
      chevAut 3 S ⟨u, hu⟩ ≠ 1 := by
    by_contra hcon
    push Not at hcon
    refine hTB fun u hu => ?_
    rw [Subgroup.mem_centralizer_iff]
    intro k hk
    have hk' := (centMod_iff.1 ((chevAut_eq_one_iff hp hc.comp (hSN u)).1
      (hcon u hu (hSN u)))).2 k hk
    rw [hO, Subgroup.mem_bot] at hk'
    exact commutatorElement_eq_one_iff_mul_comm.1 hk'
  obtain ⟨i, hi, hSi⟩ := hS
  cases i with
  | lie d =>
    have hd : ∃ q : TauCeti.PrimePower, d.1 = .twistedE6 q ∧ q.card = 2 := by
      obtain ⟨t, hv⟩ := d
      cases t with
      | twistedE6 q => exact ⟨q, rfl, by simpa [S9.isTE6two, onLie] using hi⟩
      | _ => simp [S9.isTE6two, onLie] at hi
    exact S265A.exists_fixed_involution_of_twE6 hc.normal hc.inn hc.elem d hd hSi hX4 hc.two
      hc.bnorm hU
  | cyclic _ _ => simp [S9.isTE6two, onLie] at hi
  | alternating _ _ => simp [S9.isTE6two, onLie] at hi
  | sporadic _ => simp [S9.isTE6two, onLie] at hi

end CFSG.LocalAnalysis.GLTheoremA.S265.TE6

end
