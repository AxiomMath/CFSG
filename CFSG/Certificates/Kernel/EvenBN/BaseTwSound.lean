module

public import Certificates.Data.Kernel.EvenBN.BaseTw
public import CFSG.Certificates.Kernel.SporSch.TitsCntSound
import CFSG.Certificates.Kernel.Spor.RawSiftK

public section

namespace CFSG.KS.SporSch

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim
open CFSG.Certificates.Native CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Sporadic.Schreier.Tits

variable {BP : Nat} {base : Array Nat}

theorem baseTw_of_sep {G : Subgroup (Equiv.Perm (Fin 1755))}
    (hsep : ∀ γ ∈ G, (∀ t < 5, ∀ h : base[t]! < 1755, γ ⟨base[t]!, h⟩ = ⟨base[t]!, h⟩) → γ = 1)
    (hbl : ∀ t < 5, base[t]! < 1755) (hBP : ∀ t < 5, base[t]! = pg 11 (mask 11) BP t)
    {X Y Z : Array Nat} {σ τ ρ : Equiv.Perm (Fin 1755)} (hX : Rep 1755 X σ) (hY : Rep 1755 Y τ)
    (hZ : Rep 1755 Z ρ) (hσ : σ ∈ G) (hτ : τ ∈ G) (hρ : ρ ∈ G) {gx gy gz : Nat → Nat}
    (hgx : ∀ i < 1755, gx i = X[i]!) (hgy : ∀ i < 1755, gy i = Y[i]!)
    (hgz : ∀ i < 1755, gz i = Z[i]!) :
    baseTw BP 5 gx gy gz = eqA 1755 (compA 1755 X Y) (compA 1755 Z X) := by
  rw [Bool.eq_iff_iff, eqA_iff (rep_compA hX hY) (rep_compA hZ hX)]
  have hpt : ∀ t (ht : t < 5), gx (gy base[t]!) = ((σ * τ) ⟨base[t]!, hbl t ht⟩ : Nat) ∧
      gz (gx base[t]!) = ((ρ * σ) ⟨base[t]!, hbl t ht⟩ : Nat) := by
    intro t ht
    have hb := hbl t ht
    rw [hgy _ hb, hY.apply hb, hgx _ (τ _).2, hX.apply (τ _).2, hgx _ hb, hX.apply hb,
      hgz _ (σ _).2, hZ.apply (σ _).2]
    exact ⟨rfl, rfl⟩
  constructor
  · intro h
    have hfix : ∀ t < 5, ∀ hb : base[t]! < 1755,
        ((ρ * σ)⁻¹ * (σ * τ)) ⟨base[t]!, hb⟩ = ⟨base[t]!, hb⟩ := by
      intro t ht hb
      have := allN_spec h t ht
      rw [strictB_eq, ← hBP t ht, Nat.beq_eq, (hpt t ht).1, (hpt t ht).2] at this
      rw [Equiv.Perm.mul_apply, Equiv.Perm.inv_eq_iff_eq]
      exact Fin.ext this
    have h1 := hsep _ (G.mul_mem (G.inv_mem (G.mul_mem hρ hσ)) (G.mul_mem hσ hτ)) hfix
    exact inv_mul_eq_one.1 h1 |>.symm
  · intro h
    unfold baseTw
    refine allN_of_forall fun t ht => ?_
    rw [strictB_eq, ← hBP t ht, Nat.beq_eq, (hpt t ht).1, (hpt t ht).2, h]

theorem baseTwG_eq {kS kO NS CH Y Z t0 t1 t2 t3 t4 : Nat} {PS PSI LR TR TRI : Nat → Nat}
    {S : Array (Array Nat)} {D : List (List Int)}
    (hb : Binds 1755 11 PS kS 5 BP S base)
    (hh : headK 1755 11 (mask 11) (1755 * 11) (pidn 1755 11) PS PSI kS kO D 5 BP = true)
    (hl : LevelsOK 1755 11 PS PSI LR TR TRI kS 5 BP) (hNS : 1755 ≤ NS * CH)
    (hs : ∀ i < 5, ∀ s < NS, schK 1755 11 (mask 11) (1755 * 11) (pidn 1755 11) PS PSI LR TR TRI
      kS BP 5 i (stepsAt 1755 11 PS kS BP i) (s * CH) CH = true)
    (hnd : base.toList.Nodup)
    (htr : IsTr5 LR TR t0 t1 t2 t3 t4)
    (hYc : canonK 1755 11 (mask 11) (1755 * 11) Y = true)
    (hY : siftA 1755 (rawLevels 1755 S base) base 0 (unpack 1755 11 Y) = true)
    (hZc : canonK 1755 11 (mask 11) (1755 * 11) Z = true)
    (hZ : siftA 1755 (rawLevels 1755 S base) base 0 (unpack 1755 11 Z) = true) :
    baseTw BP 5 (gptR t0 t1 t2 t3 t4) (pgR Y) (pgR Z) =
      eqA 1755 (compA 1755 (unpack 1755 11 (prod5K 1755 11 (mask 11) t0 t1 t2 t3 t4)) (unpack 1755 11 Y))
        (compA 1755 (unpack 1755 11 Z) (unpack 1755 11 (prod5K 1755 11 (mask 11) t0 t1 t2 t3 t4))) := by
  have hp := (Raw.Orb.head_facts hh).1
  obtain ⟨G, hmem, hsep⟩ := chain_group hb hh hl hNS hs hnd
  have hbl := Raw.Orb.base_lt_of_levels hb hl
  obtain ⟨⟨a0, h0, rfl⟩, ⟨a1, h1, rfl⟩, ⟨a2, h2, rfl⟩, ⟨a3, h3, rfl⟩, ⟨a4, h4, rfl⟩⟩ := htr
  obtain ⟨rX, sX⟩ := tr5_rep hb hp hl h0 h1 h2 h3 h4
  obtain ⟨⟨k0, k1, k2, k3, k4⟩, -, -⟩ := prod5_facts hb hp hl h0 h1 h2 h3 h4
  obtain ⟨-, hgX⟩ := gpt_facts k0 k1 k2 k3 k4
  obtain ⟨-, -, -, rYc⟩ := canonK_facts hYc
  obtain ⟨-, -, -, rZc⟩ := canonK_facts hZc
  obtain ⟨τ, rY⟩ := rep_of_siftA hb hp hl 5 0 rfl _ (fun i hi => by
    rw [unpack_getT hi]
    exact rYc i hi) hY
  obtain ⟨ρ, rZ⟩ := rep_of_siftA hb hp hl 5 0 rfl _ (fun i hi => by
    rw [unpack_getT hi]
    exact rZc i hi) hZ
  exact baseTw_of_sep hsep hbl (fun t ht => hb.2.2.2.2.2.2 t ht) rX rY rZ ((hmem _ _ rX).1 sX)
    ((hmem _ _ rY).1 hY) ((hmem _ _ rZ).1 hZ) (fun i hi => by rw [gptR_eq]; exact ((hgX i hi).1).symm)
    (fun i hi => by rw [pgR_eq, unpack_getT hi]) (fun i hi => by rw [pgR_eq, unpack_getT hi])

end CFSG.KS.SporSch

end
