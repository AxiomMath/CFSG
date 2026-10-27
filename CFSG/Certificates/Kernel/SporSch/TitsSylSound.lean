module

public import Certificates.Data.Kernel.SporSch.TitsSyl
public import CFSG.Certificates.Kernel.SporSch.TitsCntSound
import CFSG.Certificates.Kernel.Spor.RawSiftK

public section

namespace CFSG.KS.SporSch

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim
open CFSG.Certificates.Native CFSG.Monster.B.Co2.Native CFSG.Sporadic.Schreier.Tits
open CFSG.Monster.B.Co2 (Rep eqA_iff rep_compA rep_idA)

theorem all5K_soundA {kS BP : Nat} {PS PSI LR TR TRI : Nat → Nat} {S : Array (Array Nat)}
    {base : Array Nat} {p : Array Nat → Bool} {P : Nat → Nat → Nat → Nat → Nat → Bool}
    (hb : Binds 1755 11 PS kS 5 BP S base)
    (hp : allN kS (fun j => permOK 1755 11 (mask 11) (1755 * 11) (PS j) (PSI j)) = true)
    (hl : LevelsOK 1755 11 PS PSI LR TR TRI kS 5 BP) (hP : Agrees LR TR P p)
    (h : all5K 1755 (1755 * 11) LR TR (fun _ => P) = true) :
    all5 1755 (rawLevels 1755 S base) p = true := by
  have c0 := (lev_trAt hb hp hl (i := 0) (by omega)).1
  have c1 := (lev_trAt hb hp hl (i := 1) (by omega)).1
  have c2 := (lev_trAt hb hp hl (i := 2) (by omega)).1
  have c3 := (lev_trAt hb hp hl (i := 3) (by omega)).1
  have c4 := (lev_trAt hb hp hl (i := 4) (by omega)).1
  unfold all5
  rw [c0, c1, c2, c3, c4]
  refine CFSG.Monster.B.Co2.allLt_iff.2 fun a ha => CFSG.Monster.B.Co2.allLt_iff.2 fun b hb' =>
    CFSG.Monster.B.Co2.allLt_iff.2 fun c hc => CFSG.Monster.B.Co2.allLt_iff.2 fun d hd =>
    CFSG.Monster.B.Co2.allLt_iff.2 fun e he => ?_
  obtain ⟨-, eg, -⟩ := prod5_facts hb hp hl ha hb' hc hd he
  rw [eg, ← hP _ _ _ _ _ ⟨⟨a, ha, rfl⟩, ⟨b, hb', rfl⟩, ⟨c, hc, rfl⟩, ⟨d, hd, rfl⟩, ⟨e, he, rfl⟩⟩]
  exact all5K_at h ha hb' hc hd he

theorem baseEqF_eq {BP : Nat} {base : Array Nat} {G : Subgroup (Equiv.Perm (Fin 1755))}
    (hsep : ∀ γ ∈ G, (∀ t < 5, ∀ h : base[t]! < 1755, γ ⟨base[t]!, h⟩ = ⟨base[t]!, h⟩) → γ = 1)
    (hbl : ∀ t < 5, base[t]! < 1755) (hBP : ∀ t < 5, base[t]! = pg 11 (mask 11) BP t)
    {X Y : Array Nat} {σ τ : Equiv.Perm (Fin 1755)} (hX : Rep 1755 X σ) (hY : Rep 1755 Y τ)
    (hσ : σ ∈ G) (hτ : τ ∈ G) {gx gy : Nat → Nat} (hgx : ∀ i < 1755, gx i = X[i]!)
    (hgy : ∀ i < 1755, gy i = Y[i]!) :
    baseEqF BP 5 gx gy = eqA 1755 X Y := by
  rw [Bool.eq_iff_iff, eqA_iff hX hY]
  have hpt : ∀ t (ht : t < 5), gx base[t]! = (σ ⟨base[t]!, hbl t ht⟩ : Nat) ∧
      gy base[t]! = (τ ⟨base[t]!, hbl t ht⟩ : Nat) := fun t ht =>
    ⟨by rw [hgx _ (hbl t ht), hX.apply (hbl t ht)], by rw [hgy _ (hbl t ht), hY.apply (hbl t ht)]⟩
  constructor
  · intro h
    have hfix : ∀ t < 5, ∀ hb : base[t]! < 1755, (τ⁻¹ * σ) ⟨base[t]!, hb⟩ = ⟨base[t]!, hb⟩ := by
      intro t ht hb
      have := allN_spec h t ht
      rw [strictB_eq, ← hBP t ht, Nat.beq_eq, (hpt t ht).1, (hpt t ht).2] at this
      rw [Equiv.Perm.mul_apply, Equiv.Perm.inv_eq_iff_eq]
      exact Fin.ext this
    exact inv_mul_eq_one.1 (hsep _ (G.mul_mem (G.inv_mem hτ) hσ) hfix) |>.symm
  · intro h
    unfold baseEqF
    refine allN_of_forall fun t ht => ?_
    rw [strictB_eq, ← hBP t ht, Nat.beq_eq, (hpt t ht).1, (hpt t ht).2, h]

theorem invTB_eq {kS kO BP NS CH T B t0 t1 t2 t3 t4 : Nat} {PS PSI LR TR TRI : Nat → Nat}
    {S : Array (Array Nat)} {base : Array Nat} {D : List (List Int)}
    (hb : Binds 1755 11 PS kS 5 BP S base)
    (hh : headK 1755 11 (mask 11) (1755 * 11) (pidn 1755 11) PS PSI kS kO D 5 BP = true)
    (hl : LevelsOK 1755 11 PS PSI LR TR TRI kS 5 BP) (hNS : 1755 ≤ NS * CH)
    (hs : ∀ i < 5, ∀ s < NS, schK 1755 11 (mask 11) (1755 * 11) (pidn 1755 11) PS PSI LR TR TRI
      kS BP 5 i (stepsAt 1755 11 PS kS BP i) (s * CH) CH = true)
    (hnd : base.toList.Nodup)
    (htr : IsTr5 LR TR t0 t1 t2 t3 t4)
    (hTc : canonK 1755 11 (mask 11) (1755 * 11) T = true)
    (hT : siftA 1755 (rawLevels 1755 S base) base 0 (unpack 1755 11 T) = true)
    (hBc : canonK 1755 11 (mask 11) (1755 * 11) B = true)
    (hB : siftA 1755 (rawLevels 1755 S base) base 0 (unpack 1755 11 B) = true) :
    invTB BP T B t0 t1 t2 t3 t4 =
      (!(commA (unpack 1755 11 (prod5K 1755 11 (mask 11) t0 t1 t2 t3 t4)) (unpack 1755 11 T) &&
        commA (unpack 1755 11 (prod5K 1755 11 (mask 11) t0 t1 t2 t3 t4)) (unpack 1755 11 B) &&
        eqA 1755 (compA 1755 (unpack 1755 11 (prod5K 1755 11 (mask 11) t0 t1 t2 t3 t4))
          (unpack 1755 11 (prod5K 1755 11 (mask 11) t0 t1 t2 t3 t4))) (idA 1755)) ||
        eqA 1755 (unpack 1755 11 (prod5K 1755 11 (mask 11) t0 t1 t2 t3 t4)) (idA 1755) ||
        eqA 1755 (unpack 1755 11 (prod5K 1755 11 (mask 11) t0 t1 t2 t3 t4)) (unpack 1755 11 T)) := by
  have hp := (Raw.Orb.head_facts hh).1
  obtain ⟨G, hmem, hsep⟩ := chain_group hb hh hl hNS hs hnd
  have hbl := Raw.Orb.base_lt_of_levels hb hl
  have hBP : ∀ t < 5, base[t]! = pg 11 (mask 11) BP t := fun t ht => hb.2.2.2.2.2.2 t ht
  have e1 := baseCommG_eq hb hh hl hNS hs hnd htr hTc hT
  have e2 := baseCommG_eq hb hh hl hNS hs hnd htr hBc hB
  obtain ⟨⟨a0, h0, rfl⟩, ⟨a1, h1, rfl⟩, ⟨a2, h2, rfl⟩, ⟨a3, h3, rfl⟩, ⟨a4, h4, rfl⟩⟩ := htr
  obtain ⟨rX, sX⟩ := tr5_rep hb hp hl h0 h1 h2 h3 h4
  obtain ⟨⟨k0, k1, k2, k3, k4⟩, -, -⟩ := prod5_facts hb hp hl h0 h1 h2 h3 h4
  obtain ⟨-, hgX⟩ := gpt_facts k0 k1 k2 k3 k4
  have hσ := (hmem _ _ rX).1 sX
  obtain ⟨-, -, -, rTc⟩ := canonK_facts hTc
  obtain ⟨τ, rT⟩ := rep_of_siftA hb hp hl 5 0 rfl _ (fun i hi => by
    rw [unpack_getT hi]
    exact rTc i hi) hT
  have hτ := (hmem _ _ rT).1 hT
  set X := unpack 1755 11 (prod5K 1755 11 (mask 11) (trAt 1755 (1755 * 11) LR TR 0 a0)
    (trAt 1755 (1755 * 11) LR TR 1 a1) (trAt 1755 (1755 * 11) LR TR 2 a2)
    (trAt 1755 (1755 * 11) LR TR 3 a3) (trAt 1755 (1755 * 11) LR TR 4 a4)) with hXd
  set g := gptR (trAt 1755 (1755 * 11) LR TR 0 a0) (trAt 1755 (1755 * 11) LR TR 1 a1)
    (trAt 1755 (1755 * 11) LR TR 2 a2) (trAt 1755 (1755 * 11) LR TR 3 a3)
    (trAt 1755 (1755 * 11) LR TR 4 a4) with hgd
  have hgx : ∀ i < 1755, g i = X[i]! := fun i hi => by
    rw [hgd, gptR_eq]
    exact ((hgX i hi).1).symm
  have hid : ∀ i < 1755, (fun i : Nat => i) i = (idA 1755)[i]! := fun i hi =>
    (CFSG.Monster.B.Co2.idA_get hi).symm
  have e3 : baseEqF BP 5 (fun i => g (g i)) (fun i => i) =
      eqA 1755 (compA 1755 X X) (idA 1755) :=
    baseEqF_eq hsep hbl hBP (rep_compA rX rX) rep_idA (G.mul_mem hσ hσ) G.one_mem
      (fun i hi => by rw [CFSG.Monster.B.Co2.compA_get hi, hgx _ hi, hgx _ (rX.lt hi)]) hid
  have e4 : baseEqF BP 5 g (fun i => i) = eqA 1755 X (idA 1755) :=
    baseEqF_eq hsep hbl hBP rX rep_idA hσ G.one_mem hgx hid
  have e5 : baseEqF BP 5 g (pgR T) = eqA 1755 X (unpack 1755 11 T) :=
    baseEqF_eq hsep hbl hBP rX rT hσ hτ hgx (fun i hi => by rw [pgR_eq, unpack_getT hi])
  unfold invTB
  rw [← hgd, e1, e2, e3, e4, e5]
  generalize commA X (unpack 1755 11 T) = b1
  generalize commA X (unpack 1755 11 B) = b2
  generalize eqA 1755 (compA 1755 X X) (idA 1755) = b3
  generalize eqA 1755 X (idA 1755) = b4
  generalize eqA 1755 X (unpack 1755 11 T) = b5
  cases b1 <;> cases b2 <;> cases b3 <;> cases b4 <;> cases b5 <;> rfl

end CFSG.KS.SporSch

end
