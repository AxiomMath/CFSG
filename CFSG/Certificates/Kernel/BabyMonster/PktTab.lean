module

public import CFSG.Certificates.Kernel.BabyMonster.PktSound

public section

namespace CFSG.KC.BM.Pkt

open CFSG.KC.BM CFSG.KC.BM.B64

@[expose] noncomputable def fieldOf (v : Nat) : Nat :=
  Nat.add (Nat.mod v (nat_lit 8192))
    (Nat.mul (nat_lit 8192) (Nat.mod (Nat.div v (nat_lit 8192)) (nat_lit 8)))

@[expose] noncomputable def tableOf (p : Nat × Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) (nat_lit 0)
    (fun k acc => Nat.lor acc (Nat.shiftLeft (fieldOf (entV p.1 k)) (Nat.mul (nat_lit 16) k)))
    (nat_lit 4371)

@[expose] noncomputable def compT (T U : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) (nat_lit 0)
    (fun t acc => (fun f => (fun g => Nat.lor acc (Nat.shiftLeft
        (Nat.add (Nat.mod g (nat_lit 8192)) (Nat.mul (nat_lit 8192)
          (Nat.mod (Nat.add (Nat.div f (nat_lit 8192)) (Nat.div g (nat_lit 8192))) (nat_lit 2))))
        (Nat.mul (nat_lit 16) t)))
      (tfield U (Nat.mod f (nat_lit 8192)))) (tfield T t))
    (nat_lit 4371)

@[expose] noncomputable def compFld (T U t : Nat) : Nat :=
  tfield U (tfield T t % 8192) % 8192 +
    8192 * ((tfield T t / 8192 + tfield U (tfield T t % 8192) / 8192) % 2)

theorem fld_compT (T U t : Nat) :
    Dy.fld (compT T U) t = if t < 4371 then compFld T U t else 0 := by
  unfold compT
  generalize hn : nat_lit 4371 = n
  exact Dy.fld_recOr (c := compFld T U) (fun k acc => rfl)
    (fun k => by unfold compFld; omega) n t

theorem compT_sound {T U : Nat} (hT : tabOK T = true) (hU : tabOK U = true) :
    ∀ t u : Nat, t < 4371 → u < 4371 →
      8 * kNumMono (compT T U) t u =
        ∑ j ∈ Finset.range 4371, kNumMono T t j * kNumMono U j u := by
  intro t u ht _
  have hk : ∀ X t u, kNumMono X t u =
      if u = Dy.fld X t % 8192 then (if Dy.fld X t / 8192 = 1 then (-8 : ℤ) else 8) else 0 :=
    fun _ _ _ => rfl
  obtain ⟨hT1, hT2⟩ := tab_facts hT t ht
  obtain ⟨-, hU2⟩ := tab_facts hU _ hT1
  have hc : Dy.fld (compT T U) t = Dy.fld U (Dy.fld T t % 8192) % 8192 +
      8192 * ((Dy.fld T t / 8192 + Dy.fld U (Dy.fld T t % 8192) / 8192) % 2) := by
    rw [fld_compT, ite_eq_left ht]
    unfold compFld
    simp only [tfield_fld]
  rw [Finset.sum_eq_single (Dy.fld T t % 8192)]
  · rw [hk (compT T U), hk T, hk U, hc, ite_eq_left rfl]
    generalize Dy.fld U (Dy.fld T t % 8192) = H at hU2 ⊢
    generalize Dy.fld T t = g at hT2 ⊢
    have e1 : (H % 8192 + 8192 * ((g / 8192 + H / 8192) % 2)) % 8192 = H % 8192 := by omega
    have e2 : (H % 8192 + 8192 * ((g / 8192 + H / 8192) % 2)) / 8192 =
        (g / 8192 + H / 8192) % 2 := by omega
    rw [e1, e2]
    have ha : g / 8192 = 0 ∨ g / 8192 = 1 := by omega
    have hb : H / 8192 = 0 ∨ H / 8192 = 1 := by omega
    rcases ha with ha | ha <;> rcases hb with hb | hb <;> rw [ha, hb] <;>
      by_cases hP : u = H % 8192 <;> simp [hP]
  · intro j _ hj
    rw [hk T, ite_eq_right hj, zero_mul]
  · intro hn
    exact absurd (Finset.mem_range.2 hT1) hn

end CFSG.KC.BM.Pkt

end
