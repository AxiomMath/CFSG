module

public import CFSG.Certificates.Kernel.J4Hub.PcSound
import all CFSG.Certificates.Kernel.J4Hub.PcSound

public section

namespace CFSG.KS.J4Hub

open CFSG.KC.Ord CFSG.KS.Ord Matrix

variable {p d w S T L H CM RM ONE LV HV nb : Nat}

theorem mem_step {G : Type*} [Group G] [Finite G] (P N : Subgroup G) (u : G) (q : Nat) (hq : 0 < q)
    (hconj : ∀ g ∈ N, u⁻¹ * g * u ∈ N) (hpow : u ^ q ∈ N)
    (s : Set G) (hP : P = Subgroup.closure s) (hs : ∀ g ∈ s, g = u ∨ g ∈ N) :
    ∀ g ∈ P, ∃ e < q, ∃ h ∈ N, g = u ^ e * h := by
  have hconjE : ∀ e : Nat, ∀ g ∈ N, (u ^ e)⁻¹ * g * u ^ e ∈ N := by
    intro e
    induction e with
    | zero => intro g hg; simpa using hg
    | succ e ih =>
      intro g hg
      have := hconj _ (ih g hg)
      rw [pow_succ, _root_.mul_inv_rev]
      simpa [mul_assoc] using this
  let X : Set G := {g | ∃ e < q, ∃ h ∈ N, g = u ^ e * h}
  have hX : ∀ x ∈ s, ∀ y ∈ X, x * y ∈ X := by
    rintro x hx y ⟨e, he, h, hh, rfl⟩
    rcases hs x hx with rfl | hxN
    · by_cases he' : e + 1 < q
      · exact ⟨e + 1, he', h, hh, by rw [pow_succ', mul_assoc]⟩
      · have heq : e + 1 = q := by omega
        refine ⟨0, hq, x ^ q * h, N.mul_mem hpow hh, ?_⟩
        rw [pow_zero, one_mul, ← heq, pow_succ', mul_assoc]
    · refine ⟨e, he, (u ^ e)⁻¹ * x * u ^ e * h, N.mul_mem (hconjE e x hxN) hh, ?_⟩
      simp [mul_assoc]
  let M : Subgroup G :=
    { carrier := {g | ∀ y ∈ X, g * y ∈ X}
      one_mem' := fun y hy => by simpa using hy
      mul_mem' := fun ha hb y hy => by rw [mul_assoc]; exact ha _ (hb y hy)
      inv_mem' := by
        intro g hg
        have hpow' : ∀ k : Nat, ∀ y ∈ X, g ^ k * y ∈ X := by
          intro k
          induction k with
          | zero => intro y hy; simpa using hy
          | succ k ih => intro y hy; rw [pow_succ', mul_assoc]; exact hg _ (ih y hy)
        intro y hy
        have hinv : g⁻¹ = g ^ (orderOf g - 1) := by
          refine (eq_inv_of_mul_eq_one_left ?_).symm
          rw [← pow_succ, Nat.sub_add_cancel (orderOf_pos g), pow_orderOf_eq_one]
        rw [hinv]
        exact hpow' _ y hy }
  have hPM : P ≤ M := by
    rw [hP]
    exact (Subgroup.closure_le M).2 fun x hx => hX x hx
  have h1X : (1 : G) ∈ X := ⟨0, hq, 1, N.one_mem, by simp⟩
  intro g hg
  have := hPM hg 1 h1X
  rw [mul_one] at this
  exact this

@[expose] noncomputable def nfProd (p d w S : Nat) (RB : Nat → Nat) (PR : Nat) (e : Nat → Nat)
    (i n : Nat) : Matrix (Fin d) (Fin d) (ZMod p) :=
  ((List.range' i (n - i)).map fun k => pcMat p d w S RB PR k ^ e k).prod

theorem pcSub_normal (hc : constsOK p w S d T L H CM RM ONE LV HV = true) (hnb : nb = d * S)
    {G : Subgroup (GL (Fin d) (ZMod p))} {RB : Nat → Nat} {nreg : Nat}
    (hR : RegsIn p d w S nb L H G RB nreg) {q n pb PR PW nbl BL : Nat} (hq : q.Prime)
    (hpr : regsIn PR n nreg = true) (hpw : pwOK RB (mulR p w S d T L H CM RM) PR PW n q nreg = true)
    {Cs : List Nat}
    (hpc : Nat.beq (runPc RB (mulR p w S d T L H CM RM) ONE PR PW n q pb Cs 1) (Nat.add 1 n) = true)
    (hbl : BlocksOK p d w S T RM LV HV RB PR n q nbl BL) :
    Nat.card (pcSub p d w S RB PR 0 n) = q ^ n ∧
      ∀ g ∈ pcSub p d w S RB PR 0 n, ∃ e : Nat → Nat, (∀ k, e k < q) ∧
        ((g : GL (Fin d) (ZMod p)) : Matrix (Fin d) (Fin d) (ZMod p)) = nfProd p d w S RB PR e 0 n := by
  have hp : 2 ≤ p := Nat.le_of_ble_eq_true (andT' hc).1
  have := finite_GL (d := d) hp
  have hn := blocks_n_lt hbl.1
  have hdone := runPc_spec hn hpc
  have hup := pc_card_le hc hnb hR hq.pos hpr hpw hdone
  have hlo := blocks_le hc hnb hR hpr hbl
  refine ⟨le_antisymm hup hlo, ?_⟩
  have hu : ∀ k < n, ∃ u : GL (Fin d) (ZMod p),
      ((u : GL (Fin d) (ZMod p)) : Matrix (Fin d) (Fin d) (ZMod p)) = pcMat p d w S RB PR k := by
    intro k hk
    obtain ⟨-, u, -, eu⟩ := pc_reg hnb hc hR hpr hk
    exact ⟨u, eu⟩
  have key : ∀ t i, i + t = n → ∀ g ∈ pcSub p d w S RB PR i n, ∃ e : Nat → Nat, (∀ k, e k < q) ∧
      ((g : GL (Fin d) (ZMod p)) : Matrix (Fin d) (Fin d) (ZMod p)) = nfProd p d w S RB PR e i n := by
    intro t
    induction t with
    | zero =>
      intro i hi g hg
      have hbot : pcSub p d w S RB PR i n = ⊥ := by
        unfold pcSub
        rw [Subgroup.closure_eq_bot_iff]
        rintro g ⟨k, h1, h2, -⟩
        omega
      rw [hbot, Subgroup.mem_bot] at hg
      subst hg
      refine ⟨fun _ => 0, fun _ => hq.pos, ?_⟩
      unfold nfProd
      rw [show n - i = 0 by omega]
      simp
    | succ t ih =>
      intro i hi g hg
      obtain ⟨u, eu⟩ := hu i (by omega)
      have hstep := mem_step (pcSub p d w S RB PR i n) (pcSub p d w S RB PR (i + 1) n) u q hq.pos
        ?_ ?_ {g | ∃ k, i ≤ k ∧ k < n ∧
          ((g : GL (Fin d) (ZMod p)) : Matrix (Fin d) (Fin d) (ZMod p)) = pcMat p d w S RB PR k}
        rfl ?_ g hg
      · obtain ⟨e0, he0, h, hh, rfl⟩ := hstep
        obtain ⟨e, he, ehm⟩ := ih (i + 1) (by omega) h hh
        refine ⟨Function.update e i e0, fun k => ?_, ?_⟩
        · by_cases hk : k = i
          · subst hk; simpa using he0
          · rw [Function.update_of_ne hk]; exact he k
        · unfold nfProd at ehm ⊢
          have e1 : n - i = (n - (i + 1)) + 1 := by omega
          rw [e1, List.range'_succ, List.map_cons, List.prod_cons, Units.val_mul, Units.val_pow_eq_pow_val,
            eu, ehm, Function.update_self]
          congr 2
          refine List.map_congr_left fun k hk => ?_
          rw [List.mem_range'] at hk
          rw [Function.update_of_ne (by omega)]
      · intro g hg
        have hle : pcSub p d w S RB PR (i + 1) n ≤
            (pcSub p d w S RB PR (i + 1) n).comap (MulAut.conj u⁻¹).toMonoidHom := by
          refine (Subgroup.closure_le _).2 ?_
          rintro y ⟨k, h1, h2, ey⟩
          obtain ⟨x, hx⟩ := hdone i k (by omega) h2
          obtain ⟨g', hg', -, hrel⟩ := pcRel_spec hc hnb hR hq.pos hpr hpw (by omega) h2 hx eu ey
          have e2 := hrel (by omega)
          change u⁻¹ * y * u⁻¹⁻¹ ∈ pcSub p d w S RB PR (i + 1) n
          rw [inv_inv, mul_assoc, e2, ← mul_assoc, inv_mul_cancel, one_mul]
          exact hg'
        have := hle hg
        simpa using this
      · obtain ⟨x, hx⟩ := hdone i i le_rfl (by omega)
        obtain ⟨g', hg', hpow, -⟩ := pcRel_spec hc hnb hR hq.pos hpr hpw le_rfl (by omega) hx eu eu
        rw [hpow rfl]
        exact hg'
      · rintro g ⟨k, h1, h2, eg⟩
        rcases Nat.eq_or_lt_of_le h1 with rfl | h1
        · exact Or.inl (Units.ext (eg.trans eu.symm))
        · exact Or.inr (mem_pcSub h1 h2 eg)
  exact key n 0 (Nat.zero_add n)

end CFSG.KS.J4Hub

end
