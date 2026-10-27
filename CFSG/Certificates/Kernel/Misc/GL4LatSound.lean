module

public import Certificates.Data.Kernel.Misc.GL4Lat
public import CFSG.Certificates.Kernel.Misc.GL4EltSound
import CFSG.Certificates.Kernel.LocalQTPermSound

public section

namespace CFSG.KC.Misc.GL4

open Matrix CFSG.KC.LQT.P CFSG.KC.Ord
open scoped commutatorElement
open CFSG.KC.Misc.Clos (ClosEnc ExactList clos_card sort_distinct treeAt sortAt closedAt)
open Certificates.A5GL42 (Mat4 ofCode)
open Certificates.A5A7GL42 (Pset)
open Certificates.GL4 (GL4 sg)

theorem exists_of_invW {c d : ℕ} (h : invW c d = true) : ∃ g : GL4, enc4 g = c := by
  unfold invW at h
  obtain ⟨hc, h⟩ := andB_iff.1 h
  obtain ⟨-, hi⟩ := andB_iff.1 h
  have hm : ofCode c * ofCode d = 1 := by
    rw [← mul4F_ofCode, beq_iff.1 hi, ofCode_id4]
  exact ⟨⟨ofCode c, ofCode d, hm, mul_eq_one_comm.mp hm⟩, code4_ofCode (Nat.blt_eq.mp hc)⟩

theorem enc4_inv_of_invW {g : GL4} {d : ℕ} (h : invW (enc4 g) d = true) : enc4 g⁻¹ = d := by
  unfold invW at h
  obtain ⟨-, h⟩ := andB_iff.1 h
  obtain ⟨hd, hi⟩ := andB_iff.1 h
  have hm : (g : Mat4) * ofCode d = 1 := by
    rw [← ofCode_enc4 g, ← mul4F_ofCode, beq_iff.1 hi, ofCode_id4]
  have e : ((g⁻¹ : GL4) : Mat4) = ofCode d := Units.inv_eq_of_mul_eq_one_right hm
  rw [enc4, e, code4_ofCode (Nat.blt_eq.mp hd)]

theorem sg_eq_of (l : List ℕ) (hl : ∀ c ∈ l, ∃ g : GL4, enc4 g = c) :
    sg l = Subgroup.closure {g | g ∈ l.map u4} := by
  unfold Certificates.GL4.sg
  congr 1
  ext g
  simp only [Set.mem_setOf_eq, List.mem_map]
  constructor
  · rintro ⟨c, hc, e⟩
    refine ⟨c, hc, ?_⟩
    apply gl4_enc.inj
    rw [enc4_u4 (hl c hc), enc4, ← e, code4_ofCode]
    obtain ⟨h, rfl⟩ := hl c hc
    exact enc4_lt h
  · rintro ⟨c, hc, rfl⟩
    exact ⟨c, hc, (coe_eq_of_enc4 (enc4_u4 (hl c hc))).symm⟩

theorem enc4_getD_u4_of (d : GL4) : ∀ (l : List ℕ), (∀ c ∈ l, ∃ g : GL4, enc4 g = c) →
    ∀ j < l.length, enc4 ((l.map u4).getD j d) = l.getD j 0
  | [], _, j, hj => absurd hj (Nat.not_lt_zero _)
  | c :: _, hl, 0, _ => by
    rw [List.map_cons, List.getD_cons_zero, List.getD_cons_zero]
    exact enc4_u4 (hl c List.mem_cons_self)
  | _ :: t, hl, j + 1, hj => by
    rw [List.map_cons, List.getD_cons_succ, List.getD_cons_succ]
    exact enc4_getD_u4_of d t (fun x hx => hl x (List.mem_cons_of_mem _ hx)) j
      (Nat.lt_of_succ_lt_succ hj)

theorem sg_exact_of (l : List ℕ) (hl : ∀ c ∈ l, ∃ g : GL4, enc4 g = c) {G E PA SG CT : ℕ → ℕ}
    {N : ℕ} (hG : ∀ j < l.length, G j = l.getD j 0) (hN : 0 < N)
    (ht : ∀ k < N, treeAt mul4F id4 G l.length E PA k = true)
    (hs : ∀ k < N, sortAt N E SG k = true)
    (hc : ∀ k < N, closedAt mul4F G l.length N E CT k = true) :
    Nat.card (sg l) = N ∧ ExactList enc4 (sg l) N E := by
  have hlen : (l.map u4).length = l.length := List.length_map _
  have := finite_gl4
  have hG' : ∀ j < (l.map u4).length, G j = enc4 ((l.map u4).getD j 1) := by
    intro j hj
    have hj' : j < l.length := lt_of_lt_of_eq hj hlen
    rw [hG j hj', enc4_getD_u4_of 1 l hl j hj']
  obtain ⟨h1, -, h3⟩ := clos_card gl4_enc (l.map u4) hG' hN (by rw [hlen]; exact ht) hs
  obtain ⟨h4, h5⟩ := h3 (CT := CT) (by rw [hlen]; exact hc)
  rw [sg_eq_of l hl]
  exact ⟨h4, h1, h5, sort_distinct hs⟩

theorem card_gl4 : Nat.card GL4 = 20160 := by
  rw [Matrix.card_GL_field, ZMod.card]
  decide

theorem top_exact {E : ℕ → ℕ} (hu : ∀ k < 20160, ∃ g : GL4, enc4 g = E k)
    (hi : ∀ k, k + 1 < 20160 → E k < E (k + 1)) : ExactList enc4 ⊤ 20160 E := by
  have hmono : ∀ a b, a < b → b < 20160 → E a < E b := by
    intro a b hab hb
    induction b with
    | zero => omega
    | succ b ih =>
      rcases Nat.lt_succ_iff_lt_or_eq.1 hab with h | rfl
      · exact (ih h (by omega)).trans (hi b hb)
      · exact hi a hb
  have hd : ∀ i < 20160, ∀ j < 20160, E i = E j → i = j := by
    intro i hi' j hj e
    rcases Nat.lt_trichotomy i j with h | h | h
    · exact absurd e (hmono i j h hj).ne
    · exact h
    · exact absurd e (hmono j i h hi').ne'
  have := finite_gl4
  let f : Fin 20160 → GL4 := fun k => u4 (E k)
  have hf : ∀ k : Fin 20160, enc4 (f k) = E k := fun k => enc4_u4 (hu k k.isLt)
  have hinj : Function.Injective f := by
    intro a b h
    have : E a = E b := by rw [← hf a, ← hf b, h]
    exact Fin.ext (hd a a.isLt b b.isLt this)
  have hbij := hinj.bijective_of_nat_card_le (by rw [card_gl4, Nat.card_eq_fintype_card,
    Fintype.card_fin])
  refine ⟨fun k hk => ⟨f ⟨k, hk⟩, Subgroup.mem_top _, hf ⟨k, hk⟩⟩, fun g _ => ?_, hd⟩
  obtain ⟨k, rfl⟩ := hbij.2 g
  exact ⟨k, k.isLt, hf k⟩

end CFSG.KC.Misc.GL4

end
