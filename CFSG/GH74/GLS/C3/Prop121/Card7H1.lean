module

public import CFSG.GH74.GLS.C3.Prop121.Card7Facts
public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Fintype.Card
public import Mathlib.GroupTheory.Perm.Sign
public import Mathlib.GroupTheory.Perm.Basic
public import Mathlib.GroupTheory.Perm.Fin
public meta import Mathlib.Algebra.Group.End
public meta import Mathlib.GroupTheory.Perm.Sign
public meta import Mathlib.GroupTheory.Perm.Basic
public meta import Mathlib.GroupTheory.Perm.Fin
public meta import Mathlib.Logic.Equiv.Fin.Basic
public meta import Mathlib.Logic.Equiv.Option
public meta import Mathlib.Data.List.FinRange
public import CFSG.GH74.GLS.C3.Prop121.Card7H1Inputs
public meta import CFSG.GH74.GLS.C3.Prop121.Card7H1Inputs
public import Certificates.Certificate5080

public section

namespace CFSG.GH74.GLS.C3.Prop121.Card7.HC

open Subgroup Equiv Perm CFSG.GH74.GLS.C3.Layer2 CFSG.GH74.GLS.C3.Layer2.Model CFSG.GH74.GLS.Layer3

@[expose] def T1 : P11 := swap 8 9 * swap 9 10

theorem altY11_coe : ((altY11 : A11) : P11) = Y11 := by
  show yPerm (by norm_num : 8 ≤ 11) = Y11
  simp only [yPerm, xPerm, pt, Y11]
  decide

@[expose] def ev : H11 →* P11 :=
  (alternatingGroup (Fin 11)).subtype.comp (centralizer ({altY11} : Set A11)).subtype

theorem ev_injective : Function.Injective ev := by
  intro a b h
  exact Subtype.ext (Subtype.ext h)

theorem ev_tau1 : ev tau1 = T1 := rfl

theorem ev_ystar : ev ystar = Y11 := altY11_coe

@[expose] def mkH (σ : P11) (hσ : Hp σ) : H11 :=
  ⟨⟨σ, mem_alternatingGroup.2 hσ.1⟩, mem_centralizer_singleton_iff.2 (Subtype.ext (by
    show σ * ((altY11 : A11) : P11) = ((altY11 : A11) : P11) * σ
    rw [altY11_coe]; exact hσ.2))⟩

theorem ev_mkH (σ : P11) (hσ : Hp σ) : ev (mkH σ hσ) = σ := rfl

theorem card_H : Nat.card H11 = 1152 := by
  have h : Nat.card H11 * 2 = 384 * (11 - 8).factorial := card_centralizer_altY (by norm_num)
  have h2 : (11 - 8).factorial = 6 := by decide
  omega

theorem card_subtype_eq_countP {M N : Type*} (e : M → N) (he : Function.Injective e) (L : List N)
    (hnd : L.Nodup) (P : M → Prop) (Q : N → Bool)
    (h1 : ∀ m, P m → e m ∈ L) (h2 : ∀ m, P m → Q (e m) = true)
    (h3 : ∀ n ∈ L, Q n = true → ∃ m, e m = n ∧ P m) :
    Nat.card {m // P m} = L.countP Q := by
  classical
  have h4 : L.countP Q = (L.filter Q).length := List.countP_eq_length_filter
  rw [h4]
  have hnd' : (L.filter Q).Nodup := hnd.filter _
  have h5 : Nat.card {m // P m} = Nat.card {n // n ∈ (L.filter Q).toFinset} := by
    apply Nat.card_congr
    refine Equiv.ofBijective (fun m => ⟨e m.1, ?_⟩) ⟨?_, ?_⟩
    · simp only [List.mem_toFinset, List.mem_filter]; exact ⟨h1 _ m.2, h2 _ m.2⟩
    · intro a b hab; exact Subtype.ext (he (congrArg Subtype.val hab))
    · rintro ⟨n, hn⟩
      simp only [List.mem_toFinset, List.mem_filter] at hn
      obtain ⟨m, hm, hP⟩ := h3 n hn.1 hn.2
      exact ⟨⟨m, hP⟩, Subtype.ext hm⟩
  rw [h5, Nat.card_eq_fintype_card, Fintype.card_coe, List.toFinset_card_of_nodup hnd']

theorem HL_len_true :
    decide (HL.length = 1152) = true :=
  Certificates.certificate5080.1

theorem HL_length : HL.length = 1152 := of_decide_eq_true HL_len_true

theorem HL_nodup_true : decide HL.Nodup = true :=
  Certificates.certificate5080.2.1

theorem HL_nodup : HL.Nodup := of_decide_eq_true HL_nodup_true

theorem HL_hp_true :
    (HL.all fun σ => decide (Hp σ)) = true :=
  Certificates.certificate5080.2.2

theorem HL_hp (σ : P11) (h : σ ∈ HL) : Hp σ :=
  of_decide_eq_true (List.all_eq_true.1 HL_hp_true σ h)

theorem HL_complete (h : H11) : ev h ∈ HL := by
  classical
  have : Fintype H11 := Fintype.ofFinite _
  have hT : (HL.toFinset).card = 1152 := by rw [List.toFinset_card_of_nodup HL_nodup, HL_length]
  have hU : (Finset.univ.image ev).card = 1152 := by
    rw [Finset.card_image_of_injective _ ev_injective, Finset.card_univ, ← Nat.card_eq_fintype_card,
      card_H]
  have hsub : HL.toFinset ⊆ Finset.univ.image ev := by
    intro σ hσ
    rw [List.mem_toFinset] at hσ
    exact Finset.mem_image.2 ⟨mkH σ (HL_hp σ hσ), Finset.mem_univ _, rfl⟩
  have heq := Finset.eq_of_subset_of_card_le hsub (by rw [hT, hU])
  have : ev h ∈ Finset.univ.image ev := Finset.mem_image_of_mem _ (Finset.mem_univ h)
  rw [← heq] at this
  exact List.mem_toFinset.1 this

theorem card_H_subtype
    (P : H11 → Prop) (Q : P11 → Bool) (hPQ : ∀ h, P h ↔ Q (ev h) = true) :
    Nat.card {h : H11 // P h} = HL.countP Q := by
  refine card_subtype_eq_countP ev ev_injective HL HL_nodup P Q (fun h _ => HL_complete h)
    (fun h hh => (hPQ h).1 hh) ?_
  intro n hn hQ
  exact ⟨mkH n (HL_hp n hn), rfl, (hPQ _).2 (by rw [ev_mkH]; exact hQ)⟩

theorem ev_comm_iff (a b : H11) : a * b = b * a ↔ ev a * ev b = ev b * ev a := by
  constructor
  · intro h; rw [← map_mul, ← map_mul, h]
  · intro h; exact ev_injective (by rw [map_mul, map_mul]; exact h)

theorem ev_isInv (a : H11) : IsInv a ↔ (ev a * ev a = 1 ∧ ev a ≠ 1) := by
  unfold IsInv
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨?_, fun h => h2 (ev_injective (by rw [h, map_one]))⟩
    rw [← map_mul, ← sq, h1, map_one]
  · rintro ⟨h1, h2⟩
    refine ⟨ev_injective (by rw [map_pow, sq, h1, map_one]), fun h => h2 (by rw [h, map_one])⟩

@[expose] def ccL (σ ρ : P11) : ℕ :=
  HL.countP fun c => decide (c * σ = σ * c ∧ c * ρ = ρ * c)

theorem ccard_eq
    (u v : H11) : ccard H11 u v = ccL (ev u) (ev v) := by
  unfold ccard ccL
  refine card_H_subtype _ _ (fun h => ?_)
  rw [decide_eq_true_iff, ev_comm_iff h u, ev_comm_iff h v]

end CFSG.GH74.GLS.C3.Prop121.Card7.HC
