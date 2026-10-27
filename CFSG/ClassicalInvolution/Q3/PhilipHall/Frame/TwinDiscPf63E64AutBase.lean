
module

public import Certificates.Data.E64Aut
public import CFSG.ClassicalInvolution.Q3.TL4Mdl117Brg

@[expose] public section

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame

open CFSG.ClassicalInvolution.Q3.AE CFSG.ClassicalInvolution.Q3.AE.Wr
open Certificates.AE117 Certificates.E64Aut CFSG.ClassicalInvolution.Q3.E64Data

namespace TwinDisc

namespace E64Aut

theorem finAll_iff {α : Type} {s : Finset α} {f : α → Bool} :
    finAll s f = true ↔ ∀ x ∈ s, f x = true := by
  simp [finAll]

theorem eqPi_perm {x y : Wr 7} (h : eqPi x y = true) : x.perm = y.perm := by
  simp only [eqPi, Bool.or_eq_true, decide_eq_true_eq] at h
  rcases h with rfl | rfl
  · rfl
  · rw [Wr.mul_perm]
    exact (mul_one _).symm

theorem mem_aeSubOver_of_inM {x : Wr 7} (hx : inM x = true) : x ∈ aeSubOver l32 := by
  simp only [inM, evenColl, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at hx
  obtain ⟨hsum, hfano, hsign⟩ := hx
  refine Subgroup.mem_inf.2 ⟨mem_aeSub.2 ⟨hsum, hsign⟩, Subgroup.mem_comap.2 ?_⟩
  intro s hs
  exact hfano s hs

theorem mkQ_mem_e64Sub {x : Wr 7} (hx : inM x = true) : mkQ 7 x ∈ e64Sub :=
  Subgroup.mem_map_of_mem (mkQ 7) (mem_aeSubOver_of_inM hx)

theorem vec_perm_mem {a : Wr 7} (ha : a ∈ aeSubOver l32) :
    a.vec ∈ evenFin () ∧ a.perm ∈ l32Fin () := by
  obtain ⟨h1, h2⟩ := Subgroup.mem_inf.1 ha
  have h1' := mem_aeSub.1 h1
  have h2' : a.perm ∈ l32 := Subgroup.mem_comap.1 h2
  constructor
  · simp only [evenFin, Finset.mem_filter, Finset.mem_univ, true_and]
    exact h1'.1
  · simp only [l32Fin, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨h2', h1'.2⟩

structure FlagData (α : Finset (Fin 7)) (W : List (Wr 7)) (g : Wr 7) (C : List (Wr 7)) : Prop where
  inM_W : ∀ x ∈ W, inM x = true
  inM_g : inM g = true
  inM_C : ∀ c ∈ C, inM c = true
  fix : ∀ s ∈ W, s ∈ memAtL α true ∨ s ∈ memAtL α false
  rel : ∀ r ∈ rels, inPi (evalG (W ++ [g]) r) = true
  comm : ∀ c ∈ C, c * c = 1 ∧ ∀ s ∈ W, c * s = s * c
  sol : ∀ a : Wr 7, a.perm ∈ l32Fin () → a.vec ∈ evenFin () →
    (∀ r ∈ rels, inPi (evalG (W ++ [a]) r) = true) → ∃ c ∈ C, eqPi a (c * g * c⁻¹) = true
  mem : ∀ y ∈ allMembers (), ∃ w ∈ words0, eqPi (evalG (W ++ [g]) w) y = true

theorem exists_lift : ∀ L : List (Wr 7), (∀ x ∈ L, inM x = true) →
    ∃ T : List ↥e64Sub, T.map e64Sub.subtype = L.map (mkQ 7)
  | [], _ => ⟨[], rfl⟩
  | x :: L, h => by
    obtain ⟨T, hT⟩ := exists_lift L fun y hy => h y (List.mem_cons_of_mem _ hy)
    refine ⟨⟨mkQ 7 x, mkQ_mem_e64Sub (h x (List.mem_cons.2 (Or.inl rfl)))⟩ :: T, ?_⟩
    simp only [List.map_cons, hT]
    rfl

theorem map_evalG_eq {G H : Type*} [Group G] [Group H] (f : G ≃* H) (T : List G) (w : List ℕ) :
    f (evalG T w) = evalG (T.map f) w :=
  TL4.Mdl117.evalG_map f.toMonoidHom T w

theorem aut_core {α : Finset (Fin 7)} (hα : α.card = 4) {W : List (Wr 7)} {g : Wr 7}
    {C : List (Wr 7)} (hd : FlagData α W g C) (θ : MulAut ↥e64Sub)
    (hT : ∀ x : ↥e64Sub, (x : AEQ 7) ∈ memBar α hα true → θ x = x)
    (hF : ∀ x : ↥e64Sub, (x : AEQ 7) ∈ memBar α hα false → θ x = x) :
    ∃ c : ↥e64Sub, c * c = 1 ∧ ∀ y : ↥e64Sub,
      (∃ α' ∈ e64Sets, ∃ (h' : α'.card = 4) (b : Bool), (y : AEQ 7) ∈ memBar α' h' b) →
        θ y = c * y * c⁻¹ := by
  obtain ⟨TW, hTW⟩ := exists_lift W hd.inM_W
  let tg : ↥e64Sub := ⟨mkQ 7 g, mkQ_mem_e64Sub hd.inM_g⟩
  have hTWmem : ∀ t ∈ TW, ∃ s ∈ W, mkQ 7 s = (t : AEQ 7) := by
    intro t ht
    have h1 : (t : AEQ 7) ∈ W.map (mkQ 7) := by
      rw [← hTW]
      exact List.mem_map.2 ⟨t, ht, rfl⟩
    obtain ⟨s, hs, hst⟩ := List.mem_map.1 h1
    exact ⟨s, hs, hst⟩
  have hfixW : ∀ t ∈ TW, θ t = t := by
    intro t ht
    obtain ⟨s, hs, hst⟩ := hTWmem t ht
    rcases hd.fix s hs with h | h
    · exact hT t ((TL4.Mdl117.mem_memBar_iff α hα true _).2 ⟨s, h, hst⟩)
    · exact hF t ((TL4.Mdl117.mem_memBar_iff α hα false _).2 ⟨s, h, hst⟩)
  have hTmap : (TW ++ [tg]).map e64Sub.subtype = (W ++ [g]).map (mkQ 7) := by
    rw [List.map_append, List.map_append, hTW]
    rfl
  have hval : ∀ w, ((evalG (TW ++ [tg]) w : ↥e64Sub) : AEQ 7) = mkQ 7 (evalG (W ++ [g]) w) := by
    intro w
    have h1 := TL4.Mdl117.evalG_map e64Sub.subtype (TW ++ [tg]) w
    have h2 := TL4.Mdl117.evalG_map (mkQ 7) (W ++ [g]) w
    rw [hTmap] at h1
    exact h1.trans h2.symm
  obtain ⟨a, haM, ha⟩ : ∃ a ∈ aeSubOver l32, mkQ 7 a = ((θ tg : ↥e64Sub) : AEQ 7) :=
    Subgroup.mem_map.1 (θ tg).2
  obtain ⟨hav, hap⟩ := vec_perm_mem haM
  have hTWθ : TW.map θ = TW := (List.map_congr_left (g := id) hfixW).trans (List.map_id _)
  have hmapθ : (TW ++ [tg]).map θ = TW ++ [θ tg] := by
    rw [List.map_append, hTWθ]
    rfl
  have hmapθsub : ((TW ++ [tg]).map θ).map e64Sub.subtype = (W ++ [a]).map (mkQ 7) := by
    rw [hmapθ, List.map_append, List.map_append, hTW]
    simp only [List.map_cons, List.map_nil]
    rw [ha]
    rfl
  have hrelA : ∀ r ∈ rels, inPi (evalG (W ++ [a]) r) = true := by
    intro r hr
    rw [TL4.Mdl117.inPi_iff]
    have h1 : evalG (TW ++ [tg]) r = 1 := by
      apply Subtype.ext
      rw [hval r]
      exact (TL4.Mdl117.inPi_iff _).1 (hd.rel r hr)
    have h2 := map_evalG_eq θ (TW ++ [tg]) r
    have h3 := TL4.Mdl117.evalG_map e64Sub.subtype ((TW ++ [tg]).map θ) r
    have h4 := TL4.Mdl117.evalG_map (mkQ 7) (W ++ [a]) r
    rw [hmapθsub] at h3
    rw [h1, map_one] at h2
    rw [h4, ← h3, ← h2]
    rfl
  obtain ⟨c, hc, hca⟩ := hd.sol a hap hav hrelA
  have hca' : mkQ 7 a = mkQ 7 c * mkQ 7 g * (mkQ 7 c)⁻¹ := by
    rw [(TL4.Mdl117.eqPi_iff _ _).1 hca, map_mul, map_mul, map_inv]
  let c₀ : ↥e64Sub := ⟨mkQ 7 c, mkQ_mem_e64Sub (hd.inM_C c hc)⟩
  have hc₀sq : c₀ * c₀ = 1 := by
    apply Subtype.ext
    show mkQ 7 c * mkQ 7 c = 1
    rw [← map_mul, (hd.comm c hc).1, map_one]
  have hagree : ∀ t ∈ TW ++ [tg], θ t = MulAut.conj c₀ t := by
    intro t ht
    rcases List.mem_append.1 ht with ht | ht
    · obtain ⟨s, hs, hst⟩ := hTWmem t ht
      rw [hfixW t ht, MulAut.conj_apply]
      apply Subtype.ext
      have hcs : mkQ 7 c * mkQ 7 s = mkQ 7 s * mkQ 7 c := by
        rw [← map_mul, ← map_mul, (hd.comm c hc).2 s hs]
      show (t : AEQ 7) = mkQ 7 c * (t : AEQ 7) * (mkQ 7 c)⁻¹
      rw [← hst, hcs, mul_assoc, mul_inv_cancel, mul_one]
    · rw [List.mem_singleton.1 ht, MulAut.conj_apply]
      apply Subtype.ext
      show ((θ tg : ↥e64Sub) : AEQ 7) = mkQ 7 c * mkQ 7 g * (mkQ 7 c)⁻¹
      rw [← ha, hca']
  refine ⟨c₀, hc₀sq, ?_⟩
  rintro y ⟨α', hα', h', b, hy⟩
  obtain ⟨ℓ', hℓ', rfl⟩ := hα'
  obtain ⟨a', ha', hay⟩ := (TL4.Mdl117.mem_memBar_iff _ h' b _).1 hy
  have hmemall : a' ∈ allMembers () := by
    unfold allMembers
    rw [List.mem_flatMap]
    refine ⟨ℓ', hℓ', ?_⟩
    cases b
    · exact List.mem_append_right _ ha'
    · exact List.mem_append_left _ ha'
  obtain ⟨w, -, hw⟩ := hd.mem a' hmemall
  have hyT : y = evalG (TW ++ [tg]) w := by
    apply Subtype.ext
    rw [hval w, ← hay]
    exact ((TL4.Mdl117.eqPi_iff _ _).1 hw).symm
  rw [hyT, show c₀ * evalG (TW ++ [tg]) w * c₀⁻¹ = MulAut.conj c₀ (evalG (TW ++ [tg]) w) from
    (MulAut.conj_apply _ _).symm, map_evalG_eq θ, map_evalG_eq (MulAut.conj c₀)]
  exact congrArg (fun L => evalG L w) (List.map_congr_left hagree)

end E64Aut

end TwinDisc

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
