module

public import CFSG.Alternating.Multipliers.OddKernel
public import CFSG.GroupTheory.ElementaryAbelianTransport

public section

namespace CFSG

open CFSG.Open CFSG.Alternating.Multipliers

variable {P Q : Type*} [Group P] [Group Q] [Finite P]

theorem exists_lift_elemAbelian_two_of_central_odd_ker {f : P →* Q}
    (hf : Function.Surjective f) (hker : f.ker ≤ Subgroup.center P)
    (hodd : Odd (Nat.card f.ker)) {Tbar : Subgroup Q} (hT : IsElemAbelian 2 Tbar)
    (hcard : Nat.card Tbar = 4) :
    ∃ T : Subgroup P, T.map f = Tbar ∧ IsElemAbelian 2 T ∧ Nat.card T = 4 ∧
      T ⊓ f.ker = ⊥ ∧
      (∀ (φ : MulAut P) (ψ : MulAut Q), (∀ y : P, f (φ y) = ψ (f y)) →
        (∀ q ∈ Tbar, ψ q ∈ Tbar) → ∀ t ∈ T, φ t ∈ T) := by
  classical
  let iota : ↥Tbar →* P :=
    { toFun := fun q => sqLift f (q : Q)
      map_one' := by
        exact (eq_sqLift hker hodd (q := (1 : Q)) (by simp) (one_pow 2)).symm
      map_mul' := fun a b => by
        have ha : ((a : Q)) ∈ f.range := hf a.1
        have hb : ((b : Q)) ∈ f.range := hf b.1
        have ha2 : (a : Q) ^ 2 = 1 := hT.2 a.1 a.2
        have hb2 : (b : Q) ^ 2 = 1 := hT.2 b.1 b.2
        haveI : IsMulCommutative ↥Tbar := hT.1
        have hc : (a : Q) * (b : Q) = (b : Q) * (a : Q) :=
          congrArg Subtype.val (mul_comm' a b)
        have hm := sqLift_mul hker hodd ha ha2 hb hb2 hc
        exact hm.symm }
  have hfinj : Function.Injective iota := by
    intro a b hab
    apply Subtype.ext
    have h1 : f (iota a) = f (iota b) := congrArg f hab
    rwa [show f (iota a) = (a : Q) from (sqLift_spec hker hodd (hf a.1) (hT.2 a.1 a.2)).1,
      show f (iota b) = (b : Q) from (sqLift_spec hker hodd (hf b.1) (hT.2 b.1 b.2)).1] at h1
  refine ⟨iota.range, ?_, ?_, ?_, ?_, ?_⟩
  ·
    ext q
    constructor
    · rintro ⟨_, ⟨s, rfl⟩, rfl⟩
      show f (sqLift f (s : Q)) ∈ Tbar
      rw [(sqLift_spec hker hodd (hf s.1) (hT.2 s.1 s.2)).1]
      exact s.2
    · intro hq
      refine ⟨iota ⟨q, hq⟩, ⟨⟨q, hq⟩, rfl⟩, ?_⟩
      exact (sqLift_spec hker hodd (hf q) (hT.2 q hq)).1
  ·
    let e : ↥Tbar ≃* ↥iota.range := MonoidHom.ofInjective hfinj
    have hel : CFSG.IsElementaryAbelian 2 ↥Tbar :=
      (CFSG.Open.isElemAbelian_iff_isElementaryAbelian).mp hT
    haveI : CFSG.IsElementaryAbelian 2 ↥iota.range :=
      CFSG.IsElementaryAbelian.of_mulEquiv e hel
    exact CFSG.Open.isElemAbelian_of_isElementaryAbelian
  ·
    let e : ↥Tbar ≃* ↥iota.range := MonoidHom.ofInjective hfinj
    rw [← Nat.card_congr e.toEquiv, hcard]
  ·
    apply le_bot_iff.1
    intro t ht
    obtain ⟨s, rfl⟩ := ht.1
    have h1 : f (sqLift f (s : Q)) = (s : Q) :=
      (sqLift_spec hker hodd (hf s.1) (hT.2 s.1 s.2)).1
    have h2 : (s : Q) = 1 := by
      rw [← h1]
      exact ht.2
    rw [Subgroup.mem_bot]
    have h3 : s = 1 := by
      apply Subtype.ext
      simpa using h2
    simpa using congrArg iota h3
  ·
    intro φ ψ hφ hψ t ht
    obtain ⟨s, rfl⟩ := ht
    have hs : ((s : ↥Tbar) : Q) ∈ f.range := hf s.1
    have hs2 : ((s : ↥Tbar) : Q) ^ 2 = 1 := hT.2 s.1 s.2
    have hconj : φ (sqLift f (s : Q)) = sqLift f (ψ (s : Q)) := by
      refine eq_sqLift hker hodd ?_ ?_
      · rw [hφ, (sqLift_spec hker hodd hs hs2).1]
      · simpa [map_pow] using congrArg φ ((sqLift_spec hker hodd hs hs2).2)
    show φ (sqLift f (s : Q)) ∈ iota.range
    rw [hconj]
    exact ⟨⟨ψ (s : Q), hψ (s : Q) s.2⟩, rfl⟩

end CFSG

end
