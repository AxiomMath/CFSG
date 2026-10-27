module

public import CFSG.LocalAnalysis.GLTheoremB.I2810.Step0Basic

public section

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.LocalAnalysis.GLTheoremB.Prop95Iv
open scoped commutatorElement

namespace CFSG.LocalAnalysis.GLTheoremB.Prop95Iv.I2810

section Quasi
variable {X : Type} [Group X] {W K S : Subgroup X} [W.Normal]

theorem s0_isQuasisimple_of_open {Q : Type*} [Group Q] (h : CFSG.Open.IsQuasisimple Q) :
    CFSG.IsQuasisimple Q := by
  have hperf : Group.IsPerfect Q := ⟨h.1⟩
  refine ⟨hperf, h.2, ?_⟩
  by_contra hab
  have hcomm : ∀ x y : Q ⧸ Subgroup.center Q, x * y = y * x := by
    intro x y
    by_contra hne
    exact hab ⟨x, y, hne⟩
  have hsimple : IsSimpleGroup (Q ⧸ Subgroup.center Q) := h.2
  have hperf' : Group.IsPerfect (Q ⧸ Subgroup.center Q) :=
    Group.IsPerfect.ofSurjective (G := Q) (G' := Q ⧸ Subgroup.center Q)
      (f := QuotientGroup.mk' (Subgroup.center Q)) (QuotientGroup.mk'_surjective _)
  have hbot : _root_.commutator (Q ⧸ Subgroup.center Q) = ⊥ := by
    rw [_root_.commutator, Subgroup.commutator_eq_bot_iff_le_centralizer]
    intro x _
    rw [Subgroup.mem_centralizer_iff]
    intro y _
    exact hcomm y x
  have htop : (⊤ : Subgroup (Q ⧸ Subgroup.center Q)) = ⊥ :=
    (Group.IsPerfect.commutator_eq_top (G := Q ⧸ Subgroup.center Q)).symm.trans hbot
  have := hsimple.toNontrivial
  obtain ⟨x, hx⟩ := exists_ne (1 : Q ⧸ Subgroup.center Q)
  have hxbot : x ∈ (⊥ : Subgroup (Q ⧸ Subgroup.center Q)) := htop ▸ Subgroup.mem_top x
  exact hx (Subgroup.mem_bot.mp hxbot)

theorem s0_quasi_aux (h : Setup28 W K S) : IsQuasisimple ↥(bar W K) := by
  have hKt : CFSG.Open.IsQuasisimple ↥(K.map (QuotientGroup.mk' (CFSG.pCore 2 X))) :=
    h.hK.2.2.2.2
  have hWO : W ≤ CFSG.pCore 2 X := s0_le_pCore_of_normal W h.hW
  let f : X ⧸ W →* X ⧸ CFSG.pCore 2 X :=
    QuotientGroup.map W (CFSG.pCore 2 X) (MonoidHom.id X) hWO
  have hf : ∀ y : X, f (QuotientGroup.mk' W y) = QuotientGroup.mk' (CFSG.pCore 2 X) y := fun y => rfl
  let g : ↥(bar W K) →* ↥(K.map (QuotientGroup.mk' (CFSG.pCore 2 X))) :=
    (f.comp (bar W K).subtype).codRestrict _ (by
      rintro ⟨q, k, hk, rfl⟩
      exact ⟨k, hk, (hf k).symm⟩)
  have hsurj : Function.Surjective g := by
    rintro ⟨t, k, hk, rfl⟩
    exact ⟨⟨QuotientGroup.mk' W k, k, hk, rfl⟩, Subtype.ext (hf k)⟩
  have hP : IsPGroup 2 g.ker := by
    intro x
    obtain ⟨y, hy⟩ := QuotientGroup.mk_surjective ((x : ↥(bar W K)) : X ⧸ W)
    have hyO : y ∈ CFSG.pCore 2 X := by
      have h1 : g x = 1 := x.2
      have h2 : f ((x : ↥(bar W K)) : X ⧸ W) = 1 := congrArg Subtype.val h1
      rw [← hy] at h2
      exact (QuotientGroup.eq_one_iff y).1 h2
    obtain ⟨n, hn⟩ := (CFSG.pCore_isPGroup (p := 2) (G := X)) ⟨y, hyO⟩
    refine ⟨n, Subtype.ext (Subtype.ext ?_)⟩
    have hn' : y ^ (2 ^ n) = 1 := congrArg Subtype.val hn
    have : ((x ^ (2 ^ n) : ↥g.ker) : ↥(bar W K)) = ((x : ↥(bar W K)) ^ (2 ^ n)) := rfl
    show (((x ^ (2 ^ n) : ↥g.ker) : ↥(bar W K)) : X ⧸ W) = 1
    rw [this]
    show (((x : ↥(bar W K)) : X ⧸ W)) ^ (2 ^ n) = 1
    rw [← hy, ← QuotientGroup.mk_pow, hn', QuotientGroup.mk_one]
  have hle : g.ker ≤ CFSG.pCore 2 ↥(bar W K) := s0_le_pCore_of_normal g.ker hP
  rw [h.hO] at hle
  have hinj : Function.Injective g := (MonoidHom.ker_eq_bot_iff g).1 (le_bot_iff.1 hle)
  let e : ↥(bar W K) ≃* ↥(K.map (QuotientGroup.mk' (CFSG.pCore 2 X))) :=
    MulEquiv.ofBijective g ⟨hinj, hsurj⟩
  exact s0_isQuasisimple_of_open (CFSG.Open.IsQuasisimple.of_mulEquiv e hKt)

end Quasi

end CFSG.LocalAnalysis.GLTheoremB.Prop95Iv.I2810
