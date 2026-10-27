module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23R8Z5bTI
import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23R7LL3

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23.Z5b

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
  CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDisc CFSG.ClassicalInvolution.Uniform
  CFSG.ClassicalInvolution.Q3.Q3NL

section Generic

variable {Y : Type} [Group Y] [Finite Y]

theorem no_order_four_inf {Ω : Set (Subgroup Y)} (hΩ : HypOmegaGen Ω) {K J : Subgroup Y} (hK : K ∈ Ω)
    (hJ : J ∈ Ω) (hne : K ≠ J) {x : Y} (hxK : x ∈ K) (hxJ : x ∈ J) : orderOf x ≠ 4 := by
  intro hx4
  have hdvd : orderOf x ∣ Nat.card ↥(K ⊓ J) :=
    Subgroup.orderOf_dvd_natCard _ (Subgroup.mem_inf.mpr ⟨hxK, hxJ⟩)
  rw [hx4] at hdvd
  have hne0 : Nat.card ↥(K ⊓ J) ≠ 0 := Nat.card_pos.ne'
  have h2 : 2 ≤ padicValNat 2 (Nat.card ↥(K ⊓ J)) :=
    (padicValNat_dvd_iff_le (p := 2) hne0).mp (by rw [show (2 : ℕ) ^ 2 = 4 by norm_num]; exact hdvd)
  have h1 := (hΩ.omega4 K hK J hJ hne).1
  omega

theorem twoTwins_of_mem {R : Subgroup Y} (h2 : TwoTwins R) {L : Subgroup Y} (hL : L ∈ Om R)
    {A B C : Subgroup Y} (hA : A ∈ twinSet (Om R) L) (hB : B ∈ twinSet (Om R) L)
    (hC : C ∈ twinSet (Om R) L) : A = B ∨ A = C ∨ B = C := by
  obtain ⟨a, rfl⟩ := hL
  have hΩ : ConjInvariant (Om R) := by
    rintro m J ⟨b, rfl⟩
    exact ⟨m * b, conjSub_mul m b _⟩
  have key : ∀ M ∈ twinSet (Om R) (conjSub a (tightCore R)),
      conjSub a⁻¹ M ∈ twinSet (Om R) (tightCore R) := by
    intro M hM
    have h := twinSet_conj hΩ hM a⁻¹
    rwa [← conjSub_mul, inv_mul_cancel, conjSub_one] at h
  rcases h2 _ (key A hA) _ (key B hB) _ (key C hC) with h | h | h
  · exact Or.inl ((conjSub_inj a⁻¹).mp h)
  · exact Or.inr (Or.inl ((conjSub_inj a⁻¹).mp h))
  · exact Or.inr (Or.inr ((conjSub_inj a⁻¹).mp h))

theorem eq_one_or_eq_of_pow_two_pow {M : Subgroup Y} {e : Y}
    (hA : ∀ q ∈ M, q * q = 1 → q = 1 ∨ q = e) (hB : ∀ q ∈ M, q * q ≠ e) :
    ∀ k : ℕ, ∀ q ∈ M, q ^ (2 ^ k) = 1 → q = 1 ∨ q = e := by
  intro k
  induction k with
  | zero =>
    intro q _ hq
    left
    simpa using hq
  | succ k ih =>
    intro q hqM hq
    have hq' : (q * q) ^ (2 ^ k) = 1 := by
      rw [← pow_two, ← pow_mul, ← pow_succ']
      exact hq
    rcases ih (q * q) (mul_mem hqM hqM) hq' with h | h
    · exact hA q hqM h
    · exact absurd h (hB q hqM)

theorem card_le_two_of_forall {Q : Subgroup Y} (hQ : IsPGroup 2 Q) {e : Y} (he2 : e * e = 1)
    (h : ∀ q ∈ Q, ∀ k : ℕ, q ^ (2 ^ k) = 1 → q = 1 ∨ q = e) : Nat.card Q ≤ 2 := by
  obtain ⟨k, hk⟩ := hQ.exists_card_eq
  have hle : Q ≤ Subgroup.zpowers e := by
    intro q hq
    have hpow : q ^ (2 ^ k) = 1 := by
      rw [← hk]
      exact orderOf_dvd_iff_pow_eq_one.mp (Subgroup.orderOf_dvd_natCard Q hq)
    rcases h q hq k hpow with rfl | rfl
    · exact Subgroup.one_mem _
    · exact Subgroup.mem_zpowers _
  calc Nat.card Q ≤ Nat.card (Subgroup.zpowers e) := Subgroup.card_le_of_le hle
    _ = orderOf e := Nat.card_zpowers e
    _ ≤ 2 := Nat.le_of_dvd two_pos (orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact he2))

end Generic

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23.Z5b

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
  CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDisc CFSG.ClassicalInvolution.Uniform
  CFSG.ClassicalInvolution.Q3.Q3NL

namespace Z5b

section Cfg

variable {n : ℕ} {Y : Type} [Group Y] [Finite Y] {R : Subgroup Y} {S : Sylow 2 R} {t : Y}
  {K' W : Subgroup Y} {u e g : Y}

theorem p23_sq_ne (hc : P23Cfg n Y R S t K' W u e g) {s : Y} {L : Subgroup Y} (hL : L ∈ Om R)
    (hs : IsUniqueInvolution L s) (hse : s * e = e * s) (hLe : conjSub e L ≠ L) {q : Y}
    (hqs : q * s = s * q) : q * q ≠ e := by
  intro hqq
  have hΩ : ConjInvariant (Om R) := (CoreData.of_S hc.std.perp.core).hyp.conjInvariant
  have hmem : ∀ c : Y, c * s = s * c → conjSub c L ∈ twinSet (Om R) L := by
    intro c hcs
    refine ⟨hΩ c L hL, s, hs, ?_⟩
    have h := hs.conj c
    have hcs' : c * s * c⁻¹ = s := by rw [hcs]; group
    rwa [hcs'] at h
  have hqL : conjSub q L ≠ L := by
    intro h
    apply hLe
    rw [← hqq, conjSub_mul, h, h]
  rcases twoTwins_of_mem hc.std.two hL ⟨hL, s, hs, hs⟩ (hmem q hqs) (hmem e hse.symm) with h | h | h
  · exact hqL h.symm
  · exact hLe h.symm
  · apply hqL
    have h' : conjSub q L = conjSub q (conjSub q L) := by
      rw [← conjSub_mul, hqq]
      exact h
    exact ((conjSub_inj q).mp h').symm

theorem p23_sq_eq_one (hc : P23Cfg n Y R S t K' W u e g)
    (hgen : ∀ x : Y, (rLayer (Om R) e).map (MulAut.conj x).toMonoidHom ≠ rLayer (Om R) e →
      rLayer (Om R) e ⊔ (rLayer (Om R) e).map (MulAut.conj x).toMonoidHom = ⊤)
    (hE : LemL.OmegaOneCenter (rLayer (Om R) e) e) {s : Y} {L : Subgroup Y} (hL : L ∈ Om R)
    (hs : IsUniqueInvolution L s) (hse : s * e = e * s) (hLe : conjSub e L ≠ L) {q : Y}
    (hqE : q ∈ Subgroup.centralizer ((rLayer (Om R) e : Subgroup Y) : Set Y))
    (hqs : q * s = s * q) (hq2 : q * q = 1) : q = 1 ∨ q = e := by
  by_contra hne
  push Not at hne
  obtain ⟨hq1, hqe⟩ := hne
  have hC := CoreData.of_S hc.std.perp.core
  have heE := p23_e_mem_rLayer hc
  have heq : e * q = q * e := Subgroup.mem_centralizer_iff.mp hqE e heE
  set U : Subgroup Y := Subgroup.closure ({e, q} : Set Y) with hU
  have hUE : IsElemAbelian2 U 2 :=
    T7A.isElemAbelian2_closure_pair hc.data.he2 hq2 hc.data.he1 hq1 (Ne.symm hqe) heq
  have heU : e ∈ U := Subgroup.subset_closure (by simp)
  have heC : e ∈ Subgroup.centralizer ((rLayer (Om R) e : Subgroup Y) : Set Y) := by
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    exact Subgroup.mem_centralizer_singleton_iff.mp (rLayer_le_centralizer e hh)
  have hUC : U ≤ Subgroup.centralizer ((rLayer (Om R) e : Subgroup Y) : Set Y) := by
    rw [hU, Subgroup.closure_le]
    rintro x (rfl | rfl)
    · exact heC
    · exact hqE
  have hUs : U ≤ Subgroup.centralizer ({s} : Set Y) := by
    rw [hU, Subgroup.closure_le]
    rintro x (rfl | rfl)
    · exact Subgroup.mem_centralizer_singleton_iff.mpr hse.symm
    · exact Subgroup.mem_centralizer_singleton_iff.mpr hqs
  obtain ⟨V, hV, hUV⟩ := IsSylow2In.exists_ge (IsPGroup.of_card hUE.1) hUs
  obtain ⟨x, hxL, hx4, hxe⟩ := Q3CL.l9_3 hC.partIHypG L hL s hs V hV U hUV hUE e heU hc.data.he1
    (p23_gamma1_le_centralizer hc hgen hE hUC _)
  have hxLe : x ∈ conjSub e L := by
    rw [mem_conjSub_iff]
    have h : e⁻¹ * x * e = x := by
      calc e⁻¹ * x * e = e⁻¹ * (x * e) := by group
        _ = e⁻¹ * (e * x) := by rw [hxe]
        _ = x := by group
    rw [h]
    exact hxL
  exact no_order_four_inf hC.hyp hL (hC.hyp.conjInvariant e L hL) hLe.symm hxL hxLe hx4

theorem p23_card_le_two (hc : P23Cfg n Y R S t K' W u e g)
    (hgen : ∀ x : Y, (rLayer (Om R) e).map (MulAut.conj x).toMonoidHom ≠ rLayer (Om R) e →
      rLayer (Om R) e ⊔ (rLayer (Om R) e).map (MulAut.conj x).toMonoidHom = ⊤)
    (hE : LemL.OmegaOneCenter (rLayer (Om R) e) e) {s : Y} {L : Subgroup Y} (hL : L ∈ Om R)
    (hs : IsUniqueInvolution L s) (hse : s * e = e * s) (hLe : conjSub e L ≠ L) {Q : Subgroup Y}
    (hQ : IsPGroup 2 Q) (hQE : Q ≤ Subgroup.centralizer ((rLayer (Om R) e : Subgroup Y) : Set Y))
    (hQs : Q ≤ Subgroup.centralizer ({s} : Set Y)) : Nat.card Q ≤ 2 := by
  have key := eq_one_or_eq_of_pow_two_pow
    (M := Subgroup.centralizer ((rLayer (Om R) e : Subgroup Y) : Set Y) ⊓
      Subgroup.centralizer ({s} : Set Y)) (e := e)
    (fun q hq hq2 => p23_sq_eq_one hc hgen hE hL hs hse hLe (Subgroup.mem_inf.mp hq).1
      (Subgroup.mem_centralizer_singleton_iff.mp (Subgroup.mem_inf.mp hq).2) hq2)
    (fun q hq => p23_sq_ne hc hL hs hse hLe
      (Subgroup.mem_centralizer_singleton_iff.mp (Subgroup.mem_inf.mp hq).2))
  exact card_le_two_of_forall hQ hc.data.he2 fun q hq k hk =>
    key k q (Subgroup.mem_inf.mpr ⟨hQE hq, hQs hq⟩) hk

end Cfg

end Z5b

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23
