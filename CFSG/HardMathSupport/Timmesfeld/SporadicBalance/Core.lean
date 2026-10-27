module

public import CFSG.Sporadic.SmallOddCore.GroupFacts
public import CFSG.HardMathSupport.Timmesfeld.Coordinator.LocalThreeReduction
public import CFSG.HardMathSupport.Timmesfeld.Proving.GLAPPrimeCoreBasics

public section

namespace CFSG.HardMathSupport.Timmesfeld.SporadicBalance

open CFSG.Open CFSG.HardMathSupport.Timmesfeld.Proving CFSG.Sporadic.SmallOddCore
  CFSG.HardMathSupport.Timmesfeld.Coordinator

variable {p : ℕ} {S : Type*} [Group S]

theorem card_centralizer_conj (c a : S) :
    Nat.card ↥(Subgroup.centralizer ({c * a * c⁻¹} : Set S)) =
      Nat.card ↥(Subgroup.centralizer ({a} : Set S)) := by
  have hψ : Function.Injective (MulAut.conj c : S ≃* S).toMonoidHom :=
    (MulAut.conj c : S ≃* S).injective
  have hc := map_inf_centralizer_of_injective (MulAut.conj c : S ≃* S).toMonoidHom hψ ⊤ a
  rw [top_inf_eq, Subgroup.map_top_of_surjective _ (MulAut.conj c : S ≃* S).surjective,
    top_inf_eq] at hc
  have hs : (MulAut.conj c : S ≃* S).toMonoidHom a = c * a * c⁻¹ := by
    simp [MulAut.conj_apply]
  rw [hs] at hc
  rw [← hc]
  exact Subgroup.card_map_of_injective hψ

theorem card_centralizer_mulEquiv {S' : Type*} [Group S'] (e : S ≃* S') (a : S) :
    Nat.card ↥(Subgroup.centralizer ({e a} : Set S')) =
      Nat.card ↥(Subgroup.centralizer ({a} : Set S)) := by
  have hc := CFSG.HardMathSupport.Timmesfeld.Coordinator.map_inf_centralizer_of_injective
    e.toMonoidHom e.injective ⊤ a
  rw [top_inf_eq, Subgroup.map_top_of_surjective _ e.surjective, top_inf_eq] at hc
  have hs : e.toMonoidHom a = e a := rfl
  rw [hs] at hc
  rw [← hc]
  exact Subgroup.card_map_of_injective e.injective

theorem card_le_of_isPGroup_of_dvd {p : ℕ} (hp : p.Prime) {G : Type*} [Group G] [Finite G]
    {Q : Subgroup G} (hQ : IsPGroup p Q) {n e : ℕ} (hn : ¬ p ^ (e + 1) ∣ n)
    (hdvd : Nat.card Q ∣ n) : Nat.card Q ≤ p ^ e := by
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨k, hk⟩ := hQ.exists_card_eq
  by_contra hlt
  have hek : e + 1 ≤ k := by
    by_contra h
    apply hlt
    rw [hk]
    exact Nat.pow_le_pow_right hp.pos (by omega)
  exact hn ((pow_dvd_pow p hek).trans (hk ▸ hdvd))

theorem gLAPPrimeCoreOf_eq_bot_of_card_bound [Finite S] (hp : p.Prime) {C : Subgroup S}
    {a r m : ℕ} (hC : Nat.card C = p ^ a * r) (hr : ¬ p ∣ r) (hlt : r * m < p ^ a)
    (hm : ∀ w : S, (orderOf w).Prime → orderOf w ∣ r → ∀ Q : Subgroup S, IsPGroup p Q →
      Q ≤ Subgroup.centralizer ({w} : Set S) → Nat.card Q ≤ m) :
    GLAPPrimeCoreOf p C = ⊥ := by
  have : Fact p.Prime := ⟨hp⟩
  by_contra hL
  set L := GLAPPrimeCoreOf p C with hLdef
  have hLC : L ≤ C := GLAPPrimeCoreOf_le C
  have hcop : Nat.Coprime p (Nat.card L) := coprime_card_GLAPPrimeCoreOf hp C
  have hLr : Nat.card L ∣ r := by
    have h1 : Nat.card L ∣ p ^ a * r := hC ▸ Subgroup.card_dvd_of_le hLC
    exact (Nat.Coprime.pow_left a hcop).symm.dvd_of_dvd_mul_left h1
  have hLne : Nat.card L ≠ 1 := fun h => hL (Subgroup.card_eq_one.1 h)
  obtain ⟨q, hq, hqL⟩ := Nat.exists_prime_and_dvd hLne
  have : Fact q.Prime := ⟨hq⟩
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := L) q hqL
  set w : S := (x : S) with hw
  have hwo : orderOf w = q := by rw [hw, Subgroup.orderOf_coe, hx]
  have hwL : w ∈ L := x.2
  obtain ⟨Pc⟩ : Nonempty (Sylow p C) := inferInstance
  set P : Subgroup S := (Pc : Subgroup C).map C.subtype with hP
  have hPC : P ≤ C := Subgroup.map_subtype_le _
  have hPp : IsPGroup p P := Pc.isPGroup'.map C.subtype
  have hr0 : r ≠ 0 := by
    rintro rfl
    have := Nat.card_pos (α := C)
    rw [hC, mul_zero] at this
    exact lt_irrefl _ this
  have hPcard : Nat.card P = p ^ a := by
    rw [hP, Subgroup.card_map_of_injective C.subtype_injective, Sylow.card_eq_multiplicity, hC,
      Nat.factorization_mul (pow_ne_zero _ hp.ne_zero) hr0, hp.factorization_pow,
      Finsupp.add_apply, Finsupp.single_eq_same, Nat.factorization_eq_zero_of_not_dvd hr, add_zero]
  have hcls : conjClass P w ⊆ (L : Set S) := by
    rintro _ ⟨g, hg, rfl⟩
    exact GLAPPrimeCoreOf_conj_mem g (hPC hg) w hwL
  have hncard : (conjClass P w).ncard ≤ r := by
    calc (conjClass P w).ncard ≤ (L : Set S).ncard := Set.ncard_le_ncard hcls (Set.toFinite _)
      _ = Nat.card L := (Nat.card_coe_set_eq (L : Set S)).symm
      _ ≤ r := Nat.le_of_dvd (Nat.pos_of_ne_zero hr0) hLr
  have horb := ncard_conjClass_mul_card P w
  have hQ : Nat.card ↥(P ⊓ Subgroup.centralizer ({w} : Set S)) ≤ m :=
    hm w (by rw [hwo]; exact hq) (by rw [hwo]; exact hqL.trans hLr) _
      (hPp.to_le inf_le_left) inf_le_right
  have : p ^ a ≤ r * m := by
    rw [← hPcard, ← horb]
    exact Nat.mul_le_mul hncard hQ
  omega

end CFSG.HardMathSupport.Timmesfeld.SporadicBalance
