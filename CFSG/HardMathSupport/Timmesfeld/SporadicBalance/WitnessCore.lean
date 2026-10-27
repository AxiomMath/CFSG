module

public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Reduction
public import CFSG.RankThree.PartOne.KS.PlaneWitness
public import CFSG.Sporadic.SmallOddCore.GroupFacts

public section

namespace CFSG.HardMathSupport.Timmesfeld.SporadicBalance

open CFSG.Open CFSG.HardMathSupport.Solomon.LocalBalance CFSG.HardMathSupport.Timmesfeld.Proving
open CFSG.RankThree.PartOne CFSG.Sporadic.SmallOddCore

theorem not_involution_mem_gLAPPrimeCoreOf {A : Type} [Group A] [Finite A] {p : ℕ} (hp : p.Prime)
    (hcen : Subgroup.center A = ⊥) (h : ConjWitness A p) {x : A} (hx : orderOf x = p) {j : A}
    (hj : j ∈ GLAPPrimeCoreOf p (Subgroup.centralizer ({x} : Set A))) (hj2 : orderOf j = 2) :
    False := by
  set C := Subgroup.centralizer ({x} : Set A) with hCdef
  have hψ := conj_injective_of_center_eq_bot hcen
  have hv : orderOf (MulAut.conj j) = 2 := by rw [orderOf_injective _ hψ]; exact hj2
  have hjC : j ∈ C := GLAPPrimeCoreOf_le C hj
  have hjx : j * x = x * j := Subgroup.mem_centralizer_singleton_iff.1 hjC
  have hc : MulAut.conj j * MulAut.conj x = MulAut.conj x * MulAut.conj j := by
    rw [← map_mul, ← map_mul, hjx]
  obtain ⟨l, hl, hdvd⟩ := h (MulAut.conj j) x hv hx hc
  have hprod : (l.map fun g => MulAut.conj g * MulAut.conj j * (MulAut.conj g)⁻¹).prod =
      MulAut.conj (l.map fun g => g * j * g⁻¹).prod := by
    rw [map_list_prod, List.map_map]
    congr 1
    apply List.map_congr_left
    intro g _
    simp only [Function.comp_apply, map_mul, map_inv]
  rw [hprod, orderOf_injective _ hψ] at hdvd
  have hmem : (l.map fun g => g * j * g⁻¹).prod ∈ GLAPPrimeCoreOf p C := by
    apply Subgroup.list_prod_mem
    intro y hy
    obtain ⟨g, hg, rfl⟩ := List.mem_map.1 hy
    exact GLAPPrimeCoreOf_conj_mem g (Subgroup.mem_centralizer_singleton_iff.2 (hl g hg)) j hj
  have hcop := coprime_card_GLAPPrimeCoreOf hp C
  have hord : orderOf (⟨_, hmem⟩ : GLAPPrimeCoreOf p C) ∣ Nat.card (GLAPPrimeCoreOf p C) :=
    orderOf_dvd_natCard _
  rw [Subgroup.orderOf_mk] at hord
  exact (Nat.Prime.coprime_iff_not_dvd hp).1 hcop (hdvd.trans hord)

theorem sq_dvd_card_centralizer {G : Type*} [Group G] [Finite G] {p : ℕ} (hp : p.Prime)
    (hG : p ^ 2 ∣ Nat.card G) {x : G} (hx : orderOf x = p) :
    p ^ 2 ∣ Nat.card ↥(Subgroup.centralizer ({x} : Set G)) := by
  have : Fact p.Prime := ⟨hp⟩
  have hsp : IsPGroup p (Subgroup.zpowers x) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hx, pow_one])
  obtain ⟨S, hS⟩ := hsp.exists_le_sylow
  have hxS : x ∈ (S : Subgroup G) := hS (Subgroup.mem_zpowers x)
  have hScard : p ^ 2 ∣ Nat.card (S : Subgroup G) := by
    rw [Sylow.card_eq_multiplicity]
    exact pow_dvd_pow p ((hp.pow_dvd_iff_le_factorization Nat.card_pos.ne').1 hG)
  set CS := (S : Subgroup G) ⊓ Subgroup.centralizer ({x} : Set G) with hCS
  have hCSp : IsPGroup p CS := S.isPGroup'.to_le inf_le_left
  obtain ⟨k, hk⟩ := hCSp.exists_card_eq
  set Z := (Subgroup.center (S : Subgroup G)).map (S : Subgroup G).subtype with hZ
  have hZCS : Z ≤ CS := by
    rintro _ ⟨z, hz, rfl⟩
    refine Subgroup.mem_inf.2 ⟨z.2, Subgroup.mem_centralizer_singleton_iff.2 ?_⟩
    have := congrArg Subtype.val ((Subgroup.mem_center_iff.1 hz) ⟨x, hxS⟩)
    exact this.symm
  have hxCS : Subgroup.zpowers x ≤ CS :=
    Subgroup.zpowers_le.2 (Subgroup.mem_inf.2 ⟨hxS, Subgroup.mem_centralizer_singleton_iff.2 rfl⟩)
  by_cases hk2 : 2 ≤ k
  · exact (hk ▸ pow_dvd_pow p hk2).trans (Subgroup.card_dvd_of_le inf_le_right)
  · exfalso
    have hcard : Nat.card CS ≤ p := by
      rw [hk]
      calc p ^ k ≤ p ^ 1 := Nat.pow_le_pow_right hp.pos (by omega)
        _ = p := pow_one p
    have hxeq : Subgroup.zpowers x = CS :=
      Subgroup.eq_of_le_of_card_ge hxCS (by rw [Nat.card_zpowers, hx]; exact hcard)
    have hSnt : Nontrivial (S : Subgroup G) := by
      refine Finite.one_lt_card_iff_nontrivial.1 ?_
      have h2 := Nat.le_of_dvd Nat.card_pos hScard
      have : 1 < p ^ 2 := Nat.one_lt_pow (by norm_num) hp.one_lt
      omega
    have hZnt : Nontrivial (Subgroup.center (S : Subgroup G)) := S.isPGroup'.center_nontrivial
    obtain ⟨z, hz1⟩ := exists_ne (1 : Subgroup.center (S : Subgroup G))
    have hzZ : ((z : (S : Subgroup G)) : G) ∈ Z := ⟨z, z.2, rfl⟩
    have hzx : ((z : (S : Subgroup G)) : G) ∈ Subgroup.zpowers x := by
      rw [hxeq]; exact hZCS hzZ
    have hzo : orderOf ((z : (S : Subgroup G)) : G) = p := by
      have h1 := orderOf_dvd_of_mem_zpowers hzx
      rw [hx] at h1
      rcases (Nat.dvd_prime hp).1 h1 with h | h
      · exfalso
        rw [orderOf_eq_one_iff] at h
        exact hz1 (Subtype.ext (Subtype.ext h))
      · exact h
    have hzeq : Subgroup.zpowers ((z : (S : Subgroup G)) : G) = Subgroup.zpowers x :=
      Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.2 hzx)
        (by rw [Nat.card_zpowers, Nat.card_zpowers, hx, hzo])
    have hxz : x ∈ Subgroup.zpowers ((z : (S : Subgroup G)) : G) := by
      rw [hzeq]; exact Subgroup.mem_zpowers x
    have hSle : (S : Subgroup G) ≤ CS := by
      intro s hs
      refine Subgroup.mem_inf.2 ⟨hs, Subgroup.mem_centralizer_singleton_iff.2 ?_⟩
      obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.1 hxz
      rw [← hm]
      have hc : ((z : (S : Subgroup G)) : G) * s = s * ((z : (S : Subgroup G)) : G) :=
        congrArg Subtype.val ((Subgroup.mem_center_iff.1 z.2) ⟨s, hs⟩).symm
      exact ((Commute.zpow_left (show Commute ((z : (S : Subgroup G)) : G) s from hc) m)).eq.symm
    have h1 := Subgroup.card_le_of_le hSle
    have h2 := Nat.le_of_dvd Nat.card_pos hScard
    have : p < p ^ 2 := by
      rw [pow_two]
      exact lt_mul_self hp.one_lt
    omega

theorem gLAPPrimeCoreOf_eq_bot_of_conjWitness_card {A : Type} [Group A] [Finite A]
    {p q a b : ℕ} (hp : p.Prime) (hq : q.Prime) (hq2 : q ≠ 2) (hqp : q < p)
    (hcen : Subgroup.center A = ⊥) (h : ConjWitness A p) (hA : p ^ 2 ∣ Nat.card A) {x : A}
    (hx : orderOf x = p)
    (hC : Nat.card ↥(Subgroup.centralizer ({x} : Set A)) ∣ 2 ^ a * q * p ^ b)
    (hw : ∀ w : A, orderOf w = q → ¬ p ^ 2 ∣ Nat.card ↥(Subgroup.centralizer ({w} : Set A))) :
    GLAPPrimeCoreOf p (Subgroup.centralizer ({x} : Set A)) = ⊥ := by
  have : Fact p.Prime := ⟨hp⟩
  set C := Subgroup.centralizer ({x} : Set A) with hCdef
  set L := GLAPPrimeCoreOf p C with hLdef
  have hLC : L ≤ C := GLAPPrimeCoreOf_le C
  have hcop : Nat.Coprime p (Nat.card L) := coprime_card_GLAPPrimeCoreOf hp C
  have h2 : ¬ 2 ∣ Nat.card L := by
    intro h2
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    obtain ⟨j, hj⟩ := exists_prime_orderOf_dvd_card' (G := L) 2 h2
    exact not_involution_mem_gLAPPrimeCoreOf hp hcen h hx j.2 (by rw [Subgroup.orderOf_coe, hj])
  have hLq : Nat.card L ∣ q := by
    have h1 : Nat.card L ∣ 2 ^ a * q * p ^ b := (Subgroup.card_dvd_of_le hLC).trans hC
    have h3 : Nat.Coprime (Nat.card L) (p ^ b) := (Nat.Coprime.pow_left b hcop).symm
    have h4 : Nat.card L ∣ 2 ^ a * q := h3.dvd_of_dvd_mul_right h1
    have h5 : Nat.Coprime (Nat.card L) (2 ^ a) :=
      Nat.Coprime.pow_right a ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).2 h2).symm
    exact h5.dvd_of_dvd_mul_left h4
  rcases (Nat.dvd_prime hq).1 hLq with h1 | hLq'
  · exact Subgroup.card_eq_one.1 h1
  · exfalso
    have : Fact q.Prime := ⟨hq⟩
    obtain ⟨w, hw3⟩ := exists_prime_orderOf_dvd_card' (G := L) q (by rw [hLq'])
    set w' : A := (w : A) with hw'
    have hwo : orderOf w' = q := by rw [hw', Subgroup.orderOf_coe, hw3]
    have hwL : w' ∈ L := w.2
    obtain ⟨Pc⟩ : Nonempty (Sylow p C) := inferInstance
    set P : Subgroup A := (Pc : Subgroup C).map C.subtype with hP
    have hPC : P ≤ C := Subgroup.map_subtype_le _
    have hPcard : Nat.card P = p ^ (Nat.card C).factorization p := by
      rw [hP, Subgroup.card_map_of_injective C.subtype_injective, Sylow.card_eq_multiplicity]
    have hP2 : p ^ 2 ∣ Nat.card P := by
      rw [hPcard]
      exact pow_dvd_pow p ((hp.pow_dvd_iff_le_factorization Nat.card_pos.ne').1
        (sq_dvd_card_centralizer hp hA hx))
    have hcls : conjClass P w' ⊆ (L : Set A) \ {1} := by
      rintro _ ⟨g, hg, rfl⟩
      refine ⟨GLAPPrimeCoreOf_conj_mem g (hPC hg) w' hwL, ?_⟩
      intro h1
      have h2 : w' = 1 := by
        have := congrArg (fun y => g⁻¹ * y * g) (Set.mem_singleton_iff.1 h1)
        simpa [mul_assoc] using this
      rw [h2, orderOf_one] at hwo
      exact hq.one_lt.ne hwo
    have hncard : (conjClass P w').ncard < p := by
      have h1 : (conjClass P w').ncard ≤ ((L : Set A) \ {1}).ncard :=
        Set.ncard_le_ncard hcls (Set.toFinite _)
      have h2 : ((L : Set A) \ {1}).ncard = q - 1 := by
        rw [Set.ncard_sdiff_singleton_of_mem L.one_mem, ← Nat.card_coe_set_eq (L : Set A),
          SetLike.coe_sort_coe, hLq']
      omega
    have horb := ncard_conjClass_mul_card P w'
    have hdv : (conjClass P w').ncard ∣ p ^ (Nat.card C).factorization p :=
      hPcard ▸ Dvd.intro _ horb
    obtain ⟨i, -, hi⟩ := (Nat.dvd_prime_pow hp).1 hdv
    have hi0 : i = 0 := by
      by_contra hne
      have h1 : p ≤ p ^ i := by
        calc p = p ^ 1 := (pow_one p).symm
          _ ≤ p ^ i := Nat.pow_le_pow_right hp.pos (by omega)
      rw [← hi] at h1
      exact absurd hncard (not_lt.2 h1)
    rw [hi, hi0, pow_zero, one_mul] at horb
    apply hw w' hwo
    have h3 : p ^ 2 ∣ Nat.card ↥(P ⊓ Subgroup.centralizer ({w'} : Set A)) := by
      rw [horb]
      exact hP2
    exact h3.trans (Subgroup.card_dvd_of_le inf_le_right)

end CFSG.HardMathSupport.Timmesfeld.SporadicBalance
