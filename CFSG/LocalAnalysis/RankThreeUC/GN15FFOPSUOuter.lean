module

public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneUModel
public import CFSG.HardMathSupport.Meierfrankenfeld.FFToolkit.OuterBound

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15.GN15

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.QuasithinUnique.Setup
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  CFSG.ComponentClassification.Burgoyne.U CFSG.HardMathSupport.Meierfrankenfeld.FFToolkit

open scoped Matrix

theorem mem_inner_of_uFactor_eq_one {m f : ℕ} {K : Type} [Field K]
    (h : UnitaryFieldData 2 f K) (hn : 3 ≤ m) (hq : ¬(m = 3 ∧ 2 ^ f = 2))
    {β : MulAut (StatedProj (StatedSU m (2 ^ f) K))} (hβ2 : β * β = 1)
    (hfield : uFactor h hn hq β = 1) :
    β ∈ CFSG.ComponentClassification.OuterAutomorphisms.inner
      (StatedProj (StatedSU m (2 ^ f) K)) := by
  classical
  haveI := h.finite
  have hmemD :
      MulAut.congr (uTransport h (by omega : 1 ≤ m)) β ∈
        primeFormD h ((1 : GL (Fin m) K) : Matrix (Fin m) (Fin m) K) := by
    rw [← ker_primeFormFieldFactor h (C := (1 : GL (Fin m) K)) uGram_one hn hq]
    change primeFormFieldFactor h uGram_one hn hq
      (MulAut.congr (uTransport h (by omega : 1 ≤ m)) β) = 1 at hfield
    exact MonoidHom.mem_ker.mpr hfield
  have hodd : Odd (2 ^ f + 1) := by
    obtain ⟨g, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by have := h.one_le; omega : f ≠ 0)
    rw [pow_succ]
    exact ⟨2 ^ g, by ring⟩
  have hdiv :
      Nat.card (primeFormD h ((1 : GL (Fin m) K) : Matrix (Fin m) (Fin m) K) ⧸
        (CFSG.ComponentClassification.OuterAutomorphisms.inner
          (primeFormP h ((1 : GL (Fin m) K) : Matrix (Fin m) (Fin m) K))).subgroupOf
          (primeFormD h ((1 : GL (Fin m) K) : Matrix (Fin m) (Fin m) K))) ∣ 2 ^ f + 1 :=
    card_primeFormD_quotient_dvd h (1 : GL (Fin m) K)
  have hoddq :
      Odd (Nat.card (primeFormD h ((1 : GL (Fin m) K) : Matrix (Fin m) (Fin m) K) ⧸
        (CFSG.ComponentClassification.OuterAutomorphisms.inner
          (primeFormP h ((1 : GL (Fin m) K) : Matrix (Fin m) (Fin m) K))).subgroupOf
          (primeFormD h ((1 : GL (Fin m) K) : Matrix (Fin m) (Fin m) K)))) :=
    Odd.of_dvd_nat hodd hdiv
  let N : Subgroup (primeFormD h ((1 : GL (Fin m) K) : Matrix (Fin m) (Fin m) K)) :=
    (CFSG.ComponentClassification.OuterAutomorphisms.inner
      (primeFormP h ((1 : GL (Fin m) K) : Matrix (Fin m) (Fin m) K))).subgroupOf
      (primeFormD h ((1 : GL (Fin m) K) : Matrix (Fin m) (Fin m) K))
  haveI : N.Normal := inferInstance
  let y : primeFormD h ((1 : GL (Fin m) K) : Matrix (Fin m) (Fin m) K) :=
    ⟨MulAut.congr (uTransport h (by omega : 1 ≤ m)) β, hmemD⟩
  have hy2 : (((QuotientGroup.mk' N) y : primeFormD h
      ((1 : GL (Fin m) K) : Matrix (Fin m) (Fin m) K) ⧸ N)) ^ 2 = 1 := by
    have hyval : (y : MulAut (primeFormP h
        ((1 : GL (Fin m) K) : Matrix (Fin m) (Fin m) K))) =
        MulAut.congr (uTransport h (by omega : 1 ≤ m)) β := rfl
    have hyy : y * y = 1 := by
      apply Subtype.ext
      rw [Subgroup.coe_mul, hyval,
        ← MulEquiv.map_mul (MulAut.congr (uTransport h (by omega : 1 ≤ m))) β β,
        hβ2, map_one, Subgroup.coe_one]
    rw [← map_pow, show y ^ 2 = 1 by rw [pow_two]; exact hyy, map_one]
  have hy1 : ((QuotientGroup.mk' N) y : primeFormD h
      ((1 : GL (Fin m) K) : Matrix (Fin m) (Fin m) K) ⧸ N) = 1 := by
    have h2 : orderOf ((QuotientGroup.mk' N) y) ∣ 2 :=
      orderOf_dvd_of_pow_eq_one hy2
    have h3 : orderOf ((QuotientGroup.mk' N) y) ∣
        Nat.card (primeFormD h ((1 : GL (Fin m) K) : Matrix (Fin m) (Fin m) K) ⧸ N) :=
      orderOf_dvd_natCard _
    have hg : Nat.gcd 2 (Nat.card (primeFormD h ((1 : GL (Fin m) K) : Matrix (Fin m) (Fin m) K)
        ⧸ N)) = 1 := Odd.coprime_two_left hoddq
    have h1 : orderOf ((QuotientGroup.mk' N) y) = 1 := by
      have hd : orderOf ((QuotientGroup.mk' N) y) ∣ Nat.gcd 2
          (Nat.card (primeFormD h ((1 : GL (Fin m) K) : Matrix (Fin m) (Fin m) K) ⧸ N)) :=
        Nat.dvd_gcd h2 h3
      rw [hg] at hd
      exact Nat.dvd_one.mp hd
    exact orderOf_eq_one_iff.mp h1
  have hyN : y ∈ N := (QuotientGroup.eq_one_iff y).mp hy1
  have hmemI : MulAut.congr (uTransport h (by omega : 1 ≤ m)) β ∈
      CFSG.ComponentClassification.OuterAutomorphisms.inner
        (primeFormP h ((1 : GL (Fin m) K) : Matrix (Fin m) (Fin m) K)) :=
    Subgroup.mem_subgroupOf.mp hyN
  rw [← CFSG.ComponentClassification.OuterAutomorphisms.inner_map_congr
    (uTransport h (by omega : 1 ≤ m))] at hmemI
  obtain ⟨α, hα, hαβ⟩ := Subgroup.mem_map.mp hmemI
  have hαβ' : α = β := (MulAut.congr (uTransport h (by omega : 1 ≤ m))).injective hαβ
  rwa [hαβ'] at hα

theorem card_le_two_mul_card_inf_inner {m f : ℕ} {K : Type} [Field K]
    (h : UnitaryFieldData 2 f K) (hm : 4 ≤ m)
    (B : Subgroup (MulAut (StatedProj (StatedSU m (2 ^ f) K))))
    (hBs : ∀ x ∈ B, x * x = 1) :
    Nat.card B ≤ 2 * Nat.card ↥(B ⊓
      (MulAut.conj : StatedProj (StatedSU m (2 ^ f) K) →*
        MulAut (StatedProj (StatedSU m (2 ^ f) K))).range) := by
  classical
  haveI := h.finite
  have hn : 3 ≤ m := by omega
  have hq : ¬(m = 3 ∧ 2 ^ f = 2) := by omega
  haveI : Finite (StatedProj (StatedSU m (2 ^ f) K)) := inferInstance
  haveI : Finite (MulAut (StatedProj (StatedSU m (2 ^ f) K))) :=
    Finite.of_injective (fun g : MulAut (StatedProj (StatedSU m (2 ^ f) K)) =>
        (g : StatedProj (StatedSU m (2 ^ f) K) ≃ StatedProj (StatedSU m (2 ^ f) K)))
      (fun g h gh => MulEquiv.ext fun z => congrArg (fun e => e z) gh)
  let ψ : ↥B →* (K ≃+* K) := (uFactor h hn hq).comp B.subtype
  let barA : K ≃+* K :=
    RingEquiv.ofBijective h.bar ⟨h.bar.injective, fun c => ⟨h.bar c, h.bar_bar c⟩⟩
  have hbarA : ∀ c : K, barA c = h.bar c := fun c => rfl
  have hbarA2 : barA * barA = 1 := by
    ext c
    simp [hbarA, h.bar_bar]
  have hstep : ∀ x : ↥B, ψ x = 1 ∨ ψ x = barA := by
    intro x
    have hx2 : x * x = 1 := Subtype.ext (hBs x.1 x.2)
    have hsq : ψ x * ψ x = 1 := by
      rw [← map_mul, hx2, map_one]
    rcases ringEquiv_eq_refl_or_bar h hsq with h1 | h1
    · exact Or.inl h1
    · right
      ext c
      rw [hbarA]
      exact h1 c
  have hrange : Nat.card ψ.range ≤ 2 := by
    have hle : ψ.range ≤ Subgroup.zpowers barA := by
      intro σ hσ
      obtain ⟨x, rfl⟩ := MonoidHom.mem_range.mp hσ
      rcases hstep x with h1 | h1
      · rw [h1]; exact one_mem _
      · rw [h1]; exact Subgroup.mem_zpowers barA
    have hbarord : orderOf barA ∣ 2 := by
      apply orderOf_dvd_of_pow_eq_one
      rw [pow_two]
      exact hbarA2
    have hle2 : orderOf barA ≤ 2 := Nat.le_of_dvd (by norm_num) hbarord
    calc Nat.card ψ.range ≤ Nat.card (Subgroup.zpowers barA) :=
          Nat.le_of_dvd Nat.card_pos (Subgroup.card_dvd_of_le hle)
      _ = orderOf barA := Nat.card_zpowers barA
      _ ≤ 2 := hle2
  have hker : Nat.card ψ.ker ≤ Nat.card ↥(B ⊓
      (MulAut.conj : StatedProj (StatedSU m (2 ^ f) K) →*
        MulAut (StatedProj (StatedSU m (2 ^ f) K))).range) := by
    let g : ψ.ker → ↥(B ⊓
        (MulAut.conj : StatedProj (StatedSU m (2 ^ f) K) →*
          MulAut (StatedProj (StatedSU m (2 ^ f) K))).range) := fun x =>
      ⟨x.1.1, x.1.2, by
        have hx2 : x.1.1 * x.1.1 = 1 := hBs x.1.1 x.1.2
        have hfield : uFactor h hn hq x.1.1 = 1 := MonoidHom.mem_ker.mp x.2
        exact mem_inner_of_uFactor_eq_one h hn hq hx2 hfield⟩
    have hg : Function.Injective g := by
      intro x y hxy
      have h1 : (g x : MulAut (StatedProj (StatedSU m (2 ^ f) K))) =
          (g y : MulAut (StatedProj (StatedSU m (2 ^ f) K))) := congrArg Subtype.val hxy
      have h2 : x.1.1 = y.1.1 := h1
      exact Subtype.ext (Subtype.ext h2)
    exact Nat.card_le_card_of_injective g hg
  have hcard := Subgroup.card_ker_mul_card_range ψ
  calc Nat.card B = Nat.card ψ.ker * Nat.card ψ.range := hcard.symm
    _ ≤ Nat.card ↥(B ⊓ (MulAut.conj :
        StatedProj (StatedSU m (2 ^ f) K) →*
          MulAut (StatedProj (StatedSU m (2 ^ f) K))).range) * 2 :=
        Nat.mul_le_mul hker hrange
    _ = 2 * Nat.card ↥(B ⊓ (MulAut.conj :
        StatedProj (StatedSU m (2 ^ f) K) →*
          MulAut (StatedProj (StatedSU m (2 ^ f) K))).range) := Nat.mul_comm _ _

theorem card_le_two_mul_card_inf_of_psu {V : Type} [CommGroup V] [Finite V]
    (hV : ∀ v : V, v * v = 1) {L E : Subgroup (MulAut V)} (hirr : X1.IsIrrOn L)
    (hperf : Group.IsPerfect ↥L) {m f : ℕ} (hm : 4 ≤ m)
    (hmodel : StatedClassicalModel (↥L ⧸ Subgroup.center ↥L) .PSU m 2 f)
    (hEN : E ≤ Subgroup.normalizer (L : Set (MulAut V))) (hEel : IsElemAbelian2 E) :
    Nat.card E ≤ 2 * Nat.card ↥(E ⊓ L) := by
  classical
  obtain ⟨⟨hp, hf1, -, -⟩, K, _, _, hK, ⟨e⟩⟩ := hmodel
  have h : UnitaryFieldData 2 f K := ⟨Nat.prime_two, hf1, by rw [hK, ← pow_mul, mul_comm]⟩
  refine card_le_mul_card_inf_of_outer hV hperf hirr hEN hEel e (k := 2) ?_
  intro B _ hBs
  exact card_le_two_mul_card_inf_inner h hm B hBs

end CFSG.LocalAnalysis.RankThreeUC.S15.GN15
