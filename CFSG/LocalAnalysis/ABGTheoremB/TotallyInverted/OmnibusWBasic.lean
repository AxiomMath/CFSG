module

public import CFSG.LocalAnalysis.ABGTheoremB.TotallyInverted.OmnibusQuotient
public import CFSG.GroupTheory.QuasiDihedralFusion.Quotient

public section

namespace CFSG.ABGTheoremB.TotallyInverted.OmnibusW

open CFSG.ABGLocalTools CFSG.QuasiDihedralFusion Omnibus
open scoped Pointwise

variable {G : Type} [Group G] [Finite G] {σ : Setting G} {r : ℕ}

section Powers

omit [Finite G] in
theorem exists_mul_pow_eq {O : Subgroup G} {o u : G} (ho : o ∈ O)
    (hu : u ∈ Subgroup.normalizer (O : Set G)) (n : ℕ) :
    ∃ o' ∈ O, (o * u) ^ n = o' * u ^ n := by
  induction n with
  | zero => exact ⟨1, O.one_mem, by simp⟩
  | succ n ih =>
    obtain ⟨o', ho', he⟩ := ih
    refine ⟨o' * (u ^ n * o * (u ^ n)⁻¹), O.mul_mem ho'
      ((Subgroup.mem_normalizer_iff.mp (Subgroup.pow_mem _ hu n) o).mp ho), ?_⟩
    rw [pow_succ, he, pow_succ]
    group

omit [Finite G] in
theorem exists_pow_mem_of_mem_sup {O Y : Subgroup G}
    (hYO : Y ≤ Subgroup.normalizer (O : Set G)) (hY : ∀ y ∈ Y, ∃ k : ℕ, y ^ r ^ k ∈ O)
    {g : G} (hg : g ∈ O ⊔ Y) : ∃ k : ℕ, g ^ r ^ k ∈ O := by
  have hg' : g ∈ ((O ⊔ Y : Subgroup G) : Set G) := hg
  rw [Subgroup.coe_mul_of_right_le_normalizer_left O Y hYO] at hg'
  obtain ⟨o, ho, y, hy, rfl⟩ := hg'
  obtain ⟨k, hk⟩ := hY y hy
  obtain ⟨o', ho', he⟩ := exists_mul_pow_eq ho (hYO hy) (r ^ k)
  refine ⟨k, ?_⟩
  rw [he]
  exact O.mul_mem ho' hk

theorem le_sup_of_isSylowOf (hr : r.Prime) {O Y V : Subgroup G} (hOY : O ≤ Y)
    (hYO : Y ≤ Subgroup.normalizer (O : Set G)) (hY : ∀ g ∈ Y, ∃ k : ℕ, g ^ r ^ k ∈ O)
    (hV : IsSylowOf r V Y) : Y ≤ O ⊔ V := by
  have : Fact r.Prime := ⟨hr⟩
  have hnormal : (O.subgroupOf Y).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hOY).mpr hYO
  have hq : IsPGroup r (Y ⧸ O.subgroupOf Y) := by
    intro g
    induction g using QuotientGroup.induction_on with | H x => ?_
    obtain ⟨k, hk⟩ := hY x x.2
    refine ⟨k, ?_⟩
    rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]
    exact hk
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hq
  have hOidx : O.relIndex Y = r ^ n := by rw [Subgroup.relIndex, Subgroup.index_eq_card, hn]
  have hOVY : O ⊔ V ≤ Y := sup_le hOY hV.le
  have h1 : (O ⊔ V).relIndex Y ∣ r ^ n := by
    rw [← hOidx, ← Subgroup.relIndex_mul_relIndex O (O ⊔ V) Y le_sup_left hOVY]
    exact dvd_mul_left _ _
  have h2 : (O ⊔ V).relIndex Y ∣ V.relIndex Y := by
    rw [← Subgroup.relIndex_mul_relIndex V (O ⊔ V) Y le_sup_right hOVY]
    exact dvd_mul_left _ _
  obtain ⟨-, -, hVidx⟩ := isSylowOf_iff.mp hV
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow hr).mp h1
  have hj0 : j = 0 := by
    by_contra hj0
    apply hVidx
    rw [hj] at h2
    exact (dvd_pow_self r hj0).trans h2
  exact Subgroup.relIndex_eq_one.mp (by rw [hj, hj0, pow_zero])

theorem isSylowOf_of_isSylowOf_oddCoreIn (hr : r.Prime) (hr2 : r ≠ 2) {X V : Subgroup G}
    (hX : CFSG.HasNormalPComplement 2 X) (hV : IsSylowOf r V (oddCoreIn X)) :
    IsSylowOf r V X := by
  have : Fact r.Prime := ⟨hr⟩
  obtain ⟨hVle, hVp, hVidx⟩ := isSylowOf_iff.mp hV
  obtain ⟨k, hk⟩ := exists_relIndex_oddCoreIn_eq_two_pow hX
  refine isSylowOf_iff.mpr ⟨hVle.trans (oddCoreIn_le X), hVp, ?_⟩
  rw [← Subgroup.relIndex_mul_relIndex _ _ _ hVle (oddCoreIn_le X), hk]
  intro hdvd
  rcases (Nat.Prime.dvd_mul hr).mp hdvd with h | h
  · exact hVidx h
  · exact hr2 ((Nat.prime_dvd_prime_iff_eq hr Nat.prime_two).mp (hr.dvd_of_dvd_pow h))

end Powers

section OddCores

omit [Finite G] in
theorem odd_card_sup {O P : Subgroup G} (hPO : P ≤ Subgroup.normalizer (O : Set G))
    (hO : Odd (Nat.card O)) (hP : Odd (Nat.card P)) :
    Odd (Nat.card (O ⊔ P : Subgroup G)) := by
  have h1 := Subgroup.relIndex_mul_card O (O ⊔ P)
  rw [inf_eq_left.mpr le_sup_left, sup_comm,
    relIndex_sup_of_mul_comm (mul_comm_of_le_normalizer hPO), sup_comm] at h1
  rw [← h1]
  exact (hP.of_dvd_nat (Subgroup.relIndex_dvd_card _ _)).mul hO

omit [Finite G] in
theorem inf_le_oddCoreIn {K A : Subgroup G} (hKA : K ≤ Subgroup.normalizer (A : Set G))
    (hA : Odd (Nat.card A)) : K ⊓ A ≤ oddCoreIn K :=
  le_oddCoreIn inf_le_left
    (fun _ hk => mem_normalizer_inf (Subgroup.le_normalizer hk) (hKA hk))
    (hA.of_dvd_nat (Subgroup.card_dvd_of_le inf_le_right))

theorem oddCoreIn_le_oddCoreIn {H K : Subgroup G} (hKH : K ≤ H)
    (hdec : H ≤ oddCoreIn H ⊔ K) : oddCoreIn K ≤ oddCoreIn H := by
  set O : Subgroup G := oddCoreIn H with hOdef
  set P : Subgroup G := oddCoreIn K with hPdef
  have hHO : H ≤ Subgroup.normalizer (O : Set G) := le_normalizer_oddCoreIn H
  have hKO : K ≤ Subgroup.normalizer (O : Set G) := hKH.trans hHO
  have hPO : P ≤ Subgroup.normalizer (O : Set G) := (oddCoreIn_le K).trans hKO
  have hcoe : ((O ⊔ P : Subgroup G) : Set G) = O * P :=
    Subgroup.coe_mul_of_right_le_normalizer_left O P hPO
  have hO' : O ≤ Subgroup.normalizer ((O ⊔ P : Subgroup G) : Set G) := by
    intro o ho
    apply mem_normalizer_of_conj_le
    intro x hx
    have hx' : x ∈ ((O ⊔ P : Subgroup G) : Set G) := hx
    rw [hcoe] at hx'
    obtain ⟨o₁, ho₁, p, hp, rfl⟩ := hx'
    have h1 : p * o⁻¹ * p⁻¹ ∈ O :=
      (Subgroup.mem_normalizer_iff.mp (hPO hp) _).mp (O.inv_mem ho)
    rw [show o * (o₁ * p) * o⁻¹ = o * o₁ * (p * o⁻¹ * p⁻¹) * p by group]
    exact Subgroup.mul_mem_sup (O.mul_mem (O.mul_mem ho ho₁) h1) hp
  have hK' : K ≤ Subgroup.normalizer ((O ⊔ P : Subgroup G) : Set G) := fun k hk =>
    mem_normalizer_sup (hKO hk) (le_normalizer_oddCoreIn K hk)
  have hodd := odd_card_sup hPO (odd_card_oddCoreIn H) (odd_card_oddCoreIn K)
  exact le_sup_right.trans (le_oddCoreIn (sup_le (oddCoreIn_le H) ((oddCoreIn_le K).trans hKH))
    (hdec.trans (sup_le hO' hK')) hodd)

theorem isQGroup_of_le_sup {H K : Subgroup G} (hKH : K ≤ H) (hdec : H ≤ oddCoreIn H ⊔ K)
    (hH : IsQGroup H) : IsQGroup K := by
  set φ : K →* H ⧸ CFSG.oddCore H :=
    (QuotientGroup.mk' (CFSG.oddCore H)).comp (Subgroup.inclusion hKH) with hφ
  have hsurj : Function.Surjective φ := by
    intro q
    induction q using QuotientGroup.induction_on with | H h => ?_
    have hh : (h : G) ∈ ((oddCoreIn H ⊔ K : Subgroup G) : Set G) := hdec h.2
    rw [Subgroup.coe_mul_of_right_le_normalizer_left _ _
      (hKH.trans (le_normalizer_oddCoreIn H))] at hh
    obtain ⟨o, ho, k, hk, he⟩ := hh
    have hoH : o ∈ H := oddCoreIn_le H ho
    have ho' : (⟨o, hoH⟩ : H) ∈ CFSG.oddCore H := by
      obtain ⟨y, hy, hyo⟩ := ho
      have : y = ⟨o, hoH⟩ := Subtype.ext hyo
      rwa [← this]
    have hh' : h = ⟨o, hoH⟩ * ⟨k, hKH hk⟩ := Subtype.ext he.symm
    refine ⟨⟨k, hk⟩, ?_⟩
    rw [hh', QuotientGroup.mk_mul, (QuotientGroup.eq_one_iff _).mpr ho', one_mul]
    rfl
  have hker : Odd (Nat.card φ.ker) := by
    have hk : φ.ker = (CFSG.oddCore H).comap (Subgroup.inclusion hKH) := by
      rw [hφ, ← MonoidHom.comap_ker, QuotientGroup.ker_mk']
    rw [hk]
    exact (odd_card_oddCore H).of_dvd_nat
      (Subgroup.card_comap_dvd_of_injective _ _ (Subgroup.inclusion_injective hKH))
  exact (isQGroup_iff_of_oddKernel φ hsurj hker).mp (isQGroup_quotient_oddCore_iff.mpr hH)

end OddCores

section Lift

variable {H K : Subgroup G}

theorem inf_mem_liftedSignalizers (hσ : σ.IsValid) (hKH : K ≤ H) (hCK : σ.C ≤ K)
    (hOK : oddCoreIn K ≤ oddCoreIn H) {X : Subgroup G} (hX : X ∈ liftedSignalizers σ H r) :
    X ⊓ K ∈ liftedSignalizers σ K r := by
  obtain ⟨hOX, -, hXr, hTX, hXperm⟩ := hX
  have hKO : K ⊓ oddCoreIn H ≤ oddCoreIn K :=
    inf_le_oddCoreIn (hKH.trans (le_normalizer_oddCoreIn H)) (odd_card_oddCoreIn H)
  refine ⟨le_inf (hOK.trans hOX) (oddCoreIn_le K), inf_le_right, fun g hg => ?_,
    fun t ht => mem_normalizer_inf (hTX ht)
      (Subgroup.le_normalizer (((σ.T_le_C hσ).trans hCK) ht)),
    inf_mul_comm_of_le hCK hXperm⟩
  obtain ⟨k, hk⟩ := hXr g hg.1
  exact ⟨k, hKO ⟨K.pow_mem hg.2 _, hk⟩⟩

theorem oddCoreIn_sup_mem_liftedSignalizers_of_le (hσ : σ.IsValid) (hKH : K ≤ H)
    (hCK : σ.C ≤ K) (hOK : oddCoreIn K ≤ oddCoreIn H) {Y : Subgroup G}
    (hY : Y ∈ liftedSignalizers σ K r) : oddCoreIn H ⊔ Y ∈ liftedSignalizers σ H r := by
  obtain ⟨-, hYK, hYr, hTY, hYperm⟩ := hY
  have hHO : H ≤ Subgroup.normalizer ((oddCoreIn H : Subgroup G) : Set G) :=
    le_normalizer_oddCoreIn H
  have hYO := (hYK.trans hKH).trans hHO
  have hCO : σ.C ≤ Subgroup.normalizer ((oddCoreIn H : Subgroup G) : Set G) :=
    (hCK.trans hKH).trans hHO
  refine ⟨le_sup_left, sup_le (oddCoreIn_le H) (hYK.trans hKH),
    fun g hg => exists_pow_mem_of_mem_sup hYO (fun y hy => (hYr y hy).imp fun _ hk => hOK hk) hg,
    fun t ht => mem_normalizer_sup (hHO ((hCK.trans hKH) ((σ.T_le_C hσ) ht))) (hTY ht), ?_⟩
  rw [Subgroup.coe_mul_of_right_le_normalizer_left _ _ hYO, mul_assoc, hYperm, ← mul_assoc,
    ← mul_comm_of_le_normalizer hCO, mul_assoc]

omit [Finite G] in
theorem eq_oddCoreIn_sup_inf (hKH : K ≤ H) (hdec : H ≤ oddCoreIn H ⊔ K) {X : Subgroup G}
    (hX : X ∈ liftedSignalizers σ H r) : X = oddCoreIn H ⊔ X ⊓ K := by
  obtain ⟨hOX, hXH, -, -, -⟩ := hX
  refine le_antisymm (fun x hx => ?_) (sup_le hOX inf_le_left)
  have hx' : x ∈ ((oddCoreIn H ⊔ K : Subgroup G) : Set G) := hdec (hXH hx)
  rw [Subgroup.coe_mul_of_right_le_normalizer_left _ _
    (hKH.trans (le_normalizer_oddCoreIn H))] at hx'
  obtain ⟨o, ho, k, hk, rfl⟩ := hx'
  have hkX : k ∈ X := by
    have := X.mul_mem (X.inv_mem (hOX ho)) hx
    rwa [inv_mul_cancel_left] at this
  exact Subgroup.mul_mem_sup ho ⟨hkX, hk⟩

theorem inf_mem_maximals (hσ : σ.IsValid) (hKH : K ≤ H) (hCK : σ.C ≤ K)
    (hdec : H ≤ oddCoreIn H ⊔ K) (hOK : oddCoreIn K ≤ oddCoreIn H) {X : Subgroup G}
    (hX : X ∈ maximals (liftedSignalizers σ H r)) :
    X ⊓ K ∈ maximals (liftedSignalizers σ K r) := by
  refine ⟨inf_mem_liftedSignalizers hσ hKH hCK hOK hX.1, fun Y hY hle => ?_⟩
  have h1 := oddCoreIn_sup_mem_liftedSignalizers_of_le hσ hKH hCK hOK hY
  have h2 : X ≤ oddCoreIn H ⊔ Y :=
    (eq_oddCoreIn_sup_inf hKH hdec hX.1).le.trans (sup_le_sup_left hle _)
  have h3 := hX.2 _ h1 h2
  exact le_antisymm (le_inf (le_sup_right.trans h3.le) hY.2.1) hle

theorem conjugate_of_conjugate_inf (hσ : σ.IsValid) (hKH : K ≤ H) (hCK : σ.C ≤ K)
    (hdec : H ≤ oddCoreIn H ⊔ K) (hK : Conjugate σ K r) : Conjugate σ H r := by
  have hOK := oddCoreIn_le_oddCoreIn hKH hdec
  intro X hX X' hX'
  obtain ⟨m, ⟨hmK, hmT⟩, hm⟩ := hK _ (inf_mem_maximals hσ hKH hCK hdec hOK hX) _
    (inf_mem_maximals hσ hKH hCK hdec hOK hX')
  refine ⟨m, ⟨hKH hmK, hmT⟩, ?_⟩
  rw [eq_oddCoreIn_sup_inf hKH hdec hX'.1, conjSub_sup, hm,
    conjSub_eq_self (le_normalizer_oddCoreIn H (hKH hmK))]
  exact (eq_oddCoreIn_sup_inf hKH hdec hX.1).symm

end Lift

end CFSG.ABGTheoremB.TotallyInverted.OmnibusW
