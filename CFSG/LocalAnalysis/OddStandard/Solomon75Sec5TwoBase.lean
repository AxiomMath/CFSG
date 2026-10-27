module

public import CFSG.LocalAnalysis.OddStandard.Solomon75Sec5BaseF4
public import CFSG.LocalAnalysis.OddStandard.Solomon75Sec4Center
public import CFSG.LocalAnalysis.OddStandard.Solomon75Sec3Lemma33Struct

public section

namespace CFSG.OddStandard.Solomon75

namespace Sec5Two

open Subgroup CFSG CFSG.GH74.GLS

open scoped commutatorElement

variable {X : Type} [Group X] [Finite X] {n : ℕ} {z : X}
  {S : Sylow 2 ↥(normalizer ((zpowers z : Subgroup X) : Set X))}

theorem isIntrinsicIn_z (h : Sec5Data X n z (zpowers z) S) {A : Subgroup X}
    (hA : Sec5Comp X n (centralizer ({z} : Set X)) A) :
    IsIntrinsicIn X (centralizer ({z} : Set X)) A z := by
  obtain ⟨⟨u₀, hu₀⟩, hn⟩ := hA
  obtain ⟨u, huZ, hu⟩ := h.pair.exists_witness_mem hu₀ hn
  have hu2 : orderOf u = 2 := hu.1
  have hu1 : u ≠ 1 := fun e => by rw [e, orderOf_one] at hu2; omega
  rcases zpowers_eq_of_orderOf_two h.orderOf_z u huZ with e | e
  · exact absurd e hu1
  · rw [e] at hu; exact hu

theorem z_mem_comp (h : Sec5Data X n z (zpowers z) S) {A : Subgroup X}
    (hA : Sec5Comp X n (centralizer ({z} : Set X)) A) : z ∈ A :=
  (isIntrinsicIn_z h hA).2.1

omit [Finite X] in
theorem comp_le {H A : Subgroup X} (hA : Sec5Comp X n H A) : A ≤ H :=
  hA.isPCompIn.1

omit [Finite X] in
theorem comp_le_K0 {H A : Subgroup X} (hA : Sec5Comp X n H A) : A ≤ K0 X n H :=
  le_sSup hA

theorem comp_isPCompIn_K0 {H A : Subgroup X} (hA : Sec5Comp X n H A) :
    IsPCompIn 2 (K0 X n H) A := by
  obtain ⟨⟨u, hu⟩, hn⟩ := hA
  exact hu.isPCompIn_K0 hn

theorem z_mem_K0 (h : Sec5Data X n z (zpowers z) S) {A : Subgroup X}
    (hA : Sec5Comp X n (centralizer ({z} : Set X)) A) :
    z ∈ K0 X n (centralizer ({z} : Set X)) :=
  comp_le_K0 hA (z_mem_comp h hA)

omit [Finite X] in
theorem comm_z_of_mem_comp {A : Subgroup X} (hA : Sec5Comp X n (centralizer ({z} : Set X)) A)
    {a : X} (ha : a ∈ A) : a * z = z * a :=
  Subgroup.mem_centralizer_singleton_iff.1 (comp_le hA ha)

theorem core_K0_eq (H : Subgroup X) :
    pPrimeCoreOf 2 (K0 X n H) = K0 X n H ⊓ pPrimeCoreOf 2 H :=
  oddCoreOf_eq_inf (K0_le n H) (Sec5Data.le_normalizer_K0 X n H)

theorem inf_core_eq {H A : Subgroup X} (hA : Sec5Comp X n H A) :
    A ⊓ pPrimeCoreOf 2 (K0 X n H) = pPrimeCoreOf 2 A :=
  le_antisymm (inf_oddCoreOf_le (comp_le_K0 hA))
    (le_inf (oddCoreOf_le A) (oddCoreOf_le_of_isPCompIn (comp_isPCompIn_K0 hA)))

theorem comm_mem_of_ne {H A A' : Subgroup X} (hA : Sec5Comp X n H A) (hA' : Sec5Comp X n H A')
    (hne : A ≠ A') : ∀ a ∈ A, ∀ b ∈ A', ⁅a, b⁆ ∈ pPrimeCoreOf 2 (K0 X n H) := by
  obtain ⟨⟨u, hu⟩, hn⟩ := hA
  obtain ⟨⟨u', hu'⟩, hn'⟩ := hA'
  exact K0_comm_mem_of_ne hu hn hu' hn' hne

theorem exists_conj_of_isSylowTwoIn {W P Q : Subgroup X} (hP : IsSylowTwoIn W P)
    (hQ : IsSylowTwoIn W Q) : ∃ y ∈ W, Q = P.map (MulAut.conj y).toMonoidHom := by
  have hfact : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hPW, hPp, hPidx⟩ := hP
  obtain ⟨hQW, hQp, hQidx⟩ := hQ
  let P' : Sylow 2 ↥W := IsPGroup.toSylow (P := P.subgroupOf W)
    (hPp.of_equiv (Subgroup.subgroupOfEquivOfLe hPW).symm) hPidx
  let Q' : Sylow 2 ↥W := IsPGroup.toSylow (P := Q.subgroupOf W)
    (hQp.of_equiv (Subgroup.subgroupOfEquivOfLe hQW).symm) hQidx
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (↥W) P' Q'
  refine ⟨(g : X), g.2, ?_⟩
  ext x
  constructor
  · intro hx
    have hxW : x ∈ W := hQW hx
    have hmem : (⟨x, hxW⟩ : ↥W) ∈ ((g • P' : Sylow 2 ↥W) : Subgroup ↥W) := by
      rw [hg]; exact hx
    rw [mem_smul_sylow_iff] at hmem
    have h2 : (g : X)⁻¹ * x * g ∈ P := hmem
    exact ⟨(g : X)⁻¹ * x * g, h2, by simp [MulAut.conj_apply, mul_assoc]⟩
  · rintro ⟨y, hy, rfl⟩
    have hyW : y ∈ W := hPW hy
    have hmem : (⟨(g : X) * y * (g : X)⁻¹, mul_mem (mul_mem g.2 hyW) (inv_mem g.2)⟩ : ↥W) ∈
        ((g • P' : Sylow 2 ↥W) : Subgroup ↥W) := by
      rw [mem_smul_sylow_iff]
      show (g : X)⁻¹ * ((g : X) * y * (g : X)⁻¹) * g ∈ P
      simpa [mul_assoc] using hy
    rw [hg] at hmem
    exact hmem

omit [Finite X] in
theorem exists_mul_of_mem_sup {A O : Subgroup X} (h : A ≤ normalizer (O : Set X)) {x : X}
    (hx : x ∈ A ⊔ O) : ∃ a ∈ A, ∃ o ∈ O, x = a * o := by
  rw [sup_comm] at hx
  obtain ⟨o, ho, a, ha, rfl⟩ :=
    (CFSG.SignalizerFunctor.Helpers.mem_sup_of_normalizing O A h x).1 hx
  refine ⟨a, ha, a⁻¹ * o * a, ?_, by group⟩
  have := (Subgroup.mem_normalizer_iff.1 (h (A.inv_mem ha)) o).1 ho
  simpa using this

omit [Finite X] in
theorem not_comm_mod_core {H A : Subgroup X} (hA : Sec5Comp X n H A)
    (hcomm : ∀ a ∈ A, ∀ b ∈ A, ⁅a, b⁆ ∈ pPrimeCoreOf 2 A) : False := by
  obtain ⟨⟨-, -, x, y, hxy⟩, -, -⟩ := hA.2
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective x
  obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective y
  obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective x
  obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective y
  apply hxy
  have hc : (⁅a, b⁆ : ↥A) ∈ pPrimeCore 2 ↥A := by
    obtain ⟨_, h2⟩ := mem_oddCoreOf_iff.1 (hcomm (a : X) a.2 (b : X) b.2)
    exact h2
  have h1 : (QuotientGroup.mk ⁅a, b⁆ : ↥A ⧸ pPrimeCore 2 ↥A) = 1 :=
    (QuotientGroup.eq_one_iff _).2 hc
  have h2 : (QuotientGroup.mk a : ↥A ⧸ pPrimeCore 2 ↥A) * QuotientGroup.mk b =
      QuotientGroup.mk b * QuotientGroup.mk a := by
    have h3 := (map_commutatorElement (QuotientGroup.mk' (pPrimeCore 2 ↥A)) a b).symm.trans h1
    exact commutatorElement_eq_one_iff_mul_comm.1 h3
  show (QuotientGroup.mk (QuotientGroup.mk a) : (↥A ⧸ pPrimeCore 2 ↥A) ⧸ center _) *
    QuotientGroup.mk (QuotientGroup.mk b) = _
  rw [← QuotientGroup.mk_mul, h2, QuotientGroup.mk_mul]

theorem eq_of_le_sup_core {H A A' : Subgroup X} (hA : Sec5Comp X n H A)
    (hA' : Sec5Comp X n H A') (hle : A' ≤ A ⊔ pPrimeCoreOf 2 (K0 X n H)) : A' = A := by
  by_contra hne
  set D := K0 X n H with hD
  set O := pPrimeCoreOf 2 D with hO
  have hOn : ∀ d ∈ D, ∀ o ∈ O, d * o * d⁻¹ ∈ O := fun d hd o ho =>
    (Subgroup.mem_normalizer_iff.1 (mem_normalizer_pPrimeCoreOf_of_mem hd) o).1 ho
  have hAD : A ≤ D := comp_le_K0 hA
  have hA'D : A' ≤ D := comp_le_K0 hA'
  have hOD : O ≤ D := oddCoreOf_le D
  have hAn : A ≤ normalizer (O : Set X) := fun a ha => mem_normalizer_pPrimeCoreOf_of_mem (hAD ha)
  have hcomm : ∀ a ∈ A, ∀ b ∈ A', ⁅a, b⁆ ∈ O := comm_mem_of_ne hA hA' (Ne.symm hne)
  have hall : ∀ a' ∈ A', ∀ b' ∈ A', ⁅a', b'⁆ ∈ O := by
    intro a' ha' b' hb'
    obtain ⟨a₁, ha₁, o₁, ho₁, rfl⟩ := exists_mul_of_mem_sup hAn (hle ha')
    obtain ⟨a₂, ha₂, o₂, ho₂, hb2⟩ := exists_mul_of_mem_sup hAn (hle hb')
    have h1 : ⁅a₁ * o₁, b'⁆ ∈ O := by
      have e : ⁅a₁ * o₁, b'⁆ = (a₁ * ⁅o₁, b'⁆ * a₁⁻¹) * ⁅a₁, b'⁆ := by
        simp only [commutatorElement_def]; group
      rw [e]
      refine O.mul_mem ?_ (hcomm a₁ ha₁ b' hb')
      have hb'D : b' ∈ D := hA'D hb'
      have h5 : ⁅o₁, b'⁆ ∈ O := by
        have : ⁅o₁, b'⁆ = o₁ * (b' * o₁⁻¹ * b'⁻¹) := by
          simp only [commutatorElement_def]; group
        rw [this]
        exact O.mul_mem ho₁ (hOn b' hb'D _ (O.inv_mem ho₁))
      exact hOn a₁ (hAD ha₁) _ h5
    have ha'D : a₁ * o₁ ∈ D := D.mul_mem (hAD ha₁) (hOD ho₁)
    have e2 : ⁅a₁ * o₁, b'⁆ = ⁅a₁ * o₁, a₂ * o₂⁆ := by rw [← hb2]
    have e3 : ⁅a₁ * o₁, a₂ * o₂⁆ = ⁅a₁ * o₁, a₂⁆ * (a₂ * ⁅a₁ * o₁, o₂⁆ * a₂⁻¹) := by
      simp only [commutatorElement_def]; group
    have h2 : ⁅a₁ * o₁, a₂⁆ ∈ O := by
      have : ⁅a₁ * o₁, a₂⁆ = (⁅a₂, a₁ * o₁⁆)⁻¹ := by
        simp only [commutatorElement_def]; group
      rw [this]
      exact O.inv_mem (hcomm a₂ ha₂ _ ha')
    have h3 : ⁅a₁ * o₁, o₂⁆ ∈ O := by
      have : ⁅a₁ * o₁, o₂⁆ = ((a₁ * o₁) * o₂ * (a₁ * o₁)⁻¹) * o₂⁻¹ := by
        simp only [commutatorElement_def]
      rw [this]
      exact O.mul_mem (hOn _ ha'D o₂ ho₂) (O.inv_mem ho₂)
    have h4 : a₂ * ⁅a₁ * o₁, o₂⁆ * a₂⁻¹ ∈ O := hOn a₂ (hAD ha₂) _ h3
    rw [e2, e3]
    exact O.mul_mem h2 h4
  refine not_comm_mod_core hA' (fun a ha b hb => ?_)
  rw [← inf_core_eq hA']
  refine ⟨?_, hall a ha b hb⟩
  have e : ⁅a, b⁆ = a * (b * a⁻¹ * b⁻¹) := by simp only [commutatorElement_def]; group
  rw [e]
  exact A'.mul_mem ha (A'.mul_mem (A'.mul_mem hb (A'.inv_mem ha)) (A'.inv_mem hb))

theorem normalizes_of_comm {H A : Subgroup X} (hA : Sec5Comp X n H A) {c : X}
    (hc : c ∈ normalizer (H : Set X))
    (hcomm : ∀ a ∈ A, ⁅a, c⁆ ∈ pPrimeCoreOf 2 (K0 X n H)) :
    c ∈ normalizer (A : Set X) ∧ ∀ a ∈ A, ⁅a, c⁆ ∈ pPrimeCoreOf 2 A := by
  have hA' := Sec5Comp.map_conj hA hc
  have hle : A.map (MulAut.conj c).toMonoidHom ≤ A ⊔ pPrimeCoreOf 2 (K0 X n H) := by
    rintro _ ⟨a, ha, rfl⟩
    have e : (MulAut.conj c).toMonoidHom a = (⁅a, c⁆)⁻¹ * a := by
      simp only [commutatorElement_def]
      simp [MulAut.conj_apply]
      group
    rw [e]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_right ((pPrimeCoreOf 2 (K0 X n H)).inv_mem
      (hcomm a ha))) (Subgroup.mem_sup_left ha)
  have heq := eq_of_le_sup_core hA hA' hle
  have hcn : c ∈ normalizer (A : Set X) := mem_normalizer_of_map_conj_eq heq
  refine ⟨hcn, fun a ha => ?_⟩
  rw [← inf_core_eq hA]
  refine ⟨?_, hcomm a ha⟩
  have e : ⁅a, c⁆ = a * (c * a⁻¹ * c⁻¹) := by simp only [commutatorElement_def]; group
  rw [e]
  exact A.mul_mem ha ((Subgroup.mem_normalizer_iff.1 hcn a⁻¹).1 (A.inv_mem ha))

theorem eq_one_of_mem_oddCoreOf_of_pow {H : Subgroup X} {x : X} (hx : x ∈ oddCoreOf H) {k : ℕ}
    (hk : x ^ (2 ^ k) = 1) : x = 1 := by
  have hodd := odd_card_oddCoreOf H
  have h1 : x ^ Nat.card (oddCoreOf H) = 1 := by
    have := pow_card_eq_one' (G := oddCoreOf H) (x := ⟨x, hx⟩)
    exact congrArg Subtype.val this
  have hcop : Nat.Coprime (2 ^ k) (Nat.card (oddCoreOf H)) :=
    Nat.Coprime.pow_left k (Nat.coprime_two_left.2 hodd)
  have := pow_gcd_eq_one.2 ⟨hk, h1⟩
  rwa [Nat.Coprime.gcd_eq_one hcop, pow_one] at this

theorem eq_of_inv_mul_mem_oddCoreOf {H : Subgroup X} {a b : X} (hab : a * b = b * a) {k : ℕ}
    (ha : a ^ (2 ^ k) = 1) (hb : b ^ (2 ^ k) = 1) (h : a⁻¹ * b ∈ oddCoreOf H) : a = b := by
  have hc : Commute a⁻¹ b := (Commute.inv_left (show Commute a b from hab))
  have h1 : (a⁻¹ * b) ^ (2 ^ k) = 1 := by
    rw [hc.mul_pow, inv_pow, ha, hb]; simp
  have := eq_one_of_mem_oddCoreOf_of_pow h h1
  have h2 : b = a := by
    calc b = a * (a⁻¹ * b) := by group
      _ = a := by rw [this, mul_one]
  exact h2.symm

theorem sylow_center (h : Sec5Data X n z (zpowers z) S) {A : Subgroup X}
    (hA : Sec5Comp X n (centralizer ({z} : Set X)) A) (P : Sylow 2 ↥A) :
    z ∈ (P : Subgroup ↥A).map A.subtype ∧
      ∀ x ∈ (P : Subgroup ↥A).map A.subtype,
        (∀ y ∈ (P : Subgroup ↥A).map A.subtype, x * y = y * x) → x ∈ zpowers z := by
  have hfact : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hn8 : 8 ≤ n := h.maxdeg.1
  have hK := hA.2
  set N := pPrimeCore 2 ↥A with hN
  let π : ↥A →* ↥A ⧸ N := QuotientGroup.mk' N
  have hπ : Function.Surjective π := QuotientGroup.mk'_surjective N
  have hzA := z_mem_comp h hA
  set ζ : ↥A ⧸ N := π ⟨z, hzA⟩ with hζ
  have hz2 : z ^ 2 = 1 := by
    have := pow_orderOf_eq_one z
    rwa [h.orderOf_z] at this
  have hz1 : z ≠ 1 := fun e => by
    have := h.orderOf_z
    rw [e, orderOf_one] at this
    omega
  have hζ1 : ζ ≠ 1 := by
    intro h1
    have h2 : (⟨z, hzA⟩ : ↥A) ∈ N := (QuotientGroup.eq_one_iff _).1 h1
    have h3 : z ∈ oddCoreOf A := mem_oddCoreOf_iff.2 ⟨hzA, h2⟩
    exact hz1 (eq_one_of_mem_oddCoreOf_of_pow (k := 1) h3 (by simpa using hz2))
  have hζc : ζ ∈ center (↥A ⧸ N) := by
    rw [Subgroup.mem_center_iff]
    intro k
    obtain ⟨a, rfl⟩ := hπ k
    show π a * π ⟨z, hzA⟩ = π ⟨z, hzA⟩ * π a
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (comm_z_of_mem_comp hA a.2)
  let Pb : Sylow 2 (↥A ⧸ N) := Sylow.mapSurjective hπ P
  have hPbeq : (Pb : Subgroup (↥A ⧸ N)) = (P : Subgroup ↥A).map π :=
    Sylow.coe_mapSurjective hπ P
  have hPb : ∀ q ∈ (Pb : Subgroup (↥A ⧸ N)), ∃ y ∈ (P : Subgroup ↥A), π y = q := by
    intro q hq
    rw [hPbeq] at hq
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.1 hq
    exact ⟨y, hy, rfl⟩
  have hPmem : ∀ y ∈ (P : Subgroup ↥A), π y ∈ (Pb : Subgroup (↥A ⧸ N)) := by
    intro y hy
    rw [hPbeq]
    exact Subgroup.mem_map_of_mem _ hy
  have two_pow : ∀ p ∈ (P : Subgroup ↥A), ∃ k : ℕ, (p : X) ^ (2 ^ (k + 1)) = 1 := by
    intro p hp
    obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.1 P.isPGroup') ⟨p, hp⟩
    refine ⟨k, ?_⟩
    have h1 : (⟨p, hp⟩ : ↥(P : Subgroup ↥A)) ^ (2 ^ k) = 1 := by
      rw [← hk]; exact pow_orderOf_eq_one _
    have h2 : (p : X) ^ (2 ^ k) = 1 :=
      congrArg (fun w : ↥(P : Subgroup ↥A) => ((w : ↥A) : X)) h1
    rw [pow_succ, pow_mul, h2, one_pow]
  have key : ∀ p ∈ (P : Subgroup ↥A), π p = ζ → (p : X) = z := by
    intro p hp hpζ
    obtain ⟨k, hpk⟩ := two_pow p hp
    have hmem : p⁻¹ * ⟨z, hzA⟩ ∈ N := by
      rw [← QuotientGroup.eq]
      exact hpζ
    have hmem' : (p : X)⁻¹ * z ∈ oddCoreOf A :=
      mem_oddCoreOf_iff.2 ⟨A.mul_mem (A.inv_mem p.2) hzA, hmem⟩
    have hz2' : z ^ (2 ^ (k + 1)) = 1 := by
      rw [pow_succ, pow_mul', hz2, one_pow]
    exact eq_of_inv_mul_mem_oddCoreOf (comm_z_of_mem_comp hA p.2) hpk hz2' hmem'
  have hzP : z ∈ (P : Subgroup ↥A).map A.subtype := by
    obtain ⟨y, hy, hyζ⟩ := hPb ζ (center_le_sylow hK Pb hζc)
    rw [← key y hy hyζ]
    exact Subgroup.mem_map_of_mem _ hy
  refine ⟨hzP, ?_⟩
  intro x hx hxc
  obtain ⟨p, hp, rfl⟩ := Subgroup.mem_map.1 hx
  have hpc : π p ∈ centralizer ((Pb : Subgroup (↥A ⧸ N)) : Set (↥A ⧸ N)) := by
    rw [Subgroup.mem_centralizer_iff]
    intro q hq
    obtain ⟨y, hy, rfl⟩ := hPb q hq
    have := hxc (y : X) (Subgroup.mem_map_of_mem _ hy)
    have h2 : y * p = p * y := Subtype.ext this.symm
    show π y * π p = π p * π y
    rw [← map_mul, ← map_mul, h2]
  have hpcen : π p ∈ center (↥A ⧸ N) := by
    rw [← sylow_centralizer_self hn8 hK Pb]
    exact ⟨hpc, hPmem p hp⟩
  have hcard : Nat.card (center (↥A ⧸ N)) = 2 := hK.2.1
  have hζ2' : ζ ^ 2 = 1 := by
    rw [hζ, ← map_pow]
    have : (⟨z, hzA⟩ : ↥A) ^ 2 = 1 := Subtype.ext (by simpa using hz2)
    rw [this, map_one]
  have hζ2 : orderOf ζ = 2 := orderOf_eq_prime hζ2' hζ1
  have hzpow : Subgroup.zpowers ζ = center (↥A ⧸ N) := by
    apply Subgroup.eq_of_le_of_card_ge
    · rw [Subgroup.zpowers_le]; exact hζc
    · rw [hcard, Nat.card_zpowers, hζ2]
  have hcases : π p = 1 ∨ π p = ζ := by
    have hmem : π p ∈ Subgroup.zpowers ζ := hzpow ▸ hpcen
    rcases zpowers_eq_of_orderOf_two hζ2 _ hmem with e | e
    · exact Or.inl e
    · exact Or.inr e
  rcases hcases with h1 | h1
  ·
    have hpm : (p : X) ∈ oddCoreOf A :=
      mem_oddCoreOf_iff.2 ⟨p.2, (QuotientGroup.eq_one_iff _).1 h1⟩
    obtain ⟨k, hpk⟩ := two_pow p hp
    have := eq_one_of_mem_oddCoreOf_of_pow hpm hpk
    show (p : X) ∈ zpowers z
    rw [this]; exact one_mem _
  · have := key p hp h1
    show (p : X) ∈ zpowers z
    rw [this]; exact Subgroup.mem_zpowers z

theorem normalizer_sylow_le (h : Sec5Data X n z (zpowers z) S) {A : Subgroup X}
    (hA : Sec5Comp X n (centralizer ({z} : Set X)) A) (P : Sylow 2 ↥A) :
    normalizer (((P : Subgroup ↥A).map A.subtype : Subgroup X) : Set X) ≤
      centralizer ({z} : Set X) := by
  obtain ⟨hzP, hcen⟩ := sylow_center h hA P
  set Q := (P : Subgroup ↥A).map A.subtype with hQ
  intro g hg
  have hz1 : z ≠ 1 := fun e => by
    have := h.orderOf_z
    rw [e, orderOf_one] at this
    omega
  have hgz : g * z * g⁻¹ ∈ Q := (Subgroup.mem_normalizer_iff.1 hg z).1 hzP
  have hzc : ∀ y ∈ Q, z * y = y * z := by
    intro y hy
    obtain ⟨p, hp, rfl⟩ := Subgroup.mem_map.1 hy
    exact (comm_z_of_mem_comp hA p.2).symm
  have hcen' : ∀ y ∈ Q, (g * z * g⁻¹) * y = y * (g * z * g⁻¹) := by
    intro y hy
    have hy' : g⁻¹ * y * g ∈ Q := by
      have := (Subgroup.mem_normalizer_iff.1 (inv_mem hg) y).1 hy
      simpa using this
    have := hzc _ hy'
    calc (g * z * g⁻¹) * y = g * (z * (g⁻¹ * y * g)) * g⁻¹ := by group
      _ = g * ((g⁻¹ * y * g) * z) * g⁻¹ := by rw [this]
      _ = y * (g * z * g⁻¹) := by group
  have hgzz : g * z * g⁻¹ ∈ zpowers z := hcen _ hgz hcen'
  rcases zpowers_eq_of_orderOf_two h.orderOf_z _ hgzz with e | e
  · exfalso
    apply hz1
    have h2 : z = g⁻¹ * (g * z * g⁻¹) * g := by group
    rw [h2, e]; group
  · rw [Subgroup.mem_centralizer_singleton_iff]
    calc g * z = (g * z * g⁻¹) * g := by group
      _ = z * g := by rw [e]

end Sec5Two

end CFSG.OddStandard.Solomon75
