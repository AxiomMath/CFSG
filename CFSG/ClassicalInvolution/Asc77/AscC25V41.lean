module

public import CFSG.ClassicalInvolution.Asc77.AscC25V36
public import CFSG.ClassicalInvolution.Asc77.AscC25V40

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Asc77.C25V

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Disconnected.AschTight
open scoped MatrixGroups commutatorElement

section Abstract

variable {G : Type} [Group G]

theorem eq_one_or_eq_of_mem_zpowers_involution {z y : G} (hz : z * z = 1)
    (hy : y ∈ Subgroup.zpowers z) : y = 1 ∨ y = z := by
  obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
  have h2 : z ^ (2 : ℤ) = 1 := by rw [zpow_two]; exact hz
  have hj : j = j % 2 + 2 * (j / 2) := (Int.emod_add_mul_ediv j 2).symm
  have hz' : z ^ j = z ^ (j % 2) := by
    conv_lhs => rw [hj]
    rw [zpow_add, zpow_mul, h2, one_zpow, mul_one]
  rw [hz']
  rcases Int.emod_two_eq_zero_or_one j with h0 | h0
  · left
    rw [h0]
    exact zpow_zero z
  · right
    rw [h0]
    exact zpow_one z

theorem mul_self_eq_one_of_pow_two_pow {x : G} {i f : ℕ} (hx : x ^ 2 ^ i = 1)
    (hf : orderOf x ∣ f) (hf4 : f % 4 = 2) : x * x = 1 := by
  have hd : orderOf x ∣ 2 ^ i := orderOf_dvd_of_pow_eq_one hx
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hd
  have hj1 : j ≤ 1 := by
    by_contra hj2
    have hj3 : 2 ≤ j := by omega
    have h4 : 4 ∣ 2 ^ j := by
      have : 2 ^ 2 ∣ 2 ^ j := pow_dvd_pow 2 hj3
      simpa using this
    have h5 : 4 ∣ f := h4.trans (by rw [← hj]; exact hf)
    omega
  have h2 : orderOf x ∣ 2 := by
    rw [hj]
    calc 2 ^ j ∣ 2 ^ 1 := pow_dvd_pow 2 hj1
      _ = 2 := pow_one 2
  rw [← pow_two]
  exact orderOf_dvd_iff_pow_eq_one.mp h2

theorem pow_eq_self_of_odd_of_mul_self_eq_one {x : G} (hx : x * x = 1) {m : ℕ} (hm : Odd m) :
    x ^ m = x := by
  obtain ⟨k, hk⟩ := hm
  rw [hk, pow_succ, pow_mul, pow_two, hx, one_pow, one_mul]

end Abstract

section TConj

variable {G : Type} [Group G] {t' : G} (ht2 : t' * t' = 1)

include ht2 in
theorem tconj_mul (x y : G) : t' * (x * y) * t' = (t' * x * t') * (t' * y * t') := by
  calc t' * (x * y) * t' = t' * x * (t' * t') * y * t' := by rw [ht2]; group
    _ = (t' * x * t') * (t' * y * t') := by group

include ht2 in
theorem tconj_tconj (x : G) : t' * (t' * x * t') * t' = x := by
  calc t' * (t' * x * t') * t' = (t' * t') * x * (t' * t') := by group
    _ = x := by rw [ht2]; group

include ht2 in
theorem tconj_inv (x : G) : t' * x⁻¹ * t' = (t' * x * t')⁻¹ := by
  apply eq_inv_of_mul_eq_one_right
  calc (t' * x * t') * (t' * x⁻¹ * t') = t' * (x * (t' * t') * x⁻¹) * t' := by group
    _ = t' * (x * 1 * x⁻¹) * t' := by rw [ht2]
    _ = t' * t' := by group
    _ = 1 := ht2

include ht2 in
theorem tconj_pow (x : G) (m : ℕ) : t' * x ^ m * t' = (t' * x * t') ^ m := by
  induction m with
  | zero => simp [ht2]
  | succ m ih => rw [pow_succ, pow_succ, tconj_mul ht2, ih]

include ht2 in
theorem orderOf_tconj (x : G) : orderOf (t' * x * t') = orderOf x := by
  have hti : t'⁻¹ = t' := inv_eq_of_mul_eq_one_right ht2
  have := orderOf_injective (MulAut.conj t').toMonoidHom (MulAut.conj t').injective x
  simpa [MulAut.conj_apply, hti] using this

end TConj

section Galois

variable {p f : ℕ} [Fact p.Prime]

theorem galois_involution_unique (hf : f ≠ 0) {σ τ : GaloisField p f ≃+* GaloisField p f}
    (h1 : σ * σ = 1) (h2 : τ * τ = 1) (hσ : σ ≠ 1) (hτ : τ ≠ 1) : σ = τ := by
  obtain ⟨k₁, hk₁, hσk⟩ := AscL62.eq_frobenius_of_sq_eq_one hf h1 hσ
  obtain ⟨k₂, hk₂, hτk⟩ := AscL62.eq_frobenius_of_sq_eq_one hf h2 hτ
  have hk : k₁ = k₂ := by omega
  subst hk
  ext a
  rw [hσk, hτk]

variable {G : Type} [Group G]

theorem fieldChar_sq_eq_one_of_two_pow (hp : p ≠ 2) (hq : 5 ≤ p ^ f) {K : Subgroup G}
    (e : K ⧸ classicalInvolutionOddCore K ≃* SL(2, GaloisField p f)) {n : G} {i : ℕ}
    (hn2 : orderOf n = 2 ^ i) (hn : n ∈ Subgroup.normalizer (K : Set G)) (hf4 : f % 4 = 2) :
    fieldChar hp hq e ⟨n, hn⟩ * fieldChar hp hq e ⟨n, hn⟩ = 1 := by
  have hcardF : Nat.card (GaloisField p f ≃+* GaloisField p f) = f :=
    (CFSG.LocalAnalysis.ComponentInitial.card_ringAut_and_isCyclic (Fact.out : p.Prime)
      (GaloisField p f) (gf_facts hp hq).2.1).1
  refine mul_self_eq_one_of_pow_two_pow (i := i) ?_ ?_ hf4
  · rw [← map_pow]
    have h1 : n ^ 2 ^ i = 1 := by
      rw [← hn2]
      exact pow_orderOf_eq_one n
    have : (⟨n, hn⟩ : Subgroup.normalizer (K : Set G)) ^ 2 ^ i = 1 :=
      Subtype.ext (by simpa using h1)
    rw [this, map_one]
  · have h1 := orderOf_dvd_natCard (fieldChar hp hq e ⟨n, hn⟩)
    rwa [hcardF] at h1

theorem fieldChar_congr (hp : p ≠ 2) (hq : 5 ≤ p ^ f) {K : Subgroup G}
    (e : K ⧸ classicalInvolutionOddCore K ≃* SL(2, GaloisField p f)) {x y : G} (hxy : x = y)
    (hx : x ∈ Subgroup.normalizer (K : Set G)) (hy : y ∈ Subgroup.normalizer (K : Set G)) :
    fieldChar hp hq e ⟨x, hx⟩ = fieldChar hp hq e ⟨y, hy⟩ := by
  subst hxy
  rfl

end Galois

section Hyp

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G] [IsSimpleGroup G]
  {Ω : Set (Subgroup G)} {K K' W : Subgroup G} {S : Sylow 2 G} {R R' : Subgroup G}
  {z t u₁ u₂ t' : G}


theorem tconj_mem_normalizer (h : T7F2.Hyp25T p f Ω K K' W S R R' z t u₁ u₂ t') {m : G}
    (hmz : m * z = z * m) (hm : m ∈ Subgroup.normalizer (K : Set G)) :
    t' * m * t' ∈ Subgroup.normalizer (K : Set G) := by
  have hmK : conjSub m K = K := mem_normalizer_iff_conjSub_eq.mp hm
  have hmK' : conjSub m K' = K' := (cz_fix_iff h hmz).mp hmK
  have hK2 : conjSub (t' * m * t') K = K := by
    rw [conjSub_mul, conjSub_mul, conjSub_t'_K h, hmK', conjSub_t'_K' h]
  exact mem_normalizer_iff_conjSub_eq.mpr hK2

theorem tconj_comm_z (h : T7F2.Hyp25T p f Ω K K' W S R R' z t u₁ u₂ t') {m : G}
    (hmz : m * z = z * m) : (t' * m * t') * z = z * (t' * m * t') := by
  have ht'z := t'_comm_z h
  calc (t' * m * t') * z = t' * m * (t' * z) := by group
    _ = t' * m * (z * t') := by rw [ht'z]
    _ = t' * (m * z) * t' := by group
    _ = t' * (z * m) * t' := by rw [hmz]
    _ = (t' * z) * m * t' := by group
    _ = (z * t') * m * t' := by rw [ht'z]
    _ = z * (t' * m * t') := by group

theorem K'_le_normalizer (h : T7F2.Hyp25T p f Ω K K' W S R R' z t u₁ u₂ t') :
    K' ≤ Subgroup.normalizer (K : Set G) :=
  h.hΩ.le_normalizer_of_twin h.hK' h.hK h.hs.hne h.hz' h.hz

theorem tconj_mem_K' (h : T7F2.Hyp25T p f Ω K K' W S R R' z t u₁ u₂ t') {x : G} (hx : x ∈ K) :
    t' * x * t' ∈ K' := by
  have := conj_mem_conjSub (n := t') hx
  rwa [conjSub_t'_K h, h.ht'inv] at this

theorem tconj_mem_K (h : T7F2.Hyp25T p f Ω K K' W S R R' z t u₁ u₂ t') {x : G} (hx : x ∈ K') :
    t' * x * t' ∈ K := by
  have := conj_mem_conjSub (n := t') hx
  rwa [conjSub_t'_K' h, h.ht'inv] at this

theorem nuG_eq_one_of_mem_K' (h : T7F2.Hyp25T p f Ω K K' W S R R' z t u₁ u₂ t') (hp : p ≠ 2)
    (hq : 5 ≤ p ^ f) (e : K ⧸ classicalInvolutionOddCore K ≃* SL(2, GaloisField p f)) {x : G}
    (hx : x ∈ K') : nuG hp hq e x = 1 := by
  rw [nuG_eq_one_iff hp hq e (K'_le_normalizer h hx)]
  intro l hl
  have hcomm := h.hΩ.comm_le_oddCore_of_twin h.hK h.hK' h.hs.hne.symm h.hz h.hz'
  have h1 : ⁅l, x⁆ ∈ oddCoreOf K := (hcomm (Subgroup.commutator_mem_commutator hl hx)).1
  rw [← commutatorElement_inv]
  exact Subgroup.inv_mem _ h1

theorem eq_one_or_eq_z_of_nuG_eq_one (h : T7F2.Hyp25T p f Ω K K' W S R R' z t u₁ u₂ t')
    (hC : (S : Subgroup G) ⊓ Subgroup.centralizer ((R ⊔ R' : Subgroup G) : Set G) =
      Subgroup.zpowers z)
    (hp : p ≠ 2) (hq : 5 ≤ p ^ f) (e : K ⧸ classicalInvolutionOddCore K ≃* SL(2, GaloisField p f))
    {x : G} {i : ℕ} (hx2 : orderOf x = 2 ^ i) (hxz : x * z = z * x)
    (hxN : x ∈ Subgroup.normalizer (K : Set G))
    (hxN' : t' * x * t' ∈ Subgroup.normalizer (K : Set G))
    (hν : nuG hp hq e x = 1) (hν' : nuG hp hq e (t' * x * t') = 1) : x = 1 ∨ x = z := by
  classical
  have ht2 := h.ht'2
  have hti : t'⁻¹ = t' := inv_eq_of_mul_eq_one_right ht2
  set C : Subgroup G := Subgroup.centralizer ({z} : Set G) with hCdef
  have hmemC : ∀ g : G, g ∈ C ↔ g * z = z * g := fun g => by
    rw [hCdef, Subgroup.mem_centralizer_singleton_iff]
  have hSC : (S : Subgroup G) ≤ C := fun s hs => (hmemC s).mpr (h.hyp.hzS s hs)
  obtain ⟨c, hcC, hcS⟩ := exists_conj_mem_sylow S hSC ((hmemC x).mpr hxz) hx2
  have hcz : c * z = z * c := (hmemC c).mp hcC
  obtain ⟨x₁, hx₁def⟩ : ∃ x₁ : G, x₁ = c * x * c⁻¹ := ⟨_, rfl⟩
  have hx₁S : x₁ ∈ (S : Subgroup G) := by
    rw [hx₁def]
    exact hcS
  have hx₁ : x₁ ∈ Subgroup.normalizer (K : Set G) ∧
      t' * x₁ * t' ∈ Subgroup.normalizer (K : Set G) ∧ nuG hp hq e x₁ = 1 ∧
      nuG hp hq e (t' * x₁ * t') = 1 := by
    rcases cz_cover h hcz with hc | hc
    · have hcN : c ∈ Subgroup.normalizer (K : Set G) := mem_normalizer_iff_conjSub_eq.mpr hc
      have hcN' : t' * c * t' ∈ Subgroup.normalizer (K : Set G) :=
        tconj_mem_normalizer h hcz hcN
      have hx₁N : x₁ ∈ Subgroup.normalizer (K : Set G) := by
        rw [hx₁def]
        exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hcN hxN) (Subgroup.inv_mem _ hcN)
      have ht : t' * x₁ * t' = (t' * c * t') * (t' * x * t') * (t' * c * t')⁻¹ := by
        rw [hx₁def, tconj_mul ht2 (c * x) c⁻¹, tconj_mul ht2 c x, tconj_inv ht2 c]
      refine ⟨hx₁N, ?_, ?_, ?_⟩
      · rw [ht]
        exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hcN' hxN') (Subgroup.inv_mem _ hcN')
      · rw [hx₁def, nuG_conj hp hq e hcN hxN, hν, mul_one, mul_inv_cancel]
      · rw [ht, nuG_conj hp hq e hcN' hxN', hν', mul_one, mul_inv_cancel]
    · have hc₀N : c * t' ∈ Subgroup.normalizer (K : Set G) :=
        mem_normalizer_iff_conjSub_eq.mpr hc
      have hc₀z : (c * t') * z = z * (c * t') := by
        calc (c * t') * z = c * (t' * z) := by group
          _ = c * (z * t') := by rw [t'_comm_z h]
          _ = (c * z) * t' := by group
          _ = (z * c) * t' := by rw [hcz]
          _ = z * (c * t') := by group
      have hc₁N : t' * c ∈ Subgroup.normalizer (K : Set G) := by
        have h1 := tconj_mem_normalizer h hc₀z hc₀N
        have e1 : t' * (c * t') * t' = t' * c := by
          calc t' * (c * t') * t' = t' * c * (t' * t') := by group
            _ = t' * c := by rw [ht2]; group
        rwa [e1] at h1
      have hxx₁ : x₁ = (c * t') * (t' * x * t') * (c * t')⁻¹ := by
        rw [hx₁def, mul_inv_rev, hti]
        calc c * x * c⁻¹ = c * (t' * t') * x * (t' * t') * c⁻¹ := by rw [ht2]; group
          _ = (c * t') * (t' * x * t') * (t' * c⁻¹) := by group
      have htx₁ : t' * x₁ * t' = (t' * c) * x * (t' * c)⁻¹ := by
        rw [hx₁def, mul_inv_rev, hti]
        group
      refine ⟨?_, ?_, ?_, ?_⟩
      · rw [hxx₁]
        exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hc₀N hxN') (Subgroup.inv_mem _ hc₀N)
      · rw [htx₁]
        exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hc₁N hxN) (Subgroup.inv_mem _ hc₁N)
      · rw [hxx₁, nuG_conj hp hq e hc₀N hxN', hν', mul_one, mul_inv_cancel]
      · rw [htx₁, nuG_conj hp hq e hc₁N hxN, hν, mul_one, mul_inv_cancel]
  obtain ⟨hx₁N, hx₁N', hx₁ν, hx₁ν'⟩ := hx₁
  have hodd := oddCoreOf_odd_natCard K
  have hSpg : ∀ w ∈ (S : Subgroup G), w ∈ oddCoreOf K → w = 1 := fun w hw hwO =>
    eq_one_of_isPGroup_of_mem_odd hodd hwO (S.isPGroup'.to_le (Subgroup.zpowers_le.mpr hw))
  have hcommR : ∀ r ∈ R, x₁ * r = r * x₁ := by
    intro r hr
    have hrK : r ∈ K := h.hyp.hR.2.1 hr
    have hrS : r ∈ (S : Subgroup G) := h.hRS hr
    have h1 : ⁅x₁, r⁆ ∈ oddCoreOf K := (nuG_eq_one_iff hp hq e hx₁N).mp hx₁ν r hrK
    have h2 : ⁅x₁, r⁆ ∈ (S : Subgroup G) := by
      rw [commutatorElement_def]
      exact S.mul_mem (S.mul_mem (S.mul_mem hx₁S hrS) (S.inv_mem hx₁S)) (S.inv_mem hrS)
    exact commutatorElement_eq_one_iff_mul_comm.mp (hSpg _ h2 h1)
  have hcommR' : ∀ r ∈ R', x₁ * r = r * x₁ := by
    intro r hr
    have hrK' : r ∈ K' := h.hyp.hR'.2.1 hr
    have hrS : r ∈ (S : Subgroup G) := h.hR'S hr
    have ht'S := h.ht'S
    have h1 : ⁅t' * x₁ * t', t' * r * t'⁆ ∈ oddCoreOf K :=
      (nuG_eq_one_iff hp hq e hx₁N').mp hx₁ν' _ (tconj_mem_K h hrK')
    have h3 : t' * ⁅x₁, r⁆ * t' = ⁅t' * x₁ * t', t' * r * t'⁆ := by
      rw [commutatorElement_def, commutatorElement_def, tconj_mul ht2, tconj_mul ht2,
        tconj_mul ht2, tconj_inv ht2 x₁, tconj_inv ht2 r]
    have h2 : ⁅x₁, r⁆ ∈ (S : Subgroup G) := by
      rw [commutatorElement_def]
      exact S.mul_mem (S.mul_mem (S.mul_mem hx₁S hrS) (S.inv_mem hx₁S)) (S.inv_mem hrS)
    have h4 : t' * ⁅x₁, r⁆ * t' ∈ (S : Subgroup G) := S.mul_mem (S.mul_mem ht'S h2) ht'S
    have h5 : t' * ⁅x₁, r⁆ * t' = 1 := hSpg _ h4 (by rw [h3]; exact h1)
    have h6 : ⁅x₁, r⁆ = 1 := by
      have := tconj_tconj ht2 ⁅x₁, r⁆
      rw [h5, mul_one, ht2] at this
      exact this.symm
    exact commutatorElement_eq_one_iff_mul_comm.mp h6
  have hx₁C : x₁ ∈ (S : Subgroup G) ⊓ Subgroup.centralizer ((R ⊔ R' : Subgroup G) : Set G) := by
    refine ⟨hx₁S, ?_⟩
    have hle : R ⊔ R' ≤ Subgroup.centralizer ({x₁} : Set G) := by
      refine sup_le (fun r hr => ?_) (fun r hr => ?_)
      · exact Subgroup.mem_centralizer_singleton_iff.mpr (hcommR r hr).symm
      · exact Subgroup.mem_centralizer_singleton_iff.mpr (hcommR' r hr).symm
    exact Subgroup.mem_centralizer_iff.mpr fun g hg =>
      Subgroup.mem_centralizer_singleton_iff.mp (hle hg)
  have hx₁z : x₁ ∈ Subgroup.zpowers z := by
    rw [← hC]
    exact hx₁C
  have h1 := eq_one_or_eq_of_mem_zpowers_involution h.hz.sq hx₁z
  have hcc : c⁻¹ * z * c = z := by
    calc c⁻¹ * z * c = c⁻¹ * (z * c) := by group
      _ = c⁻¹ * (c * z) := by rw [hcz]
      _ = z := by group
  have hxx : x = c⁻¹ * x₁ * c := by
    rw [hx₁def]
    group
  rcases h1 with h1 | h1
  · left
    rw [hxx, h1]
    group
  · right
    rw [hxx, h1, hcc]

theorem exists_hom_swapProd (h : T7F2.Hyp25T p f Ω K K' W S R R' z t u₁ u₂ t') (hp : p ≠ 2)
    (hq : 5 ≤ p ^ f) (e : K ⧸ classicalInvolutionOddCore K ≃* SL(2, GaloisField p f)) :
    ∃ ϕ : ↥(Subgroup.centralizer ({z} : Set G)) →* (GaloisField p f ≃+* GaloisField p f),
      ∀ (n : G) (hnz : n ∈ Subgroup.centralizer ({z} : Set G))
        (hn : n ∈ Subgroup.normalizer (K : Set G))
        (hn' : t' * n * t' ∈ Subgroup.normalizer (K : Set G)),
        ϕ ⟨n, hnz⟩ = fieldChar hp hq e ⟨n, hn⟩ * fieldChar hp hq e ⟨t' * n * t', hn'⟩ := by
  classical
  let _ : CommGroup (GaloisField p f ≃+* GaloisField p f) := ringAutCommGroup _
  set C : Subgroup G := Subgroup.centralizer ({z} : Set G) with hC
  have hmemC : ∀ g : G, g ∈ C ↔ g * z = z * g := fun g => by
    rw [hC, Subgroup.mem_centralizer_singleton_iff]
  have ht'z : t' * z = z * t' := t'_comm_z h
  have ht'C : t' ∈ C := (hmemC t').mpr ht'z
  set N : Subgroup G := C ⊓ Subgroup.normalizer (K : Set G) with hN
  have hconjN : ∀ m ∈ N, t' * m * t' ∈ N := by
    intro m hm
    have hmz : m * z = z * m := (hmemC m).mp hm.1
    exact ⟨C.mul_mem (C.mul_mem ht'C hm.1) ht'C, tconj_mem_normalizer h hmz hm.2⟩
  have hcov : ∀ g ∈ C, g ∈ N ∨ g * t' ∈ N := by
    intro g hg
    have hgz : g * z = z * g := (hmemC g).mp hg
    rcases cz_cover h hgz with h1 | h1
    · exact Or.inl ⟨hg, mem_normalizer_iff_conjSub_eq.mpr h1⟩
    · exact Or.inr ⟨C.mul_mem hg ht'C, mem_normalizer_iff_conjSub_eq.mpr h1⟩
  let χ : N →* (GaloisField p f ≃+* GaloisField p f) :=
    (fieldChar hp hq e).comp (Subgroup.inclusion inf_le_right)
  let ϕ₀ : N →* (GaloisField p f ≃+* GaloisField p f) :=
    MonoidHom.mk' (fun n => χ n * χ ⟨t' * n * t', hconjN n n.2⟩) (by
      intro n m
      have e2 : (⟨t' * ((n * m : N) : G) * t', hconjN _ (n * m).2⟩ : N) =
          ⟨t' * n * t', hconjN n n.2⟩ * ⟨t' * m * t', hconjN m m.2⟩ := by
        apply Subtype.ext
        show t' * ((n : G) * m) * t' = (t' * n * t') * (t' * m * t')
        exact tconj_mul h.ht'2 n m
      rw [map_mul, e2, map_mul]
      exact mul_mul_mul_comm _ _ _ _)
  have hinv : ∀ (n : G) (hn : n ∈ N), ϕ₀ ⟨t' * n * t', hconjN n hn⟩ = ϕ₀ ⟨n, hn⟩ := by
    intro n hn
    have e3 : (⟨t' * (t' * n * t') * t', hconjN _ (hconjN n hn)⟩ : N) = ⟨n, hn⟩ :=
      Subtype.ext (tconj_tconj h.ht'2 n)
    change χ ⟨t' * n * t', hconjN n hn⟩ *
        χ ⟨t' * (t' * n * t') * t', hconjN _ (hconjN n hn)⟩ =
      χ ⟨n, hn⟩ * χ ⟨t' * n * t', hconjN n hn⟩
    rw [e3, mul_comm]
  have hNC : N ≤ C := inf_le_left
  obtain ⟨ϕ, hϕ⟩ := exists_hom_extension_of_index_two C N hNC t' h.ht'2 hcov hconjN ϕ₀ hinv
  refine ⟨ϕ, fun n hnz hn hn' => ?_⟩
  have hnN : n ∈ N := ⟨hnz, hn⟩
  exact (hϕ n hnN).trans rfl

theorem false_of_swap_involution (h : T7F2.Hyp25T p f Ω K K' W S R R' z t u₁ u₂ t') (hp : p ≠ 2)
    (hq : 5 ≤ p ^ f) (e : K ⧸ classicalInvolutionOddCore K ≃* SL(2, GaloisField p f)) {b y : G}
    (hb2 : b * b = 1) (hbz : b * z = z * b) (hbN : b ∈ Subgroup.normalizer (K : Set G))
    (hbN' : t' * b * t' ∈ Subgroup.normalizer (K : Set G)) (hy : y ∈ K') (hy4 : orderOf y = 4)
    (hyb : y * b = b * y)
    (hne : fieldChar hp hq e ⟨b, hbN⟩ * fieldChar hp hq e ⟨t' * b * t', hbN'⟩ ≠ 1) : False := by
  classical
  let _ : CommGroup (GaloisField p f ≃+* GaloisField p f) := ringAutCommGroup _
  obtain ⟨ϕ, hϕ⟩ := exists_hom_swapProd h hp hq e
  have hbC : b ∈ Subgroup.centralizer ({z} : Set G) :=
    Subgroup.mem_centralizer_singleton_iff.mpr hbz
  have hy4' : y ^ 4 = 1 := by
    rw [← hy4]
    exact pow_orderOf_eq_one y
  have hyz : y * z = z * y := (h.hz'.commute_of_mem hy).symm
  have hnc4 : ∀ g : G, (g * z * g⁻¹) * y = y * (g * z * g⁻¹) → g * z * g⁻¹ = z := by
    intro g hg
    have := eq_conj_z_of_commute_order_four h (c := 1) (g := g) (y₀ := y)
      (by rw [conjSub_one]; exact hy) hy4 hg
    simpa using this
  have h1 := hom_centralizer_apply_eq_one (exists_noncomm_of_swap h) hb2 hbz hyb hyz hy4' hnc4 ϕ
  rw [hϕ b hbC hbN hbN'] at h1
  exact hne h1

theorem false_of_pm (h : T7F2.Hyp25T p f Ω K K' W S R R' z t u₁ u₂ t')
    (hC : (S : Subgroup G) ⊓ Subgroup.centralizer ((R ⊔ R' : Subgroup G) : Set G) =
      Subgroup.zpowers z)
    (hp : p ≠ 2) (hq : 5 ≤ p ^ f) (e : K ⧸ classicalInvolutionOddCore K ≃* SL(2, GaloisField p f))
    {n : G} (hnz : n * z = z * n) (hn : n ∈ Subgroup.normalizer (K : Set G))
    (hn' : t' * n * t' ∈ Subgroup.normalizer (K : Set G))
    (hδ : diagChar hp hq e ⟨n, hn⟩ = 1) (hδ' : diagChar hp hq e ⟨t' * n * t', hn'⟩ = 1)
    (hx2 : fieldChar hp hq e ⟨n, hn⟩ * fieldChar hp hq e ⟨n, hn⟩ = 1)
    (hχ' : fieldChar hp hq e ⟨t' * n * t', hn'⟩ = 1) (hχ : fieldChar hp hq e ⟨n, hn⟩ ≠ 1) :
    False := by
  classical
  have ht2 := h.ht'2
  have hz2 : z * z = 1 := h.hz.sq
  obtain ⟨κ₁, hκ₁K, hκ₁⟩ := exists_mem_K_nuG_eq_inr hp hq e hn hδ
  obtain ⟨κ₂, hκ₂K, hκ₂⟩ := exists_mem_K_nuG_eq_inr hp hq e hn' hδ'
  rw [hχ'] at hκ₂
  have hκ₂1 : nuG hp hq e (κ₂⁻¹ * (t' * n * t')) = 1 := by rw [hκ₂, map_one]
  have hκ₁N : κ₁ ∈ Subgroup.normalizer (K : Set G) := Subgroup.le_normalizer hκ₁K
  have hκ₂N : κ₂ ∈ Subgroup.normalizer (K : Set G) := Subgroup.le_normalizer hκ₂K
  have hκ₁'K' : t' * κ₁ * t' ∈ K' := tconj_mem_K' h hκ₁K
  have hκ₂'K' : t' * κ₂ * t' ∈ K' := tconj_mem_K' h hκ₂K
  have hκ₁'N := K'_le_normalizer h hκ₁'K'
  have hκ₂'N := K'_le_normalizer h hκ₂'K'
  have hνA : nuG hp hq e (t' * κ₂ * t') = 1 := nuG_eq_one_of_mem_K' h hp hq e hκ₂'K'
  have hνB : nuG hp hq e (t' * κ₁ * t') = 1 := nuG_eq_one_of_mem_K' h hp hq e hκ₁'K'
  obtain ⟨g, hgdef⟩ : ∃ g : G, g = (t' * κ₂ * t')⁻¹ * (κ₁⁻¹ * n) := ⟨_, rfl⟩
  have hgN : g ∈ Subgroup.normalizer (K : Set G) := by
    rw [hgdef]
    exact Subgroup.mul_mem _ (Subgroup.inv_mem _ hκ₂'N)
      (Subgroup.mul_mem _ (Subgroup.inv_mem _ hκ₁N) hn)
  have hzg : Commute z g := by
    have c1 : Commute z (t' * κ₂ * t')⁻¹ :=
      Commute.inv_right (show Commute z (t' * κ₂ * t') from h.hz'.commute_of_mem hκ₂'K')
    have c2 : Commute z κ₁⁻¹ :=
      Commute.inv_right (show Commute z κ₁ from h.hz.commute_of_mem hκ₁K)
    have c3 : Commute z n := hnz.symm
    rw [hgdef]
    exact c1.mul_right (c2.mul_right c3)
  have hgz : g * z = z * g := hzg.eq.symm
  have e1 : t' * (t' * κ₂ * t')⁻¹ * t' = κ₂⁻¹ := by
    rw [tconj_inv ht2, tconj_tconj ht2]
  have e2 : t' * (κ₁⁻¹ * n) * t' = (t' * κ₁ * t')⁻¹ * (t' * n * t') := by
    rw [tconj_mul ht2, tconj_inv ht2]
  have hgt : t' * g * t' = κ₂⁻¹ * ((t' * κ₁ * t')⁻¹ * (t' * n * t')) := by
    rw [hgdef, tconj_mul ht2, e1, e2]
  have hgtN : t' * g * t' ∈ Subgroup.normalizer (K : Set G) := tconj_mem_normalizer h hgz hgN
  have hνg : nuG hp hq e g = SemidirectProduct.inr (fieldChar hp hq e ⟨n, hn⟩) := by
    rw [hgdef, nuG_mul hp hq e (Subgroup.inv_mem _ hκ₂'N)
      (Subgroup.mul_mem _ (Subgroup.inv_mem _ hκ₁N) hn), nuG_inv hp hq e hκ₂'N, hνA, inv_one,
      one_mul]
    exact hκ₁
  have hνgt : nuG hp hq e (t' * g * t') = 1 := by
    have hB : (t' * κ₁ * t')⁻¹ ∈ Subgroup.normalizer (K : Set G) := Subgroup.inv_mem _ hκ₁'N
    rw [hgt, nuG_mul hp hq e (Subgroup.inv_mem _ hκ₂N) (Subgroup.mul_mem _ hB hn'),
      nuG_mul hp hq e hB hn', nuG_inv hp hq e hκ₁'N, hνB, inv_one, one_mul,
      ← nuG_mul hp hq e (Subgroup.inv_mem _ hκ₂N) hn']
    exact hκ₂1
  have hg0 : orderOf g ≠ 0 := (orderOf_pos g).ne'
  obtain ⟨s, m, hm, hsm⟩ := Nat.exists_eq_two_pow_mul_odd hg0
  obtain ⟨g₂, hg₂def⟩ : ∃ g₂ : G, g₂ = g ^ m := ⟨_, rfl⟩
  have hg₂ord : orderOf g₂ = 2 ^ s := by
    have h1 : m ∣ orderOf g := ⟨2 ^ s, by rw [hsm, mul_comm]⟩
    rw [hg₂def, orderOf_pow_of_dvd hm.pos.ne' h1, hsm, Nat.mul_div_cancel _ hm.pos]
  have hg₂pow : g₂ ^ 2 ^ s = 1 := by
    rw [← hg₂ord]
    exact pow_orderOf_eq_one g₂
  have hg₂N : g₂ ∈ Subgroup.normalizer (K : Set G) := by
    rw [hg₂def]
    exact Subgroup.pow_mem _ hgN m
  have hg₂z : Commute z g₂ := by
    rw [hg₂def]
    exact hzg.pow_right m
  have hg₂tN : t' * g₂ * t' ∈ Subgroup.normalizer (K : Set G) := by
    rw [hg₂def, tconj_pow ht2]
    exact Subgroup.pow_mem _ hgtN m
  have hνg₂ : nuG hp hq e g₂ = SemidirectProduct.inr (fieldChar hp hq e ⟨n, hn⟩) := by
    rw [hg₂def, nuG_pow hp hq e hgN, hνg, ← map_pow, pow_eq_self_of_odd_of_mul_self_eq_one hx2 hm]
  have hνg₂t : nuG hp hq e (t' * g₂ * t') = 1 := by
    rw [hg₂def, tconj_pow ht2, nuG_pow hp hq e hgtN, hνgt, one_pow]
  have hχg₂ : fieldChar hp hq e ⟨g₂, hg₂N⟩ = fieldChar hp hq e ⟨n, hn⟩ := by
    rw [fieldChar_eq_rightHom_nuG hp hq e hg₂N, hνg₂]
    exact SemidirectProduct.rightHom_inr _
  have hχg₂t : fieldChar hp hq e ⟨t' * g₂ * t', hg₂tN⟩ = 1 := by
    rw [fieldChar_eq_rightHom_nuG hp hq e hg₂tN, hνg₂t, map_one]
  have hu2 : ∃ j, orderOf (g₂ * g₂) = 2 ^ j := by
    have h1 : (g₂ * g₂) ^ 2 ^ s = 1 := by
      rw [(Commute.refl g₂).mul_pow, hg₂pow, one_mul]
    obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp (orderOf_dvd_of_pow_eq_one h1)
    exact ⟨j, hj⟩
  obtain ⟨j, hj⟩ := hu2
  have huN : g₂ * g₂ ∈ Subgroup.normalizer (K : Set G) := Subgroup.mul_mem _ hg₂N hg₂N
  have huz : (g₂ * g₂) * z = z * (g₂ * g₂) := (hg₂z.mul_right hg₂z).eq.symm
  have hutN : t' * (g₂ * g₂) * t' ∈ Subgroup.normalizer (K : Set G) := by
    rw [tconj_mul ht2]
    exact Subgroup.mul_mem _ hg₂tN hg₂tN
  have hν1 : nuG hp hq e (g₂ * g₂) = 1 := by
    rw [nuG_mul hp hq e hg₂N hg₂N, hνg₂, ← map_mul, hx2, map_one]
  have hν2 : nuG hp hq e (t' * (g₂ * g₂) * t') = 1 := by
    rw [tconj_mul ht2, nuG_mul hp hq e hg₂tN hg₂tN, hνg₂t, one_mul]
  have hu := eq_one_or_eq_z_of_nuG_eq_one h hC hp hq e hj huz huN hutN hν1 hν2
  have hτg₂pow : (t' * g₂ * t') ^ 2 ^ s = 1 := by
    rw [← tconj_pow ht2, hg₂pow, mul_one, ht2]
  obtain ⟨y₀, hy₀K, hy₀4, hy₀c⟩ := exists_order_four_commute_of_comm_mod_odd (K := K)
    (h := t' * g₂ * t') (u := u₁) hτg₂pow hg₂tN ((nuG_eq_one_iff hp hq e hg₂tN).mp hνg₂t)
    (h.hyp.hR.2.1 h.hyp.hu₁.1) h.hyp.hu₁.2.1
  obtain ⟨y, hydef⟩ : ∃ y : G, y = t' * y₀ * t' := ⟨_, rfl⟩
  have hyK' : y ∈ K' := by
    rw [hydef]
    exact tconj_mem_K' h hy₀K
  have hyN : y ∈ Subgroup.normalizer (K : Set G) := K'_le_normalizer h hyK'
  have hτy : t' * y * t' = y₀ := by
    rw [hydef, tconj_tconj ht2]
  have hy4 : orderOf y = 4 := by
    rw [hydef, orderOf_tconj ht2, hy₀4]
  have hyg : y * g₂ = g₂ * y := by
    have h1 : t' * ((t' * g₂ * t') * y₀) * t' = g₂ * y := by
      rw [tconj_mul ht2 (t' * g₂ * t') y₀, tconj_tconj ht2 g₂, ← hydef]
    have h2 : t' * (y₀ * (t' * g₂ * t')) * t' = y * g₂ := by
      rw [tconj_mul ht2 y₀ (t' * g₂ * t'), tconj_tconj ht2 g₂, ← hydef]
    calc y * g₂ = t' * (y₀ * (t' * g₂ * t')) * t' := h2.symm
      _ = t' * ((t' * g₂ * t') * y₀) * t' := by rw [hy₀c]
      _ = g₂ * y := h1
  have hyz : Commute z y := h.hz'.commute_of_mem hyK'
  have hy2 : y * y = z := by
    have hsq : (y * y) * (y * y) = 1 := by
      have h4 : y ^ 4 = (y * y) * (y * y) := by
        rw [show (4 : ℕ) = 2 + 2 from rfl, pow_add, pow_two]
      have h5 : y ^ 4 = 1 := by
        rw [← hy4]
        exact pow_orderOf_eq_one y
      rw [← h4]
      exact h5
    rcases h.hz'.unique (y * y) (Subgroup.mul_mem _ hyK' hyK') hsq with h1 | h1
    · exfalso
      have h2 : orderOf y ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact h1)
      rw [hy4] at h2
      omega
    · exact h1
  rcases hu with hu1 | huz'
  ·
    refine false_of_swap_involution h hp hq e (b := g₂) hu1 hg₂z.eq.symm hg₂N hg₂tN hyK' hy4
      hyg ?_
    rw [hχg₂, hχg₂t, mul_one]
    exact hχ
  ·
    have hbN : g₂ * y ∈ Subgroup.normalizer (K : Set G) := Subgroup.mul_mem _ hg₂N hyN
    have hb2 : (g₂ * y) * (g₂ * y) = 1 := by
      calc (g₂ * y) * (g₂ * y) = g₂ * (y * g₂) * y := by group
        _ = g₂ * (g₂ * y) * y := by rw [hyg]
        _ = (g₂ * g₂) * (y * y) := by group
        _ = z * z := by rw [huz', hy2]
        _ = 1 := hz2
    have hbz : (g₂ * y) * z = z * (g₂ * y) := (hg₂z.mul_right hyz).eq.symm
    have hτyN : t' * y * t' ∈ Subgroup.normalizer (K : Set G) := by
      rw [hτy]
      exact Subgroup.le_normalizer hy₀K
    have hbtN : t' * (g₂ * y) * t' ∈ Subgroup.normalizer (K : Set G) := by
      rw [tconj_mul ht2]
      exact Subgroup.mul_mem _ hg₂tN hτyN
    have hyb : y * (g₂ * y) = (g₂ * y) * y := by
      calc y * (g₂ * y) = (y * g₂) * y := by group
        _ = (g₂ * y) * y := by rw [hyg]
    refine false_of_swap_involution h hp hq e (b := g₂ * y) hb2 hbz hbN hbtN hyK' hy4 hyb ?_
    have hχy : fieldChar hp hq e ⟨y, hyN⟩ = 1 := by
      rw [fieldChar_eq_rightHom_nuG hp hq e hyN, nuG_eq_one_of_mem_K' h hp hq e hyK', map_one]
    have hχτy : fieldChar hp hq e ⟨t' * y * t', hτyN⟩ = 1 := by
      rw [fieldChar_congr hp hq e hτy hτyN (Subgroup.le_normalizer hy₀K)]
      exact fieldChar_eq_one_of_mem hp hq e hy₀K _
    have hχb : fieldChar hp hq e ⟨g₂ * y, hbN⟩ =
        fieldChar hp hq e ⟨g₂, hg₂N⟩ * fieldChar hp hq e ⟨y, hyN⟩ := by
      have hmulN : (⟨g₂ * y, hbN⟩ : Subgroup.normalizer (K : Set G)) =
          ⟨g₂, hg₂N⟩ * ⟨y, hyN⟩ := rfl
      rw [hmulN, map_mul]
    have hχbt : fieldChar hp hq e ⟨t' * (g₂ * y) * t', hbtN⟩ =
        fieldChar hp hq e ⟨t' * g₂ * t', hg₂tN⟩ * fieldChar hp hq e ⟨t' * y * t', hτyN⟩ := by
      rw [fieldChar_congr hp hq e (tconj_mul ht2 g₂ y) hbtN (Subgroup.mul_mem _ hg₂tN hτyN)]
      have hmulN : (⟨(t' * g₂ * t') * (t' * y * t'), Subgroup.mul_mem _ hg₂tN hτyN⟩ :
          Subgroup.normalizer (K : Set G)) = ⟨t' * g₂ * t', hg₂tN⟩ * ⟨t' * y * t', hτyN⟩ := rfl
      rw [hmulN, map_mul]
    rw [hχb, hχbt, hχy, hχτy, hχg₂, hχg₂t]
    simpa using hχ

end Hyp

section Main

variable {p f : ℕ} [Fact p.Prime]


theorem gcs25z_of_pm (h11 : C25_11 p f) (hf4 : f % 4 = 2) : GCS25Z p f := by
  intro G _ _ _ Ω K K' W S R R' z t u₁ u₂ hyp a haS ha2 hFa hFa' hZ t' h hg hnf hat hp hq e n hnS
    hn hn' hδ hδ'
  by_contra hne
  have hC := h11 G Ω K K' W S R R' z t u₁ u₂ hyp
  have ht2 := h.ht'2
  have hnz : n * z = z * n := hyp.hzS n hnS
  obtain ⟨i, hi⟩ := IsPGroup.iff_orderOf.mp S.isPGroup' (⟨n, hnS⟩ : (S : Subgroup G))
  have hn2 : orderOf n = 2 ^ i := by
    rw [← hi]
    exact Subgroup.orderOf_coe (⟨n, hnS⟩ : (S : Subgroup G))
  have hn2' : orderOf (t' * n * t') = 2 ^ i := by rw [orderOf_tconj ht2, hn2]
  have hx2 : fieldChar hp hq e ⟨n, hn⟩ * fieldChar hp hq e ⟨n, hn⟩ = 1 :=
    fieldChar_sq_eq_one_of_two_pow hp hq e hn2 hn hf4
  have hw2 : fieldChar hp hq e ⟨t' * n * t', hn'⟩ * fieldChar hp hq e ⟨t' * n * t', hn'⟩ = 1 :=
    fieldChar_sq_eq_one_of_two_pow hp hq e hn2' hn' hf4
  by_cases hw : fieldChar hp hq e ⟨t' * n * t', hn'⟩ = 1
  · have hx : fieldChar hp hq e ⟨n, hn⟩ ≠ 1 := fun hx => hne (hw.trans hx.symm)
    exact false_of_pm h hC hp hq e hnz hn hn' hδ hδ' hx2 hw hx
  · by_cases hx : fieldChar hp hq e ⟨n, hn⟩ = 1
    ·
      have hnz' : (t' * n * t') * z = z * (t' * n * t') := tconj_comm_z h hnz
      have e3 : t' * (t' * n * t') * t' = n := tconj_tconj ht2 n
      have hn'' : t' * (t' * n * t') * t' ∈ Subgroup.normalizer (K : Set G) := by
        rw [e3]
        exact hn
      have hsub : (⟨t' * (t' * n * t') * t', hn''⟩ : Subgroup.normalizer (K : Set G)) =
          ⟨n, hn⟩ := Subtype.ext e3
      refine false_of_pm h hC hp hq e hnz' hn' hn'' hδ' ?_ hw2 ?_ hw
      · rw [hsub]
        exact hδ
      · rw [hsub]
        exact hx
    · exact hne (galois_involution_unique (gf_facts hp hq).1 hw2 hx2 hw hx)

end Main

end CFSG.ClassicalInvolution.Asc77.C25V
