module

public import CFSG.LieType.BorelTits.Basic
public import CFSG.Adapters.ProjectiveSpecialLinear

public section

namespace CFSG.QuasithinUnique.Vol2Native.L239.Lie

open CFSG.Open
open scoped commutatorElement

section Subnormal

variable {G : Type*} [Group G]

theorem isSubnormal_subgroupOf_of_le {P N B : Subgroup G} (hNP : N ≤ P)
    (h : (B.subgroupOf P).IsSubnormal) : (B.subgroupOf N).IsSubnormal := by
  have h1 : ((B.subgroupOf P).subgroupOf (N.subgroupOf P)).IsSubnormal := h.subgroupOf
  let e : ↥(N.subgroupOf P) ≃* ↥N := Subgroup.subgroupOfEquivOfLe hNP
  have h2 := h1.comap e.symm.toMonoidHom
  convert h2 using 1
  ext x
  simp only [Subgroup.mem_subgroupOf, Subgroup.mem_comap]
  rfl

theorem mem_of_odd_orderOf_of_isSubnormal {X : Type*} [Group X] {R : Subgroup X} [R.Normal]
    (hR : IsPGroup 2 R) {K : Subgroup X} (hK : K.IsSubnormal) :
    K ⊔ R = ⊤ → ∀ x : X, ¬ 2 ∣ orderOf x → x ∈ K := by
  induction hK with
  | top => intro _ x _; exact Subgroup.mem_top x
  | step H K' hHK' hK' hN ih =>
    intro hHR x hx
    have hK'R : K' ⊔ R = ⊤ := top_le_iff.mp (hHR ▸ sup_le_sup_right hHK' R)
    have hxK' : x ∈ K' := ih hK'R x hx
    have hxHR : x ∈ H ⊔ R := hHR ▸ Subgroup.mem_top x
    obtain ⟨h, hh, r, hr, hxhr⟩ := Subgroup.mem_sup_of_normal_right.1 hxHR
    have hrK' : r ∈ K' := by
      have : r = h⁻¹ * x := by rw [← hxhr]; group
      rw [this]
      exact K'.mul_mem (K'.inv_mem (hHK' hh)) hxK'
    let x' : K' := ⟨x, hxK'⟩
    let r' : K' := ⟨r, hrK'⟩
    let h' : K' := ⟨h, hHK' hh⟩
    have hxx : x' = h' * r' := Subtype.ext hxhr.symm
    have hh' : h' ∈ H.subgroupOf K' := hh
    have : (H.subgroupOf K').Normal := hN
    let φ := QuotientGroup.mk' (H.subgroupOf K')
    have hφh : φ h' = 1 := (QuotientGroup.eq_one_iff h').2 hh'
    obtain ⟨k, hk⟩ := hR ⟨r, hr⟩
    have hrk : r ^ (2 ^ k) = 1 := by
      have := congrArg Subtype.val hk
      simpa using this
    have hq : φ x' = φ r' := by
      rw [hxx, map_mul, hφh, one_mul]
    have h1 : (φ x') ^ (2 ^ k) = 1 := by
      rw [hq, ← map_pow]
      have : r' ^ (2 ^ k) = 1 := Subtype.ext (by simpa using hrk)
      rw [this, map_one]
    have h2 : (φ x') ^ (orderOf x) = 1 := by
      rw [← map_pow]
      have : x' ^ (orderOf x) = 1 := by
        apply Subtype.ext
        show x ^ orderOf x = 1
        exact pow_orderOf_eq_one x
      rw [this, map_one]
    have hcop : Nat.Coprime (orderOf x) (2 ^ k) := by
      apply Nat.Coprime.pow_right
      exact (Nat.coprime_comm.mp ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).2 hx))
    have h3 := (pow_gcd_eq_one (a := φ x')).mpr ⟨h2, h1⟩
    rw [hcop.gcd_eq_one, pow_one] at h3
    have : x' ∈ H.subgroupOf K' := (QuotientGroup.eq_one_iff x').1 h3
    exact this

theorem le_closure_odd_of_no_two_quotient [Finite G] {B : Subgroup G}
    (h : ∀ (N : Subgroup ↥B) [N.Normal], IsPGroup 2 (↥B ⧸ N) → N = ⊤) :
    B ≤ Subgroup.closure {x : G | x ∈ B ∧ ¬ 2 ∣ orderOf x} := by
  classical
  let S : Set ↥B := {x | ¬ 2 ∣ orderOf x}
  let D : Subgroup ↥B := Subgroup.normalClosure S
  have hD : D = ⊤ := by
    apply h D
    intro y
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective y
    obtain ⟨k, m, hm, hgm⟩ := Nat.exists_eq_two_pow_mul_odd (n := orderOf g) (orderOf_pos g).ne'
    refine ⟨k, ?_⟩
    have hdvd : 2 ^ k ∣ orderOf g := ⟨m, hgm⟩
    have hord : orderOf (g ^ (2 ^ k)) = m := by
      rw [orderOf_pow_of_dvd (by positivity) hdvd, hgm]
      exact Nat.mul_div_cancel_left m (by positivity)
    have hS : g ^ (2 ^ k) ∈ S := by
      show ¬ 2 ∣ orderOf (g ^ (2 ^ k))
      rw [hord]
      exact (Nat.not_even_iff_odd.2 hm) ∘ even_iff_two_dvd.2
    have hDmem : g ^ (2 ^ k) ∈ D := Subgroup.subset_normalClosure hS
    rw [← QuotientGroup.mk_pow]
    exact (QuotientGroup.eq_one_iff _).2 hDmem
  intro b hb
  have hb' : (⟨b, hb⟩ : ↥B) ∈ D := hD ▸ Subgroup.mem_top _
  have hnc : D ≤ (Subgroup.closure {x : G | x ∈ B ∧ ¬ 2 ∣ orderOf x}).comap B.subtype := by
    refine (Subgroup.closure_le _).2 ?_
    intro c hc
    obtain ⟨a, ha, hac⟩ := Set.mem_iUnion₂.1 hc
    obtain ⟨g, hg⟩ := isConj_iff.1 (show IsConj a c from hac)
    have hord : orderOf c = orderOf a := by
      rw [← hg]
      exact orderOf_injective (MulAut.conj g).toMonoidHom (MulAut.conj g).injective a
    apply Subgroup.subset_closure
    refine ⟨c.2, ?_⟩
    show ¬ 2 ∣ orderOf (c : G)
    rw [Subgroup.orderOf_coe, hord]
    exact ha
  exact hnc hb'

theorem normalizes_of_subnormal [Finite G] {P B Q : Subgroup G} (hBP : B ≤ P)
    (hsub : (B.subgroupOf P).IsSubnormal)
    (hB2 : ∀ (N : Subgroup ↥B) [N.Normal], IsPGroup 2 (↥B ⧸ N) → N = ⊤)
    (hQP : Q ≤ P) (hPQ : P ≤ Subgroup.normalizer (Q : Set G)) (hQ : IsPGroup 2 Q) :
    Q ≤ Subgroup.normalizer (B : Set G) := by
  classical
  set R : Subgroup G := ⁅B, Q⁆ with hR
  have hRQ : R ≤ Q := by
    rw [hR, Subgroup.commutator_le]
    intro b hb q hq
    have h1 : b * q * b⁻¹ ∈ Q := (Subgroup.mem_normalizer_iff.1 (hPQ (hBP hb)) q).1 hq
    have : ⁅b, q⁆ = (b * q * b⁻¹) * q⁻¹ := by simp [commutatorElement_def, mul_assoc]
    rw [this]
    exact Q.mul_mem h1 (Q.inv_mem hq)
  have hR2 : IsPGroup 2 R := hQ.to_le hRQ
  have hBnR : B ≤ Subgroup.normalizer (R : Set G) := Subgroup.normalizer_commutator_ge_left B Q
  have hQnR : Q ≤ Subgroup.normalizer (R : Set G) := Subgroup.normalizer_commutator_ge_right B Q
  set N' : Subgroup G := B ⊔ R with hN'
  have hN'nR : N' ≤ Subgroup.normalizer (R : Set G) := sup_le hBnR Subgroup.le_normalizer
  have hN'P : N' ≤ P := sup_le hBP (hRQ.trans hQP)
  have hBN' : B ≤ N' := le_sup_left
  have hRN' : R ≤ N' := le_sup_right
  have hconj : ∀ q ∈ Q, ∀ x ∈ N', q * x * q⁻¹ ∈ N' := by
    intro q hq x hx
    have hx' : x ∈ ((B ⊔ R : Subgroup G) : Set G) := hx
    rw [Subgroup.coe_mul_of_left_le_normalizer_right B R hBnR] at hx'
    obtain ⟨b, hb, r, hr, rfl⟩ := Set.mem_mul.1 hx'
    have h1 : q * r * q⁻¹ ∈ R := (Subgroup.mem_normalizer_iff.1 (hQnR hq) r).1 hr
    have h2 : q * b * q⁻¹ ∈ N' := by
      have hc : ⁅q, b⁆ ∈ R := by
        rw [hR, Subgroup.commutator_comm]
        exact Subgroup.commutator_mem_commutator hq hb
      have : q * b * q⁻¹ = ⁅q, b⁆ * b := by simp [commutatorElement_def, mul_assoc]
      rw [this]
      exact N'.mul_mem (hRN' hc) (hBN' hb)
    have : q * (b * r) * q⁻¹ = (q * b * q⁻¹) * (q * r * q⁻¹) := by group
    rw [this]
    exact N'.mul_mem h2 (hRN' h1)
  have hRnorm : (R.subgroupOf N').Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hRN').2 hN'nR
  have hR2' : IsPGroup 2 (R.subgroupOf N') :=
    hR2.of_equiv (Subgroup.subgroupOfEquivOfLe hRN').symm
  have hBsub : (B.subgroupOf N').IsSubnormal := isSubnormal_subgroupOf_of_le hN'P hsub
  have hsup : B.subgroupOf N' ⊔ R.subgroupOf N' = ⊤ :=
    codisjoint_iff.1 (Subgroup.codisjoint_subgroupOf_sup B R)
  have hodd := mem_of_odd_orderOf_of_isSubnormal hR2' hBsub hsup
  have hfwd : ∀ q ∈ Q, ∀ b ∈ B, q * b * q⁻¹ ∈ B := by
    intro q hq b hb
    have hcl := le_closure_odd_of_no_two_quotient hB2 hb
    refine Subgroup.closure_induction (p := fun x _ => q * x * q⁻¹ ∈ B) ?_ ?_ ?_ ?_ hcl
    · intro x hx
      obtain ⟨hxB, hxodd⟩ := hx
      have hxN' : q * x * q⁻¹ ∈ N' := hconj q hq x (hBN' hxB)
      have hord : orderOf (q * x * q⁻¹) = orderOf x :=
        orderOf_injective (MulAut.conj q).toMonoidHom (MulAut.conj q).injective x
      exact hodd ⟨q * x * q⁻¹, hxN'⟩ (by
        rw [← Subgroup.orderOf_coe]
        show ¬ 2 ∣ orderOf (q * x * q⁻¹)
        rw [hord]; exact hxodd)
    · simp
    · intro x y _ _ ihx ihy
      have : q * (x * y) * q⁻¹ = (q * x * q⁻¹) * (q * y * q⁻¹) := by group
      rw [this]
      exact B.mul_mem ihx ihy
    · intro x _ ihx
      have : q * x⁻¹ * q⁻¹ = (q * x * q⁻¹)⁻¹ := by group
      rw [this]
      exact B.inv_mem ihx
  intro q hq
  rw [Subgroup.mem_normalizer_iff]
  intro b
  refine ⟨hfwd q hq b, fun h => ?_⟩
  have := hfwd q⁻¹ (Q.inv_mem hq) _ h
  simpa [mul_assoc] using this

theorem commutator_le_inf_of_normalizes {B Q : Subgroup G}
    (hB : B ≤ Subgroup.normalizer (Q : Set G)) (hQ : Q ≤ Subgroup.normalizer (B : Set G)) :
    ⁅Q, B⁆ ≤ B ⊓ Q := by
  rw [Subgroup.commutator_le]
  intro q hq b hb
  refine ⟨?_, ?_⟩
  · have h1 : q * b * q⁻¹ ∈ B := (Subgroup.mem_normalizer_iff.1 (hQ hq) b).1 hb
    have : ⁅q, b⁆ = (q * b * q⁻¹) * b⁻¹ := by simp [commutatorElement_def, mul_assoc]
    rw [this]
    exact B.mul_mem h1 (B.inv_mem hb)
  · have h1 : b * q⁻¹ * b⁻¹ ∈ Q := (Subgroup.mem_normalizer_iff.1 (hB hb) q⁻¹).1 (Q.inv_mem hq)
    have : ⁅q, b⁆ = q * (b * q⁻¹ * b⁻¹) := by simp [commutatorElement_def, mul_assoc]
    rw [this]
    exact Q.mul_mem hq h1

theorem inf_le_pCoreOf {P B Q : Subgroup G} (hBP : B ≤ P)
    (hPQ : P ≤ Subgroup.normalizer (Q : Set G)) (hQ : IsPGroup 2 Q) :
    B ⊓ Q ≤ pCoreOf 2 B := by
  refine CFSG.LieType.BorelTits.le_pCoreOf 2 inf_le_left ?_ (hQ.to_le inf_le_right)
  rw [Subgroup.normal_subgroupOf_iff_le_normalizer inf_le_left]
  intro x hx
  exact Subgroup.inf_normalizer_le_normalizer_inf ⟨Subgroup.le_normalizer hx, hPQ (hBP hx)⟩

end Subnormal

end CFSG.QuasithinUnique.Vol2Native.L239.Lie
