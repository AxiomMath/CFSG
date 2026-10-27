module

public import CFSG.LocalAnalysis.GH72.MaxInvariant
import CFSG.LocalAnalysis.ABGTheoremB.IV1
public import CFSG.LocalAnalysis.GH72.Sec4M0

public section

namespace CFSG.GH72

open Subgroup
open scoped Pointwise

namespace G4b

section Basic

variable {G : Type} [Group G] [Finite G]

theorem exists_isMaxInvIn_ge {p : ℕ} {A H R : Subgroup G} (hRH : R ≤ H) (hR : IsPGroup p R)
    (hAR : A ≤ normalizer (R : Set G)) : ∃ P, IsMaxInvIn p A H P ∧ R ≤ P := by
  set 𝓢 : Set (Subgroup G) :=
    {Q | Q ≤ H ∧ IsPGroup p Q ∧ A ≤ normalizer (Q : Set G) ∧ R ≤ Q} with h𝓢
  have hne : 𝓢.Nonempty := ⟨R, hRH, hR, hAR, le_rfl⟩
  obtain ⟨P, ⟨hPH, hPp, hAP, hRP⟩, hmax⟩ :=
    Set.exists_max_image 𝓢 (fun Q : Subgroup G => Nat.card Q) (Set.toFinite _) hne
  refine ⟨P, ⟨hPH, hPp, hAP, fun Q hQH hQp hAQ hPQ => ?_⟩, hRP⟩
  exact (eq_of_le_of_card_ge hPQ (hmax Q ⟨hQH, hQp, hAQ, hRP.trans hPQ⟩)).symm

omit [Finite G] in
theorem exists_isSylowOf_ge {p : ℕ} [Fact p.Prime] {R K : Subgroup G} (hRK : R ≤ K)
    (hR : IsPGroup p R) : ∃ Q, ABGLocalTools.IsSylowOf p Q K ∧ R ≤ Q := by
  obtain ⟨T, hT⟩ := (hR.comap_subtype (K := K)).exists_le_sylow
  exact ⟨(T : Subgroup K).map K.subtype, ⟨T, rfl⟩, fun r hr => ⟨⟨r, hRK hr⟩, hT hr, rfl⟩⟩

theorem exists_map_conj_eq_of_isSylowOf {p : ℕ} [Fact p.Prime] {P P' K : Subgroup G}
    (h : ABGLocalTools.IsSylowOf p P K) (h' : ABGLocalTools.IsSylowOf p P' K) :
    ∃ k ∈ K, P.map (MulAut.conj k).toMonoidHom = P' := by
  obtain ⟨k, hk, hkx⟩ := h.exists_mem_conj h'
  refine ⟨k, hk, ?_⟩
  ext x
  rw [mem_map_conj, hkx]

theorem isSylowOf_of_isMaxInvIn {p : ℕ} (hp : p.Prime) {A H P W : Subgroup G}
    (hA : IsPGroup 2 A) (hP : IsMaxInvIn p A H P) (hPW : P ≤ W) (hWH : W ≤ H)
    (hW : Odd (Nat.card W)) (hAW : A ≤ normalizer (W : Set G)) :
    ABGLocalTools.IsSylowOf p P W := by
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨-, hPp, hAP, hmax⟩ := hP
  have hcop : Nat.Coprime 2 (Nat.card W) := Nat.coprime_two_left.mpr hW
  let _action := SignalizerFunctor.Helpers.conjugationAction A W hAW
  obtain ⟨Q, hPQ, hQ⟩ := SignalizerFunctor.Helpers.invariant_sylow_containing 2 p
    Nat.prime_two hp hA hcop (P.subgroupOf W) hPp.comap_subtype
    (SignalizerFunctor.Helpers.normalized_subgroup_invariant_subgroup A W P hAW hAP)
  set Q' : Subgroup G := (Q : Subgroup W).map W.subtype with hQ'
  have hPQ' : P ≤ Q' := by
    rw [hQ', ← map_subgroupOf_eq_of_le hPW]
    exact map_mono hPQ
  have hAQ' : A ≤ normalizer (Q' : Set G) := by
    apply SignalizerFunctor.Helpers.invariant_subgroup_map_normalized A W hAW
    change ∀ a : A, ∀ x ∈ (Q : Subgroup W), a • x ∈ (Q : Subgroup W)
    intro a x hx
    have hmem := smul_mem_pointwise_smul x a (Q : Subgroup W) hx
    rwa [← Sylow.pointwise_smul_def, hQ a] at hmem
  have hQ'eq : Q' = P :=
    hmax Q' ((map_subtype_le _).trans hWH) (Q.isPGroup'.map W.subtype) hAQ' hPQ'
  exact hQ'eq ▸ ⟨Q, rfl⟩

theorem le_sup_inf_centralizer {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {A L J P : Subgroup G}
    (hA : IsPGroup 2 A) (hAL : A ≤ L) (hJL : J ≤ normalizer (L : Set G)) (hPJ : P ≤ J)
    (hPp : IsPGroup p P) (hAP : A ≤ normalizer (P : Set G)) :
    P ≤ (P ⊓ L) ⊔ (P ⊓ centralizer (A : Set G)) := by
  have hN : Odd (Nat.card ↥(P ⊓ L)) := odd_card_of_isPGroup hp hp2 (hPp.to_le inf_le_left)
  have hAN : A ≤ normalizer ((P ⊓ L : Subgroup G) : Set G) := fun a ha =>
    mem_normalizer_inf (hAP ha) (le_normalizer (hAL ha))
  intro x hx
  have hx' : ∀ a ∈ A, x⁻¹ * (a * x * a⁻¹) ∈ P ⊓ L := by
    intro a ha
    refine mem_inf.2 ⟨mul_mem (inv_mem hx) ((mem_normalizer_iff.1 (hAP ha) x).1 hx), ?_⟩
    have h1 : x⁻¹ * a * x⁻¹⁻¹ ∈ L :=
      (mem_normalizer_iff.1 (hJL (inv_mem (hPJ hx))) a).1 (hAL ha)
    have e : x⁻¹ * (a * x * a⁻¹) = (x⁻¹ * a * x⁻¹⁻¹) * a⁻¹ := by group
    rw [e]
    exact mul_mem h1 (inv_mem (hAL ha))
  obtain ⟨n, hn, hfix⟩ := exists_mul_mem_centralizer hA hN hAN hx'
  have hxn : x * n ∈ P ⊓ centralizer (A : Set G) := by
    refine mem_inf.2 ⟨mul_mem hx (mem_inf.1 hn).1, ?_⟩
    rw [mem_centralizer_iff]
    intro a ha
    calc a * (x * n) = a * (x * n) * a⁻¹ * a := by group
      _ = x * n * a := by rw [hfix a ha]
  have e : x = (x * n) * n⁻¹ := by group
  rw [e, sup_comm]
  exact mul_mem_sup hxn (inv_mem hn)

theorem odd_card_of_forall_odd_orderOf {W : Subgroup G} (h : ∀ w ∈ W, Odd (orderOf w)) :
    Odd (Nat.card W) := by
  rw [Nat.odd_iff, ← Nat.two_dvd_ne_zero]
  intro h2
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨w, hw⟩ := exists_prime_orderOf_dvd_card' (G := W) 2 h2
  have := h w w.2
  rw [Subgroup.orderOf_coe, hw] at this
  exact absurd this (by decide)

theorem odd_card_sup {A N : Subgroup G} (hAN : A ≤ normalizer (N : Set G))
    (hA : Odd (Nat.card A)) (hN : Odd (Nat.card N)) : Odd (Nat.card ↥(A ⊔ N)) := by
  refine odd_card_of_forall_odd_orderOf fun x hx => ?_
  obtain ⟨a, ha, n, hn, rfl⟩ := mem_sup_of_le_normalizer hAN hx
  have key : ∀ j : ℕ, (a * n) ^ j * (a ^ j)⁻¹ ∈ N := by
    intro j
    induction j with
    | zero => simp
    | succ j ih =>
      have e : (a * n) ^ (j + 1) * (a ^ (j + 1))⁻¹ =
          ((a * n) ^ j * (a ^ j)⁻¹) * (a ^ (j + 1) * n * (a ^ (j + 1))⁻¹) := by
        rw [pow_succ, pow_succ]
        group
      rw [e]
      exact mul_mem ih ((mem_normalizer_iff.1 (pow_mem (hAN ha) (j + 1)) n).1 hn)
  have h1 : (a * n) ^ orderOf a ∈ N := by simpa [pow_orderOf_eq_one] using key (orderOf a)
  have h2 : Odd (orderOf a) := Odd.of_dvd_nat hA (Subgroup.orderOf_dvd_natCard A ha)
  have h3 : Odd (orderOf ((a * n) ^ orderOf a)) :=
    Odd.of_dvd_nat hN (Subgroup.orderOf_dvd_natCard N h1)
  have h4 : orderOf (a * n) ∣ orderOf a * orderOf ((a * n) ^ orderOf a) := by
    apply orderOf_dvd_of_pow_eq_one
    rw [pow_mul, pow_orderOf_eq_one]
  exact Odd.of_dvd_nat (h2.mul h3) h4

theorem isSylowOf_sup_of_odd {A N : Subgroup G} (hA : IsPGroup 2 A)
    (hAN : A ≤ normalizer (N : Set G)) (hN : Odd (Nat.card N)) :
    ABGLocalTools.IsSylowOf 2 A (A ⊔ N) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hAN1 : A ⊓ N = ⊥ := eq_bot_iff.2 fun x hx =>
    (mem_bot).2 (eq_one_of_mem_of_mem hA hN (mem_inf.1 hx).1 (mem_inf.1 hx).2)
  have hcard : Nat.card ↥(A ⊔ N) = Nat.card A * Nat.card N := by
    rw [sup_comm]
    rw [CFSG.CGT.Foote81L6.card_sup_of_le_normalizer hAN (by rw [inf_comm]; exact hAN1),
      mul_comm]
  refine isSylowOf_of_forall_card_le le_sup_left hA fun R hR hR2 => ?_
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.1 hR2
  have hdvd : Nat.card R ∣ Nat.card A * Nat.card N := hcard ▸ card_dvd_of_le hR
  have hcop : Nat.Coprime (Nat.card R) (Nat.card N) := by
    rw [hk]
    exact Nat.Coprime.pow_left _ (Nat.coprime_two_left.2 hN)
  exact Nat.le_of_dvd Nat.card_pos (hcop.dvd_of_dvd_mul_right hdvd)

end Basic

section Factors

variable {X : Type} [Group X] [Finite X]

omit [Finite X] in
theorem isMaxInvIn_bot_eq {p : ℕ} {Q : Subgroup X} (hQ : IsMaxInvIn p ⊥ ⊥ Q) : Q = ⊥ :=
  le_bot_iff.1 hQ.1

theorem exists_decomp_of_isMaxInvIn {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {J L₁ L₂ V₁ V₂ : Subgroup X} (hV₁L : V₁ ≤ L₁) (hV₂L : V₂ ≤ L₂) (hL₁J : L₁ ≤ J)
    (hL₂J : L₂ ≤ J) (hJL₁ : J ≤ normalizer (L₁ : Set X)) (hJL₂ : J ≤ normalizer (L₂ : Set X))
    (hLc : L₂ ≤ centralizer (L₁ : Set X)) (hLi : L₁ ⊓ L₂ = ⊥) (hV : IsPGroup 2 ↥(V₁ ⊔ V₂))
    (F9₁ : ∀ Q, IsMaxInvIn p V₁ L₁ Q →
      normalizer (L₁ : Set X) ⊓ centralizer (V₁ : Set X) ≤ normalizer (Q : Set X))
    (F9₂ : ∀ Q, IsMaxInvIn p V₂ L₂ Q →
      normalizer (L₂ : Set X) ⊓ centralizer (V₂ : Set X) ≤ normalizer (Q : Set X))
    {P : Subgroup X} (hP : IsMaxInvIn p (V₁ ⊔ V₂) ⊤ P) (hPJ : P ≤ J) :
    ∃ Q₁ Q₂ Q₀ : Subgroup X, IsMaxInvIn p V₁ L₁ Q₁ ∧ IsMaxInvIn p V₂ L₂ Q₂ ∧
      ABGLocalTools.IsSylowOf p Q₀ (J ⊓ centralizer ((V₁ ⊔ V₂ : Subgroup X) : Set X)) ∧
      (Q₁ ⊔ Q₂) ⊔ Q₀ = P := by
  have : Fact p.Prime := ⟨hp⟩
  set A : Subgroup X := V₁ ⊔ V₂ with hAdef
  obtain ⟨-, hPp, hAP, hmax⟩ := hP
  have hL₁L₂ : L₁ ≤ centralizer (L₂ : Set X) := le_centralizer_iff.1 hLc
  have hJL : J ≤ normalizer ((L₁ ⊔ L₂ : Subgroup X) : Set X) := fun j hj =>
    mem_normalizer_sup (hJL₁ hj) (hJL₂ hj)
  have hAL : A ≤ L₁ ⊔ L₂ := sup_le_sup hV₁L hV₂L
  have hdec := le_sup_inf_centralizer hp hp2 hV hAL hJL hPJ hPp hAP
  set R : Subgroup X := P ⊓ (L₁ ⊔ L₂) with hR
  have hRp : IsPGroup p R := hPp.to_le inf_le_left
  have hAR : A ≤ normalizer (R : Set X) := fun a ha =>
    mem_normalizer_inf (hAP ha) (hJL ((hAL.trans (sup_le hL₁J hL₂J)) ha))
  have hRJ : R ≤ J := inf_le_left.trans hPJ
  have hproj : ∀ {M₁ M₂ : Subgroup X}, M₁ ≤ J → M₂ ≤ J → J ≤ normalizer (M₂ : Set X) →
      M₂ ≤ centralizer (M₁ : Set X) → M₁ ⊓ M₂ = ⊥ → IsPGroup p ↥((R ⊔ M₂) ⊓ M₁) := by
    intro M₁ M₂ hM₁J hM₂J hJM₂ hMc hMi y
    obtain ⟨y, hy⟩ := y
    obtain ⟨hy₁, hy₂⟩ := mem_inf.1 hy
    obtain ⟨r, hr, m, hm, hrm⟩ := mem_sup_of_le_normalizer (hRJ.trans hJM₂) hy₁
    obtain ⟨k, hk⟩ := hRp ⟨r, hr⟩
    have hrk : r ^ p ^ k = 1 := by simpa using congrArg Subtype.val hk
    have hcomm : Commute y m⁻¹ := mem_centralizer_iff.1 (hMc (inv_mem hm)) y hy₂
    have hry : r = y * m⁻¹ := by rw [← hrm]; group
    have h1 : y ^ p ^ k * (m⁻¹) ^ p ^ k = 1 := by rw [← hcomm.mul_pow, ← hry, hrk]
    have h2 : y ^ p ^ k ∈ M₁ ⊓ M₂ := by
      refine mem_inf.2 ⟨pow_mem hy₂ _, ?_⟩
      rw [eq_inv_of_mul_eq_one_left h1]
      exact inv_mem (pow_mem (inv_mem hm) _)
    rw [hMi, mem_bot] at h2
    exact ⟨k, Subtype.ext (by simpa using h2)⟩
  have hR₁p := hproj hL₁J hL₂J hJL₂ hLc hLi
  have hR₂p := hproj hL₂J hL₁J hJL₁ hL₁L₂ (by rw [inf_comm]; exact hLi)
  have hV₁A : V₁ ≤ A := le_sup_left
  have hV₂A : V₂ ≤ A := le_sup_right
  have hV₁R₁ : V₁ ≤ normalizer (((R ⊔ L₂) ⊓ L₁ : Subgroup X) : Set X) := fun v hv =>
    mem_normalizer_inf (mem_normalizer_sup (hAR (hV₁A hv)) (hJL₂ (hL₁J (hV₁L hv))))
      (le_normalizer (hV₁L hv))
  have hV₂R₂ : V₂ ≤ normalizer (((R ⊔ L₁) ⊓ L₂ : Subgroup X) : Set X) := fun v hv =>
    mem_normalizer_inf (mem_normalizer_sup (hAR (hV₂A hv)) (hJL₁ (hL₂J (hV₂L hv))))
      (le_normalizer (hV₂L hv))
  have hRR : R ≤ ((R ⊔ L₂) ⊓ L₁) ⊔ ((R ⊔ L₁) ⊓ L₂) := by
    intro r hr
    obtain ⟨l₁, hl₁, l₂, hl₂, rfl⟩ :=
      mem_sup_of_le_normalizer (hL₁L₂.trans (centralizer_le_normalizer _)) (mem_inf.1 hr).2
    have h1 : l₁ ∈ (R ⊔ L₂) ⊓ L₁ := by
      refine mem_inf.2 ⟨?_, hl₁⟩
      have e : l₁ = (l₁ * l₂) * l₂⁻¹ := by group
      rw [e]
      exact mul_mem (mem_sup_left hr) (mem_sup_right (inv_mem hl₂))
    have h2 : l₂ ∈ (R ⊔ L₁) ⊓ L₂ := by
      refine mem_inf.2 ⟨?_, hl₂⟩
      have e : l₂ = l₁⁻¹ * (l₁ * l₂) := by group
      rw [e]
      exact mul_mem (mem_sup_right (inv_mem hl₁)) (mem_sup_left hr)
    exact mul_mem_sup h1 h2
  obtain ⟨Q₁, hQ₁, hRQ₁⟩ := exists_isMaxInvIn_ge (inf_le_right : (R ⊔ L₂) ⊓ L₁ ≤ L₁) hR₁p hV₁R₁
  obtain ⟨Q₂, hQ₂, hRQ₂⟩ := exists_isMaxInvIn_ge (inf_le_right : (R ⊔ L₁) ⊓ L₂ ≤ L₂) hR₂p hV₂R₂
  have hQ₂Q₁ : Q₂ ≤ centralizer (Q₁ : Set X) :=
    (hQ₂.1.trans hLc).trans (centralizer_le (SetLike.coe_subset_coe.2 hQ₁.1))
  have hQp : IsPGroup p ↥(Q₁ ⊔ Q₂) :=
    hQ₁.2.1.to_sup_of_normal_left' hQ₂.2.1 (hQ₂Q₁.trans (centralizer_le_normalizer _))
  have hCQ : J ⊓ centralizer (A : Set X) ≤ normalizer ((Q₁ ⊔ Q₂ : Subgroup X) : Set X) := by
    intro g hg
    obtain ⟨hgJ, hgA⟩ := mem_inf.1 hg
    exact mem_normalizer_sup
      (F9₁ Q₁ hQ₁ (mem_inf.2 ⟨hJL₁ hgJ, centralizer_le (SetLike.coe_subset_coe.2 hV₁A) hgA⟩))
      (F9₂ Q₂ hQ₂ (mem_inf.2 ⟨hJL₂ hgJ, centralizer_le (SetLike.coe_subset_coe.2 hV₂A) hgA⟩))
  have hAQ : A ≤ normalizer ((Q₁ ⊔ Q₂ : Subgroup X) : Set X) := by
    have hV₁Q₂ : V₁ ≤ centralizer (Q₂ : Set X) :=
      (hV₁L.trans hL₁L₂).trans (centralizer_le (SetLike.coe_subset_coe.2 hQ₂.1))
    have hV₂Q₁ : V₂ ≤ centralizer (Q₁ : Set X) :=
      (hV₂L.trans hLc).trans (centralizer_le (SetLike.coe_subset_coe.2 hQ₁.1))
    refine sup_le (fun v hv => mem_normalizer_sup (hQ₁.2.2.1 hv)
      (centralizer_le_normalizer _ (hV₁Q₂ hv))) (fun v hv => mem_normalizer_sup
      (centralizer_le_normalizer _ (hV₂Q₁ hv)) (hQ₂.2.2.1 hv))
  have hRQ : R ≤ Q₁ ⊔ Q₂ := hRR.trans (sup_le_sup hRQ₁ hRQ₂)
  have hPN : P ≤ normalizer ((Q₁ ⊔ Q₂ : Subgroup X) : Set X) :=
    hdec.trans (sup_le (hRQ.trans le_normalizer)
      (le_inf (inf_le_left.trans hPJ) inf_le_right |>.trans hCQ))
  have hQP : Q₁ ⊔ Q₂ ≤ P := by
    have h := hmax (P ⊔ (Q₁ ⊔ Q₂)) le_top (hPp.to_sup_of_normal_right' hQp hPN)
      (fun a ha => mem_normalizer_sup (hAP ha) (hAQ ha)) le_sup_left
    rw [← h]
    exact le_sup_right
  obtain ⟨Q₀, hQ₀, hPQ₀⟩ := exists_isSylowOf_ge
    (le_inf (inf_le_left.trans hPJ) inf_le_right : P ⊓ centralizer (A : Set X) ≤
      J ⊓ centralizer (A : Set X)) (hPp.to_le inf_le_left)
  refine ⟨Q₁, Q₂, Q₀, hQ₁, hQ₂, hQ₀, ?_⟩
  have hQ₀N : Q₀ ≤ normalizer ((Q₁ ⊔ Q₂ : Subgroup X) : Set X) := hQ₀.le.trans hCQ
  have hAQ₀ : A ≤ normalizer (Q₀ : Set X) :=
    (le_centralizer_iff.1 (hQ₀.le.trans inf_le_right)).trans (centralizer_le_normalizer _)
  have hPle : P ≤ (Q₁ ⊔ Q₂) ⊔ Q₀ := hdec.trans (sup_le_sup hRQ hPQ₀)
  exact hmax _ le_top (hQp.to_sup_of_normal_left' hQ₀.isPGroup hQ₀N)
    (fun a ha => mem_normalizer_sup (hAQ ha) (hAQ₀ ha)) hPle

theorem exists_conj_of_factors {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {J L₁ L₂ V₁ V₂ : Subgroup X} (hV₁L : V₁ ≤ L₁) (hV₂L : V₂ ≤ L₂) (hL₁J : L₁ ≤ J)
    (hL₂J : L₂ ≤ J) (hJL₁ : J ≤ normalizer (L₁ : Set X)) (hJL₂ : J ≤ normalizer (L₂ : Set X))
    (hLc : L₂ ≤ centralizer (L₁ : Set X)) (hLi : L₁ ⊓ L₂ = ⊥) (hV : IsPGroup 2 ↥(V₁ ⊔ V₂))
    (F9₁ : ∀ Q, IsMaxInvIn p V₁ L₁ Q →
      normalizer (L₁ : Set X) ⊓ centralizer (V₁ : Set X) ≤ normalizer (Q : Set X))
    (F9₂ : ∀ Q, IsMaxInvIn p V₂ L₂ Q →
      normalizer (L₂ : Set X) ⊓ centralizer (V₂ : Set X) ≤ normalizer (Q : Set X))
    (F10₁ : ∀ Q Q', IsMaxInvIn p V₁ L₁ Q → IsMaxInvIn p V₁ L₁ Q' →
      ∃ g ∈ L₁ ⊓ normalizer (V₁ : Set X), Q.map (MulAut.conj g).toMonoidHom = Q')
    (F10₂ : ∀ Q Q', IsMaxInvIn p V₂ L₂ Q → IsMaxInvIn p V₂ L₂ Q' →
      ∃ g ∈ L₂ ⊓ normalizer (V₂ : Set X), Q.map (MulAut.conj g).toMonoidHom = Q')
    {P₁ P₂ : Subgroup X} (h₁ : IsMaxInvIn p (V₁ ⊔ V₂) ⊤ P₁) (h₂ : IsMaxInvIn p (V₁ ⊔ V₂) ⊤ P₂)
    (hP₁J : P₁ ≤ J) (hP₂J : P₂ ≤ J) :
    ∃ g ∈ J ⊓ normalizer ((V₁ ⊔ V₂ : Subgroup X) : Set X),
      P₁.map (MulAut.conj g).toMonoidHom = P₂ := by
  have : Fact p.Prime := ⟨hp⟩
  set A : Subgroup X := V₁ ⊔ V₂ with hAdef
  obtain ⟨Q₁, Q₂, Q₀, hQ₁, hQ₂, hQ₀, hP₁⟩ := exists_decomp_of_isMaxInvIn hp hp2 hV₁L hV₂L
    hL₁J hL₂J hJL₁ hJL₂ hLc hLi hV F9₁ F9₂ h₁ hP₁J
  obtain ⟨Q₁', Q₂', Q₀', hQ₁', hQ₂', hQ₀', hP₂⟩ := exists_decomp_of_isMaxInvIn hp hp2 hV₁L hV₂L
    hL₁J hL₂J hJL₁ hJL₂ hLc hLi hV F9₁ F9₂ h₂ hP₂J
  obtain ⟨u₁, hu₁, hu₁Q⟩ := F10₁ Q₁ Q₁' hQ₁ hQ₁'
  obtain ⟨u₂, hu₂, hu₂Q⟩ := F10₂ Q₂ Q₂' hQ₂ hQ₂'
  have hL₁L₂ : L₁ ≤ centralizer (L₂ : Set X) := le_centralizer_iff.1 hLc
  have hu₁A : u₁ ∈ normalizer (A : Set X) := mem_normalizer_sup (mem_inf.1 hu₁).2
    (centralizer_le_normalizer _ (centralizer_le (SetLike.coe_subset_coe.2 hV₂L)
      (hL₁L₂ (mem_inf.1 hu₁).1)))
  have hu₂A : u₂ ∈ normalizer (A : Set X) := mem_normalizer_sup
    (centralizer_le_normalizer _ (centralizer_le (SetLike.coe_subset_coe.2 hV₁L)
      (hLc (mem_inf.1 hu₂).1))) (mem_inf.1 hu₂).2
  set u := u₁ * u₂ with hu
  have huJ : u ∈ J := mul_mem (hL₁J (mem_inf.1 hu₁).1) (hL₂J (mem_inf.1 hu₂).1)
  have huA : u ∈ normalizer (A : Set X) := mul_mem hu₁A hu₂A
  have hcen : ∀ {g : X} {Q : Subgroup X}, g ∈ centralizer (Q : Set X) →
      Q.map (MulAut.conj g).toMonoidHom = Q := fun hg =>
    mem_normalizer_iff_map_conj_eq'.1 (centralizer_le_normalizer _ hg)
  have hQu : (Q₁ ⊔ Q₂).map (MulAut.conj u).toMonoidHom = Q₁' ⊔ Q₂' := by
    rw [hu, ← map_conj_map_conj, Subgroup.map_sup, Subgroup.map_sup,
      hcen (centralizer_le (SetLike.coe_subset_coe.2 hQ₁.1) (hLc (mem_inf.1 hu₂).1)), hu₂Q,
      hu₁Q, hcen (centralizer_le (SetLike.coe_subset_coe.2 hQ₂'.1)
        (hL₁L₂ (mem_inf.1 hu₁).1))]
  have hCu : (J ⊓ centralizer (A : Set X)).map (MulAut.conj u).toMonoidHom =
      J ⊓ centralizer (A : Set X) :=
    mem_normalizer_iff_map_conj_eq'.1 (mem_normalizer_inf (le_normalizer huJ)
      (mem_normalizer_centralizer huA))
  have hQ₀u : ABGLocalTools.IsSylowOf p (Q₀.map (MulAut.conj u).toMonoidHom)
      (J ⊓ centralizer (A : Set X)) := by
    have h := isSylowOf_map_hom hQ₀ (MulAut.conj u).toMonoidHom
    rwa [hCu] at h
  obtain ⟨v, hv, hvQ⟩ := exists_map_conj_eq_of_isSylowOf hQ₀u hQ₀'
  obtain ⟨hvJ, hvA⟩ := mem_inf.1 hv
  have hvQ' : (Q₁' ⊔ Q₂').map (MulAut.conj v).toMonoidHom = Q₁' ⊔ Q₂' := by
    rw [Subgroup.map_sup,
      mem_normalizer_iff_map_conj_eq'.1 (F9₁ Q₁' hQ₁' (mem_inf.2 ⟨hJL₁ hvJ,
        centralizer_le (SetLike.coe_subset_coe.2 (le_sup_left : V₁ ≤ A)) hvA⟩)),
      mem_normalizer_iff_map_conj_eq'.1 (F9₂ Q₂' hQ₂' (mem_inf.2 ⟨hJL₂ hvJ,
        centralizer_le (SetLike.coe_subset_coe.2 (le_sup_right : V₂ ≤ A)) hvA⟩))]
  refine ⟨v * u, mem_inf.2 ⟨mul_mem hvJ huJ, mul_mem (centralizer_le_normalizer _ hvA) huA⟩, ?_⟩
  rw [← map_conj_map_conj, ← hP₁, ← hP₂, Subgroup.map_sup, hQu, Subgroup.map_sup, hvQ', hvQ]

end Factors

section Bar

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem bar_map_conj {C P : Subgroup G} {g : G} (hg : g ∈ C) :
    bar C (P.map (MulAut.conj g).toMonoidHom) =
      (bar C P).map (MulAut.conj (QuotientGroup.mk' (CFSG.oddCore C) ⟨g, hg⟩)).toMonoidHom := by
  ext y
  constructor
  · rintro ⟨⟨x, hxC⟩, hx, rfl⟩
    have hx' : g⁻¹ * x * g ∈ P := mem_map_conj.1 hx
    have hC : g⁻¹ * x * g ∈ C := mul_mem (mul_mem (inv_mem hg) hxC) hg
    refine ⟨QuotientGroup.mk' (CFSG.oddCore C) ⟨g⁻¹ * x * g, hC⟩, ⟨⟨_, hC⟩, hx', rfl⟩, ?_⟩
    rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, ← map_inv, ← map_mul, ← map_mul]
    congr 1
    apply Subtype.ext
    simp only [Subgroup.coe_mul, InvMemClass.coe_inv]
    group
  · rintro ⟨_, ⟨⟨x, hxC⟩, hx, rfl⟩, rfl⟩
    have hC : g * x * g⁻¹ ∈ C := mul_mem (mul_mem hg hxC) (inv_mem hg)
    refine ⟨⟨g * x * g⁻¹, hC⟩, conj_mem_map_conj hx, ?_⟩
    rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, ← map_inv, ← map_mul, ← map_mul]
    rfl

theorem isMaxInvIn_bar {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {C K A P : Subgroup G}
    (hKC : K ≤ C) (hAK : A ≤ K) (hA : IsPGroup 2 A) (hP : IsMaxInvIn p A K P) :
    IsMaxInvIn p (bar C A) (bar C K) (bar C P) := by
  have : Fact p.Prime := ⟨hp⟩
  have hP' := hP
  obtain ⟨hPK, hPp, hAP, -⟩ := hP
  refine ⟨bar_mono hPK, (hPp.comap_subtype (K := C)).map _, bar_le_normalizer_bar hAP,
    fun Q hQK hQp hAQ hPQ => ?_⟩
  set π := QuotientGroup.mk' (CFSG.oddCore C) with hπ
  set Qh : Subgroup G := (Q.comap π).map C.subtype with hQh
  have memQh : ∀ {x : G} (hx : x ∈ C), π ⟨x, hx⟩ ∈ Q → x ∈ Qh := fun hx hq => ⟨⟨_, hx⟩, hq, rfl⟩
  set W : Subgroup G := K ⊓ Qh with hW
  have hPW : P ≤ W := fun x hx =>
    mem_inf.2 ⟨hPK hx, memQh (hKC (hPK hx)) (hPQ (mk_mem_bar (hKC (hPK hx)) hx))⟩
  have hWodd : Odd (Nat.card W) := by
    refine odd_card_of_forall_odd_orderOf fun w hw => ?_
    obtain ⟨hwK, ⟨⟨w', hw'C⟩, hw'Q, hw'⟩⟩ := mem_inf.1 hw
    have hwC : w ∈ C := hKC hwK
    have e : (⟨w', hw'C⟩ : C) = ⟨w, hwC⟩ := Subtype.ext hw'
    rw [e] at hw'Q
    have hq : Odd (orderOf (π ⟨w, hwC⟩)) := Odd.of_dvd_nat (odd_card_of_isPGroup hp hp2 hQp)
      (Subgroup.orderOf_dvd_natCard Q hw'Q)
    set m := orderOf (π ⟨w, hwC⟩)
    have h1 : w ^ m ∈ O C := by
      have h2 : π (⟨w, hwC⟩ ^ m) = 1 := by rw [map_pow, pow_orderOf_eq_one]
      rw [hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h2
      exact ⟨_, h2, by simp⟩
    have h3 : Odd (orderOf (w ^ m)) :=
      Odd.of_dvd_nat (card_O_odd C) (Subgroup.orderOf_dvd_natCard _ h1)
    have h4 : orderOf w ∣ m * orderOf (w ^ m) := by
      apply orderOf_dvd_of_pow_eq_one
      rw [pow_mul, pow_orderOf_eq_one]
    exact Odd.of_dvd_nat (hq.mul h3) h4
  have hAQh : A ≤ normalizer (Qh : Set G) := by
    have key : ∀ a ∈ A, ∀ x ∈ Qh, a * x * a⁻¹ ∈ Qh := by
      intro a ha y hy
      obtain ⟨⟨x, hxC⟩, hxQ, hxy⟩ := hy
      rw [← hxy]
      show a * x * a⁻¹ ∈ Qh
      have haC : a ∈ C := hKC (hAK ha)
      have hC : a * x * a⁻¹ ∈ C := mul_mem (mul_mem haC hxC) (inv_mem haC)
      refine memQh hC ?_
      have h := (mem_normalizer_iff.1 (hAQ (mk_mem_bar haC ha)) (π ⟨x, hxC⟩)).1 hxQ
      have e : π ⟨a * x * a⁻¹, hC⟩ = π ⟨a, haC⟩ * π ⟨x, hxC⟩ * (π ⟨a, haC⟩)⁻¹ := by
        rw [← map_inv, ← map_mul, ← map_mul]
        rfl
      rw [e]
      exact h
    exact fun a ha => mem_normalizer_of_conj_mem (key a ha) (fun x hx => by
      simpa using key a⁻¹ (inv_mem ha) x hx)
  have hAW : A ≤ normalizer (W : Set G) := fun a ha =>
    mem_normalizer_inf (le_normalizer (hAK ha)) (hAQh ha)
  have hPsyl := isSylowOf_of_isMaxInvIn hp hA hP' hPW inf_le_left hWodd hAW
  have hWQ : bar C W = Q := by
    apply le_antisymm
    · rintro _ ⟨⟨w, hwC⟩, hw, rfl⟩
      obtain ⟨-, ⟨⟨w', hw'C⟩, hw'Q, hw'⟩⟩ := mem_inf.1 (show w ∈ W from hw)
      have e : (⟨w', hw'C⟩ : C) = ⟨w, hwC⟩ := Subtype.ext hw'
      rw [e] at hw'Q
      exact hw'Q
    · intro q hq
      obtain ⟨⟨k, hkC⟩, hk, rfl⟩ := hQK hq
      exact ⟨⟨k, hkC⟩, mem_inf.2 ⟨hk, memQh hkC hq⟩, rfl⟩
  have hsyl : ABGLocalTools.IsSylowOf p (bar C P) (bar C W) := by
    have h1 : ABGLocalTools.IsSylowOf p (P.subgroupOf C) (W.subgroupOf C) := by
      rw [← ABGLocalTools.isSylowOf_map_subtype_iff C, subgroupOf_map_subtype,
        subgroupOf_map_subtype, inf_eq_left.2 (hPK.trans hKC),
        inf_eq_left.2 (inf_le_left.trans hKC)]
      exact hPsyl
    exact isSylowOf_map_hom h1 π
  rw [hWQ] at hsyl
  exact hsyl.eq_of_le hPQ le_rfl hQp

theorem exists_conj_of_bar {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {C K A P₁ P₂ : Subgroup G}
    (hKC : K ≤ C) (hAK : A ≤ K) (hA : IsPGroup 2 A) (h₁ : IsMaxInvIn p A K P₁)
    (h₂ : IsMaxInvIn p A K P₂) {y : Bar C}
    (hy : y ∈ bar C K ⊓ normalizer (bar C A : Set (Bar C)))
    (hyP : (bar C P₁).map (MulAut.conj y).toMonoidHom = bar C P₂) :
    ∃ g ∈ K ⊓ normalizer (A : Set G), P₁.map (MulAut.conj g).toMonoidHom = P₂ := by
  have : Fact p.Prime := ⟨hp⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hyK, hyA⟩ := mem_inf.1 hy
  obtain ⟨⟨k, hkC⟩, hk, rfl⟩ := hyK
  have hkK : k ∈ K := hk
  set π := QuotientGroup.mk' (CFSG.oddCore C) with hπ
  set N : Subgroup G := K ⊓ O C with hN
  have hNodd : Odd (Nat.card N) := odd_card_of_le inf_le_right (card_O_odd C)
  have hKN : K ≤ normalizer (N : Set G) := fun x hx =>
    mem_normalizer_inf (le_normalizer hx) (le_normalizer_O C (hKC hx))
  have hAN : A ≤ normalizer (N : Set G) := hAK.trans hKN
  have hAk : A.map (MulAut.conj k).toMonoidHom ≤ A ⊔ N := by
    rintro _ ⟨a, ha, rfl⟩
    have haC : a ∈ C := hKC (hAK ha)
    have hC : k * a * k⁻¹ ∈ C := mul_mem (mul_mem hkC haC) (inv_mem hkC)
    have hmem : π ⟨k * a * k⁻¹, hC⟩ ∈ bar C A := by
      have h := (mem_normalizer_iff.1 hyA (π ⟨a, haC⟩)).1 (mk_mem_bar haC ha)
      have e : π ⟨k * a * k⁻¹, hC⟩ = π ⟨k, hkC⟩ * π ⟨a, haC⟩ * (π ⟨k, hkC⟩)⁻¹ := by
        rw [← map_inv, ← map_mul, ← map_mul]
        rfl
      rw [e]
      exact h
    obtain ⟨⟨a', ha'C⟩, ha', he⟩ := hmem
    have hO := inv_mul_mem_O_of_mk_eq he
    have hNmem : a'⁻¹ * (k * a * k⁻¹) ∈ N :=
      mem_inf.2 ⟨mul_mem (inv_mem (hAK ha')) (mul_mem (mul_mem hkK (hAK ha)) (inv_mem hkK)), hO⟩
    have e : (MulAut.conj k).toMonoidHom a = a' * (a'⁻¹ * (k * a * k⁻¹)) := by
      rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      group
    rw [e]
    exact mul_mem_sup ha' hNmem
  have hNk : N.map (MulAut.conj k).toMonoidHom = N :=
    mem_normalizer_iff_map_conj_eq'.1 (hKN hkK)
  have hANk : (A ⊔ N).map (MulAut.conj k).toMonoidHom = A ⊔ N := by
    refine eq_of_le_of_card_ge ?_ ?_
    · rw [Subgroup.map_sup, hNk]
      exact sup_le hAk le_sup_right
    · rw [card_map_of_injective (MulAut.conj k).injective]
  have hAsyl := isSylowOf_sup_of_odd hA hAN hNodd
  have hAksyl : ABGLocalTools.IsSylowOf 2 (A.map (MulAut.conj k).toMonoidHom) (A ⊔ N) := by
    have h := isSylowOf_map_hom hAsyl (MulAut.conj k).toMonoidHom
    rwa [hANk] at h
  obtain ⟨c, hc, hcA⟩ := exists_map_conj_eq_of_isSylowOf hAsyl hAksyl
  have hcK : c ∈ K := (sup_le hAK inf_le_left) hc
  set k' := c⁻¹ * k with hk'
  have hk'K : k' ∈ K := mul_mem (inv_mem hcK) hkK
  have hk'A : k' ∈ normalizer (A : Set G) := by
    rw [mem_normalizer_iff_map_conj_eq', hk', ← map_conj_map_conj, ← hcA, map_conj_map_conj,
      inv_mul_cancel, map_conj_one]
  obtain ⟨a, ha, n, hn, rfl⟩ := mem_sup_of_le_normalizer hAN hc
  have hP₁' : bar C (P₁.map (MulAut.conj k').toMonoidHom) = bar C P₂ := by
    have hk'C : k' ∈ C := hKC hk'K
    have haC : a ∈ C := hKC (hAK ha)
    have hnC : n ∈ C := hKC (mem_inf.1 hn).1
    have he : π ⟨k', hk'C⟩ = (π ⟨a, haC⟩)⁻¹ * π ⟨k, hkC⟩ := by
      have hn1 : π ⟨n, hnC⟩ = 1 := by
        rw [hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
        exact (mem_oddCore_iff _).2 (mem_inf.1 hn).2
      have e : (⟨k', hk'C⟩ : C) = (⟨n, hnC⟩)⁻¹ * (⟨a, haC⟩)⁻¹ * ⟨k, hkC⟩ := by
        apply Subtype.ext
        simp only [hk', Subgroup.coe_mul, InvMemClass.coe_inv]
        group
      rw [e, map_mul, map_mul, map_inv, map_inv, hn1, inv_one, one_mul]
    rw [bar_map_conj hk'C, he, ← map_conj_map_conj, hyP]
    exact mem_normalizer_iff_map_conj_eq'.1
      (inv_mem (bar_le_normalizer_bar h₂.2.2.1 (mk_mem_bar haC ha)))
  set P₁' := P₁.map (MulAut.conj k').toMonoidHom with hP₁'def
  have hP₁'max : IsMaxInvIn p A K P₁' := by
    have h := IsMaxInvIn.map h₁ (MulAut.conj k')
    rwa [mem_normalizer_iff_map_conj_eq'.1 hk'A,
      mem_normalizer_iff_map_conj_eq'.1 (le_normalizer hk'K)] at h
  have hP₁'W : P₁' ≤ P₂ ⊔ N := by
    intro x hx
    have hxK : x ∈ K := hP₁'max.1 hx
    have hxC : x ∈ C := hKC hxK
    have hmem : π ⟨x, hxC⟩ ∈ bar C P₂ := hP₁' ▸ mk_mem_bar hxC hx
    obtain ⟨⟨x₂, hx₂C⟩, hx₂, he⟩ := hmem
    have hx₂' : x₂ ∈ P₂ := hx₂
    have hO := inv_mul_mem_O_of_mk_eq he
    have hNmem : x₂⁻¹ * x ∈ N := mem_inf.2 ⟨mul_mem (inv_mem (h₂.1 hx₂')) hxK, hO⟩
    have e : x = x₂ * (x₂⁻¹ * x) := by group
    rw [e]
    exact mul_mem_sup hx₂' hNmem
  have hWK : P₂ ⊔ N ≤ K := sup_le h₂.1 inf_le_left
  have hWodd : Odd (Nat.card ↥(P₂ ⊔ N)) :=
    odd_card_sup (h₂.1.trans hKN) (odd_card_of_isPGroup hp hp2 h₂.2.1) hNodd
  have hAW : A ≤ normalizer ((P₂ ⊔ N : Subgroup G) : Set G) := fun a ha =>
    mem_normalizer_sup (h₂.2.2.1 ha) (hAN ha)
  have hs₁ := isSylowOf_of_isMaxInvIn hp hA hP₁'max hP₁'W hWK hWodd hAW
  have hs₂ := isSylowOf_of_isMaxInvIn hp hA h₂ le_sup_left hWK hWodd hAW
  obtain ⟨c', hc', hc'P⟩ := ABGTheoremB.exists_conj_eq_of_isSylowOf_normalized_of_coprime
    Nat.prime_two hp hA hAW (Nat.two_dvd_ne_zero.2 (Nat.odd_iff.1 hWodd)) hs₁ hs₂
    hP₁'max.2.2.1 h₂.2.2.1
  obtain ⟨hc'W, hc'A⟩ := mem_inf.1 hc'
  refine ⟨c' * k', mem_inf.2 ⟨mul_mem (hWK hc'W) hk'K,
    mul_mem (centralizer_le_normalizer _ hc'A) hk'A⟩, ?_⟩
  rw [← map_conj_map_conj, ← hP₁'def, hc'P]

end Bar

end G4b

end CFSG.GH72
