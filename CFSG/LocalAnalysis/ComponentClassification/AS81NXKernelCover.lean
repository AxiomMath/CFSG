module

public import CFSG.LocalAnalysis.ComponentClassification.AS81Step13Basic
public import CFSG.Quasithin.Background.A3ComponentsBasic
public import CFSG.RankThree.PerfectCover.HopfCentralCoversSetup
public import CFSG.Alternating.Multipliers.Small

public section

namespace CFSG.ComponentClassification.AS81.NXKernel

open Subgroup CFSG.Quasithin
open scoped commutatorElement

variable {G : Type} [Group G]

section Coprime

variable [Finite G]

theorem mem_of_mul_mem {S T O : Subgroup G} (hT : IsPGroup 2 T) (hO : Odd (Nat.card O)) {t o : G}
    (ht : t ∈ T) (ho : o ∈ O) (hc : t * o = o * t) (hS : t * o ∈ S) : t ∈ S ∧ o ∈ S := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨n, hn⟩ := hT.exists_card_eq
  have ht1 : t ^ 2 ^ n = 1 := by
    have h := pow_card_eq_one' (G := T) (x := ⟨t, ht⟩)
    rw [hn] at h
    simpa using congrArg Subtype.val h
  have h1 : (t * o) ^ 2 ^ n = o ^ 2 ^ n := by
    rw [(Commute.mul_pow hc (2 ^ n)), ht1, one_mul]
  have hodd : Odd (orderOf o) := hO.of_dvd_nat (Subgroup.orderOf_dvd_natCard O ho)
  have hcop : Nat.Coprime (2 ^ n) (orderOf o) :=
    Nat.Coprime.pow_left n (Nat.coprime_two_left.mpr hodd)
  obtain ⟨m, hm⟩ := exists_pow_eq_self_of_coprime hcop
  have hoS : o ∈ S := by
    rw [← hm, ← h1]
    exact pow_mem (pow_mem hS _) _
  refine ⟨?_, hoS⟩
  have h2 := S.mul_mem hS (S.inv_mem hoS)
  rwa [mul_inv_cancel_right] at h2

omit [Finite G] in
theorem eq_one_of_pow_two_pow {O : Subgroup G} (hO : Odd (Nat.card O)) {o : G} (ho : o ∈ O)
    {k : ℕ} (hk : o ^ 2 ^ k = 1) : o = 1 := by
  have hodd : Odd (orderOf o) := hO.of_dvd_nat (Subgroup.orderOf_dvd_natCard O ho)
  have h3 : orderOf o ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one hk
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp h3
  rcases j with _ | j
  · rw [pow_zero] at hj
    exact orderOf_eq_one_iff.mp hj
  · rw [hj] at hodd
    exact absurd (Nat.even_pow.mpr ⟨even_two, Nat.succ_ne_zero j⟩) (Nat.not_even_iff_odd.mpr hodd)

omit [Finite G] in
theorem inf_eq_bot_of_two_odd {T O : Subgroup G} (hT : IsPGroup 2 T) (hO : Odd (Nat.card O)) :
    T ⊓ O = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  obtain ⟨k, hk⟩ := hT ⟨x, hx.1⟩
  exact (mem_bot).mpr (eq_one_of_pow_two_pow hO hx.2 (by simpa using congrArg Subtype.val hk))

omit [Finite G] in
theorem eq_one_of_mul_pow {W O : Subgroup G} (hinf : W ⊓ O = ⊥) (hO : Odd (Nat.card O)) {w o : G}
    (hw : w ∈ W) (ho : o ∈ O) (hc : Commute w o) {k : ℕ} (hk : (w * o) ^ 2 ^ k = 1) : o = 1 := by
  rw [hc.mul_pow] at hk
  have h1 : o ^ 2 ^ k = (w ^ 2 ^ k)⁻¹ := eq_inv_of_mul_eq_one_right hk
  have h2 : o ^ 2 ^ k ∈ W ⊓ O := by
    refine ⟨?_, O.pow_mem ho _⟩
    rw [h1]
    exact W.inv_mem (W.pow_mem hw _)
  rw [hinf, mem_bot] at h2
  exact eq_one_of_pow_two_pow hO ho h2

end Coprime

theorem exists_mul_of_mem_sup {T O : Subgroup G} (hTO : T ≤ centralizer (O : Set G)) {x : G}
    (hx : x ∈ T ⊔ O) : ∃ t ∈ T, ∃ o ∈ O, x = t * o ∧ t * o = o * t := by
  have hN : T ≤ normalizer (O : Set G) := hTO.trans (Subgroup.centralizer_le_normalizer _)
  have hx' : x ∈ ((T ⊔ O : Subgroup G) : Set G) := hx
  rw [coe_mul_of_left_le_normalizer_right T O hN] at hx'
  obtain ⟨t, ht, o, ho, rfl⟩ := hx'
  exact ⟨t, ht, o, ho, rfl, (mem_centralizer_iff.mp (hTO ht) o ho).symm⟩

theorem le_normalizer_sup {N A B : Subgroup G} (hA : N ≤ normalizer (A : Set G))
    (hB : N ≤ normalizer (B : Set G)) : N ≤ normalizer ((A ⊔ B : Subgroup G) : Set G) := by
  intro n hn
  rw [mem_normalizer_iff_map_conj_eq, Subgroup.map_sup, mem_normalizer_iff_map_conj_eq.mp (hA hn),
    mem_normalizer_iff_map_conj_eq.mp (hB hn)]

section Coprime'

variable [Finite G]

theorem inf_sup_eq_sup_inf {S T O : Subgroup G} (hT : IsPGroup 2 T) (hO : Odd (Nat.card O))
    (hTO : T ≤ centralizer (O : Set G)) : S ⊓ (T ⊔ O) = (S ⊓ T) ⊔ (S ⊓ O) := by
  refine le_antisymm (fun x hx => ?_)
    (sup_le (inf_le_inf_left _ le_sup_left) (inf_le_inf_left _ le_sup_right))
  obtain ⟨t, ht, o, ho, rfl, hc⟩ := exists_mul_of_mem_sup hTO hx.2
  obtain ⟨htS, hoS⟩ := mem_of_mul_mem hT hO ht ho hc hx.1
  exact mul_mem (mem_sup_left ⟨htS, ht⟩) (mem_sup_right ⟨hoS, ho⟩)

theorem sup_inf_eq_bot {P T O : Subgroup G} (hT : IsPGroup 2 T) (hO : Odd (Nat.card O))
    (hTO : T ≤ centralizer (O : Set G)) (hPT : P ≤ normalizer (T : Set G)) (hPO : P ⊓ O = ⊥) :
    (P ⊔ T) ⊓ O = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  have hx' : x ∈ ((P ⊔ T : Subgroup G) : Set G) := hx.1
  rw [coe_mul_of_left_le_normalizer_right P T hPT] at hx'
  obtain ⟨p, hp, t, ht, hpt⟩ := hx'
  have hc : t⁻¹ * x = x * t⁻¹ := (mem_centralizer_iff.mp (hTO (T.inv_mem ht)) x hx.2).symm
  have hp' : t⁻¹ * x ∈ P := by
    have e : p = x * t⁻¹ := by rw [← hpt, mul_inv_cancel_right]
    rw [hc, ← e]
    exact hp
  obtain ⟨-, hxP⟩ := mem_of_mul_mem hT hO (T.inv_mem ht) hx.2 hc hp'
  have h := mem_inf.mpr ⟨hxP, hx.2⟩
  rwa [hPO] at h

omit [Finite G] in
theorem oUpper_le_of_forall_mul {H W O : Subgroup G} (hWO : W ≤ centralizer (O : Set G))
    (hinf : W ⊓ O = ⊥) (hO : Odd (Nat.card O)) (hH : ∀ h ∈ H, ∃ w ∈ W, ∃ o ∈ O, h = w * o) :
    AS76b.oUpperTwoPrime H ≤ W := by
  refine (closure_le W).mpr ?_
  rintro x ⟨hxH, k, hk⟩
  obtain ⟨w, hw, o, ho, rfl⟩ := hH x hxH
  have hc : Commute w o := (mem_centralizer_iff.mp (hWO hw) o ho).symm
  rw [eq_one_of_mul_pow hinf hO hw ho hc hk, mul_one]
  exact hw

end Coprime'

theorem commutator_sup_le {K C : Subgroup G} (hKC : K ≤ normalizer (C : Set G)) :
    ⁅K ⊔ C, K ⊔ C⁆ ≤ ⁅K, K⁆ ⊔ C := by
  have hconj : ∀ k ∈ K, ∀ c ∈ C, k * c * k⁻¹ ∈ C := fun k hk c hc =>
    (mem_normalizer_iff.mp (hKC hk) c).mp hc
  rw [commutator_le]
  intro a ha b hb
  have ha' : a ∈ ((K ⊔ C : Subgroup G) : Set G) := ha
  have hb' : b ∈ ((K ⊔ C : Subgroup G) : Set G) := hb
  rw [coe_mul_of_left_le_normalizer_right K C hKC] at ha' hb'
  obtain ⟨k₁, hk₁, c₁, hc₁, rfl⟩ := ha'
  obtain ⟨k₂, hk₂, c₂, hc₂, rfl⟩ := hb'
  have e : ⁅k₁ * c₁, k₂ * c₂⁆ = ⁅k₁, k₂⁆ * ((k₂ * k₁ * k₂⁻¹) * c₁ * (k₂ * k₁ * k₂⁻¹)⁻¹) *
      ((k₂ * k₁) * (c₂ * c₁⁻¹) * (k₂ * k₁)⁻¹) * (k₂ * c₂⁻¹ * k₂⁻¹) := by
    simp only [commutatorElement_def]
    group
  rw [e]
  refine mul_mem (mul_mem (mul_mem (mem_sup_left (commutator_mem_commutator hk₁ hk₂)) ?_) ?_) ?_
  · exact mem_sup_right (hconj _ (K.mul_mem (K.mul_mem hk₂ hk₁) (K.inv_mem hk₂)) _ hc₁)
  · exact mem_sup_right (hconj _ (K.mul_mem hk₂ hk₁) _ (C.mul_mem hc₂ (C.inv_mem hc₁)))
  · exact mem_sup_right (hconj _ hk₂ _ (C.inv_mem hc₂))

theorem derivedSeriesOf_sup_eq {D C L : Subgroup G} (hDC : D ⊔ C = L) (hperf : ⁅L, L⁆ ⊔ C = L)
    (hLC : L ≤ normalizer (C : Set G)) (n : ℕ) : derivedSeriesOf D n ⊔ C = L := by
  induction n with
  | zero => exact hDC
  | succ n ih =>
    rw [derivedSeriesOf_succ]
    refine le_antisymm (sup_le ((A3.commutator_self_le _).trans (le_sup_left.trans ih.le))
      (le_sup_right.trans ih.le)) ?_
    have hle : derivedSeriesOf D n ≤ normalizer (C : Set G) := (le_sup_left.trans ih.le).trans hLC
    calc L = ⁅L, L⁆ ⊔ C := hperf.symm
      _ = ⁅derivedSeriesOf D n ⊔ C, derivedSeriesOf D n ⊔ C⁆ ⊔ C := by rw [ih]
      _ ≤ (⁅derivedSeriesOf D n, derivedSeriesOf D n⁆ ⊔ C) ⊔ C :=
          sup_le_sup_right (commutator_sup_le hle) _
      _ = ⁅derivedSeriesOf D n, derivedSeriesOf D n⁆ ⊔ C := by rw [sup_assoc, sup_idem]

theorem perfectCore_sup_eq [Finite G] {D C L : Subgroup G} (hDC : D ⊔ C = L)
    (hperf : ⁅L, L⁆ ⊔ C = L) (hLC : L ≤ normalizer (C : Set G)) : perfectCore D ⊔ C = L := by
  obtain ⟨n, hn⟩ := exists_perfectCore_eq D
  rw [hn n le_rfl]
  exact derivedSeriesOf_sup_eq hDC hperf hLC n

theorem mem_center_of_perfect {Q : Type*} [Group Q] [Group.IsPerfect Q] {x : Q}
    (h : ∀ a : Q, a * x * a⁻¹ * x⁻¹ ∈ center Q) : x ∈ center Q := by
  let φ : Q →* ↥(center Q) := MonoidHom.mk' (fun a => ⟨a * x * a⁻¹ * x⁻¹, h a⟩) fun a b => by
    apply Subtype.ext
    have hb := mem_center_iff.mp (h b)
    change a * b * x * (a * b)⁻¹ * x⁻¹ = (a * x * a⁻¹ * x⁻¹) * (b * x * b⁻¹ * x⁻¹)
    calc a * b * x * (a * b)⁻¹ * x⁻¹ = a * (b * x * b⁻¹ * x⁻¹) * x * a⁻¹ * x⁻¹ := by group
      _ = (b * x * b⁻¹ * x⁻¹) * a * x * a⁻¹ * x⁻¹ := by rw [hb a]
      _ = (b * x * b⁻¹ * x⁻¹) * (a * x * a⁻¹ * x⁻¹) := by group
      _ = (a * x * a⁻¹ * x⁻¹) * (b * x * b⁻¹ * x⁻¹) := (hb _).symm
  have hker : commutator Q ≤ φ.ker := Abelianization.commutator_subset_ker φ
  rw [Group.IsPerfect.commutator_eq_top] at hker
  rw [mem_center_iff]
  intro a
  have h1 : φ a = 1 := hker (mem_top a)
  have h2 : a * x * a⁻¹ * x⁻¹ = 1 := congrArg Subtype.val h1
  calc a * x = a * x * a⁻¹ * x⁻¹ * (x * a) := by group
    _ = x * a := by rw [h2, one_mul]

theorem card_ker_dvd_six {E : Type} [Group E] [Group.IsPerfect E]
    (q : E →* alternatingGroup (Fin 6)) (hq : Function.Surjective q) (hker : q.ker ≤ center E) :
    Nat.card q.ker ∣ 6 := by
  have h := Subgroup.card_dvd_of_surjective
    (CFSG.RankThree.PerfectCover.hopfMultiplierToKer_surjective q hq hker)
  rwa [CFSG.Alternating.Multipliers.hopfMultiplier_alternatingGroup_six.2] at h

theorem card_eq_card_mul_card_map {Q : Type*} [Group Q] (M : Subgroup Q) [M.Normal]
    {H : Subgroup Q} (hMH : M ≤ H) :
    Nat.card H = Nat.card M * Nat.card (H.map (QuotientGroup.mk' M)) := by
  let f : ↥H →* Q ⧸ M := (QuotientGroup.mk' M).comp H.subtype
  have h1 := Subgroup.card_ker_mul_card_range f
  have hker : f.ker = M.subgroupOf H := by
    ext x
    rw [MonoidHom.mem_ker, mem_subgroupOf]
    exact QuotientGroup.eq_one_iff (x : Q)
  have hrange : f.range = H.map (QuotientGroup.mk' M) := by
    rw [MonoidHom.range_comp, range_subtype]
  rw [hker, hrange, Nat.card_congr (subgroupOfEquivOfLe hMH).toEquiv] at h1
  exact h1.symm

theorem card_subgroupOf (H K : Subgroup G) :
    Nat.card (H.subgroupOf K) = Nat.card (H ⊓ K : Subgroup G) := by
  rw [← subgroupOf_map_subtype, card_map_of_injective K.subtype_injective]

theorem le_normalizer_of_conj_mem {N M : Subgroup G} (h : ∀ n ∈ N, ∀ m ∈ M, n * m * n⁻¹ ∈ M) :
    N ≤ normalizer (M : Set G) := by
  intro n hn
  rw [mem_normalizer_iff]
  intro m
  refine ⟨h n hn m, fun hm => ?_⟩
  have := h n⁻¹ (N.inv_mem hn) _ hm
  rwa [show n⁻¹ * (n * m * n⁻¹) * n⁻¹⁻¹ = m by group] at this

theorem conj_mem_centralizer_of_mem_normalizer {O : Subgroup G} {n x : G}
    (hn : n ∈ normalizer (O : Set G)) (hx : x ∈ centralizer (O : Set G)) :
    n * x * n⁻¹ ∈ centralizer (O : Set G) := by
  rw [mem_centralizer_iff] at hx ⊢
  intro o ho
  have ho' : n⁻¹ * o * n ∈ O := by
    have := (mem_normalizer_iff.mp (inv_mem hn) o).mp ho
    rwa [inv_inv] at this
  have h := hx _ ho'
  calc o * (n * x * n⁻¹) = n * ((n⁻¹ * o * n) * x) * n⁻¹ := by group
    _ = n * (x * (n⁻¹ * o * n)) * n⁻¹ := by rw [h]
    _ = n * x * n⁻¹ * o := by group

section Schur

variable [Finite G]

theorem inf_eq_bot_of_perfect
    {N T O K L P : Subgroup G} {Ω : Type} [Fintype Ω] [DecidableEq Ω] (hΩ : Nat.card Ω = 6)
    (ρ : ↥N →* Equiv.Perm Ω) (hT2 : IsPGroup 2 T) (hOodd : Odd (Nat.card O))
    (hNT : N ≤ normalizer (T : Set G)) (hNO : N ≤ normalizer (O : Set G))
    (hTO : T ≤ centralizer (O : Set G))
    (hK : ∀ n : ↥N, ρ n = 1 ↔ (n : G) ∈ K) (hKN : K ≤ N) (hCK : T ⊔ O ≤ K)
    (hK3 : (T ⊔ O).relIndex K = 3)
    (hL : ∀ n : ↥N, (n : G) ∈ L ↔ ρ n ∈ alternatingGroup Ω) (hLN : L ≤ N)
    (halt : alternatingGroup Ω ≤ ρ.range)
    (hcent : ∀ n ∈ L, ∀ κ ∈ K, n * κ * n⁻¹ * κ⁻¹ ∈ T ⊔ O)
    (hPperf : ⁅P, P⁆ = P) (hPL : P ≤ L) (hPO : P ≤ centralizer (O : Set G))
    (hPC : P ⊔ (T ⊔ O) = L) : P ⊓ O = ⊥ := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set C := T ⊔ O with hC
  have hPN : P ≤ N := hPL.trans hLN
  have hNC : N ≤ normalizer (C : Set G) := le_normalizer_sup hNT hNO
  have hPCn : P ≤ normalizer (C : Set G) := hPN.trans hNC
  have hLmul : ∀ x ∈ L, ∃ p ∈ P, ∃ c ∈ C, x = p * c := by
    intro x hx
    have hx' : x ∈ ((P ⊔ C : Subgroup G) : Set G) := by
      rw [hPC]
      exact hx
    rw [coe_mul_of_left_le_normalizer_right P C hPCn] at hx'
    obtain ⟨p, hp, c, hc, rfl⟩ := hx'
    exact ⟨p, hp, c, hc, rfl⟩
  have hρC : ∀ c (hc : c ∈ C), ρ ⟨c, hKN (hCK hc)⟩ = 1 := fun c hc => (hK _).mpr (hCK hc)
  have hTn : (T.subgroupOf P).Normal := normal_subgroupOf_of_le_normalizer (hPN.trans hNT)
  have hPperf' : Group.IsPerfect ↥P := Subgroup.isPerfect_iff.mpr hPperf
  let ρA : ↥P →* alternatingGroup Ω :=
    (ρ.comp (inclusion hPN)).codRestrict (alternatingGroup Ω) fun p =>
      (hL (inclusion hPN p)).mp (hPL p.2)
  have hρA : ∀ p : ↥P, ((ρA p : alternatingGroup Ω) : Equiv.Perm Ω) = ρ (inclusion hPN p) :=
    fun p => rfl
  have hTker : T.subgroupOf P ≤ ρA.ker := by
    intro t ht
    rw [MonoidHom.mem_ker]
    apply Subtype.ext
    rw [hρA]
    exact (hK _).mpr (hCK (mem_sup_left (mem_subgroupOf.mp ht)))
  let e : Ω ≃ Fin 6 := Fintype.equivFinOfCardEq (by rw [← Nat.card_eq_fintype_card, hΩ])
  let q : ↥P ⧸ T.subgroupOf P →* alternatingGroup (Fin 6) :=
    (Equiv.altCongrHom e).toMonoidHom.comp (QuotientGroup.lift (T.subgroupOf P) ρA hTker)
  have hq : ∀ p : ↥P, q (p : ↥P ⧸ T.subgroupOf P) = Equiv.altCongrHom e (ρA p) := fun p => rfl
  have hqK : ∀ p : ↥P, q (p : ↥P ⧸ T.subgroupOf P) = 1 ↔ (p : G) ∈ K := by
    intro p
    rw [hq, MulEquiv.map_eq_one_iff, ← OneMemClass.coe_eq_one, hρA]
    exact hK _
  have hqs : Function.Surjective q := by
    intro σ
    set σ' := (Equiv.altCongrHom e).symm σ with hσ'
    obtain ⟨n, hn⟩ := halt σ'.2
    have hnL : (n : G) ∈ L := (hL n).mpr (by rw [hn]; exact σ'.2)
    obtain ⟨p, hp, c, hc, hpc⟩ := hLmul _ hnL
    refine ⟨((⟨p, hp⟩ : ↥P) : ↥P ⧸ T.subgroupOf P), ?_⟩
    rw [hq]
    have h1 : ρA ⟨p, hp⟩ = σ' := by
      apply Subtype.ext
      rw [hρA]
      have e1 : n = inclusion hPN ⟨p, hp⟩ * ⟨c, hKN (hCK hc)⟩ := Subtype.ext hpc
      rw [← hn, e1, map_mul, hρC c hc, mul_one]
    rw [h1, hσ', MulEquiv.apply_symm_apply]
  have hcen : q.ker ≤ center (↥P ⧸ T.subgroupOf P) := by
    intro x hx
    obtain ⟨p, rfl⟩ := QuotientGroup.mk_surjective x
    have hpK : (p : G) ∈ K := (hqK p).mp hx
    refine mem_center_of_perfect fun a => ?_
    obtain ⟨p₁, rfl⟩ := QuotientGroup.mk_surjective a
    have hy : ((p₁ * p * p₁⁻¹ * p⁻¹ : ↥P) : G) ∈ C := hcent _ (hPL p₁.2) _ hpK
    obtain ⟨t, ht, o, ho, hto, hc⟩ := exists_mul_of_mem_sup hTO hy
    have hmem := mem_of_mul_mem hT2 hOodd ht ho hc
      (by rw [← hto]; exact (p₁ * p * p₁⁻¹ * p⁻¹).2)
    have hc' : t⁻¹ * o = o * t⁻¹ := (show Commute t o from hc).inv_left.eq
    have e1 : ((p₁ * p * p₁⁻¹ * p⁻¹ : ↥P) : ↥P ⧸ T.subgroupOf P) =
        ((⟨o, hmem.2⟩ : ↥P) : ↥P ⧸ T.subgroupOf P) := by
      rw [QuotientGroup.eq, mem_subgroupOf]
      change ((p₁ * p * p₁⁻¹ * p⁻¹ : ↥P) : G)⁻¹ * o ∈ T
      rw [hto]
      have e2 : (t * o)⁻¹ * o = t⁻¹ := by
        calc (t * o)⁻¹ * o = o⁻¹ * (t⁻¹ * o) := by group
          _ = o⁻¹ * (o * t⁻¹) := by rw [hc']
          _ = t⁻¹ := by group
      rw [e2]
      exact T.inv_mem ht
    rw [← QuotientGroup.mk_inv, ← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul,
      ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, e1, mem_center_iff]
    intro b
    obtain ⟨p₂, rfl⟩ := QuotientGroup.mk_surjective b
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
    congr 1
    apply Subtype.ext
    exact (mem_centralizer_iff.mp (hPO p₂.2) o ho).symm
  have hkerq : q.ker = (K.subgroupOf P).map (QuotientGroup.mk' (T.subgroupOf P)) := by
    ext x
    obtain ⟨p, rfl⟩ := QuotientGroup.mk'_surjective (T.subgroupOf P) x
    constructor
    · intro hx
      exact ⟨p, mem_subgroupOf.mpr ((hqK p).mp hx), rfl⟩
    · rintro ⟨p', hp', hpp'⟩
      rw [← hpp', MonoidHom.mem_ker, QuotientGroup.mk'_apply]
      exact (hqK p').mpr (mem_subgroupOf.mp hp')
  have hTK : T.subgroupOf P ≤ K.subgroupOf P := fun t ht =>
    mem_subgroupOf.mpr (hCK (mem_sup_left (mem_subgroupOf.mp ht)))
  have h1 := card_eq_card_mul_card_map (T.subgroupOf P) hTK
  rw [← hkerq, card_subgroupOf, card_subgroupOf] at h1
  have hKL : K ≤ L := fun k hk => (hL ⟨k, hKN hk⟩).mpr (by rw [(hK _).mpr hk]; exact one_mem _)
  have hKsup : C ⊔ (K ⊓ P) = K := by
    refine le_antisymm (sup_le hCK inf_le_left) fun k hk => ?_
    obtain ⟨p, hp, c, hc, rfl⟩ := hLmul k (hKL hk)
    have hpK : p ∈ K := by
      have := K.mul_mem hk (K.inv_mem (hCK hc))
      rwa [mul_inv_cancel_right] at this
    rw [sup_comm]
    exact mul_mem (mem_sup_left ⟨hpK, hp⟩) (mem_sup_right hc)
  have h2 := card_sup_mul_card_inf (H := C) (R := K ⊓ P) (inf_le_right.trans hPCn)
  rw [hKsup, show C ⊓ (K ⊓ P) = C ⊓ P by rw [← inf_assoc, inf_eq_left.mpr hCK]] at h2
  have h3 := Subgroup.relIndex_mul_card (H := C) (K := K)
  rw [inf_eq_left.mpr hCK, hK3] at h3
  have hCP : C ⊓ P = (T ⊓ P) ⊔ (O ⊓ P) := by
    rw [inf_comm, hC, inf_sup_eq_sup_inf hT2 hOodd hTO, inf_comm P T, inf_comm P O]
  have hON : O ⊓ P ≤ normalizer ((T ⊓ P : Subgroup G) : Set G) := fun o ho =>
    Subgroup.centralizer_le_normalizer _ (mem_centralizer_iff.mpr fun x hx =>
      (mem_centralizer_iff.mp (hTO hx.1) o ho.1).symm)
  have h4 := card_sup_mul_card_inf (H := T ⊓ P) (R := O ⊓ P) hON
  have hTOP : (T ⊓ P) ⊓ (O ⊓ P) = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    have h := mem_inf.mpr ⟨hx.1.1, hx.2.1⟩
    rwa [inf_eq_bot_of_two_odd hT2 hOodd] at h
  rw [← hCP, hTOP, card_bot, mul_one] at h4
  have hCpos : 0 < Nat.card C := Nat.card_pos
  have hTPpos : 0 < Nat.card (T ⊓ P : Subgroup G) := Nat.card_pos
  have h5 : Nat.card (K ⊓ P : Subgroup G) = 3 * Nat.card (C ⊓ P : Subgroup G) := by
    have h6 : Nat.card C * Nat.card (K ⊓ P : Subgroup G) =
        Nat.card C * (3 * Nat.card (C ⊓ P : Subgroup G)) := by
      rw [← h2, ← h3]
      ring
    exact Nat.eq_of_mul_eq_mul_left hCpos h6
  have h6 : Nat.card q.ker = 3 * Nat.card (O ⊓ P : Subgroup G) := by
    have h7 : Nat.card (T ⊓ P : Subgroup G) * Nat.card q.ker =
        Nat.card (T ⊓ P : Subgroup G) * (3 * Nat.card (O ⊓ P : Subgroup G)) := by
      rw [← h1, h5, h4]
      ring
    exact Nat.eq_of_mul_eq_mul_left hTPpos h7
  have hdvd := card_ker_dvd_six q hqs hcen
  rw [h6] at hdvd
  have h7 : Nat.card (O ⊓ P : Subgroup G) ∣ 2 :=
    Nat.dvd_of_mul_dvd_mul_left (by norm_num : 0 < 3) (by simpa using hdvd)
  have h8 : Odd (Nat.card (O ⊓ P : Subgroup G)) := hOodd.of_dvd_nat (card_dvd_of_le inf_le_left)
  have h9 : Nat.card (O ⊓ P : Subgroup G) = 1 := by
    rcases (Nat.dvd_prime Nat.prime_two).mp h7 with h | h
    · exact h
    · rw [h] at h8
      exact absurd h8 (by decide)
  rw [inf_comm]
  exact Subgroup.card_eq_one.mp h9

end Schur

theorem oUpper_inf_eq_bot [Finite G]
    {N T O K L : Subgroup G} {Ω : Type} [Fintype Ω] [DecidableEq Ω] (hΩ : Nat.card Ω = 6)
    (ρ : ↥N →* Equiv.Perm Ω) (hT2 : IsPGroup 2 T) (hOodd : Odd (Nat.card O))
    (hNT : N ≤ normalizer (T : Set G)) (hNO : N ≤ normalizer (O : Set G))
    (hTO : T ≤ centralizer (O : Set G))
    (hK : ∀ n : ↥N, ρ n = 1 ↔ (n : G) ∈ K) (hKN : K ≤ N) (hCK : T ⊔ O ≤ K)
    (hK3 : (T ⊔ O).relIndex K = 3)
    (hL : ∀ n : ↥N, (n : G) ∈ L ↔ ρ n ∈ alternatingGroup Ω) (hLN : L ≤ N)
    (halt : alternatingGroup Ω ≤ ρ.range) (hperf : ⁅L, L⁆ ⊔ (T ⊔ O) = L)
    (hcent : ∀ n ∈ L, ∀ κ ∈ K, n * κ * n⁻¹ * κ⁻¹ ∈ T ⊔ O)
    (hLD : L ≤ (N ⊓ centralizer (O : Set G)) ⊔ (T ⊔ O))
    {d : G} (hdN : d ∈ N) (hdO : d ∈ centralizer (O : Set G))
    (hd : Equiv.Perm.sign (ρ ⟨d, hdN⟩) = -1) :
    AS76b.oUpperTwoPrime N ⊓ O = ⊥ := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set C := T ⊔ O with hC
  set D := N ⊓ centralizer (O : Set G) with hD
  have hNC : N ≤ normalizer (C : Set G) := le_normalizer_sup hNT hNO
  have hCL : C ≤ L := le_sup_right.trans hperf.le
  have hDconj : ∀ n ∈ N, ∀ x ∈ D, n * x * n⁻¹ ∈ D := fun n hn x hx =>
    ⟨N.mul_mem (N.mul_mem hn hx.1) (N.inv_mem hn),
      conj_mem_centralizer_of_mem_normalizer (hNO hn) hx.2⟩
  have hLconj : ∀ n ∈ N, ∀ x ∈ L, n * x * n⁻¹ ∈ L := by
    intro n hn x hx
    have hxN := hLN hx
    refine (hL ⟨_, N.mul_mem (N.mul_mem hn hxN) (N.inv_mem hn)⟩).mpr ?_
    have e1 : (⟨n * x * n⁻¹, N.mul_mem (N.mul_mem hn hxN) (N.inv_mem hn)⟩ : ↥N) =
        ⟨n, hn⟩ * ⟨x, hxN⟩ * ⟨n, hn⟩⁻¹ := rfl
    rw [e1, map_mul, map_mul, map_inv]
    exact (alternatingGroup.normal (α := Ω)).conj_mem _ ((hL ⟨x, hxN⟩).mp hx) _
  have hD₀n : N ≤ normalizer ((D ⊓ L : Subgroup G) : Set G) := le_normalizer_of_conj_mem
    fun n hn x hx => ⟨hDconj n hn x hx.1, hLconj n hn x hx.2⟩
  have hD₀C : (D ⊓ L) ⊔ C = L := by
    refine le_antisymm (sup_le inf_le_right hCL) fun l hl => ?_
    have hl' : l ∈ ((D ⊔ C : Subgroup G) : Set G) := hLD hl
    rw [coe_mul_of_left_le_normalizer_right D C (inf_le_left.trans hNC)] at hl'
    obtain ⟨x, hx, c, hc, rfl⟩ := hl'
    have hxL : x ∈ L := by
      have := L.mul_mem hl (L.inv_mem (hCL hc))
      rwa [mul_inv_cancel_right] at this
    exact mul_mem (mem_sup_left ⟨hx, hxL⟩) (mem_sup_right hc)
  set P := perfectCore (D ⊓ L) with hP
  have hPC : P ⊔ C = L := perfectCore_sup_eq hD₀C hperf (hLN.trans hNC)
  have hPperf : ⁅P, P⁆ = P := perfectCore_perfect _
  have hPD₀ : P ≤ D ⊓ L := perfectCore_le _
  have hPL : P ≤ L := hPD₀.trans inf_le_right
  have hPO : P ≤ centralizer (O : Set G) := hPD₀.trans (inf_le_left.trans inf_le_right)
  have hPN : P ≤ N := hPL.trans hLN
  have hNP : N ≤ normalizer (P : Set G) := hD₀n.trans (normalizer_le_normalizer_perfectCore _)
  have hPOb : P ⊓ O = ⊥ := inf_eq_bot_of_perfect hΩ ρ hT2 hOodd hNT hNO hTO hK hKN hCK hK3 hL
    hLN halt hcent hPperf hPL hPO hPC
  have hPTO : (P ⊔ T) ⊓ O = ⊥ := sup_inf_eq_bot hT2 hOodd hTO (hPN.trans hNT) hPOb
  have hPTc : P ⊔ T ≤ centralizer (O : Set G) := sup_le hPO hTO
  have hPTL : P ⊔ T ≤ L := sup_le hPL (le_sup_left.trans hCL)
  have hPTnN : N ≤ normalizer ((P ⊔ T : Subgroup G) : Set G) := le_normalizer_sup hNP hNT
  have hLmul : ∀ x ∈ L, ∃ y ∈ P ⊔ T, ∃ o ∈ O, x = y * o := by
    intro x hx
    have hx' : x ∈ (((P ⊔ T) ⊔ O : Subgroup G) : Set G) := by
      rw [sup_assoc, ← hC, hPC]
      exact hx
    rw [coe_mul_of_left_le_normalizer_right (P ⊔ T) O
      (hPTc.trans (Subgroup.centralizer_le_normalizer _))] at hx'
    obtain ⟨y, hy, o, ho, rfl⟩ := hx'
    exact ⟨y, hy, o, ho, rfl⟩
  obtain ⟨a, m, hm, hord⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos d).ne'
  have hd₂N : d ^ m ∈ N := pow_mem hdN m
  have hd₂O : d ^ m ∈ centralizer (O : Set G) := pow_mem hdO m
  have hd₂2 : (d ^ m) ^ 2 ^ a = 1 := by
    rw [← pow_mul, mul_comm, ← hord, pow_orderOf_eq_one]
  have hd₂odd : Equiv.Perm.sign (ρ ⟨d ^ m, hd₂N⟩) = -1 := by
    have e1 : (⟨d ^ m, hd₂N⟩ : ↥N) = ⟨d, hdN⟩ ^ m := rfl
    rw [e1, map_pow, map_pow, hd, hm.neg_one_pow]
  have hd₂sq : (d ^ m) ^ 2 ∈ P ⊔ T := by
    have hsq : (d ^ m) ^ 2 ∈ L := by
      refine (hL ⟨(d ^ m) ^ 2, pow_mem hd₂N 2⟩).mpr (Equiv.Perm.mem_alternatingGroup.mpr ?_)
      have e1 : (⟨(d ^ m) ^ 2, pow_mem hd₂N 2⟩ : ↥N) = ⟨d ^ m, hd₂N⟩ ^ 2 := rfl
      rw [e1, map_pow, map_pow, hd₂odd, neg_one_sq]
    obtain ⟨y, hy, o, ho, hyo⟩ := hLmul _ hsq
    have hc : Commute y o := (mem_centralizer_iff.mp (hPTc hy) o ho).symm
    have ho1 : o = 1 := eq_one_of_mul_pow hPTO hOodd hy ho hc (k := a) (by
      rw [← hyo, ← pow_mul, mul_comm, pow_mul, hd₂2, one_pow])
    rw [hyo, ho1, mul_one]
    exact hy
  set W := (P ⊔ T) ⊔ zpowers (d ^ m) with hW
  have hWc : W ≤ centralizer (O : Set G) := sup_le hPTc (zpowers_le.mpr hd₂O)
  have hdn : zpowers (d ^ m) ≤ normalizer ((P ⊔ T : Subgroup G) : Set G) :=
    zpowers_le.mpr (hPTnN hd₂N)
  have hWmul : ∀ w ∈ W, ∃ y ∈ P ⊔ T, ∃ k : ℤ, w = y * (d ^ m) ^ k := by
    intro w hw
    have hw' : w ∈ (((P ⊔ T) ⊔ zpowers (d ^ m) : Subgroup G) : Set G) := hw
    rw [coe_mul_of_right_le_normalizer_left (P ⊔ T) (zpowers (d ^ m)) hdn] at hw'
    obtain ⟨y, hy, z, ⟨k, rfl⟩, rfl⟩ := hw'
    exact ⟨y, hy, k, rfl⟩
  have hWO : W ⊓ O = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    obtain ⟨y, hy, k, rfl⟩ := hWmul x hx.1
    have hxK : y * (d ^ m) ^ k ∈ K := hCK (mem_sup_right hx.2)
    have hyL := hPTL hy
    have hsign : Equiv.Perm.sign (ρ ⟨y * (d ^ m) ^ k, hKN hxK⟩) = 1 := by
      rw [(hK _).mpr hxK, map_one]
    have hy1 : Equiv.Perm.sign (ρ ⟨y, hLN hyL⟩) = 1 :=
      Equiv.Perm.mem_alternatingGroup.mp ((hL _).mp hyL)
    have e1 : (⟨y * (d ^ m) ^ k, hKN hxK⟩ : ↥N) = ⟨y, hLN hyL⟩ * ⟨d ^ m, hd₂N⟩ ^ k := rfl
    rw [e1, map_mul, map_mul, hy1, one_mul, map_zpow, map_zpow, hd₂odd] at hsign
    rcases Int.even_or_odd k with ⟨j, rfl⟩ | hk
    · have hdk : (d ^ m) ^ (j + j) ∈ P ⊔ T := by
        rw [← two_mul, zpow_mul]
        exact zpow_mem (by exact_mod_cast hd₂sq) j
      have hmem : y * (d ^ m) ^ (j + j) ∈ (P ⊔ T) ⊓ O := ⟨mul_mem hy hdk, hx.2⟩
      rwa [hPTO, mem_bot] at hmem
    · rw [hk.neg_one_zpow] at hsign
      have h := congrArg Units.val hsign
      norm_num at h
  have hNmul : ∀ n ∈ N, ∃ w ∈ W, ∃ o ∈ O, n = w * o := by
    intro n hn
    rcases Int.units_eq_one_or (Equiv.Perm.sign (ρ ⟨n, hn⟩)) with h | h
    · obtain ⟨y, hy, o, ho, rfl⟩ :=
        hLmul n ((hL ⟨n, hn⟩).mpr (Equiv.Perm.mem_alternatingGroup.mpr h))
      exact ⟨y, mem_sup_left hy, o, ho, rfl⟩
    · have hnd : n * (d ^ m)⁻¹ ∈ L := by
        refine (hL ⟨n * (d ^ m)⁻¹, mul_mem hn (inv_mem hd₂N)⟩).mpr
          (Equiv.Perm.mem_alternatingGroup.mpr ?_)
        have e1 : (⟨n * (d ^ m)⁻¹, mul_mem hn (inv_mem hd₂N)⟩ : ↥N) =
            ⟨n, hn⟩ * (⟨d ^ m, hd₂N⟩ : ↥N)⁻¹ := rfl
        rw [e1, map_mul, map_inv, map_mul, map_inv, h, hd₂odd, mul_inv_cancel]
      obtain ⟨y, hy, o, ho, hyo⟩ := hLmul _ hnd
      have hc : d ^ m * o = o * d ^ m := (mem_centralizer_iff.mp hd₂O o ho).symm
      refine ⟨y * d ^ m, mul_mem (mem_sup_left hy) (mem_sup_right (mem_zpowers _)), o, ho, ?_⟩
      calc n = n * (d ^ m)⁻¹ * d ^ m := by group
        _ = y * o * d ^ m := by rw [hyo]
        _ = y * (d ^ m * o) := by rw [mul_assoc, ← hc]
        _ = y * d ^ m * o := by group
  have hle := oUpper_le_of_forall_mul hWc hWO hOodd hNmul
  rw [eq_bot_iff]
  intro x hx
  have h := mem_inf.mpr ⟨hle hx.1, hx.2⟩
  rwa [hWO] at h

end CFSG.ComponentClassification.AS81.NXKernel
