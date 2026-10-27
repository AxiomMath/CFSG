module

public import CFSG.LocalAnalysis.RankTwoShapes.AlperinFusion
public import CFSG.CharacterTheory.Semidihedral.Local.TransferCosetOrbit

public section

namespace CFSG.GroupTheory

open Subgroup

variable {G : Type*} [Group G]

@[expose] def IsNormalPComplement (p : ℕ) (N : Subgroup G) : Prop :=
  N.Normal ∧ Nat.Coprime (Nat.card N) p ∧ ∃ k : ℕ, N.index = p ^ k

namespace FrobeniusNormalComplement

variable [Finite G] {p : ℕ} [hp : Fact p.Prime]

omit [Finite G] hp in
theorem orderOf_eq_one_of_dvd {x : G} {a b : ℕ} (hab : Nat.Coprime a b) (ha : orderOf x ∣ a)
    (hb : orderOf x ∣ b) : x = 1 :=
  orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes hab ha hb)

omit [Finite G] hp in
theorem orderOf_dvd_of_mem {N : Subgroup G} [Finite N] {x : G} (hx : x ∈ N) :
    orderOf x ∣ Nat.card N := by
  rw [← Subgroup.orderOf_mk x hx]
  exact orderOf_dvd_natCard _

omit hp in
theorem le_of_isNormalPComplement {N₁ N₂ : Subgroup G} (h₁ : IsNormalPComplement p N₁)
    (h₂ : IsNormalPComplement p N₂) : N₂ ≤ N₁ := by
  obtain ⟨hn₁, -, k, hk⟩ := h₁
  obtain ⟨-, hc₂, -⟩ := h₂
  intro x hx
  have h1 : orderOf (QuotientGroup.mk' N₁ x) ∣ Nat.card N₂ :=
    (orderOf_map_dvd _ x).trans (orderOf_dvd_of_mem hx)
  have h2 : orderOf (QuotientGroup.mk' N₁ x) ∣ p ^ k := by
    rw [← hk]
    exact orderOf_dvd_natCard _
  have h3 := orderOf_eq_one_of_dvd (Nat.Coprime.pow_right k hc₂) h1 h2
  rwa [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h3

omit hp in
theorem isNormalPComplement_unique {N₁ N₂ : Subgroup G} (h₁ : IsNormalPComplement p N₁)
    (h₂ : IsNormalPComplement p N₂) : N₁ = N₂ :=
  le_antisymm (le_of_isNormalPComplement h₂ h₁) (le_of_isNormalPComplement h₁ h₂)

omit hp in
theorem IsNormalPComplement.characteristic {N : Subgroup G} (hN : IsNormalPComplement p N) :
    N.Characteristic := by
  refine Subgroup.characteristic_iff_comap_eq.mpr fun φ => isNormalPComplement_unique ?_ hN
  obtain ⟨hn, hc, k, hk⟩ := hN
  refine ⟨hn.comap _, ?_, k, ?_⟩
  · have hcard : Nat.card (N.comap φ.toMonoidHom) = Nat.card N :=
      Nat.card_congr (φ.toEquiv.subtypeEquiv (p := fun x => x ∈ N.comap φ.toMonoidHom)
        (q := fun y => y ∈ N) fun _ => Iff.rfl)
    rw [hcard]
    exact hc
  · rw [Subgroup.index_comap_of_surjective _ φ.surjective, hk]

omit hp in
theorem isPGroup_automizer {N : Subgroup G} (hN : IsNormalPComplement p N) {Q : Subgroup G}
    (hQ : IsPGroup p Q) :
    IsPGroup p (normalizer (Q : Set G) ⧸
      (centralizer (Q : Set G)).subgroupOf (normalizer (Q : Set G))) := by
  obtain ⟨hNn, hcop, k, hk⟩ := hN
  have hQN : ∀ x ∈ Q, x ∈ N → x = 1 := by
    intro x hxQ hxN
    obtain ⟨j, hj⟩ := hQ ⟨x, hxQ⟩
    have hj' : x ^ p ^ j = 1 := by
      have := congrArg Subtype.val hj
      rwa [SubgroupClass.coe_pow, OneMemClass.coe_one] at this
    exact orderOf_eq_one_of_dvd (Nat.Coprime.pow_right j hcop) (orderOf_dvd_of_mem hxN)
      (orderOf_dvd_of_pow_eq_one hj')
  have hcent : ∀ n ∈ N, n ∈ normalizer (Q : Set G) → n ∈ centralizer (Q : Set G) := by
    intro n hn hnQ
    rw [Subgroup.mem_centralizer_iff]
    intro q hq
    have h1 : q * n * q⁻¹ * n⁻¹ ∈ Q := by
      have h := (mem_normalizer_iff.mp hnQ q⁻¹).mp (inv_mem hq)
      have h' := mul_mem hq h
      rwa [show q * (n * q⁻¹ * n⁻¹) = q * n * q⁻¹ * n⁻¹ by group] at h'
    have h2 : q * n * q⁻¹ * n⁻¹ ∈ N := mul_mem (hNn.conj_mem n hn q) (inv_mem hn)
    have h3 := hQN _ h1 h2
    calc q * n = q * n * q⁻¹ * n⁻¹ * (n * q) := by group
      _ = n * q := by rw [h3, one_mul]
  have hGN : IsPGroup p (G ⧸ N) := IsPGroup.of_card (n := k) (by rw [← hk]; rfl)
  intro x
  obtain ⟨h, rfl⟩ := QuotientGroup.mk_surjective x
  obtain ⟨j, hj⟩ := hGN (QuotientGroup.mk (h : G))
  refine ⟨j, ?_⟩
  rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf,
    SubgroupClass.coe_pow]
  rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff] at hj
  exact hcent _ hj (pow_mem h.2 _)

theorem exists_mul_mem_centralizer {Q S : Subgroup G}
    (hQ : IsPGroup p (normalizer (Q : Set G) ⧸
      (centralizer (Q : Set G)).subgroupOf (normalizer (Q : Set G))))
    (hidx : Nat.Coprime p ((S ⊓ normalizer (Q : Set G)).subgroupOf
      (normalizer (Q : Set G))).index)
    {n : G} (hn : n ∈ normalizer (Q : Set G)) :
    ∃ s ∈ S, s ∈ normalizer (Q : Set G) ∧ s⁻¹ * n ∈ centralizer (Q : Set G) := by
  set D := (S ⊓ normalizer (Q : Set G)).subgroupOf (normalizer (Q : Set G))
  set π := QuotientGroup.mk' ((centralizer (Q : Set G)).subgroupOf (normalizer (Q : Set G)))
  have hdvd : (D.map π).index ∣ D.index := Subgroup.index_map_dvd D (QuotientGroup.mk'_surjective _)
  obtain ⟨m, hm⟩ := hQ.index (D.map π)
  have htop : D.map π = ⊤ := by
    rw [← Subgroup.index_eq_one, hm]
    rcases m with _ | m
    · rfl
    · exfalso
      rw [hm, pow_succ] at hdvd
      have hpd : p ∣ D.index := (Dvd.intro_left _ rfl).trans hdvd
      exact hp.out.one_lt.ne' (Nat.Coprime.eq_one_of_dvd hidx hpd)
  have hmem : π ⟨n, hn⟩ ∈ D.map π := by
    rw [htop]
    exact Subgroup.mem_top _
  obtain ⟨s, hsD, hs⟩ := hmem
  refine ⟨s, (Subgroup.mem_inf.mp hsD).1, s.2, ?_⟩
  have h := (QuotientGroup.eq (s := (centralizer (Q : Set G)).subgroupOf
    (normalizer (Q : Set G)))).mp hs
  rw [Subgroup.mem_subgroupOf] at h
  exact h

omit [Finite G] hp in
theorem exists_orbit_reps {α : Type*} [Finite α] (f : α → α) (hf : Function.Injective f) :
    ∃ R : Finset α, ∀ a, ∃! a₀, a₀ ∈ R ∧ ∃ k : ℕ, f^[k] a₀ = a := by
  classical
  have hpos : ∀ a, 0 < Function.minimalPeriod f a := fun a =>
    Function.minimalPeriod_pos_of_mem_periodicPts (hf.mem_periodicPts a)
  let s : Setoid α :=
    { r := fun a b => ∃ k : ℕ, f^[k] a = b
      iseqv := ⟨fun _ => ⟨0, rfl⟩, fun {a b} ⟨k, hk⟩ => ⟨k * Function.minimalPeriod f a - k, by
          rw [← hk, ← Function.iterate_add_apply,
            Nat.sub_add_cancel (Nat.le_mul_of_pos_right k (hpos a)), mul_comm]
          exact ((Function.isPeriodicPt_minimalPeriod f a).mul_const k).eq⟩,
        fun {a b c} ⟨k, hk⟩ ⟨l, hl⟩ => ⟨l + k, by rw [Function.iterate_add_apply, hk, hl]⟩⟩ }
  let := Fintype.ofFinite α
  refine ⟨Finset.univ.image fun a => (Quotient.mk s a).out, fun a =>
    ⟨(Quotient.mk s a).out, ⟨Finset.mem_image_of_mem _ (Finset.mem_univ a), Quotient.mk_out a⟩,
      ?_⟩⟩
  rintro a₁ ⟨ha₁, k, hk⟩
  obtain ⟨b, -, rfl⟩ := Finset.mem_image.mp ha₁
  have h1 : Quotient.mk s (Quotient.mk s b).out = Quotient.mk s a := Quotient.sound ⟨k, hk⟩
  rw [Quotient.out_eq] at h1
  rw [h1]

section Control

variable (hyp : ∀ Q : Subgroup G, IsPGroup p Q →
  IsPGroup p (normalizer (Q : Set G) ⧸
    (centralizer (Q : Set G)).subgroupOf (normalizer (Q : Set G))))
include hyp

theorem exists_mem_sylow_of_alperinDecomposition (S : Sylow p G) {P : Subgroup G} {c : G}
    (hc : CFSG.RankTwoShapes.AlperinDecomposition p (S : Subgroup G) P c) :
    ∃ u ∈ (S : Subgroup G), ∀ x ∈ P, u⁻¹ * x * u = c⁻¹ * x * c := by
  induction hc with
  | one => exact ⟨1, one_mem _, fun x _ => by group⟩
  | @step c n Q _ hQ hPQ hn ih =>
    obtain ⟨u, hu, hux⟩ := ih
    obtain ⟨s, hsS, hsN, hsC⟩ :=
      exists_mul_mem_centralizer (hyp Q (S.isPGroup'.to_le hQ.1)) hQ.2.1 hn
    refine ⟨u * s, mul_mem hu hsS, fun x hx => ?_⟩
    have hy : c⁻¹ * x * c ∈ Q := by
      have h := hPQ ⟨x, hx, rfl⟩
      rwa [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv] at h
    have hsy : s⁻¹ * (c⁻¹ * x * c) * s ∈ Q := by
      have h := (mem_normalizer_iff.mp (inv_mem hsN) (c⁻¹ * x * c)).mp hy
      rwa [inv_inv] at h
    have hcomm := Subgroup.mem_centralizer_iff.mp hsC _ hsy
    calc (u * s)⁻¹ * x * (u * s) = s⁻¹ * (u⁻¹ * x * u) * s := by group
      _ = s⁻¹ * (c⁻¹ * x * c) * s := by rw [hux x hx]
      _ = (s⁻¹ * n)⁻¹ * ((s⁻¹ * n) * (s⁻¹ * (c⁻¹ * x * c) * s)) := by group
      _ = (s⁻¹ * n)⁻¹ * ((s⁻¹ * (c⁻¹ * x * c) * s) * (s⁻¹ * n)) := by rw [hcomm]
      _ = (c * n)⁻¹ * x * (c * n) := by group

theorem exists_sylow_conj (S : Sylow p G) {x g : G} (hx : x ∈ (S : Subgroup G))
    (hg : g⁻¹ * x * g ∈ (S : Subgroup G)) :
    ∃ u ∈ (S : Subgroup G), u⁻¹ * x * u = g⁻¹ * x * g := by
  have hP : zpowers x ≤ (S : Subgroup G) := zpowers_le.mpr hx
  have hPg : (zpowers x).map (MulAut.conj g⁻¹).toMonoidHom ≤ (S : Subgroup G) := by
    rw [MonoidHom.map_zpowers]
    refine zpowers_le.mpr ?_
    rwa [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
  obtain ⟨c, hc, hcg⟩ := CFSG.RankTwoShapes.alperin_centric_radical_fusion S hP hPg
  obtain ⟨u, hu, hux⟩ := exists_mem_sylow_of_alperinDecomposition hyp S hc
  exact ⟨u, hu, (hux x (mem_zpowers x)).trans (hcg x (mem_zpowers x))⟩

theorem transfer_eq_pow_index (S : Sylow p G) (x : (S : Subgroup G)) :
    (Abelianization.of : (S : Subgroup G) →* Abelianization (S : Subgroup G)).transfer (x : G) =
      Abelianization.of x ^ (S : Subgroup G).index := by
  classical
  let := Fintype.ofFinite (Quotient (QuotientGroup.rightRel (S : Subgroup G)))
  obtain ⟨R, hR⟩ := exists_orbit_reps
    (CFSG.Semidihedral.Local.rightCosetMul (S : Subgroup G) (x : G))
    (CFSG.Semidihedral.Local.rightCosetMul_injective _ _)
  obtain ⟨hprod, hsum⟩ := (CFSG.Semidihedral.Local.transfer_coset_orbit_formula
    (S : Subgroup G) Abelianization.of).2 (x : G) R hR (fun C => C.out)
    (fun C _ => Quotient.out_eq C)
  rw [hprod, ← hsum, ← Finset.sum_coe_sort R, ← Finset.prod_pow_eq_pow_sum]
  refine Finset.prod_congr rfl fun C _ => ?_
  set r := Function.minimalPeriod (CFSG.Semidihedral.Local.rightCosetMul (S : Subgroup G) (x : G))
    (C : Quotient (QuotientGroup.rightRel (S : Subgroup G))) with hr
  have hxr : (x : G) ^ r ∈ (S : Subgroup G) := pow_mem x.2 r
  have hmem : (C : Quotient (QuotientGroup.rightRel (S : Subgroup G))).out * (x : G) ^ r *
      (C : Quotient (QuotientGroup.rightRel (S : Subgroup G))).out⁻¹ ∈ (S : Subgroup G) :=
    CFSG.Semidihedral.Local.rep_pow_rep_inv_mem _ (x : G) _ _ (Quotient.out_eq _) _
      Function.iterate_minimalPeriod
  obtain ⟨u, hu, hux⟩ := exists_sylow_conj hyp S hxr
    (g := (C : Quotient (QuotientGroup.rightRel (S : Subgroup G))).out⁻¹) (by rwa [inv_inv])
  have heq : (⟨(C : Quotient (QuotientGroup.rightRel (S : Subgroup G))).out * (x : G) ^ r *
      (C : Quotient (QuotientGroup.rightRel (S : Subgroup G))).out⁻¹, hmem⟩ : (S : Subgroup G)) =
      (⟨u, hu⟩ : (S : Subgroup G))⁻¹ * x ^ r * ⟨u, hu⟩ := by
    apply Subtype.ext
    change (C : Quotient (QuotientGroup.rightRel (S : Subgroup G))).out * (x : G) ^ r *
        (C : Quotient (QuotientGroup.rightRel (S : Subgroup G))).out⁻¹ = u⁻¹ * (x : G) ^ r * u
    rw [hux, inv_inv]
  rw [heq, map_mul, map_mul, map_inv, map_pow, inv_mul_cancel_comm]

omit [Finite G] hp in
theorem automizer_subgroup (K : Subgroup G) (Q : Subgroup K) (hQ : IsPGroup p Q) :
    IsPGroup p (normalizer (Q : Set K) ⧸
      (centralizer (Q : Set K)).subgroupOf (normalizer (Q : Set K))) := by
  have h := hyp (Q.map K.subtype) (hQ.map K.subtype)
  intro x
  obtain ⟨n, rfl⟩ := QuotientGroup.mk_surjective x
  have hn' : ((n : K) : G) ∈ normalizer ((Q.map K.subtype : Subgroup G) : Set G) := by
    rw [mem_normalizer_iff]
    intro y
    constructor
    · rintro ⟨q, hq, rfl⟩
      exact ⟨_, (mem_normalizer_iff.mp n.2 q).mp hq, rfl⟩
    · rintro ⟨q, hq, hqe⟩
      have hyK : y = ((n : K) : G)⁻¹ * K.subtype q * ((n : K) : G) := by
        rw [hqe]
        group
      have hyK' : y ∈ K := by
        rw [hyK]
        exact mul_mem (mul_mem (inv_mem (n : K).2) q.2) (n : K).2
      refine ⟨⟨y, hyK'⟩, (mem_normalizer_iff.mp n.2 ⟨y, hyK'⟩).mpr ?_, rfl⟩
      have hq' : (n : K) * ⟨y, hyK'⟩ * (n : K)⁻¹ = q := Subtype.ext hqe.symm
      rw [hq']
      exact hq
  obtain ⟨j, hj⟩ := h (QuotientGroup.mk ⟨_, hn'⟩)
  refine ⟨j, ?_⟩
  rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf] at hj ⊢
  rw [Subgroup.mem_centralizer_iff] at hj ⊢
  intro q hq
  have h1 := hj (q : G) ⟨q, hq, rfl⟩
  apply Subtype.ext
  simpa only [SubgroupClass.coe_pow, Subgroup.coe_mul] using h1

end Control

end FrobeniusNormalComplement

open FrobeniusNormalComplement

universe u

theorem exists_isNormalPComplement_of_automizer {p : ℕ} [hp : Fact p.Prime] :
    ∀ (n : ℕ) {G : Type u} [Group G] [Finite G], Nat.card G = n →
      (∀ Q : Subgroup G, IsPGroup p Q → IsPGroup p (normalizer (Q : Set G) ⧸
        (centralizer (Q : Set G)).subgroupOf (normalizer (Q : Set G)))) →
      ∃ N : Subgroup G, IsNormalPComplement p N := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro G _ _ hn hyp
  obtain ⟨S⟩ := (Sylow.nonempty : Nonempty (Sylow p G))
  by_cases hS : (S : Subgroup G) = ⊥
  · refine ⟨⊤, inferInstance, ?_, 0, by rw [Subgroup.index_top, pow_zero]⟩
    rw [Subgroup.card_top]
    have h := S.not_dvd_index
    rw [hS, Subgroup.index_bot] at h
    exact ((Nat.Prime.coprime_iff_not_dvd hp.out).mpr h).symm
  set T := (Abelianization.of : (S : Subgroup G) →* Abelianization (S : Subgroup G)).transfer
    with hTdef
  have hT : ∀ x : (S : Subgroup G), T x = Abelianization.of x ^ (S : Subgroup G).index :=
    transfer_eq_pow_index hyp S
  have hAp : IsPGroup p (Abelianization (S : Subgroup G)) := S.isPGroup'.to_quotient _
  obtain ⟨m, hm⟩ := IsPGroup.iff_card.mp hAp
  have hcop : Nat.Coprime (Nat.card (Abelianization (S : Subgroup G)))
      (S : Subgroup G).index := by
    rw [hm]
    exact Nat.Coprime.pow_left m
      ((Nat.Prime.coprime_iff_not_dvd hp.out).mpr S.not_dvd_index)
  have hsurj : Function.Surjective T := by
    intro a
    obtain ⟨y, hy⟩ := QuotientGroup.mk_surjective ((powCoprime hcop).symm a)
    refine ⟨y, ?_⟩
    rw [hT y]
    have hy' : Abelianization.of y = (powCoprime hcop).symm a := hy
    rw [hy', ← powCoprime_apply hcop, Equiv.apply_symm_apply]
  have hKne : T.ker ≠ ⊤ := by
    have : Nontrivial (S : Subgroup G) := (Subgroup.nontrivial_iff_ne_bot _).mpr hS
    have : Group.IsNilpotent (S : Subgroup G) := S.isPGroup'.isNilpotent
    obtain ⟨y, -, hy⟩ := IsConcreteLE.exists_of_lt
      (Group.IsSolvable.commutator_lt_top_of_nontrivial (G := (S : Subgroup G)))
    have hy1 : Abelianization.of y ≠ 1 := by
      rwa [Ne, ← MonoidHom.mem_ker, Abelianization.ker_of]
    obtain ⟨g, hg⟩ := hsurj (Abelianization.of y)
    intro hK
    have hgK : g ∈ T.ker := by
      rw [hK]
      exact Subgroup.mem_top g
    rw [MonoidHom.mem_ker, hg] at hgK
    exact hy1 hgK
  have hKcard : Nat.card T.ker < n := by
    rw [← hn, ← Subgroup.card_top (G := G)]
    exact Subgroup.card_lt_of_lt (lt_top_iff_ne_top.mpr hKne)
  obtain ⟨L₀, hL₀⟩ := ih _ hKcard (G := T.ker) rfl (automizer_subgroup hyp T.ker)
  refine ⟨L₀.map T.ker.subtype, ⟨fun l hl g => ?_⟩, ?_, ?_⟩
  · obtain ⟨l₀, hl₀, rfl⟩ := hl
    have hfix := (IsNormalPComplement.characteristic hL₀).fixed (MulAut.conjNormal g)
    have hmem : l₀ ∈ L₀.comap (MulAut.conjNormal g).toMonoidHom := by
      rw [hfix]
      exact hl₀
    exact ⟨_, hmem, by rw [Subgroup.coe_subtype, MulEquiv.coe_toMonoidHom,
      MulAut.conjNormal_apply]⟩
  · rw [Subgroup.card_map_of_injective T.ker.subtype_injective]
    exact hL₀.2.1
  · obtain ⟨j, hj⟩ := hL₀.2.2
    refine ⟨j + m, ?_⟩
    rw [Subgroup.index_map_subtype, hj, Subgroup.index_ker, MonoidHom.range_eq_top.mpr hsurj,
      Subgroup.card_top, hm, pow_add]

theorem frobenius_normal_p_complement {G : Type*} [Group G] [Finite G] (p : ℕ) [Fact p.Prime] :
    ((∃ N : Subgroup G, IsNormalPComplement p N) ↔
      ∀ Q : Subgroup G, IsPGroup p Q → IsPGroup p (normalizer (Q : Set G) ⧸
        (centralizer (Q : Set G)).subgroupOf (normalizer (Q : Set G)))) ∧
    (∀ N₁ N₂ : Subgroup G, IsNormalPComplement p N₁ → IsNormalPComplement p N₂ → N₁ = N₂) ∧
    ∀ N : Subgroup G, IsNormalPComplement p N → N.Characteristic :=
  ⟨⟨fun ⟨_, hN⟩ _ hQ => isPGroup_automizer hN hQ,
      fun hyp => exists_isNormalPComplement_of_automizer _ rfl hyp⟩,
    fun _ _ h₁ h₂ => isNormalPComplement_unique h₁ h₂,
    fun _ hN => IsNormalPComplement.characteristic hN⟩

theorem hasNormalPComplement_iff_exists {G : Type*} [Group G] [Finite G] (p : ℕ)
    [Fact p.Prime] : CFSG.HasNormalPComplement p G ↔ ∃ N : Subgroup G, IsNormalPComplement p N := by
  constructor
  · rintro ⟨N, hN, hc, hq⟩
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hq
    exact ⟨N, hN, hc.symm, k, hk⟩
  · rintro ⟨N, hN, hc, k, hk⟩
    exact ⟨N, hN, hc.symm, IsPGroup.of_card (n := k) hk⟩

theorem hasNormalPComplement_iff_isPGroup_automizer {G : Type*} [Group G] [Finite G] (p : ℕ)
    [Fact p.Prime] : CFSG.HasNormalPComplement p G ↔
      ∀ Q : Subgroup G, IsPGroup p Q → IsPGroup p (normalizer (Q : Set G) ⧸
        (centralizer (Q : Set G)).subgroupOf (normalizer (Q : Set G))) :=
  (hasNormalPComplement_iff_exists p).trans (frobenius_normal_p_complement p).1

end CFSG.GroupTheory
