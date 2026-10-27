module

public import CFSG.LocalAnalysis.ComponentClassification.SolMaxSig23
public import CFSG.LocalAnalysis.ComponentClassification.Sol78HMaxComp

public section

namespace CFSG.ComponentClassification.SolMax

open CFSG Subgroup

variable {X : Type} [Group X]

theorem fusionZStar_isSolvable {L : Type*} [Group L] [Finite L] :
    Group.IsSolvable ↥(Open.fusionZStar L) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hO : Group.IsSolvable ↥(pPrimeCore 2 L) :=
    Milestones.odd_order_solvable (Nat.coprime_two_left.mp pPrimeCore_coprime_card)
  have hC : Group.IsSolvable ↥(center (L ⧸ pPrimeCore 2 L)) :=
    Group.isSolvable_of_comm fun a b => Subtype.ext ((mem_center_iff.mp b.2) (a : _))
  let g : ↥(Open.fusionZStar L) →* ↥(center (L ⧸ pPrimeCore 2 L)) :=
    ((QuotientGroup.mk' (pPrimeCore 2 L)).comp (Open.fusionZStar L).subtype).codRestrict _
      fun x => by
        have hx : (x : L) ∈ (center (L ⧸ pPrimeCore 2 L)).comap
            (QuotientGroup.mk' (pPrimeCore 2 L)) := by
          rw [← Sol78.fusionZStar_eq_comap]
          exact x.2
        exact hx
  let f : ↥(pPrimeCore 2 L) →* ↥(Open.fusionZStar L) :=
    inclusion (Sol78.pPrimeCore_le_fusionZStar L)
  refine Group.isSolvable_of_ker_le_range f g fun x hx => ?_
  have hx' : (x : L) ∈ pPrimeCore 2 L := by
    have h1 : g x = 1 := hx
    have h2 := congrArg Subtype.val h1
    change QuotientGroup.mk' (pPrimeCore 2 L) (x : L) = 1 at h2
    rwa [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h2
  exact ⟨⟨x, hx'⟩, rfl⟩

theorem le_of_le_normalizer_of_perfect [Finite X] {L K N : Subgroup X} (hLperf : ⁅L, L⁆ = L)
    (hLq : IsQuasisimple (↥L ⧸ pPrimeCore 2 ↥L)) (hKL : K ≤ L) (hKperf : ⁅K, K⁆ = K)
    (hK : K ≠ ⊥) (hKN : K ≤ N) (hLN : L ≤ normalizer (N : Set X)) : L ≤ N := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set N' := N.subgroupOf L with hN'def
  have hN' : N'.Normal := by
    refine ⟨fun x hx l => ?_⟩
    rw [mem_subgroupOf] at hx ⊢
    simpa using (mem_normalizer_iff.mp (hLN l.2) (x : X)).mp hx
  set Q := ↥L ⧸ pPrimeCore 2 ↥L
  set q := QuotientGroup.mk' (pPrimeCore 2 ↥L)
  set r := QuotientGroup.mk' (center Q)
  have : IsSimpleGroup (Q ⧸ center Q) := hLq.2.1
  have hnorm : ((N'.map q).map r).Normal :=
    (hN'.map q (QuotientGroup.mk'_surjective _)).map r (QuotientGroup.mk'_surjective _)
  have hLp : Group.IsPerfect ↥L := (Subgroup.isPerfect_iff).mpr hLperf
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal ((N'.map q).map r) with h | h
  ·
    exfalso
    have hle : N' ≤ Open.fusionZStar ↥L := by
      intro x hx
      rw [Sol78.fusionZStar_eq_comap, mem_comap]
      have h1 : r (q x) = 1 := by
        rw [← mem_bot, ← h]
        exact mem_map_of_mem r (mem_map_of_mem q hx)
      rwa [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
    have hKZ : K.subgroupOf L ≤ Open.fusionZStar ↥L :=
      fun x hx => hle (show (x : X) ∈ N from hKN hx)
    have hsolv : Group.IsSolvable ↥(K.subgroupOf L) := by
      have := fusionZStar_isSolvable (L := ↥L)
      exact Group.isSolvable_of_isSolvable_injective (f := inclusion hKZ) (inclusion_injective hKZ)
    have hKp : Group.IsPerfect ↥(K.subgroupOf L) := by
      have : Group.IsPerfect ↥K := (Subgroup.isPerfect_iff).mpr hKperf
      exact Group.IsPerfect.ofSurjective (f := (subgroupOfEquivOfLe hKL).symm.toMonoidHom)
        (subgroupOfEquivOfLe hKL).symm.surjective
    have hKnt : Nontrivial ↥(K.subgroupOf L) := by
      rw [nontrivial_iff_ne_bot]
      intro h0
      apply hK
      rw [← map_subgroupOf_eq_of_le hKL, h0, Subgroup.map_bot]
    exact Group.IsPerfect.not_isSolvable _ hsolv
  ·
    by_contra hLN'
    have hN'ne : N' ≠ ⊤ := by
      intro htop
      apply hLN'
      intro l hl
      have : (⟨l, hl⟩ : ↥L) ∈ N' := htop ▸ mem_top _
      exact this
    set π := QuotientGroup.mk' N'
    have hπ : Function.Surjective π := QuotientGroup.mk'_surjective _
    have hsurj : Function.Surjective (π.comp (Open.fusionZStar ↥L).subtype) := by
      intro y
      obtain ⟨l, rfl⟩ := hπ y
      have hl : r (q l) ∈ (N'.map q).map r := by rw [h]; exact mem_top _
      obtain ⟨_, ⟨n, hn, rfl⟩, hnl⟩ := hl
      have hz : n⁻¹ * l ∈ Open.fusionZStar ↥L := by
        rw [Sol78.fusionZStar_eq_comap, mem_comap, map_mul, map_inv]
        have h1 : ((QuotientGroup.mk' (pPrimeCore 2 ↥L) n : Q) : Q ⧸ center Q) =
            ((QuotientGroup.mk' (pPrimeCore 2 ↥L) l : Q) : Q ⧸ center Q) := hnl
        rw [QuotientGroup.eq] at h1
        exact h1
      refine ⟨⟨n⁻¹ * l, hz⟩, ?_⟩
      change π (n⁻¹ * l) = π l
      have hn1 : π n = 1 := by
        rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
        exact hn
      rw [map_mul, map_inv, hn1, inv_one, one_mul]
    have hsolvQ : Group.IsSolvable (↥L ⧸ N') := by
      have := fusionZStar_isSolvable (L := ↥L)
      exact Group.isSolvable_of_surjective hsurj
    have hperfQ : Group.IsPerfect (↥L ⧸ N') := Group.IsPerfect.ofSurjective hπ
    have hntQ : Nontrivial (↥L ⧸ N') := by
      rw [← not_subsingleton_iff_nontrivial, QuotientGroup.subsingleton_iff]
      exact hN'ne
    exact Group.IsPerfect.not_isSolvable _ hsolvQ

theorem exists_involution_commute_of_even [Finite X] {K : Subgroup X} {t : X} {s : ℕ}
    (hts : t ^ 2 ^ s = 1) (htK : t ∈ normalizer (K : Set X)) (hK : Even (Nat.card K)) :
    ∃ u ∈ K, orderOf u = 2 ∧ u * t = t * u := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have := Fintype.ofFinite ↥K
  let σ : Equiv.Perm ↥K :=
    { toFun := fun x => ⟨t * x * t⁻¹, (mem_normalizer_iff.mp htK x).mp x.2⟩
      invFun := fun x => ⟨t⁻¹ * x * t, by
        have h := (mem_normalizer_iff.mp (inv_mem htK) x).mp x.2
        rwa [inv_inv] at h⟩
      left_inv := fun x => Subtype.ext (by simp [mul_assoc])
      right_inv := fun x => Subtype.ext (by simp [mul_assoc]) }
  have hσapp : ∀ x : ↥K, ((σ x : ↥K) : X) = t * x * t⁻¹ := fun x => rfl
  have hσpow : ∀ k : ℕ, ∀ x : ↥K, (((σ ^ k) x : ↥K) : X) = t ^ k * x * (t ^ k)⁻¹ := by
    intro k
    induction k with
    | zero => intro x; simp
    | succ k ih =>
      intro x
      rw [pow_succ', Equiv.Perm.mul_apply, hσapp, ih, pow_succ', mul_inv_rev]
      group
  have hσ : σ ^ 2 ^ s = 1 := by
    ext x
    rw [hσpow, hts, inv_one, one_mul, mul_one]
    rfl
  have hmod := Equiv.Perm.card_compl_support_modEq (p := 2) (n := s) hσ
  set C := K ⊓ centralizer ({t} : Set X) with hCdef
  have hfix : σ.supportᶜ.card = Nat.card C := by
    have h1 : σ.supportᶜ = Finset.univ.filter (fun x => σ x = x) := by
      ext x
      simp [Equiv.Perm.mem_support]
    rw [h1, ← Fintype.card_subtype, ← Nat.card_eq_fintype_card]
    refine Nat.card_congr ⟨fun x => ⟨(x : ↥K), (x : ↥K).2, ?_⟩, fun c => ⟨⟨c, c.2.1⟩, ?_⟩,
      fun _ => rfl, fun _ => rfl⟩
    · have h2 := congrArg Subtype.val x.2
      rw [hσapp] at h2
      show ((x : ↥K) : X) ∈ centralizer ({t} : Set X)
      rw [mem_centralizer_singleton_iff]
      calc ((x : ↥K) : X) * t = t * (x : ↥K) * t⁻¹ * t := by rw [h2]
        _ = t * (x : ↥K) := by group
    · have hc : (c : X) * t = t * c := mem_centralizer_singleton_iff.mp c.2.2
      apply Subtype.ext
      rw [hσapp]
      change t * (c : X) * t⁻¹ = c
      rw [← hc]
      group
  rw [hfix, ← Nat.card_eq_fintype_card] at hmod
  have hC : 2 ∣ Nat.card C := by
    have h1 : Nat.card ↥K % 2 = 0 := Nat.even_iff.mp hK
    have h2 : Nat.card C % 2 = Nat.card ↥K % 2 := hmod
    omega
  obtain ⟨u, hu⟩ := exists_prime_orderOf_dvd_card' 2 hC
  refine ⟨u, u.2.1, by rw [Subgroup.orderOf_coe]; exact hu, ?_⟩
  exact mem_centralizer_singleton_iff.mp u.2.2

theorem factorization_two_eq_of_coreQuot {P Q : Type*} [Group P] [Finite P] [Group Q]
    (φ : P ⧸ pPrimeCore 2 P ≃* Q) :
    (Nat.card P).factorization 2 = (Nat.card Q).factorization 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup (pPrimeCore 2 P)
  rw [Nat.card_congr φ.toEquiv] at h1
  have hQ : Nat.card Q ≠ 0 := by
    rw [← Nat.card_congr φ.toEquiv]
    exact Nat.card_pos.ne'
  have hO : (Nat.card ↥(pPrimeCore 2 P)).factorization 2 = 0 :=
    Nat.factorization_eq_zero_of_not_dvd fun h2 =>
      (Nat.not_even_iff_odd.mpr (Nat.coprime_two_left.mp pPrimeCore_coprime_card))
        (even_iff_two_dvd.mpr h2)
  rw [h1, Nat.factorization_mul hQ Nat.card_pos.ne', Finsupp.add_apply, hO, add_zero]

namespace Sig36

variable [Finite X] [IsSimpleGroup X] {t : X} {J : Subgroup X} {n : ℕ}
  {e : J ⧸ pPrimeCore 2 J ≃* alternatingGroup (Fin n)} {E : Subgroup X} {D : Finset (Fin n)}
  (S : Sig36 X t J n e E D)
include S

theorem factorization_two_le (hT13 : Sol76T13.SolomonThm13Simple)
    (hML : Sol78.MaximalityLemmaInput) (hSch : SolAltLit.SchurAlternatingMultiplierInput) {u : X}
    (hu : orderOf u = 2) (hut : u ∈ centralizer ({t} : Set X))
    (huK : u ∈ UnbalancedLayer.coreActionKernel J) {L : Subgroup X}
    (hLu : L ≤ centralizer ({u} : Set X)) (hLperf : ⁅L, L⁆ = L)
    (hLq : IsQuasisimple (↥L ⧸ pPrimeCore 2 ↥L)) (hJL : GSLit.fixedLayer J (zpowers u) ≤ L) :
    (Nat.card L).factorization 2 ≤ (Nat.card J).factorization 2 := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hu2 : IsPGroup 2 (zpowers u) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hu, pow_one])
  have ht2 : IsPGroup 2 (zpowers t) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, S.pair.1.1, pow_one])
  obtain ⟨hJuJ, hJuu, hJuC, ⟨eJu⟩⟩ := S.fixedLayer_facts hu2 hut huK
  set Ju := GSLit.fixedLayer J (zpowers u) with hJudef
  have htu : u * t = t * u := mem_centralizer_singleton_iff.mp hut
  have hT2 : IsPGroup 2 (zpowers t ⊔ zpowers u : Subgroup X) :=
    IsPGroup.to_sup_of_normal_right' ht2 hu2
      (zpowers_le.mpr (mem_normalizer_zpowers_of_commute htu))
  have hT : (zpowers t ⊔ zpowers u : Subgroup X) ≠ ⊥ := by
    intro h
    have ht : t ∈ zpowers t ⊔ zpowers u := mem_sup_left (mem_zpowers t)
    rw [h, mem_bot] at ht
    have := S.pair.1.1
    rw [ht, orderOf_one] at this
    omega
  have hN := Sol78H.le_normalizer_core_sup_of_thm13_centralizer hT13 hML hSch S.nonab S.kProper
    S.unbal S.notU S.pair.2.1 S.pair.2.2.1 ⟨t, J, S.pair.1⟩ S.pair.2.2.2.1 hT hT2 hJuC ⟨eJu⟩ hu
    hJuu
  have hJuperf : ⁅Ju, Ju⁆ = Ju := UnbalancedCorr.commutator_eq_of_isPComponent hJuC.1 hJuC.2
  have hJune : Ju ≠ ⊥ := by
    intro h0
    have : Nontrivial (alternatingGroup (Fin n)) :=
      alternatingGroup.nontrivial_of_three_le_card (by rw [Nat.card_fin]; have := S.nine_le; omega)
    have : Subsingleton ↥Ju := by
      rw [h0]
      infer_instance
    have : Subsingleton (↥Ju ⧸ pPrimeCore 2 ↥Ju) := inferInstance
    have : Subsingleton (alternatingGroup (Fin n)) := eJu.symm.toEquiv.subsingleton
    exact false_of_nontrivial_of_subsingleton (alternatingGroup (Fin n))
  have h1 := factorization_two_le_of_normalizer hJuu hLu hN fun N hJuN hLN =>
    le_of_le_normalizer_of_perfect hLperf hLq hJL hJuperf hJune hJuN hLN
  rw [factorization_two_eq_of_coreQuot eJu, ← factorization_two_eq_of_coreQuot e] at h1
  exact h1

end Sig36

end CFSG.ComponentClassification.SolMax
