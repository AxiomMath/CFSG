module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanParabHub
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanParabPrimeAbstract

public section

namespace CFSG.AGLEmbedding.ToralCensus

open CFSG.AGLEmbedding.ParabPrime (perfectJoin le_perfectJoin perfectJoin_le card_sup_dvd_mul)
open scoped commutatorElement

variable {G : Type*} [Group G]

theorem isPGroup_zpowers_of_pow_pow_eq_one {p k : ℕ} {g : G} (h : g ^ p ^ k = 1) :
    IsPGroup p (Subgroup.zpowers g) := by
  rintro ⟨x, hx⟩
  obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.1 hx
  refine ⟨k, Subtype.ext ?_⟩
  simp only [Subgroup.coe_pow, Subgroup.coe_one]
  rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, h, one_zpow]

open scoped IsMulCommutative in
theorem eq_one_of_mem_center_of_perfect_cyclic [Finite G] [Group.IsPerfect G] {p : ℕ}
    [hp : Fact p.Prime]
    (hcyc : ∀ P : Sylow p G, IsCyclic P) {z : G} (hz : z ∈ Subgroup.center G) (hzp : z ^ p = 1) :
    z = 1 := by
  obtain ⟨P⟩ : Nonempty (Sylow p G) := inferInstance
  have : (Subgroup.zpowers z).Normal := ⟨fun n hn g => by
    rw [Subgroup.mem_center_iff.1 (Subgroup.zpowers_le.2 hz hn) g, mul_inv_cancel_right]
    exact hn⟩
  have hzP : z ∈ (P : Subgroup G) := (isPGroup_zpowers_of_pow_pow_eq_one (k := 1)
    (by rwa [pow_one])).le_sylow_of_normal P (Subgroup.mem_zpowers z)
  have : IsCyclic P := hcyc P
  have hτ := MonoidHom.transfer_eq_pow (MonoidHom.id P) z fun k g₀ _ => by
    rw [mul_assoc, ← Subgroup.mem_center_iff.1 (Subgroup.pow_mem _ hz k) g₀, inv_mul_cancel_left]
  have h1 : MonoidHom.transfer (MonoidHom.id P) z = 1 :=
    Abelianization.commutator_subset_ker _ Group.IsPerfect.mem_commutator
  have h2 : z ^ (P : Subgroup G).index = 1 := by
    have := congrArg Subtype.val (hτ.symm.trans h1)
    simpa using this
  have hcop : Nat.Coprime p (P : Subgroup G).index :=
    (Nat.Prime.coprime_iff_not_dvd hp.out).2 P.not_dvd_index
  exact orderOf_eq_one_iff.1 (Nat.eq_one_of_dvd_coprimes hcop (orderOf_dvd_of_pow_eq_one hzp)
    (orderOf_dvd_of_pow_eq_one h2))

theorem eq_one_of_commute_of_perfect_cyclic [Finite G] {p : ℕ} (hp : p.Prime) {A : Subgroup G}
    (hA : ⁅A, A⁆ = A) (hcyc : ∀ Q : Subgroup G, Q ≤ A → IsPGroup p Q → IsCyclic Q) {z : G}
    (hzA : z ∈ A) (hz : ∀ a ∈ A, a * z = z * a) (hzp : z ^ p = 1) : z = 1 := by
  have : Fact p.Prime := ⟨hp⟩
  have : Group.IsPerfect A := Subgroup.isPerfect_iff.2 hA
  have key := eq_one_of_mem_center_of_perfect_cyclic (G := A) (p := p) (z := ⟨z, hzA⟩)
    (fun P => by
      have hc := hcyc ((P : Subgroup A).map A.subtype)
        (by rintro _ ⟨x, -, rfl⟩; exact x.2) (P.isPGroup'.map _)
      let e := Subgroup.equivMapOfInjective (P : Subgroup A) A.subtype A.subtype_injective
      exact isCyclic_of_surjective e.symm.toMonoidHom e.symm.surjective)
    (Subgroup.mem_center_iff.2 fun g => Subtype.ext (hz g g.2))
    (Subtype.ext (by simpa using hzp))
  simpa using congrArg Subtype.val key

theorem mem_zpowers_of_isCyclic_of_dvd {Q : Subgroup G} [Finite Q] (hQ : IsCyclic Q) {a b : G}
    (ha : a ∈ Q) (hb : b ∈ Q) (hab : orderOf a ∣ orderOf b) : a ∈ Subgroup.zpowers b := by
  have h : Subgroup.zpowers (⟨a, ha⟩ : Q) ≤ Subgroup.zpowers ⟨b, hb⟩ := by
    rw [IsCyclic.subgroup_le_iff_card_dvd, Nat.card_zpowers, Nat.card_zpowers,
      Subgroup.orderOf_mk, Subgroup.orderOf_mk]
    exact hab
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 (h (Subgroup.mem_zpowers _))
  exact Subgroup.mem_zpowers_iff.2 ⟨k, by simpa using congrArg Subtype.val hk⟩

theorem mem_zpowers_of_commute_of_pow [Finite G] {p : ℕ} {V : Subgroup G}
    (hcyc : ∀ Q : Subgroup G, Q ≤ V → IsPGroup p Q → IsCyclic Q) {a b : G} (ha : a ∈ V)
    (hb : b ∈ V) (hab : Commute a b) (hap : a ^ p = 1) (hbp : orderOf b = p) :
    a ∈ Subgroup.zpowers b := by
  set Q := Subgroup.closure ({a, b} : Set G) with hQ
  have hQV : Q ≤ V := (Subgroup.closure_le V).2 (by
    rintro _ (rfl | rfl)
    exacts [ha, hb])
  have hbp' : b ^ p = 1 := by rw [← hbp]; exact pow_orderOf_eq_one b
  have hpow : ∀ g ∈ Q, g ^ p = 1 := fun g hg =>
    ParabHub.pow_eq_one_of_mem_closure (Set.pairwise_pair.2 fun _ => ⟨hab, hab.symm⟩)
      (by rintro _ (rfl | rfl); exacts [hap, hbp']) hg
  have hQp : IsPGroup p Q := fun g => ⟨1, Subtype.ext (by simpa using hpow g g.2)⟩
  exact mem_zpowers_of_isCyclic_of_dvd (hcyc Q hQV hQp) (Subgroup.subset_closure (Or.inl rfl))
    (Subgroup.subset_closure (Or.inr rfl)) (by rw [hbp]; exact orderOf_dvd_of_pow_eq_one hap)

theorem exists_conj_mem_zpowers_of_cyclic [Finite G] {p : ℕ} (hp : p.Prime) {V : Subgroup G}
    (hcyc : ∀ Q : Subgroup G, Q ≤ V → IsPGroup p Q → IsCyclic Q) {u x : G} (hu : u ∈ V)
    (hx : x ∈ V) (hup : u ^ p = 1) (hxp : orderOf x = p) :
    ∃ g ∈ V, g * u * g⁻¹ ∈ Subgroup.zpowers x := by
  have : Fact p.Prime := ⟨hp⟩
  have hxp' : x ^ p = 1 := by rw [← hxp]; exact pow_orderOf_eq_one x
  obtain ⟨P, hP⟩ := (isPGroup_zpowers_of_pow_pow_eq_one (k := 1) (g := (⟨x, hx⟩ : V))
    (Subtype.ext (by simpa using hxp'))).exists_le_sylow
  obtain ⟨Q, hQ⟩ := (isPGroup_zpowers_of_pow_pow_eq_one (k := 1) (g := (⟨u, hu⟩ : V))
    (Subtype.ext (by simpa using hup))).exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq V Q P
  have hgu : g * ⟨u, hu⟩ * g⁻¹ ∈ (P : Subgroup V) := by
    rw [← hg, Sylow.coe_subgroup_smul, Subgroup.pointwise_smul_def]
    exact ⟨_, hQ (Subgroup.mem_zpowers _), rfl⟩
  have hcP := hcyc ((P : Subgroup V).map V.subtype) (by rintro _ ⟨y, -, rfl⟩; exact y.2)
    (P.isPGroup'.map _)
  refine ⟨g, g.2, mem_zpowers_of_isCyclic_of_dvd hcP ⟨_, hgu, rfl⟩
    ⟨_, hP (Subgroup.mem_zpowers _), rfl⟩
    ?_⟩
  have hc : orderOf ((g : G) * u * (g : G)⁻¹) = orderOf u := by
    have := MulEquiv.orderOf_eq (MulAut.conj (g : G)) u
    simpa using this
  rw [hc, hxp]
  exact orderOf_dvd_of_pow_eq_one hup

theorem exists_conj_mem_of_sup [Finite G] {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {L R : Subgroup G} (hR : IsPGroup 2 R) (hLR : L ≤ Subgroup.normalizer (R : Set G)) {u : G}
    (hu : u ∈ L ⊔ R) {k : ℕ} (huk : u ^ p ^ k = 1) : ∃ g ∈ L ⊔ R, g * u * g⁻¹ ∈ L := by
  have : Fact p.Prime := ⟨hp⟩
  set N := L ⊔ R with hN
  set L' : Subgroup N := L.subgroupOf N with hL'
  have hidx : L'.index ∣ Nat.card R := by
    have h1 := card_sup_dvd_mul L R hLR
    have h2 : Nat.card L' = Nat.card L :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe le_sup_left).toEquiv
    have h3 := L'.card_mul_index
    rw [h2] at h3
    rw [← hN, ← h3] at h1
    exact Nat.dvd_of_mul_dvd_mul_left Nat.card_pos h1
  have hpL : ¬ p ∣ L'.index := by
    obtain ⟨a, ha⟩ := hR.exists_card_eq
    intro hd
    have h2 := (hd.trans hidx).trans (by rw [ha])
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 (hp.dvd_of_dvd_pow h2))
  obtain ⟨S₁⟩ : Nonempty (Sylow p L') := inferInstance
  set S : Subgroup N := (S₁ : Subgroup L').map L'.subtype with hS
  have hSp : IsPGroup p S := S₁.isPGroup'.map _
  have hSi : ¬ p ∣ S.index := by
    rw [hS, Subgroup.index_map_subtype]
    exact fun hd => (hp.dvd_mul.1 hd).elim S₁.not_dvd_index hpL
  obtain ⟨Q, hQ⟩ := (isPGroup_zpowers_of_pow_pow_eq_one (k := k) (g := (⟨u, hu⟩ : N))
    (Subtype.ext (by simpa using huk))).exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq N Q (hSp.toSylow hSi)
  have hgu : g * ⟨u, hu⟩ * g⁻¹ ∈ S := by
    have : g * ⟨u, hu⟩ * g⁻¹ ∈ ((hSp.toSylow hSi : Sylow p N) : Subgroup N) := by
      rw [← hg, Sylow.coe_subgroup_smul, Subgroup.pointwise_smul_def]
      exact ⟨_, hQ (Subgroup.mem_zpowers _), rfl⟩
    simpa using this
  obtain ⟨y, -, hy⟩ := hgu
  refine ⟨g, g.2, ?_⟩
  have hyL : ((y : N) : G) ∈ L := Subgroup.mem_subgroupOf.1 y.2
  have hye : ((y : N) : G) = g * u * (g : G)⁻¹ := by
    have := congrArg Subtype.val hy
    simpa using this
  rwa [hye] at hyL

theorem le_map_of_perfect_of_commute {X : Type*} [Group X] {ψ : G →* X}
    (hψ : Function.Surjective ψ) (hker : ψ.ker ≤ Subgroup.center G) {J : Subgroup G} {v : G}
    (hfix : ∀ l : G, v * l * v⁻¹ = l → l ∈ J) {P : Subgroup X} (hP : ⁅P, P⁆ = P)
    (hPv : ∀ x ∈ P, x * ψ v = ψ v * x) : P ≤ J.map ψ := by
  set A := P.comap ψ with hA
  have hc : ∀ a ∈ A, a * v * a⁻¹ * v⁻¹ ∈ Subgroup.center G := fun a ha => hker (by
    rw [MonoidHom.mem_ker, map_mul, map_mul, map_mul, map_inv, map_inv, hPv (ψ a) ha]
    group)
  let f : A →* Subgroup.center G :=
    { toFun := fun a => ⟨a * v * a⁻¹ * v⁻¹, hc a a.2⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun a b => Subtype.ext (by
        have hz := Subgroup.mem_center_iff.1 (hc b b.2)
        change (a : G) * b * v * ((a : G) * b)⁻¹ * v⁻¹ =
          (a * v * (a : G)⁻¹ * v⁻¹) * (b * v * (b : G)⁻¹ * v⁻¹)
        calc (a : G) * b * v * ((a : G) * b)⁻¹ * v⁻¹
            = a * (b * v * (b : G)⁻¹ * v⁻¹) * (v * (a : G)⁻¹ * v⁻¹) := by group
          _ = (b * v * (b : G)⁻¹ * v⁻¹) * a * (v * (a : G)⁻¹ * v⁻¹) := by rw [hz]
          _ = (b * v * (b : G)⁻¹ * v⁻¹) * (a * v * (a : G)⁻¹ * v⁻¹) := by group
          _ = _ := (hz _).symm) }
  have hcomm : ⁅A, A⁆ ≤ J := by
    intro x hx
    rw [← Subgroup.map_subtype_commutator] at hx
    obtain ⟨y, hy, rfl⟩ := hx
    have h1 : f y = 1 := Abelianization.commutator_subset_ker f hy
    have h2 : (y : G) * v * (y : G)⁻¹ * v⁻¹ = 1 := congrArg Subtype.val h1
    apply hfix
    calc v * (y : G) * v⁻¹ = ((y : G) * v * (y : G)⁻¹ * v⁻¹)⁻¹ * y := by group
      _ = y := by rw [h2, inv_one, one_mul]
  calc P = ⁅P, P⁆ := hP.symm
    _ = (⁅A, A⁆).map ψ := by
        rw [Subgroup.map_commutator, hA, Subgroup.map_comap_eq_self_of_surjective hψ]
    _ ≤ J.map ψ := Subgroup.map_mono hcomm

theorem perfectJoin_le_of_le_sup {J T N : Subgroup G} (hJ : J ≤ T ⊔ N)
    (hTN : T ≤ Subgroup.normalizer (N : Set G)) (hTc : ∀ a ∈ T, ∀ b ∈ T, a * b = b * a) :
    perfectJoin J ≤ N := by
  have : (N.subgroupOf (T ⊔ N)).Normal := Subgroup.normal_subgroupOf_sup_of_le_normalizer hTN
  set φ := QuotientGroup.mk' (N.subgroupOf (T ⊔ N)) with hφ
  have hdec : ∀ a (ha : a ∈ T ⊔ N), ∃ t, ∃ ht : t ∈ T,
      φ ⟨a, ha⟩ = φ ⟨t, Subgroup.mem_sup_left ht⟩ := by
    intro a ha
    have ha' : a ∈ ((T ⊔ N : Subgroup G) : Set G) := ha
    rw [Subgroup.coe_mul_of_left_le_normalizer_right T N hTN] at ha'
    obtain ⟨t, ht, n, hn, rfl⟩ := ha'
    refine ⟨t, ht, ?_⟩
    rw [hφ, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq,
      Subgroup.mem_subgroupOf]
    simpa [mul_assoc] using inv_mem hn
  have hcomm : ∀ a ∈ T ⊔ N, ∀ b ∈ T ⊔ N, ⁅a, b⁆ ∈ N := by
    intro a ha b hb
    obtain ⟨t₁, ht₁, h1⟩ := hdec a ha
    obtain ⟨t₂, ht₂, h2⟩ := hdec b hb
    have hc : ⁅(⟨t₁, Subgroup.mem_sup_left ht₁⟩ : ↥(T ⊔ N)),
        (⟨t₂, Subgroup.mem_sup_left ht₂⟩ : ↥(T ⊔ N))⁆ = 1 := Subtype.ext (by
      simp only [commutatorElement_def, Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_one]
      rw [hTc t₁ ht₁ t₂ ht₂]
      group)
    have h3 : φ ⁅(⟨a, ha⟩ : ↥(T ⊔ N)), (⟨b, hb⟩ : ↥(T ⊔ N))⁆ = 1 := by
      rw [map_commutatorElement, h1, h2, ← map_commutatorElement, hc, map_one]
    have := Subgroup.mem_subgroupOf.1 ((QuotientGroup.eq_one_iff _).1 h3)
    have e : ((⁅(⟨a, ha⟩ : ↥(T ⊔ N)), (⟨b, hb⟩ : ↥(T ⊔ N))⁆ : ↥(T ⊔ N)) : G) = ⁅a, b⁆ := by
      simp [commutatorElement_def]
    rwa [e] at this
  calc perfectJoin J = ⁅perfectJoin J, perfectJoin J⁆ := (ParabPrime.perfectJoin_perfect J).symm
    _ ≤ N := Subgroup.commutator_le.2 fun a ha b hb =>
        hcomm a (hJ (perfectJoin_le J ha)) b (hJ (perfectJoin_le J hb))

end CFSG.AGLEmbedding.ToralCensus
