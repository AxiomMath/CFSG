module

public import CFSG.GH74.Generic.Front.Defs
public import CFSG.GH74.Generic.OuterRank
public import CFSG.GH74.Generic.OuterInvolution

public section

namespace CFSG.GH74.Generic

open CFSG CFSG.GH74 CFSG.GH74.L5U5 Subgroup

theorem normIn_of_normal {Y : Type*} [Group Y] {H₁ Q : Subgroup Y} (hQ : Q ≤ H₁)
    (h : (Q.subgroupOf H₁).Normal) : ∀ k ∈ H₁, ∀ q ∈ Q, k * q * k⁻¹ ∈ Q :=
  fun a ha q hq => (normal_subgroupOf_iff hQ).1 h q a hq ha

theorem normal_of_normIn {Y : Type*} [Group Y] {H₁ Q : Subgroup Y} (hQ : Q ≤ H₁)
    (h : ∀ k ∈ H₁, ∀ q ∈ Q, k * q * k⁻¹ ∈ Q) : (Q.subgroupOf H₁).Normal :=
  (normal_subgroupOf_iff hQ).2 fun q a hq ha => h a ha q hq

theorem exists_pow_odd_order {Y Z : Type*} [Group Y] [Group Z] [Finite Y] (π : Y →* Z) (q : Y)
    (hz : Odd (orderOf (π q))) : ∃ k : ℕ, Odd (orderOf (q ^ k)) ∧ π (q ^ k) = π q := by
  have hq0 : orderOf q ≠ 0 := (orderOf_pos q).ne'
  obtain ⟨a, m, hm, ho⟩ := Nat.exists_eq_two_pow_mul_odd hq0
  set r := orderOf (π q) with hr
  have hcop : Nat.Coprime (2 ^ a) r :=
    Nat.Coprime.pow_left _ (Nat.coprime_two_left.2 hz)
  obtain ⟨k, hk1, hk2⟩ := Nat.chineseRemainder hcop 0 1
  refine ⟨k, ?_, ?_⟩
  · have h2a : 2 ^ a ∣ k := (Nat.modEq_zero_iff_dvd).1 hk1
    obtain ⟨t, ht⟩ := h2a
    have hkm : k * m = orderOf q * t := by rw [ht, ho]; ring
    have hdvd : orderOf (q ^ k) ∣ m := by
      apply orderOf_dvd_of_pow_eq_one
      rw [← pow_mul, hkm, pow_mul, pow_orderOf_eq_one, one_pow]
    exact Odd.of_dvd_nat hm hdvd
  · rw [map_pow]
    calc π q ^ k = π q ^ (k % r) := (pow_mod_orderOf _ _).symm
      _ = π q ^ (1 % r) := by rw [hk2]
      _ = π q ^ 1 := pow_mod_orderOf _ _
      _ = π q := pow_one _

theorem exists_hull {Y Z : Type*} [Group Y] [Group Z] [Finite Y] (π : Y →* Z)
    (hodd : ∀ n : Y, π n = 1 → Odd (orderOf n)) (H₁ : Subgroup Y)
    (H : Subgroup Z) (hH : H₁.map π = H) :
    ∃ Q : Subgroup Y, Q ≤ H₁ ∧ (Q.subgroupOf H₁).Normal ∧ Q.map π = H ∧
      (⁅H, H⁆ = H → ⁅Q, Q⁆ = Q) ∧ (OddGenerated H → OddGenerated Q) ∧
      ∀ g ∈ H₁, (∃ k : ℕ, g ^ (2 ^ k) = 1) → g ∈ Q := by
  classical
  let S : Set (Subgroup Y) := {Q | Q ≤ H₁ ∧ (Q.subgroupOf H₁).Normal ∧ Q.map π = H}
  have hS : S.Nonempty := ⟨H₁, le_rfl, by rw [subgroupOf_self]; infer_instance, hH⟩
  obtain ⟨Q, hQ⟩ := (Set.toFinite S).exists_minimal hS
  obtain ⟨hQ1, hQ2, hQ3⟩ := hQ.prop
  have hmin : ∀ Q' ∈ S, Q' ≤ Q → Q ≤ Q' := fun Q' hQ' hle => hQ.2 hQ' hle
  have hnorm := normIn_of_normal hQ1 hQ2
  have hconj : ∀ k ∈ H₁, Q.map (MulAut.conj k).toMonoidHom ≤ Q := by
    rintro k hk _ ⟨q, hq, rfl⟩
    exact hnorm k hk q hq
  refine ⟨Q, hQ1, hQ2, hQ3, ?_, ?_, ?_⟩
  · intro hperf
    have hle : ⁅Q, Q⁆ ≤ Q := (Subgroup.commutator_le).2 fun a ha b hb => by
      rw [commutatorElement_def]
      exact Q.mul_mem (Q.mul_mem (Q.mul_mem ha hb) (Q.inv_mem ha)) (Q.inv_mem hb)
    have hmem : ⁅Q, Q⁆ ∈ S := by
      refine ⟨hle.trans hQ1, normal_of_normIn (hle.trans hQ1) ?_, ?_⟩
      · intro k hk q hq
        have h1 : ⁅Q, Q⁆.map (MulAut.conj k).toMonoidHom ≤ ⁅Q, Q⁆ := by
          rw [Subgroup.map_commutator]
          exact Subgroup.commutator_mono (hconj k hk) (hconj k hk)
        exact h1 ⟨q, hq, rfl⟩
      · rw [Subgroup.map_commutator, hQ3, hperf]
    exact le_antisymm hle (hmin _ hmem hle)
  · intro hoddH
    let Q'' : Subgroup Y := Subgroup.closure {g : Y | g ∈ Q ∧ Odd (orderOf g)}
    have hle : Q'' ≤ Q := (Subgroup.closure_le Q).2 (fun g hg => hg.1)
    have hmem : Q'' ∈ S := by
      refine ⟨hle.trans hQ1, normal_of_normIn (hle.trans hQ1) ?_, ?_⟩
      · intro k hk q hq
        have h1 : Q''.map (MulAut.conj k).toMonoidHom ≤ Q'' := by
          rw [MonoidHom.map_closure]
          apply Subgroup.closure_mono
          rintro _ ⟨g, ⟨hgQ, hgo⟩, rfl⟩
          refine ⟨hconj k hk ⟨g, hgQ, rfl⟩, ?_⟩
          rwa [orderOf_injective (MulAut.conj k).toMonoidHom (MulAut.conj k).injective g]
        exact h1 ⟨q, hq, rfl⟩
      · apply le_antisymm
        · rw [← hQ3]; exact Subgroup.map_mono hle
        · rw [← hoddH]
          refine (Subgroup.closure_le _).2 ?_
          rintro z ⟨hzH, hzo⟩
          rw [← hQ3] at hzH
          obtain ⟨q, hq, rfl⟩ := hzH
          obtain ⟨k, hk1, hk2⟩ := exists_pow_odd_order π q hzo
          exact ⟨q ^ k, Subgroup.subset_closure ⟨Q.pow_mem hq k, hk1⟩, hk2⟩
    have hge : Q ≤ Q'' := hmin _ hmem hle
    show Subgroup.closure {g : Y | g ∈ Q ∧ Odd (orderOf g)} = Q
    exact le_antisymm hle hge
  · intro g hg ⟨k, hk⟩
    have hπg : π g ∈ H := hH ▸ Subgroup.mem_map_of_mem π hg
    rw [← hQ3] at hπg
    obtain ⟨q, hq, hqg⟩ := hπg
    have hn1 : π (g⁻¹ * q) = 1 := by rw [map_mul, map_inv, hqg, inv_mul_cancel]
    have hnodd := hodd _ hn1
    have := hQ2
    let mkH : ↥H₁ →* ↥H₁ ⧸ Q.subgroupOf H₁ := QuotientGroup.mk' _
    let g' : ↥H₁ := ⟨g, hg⟩
    let n' : ↥H₁ := ⟨g⁻¹ * q, H₁.mul_mem (H₁.inv_mem hg) (hQ1 hq)⟩
    have hq1 : mkH ⟨q, hQ1 hq⟩ = 1 := (QuotientGroup.eq_one_iff _).2 (by
      rw [Subgroup.mem_subgroupOf]; exact hq)
    have h1 : mkH g' ^ (2 ^ k) = 1 := by
      rw [← map_pow]
      have : g' ^ (2 ^ k) = 1 := Subtype.ext (by simpa using hk)
      rw [this, map_one]
    have h2 : mkH n' = (mkH g')⁻¹ := by
      have : n' = g'⁻¹ * ⟨q, hQ1 hq⟩ := rfl
      rw [this, map_mul, map_inv, hq1, mul_one]
    have hd1 : orderOf (mkH g') ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one h1
    have hd2 : orderOf (mkH g') ∣ orderOf (g⁻¹ * q) := by
      rw [← orderOf_inv, ← h2]
      have h3 := orderOf_map_dvd mkH n'
      rwa [Subgroup.orderOf_mk] at h3
    have hodd2 : Odd (orderOf (mkH g')) := Odd.of_dvd_nat hnodd hd2
    obtain ⟨i, -, hi⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hd1
    have hi0 : i = 0 := by
      by_contra hne
      rw [hi] at hodd2
      exact (Nat.not_even_iff_odd.2 hodd2) (by
        exact (Nat.even_pow.2 ⟨even_two, hne⟩))
    rw [hi0, pow_zero, orderOf_eq_one_iff] at hi
    have := (QuotientGroup.eq_one_iff g').1 hi
    rwa [Subgroup.mem_subgroupOf] at this

theorem goodSub_map {T : Prop} {Y Z : Type*} [Group Y] [Group Z] (f : Y →* Z) {Q : Subgroup Y}
    (hQ : GoodSub T Q) : GoodSub T (Q.map f) := by
  rcases hQ with h | ⟨h, hT⟩
  · left
    rw [← Subgroup.map_commutator, h]
  · right
    refine ⟨?_, hT⟩
    unfold OddGenerated at h ⊢
    apply le_antisymm
    · exact (Subgroup.closure_le _).2 (fun g hg => hg.1)
    · calc Q.map f = (Subgroup.closure {g : Y | g ∈ Q ∧ Odd (orderOf g)}).map f := by rw [h]
        _ = Subgroup.closure (f '' {g : Y | g ∈ Q ∧ Odd (orderOf g)}) := MonoidHom.map_closure _ _
        _ ≤ _ := by
          apply Subgroup.closure_mono
          rintro _ ⟨g, ⟨hgQ, hgo⟩, rfl⟩
          exact ⟨Subgroup.mem_map_of_mem f hgQ, Odd.of_dvd_nat hgo (orderOf_map_dvd f g)⟩

theorem transfer_good {Cc X : Type*} [Group Cc] [Finite Cc] [Group X] (π : Cc →* X)
    (hodd : ∀ n : Cc, π n = 1 → Odd (orderOf n))
    (u : Cc) (hcent : ∀ z : X, z * π u = π u * z → ∃ g : Cc, g * u = u * g ∧ π g = z)
    (Ψ : ↥(Subgroup.centralizer ({u} : Set Cc)) →* X) (T : Prop) (K : Subgroup X)
    (hSch : ∀ P : Subgroup X, GoodSub T P → P ≤ K)
    (H : Subgroup X) (hH : GoodSub T H) (hHc : ∀ h ∈ H, h * π u = π u * h) :
    ∀ g : ↥(Subgroup.centralizer ({u} : Set Cc)), π g ∈ H → (∃ k : ℕ, (g : Cc) ^ (2 ^ k) = 1) →
      Ψ g ∈ K := by
  classical
  let πD : ↥(Subgroup.centralizer ({u} : Set Cc)) →* X :=
    π.comp (Subgroup.centralizer ({u} : Set Cc)).subtype
  have hoddD : ∀ n : ↥(Subgroup.centralizer ({u} : Set Cc)), πD n = 1 → Odd (orderOf n) := by
    intro n hn
    have := hodd (n : Cc) hn
    rwa [← Subgroup.orderOf_coe]
  have hrange : H ≤ πD.range := by
    intro h hh
    obtain ⟨g, hg, hgh⟩ := hcent h (hHc h hh)
    exact ⟨⟨g, by rw [Subgroup.mem_centralizer_singleton_iff]; exact hg⟩, hgh⟩
  have hmap : (H.comap πD).map πD = H := by
    rw [Subgroup.map_comap_eq]
    exact inf_eq_right.2 hrange
  obtain ⟨Q, hQ1, hQ2, hQ3, hQ4, hQ5, hQ6⟩ := exists_hull πD hoddD (H.comap πD) H hmap
  have hgoodQ : GoodSub T Q := by
    rcases hH with h | ⟨h, hT⟩
    · exact Or.inl (hQ4 h)
    · exact Or.inr ⟨hQ5 h, hT⟩
  have hR : (Q.map Ψ) ≤ K := hSch _ (goodSub_map Ψ hgoodQ)
  intro g hg hg2
  have : g ∈ Q := hQ6 g hg (by
    obtain ⟨k, hk⟩ := hg2
    exact ⟨k, Subtype.ext (by simpa using hk)⟩)
  exact hR (Subgroup.mem_map_of_mem Ψ this)

section Proj

variable {G : Type} [Group G]

@[expose] noncomputable def proj (x : G) :
    ↥(centralizer ({x} : Set G)) →* CentralizerBar x :=
  QuotientGroup.mk' _

theorem proj_apply (x : G) (g : ↥(centralizer ({x} : Set G))) :
    proj x g = (QuotientGroup.mk g : CentralizerBar x) := rfl

theorem proj_mk (x : G) {u : G} (hu : u ∈ centralizer ({x} : Set G)) :
    proj x ⟨u, hu⟩ = barOf hu := rfl

theorem proj_odd [Finite G] (x : G) (n : ↥(centralizer ({x} : Set G))) (hn : proj x n = 1) :
    Odd (orderOf n) := by
  have hmem : n ∈ pPrimeCore 2 ↥(centralizer ({x} : Set G)) :=
    (QuotientGroup.eq_one_iff n).1 hn
  have hdvd : orderOf n ∣ Nat.card (pPrimeCore 2 ↥(centralizer ({x} : Set G))) :=
    Subgroup.orderOf_dvd_natCard _ hmem
  have hcop : Nat.Coprime 2 (Nat.card (pPrimeCore 2 ↥(centralizer ({x} : Set G)))) :=
    pPrimeCore_coprime_card
  exact Nat.coprime_two_left.1 (hcop.coprime_dvd_right hdvd)

theorem proj_cent [Finite G] (x : G) {u : ↥(centralizer ({x} : Set G))} (hu2 : u * u = 1)
    (z : CentralizerBar x) (hz : z * proj x u = proj x u * z) :
    ∃ g : ↥(centralizer ({x} : Set G)), g * u = u * g ∧ proj x g = z := by
  classical
  have hfact : Fact (IsPGroup 2 ↥(zpowers u)) :=
    ⟨isPGroup_zpowers_of_pow_two_pow_eq_one (n := 1) (by simpa [pow_two] using hu2)⟩
  have hOn : (pPrimeCore 2 ↥(centralizer ({x} : Set G))).Normal := pPrimeCore_normal
  have hOcop : Nat.Coprime 2 (Nat.card (pPrimeCore 2 ↥(centralizer ({x} : Set G)))) :=
    pPrimeCore_coprime_card
  have hcen : centralizer (((zpowers u).map (proj x) :
        Subgroup (CentralizerBar x)) : Set (CentralizerBar x)) =
      (centralizer ((zpowers u : Subgroup ↥(centralizer ({x} : Set G))) :
        Set ↥(centralizer ({x} : Set G)))).map (proj x) :=
    centralizer_map_quotient_eq_map_centralizer 2 (zpowers u)
      (pPrimeCore 2 ↥(centralizer ({x} : Set G))) hOn hOcop
  have hmapz : (zpowers u).map (proj x) = zpowers (proj x u) := MonoidHom.map_zpowers _ u
  rw [hmapz] at hcen
  have hcenv : centralizer ({proj x u} : Set (CentralizerBar x)) =
      (centralizer ({u} : Set ↥(centralizer ({x} : Set G)))).map (proj x) := by
    have h1 : centralizer ((zpowers (proj x u) : Subgroup (CentralizerBar x)) :
        Set (CentralizerBar x)) = centralizer ({proj x u} : Set (CentralizerBar x)) := by
      rw [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]
    have h2 : centralizer ((zpowers u : Subgroup ↥(centralizer ({x} : Set G))) :
        Set ↥(centralizer ({x} : Set G))) =
        centralizer ({u} : Set ↥(centralizer ({x} : Set G))) := by
      rw [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]
    rw [← h1, hcen, h2]
  have hz' : z ∈ centralizer ({proj x u} : Set (CentralizerBar x)) :=
    Subgroup.mem_centralizer_singleton_iff.2 hz
  rw [hcenv] at hz'
  obtain ⟨g, hg, hgz⟩ := hz'
  exact ⟨g, Subgroup.mem_centralizer_singleton_iff.1 hg, hgz⟩

abbrev CU (x : G) (U : ↥(centralizer ({x} : Set G))) :
    Subgroup ↥(centralizer ({x} : Set G)) :=
  centralizer ({U} : Set ↥(centralizer ({x} : Set G)))

@[expose] def transportC (x : G) (U : ↥(centralizer ({x} : Set G))) {c : G}
    (hc : c⁻¹ * (U : G) * c = x) : ↥(CU x U) →* ↥(centralizer ({x} : Set G)) :=
  MonoidHom.mk' (fun g => (⟨c⁻¹ * ((g : ↥(centralizer ({x} : Set G))) : G) * c,
      Subgroup.mem_centralizer_singleton_iff.2 (by
        have hg : (g : ↥(centralizer ({x} : Set G))) * U =
            U * (g : ↥(centralizer ({x} : Set G))) :=
          Subgroup.mem_centralizer_singleton_iff.1 g.2
        have hg' : ((g : ↥(centralizer ({x} : Set G))) : G) * (U : G) =
            (U : G) * ((g : ↥(centralizer ({x} : Set G))) : G) := congrArg Subtype.val hg
        have key : c⁻¹ * ((g : ↥(centralizer ({x} : Set G))) : G) * c * (c⁻¹ * (U : G) * c) =
            c⁻¹ * (U : G) * c * (c⁻¹ * ((g : ↥(centralizer ({x} : Set G))) : G) * c) := by
          calc c⁻¹ * ((g : ↥(centralizer ({x} : Set G))) : G) * c * (c⁻¹ * (U : G) * c)
              = c⁻¹ * (((g : ↥(centralizer ({x} : Set G))) : G) * (U : G)) * c := by group
            _ = c⁻¹ * ((U : G) * ((g : ↥(centralizer ({x} : Set G))) : G)) * c := by rw [hg']
            _ = c⁻¹ * (U : G) * c * (c⁻¹ * ((g : ↥(centralizer ({x} : Set G))) : G) * c) := by
              group
        rw [hc] at key
        exact key)⟩ : ↥(centralizer ({x} : Set G))))
    (by
      intro a b
      apply Subtype.ext
      change c⁻¹ * (((a : ↥(centralizer ({x} : Set G))) : G) *
        ((b : ↥(centralizer ({x} : Set G))) : G)) * c = _
      change _ = c⁻¹ * ((a : ↥(centralizer ({x} : Set G))) : G) * c *
        (c⁻¹ * ((b : ↥(centralizer ({x} : Set G))) : G) * c)
      group)

theorem transportC_val (x : G) (U : ↥(centralizer ({x} : Set G))) {c : G}
    (hc : c⁻¹ * (U : G) * c = x) (g : ↥(CU x U)) :
    ((transportC x U hc g : ↥(centralizer ({x} : Set G))) : G) =
      c⁻¹ * ((g : ↥(centralizer ({x} : Set G))) : G) * c := rfl

theorem transportC_injective (x : G) (U : ↥(centralizer ({x} : Set G))) {c : G}
    (hc : c⁻¹ * (U : G) * c = x) : Function.Injective (transportC x U hc) := by
  intro a b hab
  have h := congrArg (fun z : ↥(centralizer ({x} : Set G)) => (z : G)) hab
  simp only [transportC_val] at h
  have h' : ((a : ↥(centralizer ({x} : Set G))) : G) = ((b : ↥(centralizer ({x} : Set G))) : G) := by
    simpa using h
  exact Subtype.ext (Subtype.ext h')

@[expose] noncomputable def transportHom (x : G) (U : ↥(centralizer ({x} : Set G))) {c : G}
    (hc : c⁻¹ * (U : G) * c = x) : ↥(CU x U) →* CentralizerBar x :=
  (proj x).comp (transportC x U hc)

theorem transfer_bar [Finite G] (x : G) (U : ↥(centralizer ({x} : Set G))) (hU2 : U * U = 1)
    {c : G} (hc : c⁻¹ * (U : G) * c = x) (T : Prop) (K : Subgroup (CentralizerBar x))
    (hSch : ∀ P : Subgroup (CentralizerBar x), GoodSub T P → P ≤ K)
    (H : Subgroup (CentralizerBar x)) (hH : GoodSub T H)
    (hHc : ∀ h ∈ H, h * proj x U = proj x U * h) :
    ∀ g : ↥(CU x U), proj x (g : ↥(centralizer ({x} : Set G))) ∈ H →
      (∃ k : ℕ, (g : ↥(centralizer ({x} : Set G))) ^ (2 ^ k) = 1) →
        transportHom x U hc g ∈ K := by
  refine transfer_good (proj x) (proj_odd x) U ?_ (transportHom x U hc) T K hSch H hH hHc
  intro z hz
  exact proj_cent x hU2 z hz

end Proj

end CFSG.GH74.Generic
