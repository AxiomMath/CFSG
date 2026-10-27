module

public import CFSG.GH74.GLS.Stage4.T2P56LayerDefs

public section

namespace CFSG.GH74.GLS.Stage4.Rest

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.IVK CFSG.Assembly.LowTwoRank

section Generic

theorem eq_one_of_mem_of_odd {X : Type} [Group X] {N : Subgroup X} (hN : Odd (Nat.card N))
    {S : Subgroup X} (hS : IsPGroup 2 S) {x : X} (hxS : x ∈ S) (hxN : x ∈ N) : x = 1 := by
  have h1 : orderOf x ∣ Nat.card N := Subgroup.orderOf_dvd_natCard N hxN
  obtain ⟨k, hk⟩ := hS ⟨x, hxS⟩
  have h2 : orderOf (⟨x, hxS⟩ : S) ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one hk
  rw [Subgroup.orderOf_mk] at h2
  obtain ⟨i, -, hi⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 h2
  rcases Nat.eq_zero_or_pos i with rfl | hi0
  · exact orderOf_eq_one_iff.1 (by simpa using hi)
  · exfalso
    have h4 : 2 ∣ orderOf x := by
      rw [hi]
      exact dvd_pow_self 2 hi0.ne'
    exact (Nat.not_even_iff_odd.2 hN) (even_iff_two_dvd.2 (h4.trans h1))

noncomputable def sdwEquivMapOfInjOn {A B : Type*} [Group A] [Group B] (f : A →* B) (W : Subgroup A)
    (h : Set.InjOn f (W : Set A)) : W ≃* W.map f :=
  (MonoidHom.ofInjective (f := f.domRestrict W) (fun x y hxy => Subtype.ext (h x.2 y.2 hxy))).trans
    (MulEquiv.subgroupCongr (by rw [MonoidHom.domRestrict_range]))

theorem sylow_two_nonempty_mulEquiv {Y : Type} [Group Y] [Finite Y] (S₁ S₂ : Sylow 2 Y) :
    Nonempty (↥(S₁ : Subgroup Y) ≃* ↥(S₂ : Subgroup Y)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq Y S₁ S₂
  exact ⟨(S₁.equivSMul g).trans (MulEquiv.subgroupCongr (congrArg Sylow.toSubgroup hg))⟩

theorem hasSylowIso_quotient_iff {X : Type} [Group X] [Finite X] (N : Subgroup X) [N.Normal]
    (hN : Odd (Nat.card N)) (T : Type) [Group T] :
    (∃ S : Sylow 2 X, Nonempty (↥(S : Subgroup X) ≃* T)) ↔
      ∃ S : Sylow 2 (X ⧸ N), Nonempty (↥(S : Subgroup (X ⧸ N)) ≃* T) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hsurj : Function.Surjective (QuotientGroup.mk' N) := QuotientGroup.mk'_surjective N
  have key : ∀ S : Sylow 2 X, Nonempty (↥(S : Subgroup X) ≃*
      ↥((S.mapSurjective hsurj : Sylow 2 (X ⧸ N)) : Subgroup (X ⧸ N))) := by
    intro S
    have hinj : Set.InjOn (QuotientGroup.mk' N) (S : Set X) := by
      intro x hx y hy hxy
      have h1 : x⁻¹ * y ∈ N := QuotientGroup.eq.1 hxy
      have h2 : x⁻¹ * y ∈ (S : Subgroup X) := (S : Subgroup X).mul_mem ((S : Subgroup X).inv_mem hx) hy
      have := eq_one_of_mem_of_odd hN S.isPGroup' h2 h1
      exact inv_mul_eq_one.1 this
    rw [Sylow.coe_mapSurjective]
    exact ⟨sdwEquivMapOfInjOn _ _ hinj⟩
  constructor
  · rintro ⟨S, ⟨e⟩⟩
    obtain ⟨e'⟩ := key S
    exact ⟨S.mapSurjective hsurj, ⟨e'.symm.trans e⟩⟩
  · rintro ⟨S', ⟨e⟩⟩
    obtain ⟨S⟩ : Nonempty (Sylow 2 X) := inferInstance
    obtain ⟨e₁⟩ := key S
    obtain ⟨e₂⟩ := sylow_two_nonempty_mulEquiv (S.mapSurjective hsurj) S'
    exact ⟨S, ⟨e₁.trans (e₂.trans e)⟩⟩

theorem hasSDOrWreathedSylow_quotient_iff {X : Type} [Group X] [Finite X] (N : Subgroup X) [N.Normal]
    (hN : Odd (Nat.card N)) :
    HasSDOrWreathedSylow X ↔ HasSDOrWreathedSylow (X ⧸ N) := by
  constructor
  · rintro ⟨S, ⟨m, hm, h⟩ | ⟨m, hm, h⟩⟩
    · obtain ⟨S', h'⟩ := (hasSylowIso_quotient_iff N hN (CFSG.Open.SemidihedralGroup m)).1 ⟨S, h⟩
      exact ⟨S', Or.inl ⟨m, hm, h'⟩⟩
    · obtain ⟨S', h'⟩ := (hasSylowIso_quotient_iff N hN (CFSG.Open.WreathedTwoGroup m)).1 ⟨S, h⟩
      exact ⟨S', Or.inr ⟨m, hm, h'⟩⟩
  · rintro ⟨S, ⟨m, hm, h⟩ | ⟨m, hm, h⟩⟩
    · obtain ⟨S', h'⟩ := (hasSylowIso_quotient_iff N hN (CFSG.Open.SemidihedralGroup m)).2 ⟨S, h⟩
      exact ⟨S', Or.inl ⟨m, hm, h'⟩⟩
    · obtain ⟨S', h'⟩ := (hasSylowIso_quotient_iff N hN (CFSG.Open.WreathedTwoGroup m)).2 ⟨S, h⟩
      exact ⟨S', Or.inr ⟨m, hm, h'⟩⟩

theorem exists_mem_centralizer_of_comm_mod {X : Type} [Group X] (N : Subgroup X) [N.Normal]
    (hN : Odd (Nat.card N)) {z : X} (hz : z * z = 1) {c : X} (hc : c * z * c⁻¹ * z⁻¹ ∈ N) :
    ∃ n ∈ N, n * c * z = z * (n * c) := by
  set m : X := c * z * c⁻¹ * z⁻¹ with hm
  have hz' : z⁻¹ = z := inv_eq_of_mul_eq_one_right hz
  have hw : c * z * c⁻¹ = m * z := by
    calc c * z * c⁻¹ = (c * z * c⁻¹ * z⁻¹) * z := by group
      _ = m * z := by rw [← hm]
  have hw2 : (m * z) * (m * z) = 1 := by
    rw [← hw]
    calc c * z * c⁻¹ * (c * z * c⁻¹) = c * (z * z) * c⁻¹ := by group
      _ = 1 := by rw [hz]; group
  have hinv : z * m * z = m⁻¹ := by
    have : m * (z * m * z) = 1 := by
      calc m * (z * m * z) = (m * z) * (m * z) := by group
        _ = 1 := hw2
    exact eq_inv_of_mul_eq_one_right this
  have hmN : m ∈ N := hc
  have hodd : Odd (orderOf m) :=
    Odd.of_dvd_nat hN (Subgroup.orderOf_dvd_natCard N hmN)
  obtain ⟨k, hk⟩ := hodd
  have hmk : m ^ (2 * k + 1) = 1 := by rw [← hk]; exact pow_orderOf_eq_one m
  set n₀ : X := m ^ (k + 1) with hn₀
  have hzn : z * n₀ * z = (m⁻¹) ^ (k + 1) := by
    have : z * n₀ * z = (z * m * z) ^ (k + 1) := by
      rw [hn₀]
      calc z * m ^ (k + 1) * z = z * m ^ (k + 1) * z⁻¹ := by rw [hz']
        _ = (z * m * z⁻¹) ^ (k + 1) := by rw [conj_pow]
        _ = (z * m * z) ^ (k + 1) := by rw [hz']
    rw [this, hinv]
  have hconj : n₀ * z * n₀⁻¹ = m * z := by
    have h1 : n₀ * z * n₀⁻¹ = n₀ * (z * n₀ * z)⁻¹ * z := by
      calc n₀ * z * n₀⁻¹ = n₀ * (z * n₀⁻¹ * z) * z := by
            calc n₀ * z * n₀⁻¹ = n₀ * (z * n₀⁻¹ * z⁻¹) * z := by group
              _ = n₀ * (z * n₀⁻¹ * z) * z := by rw [hz']
        _ = n₀ * (z * n₀ * z)⁻¹ * z := by
            congr 2
            rw [mul_inv_rev, mul_inv_rev, hz']
            group
    rw [h1, hzn, inv_pow, inv_inv, hn₀, ← pow_add]
    have : (k + 1 + (k + 1)) = 2 * k + 1 + 1 := by ring
    rw [this, pow_succ, hmk, one_mul]
  refine ⟨n₀⁻¹, N.inv_mem (N.pow_mem hmN _), ?_⟩
  calc n₀⁻¹ * c * z = n₀⁻¹ * (c * z * c⁻¹) * c := by group
    _ = n₀⁻¹ * (m * z) * c := by rw [hw]
    _ = n₀⁻¹ * (n₀ * z * n₀⁻¹) * c := by rw [hconj]
    _ = z * (n₀⁻¹ * c) := by group

theorem pPrimeCore_quotient_eq_bot' {X : Type} [Group X] [Finite X] :
    pPrimeCore 2 (X ⧸ pPrimeCore 2 X) = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set N : Subgroup X := pPrimeCore 2 X with hN
  have hNn : N.Normal := pPrimeCore_normal
  have hNodd : Odd (Nat.card N) := by
    have hcop := pPrimeCore_coprime_card (p := 2) (G := X)
    rwa [Nat.coprime_two_left] at hcop
  rw [pPrimeCore_eq_bot_iff]
  intro K hKn hKc
  have hKodd : Odd (Nat.card K) := by rwa [Nat.coprime_two_left] at hKc
  set M : Subgroup X := K.comap (QuotientGroup.mk' N) with hM
  have hMn : M.Normal := hKn.comap _
  have hModd : Nat.Coprime 2 (Nat.card M) := by
    by_contra hnc
    have h2 : 2 ∣ Nat.card M := by
      by_contra h2
      exact hnc ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).2 h2)
    obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := M) 2 h2
    have hxx : (x : X) ^ 2 = 1 := by
      have := pow_orderOf_eq_one x
      rw [hx] at this
      exact congrArg Subtype.val this
    have hx1 : (x : X) ≠ 1 := by
      intro h1
      have : x = 1 := Subtype.ext h1
      rw [this, orderOf_one] at hx
      omega
    have hπ : (QuotientGroup.mk' N) (x : X) ∈ K := x.2
    have hπ2 : ((QuotientGroup.mk' N) (x : X)) ^ 2 = 1 := by rw [← map_pow, hxx, map_one]
    have hπ1 : (QuotientGroup.mk' N) (x : X) = 1 := by
      have hK2 : orderOf (⟨(QuotientGroup.mk' N) (x : X), hπ⟩ : K) ∣ 2 :=
        orderOf_dvd_of_pow_eq_one (Subtype.ext hπ2)
      have hK3 : orderOf (⟨(QuotientGroup.mk' N) (x : X), hπ⟩ : K) ∣ Nat.card K :=
        orderOf_dvd_natCard _
      have hK4 : orderOf (⟨(QuotientGroup.mk' N) (x : X), hπ⟩ : K) = 1 := by
        rcases (Nat.dvd_prime Nat.prime_two).1 hK2 with h | h
        · exact h
        · exfalso
          rw [h] at hK3
          exact (Nat.not_even_iff_odd.2 hKodd) (even_iff_two_dvd.2 hK3)
      have := orderOf_eq_one_iff.1 hK4
      exact congrArg Subtype.val this
    have hxN : (x : X) ∈ N := by
      rw [← QuotientGroup.ker_mk' N, MonoidHom.mem_ker]; exact hπ1
    have h1 := Subgroup.orderOf_dvd_natCard N hxN
    have h2' : orderOf (x : X) = 2 := by rw [Subgroup.orderOf_coe]; exact hx
    rw [h2'] at h1
    exact (Nat.not_even_iff_odd.2 hNodd) (even_iff_two_dvd.2 h1)
  have hMle : M ≤ N := by
    rw [hN]
    exact le_sSup ⟨hMn, hModd⟩
  rw [Subgroup.eq_bot_iff_forall]
  intro k hk
  obtain ⟨x, hx⟩ := QuotientGroup.mk'_surjective N k
  have hxM : x ∈ M := by rw [hM, Subgroup.mem_comap, hx]; exact hk
  have := hMle hxM
  rw [← hx, ← QuotientGroup.ker_mk' N] at *
  simpa [MonoidHom.mem_ker] using this

theorem eq_one_of_sq_eq_one_of_odd {X : Type} [Group X] {N : Subgroup X} (hN : Odd (Nat.card N))
    {x : X} (hxN : x ∈ N) (hx : x * x = 1) : x = 1 := by
  have h1 : orderOf x ∣ Nat.card N := Subgroup.orderOf_dvd_natCard N hxN
  have h2 : orderOf x ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact hx)
  rcases (Nat.dvd_prime Nat.prime_two).1 h2 with h | h
  · exact orderOf_eq_one_iff.1 h
  · exfalso
    rw [h] at h1
    exact (Nat.not_even_iff_odd.2 hN) (even_iff_two_dvd.2 h1)

end Generic

section SL2

theorem pPrimeCore_eq_bot_of_hasSL2Model {K : Type} [Group K] {P : ℕ → Prop}
    (hP : ∀ q, P q → Odd q ∧ 3 ≤ q) (hK : HasSL2Model K P) : pPrimeCore 2 K = ⊥ := by
  obtain ⟨F, _, _, hF, ⟨e₀⟩⟩ := hK
  obtain ⟨hodd, h3⟩ := hP _ hF
  let e : K ≃* Matrix.SpecialLinearGroup (Fin 2) F := e₀.trans (specialLinearGroupEquivStatedSL 2 F).symm
  have hcore : pPrimeCore 2 (Matrix.SpecialLinearGroup (Fin 2) F) = ⊥ := by
    rcases Nat.eq_or_lt_of_le h3 with h | h
    · exact IVK.Lifted.pPrimeCore_two_sl2_three (K := F) h.symm
    · have h4 : Nat.card F ≠ 4 := by
        rintro h4
        rw [h4] at hodd
        exact absurd hodd (by decide)
      exact IVK.Lifted.pPrimeCore_two_sl2_five hodd (by omega)
  rw [pPrimeCore_eq_bot_iff]
  intro N hN hcop
  have hN' : (N.map e.toMonoidHom).Normal := Subgroup.Normal.map hN _ e.surjective
  have hcard : Nat.card ↥(N.map e.toMonoidHom) = Nat.card ↥N :=
    Subgroup.card_map_of_injective e.injective
  have h0 := (pPrimeCore_eq_bot_iff).1 hcore (N.map e.toMonoidHom) hN' (by rw [hcard]; exact hcop)
  exact (Subgroup.map_eq_bot_iff_of_injective N e.injective).1 h0

theorem eq_one_of_mem_inf_of_sl2 {X : Type} [Group X] (N : Subgroup X) [N.Normal] (hN : Odd (Nat.card N))
    {K : Subgroup X} {P : ℕ → Prop} (hP : ∀ q, P q → Odd q ∧ 3 ≤ q) (hK : HasSL2Model ↥K P)
    {k : X} (hkK : k ∈ K) (hkN : k ∈ N) : k = 1 := by
  have hbot := pPrimeCore_eq_bot_of_hasSL2Model hP hK
  rw [pPrimeCore_eq_bot_iff] at hbot
  set M : Subgroup ↥K := N.subgroupOf K with hM
  have hMn : M.Normal := inferInstance
  have hMcop : Nat.Coprime 2 (Nat.card M) := by
    rw [Nat.coprime_two_left]
    let g : ↥M →* ↥N := ((K.subtype).comp M.subtype).codRestrict N (fun x => x.2)
    have hg : Function.Injective g := by
      intro x y hxy
      apply Subtype.ext
      apply Subtype.ext
      have := congrArg Subtype.val hxy
      exact this
    exact Odd.of_dvd_nat hN (Subgroup.card_dvd_of_injective g hg)
  have h1 := hbot M hMn hMcop
  have hk : (⟨k, hkK⟩ : ↥K) ∈ M := by
    rw [hM, Subgroup.mem_subgroupOf]
    exact hkN
  rw [h1, Subgroup.mem_bot] at hk
  exact congrArg Subtype.val hk

end SL2

theorem layer_of_quotient (hL : SDWreathedLayer) {X : Type} [Group X] [Finite X] (hX : IsKGroupNative X)
    (hS : HasSDOrWreathedSylow X) {p n : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hq : 3 ≤ p ^ n)
    {z : X} (hz : orderOf z = 2) {K : Subgroup X} (hzK : z ∈ K)
    (hK : HasSL2Model ↥K (fun q => q = p ^ n))
    (hCK : ∀ c : X, c * z = z * c → ∀ k ∈ K, c * k * c⁻¹ ∈ K)
    (hfus : ∃ a : X, a * z * a⁻¹ ≠ z ∧ (a * z * a⁻¹) * z = z * (a * z * a⁻¹)) :
    ∃ E : Subgroup (X ⧸ pPrimeCore 2 X), E.Normal ∧
      K.map (QuotientGroup.mk' (pPrimeCore 2 X)) ≤ E ∧ Odd E.index ∧
      ((∃ ε : ℤ, (ε = 1 ∨ ε = -1) ∧ IsLnEps 3 ↥E ε (p ^ n)) ∨
        (p ^ n = 3 ∧ Nonempty (↥E ≃* CFSG.Open.StatedM11))) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set N : Subgroup X := pPrimeCore 2 X with hN
  have hNn : N.Normal := pPrimeCore_normal
  have hNodd : Odd (Nat.card N) := by
    have hcop := pPrimeCore_coprime_card (p := 2) (G := X)
    rwa [Nat.coprime_two_left] at hcop
  have hpodd : Odd (p ^ n) := (hp.odd_of_ne_two hp2).pow
  have hP : ∀ q, q = p ^ n → Odd q ∧ 3 ≤ q := fun q hq' => by rw [hq']; exact ⟨hpodd, hq⟩
  have hX' : IsKGroupNative (X ⧸ N) := SectionRank.IsKGroupCat.quotient hX N
  have hbot : pPrimeCore 2 (X ⧸ N) = ⊥ := pPrimeCore_quotient_eq_bot'
  have hS' : HasSDOrWreathedSylow (X ⧸ N) := (hasSDOrWreathedSylow_quotient_iff N hNodd).1 hS
  have hzz : z * z = 1 := by
    rw [← pow_two]
    conv_lhs => rw [← hz]
    exact pow_orderOf_eq_one z
  have hzN : z ∉ N := by
    intro hzN
    have := eq_one_of_sq_eq_one_of_odd hNodd hzN hzz
    rw [this, orderOf_one] at hz
    omega
  have hπz : QuotientGroup.mk' N z ≠ 1 := by
    intro h
    apply hzN
    rw [← QuotientGroup.ker_mk' N, MonoidHom.mem_ker]
    exact h
  have hz' : orderOf (QuotientGroup.mk' N z) = 2 :=
    orderOf_eq_prime (by rw [← map_pow, ← hz, pow_orderOf_eq_one, map_one]) hπz
  have hinj : Set.InjOn (QuotientGroup.mk' N) (K : Set X) := by
    intro x hx y hy hxy
    have h1 : x⁻¹ * y ∈ N := QuotientGroup.eq.1 hxy
    have h2 : x⁻¹ * y ∈ K := K.mul_mem (K.inv_mem hx) hy
    exact inv_mul_eq_one.1 (eq_one_of_mem_inf_of_sl2 N hNodd hP hK h2 h1)
  have hK' : HasSL2Model ↥(K.map (QuotientGroup.mk' N)) (fun q => q = p ^ n) := by
    obtain ⟨F, iF, iFin, hF, ⟨e⟩⟩ := hK
    exact ⟨F, iF, iFin, hF, ⟨(sdwEquivMapOfInjOn (QuotientGroup.mk' N) K hinj).symm.trans e⟩⟩
  have hCK' : ∀ c' : X ⧸ N, c' * QuotientGroup.mk' N z = QuotientGroup.mk' N z * c' →
      ∀ k' ∈ K.map (QuotientGroup.mk' N), c' * k' * c'⁻¹ ∈ K.map (QuotientGroup.mk' N) := by
    intro c' hc k' hk'
    obtain ⟨c, rfl⟩ := QuotientGroup.mk'_surjective N c'
    obtain ⟨k, hkK, rfl⟩ := hk'
    have hcz : c * z * c⁻¹ * z⁻¹ ∈ N := by
      rw [← QuotientGroup.ker_mk' N, MonoidHom.mem_ker]
      have h1 : QuotientGroup.mk' N c * QuotientGroup.mk' N z = QuotientGroup.mk' N z * QuotientGroup.mk' N c :=
        hc
      simp only [map_mul, map_inv]
      rw [h1]
      group
    obtain ⟨m, hmN, hm⟩ := exists_mem_centralizer_of_comm_mod N hNodd hzz hcz
    have hmem := hCK (m * c) hm k hkK
    refine ⟨m * c * k * (m * c)⁻¹, hmem, ?_⟩
    have hm1 : QuotientGroup.mk' N m = 1 := by
      rw [← MonoidHom.mem_ker, QuotientGroup.ker_mk']; exact hmN
    simp only [map_mul, map_inv, hm1, one_mul]
  have hfus' : ∃ a' : X ⧸ N, a' * QuotientGroup.mk' N z * a'⁻¹ ≠ QuotientGroup.mk' N z ∧
      (a' * QuotientGroup.mk' N z * a'⁻¹) * QuotientGroup.mk' N z =
        QuotientGroup.mk' N z * (a' * QuotientGroup.mk' N z * a'⁻¹) := by
    obtain ⟨a, ha1, ha2⟩ := hfus
    refine ⟨QuotientGroup.mk' N a, ?_, ?_⟩
    · intro h
      apply ha1
      have h1 : QuotientGroup.mk' N (a * z * a⁻¹) = QuotientGroup.mk' N z := by
        simpa only [map_mul, map_inv] using h
      have h2 : (a * z * a⁻¹) * z⁻¹ ∈ N := by
        rw [← QuotientGroup.ker_mk' N, MonoidHom.mem_ker]
        simp only [map_mul, map_inv] at h1 ⊢
        rw [h1]; group
      have hz' : z⁻¹ = z := inv_eq_of_mul_eq_one_right hzz
      rw [hz'] at h2
      have h3 : ((a * z * a⁻¹) * z) * ((a * z * a⁻¹) * z) = 1 := by
        calc ((a * z * a⁻¹) * z) * ((a * z * a⁻¹) * z)
            = (a * z * a⁻¹) * (z * (a * z * a⁻¹)) * z := by group
          _ = (a * z * a⁻¹) * ((a * z * a⁻¹) * z) * z := by rw [ha2]
          _ = (a * z * a⁻¹ * (a * z * a⁻¹)) * (z * z) := by group
          _ = 1 := by
              have : a * z * a⁻¹ * (a * z * a⁻¹) = a * (z * z) * a⁻¹ := by group
              rw [this, hzz]; group
      have h4 := eq_one_of_sq_eq_one_of_odd hNodd h2 h3
      calc a * z * a⁻¹ = ((a * z * a⁻¹) * z) * z⁻¹ := by group
        _ = z⁻¹ := by rw [h4, one_mul]
        _ = z := hz'
    · simpa only [map_mul, map_inv] using congrArg (QuotientGroup.mk' N) ha2
  obtain ⟨E, hEn, hKE, hEi, hE⟩ := hL (X ⧸ N) hX' hbot hS' p n hp hp2 hq (QuotientGroup.mk' N z) hz'
    (K.map (QuotientGroup.mk' N)) ⟨z, hzK, rfl⟩ hK' hCK' hfus'
  exact ⟨E, hEn, hKE, hEi, hE⟩

end CFSG.GH74.GLS.Stage4.Rest
