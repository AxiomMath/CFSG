module

public import CFSG.LargeExtraspecial.AS35MKer

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial

open Subgroup Module CFSG.RankThree.OrthogonalInvolutions CQuotE

namespace AS35M

variable {G : Type} [Group G]

@[expose] noncomputable def oTwoSub (A : Subgroup G) : Subgroup G :=
  (CFSG.pCore 2 A).map A.subtype

theorem oTwoSub_le (A : Subgroup G) : oTwoSub A ≤ A := by
  rintro _ ⟨y, -, rfl⟩
  exact y.2

theorem isPGroup_oTwoSub (A : Subgroup G) : IsPGroup 2 (oTwoSub A) :=
  CFSG.pCore_isPGroup.map _

theorem conj_mem_oTwoSub_of_mem {A : Subgroup G} {a y : G} (ha : a ∈ A) (hy : y ∈ oTwoSub A) :
    a * y * a⁻¹ ∈ oTwoSub A := by
  obtain ⟨y', hy', rfl⟩ := hy
  exact ⟨⟨a, ha⟩ * y' * ⟨a, ha⟩⁻¹, CFSG.pCore_normal.conj_mem _ hy' _, rfl⟩

theorem le_oTwoSub {A P : Subgroup G} (hPA : P ≤ A)
    (hPn : ∀ a ∈ A, ∀ p ∈ P, a * p * a⁻¹ ∈ P) (hP2 : IsPGroup 2 P) : P ≤ oTwoSub A := by
  have hn : (P.subgroupOf A).Normal := ⟨fun n hn g => by
    rw [mem_subgroupOf] at hn ⊢
    exact hPn g g.2 n hn⟩
  have hle : P.subgroupOf A ≤ CFSG.pCore 2 A :=
    le_sSup ⟨hn, hP2.comap_of_injective A.subtype A.subtype_injective⟩
  intro y hy
  exact ⟨⟨y, hPA hy⟩, hle (by rwa [mem_subgroupOf]), rfl⟩

theorem conj_mem_oTwoSub {A : Subgroup G} {g : G} (hg : ∀ a ∈ A, g * a * g⁻¹ ∈ A)
    (hg' : ∀ a ∈ A, g⁻¹ * a * g ∈ A) {y : G} (hy : y ∈ oTwoSub A) :
    g * y * g⁻¹ ∈ oTwoSub A := by
  have hle : (oTwoSub A).map (MulAut.conj g).toMonoidHom ≤ oTwoSub A := by
    refine le_oTwoSub ?_ ?_ ((isPGroup_oTwoSub A).map _)
    · rintro _ ⟨w, hw, rfl⟩
      exact hg w (oTwoSub_le A hw)
    · rintro a ha _ ⟨w, hw, rfl⟩
      refine ⟨(g⁻¹ * a * g) * w * (g⁻¹ * a * g)⁻¹,
        conj_mem_oTwoSub_of_mem (hg' a ha) hw, ?_⟩
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      group
  exact hle ⟨y, hy, rfl⟩

omit [Group G] in
theorem isPGroup_zpowers_of_pow_two_pow {H : Type} [Group H] {g : H} {k : ℕ}
    (hg : g ^ (2 ^ k) = 1) : IsPGroup 2 (zpowers g) := by
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp (orderOf_dvd_of_pow_eq_one hg)
  exact IsPGroup.of_card (n := j) (by rw [Nat.card_zpowers, hj])

theorem mem_oTwoSub_of_central [Finite G] {P N : Subgroup G}
    (hNc : ∀ n ∈ N, ∀ p ∈ P, n * p = p * n) (h2 : ∀ p ∈ P, ∃ k : ℕ, p ^ (2 ^ k) ∈ N)
    {p : G} (hp : p ∈ P) {k : ℕ} (hpk : p ^ (2 ^ k) = 1) : p ∈ oTwoSub P := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set N' : Subgroup P := N.subgroupOf P with hN'
  have hN'c : N' ≤ center P := by
    intro n hn
    rw [mem_subgroupOf] at hn
    exact mem_center_iff.mpr fun q => Subtype.ext (hNc _ hn q q.2).symm
  have : N'.Normal := Subgroup.normal_of_le_center hN'c
  have hQ : IsPGroup 2 (P ⧸ N') := by
    intro q
    obtain ⟨q', rfl⟩ := QuotientGroup.mk'_surjective N' q
    obtain ⟨j, hj⟩ := h2 q' q'.2
    refine ⟨j, ?_⟩
    rw [← map_pow, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, hN', mem_subgroupOf]
    exact hj
  have := hQ.isNilpotent
  have hnil : Group.IsNilpotent P :=
    Subgroup.isNilpotent_of_ker_le_center (QuotientGroup.mk' N') (by
      rw [QuotientGroup.ker_mk']
      exact hN'c)
  obtain ⟨S₂, hS₂⟩ := (isPGroup_zpowers_of_pow_two_pow (g := (⟨p, hp⟩ : P))
    (Subtype.ext (by simpa using hpk))).exists_le_sylow
  have hS₂n := Group.IsNilpotent.sylow_normal hnil 2 S₂
  have hle : (S₂ : Subgroup P) ≤ CFSG.pCore 2 P := le_sSup ⟨hS₂n, S₂.isPGroup'⟩
  exact ⟨⟨p, hp⟩, hle (hS₂ (mem_zpowers _)), rfl⟩

theorem exists_pow_two_mul_eq_one {p n : G} {k : ℕ} (hpn : p ^ (2 ^ k) = n)
    (hn : Odd (orderOf n)) : ∃ s : ℕ, (p * (n ^ s)⁻¹) ^ (2 ^ k) = 1 := by
  have hcop : Nat.Coprime (2 ^ k) (orderOf n) := (Nat.coprime_two_left.mpr hn).pow_left k
  have hc : ∀ s : ℕ, Commute p (n ^ s)⁻¹ := fun s => by
    rw [← hpn]
    exact (((Commute.refl p).pow_right _).pow_right _).inv_right
  by_cases h1 : orderOf n = 1
  · refine ⟨0, ?_⟩
    rw [pow_zero, inv_one, mul_one, hpn]
    exact orderOf_eq_one_iff.mp h1
  · have h0 : orderOf n ≠ 0 := fun h => by rw [h] at hn; exact absurd hn (by decide)
    obtain ⟨s, -, hs⟩ := Nat.exists_mul_mod_eq_one_of_coprime hcop (by omega)
    refine ⟨s, ?_⟩
    rw [(hc s).mul_pow, hpn, inv_pow, ← pow_mul, mul_comm s, ← pow_mod_orderOf, hs, pow_one,
      mul_inv_cancel]

end AS35M

open AS35M

namespace Setting

variable {G : Type} [Group G] [Finite G] (S : Setting G)

theorem quotOTwoHypE_EOdd {x : G} (hxM : x ∈ S.M) (hx3 : orderOf x = 3)
    (hN2 : S.MbarOTwoHyp hxM) : S.QuotOTwoHypE (S.EOdd x : Set G) := by
  have hxo : Odd (orderOf x) := by rw [hx3]; decide
  have hE := S.descentSet_EOdd hxM hxo
  set A : Subgroup G := S.M ⊓ centralizer (S.EOdd x : Set G) with hA
  have hnorm : ∀ c ∈ S.M, c * x = x * c → ∀ a ∈ A, c * a * c⁻¹ ∈ A := by
    intro c hcM hcx a ha
    obtain ⟨haM, haE⟩ := mem_inf.mp ha
    have hcx' : c * x * c⁻¹ = x ∨ c * x * c⁻¹ = x⁻¹ := Or.inl (by rw [hcx]; group)
    refine mem_inf.mpr ⟨S.M.mul_mem (S.M.mul_mem hcM haM) (S.M.inv_mem hcM),
      conj_mem_Cx (fun e he => S.conj_inv_mem_EOdd hcM hcx' he) haE⟩
  have hnorm' : ∀ c ∈ S.M, c * x = x * c → ∀ a ∈ A, c⁻¹ * a * c ∈ A := by
    intro c hcM hcx a ha
    have hcx'' : c⁻¹ * x = x * c⁻¹ := by
      calc c⁻¹ * x = c⁻¹ * (x * c) * c⁻¹ := by group
        _ = c⁻¹ * (c * x) * c⁻¹ := by rw [hcx]
        _ = x * c⁻¹ := by group
    have := hnorm c⁻¹ (S.M.inv_mem hcM) hcx'' a ha
    rwa [inv_inv] at this
  have hOQ : oTwoSub A ≤ S.QG := by
    have hOM : oTwoSub A ≤ S.M := (oTwoSub_le A).trans inf_le_left
    set R : Subgroup S.O := ((oTwoSub A).subgroupOf S.M).map S.ρ with hR
    have hR1 : R ≤ S.Mbar := by
      rintro _ ⟨m, -, rfl⟩
      exact ⟨m, rfl⟩
    have hR2 : ∀ σ ∈ R, σ * S.ρ ⟨x, hxM⟩ = S.ρ ⟨x, hxM⟩ * σ := by
      rintro _ ⟨m, hm, rfl⟩
      rw [SetLike.mem_coe, mem_subgroupOf] at hm
      have hmE := (mem_inf.mp (oTwoSub_le A hm)).2
      rw [← map_mul, ← map_mul]
      congr 1
      exact Subtype.ext (mem_centralizer_iff.mp hmE x hE.mem).symm
    have hR3 : ∀ τ ∈ S.Mbar, τ * S.ρ ⟨x, hxM⟩ = S.ρ ⟨x, hxM⟩ * τ →
        ∀ σ ∈ R, τ * σ * τ⁻¹ ∈ R := by
      rintro _ ⟨m, rfl⟩ hτ _ ⟨m', hm', rfl⟩
      obtain ⟨c, hcM, hcx, hcm⟩ := S.exists_commute_rho_eq_of_pow_three hxM
        (pow_three_of_orderOf hx3) m.2 hτ
      rw [SetLike.mem_coe, mem_subgroupOf] at hm'
      have h1 : c * (m' : G) * c⁻¹ ∈ oTwoSub A :=
        conj_mem_oTwoSub (hnorm c hcM hcx) (hnorm' c hcM hcx) hm'
      refine ⟨⟨c * m' * c⁻¹, S.M.mul_mem (S.M.mul_mem hcM m'.2) (S.M.inv_mem hcM)⟩,
        by rw [SetLike.mem_coe, mem_subgroupOf]; exact h1, ?_⟩
      have e : (⟨c * m' * c⁻¹, S.M.mul_mem (S.M.mul_mem hcM m'.2) (S.M.inv_mem hcM)⟩ : S.M) =
          ⟨c, hcM⟩ * m' * ⟨c, hcM⟩⁻¹ := rfl
      rw [e, map_mul, map_mul, map_inv, hcm]
    have hR4 : IsPGroup 2 R := ((isPGroup_oTwoSub A).comap_of_injective S.M.subtype
      S.M.subtype_injective).map S.ρ
    have hRbot := hN2 R hR1 hR2 hR3 hR4
    intro y hy
    have h1 : S.ρ ⟨y, hOM hy⟩ ∈ R :=
      ⟨⟨y, hOM hy⟩, by rw [SetLike.mem_coe, mem_subgroupOf]; exact hy, rfl⟩
    rw [hRbot, mem_bot] at h1
    exact (S.ρ_eq_one_iff _).mp h1
  intro P hPM hPE hNP hPn hP2 p hp
  obtain ⟨k, n, hn, hpn⟩ := hP2 p hp
  obtain ⟨s, hs⟩ := exists_pow_two_mul_eq_one hpn hn.2.2
  have hns : IsOddCentralE (S.EOdd x : Set G) (n ^ s) := by
    have := isOddCentralE_of_mem_Nx (E := (S.EOdd x : Set G))
      (pow_mem (mem_Nx_of_isOddCentralE hn) s)
    simpa using this
  have hnsinv : IsOddCentralE (S.EOdd x : Set G) (n ^ s)⁻¹ := by
    have := isOddCentralE_of_mem_Nx (E := (S.EOdd x : Set G))
      (inv_mem (pow_mem (mem_Nx_of_isOddCentralE hn) s))
    simpa using this
  have hp₂P : p * (n ^ s)⁻¹ ∈ P := mul_mem hp (inv_mem (hNP _ hns))
  set N₀ : Subgroup G := ((Nx (S.EOdd x : Set G)).map (Cx (S.EOdd x : Set G)).subtype) with hN₀
  have hN₀P : N₀ ≤ P := by
    rintro _ ⟨m, hm, rfl⟩
    exact hNP _ (isOddCentralE_of_mem_Nx hm)
  have hN₀c : ∀ m ∈ N₀, ∀ q ∈ P, m * q = q * m := by
    rintro _ ⟨m, hm, rfl⟩ q hq
    exact (isOddCentralE_of_mem_Nx hm).2.1 q (hPE hq)
  have hP2' : ∀ q ∈ P, ∃ j : ℕ, q ^ (2 ^ j) ∈ N₀ := by
    intro q hq
    obtain ⟨j, m, hm, hqm⟩ := hP2 q hq
    exact ⟨j, ⟨⟨m, hm.1⟩, mem_Nx_of_isOddCentralE hm, hqm.symm⟩⟩
  have hp₂O : p * (n ^ s)⁻¹ ∈ oTwoSub P := mem_oTwoSub_of_central hN₀c hP2' hp₂P hs
  have hPA : P ≤ A := fun q hq => mem_inf.mpr ⟨hPM hq, hPE hq⟩
  have hOP : oTwoSub P ≤ oTwoSub A := by
    refine le_oTwoSub ((oTwoSub_le P).trans hPA) ?_ (isPGroup_oTwoSub P)
    intro a ha y hy
    obtain ⟨haM, haE⟩ := mem_inf.mp ha
    exact conj_mem_oTwoSub (hPn a haM haE) (fun q hq => by
      have := hPn a⁻¹ (S.M.inv_mem haM) (inv_mem haE) q hq
      rwa [inv_inv] at this) hy
  exact ⟨(n ^ s)⁻¹, hnsinv, hOQ (hOP hp₂O)⟩

end Setting

end CFSG.LargeExtraspecial
