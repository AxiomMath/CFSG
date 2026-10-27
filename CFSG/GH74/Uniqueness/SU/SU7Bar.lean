module

public import CFSG.GH74.Uniqueness.SU.SU7Base

public section

namespace CFSG.GH74.Uniqueness.SU.SU7

open Subgroup CFSG.GH74.Uniqueness.SU.SU4 CFSG.GH74.Uniqueness.SU.SU5

namespace Base

variable {G : Type} [Group G] [Finite G] {S : Sylow 2 G} {U M V : Subgroup G} {x z : G}

theorem U_le_T (hH : Hyp184 S U M) (hconf : Conf18H S M V x z)
    (hcl : Concl189 S U M x hconf.x_mem) : U ≤ Tsub S U := fun g hg => by
  have hgZ : g ∈ Zc (Tsub S U) := by rw [Zc_eq_U hH hconf hcl]; exact hg
  exact hgZ.1

omit [Finite G] in
theorem T_le_S : Tsub S U ≤ (S : Subgroup G) := inf_le_right

end Base

namespace Bar

variable {G : Type} [Group G] [Finite G] {S : Sylow 2 G} {U M V : Subgroup G} {x z : G}

theorem odd_pPrimeCore (M : Subgroup G) : Odd (Nat.card (pPrimeCore 2 ↥M)) :=
  Nat.coprime_two_left.1 (CFSG.pPrimeCore_coprime_card (p := 2) (G := ↥M))

omit [Finite G] in
theorem isPGroup_subgroupOf {T : Subgroup G} (hT : IsPGroup 2 T) (M : Subgroup G) :
    IsPGroup 2 ↥(T.subgroupOf M) := hT.comap_subtype

theorem eq_of_proj_eq {T : Subgroup G} (hT : IsPGroup 2 T) (hTM : T ≤ M) {a b : G} (ha : a ∈ T)
    (hb : b ∈ T) (hab : QuotientGroup.mk' (pPrimeCore 2 ↥M) ⟨a, hTM ha⟩ =
      QuotientGroup.mk' (pPrimeCore 2 ↥M) ⟨b, hTM hb⟩) : a = b := by
  have h1 : (⟨a, hTM ha⟩ : ↥M)⁻¹ * ⟨b, hTM hb⟩ ∈ pPrimeCore 2 ↥M := QuotientGroup.eq.1 hab
  have h2 : (⟨a, hTM ha⟩ : ↥M)⁻¹ * ⟨b, hTM hb⟩ ∈ T.subgroupOf M :=
    (T.subgroupOf M).mul_mem ((T.subgroupOf M).inv_mem ha) hb
  have h3 : (⟨a, hTM ha⟩ : ↥M)⁻¹ * ⟨b, hTM hb⟩ ∈ T.subgroupOf M ⊓ pPrimeCore 2 ↥M := ⟨h2, h1⟩
  rw [Gen.inf_eq_bot_of_isPGroup (isPGroup_subgroupOf hT M) (odd_pPrimeCore M),
    Subgroup.mem_bot] at h3
  have h4 : (⟨a, hTM ha⟩ : ↥M) = ⟨b, hTM hb⟩ := inv_mul_eq_one.1 h3
  exact congrArg Subtype.val h4

theorem normalizer_lift {T : Subgroup G} (hT : IsPGroup 2 T) (hTM : T ≤ M) {g : G} (hg : g ∈ M)
    (h : QuotientGroup.mk' (pPrimeCore 2 ↥M) ⟨g, hg⟩ ∈
      normalizer ((barImage M T : Subgroup (Mbar M)) : Set (Mbar M))) :
    ∃ (n : G) (hn : n ∈ M), n ∈ normalizer (T : Set G) ∧
      QuotientGroup.mk' (pPrimeCore 2 ↥M) ⟨n, hn⟩ = QuotientGroup.mk' (pPrimeCore 2 ↥M) ⟨g, hg⟩ := by
  have h' : QuotientGroup.mk' (pPrimeCore 2 ↥M) ⟨g, hg⟩ ∈ normalizer
      (((T.subgroupOf M).map (QuotientGroup.mk' (pPrimeCore 2 ↥M)) : Subgroup (Mbar M)) :
        Set (Mbar M)) := h
  rw [← Gen.map_normalizer_mk_eq (pPrimeCore 2 ↥M) (isPGroup_subgroupOf hT M) (odd_pPrimeCore M)]
    at h'
  obtain ⟨n, hn, hnn⟩ := h'
  have hconjT : ∀ t ∈ T, (n : G) * t * (n : G)⁻¹ ∈ T := by
    intro t ht
    have htP : (⟨t, hTM ht⟩ : ↥M) ∈ T.subgroupOf M := ht
    exact (mem_normalizer_iff.1 hn _).1 htP
  exact ⟨n, n.2, Gen.mem_normalizer_of_conj_le hconjT, hnn⟩

theorem exists_fpf (hH : Hyp184 S U M) (hconf : Conf18H S M V x z)
    (hcl : Concl189 S U M x hconf.x_mem) :
    ∃ a : G, a ∈ M ∧ a ∈ normalizer ((Tsub S U : Subgroup G) : Set G) ∧
      ∀ p ∈ U, p ≠ 1 → a * p * a⁻¹ ≠ p := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨Hh, H₀, hN, -, hH₀Hh, ⟨e⟩, -, -, -, hfpf, -⟩ := hcl.normalizerT
  have hTM : Tsub S U ≤ M := Base.T_le_S.trans hconf.S_le
  have hTp : IsPGroup 2 ↥(Tsub S U) := S.isPGroup'.to_le Base.T_le_S
  obtain ⟨σ, hσ⟩ : ∃ σ : Equiv.Perm (Fin 3), orderOf σ = 3 :=
    ⟨finRotate 3, orderOf_eq_prime (by decide) (by decide)⟩
  set a₀ : ↥H₀ := e.symm σ with ha₀
  have hord : orderOf (a₀ : Mbar M) = 3 := by
    rw [Subgroup.orderOf_coe, ha₀, MulEquiv.orderOf_eq e.symm σ, hσ]
  have hmem : (a₀ : Mbar M) ∈ normalizer
      ((barImage M (Tsub S U) : Subgroup (Mbar M)) : Set (Mbar M)) := by
    have h1 : (a₀ : Mbar M) ∈ barImage M (Tsub S U) ⊔ Hh := mem_sup_right (hH₀Hh a₀.2)
    rw [← hN] at h1
    exact h1
  obtain ⟨g, hg⟩ := QuotientGroup.mk_surjective (a₀ : Mbar M)
  have hg' : QuotientGroup.mk' (pPrimeCore 2 ↥M) ⟨(g : G), g.2⟩ ∈ normalizer
      ((barImage M (Tsub S U) : Subgroup (Mbar M)) : Set (Mbar M)) := by
    have : QuotientGroup.mk' (pPrimeCore 2 ↥M) ⟨(g : G), g.2⟩ = (a₀ : Mbar M) := hg
    rw [this]; exact hmem
  obtain ⟨n, hnM, hnN, hnā⟩ := normalizer_lift hTp hTM g.2 hg'
  refine ⟨n, hnM, hnN, ?_⟩
  intro p hpU hp1 hfix
  have hpT : p ∈ Tsub S U := Base.U_le_T hH hconf hcl hpU
  have hpM : p ∈ M := hTM hpT
  have hconj : (⟨n, hnM⟩ : ↥M) * ⟨p, hpM⟩ * (⟨n, hnM⟩ : ↥M)⁻¹ = ⟨p, hpM⟩ :=
    Subtype.ext (by simpa using hfix)
  have hna : QuotientGroup.mk' (pPrimeCore 2 ↥M) ⟨n, hnM⟩ = (a₀ : Mbar M) := by
    rw [hnā]; exact hg
  have hbar : (a₀ : Mbar M) * QuotientGroup.mk' (pPrimeCore 2 ↥M) ⟨p, hpM⟩ * (a₀ : Mbar M)⁻¹ =
      QuotientGroup.mk' (pPrimeCore 2 ↥M) ⟨p, hpM⟩ := by
    rw [← hna, ← map_inv, ← map_mul, ← map_mul, hconj]
  have hpP : (⟨p, hpM⟩ : ↥M) ∈ (Tsub S U).subgroupOf M := hpT
  have hpbar : QuotientGroup.mk' (pPrimeCore 2 ↥M) ⟨p, hpM⟩ ∈ barImage M (Tsub S U) :=
    Subgroup.mem_map_of_mem _ hpP
  have h1 := hfpf (a₀ : Mbar M) a₀.2 hord _ hpbar hbar
  have h2 : (⟨p, hpM⟩ : ↥M) ∈ pPrimeCore 2 ↥M := (QuotientGroup.eq_one_iff _).1 h1
  have h3 : (⟨p, hpM⟩ : ↥M) ∈ (Tsub S U).subgroupOf M ⊓ pPrimeCore 2 ↥M := ⟨hpP, h2⟩
  rw [Gen.inf_eq_bot_of_isPGroup (isPGroup_subgroupOf hTp M) (odd_pPrimeCore M),
    Subgroup.mem_bot] at h3
  exact hp1 (congrArg Subtype.val h3)

end Bar

end CFSG.GH74.Uniqueness.SU.SU7
