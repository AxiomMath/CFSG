module

public import CFSG.GH74.Uniqueness.SU.SU13TA9M
public import CFSG.GH74.Uniqueness.SU.SU13Data9
public import CFSG.GH74.Uniqueness.SU.SU13TA9Elts

public section

namespace CFSG.GH74.Uniqueness.SU.SU13.TA.L9

open Equiv Equiv.Perm Subgroup CFSG.GH74.Uniqueness.SU.SU13.TA CFSG.GH74.Uniqueness.SU.SU13
  CFSG.GH74.Uniqueness.SU.SU4 CFSG.GH74.Uniqueness.SU.SU13.TB

variable {H : Type} [Group H] {π : H →* alternatingGroup (Fin 9)}

theorem mem_Mb_cases {y : alternatingGroup (Fin 9)} (hy : y ∈ Mb) :
    y ∈ Ebar ∨ y * et⁻¹ ∈ Ebar := by
  by_cases hyE : y ∈ Ebar
  · exact Or.inl hyE
  · right
    have hN : (Ebar.subgroupOf Mb).Normal := Subgroup.normal_of_index_eq_two relIndex_Ebar_Mb
    obtain ⟨a, ha⟩ := Subgroup.index_eq_two_iff'.mp
      (show (Ebar.subgroupOf Mb).index = 2 from relIndex_Ebar_Mb)
    have key : ∀ b : ↥Mb, b ∉ Ebar.subgroupOf Mb → a * b ∈ Ebar.subgroupOf Mb := fun b hb => by
      rcases ha b with ⟨h, -⟩ | ⟨h, -⟩
      · exact h
      · exact absurd h hb
    have h1 := key ⟨y, hy⟩ (fun h => hyE (Subgroup.mem_subgroupOf.mp h))
    have h2 := key ⟨et, et_mem_Mb⟩ (fun h => et_not_mem_Ebar (Subgroup.mem_subgroupOf.mp h))
    have h3 := Subgroup.mul_mem _ h1 (Subgroup.inv_mem _ h2)
    have h4 := hN.conj_mem _ h3 a⁻¹
    have h5 : (a⁻¹ * (a * ⟨y, hy⟩ * (a * ⟨et, et_mem_Mb⟩)⁻¹) * a⁻¹⁻¹ : ↥Mb) =
        ⟨y * et⁻¹, Mb.mul_mem hy (Mb.inv_mem et_mem_Mb)⟩ := by
      apply Subtype.ext
      simp [mul_assoc]
    rw [h5] at h4
    exact Subgroup.mem_subgroupOf.mp h4

namespace IsE

variable {E : Subgroup H}

theorem mul_self_mem (hπ : TwoCover π) (c : Cfg π) (hE : IsE π E) {m : H} (hm : m ∈ M0 c) :
    m * m ∈ E := by
  have hmb : π m ∈ Mb := π_mem_Mb hm
  have ht : c.t * c.t = 1 := by rw [← pow_two]; exact c.t_sq
  have hkcen : ∀ k ∈ π.ker, ∀ g : H, k * g = g * k := fun k hk g =>
    (Subgroup.mem_center_iff.mp (hπ.ker_le_center hk) g).symm
  rcases mem_Mb_cases hmb with h | h
  ·
    have h' : π m ∈ E.map π := hE.2 ▸ h
    obtain ⟨e, he, hem⟩ := h'
    have hk : m * e⁻¹ ∈ π.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hem]
      group
    have hk2 := hπ.sq_eq_one_of_mem_ker' hk
    have hmk : m * m = (m * e⁻¹) * (m * e⁻¹) * (e * e) := by
      calc m * m = (m * e⁻¹ * e) * (m * e⁻¹ * e) := by group
        _ = (m * e⁻¹) * (e * (m * e⁻¹)) * e := by group
        _ = (m * e⁻¹) * ((m * e⁻¹) * e) * e := by rw [← hkcen _ hk e]
        _ = (m * e⁻¹) * (m * e⁻¹) * (e * e) := by group
    rw [hmk, ← pow_two, hk2, one_mul]
    exact Subgroup.mul_mem _ he he
  ·
    have h' : π (m * c.t⁻¹) ∈ E.map π := by
      rw [map_mul, map_inv, c.π_t]
      exact hE.2 ▸ h
    obtain ⟨e, he, hem⟩ := h'
    have hk : m * c.t⁻¹ * e⁻¹ ∈ π.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hem]
      group
    have hk2 := hπ.sq_eq_one_of_mem_ker' hk
    have hte : c.t * e * c.t⁻¹ ∈ E := hE.conj_mem hπ c (t_mem_M0 hπ c) he
    set k := m * c.t⁻¹ * e⁻¹ with hkdef
    have hmk : m = k * e * c.t := by rw [hkdef]; group
    have hcalc : m * m = (k * k) * (e * (c.t * e * c.t⁻¹)) * (c.t * c.t) := by
      calc m * m = (k * e * c.t) * (k * e * c.t) := by rw [← hmk]
        _ = k * (e * c.t * k) * e * c.t := by group
        _ = k * (k * (e * c.t)) * e * c.t := by rw [← hkcen k hk (e * c.t)]
        _ = (k * k) * (e * (c.t * e * c.t⁻¹)) * (c.t * c.t) := by group
    rw [hcalc, ht, mul_one, ← pow_two, hk2, one_mul]
    exact Subgroup.mul_mem _ he hte

theorem nonempty_mulEquiv_Mbar [Finite H] (hπ : TwoCover π) (c : Cfg π) (hE : IsE π E) :
    Nonempty (Mbar (M0 c) ≃* Multiplicative (ZMod 2) × Multiplicative (ZMod 2)) := by
  classical
  have hMfin : Finite ↥(M0 c) := inferInstance
  have hoc := hE.oc_M0 hπ c
  have hpc : CFSG.pPrimeCore 2 ↥(M0 c) = E.subgroupOf (M0 c) := by
    apply Subgroup.map_injective (M0 c).subtype_injective
    have h1 : (CFSG.pPrimeCore 2 ↥(M0 c)).map (M0 c).subtype = E := hoc
    rw [h1, Subgroup.subgroupOf_map_subtype]
    exact (inf_eq_left.mpr (hE.le_M0 hπ c)).symm
  have hEN : (E.subgroupOf (M0 c)).Normal := by
    refine ⟨fun n hn g => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    exact hE.conj_mem hπ c g.2 hn
  have hcard : Nat.card (↥(M0 c) ⧸ E.subgroupOf (M0 c)) = 4 := by
    have h := Subgroup.card_eq_card_quotient_mul_card_subgroup (E.subgroupOf (M0 c))
    have hE27 : Nat.card (E.subgroupOf (M0 c)) = 27 := by
      rw [← hE.card hπ]
      exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe (hE.le_M0 hπ c)).toEquiv
    rw [card_M0 hπ c, hE27] at h
    omega
  have hsq : ∀ q : ↥(M0 c) ⧸ E.subgroupOf (M0 c), q * q = 1 := by
    intro q
    induction q using QuotientGroup.induction_on with
    | H m =>
      rw [← QuotientGroup.mk_mul, QuotientGroup.eq_one_iff]
      exact Subgroup.mem_subgroupOf.mpr (hE.mul_self_mem hπ c m.2)
  have hnt : Nontrivial (↥(M0 c) ⧸ E.subgroupOf (M0 c)) :=
    Finite.one_lt_card_iff_nontrivial.mp (by rw [hcard]; norm_num)
  have : IsKleinFour (↥(M0 c) ⧸ E.subgroupOf (M0 c)) :=
    ⟨hcard, (Monoid.exponent_eq_prime_iff Nat.prime_two).mpr (fun g hg =>
      orderOf_eq_prime (hp := ⟨Nat.prime_two⟩) (by rw [pow_two]; exact hsq g) hg)⟩
  have : IsKleinFour (Multiplicative (ZMod 2) × Multiplicative (ZMod 2)) := by
    constructor
    · simp
    · rw [Monoid.exponent_prod]
      simp
  obtain ⟨φ⟩ := IsKleinFour.nonempty_mulEquiv (G₁ := ↥(M0 c) ⧸ E.subgroupOf (M0 c))
    (G₂ := Multiplicative (ZMod 2) × Multiplicative (ZMod 2))
  exact ⟨(QuotientGroup.quotientMulEquivOfEq hpc).trans φ⟩

end IsE

theorem mpart9 [Finite H] (hπ : TwoCover π) (c : Cfg π) {E : Subgroup H} (hE : IsE π E) {z : H}
    (hz : z ∈ π.ker) (hz1 : z ≠ 1) : MPart9 z (c.elts hπ hz hz1) E := by
  have hcen : ∀ g : H, g * z = z * g := Subgroup.mem_center_iff.mp (hπ.ker_le_center hz)
  have hzz : centralizer ({z} : Set H) = ⊤ := by
    rw [eq_top_iff]
    intro g _
    exact Subgroup.mem_centralizer_singleton_iff.mpr (hcen g)
  have hMh : centralizer ({(c.elts hπ hz hz1).s₂} : Set H) ⊓ centralizer ({z} : Set H) = M0 c := by
    rw [hzz, inf_top_eq]
    rfl
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [hMh]
    exact card_M0 hπ c
  · rw [hMh]
    exact hE.le_M0 hπ c
  · rw [hMh]
    exact hE.oc_M0 hπ c
  · rw [hMh]
    exact hE.nonempty_mulEquiv_Mbar hπ c
  · intro x hx htx
    exact hE.cent_t hπ c hx htx

end CFSG.GH74.Uniqueness.SU.SU13.TA.L9
