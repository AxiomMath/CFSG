module

public import CFSG.GH74.Uniqueness.SU.KI1r4EData
public import CFSG.GH74.Uniqueness.SU.KI1r4ECount
public import CFSG.GH74.Uniqueness.SU.KI1r4EY

public section

namespace CFSG.GH74.Uniqueness.SU.K.R4

open Subgroup CFSG CFSG.LocalCores CFSG.GH74.Uniqueness.SU CFSG.GH74.Uniqueness.SU.K.R3
open CFSG.GH74.Uniqueness.SU.SU5
open scoped commutatorElement

variable {H : Type} [Group H] [Finite H]

theorem L85Data.false_of_fixed
    {T : Sylow 2 H} {x y : H} {A R : Subgroup H}
    (d : L85Data T x y A R) {K : Subgroup H} (hK : IsComponent K)
    (hKy : ∀ k ∈ K, y * k * y⁻¹ ∈ K) : False := by
  classical
  have hKL : K ≤ layer H := component_le_layer hK
  obtain ⟨z₀, hz₀K, hz₀c, hz₀1, hz₀2⟩ := d.hKinv K hK
  have hz₀E : ∀ g ∈ layer H, z₀ * g = g * z₀ := center_of_component_central hK hz₀K hz₀c
  have hz₀A : z₀ ∈ A := d.hZEA z₀ (hKL hz₀K) hz₀E
  have hyN : y ∈ normalizer (K : Set H) :=
    CFSG.GH74.Uniqueness.SU.K.R3.Pow.mem_normalizer_of_forall_mem K hKy
  have hKy' : ∀ k ∈ K, y⁻¹ * k * y ∈ K := by
    intro k hk
    have := Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hyN) k
    simpa using this.mp hk
  set ZK : Subgroup H := K ⊓ centralizer (K : Set H) with hZK
  have hZKA : ZK ≤ A := fun z hz => d.hZEA z (hKL hz.1) (center_of_component_central hK hz.1
    (fun k hk => (Subgroup.mem_centralizer_iff.mp hz.2 k hk).symm))
  have hz₀ZK : z₀ ∈ ZK :=
    ⟨hz₀K, Subgroup.mem_centralizer_iff.mpr fun k hk => (hz₀c k hk).symm⟩
  have hw : y * z₀ * y⁻¹ ∈ ZK := by
    refine ⟨hKy z₀ hz₀K, Subgroup.mem_centralizer_iff.mpr fun k hk => ?_⟩
    have hk' := hKy' k hk
    calc k * (y * z₀ * y⁻¹) = y * ((y⁻¹ * k * y) * z₀) * y⁻¹ := by group
      _ = y * (z₀ * (y⁻¹ * k * y)) * y⁻¹ := by rw [hz₀c _ hk']
      _ = (y * z₀ * y⁻¹) * k := by group
  have hwz : y * z₀ * y⁻¹ ≠ z₀ := d.rdata.y_A z₀ hz₀A hz₀1
  have hw1 : y * z₀ * y⁻¹ ≠ 1 := by
    intro h
    apply hz₀1
    have := congrArg (fun g => y⁻¹ * g * y) h
    simpa [mul_assoc] using this
  have hZKeq : ZK = A :=
    eq_of_two_distinct_involutions hZKA d.rdata.A_card hz₀ZK hw hz₀1 hw1 hwz hz₀2
  have hAZK : ∀ a ∈ A, a ∈ ZK := fun a ha => by rw [hZKeq]; exact ha
  have hZW : ∀ z ∈ center ↥R, (z : H) ∈ R ⊓ K := fun z hz =>
    ⟨z.2, (hAZK z ((d.hcenA z).mp hz)).1⟩
  have hWy : ∀ w ∈ R ⊓ K, y * w * y⁻¹ ∈ R ⊓ K :=
    fun w hw => ⟨d.rdata.y_norm w hw.1, hKy w hw.2⟩
  rcases d.rdata.invariant_abelian_or_eq d.h64 d.hZ4 d.hfr inf_le_left hZW hWy with hab | heq
  · obtain ⟨a, ha, b, hb, hnab⟩ := exists_noncomm_inf_of_component T hK hz₀K hz₀c hz₀1 hz₀2
    exact hnab (hab a ⟨d.hLT ⟨ha.1.1, ha.1.2⟩, ha.2⟩ b ⟨d.hLT ⟨hb.1.1, hb.1.2⟩, hb.2⟩)
  have hRK : R ≤ K := by
    intro r hr
    have : r ∈ R ⊓ K := by rw [heq]; exact hr
    exact this.2
  have hRT : R ≤ (T : Subgroup H) := by
    intro r hr
    have hr' := hr
    rw [d.rdata.R_eq] at hr'
    exact hr'.1
  have hTL : (T : Subgroup H) ⊓ layer H = R := le_antisymm d.hLT (le_inf hRT d.hRL)
  have hcardle : ∀ Q : Subgroup ↥K, IsPGroup 2 Q → Nat.card Q ≤ Nat.card R := by
    intro Q hQ
    have hQ' : IsPGroup 2 (Q.map K.subtype) := hQ.map _
    have hQL : Q.map K.subtype ≤ layer H := by
      rintro _ ⟨q, -, rfl⟩
      exact hKL q.2
    have := card_two_subgroup_le_inf T (Q.map K.subtype) hQ' hQL
    rw [hTL] at this
    rwa [Subgroup.card_map_of_injective K.subtype_injective] at this
  let P : Sylow 2 ↥K :=
    { toSubgroup := R.subgroupOf K
      isPGroup' := d.rdata.R_two.of_equiv (Subgroup.subgroupOfEquivOfLe hRK).symm
      is_maximal' := fun {Q} hQ hRQ => by
        have hcard : Nat.card Q ≤ Nat.card (R.subgroupOf K) := by
          rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hRK).toEquiv]
          exact hcardle Q hQ
        exact (Subgroup.eq_of_le_of_card_ge hRQ hcard).symm }
  have hcenK : ∀ z : ↥K, z ∈ center ↥K ↔ (z : H) ∈ A := by
    intro z
    constructor
    · intro hz
      have : (z : H) ∈ ZK := ⟨z.2, Subgroup.mem_centralizer_iff.mpr fun k hk =>
        congrArg Subtype.val (Subgroup.mem_center_iff.mp hz ⟨k, hk⟩)⟩
      rw [hZKeq] at this
      exact this
    · intro hz
      have : (z : H) ∈ ZK := by rw [hZKeq]; exact hz
      exact Subgroup.mem_center_iff.mpr fun g =>
        Subtype.ext (Subgroup.mem_centralizer_iff.mp this.2 g g.2)
  have hcenKcard : Nat.card (center ↥K) = 4 := by
    rw [← d.rdata.A_card]
    exact Nat.card_congr
      { toFun := fun z => ⟨(z.1 : H), (hcenK z.1).mp z.2⟩
        invFun := fun a => ⟨⟨(a : H), (hAZK a a.2).1⟩, (hcenK _).mpr a.2⟩
        left_inv := fun z => rfl
        right_inv := fun a => rfl }
  have hZ2 : IsPGroup 2 ↥(center ↥K) := by
    intro z
    refine ⟨1, Subtype.ext (Subtype.ext ?_)⟩
    have hzA : ((z : ↥K) : H) ∈ A := (hcenK z.1).mp z.2
    have := (isElemAbelian_iff.mp d.rdata.A_elem).2 _ hzA
    simpa using this
  have hZne : center ↥K ≠ ⊥ := by
    intro h
    have hz₀c' : (⟨z₀, hz₀K⟩ : ↥K) ∈ center ↥K :=
      Subgroup.mem_center_iff.mpr fun g => Subtype.ext (hz₀c g g.2).symm
    rw [h, Subgroup.mem_bot] at hz₀c'
    exact hz₀1 (congrArg Subtype.val hz₀c')
  have hcomm : ∀ a ∈ (P : Subgroup ↥K), ∀ b ∈ (P : Subgroup ↥K), ⁅a, b⁆ ∈ center ↥K := by
    intro a ha b hb
    have haR : (a : H) ∈ R := Subgroup.mem_subgroupOf.mp ha
    have hbR : (b : H) ∈ R := Subgroup.mem_subgroupOf.mp hb
    rw [hcenK]
    have := (d.hcenA ⁅(⟨(a : H), haR⟩ : ↥R), (⟨(b : H), hbR⟩ : ↥R)⁆).mp
      (d.hcom ⟨(a : H), haR⟩ ⟨(b : H), hbR⟩)
    exact this
  have hcard : Nat.card (P : Subgroup ↥K) = 16 * Nat.card (center ↥K) := by
    rw [hcenKcard]
    have : Nat.card (P : Subgroup ↥K) = Nat.card R :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hRK).toEquiv
    rw [this, d.h64]
  exact false_of_sylow_over_center hK.1 hZ2 hZne P hcomm hcard

end CFSG.GH74.Uniqueness.SU.K.R4
