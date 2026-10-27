module

public import CFSG.LocalAnalysis.GH72.DDProduct
public import CFSG.GH74.Uniqueness.Section171Group
public import CFSG.LocalAnalysis.GH72.DDStructure

public section

namespace CFSG.GH72

open Subgroup DihedralGroup
open CFSG.CGT.Foote81L6 (mem_sup_iff_of_le_normalizer le_normalizer_of_comm)
open CFSG.CGT.Foote81L6.TStruct (card_zpowers_sup_zpowers mul_self_of_mem_zpowers_sup_zpowers
  eq_one_or_eq_of_mem_zpowers)

variable {G : Type*} [Group G]

theorem dd_corrected_complement {D D₁ D₂ : Subgroup G} (hd : DDDecomp D D₁ D₂)
    {x y ε₁ ε₂ : G} (hx : x ∈ D₁) (hy : y ∈ D₁) (hx2 : x * x = 1) (hy2 : y * y = 1)
    (hgen : D₁ = Subgroup.closure {x, y})
    (hε₁ : ε₁ ∈ D₂) (hε₂ : ε₂ ∈ D₂)
    (hε₁c : ∀ d ∈ D₂, d * ε₁ = ε₁ * d) (hε₂c : ∀ d ∈ D₂, d * ε₂ = ε₂ * d)
    (hε₁2 : ε₁ * ε₁ = 1) (hε₂2 : ε₂ * ε₂ = 1) :
    ∃ U : Subgroup G, DDDecomp D U D₂ ∧ Nonempty (U ≃* D₁) ∧
      U = Subgroup.closure {x * ε₁, y * ε₂} := by
  classical
  haveI hfact : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI hfinD1 : Finite ↥D₁ := hd.dih₁.finite
  haveI hfinD2 : Finite ↥D₂ := hd.isDih₂.finite
  haveI hfinD : Finite ↥D :=
    Finite.of_equiv (↥D₁ × ↥D₂) ((ddProdEquiv hd).toEquiv).symm
  have hxinv : x⁻¹ = x := inv_eq_of_mul_eq_one_right hx2
  have hyinv : y⁻¹ = y := inv_eq_of_mul_eq_one_right hy2
  have hD1card_ge : 4 ≤ Nat.card ↥D₁ := by
    obtain ⟨a, ha, ⟨e⟩⟩ := hd.dih₁
    have hcard : Nat.card ↥D₁ = 2 * 2 ^ a := by
      rw [Nat.card_congr e.toEquiv, DihedralGroup.nat_card]
    rw [hcard]
    have h2 : 2 ≤ 2 ^ a := by
      calc 2 = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ a := Nat.pow_le_pow_right (by norm_num) ha
    omega
  have hclosure_pair : ∀ p q : G,
      Subgroup.closure ({p, q} : Set G) = Subgroup.zpowers p ⊔ Subgroup.zpowers q := by
    intro p q
    rw [← Set.singleton_union, Subgroup.closure_union, Subgroup.zpowers_eq_closure,
      Subgroup.zpowers_eq_closure]
  have hD1eq : D₁ = Subgroup.zpowers x ⊔ Subgroup.zpowers y :=
    hgen.trans (hclosure_pair x y)
  have hx1 : x ≠ 1 := by
    intro hxe
    have hle : Nat.card ↥D₁ ≤ 2 := by
      rw [hD1eq, hxe, Subgroup.zpowers_one_eq_bot, bot_sup_eq, Nat.card_zpowers]
      exact Nat.le_of_dvd (by norm_num) (orderOf_dvd_iff_pow_eq_one.2 (by rw [pow_two]; exact hy2))
    omega
  have hy1 : y ≠ 1 := by
    intro hye
    have hle : Nat.card ↥D₁ ≤ 2 := by
      rw [hD1eq, hye, Subgroup.zpowers_one_eq_bot, sup_bot_eq, Nat.card_zpowers]
      exact Nat.le_of_dvd (by norm_num) (orderOf_dvd_iff_pow_eq_one.2 (by rw [pow_two]; exact hx2))
    omega
  have hxney : x ≠ y := by
    intro hxye
    have hle : Nat.card ↥D₁ ≤ 2 := by
      rw [hD1eq, hxye, sup_idem, Nat.card_zpowers]
      exact Nat.le_of_dvd (by norm_num) (orderOf_dvd_iff_pow_eq_one.2 (by rw [pow_two]; exact hy2))
    omega
  have closure_subtype : ∀ (H : Subgroup G) (p q : G) (hp : p ∈ H) (hq : q ∈ H),
      H = Subgroup.zpowers p ⊔ Subgroup.zpowers q →
      (⊤ : Subgroup ↥H) = Subgroup.zpowers (⟨p, hp⟩ : ↥H) ⊔
        Subgroup.zpowers (⟨q, hq⟩ : ↥H) := by
    intro H p q hp hq hH
    have hinj := Subgroup.map_injective (f := Subgroup.subtype H) (Subgroup.subtype_injective H)
    refine hinj ?_
    rw [Subgroup.map_top, Subgroup.map_sup, MonoidHom.map_zpowers, MonoidHom.map_zpowers,
      Subgroup.range_subtype]
    exact hH
  set r : G := x * y with hr_def
  have hrD1 : r ∈ D₁ := by rw [hr_def]; exact mul_mem hx hy
  have hD1_rx : D₁ = Subgroup.zpowers r ⊔ Subgroup.zpowers x := by
    apply le_antisymm
    · rw [hgen]
      refine (Subgroup.closure_le (Subgroup.zpowers r ⊔ Subgroup.zpowers x)).2 ?_
      intro z hz
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
      rcases hz with hz | hz
      · rw [hz]; exact Subgroup.mem_sup_right (Subgroup.mem_zpowers x)
      · rw [hz]
        have hy_eq : y = x * r := by
          rw [hr_def]
          calc y = (x * x) * y := by rw [hx2, one_mul]
            _ = x * (x * y) := by group
        rw [hy_eq]
        exact mul_mem (Subgroup.mem_sup_right (Subgroup.mem_zpowers x))
          (Subgroup.mem_sup_left (Subgroup.mem_zpowers r))
    · exact sup_le (Subgroup.zpowers_le.2 hrD1) (Subgroup.zpowers_le.2 hx)
  have hgenD1 : (⊤ : Subgroup ↥D₁) =
      Subgroup.zpowers (⟨r, hrD1⟩ : ↥D₁) ⊔ Subgroup.zpowers (⟨x, hx⟩ : ↥D₁) :=
    closure_subtype D₁ r x hrD1 hx hD1_rx
  have hσ2D1 : (⟨x, hx⟩ : ↥D₁) ^ 2 = 1 := by
    apply Subtype.ext
    simpa [pow_two] using hx2
  have hrelD1 : (⟨x, hx⟩ : ↥D₁) * ⟨r, hrD1⟩ * (⟨x, hx⟩ : ↥D₁)⁻¹ =
      (⟨r, hrD1⟩ : ↥D₁)⁻¹ := by
    apply Subtype.ext
    change x * r * x⁻¹ = r⁻¹
    rw [hr_def]
    calc x * (x * y) * x⁻¹ = x * (x * y) * x := by rw [hxinv]
      _ = (x * x) * (y * x) := by group
      _ = y * x := by rw [hx2, one_mul]
      _ = (x * y)⁻¹ := by rw [mul_inv_rev, hxinv, hyinv]
  have hD1nc : ¬ IsCyclic ↥D₁ := by
    obtain ⟨a, ha, ⟨e⟩⟩ := hd.dih₁
    intro hcyc
    have hcyc' : IsCyclic (DihedralGroup (2 ^ a)) := (e.isCyclic).mp hcyc
    refine DihedralGroup.not_isCyclic (n := 2 ^ a) ?_ hcyc'
    have h2 : 2 ≤ 2 ^ a := by
      calc 2 = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ a := Nat.pow_le_pow_right (by norm_num) ha
    omega
  have hD1iso : Nonempty (↥D₁ ≃* DihedralGroup (orderOf (⟨r, hrD1⟩ : ↥D₁))) := by
    rcases CFSG.GorensteinWalter.isCyclic_or_dihedral_of_generators
      (⟨r, hrD1⟩ : ↥D₁) (⟨x, hx⟩ : ↥D₁) hgenD1 hσ2D1 hrelD1 with hcyc | hdih
    · exact absurd hcyc hD1nc
    · exact hdih
  have hcardD1_order : Nat.card ↥D₁ = 2 * orderOf r := by
    have hord : orderOf (⟨r, hrD1⟩ : ↥D₁) = orderOf r := (Subgroup.orderOf_coe _).symm
    obtain ⟨eD1⟩ := hD1iso
    rw [Nat.card_congr eD1.toEquiv, DihedralGroup.nat_card, hord]
  obtain ⟨a, ha, ⟨eDa⟩⟩ := hd.dih₁
  have hcardD1_pow : Nat.card ↥D₁ = 2 * 2 ^ a := by
    rw [Nat.card_congr eDa.toEquiv, DihedralGroup.nat_card]
  have horder_r : orderOf r = 2 ^ a := by
    have h : 2 * orderOf r = 2 * 2 ^ a := hcardD1_order.symm.trans hcardD1_pow
    omega
  have horder_r_pos : 0 < orderOf r := by rw [horder_r]; positivity
  have hn_even : 2 ∣ orderOf r := by
    rw [horder_r]
    have h : 2 ^ 1 ∣ 2 ^ a := pow_dvd_pow 2 ha
    simpa using h
  have hxε₁ : x * ε₁ = ε₁ * x := hd.comm hx hε₁
  have hyε₁ : y * ε₁ = ε₁ * y := hd.comm hy hε₁
  have hxε₂ : x * ε₂ = ε₂ * x := hd.comm hx hε₂
  have hyε₂ : y * ε₂ = ε₂ * y := hd.comm hy hε₂
  have hεε : ε₁ * ε₂ = ε₂ * ε₁ := (hε₁c ε₂ hε₂).symm
  set u : G := x * ε₁ with hu_def
  set v : G := y * ε₂ with hv_def
  set ε : G := ε₁ * ε₂ with hε_def
  set U : Subgroup G := Subgroup.closure {u, v} with hU_def
  have hu2 : u * u = 1 := by
    rw [hu_def]
    calc (x * ε₁) * (x * ε₁) = x * (ε₁ * x) * ε₁ := by group
      _ = x * (x * ε₁) * ε₁ := by rw [← hxε₁]
      _ = (x * x) * (ε₁ * ε₁) := by group
      _ = 1 := by rw [hx2, hε₁2, one_mul]
  have hv2 : v * v = 1 := by
    rw [hv_def]
    calc (y * ε₂) * (y * ε₂) = y * (ε₂ * y) * ε₂ := by group
      _ = y * (y * ε₂) * ε₂ := by rw [← hyε₂]
      _ = (y * y) * (ε₂ * ε₂) := by group
      _ = 1 := by rw [hy2, hε₂2, one_mul]
  have hε2 : ε * ε = 1 := by
    rw [hε_def]
    calc (ε₁ * ε₂) * (ε₁ * ε₂) = ε₁ * (ε₂ * ε₁) * ε₂ := by group
      _ = ε₁ * (ε₁ * ε₂) * ε₂ := by rw [← hεε]
      _ = (ε₁ * ε₁) * (ε₂ * ε₂) := by group
      _ = 1 := by rw [hε₁2, hε₂2, one_mul]
  have hεD2 : ε ∈ D₂ := by rw [hε_def]; exact mul_mem hε₁ hε₂
  have huU : u ∈ U := by
    rw [hU_def]; exact Subgroup.subset_closure (by simp)
  have hvU : v ∈ U := by
    rw [hU_def]; exact Subgroup.subset_closure (by simp)
  have huD : u ∈ D := by
    rw [hu_def]; exact mul_mem (hd.le_left hx) (hd.le_right hε₁)
  have hvD : v ∈ D := by
    rw [hv_def]; exact mul_mem (hd.le_left hy) (hd.le_right hε₂)
  have hUD : U ≤ D := by
    rw [hU_def]
    refine (Subgroup.closure_le D).2 fun z hz => ?_
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
    rcases hz with hz | hz
    · rw [hz]; exact huD
    · rw [hz]; exact hvD
  haveI hfinU : Finite ↥U :=
    Finite.of_injective (Subgroup.inclusion hUD) (Subgroup.inclusion_injective hUD)
  have hu1 : u ≠ 1 := by
    intro hue
    have hxeq : x = 1 := by
      have h := hd.eq_and_eq hx (one_mem D₁) hε₁ (one_mem D₂) (by
        rw [hu_def] at hue
        simpa using hue)
      exact h.1
    exact hx1 hxeq
  have hv1 : v ≠ 1 := by
    intro hve
    have hyeq : y = 1 := by
      have h := hd.eq_and_eq hy (one_mem D₁) hε₂ (one_mem D₂) (by
        rw [hv_def] at hve
        simpa using hve)
      exact h.1
    exact hy1 hyeq
  have huneqv : u ≠ v := by
    intro huve
    have hxeqy : x = y := by
      have h := hd.eq_and_eq hx hy hε₁ hε₂ (by
        rw [hu_def, hv_def] at huve
        simpa using huve)
      exact h.1
    exact hxney hxeqy
  have huv_eq : u * v = r * ε := by
    rw [hu_def, hv_def, hr_def, hε_def]
    calc x * ε₁ * (y * ε₂) = x * (ε₁ * y) * ε₂ := by group
      _ = x * (y * ε₁) * ε₂ := by rw [← hyε₁]
      _ = (x * y) * (ε₁ * ε₂) := by group
  have hcomm_rε : Commute r ε := hd.comm hrD1 hεD2
  have huveq_pow : (u * v) ^ orderOf r = 1 := by
    rw [huv_eq]
    calc (r * ε) ^ orderOf r = r ^ orderOf r * ε ^ orderOf r := hcomm_rε.mul_pow _
      _ = 1 * ε ^ orderOf r := by rw [pow_orderOf_eq_one]
      _ = ε ^ orderOf r := one_mul _
      _ = 1 := by
        obtain ⟨k, hk⟩ := hn_even
        rw [hk, pow_mul, show ε ^ 2 = 1 by rw [pow_two]; exact hε2, one_pow]
  have hw_dvd : orderOf (u * v) ∣ orderOf r := orderOf_dvd_of_pow_eq_one huveq_pow
  have hU_wu : U = Subgroup.zpowers (u * v) ⊔ Subgroup.zpowers u := by
    apply le_antisymm
    · rw [hU_def]
      refine (Subgroup.closure_le (Subgroup.zpowers (u * v) ⊔ Subgroup.zpowers u)).2 ?_
      intro z hz
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
      rcases hz with hz | hz
      · rw [hz]; exact Subgroup.mem_sup_right (Subgroup.mem_zpowers u)
      · rw [hz]
        have hmem : (u * u) * v ∈ Subgroup.zpowers (u * v) ⊔ Subgroup.zpowers u := by
          have h : (u * u) * v = u * (u * v) := by group
          rw [h]
          exact mul_mem (Subgroup.mem_sup_right (Subgroup.mem_zpowers u))
            (Subgroup.mem_sup_left (Subgroup.mem_zpowers (u * v)))
        simpa [hu2, one_mul] using hmem
    · exact sup_le (Subgroup.zpowers_le.2 (mul_mem huU hvU)) (Subgroup.zpowers_le.2 huU)
  have hgenU : (⊤ : Subgroup ↥U) =
      Subgroup.zpowers (⟨u * v, mul_mem huU hvU⟩ : ↥U) ⊔
        Subgroup.zpowers (⟨u, huU⟩ : ↥U) :=
    closure_subtype U (u * v) u (mul_mem huU hvU) huU hU_wu
  have huinv : u⁻¹ = u := inv_eq_of_mul_eq_one_right hu2
  have hvinv : v⁻¹ = v := inv_eq_of_mul_eq_one_right hv2
  have hσ2U : (⟨u, huU⟩ : ↥U) ^ 2 = 1 := by
    apply Subtype.ext
    simpa [pow_two] using hu2
  have hrelU : (⟨u, huU⟩ : ↥U) * ⟨u * v, mul_mem huU hvU⟩ * (⟨u, huU⟩ : ↥U)⁻¹ =
      (⟨u * v, mul_mem huU hvU⟩ : ↥U)⁻¹ := by
    apply Subtype.ext
    change u * (u * v) * u⁻¹ = (u * v)⁻¹
    calc u * (u * v) * u⁻¹ = u * (u * v) * u := by rw [huinv]
      _ = (u * u) * (v * u) := by group
      _ = v * u := by rw [hu2, one_mul]
      _ = (u * v)⁻¹ := by rw [mul_inv_rev, huinv, hvinv]
  have hUnc : ¬ IsCyclic ↥U := by
    intro hcyc
    haveI : IsCyclic ↥U := hcyc
    have huo : orderOf (⟨u, huU⟩ : ↥U) = 2 := by
      rw [← Subgroup.orderOf_coe]
      exact orderOf_eq_prime (by rw [pow_two]; exact hu2) hu1
    have hvo : orderOf (⟨v, hvU⟩ : ↥U) = 2 := by
      rw [← Subgroup.orderOf_coe]
      exact orderOf_eq_prime (by rw [pow_two]; exact hv2) hv1
    have heq : (⟨u, huU⟩ : ↥U) = ⟨v, hvU⟩ :=
      CFSG.GH74.Uniqueness.eq_of_orderOf_eq_two_of_isCyclic huo hvo
    exact huneqv (congrArg Subtype.val heq)
  have hUiso : Nonempty (↥U ≃* DihedralGroup (orderOf (⟨u * v, mul_mem huU hvU⟩ : ↥U))) := by
    rcases CFSG.GorensteinWalter.isCyclic_or_dihedral_of_generators
      (⟨u * v, mul_mem huU hvU⟩ : ↥U) (⟨u, huU⟩ : ↥U) hgenU hσ2U hrelU with hcyc | hdih
    · exact absurd hcyc hUnc
    · exact hdih
  have hcardU_le : Nat.card ↥U ≤ Nat.card ↥D₁ := by
    rw [hcardD1_order]
    obtain ⟨eU⟩ := hUiso
    have hcard : Nat.card ↥U = 2 * orderOf (⟨u * v, mul_mem huU hvU⟩ : ↥U) := by
      rw [Nat.card_congr eU.toEquiv, DihedralGroup.nat_card]
    have hw_order : orderOf (⟨u * v, mul_mem huU hvU⟩ : ↥U) = orderOf (u * v) :=
      (Subgroup.orderOf_coe _).symm
    have hle : orderOf (u * v) ≤ orderOf r := Nat.le_of_dvd horder_r_pos hw_dvd
    rw [hcard, hw_order]
    exact Nat.mul_le_mul_left 2 hle
  let π : ↥D →* ↥D₁ :=
    (MonoidHom.fst ↥D₁ ↥D₂).comp (ddProdEquiv hd).toMonoidHom
  have hπ_apply : ∀ g : ↥D, π g = (ddProdEquiv hd g).1 := fun _ => rfl
  have hde_u : ddProdEquiv hd ⟨u, huD⟩ = ((⟨x, hx⟩ : ↥D₁), (⟨ε₁, hε₁⟩ : ↥D₂)) := by
    have hsymm : (ddProdEquiv hd).symm ((⟨x, hx⟩ : ↥D₁), (⟨ε₁, hε₁⟩ : ↥D₂)) = ⟨u, huD⟩ := by
      apply Subtype.ext
      rw [ddProdEquiv_symm_apply]
    have h := congrArg (ddProdEquiv hd) hsymm
    simpa using h.symm
  have hde_v : ddProdEquiv hd ⟨v, hvD⟩ = ((⟨y, hy⟩ : ↥D₁), (⟨ε₂, hε₂⟩ : ↥D₂)) := by
    have hsymm : (ddProdEquiv hd).symm ((⟨y, hy⟩ : ↥D₁), (⟨ε₂, hε₂⟩ : ↥D₂)) = ⟨v, hvD⟩ := by
      apply Subtype.ext
      rw [ddProdEquiv_symm_apply]
    have h := congrArg (ddProdEquiv hd) hsymm
    simpa using h.symm
  have hπu : π (⟨u, huD⟩ : ↥D) = (⟨x, hx⟩ : ↥D₁) := by
    have := congrArg Prod.fst hde_u
    simpa [hπ_apply] using this
  have hπv : π (⟨v, hvD⟩ : ↥D) = (⟨y, hy⟩ : ↥D₁) := by
    have := congrArg Prod.fst hde_v
    simpa [hπ_apply] using this
  let πU : ↥U →* ↥D₁ := π.comp (Subgroup.inclusion hUD)
  have hπUu : πU (⟨u, huU⟩ : ↥U) = (⟨x, hx⟩ : ↥D₁) := by
    have hin : Subgroup.inclusion hUD (⟨u, huU⟩ : ↥U) = (⟨u, huD⟩ : ↥D) := by
      apply Subtype.ext
      simpa using Subgroup.coe_inclusion hUD (⟨u, huU⟩ : ↥U)
    rw [show πU (⟨u, huU⟩ : ↥U) = π (Subgroup.inclusion hUD ⟨u, huU⟩) from rfl, hin]
    exact hπu
  have hπUv : πU (⟨v, hvU⟩ : ↥U) = (⟨y, hy⟩ : ↥D₁) := by
    have hin : Subgroup.inclusion hUD (⟨v, hvU⟩ : ↥U) = (⟨v, hvD⟩ : ↥D) := by
      apply Subtype.ext
      simpa using Subgroup.coe_inclusion hUD (⟨v, hvU⟩ : ↥U)
    rw [show πU (⟨v, hvU⟩ : ↥U) = π (Subgroup.inclusion hUD ⟨v, hvU⟩) from rfl, hin]
    exact hπv
  have hgenD1_xy : (⊤ : Subgroup ↥D₁) =
      Subgroup.zpowers (⟨x, hx⟩ : ↥D₁) ⊔ Subgroup.zpowers (⟨y, hy⟩ : ↥D₁) :=
    closure_subtype D₁ x y hx hy (hgen.trans (hclosure_pair x y))
  have hsurj : Function.Surjective πU := by
    have htop : (⊤ : Subgroup ↥D₁) ≤ πU.range := by
      rw [hgenD1_xy]
      exact sup_le (Subgroup.zpowers_le.2 ⟨⟨u, huU⟩, hπUu⟩)
        (Subgroup.zpowers_le.2 ⟨⟨v, hvU⟩, hπUv⟩)
    intro g
    exact htop (Subgroup.mem_top g)
  have hcardD1_le_U : Nat.card ↥D₁ ≤ Nat.card ↥U :=
    Nat.card_le_card_of_surjective πU hsurj
  have hcardU : Nat.card ↥U = Nat.card ↥D₁ :=
    le_antisymm hcardU_le hcardD1_le_U
  have hbij : Function.Bijective πU :=
    (Nat.bijective_iff_surjective_and_card πU).2 ⟨hsurj, hcardU⟩
  have hUisoD1 : Nonempty (↥U ≃* ↥D₁) := ⟨MulEquiv.ofBijective πU hbij⟩
  have hπ_one_of_mem_D2 : ∀ g : ↥D, (g : G) ∈ D₂ → π g = 1 := by
    intro g hgD₂
    have hcomp := ddProdEquiv_apply_mul hd g
    have h1mem : ((ddProdEquiv hd g).1 : G) ∈ D₁ := (ddProdEquiv hd g).1.2
    have h2mem : ((ddProdEquiv hd g).2 : G) ∈ D₂ := (ddProdEquiv hd g).2.2
    have h1D₂ : ((ddProdEquiv hd g).1 : G) ∈ D₂ := by
      have h : ((ddProdEquiv hd g).1 : G) = (g : G) * ((ddProdEquiv hd g).2 : G)⁻¹ := by
        rw [← hcomp]; group
      rw [h]
      exact mul_mem hgD₂ (inv_mem h2mem)
    have h1bot : ((ddProdEquiv hd g).1 : G) ∈ D₁ ⊓ D₂ := ⟨h1mem, h1D₂⟩
    rw [hd.inf_eq, mem_bot] at h1bot
    have h1one : (ddProdEquiv hd g).1 = 1 := Subtype.ext h1bot
    rw [hπ_apply]
    exact h1one
  have hinf : U ⊓ D₂ = ⊥ := by
    rw [eq_bot_iff]
    rintro g ⟨hgU, hgD₂⟩
    have hg_one : (⟨g, hgU⟩ : ↥U) = 1 := by
      apply hbij.1
      have hπg : πU (⟨g, hgU⟩ : ↥U) = 1 := by
        have hin : Subgroup.inclusion hUD (⟨g, hgU⟩ : ↥U) = ⟨g, hUD hgU⟩ := by
          apply Subtype.ext
          simpa using Subgroup.coe_inclusion hUD (⟨g, hgU⟩ : ↥U)
        rw [show πU (⟨g, hgU⟩ : ↥U) = π (Subgroup.inclusion hUD ⟨g, hgU⟩) from rfl, hin]
        exact hπ_one_of_mem_D2 _ hgD₂
      simpa using hπg
    exact congrArg Subtype.val hg_one
  have hx_eq_u : x = u * ε₁⁻¹ := by rw [hu_def]; group
  have hy_eq_v : y = v * ε₂⁻¹ := by rw [hv_def]; group
  have hD1_le_UD2 : D₁ ≤ U ⊔ D₂ := by
    rw [hgen]
    refine (Subgroup.closure_le (U ⊔ D₂)).2 fun z hz => ?_
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
    rcases hz with hz | hz
    · rw [hz, hx_eq_u]
      exact mul_mem (Subgroup.mem_sup_left huU) (Subgroup.mem_sup_right (inv_mem hε₁))
    · rw [hz, hy_eq_v]
      exact mul_mem (Subgroup.mem_sup_left hvU) (Subgroup.mem_sup_right (inv_mem hε₂))
  have hsup : U ⊔ D₂ = D := by
    apply le_antisymm
    · exact sup_le hUD hd.le_right
    · rw [← hd.sup_eq]
      exact sup_le hD1_le_UD2 le_sup_right
  have hu_cent : u ∈ Subgroup.centralizer (D₂ : Set G) := by
    rw [hu_def, mem_centralizer_iff]
    intro d hdD₂
    calc d * (x * ε₁) = (d * x) * ε₁ := by group
      _ = (x * d) * ε₁ := by rw [← hd.comm hx hdD₂]
      _ = x * (d * ε₁) := by group
      _ = x * (ε₁ * d) := by rw [hε₁c d hdD₂]
      _ = x * ε₁ * d := by group
  have hv_cent : v ∈ Subgroup.centralizer (D₂ : Set G) := by
    rw [hv_def, mem_centralizer_iff]
    intro d hdD₂
    calc d * (y * ε₂) = (d * y) * ε₂ := by group
      _ = (y * d) * ε₂ := by rw [← hd.comm hy hdD₂]
      _ = y * (d * ε₂) := by group
      _ = y * (ε₂ * d) := by rw [hε₂c d hdD₂]
      _ = y * ε₂ * d := by group
  have hU_cent : U ≤ Subgroup.centralizer (D₂ : Set G) := by
    rw [hU_def]
    refine (Subgroup.closure_le _).2 fun z hz => ?_
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
    rcases hz with hz | hz
    · rw [hz]; exact hu_cent
    · rw [hz]; exact hv_cent
  have hcommU : D₂ ≤ Subgroup.centralizer (U : Set G) :=
    (Subgroup.le_centralizer_iff).1 hU_cent
  obtain ⟨eU⟩ := hUisoD1
  have hdihU : IsDih U := ⟨a, ha, ⟨eU.trans eDa⟩⟩
  refine ⟨U, ?_, ⟨eU⟩, ?_⟩
  · exact { sup_eq := hsup, inf_eq := hinf, commute := hcommU, dih₁ := hdihU, dih₂ := hd.dih₂ }
  · rw [hU_def, hu_def, hv_def]

theorem dd_corrected_complement_right {D D₁ D₂ : Subgroup G} (hd : DDDecomp D D₁ D₂)
    {x y ε₁ ε₂ : G} (hx : x ∈ D₂) (hy : y ∈ D₂) (hx2 : x * x = 1) (hy2 : y * y = 1)
    (hgen : D₂ = Subgroup.closure {x, y})
    (hε₁ : ε₁ ∈ D₁) (hε₂ : ε₂ ∈ D₁)
    (hε₁c : ∀ d ∈ D₁, d * ε₁ = ε₁ * d) (hε₂c : ∀ d ∈ D₁, d * ε₂ = ε₂ * d)
    (hε₁2 : ε₁ * ε₁ = 1) (hε₂2 : ε₂ * ε₂ = 1) :
    ∃ U : Subgroup G, DDDecomp D D₁ U ∧ Nonempty (U ≃* D₂) ∧
      U = Subgroup.closure {x * ε₁, y * ε₂} := by
  classical
  haveI hfact : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI hfinD1 : Finite ↥D₁ := hd.dih₁.finite
  haveI hfinD2 : Finite ↥D₂ := hd.isDih₂.finite
  haveI hfinD : Finite ↥D :=
    Finite.of_equiv (↥D₁ × ↥D₂) ((ddProdEquiv hd).toEquiv).symm
  have hxinv : x⁻¹ = x := inv_eq_of_mul_eq_one_right hx2
  have hyinv : y⁻¹ = y := inv_eq_of_mul_eq_one_right hy2
  have hD2card_ge : 4 ≤ Nat.card ↥D₂ := by
    obtain ⟨b, hb, ⟨e⟩⟩ := hd.dih₂
    have hcard : Nat.card ↥D₂ = 2 * 2 ^ b := by
      rw [Nat.card_congr e.toEquiv, DihedralGroup.nat_card]
    rw [hcard]
    have h2 : 2 ≤ 2 ^ b := by
      calc 2 = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ b := Nat.pow_le_pow_right (by norm_num) (by omega : 1 ≤ b)
    omega
  have hclosure_pair : ∀ p q : G,
      Subgroup.closure ({p, q} : Set G) = Subgroup.zpowers p ⊔ Subgroup.zpowers q := by
    intro p q
    rw [← Set.singleton_union, Subgroup.closure_union, Subgroup.zpowers_eq_closure,
      Subgroup.zpowers_eq_closure]
  have hD2eq : D₂ = Subgroup.zpowers x ⊔ Subgroup.zpowers y :=
    hgen.trans (hclosure_pair x y)
  have hx1 : x ≠ 1 := by
    intro hxe
    have hle : Nat.card ↥D₂ ≤ 2 := by
      rw [hD2eq, hxe, Subgroup.zpowers_one_eq_bot, bot_sup_eq, Nat.card_zpowers]
      exact Nat.le_of_dvd (by norm_num) (orderOf_dvd_iff_pow_eq_one.2 (by rw [pow_two]; exact hy2))
    omega
  have hy1 : y ≠ 1 := by
    intro hye
    have hle : Nat.card ↥D₂ ≤ 2 := by
      rw [hD2eq, hye, Subgroup.zpowers_one_eq_bot, sup_bot_eq, Nat.card_zpowers]
      exact Nat.le_of_dvd (by norm_num) (orderOf_dvd_iff_pow_eq_one.2 (by rw [pow_two]; exact hx2))
    omega
  have hxney : x ≠ y := by
    intro hxye
    have hle : Nat.card ↥D₂ ≤ 2 := by
      rw [hD2eq, hxye, sup_idem, Nat.card_zpowers]
      exact Nat.le_of_dvd (by norm_num) (orderOf_dvd_iff_pow_eq_one.2 (by rw [pow_two]; exact hy2))
    omega
  have closure_subtype : ∀ (H : Subgroup G) (p q : G) (hp : p ∈ H) (hq : q ∈ H),
      H = Subgroup.zpowers p ⊔ Subgroup.zpowers q →
      (⊤ : Subgroup ↥H) = Subgroup.zpowers (⟨p, hp⟩ : ↥H) ⊔
        Subgroup.zpowers (⟨q, hq⟩ : ↥H) := by
    intro H p q hp hq hH
    have hinj := Subgroup.map_injective (f := Subgroup.subtype H) (Subgroup.subtype_injective H)
    refine hinj ?_
    rw [Subgroup.map_top, Subgroup.map_sup, MonoidHom.map_zpowers, MonoidHom.map_zpowers,
      Subgroup.range_subtype]
    exact hH
  set r : G := x * y with hr_def
  have hrD2 : r ∈ D₂ := by rw [hr_def]; exact mul_mem hx hy
  have hD2_rx : D₂ = Subgroup.zpowers r ⊔ Subgroup.zpowers x := by
    apply le_antisymm
    · rw [hgen]
      refine (Subgroup.closure_le (Subgroup.zpowers r ⊔ Subgroup.zpowers x)).2 ?_
      intro z hz
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
      rcases hz with hz | hz
      · rw [hz]; exact Subgroup.mem_sup_right (Subgroup.mem_zpowers x)
      · rw [hz]
        have hy_eq : y = x * r := by
          rw [hr_def]
          calc y = (x * x) * y := by rw [hx2, one_mul]
            _ = x * (x * y) := by group
        rw [hy_eq]
        exact mul_mem (Subgroup.mem_sup_right (Subgroup.mem_zpowers x))
          (Subgroup.mem_sup_left (Subgroup.mem_zpowers r))
    · exact sup_le (Subgroup.zpowers_le.2 hrD2) (Subgroup.zpowers_le.2 hx)
  have hgenD2 : (⊤ : Subgroup ↥D₂) =
      Subgroup.zpowers (⟨r, hrD2⟩ : ↥D₂) ⊔ Subgroup.zpowers (⟨x, hx⟩ : ↥D₂) :=
    closure_subtype D₂ r x hrD2 hx hD2_rx
  have hσ2D2 : (⟨x, hx⟩ : ↥D₂) ^ 2 = 1 := by
    apply Subtype.ext
    simpa [pow_two] using hx2
  have hrelD2 : (⟨x, hx⟩ : ↥D₂) * ⟨r, hrD2⟩ * (⟨x, hx⟩ : ↥D₂)⁻¹ =
      (⟨r, hrD2⟩ : ↥D₂)⁻¹ := by
    apply Subtype.ext
    change x * r * x⁻¹ = r⁻¹
    rw [hr_def]
    calc x * (x * y) * x⁻¹ = x * (x * y) * x := by rw [hxinv]
      _ = (x * x) * (y * x) := by group
      _ = y * x := by rw [hx2, one_mul]
      _ = (x * y)⁻¹ := by rw [mul_inv_rev, hxinv, hyinv]
  have hD2nc : ¬ IsCyclic ↥D₂ := by
    obtain ⟨b, hb, ⟨e⟩⟩ := hd.dih₂
    intro hcyc
    have hcyc' : IsCyclic (DihedralGroup (2 ^ b)) := (e.isCyclic).mp hcyc
    refine DihedralGroup.not_isCyclic (n := 2 ^ b) ?_ hcyc'
    have h2 : 2 ≤ 2 ^ b := by
      calc 2 = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ b := Nat.pow_le_pow_right (by norm_num) (by omega : 1 ≤ b)
    omega
  have hD2iso : Nonempty (↥D₂ ≃* DihedralGroup (orderOf (⟨r, hrD2⟩ : ↥D₂))) := by
    rcases CFSG.GorensteinWalter.isCyclic_or_dihedral_of_generators
      (⟨r, hrD2⟩ : ↥D₂) (⟨x, hx⟩ : ↥D₂) hgenD2 hσ2D2 hrelD2 with hcyc | hdih
    · exact absurd hcyc hD2nc
    · exact hdih
  have hcardD2_order : Nat.card ↥D₂ = 2 * orderOf r := by
    have hord : orderOf (⟨r, hrD2⟩ : ↥D₂) = orderOf r := (Subgroup.orderOf_coe _).symm
    obtain ⟨eD2⟩ := hD2iso
    rw [Nat.card_congr eD2.toEquiv, DihedralGroup.nat_card, hord]
  obtain ⟨b, hb, ⟨eDb⟩⟩ := hd.dih₂
  have hcardD2_pow : Nat.card ↥D₂ = 2 * 2 ^ b := by
    rw [Nat.card_congr eDb.toEquiv, DihedralGroup.nat_card]
  have horder_r : orderOf r = 2 ^ b := by
    have h : 2 * orderOf r = 2 * 2 ^ b := hcardD2_order.symm.trans hcardD2_pow
    omega
  have horder_r_pos : 0 < orderOf r := by rw [horder_r]; positivity
  have hn_even : 2 ∣ orderOf r := by
    rw [horder_r]
    have h : 2 ^ 1 ∣ 2 ^ b := pow_dvd_pow 2 (by omega : 1 ≤ b)
    simpa using h
  have hxε₁ : x * ε₁ = ε₁ * x := (hd.comm hε₁ hx).symm
  have hyε₁ : y * ε₁ = ε₁ * y := (hd.comm hε₁ hy).symm
  have hxε₂ : x * ε₂ = ε₂ * x := (hd.comm hε₂ hx).symm
  have hyε₂ : y * ε₂ = ε₂ * y := (hd.comm hε₂ hy).symm
  have hεε : ε₁ * ε₂ = ε₂ * ε₁ := (hε₁c ε₂ hε₂).symm
  set u : G := x * ε₁ with hu_def
  set v : G := y * ε₂ with hv_def
  set ε : G := ε₁ * ε₂ with hε_def
  set U : Subgroup G := Subgroup.closure {u, v} with hU_def
  have hu2 : u * u = 1 := by
    rw [hu_def]
    calc (x * ε₁) * (x * ε₁) = x * (ε₁ * x) * ε₁ := by group
      _ = x * (x * ε₁) * ε₁ := by rw [← hxε₁]
      _ = (x * x) * (ε₁ * ε₁) := by group
      _ = 1 := by rw [hx2, hε₁2, one_mul]
  have hv2 : v * v = 1 := by
    rw [hv_def]
    calc (y * ε₂) * (y * ε₂) = y * (ε₂ * y) * ε₂ := by group
      _ = y * (y * ε₂) * ε₂ := by rw [← hyε₂]
      _ = (y * y) * (ε₂ * ε₂) := by group
      _ = 1 := by rw [hy2, hε₂2, one_mul]
  have hε2 : ε * ε = 1 := by
    rw [hε_def]
    calc (ε₁ * ε₂) * (ε₁ * ε₂) = ε₁ * (ε₂ * ε₁) * ε₂ := by group
      _ = ε₁ * (ε₁ * ε₂) * ε₂ := by rw [← hεε]
      _ = (ε₁ * ε₁) * (ε₂ * ε₂) := by group
      _ = 1 := by rw [hε₁2, hε₂2, one_mul]
  have hεD1 : ε ∈ D₁ := by rw [hε_def]; exact mul_mem hε₁ hε₂
  have huU : u ∈ U := by
    rw [hU_def]; exact Subgroup.subset_closure (by simp)
  have hvU : v ∈ U := by
    rw [hU_def]; exact Subgroup.subset_closure (by simp)
  have huD : u ∈ D := by
    rw [hu_def]; exact mul_mem (hd.le_right hx) (hd.le_left hε₁)
  have hvD : v ∈ D := by
    rw [hv_def]; exact mul_mem (hd.le_right hy) (hd.le_left hε₂)
  have hUD : U ≤ D := by
    rw [hU_def]
    refine (Subgroup.closure_le D).2 fun z hz => ?_
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
    rcases hz with hz | hz
    · rw [hz]; exact huD
    · rw [hz]; exact hvD
  haveI hfinU : Finite ↥U :=
    Finite.of_injective (Subgroup.inclusion hUD) (Subgroup.inclusion_injective hUD)
  have hu1 : u ≠ 1 := by
    intro hue
    have hxeq : x = 1 := by
      have h := hd.eq_and_eq hε₁ (one_mem D₁) hx (one_mem D₂) (by
        rw [hd.comm hε₁ hx]
        simpa using hue)
      exact h.2
    exact hx1 hxeq
  have hv1 : v ≠ 1 := by
    intro hve
    have hyeq : y = 1 := by
      have h := hd.eq_and_eq hε₂ (one_mem D₁) hy (one_mem D₂) (by
        rw [hd.comm hε₂ hy]
        simpa using hve)
      exact h.2
    exact hy1 hyeq
  have huneqv : u ≠ v := by
    intro huve
    have hxeqy : x = y := by
      have h := hd.eq_and_eq hε₁ hε₂ hx hy (by
        rw [hd.comm hε₁ hx, hd.comm hε₂ hy]
        simpa using huve)
      exact h.2
    exact hxney hxeqy
  have huv_eq : u * v = r * ε := by
    rw [hu_def, hv_def, hr_def, hε_def]
    calc x * ε₁ * (y * ε₂) = x * (ε₁ * y) * ε₂ := by group
      _ = x * (y * ε₁) * ε₂ := by rw [← hyε₁]
      _ = (x * y) * (ε₁ * ε₂) := by group
  have hcomm_rε : Commute r ε := (hd.comm hεD1 hrD2).symm
  have huveq_pow : (u * v) ^ orderOf r = 1 := by
    rw [huv_eq]
    calc (r * ε) ^ orderOf r = r ^ orderOf r * ε ^ orderOf r := hcomm_rε.mul_pow _
      _ = 1 * ε ^ orderOf r := by rw [pow_orderOf_eq_one]
      _ = ε ^ orderOf r := one_mul _
      _ = 1 := by
        obtain ⟨k, hk⟩ := hn_even
        rw [hk, pow_mul, show ε ^ 2 = 1 by rw [pow_two]; exact hε2, one_pow]
  have hw_dvd : orderOf (u * v) ∣ orderOf r := orderOf_dvd_of_pow_eq_one huveq_pow
  have hU_wu : U = Subgroup.zpowers (u * v) ⊔ Subgroup.zpowers u := by
    apply le_antisymm
    · rw [hU_def]
      refine (Subgroup.closure_le (Subgroup.zpowers (u * v) ⊔ Subgroup.zpowers u)).2 ?_
      intro z hz
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
      rcases hz with hz | hz
      · rw [hz]; exact Subgroup.mem_sup_right (Subgroup.mem_zpowers u)
      · rw [hz]
        have hmem : (u * u) * v ∈ Subgroup.zpowers (u * v) ⊔ Subgroup.zpowers u := by
          have h : (u * u) * v = u * (u * v) := by group
          rw [h]
          exact mul_mem (Subgroup.mem_sup_right (Subgroup.mem_zpowers u))
            (Subgroup.mem_sup_left (Subgroup.mem_zpowers (u * v)))
        simpa [hu2, one_mul] using hmem
    · exact sup_le (Subgroup.zpowers_le.2 (mul_mem huU hvU)) (Subgroup.zpowers_le.2 huU)
  have hgenU : (⊤ : Subgroup ↥U) =
      Subgroup.zpowers (⟨u * v, mul_mem huU hvU⟩ : ↥U) ⊔
        Subgroup.zpowers (⟨u, huU⟩ : ↥U) :=
    closure_subtype U (u * v) u (mul_mem huU hvU) huU hU_wu
  have huinv : u⁻¹ = u := inv_eq_of_mul_eq_one_right hu2
  have hvinv : v⁻¹ = v := inv_eq_of_mul_eq_one_right hv2
  have hσ2U : (⟨u, huU⟩ : ↥U) ^ 2 = 1 := by
    apply Subtype.ext
    simpa [pow_two] using hu2
  have hrelU : (⟨u, huU⟩ : ↥U) * ⟨u * v, mul_mem huU hvU⟩ * (⟨u, huU⟩ : ↥U)⁻¹ =
      (⟨u * v, mul_mem huU hvU⟩ : ↥U)⁻¹ := by
    apply Subtype.ext
    change u * (u * v) * u⁻¹ = (u * v)⁻¹
    calc u * (u * v) * u⁻¹ = u * (u * v) * u := by rw [huinv]
      _ = (u * u) * (v * u) := by group
      _ = v * u := by rw [hu2, one_mul]
      _ = (u * v)⁻¹ := by rw [mul_inv_rev, huinv, hvinv]
  have hUnc : ¬ IsCyclic ↥U := by
    intro hcyc
    haveI : IsCyclic ↥U := hcyc
    have huo : orderOf (⟨u, huU⟩ : ↥U) = 2 := by
      rw [← Subgroup.orderOf_coe]
      exact orderOf_eq_prime (by rw [pow_two]; exact hu2) hu1
    have hvo : orderOf (⟨v, hvU⟩ : ↥U) = 2 := by
      rw [← Subgroup.orderOf_coe]
      exact orderOf_eq_prime (by rw [pow_two]; exact hv2) hv1
    have heq : (⟨u, huU⟩ : ↥U) = ⟨v, hvU⟩ :=
      CFSG.GH74.Uniqueness.eq_of_orderOf_eq_two_of_isCyclic huo hvo
    exact huneqv (congrArg Subtype.val heq)
  have hUiso : Nonempty (↥U ≃* DihedralGroup (orderOf (⟨u * v, mul_mem huU hvU⟩ : ↥U))) := by
    rcases CFSG.GorensteinWalter.isCyclic_or_dihedral_of_generators
      (⟨u * v, mul_mem huU hvU⟩ : ↥U) (⟨u, huU⟩ : ↥U) hgenU hσ2U hrelU with hcyc | hdih
    · exact absurd hcyc hUnc
    · exact hdih
  have hcardU_le : Nat.card ↥U ≤ Nat.card ↥D₂ := by
    rw [hcardD2_order]
    obtain ⟨eU⟩ := hUiso
    have hcard : Nat.card ↥U = 2 * orderOf (⟨u * v, mul_mem huU hvU⟩ : ↥U) := by
      rw [Nat.card_congr eU.toEquiv, DihedralGroup.nat_card]
    have hw_order : orderOf (⟨u * v, mul_mem huU hvU⟩ : ↥U) = orderOf (u * v) :=
      (Subgroup.orderOf_coe _).symm
    have hle : orderOf (u * v) ≤ orderOf r := Nat.le_of_dvd horder_r_pos hw_dvd
    rw [hcard, hw_order]
    exact Nat.mul_le_mul_left 2 hle
  let π : ↥D →* ↥D₂ :=
    (MonoidHom.snd ↥D₁ ↥D₂).comp (ddProdEquiv hd).toMonoidHom
  have hπ_apply : ∀ g : ↥D, π g = (ddProdEquiv hd g).2 := fun _ => rfl
  have hde_u : ddProdEquiv hd ⟨u, huD⟩ = ((⟨ε₁, hε₁⟩ : ↥D₁), (⟨x, hx⟩ : ↥D₂)) := by
    have hsymm : (ddProdEquiv hd).symm ((⟨ε₁, hε₁⟩ : ↥D₁), (⟨x, hx⟩ : ↥D₂)) = ⟨u, huD⟩ := by
      apply Subtype.ext
      rw [ddProdEquiv_symm_apply]
      exact hxε₁.symm
    have h := congrArg (ddProdEquiv hd) hsymm
    simpa using h.symm
  have hde_v : ddProdEquiv hd ⟨v, hvD⟩ = ((⟨ε₂, hε₂⟩ : ↥D₁), (⟨y, hy⟩ : ↥D₂)) := by
    have hsymm : (ddProdEquiv hd).symm ((⟨ε₂, hε₂⟩ : ↥D₁), (⟨y, hy⟩ : ↥D₂)) = ⟨v, hvD⟩ := by
      apply Subtype.ext
      rw [ddProdEquiv_symm_apply]
      exact hyε₂.symm
    have h := congrArg (ddProdEquiv hd) hsymm
    simpa using h.symm
  have hπu : π (⟨u, huD⟩ : ↥D) = (⟨x, hx⟩ : ↥D₂) := by
    have := congrArg Prod.snd hde_u
    simpa [hπ_apply] using this
  have hπv : π (⟨v, hvD⟩ : ↥D) = (⟨y, hy⟩ : ↥D₂) := by
    have := congrArg Prod.snd hde_v
    simpa [hπ_apply] using this
  let πU : ↥U →* ↥D₂ := π.comp (Subgroup.inclusion hUD)
  have hπUu : πU (⟨u, huU⟩ : ↥U) = (⟨x, hx⟩ : ↥D₂) := by
    have hin : Subgroup.inclusion hUD (⟨u, huU⟩ : ↥U) = (⟨u, huD⟩ : ↥D) := by
      apply Subtype.ext
      simpa using Subgroup.coe_inclusion hUD (⟨u, huU⟩ : ↥U)
    rw [show πU (⟨u, huU⟩ : ↥U) = π (Subgroup.inclusion hUD ⟨u, huU⟩) from rfl, hin]
    exact hπu
  have hπUv : πU (⟨v, hvU⟩ : ↥U) = (⟨y, hy⟩ : ↥D₂) := by
    have hin : Subgroup.inclusion hUD (⟨v, hvU⟩ : ↥U) = (⟨v, hvD⟩ : ↥D) := by
      apply Subtype.ext
      simpa using Subgroup.coe_inclusion hUD (⟨v, hvU⟩ : ↥U)
    rw [show πU (⟨v, hvU⟩ : ↥U) = π (Subgroup.inclusion hUD ⟨v, hvU⟩) from rfl, hin]
    exact hπv
  have hgenD2_xy : (⊤ : Subgroup ↥D₂) =
      Subgroup.zpowers (⟨x, hx⟩ : ↥D₂) ⊔ Subgroup.zpowers (⟨y, hy⟩ : ↥D₂) :=
    closure_subtype D₂ x y hx hy (hgen.trans (hclosure_pair x y))
  have hsurj : Function.Surjective πU := by
    have htop : (⊤ : Subgroup ↥D₂) ≤ πU.range := by
      rw [hgenD2_xy]
      exact sup_le (Subgroup.zpowers_le.2 ⟨⟨u, huU⟩, hπUu⟩)
        (Subgroup.zpowers_le.2 ⟨⟨v, hvU⟩, hπUv⟩)
    intro g
    exact htop (Subgroup.mem_top g)
  have hcardD2_le_U : Nat.card ↥D₂ ≤ Nat.card ↥U :=
    Nat.card_le_card_of_surjective πU hsurj
  have hcardU : Nat.card ↥U = Nat.card ↥D₂ :=
    le_antisymm hcardU_le hcardD2_le_U
  have hbij : Function.Bijective πU :=
    (Nat.bijective_iff_surjective_and_card πU).2 ⟨hsurj, hcardU⟩
  have hUisoD2 : Nonempty (↥U ≃* ↥D₂) := ⟨MulEquiv.ofBijective πU hbij⟩
  have hπ_one_of_mem_D1 : ∀ g : ↥D, (g : G) ∈ D₁ → π g = 1 := by
    intro g hgD₁
    have hcomp := ddProdEquiv_apply_mul hd g
    have h1mem : ((ddProdEquiv hd g).1 : G) ∈ D₁ := (ddProdEquiv hd g).1.2
    have h2mem : ((ddProdEquiv hd g).2 : G) ∈ D₂ := (ddProdEquiv hd g).2.2
    have h2D₁ : ((ddProdEquiv hd g).2 : G) ∈ D₁ := by
      have h : ((ddProdEquiv hd g).2 : G) = ((ddProdEquiv hd g).1 : G)⁻¹ * (g : G) := by
        rw [← hcomp]; group
      rw [h]
      exact mul_mem (inv_mem h1mem) hgD₁
    have h1bot : ((ddProdEquiv hd g).2 : G) ∈ D₁ ⊓ D₂ := ⟨h2D₁, h2mem⟩
    rw [hd.inf_eq, mem_bot] at h1bot
    have h1one : (ddProdEquiv hd g).2 = 1 := Subtype.ext h1bot
    rw [hπ_apply]
    exact h1one
  have hinf : U ⊓ D₁ = ⊥ := by
    rw [eq_bot_iff]
    rintro g ⟨hgU, hgD₁⟩
    have hg_one : (⟨g, hgU⟩ : ↥U) = 1 := by
      apply hbij.1
      have hπg : πU (⟨g, hgU⟩ : ↥U) = 1 := by
        have hin : Subgroup.inclusion hUD (⟨g, hgU⟩ : ↥U) = ⟨g, hUD hgU⟩ := by
          apply Subtype.ext
          simpa using Subgroup.coe_inclusion hUD (⟨g, hgU⟩ : ↥U)
        rw [show πU (⟨g, hgU⟩ : ↥U) = π (Subgroup.inclusion hUD ⟨g, hgU⟩) from rfl, hin]
        exact hπ_one_of_mem_D1 _ hgD₁
      simpa using hπg
    exact congrArg Subtype.val hg_one
  have hx_eq_u : x = u * ε₁⁻¹ := by rw [hu_def]; group
  have hy_eq_v : y = v * ε₂⁻¹ := by rw [hv_def]; group
  have hD2_le_UD1 : D₂ ≤ U ⊔ D₁ := by
    rw [hgen]
    refine (Subgroup.closure_le (U ⊔ D₁)).2 fun z hz => ?_
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
    rcases hz with hz | hz
    · rw [hz, hx_eq_u]
      exact mul_mem (Subgroup.mem_sup_left huU) (Subgroup.mem_sup_right (inv_mem hε₁))
    · rw [hz, hy_eq_v]
      exact mul_mem (Subgroup.mem_sup_left hvU) (Subgroup.mem_sup_right (inv_mem hε₂))
  have hsup : U ⊔ D₁ = D := by
    apply le_antisymm
    · exact sup_le hUD hd.le_left
    · rw [← hd.sup_eq]
      exact sup_le le_sup_right hD2_le_UD1
  have hu_cent : u ∈ Subgroup.centralizer (D₁ : Set G) := by
    rw [hu_def, mem_centralizer_iff]
    intro d hdD₁
    calc d * (x * ε₁) = (d * x) * ε₁ := by group
      _ = (x * d) * ε₁ := by rw [hd.comm hdD₁ hx]
      _ = x * (d * ε₁) := by group
      _ = x * (ε₁ * d) := by rw [hε₁c d hdD₁]
      _ = x * ε₁ * d := by group
  have hv_cent : v ∈ Subgroup.centralizer (D₁ : Set G) := by
    rw [hv_def, mem_centralizer_iff]
    intro d hdD₁
    calc d * (y * ε₂) = (d * y) * ε₂ := by group
      _ = (y * d) * ε₂ := by rw [hd.comm hdD₁ hy]
      _ = y * (d * ε₂) := by group
      _ = y * (ε₂ * d) := by rw [hε₂c d hdD₁]
      _ = y * ε₂ * d := by group
  have hU_cent : U ≤ Subgroup.centralizer (D₁ : Set G) := by
    rw [hU_def]
    refine (Subgroup.closure_le _).2 fun z hz => ?_
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
    rcases hz with hz | hz
    · rw [hz]; exact hu_cent
    · rw [hz]; exact hv_cent
  have hcommU : U ≤ Subgroup.centralizer (D₁ : Set G) := hU_cent
  obtain ⟨eU⟩ := hUisoD2
  have hdihU : IsDihNonab U := by
    obtain ⟨b, hb, ⟨eDb'⟩⟩ := hd.dih₂
    exact ⟨b, hb, ⟨eU.trans eDb'⟩⟩
  have hsup' : D₁ ⊔ U = D := by rw [sup_comm]; exact hsup
  have hinf' : D₁ ⊓ U = ⊥ := by rw [inf_comm]; exact hinf
  refine ⟨U, ?_, ⟨eU⟩, ?_⟩
  · exact { sup_eq := hsup', inf_eq := hinf', commute := hcommU, dih₁ := hd.dih₁, dih₂ := hdihU }
  · rw [hU_def, hu_def, hv_def]

end CFSG.GH72
