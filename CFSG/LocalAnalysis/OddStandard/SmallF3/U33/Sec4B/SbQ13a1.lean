module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbQ13a0
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbQ13aCA
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Outside.OutSpecial
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Outside.OutAmbient
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Outside.OutNonab
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbP12f

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33.S4B

open Subgroup
open scoped Pointwise

variable {G : Type} [Group G] [Finite G] {t : G} {L S : Subgroup G} {x₁ x₂ lam rho tau om : G}

private theorem mem_normalizer_of_normalIn {H K : Subgroup G} (hK : NormalIn H K) {g : G}
    (hg : g ∈ K) : g ∈ normalizer (H : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro x
  exact ⟨fun hx => hK.2 g hg x hx, fun hx => by
    have h1 := hK.2 g⁻¹ (K.inv_mem hg) (g * x * g⁻¹) hx
    have h2 : g⁻¹ * (g * x * g⁻¹) * g⁻¹⁻¹ = x := by group
    rwa [h2] at h1⟩

private theorem map_center_subtype (H : Subgroup G) :
    (Subgroup.center ↥H).map H.subtype = H ⊓ Subgroup.centralizer ((H : Subgroup G) : Set G) := by
  ext y
  rw [Subgroup.mem_map, Subgroup.mem_inf, Subgroup.mem_centralizer_iff]
  constructor
  · rintro ⟨x, hx, rfl⟩
    refine ⟨x.2, fun h hh => ?_⟩
    exact congrArg Subtype.val (Subgroup.mem_center_iff.mp hx ⟨h, hh⟩)
  · rintro ⟨hy, hcent⟩
    refine ⟨⟨y, hy⟩, ?_, rfl⟩
    rw [Subgroup.mem_center_iff]
    intro g
    exact Subtype.ext (hcent g g.2)

private theorem map_centralizer_subtype_singleton (H : Subgroup G) (x : G) (hx : x ∈ H) :
    (Subgroup.centralizer ({⟨x, hx⟩} : Set ↥H)).map H.subtype =
      H ⊓ Subgroup.centralizer ({x} : Set G) := by
  ext y
  rw [Subgroup.mem_map, Subgroup.mem_inf, Subgroup.mem_centralizer_singleton_iff]
  constructor
  · rintro ⟨z, hz, rfl⟩
    rw [Subgroup.mem_centralizer_singleton_iff] at hz
    exact ⟨z.2, congrArg Subtype.val hz⟩
  · rintro ⟨hy, hcent⟩
    refine ⟨⟨y, hy⟩, ?_, rfl⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact Subtype.ext hcent

private theorem exists_noncomm_of_not_mem_fourGrp (h : Q13Om t L S x₁ x₂ lam rho tau om)
    {Q : Subgroup G} (hQ : Q = ctxQ t tau x₁ x₂ rho) {x : G} (hx : x ∈ Q)
    (hxV : x ∉ fourGrp x₁ x₂) (hZ : Q ⊓ Subgroup.centralizer ((Q : Subgroup G) : Set G) =
      fourGrp x₁ x₂) :
    ∃ g : ↥Q, g * ⟨x, hx⟩ ≠ ⟨x, hx⟩ * g := by
  by_contra hcon
  simp only [not_exists, not_not] at hcon
  apply hxV
  have hcent : x ∈ Subgroup.centralizer ((Q : Subgroup G) : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro q hq
    exact congrArg Subtype.val (hcon ⟨q, hq⟩)
  have hmem : x ∈ Q ⊓ Subgroup.centralizer ((Q : Subgroup G) : Set G) := ⟨hx, hcent⟩
  rwa [hZ] at hmem

theorem q13a_rho_norm_Q (h : Q13Om t L S x₁ x₂ lam rho tau om) :
    rho ∈ normalizer ((ctxQ t tau x₁ x₂ rho : Subgroup G) : Set G) :=
  mem_normalizer_of_normalIn h.c11.normal_Q (q13a_mem_M h).2.2.1

theorem q13a_Q_nonab (h : Q13Om t L S x₁ x₂ lam rho tau om) :
    ∃ a b : G, a ∈ ctxQ t tau x₁ x₂ rho ∧ b ∈ ctxQ t tau x₁ x₂ rho ∧ a * b ≠ b * a := by
  obtain ⟨e⟩ := h.syl
  obtain ⟨a, b, hab⟩ := Outside.sylSL_nonabelian
  refine ⟨e.symm a, e.symm b, (e.symm a).2, (e.symm b).2, ?_⟩
  intro hcon
  apply hab
  have hsub : e.symm a * e.symm b = e.symm b * e.symm a := Subtype.ext hcon
  simpa using congrArg e hsub

theorem q13a_fpfNonab (h : Q13Om t L S x₁ x₂ lam rho tau om) :
    Outside.FpfNonab ↥(ctxQ t tau x₁ x₂ rho)
      (Outside.conjAut (ctxQ t tau x₁ x₂ rho) rho (q13a_rho_norm_Q h)) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [l12_card_Q h.c11]; norm_num
  · obtain ⟨a, b, ha, hb, hab⟩ := q13a_Q_nonab h
    exact ⟨⟨a, ha⟩, ⟨b, hb⟩, fun hc => hab (congrArg Subtype.val hc)⟩
  · rw [← Outside.conjAut_pow (ctxQ t tau x₁ x₂ rho) (q13a_rho_norm_Q h) 3
      (pow_mem (q13a_rho_norm_Q h) 3)]
    apply MulEquiv.ext
    intro g
    apply Subtype.ext
    rw [Outside.conjAut_coe, q13a_rho_cube h]
    simp
  · intro g hg
    have hcoe := Outside.conjAut_coe (ctxQ t tau x₁ x₂ rho) rho (q13a_rho_norm_Q h) g
    have hfix : rho * (g : G) * rho⁻¹ = (g : G) := by
      rw [← hcoe, hg]
    exact Subtype.ext (l12_cent_Q_rho h.c11 g g.2 (mul_inv_eq_iff_eq_mul.mp hfix).symm)

theorem q13a_ZQ (h : Q13Om t L S x₁ x₂ lam rho tau om) :
    ctxQ t tau x₁ x₂ rho ⊓ centralizer ((ctxQ t tau x₁ x₂ rho : Subgroup G) : Set G) =
      fourGrp x₁ x₂ := by
  have hQO : ctxQ t tau x₁ x₂ rho ≤ ctxO t tau x₁ x₂ :=
    (l12_Q_le_R h.c11).trans h.c11.R_le_O
  have hVle : fourGrp x₁ x₂ ≤ ctxQ t tau x₁ x₂ rho ⊓
      Subgroup.centralizer ((ctxQ t tau x₁ x₂ rho : Subgroup G) : Set G) := by
    intro v hv
    have hcent : v ∈ Subgroup.centralizer
        ((ctxQ t tau x₁ x₂ rho : Subgroup G) : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro q hq
      have hvO : v ∈ ctxO t tau x₁ x₂ ⊓
          Subgroup.centralizer ((ctxO t tau x₁ x₂ : Subgroup G) : Set G) := by
        rw [h.c11.center_O]; exact hv
      exact (Subgroup.mem_centralizer_iff.mp hvO.2) q (hQO hq)
    exact ⟨q13a_V_le_Q h hv, hcent⟩
  have hcardV : Nat.card ↥(fourGrp x₁ x₂) = 4 := h.c11.wreath.fourGrp_eq_omega.2.2
  have hcardZ : Nat.card ↥(ctxQ t tau x₁ x₂ rho ⊓
      Subgroup.centralizer ((ctxQ t tau x₁ x₂ rho : Subgroup G) : Set G)) = 4 := by
    have hmap := map_center_subtype (ctxQ t tau x₁ x₂ rho)
    have hcenter := (q13a_fpfNonab h).card_center
    calc Nat.card ↥(ctxQ t tau x₁ x₂ rho ⊓
          Subgroup.centralizer ((ctxQ t tau x₁ x₂ rho : Subgroup G) : Set G))
        = Nat.card ↥((Subgroup.center ↥(ctxQ t tau x₁ x₂ rho)).map
            (ctxQ t tau x₁ x₂ rho).subtype) := by rw [hmap]
      _ = Nat.card ↥(Subgroup.center ↥(ctxQ t tau x₁ x₂ rho)) :=
          Subgroup.card_subtype _ _
      _ = 4 := hcenter
  exact (Subgroup.eq_of_le_of_card_ge hVle (by rw [hcardZ, hcardV])).symm

theorem q13a_Q_comm (h : Q13Om t L S x₁ x₂ lam rho tau om) :
    ⁅ctxQ t tau x₁ x₂ rho, ctxQ t tau x₁ x₂ rho⁆ = fourGrp x₁ x₂ := by
  rw [← Subgroup.map_subtype_commutator (ctxQ t tau x₁ x₂ rho),
    (q13a_fpfNonab h).commutator_eq, map_center_subtype]
  exact q13a_ZQ h

theorem q13a_V_central (h : Q13Om t L S x₁ x₂ lam rho tau om) :
    ∀ v ∈ fourGrp x₁ x₂, ∀ q ∈ ctxQ t tau x₁ x₂ rho, v * q = q * v := by
  intro v hv q hq
  have hcent : v ∈ Subgroup.centralizer
      ((ctxQ t tau x₁ x₂ rho : Subgroup G) : Set G) := by
    have hv' : v ∈ ctxQ t tau x₁ x₂ rho ⊓
        Subgroup.centralizer ((ctxQ t tau x₁ x₂ rho : Subgroup G) : Set G) := by
      rw [q13a_ZQ h]; exact hv
    exact hv'.2
  exact (Subgroup.mem_centralizer_iff.mp hcent q hq).symm

theorem q13a_x₁_not_mem_V (h : Q13Om t L S x₁ x₂ lam rho tau om) :
    x₁ ∉ fourGrp x₁ x₂ := by
  intro hx
  have h2 : x₁ ^ 2 = 1 := h.c11.wreath.fourGrp_eq_omega.2.1.2 x₁ hx
  exact (q13a_x₁_facts h).2.2.2.2.2 h2

theorem q13a_card_CQ (h : Q13Om t L S x₁ x₂ lam rho tau om) {x : G}
    (hx : x ∈ ctxQ t tau x₁ x₂ rho) (hxV : x ∉ fourGrp x₁ x₂) :
    Nat.card ↥(ctxQ t tau x₁ x₂ rho ⊓ centralizer ({x} : Set G)) = 16 := by
  obtain ⟨e⟩ := h.syl
  have hxnc : ∃ g : ↥(ctxQ t tau x₁ x₂ rho),
      g * ⟨x, hx⟩ ≠ ⟨x, hx⟩ * g :=
    exists_noncomm_of_not_mem_fourGrp h rfl hx hxV (q13a_ZQ h)
  rw [← map_centralizer_subtype_singleton (ctxQ t tau x₁ x₂ rho) x hx,
    Subgroup.card_subtype]
  exact card_cent_of_equiv e hxnc

theorem q13a_CQ_x₁ (h : Q13Om t L S x₁ x₂ lam rho tau om) :
    ctxQ t tau x₁ x₂ rho ⊓ centralizer ({x₁} : Set G) = baseGrp x₁ x₂ := by
  have hx₁ : x₁ ∈ ctxQ t tau x₁ x₂ rho := (q13a_x₁_facts h).1
  have hx₁base : x₁ ∈ baseGrp x₁ x₂ := (q13a_x₁_facts h).2.1
  have hle : baseGrp x₁ x₂ ≤ ctxQ t tau x₁ x₂ rho ⊓ centralizer ({x₁} : Set G) := by
    intro a ha
    have hcent : a ∈ Subgroup.centralizer ({x₁} : Set G) := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      haveI : IsMulCommutative ↥(baseGrp x₁ x₂) := (h.c11.wreath.baseGrp_eq).1
      exact congrArg Subtype.val
        (mul_comm' (⟨a, ha⟩ : ↥(baseGrp x₁ x₂)) (⟨x₁, hx₁base⟩ : ↥(baseGrp x₁ x₂)))
    exact ⟨h.c11.base_le_Q ha, hcent⟩
  have hcard : Nat.card ↥(ctxQ t tau x₁ x₂ rho ⊓ centralizer ({x₁} : Set G)) = 16 :=
    q13a_card_CQ h hx₁ (q13a_x₁_not_mem_V h)
  have hbase : Nat.card ↥(baseGrp x₁ x₂) = 16 := (h.c11.wreath.baseGrp_eq).2.2
  exact (Subgroup.eq_of_le_of_card_ge hle (by rw [hcard, hbase])).symm

end CFSG.OddStandard.SmallF3.HarrisU33.S4B
