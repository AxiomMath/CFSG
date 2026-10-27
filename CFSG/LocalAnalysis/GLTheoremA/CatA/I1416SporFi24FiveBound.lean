module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.I1416SporFi23FiveRow

public section

set_option linter.unusedSectionVars false
set_option maxRecDepth 100000

namespace CFSG.LocalAnalysis.GLTheoremA.Fi24FiveBound

theorem card_centralizer_le_of_equiv {G₀ G₁ : Type} [Group G₀] [Group G₁] {H₀ : Subgroup G₀}
    {H₁ : Subgroup G₁} (φ : ↥H₀ ≃* ↥H₁) {N : ℕ}
    (hH : ∀ x : ↥H₁, orderOf x = 5 → Nat.card ↥(Subgroup.centralizer ({x} : Set ↥H₁)) ≤ N)
    (g : ↥H₀) (hg : orderOf g = 5) :
    Nat.card ↥(Subgroup.centralizer ({g} : Set ↥H₀)) ≤ N := by
  have hmap := CFSG.HardMathSupport.Dickson.I271.map_centralizer_singleton φ g
  rw [← Subgroup.card_map_of_injective (f := φ.toMonoidHom) φ.injective, hmap]
  exact hH _ (by rw [MulEquiv.orderOf_eq]; exact hg)

theorem card_centralizer_fi23_le
    (s : CFSG.Sporadic.Fi23.J) (hs : orderOf s = 5) :
    Nat.card ↥(Subgroup.centralizer ({s} : Set CFSG.Sporadic.Fi23.J)) ≤ 25200 := by
  obtain ⟨m, hm, hm21, -⟩ := CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Fi23Five.card_centralizer_five s hs
  rw [hm]
  omega

end CFSG.LocalAnalysis.GLTheoremA.Fi24FiveBound

namespace CFSG.LocalAnalysis.GLTheoremA.Fi24FiveBound

open CFSG.Sporadic.Fi24 (R J JR jR tR cls D24 M)

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
attribute [local instance] CFSG.Sporadic.Fi24.rAction

section Bound

@[expose] def fixD24 (r : R) : Set R := {x | x ∈ D24 ∧ x * r = r * x}

theorem card_inf_tR_le (v : J) (hv : orderOf v = 5) (hvt : jR v * tR = tR * jR v) :
    Nat.card ↥(Subgroup.centralizer ({jR v} : Set R) ⊓ Subgroup.centralizer ({tR} : Set R)) ≤
      2 * 25200 := by
  haveI := CFSG.Sporadic.Fi24.normal_JR
  set H := Subgroup.centralizer ({jR v} : Set R) ⊓ Subgroup.centralizer ({tR} : Set R)
  have hvM : v ∈ M := (CFSG.Sporadic.Fi24.commute_tR_iff v).1 hvt
  have hvMR : jR v ∈ CFSG.Sporadic.Fi24.MR := ⟨v, hvM, rfl⟩
  set vM : ↥CFSG.Sporadic.Fi24.MR := ⟨jR v, hvMR⟩
  have hle : JR ⊓ H ≤ (Subgroup.centralizer ({vM} : Set ↥CFSG.Sporadic.Fi24.MR)).map
      CFSG.Sporadic.Fi24.MR.subtype := by
    intro x hx
    obtain ⟨hxJ, hxH⟩ := Subgroup.mem_inf.1 hx
    obtain ⟨hxv, hxt⟩ := Subgroup.mem_inf.1 hxH
    obtain ⟨g, rfl⟩ := CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Fi24Three.exists_jR_of_mem hxJ
    have hxt' := hxt
    rw [Subgroup.mem_centralizer_singleton_iff] at hxt'
    have hgM : g ∈ M := (CFSG.Sporadic.Fi24.commute_tR_iff g).1 hxt'
    have hgMR : jR g ∈ CFSG.Sporadic.Fi24.MR := ⟨g, hgM, rfl⟩
    have h := hxv
    rw [Subgroup.mem_centralizer_singleton_iff] at h
    refine ⟨⟨jR g, hgMR⟩, ?_, rfl⟩
    rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff]
    exact Subtype.ext h
  have hcardM : Nat.card ↥(Subgroup.centralizer ({vM} : Set ↥CFSG.Sporadic.Fi24.MR)) ≤ 25200 := by
    haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
    have hv5 : v ^ 5 = 1 := hv ▸ pow_orderOf_eq_one v
    have hv1 : v ≠ 1 := fun h1 => by rw [h1, orderOf_one] at hv; exact absurd hv (by norm_num)
    have hvM5 : vM ^ 5 = 1 := Subtype.ext (by rw [Subgroup.coe_pow, ← map_pow, hv5, map_one]; rfl)
    have hvM1 : vM ≠ 1 := fun h1 => hv1 (CFSG.Sporadic.Fi24.jR_injective
      (by rw [map_one]; exact congrArg Subtype.val h1))
    exact card_centralizer_le_of_equiv
      (CFSG.Sporadic.Fi24.fi23EquivMR.trans CFSG.Sporadic.Fi23.fi23EquivJ)
      card_centralizer_fi23_le vM (orderOf_eq_prime hvM5 hvM1)
  have h1 : Nat.card ↥(JR ⊓ H) ≤ 25200 :=
    (Subgroup.card_le_of_le hle).trans
      (by rw [Subgroup.card_map_of_injective CFSG.Sporadic.Fi24.MR.subtype_injective]; exact hcardM)
  have h2 := Subgroup.relIndex_mul_card JR H
  have h3 : JR.relIndex H ≤ 2 := Nat.le_of_dvd (by norm_num)
    (CFSG.Sporadic.Fi24.index_JR ▸ Subgroup.relIndex_dvd_index_of_normal JR H)
  rw [← h2]
  calc JR.relIndex H * Nat.card ↥(JR ⊓ H) ≤ 2 * 25200 := Nat.mul_le_mul h3 h1

theorem card_inf_D24_le (w : J) (hw : orderOf w = 5) {x : R} (hx : x ∈ D24)
    (hxw : x * jR w = jR w * x) :
    Nat.card ↥(Subgroup.centralizer ({jR w} : Set R) ⊓ Subgroup.centralizer ({x} : Set R)) ≤
      2 * 25200 := by
  obtain ⟨g, hg⟩ := CFSG.Sporadic.Fi24.exists_conj_eq_tR hx
  have hx' : x = (jR g)⁻¹ * tR * ((jR g)⁻¹)⁻¹ := by rw [← hg]; group
  rw [hx', CFSG.Sporadic.Fi23.card_centralizer_inf_conj]
  have he : ((jR g)⁻¹)⁻¹ * jR w * (jR g)⁻¹ = jR (g * w * g⁻¹) := by
    simp only [inv_inv, map_mul, map_inv]
  rw [he]
  refine card_inf_tR_le _ (by
    rw [show g * w * g⁻¹ = MulAut.conj g w from rfl, MulEquiv.orderOf_eq, hw]) ?_
  rw [← hg]
  simp only [map_mul, map_inv]
  calc jR g * jR w * (jR g)⁻¹ * (jR g * x * (jR g)⁻¹)
      = jR g * (jR w * x) * (jR g)⁻¹ := by group
    _ = jR g * (x * jR w) * (jR g)⁻¹ := by rw [hxw]
    _ = jR g * x * (jR g)⁻¹ * (jR g * jR w * (jR g)⁻¹) := by group

theorem card_centralizer_le_of_ncard (w : J) (hw : orderOf w = 5)
    (hF : (fixD24 (jR w)).ncard = 36) :
    Nat.card ↥(Subgroup.centralizer ({w} : Set J)) ≤ 907200 := by
  haveI := CFSG.Sporadic.Fi24.normal_JR
  set r := jR w
  obtain ⟨x₀, hx₀⟩ : (fixD24 r).Nonempty := Set.nonempty_of_ncard_ne_zero (by rw [hF]; norm_num)
  have hact : ∀ c ∈ Subgroup.centralizer ({r} : Set R), ∀ x ∈ fixD24 r,
      c * x * c⁻¹ ∈ fixD24 r := by
    rintro c hc x ⟨hx, hxr⟩
    refine ⟨CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Fi24Five.D24_conj hx c, ?_⟩
    have hcr := hc
    rw [Subgroup.mem_centralizer_singleton_iff] at hcr
    calc c * x * c⁻¹ * r = c * x * (c⁻¹ * r) := by group
      _ = c * x * (r * c⁻¹) := by
          rw [show c⁻¹ * r = r * c⁻¹ by
            calc c⁻¹ * r = c⁻¹ * (r * c) * c⁻¹ := by group
              _ = c⁻¹ * (c * r) * c⁻¹ := by rw [hcr]
              _ = r * c⁻¹ := by group]
      _ = c * (x * r) * c⁻¹ := by group
      _ = c * (r * x) * c⁻¹ := by rw [hxr]
      _ = (c * r) * x * c⁻¹ := by group
      _ = r * (c * x * c⁻¹) := by rw [hcr]; group
  obtain ⟨m, hm, hm36⟩ := CFSG.LocalAnalysis.GLTheoremA.I1416Rows.CentOrbit.card_centralizer_eq_mul_orbit hact hx₀ rfl
  have hN := card_inf_D24_le w hw hx₀.1 hx₀.2
  have hCR : Nat.card ↥(Subgroup.centralizer ({r} : Set R)) ≤ 2 * 25200 * 36 := by
    rw [hm]; exact Nat.mul_le_mul hN (hF ▸ hm36)
  have hmap : (Subgroup.centralizer ({w} : Set J)).map jR =
      Subgroup.centralizer ({r} : Set R) ⊓ JR := by
    rw [CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Fi24Five.map_centralizer_singleton_eq CFSG.Sporadic.Fi24.jR_injective w, CFSG.Sporadic.Fi24.range_jR]
  have hcJ : Nat.card ↥(Subgroup.centralizer ({w} : Set J)) =
      Nat.card ↥(JR ⊓ Subgroup.centralizer ({r} : Set R)) := by
    rw [inf_comm, ← hmap, Subgroup.card_map_of_injective CFSG.Sporadic.Fi24.jR_injective]
  have hrel := Subgroup.relIndex_mul_card JR (Subgroup.centralizer ({r} : Set R))
  have hne : JR.relIndex (Subgroup.centralizer ({r} : Set R)) ≠ 1 := by
    intro h1
    exact CFSG.Sporadic.Fi24.not_mem_JR_of_mem_D24 hx₀.1 (Subgroup.relIndex_eq_one.1 h1
      (by rw [Subgroup.mem_centralizer_singleton_iff]; exact hx₀.2))
  have hne0 : JR.relIndex (Subgroup.centralizer ({r} : Set R)) ≠ 0 := by
    intro h0
    have hd := Subgroup.relIndex_dvd_index_of_normal JR (Subgroup.centralizer ({r} : Set R))
    rw [h0, CFSG.Sporadic.Fi24.index_JR] at hd
    norm_num at hd
  rw [hcJ]
  have h2 : 2 ≤ JR.relIndex (Subgroup.centralizer ({r} : Set R)) := by omega
  have := Nat.mul_le_mul_right (Nat.card ↥(JR ⊓ Subgroup.centralizer ({r} : Set R))) h2
  omega

theorem ncard_fixD24_jR (w : J) :
    (fixD24 (jR w)).ncard = Nat.card (CFSG.Sporadic.Fi24.ptFix (w : GL (Fin 781) (ZMod 3))) := by
  rw [← CFSG.Sporadic.Fi24.card_ptFix_eq]
  have e : fixD24 (jR w) = (fun k => cls k) '' {k : Fin 306936 | w • k = k} := by
    ext x
    constructor
    · rintro ⟨hx, hxr⟩
      obtain ⟨k, rfl⟩ := CFSG.Sporadic.Fi24.exists_cls hx
      exact ⟨k, (CFSG.Sporadic.Fi24.smul_eq_iff_comm_cls w k).2 hxr.symm, rfl⟩
    · rintro ⟨k, hk, rfl⟩
      exact ⟨CFSG.Sporadic.Fi24.cls_mem k, ((CFSG.Sporadic.Fi24.smul_eq_iff_comm_cls w k).1 hk).symm⟩
  rw [e, Set.ncard_image_of_injective _ CFSG.Sporadic.Fi24.cls_injective, ← Nat.card_coe_set_eq]
  rfl

end Bound

end CFSG.LocalAnalysis.GLTheoremA.Fi24FiveBound
