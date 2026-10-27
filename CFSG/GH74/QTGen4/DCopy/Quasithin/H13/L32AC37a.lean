module

public import CFSG.Quasithin.H13.L32AC37a
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.L32A74
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.L32ASk1
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.L32NSet14Gen

public section

namespace CFSG.Quasithin.H13.L32A.C

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.LieType.BorelTits

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G] {T L V H V₂ : Subgroup G}

theorem relIndex_T_L2T_F4 (h4 : Lemma14_7_4_two_three_F4) (S : Setting147 G T L V H)
    (hV2 : A6.IsV2 T V V₂) : T.relIndex (L₁Of L V₂ ⊔ T) = 3 := by
  have hTH : T ≤ H := le_sup_right.trans S.hz.1.1
  have hO : pCoreOf 2 (A6.g1 T V) ≤ T := pCoreOf_le_of_le S.hyp (hTH.trans S.hz.2.1)
  have hI := (h4 G T L V V₂ S.hyp hV2).2.1
  have hIT : i2 T V V₂ ⊔ T = L₁Of L V₂ ⊔ T := by
    rw [hI]
    exact le_antisymm (sup_le (sup_le le_sup_left (hO.trans le_sup_right)) le_sup_right)
      (sup_le (le_sup_left.trans le_sup_left) le_sup_right)
  have hTN : T ≤ Subgroup.normalizer (i2 T V V₂ : Set G) :=
    hV2.2.2.1.trans (h4 G T L V V₂ S.hyp hV2).1.2
  have hsyl : IsSylowTwoOf (T ⊓ i2 T V V₂) (i2 T V V₂) :=
    A4.isSylowTwoOf_inf_normal
      (isSylowTwoOf_of_quasithinIsSylowTwo S.hyp.fsu.sylow (le_sup_right : T ≤ i2 T V V₂ ⊔ T))
      le_sup_left (sup_le Subgroup.le_normalizer hTN)
  rw [← hIT, U3.relIndex_sup_eq hTN, inf_comm]
  exact U3.relIndex_eq_three_of_quot
    ((quasithinO2QuotientIso_iff _ _).2 (h4 G T L V V₂ S.hyp hV2).2.2.1) hsyl

theorem inf_centralizer_le_T_F4 (h1222 : Stmt12_2_2_F4) (h1332 : Stmt13_3_2_F4) (h1334 : A6.Stmt13_3_4_F4)
    (h4 : Lemma14_7_4_two_three_F4) (S : Setting147 G T L V H) (hV2 : A6.IsV2 T V V₂) :
    (L₁Of L V₂ ⊔ T) ⊓ Subgroup.centralizer (V₂ : Set G) ≤ T := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hMod := stmtL32NModule_of_inputs_F4 h1332 h1334
  have : IsMulCommutative ↥V := (hMod G T L V S.hyp.hyp S.hyp.fsu).1.1
  have S14 := Hyp147.set14_F4 S.hyp h1222 h1332 h1334 hV2
  obtain ⟨z, a, b, hz, hz1, ha, haV, hb, hbV⟩ := S14.exists_basis_F4
  obtain ⟨l, hl, hlz⟩ := S14.exists_L2_F4 hz hz1 ha haV hb hbV
  set C' := (L₁Of L V₂ ⊔ T) ⊓ Subgroup.centralizer (V₂ : Set G) with hC'
  have hTC : T ≤ Subgroup.normalizer (C' : Set G) := fun t ht =>
    Subgroup.inf_normalizer_le_normalizer_inf ⟨Subgroup.le_normalizer (Subgroup.mem_sup_right ht),
      mem_normalizer_centralizer' (hV2.2.2.1 ht)⟩
  have hle : C' ⊔ T ≤ L₁Of L V₂ ⊔ T := sup_le inf_le_left le_sup_right
  have hm := Subgroup.relIndex_mul_relIndex T (C' ⊔ T) (L₁Of L V₂ ⊔ T) le_sup_right hle
  rw [relIndex_T_L2T_F4 h4 S hV2] at hm
  have hd : T.relIndex (C' ⊔ T) ∣ 3 := Dvd.intro _ hm
  rcases (Nat.dvd_prime Nat.prime_three).mp hd with h1 | h3
  · exact le_sup_left.trans (Subgroup.relIndex_eq_one.mp h1)
  · exfalso
    rw [h3] at hm
    have h1 : (C' ⊔ T).relIndex (L₁Of L V₂ ⊔ T) = 1 := by omega
    have hlCT : l ∈ C' ⊔ T := Subgroup.relIndex_eq_one.mp h1 (Subgroup.mem_sup_left hl)
    obtain ⟨c, hc, t, ht, rfl⟩ := (F1.mem_sup_iff_exists_mul_of_normalizes hTC).mp hlCT
    apply haV
    have hzV₂ : z ∈ V₂ := hV2.1 hz
    have hcz : c * z * c⁻¹ = z := by
      rw [← Subgroup.mem_centralizer_iff.mp hc.2 z hzV₂, mul_inv_cancel_right]
    have htz : t * z * t⁻¹ = z := conj_fsuV1 hz ht
    have e : c * t * z * (c * t)⁻¹ = c * (t * z * t⁻¹) * c⁻¹ := by group
    rw [← hlz, e, htz, hcz]
    exact hz

theorem sq_mem_centralizer_F4 (S : Setting147 G T L V H) (h1332 : Stmt13_3_2_F4)
    (h1334 : A6.Stmt13_3_4_F4) (hV2 : A6.IsV2 T V V₂) {x : G}
    (hx : x ∈ centralizerMod (fsuV1 T V) H V₂) :
    x ^ 2 ∈ Subgroup.centralizer (V₂ : Set G) := by
  have hMod := stmtL32NModule_of_inputs_F4 h1332 h1334
  obtain ⟨-, -, -, hV12, -⟩ := hMod G T L V S.hyp.hyp S.hyp.fsu
  obtain ⟨-, hxN, hxc⟩ := hx
  have hfix : ∀ d ∈ fsuV1 T V, x * d * x⁻¹ = d := by
    intro d hd
    by_cases hd1 : d = 1
    · rw [hd1, mul_one, mul_inv_cancel]
    · have hxd := (Subgroup.mem_normalizer_iff.mp hxN d).mp hd
      refine eq_of_card_two hV12 hxd hd ?_ hd1
      intro h
      apply hd1
      have h2 : x⁻¹ * (x * d * x⁻¹) * x = x⁻¹ * 1 * x := by rw [h]
      simpa [mul_assoc] using h2
  have hV2sq : ∀ v ∈ V₂, v * v = 1 := fun v hv => by
    rw [← pow_two]
    exact (hMod G T L V S.hyp.hyp S.hyp.fsu).1.2 v (hV2.2.1 hv)
  rw [Subgroup.mem_centralizer_iff]
  intro v hv
  have h1 := hxc v hv
  set d := x * v * x⁻¹ * v⁻¹ with hd
  have hxv : x * v * x⁻¹ = d * v := by rw [hd]; group
  have hd2 : d * d = 1 := hV2sq d (hV2.1 h1)
  have hconj : x ^ 2 * v * (x ^ 2)⁻¹ = v := by
    have e : x ^ 2 * v * (x ^ 2)⁻¹ = x * (x * v * x⁻¹) * x⁻¹ := by rw [pow_two]; group
    rw [e, hxv, show x * (d * v) * x⁻¹ = (x * d * x⁻¹) * (x * v * x⁻¹) by group, hfix d h1,
      hxv, ← mul_assoc, hd2, one_mul]
  calc v * x ^ 2 = (x ^ 2 * v * (x ^ 2)⁻¹) * x ^ 2 := by rw [hconj]
    _ = x ^ 2 * v := by group

end CFSG.Quasithin.H13.L32A.C
