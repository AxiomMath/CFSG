module

public import CFSG.GF2Type.Smith1979.IdxFourHLift
public import CFSG.GF2Type.Smith1979.IdxFourCoset
public import CFSG.GF2Type.Smith1979.IdxFourHSpace

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.GF2Type.Smith1979.IdxFour

open Subgroup Module QuadraticMap CFSG.LargeExtraspecial CFSG.RankThree.OrthogonalInvolutions

variable {G : Type} [Group G] [Finite G] {S : Setting G}

theorem z_mem_L0 {g : G} (H : S4.Hyp4 S g) : S.z ∈ S.L0 g :=
  ⟨S.z_mem_Qa_of_mem_QG rfl H.conj_mem H.conj_ne, S.z_mem_M⟩

theorem z_mem_QG_inf_Qa {g : G} (H : S4.Hyp4 S g) : S.z ∈ S.QG ⊓ S.Qa g :=
  ⟨S.z_mem_QG, S.z_mem_Qa_of_mem_QG rfl H.conj_mem H.conj_ne⟩

theorem QG_inf_Qa_le_L0 {g : G} : S.QG ⊓ S.Qa g ≤ S.L0 g :=
  fun _ hx => ⟨hx.2, S.QG_le_M hx.1⟩

theorem exists_involution_L0 {g : G} (H : S4.Hyp4 S g) (C : S4.Cons311 S g) {t : S.O}
    (ht : t ∈ S.Lbar g) (ht1 : t ≠ 1) :
    ∃ r : G, r ∈ S.L0 g ∧ r * r = 1 ∧ ∃ hr : r ∈ S.M, S.ρ ⟨r, hr⟩ = t := by
  obtain ⟨y, hyL, hyρ⟩ := (S4.mem_Lbar S).mp ht
  have hyQa : (y : G) ∈ (S.conjBy g).QG := hyL.1
  have hyV : (y : G) ∉ (S.QG ⊓ S.Qa g : Subgroup G) := fun h =>
    ht1 (by rw [← hyρ]; exact (S.ρ_eq_one_iff y).mpr h.1)
  have hzV : (S.conjBy g).z ∈ (S.QG ⊓ S.Qa g : Subgroup G) :=
    ⟨H.conj_mem, (S.conjBy g).z_mem_QG⟩
  have hcard : Nat.card (S.QG ⊓ S.Qa g : Subgroup G) = 2 ^ ((S.conjBy g).width + 1) := by
    rw [C.card_QG_inf_Qa, S.width_conjBy]
  have hk := card_sq_eq_one_coset (S.conjBy g) (V := S.QG ⊓ S.Qa g) inf_le_right hzV
    (fun x hx y hy => S.QG_inf_Qa_comm H.conj_ne hx hy) (fun x hx => S.QG_inf_Qa_sq H.conj_ne hx)
    hcard hyQa hyV
  have hpos : 0 < Nat.card {v : (S.QG ⊓ S.Qa g : Subgroup G) // ((y : G) * v) ^ 2 = 1} := by
    rw [hk]
    positivity
  obtain ⟨⟨v, hv⟩⟩ := (Nat.card_pos_iff.mp hpos).1
  have hvQ : (v : G) ∈ S.QG := v.2.1
  have hvM : (v : G) ∈ S.M := S.QG_le_M hvQ
  have hrM : (y : G) * v ∈ S.M := S.M.mul_mem y.2 hvM
  refine ⟨(y : G) * v, ⟨(S.Qa g).mul_mem hyL.1 v.2.2, hrM⟩, by rw [← pow_two]; exact hv, hrM, ?_⟩
  have : (⟨(y : G) * v, hrM⟩ : S.M) = y * ⟨v, hvM⟩ := rfl
  rw [this, map_mul, hyρ, (S.ρ_eq_one_iff ⟨v, hvM⟩).mpr hvQ, mul_one]

theorem comm_of_mem_L0 {g : G} (H : S4.Hyp4 S g) {r v : G} (hrL : r ∈ S.L0 g) (hrM : r ∈ S.M)
    (hv : v ∈ S.QG ⊓ S.Qa g)
    (hfix : (S.ρ ⟨r, hrM⟩ : S.Qt ≃ₗ[ZMod 2] S.Qt) (S.cl v) = S.cl v) : r * v = v * r := by
  have hrQa : r ∈ (S.conjBy g).QG := hrL.1
  have hvQa : v ∈ (S.conjBy g).QG := hv.2
  have hcl : S.cl (r * v * r⁻¹) = S.cl v := by
    rw [← S.ρ_cl ⟨r, hrM⟩ hv.1]
    exact hfix
  have hrvQ : r * v * r⁻¹ ∈ S.QG := S.conj_mem_QG hrM hv.1
  rcases (S.cl_eq_cl_iff hv.1 hrvQ).mp hcl.symm with h | h
  · calc r * v = r * v * r⁻¹ * r := by group
      _ = v * r := by rw [h]
  · exfalso
    have hcomm : r * v * r⁻¹ * v⁻¹ = S.z := by
      rw [h]
      have := S.z_comm_QG hv.1
      calc v * S.z * v⁻¹ = S.z * v * v⁻¹ := by rw [this]
        _ = S.z := by group
    rcases (S.conjBy g).commutator_eq_one_or_z hrQa hvQa with h2 | h2
    · exact S.z_ne_one (hcomm.symm.trans h2)
    · exact H.conj_ne (hcomm.symm.trans h2).symm

theorem exists_comm_form {s : S.M} {τ : S.O} (hs : S.ρ s = τ)
    (hsq : (s : G) * s = 1 ∨ (s : G) * s = S.z) {l : G} (hl : l ∈ S.M)
    (hρ : S.ρ ⟨l, hl⟩ = τ) (hll : l * l = 1) :
    ∃ u ∈ S.QG, l = (s : G) * u ∧ S.cl u ∈ fixO S τ := by
  have huM : (s : G)⁻¹ * l ∈ S.M := S.M.mul_mem (S.M.inv_mem s.2) hl
  have hρu : S.ρ ⟨(s : G)⁻¹ * l, huM⟩ = 1 := by
    have : (⟨(s : G)⁻¹ * l, huM⟩ : S.M) = s⁻¹ * ⟨l, hl⟩ := rfl
    rw [this, map_mul, map_inv, hs, hρ, inv_mul_cancel]
  have huQ : (s : G)⁻¹ * l ∈ S.QG := (S.ρ_eq_one_iff _).mp hρu
  set u : G := (s : G)⁻¹ * l with hu
  have hl_eq : l = (s : G) * u := by rw [hu]; group
  refine ⟨u, huQ, hl_eq, ?_⟩
  have h2 : (s : G) * u * ((s : G) * u) = 1 := by rw [← hl_eq]; exact hll
  have h1 : (s : G) * u * (s : G)⁻¹ = u⁻¹ * ((s : G) * s)⁻¹ := by
    calc (s : G) * u * (s : G)⁻¹ = ((s : G) * u * ((s : G) * u)) * (u⁻¹ * ((s : G) * s)⁻¹) := by
          group
      _ = u⁻¹ * ((s : G) * s)⁻¹ := by rw [h2, one_mul]
  have hss : S.cl (((s : G) * s)⁻¹) = 0 := by
    rcases hsq with h | h
    · rw [h, inv_one, S.cl_one]
    · rw [h, S.z_inv, S.cl_z]
  have hssQ : ((s : G) * s)⁻¹ ∈ S.QG := by
    rcases hsq with h | h
    · rw [h, inv_one]; exact S.QG.one_mem
    · rw [h, S.z_inv]; exact S.z_mem_QG
  rw [mem_fixO, ← hs, S.ρ_cl s huQ, h1, S.cl_mul (S.QG.inv_mem huQ) hssQ, S.cl_inv huQ, hss,
    add_zero]

theorem mul_sq_eq_one_iff {s : S.M} (hsq : (s : G) * s = 1 ∨ (s : G) * s = S.z) {u : G}
    (hu : u ∈ S.QG) (hcomm : (s : G) * u = u * s) :
    ((s : G) * u) * ((s : G) * u) = 1 ↔ (S.q (S.cl u) = 0 ↔ (s : G) * s = 1) := by
  have h1 : ((s : G) * u) * ((s : G) * u) = ((s : G) * s) * (u * u) := by
    calc ((s : G) * u) * ((s : G) * u) = (s : G) * (u * s) * u := by group
      _ = (s : G) * (s * u) * u := by rw [hcomm]
      _ = ((s : G) * s) * (u * u) := by group
  rw [h1]
  have hq : S.q (S.cl u) = 0 ↔ u * u = 1 := by rw [S.q_cl_eq_zero_iff hu, pow_two]
  have hz1 : S.z ≠ 1 := S.z_ne_one
  rcases hsq with h | h
  · rw [h, one_mul, hq]
    simp
  · rw [h, hq]
    rcases S.sq_eq_one_or_z hu with hu2 | hu2
    · have hu2' : u * u = 1 := by rwa [pow_two] at hu2
      simp [hu2', hz1]
    · have hu2' : u * u = S.z := by rwa [pow_two] at hu2
      simp [hu2', hz1, S.z_mul_z]

theorem outer_fusion {g : G} (H : S4.Hyp4 S g) (C : S4.Cons311 S g) {t : S.O}
    (ht : t ∈ S.Lbar g) (ht1 : t ≠ 1) (hout : fixO S t ≤ commO S t) {l : G} (hl : l ∈ S.M)
    (hll : l * l = 1) (hρ : S.ρ ⟨l, hl⟩ = t) : ∃ q ∈ S.QG, q * l * q⁻¹ ∈ S.L0 g := by
  have htt : t * t = 1 := S4.mul_self_of_mem_Lbar S H.conj_mem ht
  obtain ⟨r, hrL, hrr, hrM, hrρ⟩ := exists_involution_L0 H C ht ht1
  have hsq : ((⟨r, hrM⟩ : S.M) : G) * ((⟨r, hrM⟩ : S.M) : G) = 1 ∨
      ((⟨r, hrM⟩ : S.M) : G) * ((⟨r, hrM⟩ : S.M) : G) = S.z := Or.inl hrr
  obtain ⟨u, huQ, hleq, huF⟩ := exists_comm_form hrρ hsq hl hρ hll
  obtain ⟨v, hv⟩ := mem_commO.mp (hout huF)
  obtain ⟨q, hqQ, rfl⟩ := S.exists_cl v
  obtain ⟨u', hu'Q, hconj, hcl'⟩ := exists_conj_shift (s := ⟨r, hrM⟩) hrρ htt huQ hqQ
  refine ⟨q, hqQ, ?_⟩
  have hcl0 : S.cl u' = 0 := by
    rw [hcl', ← hv]
    have : (t : S.Qt ≃ₗ[ZMod 2] S.Qt) (S.cl q) + S.cl q = (t : S.Qt ≃ₗ[ZMod 2] S.Qt) (S.cl q) - S.cl q := by
      rw [sub_eq_add_vec (ZMod 2)]
    rw [this, hv, add_self_vec (ZMod 2)]
  have hu' : u' = 1 ∨ u' = S.z := (S.cl_eq_zero_iff hu'Q).mp hcl0
  have : q * l * q⁻¹ = r * u' := by rw [hleq]; exact hconj
  rw [this]
  rcases hu' with rfl | rfl
  · simpa using hrL
  · exact (S.L0 g).mul_mem hrL (z_mem_L0 H)

end CFSG.GF2Type.Smith1979.IdxFour
