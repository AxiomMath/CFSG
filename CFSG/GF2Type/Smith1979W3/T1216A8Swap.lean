module

public import CFSG.LargeExtraspecial.S3Eight

public section

namespace CFSG.GF2Type.Smith1979W3

open CFSG.LargeExtraspecial

variable {G : Type} [Group G] [Finite G]

private theorem conj_mem_and_comm (S : Setting G) {h a x : G} (hzh : h * S.z * h⁻¹ = a)
    (hah : h * a * h⁻¹ = S.z) (hxM : x ∈ S.M) (hxa : x * a = a * x) :
    h * x * h⁻¹ ∈ S.M ∧ (h * x * h⁻¹) * a = a * (h * x * h⁻¹) := by
  have hxz : x * S.z = S.z * x := S.mem_M_iff.mp hxM
  have hz' : h⁻¹ * S.z * h = a := by rw [← hah]; group
  have ha' : h⁻¹ * a * h = S.z := by rw [← hzh]; group
  refine ⟨?_, ?_⟩
  · rw [S.mem_M_iff]
    calc h * x * h⁻¹ * S.z = h * x * (h⁻¹ * S.z * h) * h⁻¹ := by group
      _ = h * x * a * h⁻¹ := by rw [hz']
      _ = h * (x * a) * h⁻¹ := by group
      _ = h * (a * x) * h⁻¹ := by rw [hxa]
      _ = h * a * x * h⁻¹ := by group
      _ = (h * a * h⁻¹) * (h * x * h⁻¹) := by group
      _ = S.z * (h * x * h⁻¹) := by rw [hah]
  · calc h * x * h⁻¹ * a = h * x * (h⁻¹ * a * h) * h⁻¹ := by group
      _ = h * x * S.z * h⁻¹ := by rw [ha']
      _ = h * (x * S.z) * h⁻¹ := by group
      _ = h * (S.z * x) * h⁻¹ := by rw [hxz]
      _ = h * S.z * x * h⁻¹ := by group
      _ = (h * S.z * h⁻¹) * (h * x * h⁻¹) := by group
      _ = a * (h * x * h⁻¹) := by rw [hzh]

theorem exists_conj_eq_of_mem_QG (S : Setting G)
    (htrans : ∀ v w : S.Qt, v ≠ 0 → w ≠ 0 → S.q v = 0 → S.q w = 0 →
      ∃ m : S.M, (S.ρ m : S.Qt ≃ₗ[ZMod 2] S.Qt) v = w)
    {a a' : G} (ha : a ∈ S.QG) (ha2 : a * a = 1) (ha1 : a ≠ 1) (haz : a ≠ S.z)
    (ha' : a' ∈ S.QG) (ha'2 : a' * a' = 1) (ha'1 : a' ≠ 1) (ha'z : a' ≠ S.z) :
    ∃ m ∈ S.M, m * a * m⁻¹ = a' := by
  have ha2' : a ^ 2 = 1 := by rw [pow_two]; exact ha2
  have ha'2' : a' ^ 2 = 1 := by rw [pow_two]; exact ha'2
  have hqa : S.q (S.cl a) = 0 := (S.q_cl_eq_zero_iff ha).mpr ha2'
  have hqa' : S.q (S.cl a') = 0 := (S.q_cl_eq_zero_iff ha').mpr ha'2'
  have hca : S.cl a ≠ 0 := fun h => by
    rcases (S.cl_eq_zero_iff ha).mp h with h1 | h1
    exacts [ha1 h1, haz h1]
  have hca' : S.cl a' ≠ 0 := fun h => by
    rcases (S.cl_eq_zero_iff ha').mp h with h1 | h1
    exacts [ha'1 h1, ha'z h1]
  obtain ⟨m, hm⟩ := htrans (S.cl a) (S.cl a') hca hca' hqa hqa'
  have hcl : S.cl ((m : G) * a * (m : G)⁻¹) = S.cl a' := (S.ρ_cl m ha).symm.trans hm
  have hmQ : (m : G) * a * (m : G)⁻¹ ∈ S.QG := S.conj_mem_QG m.2 ha
  have htQ : a' * S.z ∈ S.QG := S.QG.mul_mem ha' S.z_mem_QG
  have ht1 : a' * S.z ≠ 1 := by
    intro h
    exact ha'z (by
      calc a' = (a' * S.z) * S.z := by rw [mul_assoc, S.z_mul_z, mul_one]
        _ = 1 * S.z := by rw [h]
        _ = S.z := one_mul _)
  have htz : a' * S.z ≠ S.z := by
    intro h
    exact ha'1 (by
      calc a' = (a' * S.z) * S.z := by rw [mul_assoc, S.z_mul_z, mul_one]
        _ = S.z * S.z := by rw [h]
        _ = 1 := S.z_mul_z)
  obtain ⟨u, hu, hu'⟩ := S.exists_conj_eq_mul_z htQ ht1 htz
  have hu'' : u * (a' * S.z) * u⁻¹ = a' := by
    rw [hu', mul_assoc, S.z_mul_z, mul_one]
  rcases (S.cl_eq_cl_iff hmQ ha').mp hcl with h | h
  · exact ⟨m, m.2, h.symm⟩
  · have hmam : (m : G) * a * (m : G)⁻¹ = a' * S.z := by
      have := congrArg (fun t => t * S.z) h
      simpa only [mul_assoc, S.z_mul_z, mul_one] using this.symm
    refine ⟨u * m, S.M.mul_mem (S.QG_le_M hu) m.2, ?_⟩
    calc (u * (m : G)) * a * (u * (m : G))⁻¹
        = u * ((m : G) * a * (m : G)⁻¹) * u⁻¹ := by group
      _ = u * (a' * S.z) * u⁻¹ := by rw [hmam]
      _ = a' := hu''

theorem card_sq_eq_z_eq_card_sq_eq (S : Setting G)
    (htrans : ∀ v w : S.Qt, v ≠ 0 → w ≠ 0 → S.q v = 0 → S.q w = 0 →
      ∃ m : S.M, (S.ρ m : S.Qt ≃ₗ[ZMod 2] S.Qt) v = w)
    (hb : ∃ g : G, g * S.z * g⁻¹ ∈ S.QG ∧ g * S.z * g⁻¹ ≠ S.z)
    {a : G} (ha : a ∈ S.QG) (ha2 : a * a = 1) (ha1 : a ≠ 1) (haz : a ≠ S.z) :
    Nat.card {x : G // x ∈ S.M ∧ x * a = a * x ∧ x * x = S.z} =
      Nat.card {x : G // x ∈ S.M ∧ x * a = a * x ∧ x * x = a} := by
  obtain ⟨g₀, hg₀Q, hg₀z⟩ := hb
  have hb2 : (g₀ * S.z * g₀⁻¹) * (g₀ * S.z * g₀⁻¹) = 1 := by
    rw [show (g₀ * S.z * g₀⁻¹) * (g₀ * S.z * g₀⁻¹) = g₀ * (S.z * S.z) * g₀⁻¹ by group,
      S.z_mul_z]
    group
  have hb1 : g₀ * S.z * g₀⁻¹ ≠ 1 := by
    intro h
    apply S.z_ne_one
    calc S.z = g₀⁻¹ * (g₀ * S.z * g₀⁻¹) * g₀ := by group
      _ = 1 := by rw [h]; group
  obtain ⟨m, -, hm⟩ := exists_conj_eq_of_mem_QG S htrans ha ha2 ha1 haz hg₀Q hb2 hb1 hg₀z
  set g : G := (m : G)⁻¹ * g₀ with hg_def
  have hga : a = g * S.z * g⁻¹ := by
    calc a = (m : G)⁻¹ * ((m : G) * a * (m : G)⁻¹) * (m : G) := by group
      _ = (m : G)⁻¹ * (g₀ * S.z * g₀⁻¹) * (m : G) := by rw [hm]
      _ = g * S.z * g⁻¹ := by rw [hg_def]; group
  set a' : G := g⁻¹ * S.z * g with ha'_def
  have hzQa : S.z ∈ S.Qa g := S.z_mem_Qa_of_mem_QG (g := g) (t := a) hga.symm ha haz
  have ha'Q : a' ∈ S.QG := by
    rw [S.Qa_eq_map] at hzQa
    obtain ⟨q, hq, hqz⟩ := hzQa
    have hqz' : g * q * g⁻¹ = S.z := by
      simpa only [MulAut.conj_apply, MulEquiv.coe_toMonoidHom] using hqz
    have hq' : q = a' := by
      rw [ha'_def]
      calc q = g⁻¹ * (g * q * g⁻¹) * g := by group
        _ = g⁻¹ * S.z * g := by rw [hqz']
    simpa [hq'] using hq
  have ha'2 : a' * a' = 1 := by
    rw [ha'_def, show (g⁻¹ * S.z * g) * (g⁻¹ * S.z * g) = g⁻¹ * (S.z * S.z) * g by group,
      S.z_mul_z]
    group
  have ha'1 : a' ≠ 1 := by
    intro h
    apply S.z_ne_one
    calc S.z = g * a' * g⁻¹ := by rw [ha'_def]; group
      _ = 1 := by rw [h]; group
  have ha'z : a' ≠ S.z := by
    intro h
    rw [ha'_def] at h
    have hgz : g * S.z = S.z * g := by
      calc g * S.z = g * (g⁻¹ * S.z * g) := by rw [h]
        _ = S.z * g := by group
    have hza : a = S.z := by
      calc a = g * S.z * g⁻¹ := hga
        _ = S.z := by rw [S.z_comm (S.mem_M_iff.mpr hgz)]; group
    exact haz hza
  obtain ⟨m', hm'M, hm'⟩ := exists_conj_eq_of_mem_QG S htrans ha ha2 ha1 haz ha'Q ha'2 ha'1 ha'z
  set h : G := g * m' with hh_def
  have hzh : h * S.z * h⁻¹ = a := by
    calc h * S.z * h⁻¹ = g * (m' * S.z * m'⁻¹) * g⁻¹ := by rw [hh_def]; group
      _ = g * S.z * g⁻¹ := by
        rw [show m' * S.z * m'⁻¹ = S.z by rw [S.z_comm hm'M]; group]
      _ = a := hga.symm
  have hah : h * a * h⁻¹ = S.z := by
    calc h * a * h⁻¹ = g * (m' * a * m'⁻¹) * g⁻¹ := by rw [hh_def]; group
      _ = g * a' * g⁻¹ := by rw [hm']
      _ = S.z := by rw [ha'_def]; group
  have hzh' : h⁻¹ * S.z * h = a := by rw [← hah]; group
  have hah' : h⁻¹ * a * h = S.z := by rw [← hzh]; group
  have hsq1 : ∀ x : G, x ∈ S.M → x * a = a * x → x * x = S.z →
      h * x * h⁻¹ ∈ S.M ∧ (h * x * h⁻¹) * a = a * (h * x * h⁻¹) ∧
        (h * x * h⁻¹) * (h * x * h⁻¹) = a := by
    intro x hxM hxa hx2
    obtain ⟨hmem, hcomm⟩ := conj_mem_and_comm S hzh hah hxM hxa
    exact ⟨hmem, hcomm, by
      calc (h * x * h⁻¹) * (h * x * h⁻¹) = h * (x * x) * h⁻¹ := by group
        _ = h * S.z * h⁻¹ := by rw [hx2]
        _ = a := hzh⟩
  have hsq2 : ∀ x : G, x ∈ S.M → x * a = a * x → x * x = a →
      h⁻¹ * x * h ∈ S.M ∧ (h⁻¹ * x * h) * a = a * (h⁻¹ * x * h) ∧
        (h⁻¹ * x * h) * (h⁻¹ * x * h) = S.z := by
    intro x hxM hxa hx2
    have hzh'' : h⁻¹ * S.z * (h⁻¹)⁻¹ = a := by simpa using hzh'
    have hah'' : h⁻¹ * a * (h⁻¹)⁻¹ = S.z := by simpa using hah'
    obtain ⟨hmem, hcomm⟩ := conj_mem_and_comm S hzh'' hah'' hxM hxa
    refine ⟨by simpa using hmem, by simpa using hcomm, ?_⟩
    calc (h⁻¹ * x * h) * (h⁻¹ * x * h) = h⁻¹ * (x * x) * h := by group
      _ = h⁻¹ * a * h := by rw [hx2]
      _ = S.z := hah'
  refine Nat.card_congr
    { toFun := fun x => ⟨h * x.1 * h⁻¹, (hsq1 x.1 x.2.1 x.2.2.1 x.2.2.2).1,
        (hsq1 x.1 x.2.1 x.2.2.1 x.2.2.2).2.1, (hsq1 x.1 x.2.1 x.2.2.1 x.2.2.2).2.2⟩
      invFun := fun x => ⟨h⁻¹ * x.1 * h, (hsq2 x.1 x.2.1 x.2.2.1 x.2.2.2).1,
        (hsq2 x.1 x.2.1 x.2.2.1 x.2.2.2).2.1, (hsq2 x.1 x.2.1 x.2.2.1 x.2.2.2).2.2⟩
      left_inv := fun x => Subtype.ext (by group)
      right_inv := fun x => Subtype.ext (by group) }

end CFSG.GF2Type.Smith1979W3
