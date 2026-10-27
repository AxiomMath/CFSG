module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec10S109Cd

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {G : Type} [Group G]

theorem sec10C_Zdata [Finite G] (h3 : Asc82Sec3Res10) (h : Asc82Res10a) (hf : Asc82Facts10)
    (hb : Asc82Basic10) {t : G} {L S : Subgroup G} {z : G} {K1 K2 : Subgroup G} {g : G}
    (hctx : Sec109Ctx G t L S z K1 K2 g) :
    ∃ z' u0 : G, z' ∈ S ∧ z' * z' = 1 ∧ InducesTypeSome L z' 5 1 2 1 ∧
      (∀ k : G, k⁻¹ * z' * k ≠ t) ∧ u0 ∈ secB S L ∧ orderOf u0 = 2 ∧
      InducesTypeSome L u0 5 1 2 (-1) ∧ (∀ k : G, k⁻¹ * z * k ≠ u0) ∧
      g * (t * z') * g⁻¹ = t * u0 := by
  have hctx' : Sec10Ctx G t L S z K1 K2 := hctx.toSec10Ctx
  obtain ⟨hpsp, htC, htL, htS, hSN, hsyl⟩ := hb G t L S z hctx.toSec10Z
  obtain ⟨ht2, hz2, -, -, -, htz⟩ := sec10D_basic hb hctx'
  have hz : IsI4PlusIn L z := hctx.toSec10Z.pocket
  have hzL : z ∈ L := hz.mem
  have hgz : g⁻¹ * z * g = z := sec10C_g_conj_z hz2 hctx
  have hgt : g * t * g⁻¹ = t * z := sec10C_g_conj_t' hz2 hctx
  obtain ⟨-, -, -, -, -, φ, hperm, h4, h2, -⟩ := sec10BData_of hb hf.b5 hctx.toSec10Z
  obtain ⟨v, hv, hv4, hout⟩ := sec10C_exists_weight4_outer hf hb h.l107c hctx hperm
  obtain ⟨hadd, -, himg, -, hsurj⟩ := hperm
  have hφ1 : φ 0 = 1 := by
    have h0 : IsEvenVec (0 : Fin 5 → ZMod 2) := by simp [IsEvenVec]
    have := hadd 0 0 h0 h0
    simpa using this
  have hzB : z ∈ secB S L := sec10C_z_mem_secB hf hb hctx'
  obtain ⟨v₀, hv₀, hφv₀⟩ := (himg z).1 hzB
  have hv₀4 : vecWeight v₀ = 4 := by
    rcases even_weight_cases_five v₀ hv₀ with h0 | h02 | h04
    · exfalso
      have := hz.1
      rw [← hφv₀, h0, hφ1, orderOf_one] at this
      omega
    · exact absurd (hφv₀ ▸ hz) (h2 v₀ hv₀ h02)
    · exact h04
  obtain ⟨σ, hσ, hσv⟩ := exists_alt_permVec_weight_four v₀ v hv₀4 hv4
  obtain ⟨m, hm, hmspec⟩ := hsurj σ hσ
  have hmx : m * z * m⁻¹ = φ v := by
    rw [← hσv, ← hmspec v₀ hv₀, hφv₀]
  have hxB : φ v ∈ secB S L := (himg (φ v)).2 ⟨v, hv, rfl⟩
  have hx : IsI4PlusIn L (φ v) := h4 v hv hv4
  have hx2 : φ v * φ v = 1 := by
    rw [← hmx]
    calc m * z * m⁻¹ * (m * z * m⁻¹) = m * (z * z) * m⁻¹ := by group
      _ = 1 := by rw [hz2]; group
  have hxz : φ v * z = z * φ v := by
    have e1 := hadd v v₀ hv hv₀
    have e2 := hadd v₀ v hv₀ hv
    rw [hφv₀] at e1 e2
    rw [← e1, ← e2, add_comm]
  have hzx : z ≠ φ v := by
    intro hzx
    apply hout
    have : g⁻¹ * φ v * g = z := by rw [← hzx]; exact hgz
    rw [this]
    exact Subgroup.mem_sup_left hzL
  obtain ⟨z', hz'def⟩ : ∃ z', z' = g⁻¹ * φ v * g := ⟨_, rfl⟩
  have hgz'x : g * z' * g⁻¹ = φ v := by rw [hz'def]; group
  have hz'S : z' ∈ S := by
    refine (Subgroup.mem_normalizer_iff.mp hctx.norm z').mpr ?_
    rw [hgz'x]
    exact secB_le_S S L hxB
  have hz'2 : z' * z' = 1 := by
    rw [hz'def]
    calc g⁻¹ * φ v * g * (g⁻¹ * φ v * g) = g⁻¹ * (φ v * φ v) * g := by group
      _ = 1 := by rw [hx2]; group
  have hk₀ : z' = (m⁻¹ * g)⁻¹ * z * (m⁻¹ * g) := by
    rw [hz'def, ← hmx]
    group
  have hz'out : z' ∉ L ⊔ centralizer (L : Set G) := by rw [hz'def]; exact hout
  have hz'C : z' ∈ centralizer ({t} : Set G) := hctx.sylow.1 hz'S
  have hz'ss : z' * z' ∈ centralizer (L : Set G) := by rw [hz'2]; exact Subgroup.one_mem _
  have hz'ty : InducesTypeSome L z' 5 1 2 1 := by
    rcases (hf.factsC.ty G L hpsp z' (hSN hz'S) hz'ss).mp hz'out with hty | hty
    · exact hty
    · exact absurd hk₀.symm
        (sec10C_i4m_not_conj_z h3.l37 hf hb hctx' hty hz'C (m⁻¹ * g))
  have hnt : ∀ k : G, k⁻¹ * z' * k ≠ t := by
    intro k hk
    apply h.l108 G t L S z K1 K2 hctx' ((m⁻¹ * g) * k)⁻¹
    have e : (((m⁻¹ * g) * k)⁻¹)⁻¹ * t * ((m⁻¹ * g) * k)⁻¹ = z := by
      rw [← hk, hk₀]
      group
    rw [e]
    exact hzL
  obtain ⟨r, hrS, hr2, hrty, hne, hX, hconj⟩ := sec10C_exists_A2 h.l107c hctx
  have hrr : r * r = 1 := by
    have h' := pow_orderOf_eq_one r
    rw [hr2] at h'
    simpa [pow_two] using h'
  have hrsw : CFSG.conjugate K1 r = K2 :=
    hf.factsC.sw G L hpsp z K1 K2 hz hctx.pocket1 hctx.pocket2 hctx.ne r (hctx.central r hrS) hrty
  have hz'A2 : z' ∈ secA2 t r K1 K2 := by
    rw [← hconj]
    refine mem_conjugate_iff'.mpr ?_
    rw [hgz'x]
    exact Subgroup.mem_sup_left hxB
  have hswap : CFSG.conjugate K1 z' = K2 :=
    sec10C_A2_swap hf.pockets5 hb hctx' hrr hrS hrsw hz'A2 hz'out
  have hw : InducesTypeSome L (z' * z) 5 1 4 (-1) :=
    hf.f218e G L hpsp z K1 K2 hz hctx.pocket1 hctx.pocket2 hctx.ne z' hz'ty hswap
  have hwt : z' * z ∈ centralizer ({t} : Set G) :=
    (centralizer ({t} : Set G)).mul_mem hz'C (hctx.sylow.1 hctx.mem_S)
  have hnz : ∀ k : G, k⁻¹ * z * k ≠ z' * z :=
    sec10C_i4m_not_conj_z h3.l37 hf hb hctx' hw hwt
  have hu0ty : InducesTypeSome L (φ v * z) 5 1 2 (-1) :=
    hf.f218c G L hpsp z (φ v) hz hx hzx hxz.symm
  have hu0B : φ v * z ∈ secB S L := (secB S L).mul_mem hxB hzB
  have hu0o : orderOf (φ v * z) = 2 := by
    refine orderOf_eq_prime ?_ ?_
    · rw [pow_two]
      calc φ v * z * (φ v * z) = φ v * (z * φ v) * z := by group
        _ = φ v * (φ v * z) * z := by rw [← hxz]
        _ = (φ v * φ v) * (z * z) := by group
        _ = 1 := by rw [hx2, hz2, one_mul]
    · intro h1
      apply hzx
      have e : φ v = z⁻¹ := eq_inv_of_mul_eq_one_left h1
      rw [e]
      exact (inv_eq_of_mul_eq_one_right hz2).symm
  have hu0z : ∀ k : G, k⁻¹ * z * k ≠ φ v * z := by
    intro k hk
    apply hnz (k * g)
    have e : z' * z = g⁻¹ * (φ v * z) * g := by
      calc z' * z = g⁻¹ * φ v * g * (g⁻¹ * z * g) := by rw [hz'def, hgz]
        _ = g⁻¹ * (φ v * z) * g := by group
    rw [e, ← hk]
    group
  have hlast : g * (t * z') * g⁻¹ = t * (φ v * z) := by
    calc g * (t * z') * g⁻¹ = (g * t * g⁻¹) * (g * z' * g⁻¹) := by group
      _ = (t * z) * φ v := by rw [hgt, hgz'x]
      _ = t * (φ v * z) := by rw [mul_assoc, ← hxz]
  exact ⟨z', φ v * z, hz'S, hz'2, hz'ty, hnt, hu0B, hu0o, hu0ty, hu0z, hlast⟩

end CFSG.OddStandard.SmallF3.Omega
