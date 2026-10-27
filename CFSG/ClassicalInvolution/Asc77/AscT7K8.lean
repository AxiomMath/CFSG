module

public import CFSG.ClassicalInvolution.Asc77.AscT7K4
public import CFSG.ClassicalInvolution.Asc77.AscT7K7
public import CFSG.ClassicalInvolution.Asc77.AscT7K6

public section

namespace CFSG.ClassicalInvolution.Asc77

open CFSG CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution
  CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Balance
  CFSG.ClassicalInvolution.Balance.Bootstrap CFSG.ClassicalInvolution.Asc77.ExactLayer
  CFSG.ClassicalInvolution.Disconnected
open CFSG.Open (IsElemAbelian classicalInvolutionOddCore IsSubnormal)

namespace T7K

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
  {K K' W : Subgroup G} {z u e g : G}

omit [Finite G] in
theorem z_mem_B (z u e : G) : z ∈ Subgroup.closure ({u * e, u, z} : Set G) :=
  Subgroup.subset_closure (by simp)

omit [Finite G] in
theorem u_mem_B (z u e : G) : u ∈ Subgroup.closure ({u * e, u, z} : Set G) :=
  Subgroup.subset_closure (by simp)

omit [Finite G] in
theorem e_mem_B (z u e : G) : e ∈ Subgroup.closure ({u * e, u, z} : Set G) := by
  have h : u⁻¹ * (u * e) ∈ Subgroup.closure ({u * e, u, z} : Set G) :=
    Subgroup.mul_mem _ (Subgroup.inv_mem _ (u_mem_B z u e)) (Subgroup.subset_closure (by simp))
  simpa using h

omit [Finite G] in
theorem closure_eq_e (z u e : G) :
    Subgroup.closure ({u * e, u, z} : Set G) = Subgroup.closure ({z, u, e} : Set G) := by
  apply le_antisymm
  · rw [Subgroup.closure_le]
    intro x hx
    rcases hx with h | h | h
    · rw [h]
      exact Subgroup.mul_mem _ (Subgroup.subset_closure (by simp))
        (Subgroup.subset_closure (by simp))
    · rw [h]
      exact Subgroup.subset_closure (by simp)
    · rw [h]
      exact Subgroup.subset_closure (by simp)
  · rw [Subgroup.closure_le]
    intro x hx
    rcases hx with h | h | h
    · rw [h]
      exact z_mem_B z u e
    · rw [h]
      exact u_mem_B z u e
    · rw [h]
      exact e_mem_B z u e

omit [Finite G] in
theorem closure_eq_ze (z u e : G) :
    Subgroup.closure ({u * e, u, z} : Set G) = Subgroup.closure ({z, u, z * e} : Set G) := by
  apply le_antisymm
  · rw [Subgroup.closure_le]
    intro x hx
    rcases hx with h | h | h
    · have h1 : u * (z⁻¹ * (z * e)) ∈ Subgroup.closure ({z, u, z * e} : Set G) :=
        Subgroup.mul_mem _ (Subgroup.subset_closure (by simp))
          (Subgroup.mul_mem _ (Subgroup.inv_mem _ (Subgroup.subset_closure (by simp)))
            (Subgroup.subset_closure (by simp)))
      rw [h]
      simpa [mul_assoc] using h1
    · rw [h]
      exact Subgroup.subset_closure (by simp)
    · rw [h]
      exact Subgroup.subset_closure (by simp)
  · rw [Subgroup.closure_le]
    intro x hx
    rcases hx with h | h | h
    · rw [h]
      exact z_mem_B z u e
    · rw [h]
      exact u_mem_B z u e
    · rw [h]
      exact Subgroup.mul_mem _ (z_mem_B z u e) (e_mem_B z u e)

variable [IsSimpleGroup G]

theorem hyp51At_of_commuting (hres : TwinSmallInner p) (hex : G2D4VertexExcl p f)
    (hs : Hyp23Setting p f Ω K K' z) (hd : Hyp23bData Ω K K' W z u e g) {c : G}
    (hc2 : c * c = 1) (hc1 : c ≠ 1) (hzc : z ≠ c)
    (hcB : c ∈ Subgroup.closure ({u * e, u, z} : Set G))
    (hBgen : Subgroup.closure ({u * e, u, z} : Set G) = Subgroup.closure ({z, u, c} : Set G))
    (hcomm : ∀ x : G, (x ∈ K ∨ x ∈ K') → x ∈ Subgroup.normalizer (W : Set G) → x * c = c * x) :
    Hyp51At (Subgroup.closure ({u * e, u, z} : Set G)) c := by
  have hst := hs.stand
  have hp : p ≠ 2 := hst.odd
  have hq : 5 ≤ p ^ f := hst.five
  have hΩ : HypOmegaMod p f Ω := hst.hyp
  have hKΩ : K ∈ Ω := hst.mem
  have hK'Ω : K' ∈ Ω := hs.hK'.1
  have hzK' : IsUniqueInvolution K' z := isUniqueInvolution_of_mem_twinSet hs.hz hs.hK'
  obtain ⟨R, R', a, b, r, hR, hR', hRR', hRN, hR'N, ha, hb, haW, hbW, hab, haa, hbb, hrR, hr⟩ :=
    exists_decomp hs hd
  have hc2' : IsPGroup 2 (Subgroup.zpowers c) := isPGroup_zpowers_of_sq_eq_one hc2
  have hRc : R ≤ Subgroup.centralizer ({c} : Set G) := fun x hx =>
    Subgroup.mem_centralizer_singleton_iff.mpr (hcomm x (Or.inl (hR.1 hx)) (hRN hx))
  have hR'c : R' ≤ Subgroup.centralizer ({c} : Set G) := fun x hx =>
    Subgroup.mem_centralizer_singleton_iff.mpr (hcomm x (Or.inr (hR'.1 hx)) (hR'N hx))
  have hMK : K ∈ tqMembers Ω c :=
    ⟨hKΩ, (mem_trivialOnQuot_iff_exists_sylow hp hq hΩ hc2' hKΩ).mpr ⟨R, hR, hRc⟩⟩
  have hMK' : K' ∈ tqMembers Ω c :=
    ⟨hK'Ω, (mem_trivialOnQuot_iff_exists_sylow hp hq hΩ hc2' hK'Ω).mpr ⟨R', hR', hR'c⟩⟩
  have haE : a ∈ exactCore c K :=
    ((isSylow2In_exactCore_iff hΩ hc2' hKΩ hMK.2).mpr ⟨hR, hRc⟩).1 ha
  have hbE : b ∈ exactCore c K' :=
    ((isSylow2In_exactCore_iff hΩ hc2' hK'Ω hMK'.2).mpr ⟨hR', hR'c⟩).1 hb
  have hdsup : u ∈ exactCore c K ⊔ exactCore c K' := by
    rw [hab]
    exact Subgroup.mul_mem_sup haE hbE
  exact hyp51At_of_twin_inner hres hex hst hKΩ hK'Ω hs.hne hs.hz hzK' hMK hMK'
    (B_isElemAbelian hs hd) (z_mem_B z u e) (u_mem_B z u e) hcB hBgen hc1 hzc hd.hu1 hd.huz hd.hu2
    hdsup

omit [IsSimpleGroup G] in
theorem hyp51At_z (hs : Hyp23Setting p f Ω K K' z) (hd : Hyp23bData Ω K K' W z u e g) :
    Hyp51At (Subgroup.closure ({u * e, u, z} : Set G)) z := by
  have hst := hs.stand
  have hp : p ≠ 2 := hst.odd
  have hq : 5 ≤ p ^ f := hst.five
  have hΩ : HypOmegaMod p f Ω := hst.hyp
  have hKΩ : K ∈ Ω := hst.mem
  have hK'Ω : K' ∈ Ω := hs.hK'.1
  have hzK' : IsUniqueInvolution K' z := isUniqueInvolution_of_mem_twinSet hs.hz hs.hK'
  obtain ⟨R, R', a, b, r, hR, hR', hRR', hRN, hR'N, ha, hb, haW, hbW, hab, haa, hbb, hrR, hr⟩ :=
    exists_decomp hs hd
  have he2' : IsPGroup 2 (Subgroup.zpowers e) := isPGroup_zpowers_of_sq_eq_one hd.he2
  have hRe : R ≤ Subgroup.centralizer ({e} : Set G) := fun x hx =>
    Subgroup.mem_centralizer_singleton_iff.mpr (comm_e hd (hRN hx))
  have hR'e : R' ≤ Subgroup.centralizer ({e} : Set G) := fun x hx =>
    Subgroup.mem_centralizer_singleton_iff.mpr (comm_e hd (hR'N hx))
  have heK : e ∈ trivialOnQuot K :=
    (mem_trivialOnQuot_iff_exists_sylow hp hq hΩ he2' hKΩ).mpr ⟨R, hR, hRe⟩
  have heK' : e ∈ trivialOnQuot K' :=
    (mem_trivialOnQuot_iff_exists_sylow hp hq hΩ he2' hK'Ω).mpr ⟨R', hR', hR'e⟩
  have hez : e ≠ z := fun h => e_not_mem_sup hs hd (h ▸ Subgroup.mem_sup_left hs.hz.mem)
  have hxyB : a * b ∈ Subgroup.closure ({u * e, u, z} : Set G) := by
    rw [← hab]
    exact u_mem_B z u e
  exact hyp51At_of_twin_vertex_z hst hKΩ hK'Ω hs.hz hzK' (B_isElemAbelian hs hd) (z_mem_B z u e)
    (hR.1 ha) (hR'.1 hb) hxyB (by rw [← hab]; exact hd.hu1) (by rw [← hab]; exact hd.huz)
    (e_mem_B z u e) hd.he1 hez heK heK'

theorem hyp51_B (hres : TwinSmallInner p) (hex : G2D4VertexExcl p f)
    (hs : Hyp23Setting p f Ω K K' z) (hd : Hyp23bData Ω K K' W z u e g) :
    Hyp51 (Subgroup.closure ({u * e, u, z} : Set G)) := by
  have hzK' : IsUniqueInvolution K' z := isUniqueInvolution_of_mem_twinSet hs.hz hs.hK'
  have hz2 : z * z = 1 := hs.hz.sq
  have hez : e ≠ z := fun h => e_not_mem_sup hs hd (h ▸ Subgroup.mem_sup_left hs.hz.mem)
  have hcommK : ∀ x : G, (x ∈ K ∨ x ∈ K') → z * x = x * z := by
    rintro x (hx | hx)
    · exact hs.hz.commute_of_mem hx
    · exact hzK'.commute_of_mem hx
  have h51z := hyp51At_z hs hd
  have h51e : Hyp51At (Subgroup.closure ({u * e, u, z} : Set G)) e :=
    hyp51At_of_commuting hres hex hs hd hd.he2 hd.he1 (Ne.symm hez) (e_mem_B z u e)
      (closure_eq_e z u e) (fun x _ hx => comm_e hd hx)
  have hze2 : (z * e) * (z * e) = 1 := by
    have hce : z * e = e * z := comm_e_of_mem_W hd hd.hzW
    calc (z * e) * (z * e) = z * (e * z) * e := by group
      _ = z * (z * e) * e := by rw [← hce]
      _ = (z * z) * (e * e) := by group
      _ = 1 := by rw [hz2, hd.he2]; group
  have h51ze : Hyp51At (Subgroup.closure ({u * e, u, z} : Set G)) (z * e) := by
    refine hyp51At_of_commuting hres hex hs hd hze2 ?_ ?_ (Subgroup.mul_mem _ (z_mem_B z u e)
      (e_mem_B z u e)) (closure_eq_ze z u e) ?_
    · intro h
      exact hez (by
        have : e = z⁻¹ := eq_inv_of_mul_eq_one_right h
        rw [this]
        exact inv_eq_of_mul_eq_one_right hz2)
    · intro h
      exact hd.he1 (by simpa using h.symm)
    · intro x hx hxN
      calc x * (z * e) = (x * z) * e := by group
        _ = (z * x) * e := by rw [(hcommK x hx).symm]
        _ = z * (x * e) := by group
        _ = z * (e * x) := by rw [comm_e hd hxN]
        _ = (z * e) * x := by group
  obtain ⟨R, R', a, b, r, hR, hR', hRR', hRN, hR'N, ha, hb, haW, hbW, hab, haa, hbb, hrR, hr⟩ :=
    exists_decomp hs hd
  have hgN : g ∈ Subgroup.normalizer (W : Set G) := g_mem_normalizer hd
  have hrN : r ∈ Subgroup.normalizer (W : Set G) := hRN hrR
  have hgB := mem_normalizer_B hs hd hgN
  have hrgB : r * g ∈ Subgroup.normalizer ((Subgroup.closure ({u * e, u, z} : Set G) :
      Subgroup G) : Set G) := Subgroup.mul_mem _ (mem_normalizer_B hs hd hrN) hgB
  have hge : g * e * g⁻¹ = e := by
    rw [comm_e hd hgN]
    group
  have hre : r * e * r⁻¹ = e := by
    rw [comm_e hd hrN]
    group
  have hgz : g * z * g⁻¹ = u * e := hd.hgt
  have hgze : g * (z * e) * g⁻¹ = u := by
    calc g * (z * e) * g⁻¹ = (g * z * g⁻¹) * (g * e * g⁻¹) := by group
      _ = (u * e) * e := by rw [hgz, hge]
      _ = u * (e * e) := by group
      _ = u := by rw [hd.he2]; group
  have hcU : u * e = e * u := comm_e_of_mem_W hd hd.huW
  refine hyp51_of_orbitReps (B_isElemAbelian hs hd) (B_natCard hs hd) (R := {z, z * e, e})
    ?_ ?_
  · intro c hc
    rcases hc with rfl | rfl | rfl
    · exact h51z
    · exact h51ze
    · exact h51e
  · intro c hc hc1
    rcases mem_cases_of_commuting_involutions hd.hu2 hz2 hd.he2 (comm_uz hs hd)
      (comm_e_of_mem_W hd hd.huW) (comm_e_of_mem_W hd hd.hzW) hc with
      h | h | h | h | h | h | h | h
    · exact absurd h hc1
    · exact ⟨z, by simp, 1, Subgroup.one_mem _, by rw [h]; group⟩
    · exact ⟨z * e, by simp, g, hgB, by rw [h, hgze]⟩
    · refine ⟨z * e, by simp, r * g, hrgB, ?_⟩
      calc c = u * z := h
        _ = r * u * r⁻¹ := hr.symm
        _ = r * (g * (z * e) * g⁻¹) * r⁻¹ := by rw [hgze]
        _ = r * g * (z * e) * (r * g)⁻¹ := by group
    · exact ⟨e, by simp, 1, Subgroup.one_mem _, by rw [h]; group⟩
    · exact ⟨z * e, by simp, 1, Subgroup.one_mem _, by rw [h]; group⟩
    · exact ⟨z, by simp, g, hgB, by rw [h, hgz]⟩
    · refine ⟨z, by simp, r * g, hrgB, ?_⟩
      calc c = u * z * e := h
        _ = (r * u * r⁻¹) * (r * e * r⁻¹) := by rw [hr, hre]
        _ = r * (u * e) * r⁻¹ := by group
        _ = r * (g * z * g⁻¹) * r⁻¹ := by rw [hgz]
        _ = r * g * z * (r * g)⁻¹ := by group

theorem c23_5X_one (hres : TwinSmallInner p) (hex : G2D4VertexExcl p f)
    (hs : Hyp23Setting p f Ω K K' z) (hd : Hyp23bData Ω K K' W z u e g) :
    Odd (Nat.card ↥(alphaOf (Subgroup.closure ({u, z} : Set G)))) ∧
      ∀ A : Subgroup G, A ≤ Subgroup.closure ({u * e, u, z} : Set G) → IsElemAbelian2 A 2 →
        alphaOf A = alphaOf (Subgroup.closure ({u, z} : Set G)) := by
  have hD : IsElemAbelian2 (Subgroup.closure ({u, z} : Set G)) 2 :=
    T7A.isElemAbelian2_closure_pair hd.hu2 hs.hz.sq hd.hu1 hs.hz.ne_one hd.huz (comm_uz hs hd)
  have hDB : Subgroup.closure ({u, z} : Set G) ≤ Subgroup.closure ({u * e, u, z} : Set G) := by
    rw [Subgroup.closure_le]
    rintro x (rfl | rfl)
    · exact u_mem_B z x e
    · exact z_mem_B x u e
  exact lemma54_odd_and_eq (hyp51_B hres hex hs hd) hDB hD

end T7K

end CFSG.ClassicalInvolution.Asc77
