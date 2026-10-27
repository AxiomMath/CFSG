module

public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Lemma113ClaimsR

public section

namespace CFSG.LocalAnalysis.GLTheoremB.MovingAround

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB
open CFSG.HardMathSupport.Solomon.Coordinator (IsEkIn)
open CFSG.HardMathSupport.Solomon.LocalBalance (barOf barAut)
open scoped MatrixGroups Pointwise commutatorElement

namespace Lemma113Claims

open scoped Lemma113Claims

namespace P2

variable {G : Type} [Group G] [Finite G]

theorem shear_eq_of_mem_zpowers {E A : Subgroup G} {e : G} {K Q : Subgroup G} (c : Ctx E A e K Q)
    {q u : G} (hq : q ∈ (Q ⊓ K : Subgroup G)) (hu : u ∈ (Q ⊓ K : Subgroup G))
    (h : u * e ∈ Subgroup.zpowers (e * q)) : u = q := by
  have hqe : Commute e q := c.hKe q hq.2
  have hy3 : (e * q) ^ 3 = 1 := by rw [hqe.mul_pow, c.he3, c.Q0_pow_three hq, one_mul]
  rcases mem_zpowers_cases hy3 h with h1 | h1 | h1
  · exfalso
    apply c.e_not_mem_Q0
    have : e = u⁻¹ := eq_inv_of_mul_eq_one_right h1
    rw [this]
    exact (Q ⊓ K : Subgroup G).inv_mem hu
  · have h2 : e * u = u * e := c.hKe u hu.2
    exact mul_left_cancel (h2.trans h1)
  · exfalso
    apply c.e_not_mem_Q0
    have h2 : e * e = u⁻¹ * q⁻¹ := by
      calc e * e = u⁻¹ * (u * e * (e * q)) * q⁻¹ := by group
        _ = u⁻¹ * q⁻¹ := by rw [h1, inv_mul_cancel, mul_one]
    have h3 : e * e ∈ (Q ⊓ K : Subgroup G) := by
      rw [h2]
      exact (Q ⊓ K : Subgroup G).mul_mem ((Q ⊓ K : Subgroup G).inv_mem hu)
        ((Q ⊓ K : Subgroup G).inv_mem hq)
    have h3' : e * (e * e) = 1 := by rw [← pow_three]; exact c.he3
    have h4 : e * e * (e * e) = e := by
      calc e * e * (e * e) = (e * (e * e)) * e := by group
        _ = e := by rw [h3', one_mul]
    have h5 := (Q ⊓ K : Subgroup G).mul_mem h3 h3
    rwa [h4] at h5

theorem inf_normalizer_zpowers {E A : Subgroup G} {e : G} {K Q R : Subgroup G}
    (r : Lemma113Claims.RCfg E A e K Q R) :
    R ⊓ Subgroup.normalizer ((Subgroup.zpowers e : Subgroup G) : Set G) = Q := by
  have c := r.ctx
  apply le_antisymm
  · rintro x ⟨hxR, hxN⟩
    have hxe : x * e * x⁻¹ ∈ Subgroup.zpowers e :=
      (Subgroup.mem_normalizer_iff.1 hxN e).1 (Subgroup.mem_zpowers e)
    have hu : x * e * x⁻¹ * e⁻¹ ∈ (Q ⊓ K : Subgroup G) :=
      (mem_N1.1 (r.R_le_N1 hxR)).2.2 e c.heE
    have h2 : (x * e * x⁻¹ * e⁻¹) * e ∈ Subgroup.zpowers (e * 1) := by
      have : (x * e * x⁻¹ * e⁻¹) * e = x * e * x⁻¹ := by group
      rw [this, mul_one]
      exact hxe
    have h3 : x * e * x⁻¹ * e⁻¹ = 1 := shear_eq_of_mem_zpowers c (Q ⊓ K : Subgroup G).one_mem hu h2
    have hxe' : x * e = e * x := by
      have h4 : x * e * x⁻¹ = e := mul_inv_eq_one.1 h3
      calc x * e = (x * e * x⁻¹) * x := by group
        _ = e * x := by rw [h4]
    have hxC : x ∈ Cg e := Subgroup.mem_centralizer_iff.2 fun y hy => by
      rw [Set.mem_singleton_iff.1 hy]
      exact hxe'.symm
    have hQe : R ⊓ Cg e = Q :=
      c.hQ.2.2 _ inf_le_right (r.hRp.to_le inf_le_left) (le_inf r.hQR c.hQ.1)
    rw [← hQe]
    exact ⟨hxR, hxC⟩
  · intro x hx
    exact ⟨r.hQR hx, Lemma113b.centralizer_le_normalizer_zpowers' e (c.hQ.1 hx)⟩

theorem orbit_eq {E A : Subgroup G} {e : G} {K Q R : Subgroup G}
    (r : Lemma113Claims.RCfg E A e K Q R) :
    (MulAction.orbit ↥R (Subgroup.zpowers e : Subgroup G) : Set (Subgroup G)) =
      MulAction.orbit ↥(Subgroup.normalizer (E : Set G)) (Subgroup.zpowers e : Subgroup G) := by
  have c := r.ctx
  have hcard := card_eq_ncard_orbit_mul R (Subgroup.zpowers e : Subgroup G)
  rw [inf_normalizer_zpowers r, r.hR8, c.card_Q r.hB] at hcard
  have hR27 : (MulAction.orbit ↥R (Subgroup.zpowers e : Subgroup G)).ncard = 27 := by
    omega
  have hsub : (MulAction.orbit ↥R (Subgroup.zpowers e : Subgroup G) : Set (Subgroup G)) ⊆
      MulAction.orbit ↥(Subgroup.normalizer (E : Set G)) (Subgroup.zpowers e : Subgroup G) := by
    rintro _ ⟨ρ, rfl⟩
    refine ⟨⟨(ρ : G), r.hRN ρ.2⟩, ?_⟩
    ext x
    rw [connAct_mem_smul_iff, connAct_mem_smul_iff]
  exact Set.eq_of_subset_of_ncard_le hsub (by rw [hR27, c.ncard_orbit r.hB]) (Set.toFinite _)

theorem R_class_of_e {E A : Subgroup G} {e : G} {K Q R : Subgroup G}
    (r : Lemma113Claims.RCfg E A e K Q R) {q : G} (hq : q ∈ (Q ⊓ K : Subgroup G)) :
    ∃ ρ ∈ R, ρ * e * ρ⁻¹ = e * q := by
  have c := r.ctx
  have hmem : (Subgroup.zpowers (e * q) : Subgroup G) ∈
      MulAction.orbit ↥R (Subgroup.zpowers e : Subgroup G) := by
    rw [orbit_eq r, c.orbit_eq_image r.hB]
    exact ⟨q, hq, rfl⟩
  obtain ⟨ρ, hρ⟩ := MulAction.mem_orbit_iff.1 hmem
  refine ⟨(ρ : G), ρ.2, ?_⟩
  have h1 : (ρ : G) * e * (ρ : G)⁻¹ ∈ Subgroup.zpowers (e * q) := by
    rw [← hρ, connAct_mem_smul_iff]
    have : (ρ : G)⁻¹ * ((ρ : G) * e * (ρ : G)⁻¹) * (ρ : G) = e := by group
    rw [this]
    exact Subgroup.mem_zpowers e
  have hu : (ρ : G) * e * (ρ : G)⁻¹ * e⁻¹ ∈ (Q ⊓ K : Subgroup G) :=
    (mem_N1.1 (r.R_le_N1 ρ.2)).2.2 e c.heE
  have h2 : ((ρ : G) * e * (ρ : G)⁻¹ * e⁻¹) * e ∈ Subgroup.zpowers (e * q) := by
    have : ((ρ : G) * e * (ρ : G)⁻¹ * e⁻¹) * e = (ρ : G) * e * (ρ : G)⁻¹ := by group
    rw [this]
    exact h1
  have h3 := shear_eq_of_mem_zpowers c hq hu h2
  calc (ρ : G) * e * (ρ : G)⁻¹ = ((ρ : G) * e * (ρ : G)⁻¹ * e⁻¹) * e := by group
    _ = q * e := by rw [h3]
    _ = e * q := (c.hKe q hq.2).symm

private theorem isPGroup_of_isElemAbelian {p : ℕ} {F : Subgroup G} (hF : IsElemAbelian p F) :
    IsPGroup p ↥F :=
  fun y => ⟨1, Subtype.ext (by simpa using hF.2 y y.2)⟩

theorem exists_normalizer_of_conj_mem {e : G} {Q E' : Subgroup G}
    (hQS : IsSylowIn 3 (Subgroup.centralizer ({e} : Set G)) Q) (hE' : IsElemAbelian 3 E')
    (hWC : ∀ g : G, GLBConj g E' ≤ Q → GLBConj g E' = E') {x : G} (hx : x⁻¹ * e * x ∈ E') :
    ∃ n ∈ Subgroup.normalizer (E' : Set G), n⁻¹ * e * n = x⁻¹ * e * x := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hSC : E'.map (MulAut.conj x).toMonoidHom ≤ Subgroup.centralizer ({e} : Set G) := by
    rintro _ ⟨s, hs, rfl⟩
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    rw [Set.mem_singleton_iff.1 hy]
    have hcomm : (x⁻¹ * e * x) * s = s * (x⁻¹ * e * x) :=
      congrArg Subtype.val (hE'.1.is_comm.comm ⟨x⁻¹ * e * x, hx⟩ ⟨s, hs⟩)
    show e * (x * s * x⁻¹) = x * s * x⁻¹ * e
    calc e * (x * s * x⁻¹) = x * ((x⁻¹ * e * x) * s) * x⁻¹ := by group
      _ = x * (s * (x⁻¹ * e * x)) * x⁻¹ := by rw [hcomm]
      _ = x * s * x⁻¹ * e := by group
  have hSp : IsPGroup 3 ↥(E'.map (MulAut.conj x).toMonoidHom) := (isPGroup_of_isElemAbelian hE').map _
  obtain ⟨c, hcC, hc⟩ := Lemma113b.exists_conj_mem_of_isSylowIn hQS hSC hSp
  have hec : e * c = c * e := Subgroup.mem_centralizer_iff.1 hcC e (Set.mem_singleton e)
  have hce : c⁻¹ * e * c = e := by
    calc c⁻¹ * e * c = c⁻¹ * (e * c) := by group
      _ = c⁻¹ * (c * e) := by rw [hec]
      _ = e := by group
  have hsub : GLBConj (c * x)⁻¹ E' ≤ Q := by
    intro y hy
    have hs : (c * x)⁻¹ * y * (c * x)⁻¹⁻¹ ∈ E' := mem_gLBConj.1 hy
    have hmem : x * ((c * x)⁻¹ * y * (c * x)⁻¹⁻¹) * x⁻¹ ∈ E'.map (MulAut.conj x).toMonoidHom :=
      Subgroup.mem_map.2 ⟨_, hs, rfl⟩
    have h1 := hc _ hmem
    have h2 : c * (x * ((c * x)⁻¹ * y * (c * x)⁻¹⁻¹) * x⁻¹) * c⁻¹ = y := by group
    rw [h2] at h1
    exact h1
  have hWCw := hWC (c * x)⁻¹ hsub
  have hn : c * x ∈ Subgroup.normalizer (E' : Set G) := by
    have h3 := inv_mem (mem_normalizer_of_GLBConj_eq hWCw)
    rw [inv_inv] at h3
    exact h3
  refine ⟨c * x, hn, ?_⟩
  calc (c * x)⁻¹ * e * (c * x) = x⁻¹ * (c⁻¹ * e * c) * x := by group
    _ = x⁻¹ * e * x := by rw [hce]

theorem part2 {E A : Subgroup G} {e : G} {K Q R : Subgroup G}
    (r : Lemma113Claims.RCfg E A e K Q R)
    (hWC : ∀ g : G, GLBConj g E ≤ Q → GLBConj g E = E)
    {g : G} (hg : g⁻¹ * e * g ∈ E) :
    ∃ z ∈ R, z⁻¹ * (g⁻¹ * e * g) * z ∈ Subgroup.zpowers e := by
  have c := r.ctx
  obtain ⟨n, -, hnx⟩ := exists_normalizer_of_conj_mem c.hQ c.hEel hWC hg
  have hxQ0 : g⁻¹ * e * g ∉ (Q ⊓ K : Subgroup G) := by
    intro h
    apply c.not_conj_e_into_Q0 r.hB n⁻¹
    rw [inv_inv, hnx]
    exact h
  obtain ⟨q, hq, hzq⟩ := c.zpowers_form hg hxQ0
  have hmem : g⁻¹ * e * g ∈ Subgroup.zpowers (e * q) := hzq ▸ Subgroup.mem_zpowers _
  have hy3 : (e * q) ^ 3 = 1 := by
    have hqe : Commute e q := c.hKe q hq.2
    rw [hqe.mul_pow, c.he3, c.Q0_pow_three hq, one_mul]
  obtain ⟨ρ, hρR, hρ⟩ := R_class_of_e r hq
  have hρ' : ρ⁻¹ * (e * q) * ρ = e := by
    rw [← hρ]
    group
  refine ⟨ρ, hρR, ?_⟩
  rcases mem_zpowers_cases hy3 hmem with h1 | h1 | h1
  · exfalso
    apply c.he1
    calc e = g * (g⁻¹ * e * g) * g⁻¹ := by group
      _ = 1 := by rw [h1]; group
  · rw [h1, hρ']
    exact Subgroup.mem_zpowers e
  · rw [h1]
    have h2 : ρ⁻¹ * (e * q)⁻¹ * ρ = e⁻¹ := by
      calc ρ⁻¹ * (e * q)⁻¹ * ρ = (ρ⁻¹ * (e * q) * ρ)⁻¹ := by group
        _ = e⁻¹ := by rw [hρ']
    rw [h2]
    exact Subgroup.inv_mem _ (Subgroup.mem_zpowers e)

end P2

end Lemma113Claims

end CFSG.LocalAnalysis.GLTheoremB.MovingAround

end
