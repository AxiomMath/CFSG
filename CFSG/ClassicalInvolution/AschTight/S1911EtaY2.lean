module

public import CFSG.ClassicalInvolution.AschTight.S1911EtaY

public section

namespace CFSG.ClassicalInvolution.Disconnected.AschTight.S1911

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77
open scoped Pointwise

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G] [IsSimpleGroup G]
  {K : Subgroup G} {z : G} {S : Sylow 2 G} {W L : Subgroup G} {t : G} {V : Subgroup G}

theorem invol_mem_W (hd : Sec19DataT p f K z S W L t V) {e : G} (heW : e ∈ W)
    (he2 : e * e = 1) (he1 : e ≠ 1) : e = z ∨ e = t ∨ e = t * z := by
  have hd0 := hd.toSec19Data
  have hcomm := comm_of_mem hd0
  have hI := isUniqueInvolution_of_tight hd.tight.toTightBranch
  have hle : V ≤ Subgroup.normalizer ((K ⊓ W : Subgroup G) : Set G) := by
    intro v hv
    rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · intro hx
      have e1 : v * x * v⁻¹ = x := by rw [hcomm v (hd.leW hv) x hx.2]; group
      rw [e1]
      exact hx
    · intro hx
      have e1 : v * x * v⁻¹ = x := by
        have h := hcomm v (hd.leW hv) _ hx.2
        have h2 : v * (v * x * v⁻¹) = v * x := by rw [h]; group
        exact mul_left_cancel h2
      rw [← e1]
      exact hx
  have hmem : e ∈ ((K ⊓ W ⊔ V : Subgroup G) : Set G) := by
    rw [← sup_eq_inf_sup hd]
    exact heW
  rw [Subgroup.coe_mul_of_right_le_normalizer_left _ _ hle] at hmem
  obtain ⟨u, hu, v, hv, rfl⟩ := Set.mem_mul.mp hmem
  have huv : u * v = v * u := hcomm u hu.2 v (hd.leW hv)
  have h1 : u * u = (v * v)⁻¹ := by
    have : u * u * (v * v) = 1 := by
      calc u * u * (v * v) = u * (u * v) * v := by group
        _ = u * (v * u) * v := by rw [huv]
        _ = u * v * (u * v) := by group
        _ = 1 := he2
    exact eq_inv_of_mul_eq_one_left this
  have h2 : u * u ∈ K ⊓ W ⊓ V := ⟨Subgroup.mul_mem _ hu hu, h1 ▸ Subgroup.inv_mem _
    (Subgroup.mul_mem _ hv hv)⟩
  rw [inf_inf_eq_bot hd, Subgroup.mem_bot] at h2
  have h3 : v * v = 1 := by
    have := h1
    rw [h2] at this
    exact inv_eq_one.mp this.symm
  have hu' := hI.unique u hu.1 h2
  have hv' := hd.invL.unique v (le_member hd hv) h3
  have hzt : t * z = z * t := Subgroup.mem_centralizer_singleton_iff.mp
    (hd.hSz (hd.hWS (mem_W hd)))
  rcases hu' with hu1 | hu1 <;> rcases hv' with hv1 | hv1
  · exact absurd (by rw [hu1, hv1, one_mul]) he1
  · exact Or.inr (Or.inl (by rw [hu1, hv1, one_mul]))
  · exact Or.inl (by rw [hu1, hv1, mul_one])
  · exact Or.inr (Or.inr (by rw [hu1, hv1, hzt]))

theorem exists_sylow_member (hd : Sec19DataT p f K z S W L t V) :
    ∃ RL : Subgroup G, IsSylow2In RL L ∧ (∀ w ∈ W, conjSub w RL = RL) ∧ V ≤ RL ∧
      Nat.card RL = 2 * Nat.card V := by
  have hd0 := hd.toSec19Data
  have htb := hd.tight.toTightBranch
  have hΩ := hypOmegaMod_of_tightD hd.tight
  have hp := hd.tight.branch.odd
  have hWL : W ≤ Subgroup.normalizer (L : Set G) :=
    (le_centralizer_of_mem hd0 (mem_W hd)).trans
      (centralizer_le_normalizer_member htb hd.memL hd.invL)
  have hW2 : IsPGroup 2 W := S.isPGroup'.to_le hd.hWS
  obtain ⟨RL, hRL, hRLW⟩ := exists_sylow_normalized hW2 hWL
  have hWRL : W ≤ Subgroup.normalizer (RL : Set G) := fun w hw =>
    mem_normalizer_iff_conjSub_eq.mpr (hRLW w hw)
  have hP := IsPGroup.to_sup_of_normal_right' hW2 hRL.2.1 hWRL
  have hVRL : V ≤ RL := by
    have h1 : RL ⊔ V = RL := hRL.eq_of_le (hP.to_le (sup_le le_sup_right
      (hd.leW.trans le_sup_left))) (sup_le hRL.1 (le_member hd)) le_sup_left
    rw [← h1]
    exact le_sup_right
  obtain ⟨R', -, J, hJ, hR'J, hVR', -, hcard, -⟩ := hΩ.exists_data_of_mem_USet hp hd.memV
  have hJL : J = L := hΩ.eq_of_mem_USet hp hd.memV hJ hd.memL (hVR'.trans hR'J.1) (le_member hd)
  subst hJL
  exact ⟨RL, hRL, hRLW, hVRL, by rw [hRL.natCard_eq hR'J, hcard]⟩

theorem inf_centralizer_inf_eq_bot (hd : Sec19DataT p f K z S W L t V) {RL : Subgroup G}
    (hRL : IsSylow2In RL L) :
    W ⊓ Subgroup.centralizer (((S : Subgroup G) ⊓ K : Subgroup G) : Set G) ⊓
      Subgroup.centralizer (RL : Set G) = ⊥ := by
  have hd0 := hd.toSec19Data
  have hΩ := hypOmegaMod_of_tightD hd.tight
  have hI := isUniqueInvolution_of_tight hd.tight.toTightBranch
  have hRLmem : RL ∈ RSet (CoreAssembly.conjClass K) := mem_RSet_of_isSylow2In hd.memL hRL
  rw [eq_bot_iff]
  intro x hx
  rw [Subgroup.mem_bot]
  by_contra hx1
  obtain ⟨i, hi⟩ := AscL62.orderOf_eq_two_pow_of_isPGroup (S.isPGroup'.to_le hd.hWS) hx.1.1
  obtain ⟨e, he, he2, he1⟩ := AscL62.exists_involution_pow hx1 hi
  have heW : e ∈ W := (Subgroup.zpowers_le.mpr hx.1.1) he
  have heC : e ∈ Subgroup.centralizer (((S : Subgroup G) ⊓ K : Subgroup G) : Set G) :=
    (Subgroup.zpowers_le.mpr hx.1.2) he
  have heRL : e ∈ Subgroup.centralizer (RL : Set G) := (Subgroup.zpowers_le.mpr hx.2) he
  rcases invol_mem_W hd heW he2 he1 with rfl | rfl | rfl
  · refine not_le_centralizer_of_mem_rSet hd.tight hd.memL (CoreAssembly.mem_conjClass_self K)
      (member_ne hd) hI hRLmem hRL.1 ?_
    intro r hr
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact Subgroup.mem_centralizer_iff.mp heRL r hr
  · exact not_mem_centralizer_inf hd0 hd.memL (member_ne hd) hd.invL heC
  · obtain ⟨r, hr, hrt⟩ := exists_conj_eq_mul hd
    have hrL : IsUniqueInvolution (conjSub r L) (t * z) := hrt ▸ hd.invL.conj r
    have hne : conjSub r L ≠ K := by
      intro h
      have h1 : t * z = z := (h ▸ hrL).eq hI
      apply hd.invL.ne_one
      calc t = t * z * z⁻¹ := by group
        _ = 1 := by rw [h1, mul_inv_cancel]
    exact not_mem_centralizer_inf hd0 (hΩ.conjInvariant r L hd.memL) hne hrL heC

theorem isCyclic_inf_sec19Y (hd : Sec19DataT p f K z S W L t V) :
    IsCyclic ↥(W ⊓ sec19Y K z) := by
  have hd0 := hd.toSec19Data
  have hΩ := hypOmegaMod_of_tightD hd.tight
  have hcomm := comm_of_mem hd0
  obtain ⟨RL, hRL, hRLW, hVRL, hcardL⟩ := exists_sylow_member hd
  obtain ⟨-, -, -, -, -, -, hVcyc, -, -⟩ :=
    hΩ.exists_data_of_mem_USet hd.tight.branch.odd hd.memV
  refine isCyclic_of_inf_centralizer_eq_bot hVRL hcardL (fun x hx =>
    mem_normalizer_iff_conjSub_eq.mpr (hRLW x hx.1)) (fun x hx v hv =>
    hcomm x hx.1 v (hd.leW hv)) ?_
  rw [inf_sec19Y_eq hd0]
  exact inf_centralizer_inf_eq_bot hd hRL

end CFSG.ClassicalInvolution.Disconnected.AschTight.S1911
