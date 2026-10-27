module

public import CFSG.ClassicalInvolution.SmallCases.Hat2A7NTightA

public section

namespace CFSG.ClassicalInvolution.Hat2A7N

open CFSG.Open CFSG.ClassicalInvolution.Hat2A7

section Clique

variable {F : Type} [Group F] [Finite F] {K : Subgroup F} {z : F}

omit [Finite F] in
theorem TightSettingN.rebase (S : TightSettingN F K z) {x : F} (hx : x ∈ classOf z) :
    TightSettingN F (memb K z x) x := by
  have hc : IsConjSubgroup K (memb K z x) := S.isConjSubgroup_memb hx
  refine ⟨S.tight.memb hx, S.center_trivial, ?_, ?_⟩
  · intro y hy2 hyE L M u v hL hM hLc hMc
    refine S.IH y hy2 ((IsCommProd.congr hx).mp hyE) L M u v ?_ (hc.trans hM) hLc hMc
    rcases hL with hL | hL
    · exact Or.inl (hc.trans hL)
    · exact Or.inr (IsTwinDiag.of_isConjSubgroup hc hL)
  · intro L u hL hLc
    exact S.P1 L u (hc.trans hL) hLc

theorem TightSettingN.commOrEq_of_commute (S : TightSettingN F K z) {x u : F}
    (hx : x ∈ classOf z) (hu : u ∈ classOf z) (hcomm : u * x = x * u) :
    CommOrEq (memb K z x) (memb K z u) := by
  have hu' : u ∈ classOf x := by rw [classOf_eq_of_mem hx]; exact hu
  have := (S.rebase hx).mem_Zset_of_commute hu' hcomm
  have h2 := this.2
  rwa [memb_memb S.tight hx hu] at h2

omit [Finite F] in
theorem TightSettingN.cliqueSub_le_normalizer (S : TightSettingN F K z) {v : F}
    (hv : v ∈ Zset K z) : cliqueSub K z ≤ Subgroup.normalizer (memb K z v : Set F) := by
  refine iSup₂_le fun w hw => ?_
  rcases S.commOrEq_of_mem_Zset hw hv with h | h
  · rw [h]
    exact Subgroup.le_normalizer
  · intro g hg
    have hc : g ∈ Subgroup.centralizer ((memb K z v : Subgroup F) : Set F) := by
      rw [Subgroup.mem_centralizer_iff]
      intro x hx
      exact (h g hg x hx).symm
    exact Subgroup.centralizer_le_normalizer ((memb K z v : Subgroup F) : Set F) hc

omit [Finite F] in
theorem TightSettingN.cliqueSub_le_centralizer (S : TightSettingN F K z) {e : F}
    (he : e ∈ Subgroup.closure (Zset K z)) (he1 : e ≠ 1) :
    cliqueSub K z ≤ Subgroup.centralizer ({e} : Set F) :=
  iSup₂_le fun _ hw => (S.memb_le_centralizer_iff he he1 hw.1).mpr hw

omit [Finite F] in
theorem TightSettingN.conj_mem_cliqueSub (S : TightSettingN F K z) {g : F}
    (hg : g ∈ Subgroup.normalizer (Zset K z)) {x : F} (hx : x ∈ cliqueSub K z) :
    g * x * g⁻¹ ∈ cliqueSub K z := by
  have h : (cliqueSub K z).map (MulAut.conj g).toMonoidHom ≤ cliqueSub K z := by
    rw [Subgroup.map_le_iff_le_comap]
    refine iSup₂_le fun w hw => ?_
    intro x hx
    have hgw : g * w * g⁻¹ ∈ Zset K z := (Subgroup.mem_set_normalizer_iff.mp hg w).mp hw
    have hxm : g * x * g⁻¹ ∈ memb K z (g * w * g⁻¹) := by
      rw [memb_conj S.tight hw.1 g]
      exact ⟨x, hx, rfl⟩
    exact memb_le_cliqueSub hgw hxm
  exact h ⟨x, hx, rfl⟩

theorem TightSettingN.mem_Zset_of_commute_Zset (S : TightSettingN F K z) {x u : F}
    (hx : x ∈ Zset K z) (hu : u ∈ classOf z) (hcomm : u * x = x * u) : u ∈ Zset K z := by
  have h2 := S.commOrEq_of_commute hx.1 hu hcomm
  have h1 : CommOrEq (memb K z z) (memb K z x) := by rw [memb_self S.tight]; exact hx.2
  have := S.commOrEq_trans (mem_classOf_self z) hx.1 hu h1 h2
  rw [memb_self S.tight] at this
  exact ⟨hu, this⟩

end Clique

section Swap

variable {F : Type} [Group F] [Finite F] {K : Subgroup F} {z : F}

omit [Finite F] in
theorem TightSettingN.swap_data (S : TightSettingN F K z) {u : F}
    (hN : u ∈ Subgroup.normalizer (Zset K z)) (hfix : ∀ x ∈ Zset K z, u * x * u⁻¹ ≠ x) :
    u * z * u⁻¹ ∈ Zset K z ∧ u * z * u⁻¹ ≠ z ∧ z * (u * z * u⁻¹) = (u * z * u⁻¹) * z ∧
      z * (u * z * u⁻¹) ∈ Subgroup.closure (Zset K z) ∧ z * (u * z * u⁻¹) ≠ 1 := by
  have hKz := S.tight.classical
  have hz2 : z * z = 1 := hKz.mul_self
  obtain ⟨b, hb⟩ : ∃ b : F, b = u * z * u⁻¹ := ⟨_, rfl⟩
  have hbZ : b ∈ Zset K z := by
    rw [hb]; exact (Subgroup.mem_set_normalizer_iff.mp hN z).mp S.self_mem_Zset
  have hbz : b ≠ z := by
    intro h; exact hfix z S.self_mem_Zset (by rw [← hb]; exact h)
  have hcoZ : CommOrEq (memb K z z) (memb K z b) := S.commOrEq_of_mem_Zset S.self_mem_Zset hbZ
  have hzb : z * b = b * z := S.mem_centralizer_of_commOrEq (u := z) (v := b) hbZ.1 hcoZ
    (S.mem_memb (mem_classOf_self z))
  have hb2 : b * b = 1 := by
    have hb' : b = u * z * u⁻¹ := hb
    have : orderOf b = 2 := orderOf_eq_two_of_mem_classOf S.tight hbZ.1
    have h2 := pow_orderOf_eq_one b
    rwa [this, pow_two] at h2
  have he1 : z * b ≠ 1 := by
    intro h
    apply hbz
    have h1 : b = z⁻¹ := eq_inv_of_mul_eq_one_right h
    rw [h1]
    exact inv_eq_of_mul_eq_one_right hz2
  rw [← hb]
  exact ⟨hbZ, hbz, hzb, Subgroup.mul_mem _ (Subgroup.subset_closure S.self_mem_Zset)
    (Subgroup.subset_closure hbZ), he1⟩

end Swap

end CFSG.ClassicalInvolution.Hat2A7N
