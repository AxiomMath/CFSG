module

public import Mathlib.GroupTheory.Sylow

public section

namespace CFSG.HardMathSupport.Malle.Coordinator

variable {G : Type*} [Group G]

theorem isolated_of_odd_index [Finite G] {N M : Subgroup G} (hNM : N ≤ M)
    (hodd : ¬ 2 ∣ N.relIndex M) {u : G} (huN : u ∈ N) (hu2 : u * u = 1)
    (hCu : ¬ 2 ∣ (N ⊓ Subgroup.centralizer ({u} : Set G)).relIndex N)
    (hstar : ∀ s ∈ N, s * u = u * s → s * s = 1 → s ≠ u → ¬ ∃ g ∈ M, g * u * g⁻¹ = s) :
    ∀ g ∈ M, (g * u * g⁻¹) * u = u * (g * u * g⁻¹) → g * u * g⁻¹ = u := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro g hg hcomm
  by_contra hne
  set C := N ⊓ Subgroup.centralizer ({u} : Set G) with hC
  set CM := M ⊓ Subgroup.centralizer ({u} : Set G) with hCM
  have hCCM : C ≤ CM := inf_le_inf_right _ hNM
  obtain ⟨S'⟩ := Sylow.nonempty (p := 2) (G := C)
  set S := (S' : Subgroup C).map C.subtype with hS
  have hSC : S ≤ C := Subgroup.map_subtype_le _
  have hSp : IsPGroup 2 S := S'.isPGroup'.map _
  have hSidxC : ¬ 2 ∣ S.relIndex C := by
    have h1 : S.subgroupOf C = (S' : Subgroup C) := by
      rw [hS]; exact Subgroup.comap_map_eq_self_of_injective C.subtype_injective _
    rw [Subgroup.relIndex, h1]
    exact S'.not_dvd_index
  have hSCM : S ≤ CM := hSC.trans hCCM
  have hSidxCM : ¬ 2 ∣ S.relIndex CM := by
    intro h
    have hM : S.relIndex M = S.relIndex C * C.relIndex N * N.relIndex M := by
      rw [Subgroup.relIndex_mul_relIndex S C N hSC inf_le_left,
        Subgroup.relIndex_mul_relIndex S N M (hSC.trans inf_le_left) hNM]
    have hodd' : ¬ 2 ∣ S.relIndex M := by
      rw [hM]
      intro h2
      rcases (Nat.Prime.dvd_mul Nat.prime_two).mp h2 with h3 | h3
      · rcases (Nat.Prime.dvd_mul Nat.prime_two).mp h3 with h4 | h4
        · exact hSidxC h4
        · exact hCu h4
      · exact hodd h3
    apply hodd'
    rw [← Subgroup.relIndex_mul_relIndex S CM M hSCM inf_le_left]
    exact Dvd.dvd.mul_right h _
  set v := g * u * g⁻¹ with hv
  have hvCM : v ∈ CM := Subgroup.mem_inf.mpr ⟨M.mul_mem (M.mul_mem hg (hNM huN)) (M.inv_mem hg),
    Subgroup.mem_centralizer_singleton_iff.mpr hcomm⟩
  have hv2 : v * v = 1 := by
    calc v * v = g * (u * u) * g⁻¹ := by rw [hv]; group
      _ = 1 := by rw [hu2]; group
  let SM : Sylow 2 CM := (hSp.comap_subtype (K := CM)).toSylow hSidxCM
  have hzp : IsPGroup 2 (Subgroup.zpowers (⟨v, hvCM⟩ : CM)) := by
    refine IsPGroup.of_card (n := 1) ?_
    rw [Nat.card_zpowers, pow_one]
    apply orderOf_eq_prime
    · exact Subtype.ext (by simpa [pow_two] using hv2)
    · intro h
      apply hne
      have hv1 : v = 1 := by simpa using congrArg Subtype.val h
      have hu1 : u = 1 := by
        calc u = g⁻¹ * v * g := by rw [hv]; group
          _ = 1 := by rw [hv1]; group
      rw [hv1, hu1]
  obtain ⟨Q, hQ⟩ := hzp.exists_le_sylow
  obtain ⟨c, hc⟩ := MulAction.exists_smul_eq CM SM Q
  have hvQ : (⟨v, hvCM⟩ : CM) ∈ (Q : Subgroup CM) := hQ (Subgroup.mem_zpowers _)
  rw [← hc, Sylow.coe_subgroup_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem] at hvQ
  set s : G := (c : G)⁻¹ * v * c with hs
  have hsS : s ∈ S := by
    have h1 : ((MulAut.conj c)⁻¹ • (⟨v, hvCM⟩ : CM) : CM) ∈ S.subgroupOf CM := hvQ
    rw [Subgroup.mem_subgroupOf] at h1
    convert h1 using 1
    rw [← map_inv, MulAut.smul_def, MulAut.conj_apply]
    simp [hs]
  have hsC : s ∈ C := hSC hsS
  have hcu : (c : G) * u = u * c := (Subgroup.mem_centralizer_singleton_iff.mp c.2.2)
  refine hstar s hsC.1 (Subgroup.mem_centralizer_singleton_iff.mp hsC.2) ?_ ?_ ?_
  · calc s * s = (c : G)⁻¹ * (v * v) * c := by rw [hs]; group
      _ = 1 := by rw [hv2]; group
  · intro hsu
    apply hne
    calc v = (c : G) * s * (c : G)⁻¹ := by rw [hs]; group
      _ = c * u * (c : G)⁻¹ := by rw [hsu]
      _ = u := by rw [hcu]; group
  · refine ⟨(c : G)⁻¹ * g, M.mul_mem (M.inv_mem c.2.1) hg, ?_⟩
    rw [hs, hv]
    group

end CFSG.HardMathSupport.Malle.Coordinator
