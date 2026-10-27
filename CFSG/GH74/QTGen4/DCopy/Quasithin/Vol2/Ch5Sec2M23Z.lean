module

public import CFSG.Quasithin.Vol2.Ch5Sec2M23Z
public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch5Sec2M23G0Ext

public section

namespace CFSG.Quasithin.H13

open MulAction CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique
open CFSG.QuasithinUnique.L246.C123 (A7 fixU mem_fixU)

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G]

theorem exists_rho_of_setting_F4 (hQ : Stmt5_2_8_Q_F4) {T M L V H B D L₂ M2 : Subgroup G} {n : ℕ}
    {π : ↥M2 →* Equiv.Perm (Fin 7)} (hyp : Hyp5_2_4 G T M L V H B D L₂ n)
    (hM23 : IsOfTypeM23 M L H B D T) (hS : IsM23Setting T H M2 π) :
    ∃ (π' : ↥M2 →* A7) (ρ : A7 →* MulAut ↥(pCoreOf 2 M2)),
      Function.Surjective π' ∧ π'.ker = (pCoreOf 2 M2).subgroupOf M2 ∧ Function.Injective ρ ∧
      (∀ (g : ↥M2) (u : ↥(pCoreOf 2 M2)), ((ρ (π' g) u : ↥(pCoreOf 2 M2)) : G) =
        g * u * (g : G)⁻¹) ∧
      Nat.card ↥(pCoreOf 2 M2) = 16 ∧ (∀ u : ↥(pCoreOf 2 M2), u ^ 2 = 1) ∧
      Nat.card ((T.subgroupOf M2).map π') = 8 ∧ pCoreOf 2 M2 ≤ T ∧
      ∀ g : ↥M2, ((π' g : A7) : Equiv.Perm (Fin 7)) = π g := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hab, hU16, hTM2'⟩ := hQ G T M L V H B D L₂ n M2 hyp hM23 hS.K_lt hS.maximal hS.excA7
  set U := pCoreOf 2 M2 with hUdef
  have hcomm : ∀ a ∈ U, ∀ b ∈ U, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (hab.1.1.comm ⟨a, ha⟩ ⟨b, hb⟩)
  have hUN : M2 ≤ Subgroup.normalizer (U : Set G) :=
    Subgroup.le_normalizer.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 M2)

  let π' : ↥M2 →* A7 :=
    (MulEquiv.subgroupCongr hS.range_eq).toMonoidHom.comp π.rangeRestrict
  have hπ' : ∀ g, ((π' g : A7) : Equiv.Perm (Fin 7)) = π g := fun g => rfl
  have hsurj : Function.Surjective π' := by
    intro a
    obtain ⟨g, hg⟩ : (a : Equiv.Perm (Fin 7)) ∈ π.range := by rw [hS.range_eq]; exact a.2
    exact ⟨g, Subtype.ext (by rw [hπ']; exact hg)⟩
  have hker : π'.ker = U.subgroupOf M2 := by
    rw [← hS.ker_eq]
    ext g
    rw [MonoidHom.mem_ker, MonoidHom.mem_ker, ← hπ']
    constructor
    · intro h
      rw [h]
      rfl
    · intro h
      exact Subtype.ext h
  have hC : M2 ⊓ Subgroup.centralizer (U : Set G) ≤ U := hS.excA7.1.2.1
  refine ⟨π', m23Rho π' hsurj hker hUN hcomm, hsurj, hker,
    m23Rho_injective π' hsurj hker hUN hcomm hC,
    fun g u => m23Rho_apply π' hsurj hker hUN hcomm g u,
    hU16, fun u => Subtype.ext (by rw [Subgroup.coe_pow, Subgroup.coe_one]; exact hab.2 u u.2),
    ?_, ?_, hπ'⟩
  ·
    have hTM2 : T ≤ M2 := hS.T_le
    have hTs : IsSylowTwoOf T M2 := isSylowTwoOf_of_isSylowTwo hyp.sylow hTM2
    have hUT : U ≤ T := CFSG.Quasithin.pCoreOf_le_of_isSylowTwoOf hTs
    have hcardT := card_eq_128_of_setting_F4 hQ hyp hM23 hS
    have h1 := card_map_mul_card_inf hS.ker_eq hTM2
    rw [inf_of_le_right hUT, hcardT, hU16] at h1
    have h2 : Nat.card ((T.subgroupOf M2).map π') = Nat.card ((T.subgroupOf M2).map π) := by
      have e : ((T.subgroupOf M2).map π').map (alternatingGroup (Fin 7)).subtype =
          (T.subgroupOf M2).map π := by
        rw [Subgroup.map_map]
        rfl
      rw [← e, Subgroup.card_map_of_injective (Subgroup.subtype_injective _)]
    rw [h2]
    omega
  · exact CFSG.Quasithin.pCoreOf_le_of_isSylowTwoOf
      (isSylowTwoOf_of_isSylowTwo hyp.sylow hS.T_le)

theorem stmt5_2_12_center_of_F4 (hQ : Stmt5_2_8_Q_F4)
    {T M L V H B D L₂ M2 : Subgroup G} {n : ℕ} {π : ↥M2 →* Equiv.Perm (Fin 7)}
    (hyp : Hyp5_2_4 G T M L V H B D L₂ n) (hM23 : IsOfTypeM23 M L H B D T)
    (hS : IsM23Setting T H M2 π) :
    ∃ z : G, orderOf z = 2 ∧ centerOf T = Subgroup.zpowers z ∧ z ∈ pCoreOf 2 M2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set U := pCoreOf 2 M2 with hUdef
  obtain ⟨hab, -, -⟩ := hQ G T M L V H B D L₂ n M2 hyp hM23 hS.K_lt hS.maximal hS.excA7
  obtain ⟨π', ρ, hsurj, hker, hinj, hρ, hU16, hU2, hT8, hUT, -⟩ :=
    exists_rho_of_setting_F4 hQ hyp hM23 hS
  set PT := (T.subgroupOf M2).map π' with hPT
  let _ := commGroupOfComm U fun a ha b hb =>
    congrArg Subtype.val (hab.1.1.comm ⟨a, ha⟩ ⟨b, hb⟩)
  have hTM2 : T ≤ M2 := hS.T_le
  have hC : M2 ⊓ Subgroup.centralizer (U : Set G) ≤ U := hS.excA7.1.2.1

  have hfix : ∀ u : ↥U, u ∈ fixU ρ PT ↔ ∀ t ∈ T, t * (u : G) * t⁻¹ = u := by
    intro u
    rw [mem_fixU]
    constructor
    · intro h t ht
      have h1 := h (π' ⟨t, hTM2 ht⟩) ⟨⟨t, hTM2 ht⟩, Subgroup.mem_subgroupOf.mpr ht, rfl⟩
      have h2 := congrArg Subtype.val h1
      rwa [hρ] at h2
    · rintro h _ ⟨t, ht, rfl⟩
      apply Subtype.ext
      rw [hρ]
      exact h t (Subgroup.mem_subgroupOf.mp ht)
  obtain ⟨z, hzfix, hz1⟩ := CFSG.QuasithinUnique.L246.C123.exists_fixed_ne_one ρ hU16 hT8
  have hle2 := CFSG.QuasithinUnique.L246.C123.card_fixU_le_two ρ hU16 hinj hT8
  have hzT : ∀ t ∈ T, t * (z : G) * t⁻¹ = z := (hfix z).mp hzfix
  have hz1' : (z : G) ≠ 1 := fun h => hz1 (Subtype.ext h)
  have hzz : (z : G) ^ 2 = 1 := by rw [← Subgroup.coe_pow, hU2 z, Subgroup.coe_one]
  have hzo : orderOf (z : G) = 2 := orderOf_eq_prime hzz hz1'
  refine ⟨z, hzo, ?_, z.2⟩
  apply le_antisymm
  · intro x hx
    obtain ⟨hxT, hxc⟩ := Subgroup.mem_inf.mp hx
    have hxU : x ∈ U := hC (Subgroup.mem_inf.mpr ⟨hTM2 hxT, Subgroup.mem_centralizer_iff.mpr
      fun u hu => (Subgroup.mem_centralizer_iff.mp hxc u (hUT hu))⟩)
    have hxfix : (⟨x, hxU⟩ : ↥U) ∈ fixU ρ PT := by
      rw [hfix]
      intro t ht
      have h1 := Subgroup.mem_centralizer_iff.mp hxc t ht
      calc t * x * t⁻¹ = x * t * t⁻¹ := by rw [h1]
        _ = x := by group

    by_cases hx1 : (⟨x, hxU⟩ : ↥U) = 1
    · have : x = 1 := congrArg Subtype.val hx1
      rw [this]
      exact Subgroup.one_mem _
    · have heq : (⟨x, hxU⟩ : ↥U) = z := by
        by_contra hne
        have hsub : ({1, z, ⟨x, hxU⟩} : Set ↥U) ⊆ (fixU ρ PT : Set ↥U) := by
          intro w hw
          rcases hw with rfl | rfl | rfl
          · exact (fixU ρ PT).one_mem
          · exact hzfix
          · exact hxfix
        have h3 : ({1, z, ⟨x, hxU⟩} : Set ↥U).ncard = 3 := by
          rw [Set.ncard_insert_of_notMem, Set.ncard_pair (Ne.symm hne)]
          simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
          exact ⟨Ne.symm hz1, Ne.symm hx1⟩
        have h4 := Set.ncard_le_ncard hsub (Set.toFinite _)
        have h5 : Nat.card (fixU ρ PT) = ((fixU ρ PT : Subgroup ↥U) : Set ↥U).ncard :=
          Nat.card_coe_set_eq _
        omega
      have : x = z := congrArg Subtype.val heq
      rw [this]
      exact Subgroup.mem_zpowers _
  · rw [Subgroup.zpowers_le]
    refine Subgroup.mem_inf.mpr ⟨hUT z.2, Subgroup.mem_centralizer_iff.mpr fun t ht => ?_⟩
    have h1 := hzT t ht
    calc t * (z : G) = t * z * t⁻¹ * t := by group
      _ = z * t := by rw [h1]

theorem stmt5_2_12_transitive_of_F4 (hQ : Stmt5_2_8_Q_F4) {T M L V H B D L₂ M2 : Subgroup G} {n : ℕ}
    {π : ↥M2 →* Equiv.Perm (Fin 7)} (hyp : Hyp5_2_4 G T M L V H B D L₂ n)
    (hM23 : IsOfTypeM23 M L H B D T) (hS : IsM23Setting T H M2 π) :
    ∀ u ∈ pCoreOf 2 M2, ∀ v ∈ pCoreOf 2 M2, u ≠ 1 → v ≠ 1 → ∃ g ∈ M2, g * u * g⁻¹ = v := by
  obtain ⟨hab, -, -⟩ := hQ G T M L V H B D L₂ n M2 hyp hM23 hS.K_lt hS.maximal hS.excA7
  obtain ⟨π', ρ, hsurj, hker, hinj, hρ, hU16, hU2, hT8, hUT, -⟩ :=
    exists_rho_of_setting_F4 hQ hyp hM23 hS
  let _ := commGroupOfComm (pCoreOf 2 M2) fun a ha b hb =>
    congrArg Subtype.val (hab.1.1.comm ⟨a, ha⟩ ⟨b, hb⟩)
  intro u hu v hv hu1 hv1
  obtain ⟨z, hzfix, hz1⟩ := CFSG.QuasithinUnique.L246.C123.exists_fixed_ne_one ρ hU16 hT8
  obtain ⟨a, ha⟩ := CFSG.QuasithinUnique.L246.C123.exists_apply_eq ρ hU16 hinj hT8 hz1 hzfix
    (v := ⟨u, hu⟩) (fun h => hu1 (congrArg Subtype.val h))
  obtain ⟨b, hb⟩ := CFSG.QuasithinUnique.L246.C123.exists_apply_eq ρ hU16 hinj hT8 hz1 hzfix
    (v := ⟨v, hv⟩) (fun h => hv1 (congrArg Subtype.val h))
  obtain ⟨g, hg⟩ := hsurj (b * a⁻¹)
  refine ⟨g, g.2, ?_⟩
  have h1 : ρ (π' g) ⟨u, hu⟩ = ⟨v, hv⟩ := by
    rw [hg, ← ha, ← hb, ← MulAut.mul_apply, ← map_mul, mul_assoc, inv_mul_cancel, mul_one]
  have h2 := congrArg Subtype.val h1
  rwa [hρ] at h2

end CFSG.Quasithin.H13
