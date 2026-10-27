module

public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Final

public section

namespace CFSG.Semidihedral.ParameterFive

open CFSG.BenderSuzuki PFAppendixIII PFchapter1section1

theorem isInvolution_of_orderOf_eq_two {G : Type} [Group G] {x : G} (hx : orderOf x = 2) :
    IsInvolution x :=
  ⟨fun h => by rw [h, orderOf_one] at hx; exact absurd hx (by norm_num),
    by rw [← hx]; exact pow_orderOf_eq_one x⟩

theorem exists_conj_mem_sylow_of_le {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    (S : Sylow p G) {M : Subgroup G} (hSM : (S : Subgroup G) ≤ M) {x : G} (hxM : x ∈ M)
    {k : ℕ} (hx : orderOf x = p ^ k) : ∃ m ∈ M, m⁻¹ * x * m ∈ (S : Subgroup G) := by
  let x' : M := ⟨x, hxM⟩
  have hP : IsPGroup p (Subgroup.zpowers x') :=
    IsPGroup.of_card (n := k) (by rw [Nat.card_zpowers, Subgroup.orderOf_mk, hx])
  obtain ⟨Q, hQ⟩ := hP.exists_le_sylow
  obtain ⟨m, hm⟩ := MulAction.exists_smul_eq M (S.subtype hSM) Q
  have hxQ : x' ∈ (Q : Subgroup M) := hQ (Subgroup.mem_zpowers x')
  rw [← hm, Sylow.coe_subgroup_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem] at hxQ
  refine ⟨m, m.2, ?_⟩
  have h2 : (MulAut.conj m)⁻¹ • x' = m⁻¹ * x' * m := by
    rw [MulAut.smul_def, ← map_inv, MulAut.conj_apply, inv_inv]
  rw [h2, Sylow.coe_subtype, Subgroup.mem_subgroupOf] at hxQ
  exact hxQ

theorem isStronglyEmbedded_of_conj {G : Type} [Group G] [Finite G] {t : G}
    (ht : orderOf t = 2) {M : Subgroup G} (hMtop : M ≠ ⊤)
    (hCM : Subgroup.centralizer {t} ≤ M)
    (hconj : ∀ x ∈ M, orderOf x = 2 → ∃ m ∈ M, m * t * m⁻¹ = x) :
    IsStronglyEmbedded M := by
  have htM : t ∈ M := hCM (Subgroup.mem_centralizer_singleton_iff.mpr rfl)
  refine ⟨hMtop, ⟨t, htM, isInvolution_of_orderOf_eq_two ht⟩, ?_⟩
  intro g hgM x hxM hxg hx
  have hy : g * x * g⁻¹ ∈ M := by
    rw [rightConjugate, Subgroup.conjBy, Subgroup.mem_map] at hxg
    obtain ⟨y, hy, hyx⟩ := hxg
    have hyx' : y = g * x * g⁻¹ := by
      rw [← hyx]
      simp [mul_assoc]
    rw [← hyx']
    exact hy
  have hx2 : orderOf x = 2 := orderOf_eq_prime hx.sq_eq_one hx.ne_one
  have hy2 : orderOf (g * x * g⁻¹) = 2 := by
    rw [← MulAut.conj_apply, MulEquiv.orderOf_eq]
    exact hx2
  obtain ⟨a, haM, hat⟩ := hconj x hxM hx2
  obtain ⟨b, hbM, hbt⟩ := hconj _ hy hy2
  have hc : b⁻¹ * g * a ∈ Subgroup.centralizer {t} := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    have h1 : g * (a * t * a⁻¹) * g⁻¹ = b * t * b⁻¹ := by rw [hat, hbt]
    calc b⁻¹ * g * a * t = b⁻¹ * (g * (a * t * a⁻¹) * g⁻¹) * g * a := by group
      _ = b⁻¹ * (b * t * b⁻¹) * g * a := by rw [h1]
      _ = t * (b⁻¹ * g * a) := by group
  apply hgM
  have hg : g = b * (b⁻¹ * g * a) * a⁻¹ := by group
  rw [hg]
  exact M.mul_mem (M.mul_mem hbM (hCM hc)) (M.inv_mem haM)

theorem eq_top_of_centralizer_le
    {G : Type} [Group G] [Finite G] [IsSimpleGroup G]
    {t : G} (ht : orderOf t = 2) {M : Subgroup G} (hCM : Subgroup.centralizer {t} ≤ M)
    (hconj : ∀ x ∈ M, orderOf x = 2 → ∃ m ∈ M, m * t * m⁻¹ = x)
    (hrank : ∃ E : Subgroup G, Nat.card E = 4 ∧ ∀ x ∈ E, x ^ 2 = 1)
    (hns : ¬ Group.IsSolvable (Subgroup.centralizer ({t} : Set G))) : M = ⊤ := by
  by_contra hMtop
  have hM := isStronglyEmbedded_of_conj ht hMtop hCM hconj
  have hL : involutionCore G = ⊤ := hM.involutionCore_eq_top_of_isSimple inferInstance
  rcases theorem_SE M hM with hlow | hB
  · apply hlow
    obtain ⟨E, hE4, hE2⟩ := hrank
    refine ⟨E.subgroupOf (involutionCore G), ?_, ?_⟩
    · have hEL : E ≤ involutionCore G := hL ▸ le_top
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hEL).toEquiv, hE4]
    · rintro ⟨⟨x, hxL⟩, hxE⟩
      apply Subtype.ext
      apply Subtype.ext
      exact hE2 x hxE
  · obtain ⟨-, -, hsolv, -⟩ := hB
    set L := involutionCore G with hLdef
    let eL : L ≃* G := (MulEquiv.subgroupCongr hL).trans Subgroup.topEquiv
    have hmemL : ∀ x : G, x ∈ L := fun x => by rw [hL]; exact Subgroup.mem_top x
    have hsimpleL : IsSimpleGroup L := eL.isSimpleGroup_congr.mpr inferInstance
    have hcore : twoPrimeCore L = ⊥ := by
      rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (twoPrimeCore L) with h | h
      · exact h
      · exfalso
        have htL : t ∈ L := hmemL t
        have hodd : Odd (Nat.card (twoPrimeCore L)) :=
          Nat.coprime_two_left.mp (CFSG.pPrimeCore_coprime_card (p := 2) (G := L))
        have htcore : (⟨t, htL⟩ : L) ∈ twoPrimeCore L := h ▸ Subgroup.mem_top _
        have h2 : orderOf (⟨⟨t, htL⟩, htcore⟩ : twoPrimeCore L) = 2 := by
          rw [Subgroup.orderOf_mk, Subgroup.orderOf_mk]
          exact ht
        have := orderOf_dvd_natCard (⟨⟨t, htL⟩, htcore⟩ : twoPrimeCore L)
        rw [h2] at this
        exact (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr this)
    set B := (((M ⊓ L).subgroupOf L).map (QuotientGroup.mk' (twoPrimeCore L))) with hBdef
    have : Group.IsSolvable B := hsolv
    let φ : Subgroup.centralizer ({t} : Set G) →* B :=
      { toFun := fun c => ⟨QuotientGroup.mk' (twoPrimeCore L) ⟨c, hmemL c⟩,
          ⟨⟨c, hmemL c⟩, ⟨hCM c.2, hmemL c⟩, rfl⟩⟩
        map_one' := rfl
        map_mul' := fun _ _ => rfl }
    have hφ : Function.Injective φ := by
      intro a b hab
      have h := congrArg Subtype.val hab
      change QuotientGroup.mk' (twoPrimeCore L) _ = QuotientGroup.mk' (twoPrimeCore L) _ at h
      rw [QuotientGroup.mk'_eq_mk', hcore] at h
      obtain ⟨z, hz, hzeq⟩ := h
      rw [Subgroup.mem_bot] at hz
      rw [hz, mul_one] at hzeq
      exact Subtype.ext (congrArg (fun x : L => (x : G)) hzeq)
    exact hns (Group.isSolvable_of_isSolvable_injective hφ)

end CFSG.Semidihedral.ParameterFive
