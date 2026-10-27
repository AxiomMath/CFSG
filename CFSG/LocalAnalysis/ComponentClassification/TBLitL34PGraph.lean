module

public import CFSG.LocalAnalysis.ComponentClassification.TBLitL34PFrame
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34FactsSec5Four

public section

namespace CFSG.ComponentClassification.TBLit.L34P

open CFSG Subgroup CFSG.PSL3Four CFSG.PSL3Four.Native CFSG.ComponentClassification.PSL3Four
open CFSG.ComponentClassification.GrSLit CFSG.ComponentClassification.GrSLit.L34Facts
open CFSG.LieType.Multipliers CFSG.LieType.Multipliers.L34
open scoped MatrixGroups

theorem r₃_comm_tg4 : wordPerm (tg 4) * r₃ = r₃ * wordPerm (tg 4) :=
  (((tabRep_wordTab _).comp tabRep_r₃).beq_iff (tabRep_r₃.comp (tabRep_wordTab _))).1
    (by decide +kernel)

theorem r₃_comm_tg8 : wordPerm (tg 8) * r₃ = r₃ * wordPerm (tg 8) :=
  (((tabRep_wordTab _).comp tabRep_r₃).beq_iff (tabRep_r₃.comp (tabRep_wordTab _))).1
    (by decide +kernel)

theorem r₃_comm_tg12 : wordPerm (tg 12) * r₃ = r₃ * wordPerm (tg 12) :=
  (((tabRep_wordTab _).comp tabRep_r₃).beq_iff (tabRep_r₃.comp (tabRep_wordTab _))).1
    (by decide +kernel)

theorem Z0_le_C₃ :
    Z0 ≤ C₃ := by
  intro t ht
  refine mem_inf.mpr ⟨mem_centralizer_singleton_iff.mpr ?_, T0_le_S (mem_inf.mp
    (show t ∈ centralizer (T0 : Set (Equiv.Perm (Fin 42))) ⊓ T0 from ht)).2⟩
  obtain ⟨k, hk, rfl⟩ := mem_Z0.1 ht
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl
  · rw [wordPerm_tg_zero, one_mul, mul_one]
  · exact r₃_comm_tg4
  · exact r₃_comm_tg8
  · exact r₃_comm_tg12

theorem factorization_sixty_two : (60 : ℕ).factorization 2 = 2 := by
  have hprod : (60 : ℕ) = 2 ^ 2 * 15 := by norm_num
  rw [hprod, Nat.factorization_mul (by norm_num) (by norm_num), Finsupp.add_apply,
    Nat.factorization_pow, Finsupp.smul_apply, Nat.Prime.factorization_self Nat.prime_two,
    Nat.factorization_eq_zero_of_not_dvd (by norm_num : ¬ 2 ∣ 15)]
  rfl

variable {X : Type} [Group X] [Finite X]

theorem false_of_graph
    {β : X} {K L : Subgroup X}
    (hK : ⁅K, K⁆ = K) (hβN : β ∈ normalizer (K : Set X)) (hLK : L ≤ K)
    (hLβ : L ≤ centralizer ({β} : Set X)) {F : Type*} [Field F] [Finite F]
    (hodd : Odd (Nat.card F)) (e : ↥L ⧸ pPrimeCore 2 ↥L ≃* SL(2, F))
    {q : Jhat K →* Equiv.Perm (Fin 42)} (hqS : ∀ e, q e ∈ S) (hqsurj : ∀ s ∈ S, ∃ e, q e = s)
    (hqker : q.ker = center (Jhat K)) (h3 : ∀ e ∈ q.ker, e ^ 3 = 1 → e = 1)
    (hβ : ∀ e, q (betaHat K hβN e) = r₃ * q e * r₃⁻¹) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨l, hl, hls⟩ := exists_lam (commutator_jhat hK) q hqS hqsurj (hqker ▸ le_refl _)
  have hQS : IsQSetting q l := ⟨hqS, hqsurj, hqker, h3, hl, hls⟩
  obtain ⟨Q⟩ : Nonempty (Sylow 2 ↥L) := inferInstance
  set ψ := imageHom hLK q with hψ
  have hψC : ∀ s, ψ s ∈ C₃ := fun s => range_imageHom_le hLK hβN hLβ hqS hβ ⟨s, rfl⟩
  have hW : IsPGroup 2 (((Q : Subgroup ↥L).map ψ).subgroupOf C₃) :=
    ((Q.isPGroup').map ψ).comap_subtype
  obtain ⟨P, hWP⟩ := hW.exists_le_sylow
  have hZ0card : Nat.card (Z0.subgroupOf C₃) = 2 ^ (Nat.card ↥C₃).factorization 2 := by
    rw [card_C₃, factorization_sixty_two,
      Nat.card_congr (subgroupOfEquivOfLe Z0_le_C₃).toEquiv, card_Z0]
    norm_num
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq ↥C₃ (Sylow.ofCard _ hZ0card) P
  have hconj : ∀ s ∈ (Q : Subgroup ↥L), ((g : Equiv.Perm (Fin 42)))⁻¹ * ψ s * g ∈ Z0 := by
    intro s hs
    have h1 : (⟨ψ s, hψC s⟩ : ↥C₃) ∈ (P : Subgroup ↥C₃) :=
      hWP (mem_subgroupOf.mpr ⟨s, hs, rfl⟩)
    rw [← hg, Sylow.coe_subgroup_smul, Subgroup.mem_smul_pointwise_iff_exists,
      Sylow.coe_ofCard] at h1
    obtain ⟨b, hb, hby⟩ := h1
    have hval : (g : Equiv.Perm (Fin 42)) * b * (g : Equiv.Perm (Fin 42))⁻¹ = ψ s := by
      have := congrArg Subtype.val hby
      simpa [MulAut.smul_def, MulAut.conj_apply] using this
    rw [← hval]
    have e1 : (g : Equiv.Perm (Fin 42))⁻¹ * ((g : Equiv.Perm (Fin 42)) * b *
        (g : Equiv.Perm (Fin 42))⁻¹) * g = b := by group
    rw [e1]
    exact mem_subgroupOf.mp hb
  obtain ⟨ĉ, hĉ⟩ := hqsurj g (mem_inf.mp g.2).2
  have hcomm : ∀ s ∈ (Q : Subgroup ↥L), ∀ t ∈ (Q : Subgroup ↥L), s * t = t * s := by
    intro s hs t ht
    have hs' : q (ĉ⁻¹ * jq K ⟨s, hLK s.2⟩ * ĉ) ∈ Z0 := by
      rw [map_mul, map_mul, map_inv, hĉ]
      exact hconj s hs
    have ht' : q (ĉ⁻¹ * jq K ⟨t, hLK t.2⟩ * ĉ) ∈ Z0 := by
      rw [map_mul, map_mul, map_inv, hĉ]
      exact hconj t ht
    have h1 := hQS.comm_of_Z0 hs' ht'
    have h2 : jq K ⟨s, hLK s.2⟩ * jq K ⟨t, hLK t.2⟩ =
        jq K ⟨t, hLK t.2⟩ * jq K ⟨s, hLK s.2⟩ := by
      have h1' : ĉ⁻¹ * (jq K ⟨s, hLK s.2⟩ * jq K ⟨t, hLK t.2⟩) * ĉ =
          ĉ⁻¹ * (jq K ⟨t, hLK t.2⟩ * jq K ⟨s, hLK s.2⟩) * ĉ := by
        calc ĉ⁻¹ * (jq K ⟨s, hLK s.2⟩ * jq K ⟨t, hLK t.2⟩) * ĉ =
            (ĉ⁻¹ * jq K ⟨s, hLK s.2⟩ * ĉ) * (ĉ⁻¹ * jq K ⟨t, hLK t.2⟩ * ĉ) := by group
          _ = (ĉ⁻¹ * jq K ⟨t, hLK t.2⟩ * ĉ) * (ĉ⁻¹ * jq K ⟨s, hLK s.2⟩ * ĉ) := h1
          _ = ĉ⁻¹ * (jq K ⟨t, hLK t.2⟩ * jq K ⟨s, hLK s.2⟩) * ĉ := by group
      exact mul_left_cancel (mul_right_cancel h1')
    set Qx : Subgroup X := (Q : Subgroup ↥L).map L.subtype with hQx
    have hQxK : Qx ≤ K := by
      rintro _ ⟨u, -, rfl⟩
      exact hLK u.2
    have hQx2 : IsPGroup 2 Qx := (Q.isPGroup').map L.subtype
    have hmem : ((s * t * s⁻¹ * t⁻¹ : ↥L) : X) ∈ Qx :=
      ⟨_, (Q : Subgroup ↥L).mul_mem ((Q : Subgroup ↥L).mul_mem
        ((Q : Subgroup ↥L).mul_mem hs ht) ((Q : Subgroup ↥L).inv_mem hs))
        ((Q : Subgroup ↥L).inv_mem ht), rfl⟩
    have hjq : jq K ⟨((s * t * s⁻¹ * t⁻¹ : ↥L) : X), hQxK hmem⟩ = 1 := by
      have e1 : (⟨((s * t * s⁻¹ * t⁻¹ : ↥L) : X), hQxK hmem⟩ : K) =
          ⟨s, hLK s.2⟩ * ⟨t, hLK t.2⟩ * (⟨s, hLK s.2⟩)⁻¹ * (⟨t, hLK t.2⟩)⁻¹ := rfl
      rw [e1, map_mul, map_mul, map_mul, map_inv, map_inv, h2]
      group
    have h3' := eq_one_of_jq_eq_one hQxK hQx2 hmem hjq
    have h4 : s * t * s⁻¹ * t⁻¹ = 1 := Subtype.ext h3'
    calc s * t = s * t * s⁻¹ * t⁻¹ * (t * s) := by group
      _ = t * s := by rw [h4, one_mul]
  set π : ↥L →* SL(2, F) := e.toMonoidHom.comp (QuotientGroup.mk' (pPrimeCore 2 ↥L)) with hπ
  have hπs : Function.Surjective π := e.surjective.comp (QuotientGroup.mk'_surjective _)
  apply CFSG.Semidihedral.OddFieldSL2.sylow_two_not_isMulCommutative F hodd
    (Q.mapSurjective hπs)
  refine ⟨⟨fun a b => Subtype.ext ?_⟩⟩
  obtain ⟨s, hs, hsa⟩ := (Sylow.coe_mapSurjective hπs Q ▸ a.2 :
    (a : SL(2, F)) ∈ (Q : Subgroup ↥L).map π)
  obtain ⟨t, ht, htb⟩ := (Sylow.coe_mapSurjective hπs Q ▸ b.2 :
    (b : SL(2, F)) ∈ (Q : Subgroup ↥L).map π)
  rw [Subgroup.coe_mul, Subgroup.coe_mul, ← hsa, ← htb, ← map_mul, ← map_mul, hcomm s hs t ht]

end CFSG.ComponentClassification.TBLit.L34P
