module

public import Mathlib.GroupTheory.SchurZassenhaus

public section

namespace CFSG.AGLEmbeddingD2.Tits.OrdinaryProofs

open scoped Pointwise

theorem exists_lift_of_normal_coprime {G : Type*} [Group G] [Finite G]
    (E A U : Subgroup G) [E.Normal] [A.Normal] (hEA : E ≤ A)
    (hU : IsPGroup 2 U) (hodd : ¬ 2 ∣ E.relIndex A)
    (hcop : Nat.Coprime (E.relIndex A) A.index) (hidx : A.index = 3 * E.relIndex U) :
    ∃ S : Subgroup G, U ≤ S ∧ S ⊓ A = E ∧ S ⊔ A = ⊤ := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hfs : Function.Surjective (QuotientGroup.mk' E : G →* G ⧸ E) :=
    QuotientGroup.mk'_surjective E
  have hcardA : Nat.card (A.map (QuotientGroup.mk' E)) = E.relIndex A := by
    have h := Subgroup.relIndex_ker (QuotientGroup.mk' E : G →* G ⧸ E) (K := A)
    rw [QuotientGroup.ker_mk'] at h
    exact h.symm
  have hcardU : Nat.card (U.map (QuotientGroup.mk' E)) = E.relIndex U := by
    have h := Subgroup.relIndex_ker (QuotientGroup.mk' E : G →* G ⧸ E) (K := U)
    rw [QuotientGroup.ker_mk'] at h
    exact h.symm
  have hindex : (A.map (QuotientGroup.mk' E)).index = A.index := by
    have h := Subgroup.index_comap_of_surjective (H := A.map (QuotientGroup.mk' E)) hfs
    rw [QuotientGroup.comap_map_mk', sup_eq_right.2 hEA] at h
    exact h.symm
  have hAn : (A.map (QuotientGroup.mk' E)).Normal :=
    Subgroup.Normal.map inferInstance _ hfs
  have hcopA : Nat.Coprime (Nat.card (A.map (QuotientGroup.mk' E)))
      (A.map (QuotientGroup.mk' E)).index := by
    rw [hcardA, hindex]
    exact hcop
  obtain ⟨Hb, hHb⟩ := Subgroup.exists_right_complement'_of_coprime hcopA
  obtain ⟨k, hk⟩ : ∃ k : ℕ, Nat.card (U.map (QuotientGroup.mk' E)) = 2 ^ k :=
    IsPGroup.iff_card.1 (hU.map _)
  have hu : E.relIndex U = 2 ^ k := hcardU.symm.trans hk
  have hHbcard : Nat.card Hb = 3 * 2 ^ k := by
    rw [← hHb.symm.index_eq_card, hindex, hidx, hu]
  have hQcard : Nat.card (A.map (QuotientGroup.mk' E)) * Nat.card Hb = Nat.card (G ⧸ E) :=
    hHb.card_mul_card
  have hidxS : ∀ S : Subgroup (G ⧸ E), Nat.card S = 2 ^ k → ¬ 2 ∣ S.index := by
    intro S hS hdiv
    have h1 : Nat.card S * S.index = Nat.card (G ⧸ E) := S.card_mul_index
    rw [hS, ← hQcard, hcardA, hHbcard] at h1
    have h2 : S.index = 3 * E.relIndex A := by
      apply Nat.eq_of_mul_eq_mul_left (pow_pos two_pos k)
      rw [h1]
      ring
    rcases (Nat.Prime.dvd_mul Nat.prime_two).1 (h2 ▸ hdiv) with h3 | h3
    · norm_num at h3
    · exact hodd h3
  obtain ⟨K, hKcard, hKle⟩ : ∃ K : Subgroup (G ⧸ E), Nat.card K = 2 ^ k ∧ K ≤ Hb := by
    obtain ⟨K, h1, -, h3⟩ := Sylow.exists_subgroup_card_pow_prime_le_le Nat.prime_two
      (H := ⊥) (L := Hb) (n := k) (by rw [Subgroup.card_bot]; exact one_dvd _)
      (by rw [hHbcard]; exact dvd_mul_left _ _) bot_le
    exact ⟨K, h1, h3⟩
  have hKp : IsPGroup 2 K := IsPGroup.iff_card.2 ⟨k, hKcard⟩
  have hŪp : IsPGroup 2 (U.map (QuotientGroup.mk' E)) := hU.map _
  let SK : Sylow 2 (G ⧸ E) := hKp.toSylow (hidxS K hKcard)
  let SU : Sylow 2 (G ⧸ E) := hŪp.toSylow (hidxS _ hk)
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (G ⧸ E) SK SU
  have hsetE := congrArg (fun P : Sylow 2 (G ⧸ E) => (P : Set (G ⧸ E))) hg
  rw [Sylow.coe_smul] at hsetE
  have hŪsub : ∀ x ∈ U.map (QuotientGroup.mk' E), ∃ y ∈ K, MulAut.conj g y = x := by
    intro x hx
    have hx' : x ∈ (SU : Set (G ⧸ E)) := hx
    rw [← hsetE] at hx'
    obtain ⟨y, hy, hyx⟩ := Set.mem_smul_set.1 hx'
    exact ⟨y, hy, hyx⟩
  obtain ⟨Ĥ, hĤ⟩ : ∃ Ĥ : Subgroup (G ⧸ E), ∀ x, x ∈ Ĥ ↔ ∃ z ∈ Hb, MulAut.conj g z = x :=
    ⟨Hb.map (MulAut.conj g).toMonoidHom, fun x => Subgroup.mem_map⟩
  have hĤU : ∀ x ∈ U.map (QuotientGroup.mk' E), x ∈ Ĥ := by
    intro x hx
    obtain ⟨y, hy, hyx⟩ := hŪsub x hx
    exact (hĤ x).2 ⟨y, hKle hy, hyx⟩
  have hdisj : ∀ x ∈ A.map (QuotientGroup.mk' E), x ∈ Ĥ → x = 1 := by
    intro x hxA hxH
    obtain ⟨z, hz, rfl⟩ := (hĤ x).1 hxH
    have hz' : z ∈ A.map (QuotientGroup.mk' E) := by
      have := hAn.conj_mem _ hxA g⁻¹
      simpa [MulAut.conj_apply, mul_assoc] using this
    have hzb : z ∈ (A.map (QuotientGroup.mk' E)) ⊓ Hb := ⟨hz', hz⟩
    rw [disjoint_iff.1 hHb.disjoint, Subgroup.mem_bot] at hzb
    simp [hzb]
  have hcomp : ∀ q : G ⧸ E, q ∈ (A.map (QuotientGroup.mk' E)) ⊔ Ĥ := by
    intro q
    have hq' : g⁻¹ * q * g⁻¹⁻¹ ∈ (A.map (QuotientGroup.mk' E)) ⊔ Hb := by
      rw [hHb.sup_eq_top]
      exact Subgroup.mem_top _
    obtain ⟨y, hy, z, hz, hyz⟩ := Subgroup.mem_sup_of_normal_left.1 hq'
    have hq_eq : q = (g * y * g⁻¹) * (g * z * g⁻¹) := by
      calc q = g * (g⁻¹ * q * g⁻¹⁻¹) * g⁻¹ := by group
        _ = g * (y * z) * g⁻¹ := by rw [hyz]
        _ = _ := by group
    rw [hq_eq]
    exact Subgroup.mul_mem_sup (hAn.conj_mem y hy g) ((hĤ _).2 ⟨z, hz, rfl⟩)
  have hcomp' : ∀ q : G ⧸ E, q ∈ Ĥ ⊔ (A.map (QuotientGroup.mk' E)) := fun q => by
    rw [sup_comm]
    exact hcomp q
  refine ⟨Subgroup.comap (QuotientGroup.mk' E : G →* G ⧸ E) Ĥ, ?_, ?_, ?_⟩
  · intro x hx
    exact Subgroup.mem_comap.2 (hĤU _ (Subgroup.mem_map_of_mem _ hx))
  · ext x
    constructor
    · rintro ⟨hxS, hxA⟩
      have h1 : (QuotientGroup.mk' E : G →* G ⧸ E) x = 1 :=
        hdisj _ (Subgroup.mem_map_of_mem _ hxA) (Subgroup.mem_comap.1 hxS)
      exact (QuotientGroup.eq_one_iff x).1 h1
    · intro hxE
      refine ⟨Subgroup.mem_comap.2 ?_, hEA hxE⟩
      rw [show (QuotientGroup.mk' E : G →* G ⧸ E) x = 1 from (QuotientGroup.eq_one_iff x).2 hxE]
      exact Ĥ.one_mem
  · rw [eq_top_iff]
    intro x _
    obtain ⟨h, hh, y, hy, hxy⟩ :=
      Subgroup.mem_sup_of_normal_right.1 (hcomp' ((QuotientGroup.mk' E : G →* G ⧸ E) x))
    obtain ⟨a, ha, hay⟩ := Subgroup.mem_map.1 hy
    obtain ⟨s, hs⟩ := hfs h
    have hw : (QuotientGroup.mk' E : G →* G ⧸ E) (a⁻¹ * s⁻¹ * x) = 1 := by
      rw [map_mul, map_mul, map_inv, map_inv, hay, hs, ← hxy]
      group
    have hwE : a⁻¹ * s⁻¹ * x ∈ E := (QuotientGroup.eq_one_iff _).1 hw
    have hsx : s * (a * (a⁻¹ * s⁻¹ * x)) = x := by group
    rw [← hsx]
    exact Subgroup.mul_mem_sup (Subgroup.mem_comap.2 (by rw [hs]; exact hh))
      (A.mul_mem ha (hEA hwE))

theorem exists_order_three_permuting_of_normal_coprime {Γ : Type*} [Group Γ] [Finite Γ]
    (D U : Subgroup Γ) [D.Normal] (hD3 : ¬ 3 ∣ Nat.card D) (hU : IsPGroup 2 U)
    (hUD : ¬ 2 ∣ ((U ⊓ D).subgroupOf D).index) (hidx : (U ⊔ D).index = 3) :
    ∃ P : Subgroup Γ, Nat.card P = 3 ∧ (P : Set Γ) * U = (U : Set Γ) * P := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.1 hU
  have hUD' : ¬ 2 ∣ (U ⊓ D).relIndex D := hUD
  have hFp : IsPGroup 2 ((U ⊓ D).subgroupOf D) :=
    (hU.to_le (inf_le_left : U ⊓ D ≤ U)).comap_of_injective D.subtype Subtype.val_injective
  obtain ⟨Ps, hPs⟩ : ∃ Ps : Sylow 2 D, (Ps : Subgroup D) = (U ⊓ D).subgroupOf D :=
    ⟨hFp.toSylow hUD, IsPGroup.toSylow_coe hFp hUD⟩
  have hPsF : Subgroup.map D.subtype (Ps : Subgroup D) = U ⊓ D := by
    rw [hPs, Subgroup.subgroupOf_map_subtype, inf_eq_left.2 (inf_le_right : U ⊓ D ≤ D)]
  have hFrat : Subgroup.normalizer ((U ⊓ D : Subgroup Γ) : Set Γ) ⊔ D = ⊤ := by
    have h := Sylow.normalizer_sup_eq_top Ps
    rw [hPsF] at h
    exact h
  set N : Subgroup Γ := Subgroup.normalizer ((U ⊓ D : Subgroup Γ) : Set Γ) with hN
  have hUN : U ≤ N := by
    intro u hu
    rw [hN, Subgroup.mem_normalizer_iff]
    intro h
    have hu' : u⁻¹ ∈ U := U.inv_mem hu
    constructor
    · intro hh
      obtain ⟨hh1, hh2⟩ := Subgroup.mem_inf.1 hh
      exact Subgroup.mem_inf.2
        ⟨U.mul_mem (U.mul_mem hu hh1) hu', (inferInstance : D.Normal).conj_mem h hh2 u⟩
    · intro hh
      obtain ⟨hh1, hh2⟩ := Subgroup.mem_inf.1 hh
      have key : h = u⁻¹ * (u * h * u⁻¹) * u⁻¹⁻¹ := by group
      rw [key]
      exact Subgroup.mem_inf.2
        ⟨U.mul_mem (U.mul_mem hu' hh1) (U.inv_mem hu'),
          (inferInstance : D.Normal).conj_mem _ hh2 u⁻¹⟩
  have hE'n : ((U ⊓ D).subgroupOf N).Normal :=
    Subgroup.normal_subgroupOf_of_le_normalizer le_rfl
  have hDn : (D.subgroupOf N).Normal := inferInstance
  have hU' : IsPGroup 2 (U.subgroupOf N) := hU.comap_of_injective N.subtype Subtype.val_injective
  have hEA : (U ⊓ D).subgroupOf N ≤ D.subgroupOf N := fun x hx =>
    Subgroup.mem_subgroupOf.2 (Subgroup.mem_inf.1 (Subgroup.mem_subgroupOf.1 hx)).2
  have hEU' : (U ⊓ D).subgroupOf N ≤ U.subgroupOf N := fun x hx =>
    Subgroup.mem_subgroupOf.2 (Subgroup.mem_inf.1 (Subgroup.mem_subgroupOf.1 hx)).1
  have hArel : ((U ⊓ D).subgroupOf N).relIndex (D.subgroupOf N) = (U ⊓ D).relIndex (N ⊓ D) := by
    rw [← Subgroup.inf_subgroupOf_left D N,
      Subgroup.relIndex_subgroupOf (H := U ⊓ D) (K := N ⊓ D) (L := N) inf_le_left]
  have hUDN : U ⊓ D ≤ N ⊓ D := inf_le_inf hUN le_rfl
  have hmul : (U ⊓ D).relIndex (N ⊓ D) * (N ⊓ D).relIndex D = (U ⊓ D).relIndex D :=
    Subgroup.relIndex_mul_relIndex (H := U ⊓ D) (K := N ⊓ D) (L := D) hUDN inf_le_right
  have hadvD : (U ⊓ D).relIndex (N ⊓ D) ∣ Nat.card D :=
    dvd_trans ⟨_, hmul.symm⟩ (Subgroup.relIndex_dvd_card (U ⊓ D) D)
  have hodd_a : ¬ 2 ∣ (U ⊓ D).relIndex (N ⊓ D) := fun h => hUD' (dvd_trans h ⟨_, hmul.symm⟩)
  have hcop3 : Nat.Coprime ((U ⊓ D).relIndex (N ⊓ D)) 3 :=
    Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).2
      fun h => hD3 (dvd_trans h hadvD))
  have hcop2 : Nat.Coprime ((U ⊓ D).relIndex (N ⊓ D)) (2 ^ n) :=
    Nat.Coprime.pow_right n (Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).2 hodd_a))
  have hrU : (U ⊓ D).relIndex U ∣ 2 ^ n := by
    have h := (Subgroup.relIndex_dvd_card (H := U ⊓ D) (K := U))
    rwa [hn] at h
  have hcopU : Nat.Coprime ((U ⊓ D).relIndex (N ⊓ D)) ((U ⊓ D).relIndex U) :=
    Nat.Coprime.coprime_dvd_right hrU hcop2
  have hcop' : Nat.Coprime ((U ⊓ D).relIndex (N ⊓ D)) (3 * (U ⊓ D).relIndex U) :=
    Nat.Coprime.mul_right hcop3 hcopU
  have hDidx : (D.subgroupOf N).index = D.index := by
    have h := Subgroup.relIndex_sup_right (K := D) (H := N)
    rw [hFrat, Subgroup.relIndex_top_right] at h
    exact h.symm
  have hrel : D.relIndex U = (U ⊓ D).relIndex U := by
    unfold Subgroup.relIndex
    rw [inf_comm U D, Subgroup.inf_subgroupOf_right]
  have hDidx_val : D.index = 3 * (U ⊓ D).relIndex U := by
    have h := Subgroup.relIndex_mul_index (le_sup_right : D ≤ U ⊔ D)
    rw [hidx, Subgroup.relIndex_sup_right (K := D) (H := U), hrel] at h
    rw [← h]
    ring
  have hidx_core : (D.subgroupOf N).index = 3 * ((U ⊓ D).subgroupOf N).relIndex (U.subgroupOf N) := by
    rw [Subgroup.relIndex_subgroupOf hUN, hDidx, hDidx_val]
  have hodd_core : ¬ 2 ∣ ((U ⊓ D).subgroupOf N).relIndex (D.subgroupOf N) := by
    rw [hArel]
    exact hodd_a
  have hcop_core : Nat.Coprime (((U ⊓ D).subgroupOf N).relIndex (D.subgroupOf N))
      (D.subgroupOf N).index := by
    rw [hArel, hDidx, hDidx_val]
    exact hcop'
  obtain ⟨S', hS'U, hS'inf, hS'sup⟩ :=
    exists_lift_of_normal_coprime ((U ⊓ D).subgroupOf N) (D.subgroupOf N) (U.subgroupOf N)
      hEA hU' hodd_core hcop_core hidx_core
  have hA'S' : (D.subgroupOf N).relIndex S' = (D.subgroupOf N).index := by
    have h := Subgroup.relIndex_sup_right (K := D.subgroupOf N) (H := S')
    rw [hS'sup, Subgroup.relIndex_top_right] at h
    exact h.symm
  have c1 := Subgroup.relIndex_mul_card (H := D.subgroupOf N) (K := S')
  rw [hA'S', inf_comm, hS'inf] at c1
  have c2 := Subgroup.relIndex_mul_card (H := (U ⊓ D).subgroupOf N) (K := U.subgroupOf N)
  rw [Subgroup.relIndex_subgroupOf hUN, inf_eq_left.2 hEU'] at c2
  have hcardU' : Nat.card (U.subgroupOf N) = Nat.card U :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hUN).toEquiv
  have hS'card : Nat.card S' = 3 * Nat.card U := by
    rw [← c1, hDidx, hDidx_val, ← hcardU', ← c2]
    ring
  set S : Subgroup Γ := S'.map N.subtype with hSdef
  have hScard : Nat.card S = 3 * Nat.card U := by
    rw [hSdef, Subgroup.card_map_of_injective (f := N.subtype) Subtype.val_injective, hS'card]
  have hUS : U ≤ S := by
    intro u hu
    have hmem : (⟨u, hUN hu⟩ : N) ∈ U.subgroupOf N := Subgroup.mem_subgroupOf.2 hu
    exact Subgroup.mem_map_of_mem N.subtype (hS'U hmem)
  obtain ⟨K, hKcard, hKS⟩ : ∃ K : Subgroup Γ, Nat.card K = 3 ∧ K ≤ S := by
    obtain ⟨K, h1, -, h3⟩ := Sylow.exists_subgroup_card_pow_prime_le_le Nat.prime_three
      (H := ⊥) (L := S) (n := 1) (by rw [Subgroup.card_bot]; exact one_dvd _)
      (by rw [hScard, pow_one]; exact dvd_mul_right 3 _) bot_le
    exact ⟨K, by rw [h1, pow_one], h3⟩
  have hK0 : Nat.card (K.subgroupOf S) = 3 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hKS).toEquiv, hKcard]
  have hU0 : Nat.card (U.subgroupOf S) = Nat.card U :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hUS).toEquiv
  have hcompl : Subgroup.IsComplement' (K.subgroupOf S) (U.subgroupOf S) :=
    Subgroup.isComplement'_of_coprime (by rw [hK0, hU0, hScard])
      (by rw [hK0, hU0, hn]; exact Nat.Coprime.pow_right n (by norm_num))
  have hKS_sub : ∀ s ∈ S, ∃ k ∈ K, ∃ u ∈ U, k * u = s := by
    intro s hs
    obtain ⟨⟨⟨k₀, hk₀⟩, ⟨u₀, hu₀⟩⟩, hprod⟩ := hcompl.2 ⟨s, hs⟩
    refine ⟨(k₀ : Γ), Subgroup.mem_subgroupOf.1 hk₀, (u₀ : Γ), Subgroup.mem_subgroupOf.1 hu₀, ?_⟩
    exact congrArg Subtype.val hprod
  have hK_S : (K : Set Γ) * U = S := by
    ext s
    rw [Set.mem_mul]
    constructor
    · rintro ⟨k, hk, u, hu, rfl⟩
      exact S.mul_mem (hKS hk) (hUS hu)
    · intro hs
      obtain ⟨k, hk, u, hu, rfl⟩ := hKS_sub s hs
      exact ⟨k, hk, u, hu, rfl⟩
  have hU_K : (U : Set Γ) * K = S := by
    ext s
    rw [Set.mem_mul]
    constructor
    · rintro ⟨u, hu, k, hk, rfl⟩
      exact S.mul_mem (hUS hu) (hKS hk)
    · intro hs
      obtain ⟨k, hk, u, hu, hku⟩ := hKS_sub s⁻¹ (S.inv_mem hs)
      refine ⟨u⁻¹, U.inv_mem hu, k⁻¹, K.inv_mem hk, ?_⟩
      calc u⁻¹ * k⁻¹ = (k * u)⁻¹ := by group
        _ = s := by rw [hku, inv_inv]
  exact ⟨K, hKcard, by rw [hK_S, hU_K]⟩

end CFSG.AGLEmbeddingD2.Tits.OrdinaryProofs
