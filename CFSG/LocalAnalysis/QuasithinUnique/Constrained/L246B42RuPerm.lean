module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.L246B42RuCheck
public import CFSG.Sporadic.Schreier.RuInvClasses

public section

namespace CFSG.QuasithinUnique.Bridge.RuExcl

open CFSG.QuasithinUnique.Setup.X1 CFSG.Sporadic.RuSchreier
open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native

theorem ru_rank_P
    : ∀ B : Subgroup ↥ruP, (∀ x ∈ B, ∀ y ∈ B, x * y = y * x) →
    (∀ x ∈ B, x * x = 1) → Nat.card B ≤ 2 ^ 9 := by
  classical
  intro B _ hsq
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hpg : IsPGroup 2 B := by
    intro x
    refine ⟨1, ?_⟩
    have := hsq x x.2
    apply Subtype.ext
    simpa [sq] using this
  obtain ⟨Q, hQ⟩ := hpg.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq ruP Q ruSylow
  have hconj : ∀ x : B, ((g * (x : ↥ruP) * g⁻¹ : ↥ruP) : Equiv.Perm (Fin 4060)) ∈ ruS := by
    intro x
    have hmem : MulAut.conj g • (x : ↥ruP) ∈ (ruSylow : Subgroup ruP) := by
      rw [← hg, Sylow.coe_subgroup_smul]
      exact Subgroup.smul_mem_pointwise_smul _ _ _ (hQ x.2)
    rw [ruSylow_coe, Subgroup.mem_subgroupOf, MulAut.smul_def, MulAut.conj_apply] at hmem
    exact hmem
  have : Fintype B := Fintype.ofFinite B
  set f : B → Equiv.Perm (Fin 4060) := fun x => ((g * (x : ↥ruP) * g⁻¹ : ↥ruP) :
    Equiv.Perm (Fin 4060)) with hf
  have hinj : Function.Injective f := by
    intro x y hxy
    have h1 : g * (x : ↥ruP) * g⁻¹ = g * (y : ↥ruP) * g⁻¹ := Subtype.ext hxy
    exact Subtype.ext (mul_left_cancel (mul_right_cancel h1))
  set S : Finset (Equiv.Perm (Fin 4060)) := ((Finset.univ : Finset B).erase 1).image f with hS
  have hScard : S.card = Fintype.card B - 1 := by
    rw [hS, Finset.card_image_of_injective _ hinj, Finset.card_erase_of_mem (Finset.mem_univ _),
      Finset.card_univ]
  have hsub : (S : Set (Equiv.Perm (Fin 4060))) ⊆ ruInvS := by
    intro t ht
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.1 (Finset.mem_coe.1 ht)
    have hx1 : x ≠ 1 := Finset.ne_of_mem_erase hx
    refine ⟨hconj x, ?_⟩
    have hsq' : f x * f x = 1 := by
      have h1 : (g * (x : ↥ruP) * g⁻¹) * (g * (x : ↥ruP) * g⁻¹) = 1 := by
        have := congrArg Subtype.val (hsq (x : ↥ruP) x.2)
        calc (g * (x : ↥ruP) * g⁻¹) * (g * (x : ↥ruP) * g⁻¹)
            = g * ((x : ↥ruP) * (x : ↥ruP)) * g⁻¹ := by group
          _ = 1 := by rw [hsq (x : ↥ruP) x.2]; group
      exact congrArg Subtype.val h1
    have hne : f x ≠ 1 := fun h => hx1 (Subtype.ext (by
      have h2 : g * (x : ↥ruP) * g⁻¹ = 1 := Subtype.ext h
      have h3 : (x : ↥ruP) = 1 := by
        calc (x : ↥ruP) = g⁻¹ * (g * (x : ↥ruP) * g⁻¹) * g := by group
          _ = 1 := by rw [h2]; group
      exact h3))
    exact orderOf_eq_prime (by rw [sq]; exact hsq') hne
  have hfin : ruInvS.Finite := Set.finite_of_ncard_ne_zero (by rw [ncard_ruInvS]; norm_num)
  have hle : S.card ≤ 687 := by
    have h := Set.ncard_le_ncard hsub hfin
    rwa [Set.ncard_coe_finset, ncard_ruInvS] at h
  have hcardB : Nat.card B ≤ 688 := by
    rw [Nat.card_eq_fintype_card]
    omega
  obtain ⟨n, hn⟩ := (IsPGroup.iff_card (p := 2)).1 hpg
  rw [hn] at hcardB ⊢
  have hn9 : n ≤ 9 := by
    by_contra hlt
    push Not at hlt
    have : 2 ^ 10 ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hlt
    omega
  exact Nat.pow_le_pow_right (by norm_num) hn9

theorem ruA0P_fst : ruA0P.1 = ruA0A := by simp [ruA0P]

theorem ruA0P_snd : ruA0P.2 = ruInv ruA0A := by simp [ruA0P]

theorem ruA1P_fst : ruA1P.1 = ruA1A := by simp [ruA1P]

theorem ruA1P_snd : ruA1P.2 = ruInv ruA1A := by simp [ruA1P]

theorem ruZtP_eq : ruZtP = (compA 4060 ruA1A ruA1A, compA 4060 ruA1A ruA1A) := by
  simp [ruZtP, ruZtArr]

theorem pRep_ruA0P : PRep 4060 ruA0P ruA0 := by
  refine ⟨?_, ?_⟩
  · rw [ruA0P_fst]
    exact rep_ruA0
  · rw [ruA0P_snd]
    exact rep_ruInv rep_ruA0 ruBasic_check.1

theorem pRep_ruA1P : PRep 4060 ruA1P ruA1 := by
  refine ⟨?_, ?_⟩
  · rw [ruA1P_fst]
    exact rep_ruA1
  · rw [ruA1P_snd]
    exact rep_ruInv rep_ruA1 ruBasic_check.2.1

theorem pRep_ruZtP
    : PRep 4060 ruZtP (ruA1 * ruA1) := by
  have h4 : ruA1 ^ 4 = 1 := ruSeed_relations.2.2.1
  have hsq : ruA1 * ruA1 * (ruA1 * ruA1) = 1 := by
    have h : ruA1 ^ 4 = ruA1 * ruA1 * (ruA1 * ruA1) := by
      rw [show (4 : ℕ) = 2 + 2 from rfl, pow_add, sq]
    rw [← h]
    exact h4
  rw [ruZtP_eq]
  exact PRep.of_sq (rep_compA rep_ruA1 rep_ruA1) hsq

theorem regIn_ruP : RegIn 4060 ruP [ruA0P, ruA1P] := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact ⟨ruA0, Subgroup.subset_closure (by simp), pRep_ruA0P⟩
  · exact ⟨ruA1, Subgroup.subset_closure (by simp), pRep_ruA1P⟩

theorem gen3_of_check
    {t : PArr} {τ : Equiv.Perm (Fin 4060)} (ht : PRep 4060 t τ)
    {ws : List (List ℤ)} {prog : List (ℤ × ℤ)} (hws : ws.length = 3)
    (hc : threeConjCheck 4060 [ruA0P, ruA1P] t ws prog [ruA0A, ruA1A] = true) :
    ∃ gs : List (Equiv.Perm (Fin 4060)), gs.length = 3 ∧ (∀ g ∈ gs, g ∈ ruP) ∧
      ruP ≤ Subgroup.closure (conjSet gs {τ}) := by
  obtain ⟨gs, hlen, hgs, hmem⟩ := threeConj_sound regIn_ruP ht hc
  refine ⟨gs, hlen.trans hws, hgs, ?_⟩
  have h0 := hmem ruA0A (by simp) _ rep_ruA0
  have h1 := hmem ruA1A (by simp) _ rep_ruA1
  rw [ruP]
  refine (Subgroup.closure_le _).2 ?_
  rintro y (rfl | rfl)
  · exact h0
  · exact h1

theorem gen3_transfer {t x c : Equiv.Perm (Fin 4060)} (hc : c ∈ ruP) (hx : x = c * t * c⁻¹)
    (h : ∃ gs : List (Equiv.Perm (Fin 4060)), gs.length = 3 ∧ (∀ g ∈ gs, g ∈ ruP) ∧
      ruP ≤ Subgroup.closure (conjSet gs {t})) :
    ∃ gs : List (Equiv.Perm (Fin 4060)), gs.length = 3 ∧ (∀ g ∈ gs, g ∈ ruP) ∧
      ruP ≤ Subgroup.closure (conjSet gs {x}) := by
  obtain ⟨gs, hlen, hgs, hle⟩ := h
  refine ⟨gs.map (· * c⁻¹), by simp [hlen], ?_, fun a ha => ?_⟩
  · intro g hg
    obtain ⟨g', hg', rfl⟩ := List.mem_map.1 hg
    exact ruP.mul_mem (hgs g' hg') (ruP.inv_mem hc)
  · refine closure_conjSet_transfer (T := {x}) (T' := {t}) c⁻¹ (fun t' ht' => ⟨x, rfl, ?_⟩) gs
      (hle ha)
    have : t' = t := by simpa using ht'
    rw [this, hx]
    group

theorem ru_gen_perm
    {x : Equiv.Perm (Fin 4060)} (hxP : x ∈ ruP) (hx2 : x ^ 2 = 1)
    (hx1 : x ≠ 1) :
    ∃ gs : List (Equiv.Perm (Fin 4060)), gs.length = 3 ∧ (∀ g ∈ gs, g ∈ ruP) ∧
      ruP ≤ Subgroup.closure (conjSet gs {x}) := by
  have hord : orderOf x = 2 := orderOf_eq_prime hx2 hx1
  have hx : x ∈ {t | t ∈ ruP ∧ orderOf t = 2} := ⟨hxP, hord⟩
  rw [ruInvolutions_eq] at hx
  have cA := gen3_of_check pRep_ruA0P (by decide) ru_conjA_check
  have cZ := gen3_of_check pRep_ruZtP (by decide) ru_conjZ_check
  rcases hx with ⟨g, hg, hxg⟩ | ⟨g, hg, hxg⟩
  · obtain ⟨h, hh, hhz⟩ := ruA1_sq_mem
    have hhz' : ruA1 * ruA1 = h * ruZ * h⁻¹ := by rw [← pow_two]; exact hhz.symm
    refine gen3_transfer (c := g * h⁻¹) (ruP.mul_mem hg (ruP.inv_mem hh)) ?_ cZ
    rw [← hxg, hhz']
    group
  · exact gen3_transfer hg hxg.symm cA

end CFSG.QuasithinUnique.Bridge.RuExcl
