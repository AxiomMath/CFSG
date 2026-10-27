module

public import CFSG.GH74.Filter.Lie.TwistedF4
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I107X2Twist

public section

namespace CFSG.LocalAnalysis.GLTheoremA.I107X2

open CFSG.GH74.Filter CFSG.GH74.Filter.Lie CFSG.LieType.Ree CFSG.LieType.Chevalley CFSG.Blueprint
  CFSG.Blueprint.Chevalley
  CFSG.SectionRank CFSG.Open CFSG.LieType.BorelTits


theorem isElemAbelian_two_of_comm_sq {G : Type*} [Group G] (S : Subgroup G)
    (hc : ∀ x ∈ S, ∀ y ∈ S, x * y = y * x) (hs : ∀ x ∈ S, x * x = 1) : IsElemAbelian 2 S :=
  ⟨⟨⟨fun a b => Subtype.ext (hc a a.2 b b.2)⟩⟩, fun x hx => by
    rw [sq]
    exact hs x hx⟩

theorem twF4_pRank_ge {K : Type} [Field K] [Finite K] [CharP K 2] {a : ℕ} (ha : 1 ≤ a)
    (hK : Nat.card K = 2 ^ (2 * a + 1)) :
    2 * (2 * a + 1) ≤ CFSG.Open.pRank 2 (⊤ : Subgroup (commutator (reeFixed ReeTag.F4 K a))) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : CharP K ReeTag.F4.prime := inferInstanceAs (CharP K 2)
  have hKp : Nat.card K = ReeTag.F4.prime ^ (2 * a + 1) := hK
  let F : adjointGroup ReeTag.F4.tag K ≃* adjointGroup ReeTag.F4.tag K := ReeTag.F4.reeAut K a
  have hFF : ∀ g, F (F g) = g := ReeTag.F4.reeAut_reeAut a hK
  let f : Fin 4 → Multiplicative K →* adjointGroup ReeTag.F4.tag K := fun i =>
    rootHom (K := K) (quadF4.root i)
  obtain ⟨hcomm, hinj⟩ := SepWitness.pi_data quadF4_check (K := K)
  have hstab : ∀ i y, F (f i y) ∈ (MonoidHom.noncommPiCoprod f hcomm).range := by
    intro i y
    have h1 : f i y ∈ (rootOperatorFamily ReeTag.F4.tag).rootSubgroup K (quadF4.root i) :=
      (rootOperatorFamily _).eltElement_mem_rootSubgroup _ _
    have h2 := ReeTag.reeAut_mem_X (t := ReeTag.F4) a h1
    rw [dualRootOf_quadF4] at h2
    obtain ⟨c, hc⟩ := ((rootOperatorFamily ReeTag.F4.tag).mem_rootSubgroup).1 h2
    refine ⟨Pi.mulSingle (![1, 0, 3, 2] i) (Multiplicative.ofAdd c), ?_⟩
    rw [MonoidHom.noncommPiCoprod_mulSingle]
    exact hc
  set Rg := (MonoidHom.noncommPiCoprod f hcomm).range with hRg
  have hRc : ∀ x ∈ Rg, ∀ y ∈ Rg, x * y = y * x := by
    rintro _ ⟨a', rfl⟩ _ ⟨b, rfl⟩
    rw [← map_mul, ← map_mul, mul_comm a' b]
  have hRs : ∀ x ∈ Rg, x * x = 1 := by
    rintro _ ⟨a', rfl⟩
    rw [← map_mul]
    convert map_one (MonoidHom.noncommPiCoprod f hcomm)
    funext i
    apply Multiplicative.toAdd.injective
    simp only [Pi.mul_apply, toAdd_mul, toAdd_one, Pi.one_apply]
    exact CharTwo.add_self_eq_zero _
  have hFR : ∀ x ∈ Rg, F x ∈ Rg := map_range_noncommPiCoprod_le f hcomm F hstab
  obtain ⟨E, hER, hEF, hRE⟩ := exists_fixed_subgroup_card_sq F hFF Rg hRc hRs hFR
  have hRcard : Nat.card Rg = 2 ^ (4 * (2 * a + 1)) := by
    rw [← Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv, Nat.card_fun,
      Nat.card_congr Multiplicative.toAdd, hK, ← pow_mul, Nat.card_eq_fintype_card,
      Fintype.card_fin]
    congr 1
    ring
  have hEge : 2 ^ (2 * (2 * a + 1)) ≤ Nat.card E := by
    have h1 : (2 ^ (2 * (2 * a + 1))) ^ 2 ≤ (Nat.card E) ^ 2 := by
      have e2 : (2 ^ (2 * (2 * a + 1))) ^ 2 = Nat.card Rg := by
        rw [hRcard, ← pow_mul]
        congr 1
        ring
      rw [e2]
      exact hRE
    exact (Nat.pow_le_pow_iff_left two_ne_zero).1 h1
  have hEdvd : Nat.card E ∣ 2 ^ (4 * (2 * a + 1)) := by
    rw [← hRcard]
    exact Subgroup.card_dvd_of_le hER
  have hRU : Rg ≤ (nativeData ReeTag.F4.tag K).U := by
    rintro _ ⟨a', rfl⟩
    have e : (MonoidHom.noncommPiCoprod f hcomm) a' =
        Finset.univ.noncommProd (fun i => f i (a' i)) (fun _ _ _ _ h => hcomm h _ _) := rfl
    rw [e]
    refine Subgroup.noncommProd_mem _ (fun _ _ _ _ h => hcomm h _ _) (fun i _ => ?_)
    exact RootGroupData.X_le_U (D := nativeData ReeTag.F4.tag K)
      (SepWitness.root_pos quadF4_check i)
      ((rootOperatorFamily _).eltElement_mem_rootSubgroup _ _)
  have hEΓ : E ≤ reeFixed ReeTag.F4 K a := fun x hx => (mem_reeFixed _ _ _).2 (hEF x hx)
  have hEDer : ∀ x ∈ E, x ∈ reeDerived ReeTag.F4 K a := fun x hx =>
    reeFixed_U_le_derived ReeTag.F4 K a ha hKp x (hRU (hER hx)) (hEΓ hx)
  let Γ := reeFixed ReeTag.F4 K a
  let E' : Subgroup Γ := E.subgroupOf Γ
  have hE'der : E' ≤ commutator Γ := by
    intro y hy
    have hy' : (y : adjointGroup ReeTag.F4.tag K) ∈ E := (Subgroup.mem_subgroupOf).1 hy
    obtain ⟨z, hz, hzy⟩ := Subgroup.mem_map.1 (hEDer _ hy')
    have : z = y := Subtype.ext hzy
    rw [← this]
    exact hz
  let E'' : Subgroup (commutator Γ) := E'.subgroupOf (commutator Γ)
  have hcardE'' : Nat.card E'' = Nat.card E := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hE'der).toEquiv,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hEΓ).toEquiv]
  have hcommE'' : ∀ x ∈ E'', ∀ y ∈ E'', x * y = y * x := by
    intro x hx y hy
    have hx'' : (x : adjointGroup ReeTag.F4.tag K) ∈ E := (Subgroup.mem_subgroupOf).1
      ((Subgroup.mem_subgroupOf).1 hx)
    have hy'' : (y : adjointGroup ReeTag.F4.tag K) ∈ E := (Subgroup.mem_subgroupOf).1
      ((Subgroup.mem_subgroupOf).1 hy)
    exact Subtype.ext (Subtype.ext (hRc _ (hER hx'') _ (hER hy'')))
  have hsqE'' : ∀ x ∈ E'', x * x = 1 := by
    intro x hx
    have hx'' : (x : adjointGroup ReeTag.F4.tag K) ∈ E := (Subgroup.mem_subgroupOf).1
      ((Subgroup.mem_subgroupOf).1 hx)
    exact Subtype.ext (Subtype.ext (hRs _ (hER hx'')))
  have hdvd'' : Nat.card E'' ∣ 2 ^ (4 * (2 * a + 1)) := by
    rw [hcardE'']
    exact hEdvd
  have hle'' : 2 ^ (2 * (2 * a + 1)) ≤ Nat.card E'' := by
    rw [hcardE'']
    exact hEge
  obtain ⟨B, hB⟩ := exists_subgroup_card_two_pow (G := E'') hdvd'' hle''
  let B' : Subgroup (commutator Γ) := B.map E''.subtype
  have hB'card : Nat.card B' = 2 ^ (2 * (2 * a + 1)) := by
    rw [Subgroup.card_map_of_injective E''.subtype_injective]
    exact hB
  have hB'le : B' ≤ E'' := Subgroup.map_subtype_le B
  have hB'ab : IsElemAbelian 2 B' :=
    isElemAbelian_two_of_comm_sq B' (fun x hx y hy => hcommE'' x (hB'le hx) y (hB'le hy))
      (fun x hx => hsqE'' x (hB'le hx))
  exact CFSG.SectionRank.le_pRank (p := 2) (by norm_num) le_top hB'ab hB'card

end CFSG.LocalAnalysis.GLTheoremA.I107X2

end
