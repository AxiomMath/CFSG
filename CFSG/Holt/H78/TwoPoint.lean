module

public import CFSG.Holt.H78.JImages
public import CFSG.Holt.H78.Sec4Defs

public section

namespace CFSG.Holt.H78

open MulAction CFSG.Holt CFSG.Holt.General CFSG.Open
open scoped Pointwise

section Sylow

variable {G : Type*} [Group G]

private theorem fusionIsSylowIn_of_le_of_le {p : ℕ} {P K L : Subgroup G}
    (hP : fusionIsSylowIn p P K) (hPL : P ≤ L) (hLK : L ≤ K) : fusionIsSylowIn p P L :=
  ⟨hPL, hP.2.1, fun Q hQL hQ hPQ => hP.2.2 Q (hQL.trans hLK) hQ hPQ⟩

variable [Finite G]

private theorem fusionIsSylowIn_of_odd_relIndex {P K L : Subgroup G}
    (hP : fusionIsSylowIn 2 P K) (hKL : K ≤ L) (hodd : Odd (K.relIndex L)) :
    fusionIsSylowIn 2 P L := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine fusionIsSylowIn_of_card_eq (hP.1.trans hKL) hP.2.1 ?_
  rw [card_eq_of_fusionIsSylowIn hP]
  have h := Subgroup.relIndex_mul_card K L
  rw [inf_of_le_left hKL] at h
  rw [← h, Nat.factorization_mul hodd.pos.ne' Nat.card_pos.ne', Finsupp.add_apply,
    Nat.factorization_eq_zero_of_not_dvd hodd.not_two_dvd_nat, zero_add]

end Sylow

section TwoPointSylow

variable {G : Type*} [Group G] {Ω : Type*} [MulAction G Ω]

theorem fusionIsSylowIn_sup_zpowers_stabilizer_pair {α β : Ω} (hαβ : α ≠ β) {T : Subgroup G}
    (hT : fusionIsSylowIn 2 T (stabilizer G α ⊓ stabilizer G β)) {u : G}
    (hu : u ∈ longInvSwap G Ω α β) (huT : u ∈ Subgroup.centralizer (T : Set G)) :
    fusionIsSylowIn 2 (T ⊔ Subgroup.zpowers u) (stabilizer G ({α, β} : Set Ω)) := by
  have huX : u ∈ stabilizer G ({α, β} : Set Ω) :=
    closure_longInvSwap_le_stabilizer_pair α β (Subgroup.subset_closure hu)
  have hmem : ∀ q ∈ stabilizer G ({α, β} : Set Ω), ∀ ω ∈ ({α, β} : Set Ω),
      q • ω ∈ ({α, β} : Set Ω) := fun q hq ω hω => by
    rw [← mem_stabilizer_iff.mp hq]
    exact Set.smul_mem_smul_set hω
  refine ⟨sup_le (hT.1.trans (stabilizer_inf_le_stabilizer_pair α β))
    (Subgroup.zpowers_le.mpr huX), hT.2.1.to_sup_of_normal_left'
      (isPGroup_zpowers_of_orderOf_eq_two hu.1.1)
      (Subgroup.zpowers_le.mpr (Subgroup.centralizer_le_normalizer _ huT)),
    fun Q hQX hQ hPQ => le_antisymm (fun q hq => ?_) hPQ⟩
  have hQα : Q ⊓ stabilizer G α = T := by
    refine hT.2.2 _ (fun q hq => Subgroup.mem_inf.mpr ⟨(Subgroup.mem_inf.mp hq).2, ?_⟩)
      (hQ.to_le inf_le_left) (le_inf (le_sup_left.trans hPQ)
        (hT.1.trans inf_le_left))
    obtain ⟨hqQ, hqα⟩ := Subgroup.mem_inf.mp hq
    rw [mem_stabilizer_iff] at hqα ⊢
    rcases hmem q (hQX hqQ) β (Set.mem_insert_of_mem α rfl) with h | h
    · exact absurd (smul_left_cancel q (h.trans hqα.symm)) (Ne.symm hαβ)
    · exact h
  rcases hmem q (hQX hq) α (Set.mem_insert α _) with h | h
  · exact Subgroup.mem_sup_left (hQα ▸ Subgroup.mem_inf.mpr ⟨hq, h⟩ : q ∈ T)
  · have huq : u * q ∈ T := hQα ▸ Subgroup.mem_inf.mpr
      ⟨Q.mul_mem (hPQ (Subgroup.mem_sup_right (Subgroup.mem_zpowers u))) hq,
        by rw [mem_stabilizer_iff, mul_smul, h, smul_eq_of_mem_longInvSwap hu]⟩
    have hq' : q = u⁻¹ * (u * q) := by group
    rw [hq']
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_right (Subgroup.inv_mem _ (Subgroup.mem_zpowers u)))
      (Subgroup.mem_sup_left huq)

theorem fusionIsSylowIn_sup_zpowers_inf_stabilizer {α β γ : Ω} (hαβ : α ≠ β)
    {T : Subgroup G} (hT : fusionIsSylowIn 2 T (stabilizer G α ⊓ stabilizer G β)) {u : G}
    (hu : u ∈ longInvSwap G Ω α β) (huT : u ∈ Subgroup.centralizer (T : Set G))
    (hTγ : T ≤ stabilizer G γ) (huγ : u • γ = γ) :
    fusionIsSylowIn 2 (T ⊔ Subgroup.zpowers u)
      (stabilizer G ({α, β} : Set Ω) ⊓ stabilizer G γ) :=
  fusionIsSylowIn_of_le_of_le (fusionIsSylowIn_sup_zpowers_stabilizer_pair hαβ hT hu huT)
    (le_inf (fusionIsSylowIn_sup_zpowers_stabilizer_pair hαβ hT hu huT).1
      (sup_le hTγ (Subgroup.zpowers_le.mpr huγ))) inf_le_left

variable [Finite G]

theorem exists_mem_normalizer_smul_eq_of_mem_holtDelta {α β γ δ : Ω}
    (hγ : γ ∈ holtDelta G Ω α β) {T : Subgroup G}
    (hT : fusionIsSylowIn 2 T (stabilizer G α ⊓ stabilizer G β ⊓ stabilizer G γ))
    (hδ : δ ∈ holtDelta G Ω α β) (hδT : δ ∈ fixSet Ω T) :
    ∃ n ∈ Subgroup.normalizer (T : Set G), n ∈ stabilizer G α ⊓ stabilizer G β ∧ n • δ = γ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨⟨g, hg⟩, hgδ⟩ : γ ∈ orbit ↥(stabilizer G α ⊓ stabilizer G β) δ := by
    rw [← holtDelta_eq_orbit_of_mem hδ]
    exact hγ
  have hgδ' : g • δ = γ := hgδ
  have hgα : g • α = α := mem_stabilizer_iff.mp (Subgroup.mem_inf.mp hg).1
  have hgβ : g • β = β := mem_stabilizer_iff.mp (Subgroup.mem_inf.mp hg).2
  have hconj : ∀ {a : Ω} {t : G}, t • a = a → (g * t * g⁻¹) • (g • a) = g • a :=
    fun {a t} h => by rw [mul_smul, mul_smul, inv_smul_smul, h]
  set Q : Subgroup G := T.map (MulAut.conj g).toMonoidHom with hQ
  have hmemQ : ∀ x, x ∈ Q ↔ g⁻¹ * x * g ∈ T := fun x => by
    rw [hQ, Subgroup.mem_map_equiv, MulAut.conj_symm_apply]
  have hQT : fusionIsSylowIn 2 Q (stabilizer G α ⊓ stabilizer G β ⊓ stabilizer G γ) := by
    refine fusionIsSylowIn_of_card_eq (fun x hx => ?_) (hT.2.1.map _) ?_
    · have ht := hT.1 ((hmemQ x).mp hx)
      simp only [Subgroup.mem_inf, mem_stabilizer_iff] at ht ⊢
      have hx' : x = g * (g⁻¹ * x * g) * g⁻¹ := by group
      have h3 := hconj (hδT _ ((hmemQ x).mp hx))
      rw [← hx', hgδ'] at h3
      refine ⟨⟨?_, ?_⟩, h3⟩
      · have h1 := hconj ht.1.1
        rwa [← hx', hgα] at h1
      · have h2 := hconj ht.1.2
        rwa [← hx', hgβ] at h2
    · rw [hQ, Subgroup.card_map_of_injective (MulAut.conj g).injective,
        card_eq_of_fusionIsSylowIn hT]
  obtain ⟨k, hk, hkQ⟩ := exists_mem_conj_of_fusionIsSylowIn hT hQT
  have hk' := Subgroup.mem_inf.mp hk
  refine ⟨k⁻¹ * g, ?_, ?_, ?_⟩
  · rw [Subgroup.mem_normalizer_iff]
    intro t
    rw [show k⁻¹ * g * t * (k⁻¹ * g)⁻¹ = k⁻¹ * (g * t * g⁻¹) * k by group, ← hkQ, hmemQ,
      show g⁻¹ * (g * t * g⁻¹) * g = t by group]
  · exact Subgroup.mul_mem _ (Subgroup.inv_mem _ hk'.1) hg
  · rw [mul_smul, hgδ', inv_smul_eq_iff, mem_stabilizer_iff.mp hk'.2]

variable [Finite Ω]

theorem fusionIsSylowIn_inf_of_mem_holtDelta {α β γ : Ω} (hγ : γ ∈ holtDelta G Ω α β)
    {T : Subgroup G}
    (hT : fusionIsSylowIn 2 T (stabilizer G α ⊓ stabilizer G β ⊓ stabilizer G γ)) :
    fusionIsSylowIn 2 T (stabilizer G α ⊓ stabilizer G β) := by
  refine fusionIsSylowIn_of_odd_relIndex hT inf_le_left ?_
  rw [Subgroup.inf_relIndex_left, ← card_orbit_eq_relIndex, ← holtDelta_eq_orbit_of_mem hγ]
  exact odd_card_holtDelta (holtDelta_nonempty_iff.mp ⟨γ, hγ⟩)

end TwoPointSylow

section Lemma32i

variable {G : Type*} [Group G] [Finite G] {Ω : Type} [MulAction G Ω] [Finite Ω]

theorem exists_mem_longInvSwap_centralizer (hG : IsStarGroup G Ω)
    (hB : HoltTheorem1Below (Nat.card G) (Nat.card Ω)) {T : Subgroup G} (hT : IsPGroup 2 T)
    (h3 : 3 ≤ Nat.card (fixSet Ω T)) {α β : Ω} (hα : α ∈ fixSet Ω T) (hβ : β ∈ fixSet Ω T) :
    ∃ u ∈ longInvSwap G Ω α β, u ∈ Subgroup.centralizer (T : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_cases hT1 : T = ⊥
  · obtain ⟨u, hu⟩ := longInvSwap_nonempty hG α β
    refine ⟨u, hu, ?_⟩
    rw [hT1, Subgroup.mem_centralizer_iff]
    intro h hh
    rw [SetLike.mem_coe, Subgroup.mem_bot] at hh
    rw [hh, one_mul, mul_one]
  have hY := isStarGroup_inducedPerm_fixSet hG hT h3 le_rfl
    (Subgroup.centralizer_le_normalizer _)
  obtain ⟨y, hy⟩ := longInvSwap_nonempty hY ⟨α, hα⟩ ⟨β, hβ⟩
  have hBY := hB.induced_fixSet hT hT1 le_rfl (Subgroup.centralizer_le_normalizer _)
    (Nat.card (fixSet Ω T) + 1)
  obtain ⟨x, hxJ, hxC, hxy⟩ := (mem_longInv_inducedPerm_fixSet_iff hG hT h3 le_rfl
    (Subgroup.centralizer_le_normalizer _) hBY y).mp hy.1
  refine ⟨x, ⟨hxJ, ?_⟩, hxC⟩
  calc (x : G) • α = ((inducedHom _ (fixSet Ω T) _ x ⟨α, hα⟩ : fixSet Ω T) : Ω) := rfl
    _ = ((y : Equiv.Perm (fixSet Ω T)) ⟨α, hα⟩ : Ω) := by rw [hxy]
    _ = β := congrArg Subtype.val hy.2

theorem lemma_3_2_i (hG : IsStarGroup G Ω) (hB : HoltTheorem1Below (Nat.card G) (Nat.card Ω))
    {α β γ : Ω} (hαβ : α ≠ β) (hγ : γ ∈ holtDelta G Ω α β) {T : Subgroup G}
    (hT : fusionIsSylowIn 2 T (stabilizer G α ⊓ stabilizer G β ⊓ stabilizer G γ)) :
    fusionIsSylowIn 2 T (stabilizer G α ⊓ stabilizer G β) ∧
      ∃ u ∈ longInvSwap G Ω α β, u • γ = γ ∧ u ∈ Subgroup.centralizer (T : Set G) := by
  refine ⟨fusionIsSylowIn_inf_of_mem_holtDelta hγ hT, ?_⟩
  have hTα : α ∈ fixSet Ω T :=
    mem_fixSet_iff_le_stabilizer.mpr (hT.1.trans (inf_le_left.trans inf_le_left))
  have hTβ : β ∈ fixSet Ω T :=
    mem_fixSet_iff_le_stabilizer.mpr (hT.1.trans (inf_le_left.trans inf_le_right))
  have hTγ : γ ∈ fixSet Ω T := mem_fixSet_iff_le_stabilizer.mpr (hT.1.trans inf_le_right)
  have h3 : 3 ≤ Nat.card (fixSet Ω T) := by
    have hγα : α ≠ γ := fun h => left_notMem_holtDelta hαβ (by rwa [← h] at hγ)
    have hγβ : β ≠ γ := fun h => right_notMem_holtDelta hαβ (by rwa [← h] at hγ)
    have hsub : ({α, β, γ} : Set Ω) ⊆ fixSet Ω T := by
      rintro ω (rfl | rfl | rfl)
      exacts [hTα, hTβ, hTγ]
    calc 3 = Nat.card ({α, β, γ} : Set Ω) := by
          rw [Nat.card_coe_set_eq, Set.ncard_eq_three.mpr ⟨α, β, γ, hαβ, hγα, hγβ, rfl⟩]
      _ ≤ Nat.card (fixSet Ω T) := Nat.card_mono (Set.toFinite _) hsub
  obtain ⟨u, hu, huT⟩ := exists_mem_longInvSwap_centralizer hG hB hT.2.1 h3 hTα hTβ
  obtain ⟨δ, hδ⟩ := exists_mem_longInvAt hu.1
  have hδT : δ ∈ fixSet Ω T := fun t ht => by
    have hc : t * u = u * t := Subgroup.mem_centralizer_iff.mp huT t ht
    refine (smul_eq_iff_of_mem_longInvAt hδ (t • δ)).mp ?_
    rw [← mul_smul, ← hc, mul_smul, hδ.2]
  obtain ⟨n, hnN, hn, hnδ⟩ :=
    exists_mem_normalizer_smul_eq_of_mem_holtDelta hγ hT ⟨u, hu, hδ.2⟩ hδT
  have hn' := Subgroup.mem_inf.mp hn
  refine ⟨n * u * n⁻¹, ?_, ?_, ?_⟩
  · have h := conj_mem_longInvSwap hu n
    rwa [mem_stabilizer_iff.mp hn'.1, mem_stabilizer_iff.mp hn'.2] at h
  · rw [mul_smul, mul_smul, ← hnδ, inv_smul_smul, hδ.2]
  · rw [Subgroup.mem_centralizer_iff]
    intro t ht
    have ht' : n⁻¹ * t * n ∈ T := by
      have h := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hnN) t).mp ht
      rwa [inv_inv] at h
    have hc : n⁻¹ * t * n * u = u * (n⁻¹ * t * n) := Subgroup.mem_centralizer_iff.mp huT _ ht'
    calc t * (n * u * n⁻¹) = n * (n⁻¹ * t * n * u) * n⁻¹ := by group
      _ = n * (u * (n⁻¹ * t * n)) * n⁻¹ := by rw [hc]
      _ = n * u * n⁻¹ * t := by group

end Lemma32i

section Lemma32ii

variable {G : Type*} [Group G] [Finite G] {Ω : Type} [MulAction G Ω] [Finite Ω]

theorem isStarGroup_inducedPerm_holtDelta (hG : IsStarGroup G Ω)
    (hB : HoltTheorem1Below (Nat.card G) (Nat.card Ω)) {α β : Ω} (hαβ : α ≠ β)
    (h3 : 3 ≤ Nat.card (holtDelta G Ω α β)) :
    IsStarGroup ↥(inducedPerm (stabilizer G ({α, β} : Set Ω)) (holtDelta G Ω α β)
      (stabilizer_pair_le α β)) ↥(holtDelta G Ω α β) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine ⟨hG.odd_card_holtDelta α β, h3, fun γ R hR hRγ _ => ?_⟩
  obtain ⟨R', hR'X, hR', hlift, hlift'⟩ := exists_isPGroup_lift_inducedPerm hR
  have hR'γ : R' ≤ stabilizer G (γ : Ω) := fun r hr => by
    obtain ⟨y, hy, hyr⟩ := hlift r hr
    rw [mem_stabilizer_iff, ← hyr γ]
    exact congrArg Subtype.val (mem_stabilizer_iff.mp (hRγ hy))
  obtain ⟨T, -, hT⟩ := exists_fusionIsSylowIn_ge (IsPGroup.of_bot (p := 2))
    (bot_le : ⊥ ≤ stabilizer G α ⊓ stabilizer G β ⊓ stabilizer G (γ : Ω))
  obtain ⟨hTαβ, u, hu, huγ, huT⟩ := lemma_3_2_i hG hB hαβ γ.2 hT
  have hP' := fusionIsSylowIn_sup_zpowers_inf_stabilizer hαβ hTαβ hu huT
    (hT.1.trans inf_le_right) huγ
  obtain ⟨P, hR'P, hP⟩ := exists_fusionIsSylowIn_ge hR' (le_inf hR'X hR'γ)
  obtain ⟨k, hk, hkP⟩ := exists_mem_conj_of_fusionIsSylowIn hP' hP
  have hk' := Subgroup.mem_inf.mp hk
  have huC : T ⊔ Subgroup.zpowers u ≤ Subgroup.centralizer ({u} : Set G) :=
    sup_le (fun t ht => Subgroup.mem_centralizer_singleton_iff.mpr
      (Subgroup.mem_centralizer_iff.mp huT t ht))
      (Subgroup.zpowers_le.mpr (Subgroup.mem_centralizer_singleton_iff.mpr rfl))
  have hu'X : k * u * k⁻¹ ∈ stabilizer G ({α, β} : Set Ω) :=
    Subgroup.mul_mem _ (Subgroup.mul_mem _ hk'.1
      (closure_longInvSwap_le_stabilizer_pair α β (Subgroup.subset_closure hu)))
      (Subgroup.inv_mem _ hk'.1)
  have hu'γ : k * u * k⁻¹ ∈ longInvAt G Ω (γ : Ω) := by
    have h := conj_mem_longInvAt ⟨hu.1, huγ⟩ k
    rwa [mem_stabilizer_iff.mp hk'.2] at h
  have hcomm : ∀ r ∈ R', r * (k * u * k⁻¹) = k * u * k⁻¹ * r := fun r hr => by
    have h := Subgroup.mem_centralizer_singleton_iff.mp (huC ((hkP r).mp (hR'P hr)))
    calc r * (k * u * k⁻¹) = k * (k⁻¹ * r * k * u) * k⁻¹ := by group
      _ = k * (u * (k⁻¹ * r * k)) * k⁻¹ := by rw [h]
      _ = k * u * k⁻¹ * r := by group
  have : Nontrivial (holtDelta G Ω α β) := Finite.one_lt_card_iff_nontrivial.mp (by omega)
  refine ⟨⟨inducedHom _ (holtDelta G Ω α β) (stabilizer_pair_le α β) ⟨_, hu'X⟩, ⟨_, hu'X⟩, rfl⟩,
    mem_longInvAt_subgroup_iff.mpr (inducedHom_mem_longInvAt _ (x := ⟨_, hu'X⟩) hu'γ
      (exists_ne γ)), Subgroup.mem_centralizer_iff.mpr fun y hy => ?_⟩
  obtain ⟨r, hr, hry⟩ := hlift' y hy
  refine Subtype.ext (Equiv.ext fun δ => Subtype.ext ?_)
  simp only [Subgroup.coe_mul, Equiv.Perm.coe_mul, Function.comp_apply, hry,
    coe_inducedHom_apply]
  rw [← mul_smul, ← mul_smul, hcomm r hr]

theorem isStarGroup_twoPointSection (hG : IsStarGroup G Ω)
    (hB : HoltTheorem1Below (Nat.card G) (Nat.card Ω)) {α β : Ω} (hαβ : α ≠ β)
    (h3 : 3 ≤ Nat.card (holtDelta G Ω α β)) :
    IsStarGroup ↥(twoPointSection G Ω α β) ↥(holtDelta G Ω α β) :=
  isStarGroup_inducedPerm_holtDelta hG hB hαβ h3

end Lemma32ii

end CFSG.Holt.H78
