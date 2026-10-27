module

public import CFSG.Goldschmidt75.B1Comp2
public import CFSG.Goldschmidt75.Sec42

public section

namespace CFSG.Goldschmidt75

open CFSG.Open CFSG.Goldschmidt CFSG.Walter Subgroup

variable {G : Type} [Group G]

theorem omega1_le_self (S : Subgroup G) : Omega1 S ≤ S :=
  (closure_le _).mpr fun _ ht => ht.1

structure A2Comp (T : Sylow 2 G) (S₁ S₂ K : Subgroup G) : Prop where
  le₁ : S₁ ≤ T
  le₂ : S₂ ≤ T
  sc₁ : fusionStronglyClosed (S₁ : Set G) T
  sc₂ : fusionStronglyClosed (S₂ : Set G) T
  comm : ⁅S₁, S₂⁆ = ⊥
  normal : K.Normal
  quasi : CFSG.Open.IsQuasisimple K
  center_eq : Subgroup.center K = ⊥
  type : IsGoldTypeI K ∨ IsGoldTypeII K
  omega : ∀ t ∈ (T : Subgroup G) ⊓ K, t ^ 2 = 1 → t ∈ S₁ ⊓ S₂

namespace A2Comp

variable {T : Sylow 2 G} {S₁ S₂ K : Subgroup G}

theorem symm (h : A2Comp T S₁ S₂ K) : A2Comp T S₂ S₁ K where
  le₁ := h.le₂
  le₂ := h.le₁
  sc₁ := h.sc₂
  sc₂ := h.sc₁
  comm := by rw [commutator_comm]; exact h.comm
  normal := h.normal
  quasi := h.quasi
  center_eq := h.center_eq
  type := h.type
  omega := fun t ht h2 => by rw [inf_comm]; exact h.omega t ht h2

theorem isSimpleGroup (h : A2Comp T S₁ S₂ K) : IsSimpleGroup K := by
  have : IsSimpleGroup (K ⧸ Subgroup.center K) := h.quasi.2
  let e : K ≃* K ⧸ Subgroup.center K := (QuotientGroup.quotientBot (G := K)).symm.trans
    (QuotientGroup.quotientMulEquivOfEq h.center_eq.symm)
  exact e.isSimpleGroup

theorem sylowIn [Finite G] (h : A2Comp T S₁ S₂ K) :
    CFSG.Open.fusionIsSylowIn 2 ((T : Subgroup G) ⊓ K) K := by
  have : K.Normal := h.normal
  have hTG : fusionIsSylowIn 2 (T : Subgroup G) ⊤ :=
    ⟨le_top, T.isPGroup', fun _ _ hP hTP => T.is_maximal' hP hTP⟩
  exact G3a.fusionIsSylowIn_inf hTG le_top
    (Subgroup.normal_subgroupOf (N := K) (H := ⊤)).isSubnormal

theorem le_centralizer₁ (h : A2Comp T S₁ S₂ K) :
    S₁ ≤ centralizer ((S₁ ⊓ S₂ : Subgroup G) : Set G) :=
  (commutator_eq_bot_iff_le_centralizer.mp h.comm).trans (centralizer_le inf_le_right)

theorem omega1_le (h : A2Comp T S₁ S₂ K) : Omega1 ((T : Subgroup G) ⊓ K) ≤ S₁ ⊓ S₂ :=
  (closure_le _).mpr fun t ht => h.omega t ht.1 ht.2

theorem isMulCommutative_omega1 (h : A2Comp T S₁ S₂ K) :
    IsMulCommutative (Omega1 ((T : Subgroup G) ⊓ K)) := by
  refine ⟨⟨fun a b => Subtype.ext ?_⟩⟩
  have hb := h.omega1_le b.2
  have ha := h.omega1_le a.2
  exact (mem_centralizer_iff.mp (h.le_centralizer₁ (mem_inf.mp ha).1) _ hb).symm

theorem omega1_ne_bot [Finite G] (h : A2Comp T S₁ S₂ K) :
    Omega1 ((T : Subgroup G) ⊓ K) ≠ ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : IsSimpleGroup K := h.isSimpleGroup
  have hK : Group.IsPerfect K := ⟨h.quasi.1⟩
  have heven : 2 ∣ Nat.card K := by
    by_contra hodd
    have hsol : Group.IsSolvable K :=
      CFSG.FeitThompson.isSolvable_of_odd_natCard _ (Nat.odd_iff.mpr (Nat.two_dvd_ne_zero.mp hodd))
    exact Group.IsPerfect.not_isSolvable K hsol
  obtain ⟨t, ht⟩ := exists_prime_orderOf_dvd_card' (G := K) 2 heven
  have hR : (T : Subgroup G) ⊓ K ≠ ⊥ := by
    intro hR
    have hp : IsPGroup 2 (zpowers (t : G)) := IsPGroup.of_card (n := 1)
      (by rw [Nat.card_zpowers, Subgroup.orderOf_coe, ht, pow_one])
    have hle : (T : Subgroup G) ⊓ K ≤ zpowers (t : G) := by rw [hR]; exact bot_le
    have h1 := h.sylowIn.2.2 (zpowers (t : G)) (zpowers_le.mpr t.2) hp hle
    have h2 : (t : G) ∈ (⊥ : Subgroup G) := by rw [← hR, ← h1]; exact mem_zpowers _
    rw [mem_bot] at h2
    have h3 : orderOf (t : G) = 1 := by rw [h2, orderOf_one]
    rw [Subgroup.orderOf_coe, ht] at h3
    exact absurd h3 (by norm_num)
  have hRp : IsPGroup 2 ((T : Subgroup G) ⊓ K : Subgroup G) := T.isPGroup'.to_le inf_le_left
  rcases hRp.card_eq_or_dvd with h1 | h2
  · exact absurd ((Subgroup.card_eq_one).mp h1) hR
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' 2 h2
  intro hbot
  have hx2 : (x : G) ^ 2 = 1 := by
    rw [← Subgroup.orderOf_coe] at hx
    have := pow_orderOf_eq_one (x : G)
    rwa [hx] at this
  have hxΩ : (x : G) ∈ Omega1 ((T : Subgroup G) ⊓ K) := subset_closure ⟨x.2, hx2⟩
  rw [hbot, mem_bot] at hxΩ
  have h3 : orderOf (x : G) = 1 := by rw [hxΩ, orderOf_one]
  rw [Subgroup.orderOf_coe, hx] at h3
  exact absurd h3 (by norm_num)

theorem sstar
    [Finite G] (h : A2Comp T S₁ S₂ K) :
    IsSStarIn K (Omega1 ((T : Subgroup G) ⊓ K)) := by
  refine G41.isSStarIn_of_lt (ih_all (Nat.card K + 1)) (Nat.lt_succ_self _) h.sylowIn
    (omega1_le_self _) h.isMulCommutative_omega1 ?_
  intro a ha k _ hk
  have ha2 := sq_eq_one_of_mem_omega1 h.isMulCommutative_omega1 ha
  refine subset_closure ⟨hk, ?_⟩
  rw [show (k⁻¹ * a * k) ^ 2 = k⁻¹ * a ^ 2 * k by rw [pow_two, pow_two]; group, ha2]
  group

theorem normalClosureIn_eq [Finite G] (h : A2Comp T S₁ S₂ K) :
    normalClosureIn K (Omega1 ((T : Subgroup G) ⊓ K)) = K := by
  have : IsSimpleGroup K := h.isSimpleGroup
  set Ω := Omega1 ((T : Subgroup G) ⊓ K)
  have hΩK : Ω ≤ K := (omega1_le_self _).trans inf_le_right
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal
      (normalClosure ((Ω.subgroupOf K : Subgroup K) : Set K)) with hb | ht
  · exfalso
    apply h.omega1_ne_bot
    rw [eq_bot_iff]
    intro x hx
    have : (⟨x, hΩK hx⟩ : K) ∈ normalClosure ((Ω.subgroupOf K : Subgroup K) : Set K) :=
      subset_normalClosure (mem_subgroupOf.mpr hx)
    rw [hb, mem_bot] at this
    exact (mem_bot).mpr (congrArg Subtype.val this)
  · rw [normalClosureIn, ht, ← MonoidHom.range_eq_map, range_subtype]

theorem le_normalizer₁ (h : A2Comp T S₁ S₂ K) :
    S₁ ≤ normalizer (((T : Subgroup G) ⊓ K : Subgroup G) : Set G) := by
  intro s hs
  have hsT := h.le₁ hs
  refine mem_normalizer_iff.mpr fun x => ⟨fun hx => ?_, fun hx => ?_⟩
  · exact mem_inf.mpr ⟨mul_mem (mul_mem hsT (mem_inf.mp hx).1) (inv_mem hsT),
      h.normal.conj_mem _ (mem_inf.mp hx).2 s⟩
  · have h1 := mem_inf.mp hx
    refine mem_inf.mpr ⟨?_, ?_⟩
    · have := mul_mem (mul_mem (inv_mem hsT) h1.1) hsT
      simpa [mul_assoc] using this
    · have := h.normal.conj_mem _ h1.2 s⁻¹
      simpa [mul_assoc] using this

theorem mem_inf_of_mem (h : A2Comp T S₁ S₂ K) {α t : G} (hα : α ∈ S₁)
    (ht : t ∈ (T : Subgroup G) ⊓ K) : α⁻¹ * t * α * t⁻¹ ∈ S₁ ⊓ ((T : Subgroup G) ⊓ K) := by
  have hαN := h.le_normalizer₁ hα
  have h1 : α⁻¹ * t * α ∈ (T : Subgroup G) ⊓ K := by
    have := (mem_normalizer_iff.mp (inv_mem hαN) t).mp ht
    simpa using this
  refine mem_inf.mpr ⟨?_, mul_mem h1 (inv_mem ht)⟩
  have htT : t ∈ (T : Subgroup G) := (mem_inf.mp ht).1
  have h2 : t * α * t⁻¹ ∈ S₁ := by
    have := h.sc₁ α hα t⁻¹ (by simpa using mul_mem (mul_mem htT (h.le₁ hα)) (inv_mem htT))
    simpa using this
  have e : α⁻¹ * t * α * t⁻¹ = α⁻¹ * (t * α * t⁻¹) := by group
  rw [e]
  exact mul_mem (inv_mem hα) h2

end A2Comp

end CFSG.Goldschmidt75
