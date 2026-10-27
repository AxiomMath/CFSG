module

public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_12Aux

public section

namespace CFSG.QuasithinUnique

open CFSG.Open

section E27

variable {G : Type} [Group G] [Finite G]

theorem perm6_pow_nine : ∀ σ : Equiv.Perm (Fin 6), σ ^ 9 = 1 → σ ^ 3 = 1 := by decide +kernel

theorem exists_elemAbelian_nine {K : Subgroup G} (eK : ↥K ≃* alternatingGroup (Fin 6)) :
    ∃ P : Subgroup G, P ≤ K ∧ IsElemAbelian 3 P ∧ Nat.card P = 9 := by
  have h3 : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  have hK : Nat.card K = 360 := by
    rw [Nat.card_congr eK.toEquiv, Nat.card_eq_fintype_card, card_alternatingGroup]
    simp [Nat.factorial]
  obtain ⟨P₀, hP₀⟩ := Sylow.exists_subgroup_card_pow_prime (G := ↥K) 3 (n := 2)
    (by rw [hK]; norm_num)
  have hcomm := (IsPGroup.isMulCommutative_of_card_eq_prime_sq (p := 3) hP₀).is_comm.comm
  have hexp : ∀ x : ↥P₀, (x : ↥K) ^ 3 = 1 := by
    intro x
    have h9 : x ^ 9 = 1 := by
      have := pow_card_eq_one' (G := ↥P₀) (x := x)
      rw [hP₀] at this
      simpa using this
    have h9' : (x : ↥K) ^ 9 = 1 := by
      have := congrArg Subtype.val h9
      simpa using this
    have h9'' : ((eK (x : ↥K) : alternatingGroup (Fin 6)) : Equiv.Perm (Fin 6)) ^ 9 = 1 := by
      have := congrArg (fun y : ↥K => ((eK y : alternatingGroup (Fin 6)) : Equiv.Perm (Fin 6))) h9'
      simpa using this
    have h3'' := perm6_pow_nine _ h9''
    apply eK.injective
    apply Subtype.ext
    simpa using h3''
  refine ⟨P₀.map K.subtype, Subgroup.map_subtype_le _, ⟨⟨⟨fun a b => ?_⟩⟩, fun x hx => ?_⟩, ?_⟩
  · obtain ⟨a', ha', ha⟩ := Subgroup.mem_map.mp a.2
    obtain ⟨b', hb', hb⟩ := Subgroup.mem_map.mp b.2
    apply Subtype.ext
    show (a : G) * b = b * a
    rw [← ha, ← hb]
    have := hcomm ⟨a', ha'⟩ ⟨b', hb'⟩
    have h2 := congrArg (fun y : ↥P₀ => (K.subtype (y : ↥K))) this
    simpa using h2
  · obtain ⟨x', hx', rfl⟩ := Subgroup.mem_map.mp hx
    have := congrArg K.subtype (hexp ⟨x', hx'⟩)
    simpa using this
  · rw [Subgroup.card_map_of_injective K.subtype_injective, hP₀]
    norm_num

theorem exists_elemAbelian_27 {K : Subgroup G} (eK : ↥K ≃* alternatingGroup (Fin 6))
    (hZ : ∀ x ∈ K, (∀ y ∈ K, x * y = y * x) → x = 1) {c : G} (hc3 : c ^ 3 = 1) (hc1 : c ≠ 1)
    (hcK : ∀ k ∈ K, c * k = k * c) :
    ∃ E : Subgroup G, E ≤ K ⊔ Subgroup.zpowers c ∧ IsElemAbelian 3 E ∧ Nat.card E = 3 ^ 3 := by
  obtain ⟨P, hPK, hP, hP9⟩ := exists_elemAbelian_nine eK
  set Q : Subgroup G := Subgroup.zpowers c with hQ
  have hQcard : Nat.card Q = 3 := by
    rw [hQ, Nat.card_zpowers]
    exact orderOf_eq_prime hc3 hc1
  have hQc : ∀ y ∈ Q, ∀ k ∈ K, k * y = y * k := by
    intro y hy k hk
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
    exact ((Commute.zpow_left (show Commute c k from hcK k hk) n).symm).eq
  have hcomm : ∀ (a : ↥P) (b : ↥Q), Commute (P.subtype a) (Q.subtype b) := by
    intro a b
    exact (show Commute (a : G) (b : G) from hQc b b.2 a (hPK a.2))
  let φ : ↥P × ↥Q →* G := MonoidHom.noncommCoprod P.subtype Q.subtype hcomm
  have hdisj : Disjoint P.subtype.range Q.subtype.range := by
    rw [Subgroup.range_subtype, Subgroup.range_subtype, Subgroup.disjoint_def]
    intro x hxP hxQ
    exact hZ x (hPK hxP) (fun k hk => (hQc x hxQ k hk).symm)
  have hinj : Function.Injective φ :=
    (MonoidHom.noncommCoprod_injective _ _ hcomm).mpr
      ⟨P.subtype_injective, Q.subtype_injective, hdisj⟩
  refine ⟨φ.range, ?_, ?_, ?_⟩
  · rw [show φ.range = P.subtype.range ⊔ Q.subtype.range from MonoidHom.noncommCoprod_range _ _ hcomm,
      Subgroup.range_subtype, Subgroup.range_subtype]
    exact sup_le_sup hPK le_rfl
  · have hQcomm : ∀ y ∈ Q, ∀ y' ∈ Q, y * y' = y' * y := by
      intro y hy y' hy'
      obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
      obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy'
      exact (Commute.zpow_zpow_self c n m).eq
    have hQ3 : ∀ y ∈ Q, y ^ 3 = 1 := by
      intro y hy
      obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
      rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul]
      simp [hc3]
    have hu3 : ∀ u : ↥P × ↥Q, u ^ 3 = 1 := by
      intro u
      refine Prod.ext (Subtype.ext ?_) (Subtype.ext ?_)
      · exact hP.2 _ u.1.2
      · exact hQ3 _ u.2.2
    have hucomm : ∀ u v : ↥P × ↥Q, u * v = v * u := by
      intro u v
      refine Prod.ext (Subtype.ext ?_) (Subtype.ext ?_)
      · exact isElemAbelian_mul_comm hP u.1.2 v.1.2
      · exact hQcomm _ u.2.2 _ v.2.2
    refine ⟨⟨⟨fun x y => ?_⟩⟩, fun x hx => ?_⟩
    · obtain ⟨u, hu⟩ := x.2
      obtain ⟨v, hv⟩ := y.2
      apply Subtype.ext
      show (x : G) * y = y * x
      rw [← hu, ← hv, ← map_mul, ← map_mul, hucomm]
    · obtain ⟨u, rfl⟩ := hx
      rw [← map_pow, hu3, map_one]
  · have hc := Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv
    rw [Nat.card_prod, hP9, hQcard] at hc
    rw [← hc]
    norm_num

end E27

end CFSG.QuasithinUnique
