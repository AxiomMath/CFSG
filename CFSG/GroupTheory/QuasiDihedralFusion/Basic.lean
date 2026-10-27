module

public import CFSG.GroupTheory.QuasiDihedralFusion.Defs
public import CFSG.GroupTheory.CyclicSylowNormalOddComplement

public section

namespace CFSG.QuasiDihedralFusion

universe u v

section Automizer

variable {H : Type u} [Group H]

theorem automizerIndex_eq_card_range (T : Subgroup H) :
    automizerIndex T = Nat.card T.normalizerMonoidHom.range := by
  rw [automizerIndex, Subgroup.relIndex, ← Subgroup.normalizerMonoidHom_ker, Subgroup.index_ker]

theorem normalizerMonoidHom_apply_coe (T : Subgroup H) (g : Subgroup.normalizer (T : Set H))
    (x : T) : ((T.normalizerMonoidHom g x : T) : H) = (g : H) * x * (g : H)⁻¹ := rfl

theorem inner_le_normalizerMonoidHom_range (V : Subgroup H) :
    (MulAut.conj : V →* MulAut V).range ≤ V.normalizerMonoidHom.range := by
  rintro _ ⟨v, rfl⟩
  refine ⟨⟨v, Subgroup.le_normalizer v.property⟩, ?_⟩
  ext w
  rfl

theorem sup_centralizer_subgroupOf_eq_comap (V : Subgroup H) :
    (V ⊔ Subgroup.centralizer (V : Set H)).subgroupOf (Subgroup.normalizer (V : Set H)) =
      (MulAut.conj : V →* MulAut V).range.comap V.normalizerMonoidHom := by
  apply le_antisymm
  · rw [Subgroup.subgroupOf_sup Subgroup.le_normalizer
      (Subgroup.centralizer_le_normalizer (V : Set H))]
    apply sup_le
    · intro x hx
      refine ⟨⟨(x : H), hx⟩, ?_⟩
      ext w
      rfl
    · intro x hx
      have hker : x ∈ V.normalizerMonoidHom.ker := by
        rw [Subgroup.normalizerMonoidHom_ker]
        exact hx
      change V.normalizerMonoidHom x ∈ (MulAut.conj : V →* MulAut V).range
      rw [hker]
      exact Subgroup.one_mem _
  · rintro x ⟨v, hv⟩
    have hc : (v : H)⁻¹ * (x : H) ∈ Subgroup.centralizer (V : Set H) := by
      rw [Subgroup.mem_centralizer_iff]
      intro w hw
      have h := congrArg (fun φ : MulAut V => ((φ ⟨w, hw⟩ : V) : H)) hv
      change (v : H) * w * (v : H)⁻¹ = (x : H) * w * (x : H)⁻¹ at h
      calc w * ((v : H)⁻¹ * x) = (v : H)⁻¹ * ((v : H) * w * (v : H)⁻¹) * x := by group
        _ = (v : H)⁻¹ * ((x : H) * w * (x : H)⁻¹) * x := by rw [h]
        _ = ((v : H)⁻¹ * x) * w := by group
    have hx : (x : H) = (v : H) * ((v : H)⁻¹ * x) := by group
    change (x : H) ∈ V ⊔ Subgroup.centralizer (V : Set H)
    rw [hx]
    exact Subgroup.mul_mem_sup v.property hc

theorem outerAutomizerIndex_mul_card_inner [Finite H] (V : Subgroup H) :
    outerAutomizerIndex V * Nat.card (MulAut.conj : V →* MulAut V).range =
      Nat.card V.normalizerMonoidHom.range := by
  rw [outerAutomizerIndex, Subgroup.relIndex, sup_centralizer_subgroupOf_eq_comap,
    Subgroup.index_comap, Subgroup.relIndex]
  have hle := inner_le_normalizerMonoidHom_range V
  have h := Subgroup.card_mul_index
    ((MulAut.conj : V →* MulAut V).range.subgroupOf V.normalizerMonoidHom.range)
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv] at h
  rw [mul_comm]
  exact h

end Automizer

section Sylow

variable {H : Type u} [Group H] [Finite H]

theorem exists_conj_le_sylow {p : ℕ} [Fact p.Prime] (K : Subgroup H) (S : Sylow p H)
    (hSK : (S : Subgroup H) ≤ K) (W : Subgroup H) (hWK : W ≤ K) (hW : IsPGroup p W) :
    ∃ c ∈ K, W.map (MulAut.conj c).toMonoidHom ≤ S := by
  let S' : Sylow p K := S.subtype hSK
  have hW' : IsPGroup p (W.subgroupOf K) :=
    hW.of_equiv (Subgroup.subgroupOfEquivOfLe hWK).symm
  obtain ⟨P, hP⟩ := hW'.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq K P S'
  refine ⟨(g : H), g.property, ?_⟩
  rintro _ ⟨w, hw, rfl⟩
  have hwP : (⟨w, hWK hw⟩ : K) ∈ (P : Subgroup K) := hP hw
  have hmem : MulAut.conj g (⟨w, hWK hw⟩ : K) ∈ ((g • P : Sylow p K) : Subgroup K) := by
    rw [Sylow.coe_subgroup_smul]
    exact Subgroup.smul_mem_pointwise_smul _ _ _ hwP
  rw [hg] at hmem
  have hmem' : MulAut.conj g (⟨w, hWK hw⟩ : K) ∈ (S : Subgroup H).subgroupOf K := by
    rw [← Sylow.coe_subtype S hSK]
    exact hmem
  exact hmem'

theorem relIndex_dvd_index_of_normal_right (S K : Subgroup H) [K.Normal] :
    S.relIndex K ∣ S.index := by
  have h1 : S.relIndex K * K.index = (S ⊓ K).index := by
    have h := Subgroup.relIndex_inf_mul_relIndex S K ⊤
    rwa [inf_top_eq, Subgroup.relIndex_top_right, Subgroup.relIndex_top_right] at h
  have h2 : (S ⊓ K).relIndex S * S.index = (S ⊓ K).index :=
    Subgroup.relIndex_mul_index inf_le_left
  have h3 : (S ⊓ K).relIndex S = K.relIndex (S ⊔ K) := by
    rw [Subgroup.relIndex_sup_right, inf_comm, Subgroup.inf_relIndex_right]
  obtain ⟨m, hm⟩ := Subgroup.relIndex_dvd_index_of_le (le_sup_right : K ≤ S ⊔ K)
  have hpos : 0 < K.relIndex (S ⊔ K) := by
    apply Nat.pos_of_ne_zero
    intro h0
    rw [h0, zero_mul] at hm
    exact Subgroup.index_ne_zero_of_finite hm
  refine ⟨m, ?_⟩
  rw [hm, ← h2, h3] at h1
  have h4 : K.relIndex (S ⊔ K) * (S.relIndex K * m) = K.relIndex (S ⊔ K) * S.index := by
    rw [← h1]
    ring
  exact (Nat.eq_of_mul_eq_mul_left hpos h4).symm

omit [Finite H] in
theorem isPGroup_inf_normal {p : ℕ} (S : Sylow p H) (K : Subgroup H) :
    IsPGroup p ((S : Subgroup H).subgroupOf K) :=
  S.isPGroup'.comap_subtype

theorem not_dvd_relIndex_of_normal {p : ℕ} [Fact p.Prime] (S : Sylow p H) (K : Subgroup H)
    [K.Normal] : ¬ p ∣ ((S : Subgroup H).subgroupOf K).index := by
  intro hdvd
  have h : p ∣ (S : Subgroup H).relIndex K := hdvd
  exact S.not_dvd_index (dvd_trans h (relIndex_dvd_index_of_normal_right (S : Subgroup H) K))

@[expose] noncomputable def sylowInfNormal {p : ℕ} [Fact p.Prime] (S : Sylow p H)
    (K : Subgroup H) [K.Normal] : Sylow p K :=
  (isPGroup_inf_normal S K).toSylow (not_dvd_relIndex_of_normal S K)

theorem sylowInfNormal_coe {p : ℕ} [Fact p.Prime] (S : Sylow p H) (K : Subgroup H)
    [K.Normal] : (sylowInfNormal S K : Subgroup K) = (S : Subgroup H).subgroupOf K :=
  IsPGroup.toSylow_coe _ _

theorem normal_sup_sylow_eq_top {p : ℕ} [Fact p.Prime] (K : Subgroup H) [K.Normal]
    (hK : ∃ k : ℕ, K.index = p ^ k) (S : Sylow p H) : K ⊔ (S : Subgroup H) = ⊤ := by
  obtain ⟨k, hk⟩ := hK
  have hq : IsPGroup p (H ⧸ K) := IsPGroup.of_card (n := k) hk
  let Q : Sylow p (H ⧸ K) := S.mapSurjective (QuotientGroup.mk'_surjective K)
  have htop : (Q : Subgroup (H ⧸ K)) = ⊤ := (Q.is_maximal' (hq.to_subgroup ⊤) le_top).symm
  have hmap : (S : Subgroup H).map (QuotientGroup.mk' K) = ⊤ := by
    rw [← htop]
    exact (Sylow.coe_mapSurjective _ S).symm
  have h := congrArg (Subgroup.comap (QuotientGroup.mk' K)) hmap
  rw [Subgroup.comap_map_eq, QuotientGroup.ker_mk', Subgroup.comap_top] at h
  rw [sup_comm]
  exact h

omit [Finite H] in
theorem exists_mul_of_sup_eq_top (K S : Subgroup H) [K.Normal] (h : K ⊔ S = ⊤) (g : H) :
    ∃ t ∈ S, ∃ k ∈ K, t * k = g := by
  have hg : g ∈ ((S ⊔ K : Subgroup H) : Set H) := by
    rw [sup_comm, h]
    exact Subgroup.mem_top g
  rw [Subgroup.mul_normal S K] at hg
  obtain ⟨t, ht, k, hk, htk⟩ := Set.mem_mul.mp hg
  exact ⟨t, ht, k, hk, htk⟩

omit [Finite H] in
theorem exists_isConj_normal_of_isConj (K S : Subgroup H) [K.Normal] (h : K ⊔ S = ⊤)
    {x y : H} (hx : x ∈ K) (hxy : IsConj x y) :
    ∃ t ∈ S, ∃ hy : t⁻¹ * y * t ∈ K,
      IsConj (⟨x, hx⟩ : K) (⟨t⁻¹ * y * t, hy⟩ : K) := by
  obtain ⟨g, hg⟩ := isConj_iff.mp hxy
  obtain ⟨t, ht, k, hk, rfl⟩ := exists_mul_of_sup_eq_top K S h g
  have heq : k * x * k⁻¹ = t⁻¹ * y * t := by
    rw [← hg]
    group
  have hy : t⁻¹ * y * t ∈ K := by
    rw [← heq]
    exact K.mul_mem (K.mul_mem hk hx) (K.inv_mem hk)
  refine ⟨t, ht, hy, isConj_iff.mpr ⟨⟨k, hk⟩, ?_⟩⟩
  apply Subtype.ext
  exact heq

end Sylow

section IndexTwo

variable {K : Type v} [Group K]

theorem mem_iff_of_isConj_of_index_two {M : Subgroup K} (hM : M.index = 2) {a b : K}
    (hab : IsConj a b) : a ∈ M ↔ b ∈ M := by
  have hN := Subgroup.normal_of_index_eq_two hM
  obtain ⟨c, rfl⟩ := isConj_iff.mp hab
  constructor
  · intro ha
    exact hN.conj_mem a ha c
  · intro hb
    have h := hN.conj_mem _ hb c⁻¹
    simpa only [inv_inv, mul_assoc, inv_mul_cancel, mul_one, inv_mul_cancel_left] using h

theorem sylow_not_le_of_index_two [Finite K] {M : Subgroup K} (hM : M.index = 2)
    (P : Sylow 2 K) : ¬ (P : Subgroup K) ≤ M := by
  intro hPM
  have hdvd : M.index ∣ (P : Subgroup K).index := Subgroup.index_dvd_of_le hPM
  rw [hM] at hdvd
  exact P.not_dvd_index hdvd

end IndexTwo

section NormalSubgroups

variable {H : Type u} [Group H]

theorem mem_map_subtype_iff_mem {K : Subgroup H} {M : Subgroup K} {x : H} (hx : x ∈ K) :
    x ∈ M.map K.subtype ↔ (⟨x, hx⟩ : K) ∈ M := by
  constructor
  · rintro ⟨m, hm, hmx⟩
    have : m = ⟨x, hx⟩ := Subtype.ext hmx
    rwa [← this]
  · intro h
    exact ⟨_, h, rfl⟩

theorem map_subtype_mul_mem_iff {K : Subgroup H} {M : Subgroup K} (hM : M.index = 2) {x y : H}
    (hx : x ∈ K) (hy : y ∈ K) :
    x * y ∈ M.map K.subtype ↔ (x ∈ M.map K.subtype ↔ y ∈ M.map K.subtype) := by
  rw [mem_map_subtype_iff_mem (K.mul_mem hx hy), mem_map_subtype_iff_mem hx,
    mem_map_subtype_iff_mem hy]
  exact Subgroup.mul_mem_iff_of_index_two (a := (⟨x, hx⟩ : K)) (b := ⟨y, hy⟩) hM

theorem map_subtype_mem_iff_of_isConj {K : Subgroup H} {M : Subgroup K} (hM : M.index = 2)
    {x y : H} (hx : x ∈ K) (hy : y ∈ K) (hxy : IsConj (⟨x, hx⟩ : K) ⟨y, hy⟩) :
    x ∈ M.map K.subtype ↔ y ∈ M.map K.subtype := by
  rw [mem_map_subtype_iff_mem hx, mem_map_subtype_iff_mem hy]
  exact mem_iff_of_isConj_of_index_two hM hxy

variable [Finite H]

theorem inf_sylow_not_le_map_of_index_two (S : Sylow 2 H) (K : Subgroup H) [K.Normal]
    {M : Subgroup K} (hM : M.index = 2) : ¬ K ⊓ (S : Subgroup H) ≤ M.map K.subtype := by
  intro hle
  apply sylow_not_le_of_index_two hM (sylowInfNormal S K)
  rw [sylowInfNormal_coe]
  intro k hk
  have hkS : (k : H) ∈ (S : Subgroup H) := Subgroup.mem_subgroupOf.mp hk
  exact (mem_map_subtype_iff_mem k.property).mp (hle ⟨k.property, hkS⟩)

theorem nonempty_sylow_equiv_inf {p : ℕ} [Fact p.Prime] (S : Sylow p H) (K : Subgroup H)
    [K.Normal] (P : Sylow p K) : Nonempty (P ≃* (K ⊓ (S : Subgroup H) : Subgroup H)) := by
  have h4 : ((S : Subgroup H).subgroupOf K).map K.subtype = K ⊓ (S : Subgroup H) := by
    rw [Subgroup.subgroupOf_map_subtype, inf_comm]
  exact ⟨(Sylow.equiv P (sylowInfNormal S K)).trans
    ((MulEquiv.subgroupCongr (sylowInfNormal_coe S K)).trans
      ((((S : Subgroup H).subgroupOf K).equivMapOfInjective K.subtype
        K.subtype_injective).trans (MulEquiv.subgroupCongr h4)))⟩

theorem exists_focal_kernel (S : Sylow 2 H) :
    ∃ K : Subgroup H, K.Normal ∧ K.index = ((commutator H).subgroupOf (S : Subgroup H)).index ∧
      (∃ k : ℕ, K.index = 2 ^ k) ∧
      K ⊓ (S : Subgroup H) =
        ((commutator H).subgroupOf (S : Subgroup H)).map (S : Subgroup H).subtype := by
  have hindex : (CFSG.Semidihedral.FocalTransfer.focalTransfer (S : Subgroup H)).ker.index =
      ((commutator H).subgroupOf (S : Subgroup H)).index := by
    rw [Subgroup.index_ker, MonoidHom.range_eq_top.mpr
      (CFSG.Semidihedral.FocalTransfer.focalTransfer_surjective S), Subgroup.card_top,
      ← CFSG.Semidihedral.FocalTransfer.conjugatePairFocal_eq_derived_subgroupOf S]
    rfl
  refine ⟨_, inferInstance, hindex, ?_, ?_⟩
  · obtain ⟨a, ha⟩ := S.isPGroup'.exists_card_eq
    have hdvd : ((commutator H).subgroupOf (S : Subgroup H)).index ∣ 2 ^ a := by
      rw [← ha]
      exact Subgroup.index_dvd_card _
    obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd
    exact ⟨k, hindex.trans hk⟩
  · rw [CFSG.Semidihedral.FocalTransfer.ker_focalTransfer_inf S,
      CFSG.Semidihedral.FocalTransfer.conjugatePairFocal_eq_derived_subgroupOf S]

theorem hasNormalPComplement_of_cyclic_kernel (S : Sylow 2 H) (K : Subgroup H) [K.Normal]
    (hK : ∃ k : ℕ, K.index = 2 ^ k) (hcyc : IsCyclic (K ⊓ (S : Subgroup H) : Subgroup H)) :
    HasNormalPComplement 2 H := by
  let P := sylowInfNormal S K
  obtain ⟨eP⟩ := nonempty_sylow_equiv_inf S K P
  have hPcyc : IsCyclic P := eP.isCyclic.mpr hcyc
  obtain ⟨-, -, -, ⟨-, hodd, hidx, -⟩, -⟩ := cyclic_sylow_normal_odd_complement P hPcyc
  let N := (CFSG.pPrimeCore 2 K).map K.subtype
  have hN : N.Normal := inferInstance
  refine ⟨N, hN, ?_, ?_⟩
  · rw [Subgroup.card_map_of_injective K.subtype_injective]
    exact Nat.coprime_two_left.mpr hodd
  · obtain ⟨k, hk⟩ := hK
    obtain ⟨a, ha⟩ := P.isPGroup'.exists_card_eq
    refine IsPGroup.of_card (n := a + k) ?_
    change N.index = 2 ^ (a + k)
    rw [Subgroup.index_map_subtype, hidx, ha, hk, pow_add]

end NormalSubgroups

section ClassCount

variable {H : Type u} [Group H]

theorem conjClasses_image_eq_pair {k : ℕ} (a b : H) (ha : orderOf a = k)
    (hb : orderOf b = k) (hcover : ∀ x : H, orderOf x = k → IsConj a x ∨ IsConj b x) :
    ConjClasses.mk '' {x : H | orderOf x = k} = {ConjClasses.mk a, ConjClasses.mk b} := by
  ext c
  constructor
  · rintro ⟨x, hx, rfl⟩
    rcases hcover x hx with h | h
    · exact Or.inl (ConjClasses.mk_eq_mk_iff_isConj.mpr h.symm)
    · exact Or.inr (ConjClasses.mk_eq_mk_iff_isConj.mpr h.symm)
  · rintro (rfl | rfl)
    · exact ⟨a, ha, rfl⟩
    · exact ⟨b, hb, rfl⟩

theorem conjClassCountOfOrder_eq_one {k : ℕ} (a b : H) (ha : orderOf a = k)
    (hb : orderOf b = k) (hcover : ∀ x : H, orderOf x = k → IsConj a x ∨ IsConj b x)
    (hab : IsConj a b) : conjClassCountOfOrder H k = 1 := by
  rw [conjClassCountOfOrder, conjClasses_image_eq_pair a b ha hb hcover,
    ConjClasses.mk_eq_mk_iff_isConj.mpr hab, Set.pair_eq_singleton, Set.ncard_singleton]

theorem conjClassCountOfOrder_eq_two {k : ℕ} (a b : H) (ha : orderOf a = k)
    (hb : orderOf b = k) (hcover : ∀ x : H, orderOf x = k → IsConj a x ∨ IsConj b x)
    (hab : ¬ IsConj a b) : conjClassCountOfOrder H k = 2 := by
  rw [conjClassCountOfOrder, conjClasses_image_eq_pair a b ha hb hcover]
  exact Set.ncard_pair (fun h => hab (ConjClasses.mk_eq_mk_iff_isConj.mp h))

theorem conjClassCountOfOrder_eq_three {k : ℕ} (a b c : H) (ha : orderOf a = k)
    (hb : orderOf b = k) (hc : orderOf c = k)
    (hcover : ∀ x : H, orderOf x = k → IsConj a x ∨ IsConj b x ∨ IsConj c x)
    (hab : ¬ IsConj a b) (hac : ¬ IsConj a c) (hbc : ¬ IsConj b c) :
    conjClassCountOfOrder H k = 3 := by
  have himage : ConjClasses.mk '' {x : H | orderOf x = k} =
      {ConjClasses.mk a, ConjClasses.mk b, ConjClasses.mk c} := by
    ext d
    constructor
    · rintro ⟨x, hx, rfl⟩
      rcases hcover x hx with h | h | h
      · exact Or.inl (ConjClasses.mk_eq_mk_iff_isConj.mpr h.symm)
      · exact Or.inr (Or.inl (ConjClasses.mk_eq_mk_iff_isConj.mpr h.symm))
      · exact Or.inr (Or.inr (ConjClasses.mk_eq_mk_iff_isConj.mpr h.symm))
    · rintro (rfl | rfl | rfl)
      · exact ⟨a, ha, rfl⟩
      · exact ⟨b, hb, rfl⟩
      · exact ⟨c, hc, rfl⟩
  rw [conjClassCountOfOrder, himage, Set.ncard_eq_three]
  exact ⟨_, _, _, fun h => hab (ConjClasses.mk_eq_mk_iff_isConj.mp h),
    fun h => hac (ConjClasses.mk_eq_mk_iff_isConj.mp h),
    fun h => hbc (ConjClasses.mk_eq_mk_iff_isConj.mp h), rfl⟩

end ClassCount

end CFSG.QuasiDihedralFusion
