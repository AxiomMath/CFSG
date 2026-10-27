module

public import CFSG.LocalAnalysis.QuasithinUnique.Defs

public section

namespace CFSG.AGLEmbeddingD2.Tits.OrdinaryProofs

variable {G : Type*} [Group G]

theorem relIndex_sup_eq_relIndex_of_normalizes (T K : Subgroup G)
    (hN : T ⊔ K ≤ Subgroup.normalizer (K : Set G)) :
    K.relIndex (T ⊔ K) = K.relIndex T := by
  have : (K.subgroupOf (T ⊔ K)).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer le_sup_right).mpr hN
  have htop : T.subgroupOf (T ⊔ K) ⊔ K.subgroupOf (T ⊔ K) = ⊤ := by
    rw [← Subgroup.subgroupOf_sup le_sup_left le_sup_right, Subgroup.subgroupOf_self]
  have h1 := Subgroup.relIndex_sup_right (H := T.subgroupOf (T ⊔ K))
    (K := K.subgroupOf (T ⊔ K))
  have h2 : (K.subgroupOf (T ⊔ K)).relIndex (T.subgroupOf (T ⊔ K)) = K.relIndex T :=
    Subgroup.relIndex_subgroupOf le_sup_left
  rw [htop, Subgroup.relIndex_top_right, h2] at h1
  exact h1

theorem not_two_dvd_relIndex_inf_of_normalizes [Finite G] {T K M : Subgroup G}
    (hTM : T ≤ M) (hKM : K ≤ M) (hTN : T ≤ Subgroup.normalizer (K : Set G))
    (hodd : ¬ 2 ∣ T.relIndex M) : ¬ 2 ∣ (T ⊓ K).relIndex K := by
  have hL : T ⊔ K ≤ M := sup_le hTM hKM
  have hN : T ⊔ K ≤ Subgroup.normalizer (K : Set G) := sup_le hTN Subgroup.le_normalizer
  have hsec := relIndex_sup_eq_relIndex_of_normalizes T K hN
  have hA := Subgroup.relIndex_inf_mul_relIndex T K (T ⊔ K)
  rw [inf_eq_left.mpr le_sup_right] at hA
  rw [hsec] at hA
  have hB := Subgroup.relIndex_mul_relIndex (T ⊓ K) T (T ⊔ K) inf_le_left le_sup_left
  rw [Subgroup.inf_relIndex_left] at hB
  have hne : K.relIndex T ≠ 0 := Subgroup.index_ne_zero_of_finite
  have key : T.relIndex K * K.relIndex T = T.relIndex (T ⊔ K) * K.relIndex T := by
    rw [hA, ← hB, Nat.mul_comm]
  have hTK : T.relIndex K = T.relIndex (T ⊔ K) :=
    Nat.eq_of_mul_eq_mul_right (Nat.pos_of_ne_zero hne) key
  rw [Subgroup.inf_relIndex_right, hTK]
  intro h
  apply hodd
  exact h.trans ⟨_, (Subgroup.relIndex_mul_relIndex T (T ⊔ K) M le_sup_left hL).symm⟩

theorem relIndex_map_conj_eq [Finite G] (A K : Subgroup G) (g : G)
    (hg : g ∈ Subgroup.normalizer (K : Set G)) (hAK : A ≤ K) :
    (A.map (MulAut.conj g).toMonoidHom).relIndex K = A.relIndex K := by
  have hBK : A.map (MulAut.conj g).toMonoidHom ≤ K := by
    rintro _ ⟨a, ha, rfl⟩
    exact (Subgroup.mem_normalizer_iff.mp hg a).mp (hAK ha)
  have hcard : Nat.card (A.map (MulAut.conj g).toMonoidHom) = Nat.card A :=
    Subgroup.card_map_of_injective (MulAut.conj g).injective
  have h1 := Subgroup.relIndex_mul_card (H := A) (K := K)
  have h2 := Subgroup.relIndex_mul_card (H := A.map (MulAut.conj g).toMonoidHom) (K := K)
  rw [inf_eq_left.mpr hAK] at h1
  rw [inf_eq_left.mpr hBK, hcard] at h2
  exact Nat.eq_of_mul_eq_mul_right (Nat.card_pos) (h2.trans h1.symm)

theorem exists_conj_eq_of_sylow [Finite G] {K A B : Subgroup G} {p : ℕ} [Fact p.Prime]
    (hAK : A ≤ K) (hBK : B ≤ K)
    (hA1 : IsPGroup p (A.subgroupOf K)) (hA2 : ¬ p ∣ (A.subgroupOf K).index)
    (hB1 : IsPGroup p (B.subgroupOf K)) (hB2 : ¬ p ∣ (B.subgroupOf K).index) :
    ∃ x ∈ K, ∀ y : G, y ∈ B ↔ x⁻¹ * y * x ∈ A := by
  obtain ⟨h, hh⟩ := MulAction.exists_smul_eq K (hA1.toSylow hA2) (hB1.toSylow hB2)
  have hmap : (A.subgroupOf K).map (MulAut.conj h).toMonoidHom = B.subgroupOf K := by
    have := congrArg (fun P : Sylow p K => (P : Subgroup K)) hh
    rw [Sylow.coe_subgroup_smul, IsPGroup.toSylow_coe, Subgroup.pointwise_smul_def] at this
    exact this
  have hmem : ∀ k : K, k ∈ B.subgroupOf K ↔ (h⁻¹ * k * h) ∈ A.subgroupOf K := by
    intro k
    rw [← hmap, Subgroup.mem_map]
    constructor
    · rintro ⟨s, hs, he⟩
      have he' : (h : K) * s * (h : K)⁻¹ = k := he
      have hs' : s = h⁻¹ * k * h := by
        rw [← he']
        simp [mul_assoc]
      rw [hs'] at hs
      exact hs
    · intro hk
      exact ⟨h⁻¹ * k * h, hk, by simp [mul_assoc]⟩
  refine ⟨(h : G), h.2, fun y => ?_⟩
  by_cases hy : y ∈ K
  · have := hmem ⟨y, hy⟩
    simpa [Subgroup.mem_subgroupOf] using this
  · constructor
    · intro hyB
      exact absurd (hBK hyB) hy
    · intro hyA
      exfalso
      apply hy
      have h2 : (h : G)⁻¹ * y * h ∈ K := hAK hyA
      have := K.mul_mem (K.mul_mem h.2 h2) (K.inv_mem h.2)
      simpa [mul_assoc] using this

theorem exists_mul_of_mem_normalizer_sup [Finite G] {M C T X : Subgroup G} (hCM : C ≤ M)
    (hCn : M ≤ Subgroup.normalizer (C : Set G))
    (hT : CFSG.QuasithinUnique.IsSylowTwoOf T M)
    (hXT : X ≤ T) (hTX : T ≤ Subgroup.normalizer (X : Set G))
    (hNS : Subgroup.normalizer ((T ⊓ (X ⊔ C) : Subgroup G) : Set G) ≤
      Subgroup.normalizer (X : Set G))
    {g : G} (hgM : g ∈ M) (hg : g ∈ Subgroup.normalizer ((X ⊔ C : Subgroup G) : Set G)) :
    ∃ c ∈ C, ∃ n ∈ M ⊓ Subgroup.normalizer (X : Set G), g = c * n := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hTM, hT2, hTodd⟩ := hT
  have hXM : X ≤ M := hXT.trans hTM
  have hKM : X ⊔ C ≤ M := sup_le hXM hCM
  have hXconj : ∀ t ∈ T, ∀ x ∈ X, t * x * t⁻¹ ∈ X := fun t ht x hx =>
    (Subgroup.mem_normalizer_iff.mp (hTX ht) x).mp hx
  have hCconj : ∀ t ∈ T, ∀ c ∈ C, t * c * t⁻¹ ∈ C := fun t ht c hc =>
    (Subgroup.mem_normalizer_iff.mp (hCn (hTM ht)) c).mp hc
  have hKT : ∀ t ∈ T, ∀ k ∈ X ⊔ C, t * k * t⁻¹ ∈ X ⊔ C := by
    intro t ht
    have hle : X ⊔ C ≤ (X ⊔ C).comap (MulAut.conj t).toMonoidHom := by
      refine sup_le ?_ ?_
      · intro x hx
        exact (le_sup_left : X ≤ X ⊔ C) (hXconj t ht x hx)
      · intro c hc
        exact (le_sup_right : C ≤ X ⊔ C) (hCconj t ht c hc)
    intro k hk
    exact hle hk
  have hTK : T ≤ Subgroup.normalizer ((X ⊔ C : Subgroup G) : Set G) := by
    intro t ht
    rw [Subgroup.mem_normalizer_iff]
    intro k
    constructor
    · exact hKT t ht k
    · intro hk
      have := hKT t⁻¹ (T.inv_mem ht) (t * k * t⁻¹) hk
      simpa [mul_assoc] using this
  have hdec : ∀ k ∈ X ⊔ C, ∃ c ∈ C, ∃ y ∈ X, k = c * y := by
    let Z : Subgroup G :=
      { carrier := {k | ∃ c ∈ C, ∃ y ∈ X, k = c * y}
        mul_mem' := by
          rintro _ _ ⟨c1, hc1, y1, hy1, rfl⟩ ⟨c2, hc2, y2, hy2, rfl⟩
          have hc2' : y1 * c2 * y1⁻¹ ∈ C := hCconj y1 (hXT hy1) c2 hc2
          refine ⟨c1 * (y1 * c2 * y1⁻¹), C.mul_mem hc1 hc2', y1 * y2, X.mul_mem hy1 hy2, ?_⟩
          simp [mul_assoc]
        one_mem' := ⟨1, C.one_mem, 1, X.one_mem, by simp⟩
        inv_mem' := by
          rintro _ ⟨c, hc, y, hy, rfl⟩
          have hc' : y⁻¹ * c⁻¹ * y ∈ C := by
            have := hCconj y⁻¹ (T.inv_mem (hXT hy)) c⁻¹ (C.inv_mem hc)
            simpa [mul_assoc] using this
          refine ⟨y⁻¹ * c⁻¹ * y, hc', y⁻¹, X.inv_mem hy, ?_⟩
          simp [mul_assoc] }
    have hZ : X ⊔ C ≤ Z := by
      refine sup_le ?_ ?_
      · intro x hx
        exact ⟨1, C.one_mem, x, hx, by simp⟩
      · intro c hc
        exact ⟨c, hc, 1, X.one_mem, by simp⟩
    intro k hk
    exact hZ hk
  set K : Subgroup G := X ⊔ C with hK
  set S : Subgroup G := T ⊓ K with hS
  have hSK : S ≤ K := inf_le_right
  have hTKn : T ≤ Subgroup.normalizer (K : Set G) := hTK
  have hSodd : ¬ 2 ∣ (S.subgroupOf K).index :=
    not_two_dvd_relIndex_inf_of_normalizes hTM hKM hTKn hTodd
  have hS2 : IsPGroup 2 (S.subgroupOf K) :=
    (hT2.to_le inf_le_left).comap_of_injective K.subtype Subtype.coe_injective
  set B : Subgroup G := S.map (MulAut.conj g).toMonoidHom with hB
  have hBK : B ≤ K := by
    rintro _ ⟨s, hs, rfl⟩
    exact (Subgroup.mem_normalizer_iff.mp hg s).mp (hSK hs)
  have hBodd : ¬ 2 ∣ (B.subgroupOf K).index := by
    show ¬ 2 ∣ B.relIndex K
    rw [hB, relIndex_map_conj_eq S K g hg hSK]
    exact hSodd
  have hB2 : IsPGroup 2 (B.subgroupOf K) :=
    ((hT2.to_le inf_le_left).map (MulAut.conj g).toMonoidHom).comap_of_injective K.subtype
      Subtype.coe_injective
  obtain ⟨x, hxK, hxS⟩ := exists_conj_eq_of_sylow hSK hBK hS2 hSodd hB2 hBodd
  have huM : x⁻¹ * g ∈ M := M.mul_mem (M.inv_mem (hKM hxK)) hgM
  have hmemB : ∀ s : G, g * s * g⁻¹ ∈ B ↔ s ∈ S := by
    intro s
    constructor
    · intro hmem
      obtain ⟨s', hs', he⟩ := Subgroup.mem_map.mp hmem
      have he' : g * s' * g⁻¹ = g * s * g⁻¹ := he
      have hss : s' = s := mul_left_cancel (mul_right_cancel he')
      exact hss ▸ hs'
    · intro hs
      exact ⟨s, hs, rfl⟩
  have huN : x⁻¹ * g ∈ Subgroup.normalizer (S : Set G) := by
    rw [Subgroup.mem_normalizer_iff]
    intro s
    have key := hxS (g * s * g⁻¹)
    have hconj : (x⁻¹ * g) * s * (x⁻¹ * g)⁻¹ = x⁻¹ * (g * s * g⁻¹) * x := by
      simp [mul_assoc]
    rw [hconj, ← key, hmemB]
  obtain ⟨c, hc, y, hy, hxcy⟩ := hdec x hxK
  refine ⟨c, hc, y * (x⁻¹ * g), Subgroup.mem_inf.mpr ⟨?_, ?_⟩, ?_⟩
  · exact M.mul_mem (hXM hy) huM
  · exact Subgroup.mul_mem _ (hTX (hXT hy)) (hNS huN)
  · rw [← mul_assoc, ← hxcy, mul_inv_cancel_left]

end CFSG.AGLEmbeddingD2.Tits.OrdinaryProofs

end
