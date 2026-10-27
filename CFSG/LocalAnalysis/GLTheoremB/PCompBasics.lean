module

public import CFSG.LocalAnalysis.GLTheoremB.Lemma911Tools
public import CFSG.LocalAnalysis.GLTheoremB.Prop98Proof
public import CFSG.LocalAnalysis.GLTheoremB.LayerTools

public section

namespace CFSG.LocalAnalysis.GLTheoremB

open CFSG.Open

section Subnormal

variable {G : Type*} [Group G]

theorem isSubnormal_le' {K A : Subgroup G} (h : IsSubnormal K A) : K ≤ A :=
  h.le

theorem isSubnormal_exists_normal {K A : Subgroup G} (h : IsSubnormal K A) (hne : K ≠ A) :
    ∃ M : Subgroup G, K ≤ M ∧ M ≤ A ∧ M ≠ A ∧ (M.subgroupOf A).Normal ∧ IsSubnormal K M := by
  induction h with
  | refl => exact absurd rfl hne
  | @step H M₁ A' hHM hn hM₁ ih =>
    by_cases hM : M₁ = A'
    · subst hM
      exact ⟨H, le_rfl, hHM, hne, hn, IsSubnormal.refl H⟩
    · obtain ⟨M₂, h1, h2, h3, h4, h5⟩ := ih hM
      exact ⟨M₂, hHM.trans h1, h2, h3, h4, IsSubnormal.step hHM hn h5⟩

end Subnormal

section PPrimeCore

variable {G : Type*} [Group G] [Finite G]

theorem glaPPrimeCoreOf_inf_eq_of_isSubnormal {p : ℕ} (hp : p.Prime) {H A : Subgroup G}
    (h : IsSubnormal H A) : H ⊓ GLAPPrimeCoreOf p A = GLAPPrimeCoreOf p H := by
  have hHA : H ≤ A := isSubnormal_le' h
  refine le_antisymm ?_
    (le_inf (Subgroup.map_subtype_le _) (glaPPrimeCoreOf_le_of_isSubnormal hp h))
  set O := GLAPPrimeCoreOf p A with hO
  set N0 : Subgroup ↥H := O.subgroupOf H with hN0
  have hnorm : N0.Normal := by
    refine ⟨fun n hn h' => ?_⟩
    show ((h' * n * h'⁻¹ : ↥H) : G) ∈ O
    have := (Subgroup.mem_normalizer_iff.1
      (le_normalizer_glaPPrimeCoreOf p A (hHA h'.2)) (n : G)).1 hn
    simpa using this
  have hdvd : Nat.card N0 ∣ Nat.card O := by
    have h1 : N0.map H.subtype = H ⊓ O := by
      rw [hN0, ← Subgroup.inf_subgroupOf_right O H]
      rw [Subgroup.map_subgroupOf_eq_of_le (inf_le_right : O ⊓ H ≤ H)]
      exact inf_comm _ _
    have h2 : Nat.card (N0.map H.subtype) = Nat.card N0 :=
      Subgroup.card_map_of_injective H.subtype_injective
    rw [← h2, h1]
    exact Subgroup.card_dvd_of_le inf_le_right
  have hcop : Nat.Coprime p (Nat.card N0) :=
    (Nat.Prime.coprime_iff_not_dvd hp).2 fun hd =>
      not_dvd_card_glaPPrimeCoreOf hp A (hd.trans hdvd)
  have hle : N0 ≤ GLAPPrimeCore p ↥H := le_sSup ⟨hnorm, hcop⟩
  intro x hx
  exact ⟨⟨x, hx.1⟩, hle ((Subgroup.mem_subgroupOf).2 hx.2), rfl⟩

end PPrimeCore

section PComponent

variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
theorem commutator_le_of_le' {X A B : Subgroup G} (hA : A ≤ X) (hB : B ≤ X) : ⁅A, B⁆ ≤ X :=
  Subgroup.commutator_le.2 fun _ ha _ hb =>
    X.mul_mem (X.mul_mem (X.mul_mem (hA ha) (hB hb)) (X.inv_mem (hA ha))) (X.inv_mem (hB hb))

omit [Finite G] in
theorem subgroupOf_commutator {X A B : Subgroup G} (hA : A ≤ X) (hB : B ≤ X) :
    (⁅A, B⁆).subgroupOf X = ⁅A.subgroupOf X, B.subgroupOf X⁆ := by
  apply Subgroup.map_injective X.subtype_injective
  rw [Subgroup.map_commutator, Subgroup.map_subgroupOf_eq_of_le hA,
    Subgroup.map_subgroupOf_eq_of_le hB, Subgroup.map_subgroupOf_eq_of_le
      (commutator_le_of_le' hA hB)]

omit [Finite G] in
theorem barX_commutator (p : ℕ) {X A B : Subgroup G} (hA : A ≤ X) (hB : B ≤ X) :
    barX p X ⁅A, B⁆ = ⁅barX p X A, barX p X B⁆ := by
  unfold barX
  rw [subgroupOf_commutator hA hB, Subgroup.map_commutator]

omit [Finite G] in
theorem glaPComponent_perfect {p : ℕ} {X K : Subgroup G} (hK : GLAPComponent p X K) :
    ⁅K, K⁆ = K := by
  obtain ⟨hKX, hsn, hcomp, hmin⟩ := hK
  have hJK : ⁅K, K⁆ ≤ K := commutator_le_of_le' le_rfl le_rfl
  by_contra hne
  have hlt : ⁅K, K⁆ < K := lt_of_le_of_ne hJK hne
  have hnorm : (⁅K, K⁆.subgroupOf K).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hJK).2
      (Subgroup.le_normalizer_iff_commutator_le_left.2 (Subgroup.commutator_mono hJK le_rfl))
  have hperf : ⁅barX p X K, barX p X K⁆ = barX p X K := Subgroup.isPerfect_iff.1 ⟨hcomp.2.2.1⟩
  exact hmin _ hlt (IsSubnormal.step hJK hnorm hsn)
    (by show barX p X ⁅K, K⁆ = barX p X K
        rw [barX_commutator p hKX hKX, hperf])

end PComponent

section Preimage

variable {G : Type*} [Group G]

@[expose] def preimBarX (p : ℕ) (X K : Subgroup G) : Subgroup G :=
  ((barX p X K).comap (QuotientGroup.mk' (GLAPPrimeCore p ↥X))).map X.subtype

theorem preimBarX_le (p : ℕ) (X K : Subgroup G) : preimBarX p X K ≤ X :=
  Subgroup.map_subtype_le _

theorem le_preimBarX (p : ℕ) {X K : Subgroup G} (hK : K ≤ X) : K ≤ preimBarX p X K := by
  intro k hk
  exact ⟨⟨k, hK hk⟩, ⟨⟨k, hK hk⟩, (Subgroup.mem_subgroupOf).2 hk, rfl⟩, rfl⟩

theorem exists_mul_of_mem_preimBarX (p : ℕ) {X K : Subgroup G} {y : G}
    (hy : y ∈ preimBarX p X K) : ∃ k ∈ K, k⁻¹ * y ∈ GLAPPrimeCoreOf p X := by
  obtain ⟨y', ⟨k', hk', hky⟩, rfl⟩ := hy
  have hk : (k' : G) ∈ K := (Subgroup.mem_subgroupOf).1 hk'
  refine ⟨k', hk, ⟨k'⁻¹ * y', ?_, by simp⟩⟩
  exact (QuotientGroup.eq).1 hky

theorem isSubnormal_preimBarX (p : ℕ) {X K : Subgroup G}
    (h : IsSubnormal (barX p X K) ⊤) : IsSubnormal (preimBarX p X K) X :=
  isSubnormal_preimage_barX p h

theorem barX_gLBConj_of_mem (p : ℕ) {X : Subgroup G} {n : G} (hn : n ∈ GLAPPrimeCoreOf p X)
    (K : Subgroup G) : barX p X (GLBConj n K) = barX p X K := by
  obtain ⟨n', hn', rfl⟩ := hn
  have h1 : QuotientGroup.mk' (GLAPPrimeCore p ↥X) n' = 1 := (QuotientGroup.eq_one_iff n').2 hn'
  have hX : (n' : G) ∈ X := n'.2
  refine le_antisymm ?_ ?_
  · refine (barX_le_gLBConj p hX K).trans ?_
    have : QuotientGroup.mk' (GLAPPrimeCore p ↥X) ⟨(n' : G), hX⟩ = 1 := h1
    rw [this, gLBConj_one]
  · have hinv : ((n' : G)⁻¹) ∈ X := X.inv_mem hX
    have h3 := barX_le_gLBConj p hinv (GLBConj (n' : G) K)
    simp only [Subgroup.coe_subtype] at h3 ⊢
    rw [gLBConj_inv_gLBConj] at h3
    refine h3.trans ?_
    have h2 : QuotientGroup.mk' (GLAPPrimeCore p ↥X) ⟨(n' : G)⁻¹, hinv⟩ = 1 := by
      have : (⟨(n' : G)⁻¹, hinv⟩ : ↥X) = n'⁻¹ := rfl
      rw [this, map_inv, h1, inv_one]
    rw [h2, gLBConj_one]

end Preimage

section Unique

variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
theorem barX_perfect_of_glaPComponent {p : ℕ} {X K : Subgroup G} (hK : GLAPComponent p X K) :
    ⁅barX p X K, barX p X K⁆ = barX p X K :=
  Subgroup.isPerfect_iff.1 ⟨hK.2.2.1.2.2.1⟩

theorem card_lt_of_lt' {M A : Subgroup G} (h : M < A) : Nat.card M < Nat.card A :=
  lt_of_le_of_ne (Subgroup.card_le_of_le h.le) fun heq =>
    h.ne (Subgroup.eq_of_le_of_card_ge h.le heq.ge)

theorem glaPComponent_normal_aux {p : ℕ} {X K : Subgroup G} (hK : GLAPComponent p X K) :
    ∀ (n : ℕ) (A : Subgroup G), Nat.card A = n → K ≤ A → A ≤ preimBarX p X K →
      IsSubnormal A X → IsSubnormal K A → (K.subgroupOf A).Normal := by
  have hperf := barX_perfect_of_glaPComponent hK
  obtain ⟨hKX, hsn, hcomp, hmin⟩ := hK
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro A hA hKA hAP hAX hKAsn
  by_cases hKeq : K = A
  · subst hKeq
    rw [Subgroup.subgroupOf_self]
    infer_instance
  · obtain ⟨M, hKM, hMA, hMne, hMn, hKMsn⟩ := isSubnormal_exists_normal hKAsn hKeq
    have hMlt : M < A := lt_of_le_of_ne hMA hMne
    have hMX : IsSubnormal M X := IsSubnormal.step hMA hMn hAX
    have hKMn : (K.subgroupOf M).Normal :=
      ih (Nat.card M) (hA ▸ card_lt_of_lt' hMlt) M rfl hKM (hMA.trans hAP) hMX hKMsn
    have hMK : M ≤ Subgroup.normalizer (K : Set G) :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer hKM).1 hKMn
    have hN : ∀ y ∈ A, y ∈ GLAPPrimeCoreOf p X → y ∈ Subgroup.normalizer (K : Set G) := by
      intro y hyA hyN
      have hyM : y ∈ Subgroup.normalizer (M : Set G) :=
        (Subgroup.normal_subgroupOf_iff_le_normalizer hMA).1 hMn hyA
      have hyM' : ∀ m ∈ M, y * m * y⁻¹ ∈ M := fun m hm =>
        (Subgroup.mem_normalizer_iff.1 hyM m).1 hm
      set K' := GLBConj y K with hK'
      have hK'M : K' ≤ M := by
        intro z hz
        have h2 : y * z * y⁻¹ ∈ M := hKM (mem_gLBConj.1 hz)
        have := (Subgroup.mem_normalizer_iff.1 (Subgroup.inv_mem _ hyM) (y * z * y⁻¹)).1 h2
        simpa [mul_assoc] using this
      have hMK' : M ≤ Subgroup.normalizer (K' : Set G) := by
        intro m hm
        rw [hK', normalizer_gLBConj, mem_gLBConj]
        exact hMK (hyM' m hm)
      have hK'X : K' ≤ X := hK'M.trans (hMA.trans (hAP.trans (preimBarX_le p X K)))
      have hcomm : ⁅K, K'⁆ ≤ K ⊓ K' := by
        refine Subgroup.commutator_le.2 fun a ha b hb => ⟨?_, ?_⟩
        · have h1 := (Subgroup.mem_normalizer_iff.1 (hMK (hK'M hb)) a⁻¹).1 (K.inv_mem ha)
          have : a * (b * a⁻¹ * b⁻¹) ∈ K := K.mul_mem ha h1
          simpa [commutatorElement_def, mul_assoc] using this
        · have h1 := (Subgroup.mem_normalizer_iff.1 (hMK' (hKM ha)) b⁻¹).1 (K'.inv_mem hb)
          have : (a * b * a⁻¹) * b⁻¹ ∈ K' := by
            have := (Subgroup.mem_normalizer_iff.1 (hMK' (hKM ha)) b).1 hb
            exact K'.mul_mem this (K'.inv_mem hb)
          simpa [commutatorElement_def, mul_assoc] using this
      have hJn : ((K ⊓ K').subgroupOf M).Normal := by
        refine (Subgroup.normal_subgroupOf_iff_le_normalizer (inf_le_left.trans hKM)).2 ?_
        intro m hm
        rw [Subgroup.mem_normalizer_iff]
        intro z
        have h1 := Subgroup.mem_normalizer_iff.1 (hMK hm) z
        have h2 := Subgroup.mem_normalizer_iff.1 (hMK' hm) z
        simp only [Subgroup.mem_inf]
        rw [h1, h2]
      have hJX : IsSubnormal (K ⊓ K') X :=
        IsSubnormal.step (inf_le_left.trans hKM) hJn hMX
      have hbarK' : barX p X K' = barX p X K := barX_gLBConj_of_mem p hyN K
      have hbar : barX p X K ≤ barX p X (K ⊓ K') := by
        have h1 := barX_mono (X := X) p hcomm
        rw [barX_commutator p hKX hK'X, hbarK', hperf] at h1
        exact h1
      have hKK' : K ≤ K' := by
        by_cases hJK : K ⊓ K' = K
        · exact hJK ▸ inf_le_right
        · exfalso
          have hlt : K ⊓ K' < K := lt_of_le_of_ne inf_le_left hJK
          exact hmin _ hlt hJX (le_antisymm (barX_mono p inf_le_left) hbar)
      have hcard : Nat.card K' ≤ Nat.card K := by
        have : Nat.card K' = Nat.card K := by
          rw [hK']
          unfold GLBConj
          exact Subgroup.card_map_of_injective (MulAut.conj y⁻¹).injective
        exact this.le
      exact mem_normalizer_iff_gLBConj_eq.2 (Subgroup.eq_of_le_of_card_ge hKK' hcard).symm
    have hAK : A ≤ Subgroup.normalizer (K : Set G) := by
      intro a ha
      obtain ⟨k, hk, hkn⟩ := exists_mul_of_mem_preimBarX p (hAP ha)
      have hkA : k ∈ A := hKA hk
      have hy : k⁻¹ * a ∈ Subgroup.normalizer (K : Set G) :=
        hN _ (A.mul_mem (A.inv_mem hkA) ha) hkn
      have : a = k * (k⁻¹ * a) := by simp
      rw [this]
      exact Subgroup.mul_mem _ (Subgroup.le_normalizer hk) hy
    exact (Subgroup.normal_subgroupOf_iff_le_normalizer hKA).2 hAK

theorem glaPComponent_normal_preimBarX {p : ℕ} {X K : Subgroup G} (hK : GLAPComponent p X K) :
    (K.subgroupOf (preimBarX p X K)).Normal :=
  glaPComponent_normal_aux hK _ _ rfl (le_preimBarX p hK.1) le_rfl
    (isSubnormal_preimBarX p hK.2.2.1.2.1)
    (isSubnormal_of_le_of_le hK.2.1 (le_preimBarX p hK.1) (preimBarX_le p X K))

theorem glaPComponent_unique {p : ℕ} {X K₁ K₂ : Subgroup G} (h₁ : GLAPComponent p X K₁)
    (h₂ : GLAPComponent p X K₂) (h : barX p X K₁ = barX p X K₂) : K₁ = K₂ := by
  have hP2 : preimBarX p X K₂ = preimBarX p X K₁ := by
    unfold preimBarX
    rw [h]
  have hK₁P : K₁ ≤ preimBarX p X K₁ := le_preimBarX p h₁.1
  have hK₂P : K₂ ≤ preimBarX p X K₁ := hP2 ▸ le_preimBarX p h₂.1
  have hn₁ : (K₁.subgroupOf (preimBarX p X K₁)).Normal := glaPComponent_normal_preimBarX h₁
  have hn₂ : (K₂.subgroupOf (preimBarX p X K₁)).Normal :=
    hP2 ▸ glaPComponent_normal_preimBarX h₂
  have hN₁ : preimBarX p X K₁ ≤ Subgroup.normalizer (K₁ : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hK₁P).1 hn₁
  have hN₂ : preimBarX p X K₁ ≤ Subgroup.normalizer (K₂ : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hK₂P).1 hn₂
  have hPX : IsSubnormal (preimBarX p X K₁) X := isSubnormal_preimBarX p h₁.2.2.1.2.1
  have hJn : ((K₁ ⊓ K₂).subgroupOf (preimBarX p X K₁)).Normal := by
    have : (K₁ ⊓ K₂).subgroupOf (preimBarX p X K₁) =
        K₁.subgroupOf (preimBarX p X K₁) ⊓ K₂.subgroupOf (preimBarX p X K₁) := by
      ext x
      simp [Subgroup.mem_subgroupOf]
    rw [this]
    infer_instance
  have hJX : IsSubnormal (K₁ ⊓ K₂) X :=
    IsSubnormal.step (inf_le_left.trans hK₁P) hJn hPX
  have hcomm : ⁅K₁, K₂⁆ ≤ K₁ ⊓ K₂ := by
    refine Subgroup.commutator_le.2 fun a ha b hb => ⟨?_, ?_⟩
    · have h1 := (Subgroup.mem_normalizer_iff.1 (hN₁ (hK₂P hb)) a⁻¹).1 (K₁.inv_mem ha)
      have : a * (b * a⁻¹ * b⁻¹) ∈ K₁ := K₁.mul_mem ha h1
      simpa [commutatorElement_def, mul_assoc] using this
    · have h1 := (Subgroup.mem_normalizer_iff.1 (hN₂ (hK₁P ha)) b).1 hb
      have : (a * b * a⁻¹) * b⁻¹ ∈ K₂ := K₂.mul_mem h1 (K₂.inv_mem hb)
      simpa [commutatorElement_def, mul_assoc] using this
  have hbar : barX p X K₁ ≤ barX p X (K₁ ⊓ K₂) := by
    have h1 := barX_mono (X := X) p hcomm
    rw [barX_commutator p h₁.1 h₂.1, ← h, barX_perfect_of_glaPComponent h₁] at h1
    exact h1
  have e1 : K₁ ⊓ K₂ = K₁ := by
    by_contra hne
    exact h₁.2.2.2 _ (lt_of_le_of_ne inf_le_left hne) hJX
      (le_antisymm (barX_mono p inf_le_left) hbar)
  have e2 : K₁ ⊓ K₂ = K₂ := by
    by_contra hne
    refine h₂.2.2.2 _ (lt_of_le_of_ne inf_le_right hne) hJX ?_
    show barX p X (K₁ ⊓ K₂) = barX p X K₂
    rw [← h]
    exact le_antisymm (barX_mono p inf_le_left) hbar
  rw [← e1, e2]

omit [Finite G] in
theorem barX_self (p : ℕ) (X : Subgroup G) : barX p X X = ⊤ := by
  unfold barX
  rw [Subgroup.subgroupOf_self, Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective _)]

omit [Finite G] in
theorem barX_le_of_forall {p : ℕ} {X J K : Subgroup G} (hJX : J ≤ X)
    (h : ∀ k ∈ K, ∃ j ∈ J, j⁻¹ * k ∈ GLAPPrimeCoreOf p X) :
    barX p X K ≤ barX p X J := by
  rintro _ ⟨k, hk, rfl⟩
  obtain ⟨j, hj, z, hz, hzeq⟩ := h (k : G) ((Subgroup.mem_subgroupOf).1 hk)
  refine ⟨⟨j, hJX hj⟩, (Subgroup.mem_subgroupOf).2 hj, ?_⟩
  have : (⟨j, hJX hj⟩ : ↥X)⁻¹ * k = z := Subtype.ext (by simpa using hzeq.symm)
  exact (QuotientGroup.eq).2 (this ▸ hz)

omit [Finite G] in
theorem exists_of_barX_le {p : ℕ} {X J K : Subgroup G} (hle : barX p X K ≤ barX p X J) {k : G}
    (hk : k ∈ K) (hkX : k ∈ X) : ∃ j ∈ J, j⁻¹ * k ∈ GLAPPrimeCoreOf p X := by
  have h : QuotientGroup.mk' (GLAPPrimeCore p ↥X) ⟨k, hkX⟩ ∈ barX p X J :=
    hle ⟨⟨k, hkX⟩, (Subgroup.mem_subgroupOf).2 hk, rfl⟩
  obtain ⟨j', hj', hjk⟩ := h
  refine ⟨j', (Subgroup.mem_subgroupOf).1 hj', ?_⟩
  exact ⟨_, (QuotientGroup.eq).1 hjk, by simp⟩

theorem glaPComponent_of_le {p : ℕ} (hp : p.Prime) {A H K : Subgroup G}
    (hK : GLAPComponent p A K) (hKH : K ≤ H) (hHA : H ≤ A) : GLAPComponent p H K := by
  obtain ⟨hKA, hsn, hcomp, hmin⟩ := hK
  have hsnH : IsSubnormal K H := isSubnormal_of_le_of_le hsn hKH hHA
  refine ⟨hKH, hsnH, ⟨le_top, ?_, ?_⟩, ?_⟩
  · have := isSubnormal_barX (C := H) p hsnH
    rwa [barX_self] at this
  · have e : ↥(barX p H K) ≃* ↥(barX p A K) :=
      (quotEquivBarX hp hKH hsnH).symm.trans (quotEquivBarX hp hKA hsn)
    exact CFSG.SignalizerFunctorTheorem.TransportA.isQuasisimple_of_mulEquiv e.symm hcomp.2.2
  · intro J hJ hJsn heq
    have hJK : J ≤ K := hJ.le
    have hJsnA : IsSubnormal J A :=
      isSubnormal_trans' (isSubnormal_of_le_of_le hJsn hJK hKH) hsn
    have hcoreK : K ⊓ GLAPPrimeCoreOf p H ≤ GLAPPrimeCoreOf p A := by
      rw [glaPPrimeCoreOf_inf_eq_of_isSubnormal hp hsnH]
      exact glaPPrimeCoreOf_le_of_isSubnormal hp hsn
    refine hmin J hJ hJsnA ?_
    show barX p A J = barX p A K
    refine le_antisymm (barX_mono p hJK) ?_
    refine barX_le_of_forall (hJK.trans hKA) (fun k hk => ?_)
    obtain ⟨j, hj, hjk⟩ := exists_of_barX_le (X := H) (le_of_eq heq.symm) hk (hKH hk)
    exact ⟨j, hj, hcoreK ⟨K.mul_mem (K.inv_mem (hJK hj)) hk, hjk⟩⟩

end Unique

end CFSG.LocalAnalysis.GLTheoremB
