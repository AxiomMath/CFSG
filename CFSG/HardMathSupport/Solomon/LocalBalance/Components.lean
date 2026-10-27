module

public import CFSG.HardMathSupport.Solomon.LocalBalance.Defs
public import CFSG.HardMathSupport.Solomon.LocalBalance.Prop21
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection1.CentralizerLemmas
public import CFSG.LocalAnalysis.GLTheoremB.ComponentTools
public import CFSG.LocalAnalysis.GLTheoremB.LayerTools

public section

namespace CFSG.HardMathSupport.Solomon.LocalBalance

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB

variable {G : Type*} [Group G]

theorem coprime_card_gLAPPrimeCore_aux (p : ℕ) (H : Type*) [Group H] [Finite H] :
    Nat.Coprime p (Nat.card (GLAPPrimeCore p H)) := by
  refine Nat.coprime_of_dvd fun q hq hqp hqd => ?_
  have hle : GLAPPrimeCore p H ≤ GLAPPrimeCore q H :=
    sSup_le_sSup fun N hN => ⟨hN.1, Nat.Coprime.coprime_dvd_left hqp hN.2⟩
  have h2 := CFSG.LocalAnalysis.ComponentInitial.ProjectivePlane.coprime_card_GLAPPrimeCore hq H
  exact hq.ne_one (h2.eq_one_of_dvd (hqd.trans (Subgroup.card_dvd_of_le hle)))

theorem glaPPrimeCoreOf_le_of_normal_aux [Finite G] (p : ℕ) {H M : Subgroup G} (hHM : H ≤ M)
    (hn : (H.subgroupOf M).Normal) : GLAPPrimeCoreOf p H ≤ GLAPPrimeCoreOf p M := by
  have hMH : M ≤ Subgroup.normalizer (H : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hHM).1 hn
  set O := GLAPPrimeCoreOf p H with hO
  have hOM : M ≤ Subgroup.normalizer (O : Set G) := by
    intro m hm
    have h1 := hMH hm
    rw [mem_normalizer_iff_gLBConj_eq] at h1 ⊢
    rw [hO, ← glaPPrimeCoreOf_gLBConj, h1]
  have hOH : O ≤ H := Subgroup.map_subtype_le _
  have hOn : (O.subgroupOf M).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer (hOH.trans hHM)).2 hOM
  have hcop : Nat.Coprime p (Nat.card (O.subgroupOf M)) := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (hOH.trans hHM)).toEquiv, hO,
      GLAPPrimeCoreOf, Subgroup.card_map_of_injective H.subtype_injective]
    exact coprime_card_gLAPPrimeCore_aux p H
  have hle : O.subgroupOf M ≤ GLAPPrimeCore p ↥M := le_sSup ⟨hOn, hcop⟩
  calc O = (O.subgroupOf M).map M.subtype :=
        (Subgroup.map_subgroupOf_eq_of_le (hOH.trans hHM)).symm
    _ ≤ GLAPPrimeCoreOf p M := Subgroup.map_mono hle

theorem glaPPrimeCoreOf_le_of_isSubnormal [Finite G] (p : ℕ) {L X : Subgroup G}
    (h : IsSubnormal L X) : GLAPPrimeCoreOf p L ≤ GLAPPrimeCoreOf p X := by
  induction h with
  | refl => exact le_rfl
  | step hHM hn _ ih => exact (glaPPrimeCoreOf_le_of_normal_aux p hHM hn).trans ih

section Unique

private theorem barX_monoAux (p : ℕ) {X S T : Subgroup G} (h : S ≤ T) :
    barX p X S ≤ barX p X T :=
  Subgroup.map_mono fun _ hx => (Subgroup.mem_subgroupOf).2 (h ((Subgroup.mem_subgroupOf).1 hx))

private theorem barX_le_gLBConjAux (p : ℕ) {C : Subgroup G} {j : G} (hj : j ∈ C)
    (T : Subgroup G) :
    barX p C (GLBConj j T) ≤
      GLBConj (QuotientGroup.mk' (GLAPPrimeCore p ↥C) ⟨j, hj⟩) (barX p C T) := by
  rintro _ ⟨c, hc, rfl⟩
  have hc' : (c : G) ∈ GLBConj j T := (Subgroup.mem_subgroupOf).1 hc
  rw [mem_gLBConj, ← map_inv, ← map_mul, ← map_mul]
  refine ⟨⟨j, hj⟩ * c * ⟨j, hj⟩⁻¹, ?_, rfl⟩
  show (⟨j, hj⟩ * c * ⟨j, hj⟩⁻¹ : ↥C) ∈ T.subgroupOf C
  rw [Subgroup.mem_subgroupOf]
  simpa using mem_gLBConj.1 hc'

private theorem isSubnormal_exists_normalAux {K A : Subgroup G} (h : IsSubnormal K A) (hne : K ≠ A) :
    ∃ M : Subgroup G, K ≤ M ∧ M ≤ A ∧ M ≠ A ∧ (M.subgroupOf A).Normal ∧ IsSubnormal K M := by
  induction h with
  | refl => exact absurd rfl hne
  | @step H M₁ A' hHM hn hM₁ ih =>
    by_cases hM : M₁ = A'
    · subst hM
      exact ⟨H, le_rfl, hHM, hne, hn, IsSubnormal.refl H⟩
    · obtain ⟨M₂, h1, h2, h3, h4, h5⟩ := ih hM
      exact ⟨M₂, hHM.trans h1, h2, h3, h4, IsSubnormal.step hHM hn h5⟩

private theorem commutator_le_of_leAux {X A B : Subgroup G} (hA : A ≤ X) (hB : B ≤ X) : ⁅A, B⁆ ≤ X :=
  Subgroup.commutator_le.2 fun _ ha _ hb =>
    X.mul_mem (X.mul_mem (X.mul_mem (hA ha) (hB hb)) (X.inv_mem (hA ha))) (X.inv_mem (hB hb))

private theorem subgroupOf_commutatorAux {X A B : Subgroup G} (hA : A ≤ X) (hB : B ≤ X) :
    (⁅A, B⁆).subgroupOf X = ⁅A.subgroupOf X, B.subgroupOf X⁆ := by
  apply Subgroup.map_injective X.subtype_injective
  rw [Subgroup.map_commutator, Subgroup.map_subgroupOf_eq_of_le hA,
    Subgroup.map_subgroupOf_eq_of_le hB, Subgroup.map_subgroupOf_eq_of_le
      (commutator_le_of_leAux hA hB)]

private theorem barX_commutatorAux (p : ℕ) {X A B : Subgroup G} (hA : A ≤ X) (hB : B ≤ X) :
    barX p X ⁅A, B⁆ = ⁅barX p X A, barX p X B⁆ := by
  unfold barX
  rw [subgroupOf_commutatorAux hA hB, Subgroup.map_commutator]

private theorem glaPComponent_perfectAux {p : ℕ} {X K : Subgroup G} (hK : GLAPComponent p X K) :
    ⁅K, K⁆ = K := by
  obtain ⟨hKX, hsn, hcomp, hmin⟩ := hK
  have hJK : ⁅K, K⁆ ≤ K := commutator_le_of_leAux le_rfl le_rfl
  by_contra hne
  have hlt : ⁅K, K⁆ < K := lt_of_le_of_ne hJK hne
  have hnorm : (⁅K, K⁆.subgroupOf K).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hJK).2
      (Subgroup.le_normalizer_iff_commutator_le_left.2 (Subgroup.commutator_mono hJK le_rfl))
  have hperf : ⁅barX p X K, barX p X K⁆ = barX p X K := Subgroup.isPerfect_iff.1 ⟨hcomp.2.2.1⟩
  exact hmin _ hlt (IsSubnormal.step hJK hnorm hsn)
    (by show barX p X ⁅K, K⁆ = barX p X K
        rw [barX_commutatorAux p hKX hKX, hperf])

private def preimBarXAux (p : ℕ) (X K : Subgroup G) : Subgroup G :=
  ((barX p X K).comap (QuotientGroup.mk' (GLAPPrimeCore p ↥X))).map X.subtype

private theorem preimBarX_leAux (p : ℕ) (X K : Subgroup G) : preimBarXAux p X K ≤ X :=
  Subgroup.map_subtype_le _

private theorem le_preimBarXAux (p : ℕ) {X K : Subgroup G} (hK : K ≤ X) : K ≤ preimBarXAux p X K := by
  intro k hk
  exact ⟨⟨k, hK hk⟩, ⟨⟨k, hK hk⟩, (Subgroup.mem_subgroupOf).2 hk, rfl⟩, rfl⟩

private theorem exists_mul_of_mem_preimBarXAux (p : ℕ) {X K : Subgroup G} {y : G}
    (hy : y ∈ preimBarXAux p X K) : ∃ k ∈ K, k⁻¹ * y ∈ GLAPPrimeCoreOf p X := by
  obtain ⟨y', ⟨k', hk', hky⟩, rfl⟩ := hy
  have hk : (k' : G) ∈ K := (Subgroup.mem_subgroupOf).1 hk'
  refine ⟨k', hk, ⟨k'⁻¹ * y', ?_, by simp⟩⟩
  exact (QuotientGroup.eq).1 hky

private theorem isSubnormal_preimBarXAux (p : ℕ) {X K : Subgroup G}
    (h : IsSubnormal (barX p X K) ⊤) : IsSubnormal (preimBarXAux p X K) X := by
  have h1 := CFSG.LocalAnalysis.GLTheoremB.isSubnormal_map' X.subtype
    (CFSG.LocalAnalysis.GLTheoremB.isSubnormal_comap' (QuotientGroup.mk' (GLAPPrimeCore p ↥X)) h)
  rwa [Subgroup.comap_top, Subgroup.map_top, Subgroup.range_subtype] at h1

private theorem barX_gLBConj_of_memAux (p : ℕ) {X : Subgroup G} {n : G} (hn : n ∈ GLAPPrimeCoreOf p X)
    (K : Subgroup G) : barX p X (GLBConj n K) = barX p X K := by
  obtain ⟨n', hn', rfl⟩ := hn
  have h1 : QuotientGroup.mk' (GLAPPrimeCore p ↥X) n' = 1 := (QuotientGroup.eq_one_iff n').2 hn'
  have hX : (n' : G) ∈ X := n'.2
  refine le_antisymm ?_ ?_
  · refine (barX_le_gLBConjAux p hX K).trans ?_
    have : QuotientGroup.mk' (GLAPPrimeCore p ↥X) ⟨(n' : G), hX⟩ = 1 := h1
    rw [this, gLBConj_one]
  · have hinv : ((n' : G)⁻¹) ∈ X := X.inv_mem hX
    have h3 := barX_le_gLBConjAux p hinv (GLBConj (n' : G) K)
    simp only [Subgroup.coe_subtype] at h3 ⊢
    rw [gLBConj_inv_gLBConj] at h3
    refine h3.trans ?_
    have h2 : QuotientGroup.mk' (GLAPPrimeCore p ↥X) ⟨(n' : G)⁻¹, hinv⟩ = 1 := by
      have : (⟨(n' : G)⁻¹, hinv⟩ : ↥X) = n'⁻¹ := rfl
      rw [this, map_inv, h1, inv_one]
    rw [h2, gLBConj_one]

private theorem barX_perfect_of_glaPComponentAux {p : ℕ} {X K : Subgroup G} (hK : GLAPComponent p X K) :
    ⁅barX p X K, barX p X K⁆ = barX p X K :=
  Subgroup.isPerfect_iff.1 ⟨hK.2.2.1.2.2.1⟩

variable [Finite G]

private theorem card_lt_of_ltAux {M A : Subgroup G} (h : M < A) : Nat.card M < Nat.card A :=
  lt_of_le_of_ne (Subgroup.card_le_of_le h.le) fun heq =>
    h.ne (Subgroup.eq_of_le_of_card_ge h.le heq.ge)

private theorem glaPComponent_normal_auxAux {p : ℕ} {X K : Subgroup G} (hK : GLAPComponent p X K) :
    ∀ (n : ℕ) (A : Subgroup G), Nat.card A = n → K ≤ A → A ≤ preimBarXAux p X K →
      IsSubnormal A X → IsSubnormal K A → (K.subgroupOf A).Normal := by
  have hperf := barX_perfect_of_glaPComponentAux hK
  obtain ⟨hKX, hsn, hcomp, hmin⟩ := hK
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro A hA hKA hAP hAX hKAsn
  by_cases hKeq : K = A
  · subst hKeq
    rw [Subgroup.subgroupOf_self]
    infer_instance
  · obtain ⟨M, hKM, hMA, hMne, hMn, hKMsn⟩ := isSubnormal_exists_normalAux hKAsn hKeq
    have hMlt : M < A := lt_of_le_of_ne hMA hMne
    have hMX : IsSubnormal M X := IsSubnormal.step hMA hMn hAX
    have hKMn : (K.subgroupOf M).Normal :=
      ih (Nat.card M) (hA ▸ card_lt_of_ltAux hMlt) M rfl hKM (hMA.trans hAP) hMX hKMsn
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
      have hK'X : K' ≤ X := hK'M.trans (hMA.trans (hAP.trans (preimBarX_leAux p X K)))
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
      have hbarK' : barX p X K' = barX p X K := barX_gLBConj_of_memAux p hyN K
      have hbar : barX p X K ≤ barX p X (K ⊓ K') := by
        have h1 := barX_monoAux (X := X) p hcomm
        rw [barX_commutatorAux p hKX hK'X, hbarK', hperf] at h1
        exact h1
      have hKK' : K ≤ K' := by
        by_cases hJK : K ⊓ K' = K
        · exact hJK ▸ inf_le_right
        · exfalso
          have hlt : K ⊓ K' < K := lt_of_le_of_ne inf_le_left hJK
          exact hmin _ hlt hJX (le_antisymm (barX_monoAux p inf_le_left) hbar)
      have hcard : Nat.card K' ≤ Nat.card K := by
        have : Nat.card K' = Nat.card K := by
          rw [hK']
          unfold GLBConj
          exact Subgroup.card_map_of_injective (MulAut.conj y⁻¹).injective
        exact this.le
      exact mem_normalizer_iff_gLBConj_eq.2 (Subgroup.eq_of_le_of_card_ge hKK' hcard).symm
    have hAK : A ≤ Subgroup.normalizer (K : Set G) := by
      intro a ha
      obtain ⟨k, hk, hkn⟩ := exists_mul_of_mem_preimBarXAux p (hAP ha)
      have hkA : k ∈ A := hKA hk
      have hy : k⁻¹ * a ∈ Subgroup.normalizer (K : Set G) :=
        hN _ (A.mul_mem (A.inv_mem hkA) ha) hkn
      have : a = k * (k⁻¹ * a) := by simp
      rw [this]
      exact Subgroup.mul_mem _ (Subgroup.le_normalizer hk) hy
    exact (Subgroup.normal_subgroupOf_iff_le_normalizer hKA).2 hAK

private theorem glaPComponent_normal_preimBarXAux {p : ℕ} {X K : Subgroup G} (hK : GLAPComponent p X K) :
    (K.subgroupOf (preimBarXAux p X K)).Normal :=
  glaPComponent_normal_auxAux hK _ _ rfl (le_preimBarXAux p hK.1) le_rfl
    (isSubnormal_preimBarXAux p hK.2.2.1.2.1)
    (isSubnormal_of_le_of_le hK.2.1 (le_preimBarXAux p hK.1) (preimBarX_leAux p X K))

theorem glaPComponent_uniqueAux {p : ℕ} {X K₁ K₂ : Subgroup G} (h₁ : GLAPComponent p X K₁)
    (h₂ : GLAPComponent p X K₂) (h : barX p X K₁ = barX p X K₂) : K₁ = K₂ := by
  have hP2 : preimBarXAux p X K₂ = preimBarXAux p X K₁ := by
    unfold preimBarXAux
    rw [h]
  have hK₁P : K₁ ≤ preimBarXAux p X K₁ := le_preimBarXAux p h₁.1
  have hK₂P : K₂ ≤ preimBarXAux p X K₁ := hP2 ▸ le_preimBarXAux p h₂.1
  have hn₁ : (K₁.subgroupOf (preimBarXAux p X K₁)).Normal := glaPComponent_normal_preimBarXAux h₁
  have hn₂ : (K₂.subgroupOf (preimBarXAux p X K₁)).Normal :=
    hP2 ▸ glaPComponent_normal_preimBarXAux h₂
  have hN₁ : preimBarXAux p X K₁ ≤ Subgroup.normalizer (K₁ : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hK₁P).1 hn₁
  have hN₂ : preimBarXAux p X K₁ ≤ Subgroup.normalizer (K₂ : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hK₂P).1 hn₂
  have hPX : IsSubnormal (preimBarXAux p X K₁) X := isSubnormal_preimBarXAux p h₁.2.2.1.2.1
  have hJn : ((K₁ ⊓ K₂).subgroupOf (preimBarXAux p X K₁)).Normal := by
    have : (K₁ ⊓ K₂).subgroupOf (preimBarXAux p X K₁) =
        K₁.subgroupOf (preimBarXAux p X K₁) ⊓ K₂.subgroupOf (preimBarXAux p X K₁) := by
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
    have h1 := barX_monoAux (X := X) p hcomm
    rw [barX_commutatorAux p h₁.1 h₂.1, ← h, barX_perfect_of_glaPComponentAux h₁] at h1
    exact h1
  have e1 : K₁ ⊓ K₂ = K₁ := by
    by_contra hne
    exact h₁.2.2.2 _ (lt_of_le_of_ne inf_le_left hne) hJX
      (le_antisymm (barX_monoAux p inf_le_left) hbar)
  have e2 : K₁ ⊓ K₂ = K₂ := by
    by_contra hne
    refine h₂.2.2.2 _ (lt_of_le_of_ne inf_le_right hne) hJX ?_
    show barX p X (K₁ ⊓ K₂) = barX p X K₂
    rw [← h]
    exact le_antisymm (barX_monoAux p inf_le_left) hbar
  rw [← e1, e2]

end Unique

theorem mem_pCore_of_forall_comm_aux {p : ℕ} (hp : p.Prime) {H : Type*} [Group H]
    [Finite H] {z : H ⧸ GLAPPrimeCore p H} (hz : ∀ w, w * z = z * w) :
    z ∈ CFSG.pCore p (H ⧸ GLAPPrimeCore p H) := by
  have := Fact.mk hp
  have hbot : GLAPPrimeCore p (H ⧸ GLAPPrimeCore p H) = ⊥ :=
    CFSG.pPrimeCore_quotient_pPrimeCore_eq_bot p
  have hnorm : ∀ u : H ⧸ GLAPPrimeCore p H, (∀ w, w * u = u * w) →
      (Subgroup.zpowers u).Normal := by
    intro u hu
    refine ⟨fun n hn g => ?_⟩
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hn
    have : g * u ^ k = u ^ k * g := (Commute.zpow_right (hu g) k).eq
    rw [this, mul_inv_cancel_right]
    exact Subgroup.zpow_mem _ (Subgroup.mem_zpowers u) k
  obtain ⟨e, m, hm, hord⟩ := Nat.exists_eq_pow_mul_and_not_dvd (orderOf_pos z).ne' p hp.ne_one
  have hwcen : ∀ w, w * z ^ p ^ e = z ^ p ^ e * w := fun w =>
    (Commute.pow_right (hz w) (p ^ e)).eq
  have hordw : orderOf (z ^ p ^ e) = m := by
    rw [orderOf_pow_of_dvd (pow_ne_zero _ hp.ne_zero) (hord ▸ dvd_mul_right _ _), hord,
      Nat.mul_div_cancel_left _ (pow_pos hp.pos _)]
  have hcop : Nat.Coprime p (Nat.card (Subgroup.zpowers (z ^ p ^ e))) := by
    rw [Nat.card_zpowers, hordw]
    exact (hp.coprime_iff_not_dvd).2 hm
  have hw1 : Subgroup.zpowers (z ^ p ^ e) = ⊥ := by
    refine (CFSG.pPrimeCore_eq_bot_iff.1 hbot) _ (hnorm _ hwcen) hcop
  have hm1 : m = 1 := by
    rw [← hordw, orderOf_eq_one_iff]
    exact Subgroup.zpowers_eq_bot.1 hw1
  have hpg : IsPGroup p (Subgroup.zpowers z) := by
    refine IsPGroup.iff_card.2 ⟨e, ?_⟩
    rw [Nat.card_zpowers, hord, hm1, mul_one]
  exact le_sSup (show Subgroup.zpowers z ∈ {K : Subgroup (H ⧸ GLAPPrimeCore p H) |
    K.Normal ∧ IsPGroup p K} from ⟨hnorm z hz, hpg⟩) (Subgroup.mem_zpowers z)

theorem inf_le_oPrimePOf_of_ne [Finite G] {p : ℕ} (hp : p.Prime) {X L L' : Subgroup G}
    (hL : GLAPComponent p X L) (hL' : GLAPComponent p X L') (hne : L ≠ L') :
    L ⊓ L' ≤ oPrimePOf p L := by
  intro y hy
  obtain ⟨hyL, hyL'⟩ := hy
  have hbar : barX p X L ≠ barX p X L' := fun h => hne (glaPComponent_uniqueAux hL hL' h)
  have hcomm : ⁅barX p X L, barX p X L'⁆ = ⊥ :=
    CFSG.ComponentClassification.LocalComponents.commute_of_ne _ _ hL.2.2.1 hL'.2.2.1 hbar
  have hcen := Subgroup.commutator_eq_bot_iff_le_centralizer.1 hcomm
  have key : ∀ ℓ ∈ L, ∀ u ∈ L ⊓ L', u⁻¹ * ℓ⁻¹ * u * ℓ ∈ GLAPPrimeCoreOf p L := by
    intro ℓ hℓ u hu
    have hℓX : ℓ ∈ X := hL.1 hℓ
    have huX : u ∈ X := hL.1 hu.1
    have hℓbar : QuotientGroup.mk' (GLAPPrimeCore p ↥X) ⟨ℓ, hℓX⟩ ∈ barX p X L :=
      ⟨⟨ℓ, hℓX⟩, (Subgroup.mem_subgroupOf).2 hℓ, rfl⟩
    have hubar : QuotientGroup.mk' (GLAPPrimeCore p ↥X) ⟨u, huX⟩ ∈ barX p X L' :=
      ⟨⟨u, huX⟩, (Subgroup.mem_subgroupOf).2 hu.2, rfl⟩
    have h1 := Subgroup.mem_centralizer_iff.1 (hcen hℓbar) _ hubar
    have hxX : u⁻¹ * ℓ⁻¹ * u * ℓ ∈ X :=
      X.mul_mem (X.mul_mem (X.mul_mem (X.inv_mem huX) (X.inv_mem hℓX)) huX) hℓX
    have hxN : u⁻¹ * ℓ⁻¹ * u * ℓ ∈ GLAPPrimeCoreOf p X := by
      refine ⟨⟨_, hxX⟩, (QuotientGroup.eq_one_iff _).1 ?_, rfl⟩
      have h2 : (⟨u⁻¹ * ℓ⁻¹ * u * ℓ, hxX⟩ : ↥X) = ⟨u, huX⟩⁻¹ * ⟨ℓ, hℓX⟩⁻¹ * ⟨u, huX⟩ * ⟨ℓ, hℓX⟩ :=
        rfl
      show QuotientGroup.mk' (GLAPPrimeCore p ↥X) _ = 1
      rw [h2, map_mul, map_mul, map_mul, map_inv, map_inv]
      set a := QuotientGroup.mk' (GLAPPrimeCore p ↥X) ⟨ℓ, hℓX⟩
      set b := QuotientGroup.mk' (GLAPPrimeCore p ↥X) ⟨u, huX⟩
      calc b⁻¹ * a⁻¹ * b * a = (a * b)⁻¹ * (b * a) := by group
        _ = 1 := by rw [← h1]; simp
    have hx := gLAPPrimeCoreOf_inf_le hp X L
    rw [inf_eq_right.2 hL.1] at hx
    exact hx ⟨hxN, L.mul_mem (L.mul_mem (L.mul_mem (L.inv_mem hu.1) (L.inv_mem hℓ)) hu.1) hℓ⟩
  refine ⟨⟨y, hyL⟩, ?_, rfl⟩
  show QuotientGroup.mk' (GLAPPrimeCore p ↥L) ⟨y, hyL⟩ ∈ CFSG.pCore p (↥L ⧸ GLAPPrimeCore p ↥L)
  refine mem_pCore_of_forall_comm_aux hp fun w => ?_
  obtain ⟨ℓ, rfl⟩ := QuotientGroup.mk'_surjective (GLAPPrimeCore p ↥L) w
  rw [← map_mul, ← map_mul, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq]
  have := key ℓ ℓ.2 y ⟨hyL, hyL'⟩
  refine (Subgroup.mem_map_iff_mem L.subtype_injective).1
    (?_ : L.subtype _ ∈ GLAPPrimeCoreOf p L)
  simpa [mul_assoc] using this

theorem glaPComponent_gLBConj [Finite G] {p : ℕ} {X L : Subgroup G} (g : G)
    (hL : GLAPComponent p X L) : GLAPComponent p (GLBConj g X) (GLBConj g L) :=
  CFSG.LocalAnalysis.GLTheoremB.glaPComponent_gLBConj hL g

theorem exists_three_conjugates {B L : Subgroup G} (hB : IsMulCommutative B)
    (h3 : (Subgroup.normalizer (L : Set G)).relIndex B = 3) :
    ∃ L₂ L₃ : Subgroup G, (∃ g ∈ B, L₂ = GLBConj g L) ∧ (∃ g ∈ B, L₃ = GLBConj g L) ∧
      L ≠ L₂ ∧ L ≠ L₃ ∧ L₂ ≠ L₃ ∧
      ∀ L' : Subgroup G, (∃ g ∈ B, L' = GLBConj g L) → L' = L ∨ L' = L₂ ∨ L' = L₃ := by
  classical
  set N : Subgroup B := (Subgroup.normalizer (L : Set G)).subgroupOf B with hN
  let F : B → Subgroup G := fun b => GLBConj (b : G) L
  have hF : ∀ a b : B, F a = F b ↔ a⁻¹ * b ∈ N := by
    intro a b
    have hcomm : ((a⁻¹ * b : B) : G) = (b : G) * (a : G)⁻¹ := by
      have := hB.is_comm.comm a⁻¹ b
      have h2 := congrArg Subtype.val this
      simpa using h2
    rw [hN, Subgroup.mem_subgroupOf, hcomm, mem_normalizer_iff_gLBConj_eq]
    constructor
    · intro h
      have h' : GLBConj (a : G) L = GLBConj (b : G) L := h
      rw [← gLBConj_gLBConj, ← h', gLBConj_inv_gLBConj]
    · intro h
      have h' : GLBConj (a : G)⁻¹ (GLBConj (b : G) L) = L := by
        rw [gLBConj_gLBConj, h]
      have h2 := congrArg (GLBConj (a : G)) h'
      rw [gLBConj_gLBConj_inv] at h2
      exact h2.symm
  have hcard : Nat.card (B ⧸ N) = 3 := by
    rw [← Subgroup.index_eq_card]
    exact h3
  let f : B ⧸ N → Subgroup G :=
    Quotient.lift F (fun a b hab => (hF a b).2 (QuotientGroup.leftRel_apply.1 hab))
  have hf : ∀ b : B, f (b : B ⧸ N) = GLBConj (b : G) L := fun b => rfl
  have hinj : Function.Injective f := by
    intro x y hxy
    induction x using QuotientGroup.induction_on with | _ a => ?_
    induction y using QuotientGroup.induction_on with | _ b => ?_
    exact QuotientGroup.eq.2 ((hF a b).1 hxy)
  have : Finite (B ⧸ N) := Nat.finite_of_card_ne_zero (by rw [hcard]; norm_num)
  let _ : Fintype (B ⧸ N) := Fintype.ofFinite _
  have hcard2 : (Finset.univ.erase (1 : B ⧸ N)).card = 2 := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ,
      ← Nat.card_eq_fintype_card, hcard]
  obtain ⟨x, y, hxy, hs⟩ := Finset.card_eq_two.1 hcard2
  have hcases : ∀ t : B ⧸ N, t = 1 ∨ t = x ∨ t = y := by
    intro t
    by_cases ht : t = 1
    · exact Or.inl ht
    · have : t ∈ Finset.univ.erase (1 : B ⧸ N) := Finset.mem_erase.2 ⟨ht, Finset.mem_univ _⟩
      rw [hs] at this
      simp only [Finset.mem_insert, Finset.mem_singleton] at this
      exact Or.inr this
  have hx1 : x ≠ 1 := fun h => by
    have : x ∈ Finset.univ.erase (1 : B ⧸ N) := by rw [hs]; simp
    exact (Finset.mem_erase.1 this).1 h
  have hy1 : y ≠ 1 := fun h => by
    have : y ∈ Finset.univ.erase (1 : B ⧸ N) := by rw [hs]; simp
    exact (Finset.mem_erase.1 this).1 h
  obtain ⟨bx, rfl⟩ := QuotientGroup.mk_surjective x
  obtain ⟨by', rfl⟩ := QuotientGroup.mk_surjective y
  have h1 : f (1 : B ⧸ N) = L := by
    have := hf 1
    rw [show ((1 : B) : B ⧸ N) = 1 from rfl] at this
    rw [this]
    exact gLBConj_one L
  refine ⟨GLBConj (bx : G) L, GLBConj (by' : G) L, ⟨bx, bx.2, rfl⟩, ⟨by', by'.2, rfl⟩, ?_, ?_, ?_,
    ?_⟩
  · intro h
    exact hx1 (hinj (by rw [hf, ← h, h1]))
  · intro h
    exact hy1 (hinj (by rw [hf, ← h, h1]))
  · intro h
    exact hxy (hinj (by rw [hf, hf]; exact h))
  · rintro L' ⟨g, hg, rfl⟩
    have hg' := hf ⟨g, hg⟩
    rcases hcases ((⟨g, hg⟩ : B) : B ⧸ N) with h | h | h
    · rw [h] at hg'
      exact Or.inl (hg'.symm.trans h1)
    · rw [h] at hg'
      exact Or.inr (Or.inl (hg'.symm.trans (hf bx)))
    · rw [h] at hg'
      exact Or.inr (Or.inr (hg'.symm.trans (hf by')))

end CFSG.HardMathSupport.Solomon.LocalBalance
