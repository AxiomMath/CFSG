module

public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec6FStmts
public import CFSG.LocalAnalysis.GLTheoremB.CentralizerLift
public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec6B67
public import CFSG.GroupTheory.LocalCores.Components

public section

namespace CFSG.HardMathSupport.Solomon.UniquenessMaximal

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.HardMathSupport.Solomon.Coordinator

section QuasisimpleComponents

variable {X : Type*} [Group X]

private theorem localCores_isQuasisimple {Q : Type*} [Group Q] (hQ : CFSG.Open.IsQuasisimple Q) :
    CFSG.IsQuasisimple Q :=
  ⟨⟨hQ.1⟩, hQ.2, ComponentClassification.Helpers.quasisimple_central_quotient_nonabelian Q hQ⟩

private theorem isSubnormal_eq_or_le_center {A B : Subgroup X} (h : IsSubnormal A B)
    (hB : CFSG.Open.IsQuasisimple B) : A = B ∨ A ≤ (Subgroup.center B).map B.subtype := by
  induction h with
  | refl A => exact Or.inl rfl
  | step hAM hn _ ih =>
    rename_i A M
    rcases ih hB with hMB | hM
    · subst hMB
      rcases CFSG.LocalCores.quasisimple_normal_subgroups (localCores_isQuasisimple hB) hn with
        h | h
      · exact Or.inl (le_antisymm hAM (Subgroup.subgroupOf_eq_top.mp h))
      · refine Or.inr fun x hx => ⟨⟨x, hAM hx⟩, h ?_, rfl⟩
        exact hx
    · exact Or.inr (hAM.trans hM)

private theorem not_isQuasisimple_of_le_comm {K A : Subgroup X} (hK : CFSG.Open.IsQuasisimple K)
    (hA : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a) (hKA : K ≤ A) : False := by
  have htop : Subgroup.center K = ⊤ := by
    rw [eq_top_iff]
    intro x _
    rw [Subgroup.mem_center_iff]
    intro y
    exact Subtype.ext (hA _ (hKA y.2) _ (hKA x.2))
  have := hK.2
  obtain ⟨a, b, hab⟩ := ComponentClassification.Helpers.quasisimple_central_quotient_nonabelian K hK
  apply hab
  have h1 : ∀ z : K ⧸ Subgroup.center K, z = 1 := by
    intro z
    obtain ⟨z, rfl⟩ := QuotientGroup.mk_surjective z
    rw [QuotientGroup.eq_one_iff, htop]
    trivial
  rw [h1 a, h1 b]

theorem isComponentOf_eq_of_isQuasisimple {K C : Subgroup X} (h : IsComponentOf K C)
    (hC : CFSG.Open.IsQuasisimple C) : K = C := by
  rcases isSubnormal_eq_or_le_center h.2.1 hC with h' | h'
  · exact h'
  · refine (not_isQuasisimple_of_le_comm h.2.2 (A := (Subgroup.center C).map C.subtype)
      ?_ h').elim
    rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    exact congrArg Subtype.val (Subgroup.mem_center_iff.mp ha b).symm

end QuasisimpleComponents

section Cover

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem mem_glaPPrimeCoreOf_iff {p : ℕ} {A : Subgroup G} {g : G} :
    g ∈ GLAPPrimeCoreOf p A ↔ ∃ h : g ∈ A, (⟨g, h⟩ : ↥A) ∈ GLAPPrimeCore p ↥A := by
  unfold GLAPPrimeCoreOf
  constructor
  · intro h
    obtain ⟨a, ha, rfl⟩ := Subgroup.mem_map.1 h
    exact ⟨a.2, ha⟩
  · rintro ⟨h, h'⟩
    exact Subgroup.mem_map.2 ⟨⟨g, h⟩, h', rfl⟩

omit [Finite G] in
theorem glaPPrimeCoreOf_le {p : ℕ} (A : Subgroup G) : GLAPPrimeCoreOf p A ≤ A := by
  intro g hg
  exact (mem_glaPPrimeCoreOf_iff.1 hg).1

theorem coprime_card_glaPPrimeCoreOf {p : ℕ} [Fact p.Prime] (A : Subgroup G) :
    Nat.Coprime p (Nat.card (GLAPPrimeCoreOf p A)) := by
  unfold GLAPPrimeCoreOf
  rw [Subgroup.card_map_of_injective A.subtype_injective]
  exact CFSG.pPrimeCore_coprime_card

omit [Finite G] in
theorem conj_mem_glaPPrimeCoreOf {p : ℕ} {A : Subgroup G} {a n : G} (ha : a ∈ A)
    (hn : n ∈ GLAPPrimeCoreOf p A) : a * n * a⁻¹ ∈ GLAPPrimeCoreOf p A := by
  obtain ⟨hnA, hn'⟩ := mem_glaPPrimeCoreOf_iff.1 hn
  refine mem_glaPPrimeCoreOf_iff.2 ⟨A.mul_mem (A.mul_mem ha hnA) (A.inv_mem ha), ?_⟩
  have := (GLAPPrimeCore.normal p ↥A).conj_mem _ hn' ⟨a, ha⟩
  exact this

omit [Finite G] in
theorem le_glaPPrimeCoreOf {p : ℕ} {A N : Subgroup G} (hNA : N ≤ A)
    (hn : ∀ a ∈ A, ∀ n ∈ N, a * n * a⁻¹ ∈ N) (hc : Nat.Coprime p (Nat.card N)) :
    N ≤ GLAPPrimeCoreOf p A := by
  have hnorm : (N.subgroupOf A).Normal := by
    refine ⟨fun n hn' a => ?_⟩
    exact hn a a.2 n hn'
  have hcard : Nat.card (N.subgroupOf A) = Nat.card N :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hNA).toEquiv
  have h1 : N.subgroupOf A ≤ GLAPPrimeCore p ↥A := le_sSup ⟨hnorm, hcard ▸ hc⟩
  have h2 := Subgroup.map_mono (f := A.subtype) h1
  rwa [Subgroup.map_subgroupOf_eq_of_le hNA] at h2

theorem exists_glaPComponent_of_isQuasisimple {p : ℕ} {C : Subgroup G}
    (hQ : CFSG.Open.IsQuasisimple (↥C ⧸ GLAPPrimeCore p ↥C)) :
    ∃ J : Subgroup G, GLAPComponent p C J ∧ barX p C J = ⊤ ∧
      ∀ J' : Subgroup G, GLAPComponent p C J' → J' = J := by
  classical
  have hQtop : CFSG.Open.IsQuasisimple ↥(⊤ : Subgroup (↥C ⧸ GLAPPrimeCore p ↥C)) :=
    CFSG.SignalizerFunctorTheorem.TransportA.isQuasisimple_of_mulEquiv Subgroup.topEquiv.symm hQ
  have hne : ∃ n : ℕ, ∃ L : Subgroup G, L ≤ C ∧ IsSubnormal L C ∧ barX p C L = ⊤ ∧
      Nat.card L = n := ⟨_, C, le_rfl, IsSubnormal.refl C, barX_self p C, rfl⟩
  obtain ⟨L, hLC, hLsn, hLtop, hLcard⟩ := Nat.find_spec hne
  have hmin : ∀ L' : Subgroup G, L' ≤ C → IsSubnormal L' C → barX p C L' = ⊤ →
      Nat.card L ≤ Nat.card L' := fun L' h1 h2 h3 => by
    rw [hLcard]
    exact Nat.find_min' hne ⟨L', h1, h2, h3, rfl⟩
  have hJ : GLAPComponent p C L := by
    refine ⟨hLC, hLsn, ?_, ?_⟩
    · show IsComponentOf (barX p C L) ⊤
      rw [hLtop]
      exact ⟨le_rfl, IsSubnormal.refl _, hQtop⟩
    · intro J hJ hJsn heq
      have hJC : J ≤ C := hJ.le.trans hLC
      have hJtop : barX p C J = ⊤ := heq.trans hLtop
      have := hmin J hJC hJsn hJtop
      have := card_lt_of_lt' hJ
      omega
  refine ⟨L, hJ, hLtop, fun J' hJ' => ?_⟩
  have hc : IsComponentOf (barX p C J') ⊤ := hJ'.2.2.1
  have hJ'top : barX p C J' = ⊤ :=
    isComponentOf_eq_of_isQuasisimple hc hQtop
  exact glaPComponent_unique hJ' hJ (hJ'top.trans hLtop.symm)

theorem exists_mul_mem_cover {K E : Subgroup G} (hE : IsPGroup 3 ↥E) (hED : E ≤ dQ K) {k : G}
    (hk : k ∈ K) :
    ∃ u ∈ GLAPPrimeCoreOf 3 K, k * u ∈ K ⊓ Subgroup.centralizer (E : Set G) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hUK := glaPPrimeCoreOf_le (p := 3) K
  have hnormU : ∀ a ∈ K, a ∈ Subgroup.normalizer (GLAPPrimeCoreOf 3 K : Set G) := fun a ha => by
    rw [Subgroup.mem_normalizer_iff]
    intro n
    constructor
    · exact fun hn => conj_mem_glaPPrimeCoreOf ha hn
    · intro hn
      have := conj_mem_glaPPrimeCoreOf (K.inv_mem ha) hn
      simpa [mul_assoc] using this
  have hVp : ¬ 3 ∣ Nat.card (GLAPPrimeCoreOf 3 K) :=
    (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).1 (coprime_card_glaPPrimeCoreOf K)
  obtain ⟨v, hv, hfix⟩ := exists_fixed_in_coset' (p := 3) (U := E) (V := GLAPPrimeCoreOf 3 K) hE
    hVp (fun e he => (mem_dQ.1 (hED he)).2.1) (hnormU k hk) (fun e he => by
      have h := (mem_dQ.1 (hED he)).2.2 k hk
      have := (GLAPPrimeCoreOf 3 K).inv_mem h
      simpa [mul_assoc] using this)
  refine ⟨v, hv, K.mul_mem hk (hUK hv), Subgroup.mem_centralizer_iff.2 fun e he => ?_⟩
  exact mul_inv_eq_iff_eq_mul.1 (hfix e he)

theorem glaPPrimeCoreOf_cover {K E : Subgroup G} (hE : IsPGroup 3 ↥E) (hED : E ≤ dQ K) :
    GLAPPrimeCoreOf 3 (K ⊓ Subgroup.centralizer (E : Set G)) =
      (K ⊓ Subgroup.centralizer (E : Set G)) ⊓ GLAPPrimeCoreOf 3 K := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set C := K ⊓ Subgroup.centralizer (E : Set G) with hC
  have hCK : C ≤ K := inf_le_left
  have hUK := glaPPrimeCoreOf_le (p := 3) K
  refine le_antisymm (le_inf (glaPPrimeCoreOf_le C) ?_) ?_
  · intro n hn
    set φ : ↥K →* ↥K ⧸ GLAPPrimeCore 3 ↥K := QuotientGroup.mk' (GLAPPrimeCore 3 ↥K) with hφ
    set N := GLAPPrimeCoreOf 3 C with hN
    have hNK : N ≤ K := (glaPPrimeCoreOf_le C).trans hCK
    set S : Subgroup (↥K ⧸ GLAPPrimeCore 3 ↥K) := (N.subgroupOf K).map φ with hS
    have hSnorm : ∀ g : ↥K ⧸ GLAPPrimeCore 3 ↥K, ∀ s ∈ S, g * s * g⁻¹ ∈ S := by
      intro g s hs
      obtain ⟨k0, rfl⟩ := QuotientGroup.mk_surjective g
      obtain ⟨m, hm, rfl⟩ := hs
      obtain ⟨u, hu, hku⟩ := exists_mul_mem_cover hE hED k0.2
      obtain ⟨huK, hu'⟩ := mem_glaPPrimeCoreOf_iff.1 hu
      set c : ↥K := k0 * ⟨u, huK⟩ with hc
      have hg : φ k0 = φ c := by
        rw [hc, map_mul, hφ, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply,
          (QuotientGroup.eq_one_iff (⟨u, huK⟩ : ↥K)).2 hu']
        simp
      refine ⟨c * m * c⁻¹, ?_, ?_⟩
      · refine Subgroup.mem_subgroupOf.2 ?_
        exact conj_mem_glaPPrimeCoreOf (A := C) (a := (c : G)) hku (Subgroup.mem_subgroupOf.1 hm)
      · simp only [map_mul, map_inv]
        show φ c * φ m * (φ c)⁻¹ = φ k0 * φ m * (φ k0)⁻¹
        rw [hg]
    have hScard : Nat.Coprime 3 (Nat.card S) := by
      refine Nat.Coprime.coprime_dvd_right ?_ (coprime_card_glaPPrimeCoreOf C)
      refine (Subgroup.card_map_dvd (H := N.subgroupOf K) φ).trans ?_
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hNK).toEquiv]
    have hSle : S ≤ GLAPPrimeCore 3 (↥K ⧸ GLAPPrimeCore 3 ↥K) :=
      le_sSup ⟨⟨fun s hs g => hSnorm g s hs⟩, hScard⟩
    rw [glaPPrimeCore_quotient_eq_bot Nat.prime_three] at hSle
    have h1 : φ ⟨n, hNK hn⟩ ∈ S := ⟨_, Subgroup.mem_subgroupOf.2 hn, rfl⟩
    have h2 : φ ⟨n, hNK hn⟩ = 1 := Subgroup.mem_bot.1 (hSle h1)
    exact mem_glaPPrimeCoreOf_iff.2 ⟨hNK hn, (QuotientGroup.eq_one_iff _).1 h2⟩
  · refine le_glaPPrimeCoreOf inf_le_left (fun a ha n hn => ?_) ?_
    · exact ⟨C.mul_mem (C.mul_mem ha hn.1) (C.inv_mem ha),
        conj_mem_glaPPrimeCoreOf (hCK ha) hn.2⟩
    · exact Nat.Coprime.coprime_dvd_right (Subgroup.card_dvd_of_le inf_le_right)
        (coprime_card_glaPPrimeCoreOf K)

theorem isQuasisimple_cover {K E : Subgroup G} (hE : IsPGroup 3 ↥E) (hED : E ≤ dQ K)
    (hq : CFSG.Open.IsQuasisimple (↥K ⧸ GLAPPrimeCore 3 ↥K)) :
    CFSG.Open.IsQuasisimple
      (↥(K ⊓ Subgroup.centralizer (E : Set G)) ⧸
        GLAPPrimeCore 3 ↥(K ⊓ Subgroup.centralizer (E : Set G))) := by
  set C := K ⊓ Subgroup.centralizer (E : Set G) with hC
  have hCK : C ≤ K := inf_le_left
  set ψ : ↥C →* ↥K ⧸ GLAPPrimeCore 3 ↥K :=
    (QuotientGroup.mk' (GLAPPrimeCore 3 ↥K)).comp (Subgroup.inclusion hCK) with hψ
  have hsurj : Function.Surjective ψ := by
    intro z
    obtain ⟨k0, rfl⟩ := QuotientGroup.mk_surjective z
    obtain ⟨u, hu, hku⟩ := exists_mul_mem_cover hE hED k0.2
    obtain ⟨huK, hu'⟩ := mem_glaPPrimeCoreOf_iff.1 hu
    refine ⟨⟨(k0 : G) * u, hku⟩, ?_⟩
    show QuotientGroup.mk (⟨(k0 : G) * u, hCK hku⟩ : ↥K) = QuotientGroup.mk k0
    have : (⟨(k0 : G) * u, hCK hku⟩ : ↥K) = k0 * ⟨u, huK⟩ := rfl
    rw [this, QuotientGroup.mk_mul, (QuotientGroup.eq_one_iff (⟨u, huK⟩ : ↥K)).2 hu']
    simp
  have hker : GLAPPrimeCore 3 ↥C = ψ.ker := by
    ext x
    have h1 : x ∈ ψ.ker ↔ (x : G) ∈ GLAPPrimeCoreOf 3 K := by
      rw [MonoidHom.mem_ker]
      show QuotientGroup.mk (⟨(x : G), hCK x.2⟩ : ↥K) = 1 ↔ _
      rw [QuotientGroup.eq_one_iff]
      constructor
      · intro h
        exact mem_glaPPrimeCoreOf_iff.2 ⟨hCK x.2, h⟩
      · intro h
        exact (mem_glaPPrimeCoreOf_iff.1 h).2
    rw [h1]
    have h2 : (x : G) ∈ GLAPPrimeCoreOf 3 C ↔ (x : G) ∈ GLAPPrimeCoreOf 3 K := by
      rw [glaPPrimeCoreOf_cover hE hED]
      exact ⟨fun h => h.2, fun h => ⟨x.2, h⟩⟩
    rw [← h2, mem_glaPPrimeCoreOf_iff]
    exact ⟨fun h => ⟨x.2, h⟩, fun ⟨_, h⟩ => h⟩
  have e : (↥C ⧸ GLAPPrimeCore 3 ↥C) ≃* (↥K ⧸ GLAPPrimeCore 3 ↥K) :=
    (QuotientGroup.quotientMulEquivOfEq hker).trans (QuotientGroup.quotientKerEquivOfSurjective ψ hsurj)
  exact CFSG.SignalizerFunctorTheorem.TransportA.isQuasisimple_of_mulEquiv e.symm hq

theorem coverStmt : CoverStmt := by
  intro G _ _ X K E hK hE hED
  have hq := isQuasisimple_quotient_of_glaPComponent Nat.prime_three hK
  have hQ := isQuasisimple_cover hE hED hq
  obtain ⟨J, hJ, hJtop, huniq⟩ := exists_glaPComponent_of_isQuasisimple hQ
  have hcore := glaPPrimeCoreOf_cover hE hED
  set C := K ⊓ Subgroup.centralizer (E : Set G) with hC
  have hCK : C ≤ K := inf_le_left
  refine ⟨J, hJ, ?_, huniq, ?_⟩
  · intro k hk
    obtain ⟨u, hu, hku⟩ := exists_mul_mem_cover hE hED hk
    have hle : barX 3 C C ≤ barX 3 C J := hJtop ▸ le_top
    obtain ⟨j, hj, hjc⟩ := exists_of_barX_le hle hku hku
    have hw : j⁻¹ * ((k : G) * u) ∈ GLAPPrimeCoreOf 3 K := by
      rw [hcore] at hjc
      exact hjc.2
    have : k = j * (j⁻¹ * ((k : G) * u)) * u⁻¹ := by group
    rw [this]
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mem_sup_left hj)
      (Subgroup.mem_sup_right hw)) (Subgroup.inv_mem _ (Subgroup.mem_sup_right hu))
  · rw [← glaPPrimeCoreOf_inf_eq_of_isSubnormal Nat.prime_three hJ.2.1, hcore]
    ext x
    simp only [Subgroup.mem_inf]
    exact ⟨fun h => ⟨h.1, h.2.2⟩, fun h => ⟨h.1, hJ.1 h.1, h.2⟩⟩

end Cover

end CFSG.HardMathSupport.Solomon.UniquenessMaximal
