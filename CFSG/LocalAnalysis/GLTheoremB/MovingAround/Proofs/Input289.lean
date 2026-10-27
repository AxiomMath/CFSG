module

public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Claims1115c
public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec7K28_8
import CFSG.HardMathSupport.Solomon.Coordinator.Th1J1.Main

public section

namespace CFSG.LocalAnalysis.GLTheoremB.MovingAround.Input289

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB
open CFSG.HardMathSupport.Solomon.Coordinator (IsEkIn IsCatalogLieIso IsL364Index Is3D44Index)
open CFSG.HardMathSupport.Solomon.LocalBalance (barOf)
open CFSG.HardMathSupport.Solomon.UniquenessMaximal (IsMaxBInvariantTwo jOf omegaOneZ tripleOf)

section Transport

variable {G : Type} [Group G] [Finite G]

theorem thompsonJ_eq_jOf (T : Subgroup G) : thompsonJ 2 T = jOf T := rfl

theorem omegaOne_centerOf_eq (T : Subgroup G) : omegaOne 2 (centerOf T) = omegaOneZ T := rfl

theorem map_tripleOf_zero {X T : Subgroup G} (hTX : T ≤ X) :
    (tripleOf (T.subgroupOf X) 0).map X.subtype = thompsonJ 2 T := by
  rw [CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec7.tripleOf_zero, thompsonJ_eq_jOf,
    CFSG.HardMathSupport.Solomon.Coordinator.I28_8.jOf_eq_thompsonJ,
    CFSG.HardMathSupport.Solomon.Coordinator.I28_8.jOf_eq_thompsonJ,
    CFSG.HardMathSupport.Solomon.Coordinator.I28_8.thompsonJ_map_subtype hTX]

theorem map_tripleOf_two {X T : Subgroup G} (hTX : T ≤ X) :
    (tripleOf (T.subgroupOf X) 2).map X.subtype = omegaOne 2 (centerOf T) := by
  rw [CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec7.tripleOf_two, omegaOne_centerOf_eq,
    CFSG.HardMathSupport.Solomon.Coordinator.I28_8.omegaOneZ_eq,
    CFSG.HardMathSupport.Solomon.Coordinator.I28_8.omegaOneZ_eq,
    CFSG.HardMathSupport.Solomon.Coordinator.I28_8.map_quasithinOmegaOneCenter hTX]

theorem isMaxBInvariantTwo_subgroupOf {X B T : Subgroup G} (hBX : B ≤ X)
    (hT : IsMaxInvTwoSub X B T) : IsMaxBInvariantTwo (B.subgroupOf X) (T.subgroupOf X) := by
  obtain ⟨hTX, hT2, hBT, hmax⟩ := hT
  refine ⟨hT2.of_equiv (Subgroup.subgroupOfEquivOfLe hTX).symm, fun b hb => ?_, ?_⟩
  · rw [Subgroup.mem_normalizer_iff]
    intro t
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
    have := (Subgroup.mem_normalizer_iff.1 (hBT (Subgroup.mem_subgroupOf.1 hb))) (t : G)
    simpa using this
  · intro T'' hT''2 hBT'' hTT''
    have hB2 : B ≤ Subgroup.normalizer ((T''.map X.subtype : Subgroup G) : Set G) := fun b hb =>
      CFSG.HardMathSupport.Solomon.Coordinator.I28_8.mem_normalizer_map_subtype
        (n := ⟨b, hBX hb⟩) (hBT'' (Subgroup.mem_subgroupOf.2 hb))
    have hTle : T ≤ T''.map X.subtype := fun t ht =>
      ⟨⟨t, hTX ht⟩, hTT'' (Subgroup.mem_subgroupOf.2 ht), rfl⟩
    have heq : T''.map X.subtype = T :=
      hmax _ (Subgroup.map_subtype_le _) (hT''2.map _) hB2 hTle
    rw [← heq]
    exact (Subgroup.comap_map_eq_self_of_injective X.subtype_injective T'').symm

theorem oPrime3_eq (Y : Type) [Group Y] :
    CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec7K28.oPrime3 Y = GLAPPrimeCore 3 Y :=
  glaPPrimeCore_map_iso 3 (Subgroup.topEquiv (G := Y))

end Transport

section Cover

variable {G : Type} [Group G] [Finite G]

open CFSG.HardMathSupport.Solomon.Coordinator in
theorem cover_of_dichotomy {X B T : Subgroup G}
    (hF : X ⊓ Subgroup.centralizer (pCoreOf 2 X : Set G) ≤ pCoreOf 2 X)
    (hBX : B ≤ X) (hB3 : IsPGroup 3 ↥B) (hT : IsMaxInvTwoSub X B T)
    {E : Subgroup (↥X ⧸ GLAPPrimeCore 3 ↥X)}
    (hE : E ≤ Subgroup.centralizer (barX 3 X T : Set (↥X ⧸ GLAPPrimeCore 3 ↥X)) ∨
      ∃ Q : Subgroup (↥X ⧸ GLAPPrimeCore 3 ↥X), Q ≤ E ∧ Nat.card Q = 7 ∧
        barX 3 X T ≤ Subgroup.normalizer (Q : Set (↥X ⧸ GLAPPrimeCore 3 ↥X)) ∧
        (∃ t ∈ barX 3 X T, ∀ q ∈ Q, t * q * t⁻¹ = q⁻¹) ∧
        (Subgroup.centralizer (barX 3 X T : Set (↥X ⧸ GLAPPrimeCore 3 ↥X)) ⊓ E) ⊔ Q = E) :
    E ≤ barX 3 X (Subgroup.normalizer (thompsonJ 2 T : Set G)) ∨
      E ≤ barX 3 X (Subgroup.normalizer (omegaOne 2 (centerOf T) : Set G)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hTX : T ≤ X := hT.1
  set N : Subgroup ↥X := GLAPPrimeCore 3 ↥X with hN
  set π : ↥X →* ↥X ⧸ N := QuotientGroup.mk' N with hπ
  set T' : Subgroup ↥X := T.subgroupOf X with hT'
  have hT'2 : IsPGroup 2 ↥T' := hT.2.1.of_equiv (Subgroup.subgroupOfEquivOfLe hTX).symm
  have hB'3 : IsPGroup 3 ↥(B.subgroupOf X) :=
    hB3.of_equiv (Subgroup.subgroupOfEquivOfLe hBX).symm
  have hmax := isMaxBInvariantTwo_subgroupOf hBX hT
  have hPN : ¬ 2 ∣ (T' ⊓ N).relIndex N := by
    have := CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec7K28.not_two_dvd_relIndex_inf
      hB'3 hmax
    rwa [oPrime3_eq] at this
  have hcent : Subgroup.centralizer ((T'.map π : Subgroup (↥X ⧸ N)) : Set (↥X ⧸ N)) ≤
      (Subgroup.normalizer (T' : Set ↥X)).map π :=
    I28_8.centralizer_map_le_map_normalizer π (QuotientGroup.ker_mk' N)
      (QuotientGroup.mk'_surjective N) hT'2 hPN
  set U : Subgroup ↥X := CFSG.Open.pCore 2 ↥X with hU
  have hUn : U.Normal := CFSG.pCore_normal
  have hU2 : IsPGroup 2 ↥U := CFSG.pCore_isPGroup
  have hUT : U ≤ T' := I28_8.pCore_le_of_isMax hU2 hmax
  have hC : Subgroup.centralizer (U : Set ↥X) ≤ U := by
    intro x hx
    have hxG : (x : G) ∈ X ⊓ Subgroup.centralizer (pCoreOf 2 X : Set G) := by
      refine Subgroup.mem_inf.2 ⟨x.2, Subgroup.mem_centralizer_iff.2 ?_⟩
      rintro _ ⟨u, hu, rfl⟩
      exact congrArg Subtype.val (Subgroup.mem_centralizer_iff.1 hx u hu)
    obtain ⟨u, hu, hux⟩ := hF hxG
    have : u = x := Subtype.ext hux
    exact this ▸ hu
  have htr : ∀ {M : Subgroup ↥X} {S : Subgroup G}, M.map X.subtype = S →
      (Subgroup.normalizer (M : Set ↥X)).map π ≤
        barX 3 X (Subgroup.normalizer (S : Set G)) := by
    intro M S hMS
    rintro _ ⟨x, hx, rfl⟩
    refine ⟨x, Subgroup.mem_subgroupOf.2 ?_, rfl⟩
    have := I28_8.mem_normalizer_map_subtype hx
    rwa [hMS] at this
  have h0 := htr (map_tripleOf_zero hTX)
  have h2 := htr (map_tripleOf_two hTX)
  have hNT : ∀ i : Fin 3, (Subgroup.normalizer (T' : Set ↥X)).map π ≤
      (Subgroup.normalizer (tripleOf T' i : Set ↥X)).map π := fun i =>
    Subgroup.map_mono
      (CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec7.normalizer_le_normalizer_tripleOf T' i)
  rcases hE with hE | ⟨Q, hQE, hQ7, hTQ, ⟨t, ht, hinv⟩, hgen⟩
  · exact Or.inl (hE.trans (hcent.trans ((hNT 0).trans h0)))
  · obtain ⟨t₀, ht₀, rfl⟩ := ht
    have h27 := I28_8.twoSeven_of_th1 (I28_8.th1_of_th1J1 I28_8.th1J1Factorization)
    have hQr : Q ≤ π.range := by
      rw [MonoidHom.range_eq_top.2 (QuotientGroup.mk'_surjective N)]
      exact le_top
    obtain ⟨s, hs, hsQ⟩ := I28_8.two_cover_of_twoSeven h27 hT'2 hPN hUn hU2 hUT hC π
      (QuotientGroup.ker_mk' N) Q hQ7 hQr hTQ ⟨t₀, ht₀, hinv⟩
    obtain ⟨i, hi, hi1⟩ : ∃ i ∈ s, i ≠ 1 := by
      by_contra hne
      push Not at hne
      have hsub : s ⊆ {1} := fun i hi => Finset.mem_singleton.2 (hne i hi)
      have := Finset.card_le_card hsub
      rw [Finset.card_singleton] at this
      omega
    have hEi : E ≤ (Subgroup.normalizer (tripleOf T' i : Set ↥X)).map π := by
      rw [← hgen]
      exact sup_le (inf_le_left.trans (hcent.trans (hNT i))) (hsQ i hi)
    rcases CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec7.fin_three_cases i with
      rfl | rfl | rfl
    · exact Or.inl (hEi.trans h0)
    · exact absurd rfl hi1
    · exact Or.inr (hEi.trans h2)

end Cover

section L34

variable {Y : Type} [Group Y] [Finite Y]

open CFSG.GH74.KGroups CFSG.GH74.KGroups.L34 CFSG.Sporadic.Schreier
  CFSG.HardMathSupport.Solomon.Coordinator CFSG.HardMathSupport.Solomon.Coordinator.I28_8
  CFSG.LocalAnalysis.ComponentInitial.LinearFlag in
theorem l34FactsAut
    {K T D : Subgroup Y}
    (hL : IsLThreeFour ↥K) (hT : IsPGroup 2 ↥T) (hTK : T ≤ Subgroup.normalizer (K : Set Y))
    (hDK : D ≤ K) (hD : Nat.card D = 9)
    (hDT : ∀ d ∈ D, ∀ t ∈ T, ∃ t' ∈ T, ∀ k ∈ K,
      d * t * d⁻¹ * k * (d * t * d⁻¹)⁻¹ = t' * k * t'⁻¹) :
    K ≤ Subgroup.centralizer (T : Set Y) ∨
      ∃ Q : Subgroup Y, Q ≤ K ∧ Nat.card Q = 7 ∧ T ≤ Subgroup.normalizer (Q : Set Y) ∧
        (∃ t ∈ T, ∀ q ∈ Q, t * q * t⁻¹ = q⁻¹) ∧
        (Subgroup.centralizer (T : Set Y) ⊓ K) ⊔ Q = K := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set NK : Subgroup Y := Subgroup.normalizer (K : Set Y) with hNK
  set ρ : ↥NK →* MulAut ↥K := K.normalizerMonoidHom with hρ
  have hρ1 : ∀ (g : ↥NK) (x : ↥K), ((ρ g x : ↥K) : Y) = (g : Y) * x * (g : Y)⁻¹ := fun g x => by
    rw [hρ, Subgroup.normalizerMonoidHom_apply_apply_coe]
  set TT : Subgroup (MulAut ↥K) := (T.subgroupOf NK).map ρ with hTT
  have hmemTT : ∀ t (ht : t ∈ T), ρ ⟨t, hTK ht⟩ ∈ TT := fun t ht =>
    ⟨⟨t, hTK ht⟩, Subgroup.mem_subgroupOf.2 ht, rfl⟩
  set D' : Subgroup ↥K := D.subgroupOf K with hD'
  have hD'9 : Nat.card D' = 9 := by
    rw [← hD]; exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hDK).toEquiv
  have hX : ¬ 3 ∣ Nat.card TT := by
    intro h3
    have hT' : IsPGroup 2 ↥(T.subgroupOf NK) :=
      hT.of_equiv (Subgroup.subgroupOfEquivOfLe hTK).symm
    obtain ⟨n, hn⟩ := (IsPGroup.iff_card (p := 2)).1 hT'
    have h4 : Nat.card TT ∣ 2 ^ n := hn ▸ Subgroup.card_map_dvd (H := T.subgroupOf NK) ρ
    exact absurd (Nat.Prime.dvd_of_dvd_pow Nat.prime_three (h3.trans h4)) (by norm_num)
  have hconj : ∀ d ∈ D', ∀ m ∈ TT, MulAut.conj d * m * (MulAut.conj d)⁻¹ ∈ TT := by
    rintro d hd _ ⟨⟨t, htN⟩, ht, rfl⟩
    obtain ⟨t', ht', heq⟩ :=
      hDT (d : Y) (Subgroup.mem_subgroupOf.1 hd) t (Subgroup.mem_subgroupOf.1 ht)
    refine ⟨⟨t', hTK ht'⟩, Subgroup.mem_subgroupOf.2 ht', ?_⟩
    ext k
    rw [hρ1]
    simp only [MulAut.mul_apply, MulAut.conj_apply, MulAut.conj_inv_apply, Subgroup.coe_mul,
      Subgroup.coe_inv, hρ1]
    rw [← heq (k : Y) k.2]
    group
  have hDX : ∀ d ∈ D', MulAut.conj d ∈ Subgroup.normalizer (TT : Set (MulAut ↥K)) := by
    intro d hd
    refine I28_8.mem_normalizer_of_conj_mem' (hconj d hd) (fun m hm => ?_)
    have h := hconj d⁻¹ (D'.inv_mem hd) m hm
    rwa [map_inv, inv_inv] at h
  rcases exists_tau hL hD'9 hX hDX with hbot | ⟨τ, hXτ, hτ2, hout, hfix⟩
  · left
    intro k hk
    rw [Subgroup.mem_centralizer_iff]
    intro t ht
    have h1 : ρ ⟨t, hTK ht⟩ = 1 := by
      have := hmemTT t ht
      rw [hbot] at this
      exact this
    have h2 := congrArg (fun m : MulAut ↥K => ((m ⟨k, hk⟩ : ↥K) : Y)) h1
    simp only [hρ1, MulAut.one_apply] at h2
    rw [show t * k = (t * k * t⁻¹) * t by group, h2]
  · obtain ⟨ψ⟩ := exists_equiv_P21 hL
    obtain ⟨π⟩ := equiv_P21_P
    obtain ⟨x, hx7, hxτ⟩ := exists_seven (ψ.trans π) hτ2 hout
    have hxne : τ x ≠ x := by
      intro hx
      have hxN : x ∈ Subgroup.normalizer (D' : Set ↥K) := (hfix x).1 hx
      have h72 := CFSG.RankThree.PartTwo.KFacts.L34Max.card_normalizer_of_mulEquiv ψ hD'9
      have h1 := orderOf_dvd_natCard (⟨x, hxN⟩ : Subgroup.normalizer (D' : Set ↥K))
      rw [h72] at h1
      have h2 : orderOf x ∣ 72 := by
        rw [← (Subgroup.orderOf_coe (⟨x, hxN⟩ : Subgroup.normalizer (D' : Set ↥K)))] at h1
        exact h1
      rw [hx7] at h2
      omega
    have hτx : τ x = x⁻¹ := hxτ.resolve_left hxne
    set x' : Y := (x : Y) with hx'
    set Q : Subgroup Y := Subgroup.zpowers x' with hQ
    have hQK : Q ≤ K := (Subgroup.zpowers_le).2 x.2
    have hQcard : Nat.card Q = 7 := by
      rw [hQ, Nat.card_zpowers, hx', Subgroup.orderOf_coe, hx7]
    have hρT : ∀ t (ht : t ∈ T), ρ ⟨t, hTK ht⟩ = 1 ∨ ρ ⟨t, hTK ht⟩ = τ := fun t ht =>
      zpowers_involution_cases hτ2 (hXτ ▸ hmemTT t ht)
    have hact : ∀ t ∈ T, t * x' * t⁻¹ = x' ∨ t * x' * t⁻¹ = x'⁻¹ := by
      intro t ht
      have h1 := hρ1 ⟨t, hTK ht⟩ x
      rcases hρT t ht with h | h
      · left; rw [h] at h1; simpa using h1.symm
      · right; rw [h, hτx] at h1; simpa using h1.symm
    have hconjQ : ∀ t ∈ T, ∀ q ∈ Q, t * q * t⁻¹ ∈ Q := by
      intro t ht q hq
      obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.1 hq
      have : t * x' ^ m * t⁻¹ = (t * x' * t⁻¹) ^ m := by
        simp
      rw [this]
      rcases hact t ht with h | h <;> rw [h]
      · exact Subgroup.zpow_mem _ (Subgroup.mem_zpowers _) _
      · exact Subgroup.zpow_mem _ (Subgroup.inv_mem _ (Subgroup.mem_zpowers _)) _
    have hTQ : T ≤ Subgroup.normalizer (Q : Set Y) := fun t ht =>
      CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec7.mem_normalizer_of_conj_mem
        (hconjQ t ht) (fun q hq => by simpa using hconjQ t⁻¹ (inv_mem ht) q hq)
    obtain ⟨t0, ht0, hρt0⟩ : ∃ t0 : ↥NK, (t0 : Y) ∈ T ∧ ρ t0 = τ := by
      have : τ ∈ TT := hXτ ▸ Subgroup.mem_zpowers τ
      obtain ⟨t0, ht0, hte⟩ := this
      exact ⟨t0, Subgroup.mem_subgroupOf.1 ht0, hte⟩
    have hinv : ∀ q ∈ Q, (t0 : Y) * q * (t0 : Y)⁻¹ = q⁻¹ := by
      intro q hq
      obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.1 hq
      have h1 : (t0 : Y) * x' * (t0 : Y)⁻¹ = x'⁻¹ := by
        have := hρ1 t0 x
        rw [hρt0, hτx] at this
        simpa using this.symm
      have : (t0 : Y) * x' ^ m * (t0 : Y)⁻¹ = ((t0 : Y) * x' * (t0 : Y)⁻¹) ^ m := by
        simp
      rw [this, h1, inv_zpow', zpow_neg]
    right
    refine ⟨Q, hQK, hQcard, hTQ, ⟨(t0 : Y), ht0, hinv⟩, ?_⟩
    apply le_antisymm (sup_le inf_le_right hQK)
    set W : Subgroup Y := (Subgroup.centralizer (T : Set Y) ⊓ K) ⊔ Q with hW
    have hfixcent : ∀ k : ↥K, τ k = k → (k : Y) ∈ Subgroup.centralizer (T : Set Y) := by
      intro k hk
      rw [Subgroup.mem_centralizer_iff]
      intro t ht
      have h1 := hρ1 ⟨t, hTK ht⟩ k
      have h2 : t * k * t⁻¹ = k := by
        rcases hρT t ht with h | h
        · rw [h] at h1; simpa using h1.symm
        · rw [h, hk] at h1; exact h1.symm
      rw [show t * k = (t * k * t⁻¹) * t by group, h2]
    have hWk : W.subgroupOf K = ⊤ := by
      by_contra hne
      have hEY : Subgroup.normalizer (D' : Set ↥K) ≤ W.subgroupOf K := by
        intro k hk
        rw [Subgroup.mem_subgroupOf]
        exact Subgroup.mem_sup_left ⟨hfixcent k ((hfix k).2 hk), k.2⟩
      have heq := CFSG.RankThree.PartTwo.KFacts.L34Max.eq_normalizer_of_mulEquiv ψ hD'9 hEY hne
      have hxW : x ∈ W.subgroupOf K := by
        rw [Subgroup.mem_subgroupOf]
        exact Subgroup.mem_sup_right (Subgroup.mem_zpowers _)
      rw [heq] at hxW
      exact hxne ((hfix x).2 hxW)
    intro k hk
    have : (⟨k, hk⟩ : ↥K) ∈ W.subgroupOf K := hWk ▸ Subgroup.mem_top _
    exact Subgroup.mem_subgroupOf.1 this

end L34

section Facts

@[expose] def CoverFacts (P : TauCeti.LieTypeIndex → Prop) : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (K T D J : Subgroup Y), K.Normal → IsCatalogLieIso ↥K P →
    IsPGroup 2 ↥T → D ≤ Subgroup.normalizer (T : Set Y) → IsElemAbelian 3 D → Nat.card D = 9 →
    D ≤ J → J ≤ K → IsLThreeFour (barOf 3 J) →
      K ≤ Subgroup.centralizer (T : Set Y) ∨
        ∃ Q : Subgroup Y, Q ≤ K ∧ Nat.card Q = 7 ∧ T ≤ Subgroup.normalizer (Q : Set Y) ∧
          (∃ t ∈ T, ∀ q ∈ Q, t * q * t⁻¹ = q⁻¹) ∧
          (Subgroup.centralizer (T : Set Y) ⊓ K) ⊔ Q = K

@[expose] def CoverFactsL364 : Prop := CoverFacts IsL364Index

@[expose] def CoverFacts3D44 : Prop := CoverFacts Is3D44Index

@[expose] def CoverFactsRest : Prop := CoverFactsL364 ∧ CoverFacts3D44

end Facts

section Bar

variable {G : Type} [Group G] [Finite G]

theorem card_inf_eq_nine {X B J : Subgroup G} {b : G} (hB : IsEkIn 3 3 X B) (hbB : b ∈ B)
    (hb1 : b ≠ 1) (hinf : Subgroup.zpowers b ⊓ (B ⊓ J) = ⊥)
    (hsup : Subgroup.zpowers b ⊔ (B ⊓ J) = B) : Nat.card ↥(B ⊓ J) = 9 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hbJ : b ∉ B ⊓ J := fun h => hb1 (by
    have hb : b ∈ Subgroup.zpowers b ⊓ (B ⊓ J) := ⟨Subgroup.mem_zpowers b, h⟩
    rw [hinf] at hb
    exact hb)
  have h := GL83.CompFam.card_sup_zpowers hB.2.1 inf_le_left hbB hbJ
  rw [sup_comm, hsup, hB.2.2] at h
  have h' : 3 * Nat.card ↥(B ⊓ J) = 3 * 9 := by rw [← h]; norm_num
  exact Nat.eq_of_mul_eq_mul_left (by norm_num) h'

theorem isLThreeFour_barOf_barX {X J : Subgroup G} (hJX : J ≤ X) (h : IsLThreeFour (barOf 3 J)) :
    IsLThreeFour (barOf 3 (barX 3 X J)) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let A : Subgroup ↥X := J.subgroupOf X
  let e : ↥J ≃* ↥A := (Subgroup.subgroupOfEquivOfLe hJX).symm
  have hker : Nat.Coprime 3
      (Nat.card ↥(A ⊓ (QuotientGroup.mk' (GLAPPrimeCore 3 ↥X)).ker)) := by
    refine Nat.Coprime.coprime_dvd_right (Subgroup.card_dvd_of_le inf_le_right) ?_
    rw [QuotientGroup.ker_mk']
    exact CFSG.pPrimeCore_coprime_card
  exact CFSG.HardMathSupport.Solomon.Coordinator.I28_8.isLThreeFour_of_equiv
    ((QuotientGroup.congr _ _ e (glaPPrimeCore_map_iso 3 e)).trans
      (lcEquiv Nat.prime_three (QuotientGroup.mk' (GLAPPrimeCore 3 ↥X)) A hker)) h

theorem eq_one_of_mem_center {X J : Subgroup G} (hJX : J ≤ X) (hJ34 : IsLThreeFour (barOf 3 J))
    {y : ↥X ⧸ GLAPPrimeCore 3 ↥X} (hyJ : y ∈ barX 3 X J)
    (hyc : y ∈ Subgroup.centralizer (barX 3 X J : Set (↥X ⧸ GLAPPrimeCore 3 ↥X)))
    (hy3 : y ^ 3 = 1) : y = 1 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set Jb := barX 3 X J with hJb
  have h34 : IsLThreeFour (barOf 3 Jb) := isLThreeFour_barOf_barX hJX hJ34
  set π := QuotientGroup.mk' (GLAPPrimeCore 3 ↥Jb) with hπ
  have hcen : π ⟨y, hyJ⟩ ∈ Subgroup.center (barOf 3 Jb) := by
    rw [Subgroup.mem_center_iff]
    intro z
    obtain ⟨k, rfl⟩ := QuotientGroup.mk'_surjective (GLAPPrimeCore 3 ↥Jb) z
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (Subgroup.mem_centralizer_iff.1 hyc (k : ↥X ⧸ GLAPPrimeCore 3 ↥X) k.2)
  rw [Claims1115b.center_eq_bot_of_isLThreeFour h34, Subgroup.mem_bot, hπ,
    QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hcen
  have hdvd : orderOf (⟨y, hyJ⟩ : ↥Jb) ∣ Nat.card (GLAPPrimeCore 3 ↥Jb) :=
    Subgroup.orderOf_dvd_natCard _ hcen
  have hcop := CFSG.HardMathSupport.Solomon.LocalBalance.coprime_card_gLAPPrimeCore_aux 3 ↥Jb
  have h3 : orderOf (⟨y, hyJ⟩ : ↥Jb) ∣ 3 :=
    orderOf_dvd_of_pow_eq_one (Subtype.ext (by simpa using hy3))
  have h1 : orderOf (⟨y, hyJ⟩ : ↥Jb) = 1 :=
    Nat.Coprime.eq_one_of_dvd (Nat.Coprime.coprime_dvd_left h3 hcop) hdvd
  have := orderOf_eq_one_iff.1 h1
  exact congrArg Subtype.val this

theorem mem_of_le_sSup {X L : Subgroup G} (hL : GLAPComponent 3 X L) {𝒦 : Set (Subgroup G)}
    (h𝒦 : ∀ K ∈ 𝒦, GLAPComponent 3 X K) (hle : L ≤ sSup 𝒦) : L ∈ 𝒦 := by
  by_contra hL𝒦
  set π := QuotientGroup.mk' (GLAPPrimeCore 3 ↥X) with hπ
  set W : Subgroup G := ((Subgroup.centralizer (barX 3 X L : Set (↥X ⧸ GLAPPrimeCore 3 ↥X))).comap
    π).map X.subtype with hW
  have hKW : ∀ K ∈ 𝒦, K ≤ W := by
    intro K hK k hk
    have hkX : k ∈ X := (h𝒦 K hK).1 hk
    have hne : L ≠ K := fun h => hL𝒦 (h ▸ hK)
    exact ⟨⟨k, hkX⟩, Subgroup.mem_comap.2 (Claims1115b.barX_le_centralizer_of_ne' hL (h𝒦 K hK) hne
      (Inputs1115.mk_mem_barX hkX hk)), rfl⟩
  have hLW : L ≤ W := hle.trans (sSup_le hKW)
  have hab : barX 3 X L ≤ Subgroup.centralizer (barX 3 X L : Set (↥X ⧸ GLAPPrimeCore 3 ↥X)) := by
    rintro _ ⟨l, hl, rfl⟩
    obtain ⟨y, hy, hyl⟩ := hLW (Subgroup.mem_subgroupOf.1 hl)
    have : y = l := Subtype.ext hyl
    rw [← this]
    exact hy
  have hc : CFSG.Open.IsComponentOf (barX 3 X L) ⊤ := hL.2.2.1
  have hq : CFSG.Open.IsQuasisimple ↥(barX 3 X L) := hc.2.2
  have hcomm : commutator ↥(barX 3 X L) = ⊥ := by
    show ⁅(⊤ : Subgroup ↥(barX 3 X L)), ⊤⁆ = ⊥
    rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
    intro x _
    rw [Subgroup.mem_centralizer_iff]
    intro y _
    exact Subtype.ext (Subgroup.mem_centralizer_iff.1 (hab x.2) (y : ↥X ⧸ GLAPPrimeCore 3 ↥X) y.2)
  have htop : (⊤ : Subgroup ↥(barX 3 X L)) = ⊥ := hq.1.symm.trans hcomm
  apply CFSG.HardMathSupport.Solomon.LocalBalance.Lemma54Ns.barX_ne_bot_of_comp hL
  rw [eq_bot_iff]
  intro z hz
  have : (⟨z, hz⟩ : ↥(barX 3 X L)) ∈ (⊥ : Subgroup ↥(barX 3 X L)) := htop ▸ Subgroup.mem_top _
  rw [Subgroup.mem_bot] at this
  exact Subgroup.mem_bot.2 (congrArg Subtype.val this)

theorem barX_layer_normal (X : Subgroup G) : (barX 3 X (GLAPLayer 3 X)).Normal := by
  have hN : X ≤ Subgroup.normalizer (GLAPLayer 3 X : Set G) :=
    CFSG.HardMathSupport.Solomon.LocalBalance.Lemma512Ns.le_normalizer_gLAPLayer 3
      (fun y hy => Subgroup.le_normalizer hy)
  have h1 : ((GLAPLayer 3 X).subgroupOf X).Normal := by
    refine ⟨fun x hx g => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hx ⊢
    exact (Subgroup.mem_normalizer_iff.1 (hN g.2) x).1 hx
  exact h1.map _ (QuotientGroup.mk'_surjective _)

end Bar

section Single

variable {G : Type} [Group G] [Finite G]

theorem cover_single
    (h364 : CoverFactsL364) (h3D4 : CoverFacts3D44) {X B T J : Subgroup G} {b : G}
    (hF : X ⊓ Subgroup.centralizer (pCoreOf 2 X : Set G) ≤ pCoreOf 2 X)
    (htype : IsLThreeFour ↥(barX 3 X (GLAPLayer 3 X)) ∨
      IsCatalogLieIso ↥(barX 3 X (GLAPLayer 3 X)) IsL364Index ∨
      IsCatalogLieIso ↥(barX 3 X (GLAPLayer 3 X)) Is3D44Index)
    (hB : IsEkIn 3 3 X B) (hT : IsMaxInvTwoSub X B T) (hbB : b ∈ B) (hb1 : b ≠ 1)
    (hJ : GLAPComponent 3 (GLAPLayer 3 (GLAPLayer 3 X ⊓ Subgroup.centralizer ({b} : Set G))) J)
    (hJ34 : IsLThreeFour (barOf 3 J)) (hinf : Subgroup.zpowers b ⊓ (B ⊓ J) = ⊥)
    (hsup : Subgroup.zpowers b ⊔ (B ⊓ J) = B) :
    Covers 3 X (Subgroup.normalizer (thompsonJ 2 T : Set G)) (GLAPLayer 3 X) ∨
      Covers 3 X (Subgroup.normalizer (omegaOne 2 (centerOf T) : Set G)) (GLAPLayer 3 X) := by
  have hBX : B ≤ X := hB.1
  have hB3 : IsPGroup 3 ↥B := hB.2.1.isPGroup
  have hTX : T ≤ X := hT.1
  have hKX : GLAPLayer 3 X ≤ X := sSup_le fun _ h => h.1
  have hJK : J ≤ GLAPLayer 3 X := hJ.1.trans ((sSup_le fun _ h => h.1).trans inf_le_left)
  have hJX : J ≤ X := hJK.trans hKX
  have hD9 : Nat.card ↥(barX 3 X (B ⊓ J)) = 9 := by
    rw [Claims1115b.card_barX_of_isPGroup (inf_le_left.trans hBX) (hB3.to_le inf_le_left)]
    exact card_inf_eq_nine hB hbB hb1 hinf hsup
  have hDK : barX 3 X (B ⊓ J) ≤ barX 3 X (GLAPLayer 3 X) :=
    Inputs1115.barX_le_barX (inf_le_right.trans hJK)
  have hDJ : barX 3 X (B ⊓ J) ≤ barX 3 X J := Inputs1115.barX_le_barX inf_le_right
  have hJK' : barX 3 X J ≤ barX 3 X (GLAPLayer 3 X) := Inputs1115.barX_le_barX hJK
  have hDT : barX 3 X (B ⊓ J) ≤
      Subgroup.normalizer (barX 3 X T : Set (↥X ⧸ GLAPPrimeCore 3 ↥X)) :=
    barX_le_normalizer (inf_le_left.trans hT.2.2.1)
  have hDel : IsElemAbelian 3 (barX 3 X (B ⊓ J)) :=
    ((hB.2.1.mono inf_le_left).subgroupOf X).map _
  have hT2 : IsPGroup 2 ↥(barX 3 X T) :=
    (hT.2.1.of_equiv (Subgroup.subgroupOfEquivOfLe hTX).symm).map _
  have hKn := barX_layer_normal X
  have hTK : barX 3 X T ≤
      Subgroup.normalizer (barX 3 X (GLAPLayer 3 X) : Set (↥X ⧸ GLAPPrimeCore 3 ↥X)) := by
    haveI := hKn
    rw [Subgroup.normalizer_eq_top]
    exact le_top
  have hJ34' := isLThreeFour_barOf_barX hJX hJ34
  have hdich : barX 3 X (GLAPLayer 3 X) ≤
        Subgroup.centralizer (barX 3 X T : Set (↥X ⧸ GLAPPrimeCore 3 ↥X)) ∨
      ∃ Q : Subgroup (↥X ⧸ GLAPPrimeCore 3 ↥X), Q ≤ barX 3 X (GLAPLayer 3 X) ∧ Nat.card Q = 7 ∧
        barX 3 X T ≤ Subgroup.normalizer (Q : Set (↥X ⧸ GLAPPrimeCore 3 ↥X)) ∧
        (∃ t ∈ barX 3 X T, ∀ q ∈ Q, t * q * t⁻¹ = q⁻¹) ∧
        (Subgroup.centralizer (barX 3 X T : Set (↥X ⧸ GLAPPrimeCore 3 ↥X)) ⊓
          barX 3 X (GLAPLayer 3 X)) ⊔ Q = barX 3 X (GLAPLayer 3 X) := by
    rcases htype with h34 | hcat | hcat
    · refine l34FactsAut h34 hT2 hTK hDK hD9
        (fun d hd t ht => ⟨d * t * d⁻¹, (Subgroup.mem_normalizer_iff.1 (hDT hd) t).1 ht,
          fun _ _ => rfl⟩)
    · exact h364 _ _ _ _ _ hKn hcat hT2 hDT hDel hD9 hDJ hJK' hJ34'
    · exact h3D4 _ _ _ _ _ hKn hcat hT2 hDT hDel hD9 hDJ hJK' hJ34'
  exact cover_of_dichotomy hF hBX hB3 hT hdich

end Single

section Group

variable {Γ : Type*} [Group Γ]

theorem mem_centralizer_gLBConj {S : Subgroup Γ} {y g : Γ} (hyg : y * g = g * y)
    (hy : y ∈ Subgroup.centralizer (S : Set Γ)) :
    y ∈ Subgroup.centralizer ((GLBConj g S : Subgroup Γ) : Set Γ) := by
  rw [Subgroup.mem_centralizer_iff] at hy ⊢
  intro z hz
  have h1 := hy _ (mem_gLBConj.1 hz)
  have hgy : g * y * g⁻¹ = y := by rw [← hyg, mul_inv_cancel_right]
  calc z * y = g⁻¹ * ((g * z * g⁻¹) * (g * y * g⁻¹)) * g := by group
    _ = g⁻¹ * ((g * z * g⁻¹) * y) * g := by rw [hgy]
    _ = g⁻¹ * (y * (g * z * g⁻¹)) * g := by rw [h1]
    _ = g⁻¹ * ((g * y * g⁻¹) * (g * z * g⁻¹)) * g := by rw [hgy]
    _ = y * z := by group

theorem conj_act_eq {E : Subgroup Γ} {x e t : Γ} (hxN : x ∈ Subgroup.normalizer (E : Set Γ))
    (htN : t ∈ Subgroup.normalizer (E : Set Γ)) (hxe : ∀ w ∈ E, x * w * x⁻¹ = e * w * e⁻¹)
    {k : Γ} (hk : k ∈ E) :
    e * t * e⁻¹ * k * (e * t * e⁻¹)⁻¹ = x * t * x⁻¹ * k * (x * t * x⁻¹)⁻¹ := by
  have hk₁ : x⁻¹ * k * x ∈ E := by
    have := (Subgroup.mem_normalizer_iff.1 (Subgroup.inv_mem _ hxN) k).1 hk
    simpa using this
  have e1 : e⁻¹ * k * e = x⁻¹ * k * x := by
    have h1 := hxe _ hk₁
    have h2 : k = e * (x⁻¹ * k * x) * e⁻¹ := by rw [← h1]; group
    calc e⁻¹ * k * e = e⁻¹ * (e * (x⁻¹ * k * x) * e⁻¹) * e := by rw [← h2]
      _ = x⁻¹ * k * x := by group
  have hk₂ : t * (x⁻¹ * k * x) * t⁻¹ ∈ E := (Subgroup.mem_normalizer_iff.1 htN _).1 hk₁
  have e2 := hxe _ hk₂
  calc e * t * e⁻¹ * k * (e * t * e⁻¹)⁻¹ = e * (t * (e⁻¹ * k * e) * t⁻¹) * e⁻¹ := by group
    _ = e * (t * (x⁻¹ * k * x) * t⁻¹) * e⁻¹ := by rw [e1]
    _ = x * (t * (x⁻¹ * k * x) * t⁻¹) * x⁻¹ := e2.symm
    _ = x * t * x⁻¹ * k * (x * t * x⁻¹)⁻¹ := by group

end Group

section Triple

variable {G : Type} [Group G] [Finite G]

@[expose] def IsLThreeFourCubeCyc (X : Subgroup G) (b : G) : Prop :=
  ∃ K₁ : Subgroup G, GLAPComponent 3 X K₁ ∧ GLBConj b K₁ ≠ K₁ ∧
    GLAPLayer 3 X = K₁ ⊔ GLBConj b K₁ ⊔ GLBConj b (GLBConj b K₁) ∧ IsLThreeFour ↥(barX 3 X K₁)

theorem le_normalizer_gLBConj {T L : Subgroup G} {b : G}
    (hbT : b ∈ Subgroup.normalizer (T : Set G)) (hTL : T ≤ Subgroup.normalizer (L : Set G)) :
    T ≤ Subgroup.normalizer (GLBConj b L : Set G) := by
  intro t ht
  rw [mem_normalizer_iff_gLBConj_eq]
  have hs : b * t * b⁻¹ ∈ T := (Subgroup.mem_normalizer_iff.1 hbT t).1 ht
  have e : GLBConj t (GLBConj b L) = GLBConj b (GLBConj (b * t * b⁻¹) L) := by
    rw [gLBConj_gLBConj, gLBConj_gLBConj]
    congr 1
    group
  rw [e, gLBConj_eq_of_mem_normalizer (hTL hs)]

theorem le_normalizer_of_three {X T : Subgroup G} (hTX : T ≤ X) (hT2 : IsPGroup 2 ↥T)
    {K₁ K₂ K₃ : Subgroup G} (h₁ : GLAPComponent 3 X K₁) (h₂ : GLAPComponent 3 X K₂)
    (h₃ : GLAPComponent 3 X K₃) (h12 : K₁ ≠ K₂) (h13 : K₁ ≠ K₃) (h23 : K₂ ≠ K₃)
    (hlay : GLAPLayer 3 X = K₁ ⊔ K₂ ⊔ K₃) :
    T ≤ Subgroup.normalizer (K₁ : Set G) ∨ T ≤ Subgroup.normalizer (K₂ : Set G) ∨
      T ≤ Subgroup.normalizer (K₃ : Set G) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Finite (Subgroup G) := Finite.of_injective _ SetLike.coe_injective
  have hiff : ∀ L : Subgroup G, GLAPComponent 3 X L ↔ L ∈ ({K₁, K₂, K₃} : Set (Subgroup G)) := by
    intro L
    constructor
    · intro hL
      refine mem_of_le_sSup hL (fun K hK => ?_) ?_
      · rcases hK with rfl | rfl | rfl
        · exact h₁
        · exact h₂
        · exact h₃
      · have e : sSup ({K₁, K₂, K₃} : Set (Subgroup G)) = K₁ ⊔ K₂ ⊔ K₃ := by
          rw [sSup_insert, sSup_insert, sSup_singleton, sup_assoc]
        rw [e, ← hlay]
        exact le_sSup hL
    · rintro (rfl | rfl | rfl)
      · exact h₁
      · exact h₂
      · exact h₃
  let α := {L : Subgroup G // GLAPComponent 3 X L}
  letI : MulAction ↥T α :=
    { smul := fun t L => ⟨GLBConj (t : G)⁻¹ L.1,
        Inputs1115.glaPComponent_conj_of_mem L.2 (X.inv_mem (hTX t.2))⟩
      one_smul := fun L => Subtype.ext (by
        show GLBConj ((1 : ↥T) : G)⁻¹ L.1 = L.1
        rw [OneMemClass.coe_one, inv_one, gLBConj_one])
      mul_smul := fun s t L => Subtype.ext (by
        show GLBConj ((s * t : ↥T) : G)⁻¹ L.1 = GLBConj (s : G)⁻¹ (GLBConj (t : G)⁻¹ L.1)
        rw [gLBConj_gLBConj, Subgroup.coe_mul, mul_inv_rev]) }
  have hcard : Nat.card α = 3 := by
    have e : α ≃ ({K₁, K₂, K₃} : Set (Subgroup G)) := Equiv.subtypeEquivRight hiff
    rw [Nat.card_congr e, Nat.card_coe_set_eq, Set.ncard_eq_three]
    exact ⟨K₁, K₂, K₃, h12, h13, h23, rfl⟩
  have hmod := hT2.card_modEq_card_fixedPoints α
  rw [hcard] at hmod
  have hne : (MulAction.fixedPoints ↥T α).Nonempty := by
    by_contra h
    rw [Set.not_nonempty_iff_eq_empty] at h
    rw [h] at hmod
    have h0 : Nat.card (↥(∅ : Set α)) = 0 := by simp
    rw [h0] at hmod
    exact absurd hmod (by decide)
  obtain ⟨L, hL⟩ := hne
  have hTL : T ≤ Subgroup.normalizer (L.1 : Set G) := by
    intro t ht
    have h1 : (⟨t, ht⟩ : ↥T) • L = L := hL ⟨t, ht⟩
    have h2 : GLBConj t⁻¹ L.1 = L.1 := congrArg Subtype.val h1
    have h3 : t⁻¹ ∈ Subgroup.normalizer (L.1 : Set G) := mem_normalizer_iff_gLBConj_eq.2 h2
    simpa using Subgroup.inv_mem _ h3
  rcases (hiff L.1).1 L.2 with h | h | h
  · exact Or.inl (h ▸ hTL)
  · exact Or.inr (Or.inl (h ▸ hTL))
  · exact Or.inr (Or.inr (h ▸ hTL))

theorem barX_gLBConj_le {X N L : Subgroup G} {b : G} (hbX : b ∈ X) (hbN : b ∈ N)
    (h : barX 3 X L ≤ barX 3 X N) : barX 3 X (GLBConj b L) ≤ barX 3 X N := by
  rw [barX_gLBConj_eq 3 hbX]
  have h1 := gLBConj_mono (QuotientGroup.mk' (GLAPPrimeCore 3 ↥X) ⟨b, hbX⟩) h
  have h2 : GLBConj (QuotientGroup.mk' (GLAPPrimeCore 3 ↥X) ⟨b, hbX⟩) (barX 3 X N) = barX 3 X N := by
    rw [← barX_gLBConj_eq 3 hbX, gLBConj_eq_of_mem_normalizer (Subgroup.le_normalizer hbN)]
  exact h1.trans h2.le

theorem cover_cyc
    {X B T J : Subgroup G} {b : G}
    (hF : X ⊓ Subgroup.centralizer (pCoreOf 2 X : Set G) ≤ pCoreOf 2 X)
    (hcyc : IsLThreeFourCubeCyc X b) (hB : IsEkIn 3 3 X B) (hT : IsMaxInvTwoSub X B T)
    (hbB : b ∈ B) (hb1 : b ≠ 1)
    (hJ : GLAPComponent 3 (GLAPLayer 3 (GLAPLayer 3 X ⊓ Subgroup.centralizer ({b} : Set G))) J)
    (hJ34 : IsLThreeFour (barOf 3 J)) (hinf : Subgroup.zpowers b ⊓ (B ⊓ J) = ⊥)
    (hsup : Subgroup.zpowers b ⊔ (B ⊓ J) = B) :
    Covers 3 X (Subgroup.normalizer (thompsonJ 2 T : Set G)) (GLAPLayer 3 X) ∨
      Covers 3 X (Subgroup.normalizer (omegaOne 2 (centerOf T) : Set G)) (GLAPLayer 3 X) := by
  obtain ⟨K₁, hK₁, hne, hlay, hK₁34⟩ := hcyc
  have hBX : B ≤ X := hB.1
  have hbX : b ∈ X := hBX hbB
  have hBel := hB.2.1
  have hb3 : b ^ 3 = 1 := hBel.2 b hbB
  have hB3 : IsPGroup 3 ↥B := hBel.isPGroup
  have hTX : T ≤ X := hT.1
  have hT2 : IsPGroup 2 ↥T := hT.2.1
  have hBT : B ≤ Subgroup.normalizer (T : Set G) := hT.2.2.1
  set K₂ := GLBConj b K₁ with hK₂def
  set K₃ := GLBConj b K₂ with hK₃def
  have hK₂ : GLAPComponent 3 X K₂ := Inputs1115.glaPComponent_conj_of_mem hK₁ hbX
  have hK₃ : GLAPComponent 3 X K₃ := Inputs1115.glaPComponent_conj_of_mem hK₂ hbX
  have hK₃₁ : GLBConj b K₃ = K₁ := by
    rw [hK₃def, hK₂def, gLBConj_gLBConj, gLBConj_gLBConj]
    have : b * (b * b) = 1 := by rw [← pow_three]; exact hb3
    rw [this, gLBConj_one]
  have h12 : K₁ ≠ K₂ := fun h => hne h.symm
  have h13 : K₁ ≠ K₃ := by
    intro h
    apply hne
    calc GLBConj b K₁ = GLBConj b K₃ := by rw [← h]
      _ = K₁ := hK₃₁
  have h23 : K₂ ≠ K₃ := by
    intro h
    apply hne
    have := congrArg (GLBConj b⁻¹) h
    rw [hK₃def, gLBConj_inv_gLBConj, hK₂def, gLBConj_inv_gLBConj] at this
    exact this.symm
  have hbT : b ∈ Subgroup.normalizer (T : Set G) := hBT hbB
  have hTK₁ : T ≤ Subgroup.normalizer (K₁ : Set G) := by
    rcases le_normalizer_of_three hTX hT2 hK₁ hK₂ hK₃ h12 h13 h23 hlay with h | h | h
    · exact h
    · have h1 := le_normalizer_gLBConj hbT (le_normalizer_gLBConj hbT h)
      rwa [hK₃₁] at h1
    · have h1 := le_normalizer_gLBConj hbT h
      rwa [hK₃₁] at h1
  have hlayN : GLAPLayer 3 X ≤ Subgroup.normalizer (K₁ : Set G) := by
    rw [hlay]
    exact sup_le (sup_le Subgroup.le_normalizer (Claims1115c.le_normalizer_of_ne hK₁ hK₂ h12))
      (Claims1115c.le_normalizer_of_ne hK₁ hK₃ h13)
  have hlayX : GLAPLayer 3 X ≤ X := sSup_le fun _ h => h.1
  have hJlay : J ≤ GLAPLayer 3 X := hJ.1.trans ((sSup_le fun _ h => h.1).trans inf_le_left)
  have hJX : J ≤ X := hJlay.trans hlayX
  have hB0X : B ⊓ J ≤ X := inf_le_left.trans hBX
  set E := barX 3 X K₁ with hE
  set Tb := barX 3 X T with hTb
  set B₀ := barX 3 X (B ⊓ J) with hB₀
  set bb : ↥X ⧸ GLAPPrimeCore 3 ↥X := QuotientGroup.mk' (GLAPPrimeCore 3 ↥X) ⟨b, hbX⟩ with hbb
  have hTE : Tb ≤ Subgroup.normalizer (E : Set (↥X ⧸ GLAPPrimeCore 3 ↥X)) :=
    barX_le_normalizer hTK₁
  have hB₀E : B₀ ≤ Subgroup.normalizer (E : Set (↥X ⧸ GLAPPrimeCore 3 ↥X)) :=
    barX_le_normalizer ((inf_le_right.trans hJlay).trans hlayN)
  have hB₀T : B₀ ≤ Subgroup.normalizer (Tb : Set (↥X ⧸ GLAPPrimeCore 3 ↥X)) :=
    barX_le_normalizer (inf_le_left.trans hBT)
  have hB₀9 : Nat.card B₀ = 9 := by
    rw [hB₀, Claims1115b.card_barX_of_isPGroup hB0X (hB3.to_le inf_le_left)]
    exact card_inf_eq_nine hB hbB hb1 hinf hsup
  have hBbel : IsElemAbelian 3 (barX 3 X B) := (hBel.subgroupOf X).map _
  have hbbB : bb ∈ barX 3 X B := Inputs1115.mk_mem_barX hbX hbB
  have hB₀B : B₀ ≤ barX 3 X B := Inputs1115.barX_le_barX inf_le_left
  have hlayb : barX 3 X (GLAPLayer 3 X) = E ⊔ (barX 3 X K₂ ⊔ barX 3 X K₃) := by
    rw [hlay, CFSG.HardMathSupport.Solomon.Coordinator.i183_barX_sup (sup_le hK₁.1 hK₂.1) hK₃.1,
      CFSG.HardMathSupport.Solomon.Coordinator.i183_barX_sup hK₁.1 hK₂.1, sup_assoc]
  have hK₂b : barX 3 X K₂ = GLBConj bb E := barX_gLBConj_eq 3 hbX K₁
  have hK₃b : barX 3 X K₃ = GLBConj bb (barX 3 X K₂) := barX_gLBConj_eq 3 hbX K₂
  have hcentE : barX 3 X K₂ ⊔ barX 3 X K₃ ≤
      Subgroup.centralizer (E : Set (↥X ⧸ GLAPPrimeCore 3 ↥X)) :=
    sup_le (Claims1115b.barX_le_centralizer_of_ne' hK₁ hK₂ h12)
      (Claims1115b.barX_le_centralizer_of_ne' hK₁ hK₃ h13)
  have hB₀lay : B₀ ≤ barX 3 X (GLAPLayer 3 X) :=
    Inputs1115.barX_le_barX (inf_le_right.trans hJlay)
  have hJlayb : barX 3 X J ≤ barX 3 X (GLAPLayer 3 X) := Inputs1115.barX_le_barX hJlay
  set NE : Subgroup (↥X ⧸ GLAPPrimeCore 3 ↥X) :=
    Subgroup.normalizer (E : Set (↥X ⧸ GLAPPrimeCore 3 ↥X)) with hNE
  set ρ : ↥NE →* MulAut ↥E := E.normalizerMonoidHom with hρ
  have hρ1 : ∀ (g : ↥NE) (w : ↥E), ((ρ g w : ↥E) : ↥X ⧸ GLAPPrimeCore 3 ↥X) =
      (g : ↥X ⧸ GLAPPrimeCore 3 ↥X) * (w : ↥X ⧸ GLAPPrimeCore 3 ↥X) *
        ((g : ↥X ⧸ GLAPPrimeCore 3 ↥X))⁻¹ :=
    fun g w => by rw [hρ, Subgroup.normalizerMonoidHom_apply_apply_coe]
  set B₀' : Subgroup ↥NE := B₀.subgroupOf NE with hB₀'
  set Bρ : Subgroup (MulAut ↥E) := B₀'.map ρ with hBρ
  have hcen : ∀ z : ↥E, (∀ w : ↥E, z * w = w * z) → z = 1 :=
    CFSG.HardMathSupport.Solomon.Coordinator.I28_8.center_trivial_of_isLThreeFour hK₁34
  have hconj_inj : Function.Injective (MulAut.conj : ↥E →* MulAut ↥E) := by
    rw [injective_iff_map_eq_one]
    intro z hz
    refine hcen z fun w => ?_
    have := congrArg (fun m : MulAut ↥E => m w) hz
    simp only [MulAut.conj_apply, MulAut.one_apply] at this
    calc z * w = (z * w * z⁻¹) * z := by group
      _ = w * z := by rw [this]
  have hinner : Bρ ≤ (MulAut.conj : ↥E →* MulAut ↥E).range := by
    rintro _ ⟨x, hx, rfl⟩
    have hxlay : (x : ↥X ⧸ GLAPPrimeCore 3 ↥X) ∈ barX 3 X (GLAPLayer 3 X) :=
      hB₀lay (Subgroup.mem_subgroupOf.1 hx)
    rw [hlayb] at hxlay
    have hxm : (x : ↥X ⧸ GLAPPrimeCore 3 ↥X) ∈
        ((E ⊔ (barX 3 X K₂ ⊔ barX 3 X K₃) : Subgroup (↥X ⧸ GLAPPrimeCore 3 ↥X)) :
          Set (↥X ⧸ GLAPPrimeCore 3 ↥X)) := hxlay
    rw [Subgroup.coe_mul_of_right_le_normalizer_left E _
      (hcentE.trans (Subgroup.centralizer_le_normalizer _))] at hxm
    obtain ⟨k, hk, r, hr, hkr⟩ := hxm
    refine ⟨⟨k, hk⟩, ?_⟩
    ext w
    rw [hρ1]
    simp only [MulAut.conj_apply, Subgroup.coe_mul, Subgroup.coe_inv]
    rw [← hkr]
    have hre : r * (w : ↥X ⧸ GLAPPrimeCore 3 ↥X) = w * r :=
      (Subgroup.mem_centralizer_iff.1 (hcentE hr) w w.2).symm
    calc k * (w : ↥X ⧸ GLAPPrimeCore 3 ↥X) * k⁻¹ = k * (r * w * r⁻¹) * k⁻¹ := by
          rw [hre, mul_inv_cancel_right]
      _ = k * r * w * (k * r)⁻¹ := by group
  have hρinj : ∀ x ∈ B₀', ρ x = 1 → x = 1 := by
    intro x hx hx1
    set y : ↥X ⧸ GLAPPrimeCore 3 ↥X := (x : ↥X ⧸ GLAPPrimeCore 3 ↥X) with hy
    have hyB₀ : y ∈ B₀ := Subgroup.mem_subgroupOf.1 hx
    have hyE : y ∈ Subgroup.centralizer (E : Set (↥X ⧸ GLAPPrimeCore 3 ↥X)) := by
      rw [Subgroup.mem_centralizer_iff]
      intro w hw
      have h1 := hρ1 x ⟨w, hw⟩
      rw [hx1, MulAut.one_apply] at h1
      change w = y * w * y⁻¹ at h1
      calc w * y = (y * w * y⁻¹) * y := by rw [← h1]
        _ = y * w := by group
    have hyb : y * bb = bb * y := by
      have := hBbel.1.is_comm.comm ⟨y, hB₀B hyB₀⟩ ⟨bb, hbbB⟩
      exact congrArg Subtype.val this
    have hy2 : y ∈ Subgroup.centralizer (barX 3 X K₂ : Set (↥X ⧸ GLAPPrimeCore 3 ↥X)) := by
      rw [hK₂b]; exact mem_centralizer_gLBConj hyb hyE
    have hy3 : y ∈ Subgroup.centralizer (barX 3 X K₃ : Set (↥X ⧸ GLAPPrimeCore 3 ↥X)) := by
      rw [hK₃b]; exact mem_centralizer_gLBConj hyb hy2
    have hylay : y ∈ Subgroup.centralizer
        (barX 3 X (GLAPLayer 3 X) : Set (↥X ⧸ GLAPPrimeCore 3 ↥X)) := by
      rw [hlayb]
      have := Claims1115c.le_centralizer_sup (P := E) (Q := barX 3 X K₂ ⊔ barX 3 X K₃)
        (R := Subgroup.zpowers y) ((Subgroup.zpowers_le).2 hyE)
        (Claims1115c.le_centralizer_sup ((Subgroup.zpowers_le).2 hy2)
          ((Subgroup.zpowers_le).2 hy3))
      exact this (Subgroup.mem_zpowers y)
    have hyJ : y ∈ barX 3 X J := Inputs1115.barX_le_barX inf_le_right hyB₀
    have hyJc : y ∈ Subgroup.centralizer (barX 3 X J : Set (↥X ⧸ GLAPPrimeCore 3 ↥X)) :=
      Subgroup.centralizer_le hJlayb hylay
    have hy3' : y ^ 3 = 1 := hBbel.2 y (hB₀B hyB₀)
    have h1 := eq_one_of_mem_center hJX hJ34 hyJ hyJc hy3'
    exact Subtype.ext h1
  set D : Subgroup (↥X ⧸ GLAPPrimeCore 3 ↥X) :=
    (Bρ.comap (MulAut.conj : ↥E →* MulAut ↥E)).map E.subtype with hD
  have hDE : D ≤ E := Subgroup.map_subtype_le _
  have hD9 : Nat.card D = 9 := by
    have h1 : Nat.card D = Nat.card (Bρ.comap (MulAut.conj : ↥E →* MulAut ↥E)) :=
      Subgroup.card_map_of_injective E.subtype_injective
    have h2 : Nat.card (Bρ.comap (MulAut.conj : ↥E →* MulAut ↥E)) = Nat.card Bρ := by
      have h := Subgroup.card_map_of_injective (f := (MulAut.conj : ↥E →* MulAut ↥E))
        (K := Bρ.comap (MulAut.conj : ↥E →* MulAut ↥E)) hconj_inj
      rw [Subgroup.map_comap_eq_self hinner] at h
      exact h.symm
    have h3 : Nat.card Bρ = Nat.card B₀' := by
      set f : ↥B₀' →* MulAut ↥E := ρ.comp B₀'.subtype with hf
      have hfinj : Function.Injective f := by
        rw [injective_iff_map_eq_one]
        intro z hz
        exact Subtype.ext (hρinj z z.2 hz)
      have hrange : f.range = Bρ := by
        rw [hf, MonoidHom.range_comp, Subgroup.range_subtype]
      rw [← hrange]
      exact (Nat.card_congr (MonoidHom.ofInjective hfinj).toEquiv).symm
    have h4 : Nat.card B₀' = Nat.card B₀ :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hB₀E).toEquiv
    rw [h1, h2, h3, h4, hB₀9]
  have hDT : ∀ d ∈ D, ∀ t ∈ Tb, ∃ t' ∈ Tb, ∀ k ∈ E,
      d * t * d⁻¹ * k * (d * t * d⁻¹)⁻¹ = t' * k * t'⁻¹ := by
    rintro _ ⟨e, he, rfl⟩ t ht
    obtain ⟨x, hx, hxe⟩ := he
    have hxB₀ : (x : ↥X ⧸ GLAPPrimeCore 3 ↥X) ∈ B₀ := Subgroup.mem_subgroupOf.1 hx
    have hxE : ∀ w ∈ E, (x : ↥X ⧸ GLAPPrimeCore 3 ↥X) * w * ((x : ↥X ⧸ GLAPPrimeCore 3 ↥X))⁻¹ =
        (e : ↥X ⧸ GLAPPrimeCore 3 ↥X) * w * ((e : ↥X ⧸ GLAPPrimeCore 3 ↥X))⁻¹ := by
      intro w hw
      have h1 := congrArg (fun m : MulAut ↥E => ((m ⟨w, hw⟩ : ↥E) : ↥X ⧸ GLAPPrimeCore 3 ↥X)) hxe
      simp only [hρ1, MulAut.conj_apply, Subgroup.coe_mul, Subgroup.coe_inv] at h1
      exact h1
    refine ⟨(x : ↥X ⧸ GLAPPrimeCore 3 ↥X) * t * ((x : ↥X ⧸ GLAPPrimeCore 3 ↥X))⁻¹,
      (Subgroup.mem_normalizer_iff.1 (hB₀T hxB₀) t).1 ht, fun k hk => ?_⟩
    exact conj_act_eq x.2 (hTE ht) hxE hk
  have hTb2 : IsPGroup 2 ↥Tb := (hT2.of_equiv (Subgroup.subgroupOfEquivOfLe hTX).symm).map _
  have hdich := l34FactsAut hK₁34 hTb2 hTE hDE hD9 hDT
  have hext : ∀ T₀ : Subgroup G, IsCharIn T₀ T → E ≤ barX 3 X (Subgroup.normalizer (T₀ : Set G)) →
      barX 3 X (GLAPLayer 3 X) ≤ barX 3 X (Subgroup.normalizer (T₀ : Set G)) := by
    intro T₀ hchar h
    have hbN : b ∈ Subgroup.normalizer (T₀ : Set G) :=
      Lemma1115.mem_normalizer_of_isCharIn hchar hbT
    have h2 := barX_gLBConj_le hbX hbN h
    have h3 := barX_gLBConj_le hbX hbN h2
    rw [hlayb]
    exact sup_le h (sup_le h2 h3)
  rcases cover_of_dichotomy hF hBX hB3 hT hdich with h | h
  · exact Or.inl (hext _ (Claims1115c.isCharIn_thompsonJ T) h)
  · exact Or.inr (hext _ (Claims1115c.isCharIn_omegaOne_center T) h)

end Triple

section Main

@[expose] def Input28_9Cyc : Prop :=
  ∀ {G : Type} [Group G] [Finite G] (X B T J : Subgroup G) (b : G),
    X ⊓ Subgroup.centralizer (pCoreOf 2 X : Set G) ≤ pCoreOf 2 X →
    (IsLThreeFour ↥(barX 3 X (GLAPLayer 3 X)) ∨
      IsCatalogLieIso ↥(barX 3 X (GLAPLayer 3 X)) IsL364Index ∨
      IsCatalogLieIso ↥(barX 3 X (GLAPLayer 3 X)) Is3D44Index ∨
      IsLThreeFourCubeCyc X b) →
    IsEkIn 3 3 X B → IsMaxInvTwoSub X B T → b ∈ B → b ≠ 1 →
    GLAPComponent 3 (GLAPLayer 3 (GLAPLayer 3 X ⊓ Subgroup.centralizer ({b} : Set G))) J →
    IsLThreeFour (barOf 3 J) → Subgroup.zpowers b ⊓ (B ⊓ J) = ⊥ →
    Subgroup.zpowers b ⊔ (B ⊓ J) = B →
    Covers 3 X (Subgroup.normalizer (thompsonJ 2 T : Set G)) (GLAPLayer 3 X) ∨
      Covers 3 X (Subgroup.normalizer (omegaOne 2 (centerOf T) : Set G)) (GLAPLayer 3 X)

theorem input28_9Cyc_of_facts
    (h364 : CoverFactsL364) (h3D4 : CoverFacts3D44) : Input28_9Cyc := by
  intro G _ _ X B T J b hF htype hB hT hbB hb1 hJ hJ34 hinf hsup
  rcases htype with h | h | h | h
  · exact cover_single h364 h3D4 hF (Or.inl h) hB hT hbB hb1 hJ hJ34 hinf hsup
  · exact cover_single h364 h3D4 hF (Or.inr (Or.inl h)) hB hT hbB hb1 hJ hJ34 hinf hsup
  · exact cover_single h364 h3D4 hF (Or.inr (Or.inr h)) hB hT hbB hb1 hJ hJ34 hinf hsup
  · exact cover_cyc hF h hB hT hbB hb1 hJ hJ34 hinf hsup

end Main

section PushUp

variable {G : Type} [Group G] [Finite G] {M E A K H : Subgroup G} {a : G} {K' : Subgroup G}

theorem types_XCyc {m : ℕ}
    {B : Subgroup G} (h : Cex117 G m 3 B M E A a K) (h1111 : Lemma1111Statement)
    (h104v : Lemma104_vStatement) (h111 : Prop111Statement)
    (hup34 : CFSG.HardMathSupport.Dickson.Sec6.Up34Statement)
    (hD44 : Claims1115b.Seitz2310D44Inner) (h102 : Claims1115b.Input10_2D44)
    (hZ3D4 : Claims1115c.Centre3D44) (S : Claims1115b.Sit M E A K H a K') {X : Subgroup G}
    (hJX : Lemma1115.jLayer a H ≤ X) (hXH : X ≤ H) (hlayer : GLAPLayer 3 X = Lemma1115.jLayer a H) :
    IsLThreeFour ↥(barX 3 X (GLAPLayer 3 X)) ∨
      IsCatalogLieIso ↥(barX 3 X (GLAPLayer 3 X)) IsL364Index ∨
      IsCatalogLieIso ↥(barX 3 X (GLAPLayer 3 X)) Is3D44Index ∨
      IsLThreeFourCubeCyc X a := by
  have hp : Nat.Prime 3 := Nat.prime_three
  rcases S.cases with ⟨L, hL, -, hJ⟩ | ⟨L, c, hJ⟩
  · rcases S.types_X h h1111 h104v h111 hup34 hD44 h102 hZ3D4 hJX hXH hlayer with h1 | h2 | h3 |
      ⟨K₁, K₂, -, hK₁, hK₂, -, h12, -⟩
    · exact Or.inl h1
    · exact Or.inr (Or.inl h2)
    · exact Or.inr (Or.inr (Or.inl h3))
    · exfalso
      have hLX : GLAPComponent 3 X L := glaPComponent_of_le hp hL (hJ ▸ hJX) hXH
      have hone : ∀ L' : Subgroup G, GLAPComponent 3 X L' → L' = L := by
        intro L' hL'
        have hmem := mem_of_le_sSup (𝒦 := {L}) hL'
          (fun K₀ hK₀ => (Set.mem_singleton_iff.1 hK₀) ▸ hLX) (by
            rw [sSup_singleton, ← hJ, ← hlayer]
            exact le_sSup hL')
        exact Set.mem_singleton_iff.1 hmem
      exact h12 ((hone K₁ hK₁).trans (hone K₂ hK₂).symm)
  · refine Or.inr (Or.inr (Or.inr ?_))
    have hL : GLAPComponent 3 H L := c.hM
    have hJX' : L ⊔ GLBConj a L ⊔ GLBConj a (GLBConj a L) ≤ X := hJ ▸ hJX
    have hK₁ := glaPComponent_of_le hp hL ((le_sup_left.trans le_sup_left).trans hJX') hXH
    have h34 : IsLThreeFour (barOf 3 L) := by
      have hZ := S.center_eq_bot_triple c hJ
      have eZ : (barOf 3 L ⧸ Subgroup.center (barOf 3 L)) ≃* barOf 3 L :=
        (QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot
      obtain ⟨F, hF, hFf, hcF, ⟨f⟩⟩ := S.triple_type c hJ
      exact ⟨F, hF, hFf, hcF, ⟨eZ.symm.trans f⟩⟩
    have hbar : IsLThreeFour ↥(barX 3 X L) := by
      obtain ⟨F, hF, hFf, hcF, ⟨f⟩⟩ := h34
      exact ⟨F, hF, hFf, hcF, ⟨(quotEquivBarX hp hK₁.1 hK₁.2.1).symm.trans f⟩⟩
    exact ⟨L, hK₁, c.h1, by rw [hlayer, hJ], hbar⟩

theorem input1115PushUp_of_inputsCyc
    (hS : CFSG.ComponentClassification.CatalogueRelativeB.CatalogueSchreier)
    (h1111 : Lemma1111Statement) (h119 : Lemma119Statement) (h1112 : Lemma1112Statement)
    (h104v : Lemma104_vStatement) (h111 : Prop111Statement)
    (hup34 : CFSG.HardMathSupport.Dickson.Sec6.Up34Statement)
    (hD44 : Claims1115b.Seitz2310D44Inner) (h102 : Claims1115b.Input10_2D44)
    (hZ3D4 : Claims1115c.Centre3D44) (h289 : Input28_9Cyc) : Lemma1115.Input1115PushUp := by
  intro G _ _ m B M E A a K h H hH T hT hTN
  obtain ⟨K', S⟩ := Claims1115b.exists_sit hS h1111 h119 h1112 h hH
  obtain ⟨𝒞, hJ⟩ := S.exists_isJoin
  have hsec : Sec11 G m 3 B M E A := h.toCex117Base.toSec11
  have hAH : A ≤ H := S.hAH
  have hTH : T ≤ H := hT.1
  have hT2 : IsPGroup 2 ↥T := hT.2.1
  have hAT : A ≤ Subgroup.normalizer (T : Set G) := hT.2.2.1
  have hAab : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x :=
    CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.T29.comm_of_isElemAbelian S.cfg.hAel
  have hAC : A ≤ Cg a := fun x hx =>
    Subgroup.mem_centralizer_singleton_iff.2 (hAab x hx a S.cfg.ha)
  have hAN : A ≤ Subgroup.normalizer (Lemma1115.jLayer a H : Set G) :=
    Claims1115c.A_le_normalizer_jLayer hAH hAC
  have hOH : GLAPPrimeCoreOf 3 H ≤ H := Subgroup.map_subtype_le _
  set X := GLAPPrimeCoreOf 3 H ⊔ Lemma1115.jLayer a H ⊔ T ⊔ A with hXdef
  have hXH : X ≤ H := sup_le (sup_le (sup_le hOH hJ.le) hTH) hAH
  have hOX : GLAPPrimeCoreOf 3 H ≤ X := le_sup_left.trans (le_sup_left.trans le_sup_left)
  have hJX : Lemma1115.jLayer a H ≤ X := le_sup_right.trans (le_sup_left.trans le_sup_left)
  have hTX : T ≤ X := le_sup_right.trans le_sup_left
  have hAX : A ≤ X := le_sup_right
  have hlayer : GLAPLayer 3 X = Lemma1115.jLayer a H :=
    Claims1115c.layer_eq_of_join hJ hT2 hTH hAH hTN hAN hAT hAab
  have hFstar := Claims1115c.centralizer_pCore_le hH.1 hsec.standing.charTwo hXH hOX
  have htypes := types_XCyc h h1111 h104v h111 hup34 hD44 h102 hZ3D4 S hJX hXH hlayer
  have hEk : IsEkIn 3 3 X A := ⟨hAX, S.cfg.hAel, by rw [S.cfg.hA27]; norm_num⟩
  have hTX' : IsMaxInvTwoSub X A T := ⟨hTX, hT2, hAT, fun T' hT'X hT'2 hAT' hTT' =>
    hT.2.2.2 T' (hT'X.trans hXH) hT'2 hAT' hTT'⟩
  have hK'c : GLAPComponent 3
      (GLAPLayer 3 (GLAPLayer 3 X ⊓ Subgroup.centralizer ({a} : Set G))) K' := by
    rw [hlayer]
    have h1 : GLAPComponent 3 (Lemma1115.jLayer a H ⊓ Subgroup.centralizer ({a} : Set G)) K' :=
      glaPComponent_of_le Nat.prime_three S.hK'
        (le_inf S.K'_le_jLayer (S.hK'.1.trans inf_le_right))
        (inf_le_inf_right _ (Inputs1115.jLayer_le H))
    exact glaPComponent_of_le Nat.prime_three h1 (le_sSup h1) (sSup_le fun _ h => h.1)
  have hconc := h289 X A T K' a hFstar htypes hEk hTX' S.cfg.ha S.cfg.ha1 hK'c
    (Claims1115b.isLThreeFour_barOf_K' S.cfg S.hK' S.hbar) S.zpowers_inf S.zpowers_sup
  rw [hlayer] at hconc
  have hT0 : T ≠ ⊥ := Claims1115c.ne_bot_of_isMaxInvTwoSub hH.1 hAH hT
  rcases hconc with hc | hc
  · exact ⟨thompsonJ 2 T, Claims1115c.thompsonJ_ne_bot hT2 hT0, Claims1115c.isCharIn_thompsonJ T,
      Claims1115c.covers_of_covers_sub hJ hJX hXH hc⟩
  · exact ⟨omegaOne 2 (centerOf T), Claims1115c.omegaOne_center_ne_bot hT2 hT0,
      Claims1115c.isCharIn_omegaOne_center T, Claims1115c.covers_of_covers_sub hJ hJX hXH hc⟩

theorem input1115PushUp_of_leavesCyc
    (hS : CFSG.ComponentClassification.CatalogueRelativeB.CatalogueSchreier)
    (h1111 : Lemma1111Statement) (h119 : Lemma119Statement) (h1112 : Lemma1112Statement)
    (h104v : Lemma104_vStatement) (h111 : Prop111Statement)
    (hup34 : CFSG.HardMathSupport.Dickson.Sec6.Up34Statement) (h364 : CoverFactsL364)
    (h3D4 : CoverFacts3D44) : Lemma1115.Input1115PushUp :=
  input1115PushUp_of_inputsCyc hS h1111 h119 h1112 h104v h111 hup34
    Claims1115c.seitz2310D44Inner_holds Claims1115c.input10_2D44_holds Claims1115c.centre3D44_holds
    (input28_9Cyc_of_facts h364 h3D4)

end PushUp

end CFSG.LocalAnalysis.GLTheoremB.MovingAround.Input289

end
