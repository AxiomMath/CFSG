module

public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallDefs
import CFSG.LocalAnalysis.AGLEmbedding.LinTwoCompetitorAux
import CFSG.LocalAnalysis.AGLEmbedding.OneLieCompetitorReduced
import CFSG.LocalAnalysis.AGLEmbedding.OneSmallBOneChar
import CFSG.LocalAnalysis.AGLEmbedding.OneSmallGEVCoverStar
import CFSG.LocalAnalysis.AGLEmbedding.UPrimeComponents

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.PreuniquenessRankFour.Helpers
open CFSG.RankThreeCoreUniqueness.Helpers
open CFSG.ComponentClassification.OuterAutomorphisms

variable {G : Type} [Group G] [Finite G] {p : ℕ} {P : Sylow p G} {M H R : Subgroup G}
  {Rbar : Sylow p (H ⧸ primeComplementCore (G := H) p)}
  {K : Subgroup (H ⧸ primeComplementCore (G := H) p)}

theorem D1OneSmallData.d1X0_subgroupOf_eq_glbCore (hd : D1OneSmallData p P M H R Rbar K)
    {T₁ : Sylow p K} (hT₁ : (T₁ : Subgroup K).map K.subtype =
      (Rbar : Subgroup (H ⧸ primeComplementCore (G := H) p)) ⊓ K)
    (hUP : KFactUPrime p K) : (d1X0 p M H).subgroupOf K = GLBCore p 1 (T₁ : Subgroup K) := by
  have hp := hd.cfg.red.prime
  have : Fact p.Prime := ⟨hp⟩
  set X₀ := d1X0 p M H
  obtain ⟨z, hzR, hzK, hzp, hzc⟩ := hd.z
  obtain ⟨hN, hKX₀⟩ := hd.cfg.red.rankOne_principle hd.comp hd.noncyclic hzR hzK hzp hzc
  have hne := hd.cfg.red.glbCore_ne_top_of_rankOne hN hKX₀ hT₁
  have hΓX : (GLBCore p 1 (T₁ : Subgroup K)).map K.subtype ≤ X₀ :=
    glbCore_map_le_of_normalizer_le hp hT₁ hN
  rcases (hUP T₁ hne).1 (X₀.comap K.subtype) (Subgroup.map_le_iff_le_comap.mp hΓX) with h | h
  · exact h
  · exact absurd (fun k hk => (Subgroup.mem_comap.mp (h.ge (Subgroup.mem_top ⟨k, hk⟩)) :)) hKX₀

theorem D1OneSmallData.le_centralizer_of_perfect_of_eq (hd : D1OneSmallData p P M H R Rbar K)
    {T₁ : Sylow p K} (hY : (d1X0 p M H).subgroupOf K = GLBCore p 1 (T₁ : Subgroup K))
    (hout : Group.IsSolvable (Outer K))
    (hs : Group.IsSolvable (GLBCore p 1 (T₁ : Subgroup K)))
    {W : Subgroup (H ⧸ primeComplementCore (G := H) p)} (hWX : W ≤ d1X0 p M H)
    (hWp : ⁅W, W⁆ = W) :
    W ≤ Subgroup.centralizer (K : Set (H ⧸ primeComplementCore (G := H) p)) := by
  set X₀ := d1X0 p M H
  have hKn : K.Normal := hd.cfg.red.normal_of_rankOne hd.comp hd.noncyclic
  obtain ⟨z, hzR, hzK, hzp, hzc⟩ := hd.z
  have hcomap : X₀.comap K.subtype = GLBCore p 1 (T₁ : Subgroup K) := hY
  have hKX : K ⊓ X₀ = (GLBCore p 1 (T₁ : Subgroup K)).map K.subtype := by
    rw [← hcomap, Subgroup.map_comap_eq, Subgroup.range_subtype, inf_comm]
  have hKXs : Group.IsSolvable (K ⊓ X₀ : Subgroup (H ⧸ primeComplementCore (G := H) p)) := by
    rw [hKX]
    exact Group.isSolvable_of_surjective (f := ((GLBCore p 1 (T₁ : Subgroup K)).equivMapOfInjective
      K.subtype K.subtype_injective).toMonoidHom) (MulEquiv.surjective _)
  set C := Subgroup.centralizer (K : Set (H ⧸ primeComplementCore (G := H) p))
  have hWKC : W ≤ K ⊔ C := le_sup_centralizer_of_isPerfect (Subgroup.isPerfect_iff.mpr hWp) hout
  have hCX : C ≤ X₀ := hd.cfg.red.centralizer_le_of_rankOne hd.noncyclic hzR hzK hzp hzc
  have hCn : C.Normal := Subgroup.normal_centralizer
  set φ := QuotientGroup.mk' C
  have hφ : W.map φ ≤ (K ⊓ X₀).map φ := by
    rintro _ ⟨u, hu, rfl⟩
    obtain ⟨k, hk, c, hc, rfl⟩ := Subgroup.mem_sup_of_normal_left.mp (hWKC hu)
    have hkX : k ∈ X₀ := by
      have := X₀.mul_mem (hWX hu) (X₀.inv_mem (hCX hc))
      simpa using this
    refine ⟨k, ⟨hk, hkX⟩, ?_⟩
    have hc1 : φ c = 1 := (QuotientGroup.eq_one_iff c).mpr hc
    change φ k = φ (k * c)
    rw [map_mul, hc1, mul_one]
  have hsolφ : Group.IsSolvable ((K ⊓ X₀).map φ) :=
    Group.isSolvable_of_surjective (φ.subgroupMap_surjective (K ⊓ X₀))
  have hsolU : Group.IsSolvable (W.map φ) :=
    Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective hφ)
  have hWφ : W.map φ = ⊥ := by
    by_contra hne'
    have : Nontrivial (W.map φ) := (Subgroup.nontrivial_iff_ne_bot _).mpr hne'
    have : Group.IsPerfect (W.map φ) :=
      Subgroup.isPerfect_iff.mpr (by rw [← Subgroup.map_commutator, hWp])
    exact Group.IsPerfect.not_isSolvable _ hsolU
  rwa [Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk'] at hWφ

theorem D1OneSmallData.le_centralizer_of_perfect (hd : D1OneSmallData p P M H R Rbar K)
    {T₁ : Sylow p K} (hT₁ : (T₁ : Subgroup K).map K.subtype =
      (Rbar : Subgroup (H ⧸ primeComplementCore (G := H) p)) ⊓ K)
    (hUP : KFactUPrime p K) (hout : Group.IsSolvable (Outer K))
    (hs : Group.IsSolvable (GLBCore p 1 (T₁ : Subgroup K)))
    {W : Subgroup (H ⧸ primeComplementCore (G := H) p)} (hWX : W ≤ d1X0 p M H)
    (hWp : ⁅W, W⁆ = W) :
    W ≤ Subgroup.centralizer (K : Set (H ⧸ primeComplementCore (G := H) p)) :=
  hd.le_centralizer_of_perfect_of_eq (hd.d1X0_subgroupOf_eq_glbCore hT₁ hUP) hout hs hWX hWp

theorem D1OneSmallData.card_le_of_le_centralizer (hd : D1OneSmallData p P M H R Rbar K)
    (hR : Nat.card R ≤ p * Nat.card ((Rbar : Subgroup (H ⧸ primeComplementCore (G := H) p)) ⊓ K :
      Subgroup (H ⧸ primeComplementCore (G := H) p)))
    {Q : Subgroup (H ⧸ primeComplementCore (G := H) p)}
    (hQC : Q ≤ Subgroup.centralizer (K : Set (H ⧸ primeComplementCore (G := H) p)))
    (hQp : IsPGroup p Q) : Nat.card Q ≤ p := by
  have hp := hd.cfg.red.prime
  have : Fact p.Prime := ⟨hp⟩
  set C := Subgroup.centralizer (K : Set (H ⧸ primeComplementCore (G := H) p))
  have hKn : K.Normal := hd.cfg.red.normal_of_rankOne hd.comp hd.noncyclic
  have hCn : C.Normal := Subgroup.normal_centralizer
  obtain ⟨Tc, hTc⟩ := CFSG.Walter.exists_sylow_map_eq_inf_of_isSubnormal Rbar hCn.isSubnormal
  have h1 : Nat.card Q ≤ Nat.card ((Rbar : Subgroup _) ⊓ C : Subgroup _) := by
    rw [← hTc]
    exact card_le_card_map_sylow Tc hQp hQC
  have hKC : K ⊓ C = ⊥ := inf_centralizer_eq_bot_of_center hd.center
  have hdisj : ((Rbar : Subgroup (H ⧸ primeComplementCore (G := H) p)) ⊓ K) ⊓
      ((Rbar : Subgroup _) ⊓ C) = ⊥ := by
    rw [eq_bot_iff, ← hKC]
    exact le_inf (inf_le_left.trans inf_le_right) (inf_le_right.trans inf_le_right)
  have h2 := mul_card_le_of_inf_eq_bot inf_le_left inf_le_left hdisj
  rw [card_rbar_eq hd.cfg] at h2
  have hpos : 0 < Nat.card ((Rbar : Subgroup (H ⧸ primeComplementCore (G := H) p)) ⊓ K :
      Subgroup (H ⧸ primeComplementCore (G := H) p)) := Nat.card_pos
  have h3 : Nat.card ((Rbar : Subgroup _) ⊓ C : Subgroup _) ≤ p :=
    Nat.le_of_mul_le_mul_left (h2.trans (hR.trans_eq (mul_comm _ _))) hpos
  exact h1.trans h3

theorem not_sq_dvd_of_card_le {X : Type*} [Group X] [Finite X] [Fact p.Prime] {W : Subgroup X}
    (hW : ∀ Q : Subgroup X, Q ≤ W → IsPGroup p Q → Nat.card Q ≤ p) : ¬ p ^ 2 ∣ Nat.card W := by
  intro h
  obtain ⟨Q, hQ⟩ := Sylow.exists_subgroup_card_pow_prime (G := W) p h
  have hQp : IsPGroup p Q := IsPGroup.of_card hQ
  have h1 := hW (Q.map W.subtype) (Subgroup.map_subtype_le Q) (hQp.map _)
  rw [Subgroup.card_map_of_injective W.subtype_injective, hQ] at h1
  have := (Fact.out : p.Prime).two_le
  nlinarith

theorem exists_barM_hom_of (hph : D1PhaseThree p P M H R) :
    ∃ θ : ↥(barM M (H ⊓ M)) →* H ⧸ primeComplementCore (G := H) p,
      p.Coprime (Nat.card θ.ker) ∧ ∀ (m : ↥M) (hmH : (m : G) ∈ H)
        (hm : QuotientGroup.mk' (CFSG.pCore 2 ↥M) m ∈ barM M (H ⊓ M)),
        θ ⟨QuotientGroup.mk' (CFSG.pCore 2 ↥M) m, hm⟩ =
          QuotientGroup.mk' (primeComplementCore (G := H) p) ⟨m, hmH⟩ := by
  have hQ : pCoreOf 2 M ≤ GLBPrimeCore p H :=
    (hph.twoCore_M_le hph.twoCore_inf).trans (pCoreOf_le_glbPrimeCore Nat.prime_two
      ((Nat.coprime_primes hph.prime Nat.prime_two).mpr hph.ne_two) H)
  set A := H ⊓ M
  set mkM := QuotientGroup.mk' (CFSG.pCore 2 ↥M)
  set π := QuotientGroup.mk' (primeComplementCore (G := H) p)
  set α : ↥A →* ↥(barM M A) := (mkM.comp (Subgroup.inclusion inf_le_right)).codRestrict
    (barM M A) fun a => ⟨Subgroup.inclusion inf_le_right a, Subgroup.mem_subgroupOf.mpr a.2, rfl⟩
  set β : ↥A →* H ⧸ primeComplementCore (G := H) p := π.comp (Subgroup.inclusion inf_le_left)
  have hsurj : Function.Surjective α := by
    rintro ⟨_, ⟨m, hm, rfl⟩⟩
    exact ⟨⟨m, Subgroup.mem_subgroupOf.mp hm⟩, rfl⟩
  have hker : α.ker ≤ β.ker := by
    intro a ha
    have h1 : mkM (Subgroup.inclusion inf_le_right a) = 1 :=
      congrArg Subtype.val ((MonoidHom.mem_ker).mp ha)
    have h2 := hQ (coe_mem_pCoreOf_two_of_mk_eq_one _ h1)
    exact (MonoidHom.mem_ker).mpr ((mk'_primeComplementCore_eq_one_iff p _).mpr h2)
  set θ := (α.liftOfRightInverse (Function.surjInv hsurj) (Function.rightInverse_surjInv hsurj))
    ⟨β, hker⟩
  have hθ : ∀ a : ↥A, θ (α a) = β a := fun a =>
    MonoidHom.liftOfRightInverse_comp_apply _ _ _ _ a
  refine ⟨θ, ?_, fun m hmH hm => ?_⟩
  · have hle : θ.ker ≤ β.ker.map α := by
      intro x hx
      obtain ⟨a, rfl⟩ := hsurj x
      exact ⟨a, (MonoidHom.mem_ker).mpr (by rw [← hθ]; exact (MonoidHom.mem_ker).mp hx), rfl⟩
    have hβ : β.ker.map A.subtype ≤ GLBPrimeCore p H := by
      rintro _ ⟨a, ha, rfl⟩
      exact (mk'_primeComplementCore_eq_one_iff p _).mp ((MonoidHom.mem_ker).mp ha)
    have h1 : Nat.card β.ker ∣ Nat.card (GLBPrimeCore p H) := by
      rw [← Subgroup.card_map_of_injective A.subtype_injective]
      exact Subgroup.card_dvd_of_le hβ
    exact Nat.Coprime.coprime_dvd_right ((Subgroup.card_dvd_of_le hle).trans
      ((Subgroup.card_map_dvd _ _).trans h1)) (glbPrimeCore_coprime p H)
  · have hmA : (m : G) ∈ A := ⟨hmH, m.2⟩
    have h1 : α ⟨m, hmA⟩ = ⟨mkM m, hm⟩ := rfl
    rw [← h1, hθ]
    rfl

theorem D1OneSmallData.perf_barM_of_eq (hd : D1OneSmallData p P M H R Rbar K)
    (hph : D1PhaseThree p P M H R) {T₁ : Sylow p K}
    (hY : (d1X0 p M H).subgroupOf K = GLBCore p 1 (T₁ : Subgroup K))
    (hout : Group.IsSolvable (Outer K))
    (hs : Group.IsSolvable (GLBCore p 1 (T₁ : Subgroup K)))
    (hR : Nat.card R ≤ p * Nat.card ((Rbar : Subgroup (H ⧸ primeComplementCore (G := H) p)) ⊓ K :
      Subgroup (H ⧸ primeComplementCore (G := H) p))) :
    ∀ V : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M), V ≤ barM M (H ⊓ M) → ⁅V, V⁆ = V →
      ¬ p ^ 2 ∣ Nat.card V := by
  have hp := hd.cfg.red.prime
  have : Fact p.Prime := ⟨hp⟩
  intro V hVB hVp
  set B := barM M (H ⊓ M)
  obtain ⟨θ, hθk, hθ⟩ := exists_barM_hom_of hph
  set V' := V.subgroupOf B
  set U := V'.map θ
  have hV'p : ⁅V', V'⁆ = V' := by
    apply Subgroup.map_injective B.subtype_injective
    rw [Subgroup.map_commutator, Subgroup.map_subgroupOf_eq_of_le hVB, hVp]
  have hUp : ⁅U, U⁆ = U := by rw [← Subgroup.map_commutator, hV'p]
  have hUX : U ≤ d1X0 p M H := by
    rintro _ ⟨x, -, rfl⟩
    obtain ⟨m, hm, hmx⟩ := x.2
    have hmA := Subgroup.mem_subgroupOf.mp hm
    have hx : x = ⟨QuotientGroup.mk' (CFSG.pCore 2 ↥M) m, hmx ▸ x.2⟩ := Subtype.ext hmx.symm
    rw [hx, hθ m hmA.1]
    exact ⟨⟨m, hmA.1⟩, Subgroup.mem_subgroupOf.mpr hmA, rfl⟩
  have hUC := D1OneSmallData.le_centralizer_of_perfect_of_eq hd hY hout hs hUX hUp
  have hθk' : ∀ y, θ y = 1 → p.Coprime (orderOf y) := fun y hy =>
    hθk.coprime_dvd_right (by
      have := Subgroup.orderOf_dvd_natCard θ.ker (x := y) hy
      exact this)
  refine not_sq_dvd_of_card_le fun Q hQV hQp => ?_
  set Q' := Q.subgroupOf B
  have hQ'p : IsPGroup p Q' := hQp.comap_subtype
  have hQ'U : Q'.map θ ≤ U := Subgroup.map_mono fun q hq =>
    Subgroup.mem_subgroupOf.mpr (hQV (Subgroup.mem_subgroupOf.mp hq))
  have h1 := D1OneSmallData.card_le_of_le_centralizer hd hR (hQ'U.trans hUC) (hQ'p.map θ)
  rw [card_map_of_coprime θ hθk' hQ'p] at h1
  rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (hQV.trans hVB)).toEquiv] at h1

theorem D1OneSmallData.perf_barM (hd : D1OneSmallData p P M H R Rbar K)
    (hph : D1PhaseThree p P M H R) {T₁ : Sylow p K}
    (hT₁ : (T₁ : Subgroup K).map K.subtype =
      (Rbar : Subgroup (H ⧸ primeComplementCore (G := H) p)) ⊓ K)
    (hUP : KFactUPrime p K) (hout : Group.IsSolvable (Outer K))
    (hs : Group.IsSolvable (GLBCore p 1 (T₁ : Subgroup K)))
    (hR : Nat.card R ≤ p * Nat.card ((Rbar : Subgroup (H ⧸ primeComplementCore (G := H) p)) ⊓ K :
      Subgroup (H ⧸ primeComplementCore (G := H) p))) :
    ∀ V : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M), V ≤ barM M (H ⊓ M) → ⁅V, V⁆ = V →
      ¬ p ^ 2 ∣ Nat.card V :=
  hd.perf_barM_of_eq hph (hd.d1X0_subgroupOf_eq_glbCore hT₁ hUP) hout hs hR

end CFSG.AGLEmbedding
