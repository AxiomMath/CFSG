module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec4InputsEndS4
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec4GL32
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec4EndS3

public section

namespace CFSG.ComponentClassification.GrSLit.GrS4

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
  CFSG.ComponentClassification.UnbalancedCorr

variable {G : Type} [Group G] [Finite G]

theorem exists_conj_eq_of_transvection (hT : L34EightTransvectionFact)
    (hSq : L34OutSquareFact) {a : G} {J S B : Subgroup G} (hJper : ⁅J, J⁆ = J)
    (hL34 : IsL34Type (J ⧸ Open.fusionZStar J)) (hSJ : S ≤ normalizer (J : Set G))
    (hSyl : ∃ P : Sylow 2 G, (P : Subgroup G) = S) (hcent : ∀ s ∈ S, s * a = a * s)
    (hP : IsSylowTwoIn (S ⊓ J) J) (hZc : IsCyclic ↥(S ⊓ zStarIn J))
    (hZ4 : Nat.card ↥(S ⊓ zStarIn J) = 4) (haZ : a ∈ S ⊓ zStarIn J) (haa : a * a = 1)
    (ha1 : a ≠ 1) (hinv : ∀ y ∈ S ⊓ withKernel J, y * y = 1 → y ∈ S ⊓ J)
    (hcls : ∀ y ∈ S ⊓ J, y * y = 1 → y ≠ 1 → ∃ g : G, y = g⁻¹ * a * g)
    (hBP : B ≤ S ⊓ J) (hB8 : IsEightGroup B)
    (hBsq : B ≤ closure {t | ∃ s ∈ S ⊓ J ⊓ centralizer (B : Set G), t = s * s})
    (σ : ↥B ≃* ↥B) {c : G} (hcB : c ∈ B) (hσ : ∀ y : ↥B, (y : G)⁻¹ * (σ y : G) ∈ zpowers c) :
    ∃ n : G, ∀ y : ↥B, n⁻¹ * (y : G) * n = (σ y : G) := by
  by_cases hc1 : c = 1
  · refine ⟨1, fun y => ?_⟩
    have h1 := hσ y
    rw [hc1, zpowers_one_eq_bot, mem_bot] at h1
    rw [inv_one, one_mul, mul_one]
    exact inv_mul_eq_one.mp h1
  obtain ⟨g, hg⟩ := hcls c (hBP hcB) (hB8.1.2 c hcB) hc1
  obtain ⟨P, hPS⟩ := hSyl
  have hS2 : IsPGroup 2 S := hPS ▸ P.isPGroup'
  set T : Subgroup G := S ⊓ centralizer (B : Set G) with hTdef
  have hSC : (P : Subgroup G) ≤ centralizer ({a} : Set G) := fun s hs =>
    mem_centralizer_singleton_iff.mpr (hcent s (hPS ▸ hs))
  have hVC : T.map (MulAut.conj g).toMonoidHom ≤ centralizer ({a} : Set G) := by
    rintro _ ⟨t, ht, rfl⟩
    rw [mem_centralizer_singleton_iff]
    have htc : c * t = t * c := mem_centralizer_iff.mp (mem_inf.mp ht).2 c hcB
    have ha : a = g * c * g⁻¹ := by rw [hg]; group
    change g * t * g⁻¹ * a = a * (g * t * g⁻¹)
    rw [ha, show g * c * g⁻¹ * (g * t * g⁻¹) = g * (c * t) * g⁻¹ by group, htc]
    group
  obtain ⟨k, hkC, hk⟩ := exists_conj_le_sylow P hSC hVC
    ((hS2.to_le inf_le_left).map (MulAut.conj g).toMonoidHom)
  have hka : a * k = k * a := (mem_centralizer_singleton_iff.mp hkC).symm
  set h : G := g⁻¹ * k with hhdef
  have hhc : h⁻¹ * c * h = a := by
    rw [hhdef, hg, show (g⁻¹ * k)⁻¹ * (g⁻¹ * a * g) * (g⁻¹ * k) = k⁻¹ * (a * k) by group, hka]
    group
  have hhT : ∀ t ∈ T, h⁻¹ * t * h ∈ S := fun t ht => by
    have h1 := hk (g * t * g⁻¹) (mem_map_of_mem _ ht)
    rw [← hPS]
    convert h1 using 1
    rw [hhdef]
    group
  set f : G →* G := ((MulAut.conj h⁻¹ : G ≃* G) : G →* G) with hfdef
  have hf : ∀ y, f y = h⁻¹ * y * h := fun y => by
    rw [hfdef, MonoidHom.coe_ofClass, MulAut.conj_apply, inv_inv]
  set E : Subgroup G := B.map f with hEdef
  have hsqS : (closure {t | ∃ s ∈ S ⊓ J ⊓ centralizer (B : Set G), t = s * s}).map f ≤
      S ⊓ withKernel J := by
    rw [MonoidHom.map_closure, closure_le]
    rintro _ ⟨_, ⟨s, hs, rfl⟩, rfl⟩
    have hsT : s ∈ T := mem_inf.mpr ⟨(mem_inf.mp (mem_inf.mp hs).1).1, (mem_inf.mp hs).2⟩
    have hs' := hhT s hsT
    rw [SetLike.mem_coe, hf, show h⁻¹ * (s * s) * h = h⁻¹ * s * h * (h⁻¹ * s * h) by group]
    exact mem_inf.mpr ⟨mul_mem hs' hs', hSq G J hJper hL34 _ (hSJ hs')
      (hS2.to_le (zpowers_le.mpr hs'))⟩
  have hES : E ≤ S ⊓ J := by
    rintro _ ⟨y, hy, rfl⟩
    refine hinv _ (hsqS (mem_map_of_mem f (hBsq hy))) ?_
    rw [hf, show h⁻¹ * y * h * (h⁻¹ * y * h) = h⁻¹ * (y * y) * h by group, hB8.1.2 y hy]
    group
  have hE8 : IsEightGroup E := by
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · rintro _ ⟨u, hu, rfl⟩ _ ⟨v, hv, rfl⟩
      rw [← map_mul, ← map_mul, hB8.1.1 u hu v hv]
    · rintro _ ⟨u, hu, rfl⟩
      rw [← map_mul, hB8.1.2 u hu, map_one]
    · rw [hEdef, card_map_of_injective (MulAut.conj h⁻¹).injective, hB8.2]
  have haE : a ∈ E := ⟨c, hcB, by rw [hf, hhc]⟩
  have hEZ : E ⊓ zStarIn J = zpowers a := by
    apply le_antisymm
    · rintro z ⟨hzE, hzZ⟩
      by_cases hz1 : z = 1
      · rw [hz1]
        exact one_mem _
      · rw [eq_of_mul_self_eq_one_of_isCyclic hZc
          (mem_inf.mpr ⟨(mem_inf.mp (hES hzE)).1, hzZ⟩) haZ (hE8.1.2 z hzE) haa hz1 ha1]
        exact mem_zpowers a
    · rw [zpowers_le]
      exact mem_inf.mpr ⟨haE, (mem_inf.mp haZ).2⟩
  have hZJ : zStarIn J ≤ J := map_subtype_le _
  have hZP : S ⊓ J ⊓ zStarIn J = S ⊓ zStarIn J := by
    rw [inf_assoc, inf_eq_right.mpr hZJ]
  set ψ : ↥B ≃* ↥E := (MulAut.conj h⁻¹ : G ≃* G).subgroupMap B with hψdef
  have hψ : ∀ y : ↥B, (ψ y : G) = h⁻¹ * (y : G) * h := fun y => by
    rw [hψdef, MulEquiv.coe_subgroupMap_apply, MulAut.conj_apply, inv_inv]
  set τ : ↥E ≃* ↥E := (ψ.symm.trans σ).trans ψ with hτdef
  have hτψ : ∀ y : ↥B, (τ (ψ y) : G) = h⁻¹ * (σ y : G) * h := fun y => by
    rw [hτdef, MulEquiv.trans_apply, MulEquiv.trans_apply, MulEquiv.symm_apply_apply, hψ]
  have hτ : ∀ z : ↥E, (z : G)⁻¹ * (τ z : G) ∈ zpowers a := by
    intro z
    obtain ⟨y, rfl⟩ := ψ.surjective z
    rw [hτψ, hψ]
    obtain ⟨m, hm⟩ := mem_zpowers_iff.mp (hσ y)
    refine mem_zpowers_iff.mpr ⟨m, ?_⟩
    have h1 := map_zpow f c m
    rw [hf, hf, hhc] at h1
    rw [← h1, hm]
    group
  obtain ⟨p, -, hpτ⟩ := hT G J (S ⊓ J) E a hJper hL34 hP (by rwa [hZP]) (by rwa [hZP]) hES hE8
    hEZ τ hτ
  refine ⟨h * p * h⁻¹, fun y => ?_⟩
  have h2 := hpτ (ψ y)
  rw [hτψ, hψ] at h2
  calc (h * p * h⁻¹)⁻¹ * (y : G) * (h * p * h⁻¹) = h * (p⁻¹ * (h⁻¹ * y * h) * p) * h⁻¹ := by
        group
    _ = (σ y : G) := by rw [h2]; group

end CFSG.ComponentClassification.GrSLit.GrS4

namespace CFSG.ComponentClassification.GrSLit

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
  CFSG.ComponentClassification.UnbalancedCorr

theorem l34EndGL32Step_of_local (hE : L34CyclicCentralEightFact)
    (hT : L34EightTransvectionFact) (hSq : L34OutSquareFact)
    {G : Type} [Group G] [Finite G] {a : G} {J S : Subgroup G}
    (hJper : ⁅J, J⁆ = J) (hL34 : IsL34Type (J ⧸ Open.fusionZStar J))
    (hS : IsSylowTwoIn S (normalizer (J : Set G)))
    (hSyl : ∃ P : Sylow 2 G, (P : Subgroup G) = S)
    (hcent : ∀ s ∈ S, s * a = a * s)
    (hP : IsSylowTwoIn (S ⊓ J) J)
    (hZc : IsCyclic ↥(S ⊓ zStarIn J))
    (hZ4 : Nat.card ↥(S ⊓ zStarIn J) = 4)
    (haZ : a ∈ S ⊓ zStarIn J) (haa : a * a = 1) (ha1 : a ≠ 1)
    (hinv : ∀ y ∈ S ⊓ J ⊔ S ⊓ coreActionKernel J, y * y = 1 → y ∈ S ⊓ J)
    (hcls : ∀ y ∈ S ⊓ J, y * y = 1 → y ≠ 1 → ∃ g : G, y = g⁻¹ * a * g) :
    ∃ B : Subgroup G, B ≤ S ⊓ J ∧ IsEightGroup B ∧ B ⊓ zStarIn J = zpowers a ∧
      S ≤ normalizer (B : Set G) ∧
      (∀ y ∈ S ⊓ J, (∀ w ∈ S ⊓ J, y⁻¹ * w⁻¹ * y * w ∈ zStarIn J) ↔
        y ∈ B ⊔ (S ⊓ zStarIn J)) ∧
      ∀ σ : ↥B ≃* ↥B, ∃ n ∈ normalizer (B : Set G),
        ∀ b : ↥B, n⁻¹ * (b : G) * n = (σ b : G) := by
  have hZJ : zStarIn J ≤ J := map_subtype_le _
  have hZP : S ⊓ J ⊓ zStarIn J = S ⊓ zStarIn J := by
    rw [inf_assoc, inf_eq_right.mpr hZJ]
  obtain ⟨B, hBP, hB8, hBZ, hBchar, hBiff, hBsq⟩ := hE G J (S ⊓ J) a hJper hL34 hP
    (by rwa [hZP]) (by rwa [hZP]) (by rwa [hZP]) haa ha1
  have hconj : ∀ s ∈ S, ∀ y ∈ B, s * y * s⁻¹ ∈ B := by
    intro s hs y hy
    have hsJ : s ∈ normalizer (J : Set G) := hS.1 hs
    have hyP := hBP hy
    obtain ⟨hyy, hyc⟩ := (hBchar y hyP).mp hy
    have hsyP : s * y * s⁻¹ ∈ S ⊓ J := mem_inf.mpr
      ⟨mul_mem (mul_mem hs (mem_inf.mp hyP).1) (inv_mem hs),
        (mem_normalizer_iff.mp hsJ y).mp (mem_inf.mp hyP).2⟩
    refine (hBchar _ hsyP).mpr ⟨?_, fun w hw => ?_⟩
    · rw [show s * y * s⁻¹ * (s * y * s⁻¹) = s * (y * y) * s⁻¹ by group, hyy]
      group
    · have hw' : s⁻¹ * w * s ∈ S ⊓ J := by
        have h1 := (mem_normalizer_iff.mp (inv_mem hsJ) w).mp (mem_inf.mp hw).2
        rw [inv_inv] at h1
        exact mem_inf.mpr ⟨mul_mem (mul_mem (inv_mem hs) (mem_inf.mp hw).1) hs, h1⟩
      have h1 := GrS4.conj_mem_zStarIn hsJ (hyc _ hw')
      convert h1 using 1
      group
  have hSN : S ≤ normalizer (B : Set G) := fun s hs =>
    GrS4.mem_normalizer_of_map_le_self (by
      rintro _ ⟨y, hy, rfl⟩
      exact hconj s hs y hy)
  have hinv' : ∀ y ∈ S ⊓ withKernel J, y * y = 1 → y ∈ S ⊓ J := by
    have hPQ := GrS4.isSylowTwoIn_withKernel hS
    have hle : S ⊓ J ⊔ S ⊓ coreActionKernel J ≤ S ⊓ withKernel J :=
      sup_le (inf_le_inf_left _ le_sup_left) (inf_le_inf_left _ le_sup_right)
    have heq := hPQ.eq_of_le hle inf_le_right
      ((GrS4.isPGroup_of_isSylowTwoIn hS).to_le inf_le_left)
    intro y hy hyy
    have hy' : y ∈ S ⊓ J ⊔ S ⊓ coreActionKernel J := by
      rw [← heq]
      exact hy
    exact hinv y hy' hyy
  let H : Subgroup (MulAut ↥B) :=
    { carrier := {σ | ∃ n : G, ∀ y : ↥B, n⁻¹ * (y : G) * n = (σ y : G)}
      one_mem' := ⟨1, fun y => by simp⟩
      mul_mem' := by
        rintro σ₁ σ₂ ⟨n₁, h₁⟩ ⟨n₂, h₂⟩
        refine ⟨n₂ * n₁, fun y => ?_⟩
        rw [MulAut.mul_apply, ← h₁, ← h₂]
        group
      inv_mem' := by
        rintro σ ⟨n, hn⟩
        refine ⟨n⁻¹, fun y => ?_⟩
        have h1 := hn (σ⁻¹ y)
        rw [MulAut.apply_inv_self] at h1
        rw [inv_inv, ← h1]
        group }
  have hHtop : H = ⊤ := GrS4.mulAut_eq_top_of_transvection_mem
    (fun u v => Subtype.ext (hB8.1.1 _ u.2 _ v.2)) (fun u => Subtype.ext (hB8.1.2 _ u.2)) H
    (fun σ c hσ => GrS4.exists_conj_eq_of_transvection hT hSq hJper hL34 hS.1 hSyl hcent hP
      hZc hZ4 haZ haa ha1 hinv' hcls hBP hB8 hBsq σ c.2 fun y => by
        obtain ⟨m, hm⟩ := mem_zpowers_iff.mp (hσ y)
        refine mem_zpowers_iff.mpr ⟨m, ?_⟩
        have h1 := congrArg Subtype.val hm
        simpa using h1)
  refine ⟨B, hBP, hB8, hBZ, hSN, fun y hy => by rw [← hZP]; exact hBiff y hy, fun σ => ?_⟩
  have hσH : σ ∈ H := by
    rw [hHtop]
    exact mem_top σ
  obtain ⟨n, hn⟩ : ∃ n : G, ∀ y : ↥B, n⁻¹ * (y : G) * n = (σ y : G) := hσH
  have hn' : n⁻¹ ∈ normalizer (B : Set G) := GrS4.mem_normalizer_of_map_le_self (by
    rintro _ ⟨y, hy, rfl⟩
    show n⁻¹ * y * n⁻¹⁻¹ ∈ B
    rw [inv_inv, hn ⟨y, hy⟩]
    exact (σ ⟨y, hy⟩).2)
  exact ⟨n, by simpa using inv_mem hn', hn⟩


theorem l34EndGL32Step_of_inputs (hE : L34CyclicCentralEightFact)
    (hT : L34EightTransvectionFact) (hSq : L34OutSquareFact) : L34EndGL32Step := by
  intro G _ _ a x J S A hset hcent hZ hrun hZc hZ4 hQc hinv hSyl hcls
  obtain ⟨-, hU3, hL34, -, hS, -, -⟩ := id hset
  have hJa : J ≤ centralizer ({a} : Set G) := hU3.2.2.2.1
  have hJc := hU3.2.2.2.2.1
  have hJper : ⁅J, J⁆ = J := commutator_eq_of_isPComponent hJa hJc
  have hP : IsSylowTwoIn (S ⊓ J) J := GrS4.isSylowTwoIn_inf hS
  have hZJ : zStarIn J ≤ J := map_subtype_le _
  have hZP : S ⊓ J ⊓ zStarIn J = S ⊓ zStarIn J := by
    rw [inf_assoc, inf_eq_right.mpr hZJ]
  have hZne : S ⊓ zStarIn J ≠ ⊥ := by
    intro hbot
    rw [hbot, card_bot] at hZ4
    norm_num at hZ4
  have haZ : a ∈ S ⊓ zStarIn J := hZ hZne
  have ha2 : orderOf a = 2 := hU3.1
  have ha1 : a ≠ 1 := by
    intro h
    rw [h, orderOf_one] at ha2
    exact absurd ha2 (by norm_num)
  have haa : a * a = 1 := by rw [← pow_two, ← ha2, pow_orderOf_eq_one]
  exact l34EndGL32Step_of_local hE hT hSq hJper hL34 hS hSyl hcent hP hZc hZ4 haZ
    haa ha1 hinv hcls

theorem l34EndStructureRestStep_of_facts (hcls : L34CyclicInvolutionClassFact)
    (hE : L34CyclicCentralEightFact) (hT : L34EightTransvectionFact) (hSq : L34OutSquareFact)
    (hE4 : L34EndTStep) (hE6 : L34EndGraphStep) : L34EndStructureRestStep :=
  l34EndStructureRestStep_of_inputs hcls (l34EndGL32Step_of_inputs hE hT hSq) hE4 hE6

end CFSG.ComponentClassification.GrSLit
