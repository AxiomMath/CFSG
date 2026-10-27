module

public import CFSG.HardMathSupport.Curtis.Coordinator.AnisoE7.A5Abstract
public import CFSG.HardMathSupport.Curtis.Coordinator.AnisoE7.A5SigmaStd
public import CFSG.HardMathSupport.Curtis.Coordinator.AnisoE7.FrameLines
public import CFSG.HardMathSupport.Curtis.Coordinator.AnisoE7.A5Lang
public import CFSG.HardMathSupport.Curtis.Coordinator.AnisoE7.A5Std

public noncomputable section

set_option linter.unusedSectionVars false

namespace CFSG.HardMathSupport.Curtis.Coordinator.AnisoE7

open Matrix CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.RankThree.Chevalley CFSG.RankThree.PartOne.KE CFSG.RankThree.PartOne.KA5L
  CFSG.RankThree.Classical2 CFSG.LieType.SeitzGeneration
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open scoped MatrixGroups commutatorElement Pointwise


theorem centralizer_le_hyperClosure_of_a5_line
    {K : Type} [Field K] [Finite K] {ℓ f p : ℕ} [Fact ℓ.Prime] [CharP K ℓ]
    {L : Type} [Field L] [Algebra K L] [IsAlgClosure K L] [CharP L ℓ]
    (F : E7ThreeFrame K L ℓ f p (-1)) (hf : 1 ≤ f) (hK : Nat.card K = ℓ ^ f) (hp : p.Prime)
    (hp3 : 3 < p)
    (hpf : (p : ℤ) ∣ (Nat.card K : ℤ) ^ 2 + (-1 : ℤ) * (Nat.card K : ℤ) + 1)
    {c : adjointGroup .E7 K} {E : Subgroup (adjointGroup .E7 K)} (hE : IsElemAbelian p E)
    (hEc : Nat.card E = p ^ 3)
    (hT : ∀ x ∈ E, psiC F.g0 c x ∈
      twistedTorusOf F.n (Units.map (entrywiseHom (iterateFrobenius L ℓ f))))
    {y : adjointGroup .E7 K} (hy : y ∈ E) (hy1 : y ≠ 1) (v : WeylGroup Tag.E7)
    (hker : ∀ b : Fin Tag.E7.rank → Lˣ, rootDiagUnit .E7 b = psiC F.g0 c y →
      rootCharKernel b = (fun γ => v • γ) '' parabolicRoots Tag.E7 (a5Nodes Tag.E7))
    (hcert : ∃ u ∈ parabolicWeylGroup Tag.E7 (a5Nodes Tag.E7),
      ∀ α ∈ parabolicRoots Tag.E7 (a5Nodes Tag.E7),
        (v⁻¹ * weylQuotientHom Tag.E7 L ⟨F.n, F.hnm⟩ * v) • α = u • ((-1 : ℤ) • α)) :
    Subgroup.centralizer ({y} : Set (adjointGroup .E7 K)) ≤ hyperClosure p (⊤ : Subgroup _) E := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have : IsAlgClosed L := IsAlgClosure.isAlgClosed K
  have hℓ : ℓ.Prime := Fact.out
  set Fr : L →+* L := iterateFrobenius L ℓ f with hFrdef
  set Φ : ModGL Tag.E7 L →* ModGL Tag.E7 L := Units.map (entrywiseHom Fr) with hΦdef
  have hFr : ∀ x, Fr x = x ^ Nat.card K := fun x => by
    rw [hK]; exact iterateFrobenius_def ℓ f x
  have hFrbij : Function.Bijective Fr := ⟨Fr.injective, fun z => by
    obtain ⟨x, hx⟩ := IsAlgClosed.exists_pow_nat_eq z (show 0 < Nat.card K by
      rw [hK]; exact pow_pos hℓ.pos f)
    exact ⟨x, by rw [hFr, hx]⟩⟩
  have hKq : 2 ≤ Nat.card K := Finite.one_lt_card
  have hε : ((-1 : ℤ) = 1 ∨ (-1 : ℤ) = -1) := Or.inr rfl
  have h2 : 2 < ℓ ^ f := by
    rw [← hK]
    exact e7T3_q_gt_two hp3 rfl hKq hpf rfl
  have hstab := e7T3_stabHyp F hK hp hp3 hε hpf
  have hyo : orderOf y = p := orderOf_eq_prime (hE.2 y hy) hy1
  have hhy : F.g0⁻¹ * adjEmb .E7 K L (c * y * c⁻¹) * F.g0 ∈
      twistedTorusOf F.n (Units.map (entrywiseHom (iterateFrobenius L ℓ f))) := by
    simpa [psiC_apply] using hT y hy
  obtain ⟨b, hb, hap, hb1, hbh, -⟩ := e7_three_prelim F hp hyo c hhy
  have hbψ : rootDiagUnit .E7 b = psiC F.g0 c y := by rw [psiC_apply]; exact hbh
  have hSeq := hker b hbψ
  set V : ModGL Tag.E7 L := canonicalRep (coxeterSystem Tag.E7) L v with hV
  have hVm : V ∈ monomialSubgroup Tag.E7 L := canonicalRep_mem_monomialSubgroup L v
  have hVadj : V ∈ adjointGroup Tag.E7 L := canonicalRep_mem_adjointGroup _ L v
  have hΦV : Φ V = V := by
    have h1 := entrywise_canonicalRep (RingEquiv.ofBijective Fr hFrbij) v
    have h2 : (RingEquiv.ofBijective Fr hFrbij).toRingHom = Fr := RingHom.ext fun _ => rfl
    rw [h2] at h1
    exact h1
  have hnC : F.n ∈ adjointGroup Tag.E7 L := monomialSubgroup_le_adjointGroup' F.hnm
  set n' : ModGL Tag.E7 L := V⁻¹ * F.n * V with hn'
  have hn'm : n' ∈ monomialSubgroup Tag.E7 L := mul_mem (mul_mem (inv_mem hVm) F.hnm) hVm
  have hn'adj : n' ∈ adjointGroup Tag.E7 L := mul_mem (mul_mem (inv_mem hVadj) hnC) hVadj
  have hπV : weylQuotientHom Tag.E7 L ⟨V, hVm⟩ = v :=
    weylQuotientHom_eq (mapsRootLines_canonicalRep v)
  have hπn' : weylQuotientHom Tag.E7 L ⟨n', hn'm⟩ =
      v⁻¹ * weylQuotientHom Tag.E7 L ⟨F.n, F.hnm⟩ * v := by
    have : (⟨n', hn'm⟩ : monomialSubgroup Tag.E7 L) =
        ⟨V, hVm⟩⁻¹ * ⟨F.n, F.hnm⟩ * ⟨V, hVm⟩ := Subtype.ext rfl
    rw [this, map_mul, map_mul, map_inv, hπV]
  have hact' : ∃ u ∈ parabolicWeylGroup Tag.E7 (a5Nodes Tag.E7),
      ∀ α ∈ parabolicRoots Tag.E7 (a5Nodes Tag.E7),
        weylQuotientHom Tag.E7 L ⟨n', hn'm⟩ • α = u • ((-1 : ℤ) • α) := by
    obtain ⟨u, hu, hact⟩ := hcert
    exact ⟨u, hu, fun α hα => by rw [hπn']; exact hact α hα⟩
  have halg := isAlgebraic_zmod_of_card (ℓ := ℓ) (L := L) hK
  obtain ⟨u, hu, hu'⟩ := hact'
  obtain ⟨hwS, hwS'⟩ := perm_of_act hu hu'
  have hnw' : MapsRootLines n' (weylQuotientHom Tag.E7 L ⟨n', hn'm⟩) :=
    mapsRootLines_weylQuotientHom ⟨n', hn'm⟩
  let q : TauCeti.PrimePower := ⟨ℓ, f, hℓ, hf⟩
  have hv : (TauCeti.LieTypeIndex.twistedA 5 q).Valid := by
    simp
  obtain ⟨Φ', hΦ', hfin, hqs, ρ, hρs, hρc, hρd⟩ :=
    exists_a5Std_data hf halg n' hn'm ⟨u, hu, hu'⟩ (q := q) rfl rfl hv
  let P' : Subgroup (ModGL Tag.E7 L) := (fixSubgroup Φ').map (a5Frame L)
  set Γ' : Subgroup (ModGL Tag.E7 L) :=
    rootSpan Tag.E7 L (parabolicRoots Tag.E7 (a5Nodes Tag.E7)) ⊓
      twistedFixedPoints n' Φ with hΓ'
  have hPeq : ⁅Γ', Γ'⁆ = P' := commutator_Gamma Fr n' Φ' hΦ' hqs
  have hstd := a5_sigmaFactor_std hf halg h2 n' hn'm hn'adj ⟨u, hu, hu'⟩
  have hstd' : SigmaFactor n' Fr (parabolicRoots Tag.E7 (a5Nodes Tag.E7)) (fun _ : Unit => P')
      (Subgroup.normalizer
        (rootSpan Tag.E7 L (parabolicRoots Tag.E7 (a5Nodes Tag.E7)) : Set (ModGL Tag.E7 L))) := by
    rw [← hPeq]; exact hstd
  have hroots : ∀ r ∈ parabolicRoots Tag.E7 (a5Nodes Tag.E7), IsRoot Tag.E7 r := fun r hr => hr.1
  have htr := SigmaFactor.transport Fr hFrbij v F.n hroots hstd'
  set c₀ : ModGL Tag.E7 L →* ModGL Tag.E7 L := (MulAut.conj V).toMonoidHom with hc₀
  have hcapp : ∀ x, c₀ x = V * x * V⁻¹ := fun x => by simp [hc₀, MulAut.conj_apply]
  have hQ : (rootSpan Tag.E7 L (parabolicRoots Tag.E7 (a5Nodes Tag.E7))).map c₀ =
      rootSpan Tag.E7 L ((fun γ => v • γ) '' parabolicRoots Tag.E7 (a5Nodes Tag.E7)) :=
    map_conj_rootSpan v hroots
  have hR : (twistedFixedPoints n' Φ).map c₀ = twistedFixedPoints F.n Φ := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      rw [hcapp]
      exact (mem_twistedFixedPoints_conj hΦV).1 hx
    · intro hy
      refine ⟨V⁻¹ * y * V, (mem_twistedFixedPoints_conj hΦV).2 ?_, ?_⟩
      · have e : V * (V⁻¹ * y * V) * V⁻¹ = y := by group
        rw [e]
        exact hy
      · rw [hcapp]
        group
  have hΓeq : Γ'.map c₀ = rootSpan Tag.E7 L ((fun γ => v • γ) '' parabolicRoots Tag.E7
      (a5Nodes Tag.E7)) ⊓ twistedFixedPoints F.n Φ := by
    rw [hΓ', Subgroup.map_inf _ _ c₀ (MulAut.conj V).injective, hQ, hR]
  have hPeq' : P'.map c₀ = ⁅Γ'.map c₀, Γ'.map c₀⁆ := by
    rw [← hPeq, Subgroup.map_commutator]
  have hSn : ∀ α ∈ rootCharKernel b, -α ∈ rootCharKernel b := fun α hα =>
    ⟨IsRoot.neg hα.1, by rw [CFSG.RankThree.Chevalley.rootChar_neg', hα.2, inv_one]⟩
  have hPfin : ∀ i : Unit, Finite (P'.map c₀) := fun _ => htr.finite ()
  have hPq : ∀ i : Unit, CFSG.IsQuasisimple (P'.map c₀) := fun _ => htr.quasi ()
  have hPQ : ∀ i : Unit, P'.map c₀ ≤ rootSpan Tag.E7 L (rootCharKernel b) := fun _ => by
    rw [hSeq]; exact htr.le_root ()
  have hPR : ∀ i : Unit, P'.map c₀ ≤ twistedFixedPoints F.n Φ := fun _ => htr.le_fix ()
  have hPadj : ∀ i : Unit, P'.map c₀ ≤ adjointGroup Tag.E7 L := fun _ => htr.le_adj ()
  have hPnorm : ∀ i : Unit, ∀ y ∈ torusGroup Tag.E7 L ⊔ rootSpan Tag.E7 L (rootCharKernel b),
      y ∈ twistedFixedPoints F.n Φ → ∀ u ∈ P'.map c₀, y * u * y⁻¹ ∈ P'.map c₀ := by
    intro _ y hy hyR u hu
    rw [hSeq] at hy
    have hyN : y ∈ Subgroup.normalizer
        (rootSpan Tag.E7 L ((fun γ => v • γ) '' parabolicRoots Tag.E7 (a5Nodes Tag.E7)) :
          Set (ModGL Tag.E7 L)) :=
      sup_le (CFSG.RankThree.PartOne.KE.torusGroup_le_normalizer_rootSpan (fun γ hγ => by
        obtain ⟨α, hα, rfl⟩ := hγ
        exact IsRoot.smul hα.1 v)) (Subgroup.le_normalizer) hy
    rw [hPeq', hΓeq] at hu ⊢
    refine conj_mem_commutator_of_normalizes (fun γ hγ => ?_) hu
    exact Subgroup.mem_inf.2 ⟨(Subgroup.mem_normalizer_iff.1 hyN γ).1 hγ.1,
      mul_mem (mul_mem hyR hγ.2) (inv_mem hyR)⟩
  have hPcent : ∀ y ∈ torusGroup Tag.E7 L ⊔ rootSpan Tag.E7 L (rootCharKernel b),
      y ∈ twistedFixedPoints F.n Φ → (∀ i : Unit, ∀ u ∈ P'.map c₀, y * u = u * y) →
      y ∈ subtorusSigma F.n Φ (rootCharKernel b) := by
    intro y hy hyR hc
    rw [hSeq] at hy ⊢
    obtain ⟨hyH, hyC⟩ := htr.thetaFree y hy (fun i u hu => hc i u hu)
    exact Subgroup.mem_inf.2 ⟨mem_twistedTorusOf.2 ⟨hyH, hyR⟩, hyC⟩
  obtain ⟨hcS, hkerZ⟩ := e7_perx_hc_hkerZ (K := K) Fr F.g0 hbh hhy (S := rootCharKernel b) rfl
  obtain ⟨ψS, hψinj, hψ, hψHQ, hψR, hψadj, hPψ, -⟩ := sigma_embedding_data_of_stab
    (adjEmb .E7 K L) adjEmb_injective adjEmb_mem Φ (adjEmb_frobenius Fr hFr) F.n F.g0 F.hg0C
    F.hg0 F.hperf hp (fun a hap ha1 haT => hstab a hap ha1 haT) (fun α hα => hα.1) hSn
    (fun _ : Unit => P'.map c₀) hPfin hPq hPQ hPR hPadj hPnorm hPcent hyo c hcS hkerZ
  have hInvH : ∀ {t : ModGL Tag.E7 L}, t ∈ torusGroup Tag.E7 L →
      V⁻¹ * t * V ∈ torusGroup Tag.E7 L := by
    intro t ht
    have h := (Subgroup.mem_normalizer_iff.1
      (inv_mem (canonicalRep_mem_normalizer (R := L) v)) t).1 ht
    rwa [inv_inv] at h
  have hVconj : ∀ g ∈ rootSpan Tag.E7 L ((fun γ => v • γ) '' parabolicRoots Tag.E7
      (a5Nodes Tag.E7)), V⁻¹ * g * V ∈ rootSpan Tag.E7 L (parabolicRoots Tag.E7 (a5Nodes Tag.E7)) := by
    intro g hg
    rw [← hQ] at hg
    obtain ⟨q', hq', rfl⟩ := hg
    rw [hcapp]
    have e : V⁻¹ * (V * q' * V⁻¹) * V = q' := by group
    rw [e]
    exact hq'
  have hVconj' : ∀ g ∈ rootSpan Tag.E7 L (parabolicRoots Tag.E7 (a5Nodes Tag.E7)),
      V * g * V⁻¹ ∈ rootSpan Tag.E7 L ((fun γ => v • γ) '' parabolicRoots Tag.E7
        (a5Nodes Tag.E7)) := by
    intro g hg
    rw [← hQ, ← hcapp]
    exact Subgroup.mem_map_of_mem _ hg
  let θ : ModGL Tag.E7 L →* ModGL Tag.E7 L := (MulAut.conj n').toMonoidHom.comp Φ
  have hθapp : ∀ x, θ x = n' * Φ x * n'⁻¹ := fun x => by simp [θ, MulAut.conj_apply]
  let ψ₁ : adjointGroup .E7 K →* ModGL Tag.E7 L :=
    (MulAut.conj V⁻¹).toMonoidHom.comp (psiC F.g0 c)
  have hψ₁ : ∀ x, ψ₁ x = V⁻¹ * psiC F.g0 c x * V := fun x => by
    simp [ψ₁, MulAut.conj_apply]
  have hθfix : ∀ m : ModGL Tag.E7 L, F.n * Φ m * F.n⁻¹ = m → θ (V⁻¹ * m * V) = V⁻¹ * m * V := by
    intro m hm
    have := (mem_twistedFixedPoints_conj (Φ := Φ) (n := F.n) hΦV (x := V⁻¹ * m * V)).2
      (by have e : V * (V⁻¹ * m * V) * V⁻¹ = m := by group
          rw [e]; exact hm)
    rw [hθapp]
    exact this
  have hWσ : (∀ α ∈ parabolicRoots Tag.E7 (a5Nodes Tag.E7),
      weylQuotientHom Tag.E7 L ⟨n', hn'm⟩ • α ∈ parabolicRoots Tag.E7 (a5Nodes Tag.E7)) := hwS
  have hθQeq := map_theta_rootSpan_eq hFrbij hn'm hnw' (fun α hα => hα.1) hwS hwS'
  have hKq' : 2 ≤ Nat.card K := hKq
  have hFr' : ∀ x, Fr x = x ^ Nat.card K := hFr
  have hpq : p ∣ q.card ^ 2 - q.card + 1 := by
    have hqc : q.card = Nat.card K := by
      rw [hK]
      simp [q, TauCeti.PrimePower.card_def]
    rw [hqc]
    have hle : Nat.card K ≤ Nat.card K ^ 2 := Nat.le_self_pow two_ne_zero _
    have : ((Nat.card K ^ 2 - Nat.card K + 1 : ℕ) : ℤ) = (Nat.card K : ℤ) ^ 2 +
        (-1 : ℤ) * (Nat.card K : ℤ) + 1 := by
      push_cast [Nat.cast_sub hle]
      ring
    exact Int.natCast_dvd_natCast.1 (by rw [this]; exact hpf)
  refine centralizer_le_hyperClosure_of_abstract_a5 (G := adjointGroup .E7 K) θ hp hp3 hv hpq
    (H := torusGroup Tag.E7 L) (Q := rootSpan Tag.E7 L (parabolicRoots Tag.E7 (a5Nodes Tag.E7)))
    (P := P')
    (fun a ha b hb => torusGroup_comm ha hb)
    (CFSG.RankThree.PartOne.KE.torusGroup_le_normalizer_rootSpan (fun α hα => hα.1))
    (fun h hh => by rw [hθapp]; exact theta_mem_torusGroup_of_monomial hFrbij hn'm hh)
    (fun g hg => by
      have : θ g ∈ (rootSpan Tag.E7 L (parabolicRoots Tag.E7 (a5Nodes Tag.E7))).map θ :=
        Subgroup.mem_map_of_mem _ hg
      rw [hθQeq] at this
      exact this)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ρ hρs hρc hρd ψ₁ ?_ E hE hEc ?_ hy hy1 ?_ ?_ ?_
  ·
    intro z hz hc g hg
    have hmem : g ∈ (rootSpan Tag.E7 L (parabolicRoots Tag.E7 (a5Nodes Tag.E7))).map θ := by
      rw [hθQeq]; exact hg
    obtain ⟨g', hg', rfl⟩ := hmem
    rw [← map_mul, ← map_mul, hc g' hg']
  ·
    intro s hs
    obtain ⟨t, ht, h⟩ := lang_torus_inf_rootSpan hKq' hFr' hn'm hwS s hs
    exact ⟨t, ht, by rw [hθapp]; exact h⟩
  ·
    intro g hg hθg
    obtain ⟨s, hs, hθs, x, hx, hgx⟩ := exists_split_fixed_Q hFrbij hKq' hFr' hn'm hnw' hwS hwS'
      Φ' hΦ' hg (by rw [← hθapp]; exact hθg)
    exact ⟨s, hs, by rw [hθapp]; exact hθs, x, hx, hgx⟩
  ·
    rintro _ ⟨X, hX, rfl⟩
    rw [← subsystemGroup_eq_rootSpan, ← range_a5Frame]
    exact ⟨X, rfl⟩
  ·
    rintro _ ⟨X, hX, rfl⟩
    rw [hθapp, hΦ' X, (mem_fixSubgroup Φ').1 hX]
  ·
    intro m hm hc
    obtain ⟨hmH, hmC⟩ := hstd'.thetaFree m hm (fun _ u hu => hc u hu)
    exact ⟨hmH, fun g hg => (Subgroup.mem_centralizer_iff.1 hmC g hg).symm⟩
  · exact fun t ht _ => exists_pow_six_eq_mul ht
  · exact fun f hf hc => pow_six_eq_one_of_centralizes hf hc
  · exact fun g hg hθg => pow_six_mem_of_fixed Fr n' Φ' hΦ' hg (by rw [← hθapp]; exact hθg)
  ·
    exact (MulAut.conj V⁻¹).injective.comp (psiC_injective F.g0 c)
  ·
    intro e he
    obtain ⟨hHm, hFix⟩ := mem_twistedTorusOf.1 (hT e he)
    rw [hψ₁]
    exact ⟨hInvH hHm, hθfix _ hFix⟩
  ·
    intro g hg
    have hS : (fun γ => v • γ) '' parabolicRoots Tag.E7 (a5Nodes Tag.E7) ⊆ rootCharKernel b := by
      rw [hSeq]
    have hcent := rootSpan_le_centralizer (K := L) b hS (hVconj' g hg)
    have h1 := Subgroup.mem_centralizer_singleton_iff.1 hcent
    rw [hψ₁, ← hbψ]
    calc V⁻¹ * rootDiagUnit .E7 b * V * g
        = V⁻¹ * (rootDiagUnit .E7 b * (V * g * V⁻¹)) * V := by group
      _ = V⁻¹ * ((V * g * V⁻¹) * rootDiagUnit .E7 b) * V := by rw [h1]
      _ = g * (V⁻¹ * rootDiagUnit .E7 b * V) := by group
  ·
    intro k hk
    have hkC : k ∈ Subgroup.centralizer ({y} : Set (adjointGroup .E7 K)) :=
      Subgroup.mem_centralizer_singleton_iff.2 hk
    have h1 := hψHQ ⟨k, hkC⟩
    have h2 := hψR ⟨k, hkC⟩
    have h3 : ψS ⟨k, hkC⟩ = psiC F.g0 c k := by rw [hψ, psiC_apply]
    rw [h3, hSeq] at h1
    rw [h3] at h2
    refine ⟨?_, ?_⟩
    · rw [hψ₁]
      have hle : torusGroup Tag.E7 L ⊔ rootSpan Tag.E7 L ((fun γ => v • γ) ''
          parabolicRoots Tag.E7 (a5Nodes Tag.E7)) ≤ (torusGroup Tag.E7 L ⊔
          rootSpan Tag.E7 L (parabolicRoots Tag.E7 (a5Nodes Tag.E7))).comap
          (MulAut.conj V⁻¹).toMonoidHom := by
        refine sup_le (fun t ht => ?_) (fun g hg => ?_)
        · rw [Subgroup.mem_comap]
          have : (MulAut.conj V⁻¹).toMonoidHom t = V⁻¹ * t * V := by
            simp [MulAut.conj_apply]
          rw [this]
          exact Subgroup.mem_sup_left (hInvH ht)
        · rw [Subgroup.mem_comap]
          have : (MulAut.conj V⁻¹).toMonoidHom g = V⁻¹ * g * V := by
            simp [MulAut.conj_apply]
          rw [this]
          exact Subgroup.mem_sup_right (hVconj g hg)
      have := hle h1
      rw [Subgroup.mem_comap] at this
      simpa [MulAut.conj_apply] using this
    · rw [hψ₁]
      exact hθfix _ h2
  ·
    intro u hu
    have hmem : V * u * V⁻¹ ∈ P'.map c₀ := Subgroup.mem_map.2 ⟨u, hu, hcapp u⟩
    obtain ⟨d, hd⟩ := hPψ () hmem
    refine ⟨(d : adjointGroup .E7 K), ?_⟩
    have h3 : ψS d = psiC F.g0 c (d : adjointGroup .E7 K) := by rw [hψ, psiC_apply]
    rw [hψ₁, ← h3, hd]
    group

end CFSG.HardMathSupport.Curtis.Coordinator.AnisoE7
