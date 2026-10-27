module

public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.KS.U3CoreMaxMod
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.KS.F4InnerCompSU3
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.Bal209F4

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.ChevQ

namespace KSU3Core

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.HardMathSupport.Solomon.LocalBalance
  CFSG.HardMathSupport.Dickson.I271 CFSG.RankThree.PartTwo.KFacts CFSG.ClassicalGroups.UnitaryFlag
  CFSG.LocalAnalysis.ComponentInitial CFSG.LieType.Steinberg CFSG.LieType.Steinberg.CentralExt
  CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.OuterFourInAux

section Z3


theorem u3_centerThree {X : Type} [Group X] [Finite X] {K B : Subgroup X}
    (hKc : CFSG.Open.IsComponentOf K ⊤) (hSC : IsSCp 3 ⊤ B)
    (hBN : B ≤ Subgroup.normalizer (K : Set X))
    (hLie : IsLieQuot ↥K IsU3EightIndex) (hZ : Subgroup.center ↥K ≠ ⊥)
    (hF : ∃ φ ∈ autImage B K, FieldAutU 3 (↥K ⧸ Subgroup.center ↥K) φ) :
    IsStronglyBalancedIn 3 B K := by
  obtain ⟨φ, hφA, hφF⟩ := hF
  obtain ⟨F, _, h, e, hnot⟩ := exists_unitaryPSU_model_of_fieldAutU hφF
  have hKcomm : commutator ↥K = ⊤ := hKc.2.2.1
  obtain ⟨ψ, hψ⟩ := exists_mulEquiv_unitarySU_three_compat h (by norm_num) hKcomm e hZ
  have hq : 2 < 2 ^ 3 := by norm_num
  set N := Subgroup.normalizer (K : Set X) with hN
  set act : ↥N →* MulAut (unitarySU 2 3 F 3) :=
    (MulAut.congr ψ.symm).toMonoidHom.comp K.normalizerMonoidHom with hact
  have hact_apply : ∀ (n : ↥N) (s : unitarySU 2 3 F 3), ψ (act n s) = K.normalizerMonoidHom n (ψ s) := by
    intro n s
    simp [hact, MulAut.congr_apply]
  intro S hSN hcop hBS
  set A : Subgroup (MulAut (unitarySU 2 3 F 3)) := (B.subgroupOf N).map act with hAdef
  set T : Subgroup (MulAut (unitarySU 2 3 F 3)) := (S.subgroupOf N).map act with hTdef
  have hAel : IsElemAbelian 3 A := IsElemAbelian.map (IsElemAbelian.subgroupOf hSC.2.1 N) _
  have memA : ∀ (b : X) (hb : b ∈ B), act ⟨b, hBN hb⟩ ∈ A := fun b hb =>
    Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.2 hb)
  have memT : ∀ (s : X) (hs : s ∈ S), act ⟨s, hSN hs⟩ ∈ T := fun s hs =>
    Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.2 hs)
  have hφ' : ∃ φ' ∈ A, φ' ∉ (suConj h).range := by
    obtain ⟨b, hbN, hbB, hbφ⟩ := mem_autImage.1 hφA
    refine ⟨act ⟨b, hbN⟩, memA b hbB, ?_⟩
    rintro ⟨Y, hY⟩
    apply hnot
    refine ⟨Y, MulEquiv.ext fun x => ?_⟩
    obtain ⟨s, rfl⟩ := unitaryProj_surjective h 3 x
    have h1 := hψ s
    have h2 : (MulAut.congr e φ) (unitaryProj h 3 s) = e (φ (QuotientGroup.mk (ψ s))) := by
      rw [← h1]
      simp [MulAut.congr_apply]
    rw [h2, ← hbφ, actHom_mk]
    have h3 : K.normalizerMonoidHom ⟨b, hbN⟩ (ψ s) = ψ (act ⟨b, hbN⟩ s) := (hact_apply _ _).symm
    rw [h3, hψ, ← hY]
    rfl
  have hMax : ∀ e' : unitarySU 2 3 F 3, e' ^ 3 = 1 → (∀ α ∈ A, α e' = e') →
      MulAut.conj e' ∈ A := by
    intro e' he3 hfix
    set k : ↥K := ψ e' with hk
    have hk3 : (k : X) ^ 3 = 1 := by
      have : k ^ 3 = 1 := by rw [hk, ← map_pow, he3, map_one]
      rw [← Subgroup.coe_pow, this]
      rfl
    have hcomm : ∀ b ∈ B, b * (k : X) = (k : X) * b := by
      intro b hb
      have h1 := hfix _ (memA b hb)
      have h2 : K.normalizerMonoidHom ⟨b, hBN hb⟩ k = k := by
        have := congrArg ψ h1
        rw [hact_apply] at this
        exact this
      have h3 := congrArg (fun w : ↥K => (w : X)) h2
      simp only [coe_normalizerMonoidHom] at h3
      calc b * (k : X) = ((b : X) * (k : X) * (b : X)⁻¹) * b := by group
        _ = (k : X) * b := by rw [h3]
    have hkB : (k : X) ∈ B := mem_of_isSCp_of_commute hSC hk3 hcomm
    have hconj : MulAut.conj e' = act ⟨(k : X), hBN hkB⟩ := by
      refine MulEquiv.ext fun s => ?_
      apply ψ.injective
      rw [hact_apply, MulAut.conj_apply, map_mul, map_mul, map_inv]
      exact Subtype.ext rfl
    rw [hconj]
    exact memA _ hkB
  have hT3 : ¬ 3 ∣ Nat.card T := by
    intro h3
    have h1 : Nat.card T ∣ Nat.card (S.subgroupOf N) := Subgroup.card_map_dvd _ _
    have h2 : Nat.card (S.subgroupOf N) = Nat.card S :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hSN).toEquiv
    have h4 : 3 ∣ Nat.card S := h2 ▸ h3.trans h1
    exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).1 hcop h4
  have hstable : ∀ a ∈ A, ∀ t ∈ T, a * t * a⁻¹ ∈ T := by
    rintro _ ⟨n, hn, rfl⟩ _ ⟨m, hm, rfl⟩
    have hnB : (n : X) ∈ B := Subgroup.mem_subgroupOf.1 hn
    have hmS : (m : X) ∈ S := Subgroup.mem_subgroupOf.1 hm
    have hconj : (n : X) * (m : X) * (n : X)⁻¹ ∈ S :=
      (Subgroup.mem_normalizer_iff.1 (hBS ⟨hnB, n.2⟩) _).1 hmS
    have hconjN : (n : X) * (m : X) * (n : X)⁻¹ ∈ N := N.mul_mem (N.mul_mem n.2 m.2) (N.inv_mem n.2)
    refine Subgroup.mem_map.2 ⟨⟨(n : X) * (m : X) * (n : X)⁻¹, hconjN⟩,
      Subgroup.mem_subgroupOf.2 hconj, ?_⟩
    rw [show (⟨(n : X) * (m : X) * (n : X)⁻¹, hconjN⟩ : N) = n * m * n⁻¹ from rfl]
    simp only [map_mul, map_inv]
  have hAT : A ≤ Subgroup.normalizer (T : Set (MulAut (unitarySU 2 3 F 3))) := by
    intro a ha
    rw [Subgroup.mem_normalizer_iff]
    intro t
    refine ⟨fun ht => hstable a ha t ht, fun ht => ?_⟩
    have := hstable a⁻¹ (A.inv_mem ha) _ ht
    simpa [mul_assoc] using this
  have hz3 : ∀ z ∈ Subgroup.center (unitarySU 2 3 F 3), z ^ 3 = 1 := by
    intro z hz
    rw [center_unitarySU_three (h := h) hq] at hz
    obtain ⟨c, -, hc3, hzc⟩ := mem_unitaryScalars.mp hz
    apply Subtype.ext
    change ((z : GL (Fin 3) F) ^ 3 : GL (Fin 3) F) = 1
    rw [hzc, ← map_pow, hc3, map_one]
  have hTZ : ∀ t ∈ T, ∀ z ∈ Subgroup.center (unitarySU 2 3 F 3), t z = z := by
    rintro _ ⟨n, hn, rfl⟩ z hz
    obtain ⟨s, hsN⟩ := n
    have hsS : s ∈ S := Subgroup.mem_subgroupOf.1 hn
    set k : ↥K := ψ z with hk
    have hcen : ∀ κ : ↥K, κ ∈ Subgroup.center ↥K → ψ.symm κ ∈ Subgroup.center (unitarySU 2 3 F 3) := by
      intro κ hκ
      rw [Subgroup.mem_center_iff] at hκ ⊢
      intro g
      apply ψ.injective
      rw [map_mul, map_mul, MulEquiv.apply_symm_apply]
      exact hκ (ψ g)
    have hkc : k ∈ Subgroup.center ↥K := by
      rw [Subgroup.mem_center_iff]
      intro g
      obtain ⟨u, rfl⟩ := ψ.surjective g
      rw [hk, ← map_mul, ← map_mul, Subgroup.mem_center_iff.1 hz u]
    have hk3' : ∀ κ : ↥K, κ ∈ Subgroup.center ↥K → (κ : X) ^ 3 = 1 := by
      intro κ hκ
      have h1 : (ψ.symm κ) ^ 3 = 1 := hz3 _ (hcen κ hκ)
      have h2 : κ ^ 3 = 1 := by
        have := congrArg ψ h1
        rwa [map_pow, MulEquiv.apply_symm_apply, map_one] at this
      rw [← Subgroup.coe_pow, h2]
      rfl
    have hcomm : ∀ b ∈ B, b * (k : X) = (k : X) * b := by
      intro b hb
      have he3 : (act ⟨b, hBN hb⟩) ^ 3 = 1 := by
        have : (⟨b, hBN hb⟩ : ↥N) ^ 3 = 1 := Subtype.ext (by simpa using hSC.2.1.2 b hb)
        rw [← map_pow, this, map_one]
      have h1 := CFSG.RankThree.PartTwo.Sec19.Item19Res6Proof.apply_eq_of_mem_center h hq he3 hz
      have h2 : K.normalizerMonoidHom ⟨b, hBN hb⟩ k = k := by
        have := congrArg ψ h1
        rw [hact_apply] at this
        exact this
      have h3 := congrArg (fun w : ↥K => (w : X)) h2
      simp only [coe_normalizerMonoidHom] at h3
      calc b * (k : X) = ((b : X) * (k : X) * (b : X)⁻¹) * b := by group
        _ = (k : X) * b := by rw [h3]
    have hkB : (k : X) ∈ B := mem_of_isSCp_of_commute hSC (hk3' k hkc) hcomm
    have hwS : (k : X) * s * (k : X)⁻¹ * s⁻¹ ∈ S :=
      S.mul_mem ((Subgroup.mem_normalizer_iff.1 (hBS ⟨hkB, hBN hkB⟩) s).1 hsS) (S.inv_mem hsS)
    set κ : ↥K := k * K.normalizerMonoidHom ⟨s, hsN⟩ k⁻¹ with hκ
    have hκc : κ ∈ Subgroup.center ↥K := by
      refine Subgroup.mul_mem _ hkc ?_
      have hk' : k⁻¹ ∈ Subgroup.center ↥K := Subgroup.inv_mem _ hkc
      rw [Subgroup.mem_center_iff] at hk' ⊢
      intro g
      obtain ⟨u, rfl⟩ := (K.normalizerMonoidHom ⟨s, hsN⟩).surjective g
      rw [← map_mul, ← map_mul, hk' u]
    have hκw : (κ : X) = (k : X) * s * (k : X)⁻¹ * s⁻¹ := by
      rw [hκ]
      simp only [Subgroup.coe_mul, coe_normalizerMonoidHom, Subgroup.coe_inv]
      group
    have hw3 : ((k : X) * s * (k : X)⁻¹ * s⁻¹) ^ 3 = 1 := by rw [← hκw]; exact hk3' κ hκc
    have hw1 : (k : X) * s * (k : X)⁻¹ * s⁻¹ = 1 := by
      have h1 : orderOf ((k : X) * s * (k : X)⁻¹ * s⁻¹) ∣ 3 := orderOf_dvd_of_pow_eq_one hw3
      have h2 := Subgroup.orderOf_dvd_natCard S hwS
      have h3 : orderOf ((k : X) * s * (k : X)⁻¹ * s⁻¹) ∣ Nat.gcd 3 (Nat.card S) := Nat.dvd_gcd h1 h2
      rw [hcop, Nat.dvd_one, orderOf_eq_one_iff] at h3
      exact h3
    apply ψ.injective
    rw [hact_apply]
    apply Subtype.ext
    rw [coe_normalizerMonoidHom]
    have : (k : X) * s = s * k := by
      calc (k : X) * s = ((k : X) * s * (k : X)⁻¹ * s⁻¹) * s * k := by group
        _ = s * k := by rw [hw1]; group
    calc (s : X) * (k : X) * (s : X)⁻¹ = (k : X) * s * (s : X)⁻¹ := by rw [this]
      _ = k := by group
  have hTbot : T = ⊥ := eq_bot_of_maxStrict h A hAel hφ' hMax T hT3 hAT hTZ
  intro s hs
  have h1 : act ⟨s, hSN hs⟩ = 1 := by
    have := memT s hs
    rw [hTbot] at this
    exact this
  rw [Subgroup.mem_centralizer_iff]
  intro k hk
  obtain ⟨u, hu⟩ := ψ.surjective ⟨k, hk⟩
  have h2 := congrArg ψ (DFunLike.congr_fun h1 u)
  rw [hact_apply, hu, MulAut.one_apply, hu] at h2
  have h3 := congrArg (fun w : ↥K => (w : X)) h2
  simp only [coe_normalizerMonoidHom] at h3
  calc k * s = ((s : X) * k * (s : X)⁻¹) * s := by rw [h3]
    _ = s * k := by group

end Z3

theorem isU3EightIndexTwo_of {d : TauCeti.LieTypeIndex} (hd : IsU3EightIndex d) :
    KSF4SU3.IsU3EightIndexTwo d := by
  cases d with
  | twistedA r q =>
    obtain ⟨rfl, hq⟩ := hd
    exact ⟨q, hq, rfl⟩
  | _ => exact hd.elim

section Z1Glue


set_option linter.unusedSectionVars false

theorem u3_trivialCenter {X : Type} [Group X] [Finite X] {K B : Subgroup X}
    (hKc : CFSG.Open.IsComponentOf K ⊤) (hSC : IsSCp 3 ⊤ B)
    (hBN : B ≤ Subgroup.normalizer (K : Set X))
    (hLie : IsLieQuot ↥K IsU3EightIndex) (hZ : Subgroup.center ↥K = ⊥)
    (hF : ∃ φ ∈ autImage B K, FieldAutU 3 (↥K ⧸ Subgroup.center ↥K) φ) :
    IsStronglyBalancedIn 3 B K := by
  obtain ⟨φ, hφA, hφF⟩ := hF
  obtain ⟨F, _, h, e, hnot⟩ := exists_unitaryPSU_model_of_fieldAutU hφF
  have hperf : ⁅K, K⁆ = K := Subgroup.isPerfect_iff.1 ⟨hKc.2.2.1⟩
  set A : Subgroup (MulAut (unitaryPSU h 3)) :=
    (autImage B K).map (MulAut.congr e).toMonoidHom with hAdef
  have hAel : IsElemAbelian 3 A := IsElemAbelian.map (isElemAbelian_autImage hSC.2.1) _
  have hmax : ∀ x : unitaryPSU h 3, x ^ 3 = 1 → (∀ α ∈ A, α x = x) → MulAut.conj x ∈ A := by
    intro x hx3 hfix
    obtain ⟨k, hk⟩ := QuotientGroup.mk_surjective (e.symm x)
    have hk3 : k ^ 3 = 1 := by
      have h1 : (QuotientGroup.mk (k ^ 3) : ↥K ⧸ Subgroup.center ↥K) = 1 := by
        rw [QuotientGroup.mk_pow, hk, ← map_pow, hx3, map_one]
      have h2 : k ^ 3 ∈ Subgroup.center ↥K := (QuotientGroup.eq_one_iff _).1 h1
      rw [hZ, Subgroup.mem_bot] at h2
      exact h2
    have hcomm : ∀ b ∈ B, b * (k : X) = (k : X) * b := by
      intro b hb
      have hα : MulAut.congr e (actHom K ⟨b, hBN hb⟩) ∈ A :=
        Subgroup.mem_map_of_mem _ (mem_autImage.2 ⟨b, hBN hb, hb, rfl⟩)
      have h1 := hfix _ hα
      have h2 : actHom K ⟨b, hBN hb⟩ (QuotientGroup.mk k) = QuotientGroup.mk k := by
        rw [hk]
        apply e.injective
        simpa [MulAut.congr_apply] using h1
      rw [actHom_mk] at h2
      have h3 := (QuotientGroup.eq.1 h2)
      rw [hZ, Subgroup.mem_bot] at h3
      have h4 : K.normalizerMonoidHom ⟨b, hBN hb⟩ k = k := by
        have := inv_mul_eq_one.1 h3
        exact this
      have h5 := congrArg (fun w : ↥K => (w : X)) h4
      simp only [coe_normalizerMonoidHom] at h5
      calc b * (k : X) = ((b : X) * (k : X) * (b : X)⁻¹) * b := by group
        _ = (k : X) * b := by rw [h5]
    have hkB : (k : X) ∈ B :=
      mem_of_isSCp_of_commute hSC (by rw [← Subgroup.coe_pow, hk3]; rfl) hcomm
    have hmem : MulAut.congr e (actHom K ⟨(k : X), hBN hkB⟩) ∈ A :=
      Subgroup.mem_map_of_mem _ (mem_autImage.2 ⟨(k : X), hBN hkB, hkB, rfl⟩)
    have hEq : MulAut.congr e (actHom K ⟨(k : X), hBN hkB⟩) = MulAut.conj x := by
      refine MulEquiv.ext fun y => ?_
      obtain ⟨k', hk'⟩ := QuotientGroup.mk_surjective (e.symm y)
      have hy : y = e (QuotientGroup.mk k') := by rw [hk']; simp
      have hx : x = e (QuotientGroup.mk k) := by rw [hk]; simp
      have hnm : K.normalizerMonoidHom ⟨(k : X), hBN hkB⟩ k' = k * k' * k⁻¹ := Subtype.ext rfl
      rw [hy]
      simp only [MulAut.congr_apply, MulEquiv.trans_apply, MulEquiv.symm_apply_apply,
        MulAut.conj_apply]
      rw [actHom_mk, hnm, hx]
      simp [QuotientGroup.mk_mul, map_mul, map_inv]
    rw [← hEq]
    exact hmem
  have hcard : Nat.card A = 27 :=
    exists_rankThree_of_maxMod h A hAel ⟨_, Subgroup.mem_map_of_mem _ hφA, hnot⟩ hmax
  have hcard' : Nat.card (autImage B K) = 27 := by
    rw [← hcard, hAdef, Subgroup.card_map_of_injective (MulAut.congr e).injective]
  have hE : KSF4SU3.AutImageRankThree B K :=
    ⟨autImage B K, le_rfl, isElemAbelian_autImage hSC.2.1, hcard'⟩
  have hJ : Nonempty ((↥K ⧸ Subgroup.center ↥K) ≃* CFSG.PGLModel.projSU 3 2 3) :=
    KSF4SU3.nonempty_equiv_projSU_of_isLieQuot
      (Bal209F4Aux.isLieQuot_mono hLie fun d hd => isU3EightIndexTwo_of hd)
  intro S hSN hcop hBS
  exact KSF4SU3.centralizes_of_autImageRankThree hperf hJ hE hSN hcop hBS

theorem bal209FourUAt_u3 : Bal209FourUAt IsU3EightIndex (FieldAutU 3) := by
  intro X _ _ _ K B hKc hSC hBN _ hLie hF
  by_cases hZ : Subgroup.center ↥K = ⊥
  · exact u3_trivialCenter hKc hSC hBN hLie hZ hF
  · exact u3_centerThree hKc hSC hBN hLie hZ hF

end Z1Glue

end KSU3Core

end CFSG.HardMathSupport.Solomon.Coordinator.ChevQ
