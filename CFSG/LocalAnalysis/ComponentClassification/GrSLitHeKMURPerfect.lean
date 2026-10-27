module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitHeDG
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitHeKPCore
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitHeGS36

public section

namespace CFSG.ComponentClassification.GrSLit

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedGS

namespace HeKMUR

variable {X : Type} [Group X] [Finite X]

section Facts


theorem mem_gsFixedLayer_self {N : Subgroup X}
    (hN : Nonempty (↥N ≃* Blueprint.NativeSporadic.He)) {n : X} (hn : HeldTwoA N n) :
    n ∈ gsFixedLayer N n := by
  obtain ⟨-, -, hAK⟩ := heldTwoAKFact X N hN n hn
  have hKn : gsFixedLayer N n ≤ centralizer ({n} : Set X) :=
    (gsFixedLayer_le_inf N n).trans inf_le_right
  have hn1 : n ≠ 1 := fun h => by
    have h2 := hn.2.1
    rw [h, orderOf_one] at h2
    norm_num at h2
  rcases hAK n hn.1 fun k hk => (mem_centralizer_singleton_iff.mp (hKn hk)).symm with
    h | ⟨-, h⟩
  · exact absurd h hn1
  · exact map_subtype_le _ h


theorem le_centralizer_of_perfect
    {N : Subgroup X} (hsetN : HeldEndSetting X N) {w n : X} (hw2 : orderOf w = 2)
    (hNw : N ≤ centralizer ({w} : Set X)) (hn : HeldTwoA N n) {P : Subgroup X}
    (hPw : P ≤ centralizer ({w} : Set X)) (hPp : ⁅P, P⁆ = P)
    (hPK : ∀ p ∈ P, ∀ k ∈ gsFixedLayer N n, p * k = k * p) :
    P ≤ centralizer (N : Set X) := by
  obtain ⟨-, -, hstd, ⟨eN⟩, -⟩ := id hsetN
  have hZ := HeZ.center_eq_bot_of_held eN
  have hwC : w ∈ centralizer (N : Set X) :=
    mem_centralizer_iff.mpr fun x hx => mem_centralizer_singleton_iff.mp (hNw hx)
  have hPN : P ≤ normalizer (N : Set X) :=
    hPw.trans (HeZ.centralizer_le_normalizer hstd hwC hw2)
  have hQ := SeitzReduction.perfect_le_sup_centralizer (heldOuterSolvableFact X N ⟨eN⟩) hPp hPN
  have hKN : gsFixedLayer N n ≤ N := (gsFixedLayer_le_inf N n).trans inf_le_left
  obtain ⟨-, -, hAK⟩ := heldTwoAKFact X N ⟨eN⟩ n hn
  have hprojZ : HeZ.projL hZ hQ ≤
      (center ↥(gsFixedLayer N n)).map (gsFixedLayer N n).subtype := by
    intro y hy
    have hyK : ∀ k ∈ gsFixedLayer N n, y * k = k * y := fun k hk =>
      mem_centralizer_singleton_iff.mp (HeZ.projL_le_centralizer hZ hQ (hKN hk)
        (fun p hp => mem_centralizer_singleton_iff.mpr (hPK p hp k hk)) hy)
    rcases hAK y (HeZ.projL_le hZ hQ hy) hyK with rfl | ⟨-, h⟩
    · exact one_mem _
    · exact h
  have hbot : HeZ.projL hZ hQ = ⊥ := by
    rw [← HeZ.projL_perfect hZ hQ hPp, commutator_eq_bot_iff_le_centralizer]
    intro y hy
    rw [mem_centralizer_iff]
    intro y' hy'
    obtain ⟨z, hz, rfl⟩ := mem_map.mp (hprojZ hy)
    obtain ⟨z', -, rfl⟩ := mem_map.mp (hprojZ hy')
    exact congrArg Subtype.val (mem_center_iff.mp hz z')
  intro q hq
  have h1 : ((HeZ.fstHom hZ hQ ⟨q, hq⟩ : ↥N) : X) ∈ HeZ.projL hZ hQ :=
    mem_map_of_mem _ (MonoidHom.mem_range.mpr ⟨_, rfl⟩)
  rw [hbot, mem_bot] at h1
  exact (HeZ.mem_ker_fstHom_iff hZ hQ ⟨q, hq⟩).mp (MonoidHom.mem_ker.mpr (Subtype.ext h1))

theorem false_of_perfect_pair
    {N : Subgroup X} (hsetN : HeldEndSetting X N) {w n : X} (hw2 : orderOf w = 2)
    (hNw : N ≤ centralizer ({w} : Set X)) (hn : HeldTwoA N n) {P : Subgroup X}
    (hPw : P ≤ centralizer ({w} : Set X)) (hPp : ⁅P, P⁆ = P)
    (hPK : ∀ p ∈ P, ∀ k ∈ gsFixedLayer N n, p * k = k * p) {y₁ y₂ : X} (h₁ : y₁ ∈ P)
    (h₂ : y₂ ∈ P) (hy₁ : y₁ * y₁ = 1) (hy₂ : y₂ * y₂ = 1) (h1 : y₁ ≠ 1) (h2 : y₂ ≠ 1)
    (hne : y₁ ≠ y₂) (hc : y₁ * y₂ = y₂ * y₁) : False := by
  have hPC := le_centralizer_of_perfect hsetN hw2 hNw hn hPw hPp hPK
  exact HeZ.false_of_pair hsetN.2.2.2.2 (hPC h₁) (hPC h₂) hy₁ hy₂ h1 h2 hne hc

theorem false_of_conj_eq_mul
    {L N M : Subgroup X} {a u w n₀ c d : X} (hset : HeldEndSetting X L) (ha : orderOf a = 2)
    (hLa : L ≤ centralizer ({a} : Set X)) (hu : HeldTwoA L u)
    (hMu : M ≤ centralizer ({u} : Set X))
    (hMp : IsPComponent 2 (M.subgroupOf (centralizer ({u} : Set X))))
    (hne : conjugate M a ≠ M) (hfix : gsFixedLayer (M ⊔ conjugate M a) a = gsFixedLayer L u)
    (hc : ∀ x ∈ (pPrimeCore 2 ↥M).map M.subtype, ∀ m ∈ M, x * m = m * x)
    (hsetN : HeldEndSetting X N) (hw2 : orderOf w = 2) (hNw : N ≤ centralizer ({w} : Set X))
    (hTA : HeldTwoA N n₀) (hKM : gsFixedLayer N n₀ = M) (hdM : ∀ m ∈ M, d * m = m * d)
    (hcd : c = d⁻¹ * u * d) (hcn : c = n₀ * w) : False := by
  obtain ⟨-, -, -, ⟨eL⟩, -⟩ := id hset
  obtain ⟨-, -, -, ⟨eN⟩, -⟩ := id hsetN
  have haa : a * a = 1 := by rw [← pow_two, ← ha, pow_orderOf_eq_one]
  have haCu : a ∈ centralizer ({u} : Set X) := mem_centralizer_singleton_iff.mpr
    (mem_centralizer_singleton_iff.mp (hLa hu.1)).symm
  have hMc : IsComponent (M.subgroupOf (centralizer ({u} : Set X))) :=
    HeUC.isComponent_of_central hMu hMp hc
  have hMac : IsComponent ((conjugate M a).subgroupOf (centralizer ({u} : Set X))) :=
    HeKP.isComponent_conjugate hMc haCu
  have hMau : conjugate M a ≤ centralizer ({u} : Set X) := by
    intro x hx
    rw [HeKP.mem_conjugate] at hx
    have h := mul_mem (mul_mem (inv_mem haCu) (hMu hx)) haCu
    rwa [show a⁻¹ * (a * x * a⁻¹) * a = x by group] at h
  have hMN := HeKP.commute_of_components hMu hMau hMc hMac (Ne.symm hne)
  have hMq : IsQuasisimple ↥M :=
    LocalCores.isQuasisimple_of_mulEquiv (subgroupOfEquivOfLe hMu) hMc.1
  have haM : ∀ y ∈ M, a * y * a⁻¹ ∈ conjugate M a := fun y hy => by
    rw [HeKP.mem_conjugate,
      show a * (a * y * a⁻¹) * a⁻¹ = (a * a) * y * (a * a)⁻¹ by group, haa]
    simpa using hy
  have haN : ∀ x ∈ conjugate M a, a * x * a⁻¹ ∈ M := fun x hx => HeKP.mem_conjugate.mp hx
  have hKδ : gsFixedLayer L u = (HeDQ.delta hMN haM).range :=
    hfix.symm.trans (HeDG.gsFixedLayer_eq_range haa hMN haM haN hMq (by rw [hfix]; exact hu.2.2))
  have huK := mem_gsFixedLayer_self ⟨eL⟩ hu
  rw [hKδ] at huK
  obtain ⟨x, hx⟩ := huK
  rw [HeDQ.delta_apply] at hx
  have hxM : ∀ m ∈ M, (x : X) * m = m * x := by
    intro m hm
    have h1 : Commute u m := (mem_centralizer_singleton_iff.mp (hMu hm)).symm
    have h2 : Commute (a * x * a⁻¹) m := (hMN m hm _ (haM x x.2)).symm
    have h3 : (x : X) = u * (a * x * a⁻¹)⁻¹ := by rw [← hx]; group
    rw [h3]
    exact (h1.mul_left h2.inv_left).eq
  have hn₀n₀ : n₀ * n₀ = 1 := by rw [← pow_two, ← hTA.2.1, pow_orderOf_eq_one]
  have hn₀M : n₀ ∈ M := hKM ▸ mem_gsFixedLayer_self ⟨eN⟩ hTA
  have hw : w = d⁻¹ * (n₀ * u) * d := by
    have h1 : w = n₀ * c := by rw [hcn, ← mul_assoc, hn₀n₀, one_mul]
    have h2 : d * n₀ = n₀ * d := hdM n₀ hn₀M
    rw [h1, hcd]
    calc n₀ * (d⁻¹ * u * d) = d⁻¹ * (d * n₀) * d⁻¹ * u * d := by group
      _ = d⁻¹ * (n₀ * d) * d⁻¹ * u * d := by rw [h2]
      _ = d⁻¹ * (n₀ * u) * d := by group
  set g := d⁻¹ * a with hg
  set P := M.map (MulAut.conj g).toMonoidHom with hP
  have hPmem : ∀ p ∈ P, ∃ m ∈ M, p = d⁻¹ * (a * m * a⁻¹) * d := by
    rintro _ ⟨m, hm, rfl⟩
    refine ⟨m, hm, ?_⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, hg]
    group
  have hMperf : ⁅M, M⁆ = M := by
    have h := (heldTwoALayerFact X N ⟨eN⟩ n₀ hTA).1
    rwa [hKM] at h
  have hPp : ⁅P, P⁆ = P := by rw [hP, ← map_commutator, hMperf]
  have hyu : ∀ m ∈ M, Commute (n₀ * u) (a * m * a⁻¹) := by
    intro m hm
    have hy := haM m hm
    have e1 : Commute n₀ (a * m * a⁻¹) := hMN n₀ hn₀M _ hy
    have e2 : Commute (x : X) (a * m * a⁻¹) := hMN x x.2 _ hy
    have e3 : Commute (a * x * a⁻¹) (a * m * a⁻¹) := by
      show a * x * a⁻¹ * (a * m * a⁻¹) = a * m * a⁻¹ * (a * x * a⁻¹)
      calc a * ↑x * a⁻¹ * (a * m * a⁻¹) = a * (↑x * m) * a⁻¹ := by group
        _ = a * (m * ↑x) * a⁻¹ := by rw [hxM m hm]
        _ = a * m * a⁻¹ * (a * ↑x * a⁻¹) := by group
    rw [← hx]
    exact e1.mul_left (e2.mul_left e3)
  have hPw : P ≤ centralizer ({w} : Set X) := by
    intro p hp
    obtain ⟨m, hm, rfl⟩ := hPmem p hp
    rw [mem_centralizer_singleton_iff, hw]
    have h := (hyu m hm).eq
    calc d⁻¹ * (a * m * a⁻¹) * d * (d⁻¹ * (n₀ * u) * d)
        = d⁻¹ * ((a * m * a⁻¹) * (n₀ * u)) * d := by group
      _ = d⁻¹ * ((n₀ * u) * (a * m * a⁻¹)) * d := by rw [h]
      _ = d⁻¹ * (n₀ * u) * d * (d⁻¹ * (a * m * a⁻¹) * d) := by group
  have hPK : ∀ p ∈ P, ∀ k ∈ gsFixedLayer N n₀, p * k = k * p := by
    intro p hp k hk
    rw [hKM] at hk
    obtain ⟨m, hm, rfl⟩ := hPmem p hp
    have h1 : Commute (a * m * a⁻¹) k := (hMN k hk _ (haM m hm)).symm
    have h2 : Commute d k := hdM k hk
    exact ((h2.inv_left.mul_left h1).mul_left h2).eq
  obtain ⟨y₁, hy₁, y₂, hy₂, hyy₁, hyy₂, hy₁1, hy₂1, hy12, hyc⟩ :=
    heldTwoAFourFact_of_model HeGS.heldTwoAFourModel X N ⟨eN⟩ n₀ hTA
  rw [hKM] at hy₁ hy₂
  have hconj : ∀ y : X, g * y * g⁻¹ * (g * y * g⁻¹) = g * (y * y) * g⁻¹ := fun y => by group
  have hmemP : ∀ y ∈ M, g * y * g⁻¹ ∈ P := fun y hy => ⟨y, hy, rfl⟩
  refine false_of_perfect_pair hsetN hw2 hNw hTA hPw hPp hPK (hmemP y₁ hy₁) (hmemP y₂ hy₂)
    ?_ ?_ ?_ ?_ ?_ ?_
  · rw [hconj, hyy₁]
    group
  · rw [hconj, hyy₂]
    group
  · intro h
    apply hy₁1
    calc y₁ = g⁻¹ * (g * y₁ * g⁻¹) * g := by group
      _ = 1 := by rw [h]; group
  · intro h
    apply hy₂1
    calc y₂ = g⁻¹ * (g * y₂ * g⁻¹) * g := by group
      _ = 1 := by rw [h]; group
  · intro h
    apply hy12
    calc y₁ = g⁻¹ * (g * y₁ * g⁻¹) * g := by group
      _ = y₂ := by rw [h]; group
  · calc g * y₁ * g⁻¹ * (g * y₂ * g⁻¹) = g * (y₁ * y₂) * g⁻¹ := by group
      _ = g * (y₂ * y₁) * g⁻¹ := by rw [hyc]
      _ = g * y₂ * g⁻¹ * (g * y₁ * g⁻¹) := by group

end Facts

end HeKMUR

end CFSG.ComponentClassification.GrSLit
