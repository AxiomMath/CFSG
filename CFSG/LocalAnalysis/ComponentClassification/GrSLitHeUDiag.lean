module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitHeUVert
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitHeUComp

public section

namespace CFSG.ComponentClassification.GrSLit

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedGS
open scoped commutatorElement Pointwise

namespace HeUD

variable {X : Type} [Group X] [Finite X]

omit [Finite X] in
theorem mem_zStar_iff {T : Subgroup X} {z : X} :
    z ∈ (Open.fusionZStar ↥T).map T.subtype ↔
      z ∈ T ∧ ∀ t ∈ T, z * t * z⁻¹ * t⁻¹ ∈ (pPrimeCore 2 ↥T).map T.subtype := by
  constructor
  · rintro ⟨z', hz', rfl⟩
    refine ⟨z'.2, fun t ht => ?_⟩
    have h := GSThmB.OddQuot.mem_fusionZStar_iff.mp hz' ⟨t, ht⟩
    exact ⟨_, h, by simp [commutatorElement_def]⟩
  · rintro ⟨hzT, h⟩
    refine ⟨⟨z, hzT⟩, GSThmB.OddQuot.mem_fusionZStar_iff.mpr fun t => ?_, rfl⟩
    obtain ⟨o, ho, hoe⟩ := h t t.2
    have hoe' : (o : X) = z * t * z⁻¹ * t⁻¹ := hoe
    have : o = ⁅(⟨z, hzT⟩ : ↥T), t⁆ := Subtype.ext (by rw [hoe']; simp [commutatorElement_def])
    rw [← this]
    exact ho

omit [Finite X] in
theorem conj_mem_zStar {T : Subgroup X} {g z : X} (hg : g ∈ normalizer (T : Set X))
    (hz : z ∈ (Open.fusionZStar ↥T).map T.subtype) :
    g * z * g⁻¹ ∈ (Open.fusionZStar ↥T).map T.subtype := by
  obtain ⟨hzT, h⟩ := mem_zStar_iff.mp hz
  refine mem_zStar_iff.mpr ⟨(mem_normalizer_iff.mp hg z).mp hzT, fun t ht => ?_⟩
  have ht' : g⁻¹ * t * g ∈ T := by
    have := (mem_normalizer_iff.mp (inv_mem hg) t).mp ht
    rwa [inv_inv] at this
  have h1 := HeUV.conj_mem_of_normalizer hg (h _ ht')
  rwa [show g * (z * (g⁻¹ * t * g) * z⁻¹ * (g⁻¹ * t * g)⁻¹) * g⁻¹ =
    g * z * g⁻¹ * t * (g * z * g⁻¹)⁻¹ * t⁻¹ by group] at h1

theorem commute_of_diagonal {a : X} (ha : a * a = 1) {C M T : Subgroup X} (hMC : M ≤ C)
    (hM : IsComponent (M.subgroupOf C)) (hNC : conjugate M a ≤ C)
    (hN : IsComponent ((conjugate M a).subgroupOf C)) (hne : conjugate M a ≠ M)
    (hT : gsFixedLayer (M ⊔ conjugate M a) a = T) {v : X}
    (hv : v ∈ (Open.fusionZStar ↥T).map T.subtype) : ∀ m ∈ M, v * m = m * v := by
  classical
  set N := conjugate M a with hNdef
  set K := M ⊔ N with hK
  set H := K ⊓ centralizer ({a} : Set X) with hH
  have hainv : a⁻¹ = a := inv_eq_of_mul_eq_one_right ha
  have hmemN : ∀ x, x ∈ N ↔ a * x * a⁻¹ ∈ M := fun x => UnbalancedLayer.mem_conjugate_iff
  have hMN : ∀ m ∈ M, a * m * a⁻¹ ∈ N := fun m hm => by
    rw [hmemN, show a * (a * m * a⁻¹) * a⁻¹ = (a * a) * m * (a * a)⁻¹ by group, ha]
    simpa using hm
  have hcomm : ∀ x ∈ M, ∀ y ∈ N, x * y = y * x := by
    have hne' : M.subgroupOf C ≠ N.subgroupOf C := fun h => hne (by
      have := congrArg (Subgroup.map C.subtype) h
      rwa [map_subgroupOf_eq_of_le hMC, map_subgroupOf_eq_of_le hNC, eq_comm] at this)
    rcases LocalCores.distinct_components_commute hM hN with h | h
    · exact absurd h hne'
    · intro x hx y hy
      have hmem : ⁅(⟨x, hMC hx⟩ : C), ⟨y, hNC hy⟩⁆ ∈ ⁅M.subgroupOf C, N.subgroupOf C⁆ :=
        commutator_mem_commutator hx hy
      rw [h, mem_bot] at hmem
      have h2 : x * y * x⁻¹ * y⁻¹ = 1 := by
        have := congrArg Subtype.val hmem
        simpa [commutatorElement_def] using this
      calc x * y = x * y * x⁻¹ * y⁻¹ * (y * x) := by group
        _ = y * x := by rw [h2, one_mul]
  have hMq : IsQuasisimple ↥M :=
    LocalCores.isQuasisimple_of_mulEquiv (subgroupOfEquivOfLe hMC) hM.1
  have hMperf : commutator ↥M = ⊤ := hMq.1.commutator_eq_top
  have hMnt : Nontrivial ↥M := LocalCores.isQuasisimple_nontrivial hMq
  have hdec : ∀ k ∈ K, ∃ m ∈ M, ∃ n ∈ N, m * n = k := by
    intro k hk
    have hle : M ≤ normalizer (N : Set X) := fun x hx => by
      rw [mem_normalizer_iff]
      intro y
      constructor
      · intro hy
        rw [hcomm x hx y hy, mul_inv_cancel_right]
        exact hy
      · intro hy
        have h1 := hcomm _ (inv_mem hx) _ hy
        have h2 : y = x * y * x⁻¹ := by
          calc y = x⁻¹ * (x * y * x⁻¹) * x := by group
            _ = x * y * x⁻¹ * x⁻¹ * x := by rw [h1]
            _ = x * y * x⁻¹ := by group
        rw [h2]
        exact hy
    have hk' : k ∈ (M : Set X) * (N : Set X) := by
      rw [← Subgroup.coe_mul_of_left_le_normalizer_right M N hle]
      exact hk
    obtain ⟨m, hm, n, hn, hmn⟩ := Set.mem_mul.mp hk'
    exact ⟨m, hm, n, hn, hmn⟩
  let δ : ↥M →* X :=
    { toFun := fun m => (m : X) * (a * m * a⁻¹)
      map_one' := by simp
      map_mul' := fun m₁ m₂ => by
        simp only [coe_mul]
        have h := hcomm m₂ m₂.2 _ (hMN m₁ m₁.2)
        calc (m₁ : X) * m₂ * (a * (m₁ * m₂) * a⁻¹)
            = m₁ * (m₂ * (a * m₁ * a⁻¹)) * (a * m₂ * a⁻¹) := by group
          _ = m₁ * ((a * m₁ * a⁻¹) * m₂) * (a * m₂ * a⁻¹) := by rw [h]
          _ = m₁ * (a * m₁ * a⁻¹) * (m₂ * (a * m₂ * a⁻¹)) := by group }
  have hδ : ∀ m : ↥M, δ m = (m : X) * (a * m * a⁻¹) := fun m => rfl
  have hδK : ∀ m : ↥M, δ m ∈ K := fun m =>
    mul_mem (mem_sup_left m.2) (mem_sup_right (hMN m m.2))
  have hδa : ∀ m : ↥M, δ m ∈ centralizer ({a} : Set X) := by
    intro m
    rw [mem_centralizer_singleton_iff, hδ]
    have h := hcomm m m.2 _ (hMN m m.2)
    calc (m : X) * (a * m * a⁻¹) * a = (a * m * a⁻¹) * m * a := by rw [h]
      _ = a * ((m : X) * (a * m * a⁻¹)) := by rw [hainv]; group
  have hδH : ∀ m : ↥M, δ m ∈ H := fun m => mem_inf.mpr ⟨hδK m, hδa m⟩
  have hTH : T ≤ H := hT ▸ gsFixedLayer_le_inf K a
  have hTn : ∀ c ∈ H, ∀ t ∈ T, c * t * c⁻¹ ∈ T := by
    intro c hc t ht
    rw [← hT] at ht ⊢
    change t ∈ (pLayer ↥H 2).map H.subtype at ht
    change c * t * c⁻¹ ∈ (pLayer ↥H 2).map H.subtype
    obtain ⟨t', ht', rfl⟩ := ht
    have : (pLayer ↥H 2).Characteristic := CatalogueBPrimeJoin.pLayer_characteristic
    have hnorm : (pLayer ↥H 2).Normal := inferInstance
    exact ⟨⟨c, hc⟩ * t' * ⟨c, hc⟩⁻¹, hnorm.conj_mem t' ht' ⟨c, hc⟩, by simp⟩
  have hTN : ∀ c ∈ H, c ∈ normalizer (T : Set X) := fun c hc => by
    rw [mem_normalizer_iff]
    intro t
    refine ⟨hTn c hc t, fun h => ?_⟩
    have := hTn c⁻¹ (inv_mem hc) _ h
    rwa [show c⁻¹ * (c * t * c⁻¹) * c⁻¹⁻¹ = t by group] at this
  set Z := (Open.fusionZStar ↥T).map T.subtype with hZ
  have hZn : ∀ c ∈ H, ∀ z ∈ Z, c * z * c⁻¹ ∈ Z := fun c hc z hz =>
    conj_mem_zStar (hTN c hc) hz
  set R : Subgroup ↥M := Z.comap δ with hR
  have hRn : R.Normal := ⟨fun r hr g => by
    show δ (g * r * g⁻¹) ∈ Z
    rw [map_mul, map_mul, map_inv]
    exact hZn _ (hδH g) _ hr⟩
  rcases LocalCores.quasisimple_normal_subgroups hMq hRn with hRt | hRc
  ·
    exfalso
    have hall : ∀ m : ↥M, δ m ∈ Z := fun m => by
      have : m ∈ R := hRt ▸ mem_top m
      exact this
    have hDp : ⁅δ.range, δ.range⁆ = δ.range := by
      rw [MonoidHom.range_eq_map, ← map_commutator, ← _root_.commutator_def, hMperf]
    have hD : δ.range ≤ (pPrimeCore 2 ↥T).map T.subtype := by
      rw [← hDp, commutator_le]
      rintro _ ⟨m, rfl⟩ _ ⟨m', rfl⟩
      have h2 := (mem_zStar_iff.mp (hall m)).2 _ (mem_zStar_iff.mp (hall m')).1
      rwa [commutatorElement_def]
    have hodd : Odd (Nat.card δ.range) := by
      have h1 : Nat.card δ.range ∣ Nat.card ((pPrimeCore 2 ↥T).map T.subtype) :=
        card_dvd_of_le hD
      have h2 : Odd (Nat.card ((pPrimeCore 2 ↥T).map T.subtype)) := by
        rw [card_map_of_injective T.subtype_injective]
        exact Nat.coprime_two_left.mp pPrimeCore_coprime_card
      exact h2.of_dvd_nat h1
    have hsol : Group.IsSolvable δ.range := CFSG.FeitThompson.isSolvable_of_odd_natCard _ hodd
    have hbot : δ.range = ⊥ := by
      by_contra hne'
      have : Nontrivial δ.range := (nontrivial_iff_ne_bot _).mpr hne'
      have : Group.IsPerfect δ.range := isPerfect_iff.mpr hDp
      exact Group.IsPerfect.not_isSolvable δ.range hsol
    have hMN' : ∀ m ∈ M, m ∈ N := by
      intro m hm
      have h1 : δ ⟨m, hm⟩ = 1 := by
        have : δ ⟨m, hm⟩ ∈ δ.range := ⟨_, rfl⟩
        rwa [hbot, mem_bot] at this
      rw [hδ] at h1
      have h2 : a * m * a⁻¹ = m⁻¹ := eq_inv_of_mul_eq_one_right h1
      have h3 := hMN m hm
      rw [h2] at h3
      simpa using inv_mem h3
    have hab : commutator ↥M = ⊥ := by
      rw [_root_.commutator_def, commutator_eq_bot_iff_le_centralizer]
      intro x _
      rw [mem_centralizer_iff]
      intro y _
      exact Subtype.ext (hcomm y y.2 x (hMN' x x.2))
    rw [hab] at hMperf
    obtain ⟨x, y, hxy⟩ := hMnt
    have hx : x ∈ (⊥ : Subgroup ↥M) := hMperf ▸ mem_top x
    have hy : y ∈ (⊥ : Subgroup ↥M) := hMperf ▸ mem_top y
    rw [mem_bot] at hx hy
    exact hxy (hx.trans hy.symm)
  ·
    have hvH : v ∈ H := hTH (mem_zStar_iff.mp hv).1
    obtain ⟨m₁, hm₁, n₁, hn₁, rfl⟩ := hdec v (mem_inf.mp hvH).1
    have hva : m₁ * n₁ * a = a * (m₁ * n₁) :=
      mem_centralizer_singleton_iff.mp (mem_inf.mp hvH).2
    have hw : a * n₁ * a⁻¹ ∈ M := (hmemN n₁).mp hn₁
    have hq : a * m₁ * a⁻¹ = m₁ * n₁ * (a * n₁ * a⁻¹)⁻¹ := by
      have h : a * (m₁ * n₁) * a⁻¹ = m₁ * n₁ := by rw [← hva]; group
      calc a * m₁ * a⁻¹ = a * (m₁ * n₁) * a⁻¹ * (a * n₁ * a⁻¹)⁻¹ := by group
        _ = m₁ * n₁ * (a * n₁ * a⁻¹)⁻¹ := by rw [h]
    have hiden : ∀ m ∈ M, m₁ * n₁ * (m * (a * m * a⁻¹)) * (m₁ * n₁)⁻¹ =
        m₁ * m * m₁⁻¹ * (a * (m₁ * m * m₁⁻¹) * a⁻¹) := by
      intro m hm
      have hp := hMN m hm
      have h1 : n₁ * m = m * n₁ := (hcomm m hm n₁ hn₁).symm
      have h2 : (a * n₁ * a⁻¹) * (a * m * a⁻¹) = (a * m * a⁻¹) * (a * n₁ * a⁻¹) :=
        hcomm _ hw _ hp
      calc m₁ * n₁ * (m * (a * m * a⁻¹)) * (m₁ * n₁)⁻¹
          = m₁ * (n₁ * m) * (a * m * a⁻¹) * n₁⁻¹ * m₁⁻¹ := by group
        _ = m₁ * (m * n₁) * (a * m * a⁻¹) * n₁⁻¹ * m₁⁻¹ := by rw [h1]
        _ = m₁ * m * n₁ * ((a * n₁ * a⁻¹)⁻¹ * ((a * n₁ * a⁻¹) * (a * m * a⁻¹))) * n₁⁻¹ *
              m₁⁻¹ := by group
        _ = m₁ * m * n₁ * ((a * n₁ * a⁻¹)⁻¹ * ((a * m * a⁻¹) * (a * n₁ * a⁻¹))) * n₁⁻¹ *
              m₁⁻¹ := by rw [h2]
        _ = m₁ * m * m₁⁻¹ * ((m₁ * n₁ * (a * n₁ * a⁻¹)⁻¹) * (a * m * a⁻¹) *
              (m₁ * n₁ * (a * n₁ * a⁻¹)⁻¹)⁻¹) := by group
        _ = m₁ * m * m₁⁻¹ * ((a * m₁ * a⁻¹) * (a * m * a⁻¹) * (a * m₁ * a⁻¹)⁻¹) := by
              rw [← hq]
        _ = m₁ * m * m₁⁻¹ * (a * (m₁ * m * m₁⁻¹) * a⁻¹) := by group
    have hcen : ∀ m ∈ M, ∀ n ∈ M, m₁ * m * m₁⁻¹ * m⁻¹ * n = n * (m₁ * m * m₁⁻¹ * m⁻¹) := by
      intro m hm n hn
      have hc : m₁ * m * m₁⁻¹ * m⁻¹ ∈ M :=
        mul_mem (mul_mem (mul_mem hm₁ hm) (inv_mem hm₁)) (inv_mem hm)
      have hmem : (⟨_, hc⟩ : ↥M) ∈ R := by
        show δ ⟨_, hc⟩ ∈ Z
        have h1 : δ ⟨_, hc⟩ = (m₁ * n₁) * δ ⟨m, hm⟩ * (m₁ * n₁)⁻¹ * (δ ⟨m, hm⟩)⁻¹ := by
          have h2 : δ ⟨_, hc⟩ = δ ⟨m₁ * m * m₁⁻¹, mul_mem (mul_mem hm₁ hm) (inv_mem hm₁)⟩ *
              (δ ⟨m, hm⟩)⁻¹ := by
            rw [← map_inv, ← map_mul]
            rfl
          rw [h2, hδ, hδ, hiden m hm]
        rw [h1]
        have h3 : δ ⟨m, hm⟩ * (m₁ * n₁)⁻¹ * (δ ⟨m, hm⟩)⁻¹ ∈ Z :=
          hZn _ (hδH _) _ (inv_mem hv)
        have h4 := mul_mem hv h3
        rwa [show m₁ * n₁ * (δ ⟨m, hm⟩ * (m₁ * n₁)⁻¹ * (δ ⟨m, hm⟩)⁻¹) =
          m₁ * n₁ * δ ⟨m, hm⟩ * (m₁ * n₁)⁻¹ * (δ ⟨m, hm⟩)⁻¹ by group] at h4
      have h5 := mem_center_iff.mp (hRc hmem) ⟨n, hn⟩
      exact (congrArg Subtype.val h5).symm
    have hm₁c := HeUC.commute_of_commutator_central hMperf (le_normalizer hm₁) hcen
    intro m hm
    calc m₁ * n₁ * m = m₁ * (n₁ * m) := by group
      _ = m₁ * (m * n₁) := by rw [(hcomm m hm n₁ hn₁).symm]
      _ = (m₁ * m) * n₁ := by group
      _ = (m * m₁) * n₁ := by rw [hm₁c m hm]
      _ = m * (m₁ * n₁) := by group

theorem commute_of_diagonal' {a : X} (ha : a * a = 1) {C M T : Subgroup X} (hMC : M ≤ C)
    (hM : IsComponent (M.subgroupOf C)) (hNC : conjugate M a ≤ C)
    (hN : IsComponent ((conjugate M a).subgroupOf C)) (hne : conjugate M a ≠ M)
    (hT : gsFixedLayer (M ⊔ conjugate M a) a = T) {v : X}
    (hv : v ∈ (Open.fusionZStar ↥T).map T.subtype) :
    ∀ m ∈ conjugate M a, v * m = m * v := by
  have hMM : conjugate (conjugate M a) a = M :=
    UnbalancedLayer.conjugate_conjugate_self_of_mul_self ha
  refine commute_of_diagonal ha hNC hN (by rw [hMM]; exact hMC) (by rw [hMM]; exact hM)
    (by rw [hMM]; exact hne.symm) ?_ hv
  rw [hMM, sup_comm]
  exact hT

end HeUD

end CFSG.ComponentClassification.GrSLit
