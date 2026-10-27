module

public import CFSG.Quasithin.EmptyFaithful.Stellmacher.PushingUpAndModuleTheory.BaumannS3
public import CFSG.HardMathSupport.Cooperstein.StructureLie.ShortCommAlg

public section

namespace CFSG.HardMathSupport.Cooperstein.StructureLie

namespace ShortComm

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.F53Push
open CFSG.RankThreeCoreUniqueness.Helpers CFSG.QuasithinUnique.Setup.Campbell
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem conj_mem_centralizer {V : Subgroup G} {g c : G}
    (hg : g ∈ Subgroup.normalizer (V : Set G)) (hc : c ∈ Subgroup.centralizer (V : Set G)) :
    g * c * g⁻¹ ∈ Subgroup.centralizer (V : Set G) := by
  rw [Subgroup.mem_centralizer_iff] at hc ⊢
  intro v hv
  have h1 : g⁻¹ * v * g ∈ V := by
    have h := (Subgroup.mem_normalizer_iff.mp hg (g⁻¹ * v * g)).mpr
    have e : g * (g⁻¹ * v * g) * g⁻¹ = v := by group
    rw [e] at h
    exact h hv
  have h2 := hc _ h1
  calc v * (g * c * g⁻¹) = g * ((g⁻¹ * v * g) * c) * g⁻¹ := by group
    _ = g * (c * (g⁻¹ * v * g)) * g⁻¹ := by rw [h2]
    _ = g * c * g⁻¹ * v := by group

omit [Finite G] in
theorem commutator_mem_of_mem_normalizer {N : Subgroup G} {x y : G}
    (hx : x ∈ Subgroup.normalizer (N : Set G)) (hy : y ∈ N) : y * x * y⁻¹ * x⁻¹ ∈ N := by
  have h : x * y⁻¹ * x⁻¹ ∈ N := (Subgroup.mem_normalizer_iff.mp hx y⁻¹).mp (N.inv_mem hy)
  have e : y * x * y⁻¹ * x⁻¹ = y * (x * y⁻¹ * x⁻¹) := by group
  rw [e]
  exact N.mul_mem hy h

theorem exists_baumann_commutator
    {Q V S M : Subgroup G} {s x : G}
    (hQ2 : IsPGroup 2 Q) (hS2 : IsPGroup 2 S)
    (hMQ : M ≤ Subgroup.normalizer (Q : Set G)) (hMV : M ≤ Subgroup.normalizer (V : Set G))
    (hQS : Q ≤ S) (hSM : S ≤ M) (hVQ : V ≤ Q) (hVel : IsElemAbelian 2 V)
    (hQC : Q ≤ Subgroup.centralizer (V : Set G))
    (hsS : s ∈ S) (hsQ : s * s ∈ Q) (hSgen : S ≤ Subgroup.zpowers s ⊔ Q)
    (hsC : s ∉ Subgroup.centralizer (V : Set G))
    (hxM : x ∈ M) (hx3 : x ^ 3 ∈ Q) (hsx : s * x * s⁻¹ * x ∈ Q)
    (hxC : x ∉ Subgroup.centralizer (V : Set G))
    (hcgs : ∀ C : Subgroup G, C ≤ S → C ≠ ⊥ → (C.subgroupOf S).Characteristic →
      ∀ y ∈ M, y ∈ Subgroup.normalizer (C : Set G) → y ∈ Subgroup.normalizer (S : Set G)) :
    ∃ k : ℕ, ∀ q ∈ Q, ⁅q, x ^ 2 ^ k⁆ ∈ V := by
  classical
  set X₀ : Subgroup G := Q ⊔ Subgroup.zpowers s ⊔ Subgroup.zpowers x with hX₀def
  have hsM : s ∈ M := hSM hsS
  have hQM : Q ≤ M := hQS.trans hSM
  have hQX₀ : Q ≤ X₀ := le_sup_left.trans le_sup_left
  have hsX₀ : s ∈ X₀ :=
    Subgroup.mem_sup_left (Subgroup.mem_sup_right (Subgroup.mem_zpowers s))
  have hxX₀ : x ∈ X₀ := Subgroup.mem_sup_right (Subgroup.mem_zpowers x)
  have hSX₀ : S ≤ X₀ := by
    have : Subgroup.zpowers s ⊔ Q ≤ X₀ :=
      sup_le (Subgroup.zpowers_le.mpr hsX₀) hQX₀
    exact hSgen.trans this
  have hX₀M : X₀ ≤ M :=
    sup_le (sup_le hQM (Subgroup.zpowers_le.mpr hsM)) (Subgroup.zpowers_le.mpr hxM)
  have hX₀Q : X₀ ≤ Subgroup.normalizer (Q : Set G) := hX₀M.trans hMQ
  have hX₀V : X₀ ≤ Subgroup.normalizer (V : Set G) := hX₀M.trans hMV
  have hC_norm : X₀ ≤ Subgroup.normalizer (Subgroup.centralizer (V : Set G) : Set G) := by
    intro g hg
    rw [Subgroup.mem_normalizer_iff]
    intro c
    refine ⟨fun hc => conj_mem_centralizer (hX₀V hg) hc, fun hc => ?_⟩
    have := conj_mem_centralizer (V := V) (hX₀V (X₀.inv_mem hg)) hc
    have e : g⁻¹ * (g * c * g⁻¹) * g⁻¹⁻¹ = c := by group
    rw [e] at this
    exact this
  have hO_norm : X₀ ≤ Subgroup.normalizer (pCoreOf 2 X₀ : Set G) :=
    localGroup_le_normalizer_pCoreOf 2 X₀
  have hQn : (Q.subgroupOf X₀).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hQX₀).mpr hX₀Q
  let mk : ↥X₀ →* ↥X₀ ⧸ Q.subgroupOf X₀ := QuotientGroup.mk' (Q.subgroupOf X₀)
  have mk_eq_one : ∀ y : ↥X₀, mk y = 1 ↔ (y : G) ∈ Q := by
    intro y
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
  let sX : ↥X₀ := ⟨s, hsX₀⟩
  let xX : ↥X₀ := ⟨x, hxX₀⟩
  set a : ↥X₀ ⧸ Q.subgroupOf X₀ := mk sX with ha
  set c : ↥X₀ ⧸ Q.subgroupOf X₀ := mk xX with hc
  have ha2 : a * a = 1 := by
    rw [ha, ← map_mul, mk_eq_one]; exact hsQ
  have hc3 : c ^ 3 = 1 := by
    rw [hc, ← map_pow, mk_eq_one]; exact hx3
  have hac : a * c * a⁻¹ * c = 1 := by
    rw [ha, hc, ← map_inv, ← map_mul, ← map_mul, ← map_mul, mk_eq_one]; exact hsx
  have hsQ' : s ∉ Q := fun h => hsC (hQC h)
  have hxQ' : x ∉ Q := fun h => hxC (hQC h)
  have ha1 : a ≠ 1 := fun h => hsQ' ((mk_eq_one sX).mp h)
  have hc1 : c ≠ 1 := fun h => hxQ' ((mk_eq_one xX).mp h)
  have ha_inv : a⁻¹ = a := inv_eq_of_mul_eq_one_right ha2
  have hb2 : (a * c) * (a * c) = 1 := by
    calc (a * c) * (a * c) = a * c * a⁻¹ * c := by rw [ha_inv]; group
      _ = 1 := hac
  have hac' : a * (a * c) = c := by rw [← mul_assoc, ha2, one_mul]
  have hab3 : (a * (a * c)) ^ 3 = 1 := by rw [hac']; exact hc3
  have hgen : Subgroup.closure ({a, a * c} : Set (↥X₀ ⧸ Q.subgroupOf X₀)) = ⊤ := by
    rw [eq_top_iff]
    let K : Subgroup ↥X₀ := (Subgroup.closure ({a, a * c} : Set (↥X₀ ⧸ Q.subgroupOf X₀))).comap mk
    have hQK : Q ≤ K.map X₀.subtype := by
      intro q hq
      refine ⟨⟨q, hQX₀ hq⟩, Subgroup.mem_comap.mpr ?_, rfl⟩
      rw [(mk_eq_one _).mpr hq]
      exact Subgroup.one_mem _
    have hsK : Subgroup.zpowers s ≤ K.map X₀.subtype := by
      rw [Subgroup.zpowers_le]
      exact ⟨sX, Subgroup.mem_comap.mpr (Subgroup.subset_closure (Or.inl rfl)), rfl⟩
    have hxK : Subgroup.zpowers x ≤ K.map X₀.subtype := by
      rw [Subgroup.zpowers_le]
      refine ⟨xX, Subgroup.mem_comap.mpr ?_, rfl⟩
      show c ∈ _
      have hmem : a * (a * c) ∈ Subgroup.closure ({a, a * c} : Set (↥X₀ ⧸ Q.subgroupOf X₀)) :=
        Subgroup.mul_mem _ (Subgroup.subset_closure (Or.inl rfl))
          (Subgroup.subset_closure (Or.inr rfl))
      rwa [hac'] at hmem
    have hXK : X₀ ≤ K.map X₀.subtype := sup_le (sup_le hQK hsK) hxK
    intro y _
    obtain ⟨z, rfl⟩ := QuotientGroup.mk_surjective y
    obtain ⟨k, hk, hkz⟩ := hXK z.2
    have : k = z := Subtype.ext hkz
    rw [this] at hk
    exact hk
  have hnot : ¬ ∀ q : ↥X₀ ⧸ Q.subgroupOf X₀, ∃ n : ℕ, q ^ 2 ^ n = 1 := by
    intro h
    obtain ⟨n, hn⟩ := h c
    exact hc1 (eq_one_of_pow_three_of_pow_two_pow hc3 hn)
  obtain ⟨e⟩ := nonempty_mulEquiv_perm_three_of_involutions' ha2 hb2 hab3 ha1 hgen hnot
  set π : ↥X₀ →* Equiv.Perm (Fin 3) := e.toMonoidHom.comp mk with hπdef
  have hπ1 : ∀ y : ↥X₀, π y = 1 ↔ (y : G) ∈ Q := by
    intro y
    show e (mk y) = 1 ↔ _
    rw [e.map_eq_one_iff, mk_eq_one]
  set A : Equiv.Perm (Fin 3) := e a with hA
  set R : Equiv.Perm (Fin 3) := e c with hR
  have hA2 : A * A = 1 := by rw [hA, ← map_mul, ha2, map_one]
  have hAne : A ≠ 1 := fun h => ha1 (e.map_eq_one_iff.mp h)
  have hR3 : R ^ 3 = 1 := by rw [hR, ← map_pow, hc3, map_one]
  have hRne : R ≠ 1 := fun h => hc1 (e.map_eq_one_iff.mp h)
  have hR3' : R⁻¹ ^ 3 = 1 := by rw [inv_pow, hR3, inv_one]
  have hdich : ∀ (y : G) (hy : y ∈ X₀), π ⟨y, hy⟩ ≠ 1 →
      ∃ (y' : G) (hy' : y' ∈ X₀),
        (y ∈ Subgroup.centralizer (V : Set G) → y' ∈ Subgroup.centralizer (V : Set G)) ∧
        (y ∈ pCoreOf 2 X₀ → y' ∈ pCoreOf 2 X₀) ∧ (π ⟨y', hy'⟩ = R ∨ π ⟨y', hy'⟩ = R⁻¹) := by
    intro y hy hne
    rcases perm3_cases (π ⟨y, hy⟩) R hR3 hRne hne with h | h | h | h
    · exact ⟨y, hy, id, id, Or.inl h⟩
    · exact ⟨y, hy, id, id, Or.inr h⟩
    all_goals
      have hw : y * x * y⁻¹ * x⁻¹ ∈ X₀ :=
        X₀.mul_mem (X₀.mul_mem (X₀.mul_mem hy hxX₀) (X₀.inv_mem hy)) (X₀.inv_mem hxX₀)
      have hπw : π ⟨y * x * y⁻¹ * x⁻¹, hw⟩ = π ⟨y, hy⟩ * R * (π ⟨y, hy⟩)⁻¹ * R⁻¹ := by
        show π (⟨y, hy⟩ * xX * ⟨y, hy⟩⁻¹ * xX⁻¹) = _
        simp only [map_mul, map_inv]
        rfl
    · exact ⟨y * x * y⁻¹ * x⁻¹, hw,
        fun hyC => commutator_mem_of_mem_normalizer (hC_norm hxX₀) hyC,
        fun hyO => commutator_mem_of_mem_normalizer (hO_norm hxX₀) hyO, Or.inl (by rw [hπw]; exact h)⟩
    · exact ⟨y * x * y⁻¹ * x⁻¹, hw,
        fun hyC => commutator_mem_of_mem_normalizer (hC_norm hxX₀) hyC,
        fun hyO => commutator_mem_of_mem_normalizer (hO_norm hxX₀) hyO, Or.inr (by rw [hπw]; exact h)⟩
  have hbadC : ∀ (y' : G) (hy' : y' ∈ X₀), (π ⟨y', hy'⟩ = R ∨ π ⟨y', hy'⟩ = R⁻¹) →
      y' ∈ Subgroup.centralizer (V : Set G) → False := by
    intro y' hy' hRy hyC
    rcases hRy with hRy | hRy
    · have h1 : π (xX⁻¹ * ⟨y', hy'⟩) = 1 := by
        rw [map_mul, map_inv, hRy]
        exact inv_mul_cancel R
      have h2 : x⁻¹ * y' ∈ Q := (hπ1 _).mp h1
      apply hxC
      have h3 := Subgroup.mul_mem _ hyC (Subgroup.inv_mem _ (hQC h2))
      have e1 : y' * (x⁻¹ * y')⁻¹ = x := by group
      rwa [e1] at h3
    · have h1 : π (xX * ⟨y', hy'⟩) = 1 := by
        rw [map_mul, hRy]
        exact mul_inv_cancel R
      have h2 : x * y' ∈ Q := (hπ1 _).mp h1
      apply hxC
      have h3 := Subgroup.mul_mem _ (hQC h2) (Subgroup.inv_mem _ hyC)
      have e1 : x * y' * y'⁻¹ = x := by group
      rwa [e1] at h3
  have hbadO : ∀ (y' : G) (hy' : y' ∈ X₀), (π ⟨y', hy'⟩ = R ∨ π ⟨y', hy'⟩ = R⁻¹) →
      y' ∈ pCoreOf 2 X₀ → False := by
    intro y' hy' hRy hyO
    obtain ⟨k, hk⟩ := pCoreOf_isPGroup 2 X₀ ⟨y', hyO⟩
    have hk' : (⟨y', hy'⟩ : ↥X₀) ^ 2 ^ k = 1 := Subtype.ext (by simpa using congrArg Subtype.val hk)
    have hk'' : π ⟨y', hy'⟩ ^ 2 ^ k = 1 := by rw [← map_pow, hk', map_one]
    rcases hRy with hRy | hRy
    · rw [hRy] at hk''
      exact hRne (eq_one_of_pow_three_of_pow_two_pow hR3 hk'')
    · rw [hRy] at hk''
      exact hRne (inv_eq_one.mp (eq_one_of_pow_three_of_pow_two_pow hR3' hk''))
  have hK2 : ∀ y ∈ X₀, y ∈ Subgroup.centralizer (V : Set G) → y ∈ Q := by
    intro y hy hyC
    by_contra hyQ
    have hne : π ⟨y, hy⟩ ≠ 1 := fun h => hyQ ((hπ1 _).mp h)
    obtain ⟨y', hy', hC', -, hRy⟩ := hdich y hy hne
    exact hbadC y' hy' hRy (hC' hyC)
  have hK3 : ∀ y ∈ pCoreOf 2 X₀, y ∈ Q := by
    intro y hy
    have hyX : y ∈ X₀ := pCoreOf_le 2 X₀ hy
    by_contra hyQ
    have hne : π ⟨y, hyX⟩ ≠ 1 := fun h => hyQ ((hπ1 _).mp h)
    obtain ⟨y', hy', -, hO', hRy⟩ := hdich y hyX hne
    exact hbadO y' hy' hRy (hO' hy)
  have hQ' : pCoreOf 2 X₀ = Q :=
    le_antisymm hK3 (normal_pGroup_le_pCoreOf 2 Q X₀ hQX₀ hQn hQ2)
  have hpc : CFSG.Open.pCore 2 ↥X₀ = Q.subgroupOf X₀ := by
    ext y
    rw [Subgroup.mem_subgroupOf, ← hQ']
    constructor
    · intro hy
      exact ⟨y, hy, rfl⟩
    · rintro ⟨y', hy', hyy⟩
      have : y' = y := Subtype.ext hyy
      rwa [this] at hy'
  let e' : OTwoQuot X₀ ≃* Equiv.Perm (Fin 3) := (QuotientGroup.quotientMulEquivOfEq hpc).trans e
  have hApow : ∀ k : ℤ, A ^ k = 1 ∨ A ^ k = A := by
    intro k
    rcases Int.even_or_odd' k with ⟨m, rfl | rfl⟩
    · left; rw [zpow_mul, zpow_two, hA2, one_zpow]
    · right; rw [zpow_add_one, zpow_mul, zpow_two, hA2, one_zpow, one_mul]
  have hSπ : ∀ (y : G) (hy : y ∈ S), π ⟨y, hSX₀ hy⟩ = 1 ∨ π ⟨y, hSX₀ hy⟩ = A := by
    intro y hy
    have hy' : y ∈ Q ⊔ Subgroup.zpowers s := by rw [sup_comm]; exact hSgen hy
    have hsN : Subgroup.zpowers s ≤ Subgroup.normalizer (Q : Set G) :=
      Subgroup.zpowers_le.mpr (hMQ hsM)
    obtain ⟨q, hq, t, ht, rfl⟩ := mem_sup_of_le_normalizer hsN hy'
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp ht
    have hqX : q ∈ X₀ := hQX₀ hq
    have hsk : s ^ k ∈ X₀ := X₀.zpow_mem hsX₀ k
    have h1 : π ⟨q * s ^ k, hSX₀ hy⟩ = π ⟨q, hqX⟩ * A ^ k := by
      show π (⟨q, hqX⟩ * sX ^ k) = _
      rw [map_mul, map_zpow]
      rfl
    have h2 : π ⟨q, hqX⟩ = 1 := (hπ1 _).mpr hq
    rw [h1, h2, one_mul]
    exact hApow k
  have hπs : Function.Surjective π := e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hodd : ¬ 2 ∣ (S.subgroupOf X₀).index := by
    set T : Subgroup ↥X₀ := S.subgroupOf X₀ with hT
    have hkerT : π.ker ≤ T := by
      intro y hy
      rw [MonoidHom.mem_ker, hπ1] at hy
      exact Subgroup.mem_subgroupOf.mpr (hQS hy)
    have hTc : T = (T.map π).comap π := by
      rw [Subgroup.comap_map_eq, sup_eq_left.mpr hkerT]
    have hidx : T.index = (T.map π).index := by
      have h := Subgroup.index_comap_of_surjective (T.map π) hπs
      rw [← hTc] at h
      exact h
    have hH₂ : T.map π = Subgroup.zpowers A := by
      apply le_antisymm
      · rintro _ ⟨t, ht, rfl⟩
        have htS : (t : G) ∈ S := Subgroup.mem_subgroupOf.mp ht
        have := hSπ (t : G) htS
        rcases this with h | h
        · rw [show π t = 1 from h]
          exact Subgroup.one_mem _
        · rw [show π t = A from h]
          exact Subgroup.mem_zpowers A
      · rw [Subgroup.zpowers_le]
        exact ⟨sX, Subgroup.mem_subgroupOf.mpr hsS, rfl⟩
    have hcard : Nat.card (T.map π) = 2 := by
      rw [hH₂, Nat.card_zpowers]
      exact orderOf_eq_prime (by rw [pow_two]; exact hA2) hAne
    have hmul := Subgroup.card_mul_index (T.map π)
    rw [hcard, card_perm3] at hmul
    rw [hidx]
    omega
  have hsyl : IsSylowTwoOf S X₀ := ⟨hSX₀, hS2, hodd⟩
  have hcent : X₀ ⊓ Subgroup.centralizer (V : Set G) = pCoreOf 2 X₀ := by
    rw [hQ']
    ext y
    constructor
    · rintro ⟨hy, hyC⟩
      exact hK2 y hy hyC
    · intro hy
      exact ⟨hQX₀ hy, hQC hy⟩
  have hpush : PushHyp X₀ S V :=
    ⟨hsyl, hX₀V, hVel, by rw [hQ']; exact hVQ, hcent⟩
  have hnc : NoCharNormal S X₀ := by
    intro C hCS hC1 hchar hnorm
    have hxN : x ∈ Subgroup.normalizer (C : Set G) := hnorm hxX₀
    have hxS : x ∈ Subgroup.normalizer (S : Set G) := hcgs C hCS hC1 hchar x hxM hxN
    have hxsx : x * s * x⁻¹ ∈ S := (Subgroup.mem_normalizer_iff.mp hxS s).mp hsS
    have hmem := hSπ _ hxsx
    have hπ' : π ⟨x * s * x⁻¹, hSX₀ hxsx⟩ = R * A * R⁻¹ := by
      show π (xX * sX * xX⁻¹) = _
      simp only [map_mul, map_inv]
      rfl
    rw [hπ'] at hmem
    rcases hmem with h | h
    · exact perm3_conj_ne_one A R hA2 hAne hR3 hRne h
    · exact perm3_conj_ne_self A R hA2 hAne hR3 hRne h
  have hbc : BaumannC X₀ V := baumann_c_s3 hpush ⟨e'⟩ hnc
  obtain ⟨k, hk⟩ := exists_pow_mem_pResidualOf X₀ hxX₀
  refine ⟨k, fun q hq => ?_⟩
  have h1 : ⁅q, x ^ 2 ^ k⁆ ∈ ⁅pCoreOf 2 X₀, pResidualOf 2 X₀⁆ :=
    Subgroup.commutator_mem_commutator (by rw [hQ']; exact hq) hk
  exact (show ⁅pCoreOf 2 X₀, pResidualOf 2 X₀⁆ ≤ V from hbc) h1

end ShortComm

end CFSG.HardMathSupport.Cooperstein.StructureLie
