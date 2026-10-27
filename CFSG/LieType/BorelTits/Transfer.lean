module

public import CFSG.LieType.BorelTits.Basic

public section

namespace CFSG.LieType.BorelTits

open CFSG.Open

variable {Γ : Type*} [Group Γ] {Y : Subgroup Γ}

theorem le_of_isPGroup_of_coprime_index [Finite Γ] {p : ℕ} [Y.Normal]
    (hY : Nat.Coprime Y.index p) {P : Subgroup Γ} (hP : IsPGroup p P) : P ≤ Y := by
  intro x hx
  obtain ⟨k, hk⟩ := hP ⟨x, hx⟩
  have hxk : x ^ p ^ k = 1 := by simpa using congrArg Subtype.val hk
  have hpow : (x : Γ ⧸ Y) ^ p ^ k = 1 := by
    rw [← QuotientGroup.mk_pow, hxk, QuotientGroup.mk_one]
  have hdvd : orderOf (x : Γ ⧸ Y) ∣ Y.index := by
    rw [Subgroup.index]
    exact orderOf_dvd_natCard _
  have hord : orderOf (x : Γ ⧸ Y) = 1 :=
    Nat.Coprime.eq_one_of_dvd (Nat.Coprime.coprime_dvd_left hdvd (Nat.Coprime.pow_right _ hY))
      (orderOf_dvd_of_pow_eq_one hpow)
  rw [orderOf_eq_one_iff, QuotientGroup.eq_one_iff] at hord
  exact hord

theorem coe_mem_normalizer_map_subtype {H : Subgroup Y} {x : Y}
    (hx : x ∈ Subgroup.normalizer (H : Set Y)) :
    (x : Γ) ∈ Subgroup.normalizer ((H.map Y.subtype : Subgroup Γ) : Set Γ) :=
  Subgroup.le_normalizer_map Y.subtype (Subgroup.mem_map_of_mem _ hx)

theorem map_conjNormal_le [Y.Normal] {V : Subgroup Y} {x : Γ}
    (hx : x ∈ Subgroup.normalizer ((V.map Y.subtype : Subgroup Γ) : Set Γ)) :
    V.map (MulAut.conjNormal x : MulAut Y).toMonoidHom ≤ V := by
  rintro _ ⟨v, hv, rfl⟩
  have h1 : x * (v : Γ) * x⁻¹ ∈ V.map Y.subtype :=
    (Subgroup.mem_normalizer_iff.mp hx _).mp (Subgroup.mem_map_of_mem _ hv)
  obtain ⟨u, hu, hu'⟩ := Subgroup.mem_map.mp h1
  have heq : u = (MulAut.conjNormal x : MulAut Y) v := by
    apply Subtype.ext
    rw [MulAut.conjNormal_apply]
    exact hu'
  rw [MulEquiv.coe_toMonoidHom, ← heq]
  exact hu

theorem map_conjNormal_eq [Y.Normal] {V : Subgroup Y} {x : Γ}
    (hx : x ∈ Subgroup.normalizer ((V.map Y.subtype : Subgroup Γ) : Set Γ)) :
    V.map (MulAut.conjNormal x : MulAut Y).toMonoidHom = V := by
  refine le_antisymm (map_conjNormal_le hx) fun v hv => ?_
  have hv' := map_conjNormal_le (inv_mem hx) (Subgroup.mem_map_of_mem _ hv)
  refine ⟨(MulAut.conjNormal x⁻¹ : MulAut Y) v, hv', ?_⟩
  apply Subtype.ext
  simp only [MulEquiv.coe_toMonoidHom, MulAut.conjNormal_apply]
  group

theorem pCoreOf_normalizer_le_subgroupOf [Finite Γ] {p : ℕ} [Fact p.Prime] [Y.Normal]
    {V : Subgroup Y} {P : Subgroup Γ}
    (hcore : pCoreOf p (Subgroup.normalizer ((V.map Y.subtype : Subgroup Γ) : Set Γ)) ≤
      pCoreOf p P) :
    pCoreOf p (Subgroup.normalizer (V : Set Y)) ≤ pCoreOf p (P.subgroupOf Y) := by
  set M := Subgroup.normalizer (V : Set Y) with hM
  set Q₁ := pCoreOf p M with hQ₁
  set Q₁' := Q₁.map Y.subtype with hQ₁'
  have hQ₁M : Q₁ ≤ M := pCoreOf_le p M
  have hQ₁p : IsPGroup p Q₁' := (pCoreOf_isPGroup p M).map _
  have hconj : ∀ x ∈ Subgroup.normalizer ((V.map Y.subtype : Subgroup Γ) : Set Γ),
      ∀ z ∈ Q₁', x * z * x⁻¹ ∈ Q₁' := by
    intro x hx z hz
    obtain ⟨q, hq, rfl⟩ := Subgroup.mem_map.mp hz
    let φ : Y ≃* Y := MulAut.conjNormal x
    have hVφ : V.map φ.toMonoidHom = V := map_conjNormal_eq hx
    have hMφ : M.map φ.toMonoidHom = M := by
      rw [hM, Subgroup.map_equiv_normalizer_eq, hVφ]
    have hQφ : Q₁.map φ.toMonoidHom = Q₁ := by
      rw [hQ₁, ← pCoreOf_map_mulEquiv, hMφ]
    have hφq : φ q ∈ Q₁ := by
      rw [← hQφ]
      exact Subgroup.mem_map_of_mem _ hq
    refine Subgroup.mem_map.mpr ⟨φ q, hφq, ?_⟩
    simp only [Subgroup.coe_subtype]
    exact MulAut.conjNormal_apply x q
  have hnorm : Subgroup.normalizer ((V.map Y.subtype : Subgroup Γ) : Set Γ) ≤
      Subgroup.normalizer (Q₁' : Set Γ) := by
    intro x hx
    rw [Subgroup.mem_normalizer_iff]
    intro z
    refine ⟨fun hz => hconj x hx z hz, fun hz => ?_⟩
    have := hconj x⁻¹ (inv_mem hx) _ hz
    simpa [mul_assoc] using this
  have hQ₁'N : Q₁' ≤ Subgroup.normalizer ((V.map Y.subtype : Subgroup Γ) : Set Γ) := by
    rintro _ ⟨q, hq, rfl⟩
    exact coe_mem_normalizer_map_subtype (hQ₁M hq)
  have hQ₁'core : Q₁' ≤ pCoreOf p P :=
    (le_pCoreOf_of_le_normalizer p hQ₁'N hnorm hQ₁p).trans hcore
  set C := (pCoreOf p P).subgroupOf Y with hC
  have hCP : C ≤ P.subgroupOf Y := Subgroup.subgroupOf_mono Y (pCoreOf_le p P)
  have hPC : P.subgroupOf Y ≤ Subgroup.normalizer (C : Set Y) := by
    intro y hy
    rw [Subgroup.mem_subgroupOf] at hy
    have hyN := le_normalizer_pCoreOf p P hy
    rw [Subgroup.mem_normalizer_iff]
    intro z
    simp only [hC, Subgroup.mem_subgroupOf, Subgroup.coe_mul, Subgroup.coe_inv]
    exact Subgroup.mem_normalizer_iff.mp hyN z
  have hCp : IsPGroup p C := (pCoreOf_isPGroup p P).comap_subtype
  have hCcore : C ≤ pCoreOf p (P.subgroupOf Y) := le_pCoreOf_of_le_normalizer p hCP hPC hCp
  intro q hq
  refine hCcore ?_
  rw [hC, Subgroup.mem_subgroupOf]
  exact hQ₁'core (Subgroup.mem_map_of_mem _ hq)

theorem normalizer_le_subgroupOf {V : Subgroup Y} {P : Subgroup Γ}
    (hN : Subgroup.normalizer ((V.map Y.subtype : Subgroup Γ) : Set Γ) ≤ P) :
    Subgroup.normalizer (V : Set Y) ≤ P.subgroupOf Y := fun _ hx =>
  Subgroup.mem_subgroupOf.mpr (hN (coe_mem_normalizer_map_subtype hx))

theorem Holds.of_normal_of_coprime_index [Finite Γ] {p : ℕ} [Fact p.Prime] [Y.Normal]
    (hY : Nat.Coprime Y.index p) (h : Holds Γ p) : Holds Y p := by
  intro V hV hVp
  set V' := V.map Y.subtype with hV'
  have hV'ne : V' ≠ ⊥ := by
    intro hbot
    apply hV
    rw [eq_bot_iff]
    intro v hv
    have : (v : Γ) ∈ V' := Subgroup.mem_map_of_mem _ hv
    rw [hbot, Subgroup.mem_bot] at this
    exact Subtype.ext this
  obtain ⟨S, P, hP, hN, hcore, -, hS⟩ := h V' hV'ne (hVp.map _)
  have hSY : (S : Subgroup Γ) ≤ Y := le_of_isPGroup_of_coprime_index hY S.isPGroup'
  let S₀ : Sylow p Y := S.subtype hSY
  have hS₀ : (S₀ : Subgroup Y).map Y.subtype = S := by
    rw [Sylow.coe_subtype, Subgroup.map_subgroupOf_eq_of_le hSY]
  refine conclusion_of_core p V hVp S₀ (P.subgroupOf Y) ?_ (normalizer_le_subgroupOf hN)
    (pCoreOf_normalizer_le_subgroupOf hcore) ?_
  · intro htop
    apply hP
    have hYP : Y ≤ P := Subgroup.subgroupOf_eq_top.mp htop
    have hfr := Sylow.normalizer_sup_eq_top (p := p) (N := Y) S₀
    rw [hS₀] at hfr
    rw [eq_top_iff, ← hfr]
    exact sup_le hS hYP
  · intro x hx
    rw [Subgroup.mem_subgroupOf]
    apply hS
    have := coe_mem_normalizer_map_subtype hx
    rwa [hS₀] at this

theorem conclusion_of_normal_of_index_eq [Finite Γ] {p : ℕ} [Fact p.Prime] [Y.Normal]
    (hY : Y.index = p) (h : Holds Γ p) (V : Subgroup Y) (hV : V ≠ ⊥) (hVp : IsPGroup p V) :
    ∃ (S : Sylow p Y) (P : Subgroup Y), P ≠ ⊤ ∧ Subgroup.normalizer (V : Set Y) ≤ P ∧
      pCoreOf p (Subgroup.normalizer (V : Set Y)) ≤ pCoreOf p P ∧ V ≤ pCoreOf p P ∧
      (S : Subgroup Y) ≤ P := by
  set V' := V.map Y.subtype with hV'
  have hV'ne : V' ≠ ⊥ := by
    intro hbot
    apply hV
    rw [eq_bot_iff]
    intro v hv
    have : (v : Γ) ∈ V' := Subgroup.mem_map_of_mem _ hv
    rw [hbot, Subgroup.mem_bot] at this
    exact Subtype.ext this
  obtain ⟨S, P, hP, hN, hcore, -, hS⟩ := h V' hV'ne (hVp.map _)
  have hp : p.Prime := Fact.out
  have hSP : (S : Subgroup Γ) ≤ P := Subgroup.le_normalizer.trans hS
  have hSY : ¬ (S : Subgroup Γ) ≤ Y := by
    intro hle
    have hdvd := Subgroup.index_dvd_of_le hle
    rw [hY] at hdvd
    exact S.not_dvd_index hdvd
  have hsup : (S : Subgroup Γ) ⊔ Y = ⊤ := by
    have hmul := Subgroup.relIndex_mul_index (le_sup_right : Y ≤ (S : Subgroup Γ) ⊔ Y)
    rw [hY] at hmul
    have hprime : (Y.relIndex ((S : Subgroup Γ) ⊔ Y) * ((S : Subgroup Γ) ⊔ Y).index).Prime := by
      rw [hmul]
      exact hp
    rcases Nat.prime_mul_iff.mp hprime with ⟨-, h1⟩ | ⟨-, h1⟩
    · exact Subgroup.index_eq_one.mp h1
    · exact absurd (le_sup_left.trans (Subgroup.relIndex_eq_one.mp h1)) hSY
  have hPtop : P.subgroupOf Y ≠ ⊤ := by
    intro htop
    apply hP
    have hYP : Y ≤ P := Subgroup.subgroupOf_eq_top.mp htop
    rw [eq_top_iff, ← hsup]
    exact sup_le hSP hYP
  set T := (S : Subgroup Γ).subgroupOf Y with hT
  have hTp : IsPGroup p T := S.isPGroup'.comap_subtype
  have hTidx : T.index = (S : Subgroup Γ).index := by
    have h1 := Subgroup.relIndex_mul_index (inf_le_right : (S : Subgroup Γ) ⊓ Y ≤ Y)
    have h2 := Subgroup.relIndex_mul_index (inf_le_left : (S : Subgroup Γ) ⊓ Y ≤ S)
    rw [Subgroup.inf_relIndex_right, hY] at h1
    rw [Subgroup.inf_relIndex_left, ← Subgroup.relIndex_sup_right, hsup,
      Subgroup.relIndex_top_right, hY] at h2
    have h3 : (S : Subgroup Γ).relIndex Y * p = p * (S : Subgroup Γ).index := by
      rw [h1, h2]
    have h4 : (S : Subgroup Γ).relIndex Y = (S : Subgroup Γ).index := by
      have := hp.pos
      nlinarith
    rw [hT, ← Subgroup.relIndex, h4]
  have hTndvd : ¬ p ∣ T.index := by
    rw [hTidx]
    exact S.not_dvd_index
  refine ⟨hTp.toSylow hTndvd, P.subgroupOf Y, hPtop, normalizer_le_subgroupOf hN,
    pCoreOf_normalizer_le_subgroupOf hcore,
    (le_pCoreOf_normalizer p V hVp).trans (pCoreOf_normalizer_le_subgroupOf hcore), ?_⟩
  intro x hx
  exact Subgroup.subgroupOf_mono Y hSP ((IsPGroup.mem_toSylow hTp hTndvd).mp hx)

theorem conclusion_of_normal_of_isPGroup_quotient [Finite Γ] {p : ℕ} [Fact p.Prime] [Y.Normal]
    (hY : IsPGroup p (Γ ⧸ Y)) (h : Holds Γ p) (V : Subgroup Y) (hV : V ≠ ⊥)
    (hVp : IsPGroup p V) :
    ∃ (S : Sylow p Y) (P : Subgroup Y), P ≠ ⊤ ∧ Subgroup.normalizer (V : Set Y) ≤ P ∧
      pCoreOf p (Subgroup.normalizer (V : Set Y)) ≤ pCoreOf p P ∧ V ≤ pCoreOf p P ∧
      (S : Subgroup Y) ≤ P := by
  set V' := V.map Y.subtype with hV'
  have hV'ne : V' ≠ ⊥ := by
    intro hbot
    apply hV
    rw [eq_bot_iff]
    intro v hv
    have : (v : Γ) ∈ V' := Subgroup.mem_map_of_mem _ hv
    rw [hbot, Subgroup.mem_bot] at this
    exact Subtype.ext this
  obtain ⟨S, P, hP, hN, hcore, -, hS⟩ := h V' hV'ne (hVp.map _)
  have hp : p.Prime := Fact.out
  have hSP : (S : Subgroup Γ) ≤ P := Subgroup.le_normalizer.trans hS
  obtain ⟨k, hk⟩ : ∃ k, Y.index = p ^ k := by
    obtain ⟨k, hk⟩ := (IsPGroup.iff_card.mp hY)
    exact ⟨k, by rw [Subgroup.index, hk]⟩
  have hsup : (S : Subgroup Γ) ⊔ Y = ⊤ := by
    have h1 : ((S : Subgroup Γ) ⊔ Y).index ∣ p ^ k :=
      hk ▸ Subgroup.index_dvd_of_le le_sup_right
    have h2 : ((S : Subgroup Γ) ⊔ Y).index ∣ (S : Subgroup Γ).index :=
      Subgroup.index_dvd_of_le le_sup_left
    obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow hp).mp h1
    rcases j with _ | j
    · exact Subgroup.index_eq_one.mp (by simpa using hj)
    · exfalso
      apply S.not_dvd_index
      rw [hj, pow_succ] at h2
      exact (Dvd.intro_left _ rfl).trans h2
  have hPtop : P.subgroupOf Y ≠ ⊤ := by
    intro htop
    apply hP
    have hYP : Y ≤ P := Subgroup.subgroupOf_eq_top.mp htop
    rw [eq_top_iff, ← hsup]
    exact sup_le hSP hYP
  set T := (S : Subgroup Γ).subgroupOf Y with hT
  have hTp : IsPGroup p T := S.isPGroup'.comap_subtype
  have hTidx : T.index = (S : Subgroup Γ).index := by
    have h1 := Subgroup.relIndex_mul_index (inf_le_right : (S : Subgroup Γ) ⊓ Y ≤ Y)
    have h2 := Subgroup.relIndex_mul_index (inf_le_left : (S : Subgroup Γ) ⊓ Y ≤ S)
    rw [Subgroup.inf_relIndex_right] at h1
    rw [Subgroup.inf_relIndex_left, ← Subgroup.relIndex_sup_right, hsup,
      Subgroup.relIndex_top_right] at h2
    have hYpos : 0 < Y.index := Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite
    have h3 : (S : Subgroup Γ).relIndex Y * Y.index = Y.index * (S : Subgroup Γ).index := by
      rw [h1, h2]
    have h4 : (S : Subgroup Γ).relIndex Y = (S : Subgroup Γ).index := by
      rw [mul_comm] at h3
      exact Nat.eq_of_mul_eq_mul_left hYpos h3
    rw [hT, ← Subgroup.relIndex, h4]
  have hTndvd : ¬ p ∣ T.index := by
    rw [hTidx]
    exact S.not_dvd_index
  refine ⟨hTp.toSylow hTndvd, P.subgroupOf Y, hPtop, normalizer_le_subgroupOf hN,
    pCoreOf_normalizer_le_subgroupOf hcore,
    (le_pCoreOf_normalizer p V hVp).trans (pCoreOf_normalizer_le_subgroupOf hcore), ?_⟩
  intro x hx
  exact Subgroup.subgroupOf_mono Y hSP ((IsPGroup.mem_toSylow hTp hTndvd).mp hx)

end CFSG.LieType.BorelTits
