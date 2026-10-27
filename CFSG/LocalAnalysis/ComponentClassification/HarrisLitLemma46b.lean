module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitLemma46a

public noncomputable section

namespace CFSG.ComponentClassification.HarrisLit

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer CFSG.ABGLocalTools

variable {X : Type} [Group X] [Finite X]

theorem nonempty_mulEquiv_of_isSylowOf {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {P P' K : Subgroup G} (h : IsSylowOf p P K) (h' : IsSylowOf p P' K) :
    Nonempty (↥P' ≃* ↥P) := by
  obtain ⟨k, -, hk⟩ := h.exists_mem_conj h'
  have hmap : P'.map (MulAut.conj k⁻¹).toMonoidHom = P := by
    ext y
    simp only [mem_map, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact (hk x).mp hx
    · intro hy
      refine ⟨k * y * k⁻¹, (hk _).mpr ?_, by group⟩
      rwa [show k⁻¹ * (k * y * k⁻¹) * k = y by group]
  exact ⟨(equivMapOfInjective P' _ (MulAut.conj k⁻¹).injective).trans
    (MulEquiv.subgroupCongr hmap)⟩

theorem exists_lift_of_isPGroup {H : Type*} [Group H] [Finite H] {A : Subgroup H}
    (hA : IsPGroup 2 A) {R : Subgroup (H ⧸ pPrimeCore 2 H)} (hR : IsPGroup 2 R)
    (hAR : A.map (QuotientGroup.mk' (pPrimeCore 2 H)) ≤ R) :
    ∃ U : Subgroup H, IsPGroup 2 U ∧ A ≤ U ∧ U.map (QuotientGroup.mk' (pPrimeCore 2 H)) = R := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set π := QuotientGroup.mk' (pPrimeCore 2 H)
  have hAP : A ≤ R.comap π := map_le_iff_le_comap.mp hAR
  obtain ⟨U, hU, hAU⟩ := exists_isSylowOf_ge hA hAP
  refine ⟨U, hU.isPGroup, hAU, ?_⟩
  have h1 := isSylowOf_map π hU
  rw [map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective _)] at h1
  exact (h1.eq_of_le h1.le le_rfl hR).symm

theorem nonempty_mulEquiv_map_mk {H : Type*} [Group H] [Finite H] {U : Subgroup H}
    (hU : IsPGroup 2 U) :
    Nonempty (↥U ≃* ↥(U.map (QuotientGroup.mk' (pPrimeCore 2 H)))) := by
  have hinj : Function.Injective ((QuotientGroup.mk' (pPrimeCore 2 H)).comp U.subtype) :=
    fun x y hxy => Subtype.ext (GSThmB.OddQuot.injOn_of_isPGroup hU x.2 y.2 hxy)
  refine ⟨(MonoidHom.ofInjective hinj).trans (MulEquiv.subgroupCongr ?_)⟩
  rw [MonoidHom.range_comp, range_subtype]

@[expose] def betaBar (β : X) : MBar β :=
  QuotientGroup.mk ⟨β, mem_centralizer_singleton_iff.mpr rfl⟩

omit [Finite X] in
theorem betaBar_mem_center (β : X) : betaBar β ∈ center (MBar β) := by
  rw [mem_center_iff]
  intro g
  obtain ⟨m, rfl⟩ := QuotientGroup.mk_surjective g
  rw [betaBar, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
  congr 1
  exact Subtype.ext (mem_centralizer_singleton_iff.mp m.2)

variable {t : X} {L : Subgroup X} {p f : ℕ}

namespace Standing.Setup42

variable {h : Standing t L p f} {S : Subgroup X} {hS : IsSylowOf 2 S (centralizer ({t} : Set X))}
  {w z : X}

omit [Finite X] in
theorem betaBar_mem_centralizer_K (β : X) :
    betaBar β ∈ centralizer (KBar L β : Set (MBar β)) :=
  mem_centralizer_iff.mpr fun y _ => mem_center_iff.mp (betaBar_mem_center β) y

theorem tBar_mem_centralizer_K (hσ : Setup42 h hS w z) (i j : ℕ) :
    hσ.tBar i j ∈ centralizer (KBar L (w ^ (orderOf w / 2) * t ^ i * z ^ j) :
      Set (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j))) := by
  refine mem_centralizer_iff.mpr ?_
  rintro _ ⟨k, hk, rfl⟩
  rw [tBar, QuotientGroup.mk'_apply, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
  congr 1
  exact Subtype.ext (mem_centralizer_singleton_iff.mp (h.K_le_M _ hk).1)

theorem shape_of_le_centralizer_K (hFC : AutPSL2FieldCentralizerInput)
    (hKC : AutPSL2CentralizerInput) (hσ : Setup42 h hS w z) (i j : ℕ) :
    ∀ Q : Subgroup (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)), IsPGroup 2 Q →
      Q ≤ centralizer (KBar L (w ^ (orderOf w / 2) * t ^ i * z ^ j) :
        Set (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j))) →
      hσ.tBar i j ∈ Q → betaBar (w ^ (orderOf w / 2) * t ^ i * z ^ j) ∈ Q →
      (Nat.card Q = 4 ∨ (∃ k : ℕ, 2 ≤ k ∧ Nonempty (↥Q ≃* DihedralGroup (2 ^ k))) ∨
          ∃ n : ℕ, 4 ≤ n ∧ Nonempty (↥Q ≃* CFSG.Open.SemidihedralGroup n)) ∧
        Q ⊓ centralizer {hσ.tBar i j} ≤ closure {hσ.tBar i j,
          betaBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)} := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set β := w ^ (orderOf w / 2) * t ^ i * z ^ j with hβ
  set M := centralizer ({β} : Set X) with hM
  set π := QuotientGroup.mk' (pPrimeCore 2 ↥M) with hπ
  set CK := centralizer (KBar L β : Set (MBar β)) with hCK
  intro Q hQ2 hQK htQ hβQ
  have htM : t ∈ M := hσ.t_mem_centralizer_beta i j
  have hβM : β ∈ M := mem_centralizer_singleton_iff.mpr rfl
  set t' : ↥M := ⟨t, htM⟩ with ht'
  set β' : ↥M := ⟨β, hβM⟩ with hβ'
  set A : Subgroup ↥M := closure {t', β'} with hA
  have hAX : A.map M.subtype = closure {t, β} := by
    rw [hA, MonoidHom.map_closure, Set.image_pair]
    rfl
  have hX2 : ∀ x ∈ closure ({t, β} : Set X), x ^ 2 = 1 := fun x hx =>
    hσ.sq_eq_one_of_mem_X ((closure_le _).mpr (by
      rintro g (rfl | rfl)
      · exact subset_closure (by simp)
      · exact beta_mem_X i j) hx)
  have hA2 : IsPGroup 2 A := fun x => ⟨1, by
    apply Subtype.ext
    apply Subtype.ext
    have hx : ((x : ↥M) : X) ∈ closure ({t, β} : Set X) := by
      rw [← hAX]
      exact ⟨x, x.2, rfl⟩
    simpa using hX2 _ hx⟩
  have hAQ : A.map π ≤ Q := by
    rw [hA, MonoidHom.map_closure, closure_le, Set.image_pair]
    rintro _ (rfl | rfl)
    · exact htQ
    · exact hβQ
  obtain ⟨U, hU2, hAU, hUR₀⟩ := exists_lift_of_isPGroup hA2 hQ2 hAQ
  set W : Subgroup X := U.map M.subtype with hW
  have hW2 : IsPGroup 2 W := hU2.map M.subtype
  have hU0W : closure {t, β} ≤ W := by
    rw [← hAX]
    exact map_mono hAU
  have hWt : W ⊓ centralizer ({t} : Set X) ≤
      centralizer ({t} : Set X) ⊓ coreActionKernel (centralizerResidual L β) := by
    rintro x ⟨⟨u, huU, rfl⟩, hxt⟩
    refine ⟨hxt, show ((u : X)) ∈ coreActionKernel _ from ?_⟩
    have hxM : (u : X) ∈ centralizer ({t} : Set X) ⊓ centralizer {β} := ⟨hxt, u.2⟩
    rw [mem_coreActionKernel]
    refine ⟨h.M_le_normalizer_K β hxM, fun k hk => ?_⟩
    have hkM : k ∈ M := K_le_centralizer_beta (L := L) (w := w) (t := t) (z := z) i j hk
    have hcK : k⁻¹ * (u : X)⁻¹ * k * u ∈ centralizerResidual L β := by
      have h1 := (mem_normalizer_iff.mp (inv_mem (h.M_le_normalizer_K β hxM)) k).mp hk
      rw [inv_inv] at h1
      rw [show k⁻¹ * (u : X)⁻¹ * k * u = k⁻¹ * ((u : X)⁻¹ * k * (u : X)) by group]
      exact mul_mem (inv_mem hk) h1
    have hcM : k⁻¹ * (u : X)⁻¹ * k * u ∈ (pPrimeCore 2 ↥M).map M.subtype := by
      have hu : π u ∈ CK := hQK (by rw [← hUR₀]; exact ⟨u, huU, rfl⟩)
      have hkK : π ⟨k, hkM⟩ ∈ KBar L β := ⟨⟨k, hkM⟩, hk, rfl⟩
      have hcomm := mem_centralizer_iff.mp hu _ hkK
      have h1 : π (⟨k, hkM⟩⁻¹ * u⁻¹ * ⟨k, hkM⟩ * u) = 1 := by
        simp only [map_mul, map_inv, mul_assoc]
        rw [hcomm]
        group
      rw [hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
      exact ⟨_, h1, rfl⟩
    have hle : (pPrimeCore 2 ↥M).map M.subtype ⊓ centralizerResidual L β ≤
        (pPrimeCore 2 ↥(centralizerResidual L β)).map (centralizerResidual L β).subtype :=
      le_map_pPrimeCore inf_le_right (fun a ha n hn =>
        ⟨conj_mem_map_pPrimeCore_self
          (K_le_centralizer_beta (L := L) (w := w) (t := t) (z := z) i j ha) hn.1,
          (centralizerResidual L β).mul_mem ((centralizerResidual L β).mul_mem ha hn.2)
            ((centralizerResidual L β).inv_mem ha)⟩)
        (Nat.Coprime.coprime_dvd_right (card_dvd_of_le inf_le_left)
          (coprime_card_map_pPrimeCore _))
    exact hle ⟨hcM, hcK⟩
  have hU0t : closure {t, β} ≤ centralizer ({t} : Set X) := by
    rw [closure_le]
    rintro g (rfl | rfl)
    · exact mem_centralizer_singleton_iff.mpr rfl
    · exact hσ.beta_mem_H i j
  have hWtU : W ⊓ centralizer ({t} : Set X) = closure {t, β} :=
    (hσ.isSylowOf_tβ hFC hKC i j).eq_of_le (le_inf hU0W hU0t) hWt (hW2.to_le inf_le_left)
  have hCQ : Q ⊓ centralizer {hσ.tBar i j} ≤ closure {hσ.tBar i j, betaBar β} := by
    rintro _ ⟨hyQ, hyt⟩
    rw [← hUR₀] at hyQ
    obtain ⟨u, huU, rfl⟩ := hyQ
    have hut : (u : X) * t = t * u := by
      have h1 : π (u * t' * u⁻¹ * t'⁻¹) = 1 := by
        simp only [map_mul, map_inv]
        have := mem_centralizer_singleton_iff.mp hyt
        rw [← hπ] at this
        rw [show π t' = hσ.tBar i j from rfl, this]
        group
      have hmem : u * t' * u⁻¹ * t'⁻¹ ∈ U :=
        mul_mem (mul_mem (mul_mem huU (hAU (subset_closure (by simp)))) (inv_mem huU))
          (inv_mem (hAU (subset_closure (by simp))))
      have h2 := GSThmB.OddQuot.injOn_of_isPGroup hU2 hmem (one_mem U)
        (by rw [map_one]; exact h1)
      have h3 := congrArg Subtype.val h2
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_one] at h3
      rw [mul_inv_eq_one, mul_inv_eq_iff_eq_mul] at h3
      exact h3
    have huW : (u : X) ∈ W ⊓ centralizer ({t} : Set X) :=
      ⟨⟨u, huU, rfl⟩, mem_centralizer_singleton_iff.mpr hut⟩
    rw [hWtU] at huW
    have hu' : u ∈ A := by
      rw [← hAX] at huW
      obtain ⟨a, ha, hau⟩ := huW
      rwa [Subtype.ext hau] at ha
    have hmap : A.map π = closure {hσ.tBar i j, betaBar β} := by
      rw [hA, MonoidHom.map_closure, Set.image_pair]
      rfl
    rw [← hmap]
    exact ⟨u, hu', rfl⟩
  refine ⟨?_, hCQ⟩
  obtain ⟨e₂⟩ := nonempty_mulEquiv_map_mk hU2
  have e₂' : ↥Q ≃* ↥U := (MulEquiv.subgroupCongr hUR₀.symm).trans e₂.symm
  have e₃ : ↥U ≃* ↥W := equivMapOfInjective U M.subtype M.subtype_injective
  have e : ↥Q ≃* ↥W := e₂'.trans e₃
  by_cases hWU : W = closure {t, β}
  · left
    rw [Nat.card_congr e.toEquiv, hWU]
    exact hσ.card_closure_t_beta i j
  · right
    have htU : t ∈ closure ({t, β} : Set X) := subset_closure (by simp)
    have hC : W ⊓ centralizer ((closure {t, β} : Subgroup X) : Set X) ≤ closure {t, β} := by
      calc W ⊓ centralizer ((closure {t, β} : Subgroup X) : Set X) ≤
            W ⊓ centralizer ({t} : Set X) := inf_le_inf_left _ fun x hx =>
              mem_centralizer_singleton_iff.mpr (mem_centralizer_iff.mp hx t htU).symm
        _ = closure {t, β} := hWtU
    rcases QuasithinUnique.suzuki_selfCentralizing_four hW2 hU0W (hσ.card_closure_t_beta i j)
      hX2 hC (fun h' => hWU h'.symm) with ⟨k, hk, ⟨d⟩⟩ | ⟨n, hn, ⟨d⟩⟩
    · exact Or.inl ⟨k, hk, ⟨e.trans d⟩⟩
    · exact Or.inr ⟨n, hn, ⟨e.trans d⟩⟩

theorem lemma46b (hFC : AutPSL2FieldCentralizerInput) (hKC : AutPSL2CentralizerInput)
    (hσ : Setup42 h hS w z) (i j : ℕ) :
    (betaBar (w ^ (orderOf w / 2) * t ^ i * z ^ j) ∈
        centralizer (KBar L (w ^ (orderOf w / 2) * t ^ i * z ^ j) :
          Set (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j))) ∧
      betaBar (w ^ (orderOf w / 2) * t ^ i * z ^ j) ∈
        center (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j))) ∧
    ∀ R : Subgroup (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)), IsSylowOf 2 R
        (centralizer (KBar L (w ^ (orderOf w / 2) * t ^ i * z ^ j) :
          Set (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)))) →
      Nat.card R = 4 ∨ (∃ k : ℕ, 2 ≤ k ∧ Nonempty (↥R ≃* DihedralGroup (2 ^ k))) ∨
        ∃ n : ℕ, 4 ≤ n ∧ Nonempty (↥R ≃* CFSG.Open.SemidihedralGroup n) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set β := w ^ (orderOf w / 2) * t ^ i * z ^ j with hβ
  refine ⟨⟨betaBar_mem_centralizer_K β, betaBar_mem_center β⟩, fun R hR => ?_⟩
  have hU2 : IsPGroup 2 (closure {hσ.tBar i j, betaBar β}) := by
    have htβ : Commute (hσ.tBar i j) (betaBar β) :=
      (mem_center_iff.mp (betaBar_mem_center β) (hσ.tBar i j))
    have ht2 : hσ.tBar i j ^ 2 = 1 := by
      rw [tBar, ← QuotientGroup.mk_pow]
      rw [show (⟨t, hσ.t_mem_centralizer_beta i j⟩ : ↥(centralizer ({β} : Set X))) ^ 2 = 1 from
        Subtype.ext (by rw [Subgroup.coe_pow, ← h.config.orderOf_eq, pow_orderOf_eq_one,
          Subgroup.coe_one]), QuotientGroup.mk_one]
    have hb2 : betaBar β ^ 2 = 1 := by
      rw [betaBar, ← QuotientGroup.mk_pow]
      rw [show (⟨β, mem_centralizer_singleton_iff.mpr rfl⟩ : ↥(centralizer ({β} : Set X))) ^ 2 =
        1 from Subtype.ext (by rw [Subgroup.coe_pow, hσ.sq_eq_one_of_mem_X (beta_mem_X i j),
          Subgroup.coe_one]), QuotientGroup.mk_one]
    intro x
    refine ⟨1, ?_⟩
    rw [pow_one]
    apply Subtype.ext
    rcases mem_closure_pair ht2 hb2 htβ.eq x.2 with hx | hx | hx | hx <;>
      simp only [Subgroup.coe_pow, hx, Subgroup.coe_one, one_pow, ht2, hb2]
    rw [htβ.mul_pow, ht2, hb2, one_mul]
  have hUK : closure {hσ.tBar i j, betaBar β} ≤
      centralizer (KBar L β : Set (MBar β)) := by
    rw [closure_le]
    rintro _ (rfl | rfl)
    · exact hσ.tBar_mem_centralizer_K i j
    · exact betaBar_mem_centralizer_K β
  obtain ⟨R₀, hR₀, hUR⟩ := exists_isSylowOf_ge hU2 hUK
  obtain ⟨e₁⟩ := nonempty_mulEquiv_of_isSylowOf hR₀ hR
  rcases (hσ.shape_of_le_centralizer_K hFC hKC i j R₀ hR₀.isPGroup hR₀.le
      (hUR (subset_closure (Set.mem_insert _ _)))
      (hUR (subset_closure (Set.mem_insert_of_mem _ (Set.mem_singleton _))))).1 with
      h4 | ⟨k, hk, ⟨d⟩⟩ | ⟨n, hn, ⟨d⟩⟩
  · left
    rw [Nat.card_congr e₁.toEquiv, h4]
  · exact Or.inr (Or.inl ⟨k, hk, ⟨e₁.trans d⟩⟩)
  · exact Or.inr (Or.inr ⟨n, hn, ⟨e₁.trans d⟩⟩)

end Standing.Setup42

end CFSG.ComponentClassification.HarrisLit
