module

public import CFSG.LocalAnalysis.ComponentInitial.ProjectiveSymplecticLocalComponentPaired
public import CFSG.LocalAnalysis.ComponentInitial.ProjectiveSymplecticLocalComponentUnitary
public import CFSG.LocalAnalysis.ComponentInitial.ProjectiveUnitaryLocalComponent

public section

namespace CFSG.LocalAnalysis.ComponentInitial.ProjectiveSymplectic

open Module CFSG.ComponentClassification CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  CFSG.LocalAnalysis.ComponentInitial.CentralQuotientLift
open scoped commutatorElement

section Twist

variable {G : Type*} [Group G] {Z : Subgroup G} [Z.Normal]

@[expose] def twistHom (hZ : Z ≤ Subgroup.center G) (T : G) :
    (Subgroup.centralizer {(QuotientGroup.mk' Z) T}).comap (QuotientGroup.mk' Z) →*
      Subgroup.center G where
  toFun g := ⟨(g : G) * T * (g : G)⁻¹ * T⁻¹, hZ (by
    have h1 := Subgroup.mem_centralizer_singleton_iff.mp (Subgroup.mem_comap.mp g.2)
    rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_mul, QuotientGroup.mk_mul,
      QuotientGroup.mk_mul, QuotientGroup.mk_inv, QuotientGroup.mk_inv]
    change (QuotientGroup.mk' Z) (g : G) * (QuotientGroup.mk' Z) T *
      ((QuotientGroup.mk' Z) (g : G))⁻¹ * ((QuotientGroup.mk' Z) T)⁻¹ = 1
    rw [h1]
    group)⟩
  map_one' := Subtype.ext (by simp)
  map_mul' g h := by
    apply Subtype.ext
    have hc : ∀ x : G, x * ((h : G) * T * (h : G)⁻¹ * T⁻¹) =
        ((h : G) * T * (h : G)⁻¹ * T⁻¹) * x := by
      intro x
      have hmem : (h : G) * T * (h : G)⁻¹ * T⁻¹ ∈ Subgroup.center G := hZ (by
        have h1 := Subgroup.mem_centralizer_singleton_iff.mp (Subgroup.mem_comap.mp h.2)
        rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_mul, QuotientGroup.mk_mul,
          QuotientGroup.mk_mul, QuotientGroup.mk_inv, QuotientGroup.mk_inv]
        change (QuotientGroup.mk' Z) (h : G) * (QuotientGroup.mk' Z) T *
          ((QuotientGroup.mk' Z) (h : G))⁻¹ * ((QuotientGroup.mk' Z) T)⁻¹ = 1
        rw [h1]
        group)
      exact (Subgroup.mem_center_iff.mp hmem x)
    change ((g : G) * h) * T * ((g : G) * h)⁻¹ * T⁻¹ =
      ((g : G) * T * (g : G)⁻¹ * T⁻¹) * ((h : G) * T * (h : G)⁻¹ * T⁻¹)
    calc ((g : G) * h) * T * ((g : G) * h)⁻¹ * T⁻¹ =
        (g : G) * ((h : G) * T * (h : G)⁻¹ * T⁻¹) * T * (g : G)⁻¹ * T⁻¹ := by group
      _ = ((h : G) * T * (h : G)⁻¹ * T⁻¹) * ((g : G) * T * (g : G)⁻¹ * T⁻¹) := by
        rw [hc (g : G)]
        group
      _ = ((g : G) * T * (g : G)⁻¹ * T⁻¹) * ((h : G) * T * (h : G)⁻¹ * T⁻¹) :=
        (hc _).symm

theorem commutator_le_range_centralizerProj (hZ : Z ≤ Subgroup.center G) (T : G) :
    _root_.commutator (Subgroup.centralizer {(QuotientGroup.mk' Z) T}) ≤
      (centralizerProj Z T).range := by
  rw [_root_.commutator_def, Subgroup.commutator_le]
  rintro x - y -
  obtain ⟨a, ha⟩ := QuotientGroup.mk'_surjective Z (x : G ⧸ Z)
  obtain ⟨b, hb⟩ := QuotientGroup.mk'_surjective Z (y : G ⧸ Z)
  have haP : a ∈ (Subgroup.centralizer {(QuotientGroup.mk' Z) T}).comap (QuotientGroup.mk' Z) :=
    Subgroup.mem_comap.mpr (by rw [ha]; exact x.2)
  have hbP : b ∈ (Subgroup.centralizer {(QuotientGroup.mk' Z) T}).comap (QuotientGroup.mk' Z) :=
    Subgroup.mem_comap.mpr (by rw [hb]; exact y.2)
  have htw : twistHom hZ T ⁅(⟨a, haP⟩ : (Subgroup.centralizer
      {(QuotientGroup.mk' Z) T}).comap (QuotientGroup.mk' Z)), ⟨b, hbP⟩⁆ = 1 := by
    rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
    exact Subtype.ext (Subgroup.mem_center_iff.mp ((twistHom hZ T) ⟨b, hbP⟩).2 _)
  have h1 : ⁅a, b⁆ * T * ⁅a, b⁆⁻¹ * T⁻¹ = 1 := congrArg Subtype.val htw
  have hcomm : ⁅a, b⁆ ∈ Subgroup.centralizer {T} := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    have h2 : ⁅a, b⁆ * T * ⁅a, b⁆⁻¹ = T := by
      rw [← mul_inv_eq_one]
      exact h1
    calc ⁅a, b⁆ * T = (⁅a, b⁆ * T * ⁅a, b⁆⁻¹) * ⁅a, b⁆ := by group
      _ = T * ⁅a, b⁆ := by rw [h2]
  refine ⟨⟨⁅a, b⁆, hcomm⟩, Subtype.ext ?_⟩
  rw [centralizerProj_apply, map_commutatorElement, ha, hb]
  rfl

end Twist

variable {K : Type} [Field K] {V : Type} [AddCommGroup V] [Module K V]
  {B : LinearMap.BilinForm K V}

@[expose] def spSigns (B : LinearMap.BilinForm K V) : Subgroup (sesqUnitaryGroup B) where
  carrier := {g | spOp g = 1 ∨ spOp g = -1}
  one_mem' := Or.inl rfl
  mul_mem' := by
    rintro g g' (hg | hg) (hg' | hg')
    · exact Or.inl (show spOp g * spOp g' = 1 by rw [hg, hg', one_mul])
    · exact Or.inr (show spOp g * spOp g' = -1 by rw [hg, hg', one_mul])
    · exact Or.inr (show spOp g * spOp g' = -1 by rw [hg, hg', mul_one])
    · exact Or.inl (show spOp g * spOp g' = 1 by rw [hg, hg', neg_mul_neg, one_mul])
  inv_mem' := by
    rintro g (hg | hg)
    · refine Or.inl ?_
      have h1 : (g : LinearMap.GeneralLinearGroup K V) = 1 := Units.ext hg
      change (((g : LinearMap.GeneralLinearGroup K V)⁻¹ : LinearMap.GeneralLinearGroup K V) :
        Module.End K V) = 1
      rw [h1, inv_one, Units.val_one]
    · refine Or.inr ?_
      have h1 : (g : LinearMap.GeneralLinearGroup K V) = -1 := Units.ext (by
        change spOp g = _
        rw [hg, Units.val_neg, Units.val_one])
      change (((g : LinearMap.GeneralLinearGroup K V)⁻¹ : LinearMap.GeneralLinearGroup K V) :
        Module.End K V) = -1
      rw [h1, inv_neg_one, Units.val_neg, Units.val_one]

theorem mem_spSigns {g : sesqUnitaryGroup B} : g ∈ spSigns B ↔ spOp g = 1 ∨ spOp g = -1 :=
  Iff.rfl

theorem spSigns_le_center (B : LinearMap.BilinForm K V) :
    spSigns B ≤ Subgroup.center (sesqUnitaryGroup B) := by
  rintro z hz
  rw [Subgroup.mem_center_iff]
  intro g
  apply Subtype.ext
  apply Units.ext
  change spOp g * spOp z = spOp z * spOp g
  rcases hz with hz | hz <;> rw [hz] <;> simp

instance spSigns_normal (B : LinearMap.BilinForm K V) : (spSigns B).Normal :=
  ⟨fun z hz g => by
    have h1 := Subgroup.mem_center_iff.mp (spSigns_le_center B hz) g
    rw [h1, mul_inv_cancel_right]
    exact hz⟩

theorem lift_involution (hBnd : B.Nondegenerate) [Nontrivial V] {T : sesqUnitaryGroup B}
    (hT : orderOf (QuotientGroup.mk' (spSigns B) T) = 2) :
    (∀ c : K, spOp T ≠ c • 1) ∧ (spOp T * spOp T = 1 ∨ spOp T * spOp T = -1) := by
  refine ⟨fun c hc => ?_, ?_⟩
  · obtain ⟨v, hv⟩ := exists_ne (0 : V)
    obtain ⟨w, hw⟩ : ∃ w, B v w ≠ 0 := by
      by_contra! h0
      exact hv (hBnd.1 v h0)
    have h1 := mem_sesqUnitaryGroup.mp T.2 v w
    change B (spOp T v) (spOp T w) = B v w at h1
    simp only [hc, LinearMap.smul_apply, Module.End.one_apply, map_smul, smul_eq_mul] at h1
    have hc2 : c * c = 1 := by
      have h3 : (c * c - 1) * B v w = 0 := by linear_combination h1
      exact sub_eq_zero.mp ((mul_eq_zero.mp h3).resolve_right hw)
    have hTZ : T ∈ spSigns B := by
      rcases mul_self_eq_one_iff.mp hc2 with rfl | rfl
      · exact Or.inl (by rw [hc, one_smul])
      · exact Or.inr (by rw [hc, neg_smul, one_smul])
    have h4 : QuotientGroup.mk' (spSigns B) T = 1 := (QuotientGroup.eq_one_iff T).mpr hTZ
    rw [h4, orderOf_one] at hT
    exact absurd hT (by norm_num)
  · have h1 : QuotientGroup.mk' (spSigns B) (T * T) = 1 := by
      rw [map_mul, ← pow_two, ← hT, pow_orderOf_eq_one]
    exact (QuotientGroup.eq_one_iff (T * T)).mp h1

theorem exists_summand_of_isComponent {ℓ f : ℕ} (hℓ : ℓ.Prime) (hℓ2 : ℓ ≠ 2) (hf : 1 ≤ f)
    (hK : Nat.card K = ℓ ^ f) [FiniteDimensional K V] {r : ℕ} (hr : 1 ≤ r)
    (hdim : finrank K V = 2 * r) (hB : B.IsAlt) (hBnd : B.Nondegenerate)
    {T : sesqUnitaryGroup B} (hTns : ∀ c : K, spOp T ≠ c • 1) (hTT : spOp T * spOp T = 1)
    {L : Subgroup (Subgroup.centralizer {T})} (hL : CFSG.IsComponent L) :
    eigenPlus 1 (spOp T) ≠ ⊥ ∧ eigenMinus 1 (spOp T) ≠ ⊥ ∧
      (∀ v ∈ eigenPlus 1 (spOp T), ∀ w ∈ eigenMinus 1 (spOp T), B v w = 0) ∧
      (B.domRestrict₁₂ (eigenPlus 1 (spOp T)) (eigenPlus 1 (spOp T))).Nondegenerate ∧
      (B.domRestrict₁₂ (eigenMinus 1 (spOp T)) (eigenMinus 1 (spOp T))).Nondegenerate ∧
      ∃ A W : Submodule K V,
        (A = eigenPlus 1 (spOp T) ∧ W = eigenMinus 1 (spOp T) ∨
          A = eigenMinus 1 (spOp T) ∧ W = eigenPlus 1 (spOp T)) ∧
        ((L.map (Subgroup.centralizer {T}).subtype : Subgroup (sesqUnitaryGroup B)) :
          Set (sesqUnitaryGroup B)) = symplecticSummandSet B A W ∧
        ∀ R : Subgroup (sesqUnitaryGroup B),
          R ≤ Subgroup.centralizer ((L.map (Subgroup.centralizer {T}).subtype :
            Subgroup (sesqUnitaryGroup B)) : Set (sesqUnitaryGroup B)) →
          ⁅R, R⁆ = R → ∀ g ∈ R, ∀ a ∈ A, spOp g a = a := by
  have : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; exact (pow_pos hℓ.pos f).ne')
  obtain ⟨-, hsq, -⟩ := odd_symplectic_scalar_square_centralizer_structure hℓ hℓ2 hf hK hr hdim
    hB hBnd (A := (T : LinearMap.GeneralLinearGroup K V)) hTns one_ne_zero
    (by rw [one_smul]; exact hTT) (μ := 1)
    (fun v w => by rw [one_mul]; exact mem_sesqUnitaryGroup.mp T.2 v w)
  obtain ⟨-, -, hpos, -⟩ := hsq 1 (one_pow 2)
  obtain ⟨-, -, -, -, -, e, he⟩ := hpos (div_one 1)
  rcases fst_eq_or_snd_eq_of_isComponent_prod
      (isComponent_map_of_isComponent ((centralizerSimEquiv T).trans e) hL) with h2 | h1
  · have hfix : ∀ x ∈ L, ∀ w ∈ eigenMinus 1 (spOp T), spOp (x : sesqUnitaryGroup B) w = w := by
      intro x hx w hw
      have h3 := h2 _ (Subgroup.mem_map_of_mem ((centralizerSimEquiv T).trans e).toMonoidHom hx)
      have h4 : ((((e (centralizerSimEquiv T x)).2 :
          LinearMap.GeneralLinearGroup K (eigenMinus 1 (spOp T))) :
            Module.End K (eigenMinus 1 (spOp T))) ⟨w, hw⟩ : V) =
          spOp (x : sesqUnitaryGroup B) w :=
        LinearMap.congr_fun (he (centralizerSimEquiv T x)).2 ⟨w, hw⟩
      rw [← h4]
      change ((((((centralizerSimEquiv T).trans e).toMonoidHom x).2 :
          LinearMap.GeneralLinearGroup K (eigenMinus 1 (spOp T))) :
            Module.End K (eigenMinus 1 (spOp T))) ⟨w, hw⟩ : V) = w
      rw [h3]
      rfl
    obtain ⟨hP, hM, horth, hndP, hndM, hset, hfixR⟩ :=
      split_case hℓ hℓ2 hf hK hr hdim hB hBnd hTns hTT (one_pow 2) hL hfix
    exact ⟨hP, hM, horth, hndP, hndM, _, _, Or.inl ⟨rfl, rfl⟩, hset, hfixR⟩
  · have hfix : ∀ x ∈ L, ∀ w ∈ eigenMinus (-1) (spOp T),
        spOp (x : sesqUnitaryGroup B) w = w := by
      intro x hx w hw
      rw [eigenMinus_neg] at hw
      have h3 := h1 _ (Subgroup.mem_map_of_mem ((centralizerSimEquiv T).trans e).toMonoidHom hx)
      have h4 : ((((e (centralizerSimEquiv T x)).1 :
          LinearMap.GeneralLinearGroup K (eigenPlus 1 (spOp T))) :
            Module.End K (eigenPlus 1 (spOp T))) ⟨w, hw⟩ : V) =
          spOp (x : sesqUnitaryGroup B) w :=
        LinearMap.congr_fun (he (centralizerSimEquiv T x)).1 ⟨w, hw⟩
      rw [← h4]
      change ((((((centralizerSimEquiv T).trans e).toMonoidHom x).1 :
          LinearMap.GeneralLinearGroup K (eigenPlus 1 (spOp T))) :
            Module.End K (eigenPlus 1 (spOp T))) ⟨w, hw⟩ : V) = w
      rw [h3]
      rfl
    obtain ⟨hP, hM, horth, hndP, hndM, hset, hfixR⟩ :=
      split_case hℓ hℓ2 hf hK hr hdim hB hBnd hTns hTT (by norm_num) hL hfix
    rw [eigenPlus_neg] at hP hndP hfixR
    rw [eigenMinus_neg] at hM hndM
    rw [eigenPlus_neg, eigenMinus_neg] at horth hset
    exact ⟨hM, hP, fun v hv w hw => by rw [← hB.neg_eq, horth w hw v hv, neg_zero], hndM, hndP,
      _, _, Or.inr ⟨rfl, rfl⟩, hset, hfixR⟩

theorem sq_eq_one_of_isComponent {ℓ f : ℕ} (hℓ : ℓ.Prime) (hℓ2 : ℓ ≠ 2) (hf : 1 ≤ f)
    (hK : Nat.card K = ℓ ^ f) [FiniteDimensional K V] {r : ℕ} (hr : 1 ≤ r)
    (hdim : finrank K V = 2 * r) (hB : B.IsAlt) (hBnd : B.Nondegenerate)
    {T : sesqUnitaryGroup B} (hTns : ∀ c : K, spOp T ≠ c • 1)
    (hTsq : spOp T * spOp T = 1 ∨ spOp T * spOp T = -1)
    {L : Subgroup (Subgroup.centralizer {T})} (hL : CFSG.IsComponent L)
    {R : Subgroup (sesqUnitaryGroup B)}
    (hR : R ≤ Subgroup.centralizer ((L.map (Subgroup.centralizer {T}).subtype :
      Subgroup (sesqUnitaryGroup B)) : Set (sesqUnitaryGroup B)))
    (hRp : ⁅R, R⁆ = R) (hR1 : R ≠ ⊥) : spOp T * spOp T = 1 := by
  rcases hTsq with h1 | h1
  · exact h1
  · exfalso
    have h1' : spOp T * spOp T = (-1 : K) • 1 := by rw [h1, neg_smul, one_smul]
    by_cases hsq : ∃ l : K, l ^ 2 = -1
    · obtain ⟨l, hl⟩ := hsq
      exact hR1 (paired_case hℓ hℓ2 hf hK hr hdim hB hBnd hTns h1' hl hL hR hRp)
    · push Not at hsq
      exact hR1 (unitary_case hℓ hℓ2 hf hK hr hdim hB hBnd hTns h1' hsq hL hR hRp)

theorem eq_one_of_mem_spSigns (h2 : (2 : K) ≠ 0) {g : sesqUnitaryGroup B} (hg : g ∈ spSigns B)
    {W : Submodule K V} (hW0 : W ≠ ⊥) (hfix : ∀ w ∈ W, spOp g w = w) : g = 1 := by
  rcases mem_spSigns.mp hg with h1 | h1
  · exact Subtype.ext (Units.ext h1)
  · exfalso
    obtain ⟨w, hwW, hw0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hW0
    have h3 := hfix w hwW
    rw [h1, LinearMap.neg_apply, Module.End.one_apply] at h3
    have h4 : (2 : K) • w = 0 := by
      rw [two_smul]
      nth_rewrite 1 [← h3]
      exact neg_add_cancel w
    exact hw0 ((smul_eq_zero.mp h4).resolve_left h2)

theorem odd_projective_symplectic_local_component_supported_on_eigenspace {p f : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hf : 1 ≤ f) (hK : Nat.card K = p ^ f) [FiniteDimensional K V]
    {r : ℕ} (hr : 1 ≤ r) (hdim : finrank K V = 2 * r) (hB : B.IsAlt) (hBnd : B.Nondegenerate)
    {u : sesqUnitaryGroup B ⧸ spSigns B} (hu : orderOf u = 2) {T : sesqUnitaryGroup B}
    (hTu : QuotientGroup.mk' (spSigns B) T = u)
    {B₀ : Subgroup (Subgroup.centralizer {u})} (hB₀ : CFSG.IsComponent B₀)
    {Q : Subgroup (sesqUnitaryGroup B ⧸ spSigns B)}
    (hQB : Q ≤ Subgroup.centralizer ((B₀.map (Subgroup.centralizer {u}).subtype :
      Subgroup (sesqUnitaryGroup B ⧸ spSigns B)) : Set (sesqUnitaryGroup B ⧸ spSigns B)))
    (hQ : Q ≠ ⊥) (hQp : ⁅Q, Q⁆ = Q) :
    spOp T * spOp T = 1 ∧
      LinearMap.ker (spOp T - 1) ≠ ⊥ ∧ LinearMap.ker (spOp T + 1) ≠ ⊥ ∧
      (∀ v ∈ LinearMap.ker (spOp T - 1), ∀ w ∈ LinearMap.ker (spOp T + 1), B v w = 0) ∧
      (B.domRestrict₁₂ (LinearMap.ker (spOp T - 1))
        (LinearMap.ker (spOp T - 1))).Nondegenerate ∧
      (B.domRestrict₁₂ (LinearMap.ker (spOp T + 1))
        (LinearMap.ker (spOp T + 1))).Nondegenerate ∧
      ∃ A W : Submodule K V,
        (A = LinearMap.ker (spOp T - 1) ∧ W = LinearMap.ker (spOp T + 1) ∨
          A = LinearMap.ker (spOp T + 1) ∧ W = LinearMap.ker (spOp T - 1)) ∧
        ((⁅(B₀.map (Subgroup.centralizer {u}).subtype).comap (QuotientGroup.mk' (spSigns B)),
          (B₀.map (Subgroup.centralizer {u}).subtype).comap (QuotientGroup.mk' (spSigns B))⁆ :
            Subgroup (sesqUnitaryGroup B)) : Set (sesqUnitaryGroup B)) =
          symplecticSummandSet B A W ∧
        (∃ e : (⁅(B₀.map (Subgroup.centralizer {u}).subtype).comap
            (QuotientGroup.mk' (spSigns B)),
          (B₀.map (Subgroup.centralizer {u}).subtype).comap (QuotientGroup.mk' (spSigns B))⁆ :
            Subgroup (sesqUnitaryGroup B)) ≃* B₀,
          ∀ g, ((e g : Subgroup.centralizer {u}) : sesqUnitaryGroup B ⧸ spSigns B) =
            QuotientGroup.mk' (spSigns B) (g : sesqUnitaryGroup B)) ∧
        ∀ g ∈ ⁅Q.comap (QuotientGroup.mk' (spSigns B)), Q.comap (QuotientGroup.mk' (spSigns B))⁆,
          ∀ a ∈ A, spOp g a = a := by
  subst hTu
  have : Nontrivial V := Module.nontrivial_of_finrank_pos (R := K) (by omega)
  have hchar : CharP K p := finite_field_prime_power_characteristic hp hf hK
  have hk : ringChar K ≠ 2 := by
    rw [ringChar.eq K p]
    exact hp2
  have h2 : (2 : K) ≠ 0 := Ring.two_ne_zero hk
  obtain ⟨hTns, hTsq⟩ := lift_involution hBnd hu
  obtain ⟨hLc, hLB, hPL, hQperf, -, hQhat, hQcent⟩ := lift_component (spSigns_le_center B)
    (commutator_le_range_centralizerProj (spSigns_le_center B) T) hB₀ hQB hQ hQp
  generalize ⁅B₀.comap (centralizerProj (spSigns B) T),
    B₀.comap (centralizerProj (spSigns B) T)⁆ = L at hLc hLB hPL hQcent
  have hTT := sq_eq_one_of_isComponent hp hp2 hf hK hr hdim hB hBnd hTns hTsq hLc hQcent hQperf
    hQhat
  obtain ⟨hP, hM, horth, hndP, hndM, A, W, hAW, hset, hfixR⟩ :=
    exists_summand_of_isComponent hp hp2 hf hK hr hdim hB hBnd hTns hTT hLc
  have hW0 : W ≠ ⊥ := by
    rcases hAW with ⟨-, rfl⟩ | ⟨-, rfl⟩
    exacts [hM, hP]
  obtain ⟨e, he⟩ := exists_mulEquiv_of_inf_eq_one hLB fun x hx hxZ => Subtype.ext
    (eq_one_of_mem_spSigns h2 hxZ hW0
      ((Set.ext_iff.mp hset _).mp (Subgroup.mem_map_of_mem _ hx)).1)
  have hPker : eigenPlus 1 (spOp T) = LinearMap.ker (spOp T - 1) := by
    rw [eigenPlus_eq_ker one_ne_zero, one_smul]
  have hMker : eigenMinus 1 (spOp T) = LinearMap.ker (spOp T + 1) := by
    rw [eigenMinus_eq_ker one_ne_zero, one_smul]
  rw [hPker, hMker] at hAW
  rw [hPker] at hP hndP
  rw [hMker] at hM hndM
  rw [hPker, hMker] at horth
  rw [← hPL] at hset
  exact ⟨hTT, hP, hM, horth, hndP, hndM, A, W, hAW, hset, hPL ▸ ⟨e, he⟩,
    fun g hg a ha => hfixR _ hQcent hQperf g hg a ha⟩

end CFSG.LocalAnalysis.ComponentInitial.ProjectiveSymplectic
