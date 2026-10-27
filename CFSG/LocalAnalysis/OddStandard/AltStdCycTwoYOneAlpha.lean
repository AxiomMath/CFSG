module

public import CFSG.LocalAnalysis.OddStandard.AltStdCycTwoYOneLocal
public import CFSG.LocalAnalysis.SeitzReduction.CentralizerComponents
public import CFSG.LocalAnalysis.OddStandard.AltStdSecLookupConsAlt

public section

namespace CFSG.OddStandard.AltStdCycTwo.YOne

open Subgroup Equiv Equiv.Perm AltStdSec CFSG.ComponentClassification

section Alpha

variable {X : Type} [Group X] [Finite X] {t : X} {D : Subgroup X} {Ω : Type} [Fintype Ω]
  [DecidableEq Ω]

theorem LocalDatum.alpha (h : LocalDatum t D Ω) (η : D ≃* alternatingGroup Ω) :
    D ≤ CFSG.layer X ∧ ∃ K : Subgroup X, CFSG.IsComponent K ∧ ⁅D, K⁆ ≠ ⊥ ∧
      D ≤ K ⊔ K.map (MulAut.conj t).toMonoidHom ∧
      (∀ M : Subgroup X, CFSG.IsComponent M →
        (⁅D, M⁆ ≠ ⊥ ↔ M = K ∨ M = K.map (MulAut.conj t).toMonoidHom)) ∧
      (K.map (MulAut.conj t).toMonoidHom = K →
        D ≤ K ∧ CFSG.IsComponent (D.subgroupOf (K ⊓ centralizer ({t} : Set X)))) ∧
      (K.map (MulAut.conj t).toMonoidHom ≠ K →
        ⁅K, K.map (MulAut.conj t).toMonoidHom⁆ = ⊥ ∧
          (D : Set X) = {g | ∃ k ∈ K, k * (t * k * t⁻¹) = g}) := by
  have hpp : CFSG.pPrimeCore 2 X = ⊥ := by
    rw [← ClassicalInvolution.QuaternionStructure.oddCore_eq_pPrimeCore_two]; exact h.core
  have ht2 : t ^ 2 = 1 := by rw [← h.order]; exact pow_orderOf_eq_one t
  obtain ⟨hDE, K, hK, hDK, hle, -, hiff, hKK, hKt⟩ :=
    SeitzReduction.exists_isComponent_orbit_of_isComponent_centralizer hpp ht2 h.le_cent
      (h.isComponent η)
  exact ⟨hDE, K, hK, hDK, hle, hiff, hKK, fun hne => ⟨(hKt hne).1, (hKt hne).2.2.1⟩⟩

end Alpha

section Qact

variable {X : Type} [Group X]

@[expose] noncomputable def qact (K : Subgroup X) :
    normalizer (K : Set X) →* MulAut (K ⧸ center K) :=
  (PerfectAutomorphisms.centerQuotientHom K).comp K.normalizerMonoidHom

theorem qact_mk (K : Subgroup X) (x : normalizer (K : Set X)) (k : K) :
    qact K x (k : K ⧸ center K) =
      ((K.normalizerMonoidHom x k : K) : K ⧸ center K) :=
  PerfectAutomorphisms.onCenterQuotient_apply_mk _ k

theorem qact_eq_one_iff {K : Subgroup X} [Group.IsPerfect K] (x : normalizer (K : Set X)) :
    qact K x = 1 ↔ (x : X) ∈ centralizer (K : Set X) := by
  constructor
  · intro h
    have h1 : K.normalizerMonoidHom x = 1 :=
      PerfectAutomorphisms.centerQuotientHom_injective K (by rw [map_one]; exact h)
    rw [mem_centralizer_iff]
    intro k hk
    have h2 := congrArg (fun φ : MulAut K => ((φ ⟨k, hk⟩ : K) : X)) h1
    simp only [normalizerMonoidHom_apply_apply_coe, MulAut.one_apply] at h2
    calc k * x = (x * k * (x : X)⁻¹) * x := by rw [h2]
      _ = x * k := by group
  · intro h
    have h1 : K.normalizerMonoidHom x = 1 := by
      ext k
      simp only [normalizerMonoidHom_apply_apply_coe, MulAut.one_apply]
      rw [← mem_centralizer_iff.1 h k k.2]
      group
    rw [qact, MonoidHom.comp_apply, h1, map_one]

theorem qact_of_mem (K : Subgroup X) (x : normalizer (K : Set X)) (hx : (x : X) ∈ K) :
    qact K x = MulAut.conj ((⟨x, hx⟩ : K) : K ⧸ center K) := by
  ext q
  obtain ⟨k, rfl⟩ := QuotientGroup.mk_surjective q
  rw [qact_mk, MulAut.conj_apply, ← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul,
    ← QuotientGroup.mk_mul]
  congr 1

end Qact

section Inner

variable {S : Type} [Group S]

theorem center_eq_bot_of_nonab [IsSimpleGroup S] (hS : ∃ a b : S, a * b ≠ b * a) : center S = ⊥ :=
  (CFSG.LocalCores.isQuasisimple_of_isSimpleGroup hS).2

theorem conj_injective_of_nonab [IsSimpleGroup S] (hS : ∃ a b : S, a * b ≠ b * a) :
    Function.Injective (MulAut.conj : S →* MulAut S) := by
  rw [injective_iff_map_eq_one]
  intro s hs
  have hc : s ∈ center S := by
    rw [mem_center_iff]
    intro g
    have h1 := congrArg (fun φ : MulAut S => φ g) hs
    simp only [MulAut.conj_apply, MulAut.one_apply] at h1
    calc g * s = (s * g * s⁻¹) * s := by rw [h1]
      _ = s * g := by group
  rw [center_eq_bot_of_nonab hS, mem_bot] at hc
  exact hc

theorem normal_range_conj : (MulAut.conj : S →* MulAut S).range.Normal := by
  refine ⟨fun w hw σ => ?_⟩
  obtain ⟨s, rfl⟩ := hw
  refine ⟨σ s, ?_⟩
  ext g
  simp [MulAut.conj_apply, MulAut.mul_apply]

theorem centralizer_range_conj [IsSimpleGroup S] (hS : ∃ a b : S, a * b ≠ b * a) :
    centralizer ((MulAut.conj : S →* MulAut S).range : Set (MulAut S)) = ⊥ := by
  rw [eq_bot_iff]
  intro σ hσ
  rw [mem_bot]
  ext s
  have h1 := mem_centralizer_iff.1 hσ (MulAut.conj s) ⟨s, rfl⟩
  have h2 : MulAut.conj (σ s) = MulAut.conj s := by
    ext g
    obtain ⟨g', rfl⟩ := σ.surjective g
    have := congrArg (fun φ : MulAut S => φ g') h1
    simp only [MulAut.mul_apply, MulAut.conj_apply] at this
    simp only [MulAut.conj_apply]
    rw [← map_inv, ← map_mul, ← map_mul]
    exact this.symm
  exact conj_injective_of_nonab hS h2

noncomputable def innEquiv [IsSimpleGroup S] (hS : ∃ a b : S, a * b ≠ b * a) :
    (MulAut.conj : S →* MulAut S).range ≃* S :=
  (MonoidHom.ofInjective (conj_injective_of_nonab hS)).symm

end Inner

section Ident

variable {X : Type} [Group X] [Finite X] {t : X} {D : Subgroup X} {Ω : Type} [Fintype Ω]
  [DecidableEq Ω]

omit [Finite X] in
theorem mem_normalizer_of_map_conj_eq {K : Subgroup X} {t : X}
    (h : K.map (MulAut.conj t).toMonoidHom = K) : t ∈ normalizer (K : Set X) := by
  rw [mem_normalizer_iff]
  intro k
  constructor
  · intro hk
    have : t * k * t⁻¹ ∈ K.map (MulAut.conj t).toMonoidHom :=
      ⟨k, hk, by simp [MulAut.conj_apply]⟩
    rwa [h] at this
  · intro hk
    rw [← h] at hk
    obtain ⟨k', hk', he⟩ := hk
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at he
    have hkk : k = k' := by
      have := congrArg (fun g => t⁻¹ * g * t) he
      simp only [mul_assoc, inv_mul_cancel_left] at this
      simpa using this.symm
    rw [hkk]
    exact hk'

theorem LocalDatum.qact_ne_one (h : LocalDatum t D Ω) (η : D ≃* alternatingGroup Ω)
    {K : Subgroup X} (hK : CFSG.IsComponent K) (ht : t ∈ normalizer (K : Set X)) (hDK : D ≤ K)
    (hne : K ≠ D) : qact K ⟨t, ht⟩ ≠ 1 := by
  have : Group.IsPerfect K := hK.1.1
  intro h1
  have htK : t ∈ centralizer (K : Set X) := (qact_eq_one_iff ⟨t, ht⟩).1 h1
  have hKt : K ≤ centralizer ({t} : Set X) := fun k hk =>
    mem_centralizer_singleton_iff.2 (mem_centralizer_iff.1 htK k hk)
  rcases CFSG.LocalCores.distinct_components_commute (h.isComponent η)
      (CFSG.LocalCores.component_overgroup hK hKt) with h2 | h2
  · apply hne
    have h3 := (Subgroup.subgroupOf_inj).1 h2
    rw [inf_eq_left.2 h.le_cent, inf_eq_left.2 hKt] at h3
    exact h3.symm
  · obtain ⟨a, b, hab⟩ := h.nonab η
    apply hab
    have hle : D.subgroupOf (centralizer ({t} : Set X)) ≤
        centralizer ((K.subgroupOf (centralizer ({t} : Set X)) : Subgroup _) : Set _) :=
      (Subgroup.commutator_eq_bot_iff_le_centralizer).1 h2
    have h4 := mem_centralizer_iff.1 (hle (show (⟨a, h.le_cent a.2⟩ :
      centralizer ({t} : Set X)) ∈ D.subgroupOf (centralizer ({t} : Set X)) from a.2))
      ⟨b, h.le_cent b.2⟩ (hDK b.2)
    exact Subtype.ext (congrArg Subtype.val h4).symm

theorem LocalDatum.qact_injOn (h : LocalDatum t D Ω) (η : D ≃* alternatingGroup Ω)
    {K : Subgroup X} [Group.IsPerfect K] (hDK : D ≤ K) :
    Function.Injective ((qact K).comp (D.subgroupOf (normalizer (K : Set X))).subtype) := by
  rw [injective_iff_map_eq_one]
  intro x hx
  have h1 : ((x : normalizer (K : Set X)) : X) ∈ centralizer (K : Set X) :=
    (qact_eq_one_iff _).1 hx
  have h2 : (⟨((x : normalizer (K : Set X)) : X), x.2⟩ : D) ∈ center D := by
    rw [mem_center_iff]
    intro d
    exact Subtype.ext (mem_centralizer_iff.1 h1 d (hDK d.2))
  rw [h.center_eq_bot η, mem_bot] at h2
  apply Subtype.ext
  apply Subtype.ext
  simpa using congrArg Subtype.val h2

theorem isSubnormal_qact_image {K : Subgroup X} [Group.IsPerfect K]
    (ht : t ∈ normalizer (K : Set X)) (hDK : D ≤ K) (hDt : D ≤ centralizer ({t} : Set X))
    (hDc : CFSG.IsComponent (D.subgroupOf (K ⊓ centralizer ({t} : Set X)))) :
    CFSG.Assembly.IsSubnormal ((D.subgroupOf (normalizer (K : Set X))).map (qact K))
      (centralizer ({qact K ⟨t, ht⟩} : Set (MulAut (K ⧸ center K)))) := by
  set N := normalizer (K : Set X)
  set A := MulAut (K ⧸ center K)
  set W : Subgroup A := (MulAut.conj : K ⧸ center K →* A).range with hW
  have : W.Normal := normal_range_conj
  set a : A := qact K ⟨t, ht⟩ with ha
  set Ct : Subgroup N := (K ⊓ centralizer ({t} : Set X)).subgroupOf N with hCt
  have hD1 : CFSG.Assembly.IsSubnormal (D.subgroupOf N) Ct := by
    have h1 : CFSG.Assembly.IsSubnormal D (K ⊓ centralizer ({t} : Set X)) :=
      (CFSG.Assembly.IsSubnormal.iff_subgroupOf (le_inf hDK hDt)).2 hDc.2
    exact h1.comap N.subtype
  set B₁ : Subgroup A := Ct.map (qact K) with hB₁
  set B₂ : Subgroup A := W ⊓ centralizer ({a} : Set A) with hB₂
  have hW_of : ∀ x : N, (x : X) ∈ K → qact K x ∈ W := fun x hx =>
    ⟨_, (qact_of_mem K x hx).symm⟩
  have hcomm_a : ∀ x : N, (x : X) * t = t * x → qact K x ∈ centralizer ({a} : Set A) := by
    intro x hx
    rw [mem_centralizer_singleton_iff, ha, ← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext hx
  have hB₁B₂ : B₁ ≤ B₂ := by
    rintro _ ⟨x, hx, rfl⟩
    exact ⟨hW_of x hx.1, hcomm_a x (mem_centralizer_singleton_iff.1 hx.2)⟩
  have hB₁n : (B₁.subgroupOf B₂).Normal := by
    refine ⟨fun b₁ hb₁ b₂ => ?_⟩
    obtain ⟨x, hx, hxe⟩ := hb₁
    obtain ⟨⟨q, hq⟩, hb₂a⟩ := b₂.2
    obtain ⟨j, rfl⟩ := QuotientGroup.mk_surjective q
    set j' : N := ⟨j, le_normalizer j.2⟩ with hj'
    have hj'q : qact K j' = (b₂ : A) := by rw [qact_of_mem K j' j.2]; exact hq
    have hjt : (t : X) * j * t⁻¹ * (j : X)⁻¹ ∈ centralizer (K : Set X) := by
      have hcomm : (b₂ : A) * qact K ⟨t, ht⟩ = qact K ⟨t, ht⟩ * b₂ :=
        mem_centralizer_singleton_iff.1 hb₂a
      have h1 : qact K (⟨t, ht⟩ * j' * ⟨t, ht⟩⁻¹ * j'⁻¹) = 1 := by
        rw [map_mul, map_mul, map_mul, map_inv, map_inv, hj'q, ← hcomm]
        group
      exact (qact_eq_one_iff _).1 h1
    have hmem : j' * x * j'⁻¹ ∈ Ct := by
      have hxK : (x : X) ∈ K := hx.1
      have hxt : (x : X) * t = t * x := mem_centralizer_singleton_iff.1 hx.2
      have hmemK : (j : X) * x * (j : X)⁻¹ ∈ K := K.mul_mem (K.mul_mem j.2 hxK) (K.inv_mem j.2)
      set c := (t : X) * j * t⁻¹ * (j : X)⁻¹ with hc
      have hcj : (t : X) * j * t⁻¹ = c * j := by rw [hc]; group
      have hc1 : (c : X) * ((j : X) * x * (j : X)⁻¹) = ((j : X) * x * (j : X)⁻¹) * c :=
        (mem_centralizer_iff.1 hjt _ hmemK).symm
      have hkey : (t : X) * ((j : X) * x * (j : X)⁻¹) * t⁻¹ = (j : X) * x * (j : X)⁻¹ := by
        calc (t : X) * ((j : X) * x * (j : X)⁻¹) * t⁻¹
            = ((t : X) * j * t⁻¹) * ((t : X) * x * t⁻¹) * ((t : X) * j * t⁻¹)⁻¹ := by group
          _ = (c * j) * x * (c * j)⁻¹ := by
              rw [hcj, show (t : X) * x * t⁻¹ = x by rw [← hxt]; group]
          _ = (c * ((j : X) * x * (j : X)⁻¹)) * c⁻¹ := by group
          _ = (j : X) * x * (j : X)⁻¹ := by rw [hc1]; group
      show ((j' * x * j'⁻¹ : N) : X) ∈ K ⊓ centralizer ({t} : Set X)
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      refine Subgroup.mem_inf.2 ⟨hmemK, mem_centralizer_singleton_iff.2 ?_⟩
      calc ((j : X) * x * (j : X)⁻¹) * t
          = ((t : X) * ((j : X) * x * (j : X)⁻¹) * t⁻¹) * t := by rw [hkey]
        _ = t * ((j : X) * x * (j : X)⁻¹) := by group
    have hxe' : qact K x = (b₁ : A) := hxe
    show (b₂ : A) * b₁ * (b₂ : A)⁻¹ ∈ B₁
    rw [← hj'q, ← hxe', ← map_inv, ← map_mul, ← map_mul]
    exact ⟨_, hmem, rfl⟩
  have hB₂n : (B₂.subgroupOf (centralizer ({a} : Set A))).Normal := by
    refine ⟨fun w hw y => ?_⟩
    have hw' : (w : A) ∈ W ⊓ centralizer ({a} : Set A) := hw
    show ((y * w * y⁻¹ : centralizer ({a} : Set A)) : A) ∈ W ⊓ centralizer ({a} : Set A)
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    exact Subgroup.mem_inf.2 ⟨(inferInstance : W.Normal).conj_mem _ (Subgroup.mem_inf.1 hw').1 _,
      Subgroup.mul_mem _ (Subgroup.mul_mem _ y.2 (Subgroup.mem_inf.1 hw').2)
        (Subgroup.inv_mem _ y.2)⟩
  exact (hD1.map (qact K)).trans (.step hB₁B₂ hB₁n (.step inf_le_right hB₂n (.refl _)))

theorem LocalDatum.exists_perm_action (h : LocalDatum t D Ω) (η : D ≃* alternatingGroup Ω)
    (hlook : AltLookupAt (Fintype.card Ω)) {K : Subgroup X} (hK : CFSG.IsComponent K)
    (ht : t ∈ normalizer (K : Set X)) (hDK : D ≤ K)
    (hDc : CFSG.IsComponent (D.subgroupOf (K ⊓ centralizer ({t} : Set X)))) (hne : K ≠ D) :
    ∃ N : ℕ, ∃ φ : normalizer (K : Set X) →* Perm (Fin N),
      (∀ x, φ x = 1 ↔ (x : X) ∈ centralizer (K : Set X)) ∧
      (∀ x : normalizer (K : Set X), (x : X) ∈ K → φ x ∈ alternatingGroup (Fin N)) ∧
      (∀ g ∈ alternatingGroup (Fin N), ∃ x : normalizer (K : Set X), (x : X) ∈ K ∧ φ x = g) ∧
      φ ⟨t, ht⟩ * φ ⟨t, ht⟩ = 1 ∧
      (∀ d (hd : d ∈ D), ∀ y, φ ⟨t, ht⟩ y ≠ y → φ ⟨d, le_normalizer (hDK hd)⟩ y = y) ∧
      Fintype.card {y // φ ⟨t, ht⟩ y = y} = Fintype.card Ω := by
  classical
  have : Group.IsPerfect K := hK.1.1
  have hsK : IsSimpleGroup (K ⧸ center K) := hK.1.2.1
  have hnabK : ∃ a b : K ⧸ center K, a * b ≠ b * a := hK.1.2.2
  have ht2 : t * t = 1 := by rw [← sq, ← h.order]; exact pow_orderOf_eq_one t
  set Nk := normalizer (K : Set X) with hNk
  set A := MulAut (K ⧸ center K)
  set W : Subgroup A := (MulAut.conj : K ⧸ center K →* A).range with hW
  have : W.Normal := normal_range_conj
  have hWs : IsSimpleGroup W := (innEquiv hnabK).isSimpleGroup
  have hWnab : ∃ x y : W, x * y ≠ y * x := by
    have ⟨a, b, hab⟩ := hnabK
    refine ⟨(innEquiv hnabK).symm a, (innEquiv hnabK).symm b, fun hc => hab ?_⟩
    have := congrArg (innEquiv hnabK) hc
    simpa using this
  have hCW : centralizer (W : Set A) = ⊥ := centralizer_range_conj hnabK
  have hcatW : CFSG.Blueprint.Catalog W :=
    CFSG.SectionRank.catalog_of_mulEquiv (innEquiv hnabK)
      (CFSG.SectionRank.catalog_of_isKGroupCat_of_surjective h.kgroup K
        (QuotientGroup.mk' (center K)) (QuotientGroup.mk'_surjective _))
  set a : A := qact K ⟨t, ht⟩ with ha
  have ha2 : a * a = 1 := by
    rw [ha, ← map_mul]
    have : (⟨t, ht⟩ * ⟨t, ht⟩ : Nk) = 1 := Subtype.ext ht2
    rw [this, map_one]
  have ha1 : a ≠ 1 := h.qact_ne_one η hK ht hDK hne
  have hao : orderOf a = 2 := by
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    exact orderOf_eq_prime (by rw [sq]; exact ha2) ha1
  set B : Subgroup A := (D.subgroupOf Nk).map (qact K) with hB
  have hBW : B ≤ W := by
    rintro _ ⟨x, hx, rfl⟩
    exact ⟨_, (qact_of_mem K x (hDK hx)).symm⟩
  have hinj := h.qact_injOn η (K := K) hDK
  have eBD : B ≃* D :=
    (MulEquiv.subgroupCongr (by rw [MonoidHom.range_comp, Subgroup.range_subtype])).symm.trans
      ((MonoidHom.ofInjective hinj).symm.trans (subgroupOfEquivOfLe (hDK.trans le_normalizer)))
  have hBq : CFSG.Assembly.IsQuasisimple B :=
    (CFSG.ComponentClassification.AssemblyBPredicates.isQuasisimple_iff_native B).2
      (CFSG.LocalCores.isQuasisimple_of_mulEquiv eBD.symm (h.isQuasisimple η))
  have hBsub := isSubnormal_qact_image ht hDK h.le_cent hDc
  have hBcomp : CFSG.Assembly.IsComponentOf B (centralizer ({a} : Set A)) :=
    ⟨hBsub.le, hBsub, hBq⟩
  have eB : B ≃* alternatingGroup (Fin (Fintype.card Ω)) :=
    eBD.trans (η.trans (Fintype.equivFin Ω).altCongrHom)
  obtain ⟨N, ⟨eW⟩⟩ := hlook A W hWs hWnab hCW hcatW a hao B hBW hBcomp ⟨eB⟩
  have h7 := h.card
  have hcardB : Nat.card B = (Fintype.card Ω).factorial / 2 := by
    have : Nontrivial (Fin (Fintype.card Ω)) := Fin.nontrivial_iff_two_le.2 (by omega)
    rw [Nat.card_congr eB.toEquiv, nat_card_alternatingGroup, Nat.card_eq_fintype_card,
      Fintype.card_fin]
  have h2520 : 2520 ≤ (Fintype.card Ω).factorial / 2 := by
    have h1 := Nat.factorial_le h7
    have h2 : Nat.factorial 7 = 5040 := by decide
    omega
  have hN7 : 7 ≤ N := by
    by_contra hlt
    push Not at hlt
    have h1 : Nat.card B ≤ Nat.card W := Subgroup.card_le_of_le hBW
    have h2 : Nat.card W ≤ N.factorial := by
      rw [Nat.card_congr eW.toEquiv]
      calc Nat.card (alternatingGroup (Fin N)) ≤ Nat.card (Perm (Fin N)) :=
            Subgroup.card_le_card_group _
        _ = N.factorial := by rw [Nat.card_perm, Nat.card_eq_fintype_card, Fintype.card_fin]
    have h3 : N.factorial ≤ Nat.factorial 6 := Nat.factorial_le (by omega)
    have h4 : Nat.factorial 6 = 720 := by decide
    omega
  obtain ⟨ι, hι, hιW⟩ := lookup_exists_perm_embedding W hCW (by omega) (by omega) eW
  set φ : Nk →* Perm (Fin N) := ι.comp (qact K) with hφ
  have hker : ∀ x, φ x = 1 ↔ (x : X) ∈ centralizer (K : Set X) := by
    intro x
    rw [← qact_eq_one_iff x]
    constructor
    · intro h1
      exact hι (by rw [map_one]; exact h1)
    · intro h1
      simp only [hφ, MonoidHom.comp_apply, h1, map_one]
  have hW_of : ∀ x : Nk, (x : X) ∈ K → qact K x ∈ W := fun x hx =>
    ⟨_, (qact_of_mem K x hx).symm⟩
  have halt : ∀ x : Nk, (x : X) ∈ K → φ x ∈ alternatingGroup (Fin N) := by
    intro x hx
    have := hιW ⟨qact K x, hW_of x hx⟩
    show ι (qact K x) ∈ alternatingGroup (Fin N)
    rw [show ι (qact K x) = ι ((⟨qact K x, hW_of x hx⟩ : W) : A) from rfl, this]
    exact (eW _).2
  have hsurj : ∀ g ∈ alternatingGroup (Fin N), ∃ x : Nk, (x : X) ∈ K ∧ φ x = g := by
    intro g hg
    obtain ⟨w, hw⟩ := lookup_exists_of_mem_alt eW ι hιW hg
    obtain ⟨q, hq⟩ := w.2
    obtain ⟨j, rfl⟩ := QuotientGroup.mk_surjective q
    refine ⟨⟨j, le_normalizer j.2⟩, j.2, ?_⟩
    show ι (qact K ⟨j, le_normalizer j.2⟩) = g
    rw [qact_of_mem K _ j.2, ← hw, ← hq]
  set τ := φ ⟨t, ht⟩ with hτ
  have hτa : τ = ι a := rfl
  have hτ2 : τ * τ = 1 := by rw [hτa, ← map_mul, ha2, map_one]
  set P : Subgroup (Perm (Fin N)) := B.map ι with hP
  have hPA : P ≤ alternatingGroup (Fin N) := by
    rintro _ ⟨b, hb, rfl⟩
    rw [show ι b = ι ((⟨b, hBW hb⟩ : W) : A) from rfl, hιW]
    exact (eW _).2
  have hPc : P ≤ centralizer ({τ} : Set (Perm (Fin N))) := by
    rintro _ ⟨b, hb, rfl⟩
    rw [mem_centralizer_singleton_iff, hτa, ← map_mul, ← map_mul,
      mem_centralizer_singleton_iff.1 (hBsub.le hb)]
  have hCWt : (W ⊓ centralizer ({a} : Set A)).map ι =
      alternatingGroup (Fin N) ⊓ centralizer ({τ} : Set (Perm (Fin N))) := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      refine ⟨?_, mem_centralizer_singleton_iff.2 ?_⟩
      · rw [show ι y = ι ((⟨y, hy.1⟩ : W) : A) from rfl, hιW]
        exact (eW _).2
      · rw [hτa, ← map_mul, ← map_mul, mem_centralizer_singleton_iff.1 hy.2]
    · rintro ⟨hx, hxc⟩
      obtain ⟨w, hw⟩ := lookup_exists_of_mem_alt eW ι hιW hx
      refine ⟨w, ⟨w.2, mem_centralizer_singleton_iff.2 ?_⟩, hw⟩
      apply hι
      rw [map_mul, map_mul, hw, ← hτa]
      exact mem_centralizer_singleton_iff.1 hxc
  have hPcomp : CFSG.IsComponent
      (P.subgroupOf (alternatingGroup (Fin N) ⊓ centralizer ({τ} : Set (Perm (Fin N))))) := by
    have h1 : CFSG.Assembly.IsComponentOf B (W ⊓ centralizer ({a} : Set A)) :=
      CFSG.LocalAnalysis.ComponentInitial.isComponentOf_of_le hBcomp (le_inf hBW hBsub.le)
        inf_le_right
    have h2 := (CFSG.LocalAnalysis.ComponentInitial.isComponentOf_map_iff hι).2 h1
    rw [hCWt] at h2
    exact (CFSG.LocalAnalysis.ComponentInitial.isComponentOf_iff_isComponent_subgroupOf
      (le_inf hPA hPc)).1 h2
  obtain ⟨hF5, hPfix, ⟨eP⟩⟩ := component_eq_alt_fixed hτ2 hPA hPc hPcomp
  refine ⟨N, φ, hker, halt, hsurj, hτ2, fun d hd y hy => ?_, ?_⟩
  · exact hPfix _ ⟨qact K ⟨d, le_normalizer (hDK hd)⟩, ⟨⟨d, _⟩, hd, rfl⟩, rfl⟩ y hy
  · have hcardP : Nat.card P = (Fintype.card Ω).factorial / 2 := by
      rw [hP, Subgroup.card_map_of_injective hι, hcardB]
    have hcardFix : Nat.card P = (Fintype.card {y // τ y = y}).factorial / 2 := by
      have : Nontrivial {y // τ y = y} := Fintype.one_lt_card_iff_nontrivial.1 (by omega)
      rw [Nat.card_congr eP.toEquiv, nat_card_alternatingGroup, Nat.card_eq_fintype_card]
    have h1 : (Fintype.card Ω).factorial / 2 = (Fintype.card {y // τ y = y}).factorial / 2 :=
      hcardP.symm.trans hcardFix
    have h2 : (Fintype.card Ω).factorial = (Fintype.card {y // τ y = y}).factorial :=
      (Nat.div_left_inj (Nat.dvd_factorial (by norm_num) (by omega))
        (Nat.dvd_factorial (by norm_num) (by omega))).1 h1
    exact ((Nat.factorial_inj (by omega)).1 h2).symm

omit [Finite X] in
theorem exists_sq_lift {K : Subgroup X} (hDK : D ≤ K) [Group.IsPerfect D] (ht2 : t * t = 1)
    (htK : t ∈ normalizer (K : Set X)) {j : X} (hj : j ∈ K)
    (hjt : j⁻¹ * (t * j * t⁻¹) ∈ centralizer (K : Set X))
    (hjD : ∀ d ∈ D, j * d * j⁻¹ * d⁻¹ ∈ centralizer (K : Set X)) :
    ∃ w ∈ K, w * t = t * w ∧ (∀ d ∈ D, w * d = d * w) ∧
      w * (j * j)⁻¹ ∈ centralizer (K : Set X) := by
  have hjd_mem : ∀ d ∈ D, j * d * j⁻¹ * d⁻¹ ∈ K := fun d hd =>
    K.mul_mem (K.mul_mem (K.mul_mem hj (hDK hd)) (K.inv_mem hj)) (K.inv_mem (hDK hd))
  let f : D →* center K :=
    { toFun := fun d => ⟨⟨j * d * j⁻¹ * (d : X)⁻¹, hjd_mem d d.2⟩,
        mem_center_iff.2 fun k => Subtype.ext (mem_centralizer_iff.1 (hjD d d.2) k k.2)⟩
      map_one' := by apply Subtype.ext; apply Subtype.ext; simp
      map_mul' := fun d₁ d₂ => by
        apply Subtype.ext; apply Subtype.ext
        simp only [Subgroup.coe_mul]
        have hc' : (d₁ : X)⁻¹ * (j * d₂ * j⁻¹ * (d₂ : X)⁻¹) =
            (j * d₂ * j⁻¹ * (d₂ : X)⁻¹) * (d₁ : X)⁻¹ :=
          mem_centralizer_iff.1 (hjD d₂ d₂.2) _ (K.inv_mem (hDK d₁.2))
        calc j * ((d₁ : X) * d₂) * j⁻¹ * ((d₁ : X) * d₂)⁻¹
            = j * d₁ * j⁻¹ * ((j * d₂ * j⁻¹ * (d₂ : X)⁻¹) * (d₁ : X)⁻¹) := by group
          _ = j * d₁ * j⁻¹ * ((d₁ : X)⁻¹ * (j * d₂ * j⁻¹ * (d₂ : X)⁻¹)) := by rw [hc']
          _ = j * d₁ * j⁻¹ * (d₁ : X)⁻¹ * (j * d₂ * j⁻¹ * (d₂ : X)⁻¹) := by group }
  have hf := PerfectAutomorphisms.hom_eq_one_of_commutative f
  have hjD' : ∀ d ∈ D, j * d = d * j := by
    intro d hd
    have h1 := congrArg (fun φ : D →* center K => ((φ ⟨d, hd⟩ : center K) : X)) hf
    simp only [f, MonoidHom.coe_mk, OneHom.coe_mk, MonoidHom.one_apply, OneMemClass.coe_one] at h1
    calc j * d = (j * d * j⁻¹ * d⁻¹) * d * j := by group
      _ = d * j := by rw [h1, one_mul]
  obtain ⟨c, hc⟩ : ∃ c, c = j⁻¹ * (t * j * t⁻¹) := ⟨_, rfl⟩
  rw [← hc] at hjt
  have hcK : c ∈ K := by
    rw [hc]
    exact K.mul_mem (K.inv_mem hj) ((mem_normalizer_iff.1 htK j).1 hj)
  have hcj : c * j = j * c := (mem_centralizer_iff.1 hjt j hj).symm
  have htj : t * j * t⁻¹ = j * c := by rw [hc]; group
  have htc : t * c * t⁻¹ = c⁻¹ := by
    calc t * c * t⁻¹ = (t * j * t⁻¹)⁻¹ * ((t * t) * j * (t * t)⁻¹) := by rw [hc]; group
      _ = (j * c)⁻¹ * j := by rw [htj, ht2]; group
      _ = c⁻¹ := by group
  refine ⟨j * j * c, K.mul_mem (K.mul_mem hj hj) hcK, ?_, fun d hd => ?_, ?_⟩
  · have h1 : t * (j * j * c) * t⁻¹ = j * j * c := by
      calc t * (j * j * c) * t⁻¹ = (t * j * t⁻¹) * (t * j * t⁻¹) * (t * c * t⁻¹) := by group
        _ = j * (c * j) * c * c⁻¹ := by rw [htj, htc]; group
        _ = j * j * c := by rw [hcj]; group
    calc j * j * c * t = (t * (j * j * c) * t⁻¹) * t := by rw [h1]
      _ = t * (j * j * c) := by group
  · have hcd : c * d = d * c := (mem_centralizer_iff.1 hjt d (hDK hd)).symm
    have h2 : j * j * d = d * j * j := by
      rw [mul_assoc, hjD' d hd, ← mul_assoc, hjD' d hd]
    calc j * j * c * d = j * j * (c * d) := by group
      _ = j * j * d * c := by rw [hcd]; group
      _ = d * j * j * c := by rw [h2]
      _ = d * (j * j * c) := by group
  · have : j * j * c * (j * j)⁻¹ = c := by
      calc j * j * c * (j * j)⁻¹ = j * (j * c) * j⁻¹ * j⁻¹ := by group
        _ = c := by rw [← hcj, ← mul_assoc, ← hcj]; group
    rw [this]
    exact hjt

omit [Finite X] in
theorem exists_odd_pow_eq {Y H : Type*} [Group Y] [Finite Y] [Monoid H] (f : Y →* H) {x : Y}
    {g : H} (hg : g ^ 3 = 1) (hfx : f x = g) :
    ∃ k : ℕ, Odd (orderOf (x ^ k)) ∧ f (x ^ k) = g := by
  obtain ⟨a, u, hu, hord⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos x).ne'
  refine ⟨4 ^ a, ?_, ?_⟩
  · refine Odd.of_dvd_nat hu (orderOf_dvd_of_pow_eq_one ?_)
    rw [← pow_mul, show 4 ^ a * u = 2 ^ a * u * 2 ^ a by
      rw [show (4 : ℕ) = 2 * 2 from rfl, mul_pow]; ring, pow_mul, ← hord, pow_orderOf_eq_one,
      one_pow]
  · rw [map_pow, hfx]
    have h1 : 4 ^ a % 3 = 1 := by
      rw [Nat.pow_mod]
      norm_num
    rw [← Nat.div_add_mod (4 ^ a) 3, h1, pow_succ, pow_mul, hg, one_pow, one_mul]

theorem LocalDatum.moved_card_le_four (h : LocalDatum t D Ω) (η : D ≃* alternatingGroup Ω)
    {K : Subgroup X} (ht : t ∈ normalizer (K : Set X)) (hDK : D ≤ K)
    {N : ℕ} {φ : normalizer (K : Set X) →* Perm (Fin N)}
    (hker : ∀ x, φ x = 1 ↔ (x : X) ∈ centralizer (K : Set X))
    (hsurj : ∀ g ∈ alternatingGroup (Fin N), ∃ x : normalizer (K : Set X), (x : X) ∈ K ∧ φ x = g)
    (hinv : φ ⟨t, ht⟩ * φ ⟨t, ht⟩ = 1)
    (hfix : ∀ d (hd : d ∈ D), ∀ y, φ ⟨t, ht⟩ y ≠ y → φ ⟨d, le_normalizer (hDK hd)⟩ y = y) :
    (moved (φ ⟨t, ht⟩)).card ≤ 4 := by
  have : Group.IsPerfect D := h.isPerfect η
  have ht2 : t * t = 1 := by rw [← sq, ← h.order]; exact pow_orderOf_eq_one t
  set τ := φ ⟨t, ht⟩ with hτ
  have hlift : ∀ g ∈ alternatingGroup (Fin N), g * τ = τ * g → (∀ y, τ y = y → g y = y) →
      ∃ w : normalizer (K : Set X), (w : X) ∈ centralizer ({t} : Set X) ⊓ centralizer (D : Set X) ∧
        φ w = g * g := by
    intro g hgA hgτ hgfix
    obtain ⟨x, hxK, hxg⟩ := hsurj g hgA
    have hjt : (x : X)⁻¹ * (t * x * t⁻¹) ∈ centralizer (K : Set X) := by
      have h1 : φ (x⁻¹ * (⟨t, ht⟩ * x * ⟨t, ht⟩⁻¹)) = 1 := by
        rw [map_mul, map_mul, map_mul, map_inv, map_inv, hxg, ← hτ, ← mul_assoc, ← mul_assoc,
          mul_assoc g⁻¹, ← hgτ]
        group
      exact (hker _).1 h1
    have hjD : ∀ d ∈ D, (x : X) * d * (x : X)⁻¹ * d⁻¹ ∈ centralizer (K : Set X) := by
      intro d hd
      set d' : normalizer (K : Set X) := ⟨d, le_normalizer (hDK hd)⟩
      have hcomm : g * φ d' = φ d' * g := by
        refine Perm.Disjoint.commute fun y => ?_
        by_cases hy : τ y = y
        · exact Or.inl (hgfix y hy)
        · exact Or.inr (hfix d hd y hy)
      have h1 : φ (x * d' * x⁻¹ * d'⁻¹) = 1 := by
        rw [map_mul, map_mul, map_mul, map_inv, map_inv, hxg, hcomm]
        group
      exact (hker _).1 h1
    obtain ⟨w, hwK, hwt, hwD, hwc⟩ := exists_sq_lift hDK ht2 ht hxK hjt hjD
    refine ⟨⟨w, le_normalizer hwK⟩, ⟨mem_centralizer_singleton_iff.2 hwt,
      mem_centralizer_iff.2 fun d hd => (hwD d hd).symm⟩, ?_⟩
    have h1 : φ (⟨w, le_normalizer hwK⟩ * (x * x)⁻¹) = 1 := (hker _).2 hwc
    rw [map_mul, map_inv, map_mul, hxg] at h1
    exact mul_inv_eq_one.1 h1
  by_contra hcard
  obtain ⟨ρ, ρ', hρA, hρ'A, hρτ, hρ'τ, hρfix, hρ'fix, hρ3, hρ'3, hord⟩ :=
    exists_three_pairs hinv (by omega)
  have hsq : ∀ r : Perm (Fin N), r ^ 3 = 1 → r * r * (r * r) = r := by
    intro r hr
    calc r * r * (r * r) = r ^ 3 * r := by simp only [pow_succ, pow_zero, one_mul, mul_assoc]
      _ = r := by rw [hr, one_mul]
  have hcomm2 : ∀ r : Perm (Fin N), r * τ = τ * r → r * r * τ = τ * (r * r) := by
    intro r hr
    rw [mul_assoc, hr, ← mul_assoc, hr, mul_assoc]
  obtain ⟨w₁, hw₁, hφ₁⟩ := hlift (ρ * ρ) (mul_mem hρA hρA) (hcomm2 ρ hρτ)
    (fun y hy => by rw [Perm.mul_apply, hρfix y hy, hρfix y hy])
  obtain ⟨w₂, hw₂, hφ₂⟩ := hlift (ρ' * ρ') (mul_mem hρ'A hρ'A) (hcomm2 ρ' hρ'τ)
    (fun y hy => by rw [Perm.mul_apply, hρ'fix y hy, hρ'fix y hy])
  rw [hsq ρ hρ3] at hφ₁
  rw [hsq ρ' hρ'3] at hφ₂
  obtain ⟨k₁, hk₁o, hk₁φ⟩ := exists_odd_pow_eq φ hρ3 hφ₁
  obtain ⟨k₂, hk₂o, hk₂φ⟩ := exists_odd_pow_eq φ hρ'3 hφ₂
  set v₁ := w₁ ^ k₁
  set v₂ := w₂ ^ k₂
  have hv₁ : (v₁ : X) ∈ centralizer ({t} : Set X) ⊓ centralizer (D : Set X) := by
    rw [Subgroup.coe_pow]; exact pow_mem hw₁ k₁
  have hv₂ : (v₂ : X) ∈ centralizer ({t} : Set X) ⊓ centralizer (D : Set X) := by
    rw [Subgroup.coe_pow]; exact pow_mem hw₂ k₂
  have hodd := h.lam _ (inv_mem hv₁) _ hv₂
    (by rw [orderOf_inv, Subgroup.orderOf_coe]; exact hk₁o)
    (by rw [Subgroup.orderOf_coe]; exact hk₂o)
  have hodd' : Odd (orderOf (v₁⁻¹ * v₂)) := by
    rw [← Subgroup.orderOf_coe]
    simpa using hodd
  have hdvd := orderOf_map_dvd φ (v₁⁻¹ * v₂)
  rw [map_mul, map_inv, hk₁φ, hk₂φ, hord] at hdvd
  exact absurd (Odd.of_dvd_nat hodd' hdvd) (by decide)

theorem LocalDatum.exists_beta (h : LocalDatum t D Ω) (η : D ≃* alternatingGroup Ω)
    {K : Subgroup X} (ht : t ∈ normalizer (K : Set X)) (hDK : D ≤ K)
    {N : ℕ} {φ : normalizer (K : Set X) →* Perm (Fin N)}
    (hker : ∀ x, φ x = 1 ↔ (x : X) ∈ centralizer (K : Set X))
    (halt : ∀ x : normalizer (K : Set X), (x : X) ∈ K → φ x ∈ alternatingGroup (Fin N))
    (hfix : ∀ d (hd : d ∈ D), ∀ y, φ ⟨t, ht⟩ y ≠ y → φ ⟨d, le_normalizer (hDK hd)⟩ y = y)
    (hcard : Fintype.card {y // φ ⟨t, ht⟩ y = y} = Fintype.card Ω) :
    ∃ β : Ω ≃ {y // φ ⟨t, ht⟩ y = y}, ∀ (d : D) (ω : Ω),
      φ ⟨d, le_normalizer (hDK d.2)⟩ (β ω : Fin N) =
        (β (((η d : alternatingGroup Ω) : Perm Ω) ω) : Fin N) := by
  classical
  set τ := φ ⟨t, ht⟩ with hτ
  have hdt : ∀ d : D, φ ⟨d, le_normalizer (hDK d.2)⟩ * τ = τ * φ ⟨d, le_normalizer (hDK d.2)⟩ := by
    intro d
    rw [hτ, ← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (mem_centralizer_singleton_iff.1 (h.le_cent d.2))
  have hpres : ∀ d : D, ∀ y, τ (φ ⟨d, le_normalizer (hDK d.2)⟩ y) =
      φ ⟨d, le_normalizer (hDK d.2)⟩ y ↔ τ y = y := by
    intro d y
    have := comm_apply_ne_iff (hdt d) y
    tauto
  let Ψ : D →* Perm {y // τ y = y} :=
    { toFun := fun d => (φ ⟨d, le_normalizer (hDK d.2)⟩).subtypePerm (hpres d)
      map_one' := by
        ext y
        simp only [Perm.subtypePerm_apply, Perm.coe_one, id_eq]
        have : (⟨((1 : D) : X), le_normalizer (hDK (1 : D).2)⟩ : normalizer (K : Set X)) = 1 :=
          rfl
        rw [this, map_one]
        rfl
      map_mul' := fun d₁ d₂ => by
        ext y
        simp only [Perm.subtypePerm_apply, Perm.coe_mul, Function.comp_apply]
        have : (⟨((d₁ * d₂ : D) : X), le_normalizer (hDK (d₁ * d₂).2)⟩ :
            normalizer (K : Set X)) =
            ⟨d₁, le_normalizer (hDK d₁.2)⟩ * ⟨d₂, le_normalizer (hDK d₂.2)⟩ := rfl
        rw [this, map_mul]
        rfl }
  have hΨ : ∀ (d : D) (y : {y // τ y = y}), ((Ψ d y : {y // τ y = y}) : Fin N) =
      φ ⟨d, le_normalizer (hDK d.2)⟩ y := fun _ _ => rfl
  have hsign : ∀ d : D, Ψ d ∈ alternatingGroup {y // τ y = y} := by
    intro d
    rw [Perm.mem_alternatingGroup]
    show Perm.sign ((φ ⟨d, le_normalizer (hDK d.2)⟩).subtypePerm (hpres d)) = 1
    rw [Perm.sign_subtypePerm _ _ (fun y hy => by
      by_contra hτy
      exact hy (hfix d d.2 y hτy))]
    exact Perm.mem_alternatingGroup.1 (halt _ (hDK d.2))
  let Φ : alternatingGroup Ω →* alternatingGroup {y // τ y = y} :=
    (Ψ.comp η.symm.toMonoidHom).codRestrict _ (fun g => hsign _)
  have hΦinj : Function.Injective Φ := by
    rw [injective_iff_map_eq_one]
    intro g hg
    set d := η.symm g with hd
    have h1 : Ψ d = 1 := congrArg Subtype.val hg
    have h2 : φ ⟨d, le_normalizer (hDK d.2)⟩ = 1 := by
      refine Equiv.ext fun y => ?_
      rw [Perm.one_apply]
      by_cases hy : τ y = y
      · have := congrArg (fun p : Perm {y // τ y = y} => ((p ⟨y, hy⟩ : {y // τ y = y}) : Fin N)) h1
        simpa [hΨ] using this
      · simpa using hfix d d.2 y hy
    have h3 : (d : X) ∈ centralizer (K : Set X) := (hker _).1 h2
    have h4 : d ∈ center D := by
      rw [mem_center_iff]
      intro d'
      exact Subtype.ext (mem_centralizer_iff.1 h3 d' (hDK d'.2))
    rw [h.center_eq_bot η, mem_bot] at h4
    rw [← η.apply_symm_apply g, ← hd, h4, map_one]
  have hcardA : Fintype.card (alternatingGroup Ω) =
      Fintype.card (alternatingGroup {y // τ y = y}) := by
    have e := (Fintype.equivOfCardEq hcard.symm).altCongrHom
    exact Fintype.card_congr e.toEquiv
  have hΦbij : Function.Bijective Φ :=
    (Fintype.bijective_iff_injective_and_card Φ).2 ⟨hΦinj, hcardA⟩
  obtain ⟨β, hβ⟩ := exists_equiv_of_mulEquiv_alternatingGroup (by have := h.card; omega)
    (by have := h.card; omega) hcard.symm (MulEquiv.ofBijective Φ hΦbij)
  refine ⟨β, fun d ω => ?_⟩
  have h1 := hβ (η d) ω
  have h2 : ((MulEquiv.ofBijective Φ hΦbij (η d) : alternatingGroup {y // τ y = y}) :
      Perm {y // τ y = y}) = Ψ d := by
    simp [Φ]
  rw [h2] at h1
  rw [← hΨ, h1]

structure AltIdent (K : Subgroup X) (t : X) (D : Subgroup X) (Ω : Type) [Fintype Ω]
    [DecidableEq Ω] (η : D ≃* alternatingGroup Ω) (N : ℕ)
    (φ : normalizer (K : Set X) →* Perm (Fin N)) :
    Prop where
  ht : t ∈ normalizer (K : Set X)
  hD : D ≤ K
  ker : ∀ x, φ x = 1 ↔ (x : X) ∈ centralizer (K : Set X)
  alt : ∀ x : normalizer (K : Set X), (x : X) ∈ K → φ x ∈ alternatingGroup (Fin N)
  inv : φ ⟨t, ht⟩ * φ ⟨t, ht⟩ = 1
  moved : (moved (φ ⟨t, ht⟩)).card ≤ 4
  bij : ∃ β : Ω ≃ {y // φ ⟨t, ht⟩ y = y}, ∀ d : D,
    φ ⟨d, le_normalizer (hD d.2)⟩ =
      Perm.ofSubtype (β.permCongr ((η d : alternatingGroup Ω) : Perm Ω))

theorem LocalDatum.altIdent (h : LocalDatum t D Ω) (η : D ≃* alternatingGroup Ω)
    (hlook : AltLookupAt (Fintype.card Ω)) {K : Subgroup X} (hK : CFSG.IsComponent K)
    (hKt : K.map (MulAut.conj t).toMonoidHom = K) (hDK : D ≤ K)
    (hDc : CFSG.IsComponent (D.subgroupOf (K ⊓ centralizer ({t} : Set X)))) (hne : K ≠ D) :
    ∃ N : ℕ, ∃ φ : normalizer (K : Set X) →* Perm (Fin N), AltIdent K t D Ω η N φ := by
  classical
  have ht := mem_normalizer_of_map_conj_eq hKt
  obtain ⟨N, φ, hker, halt, hsurj, hinv, hfix, hcard⟩ :=
    h.exists_perm_action η hlook hK ht hDK hDc hne
  obtain ⟨β, hβ⟩ := h.exists_beta η ht hDK hker halt hfix hcard
  refine ⟨N, φ, ht, hDK, hker, halt, hinv, h.moved_card_le_four η ht hDK hker hsurj hinv hfix,
    β, fun d => ?_⟩
  refine Equiv.ext fun y => ?_
  by_cases hy : φ ⟨t, ht⟩ y = y
  · rw [Perm.ofSubtype_apply_of_mem (p := fun x => φ ⟨t, ht⟩ x = x) _ hy,
      Equiv.permCongr_apply]
    have h1 := hβ d (β.symm ⟨y, hy⟩)
    rw [Equiv.apply_symm_apply] at h1
    exact h1
  · rw [Perm.ofSubtype_apply_of_not_mem (p := fun x => φ ⟨t, ht⟩ x = x) _ hy]
    exact hfix d d.2 y hy

end Ident

section Transport

variable {α Ω : Type*} [DecidableEq α] [DecidableEq Ω] {p : α → Prop} [DecidablePred p]

omit [DecidablePred p] in
theorem permCongr_swap (β : Ω ≃ Subtype p) (a b : Ω) :
    β.permCongr (swap a b) = swap (β a) (β b) := by
  ext y
  rw [Equiv.permCongr_apply, ← (β.injective).swap_apply, Equiv.apply_symm_apply]

theorem ofSubtype_permCongr_swap_mul_swap (β : Ω ≃ Subtype p) (a b c d : Ω) :
    Perm.ofSubtype (β.permCongr (swap a b * swap c d)) =
      swap (β a : α) (β b) * swap (β c : α) (β d) := by
  rw [Equiv.permCongr_mul, map_mul, permCongr_swap, permCongr_swap, Perm.ofSubtype_swap_eq,
    Perm.ofSubtype_swap_eq]

theorem ofSubtype_permCongr_cyc3 (β : Ω ≃ Subtype p) (a b c : Ω) :
    Perm.ofSubtype (β.permCongr (cyc3 a b c)) = cyc3 (β a : α) (β b) (β c) := by
  rw [cyc3, ofSubtype_permCongr_swap_mul_swap, cyc3]

end Transport

section Five

variable {X : Type} [Group X] [Finite X] {t : X} {D : Subgroup X} {Ω : Type} [Fintype Ω]
  [DecidableEq Ω]

omit [Finite X] in
theorem exists_pow_sq_eq {y : X} (hodd : Odd (orderOf y)) : ∃ k : ℕ, (y ^ 2) ^ k = y := by
  obtain ⟨m, hm⟩ := hodd
  refine ⟨m + 1, ?_⟩
  rw [← pow_mul, show 2 * (m + 1) = orderOf y + 1 by omega, pow_succ, pow_orderOf_eq_one,
    one_mul]

omit [Finite X] in
theorem map_conj_mul (a b : X) (K : Subgroup X) :
    K.map (MulAut.conj (a * b)).toMonoidHom =
      (K.map (MulAut.conj b).toMonoidHom).map (MulAut.conj a).toMonoidHom := by
  rw [Subgroup.map_map]
  congr 1
  ext x
  simp [MulAut.conj_apply, mul_assoc]

theorem normalizer_of_alpha (ht2 : t * t = 1) {K : Subgroup X} (hK : CFSG.IsComponent K)
    (hiff : ∀ M : Subgroup X, CFSG.IsComponent M →
      (⁅D, M⁆ ≠ ⊥ ↔ M = K ∨ M = K.map (MulAut.conj t).toMonoidHom))
    (hDK : ⁅D, K⁆ ≠ ⊥) {y : X} (hyt : y * t = t * y) (hyD : y ∈ centralizer (D : Set X))
    (hodd : Odd (orderOf y)) : y ∈ normalizer (K : Set X) := by
  have hD : D.map (MulAut.conj y).toMonoidHom = D := by
    ext x
    constructor
    · rintro ⟨d, hd, rfl⟩
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      rw [← mem_centralizer_iff.1 hyD d hd]
      simpa using hd
    · intro hx
      refine ⟨x, hx, ?_⟩
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      rw [← mem_centralizer_iff.1 hyD x hx]
      group
  have hcomp : CFSG.IsComponent (K.map (MulAut.conj y).toMonoidHom) :=
    CFSG.LocalCores.isComponent_map_mulEquiv (MulAut.conj y) hK
  have hcomm : ⁅D, K.map (MulAut.conj y).toMonoidHom⁆ ≠ ⊥ := by
    intro h0
    apply hDK
    have h1 : (⁅D, K⁆).map (MulAut.conj y).toMonoidHom = ⊥ := by
      rw [Subgroup.map_commutator, hD, h0]
    exact (Subgroup.map_eq_bot_iff_of_injective _ (MulAut.conj y).injective).1 h1
  have hnorm : ∀ g : X, K.map (MulAut.conj g).toMonoidHom = K → g ∈ normalizer (K : Set X) :=
    fun g hg => mem_normalizer_of_map_conj_eq hg
  rcases (hiff _ hcomp).1 hcomm with h1 | h1
  · exact hnorm y h1
  ·
    have hconj : K.map (MulAut.conj (y ^ 2)).toMonoidHom = K := by
      have hyt' : y * t = t * y := hyt
      rw [sq, map_conj_mul, h1, ← map_conj_mul, hyt', map_conj_mul, h1, ← map_conj_mul, ht2]
      rw [show (MulAut.conj (1 : X)).toMonoidHom = MonoidHom.id X by ext; simp, Subgroup.map_id]
    obtain ⟨k, hk⟩ := exists_pow_sq_eq hodd
    rw [← hk]
    exact pow_mem (hnorm _ hconj) k

theorem LocalDatum.le_centralizer_alpha (h : LocalDatum t D Ω) (η : D ≃* alternatingGroup Ω)
    (hlook : AltLookupAt (Fintype.card Ω)) {Y : Subgroup X} (hYodd : Odd (Nat.card Y))
    (hYt : Y ≤ centralizer ({t} : Set X)) (hYD : Y ≤ centralizer (D : Set X))
    {M : Subgroup X} (hM : CFSG.IsComponent M) (hMD : ⁅D, M⁆ ≠ ⊥) :
    Y ≤ centralizer (M : Set X) := by
  classical
  have ht2 : t * t = 1 := by rw [← sq, ← h.order]; exact pow_orderOf_eq_one t
  obtain ⟨-, K, hK, hDK, -, hiff, hKK, hKt⟩ := h.alpha η
  have : Group.IsPerfect K := hK.1.1
  have hyodd : ∀ y ∈ Y, Odd (orderOf y) := fun y hy => by
    have h1 := orderOf_dvd_natCard (⟨y, hy⟩ : Y)
    rw [Subgroup.orderOf_mk] at h1
    exact Odd.of_dvd_nat hYodd h1
  have hnormY : ∀ y ∈ Y, y ∈ normalizer (K : Set X) := fun y hy =>
    normalizer_of_alpha ht2 hK hiff hDK (mem_centralizer_singleton_iff.1 (hYt hy)) (hYD hy)
      (hyodd y hy)
  have hKt_of : Y ≤ centralizer (K : Set X) →
      Y ≤ centralizer ((K.map (MulAut.conj t).toMonoidHom : Subgroup X) : Set X) := by
    intro hYK y hy
    rw [mem_centralizer_iff]
    rintro _ ⟨k, hk, rfl⟩
    have hyt : y * t = t * y := mem_centralizer_singleton_iff.1 (hYt hy)
    have hyk : k * y = y * k := mem_centralizer_iff.1 (hYK hy) k hk
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    have hyt' : t⁻¹ * y = y * t⁻¹ := by
      rw [inv_mul_eq_iff_eq_mul, ← mul_assoc, ← hyt, mul_assoc, mul_inv_cancel, mul_one]
    calc t * k * t⁻¹ * y = t * k * (t⁻¹ * y) := by group
      _ = t * k * (y * t⁻¹) := by rw [hyt']
      _ = t * (k * y) * t⁻¹ := by group
      _ = t * (y * k) * t⁻¹ := by rw [hyk]
      _ = (t * y) * k * t⁻¹ := by group
      _ = (y * t) * k * t⁻¹ := by rw [hyt]
      _ = y * (t * k * t⁻¹) := by group
  suffices hYK : Y ≤ centralizer (K : Set X) by
    rcases (hiff M hM).1 hMD with rfl | rfl
    · exact hYK
    · exact hKt_of hYK
  by_cases hKK' : K.map (MulAut.conj t).toMonoidHom = K
  ·
    obtain ⟨hDK', hDc⟩ := hKK hKK'
    by_cases hKD : K = D
    · subst hKD
      exact hYD
    obtain ⟨N, φ, hI⟩ := h.altIdent η hlook hK hKK' hDK' hDc hKD
    obtain ⟨β, hβ⟩ := hI.bij
    intro y hy
    have hgodd : Odd (orderOf (φ ⟨y, hnormY y hy⟩)) := by
      refine Odd.of_dvd_nat (hyodd y hy) ?_
      have := orderOf_map_dvd φ ⟨y, hnormY y hy⟩
      rwa [Subgroup.orderOf_mk] at this
    have hgτ : φ ⟨y, hnormY y hy⟩ * φ ⟨t, hI.ht⟩ = φ ⟨t, hI.ht⟩ * φ ⟨y, hnormY y hy⟩ := by
      rw [← map_mul, ← map_mul]
      congr 1
      exact Subtype.ext (mem_centralizer_singleton_iff.1 (hYt hy))
    have hFix : 4 ≤ (Finset.univ.filter fun x : Fin N => φ ⟨t, hI.ht⟩ x = x).card := by
      have h1 : (Finset.univ.filter fun x : Fin N => φ ⟨t, hI.ht⟩ x = x).card =
          Fintype.card {x // φ ⟨t, hI.ht⟩ x = x} := (Fintype.card_subtype _).symm
      rw [h1, ← Fintype.card_congr β]
      have := h.card
      omega
    have hgfix : ∀ x, φ ⟨t, hI.ht⟩ x = x → φ ⟨y, hnormY y hy⟩ x = x := by
      have key := fixes_of_comm_cyc3 hFix (σ := φ ⟨y, hnormY y hy⟩)
        (fun x₁ hx₁ x₂ hx₂ x₃ hx₃ h12 h23 h13 => by
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx₁ hx₂ hx₃
          have e12 : β.symm ⟨x₁, hx₁⟩ ≠ β.symm ⟨x₂, hx₂⟩ := fun e => h12 (by
            have := congrArg (fun ω => (β ω : Fin N)) e
            simpa using this)
          have e23 : β.symm ⟨x₂, hx₂⟩ ≠ β.symm ⟨x₃, hx₃⟩ := fun e => h23 (by
            have := congrArg (fun ω => (β ω : Fin N)) e
            simpa using this)
          have hd := hβ (η.symm ⟨cyc3 (β.symm ⟨x₁, hx₁⟩) (β.symm ⟨x₂, hx₂⟩) (β.symm ⟨x₃, hx₃⟩),
            mem_alt_cyc3 e12 e23⟩)
          rw [MulEquiv.apply_symm_apply, ofSubtype_permCongr_cyc3] at hd
          simp only [Equiv.apply_symm_apply] at hd
          rw [← hd, ← map_mul, ← map_mul]
          congr 1
          exact Subtype.ext (mem_centralizer_iff.1 (hYD hy) _ (Subtype.coe_prop _)).symm)
      intro x hx
      exact key x (by simp [hx])
    have hg1 : φ ⟨y, hnormY y hy⟩ = 1 :=
      eq_one_of_comm_of_odd hI.inv hI.moved hgτ hgfix hgodd
    exact (hI.ker _).1 hg1
  ·
    obtain ⟨hcommK, hDset⟩ := hKt hKK'
    intro y hy
    have hyN := hnormY y hy
    have hyt : y * t = t * y := mem_centralizer_singleton_iff.1 (hYt hy)
    have hcen : ∀ k : K, k⁻¹ * (K.normalizerMonoidHom ⟨y, hyN⟩ k) ∈ center K := by
      intro k
      set k' : K := K.normalizerMonoidHom ⟨y, hyN⟩ k with hk'
      have hk'e : (k' : X) = y * k * y⁻¹ := rfl
      have hdk : (k : X) * (t * k * t⁻¹) ∈ D := by
        have : (k : X) * (t * k * t⁻¹) ∈ (D : Set X) := by rw [hDset]; exact ⟨k, k.2, rfl⟩
        exact this
      have hfix : y * ((k : X) * (t * k * t⁻¹)) * y⁻¹ = (k : X) * (t * k * t⁻¹) := by
        rw [← mem_centralizer_iff.1 (hYD hy) _ hdk]
        group
      have hconj : t * (y * k * y⁻¹) * t⁻¹ = y * (t * k * t⁻¹) * y⁻¹ := by
        calc t * (y * k * y⁻¹) * t⁻¹ = (t * y) * k * (t * y)⁻¹ := by group
          _ = (y * t) * k * (y * t)⁻¹ := by rw [hyt]
          _ = y * (t * k * t⁻¹) * y⁻¹ := by group
      have heq : (k' : X) * (t * k' * t⁻¹) = (k : X) * (t * k * t⁻¹) := by
        rw [hk'e, hconj, ← hfix]
        group
      have hmemKt : (k : X)⁻¹ * k' ∈ K.map (MulAut.conj t).toMonoidHom := by
        refine ⟨k * k'⁻¹, mul_mem k.2 (inv_mem k'.2), ?_⟩
        simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
        calc t * ((k : X) * (k' : X)⁻¹) * t⁻¹ = (t * k * t⁻¹) * (t * k' * t⁻¹)⁻¹ := by group
          _ = (k : X)⁻¹ * ((k : X) * (t * k * t⁻¹)) * (t * k' * t⁻¹)⁻¹ := by group
          _ = (k : X)⁻¹ * ((k' : X) * (t * k' * t⁻¹)) * (t * k' * t⁻¹)⁻¹ := by rw [heq]
          _ = (k : X)⁻¹ * k' := by group
      rw [mem_center_iff]
      intro k₀
      apply Subtype.ext
      have := mem_centralizer_iff.1 ((Subgroup.commutator_eq_bot_iff_le_centralizer.1 hcommK)
        k₀.2) _ hmemKt
      simpa using this.symm
    have hid := PerfectAutomorphisms.hom_eq_id_of_central_displacement
      (K.normalizerMonoidHom ⟨y, hyN⟩).toMonoidHom hcen
    rw [mem_centralizer_iff]
    intro k hk
    have h1 := congrArg (fun φ : K →* K => ((φ ⟨k, hk⟩ : K) : X)) hid
    simp only [MulEquiv.coe_toMonoidHom, MonoidHom.id_apply] at h1
    have h2 : y * k * y⁻¹ = k := h1
    calc k * y = (y * k * y⁻¹) * y := by rw [h2]
      _ = y * k := by group

end Five

end CFSG.OddStandard.AltStdCycTwo.YOne
