module

public import CFSG.LocalAnalysis.RankFourTheoremC.InvariantTwo.KFacts.Lemma213Coord
public import CFSG.Open.Defs

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.RankP

open CFSG CFSG.LocalCores Subgroup CFSG.LocalAnalysis.RankFourTheoremC.Lemma213
open scoped commutatorElement

@[expose] def GL83I66Two : Prop :=
  ∀ (K : Type) [Group K] [Finite K] (f : ℕ), f.Prime → 5 ≤ f → CFSG.Open.IsKGroup K →
    CFSG.IsQuasisimple K → ∀ (K' : Type) [Group K'] (φ : K →* K'), Function.Surjective φ →
      φ.ker = center K → ∀ z : K', orderOf z = f →
        (∃ S : Sylow f K', z ∈ (S : Subgroup K') ∧ ∀ s ∈ (S : Subgroup K'), z * s = s * z) →
          ∃ w : K, orderOf w = f ∧ φ w = z

theorem isoInvariant_isCatalogGroup' : CFSG.KCore.IsoInvariant (@CFSG.Open.IsCatalogGroup) := by
  intro X Y _ _ e h
  obtain ⟨i, ⟨f⟩⟩ := h
  exact ⟨i, ⟨e.trans f⟩⟩

theorem commutatorElement_central_mul_left {G : Type*} [Group G] {a : G} (ha : a ∈ center G)
    (x y : G) : ⁅a * x, y⁆ = ⁅x, y⁆ := by
  have h1 : a * (x * y * x⁻¹) = (x * y * x⁻¹) * a := (Subgroup.mem_center_iff.mp ha _).symm
  have h2 : a * (x * y * x⁻¹) * a⁻¹ = x * y * x⁻¹ := mul_inv_eq_iff_eq_mul.mpr h1
  calc ⁅a * x, y⁆ = (a * (x * y * x⁻¹) * a⁻¹) * y⁻¹ := by
        rw [commutatorElement_def]
        group
    _ = ⁅x, y⁆ := by rw [h2]; rfl

theorem commutatorElement_central_mul_right {G : Type*} [Group G] {a : G} (ha : a ∈ center G)
    (x y : G) : ⁅x, a * y⁆ = ⁅x, y⁆ := by
  have h1 : a * (x * y * x⁻¹ * y⁻¹) = (x * y * x⁻¹ * y⁻¹) * a :=
    (Subgroup.mem_center_iff.mp ha _).symm
  have h2 : a * (x * y * x⁻¹ * y⁻¹) * a⁻¹ = x * y * x⁻¹ * y⁻¹ := mul_inv_eq_iff_eq_mul.mpr h1
  have h3 : x * a = a * x := (Subgroup.mem_center_iff.mp ha x)
  calc ⁅x, a * y⁆ = x * a * y * x⁻¹ * (y⁻¹ * a⁻¹) := by
        simp only [commutatorElement_def, mul_inv_rev, mul_assoc]
    _ = a * (x * y * x⁻¹ * y⁻¹) * a⁻¹ := by rw [h3]; group
    _ = ⁅x, y⁆ := by rw [h2]; rfl

theorem center_eq_bot_of_quasisimple_simple {C : Type*} [Group C] (hq : CFSG.IsQuasisimple C)
    (hs : IsSimpleGroup C) : center C = ⊥ := by
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (center C) with h | h
  · exact h
  · exfalso
    haveI : IsSimpleGroup (C ⧸ center C) := hq.2.1
    have hsub : Subsingleton (C ⧸ center C) := QuotientGroup.subsingleton_iff.mpr h
    exact not_subsingleton _ hsub

theorem lift_component (hI : GL83I66Two) {f : ℕ} (hf : f.Prime) (hf5 : 5 ≤ f)
    {Γ V : Type} [Group Γ] [Finite Γ] [Group V] (hΓ : CFSG.Open.IsKGroup Γ) (φ : Γ →* V)
    (hker : φ.ker ≤ center Γ) (C : Subgroup V) (hCq : CFSG.IsQuasisimple C)
    (hCs : IsSimpleGroup C) (hCφ : C ≤ φ.range) :
    ∃ K : Subgroup Γ, ⁅K, K⁆ = K ∧ K.map φ = C ∧
      ∀ (z : V) (hz : z ∈ C), orderOf z = f →
        (∃ S : Sylow f C, (⟨z, hz⟩ : C) ∈ (S : Subgroup C) ∧
          ∀ s ∈ (S : Subgroup C), (⟨z, hz⟩ : C) * s = s * (⟨z, hz⟩ : C)) →
        ∃ w ∈ K, orderOf w = f ∧ φ w = z := by
  set M : Subgroup Γ := C.comap φ with hM
  set K : Subgroup Γ := ⁅M, M⁆ with hK
  have hMmap : M.map φ = C := Subgroup.map_comap_eq_self hCφ
  have hCperf : ⁅C, C⁆ = C := Subgroup.isPerfect_iff.mp hCq.1
  have hKmap : K.map φ = C := by
    rw [hK, Subgroup.map_commutator, hMmap, hCperf]
  have hMsup : ∀ m ∈ M, ∃ k ∈ K, m * k⁻¹ ∈ φ.ker := by
    intro m hm
    have : φ m ∈ K.map φ := by
      rw [hKmap]
      exact hm
    obtain ⟨k, hk, hkm⟩ := Subgroup.mem_map.mp this
    exact ⟨k, hk, by rw [MonoidHom.mem_ker, map_mul, map_inv, hkm, mul_inv_cancel]⟩
  have hKperf : ⁅K, K⁆ = K := by
    apply le_antisymm
    · exact Subgroup.commutator_le.mpr fun a ha b hb =>
        K.mul_mem (K.mul_mem (K.mul_mem ha hb) (K.inv_mem ha)) (K.inv_mem hb)
    · refine Subgroup.commutator_le.mpr fun m₁ hm₁ m₂ hm₂ => ?_
      obtain ⟨k₁, hk₁, hmk₁⟩ := hMsup m₁ hm₁
      obtain ⟨k₂, hk₂, hmk₂⟩ := hMsup m₂ hm₂
      have e₁ : m₁ = (m₁ * k₁⁻¹) * k₁ := by group
      have e₂ : m₂ = (m₂ * k₂⁻¹) * k₂ := by group
      rw [e₁, e₂, commutatorElement_central_mul_left (hker hmk₁),
        commutatorElement_central_mul_right (hker hmk₂)]
      exact Subgroup.commutator_mem_commutator hk₁ hk₂
  have hKφ : ∀ k : K, φ k ∈ C := fun k => by
    have := Subgroup.mem_map_of_mem φ k.2
    rwa [hKmap] at this
  let φK : K →* C := (φ.comp K.subtype).codRestrict C hKφ
  have hφK : ∀ k : K, ((φK k : C) : V) = φ k := fun k => rfl
  have hsurj : Function.Surjective φK := by
    intro c
    have : (c : V) ∈ K.map φ := by rw [hKmap]; exact c.2
    obtain ⟨k, hk, hkc⟩ := Subgroup.mem_map.mp this
    exact ⟨⟨k, hk⟩, Subtype.ext hkc⟩
  have hCbot : center C = ⊥ := center_eq_bot_of_quasisimple_simple hCq hCs
  have hkerK : φK.ker = center K := by
    apply le_antisymm
    · intro k hk
      rw [Subgroup.mem_center_iff]
      intro g
      have hk1 : (k : Γ) ∈ φ.ker := by
        rw [MonoidHom.mem_ker]
        have := congrArg Subtype.val (MonoidHom.mem_ker.mp hk)
        rw [hφK] at this
        exact this
      have := Subgroup.mem_center_iff.mp (hker hk1) (g : Γ)
      exact Subtype.ext this
    · intro z hz
      have hzc : φK z ∈ center C := by
        rw [Subgroup.mem_center_iff]
        intro c
        obtain ⟨k, rfl⟩ := hsurj c
        rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.mp hz k]
      rw [hCbot, Subgroup.mem_bot] at hzc
      exact hzc
  have hKq : CFSG.IsQuasisimple K :=
    (isQuasisimple_iff_of_surjective (Subgroup.isPerfect_iff.mpr hKperf) φK hsurj
      (le_of_eq hkerK)).mpr hCq
  have hKgrp : CFSG.Open.IsKGroup K :=
    CFSG.KCore.KGroupNonab.subgroup isoInvariant_isCatalogGroup' hΓ K
  refine ⟨K, hKperf, hKmap, fun z hz hord hcen => ?_⟩
  obtain ⟨w, hw, hwz⟩ := hI K f hf hf5 hKgrp hKq C φK hsurj hkerK ⟨z, hz⟩
    (by rw [orderOf_mk]; exact hord) hcen
  refine ⟨(w : Γ), w.2, ?_, ?_⟩
  · rw [Subgroup.orderOf_coe]
    exact hw
  · have := congrArg Subtype.val hwz
    exact this

theorem lift_layer (hI : GL83I66Two) {f : ℕ} (hf : f.Prime) (hf5 : 5 ≤ f)
    {Γ V : Type} [Group Γ] [Finite Γ] [Group V] [Finite V] (hΓ : CFSG.Open.IsKGroup Γ)
    (φ : Γ →* V) (hker : φ.ker ≤ center Γ) (hC : ∀ C : ComponentIndex V, IsSimpleGroup C.1)
    (hZ : ∀ C : ComponentIndex V, center C.1 = ⊥) (hΛ : layer V ≤ φ.range) {z : V}
    (hzΛ : z ∈ layer V) (hzf : z ^ f = 1)
    (hcen : ∀ C : ComponentIndex V, ∃ S : Sylow f C.1,
      coord hZ C ⟨z, hzΛ⟩ ∈ (S : Subgroup C.1) ∧
        ∀ s ∈ (S : Subgroup C.1), coord hZ C ⟨z, hzΛ⟩ * s = s * coord hZ C ⟨z, hzΛ⟩) :
    ∃ w : Γ, w ^ f = 1 ∧ φ w = z := by
  classical
  haveI := Fact.mk hf
  choose K hKperf hKmap hKlift using fun C : ComponentIndex V =>
    lift_component hI hf hf5 hΓ φ hker C.1 C.2.1 (hC C) ((component_le_layer C.2).trans hΛ)
  have hw : ∀ C : ComponentIndex V, ∃ w ∈ K C, w ^ f = 1 ∧
      φ w = ((coord hZ C ⟨z, hzΛ⟩ : C.1) : V) := by
    intro C
    by_cases h1 : coord hZ C ⟨z, hzΛ⟩ = 1
    · refine ⟨1, Subgroup.one_mem _, one_pow f, ?_⟩
      rw [h1]
      simp
    · have hpow : (coord hZ C ⟨z, hzΛ⟩) ^ f = 1 := by
        rw [← map_pow]
        have : (⟨z, hzΛ⟩ : layer V) ^ f = 1 := Subtype.ext (by simpa using hzf)
        rw [this, map_one]
      have hord : orderOf (coord hZ C ⟨z, hzΛ⟩) = f := orderOf_eq_prime hpow h1
      have hordV : orderOf (((coord hZ C ⟨z, hzΛ⟩ : C.1) : V)) = f := by
        rw [Subgroup.orderOf_coe]
        exact hord
      obtain ⟨w, hwK, hwo, hwφ⟩ := hKlift C _ (coord hZ C ⟨z, hzΛ⟩).2 hordV (hcen C)
      refine ⟨w, hwK, ?_, hwφ⟩
      have := pow_orderOf_eq_one w
      rwa [hwo] at this
  choose w hwK hwf hwφ using hw
  have hcomm : Pairwise fun C D : ComponentIndex V =>
      ∀ x y : Γ, x ∈ K C → y ∈ K D → Commute x y := by
    intro C D hCD x y hx hy
    have hKK : ⁅K C, K D⁆ = ⊥ := by
      have hcentral : ⁅K C, K D⁆ ≤ center Γ := by
        refine Subgroup.commutator_le.mpr fun k hk l hl => hker ?_
        rw [MonoidHom.mem_ker, map_commutatorElement]
        have hkC : φ k ∈ C.1 := by
          have := Subgroup.mem_map_of_mem φ hk
          rwa [hKmap C] at this
        have hlD : φ l ∈ D.1 := by
          have := Subgroup.mem_map_of_mem φ hl
          rwa [hKmap D] at this
        exact commutatorElement_eq_one_iff_mul_comm.mpr (componentIndex_commute hCD _ _ hkC hlD)
      have hdouble : ⁅⁅K C, K D⁆, K C⁆ = ⊥ :=
        le_bot_iff.mp ((Subgroup.commutator_mono hcentral le_rfl).trans
          (Subgroup.commutator_center_left _).le)
      exact perfect_double_commutator (Subgroup.isPerfect_iff.mpr (hKperf C)) hdouble
    have := Subgroup.commutator_mem_commutator hx hy
    rw [hKK, Subgroup.mem_bot] at this
    exact commutatorElement_eq_one_iff_mul_comm.mp this
  let W : (∀ C : ComponentIndex V, K C) →* Γ :=
    MonoidHom.noncommPiCoprod (fun C => (K C).subtype)
      (fun C D hCD x y => hcomm hCD x y x.2 y.2)
  let x₀ : ∀ C : ComponentIndex V, K C := fun C => ⟨w C, hwK C⟩
  refine ⟨W x₀, ?_, ?_⟩
  · rw [← map_pow]
    have : x₀ ^ f = 1 := funext fun C => Subtype.ext (hwf C)
    rw [this, map_one]
  · have hcommw : (↑(Finset.univ : Finset (ComponentIndex V)) : Set (ComponentIndex V)).Pairwise
        fun C D => Commute (w C) (w D) :=
      fun C _ D _ hCD => hcomm hCD _ _ (hwK C) (hwK D)
    have h1 : W x₀ = Finset.univ.noncommProd (fun C => w C) hcommw :=
      MonoidHom.noncommPiCoprod_apply _ x₀
    have h3 := Finset.map_noncommProd Finset.univ (fun C => w C) hcommw φ
    set y₀ : ∀ C : ComponentIndex V, C.1 := (layerEquiv hZ).symm ⟨z, hzΛ⟩ with hy₀
    have h2 : layerMul V y₀ = z := congrArg Subtype.val ((layerEquiv hZ).apply_symm_apply ⟨z, hzΛ⟩)
    rw [h1, h3, ← h2, layerMul_apply]
    exact Finset.noncommProd_congr rfl (fun C _ => hwφ C) _

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.RankP
