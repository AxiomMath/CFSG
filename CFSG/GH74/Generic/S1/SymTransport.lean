module

public import CFSG.GH74.Generic.S1.Props
public import CFSG.GH74.Generic.JMaxCongr

public section

namespace CFSG.GH74.Generic.S1

open CFSG CFSG.GH74 CFSG.GH74.L5U5 CFSG.Blueprint Subgroup CFSG.GH74.Generic

variable {G : Type} [Group G]

theorem map_centralizer_conj (x g : G) :
    (centralizer ({x} : Set G)).map (MulAut.conj g).toMonoidHom =
      centralizer ({g * x * g⁻¹} : Set G) := by
  ext z
  constructor
  · rintro ⟨w, hw, rfl⟩
    have hw' : w ∈ centralizer ({x} : Set G) := hw
    rw [mem_centralizer_singleton_iff] at hw'
    rw [mem_centralizer_singleton_iff]
    change g * w * g⁻¹ * (g * x * g⁻¹) = g * x * g⁻¹ * (g * w * g⁻¹)
    calc g * w * g⁻¹ * (g * x * g⁻¹) = g * (w * x) * g⁻¹ := by group
      _ = g * (x * w) * g⁻¹ := by rw [hw']
      _ = g * x * g⁻¹ * (g * w * g⁻¹) := by group
  · intro hz
    rw [mem_centralizer_singleton_iff] at hz
    refine ⟨g⁻¹ * z * g, ?_, by change g * (g⁻¹ * z * g) * g⁻¹ = z; group⟩
    show g⁻¹ * z * g ∈ centralizer ({x} : Set G)
    rw [mem_centralizer_singleton_iff]
    have h1 : z * (g * x * g⁻¹) = g * x * g⁻¹ * z := hz
    calc g⁻¹ * z * g * x = g⁻¹ * (z * (g * x * g⁻¹)) * g := by group
      _ = g⁻¹ * (g * x * g⁻¹ * z) * g := by rw [h1]
      _ = x * (g⁻¹ * z * g) := by group

@[expose] noncomputable def cenConj (x g : G) :
    ↥(centralizer ({x} : Set G)) ≃* ↥(centralizer ({g * x * g⁻¹} : Set G)) :=
  (MulEquiv.subgroupMap (MulAut.conj g) (centralizer ({x} : Set G))).trans
    (MulEquiv.subgroupCongr (map_centralizer_conj x g))

theorem cenConj_val (x g : G) (u : ↥(centralizer ({x} : Set G))) :
    ((cenConj x g u : ↥(centralizer ({g * x * g⁻¹} : Set G))) : G) = g * (u : G) * g⁻¹ := rfl

@[expose] noncomputable def barConj (x g : G) : CentralizerBar x ≃* CentralizerBar (g * x * g⁻¹) :=
  QuotientGroup.congr (pPrimeCore 2 ↥(centralizer ({x} : Set G)))
    (pPrimeCore 2 ↥(centralizer ({g * x * g⁻¹} : Set G))) (cenConj x g)
    (pPrimeCore_map_iso 2 (cenConj x g))

theorem barConj_mk (x g : G) (u : ↥(centralizer ({x} : Set G))) :
    barConj x g (QuotientGroup.mk u) = QuotientGroup.mk (cenConj x g u) := rfl

theorem barConj_barOf (x g : G) {u : G} (hu : u ∈ centralizer ({x} : Set G)) {u' : G}
    (hu' : u' ∈ centralizer ({g * x * g⁻¹} : Set G)) (h : u' = g * u * g⁻¹) :
    barConj x g (barOf hu) = barOf hu' := by
  subst h
  rfl

theorem barConj_xbar (x g : G) : barConj x g (xbar x) = xbar (g * x * g⁻¹) := rfl

theorem isJMax_conj {x : G} {K : Subgroup (CentralizerBar x)} (h : IsJMax x K) (g : G) :
    IsJMax (g * x * g⁻¹) (K.map (barConj x g).toMonoidHom) := by
  have e : ↥K ≃* ↥(K.map (barConj x g).toMonoidHom) :=
    K.equivMapOfInjective (barConj x g).toMonoidHom (barConj x g).injective
  obtain ⟨⟨hx, hc, hG2⟩, hmin⟩ := h
  refine ⟨⟨?_, CFSG.LocalCores.isComponent_map_mulEquiv (barConj x g) hc, inG2_of_mulEquiv e hG2⟩, ?_⟩
  · rw [← hx]
    exact orderOf_injective (MulAut.conj g).toMonoidHom (MulAut.conj g).injective x
  · intro y L hL
    obtain ⟨h1, h2⟩ := hmin y L hL
    rw [← d2_congr e]
    refine ⟨h1, fun hd => ?_⟩
    rw [← fRank_congr e]
    exact h2 hd

variable [Finite G]

theorem S1Setup.conj {x : G} {K : Subgroup (CentralizerBar x)} (h : S1Setup G x K) (g : G) :
    S1Setup G (g * x * g⁻¹) (K.map (barConj x g).toMonoidHom) := by
  refine ⟨h.simple, h.nonab, h.rank, h.gen4, h.kgh, h.sylow, h.layerNe, ?_, ?_, ?_, isJMax_conj h.jmax g, h.nothin⟩
  · rw [← h.inv]
    exact orderOf_injective (MulAut.conj g).toMonoidHom (MulAut.conj g).injective x
  · exact CFSG.LocalCores.isComponent_map_mulEquiv (barConj x g) h.comp
  · refine ⟨h.shape.1.of_mulEquiv (K.equivMapOfInjective (barConj x g).toMonoidHom
      (barConj x g).injective), ?_⟩
    rw [← barConj_xbar x g]
    exact Subgroup.mem_map_of_mem _ h.shape.2

theorem centralizer_map_mulEquiv {A B : Type*} [Group A] [Group B] (f : A ≃* B) (S : Subgroup A) :
    centralizer ((S.map f.toMonoidHom : Subgroup B) : Set B) =
      (centralizer (S : Set A)).map f.toMonoidHom := by
  ext y
  constructor
  · intro hy
    refine ⟨f.symm y, ?_, f.apply_symm_apply y⟩
    show f.symm y ∈ centralizer (S : Set A)
    rw [mem_centralizer_iff]
    intro s hs
    have h1 := mem_centralizer_iff.1 hy (f s) (Subgroup.mem_map_of_mem _ hs)
    apply f.injective
    rw [map_mul, map_mul, f.apply_symm_apply]
    exact h1
  · rintro ⟨w, hw, rfl⟩
    have hw' : w ∈ centralizer (S : Set A) := hw
    show f w ∈ centralizer ((S.map f.toMonoidHom : Subgroup B) : Set B)
    rw [mem_centralizer_iff]
    rintro _ ⟨s, hs, rfl⟩
    have h1 := mem_centralizer_iff.1 hw' s hs
    change f s * f w = f w * f s
    rw [← map_mul, ← map_mul, h1]

theorem layer_map_mulEquiv' {A B : Type} [Group A] [Group B] (f : A ≃* B) :
    (layer A).map f.toMonoidHom = layer B := by
  have hbij := (CFSG.LocalCores.component_isomorphism f).2
  change MulEquiv.mapSubgroup f (sSup {K : Subgroup A | IsComponent K}) = layer B
  rw [OrderIso.map_sSup, ← sSup_image]
  exact congrArg sSup hbij.image_eq

theorem S1Front.conj {x : G} {K : Subgroup (CentralizerBar x)} (h : S1Front G x K) (g : G) :
    S1Front G (g * x * g⁻¹) (K.map (barConj x g).toMonoidHom) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← h.layer_eq]
    exact (layer_map_mulEquiv' (barConj x g)).symm
  · rw [centralizer_map_mulEquiv, h.cent_eq, MonoidHom.map_zpowers]
    rfl
  · intro u hu hu2 hub hune hconj
    have hu0 : g⁻¹ * u * g ∈ centralizer ({x} : Set G) := by
      have h1 := hu
      rw [mem_centralizer_singleton_iff] at h1 ⊢
      calc g⁻¹ * u * g * x = g⁻¹ * (u * (g * x * g⁻¹)) * g := by group
        _ = g⁻¹ * (g * x * g⁻¹ * u) * g := by rw [h1]
        _ = x * (g⁻¹ * u * g) := by group
    have hbar : barConj x g (barOf hu0) = barOf hu := barConj_barOf x g hu0 hu (by group)
    refine h.b5 (g⁻¹ * u * g) hu0 ?_ ?_ ?_ ?_
    · calc g⁻¹ * u * g * (g⁻¹ * u * g) = g⁻¹ * (u * u) * g := by group
        _ = 1 := by rw [hu2]; group
    · have h1 : barOf hu ∈ K.map (barConj x g).toMonoidHom := hub
      rw [← hbar] at h1
      obtain ⟨k, hk, hk'⟩ := h1
      have h2 := (barConj x g).injective hk'
      rw [← h2]
      exact hk
    · intro heq
      apply hune
      rw [← hbar, heq, barConj_xbar]
    · have h1 : IsConj x (g * x * g⁻¹) := isConj_iff.2 ⟨g, rfl⟩
      have h2 : IsConj u (g⁻¹ * u * g) := isConj_iff.2 ⟨g⁻¹, by simp⟩
      exact (h1.trans hconj).trans h2
  · intro P hP
    have hT : ThreeModel ↥(K.map (barConj x g).toMonoidHom) → ThreeModel ↥K := fun hh =>
      ThreeModel.of_mulEquiv (K.equivMapOfInjective (barConj x g).toMonoidHom
        (barConj x g).injective).symm hh
    have h1 := goodSub_map (barConj x g).symm.toMonoidHom hP
    have h2 := h1.mono hT
    have h3 := h.good_le _ h2
    intro y hy
    have h4 : (barConj x g).symm y ∈ P.map (barConj x g).symm.toMonoidHom := ⟨y, hy, rfl⟩
    exact ⟨_, h3 h4, (barConj x g).apply_symm_apply y⟩

end CFSG.GH74.Generic.S1
