module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.S2Basic
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.AppCStd
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.Inputs25

public section

namespace CFSG.QuasithinUnique.A5.S2

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.QuasithinUnique.DoubleA3
  CFSG.QuasithinUnique.A5.Delta5 CFSG.QuasithinUnique.AppC Equiv
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {T M H S L : Subgroup G}

namespace Data

variable {t : G} (h : Data T M H S L t)
include h

theorem S_le_M : S ≤ M := fun _ hx => (h.cs.sylow_inf.1 hx).2

theorem S_le_H : S ≤ H := fun _ hx => h.cs.sylow.1 hx

theorem cj_M {x : G} (hx : x ∈ S) : cj x M = M :=
  mem_normalizer_iff_cj.1 (Subgroup.le_normalizer (h.S_le_M hx))

theorem conjJoin_L₂ : conjJoin S (cj t L) = conjJoin S L := by
  apply le_antisymm
  · refine iSup_le fun s => ?_
    have : (cj t L).map (MulAut.conj (s : G)).toMonoidHom = cj ((s : G) * t) L := cj_cj _ _ L
    show cj (s : G) (cj t L) ≤ _
    rw [cj_cj]
    exact le_iSup (fun s' : S => L.map (MulAut.conj (s' : G)).toMonoidHom)
      ⟨(s : G) * t, S.mul_mem s.2 h.t_mem⟩
  · refine iSup_le fun s => ?_
    have e : cj (s : G) L = cj ((s : G) * t⁻¹) (cj t L) := by rw [cj_cj]; simp
    show cj (s : G) L ≤ _
    rw [e]
    exact le_iSup (fun s' : S => (cj t L).map (MulAut.conj (s' : G)).toMonoidHom)
      ⟨(s : G) * t⁻¹, S.mul_mem s.2 (S.inv_mem h.t_mem)⟩

omit [Finite G] h in
theorem cj_comm (t : G) (X Y : Subgroup G) : ⁅cj t X, cj t Y⁆ = cj t ⁅X, Y⁆ :=
  (Subgroup.map_commutator _ _ _).symm

omit [Finite G] h in
theorem cj_thompsonJ {x : G} (hx : x ∈ S) : cj x (thompsonJ S) = thompsonJ S :=
  mem_normalizer_iff_cj.1 (GammaExtra.normalizer_le_normalizer_thompsonJ S
    (Subgroup.le_normalizer hx))

theorem cs₂ : ConstrainedSetting G T M H S (cj t L) where
  setting := h.cs.setting
  notBender := h.cs.notBender
  notSmall := h.cs.notSmall
  gamma0 := h.cs.gamma0
  charTwo := h.cs.charTwo
  sylow := h.cs.sylow
  sylow_inf := h.cs.sylow_inf
  le_T := h.cs.le_T
  center_le := h.cs.center_le
  ne_T := h.cs.ne_T
  witness := h.cs.witness
  block := ⟨CFSG.Quasithin.IsBlock2.conjByElt_of_mem h.cs.block.1 (h.S_le_H h.t_mem),
    Or.inr (Or.inr h.alt5₂)⟩
  not_le := by
    intro hle
    apply h.cs.not_le
    have h1 := cj_mono (t := t⁻¹) hle
    rw [cj_cj, inv_mul_cancel, cj_one, h.cj_M (S.inv_mem h.t_mem)] at h1
    exact h1
  thompson := by
    calc ⁅cj t L, thompsonJ S⁆ = ⁅cj t L, cj t (thompsonJ S)⁆ := by rw [cj_thompsonJ h.t_mem]
      _ = cj t ⁅L, thompsonJ S⁆ := cj_comm t L _
      _ = cj t L := by rw [h.cs.thompson]
  eq_join := by
    rw [h.conjJoin_L₂]
    exact h.cs.eq_join
  blocks := by
    refine Or.inr ⟨t⁻¹, S.inv_mem h.t_mem, ?_, ?_, ?_⟩
    · show cj t⁻¹ (cj t L) ≠ cj t L
      rw [cj_cj, inv_mul_cancel, cj_one]
      exact fun hh => h.ne hh.symm
    · show conjJoin S (cj t L) = cj t L ⊔ cj t⁻¹ (cj t L)
      rw [h.conjJoin_L₂, h.join, cj_cj, inv_mul_cancel, cj_one, sup_comm]
    · show ⁅cj t L, cj t⁻¹ (cj t L)⁆ = ⊥
      rw [cj_cj, inv_mul_cancel, cj_one, Subgroup.commutator_comm]
      exact h.comm
  minParabolic := h.cs.minParabolic
  maxInf := h.cs.maxInf

theorem cfg₂ : A5Cfg2 G T M H S (cj t L) where
  cs := h.cs₂
  alt5 := h.alt5₂
  double := by
    rw [h.conjJoin_L₂, h.join]
    intro hh
    apply h.ne
    have hLle : L ≤ cj t L := le_sup_left.trans hh.le
    exact (Subgroup.eq_of_le_of_card_ge hLle (by rw [card_cj])).symm

end Data

section Std

variable {R : Subgroup G}

omit [Finite G] in
theorem pi_eq_theta {L R : Subgroup G} (hRN : R ≤ Subgroup.normalizer (L : Set G)) (P : A5Pi L)
    (θ : ↥(L ⊔ R) →* Perm (Fin 5))
    (hθα : ∀ (l : G) (hl : l ∈ L), θ ⟨l, Subgroup.mem_sup_left hl⟩ =
      ((P.α ⟨l, hl⟩ : Alt5) : Perm (Fin 5))) (y : ↥(L ⊔ R)) :
    P.π ⟨y, (sup_le Subgroup.le_normalizer hRN : L ⊔ R ≤ Subgroup.normalizer (L : Set G)) y.2⟩ =
      θ y := by
  have hyN : (y : G) ∈ Subgroup.normalizer (L : Set G) :=
    (sup_le Subgroup.le_normalizer hRN : L ⊔ R ≤ Subgroup.normalizer (L : Set G)) y.2
  apply Action.centerless
  intro a
  obtain ⟨ℓ, rfl⟩ := P.hα a
  have hℓ' : (y : G) * (ℓ : G) * (y : G)⁻¹ ∈ L :=
    (Subgroup.mem_normalizer_iff.mp hyN (ℓ : G)).1 ℓ.2
  have h1 : P.π ⟨(y : G) * (ℓ : G) * (y : G)⁻¹, Subgroup.le_normalizer hℓ'⟩ =
      P.π ⟨y, hyN⟩ * ((P.α ℓ : Alt5) : Perm (Fin 5)) * (P.π ⟨y, hyN⟩)⁻¹ := by
    have e : (⟨(y : G) * (ℓ : G) * (y : G)⁻¹, Subgroup.le_normalizer hℓ'⟩ :
        ↥(Subgroup.normalizer (L : Set G))) =
        ⟨y, hyN⟩ * ⟨(ℓ : G), Subgroup.le_normalizer ℓ.2⟩ * ⟨y, hyN⟩⁻¹ := rfl
    rw [e, map_mul, map_mul, map_inv, P.hπα (ℓ : G) ℓ.2]
  have h2 : θ ⟨(y : G) * (ℓ : G) * (y : G)⁻¹, Subgroup.mem_sup_left hℓ'⟩ =
      θ y * ((P.α ℓ : Alt5) : Perm (Fin 5)) * (θ y)⁻¹ := by
    have e : (⟨(y : G) * (ℓ : G) * (y : G)⁻¹, Subgroup.mem_sup_left hℓ'⟩ : ↥(L ⊔ R)) =
        y * ⟨(ℓ : G), Subgroup.mem_sup_left ℓ.2⟩ * y⁻¹ := rfl
    rw [e, map_mul, map_mul, map_inv, hθα (ℓ : G) ℓ.2]
  have h3 := P.hπα ((y : G) * (ℓ : G) * (y : G)⁻¹) hℓ'
  have h4 := hθα ((y : G) * (ℓ : G) * (y : G)⁻¹) hℓ'
  rw [← h1, ← h2, h3, h4]

omit [Finite G] in
theorem im_eq_map_theta {L R K : Subgroup G} (hRN : R ≤ Subgroup.normalizer (L : Set G))
    (P : A5Pi L) (θ : ↥(L ⊔ R) →* Perm (Fin 5))
    (hθα : ∀ (l : G) (hl : l ∈ L), θ ⟨l, Subgroup.mem_sup_left hl⟩ =
      ((P.α ⟨l, hl⟩ : Alt5) : Perm (Fin 5))) (hK : K ≤ L ⊔ R) :
    P.im K = (K.subgroupOf (L ⊔ R)).map θ := by
  ext g
  rw [P.mem_im, Subgroup.mem_map]
  constructor
  · rintro ⟨y, hyK, rfl⟩
    refine ⟨⟨y, hK hyK⟩, Subgroup.mem_subgroupOf.2 hyK, ?_⟩
    exact (pi_eq_theta hRN P θ hθα ⟨y, hK hyK⟩).symm
  · rintro ⟨y, hy, rfl⟩
    exact ⟨⟨y, (sup_le Subgroup.le_normalizer hRN : L ⊔ R ≤ _) y.2⟩, Subgroup.mem_subgroupOf.1 hy,
      pi_eq_theta hRN P θ hθα y⟩

theorem exists_std2 (hC54 : LemmaC54_3_s2) (hcs : ConstrainedSetting G T M H S L)
    (h5 : IsAltType L 5) (hne : conjJoin S L ≠ L) :
    ∃ P : A5Pi L, P.im (baum S) = Estd ∧ P.im (thompsonJ S) = Estd := by
  obtain ⟨hRN, -, -, -, hθ⟩ := hC54 G T M H S L hcs h5 hne
  have hL := hcs.block.1.1
  obtain ⟨α, hα, hαk, -⟩ := id h5
  obtain ⟨P, hPα⟩ := exists_a5pi hL h5 α hα hαk
  obtain ⟨θ, τ₁, τ₂, -, -, hθα, hτ₁, hτ₂, hdis, hθR, hθJ⟩ := hθ α hα hαk
  have hθα' : ∀ (l : G) (hl : l ∈ L), θ ⟨l, Subgroup.mem_sup_left hl⟩ =
      ((P.α ⟨l, hl⟩ : Alt5) : Perm (Fin 5)) := by
    intro l hl
    rw [hθα l hl, hPα]
  have hRLR : baum S ≤ L ⊔ baum S := le_sup_right
  have hJLR : thompsonJ S ≤ L ⊔ baum S := (C1GN.thompsonJ_le_baum S).trans hRLR
  obtain ⟨ρ, hρ1, hρ2⟩ := swaps_conj τ₁ τ₂ hτ₁ hτ₂ hdis
  have hcl : (Subgroup.closure ({τ₁, τ₂} : Set (Perm (Fin 5)))).map (MulAut.conj ρ).toMonoidHom =
      Estd := by
    rw [MonoidHom.map_closure, ← closure_swaps]
    congr 1
    ext g
    simp only [Set.mem_image, Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · rintro ⟨x, rfl | rfl, rfl⟩
      · exact Or.inl hρ1
      · exact Or.inr hρ2
    · rintro (rfl | rfl)
      · exact ⟨τ₁, Or.inl rfl, hρ1⟩
      · exact ⟨τ₂, Or.inr rfl, hρ2⟩
  refine ⟨P.conj ρ, ?_, ?_⟩
  · rw [A5Pi.im_conj, im_eq_map_theta hRN P θ hθα' hRLR, hθR, hcl]
  · rw [A5Pi.im_conj, im_eq_map_theta hRN P θ hθα' hJLR, hθJ, hcl]

end Std

end CFSG.QuasithinUnique.A5.S2
