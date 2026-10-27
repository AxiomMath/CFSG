module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.Action
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.Block
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.DoubleA3.L2_4_27
public import Certificates.Certificate12952
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.Inputs

public section

namespace CFSG.QuasithinUnique.A5

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.QuasithinUnique.DoubleA3
  CFSG.QuasithinUnique.A5.Delta5 CFSG.QuasithinUnique.A5.Action

variable {G : Type} [Group G] [Finite G] {T M H S L : Subgroup G}

structure H247Facts (T H S L : Subgroup G) : Prop where
  index_two : S.relIndex T = 2
  TC_abel : IsElemAbelian 2 (blockTC T S L)
  Q_eq : pCoreOf 2 H = blockTC T S L ⊔ blockU L
  TC_inf_U : blockTC T S L ⊓ blockU L = ⊥
  TC_inf_conj : ∀ x ∈ T, x ∉ S → blockTC T S L ⊓ conjR (blockTC T S L) x = ⊥
  R_eq : ∀ x ∈ T, x ∉ S → baum S = blockTC T S L ⊔ (blockU L ⊔ conjR (blockU L) x)
  TC_inf_UU : ∀ x ∈ T, x ∉ S → blockTC T S L ⊓ (blockU L ⊔ conjR (blockU L) x) = ⊥
  TC_comm : ∀ x ∈ T, x ∉ S → ∀ t ∈ blockTC T S L, ∀ y ∈ blockU L ⊔ conjR (blockU L) x,
    t * y = y * t
  L_eq : ∀ x ∈ T, x ∉ S → ⁅L, conjR (blockU L) x⁆ = L

theorem h247_facts (h247 : Lemma2_4_27) (hcs : ConstrainedSetting G T M H S L)
    (h5 : IsAltType L 5) (hj : conjJoin S L = L) : H247Facts T H S L := by
  obtain ⟨⟨hidx, -, -⟩, -, ⟨hab, hQ, hinf, hconj⟩, hR⟩ :=
    h247 G T M H S L hcs (Or.inl ⟨h5, hj⟩)
  have hU0 : blockU0 S L = blockU L := blockU0_eq_blockU hj
  rw [hU0] at hQ hinf
  refine ⟨hidx, hab, hQ, hinf, hconj, ?_, ?_, ?_, ?_⟩
  · intro x hx hxS
    have := (hR x hx hxS).1
    rwa [hU0] at this
  · intro x hx hxS
    have := (hR x hx hxS).2.1
    rwa [hU0] at this
  · intro x hx hxS
    have := (hR x hx hxS).2.2.1
    rwa [hU0] at this
  · intro x hx hxS
    have := (hR x hx hxS).2.2.2
    rwa [hU0, hj] at this

theorem baum_le_H (hcs : ConstrainedSetting G T M H S L) : baum S ≤ H :=
  fun _ hx => hcs.sylow.le hx.1

omit [Finite G] in
theorem baum_le_S : baum S ≤ S := fun _ hx => hx.1

theorem pCoreOf_le_baum (hcs : ConstrainedSetting G T M H S L) (F : H247Facts T H S L) :
    pCoreOf 2 H ≤ baum S := by
  obtain ⟨x, hxT, hxS⟩ : ∃ x ∈ T, x ∉ S := by
    by_contra hcon
    push Not at hcon
    exact hcs.ne_T (le_antisymm hcs.le_T hcon)
  rw [F.Q_eq, F.R_eq x hxT hxS]
  exact sup_le_sup_left le_sup_left _

theorem blockZ_eq_bot (hcs : ConstrainedSetting G T M H S L) (F : H247Facts T H S L)
    (hj : conjJoin S L = L) (hUS : blockU L ≤ S) : blockZ L = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  have hxTC : x ∈ blockTC T S L := by
    show x ∈ T ⊓ Subgroup.centralizer (conjJoin S L : Set G)
    rw [hj]
    exact ⟨hcs.le_T (hUS hx.1), hx.2⟩
  have : x ∈ blockTC T S L ⊓ blockU L := ⟨hxTC, hx.1⟩
  rwa [F.TC_inf_U] at this

theorem blockU_le_S (hcs : ConstrainedSetting G T M H S L) (hj : conjJoin S L = L) :
    blockU L ≤ S :=
  (C56.blockU_le_pCoreOf hcs hj).trans (C56.pCoreOf_le_S hcs)

omit [Finite G] in
theorem ModData.pi_eq_one_iff {H L : Subgroup G} (D : ModData H L)
    (hHU : ∀ h ∈ H, ∀ u ∈ blockU L, h * u * h⁻¹ ∈ blockU L) (h : ↥H) :
    D.π h = 1 ↔ ∀ u ∈ blockU L, (h : G) * u * (h : G)⁻¹ = u := by
  constructor
  · intro h1 u hu
    have hmem := hHU h h.2 u hu
    have := D.hβ h ⟨u, hu⟩ ⟨_, hmem⟩ rfl
    rw [h1, vact_one] at this
    have h2 := D.β.injective (Multiplicative.toAdd.injective this)
    exact congrArg Subtype.val h2
  · intro h1
    apply vact_faithful
    intro w
    obtain ⟨u, rfl⟩ : ∃ u : ↥(blockU L), Multiplicative.toAdd (D.β u) = w :=
      ⟨D.β.symm (Multiplicative.ofAdd w), by simp⟩
    exact (D.hβ h u u (h1 u u.2).symm).symm

theorem H_normalizes_U (hcs : ConstrainedSetting G T M H S L) (hj : conjJoin S L = L) :
    ∀ h ∈ H, ∀ u ∈ blockU L, h * u * h⁻¹ ∈ blockU L := by
  intro h hh u hu
  have := C1.mem_normalizer_blockU (C56.H_le_normalizer hcs hj hh)
  exact ((Subgroup.mem_normalizer_iff.mp this) u).mp hu

theorem ModData.ker_iff (hcs : ConstrainedSetting G T M H S L) (hj : conjJoin S L = L)
    (D : ModData H L) (h : ↥H) : D.π h = 1 ↔ (h : G) ∈ pCoreOf 2 H := by
  rw [D.pi_eq_one_iff (H_normalizes_U hcs hj), ← C56.inf_centralizer_eq hcs hj]
  constructor
  · intro h1
    refine ⟨h.2, ?_⟩
    show (h : G) ∈ Subgroup.centralizer (blockU L : Set G)
    rw [Subgroup.mem_centralizer_iff]
    intro u hu
    have := h1 u hu
    calc u * (h : G) = ((h : G) * u * (h : G)⁻¹) * (h : G) := by rw [this]
      _ = (h : G) * u := by group
  · rintro ⟨-, h2⟩ u hu
    have h2' : (h : G) ∈ Subgroup.centralizer (blockU L : Set G) := h2
    have := Subgroup.mem_centralizer_iff.mp h2' u hu
    calc (h : G) * u * (h : G)⁻¹ = (u * (h : G)) * (h : G)⁻¹ := by rw [← this]
      _ = u := by group

theorem conj_mem_Estd {ρ τ₁ τ₂ : Equiv.Perm (Fin 5)} (h1 : ρ * τ₁ * ρ⁻¹ = Equiv.swap 0 1)
    (h2 : ρ * τ₂ * ρ⁻¹ = Equiv.swap 2 3) {σ : Equiv.Perm (Fin 5)}
    (hσ : σ ∈ Subgroup.closure ({τ₁, τ₂} : Set (Equiv.Perm (Fin 5)))) : ρ * σ * ρ⁻¹ ∈ Estd := by
  rw [← closure_swaps]
  induction hσ using Subgroup.closure_induction with
  | mem x hx =>
    rcases hx with rfl | rfl
    · rw [h1]; exact Subgroup.subset_closure (by simp)
    · rw [h2]; exact Subgroup.subset_closure (by simp)
  | one => simp
  | mul a b _ _ ha hb =>
    rw [show ρ * (a * b) * ρ⁻¹ = (ρ * a * ρ⁻¹) * (ρ * b * ρ⁻¹) by group]
    exact mul_mem ha hb
  | inv a _ ha =>
    rw [show ρ * a⁻¹ * ρ⁻¹ = (ρ * a * ρ⁻¹)⁻¹ by group]
    exact inv_mem ha

theorem mem_closure_of_conj_mem_Estd {ρ τ₁ τ₂ : Equiv.Perm (Fin 5)}
    (h1 : ρ * τ₁ * ρ⁻¹ = Equiv.swap 0 1) (h2 : ρ * τ₂ * ρ⁻¹ = Equiv.swap 2 3)
    {σ : Equiv.Perm (Fin 5)} (hσ : ρ * σ * ρ⁻¹ ∈ Estd) :
    σ ∈ Subgroup.closure ({τ₁, τ₂} : Set (Equiv.Perm (Fin 5))) := by
  have hE : ρ * σ * ρ⁻¹ ∈ Subgroup.closure ({Equiv.swap 0 1, Equiv.swap 2 3} :
      Set (Equiv.Perm (Fin 5))) := by rw [closure_swaps]; exact hσ
  have key : ∀ y ∈ Subgroup.closure ({Equiv.swap 0 1, Equiv.swap 2 3} :
      Set (Equiv.Perm (Fin 5))), ρ⁻¹ * y * ρ ∈ Subgroup.closure ({τ₁, τ₂} :
      Set (Equiv.Perm (Fin 5))) := by
    intro y hy
    induction hy using Subgroup.closure_induction with
    | mem x hx =>
      rcases hx with rfl | rfl
      · have : ρ⁻¹ * Equiv.swap 0 1 * ρ = τ₁ := by rw [← h1]; group
        rw [this]; exact Subgroup.subset_closure (by simp)
      · have : ρ⁻¹ * Equiv.swap 2 3 * ρ = τ₂ := by rw [← h2]; group
        rw [this]; exact Subgroup.subset_closure (by simp)
    | one => simp
    | mul a b _ _ ha hb =>
      rw [show ρ⁻¹ * (a * b) * ρ = (ρ⁻¹ * a * ρ) * (ρ⁻¹ * b * ρ) by group]
      exact mul_mem ha hb
    | inv a _ ha =>
      rw [show ρ⁻¹ * a⁻¹ * ρ = (ρ⁻¹ * a * ρ)⁻¹ by group]
      exact inv_mem ha
  have := key _ hE
  rwa [show ρ⁻¹ * (ρ * σ * ρ⁻¹) * ρ = σ by group] at this

theorem blockQ_eq_blockU (h245_4 : Lemma245_4) (hcs : ConstrainedSetting G T M H S L)
    (hj : conjJoin S L = L) : blockQ L = blockU L := by
  have := h245_4 G T M H S L hcs
  rw [blockU0_eq_blockU hj, hj] at this
  exact this.symm

theorem exists_stdData (hcs : ConstrainedSetting G T M H S L)
    (hj : conjJoin S L = L)
    (h5 : IsAltType L 5) (F : H247Facts T H S L) (hQ : blockQ L = blockU L)
    (hC54 : LemmaC54_3) :
    ∃ D : ModData H L, Function.Surjective D.π ∧
      (∀ h : ↥H, D.π h = 1 ↔ (h : G) ∈ pCoreOf 2 H) ∧
      (∀ (r : G) (hr : r ∈ baum S), D.π ⟨r, baum_le_H hcs hr⟩ ∈ Estd) ∧
      (∀ σ ∈ Estd, ∃ (r : G) (hr : r ∈ baum S), D.π ⟨r, baum_le_H hcs hr⟩ = σ) ∧
      H = L ⊔ baum S := by
  have hUS := blockU_le_S hcs hj
  have hZ := blockZ_eq_bot hcs F hj hUS
  obtain ⟨D₀⟩ := exists_modData hcs hj hQ hZ h5
  obtain ⟨θ, τ₁, τ₂, -, -, hθα, hτ₁, hτ₂, hdisj, hθR⟩ :=
    hC54 G T M H S L hcs h5 hj D₀.α D₀.hα D₀.hα_ker
  have hRH : baum S ≤ H := baum_le_H hcs
  have hRL : ∀ r ∈ baum S, ∀ l ∈ L, r * l * r⁻¹ ∈ L := fun r hr l hl =>
    ((Subgroup.mem_normalizer_iff.mp (C56.H_le_normalizer hcs hj (hRH hr))) l).mp hl
  have hπθR : ∀ (r : G) (hr : r ∈ baum S),
      D₀.π ⟨r, hRH hr⟩ = θ ⟨r, Subgroup.mem_sup_right hr⟩ := by
    intro r hr
    apply centerless
    intro a
    obtain ⟨l, rfl⟩ := D₀.hα a
    have hl' := hRL r hr l l.2
    have h1 := D₀.hπψ ⟨r, hRH hr⟩ l ⟨_, hl'⟩ rfl
    have h2 : θ ⟨r * l * r⁻¹, Subgroup.mem_sup_left hl'⟩ =
        θ ⟨r, Subgroup.mem_sup_right hr⟩ * θ ⟨l, Subgroup.mem_sup_left l.2⟩ *
          (θ ⟨r, Subgroup.mem_sup_right hr⟩)⁻¹ := by
      rw [← map_inv, ← map_mul, ← map_mul]; rfl
    rw [hθα _ hl', hθα _ l.2] at h2
    exact h1.symm.trans h2
  have hRmem : ∀ (r : G) (hr : r ∈ baum S),
      θ ⟨r, Subgroup.mem_sup_right hr⟩ ∈
        Subgroup.closure ({τ₁, τ₂} : Set (Equiv.Perm (Fin 5))) := by
    intro r hr
    rw [← hθR]
    exact ⟨⟨r, Subgroup.mem_sup_right hr⟩, Subgroup.mem_subgroupOf.mpr hr, rfl⟩
  have hRsurj : ∀ σ ∈ Subgroup.closure ({τ₁, τ₂} : Set (Equiv.Perm (Fin 5))),
      ∃ (r : G) (hr : r ∈ baum S), θ ⟨r, Subgroup.mem_sup_right hr⟩ = σ := by
    intro σ hσ
    rw [← hθR] at hσ
    obtain ⟨y, hy, rfl⟩ := hσ
    exact ⟨y.1, Subgroup.mem_subgroupOf.mp hy, rfl⟩
  obtain ⟨ρ, hρ1, hρ2⟩ := swaps_conj τ₁ τ₂ hτ₁ hτ₂ hdisj
  let D := D₀.conj ρ
  have hDπ : ∀ h : ↥H, D.π h = ρ * D₀.π h * ρ⁻¹ := fun h => rfl
  have hDR : ∀ (r : G) (hr : r ∈ baum S), D.π ⟨r, hRH hr⟩ ∈ Estd := by
    intro r hr
    rw [hDπ, hπθR r hr]
    exact conj_mem_Estd hρ1 hρ2 (hRmem r hr)
  have hDRsurj : ∀ σ ∈ Estd, ∃ (r : G) (hr : r ∈ baum S), D.π ⟨r, hRH hr⟩ = σ := by
    intro σ hσ
    have hσ' : ρ⁻¹ * σ * ρ ∈ Subgroup.closure ({τ₁, τ₂} : Set (Equiv.Perm (Fin 5))) :=
      mem_closure_of_conj_mem_Estd hρ1 hρ2 (by
        rw [show ρ * (ρ⁻¹ * σ * ρ) * ρ⁻¹ = σ by group]; exact hσ)
    obtain ⟨r, hr, hθr⟩ := hRsurj _ hσ'
    refine ⟨r, hr, ?_⟩
    rw [hDπ, hπθR r hr, hθr]
    group
  have hsurj' : ∀ σ : Equiv.Perm (Fin 5),
      ∃ x : ↥H, (x : G) ∈ L ⊔ baum S ∧ D.π x = σ := by
    intro σ
    by_cases hs : Equiv.Perm.sign σ = 1
    · obtain ⟨l, hl⟩ := D.hα ⟨σ, Equiv.Perm.mem_alternatingGroup.mpr hs⟩
      refine ⟨⟨l, D.hLH l.2⟩, Subgroup.mem_sup_left l.2, ?_⟩
      have := D.hπL l l.2
      rw [hl] at this
      exact this
    · have hτ : Equiv.swap (0 : Fin 5) 1 ∈ Estd := by
        show Equiv.swap (0 : Fin 5) 1 ∈ Eset; exact Certificates.certificate12952
      obtain ⟨r, hr, hπr⟩ := hDRsurj _ hτ
      have hsg : Equiv.Perm.sign (σ * (Equiv.swap (0 : Fin 5) 1)⁻¹) = 1 := by
        rw [Equiv.Perm.sign_mul, Equiv.Perm.sign_inv]
        rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h
        · exact absurd h hs
        · rw [h, Equiv.Perm.sign_swap (by decide)]; decide
      obtain ⟨l, hl⟩ := D.hα ⟨σ * (Equiv.swap (0 : Fin 5) 1)⁻¹,
        Equiv.Perm.mem_alternatingGroup.mpr hsg⟩
      refine ⟨⟨l, D.hLH l.2⟩ * ⟨r, hRH hr⟩,
        Subgroup.mul_mem_sup l.2 hr, ?_⟩
      have h1 := D.hπL l l.2
      rw [hl] at h1
      rw [map_mul, h1, hπr]
      group
  refine ⟨D, ?_, fun h => D.ker_iff hcs hj h, hDR, hDRsurj, ?_⟩
  · intro σ
    obtain ⟨x, -, hx⟩ := hsurj' σ
    exact ⟨x, hx⟩
  · apply le_antisymm _ (sup_le D.hLH hRH)
    intro h hh
    obtain ⟨x, hx, hπx⟩ := hsurj' (D.π ⟨h, hh⟩)
    have hker : (⟨h, hh⟩ * x⁻¹ : ↥H) ∈ D.π.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hπx, mul_inv_cancel]
    have hQ' : ((⟨h, hh⟩ * x⁻¹ : ↥H) : G) ∈ pCoreOf 2 H := (D.ker_iff hcs hj _).mp hker
    have hRQ := pCoreOf_le_baum hcs F hQ'
    have hh' : h = (h * (x : G)⁻¹) * x := by group
    rw [hh']
    exact mul_mem (Subgroup.mem_sup_right hRQ) hx

end CFSG.QuasithinUnique.A5
