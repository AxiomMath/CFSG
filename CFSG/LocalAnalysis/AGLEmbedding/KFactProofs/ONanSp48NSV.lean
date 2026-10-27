module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanSp48NSBase
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanSp48Fac

public section

namespace CFSG.AGLEmbedding.KFactProofs.Sp48

open CFSG.Quasithin CFSG.Open CFSG.ClassicalInvolution.Models.SymplecticPairs
open scoped MatrixGroups

section V

variable {Y : Type} [Group Y] {K : Subgroup Y} [K.Normal] {e : K ≃* Sp8} {ψ : Sp8 ≃* Sp8}

@[expose] noncomputable def Vone (e : K ≃* Sp8) (ψ : Sp8 ≃* Sp8) : Subgroup Y :=
  ((fpsi e ψ).comp blk0).range

@[expose] noncomputable def Vtwo (e : K ≃* Sp8) (ψ : Sp8 ≃* Sp8) : Subgroup Y :=
  ((fpsi e ψ).comp blk1).range

@[expose] noncomputable def Vzero (e : K ≃* Sp8) (ψ : Sp8 ≃* Sp8) : Subgroup Y :=
  ((fpsi e ψ).comp blkHom).range

omit [K.Normal] in
theorem Vone_eq_map : Vone e ψ = (MonoidHom.range blk0).map (fpsi e ψ) :=
  MonoidHom.range_comp _ _

omit [K.Normal] in
theorem Vtwo_eq_map : Vtwo e ψ = (MonoidHom.range blk1).map (fpsi e ψ) :=
  MonoidHom.range_comp _ _

omit [K.Normal] in
theorem Vzero_eq_map : Vzero e ψ = (MonoidHom.range blkHom).map (fpsi e ψ) :=
  MonoidHom.range_comp _ _

omit [K.Normal] in
theorem Vzero_eq_sup : Vzero e ψ = Vone e ψ ⊔ Vtwo e ψ := by
  apply le_antisymm
  · rintro _ ⟨⟨x, y⟩, rfl⟩
    show fpsi e ψ (blk0 x * blk1 y) ∈ _
    rw [map_mul]
    exact Subgroup.mul_mem_sup ⟨x, rfl⟩ ⟨y, rfl⟩
  · refine sup_le ?_ ?_
    · rintro _ ⟨x, rfl⟩
      exact ⟨(x, 1), by simp [blkHom_apply]⟩
    · rintro _ ⟨y, rfl⟩
      exact ⟨(1, y), by simp [blkHom_apply]⟩

omit [K.Normal] in
theorem Vzero_le_K : Vzero e ψ ≤ K := by
  rintro _ ⟨p, rfl⟩
  exact emb_mem e _

omit [K.Normal] in
theorem Vone_perfect : ⁅Vone e ψ, Vone e ψ⁆ = Vone e ψ := by
  rw [Vone_eq_map, ← Subgroup.map_commutator, blk0_range_perfect]

omit [K.Normal] in
theorem Vtwo_perfect : ⁅Vtwo e ψ, Vtwo e ψ⁆ = Vtwo e ψ := by
  rw [Vtwo_eq_map, ← Subgroup.map_commutator, blk1_range_perfect]

omit [K.Normal] in
theorem commutator_Vone_Vtwo : ⁅Vone e ψ, Vtwo e ψ⁆ = ⊥ := by
  rw [Vone_eq_map, Vtwo_eq_map, ← Subgroup.map_commutator]
  have : ⁅MonoidHom.range blk0, MonoidHom.range blk1⁆ = ⊥ := by
    rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
    rintro _ ⟨x, rfl⟩
    rw [Subgroup.mem_centralizer_iff]
    rintro _ ⟨y, rfl⟩
    exact (blk_commute x y).symm.eq
  rw [this, Subgroup.map_bot]

omit [K.Normal] in
theorem Vzero_perfect : ⁅Vzero e ψ, Vzero e ψ⁆ = Vzero e ψ := by
  apply le_antisymm (Subgroup.commutator_le_self _)
  rw [Vzero_eq_sup]
  calc Vone e ψ ⊔ Vtwo e ψ = ⁅Vone e ψ, Vone e ψ⁆ ⊔ ⁅Vtwo e ψ, Vtwo e ψ⁆ := by
        rw [Vone_perfect, Vtwo_perfect]
    _ ≤ _ := sup_le
        (Subgroup.commutator_mono le_sup_left le_sup_left)
        (Subgroup.commutator_mono le_sup_right le_sup_right)

theorem blk0_injective : Function.Injective blk0 := longBlock_injective (K := GF8) (n := 2) 0

theorem blk1_injective : Function.Injective blk1 := longBlock_injective (K := GF8) (n := 2) 1

omit [K.Normal] in
noncomputable def VoneEquiv (e : K ≃* Sp8) (ψ : Sp8 ≃* Sp8) : Sl28 ≃* Vone e ψ :=
  MonoidHom.ofInjective ((fpsi_injective e ψ).comp blk0_injective)

omit [K.Normal] in
noncomputable def VtwoEquiv (e : K ≃* Sp8) (ψ : Sp8 ≃* Sp8) : Sl28 ≃* Vtwo e ψ :=
  MonoidHom.ofInjective ((fpsi_injective e ψ).comp blk1_injective)

omit [K.Normal] in
theorem Vone_caseTwo : ∃ d : TauCeti.ValidLieTypeIndex, IsCaseTwoIndex 3 d ∧
    Nonempty (Vone e ψ ≃* CatGroup d) := by
  obtain ⟨d, hd, ⟨eL⟩⟩ := sl28_isCaseTwoGroup
  exact ⟨d, hd, ⟨(VoneEquiv e ψ).symm.trans eL⟩⟩

omit [K.Normal] in
theorem Vtwo_caseTwo : ∃ d : TauCeti.ValidLieTypeIndex, IsCaseTwoIndex 3 d ∧
    Nonempty (Vtwo e ψ ≃* CatGroup d) := by
  obtain ⟨d, hd, ⟨eL⟩⟩ := sl28_isCaseTwoGroup
  exact ⟨d, hd, ⟨(VtwoEquiv e ψ).symm.trans eL⟩⟩

end V

section VY

variable {Y : Type} [Group Y] [Finite Y] {K : Subgroup Y} [K.Normal] {e : K ≃* Sp8}
  {T : Subgroup Y} {y : Y} {ψ : Sp8 ≃* Sp8} {Y₀ : Subgroup Y}

omit [Finite Y] [K.Normal] in
theorem fpsi_mem_Y₀ (hcl : Y₀.comap (emb e) = (wrp (⊤ : Subgroup Sl28)).map ψ.toMonoidHom)
    {m : Sp8} (hm : m ∈ wrp (⊤ : Subgroup Sl28)) : fpsi e ψ m ∈ Y₀ := by
  have : ψ m ∈ Y₀.comap (emb e) := by
    rw [hcl]
    exact ⟨m, hm, rfl⟩
  exact this

omit [Finite Y] [K.Normal] in
theorem Vzero_le_Y₀ (hcl : Y₀.comap (emb e) = (wrp (⊤ : Subgroup Sl28)).map ψ.toMonoidHom) :
    Vzero e ψ ≤ Y₀ := by
  rintro _ ⟨⟨x, y⟩, rfl⟩
  exact fpsi_mem_Y₀ hcl (blkRange_le_wrp ⟨(x, y), rfl⟩)

omit [Finite Y] [K.Normal] in
theorem fpsi_mem_Vzero {v : Sp8} (hv : v ∈ MonoidHom.range blkHom) : fpsi e ψ v ∈ Vzero e ψ := by
  rw [Vzero_eq_map]
  exact ⟨v, hv, rfl⟩

omit [Finite Y] [K.Normal] in
theorem emb_mem_Vzero (hψ : ∀ x, x ∈ spT0 ↔ ψ x ∈ spT0) {s : Sp8} (hs : s ∈ spT0) :
    emb e s ∈ Vzero e ψ := by
  have h1 : ψ.symm s ∈ spT0 := by
    rw [hψ, MulEquiv.apply_symm_apply]
    exact hs
  have := fpsi_mem_Vzero (e := e) (ψ := ψ) (spT0_le_blkRange h1)
  rwa [fpsi_apply, MulEquiv.apply_symm_apply] at this

omit [Finite Y] in
theorem Vzero_mem_normalizer (hcl : Y₀.comap (emb e) = (wrp (⊤ : Subgroup Sl28)).map ψ.toMonoidHom)
    {g : Y} (hg : g ∈ Y₀) : g ∈ Subgroup.normalizer (Vzero e ψ : Set Y) := by
  apply mem_normalizer_of_map_conj
  rw [Vzero_eq_map, conj_map_fpsi, map_blkRange_eq (omg_wrp_top hcl hg)]

omit [Finite Y] in
theorem Vone_mem_normalizer (hcl : Y₀.comap (emb e) = (wrp (⊤ : Subgroup Sl28)).map ψ.toMonoidHom)
    {g : Y} (hg : g ∈ Y₀) (hc : g * fpsi e ψ (blk0 slZ) = fpsi e ψ (blk0 slZ) * g) :
    g ∈ Subgroup.normalizer (Vone e ψ : Set Y) := by
  apply mem_normalizer_of_map_conj
  rw [Vone_eq_map, conj_map_fpsi]
  have hV := map_blkRange_eq (omg_wrp_top hcl hg)
  have hz : omg e ψ g (blk0 slZ) = blk0 slZ := by
    apply fpsi_injective e ψ
    rw [fpsi_omg, hc]
    group
  rw [map_blk0_range_eq hV hz]

omit [Finite Y] in
theorem Vtwo_mem_normalizer (hcl : Y₀.comap (emb e) = (wrp (⊤ : Subgroup Sl28)).map ψ.toMonoidHom)
    {g : Y} (hg : g ∈ Y₀) (hc : g * fpsi e ψ (blk1 slZ) = fpsi e ψ (blk1 slZ) * g) :
    g ∈ Subgroup.normalizer (Vtwo e ψ : Set Y) := by
  apply mem_normalizer_of_map_conj
  rw [Vtwo_eq_map, conj_map_fpsi]
  have hV := map_blkRange_eq (omg_wrp_top hcl hg)
  have hz : omg e ψ g (blk1 slZ) = blk1 slZ := by
    apply fpsi_injective e ψ
    rw [fpsi_omg, hc]
    group
  rw [map_blk1_range_eq hV hz]

omit [K.Normal] in
theorem Sp48Setup.T_le_Y₀ (S : Sp48Setup e T y)
    (hNE : Subgroup.normalizer ((spE.map (emb e) : Subgroup Y) : Set Y) ≤ Y₀) : T ≤ Y₀ := by
  intro t ht
  apply hNE
  apply Subgroup.mem_normalizer_fintype
  intro z hz
  have hz' : z ∈ centerOf T := by
    rw [S.center_T]
    exact hz
  have hcomm : t * z = z * t := Subgroup.mem_centralizer_iff.1 hz'.2 t ht
  rw [hcomm]
  simpa using hz

omit [Finite Y] [K.Normal] in
theorem Sp48Setup.inf_K_eq (S : Sp48Setup e T y) : T ⊓ K = spT0.map (emb e) := by
  ext t
  rw [Subgroup.mem_inf]
  constructor
  · rintro ⟨ht, htK⟩
    obtain ⟨k, hk, rfl⟩ := S.inf_K ht htK
    exact ⟨k, hk, rfl⟩
  · rintro ⟨k, hk, rfl⟩
    exact ⟨S.emb_mem_T hk, emb_mem e k⟩

omit [Finite Y] [K.Normal] in
theorem Sp48Setup.card_inf_K (S : Sp48Setup e T y) : Nat.card (T ⊓ K : Subgroup Y) = 3 ^ 4 := by
  rw [S.inf_K_eq, Subgroup.card_map_of_injective (emb_injective e), card_spT0]
  norm_num

omit [Finite Y] [K.Normal] in
theorem Sp48Setup.TK_le_Vzero (S : Sp48Setup e T y) (hψ : ∀ x, x ∈ spT0 ↔ ψ x ∈ spT0) :
    T ⊓ K ≤ Vzero e ψ := by
  intro t ht
  obtain ⟨k, hk, rfl⟩ := S.inf_K ht.1 ht.2
  exact emb_mem_Vzero hψ hk

omit [Finite Y] in
theorem Sp48Setup.T_le_normalizer_Vone (S : Sp48Setup e T y)
    (hcl : Y₀.comap (emb e) = (wrp (⊤ : Subgroup Sl28)).map ψ.toMonoidHom)
    (hψ : ∀ x, x ∈ spT0 ↔ ψ x ∈ spT0) (hTY : T ≤ Y₀) :
    T ≤ Subgroup.normalizer (Vone e ψ : Set Y) := by
  intro t ht
  refine Vone_mem_normalizer hcl (hTY ht) ?_
  have hz : fpsi e ψ (blk0 slZ) ∈ centerOf T := by
    rw [S.center_T]
    exact ⟨ψ (blk0 slZ), psi_spE hψ blk0_slZ_mem_spE, rfl⟩
  exact Subgroup.mem_centralizer_iff.1 hz.2 t ht

omit [Finite Y] in
theorem Sp48Setup.T_le_normalizer_Vtwo (S : Sp48Setup e T y)
    (hcl : Y₀.comap (emb e) = (wrp (⊤ : Subgroup Sl28)).map ψ.toMonoidHom)
    (hψ : ∀ x, x ∈ spT0 ↔ ψ x ∈ spT0) (hTY : T ≤ Y₀) :
    T ≤ Subgroup.normalizer (Vtwo e ψ : Set Y) := by
  intro t ht
  refine Vtwo_mem_normalizer hcl (hTY ht) ?_
  have hz : fpsi e ψ (blk1 slZ) ∈ centerOf T := by
    rw [S.center_T]
    exact ⟨ψ (blk1 slZ), psi_spE hψ blk1_slZ_mem_spE, rfl⟩
  exact Subgroup.mem_centralizer_iff.1 hz.2 t ht

omit [Finite Y] [K.Normal] in
theorem Vone_conj_swap : (Vone e ψ).map (MulAut.conj (fpsi e ψ swp)).toMonoidHom = Vtwo e ψ := by
  ext t
  constructor
  · rintro ⟨_, ⟨x, rfl⟩, rfl⟩
    refine ⟨x, ?_⟩
    show fpsi e ψ (blk1 x) = fpsi e ψ swp * fpsi e ψ (blk0 x) * (fpsi e ψ swp)⁻¹
    rw [← map_inv, ← map_mul, ← map_mul, swp_conj_blk0]
  · rintro ⟨x, rfl⟩
    refine ⟨fpsi e ψ (blk0 x), ⟨x, rfl⟩, ?_⟩
    show fpsi e ψ swp * fpsi e ψ (blk0 x) * (fpsi e ψ swp)⁻¹ = fpsi e ψ (blk1 x)
    rw [← map_inv, ← map_mul, ← map_mul, swp_conj_blk0]

omit [Finite Y] [K.Normal] in
theorem Vtwo_conj_swap : (Vtwo e ψ).map (MulAut.conj (fpsi e ψ swp)).toMonoidHom = Vone e ψ := by
  ext t
  constructor
  · rintro ⟨_, ⟨x, rfl⟩, rfl⟩
    refine ⟨x, ?_⟩
    show fpsi e ψ (blk0 x) = fpsi e ψ swp * fpsi e ψ (blk1 x) * (fpsi e ψ swp)⁻¹
    rw [← map_inv, ← map_mul, ← map_mul, swp_conj_blk1]
  · rintro ⟨x, rfl⟩
    refine ⟨fpsi e ψ (blk1 x), ⟨x, rfl⟩, ?_⟩
    show fpsi e ψ swp * fpsi e ψ (blk1 x) * (fpsi e ψ swp)⁻¹ = fpsi e ψ (blk0 x)
    rw [← map_inv, ← map_mul, ← map_mul, swp_conj_blk1]

theorem Sp48Setup.minimal_V (S : Sp48Setup e T y) (hC : Subgroup.centralizer (K : Set Y) = ⊥)
    (hNE : Subgroup.normalizer ((spE.map (emb e) : Subgroup Y) : Set Y) ≤ Y₀)
    (hcl : Y₀.comap (emb e) = (wrp (⊤ : Subgroup Sl28)).map ψ.toMonoidHom)
    {W : Subgroup Y} (hWY : W ≤ Y₀) (hn : Y₀ ≤ Subgroup.normalizer (W : Set Y)) :
    W = ⊥ ∨ Vzero e ψ ≤ W := by
  by_cases hW : W = ⊥
  · exact Or.inl hW
  right
  have hne := S.comap_ne_bot hC hNE hn hW
  have hle : W.comap (fpsi e ψ) ≤ wrp (⊤ : Subgroup Sl28) := by
    intro x hx
    have h1 : ψ x ∈ Y₀.comap (emb e) := hWY hx
    rw [hcl] at h1
    obtain ⟨m, hm, hmx⟩ := h1
    have : m = x := ψ.injective hmx
    rwa [← this]
  have hn2 : ∀ m ∈ wrp (⊤ : Subgroup Sl28), ∀ w ∈ W.comap (fpsi e ψ),
      m * w * m⁻¹ ∈ W.comap (fpsi e ψ) := by
    intro m hm w hw
    show fpsi e ψ (m * w * m⁻¹) ∈ W
    rw [map_mul, map_mul, map_inv]
    exact (Subgroup.mem_normalizer_iff.1 (hn (fpsi_mem_Y₀ hcl hm)) _).1 hw
  have hne2 : W.comap (fpsi e ψ) ≠ ⊥ := by
    intro h2
    apply hne
    rw [eq_bot_iff]
    intro k hk
    have h3 : ψ.symm k ∈ W.comap (fpsi e ψ) := by
      show fpsi e ψ (ψ.symm k) ∈ W
      rw [fpsi_apply, MulEquiv.apply_symm_apply]
      exact hk
    rw [h2, Subgroup.mem_bot] at h3
    have : k = 1 := by
      have := congrArg ψ h3
      simpa using this
    rw [this]
    exact Subgroup.one_mem _
  obtain ⟨h0, h1⟩ := normal_wrp_top hle hn2 hne2
  rintro _ ⟨⟨x, y⟩, rfl⟩
  show fpsi e ψ (blk0 x * blk1 y) ∈ W
  rw [map_mul]
  exact W.mul_mem (h0 x) (h1 y)

omit [Finite Y] in
theorem Sp48Setup.V_centralizer (S : Sp48Setup e T y)
    (hC : Subgroup.centralizer (K : Set Y) = ⊥) (hψ : ∀ x, x ∈ spT0 ↔ ψ x ∈ spT0) :
    Y₀ ⊓ Subgroup.centralizer (Vzero e ψ : Set Y) = ⊥ := by
  rw [eq_bot_iff]
  rintro g ⟨-, hgC⟩
  rw [Subgroup.mem_bot]
  have hgc : ∀ v ∈ Vzero e ψ, v * g = g * v := fun v hv => Subgroup.mem_centralizer_iff.1 hgC v hv
  have hgE : ∀ z ∈ spE.map (emb e), g * z = z * g := by
    rintro _ ⟨s, hs, rfl⟩
    exact (hgc _ (emb_mem_Vzero hψ (spE_le_spT0 hs))).symm
  have hgT : g ∈ T := S.cent_E_le hC hgE
  obtain ⟨k, hk, rfl⟩ := S.cent_T0 hgT fun s hs => (hgc _ (emb_mem_Vzero hψ hs)).symm
  have hu : ψ.symm k ∈ MonoidHom.range blkHom := by
    refine spT0_le_blkRange ?_
    rw [hψ, MulEquiv.apply_symm_apply]
    exact hk
  have hgk : emb e k = fpsi e ψ (ψ.symm k) := by
    rw [fpsi_apply, MulEquiv.apply_symm_apply]
  have h1 : ψ.symm k = 1 := by
    refine blkRange_center hu fun w hw => ?_
    apply fpsi_injective e ψ
    rw [map_mul, map_mul, ← hgk]
    exact (hgc _ (fpsi_mem_Vzero hw)).symm
  rw [hgk, h1, map_one]

omit [K.Normal] in
theorem Sp48Setup.sylow_normal_V (S : Sp48Setup e T y) (hψ : ∀ x, x ∈ spT0 ↔ ψ x ∈ spT0)
    {W : Subgroup Y} (hVW : Vzero e ψ ≤ W) : T ⊓ W = T ⊓ K ∨ T ⊓ W = T := by
  have hTK : T ⊓ K ≤ T ⊓ W := le_inf inf_le_left ((S.TK_le_Vzero hψ).trans hVW)
  have h1 : 3 ^ 4 ∣ Nat.card (T ⊓ W : Subgroup Y) := by
    have := Subgroup.card_dvd_of_le hTK
    rwa [S.card_inf_K] at this
  have h2 : Nat.card (T ⊓ W : Subgroup Y) ∣ 3 ^ 5 := by
    have := Subgroup.card_dvd_of_le (inf_le_left : T ⊓ W ≤ T)
    rwa [S.card_T] at this
  obtain ⟨i, hi, hcard⟩ := (Nat.dvd_prime_pow Nat.prime_three).1 h2
  rw [hcard] at h1
  have h4 : 4 ≤ i := (Nat.pow_dvd_pow_iff_le_right (by norm_num)).1 h1
  have : i = 4 ∨ i = 5 := by omega
  rcases this with rfl | rfl
  · left
    exact (Subgroup.eq_of_le_of_card_ge hTK (by rw [hcard, S.card_inf_K])).symm
  · right
    exact Subgroup.eq_of_le_of_card_ge (inf_le_left : T ⊓ W ≤ T) (by rw [hcard, S.card_T])

end VY

end CFSG.AGLEmbedding.KFactProofs.Sp48
