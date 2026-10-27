module

public import CFSG.Quasithin.EmptyFaithful.S152Y29
public import CFSG.GH74.QTGen4.DCopy.Quasithin.EmptyFaithful.S152Y27

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType
open scoped commutatorElement

namespace S152Y

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G] {T Mc M : Subgroup G}

theorem exists_Y1_of_line_F4 (hs : Setting152 T Mc M) (h : Data T Mc M) (h5 : StageLemma15205_F4)
    (hexp : ∀ x ∈ Ys T Mc M, x ^ 3 = 1) {A₀ : Subgroup (MulAut (V154 T Mc M))}
    (hA₀Y : A₀ ≤ autOn (yOf152 T Mc M) (V154 T Mc M)) (hcard : Nat.card A₀ = 3)
    (hinvT : ∀ t ∈ autOn T (V154 T Mc M), ∀ a ∈ A₀, t * a * t⁻¹ ∈ A₀)
    (hact : ∃ r ∈ autOn (rcOf Mc M) (V154 T Mc M), ∃ a ∈ A₀, r * a * r⁻¹ ≠ a)
    (hRe : ∀ x ∈ autOn (rcOf Mc M) (V154 T Mc M), x * x = 1) :
    ∃ Y₁ : Subgroup G, IsY1 T Mc M Y₁ := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hA₀cyc : IsCyclic ↥A₀ := isCyclic_of_prime_card hcard

  set Ks : Subgroup (OTwoQuot M) := Ys T Mc M ⊓ (piStar h).ker with hKs
  set Ws : Subgroup (OTwoQuot M) := Ys T Mc M ⊓ A₀.comap (piStar h) with hWs
  have hKW : Ks ≤ Ws := by
    intro u hu
    refine ⟨hu.1, ?_⟩
    show piStar h u ∈ A₀
    rw [MonoidHom.mem_ker.mp hu.2]
    exact A₀.one_mem
  have hKcentral : ∀ k ∈ Ks, ∀ x ∈ Ys T Mc M, x * k = k * x := fun k hk x hx =>
    Data.K_central h k hk x (Data.Ys_le_Ls h hx)
  have hWY : Ws ≤ Ys T Mc M := fun u hu => hu.1
  have hWab : ∀ x ∈ Ws, ∀ y ∈ Ws, x * y = y * x := by
    let f : ↥Ws →* ↥A₀ :=
      MonoidHom.codRestrict ((piStar h).comp Ws.subtype) A₀ (fun u => u.2.2)
    have hf : f.ker ≤ Subgroup.center ↥Ws := by
      intro u hu
      rw [Subgroup.mem_center_iff]
      intro g
      have hu1 : piStar h (u : OTwoQuot M) = 1 := congrArg Subtype.val (MonoidHom.mem_ker.mp hu)
      have hmem : (u : OTwoQuot M) ∈ Ks := ⟨hWY u.2, hu1⟩
      exact Subtype.ext (hKcentral _ hmem (g : OTwoQuot M) (hWY g.2))
    intro a ha b hb
    have : IsMulCommutative ↥Ws := MonoidHom.isMulCommutative_of_isCyclic_of_ker_le_center f hf
    exact congrArg Subtype.val (mul_comm' (⟨a, ha⟩ : ↥Ws) ⟨b, hb⟩)

  have hTsY : imageOTwoQuot M T ≤ Subgroup.normalizer (Ys T Mc M : Set (OTwoQuot M)) :=
    imageOTwoQuot_le_normalizer (T_le_normalizer_yOf T Mc M)
  have hTsK : imageOTwoQuot M T ≤ Subgroup.normalizer (Ks : Set (OTwoQuot M)) := by
    intro u hu
    exact Subgroup.inf_normalizer_le_normalizer_inf ⟨hTsY hu, Subgroup.le_normalizer_of_normal hu⟩
  have hTsW : imageOTwoQuot M T ≤ Subgroup.normalizer (Ws : Set (OTwoQuot M)) := by
    intro u hu
    refine A4.mem_normalizer_of_conj_mem fun w hw => ?_
    refine ⟨(Subgroup.mem_normalizer_iff.mp (hTsY hu) w).mp hw.1, ?_⟩
    show piStar h (u * w * u⁻¹) ∈ A₀
    rw [map_mul, map_mul, map_inv]
    have hπu : piStar h u ∈ autOn T (V154 T Mc M) := by
      rw [← map_piStar_imageOTwoQuot h h.T_le]
      exact ⟨u, hu, rfl⟩
    exact hinvT _ hπu _ hw.2
  have hT2G : IsPGroup 2 T := (isSylowTwoOf_of_le151 h.qtfe.sylow h.T_le).2.1
  have hTs2 : IsPGroup 2 (imageOTwoQuot M T) := imageOTwoQuot_isPGroup h.T_le hT2G

  obtain ⟨W', -, hW'W, hTsW', hsup, hinf⟩ := B6.exists_isCompl_of_coprime_section (p := 3)
    (by norm_num) (K := Ws) (Φ := ⊥) (W := Ks) (T := imageOTwoQuot M T) bot_le hKW
    (fun x hx => by rw [hexp x (hWY hx)]; exact Subgroup.one_mem _)
    (by
      rw [Subgroup.commutator_le]
      intro a ha b hb
      rw [Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm]
      exact hWab a ha b hb)
    hTsW (Subgroup.le_normalizer_of_normal) hTsK hTs2
  have hW'Ys : W' ≤ Ys T Mc M := hW'W.trans hWY
  have hW'odd : ∀ u ∈ W', Odd (orderOf u) := fun u hu =>
    Odd.of_dvd_nat (by decide) (orderOf_dvd_of_pow_eq_one (hexp u (hW'Ys hu)))

  obtain ⟨Y₀, hY₀⟩ : ∃ Y₀ : Subgroup G, Y₀ = yOf152 T Mc M ⊓ starPre M W' := ⟨_, rfl⟩
  obtain ⟨Y₁, hY₁⟩ : ∃ Y₁ : Subgroup G, Y₁ = oTwoUpper Y₀ := ⟨_, rfl⟩
  have hY₀Y : Y₀ ≤ yOf152 T Mc M := by rw [hY₀]; exact inf_le_left
  have hY₀M : Y₀ ≤ M := hY₀Y.trans h.yOf_le_M
  have hY₁Y₀ : Y₁ ≤ Y₀ := by rw [hY₁]; exact oTwoUpper_le _
  have hY₁Y : Y₁ ≤ yOf152 T Mc M := hY₁Y₀.trans hY₀Y
  have hY₁M : Y₁ ≤ M := hY₁Y.trans h.yOf_le_M
  have himg₀ : imageOTwoQuot M Y₀ = W' := by
    rw [hY₀, imageOTwoQuot_inf_starPre]
    exact inf_eq_right.mpr hW'Ys
  have himg₁ : imageOTwoQuot M Y₁ = W' := by
    rw [hY₁, imageOTwoQuot_oTwoUpper hY₀M, himg₀]
    exact oTwoUpper_eq_self_of_odd hW'odd
  have hTY₀ : T ≤ Subgroup.normalizer (Y₀ : Set G) := by
    rw [hY₀]
    intro t ht
    exact Subgroup.inf_normalizer_le_normalizer_inf
      ⟨T_le_normalizer_yOf T Mc M ht, le_normalizer_starPre h.T_le hTsW' ht⟩
  have hTY₁ : T ≤ Subgroup.normalizer (Y₁ : Set G) := by
    rw [hY₁]
    exact hTY₀.trans (normalizer_le_normalizer_oTwoUpper _)
  have hRY₁ : rcOf Mc M ≤ Subgroup.normalizer (Y₁ : Set G) := h.rc_le_T.trans hTY₁
  have hK : imageOTwoQuot M Y₁ ⊓ (piStar h).ker = ⊥ := by
    rw [himg₁, eq_bot_iff]
    intro u hu
    have : u ∈ Ks ⊓ W' := ⟨⟨hW'Ys hu.1, hu.2⟩, hu.1⟩
    rw [hinf] at this
    exact this
  have hodd : ∀ u ∈ imageOTwoQuot M Y₁, Odd (orderOf u) := by
    rw [himg₁]
    exact hW'odd

  have hW'normK : W' ≤ Subgroup.normalizer (Ks : Set (OTwoQuot M)) := by
    intro w hw
    refine A4.mem_normalizer_of_conj_mem fun k hk => ?_
    have := hKcentral k hk w (hW'Ys hw)
    have h2 : w * k * w⁻¹ = k := by
      calc w * k * w⁻¹ = k * w * w⁻¹ := by rw [this]
        _ = k := by group
    rw [h2]
    exact hk
  have hautY₁ : autOn Y₁ (V154 T Mc M) = A₀ := by
    rw [← map_piStar_imageOTwoQuot h hY₁M, himg₁]
    apply le_antisymm
    · rintro _ ⟨u, hu, rfl⟩
      exact (hW'W hu).2
    · intro a₀ ha₀
      have hmem : a₀ ∈ (Ys T Mc M).map (piStar h) := by
        rw [h.map_Ys]
        exact hA₀Y ha₀
      obtain ⟨u, hu, rfl⟩ := hmem
      have huW : u ∈ Ws := ⟨hu, ha₀⟩
      rw [← hsup, sup_comm] at huW
      have hmul := Subgroup.coe_mul_of_left_le_normalizer_right W' Ks hW'normK
      have huW' : u ∈ ((W' ⊔ Ks : Subgroup (OTwoQuot M)) : Set (OTwoQuot M)) := huW
      rw [hmul] at huW'
      obtain ⟨w, hw, k, hk, rfl⟩ := Set.mem_mul.mp huW'
      refine ⟨w, hw, ?_⟩
      have hk1 : piStar h k = 1 := MonoidHom.mem_ker.mp hk.2
      rw [map_mul, hk1, mul_one]
  have hcardY₁ : Nat.card (autOn Y₁ (V154 T Mc M)) = 3 := by
    rw [hautY₁]
    exact hcard
  have hactY₁ : ∃ r ∈ autOn (rcOf Mc M) (V154 T Mc M), ∃ a ∈ autOn Y₁ (V154 T Mc M),
      r * a * r⁻¹ ≠ a := by
    rw [hautY₁]
    exact hact
  obtain ⟨e⟩ := quot_dihedral_of_star h hY₁M hRY₁ (p := 3) (by norm_num) hK hcardY₁ hRe hactY₁
  obtain ⟨d⟩ := S152N2.nonempty_d3_equiv_perm
  have hunique := isUniqueM_of_five_F4 h h5 hs hY₁M
    (not_le_Mc hRY₁ hodd (exists_nontrivial_action h hY₁M hactY₁))
  exact ⟨Y₁, isY1_of_star h hY₁Y hTY₁ (by rw [hY₁]; exact (A4.oTwoUpper_oTwoUpper Y₀).symm)
    (Or.inl ⟨e.trans d⟩) hK hodd hunique⟩

end S152Y

end CFSG.Quasithin
