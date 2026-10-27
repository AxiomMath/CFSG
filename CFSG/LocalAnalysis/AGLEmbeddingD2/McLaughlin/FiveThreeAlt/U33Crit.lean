module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.FiveThreeAlt.SecCrit
public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.OrdinaryProofs.SmallRepIrr
public import CFSG.Quasithin.Background.SmithB42U33
public import CFSG.Quasithin.Background.SmithD37Num
public import CFSG.Quasithin.Background.Harris.G2.U33Setup

public section

namespace CFSG.AGLEmbeddingD2.McLaughlin.FiveThreeAlt

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.B42U33 CFSG.Quasithin.H13
open CFSG.AGLEmbeddingD2.McLaughlin.OrdinaryProofs

variable {V : Type} [CommGroup V] [Finite V]

theorem inf_centralizer_eq_bot (hV : ∀ v : V, v ^ 2 = 1) {G L : Subgroup (MulAut V)}
    (hGN : G ≤ Subgroup.normalizer (L : Set (MulAut V))) (hsq : ∀ y ∈ G, y ^ 2 ∈ L)
    (hZ : Subgroup.center ↥L = ⊥) (hL1 : L ≠ ⊥)
    (hirr : ∀ J : Subgroup V, (∀ g ∈ G, ∀ v ∈ J, g v ∈ J) → J = ⊥ ∨ J = ⊤) :
    G ⊓ Subgroup.centralizer (L : Set (MulAut V)) = ⊥ := by
  set C := G ⊓ Subgroup.centralizer (L : Set (MulAut V)) with hC
  have hC2 : ∀ c ∈ C, c ^ 2 = 1 := by
    intro c hc
    have h1 : c ^ 2 ∈ L := hsq c hc.1
    have h2 : (⟨c ^ 2, h1⟩ : ↥L) ∈ Subgroup.center ↥L := by
      rw [Subgroup.mem_center_iff]
      intro y
      apply Subtype.ext
      have := Subgroup.mem_centralizer_iff.mp (Subgroup.pow_mem _ hc.2 2) y y.2
      exact this
    rw [hZ, Subgroup.mem_bot] at h2
    exact congrArg Subtype.val h2
  have hCp : IsPGroup 2 ↥C := fun c => ⟨1, Subtype.ext (by
    rw [pow_one, Subgroup.coe_pow, Subgroup.coe_one]
    exact hC2 c c.2)⟩
  have hnt : Nontrivial V := by
    obtain ⟨l, hl1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hL1
    have hl1' : (l : MulAut V) ≠ 1 := fun h => hl1 (Subtype.ext h)
    by_contra hcon
    rw [not_nontrivial_iff_subsingleton] at hcon
    exact hl1' (MulEquiv.ext fun v => Subsingleton.elim _ _)
  have h2 := CFSG.Quasithin.SmithD37.two_le_card_fixV hV hCp
  have hinv : ∀ g ∈ G, ∀ v ∈ fixV C, g v ∈ fixV C := by
    intro g hg v hv c hc
    have hc' : g⁻¹ * c * g ∈ C := by
      refine Subgroup.mem_inf.mpr ⟨G.mul_mem (G.mul_mem (G.inv_mem hg) hc.1) hg, ?_⟩
      rw [Subgroup.mem_centralizer_iff]
      intro l hl
      have hgl : g * l * g⁻¹ ∈ L := (Subgroup.mem_normalizer_iff.mp (hGN hg) l).mp hl
      have h3 := Subgroup.mem_centralizer_iff.mp hc.2 _ hgl
      calc l * (g⁻¹ * c * g) = g⁻¹ * ((g * l * g⁻¹) * c) * g := by group
        _ = g⁻¹ * (c * (g * l * g⁻¹)) * g := by rw [h3]
        _ = g⁻¹ * c * g * l := by group
    have h4 := hv _ hc'
    have e : c (g v) = g ((g⁻¹ * c * g) v) := by
      simp only [MulAut.mul_apply, MulAut.inv_apply, MulEquiv.apply_symm_apply]
    rw [e, h4]
  rcases hirr (fixV C) hinv with h | h
  · exfalso
    rw [h, Subgroup.card_bot] at h2
    omega
  · rw [eq_bot_iff]
    intro c hc
    rw [Subgroup.mem_bot]
    refine MulEquiv.ext fun v => ?_
    have hv : v ∈ fixV C := h ▸ Subgroup.mem_top v
    exact hv c hc

omit [Finite V] in
theorem fixV_eq_bot_of_irr {G L : Subgroup (MulAut V)}
    (hGN : G ≤ Subgroup.normalizer (L : Set (MulAut V))) (hL1 : L ≠ ⊥)
    (hirr : ∀ J : Subgroup V, (∀ g ∈ G, ∀ v ∈ J, g v ∈ J) → J = ⊥ ∨ J = ⊤) : fixV L = ⊥ := by
  have hinv : ∀ g ∈ G, ∀ v ∈ fixV L, g v ∈ fixV L := by
    intro g hg v hv l hl
    have hl' : g⁻¹ * l * g ∈ L := by
      have := (Subgroup.mem_normalizer_iff.mp (hGN (G.inv_mem hg)) l).mp hl
      simpa using this
    have h4 := hv _ hl'
    have e : l (g v) = g ((g⁻¹ * l * g) v) := by
      simp only [MulAut.mul_apply, MulAut.inv_apply, MulEquiv.apply_symm_apply]
    rw [e, h4]
  rcases hirr (fixV L) hinv with h | h
  · exact h
  · exfalso
    apply hL1
    rw [eq_bot_iff]
    intro l hl
    rw [Subgroup.mem_bot]
    refine MulEquiv.ext fun v => ?_
    have hv : v ∈ fixV L := h ▸ Subgroup.mem_top v
    exact hv l hl

section U33


omit [Finite V] in
theorem exists_embedding' {G L : Subgroup (MulAut V)} (hLG : L ≤ G)
    (hGN : G ≤ Subgroup.normalizer (L : Set (MulAut V)))
    (hCL : G ⊓ Subgroup.centralizer (L : Set (MulAut V)) ≤ L) (hP : B42TypeU33 ↥L) :
    ∃ ψ : ↥G →* ↥(quasithinG2 (ZMod 2)), Function.Injective ψ ∧
      (∀ g : ↥G, (g : MulAut V) ∈ L → ψ g ∈ g2Derived (ZMod 2)) ∧
      ∀ δ ∈ g2Derived (ZMod 2), ∃ g : ↥G, (g : MulAut V) ∈ L ∧ ψ g = δ := by
  have hL'n : (L.subgroupOf G).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hLG).2 hGN
  obtain ⟨θ⟩ := nonempty_equiv_g2Derived hP
  let θ' : ↥(L.subgroupOf G) ≃* ↥(g2Derived (ZMod 2)) :=
    (Subgroup.subgroupOfEquivOfLe hLG).trans θ
  refine ⟨embG conjNormal_bijective θ', ?_, fun g hg => ?_, fun δ hδ => ?_⟩
  · rw [injective_iff_map_eq_one]
    intro g hg
    have hc := embG_eq_one conjNormal_bijective θ' hg
    have hcomm : ∀ x ∈ L, x * (g : MulAut V) = (g : MulAut V) * x := by
      intro x hx
      have h1 := congrArg Subtype.val (hc ⟨x, hLG hx⟩ hx)
      change (g : MulAut V) * x * (g : MulAut V)⁻¹ = x at h1
      calc x * (g : MulAut V) = (g : MulAut V) * x * (g : MulAut V)⁻¹ * g := by rw [h1]
        _ = (g : MulAut V) * x := by group
    have hgL : (g : MulAut V) ∈ L :=
      hCL ⟨g.2, Subgroup.mem_centralizer_iff.2 fun x hx => hcomm x hx⟩
    have hgZ : (⟨g, hgL⟩ : ↥L) ∈ Subgroup.center ↥L := by
      rw [Subgroup.mem_center_iff]
      intro y
      exact Subtype.ext (hcomm y y.2)
    rw [hP.1, Subgroup.mem_bot] at hgZ
    have h1 : (g : MulAut V) = 1 := congrArg (fun y : ↥L => (y : MulAut V)) hgZ
    exact Subtype.ext h1
  · have := embG_coe conjNormal_bijective θ' ⟨g, hg⟩
    rw [this]
    exact (θ' _).2
  · refine ⟨θ'.symm ⟨δ, hδ⟩, (θ'.symm ⟨δ, hδ⟩).2, ?_⟩
    rw [embG_coe conjNormal_bijective, MulEquiv.apply_symm_apply]

omit [Finite V] in
theorem short_generation' {G L : Subgroup (MulAut V)} (hLG : L ≤ G)
    (hGN : G ≤ Subgroup.normalizer (L : Set (MulAut V)))
    (hCL : G ⊓ Subgroup.centralizer (L : Set (MulAut V)) ≤ L) (hP : B42TypeU33 ↥L)
    {A : Subgroup (MulAut V)} (hAG : A ≤ G) (hA1 : A ≠ ⊥) (hAe : IsElemAbelian2 A) :
    ∃ r m : ℕ, Nat.card A = 2 ^ r ∧ 1 ≤ r ∧ r ≤ 3 ∧ m * r ≤ 6 ∧
      ∃ l : Fin m → MulAut V, (∀ i, l i ∈ L) ∧
        L ≤ Subgroup.closure (⋃ i, ((A.map (MulAut.conj (l i)).toMonoidHom :
          Subgroup (MulAut V)) : Set (MulAut V))) := by
  obtain ⟨ψ, hψ, hψL, hψD⟩ := exists_embedding' hLG hGN hCL hP
  set A' : Subgroup ↥G := A.subgroupOf G with hA'
  set B : Subgroup ↥(quasithinG2 (ZMod 2)) := A'.map ψ with hBdef
  have hB1 : B ≠ ⊥ := by
    intro h
    apply hA1
    rw [eq_bot_iff]
    intro a ha
    have h1 : ψ ⟨a, hAG ha⟩ ∈ B := ⟨⟨a, hAG ha⟩, ha, rfl⟩
    rw [h, Subgroup.mem_bot, ← map_one ψ] at h1
    rw [Subgroup.mem_bot]
    exact congrArg Subtype.val (hψ h1)
  have hBc : ∀ a ∈ B, ∀ b ∈ B, a * b = b * a := by
    rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (hAe.1 _ ha _ hb)
  have hB2 : ∀ b ∈ B, b ^ 2 = 1 := by
    rintro _ ⟨a, ha, rfl⟩
    rw [← map_pow, ← map_one ψ]
    congr 1
    exact Subtype.ext (hAe.2 _ ha)
  obtain ⟨r, m, hr, hr1, hr3, hmr, d, hd, hle⟩ := shortGen hB1 hBc hB2
  choose l hlL hld using fun i => hψD (d i) (hd i)
  refine ⟨r, m, ?_, hr1, hr3, hmr, fun i => (l i : MulAut V), hlL, ?_⟩
  · rw [← hr, hBdef, Subgroup.card_map_of_injective hψ]
    exact (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAG).toEquiv).symm
  · have hmap : ∀ i, B.map (MulAut.conj (d i)).toMonoidHom =
        (A'.map (MulAut.conj (l i)).toMonoidHom).map ψ := by
      intro i
      rw [hBdef, Subgroup.map_map, Subgroup.map_map]
      congr 1
      refine MonoidHom.ext fun a => ?_
      simp only [MonoidHom.coe_comp, Function.comp_apply, MulEquiv.coe_toMonoidHom,
        MulAut.conj_apply, map_mul, map_inv, ← hld i]
    intro y hy
    have hy' := hle (hψL ⟨y, hLG hy⟩ hy)
    simp only [hmap, Subgroup.coe_map] at hy'
    rw [← Set.image_iUnion, ← MonoidHom.map_closure] at hy'
    · obtain ⟨z, hz, hzy⟩ := hy'
      have hzy' : z = ⟨y, hLG hy⟩ := hψ hzy
      have h1 := Subgroup.mem_map_of_mem G.subtype hz
      rw [MonoidHom.map_closure, hzy'] at h1
      refine Subgroup.closure_mono ?_ h1
      rintro _ ⟨x, hx, rfl⟩
      obtain ⟨i, hi⟩ := Set.mem_iUnion.1 hx
      obtain ⟨a, ha, rfl⟩ := hi
      exact Set.mem_iUnion.2 ⟨i, ⟨(a : MulAut V), ha, rfl⟩⟩


theorem u33_secCrit {K : Type} [Group K] (hKs : IsSimpleGroup K)
    (hK : CFSG.Assembly.LowTwoRank.StatedClassicalModel K .PSU 3 3 1) :
    SecCrit K (· = 2 ^ 6) := by
  intro V _ _ hV G L B ⟨eL⟩ hLG hGN hBG hGeq hsq hB1 hBe hBq hirr hoff
  have hLs : IsSimpleGroup ↥L := eL.isSimpleGroup
  have hP : B42TypeU33 ↥L :=
    G11.Harris.G2.b42TypeU33_of_simple hLs (G11.Harris.G2.statedModel_of_equiv eL.symm hK)
  have hL6048 : Nat.card ↥L = 6048 := card_of_b42TypeU33 hP
  have hL1 : L ≠ ⊥ := by
    intro h
    rw [h, Subgroup.card_bot] at hL6048
    omega
  have hCL : G ⊓ Subgroup.centralizer (L : Set (MulAut V)) ≤ L := by
    rw [inf_centralizer_eq_bot hV hGN hsq hP.1 hL1 hirr]
    exact bot_le
  have hfixL : fixV L = ⊥ := fixV_eq_bot_of_irr hGN hL1 hirr
  obtain ⟨r, m, hr, -, -, hmr, l, -, hle⟩ := short_generation' hLG hGN hCL hP hBG hB1 hBe
  have h1 := HatA6.card_le_pow_of_le_closure hfixL l hle
  have hidx : (fixV B).index ≤ Nat.card B := by
    have e := (fixV B).card_mul_index
    have hpos : 0 < Nat.card (fixV B) := Nat.card_pos
    rw [← e, mul_comm (Nat.card B)] at hoff
    exact Nat.le_of_mul_le_mul_left hoff hpos
  have hup : Nat.card V ≤ 2 ^ 6 := by
    refine h1.trans ((Nat.pow_le_pow_left hidx m).trans ?_)
    rw [hr, ← pow_mul]
    exact Nat.pow_le_pow_right (by norm_num) (by rw [mul_comm]; exact hmr)
  obtain ⟨k, hk⟩ := natCard_eq_two_pow_of_exponent_two V hV
  have hk6 : k ≤ 6 := by
    rw [hk] at hup
    exact (Nat.pow_le_pow_iff_right (by norm_num)).1 hup
  have h6 := six_le_of_card_dvd hV hk L hL6048
  have hcard : Nat.card V = 2 ^ 6 := by rw [hk, show k = 6 by omega]
  obtain ⟨e, hLe⟩ := exists_equiv_of_g2NaturalDerived (u33SixNatural V hV hcard L hP)
  set φ := (MulAut.congr e).toMonoidHom with hφ
  have hφinj : Function.Injective φ := (MulAut.congr e).injective
  have hGimg : ∀ x ∈ G, MulAut.congr e x ∈ (g2QAct (ZMod 2)).range := by
    intro x hx
    refine normalizer_two_Q _ fun h => ?_
    obtain ⟨h', rfl⟩ := (MulAut.congr e).surjective h
    have hxN := Subgroup.mem_normalizer_iff.1 (hGN hx) h'
    rw [← hLe, ← map_inv, ← map_mul, ← map_mul]
    change φ h' ∈ L.map φ ↔ φ (x * h' * x⁻¹) ∈ L.map φ
    rw [Subgroup.mem_map_iff_mem hφinj, Subgroup.mem_map_iff_mem hφinj]
    exact hxN
  have hB8 : Nat.card B = 8 ∧ Nat.card (fixV B) = 8 := by
    have hle' : B.map φ ≤ (g2QAct (ZMod 2)).range := by
      rintro _ ⟨b, hb, rfl⟩
      exact hGimg b (hBG hb)
    have hne : B.map φ ≠ ⊥ := fun h =>
      hB1 ((Subgroup.map_eq_bot_iff_of_injective _ hφinj).1 h)
    have hcardB : Nat.card (B.map φ) = Nat.card B := Subgroup.card_map_of_injective hφinj
    have hfix : Nat.card (fixV (B.map φ)) = Nat.card (fixV B) := by
      rw [hφ, H13.fixV_map_congr e, Subgroup.card_map_of_injective (f := e.toMonoidHom) e.injective]
    have hff : Nat.card ModQ ≤ Nat.card (B.map φ) * Nat.card (fixV (B.map φ)) := by
      rw [hcardB, hfix, ← Nat.card_congr e.toEquiv]
      exact hoff
    have h := offender_exact hle' hne (H13.isElemAbelian2_map_congr e hBe) hff
    rwa [hcardB, hfix] at h
  refine ⟨fun J hJ => ?_, ?_, hcard⟩
  ·
    have hnc : ∃ x ∈ L, ∃ y ∈ L, x * y ≠ y * x := by
      by_contra hcon
      push Not at hcon
      let _ : CommGroup ↥L :=
        { (inferInstance : Group ↥L) with
          mul_comm := fun a b => Subtype.ext (hcon a a.2 b b.2) }
      have := IsSimpleGroup.prime_card (α := ↥L)
      rw [hL6048] at this
      exact absurd this (by norm_num)
    refine eq_bot_or_eq_top_of_small hV hnc (fun J _ _ hJ2 hJc φ' => ?_) J hJ
    rw [hcard] at hJc
    exact trivial_of_card_lt_two_pow_six hL6048 J hJ2 hJc φ'
  · rw [hB8.1, hB8.2, hcard]
    norm_num

end U33

end CFSG.AGLEmbeddingD2.McLaughlin.FiveThreeAlt
