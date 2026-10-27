module

public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_15Setup

public section

namespace CFSG.QuasithinUnique.Unc25K1

open CFSG.Open CFSG.Quasithin

section Generic

variable {G : Type*} [Group G]

theorem card_eq_card_range_mul_card_ker {A B : Type*} [Group A] [Group B] (f : A →* B) :
    Nat.card A = Nat.card f.range * Nat.card f.ker := by
  rw [Subgroup.card_eq_card_quotient_mul_card_subgroup f.ker,
    Nat.card_congr (QuotientGroup.quotientKerEquivRange f).toEquiv]

theorem card_le_two_of_forall_eq [Finite G] {B : Subgroup G} {a : G}
    (h : ∀ b ∈ B, b = 1 ∨ b = a) : Nat.card B ≤ 2 := by
  have h1 : Nat.card B ≤ Nat.card ({1, a} : Set G) := by
    apply Nat.card_le_card_of_injective
      (fun b : B => (⟨(b : G), by simpa using h b b.2⟩ : ({1, a} : Set G)))
    intro x y hxy
    have := congrArg Subtype.val hxy
    exact Subtype.ext this
  refine h1.trans ?_
  rw [Nat.card_coe_set_eq]
  exact (Set.ncard_insert_le _ _).trans (by simp)

theorem mem_normalizer_sup [Finite G] {A B : Subgroup G} {g : G}
    (hA : g ∈ Subgroup.normalizer (A : Set G)) (hB : g ∈ Subgroup.normalizer (B : Set G)) :
    g ∈ Subgroup.normalizer ((A ⊔ B : Subgroup G) : Set G) := by
  rw [Subgroup.sup_eq_closure]
  apply normalizer_closure_of_forall
  intro y hy
  apply Subgroup.subset_closure
  rcases hy with hy | hy
  · exact Or.inl ((Subgroup.mem_normalizer_iff.mp hA y).mp hy)
  · exact Or.inr ((Subgroup.mem_normalizer_iff.mp hB y).mp hy)

end Generic

section Config

variable {G : Type} [Group G] [Finite G] {T M : Subgroup G} {hs : UnconstrainedSetting G T M}
  (N : Notation25 hs) {t zK : G}

theorem isPGroup_T (hs : UnconstrainedSetting G T M) : IsPGroup 2 T :=
  hs.setting.isSylowTwoOf_M.isPGroup

theorem exists_SK_mul_centralizes (h : Lv2513 N t zK) (F : K33Facts N.K)
    (hKt : Subgroup.centralizer ({t} : Set G) ≤ Subgroup.normalizer (N.K : Set G)) {g : G}
    (hg : g ∈ T ⊓ Subgroup.normalizer (N.S : Set G)) :
    ∃ s ∈ N.SK, ∀ v ∈ threeCoreCent N.K zK, (s⁻¹ * g) * v = v * (s⁻¹ * g) := by
  classical
  have hf := h.facts2511
  have hzKK : zK ∈ N.K := zK_mem_K N h F
  have hKz := F.inv zK hzKK (zK_ne_one N hf) (by rw [sq]; exact zK_mul_self N hf)
  have hQeq : Kz N.S = threeCoreCent N.K zK := Kz_eq N h F hKt
  set Q₀ : Subgroup G := threeCoreCent N.K zK with hQ₀
  have hPQ : ∀ y ∈ T ⊓ Subgroup.normalizer (N.S : Set G),
      y ∈ Subgroup.normalizer (Q₀ : Set G) := by
    intro y hy
    rw [← hQeq]
    exact mem_normalizer_Kz hy.2
  set P : Subgroup G := T ⊓ Subgroup.normalizer (N.S : Set G) with hP
  have hP2 : IsPGroup 2 P := (isPGroup_T hs).to_le inf_le_left
  let ρP : ↥P →* MulAut ↥Q₀ := (conjAct Q₀).comp (Subgroup.inclusion (fun y hy => hPQ y hy))
  have hSKP : N.SK ≤ P := fun s hs' =>
    ⟨N.S_le_T (N.SK_le_S hs'), Subgroup.le_normalizer (N.SK_le_S hs')⟩
  let ρS : ↥N.SK →* MulAut ↥Q₀ := ρP.comp (Subgroup.inclusion hSKP)
  have hrange : ρS.range ≤ ρP.range := by
    rintro _ ⟨s, rfl⟩
    exact ⟨Subgroup.inclusion hSKP s, rfl⟩
  have hP8 : Nat.card ρP.range ≤ 8 :=
    hKz.aut ρP.range (IsPGroup.of_surjective hP2 ρP.rangeRestrict ρP.rangeRestrict_surjective)
  have hSK16 : Nat.card N.SK = 16 := by
    rw [N.SK_sylow.card_eq]
    rcases F.card with hc | hc
    · exact twoPart_eq_sixteen (b := 351) (by norm_num) (by rw [hc])
    · exact twoPart_eq_sixteen (b := 495) (by norm_num) (by rw [hc])
  have hker : Nat.card ρS.ker ≤ 2 := by
    have hzSK : zK ∈ N.SK := ⟨(zK_mem_center N hf).1, hzKK⟩
    refine card_le_two_of_forall_eq (a := (⟨zK, hzSK⟩ : ↥N.SK)) ?_
    intro b hb
    have hb1 : ρS b = 1 := hb
    have hcomm : ∀ v ∈ Q₀, (b : G) * v = v * (b : G) := by
      intro v hv
      have h1 := congrArg (fun φ : MulAut ↥Q₀ => ((φ ⟨v, hv⟩ : ↥Q₀) : G)) hb1
      have h2 : (b : G) * v * (b : G)⁻¹ = v := h1
      calc (b : G) * v = ((b : G) * v * (b : G)⁻¹) * b := by group
        _ = v * b := by rw [h2]
    rcases hKz.centralizer (b : G) (N.SK_le_K b.2) hcomm with h1 | h1
    · exact Or.inl (Subtype.ext h1)
    · exact Or.inr (Subtype.ext h1)
  have hcardSK := card_eq_card_range_mul_card_ker ρS
  have hrange8 : 8 ≤ Nat.card ρS.range := by
    rw [hSK16] at hcardSK
    by_contra hlt
    have h7 : Nat.card ρS.range ≤ 7 := by omega
    have : Nat.card ρS.range * Nat.card ρS.ker ≤ 7 * 2 := Nat.mul_le_mul h7 hker
    omega
  have hreq : ρS.range = ρP.range := Subgroup.eq_of_le_of_card_ge hrange (by omega)
  let gP : ↥P := ⟨g, hg⟩
  have hmem : ρP gP ∈ ρS.range := by
    rw [hreq]
    exact ⟨gP, rfl⟩
  obtain ⟨s, hsg⟩ := hmem
  refine ⟨(s : G), s.2, ?_⟩
  intro v hv
  have h1 := congrArg (fun φ : MulAut ↥Q₀ => ((φ ⟨v, hv⟩ : ↥Q₀) : G)) hsg
  have h2 : (s : G) * v * (s : G)⁻¹ = g * v * g⁻¹ := h1
  calc (s : G)⁻¹ * g * v = (s : G)⁻¹ * (g * v * g⁻¹) * g := by group
    _ = (s : G)⁻¹ * ((s : G) * v * (s : G)⁻¹) * g := by rw [h2]
    _ = v * ((s : G)⁻¹ * g) := by group

theorem xprime_sq_mem {s : G} (hs' : s ∈ N.S) : (s⁻¹ * N.x) ^ 2 ∈ N.S := by
  have hxN : N.x ∈ Subgroup.normalizer (N.S : Set G) := N.x_mem.2
  have h1 : N.x * s⁻¹ * N.x⁻¹ ∈ N.S :=
    (Subgroup.mem_normalizer_iff.mp hxN _).mp (N.S.inv_mem hs')
  have h2 : (s⁻¹ * N.x) ^ 2 = s⁻¹ * (N.x * s⁻¹ * N.x⁻¹) * N.x ^ 2 := by
    simp only [sq]
    group
  rw [h2]
  exact N.S.mul_mem (N.S.mul_mem (N.S.inv_mem hs') h1) N.x_sq

theorem exists_xprime (h : Lv2513 N t zK) (F : K33Facts N.K)
    (hKt : Subgroup.centralizer ({t} : Set G) ≤ Subgroup.normalizer (N.K : Set G)) :
    ∃ x' : G, x' ∈ T ⊓ Subgroup.normalizer (N.S : Set G) ∧ x' ∉ N.S ∧ x' ^ 2 ∈ N.S ∧
      ∀ v ∈ threeCoreCent N.K zK, x' * v = v * x' := by
  obtain ⟨s, hs', hc⟩ := exists_SK_mul_centralizes N h F hKt N.x_mem
  have hsP : s ∈ T ⊓ Subgroup.normalizer (N.S : Set G) :=
    ⟨N.S_le_T (N.SK_le_S hs'), Subgroup.le_normalizer (N.SK_le_S hs')⟩
  refine ⟨s⁻¹ * N.x, (T ⊓ Subgroup.normalizer (N.S : Set G)).mul_mem
    ((T ⊓ Subgroup.normalizer (N.S : Set G)).inv_mem hsP) N.x_mem, ?_,
    xprime_sq_mem N (N.SK_le_S hs'), hc⟩
  intro hS'
  apply N.x_not_mem
  have : N.x = s * (s⁻¹ * N.x) := by group
  rw [this]
  exact N.S.mul_mem (N.SK_le_S hs') hS'

omit [Finite G] in
theorem isUStarPair_conjugate {M H U HU : Subgroup G} {g : G} (hgM : g ∈ M) (hgH : g ∈ H)
    (h : IsUStarPair M H U HU) :
    IsUStarPair M H (CFSG.conjugate U g) (CFSG.conjugate HU g) := by
  have hf : M.map (MulAut.conj g⁻¹).toMonoidHom = M := map_conj_eq_self_of_mem (M.inv_mem hgM)
  have hfH : H.map (MulAut.conj g⁻¹).toMonoidHom = H := map_conj_eq_self_of_mem (H.inv_mem hgH)
  have hf' := map_symm_eq_self_of_map_eq_self hf
  refine ⟨⟨h.1.1.map_equiv hf, ?_⟩, ?_⟩
  · rw [← hfH]
    exact Subgroup.map_mono h.1.2
  · intro V hV
    calc Nat.card V = Nat.card (V.map (MulAut.conj g⁻¹).symm.toMonoidHom) :=
          (card_map_equiv _ V).symm
      _ ≤ Nat.card U := h.2 _ (hV.map_equiv hf')
      _ = Nat.card (U.map (MulAut.conj g⁻¹).toMonoidHom) := (card_map_equiv _ U).symm

theorem exists_ustarPair_le_S :
    ∃ U HU : Subgroup G, IsUStarPair M N.H U HU ∧ U ≤ N.S := by
  obtain ⟨⟨-, U₀, HU₀, hwit, hHU₀, hmax⟩, -⟩ := N.gammaU
  have hpair₀ : IsUStarPair M N.H U₀ HU₀ := ⟨⟨hwit, hHU₀⟩, hmax⟩
  have hU₀HM : U₀ ≤ N.H ⊓ M := le_inf (hwit.2.1.trans hHU₀) hwit.1.1
  obtain ⟨S', hU₀S', hS'⟩ := exists_isSylowTwoOf_of_le hU₀HM hwit.1.2.2.1
  obtain ⟨m, hm, hS'm⟩ := N.tuple.sylow_inf.exists_conj hS'
  refine ⟨CFSG.conjugate U₀ m, CFSG.conjugate HU₀ m, isUStarPair_conjugate hm.2 hm.1 hpair₀, ?_⟩
  have hsymm : (MulAut.conj m).symm = MulAut.conj m⁻¹ := by
    ext x
    simp [MulAut.conj_symm_apply]
  calc U₀.map (MulAut.conj m⁻¹).toMonoidHom ≤ S'.map (MulAut.conj m⁻¹).toMonoidHom :=
        Subgroup.map_mono hU₀S'
    _ = N.S := by
      rw [hS'm, ← hsymm]
      exact map_equiv_symm_map_equiv _ _

theorem false_of_normalizes (h : Lv2513 N t zK) (F : K33Facts N.K) {U HU E : Subgroup G}
    (hpair : IsUStarPair M N.H U HU) (hUS : U ≤ N.S)
    (hHU : HU = N.H ⊓ Subgroup.normalizer (E : Set G))
    (hU : U = N.S ⊓ Subgroup.normalizer (E : Set G)) (hESK : E ≤ N.SK) (hzE : N.z ∈ E)
    {x' : G} (hx' : x' ∈ T ⊓ Subgroup.normalizer (N.S : Set G)) (hx'S : x' ∉ N.S)
    (htx : x'⁻¹ * t * x' = t * N.z)
    (hEx : ∀ e ∈ E, x'⁻¹ * e * x' ∈ Subgroup.zpowers t ⊔ E) : False := by
  have hf := h.facts2511
  have hKH := H_le_normalizer_K N h F
  obtain ⟨-, hQ⟩ := (h.concl2512 hKH).1 U HU hpair hUS
  have ht2 := t_mul_self N hf
  have htS : t ∈ N.S := N.SC_le_S hf.t_mem
  have hK0 : N.K0 = N.K := N.K0_eq hKH
  have htK : ∀ k ∈ N.K, k * t = t * k := fun k hk =>
    Subgroup.mem_centralizer_iff.mp (N.SC_le_centralizer hf.t_mem) k (hK0 ▸ hk)
  have hEK : E ≤ N.K := hESK.trans N.SK_le_K
  have htE : t ∈ Subgroup.normalizer (E : Set G) :=
    BenderBranch.mem_normalizer_of_forall_commute fun k hk => (htK k (hEK hk)).symm
  have hzt : ∀ g ∈ N.H, g ∈ Subgroup.normalizer (Subgroup.zpowers t : Set G) := by
    intro g hg
    rw [normalizer_zpowers_eq_centralizer ht2]
    exact hf.H_le hg
  have hQ₁S : Subgroup.zpowers t ⊔ E ≤ N.S :=
    sup_le (Subgroup.zpowers_le.mpr htS) (hESK.trans N.SK_le_S)
  have hQ₁2 : IsPGroup 2 ↥(Subgroup.zpowers t ⊔ E) := N.tuple.sylow.isPGroup.to_le hQ₁S
  have hzQ : N.z ∈ Subgroup.zpowers t ⊔ E := Subgroup.mem_sup_right hzE
  have hQ₁HU : Subgroup.zpowers t ⊔ E ≤ HU := by
    rw [hHU]
    refine sup_le ?_ (le_inf (hEK.trans N.K_le_H) Subgroup.le_normalizer)
    rw [Subgroup.zpowers_le]
    exact ⟨N.S_le_H htS, htE⟩
  have hHUN : HU ≤ Subgroup.normalizer ((Subgroup.zpowers t ⊔ E : Subgroup G) : Set G) := by
    intro g hg
    rw [hHU] at hg
    exact mem_normalizer_sup (hzt g hg.1) hg.2
  have hUsyl := (hQ (Subgroup.zpowers t ⊔ E) hQ₁2 hzQ hQ₁HU hHUN).2
  have hx'inv : x'⁻¹ ∈ Subgroup.normalizer ((Subgroup.zpowers t ⊔ E : Subgroup G) : Set G) := by
    rw [Subgroup.sup_eq_closure]
    apply normalizer_closure_of_forall
    intro y hy
    rcases hy with hy | hy
    · rcases mem_zpowers_involution ht2 hy with h1 | h1
      · rw [h1]
        simp
      · rw [h1, inv_inv, htx]
        exact Subgroup.mul_mem _ (Subgroup.subset_closure (Or.inl (Subgroup.mem_zpowers t)))
          (Subgroup.subset_closure (Or.inr hzE))
    · have := hEx y hy
      rw [Subgroup.sup_eq_closure] at this
      simpa using this
  have hx'N : x' ∈ Subgroup.normalizer ((Subgroup.zpowers t ⊔ E : Subgroup G) : Set G) := by
    have := Subgroup.inv_mem _ hx'inv
    simpa using this
  have hUN : U ≤ Subgroup.normalizer ((Subgroup.zpowers t ⊔ E : Subgroup G) : Set G) := by
    refine le_trans ?_ hHUN
    rw [hU, hHU]
    exact inf_le_inf_right _ N.S_le_H
  have hjoin : U ⊔ Subgroup.zpowers x' ≤
      Subgroup.normalizer ((Subgroup.zpowers t ⊔ E : Subgroup G) : Set G) :=
    sup_le hUN (Subgroup.zpowers_le.mpr hx'N)
  have hjoinT : U ⊔ Subgroup.zpowers x' ≤ T :=
    sup_le (hUS.trans N.S_le_T) (Subgroup.zpowers_le.mpr hx'.1)
  have hj2 : IsPGroup 2 ↥(U ⊔ Subgroup.zpowers x') := (isPGroup_T hs).to_le hjoinT
  have heq := hUsyl.eq_of_le le_sup_left hjoin hj2
  apply hx'S
  have hmem : x' ∈ U ⊔ Subgroup.zpowers x' := Subgroup.mem_sup_right (Subgroup.mem_zpowers x')
  rw [heq] at hmem
  exact hUS hmem

end Config

end CFSG.QuasithinUnique.Unc25K1
