module

public import CFSG.LocalAnalysis.EvenBN.U5.Sec3B6

public noncomputable section

namespace CFSG.LocalAnalysis.EvenBN.U5

open Subgroup CFSG.Open CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
  CFSG.RankThree.PartOne.U5K.Hyp CFSG.LocalAnalysis.EvenBN.Common
open scoped commutatorElement

section Generic

variable {G : Type*} [Group G]

theorem exists_mem_normalizer_not_mem_of_card_lt [Finite G] {p : ℕ} [Fact p.Prime]
    {P Q : Subgroup G} (hP : IsPGroup p P) (hQ : IsPGroup p Q) (hlt : Nat.card P < Nat.card Q) :
    ∃ y ∈ normalizer (P : Set G), y ∉ P ∧ IsPGroup p (P ⊔ zpowers y : Subgroup G) := by
  obtain ⟨S₀, hPS₀⟩ := hP.exists_le_sylow
  obtain ⟨S₁, hQS₁⟩ := hQ.exists_le_sylow
  have hcard : Nat.card P < Nat.card S₀ :=
    calc _ < Nat.card Q := hlt
      _ ≤ Nat.card S₁ := card_le_of_le hQS₁
      _ = Nat.card S₀ := by rw [Sylow.card_eq_multiplicity, Sylow.card_eq_multiplicity]
  have hlt' : P.subgroupOf (S₀ : Subgroup G) < ⊤ := by
    refine lt_top_iff_ne_top.2 fun htop => ?_
    have hle : (S₀ : Subgroup G) ≤ P := fun x hx => by
      have : (⟨x, hx⟩ : (S₀ : Subgroup G)) ∈ P.subgroupOf (S₀ : Subgroup G) := by
        rw [htop]
        exact mem_top _
      exact mem_subgroupOf.1 this
    exact absurd (card_le_of_le hle) (not_le.2 hcard)
  have : Group.IsNilpotent (S₀ : Subgroup G) := S₀.isPGroup'.isNilpotent
  obtain ⟨y, hyN, hyP⟩ :=
    IsConcreteLE.exists_of_lt (Group.normalizerCondition_of_isNilpotent _ hlt')
  refine ⟨y, mem_normalizer_fintype fun n hn =>
      mem_subgroupOf.1 ((mem_normalizer_iff.1 hyN ⟨n, hPS₀ hn⟩).1 (mem_subgroupOf.2 hn)),
    fun e => hyP (mem_subgroupOf.2 e), S₀.isPGroup'.to_le (sup_le hPS₀ (zpowers_le.2 y.2))⟩

theorem ElemAbMod.map_conj {N E : Subgroup G} (hE : ElemAbMod N E) (y : G) :
    ElemAbMod (N.map (MulAut.conj y).toMonoidHom) (E.map (MulAut.conj y).toMonoidHom) := by
  refine ⟨?_, ?_⟩
  · rintro _ ⟨x, hx, rfl⟩
    exact ⟨x * x, hE.1 x hx, map_mul _ x x⟩
  · rintro _ ⟨x, hx, rfl⟩ _ ⟨x', hx', rfl⟩
    exact ⟨⁅x, x'⁆, hE.2 x hx x' hx', map_commutatorElement _ x x'⟩

end Generic

namespace Data

variable {G : Type} [Group G] [Finite G] {f : ℕ} {K : Type} [Field K]
  {h : UnitaryFieldData 2 f K} {d : Data G h}

theorem Hyp.T_le_normalizer_E (hGMS : GMSK.GMSUnitarySharpKRankOneStatement) (hd : d.Hyp) :
    d.T ≤ normalizer (d.E : Set G) := fun _ hs =>
  hd.normalizer_B₄_le_normalizer_E hGMS (d.le_normalizer_B₄
    (d.normalizer_tP_le_normalizer_ZtP (hd.normalizer_T_le (le_normalizer hs))))

theorem Hyp.isPGroup_E (hGMS : GMSK.GMSUnitarySharpKRankOneStatement) (hd : d.Hyp) :
    IsPGroup 2 d.E :=
  IsPGroup.of_card (n := f * 14) (by rw [hd.card_E hGMS, ← pow_mul])

theorem Hyp.E_inf_T_le_A₂ (hGMS : GMSK.GMSUnitarySharpKRankOneStatement) (hd : d.Hyp) :
    d.E ⊓ d.T ≤ d.A₂ := fun x hx => by
  rw [← hd.E_inf_B₂ hGMS]
  exact ⟨hx.1, hd.C₀_inf_C_le_B₂ ⟨hd.E_le_C₀ hGMS hx.1, hd.T_le_centralizer hx.2⟩⟩

theorem Hyp.card_FT_lt_card_ET (hGMS : GMSK.GMSUnitarySharpKRankOneStatement) (hd : d.Hyp) :
    Nat.card (d.F ⊔ d.T : Subgroup G) < Nat.card (d.E ⊔ d.T : Subgroup G) := by
  set q := 2 ^ f with hq
  have hq4 : 4 ≤ q := hd.four_le
  have h1 := Common.card_sup_mul_card_inf_eq (hd.T_le_normalizer_F hGMS)
  rw [hd.F_inf_T hGMS, hd.card_F hGMS, d.card_A₁] at h1
  have h2 := Common.card_sup_mul_card_inf_eq (hd.T_le_normalizer_E hGMS)
  rw [hd.card_E hGMS] at h2
  have h3 : Nat.card (d.E ⊓ d.T : Subgroup G) ≤ q ^ 7 := by
    rw [← d.card_A₂]
    exact Subgroup.card_le_of_le (hd.E_inf_T_le_A₂ hGMS)
  have hT0 : 0 < Nat.card d.T := Nat.card_pos
  have hFT : Nat.card (d.F ⊔ d.T : Subgroup G) = q ^ 4 * Nat.card d.T :=
    Nat.eq_of_mul_eq_mul_right (by positivity : 0 < q ^ 4) (h1.trans (by ring))
  have hET : q ^ 7 * Nat.card d.T ≤ Nat.card (d.E ⊔ d.T : Subgroup G) := by
    refine Nat.le_of_mul_le_mul_right (c := q ^ 7) ?_ (by positivity)
    calc q ^ 7 * Nat.card d.T * q ^ 7 = q ^ 14 * Nat.card d.T := by ring
      _ = Nat.card (d.E ⊔ d.T : Subgroup G) * Nat.card (d.E ⊓ d.T : Subgroup G) := h2.symm
      _ ≤ Nat.card (d.E ⊔ d.T : Subgroup G) * q ^ 7 := Nat.mul_le_mul_left _ h3
  have h47 : q ^ 4 < q ^ 7 := Nat.pow_lt_pow_right (by omega) (by norm_num)
  rw [hFT]
  exact lt_of_lt_of_le (Nat.mul_lt_mul_of_pos_right h47 hT0) hET

theorem Hyp.mem_normalizer_F_of_conj_le (hGMS : GMSK.GMSUnitarySharpKRankOneStatement)
    (hd : d.Hyp) {y : G} (hy : ∀ x ∈ d.F, y * x * y⁻¹ ∈ d.F ⊔ d.T) :
    y ∈ normalizer (d.F : Set G) := by
  set F' := d.F.map (MulAut.conj y).toMonoidHom with hF'
  have hF'FT : F' ≤ d.F ⊔ d.T := by
    rintro _ ⟨x, hx, rfl⟩
    exact hy x hx
  have hF'el : CFSG.IsElementaryAbelian 2 F' := by
    refine isElementaryAbelian_of_forall ?_ ?_
    · rintro _ ⟨x, hx, rfl⟩ _ ⟨x', hx', rfl⟩
      rw [← map_mul, ← map_mul, hd.F_comm hGMS x hx x' hx']
    · rintro _ ⟨x, hx, rfl⟩
      rw [← map_mul, hd.mul_self_eq_one_of_mem_F hGMS hx, map_one]
  have hcard : Nat.card F' = (2 ^ f) ^ 8 := by
    rw [hF', card_map_of_injective (MulAut.conj y).injective, hd.card_F hGMS]
  exact mem_normalizer_of_map_conj_eq ((hd.card_le_of_le_FT hGMS hF'FT hF'el).2 hcard.ge)

theorem Hyp.FB₂_inf_centralizer_F_le (hGMS : GMSK.GMSUnitarySharpKRankOneStatement)
    (hd : d.Hyp) :
    (d.F ⊔ d.B₂) ⊓ centralizer (d.F : Set G) ≤ d.F ⊔ (d.A₂ ⊓ d.A₃) := by
  intro x hx
  have hB₂N : d.B₂ ≤ normalizer (d.F : Set G) :=
    (hd.B₂_spec.2.1.trans hd.tP_le_T).trans (hd.T_le_normalizer_F hGMS)
  obtain ⟨y, hy, b, hb, rfl⟩ := exists_mul_of_mem_sup_of_le_normalizer hB₂N hx.1
  have hyc : y ∈ centralizer (d.F : Set G) :=
    mem_centralizer_iff.2 fun z hz => hd.F_comm hGMS z hz y hy
  have hbc : b ∈ centralizer (d.F : Set G) := by
    have := mul_mem (inv_mem hyc) hx.2
    rwa [inv_mul_cancel_left] at this
  have hbA : b ∈ centralizer (d.A₁ : Set G) :=
    Subgroup.centralizer_le (SetLike.coe_subset_coe.2 hd.A₁_le_F) hbc
  have htA : d.t ∈ centralizer (d.A₁ : Set G) :=
    Subgroup.centralizer_le (SetLike.coe_subset_coe.2 (d.A₁_le_P.trans d.P_le_L)) hd.t_mem
  obtain ⟨a, ha, e | e⟩ := hd.exists_of_mem_zpowers_sup d.A₂_le_L hb <;> subst b
  · exact mul_mem (mem_sup_left hy) (mem_sup_right
      ⟨ha, hd.mem_A₃_of_mem_P_of_comm (d.A₂_le_P ha) hbA⟩)
  · exfalso
    have haA : a ∈ centralizer (d.A₁ : Set G) := by
      have := mul_mem (inv_mem htA) hbA
      rwa [inv_mul_cancel_left] at this
    have haA₃ := hd.mem_A₃_of_mem_P_of_comm (d.A₂_le_P ha) haA
    apply hd.t_not_mem_centralizer_F hGMS
    have := mul_mem hbc (inv_mem (hd.A₃_le_centralizer_F haA₃))
    rwa [mul_inv_cancel_right] at this

theorem Hyp.A₃_not_le (hGMS : GMSK.GMSUnitarySharpKRankOneStatement) (hd : d.Hyp) :
    ¬ d.A₃ ≤ d.F ⊔ (d.A₂ ⊓ d.A₃) := by
  intro hA₃
  obtain ⟨g₀, hg₀, hcrd⟩ := exists_Ssub_crd h ![0, 1]
  obtain ⟨y₁, hy₁, a, ha, he⟩ := exists_mul_of_mem_sup_of_le_normalizer
    (inf_le_right.trans (hd.A₃_le_normalizer_F hGMS)) (hA₃ ⟨g₀, hg₀, rfl⟩)
  have ha₂ : a ∈ d.A₂ := (Subgroup.mem_inf.1 ha).1
  have ha₃ : a ∈ d.A₃ := (Subgroup.mem_inf.1 ha).2
  have hy₁A : y₁ ∈ d.A₁ := by
    rw [← hd.F_inf_A₃ hGMS]
    refine Subgroup.mem_inf.2 ⟨hy₁, ?_⟩
    rw [show y₁ = d.η g₀ * a⁻¹ by rw [he, mul_inv_cancel_right]]
    exact mul_mem ⟨g₀, hg₀, rfl⟩ (inv_mem ha₃)
  obtain ⟨v, hv, rfl⟩ := hy₁A
  obtain ⟨s', hs', hss'⟩ := ha₃
  obtain ⟨s, hs, rfl⟩ := ha₂
  have hss : s' = s := d.η_injOn (Ssub_le_Usub hs') (A₂sub_le_U hs) hss'
  subst hss
  have hg : g₀ = v * s' := d.η_injOn (Ssub_le_Usub hg₀)
    (mul_mem (Ssub_le_Usub (Vsub_le_Ssub hv)) (Ssub_le_Usub hs')) (by rw [map_mul]; exact he)
  have := congrFun (crd_mul (Vsub_le_Ssub hv) hs') 1
  rw [← hg, hcrd, (crd_eq_zero_iff (Vsub_le_Ssub hv)).2 hv, Pi.add_apply,
    crd_one_eq_zero_of_mem_A₂sub hs] at this
  simp at this

theorem Hyp.mem_normalizer_FB₃_of (hGMS : GMSK.GMSUnitarySharpKRankOneStatement) (hd : d.Hyp)
    {y : G} (hyT : y ∈ normalizer ((d.F ⊔ d.T : Subgroup G) : Set G)) :
    y ∈ normalizer ((d.F ⊔ d.B₃ : Subgroup G) : Set G) := by
  have hyF : y ∈ normalizer (d.F : Set G) := hd.mem_normalizer_F_of_conj_le hGMS fun x hx =>
    (mem_normalizer_iff.1 hyT x).1 (mem_sup_left hx)
  have hB₃T : d.B₃ ≤ d.T := d.B₃_le_tP.trans hd.tP_le_T
  set X := (d.F ⊔ d.B₃).map (MulAut.conj y).toMonoidHom with hX
  have hFX : d.F ≤ X := by
    rw [← map_conj_eq_of_mem_normalizer hyF]
    exact map_mono le_sup_left
  have hXT : X ≤ d.F ⊔ d.T := by
    rintro _ ⟨x, hx, rfl⟩
    exact (mem_normalizer_iff.1 hyT x).1 (sup_le_sup_left hB₃T _ hx)
  have hXel : ElemAbMod d.F X := by
    have := (hd.elemAbMod_F_FB₃).map_conj y
    rwa [map_conj_eq_of_mem_normalizer hyF] at this
  have hXc : Nat.card X = 2 * (2 ^ f) ^ 12 := by
    rw [hX, card_map_of_injective (MulAut.conj y).injective, hd.card_FB₃ hGMS]
  rcases (hd.card_le_of_elemAbMod_F hGMS hFX hXT hXel).2 hXc with e | e
  · exact mem_normalizer_of_map_conj_eq e
  · exfalso
    have hle : (d.F ⊔ d.A₃).map (MulAut.conj y).toMonoidHom ≤ d.F ⊔ (d.A₂ ⊓ d.A₃) := by
      rintro _ ⟨x, hx, rfl⟩
      have hxc := ((hd.FB₃_inf_centralizer_F hGMS).ge hx).2
      refine hd.FB₂_inf_centralizer_F_le hGMS ⟨?_, ?_⟩
      · rw [← e]
        exact ⟨x, sup_le_sup_left d.A₃_le_B₃ _ hx, rfl⟩
      · exact (mem_normalizer_iff.1 (Prelim.normalizer_le_normalizer_centralizer d.F hyF) x).1
          hxc
    have hle2 : d.F ⊔ (d.A₂ ⊓ d.A₃) ≤ d.F ⊔ d.A₃ := sup_le_sup_left inf_le_right _
    have heq : (d.F ⊔ d.A₃).map (MulAut.conj y).toMonoidHom = d.F ⊔ d.A₃ :=
      Subgroup.eq_of_le_of_card_ge (hle.trans hle2)
        (by rw [card_map_of_injective (MulAut.conj y).injective])
    exact hd.A₃_not_le hGMS (le_sup_right.trans (heq ▸ hle))

theorem Hyp.exists_mem_normalizer_FB₃_not_mem_normalizer_B₁
    (hGMS : GMSK.GMSUnitarySharpKRankOneStatement) (hd : d.Hyp) :
    ∃ y ∈ normalizer ((d.F ⊔ d.B₃ : Subgroup G) : Set G), y ∉ normalizer (d.B₁ : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hFT2 : IsPGroup 2 (d.F ⊔ d.T : Subgroup G) :=
    hd.isPGroup_F.to_sup_of_normal_left' hd.isPGroup_T (hd.T_le_normalizer_F hGMS)
  have hET2 : IsPGroup 2 (d.E ⊔ d.T : Subgroup G) :=
    (hd.isPGroup_E hGMS).to_sup_of_normal_left' hd.isPGroup_T (hd.T_le_normalizer_E hGMS)
  obtain ⟨y, hyN, hyFT, hX2⟩ :=
    exists_mem_normalizer_not_mem_of_card_lt hFT2 hET2 (hd.card_FT_lt_card_ET hGMS)
  refine ⟨y, hd.mem_normalizer_FB₃_of hGMS hyN, fun hyB => hyFT ?_⟩
  obtain ⟨x, hx, c, hc, hyc⟩ := hd.exists_F_mul hGMS hyB
  have hcX : c ∈ (d.F ⊔ d.T) ⊔ zpowers y := by
    rw [show c = x⁻¹ * y by rw [hyc]; group]
    exact mul_mem (mem_sup_left (mem_sup_left (inv_mem hx))) (mem_sup_right (mem_zpowers y))
  have hT : ((d.F ⊔ d.T) ⊔ zpowers y) ⊓ centralizer ({d.t} : Set G) = d.T :=
    hd.T_syl.eq_of_le (le_inf (le_sup_right.trans le_sup_left) hd.T_le_centralizer)
      inf_le_right (hX2.to_le inf_le_left)
  have hcT : c ∈ d.T := hT ▸ ⟨hcX, hc.2⟩
  rw [hyc]
  exact mul_mem (mem_sup_left hx) (mem_sup_right hcT)

end Data

end CFSG.LocalAnalysis.EvenBN.U5
