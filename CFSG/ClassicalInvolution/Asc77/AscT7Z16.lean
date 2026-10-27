module

public import CFSG.ClassicalInvolution.Asc77.AscT7Z15
public import CFSG.ClassicalInvolution.Asc77.AscT7Z5
public import CFSG.ClassicalInvolution.Asc77.AscT7Y3
public import CFSG.ClassicalInvolution.Asc77.AscT7Z1

public section

namespace CFSG.ClassicalInvolution.Asc77

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Asc77.ExactLayer
  CFSG.ClassicalInvolution.Balance CFSG.ClassicalInvolution.Balance.Bootstrap
open scoped commutatorElement

namespace T7Z

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
  {K K' W : Subgroup G} {z u e g : G}

section Perfect

omit [Finite G] in
theorem perfect_exactLayer (Ω : Set (Subgroup G)) (c : G) [Finite G] :
    Group.IsPerfect ↥(exactLayer Ω c) := by
  refine Subgroup.isPerfect_iff.mpr (le_antisymm ?_ ?_)
  · exact Subgroup.commutator_le.mpr fun x hx y hy => by
      rw [commutatorElement_def]
      exact (exactLayer Ω c).mul_mem ((exactLayer Ω c).mul_mem
        ((exactLayer Ω c).mul_mem hx hy) ((exactLayer Ω c).inv_mem hx))
        ((exactLayer Ω c).inv_mem hy)
  · rw [exactLayer_eq_omegaGen]
    refine iSup₂_le fun L hL => ?_
    obtain ⟨K₀, hK₀, rfl⟩ := hL
    have hle : exactCore c K₀ ≤ omegaGen (exactFamily Ω c) := le_omegaGen ⟨K₀, hK₀, rfl⟩
    have hperf := Subgroup.isPerfect_iff.mp (perfect_exactCore (c := c) K₀)
    calc exactCore c K₀ = ⁅exactCore c K₀, exactCore c K₀⁆ := hperf.symm
      _ ≤ ⁅omegaGen (exactFamily Ω c), omegaGen (exactFamily Ω c)⁆ :=
        Subgroup.commutator_mono hle hle

end Perfect

section Alpha

omit [Finite G] in
theorem oddCore_commutes_of_alphaOf [Finite G] (hΩ : ConjInvariant Ω) {c t : G} (hc1 : c ≠ 1)
    {A : Subgroup G} (hcA : c ∈ A) (htA : t ∈ A) (hα : alphaOf A = ⊥) {n : G}
    (hn : n ∈ oddCoreOf (exactLayer Ω c)) : n * t = t * n := by
  have hBN : ∀ b ∈ Subgroup.centralizer ({c} : Set G),
      b ∈ Subgroup.normalizer (oddCoreOf (exactLayer Ω c) : Set G) := fun b hb =>
    T7L.mem_normalizer_oddCoreOf (T7Y.mem_normalizer_exactLayer hΩ hb)
  have hOY : oddCoreOf (exactLayer Ω c) ≤ oddCoreOf (Subgroup.centralizer ({c} : Set G)) :=
    le_oddCoreIn_of_normalizes ((oddCoreIn_le _).trans (exactLayer_le_centralizer Ω c)) hBN
      (oddCoreOf_odd_natCard _)
  exact T7Y.commute_of_alphaOf_eq_bot hcA hc1 hα (hOY hn) htA

variable [IsSimpleGroup G]


theorem alphaOf_pair_eq_bot (hs : Hyp23Setting p f Ω K K' z) (hd : Hyp23bData Ω K K' W z u e g)
    (hα : alphaOf (Subgroup.closure ({u, z} : Set G)) = ⊥) {x y : G}
    (hx : x ∈ Subgroup.closure ({u * e, u, z} : Set G))
    (hy : y ∈ Subgroup.closure ({u * e, u, z} : Set G)) (hx1 : x ≠ 1) (hy1 : y ≠ 1) (hxy : x ≠ y) :
    alphaOf (Subgroup.closure ({x, y} : Set G)) = ⊥ := by
  obtain ⟨-, halpha⟩ := T7K.c23_5X_one_proved hs hd
  have hBel := T7K.B_isElemAbelian hs hd
  have sq : ∀ w ∈ Subgroup.closure ({u * e, u, z} : Set G), w * w = 1 := fun w hw => by
    have := hBel.2 w hw
    rwa [pow_two] at this
  have hcomm := T7A.commutes_closure (T7K.comm_gen hs hd)
  have hA : IsElemAbelian2 (Subgroup.closure ({x, y} : Set G)) 2 :=
    T7A.isElemAbelian2_closure_pair (sq x hx) (sq y hy) hx1 hy1 hxy (hcomm x hx y hy)
  have hAB : Subgroup.closure ({x, y} : Set G) ≤ Subgroup.closure ({u * e, u, z} : Set G) := by
    rw [Subgroup.closure_le]
    intro w hw
    rcases hw with rfl | rfl
    · exact hx
    · exact hy
  exact (halpha _ hAB hA).trans hα

end Alpha

section ZStarE

variable [IsSimpleGroup G]


theorem alphaOf_et_eq_bot (hs : Hyp23Setting p f Ω K K' z) (hd : Hyp23bData Ω K K' W z u e g)
    (hα : alphaOf (Subgroup.closure ({u, z} : Set G)) = ⊥) :
    alphaOf (Subgroup.closure ({e, u * e} : Set G)) = ⊥ := by
  obtain ⟨hzB, huB, heB⟩ := T7K.generators_mem_B z u e
  have htB : u * e ∈ Subgroup.closure ({u * e, u, z} : Set G) := Subgroup.mul_mem _ huB heB
  obtain ⟨⟨ht1, htu⟩, -⟩ := T7L.B_ne hs hd
  have hne : e ≠ u * e := fun h => hd.hu1 (by
    have : u * e = 1 * e := by rw [one_mul]; exact h.symm
    exact mul_right_cancel this)
  exact alphaOf_pair_eq_bot hs hd hα heB htB hd.he1 ht1 hne

theorem alphaOf_ut_eq_bot (hs : Hyp23Setting p f Ω K K' z) (hd : Hyp23bData Ω K K' W z u e g)
    (hα : alphaOf (Subgroup.closure ({u, z} : Set G)) = ⊥) :
    alphaOf (Subgroup.closure ({u, u * e} : Set G)) = ⊥ := by
  obtain ⟨hzB, huB, heB⟩ := T7K.generators_mem_B z u e
  have htB : u * e ∈ Subgroup.closure ({u * e, u, z} : Set G) := Subgroup.mul_mem _ huB heB
  obtain ⟨⟨ht1, htu⟩, -⟩ := T7L.B_ne hs hd
  exact alphaOf_pair_eq_bot hs hd hα huB htB hd.hu1 ht1 (Ne.symm htu)

theorem g_mem_E (hs : Hyp23Setting p f Ω K K' z) (hd : Hyp23bData Ω K K' W z u e g) :
    g ∈ exactLayer Ω e := by
  have hst := hs.stand
  rw [← rLayer_eq_exactLayer hst.odd hst.five hst.hyp hd.he2]
  have : (⨆ R ∈ DSet Ω W, R) ≤ rLayer Ω e := by
    refine iSup₂_le fun R hR => ?_
    refine le_iSup₂_of_le R hR.1 (le_iSup_of_le (fun r hr => ?_) le_rfl)
    exact Subgroup.mem_centralizer_singleton_iff.mpr (T7K.comm_e hd (hR.2 hr))
  exact this hd.hg

theorem z_mem_E (hs : Hyp23Setting p f Ω K K' z) (hd : Hyp23bData Ω K K' W z u e g)
    (hα : alphaOf (Subgroup.closure ({u, z} : Set G)) = ⊥) : z ∈ exactLayer Ω e := by
  have hst := hs.stand
  obtain ⟨R, R', a, b, r, hR, hR', -, hRN, hR'N, haR, hbR', -, -, hu, haa, hbb, -, -⟩ :=
    T7K.exists_decomp hs hd
  have hKe := T7Y.le_centralizer_e hs hd hα hst.mem hs.hz hR hRN
  have : K ≤ exactLayer Ω e := by
    rw [exactLayer_eq_omegaGen]
    exact le_omegaGen (centMembers_subset_exactFamily hst.hyp.classical ⟨hst.mem, hKe⟩)
  exact this hs.hz.mem

theorem t_mem_E (hs : Hyp23Setting p f Ω K K' z) (hd : Hyp23bData Ω K K' W z u e g)
    (hα : alphaOf (Subgroup.closure ({u, z} : Set G)) = ⊥) : u * e ∈ exactLayer Ω e := by
  have hgE := g_mem_E hs hd
  have hzE := z_mem_E hs hd hα
  rw [← hd.hgt]
  exact (exactLayer Ω e).mul_mem ((exactLayer Ω e).mul_mem hgE hzE) ((exactLayer Ω e).inv_mem hgE)

theorem not_mem_zStar_E (hs : Hyp23Setting p f Ω K K' z) (hd : Hyp23bData Ω K K' W z u e g)
    (hα : alphaOf (Subgroup.closure ({u, z} : Set G)) = ⊥) :
    u * e ∉ zStarOf (exactLayer Ω e) := by
  intro htZ
  have hst := hs.stand
  have hΩ : HypOmegaMod p f Ω := hst.hyp
  obtain ⟨hzB, huB, heB⟩ := T7K.generators_mem_B z u e
  have htB : u * e ∈ Subgroup.closure ({u * e, u, z} : Set G) := Subgroup.mul_mem _ huB heB
  have hαA := alphaOf_et_eq_bot hs hd hα
  have ht2 : (u * e) * (u * e) = 1 := t_sq hd hs
  have hgE := g_mem_E hs hd
  have htE := t_mem_E hs hd hα
  have hEt : ∀ y ∈ exactLayer Ω e, y * (u * e) = (u * e) * y := by
    intro y hy
    set N₀ := classicalInvolutionOddCore ↥(exactLayer Ω e) with hN₀
    obtain ⟨x₀, hx₀, hx₀t⟩ := Subgroup.mem_map.mp htZ
    have hcen := Subgroup.mem_center_iff.mp (Subgroup.mem_comap.mp hx₀)
      (QuotientGroup.mk' N₀ ⟨y⁻¹, Subgroup.inv_mem _ hy⟩)
    have hx₀' : x₀ = ⟨u * e, htE⟩ := Subtype.ext hx₀t
    rw [hx₀'] at hcen
    have hmk : QuotientGroup.mk' N₀ ⟨y⁻¹, Subgroup.inv_mem _ hy⟩ *
        QuotientGroup.mk' N₀ ⟨u * e, htE⟩ *
        (QuotientGroup.mk' N₀ ⟨y⁻¹, Subgroup.inv_mem _ hy⟩)⁻¹ =
        QuotientGroup.mk' N₀ ⟨u * e, htE⟩ := by
      rw [hcen, mul_inv_cancel_right]
    have ho := T7L.mem_oddCore_of_mk_conj htE htE ⟨y⁻¹, Subgroup.inv_mem _ hy⟩ hmk
    simp only [inv_inv] at ho
    set o : G := (u * e)⁻¹ * (y * (u * e) * y⁻¹) with hodef
    have hot : o * (u * e) = (u * e) * o :=
      oddCore_commutes_of_alphaOf hΩ.conjInvariant hd.he1 (Subgroup.subset_closure (by simp))
        (Subgroup.subset_closure (by simp)) hαA ho
    have hyt : y * (u * e) * y⁻¹ = (u * e) * o := by simp only [hodef]; group
    have hsq : ((u * e) * o) * ((u * e) * o) = 1 := by
      rw [← hyt]
      calc (y * (u * e) * y⁻¹) * (y * (u * e) * y⁻¹) = y * ((u * e) * (u * e)) * y⁻¹ := by group
        _ = 1 := by rw [ht2]; group
    have hoo : o * o = 1 := by
      have h1 : ((u * e) * o) * ((u * e) * o) = o * o := by
        calc ((u * e) * o) * ((u * e) * o) = (u * e) * (o * (u * e)) * o := by group
          _ = (u * e) * ((u * e) * o) * o := by rw [hot]
          _ = ((u * e) * (u * e)) * (o * o) := by group
          _ = o * o := by rw [ht2, one_mul]
      exact h1.symm.trans hsq
    have ho1 : o = 1 := T7Y.eq_one_of_sq_eq_one_of_mem_odd (oddCoreOf_odd_natCard _) ho hoo
    rw [ho1, mul_one] at hyt
    exact mul_inv_eq_iff_eq_mul.mp hyt
  have hgt := hEt g hgE
  have hzt : z = u * e := by
    calc z = g⁻¹ * (g * z * g⁻¹) * g := by group
      _ = g⁻¹ * (u * e) * g := by rw [hd.hgt]
      _ = g⁻¹ * ((u * e) * g) := by group
      _ = g⁻¹ * (g * (u * e)) := by rw [hgt]
      _ = u * e := by group
  exact t_ne_z hs hd hzt.symm

end ZStarE

section Layer


theorem oddCore_exactLayer_eq_bot (hodd : OddCenterClassical) (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f)
    {c : G} {d : ℕ} {ε : Bool} (hd56 : d = 5 ∨ d = 6) (hlayer : LayerOrthType p f Ω c d ε)
    {t : G} (htY : t ∈ exactLayer Ω c)
    (htcomm : ∀ n ∈ oddCoreOf (exactLayer Ω c), n * t = t * n)
    (htz : t ∉ zStarOf (exactLayer Ω c)) :
    classicalInvolutionOddCore ↥(exactLayer Ω c) = ⊥ := by
  obtain ⟨t', n', hT, D, hcard, i, hit, hir⟩ := hlayer
  have ht : (D.tag i = .PSL ∧ D.rank i = 4) ∨ (D.tag i = .PSU ∧ D.rank i = 4) ∨
      (D.tag i = .PSp ∧ D.rank i = 2) := by
    rcases hT with ⟨-, h1, h2⟩ | ⟨-, -, h1, h2⟩ | ⟨-, -, h1, h2⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩
    · exact Or.inr (Or.inr ⟨hit.trans h1, hir.trans h2⟩)
    · exact Or.inl ⟨hit.trans h1, hir.trans h2⟩
    · exact Or.inr (Or.inl ⟨hit.trans h1, hir.trans h2⟩)
    all_goals omega
  refine oddCore_eq_bot_of_lie hodd hp2 hq (perfect_exactLayer Ω c) D hcard i ht
    (t := ⟨t, htY⟩) ?_ ?_
  · intro n hn
    exact Subtype.ext (htcomm n ⟨n, hn, rfl⟩)
  · intro hc
    apply htz
    exact Subgroup.mem_map.mpr ⟨⟨t, htY⟩, Subgroup.mem_comap.mpr hc, rfl⟩

end Layer

section Final

variable [IsSimpleGroup G]


theorem oddCore_layers_eq_bot (hodd : OddCenterClassical) (hs : Hyp23Setting p f Ω K K' z)
    (hd : Hyp23bData Ω K K' W z u e g) (hα : alphaOf (Subgroup.closure ({u, z} : Set G)) = ⊥)
    (hE : LayerOrthType p f Ω e 6 (piSign p f))
    (hY : LayerOrthType p f Ω u 5 true ∨ LayerOrthType p f Ω u 6 (!piSign p f)) :
    classicalInvolutionOddCore ↥(exactLayer Ω e) = ⊥ ∧
      classicalInvolutionOddCore ↥(exactLayer Ω u) = ⊥ := by
  have hst := hs.stand
  have hp2 : p ≠ 2 := hst.odd
  have hq : 5 ≤ p ^ f := hst.five
  have hΩ : HypOmegaMod p f Ω := hst.hyp
  refine ⟨?_, ?_⟩
  · refine oddCore_exactLayer_eq_bot hodd hp2 hq (Or.inr rfl) hE (t := u * e)
      (t_mem_E hs hd hα) ?_ (not_mem_zStar_E hs hd hα)
    intro n hn
    exact oddCore_commutes_of_alphaOf hΩ.conjInvariant hd.he1 (Subgroup.subset_closure (by simp))
      (Subgroup.subset_closure (by simp)) (alphaOf_et_eq_bot hs hd hα) hn
  · obtain ⟨a₂, b₂, v', ha₂Y, hb₂Y, hv'Y, htY, hv'z, hS, hlt, T, hconj⟩ := T7L.layer_u_frame hs hd
    have hnoZ := c23_9_noZX_proved (p := p) (f := f) G Ω K K' W z u e g hs hd hE
    rw [rLayer_eq_exactLayer hp2 hq hΩ hd.hu2] at hnoZ
    have hcomm : ∀ n ∈ oddCoreOf (exactLayer Ω u), n * (u * e) = (u * e) * n := fun n hn =>
      oddCore_commutes_of_alphaOf hΩ.conjInvariant hd.hu1 (Subgroup.subset_closure (by simp))
        (Subgroup.subset_closure (by simp)) (alphaOf_ut_eq_bot hs hd hα) hn
    rcases hY with hY | hY
    · exact oddCore_exactLayer_eq_bot hodd hp2 hq (Or.inl rfl) hY htY hcomm hnoZ
    · exact oddCore_exactLayer_eq_bot hodd hp2 hq (Or.inr rfl) hY htY hcomm hnoZ

end Final

end T7Z

end CFSG.ClassicalInvolution.Asc77
