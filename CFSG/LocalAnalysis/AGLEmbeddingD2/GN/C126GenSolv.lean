module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.GN.C126GenBaum
public import CFSG.LocalAnalysis.AGLEmbeddingD2.GN.C126GenDefs

public section

namespace CFSG.AGLEmbeddingD2.GN

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Quasithin.B2F CFSG.Quasithin.E2
  CFSG.LieType.BorelTits

section Gen

variable {G : Type*} [Group G] [Finite G] {V : Subgroup G} {hV : IsElemAbelian 2 V}
  {H T M : Subgroup G} {𝓗 I : Finset (Subgroup (MulAut (IntMod V hV)))}

theorem baumann_gen (B : Blocks hV H 𝓗 I) (h : MinParabolic H T M)
    (hsolv : Group.IsSolvable H) (hred : IsTwoReducedIn H V)
    (hJ : ¬ thompsonJ T ≤ Subgroup.centralizer (V : Set G)) :
    omegaOneCenterOf (thompsonJ T) = (V ⊓ Subgroup.centralizer (thompsonJ T : Set G)) ⊔
        (omegaOneCenterOf (thompsonJ T) ⊓ Subgroup.centralizer (twoResidual H : Set G)) := by
  have hT := h.isSylow
  have hHN : H ≤ Subgroup.normalizer (V : Set G) := hred.2.1
  have hKH : twoResidual H ≤ H := twoResidual_le H
  have hVT : V ≤ T := (MinParabolic.le_pCoreOf_of_isTwoReduced hred).trans
    (B6.pCoreOf_two_le_of_isSylowTwoOf hT)
  have hTN : T ≤ Subgroup.normalizer (V : Set G) := hT.1.trans hHN
  obtain ⟨g, hgK, hgN, hKI⟩ := exists_twoResidual_le_gen B h hsolv hred hJ
  set E := omegaOneCenterOf (thompsonJ T) with hE
  set α := omegaOneCenterOf (thompsonJ (T ⊓ Subgroup.centralizer (V : Set G))) with hα
  set I₀ := thompsonJ T ⊔ cjSub g (thompsonJ T) with hI₀
  have hJTH : thompsonJ T ≤ H := (thompsonJ_le_self T).trans hT.1
  have hI₀H : I₀ ≤ H := by
    refine sup_le hJTH fun z hz => ?_
    rw [mem_cjSub] at hz
    have := H.mul_mem (H.mul_mem (hKH hgK) (hJTH hz)) (H.inv_mem (hKH hgK))
    simpa [mul_assoc] using this
  have hI₀N : I₀ ≤ Subgroup.normalizer (V : Set G) := hI₀H.trans hHN
  obtain ⟨-, hVα, hEα, -⟩ := alpha_facts hV hVT hTN (not_strong hred hsolv hT hJ)
  have hαel : IsElemAbelian 2 α := isElemAbelian_omegaOneCenterOf _
  set W := E ⊔ V with hW
  have hWα : W ≤ α := sup_le hEα hVα
  have hWel : IsElemAbelian 2 W := isElemAbelian_mono hWα hαel
  have hI₀C : I₀ ≤ commCentralizer α V := by
    refine sup_le (fun x hx => ?_) (cjSub_thompsonJ_le_commCentralizer h hred hsolv hJ (hKH hgK))
    refine cjSub_thompsonJ_le_commCentralizer h hred hsolv hJ H.one_mem ?_
    rw [cjSub_one]
    exact hx
  have hI₀W : I₀ ≤ Subgroup.normalizer (W : Set G) := by
    have key : ∀ j ∈ commCentralizer α V, ∀ w ∈ W, j * w * j⁻¹ ∈ W := by
      intro j hj w hw
      have h1 := hj.2 w (hWα hw)
      have h2 : j * w * j⁻¹ = (w * j * w⁻¹ * j⁻¹)⁻¹ * w := by group
      rw [h2]
      exact W.mul_mem (Subgroup.mem_sup_right (V.inv_mem h1)) hw
    intro i hi
    have hiC := hI₀C hi
    rw [Subgroup.mem_normalizer_iff]
    intro w
    refine ⟨key i hiC w, fun hw => ?_⟩
    have := key i⁻¹ ((commCentralizer α V).inv_mem hiC) _ hw
    simpa [mul_assoc] using this
  have hJTN : thompsonJ T ≤ Subgroup.normalizer (V : Set G) := hJTH.trans hHN
  have hJgN : cjSub g (thompsonJ T) ≤ Subgroup.normalizer (V : Set G) :=
    (le_sup_right : cjSub g (thompsonJ T) ≤ I₀).trans hI₀N
  have hKN : twoResidual H ≤ Subgroup.normalizer (V : Set G) := hKH.trans hHN
  have r1 := rkIdx_fixV_autI hV hJTN
  have r2 := rkIdx_fixV_autI hV hJgN
  have r3 := rk_inf_centralizer_cjSub (U := V) hgN (thompsonJ T)
  have r4 := two_mul_rkIdx_le_gen B h hsolv hred hJ
  have r5 := rkIdx_fixV_autI hV hKN
  have hd : rkIdx (fixV (autI hV (thompsonJ T))) +
      rkIdx (fixV (autI hV (cjSub g (thompsonJ T)))) ≤
        rkIdx (fixV (autI hV (twoResidual H))) := by omega
  have hX₁ : ∃ x ∈ I₀, cjSub x (thompsonJ T) ≤ thompsonJ T :=
    ⟨1, I₀.one_mem, (cjSub_one _).le⟩
  have hX₂ : ∃ x ∈ I₀, cjSub x (cjSub g (thompsonJ T)) ≤ thompsonJ T :=
    ⟨g⁻¹, I₀.inv_mem (hKI hgK), (cjSub_inv_cjSub g _).le⟩
  have hEZ : E ≤ Subgroup.centralizer (thompsonJ T : Set G) :=
    fun x hx => (omegaOneCenterOf_le_centerOf _ hx).2
  have hEJ : E ≤ thompsonJ T := fun x hx => (omegaOneCenterOf_le_centerOf _ hx).1
  have hWJ : W ≤ (W ⊓ Subgroup.centralizer (thompsonJ T : Set G)) ⊔ V :=
    sup_le ((le_inf le_sup_left hEZ).trans le_sup_left) le_sup_right
  obtain ⟨hU, hWUV⟩ := W_decomp_two hWel le_sup_right hI₀W hI₀N hKI hd hX₁ hX₂ hWJ
  have hWT : W ≤ T := sup_le (hEJ.trans (thompsonJ_le_self T)) hVT
  have hUE : W ⊓ Subgroup.centralizer (twoResidual H : Set G) ≤ E := by
    intro u hu
    have hu' : u ∈ W ⊓ Subgroup.centralizer (I₀ : Set G) := hU ▸ hu
    rw [hE, ← (omegaOne_centralizer_thompsonJ T).1]
    exact Subgroup.subset_closure ⟨⟨hWT hu'.1,
      Subgroup.centralizer_le (le_sup_left : thompsonJ T ≤ I₀) hu'.2⟩, hWel.2 u hu'.1⟩
  have hVU : V ≤ Subgroup.normalizer
      ((W ⊓ Subgroup.centralizer (twoResidual H : Set G) : Subgroup G) : Set G) :=
    le_normalizer_of_commute fun a ha b hb =>
      isElemAbelian_comm hWel ((le_sup_right : V ≤ W) ha) hb.1
  have hEeq : E = (V ⊓ Subgroup.centralizer (thompsonJ T : Set G)) ⊔
      (E ⊓ Subgroup.centralizer (twoResidual H : Set G)) := by
    refine le_antisymm ?_ (sup_le (inf_centralizer_thompsonJ_le hV hVT) inf_le_left)
    intro x hx
    have hxW : x ∈ ((V ⊔ (W ⊓ Subgroup.centralizer (twoResidual H : Set G)) : Subgroup G) :
        Set G) := by
      rw [← hWUV]
      exact Subgroup.mem_sup_left hx
    rw [Subgroup.coe_mul_of_left_le_normalizer_right _ _ hVU] at hxW
    obtain ⟨v, hv, u, hu, rfl⟩ := hxW
    have huE : u ∈ E := hUE hu
    have hvE : v ∈ E := by
      have := E.mul_mem hx (E.inv_mem huE)
      simpa using this
    exact Subgroup.mul_mem_sup ⟨hv, hEZ hvE⟩ ⟨huE, hu.2⟩
  exact hEeq

theorem isSylowTwoOf_baum_gen (B : Blocks hV H 𝓗 I) (h : MinParabolic H T M)
    (hsolv : Group.IsSolvable H) (hred : IsTwoReducedIn H V)
    (hJ : ¬ thompsonJ T ≤ Subgroup.centralizer (V : Set G)) :
    IsSylowTwoOf (baum T) (twoResidual H ⊔ baum T) := by
  have hT := h.isSylow
  obtain ⟨-, hsyl, -⟩ := B2F.structure_of_not_le hV hred hsolv hT hJ
  have hS := autI_baum_gen B h hsolv hred hJ
  have hE := baumann_gen B h hsolv hred hJ
  set E := omegaOneCenterOf (thompsonJ T) with hEdef
  set K := twoResidual H with hK
  set S := baum T with hSdef
  have hHN : H ≤ Subgroup.normalizer (V : Set G) := hred.2.1
  have hKH : K ≤ H := twoResidual_le H
  have hST : S ≤ T := inf_le_left
  have hSH : S ≤ H := hST.trans hT.1
  have hKN : K ≤ Subgroup.normalizer (V : Set G) := hKH.trans hHN
  have hSN : S ≤ Subgroup.normalizer (V : Set G) := hSH.trans hHN
  have hVT : V ≤ T := (MinParabolic.le_pCoreOf_of_isTwoReduced hred).trans
    (B6.pCoreOf_two_le_of_isSylowTwoOf hT)
  have hTK : T ≤ Subgroup.normalizer (K : Set G) := hT.1.trans (le_normalizer_twoResidual H)
  have hTS : T ≤ Subgroup.normalizer (S : Set G) :=
    Subgroup.le_normalizer.trans (normalizer_le_normalizer_baum T)
  have hSK : S ≤ Subgroup.normalizer (K : Set G) := hST.trans hTK
  have h2 : IsSylowTwoOf (autI hV S) (autI hV (K ⊔ S)) := by
    rw [autI_sup hV hKN hSN, hS]
    have hle : autI hV K ⊔ autI hV (thompsonJ T) ≤ autI hV (thompsonJ H) :=
      sup_le (autI_mono hV (twoResidual_le_thompsonJ h hred hJ)) hsyl.1
    refine ⟨le_sup_right, hsyl.2.1, fun h2 => hsyl.2.2 ?_⟩
    have h2' : 2 ∣ (autI hV (thompsonJ T)).relIndex (autI hV K ⊔ autI hV (thompsonJ T)) := h2
    show 2 ∣ (autI hV (thompsonJ T)).relIndex (autI hV (thompsonJ H))
    rw [← Subgroup.relIndex_mul_relIndex _ _ _ le_sup_right hle]
    exact h2'.mul_right _
  have hN_le : (K ⊔ S) ⊓ Subgroup.centralizer (V : Set G) ≤ H :=
    inf_le_left.trans (sup_le hKH hSH)
  have hTN' : T ≤ Subgroup.normalizer
      (((K ⊔ S) ⊓ Subgroup.centralizer (V : Set G) : Subgroup G) : Set G) :=
    B2F.le_normalizer_inf (B2F.le_normalizer_sup hTK hTS)
      (B2F.le_normalizer_centralizer (hT.1.trans hHN))
  have hodd := not_two_dvd_relIndex_inf_of_normalizer hT.1 hN_le hT.2.2 hTN'
  have hclaim : T ⊓ ((K ⊔ S) ⊓ Subgroup.centralizer (V : Set G)) =
      S ⊓ Subgroup.centralizer (V : Set G) := by
    apply le_antisymm
    · rintro x ⟨hxT, hxKS, hxC⟩
      refine ⟨⟨hxT, ?_⟩, hxC⟩
      have hxKS' : x ∈ ((K ⊔ S : Subgroup G) : Set G) := hxKS
      rw [Subgroup.coe_mul_of_right_le_normalizer_left _ _ hSK] at hxKS'
      obtain ⟨k, hk, s, hs, rfl⟩ := hxKS'
      show k * s ∈ Subgroup.centralizer (E : Set G)
      rw [hE]
      refine mem_centralizer_sup ?_ ?_
      · exact Subgroup.mem_centralizer_iff.2 fun y hy =>
          Subgroup.mem_centralizer_iff.1 hxC y hy.1
      · refine Subgroup.mem_centralizer_iff.2 fun y hy => ?_
        have e1 := Subgroup.mem_centralizer_iff.1 hy.2 k hk
        have e2 := Subgroup.mem_centralizer_iff.1 hs.2 y hy.1
        calc y * (k * s) = (y * k) * s := by rw [mul_assoc]
          _ = (k * y) * s := by rw [← e1]
          _ = k * (y * s) := by rw [mul_assoc]
          _ = k * (s * y) := by rw [e2]
          _ = (k * s) * y := by rw [mul_assoc]
    · exact fun x hx => ⟨hST hx.1, ⟨Subgroup.mem_sup_right hx.1, hx.2⟩⟩
  have hsylC : IsSylowTwoOf (S ⊓ Subgroup.centralizer (V : Set G))
      ((K ⊔ S) ⊓ Subgroup.centralizer (V : Set G)) := by
    refine ⟨inf_le_inf_right _ le_sup_right, hT.2.1.to_le (inf_le_left.trans hST), ?_⟩
    rw [← hclaim]
    exact hodd
  exact isSylowTwoOf_of_isSylowTwoOf_autI hV (sup_le hKN hSN) le_sup_right
    (hT.2.1.to_le hST) hsylC h2
end Gen

section Final

variable {G : Type} [Group G] [Finite G]

theorem e23ConclGen_of_isSolvable {H T M V : Subgroup G} (hV : IsElemAbelian 2 V)
    (h : MinParabolic H T M) (hsolv : Group.IsSolvable H) (hred : IsTwoReducedIn H V)
    (hJ : ¬ thompsonJ T ≤ Subgroup.centralizer (V : Set G)) : E23ConclGen H T V hV := by
  have hW : ∀ w : IntMod V hV, w ^ 2 = 1 := fun w => IntMod.sq_eq_one w
  obtain ⟨𝓗, I, B⟩ := exists_blocks hV hred hsolv h.isSylow hJ
  have hCL : ∀ L ∈ I, commV L ⊓ fixV (autI hV (twoResidual H)) = ⊥ := by
    intro L hL
    refine le_bot_iff.1 ?_
    rw [commV_eq_commSub, inf_comm]
    calc fixV (autI hV (twoResidual H)) ⊓ commSub (⊤ : Subgroup (IntMod V hV)) L
        ≤ fixV (autI hV (twoResidual H)) ⊓ ⨆ L' ∈ I, commSub (⊤ : Subgroup (IntMod V hV)) L' :=
          inf_le_inf_left _ (le_iSup₂_of_le (f := fun (K : Subgroup (MulAut (IntMod V hV)))
            (_ : K ∈ I) => commSub (⊤ : Subgroup (IntMod V hV)) K) L hL le_rfl)
      _ = ⊥ := fixV_twoResidual_inf_gen B
  refine ⟨twoResidual_le_thompsonJ h hred hJ, I, B.nonempty h.isSylow hred hJ, B.eq,
    fun L hL L' hL' hne a ha b hb => B.comm hL hL' hne ha hb,
    fun L hL L' hL' => B.transitive h hred hJ hL hL', fun L hL => Or.inl ⟨1, ?_⟩, ?_, ?_⟩
  · refine isL2Natural_of_actsAsNaturalL2 ?_ (hCL L hL)
    rw [commV_eq_commSub]
    exact actsAsNaturalL2_of_full hW (B.hb.card_comm L (B.sub hL)) (B.hb.le_stabSub (B.sub hL))
      (B.hb.inf_centSub (B.sub hL)) (B.hb.autSub_eq_top L (B.sub hL))
  · intro _
    obtain ⟨-, hsyl, -⟩ := B2F.structure_of_not_le hV hred hsolv h.isSylow hJ
    exact ⟨autI_baum_gen B h hsolv hred hJ, hsyl, isSylowTwoOf_baum_gen B h hsolv hred hJ⟩
  · intro m hm hsym
    exfalso
    obtain ⟨L, hL⟩ := B.nonempty h.isSylow hred hJ
    obtain ⟨θ, -⟩ := hsym L hL
    have h6 := B.card_eq hL
    rw [Nat.card_congr θ.toEquiv, Nat.card_perm, Nat.card_fin] at h6
    have h4 : 2 ^ 2 ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm
    have h120 : Nat.factorial 5 ≤ Nat.factorial (2 ^ m + 1) := Nat.factorial_le (by omega)
    have : Nat.factorial 5 = 120 := by decide
    omega

end Final

end CFSG.AGLEmbeddingD2.GN
