module

public import CFSG.CGT.PushingUpLit.BHS.Prelim
public import CFSG.CGT.PushingUpLit.BHS.ThreeEightAux
public import CFSG.CGT.PushingUpLit.BHS.ThreeSeven
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.LiftPieceCommon

public section

namespace CFSG.CGT.PushingUpLit.BHS6

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.QuasithinUnique.Setup
  CFSG.QuasithinUnique.Setup.Campbell CFSG.QuasithinUnique.Setup.Lift.Piece
  CFSG.CGT.PushingUpLit.BHS
open scoped LinearAlgebra.Projectivization Pointwise commutatorElement

variable {Γ : Type} [Group Γ] [Finite Γ]

section Frattini

variable {F : Type} [Field F] {G T V M : Subgroup Γ}

theorem mem_of_map_mem_normalizer_gen (hT : IsSylowTwoOf T G)
    (hN : G ⊓ Subgroup.normalizer (T : Set Γ) ≤ M)
    (hVG : G ≤ Subgroup.normalizer (V : Set Γ))
    (hC : G ⊓ Subgroup.centralizer (V : Set Γ) ≤ M)
    (α : ↥G →* Matrix.SpecialLinearGroup (Fin 2) F)
    (hαk : α.ker = (Subgroup.centralizer (V : Set Γ)).subgroupOf G)
    {g : Γ} (hg : g ∈ G)
    (hgn : α ⟨g, hg⟩ ∈ Subgroup.normalizer (((T.subgroupOf G).map α : Subgroup _) : Set _)) :
    g ∈ M := by
  classical
  set K : Subgroup Γ := G ⊓ Subgroup.centralizer (V : Set Γ) with hK
  have hKG : K ≤ G := inf_le_left
  have hGK : G ≤ Subgroup.normalizer (K : Set Γ) := le_normalizer_inf_centralizer hVG
  have hTK : T ≤ Subgroup.normalizer (K : Set Γ) := hT.1.trans hGK
  have hker : ∀ (x : Γ) (hx : x ∈ G), α ⟨x, hx⟩ = 1 ↔ x ∈ K := by
    intro x hx
    rw [← MonoidHom.mem_ker, hαk, Subgroup.mem_subgroupOf]
    exact ⟨fun h => ⟨hx, h⟩, fun h => h.2⟩
  set T' : Subgroup Γ := T ⊔ K with hT'
  have hT'G : T' ≤ G := sup_le hT.1 hKG
  have hT'mul : ((T' : Subgroup Γ) : Set Γ) = (T : Set Γ) * (K : Set Γ) :=
    Subgroup.coe_mul_of_left_le_normalizer_right T K hTK
  have hcl : ∀ (x : Γ) (hx : x ∈ G), α ⟨x, hx⟩ ∈
      Subgroup.normalizer (((T.subgroupOf G).map α : Subgroup _) : Set _) →
      ∀ y ∈ T', x * y * x⁻¹ ∈ T' := by
    intro x hx hxn y hy
    have hy' : y ∈ ((T' : Subgroup Γ) : Set Γ) := hy
    rw [hT'mul] at hy'
    obtain ⟨t, ht, k, hk, rfl⟩ := hy'
    have htG : t ∈ G := hT.1 ht
    have hkG : k ∈ G := hKG hk
    have hxkx : x * k * x⁻¹ ∈ K := by
      have := (Subgroup.mem_normalizer_iff.mp (hGK hx) k).mp hk
      exact this
    have hxtx : x * t * x⁻¹ ∈ T' := by
      have hxtxG : x * t * x⁻¹ ∈ G := G.mul_mem (G.mul_mem hx htG) (G.inv_mem hx)
      have himg : α ⟨t, htG⟩ ∈ ((T.subgroupOf G).map α : Subgroup _) :=
        ⟨⟨t, htG⟩, Subgroup.mem_subgroupOf.mpr ht, rfl⟩
      have h1 := (Subgroup.mem_normalizer_iff.mp hxn (α ⟨t, htG⟩)).mp himg
      obtain ⟨u, hu, hu'⟩ := h1
      have hu2 : (u : Γ) ∈ T := Subgroup.mem_subgroupOf.mp hu
      have heq : α u = α ⟨x * t * x⁻¹, hxtxG⟩ := by
        rw [hu']
        have e : (⟨x * t * x⁻¹, hxtxG⟩ : G) = ⟨x, hx⟩ * ⟨t, htG⟩ * ⟨x, hx⟩⁻¹ := rfl
        rw [e, map_mul, map_mul, map_inv]
      have hdiv : (u : Γ)⁻¹ * (x * t * x⁻¹) ∈ K := by
        rw [← hker _ (G.mul_mem (G.inv_mem u.2) hxtxG)]
        have : α (u⁻¹ * ⟨x * t * x⁻¹, hxtxG⟩) = 1 := by
          rw [map_mul, map_inv, heq, inv_mul_cancel]
        exact this
      have : x * t * x⁻¹ = (u : Γ) * ((u : Γ)⁻¹ * (x * t * x⁻¹)) := by group
      rw [this]
      exact T'.mul_mem (Subgroup.mem_sup_left hu2) (Subgroup.mem_sup_right hdiv)
    have : x * (t * k) * x⁻¹ = (x * t * x⁻¹) * (x * k * x⁻¹) := by group
    rw [this]
    exact T'.mul_mem hxtx (Subgroup.mem_sup_right hxkx)
  have hnormT' : g ∈ Subgroup.normalizer (T' : Set Γ) := by
    have hgn' : α ⟨g⁻¹, G.inv_mem hg⟩ ∈
        Subgroup.normalizer (((T.subgroupOf G).map α : Subgroup _) : Set _) := by
      have e : α ⟨g⁻¹, G.inv_mem hg⟩ = (α ⟨g, hg⟩)⁻¹ := by rw [← map_inv]; rfl
      rw [e]
      exact inv_mem hgn
    rw [Subgroup.mem_normalizer_iff]
    intro y
    refine ⟨hcl g hg hgn y, fun hy => ?_⟩
    have := hcl g⁻¹ (G.inv_mem hg) hgn' _ hy
    simpa [mul_assoc] using this
  have hH : IsSylowTwoOf T T' := isSylowTwoOf_of_le hT le_sup_left hT'G
  have hfr := B6.frattini_two (H := G ⊓ Subgroup.normalizer (T' : Set Γ)) (N := T') (S := T)
    (le_inf hT'G Subgroup.le_normalizer) inf_le_right hH
  have hgmem : g ∈ G ⊓ Subgroup.normalizer (T' : Set Γ) := ⟨hg, hnormT'⟩
  have hgfr := hfr hgmem
  have hTC : T ≤ M := fun t ht => hN ⟨hT.1 ht, Subgroup.le_normalizer ht⟩
  have hT'C : T' ≤ M := sup_le hTC hC
  have hHC : (G ⊓ Subgroup.normalizer (T' : Set Γ)) ⊓ Subgroup.normalizer (T : Set Γ) ≤ M :=
    fun x hx => hN ⟨hx.1.1, hx.2⟩
  have hsup : T' ⊔ ((G ⊓ Subgroup.normalizer (T' : Set Γ)) ⊓ Subgroup.normalizer (T : Set Γ)) ≤
      M := sup_le hT'C hHC
  exact hsup hgfr

end Frattini

section Root

variable {F : Type} [Field F] [Finite F] [CharP F 2] {G T V M : Subgroup Γ}

theorem map_eq_top_of_not_le_gen (hT : IsSylowTwoOf T G)
    (hN : G ⊓ Subgroup.normalizer (T : Set Γ) ≤ M)
    (hVG : G ≤ Subgroup.normalizer (V : Set Γ))
    (hC : G ⊓ Subgroup.centralizer (V : Set Γ) ≤ M)
    (α : ↥G →* Matrix.SpecialLinearGroup (Fin 2) F) (hα : Function.Surjective α)
    (hαk : α.ker = (Subgroup.centralizer (V : Set Γ)).subgroupOf G)
    {X : Subgroup Γ} (hTX : T ≤ X ⊔ (G ⊓ Subgroup.centralizer (V : Set Γ))) (hXG : X ≤ G)
    (hX : ¬ X ≤ M) :
    (X.subgroupOf G).map α = ⊤ := by
  obtain ⟨ℓ, hℓ⟩ := exists_rootGrp_eq_map_of_isSylowTwoOf hT α hα
  have hle : rootGrp ℓ ≤ (X.subgroupOf G).map α := by
    rw [← hℓ]
    rintro _ ⟨t, ht, rfl⟩
    have htT : (t : Γ) ∈ T := Subgroup.mem_subgroupOf.mp ht
    have hmem : (t : Γ) ∈ ((X ⊔ (G ⊓ Subgroup.centralizer (V : Set Γ)) : Subgroup Γ) : Set Γ) :=
      hTX htT
    rw [Subgroup.coe_mul_of_left_le_normalizer_right X (G ⊓ Subgroup.centralizer (V : Set Γ))
      (hXG.trans (le_normalizer_inf_centralizer hVG))] at hmem
    obtain ⟨x, hx, k, hk, hxk⟩ := hmem
    have hxG : x ∈ G := hXG hx
    have hkα : α ⟨k, hk.1⟩ = 1 := (map_eq_one_iff_centralizer α hαk hk.1).mpr hk.2
    refine ⟨⟨x, hxG⟩, Subgroup.mem_subgroupOf.mpr hx, ?_⟩
    have e : t = ⟨x, hxG⟩ * ⟨k, hk.1⟩ := Subtype.ext hxk.symm
    rw [e, map_mul, hkα, mul_one]
  refine eq_top_of_rootGrp_le hle ?_
  by_contra hcon
  push Not at hcon
  apply hX
  intro x hx
  have hxG : x ∈ G := hXG hx
  have hmem : α ⟨x, hxG⟩ ∈ (X.subgroupOf G).map α :=
    ⟨⟨x, hxG⟩, Subgroup.mem_subgroupOf.mpr hx, rfl⟩
  refine mem_of_map_mem_normalizer_gen hT hN hVG hC α hαk hxG ?_
  rw [hℓ, mem_normalizer_rootGrp_iff]
  exact hcon _ hmem

end Root

section Baum

variable {G T V M : Subgroup Γ}

theorem baum_not_le_centralizer_gen (hT : IsSylowTwoOf T G)
    (hVG : G ≤ Subgroup.normalizer (V : Set Γ))
    (hbN : G ⊓ Subgroup.normalizer (baum T : Set Γ) ≤ M)
    (hC : G ⊓ Subgroup.centralizer (V : Set Γ) ≤ M) (hMG : M ≤ G) (hne : M ≠ G) :
    ¬ baum T ≤ Subgroup.centralizer (V : Set Γ) := by
  intro hb
  set N : Subgroup Γ := G ⊓ Subgroup.centralizer (V : Set Γ) with hN
  have hNG : N ≤ G := inf_le_left
  have hGN : G ≤ Subgroup.normalizer (N : Set Γ) := fun g hg =>
    Subgroup.inf_normalizer_le_normalizer_inf
      ⟨Subgroup.le_normalizer hg, B6.le_normalizer_centralizer hVG hg⟩
  have hsyl : IsSylowTwoOf (T ⊓ N) N := B6.isSylowTwoOf_inf_normal hT hNG hGN
  have hbTN : baum T ≤ T ⊓ N :=
    le_inf inf_le_left (le_inf (inf_le_left.trans hT.1) hb)
  have hbeq : baum T = baum (T ⊓ N) := baum_eq_of_le hbTN inf_le_left
  have hfr := B6.frattini_two hNG hGN hsyl
  apply hne
  refine le_antisymm hMG fun g hg => ?_
  have hKN : G ⊓ Subgroup.normalizer ((T ⊓ N : Subgroup Γ) : Set Γ) ≤
      Subgroup.normalizer (N : Set Γ) := inf_le_left.trans hGN
  have hg' : g ∈ ((G ⊓ Subgroup.normalizer ((T ⊓ N : Subgroup Γ) : Set Γ) ⊔ N : Subgroup Γ) :
      Set Γ) := by
    rw [sup_comm]
    exact hfr hg
  rw [Subgroup.coe_mul_of_left_le_normalizer_right _ N hKN] at hg'
  obtain ⟨m, hm, n, hn, rfl⟩ := hg'
  refine mul_mem ?_ (hC hn)
  refine hbN ⟨hm.1, ?_⟩
  have := normalizer_le_normalizer_baum (T ⊓ N) hm.2
  rwa [← hbeq] at this

end Baum

section Main

variable {F : Type} [Field F] [Finite F] [CharP F 2]

theorem exists_pushUp_parabolics_gen {G T V M : Subgroup Γ}
    (hG : CharTwo G) (hT : IsSylowTwoOf T G) (hMG : M ≤ G) (hne : M ≠ G)
    (hN : G ⊓ Subgroup.normalizer (T : Set Γ) ≤ M)
    (hchN : ∀ C : Subgroup Γ, C ≤ baum T → C ≠ ⊥ → (C.subgroupOf (baum T)).Characteristic →
      G ⊓ Subgroup.normalizer (C : Set Γ) ≤ M)
    (hC : G ⊓ Subgroup.centralizer (V : Set Γ) ≤ M)
    (hVn : G ≤ Subgroup.normalizer (V : Set Γ))
    (hVQ : V ≤ omegaOneCenterOf (pCoreOf 2 G))
    (α : ↥G →* Matrix.SpecialLinearGroup (Fin 2) F) (hα : Function.Surjective α)
    (hαk : α.ker = (Subgroup.centralizer (V : Set Γ)).subgroupOf G)
    (β : ↥V →* Multiplicative (Fin 2 → F)) (hβ : Function.Surjective β)
    (hβe : ∀ (g : ↥G) (v v' : ↥V), (v' : Γ) = g * v * g⁻¹ →
      Multiplicative.toAdd (β v') =
        (α g : Matrix (Fin 2) (Fin 2) F).mulVec (Multiplicative.toAdd (β v)))
    (hβk : β.ker = (Subgroup.centralizer (G : Set Γ)).subgroupOf V) :
    ∃ P' : Subgroup Γ, P' ≤ G ∧ baum T ≤ P' ∧ V ≤ P' ∧ IsSylowTwoOf (baum T) P' ∧
      IsMinParabolic2 (baum T) P' ∧ CharTwo P' ∧ (P'.subgroupOf G).map α = ⊤ ∧
      (∀ C : Subgroup Γ, C ≤ baum T → C ≠ ⊥ → (C.subgroupOf (baum T)).Characteristic →
        ¬ P' ≤ Subgroup.normalizer (C : Set Γ)) ∧
      (∀ t ∈ T, ∃ b ∈ baum T, b⁻¹ * t ∈ Subgroup.centralizer (V : Set Γ)) ∧
      ¬ thompsonJ (baum T) ≤ Subgroup.centralizer (V : Set Γ) := by
  classical
  have hT2 : IsPGroup 2 T := hT.2.1
  have hT0 : T ≠ ⊥ := by
    rintro rfl
    apply hne
    refine le_antisymm hMG fun g hg => hN ⟨hg, ?_⟩
    show g ∈ Subgroup.normalizer (((⊥ : Subgroup Γ)) : Set Γ)
    rw [Subgroup.mem_normalizer_iff]
    intro h
    simp
  have hTM : T ≤ M := fun t ht => hN ⟨hT.1 ht, Subgroup.le_normalizer ht⟩
  have hOT : pCoreOf 2 G ≤ T := hT.pCoreOf_le
  have hVQ' : V ≤ pCoreOf 2 G := hVQ.trans (C1GN.omegaOneCenterOf_le_self _)
  have hVT' : V ≤ T := hVQ'.trans hOT
  have hVe : IsElemAbelian 2 V := isElemAbelian_of_le' hVQ (isElemAbelian_omegaOneCenterOf' _)
  have hb0 : baum T ≠ ⊥ := C1GN.baum_ne_bot hT2 hT0
  have hbN : G ⊓ Subgroup.normalizer (baum T : Set Γ) ≤ M := by
    refine hchN (baum T) le_rfl hb0 ?_
    rw [Subgroup.subgroupOf_self]
    infer_instance
  obtain ⟨P, hTP, hPG, hPC, hmin⟩ := exists_minimal_not_le (S := T) (Y := G) (M := M)
    hT.1 (fun h => hne (le_antisymm hMG h))
  have hnnP : ¬ P ≤ Subgroup.normalizer (T : Set Γ) := fun hPN =>
    hPC fun x hx => hN ⟨hPG hx, hPN hx⟩
  have hminP : IsMinParabolic2 T P :=
    isMinParabolic2_of_minimal_gen (isSylowTwoOf_of_le hT hTP hPG) hTM hnnP hPC hmin
  have hVP : V ≤ P := hVT'.trans hTP
  have hVnP : P ≤ Subgroup.normalizer (V : Set Γ) := hPG.trans hVn
  have hPtop : (P.subgroupOf G).map α = ⊤ :=
    map_eq_top_of_not_le_gen hT hN hVn hC α hα hαk (le_sup_of_le_left hTP) hPG hPC
  obtain ⟨hαP, hαkP, hβeP, hβkP⟩ := natural_data_restrict α hαk β hβe hβk hPG hPtop
  have hbaum : ¬ baum T ≤ Subgroup.centralizer (V : Set Γ) :=
    baum_not_le_centralizer_gen hT hVn hbN hC hMG hne
  have hJ : ¬ thompsonJ T ≤ Subgroup.centralizer (V : Set Γ) :=
    thompsonJ_not_le_centralizer hVT' hVe hbaum
  obtain ⟨hSylH₀, hVH₀, hαH₀, hTSC⟩ :=
    three_seven_linear hminP hVP hVe hVnP (α.comp (Subgroup.inclusion hPG)) hαP hαkP β hβ hβeP
      hβkP hJ
  have hSP : baum T ≤ twoResidual P ⊔ baum T := le_sup_right
  have hH₀P : twoResidual P ⊔ baum T ≤ P :=
    sup_le (twoResidual_le P) ((inf_le_left : baum T ≤ T).trans hTP)
  have hH₀C : ¬ twoResidual P ⊔ baum T ≤ M := by
    intro h
    apply map_cStarIn_ne_top hMG α hαk hC hne
    refine top_unique fun A _ => ?_
    obtain ⟨x, hxH, hxA⟩ := hαH₀ A
    exact ⟨⟨x, hPG x.2⟩, Subgroup.mem_subgroupOf.mpr (h hxH), hxA⟩
  obtain ⟨P', hSP', hP'H₀, hP'C, hminP'⟩ := exists_minimal_not_le (S := baum T)
    (Y := twoResidual P ⊔ baum T) (M := M) hSP hH₀C
  have hP'P : P' ≤ P := hP'H₀.trans hH₀P
  have hP'G : P' ≤ G := hP'P.trans hPG
  have hSylP' : IsSylowTwoOf (baum T) P' := isSylowTwoOf_of_le hSylH₀ hSP' hP'H₀
  have hP'T : P' ⊔ T = P := by
    by_contra hne'
    have hlt : P' ⊔ T < P := lt_of_le_of_ne (sup_le hP'P hTP) hne'
    exact hP'C (le_sup_left.trans (hmin (P' ⊔ T) le_sup_right hlt))
  have hTn : T ≤ Subgroup.normalizer (baum T : Set Γ) :=
    Subgroup.le_normalizer.trans (normalizer_le_normalizer_baum T)
  have hnn' : ¬ P' ≤ Subgroup.normalizer (baum T : Set Γ) := by
    intro hn
    apply hPC
    have : P ≤ Subgroup.normalizer (baum T : Set Γ) := hP'T ▸ sup_le hn hTn
    exact fun x hx => hbN ⟨hPG hx, this hx⟩
  have hSC : baum T ≤ M := (inf_le_left : baum T ≤ T).trans hTM
  have hminP'' : IsMinParabolic2 (baum T) P' :=
    isMinParabolic2_of_minimal_gen hSylP' hSC hnn' hP'C hminP'
  have hαP'top : (P'.subgroupOf G).map α = ⊤ := by
    refine map_eq_top_of_not_le_gen hT hN hVn hC α hα hαk ?_ hP'G hP'C
    intro t ht
    obtain ⟨b, hb, hbt⟩ := hTSC t ht
    have htG : t ∈ G := hT.1 ht
    have hbG : b ∈ G := hT.1 ((inf_le_left : baum T ≤ T) hb)
    have e : t = b * (b⁻¹ * t) := by group
    rw [e]
    exact Subgroup.mul_mem_sup (hSP' hb) ⟨G.mul_mem (G.inv_mem hbG) htG, hbt⟩
  have hVH₀n : twoResidual P ⊔ baum T ≤ Subgroup.normalizer (V : Set Γ) := hH₀P.trans hVnP
  have hVS : V ≤ baum T :=
    (le_pCoreOf_of_normalizes (p := 2) hVH₀ hVH₀n (hT2.to_le hVT')).trans hSylH₀.pCoreOf_le
  have hVP' : V ≤ P' := hVS.trans hSP'
  have hcharP : CharTwo P := two_two_core hG (hOT.trans hTP) hPG
  have hTnH₀ : T ≤ Subgroup.normalizer ((twoResidual P ⊔ baum T : Subgroup Γ) : Set Γ) := by
    intro t ht
    have h1 : t ∈ Subgroup.normalizer (twoResidual P : Set Γ) :=
      le_normalizer_twoResidual P (hTP ht)
    exact C1.mem_normalizer_sup h1 (hTn ht)
  have hTsylP : IsSylowTwoOf T P := isSylowTwoOf_of_le hT hTP hPG
  have hcharH₀ : CharTwo (twoResidual P ⊔ baum T) :=
    two_two_normalizes hcharP hH₀P (hTsylP.pCoreOf_le.trans hTnH₀)
  have hcharP' : CharTwo P' := two_two_core hcharH₀ (hSylH₀.pCoreOf_le.trans hSP') hP'H₀
  refine ⟨P', hP'G, hSP', hVP', hSylP', hminP'', hcharP', hαP'top, ?_, hTSC, ?_⟩
  · intro C hCS hC0 hCchar hn
    apply hPC
    have hTC' : T ≤ Subgroup.normalizer (C : Set Γ) :=
      hTn.trans (normalizer_le_normalizer_of_char' hCS hCchar)
    have hPn : P ≤ Subgroup.normalizer (C : Set Γ) := hP'T ▸ sup_le hn hTC'
    intro x hx
    exact hchN C hCS hC0 hCchar ⟨hPG hx, hPn hx⟩
  · rw [B6.thompsonJ_eq_of_le (B6.thompsonJ_le_baum T) inf_le_left]
    exact hJ

end Main

end CFSG.CGT.PushingUpLit.BHS6
