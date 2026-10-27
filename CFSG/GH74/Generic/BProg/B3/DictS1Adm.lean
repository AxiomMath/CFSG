module

public import CFSG.GH74.Generic.BProg.B1.PilotS1Three

public section

namespace CFSG.GH74.Generic.BProg.B3

open CFSG CFSG.GH74 CFSG.GH74.L5U5 CFSG.GH74.GLS CFSG.GH74.Generic CFSG.GH74.Generic.S3 CFSG.GH74.Generic.BProg
  CFSG.GH74.Generic.BProg.B1 CFSG.GH74.Generic.BProg.B1.PilotS1 CFSG.GH74.Generic.BProg.B1.PilotS5 Subgroup

variable {G : Type} [Group G] [Finite G]

theorem isAdmPair_of_splitAt {F' : Type} [Field F'] [Finite F'] {x y : G} {K A : Subgroup G}
    {Lb J₂ : Subgroup (CentralizerBar x)} (hodd : Odd (Nat.card F')) (hbig : 4 ≤ Nat.card F')
    (hx : orderOf x = 2) (hK : IsPCompIn 2 (centralizer ({x} : Set G)) K)
    (hY : Split1Like F' (imgBar x K) (xbar x))
    (hCY : ∀ w ∈ centralizer ((imgBar x K : Subgroup (CentralizerBar x)) : Set (CentralizerBar x)),
      w = 1 ∨ w = xbar x)
    (hAK : A ≤ K) (hAel : CFSG.IsElementaryAbelian 2 ↥A) (hA8 : Nat.card ↥A = 8) (hxA : x ∈ A)
    (hyA : y ∈ A) (hy2 : orderOf y = 2) (hyne : bar x y ∉ zpowers (xbar x))
    (hS : SplitAt F' (imgBar x K) (xbar x) (bar x y) Lb J₂) : IsAdmPair x K A y Lb := by
  classical
  have _hA := hAel
  have _hA8 := hA8
  have hKC : K ≤ centralizer ({x} : Set G) := hK.1
  have hxC : x ∈ centralizer ({x} : Set G) := Subgroup.mem_centralizer_singleton_iff.2 rfl
  have hyK : y ∈ K := hAK hyA
  have hyC : y ∈ centralizer ({x} : Set G) := hKC hyK
  have hxy : x * y = y * x := (Subgroup.mem_centralizer_singleton_iff.1 hyC).symm
  have hxyne : x ≠ y := by
    rintro rfl
    apply hyne
    rw [bar_of_mem hxC]
    exact Subgroup.mem_zpowers _
  obtain ⟨hbmem, -, -⟩ := bar_facts hKC hyK hy2
  obtain ⟨hDA, hDC, hDel, hDrank, hDcomm⟩ := D_facts hx hy2 hxy hxyne hxA hyA (hAK.trans hKC)
  have hLD := centralizes_Dbar hyC (fun l hl => (hS.le₁ hl).1)
  have hLself : pLayerOf 2 (centralizer ((imgBar x (closure ({x, y} : Set G)) :
      Subgroup (CentralizerBar x)) : Set (CentralizerBar x)) ⊓ Lb) = Lb := by
    rw [inf_eq_right.2 hLD]
    exact le_antisymm (sSup_le fun L' hL' => hL'.1) (le_sSup (hS.isPCompIn_self₁ hodd hbig))
  refine ⟨⟨hyC, hy2, hyne, hY.subtermRel hodd hbig hCY hbmem hS,
    fun _ => ⟨hS.isPCompIn₁ hodd hbig, fun L' hL' _ => hS.card_le_of_isPCompIn hodd hbig hL'⟩⟩,
    closure ({x, y} : Set G), Lb, ⟨hDA, hDel, hDrank⟩, Or.inl ⟨⟨hyC, hy2, hyne, hDC, hDel,
      fun d hd => Subgroup.le_normalizer hd, ?_⟩, Subgroup.le_normalizer hyK,
      hS.pLayerOf_ne_bot hodd hbig, hS.isPCompIn₁ hodd hbig, ?_⟩⟩
  · rw [inf_eq_left.2 hDcomm]
    exact hDrank
  · rw [hLself]
    exact hS.isPCompIn_self₁ hodd hbig

theorem isAdmPair_of_splitAt_three {F' : Type} [Field F'] [Finite F'] {x y : G} {K A : Subgroup G}
    {J₁ J₂ : Subgroup (CentralizerBar x)} (hF3 : Nat.card F' = 3)
    (hx : orderOf x = 2) (hK : IsPCompIn 2 (centralizer ({x} : Set G)) K)
    (hY : Split1Like F' (imgBar x K) (xbar x))
    (hCY : ∀ w ∈ centralizer ((imgBar x K : Subgroup (CentralizerBar x)) : Set (CentralizerBar x)),
      w = 1 ∨ w = xbar x)
    (hSq : IsQuasisimple ↥(imgBar x K)) (hSZ : Nat.card ↥(center ↥(imgBar x K)) = 2)
    (hAK : A ≤ K) (hAel : CFSG.IsElementaryAbelian 2 ↥A) (hA8 : Nat.card ↥A = 8) (hxA : x ∈ A)
    (hyA : y ∈ A) (hy2 : orderOf y = 2) (hyne : bar x y ∉ zpowers (xbar x))
    (hS : SplitAt F' (imgBar x K) (xbar x) (bar x y) J₁ J₂) : IsAdmPair x K A y J₁ := by
  classical
  have _hA := hAel
  have _hA8 := hA8
  have hKC : K ≤ centralizer ({x} : Set G) := hK.1
  have hxC : x ∈ centralizer ({x} : Set G) := Subgroup.mem_centralizer_singleton_iff.2 rfl
  have hyK : y ∈ K := hAK hyA
  have hyC : y ∈ centralizer ({x} : Set G) := hKC hyK
  have hxy : x * y = y * x := (Subgroup.mem_centralizer_singleton_iff.1 hyC).symm
  have hxyne : x ≠ y := by
    rintro rfl
    apply hyne
    rw [bar_of_mem hxC]
    exact Subgroup.mem_zpowers _
  obtain ⟨hbmem, -, hb2⟩ := bar_facts hKC hyK hy2
  obtain ⟨hDA, hDC, hDel, hDrank, hDcomm⟩ := D_facts hx hy2 hxy hxyne hxA hyA (hAK.trans hKC)
  have hLD := centralizes_Dbar hyC (fun l hl => (hS.le₁ hl).1)
  have hsolv := hS.isSolv2CompIn₁ hF3
  have hPL := hS.pLayerOf_eq_bot_three hF3
  have hbb : bar x y * bar x y = 1 := by
    have h := pow_orderOf_eq_one (bar x y)
    rw [hb2, pow_two] at h
    exact h
  have hJ₁S : J₁ ≤ imgBar x K := fun l hl => (hS.le₁ hl).2
  have hJ₁ne : J₁ ≠ ⊥ := by
    intro hbot
    have h1 := hS.u_mem
    rw [hbot, Subgroup.mem_bot] at h1
    rw [h1, orderOf_one] at hb2
    exact absurd hb2 (by norm_num)
  have hsetup : Setup1E x y (closure ({x, y} : Set G)) :=
    ⟨hyC, hy2, hyne, hDC, hDel, fun d hd => Subgroup.le_normalizer hd, by
      rw [inf_eq_left.2 hDcomm]; exact hDrank⟩
  have hyD : y ∈ closure ({x, y} : Set G) := Subgroup.subset_closure (by simp)
  have hcentE : ∀ e ∈ closure ({x, y} : Set G), e * y = y * e := fun e he =>
    congrArg Subtype.val ((IsMulCommutative.is_comm (M := ↥(closure ({x, y} : Set G)))).comm
      ⟨e, he⟩ ⟨y, hyD⟩)
  have hlayer : extLayer2 (centralizer ({bar x y} : Set (CentralizerBar x)) ⊓ imgBar x K) ≠ ⊥ := by
    intro hbot
    have h1 : J₁ ≤ extLayer2 (centralizer ({bar x y} : Set (CentralizerBar x)) ⊓ imgBar x K) :=
      le_sup_of_le_right (le_iSup₂_of_le J₁ hsolv le_rfl)
    rw [hbot, le_bot_iff] at h1
    exact hJ₁ne h1
  have hinvL : ∀ e ∈ imgBar x (closure ({x, y} : Set G)),
      e ∈ normalizer (J₁ : Set (CentralizerBar x)) := fun e he =>
    Subgroup.centralizer_le_normalizer _ (Subgroup.mem_centralizer_iff.2 fun l hl =>
      (Subgroup.mem_centralizer_iff.1 (hLD hl) e he).symm)
  have hsolvI : IsSolv2CompIn (extLayer2 (centralizer ((imgBar x (closure ({x, y} : Set G)) :
      Subgroup (CentralizerBar x)) : Set (CentralizerBar x)) ⊓ J₁)) J₁ := by
    rw [inf_eq_right.2 hLD, hS.extLayer2_eq_three hF3]
    exact hS.isSolv2CompIn_self hF3
  have hSx : centralizer ({xbar x} : Set (CentralizerBar x)) ⊓ imgBar x K = imgBar x K :=
    inf_eq_right.2 fun g _ => Subgroup.mem_centralizer_singleton_iff.2 (xbar_comm x g)
  have hSpc : IsPCompIn 2 (imgBar x K) (imgBar x K) := by
    have hO := pPrimeCore_eq_bot_of_quasisimple hSq hSZ
    refine ⟨le_rfl, ?_⟩
    rw [Subgroup.subgroupOf_self]
    exact isPComponent_of_pPrimeCore_eq_bot hO inferInstance
      (CFSG.LocalCores.isQuasisimple_of_mulEquiv Subgroup.topEquiv.symm hSq)
  have hres_le : oPrimeResidualOf 2 J₁ ≤ J₁ := Subgroup.map_subtype_le _
  have hexists : ∀ e ∈ imgBar x (closure ({x, y} : Set G)), e ≠ 1 → ∃ Ie : Subgroup (CentralizerBar x),
      IsQuasi2CompIn (centralizer ({e} : Set (CentralizerBar x)) ⊓ imgBar x K) Ie ∧
        oPrimeResidualOf 2 J₁ ≤ Ie := by
    intro e he hne
    rcases mem_imgBar_pair hx hy2 hxy hxyne hyC he with h | h | h | h
    · exact absurd h hne
    · refine ⟨imgBar x K, Or.inl ?_, hres_le.trans hJ₁S⟩
      rw [h, hSx]
      exact hSpc
    · exact ⟨J₁, Or.inr (by rw [h]; exact hsolv), hres_le⟩
    · exact ⟨J₁, Or.inr (by rw [h, hY.centralizer_mul_eq]; exact hsolv), hres_le⟩
  have hcond6 : ∀ e ∈ imgBar x (closure ({x, y} : Set G)), e ≠ 1 →
      ∀ Ie : Subgroup (CentralizerBar x),
        IsQuasi2CompIn (centralizer ({e} : Set (CentralizerBar x)) ⊓ imgBar x K) Ie →
          oPrimeResidualOf 2 J₁ ≤ Ie →
            IsSolv2CompIn (centralizer ({e} : Set (CentralizerBar x)) ⊓ imgBar x K) Ie →
              (∃ l ∈ Ie, orderOf l = 2 ∧ ∀ k ∈ imgBar x K, e * k * e⁻¹ = l * k * l⁻¹) ∨
                NotDirectFactor6b (centralizer ({e} : Set (CentralizerBar x)) ⊓ imgBar x K) Ie := by
    intro e he hne Ie _ hres hIe
    have hlmem : bar x y ∈ Ie := hres (mem_oPrimeResidualOf_of_two hS.u_mem hbb)
    rcases mem_imgBar_pair hx hy2 hxy hxyne hyC he with h | h | h | h
    · exact absurd h hne
    · exfalso
      rw [h, hSx] at hIe
      exact not_isSolv2CompIn_of_quasisimple hSq hSZ hIe
    · exact Or.inl ⟨bar x y, hlmem, hb2, fun k _ => by rw [h]⟩
    · refine Or.inl ⟨bar x y, hlmem, hb2, fun k _ => ?_⟩
      rw [h]
      have hc := xbar_comm x (bar x y * k * (bar x y)⁻¹)
      calc xbar x * bar x y * k * (xbar x * bar x y)⁻¹
          = xbar x * (bar x y * k * (bar x y)⁻¹) * (xbar x)⁻¹ := by group
        _ = bar x y * k * (bar x y)⁻¹ := mul_inv_eq_iff_eq_mul.2 hc.symm
  exact ⟨⟨hyC, hy2, hyne, hY.subtermRel_three hF3 hCY hbmem hS,
    fun hne => absurd hPL hne⟩, closure ({x, y} : Set G), J₁, ⟨hDA, hDel, hDrank⟩,
    Or.inr ⟨hsetup, Subgroup.le_normalizer hyK, hcentE, hlayer, Or.inr hsolv, hinvL, hsolvI,
      hexists, hcond6⟩⟩

end CFSG.GH74.Generic.BProg.B3
