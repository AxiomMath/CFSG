module

public import CFSG.GH74.QTGen4.DCopy.Quasithin.EmptyFaithful.S152He12E
public import CFSG.GH74.QTGen4.DCopy.Quasithin.EmptyFaithful.S152L27
public import CFSG.GH74.QTGen4.DCopy.Quasithin.EmptyFaithful.S152L27E
public import CFSG.GH74.QTGen4.DCopy.Quasithin.EmptyFaithful.S152L27Main
public import CFSG.Quasithin.EmptyFaithful.S152He12D
public import CFSG.Quasithin.EmptyFaithful.S152He5Consumer
public import CFSG.Quasithin.EmptyFaithful.S152He5Defs
public import CFSG.Quasithin.EmptyFaithful.S152L27
public import CFSG.Quasithin.EmptyFaithful.S152L27D
public import CFSG.Quasithin.EmptyFaithful.S152L27F
public import CFSG.Quasithin.EmptyFaithful.S152L27G
public import CFSG.Quasithin.EmptyFaithful.S152L27Insp
public import CFSG.Quasithin.EmptyFaithful.S152L27Main

public section

namespace CFSG.Quasithin

namespace He12

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.S152N CFSG.Quasithin.S152N2
open scoped Pointwise

theorem stageLemma15227TwoW_of_good_F4 (h1519 : StageLemma1519) (h15111 : StageLemma15111)
    (h15201 : StageLemma15201_F4) (h15208 : StageLemma15208_F4) (h15209 : StageNotation15209_F4)
    (h15211 : StageLemma15211_F4) (h15212 : StageLemma15212W_F4) (h15213 : StageLemma15213_F4)
    (h15214 : StageLemma15214_F4) (hTrans : Insp15227Trans) (hParGood : Insp15227ParGood)
    (hShape : Insp15227Shape) :
    StageLemma15227Two_F4 := by
  intro G _ _ T Mc M hs
  by_contra hV
  set V : Subgroup G := V154 T Mc M with hVdef
  have hTMc : T ≤ Mc := hs.qtfe.t_le_mc
  have hTM : T ≤ M := hs.mf.1.1.2
  obtain ⟨H, hH⟩ := exists_isHStar hs.qtfe.inM_mc hs.mf.1.1 hs.mf.2.1.symm
  obtain ⟨B₀, hB₀, hB₀uniq, hB₀prop⟩ := (h15213 G T Mc M hs H hH).exists_B0
  obtain ⟨B, hB⟩ := (h15209 G T Mc M hs H hH).sigmaPrime_nonempty
  have h14 := h15214 G T Mc M hs B₀ hB₀
  have h11 := h15211 G T Mc M hs H hH B hB
  have h12 := h15212 G T Mc M hs H hH B hB
  have h1519c := h1519 G T Mc M hs.qtfe hs.mf hs.ce
  have hV16 : Nat.card (V154 T Mc M) = 16 := (h15201 G T Mc M hs).card
  have hT2 : IsPGroup 2 T := hs.qtfe.sylow.1
  have hsyl : ∀ P : Subgroup G, T ≤ P → IsSylowTwoOf T P := fun P hTP =>
    isSylowTwoOf_of_le151 hs.qtfe.sylow hTP
  have hchar : CharTwo Mc :=
    charTwo_of_inH' hs.qtfe.qtke hs.qtfe.sylow (inH_of_inM hs.qtfe.inM_mc)

  set Z : Subgroup G := quasithinOmegaOneCenter T with hZdef
  set ZS : Subgroup G := zSOf T Mc M B₀ with hZSdef
  set K : Subgroup G := oTwoUpper H with hKdef
  set Kc : Subgroup G := conjClosure K Mc with hKcdef
  set Q : Subgroup G := pCoreOf 2 Mc with hQdef
  set X : Subgroup G := Kc ⊔ T with hXdef

  have hHMc : H ≤ Mc := (h1519c.three H hH).1.trans (h1519c.three H hH).2
  have hKMc : K ≤ Mc := (oTwoUpper_le H).trans hHMc
  have hKcMc : Kc ≤ Mc := conjClosure_le fun h hh z hz =>
    Mc.mul_mem (Mc.mul_mem hh (hKMc hz)) (Mc.inv_mem hh)
  have hMcn : Mc ≤ Subgroup.normalizer (Kc : Set G) := le_normalizer_conjClosure K Mc
  have hXMc : X ≤ Mc := sup_le hKcMc hTMc
  have hTX : T ≤ X := le_sup_right
  have hKcX : Kc ≤ X := le_sup_left
  have hQT : Q ≤ T := pCoreOf_le_of_isSylowTwoOf (hsyl Mc hTMc)
  have hVO2H : V ≤ pCoreOf 2 H := (h15111 G T Mc M hs.qtfe hs.mf hs.ce H hH).1
  have hVT : V ≤ T := hVO2H.trans (pCoreOf_le_of_isSylowTwoOf (hsyl H hH.1.1))
  have hVn : M ≤ Subgroup.normalizer (V : Set G) := le_normalizer_V154 T Mc M
  have hV2 : IsPGroup 2 V := hT2.to_le hVT
  have hVMc : V ≤ Mc := hVT.trans hTMc
  have hVTn : ∀ t ∈ T, ∀ v ∈ V, t * v * t⁻¹ ∈ V := fun t ht v hv =>
    (Subgroup.mem_normalizer_iff.mp (hVn (hTM ht)) v).mp hv

  have hZT : Z ≤ T ⊓ Subgroup.centralizer (T : Set G) := quasithinOmegaOneCenter_le_center T
  have hZ2 : IsPGroup 2 Z := hT2.to_le (hZT.trans inf_le_left)
  have hZc : ∀ g ∈ Mc, ∀ z ∈ Z, g * z * g⁻¹ = z := by
    intro g hg z hz
    have hg' : g ∈ Subgroup.centralizer (Z : Set G) := h14.mc_eq ▸ hg
    have := Subgroup.mem_centralizer_iff.mp hg' z hz
    rw [← this]; group

  have hZSeq : ⁅V, B⁆ = ZS := (hB₀prop B hB).2.2.1
  have hZS4 : Nat.card ZS = 4 := hZSeq ▸ h11.card
  have hZSab : IsElemAbelian 2 ZS := hZSeq ▸ h11.elemAbelian
  have hTZS : T ≤ Subgroup.normalizer (ZS : Set G) := hZSeq ▸ h11.normal
  have hZZS : Z ≤ ZS := h14.le_zS
  have hZSV : ZS ≤ V := zSOf_le_V154 T Mc M B₀
  have hcase : Z = ZS ∨ (Nat.card Z = 2 ∧ Nat.card ZS = 4) := by
    rcases h14.cases with ⟨-, hZeq, -, -⟩ | ⟨-, hZ2', -⟩
    · exact Or.inl hZeq
    · exact Or.inr ⟨hZ2', hZS4⟩
  have hTC : T ≤ zsMod152 ZS Z hZZS := by
    intro t ht
    refine ⟨hTZS ht, ?_⟩
    exact commutator_mem_of_card_four152 hZZS
      (fun t ht s hs' => (Subgroup.mem_normalizer_iff.mp (hTZS ht) s).mp hs')
      (fun t ht z hz => by
        have := Subgroup.mem_centralizer_iff.mp (hZT hz).2 t ht
        rw [this]; group)
      (fun a ha b hb => F7.isElemAbelian_comm hZSab ha hb) hcase t ht

  have hO3 : ∀ W : Subgroup G, W ≤ Mc → Mc ≤ Subgroup.normalizer (W : Set G) → ¬ 3 ∣ Nat.card W →
      W ≤ M ⊓ Mc := fun W hWMc hWn hW3 =>
    le_inf (normal_threePrime_le_M152_F4 hs h15208 hWMc hWn hW3) hWMc
  have hKne : Kc ≠ K := by
    intro hKK

    have hKn : Mc ≤ Subgroup.normalizer (K : Set G) := by
      rw [← hKK]
      exact hMcn
    have hcommK : ∀ k ∈ Kc, ∀ v ∈ V, k * v * k⁻¹ * v⁻¹ ∈ Q :=
      comm_mem_pCoreOf152 (Y := H) (R := pCoreOf 2 H) hKcMc hMcn
        (by rw [hKK]; exact oTwoUpper_le H) (by rw [hKK]; exact le_normalizer_oTwoUpper H)
        (CFSG.LieType.BorelTits.pCoreOf_le 2 H) (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 H)
        (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 H) hVO2H
    exact hV (He12.le_pCoreOf_of_commutes_caseI hKMc hKn
      (fun x hx hx3 => He12.mem_of_orderOf_three_F4 h15208 h15209 hs hH hKK hx hx3)
      hO3 hVMc hV2 (fun n hn v hv => (Subgroup.mem_normalizer_iff.mp (hVn hn.1) v).mp hv)
      (fun k hk v hv => hcommK k (by rw [hKK]; exact hk) v hv))
  have h3 : ∀ x ∈ Mc, (∃ k : ℕ, orderOf x = 3 ^ k) → x ∈ Kc := by
    intro x hx hk
    have : x ∈ oPrimeResidualOf 3 Mc := Subgroup.subset_closure ⟨hx, hk⟩
    rw [← h12.eq_oThreePrime_of_ne hKne] at this
    exact this
  have hVO2 : ¬ ∀ k ∈ Kc, ∀ v ∈ V, k * v * k⁻¹ * v⁻¹ ∈ Q := fun hall =>
    hV (le_pCoreOf_of_commutes152 hKcMc hMcn h3 hO3 hVMc hV2
      (fun n hn v hv => (Subgroup.mem_normalizer_iff.mp (hVn hn.1) v).mp hv) hall)
  have hVOX : ¬ V ≤ pCoreOf 2 X := fun hVX =>
    hVO2 (comm_mem_pCoreOf152 (Y := X) (R := pCoreOf 2 X) hKcMc hMcn hKcX (hXMc.trans hMcn)
      (CFSG.LieType.BorelTits.pCoreOf_le 2 X) (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 X)
      (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 X) hVX)
  have hZQ : Z ≤ Q := fun z hz => hchar ⟨hTMc (hZT hz).1,
    Subgroup.mem_centralizer_iff.mpr fun q hq =>
      Subgroup.mem_centralizer_iff.mp (hZT hz).2 q (hQT hq)⟩
  have hZcard : 2 ≤ Nat.card Z := by
    rcases hcase with hZe | ⟨hZ2', -⟩
    · rw [hZe, hZS4]; norm_num
    · rw [hZ2']
  have hVc_lt : V ⊓ Q < V := lt_of_le_of_ne inf_le_left fun h => hV (h ▸ inf_le_right)
  have hcardVc : Nat.card (V ⊓ Q : Subgroup G) ≤ 8 := by
    have hlt := Subgroup.card_lt_of_lt hVc_lt
    obtain ⟨c, hc⟩ := Subgroup.card_dvd_of_le (inf_le_left : V ⊓ Q ≤ V)
    rw [hV16] at hc hlt
    rcases c with _ | _ | c
    · omega
    · omega
    · have e : Nat.card (V ⊓ Q : Subgroup G) * (c + 1 + 1) =
          Nat.card (V ⊓ Q : Subgroup G) * c + Nat.card (V ⊓ Q : Subgroup G) * 2 := by ring
      omega
  have hcase23 : Case15212ii T Mc Kc ∨ Case15212iii T Mc Kc := by
    rcases h12.cases with h | h | h | h
    · exact absurd h hKne
    · exact Or.inl h
    · exact Or.inr h
    ·
      exact (false_of_he_small_commutator hTrans.2 h.2.2 hXdef
        (fun g hg k hk => (Subgroup.mem_normalizer_iff.mp (hMcn (hXMc hg)) k).mp hk)
        (hsyl X hTX) (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 Mc) hQT
        (fun g hg q hq => (Subgroup.mem_normalizer_iff.mp
          (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 Mc (hXMc hg)) q).mp hq)
        (fun x hx hcomm => hchar ⟨hXMc hx, Subgroup.mem_centralizer_iff.mpr hcomm⟩)
        hVT hVTn hV16 hV hVOX hZ2 (hZZS.trans hZSV) hZQ hZcard
        (fun g hg z hz => hZc g (hXMc hg) z hz)).elim

  have hgood : GoodShape152 X := by
    obtain ⟨L₀, N₀, hLN₀, hZL₀, hNVL₀⟩ := exists_chiefStep_of_not_le_pCoreOf (X := X) (Q := Q)
      (ZS := Z) (Z := ⊥) (V := V) (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 Mc)
      IsPGroup.of_bot hZQ
      (fun g hg s hs' => by rw [hZc g (hXMc hg) s hs']; exact hs')
      (fun g hg s hs' => by rw [hZc g (hXMc hg) s hs']; simp)
      (fun g hg z hz => by rw [Subgroup.mem_bot.mp hz]; simp)
      (fun g hg q hq => (Subgroup.mem_normalizer_iff.mp
        (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 Mc (hXMc hg)) q).mp hq)
      (fun x hx hcomm => hchar ⟨hXMc hx, Subgroup.mem_centralizer_iff.mpr hcomm⟩)
      (hVT.trans hTX) hVOX
    have hNQ₀ : N₀ ≤ Q := hLN₀.1.1
    have hcommVc₀ : ⁅N₀, V⁆ ≤ V ⊓ Q := by
      refine Subgroup.commutator_le.mpr fun n hn v hv => ?_
      rw [commutatorElement_def]
      refine ⟨?_, ?_⟩
      · exact V.mul_mem (hVTn n (hQT (hNQ₀ hn)) v hv) (V.inv_mem hv)
      · have h1 : v * n⁻¹ * v⁻¹ ∈ Q :=
          (Subgroup.mem_normalizer_iff.mp (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 Mc
            (hVMc hv)) n⁻¹).mp (Q.inv_mem (hNQ₀ hn))
        have := Q.mul_mem (hNQ₀ hn) h1
        simpa [mul_assoc] using this
    have hVcn₀ : V ⊓ Q ≤ Subgroup.normalizer (L₀ : Set G) := by
      intro g hg
      have hgX : g ∈ X := hTX (hQT hg.2)
      rw [Subgroup.mem_normalizer_iff]
      intro x
      refine ⟨fun hx => hLN₀.2.1.2 g hgX x hx, fun hx => ?_⟩
      have := hLN₀.2.1.2 g⁻¹ (X.inv_mem hgX) _ hx
      simpa [mul_assoc] using this
    have hsup₀ := card_sup_le_mul152 4 (le_inf (hZZS.trans hZSV) hZQ) hZL₀ hVcn₀
      (by omega)
    have hcard4 : Nat.card ↥(⁅N₀, V⁆ ⊔ L₀) ≤ 4 * Nat.card L₀ :=
      (Subgroup.card_le_of_le (sup_le_sup_right hcommVc₀ L₀)).trans hsup₀
    exact hShape G T Mc M H hs hH hV hcase23 L₀ N₀ hLN₀ hZL₀ hNVL₀ hcard4

  have hX : X ≤ zsMod152 ZS Z hZZS :=
    le_zsMod152 hZZS hZSV hsyl hTM hVn hTX hXMc h1519c.seven_normalizer
      (h14.inf_eq.1.trans h14.inf_eq.2).le hTC
      (fun P hP => oTwoUpper_le_centralizer_zS152_F4 hs h15209 h15211 h15213 hB₀ hP)
      (hParGood G T Mc M H hs hH hV hcase23 hgood)
  have hZSQ : ZS ≤ Q := by
    intro s hs'
    refine mem_pCoreOf_of_comm_mod_central hZ2 hZc hchar (hVMc (hZSV hs')) ?_
    intro q hq
    have hqX := hX (hTX (hQT hq))
    have h1 := hqX.2 s hs'
    have e : s * q * s⁻¹ * q⁻¹ = (q * s * q⁻¹ * s⁻¹)⁻¹ := by group
    rw [e]; exact Z.inv_mem h1

  obtain ⟨L, N, hLN, hZSL, hNVL⟩ := exists_chiefStep_of_not_le_pCoreOf (X := X) (Q := Q)
    (ZS := ZS) (Z := Z) (V := V) (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 Mc) hZ2 hZSQ
    (fun g hg s hs' => (Subgroup.mem_normalizer_iff.mp (hX hg).1 s).mp hs')
    (fun g hg s hs' => (hX hg).2 s hs')
    (fun g hg z hz => hZc g (hXMc hg) z hz)
    (fun g hg q hq => (Subgroup.mem_normalizer_iff.mp
      (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 Mc (hXMc hg)) q).mp hq)
    (fun x hx hcomm => hchar ⟨hXMc hx, Subgroup.mem_centralizer_iff.mpr hcomm⟩)
    (hVT.trans hTX) hVOX

  have hNQ : N ≤ Q := hLN.1.1
  have hcommVc : ⁅N, V⁆ ≤ V ⊓ Q := by
    refine Subgroup.commutator_le.mpr fun n hn v hv => ?_
    rw [commutatorElement_def]
    refine ⟨?_, ?_⟩
    · exact V.mul_mem (hVTn n (hQT (hNQ hn)) v hv) (V.inv_mem hv)
    · have h1 : v * n⁻¹ * v⁻¹ ∈ Q :=
        (Subgroup.mem_normalizer_iff.mp (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 Mc
          (hVMc hv)) n⁻¹).mp (Q.inv_mem (hNQ hn))
      have := Q.mul_mem (hNQ hn) h1
      simpa [mul_assoc] using this
  have hVcn : V ⊓ Q ≤ Subgroup.normalizer (L : Set G) := by
    intro g hg
    have hgX : g ∈ X := hTX (hQT hg.2)
    rw [Subgroup.mem_normalizer_iff]
    intro x
    refine ⟨fun hx => hLN.2.1.2 g hgX x hx, fun hx => ?_⟩
    have := hLN.2.1.2 g⁻¹ (X.inv_mem hgX) _ hx
    simpa [mul_assoc] using this
  have hsup := card_sup_le_two_mul152 (le_inf hZSV hZSQ) hZSL hVcn (by rw [hZS4]; omega)
  have hcard1 : Nat.card ↥(⁅N, V⁆ ⊔ L) ≤ 2 * Nat.card L :=
    (Subgroup.card_le_of_le (sup_le_sup_right hcommVc L)).trans hsup
  have hLlt : L < ⁅N, V⁆ ⊔ L := lt_of_le_of_ne le_sup_right fun h => hNVL (h ▸ le_sup_left)
  have hlt' := Subgroup.card_lt_of_lt hLlt
  obtain ⟨m, hm⟩ := Subgroup.card_dvd_of_le (le_sup_right : L ≤ ⁅N, V⁆ ⊔ L)
  have hLpos : 0 < Nat.card L := Nat.card_pos
  have heq : Nat.card ↥(⁅N, V⁆ ⊔ L) = 2 * Nat.card L := by
    rcases m with _ | _ | _ | m
    · omega
    · omega
    · omega
    · have e : Nat.card L * (m + 1 + 1 + 1) = Nat.card L * m + Nat.card L * 3 := by ring
      omega
  exact hTrans.1 G T Mc M H hs hH hV hcase23 L N hLN heq

end He12

end CFSG.Quasithin
