module

public import CFSG.CGT.PushingUpLit.C2L.BlockTwoQuot
public import CFSG.CGT.PushingUpLit.C2L.BlockTwoNat
import CFSG.CGT.PushingUpLit.A78One.DictStar
public import CFSG.CGT.PushingUpLit.A78One.NatExtend

public section

namespace CFSG.CGT.PushingUpLit.C2L

open CFSG CFSG.ABGLocalTools CFSG.CGT.PushingUpLit CFSG.CGT.PushingUpLit.T2K
  CFSG.CGT.PushingUpLit.T2KSW CFSG.CGT.PushingUpLit.A78One CFSG.CGT.PushingUpLit.A78

variable {G : Type} [Group G] [Finite G] {L M T D D₂ : Subgroup G} {n : ℕ} {a : G}

section First

theorem oTwoIn_le_D (hs : Sec4Core G L M T n) (hN : Subgroup.normalizer (L : Set G) = M)
    (hin : SecondBlockInput G L M T n D D₂ a) : oTwoIn L ≤ D := by
  rw [← hin.D_eq]
  refine le_oTwoIn_of_normal ((oTwoIn_le L).trans le_sup_left) ?_ (isPGroup_oTwoIn L)
  refine sup_le (le_normalizer_oTwoIn L) ?_
  refine le_trans ?_ (normalizer_le_normalizer_oTwoIn L)
  rw [hN]
  exact hs.sylow.le

theorem natExt_D (hs : Sec4Core G L M T n) (hN : Subgroup.normalizer (L : Set G) = M)
    (hin : SecondBlockInput G L M T n D D₂ a) : NatExt L D := by
  have hWD := oTwoIn_le_D hs hN hin
  have hUD : blockU L ≤ D := (blockU_le_oTwoIn L).trans hWD
  have hcomm : ∀ x ∈ D, ∀ y ∈ D, x * y = y * x :=
    fun x hx y hy => congrArg Subtype.val (hin.D_elem.1.is_comm.comm (⟨x, hx⟩ : D) ⟨y, hy⟩)
  refine ⟨hUD, hcomm, ?_, ?_⟩
  · intro p hp
    obtain ⟨v, hv, e, he, rfl⟩ := hin.D_dec p hp
    exact ⟨v, hv, e, ⟨hin.E_le he, he.2⟩, rfl⟩
  · apply le_antisymm
    · calc L ⊓ Subgroup.centralizer (D : Set G)
          ≤ L ⊓ Subgroup.centralizer (blockU L : Set G) :=
            inf_le_inf_left L (Subgroup.centralizer_le (fun u hu => hUD hu))
        _ = oTwoIn L := hs.hyp.natBlock.inf_centralizer_blockU
    · intro o ho
      exact ⟨oTwoIn_le L ho, Subgroup.mem_centralizer_iff.2 fun p hp => hcomm p hp o (hWD ho)⟩

theorem a78Side_first (hE1 : FooteNonsolvableSimple) (hs : Sec4Core G L M T n)
    (hin : SecondBlockInput G L M T n D D₂ a) : A78Side G L T T n := by
  have hN : Subgroup.normalizer (L : Set G) = M := hs.hyp.normalizer_eq hE1
  have hnM : M ≤ Subgroup.normalizer (L : Set G) := hN.ge
  have hO : oTwoIn (L ⊔ T) = cexP L T := hin.D_eq.trans hin.D_def
  have hTLD : T ≤ L ⊔ D := hin.T_le.trans (sup_le_sup_right inf_le_right D)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hN]
    exact hs.sylow
  · rw [hin.D_eq]
    exact hin.D_elem
  · rw [hO]
    exact exists_phi_of hs.hyp hnM hs.sylow
  · rw [hin.D_eq]
    exact NatExt.isNatSL_of_natExt hs.hyp.natBlock.natData (natExt_D hs hN hin)
  · rw [hin.D_eq]
    exact hs.sylowG.of_le hTLD le_top
  · rw [hN]
    have hu := hs.hyp.unique
    ext K
    rw [Set.mem_singleton_iff]
    constructor
    · rintro ⟨hK, hKle⟩
      have h1 : K ∈ maximalTwoLocalsContaining (L : Set G) :=
        ⟨hK, fun l hl => hKle (Subgroup.mem_sup_left hl)⟩
      rw [hu] at h1
      exact h1
    · rintro rfl
      exact ⟨hs.hyp.maxLocal, fun y hy => (sup_le hs.hyp.le hs.sylow.le) hy⟩

end First

section Second

variable {L₂ : Subgroup G}

omit [Finite G] in
theorem conj_mem_zc {g x : G} (hg : g ∈ Subgroup.normalizer (T : Set G)) (hx : x ∈ zc T) :
    g * x * g⁻¹ ∈ zc T := by
  refine ⟨(Subgroup.mem_normalizer_iff.1 hg x).1 hx.1, Subgroup.mem_centralizer_iff.2 ?_⟩
  intro t ht
  have hg' : g⁻¹ ∈ Subgroup.normalizer (T : Set G) := (Subgroup.normalizer _).inv_mem hg
  have ht' : g⁻¹ * t * g⁻¹⁻¹ ∈ T := (Subgroup.mem_normalizer_iff.1 hg' t).1 ht
  have hc := Subgroup.mem_centralizer_iff.1 hx.2 _ ht'
  rw [inv_inv] at hc
  calc t * (g * x * g⁻¹) = g * ((g⁻¹ * t * g) * x) * g⁻¹ := by group
    _ = g * (x * (g⁻¹ * t * g)) * g⁻¹ := by rw [hc]
    _ = (g * x * g⁻¹) * t := by group

theorem le_of_normal_of_isSylowOf {K T' H : Subgroup G} (hT : IsSylowOf 2 T' K) (hHK : H ≤ K)
    (hn : K ≤ Subgroup.normalizer (H : Set G)) (hH : IsPGroup 2 H) : H ≤ T' := by
  have hsup : IsPGroup 2 (T' ⊔ H : Subgroup G) :=
    IsPGroup.to_sup_of_normal_right' hT.isPGroup hH (hT.le.trans hn)
  have h := hT.eq_of_le le_sup_left (sup_le hT.le hHK) hsup
  exact le_sup_right.trans h.le

theorem BlockTwoFacts.le_normalizer
    (hf : BlockTwoFacts G (Subgroup.normalizer (D₂ : Set G)) D₂ T L₂ n) :
    Subgroup.normalizer (D₂ : Set G) ≤ Subgroup.normalizer (L₂ : Set G) :=
  fun g hg => Subgroup.mem_normalizer_fintype (hf.normal g hg)

theorem oTwoIn_L₂ (hin : SecondBlockInput G L M T n D D₂ a)
    (hf : BlockTwoFacts G (Subgroup.normalizer (D₂ : Set G)) D₂ T L₂ n) : oTwoIn L₂ = D₂ := by
  apply le_antisymm
  · have h1 : oTwoIn L₂ ≤ oTwoIn (Subgroup.normalizer (D₂ : Set G)) :=
      le_oTwoIn_of_normal ((oTwoIn_le L₂).trans hf.le_N)
        (hf.le_normalizer.trans (normalizer_le_normalizer_oTwoIn L₂)) (isPGroup_oTwoIn L₂)
    rwa [hin.gomiH.oTwoIn_eq] at h1
  · exact le_oTwoIn_of_normal hf.D_le hf.le_N hin.gomiH.isPGroup

theorem normalizer_L₂ (hin : SecondBlockInput G L M T n D D₂ a)
    (hf : BlockTwoFacts G (Subgroup.normalizer (D₂ : Set G)) D₂ T L₂ n) :
    Subgroup.normalizer (L₂ : Set G) = Subgroup.normalizer (D₂ : Set G) := by
  apply le_antisymm
  · intro g hg
    have : g ∈ Subgroup.normalizer (oTwoIn L₂ : Set G) := normalizer_le_normalizer_oTwoIn L₂ hg
    rwa [oTwoIn_L₂ hin hf] at this
  · exact hf.le_normalizer

theorem maximalTwoLocalsContaining_L₂ (hs : Sec4Core G L M T n)
    (hin : SecondBlockInput G L M T n D D₂ a)
    (hf : BlockTwoFacts G (Subgroup.normalizer (D₂ : Set G)) D₂ T L₂ n) :
    maximalTwoLocalsContaining ((L₂ ⊔ T : Subgroup G) : Set G) =
      {Subgroup.normalizer (L₂ : Set G)} := by
  have hLT : L₂ ⊔ T = L₂ := sup_eq_left.2 hf.T_le
  have hN₂ := normalizer_L₂ hin hf
  have hTL : IsSylowOf 2 T L₂ := hs.sylowG.of_le hf.T_le le_top
  have claimA : ∀ K : Subgroup G, IsMaximalTwoLocal K → L₂ ≤ K →
      K = Subgroup.normalizer (D₂ : Set G) := by
    intro K hK hLK
    obtain ⟨P₀, hP₀ne, hP₀2, hKP₀⟩ := hK.1
    have hH2 : IsPGroup 2 (oTwoIn K) := isPGroup_oTwoIn K
    have hP₀H : P₀ ≤ oTwoIn K :=
      le_oTwoIn_of_normal (hKP₀ ▸ Subgroup.le_normalizer) hKP₀.le hP₀2
    have hHne : oTwoIn K ≠ ⊥ := fun h => hP₀ne (le_bot_iff.1 (h ▸ hP₀H))
    have hKH : K = Subgroup.normalizer (oTwoIn K : Set G) := by
      by_contra hne
      exact hK.2 _ (lt_of_le_of_ne (le_normalizer_oTwoIn K) hne)
        (CFSG.CGT.PushingUp.isPLocal_normalizer_of_isPGroup hH2 hHne)
    have hcent : Subgroup.centralizer (oTwoIn K : Set G) ≤ oTwoIn K := by
      intro x hx
      have h1 := hs.hyp.charTwo K hK.1
      rw [assembly_pCoreOf_two_eq_oTwoIn] at h1
      have hxK : x ∈ K := by
        rw [hKH]
        exact Subgroup.centralizer_le_normalizer _ hx
      exact h1 (Subgroup.mem_inf.2 ⟨hxK, hx⟩)
    have hTK : IsSylowOf 2 T K := hs.sylowG.of_le (hf.T_le.trans hLK) le_top
    have hHT : oTwoIn K ≤ T :=
      le_of_normal_of_isSylowOf hTK (oTwoIn_le K) (le_normalizer_oTwoIn K) hH2
    have hXH : zc T ≤ oTwoIn K := fun x hx =>
      hcent (Subgroup.mem_centralizer_iff.2 fun h' hh' =>
        (Subgroup.mem_centralizer_iff.1 hx.2) h' (hHT hh'))
    have hnormH : ∀ l ∈ L₂, ∀ h' ∈ oTwoIn K, l * h' * l⁻¹ ∈ oTwoIn K := by
      intro l hl h' hh'
      have : l ∈ Subgroup.normalizer (oTwoIn K : Set G) := by
        rw [← hKH]
        exact hLK hl
      exact (Subgroup.mem_normalizer_iff.1 this h').1 hh'
    have hTaL : T.map (MulAut.conj a).toMonoidHom ≤ L₂ := by
      rintro _ ⟨t, ht, rfl⟩
      exact hf.normal a hin.a_mem t (hf.T_le ht)
    obtain ⟨h₀, hh₀, hh₀T⟩ := CFSG.CGT.PushingUpLit.T2KSW.exists_mem_conj_mem_of_isSylowOf hTL
      hTaL (hs.sylowG.isPGroup.map _)
    have hg₀ : h₀⁻¹ * a ∈ Subgroup.normalizer (T : Set G) := by
      refine Subgroup.mem_normalizer_fintype fun t ht => ?_
      have h1 := hh₀T (a * t * a⁻¹) ⟨t, ht, by simp [MulAut.conj_apply]⟩
      have e : (h₀⁻¹ * a) * t * (h₀⁻¹ * a)⁻¹ = h₀⁻¹ * (a * t * a⁻¹) * h₀ := by group
      rw [e]
      exact h1
    have hX₂H : (zc T).map (MulAut.conj a).toMonoidHom ≤ oTwoIn K := by
      rintro _ ⟨x, hx, rfl⟩
      have hx' := conj_mem_zc hg₀ hx
      have e : (MulAut.conj a).toMonoidHom x = h₀ * ((h₀⁻¹ * a) * x * (h₀⁻¹ * a)⁻¹) * h₀⁻¹ := by
        simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
        group
      rw [e]
      exact hnormH h₀ hh₀ _ (hXH hx')
    have hD₂H : D₂ ≤ oTwoIn K := by
      rw [hin.D₂_eq]
      exact sup_le hX₂H hXH
    have hHD₂ : oTwoIn K ≤ D₂ := by
      have h1 := le_oTwoIn_of_normal (hHT.trans hf.T_le : oTwoIn K ≤ L₂)
        (fun l hl => by
          have : l ∈ Subgroup.normalizer (oTwoIn K : Set G) := by
            rw [← hKH]
            exact hLK hl
          exact this) hH2
      rwa [oTwoIn_L₂ hin hf] at h1
    rw [hKH, le_antisymm hHD₂ hD₂H]
  have claimB : IsMaximalTwoLocal (Subgroup.normalizer (D₂ : Set G)) := by
    have hloc := CFSG.CGT.PushingUp.isPLocal_normalizer_of_isPGroup hin.gomiH.isPGroup
      hin.gomiH.ne_bot
    obtain ⟨K', hNK', hK'⟩ := CFSG.CGT.PushingUp.exists_isMaximalTwoLocal_ge hloc
    have : K' = Subgroup.normalizer (D₂ : Set G) := claimA K' hK' (hf.le_N.trans hNK')
    rwa [this] at hK'
  rw [hLT, hN₂]
  ext K
  rw [Set.mem_singleton_iff]
  constructor
  · rintro ⟨hK, hKle⟩
    exact claimA K hK (fun x hx => hKle hx)
  · rintro rfl
    exact ⟨claimB, fun x hx => hf.le_N hx⟩

theorem a78Side_second (hs : Sec4Core G L M T n) (hin : SecondBlockInput G L M T n D D₂ a)
    (hf : BlockTwoFacts G (Subgroup.normalizer (D₂ : Set G)) D₂ T L₂ n)
    (hnat : BHS.IsNatSL L₂ D₂ n) : A78Side G L₂ T T n := by
  have hLT : L₂ ⊔ T = L₂ := sup_eq_left.2 hf.T_le
  have hO := oTwoIn_L₂ hin hf
  have hLD : L₂ ⊔ D₂ = L₂ := sup_eq_left.2 hf.D_le
  obtain ⟨φ, hφs, hφk, -⟩ := hf.quot
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [normalizer_L₂ hin hf]
    exact hs.sylowG.of_le hin.T_le_N le_top
  · rw [hLT, hO]
    exact hin.D₂_elem
  · rw [hLT, hO, hLD]
    exact ⟨φ, hφs, hφk⟩
  · rw [hLT, hO]
    exact hnat
  · rw [hLT, hO, hLD]
    exact hs.sylowG.of_le hf.T_le le_top
  · exact maximalTwoLocalsContaining_L₂ hs hin hf

theorem a78Cfg_of_blockTwo (hE1 : FooteNonsolvableSimple) (hs : Sec4Core G L M T n)
    (hE : Ec L T ≠ ⊥) (hin : SecondBlockInput G L M T n D D₂ a)
    (hf : BlockTwoFacts G (Subgroup.normalizer (D₂ : Set G)) D₂ T L₂ n)
    (hnat : BHS.IsNatSL L₂ D₂ n) :
    A78Cfg G L L₂ T n ∧ oTwoIn (L ⊔ T) ⊓ Subgroup.centralizer (L : Set G) ≠ ⊥ ∧
      oTwoIn (L ⊔ T) ⊔ oTwoIn (L₂ ⊔ T) = T := by
  have hLT : L₂ ⊔ T = L₂ := sup_eq_left.2 hf.T_le
  have hJ : oTwoIn (L ⊔ T) ⊔ oTwoIn (L₂ ⊔ T) = T := by
    rw [hin.D_eq, hLT, oTwoIn_L₂ hin hf]
    exact hin.sup_eq
  have hN : Subgroup.normalizer (L : Set G) = M := hs.hyp.normalizer_eq hE1
  refine ⟨⟨hs.hyp.kproper, hs.hyp.simple, hs.hyp.charTwo, hs.hyp.two_le, ?_, ?_, ?_⟩, ?_, hJ⟩
  · rw [hN, normalizer_L₂ hin hf]
    exact fun h => hin.ne_M h.ge
  · rw [hJ]
    exact a78Side_first hE1 hs hin
  · rw [hJ]
    exact a78Side_second hs hin hf hnat
  · intro hbot
    apply hE
    rw [Subgroup.eq_bot_iff_forall] at hbot ⊢
    intro e he
    exact hbot e ⟨by rw [hin.D_eq]; exact hin.E_le he, he.2⟩

end Second

theorem secondBlock_cfg (hE1 : FooteNonsolvableSimple)
    (hs : Sec4Core G L M T n) (hE : Ec L T ≠ ⊥) (hc : ClassLETwo T)
    (hin : SecondBlockInput G L M T n D D₂ a) :
    ∃ L₂ : Subgroup G, A78Cfg G L L₂ T n ∧
      oTwoIn (L ⊔ T) ⊓ Subgroup.centralizer (L : Set G) ≠ ⊥ ∧
      oTwoIn (L ⊔ T) ⊔ oTwoIn (L₂ ⊔ T) = T := by
  have hTN := hin.T_le_N
  obtain ⟨L₂, hDL, hTL, hLN, hnorm, hquot, hgen⟩ := exists_block_of_isTI_quotient
    hs.hyp.two_le hin.D₂_le hTN le_rfl (hs.sylowG.of_le hTN le_top) hin.quot_elem
    hin.card_T_D₂ hin.ti (fun h => hin.a_not (h hin.a_mem))
  have hf : BlockTwoFacts G (Subgroup.normalizer (D₂ : Set G)) D₂ T L₂ n :=
    ⟨hDL, hTL, hLN, hnorm, hquot, hgen⟩
  exact ⟨L₂, a78Cfg_of_blockTwo hE1 hs hE hin hf (isNatSL_second hs hc hin hf)⟩

theorem phaseL_of_secondBlockInput (hE1 : FooteNonsolvableSimple)
    (h : ∀ (G : Type) [Group G] [Finite G] (L M T : Subgroup G) (n : ℕ), Sec4 G L M T n →
      Ec L T ≠ ⊥ → ClassLETwo T → ¬ EWeaklyClosed L T →
        ∃ (D D₂ : Subgroup G) (a : G), SecondBlockInput G L M T n D D₂ a) :
    PhaseL := by
  intro G _ _ L M T n hs hE hc hw
  obtain ⟨D, D₂, a, hin⟩ := h G L M T n hs hE hc hw
  exact secondBlock_cfg hE1 (sec4Core_of_sec4 hs) hE hc hin

end CFSG.CGT.PushingUpLit.C2L
