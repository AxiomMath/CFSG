module

public import CFSG.CGT.PushingUpLit.CGT6.EmbAltEnd
public import CFSG.CGT.PushingUpLit.CGT6.EmbEndPass
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoStandardDefs
public import CFSG.RankThree.PartOne.S8.Statements
import CFSG.CGT.PushingUpLit.CGT6.EmbAltPos
import CFSG.LocalAnalysis.ComponentInitial.AlternatingFourGroup

public section

namespace CFSG.CGT.PushingUpLit.CGT6

open CFSG CFSG.RankThree.PartOne CFSG.Quasithin CFSG.CGT.PushingUp CFSG.Open Equiv
open CFSG.ComponentClassification
open scoped commutatorElement

section Module

variable {V : Type} [CommGroup V] {k : ℕ}

private theorem commV_invariant_norm {K : Subgroup (MulAut V)} {c : MulAut V}
    (hnorm : ∀ y ∈ K, c * y * c⁻¹ ∈ K) {w : V} (hw : w ∈ commV K) : c w ∈ commV K := by
  induction hw using Subgroup.closure_induction with
  | mem w hw =>
    obtain ⟨y, hy, v, rfl⟩ := hw
    have h1 : c (y v * v⁻¹) = (c * y * c⁻¹) (c v) * (c v)⁻¹ := by
      simp [MulAut.mul_apply]
    rw [h1]
    exact Subgroup.subset_closure ⟨c * y * c⁻¹, hnorm y hy, c v, rfl⟩
  | one => simp
  | mul a b _ _ ha hb => rw [map_mul]; exact mul_mem ha hb
  | inv a _ ha => rw [map_inv]; exact inv_mem ha

theorem fix_commV_of_commute_any (hk : Odd k) (hk5 : 5 ≤ k) {K : Subgroup (MulAut V)}
    (θ : K ≃* alternatingGroup (Fin k)) (h : IsNatSectionWith (altAct k) θ (commV K) ⊥)
    {z : MulAut V} (hc : ∀ y ∈ K, z * y = y * z) : ∀ e ∈ commV K, z e = e := by
  classical
  have hk0 : 0 < k := by omega
  let p : Fin k := ⟨0, hk0⟩
  let N : Subgroup (MulAut V) := ((altStabilizer k {p}).comap θ.toMonoidHom).map K.subtype
  have hNK : N ≤ K := by
    rintro _ ⟨x, -, rfl⟩
    exact x.2
  have hN : (N.subgroupOf K).map θ.toMonoidHom = altStabilizer k {p} := by
    have h1 : N.subgroupOf K = (altStabilizer k {p}).comap θ.toMonoidHom :=
      Subgroup.comap_map_eq_self_of_injective K.subtype_injective _
    rw [h1, Subgroup.map_comap_eq_self_of_surjective θ.surjective]
  obtain ⟨w, hw1, hwN, hwfix, hw⟩ := exists_fixed_pair_of_natural hk hk5 θ h hNK p hN
  have hwE : w ∈ commV K := commV_mono hNK hwN
  have hznorm : ∀ y ∈ K, z * y * z⁻¹ ∈ K := fun y hy => by
    have : z * y * z⁻¹ = y := by rw [hc y hy]; group
    rw [this]
    exact hy
  have hzw : z w = w := by
    have h1 : z w ∈ commV K := commV_invariant_norm hznorm hwE
    have h2 : z w ∈ fixV N := by
      intro n hn
      have := congrArg (fun g : MulAut V => g w) (hc n (hNK hn))
      simp only [MulAut.mul_apply] at this
      rw [← this, mem_fixV.mp hwfix n hn]
    rcases hw (z w) h1 h2 with h3 | h3
    · exact absurd ((map_eq_one_iff z z.injective).mp h3) hw1
    · exact h3
  let W : Subgroup V := Subgroup.closure {u | ∃ y ∈ K, u = y w}
  have hWK : ∀ x ∈ K, ∀ a ∈ W, x a ∈ W := by
    intro x hx a ha
    induction ha using Subgroup.closure_induction with
    | mem a ha =>
      obtain ⟨y, hy, rfl⟩ := ha
      exact Subgroup.subset_closure ⟨x * y, K.mul_mem hx hy, by simp [MulAut.mul_apply]⟩
    | one => simp
    | mul a b _ _ ha hb => rw [map_mul]; exact mul_mem ha hb
    | inv a _ ha => rw [map_inv]; exact inv_mem ha
  have hWle : W ≤ commV K := by
    refine (Subgroup.closure_le _).mpr ?_
    rintro _ ⟨y, hy, rfl⟩
    exact commV_invariant hy hwE
  have hwW : w ∈ W := Subgroup.subset_closure ⟨1, K.one_mem, by simp⟩
  have hWtop : W = commV K := by
    rcases commV_subgroup_eq_bot_or_top_of_natural hk hk5 θ h hWK hWle with h0 | h1
    · exact absurd (h0 ▸ hwW) (by simpa using hw1)
    · exact h1
  have hzW : ∀ a ∈ W, z a = a := by
    intro a ha
    induction ha using Subgroup.closure_induction with
    | mem a ha =>
      obtain ⟨y, hy, rfl⟩ := ha
      have := congrArg (fun g : MulAut V => g w) (hc y hy)
      simp only [MulAut.mul_apply] at this
      rw [this, hzw]
    | one => simp
    | mul a b _ _ ha hb => rw [map_mul, ha, hb]
    | inv a _ ha => rw [map_inv, ha]
  intro e he
  rw [← hWtop] at he
  exact hzW e he

end Module

private theorem commV_closure_le {V : Type} [CommGroup V] {S : Set (MulAut V)} {W : Subgroup V}
    (hS : ∀ s ∈ S, ∀ v : V, s v * v⁻¹ ∈ W) : commV (Subgroup.closure S) ≤ W := by
  have key : ∀ l ∈ Subgroup.closure S, ∀ v : V, l v * v⁻¹ ∈ W := by
    intro l hl
    induction hl using Subgroup.closure_induction with
    | mem s hs => exact hS s hs
    | one => intro v; simp
    | mul a b _ _ ha hb =>
      intro v
      have : (a * b) v * v⁻¹ = (a (b v) * (b v)⁻¹) * (b v * v⁻¹) := by
        simp [MulAut.mul_apply]
      rw [this]
      exact W.mul_mem (ha (b v)) (hb v)
    | inv a _ ha =>
      intro v
      have : a⁻¹ v * v⁻¹ = (a (a⁻¹ v) * (a⁻¹ v)⁻¹)⁻¹ := by simp
      rw [this]
      exact W.inv_mem (ha (a⁻¹ v))
  refine (Subgroup.closure_le _).mpr ?_
  rintro _ ⟨l, hl, v, rfl⟩
  exact key l hl v

section Center

variable {V : Type} [CommGroup V] [Finite V] {G T Y : Subgroup (MulAut V)}

theorem EndCfg4.eq_one_of_commute (h : EndCfg4 G T Y) (hV : ∀ v : V, v ^ 2 = 1) {m : ℕ}
    (hm : 7 ≤ m) (hodd : Odd m) (hY : YAlt Y m) {z : MulAut V}
    (hz : ∀ l ∈ conjClosure Y G, z * l = l * z) : z = 1 := by
  obtain ⟨θ₀, hnat⟩ := h.exists_natSection hV hm hodd hY
  have hYG : Y ≤ G := fun y hy => (h.adm.hYC hy).1
  have hLG : conjClosure Y G ≤ G := conjClosure_le hYG
  have hLn : ((conjClosure Y G).subgroupOf G).Normal :=
    ⟨fun n hn g => (Subgroup.mem_normalizer_iff.mp (le_normalizer_conjClosure g.2) n).mp hn⟩
  have hYnt : Nontrivial ↥Y := by
    obtain ⟨ε⟩ := hY
    have : Nontrivial (alternatingGroup (Fin m)) :=
      alternatingGroup.nontrivial_of_three_le_card (by simp; omega)
    exact ε.toEquiv.nontrivial
  have hLnt : Nontrivial ↥(conjClosure Y G) := by
    rw [Subgroup.nontrivial_iff_ne_bot] at hYnt ⊢
    exact ne_bot_of_le_ne_bot hYnt le_conjClosure
  obtain ⟨-, hVL⟩ := h.fixV_commV_of_normal hLG hLn hLnt
  have key : ∀ g ∈ G, ∀ e ∈ commV Y, z (g e) = g e := by
    intro g hg e he
    have hz'c : ∀ y ∈ Y, g⁻¹ * z * g * y = y * (g⁻¹ * z * g) := by
      intro y hy
      have h1 := hz _ (mem_conjClosure_of_mem hg hy)
      calc g⁻¹ * z * g * y = g⁻¹ * (z * (g * y * g⁻¹)) * g := by group
        _ = g⁻¹ * ((g * y * g⁻¹) * z) * g := by rw [h1]
        _ = y * (g⁻¹ * z * g) := by group
    have h2 := fix_commV_of_commute_any hodd (by omega) θ₀ hnat hz'c e he
    calc z (g e) = g ((g⁻¹ * z * g) e) := by simp [MulAut.mul_apply]
      _ = g e := by rw [h2]
  let W : Subgroup V :=
    { carrier := {v | z v = v}
      one_mem' := map_one z
      mul_mem' := fun {a b} ha hb => by
        show z (a * b) = a * b
        rw [map_mul, show z a = a from ha, show z b = b from hb]
      inv_mem' := fun {a} ha => by
        show z a⁻¹ = a⁻¹
        rw [map_inv, show z a = a from ha] }
  have hWtop : commV (conjClosure Y G) ≤ W := by
    refine commV_closure_le ?_
    rintro _ ⟨g, hg, y, hy, rfl⟩ v
    have h1 : (g * y * g⁻¹ : MulAut V) v * v⁻¹ = g (y (g⁻¹ v) * (g⁻¹ v)⁻¹) := by
      simp [MulAut.mul_apply]
    show (g * y * g⁻¹ : MulAut V) v * v⁻¹ ∈ W
    rw [h1]
    exact key g hg _ (Subgroup.subset_closure ⟨y, hy, g⁻¹ v, rfl⟩)
  rw [hVL] at hWtop
  ext v
  exact hWtop (Subgroup.mem_top v)

theorem EndCfg4.zc_lamG_eq_bot (h : EndCfg4 G T Y) (hV : ∀ v : V, v ^ 2 = 1) {m : ℕ}
    (hm : 7 ≤ m) (hodd : Odd m) (hY : YAlt Y m) : EndQuot.zc (lamG G Y) = ⊥ := by
  have hYG : Y ≤ G := fun y hy => (h.adm.hYC hy).1
  have hΛ := normalClosure_subgroupOf_eq (G := G) (Y := Y) hYG
  rw [eq_bot_iff]
  intro x hx
  obtain ⟨-, hxc⟩ := EndQuot.mem_zc.mp hx
  refine Subgroup.mem_bot.mpr (Subtype.ext ?_)
  refine h.eq_one_of_commute hV hm hodd hY fun l hl => ?_
  have hlΛ : (⟨l, conjClosure_le hYG hl⟩ : ↥G) ∈ lamG G Y := by
    rw [hΛ]
    exact hl
  exact (congrArg Subtype.val (hxc _ hlΛ)).symm

end Center

section Cfg

variable {V : Type} [CommGroup V] [Finite V] {G T Y : Subgroup (MulAut V)}

theorem EndCfg4.cfg_of (h : EndCfg4 G T Y)
    (hstd : CFSG.Open.standardIsStandardSubgroup (Y.subgroupOf G))
    (hcen : Subgroup.center ↥(Y.subgroupOf G) = ⊥) (hev : Even (Nat.card ↥(Y.subgroupOf G))) :
    EndQuot.Cfg ↥G (lamG G Y) (Y.subgroupOf G) (T.subgroupOf G) := by
  have hTG : T ≤ G := h.adm.hTG
  have hYG : Y ≤ G := fun y hy => (h.adm.hYC hy).1
  have hΛ := normalClosure_subgroupOf_eq (G := G) (Y := Y) hYG
  let eΛ : ↥(conjClosure Y G) ≃* ↥(lamG G Y) :=
    (Subgroup.subgroupOfEquivOfLe (conjClosure_le hYG)).symm.trans
      (MulEquiv.subgroupCongr hΛ.symm)
  have hq : CFSG.IsQuasisimple ↥(conjClosure Y G) :=
    (EndQuot.isQuasisimple_iff_open _).mpr h.quasi
  refine
    { le := fun x hx => Subgroup.subset_normalClosure hx
      qs := LocalCores.isQuasisimple_of_mulEquiv eΛ hq
      fs := h.fstar.trans hΛ.symm
      zodd := ?_
      perf := ?_
      cen := hcen
      evenΥ := hev
      std := hstd
      gen := fun N hN hle => ?_
      hT := ?_
      T2 := h.adm.hT2.comap_subtype
      Tne := ?_
      Tmax := ?_ }
  · rw [card_zc_eq, ← card_center_congr eΛ]
    exact h.oddZ
  · apply Subgroup.map_injective G.subtype_injective
    rw [Subgroup.map_commutator, Subgroup.map_subgroupOf_eq_of_le hYG]
    exact h.adm.hperf
  · exact Subgroup.normalClosure_le_normal (fun x hx => hle hx)
  · intro t ht y hy
    have := Subgroup.mem_centralizer_iff.mp (h.adm.hYC hy).2 (t : MulAut V) ht
    exact Subtype.ext this.symm
  · intro hbot
    apply h.adm.hT1
    have := Subgroup.map_subgroupOf_eq_of_le hTG
    rw [hbot, Subgroup.map_bot] at this
    exact this.symm
  · intro T' hTT' hT'c hT'2
    have hmap : T'.map G.subtype = T := by
      apply h.sylow (T'.map G.subtype)
      · intro x hx
        exact ⟨⟨x, hTG hx⟩, hTT' (show (⟨x, hTG hx⟩ : ↥G) ∈ T.subgroupOf G from hx), rfl⟩
      · rintro _ ⟨t, ht, rfl⟩
        refine ⟨t.2, Subgroup.mem_centralizer_iff.mpr fun y hy => ?_⟩
        have := Subgroup.mem_centralizer_iff.mp (hT'c ht) ⟨y, hYG hy⟩
          (show (⟨y, hYG hy⟩ : ↥G) ∈ Y.subgroupOf G from hy)
        exact congrArg Subtype.val this
      · exact hT'2.map _
    calc T' = (T'.map G.subtype).comap G.subtype :=
          (Subgroup.comap_map_eq_self_of_injective G.subtype_injective T').symm
      _ = T.subgroupOf G := by rw [hmap]; rfl

end Cfg

section Bridge

theorem kProper_catalog_of_isKGroup (hB : TauCetiCatalogBridge) {Γ : Type} [Group Γ] [Finite Γ]
    (hK : CFSG.IsKGroup Γ) : CFSG.Assembly.KProper CFSG.Blueprint.Catalog Γ :=
  CFSG.Assembly.kProper_of_kGroupAllSimple_of_catalogImp hB hK

private theorem two_le_pRank_of_commuting {Γ : Type} [Group Γ] [Finite Γ] (H : Subgroup Γ)
    {x y : Γ} (hx : x ∈ H) (hy : y ∈ H) (hx2 : orderOf x = 2) (hy2 : orderOf y = 2)
    (hxy : x * y = y * x) (hne : x ≠ y) : 2 ≤ CFSG.Open.pRank 2 H := by
  obtain ⟨E, hEle, hE, hEcard⟩ :=
    CFSG.LocalAnalysis.ComponentInitial.AlternatingFourGroup.exists_elementary_four_of_commute
      hx2 hy2 hxy hne
  have hEH : E ≤ H := hEle.trans ((Subgroup.closure_le _).mpr (by
    rintro _ (rfl | rfl)
    · exact hx
    · exact hy))
  refine le_csSup ⟨Nat.card Γ, ?_⟩ ⟨E, hEH,
    (CFSG.SectionRank.isElementaryAbelian_iff_isElemAbelian 2 E).mp hE, ?_⟩
  · rintro r ⟨B, -, -, hB⟩
    calc r ≤ 2 ^ r := (Nat.lt_pow_self (by norm_num : 1 < 2)).le
      _ = Nat.card B := hB.symm
      _ ≤ Nat.card Γ := Subgroup.card_le_card_group B
  · rw [hEcard]
    norm_num

private theorem center_eq_bot_of_equiv_alt {Γ : Type*} [Group Γ] {m : ℕ} (hm : 4 ≤ m)
    (e : Γ ≃* alternatingGroup (Fin m)) : Subgroup.center Γ = ⊥ := by
  have h1 : (Subgroup.center Γ).map e.toMonoidHom = Subgroup.center (alternatingGroup (Fin m)) :=
    Subgroup.map_center_eq e
  rw [alternatingGroup.center_eq_bot (by simpa using hm)] at h1
  exact (Subgroup.map_eq_bot_iff_of_injective _ e.injective).mp h1

private theorem even_card_equiv_alt {Γ : Type*} [Group Γ] {m : ℕ} (hm : 4 ≤ m)
    (e : Γ ≃* alternatingGroup (Fin m)) : Even (Nat.card Γ) := by
  have : Nontrivial (Fin m) := Fin.nontrivial_iff_two_le.mpr (by omega)
  rw [Nat.card_congr e.toEquiv, nat_card_alternatingGroup, Nat.card_eq_fintype_card,
    Fintype.card_fin]
  obtain ⟨k, hk⟩ := Nat.dvd_factorial (by norm_num : 0 < 4) hm
  rw [hk]
  exact ⟨k, by omega⟩

end Bridge

section Main

@[expose] def AltM4 : Prop :=
  ∀ (V : Type) [CommGroup V] [Finite V], (∀ v : V, v ^ 2 = 1) →
    ∀ G T Y : Subgroup (MulAut V), EndCfg4 G T Y → ∀ m : ℕ, 7 ≤ m → Odd m → YAlt Y m →
      ∀ (θ : ↥(conjClosure Y G) ≃* alternatingGroup (Fin (m + 4))) (a b c d : Fin (m + 4)),
        a ≠ b → a ≠ c → a ≠ d → b ≠ c → b ≠ d → c ≠ d →
        (Y.subgroupOf (conjClosure Y G)).map θ.toMonoidHom = altStabilizer (m + 4) {a, b, c, d} →
          False

theorem alt2Rank1_of (hB : TauCetiCatalogBridge)
    (hK3 : RankTwoStandard.RankTwoAlternatingStandard) (hM4 : AltM4) : Alt2Rank1 := by
  intro V _ _ hV G T Y h m hm hodd hY a b haG hbG haC hbC ha2 hb2 ha1 hb1 hab hcomm
  classical
  have hYG : Y ≤ G := fun y hy => (h.adm.hYC hy).1
  obtain ⟨ε⟩ := hY
  have hzc := h.zc_lamG_eq_bot hV hm hodd ⟨ε⟩
  have hstd := h.std_of_YAlt hm ⟨ε⟩
  have hYe : ↥(Y.subgroupOf G) ≃* alternatingGroup (Fin m) :=
    (Subgroup.subgroupOfEquivOfLe hYG).trans ε
  have hcen := center_eq_bot_of_equiv_alt (by omega) hYe
  have cfg := h.cfg_of hstd hcen (even_card_equiv_alt (by omega) hYe)
  have hnn : ¬ (Y.subgroupOf G).Normal := by
    intro hn
    have hΛΥ : lamG G Y ≤ Y.subgroupOf G := cfg.gen _ hn le_rfl
    have hTz : T.subgroupOf G ≤ EndQuot.zc (lamG G Y) := fun x hx =>
      cfg.centralizer_le (Subgroup.centralizer_le hΛΥ (cfg.hT hx))
    rw [hzc, le_bot_iff] at hTz
    exact cfg.Tne hTz
  let a' : ↥G := ⟨a, haG⟩
  let b' : ↥G := ⟨b, hbG⟩
  have ha2' : a' ^ 2 = 1 := Subtype.ext (by simpa [a'] using ha2)
  have hb2' : b' ^ 2 = 1 := Subtype.ext (by simpa [b'] using hb2)
  have ha1' : a' ≠ 1 := fun h1 => ha1 (by simpa [a'] using congrArg Subtype.val h1)
  have hb1' : b' ≠ 1 := fun h1 => hb1 (by simpa [b'] using congrArg Subtype.val h1)
  have hab' : a' ≠ b' := fun h1 => hab (congrArg Subtype.val h1)
  have hcomm' : a' * b' = b' * a' := Subtype.ext hcomm
  have ha'o : orderOf a' = 2 := orderOf_eq_prime ha2' ha1'
  have hb'o : orderOf b' = 2 := orderOf_eq_prime hb2' hb1'
  have hcentr : ∀ c : ↥G, (c : MulAut V) ∈ Subgroup.centralizer (Y : Set (MulAut V)) →
      c ∈ Subgroup.centralizer ((Y.subgroupOf G : Subgroup ↥G) : Set ↥G) := by
    intro c hc
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    exact Subtype.ext ((Subgroup.mem_centralizer_iff.mp hc) y.val hy)
  have hrank : 2 ≤ CFSG.Open.pRank 2
      (Subgroup.centralizer ((Y.subgroupOf G : Subgroup ↥G) : Set ↥G)) :=
    two_le_pRank_of_commuting _ (hcentr a' haC) (hcentr b' hbC) ha'o hb'o hcomm' hab'
  have hhyp : RankTwoStandard.RankTwoHyp ↥G (Y.subgroupOf G) :=
    ⟨kProper_catalog_of_isKGroup hB h.kgroup, hstd, hnn, hrank⟩
  have hO : CFSG.Open.standardComponentOddCore ↥G = ⊥ := by
    have h1 := cfg.oddCore
    rw [hzc] at h1
    exact h1
  have hQ : Nonempty (RankTwoStandard.rankTwoQuot (Y.subgroupOf G) ≃*
      alternatingGroup (Fin m)) :=
    ⟨((QuotientGroup.quotientMulEquivOfEq hcen).trans QuotientGroup.quotientBot).trans hYe⟩
  rcases hK3 ↥G (Y.subgroupOf G) hhyp hO m (by omega) hQ with ⟨⟨e⟩⟩ | ⟨h5, -⟩ | ⟨h5, -, -⟩
  swap
  · omega
  swap
  · omega
  have hΛ := normalClosure_subgroupOf_eq (G := G) (Y := Y) hYG
  let θΛ : ↥(lamG G Y) ≃* alternatingGroup (Fin (m + 4)) := e
  let eΛ : ↥(conjClosure Y G) ≃* ↥(lamG G Y) :=
    (Subgroup.subgroupOfEquivOfLe (conjClosure_le hYG)).symm.trans
      (MulEquiv.subgroupCongr hΛ.symm)
  let θ : ↥(conjClosure Y G) ≃* alternatingGroup (Fin (m + 4)) := eΛ.trans θΛ
  have hbij := CFSG.GroupTheory.AutAlternating.aut_alternatingGroup_bijective_conj (m + 4)
    (by omega) (by omega)
  let e1 : Perm (Fin (m + 4)) ≃* MulAut (alternatingGroup (Fin (m + 4))) :=
    MulEquiv.ofBijective _ hbij
  let ρ : ↥G →* Perm (Fin (m + 4)) :=
    e1.symm.toMonoidHom.comp ((MulAut.congr θΛ).toMonoidHom.comp MulAut.conjNormal)
  have hρ : ∀ (g : ↥G) (l : ↥(lamG G Y)),
      ((θΛ (MulAut.conjNormal g l) : alternatingGroup (Fin (m + 4))) : Perm (Fin (m + 4))) =
        ρ g * (θΛ l : Perm (Fin (m + 4))) * (ρ g)⁻¹ := by
    intro g l
    have h1 : e1 (ρ g) = MulAut.congr θΛ (MulAut.conjNormal g) := e1.apply_symm_apply _
    have h2 := congrArg (fun φ : MulAut (alternatingGroup (Fin (m + 4))) =>
      ((φ (θΛ l) : alternatingGroup (Fin (m + 4))) : Perm (Fin (m + 4)))) h1
    simp only [e1, MulEquiv.ofBijective_apply, MulAut.conjNormal_apply, MulAut.congr_apply,
      MulEquiv.trans_apply, MulEquiv.symm_apply_apply] at h2
    exact h2.symm
  have hmemΛ : ∀ l ∈ conjClosure Y G, ∃ hlG : l ∈ G, (⟨l, hlG⟩ : ↥G) ∈ lamG G Y := fun l hl =>
    ⟨conjClosure_le hYG hl, by rw [hΛ]; exact hl⟩
  have hρinj : ∀ g : ↥G, ρ g = 1 → g = 1 := by
    intro g hg
    apply Subtype.ext
    refine h.eq_one_of_commute hV hm hodd ⟨ε⟩ (fun l hl => ?_)
    obtain ⟨hlG, hlΛ⟩ := hmemΛ l hl
    have h1 := hρ g ⟨⟨l, hlG⟩, hlΛ⟩
    rw [hg, one_mul, inv_one, mul_one] at h1
    have h2 : MulAut.conjNormal g ⟨⟨l, hlG⟩, hlΛ⟩ = ⟨⟨l, hlG⟩, hlΛ⟩ :=
      θΛ.injective (Subtype.ext h1)
    have h3 := congrArg (fun x : ↥(lamG G Y) => ((x : ↥G) : MulAut V)) h2
    simp only [MulAut.conjNormal_apply] at h3
    have h4 : (g : MulAut V) * l * (g : MulAut V)⁻¹ = l := h3
    calc (g : MulAut V) * l = (g : MulAut V) * l * (g : MulAut V)⁻¹ * (g : MulAut V) := by group
      _ = l * (g : MulAut V) := by rw [h4]
  let H : Subgroup (alternatingGroup (Fin (m + 4))) :=
    (Y.subgroupOf (conjClosure Y G)).map θ.toMonoidHom
  have hH : Nonempty (↥H ≃* alternatingGroup (Fin m)) :=
    ⟨((Y.subgroupOf (conjClosure Y G)).equivMapOfInjective θ.toMonoidHom θ.injective).symm.trans
      ((Subgroup.subgroupOfEquivOfLe (le_conjClosure : Y ≤ conjClosure Y G)).trans ε)⟩
  have hcentral : ∀ c : ↥G, (c : MulAut V) ∈ Subgroup.centralizer (Y : Set (MulAut V)) →
      ∀ x ∈ H, ρ c * (x : Perm (Fin (m + 4))) = (x : Perm (Fin (m + 4))) * ρ c := by
    rintro c hc _ ⟨y, hy, rfl⟩
    have hyY : (y : MulAut V) ∈ Y := hy
    obtain ⟨hyG, hyΛ⟩ := hmemΛ (y : MulAut V) y.2
    have h1 := hρ c ⟨⟨(y : MulAut V), hyG⟩, hyΛ⟩
    have h2 : MulAut.conjNormal c ⟨⟨(y : MulAut V), hyG⟩, hyΛ⟩ =
        ⟨⟨(y : MulAut V), hyG⟩, hyΛ⟩ := by
      apply Subtype.ext
      apply Subtype.ext
      show (c : MulAut V) * (y : MulAut V) * (c : MulAut V)⁻¹ = (y : MulAut V)
      have h3 := Subgroup.mem_centralizer_iff.mp hc (y : MulAut V) hyY
      calc (c : MulAut V) * (y : MulAut V) * (c : MulAut V)⁻¹
          = ((y : MulAut V) * (c : MulAut V)) * (c : MulAut V)⁻¹ := by rw [h3]
        _ = (y : MulAut V) := by group
    rw [h2] at h1
    show ρ c * ((θΛ ⟨⟨(y : MulAut V), hyG⟩, hyΛ⟩ : alternatingGroup (Fin (m + 4))) :
        Perm (Fin (m + 4))) = ((θΛ ⟨⟨(y : MulAut V), hyG⟩, hyΛ⟩ : alternatingGroup (Fin (m + 4))) :
        Perm (Fin (m + 4))) * ρ c
    calc ρ c * ((θΛ ⟨⟨(y : MulAut V), hyG⟩, hyΛ⟩ : alternatingGroup (Fin (m + 4))) :
          Perm (Fin (m + 4)))
        = (ρ c * ((θΛ ⟨⟨(y : MulAut V), hyG⟩, hyΛ⟩ : alternatingGroup (Fin (m + 4))) :
          Perm (Fin (m + 4))) * (ρ c)⁻¹) * ρ c := by group
      _ = ((θΛ ⟨⟨(y : MulAut V), hyG⟩, hyΛ⟩ : alternatingGroup (Fin (m + 4))) :
          Perm (Fin (m + 4))) * ρ c := by rw [← h1]
  have hρa2 : ρ a' * ρ a' = 1 := by rw [← map_mul, ← sq, ha2', map_one]
  have hρb2 : ρ b' * ρ b' = 1 := by rw [← map_mul, ← sq, hb2', map_one]
  have hρcomm : ρ a' * ρ b' = ρ b' * ρ a' := by rw [← map_mul, ← map_mul, hcomm']
  have hρa1 : ρ a' ≠ 1 := fun h1 => ha1' (hρinj a' h1)
  have hρb1 : ρ b' ≠ 1 := fun h1 => hb1' (hρinj b' h1)
  have hρne : ρ a' ≠ ρ b' := fun h1 => hab' (by
    have h2 : ρ (a'⁻¹ * b') = 1 := by rw [map_mul, map_inv, h1, inv_mul_cancel]
    exact inv_mul_eq_one.mp (hρinj _ h2))
  obtain ⟨a₁, b₁, c₁, d₁, h12, h13, h14, h23, h24, h34, hHeq, -⟩ :=
    exists_altStabilizer_of_commuting_involutions (by omega) hH hρa2 hρb2 hρcomm hρa1 hρb1 hρne
      (hcentral a' haC) (hcentral b' hbC)
  exact hM4 V hV G T Y h m hm hodd ⟨ε⟩ θ a₁ b₁ c₁ d₁ h12 h13 h14 h23 h24 h34 hHeq

end Main

end CFSG.CGT.PushingUpLit.CGT6
