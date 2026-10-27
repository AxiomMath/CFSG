module

public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55FTGLink
public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55BrData
public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8Final
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87L2Card

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Ivk8

namespace FTG

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Blueprint CFSG.GH74.GLS.Stage12
  CFSG.GH74.GLS.Stage2.Local CFSG.GH74.GLS.Stage2.Signalizer.Odd87
  CFSG.GH74.GLS.Stage2.Bender.Thm2 CFSG.GH74.GLS.IVK.Proofs2
open scoped commutatorElement

theorem card_alt_eleven : Nat.card (alternatingGroup (Fin 11)) = 19958400 := by
  rw [nat_card_alternatingGroup]
  simp [Nat.factorial]

theorem card_alt_nine : Nat.card (alternatingGroup (Fin 9)) = 181440 := by
  rw [nat_card_alternatingGroup]
  simp [Nat.factorial]

theorem card_alt_eight : Nat.card (alternatingGroup (Fin 8)) = 20160 := by
  rw [nat_card_alternatingGroup]
  simp [Nat.factorial]

theorem not_isL2_alt11 {Y : Type} [Group Y] (e : Y ≃* alternatingGroup (Fin 11)) :
    ¬ IVK.IsL2 Y (fun r => Odd r ∧ 5 ≤ r) := by
  rintro ⟨F, _, _, ⟨hr, -⟩, ⟨f⟩⟩
  have h1 : IVK.IsL2 Y (fun r => r = Nat.card F) := ⟨F, inferInstance, inferInstance, rfl, ⟨f⟩⟩
  have h2 := CFSG.GH74.GLS.Stage2.Local.P27.QId.card_isL2 hr h1
  rw [Nat.card_congr e.toEquiv, card_alt_eleven] at h2
  set r := Nat.card F
  rcases Nat.lt_or_ge r 342 with h | h
  · have h3 : r * (r ^ 2 - 1) ≤ 341 * (341 ^ 2 - 1) :=
      Nat.mul_le_mul (by omega) (Nat.sub_le_sub_right (Nat.pow_le_pow_left (by omega) 2) 1)
    have h4 : r * (r ^ 2 - 1) / 2 ≤ 341 * (341 ^ 2 - 1) / 2 := Nat.div_le_div_right h3
    rw [← h2] at h4
    norm_num at h4
  · rcases Nat.lt_or_ge r 344 with h' | h'
    · interval_cases r <;> norm_num at h2
    · have h3 : 344 * (344 ^ 2 - 1) ≤ r * (r ^ 2 - 1) :=
        Nat.mul_le_mul h' (Nat.sub_le_sub_right (Nat.pow_le_pow_left h' 2) 1)
      have h4 : 344 * (344 ^ 2 - 1) / 2 ≤ r * (r ^ 2 - 1) / 2 := Nat.div_le_div_right h3
      rw [← h2] at h4
      norm_num at h4

theorem kind_eq_ly_of_alt11 {k : Kind} {Y : Type} [Group Y] (e : Y ≃* alternatingGroup (Fin 11))
    (h : KindFactorAll k Y) : k = Kind.ly := by
  have hY : Nat.card Y = 19958400 := by rw [Nat.card_congr e.toEquiv, card_alt_eleven]
  cases k with
  | g2 => exact (not_isL2_alt11 e h).elim
  | psp4 => exact (not_isL2_alt11 e h).elim
  | m12 => exact (not_isL2_alt11 e h).elim
  | l4 ε =>
    rcases h with h | h
    · exact (not_isL2_alt11 e h).elim
    · have := h.card_dvd
      rw [hY, card_alt_seven] at this
      exact absurd this (by norm_num)
  | mcl =>
    obtain ⟨n, hn8, hn9, hs⟩ := h
    have h1 := hs.card_dvd
    rw [hY] at h1
    have h2 : Nat.card (alternatingGroup (Fin n)) ∣ 181440 := by
      interval_cases n
      · rw [card_alt_eight]; norm_num
      · rw [card_alt_nine]
    exact absurd (h1.trans h2) (by norm_num)
  | ly => rfl

theorem kind_of_alt7 {k : Kind} {Y : Type} [Group Y] (e : Y ≃* alternatingGroup (Fin 7))
    (h : KindFactorAll k Y) : (∃ ε, k = Kind.l4 ε) ∨ k = Kind.mcl ∨ k = Kind.ly := by
  have hL : ¬ IVK.IsL2 Y (fun r => Odd r ∧ 5 ≤ r) := fun hl => not_isL2_alt7 (by
    obtain ⟨F, _, _, hF, ⟨f⟩⟩ := hl
    exact ⟨F, inferInstance, inferInstance, hF, ⟨e.symm.trans f⟩⟩)
  cases k with
  | g2 => exact (hL h).elim
  | psp4 => exact (hL h).elim
  | m12 => exact (hL h).elim
  | l4 ε => exact Or.inl ⟨ε, rfl⟩
  | mcl => exact Or.inr (Or.inl rfl)
  | ly => exact Or.inr (Or.inr rfl)

variable {G : Type} [Group G] [Finite G]

theorem exists_inv_section_of_hbar (H : Subgroup G) (x : HBar H) (hx2 : orderOf x = 2)
    {Y : Type} [Group Y] (h : IsSection Y ↥(centralizer ({x} : Set (HBar H)))) :
    ∃ t : G, orderOf t = 2 ∧ IsSection Y ↥(centralizer ({t} : Set G)) := by
  have hodd : Odd (Nat.card ↥(pPrimeCore 2 ↥H)) :=
    Nat.coprime_two_left.mp pPrimeCore_coprime_card
  have hxx : x * x = 1 := by
    have := pow_orderOf_eq_one x
    rwa [hx2, pow_two] at this
  obtain ⟨t, ht2, htx⟩ := exists_involution_lift (pPrimeCore 2 ↥H) hodd hxx
  have hx'2 : (t : G) * (t : G) = 1 := congrArg (fun y : ↥H => (y : G)) ht2
  have hx'1 : (t : G) ≠ 1 := by
    intro h1
    have h2 : t = 1 := Subtype.ext h1
    rw [h2] at htx
    have h3 : x = 1 := htx.symm
    rw [h3, orderOf_one] at hx2
    exact absurd hx2 (by norm_num)
  have hx'ord : orderOf (t : G) = 2 := orderOf_eq_prime (by rw [pow_two]; exact hx'2) hx'1
  obtain ⟨D, f, hD, hf⟩ := csec_of_sig4B (z := (t : G)) (pPrimeCore 2 ↥H) t.2 hx'2 hodd
  have hzs : zSec (t : G) H t.2 (pPrimeCore 2 ↥H) = x := htx
  rw [← hzs] at h
  exact ⟨t, hx'ord, IsSection.of_le_le hD (IsSection.of_surjective f hf h)⟩

theorem kindFactor_of_even_center_of_one {z : G} {k : Kind}
    {S : Subgroup G} (hctx : Stage2Ctx G z k S) (hone : OneClassInv G) (H : Subgroup G)
    {J : Subgroup (HBar H)} (hJ : IsComponent J) (hev : Even (Nat.card (center ↥J))) :
    KindFactor k (↥J ⧸ center ↥J) := by
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' 2 (even_iff_two_dvd.mp hev)
  set u : HBar H := ((x : ↥J) : HBar H) with hu
  have hu2 : orderOf u = 2 := by
    rw [hu, Subgroup.orderOf_coe, Subgroup.orderOf_coe]
    exact hx
  have hJC : J ≤ centralizer ({u} : Set (HBar H)) := by
    intro v hv
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact congrArg Subtype.val (Subgroup.mem_center_iff.mp x.2 ⟨v, hv⟩)
  have hs : IsSimpleGroup (↥J ⧸ center ↥J) := hJ.1.2.1
  have hns : ¬ Group.IsSolvable (↥J ⧸ center ↥J) := by
    intro hsol
    obtain ⟨a, b, hab⟩ := hJ.1.2.2
    exact hab (IsSimpleGroup.comm_iff_isSolvable.mpr hsol a b)
  have hsec : IsSection (↥J ⧸ center ↥J) ↥J :=
    ⟨⊤, (QuotientGroup.mk' (center ↥J)).comp (⊤ : Subgroup ↥J).subtype, fun v => by
      obtain ⟨w, rfl⟩ := QuotientGroup.mk_surjective v
      exact ⟨⟨w, Subgroup.mem_top w⟩, rfl⟩⟩
  obtain ⟨t, ht2, hst⟩ := exists_inv_section_of_hbar H u hu2 (IsSection.of_le_le hJC hsec)
  obtain ⟨c, hc⟩ := isConj_iff.mp (hone z t hctx.orderOf_z ht2)
  obtain ⟨e⟩ := cenConj_nonempty c hc
  exact kindFactor_of_section_C hctx hns (IsSection.of_equiv e hst)

theorem comp_eq_top_of_isQuasisimple {B : Type} [Group B] [Finite B] (hB : IsQuasisimple B)
    {J : Subgroup B} (hJ : IsComponent J) : J = ⊤ := by
  have htop : IsComponent (⊤ : Subgroup B) :=
    ⟨CFSG.LocalCores.isQuasisimple_of_mulEquiv Subgroup.topEquiv.symm hB,
      Subgroup.IsSubnormal.top⟩
  rcases CFSG.LocalCores.distinct_components_commute hJ htop with h | h
  · exact h
  · exfalso
    have hle : J ≤ center B := by
      intro j hj
      have hc := Subgroup.commutator_eq_bot_iff_le_centralizer.mp h hj
      rw [Subgroup.mem_center_iff]
      intro b
      exact Subgroup.mem_centralizer_iff.mp hc b (Subgroup.mem_top b)
    obtain ⟨a, b, hab⟩ := not_comm_of_isQuasisimple hJ.1
    apply hab
    exact Subtype.ext (Subgroup.mem_center_iff.mp (hle a.2) (b : B)).symm

theorem quotCenter_top_equiv (B : Type) [Group B] :
    Nonempty ((↥(⊤ : Subgroup B) ⧸ center ↥(⊤ : Subgroup B)) ≃* (B ⧸ center B)) :=
  ⟨QuotientGroup.congr _ _ Subgroup.topEquiv (Subgroup.map_center_eq _)⟩

theorem isDoubleCoverOfAlt_of_equiv {B C : Type} [Group B] [Group C] (e : B ≃* C) {n : ℕ}
    (h : IsDoubleCoverOfAlt B n) : IsDoubleCoverOfAlt C n := by
  obtain ⟨hq, hc, ⟨φ⟩⟩ := h
  refine ⟨CFSG.LocalCores.isQuasisimple_of_mulEquiv e hq, ?_, ?_⟩
  · have hmap : (center B).map (e : B →* C) = center C := Subgroup.map_center_eq e
    rw [← hmap, Subgroup.card_map_of_injective e.injective]
    exact hc
  · exact ⟨(QuotientGroup.congr _ _ e (Subgroup.map_center_eq e)).symm.trans φ⟩

omit [Finite G] in
theorem l55_of_hbar {H : Subgroup G} {k : Kind} {p : ℕ}
    (h : IsDoubleCoverOfAlt (HBar H) 11) (hk : k = Kind.ly) (hp : p = 3) : L55 k p H := by
  have hl : layer (HBar H) = ⊤ := by
    rw [eq_top_iff]
    intro x _
    have htop : IsComponent (⊤ : Subgroup (HBar H)) :=
      ⟨CFSG.LocalCores.isQuasisimple_of_mulEquiv Subgroup.topEquiv.symm h.1,
        Subgroup.IsSubnormal.top⟩
    exact (le_sSup htop : (⊤ : Subgroup (HBar H)) ≤ layer (HBar H)) (Subgroup.mem_top x)
  refine ⟨hl, ?_, hk, hp⟩
  rw [hl]
  exact isDoubleCoverOfAlt_of_equiv Subgroup.topEquiv.symm h

theorem isQuasisimple_of_simple {B : Type} [Group B] [Finite B] (hs : IsSimpleGroup B)
    (hp : ¬ (Nat.card B).Prime) : IsQuasisimple B ∧ center B = ⊥ := by
  have hnc : ∃ a b : B, a * b ≠ b * a := by
    by_contra hall
    push Not at hall
    have hnt : Nontrivial B := hs.toNontrivial
    have h1 : 1 < Nat.card B := Finite.one_lt_card
    have hq : (Nat.card B).minFac.Prime := Nat.minFac_prime (by omega)
    have : Fact (Nat.card B).minFac.Prime := ⟨hq⟩
    obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' _ (Nat.minFac_dvd (Nat.card B))
    have hN : (zpowers x).Normal := ⟨fun n _ g => by rwa [hall g n, mul_inv_cancel_right]⟩
    rcases hs.eq_bot_or_eq_top_of_normal (zpowers x) with h | h
    · have : x = 1 := by rw [← Subgroup.mem_bot, ← h]; exact Subgroup.mem_zpowers x
      rw [this, orderOf_one] at hx
      exact hq.one_lt.ne hx
    · have hc : Nat.card (zpowers x) = Nat.card B := by rw [h, Subgroup.card_top]
      rw [Nat.card_zpowers, hx] at hc
      exact hp (hc ▸ hq)
  have hZ : center B = ⊥ := by
    rcases hs.eq_bot_or_eq_top_of_normal (center B) with h | h
    · exact h
    · exfalso
      obtain ⟨a, b, hab⟩ := hnc
      exact hab (Subgroup.mem_center_iff.mp (h ▸ Subgroup.mem_top b) a)
  have hperf : Group.IsPerfect B := by
    rcases hs.eq_bot_or_eq_top_of_normal (commutator B) with h | h
    · exfalso
      obtain ⟨a, b, hab⟩ := hnc
      have : ⁅a, b⁆ ∈ commutator B :=
        Subgroup.commutator_mem_commutator (Subgroup.mem_top a) (Subgroup.mem_top b)
      rw [h, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at this
      exact hab this
    · exact ⟨h⟩
  let e : (B ⧸ center B) ≃* B :=
    (QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot
  refine ⟨⟨hperf, (e.isSimpleGroup_congr).2 hs, ?_⟩, hZ⟩
  obtain ⟨a, b, hab⟩ := hnc
  exact ⟨e.symm a, e.symm b, fun h => hab (by simpa using congrArg e h)⟩

theorem maxSInv_of_cfg {z : G} {k : Kind} {S T Tstar : Subgroup G} {p : ℕ} {H P : Subgroup G}
    {g : G} {X Y : Subgroup G} (hcfg : Cfg55 G z k S T Tstar p H P g X Y) : MaxSInv p S H P := by
  have hT := hcfg.T_eq
  have hTs : Tstar = S := by
    rcases hcfg.c51.T5 with ⟨-, -, h⟩ | ⟨hno, -⟩
    · exact h
    · exact absurd hcfg.one hno
  have hmaxi := hcfg.c51.maxi
  rw [hT, hTs] at hmaxi
  obtain ⟨⟨hPH, hPp, hSN, -⟩, hmax⟩ := hmaxi
  refine ⟨hPH, hPp, hSN, fun W hWH hWp hSW hPW => hmax W ⟨hWH, hWp, hSW, ?_⟩ hPW⟩
  have hSH : S ≤ H := hT ▸ hcfg.T_le
  intro s hs
  exact Subgroup.mem_sup_left ⟨⟨hSH hs, hSW hs⟩, hs⟩

theorem not_le_oddCore {z : G} {k : Kind} {S T Tstar : Subgroup G} {p : ℕ} {H P : Subgroup G}
    {g : G} {X Y : Subgroup G} (hcfg : Cfg55 G z k S T Tstar p H P g X Y)
    {J : Subgroup (HBar H)} (hJc : ¬ barIn H (zpowers g) ≤ centralizer (J : Set (HBar H))) :
    ¬ P ≤ pPrimeCoreOf 2 H := by
  intro hP
  apply hJc
  have hg : g ∈ pPrimeCoreOf 2 H := hP hcfg.g_mem
  obtain ⟨g', hg', hgg'⟩ := hg
  have hbot : barIn H (zpowers g) = ⊥ := by
    rw [eq_bot_iff]
    rintro _ ⟨y, hy, rfl⟩
    have hy2 : (y : G) ∈ zpowers g := hy
    obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp hy2
    have hgg'' : (g' : G) = g := hgg'
    have hy' : y = g' ^ n := Subtype.ext (by rw [Subgroup.coe_zpow, hgg'', hn])
    rw [Subgroup.mem_bot, QuotientGroup.mk'_apply, hy', QuotientGroup.eq_one_iff]
    exact zpow_mem hg' n
  rw [hbot]
  exact bot_le

theorem hbar_of_ly {z : G} {k : Kind} {S T Tstar : Subgroup G} {p : ℕ} {H P : Subgroup G}
    {g : G} {X Y : Subgroup G} (hcfg : Cfg55 G z k S T Tstar p H P g X Y) (hk : k = Kind.ly)
    (hp : p = 3) {J : Subgroup (HBar H)} (hJ : IsComponent J)
    (hJc : ¬ barIn H (zpowers g) ≤ centralizer (J : Set (HBar H))) :
    J = ⊤ ∧ (IsDoubleCoverOfAlt (HBar H) 11 ∨
      Nat.card (HBar H ⧸ center (HBar H)) = 2 ^ 8 * 3 ^ 7 * 5 ^ 6 * 7 * 11 * 31 * 37 * 67) := by
  have hctx := hcfg.ctx
  subst hk hp
  have hSH : S ≤ H := hcfg.T_eq ▸ hcfg.T_le
  have h812 := ivk812CoreA_thm G z S hctx H hcfg.H_ne_top hSH P (maxSInv_of_cfg hcfg)
    (not_le_oddCore hcfg hJc)
  rcases h812 with h | h
  · exact ⟨comp_eq_top_of_isQuasisimple h.1 hJ, Or.inl h⟩
  · have hcard := card_of_isSporadic_Ly h
    obtain ⟨e⟩ := h
    have hs : IsSimpleGroup (HBar H) := (e.isSimpleGroup_congr).2 CFSG.Sporadic.Ly.isSimpleGroup_Ly
    obtain ⟨hq, hZ⟩ := isQuasisimple_of_simple hs (by rw [hcard]; norm_num)
    refine ⟨comp_eq_top_of_isQuasisimple hq hJ, Or.inr ?_⟩
    rw [← hcard, Nat.card_congr ((QuotientGroup.quotientMulEquivOfEq hZ).trans
      QuotientGroup.quotientBot).toEquiv]

theorem endgame_alt (hInv : InvSec) {z : G} {k : Kind} {S T Tstar : Subgroup G} {p : ℕ}
    {H P : Subgroup G} {g : G} {X Y : Subgroup G} (hcfg : Cfg55 G z k S T Tstar p H P g X Y)
    {Γ : Type} [Group Γ] {K : Subgroup Γ} [K.Normal] {P' : Subgroup Γ} {J : Subgroup (HBar H)}
    (hd : CompData H P g K P' J) (hp : p = 3) {n : ℕ} (hn : n = 7 ∨ n = 11)
    (hK : IsDoubleCoverOfAlt ↥K n) (hmcl : k = Kind.mcl → n = 7 → False) : L55 k p H := by
  obtain ⟨-, hZK, ⟨eK⟩⟩ := hK
  have hev : Even (Nat.card (center ↥J)) := hd.even (by rw [hZK]; exact even_two)
  obtain ⟨eKJ⟩ := hd.quot
  let eJ : (↥J ⧸ center ↥J) ≃* alternatingGroup (Fin n) := eKJ.symm.trans eK
  have hkf := kindFactorAll_of_even_center hInv hcfg.ctx H hd.comp hev
  have hk : k = Kind.ly := by
    rcases hn with rfl | rfl
    · rcases kind_of_alt7 eJ hkf with ⟨ε, rfl⟩ | rfl | h
      · exfalso
        have hone : OneClassInv G := by
          rcases hcfg.one with h | h
          · exact h
          · exact absurd h (by simp)
        obtain ⟨F, _, _, hF, ⟨f⟩⟩ :=
          (kindFactor_of_even_center_of_one hcfg.ctx hone H hd.comp hev :
            IVK.IsL2 (↥J ⧸ center ↥J) (fun r => Odd r ∧ 5 ≤ r))
        exact not_isL2_alt7 ⟨F, inferInstance, inferInstance, hF, ⟨eJ.symm.trans f⟩⟩
      · exact (hmcl rfl rfl).elim
      · exact h
    · exact kind_eq_ly_of_alt11 eJ hkf
  obtain ⟨hJt, h812⟩ := hbar_of_ly hcfg hk hp hd.comp hd.ncent
  subst hJt
  obtain ⟨eT⟩ := quotCenter_top_equiv (HBar H)
  have hcn : Nat.card (alternatingGroup (Fin n)) = Nat.card (HBar H ⧸ center (HBar H)) :=
    Nat.card_congr (eJ.symm.trans eT).toEquiv
  rcases h812 with h | h
  · rcases hn with rfl | rfl
    · exfalso
      obtain ⟨-, -, ⟨eA⟩⟩ := h
      rw [Nat.card_congr eA.toEquiv, card_alt_seven, card_alt_eleven] at hcn
      exact absurd hcn (by norm_num)
    · exact l55_of_hbar h hk hp
  · exfalso
    rw [h] at hcn
    rcases hn with rfl | rfl
    · rw [card_alt_seven] at hcn
      exact absurd hcn (by norm_num)
    · rw [card_alt_eleven] at hcn
      exact absurd hcn (by norm_num)

end FTG

end CFSG.GH74.GLS.Stage2.Signalizer.Ivk8
