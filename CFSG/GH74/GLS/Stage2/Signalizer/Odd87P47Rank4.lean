module

public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87P47Stmt
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.KleinFourOfCommutingInvolutions
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.CardSupOfDisjointNormalizer

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Odd87

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage2.Local CFSG.GH74.GLS.Bg CFSG.GH74.GLS.Stage2.Signalizer
open scoped commutatorElement Pointwise

section Dihedral

theorem exists_commuting_invol_dihedral {k : ℕ} (hk : 2 ≤ k) (hk2 : Even k) :
    ∃ a b : DihedralGroup k, a ≠ b ∧ a * a = 1 ∧ b * b = 1 ∧ a ≠ 1 ∧ b ≠ 1 ∧ a * b = b * a := by
  have : NeZero k := ⟨by omega⟩
  obtain ⟨m, hm⟩ := hk2
  have hmm : ((m : ℕ) : ZMod k) + (m : ZMod k) = 0 := by
    have : ((m + m : ℕ) : ZMod k) = ((k : ℕ) : ZMod k) := by rw [hm]
    rw [ZMod.natCast_self] at this
    simpa using this
  refine ⟨DihedralGroup.r (m : ZMod k), DihedralGroup.sr 0, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro h; cases h
  · simp [DihedralGroup.r_mul_r, hmm]
  · simp
  · intro h
    have h1 : (DihedralGroup.r (m : ZMod k)) = DihedralGroup.r 0 := h
    have h2 : ((m : ℕ) : ZMod k) = 0 := DihedralGroup.r.inj h1
    rw [ZMod.natCast_eq_zero_iff] at h2
    have := Nat.le_of_dvd (by omega) h2
    omega
  · intro h
    change DihedralGroup.sr (0 : ZMod k) = DihedralGroup.r 0 at h
    cases h
  · rw [DihedralGroup.r_mul_sr, DihedralGroup.sr_mul_r]
    congr 1
    rw [zero_sub, zero_add]
    exact neg_eq_of_add_eq_zero_left hmm

theorem exists_commuting_invol_of_dihedral {G : Type} [Group G] [Finite G] {D : Subgroup G} (hD2 : IsPGroup 2 ↥D)
    (hd : IsDihedral ↥D) :
    ∃ a b : G, a ∈ D ∧ b ∈ D ∧ a ≠ b ∧ a * a = 1 ∧ b * b = 1 ∧ a ≠ 1 ∧ b ≠ 1 ∧ a * b = b * a := by
  obtain ⟨m, k, hmk, hk2, ⟨e⟩⟩ := hd
  have hk0 : NeZero k := ⟨by omega⟩
  have hcard : Nat.card ↥D = 2 * k := by
    rw [Nat.card_congr e.toEquiv]
    simp [Nat.card_eq_fintype_card, DihedralGroup.card]
  obtain ⟨n, hn⟩ := hD2.exists_card_eq
  have hkeven : Even k := by
    have h4 : 2 * k = 2 ^ n := by rw [← hcard, hn]
    have hn2 : 2 ≤ n := by
      by_contra hlt
      push Not at hlt
      interval_cases n <;> omega
    have : 4 ∣ 2 ^ n := by
      have : 2 ^ 2 ∣ 2 ^ n := pow_dvd_pow 2 hn2
      simpa using this
    rw [← h4] at this
    exact even_iff_two_dvd.mpr (by omega)
  obtain ⟨a, b, hab, ha2, hb2, ha1, hb1, hcom⟩ := exists_commuting_invol_dihedral hk2 hkeven
  refine ⟨(e.symm a : G), (e.symm b : G), (e.symm a).2, (e.symm b).2, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro h
    exact hab (e.symm.injective (Subtype.ext h))
  · have := congrArg (fun w : ↥D => (w : G)) (show e.symm a * e.symm a = 1 by rw [← map_mul, ha2, map_one])
    simpa using this
  · have := congrArg (fun w : ↥D => (w : G)) (show e.symm b * e.symm b = 1 by rw [← map_mul, hb2, map_one])
    simpa using this
  · intro h
    apply ha1
    apply e.symm.injective
    rw [map_one]
    exact Subtype.ext (by simpa using h)
  · intro h
    apply hb1
    apply e.symm.injective
    rw [map_one]
    exact Subtype.ext (by simpa using h)
  · have := congrArg (fun w : ↥D => (w : G)) (show e.symm a * e.symm b = e.symm b * e.symm a by rw [← map_mul, ← map_mul, hcom])
    simpa using this

end Dihedral

section Rank4

variable {G : Type} [Group G]

theorem isElemAbelian_of_isKleinFour {V : Subgroup G} (h : IsKleinFour ↥V) :
    CFSG.Open.IsElemAbelian 2 V := by
  refine ⟨h.isMulCommutative, fun x hx => ?_⟩
  have h1 := Monoid.pow_exponent_eq_one (⟨x, hx⟩ : ↥V)
  rw [h.exponent_two] at h1
  exact congrArg Subtype.val h1

theorem elemAbelian_sup_card [Finite G] {W V D : Subgroup G} (hW : CFSG.Open.IsElemAbelian 2 W)
    (hV : CFSG.Open.IsElemAbelian 2 V) (hVD : V ≤ D) (hcomm : ∀ w ∈ W, ∀ d ∈ D, w * d = d * w)
    (hdisj : W ⊓ D = ⊥) :
    CFSG.Open.IsElemAbelian 2 (W ⊔ V) ∧ Nat.card ↥(W ⊔ V) = Nat.card ↥W * Nat.card ↥V := by
  have hc : ∀ v ∈ V, ∀ w ∈ W, v * w * v⁻¹ = w := fun v hv w hw => by
    have := hcomm w hw v (hVD hv)
    rw [← this, mul_inv_cancel_right]
  have hvw : ∀ v ∈ V, ∀ w ∈ W, v * w = w * v := fun v hv w hw => by
    have := hcomm w hw v (hVD hv)
    exact this.symm
  have hnorm : V ≤ normalizer (W : Set G) := by
    intro v hv
    rw [Subgroup.mem_normalizer_iff]
    intro w
    constructor
    · intro hw
      rw [hc v hv w hw]
      exact hw
    · intro hw
      have h1 : v⁻¹ * (v * w * v⁻¹) * (v⁻¹)⁻¹ = v * w * v⁻¹ := hc v⁻¹ (V.inv_mem hv) _ hw
      have h2 : v⁻¹ * (v * w * v⁻¹) * (v⁻¹)⁻¹ = w := by group
      rw [h2] at h1
      rw [h1]
      exact hw
  have hdisjoint : Disjoint W V := (disjoint_iff.mpr hdisj).mono_right hVD
  have hmul : (↑(W ⊔ V) : Set G) = (W : Set G) * (V : Set G) :=
    Subgroup.coe_mul_of_right_le_normalizer_left W V hnorm
  have hdecomp : ∀ x ∈ W ⊔ V, ∃ w ∈ W, ∃ v ∈ V, x = w * v := fun x hx => by
    have : x ∈ (W : Set G) * (V : Set G) := by rw [← hmul]; exact hx
    obtain ⟨w, hw, v, hv, hxe⟩ := this
    exact ⟨w, hw, v, hv, hxe.symm⟩
  refine ⟨⟨⟨⟨fun a b => ?_⟩⟩, fun x hx => ?_⟩, ?_⟩
  · obtain ⟨w₁, hw₁, v₁, hv₁, ha⟩ := hdecomp a a.2
    obtain ⟨w₂, hw₂, v₂, hv₂, hb⟩ := hdecomp b b.2
    apply Subtype.ext
    show (a : G) * b = b * a
    rw [ha, hb]
    have hWc : w₁ * w₂ = w₂ * w₁ := hW.1.is_comm.comm (⟨w₁, hw₁⟩ : ↥W) ⟨w₂, hw₂⟩ |> congrArg Subtype.val
    have hVc : v₁ * v₂ = v₂ * v₁ := hV.1.is_comm.comm (⟨v₁, hv₁⟩ : ↥V) ⟨v₂, hv₂⟩ |> congrArg Subtype.val
    calc w₁ * v₁ * (w₂ * v₂) = w₁ * (v₁ * w₂) * v₂ := by group
      _ = w₁ * (w₂ * v₁) * v₂ := by rw [hvw v₁ hv₁ w₂ hw₂]
      _ = (w₁ * w₂) * (v₁ * v₂) := by group
      _ = (w₂ * w₁) * (v₂ * v₁) := by rw [hWc, hVc]
      _ = w₂ * (w₁ * v₂) * v₁ := by group
      _ = w₂ * (v₂ * w₁) * v₁ := by rw [hvw v₂ hv₂ w₁ hw₁]
      _ = w₂ * v₂ * (w₁ * v₁) := by group
  · obtain ⟨w, hw, v, hv, hxe⟩ := hdecomp x hx
    rw [hxe]
    have hw2 : w ^ 2 = 1 := hW.2 w hw
    have hv2 : v ^ 2 = 1 := hV.2 v hv
    calc (w * v) ^ 2 = (w * v) * (w * v) := pow_two _
      _ = w * (v * w) * v := by simp only [mul_assoc]
      _ = w * (w * v) * v := by rw [hvw v hv w hw]
      _ = (w * w) * (v * v) := by simp only [mul_assoc]
      _ = 1 := by rw [← pow_two, ← pow_two, hw2, hv2, one_mul]
  · exact CFSG.GorensteinWalter.card_sup_eq_mul_of_disjoint_of_le_normalizer W V hnorm hdisjoint

end Rank4

section Main

variable {G : Type} [Group G] [Finite G]

theorem stage1_two {z : G} {k : Kind} {S : Subgroup G} (ctx : Stage2Ctx G z k S)
    (hn : ¬ TypeOneCase G k) :
    ∃ (q : ℕ) (L₁ L₂ : Subgroup (CentralizerBar z)) (x : G),
      Stage1Pair G z S q L₁ L₂ ∧ TwoClassData G z S L₁ L₂ q x := by
  have hd := ctx.data
  cases hd with
  | g2 hg => exact absurd (Or.inl hg.one_class) hn
  | m12 _ => exact absurd (Or.inr rfl) hn
  | psp4 h =>
    obtain ⟨q, L₁, L₂, hq⟩ := h
    obtain ⟨x, hx⟩ := hq.two
    exact ⟨q, L₁, L₂, x, hq.pair, hx⟩
  | l4 ε h =>
    obtain ⟨q, L₁, L₂, hq⟩ := h
    rcases hq.fusion with ⟨-, h1⟩ | ⟨-, x, hx, -⟩
    · exact absurd (Or.inl h1) hn
    · exact ⟨q, L₁, L₂, x, hq.pair, hx⟩
  | mcl hm =>
    obtain ⟨n, -, hs⟩ := hm
    exact absurd (Or.inl hs.one_class) hn
  | ly hm =>
    obtain ⟨n, -, hs⟩ := hm
    exact absurd (Or.inl hs.one_class) hn

omit [Finite G] in
theorem swaps_of_swapsComps {z t : G} {L₁ L₂ : Subgroup (CentralizerBar z)}
    (hc : {K : Subgroup (CentralizerBar z) | IsComponent K} = {L₁, L₂}) (h : SwapsComps z t) :
    Swaps z t L₁ L₂ := by
  obtain ⟨L₁', L₂', -, hc', hsw⟩ := h
  have h12 : ({L₁, L₂} : Set (Subgroup (CentralizerBar z))) = {L₁', L₂'} := hc.symm.trans hc'
  rcases Set.pair_eq_pair_iff.mp h12 with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · subst h1
    subst h2
    exact hsw
  · subst h1
    subst h2
    obtain ⟨ht, ha, hb⟩ := hsw
    exact ⟨ht, hb, ha⟩

theorem T4CS.exists_elemAbelian_sixteen {z : G} {k : Kind} {S T : Subgroup G}
    (ctx : Stage2Ctx G z k S) (hn : ¬ TypeOneCase G k) (hT : T4CS z k S T) :
    ∃ E : Subgroup G, E ≤ T ∧ CFSG.Open.IsElemAbelian 2 E ∧ Nat.card ↥E = 16 := by
  rcases hT with ⟨h1, -⟩ | ⟨-, U, hUS, hU4, hzU, ⟨t, htU, htz, hsw⟩, -, hTeq, -⟩
  · exact absurd h1 hn
  obtain ⟨q, L₁, L₂, x, hpair, htwo⟩ := stage1_two ctx hn
  have hswaps : Swaps z t L₁ L₂ := swaps_of_swapsComps hpair.comps hsw
  have htS : t ∈ S := hUS htU
  obtain ⟨hxt, -, ⟨-, D, hDprod, hDdih⟩, -⟩ := htwo.swap_conseq t htS htz hswaps
  have hU4' : CFSG.Open.IsElemAbelian 2 U ∧ Nat.card ↥U = 4 :=
    ⟨(CFSG.SectionRank.isElementaryAbelian_iff_isElemAbelian 2 U).mp hU4.1, hU4.2⟩
  have hz2' : orderOf z = 2 := ctx.orderOf_z
  have hz2 : z * z = 1 := by
    have := pow_orderOf_eq_one z
    rw [hz2', pow_two] at this
    exact this
  have ht2 : t * t = 1 := by
    have := hU4'.1.2 t htU
    rwa [pow_two] at this
  have hz1 : z ≠ 1 := fun h => by
    rw [h, orderOf_one] at hz2'
    omega
  have ht1 : t ≠ 1 := fun h => by
    subst h
    exact hz1 (isConj_one_right.mp htz.symm)
  have hzt : z ≠ t := fun h => by
    subst h
    have h3 : IsConj x (1 : G) := by simpa [hz2] using hxt
    have h4 : x = 1 := isConj_one_right.mp h3.symm
    have h5 := htwo.x_inv
    rw [h4, orderOf_one] at h5
    omega
  have hcomm : Commute z t := by
    have := hU4'.1.1.is_comm.comm (⟨z, hzU⟩ : ↥U) ⟨t, htU⟩
    exact congrArg Subtype.val this
  set W : Subgroup G := CFSG.GorensteinWalter.kleinFourOfCommutingInvolutions z t hz2 ht2 hcomm
    with hWdef
  have hW4 : IsKleinFour ↥W :=
    CFSG.GorensteinWalter.isKleinFour_kleinFourOfCommutingInvolutions z t hz2 ht2 hz1 ht1 hzt hcomm
  have hWU : W ≤ U := by
    intro y hy
    change y ∈ ({z * t, z, t, 1} : Set G) at hy
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
    rcases hy with rfl | rfl | rfl | rfl
    · exact U.mul_mem hzU htU
    · exact hzU
    · exact htU
    · exact U.one_mem
  have hWeq : W = U := Subgroup.eq_of_le_of_card_ge hWU (by rw [hU4'.2, hW4.card_four])
  have hW0 : zpowers z ⊔ zpowers t = U := by
    apply le_antisymm
    · exact sup_le (Subgroup.zpowers_le.mpr hzU) (Subgroup.zpowers_le.mpr htU)
    · rw [← hWeq]
      intro y hy
      change y ∈ ({z * t, z, t, 1} : Set G) at hy
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
      rcases hy with rfl | rfl | rfl | rfl
      · exact Subgroup.mul_mem _ (Subgroup.mem_sup_left (Subgroup.mem_zpowers _))
          (Subgroup.mem_sup_right (Subgroup.mem_zpowers _))
      · exact Subgroup.mem_sup_left (Subgroup.mem_zpowers _)
      · exact Subgroup.mem_sup_right (Subgroup.mem_zpowers _)
      · exact Subgroup.one_mem _
  rw [hW0] at hDprod
  obtain ⟨hsup, hcommUD, hdisj⟩ := hDprod
  have hSz : S ≤ centralizer ({z} : Set G) := ctx.sylow.le
  have hT' : T = U ⊔ D := by
    rw [hTeq, hsup]
    apply le_antisymm
    · exact inf_le_inf_left S (Subgroup.centralizer_le (Set.singleton_subset_iff.mpr htU))
    · intro s hs
      have hzs : z ∈ centralizer ({s} : Set G) := by
        rw [Subgroup.mem_centralizer_singleton_iff]
        exact (Subgroup.mem_centralizer_singleton_iff.mp (hSz hs.1)).symm
      have hts : t ∈ centralizer ({s} : Set G) := by
        rw [Subgroup.mem_centralizer_singleton_iff]
        exact (Subgroup.mem_centralizer_singleton_iff.mp hs.2).symm
      have hUs : U ≤ centralizer ({s} : Set G) := by
        rw [← hW0]
        exact sup_le (Subgroup.zpowers_le.mpr hzs) (Subgroup.zpowers_le.mpr hts)
      refine ⟨hs.1, Subgroup.mem_centralizer_iff.mpr ?_⟩
      intro u hu
      have := Subgroup.mem_centralizer_singleton_iff.mp (hUs hu)
      exact this
  have hDS : D ≤ S := by
    have : D ≤ U ⊔ D := le_sup_right
    rw [hsup] at this
    exact this.trans inf_le_left
  have hD2 : IsPGroup 2 ↥D := ctx.sylow.isPGroup.to_le hDS
  obtain ⟨a, b, haD, hbD, hab, ha2, hb2, ha1, hb1, hcab⟩ := exists_commuting_invol_of_dihedral hD2 hDdih
  set V : Subgroup G := CFSG.GorensteinWalter.kleinFourOfCommutingInvolutions a b ha2 hb2 hcab
    with hVdef
  have hV4 : IsKleinFour ↥V :=
    CFSG.GorensteinWalter.isKleinFour_kleinFourOfCommutingInvolutions a b ha2 hb2 ha1 hb1 hab hcab
  have hVD : V ≤ D := by
    intro y hy
    change y ∈ ({a * b, a, b, 1} : Set G) at hy
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
    rcases hy with rfl | rfl | rfl | rfl
    · exact D.mul_mem haD hbD
    · exact haD
    · exact hbD
    · exact D.one_mem
  obtain ⟨hEab, hEcard⟩ := elemAbelian_sup_card hU4'.1 (isElemAbelian_of_isKleinFour hV4) hVD
    hcommUD hdisj
  refine ⟨U ⊔ V, ?_, hEab, ?_⟩
  · rw [hT']
    exact sup_le_sup_left hVD U
  · rw [hEcard, hU4'.2, hV4.card_four]

end Main

end CFSG.GH74.GLS.Stage2.Signalizer.Odd87
