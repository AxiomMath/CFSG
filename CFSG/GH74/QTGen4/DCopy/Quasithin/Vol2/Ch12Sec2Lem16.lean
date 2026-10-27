module

public import CFSG.Quasithin.Vol2.Ch12Sec2Lem16
public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch12Sec2Lem16Stmts
public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch12Sec2Statements
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.Stmt331F4

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique
open scoped IsMulCommutative

open Orbit

namespace Lem16

variable {G : Type} [Group G]

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G] {T L V : Subgroup G}

theorem false_of_twisted_F4 (h331 : Stmt3_3_1_F4) (h6 : CoreSixTwoCentral) (hW : G2WeylTwoCentral)
    (h8 : Lem12216CoreEight_F4) (hH : Hyp1223 G T L V) (hE : NoEscape12_2_13 L V)
    [IsMulCommutative ↥V] (hsq : ∀ w : ↥V, w ^ 2 = 1) {z : ↥V} (hz1 : z ≠ 1)
    (hzfix : fixV (autOn L V) = Subgroup.zpowers z)
    (hmodE : (altCoreModel 6).Realizes (autOn L V) ⊤ ⊥ ∨
      (altCoreModel 8).Realizes (autOn L V) ⊤ ⊥ ∨ G2WeylDerived (autOn L V))
    (hMV : Subgroup.normalizer (L : Set G) ≤ Subgroup.normalizer (V : Set G))
    {v g : G} (hv : v ∈ V) (hvz : v ∉ Subgroup.zpowers (z : G))
    (hgM : g ∉ Subgroup.normalizer (L : Set G)) (hg : g⁻¹ * v * g = v * z) : False := by
  set M := Subgroup.normalizer (L : Set G) with hMdef
  have hLV : L ≤ Subgroup.normalizer (V : Set G) := le_normalizer_of_hyp1223 hH
  have hLM : L ≤ M := Subgroup.le_normalizer
  have hTM : T ≤ M := hH.normalizes
  have hz2 : (z : G) * z = 1 := by
    have := congrArg Subtype.val (hsq z)
    rwa [pow_two] at this
  have hz2' : z * z = 1 := Subtype.ext hz2
  have hz1G : (z : G) ≠ 1 := fun h => hz1 (Subtype.ext h)

  have hCVL : V ⊓ Subgroup.centralizer (L : Set G) = Subgroup.zpowers (z : G) := by
    have h1 := congrArg (Subgroup.map V.subtype) ((fixV_autOn_eq hLV).symm.trans hzfix)
    rw [Subgroup.subgroupOf_map_subtype, MonoidHom.map_zpowers] at h1
    rw [inf_comm]
    exact h1

  have hMz : M ≤ Subgroup.centralizer ({(z : G)} : Set G) := by
    intro m hm
    have hzC : (z : G) ∈ V ⊓ Subgroup.centralizer (L : Set G) := by
      rw [hCVL]
      exact Subgroup.mem_zpowers _
    have h1 : m * (z : G) * m⁻¹ ∈ V ⊓ Subgroup.centralizer (L : Set G) :=
      ⟨(Subgroup.mem_normalizer_iff.mp (hMV hm) _).mp hzC.1,
        (Subgroup.mem_normalizer_iff.mp (A4.mem_normalizer_centralizer hm) _).mp hzC.2⟩
    rw [hCVL, mem_zpowers_of_mul_self_eq_one hz2] at h1
    rw [Subgroup.mem_centralizer_singleton_iff]
    rcases h1 with h | h
    · exfalso
      apply hz1G
      calc (z : G) = m⁻¹ * (m * z * m⁻¹) * m := by group
        _ = 1 := by rw [h]; group
    · calc m * (z : G) = m * z * m⁻¹ * m := by group
        _ = z * m := by rw [h]
  have hzM : Subgroup.centralizer ({(z : G)} : Set G) ≤ M := hE z z.2 hz1G
  have hv1 : v ≠ 1 := fun h => hvz (h ▸ Subgroup.one_mem _)
  have hvz' : v ≠ z := fun h => hvz (h ▸ Subgroup.mem_zpowers _)

  have hmove : ∀ m ∈ M, (m * g * m⁻¹)⁻¹ * (m * v * m⁻¹) * (m * g * m⁻¹) =
      (m * v * m⁻¹) * z ∧ m * g * m⁻¹ ∉ M := by
    intro m hm
    have hmz := Subgroup.mem_centralizer_singleton_iff.mp (hMz hm)
    refine ⟨?_, fun h => hgM ?_⟩
    · calc (m * g * m⁻¹)⁻¹ * (m * v * m⁻¹) * (m * g * m⁻¹) = m * (g⁻¹ * v * g) * m⁻¹ := by
            group
        _ = m * v * m⁻¹ * (m * z * m⁻¹) := by rw [hg]; group
        _ = m * v * m⁻¹ * z := by rw [hmz]; group
    · have := M.mul_mem (M.mul_mem (M.inv_mem hm) h) hm
      rwa [show m⁻¹ * (m * g * m⁻¹) * m = g by group] at this
  have hmV : ∀ m ∈ M, m * v * m⁻¹ ∈ V := fun m hm =>
    (Subgroup.mem_normalizer_iff.mp (hMV hm) v).mp hv
  have hmvz : ∀ m ∈ M, m * v * m⁻¹ ∉ Subgroup.zpowers (z : G) := by
    intro m hm h
    rw [mem_zpowers_of_mul_self_eq_one hz2] at h
    have hmz := Subgroup.mem_centralizer_singleton_iff.mp (hMz hm)
    rcases h with h | h
    · exact hv1 (by
        calc v = m⁻¹ * (m * v * m⁻¹) * m := by group
          _ = 1 := by rw [h]; group)
    · exact hvz' (by
        calc v = m⁻¹ * (m * v * m⁻¹) * m := by group
          _ = m⁻¹ * (m * z) := by rw [h, mul_assoc, ← hmz]
          _ = z := by group)

  have hNT : Subgroup.normalizer (T : Set G) ≤ M := by
    obtain ⟨⟨hmax2, -, -⟩, -, -, hNT0, -⟩ :=
      (h331 G T hH.simple hH.nonabelian hH.qtke hH.sylow).2 L hH.maximal hH.quasisimple
    rwa [hH.conjClosure_eq] at hNT0
  have hTsyl : IsSylowTwoOf T M := isSylowTwoOf_of_quasithinIsSylowTwo hH.sylow hTM
  have hu1 : ∀ m ∈ M, m * v * m⁻¹ * (z : G) ≠ 1 := by
    intro m hm h
    apply hmvz m hm
    rw [mul_eq_one_iff_eq_inv.mp h]
    exact Subgroup.inv_mem _ (Subgroup.mem_zpowers _)

  have hTu : ∀ m : G, T ⊓ Subgroup.centralizer ({m * v * m⁻¹} : Set G) ≤
      Subgroup.centralizer ({m * v * m⁻¹ * (z : G)} : Set G) := by
    intro m t ht
    have h1 := Subgroup.mem_centralizer_singleton_iff.mp ht.2
    have h2 := Subgroup.mem_centralizer_singleton_iff.mp (hMz (hTM ht.1))
    rw [Subgroup.mem_centralizer_singleton_iff]
    calc t * (m * v * m⁻¹ * z) = (t * (m * v * m⁻¹)) * z := by group
      _ = (m * v * m⁻¹ * t) * z := by rw [h1]
      _ = m * v * m⁻¹ * (t * z) := by group
      _ = m * v * m⁻¹ * (z * t) := by rw [h2]
      _ = m * v * m⁻¹ * z * t := by group

  have hback : ∀ m ∈ M, ∀ c ∈ Subgroup.centralizer ({m * v * m⁻¹ * (z : G)} : Set G),
      m * g * m⁻¹ * c ∉ M := by
    intro m hm c hc h
    have hcM : c ∈ M := hE _ (V.mul_mem (hmV m hm) z.2) (hu1 m hm) hc
    apply (hmove m hm).2
    have := M.mul_mem h (M.inv_mem hcM)
    rwa [mul_inv_cancel_right] at this

  have hfin2 : (∃ x ∈ autOn M V, ∀ s ∈ autOn T V,
      (s : MulAut ↥V) ((x : MulAut ↥V) ⟨v, hv⟩) = (x : MulAut ↥V) ⟨v, hv⟩) → False := by
    rintro ⟨x, hx, hxs⟩
    obtain ⟨⟨m, hmM⟩, rfl⟩ := (A4.mem_autOn_iff hMV).mp hx
    have hTN : T ≤ Subgroup.normalizer (V : Set G) := hTM.trans hMV
    have hTv : T ≤ Subgroup.centralizer ({m * v * m⁻¹} : Set G) := by
      intro t ht
      have hts := hxs (A4.actionOn V T hTN ⟨t, ht⟩) ((A4.mem_autOn_iff hTN).mpr ⟨⟨t, ht⟩, rfl⟩)
      have h1 := congrArg Subtype.val hts
      rw [A4.actionOn_apply_coe, A4.actionOn_apply_coe] at h1
      change t * (m * v * m⁻¹) * t⁻¹ = m * v * m⁻¹ at h1
      rw [Subgroup.mem_centralizer_singleton_iff]
      calc t * (m * v * m⁻¹) = t * (m * v * m⁻¹) * t⁻¹ * t := by group
        _ = m * v * m⁻¹ * t := by rw [h1]
    have hTsylv : IsSylowTwoOf T (Subgroup.centralizer ({m * v * m⁻¹} : Set G)) :=
      isSylowTwoOf_of_quasithinIsSylowTwo hH.sylow hTv
    have hTu' : T ≤ Subgroup.centralizer ({m * v * m⁻¹ * (z : G)} : Set G) :=
      fun t ht => hTu m ⟨ht, hTv ht⟩
    obtain ⟨c, hc, hcN, -⟩ := exists_mul_mem_normalizer hTsylv hTu' (hmove m hmM).1
    exact hback m hmM c hc (hNT hcN)
  have hzH : z ∈ fixV (autOn L V) := hzfix ▸ Subgroup.mem_zpowers z
  have hLMb : autOn L V ≤ autOn M V := A4.autOn_mono hLM
  have hMN : autOn M V ≤ Subgroup.normalizer (autOn L V : Set (MulAut ↥V)) :=
    autOn_le_normalizer_autOn hLV hMV le_rfl
  have hSsyl : IsSylowTwoOf (autOn T V) (autOn M V) := Setup.isSylowTwoOf_autOn hTsyl hMV
  have hv1' : (⟨v, hv⟩ : ↥V) ≠ 1 := fun h => hv1 (congrArg Subtype.val h)
  have hvz'' : (⟨v, hv⟩ : ↥V) ≠ z := fun h => hvz' (congrArg Subtype.val h)
  rcases hmodE with hE6 | hE8 | hWeyl
  ·
    exact hfin2 (h6 ↥V (autOn L V) (autOn M V) (autOn T V) z hz1 hzH hE6 hLMb hMN hSsyl
      ⟨v, hv⟩ hv1' hvz'')
  ·
    obtain ⟨S, hS⟩ := exists_isSylowTwoOf (Subgroup.centralizer ({v} : Set G))
    have hSM : S ≤ M := hS.1.trans (hE v hv hv1)
    obtain ⟨m, hmM, hmS⟩ := exists_conj_le_of_isSylowTwoOf hTsyl hSM hS.2.1
    have hTv : IsSylowTwoOf (T ⊓ Subgroup.centralizer ({m * v * m⁻¹} : Set G))
        (Subgroup.centralizer ({m * v * m⁻¹} : Set G)) := by
      have hle : cjSub m S ≤ T ⊓ Subgroup.centralizer ({m * v * m⁻¹} : Set G) := by
        refine le_inf hmS ?_
        rintro _ ⟨s, hs, rfl⟩
        rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
        refine mem_centralizer_conj_iff.mpr ?_
        rw [show m⁻¹ * (m * s * m⁻¹) * m = s by group]
        exact hS.1 hs
      have hcardS : Nat.card (cjSub m S) = Nat.card S :=
        (Nat.card_congr (Subgroup.equivMapOfInjective S _ (MulAut.conj m).injective).toEquiv).symm
      have htp : twoPart (Subgroup.centralizer ({m * v * m⁻¹} : Set G)) =
          twoPart (Subgroup.centralizer ({v} : Set G)) := by
        unfold twoPart
        rw [card_centralizer_conj]
      have h2 : IsPGroup 2 ↥(T ⊓ Subgroup.centralizer ({m * v * m⁻¹} : Set G)) :=
        hH.sylow.1.to_le inf_le_left
      refine isSylowTwoOf_of_card_eq inf_le_right h2
        (le_antisymm (card_le_twoPart inf_le_right h2) ?_)
      calc twoPart (Subgroup.centralizer ({m * v * m⁻¹} : Set G)) =
            twoPart (Subgroup.centralizer ({v} : Set G)) := htp
        _ = Nat.card S := hS.card_eq.symm
        _ = Nat.card (cjSub m S) := hcardS.symm
        _ ≤ Nat.card ↥(T ⊓ Subgroup.centralizer ({m * v * m⁻¹} : Set G)) :=
          Subgroup.card_le_of_le hle
    obtain ⟨c, hc, hcN, hcg⟩ := exists_mul_mem_normalizer hTv (hTu m) (hmove m hmM).1
    exact h8 G T L V z (m * v * m⁻¹) (m * g * m⁻¹ * c) hH hE ⟨inferInstance, hE8⟩ hCVL hz1G hMV
      (hmV m hmM) (hmvz m hmM) (hback m hmM c hc) hcg hTv hcN
  ·
    exact hfin2 (hW ↥V (autOn L V) (autOn M V) (autOn T V) z hz1 hzH hWeyl hLMb hMN hSsyl
      ⟨v, hv⟩ hv1' hvz'')

end Lem16

open Lem16

theorem stmt12_2_16_of_F4 (h1222 : Stmt12_2_2_F4) (h331 : Stmt3_3_1_F4) (hL52 : OrbitL52Ten)
    (hL32 : OrbitL32Four) (hHat : OrbitHatA6Six) (hG2c : G2NaturalCover)
    (h6 : CoreSixTwoCentral) (hW : G2WeylTwoCentral) (h8 : Lem12216CoreEight_F4) :
    Stmt12_2_16_F4 := by
  intro G _ _ T L V hH hE g
  set M := Subgroup.normalizer (L : Set G) with hMdef
  obtain ⟨-, -, hall⟩ := ((h1222 G T hH.simple hH.nonabelian hH.qtke hH.sylow).resolve_left
    hH.notAlt) L hH.maximal hH.faithful hH.quasisimple
  obtain ⟨⟨-, -, hred, -⟩, hTIM, hMC, hab, hmod⟩ := hall V hH.irrPlus
  have hLV := le_normalizer_of_hyp1223 hH
  have hLM : L ≤ M := Subgroup.le_normalizer
  have hsq := sq_eq_one_of_hyp1223 hH hred
  by_contra hcon
  have hne : CFSG.conjugate V g ≠ V := fun h => hcon (Or.inl h)
  have hinf : V ⊓ CFSG.conjugate V g ≠ ⊥ := fun h => hcon (Or.inr h)
  have hgM : g ∉ M := fun hg => (hTIM g hg).elim hne hinf
  obtain ⟨⟨u, huV, hug⟩, hu1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hinf
  have hu1' : u ≠ 1 := fun h => hu1 (Subtype.ext h)
  have hvV : g * u * g⁻¹ ∈ V := Sec121.mem_conjugate_iff.mp hug
  have hv1 : g * u * g⁻¹ ≠ 1 := fun h => hu1' (by
    calc u = g⁻¹ * (g * u * g⁻¹) * g := by group
      _ = 1 := by rw [h]; group)
  have hgv : g⁻¹ * (g * u * g⁻¹) * g = u := by group

  have hnot : ∀ x ∈ M, x * u * x⁻¹ ≠ g * u * g⁻¹ := by
    intro x hx hxv
    apply hgM
    have hc : g⁻¹ * x ∈ Subgroup.centralizer ({u} : Set G) := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      calc g⁻¹ * x * u = g⁻¹ * (x * u * x⁻¹) * x := by group
        _ = g⁻¹ * (g * u * g⁻¹) * x := by rw [hxv]
        _ = u * (g⁻¹ * x) := by group
    have h1 := M.mul_mem (hE u huV hu1' hc) (M.inv_mem hx)
    rw [show g⁻¹ * x * x⁻¹ = g⁻¹ by group] at h1
    simpa using M.inv_mem h1

  have hCN : ∀ w ∈ V, w ≠ 1 → Subgroup.centralizer ({w} : Set G) ≤
      M ⊓ Subgroup.normalizer (V : Set G) := by
    intro w hw hw1 c hc
    have hcM := hE w hw hw1 hc
    refine Subgroup.mem_inf.mpr ⟨hcM, ?_⟩
    have hcw := Subgroup.mem_centralizer_singleton_iff.mp hc
    rcases hTIM c hcM with h | h
    · rw [Subgroup.mem_normalizer_iff]
      intro x
      conv_lhs => rw [← h]
      exact Sec121.mem_conjugate_iff
    · exfalso
      have hmem : w ∈ V ⊓ CFSG.conjugate V c := by
        refine ⟨hw, Sec121.mem_conjugate_iff.mpr ?_⟩
        rw [hcw, mul_inv_cancel_right]
        exact hw
      rw [h, Subgroup.mem_bot] at hmem
      exact hw1 hmem

  have hcard : Nat.card ↥(Subgroup.centralizer ({u} : Set G)) =
      Nat.card ↥(Subgroup.centralizer ({g * u * g⁻¹} : Set G)) :=
    (card_centralizer_conj g u).symm
  rcases orbitCase_of_modules hL52 hL32 hHat hG2c hH hred hmod with
    hsep | ⟨z, hz1, hzfix, hmodE⟩
  ·
    set N := M ⊓ Subgroup.normalizer (V : Set G) with hNdef
    have hNV : N ≤ Subgroup.normalizer (V : Set G) := inf_le_right
    have hsepN : OrbitsSeparated (autOn N V) :=
      orbitsSeparated_of_le_normalizer (A4.autOn_mono (le_inf hLM hLV))
        (autOn_le_normalizer_of_le hLV hNV inf_le_left) hsep
    have hcN : Nat.card ↥(N ⊓ Subgroup.centralizer ({u} : Set G)) =
        Nat.card ↥(N ⊓ Subgroup.centralizer ({g * u * g⁻¹} : Set G)) := by
      rw [inf_eq_right.mpr (hCN u huV hu1'), inf_eq_right.mpr (hCN _ hvV hv1)]
      exact hcard
    obtain ⟨n, hn, hnuv⟩ := exists_conj_of_card_centralizer_eq hNV hsepN
      (a := ⟨u, huV⟩) (b := ⟨g * u * g⁻¹, hvV⟩) (fun h => hu1' (congrArg Subtype.val h))
      (fun h => hv1 (congrArg Subtype.val h)) hcN
    exact hnot n hn.1 hnuv
  ·
    have hzH : z ∈ fixV (autOn L V) := hzfix ▸ Subgroup.mem_zpowers z
    have hzC : (z : G) ∈ V ⊓ Subgroup.centralizer (L : Set G) := by
      refine ⟨z.2, ?_⟩
      have h1 := hzH
      rw [fixV_autOn_eq hLV] at h1
      exact h1
    have hMV : M ≤ Subgroup.normalizer (V : Set G) := by
      rcases hMC with h | h
      · exact h
      · exfalso
        rw [h, Subgroup.mem_bot] at hzC
        exact hz1 (Subtype.ext hzC)
    have hz2 : z * z = 1 := by
      rw [← pow_two]
      exact hsq z

    have hzM : Subgroup.centralizer ({(z : G)} : Set G) = M := by
      refine le_antisymm (hE z z.2 (fun h => hz1 (Subtype.ext h))) ?_
      intro m hm
      rw [Subgroup.mem_centralizer_singleton_iff]
      have h1 : m * (z : G) * m⁻¹ ∈ V ⊓ Subgroup.centralizer (L : Set G) :=
        ⟨(Subgroup.mem_normalizer_iff.mp (hMV hm) _).mp hzC.1,
          (Subgroup.mem_normalizer_iff.mp (A4.mem_normalizer_centralizer hm) _).mp hzC.2⟩
      have hcvl : V ⊓ Subgroup.centralizer (L : Set G) = Subgroup.zpowers (z : G) := by
        have h2 := congrArg (Subgroup.map V.subtype) ((fixV_autOn_eq hLV).symm.trans hzfix)
        rw [Subgroup.subgroupOf_map_subtype, MonoidHom.map_zpowers] at h2
        rw [inf_comm]
        exact h2
      have hz2G : (z : G) * z = 1 := congrArg Subtype.val hz2
      rw [hcvl, mem_zpowers_of_mul_self_eq_one hz2G] at h1
      rcases h1 with h | h
      · exfalso
        apply hz1
        apply Subtype.ext
        calc (z : G) = m⁻¹ * (m * z * m⁻¹) * m := by group
          _ = 1 := by rw [h]; group
      · calc m * (z : G) = m * z * m⁻¹ * m := by group
          _ = z * m := by rw [h]
    have hnz : ∀ w : ↥V, (w : G) ∈ V → w ≠ 1 →
        Nat.card ↥(Subgroup.centralizer ({(w : G)} : Set G)) = Nat.card M → w = z := by
      intro w _ hw1 hw
      have hle : Subgroup.centralizer ({(w : G)} : Set G) ≤ M :=
        hE w w.2 (fun h => hw1 (Subtype.ext h))
      have heq : Subgroup.centralizer ({(w : G)} : Set G) = M :=
        Subgroup.eq_of_le_of_card_ge hle (le_of_eq hw.symm)

      have hwL : (w : G) ∈ Subgroup.centralizer (L : Set G) := by
        rw [Subgroup.mem_centralizer_iff]
        intro l hl
        have hl' : l ∈ Subgroup.centralizer ({(w : G)} : Set G) := by
          rw [heq]
          exact hLM hl
        exact Subgroup.mem_centralizer_singleton_iff.mp hl'
      have hwfix : w ∈ fixV (autOn L V) := by
        rw [fixV_autOn_eq hLV]
        exact hwL
      rw [hzfix, mem_zpowers_of_mul_self_eq_one hz2] at hwfix
      exact hwfix.resolve_left hw1
    have hgz : g * (z : G) * g⁻¹ = z → False := by
      intro h
      apply hgM
      rw [← hzM, Subgroup.mem_centralizer_singleton_iff]
      calc g * (z : G) = g * z * g⁻¹ * g := by group
        _ = z * g := by rw [h]
    set u' : ↥V := ⟨u, huV⟩ with hu'
    set v' : ↥V := ⟨g * u * g⁻¹, hvV⟩ with hv'
    have hu'1 : u' ≠ 1 := fun h => hu1' (congrArg Subtype.val h)
    have hv'1 : v' ≠ 1 := fun h => hv1 (congrArg Subtype.val h)
    have hcM : Nat.card ↥(Subgroup.centralizer ({(z : G)} : Set G)) = Nat.card M := by rw [hzM]
    have hu'z : u' ≠ z := by
      intro h
      have hu : u = (z : G) := congrArg Subtype.val h
      have hvz := hnz v' hvV hv'1 (hcard.symm.trans (by rw [hu]; exact hcM))
      apply hgz
      have hv : g * u * g⁻¹ = (z : G) := congrArg Subtype.val hvz
      rwa [hu] at hv
    have hv'z : v' ≠ z := by
      intro h
      have hv : g * u * g⁻¹ = (z : G) := congrArg Subtype.val h
      have huz := hnz u' huV hu'1 (hcard.trans (by rw [hv]; exact hcM))
      apply hgz
      have hu : u = (z : G) := congrArg Subtype.val huz
      rwa [hu] at hv

    have hzHM : z ∈ fixV (autOn M V) := by
      intro x hx
      obtain ⟨m, rfl⟩ := (A4.mem_autOn_iff hMV).mp hx
      apply Subtype.ext
      rw [A4.actionOn_apply_coe]
      have hm' : (m : G) ∈ Subgroup.centralizer ({(z : G)} : Set G) := by
        rw [hzM]
        exact m.2
      have hmz := Subgroup.mem_centralizer_singleton_iff.mp hm'
      rw [hmz]
      group
    have hLMb : autOn L V ≤ autOn M V := A4.autOn_mono hLM
    have hMN : autOn M V ≤ Subgroup.normalizer (autOn L V : Set (MulAut ↥V)) :=
      autOn_le_normalizer_autOn hLV hMV le_rfl
    obtain ⟨ℓ, hℓ, hlen, hsepm⟩ : ∃ ℓ : List ℕ, (∀ x ∈ ℓ, ∀ y ∈ ℓ, x ≠ 2 * y) ∧
        OrbitLengthsInMod (autOn L V) z ℓ ∧ OrbitsSeparatedMod (autOn L V) z := by
      rcases hmodE with hE6 | hE8 | hWeyl
      · exact ⟨[15], by decide, orbitAltCoreSix ↥V (autOn L V) z hz1 hzH hE6⟩
      · exact ⟨[28, 70], by decide, orbitAltCoreEight ↥V (autOn L V) z hz1 hzH hE8⟩
      · exact ⟨[63], by decide, orbitG2Weyl ↥V (autOn L V) z hz1 hzH hWeyl⟩
    have hcardM : Nat.card (orbitIn (autOn M V) u') = Nat.card (orbitIn (autOn M V) v') := by
      have h1 := card_orbitIn_mul_card_centralizer hMV u'
      have h2 := card_orbitIn_mul_card_centralizer hMV v'
      rw [inf_eq_right.mpr (hE u huV hu1')] at h1
      rw [inf_eq_right.mpr (hE _ hvV hv1)] at h2
      have hpos : 0 < Nat.card ↥(Subgroup.centralizer ({g * u * g⁻¹} : Set G)) := Nat.card_pos
      change Nat.card (orbitIn (autOn M V) u') *
        Nat.card ↥(Subgroup.centralizer ({u} : Set G)) = Nat.card M at h1
      change Nat.card (orbitIn (autOn M V) v') *
        Nat.card ↥(Subgroup.centralizer ({g * u * g⁻¹} : Set G)) = Nat.card M at h2
      rw [hcard] at h1
      exact Nat.eq_of_mul_eq_mul_right hpos (h1.trans h2.symm)
    have hKuv : Nat.card (orbitIn (autOn L V) v') = Nat.card (orbitIn (autOn L V) u') :=
      (eq_of_card_cases hℓ (hlen u' hu'1 hu'z) (hlen v' hv'1 hv'z)
        (card_orbitIn_eq_or hLMb hMN hzHM hz2 hsepm hu'1 hu'z)
        (card_orbitIn_eq_or hLMb hMN hzHM hz2 hsepm hv'1 hv'z) hcardM).symm
    obtain ⟨k, hk, hkv | hkv⟩ := hsepm v' u' hv'1 hu'1 hv'z hu'z hKuv
    ·
      obtain ⟨l, rfl⟩ := (A4.mem_autOn_iff hLV).mp hk
      have h1 := congrArg Subtype.val hkv
      rw [A4.actionOn_apply_coe] at h1
      change (l : G) * (g * u * g⁻¹) * (l : G)⁻¹ = u at h1
      apply hnot (l : G)⁻¹ (M.inv_mem (hLM l.2))
      calc (l : G)⁻¹ * u * (l : G)⁻¹⁻¹ = (l : G)⁻¹ * ((l : G) * (g * u * g⁻¹) * (l : G)⁻¹) * l := by
            rw [h1, inv_inv]
        _ = g * u * g⁻¹ := by group
    ·
      obtain ⟨l, rfl⟩ := (A4.mem_autOn_iff hLV).mp hk
      have h1 := congrArg Subtype.val hkv
      rw [A4.actionOn_apply_coe] at h1
      change (l : G) * (g * u * g⁻¹) * (l : G)⁻¹ = u * z at h1
      have hz2G : (z : G) * z = 1 := congrArg Subtype.val hz2
      have hv₁ : (l : G) * (g * u * g⁻¹) * (l : G)⁻¹ ∈ V :=
        (Subgroup.mem_normalizer_iff.mp (hLV l.2) _).mp hvV
      refine false_of_twisted_F4 h331 h6 hW h8 hH hE hsq hz1 hzfix hmodE hMV hv₁ ?_
        (fun h => hgM (by
          have := M.mul_mem (M.inv_mem (hLM l.2)) h
          rwa [inv_mul_cancel_left] at this)) ?_
      ·
        rw [h1, mem_zpowers_of_mul_self_eq_one hz2G]
        rintro (h | h)
        · apply hu'z
          apply Subtype.ext
          change u = z
          calc u = u * z * z := by rw [mul_assoc, hz2G, mul_one]
            _ = z := by rw [h, one_mul]
        · apply hu1'
          calc u = u * (z : G) * (z : G)⁻¹ := by group
            _ = 1 := by rw [h, mul_inv_cancel]
      ·
        rw [h1]
        calc ((l : G) * g)⁻¹ * (u * z) * ((l : G) * g) =
              g⁻¹ * ((l : G)⁻¹ * (u * z) * l) * g := by group
          _ = g⁻¹ * ((l : G)⁻¹ * ((l : G) * (g * u * g⁻¹) * (l : G)⁻¹) * l) * g := by rw [h1]
          _ = u := by group
          _ = u * z * z := by rw [mul_assoc, hz2G, mul_one]

end CFSG.Quasithin.H13
