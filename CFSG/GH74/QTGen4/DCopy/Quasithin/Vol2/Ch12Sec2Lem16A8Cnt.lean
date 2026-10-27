module

public import CFSG.Quasithin.Vol2.Ch12Sec2Lem16A8Cnt
public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch12Sec2Lem16A8Zv
public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch12Sec2Wired

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique
open scoped IsMulCommutative

open Orbit

open Lem16A8 in

theorem lem12216CoreEight_of_zv_F4 (h1222 : Stmt12_2_2_F4) (h323 : Stmt3_2_3)
    (hzv : Lem12216A8Zv_F4) : Lem12216CoreEight_F4 := by
  intro G _ _ T L V z v g hyp hNE hmod hVL hz1 hNV hvV hvz hgM hgv hsyl hgN
  classical
  have hres := hzv G T L V z v g hyp hNE hmod hVL hz1 hNV hvV hvz hgM hgv hsyl hgN
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

  obtain ⟨-, -, hall⟩ := ((h1222 G T hyp.simple hyp.nonabelian hyp.qtke hyp.sylow).resolve_left
    hyp.notAlt) L hyp.maximal hyp.faithful hyp.quasisimple
  obtain ⟨⟨hVT, -, hred, -⟩, -, -, -, -⟩ := hall V hyp.irrPlus
  have hV2' := sq_eq_one_of_hyp1223 hyp hred
  have hV2 : ∀ x ∈ V, x ^ 2 = 1 := fun x hx => by
    simpa using congrArg Subtype.val (hV2' ⟨x, hx⟩)
  have hinv2 : ∀ {y : G}, y ^ 2 = 1 → y⁻¹ = y := fun hy =>
    inv_eq_of_mul_eq_one_right (by rw [← pow_two, hy])
  have hVc : ∀ x ∈ V, ∀ y ∈ V, x * y = y * x := by
    intro x hx y hy
    calc x * y = (x * y)⁻¹ := (hinv2 (hV2 _ (V.mul_mem hx hy))).symm
      _ = y⁻¹ * x⁻¹ := mul_inv_rev x y
      _ = y * x := by rw [hinv2 (hV2 y hy), hinv2 (hV2 x hx)]
  have hT2 : IsPGroup 2 ↥T :=
    (CFSG.Quasithin.exists_sylow_of_quasithinIsSylowTwo hyp.sylow).elim
      fun S hS => hS ▸ S.isPGroup'

  have hzVL : z ∈ V ⊓ Subgroup.centralizer (L : Set G) := by
    rw [hVL]
    exact Subgroup.mem_zpowers z
  have hzV : z ∈ V := hzVL.1
  have hz2 : z ^ 2 = 1 := hV2 z hzV
  have hzp : ∀ x ∈ Subgroup.zpowers z, x = 1 ∨ x = z := by
    intro x hx
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
    have hoz : orderOf z = 2 := orderOf_eq_prime hz2 hz1
    rw [← zpow_mod_orderOf, hoz, Nat.cast_ofNat]
    rcases Int.emod_two_eq_zero_or_one k with hk | hk
    · rw [hk, zpow_zero]
      exact Or.inl rfl
    · rw [hk, zpow_one]
      exact Or.inr rfl
  have hMz : ∀ m ∈ Subgroup.normalizer (L : Set G), m * z * m⁻¹ = z := by
    intro m hm
    have h1 : m * z * m⁻¹ ∈ V ⊓ Subgroup.centralizer (L : Set G) := by
      refine Subgroup.mem_inf.mpr ⟨(Subgroup.mem_normalizer_iff.mp (hNV hm) z).mp hzV, ?_⟩
      rw [Subgroup.mem_centralizer_iff]
      intro l hl
      have hl' : m⁻¹ * l * m ∈ L := by
        have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hm) l).mp hl
        simpa using this
      have hc := (Subgroup.mem_centralizer_iff.mp hzVL.2) _ hl'
      calc l * (m * z * m⁻¹) = m * ((m⁻¹ * l * m) * z) * m⁻¹ := by group
        _ = m * (z * (m⁻¹ * l * m)) * m⁻¹ := by rw [hc]
        _ = m * z * m⁻¹ * l := by group
    rw [hVL] at h1
    rcases hzp _ h1 with h | h
    · exfalso
      apply hz1
      calc z = m⁻¹ * (m * z * m⁻¹) * m := by group
        _ = 1 := by rw [h]; group
    · exact h

  obtain ⟨⟨hMmax, -⟩, ⟨-, huniq⟩, -⟩ :=
    h323 G T L hyp.simple hyp.nonabelian hyp.qtke hyp.sylow hyp.maximal hyp.faithful
      hyp.quasisimple
  rw [hyp.conjClosure_eq] at hMmax huniq
  have hv1 : v ≠ 1 := fun h => hvz (h ▸ Subgroup.one_mem _)

  have hnot : ∀ m ∈ Subgroup.normalizer (L : Set G), m * v * m⁻¹ ≠ v * z := by
    intro m hm h
    apply hgM
    have hgm : g * m ∈ Subgroup.centralizer ({v} : Set G) := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      calc g * m * v = g * (m * v * m⁻¹) * m := by group
        _ = g * (v * z) * m := by rw [h]
        _ = g * (g⁻¹ * v * g) * m := by rw [hgv]
        _ = v * (g * m) := by group
    have e : g = (g * m) * m⁻¹ := by group
    rw [e]
    exact Subgroup.mul_mem _ (hNE v hvV hv1 hgm) (Subgroup.inv_mem _ hm)

  obtain ⟨hcomm, hR⟩ := hmod
  have hLV : L ≤ Subgroup.normalizer (V : Set G) := hyp.irrPlus.2.2.1
  have hTV : T ≤ Subgroup.normalizer (V : Set G) := hyp.normalizes.trans hNV
  set z' : ↥V := ⟨z, hzV⟩ with hz'
  have hz'1 : z' ≠ 1 := fun h => hz1 (congrArg Subtype.val h)
  have hz'fix : z' ∈ fixV (autOn L V) := by
    intro h hh
    obtain ⟨l, rfl⟩ := (A4.mem_autOn_iff hLV).mp hh
    apply Subtype.ext
    rw [A4.actionOn_apply_coe]
    have hc := (Subgroup.mem_centralizer_iff.mp hzVL.2) _ l.2
    show (l : G) * z * (l : G)⁻¹ = z
    rw [hc, mul_inv_cancel_right]
  obtain ⟨-, hsep⟩ := orbitAltCoreEight ↥V (autOn L V) z' hz'1 hz'fix hR
  have hTC : ∀ t ∈ T, ∃ l ∈ L, t * l ∈ Subgroup.centralizer ({v} : Set G) := by
    intro t ht
    have htN : t ∈ Subgroup.normalizer (L : Set G) := hyp.normalizes ht
    set a : ↥V := ⟨v, hvV⟩ with ha
    set h₀ : MulAut ↥V := A4.actionOn V T hTV ⟨t⁻¹, T.inv_mem ht⟩ with hh₀
    have hh₀A : h₀ ∈ autOn T V := (A4.mem_autOn_iff hTV).mpr ⟨_, rfl⟩
    have hh₀N := Lem16.autOn_le_normalizer_of_le hLV hTV hyp.normalizes hh₀A
    have hcard := Lem16.card_orbitIn_apply hh₀N a
    have hw : ((h₀ a : ↥V) : G) = t⁻¹ * v * t := by
      rw [hh₀, A4.actionOn_apply_coe, inv_inv]
    have ha1 : a ≠ 1 := fun h => hv1 (congrArg Subtype.val h)
    have haz : a ≠ z' := by
      intro h
      apply hvz
      have h1 : v = z := congrArg Subtype.val h
      rw [h1]
      exact Subgroup.mem_zpowers z
    have hw1 : h₀ a ≠ 1 := fun h => ha1 (h₀.injective (h.trans (map_one h₀).symm))
    have hwz : h₀ a ≠ z' := by
      intro h
      apply haz
      apply Subtype.ext
      have h1 := congrArg Subtype.val h
      rw [hw] at h1
      show v = z
      calc v = t * (t⁻¹ * v * t) * t⁻¹ := by group
        _ = t * z * t⁻¹ := by rw [h1]
        _ = z := hMz t htN
    obtain ⟨h, hh, hcase⟩ := hsep a (h₀ a) ha1 hw1 haz hwz hcard.symm
    obtain ⟨l, rfl⟩ := (A4.mem_autOn_iff hLV).mp hh
    have hl : (l : G) ∈ L := l.2
    rcases hcase with h1 | h1
    · refine ⟨l, hl, ?_⟩
      have h2 := congrArg Subtype.val h1
      rw [A4.actionOn_apply_coe, hw] at h2
      rw [Subgroup.mem_centralizer_singleton_iff]
      calc t * l * v = t * ((l : G) * v * (l : G)⁻¹) * l := by group
        _ = t * (t⁻¹ * v * t) * l := by rw [h2]
        _ = v * (t * l) := by group
    · exfalso
      have h2 := congrArg Subtype.val h1
      rw [Subgroup.coe_mul, A4.actionOn_apply_coe, hw] at h2
      apply hnot (t * l) (Subgroup.mul_mem _ htN (Subgroup.le_normalizer hl))
      calc t * l * v * (t * l)⁻¹ = t * ((l : G) * v * (l : G)⁻¹) * t⁻¹ := by group
        _ = t * (t⁻¹ * v * t * z) * t⁻¹ := by rw [h2]
        _ = v * (t * z * t⁻¹) := by group
        _ = v * z := by rw [hMz t htN]
  set Tv := T ⊓ Subgroup.centralizer ({v} : Set G) with hTvdef
  have hTLv : T ≤ L ⊔ Tv := le_sup_of_sylow hT2 hyp.normalizes hsyl inf_le_left hTC

  set Zv := zv Tv with hZvdef
  set C := V ⊓ Zv with hCdef
  set ZL := Zv ⊓ Subgroup.centralizer (L : Set G) with hZLdef
  set ZLg := ZL.map (MulAut.conj g⁻¹).toMonoidHom with hZLgdef
  have hvTv : ∀ x ∈ V, x ∈ Tv := fun x hx =>
    ⟨hVT hx, Subgroup.mem_centralizer_singleton_iff.mpr (hVc x hx v hvV)⟩
  have hzZv : z ∈ Zv := by
    refine ⟨hvTv z hzV, Subgroup.mem_centralizer_iff.mpr fun t ht => ?_, hz2⟩
    have := hMz t (hyp.normalizes ht.1)
    calc t * z = (t * z * t⁻¹) * t := by group
      _ = z * t := by rw [this]
  have hzC : z ∈ C := ⟨hzV, hzZv⟩
  have hzZL : z ∈ ZL := ⟨hzZv, hzVL.2⟩
  have hgi : g⁻¹ ∈ Subgroup.normalizer (Tv : Set G) := Subgroup.inv_mem _ hgN
  have hconj : ∀ y : G, (MulAut.conj g⁻¹).toMonoidHom y = g⁻¹ * y * g := fun y => by
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
  have hZLgZv : ZLg ≤ Zv := by
    rintro _ ⟨b, ⟨⟨hbT, hbc, hb2⟩, -⟩, rfl⟩
    rw [hconj]
    refine ⟨?_, Subgroup.mem_centralizer_iff.mpr fun t ht => ?_, ?_⟩
    · have := (Subgroup.mem_normalizer_iff.mp hgi b).mp hbT
      simpa using this
    · have ht' : g * t * g⁻¹ ∈ Tv := (Subgroup.mem_normalizer_iff.mp hgN t).mp ht
      have hc := (Subgroup.mem_centralizer_iff.mp hbc) _ ht'
      calc t * (g⁻¹ * b * g) = g⁻¹ * ((g * t * g⁻¹) * b) * g := by group
        _ = g⁻¹ * (b * (g * t * g⁻¹)) * g := by rw [hc]
        _ = g⁻¹ * b * g * t := by group
    · calc (g⁻¹ * b * g) ^ 2 = g⁻¹ * b ^ 2 * g := by rw [pow_two, pow_two]; group
        _ = 1 := by rw [hb2]; group

  have hCZ : C ⊓ ZLg = ⊥ := by
    rw [eq_bot_iff]
    rintro x ⟨⟨hxV, -⟩, ⟨b, ⟨⟨hbT, hbc, -⟩, hbL⟩, rfl⟩⟩
    rw [Subgroup.mem_bot]
    by_contra hx1
    rw [hconj] at hxV hx1
    apply hgM

    have hLTb : L ⊔ T ≤ Subgroup.centralizer ({b} : Set G) := by
      refine sup_le (fun l hl => ?_) (hTLv.trans (sup_le (fun l hl => ?_) fun t ht => ?_))
      · exact Subgroup.mem_centralizer_singleton_iff.mpr
          (Subgroup.mem_centralizer_iff.mp hbL l hl)
      · exact Subgroup.mem_centralizer_singleton_iff.mpr
          (Subgroup.mem_centralizer_iff.mp hbL l hl)
      · exact Subgroup.mem_centralizer_singleton_iff.mpr
          (Subgroup.mem_centralizer_iff.mp hbc t ht)

    have hCx := hNE _ hxV hx1
    set M' := (Subgroup.normalizer (L : Set G)).map (MulAut.conj g).toMonoidHom with hM'
    have hLTM' : L ⊔ T ≤ M' := by
      intro y hy
      have hyb := Subgroup.mem_centralizer_singleton_iff.mp (hLTb hy)
      have h1 : g⁻¹ * y * g ∈ Subgroup.centralizer ({g⁻¹ * b * g} : Set G) := by
        rw [Subgroup.mem_centralizer_singleton_iff]
        calc g⁻¹ * y * g * (g⁻¹ * b * g) = g⁻¹ * (y * b) * g := by group
          _ = g⁻¹ * (b * y) * g := by rw [hyb]
          _ = g⁻¹ * b * g * (g⁻¹ * y * g) := by group
      refine ⟨g⁻¹ * y * g, hCx h1, ?_⟩
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      group
    have heq := huniq M' (quasithinIsMaxTwoLocal_conj hMmax g) hLTM'
    exact mem_of_map_conj_eq hMmax heq

  have hZvsub : ∀ x ∈ Zv, ∃ c ∈ C, ∃ b ∈ ZL, x = c * b := by
    rintro x ⟨hxT, hxc, hx2⟩
    obtain ⟨a, haV, hac, b, hbT, hbc, hbL, rfl⟩ := hres x hxT hxc hx2
    have ha2 : a ^ 2 = 1 := hV2 a haV
    have haZ : a ∈ Zv := ⟨hvTv a haV, hac, ha2⟩
    refine ⟨a, ⟨haV, haZ⟩, b, ⟨⟨hbT, hbc, ?_⟩, hbL⟩, rfl⟩
    have hab : b * a = a * b := Subgroup.mem_centralizer_iff.mp hac b hbT
    have h1 : a * b * (a * b) = 1 := by rw [← pow_two]; exact hx2
    have h2 : a * a * (b * b) = 1 := by
      calc a * a * (b * b) = a * (a * b) * b := by group
        _ = a * (b * a) * b := by rw [hab]
        _ = a * b * (a * b) := by group
        _ = 1 := h1
    have h3 : a * a = 1 := by rw [← pow_two]; exact ha2
    rw [h3, one_mul] at h2
    rw [pow_two]
    exact h2

  have hμ₁ : Function.Injective (fun p : ↥C × ↥ZLg =>
      (⟨(p.1 : G) * p.2, Zv.mul_mem p.1.2.2 (hZLgZv p.2.2)⟩ : ↥Zv)) := by
    rintro ⟨c, d⟩ ⟨c', d'⟩ h
    have h1 : (c : G) * d = c' * d' := congrArg Subtype.val h
    have h2 : (c' : G)⁻¹ * c = d' * (d : G)⁻¹ := by
      calc (c' : G)⁻¹ * c = (c' : G)⁻¹ * (c * d) * (d : G)⁻¹ := by group
        _ = (c' : G)⁻¹ * (c' * d') * (d : G)⁻¹ := by rw [h1]
        _ = d' * (d : G)⁻¹ := by group
    have h3 : (c' : G)⁻¹ * c ∈ C ⊓ ZLg :=
      ⟨C.mul_mem (C.inv_mem c'.2) c.2, h2 ▸ ZLg.mul_mem d'.2 (ZLg.inv_mem d.2)⟩
    rw [hCZ, Subgroup.mem_bot] at h3
    have hc : c = c' := Subtype.ext (by
      calc (c : G) = c' * ((c' : G)⁻¹ * c) := by group
        _ = c' := by rw [h3, mul_one])
    have hd : d = d' := Subtype.ext (by
      rw [hc] at h1
      exact mul_left_cancel h1)
    rw [hc, hd]
  set μ₂ : ↥C × ↥ZL → ↥Zv := fun p => ⟨(p.1 : G) * p.2, Zv.mul_mem p.1.2.2 p.2.2.1⟩ with hμ₂
  have hμ₂s : Function.Surjective μ₂ := by
    rintro ⟨x, hx⟩
    obtain ⟨c, hc, b, hb, rfl⟩ := hZvsub x hx
    exact ⟨⟨⟨c, hc⟩, ⟨b, hb⟩⟩, rfl⟩
  have hμ₂i : ¬ Function.Injective μ₂ := by
    intro h
    have h1 : μ₂ (⟨z, hzC⟩, ⟨z, hzZL⟩) = μ₂ (1, 1) := by
      apply Subtype.ext
      show z * z = 1 * 1
      rw [← pow_two, hz2, one_mul]
    have h2 := congrArg (fun p : ↥C × ↥ZL => (p.1 : G)) (h h1)
    exact hz1 h2
  have hcardg : Nat.card ↥ZLg = Nat.card ↥ZL :=
    Subgroup.card_map_of_injective (MulAut.conj g⁻¹).injective
  have hle := Nat.card_le_card_of_injective _ hμ₁
  have hlt : Nat.card ↥Zv < Nat.card (↥C × ↥ZL) := by
    have := Fintype.ofFinite ↥Zv
    have := Fintype.ofFinite (↥C × ↥ZL)
    rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
    exact Fintype.card_lt_of_surjective_not_injective μ₂ hμ₂s hμ₂i
  rw [Nat.card_prod, hcardg] at hle
  rw [Nat.card_prod] at hlt
  omega

theorem stmt12_2_16_of_orbitsA8Zv_F4
    (h1222 : Stmt12_2_2_F4)
    (h331 : Stmt3_3_1_F4) (h323 : Stmt3_2_3) (h6 : CoreSixTwoCentral) (hW : G2WeylTwoCentral)
    (hzv : Lem12216A8Zv_F4) : Stmt12_2_16_F4 :=
  stmt12_2_16_of_orbits_F4 h1222 h331 h6 hW (lem12216CoreEight_of_zv_F4 h1222 h323 hzv)

end CFSG.Quasithin.H13
