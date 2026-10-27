module

public import CFSG.LargeExtraspecial.AS35DFourSeven

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial

open Subgroup Asc77 CFSG.DisconnectedInvolutionGraph.Helpers

namespace Setting

variable {G : Type} [Group G] [Finite G] (S : Setting G)

theorem eq_bot_of_normal_odd_gen {X : Set G} (hX2 : ∀ x ∈ X, x * x = 1)
    (hXzmul : ∀ x ∈ X, x * S.z ∈ X) (hXne : X.Nonempty) (hO : ∀ x ∈ X, S.ZInOTwo x)
    {N : Subgroup G} (hNn : N.Normal) (hN : Odd (Nat.card N)) : N = ⊥ := by
  obtain ⟨t, ht⟩ := hXne
  exact S.eq_bot_of_odd S.QG.one_mem (fun x _ => mem_centralizer_singleton_iff.mpr (by group))
    (fun c _ k hk => hNn.conj_mem k hk c) hN (by group) (hX2 t ht) (hO t ht)
    (hO _ (hXzmul t ht))

theorem z_mem_of_normal_gen {X : Set G} (hX2 : ∀ x ∈ X, x * x = 1)
    (hXzmul : ∀ x ∈ X, x * S.z ∈ X) (hXne : X.Nonempty) (hO : ∀ x ∈ X, S.ZInOTwo x)
    {N : Subgroup G} (hNn : N.Normal) (hN : N ≠ ⊥) : S.z ∈ N := by
  have hNM : N ⊓ S.M ≠ ⊥ := by
    intro h0
    have hfix : ∀ k ∈ N, k * S.z = S.z * k → k = 1 := fun k hk hkz => by
      have : k ∈ N ⊓ S.M := mem_inf.mpr ⟨hk, S.mem_M_iff.mpr hkz⟩
      rwa [h0, mem_bot] at this
    have hodd : Odd (Nat.card N) := by
      by_contra hev
      rw [Nat.not_odd_iff_even] at hev
      obtain ⟨k, hk⟩ := exists_prime_orderOf_dvd_card' (G := N) 2 (even_iff_two_dvd.mp hev)
      have hk' : orderOf (k : G) = 2 := by rw [Subgroup.orderOf_coe]; exact hk
      have hk2 : (k : G) * k = 1 := by rw [← pow_two, ← hk', pow_orderOf_eq_one]
      have hk1 : (k : G) ≠ 1 := by
        intro h
        rw [h, orderOf_one] at hk'
        exact absurd hk' (by norm_num)
      apply hk1
      apply hfix k k.2
      have hinv := conj_eq_inv_of_fixedPointFree (fun k hk => hNn.conj_mem k hk S.z) S.z_mul_z
        hfix k.2
      have hki : (k : G)⁻¹ = k := inv_eq_of_mul_eq_one_right hk2
      rw [hki] at hinv
      calc (k : G) * S.z = S.z * k * S.z⁻¹ * S.z := by rw [hinv]
        _ = S.z * k := by group
    exact hN (S.eq_bot_of_normal_odd_gen hX2 hXzmul hXne hO hNn hodd)
  have h := S.z_mem_of_le_M inf_le_right (fun q hq n hn' => mem_inf.mpr
    ⟨hNn.conj_mem n (mem_inf.mp hn').1 q, S.M.mul_mem (S.M.mul_mem (S.QG_le_M hq)
      (mem_inf.mp hn').2) (S.M.inv_mem (S.QG_le_M hq))⟩) hNM
  exact (mem_inf.mp h).1

theorem centralizer_zGen_eq_bot_of_not_mem_gen {X : Set G} (hX2 : ∀ x ∈ X, x * x = 1)
    (hXzmul : ∀ x ∈ X, x * S.z ∈ X) (hXne : X.Nonempty) (hO : ∀ x ∈ X, S.ZInOTwo x)
    (h : S.z ∉ centralizer (S.zGen : Set G)) :
    centralizer (S.zGen : Set G) = ⊥ := by
  have : S.zGen.Normal := S.zGen_normal
  by_contra hne
  exact h (S.z_mem_of_normal_gen hX2 hXzmul hXne hO inferInstance hne)

theorem eq_bot_of_normal_two_gen {X : Set G} (hX2 : ∀ x ∈ X, x * x = 1)
    (hXzmul : ∀ x ∈ X, x * S.z ∈ X) (hXne : X.Nonempty) (hO : ∀ x ∈ X, S.ZInOTwo x)
    (hC : centralizer (S.zGen : Set G) = ⊥) {Y : Subgroup G} (hYn : Y.Normal)
    (hY : IsPGroup 2 Y) : Y = ⊥ := by
  by_contra hY1
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Nontrivial Y := (Subgroup.nontrivial_iff_ne_bot Y).mpr hY1
  set ZY := (center Y).map Y.subtype with hZY
  have hZYn : ZY.Normal := ⟨fun y hy g =>
    conj_mem_map_of_characteristic _ (normal_conj_mem hYn g).1 (normal_conj_mem hYn g).2 hy⟩
  have hZY1 : ZY ≠ ⊥ := by
    intro h
    obtain ⟨c, hc, hc1⟩ := (Subgroup.nontrivial_iff_exists_ne_one (center Y)).mp
      hY.center_nontrivial
    have : (c : G) ∈ ZY := ⟨c, hc, rfl⟩
    rw [h, mem_bot] at this
    exact hc1 (Subtype.ext this)
  have hz := S.z_mem_of_normal_gen hX2 hXzmul hXne hO hZYn hZY1
  have hLZ := S.zGen_le_of_normal hZYn hz
  have hzC : S.z ∈ centralizer (S.zGen : Set G) := by
    rw [mem_centralizer_iff]
    intro x hx
    obtain ⟨c, hc, rfl⟩ := hLZ hx
    obtain ⟨d, -, hd⟩ := hz
    rw [← hd]
    exact congrArg Subtype.val (mem_center_iff.mp hc d).symm
  rw [hC, mem_bot] at hzC
  exact S.z_ne_one hzC

theorem isSimpleGroup_zGen_gen {X : Set G} (hXQ : X ⊆ S.QG) (hX2 : ∀ x ∈ X, x * x = 1)
    (hXzmul : ∀ x ∈ X, x * S.z ∈ X) (hXne : X.Nonempty)
    (hgen : S.QG ≤ Subgroup.closure (X ∪ {S.z})) (hO : ∀ x ∈ X, S.ZInOTwo x)
    (hC : centralizer (S.zGen : Set G) = ⊥) : IsSimpleGroup S.zGen := by
  set L := S.zGen with hLdef
  have hLn : L.Normal := S.zGen_normal
  have hzL : S.z ∈ L := S.z_mem_zGen
  have hL1 : L ≠ ⊥ := fun h => S.z_ne_one (by rw [h] at hzL; exact mem_bot.mp hzL)
  obtain ⟨K, hK, k₀, hk₀K, hk₀⟩ :
      ∃ K, IsMinNormalIn L K ∧ ∃ k₀ ∈ K, k₀ * S.z ≠ S.z * k₀ := by
    obtain ⟨K₀, hK₀⟩ := exists_isMinNormalIn hL1
    by_contra! hall
    have hcen : normalClosure (K₀ : Set G) ≤ S.M := by
      rw [normalClosure, closure_le]
      intro y hy
      obtain ⟨a, ha, hay⟩ := Group.mem_conjugatesOfSet_iff.mp hy
      obtain ⟨g, rfl⟩ := isConj_iff.mp hay
      exact S.mem_M_iff.mpr (hall _ (hK₀.subConj hLn g) _ (conj_mem_subConj ha))
    have hne : normalClosure (K₀ : Set G) ≠ ⊥ := by
      intro h
      apply hK₀.2.2.1
      rw [eq_bot_iff]
      intro k hk
      rw [← h]
      exact subset_normalClosure hk
    have hz := S.z_mem_of_normal_gen hX2 hXzmul hXne hO normalClosure_normal hne
    have hLM : L ≤ S.M := (S.zGen_le_of_normal normalClosure_normal hz).trans hcen
    have hzC : S.z ∈ centralizer (L : Set G) :=
      mem_centralizer_iff.mpr fun x hx => S.mem_M_iff.mp (hLM hx)
    rw [hC, mem_bot] at hzC
    exact S.z_ne_one hzC
  have hzK : ∀ x ∈ K, S.z * x * S.z⁻¹ ∈ K := fun x hx => hK.2.1 S.z hzL x hx
  have hKeven : Even (Nat.card K) := by
    by_contra hodd
    rw [Nat.not_even_iff_odd] at hodd
    have hchar := oddCore_characteristic (G := L)
    set O := (oddCore L).map L.subtype with hOdef
    have hKO : K ≤ O := by
      intro k hk
      refine ⟨⟨k, hK.1 hk⟩, normal_odd_le_oddCore (K.subgroupOf L) ?_ ?_
        (by rw [mem_subgroupOf]; exact hk), rfl⟩
      · exact ⟨fun n hn l => by
          rw [mem_subgroupOf] at hn ⊢
          exact hK.2.1 l l.2 n hn⟩
      · rwa [Nat.card_congr (subgroupOfEquivOfLe hK.1).toEquiv]
    have hOn : O.Normal := ⟨fun y hy g =>
      conj_mem_map_of_characteristic (oddCore L) (hC := hchar) (normal_conj_mem hLn g).1
        (normal_conj_mem hLn g).2 hy⟩
    have hOodd : Odd (Nat.card O) := by
      rw [hOdef, card_map_of_injective L.subtype_injective]
      exact oddCore_odd
    have hO1 := S.eq_bot_of_normal_odd_gen hX2 hXzmul hXne hO hOn hOodd
    exact hK.2.2.1 (eq_bot_iff.mpr (hO1 ▸ hKO))
  have hK2 : ∀ P : Subgroup G, P ≤ K → (∀ k ∈ K, ∀ p ∈ P, k * p * k⁻¹ ∈ P) →
      IsPGroup 2 P → P = ⊥ := by
    intro P hPK hPn hP2
    set O2K := (CFSG.pCore 2 K).map K.subtype with hO2Kdef
    have hPO : P ≤ O2K := by
      intro p hp
      refine ⟨⟨p, hPK hp⟩, ?_, rfl⟩
      have hle : P.subgroupOf K ≤ CFSG.pCore 2 K :=
        le_sSup ⟨⟨fun n hn k => by
          rw [mem_subgroupOf] at hn ⊢
          exact hPn k k.2 n hn⟩, hP2.comap_of_injective K.subtype K.subtype_injective⟩
      exact hle (by rw [mem_subgroupOf]; exact hp)
    have hO2K : O2K = ⊥ := by
      by_contra hne
      have hO2Kn : ∀ l ∈ L, ∀ y ∈ O2K, l * y * l⁻¹ ∈ O2K := fun l hl y hy =>
        conj_mem_map_of_characteristic _ (hK.2.1 l hl)
          (fun n hn => by
            have := hK.2.1 l⁻¹ (L.inv_mem hl) n hn
            rwa [inv_inv] at this) hy
      have hEq : O2K = K := hK.2.2.2 O2K (map_subtype_le _) hO2Kn hne
      have hKp : IsPGroup 2 K := by
        rw [← hEq]
        exact CFSG.pCore_isPGroup.map K.subtype
      set O2L := (CFSG.pCore 2 L).map L.subtype with hO2Ldef
      have hKO2L : K ≤ O2L := by
        intro k hk
        refine ⟨⟨k, hK.1 hk⟩, ?_, rfl⟩
        have hle : K.subgroupOf L ≤ CFSG.pCore 2 L :=
          le_sSup ⟨⟨fun n hn l => by
            rw [mem_subgroupOf] at hn ⊢
            exact hK.2.1 l l.2 n hn⟩, hKp.comap_of_injective L.subtype L.subtype_injective⟩
        exact hle (by rw [mem_subgroupOf]; exact hk)
      have hO2Ln : O2L.Normal := ⟨fun y hy g =>
        conj_mem_map_of_characteristic _ (normal_conj_mem hLn g).1 (normal_conj_mem hLn g).2 hy⟩
      have hO2L1 := S.eq_bot_of_normal_two_gen hX2 hXzmul hXne hO hC hO2Ln
        (CFSG.pCore_isPGroup.map _)
      exact hK.2.2.1 (eq_bot_iff.mpr (hO2L1 ▸ hKO2L))
    exact eq_bot_iff.mpr (hO2K ▸ hPO)
  have hKt : ∀ t ∈ X, Asc77.subConj K t = K := by
    intro t htX
    have htQ : t ∈ S.QG := hXQ htX
    have ht2 : t * t = 1 := hX2 t htX
    by_contra hne
    have hKt' := hK.subConj hLn t
    have hcomm : ∀ a ∈ K, ∀ b ∈ Asc77.subConj K t, a * b = b * a := fun a ha b hb =>
      hK.commute hKt' (Ne.symm hne) ha hb
    have hinf := hK.inf_eq_bot hKt' (Ne.symm hne)
    have hmem : ∀ x ∈ K, t * x * t⁻¹ ∈ Asc77.subConj K t := fun x hx => conj_mem_subConj hx
    have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht2
    let φ : K →* G :=
      { toFun := fun x => x * (t * x * t⁻¹)
        map_one' := by
          change (1 : G) * (t * 1 * t⁻¹) = 1
          group
        map_mul' := fun x y => by
          change (x * y : G) * (t * (x * y) * t⁻¹) = x * (t * x * t⁻¹) * (y * (t * y * t⁻¹))
          have h := hcomm y y.2 (t * x * t⁻¹) (hmem x x.2)
          calc (x * y : G) * (t * (x * y) * t⁻¹) = x * (y * (t * x * t⁻¹)) * (t * y * t⁻¹) := by
                group
            _ = x * ((t * x * t⁻¹) * y) * (t * y * t⁻¹) := by rw [h]
            _ = x * (t * x * t⁻¹) * (y * (t * y * t⁻¹)) := by group }
    have hφ : ∀ x : K, φ x = x * (t * x * t⁻¹) := fun _ => rfl
    have hφinj : Function.Injective φ := by
      rw [injective_iff_map_eq_one]
      intro x hx
      rw [hφ] at hx
      have h1 : t * (x : G) * t⁻¹ = (x : G)⁻¹ := eq_inv_of_mul_eq_one_right hx
      have hxt : (x : G) ∈ Asc77.subConj K t := by
        have := Subgroup.inv_mem _ (hmem x x.2)
        rwa [h1, inv_inv] at this
      have : (x : G) ∈ K ⊓ Asc77.subConj K t := mem_inf.mpr ⟨x.2, hxt⟩
      rw [hinf, mem_bot] at this
      exact Subtype.ext this
    have hφt : ∀ x : K, φ x ∈ centralizer ({t} : Set G) := by
      intro x
      rw [mem_centralizer_singleton_iff, hφ]
      have h := hcomm x x.2 (t * x * t⁻¹) (hmem x x.2)
      rw [htinv] at h ⊢
      calc (x : G) * (t * x * t) * t = t * x * t * x * t := by rw [h]
        _ = t * (x * (t * x * t)) := by group
    have hzt : S.z * t = t * S.z := (S.z_comm_QG htQ).symm
    have hφz : ∀ x : K, S.z * φ x * S.z⁻¹ = φ ⟨S.z * x * S.z⁻¹, hzK x x.2⟩ := by
      intro x
      rw [hφ, hφ]
      change S.z * (x * (t * x * t⁻¹)) * S.z⁻¹ =
        S.z * x * S.z⁻¹ * (t * (S.z * x * S.z⁻¹) * t⁻¹)
      calc S.z * (x * (t * x * t⁻¹)) * S.z⁻¹
          = S.z * x * S.z⁻¹ * ((S.z * t) * x * (S.z * t)⁻¹) := by group
        _ = S.z * x * S.z⁻¹ * ((t * S.z) * x * (t * S.z)⁻¹) := by rw [hzt]
        _ = S.z * x * S.z⁻¹ * (t * (S.z * x * S.z⁻¹) * t⁻¹) := by group
    set P : Subgroup G := ((oTwoCent t).comap φ).map K.subtype with hPdef
    have hP : P = ⊥ := by
      refine hK2 P (map_subtype_le _) ?_ ?_
      · rintro k hk _ ⟨p, hp, rfl⟩
        refine ⟨⟨k, hk⟩ * p * ⟨k, hk⟩⁻¹, ?_, rfl⟩
        rw [SetLike.mem_coe, mem_comap] at hp ⊢
        rw [map_mul, map_mul, map_inv]
        exact conj_mem_oTwoCent (hφt _) hp
      · exact ((isPGroup_oTwoCent t).comap_of_injective φ hφinj).map K.subtype
    have hz2 : S.z ∈ oTwoCent t := hO t htX
    apply hk₀
    set k' : K := ⟨k₀, hk₀K⟩
    set c₂ : K := ⟨S.z * k₀⁻¹ * S.z⁻¹, hzK _ (K.inv_mem hk₀K)⟩
    have hc₂ : φ c₂ = S.z * (φ k')⁻¹ * S.z⁻¹ := by
      have := hφz k'⁻¹
      rw [map_inv] at this
      rw [this]
      rfl
    have hc : φ (k' * c₂) = φ k' * S.z * (φ k')⁻¹ * S.z⁻¹ := by
      rw [map_mul, hc₂]
      group
    have hcO : φ (k' * c₂) ∈ oTwoCent t := by
      rw [hc]
      exact mul_mem (conj_mem_oTwoCent (hφt k') hz2) (inv_mem hz2)
    have hcP : ((k' * c₂ : K) : G) ∈ P := ⟨k' * c₂, hcO, rfl⟩
    rw [hP, mem_bot] at hcP
    change k₀ * (S.z * k₀⁻¹ * S.z⁻¹) = 1 at hcP
    calc k₀ * S.z = k₀ * (S.z * k₀⁻¹ * S.z⁻¹) * (S.z * k₀) := by group
      _ = S.z * k₀ := by rw [hcP, one_mul]
  have hzK' : ∀ x ∈ K, S.z⁻¹ * x * S.z ∈ K := fun x hx => by
    rw [S.z_inv]
    have := hzK x hx
    rwa [S.z_inv] at this
  have hQK : ∀ q ∈ S.QG, ∀ k ∈ K, q * k * q⁻¹ ∈ K := by
    have hnormX : ∀ x ∈ X, x ∈ normalizer (K : Set G) := by
      intro x hx
      have h := hKt x hx
      rw [mem_normalizer_iff]
      intro k
      refine ⟨fun hk => ?_, fun hk => ?_⟩
      · rw [← h]
        exact conj_mem_subConj hk
      · rw [← h, mem_subConj] at hk
        rwa [show x⁻¹ * (x * k * x⁻¹) * x = k by group] at hk
    have hnormz : S.z ∈ normalizer (K : Set G) := by
      rw [mem_normalizer_iff]
      intro k
      refine ⟨fun hk => hzK k hk, fun hk => ?_⟩
      have := hzK' _ hk
      rwa [show S.z⁻¹ * (S.z * k * S.z⁻¹) * S.z = k by group] at this
    have hle : S.QG ≤ normalizer (K : Set G) := by
      refine hgen.trans ?_
      rw [closure_le]
      rintro u (hu | hu)
      · exact hnormX u hu
      · rw [Set.mem_singleton_iff.mp hu]
        exact hnormz
    intro q hq k hk
    exact (mem_normalizer_iff.mp (hle hq) k).mp hk
  have hzKK : S.z ∈ K := S.z_mem_of_normalized hQK hKeven
  have hMK : ∀ m ∈ S.M, Asc77.subConj K m = K := by
    intro m hm
    by_contra hne
    have hinf := (hK.subConj hLn m).inf_eq_bot hK hne
    have hz1 : S.z ∈ Asc77.subConj K m ⊓ K := by
      refine mem_inf.mpr ⟨?_, hzKK⟩
      rw [mem_subConj, show m⁻¹ * S.z * m = S.z by
        rw [mul_assoc, ← S.mem_M_iff.mp hm]
        group]
      exact hzKK
    rw [hinf, mem_bot] at hz1
    exact S.z_ne_one hz1
  have hJ : L ⊓ centralizer (K : Set G) = ⊥ := by
    by_contra hne
    have hJM : L ⊓ centralizer (K : Set G) ≤ S.M := fun j hj =>
      S.mem_M_iff.mpr (mem_centralizer_iff.mp (mem_inf.mp hj).2 S.z hzKK).symm
    have hJQ : ∀ q ∈ S.QG, ∀ j ∈ L ⊓ centralizer (K : Set G),
        q * j * q⁻¹ ∈ L ⊓ centralizer (K : Set G) := by
      intro q hq j hj
      refine mem_inf.mpr ⟨hLn.conj_mem j (mem_inf.mp hj).1 q, mem_centralizer_iff.mpr ?_⟩
      intro k hk
      have hk' : q⁻¹ * k * q ∈ K := by
        have := hMK q (S.QG_le_M hq)
        exact mem_subConj.mp (by rw [this]; exact hk)
      have h1 := mem_centralizer_iff.mp (mem_inf.mp hj).2 _ hk'
      calc k * (q * j * q⁻¹) = q * ((q⁻¹ * k * q) * j) * q⁻¹ := by group
        _ = q * (j * (q⁻¹ * k * q)) * q⁻¹ := by rw [h1]
        _ = q * j * q⁻¹ * k := by group
    have hz := S.z_mem_of_le_M hJM hJQ hne
    exact hk₀ (mem_centralizer_iff.mp (mem_inf.mp hz).2 k₀ hk₀K)
  have hKg : ∀ g : G, Asc77.subConj K g = K := by
    intro g
    by_contra hne
    have hKg' := hK.subConj hLn g
    apply hKg'.2.2.1
    rw [eq_bot_iff, ← hJ]
    intro y hy
    refine mem_inf.mpr ⟨hKg'.1 hy, mem_centralizer_iff.mpr fun k hk => ?_⟩
    exact hK.commute hKg' (Ne.symm hne) hk hy
  have hKn : K.Normal := ⟨fun k hk g => by
    rw [← hKg g]
    exact conj_mem_subConj hk⟩
  have hKL : K = L := le_antisymm hK.1 (S.zGen_le_of_normal hKn hzKK)
  have : Nontrivial L := ⟨⟨⟨S.z, hzL⟩, 1, fun h => S.z_ne_one (congrArg Subtype.val h)⟩⟩
  refine ⟨fun N hN => ?_⟩
  by_cases hN1 : N = ⊥
  · exact Or.inl hN1
  right
  have hNmap : N.map L.subtype = K := by
    refine hK.2.2.2 _ (hKL ▸ map_subtype_le N) ?_ ?_
    · rintro l hl _ ⟨n, hn, rfl⟩
      exact ⟨⟨l, hl⟩ * n * ⟨l, hl⟩⁻¹, hN.conj_mem n hn ⟨l, hl⟩, rfl⟩
    · intro h
      exact hN1 ((map_eq_bot_iff_of_injective N L.subtype_injective).mp h)
  rw [eq_top_iff]
  intro x _
  have hx : (x : G) ∈ N.map L.subtype := by
    rw [hNmap, hKL]
    exact x.2
  obtain ⟨y, hy, hxy⟩ := hx
  rwa [Subtype.ext hxy] at hy

theorem fourSeven_gen {X : Set G} (hXQ : X ⊆ S.QG)
    (hX2 : ∀ x ∈ X, x * x = 1)
    (hXzmul : ∀ x ∈ X, x * S.z ∈ X) (hXne : X.Nonempty)
    (hgen : S.QG ≤ Subgroup.closure (X ∪ {S.z})) (hO : ∀ x ∈ X, S.ZInOTwo x) :
    S.M = ⊤ ∨ (∀ x ∈ S.zGen, x ≠ 1 → IsConj S.z x) ∨
      (IsSimpleGroup S.zGen ∧ Subgroup.centralizer (S.zGen : Set G) = ⊥) := by
  by_cases h : S.z ∈ centralizer (S.zGen : Set G)
  · exact Or.inr (Or.inl fun x hx hx1 => S.isConj_of_mem_zGen_of_mem_centralizer h hx hx1)
  · have hC := S.centralizer_zGen_eq_bot_of_not_mem_gen hX2 hXzmul hXne hO h
    exact Or.inr (Or.inr ⟨S.isSimpleGroup_zGen_gen hXQ hX2 hXzmul hXne hgen hO hC, hC⟩)

end Setting

end CFSG.LargeExtraspecial
