module

public import CFSG.Open.LocalVocabulary

public section

namespace CFSG.GroupTheory

open Subgroup

variable {G : Type*} [Group G] [Finite G]

private abbrev OrderThreeSubgroups (A : Subgroup G) : Type _ :=
  {P : Subgroup G // P ≤ A ∧ Nat.card P = 3}

private lemma map_conj_mem_orderThreeSubgroups {A : Subgroup G}
    (n : Subgroup.normalizer (A : Set G)) (P : OrderThreeSubgroups A) :
    P.1.map (MulAut.conj (n : G)).toMonoidHom ≤ A ∧
      Nat.card (P.1.map (MulAut.conj (n : G)).toMonoidHom) = 3 := by
  constructor
  · rintro x ⟨y, hy, rfl⟩
    exact (Subgroup.mem_normalizer_iff.mp n.2 y).mp (P.2.1 hy)
  · rw [Subgroup.card_map_of_injective (MulAut.conj (n : G)).injective, P.2.2]

private instance (A : Subgroup G) :
    MulAction (Subgroup.normalizer (A : Set G)) (OrderThreeSubgroups A) where
  smul n P :=
    ⟨P.1.map (MulAut.conj (n : G)).toMonoidHom, map_conj_mem_orderThreeSubgroups n P⟩
  one_smul P := by
    apply Subtype.ext
    change P.1.map (MulAut.conj (1 : G)).toMonoidHom = P.1
    rw [show (MulAut.conj (1 : G)).toMonoidHom = MonoidHom.id G by
      ext x
      simp [MulAut.conj_apply]]
    exact Subgroup.map_id P.1
  mul_smul n m P := by
    apply Subtype.ext
    change P.1.map (MulAut.conj (((n * m : Subgroup.normalizer (A : Set G)) : G))).toMonoidHom =
      (P.1.map (MulAut.conj (m : G)).toMonoidHom).map (MulAut.conj (n : G)).toMonoidHom
    rw [Subgroup.map_map]
    congr 1
    ext x
    simp [MulAut.conj_apply, mul_assoc]


private lemma coe_smul_orderThreeSubgroups {A : Subgroup G}
    (n : Subgroup.normalizer (A : Set G)) (P : OrderThreeSubgroups A) :
    ((n • P : OrderThreeSubgroups A) : Subgroup G) =
      P.1.map (MulAut.conj (n : G)).toMonoidHom := rfl

private theorem natCard_orderThreeSubgroups {A : Subgroup G}
    (hA : CFSG.Open.IsElemAbelian 3 A) (hAcard : Nat.card A = 27) :
    Nat.card (OrderThreeSubgroups A) = 13 := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  haveI : Fintype A := Fintype.ofFinite A
  let S := {x : A // x ≠ 1}
  haveI : Fintype S := Fintype.ofFinite S
  have hS : Nat.card S = 26 := by
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype_compl (fun x : A => x = 1)]
    rw [Fintype.card_eq_nat_card, hAcard]
    simp
  let f : S → OrderThreeSubgroups A := fun x =>
    ⟨Subgroup.zpowers (x.1 : G), by
      refine ⟨Subgroup.zpowers_le.mpr x.1.2, ?_⟩
      rw [Nat.card_zpowers]
      exact orderOf_eq_prime (by simpa using hA.2 x.1 x.1.2) (by exact_mod_cast x.2)⟩
  have hfiber : ∀ P : OrderThreeSubgroups A, Nat.card {x : S // f x = P} = 2 := by
    intro P
    obtain ⟨xg, hxgP, hxg1⟩ : ∃ x : G, x ∈ P.1 ∧ x ≠ 1 := by
      have hne : P.1 ≠ ⊥ := by
        intro hbot
        have h1 : Nat.card P.1 = 1 := by simp [hbot]
        omega
      rcases Subgroup.bot_or_exists_ne_one P.1 with h | ⟨x, hxP, hx1⟩
      · exact absurd h hne
      · exact ⟨x, hxP, hx1⟩
    have hxA : xg ∈ A := P.2.1 hxgP
    let xa : A := ⟨xg, hxA⟩
    have hxa1 : xa ≠ 1 := by
      intro h
      exact hxg1 (congrArg Subtype.val h)
    have hfx : f ⟨xa, hxa1⟩ = P := by
      apply Subtype.ext
      show Subgroup.zpowers xg = P.1
      have hle : Subgroup.zpowers xg ≤ P.1 := Subgroup.zpowers_le.mpr hxgP
      have hcard : Nat.card (Subgroup.zpowers xg) = Nat.card P.1 := by
        rw [Nat.card_zpowers, P.2.2]
        exact orderOf_eq_prime (by simpa using hA.2 xg hxA) hxg1
      exact Subgroup.eq_of_le_of_card_ge hle hcard.ge
    have hcard_fiber : Nat.card {z : S // f z = P} =
        Nat.card {y : A // y.1 ∈ P.1 ∧ y ≠ 1} := by
      refine Nat.card_congr ?_
      refine
        { toFun := fun z => ⟨z.1.1, ?_, z.1.2⟩
          invFun := fun y => ⟨⟨y.1, y.2.2⟩, ?_⟩
          left_inv := fun z => by apply Subtype.ext; rfl
          right_inv := fun y => by apply Subtype.ext; rfl }
      · have h : Subgroup.zpowers (z.1.1 : G) = P.1 := congrArg Subtype.val z.2
        rw [← h]
        exact Subgroup.mem_zpowers _
      · apply Subtype.ext
        show Subgroup.zpowers (y.1 : G) = P.1
        have hyG : (y.1 : G) ≠ 1 := by
          intro h
          exact y.2.2 (Subtype.ext h)
        have hle : Subgroup.zpowers (y.1 : G) ≤ P.1 :=
          Subgroup.zpowers_le.mpr y.2.1
        have hcard : Nat.card (Subgroup.zpowers (y.1 : G)) = Nat.card P.1 := by
          rw [Nat.card_zpowers, P.2.2]
          exact orderOf_eq_prime (by simpa using hA.2 (y.1 : G) y.1.2) hyG
        exact Subgroup.eq_of_le_of_card_ge hle hcard.ge
    have hcard_P : Nat.card {y : A // y.1 ∈ P.1 ∧ y ≠ 1} =
        Nat.card {z : P.1 // z ≠ 1} := by
      refine Nat.card_congr ?_
      exact
        { toFun := fun y => ⟨⟨y.1.1, y.2.1⟩, by
            intro h
            exact y.2.2 (Subtype.ext
              (show (y.1 : G) = 1 from congrArg (fun z : P.1 => (z : G)) h))⟩
          invFun := fun z => ⟨⟨z.1.1, P.2.1 z.1.2⟩, z.1.2, by
            intro h
            exact z.2 (Subtype.ext
              (show (z.1 : G) = 1 from congrArg (fun w : A => (w : G)) h))⟩
          left_inv := fun y => by apply Subtype.ext; rfl
          right_inv := fun z => by apply Subtype.ext; rfl }
    haveI : Fintype P.1 := Fintype.ofFinite P.1
    have hcard_nontriv : Nat.card {y : P.1 // y ≠ 1} = 2 := by
      rw [Nat.card_eq_fintype_card, Fintype.card_subtype_compl (fun y : P.1 => y = 1),
        Fintype.card_eq_nat_card, P.2.2]
      simp
    rw [hcard_fiber, hcard_P, hcard_nontriv]
  haveI : Fintype (OrderThreeSubgroups A) := Fintype.ofFinite _
  have hsum : Nat.card S = ∑ P : OrderThreeSubgroups A, Nat.card {x : S // f x = P} := by
    rw [← Nat.card_sigma]
    exact Nat.card_congr (Equiv.sigmaFiberEquiv f).symm
  have hcount : 26 = 2 * Nat.card (OrderThreeSubgroups A) := by
    have h : Nat.card S = ∑ _P : OrderThreeSubgroups A, 2 := by
      simpa only [hfiber] using hsum
    rw [hS] at h
    rw [h, Finset.sum_const, Finset.card_univ, Nat.card_eq_fintype_card]
    simp [Nat.mul_comm]
  omega

private theorem exists_fixed_orderThreeSubgroup
    {A : Subgroup G} (hA : CFSG.Open.IsElemAbelian 3 A) (hAcard : Nat.card A = 27)
    {p : ℕ} [Fact p.Prime] (hp5 : 5 ≤ p)
    {g : G} (hgA : g ∈ Subgroup.normalizer (A : Set G))
    (hg : IsPGroup p (Subgroup.zpowers g))
    {H : Subgroup G} (hHA : H ≤ Subgroup.normalizer (A : Set G))
    (hgH : g ∈ Subgroup.normalizer (H : Set G))
    {X : Subgroup G} (hXA : X ≤ A) (hX : Nat.card X = 3)
    (hmove : ∃ h ∈ H, X.map (MulAut.conj h).toMonoidHom ≠ X)
    (hmiss : ∃ Y : Subgroup G, Y ≤ A ∧ Nat.card Y = 3 ∧
      ∀ h ∈ H, X.map (MulAut.conj h).toMonoidHom ≠ Y) :
    ∃ P : OrderThreeSubgroups A,
      ∀ k : Subgroup.zpowers g,
        (Subgroup.inclusion (Subgroup.zpowers_le.mpr hgA) k) • P = P := by
  classical
  let N := Subgroup.normalizer (A : Set G)
  let K := Subgroup.zpowers g
  let Ω := OrderThreeSubgroups A
  have hKle : K ≤ N := Subgroup.zpowers_le.mpr hgA
  letI : MulAction K Ω := MulAction.compHom Ω (Subgroup.inclusion hKle)
  have hΩcard : Nat.card Ω = 13 := natCard_orderThreeSubgroups hA hAcard
  let XΩ : Ω := ⟨X, hXA, hX⟩
  have hKp : IsPGroup p K := hg
  by_contra hno
  have hno' : ¬ (MulAction.fixedPoints K Ω).Nonempty := by
    rintro ⟨P, hP⟩
    exact hno ⟨P, fun k => (MulAction.mem_fixedPoints.mp hP) k⟩
  have hp13 : p = 13 := by
    by_contra hpne
    have hndvd : ¬ p ∣ Nat.card Ω := by
      rw [hΩcard]
      intro hdvd
      have h : p = 1 ∨ p = 13 :=
        (show Nat.Prime 13 by norm_num).eq_one_or_self_of_dvd p hdvd
      exact hpne (h.resolve_left (Fact.out : Nat.Prime p).ne_one)
    exact hno' (hKp.nonempty_fixed_point_of_prime_not_dvd_card Ω hndvd)
  subst hp13
  have htrans : MulAction.IsPretransitive K Ω := by
    refine MulAction.IsPretransitive.mk fun P Q => ?_
    have horbit : MulAction.orbit K P = Set.univ := by
      rw [Set.eq_univ_iff_ncard]
      have hcard : (MulAction.orbit K P).ncard = 13 := by
        obtain ⟨n, hn⟩ := hKp.card_orbit P
        have hn' : (MulAction.orbit K P).ncard = 13 ^ n := by
          rw [← Nat.card_coe_set_eq, hn]
        have hle : (MulAction.orbit K P).ncard ≤ 13 := by
          calc (MulAction.orbit K P).ncard ≤ (Set.univ : Set Ω).ncard :=
                Set.ncard_le_ncard (Set.subset_univ _)
            _ = Nat.card Ω := Set.ncard_univ Ω
            _ = 13 := hΩcard
        have hnpos : 0 < n := by
          by_contra hn0
          have hn0' : n = 0 := Nat.eq_zero_of_not_pos hn0
          have h1 : (MulAction.orbit K P).ncard = 1 := by simp [hn', hn0']
          have hfix : P ∈ MulAction.fixedPoints K Ω := by
            rw [MulAction.mem_fixedPoints]
            intro k
            have hone : (MulAction.orbit K P) = {P} := by
              obtain ⟨x, hx⟩ := Set.ncard_eq_one.mp h1
              have hPx : P = x := by
                have : P ∈ ({x} : Set Ω) := by
                  rw [← hx]
                  exact MulAction.mem_orbit_self P
                simpa using this
              rw [hx, hPx]
            have : k • P ∈ ({P} : Set Ω) := by
              rw [← hone]
              exact MulAction.mem_orbit P k
            simpa using this
          exact hno' ⟨P, hfix⟩
        have hge : 13 ≤ (MulAction.orbit K P).ncard := by
          rw [hn']
          exact Nat.le_self_pow (Nat.ne_of_gt hnpos) 13
        omega
      rw [hcard, hΩcard]
    have : Q ∈ MulAction.orbit K P := by
      rw [horbit]
      exact Set.mem_univ Q
    obtain ⟨k, hk⟩ := MulAction.mem_orbit_iff.mp this
    exact ⟨k, hk⟩
  let L := H ⊔ K
  have hLle : L ≤ N := sup_le hHA hKle
  letI : MulAction L Ω := MulAction.compHom Ω (Subgroup.inclusion hLle)
  have hLtrans : MulAction.IsPretransitive L Ω := by
    refine MulAction.IsPretransitive.mk fun P Q => ?_
    obtain ⟨k, hk⟩ := htrans.exists_smul_eq P Q
    exact ⟨⟨k, (le_sup_right : K ≤ H ⊔ K) k.2⟩, hk⟩
  let H' : Subgroup L := H.subgroupOf L
  have hH'normal : H'.Normal := by
    have hLnormH : L ≤ Subgroup.normalizer (H : Set G) :=
      sup_le Subgroup.le_normalizer (Subgroup.zpowers_le.mpr hgH)
    exact (Subgroup.normal_subgroupOf_iff_le_normalizer le_sup_left).mpr hLnormH
  letI : H'.Normal := hH'normal
  have hcoe_H' : ∀ h' : H', ((h' • XΩ : Ω) : Subgroup G) =
      X.map (MulAut.conj
        ((Subgroup.subgroupOfEquivOfLe le_sup_left h' : H) : G)).toMonoidHom := by
    intro h'
    change ((Subgroup.inclusion hLle h' • XΩ : Ω) : Subgroup G) =
      X.map (MulAut.conj
        ((Subgroup.subgroupOfEquivOfLe le_sup_left h' : H) : G)).toMonoidHom
    rw [coe_smul_orderThreeSubgroups]
    congr 1
  have hblock : MulAction.IsBlock L (MulAction.orbit H' XΩ) :=
    MulAction.IsBlock.orbit_of_normal XΩ
  have hne : (MulAction.orbit H' XΩ).Nonempty := ⟨XΩ, MulAction.mem_orbit_self XΩ⟩
  have hdvd : (MulAction.orbit H' XΩ).ncard ∣ Nat.card Ω :=
    MulAction.IsBlock.ncard_dvd_card hblock hne
  have hdvd13 : (MulAction.orbit H' XΩ).ncard ∣ 13 := by
    rwa [hΩcard] at hdvd
  obtain ⟨Y, hYA, hYcard, hYmiss⟩ := hmiss
  let YΩ : Ω := ⟨Y, hYA, hYcard⟩
  have hYnot : YΩ ∉ MulAction.orbit H' XΩ := by
    intro hY
    obtain ⟨h', hh'⟩ := MulAction.mem_orbit_iff.mp hY
    have hcoe := congrArg (fun P : Ω => (P : Subgroup G)) hh'
    rw [hcoe_H'] at hcoe
    exact hYmiss _ (Subgroup.subgroupOfEquivOfLe le_sup_left h').2 hcoe
  have hproper : MulAction.orbit H' XΩ ⊂ Set.univ := by
    rw [Set.ssubset_univ_iff]
    intro htop
    exact hYnot (by rw [htop]; exact Set.mem_univ YΩ)
  have hlt : (MulAction.orbit H' XΩ).ncard < Nat.card Ω := by
    simpa only [Set.ncard_univ, hΩcard] using Set.ncard_lt_ncard hproper
  have hle12 : (MulAction.orbit H' XΩ).ncard ≤ 12 := by omega
  obtain ⟨h0, hh0H, hh0move⟩ := hmove
  let h0' : H' := (Subgroup.subgroupOfEquivOfLe le_sup_left).symm ⟨h0, hh0H⟩
  have h0coe : ((Subgroup.subgroupOfEquivOfLe le_sup_left h0' : H) : G) = h0 := by
    simp [h0']
  have hneq : h0' • XΩ ≠ XΩ := by
    intro h
    apply hh0move
    have hcoe := congrArg (fun P : Ω => (P : Subgroup G)) h
    rw [hcoe_H', h0coe] at hcoe
    exact hcoe
  have hsub : ({XΩ, h0' • XΩ} : Set Ω) ⊆ MulAction.orbit H' XΩ := by
    intro P hP
    rcases hP with hP | hP
    · rw [hP]
      exact MulAction.mem_orbit_self XΩ
    · rw [hP]
      exact MulAction.mem_orbit XΩ h0'
  have hpair : ({XΩ, h0' • XΩ} : Set Ω).ncard = 2 := Set.ncard_pair hneq.symm
  have hge2 : 2 ≤ (MulAction.orbit H' XΩ).ncard := by
    rw [← hpair]
    exact Set.ncard_le_ncard hsub
  have hdiv : (MulAction.orbit H' XΩ).ncard = 1 ∨
      (MulAction.orbit H' XΩ).ncard = 13 :=
    (Nat.dvd_prime (by norm_num : Nat.Prime 13)).mp hdvd13
  omega



private theorem mem_centralizer_of_fixed_orderThreeSubgroup
    {A : Subgroup G} (hA : CFSG.Open.IsElemAbelian 3 A) (hAcard : Nat.card A = 27)
    {p : ℕ} [Fact p.Prime] (hp5 : 5 ≤ p)
    {g : G} (hgA : g ∈ Subgroup.normalizer (A : Set G))
    (hg : IsPGroup p (Subgroup.zpowers g))
    {P : OrderThreeSubgroups A}
    (hP : ∀ k : Subgroup.zpowers g,
      (Subgroup.inclusion (Subgroup.zpowers_le.mpr hgA) k) • P = P) :
    g ∈ Subgroup.centralizer (A : Set G) := by
  classical
  let N := Subgroup.normalizer (A : Set G)
  let φ : MulAut A := A.normalizerMonoidHom ⟨g, hgA⟩
  let : MulAction (MulAut A) (Set A) :=
    { smul := fun f s => f '' s
      one_smul := by
        intro s
        ext x
        constructor
        · rintro ⟨y, hy, rfl⟩
          simpa using hy
        · intro hx
          exact ⟨x, hx, by rw [MulAut.one_apply]⟩
      mul_smul := by
        intro f g s
        ext x
        constructor
        · rintro ⟨y, hy, rfl⟩
          exact ⟨g y, ⟨y, hy, rfl⟩, rfl⟩
        · rintro ⟨z, ⟨y, hy, rfl⟩, rfl⟩
          exact ⟨y, hy, rfl⟩ }
  have hφp : IsPGroup p (Subgroup.zpowers φ) := by
    obtain ⟨n, hn⟩ := hg.exists_card_eq
    have hordg : orderOf g = p ^ n := by
      rw [← Nat.card_zpowers]
      exact hn
    have hdvd : orderOf φ ∣ p ^ n := by
      have h1 : orderOf φ ∣ orderOf (⟨g, hgA⟩ : N) := orderOf_map_dvd _ _
      rw [show orderOf (⟨g, hgA⟩ : N) = orderOf g from (Subgroup.orderOf_coe _).symm,
        hordg] at h1
      exact h1
    obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow Fact.out).mp hdvd
    exact IsPGroup.of_card (n := k) (by rwa [Nat.card_zpowers])
  let Gφ := Subgroup.zpowers φ
  let P_A : Subgroup A := P.1.subgroupOf A
  have hPnorm : P.1.map (MulAut.conj g).toMonoidHom = P.1 := by
    have h := hP ⟨g, Subgroup.mem_zpowers g⟩
    have hcoe := congrArg (fun Q : OrderThreeSubgroups A => (Q : Subgroup G)) h
    simpa [coe_smul_orderThreeSubgroups, Subgroup.zpowers_le.mpr hgA] using hcoe
  have hφ_mem : ∀ x : P_A, φ x.1 ∈ P_A := by
    intro x
    rw [Subgroup.mem_subgroupOf]
    have hx : (x.1 : G) ∈ P.1 := x.2
    have hmem : g * (x.1 : G) * g⁻¹ ∈ P.1.map (MulAut.conj g).toMonoidHom :=
      Subgroup.mem_map_of_mem _ hx
    rw [hPnorm] at hmem
    simpa [φ, Subgroup.normalizerMonoidHom_apply_apply_coe] using hmem
  have hφ_image_subset : φ '' (P_A : Set A) ⊆ (P_A : Set A) := by
    rintro _ ⟨x, hx, rfl⟩
    exact hφ_mem ⟨x, hx⟩
  have hφ_image_eq : φ '' (P_A : Set A) = (P_A : Set A) := by
    refine Set.eq_of_subset_of_ncard_le hφ_image_subset ?_
    rw [Set.ncard_image_of_injective _ φ.injective]
  have hφ_smul_eq : φ • (P_A : Set A) = (P_A : Set A) := hφ_image_eq
  have hφ_stab : φ ∈ MulAction.stabilizer (MulAut A) (P_A : Set A) := by
    rw [MulAction.mem_stabilizer_iff]
    exact hφ_smul_eq
  have hGφ_stab : Gφ ≤ MulAction.stabilizer (MulAut A) (P_A : Set A) :=
    Subgroup.zpowers_le.mpr hφ_stab
  have hPcard : (P_A : Set A).ncard = 3 := by
    rw [← Nat.card_coe_set_eq]
    exact (Nat.card_congr (Subgroup.subgroupOfEquivOfLe P.2.1).toEquiv).trans P.2.2
  have horbit_sub : ∀ x : P_A, MulAction.orbit Gφ x.1 ⊆ (P_A : Set A) := by
    intro x y hy
    obtain ⟨k, rfl⟩ := MulAction.mem_orbit_iff.mp hy
    have hk : (k : MulAut A) ∈ MulAction.stabilizer (MulAut A) (P_A : Set A) :=
      hGφ_stab k.2
    have hsmul : k • (P_A : Set A) = (P_A : Set A) :=
      (MulAction.mem_stabilizer_iff.mp hk)
    have : k • x.1 ∈ k • (P_A : Set A) := Set.smul_mem_smul_set x.2
    rwa [hsmul] at this
  have hfix : ∀ x : P_A, φ x.1 = x.1 := by
    intro x
    obtain ⟨n, hn⟩ := hφp.card_orbit x.1
    have hle : Nat.card (MulAction.orbit Gφ x.1) ≤ 3 := by
      calc Nat.card (MulAction.orbit Gφ x.1) = (MulAction.orbit Gφ x.1).ncard :=
            Nat.card_coe_set_eq _
        _ ≤ (P_A : Set A).ncard := Set.ncard_le_ncard (horbit_sub x)
        _ = 3 := hPcard
    have hcard_le : p ^ n ≤ 3 := by
      rw [← hn]
      exact hle
    have hn0 : n = 0 := by
      by_contra hn0
      have hge : 5 ≤ p ^ n := by
        calc 5 ≤ p := hp5
          _ ≤ p ^ n := Nat.le_self_pow hn0 p
      omega
    have h1 : (MulAction.orbit Gφ x.1).ncard = 1 := by
      rw [← Nat.card_coe_set_eq, hn, hn0, pow_zero]
    have hφfix : (⟨φ, Subgroup.mem_zpowers φ⟩ : Gφ) • x.1 = x.1 := by
      obtain ⟨y, hy⟩ := Set.ncard_eq_one.mp h1
      have hxy : x.1 = y := by
        have : x.1 ∈ ({y} : Set A) := by
          rw [← hy]
          exact MulAction.mem_orbit_self x.1
        simpa using this
      have hky : (⟨φ, Subgroup.mem_zpowers φ⟩ : Gφ) • x.1 = y := by
        have : (⟨φ, Subgroup.mem_zpowers φ⟩ : Gφ) • x.1 ∈ ({y} : Set A) := by
          rw [← hy]
          exact MulAction.mem_orbit x.1 _
        simpa using this
      exact hky.trans hxy.symm
    simpa [MulAut.smul_def] using hφfix
  have hPA_le_C : P_A ≤ FixedPoints.subgroup Gφ A := by
    intro x hx
    rw [FixedPoints.mem_subgroup]
    intro k
    have hφ_stab_x : φ ∈ MulAction.stabilizer (MulAut A) x := by
      rw [MulAction.mem_stabilizer_iff]
      simpa [MulAut.smul_def] using hfix ⟨x, hx⟩
    have hk := (Subgroup.zpowers_le.mpr hφ_stab_x) k.2
    exact MulAction.mem_stabilizer_iff.mp hk
  let C : Subgroup A := FixedPoints.subgroup Gφ A
  have hCcard : Nat.card C = Nat.card (MulAction.fixedPoints Gφ A) := rfl
  have hC_ge : 3 ≤ Nat.card C := by
    have := Subgroup.card_le_of_le hPA_le_C
    rwa [show Nat.card P_A = 3 from (Nat.card_congr
      (Subgroup.subgroupOfEquivOfLe P.2.1).toEquiv).trans P.2.2] at this
  have hmod := hφp.card_modEq_card_fixedPoints A
  have hmodC : Nat.card C ≡ 27 [MOD p] := by
    rw [hCcard]
    rw [hAcard] at hmod
    exact hmod.symm
  have hC_dvd : Nat.card C ∣ 27 := by
    rw [← hAcard]
    exact Subgroup.card_subgroup_dvd_card C
  have hC_cases : Nat.card C = 1 ∨ Nat.card C = 3 ∨ Nat.card C = 9 ∨ Nat.card C = 27 := by
    have hdvd : Nat.card C ∣ 3 ^ 3 := by
      rw [show (3 : ℕ) ^ 3 = 27 by norm_num]
      exact hC_dvd
    obtain ⟨k, hk_le, hk⟩ := (Nat.dvd_prime_pow (by norm_num : Nat.Prime 3)).mp hdvd
    interval_cases k <;> simp_all
  have hC27 : Nat.card C = 27 := by
    rcases hC_cases with h | h | h | h
    · have hdvd : p ∣ 2 * 13 := by
        rw [show (2 : ℕ) * 13 = 26 by norm_num]
        have := (Nat.modEq_iff_dvd' (a := Nat.card C) (b := 27) (n := p)
          (by rw [h]; norm_num)).mp hmodC
        simpa [h] using this
      have hp13 : p = 13 := by
        rcases (Nat.Prime.dvd_mul Fact.out).mp hdvd with h2 | h13
        · have := Nat.le_of_dvd (by norm_num) h2
          omega
        · exact ((show Nat.Prime 13 by norm_num).eq_one_or_self_of_dvd p h13).resolve_left
            (Fact.out : Nat.Prime p).ne_one
      omega
    · have hdvd : p ∣ 2 ^ 3 * 3 := by
        rw [show (2 : ℕ) ^ 3 * 3 = 24 by norm_num]
        have := (Nat.modEq_iff_dvd' (a := Nat.card C) (b := 27) (n := p)
          (by rw [h]; norm_num)).mp hmodC
        simpa [h] using this
      rcases (Nat.Prime.dvd_mul Fact.out).mp hdvd with h2 | h3
      · have h2' : p ∣ 2 := Nat.Prime.dvd_of_dvd_pow Fact.out h2
        have := Nat.le_of_dvd (by norm_num) h2'
        omega
      · have hp3 : p = 3 :=
          ((show Nat.Prime 3 by norm_num).eq_one_or_self_of_dvd p h3).resolve_left
            (Fact.out : Nat.Prime p).ne_one
        omega
    · have hdvd : p ∣ 2 * 3 ^ 2 := by
        rw [show (2 : ℕ) * 3 ^ 2 = 18 by norm_num]
        have := (Nat.modEq_iff_dvd' (a := Nat.card C) (b := 27) (n := p)
          (by rw [h]; norm_num)).mp hmodC
        simpa [h] using this
      rcases (Nat.Prime.dvd_mul Fact.out).mp hdvd with h2 | h3
      · have := Nat.le_of_dvd (by norm_num) h2
        omega
      · have h3' : p ∣ 3 := Nat.Prime.dvd_of_dvd_pow Fact.out h3
        have hp3 : p = 3 :=
          ((show Nat.Prime 3 by norm_num).eq_one_or_self_of_dvd p h3').resolve_left
            (Fact.out : Nat.Prime p).ne_one
        omega
    · exact h
  have hφ_one : φ = 1 := by
    apply MulEquiv.ext
    intro a
    have hCtop : C = ⊤ := Subgroup.eq_top_of_card_eq C (by rw [hC27, hAcard])
    have ha : a ∈ C := by rw [hCtop]; exact Subgroup.mem_top a
    have hfixa := (FixedPoints.mem_subgroup Gφ A a).mp ha
    have h := hfixa ⟨φ, Subgroup.mem_zpowers φ⟩
    simpa [MulAut.smul_def] using h
  have hker : (⟨g, hgA⟩ : N) ∈ A.normalizerMonoidHom.ker := by
    rw [MonoidHom.mem_ker]
    exact hφ_one
  rw [Subgroup.normalizerMonoidHom_ker] at hker
  rwa [Subgroup.mem_subgroupOf] at hker



theorem mem_centralizer_of_isPGroup_of_le_normalizer {G : Type*} [Group G] [Finite G]
    {A : Subgroup G} (hA : CFSG.Open.IsElemAbelian 3 A) (hAcard : Nat.card A = 27)
    {p : ℕ} [Fact p.Prime] (hp5 : 5 ≤ p) {g : G}
    (hgA : g ∈ Subgroup.normalizer (A : Set G)) (hg : IsPGroup p (Subgroup.zpowers g))
    {H : Subgroup G} (hHA : H ≤ Subgroup.normalizer (A : Set G))
    (hgH : g ∈ Subgroup.normalizer (H : Set G))
    {X : Subgroup G} (hXA : X ≤ A) (hX : Nat.card X = 3)
    (hmove : ∃ h ∈ H, X.map (MulAut.conj h).toMonoidHom ≠ X)
    (hmiss : ∃ Y : Subgroup G, Y ≤ A ∧ Nat.card Y = 3 ∧
      ∀ h ∈ H, X.map (MulAut.conj h).toMonoidHom ≠ Y) :
    g ∈ Subgroup.centralizer (A : Set G) := by
  obtain ⟨P, hP⟩ := exists_fixed_orderThreeSubgroup hA hAcard hp5 hgA hg hHA hgH hXA hX hmove hmiss
  exact mem_centralizer_of_fixed_orderThreeSubgroup hA hAcard hp5 hgA hg hP


end CFSG.GroupTheory

end
