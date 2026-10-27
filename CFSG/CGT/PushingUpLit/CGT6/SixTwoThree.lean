module

public import CFSG.CGT.PushingUpLit.CGT6.SixTwoNat
public import CFSG.CGT.PushingUpLit.CGT6.SixTwoOmega
public import CFSG.CGT.PushingUpLit.CGT6.SixTwoJ
public import CFSG.CGT.PushingUpLit.BHS.TwoSixteenThree

public section

namespace CFSG.CGT.PushingUpLit.CGT6

open CFSG CFSG.RankThree.PartOne CFSG.CGT.PushingUp CFSG.CGT.PushingUpLit
open CFSG.CGT.PushingUpLit.BHS CFSG.CGT.PushingUpLit.BHS6 CFSG.Quasithin CFSG.Quasithin.G6
open scoped commutatorElement Pointwise

theorem card_sl2_ne_three (n : ℕ) :
    Nat.card (Matrix.SpecialLinearGroup (Fin 2) (Fq n)) ≠ 3 := by
  intro h
  let t : Matrix.SpecialLinearGroup (Fin 2) (Fq n) :=
    ⟨!![1, 1; 0, 1], by simp [Matrix.det_fin_two]⟩
  have h11 : (1 : Fq n) + 1 = 0 := CharTwo.add_self_eq_zero 1
  have ht2 : t ^ 2 = 1 := by
    apply Subtype.ext
    rw [Matrix.SpecialLinearGroup.coe_pow, pow_two]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [t, Matrix.mul_apply, Fin.sum_univ_two, h11]
  have ht1 : t ≠ 1 := by
    intro h1
    have := congrArg (fun m : Matrix.SpecialLinearGroup (Fin 2) (Fq n) =>
      (m : Matrix (Fin 2) (Fin 2) (Fq n)) 0 1) h1
    simp [t] at this
  have h2 : orderOf t = 2 := orderOf_eq_prime ht2 ht1
  have := orderOf_dvd_natCard t
  rw [h2, h] at this
  omega

theorem prime_type_natural_alt {G : Type} [Group G] [Finite G] {Y : Subgroup G}
    (hY : InClassX ↥Y) (hp : (Nat.card (↥Y ⧸ pCore 2 ↥Y)).Prime) :
    ∃ φ : (↥Y ⧸ pCore 2 ↥Y) ≃* alternatingGroup (Fin (2 * 1 + 1)),
      IsNaturalAltModuleWith ↥Y 1 φ := by
  have h3 := card_top_eq_three_of_inClassX hY hp
  rcases hY.2 with ⟨n, hn, φ, hnat⟩ | ⟨n, hn, φ, hnat⟩
  · have hcard : Nat.card (alternatingGroup (Fin (2 * n + 1))) = 3 := by
      rw [← Nat.card_congr φ.toEquiv]
      exact h3
    have : Nontrivial (Fin (2 * n + 1)) := Fin.nontrivial_iff_two_le.mpr (by omega)
    rw [Nat.card_eq_fintype_card, card_alternatingGroup, Fintype.card_fin] at hcard
    have hn1 : n = 1 := by
      by_contra hne
      have h5 : 5 ≤ 2 * n + 1 := by omega
      have := Nat.factorial_le h5
      have h120 : Nat.factorial 5 = 120 := by decide
      omega
    subst hn1
    exact ⟨φ, hnat⟩
  · exfalso
    have : Nat.card (Matrix.SpecialLinearGroup (Fin 2) (Fq n)) = 3 := by
      rw [← Nat.card_congr φ.toEquiv]
      exact h3
    exact card_sl2_ne_three n this


theorem eq_bot_of_central_two_index_three {E : Type} [Group E] [Finite E] {Z : Subgroup E}
    [Z.Normal] (hZc : ∀ z ∈ Z, ∀ e : E, z * e = e * z) (hZ2 : IsPGroup 2 ↥Z)
    (h3 : Z.index = 3)
    (hNo : ∀ N : Subgroup E, N.Normal → (∀ x : E, ∃ k : ℕ, x ^ 2 ^ k ∈ N) → N = ⊤) :
    Z = ⊥ := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨m, hm⟩ := IsPGroup.iff_card.mp hZ2
  have hcop : Nat.Coprime (Nat.card Z) Z.index := by
    rw [hm, h3]
    exact Nat.Coprime.pow_left m (by norm_num)
  obtain ⟨H, hH⟩ := Subgroup.exists_right_complement'_of_coprime hcop
  have hsup : Z ⊔ H = ⊤ := hH.sup_eq_top
  have hdis : Disjoint Z H := hH.disjoint
  have hdec : ∀ e : E, ∃ z ∈ Z, ∃ h ∈ H, e = z * h := by
    intro e
    have he : e ∈ (Z : Set E) * (H : Set E) := by
      rw [← Subgroup.coe_mul_of_right_le_normalizer_left Z H
        (by rw [Subgroup.normalizer_eq_top Z]; exact le_top), hsup]
      trivial
    obtain ⟨z, hz, h, hh, rfl⟩ := he
    exact ⟨z, hz, h, hh, rfl⟩
  have hHn : H.Normal := by
    refine ⟨fun h hh e => ?_⟩
    obtain ⟨z, hz, h₀, hh₀, rfl⟩ := hdec e
    have hc : z * (h₀ * h * h₀⁻¹) = (h₀ * h * h₀⁻¹) * z := hZc z hz _
    have e1 : z * h₀ * h * (z * h₀)⁻¹ = h₀ * h * h₀⁻¹ := by
      calc z * h₀ * h * (z * h₀)⁻¹ = z * (h₀ * h * h₀⁻¹) * z⁻¹ := by group
        _ = (h₀ * h * h₀⁻¹) * z * z⁻¹ := by rw [hc]
        _ = h₀ * h * h₀⁻¹ := by group
    rw [e1]
    exact H.mul_mem (H.mul_mem hh₀ hh) (H.inv_mem hh₀)
  have hHtop : H = ⊤ := by
    refine hNo H hHn fun x => ⟨m, ?_⟩
    obtain ⟨z, hz, h₀, hh₀, rfl⟩ := hdec x
    have hcomm : Commute z h₀ := hZc z hz h₀
    rw [hcomm.mul_pow]
    have hz1 : z ^ 2 ^ m = 1 := by
      have := pow_card_eq_one' (G := ↥Z) (x := ⟨z, hz⟩)
      rw [hm] at this
      exact congrArg Subtype.val this
    rw [hz1, one_mul]
    exact H.pow_mem hh₀ _
  rw [eq_bot_iff]
  intro z hz
  have hzH : z ∈ H := by rw [hHtop]; trivial
  exact Subgroup.mem_bot.mpr (Subgroup.mem_bot.mp (hdis.le_bot ⟨hz, hzH⟩))

theorem oTwoIn_le_centralizer_of_card_three {G : Type} [Group G] [Finite G] {V Y : Subgroup G}
    [V.Normal] (hres : oResidualTwo ↥Y = ⊤) (h3 : Nat.card (↥Y ⧸ pCore 2 ↥Y) = 3)
    (hN0 : Y ⊓ Subgroup.centralizer (V : Set G) ≤ oTwoIn Y)
    (hUC : ⁅oTwoIn Y, Y⁆ ≤ Subgroup.centralizer (V : Set G)) :
    oTwoIn Y ≤ Subgroup.centralizer (V : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set K : Subgroup ↥Y := (Subgroup.centralizer (V : Set G)).comap Y.subtype with hK
  have hKn : K.Normal := (inferInstance : (Subgroup.centralizer (V : Set G)).Normal).comap _
  have hKP : K ≤ pCore 2 ↥Y := fun x hx => by
    have : (x : G) ∈ oTwoIn Y := hN0 ⟨x.2, hx⟩
    exact (Subgroup.mem_map_iff_mem Y.subtype_injective).mp this
  have hPn : (pCore 2 ↥Y).Normal := pCore_normal
  have hZn : ((pCore 2 ↥Y).map (QuotientGroup.mk' K)).Normal :=
    hPn.map _ (QuotientGroup.mk'_surjective K)
  have hZ : (pCore 2 ↥Y).map (QuotientGroup.mk' K) = ⊥ := by
    refine eq_bot_of_central_two_index_three ?_ (isPGroup_map_two pCore_isPGroup _) ?_ ?_
    · rintro _ ⟨p, hp, rfl⟩ e
      obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective e
      show (QuotientGroup.mk p : ↥Y ⧸ K) * QuotientGroup.mk y =
        QuotientGroup.mk y * QuotientGroup.mk p
      rw [← commutatorElement_eq_one_iff_mul_comm]
      show ⁅QuotientGroup.mk' K p, QuotientGroup.mk' K y⁆ = 1
      rw [← map_commutatorElement]
      exact (QuotientGroup.eq_one_iff _).mpr
        (hUC (Subgroup.commutator_mem_commutator ⟨p, hp, rfl⟩ y.2))
    · rw [Subgroup.index_map, QuotientGroup.ker_mk', MonoidHom.range_eq_top.mpr
        (QuotientGroup.mk'_surjective K), Subgroup.index_top, mul_one, sup_eq_left.mpr hKP]
      exact h3
    · intro N hN hpow
      have hN' : (N.comap (QuotientGroup.mk' K)).Normal := hN.comap _
      have htop := (oResidualTwo_eq_top_iff).1 hres _ hN' fun y => by
        obtain ⟨k, hk⟩ := hpow (QuotientGroup.mk' K y)
        exact ⟨k, by simpa [map_pow] using hk⟩
      rw [eq_top_iff]
      intro q _
      obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective q
      have : y ∈ N.comap (QuotientGroup.mk' K) := by rw [htop]; trivial
      exact this
  rintro _ ⟨p, hp, rfl⟩
  have : QuotientGroup.mk' K p ∈ (pCore 2 ↥Y).map (QuotientGroup.mk' K) := ⟨p, hp, rfl⟩
  rw [hZ, Subgroup.mem_bot] at this
  exact (QuotientGroup.eq_one_iff p).mp this


theorem mem_normalizer_of_map_conj_eq_self {G : Type} [Group G] {W : Subgroup G} {a : G}
    (h : W.map (MulAut.conj a).toMonoidHom = W) : a ∈ Subgroup.normalizer (W : Set G) := by
  refine Subgroup.mem_normalizer_iff.mpr fun y => ⟨fun hy => ?_, fun hy => ?_⟩
  · have : a * y * a⁻¹ ∈ W.map (MulAut.conj a).toMonoidHom :=
      ⟨y, hy, by simp [MulAut.conj_apply]⟩
    rwa [h] at this
  · have hy' : a * y * a⁻¹ ∈ W.map (MulAut.conj a).toMonoidHom := by rw [h]; exact hy
    obtain ⟨z, hz, hzy⟩ := hy'
    have h2 : a * z * a⁻¹ = a * y * a⁻¹ := by simpa [MulAut.conj_apply] using hzy
    have hzy' : z = y := mul_left_cancel (mul_right_cancel h2)
    rwa [← hzy']

theorem normalizes_of_prime_type {G : Type} [Group G] [Finite G] {V Y : Subgroup G} [V.Normal]
    (hchar : IsCharacteristicP 2 G) (hV : CFSG.Open.IsElemAbelian 2 V) (hY : InClassX ↥Y)
    (hp : (Nat.card (↥Y ⧸ pCore 2 ↥Y)).Prime) (h : XCtx V Y Y)
    (hYV : ¬ Y ≤ Subgroup.centralizer (V : Set G)) (hUV : ⁅oTwoIn Y, Y⁆ ≤ V)
    {A : Subgroup G} (hA : IsMaxElemAbelian ⊤ A) : A ≤ Subgroup.normalizer (Y : Set G) := by
  classical
  by_cases hAC : A ≤ Subgroup.centralizer (V : Set G)
  · exact fun a ha => (h.hCY (hAC ha)).1
  have hOff : IsOffG V A :=
    isOffG_of_isMaxElemAbelian hV le_top (by rw [Subgroup.normalizer_eq_top V]) hA hAC
  have hAN : A ≤ Subgroup.normalizer (V : Set G) := hOff.1
  have hYN : Y ≤ Subgroup.normalizer (V : Set G) := by
    rw [Subgroup.normalizer_eq_top V]
    exact le_top
  have h3 := card_top_eq_three_of_inClassX hY hp
  obtain ⟨φ, hφ⟩ := prime_type_natural_alt hY hp
  have hres := hY.1.residual_eq
  have hVC : V ≤ Subgroup.centralizer (V : Set G) := fun v hv =>
    Subgroup.mem_centralizer_iff.mpr fun w hw => isElemAbelian_comm' hV hw hv
  have hUC : ⁅oTwoIn Y, Y⁆ ≤ Subgroup.centralizer (V : Set G) := hUV.trans hVC
  have hN0 : Y ⊓ Subgroup.centralizer (V : Set G) ≤ oTwoIn Y := h.inf_le_oTwoIn
  have hO2C : oTwoIn Y ≤ Subgroup.centralizer (V : Set G) :=
    oTwoIn_le_centralizer_of_card_three hres h3 hN0 hUC
  have hCU : Y ⊓ Subgroup.centralizer (blockU Y : Set G) = oTwoIn Y :=
    inf_centralizer_blockU_eq hY.1 (by norm_num) hφ
  have hker : Y ⊓ Subgroup.centralizer (V : Set G) =
      Y ⊓ Subgroup.centralizer (blockU Y : Set G) := by
    rw [hCU]
    exact le_antisymm hN0 (le_inf (oTwoIn_le Y) hO2C)
  have hYVU : ⁅Y, V⁆ = blockU Y := by
    have hsY : (Y.subgroupOf ⊤).IsSubnormal := isSubnormal_subgroupOf_of_isSubnormal h.hXs ⊤
    obtain ⟨-, -, hc⟩ := commutator_eq_U_of_isSubnormal hY.1 (isPGroup_two_of_isElemAbelian hV)
      hYN (le_top : Y ≤ ⊤) (le_top : V ≤ ⊤) hsY
    rcases hc with hc | hc
    · exact absurd (Subgroup.commutator_eq_bot_iff_le_centralizer.mp
        (by rw [Subgroup.commutator_comm]; exact hc)) hYV
    · rw [Subgroup.commutator_comm]
      exact hc
  let _ : CommGroup ↥V := commGroupOfElemAbelian hV
  have hV2 : ∀ v : ↥V, v ^ 2 = 1 := fun v => Subtype.ext (by simpa using hV.2 v v.2)
  have hnatY : IsNatAlt Y (blockU Y) (2 * 1 + 1) := isNatAlt_blockU hY.1 (by norm_num) hφ
  have hfac : ∀ w ∈ blockU Y, ∃ p ∈ (⁅Y, V⁆ : Subgroup G),
      ∃ c ∈ blockU Y ⊓ Subgroup.centralizer (Y : Set G), w = p * c :=
    fun w hw => ⟨w, hYVU ▸ hw, 1, one_mem _, (mul_one w).symm⟩
  have hsec := isNatSectionBy_autOn hV hYN hnatY hYVU.le hfac hker
  have hnat3 : IsAltNatSection (autOn Y V) (commV (autOn Y V))
      (commV (autOn Y V) ⊓ fixV (autOn Y V)) 3 := (isAltNatSection_iff).mpr hsec
  have hsub : CFSG.Open.IsSubnormal (autOn Y V) (autOn ⊤ V) := autOn_isSubnormal h.hXs
  have hoff : IsOff (autOn A V) := (isOffG_iff_isOff_autOn hV hAN).mp hOff
  have hAG : autOn A V ≤ autOn ⊤ V := autOn_le_autOn V le_top
  have hAnorm : autOn A V ≤ Subgroup.normalizer (autOn Y V : Set (MulAut ↥V)) := by
    by_cases hEA : ⁅autOn Y V, autOn A V⁆ = ⊥
    · intro g hg
      have hEc := Subgroup.commutator_eq_bot_iff_le_centralizer.mp hEA
      have e1 : ∀ g' ∈ autOn A V, ∀ e' ∈ autOn Y V, g' * e' * g'⁻¹ = e' := fun g' hg' e' he' => by
        have := Subgroup.mem_centralizer_iff.mp (hEc he') g' hg'
        rw [this]
        group
      rw [Subgroup.mem_normalizer_iff]
      intro e
      constructor
      · intro he
        rw [e1 g hg e he]
        exact he
      · intro he
        have h1 := e1 g⁻¹ ((autOn A V).inv_mem hg) _ he
        have e2 : g⁻¹ * (g * e * g⁻¹) * g⁻¹⁻¹ = e := by group
        rw [e2] at h1
        rw [h1]
        exact he
    · exact (two_sixteen_three hV2 hoff hAG hsub hnat3 hEA).1
  obtain ⟨-, θ, β, hβs, hβk, -⟩ := hnat3
  obtain ⟨-, hinf, -⟩ := three_facts hV2 rfl θ β hβs hβk
  have hmapY := conj_mem_sup_centralizer_of_autOn hAN hAnorm
  have hCN : Subgroup.centralizer (V : Set G) ≤ Subgroup.normalizer (Y : Set G) :=
    fun g hg => (h.hCY hg).1
  have hCn : (Subgroup.centralizer (V : Set G)).Normal := inferInstance
  intro a ha
  by_contra hna
  have hne : Y.map (MulAut.conj a).toMonoidHom ≠ Y := fun heq =>
    hna (mem_normalizer_of_map_conj_eq_self heq)
  have hblk' : IsBlockInX (Y.map (MulAut.conj a).toMonoidHom) :=
    ⟨h.hXs.map (MulAut.conj a).surjective,
      InClassX.of_mulEquiv ((MulAut.conj a).subgroupMap Y) hY⟩
  have hcomm : ⁅Y.map (MulAut.conj a).toMonoidHom, Y⁆ = ⊥ :=
    distinct_blocks_commute_of_inClassX hchar hblk' ⟨h.hXs, hY⟩ hne
  have hagree : ∀ y ∈ Y, ∃ y' ∈ Y.map (MulAut.conj a).toMonoidHom,
      y⁻¹ * y' ∈ Subgroup.centralizer (V : Set G) := by
    intro y hy
    have h1 := hmapY a⁻¹ (A.inv_mem ha) y hy
    rw [inv_inv] at h1
    have hmem : a⁻¹ * y * a ∈ (Y : Set G) * (Subgroup.centralizer (V : Set G) : Set G) := by
      rw [← Subgroup.coe_mul_of_right_le_normalizer_left Y _ hCN]
      exact h1
    obtain ⟨y₀, hy₀, c, hc, hyc⟩ := hmem
    refine ⟨a * y₀ * a⁻¹, ⟨y₀, hy₀, by simp [MulAut.conj_apply]⟩, ?_⟩
    have hyc' : y₀ * c = a⁻¹ * y * a := hyc
    have e1 : y = a * (y₀ * c) * a⁻¹ := by
      rw [hyc']
      group
    have e2 : y⁻¹ * (a * y₀ * a⁻¹) = (a * c * a⁻¹)⁻¹ := by
      rw [e1]
      group
    rw [e2]
    exact (Subgroup.centralizer (V : Set G)).inv_mem (hCn.conj_mem c hc a)
  have hcent : ∀ u ∈ blockU Y, ∀ y ∈ Y, y * u * y⁻¹ = u := by
    intro u hu y hy
    obtain ⟨y', hy', hyc⟩ := hagree y hy
    have hu1 : y' * u = u * y' := by
      have : ⁅y', u⁆ ∈ ⁅Y.map (MulAut.conj a).toMonoidHom, Y⁆ :=
        Subgroup.commutator_mem_commutator hy' (blockU_le Y hu)
      rw [hcomm, Subgroup.mem_bot] at this
      exact commutatorElement_eq_one_iff_mul_comm.mp this
    have hcu : u * (y⁻¹ * y') = (y⁻¹ * y') * u :=
      Subgroup.mem_centralizer_iff.mp hyc u (hUV hu)
    have hy_eq : y = y' * (y⁻¹ * y')⁻¹ := by group
    have e3 : (y⁻¹ * y')⁻¹ * u * (y⁻¹ * y') = u := by
      rw [mul_assoc, hcu]
      group
    calc y * u * y⁻¹ = y' * ((y⁻¹ * y')⁻¹ * u * (y⁻¹ * y')) * y'⁻¹ := by
          conv_lhs => rw [hy_eq]
          group
      _ = u := by
          rw [e3, hu1]
          group
  obtain ⟨⟨u, hu⟩, hu1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp (blockU_ne_bot_of_short hY.1)
  have huV : u ∈ V := hUV (by
    rw [show blockU Y = ⁅oTwoIn Y, Y⁆ from rfl] at hu
    exact hu)
  have hcomm_mem : (⟨u, huV⟩ : ↥V) ∈ commV (autOn Y V) := by
    have : (⟨u, huV⟩ : ↥V) ∈ commOn hV Y := by
      rw [commOn_eq hV hYN, Subgroup.mem_subgroupOf]
      show u ∈ ⁅Y, V⁆
      rw [hYVU]
      exact hu
    exact this
  have hfix_mem : (⟨u, huV⟩ : ↥V) ∈ fixV (autOn Y V) := by
    intro g hg
    obtain ⟨y, hy, rfl⟩ := mem_autOn_iff.mp hg
    apply Subtype.ext
    rw [conjAct_apply']
    exact hcent u hu y hy
  have hmem : (⟨u, huV⟩ : ↥V) ∈ commV (autOn Y V) ⊓ fixV (autOn Y V) := ⟨hcomm_mem, hfix_mem⟩
  rw [hinf, Subgroup.mem_bot] at hmem
  have hu0 : u = 1 := congrArg Subtype.val hmem
  exact hu1 (Subtype.ext hu0)

end CFSG.CGT.PushingUpLit.CGT6
