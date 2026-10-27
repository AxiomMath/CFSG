module

public import CFSG.CharacterTheory.Semidihedral.Principal.NormalFourAffineAction
public import CFSG.CharacterTheory.Semidihedral.Principal.CoprimeFixedPointLifting
public import CFSG.CharacterTheory.Semidihedral.Principal.CyclicInversionAlternatingFive
public import CFSG.CharacterTheory.Semidihedral.Principal.NormalPrimeInversionInvolutionSum

public section

namespace CFSG.Semidihedral.Principal

open CFSG.TwoRankLowerBound.Helpers

universe u

namespace OrderOneTwenty

open scoped Classical

variable {H : Type u} [Group H] [Fintype H]

theorem index_centralizer_le_two_of_central (V : Subgroup H) [V.Normal] [IsKleinFour V] {v : H}
    (hvV : v ∈ V) (hv1 : v ≠ 1) (hcentral : ∀ h : H, h * v * h⁻¹ = v) :
    (Subgroup.centralizer (V : Set H)).index ≤ 2 := by
  obtain ⟨x, hx⟩ := Finset.card_pos.mp (by
    rw [Finset.card_erase_of_mem (Finset.mem_erase.mpr ⟨fun h => hv1 (congrArg Subtype.val h),
      Finset.mem_univ _⟩), Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ,
      IsKleinFour.card_four']
    norm_num : 0 < (((Finset.univ : Finset V).erase 1).erase ⟨v, hvV⟩).card)
  have hx1 : x ≠ 1 := (Finset.mem_erase.mp (Finset.mem_erase.mp hx).2).1
  have hxv : x ≠ ⟨v, hvV⟩ := (Finset.mem_erase.mp hx).1
  have hv1' : (⟨v, hvV⟩ : V) ≠ 1 := fun h => hv1 (congrArg Subtype.val h)
  have huniv := IsKleinFour.eq_finset_univ hv1' hx1 (Ne.symm hxv)
  have hconj_x : ∀ h : H, h * (x : H) * h⁻¹ = x ∨ h * (x : H) * h⁻¹ = v * x := by
    intro h
    have hmem := CFSG.Semidihedral.Principal.NormalFourAffine.conj_mem_ne V h x.2
      (fun h1 => hx1 (Subtype.ext h1))
    by_cases hfix : h * (x : H) * h⁻¹ = x
    · exact Or.inl hfix
    · right
      have hne_v : (⟨h * x * h⁻¹, hmem.1⟩ : V) ≠ ⟨v, hvV⟩ := by
        intro h1
        have h2 : h * (x : H) * h⁻¹ = h * v * h⁻¹ := by
          rw [hcentral h]
          exact congrArg Subtype.val h1
        apply hxv
        apply Subtype.ext
        simpa using h2
      have h3 := IsKleinFour.eq_mul_of_ne_all hv1' hx1 (Ne.symm hxv)
        (z := ⟨h * x * h⁻¹, hmem.1⟩) (fun h1 => hmem.2 (congrArg Subtype.val h1)) hne_v
        (fun h1 => hfix (congrArg Subtype.val h1))
      exact congrArg Subtype.val h3
  have hle : Subgroup.centralizer ({(x : H)} : Set H) ≤ Subgroup.centralizer (V : Set H) := by
    intro g hg
    rw [Subgroup.mem_centralizer_singleton_iff] at hg
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    have hzmem : (⟨z, hz⟩ : V) ∈ ({⟨v, hvV⟩ * x, ⟨v, hvV⟩, x, 1} : Finset V) := by
      rw [huniv]
      exact Finset.mem_univ _
    have hvg : g * v = v * g := by
      have h1 := hcentral g
      calc g * v = g * v * g⁻¹ * g := by group
        _ = v * g := by rw [h1]
    simp only [Finset.mem_insert, Finset.mem_singleton] at hzmem
    rcases hzmem with h1 | h1 | h1 | h1 <;>
      have h2 := congrArg Subtype.val h1 <;>
      simp only [Subgroup.coe_mul, Subgroup.coe_one] at h2 <;> rw [h2]
    · rw [mul_assoc, ← hg, ← mul_assoc, ← hvg, mul_assoc]
    · exact hvg.symm
    · exact hg.symm
    · rw [one_mul, mul_one]
  have hidx : (Subgroup.centralizer ({(x : H)} : Set H)).index ≤ 2 := by
    by_cases htop : Subgroup.centralizer ({(x : H)} : Set H) = ⊤
    · rw [htop, Subgroup.index_top]
      norm_num
    · obtain ⟨h₁, hh₁⟩ : ∃ h₁ : H, h₁ ∉ Subgroup.centralizer ({(x : H)} : Set H) := by
        by_contra hall
        push Not at hall
        exact htop (eq_top_iff.mpr fun g _ => hall g)
      have hmove : ∀ b : H, b ∉ Subgroup.centralizer ({(x : H)} : Set H) →
          b * (x : H) * b⁻¹ = v * x := by
        intro b hb
        rcases hconj_x b with h1 | h1
        · exfalso
          apply hb
          rw [Subgroup.mem_centralizer_singleton_iff]
          calc b * (x : H) = b * x * b⁻¹ * b := by group
            _ = x * b := by rw [h1]
        · exact h1
      have hv2 : v * v = 1 := congrArg Subtype.val (IsKleinFour.mul_self (⟨v, hvV⟩ : V))
      have hvx : ∀ b : H, b * (v * (x : H)) * b⁻¹ = v * (b * x * b⁻¹) := by
        intro b
        calc b * (v * (x : H)) * b⁻¹ = (b * v * b⁻¹) * (b * x * b⁻¹) := by group
          _ = v * (b * x * b⁻¹) := by rw [hcentral b]
      apply le_of_eq
      apply Subgroup.index_eq_two_iff.mpr
      refine ⟨h₁, fun b => ?_⟩
      have hb1 : b * h₁ * (x : H) * (b * h₁)⁻¹ = b * (h₁ * x * h₁⁻¹) * b⁻¹ := by group
      by_cases hb : b ∈ Subgroup.centralizer ({(x : H)} : Set H)
      · refine Or.inr ⟨hb, fun hbh => ?_⟩
        have hbx : b * (x : H) * b⁻¹ = x := by
          rw [Subgroup.mem_centralizer_singleton_iff] at hb
          rw [hb, mul_inv_cancel_right]
        rw [Subgroup.mem_centralizer_singleton_iff] at hbh
        have h2 : b * h₁ * (x : H) * (b * h₁)⁻¹ = x := by
          rw [hbh, mul_inv_cancel_right]
        rw [hb1, hmove h₁ hh₁, hvx, hbx] at h2
        have h3 : v = 1 := by
          calc v = v * x * (x : H)⁻¹ := by group
            _ = 1 := by rw [h2, mul_inv_cancel]
        exact hv1 h3
      · refine Or.inl ⟨?_, hb⟩
        rw [Subgroup.mem_centralizer_singleton_iff]
        have h2 : b * h₁ * (x : H) * (b * h₁)⁻¹ = x := by
          rw [hb1, hmove h₁ hh₁, hvx, hmove b hb, ← mul_assoc, hv2, one_mul]
        calc b * h₁ * (x : H) = b * h₁ * x * (b * h₁)⁻¹ * (b * h₁) := by group
          _ = x * (b * h₁) := by rw [h2]
  calc (Subgroup.centralizer (V : Set H)).index
      ≤ (Subgroup.centralizer ({(x : H)} : Set H)).index := Subgroup.index_antitone hle
    _ ≤ 2 := hidx

theorem exists_quotient_equiv_perm (hH : Nat.card H = 120) (V W : Subgroup H) [V.Normal]
    [W.Normal] [IsKleinFour V] (hW : Nat.card W = 5)
    (hCV : Subgroup.centralizer (V : Set H) = V ⊔ W)
    (hWK : W ≤ Subgroup.centralizer (W : Set H))
    (hindex : (Subgroup.centralizer (W : Set H)).index = 2) :
    ∃ τ : H ⧸ W ≃* Equiv.Perm (Fin 4), ∀ q : H ⧸ W,
      q ∈ (Subgroup.centralizer (W : Set H)).map (QuotientGroup.mk' W) ↔
        τ q ∈ alternatingGroup (Fin 4) := by
  have hVW : V ⊓ W = ⊥ := disjoint_iff.mp (Subgroup.disjoint_of_coprime_natCard
    (by rw [IsKleinFour.card_four, hW]; norm_num))
  have hsup : Nat.card (V ⊔ W : Subgroup H) = 20 := by
    have h1 := Subgroup.relIndex_mul_card (H := W) (K := V ⊔ W)
    rw [inf_of_le_left le_sup_right, Subgroup.relIndex_sup_right] at h1
    have h2 := Subgroup.relIndex_mul_card (H := W) (K := V)
    rw [inf_comm, hVW, Subgroup.card_bot, mul_one, IsKleinFour.card_four] at h2
    rw [← h1, h2, hW]
  have hCVidx : (Subgroup.centralizer (V : Set H)).index = 6 := by
    have h1 := (Subgroup.centralizer (V : Set H)).card_mul_index
    have h2 : Nat.card (Subgroup.centralizer (V : Set H)) = 20 := by rw [hCV, hsup]
    rw [h2, hH] at h1
    omega
  have hnocentral : ∀ v ∈ V, v ≠ 1 → ∃ h : H, h * v * h⁻¹ ≠ v := by
    intro v hv hv1
    by_contra hall
    push Not at hall
    have h1 := index_centralizer_le_two_of_central V hv hv1 hall
    omega
  let f : V →* H ⧸ W := (QuotientGroup.mk' W).comp V.subtype
  have hfinj : Function.Injective f := by
    rw [injective_iff_map_eq_one]
    intro v hv
    have h1 : (v : H) ∈ W := (QuotientGroup.eq_one_iff _).mp hv
    have h2 : (v : H) ∈ V ⊓ W := ⟨v.2, h1⟩
    rw [hVW] at h2
    exact Subtype.ext h2
  have hrange : f.range = V.map (QuotientGroup.mk' W) := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
  let eV : V ≃* V.map (QuotientGroup.mk' W) :=
    (MonoidHom.ofInjective hfinj).trans (MulEquiv.subgroupCongr hrange)
  have hK4 : IsKleinFour (V.map (QuotientGroup.mk' W)) :=
    ⟨by rw [← Nat.card_congr eV.toEquiv]; exact IsKleinFour.card_four,
      by rw [← Monoid.exponent_eq_of_mulEquiv eV]; exact IsKleinFour.exponent_two⟩
  have hVbarn : (V.map (QuotientGroup.mk' W)).Normal :=
    Subgroup.Normal.map inferInstance _ (QuotientGroup.mk'_surjective W)
  have hmapsup : (V ⊔ W).map (QuotientGroup.mk' W) = V.map (QuotientGroup.mk' W) := by
    rw [Subgroup.map_sup, QuotientGroup.map_mk'_self, sup_bot_eq]
  have hcentX : Subgroup.centralizer ((V.map (QuotientGroup.mk' W) : Subgroup (H ⧸ W)) :
      Set (H ⧸ W)) = V.map (QuotientGroup.mk' W) := by
    let α : V →* MulAut H := MulAut.conj.comp V.subtype
    have hN : ∀ a : V, ∀ n ∈ W, α a n ∈ W := fun a n hn =>
      Subgroup.Normal.conj_mem inferInstance n hn a
    have hcop : ¬ 2 ∣ Nat.card W := by
      rw [hW]
      norm_num
    have hA : IsPGroup 2 V := IsPGroup.of_card (n := 2) (by rw [IsKleinFour.card_four]; norm_num)
    have hlift := coprime_fixed_point_lifting 2 hA α W hN hcop
    apply le_antisymm
    · intro q hq
      have hq' : q ∈ {q : H ⧸ W | ∀ a : V, CoprimeFixedPoint.quotientAction α W hN a q = q} := by
        intro a
        obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective q
        rw [CoprimeFixedPoint.quotientAction_mk]
        have h1 := Subgroup.mem_centralizer_iff.mp hq ((a : H) : H ⧸ W) ⟨a, a.2, rfl⟩
        change (((a : H) * g * (a : H)⁻¹ : H) : H ⧸ W) = (g : H ⧸ W)
        rw [QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv, h1]
        group
      rw [hlift] at hq'
      obtain ⟨c, hc, rfl⟩ := hq'
      have hcC : c ∈ Subgroup.centralizer (V : Set H) := by
        rw [Subgroup.mem_centralizer_iff]
        intro v hv
        have h1 : (v : H) * c * v⁻¹ = c := hc ⟨v, hv⟩
        calc v * c = v * c * v⁻¹ * v := by group
          _ = c * v := by rw [h1]
      rw [hCV] at hcC
      rw [← hmapsup]
      exact ⟨c, hcC, rfl⟩
    · intro q hq
      rw [Subgroup.mem_centralizer_iff]
      intro r hr
      have h1 := (IsKleinFour.isMulCommutative (G := V.map (QuotientGroup.mk' W))).is_comm.comm
        ⟨r, hr⟩ ⟨q, hq⟩
      exact congrArg Subtype.val h1
  have hminX : ∀ N : Subgroup (H ⧸ W), N.Normal → N ≤ V.map (QuotientGroup.mk' W) →
      N = ⊥ ∨ N = V.map (QuotientGroup.mk' W) := by
    intro N hNn hNV
    by_contra hcon
    push Not at hcon
    obtain ⟨hN1, hN2⟩ := hcon
    have hcardN : Nat.card N = 2 := by
      have hdvd : Nat.card N ∣ 2 ^ 2 := by
        have h1 := Subgroup.card_dvd_of_le hNV
        rw [IsKleinFour.card_four (G := V.map (QuotientGroup.mk' W))] at h1
        exact h1
      obtain ⟨k, hk, hk'⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd
      interval_cases k
      · exact absurd (Subgroup.eq_bot_of_card_eq N (by rw [hk']; rfl)) hN1
      · rw [hk']
        rfl
      · exfalso
        apply hN2
        apply Subgroup.eq_of_le_of_card_ge hNV
        rw [hk', IsKleinFour.card_four (G := V.map (QuotientGroup.mk' W))]
        norm_num
    obtain ⟨⟨n, hnN⟩, hn1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hN1
    have hn1' : n ≠ 1 := fun h => hn1 (Subtype.ext h)
    have hn2 : n ^ 2 = 1 := by
      have h1 := IsKleinFour.mul_self (⟨n, hNV hnN⟩ : V.map (QuotientGroup.mk' W))
      rw [pow_two]
      exact congrArg Subtype.val h1
    have hnord : orderOf n = 2 := orderOf_eq_prime hn2 hn1'
    have hNz : N = Subgroup.zpowers n := by
      symm
      apply Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hnN)
      rw [hcardN, Nat.card_zpowers, hnord]
    have hfix : ∀ q : H ⧸ W, q * n * q⁻¹ = n := by
      intro q
      have hmem := hNn.conj_mem n hnN q
      rw [hNz] at hmem
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hmem
      have hn2' : n ^ (2 : ℤ) = 1 := by rw [zpow_two, ← pow_two, hn2]
      have hnk : n ^ k = n ^ (k % 2) := by
        conv_lhs => rw [← Int.emod_add_mul_ediv k 2]
        rw [zpow_add, zpow_mul, hn2', one_zpow, mul_one]
      rcases Int.emod_two_eq_zero_or_one k with h0 | h1
      · exfalso
        rw [hnk, h0, zpow_zero] at hk
        apply hn1'
        calc n = q⁻¹ * (q * n * q⁻¹) * q := by group
          _ = 1 := by rw [← hk]; group
      · rw [← hk, hnk, h1, zpow_one]
    obtain ⟨v, hvV, hvn⟩ := hNV hnN
    have hv1 : v ≠ 1 := fun h => hn1' (by rw [← hvn, h, map_one])
    obtain ⟨h, hh⟩ := hnocentral v hvV hv1
    apply hh
    have h1 := hfix (h : H ⧸ W)
    rw [← hvn] at h1
    have h2 : h * v * h⁻¹ * v⁻¹ ∈ W := by
      rw [← QuotientGroup.eq_one_iff]
      simp only [QuotientGroup.mk_mul, QuotientGroup.mk_inv]
      change ((h : H ⧸ W) * (QuotientGroup.mk' W v) * (h : H ⧸ W)⁻¹) * (QuotientGroup.mk' W v)⁻¹
        = 1
      rw [h1, mul_inv_cancel]
    have h3 : h * v * h⁻¹ * v⁻¹ ∈ V :=
      Subgroup.mul_mem _ (Subgroup.Normal.conj_mem inferInstance v hvV h) (Subgroup.inv_mem _ hvV)
    have h4 : h * v * h⁻¹ * v⁻¹ ∈ V ⊓ W := ⟨h3, h2⟩
    rw [hVW, Subgroup.mem_bot] at h4
    calc h * v * h⁻¹ = h * v * h⁻¹ * v⁻¹ * v := by group
      _ = v := by rw [h4, one_mul]
  obtain ⟨ρ, hρinj, -, -, -⟩ := normal_four_self_centralizing_affine_action
    (V.map (QuotientGroup.mk' W)) hminX hcentX
  have hXcard : Nat.card (H ⧸ W) = 24 := by
    have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup W
    rw [hH, hW] at h1
    omega
  have hperm : Nat.card (Equiv.Perm (V.map (QuotientGroup.mk' W))) = 24 := by
    rw [Nat.card_perm, IsKleinFour.card_four]
    rfl
  have hρbij : Function.Bijective ρ := hρinj.bijective_of_nat_card_le (by rw [hXcard, hperm])
  let eF : V.map (QuotientGroup.mk' W) ≃ Fin 4 := Finite.equivFinOfCardEq IsKleinFour.card_four
  let τ : H ⧸ W ≃* Equiv.Perm (Fin 4) := (MulEquiv.ofBijective ρ hρbij).trans eF.permCongrHom
  refine ⟨τ, fun q => ?_⟩
  have hKbar : ((Subgroup.centralizer (W : Set H)).map (QuotientGroup.mk' W)).index = 2 := by
    rw [Subgroup.index_map_eq _ (QuotientGroup.mk'_surjective W)
      (by rw [QuotientGroup.ker_mk']; exact hWK), hindex]
  have hτK : ((Subgroup.centralizer (W : Set H)).map (QuotientGroup.mk' W)).map
      τ.toMonoidHom = alternatingGroup (Fin 4) := by
    apply Equiv.Perm.eq_alternatingGroup_of_index_eq_two
    rw [Subgroup.index_map_eq _ τ.surjective (by
      rw [(MonoidHom.ker_eq_bot_iff _).mpr τ.injective]
      exact bot_le), hKbar]
  rw [← hτK]
  exact (Subgroup.mem_map_iff_mem τ.injective).symm

end OrderOneTwenty

open scoped Classical in
theorem order_one_twenty_four_by_five_local_principal_block_involution_sum
    {H : Type u} [Group H] [Fintype H] (hH : Nat.card H = 120)
    (V W : Subgroup H) [V.Normal] [W.Normal] [IsKleinFour V] [IsCyclic W] (hW : Nat.card W = 5)
    (hCV : Subgroup.centralizer (V : Set H) = V ⊔ W)
    (hindex : (Subgroup.centralizer (W : Set H)).index = 2)
    (basis : FiniteIrreducibleCharacterBasis H) (ideal : Ideal ComplexAlgebraicIntegers)
    [ideal.IsMaximal] [CharP (ComplexAlgebraicIntegers ⧸ ideal) 5] (principal : basis.index)
    (hprincipal : (basis.representation principal).character = 1) :
    (∃ τ : H ⧸ W ≃* Equiv.Perm (Fin 4), ∀ q : H ⧸ W,
      q ∈ (Subgroup.centralizer (W : Set H)).map (QuotientGroup.mk' W) ↔
        τ q ∈ alternatingGroup (Fin 4)) ∧
    Nat.card {x : H // x ∈ Subgroup.centralizer (W : Set H) ∧ orderOf x = 2} = 3 ∧
    Nat.card {x : H // x ∉ Subgroup.centralizer (W : Set H) ∧ orderOf x = 2} = 30 ∧
    ∀ w ∈ W, w ≠ 1 →
      ∑ θ ∈ coefficientBlock basis (localizedComplexIntegerRing ideal) principal,
        ((Nat.card H : ℂ)⁻¹ * ∑ x ∈ Finset.univ.filter (fun x : H => orderOf x = 2),
          (basis.representation θ).character x) ^ 2 * (basis.representation θ).character w /
            (basis.representation θ).character 1 = 1 / 8 := by
  have hWK : W ≤ Subgroup.centralizer (W : Set H) := CyclicInversion.le_centralizer_of_isCyclic W
  obtain ⟨τ, hτ⟩ := OrderOneTwenty.exists_quotient_equiv_perm hH V W hW hCV hWK hindex
  let σH : H →* Equiv.Perm (Fin 4) := τ.toMonoidHom.comp (QuotientGroup.mk' W)
  have hσsurj : Function.Surjective σH := τ.surjective.comp (QuotientGroup.mk'_surjective W)
  have hσker : ∀ h, σH h = 1 ↔ h ∈ W := fun h => by
    change τ (h : H ⧸ W) = 1 ↔ h ∈ W
    rw [MulEquiv.map_eq_one_iff, QuotientGroup.eq_one_iff]
  have hσK : ∀ h, h ∈ Subgroup.centralizer (W : Set H) ↔
      σH h ∈ alternatingGroup (Fin 4) := fun h => by
    rw [← CyclicAlternatingFive.mk_mem_centralizerImage_iff W hWK h]
    exact hτ (h : H ⧸ W)
  have hodd : Odd (Nat.card W) := by
    rw [hW]
    decide
  have hp5 : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have hrel : (Subgroup.centralizer (W : Set H)).relIndex (Subgroup.normalizer (W : Set H)) =
      2 := by
    rw [Subgroup.normalizer_eq_top (H := W), Subgroup.relIndex_top_right]
    exact hindex
  have hinv : ∀ h, h ∉ Subgroup.centralizer (W : Set H) → ∀ w ∈ W, h * w * h⁻¹ = w⁻¹ :=
    fun h hh w hw => CyclicInversion.inverts_of_mem_normalizer (p := 5) W (by norm_num) 1
      (by rw [hW, pow_one]) hrel h (by rw [Subgroup.normalizer_eq_top (H := W)]; trivial) hh w hw
  have hinner := CyclicAlternatingFive.card_inner_involutions W σH hodd hWK hσsurj hσker hσK
  rw [CyclicSymmetricFour.nat_card_alternating_involutions] at hinner
  have houter := CyclicAlternatingFive.card_outer_involutions W σH hodd hWK hinv hσsurj hσker
    hσK
  rw [CyclicSymmetricFour.nat_card_odd_involutions, hW] at houter
  refine ⟨⟨τ, hτ⟩, hinner, houter, ?_⟩
  intro w hw hw1
  have hsyl : Nat.card W = 5 ^ (Nat.card H).factorization 5 := by
    rw [hH, hW, show (120 : ℕ) = 5 * 24 by norm_num,
      Nat.factorization_mul (by norm_num) (by norm_num), Finsupp.add_apply,
      Nat.Prime.factorization_self (by norm_num),
      Nat.factorization_eq_zero_of_not_dvd (by norm_num), add_zero, pow_one]
  obtain ⟨S, rfl⟩ : ∃ S : Sylow 5 H, (S : Subgroup H) = W := ⟨Sylow.ofCard W hsyl, rfl⟩
  have hmain := (normal_prime_inversion_principal_block_involution_sum basis ideal 5 le_rfl
    principal hprincipal S inferInstance hW hindex).1 w hw hw1
  have hb : (Finset.univ.filter fun x : H =>
      x ∉ Subgroup.centralizer (S : Set H) ∧ orderOf x = 2).card = 30 := by
    rw [CyclicSymmetricFour.card_filter_eq_nat_card]
    exact houter
  rw [hmain, hb, hH]
  norm_num

end CFSG.Semidihedral.Principal
