module

public import CFSG.CharacterTheory.Semidihedral.FixedCoreNontrivialEqualParameterData
public import CFSG.CharacterTheory.Semidihedral.FixedCoreNontrivialEqualParameterGeneric
public import CFSG.CharacterTheory.Semidihedral.FixedCoreNontrivialOddComplement
public import CFSG.CharacterTheory.Semidihedral.FixedCoreNontrivialCore
public import CFSG.GroupTheory.ABGLocalTools.Basic

public section

namespace CFSG.Semidihedral.FixedCoreNontrivial

open CFSG.Open CFSG.Semidihedral CFSG.Semidihedral.ActualSimpleLayerLocalPackage
open CFSG.ComponentClassification.CatalogueSchreierLinearTwo
open CFSG.ABGLocalTools (IsSylowOf)

theorem exists_sylow_eq_of_card {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {X : Subgroup G} (hX : IsPGroup p X)
    {n : ℕ} (hsyl : ∀ T : Sylow p G, Nat.card T = n) (hXn : Nat.card X = n) :
    ∃ T : Sylow p G, (T : Subgroup G) = X := by
  obtain ⟨T, hT⟩ := hX.exists_le_sylow
  exact ⟨T, (Subgroup.eq_of_le_of_card_ge hT (by rw [hsyl T, hXn])).symm⟩

theorem EqualParameterData.false_of_card_sylow_of_facts {G : Type} [Group G] [Finite G]
    {t s₀ d d₁ : G} {J : Subgroup G} {p f : ℕ} {F : Type} [Field F] [Finite F]
    {κ : C t →* Equiv.Perm (Omega F)} {F' : Type} [Field F'] [Finite F']
    {φ : torusH G t s₀ ⧸ CFSG.pPrimeCore 2 (torusH G t s₀) ≃* CFSG.GorensteinWalter.PGL2 F'}
    (h : EqualParameterData G t s₀ d d₁ J p f F κ F' φ)
    (hsyl : ∀ T : Sylow p G, Nat.card T = p ^ f)
    (hCfacts : ∀ {Q₁ : Subgroup G}, IsSylowOf p Q₁ (C t) →
      Nat.card Q₁ = p ^ f ∧ Q₁ ≤ J ∧ (∀ x ∈ Q₁, ∀ y ∈ Q₁, x * y = y * x) ∧
      C t ⊓ Subgroup.centralizer (Q₁ : Set G) =
        Q₁ ⊔ (N t).map (C t).subtype ⊔ Subgroup.zpowers t ∧
      Nat.card (C t ⊓ Subgroup.normalizer (Q₁ : Set G) : Subgroup G) =
        2 * Nat.card ((N t).map (C t).subtype) * p ^ f * (p ^ f - 1))
    (hfour : Nat.card (Subgroup.centralizer
        ((Subgroup.zpowers t ⊔ Subgroup.zpowers s₀ : Subgroup G) : Set G)) =
      4 * Nat.card (torusW G t s₀) ∧
      ∀ T X : Subgroup G, IsKleinFour T → IsPGroup p X → X ≤ Subgroup.centralizer (T : Set G) →
        X = ⊥)
    (hHfacts : ∀ {P : Subgroup G}, IsSylowOf p P (torusH G t s₀) →
      Nat.card P = p ^ f ∧ P ≤ torusK G t s₀ ∧
        torusH G t s₀ ⊓ Subgroup.centralizer (P : Set G) = P ⊔ torusW G t s₀) :
    False := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hp := h.prime
  have : Fact p.Prime := ⟨hp⟩
  have hpodd := h.odd
  have hL := h.localData
  set B : Subgroup G := (N t).map (C t).subtype with hBdef
  set W : Subgroup G := torusW G t s₀ with hWdef
  set H : Subgroup G := torusH G t s₀ with hHdef
  obtain ⟨-, hWcard, -, -, -, -, -, -, -, -, hNW, -⟩ := h.clauses
  have hq1 : 1 < p ^ f := Nat.one_lt_pow (by have := h.one_le; omega) hp.one_lt
  have hW2 : 2 * (Nat.card W : ℤ) = ((p ^ f : ℕ) : ℤ) + (if p ^ f % 4 = 1 then 1 else -1) := by
    have hqodd : Odd (p ^ f) := hpodd.pow
    obtain ⟨k, hk⟩ := hqodd
    rw [hWcard]
    split_ifs with h4
    · rw [show ((p ^ f : ℕ) : ℤ) + 1 = 2 * ((k : ℤ) + 1) by push_cast [hk]; ring,
        Int.mul_ediv_cancel_left _ (by norm_num)]
    · rw [show ((p ^ f : ℕ) : ℤ) + -1 = 2 * (k : ℤ) by push_cast [hk]; ring,
        Int.mul_ediv_cancel_left _ (by norm_num)]
  have hWp : Nat.Coprime (Nat.card W) p := by
    refine (Nat.Prime.coprime_iff_not_dvd hp).mpr ?_ |>.symm
    intro hd
    have h1 : (p : ℤ) ∣ 2 * (Nat.card W : ℤ) :=
      dvd_mul_of_dvd_right (Int.natCast_dvd_natCast.mpr hd) 2
    rw [hW2] at h1
    have h2 : (p : ℤ) ∣ ((p ^ f : ℕ) : ℤ) := by
      exact_mod_cast dvd_pow_self p (by have := h.one_le; omega)
    have h3 := (dvd_add_right h2).mp h1
    have h4 : (p : ℤ) ∣ 1 := by
      split_ifs at h3
      · exact h3
      · exact (dvd_neg).mp h3
    have := Int.eq_one_of_dvd_one (by positivity) h4
    have := hp.one_lt
    omega
  have hWodd : Odd (Nat.card W) := by
    have hqodd : Odd (p ^ f) := hpodd.pow
    obtain ⟨k, hk⟩ := hqodd
    have h1 := hW2
    split_ifs at h1 with h4
    · exact ⟨k / 2, by
        have : (Nat.card W : ℤ) = k + 1 := by push_cast [hk] at h1; linarith
        have h5 : p ^ f % 4 = 1 := h4
        omega⟩
    · exact ⟨k / 2, by
        have : (Nat.card W : ℤ) = k := by push_cast [hk] at h1; linarith
        have h5 : p ^ f % 4 ≠ 1 := h4
        omega⟩
  have hW1 : W ≠ ⊥ := by
    intro hbot
    have h1 : Nat.card W = 1 := by rw [hbot]; exact Subgroup.card_bot
    rw [h1] at hW2
    have := h.q_gt
    split_ifs at hW2 <;> omega
  let P₀ : Sylow p H := default
  set P : Subgroup G := (P₀ : Subgroup H).map H.subtype with hPdef
  have hPsyl : IsSylowOf p P H := ⟨P₀, rfl⟩
  obtain ⟨hPcard, hPK, hHP⟩ := hHfacts hPsyl
  have hPp : IsPGroup p P := P₀.isPGroup'.map _
  let Q₀ : Sylow p (C t) := default
  set Q₁ : Subgroup G := (Q₀ : Subgroup (C t)).map (C t).subtype with hQ₁def
  have hQsyl : IsSylowOf p Q₁ (C t) := ⟨Q₀, rfl⟩
  obtain ⟨hQcard, hQJ, -, hCQ, -⟩ := hCfacts hQsyl
  have hQp : IsPGroup p Q₁ := Q₀.isPGroup'.map _
  have hQC : Q₁ ≤ C t := Subgroup.map_subtype_le _
  obtain ⟨TP, hTP⟩ := exists_sylow_eq_of_card hPp hsyl hPcard
  obtain ⟨TQ, hTQ⟩ := exists_sylow_eq_of_card hQp hsyl hQcard
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G TQ TP
  have hPmem : ∀ x : G, x ∈ P ↔ g⁻¹ * x * g ∈ Q₁ := by
    intro x
    rw [← hTP, ← hg, Sylow.coe_subgroup_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem,
      ← hTQ]
    simp [MulAut.smul_def, MulAut.inv_def, MulAut.conj_symm_apply]
  have hQmem : ∀ y ∈ Q₁, g * y * g⁻¹ ∈ P := by
    intro y hy
    rw [hPmem]
    simpa [mul_assoc] using hy
  set u : G := g * t * g⁻¹ with hudef
  have ht2 : orderOf t = 2 := hL.t_orderOf
  have hu2 : orderOf u = 2 := by rw [hudef, ← MulAut.conj_apply, MulEquiv.orderOf_eq, ht2]
  set Fc : Subgroup G := Subgroup.centralizer (P : Set G) with hFcdef
  have huF : u ∈ Fc := by
    rw [hFcdef, Subgroup.mem_centralizer_iff]
    intro x hx
    have hy : g⁻¹ * x * g ∈ Q₁ := (hPmem x).mp hx
    have hyt : (g⁻¹ * x * g) * t = t * (g⁻¹ * x * g) :=
      Subgroup.mem_centralizer_singleton_iff.mp (hQC hy)
    calc x * u = g * ((g⁻¹ * x * g) * t) * g⁻¹ := by rw [hudef]; group
      _ = g * (t * (g⁻¹ * x * g)) * g⁻¹ := by rw [hyt]
      _ = u * x := by rw [hudef]; group
  have hQodd : ∀ y ∈ Q₁, Odd (orderOf y) := by
    intro y hy
    obtain ⟨k, hk⟩ := hQp ⟨y, hy⟩
    have h1 : y ^ p ^ k = 1 := by simpa using congrArg Subtype.val hk
    exact (hpodd.pow (n := k)).of_dvd_nat (orderOf_dvd_of_pow_eq_one h1)
  have htwo : ∀ x ∈ Q₁ ⊔ B ⊔ Subgroup.zpowers t, ∀ k : ℕ, x ^ 2 ^ k = 1 →
      x ∈ Subgroup.zpowers t := by
    intro x hx k hk
    have hcomm1 : ∀ m ∈ Q₁ ⊔ B, ∀ c ∈ Subgroup.zpowers t, m * c = c * m := by
      intro m hm c hc
      have hmC : m ∈ C t := sup_le (hQC) hL.B_le hm
      obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hc
      exact (Commute.zpow_right (Subgroup.mem_centralizer_singleton_iff.mp hmC) i)
    obtain ⟨m, hm, c, hc, rfl⟩ := exists_mul_of_mem_sup hcomm1 hx
    have hcomm2 : ∀ a ∈ Q₁, ∀ b ∈ B, a * b = b * a := fun a ha b hb => hL.JB_comm a (hQJ ha) b hb
    obtain ⟨a, ha, b, hb, rfl⟩ := exists_mul_of_mem_sup hcomm2 hm
    have hmodd : Odd (orderOf (a * b)) :=
      odd_orderOf_mul_of_commute (hcomm2 a ha b hb) (hQodd a ha) (hL.B_odd b hb)
    have hmc : Commute (a * b) c := hcomm1 _ hm c hc
    have h1 : (a * b) ^ 2 ^ k = (c ^ 2 ^ k)⁻¹ := by
      rw [hmc.mul_pow] at hk
      exact eq_inv_of_mul_eq_one_left hk
    have h2 : (a * b) ^ 2 ^ k ∈ Subgroup.zpowers t := by
      rw [h1]
      exact Subgroup.inv_mem _ (Subgroup.pow_mem _ hc _)
    have h3 : (a * b) ^ 2 ^ k = 1 := by
      rcases zpowers_cases_of_mul_self hL.t_sq _ h2 with h4 | h4
      · exact h4
      · exfalso
        have h5 : Odd (orderOf ((a * b) ^ 2 ^ k)) :=
          hmodd.of_dvd_nat (orderOf_pow_dvd _)
        rw [h4, ht2] at h5
        exact absurd h5 (by decide)
    have h4 : a * b = 1 := by
      have h5 := orderOf_dvd_of_pow_eq_one h3
      have h6 : Nat.Coprime (orderOf (a * b)) (2 ^ k) :=
        Nat.Coprime.pow_right k (Nat.coprime_two_right.mpr hmodd)
      exact orderOf_eq_one_iff.mp (Nat.Coprime.eq_one_of_dvd h6 h5)
    rw [h4, one_mul]
    exact hc
  set u' : Fc := ⟨u, huF⟩ with hu'def
  have hZ : IsPGroup 2 (Subgroup.zpowers u') :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, Subgroup.orderOf_mk, hu2, pow_one])
  obtain ⟨S, hS⟩ := hZ.exists_le_sylow
  set S' : Subgroup G := (S : Subgroup Fc).map Fc.subtype with hS'def
  have hS'2 : IsPGroup 2 S' := S.isPGroup'.map _
  have huS' : u ∈ S' := ⟨u', hS (Subgroup.mem_zpowers u'), rfl⟩
  have hS'F : S' ≤ Fc := Subgroup.map_subtype_le _
  have hPne : P ≠ ⊥ := by
    intro hbot
    have h1 : Nat.card P = 1 := by rw [hbot]; exact Subgroup.card_bot
    omega
  have hno4 : ∀ T : Subgroup G, T ≤ S' → ¬ IsKleinFour T := by
    intro T hTS hT
    apply hPne
    refine hfour.2 T P hT hPp fun x hx => ?_
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    have hyF : y ∈ Fc := hS'F (hTS hy)
    exact (Subgroup.mem_centralizer_iff.mp hyF x hx).symm
  have hS'u := le_centralizer_of_isPGroup_two_of_no_kleinFour hS'2 hno4 huS' hu2
  have hS'z : S' ≤ Subgroup.zpowers u := by
    intro s hs
    have hsu : s * u = u * s := Subgroup.mem_centralizer_singleton_iff.mp (hS'u hs)
    have hsF : s ∈ Fc := hS'F hs
    have hyC : g⁻¹ * s * g ∈ C t := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      calc g⁻¹ * s * g * t = g⁻¹ * (s * u) * g := by rw [hudef]; group
        _ = g⁻¹ * (u * s) * g := by rw [hsu]
        _ = t * (g⁻¹ * s * g) := by rw [hudef]; group
    have hyQ : g⁻¹ * s * g ∈ Subgroup.centralizer (Q₁ : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      have hgy := hQmem y hy
      have h1 : g * y * g⁻¹ * s = s * (g * y * g⁻¹) :=
        Subgroup.mem_centralizer_iff.mp hsF _ hgy
      calc y * (g⁻¹ * s * g) = g⁻¹ * (g * y * g⁻¹ * s) * g := by group
        _ = g⁻¹ * (s * (g * y * g⁻¹)) * g := by rw [h1]
        _ = g⁻¹ * s * g * y := by group
    have hymem : g⁻¹ * s * g ∈ Q₁ ⊔ B ⊔ Subgroup.zpowers t := by
      rw [← hCQ]
      exact ⟨hyC, hyQ⟩
    obtain ⟨k, hk⟩ := hS'2 ⟨s, hs⟩
    have hsk : s ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
    have hyk : (g⁻¹ * s * g) ^ 2 ^ k = 1 := by
      have h1 : g⁻¹ * s * g = g⁻¹ * s * g⁻¹⁻¹ := by rw [inv_inv]
      rw [h1, conj_pow, hsk, mul_one, mul_inv_cancel]
    have hyt := htwo _ hymem k hyk
    obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.mp hyt
    refine Subgroup.mem_zpowers_iff.mpr ⟨i, ?_⟩
    rw [hudef, conj_zpow, hi]
    group
  have hS'cyc : IsCyclic S' :=
    isCyclic_of_surjective (Subgroup.subgroupOfEquivOfLe hS'z).toMonoidHom
      (Subgroup.subgroupOfEquivOfLe hS'z).surjective
  have hScyc : IsCyclic (S : Subgroup Fc) :=
    isCyclic_of_surjective ((S : Subgroup Fc).equivMapOfInjective Fc.subtype
      Fc.subtype_injective).symm.toMonoidHom (MulEquiv.surjective _)
  obtain ⟨hFq, hFodd⟩ := odd_mem_pPrimeCore_of_isCyclic_sylow S hScyc
  set R : Subgroup G := (CFSG.pPrimeCore 2 Fc).map Fc.subtype with hRdef
  have hRF : R ≤ Fc := Subgroup.map_subtype_le _
  have hRodd : Odd (Nat.card R) := by
    rw [hRdef, Subgroup.card_map_of_injective Fc.subtype_injective]
    exact Nat.coprime_two_left.mp (CFSG.pPrimeCore_coprime_card (p := 2) (G := Fc))
  have hWF : W ≤ Fc := by
    intro w hw
    rw [hFcdef, Subgroup.mem_centralizer_iff]
    intro x hx
    exact (Subgroup.mem_centralizer_iff.mp (hPK hx) w hw).symm
  have hWR : W ≤ R := fun w hw => hFodd w (hWF hw) (hL.W_odd w hw)
  have hWH : W ≤ H := by
    intro w hw
    have hwC : w ∈ Subgroup.centralizer (W : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      exact hL.W_comm y hy w hw
    exact Subgroup.centralizer_le_normalizer _ hwC
  have hFH : Fc ⊓ H = P ⊔ W := by rw [inf_comm]; exact hHP
  have hdisj : Disjoint W P := by
    rw [Subgroup.disjoint_def]
    intro x hxW hxP
    obtain ⟨k, hk⟩ := hPp ⟨x, hxP⟩
    have h1 : x ^ p ^ k = 1 := by simpa using congrArg Subtype.val hk
    have h2 : orderOf x ∣ p ^ k := orderOf_dvd_of_pow_eq_one h1
    have h3 : orderOf x ∣ Nat.card W := Subgroup.orderOf_dvd_natCard W hxW
    have h4 : Nat.Coprime (Nat.card W) (p ^ k) := Nat.Coprime.pow_right k hWp
    exact orderOf_eq_one_iff.mp (Nat.Coprime.eq_one_of_dvd (Nat.Coprime.coprime_dvd_left h3 h4) h2)
  have hPN : P ≤ Subgroup.normalizer (W : Set G) :=
    hPK.trans (Subgroup.centralizer_le_normalizer _)
  have hPW : Nat.card (P ⊔ W : Subgroup G) = p ^ f * Nat.card W := by
    rw [sup_comm, CFSG.GorensteinWalter.card_sup_eq_mul_of_disjoint_of_le_normalizer W P hPN hdisj,
      hPcard, mul_comm]
  have hRH : R ⊓ H ≤ P ⊔ W := hFH ▸ inf_le_inf_right H hRF
  have hWRH : W ≤ R ⊓ H := le_inf hWR hWH
  have hWPW : W ≤ P ⊔ W := le_sup_right
  have hrel : W.relIndex (P ⊔ W) = p ^ f := by
    have h1 := (W.subgroupOf (P ⊔ W)).card_mul_index
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hWPW).toEquiv, hPW] at h1
    have hW0 : 0 < Nat.card W := Nat.card_pos
    change Nat.card W * W.relIndex (P ⊔ W) = p ^ f * Nat.card W at h1
    exact Nat.eq_of_mul_eq_mul_left hW0 (by linarith)
  have hHall : Nat.Coprime (Nat.card W) (W.relIndex (R ⊓ H)) := by
    have h1 := Subgroup.relIndex_mul_relIndex W (R ⊓ H) (P ⊔ W) hWRH hRH
    rw [hrel] at h1
    exact Nat.Coprime.coprime_dvd_right (Dvd.intro _ h1) (Nat.Coprime.pow_right f hWp)
  obtain ⟨hHallR, -⟩ := odd_subgroup_torus_hall_normal_complement h.clauses R hRodd hWR hHall
  have hW1' : Nat.card W ≠ 1 := fun h1 => hW1 (Subgroup.card_eq_one.mp h1)
  obtain ⟨r, hr, hrW⟩ := Nat.exists_prime_and_dvd hW1'
  have : Fact r.Prime := ⟨hr⟩
  have hr2 : r ≠ 2 := by
    rintro rfl
    exact (Nat.not_even_iff_odd.mpr hWodd) (even_iff_two_dvd.mpr hrW)
  let Wr₀ : Sylow r W := default
  set Wr : Subgroup G := (Wr₀ : Subgroup W).map W.subtype with hWrdef
  have hWrW : Wr ≤ W := Subgroup.map_subtype_le _
  have hWrne : Wr ≠ ⊥ := by
    intro hbot
    exact Wr₀.ne_bot_of_dvd_card hrW
      ((Subgroup.map_eq_bot_iff_of_injective _ W.subtype_injective).mp hbot)
  have hWrp : IsPGroup r Wr := Wr₀.isPGroup'.map _
  have hWrF : Wr ≤ Fc := hWrW.trans hWF
  have hidx : ¬ r ∣ (Wr.subgroupOf Fc).index := by
    change ¬ r ∣ Wr.relIndex Fc
    rw [← Subgroup.relIndex_mul_relIndex Wr W Fc hWrW hWF,
      ← Subgroup.relIndex_mul_relIndex W R Fc hWR hRF]
    intro hd
    rcases (Nat.Prime.dvd_mul hr).mp hd with h1 | h1
    · apply Wr₀.not_dvd_index
      have h2 : Wr.relIndex W = (Wr₀ : Subgroup W).index := by
        rw [Subgroup.relIndex, hWrdef, Subgroup.subgroupOf,
          Subgroup.comap_map_eq_self_of_injective W.subtype_injective]
      rwa [← h2]
    · rcases (Nat.Prime.dvd_mul hr).mp h1 with h2 | h2
      · exact hr.not_dvd_one (by rw [← Nat.Coprime.gcd_eq_one hHallR]; exact Nat.dvd_gcd hrW h2)
      · have h3 : R.relIndex Fc = Nat.card (Fc ⧸ CFSG.pPrimeCore 2 Fc) := by
          rw [Subgroup.relIndex, hRdef, Subgroup.subgroupOf,
            Subgroup.comap_map_eq_self_of_injective Fc.subtype_injective]
          rfl
        rw [h3] at h2
        obtain ⟨n, hn⟩ := hFq.exists_card_eq
        rw [hn] at h2
        have h4 := (Nat.prime_dvd_prime_iff_eq hr Nat.prime_two).mp (hr.dvd_of_dvd_pow h2)
        exact hr2 h4
  have hWrFp : IsPGroup r (Wr.subgroupOf Fc) :=
    hWrp.of_equiv (Subgroup.subgroupOfEquivOfLe hWrF).symm
  let Tr : Sylow r Fc := hWrFp.toSylow hidx
  have hTr : (Tr : Subgroup Fc) = Wr.subgroupOf Fc := IsPGroup.toSylow_coe hWrFp hidx
  have hTrN : (Tr : Subgroup Fc) ≤ CFSG.pPrimeCore 2 Fc := by
    intro x hx
    rw [hTr, Subgroup.mem_subgroupOf] at hx
    obtain ⟨y, hy, hyx⟩ := hWR (hWrW hx)
    have hyx' : y = x := Subtype.ext hyx
    rw [← hyx']
    exact hy
  have htop := Sylow.normalizer_sup_eq_top' Tr hTrN
  have hu'top := Subgroup.mem_top u'
  rw [← htop] at hu'top
  have hu'mem : u' ∈ ((Subgroup.normalizer ((Tr : Subgroup Fc) : Set Fc) ⊔
      CFSG.pPrimeCore 2 Fc : Subgroup Fc) : Set Fc) := hu'top
  rw [Subgroup.mul_normal] at hu'mem
  obtain ⟨n, hn, o, ho, hno⟩ := hu'mem
  have hu'2 : orderOf u' = 2 := by rw [hu'def, Subgroup.orderOf_mk, hu2]
  have hu'N : u' ∉ CFSG.pPrimeCore 2 Fc := by
    intro hmem
    have h1 := Subgroup.orderOf_dvd_natCard _ hmem
    rw [hu'2] at h1
    have h2 := Nat.coprime_two_left.mp (CFSG.pPrimeCore_coprime_card (p := 2) (G := Fc))
    exact (Nat.not_even_iff_odd.mpr h2) (even_iff_two_dvd.mpr h1)
  have hπu : (QuotientGroup.mk' (CFSG.pPrimeCore 2 Fc)) u' =
      (QuotientGroup.mk' (CFSG.pPrimeCore 2 Fc)) n := by
    have ho1 : (QuotientGroup.mk' (CFSG.pPrimeCore 2 Fc)) o = 1 :=
      (QuotientGroup.eq_one_iff o).mpr ho
    rw [← hno, map_mul, ho1, mul_one]
  have hπu1 : (QuotientGroup.mk' (CFSG.pPrimeCore 2 Fc)) u' ≠ 1 := fun h1 =>
    hu'N ((QuotientGroup.eq_one_iff u').mp h1)
  have hπu2 : (QuotientGroup.mk' (CFSG.pPrimeCore 2 Fc)) u' ^ 2 = 1 := by
    rw [← map_pow, ← hu'2, pow_orderOf_eq_one, map_one]
  have hπn : orderOf ((QuotientGroup.mk' (CFSG.pPrimeCore 2 Fc)) n) = 2 := by
    rw [← hπu]
    exact orderOf_eq_prime hπu2 hπu1
  have h2n : 2 ∣ orderOf n := hπn ▸ orderOf_map_dvd _ n
  have hn0 : orderOf n / 2 ≠ 0 := by
    have := Nat.le_of_dvd (orderOf_pos n) h2n
    omega
  have hv2 : orderOf (n ^ (orderOf n / 2)) = 2 := by
    rw [orderOf_pow_of_dvd hn0 (Nat.div_dvd_of_dvd h2n), Nat.div_div_self h2n (orderOf_pos n).ne']
  have hvN : n ^ (orderOf n / 2) ∈ Subgroup.normalizer ((Tr : Subgroup Fc) : Set Fc) :=
    Subgroup.pow_mem _ hn _
  have hvWr : ((n ^ (orderOf n / 2) : Fc) : G) ∈ Subgroup.normalizer (Wr : Set G) := by
    apply mem_normalizer_of_conj_mem
    intro w hw
    have hwF : w ∈ Fc := hWrF hw
    have h1 : (⟨w, hwF⟩ : Fc) ∈ (Tr : Subgroup Fc) := by
      rw [hTr]
      exact hw
    have h2 := (Subgroup.mem_normalizer_iff.mp hvN _).mp h1
    rw [hTr, Subgroup.mem_subgroupOf] at h2
    exact h2
  have hvH : ((n ^ (orderOf n / 2) : Fc) : G) ∈ H := (hNW Wr hWrW hWrne).le hvWr
  have hvPW : ((n ^ (orderOf n / 2) : Fc) : G) ∈ P ⊔ W := by
    rw [← hFH]
    exact ⟨(n ^ (orderOf n / 2)).2, hvH⟩
  have hPWodd : Odd (Nat.card (P ⊔ W : Subgroup G)) := by
    rw [hPW]
    exact (hpodd.pow).mul hWodd
  have hvodd := hPWodd.of_dvd_nat (Subgroup.orderOf_dvd_natCard _ hvPW)
  rw [Subgroup.orderOf_coe, hv2] at hvodd
  exact absurd hvodd (by decide)

end CFSG.Semidihedral.FixedCoreNontrivial
