module

public import CFSG.Quasithin.Vol2.Ch5Sec1L34Lem519
public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch5StatementsB
public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch5StatementsS331

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin
open scoped Pointwise commutatorElement

theorem stmt5_1_19_of_inputs_F4 (h513 : Stmt5_1_3_F4) (h515 : Stmt5_1_15_F4) (h516 : Stmt5_1_16_F4)
    (h518 : Stmt5_1_18_F4) (h5114 : Stmt5_1_14_first_F4) (hF : L2TorusFact)
    (hOrth : OrthTorusFixFact) (hA9 : L34AutNoNineFact) : Stmt5_1_19_F4 := by
  intro G _ _ T M L V H B D n hyp hN hV hK hnot D₃ hD₃ h3
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hh := hyp.toHyp5_0_1
  obtain ⟨hDcyc, hDcard⟩ := hh.isCyclic_card_of_isHall hF hN.2.1
  by_cases hD₃M : D₃ ≤ Subgroup.normalizer (oTwoUpper H : Set G)
  swap
  · rcases h515 G T M L V H B D n hyp hN hV hK with h1 | h2 | h3' | h4
    · exact absurd (hD₃.trans h1) hD₃M
    · exact Or.inl ⟨hD₃M, Or.inl h2⟩
    · exact Or.inl ⟨hD₃M, Or.inr h3'⟩
    · exact Or.inr (Or.inl ⟨h4.1, h4.2.1, hD₃M⟩)

  obtain ⟨hD₃B, hZD₃⟩ := h518 G T M L V H B D n hyp hN hV hK D₃ hD₃ h3 hD₃M
  have hZL : quasithinOmegaOneCenter T ⊓ Subgroup.centralizer (L : Set G) = ⊥ :=
    (h5114 G T M L V H B D n hyp hN hV hK).2.2
  have hDB : n = 2 → D = B := by
    intro hn2
    rw [← hD₃B]
    refine (Subgroup.eq_of_le_of_card_ge hD₃ ?_).symm
    rw [hDcard, h3, hn2]
    norm_num
  obtain ⟨d, hdD₃, hd1⟩ := exists_ne_one_of_card_prime Nat.prime_three h3
  have hd3 := pow_three_of_mem_of_card_three h3 hdD₃
  have hdD : d ∈ D := hD₃ hdD₃
  have hdBorel : d ∈ borelL T L := hN.2.1.1 hdD
  have hdL : d ∈ L := hdBorel.1
  have hdfix : ∀ z ∈ quasithinOmegaOneCenter T, d * z * d⁻¹ = z := by
    intro z hz
    have hzC : z ∈ Subgroup.centralizer (D₃ : Set G) :=
      Subgroup.commutator_eq_bot_iff_le_centralizer.mp hZD₃ hz
    rw [Subgroup.mem_centralizer_iff.mp hzC d hdD₃, mul_assoc, mul_inv_cancel, mul_one]
  have hred := hV.isTwoReducedIn
  have hT2 : IsPGroup 2 T := hh.sylow.1
  have hVT : V ≤ T := hh.V_le_T hV
  have hTV : T ≤ Subgroup.normalizer (V : Set G) := le_sup_right.trans hred.2.1
  have hLV : L ≤ Subgroup.normalizer (V : Set G) := le_sup_left.trans hred.2.1
  have hVne : V ≠ ⊥ := by
    intro hb
    apply hV.2.2
    rw [hb, eq_bot_iff, Subgroup.commutator_le]
    intro v hv l _
    rw [Subgroup.mem_bot] at hv ⊢
    rw [hv]
    simp
  obtain ⟨z, hzV, hz1, hzZ⟩ := exists_mem_omegaOneCenter hT2 hred.2.2.1 le_rfl hVT hTV hVne
  rcases h513 G T M L V n hh hV with hc1 | hc2 | hc3 | hc4 | hc5
  ·
    exfalso
    obtain ⟨W₁, W₂, hLW₁, hLW₂, hinf, hsup, hN₁, hN₂⟩ := hc1
    have hW₂N : W₂ ≤ Subgroup.normalizer (W₁ : Set G) := by
      intro y hy
      apply mem_normalizer_of_forall_conj_mem'
      intro x hx
      have hxV : x ∈ V := hsup ▸ Subgroup.mem_sup_left hx
      have hyV : y ∈ V := hsup ▸ Subgroup.mem_sup_right hy
      rw [comm_of_mem_of_isElemAbelian hred.2.2.1 hyV hxV, mul_assoc, mul_inv_cancel, mul_one]
      exact hx
    have hset : ((W₁ ⊔ W₂ : Subgroup G) : Set G) = (W₁ : Set G) * (W₂ : Set G) :=
      Subgroup.coe_mul_of_right_le_normalizer_left _ _ hW₂N
    have hzm : z ∈ (W₁ : Set G) * (W₂ : Set G) := by
      rw [← hset, hsup]
      exact hzV
    obtain ⟨w₁, hw₁, w₂, hw₂, rfl⟩ := Set.mem_mul.mp hzm
    have hc₁ : d * w₁ * d⁻¹ ∈ W₁ := (Subgroup.mem_normalizer_iff.mp (hLW₁ hdL) w₁).mp hw₁
    have hc₂ : d * w₂ * d⁻¹ ∈ W₂ := (Subgroup.mem_normalizer_iff.mp (hLW₂ hdL) w₂).mp hw₂
    have hprod : (d * w₁ * d⁻¹) * (d * w₂ * d⁻¹) = w₁ * w₂ := by
      rw [← hdfix _ hzZ]
      group

    have hu : (w₁⁻¹ * (d * w₁ * d⁻¹)) = w₂ * (d * w₂ * d⁻¹)⁻¹ := by
      have e : w₁⁻¹ * (d * w₁ * d⁻¹) * (d * w₂ * d⁻¹) = w₂ := by
        rw [mul_assoc, hprod]
        group
      exact eq_mul_inv_of_mul_eq e
    have hmem : w₁⁻¹ * (d * w₁ * d⁻¹) ∈ W₁ ⊓ W₂ :=
      ⟨W₁.mul_mem (W₁.inv_mem hw₁) hc₁, hu ▸ W₂.mul_mem hw₂ (W₂.inv_mem hc₂)⟩
    rw [hinf, Subgroup.mem_bot] at hmem
    have hfix₁ : d * w₁ * d⁻¹ = w₁ := by
      have := congrArg (w₁ * ·) hmem
      simpa using this
    have hfix₂ : d * w₂ * d⁻¹ = w₂ := by
      rw [hmem] at hu
      have := congrArg (· * (d * w₂ * d⁻¹)) hu
      simp only [one_mul, inv_mul_cancel_right] at this
      exact this
    by_cases hw₁1 : w₁ = 1
    · have hw₂1 : w₂ ≠ 1 := by
        intro hw
        apply hz1
        rw [hw₁1, hw, one_mul]
      exact hh.conj_ne_of_isNatModCh5 hN₂ hdL hd3 hd1 hw₂ hw₂1 hfix₂
    · exact hh.conj_ne_of_isNatModCh5 hN₁ hdL hd3 hd1 hw₁ hw₁1 hfix₁
  ·
    exfalso
    exact hnot ⟨hc2.1, Or.inl ⟨hc2.2.1, Or.inr hc2.2.2⟩, hDB hc2.1⟩
  ·
    exfalso
    set W := ⁅V, L⁆ with hWdef
    have hWV : W ≤ V := by
      rw [hWdef, Subgroup.commutator_le]
      intro v hv l hl
      have : l * v⁻¹ * l⁻¹ ∈ V :=
        (Subgroup.mem_normalizer_iff.mp (hLV hl) v⁻¹).mp (V.inv_mem hv)
      have e : ⁅v, l⁆ = v * (l * v⁻¹ * l⁻¹) := by
        simp [commutatorElement_def, mul_assoc]
      rw [e]
      exact V.mul_mem hv this
    have hTW : T ≤ Subgroup.normalizer (W : Set G) :=
      le_normalizer_commutator_of hTV hh.T_le_normalizer
    have hTC : T ≤ Subgroup.normalizer
        ((W ⊓ Subgroup.centralizer (L : Set G) : Subgroup G) : Set G) := by
      intro t ht
      apply mem_normalizer_of_forall_conj_mem'
      intro c hc
      obtain ⟨hcW, hcL⟩ := Subgroup.mem_inf.mp hc
      refine Subgroup.mem_inf.mpr ⟨(Subgroup.mem_normalizer_iff.mp (hTW ht) c).mp hcW, ?_⟩
      rw [Subgroup.mem_centralizer_iff]
      intro l hl
      have hl' : t⁻¹ * l * t ∈ L := by
        have := (Subgroup.mem_normalizer_iff.mp (hh.T_le_normalizer (T.inv_mem ht)) l).mp hl
        simpa using this
      have hcomm := Subgroup.mem_centralizer_iff.mp hcL _ hl'
      calc l * (t * c * t⁻¹) = t * ((t⁻¹ * l * t) * c) * t⁻¹ := by group
        _ = t * (c * (t⁻¹ * l * t)) * t⁻¹ := by rw [hcomm]
        _ = t * c * t⁻¹ * l := by group
    have hC : W ⊓ Subgroup.centralizer (L : Set G) = ⊥ := by
      by_contra hne
      obtain ⟨c, hc, hc1, hcZ⟩ :=
        exists_mem_omegaOneCenter hT2 hred.2.2.1 (inf_le_left.trans hWV) hVT hTC hne
      have : c ∈ quasithinOmegaOneCenter T ⊓ Subgroup.centralizer (L : Set G) := ⟨hcZ, hc.2⟩
      rw [hZL, Subgroup.mem_bot] at this
      exact hc1 this
    have hWnat := isNatModCh5_of_isNatQuotCh5 hc3 hC
    obtain ⟨z', hz'W, hz'1, hz'Z⟩ :=
      exists_mem_omegaOneCenter hT2 hred.2.2.1 hWV hVT hTW hV.2.2
    exact hh.conj_ne_of_isNatModCh5 hWnat hdL hd3 hd1 hz'W hz'1 (hdfix z' hz'Z)
  ·
    obtain ⟨m, hnm, -⟩ := id hc4
    by_cases hn2 : n = 2
    · exfalso
      exact hnot ⟨hn2, Or.inr (hn2 ▸ hc4), hDB hn2⟩
    have h2n := hh.two_le

    have hmodd : ¬ Even m := by
      intro hme
      have hS : IsSylowTwoOf (T ⊓ L) L :=
        A4.isSylowTwoOf_inf_normal (hh.isSylowTwoOf le_sup_right) le_sup_left
          hh.sup_le_normalizer
      have hCV : IsPGroup 2 ↥(L ⊓ Subgroup.centralizer (V : Set G)) :=
        (pCoreOf_isPGroup 2 L).to_le (hh.inf_centralizer_le hLV hV.2.2)
      have hord : orderOf d = 3 := orderOf_eq_prime hd3 hd1
      have hzC : z ∈ Subgroup.centralizer ((T ⊓ L : Subgroup G) : Set G) :=
        Subgroup.centralizer_le (fun x hx => hx.1)
          (quasithinOmegaOneCenter_le_inf T hzZ).2
      exact hz1 (hOrth G L V (T ⊓ L) m d z (hnm ▸ hc4) hme hS hCV hdBorel hord hzV hzC
        (hdfix z hzZ))
    have hmod : n % 4 = 2 := by
      rcases Nat.even_or_odd m with hme | ⟨k, hk⟩
      · exact absurd hme hmodd
      · omega
    have hgt : 2 < n := by omega

    have hDM : D ≤ Subgroup.normalizer (oTwoUpper H : Set G) := by
      rcases h515 G T M L V H B D n hyp hN hV hK with h1 | h2 | h3' | h4
      · exact h1
      · exact absurd h2.1 hn2
      · exfalso; rcases h3'.1 with h | h <;> omega
      · exfalso; rcases h4.1 with h | h <;> omega

    have h3n : ¬ 3 ∣ n := by
      intro h3n
      have h6 : 2 * 3 ∣ n :=
        Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num : Nat.Coprime 2 3) (by omega) h3n
      obtain ⟨k, hk⟩ := h6
      have h9 : 9 ∣ Nat.card D := by
        rw [hDcard, hk, show 2 * 3 * k = 6 * k by ring, pow_mul]
        have h63 : 2 ^ 6 - 1 ∣ (2 ^ 6) ^ k - 1 ^ k := Nat.sub_dvd_pow_sub_pow _ _ k
        rw [one_pow] at h63
        exact (show 9 ∣ 2 ^ 6 - 1 by norm_num).trans h63
      obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := ↥D)
      have hgord : orderOf g = Nat.card D := orderOf_eq_card_of_forall_mem_zpowers hg
      have hg0 : orderOf g ≠ 0 := by
        rw [hgord]
        exact Nat.card_pos.ne'
      set x := g ^ (orderOf g / 9) with hxdef
      have hxord : orderOf x = 9 := orderOf_pow_orderOf_div hg0 (hgord ▸ h9)
      have hxM : (x : G) ∈ Subgroup.normalizer (oTwoUpper H : Set G) := hDM x.2
      let y : ↥(Subgroup.normalizer (oTwoUpper H : Set G)) := ⟨x, hxM⟩
      have hy9 : quotConjAut (oTwoUpper H) y ^ 9 = 1 := by
        rw [← map_pow]
        have : y ^ 9 = 1 := by
          apply Subtype.ext
          simp only [y, Subgroup.coe_pow, Subgroup.coe_one]
          have := pow_orderOf_eq_one x
          rw [hxord] at this
          exact congrArg Subtype.val this
        rw [this, map_one]
      have hy3 := hA9 _ hK _ hy9
      rw [← map_pow] at hy3
      have hmem := mem_centralizerModO2_of_quotConjAut_eq_one hy3
      have hx3 : orderOf ((x : G) ^ 3) = 3 := by
        rw [orderOf_pow' _ (by norm_num), Subgroup.orderOf_coe, hxord]
        norm_num
      have hdvd : 3 ∣ Nat.card ↥(centralizerModO2 (oTwoUpper H)) := by
        have := orderOf_dvd_natCard (⟨(x : G) ^ 3, by simpa [y] using hmem⟩ :
          ↥(centralizerModO2 (oTwoUpper H)))
        rwa [Subgroup.orderOf_mk, hx3] at this
      exact (h516 G T M L V H B D n hyp hN hV hK).1 hdvd
    exact Or.inr (Or.inr ⟨hmod, hgt, h3n, hD₃B, hD₃M, hc4⟩)
  ·
    exfalso
    obtain ⟨⟨-, hsplit⟩, hS5, hmod⟩ := hc5
    have hn2 := hh.n_eq_two_of_isBarS5 hV hS5
    have hCV : V ⊓ Subgroup.centralizer ((L ⊔ T : Subgroup G) : Set G) = ⊥ := by
      rw [eq_bot_iff]
      rintro c ⟨hcV, hcC⟩
      have hcT : c ∈ Subgroup.centralizer (T : Set G) :=
        Subgroup.centralizer_le (fun x hx => Subgroup.mem_sup_right hx) hcC
      have hcL : c ∈ Subgroup.centralizer (L : Set G) :=
        Subgroup.centralizer_le (fun x hx => Subgroup.mem_sup_left hx) hcC
      have hcZ : c ∈ quasithinOmegaOneCenter T :=
        mem_quasithinOmegaOneCenter_iff.mpr ⟨hVT hcV, hcT, hred.2.2.1.2 c hcV⟩
      have : c ∈ quasithinOmegaOneCenter T ⊓ Subgroup.centralizer (L : Set G) := ⟨hcZ, hcL⟩
      rwa [hZL] at this
    rw [hCV, sup_bot_eq] at hsplit
    rw [hsplit] at hmod
    exact hnot ⟨hn2, Or.inl ⟨hS5, Or.inl hmod⟩, hDB hn2⟩

end CFSG.Quasithin.H13
