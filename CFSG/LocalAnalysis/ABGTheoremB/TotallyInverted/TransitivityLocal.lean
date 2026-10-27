module

public import CFSG.LocalAnalysis.ABGTheoremB.TotallyInverted.TransitivityBasic
public import CFSG.GroupTheory.ABGDGroups.WreathedDGroups
public import CFSG.GroupTheory.QuasiDihedralFusion.SemidihedralModel
public import CFSG.LocalAnalysis.ABGTheoremB.Facts
public import CFSG.LocalAnalysis.ABGTheoremB.TotallyInverted.TransitivityInputs

public section

namespace CFSG.ABGTheoremB.TotallyInverted.Sec10

open CFSG.QuasiDihedralFusion CFSG.ABGLocalTools
open scoped Pointwise

variable {G : Type} [Group G] [Finite G] {σ : Setting G} {r : ℕ}

theorem fact_prime (Δ : Data σ r) : Fact r.Prime := ⟨Δ.prime⟩

theorem odd_r (Δ : Data σ r) : Odd r := Δ.prime.odd_of_ne_two Δ.ne_two

theorem Ps_zero_ne_bot (Δ : Data σ r) : σ.Ps r 0 ≠ ⊥ := by
  have := fact_prime Δ
  intro h
  have hcard := Δ.P_sylow.card_eq
  rw [h, Subgroup.card_bot] at hcard
  have hpos : 0 < (Nat.card σ.ON).factorization r :=
    (Δ.prime.dvd_iff_one_le_factorization Nat.card_pos.ne').mp Δ.dvd
  have := Nat.one_lt_pow hpos.ne' Δ.prime.one_lt
  omega

omit [Finite G] in
theorem conjSub_oddCoreIn {H : Subgroup G} {h : G} (hh : h ∈ H) :
    conjSub h (oddCoreIn H) = oddCoreIn H :=
  conjSub_eq_self (le_normalizer_oddCoreIn H hh)

omit [Finite G] in
theorem mem_normalizer_sup {X Y : Subgroup G} {g : G}
    (hX : g ∈ Subgroup.normalizer (X : Set G)) (hY : g ∈ Subgroup.normalizer (Y : Set G)) :
    g ∈ Subgroup.normalizer ((X ⊔ Y : Subgroup G) : Set G) := by
  rw [le_normalizer_iff_conjSub, conjSub_sup, conjSub_eq_self hX, conjSub_eq_self hY]

theorem odd_card_of_maximals {H X : Subgroup G} (Δ : Data σ r)
    (hX : X ∈ maximals (signalizersPerm H σ.T σ.C r)) : Odd (Nat.card X) := by
  have := fact_prime Δ
  exact odd_card_of_isPGroup (odd_r Δ) (mem_signalizersPerm_iff.mp hX.1).2.1

theorem exists_conj_of_le_sup_oddCoreIn (hσ : σ.IsValid) {Δ : Data σ r} (homni : Omnibus Δ)
    {H X Y : Subgroup G} (hCH : σ.C ≤ H) (hO : oddCoreIn H ≠ ⊥)
    (hX : X ∈ maximals (signalizersPerm H σ.T σ.C r))
    (hY : Y ∈ maximals (signalizersPerm H σ.T σ.C r)) (hYX : Y ≤ X ⊔ oddCoreIn H) :
    ∃ c ∈ σ.C, conjSub c X = Y := by
  have := fact_prime Δ
  have hXO := homni H hCH X hX
  obtain ⟨m, -, hm⟩ := hXO.part_iv hO Y hY
  obtain ⟨R₀, hR₀, hR₀X⟩ := hXO.part_ii_b
  obtain ⟨hXH, hXp, hTX, -, -⟩ := mem_signalizersPerm_iff.mp hX.1
  obtain ⟨-, hYp, hTY, -, -⟩ := mem_signalizersPerm_iff.mp hY.1
  set O := oddCoreIn H with hOdef
  have hXN : X ≤ Subgroup.normalizer (O : Set G) := hXH.trans (le_normalizer_oddCoreIn H)
  have hcard := card_sup_mul_card_inf hXN
  have hXOs : IsSylowOf r (X ⊓ O) O := by
    have := hR₀.eq_of_le (le_inf hR₀X hR₀.le) inf_le_right (hXp.to_le inf_le_left)
    rw [this]
    exact hR₀
  have hXodd : Odd (Nat.card X) := odd_card_of_isPGroup (odd_r Δ) hXp
  have hKodd : Odd (Nat.card (X ⊔ O : Subgroup G)) :=
    (hXodd.mul (odd_card_oddCoreIn H)).of_dvd_nat (card_sup_dvd hXN)
  have hTK : σ.T ≤ Subgroup.normalizer ((X ⊔ O : Subgroup G) : Set G) := fun t ht =>
    mem_normalizer_sup (hTX ht) (le_normalizer_oddCoreIn H (hCH (σ.T_le_C hσ ht)))
  have hXK : IsSylowOf r X (X ⊔ O) := by
    rw [isSylowOf_iff]
    refine ⟨le_sup_left, hXp, ?_⟩
    have h1 := Subgroup.relIndex_mul_card X (X ⊔ O)
    have h2 := Subgroup.relIndex_mul_card (X ⊓ O) O
    rw [inf_eq_left.mpr le_sup_left] at h1
    rw [inf_eq_left.mpr inf_le_right] at h2
    have hpos : 0 < Nat.card X * Nat.card (X ⊓ O : Subgroup G) :=
      Nat.mul_pos Nat.card_pos Nat.card_pos
    have heq : X.relIndex (X ⊔ O) = (X ⊓ O).relIndex O := by
      apply Nat.eq_of_mul_eq_mul_right hpos
      calc X.relIndex (X ⊔ O) * (Nat.card X * Nat.card (X ⊓ O : Subgroup G))
          = Nat.card (X ⊔ O : Subgroup G) * Nat.card (X ⊓ O : Subgroup G) := by rw [← h1]; ring
        _ = Nat.card X * Nat.card O := hcard
        _ = (X ⊓ O).relIndex O * (Nat.card X * Nat.card (X ⊓ O : Subgroup G)) := by
            rw [← h2]; ring
    rw [heq]
    exact (isSylowOf_iff.mp hXOs).2.2
  have hYK : IsSylowOf r Y (X ⊔ O) := by
    apply isSylowOf_of_card hYX
    rw [← hXK.card_eq, ← hm, card_conjSub]
  have hT4 : Nat.card σ.T = 4 := (T_isKleinFour hσ).card_four
  obtain ⟨c, hc, hcXY⟩ := exists_conjSub_eq_of_isSylowOf hT4 hKodd hTK hXK hYK hTX hTY
  exact ⟨c, hc.2, hcXY⟩

@[expose] def OddInvariantInCore (σ : Setting G) (H : Subgroup G) : Prop :=
  ∀ Z : Subgroup G, Z ≤ H → Odd (Nat.card Z) → σ.T ≤ Subgroup.normalizer (Z : Set G) →
    Z ≤ oddCoreIn H

@[expose] def CentralInvolutionFusion (σ : Setting G) (H : Subgroup G) : Prop :=
  ∃ z ∈ σ.T, z ≠ 1 ∧ (∀ h ∈ H, h * z * h⁻¹ * z⁻¹ ∈ oddCoreIn H) ∧
    ∀ t ∈ σ.T, t ≠ 1 → t ≠ z → ∃ h ∈ H, h * t * h⁻¹ = t * z

theorem oddInvariantInCore_of_conjSub {H : Subgroup G} {m : G}
    (hm : m ∈ Subgroup.normalizer ((σ.T : Subgroup G) : Set G))
    (h : OddInvariantInCore σ (conjSub m H)) : OddInvariantInCore σ H := by
  intro Z hZH hZ hTZ
  have hT : conjSub m σ.T = σ.T := conjSub_eq_self hm
  have hle := h (conjSub m Z) (conjSub_mono hZH) (by rwa [card_conjSub]) (by
    intro t ht
    rw [← hT, mem_conjSub] at ht
    rw [le_normalizer_iff_conjSub, ← conjSub_mul, show t * m = m * (m⁻¹ * t * m) by group,
      conjSub_mul, conjSub_eq_self (hTZ ht)])
  rwa [oddCoreIn_conjSub, conjSub_le_conjSub_iff] at hle

theorem centralInvolutionFusion_of_conjSub {H : Subgroup G} {m : G}
    (hm : m ∈ Subgroup.normalizer ((σ.T : Subgroup G) : Set G))
    (h : CentralInvolutionFusion σ (conjSub m H)) : CentralInvolutionFusion σ H := by
  obtain ⟨z, hz, hz1, hzc, hzf⟩ := h
  have hT : conjSub m σ.T = σ.T := conjSub_eq_self hm
  have hzT : m⁻¹ * z * m ∈ σ.T := by rw [← hT, mem_conjSub] at hz; exact hz
  refine ⟨m⁻¹ * z * m, hzT, fun h1 => hz1 ?_, fun h hh => ?_, fun t ht ht1 htz => ?_⟩
  · calc z = m * (m⁻¹ * z * m) * m⁻¹ := by group
      _ = 1 := by rw [h1]; group
  · have := hzc (m * h * m⁻¹) (conj_mem_conjSub hh)
    rw [oddCoreIn_conjSub, mem_conjSub] at this
    convert this using 1
    group
  · have htT : m * t * m⁻¹ ∈ σ.T := by rw [← hT]; exact conj_mem_conjSub ht
    obtain ⟨h', hh', hh't⟩ := hzf (m * t * m⁻¹) htT
      (fun h1 => ht1 (by
        calc t = m⁻¹ * (m * t * m⁻¹) * m := by group
          _ = 1 := by rw [h1]; group))
      (fun h1 => htz (by rw [← h1]; group))
    rw [mem_conjSub] at hh'
    refine ⟨m⁻¹ * h' * m, hh', ?_⟩
    calc m⁻¹ * h' * m * t * (m⁻¹ * h' * m)⁻¹ = m⁻¹ * (h' * (m * t * m⁻¹) * h'⁻¹) * m := by
          group
      _ = t * (m⁻¹ * z * m) := by rw [hh't]; group

omit [Finite G] in
theorem exists_isSylowOf_ge {p : ℕ} [Fact p.Prime] {K A : Subgroup G} (hAK : A ≤ K)
    (hA : IsPGroup p A) : ∃ B : Subgroup G, IsSylowOf p B K ∧ A ≤ B := by
  have hA' : IsPGroup p (A.subgroupOf K) := hA.comap_subtype
  obtain ⟨Q, hQ⟩ := hA'.exists_le_sylow
  refine ⟨(Q : Subgroup K).map K.subtype, ⟨Q, rfl⟩, fun a ha => ?_⟩
  exact ⟨⟨a, hAK ha⟩, hQ ha, rfl⟩

theorem exists_mem_conjSub_eq {p : ℕ} [Fact p.Prime] {K A B : Subgroup G}
    (hA : IsSylowOf p A K) (hB : IsSylowOf p B K) : ∃ k ∈ K, conjSub k A = B := by
  obtain ⟨QA, rfl⟩ := hA
  obtain ⟨QB, rfl⟩ := hB
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq K QA QB
  refine ⟨g, g.2, ?_⟩
  rw [← hg, Sylow.coe_subgroup_smul, Subgroup.pointwise_smul_def]
  change ((QA : Subgroup K).map K.subtype).map (MulAut.conj (g : G)).toMonoidHom =
    ((QA : Subgroup K).map (MulAut.conj g).toMonoidHom).map K.subtype
  rw [Subgroup.map_map, Subgroup.map_map]
  congr 1

theorem isSylowOf_top_of_card {p : ℕ} [Fact p.Prime] {X : Subgroup G} (P : Sylow p G)
    (h : Nat.card X = Nat.card (P : Subgroup G)) : IsSylowOf p X ⊤ := by
  apply isSylowOf_of_card le_top
  rw [h, Sylow.card_eq_multiplicity, Subgroup.card_top]

omit [Finite G] in
theorem isKleinFour_conjSub {T₂ : Subgroup G} (hT₂ : IsKleinFour T₂) (g : G) :
    IsKleinFour (conjSub g T₂) :=
  ⟨by rw [card_conjSub]; exact hT₂.card_four,
    by rw [← Monoid.exponent_eq_of_mulEquiv (conjSubEquiv g T₂)]; exact hT₂.exponent_two⟩

omit [Finite G] in
theorem isKleinFour_subgroupOf {T₂ H : Subgroup G} (hT₂ : IsKleinFour T₂) (hT₂H : T₂ ≤ H) :
    IsKleinFour (T₂.subgroupOf H) := by
  refine ⟨?_, ?_⟩
  · rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hT₂H).toEquiv]
    exact hT₂.card_four
  · rw [Monoid.exponent_eq_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hT₂H)]
    exact hT₂.exponent_two

omit [Finite G] in
theorem odd_card_subgroupOf {Z H : Subgroup G} (hZH : Z ≤ H) (hZ : Odd (Nat.card Z)) :
    Odd (Nat.card (Z.subgroupOf H)) := by
  rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hZH).toEquiv]

omit [Finite G] in
theorem subgroupOf_le_normalizer {H A B : Subgroup G}
    (hAB : A ≤ Subgroup.normalizer (B : Set G)) :
    A.subgroupOf H ≤ Subgroup.normalizer ((B.subgroupOf H : Subgroup H) : Set H) := by
  intro a ha
  rw [Subgroup.mem_normalizer_iff]
  intro h
  simp only [Subgroup.mem_subgroupOf, Subgroup.coe_mul, Subgroup.coe_inv]
  exact (Subgroup.mem_normalizer_iff.mp (hAB ha)) h

omit [Finite G] in
theorem le_oddCoreIn_of_subgroupOf {H Z : Subgroup G} (hZH : Z ≤ H)
    (h : Z.subgroupOf H ≤ CFSG.oddCore H) : Z ≤ oddCoreIn H := fun z hz =>
  ⟨⟨z, hZH hz⟩, h hz, rfl⟩

theorem exists_three_element_of_three_dvd {K T₂ : Subgroup G} (hT₂K : T₂ ≤ K)
    (h3 : 3 ∣ automizerIndex (T₂.subgroupOf K)) :
    ∃ k ∈ K, k ∈ Subgroup.normalizer (T₂ : Set G) ∧
      k ∉ Subgroup.centralizer (T₂ : Set G) ∧ ∃ b : ℕ, k ^ (3 ^ b) = 1 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set T' := T₂.subgroupOf K
  set N' := Subgroup.normalizer (T' : Set K)
  set C' := Subgroup.centralizer (T' : Set K)
  obtain ⟨Q⟩ : Nonempty (Sylow 3 N') := inferInstance
  have hQ : ¬ (Q : Subgroup N') ≤ C'.subgroupOf N' := by
    intro hle
    apply Q.not_dvd_index
    exact h3.trans (Subgroup.index_dvd_of_le hle)
  obtain ⟨q, hqQ, hqC⟩ := IsConcreteLE.not_le_iff_exists.mp hQ
  obtain ⟨b, hb⟩ := Q.isPGroup' ⟨q, hqQ⟩
  refine ⟨((q : K) : G), (q : K).2, ?_, ?_, b, ?_⟩
  · rw [Subgroup.mem_normalizer_iff]
    intro g
    by_cases hg : g ∈ K
    · have := (Subgroup.mem_normalizer_iff.mp q.2) ⟨g, hg⟩
      simpa [T', Subgroup.mem_subgroupOf] using this
    · have h1 : g ∉ T₂ := fun h => hg (hT₂K h)
      have h2 : (q : G) * g * (q : G)⁻¹ ∉ T₂ := by
        intro h
        apply hg
        have := K.mul_mem (K.mul_mem (K.inv_mem (q : K).2) (hT₂K h)) (q : K).2
        simpa [mul_assoc] using this
      exact ⟨fun h => absurd h h1, fun h => absurd h h2⟩
  · intro hk
    apply hqC
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_centralizer_iff]
    intro t ht
    apply Subtype.ext
    exact (Subgroup.mem_centralizer_iff.mp hk) t ht
  · have := congrArg (fun y : Q => ((y : N') : K)) hb
    simpa using congrArg Subtype.val this

theorem conj_x_ne_of_three_element (hσ : σ.IsValid) {k : G}
    (hkN : k ∈ Subgroup.normalizer ((σ.T : Subgroup G) : Set G)) (hkC : k ∉ σ.C) {b : ℕ}
    (hkb : k ^ (3 ^ b) = 1) : k * σ.x * k⁻¹ ≠ σ.x := by
  intro hfix
  have hmemT : ∀ {t : G}, t ∈ σ.T → k * t * k⁻¹ ∈ σ.T := fun ht =>
    (Subgroup.mem_normalizer_iff.mp hkN _).mp ht
  have hx₂ := hmemT σ.x₂_mem_T
  have hne1 : k * σ.x₂ * k⁻¹ ≠ 1 := fun h => x₂_ne_one hσ (by
    calc σ.x₂ = k⁻¹ * (k * σ.x₂ * k⁻¹) * k := by group
      _ = 1 := by rw [h]; group)
  have hnex : k * σ.x₂ * k⁻¹ ≠ σ.x := fun h => hσ.x_ne_x₂ (by
    calc σ.x = k⁻¹ * (k * σ.x * k⁻¹) * k := by group
      _ = k⁻¹ * (k * σ.x₂ * k⁻¹) * k := by rw [hfix, h]
      _ = σ.x₂ := by group)
  have hC : ∀ {c : G}, c * σ.x * c⁻¹ = σ.x → c * σ.x₂ * c⁻¹ = σ.x₂ → c ∈ σ.C := by
    intro c h1 h2
    rw [mem_C_iff_commute_xs]
    have e1 : c * σ.x = σ.x * c := by
      calc c * σ.x = c * σ.x * c⁻¹ * c := by group
        _ = σ.x * c := by rw [h1]
    have e2 : c * σ.x₂ = σ.x₂ * c := by
      calc c * σ.x₂ = c * σ.x₂ * c⁻¹ * c := by group
        _ = σ.x₂ * c := by rw [h2]
    intro i
    fin_cases i
    · exact e1
    · exact e2
    · change c * (σ.x * σ.x₂) = σ.x * σ.x₂ * c
      rw [← mul_assoc, e1, mul_assoc, e2, mul_assoc]
  rcases (mem_T_iff hσ).mp hx₂ with h | h | h | h
  · exact hne1 h
  · exact hnex h
  · exact hkC (hC hfix h)
  ·
    have hk2x : k ^ 2 * σ.x * (k ^ 2)⁻¹ = σ.x := by
      calc k ^ 2 * σ.x * (k ^ 2)⁻¹ = k * (k * σ.x * k⁻¹) * k⁻¹ := by rw [pow_two]; group
        _ = σ.x := by rw [hfix, hfix]
    have hk2x₂ : k ^ 2 * σ.x₂ * (k ^ 2)⁻¹ = σ.x₂ := by
      calc k ^ 2 * σ.x₂ * (k ^ 2)⁻¹ = k * (k * σ.x₂ * k⁻¹) * k⁻¹ := by rw [pow_two]; group
        _ = k * (σ.x * σ.x₂) * k⁻¹ := by rw [h]; rfl
        _ = (k * σ.x * k⁻¹) * (k * σ.x₂ * k⁻¹) := by group
        _ = σ.x * (σ.x * σ.x₂) := by rw [hfix, h]; rfl
        _ = σ.x₂ := by rw [← mul_assoc, mul_self_of_orderOf_eq_two hσ.x_order, one_mul]
    have hk2 : k ^ 2 ∈ σ.C := hC hk2x hk2x₂
    apply hkC
    have hodd : Odd (3 ^ b) := Odd.pow (by decide)
    obtain ⟨m, hm⟩ := hodd
    have : k = (k ^ 2) ^ (m + 1) := by
      rw [← pow_mul, show 2 * (m + 1) = 3 ^ b + 1 by omega, pow_succ, hkb, one_mul]
    rw [this]
    exact σ.C.pow_mem hk2 _

theorem exists_hasSemidihedralSylow (hσ : σ.IsValid) (hheight : σ.height = 1) :
    ∃ n : ℕ, HasSemidihedralSylow G n := by
  rcases hσ.sylow with ⟨-, h⟩ | h
  · exact h
  · have := h.1
    omega

theorem exists_conjSub_eq_T (hσ : σ.IsValid) (hheight : σ.height = 1) {T₂ : Subgroup G}
    (hT₂ : IsKleinFour T₂) (hT₂N : T₂ ≤ σ.N) : ∃ v ∈ σ.N, conjSub v T₂ = σ.T := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨n, hn, hSD⟩ := exists_hasSemidihedralSylow hσ hheight
  have hSN : (σ.S : Subgroup G) ≤ σ.N := σ.S_le_N hσ
  have hS : IsSylowOf 2 (σ.S : Subgroup G) σ.N := ⟨σ.S.subtype hSN, by
    rw [Sylow.coe_subtype, Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hSN]⟩
  have hT₂p : IsPGroup 2 T₂ := IsPGroup.of_card (n := 2) (by rw [hT₂.card_four]; norm_num)
  obtain ⟨B, hB, hT₂B⟩ := exists_isSylowOf_ge hT₂N hT₂p
  obtain ⟨g, hgN, hgSB⟩ := exists_mem_conjSub_eq hS hB
  have hle : conjSub g⁻¹ T₂ ≤ σ.S := by
    rw [← conjSub_inv_conjSub g (σ.S : Subgroup G), hgSB]
    exact conjSub_mono hT₂B
  obtain ⟨f⟩ := hSD σ.S
  have := isKleinFour_conjSub hT₂ g⁻¹
  have := T_isKleinFour hσ
  obtain ⟨w, hwS, hw⟩ := exists_conj_eq_qdFour hn (σ.S : Subgroup G) f _ hle
  obtain ⟨w', hw'S, hw'⟩ := exists_conj_eq_qdFour hn (σ.S : Subgroup G) f _ (σ.T_le_S hσ)
  refine ⟨w' * w⁻¹ * g⁻¹, σ.N.mul_mem (σ.N.mul_mem (hSN hw'S) (σ.N.inv_mem (hSN hwS)))
    (σ.N.inv_mem hgN), ?_⟩
  rw [conjSub_mul, conjSub_mul, show conjSub g⁻¹ T₂ = conjSub w (qdFour (σ.S : Subgroup G) f)
    from hw, conjSub_inv_conjSub]
  exact hw'.symm

theorem mem_normalizer_T_of_perm (hσ : σ.IsValid) {g : G}
    (hg : ∀ i, ∃ j, g * σ.xs i * g⁻¹ = σ.xs j) (hg' : ∀ i, ∃ j, g⁻¹ * σ.xs i * g = σ.xs j) :
    g ∈ Subgroup.normalizer ((σ.T : Subgroup G) : Set G) := by
  have key : ∀ {g : G}, (∀ i, ∃ j, g * σ.xs i * g⁻¹ = σ.xs j) →
      ∀ t ∈ σ.T, g * t * g⁻¹ ∈ σ.T := by
    intro g hg t ht
    by_cases ht1 : t = 1
    · rw [ht1, mul_one, mul_inv_cancel]
      exact σ.T.one_mem
    obtain ⟨i, rfl⟩ := exists_xs_of_mem_T hσ ht ht1
    obtain ⟨j, hj⟩ := hg i
    rw [hj]
    exact xs_mem_T j
  rw [Subgroup.mem_normalizer_iff]
  intro t
  refine ⟨key hg t, fun ht => ?_⟩
  have := key (g := g⁻¹) (by simpa using hg') _ ht
  simpa [mul_assoc] using this

theorem M_le_normalizer_T (hσ : σ.IsValid) (Δ : Data σ r) :
    σ.M ≤ Subgroup.normalizer ((σ.T : Subgroup G) : Set G) := by
  rw [Δ.M_eq]
  refine sup_le (Subgroup.centralizer_le_normalizer _) (Subgroup.closure_le _ |>.mpr ?_)
  intro g hg
  rcases hg with rfl | rfl
  · exact Δ.d_mem.2
  · refine mem_normalizer_T_of_perm hσ (fun i => ⟨i + 1, Δ.a_cycle i⟩) fun i => ⟨i - 1, ?_⟩
    have h := Δ.a_cycle (i - 1)
    rw [sub_add_cancel] at h
    rw [← h]
    group

theorem hasWreathedSylow_of_height (hσ : σ.IsValid) (hh : σ.height ≠ 1) :
    HasWreathedSylow G σ.height := by
  rcases hσ.sylow with ⟨h, -⟩ | h
  · exact absurd h hh
  · exact h

theorem D_eq_S (hσ : σ.IsValid) (hh : σ.height ≠ 1) : σ.D = σ.S :=
  inf_eq_left.mpr (hσ.T_normal hh)

omit [Finite G] in
theorem two_pow_sq (n : ℕ) : (2 ^ n) ^ 2 = 4 ^ n := by
  rw [← pow_mul, mul_comm, pow_mul]
  norm_num

theorem card_S (hσ : σ.IsValid) (hh : σ.height ≠ 1) :
    Nat.card (σ.S : Subgroup G) = 2 * 4 ^ σ.height := by
  obtain ⟨e⟩ := (hasWreathedSylow_of_height hσ hh).2 σ.S
  rw [Nat.card_congr e.toEquiv, CFSG.Wreathed.card_wreath, two_pow_sq]

theorem conj_x₂_of_mem_S (hσ : σ.IsValid) (hh : σ.height ≠ 1) {s : G}
    (hs : s ∈ (σ.S : Subgroup G)) (hsC : s ∉ σ.C) : s * σ.x₂ * s⁻¹ = σ.x₃ := by
  have hsx : s * σ.x * s⁻¹ = σ.x := by
    rw [(Subgroup.mem_centralizer_iff.mp hσ.x_mem_center.2) s hs]
    group
  have hT := (Subgroup.mem_normalizer_iff.mp (hσ.T_normal hh hs) σ.x₂).mp σ.x₂_mem_T
  rcases (mem_T_iff hσ).mp hT with h | h | h | h
  · exact absurd (by
      calc σ.x₂ = s⁻¹ * (s * σ.x₂ * s⁻¹) * s := by group
        _ = 1 := by rw [h]; group) (x₂_ne_one hσ)
  · exact absurd (by
      calc σ.x = s⁻¹ * (s * σ.x * s⁻¹) * s := by group
        _ = s⁻¹ * (s * σ.x₂ * s⁻¹) * s := by rw [hsx, h]
        _ = σ.x₂ := by group) hσ.x_ne_x₂
  · exfalso
    apply hsC
    rw [mem_C_iff_commute_xs]
    have e1 : s * σ.x = σ.x * s := by
      calc s * σ.x = s * σ.x * s⁻¹ * s := by group
        _ = σ.x * s := by rw [hsx]
    have e2 : s * σ.x₂ = σ.x₂ * s := by
      calc s * σ.x₂ = s * σ.x₂ * s⁻¹ * s := by group
        _ = σ.x₂ * s := by rw [h]
    intro i
    fin_cases i
    · exact e1
    · exact e2
    · change s * (σ.x * σ.x₂) = σ.x * σ.x₂ * s
      rw [← mul_assoc, e1, mul_assoc, e2, mul_assoc]
  · exact h

omit [Finite G] in
theorem F₀_le_C : σ.F₀ ≤ σ.C := inf_le_right

theorem T_le_F₀ (hσ : σ.IsValid) : σ.T ≤ σ.F₀ := le_inf (σ.T_le_D hσ) (σ.T_le_C hσ)

theorem F₀_relIndex_S (hσ : σ.IsValid) (hh : σ.height ≠ 1) :
    σ.F₀.relIndex (σ.S : Subgroup G) = 2 := by
  have hDS := D_eq_S hσ hh
  have hmem : ∀ b : (σ.S : Subgroup G), b ∈ σ.F₀.subgroupOf σ.S ↔ (b : G) ∈ σ.C := by
    intro b
    rw [Subgroup.mem_subgroupOf]
    exact ⟨fun h => h.2, fun h => ⟨by rw [hDS]; exact b.2, h⟩⟩
  obtain ⟨s₀, hs₀S, hs₀C⟩ : ∃ s ∈ (σ.S : Subgroup G), s ∉ σ.C := by
    by_contra hcon
    push Not at hcon
    apply hσ.x_ne_x₂
    refine (hσ.center_involution σ.x₂ (Subgroup.mem_inf.mpr ⟨hσ.x₂_mem,
      Subgroup.mem_centralizer_iff.mpr ?_⟩) hσ.x₂_order).symm
    intro s hs
    exact (Subgroup.mem_centralizer_iff.mp (hcon s hs) σ.x₂ σ.x₂_mem_T).symm
  change (σ.F₀.subgroupOf σ.S).index = 2
  rw [Subgroup.index_eq_two_iff]
  refine ⟨⟨s₀, hs₀S⟩, fun b => ?_⟩
  rw [hmem, hmem]
  by_cases hb : (b : G) ∈ σ.C
  · refine Or.inr ⟨hb, fun h => hs₀C ?_⟩
    have := σ.C.mul_mem (σ.C.inv_mem hb) h
    simpa using this
  · refine Or.inl ⟨?_, hb⟩
    have h1 := conj_x₂_of_mem_S hσ hh b.2 hb
    have h2 := conj_x₂_of_mem_S hσ hh hs₀S hs₀C
    have hbx : (b : G) * σ.x * (b : G)⁻¹ = σ.x := by
      rw [(Subgroup.mem_centralizer_iff.mp hσ.x_mem_center.2) b b.2]
      group
    have hs₀x : s₀ * σ.x * s₀⁻¹ = σ.x := by
      rw [(Subgroup.mem_centralizer_iff.mp hσ.x_mem_center.2) s₀ hs₀S]
      group
    rw [mem_C_iff_commute_xs]
    have e1 : (b : G) * s₀ * σ.x = σ.x * ((b : G) * s₀) := by
      calc (b : G) * s₀ * σ.x = (b : G) * (s₀ * σ.x * s₀⁻¹) * (b : G)⁻¹ * ((b : G) * s₀) := by
            group
        _ = σ.x * ((b : G) * s₀) := by rw [hs₀x, hbx]
    have e2 : (b : G) * s₀ * σ.x₂ = σ.x₂ * ((b : G) * s₀) := by
      calc (b : G) * s₀ * σ.x₂ = (b : G) * (s₀ * σ.x₂ * s₀⁻¹) * (b : G)⁻¹ * ((b : G) * s₀) := by
            group
        _ = (b : G) * (σ.x * σ.x₂) * (b : G)⁻¹ * ((b : G) * s₀) := by rw [h2]; rfl
        _ = ((b : G) * σ.x * (b : G)⁻¹) * ((b : G) * σ.x₂ * (b : G)⁻¹) * ((b : G) * s₀) := by
            group
        _ = σ.x * (σ.x * σ.x₂) * ((b : G) * s₀) := by rw [hbx, h1]; rfl
        _ = σ.x₂ * ((b : G) * s₀) := by
            rw [← mul_assoc σ.x, mul_self_of_orderOf_eq_two hσ.x_order, one_mul]
    intro i
    fin_cases i
    · exact e1
    · exact e2
    · change (b : G) * s₀ * (σ.x * σ.x₂) = σ.x * σ.x₂ * ((b : G) * s₀)
      rw [← mul_assoc, e1, mul_assoc, e2, mul_assoc]

theorem card_F₀ (hσ : σ.IsValid) (hh : σ.height ≠ 1) : Nat.card σ.F₀ = 4 ^ σ.height := by
  have h := Subgroup.relIndex_mul_card σ.F₀ (σ.S : Subgroup G)
  rw [F₀_relIndex_S hσ hh, card_S hσ hh,
    inf_eq_left.mpr ((D_eq_S hσ hh) ▸ (inf_le_left : σ.F₀ ≤ σ.D))] at h
  omega

omit [Finite G] in
theorem nonempty_base_mulEquiv (m : ℕ) :
    Nonempty (CFSG.Wreathed.baseSubgroup m ≃*
      Multiplicative (ZMod m) × Multiplicative (ZMod m)) := by
  refine ⟨MulEquiv.mk' ((CFSG.Wreathed.baseCoordinateEquiv m).trans
    (Multiplicative.ofAdd.prodCongr Multiplicative.ofAdd)) fun x y => ?_⟩
  obtain ⟨⟨a, b⟩, rfl⟩ := (CFSG.Wreathed.baseCoordinateEquiv m).symm.surjective x
  obtain ⟨⟨c, d⟩, rfl⟩ := (CFSG.Wreathed.baseCoordinateEquiv m).symm.surjective y
  have hmul : (CFSG.Wreathed.baseCoordinateEquiv m).symm (a, b) *
      (CFSG.Wreathed.baseCoordinateEquiv m).symm (c, d) =
      (CFSG.Wreathed.baseCoordinateEquiv m).symm (a + c, b + d) :=
    Subtype.ext (CFSG.Wreathed.element_base_mul m a b c d 0)
  simp only [Equiv.trans_apply, hmul, Equiv.apply_symm_apply]
  rfl

omit [Finite G] in
theorem nonempty_homocyclic_of_le_wreath {S U : Subgroup G} {n : ℕ} (hn : 2 ≤ n)
    (e : S ≃* CFSG.Wreathed.Wreath (2 ^ n)) (hUS : U ≤ S) [IsMulCommutative U]
    (hcardU : Nat.card U = 4 ^ n) : Nonempty (U ≃* CFSG.RankTwoShapes.HomocyclicGroup n) := by
  have hbase : (U.subgroupOf S).map e.toMonoidHom = CFSG.Wreathed.baseSubgroup (2 ^ n) := by
    have h2n : 2 < 2 ^ n := by
      calc 2 < 2 ^ 2 := by norm_num
        _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
    apply CFSG.Wreathed.unique_abelian_index_two (2 ^ n) h2n
    · have := Subgroup.subgroupOf_isMulCommutative S U
      exact Subgroup.map_isMulCommutative _ _
    · have hc : Nat.card ((U.subgroupOf S).map e.toMonoidHom) = 4 ^ n := by
        rw [Subgroup.card_map_of_injective e.injective,
          Nat.card_congr (Subgroup.subgroupOfEquivOfLe hUS).toEquiv, hcardU]
      have h := ((U.subgroupOf S).map e.toMonoidHom).card_mul_index
      rw [hc, CFSG.Wreathed.card_wreath, two_pow_sq, mul_comm] at h
      exact Nat.eq_of_mul_eq_mul_right (by positivity) h
  exact ⟨(Subgroup.subgroupOfEquivOfLe hUS).symm.trans
    (((U.subgroupOf S).equivMapOfInjective e.toMonoidHom e.injective).trans
      ((MulEquiv.subgroupCongr hbase).trans (nonempty_base_mulEquiv (2 ^ n)).some))⟩

theorem nonempty_F₀_homocyclic (hσ : σ.IsValid) (Δ : Data σ r) (hh : σ.height ≠ 1) :
    Nonempty (σ.F₀ ≃* CFSG.RankTwoShapes.HomocyclicGroup σ.height) := by
  have hW := hasWreathedSylow_of_height hσ hh
  obtain ⟨e⟩ := hW.2 σ.S
  have : IsMulCommutative σ.F₀ :=
    ⟨⟨fun a b => Subtype.ext (Δ.F₀_abelian a a.2 b b.2)⟩⟩
  exact nonempty_homocyclic_of_le_wreath hW.1 e ((D_eq_S hσ hh) ▸ inf_le_left) (card_F₀ hσ hh)

omit [Finite G] in
theorem not_dihedral_of_wreath {X : Type*} [Group X] {m n : ℕ} (hn : 2 ≤ n)
    (e₁ : X ≃* DihedralGroup (2 ^ m)) (e₂ : X ≃* CFSG.Wreathed.Wreath (2 ^ n)) : False := by
  have f := e₁.symm.trans e₂
  have hcard : 2 * 2 ^ m = 2 * (2 ^ n) ^ 2 := by
    rw [← DihedralGroup.nat_card, ← CFSG.Wreathed.card_wreath, Nat.card_congr f.toEquiv]
  have hm : m = 2 * n := by
    have h1 : 2 ^ m = (2 ^ n) ^ 2 := Nat.eq_of_mul_eq_mul_left (by norm_num) hcard
    rw [← pow_mul, mul_comm] at h1
    exact Nat.pow_right_injective le_rfl h1
  have hord : orderOf (f (DihedralGroup.r 1)) = 2 ^ m := by
    rw [MulEquiv.orderOf_eq, DihedralGroup.orderOf_r_one]
  have hdvd : 2 ^ m ∣ 2 ^ (n + 1) := by
    rw [← hord, pow_succ']
    exact orderOf_dvd_of_pow_eq_one (CFSG.Wreathed.element_pow_twice_modulus _ _)
  have := (Nat.pow_dvd_pow_iff_le_right (by norm_num : 1 < 2)).mp hdvd
  omega

theorem le_normalizer_T_of_le_normalizer_F₀ (hσ : σ.IsValid) (Δ : Data σ r) {g : G}
    (hg : g ∈ Subgroup.normalizer ((σ.F₀ : Subgroup G) : Set G)) :
    g ∈ Subgroup.normalizer ((σ.T : Subgroup G) : Set G) := by
  have key : ∀ {g : G}, g ∈ Subgroup.normalizer ((σ.F₀ : Subgroup G) : Set G) →
      ∀ t ∈ σ.T, g * t * g⁻¹ ∈ σ.T := by
    intro g hg t ht
    apply Δ.F₀_omega
    · exact (Subgroup.mem_normalizer_iff.mp hg t).mp (T_le_F₀ hσ ht)
    · have := T_isKleinFour hσ
      rw [pow_two]
      calc g * t * g⁻¹ * (g * t * g⁻¹) = g * (t * t) * g⁻¹ := by group
        _ = 1 := by rw [kleinFour_mul_self ht]; group
  rw [Subgroup.mem_normalizer_iff]
  intro t
  refine ⟨key hg t, fun ht => ?_⟩
  have := key (Subgroup.inv_mem _ hg) _ ht
  simpa [mul_assoc] using this

theorem wreathed_cases (hσ : σ.IsValid) (hF : σ.ChapterIIFacts) (Δ : Data σ r)
    (hQ : QGroupFourFusion G) (hh : σ.height ≠ 1) {H : Subgroup G} (hCH : σ.C ≤ H)
    (hHtop : H ≠ ⊤) (hO : oddCoreIn H ≠ ⊥) :
    OddInvariantInCore σ H ∨ CentralInvolutionFusion σ H := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hW := hasWreathedSylow_of_height hσ hh
  have hn : 2 ≤ σ.height := hW.1
  have hF₀H : σ.F₀ ≤ H := F₀_le_C.trans hCH
  have hcardF₀ := card_F₀ hσ hh
  have hF₀p : IsPGroup 2 σ.F₀ :=
    IsPGroup.of_card (n := 2 * σ.height) (by rw [hcardF₀, pow_mul]; norm_num)
  obtain ⟨Ts, hTs, hF₀Ts⟩ := exists_isSylowOf_ge hF₀H hF₀p
  obtain ⟨a, ha⟩ := IsPGroup.iff_card.mp hTs.isPGroup
  have hle : Nat.card Ts ≤ Nat.card (σ.S : Subgroup G) := by
    obtain ⟨S', hS'⟩ := hTs.isPGroup.exists_le_sylow
    calc Nat.card Ts ≤ Nat.card (S' : Subgroup G) := Subgroup.card_le_of_le hS'
      _ = Nat.card (σ.S : Subgroup G) := by
          rw [Sylow.card_eq_multiplicity, Sylow.card_eq_multiplicity]
  have hdvd : 4 ^ σ.height ∣ Nat.card Ts := hcardF₀ ▸ Subgroup.card_dvd_of_le hF₀Ts
  rw [card_S hσ hh, ha] at hle
  rw [ha, show (4 : ℕ) ^ σ.height = 2 ^ (2 * σ.height) by rw [pow_mul]; norm_num] at hdvd
  have ha1 := (Nat.pow_dvd_pow_iff_le_right (by norm_num : 1 < 2)).mp hdvd
  have ha2 : a ≤ 2 * σ.height + 1 := by
    have : 2 ^ a ≤ 2 ^ (2 * σ.height + 1) := by
      rw [pow_succ, pow_mul]
      norm_num
      linarith
    exact (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).mp this
  have hT4 := (T_isKleinFour hσ).card_four
  have hTH : σ.T ≤ H := (σ.T_le_C hσ).trans hCH
  rcases (show a = 2 * σ.height ∨ a = 2 * σ.height + 1 by omega) with rfl | rfl
  ·
    left
    have hTsF₀ : σ.F₀ = Ts := Subgroup.eq_of_le_of_card_ge hF₀Ts (by
      rw [ha, hcardF₀, pow_mul]; norm_num)
    rw [← hTsF₀] at hTs
    obtain ⟨U, hU⟩ := hTs.exists_sylow_eq_subgroupOf
    obtain ⟨eF₀⟩ := nonempty_F₀_homocyclic hσ Δ hh
    let e : (U : Subgroup H) ≃* CFSG.RankTwoShapes.HomocyclicGroup σ.height :=
      (MulEquiv.subgroupCongr hU).trans ((Subgroup.subgroupOfEquivOfLe hF₀H).trans eF₀)
    intro Z hZH hZ hTZ
    apply le_oddCoreIn_of_subgroupOf hZH
    exact CFSG.ABGDGroups.homocyclic_sylow_odd_four_invariant_le_oddCore U hn e
      (isKleinFour_subgroupOf (T_isKleinFour hσ) hTH) (odd_card_subgroupOf hZH hZ)
      (subgroupOf_le_normalizer hTZ)
  ·
    have hcardTs : Nat.card Ts = Nat.card (σ.S : Subgroup G) := by
      rw [ha, card_S hσ hh, pow_succ, pow_mul]
      norm_num
      ring
    have hF₀Ts2 : σ.F₀.relIndex Ts = 2 := by
      have h := Subgroup.relIndex_mul_card σ.F₀ Ts
      rw [inf_eq_left.mpr hF₀Ts, hcardTs, card_S hσ hh, hcardF₀] at h
      have hpos : 0 < 4 ^ σ.height := by positivity
      exact Nat.eq_of_mul_eq_mul_right hpos (by rw [h])
    have hnormal : (σ.F₀.subgroupOf Ts).Normal := Subgroup.normal_of_index_eq_two hF₀Ts2
    have hTsN : Ts ≤ Subgroup.normalizer ((σ.F₀ : Subgroup G) : Set G) :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer hF₀Ts).mp hnormal
    have hTsM : Ts ≤ σ.M := fun g hg =>
      normalizer_T_le_M (le_normalizer_T_of_le_normalizer_F₀ hσ Δ (hTsN hg))
    have hSM : (σ.S : Subgroup G) ≤ σ.M := fun g hg => normalizer_T_le_M (hσ.T_normal hh hg)
    have hTsSyl : IsSylowOf 2 Ts σ.M := (isSylowOf_top_of_card σ.S hcardTs).of_le hTsM le_top
    have hSSyl : IsSylowOf 2 (σ.S : Subgroup G) σ.M :=
      (isSylowOf_top_of_card σ.S rfl).of_le hSM le_top
    obtain ⟨m, hmM, hmTs⟩ := exists_mem_conjSub_eq hTsSyl hSSyl
    have hmN := M_le_normalizer_T hσ Δ hmM
    have hmT : conjSub m σ.T = σ.T := conjSub_eq_self hmN
    have hmC : conjSub m σ.C = σ.C := conjSub_C_of_mem_M hmM
    set H' := conjSub m H with hH'
    have hTH' : σ.T ≤ H' := hmT ▸ conjSub_mono hTH
    have hCH' : σ.C ≤ H' := hmC ▸ conjSub_mono hCH
    have hSH' : (σ.S : Subgroup G) ≤ H' := hmTs ▸ conjSub_mono hTs.le
    have hDH' : σ.D ≤ H' := (D_eq_S hσ hh) ▸ hSH'
    have hH'top : H' ≠ ⊤ := by
      intro h
      apply hHtop
      rw [← conjSub_inv_conjSub m H, ← hH', h, conjSub_top]
    have hO' : oddCoreIn H' ≠ ⊥ := by
      rw [hH', oddCoreIn_conjSub]
      exact fun h => hO (conjSub_eq_bot_iff.mp h)
    rcases hF.fusion_cases H' hH'top hTH' (Or.inl hDH') with hQD | hQg | hDg | h2
    · exfalso
      refine hF.not_qd_of_cover H' hTH' hO' ?_ hQD
      intro g hg
      exact ⟨g, hCH' hg.1, 1, (σ.C ⊓ σ.ON).one_mem, mul_one g⟩
    · right
      exact centralInvolutionFusion_of_conjSub hmN
        (hQ H' hQg σ.T hTH' (T_isKleinFour hσ))
    · left
      apply oddInvariantInCore_of_conjSub hmN
      have hW' : HasWreathedSylow H' σ.height := by
        refine ⟨hn, fun Q => ?_⟩
        let S' : Sylow 2 H' := σ.S.subtype hSH'
        have hQS : Nat.card (Q : Subgroup H') = Nat.card (σ.S : Subgroup G) := by
          rw [Sylow.card_eq_multiplicity, ← Sylow.card_eq_multiplicity S', Sylow.coe_subtype,
            Nat.card_congr (Subgroup.subgroupOfEquivOfLe hSH').toEquiv]
        set Q' := (Q : Subgroup H').map H'.subtype
        have hQ' : Nat.card Q' = Nat.card (σ.S : Subgroup G) := by
          rw [Subgroup.card_map_of_injective H'.subtype_injective, hQS]
        let Q'' : Sylow 2 G := Sylow.ofCard Q' (by rw [hQ', Sylow.card_eq_multiplicity])
        obtain ⟨eQ⟩ := hW.2 Q''
        exact ⟨((Q : Subgroup H').equivMapOfInjective H'.subtype H'.subtype_injective).trans
          ((MulEquiv.subgroupCongr (Sylow.coe_ofCard Q' _).symm).trans eQ)⟩
      obtain ⟨K, hK⟩ : ∃ K : Subgroup H', IsDGroupData K := by
        rcases hDg with ⟨hdih, -⟩ | hK
        · exfalso
          let S' : Sylow 2 H' := σ.S.subtype hSH'
          obtain ⟨m', -, ⟨e₁⟩⟩ := hdih S'
          obtain ⟨e₂⟩ := hW'.2 S'
          exact not_dihedral_of_wreath hn e₁ e₂
        · exact hK
      intro Z hZH hZ hTZ
      apply le_oddCoreIn_of_subgroupOf hZH
      exact CFSG.ABGDGroups.wreathed_dGroup_odd_four_invariant_le_oddCore hK hW'
        (isKleinFour_subgroupOf (T_isKleinFour hσ) hTH') (odd_card_subgroupOf hZH hZ)
        (subgroupOf_le_normalizer hTZ)
    · left
      exact oddInvariantInCore_of_conjSub hmN fun Z hZH hZ _ =>
        le_oddCoreIn_of_hasNormalPComplement h2 hZH hZ

structure Config (σ : Setting G) (r : ℕ) (Rs X Y : Subgroup G) : Prop where
  isPGroup : IsPGroup r Rs
  P₁_le : σ.Ps r 0 ≤ Rs
  C_le : σ.C ≤ Subgroup.normalizer (Rs : Set G)
  P₂_not_le : ¬ σ.Ps r 1 ≤ Rs
  P₃_not_le : ¬ σ.Ps r 2 ≤ Rs
  X_mem : X ∈ maximals (signalizersPerm (Subgroup.normalizer (Rs : Set G)) σ.T σ.C r)
  Y_mem : Y ∈ maximals (signalizersPerm (Subgroup.normalizer (Rs : Set G)) σ.T σ.C r)
  not_conj : ¬ ∃ c ∈ σ.C, conjSub c X = Y
  comp_not_le : ∃ j : Fin 3, j ≠ 0 ∧ ∃ u ∈ comp σ X j,
    u ∉ oddCoreIn (Subgroup.normalizer (Rs : Set G))

namespace Config

variable {Rs X Y : Subgroup G}

omit [Finite G] in
theorem conj_x_ne (hc : Config σ r Rs X Y) {h : G}
    (hh : h ∈ Subgroup.normalizer (Rs : Set G)) {i : Fin 3} (hi : i ≠ 0) :
    h * σ.x * h⁻¹ ≠ σ.xs i := by
  intro heq
  have hP := conjSub_Ps r (i := i) (j := 0) heq
  have hle : σ.Ps r i ≤ Rs := by
    rw [← hP, ← conjSub_eq_self hh]
    exact conjSub_mono hc.P₁_le
  fin_cases i
  · exact hi rfl
  · exact hc.P₂_not_le hle
  · exact hc.P₃_not_le hle

theorem ne_bot (hc : Config σ r Rs X Y) (Δ : Data σ r) : Rs ≠ ⊥ := fun h =>
  Ps_zero_ne_bot Δ (le_bot_iff.mp (h ▸ hc.P₁_le))

theorem le_oddCoreIn (hc : Config σ r Rs X Y) (Δ : Data σ r) :
    Rs ≤ oddCoreIn (Subgroup.normalizer (Rs : Set G)) := by
  have := fact_prime Δ
  exact CFSG.ABGTheoremB.le_oddCoreIn Subgroup.le_normalizer le_rfl
    (odd_card_of_isPGroup (odd_r Δ) hc.isPGroup)

theorem oddCoreIn_ne_bot (hc : Config σ r Rs X Y) (Δ : Data σ r) :
    oddCoreIn (Subgroup.normalizer (Rs : Set G)) ≠ ⊥ := fun h =>
  hc.ne_bot Δ (le_bot_iff.mp (h ▸ hc.le_oddCoreIn Δ))

theorem T_le_H (hc : Config σ r Rs X Y) (hσ : σ.IsValid) :
    σ.T ≤ Subgroup.normalizer (Rs : Set G) := (σ.T_le_C hσ).trans hc.C_le

theorem ne_top (hc : Config σ r Rs X Y) (hσ : σ.IsValid) (Δ : Data σ r) :
    Subgroup.normalizer (Rs : Set G) ≠ ⊤ := by
  have := fact_prime Δ
  intro htop
  have hn : Rs.Normal := Subgroup.normalizer_eq_top_iff.mp htop
  rcases hσ.simple.eq_bot_or_eq_top_of_normal Rs with h | h
  · exact hc.ne_bot Δ h
  · have hT : IsPGroup r σ.T := hc.isPGroup.to_le (h ▸ le_top)
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hT
    rw [(T_isKleinFour hσ).card_four] at hk
    have h2 : 2 ∣ r ^ k := hk ▸ (by norm_num : 2 ∣ 4)
    have := (Nat.prime_dvd_prime_iff_eq Nat.prime_two Δ.prime).mp (Nat.prime_two.dvd_of_dvd_pow h2)
    exact Δ.ne_two this.symm

theorem not_isQDGroup (hc : Config σ r Rs X Y) (hσ : σ.IsValid) (hF : σ.ChapterIIFacts)
    (Δ : Data σ r) : ¬ IsQDGroup (Subgroup.normalizer (Rs : Set G)) := by
  refine hF.not_qd_of_cover _ (hc.T_le_H hσ) (hc.oddCoreIn_ne_bot Δ) ?_
  intro g hg
  exact ⟨g, hc.C_le hg.1, 1, (σ.C ⊓ σ.ON).one_mem, mul_one g⟩

theorem false_of_oddInvariantInCore (hc : Config σ r Rs X Y) (hσ : σ.IsValid) {Δ : Data σ r}
    (homni : Omnibus Δ) (h : OddInvariantInCore σ (Subgroup.normalizer (Rs : Set G))) :
    False := by
  obtain ⟨hYH, -, hTY, -, -⟩ := mem_signalizersPerm_iff.mp hc.Y_mem.1
  have hYO := h Y hYH (odd_card_of_maximals Δ hc.Y_mem) hTY
  exact hc.not_conj (exists_conj_of_le_sup_oddCoreIn hσ homni hc.C_le (hc.oddCoreIn_ne_bot Δ)
    hc.X_mem hc.Y_mem (hYO.trans le_sup_right))

theorem false_of_centralInvolutionFusion (hc : Config σ r Rs X Y) (hσ : σ.IsValid)
    (Δ : Data σ r) (h : CentralInvolutionFusion σ (Subgroup.normalizer (Rs : Set G))) :
    False := by
  obtain ⟨z, hzT, hz1, hzc, hzf⟩ := h
  by_cases hzx : z = σ.x
  · subst hzx
    obtain ⟨j, hj, u, hu, huO⟩ := hc.comp_not_le
    have huX : u ∈ X := hu.1
    have huH : u ∈ Subgroup.normalizer (Rs : Set G) :=
      (mem_signalizersPerm_iff.mp hc.X_mem.1).1 huX
    have hinv := x_conj_of_mem_comp hσ hj hu
    have hsq : u * σ.x * u⁻¹ * σ.x⁻¹ = u ^ 2 := by
      calc u * σ.x * u⁻¹ * σ.x⁻¹ = u * (σ.x * u * σ.x⁻¹)⁻¹ := by group
        _ = u ^ 2 := by rw [hinv, inv_inv, pow_two]
    have h2 := hzc u huH
    rw [hsq] at h2
    exact huO (mem_of_sq_mem_of_odd
      (odd_orderOf_of_mem (odd_card_of_maximals Δ hc.X_mem) huX) h2)
  · obtain ⟨h, hh, hht⟩ := hzf σ.x σ.x_mem_T (x_ne_one hσ) (Ne.symm hzx)
    have hxzT : σ.x * z ∈ σ.T := σ.T.mul_mem σ.x_mem_T hzT
    have hxz1 : σ.x * z ≠ 1 := fun h1 => hzx (by
      rw [mul_eq_one_iff_inv_eq, inv_of_orderOf_eq_two hσ.x_order] at h1
      exact h1.symm)
    obtain ⟨i, hi⟩ := exists_xs_of_mem_T hσ hxzT hxz1
    have hi0 : i ≠ 0 := by
      rintro rfl
      apply hz1
      have h0 : σ.x * z = σ.x * 1 := by rw [mul_one]; exact hi
      exact mul_left_cancel h0
    exact hc.conj_x_ne hh hi0 (hht.trans hi)

theorem not_hasNormalPComplement (hc : Config σ r Rs X Y) (hσ : σ.IsValid) {Δ : Data σ r}
    (homni : Omnibus Δ) :
    ¬ CFSG.HasNormalPComplement 2 (Subgroup.normalizer (Rs : Set G)) := fun h =>
  hc.false_of_oddInvariantInCore hσ homni fun _ hZH hZ _ =>
    le_oddCoreIn_of_hasNormalPComplement h hZH hZ

theorem false_of_three_dvd (hc : Config σ r Rs X Y) (hσ : σ.IsValid) (h92 : NotPGroupP σ r)
    (hheight : σ.height = 1) {T₂ : Subgroup G}
    (hT₂H : T₂ ≤ Subgroup.normalizer (Rs : Set G)) (hT₂ : IsKleinFour T₂) (hxT₂ : σ.x ∈ T₂)
    (h3 : 3 ∣ automizerIndex (T₂.subgroupOf (Subgroup.normalizer (Rs : Set G)))) : False := by
  obtain ⟨k, hkH, hkN, hkC, b, hkb⟩ := exists_three_element_of_three_dvd hT₂H h3
  have hT₂N : T₂ ≤ σ.N := by
    intro t ht
    rw [Setting.mem_N_iff]
    exact (kleinFour_comm (T := T₂) ht hxT₂)
  obtain ⟨v, hvN, hvT⟩ := exists_conjSub_eq_T hσ hheight hT₂ hT₂N
  set k' := v * k * v⁻¹ with hk'
  have hk'N : k' ∈ Subgroup.normalizer ((σ.T : Subgroup G) : Set G) := by
    rw [le_normalizer_iff_conjSub, ← hvT, hk', conjSub_mul, conjSub_mul, conjSub_inv_conjSub,
      conjSub_eq_self hkN]
  have hk'C : k' ∉ σ.C := by
    intro h
    apply hkC
    have h' : v⁻¹ * k' * v ∈ conjSub v⁻¹ (Subgroup.centralizer (σ.T : Set G)) := by
      rw [mem_conjSub]
      have e : (v⁻¹)⁻¹ * (v⁻¹ * k' * v) * v⁻¹ = k' := by group
      rw [e]
      exact h
    rw [conjSub_centralizer, ← hvT, conjSub_inv_conjSub] at h'
    have e : v⁻¹ * k' * v = k := by rw [hk']; group
    rwa [e] at h'
  have hk'b : k' ^ (3 ^ b) = 1 := by
    rw [hk', conj_pow, hkb]
    group
  set Rs' := conjSub v Rs
  have hk'Rs : k' ∈ Subgroup.normalizer (Rs' : Set G) := by
    rw [le_normalizer_iff_conjSub, hk', conjSub_mul, conjSub_mul, conjSub_inv_conjSub,
      conjSub_eq_self hkH]
  have hvx : v * σ.x * v⁻¹ = σ.x := by
    have := (Setting.mem_N_iff σ v).mp hvN
    rw [this]
    group
  have hP₁ : σ.Ps r 0 ≤ Rs' := by
    rw [← conjSub_Ps r (i := 0) (j := 0) hvx]
    exact conjSub_mono hc.P₁_le
  have hmove₁ := conj_x_ne_of_three_element hσ hk'N hk'C hk'b
  have hk'2N : k' ^ 2 ∈ Subgroup.normalizer ((σ.T : Subgroup G) : Set G) :=
    Subgroup.pow_mem _ hk'N 2
  have hk'2C : k' ^ 2 ∉ σ.C := by
    intro h
    apply hk'C
    have hodd : Odd (3 ^ b) := Odd.pow (by decide)
    obtain ⟨m, hm⟩ := hodd
    have : k' = (k' ^ 2) ^ (m + 1) := by
      rw [← pow_mul, show 2 * (m + 1) = 3 ^ b + 1 by omega, pow_succ, hk'b, one_mul]
    rw [this]
    exact σ.C.pow_mem h _
  have hk'2b : (k' ^ 2) ^ (3 ^ b) = 1 := by rw [← pow_mul, mul_comm, pow_mul, hk'b, one_pow]
  have hmove₂ := conj_x_ne_of_three_element hσ hk'2N hk'2C hk'2b
  have hmemT : ∀ {g t : G}, g ∈ Subgroup.normalizer ((σ.T : Subgroup G) : Set G) → t ∈ σ.T →
      g * t * g⁻¹ ∈ σ.T := fun hg ht => (Subgroup.mem_normalizer_iff.mp hg _).mp ht
  have hne1 : ∀ {g : G}, g * σ.x * g⁻¹ ≠ 1 := fun {g} h => x_ne_one hσ (by
    calc σ.x = g⁻¹ * (g * σ.x * g⁻¹) * g := by group
      _ = 1 := by rw [h]; group)
  obtain ⟨i, hi⟩ := exists_xs_of_mem_T hσ (hmemT hk'N σ.x_mem_T) hne1
  obtain ⟨i', hi'⟩ := exists_xs_of_mem_T hσ (hmemT hk'2N σ.x_mem_T) hne1
  have hi0 : i ≠ 0 := by rintro rfl; exact hmove₁ hi
  have hi'0 : i' ≠ 0 := by rintro rfl; exact hmove₂ hi'
  have hii' : i ≠ i' := by
    rintro rfl
    apply hmove₁
    have : k' * (k' * σ.x * k'⁻¹) * k'⁻¹ = k' * σ.x * k'⁻¹ := by
      rw [← hi'] at hi
      calc k' * (k' * σ.x * k'⁻¹) * k'⁻¹ = k' ^ 2 * σ.x * (k' ^ 2)⁻¹ := by
            rw [pow_two]; group
        _ = k' * σ.x * k'⁻¹ := hi.symm
    calc k' * σ.x * k'⁻¹ = k'⁻¹ * (k' * (k' * σ.x * k'⁻¹) * k'⁻¹) * k' := by group
      _ = k'⁻¹ * (k' * σ.x * k'⁻¹) * k' := by rw [this]
      _ = σ.x := by group
  have hPi : σ.Ps r i ≤ Rs' := by
    rw [← conjSub_Ps r (i := i) (j := 0) hi, ← conjSub_eq_self hk'Rs]
    exact conjSub_mono hP₁
  have hPi' : σ.Ps r i' ≤ Rs' := by
    have h2 : k' ^ 2 * σ.xs 0 * (k' ^ 2)⁻¹ = σ.xs i' := hi'
    rw [← conjSub_Ps r (i := i') (j := 0) h2, ← conjSub_eq_self (Subgroup.pow_mem _ hk'Rs 2)]
    exact conjSub_mono hP₁
  apply h92
  apply (isPGroup_conjSub hc.isPGroup v).to_le
  have hall : ∀ j : Fin 3, σ.Ps r j ≤ Rs' := by
    intro j
    fin_cases j
    · exact hP₁
    · fin_cases i <;> fin_cases i' <;> simp_all
    · fin_cases i <;> fin_cases i' <;> simp_all
  exact sup_le (sup_le (hall 0) (hall 1)) (hall 2)

theorem false (hc : Config σ r Rs X Y) (hσ : σ.IsValid) (hF : σ.ChapterIIFacts) (Δ : Data σ r)
    (homni : Omnibus Δ) (h92 : NotPGroupP σ r) (hQ : QGroupFourFusion G)
    (hD : DGroupFourFusion G) : False := by
  by_cases hh : σ.height = 1
  · rcases hF.fusion_cases _ (hc.ne_top hσ Δ) (hc.T_le_H hσ) (Or.inr hh) with
      hQD | hQg | hDg | h2
    · exact hc.not_isQDGroup hσ hF Δ hQD
    · exact hc.false_of_centralInvolutionFusion hσ Δ
        (hQ _ hQg σ.T (hc.T_le_H hσ) (T_isKleinFour hσ))
    · rcases hD (exists_hasSemidihedralSylow hσ hh) _ hDg σ.T (hc.T_le_H hσ)
        (T_isKleinFour hσ) σ.x σ.x_mem_T (x_ne_one hσ) with
        ⟨h, hh', t', ht', ht'x, heq⟩ | ⟨T₂, hT₂H, hT₂, hxT₂, h3⟩
      · have ht'1 : t' ≠ 1 := by
          rintro rfl
          apply x_ne_one hσ
          calc σ.x = h⁻¹ * (h * σ.x * h⁻¹) * h := by group
            _ = 1 := by rw [heq]; group
        obtain ⟨i, rfl⟩ := exists_xs_of_mem_T hσ ht' ht'1
        have hi : i ≠ 0 := by
          rintro rfl
          exact ht'x rfl
        exact hc.conj_x_ne hh' hi heq
      · exact hc.false_of_three_dvd hσ h92 hh hT₂H hT₂ hxT₂ h3
    · exact hc.not_hasNormalPComplement hσ homni h2
  · rcases wreathed_cases hσ hF Δ hQ hh hc.C_le (hc.ne_top hσ Δ) (hc.oddCoreIn_ne_bot Δ) with
      h | h
    · exact hc.false_of_oddInvariantInCore hσ homni h
    · exact hc.false_of_centralInvolutionFusion hσ Δ h

end Config

end CFSG.ABGTheoremB.TotallyInverted.Sec10
