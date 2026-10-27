module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10FSeitz
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10FBase2
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10FBaseIso
public import CFSG.LocalAnalysis.GLTheoremA.S11.InputsCE

public section

namespace CFSG.LocalAnalysis.GLTheoremA.Y10F

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB

@[expose] def SeitzNoncentral : Prop :=
  ∀ (K : Type) [Group K] [Finite K], HasLabel K (fun _ => True) →
    ∀ q : ℕ, q.Prime → q ≠ 2 → 4 ≤ GLATwoLocalRank q K →
      ∃ E : Subgroup K, IsElemAbelian q E ∧ Nat.card E = q ^ 3 ∧
        ∃ T : Subgroup K, IsPGroup 2 T ∧ ¬ T ≤ Subgroup.center K ∧
          E ≤ Subgroup.normalizer (T : Set K)

theorem conj_mem_center_iff {K : Type} [Group K] (g : K) (x : K) :
    g * x * g⁻¹ ∈ Subgroup.center K ↔ x ∈ Subgroup.center K := by
  constructor
  · intro h
    rw [Subgroup.mem_center_iff] at h ⊢
    intro z
    have := h (g * z * g⁻¹)
    have h2 : g * z * g⁻¹ * (g * x * g⁻¹) = g * x * g⁻¹ * (g * z * g⁻¹) := this
    have h3 : g * (z * x) * g⁻¹ = g * (x * z) * g⁻¹ := by
      calc g * (z * x) * g⁻¹ = g * z * g⁻¹ * (g * x * g⁻¹) := by group
        _ = g * x * g⁻¹ * (g * z * g⁻¹) := h2
        _ = g * (x * z) * g⁻¹ := by group
    exact mul_left_cancel (mul_right_cancel h3)
  · intro h
    rw [Subgroup.mem_center_iff] at h ⊢
    intro z
    have := h (g⁻¹ * z * g)
    calc z * (g * x * g⁻¹) = g * ((g⁻¹ * z * g) * x) * g⁻¹ := by group
      _ = g * (x * (g⁻¹ * z * g)) * g⁻¹ := by rw [this]
      _ = g * x * g⁻¹ * z := by group

theorem map_le_normalizer_map_equiv {K : Type} [Group K] (c : MulAut K) {E T : Subgroup K}
    (h : E ≤ Subgroup.normalizer (T : Set K)) :
    E.map c.toMonoidHom ≤ Subgroup.normalizer ((T.map c.toMonoidHom : Subgroup K) : Set K) := by
  rintro _ ⟨e, he, rfl⟩
  rw [Subgroup.mem_normalizer_iff]
  intro y
  obtain ⟨y₀, rfl⟩ := c.surjective y
  have hmem : ∀ z : K, c z ∈ T.map c.toMonoidHom ↔ z ∈ T := by
    intro z
    constructor
    · rintro ⟨t, ht, hct⟩
      exact (c.injective hct) ▸ ht
    · intro hz
      exact ⟨z, hz, rfl⟩
  have hconj : c e * c y₀ * (c e)⁻¹ = c (e * y₀ * e⁻¹) := by simp
  change c y₀ ∈ T.map c.toMonoidHom ↔ c e * c y₀ * (c e)⁻¹ ∈ T.map c.toMonoidHom
  rw [hconj, hmem, hmem]
  exact Subgroup.mem_normalizer_iff.1 (h he) y₀

theorem exists_noncentral_in_sylow (h2 : SeitzNoncentral) {K : Type} [Group K] [Finite K]
    (hK : HasLabel K (fun _ => True)) {q : ℕ} (hq : q.Prime) (hq2 : q ≠ 2)
    (h4 : 4 ≤ GLATwoLocalRank q K) {Q' : Subgroup K} (hQ : IsPGroup q Q')
    (hmax : ∀ Q : Subgroup K, IsPGroup q Q → Q' ≤ Q → Q = Q') :
    ∃ E : Subgroup K, E ≤ Q' ∧ IsElemAbelian q E ∧ Nat.card E = q ^ 3 ∧
      ∃ T : Subgroup K, IsPGroup 2 T ∧ ¬ T ≤ Subgroup.center K ∧
        E ≤ Subgroup.normalizer (T : Set K) := by
  haveI : Fact q.Prime := ⟨hq⟩
  obtain ⟨E₀, hE₀, hE₀c, T₀, hT₀2, hT₀nc, hE₀T₀⟩ := h2 K hK q hq hq2 h4
  obtain ⟨g, hg⟩ := exists_conj_le_sylow (isPGroup_of_isElemAbelian hE₀) hQ hmax
  have hc : Function.Injective (MulAut.conj g).toMonoidHom := (MulAut.conj g).injective
  refine ⟨E₀.map (MulAut.conj g).toMonoidHom, hg,
    (isElemAbelian_map_iff_of_injective hc E₀).2 hE₀, ?_,
    T₀.map (MulAut.conj g).toMonoidHom, (isPGroup_map_iff_of_injective hc T₀).2 hT₀2, ?_, ?_⟩
  · rw [Subgroup.card_map_of_injective hc]; exact hE₀c
  · intro hT
    apply hT₀nc
    intro t ht
    have := hT (Subgroup.mem_map_of_mem _ ht)
    exact (conj_mem_center_iff g t).1 this
  · exact map_le_normalizer_map_equiv (MulAut.conj g) hE₀T₀


variable {G : Type} [Group G] [Finite G]

theorem i2315aAt_of_noncentral (h1 : SeitzGen) (h2 : SeitzNoncentral) : I2315aAt G := by
  intro q hq hq2 K Qo hK hQo hQoK hmax h4
  haveI : Fact q.Prime := ⟨hq⟩
  have hι : Function.Injective K.subtype := K.subtype_injective
  set Q' : Subgroup K := Qo.subgroupOf K with hQ'
  have hQ'map : Q'.map K.subtype = Qo := subgroupOf_map_subtype_of_le hQoK
  have hQ'p : IsPGroup q Q' := (isPGroup_subgroupOf_iff hQoK).2 hQo
  have hQ'max : ∀ Q : Subgroup K, IsPGroup q Q → Q' ≤ Q → Q = Q' := by
    intro Q hQ hle
    have h1' : IsPGroup q (Q.map K.subtype) := (isPGroup_map_subtype_iff Q).2 hQ
    have h2' : Qo ≤ Q.map K.subtype := hQ'map ▸ Subgroup.map_mono hle
    have h3' := hmax (Q.map K.subtype) h1' (map_subtype_le Q) h2'
    rw [← map_subtype_subgroupOf Q, h3']
  obtain ⟨E, hEQ, hEel, hEc, T, hT2, hTnc, hET⟩ :=
    exists_noncentral_in_sylow h2 hK hq hq2 h4 hQ'p hQ'max
  have hcardE : Nat.card (E.map (MulAut.conj : K →* MulAut K)) ≤ q ^ 3 :=
    (card_map_le_of_finite (MulAut.conj : K →* MulAut K) E).trans hEc.le
  have hgen := seitzGen_action h1 hK hq hq2 (MulAut.conj : K →* MulAut K) hEel hcardE
    ⟨T, hT2, hTnc, fun e he t ht => by
      rw [MulAut.conj_apply]; exact (Subgroup.mem_normalizer_iff.1 (hET he) t).1 ht⟩
  have hKtop : K = (⊤ : Subgroup K).map K.subtype := by
    rw [Subgroup.map_top, Subgroup.range_subtype]
  refine hKtop.le.trans ?_
  rw [← hgen, Subgroup.map_le_iff_le_comap]
  refine iSup₂_le fun F hF => ?_
  rw [← Subgroup.map_le_iff_le_comap]
  obtain ⟨hFE, hFi⟩ := hF
  have hFel : IsElemAbelian q F := isElemAbelian_mono hEel hFE
  have hFQo : F.map K.subtype ≤ Qo := hQ'map ▸ Subgroup.map_mono (hFE.trans hEQ)
  have hcardF : 2 ≤ CFSG.Open.pRank q F := by
    obtain ⟨j, hj⟩ := exists_card_eq_pow_of_isElemAbelian hq hFel
    have hmul := card_mul_relIndex hFE
    rw [hEc, hj] at hmul
    have hj2 : 2 ≤ j := by
      by_contra hlt
      have hj1 : j ≤ 1 := by omega
      have h5 : q ^ j * F.relIndex E ≤ q ^ 1 * q := Nat.mul_le_mul (Nat.pow_le_pow_right hq.pos hj1) hFi
      have h6 : q ^ 1 * q < q ^ 3 := by
        rw [← pow_succ]
        exact Nat.pow_lt_pow_right hq.one_lt (by norm_num)
      omega
    exact hj2.trans (le_pRank_of_elem hq.one_lt le_rfl hFel hj)
  refine le_trans ?_ (le_sSup ⟨F.map K.subtype, hFQo, by rw [pRank_map_subtype]; exact hcardF, ?_, rfl⟩)
  · rintro _ ⟨k, hk, rfl⟩
    refine ⟨?_, k.2⟩
    have hc : K.subtype k ∈ Subgroup.centralizer ((F.map K.subtype : Subgroup G) : Set G) := by
      refine Subgroup.mem_centralizer_iff.2 ?_
      rintro _ ⟨f, hf, rfl⟩
      have := (mem_centFixAct.1 hk) f hf
      rw [MulAut.conj_apply] at this
      have h' : (f : K) * k = k * f := by
        calc f * k = f * k * f⁻¹ * f := by group
          _ = k * f := by rw [this]
      exact congrArg Subtype.val h'
    exact Subgroup.centralizer_le_normalizer _ hc
  · have hsub : E.map K.subtype ≤ F.map K.subtype ⊔ (Qo ⊓ Subgroup.centralizer ((F.map K.subtype : Subgroup G) : Set G)) := by
      refine le_trans ?_ le_sup_right
      rintro _ ⟨e, he, rfl⟩
      refine ⟨hQ'map ▸ Subgroup.mem_map_of_mem _ (hEQ he), ?_⟩
      refine Subgroup.mem_centralizer_iff.2 ?_
      rintro _ ⟨f, hf, rfl⟩
      have := isElemAbelian_commute hEel (hFE hf) he
      exact congrArg Subtype.val this
    have h3 := le_pRank_of_elem hq.one_lt hsub ((isElemAbelian_map_subtype_iff E).2 hEel)
      (k := 3) (by rw [card_map_subtype]; exact hEc)
    exact h3


@[expose] def SeitzEvenCentre : Prop :=
  ∀ (K : Type) [Group K] [Finite K], HasLabel K (fun _ => True) →
    ∀ q : ℕ, q.Prime → q ≠ 2 → Even (Nat.card (Subgroup.center K)) →
      4 ≤ CFSG.Open.pRank q (⊤ : Subgroup K) →
      ∃ E : Subgroup K, IsElemAbelian q E ∧ Nat.card E = q ^ 3 ∧
        ∃ T : Subgroup K, IsPGroup 2 T ∧ ¬ T ≤ Subgroup.center K ∧
          E ≤ Subgroup.normalizer (T : Set K)

theorem seitzNoncentral_of_evenCentre (h : SeitzEvenCentre) : SeitzNoncentral := by
  intro K _ _ hK q hq hq2 h4
  haveI : Fact q.Prime := ⟨hq⟩
  have hbdd := bddAbove_twoLocalPRanks (G := K) hq.one_lt
  have hne : {k | ∃ H : Subgroup K, IsTwoLocal H ∧ CFSG.Open.pRank q H = k}.Nonempty := by
    by_contra hemp
    rw [Set.not_nonempty_iff_eq_empty] at hemp
    have h0 : GLATwoLocalRank q K = 0 := by
      show sSup {k | ∃ H : Subgroup K, IsTwoLocal H ∧ CFSG.Open.pRank q H = k} = 0
      rw [hemp]; exact csSup_empty
    omega
  obtain ⟨H, ⟨S, hS0, hS2, rfl⟩, hk⟩ := Nat.sSup_mem hne hbdd
  have hk4 : 4 ≤ CFSG.Open.pRank q (Subgroup.normalizer (S : Set K)) := by
    rw [hk]; exact h4
  obtain ⟨B, hBN, hBel, k, hk4', hBc⟩ := exists_elem_of_le_pRank hq.one_lt hk4
  by_cases hSc : S ≤ Subgroup.center K
  · refine h K hK q hq hq2 ?_ ?_
    ·
      have hSd : Nat.card S ∣ Nat.card (Subgroup.center K) := Subgroup.card_dvd_of_le hSc
      have hS1 : Nat.card S ≠ 1 := by
        intro h1
        exact hS0 (Subgroup.card_eq_one.1 h1)
      obtain ⟨j, hj⟩ := hS2.exists_card_eq
      have hj0 : j ≠ 0 := by
        rintro rfl
        exact hS1 (by simpa using hj)
      have : 2 ∣ Nat.card S := by rw [hj]; exact dvd_pow_self 2 hj0
      exact even_iff_two_dvd.2 (this.trans hSd)
    · exact (hk4'.trans (le_pRank_of_elem hq.one_lt (le_top : B ≤ ⊤) hBel hBc))
  · have hdvd : q ^ 3 ∣ Nat.card B := by
      rw [hBc]; exact pow_dvd_pow q (by omega)
    obtain ⟨E', hE'⟩ := Sylow.exists_subgroup_card_pow_prime q hdvd
    refine ⟨E'.map B.subtype, ?_, ?_, S, hS2, hSc, ?_⟩
    · exact isElemAbelian_mono hBel (map_subtype_le E')
    · rw [card_map_subtype]; exact hE'
    · exact (map_subtype_le E').trans hBN

theorem i2315aAt_of_seitzGen (h1 : SeitzGen) (h2 : SeitzEvenCentre) : I2315aAt G :=
  i2315aAt_of_noncentral h1 (seitzNoncentral_of_evenCentre h2)

end CFSG.LocalAnalysis.GLTheoremA.Y10F
