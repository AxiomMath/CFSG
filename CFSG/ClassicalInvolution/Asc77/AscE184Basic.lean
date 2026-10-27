module

public import CFSG.ClassicalInvolution.Asc77.AscSteps182
public import CFSG.ClassicalInvolution.Asc77.AscSteps185
public import CFSG.Goldschmidt.Steps.LemmaXBasic

public section

namespace CFSG.ClassicalInvolution.Asc77

open CFSG.Open CFSG.ClassicalInvolution.Generic

variable {G : Type} [Group G] {p f : ℕ} [Fact p.Prime] {Ω : Set (Subgroup G)}

section General

omit [Fact p.Prime] in
private theorem sq_eq_of_orderOf_four {J : Subgroup G} {z u : G} (hz : IsUniqueInvolution J z)
    (hu : u ∈ J) (h4 : orderOf u = 4) : u * u = z := by
  have h1 : (u * u) * (u * u) = 1 := by
    have := pow_orderOf_eq_one u
    rw [h4] at this
    calc (u * u) * (u * u) = u ^ 4 := by simp [pow_succ, mul_assoc]
      _ = 1 := this
  rcases hz.unique (u * u) (J.mul_mem hu hu) h1 with h | h
  · exfalso
    have : orderOf u ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact h)
    rw [h4] at this
    omega
  · exact h

omit [Fact p.Prime] in
private theorem isPGroup_zpowers_of_orderOf_four {u : G} (h4 : orderOf u = 4) :
    IsPGroup 2 (Subgroup.zpowers u) :=
  IsPGroup.of_card (n := 2) (by rw [Nat.card_zpowers, h4]; norm_num)

theorem mem_normalizer_oddCoreOf {Y : Subgroup G} {y : G} (hy : y ∈ Y) :
    y ∈ Subgroup.normalizer (oddCoreOf Y : Set G) := by
  have key : ∀ {y : G}, y ∈ Y → ∀ {x : G}, x ∈ oddCoreOf Y → y * x * y⁻¹ ∈ oddCoreOf Y := by
    intro y hy x hx
    obtain ⟨n, hn, rfl⟩ := hx
    have h1 := (inferInstance : (classicalInvolutionOddCore ↥Y).Normal).conj_mem n hn ⟨y, hy⟩
    exact ⟨_, h1, by simp⟩
  rw [Subgroup.mem_normalizer_iff]
  intro x
  refine ⟨fun hx => key hy hx, fun hx => ?_⟩
  have := key (Y.inv_mem hy) hx
  simpa [mul_assoc] using this

theorem odd_natCard_oddCoreOf [Finite G] (Y : Subgroup G) : Odd (Nat.card (oddCoreOf Y)) := by
  have h : Nat.card (oddCoreOf Y) = Nat.card (classicalInvolutionOddCore ↥Y) :=
    Subgroup.card_map_of_injective Y.subtype_injective
  rw [h]
  exact CFSG.ComponentClassification.OddCore.odd_card ↥Y

end General

section MinCex

variable [Finite G] {K : Subgroup G} {S : Sylow 2 G} {R W H : Subgroup G}

theorem MinCex.le_H (c : MinCex p f Ω K S R W H) : K ≤ H := by
  obtain ⟨z, hz, hcz⟩ := c.exists_centralizer_le p f
  intro k hk
  apply hcz
  rw [Subgroup.mem_centralizer_singleton_iff]
  exact (hz.commute_of_mem hk).symm

theorem MinCex.twin_le_H (c : MinCex p f Ω K S R W H) {K' : Subgroup G} (hK' : K' ∈ twinSet Ω K) :
    K' ≤ H := by
  obtain ⟨z, hz, hcz⟩ := c.exists_centralizer_le p f
  obtain ⟨hK'Ω, z', hz'K, hz'K'⟩ := hK'
  have hzz : z = z' := hz.eq hz'K
  subst hzz
  intro k hk
  apply hcz
  rw [Subgroup.mem_centralizer_singleton_iff]
  exact (hz'K'.commute_of_mem hk).symm

theorem MinCex.mem_of_conjSub_le (c : MinCex p f Ω K S R W H) (hA : EtaAbelian Ω)
    (hM : EtaMeet Ω) {g : G} (hg : conjSub g R ≤ H) : g ∈ H := by
  obtain ⟨u, huR, hu4⟩ :=
    c.stand.hyp.exists_orderOf_eq_four_of_mem_RSet c.stand.odd c.stand.hR.1
  exact c.mem_of_conj_mem hA hM (c.stand.hR.2.1 huR) hu4 (hg (conj_mem_conjSub huR))

theorem E187C.normalizer_le_of_le_of {G : Type} [Group G] {R H Y : Subgroup G}
    (hmem : ∀ {g : G}, conjSub g R ≤ H → g ∈ H) (hRY : R ≤ Y) (hYH : Y ≤ H) :
    Subgroup.normalizer (Y : Set G) ≤ H := by
  intro n hn
  refine hmem (g := n) fun x hx => ?_
  rw [mem_conjSub_iff] at hx
  have h1 : n * (n⁻¹ * x * n) * n⁻¹ ∈ Y := (Subgroup.mem_normalizer_iff.mp hn _).mp (hRY hx)
  have e : n * (n⁻¹ * x * n) * n⁻¹ = x := by group
  rw [e] at h1
  exact hYH h1

theorem MinCex.normalizer_le_of_le (c : MinCex p f Ω K S R W H) (hA : EtaAbelian Ω)
    (hM : EtaMeet Ω) {Y : Subgroup G} (hRY : R ≤ Y) (hYH : Y ≤ H) :
    Subgroup.normalizer (Y : Set G) ≤ H :=
  E187C.normalizer_le_of_le_of (fun hg => c.mem_of_conjSub_le hA hM hg) hRY hYH

theorem E187C.exists_orderOf_four_mem_W_of {G : Type} [Group G] [Finite G]
    {Ω : Set (Subgroup G)} {K W : Subgroup G} {S : Sylow 2 G} {J T : Subgroup G} (hM : EtaMeet Ω)
    (heta : ∃ η : Set (Subgroup G), η ∈ etaG Ω ∧ W = ⨆ V ∈ η, V ∧
      (∀ V ∈ η, V ∈ USet Ω ∧ V ≤ (S : Subgroup G)) ∧
      (∀ x ∈ W, ∀ y ∈ W, x * y = y * x) ∧ ∃ V₀ ∈ η, V₀ ≤ K)
    (hJ : J ∈ Ω) (hT : IsSylow2In T J) (hTS : T ≤ (S : Subgroup G))
    (h8R : ∀ {Q : Subgroup G}, Q ∈ RSet Ω → 8 ≤ Nat.card Q)
    (hdU : ∀ {U : Subgroup G}, U ∈ USet Ω → IsCyclic ↥U ∧ 4 ≤ Nat.card U)
    (h2U : ∀ {U : Subgroup G}, U ∈ USet Ω → IsPGroup 2 U) :
    ∃ u ∈ J ⊓ W, orderOf u = 4 ∧ u ∈ T := by
  obtain ⟨η, hη, hWη, hηU, -, -⟩ := heta
  have hTmem : T ∈ RSet Ω := mem_RSet_of_isSylow2In hJ hT
  have h8 := h8R hTmem
  have hle : T ≤ J ⊓ (S : Subgroup G) := le_inf hT.1 hTS
  have h2 : 2 < Nat.card ↥(J ⊓ (S : Subgroup G)) := by
    have := Subgroup.card_le_of_le hle
    omega
  have hmem : J ⊓ (⨆ V ∈ η, V) ∈ η := hM S η hη (fun V hV => (hηU V hV).2) J hJ h2
  rw [← hWη] at hmem
  have hU : J ⊓ W ∈ USet Ω := (hηU _ hmem).1
  obtain ⟨hcyc, h4⟩ := hdU hU
  obtain ⟨u, hu, hu4⟩ := exists_orderOf_eq_four_of_isPGroup_of_isCyclic (h2U hU) hcyc h4
  refine ⟨u, hu, hu4, ?_⟩
  have hSp : IsPGroup 2 ↥(J ⊓ (S : Subgroup G)) :=
    (Sylow.isPGroup' S).to_le (inf_le_right : J ⊓ (S : Subgroup G) ≤ S)
  have heq : J ⊓ (S : Subgroup G) = T := hT.eq_of_le hSp inf_le_left hle
  rw [← heq]
  exact ⟨hu.1, (hηU _ hmem).2 hu⟩

theorem MinCex.exists_orderOf_four_mem_W (c : MinCex p f Ω K S R W H) (hA : EtaAbelian Ω)
    (hM : EtaMeet Ω) {J T : Subgroup G} (hJ : J ∈ Ω) (hT : IsSylow2In T J)
    (hTS : T ≤ (S : Subgroup G)) : ∃ u ∈ J ⊓ W, orderOf u = 4 ∧ u ∈ T := by
  exact E187C.exists_orderOf_four_mem_W_of hM (c.exists_eta hA) hJ hT hTS
    (fun hQ => c.stand.hyp.eight_le_of_mem_RSet c.stand.odd hQ)
    (fun hU => by
      obtain ⟨-, -, -, -, -, -, hcyc, -, h4⟩ := c.stand.hyp.exists_data_of_mem_USet c.stand.odd hU
      exact ⟨hcyc, h4⟩)
    (fun hU => c.stand.hyp.isPGroup_of_mem_USet c.stand.odd hU)

theorem E187C.exists_fourGroup_of
    (hfour : ∀ {J T : Subgroup G}, J ∈ Ω → IsSylow2In T J → T ≤ (S : Subgroup G) →
      ∃ u ∈ J ⊓ W, orderOf u = 4 ∧ u ∈ T)
    (habel : ∀ x ∈ W, ∀ y ∈ W, x * y = y * x)
    (hsyl : ∀ {K Q : Subgroup G}, K ∈ Ω → Q ∈ RSet Ω → Q ≤ K → IsSylow2In Q K)
    (heq : ∀ {K J A : Subgroup G}, K ∈ Ω → J ∈ Ω → IsPGroup 2 A → 4 ≤ Nat.card A → A ≤ K →
      A ≤ J → K = J)
    (hnormtw : ∀ {K J : Subgroup G} {z : G}, K ∈ Ω → J ∈ Ω → K ≠ J → IsUniqueInvolution K z →
      IsUniqueInvolution J z → K ≤ Subgroup.normalizer (J : Set G))
    (hcmmtw : ∀ {K J : Subgroup G} {z : G} {A B : Subgroup G}, K ∈ Ω → J ∈ Ω → K ≠ J →
      IsUniqueInvolution K z → IsUniqueInvolution J z → A ≤ K → B ≤ J → IsPGroup 2 ↥(A ⊔ B) →
      Commutes A B)
    (hcent : ∀ {z : G} {J R₂ : Subgroup G}, IsUniqueInvolution K z → J ∈ KPerp Ω K →
      R₂ ∈ RSet Ω → R₂ ≤ J → Commutes R R₂ → ∀ a ∈ R ⊔ R₂, a ∈ W → a ≠ 1 → a * a = 1 →
      Subgroup.centralizer ({a} : Set G) ≤ H)
    (hK : K ∈ Ω) (hRR : R ∈ RSet Ω) (hRK : R ≤ K) (hRS : R ≤ (S : Subgroup G))
    {K' : Subgroup G} (hK' : K' ∈ twinSet Ω K) (hK'ne : K' ≠ K)
    {R' : Subgroup G} (hR' : R' ∈ RSet Ω) (hR'K' : R' ≤ K') (hR'S : R' ≤ (S : Subgroup G)) :
    ∃ U : Subgroup G, U ≤ R ⊔ R' ∧ U ≤ W ∧ (∀ x ∈ U, ∀ y ∈ U, x * y = y * x) ∧
      (∀ x ∈ U, x * x = 1) ∧ 4 ≤ Nat.card U ∧
      ∀ e ∈ U, e ≠ 1 → Subgroup.centralizer ({e} : Set G) ≤ H := by
  obtain ⟨hK'Ω, z, hzK, hzK'⟩ := hK'
  have hRsyl : IsSylow2In R K := hsyl hK hRR hRK
  have hR'syl : IsSylow2In R' K' := hsyl hK'Ω hR' hR'K'
  obtain ⟨u₁, ⟨hu₁K, hu₁W⟩, hu₁4, hu₁R⟩ := hfour hK hRsyl hRS
  obtain ⟨u₂, ⟨hu₂K', hu₂W⟩, hu₂4, hu₂R'⟩ := hfour hK'Ω hR'syl hR'S
  have hsq₁ : u₁ * u₁ = z := sq_eq_of_orderOf_four hzK hu₁K hu₁4
  have hsq₂ : u₂ * u₂ = z := sq_eq_of_orderOf_four hzK' hu₂K' hu₂4
  have hzW : z ∈ W := hsq₁ ▸ W.mul_mem hu₁W hu₁W
  have hzR : z ∈ R := hsq₁ ▸ R.mul_mem hu₁R hu₁R
  have hdisj : ∀ {u : G}, u ∈ K → u ∈ K' → orderOf u = 4 → False := by
    intro u huK huK' hu4
    have := heq hK hK'Ω (isPGroup_zpowers_of_orderOf_four hu4)
      (by rw [Nat.card_zpowers, hu4]) (Subgroup.zpowers_le.mpr huK)
      (Subgroup.zpowers_le.mpr huK')
    exact hK'ne this.symm
  have hu₁K' : u₁ ∉ K' := fun h => hdisj hu₁K h hu₁4
  have hu₂K : u₂ ∉ K := fun h => hdisj h hu₂K' hu₂4
  set a : G := u₁ * u₂⁻¹ with ha
  have haW : a ∈ W := W.mul_mem hu₁W (W.inv_mem hu₂W)
  have haR : a ∈ R ⊔ R' :=
    Subgroup.mul_mem _ (Subgroup.mem_sup_left hu₁R)
      (Subgroup.inv_mem _ (Subgroup.mem_sup_right hu₂R'))
  have haa : a * a = 1 := by
    have hc : u₂⁻¹ * u₁ = u₁ * u₂⁻¹ := habel _ (W.inv_mem hu₂W) _ hu₁W
    have h2inv : u₂⁻¹ * u₂⁻¹ = z⁻¹ := by
      rw [← hsq₂, mul_inv_rev]
    calc a * a = u₁ * (u₂⁻¹ * u₁) * u₂⁻¹ := by rw [ha]; group
      _ = u₁ * (u₁ * u₂⁻¹) * u₂⁻¹ := by rw [hc]
      _ = (u₁ * u₁) * (u₂⁻¹ * u₂⁻¹) := by group
      _ = z * z⁻¹ := by rw [hsq₁, h2inv]
      _ = 1 := mul_inv_cancel z
  have haK : a ∉ K := by
    intro haK
    apply hu₂K
    have : u₂⁻¹ = u₁⁻¹ * a := by rw [ha]; group
    have h' : u₂⁻¹ ∈ K := this ▸ K.mul_mem (K.inv_mem hu₁K) haK
    simpa using K.inv_mem h'
  have hzK_mem : z ∈ K := hzK.mem
  have ha1 : a ≠ 1 := fun h => haK (h ▸ K.one_mem)
  have haz : a ≠ z := fun h => haK (h ▸ hzK_mem)
  set U : Subgroup G := Subgroup.closure ({z, a} : Set G) with hU
  have hUW : U ≤ W := by
    rw [hU, Subgroup.closure_le]
    intro x hx
    rcases hx with rfl | rfl
    · exact hzW
    · exact haW
  have hURR : U ≤ R ⊔ R' := by
    rw [hU, Subgroup.closure_le]
    intro x hx
    rcases hx with rfl | rfl
    · exact Subgroup.mem_sup_left hzR
    · exact haR
  have hcomm : ∀ x ∈ U, ∀ y ∈ U, x * y = y * x := fun x hx y hy => habel x (hUW hx) y (hUW hy)
  have hsq : ∀ x ∈ U, x * x = 1 := by
    intro x hx
    induction hx using Subgroup.closure_induction with
    | mem x hx =>
      rcases hx with rfl | rfl
      · exact hzK.sq
      · exact haa
    | one => simp
    | mul x y hx hy ihx ihy =>
      have hxy : y * x = x * y := (hcomm x hx y hy).symm
      calc x * y * (x * y) = x * (y * x) * y := by group
        _ = x * (x * y) * y := by rw [hxy]
        _ = (x * x) * (y * y) := by group
        _ = 1 := by rw [ihx, ihy]; simp
    | inv x hx ihx =>
      calc x⁻¹ * x⁻¹ = (x * x)⁻¹ := by group
        _ = 1 := by rw [ihx]; simp
  have hcard : 4 ≤ Nat.card U := by
    have hz2 : orderOf z = 2 := orderOf_eq_prime (by rw [pow_two]; exact hzK.sq) hzK.ne_one
    have hH1U : Subgroup.zpowers z ≤ U :=
      Subgroup.zpowers_le.mpr (Subgroup.subset_closure (by simp))
    have hc2 : Nat.card (Subgroup.zpowers z) = 2 := by rw [Nat.card_zpowers, hz2]
    have hdvd : 2 ∣ Nat.card U := hc2 ▸ Subgroup.card_dvd_of_le hH1U
    have hne : Subgroup.zpowers z ≠ U := by
      intro h
      have haU : a ∈ U := Subgroup.subset_closure (by simp)
      rw [← h] at haU
      exact haK (Subgroup.zpowers_le.mpr hzK_mem haU)
    have hlt : 2 < Nat.card U := by
      by_contra hle
      have hle' := not_lt.mp hle
      exact hne (Subgroup.eq_of_le_of_card_ge hH1U (by omega))
    obtain ⟨m, hm⟩ := hdvd
    omega
  refine ⟨U, hURR, hUW, hcomm, hsq, hcard, fun e he he1 => ?_⟩
  have hKperp : K' ∈ KPerp Ω K := by
    refine Set.mem_insert_of_mem _ ⟨hK'Ω, hK'ne, R', hR', hR'K', fun x hx => ?_⟩
    exact hnormtw hK'Ω hK hK'ne hzK' hzK (hR'K' hx)
  have hRR'2 : IsPGroup 2 ↥(R ⊔ R') := S.isPGroup'.to_le (sup_le hRS hR'S)
  have hcomm' : Commutes R R' :=
    hcmmtw hK hK'Ω (Ne.symm hK'ne) hzK hzK' hRK hR'K' hRR'2
  exact hcent hzK hKperp hR' hR'K' hcomm' e (hURR he) (hUW he) he1 (hsq e he)


theorem MinCex.exists_fourGroup (c : MinCex p f Ω K S R W H) (hA : EtaAbelian Ω)
    (hM : EtaMeet Ω) {K' : Subgroup G} (hK' : K' ∈ twinSet Ω K) (hK'ne : K' ≠ K)
    {R' : Subgroup G} (hR' : R' ∈ RSet Ω) (hR'K' : R' ≤ K') (hR'S : R' ≤ (S : Subgroup G)) :
    ∃ U : Subgroup G, U ≤ R ⊔ R' ∧ U ≤ W ∧ (∀ x ∈ U, ∀ y ∈ U, x * y = y * x) ∧
      (∀ x ∈ U, x * x = 1) ∧ 4 ≤ Nat.card U ∧
      ∀ e ∈ U, e ≠ 1 → Subgroup.centralizer ({e} : Set G) ≤ H := by
  have hp : p ≠ 2 := c.stand.odd
  have hΩ : HypOmegaMod p f Ω := c.stand.hyp
  obtain ⟨hRR, hRK, hRS⟩ := c.stand.hR
  exact E187C.exists_fourGroup_of
    (fun hJ hT hTS => c.exists_orderOf_four_mem_W hA hM hJ hT hTS)
    (by obtain ⟨-, -, -, -, habel, -⟩ := c.exists_eta hA; exact habel)
    (fun hK hR hRK => hΩ.isSylow2In_of_mem_RSet_of_le hp hK hR hRK)
    (fun hK hJ hA hcard hAK hAJ => hΩ.eq_of_le_of_le hK hJ hA hcard hAK hAJ)
    (fun hK hJ hKJ hzK hzJ => hΩ.le_normalizer_of_twin hK hJ hKJ hzK hzJ)
    (fun hK hJ hKJ hzK hzJ hA hB hAB =>
      hΩ.commutes_of_twin_of_isPGroup hK hJ hKJ hzK hzJ hA hB hAB)
    (fun hz hJ hR₂ hR₂J hcomm a ha _ ha1 ha2 =>
      c.hyp.cent K ⟨c.stand.mem, _, hz, hz⟩ _ hJ R _ hRR hRK hR₂ hR₂J (Or.inl hcomm) a ha ha1 ha2)
    c.stand.mem hRR hRK hRS hK' hK'ne hR' hR'K' hR'S

theorem MinCex.oddCoreOf_le (c : MinCex p f Ω K S R W H) (hA : EtaAbelian Ω) (hM : EtaMeet Ω)
    {K' : Subgroup G} (hK' : K' ∈ twinSet Ω K) (hK'ne : K' ≠ K) {R' : Subgroup G}
    (hR' : R' ∈ RSet Ω) (hR'K' : R' ≤ K') (hR'S : R' ≤ (S : Subgroup G)) {Y : Subgroup G}
    (hY : R ⊔ R' ≤ Y) : oddCoreOf Y ≤ H := by
  obtain ⟨U, hUR, -, hcomm, hsq, hU4, hC⟩ := c.exists_fourGroup hA hM hK' hK'ne hR' hR'K' hR'S
  have hUY : U ≤ Y := hUR.trans hY
  have : IsMulCommutative ↥U := ⟨⟨fun a b => Subtype.ext (hcomm _ a.2 _ b.2)⟩⟩
  exact CFSG.Goldschmidt.LemmaX.le_of_forall_inf_centralizer_le (E := U) (N := oddCoreOf Y)
    (J := H) this (fun x hx => by rw [pow_two]; exact hsq x hx) hU4
    (fun u hu => mem_normalizer_oddCoreOf (hUY hu)) (odd_natCard_oddCoreOf Y)
    (fun e he he1 => inf_le_right.trans (hC e he he1))

end MinCex

end CFSG.ClassicalInvolution.Asc77
