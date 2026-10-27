module

public import CFSG.GH74.Uniqueness.SU.KI4Comb
public import CFSG.GH74.Uniqueness.SU.KI4Struct
public import CFSG.GH74.Uniqueness.SU.KI4Comp
public import CFSG.GH74.Uniqueness.SU.KI6BFrat
public import CFSG.Monster.B.Recog.GenericGoldschmidtApp
public import CFSG.Goldschmidt.Final
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTheorem3GoldCore
public import CFSG.Goldschmidt.Steps.G3aComp

public section

namespace CFSG.GH74.Uniqueness.SU.K.R4

open Subgroup CFSG CFSG.Open

variable {Y : Type} [Group Y] [Finite Y]

open CFSG.GH74.Uniqueness.SU.K.R6 in
theorem ki4_core
    (h : Setup Y) (S' : Sylow 2 Y) (R' : Subgroup Y)
    (hR'sq : ∀ r ∈ R', r * r = 1)
    (hR' : R' = CFSG.Open.pCore 2 Y ⊔
      Subgroup.closure {t | t ∈ (S' : Subgroup Y) ⊓ goldschmidtLayer Y ∧ t ^ 2 = 1})
    (hcomp : ∀ K : Subgroup Y, IsComponentOf K ⊤ →
      goldschmidtSimpleType (K ⧸ Subgroup.center K))
    (hcl : ∀ r ∈ R', ∀ y : Y, y⁻¹ * r * y ∈ (S' : Subgroup Y) → y⁻¹ * r * y ∈ R')
    (X : Finset Y) (hX : X.card = 5) (hXR' : ∀ x ∈ X, x ∈ R')
    (hXcl : ∀ x ∈ X, ∀ y : Y, y⁻¹ * x * y ∈ R' → y⁻¹ * x * y ∈ X)
    (hXQ : ∀ x ∈ X, x ∉ CFSG.Open.pCore 2 Y) : False := by
  classical
  have hex : ∀ K : {K : Subgroup Y // CFSG.IsComponent K},
      ∃ (f : Y →* K.1 ⧸ Subgroup.center K.1) (Ω : Subgroup (K.1 ⧸ Subgroup.center K.1)),
        (∀ k : K.1, f (k : Y) = (k : K.1 ⧸ Subgroup.center K.1)) ∧
        (∀ y : Y, f y = 1 ↔ y ∈ Subgroup.centralizer (K.1 : Set Y)) ∧
        (∀ x ∈ Ω, x * x = 1) ∧
        Ω ≤ ((S' : Subgroup Y).subgroupOf K.1).map (QuotientGroup.mk' (Subgroup.center K.1)) ∧
        (∀ x ∈ ((S' : Subgroup Y).subgroupOf K.1).map
            (QuotientGroup.mk' (Subgroup.center K.1)), x * x = 1 → x ∈ Ω) ∧
        IsMulCommutative Ω ∧ 4 ≤ Nat.card Ω ∧
        ∀ u ∈ Ω, ∀ v ∈ Ω, u ≠ 1 → v ≠ 1 →
          ∃ n : K.1, n ∈ Subgroup.normalizer ((Ω.comap (QuotientGroup.mk'
              (Subgroup.center K.1)) : Subgroup K.1) : Set K.1) ∧
            ((n : K.1 ⧸ Subgroup.center K.1))⁻¹ * u * (n : K.1 ⧸ Subgroup.center K.1) = v := by
    intro K
    obtain ⟨f, hf1, hf2⟩ := h.exists_proj K.2
    obtain ⟨S₀, hS₀⟩ := exists_sylow_component S' K.2
    have hS₀eq : (S₀ : Subgroup K.1) = (S' : Subgroup Y).subgroupOf K.1 := by
      ext x; exact hS₀ x
    obtain ⟨Ω, hΩ⟩ := goldschmidt_component_data K.2.1
      (hcomp K.1 (isComponentOf_top_of_isComponent K.2)) S₀
    rw [hS₀eq] at hΩ
    exact ⟨f, Ω, hf1, hf2, hΩ⟩
  choose f Ω hf1 hf2 hΩsq hΩT hΩT' hΩc hΩ4 hΩtr using hex
  have hQn : (CFSG.Open.pCore 2 Y).Normal := by
    have := CFSG.Monster.B.Recog.GoldschmidtApp.openPCore_characteristic Y
    infer_instance
  have hQS : CFSG.Open.pCore 2 Y ≤ (S' : Subgroup Y) := CFSG.Goldschmidt.G3a.pCore_le_sylow S'
  have hQC : ∀ K : {K : Subgroup Y // CFSG.IsComponent K}, CFSG.Open.pCore 2 Y ≤
      Subgroup.centralizer (K.1 : Set Y) := by
    intro K q hq
    rw [Subgroup.mem_centralizer_iff]
    intro k hk
    refine (h.pCore_comm hq ?_).symm
    rw [CFSG.ComponentClassification.AschbacherTheorem3.goldschmidtLayer_eq_layer]
    exact CFSG.LocalCores.component_le_layer K.2 hk
  have hdec : ∀ x ∈ X, ∃ w ∈ (S' : Subgroup Y), w ∈ goldschmidtLayer Y ∧ w * w = 1 ∧
      ∃ q ∈ CFSG.Open.pCore 2 Y, x = w * q := by
    intro x hx
    have hxR := hXR' x hx
    set Ω₁ : Subgroup Y := Subgroup.closure
      {t | t ∈ (S' : Subgroup Y) ⊓ goldschmidtLayer Y ∧ t ^ 2 = 1} with hΩ₁
    have hxsup : x ∈ Ω₁ ⊔ CFSG.Open.pCore 2 Y := by rw [sup_comm, ← hR']; exact hxR
    rw [← SetLike.mem_coe, Subgroup.mul_normal] at hxsup
    obtain ⟨w, hw, q, hq, hwq⟩ := Set.mem_mul.mp hxsup
    have hwle : Ω₁ ≤ (S' : Subgroup Y) ⊓ goldschmidtLayer Y := by
      rw [hΩ₁, Subgroup.closure_le]
      exact fun t ht => ht.1
    have hwR : w ∈ R' := by rw [hR']; exact Subgroup.mem_sup_right hw
    exact ⟨w, (hwle hw).1, (hwle hw).2, hR'sq w hwR, q, hq, hwq.symm⟩
  have hdecK : ∀ (K : {K : Subgroup Y // CFSG.IsComponent K}), ∀ x ∈ X,
      ∃ (k : K.1) (c q : Y), (k : Y) ∈ (S' : Subgroup Y) ∧ c ∈ (S' : Subgroup Y) ∧
        c ∈ Subgroup.centralizer (K.1 : Set Y) ∧ q ∈ CFSG.Open.pCore 2 Y ∧
        x = (k : Y) * c * q ∧ (k : K.1 ⧸ Subgroup.center K.1) ∈ Ω K := by
    intro K x hx
    obtain ⟨w, hwS, hwE, hww, q, hq, hxwq⟩ := hdec x hx
    obtain ⟨k0, hk, c, hc, hwkc⟩ := h.sylow_dec K.2 S' hwS
    have hck : c * k0 = k0 * c := (Subgroup.mem_centralizer_iff.mp hc.2 k0 hk.2).symm
    have h1 : k0 * k0 * (c * c) = 1 := by
      calc k0 * k0 * (c * c) = k0 * (k0 * c) * c := by group
        _ = k0 * (c * k0) * c := by rw [hck]
        _ = (k0 * c) * (k0 * c) := by group
        _ = 1 := by rw [← hwkc]; exact hww
    have h2 : k0 * k0 = (c * c)⁻¹ := eq_inv_of_mul_eq_one_left h1
    have hkk : k0 * k0 ∈ Subgroup.centralizer (K.1 : Set Y) := by
      rw [h2]; exact Subgroup.inv_mem _ (Subgroup.mul_mem _ hc.2 hc.2)
    refine ⟨⟨k0, hk.2⟩, c, q, hk.1, hc.1, hc.2, hq, by rw [hxwq, hwkc], ?_⟩
    apply hΩT' K
    · exact ⟨⟨k0, hk.2⟩, Subgroup.mem_subgroupOf.mpr hk.1, rfl⟩
    · have := (hf2 K (k0 * k0)).mpr hkk
      have hfk : f K k0 = ((⟨k0, hk.2⟩ : K.1) : K.1 ⧸ Subgroup.center K.1) :=
        hf1 K ⟨k0, hk.2⟩
      rw [map_mul, hfk] at this
      exact this
  have hmem : ∀ (K : {K : Subgroup Y // CFSG.IsComponent K}), ∀ x ∈ X, f K x ∈ Ω K := by
    intro K x hx
    obtain ⟨k, c, q, hkS, hcS, hcC, hq, hxe, hkΩ⟩ := hdecK K x hx
    have hfc : f K c = 1 := (hf2 K c).mpr hcC
    have hfq : f K q = 1 := (hf2 K q).mpr (hQC K hq)
    have hfk : f K (k : Y) = (k : K.1 ⧸ Subgroup.center K.1) := hf1 K k
    rw [hxe, map_mul, map_mul, hfc, hfq, mul_one, mul_one, hfk]
    exact hkΩ
  have hnontriv : ∀ x ∈ X, ∃ K : {K : Subgroup Y // CFSG.IsComponent K}, f K x ≠ 1 := by
    intro x hx
    by_contra hall
    push Not at hall
    obtain ⟨w, hwS, hwE, hww, q, hq, hxwq⟩ := hdec x hx
    have hwC : ∀ K : {K : Subgroup Y // CFSG.IsComponent K},
        w ∈ Subgroup.centralizer (K.1 : Set Y) := by
      intro K
      have hxC : x ∈ Subgroup.centralizer (K.1 : Set Y) := (hf2 K x).mp (hall K)
      have : w = x * q⁻¹ := by rw [hxwq]; group
      rw [this]
      exact Subgroup.mul_mem _ hxC (Subgroup.inv_mem _ (hQC K hq))
    have hwQ : w ∈ CFSG.Open.pCore 2 Y := by
      apply h.center_layer_le hwE
      intro e he
      have hE : goldschmidtLayer Y ≤ Subgroup.centralizer ({w} : Set Y) := by
        rw [CFSG.ComponentClassification.AschbacherTheorem3.goldschmidtLayer_eq_layer]
        refine sSup_le fun K hK k hk => ?_
        rw [Subgroup.mem_centralizer_singleton_iff]
        exact Subgroup.mem_centralizer_iff.mp (hwC ⟨K, hK⟩) k hk
      have := Subgroup.mem_centralizer_singleton_iff.mp (hE he)
      exact this.symm
    exact hXQ x hx (by rw [hxwq]; exact Subgroup.mul_mem _ hwQ hq)
  let N : {K : Subgroup Y // CFSG.IsComponent K} → Subgroup Y := fun K =>
    (Subgroup.normalizer (((Ω K).comap (QuotientGroup.mk' (Subgroup.center K.1)) :
      Subgroup K.1) : Set K.1)).map K.1.subtype
  have hΩ2 : ∀ K : {K : Subgroup Y // CFSG.IsComponent K}, ∃ m : ℕ, Nat.card (Ω K) = 2 ^ m := by
    intro K
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have hp : IsPGroup 2 (Ω K) := by
      rw [IsPGroup.iff_orderOf]
      intro g
      have hg2 : (g : K.1 ⧸ Subgroup.center K.1) * g = 1 := hΩsq K g g.2
      have hdvd : orderOf g ∣ 2 := orderOf_dvd_of_pow_eq_one (by
        apply Subtype.ext
        simpa [pow_two] using hg2)
      rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h1 | h1
      · exact ⟨0, by simpa using h1⟩
      · exact ⟨1, by simpa using h1⟩
    exact IsPGroup.iff_card.mp hp
  have htrans : ∀ K : {K : Subgroup Y // CFSG.IsComponent K}, ∀ u ∈ Ω K, ∀ v ∈ Ω K,
      u ≠ 1 → v ≠ 1 → ∃ n ∈ N K, f K n * u * (f K n)⁻¹ = v := by
    intro K u hu v hv hu1 hv1
    obtain ⟨m, hm, hmuv⟩ := hΩtr K u hu v hv hu1 hv1
    refine ⟨((m⁻¹ : K.1) : Y), ⟨m⁻¹, (Subgroup.normalizer _).inv_mem hm, rfl⟩, ?_⟩
    rw [hf1 K (m⁻¹)]
    rw [← hmuv]
    simp
  have hcross : ∀ K L : {K : Subgroup Y // CFSG.IsComponent K}, K ≠ L → ∀ n ∈ N K, f L n = 1 := by
    intro K L hKL n hn
    obtain ⟨m, hm, rfl⟩ := Subgroup.mem_map.mp hn
    apply (hf2 L _).mpr
    rw [Subgroup.mem_centralizer_iff]
    intro k hk
    exact components_commute L.2 K.2 (fun h' => hKL (Subtype.ext h'.symm)) k hk m m.2
  have hinv : ∀ K : {K : Subgroup Y // CFSG.IsComponent K}, ∀ n ∈ N K, ∀ x ∈ X,
      n * x * n⁻¹ ∈ X := by
    intro K n hn x hx
    obtain ⟨m, hm, rfl⟩ := Subgroup.mem_map.mp hn
    obtain ⟨k, c, q, hkS, hcS, hcC, hq, hxe, hkΩ⟩ := hdecK K x hx
    have hmk : (m * k * m⁻¹ : K.1) ∈ (Ω K).comap (QuotientGroup.mk' (Subgroup.center K.1)) :=
      (Subgroup.mem_normalizer_iff.mp hm k).mp (Subgroup.mem_comap.mpr hkΩ)
    have hmkΩ : (((m * k * m⁻¹ : K.1)) : K.1 ⧸ Subgroup.center K.1) ∈ Ω K := hmk
    obtain ⟨s, hsS, hs⟩ := hΩT K hmkΩ
    have hz : s⁻¹ * (m * k * m⁻¹) ∈ Subgroup.center K.1 := by
      have := hs
      rw [QuotientGroup.mk'_apply] at this
      exact QuotientGroup.eq.mp this
    have hzS : (((s⁻¹ * (m * k * m⁻¹) : K.1)) : Y) ∈ (S' : Subgroup Y) :=
      h.center_le_sylow K.2 S' (s⁻¹ * (m * k * m⁻¹) : K.1).2
        (fun k' hk' => (congrArg Subtype.val (Subgroup.mem_center_iff.mp hz ⟨k', hk'⟩)).symm)
    have hkS' : (((m * k * m⁻¹ : K.1)) : Y) ∈ (S' : Subgroup Y) := by
      have h1 : (((m * k * m⁻¹ : K.1)) : Y) = (s : Y) * (((s⁻¹ * (m * k * m⁻¹) : K.1)) : Y) := by
        simp
      rw [h1]
      exact (S' : Subgroup Y).mul_mem (Subgroup.mem_subgroupOf.mp hsS) hzS
    have hnc : (m : Y) * c * (m : Y)⁻¹ = c := by
      have := (Subgroup.mem_centralizer_iff.mp hcC (m : Y) m.2)
      calc (m : Y) * c * (m : Y)⁻¹ = c * (m : Y) * (m : Y)⁻¹ := by rw [this]
        _ = c := by group
    have hnq : (m : Y) * q * (m : Y)⁻¹ ∈ CFSG.Open.pCore 2 Y := hQn.conj_mem q hq (m : Y)
    have hxS : (m : Y) * x * (m : Y)⁻¹ ∈ (S' : Subgroup Y) := by
      have : (m : Y) * x * (m : Y)⁻¹ =
          (((m * k * m⁻¹ : K.1)) : Y) * ((m : Y) * c * (m : Y)⁻¹) * ((m : Y) * q * (m : Y)⁻¹) := by
        rw [hxe]; simp only [Subgroup.coe_mul, Subgroup.coe_inv]; group
      rw [this, hnc]
      exact (S' : Subgroup Y).mul_mem ((S' : Subgroup Y).mul_mem hkS' hcS) (hQS hnq)
    have hxR : (m : Y) * x * (m : Y)⁻¹ ∈ R' := by
      have := hcl x (hXR' x hx) ((m : Y)⁻¹) (by simpa using hxS)
      simpa using this
    have := hXcl x hx ((m : Y)⁻¹) (by simpa using hxR)
    simpa using this
  exact five_contradiction X hX (fun K => K.1 ⧸ Subgroup.center K.1) f N Ω hΩ2
    (fun K => hΩ4 K) htrans hinv hcross hmem hnontriv


open CFSG.GH74.Uniqueness.SU.K.R6 in
theorem ki4
    : CFSG.GH74.Uniqueness.SU.K.KI4 := by
  intro H _ _ hGH hodd S R hRS hRel hRcard hRcl X₀ hX₀R hX₀card hX₀ord hX₀gen hX₀conj hX₀cl
  have hRab : IsMulCommutative R := hRel.1
  have hOH : CFSG.oddCore H = ⊥ := by
    have : CFSG.oddCore H = CFSG.pPrimeCore 2 H := by
      unfold CFSG.oddCore CFSG.pPrimeCore
      congr 1
      ext K
      simp only [Set.mem_ofPred_eq, Nat.coprime_two_left]
    rw [this]; exact hodd
  set M : Subgroup H := Subgroup.normalClosure (R : Set H) with hM
  have hRM : R ≤ M := Subgroup.le_normalClosure
  have hMn : M.Normal := Subgroup.normalClosure_normal
  have hOM : CFSG.oddCore ↥M = ⊥ := by
    have h1 := CFSG.ComponentClassification.OddCore.normal_intersection H M
    have h' : CFSG.Open.componentClassificationOddCore H = ⊥ := hOH
    rw [h', inf_bot_eq] at h1
    exact (Subgroup.map_eq_bot_iff_of_injective _ (Subgroup.subtype_injective _)).1 h1
  obtain ⟨hsup, hRq, hcomp⟩ := CFSG.ComponentClassification.AschbacherTheorem3.goldschmidt_subgroup
    CFSG.Goldschmidt.topStatement S hRS hRab hRcl rfl hOM
  let S' : Sylow 2 ↥M := CFSG.BenderSuzuki.External.hallSylowSubgroupOfNormal S M
  have hS'mem : ∀ y : ↥M, y ∈ (S' : Subgroup ↥M) ↔ (y : H) ∈ (S : Subgroup H) := fun y => Iff.rfl
  have hsetup : Setup ↥M := ⟨hOM, hsup⟩
  have hQHn : ((CFSG.Open.pCore 2 ↥M).map M.subtype).Normal := by
    have := CFSG.Monster.B.Recog.GoldschmidtApp.normal_map_of_characteristic (X := H) (M := M)
      (MulEquiv.refl ↥M) (CFSG.Monster.B.Recog.GoldschmidtApp.openPCore_characteristic ↥M)
    simpa using this
  by_cases hcase : ∃ x ∈ X₀, x ∈ (CFSG.Open.pCore 2 ↥M).map M.subtype
  ·
    obtain ⟨x₀, hx₀, hx₀Q⟩ := hcase
    have hX₀Q : X₀ ⊆ ((CFSG.Open.pCore 2 ↥M).map M.subtype : Set H) := by
      intro y hy
      obtain ⟨g, hg⟩ := hX₀conj x₀ hx₀ y hy
      rw [← hg]
      have := hQHn.conj_mem x₀ hx₀Q g⁻¹
      simpa using this
    have hRQ : R ≤ (CFSG.Open.pCore 2 ↥M).map M.subtype := by
      rw [← hX₀gen, Subgroup.closure_le]; exact hX₀Q
    have hMQ : M ≤ (CFSG.Open.pCore 2 ↥M).map M.subtype :=
      Subgroup.normalClosure_le_normal hRQ
    have hQtop : CFSG.Open.pCore 2 ↥M = ⊤ := by
      rw [eq_top_iff]
      intro m _
      obtain ⟨q, hq, hqm⟩ := hMQ m.2
      have : q = m := Subtype.ext hqm
      rw [← this]; exact hq
    have hR'top : R.subgroupOf M = ⊤ := by
      rw [eq_top_iff, hRq, hQtop]
      exact le_sup_left
    have hMR : M ≤ R := by
      intro m hm
      have : (⟨m, hm⟩ : ↥M) ∈ R.subgroupOf M := by rw [hR'top]; trivial
      exact Subgroup.mem_subgroupOf.mp this
    have hReq : R = M := le_antisymm hRM hMR
    intro g r hr
    rw [hReq] at hr ⊢
    have := hMn.conj_mem r hr g⁻¹
    simpa using this
  ·
    exfalso
    push Not at hcase
    let Xset : Set ↥M := {y | (y : H) ∈ X₀}
    have hXfin : Xset.Finite := Set.toFinite _
    let X : Finset ↥M := hXfin.toFinset
    have hXmem : ∀ y : ↥M, y ∈ X ↔ (y : H) ∈ X₀ := by
      intro y; simp [X, Xset]
    have hXcard : X.card = 5 := by
      have h1 : Xset.ncard = X₀.ncard := by
        apply Set.ncard_preimage_of_injective_subset_range M.subtype_injective
        intro x hx
        exact ⟨⟨x, hRM (hX₀R hx)⟩, rfl⟩
      rw [← hX₀card, ← h1, ← Set.ncard_coe_finset]
      simp [X]
    refine ki4_core hsetup S' (R.subgroupOf M) ?_ hRq hcomp ?_ X hXcard ?_ ?_ ?_
    · intro r hr
      have := hRel.2 (r : H) (Subgroup.mem_subgroupOf.mp hr)
      apply Subtype.ext
      simpa [pow_two] using this
    · intro r hr y hy
      have := hRcl (r : H) (Subgroup.mem_subgroupOf.mp hr) (y : H) hy
      exact Subgroup.mem_subgroupOf.mpr (by simpa using this)
    · intro x hx
      exact Subgroup.mem_subgroupOf.mpr (hX₀R ((hXmem x).mp hx))
    · intro x hx y hy
      have hxX₀ : (x : H) ∈ X₀ := (hXmem x).mp hx
      have := hX₀cl (x : H) hxX₀ (y : H) (Subgroup.mem_subgroupOf.mp hy)
      exact (hXmem _).mpr (by simpa using this)
    · intro x hx hxQ
      exact hcase (x : H) ((hXmem x).mp hx) ⟨x, hxQ, rfl⟩

end CFSG.GH74.Uniqueness.SU.K.R4
