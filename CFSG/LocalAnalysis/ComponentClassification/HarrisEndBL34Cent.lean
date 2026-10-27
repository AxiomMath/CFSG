module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisEndBL34Center
public import CFSG.LocalAnalysis.ComponentClassification.HarrisEndBSub1
public import CFSG.LocalAnalysis.ComponentClassification.HarrisEndL34Facts

public noncomputable section

namespace CFSG.ComponentClassification.HarrisLit

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer CFSG.ABGLocalTools HarrisEnd
open Standing.Setup42

variable {X : Type} [Group X] [Finite X] {t : X} {L : Subgroup X} {p f : ℕ} {S : Subgroup X}
  {w z : X} {V : Subgroup X} {i j : ℕ}

namespace EndB.LLayer

variable {hs : Setting46e t L p f S w z V i j}
  {π : ↥(layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j))) →* PSL3Four.S}

theorem withKernel_eq (hL : LLayer hs π) :
    GrSLit.withKernel (layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j))) =
      layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)) ⊔
        pCore 2 (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)) := by
  rw [GrSLit.withKernel, ← hs.centralizer_layer_eq hL.h412]
  congr 1
  ext g
  constructor
  · rintro ⟨-, hg⟩
    rw [mem_centralizer_iff]
    intro e he
    have h1 := hg e he
    rw [Setting46e.pPrimeCore_layer_eq_bot, Subgroup.map_bot, mem_bot] at h1
    have h2 : g⁻¹ * e * g = e := by
      calc g⁻¹ * e * g = e * (e⁻¹ * g⁻¹ * e * g) := by group
        _ = e := by rw [h1, mul_one]
    calc e * g = g * (g⁻¹ * e * g) := by group
      _ = g * e := by rw [h2]
  · intro hg
    refine ⟨?_, fun e he => ?_⟩
    · rw [mem_normalizer_iff]
      intro e
      have hn : (layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j))).Normal := inferInstance
      constructor
      · intro he
        exact hn.conj_mem e he g
      · intro he
        have := hn.conj_mem _ he g⁻¹
        rwa [show g⁻¹ * (g * e * g⁻¹) * g⁻¹⁻¹ = e by group] at this
    · rw [Setting46e.pPrimeCore_layer_eq_bot, Subgroup.map_bot, mem_bot]
      have h1 := mem_centralizer_iff.mp hg e he
      calc e⁻¹ * g⁻¹ * e * g = e⁻¹ * g⁻¹ * (e * g) := by group
        _ = 1 := by rw [h1]; group

theorem _root_.CFSG.ComponentClassification.HarrisLit.EndB.card_centralizer_conj_S
    {x r c : Equiv.Perm (Fin 42)} (hc : c ∈ PSL3Four.R)
    (hx : x = c * r * c⁻¹) :
    Nat.card ↥(centralizer {x} ⊓ PSL3Four.S) = Nat.card ↥(centralizer {r} ⊓ PSL3Four.S) := by
  obtain ⟨e⟩ := nonempty_centralizer_conj_equiv hc hx
  exact Nat.card_congr e.toEquiv

theorem isL34Unitary (hL : LLayer hs π)
    {g : MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)} (hg2 : g ^ 2 = 1)
    {c : Equiv.Perm (Fin 42)} (hc : c ∈ PSL3Four.R)
    (hgc : ((hL.rho g : PSL3Four.R) : Equiv.Perm (Fin 42)) = c * PSL3Four.r₄ * c⁻¹) :
    GrSLit.IsL34Unitary (layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j))) g := by
  have hn : (layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j))).Normal := inferInstance
  set r : Equiv.Perm (Fin 42) := ((hL.rho g : PSL3Four.R) : Equiv.Perm (Fin 42)) with hr
  refine ⟨?_, by rw [← sq]; exact hg2, ?_, ?_⟩
  · rw [mem_normalizer_iff]
    intro e
    refine ⟨fun he => hn.conj_mem e he g, fun he => ?_⟩
    have := hn.conj_mem _ he g⁻¹
    rwa [show g⁻¹ * (g * e * g⁻¹) * g⁻¹⁻¹ = e by group] at this
  · rw [hL.withKernel_eq, ← hL.rho_mem_S_iff]
    intro h
    apply PSL3Four.not_mem_S_r₄
    have := PSL3Four.conj_mem_S (inv_mem hc) h
    rwa [← hr, hgc, show c⁻¹ * (c * PSL3Four.r₄ * c⁻¹) * c⁻¹⁻¹ = PSL3Four.r₄ by group] at this
  ·
    set Ys : Subgroup ↥PSL3Four.S := (centralizer {r}).comap PSL3Four.S.subtype with hYs
    set Y : Subgroup ↥(layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j))) := Ys.comap π
      with hY
    have hA : ∀ e : ↥(layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j))),
        (e : MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j))⁻¹ * g⁻¹ * e * g ∈
          GrSLit.zStarIn (layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j))) ↔ e ∈ Y := by
      intro e
      have hae : g⁻¹ * (e : MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)) * g⁻¹⁻¹ ∈
          layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)) :=
        hn.conj_mem _ e.2 _
      set a : ↥(layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j))) := ⟨_, hae⟩ with ha
      have hπa := hL.rho_conj g⁻¹ e a rfl
      rw [map_inv, Subgroup.coe_inv, inv_inv, ← hr] at hπa
      have heq : (e : MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j))⁻¹ * g⁻¹ * e * g =
          (layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j))).subtype (e⁻¹ * a) := by
        rw [Subgroup.coe_subtype, Subgroup.coe_mul, Subgroup.coe_inv, ha]
        group
      rw [heq, zStarIn_eq, mem_map_iff_mem (subtype_injective _), ← hL.ker, MonoidHom.mem_ker,
        hY, mem_comap, hYs, mem_comap, Subgroup.coe_subtype, mem_centralizer_singleton_iff,
        map_mul, map_inv, inv_mul_eq_one]
      constructor
      · intro h
        have h1 : (π e : Equiv.Perm (Fin 42)) = π a := congrArg Subtype.val h
        rw [← hπa] at h1
        calc (π e : Equiv.Perm (Fin 42)) * r = r * (r⁻¹ * (π e : Equiv.Perm (Fin 42)) * r) := by
              group
          _ = r * π e := by rw [← h1]
      · intro h
        apply Subtype.ext
        rw [← hπa]
        calc (π e : Equiv.Perm (Fin 42)) = r⁻¹ * (r * π e) := by group
          _ = r⁻¹ * ((π e : Equiv.Perm (Fin 42)) * r) := by rw [h]
          _ = r⁻¹ * π e * r := by group
    have hYs72 : Nat.card Ys = 72 := by
      have h1 : Nat.card Ys = Nat.card ↥(centralizer {r} ⊓ PSL3Four.S) := by
        rw [hYs, ← Subgroup.subgroupOf, ← Subgroup.inf_subgroupOf_right]
        exact Nat.card_congr (subgroupOfEquivOfLe inf_le_right).toEquiv
      rw [h1, card_centralizer_conj_S hc hgc]
      exact PSL3Four.card_C₄
    have hcardE := Subgroup.card_ker_mul_card_range π
    rw [MonoidHom.range_eq_top.mpr hL.surj, card_top] at hcardE
    have hYidx : Y.index = Ys.index := Subgroup.index_comap_of_surjective Ys hL.surj
    have h1 := Subgroup.card_mul_index Y
    have h2 := Subgroup.card_mul_index Ys
    have hcardY : Nat.card Y = Nat.card π.ker * Nat.card Ys := by
      have hpos : 0 < Ys.index := Nat.pos_of_ne_zero (Subgroup.index_ne_zero_of_finite)
      rw [hYidx] at h1
      apply Nat.eq_of_mul_eq_mul_right hpos
      rw [h1, mul_assoc (Nat.card π.ker), h2, hcardE]
    have hZ : Nat.card (GrSLit.zStarIn (layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)))) =
        Nat.card π.ker := by
      rw [zStarIn_eq, hL.ker, Subgroup.card_map_of_injective (subtype_injective _)]
    rw [hZ, Nat.card_congr (Equiv.subtypeEquivRight hA)]
    change Nat.card ↥Y = _
    rw [hcardY, hYs72, mul_comm]

theorem _root_.CFSG.ComponentClassification.HarrisLit.EndB.isPGroup_zpowers_of_sq {G : Type*}
    [Group G] {g : G} (hg2 : g ^ 2 = 1) : IsPGroup 2 ↥(zpowers g) := by
  rintro ⟨_, k, rfl⟩
  refine ⟨1, Subtype.ext ?_⟩
  simp only [pow_one, Subgroup.coe_pow, Subgroup.coe_one]
  rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hg2, one_zpow]

theorem exists_sylow_of_sq (_hL : LLayer hs π) {g : MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)}
    (hg2 : g ^ 2 = 1) :
    ∃ P : Subgroup (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)),
      GrSLit.IsSylowTwoIn P (layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j))) ∧
      g ∈ normalizer (P : Set (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j))) ∧
      ∀ B : Subgroup (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)),
        B ≤ layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)) ⊓ centralizer {g} →
        IsPGroup 2 B → Nat.card B ≤ Nat.card ↥(P ⊓ centralizer {g}) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hn : (layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j))).Normal := inferInstance
  obtain ⟨B₀, hB₀⟩ := exists_isSylowOf 2
    (layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)) ⊓ centralizer {g})
  have hgN : zpowers g ≤ normalizer (B₀ : Set (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j))) := by
    rw [zpowers_le, mem_normalizer_iff]
    intro k
    have hkg : ∀ k ∈ B₀, g * k * g⁻¹ = k := fun k hk => by
      rw [← mem_centralizer_singleton_iff.mp (mem_inf.mp (hB₀.le hk)).2]
      group
    refine ⟨fun hk => by rw [hkg k hk]; exact hk, fun hk => ?_⟩
    have := hkg _ hk
    have h1 : k = g * k * g⁻¹ := by
      calc k = g⁻¹ * (g * k * g⁻¹) * g := by group
        _ = g⁻¹ * (g * (g * k * g⁻¹) * g⁻¹) * g := by rw [this]
        _ = g * k * g⁻¹ := by
          rw [show g⁻¹ * (g * (g * k * g⁻¹) * g⁻¹) * g = g * k * g⁻¹ by group]
    rw [h1]
    exact hk
  have hB : IsPGroup 2 ↥(B₀ ⊔ zpowers g) :=
    IsPGroup.to_sup_of_normal_left' hB₀.isPGroup (isPGroup_zpowers_of_sq hg2) hgN
  obtain ⟨A, hA, hBA⟩ := exists_isSylowOf_ge hB (le_top : B₀ ⊔ zpowers g ≤ ⊤)
  have hPE := hA.inf_of_le_normalizer (le_top :
    layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)) ≤ ⊤) (fun x _ => by
      rw [mem_normalizer_iff]
      intro e
      refine ⟨fun he => hn.conj_mem e he x, fun he => ?_⟩
      have := hn.conj_mem _ he x⁻¹
      rwa [show x⁻¹ * (x * e * x⁻¹) * x⁻¹⁻¹ = e by group] at this)
  obtain ⟨Q, hQ⟩ := hPE.exists_sylow_eq_subgroupOf
  have hgA : g ∈ A := hBA (mem_sup_right (mem_zpowers g))
  refine ⟨A ⊓ layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)), ⟨inf_le_right, Q, hQ⟩, ?_, ?_⟩
  · rw [mem_normalizer_iff]
    intro k
    constructor
    · intro hk
      exact mem_inf.mpr ⟨mul_mem (mul_mem hgA (mem_inf.mp hk).1) (inv_mem hgA),
        hn.conj_mem _ (mem_inf.mp hk).2 g⟩
    · intro hk
      have h1 := (mem_inf.mp hk).1
      have h2 := (mem_inf.mp hk).2
      have hk' : k = g⁻¹ * (g * k * g⁻¹) * g⁻¹⁻¹ := by group
      refine mem_inf.mpr ⟨?_, ?_⟩
      · rw [hk']
        exact mul_mem (mul_mem (inv_mem hgA) h1) (inv_mem (inv_mem hgA))
      · rw [hk']
        exact hn.conj_mem _ h2 _
  · intro B hBle hB2
    calc Nat.card B ≤ twoPart (layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)) ⊓
          centralizer {g}) := card_le_twoPart hB2 hBle
      _ = Nat.card B₀ := hB₀.card_eq.symm
      _ ≤ _ := Subgroup.card_le_of_le (fun k hk => mem_inf.mpr
          ⟨mem_inf.mpr ⟨hBA (mem_sup_left hk), (mem_inf.mp (hB₀.le hk)).1⟩,
            (mem_inf.mp (hB₀.le hk)).2⟩)

theorem card_le_eight_of_unitary
    (hUC : GrSLit.L34UnitaryCentralizerFact) (hL : LLayer hs π)
    {g : MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)} (hg2 : g ^ 2 = 1)
    {c : Equiv.Perm (Fin 42)} (hc : c ∈ PSL3Four.R)
    (hgc : ((hL.rho g : PSL3Four.R) : Equiv.Perm (Fin 42)) = c * PSL3Four.r₄ * c⁻¹) :
    ∃ P : Subgroup (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)),
      P ≤ layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)) ∧
      Nat.card ↥(P ⊓ centralizer {g}) = 8 ∧
      ∀ B : Subgroup (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)),
        B ≤ layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)) ⊓ centralizer {g} →
        IsPGroup 2 B → Nat.card B ≤ 8 := by
  obtain ⟨P, hP, hgP, hB⟩ := hL.exists_sylow_of_sq hg2
  have h8 := (hUC (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j))
    (layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j))) P g
    (Subgroup.isPerfect_iff.mp hL.isPerfect) hL.isL34Type (hL.isL34Unitary hg2 hc hgc) hP
    hgP).2.1
  exact ⟨P, hP.1, h8, fun B hBle hB2 => h8 ▸ hB B hBle hB2⟩

instance _root_.CFSG.ComponentClassification.HarrisLit.EndB.normal_SR :
    (PSL3Four.S.subgroupOf PSL3Four.R).Normal :=
  ⟨fun n hn r => by
    rw [mem_subgroupOf] at hn ⊢
    simpa using PSL3Four.conj_mem_S r.2 hn⟩

theorem _root_.CFSG.ComponentClassification.HarrisLit.EndB.index_SR :
    (PSL3Four.S.subgroupOf PSL3Four.R).index = 12 := by
  have h := Subgroup.card_mul_index (PSL3Four.S.subgroupOf PSL3Four.R)
  rw [Nat.card_congr (subgroupOfEquivOfLe PSL3Four.S_le_R).toEquiv, PSL3Four.card_S,
    PSL3Four.card_R] at h
  omega

@[expose] def psi (hL : LLayer hs π) :
    MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j) →* ↥PSL3Four.R ⧸
      PSL3Four.S.subgroupOf PSL3Four.R :=
  (QuotientGroup.mk' (PSL3Four.S.subgroupOf PSL3Four.R)).comp hL.rho

theorem mem_ker_psi (hL : LLayer hs π)
    (g : MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)) :
    g ∈ hL.psi.ker ↔ g ∈ layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)) ⊔
      pCore 2 (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)) := by
  rw [MonoidHom.mem_ker, psi, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
    QuotientGroup.eq_one_iff, mem_subgroupOf, hL.rho_mem_S_iff]

theorem card_le_four_mul (hL : LLayer hs π)
    {B : Subgroup (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j))} (hB : IsPGroup 2 B) :
    Nat.card B ≤ 4 * Nat.card ↥(B ⊓ (layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)) ⊔
      pCore 2 (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)))) := by
  have h := Subgroup.card_ker_mul_card_range (hL.psi.comp B.subtype)
  rw [MonoidHom.range_comp, Subgroup.range_subtype, ← MonoidHom.comap_ker] at h
  have hker : Nat.card ↥(hL.psi.ker.comap B.subtype) = Nat.card ↥(B ⊓
      (layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)) ⊔
        pCore 2 (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)))) := by
    have heq : hL.psi.ker = layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)) ⊔
        pCore 2 (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)) := by
      ext g
      exact hL.mem_ker_psi g
    rw [heq, ← Subgroup.subgroupOf, ← Subgroup.inf_subgroupOf_left]
    exact Nat.card_congr (subgroupOfEquivOfLe inf_le_left).toEquiv
  rw [hker] at h
  have h4 : Nat.card ↥(B.map hL.psi) ≤ 4 := by
    have hdvd := Subgroup.card_subgroup_dvd_card (B.map hL.psi)
    rw [← Subgroup.index, index_SR] at hdvd
    obtain ⟨k, hk⟩ := (hB.map hL.psi).exists_card_eq
    rw [hk] at hdvd ⊢
    have hk3 : k ≤ 2 := by
      by_contra hk3
      have : 2 ^ 3 ∣ 12 := (pow_dvd_pow 2 (by omega)).trans hdvd
      norm_num at this
    calc 2 ^ k ≤ 2 ^ 2 := Nat.pow_le_pow_right (by norm_num) hk3
      _ = 4 := by norm_num
  rw [← h, mul_comm 4]
  exact Nat.mul_le_mul_left _ h4

theorem card_le_32_of_unitary
    (hUC : GrSLit.L34UnitaryCentralizerFact) (hL : LLayer hs π)
    (hQE : pCore 2 (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)) ≤
      layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)))
    {g : MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)} (hg2 : g ^ 2 = 1)
    {c : Equiv.Perm (Fin 42)} (hc : c ∈ PSL3Four.R)
    (hgc : ((hL.rho g : PSL3Four.R) : Equiv.Perm (Fin 42)) = c * PSL3Four.r₄ * c⁻¹)
    {B : Subgroup (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j))} (hB : B ≤ centralizer {g})
    (hB2 : IsPGroup 2 B) : Nat.card B ≤ 32 := by
  obtain ⟨P, -, -, h8⟩ := hL.card_le_eight_of_unitary hUC hg2 hc hgc
  have h1 := hL.card_le_four_mul hB2
  rw [sup_of_le_left hQE] at h1
  have h2 := h8 (B ⊓ layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)))
    (fun x hx => mem_inf.mpr ⟨(mem_inf.mp hx).2, hB (mem_inf.mp hx).1⟩) (hB2.to_le inf_le_left)
  omega

theorem exists_card_ge_four_mul (_hL : LLayer hs π)
    {g : MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)}
    {A₀ : Subgroup (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j))}
    (hA₀ : A₀ ≤ centralizer {g} ⊓ (layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)) ⊔
      pCore 2 (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)))) (hA₀2 : IsPGroup 2 A₀)
    {a b : MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)} (ha : a ∈ centralizer {g})
    (hb : b ∈ centralizer {g}) (ha2 : a ^ 2 = 1) (hb2 : b ^ 2 = 1) (hab : a * b = b * a)
    (haE : a ∉ layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)) ⊔
      pCore 2 (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)))
    (hbE : b ∉ layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)) ⊔
      pCore 2 (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)))
    (habE : a * b ∉ layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)) ⊔
      pCore 2 (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j))) :
    ∃ U : Subgroup (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)),
      U ≤ centralizer {g} ∧ IsPGroup 2 U ∧ 4 * Nat.card A₀ ≤ Nat.card U := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set F := layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)) ⊔
    pCore 2 (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)) with hF
  have hFn : F.Normal := by
    rw [hF]
    infer_instance
  have hab2 : IsPGroup 2 ↥(zpowers a ⊔ zpowers b) := by
    refine IsPGroup.to_sup_of_normal_left' (isPGroup_zpowers_of_sq ha2)
      (isPGroup_zpowers_of_sq hb2) ?_
    rw [zpowers_le, mem_normalizer_iff]
    intro k
    have hcomm : ∀ k ∈ zpowers a, b * k * b⁻¹ = k := by
      rintro _ ⟨n, rfl⟩
      have hba : b * a * b⁻¹ = a := by rw [← hab]; group
      change b * a ^ n * b⁻¹ = a ^ n
      rw [← conj_zpow, hba]
    refine ⟨fun hk => by rw [hcomm k hk]; exact hk, fun hk => ?_⟩
    rw [show k = b * k * b⁻¹ by
      have := hcomm _ hk
      calc k = b⁻¹ * (b * k * b⁻¹) * b := by group
        _ = b⁻¹ * (b * (b * k * b⁻¹) * b⁻¹) * b := by rw [this]
        _ = b * k * b⁻¹ := by group]
    exact hk
  obtain ⟨U, hU, hUab⟩ := exists_isSylowOf_ge hab2 (sup_le (zpowers_le.mpr ha) (zpowers_le.mpr hb))
  have haU : a ∈ U := hUab (mem_sup_left (mem_zpowers a))
  have hbU : b ∈ U := hUab (mem_sup_right (mem_zpowers b))
  have hB₁ := hU.inf_of_le_normalizer (inf_le_left : centralizer {g} ⊓ F ≤ centralizer {g})
    (fun x hx => by
      rw [mem_normalizer_iff]
      intro k
      constructor
      · intro hk
        exact mem_inf.mpr ⟨mul_mem (mul_mem hx (mem_inf.mp hk).1) (inv_mem hx),
          hFn.conj_mem _ (mem_inf.mp hk).2 x⟩
      · intro hk
        have hk' : k = x⁻¹ * (x * k * x⁻¹) * x⁻¹⁻¹ := by group
        refine mem_inf.mpr ⟨?_, ?_⟩
        · rw [hk']
          exact mul_mem (mul_mem (inv_mem hx) (mem_inf.mp hk).1) (inv_mem (inv_mem hx))
        · rw [hk']
          exact hFn.conj_mem _ (mem_inf.mp hk).2 _)
  set B₁ := U ⊓ (centralizer {g} ⊓ F) with hB₁def
  have h8' : Nat.card A₀ ≤ Nat.card B₁ := by
    have := card_le_twoPart (K := centralizer {g} ⊓ F) hA₀2 hA₀
    rw [hB₁.card_eq]
    exact this
  have hconjB : ∀ y ∈ U, y ∈ centralizer {g} → ∀ k ∈ B₁, y * k * y⁻¹ ∈ B₁ := by
    intro y hyU hyC k hk
    have hkU : k ∈ U := (mem_inf.mp hk).1
    have hkC : k ∈ centralizer {g} := (mem_inf.mp (mem_inf.mp hk).2).1
    have hkF : k ∈ F := (mem_inf.mp (mem_inf.mp hk).2).2
    exact mem_inf.mpr ⟨mul_mem (mul_mem hyU hkU) (inv_mem hyU), mem_inf.mpr
      ⟨mul_mem (mul_mem hyC hkC) (inv_mem hyC), hFn.conj_mem _ hkF y⟩⟩
  have ha2' : a ^ 2 ∈ B₁ := by rw [ha2]; exact one_mem _
  have haB : a ∉ B₁ := fun h => haE (mem_inf.mp (mem_inf.mp h).2).2
  have hK₁ := card_sup_zpowers (hconjB a haU ha) ha2' haB
  have hainv : a⁻¹ = a := inv_eq_of_mul_eq_one_right (by rw [← sq, ha2])
  have hba : b * a * b⁻¹ = a := by rw [← hab]; group
  have hnK₁ : ∀ k ∈ B₁ ⊔ zpowers a, b * k * b⁻¹ ∈ B₁ ⊔ zpowers a := by
    intro k hk
    rcases (mem_sup_zpowers_iff (hconjB a haU ha) ha2').mp hk with h | h
    · exact mem_sup_left (hconjB b hbU hb k h)
    · rw [show b * k * b⁻¹ = (b * (k * a⁻¹) * b⁻¹) * (b * a * b⁻¹) by group, hba]
      exact mul_mem (mem_sup_left (hconjB b hbU hb _ h)) (mem_sup_right (mem_zpowers a))
  have hb2' : b ^ 2 ∈ B₁ ⊔ zpowers a := by rw [hb2]; exact one_mem _
  have hbK : b ∉ B₁ ⊔ zpowers a := by
    intro h
    rcases (mem_sup_zpowers_iff (hconjB a haU ha) ha2').mp h with h | h
    · exact hbE (mem_inf.mp (mem_inf.mp h).2).2
    · apply habE
      have := (mem_inf.mp (mem_inf.mp h).2).2
      rw [hainv] at this
      rw [hab]
      exact this
  have hK₂ := card_sup_zpowers hnK₁ hb2' hbK
  have hle : B₁ ⊔ zpowers a ⊔ zpowers b ≤ U :=
    sup_le (sup_le inf_le_left (zpowers_le.mpr haU)) (zpowers_le.mpr hbU)
  have := Subgroup.card_le_of_le hle
  exact ⟨U, hU.le, hU.isPGroup, by omega⟩

theorem exists_card_ge_32
    (hUC : GrSLit.L34UnitaryCentralizerFact) (hL : LLayer hs π)
    {g : MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)} (hg2 : g ^ 2 = 1)
    {c : Equiv.Perm (Fin 42)} (hc : c ∈ PSL3Four.R)
    (hgc : ((hL.rho g : PSL3Four.R) : Equiv.Perm (Fin 42)) = c * PSL3Four.r₄ * c⁻¹)
    {a b : MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)} (ha : a ∈ centralizer {g})
    (hb : b ∈ centralizer {g}) (ha2 : a ^ 2 = 1) (hb2 : b ^ 2 = 1) (hab : a * b = b * a)
    (haE : a ∉ layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)) ⊔
      pCore 2 (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)))
    (hbE : b ∉ layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)) ⊔
      pCore 2 (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)))
    (habE : a * b ∉ layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)) ⊔
      pCore 2 (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j))) :
    ∃ U : Subgroup (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)),
      U ≤ centralizer {g} ∧ IsPGroup 2 U ∧ 32 ≤ Nat.card U := by
  obtain ⟨P, hPE, h8, -⟩ := hL.card_le_eight_of_unitary hUC hg2 hc hgc
  have hP2 : IsPGroup 2 ↥(P ⊓ centralizer {g}) := IsPGroup.of_card (n := 3) (by rw [h8]; norm_num)
  obtain ⟨U, hU, hU2, hcard⟩ := hL.exists_card_ge_four_mul (A₀ := P ⊓ centralizer {g})
    (fun x hx => mem_inf.mpr ⟨(mem_inf.mp hx).2, mem_sup_left (hPE (mem_inf.mp hx).1)⟩) hP2
    ha hb ha2 hb2 hab haE hbE habE
  exact ⟨U, hU, hU2, by rw [h8] at hcard; omega⟩

end EndB.LLayer

end CFSG.ComponentClassification.HarrisLit
