module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit415Dih
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit415AutInputs
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit415W0Sylow

public noncomputable section

namespace CFSG.ComponentClassification.HarrisLit

open CFSG Subgroup DihedralGroup CFSG.ABGLocalTools

namespace L415

namespace IsProd

variable {G : Type} [Group G] [Finite G] {E K₁ K₂ : Subgroup G} {s : G}

omit [Finite G] in
theorem diag_conj (h : IsProd E K₁ K₂ s) {g : G} (hgs : g * s = s * g) {k : G} (hk : k ∈ K₁)
    (hk' : g * k * g⁻¹ ∈ K₁) :
    h.diag ⟨g * k * g⁻¹, hk'⟩ = g * h.diag ⟨k, hk⟩ * g⁻¹ := by
  rw [diag_apply, diag_apply]
  have h1 : g⁻¹ * s⁻¹ * g = s⁻¹ := by
    calc g⁻¹ * s⁻¹ * g = g⁻¹ * (s⁻¹ * (g * s) * s⁻¹) := by group
      _ = g⁻¹ * (s⁻¹ * (s * g) * s⁻¹) := by rw [hgs]
      _ = s⁻¹ := by group
  have h2 : g⁻¹ * s = s * g⁻¹ := by
    calc g⁻¹ * s = g⁻¹ * (s * g) * g⁻¹ := by group
      _ = g⁻¹ * (g * s) * g⁻¹ := by rw [hgs]
      _ = s * g⁻¹ := by group
  calc g * k * g⁻¹ * (s⁻¹ * (g * k * g⁻¹) * s) = g * k * (g⁻¹ * s⁻¹ * g) * k * (g⁻¹ * s) := by
        group
    _ = g * k * s⁻¹ * k * (s * g⁻¹) := by rw [h1, h2]
    _ = g * (k * (s⁻¹ * k * s)) * g⁻¹ := by group

theorem diag_mem (h : IsProd E K₁ K₂ s) (hs : s * s = 1) {P : Subgroup G} (hsP : s ∈ P)
    {D : Subgroup G} (hPD : P ⊓ (E ⊓ centralizer {s}) = D) {c : G} (hc : c ∈ P ⊓ K₁) :
    h.diag ⟨c, hc.2⟩ ∈ D := by
  rw [← hPD]
  refine mem_inf.mpr ⟨mul_mem hc.1 (mul_mem (mul_mem (inv_mem hsP) hc.1) hsP),
    mem_inf.mpr ⟨mul_mem (h.K₁_le hc.2) (h.K₂_le (h.conj_mem_K₂ hc.2)), ?_⟩⟩
  refine mem_centralizer_singleton_iff.mpr ?_
  exact ((h.mem_centralizer_iff hs (mul_mem (h.K₁_le hc.2)
    (h.K₂_le (h.conj_mem_K₂ hc.2)))).mpr ⟨⟨c, hc.2⟩, rfl⟩).symm

variable (h : IsProd E K₁ K₂ s) (hE : E.Normal) {P : Subgroup G} (hP : IsSylowOf 2 P ⊤)
  (hs : s * s = 1) (hsP : s ∈ P) {D : Subgroup G} (hD : IsSylowOf 2 D (E ⊓ centralizer {s}))
  (hDP : D ≤ P)
include h hE hP hs hsP hD hDP

theorem exists_sq_commutator {m : ℕ} (hm : 2 ≤ m) (eD : ↥D ≃* DihedralGroup (2 ^ m)) {z₁ : G}
    (hz₁ : z₁ ∈ P ⊓ K₁) (hzc : ∀ d ∈ D, z₁ * (s⁻¹ * z₁ * s) * d = d * (z₁ * (s⁻¹ * z₁ * s)))
    (hz1 : z₁ * (s⁻¹ * z₁ * s) ≠ 1) {x : G} (hx2 : x * x = 1) (hxs : x * s = s * x)
    (hxD : ∀ d ∈ D, x * d * x⁻¹ ∈ D)
    (hx : ∀ y ∈ D, y * x = x * y → y = 1 ∨ y = z₁ * (s⁻¹ * z₁ * s)) {a : G}
    (ha : a = x ∨ a = x * s) (haK : K₁.map (MulAut.conj a).toMonoidHom = K₁) :
    ∃ d ∈ P ⊓ K₁, (d * a * d⁻¹ * a⁻¹) ^ 2 = z₁ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hPD : P ⊓ (E ⊓ centralizer {s}) = D :=
    (hD.eq_of_le (le_inf hDP hD.le) inf_le_right (hP.isPGroup.to_le inf_le_left))
  have has : a * s = s * a := by
    rcases ha with rfl | rfl
    · exact hxs
    · rw [show x * s * s = s * x * s by rw [hxs]]; group
  set z := z₁ * (s⁻¹ * z₁ * s) with hz
  have hzD : z ∈ D := h.diag_mem hs hsP hPD hz₁
  set δ : ↥D := eD.symm (r 1) with hδ
  have hc2 : (((δ : G) ^ (2 ^ (m - 2))) ^ 2) = z := by
    have hj : ((2 ^ (m - 1) : ℕ) : ZMod (2 ^ m)) + ((2 ^ (m - 1) : ℕ) : ZMod (2 ^ m)) = 0 := by
      rw [← Nat.cast_add, ← two_mul, ← pow_succ', Nat.sub_add_cancel (by omega : 1 ≤ m),
        ZMod.natCast_self]
    have hcen : (eD.symm (r ((2 ^ (m - 1) : ℕ) : ZMod (2 ^ m))) : ↥D) ∈ center ↥D :=
      mem_center_iff.mpr fun g => (comm_of_r_double eD hj g).symm
    have hzc' : (⟨z, hzD⟩ : ↥D) ∈ center ↥D :=
      mem_center_iff.mpr fun g => Subtype.ext (hzc g g.2).symm
    have hne : eD.symm (r ((2 ^ (m - 1) : ℕ) : ZMod (2 ^ m))) ≠ 1 := by
      intro h1
      have h2 := congrArg eD h1
      rw [MulEquiv.apply_symm_apply, map_one, one_def, r.injEq, ZMod.natCast_eq_zero_iff] at h2
      have := Nat.le_of_dvd (by positivity) h2
      have h3 : 2 ^ m = 2 * 2 ^ (m - 1) := by
        rw [← pow_succ', Nat.sub_add_cancel (by omega : 1 ≤ m)]
      have h4 : 0 < 2 ^ (m - 1) := by positivity
      omega
    rcases eq_of_mem_center_dihedral eD hm hzc' (fun h1 => hz1 (congrArg Subtype.val h1))
      hcen with h1 | h1
    · exact absurd h1 hne
    · have h2 : ((δ : G) ^ (2 ^ (m - 2))) ^ 2 =
          ((eD.symm (r ((2 ^ (m - 1) : ℕ) : ZMod (2 ^ m))) : ↥D) : G) := by
        rw [← pow_mul, ← pow_succ, show m - 2 + 1 = m - 1 by omega, hδ, ← Subgroup.coe_pow,
          ← map_pow, r_one_pow]
      rw [h2, h1]
  obtain ⟨y, hyD, hyc⟩ := exists_commutator_eq_pow eD hm hx2 hxD hx (2 ^ (m - 2))
  have hy' : y ∈ P ⊓ (E ⊓ centralizer {s}) := hPD ▸ hyD
  obtain ⟨d, hd, hdy⟩ := h.exists_diag hE hP hs ⟨hy'.1, hy'.2.1⟩
    (mem_centralizer_singleton_iff.mp hy'.2.2).symm
  have hys : y * s = s * y := mem_centralizer_singleton_iff.mp hy'.2.2
  have hadK : a * d⁻¹ * a⁻¹ ∈ K₁ := by
    rw [← haK]
    exact ⟨d⁻¹, inv_mem hd.2, rfl⟩
  refine ⟨d, hd, ?_⟩
  have hγK : d * a * d⁻¹ * a⁻¹ ∈ K₁ := by
    rw [show d * a * d⁻¹ * a⁻¹ = d * (a * d⁻¹ * a⁻¹) by group]
    exact mul_mem hd.2 hadK
  have hδγ : h.diag ⟨d * a * d⁻¹ * a⁻¹, hγK⟩ = y * x * y⁻¹ * x⁻¹ := by
    have h1 : (⟨d * a * d⁻¹ * a⁻¹, hγK⟩ : ↥K₁) = ⟨d, hd.2⟩ * ⟨a * d⁻¹ * a⁻¹, hadK⟩ :=
      Subtype.ext (by simp only [Subgroup.coe_mul]; group)
    rw [h1, map_mul, diag_conj h has (inv_mem hd.2) hadK]
    have h2 : h.diag ⟨d⁻¹, inv_mem hd.2⟩ = y⁻¹ := by
      rw [show (⟨d⁻¹, inv_mem hd.2⟩ : ↥K₁) = (⟨d, hd.2⟩ : ↥K₁)⁻¹ from rfl, map_inv, diag_apply,
        ← hdy]
    rw [h2, diag_apply, ← hdy]
    rcases ha with rfl | rfl
    · group
    · have hsi : s⁻¹ = s := inv_eq_of_mul_eq_one_right hs
      have h3 : s * y⁻¹ = y⁻¹ * s := by
        calc s * y⁻¹ = y⁻¹ * (y * s) * y⁻¹ := by group
          _ = y⁻¹ * (s * y) * y⁻¹ := by rw [hys]
          _ = y⁻¹ * s := by group
      calc y * (x * s * y⁻¹ * (x * s)⁻¹) = y * x * (s * y⁻¹) * s⁻¹ * x⁻¹ := by group
        _ = y * x * (y⁻¹ * s) * s⁻¹ * x⁻¹ := by rw [h3]
        _ = y * x * y⁻¹ * x⁻¹ := by group
  apply congrArg Subtype.val (h.diag_injective (a₁ := ⟨_, pow_mem hγK 2⟩) (a₂ := ⟨z₁, hz₁.2⟩) ?_)
  rw [show (⟨(d * a * d⁻¹ * a⁻¹) ^ 2, pow_mem hγK 2⟩ : ↥K₁) = ⟨_, hγK⟩ ^ 2 from rfl, map_pow,
    hδγ, hyc, hc2, diag_apply]

omit h hE hP hs hsP hD hDP in
theorem conj_eq_of_mem_commutator (hA : AutPSL2RDerivedInput) {p n : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) {K : Subgroup G} (hlie : Blueprint.LieModel ↥K .PSL 2 p n) {P : Subgroup G}
    (hP2 : IsPGroup 2 P) (hPK : IsSylowOf 2 (P ⊓ K) K) (h8 : 8 ≤ Nat.card ↥(P ⊓ K))
    {P₀ : Subgroup G} (hP₀P : P₀ ≤ P) (hP₀N : P₀ ≤ normalizer (K : Set G)) (hKP₀ : P ⊓ K ≤ P₀)
    {δ : G} (hδ : δ ∈ P ⊓ K) (hδo : 2 * orderOf δ = Nat.card ↥(P ⊓ K)) {y : G}
    (hy : y ∈ ⁅P₀, P₀⁆) : ∃ c : ℤ, ∀ k ∈ K, y * k * y⁻¹ = δ ^ c * k * (δ ^ c)⁻¹ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set N := normalizer (K : Set G) with hN
  set P₀' : Subgroup (MulAut ↥K) := (P₀.subgroupOf N).map (normalizerConj K) with hP₀'
  have hP₀'2 : IsPGroup 2 P₀' := ((hP2.to_le hP₀P).comap_subtype).map (normalizerConj K)
  set R : Subgroup ↥K := (P ⊓ K).subgroupOf K with hR
  obtain ⟨Q, hQ⟩ := hPK
  have hQR : (Q : Subgroup ↥K) = R := by
    rw [hR, ← hQ]
    exact (comap_map_eq_self_of_injective K.subtype_injective _).symm
  have hcardR : Nat.card R = Nat.card ↥(P ⊓ K) :=
    Nat.card_congr (subgroupOfEquivOfLe (inf_le_right : P ⊓ K ≤ K)).toEquiv
  have hδR : (⟨δ, hδ.2⟩ : ↥K) ∈ R := hδ
  have hδRo : 2 * orderOf (⟨δ, hδ.2⟩ : ↥K) = Nat.card R := by
    rw [Subgroup.orderOf_mk, hcardR, hδo]
  have hInn : ∀ x ∈ R, MulAut.conj x ∈ P₀' := by
    intro x hx
    refine ⟨⟨(x : G), le_normalizer x.2⟩, hKP₀ hx, ?_⟩
    ext k
    rw [normalizerConj_apply, MulAut.conj_apply]
    simp
  have hle := hA ↥K p n hp hp2 hlie R ⟨Q, hQR⟩ (hcardR ▸ h8) ⟨δ, hδ.2⟩ hδR hδRo P₀' hP₀'2 hInn
  have hP₀map : (P₀.subgroupOf N).map N.subtype = P₀ := by
    rw [subgroupOf_map_subtype, inf_of_le_left hP₀N]
  have hy' : y ∈ (⁅P₀.subgroupOf N, P₀.subgroupOf N⁆).map N.subtype := by
    rw [map_commutator, hP₀map]
    exact hy
  obtain ⟨y', hy'c, rfl⟩ := hy'
  have hρy : normalizerConj K y' ∈ ⁅P₀', P₀'⁆ := by
    rw [hP₀', ← map_commutator]
    exact mem_map_of_mem _ hy'c
  obtain ⟨c', hc', hc'eq⟩ := hle hρy
  obtain ⟨c, rfl⟩ := mem_zpowers_iff.mp hc'
  refine ⟨c, fun k hk => ?_⟩
  have h1 := congrArg (fun φ : MulAut ↥K => ((φ ⟨k, hk⟩ : ↥K) : G)) hc'eq
  simp only [MulAut.conj_apply, normalizerConj_apply] at h1
  rw [Subgroup.coe_subtype, ← h1]
  simp

omit hs hsP hD hDP in
theorem sq_eq_of_mem_commutator (hA : AutPSL2RDerivedInput) {p n : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hlie : Blueprint.LieModel ↥K₁ .PSL 2 p n) (h8 : 8 ≤ Nat.card ↥(P ⊓ K₁))
    {Q : Subgroup G} (hCQ : centralizer (E : Set G) ≤ Q) (hQ2 : ∀ q ∈ Q, q * q = 1)
    {δ₁ δ₂ : G} (hδ₁ : δ₁ ∈ P ⊓ K₁) (hδ₁o : 2 * orderOf δ₁ = Nat.card ↥(P ⊓ K₁))
    (hδ₂ : δ₂ ∈ P ⊓ K₂) (hδ₂o : 2 * orderOf δ₂ = Nat.card ↥(P ⊓ K₂)) {y : G}
    (hy : y ∈ ⁅P ⊓ normalizer (K₁ : Set G), P ⊓ normalizer (K₁ : Set G)⁆) :
    ∃ a b : ℤ, y ^ 2 = (δ₁ ^ a) ^ 2 * (δ₂ ^ b) ^ 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hN₂ : P ⊓ normalizer (K₁ : Set G) ≤ normalizer (K₂ : Set G) := by
    intro g hg
    rw [mem_normalizer_iff_map]
    exact h.map_K₂_of_map_K₁ hE ((mem_normalizer_iff_map _ _).mp (mem_inf.mp hg).2)
  have hK₁P₀ : P ⊓ K₁ ≤ P ⊓ normalizer (K₁ : Set G) := inf_le_inf_left _ le_normalizer
  have hK₂P₀ : P ⊓ K₂ ≤ P ⊓ normalizer (K₁ : Set G) :=
    inf_le_inf_left _ (h.K₂_le.trans h.le_normalizer₁)
  have hS₂ := h.isSylowOf_inf_K₂ hE hP
  have hcard₂ : Nat.card ↥(P ⊓ K₂) = Nat.card ↥(P ⊓ K₁) := by
    rw [(h.isSylowOf_inf_K₁ hE hP).card_eq, hS₂.card_eq, ← Nat.card_congr h.equivK₂.toEquiv]
  obtain ⟨a, ha⟩ := conj_eq_of_mem_commutator hA hp hp2 hlie hP.isPGroup
    (h.isSylowOf_inf_K₁ hE hP) h8 inf_le_left inf_le_right hK₁P₀ hδ₁ hδ₁o hy
  obtain ⟨b, hb⟩ := conj_eq_of_mem_commutator hA hp hp2
    (GSThmB.OddQuot.lieModel_of_equiv h.equivK₂ hlie) hP.isPGroup hS₂ (hcard₂ ▸ h8) inf_le_left
    hN₂ hK₂P₀ hδ₂ hδ₂o hy
  set A := δ₁ ^ a with hA'
  set B := δ₂ ^ b with hB'
  have hAK : A ∈ K₁ := zpow_mem (mem_inf.mp hδ₁).2 a
  have hBK : B ∈ K₂ := zpow_mem (mem_inf.mp hδ₂).2 b
  have hAB : A * B = B * A := h.comm hAK hBK
  set q := (A * B)⁻¹ * y with hq
  have hqE : q ∈ centralizer (E : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro e he
    obtain ⟨k₁, hk₁, k₂, hk₂, rfl⟩ := h.exists_mul he
    have h1 : y * k₁ = A * k₁ * A⁻¹ * y := by
      calc y * k₁ = (y * k₁ * y⁻¹) * y := by group
        _ = A * k₁ * A⁻¹ * y := by rw [ha k₁ hk₁]
    have h2 : y * k₂ = B * k₂ * B⁻¹ * y := by
      calc y * k₂ = (y * k₂ * y⁻¹) * y := by group
        _ = B * k₂ * B⁻¹ * y := by rw [hb k₂ hk₂]
    have hc1 : B⁻¹ * k₁ = k₁ * B⁻¹ := (h.comm hk₁ (inv_mem hBK)).symm
    have hc2 : A⁻¹ * (B * k₂ * B⁻¹) = (B * k₂ * B⁻¹) * A⁻¹ :=
      h.comm (inv_mem hAK) (mul_mem (mul_mem hBK hk₂) (inv_mem hBK))
    have hq1 : q * k₁ = k₁ * q := by
      calc q * k₁ = B⁻¹ * A⁻¹ * (y * k₁) := by rw [hq]; group
        _ = B⁻¹ * k₁ * (A⁻¹ * y) := by rw [h1]; group
        _ = k₁ * B⁻¹ * (A⁻¹ * y) := by rw [hc1]
        _ = k₁ * q := by rw [hq]; group
    have hq2 : q * k₂ = k₂ * q := by
      calc q * k₂ = B⁻¹ * A⁻¹ * (y * k₂) := by rw [hq]; group
        _ = B⁻¹ * (A⁻¹ * (B * k₂ * B⁻¹)) * y := by rw [h2]; group
        _ = B⁻¹ * ((B * k₂ * B⁻¹) * A⁻¹) * y := by rw [hc2]
        _ = k₂ * q := by rw [hq]; group
    calc k₁ * k₂ * q = k₁ * (q * k₂) := by rw [hq2]; group
      _ = (k₁ * q) * k₂ := by group
      _ = q * k₁ * k₂ := by rw [hq1]
      _ = q * (k₁ * k₂) := by group
  have hq2 : q * q = 1 := hQ2 q (hCQ hqE)
  have hqA : q * A = A * q :=
    ((Subgroup.mem_centralizer_iff.mp hqE) A (h.K₁_le hAK)).symm
  have hqB : q * B = B * q :=
    ((Subgroup.mem_centralizer_iff.mp hqE) B (h.K₂_le hBK)).symm
  refine ⟨a, b, ?_⟩
  have hy : y = A * B * q := by rw [hq]; group
  rw [hy]
  calc (A * B * q) ^ 2 = A * B * (q * A) * B * q := by rw [sq]; group
    _ = A * B * A * (q * B) * q := by rw [hqA]; group
    _ = A * B * A * B * (q * q) := by rw [hqB]; group
    _ = A * (B * A) * B := by rw [hq2]; group
    _ = A * (A * B) * B := by rw [hAB]
    _ = A ^ 2 * B ^ 2 := by rw [sq, sq]; group

omit hs hsP hD hDP in
theorem sq_mem_of_mem_commutator (hA : AutPSL2RDerivedInput) {p n : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hlie : Blueprint.LieModel ↥K₁ .PSL 2 p n) (h8 : 8 ≤ Nat.card ↥(P ⊓ K₁))
    {Q : Subgroup G} (hCQ : centralizer (E : Set G) ≤ Q) (hQ2 : ∀ q ∈ Q, q * q = 1)
    {δ₁ δ₂ : G} (hδ₁ : δ₁ ∈ P ⊓ K₁) (hδ₁o : 2 * orderOf δ₁ = Nat.card ↥(P ⊓ K₁))
    (hδ₂ : δ₂ ∈ P ⊓ K₂) (hδ₂o : 2 * orderOf δ₂ = Nat.card ↥(P ⊓ K₂)) {z₁ z₂ : G}
    (hz₁ : ∀ c ∈ zpowers δ₁, c ^ 2 = 1 → c = 1 ∨ c = z₁)
    (hz₂ : ∀ c ∈ zpowers δ₂, c ^ 2 = 1 → c = 1 ∨ c = z₂) {y : G}
    (hy : y ∈ ⁅P ⊓ normalizer (K₁ : Set G), P ⊓ normalizer (K₁ : Set G)⁆)
    (hy4 : (y ^ 2) ^ 2 = 1) :
    y ^ 2 = 1 ∨ y ^ 2 = z₁ ∨ y ^ 2 = z₂ ∨ y ^ 2 = z₁ * z₂ := by
  obtain ⟨a, b, hab⟩ := h.sq_eq_of_mem_commutator hE hP hA hp hp2 hlie h8 hCQ hQ2 hδ₁ hδ₁o hδ₂
    hδ₂o hy
  set A := (δ₁ ^ a) ^ 2 with hA'
  set B := (δ₂ ^ b) ^ 2 with hB'
  have hAK : A ∈ K₁ := pow_mem (zpow_mem (mem_inf.mp hδ₁).2 a) 2
  have hBK : B ∈ K₂ := pow_mem (zpow_mem (mem_inf.mp hδ₂).2 b) 2
  have hAB : A * B = B * A := h.comm hAK hBK
  rw [hab] at hy4 ⊢
  have h1 : A ^ 2 * B ^ 2 = 1 := by
    rw [← hy4, sq, sq, sq]
    calc A * A * (B * B) = A * (A * B) * B := by group
      _ = A * (B * A) * B := by rw [hAB]
      _ = A * B * (A * B) := by group
  have hA2 : A ^ 2 = 1 := by
    have h2 : A ^ 2 = (B ^ 2)⁻¹ := eq_inv_of_mul_eq_one_left h1
    have h3 : A ^ 2 ∈ K₁ ⊓ K₂ := mem_inf.mpr ⟨pow_mem hAK 2, h2 ▸ inv_mem (pow_mem hBK 2)⟩
    rw [h.inf_eq, mem_bot] at h3
    exact h3
  have hB2 : B ^ 2 = 1 := by
    rw [hA2, one_mul] at h1
    exact h1
  have hAm : A ∈ zpowers δ₁ := pow_mem (zpow_mem (mem_zpowers δ₁) a) 2
  have hBm : B ∈ zpowers δ₂ := pow_mem (zpow_mem (mem_zpowers δ₂) b) 2
  rcases hz₁ A hAm hA2 with h4 | h4 <;> rcases hz₂ B hBm hB2 with h5 | h5 <;>
    simp [h4, h5]

end IsProd

end L415

end CFSG.ComponentClassification.HarrisLit
