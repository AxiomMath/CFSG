module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisEndBL2Norm2
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit415JX

public noncomputable section

namespace CFSG.ComponentClassification.HarrisLit

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer CFSG.ABGLocalTools HarrisEnd
open Standing.Setup42 DihedralGroup
open scoped Pointwise

variable {X : Type} [Group X] [Finite X] {t : X} {L : Subgroup X} {p f : ℕ} {S : Subgroup X}
  {w z : X} {V : Subgroup X} {i j : ℕ}

theorem EndB.comm_of_central {G : Type*} [Group G] [Finite G] {P R : Subgroup G} {m k : ℕ}
    (hm : 3 ≤ m) (e : ↥R ≃* DihedralGroup (2 ^ m)) {v : G}
    (hvN : zpowers v ≤ normalizer (R : Set G)) (hdisj : zpowers v ⊓ R = ⊥)
    (hv : orderOf v = 2 ^ k) (hv1 : v ≠ 1)
    (hv₀c : ∀ c ∈ R, c * v ^ (orderOf v / 2) = v ^ (orderOf v / 2) * c)
    (hsmall : P ≠ R ⊔ zpowers v → ∀ α ∈ P, α ∉ R ⊔ zpowers v → α ^ 2 = 1 →
      Nat.card ↥(R ⊓ centralizer {α}) ≤ 4)
    {α : G} (hαP : α ∈ P) (hα2 : α * α = 1)
    (hαc : ∀ r ∈ R, α * r * α⁻¹ * r⁻¹ ∈ R ⊓ centralizer (R : Set G)) {r : G} (hr : r ∈ R) :
    r * α = α * r := by
  have hZ2 := EndB.dih_card_center_le (by omega) e
  have hR16 : 16 ≤ Nat.card R := by
    rw [Nat.card_congr e.toEquiv, DihedralGroup.nat_card]
    have : 2 ^ 3 ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm
    omega
  have hαRv : α ∈ R ⊔ zpowers v := by
    by_contra hno
    have hne : P ≠ R ⊔ zpowers v := fun h => hno (h ▸ hαP)
    have h4 := hsmall hne α hαP hno (by rw [sq, hα2])
    have h8 := EndB.card_le_of_comm_mem (R := R) (Z := R ⊓ centralizer (R : Set G)) hαc
    have := Nat.mul_le_mul h4 hZ2
    omega
  rw [sup_comm] at hαRv
  have hαRv' : α ∈ ((zpowers v : Set G) * (R : Set G)) := by
    rw [← coe_mul_of_left_le_normalizer_right _ _ hvN]
    exact hαRv
  obtain ⟨y, hy, ρ', hρ'R, rfl⟩ := hαRv'
  beta_reduce at hαP hα2 hαc ⊢
  obtain ⟨a, rfl⟩ := mem_zpowers_iff.mp hy
  have hσR : v ^ a * ρ' * (v ^ a)⁻¹ ∈ R :=
    (mem_normalizer_iff.mp (hvN (zpow_mem (mem_zpowers v) a)) ρ').mp hρ'R
  have hv2a : (v ^ a) ^ 2 = 1 := by
    have h1 : (v ^ a) ^ 2 = (v ^ a * ρ' * (v ^ a)⁻¹)⁻¹ * (v ^ a * ρ' * (v ^ a * ρ')) * ρ'⁻¹ := by
      group
    have h2 : (v ^ a) ^ 2 ∈ R := by
      rw [h1, hα2, mul_one]
      exact mul_mem (inv_mem hσR) (inv_mem hρ'R)
    have h3 : (v ^ a) ^ 2 ∈ zpowers v ⊓ R := ⟨pow_mem (zpow_mem (mem_zpowers v) a) 2, h2⟩
    rwa [hdisj, mem_bot] at h3
  have hk1 : 1 ≤ k := by
    rcases Nat.eq_zero_or_pos k with h0 | h0
    · rw [h0, pow_zero, orderOf_eq_one_iff] at hv
      exact absurd hv hv1
    · exact h0
  have hhalf : orderOf v / 2 = 2 ^ (k - 1) := by
    rw [hv, show k = (k - 1) + 1 by omega, pow_succ, Nat.mul_div_cancel _ two_pos,
      show k - 1 + 1 - 1 = k - 1 by omega]
  have hva : v ^ a = 1 ∨ v ^ a = v ^ (orderOf v / 2) := by
    rw [hhalf]
    exact L415.eq_of_mem_zpowers_sq hk1 hv (zpow_mem (mem_zpowers v) a) hv2a
  set v₀ := v ^ (orderOf v / 2) with hv₀
  have hv₀2 : v₀ * v₀ = 1 := by
    rw [hv₀, ← pow_add, ← two_mul, hhalf, ← pow_succ', show k - 1 + 1 = k by omega, ← hv,
      pow_orderOf_eq_one]
  have hred : ∃ ε : G, (ε = 1 ∨ ε = v₀) ∧ v ^ a * ρ' = ε * ρ' := by
    rcases hva with h | h
    · exact ⟨1, Or.inl rfl, by rw [h]⟩
    · exact ⟨v₀, Or.inr rfl, by rw [h]⟩
  obtain ⟨ε, hε, hεeq⟩ := hred
  rw [hεeq] at hα2 hαc ⊢
  have hεc : ∀ c ∈ R, c * ε = ε * c := fun c hc' => by
    rcases hε with h | h
    · rw [h, mul_one, one_mul]
    · rw [h]; exact hv₀c c hc'
  have hε2 : ε * ε = 1 := by
    rcases hε with h | h
    · rw [h, mul_one]
    · rw [h]
      exact hv₀2
  have hερ : ε * ρ' = ρ' * ε := (hεc ρ' hρ'R).symm
  have hρ'2 : ρ' * ρ' = 1 := by
    calc ρ' * ρ' = (ε * ε) * (ρ' * ρ') := by rw [hε2, one_mul]
      _ = ε * (ε * ρ') * ρ' := by group
      _ = ε * (ρ' * ε) * ρ' := by rw [hερ]
      _ = (ε * ρ') * (ε * ρ') := by group
      _ = 1 := hα2
  have hρ'c : ∀ r ∈ R, ρ' * r * ρ'⁻¹ * r⁻¹ ∈ R ⊓ centralizer (R : Set G) := fun r hr' => by
    have h1 := hαc r hr'
    have h2 : ε * ρ' * r * (ε * ρ')⁻¹ * r⁻¹ = ρ' * r * ρ'⁻¹ * r⁻¹ := by
      have hc1 : ρ' * r * ρ'⁻¹ ∈ R := mul_mem (mul_mem hρ'R hr') (inv_mem hρ'R)
      calc ε * ρ' * r * (ε * ρ')⁻¹ * r⁻¹ = ε * (ρ' * r * ρ'⁻¹) * ε⁻¹ * r⁻¹ := by group
        _ = (ρ' * r * ρ'⁻¹) * ε * ε⁻¹ * r⁻¹ := by rw [← hεc _ hc1]
        _ = ρ' * r * ρ'⁻¹ * r⁻¹ := by group
    rwa [h2] at h1
  set δ : G := (e.symm (DihedralGroup.r 1) : G) with hδ
  have hδR : δ ∈ R := (e.symm (DihedralGroup.r 1)).2
  have hcZ := hρ'c δ hδR
  set c := ρ' * δ * ρ'⁻¹ * δ⁻¹ with hc
  have hc2 : c * c = 1 := by
    have hcard := pow_card_eq_one' (G := ↥(R ⊓ centralizer (R : Set G))) (x := ⟨c, hcZ⟩)
    have hcard' : c ^ Nat.card ↥(R ⊓ centralizer (R : Set G)) = 1 := by
      have := congrArg Subtype.val hcard
      simpa using this
    have hpos : 0 < Nat.card ↥(R ⊓ centralizer (R : Set G)) := Nat.card_pos
    interval_cases h : Nat.card ↥(R ⊓ centralizer (R : Set G))
    · rw [pow_one] at hcard'; rw [hcard', one_mul]
    · rw [← sq]; exact hcard'
  have hδ2 : δ * δ = (e.symm (DihedralGroup.r 2) : G) := by
    rw [hδ, ← Subgroup.coe_mul, ← map_mul, r_mul_r]
    norm_num
  have hρ'δ : ρ' * (e.symm (DihedralGroup.r 2) : G) = (e.symm (DihedralGroup.r 2) : G) * ρ' := by
    rw [← hδ2]
    have hcδ : c * δ = δ * c := (mem_centralizer_iff.mp hcZ.2 δ hδR).symm
    have h1 : ρ' * δ * ρ'⁻¹ = c * δ := by rw [hc]; group
    have hρ'i : ρ'⁻¹ = ρ' := inv_eq_of_mul_eq_one_right hρ'2
    calc ρ' * (δ * δ) = (ρ' * δ * ρ'⁻¹) * (ρ' * δ * ρ'⁻¹) * ρ' := by group
      _ = c * δ * (c * δ) * ρ' := by rw [h1]
      _ = c * c * (δ * δ) * ρ' := by
          rw [show c * δ * (c * δ) = c * (δ * c) * δ by group, ← hcδ]; group
      _ = (δ * δ) * ρ' := by rw [hc2, one_mul]
  have hcent := EndB.dih_comm_of_comm_sq hm e hρ'R hρ'2 hρ'δ hr
  calc r * (ε * ρ') = (r * ε) * ρ' := by group
    _ = (ε * r) * ρ' := by rw [hεc r hr]
    _ = ε * (r * ρ') := by group
    _ = ε * (ρ' * r) := by rw [hcent]
    _ = ε * ρ' * r := by group

theorem EndB.conj_mem_inf_innAut {Y : Type} [Group Y] {P : Subgroup (MulAut Y)} {π ρ : MulAut Y}
    (hπ : π ∈ P) (hρ : ρ ∈ P ⊓ innAut Y) : π * ρ * π⁻¹ ∈ P ⊓ innAut Y := by
  refine ⟨Subgroup.mul_mem _ (Subgroup.mul_mem _ hπ hρ.1) (Subgroup.inv_mem _ hπ), ?_⟩
  obtain ⟨y, hy⟩ := hρ.2
  exact ⟨π y, by rw [← hy]; exact (EndB.mul_conj_mul_inv π y).symm⟩

namespace EndB.L2Ctx

variable {hs : Setting46e t L p f S w z V i j} {W : Subgroup X}

theorem le_N0_of_normal (hKG : AutPSL2SylowInput) (hKC : AutPSL2CentralizerInput)
    (hFC : AutPSL2FieldCentralizerInput) (hc : L2Ctx hs W) {Y' : Subgroup X} (hYW : Y' ≤ W)
    (hYn : ∀ g ∈ W, ∀ y ∈ Y', g * y * g⁻¹ ∈ Y') (hY2 : ∀ y ∈ Y', y * y = 1) :
    Y' ≤ qTilde (w ^ (orderOf w / 2) * t ^ i * z ^ j) W ⊔ closure ({t, z} : Set X) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro y hy
  set M := centralizer ({w ^ (orderOf w / 2) * t ^ i * z ^ j} : Set X) with hM
  set E := layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)) with hE
  obtain ⟨v, hv⟩ := hc.exists_sylowAutData hKG
  obtain ⟨m, hm, ⟨e⟩⟩ := hv.dihedral
  have hP2 : IsPGroup 2 ((barOf (centralizer ({w ^ (orderOf w / 2) * t ^ i * z ^ j} : Set X))
      W).map (conjOn (layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j))))) :=
    ((isSylowOf_barOf hc.sylow).isPGroup).map _
  have hv1 : v ≠ 1 := fun h => hv.not_mem_inn (by rw [h]; exact one_mem _)
  obtain ⟨k, hk⟩ := IsPGroup.iff_orderOf.mp hP2 ⟨v, hv.mem⟩
  rw [Subgroup.orderOf_mk] at hk
  have hYM : ∀ y ∈ Y', y ∈ M := fun y hy => hc.sylow.le (hYW hy)
  have hŶn : ∀ π ∈ (barOf M W).map (conjOn E), ∀ a ∈ (barOf M Y').map (conjOn E),
      π * a * π⁻¹ ∈ (barOf M Y').map (conjOn E) := by
    rintro _ ⟨gb, hgb, rfl⟩ _ ⟨yb, hyb, rfl⟩
    obtain ⟨g, hgW, rfl⟩ := mem_barOf.mp hgb
    obtain ⟨y', hy'Y, rfl⟩ := mem_barOf.mp hyb
    refine ⟨QuotientGroup.mk (g * y' * g⁻¹), mk_mem_barOf _ (hYn g hgW y' hy'Y), ?_⟩
    rw [QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv, map_mul, map_mul,
      map_inv]
  have hŶ2 : ∀ a ∈ (barOf M Y').map (conjOn E), a * a = 1 := by
    rintro _ ⟨yb, hyb, rfl⟩
    obtain ⟨y', hy'Y, rfl⟩ := mem_barOf.mp hyb
    rw [← map_mul, ← QuotientGroup.mk_mul]
    have : y' * y' = 1 := Subtype.ext (hY2 _ hy'Y)
    rw [this, QuotientGroup.mk_one, map_one]
  have hŶP : (barOf M Y').map (conjOn E) ≤ (barOf M W).map (conjOn E) :=
    map_mono (EndB.barOf_mono hYW)
  have hNc : ∀ x ∈ (barOf M Y').map (conjOn E) ⊓ ((barOf M W).map (conjOn E) ⊓ innAut ↥E),
      ∀ r' ∈ (barOf M W).map (conjOn E) ⊓ innAut ↥E, r' * x = x * r' := fun x hx r' hr' =>
    EndB.dih_comm_of_normal hm e (N := (barOf M Y').map (conjOn E) ⊓
      ((barOf M W).map (conjOn E) ⊓ innAut ↥E)) inf_le_right
      (fun r hr x hx => ⟨hŶn r hr.1 x hx.1, EndB.conj_mem_inf_innAut hr.1 hx.2⟩)
      (fun x hx => hŶ2 x hx.1) hx hr'
  set α := conjOn E (QuotientGroup.mk ⟨y, hYM y hy⟩) with hα
  have hαŶ : α ∈ (barOf M Y').map (conjOn E) := ⟨_, mk_mem_barOf _ hy, rfl⟩
  have hαP : α ∈ (barOf M W).map (conjOn E) := hŶP hαŶ
  have hαc : ∀ r ∈ (barOf M W).map (conjOn E) ⊓ innAut ↥E,
      α * r * α⁻¹ * r⁻¹ ∈ ((barOf M W).map (conjOn E) ⊓ innAut ↥E) ⊓
        centralizer (((barOf M W).map (conjOn E) ⊓ innAut ↥E : Subgroup _) : Set _) := by
    intro r hr
    have hmemN : α * r * α⁻¹ * r⁻¹ ∈ (barOf M Y').map (conjOn E) ⊓
        ((barOf M W).map (conjOn E) ⊓ innAut ↥E) := by
      refine ⟨?_, Subgroup.mul_mem _ (EndB.conj_mem_inf_innAut hαP hr) (Subgroup.inv_mem _ hr)⟩
      have : α * r * α⁻¹ * r⁻¹ = α * (r * α⁻¹ * r⁻¹) := by group
      rw [this]
      exact Subgroup.mul_mem _ hαŶ (hŶn r hr.1 _ (Subgroup.inv_mem _ hαŶ))
    exact ⟨hmemN.2, Subgroup.mem_centralizer_iff.mpr fun r' hr' => hNc _ hmemN r' hr'⟩
  have hvN : zpowers v ≤ normalizer (((barOf M W).map (conjOn E) ⊓ innAut ↥E :
      Subgroup _) : Set _) := by
    rw [zpowers_le]
    rw [mem_normalizer_iff]
    intro r
    constructor
    · exact fun hr => EndB.conj_mem_inf_innAut hv.mem hr
    · intro hr
      have := EndB.conj_mem_inf_innAut (Subgroup.inv_mem _ hv.mem) hr
      simpa [mul_assoc] using this
  have hcomm := fun {r} (hr : r ∈ (barOf M W).map (conjOn E) ⊓ innAut ↥E) =>
    EndB.comm_of_central hm e hvN hv.disj hk hv1 hv.comm_v₀ hv.small_of_ne hαP
      (hŶ2 α hαŶ) hαc hr
  exact hc.mem_N0_of_conjOn_mem hKC hFC hv (hYW hy)
    (Subgroup.mem_centralizer_iff.mpr fun r hr => hcomm hr)

end EndB.L2Ctx

end CFSG.ComponentClassification.HarrisLit
