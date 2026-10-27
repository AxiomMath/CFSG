module

public import CFSG.Walter.Bender1970.S3.CoreExchangeTools
import CFSG.GroupTheory.ElementaryAbelianTransport
public import CFSG.Assembly.LowTwoRankDefs
public import CFSG.Goldschmidt.BasicG

public section

namespace CFSG.Goldschmidt.G55

open CFSG.GorensteinWalter CFSG.Walter
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem oddCoreOf_eq (H : Subgroup G) :
    CFSG.Goldschmidt.oddCoreOf H = CFSG.GorensteinWalter.oddCoreOf H := by
  simp only [CFSG.Goldschmidt.oddCoreOf, CFSG.GorensteinWalter.oddCoreOf,
    goldschmidtOddCore_eq_pPrimeCore]

omit [Finite G] in
theorem fstarZero_le (H : Subgroup G) : fstarZero H ≤ generalizedFittingSubgroupOf H :=
  sup_le ((Bender35.commutator_self_le _).trans le_sup_left) inf_le_left

omit [Finite G] in
theorem le_normalizer_fstarZero (H : Subgroup G) :
    H ≤ Subgroup.normalizer (fstarZero H : Set G) := by
  intro h hh
  have hF : h ∈ Subgroup.normalizer (CFSG.fittingSubgroupOf H : Set G) :=
    le_normalizer_of_isNormalIn (fittingSubgroupOf_isNormalIn H) hh
  have hFs : h ∈ Subgroup.normalizer (generalizedFittingSubgroupOf H : Set G) :=
    le_normalizer_of_isNormalIn (generalizedFittingSubgroupOf_isNormalIn H) hh
  have h1 := mem_normalizer_commutator hF hF
  have h2 := mem_normalizer_inf hFs (Bender35.mem_normalizer_centralizer h1)
  have hs : fstarZero H = sSup {⁅CFSG.fittingSubgroupOf H, CFSG.fittingSubgroupOf H⁆,
      generalizedFittingSubgroupOf H ⊓ Subgroup.centralizer
        ((⁅CFSG.fittingSubgroupOf H, CFSG.fittingSubgroupOf H⁆ : Subgroup G) : Set G)} := by
    rw [sSup_pair]; rfl
  rw [hs]
  refine mem_normalizer_sSup fun K hK => ?_
  rcases hK with rfl | rfl
  · exact h1
  · exact h2

omit [Finite G] in
theorem fstarZero_isNormalIn (H : Subgroup G) : IsNormalIn (fstarZero H) H :=
  ⟨(fstarZero_le H).trans (generalizedFittingSubgroupOf_le H), fun _ hh k hk =>
    (Subgroup.mem_normalizer_iff.mp (le_normalizer_fstarZero H hh) k).mp hk⟩

omit [Finite G] in
theorem fstarZero_isNormalIn_generalizedFitting (H : Subgroup G) :
    IsNormalIn (fstarZero H) (generalizedFittingSubgroupOf H) :=
  ⟨fstarZero_le H, fun _ hh k hk => (fstarZero_isNormalIn H).2 _
    (generalizedFittingSubgroupOf_le H hh) k hk⟩

omit [Finite G] in
theorem isSubnormal_of_fstarZero {H Y : Subgroup G} (hY : Y ≤ fstarZero H)
    (hYsn : (Y.subgroupOf (fstarZero H)).IsSubnormal) :
    Y ≤ generalizedFittingSubgroupOf H ∧
      (Y.subgroupOf (generalizedFittingSubgroupOf H)).IsSubnormal :=
  ⟨hY.trans (fstarZero_le H), isSubnormal_subgroupOf_trans hY hYsn
    (isSubnormal_subgroupOf_of_isNormalIn (fstarZero_isNormalIn_generalizedFitting H))⟩

theorem fitting_le_qCoreOf_sup (H : Subgroup G) {p : ℕ} (hp : p.Prime) :
    CFSG.fittingSubgroupOf H ≤ qCoreOf H p ⊔
      (CFSG.fittingSubgroupOf H ⊓ Subgroup.centralizer (qCoreOf H p : Set G)) := by
  refine (fittingSubgroupOf_eq_iSup_qCoreOf H).le.trans (iSup_le fun q => ?_)
  have hq : q.1.1.Prime := Nat.prime_of_mem_primeFactors q.1.2
  by_cases hqp : q.1.1 = p
  · rw [hqp]
    exact le_sup_left
  · exact (le_inf (qCoreOf_le_fittingSubgroupOf H _ hq)
      (qCoreOf_centralizer_of_ne H hp hq (Ne.symm hqp))).trans le_sup_right

omit [Finite G] in
theorem commutatorElement_mul_mul {a b c d : G} (hca : Commute c a) (hcb : Commute c b)
    (hda : Commute d a) (hdb : Commute d b) : ⁅a * c, b * d⁆ = ⁅a, b⁆ * ⁅c, d⁆ := by
  simp only [commutatorElement_def]
  calc a * c * (b * d) * (a * c)⁻¹ * (b * d)⁻¹
      = a * (c * b) * d * c⁻¹ * a⁻¹ * d⁻¹ * b⁻¹ := by group
    _ = a * (b * c) * d * c⁻¹ * a⁻¹ * d⁻¹ * b⁻¹ := by rw [hcb.eq]
    _ = a * b * (c * d * c⁻¹) * a⁻¹ * d⁻¹ * b⁻¹ := by group
    _ = a * b * a⁻¹ * (c * d * c⁻¹) * d⁻¹ * b⁻¹ := by
        rw [mul_assoc (a * b) (c * d * c⁻¹) a⁻¹,
          (((hca.mul_left hda).mul_left hca.inv_left).inv_right).eq]
        group
    _ = a * b * a⁻¹ * (c * d * c⁻¹ * d⁻¹) * b⁻¹ := by group
    _ = a * b * a⁻¹ * b⁻¹ * (c * d * c⁻¹ * d⁻¹) := by
        rw [mul_assoc (a * b * a⁻¹) (c * d * c⁻¹ * d⁻¹) b⁻¹,
          ((((hcb.mul_left hdb).mul_left hcb.inv_left).mul_left hdb.inv_left).inv_right).eq]
        group

theorem commutator_fitting_le_centralizer (H : Subgroup G) {p : ℕ} (hp : p.Prime) {z : G}
    (hz : z ∈ qCoreOf H p)
    (hzc : z ∈ Subgroup.centralizer ((⁅qCoreOf H p, qCoreOf H p⁆ : Subgroup G) : Set G)) :
    ⁅CFSG.fittingSubgroupOf H, CFSG.fittingSubgroupOf H⁆ ≤ Subgroup.centralizer ({z} : Set G) := by
  set P := qCoreOf H p
  set F := CFSG.fittingSubgroupOf H
  have hle := fitting_le_qCoreOf_sup H hp
  have hCP : F ⊓ Subgroup.centralizer (P : Set G) ≤ Subgroup.centralizer (P : Set G) :=
    inf_le_right
  rw [Subgroup.commutator_le]
  intro f₁ hf₁ f₂ hf₂
  obtain ⟨u₁, hu₁, c₁, hc₁, rfl⟩ := mem_sup_decompose_of_centralizes (hle hf₁) hCP
  obtain ⟨u₂, hu₂, c₂, hc₂, rfl⟩ := mem_sup_decompose_of_centralizes (hle hf₂) hCP
  have hcom : ∀ c ∈ F ⊓ Subgroup.centralizer (P : Set G), ∀ u ∈ P, Commute c u :=
    fun c hc u hu => ((Subgroup.mem_centralizer_iff.mp hc.2) u hu).symm
  rw [commutatorElement_mul_mul (hcom c₁ hc₁ u₁ hu₁) (hcom c₁ hc₁ u₂ hu₂)
    (hcom c₂ hc₂ u₁ hu₁) (hcom c₂ hc₂ u₂ hu₂)]
  refine Subgroup.mul_mem _ ?_ ?_
  · rw [Subgroup.mem_centralizer_singleton_iff]
    exact (Subgroup.mem_centralizer_iff.mp hzc) _ (Subgroup.commutator_mem_commutator hu₁ hu₂)
  · have h1 : z ∈ Subgroup.centralizer ({c₁} : Set G) :=
      Subgroup.mem_centralizer_singleton_iff.mpr (hcom c₁ hc₁ z hz).eq.symm
    have h2 : z ∈ Subgroup.centralizer ({c₂} : Set G) :=
      Subgroup.mem_centralizer_singleton_iff.mpr (hcom c₂ hc₂ z hz).eq.symm
    rw [Subgroup.mem_centralizer_singleton_iff] at h1 h2 ⊢
    rw [commutatorElement_def]
    have h1' : Commute z c₁ := h1
    have h2' : Commute z c₂ := h2
    exact (((h1'.mul_right h2').mul_right h1'.inv_right).mul_right h2'.inv_right).eq.symm

theorem inf_centralizer_le_fstarZero (H : Subgroup G) {p : ℕ} (hp : p.Prime) :
    qCoreOf H p ⊓ Subgroup.centralizer ((qCoreOf H p ⊓ fstarZero H : Subgroup G) : Set G) ≤
      fstarZero H := by
  rintro x ⟨hxP, hxC⟩
  have hPF : qCoreOf H p ≤ CFSG.fittingSubgroupOf H := qCoreOf_le_fittingSubgroupOf H p hp
  have hPP : ⁅qCoreOf H p, qCoreOf H p⁆ ≤ qCoreOf H p ⊓ fstarZero H :=
    le_inf (Bender35.commutator_self_le _) ((Subgroup.commutator_mono hPF hPF).trans le_sup_left)
  have hxc := Subgroup.centralizer_le hPP hxC
  have h := commutator_fitting_le_centralizer H hp hxP hxc
  refine (le_sup_right : _ ≤ fstarZero H) ⟨(hPF.trans le_sup_left) hxP,
    Subgroup.mem_centralizer_iff.mpr fun y hy => ?_⟩
  exact Subgroup.mem_centralizer_singleton_iff.mp (h hy)

theorem center_commutator_le_centralizer_fstarZero (H : Subgroup G) {p : ℕ} (hp : p.Prime) :
    ⁅qCoreOf H p, qCoreOf H p⁆ ⊓
        Subgroup.centralizer ((⁅qCoreOf H p, qCoreOf H p⁆ : Subgroup G) : Set G) ≤
      Subgroup.centralizer (fstarZero H : Set G) := by
  rintro z ⟨hzP', hzc⟩
  have hPF : qCoreOf H p ≤ CFSG.fittingSubgroupOf H := qCoreOf_le_fittingSubgroupOf H p hp
  have hzP : z ∈ qCoreOf H p := Bender35.commutator_self_le _ hzP'
  have h := commutator_fitting_le_centralizer H hp hzP hzc
  refine fstar_centralizer_of_centralizes_join ?_ ?_
  · rw [Subgroup.mem_centralizer_iff]
    intro y hy
    exact Subgroup.mem_centralizer_singleton_iff.mp (h hy)
  · rw [Subgroup.mem_centralizer_iff]
    intro y hy
    exact ((Subgroup.mem_centralizer_iff.mp hy.2) z (Subgroup.commutator_mono hPF hPF hzP')).symm

theorem mem_centralizer_qCoreOf_of_coprime (H : Subgroup G) {p : ℕ} (hp : p.Prime) {c : G}
    (hc : c ∈ CFSG.fittingSubgroupOf H) (hcop : Nat.Coprime p (orderOf c)) :
    c ∈ Subgroup.centralizer (qCoreOf H p : Set G) := by
  have : Fact p.Prime := ⟨hp⟩
  set P := qCoreOf H p
  have hCP : CFSG.fittingSubgroupOf H ⊓ Subgroup.centralizer (P : Set G) ≤
      Subgroup.centralizer (P : Set G) := inf_le_right
  obtain ⟨u, hu, c₀, hc₀, rfl⟩ :=
    mem_sup_decompose_of_centralizes (fitting_le_qCoreOf_sup H hp hc) hCP
  have hcomm : Commute u c₀ := (Subgroup.mem_centralizer_iff.mp hc₀.2) u hu
  set m := orderOf (u * c₀)
  have hm : u ^ m * c₀ ^ m = 1 := by rw [← hcomm.mul_pow, pow_orderOf_eq_one]
  have hum : u ^ m ∈ Subgroup.centralizer (P : Set G) := by
    have : u ^ m = (c₀ ^ m)⁻¹ := eq_inv_of_mul_eq_one_left hm
    rw [this]
    exact Subgroup.inv_mem _ (Subgroup.pow_mem _ hc₀.2 m)
  have hcop' : Nat.Coprime m (orderOf u) := by
    obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.mp (qCoreOf_isPGroup H p)) ⟨u, hu⟩
    rw [← Subgroup.orderOf_mk u hu, hk]
    exact Nat.Coprime.pow_right k hcop.symm
  obtain ⟨k, hk⟩ := exists_pow_eq_self_of_coprime hcop'
  have huC : u ∈ Subgroup.centralizer (P : Set G) := hk ▸ Subgroup.pow_mem _ hum k
  exact Subgroup.mul_mem _ huC hc₀.2

omit [Finite G] in
theorem exists_pow_mul_pow {p : ℕ} (hp : p.Prime) {y : G} (hy : IsOfFinOrder y) :
    ∃ a ∈ Subgroup.zpowers y, ∃ b ∈ Subgroup.zpowers y, y = a * b ∧ Commute a b ∧
      (∃ k : ℕ, orderOf a ∣ p ^ k) ∧ Nat.Coprime p (orderOf b) := by
  have hn0 : orderOf y ≠ 0 := (orderOf_pos_iff.mpr hy).ne'
  obtain ⟨e, m, hpm, hn⟩ := Nat.exists_eq_pow_mul_and_not_dvd hn0 p hp.one_lt.ne'
  have hcop : Nat.Coprime (p ^ e) m :=
    Nat.Coprime.pow_left e ((Nat.Prime.coprime_iff_not_dvd hp).mpr hpm)
  have hbez := Nat.gcd_eq_gcd_ab (p ^ e) m
  rw [hcop.gcd_eq_one, Nat.cast_one] at hbez
  set s := (p ^ e).gcdA m
  set t := (p ^ e).gcdB m
  refine ⟨y ^ ((m : ℤ) * t), Subgroup.zpow_mem_zpowers _ _, y ^ (((p ^ e : ℕ) : ℤ) * s),
    Subgroup.zpow_mem_zpowers _ _, ?_, Commute.zpow_zpow_self y _ _, ⟨e, ?_⟩, ?_⟩
  · rw [← zpow_add, add_comm, ← hbez, zpow_one]
  · apply orderOf_dvd_of_pow_eq_one
    rw [← zpow_natCast, ← zpow_mul, mul_comm, ← mul_assoc, ← Nat.cast_mul, ← hn, zpow_mul,
      zpow_natCast, pow_orderOf_eq_one, one_zpow]
  · have h1 : orderOf (y ^ (((p ^ e : ℕ) : ℤ) * s)) ∣ m := by
      apply orderOf_dvd_of_pow_eq_one
      rw [← zpow_natCast, ← zpow_mul, mul_comm, ← mul_assoc, ← Nat.cast_mul, mul_comm m,
        ← hn, zpow_mul, zpow_natCast, pow_orderOf_eq_one, one_zpow]
    exact Nat.Coprime.coprime_dvd_right h1 ((Nat.Prime.coprime_iff_not_dvd hp).mpr hpm)

theorem conj_mem_of_mem_normalizer_inf_qCoreOf {H Y : Subgroup G} {p : ℕ} (hp : p.Prime)
    (hYF : Y ≤ generalizedFittingSubgroupOf H)
    (hY : (Y.subgroupOf (generalizedFittingSubgroupOf H)).IsSubnormal) {x : G}
    (hx : x ∈ qCoreOf H p)
    (hxN : x ∈ Subgroup.normalizer ((Y ⊓ qCoreOf H p : Subgroup G) : Set G)) {y : G}
    (hy : y ∈ Y) : x * y * x⁻¹ ∈ Y := by
  set P := qCoreOf H p
  set F := CFSG.fittingSubgroupOf H
  set E := componentLayerOf H
  have hYH : Y ≤ H := hYF.trans (generalizedFittingSubgroupOf_le H)
  have hYsnH : (Y.subgroupOf H).IsSubnormal :=
    isSubnormal_subgroupOf_of_isSubnormal_generalizedFitting hYF hY
  set E₁ := sSup {L : Subgroup G | IsComponentOf L H ∧ L ≤ Y}
  set E₂ := sSup {L : Subgroup G | IsComponentOf L H ∧ ⁅L, Y⁆ = ⊥}
  have hE₁Y : E₁ ≤ Y := sSup_le fun L hL => hL.2
  have hE₂C : E₂ ≤ Subgroup.centralizer (Y : Set G) :=
    sSup_le fun L hL => Subgroup.commutator_eq_bot_iff_le_centralizer.mp hL.2
  have hE₁E : E₁ ≤ E := sSup_le fun L hL => le_sSup (s := {L | IsComponentOf L H}) hL.1
  have hE₂E : E₂ ≤ E := sSup_le fun L hL => le_sSup (s := {L | IsComponentOf L H}) hL.1
  have hE : E ≤ E₂ ⊔ E₁ := by
    refine sSup_le fun L hL => ?_
    rcases fstar_component_le_or_commutator_eq_bot_of_subnormal_subgroupOf hYH hYsnH hL with
      h | h
    · exact (le_sSup (s := {L : Subgroup G | IsComponentOf L H ∧ L ≤ Y}) ⟨hL, h⟩).trans
        le_sup_right
    · exact (le_sSup (s := {L : Subgroup G | IsComponentOf L H ∧ ⁅L, Y⁆ = ⊥}) ⟨hL, h⟩).trans
        le_sup_left
  have hYE₂ : Y ≤ Subgroup.centralizer (E₂ : Set G) := Subgroup.le_centralizer_iff.mp hE₂C
  have hE₁E₂ : E₁ ≤ Subgroup.centralizer (E₂ : Set G) := hE₁Y.trans hYE₂
  have hFE : F ≤ Subgroup.centralizer (E : Set G) := fittingSubgroupOf_le_centralizer_layer H
  have hxE : x ∈ Subgroup.centralizer (E : Set G) :=
    hFE (qCoreOf_le_fittingSubgroupOf H p hp hx)
  obtain ⟨f, hf, e, he, rfl⟩ :=
    mem_sup_decompose_of_centralizes (hYF hy) (componentLayerOf_le_centralizer_fitting H)
  obtain ⟨e₂, he₂, e₁, he₁, rfl⟩ := mem_sup_decompose_of_centralizes (hE he) hE₁E₂
  set y' := f * e₂ with hy'def
  have hy'Y : y' ∈ Y := by
    have : y' = f * (e₂ * e₁) * e₁⁻¹ := by rw [hy'def]; group
    rw [this]
    exact Y.mul_mem hy (Y.inv_mem (hE₁Y he₁))
  have he₂F : e₂ ∈ F := by
    have he₂C₂ : e₂ ∈ Subgroup.centralizer (E₂ : Set G) := by
      have : e₂ = f⁻¹ * y' := by rw [hy'def]; group
      rw [this]
      exact Subgroup.mul_mem _ (Subgroup.inv_mem _
        ((Subgroup.centralizer_le hE₂E) (hFE hf))) (hYE₂ hy'Y)
    have he₂C₁ : e₂ ∈ Subgroup.centralizer (E₁ : Set G) :=
      Subgroup.le_centralizer_iff.mp hE₁E₂ he₂
    have he₂C : e₂ ∈ Subgroup.centralizer (E : Set G) :=
      Subgroup.centralizer_le hE (fstar_centralizer_of_centralizes_join he₂C₂ he₂C₁)
    exact generalizedFittingSubgroupOf_inf_centralizer_le H
      ⟨(le_sup_right : E ≤ generalizedFittingSubgroupOf H) (hE₂E he₂), he₂C⟩
  have hy'F : y' ∈ F := F.mul_mem hf he₂F
  obtain ⟨u, hu, c, hc, hy'uc, -, ⟨k, hk⟩, hcop⟩ :=
    exists_pow_mul_pow hp (isOfFinOrder_of_finite y')
  have huY : u ∈ Y := (Subgroup.zpowers_le.mpr hy'Y) hu
  have hcY : c ∈ Y := (Subgroup.zpowers_le.mpr hy'Y) hc
  have huF : u ∈ F := (Subgroup.zpowers_le.mpr hy'F) hu
  have hcF : c ∈ F := (Subgroup.zpowers_le.mpr hy'F) hc
  have huP : u ∈ P := by
    have : Fact p.Prime := ⟨hp⟩
    have hup : IsPGroup p (Subgroup.zpowers u) := by
      refine IsPGroup.iff_orderOf.mpr fun g => ?_
      obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow hp).mp ((orderOf_dvd_of_mem_zpowers g.2).trans hk)
      exact ⟨j, by rw [← Subgroup.orderOf_coe g]; exact hj⟩
    have hsn : ((Subgroup.zpowers u).subgroupOf H).IsSubnormal :=
      isSubnormal_subgroupOf_trans (Subgroup.zpowers_le.mpr huF)
        (isSubnormal_of_nilpotent (CFSG.fittingSubgroupOf_isNilpotent H) _
          (Subgroup.zpowers_le.mpr huF))
        (isSubnormal_subgroupOf_of_isNormalIn (fittingSubgroupOf_isNormalIn H))
    exact le_qCoreOf_of_isSubnormal_isPGroup H _ p
      (Subgroup.zpowers_le.mpr (generalizedFittingSubgroupOf_le H
        ((le_sup_left : F ≤ generalizedFittingSubgroupOf H) huF))) hsn hup
      (Subgroup.mem_zpowers u)
  have hcP : c ∈ Subgroup.centralizer (P : Set G) :=
    mem_centralizer_qCoreOf_of_coprime H hp hcF hcop
  have hxu : x * u * x⁻¹ ∈ Y ⊓ P := (Subgroup.mem_normalizer_iff.mp hxN u).mp ⟨huY, huP⟩
  have hxc : x * c * x⁻¹ = c := by
    rw [Subgroup.mem_centralizer_iff.mp hcP x hx, mul_inv_cancel_right]
  have hxe₁ : x * e₁ * x⁻¹ = e₁ := by
    rw [← Subgroup.mem_centralizer_iff.mp hxE e₁ (hE₁E he₁), mul_inv_cancel_right]
  have heq : x * (f * (e₂ * e₁)) * x⁻¹ = (x * u * x⁻¹) * (x * c * x⁻¹) * (x * e₁ * x⁻¹) := by
    have : f * (e₂ * e₁) = u * c * e₁ := by rw [← hy'uc, hy'def, mul_assoc]
    rw [this]
    group
  rw [heq, hxc, hxe₁]
  exact Y.mul_mem (Y.mul_mem hxu.1 hcY) (hE₁Y he₁)

theorem mem_normalizer_of_mem_normalizer_inf_qCoreOf {H Y : Subgroup G} {p : ℕ} (hp : p.Prime)
    (hYF : Y ≤ generalizedFittingSubgroupOf H)
    (hY : (Y.subgroupOf (generalizedFittingSubgroupOf H)).IsSubnormal) {x : G}
    (hx : x ∈ qCoreOf H p)
    (hxN : x ∈ Subgroup.normalizer ((Y ⊓ qCoreOf H p : Subgroup G) : Set G)) :
    x ∈ Subgroup.normalizer (Y : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro y
  refine ⟨conj_mem_of_mem_normalizer_inf_qCoreOf hp hYF hY hx hxN, fun h => ?_⟩
  have := conj_mem_of_mem_normalizer_inf_qCoreOf hp hYF hY (Subgroup.inv_mem _ hx)
    (Subgroup.inv_mem _ hxN) h
  simpa [mul_assoc] using this

omit [Finite G] in
theorem commutator_self_eq_of_isComponentOf {L X : Subgroup G} (hL : IsComponentOf L X) :
    ⁅L, L⁆ = L :=
  (Subgroup.isPerfect_iff (H := L)).mp ((Group.isPerfect_def).2 hL.2.2.2.1)

theorem le_commutator_or_eq_bot {L X : Subgroup G} (hL : IsComponentOf L X) {x : G}
    (hx : x ∈ X) : ⁅L, Subgroup.zpowers x⁆ = ⊥ ∨ L ≤ ⁅L, Subgroup.zpowers x⁆ := by
  by_cases hN : x ∈ Subgroup.normalizer (L : Set G)
  · exact commutator_eq_bot_or_le_of_isComponentOf hL (Subgroup.zpowers_le.mpr hN)
  · right
    set L' := L.map (MulAut.conj x).toMonoidHom with hL'def
    have hL' : IsComponentOf L' X := isComponentOf_map_conj hL (X.le_normalizer hx)
    have hne : L ≠ L' := fun h => hN (Bender35.mem_normalizer_of_map_conj_eq h.symm)
    have hcomm : L ≤ Subgroup.centralizer (L' : Set G) :=
      Subgroup.commutator_eq_bot_iff_le_centralizer.mp
        ((isComponentOf_eq_or_commutator_eq_bot hL hL').resolve_left hne)
    have hN' : L ≤ Subgroup.normalizer
        ((⁅L, Subgroup.zpowers x⁆ : Subgroup G) : Set G) :=
      Subgroup.normalizer_commutator_ge_left _ _
    calc L = ⁅L, L⁆ := (commutator_self_eq_of_isComponentOf hL).symm
      _ ≤ ⁅L, Subgroup.zpowers x⁆ := by
        rw [Subgroup.commutator_le]
        intro l hl m hm
        have hlx : ⁅l, x⁆ ∈ ⁅L, Subgroup.zpowers x⁆ :=
          Subgroup.commutator_mem_commutator hl (Subgroup.mem_zpowers x)
        have hl' : x * l⁻¹ * x⁻¹ ∈ L' := ⟨l⁻¹, L.inv_mem hl, rfl⟩
        have hml : m * (x * l⁻¹ * x⁻¹) = (x * l⁻¹ * x⁻¹) * m :=
          ((Subgroup.mem_centralizer_iff.mp (hcomm hm)) _ hl').symm
        have heq : ⁅l, m⁆ = ⁅⁅l, x⁆, m⁆ := by
          simp only [commutatorElement_def]
          calc l * m * l⁻¹ * m⁻¹ = l * (x * l⁻¹ * x⁻¹) * m * (x * l⁻¹ * x⁻¹)⁻¹ * l⁻¹ * m⁻¹ := by
                rw [mul_assoc l (x * l⁻¹ * x⁻¹) m, ← hml]
                group
            _ = l * x * l⁻¹ * x⁻¹ * m * (l * x * l⁻¹ * x⁻¹)⁻¹ * m⁻¹ := by group
        rw [heq, commutatorElement_def]
        exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hlx
          ((Subgroup.mem_normalizer_iff.mp (hN' hm) _).mp (Subgroup.inv_mem _ hlx)))
          (Subgroup.one_mem _) |> fun h => by simpa [mul_assoc] using h

omit [Finite G] in
theorem isCyclic_of_le {E Q : Subgroup G} (hEQ : E ≤ Q) (hQ : IsCyclic Q) : IsCyclic E := by
  have : IsCyclic (E.subgroupOf Q) := Subgroup.isCyclic _
  exact (Subgroup.subgroupOfEquivOfLe hEQ).isCyclic.mp this

omit [Finite G] in
theorem isElemAbelian_of_le {E E₀ : Subgroup G} {p : ℕ} (hE₀ : CFSG.Open.IsElemAbelian p E₀)
    (hEE₀ : E ≤ E₀) : CFSG.Open.IsElemAbelian p E := CFSG.Open.IsElemAbelian.mono hE₀ hEE₀

omit [Finite G] in
theorem isElemAbelian_zpowers {p : ℕ} {z : G} (hz : z ^ p = 1) :
    CFSG.Open.IsElemAbelian p (Subgroup.zpowers z) := CFSG.Open.isElemAbelian_zpowers hz

theorem not_isCyclic_of_isElemAbelian {E : Subgroup G} {p : ℕ} (hp : p.Prime)
    (hE : CFSG.Open.IsElemAbelian p E) (hcard : p ^ 2 ≤ Nat.card E) : ¬ IsCyclic E := by
  intro hcyc
  have h := Bender35.card_le_of_isCyclic_of_pow_eq_one hp hcyc hE.2
  have := hp.one_lt
  nlinarith

theorem exists_le_isElemAbelian_card_sq {E₀ : Subgroup G} {p : ℕ} (hp : p.Prime)
    (hE₀ : CFSG.Open.IsElemAbelian p E₀) (hE₀p : IsPGroup p E₀) (hcard : p ^ 2 ≤ Nat.card E₀) :
    ∃ E ≤ E₀, CFSG.Open.IsElemAbelian p E ∧ Nat.card E = p ^ 2 := by
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨k, hk⟩ := hE₀p.exists_card_eq
  have hk2 : 2 ≤ k := by
    rw [hk] at hcard
    exact (Nat.pow_le_pow_iff_right hp.one_lt).mp hcard
  obtain ⟨K, hK⟩ := Sylow.exists_subgroup_card_pow_prime (G := E₀) p (n := 2)
    (hk ▸ Nat.pow_dvd_pow p hk2)
  refine ⟨K.map E₀.subtype, Subgroup.map_subtype_le _,
    isElemAbelian_of_le hE₀ (Subgroup.map_subtype_le _), ?_⟩
  rw [Subgroup.card_map_of_injective E₀.subtype_injective, hK]

theorem exists_isElemAbelian_card_sq {Q : Subgroup G} {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hQp : IsPGroup p Q) (hQ : ¬ IsCyclic Q) :
    ∃ E ≤ Q, CFSG.Open.IsElemAbelian p E ∧ Nat.card E = p ^ 2 := by
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨X, hXQ, hXc, hXexp, -⟩ := exists_noncyclic_exponent_le hp hp2 hQp hQ
  obtain ⟨z, hzX, x, hxX, hz1, hzC, hxz, -, -, -⟩ := exists_typePP hp hp2 (hQp.to_le hXQ) le_rfl
    X.le_normalizer hXexp hXc (t := 1) (mul_one 1) (Subgroup.one_mem _) (Subgroup.one_mem _)
  set E₀ := Subgroup.zpowers z ⊔ Subgroup.zpowers x
  have hzx : Subgroup.zpowers z ≤ Subgroup.centralizer ((Subgroup.zpowers x : Subgroup G) :
      Set G) := by
    rw [centralizer_zpowers_eq', Subgroup.zpowers_le, Subgroup.mem_centralizer_singleton_iff]
    exact ((Subgroup.mem_centralizer_iff.mp hzC) x hxX).symm
  have hE₀ : CFSG.Open.IsElemAbelian p E₀ := isElemAbelian_sup (isElemAbelian_zpowers
    (hXexp z hzX)) (isElemAbelian_zpowers (hXexp x hxX)) hzx
  have hE₀Q : E₀ ≤ Q := sup_le (Subgroup.zpowers_le.mpr (hXQ hzX))
    (Subgroup.zpowers_le.mpr (hXQ hxX))
  have hzp : Nat.card (Subgroup.zpowers z) = p := by
    rw [Nat.card_zpowers, orderOf_eq_prime (hXexp z hzX) hz1]
  have hlt : Subgroup.zpowers z < E₀ := lt_of_le_of_ne le_sup_left fun h =>
    hxz (h ▸ (le_sup_right : Subgroup.zpowers x ≤ E₀) (Subgroup.mem_zpowers x))
  have hge := card_ge_of_lt' hp (hQp.to_le hE₀Q) hlt
  rw [hzp, ← pow_two] at hge
  obtain ⟨E, hEE₀, hE, hEc⟩ := exists_le_isElemAbelian_card_sq hp hE₀ (hQp.to_le hE₀Q) hge
  exact ⟨E, hEE₀.trans hE₀Q, hE, hEc⟩

theorem not_isCyclic_center_commutator {P : Subgroup G} {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hPp : IsPGroup p P) (hP' : ¬ IsCyclic (⁅P, P⁆ : Subgroup G)) :
    ¬ IsCyclic (⁅P, P⁆ ⊓ Subgroup.centralizer ((⁅P, P⁆ : Subgroup G) : Set G) : Subgroup G) := by
  have : Fact p.Prime := ⟨hp⟩
  have hP'P : ⁅P, P⁆ ≤ P := Bender35.commutator_self_le P
  obtain ⟨X, hXQ, hXc, hXexp, hXN⟩ := exists_noncyclic_exponent_le hp hp2 (hPp.to_le hP'P) hP'
  have hPX : P ≤ Subgroup.normalizer (X : Set G) :=
    (Subgroup.normalizer_commutator_ge_left P P).trans hXN
  obtain ⟨z, hzX, x, hxX, hz1, hzC, hxz, hxP, -, -⟩ := exists_typePP hp hp2 hPp (hXQ.trans hP'P)
    hPX hXexp hXc (t := 1) (mul_one 1) (Subgroup.one_mem _) (Subgroup.one_mem _)
  have hP'x := (card_le_and_commutator_le_of_commutator_mem hzC hxP le_rfl).2
  set E₀ := Subgroup.zpowers z ⊔ Subgroup.zpowers x
  have hzx : Subgroup.zpowers z ≤ Subgroup.centralizer ((Subgroup.zpowers x : Subgroup G) :
      Set G) := by
    rw [centralizer_zpowers_eq', Subgroup.zpowers_le, Subgroup.mem_centralizer_singleton_iff]
    exact ((Subgroup.mem_centralizer_iff.mp hzC) x (hP'P (hXQ hxX))).symm
  have hE₀ : CFSG.Open.IsElemAbelian p E₀ := isElemAbelian_sup (isElemAbelian_zpowers
    (hXexp z hzX)) (isElemAbelian_zpowers (hXexp x hxX)) hzx
  have hE₀Z : E₀ ≤ ⁅P, P⁆ ⊓ Subgroup.centralizer ((⁅P, P⁆ : Subgroup G) : Set G) := by
    refine sup_le (Subgroup.zpowers_le.mpr ⟨hXQ hzX, ?_⟩) (Subgroup.zpowers_le.mpr ⟨hXQ hxX, ?_⟩)
    · exact Subgroup.centralizer_le (fun _ hy => hP'P hy) hzC
    · exact Subgroup.mem_centralizer_iff.mpr fun y hy =>
        Subgroup.mem_centralizer_singleton_iff.mp (hP'x hy)
  have hzp : Nat.card (Subgroup.zpowers z) = p := by
    rw [Nat.card_zpowers, orderOf_eq_prime (hXexp z hzX) hz1]
  have hlt : Subgroup.zpowers z < E₀ := lt_of_le_of_ne le_sup_left fun h =>
    hxz (h ▸ (le_sup_right : Subgroup.zpowers x ≤ E₀) (Subgroup.mem_zpowers x))
  have hge := card_ge_of_lt' hp (hPp.to_le (hE₀Z.trans (inf_le_left.trans hP'P))) hlt
  rw [hzp, ← pow_two] at hge
  exact fun hcyc => not_isCyclic_of_isElemAbelian hp hE₀ hge (isCyclic_of_le hE₀Z hcyc)

omit [Finite G] in
theorem conj_pow_eq_inv {t w : G} (h : t * w * t⁻¹ = w⁻¹) (n : ℕ) :
    t * w ^ n * t⁻¹ = (w ^ n)⁻¹ := by
  rw [← MulAut.conj_apply, map_pow, MulAut.conj_apply, h, inv_pow]

omit [Finite G] in
theorem exists_orderOf_eq_prime_of_conj_eq_inv {P : Subgroup G} {p : ℕ} (hp : p.Prime)
    (hPp : IsPGroup p P) {w t : G} (hwP : w ∈ P) (hw : w ≠ 1) (htw : t * w * t⁻¹ = w⁻¹) :
    ∃ x ∈ Subgroup.zpowers w, orderOf x = p ∧ t * x * t⁻¹ = x⁻¹ := by
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.mp hPp) ⟨w, hwP⟩
  rw [Subgroup.orderOf_mk] at hk
  have hk0 : k ≠ 0 := by
    rintro rfl
    rw [pow_zero, orderOf_eq_one_iff] at hk
    exact hw hk
  refine ⟨w ^ (p ^ (k - 1)), Subgroup.npow_mem_zpowers _ _, ?_, conj_pow_eq_inv htw _⟩
  have hdvd : p ^ (k - 1) ∣ orderOf w := hk ▸ Nat.pow_dvd_pow p (Nat.sub_le k 1)
  rw [orderOf_pow_of_dvd (pow_ne_zero _ hp.ne_zero) hdvd, hk]
  conv_lhs => rw [show k = (k - 1) + 1 by omega, pow_succ]
  exact Nat.mul_div_cancel_left p (pow_pos hp.pos _)

theorem le_centralizer_of_isCyclic {C Z : Subgroup G} {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hCp : IsPGroup p C) (hC : IsCyclic C) (hZC : Z ≤ C) (hZp : Nat.card Z = p) {b : G}
    (hb : b * b = 1) (hbC : b ∈ Subgroup.normalizer (C : Set G))
    (hbZ : Z ≤ Subgroup.centralizer ({b} : Set G)) : C ≤ Subgroup.centralizer ({b} : Set G) := by
  have : Fact p.Prime := ⟨hp⟩
  intro g hg
  by_contra hgb
  set w := ⁅g, b⁆ with hwdef
  have hwC : w ∈ C := by
    have : w = g * (b * g⁻¹ * b⁻¹) := by rw [hwdef, commutatorElement_def]; group
    rw [this]
    exact C.mul_mem hg ((Subgroup.mem_normalizer_iff.mp hbC _).mp (C.inv_mem hg))
  have hw1 : w ≠ 1 := by
    rw [hwdef, Ne, commutatorElement_eq_one_iff_mul_comm]
    exact fun h => hgb (Subgroup.mem_centralizer_singleton_iff.mpr h)
  obtain ⟨y, hyw, hyo, hby⟩ := exists_orderOf_eq_prime_of_conj_eq_inv hp hCp hwC hw1
    (conj_commutatorElement_eq_inv hb g)
  have hyC : y ∈ C := (Subgroup.zpowers_le.mpr hwC) hyw
  have hCab : IsMulCommutative C := hC.isMulCommutative
  have hCc : C ≤ Subgroup.centralizer (C : Set G) := by
    intro c hc
    rw [Subgroup.mem_centralizer_iff]
    intro d hd
    exact congrArg Subtype.val (hCab.is_comm.comm ⟨d, hd⟩ ⟨c, hc⟩)
  have hZel : CFSG.Open.IsElemAbelian p Z := by
    refine ⟨⟨⟨fun a b => Subtype.ext ?_⟩⟩, fun x hx => ?_⟩
    · exact (Subgroup.mem_centralizer_iff.mp (hCc (hZC b.2))) a (hZC a.2)
    · exact orderOf_dvd_iff_pow_eq_one.mp (hZp ▸ Subgroup.orderOf_dvd_natCard Z hx)
  have hyel : CFSG.Open.IsElemAbelian p (Subgroup.zpowers y) :=
    isElemAbelian_zpowers (hyo ▸ pow_orderOf_eq_one y)
  have hZy : Z ≤ Subgroup.centralizer ((Subgroup.zpowers y : Subgroup G) : Set G) := by
    rw [centralizer_zpowers_eq']
    intro z hz
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact (Subgroup.mem_centralizer_iff.mp (hCc hyC)) z (hZC hz)
  set E := Z ⊔ Subgroup.zpowers y
  have hEC : E ≤ C := sup_le hZC (Subgroup.zpowers_le.mpr hyC)
  have hEel := isElemAbelian_sup hZel hyel hZy
  have hEcard := Bender35.card_le_of_isCyclic_of_pow_eq_one hp (isCyclic_of_le hEC hC) hEel.2
  have hZE : Z = E := Subgroup.eq_of_le_of_card_ge le_sup_left (hZp ▸ hEcard)
  have hyZ : y ∈ Z := hZE ▸ (le_sup_right : Subgroup.zpowers y ≤ E) (Subgroup.mem_zpowers y)
  have hyb : b * y * b⁻¹ = y := by
    rw [← Subgroup.mem_centralizer_singleton_iff.mp (hbZ hyZ), mul_inv_cancel_right]
  have hyy : y * y = 1 := by
    have h := hby
    rw [hyb] at h
    calc y * y = y * y⁻¹ := by rw [← h]
      _ = 1 := mul_inv_cancel y
  have h2 : orderOf y ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [pow_two, hyy])
  rw [hyo] at h2
  exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp h2)

end CFSG.Goldschmidt.G55
