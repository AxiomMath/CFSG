module

public import CFSG.LargeExtraspecial.S5C
public import CFSG.LargeExtraspecial.S5Comp

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.S5

open Subgroup Module CFSG.LargeExtraspecial.S4

variable {G : Type*} [Group G] [Finite G] {S : Setting G} {g : G}

@[expose] noncomputable def imgR (haQ : g * S.z * g⁻¹ ∈ S.QG) (t : S.O) (X : Subgroup S.O) :
    Subgroup (Vt S g t ≃ₗ[ZMod 2] Vt S g t) :=
  (X.subgroupOf (Rbar S g t)).map (resV haQ t)

theorem mem_imgR {haQ : g * S.z * g⁻¹ ∈ S.QG} {t : S.O} {X : Subgroup S.O}
    {e : Vt S g t ≃ₗ[ZMod 2] Vt S g t} :
    e ∈ imgR haQ t X ↔ ∃ y : Rbar S g t, (y : S.O) ∈ X ∧ resV haQ t y = e := by
  rw [imgR, mem_map]
  exact ⟨fun ⟨y, hy, hye⟩ => ⟨y, mem_subgroupOf.mp hy, hye⟩,
    fun ⟨y, hy, hye⟩ => ⟨y, mem_subgroupOf.mpr hy, hye⟩⟩

theorem imgR_le_RmodN (haQ : g * S.z * g⁻¹ ∈ S.QG) (t : S.O) (X : Subgroup S.O) :
    imgR haQ t X ≤ RmodN S g t := by
  rw [← range_resV haQ t]
  exact map_le_range _ _

theorem resV_mem_LmodN (haQ : g * S.z * g⁻¹ ∈ S.QG) {t : S.O} {s : S.O} (hs : s ∈ S.Lbar g)
    (hsR : s ∈ Rbar S g t) : resV haQ t ⟨s, hsR⟩ ∈ LmodN S g t :=
  ⟨s, hs, fun _ => rfl⟩

theorem exists_mul_mul_of_factor (H : Hyp4 S g) {t : S.O} (ht : t ∈ S.Lbar g)
    {X : Subgroup S.O}
    (hfac : ∀ x ∈ RmodN S g t, ∃ k ∈ imgR H.conj_mem t X, ∃ e ∈ LmodN S g t, x = k * e)
    {r : S.O} (hr : r ∈ Rbar S g t) :
    ∃ y ∈ X, y ∈ Rbar S g t ∧ ∃ s ∈ S.Lbar g, ∃ n ∈ Nbar S g t, r = y * s * n := by
  obtain ⟨k, hk, e, he, hke⟩ := hfac _ (by rw [← range_resV H.conj_mem t]; exact ⟨⟨r, hr⟩, rfl⟩)
  obtain ⟨y, hyX, rfl⟩ := mem_imgR.mp hk
  obtain ⟨s, hs, hse⟩ := he
  have hsR : s ∈ Rbar S g t := Lbar_le_Rbar ht hs
  have hres : resV H.conj_mem t ⟨s, hsR⟩ = e :=
    LinearEquiv.ext fun v => Subtype.ext (hse v).symm
  set n : Rbar S g t := (y * ⟨s, hsR⟩)⁻¹ * ⟨r, hr⟩ with hn
  have hnN : resV H.conj_mem t n = 1 := by
    rw [hn, map_mul, map_inv, map_mul, hres, ← hke, inv_mul_cancel]
  refine ⟨y, hyX, y.2, s, hs, n, (resV_eq_one_iff H.conj_mem n).mp hnN, ?_⟩
  rw [hn]
  simp only [coe_mul, coe_inv]
  group

theorem exists_apply_eq_of_factor (H : Hyp4 S g) {t : S.O} (ht : t ∈ S.Lbar g)
    {X : Subgroup S.O}
    (hfac : ∀ x ∈ RmodN S g t, ∃ k ∈ imgR H.conj_mem t X, ∃ e ∈ LmodN S g t, x = k * e)
    {r : S.O} (hr : r ∈ Rbar S g t) :
    ∃ y ∈ X, y ∈ Rbar S g t ∧ (y : S.Qt ≃ₗ[ZMod 2] S.Qt) (S.cl (g * S.z * g⁻¹)) =
      (r : S.Qt ≃ₗ[ZMod 2] S.Qt) (S.cl (g * S.z * g⁻¹)) := by
  obtain ⟨y, hyX, hyR, s, hs, n, hn, rfl⟩ := exists_mul_mul_of_factor H ht hfac hr
  refine ⟨y, hyX, hyR, ?_⟩
  have hna : (n : S.Qt ≃ₗ[ZMod 2] S.Qt) (S.cl (g * S.z * g⁻¹)) = S.cl (g * S.z * g⁻¹) :=
    hn.2 _ (cl_a_mem_Vt ht)
  have hsa : (s : S.Qt ≃ₗ[ZMod 2] S.Qt) (S.cl (g * S.z * g⁻¹)) = S.cl (g * S.z * g⁻¹) :=
    (mem_fixSub S).mp (by rw [H.fixSub_eq]; exact Submodule.mem_span_singleton_self _) s hs
  rw [coe_mul_apply, coe_mul_apply, hna, hsa]

theorem mem_Lbar_mul_of_factor (H : Hyp4 S g) {t : S.O} (ht : t ∈ S.Lbar g)
    {X : Subgroup S.O}
    (hfac : ∀ x ∈ RmodN S g t, ∃ k ∈ imgR H.conj_mem t X, ∃ e ∈ LmodN S g t, x = k * e)
    {τ : S.O} (hτL : τ ∈ S.Lbar g) (hτX : ∀ y ∈ X, τ * y = y * τ) {k : S.M}
    (hk : S.ρ k ∈ Rbar S g t) : τ ∈ S.Lbar ((k : G) * g) := by
  obtain ⟨y, hyX, -, s, hs, n, hn, hkr⟩ := exists_mul_mul_of_factor H ht hfac hk
  rw [mem_Lbar_mul_iff, hkr]
  have hnL := Nbar_le_normalizer H.conj_mem H.conj_ne (Lbar_mem_Dset ht) hn
  have hs' : s * τ = τ * s := Lbar_comm S H.conj_mem hs hτL
  have e : (y * s * n)⁻¹ * τ * (y * s * n) = n⁻¹ * τ * n := by
    calc (y * s * n)⁻¹ * τ * (y * s * n) = n⁻¹ * s⁻¹ * (y⁻¹ * (τ * y)) * s * n := by group
      _ = n⁻¹ * s⁻¹ * (y⁻¹ * (y * τ)) * s * n := by rw [hτX y hyX]
      _ = n⁻¹ * (s⁻¹ * (τ * s)) * n := by group
      _ = n⁻¹ * (s⁻¹ * (s * τ)) * n := by rw [hs']
      _ = n⁻¹ * τ * n := by group
  rw [e]
  have := (mem_normalizer_iff.mp (inv_mem hnL) τ).mp hτL
  simpa using this

theorem eq_one_or_eq_of_factor (H : Hyp4 S g) (C : Cons311 S g) {t : S.O}
    (ht : t ∈ S.Lbar g) (ht1 : t ≠ 1) (hVQ : ¬ V S g t ≤ S.Qa g) {X : Subgroup S.O}
    (hfac : ∀ x ∈ RmodN S g t, ∃ k ∈ imgR H.conj_mem t X, ∃ e ∈ LmodN S g t, x = k * e)
    {τ : S.O} (hτL : τ ∈ S.Lbar g) (hτX : ∀ y ∈ X, τ * y = y * τ) : τ = 1 ∨ τ = t := by
  refine eq_one_or_eq_of_forall H C ht ht1 hVQ hτL
    (fun k hk => mem_Lbar_mul_of_factor H ht hfac hτL hτX hk) fun r hr => ?_
  obtain ⟨y, hyX, hyR, hya⟩ := exists_apply_eq_of_factor H ht hfac hr
  exact ⟨y, hyR, (hτX y hyX).symm, hya⟩

theorem isSubnormal_imgR (haQ : g * S.z * g⁻¹ ∈ S.QG) {t : S.O} {X : Subgroup S.O}
    (hXR : X ≤ Rbar S g t) (hX : CFSG.Open.IsSubnormal X (Rbar S g t)) :
    CFSG.Open.IsSubnormal (imgR haQ t X) (RmodN S g t) := by
  have h1 := (isSubnormal_subgroupOf_top_iff hXR).mpr hX
  have h2 := CFSG.Quasithin.A3.subnormal_map (resV haQ t) h1
  rwa [← MonoidHom.range_eq_map, range_resV] at h2

theorem isQuasisimple_imgR (haQ : g * S.z * g⁻¹ ∈ S.QG) {t : S.O} {X : Subgroup S.O}
    (hXR : X ≤ Rbar S g t) (hq : CFSG.Open.IsQuasisimple X) (hXN : ¬ X ≤ Nbar S g t) :
    CFSG.Open.IsQuasisimple (imgR haQ t X) := by
  let φ : X →* (Vt S g t ≃ₗ[ZMod 2] Vt S g t) := (resV haQ t).comp (Subgroup.inclusion hXR)
  have hker : φ.ker ≠ ⊤ := by
    intro h
    apply hXN
    intro y hy
    have hmem : (⟨y, hy⟩ : X) ∈ φ.ker := h ▸ mem_top _
    exact (resV_eq_one_iff haQ _).mp (MonoidHom.mem_ker.mp hmem)
  have hq' := CFSG.ComponentClassification.Quasisimple.range_quasisimple_of_ker_ne_top hq φ hker
  have hrange : φ.range = imgR haQ t X := by
    ext e
    rw [MonoidHom.mem_range, mem_imgR]
    constructor
    · rintro ⟨y, rfl⟩
      exact ⟨Subgroup.inclusion hXR y, y.2, rfl⟩
    · rintro ⟨y, hy, rfl⟩
      exact ⟨⟨y, hy⟩, rfl⟩
  exact hrange ▸ hq'

theorem commute_of_mem_Lbar_inf_Nbar (H : Hyp4 S g) {t : S.O} (ht : t ∈ S.Lbar g)
    {X : Subgroup S.O} (hXR : X ≤ Rbar S g t) (hq : CFSG.Open.IsQuasisimple X)
    (hXN : ¬ X ≤ Nbar S g t) (hLX : ∀ s ∈ S.Lbar g, ∀ y ∈ X, s * y * s⁻¹ ∈ X)
    (hZ : ∀ z ∈ X, (∀ y ∈ X, z * y = y * z) → ∀ k : ℕ, z ^ (2 ^ k) = 1 → z = 1)
    {x : S.O} (hxL : x ∈ S.Lbar g) (hxN : x ∈ Nbar S g t) {y : S.O} (hy : y ∈ X) :
    x * y = y * x := by
  have haQ := H.conj_mem
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hyR := hXR hy
  obtain ⟨k, rfl⟩ := MonoidHom.mem_range.mp (Rbar_le_Mbar hyR)
  have hkt : S.ρ k * t = t * S.ρ k := commute_of_mem_Rbar haQ hyR
  set c := x * S.ρ k * x⁻¹ * (S.ρ k)⁻¹ with hc
  have hcX : c ∈ X := X.mul_mem (hLX x hxL _ hy) (X.inv_mem hy)
  have hy' : S.ρ k * x⁻¹ * (S.ρ k)⁻¹ ∈ Nbar S g t := conj_mem_Nbar haQ hkt (inv_mem hxN)
  have hcN : c ∈ Nbar S g t := by
    have : c = x * (S.ρ k * x⁻¹ * (S.ρ k)⁻¹) := by rw [hc]; group
    rw [this]
    exact mul_mem hxN hy'
  have htk : t ∈ S.Lbar ((k : G) * g) := mem_Lbar_mul_of_mem_Rbar H ht hyR
  have hxnorm : x ∈ normalizer (S.Lbar ((k : G) * g) : Set S.O) :=
    Nbar_le_normalizer haQ H.conj_ne (Lbar_mul_mem_Dset htk) hxN
  have hx2 : IsPGroup 2 (zpowers x) := by
    have hxx : x ^ (2 ^ 1) = 1 := by rw [pow_one, pow_two]; exact S4.mul_self_of_mem_Lbar S haQ hxL
    obtain ⟨i, -, hi⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp (orderOf_dvd_of_pow_eq_one hxx)
    exact IsPGroup.of_card (n := i) (by rw [Nat.card_zpowers, hi])
  have hP : IsPGroup 2 (zpowers x ⊔ S.Lbar ((k : G) * g) : Subgroup S.O) :=
    IsPGroup.to_sup_of_normal_right' hx2 (isPGroup_Lbar S (conj_mem_QG' S k.2 haQ))
      (zpowers_le.mpr hxnorm)
  have hcP : c ∈ (zpowers x ⊔ S.Lbar ((k : G) * g) : Subgroup S.O) := by
    have : c = x * (S.ρ k * x⁻¹ * (S.ρ k)⁻¹) := by rw [hc]; group
    rw [this]
    exact mul_mem (mem_sup_left (mem_zpowers x))
      (mem_sup_right (conj_mem_Lbar_mul S k (inv_mem hxL)))
  obtain ⟨j, hj⟩ := hP ⟨c, hcP⟩
  have hcj : c ^ (2 ^ j) = 1 := congrArg Subtype.val hj
  have hnorm : ∀ a ∈ X, ∀ n ∈ X ⊓ Nbar S g t, a * n * a⁻¹ ∈ X ⊓ Nbar S g t := by
    intro a ha n hn
    obtain ⟨k', rfl⟩ := MonoidHom.mem_range.mp (Rbar_le_Mbar (hXR ha))
    exact ⟨X.mul_mem (X.mul_mem ha hn.1) (X.inv_mem ha),
      conj_mem_Nbar haQ (commute_of_mem_Rbar haQ (hXR ha)) hn.2⟩
  rcases commute_or_eq_of_normalized hq inf_le_left hnorm with hcen | heq
  · have hc1 := hZ c hcX (fun y' hy' => hcen c ⟨hcX, hcN⟩ y' hy') j hcj
    calc x * S.ρ k = c * (S.ρ k * x) := by rw [hc]; group
      _ = S.ρ k * x := by rw [hc1, one_mul]
  · exact absurd (heq ▸ inf_le_right : X ≤ Nbar S g t) hXN

end CFSG.LargeExtraspecial.S5
