module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec8T84D2Def

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {G : Type} [Group G] [Finite G] {t : G} {E X1 X2 : Subgroup G}

theorem sec8t84d2_mem_autIn {Y : Subgroup G} {a : MulAut ↥E} (ha : a ∈ autIn Y E) :
    ∃ x ∈ Y, ∀ e : ↥E, ((a e : ↥E) : G) = x * (e : G) * x⁻¹ := by
  rw [autIn] at ha
  obtain ⟨n, hn, rfl⟩ := ha
  exact ⟨(n : G), hn, fun e => Subgroup.normalizerMonoidHom_apply_apply_coe E n e⟩

theorem sec8t84d2_conj_mem {Y : Subgroup G} (hY : Y ≤ normalizer (E : Set G)) {x : G}
    (hx : x ∈ Y) : ∃ a ∈ autIn Y E, ∀ e : ↥E, ((a e : ↥E) : G) = x * (e : G) * x⁻¹ := by
  refine ⟨E.normalizerMonoidHom ⟨x, hY hx⟩, ?_, fun e =>
    Subgroup.normalizerMonoidHom_apply_apply_coe E ⟨x, hY hx⟩ e⟩
  rw [autIn]
  exact Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr hx)

theorem sec8t84d2_equiv {Y : Subgroup G} (hY : Y ≤ normalizer (E : Set G))
    (hC : centralizer (E : Set G) ≤ Y) {F : Type} [Group F]
    (hq : QuotEquivTo Y (centralizer (E : Set G)) F) : Nonempty (↥(autIn Y E) ≃* F) := by
  let φ : ↥Y →* MulAut ↥E := E.normalizerMonoidHom.comp (Subgroup.inclusion hY)
  have hrange : φ.range = autIn Y E := by
    rw [autIn, ← Subgroup.inclusion_range hY, ← MonoidHom.map_range]
  have hker : φ.ker = (centralizer (E : Set G)).subgroupOf Y := by
    ext y
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    change E.normalizerMonoidHom (Subgroup.inclusion hY y) = 1 ↔ (y : G) ∈ centralizer (E : Set G)
    rw [← MonoidHom.mem_ker, Subgroup.normalizerMonoidHom_ker, Subgroup.mem_subgroupOf]
    simp
  obtain ⟨f, hf_surj, hf_ker⟩ := hq
  haveI hnorm : ((centralizer (E : Set G)).subgroupOf Y).Normal := hf_ker ▸ inferInstance
  refine ⟨?_⟩
  exact (((QuotientGroup.quotientMulEquivOfEq hker.symm).trans
    (QuotientGroup.quotientKerEquivRange φ)).trans (MulEquiv.subgroupCongr hrange)).symm.trans
    ((QuotientGroup.quotientMulEquivOfEq hf_ker.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective (φ := f) hf_surj))

theorem sec8t84d2_comm (hX : Sec8X G t E X1 X2) :
    ∀ a ∈ autIn X1 E, ∀ b ∈ autIn X2 E, a * b = b * a := by
  intro a ha b hb
  obtain ⟨x, hxX1, hax⟩ := sec8t84d2_mem_autIn ha
  obtain ⟨y, hyX2, hby⟩ := sec8t84d2_mem_autIn hb
  have hxN : x ∈ normalizer (E : Set G) := hX.le1 hxX1
  have hyN : y ∈ normalizer (E : Set G) := hX.le2 hyX2
  have hc : x * y * x⁻¹ * y⁻¹ ∈ centralizer (E : Set G) := hX.comm x hxX1 y hyX2
  ext e
  rw [MulAut.mul_apply, MulAut.mul_apply, hax, hby, hby, hax]
  have hxe : x * (e : G) * x⁻¹ ∈ E := (Subgroup.mem_normalizer_iff.mp hxN (e : G)).mp e.2
  have hdE : y * (x * (e : G) * x⁻¹) * y⁻¹ ∈ E :=
    (Subgroup.mem_normalizer_iff.mp hyN _).mp hxe
  have hcd : (x * y * x⁻¹ * y⁻¹) * (y * (x * (e : G) * x⁻¹) * y⁻¹) *
      (x * y * x⁻¹ * y⁻¹)⁻¹ = y * (x * (e : G) * x⁻¹) * y⁻¹ := by
    rw [← Subgroup.mem_centralizer_iff.mp hc _ hdE]
    group
  calc x * (y * (e : G) * y⁻¹) * x⁻¹
      = (x * y) * (e : G) * (x * y)⁻¹ := by group
    _ = ((x * y * x⁻¹ * y⁻¹) * (y * x)) * (e : G) *
          ((x * y * x⁻¹ * y⁻¹) * (y * x))⁻¹ := by group
    _ = (x * y * x⁻¹ * y⁻¹) * ((y * x) * (e : G) * (y * x)⁻¹) *
          (x * y * x⁻¹ * y⁻¹)⁻¹ := by group
    _ = (y * x) * (e : G) * (y * x)⁻¹ := by
          rw [show (y * x) * (e : G) * (y * x)⁻¹ =
            y * (x * (e : G) * x⁻¹) * y⁻¹ by group]
          exact hcd
    _ = y * (x * (e : G) * x⁻¹) * y⁻¹ := by group

theorem sec8t84d2_E_comm {k : ℕ} (hE : IsElemAb2 E k) : ∀ x y : ↥E, x * y = y * x :=
  fun x y => hE.1.1.is_comm.comm x y

theorem sec8t84d2_E_sq {k : ℕ} (hE : IsElemAb2 E k) : ∀ x : ↥E, x * x = 1 := by
  intro x
  apply Subtype.ext
  simpa [pow_two] using hE.1.2 x x.2

theorem sec8t84d2_orderOf_five_iff {x : G} (hx : x ∈ normalizer (E : Set G)) {a : MulAut ↥E}
    (ha : ∀ e : ↥E, ((a e : ↥E) : G) = x * (e : G) * x⁻¹) :
    orderOf a = 5 ↔ (x ^ 5 ∈ centralizer (E : Set G) ∧ x ∉ centralizer (E : Set G)) := by
  have ha_eq : a = E.normalizerMonoidHom ⟨x, hx⟩ := by
    ext e
    rw [ha, Subgroup.normalizerMonoidHom_apply_apply_coe]
  have hxpow : x ^ 5 ∈ normalizer (E : Set G) := pow_mem hx 5
  have hpow_eq : a ^ 5 = E.normalizerMonoidHom ⟨x ^ 5, hxpow⟩ := by
    rw [ha_eq, ← map_pow]
    rfl
  have hker5 : E.normalizerMonoidHom ⟨x ^ 5, hxpow⟩ = 1 ↔ x ^ 5 ∈ centralizer (E : Set G) := by
    rw [← MonoidHom.mem_ker, Subgroup.normalizerMonoidHom_ker, Subgroup.mem_subgroupOf]
  have hker1 : E.normalizerMonoidHom ⟨x, hx⟩ = 1 ↔ x ∈ centralizer (E : Set G) := by
    rw [← MonoidHom.mem_ker, Subgroup.normalizerMonoidHom_ker, Subgroup.mem_subgroupOf]
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  rw [orderOf_eq_prime_iff]
  constructor
  · rintro ⟨h5, hne⟩
    exact ⟨hker5.mp (by rwa [hpow_eq] at h5), fun hxin => hne (by
      rw [ha_eq]
      exact hker1.mpr hxin)⟩
  · rintro ⟨h5C, hxC⟩
    exact ⟨by rw [hpow_eq]; exact hker5.mpr h5C, fun h1 =>
      hxC (hker1.mp (by rwa [ha_eq] at h1))⟩

theorem sec8t84d2_ctx (hCE : Asc82FinkCE) {L S : Subgroup G} {z g : G} {B : Subgroup G}
    (hE : Sec8E G t L S z g B E) (hX : Sec8X G t E X1 X2) : Sec8T84DCtx G t E X1 X2 := by
  have ht2 : t ^ 2 = 1 := by
    have h := pow_orderOf_eq_one t
    rwa [hE.ctx.involution] at h
  exact
    { elem := hE.elem
      hX := hX
      t_sq := by simpa [pow_two] using ht2
      hCE := (hCE G t L S z g B E hE).1
      hO := (hCE G t L S z g B E hE).2 }

end CFSG.OddStandard.SmallF3.Omega
