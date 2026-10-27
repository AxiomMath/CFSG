module

public import CFSG.HardMathSupport.Timmesfeld.Balance.Basic
import CFSG.GroupTheory.Fitting.LayerTopBot
public import CFSG.HardMathSupport.Timmesfeld.Proving.ExistsOrderPCentralizer
public import CFSG.HardMathSupport.Timmesfeld.Proving.GLAPrimeCoreCentralizer

public section

namespace CFSG.HardMathSupport.Timmesfeld.Balance

open CFSG CFSG.LocalCores CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.HardMathSupport.Solomon.LocalBalance
  CFSG.ClassicalInvolution.Balance.LocalBalance

universe u

variable {Y : Type u} [Group Y] [Finite Y] {p : ℕ}

theorem mem_centralizer_layer_of_central_p {X : Type*} [Group X] [Finite X] {L : Subgroup X}
    (hL : IsComponent L) {a : X} (ha : a ∈ L) (hcen : ∀ w ∈ L, w * a = a * w) :
    a ∈ Subgroup.centralizer (layer X : Set X) :=
  CFSG.WholeGroup.mem_centralizer_layer_of_mem_component hL ha hcen

theorem isPGroup_zpowers_of_pow_eq_one (hp : p.Prime) {Z : Type*} [Group Z] {g : Z}
    (hg : g ^ p = 1) : IsPGroup p (Subgroup.zpowers g) := by
  have : Fact p.Prime := ⟨hp⟩
  have : Finite (Subgroup.zpowers g) := by
    have : IsOfFinOrder g := isOfFinOrder_iff_pow_eq_one.mpr ⟨p, hp.pos, hg⟩
    exact this.finite_zpowers
  rw [IsPGroup.iff_card, Nat.card_zpowers]
  have h2 : orderOf g ∣ p ^ 1 := by
    rw [pow_one]
    exact orderOf_dvd_of_pow_eq_one hg
  obtain ⟨i, -, hi⟩ := (Nat.dvd_prime_pow hp).mp h2
  exact ⟨i, hi⟩

theorem conj_mem_gLAPPrimeCoreOf_of_mem_centralizer {Z : Type*} [Group Z] {p : ℕ} {a c u : Z}
    (hc : c ∈ Subgroup.centralizer ({a} : Set Z))
    (hu : u ∈ GLAPPrimeCoreOf p (Subgroup.centralizer ({a} : Set Z))) :
    c * u * c⁻¹ ∈ GLAPPrimeCoreOf p (Subgroup.centralizer ({a} : Set Z)) := by
  obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.1 hu
  refine Subgroup.mem_map.2 ⟨(⟨c, hc⟩ : ↥(Subgroup.centralizer ({a} : Set Z))) * y *
    (⟨c, hc⟩ : ↥(Subgroup.centralizer ({a} : Set Z)))⁻¹,
    (GLAPPrimeCore.normal p _).conj_mem y hy _, ?_⟩
  simp

theorem conjSub_eq_of_mem_gLAPPrimeCoreOf (hH1 : H1Stmt.{u}) (hp : p.Prime) {L : Subgroup Y}
    (hL : IsComponent L) (hLp : p ∣ Nat.card (↥L ⧸ Subgroup.center ↥L)) {f : Y}
    (hf : f ^ p = 1) (hfL : conjSub f L = L) {d : Y}
    (hd : d ∈ GLAPPrimeCoreOf p (Subgroup.centralizer ({f} : Set Y))) : conjSub d L = L := by
  by_contra hne
  have hL₂ : IsComponent (conjSub d L) := isComponent_map_mulEquiv (MulAut.conj d) hL
  have hcomm : ∀ a ∈ L, ∀ b ∈ conjSub d L, a * b = b * a :=
    commute_of_isComponent_of_ne hL hL₂ (fun h => hne h.symm)
  have hEn : (layer Y).Normal := by
    have : (layer Y).Characteristic := layer_characteristic
    infer_instance
  set CE : Subgroup Y := Subgroup.centralizer (layer Y : Set Y) with hCE
  have hCEn : CE.Normal := Subgroup.normal_centralizer
  let π : Y →* Y ⧸ CE := QuotientGroup.mk' CE
  have hπ : Function.Surjective π := QuotientGroup.mk'_surjective CE
  have hLE : L ≤ layer Y := component_le_layer hL
  have hinter : ∀ a ∈ L, ∀ b ∈ conjSub d L, π a = π b → π a = 1 := by
    intro a ha b hb hab
    have hmem : a⁻¹ * b ∈ CE := QuotientGroup.eq.mp hab
    have hc : ∀ w ∈ L, w * a = a * w := by
      intro w hw
      have h1 : w * (a⁻¹ * b) = (a⁻¹ * b) * w := Subgroup.mem_centralizer_iff.mp hmem w (hLE hw)
      have h2 : w * b = b * w := hcomm w hw b hb
      have h3 : w * a⁻¹ = a⁻¹ * w := by
        have h4 : w * a⁻¹ * b = a⁻¹ * w * b := by
          calc w * a⁻¹ * b = w * (a⁻¹ * b) := by group
            _ = (a⁻¹ * b) * w := h1
            _ = a⁻¹ * (b * w) := by group
            _ = a⁻¹ * (w * b) := by rw [h2]
            _ = a⁻¹ * w * b := by group
        exact mul_right_cancel h4
      calc w * a = a * (a⁻¹ * w) * a := by group
        _ = a * (w * a⁻¹) * a := by rw [h3]
        _ = a * w := by group
    exact (QuotientGroup.eq_one_iff a).mpr (mem_centralizer_layer_of_central_p hL ha hc)
  set Lb : Subgroup (Y ⧸ CE) := L.map π with hLb
  have hpLb : p ∣ Nat.card Lb := by
    have hker : (π.subgroupMap L).ker = Subgroup.center L := by
      ext ⟨a, ha⟩
      rw [MonoidHom.mem_ker, Subgroup.mem_center_iff]
      constructor
      · intro h1
        have h2 : a ∈ CE := (QuotientGroup.eq_one_iff a).mp (congrArg Subtype.val h1)
        intro g
        exact Subtype.ext (by
          have := Subgroup.mem_centralizer_iff.mp h2 (g : Y) (hLE g.2)
          simpa using this)
      · intro h1
        apply Subtype.ext
        exact (QuotientGroup.eq_one_iff a).mpr
          (mem_centralizer_layer_of_central_p hL ha fun w hw =>
            congrArg Subtype.val (h1 ⟨w, hw⟩))
    have e1 := (QuotientGroup.quotientKerEquivOfSurjective (π.subgroupMap L)
      (π.subgroupMap_surjective L)).toEquiv
    have e2 := (QuotientGroup.quotientMulEquivOfEq hker).toEquiv
    have := Nat.card_congr (e2.symm.trans e1)
    rw [← this]
    exact hLp
  have hLbn : ∀ y ∈ Lb, π f * y * (π f)⁻¹ ∈ Lb := by
    rintro _ ⟨x, hx, rfl⟩
    refine ⟨f * x * f⁻¹, ?_, by simp only [map_mul, map_inv]⟩
    have : f * x * f⁻¹ ∈ conjSub f L := conj_mem_conjSub hx
    rwa [hfL] at this
  have hLbn' : ∀ n : ℕ, ∀ y ∈ Lb, (π f) ^ n * y * ((π f) ^ n)⁻¹ ∈ Lb := by
    intro n
    induction n with
    | zero => intro y hy; simpa using hy
    | succ n ih =>
      intro y hy
      have := hLbn _ (ih y hy)
      rwa [show π f * ((π f) ^ n * y * ((π f) ^ n)⁻¹) * (π f)⁻¹ =
        (π f) ^ (n + 1) * y * ((π f) ^ (n + 1))⁻¹ by group] at this
  have hpf : (π f) ^ p = 1 := by rw [← map_pow, hf, map_one]
  have hQ : IsPGroup p (Subgroup.zpowers (π f)) := isPGroup_zpowers_of_pow_eq_one hp hpf
  have hQK : ∀ q ∈ Subgroup.zpowers (π f), ∀ k ∈ Lb, q * k * q⁻¹ ∈ Lb := by
    intro q hq k hk
    rw [← mem_powers_iff_mem_zpowers] at hq
    obtain ⟨n, rfl⟩ := hq
    exact hLbn' n k hk
  obtain ⟨xb, hxbm, hxord⟩ :=
    CFSG.HardMathSupport.Timmesfeld.Proving.exists_orderOf_eq_prime_mem_inf_centralizer hp hQ hQK
      hpLb
  have hxbL : xb ∈ Lb := hxbm.1
  have hxbC : xb ∈ Subgroup.centralizer ({π f} : Set (Y ⧸ CE)) := by
    refine Subgroup.mem_centralizer_iff.mpr fun h hh => ?_
    rw [Set.mem_singleton_iff] at hh
    subst hh
    exact Subgroup.mem_centralizer_iff.mp hxbm.2 _ (Subgroup.mem_zpowers _)
  obtain ⟨x, hx, hxπ⟩ := hxbL
  have hdb : π d ∈ GLAPPrimeCoreOf p (Subgroup.centralizer ({π f} : Set (Y ⧸ CE))) := by
    have hpg : IsPGroup p (Subgroup.zpowers f) := isPGroup_zpowers_of_pow_eq_one hp hf
    have h1 := hH1 π hπ hp hpg
    rw [MonoidHom.map_zpowers, Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure,
      Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure] at h1
    exact h1 ⟨d, hd, rfl⟩
  have hcmem : xb⁻¹ * (π d * xb * (π d)⁻¹) ∈
      GLAPPrimeCoreOf p (Subgroup.centralizer ({π f} : Set (Y ⧸ CE))) := by
    have h1 := conj_mem_gLAPPrimeCoreOf_of_mem_centralizer (p := p) (inv_mem hxbC) hdb
    have : xb⁻¹ * (π d * xb * (π d)⁻¹) = (xb⁻¹ * π d * xb⁻¹⁻¹) * (π d)⁻¹ := by group
    rw [this]
    exact mul_mem h1 (inv_mem hdb)
  have hcodd := CFSG.HardMathSupport.Timmesfeld.Proving.orderOf_coprime_of_mem_GLAPPrimeCoreOf
    hp hcmem
  have hy : d * x * d⁻¹ ∈ conjSub d L := conj_mem_conjSub hx
  have hyb : π d * xb * (π d)⁻¹ = π (d * x * d⁻¹) := by
    rw [← hxπ]
    simp only [map_mul, map_inv]
  have hxy : Commute (π x) (π (d * x * d⁻¹)) := by
    have := congrArg π (hcomm x hx _ hy)
    rwa [map_mul, map_mul] at this
  set n := orderOf (xb⁻¹ * (π d * xb * (π d)⁻¹)) with hn
  have hcn : (xb⁻¹ * (π d * xb * (π d)⁻¹)) ^ n = 1 := pow_orderOf_eq_one _
  have hcomm' : Commute xb⁻¹ (π (d * x * d⁻¹)) := by
    rw [← hxπ]
    exact hxy.inv_left
  have hkey : (xb⁻¹ * (π d * xb * (π d)⁻¹)) ^ n = xb⁻¹ ^ n * (π (d * x * d⁻¹)) ^ n := by
    rw [hyb]
    exact hcomm'.mul_pow n
  rw [hkey, inv_pow, inv_mul_eq_one] at hcn
  have h1 : π (x ^ n) = π ((d * x * d⁻¹) ^ n) := by
    rw [map_pow, map_pow, hxπ]
    exact hcn
  have h2 := hinter (x ^ n) (pow_mem hx n) ((d * x * d⁻¹) ^ n) (pow_mem hy n) h1
  rw [map_pow, hxπ] at h2
  have h3 : orderOf xb ∣ n := orderOf_dvd_of_pow_eq_one h2
  rw [hxord] at h3
  exact (Nat.Prime.coprime_iff_not_dvd hp).mp hcodd.symm h3

end CFSG.HardMathSupport.Timmesfeld.Balance
