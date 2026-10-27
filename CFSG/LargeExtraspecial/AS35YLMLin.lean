module

public import CFSG.LargeExtraspecial.AS35YLSCen
public import CFSG.LieType.SteinbergBRAltFiveGL3TwoRank

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial

open Subgroup Module CFSG.Blueprint CFSG.RankThree.OrthogonalInvolutions
open CFSG.QuasithinUnique.Setup.Family (GL32 aut_GL32_cases glGraphAut_ne_conj center_GL32)

namespace AS35YL

theorem mat3_orders_YL : ∀ a b c d e f g h i : ZMod 2,
    (!![a, b, c; d, e, f; g, h, i] : Matrix (Fin 3) (Fin 3) (ZMod 2)).det = 1 →
    (!![a, b, c; d, e, f; g, h, i] : Matrix (Fin 3) (Fin 3) (ZMod 2)) ^ 4 = 1 ∨
      (!![a, b, c; d, e, f; g, h, i] : Matrix (Fin 3) (Fin 3) (ZMod 2)) ^ 3 = 1 ∨
      (!![a, b, c; d, e, f; g, h, i] : Matrix (Fin 3) (Fin 3) (ZMod 2)) ^ 7 = 1 := by
  decide

theorem GL32_orders_YL (g : GL32) : g ^ 4 = 1 ∨ g ^ 3 = 1 ∨ g ^ 7 = 1 := by
  have hdet : (g : Matrix (Fin 3) (Fin 3) (ZMod 2)).det = 1 := by
    have h1 : Matrix.GeneralLinearGroup.det g = 1 := Subsingleton.elim _ _
    have h2 := congrArg (fun u : (ZMod 2)ˣ => (u : ZMod 2)) h1
    simpa using h2
  have h := mat3_orders_YL ((g : Matrix (Fin 3) (Fin 3) (ZMod 2)) 0 0)
    ((g : Matrix (Fin 3) (Fin 3) (ZMod 2)) 0 1) ((g : Matrix (Fin 3) (Fin 3) (ZMod 2)) 0 2)
    ((g : Matrix (Fin 3) (Fin 3) (ZMod 2)) 1 0) ((g : Matrix (Fin 3) (Fin 3) (ZMod 2)) 1 1)
    ((g : Matrix (Fin 3) (Fin 3) (ZMod 2)) 1 2) ((g : Matrix (Fin 3) (Fin 3) (ZMod 2)) 2 0)
    ((g : Matrix (Fin 3) (Fin 3) (ZMod 2)) 2 1) ((g : Matrix (Fin 3) (Fin 3) (ZMod 2)) 2 2)
  rw [← Matrix.eta_fin_three (g : Matrix (Fin 3) (Fin 3) (ZMod 2))] at h
  rcases h hdet with h | h | h
  · left; apply Units.ext; rw [Units.val_pow_eq_pow_val, h]; rfl
  · right; left; apply Units.ext; rw [Units.val_pow_eq_pow_val, h]; rfl
  · right; right; apply Units.ext; rw [Units.val_pow_eq_pow_val, h]; rfl

theorem eq_one_of_pow_three_pow_YL {M : Type*} [Monoid M] {y : M} {k m : ℕ}
    (hk : y ^ (3 ^ k) = 1) (hm : y ^ m = 1) (hcop : Nat.Coprime m 3) : y = 1 := by
  have h1 := orderOf_dvd_of_pow_eq_one hk
  have h2 := orderOf_dvd_of_pow_eq_one hm
  have h3 : orderOf y ∣ Nat.gcd m (3 ^ k) := Nat.dvd_gcd h2 h1
  rw [Nat.Coprime.gcd_eq_one (Nat.Coprime.pow_right k hcop), Nat.dvd_one] at h3
  exact orderOf_eq_one_iff.mp h3

theorem eq_one_of_commute_GL32_YL {s t : GL32} {k : ℕ} (hs : s ^ (3 ^ k) = 1) (htt : t * t = 1)
    (ht1 : t ≠ 1) (hst : s * t = t * s) : s = 1 := by
  have hc : Commute s t := hst
  have ht2 : t ^ 2 = 1 := by rw [sq, htt]
  have ht_odd : ∀ n : ℕ, t ^ (2 * n + 1) = t := fun n => by
    rw [pow_succ, pow_mul, ht2, one_pow, one_mul]
  have ht3 : t ^ 3 = t := ht_odd 1
  have ht4 : t ^ 4 = 1 := by
    rw [show t ^ 4 = (t ^ 2) ^ 2 by rw [← pow_mul], ht2, one_pow]
  have ht7 : t ^ 7 = t := ht_odd 3
  rcases GL32_orders_YL (s * t) with h | h | h
  · rw [hc.mul_pow, ht4, mul_one] at h
    exact eq_one_of_pow_three_pow_YL hs h (by norm_num)
  · exfalso
    rw [hc.mul_pow, ht3] at h
    have hts : t = (s ^ 3)⁻¹ := eq_inv_of_mul_eq_one_right h
    have htk : t ^ (3 ^ k) = 1 := by
      rw [hts, inv_pow, ← pow_mul, mul_comm, pow_mul, hs, one_pow, inv_one]
    exact ht1 (eq_one_of_pow_three_pow_YL htk ht2 (by norm_num))
  · exfalso
    rw [hc.mul_pow, ht7] at h
    have hts : t = (s ^ 7)⁻¹ := eq_inv_of_mul_eq_one_right h
    have htk : t ^ (3 ^ k) = 1 := by
      rw [hts, inv_pow, ← pow_mul, mul_comm, pow_mul, hs, one_pow, inv_one]
    exact ht1 (eq_one_of_pow_three_pow_YL htk ht2 (by norm_num))

open CFSG.LieType.SteinbergBR.AutGL32 (tau tau_mul_conj tau_mul_tau) in
theorem aut_eq_one_of_GL32_YL {L : Type} [Group L] (E : L ≃* GL32) (α : MulAut L) {k : ℕ}
    (hk : α ^ (3 ^ k) = 1) {t : L} (htt : t * t = 1) (ht1 : t ≠ 1) (hαt : α t = t) : α = 1 := by
  set β : MulAut GL32 := MulAut.congr E α with hβ
  have hβk : β ^ (3 ^ k) = 1 := by rw [hβ, ← map_pow, hk, map_one]
  have hβt : β (E t) = E t := by
    rw [hβ, MulAut.congr_apply]
    simp [hαt]
  have hβ1 : β = 1 := by
    rcases aut_GL32_cases β with ⟨s, hs⟩ | ⟨s, hs⟩
    · have hsk : s ^ (3 ^ k) = 1 := by
        refine CFSG.LieType.SteinbergBR.AutGL32.conj_injective ?_
        rw [map_pow, ← hs, hβk, map_one]
      have hst : s * E t = E t * s := by
        have h := hβt
        rw [hs, MulAut.conj_apply] at h
        calc s * E t = s * E t * s⁻¹ * s := by group
          _ = E t * s := by rw [h]
      have htt' : E t * E t = 1 := by rw [← map_mul, htt, map_one]
      have ht1' : E t ≠ 1 := fun h => ht1 (E.injective (h.trans (map_one E).symm))
      rw [hs, eq_one_of_commute_GL32_YL hsk htt' ht1' hst, map_one]
    · exfalso
      have hsq : β ^ 2 = MulAut.conj (s * tau s) := by
        rw [pow_two, hs, mul_assoc, ← mul_assoc tau, tau_mul_conj, mul_assoc, tau_mul_tau,
          mul_one, ← map_mul]
      obtain ⟨m, hm⟩ : Even (3 ^ k + 1) := (Odd.pow (by decide : Odd 3)).add_one
      have hβeq : β = MulAut.conj ((s * tau s) ^ m) := by
        calc β = β ^ (3 ^ k) * β := by rw [hβk, one_mul]
          _ = β ^ (3 ^ k + 1) := (pow_succ β (3 ^ k)).symm
          _ = (β ^ 2) ^ m := by rw [hm, ← two_mul, pow_mul]
          _ = MulAut.conj ((s * tau s) ^ m) := by rw [hsq, map_pow]
      have htau : tau = MulAut.conj (s⁻¹ * (s * tau s) ^ m) := by
        rw [map_mul, map_inv, ← hβeq, hs, ← mul_assoc, inv_mul_cancel, one_mul]
      exact glGraphAut_ne_conj _ htau
  have h := congrArg (MulAut.congr E).symm hβ1
  rwa [hβ, MulEquiv.symm_apply_apply, map_one] at h

variable {H : Type} [Group H]

@[expose] def conjAut_YL (L : Subgroup H) (x : H) (hx : ∀ l ∈ L, x * l * x⁻¹ ∈ L)
    (hx' : ∀ l ∈ L, x⁻¹ * l * x ∈ L) : MulAut L where
  toFun l := ⟨x * l * x⁻¹, hx l l.2⟩
  invFun l := ⟨x⁻¹ * l * x, hx' l l.2⟩
  left_inv l := Subtype.ext (by simp [mul_assoc])
  right_inv l := Subtype.ext (by simp [mul_assoc])
  map_mul' a b := Subtype.ext (by simp [mul_assoc])

theorem conjAut_YL_apply (L : Subgroup H) (x : H) (hx : ∀ l ∈ L, x * l * x⁻¹ ∈ L)
    (hx' : ∀ l ∈ L, x⁻¹ * l * x ∈ L) (l : L) :
    ((conjAut_YL L x hx hx' l : L) : H) = x * l * x⁻¹ := rfl

theorem conjAut_YL_pow (L : Subgroup H) (x : H) (hx : ∀ l ∈ L, x * l * x⁻¹ ∈ L)
    (hx' : ∀ l ∈ L, x⁻¹ * l * x ∈ L) (n : ℕ) (l : L) :
    (((conjAut_YL L x hx hx' ^ n) l : L) : H) = x ^ n * l * (x ^ n)⁻¹ := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ', MulAut.mul_apply, conjAut_YL_apply, ih, pow_succ']
    group

theorem conjAut_YL_pow_eq_one (L : Subgroup H) (x : H) (hx : ∀ l ∈ L, x * l * x⁻¹ ∈ L)
    (hx' : ∀ l ∈ L, x⁻¹ * l * x ∈ L) {n : ℕ} (h : x ^ n = 1) :
    conjAut_YL L x hx hx' ^ n = 1 := by
  refine MulEquiv.ext fun l => Subtype.ext ?_
  rw [conjAut_YL_pow, h, one_mul, inv_one, mul_one]
  rfl

theorem conjAut_YL_fix (L : Subgroup H) (x : H) (hx : ∀ l ∈ L, x * l * x⁻¹ ∈ L)
    (hx' : ∀ l ∈ L, x⁻¹ * l * x ∈ L) {l : L} (h : x * l = l * x) :
    conjAut_YL L x hx hx' l = l :=
  Subtype.ext (by rw [conjAut_YL_apply, h, mul_inv_cancel_right])

theorem commute_of_conjAut_YL_eq_one (L : Subgroup H) (x : H) (hx : ∀ l ∈ L, x * l * x⁻¹ ∈ L)
    (hx' : ∀ l ∈ L, x⁻¹ * l * x ∈ L) (h : conjAut_YL L x hx hx' = 1) {l : H} (hl : l ∈ L) :
    x * l = l * x := by
  have h1 : x * l * x⁻¹ = l := by
    have := congrArg (fun φ : MulAut L => ((φ ⟨l, hl⟩ : L) : H)) h
    simpa [conjAut_YL_apply] using this
  calc x * l = x * l * x⁻¹ * x := by group
    _ = l * x := by rw [h1]

end AS35YL

namespace S14

theorem asc512InspPSL3_of (h5127 : Asc512FiveTwelveSevenStmt) :
    Asc512InspFor fun (X : Type) [Group X] (D : Set X) =>
      InspNondeg X D ∧ LieModel X .PSL 3 2 1 := by
  intro G _ _ S hS hst h
  exfalso
  obtain ⟨hnd, hL⟩ := h
  have hc := Setting.center_LbarAsc_eq_bot_YL hS hst hnd
  have : Nontrivial (S.LbarAsc ⧸ center S.LbarAsc) := AS35YL.nontrivial_of_inspNondeg_YL hnd
  obtain ⟨e⟩ := CFSG.LieType.SteinbergBR.AltFiveGL3.nonempty_equiv_GL32 hL
  set E : S.LbarAsc ≃* GL32 := (AS35YL.quotEquiv_YL S.LbarAsc hc).symm.trans e with hE
  obtain ⟨t₀, ht₀⟩ := Setting.DbarAsc_nonempty_YL (S := S)
  obtain ⟨t, ht, htM, rfl⟩ := ht₀
  obtain ⟨g, rfl⟩ := isConj_iff.mp (S.isConj_of_mem_ESet ht.1)
  obtain ⟨x, hxM, ⟨k, hxk⟩, hxt, hfpf⟩ := h5127 G S hS g ht htM
  have hx3 : x ^ (3 ^ k) = 1 := by rw [← hxk]; exact pow_orderOf_eq_one x
  have hxL : ∀ l ∈ S.LbarAsc, x * l * x⁻¹ ∈ S.LbarAsc := fun l hl => hst.normal x hxM l hl
  have hxL' : ∀ l ∈ S.LbarAsc, x⁻¹ * l * x ∈ S.LbarAsc := fun l hl => by
    have := hst.normal x⁻¹ (S.Mbar.inv_mem hxM) l hl
    rwa [inv_inv] at this
  have hαk := AS35YL.conjAut_YL_pow_eq_one S.LbarAsc x hxL hxL' hx3
  have htD : S.ρ ⟨_, htM⟩ ∈ S.DbarAsc := ⟨_, ht, htM, rfl⟩
  have hαt := AS35YL.conjAut_YL_fix S.LbarAsc x hxL hxL' (l := ⟨S.ρ ⟨_, htM⟩, subset_closure htD⟩)
    hxt
  have hTT : (⟨S.ρ ⟨_, htM⟩, subset_closure htD⟩ : S.LbarAsc) * ⟨S.ρ ⟨_, htM⟩, subset_closure htD⟩
      = 1 := Subtype.ext (Setting.mul_self_of_mem_DbarAsc_YL htD)
  have hT1 : (⟨S.ρ ⟨_, htM⟩, subset_closure htD⟩ : S.LbarAsc) ≠ 1 := fun h1 =>
    (Setting.isTypeA_of_mem_DbarAsc_YL hS htD).2.1 (by
      have := congrArg (fun y : S.LbarAsc => ((y : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt)) h1
      simpa using this)
  have hα1 := AS35YL.aut_eq_one_of_GL32_YL E _ hαk hTT hT1 hαt
  have hcomm : ∀ l ∈ S.LbarAsc, ((x : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) *
      ((l : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) = ((l : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) * x := fun l hl =>
    congrArg Subtype.val (AS35YL.commute_of_conjAut_YL_eq_one S.LbarAsc x hxL hxL' hα1 hl)
  exact Setting.not_inspNondeg_of_fpf_YL hS hst
    (fun v => TauCeti.QuadraticMap.map_app_of_mem_orthogonalGroup x.2 v) hcomm htD hfpf hnd

@[expose] def Asc512PSL4WidthThreeStmt : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (S : Setting G), S.SixHyp → S.Asc512Standing →
    InspNondeg _ S.EhatAsc → LieModel (S.LbarAsc ⧸ center S.LbarAsc) .PSL 4 2 1 →
      S.LbarIrred_YL → S.width ≠ 3

end S14

end CFSG.LargeExtraspecial
