module

public import CFSG.GH74.GLS.IVK.Lifted.Strong
public import CFSG.GH74.GLS.IVK.Lifted.PNoncyclic
public import CFSG.GH74.GLS.IVK.Lifted.Outer14
public import CFSG.GH74.GLS.IVK.Lifted.SLSign
public import CFSG.GH74.GLS.Stage1.Thm3.Sec4.Struct5

public section

namespace CFSG.GH74.GLS.IVK.Lifted

open Subgroup Matrix CFSG CFSG.GH74.GLS CFSG.GH74.GLS.IVK CFSG.GorensteinWalter CFSG.ABGLocalTools
  CFSG.ABGDGroups CFSG.Assembly.LowTwoRank CFSG.GH74.GLS.Stage1.Thm2.Recip
  CFSG.GH74.GLS.Stage1.Thm3.Sec4 CFSG.GH74.GLS.Stage1.Thm3.Sec5 CFSG.GH74.GLS.Stage1.Thm3.Sec6
  CFSG.GH74.GLS.Stage1.Thm6 CFSG.DisconnectedInvolutionGraph CFSG.DisconnectedInvolutionGraph.Helpers
open scoped commutatorElement

section Basic

variable {G : Type} [Group G] [Finite G] {z : G} {S K₁ K₂ : Subgroup G}

theorem std4_normalizer_swap (h : Std4 G z S K₁ K₂) {c : G} (hc : c ∈ centralizer ({z} : Set G)) :
    c ∈ normalizer (K₁ : Set G) ↔ c ∈ normalizer (K₂ : Set G) := by
  rcases std4_perm_cmap h hc with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact ⟨fun _ => (cmap_eq_iff_normalizer K₂ c).1 h2, fun _ => (cmap_eq_iff_normalizer K₁ c).1 h1⟩
  · constructor
    · intro hn
      exfalso
      have := (cmap_eq_iff_normalizer K₁ c).2 hn
      rw [h1] at this
      exact h.ne this.symm
    · intro hn
      exfalso
      have := (cmap_eq_iff_normalizer K₂ c).2 hn
      rw [h2] at this
      exact h.ne this

theorem normalizer_AB (h : Std4 G z S K₁ K₂) {A B : Subgroup G}
    (hAB : A = K₁ ∧ B = K₂ ∨ A = K₂ ∧ B = K₁) {c : G} (hc : c ∈ centralizer ({z} : Set G)) :
    c ∈ normalizer (A : Set G) ↔ c ∈ normalizer (B : Set G) := by
  rcases hAB with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact std4_normalizer_swap h hc
  · exact (std4_normalizer_swap h hc).symm

omit [Finite G] in
theorem cSec_conj_mem {K : Subgroup G} {g x : G} (hg : g ∈ normalizer (K : Set G)) (hx : x ∈ cSec K) :
    g * x * g⁻¹ ∈ cSec K := by
  obtain ⟨hxN, -, -⟩ := id hx
  have hgx : g * x * g⁻¹ ∈ normalizer (K : Set G) := mul_mem (mul_mem hg hxN) (inv_mem hg)
  rw [← phi_eq_one_iff K hgx]
  have h1 : phi K (g * x * g⁻¹) hgx = phi K g hg * phi K x hxN * phi K g⁻¹ (inv_mem hg) := by
    rw [phi_mul K (mul_mem hg hxN) (inv_mem hg), phi_mul K hg hxN]
  have hx1 : phi K x hxN = 1 := (phi_eq_one_iff K hxN).2 hx
  rw [h1, hx1, mul_one, ← phi_mul K hg (inv_mem hg)]
  have : phi K (g * g⁻¹) (mul_mem hg (inv_mem hg)) = phi K 1 (one_mem _) :=
    phi_congr K (mul_inv_cancel g) _ _
  rw [this]
  exact phi_one_aux K _

omit [Finite G] in
theorem normalizes_Q {K : Subgroup G} {g : G} (hgS : g ∈ S) (hg : g ∈ normalizer (K : Set G)) :
    g ∈ normalizer ((Qof S K : Subgroup G) : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro q
  constructor
  · intro hq
    exact ⟨S.mul_mem (S.mul_mem hgS hq.1) (S.inv_mem hgS), cSec_conj_mem hg hq.2⟩
  · intro hq
    have h1 : g⁻¹ * (g * q * g⁻¹) * g⁻¹⁻¹ ∈ Qof S K :=
      ⟨S.mul_mem (S.mul_mem (S.inv_mem hgS) hq.1) (by simpa using hgS),
        cSec_conj_mem (inv_mem hg) hq.2⟩
    simpa [mul_assoc] using h1

omit [Finite G] in
theorem Qof_le_S {K : Subgroup G} : Qof S K ≤ S := inf_le_left

theorem Q_inf_Q5 (hII : II4_4_4_center) (h : Cfg5 G z S K₁ K₂) :
    Qof S K₁ ⊓ Qof S K₂ = zpowers z := by
  have hM := m4_of_std hII h.std
  apply le_antisymm
  · rintro c ⟨⟨hcS, hc1⟩, ⟨-, hc2⟩⟩
    obtain ⟨-, -, hc1'⟩ := hc1
    obtain ⟨-, -, hc2'⟩ := hc2
    have hcC : c ∈ centralizer ({z} : Set G) := hM.S_syl.1 hcS
    have h1 : ∀ x ∈ K₁, ⁅x, c⁆ ∈ pPrimeCoreOf 2 (K₁ ⊔ K₂) := fun x hx =>
      hM.O_le_OK (Or.inl rfl) (hc1' x hx)
    have h2 : ∀ y ∈ K₂, ⁅y, c⁆ ∈ pPrimeCoreOf 2 (K₁ ⊔ K₂) := fun y hy =>
      hM.O_le_OK (Or.inr rfl) (hc2' y hy)
    have hcs := hM.secCent_of_gen hcC h1 h2
    have hcQ : c ∈ Qz S z := by
      rw [Qz_eq h.std]
      exact ⟨hcS, hcs⟩
    rw [h.hQ] at hcQ
    exact hcQ
  · exact zpowers_le.2 ⟨z_mem_Qof hM (Or.inl rfl), z_mem_Qof hM (Or.inr rfl)⟩

theorem Q_inf_Q5' (hII : II4_4_4_center) (h : Cfg5 G z S K₁ K₂) {A B : Subgroup G}
    (hAB : A = K₁ ∧ B = K₂ ∨ A = K₂ ∧ B = K₁) : Qof S B ⊓ Qof S A = zpowers z := by
  rcases hAB with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · rw [inf_comm]
    exact Q_inf_Q5 hII h
  · exact Q_inf_Q5 hII h

end Basic

section LiftInner

variable {G : Type} [Group G] [Finite G]

theorem lift_inner_gen {S K : Subgroup G} (hS2 : IsPGroup 2 ↥S)
    (hSyl : ∃ P : Sylow 2 ↥K, (P : Subgroup ↥K).map K.subtype = S ⊓ K)
    (hZ : ∀ x ∈ Subgroup.center (Hat K), x * x = 1) {s : G} (hs : s ∈ S)
    (hsN : s ∈ normalizer (K : Set G)) (hin : InducesInner s K) :
    ∃ k₀ ∈ S ⊓ K, s * k₀⁻¹ ∈ S ⊓ cSec K := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨P, hP⟩ := hSyl
  let Pbar : Sylow 2 (Hat K) := P.mapSurjective (hatMk_surjective K)
  have hPbar : (Pbar : Subgroup (Hat K)) = (P : Subgroup ↥K).map (hatMk K) :=
    Sylow.coe_mapSurjective (hatMk_surjective K) P
  have hPsub : (S ⊓ K).subgroupOf K = (P : Subgroup ↥K) := by
    rw [← hP]
    exact Subgroup.comap_map_eq_self_of_injective K.subtype_injective _
  have hPimg : (Pbar : Subgroup (Hat K)) = hatImg K (S ⊓ K) := by
    rw [hPbar, hatImg_eq_map, hPsub]
  have phi_one : ∀ hh : (1 : G) ∈ normalizer (K : Set G), phi K (1 : G) hh = 1 := by
    intro hh
    have h1K : hatMk K (⟨1, one_mem K⟩ : ↥K) = 1 := by
      have : (⟨1, one_mem K⟩ : ↥K) = 1 := rfl
      rw [this, map_one]
    rw [show phi K (1 : G) hh = phi K (1 : G) (le_normalizer (one_mem K)) from rfl,
      phi_of_mem K (one_mem K), h1K, map_one]
  obtain ⟨k, hk, hkc⟩ := hin
  have hsk : s * k⁻¹ ∈ normalizer (K : Set G) := hkc.1
  have h1 : phi K (s * k⁻¹) hsk = 1 := (phi_eq_one_iff K hsk).mpr hkc
  have hφ : phi K s hsN = MulAut.conj (hatMk K ⟨k, hk⟩) := by
    have h2 : phi K s hsN = phi K (s * k⁻¹) hsk * phi K k (le_normalizer hk) := by
      rw [← phi_mul K hsk (le_normalizer hk)]
      exact phi_congr K (by group) hsN _
    rw [h2, h1, one_mul, phi_of_mem K hk]
  set kb : Hat K := hatMk K ⟨k, hk⟩ with hkb
  have hsinv : s⁻¹ ∈ S := S.inv_mem hs
  have hsinvN : s⁻¹ ∈ normalizer (K : Set G) := inv_mem hsN
  have hφinv : phi K s⁻¹ hsinvN = (phi K s hsN)⁻¹ := by
    have h3 : phi K s hsN * phi K s⁻¹ hsinvN = 1 := by
      rw [← phi_mul K hsN hsinvN]
      have : phi K (s * s⁻¹) (mul_mem hsN hsinvN) = phi K 1 (one_mem _) :=
        phi_congr K (by group) _ _
      rw [this]
      exact phi_one _
    exact eq_inv_of_mul_eq_one_right h3
  have hnorm : kb ∈ normalizer ((Pbar : Subgroup (Hat K)) : Set (Hat K)) := by
    rw [mem_normalizer_iff]
    intro x
    rw [hPimg]
    have hSs : ∀ a ∈ S ⊓ K, s * a * s⁻¹ ∈ S ⊓ K := fun a ha =>
      ⟨S.mul_mem (S.mul_mem hs ha.1) hsinv, (mem_normalizer_iff.mp hsN a).mp ha.2⟩
    have hSs' : ∀ a ∈ S ⊓ K, s⁻¹ * a * s⁻¹⁻¹ ∈ S ⊓ K := fun a ha =>
      ⟨S.mul_mem (S.mul_mem hsinv ha.1) (by simpa using hs),
        (mem_normalizer_iff.mp hsinvN a).mp ha.2⟩
    constructor
    · intro hx
      have := phi_mem_hatImg hsN hSs hx
      rwa [hφ, MulAut.conj_apply] at this
    · intro hx
      have h4 : phi K s hsN x ∈ hatImg K (S ⊓ K) := by
        rw [hφ, MulAut.conj_apply]
        exact hx
      have h5 := phi_mem_hatImg hsinvN hSs' h4
      rwa [hφinv, MulAut.inv_apply_self] at h5
  obtain ⟨m, hm⟩ := (IsPGroup.iff_orderOf.1 hS2) ⟨s, hs⟩
  have hs2 : s ^ (2 ^ m) = 1 := by
    have h6 := pow_orderOf_eq_one (⟨s, hs⟩ : ↥S)
    rw [hm] at h6
    simpa using congrArg Subtype.val h6
  have hφpow : ∀ n : ℕ, (phi K s hsN) ^ n = phi K (s ^ n) (pow_mem hsN n) := by
    intro n
    induction n with
    | zero =>
      rw [pow_zero]
      have : phi K (s ^ 0) (pow_mem hsN 0) = phi K (1 : G) (one_mem _) :=
        phi_congr K (pow_zero s) _ _
      rw [this, phi_one]
    | succ n ih =>
      rw [pow_succ, ih, ← phi_mul K (pow_mem hsN n) hsN]
      exact phi_congr K (by rw [pow_succ]) _ _
  have hkb2 : kb ^ (2 ^ (m + 1)) = 1 := by
    have h7 : (MulAut.conj kb) ^ (2 ^ m) = 1 := by
      rw [← hφ, hφpow]
      have : phi K (s ^ 2 ^ m) (pow_mem hsN _) = phi K 1 (one_mem _) := phi_congr K hs2 _ _
      rw [this, phi_one]
    have h8 : kb ^ (2 ^ m) ∈ Subgroup.center (Hat K) := by
      rw [Subgroup.mem_center_iff]
      intro x
      have h9 : MulAut.conj (kb ^ 2 ^ m) x = x := by
        rw [map_pow, h7]
        rfl
      rw [MulAut.conj_apply] at h9
      calc x * kb ^ 2 ^ m = (kb ^ 2 ^ m * x * (kb ^ 2 ^ m)⁻¹) * kb ^ 2 ^ m := by rw [h9]
        _ = kb ^ 2 ^ m * x := by group
    have h10 := hZ _ h8
    rw [pow_succ, pow_mul, sq]
    exact h10
  have hmem : kb ∈ (Pbar : Subgroup (Hat K)) :=
    CFSG.Walter.J1.JankoHyp.mem_sylow_of_mem_normalizer Pbar hnorm hkb2
  rw [hPbar] at hmem
  obtain ⟨k₀, hk₀P, hk₀⟩ := Subgroup.mem_map.1 hmem
  have hk₀S : (k₀ : G) ∈ S ⊓ K := by
    rw [← hP]
    exact ⟨k₀, hk₀P, rfl⟩
  refine ⟨(k₀ : G), hk₀S, ?_⟩
  have hk0N : (k₀ : G) ∈ normalizer (K : Set G) := le_normalizer k₀.2
  have hsk0 : s * (k₀ : G)⁻¹ ∈ normalizer (K : Set G) := mul_mem hsN (inv_mem hk0N)
  refine ⟨S.mul_mem hs (S.inv_mem hk₀S.1), ?_⟩
  refine (phi_eq_one_iff K hsk0).mp ?_
  rw [phi_mul K hsN (inv_mem hk0N), hφ]
  have h11 : phi K (k₀ : G)⁻¹ (inv_mem hk0N) = MulAut.conj (hatMk K ⟨(k₀ : G)⁻¹, inv_mem k₀.2⟩) :=
    phi_of_mem K (inv_mem k₀.2)
  rw [h11]
  have h12 : (hatMk K ⟨(k₀ : G)⁻¹, inv_mem k₀.2⟩) = (hatMk K k₀)⁻¹ := by
    rw [← map_inv]
    rfl
  rw [h12, hk₀]
  show MulAut.conj kb * MulAut.conj kb⁻¹ = 1
  rw [← map_mul, mul_inv_cancel, map_one]

end LiftInner

section QB

variable {G : Type} [Group G] [Finite G] {z : G} {S K₁ K₂ : Subgroup G}

theorem QB_le_normalizer (hII : II4_4_4_center) (hC : Cfg5 G z S K₁ K₂) {A B : Subgroup G}
    (hAB : A = K₁ ∧ B = K₂ ∨ A = K₂ ∧ B = K₁) : Qof S B ≤ normalizer (A : Set G) := by
  have hM := m4_of_std hII hC.std
  intro x hx
  obtain ⟨hn, -, -⟩ := id hx.2
  exact (normalizer_AB hC.std hAB (hM.S_syl.1 hx.1)).2 hn

theorem QB_dihedral52
    (hII : II4_4_4_center) (hC : Cfg5 G z S K₁ K₂) {A B : Subgroup G}
    (hAB : A = K₁ ∧ B = K₂ ∨ A = K₂ ∧ B = K₁) (hne : Qof S B ≠ Pof S A) :
    ∃ (Pbar : Sylow 2 (Hat A)) (M : Subgroup (MulAut (Hat A))), IsPGroup 2 ↥M ∧
      (Pbar : Subgroup (Hat A)).map (MulAut.conj : Hat A →* MulAut (Hat A)) ≤ M ∧
      M ≠ (Pbar : Subgroup (Hat A)).map (MulAut.conj : Hat A →* MulAut (Hat A)) ∧
      (∃ n, IsDihedralTwoGroup ↥M n) ∧
      ∀ x (hx : x ∈ normalizer (A : Set G)), x ∈ Qof S B → phi A x hx ∈ M := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hM := m4_of_std hII hC.std
  have hAc : A = K₁ ∨ A = K₂ := by
    rcases hAB with ⟨h, _⟩ | ⟨h, _⟩
    · exact Or.inl h
    · exact Or.inr h
  have hBc : B = K₁ ∨ B = K₂ := by
    rcases hAB with ⟨_, h⟩ | ⟨_, h⟩
    · exact Or.inr h
    · exact Or.inl h
  have hmQ : pRank 2 ↥(Qof S B) = 1 := by
    rcases hAB with ⟨_, rfl⟩ | ⟨_, rfl⟩
    · exact hC.m₂
    · exact hC.m₁
  have hQNA : Qof S B ≤ normalizer (A : Set G) := fun x hx => by
    obtain ⟨hn, -, -⟩ := id hx.2
    exact (normalizer_AB hC.std hAB (hM.S_syl.1 hx.1)).2 hn
  obtain ⟨Pbar, hPbar⟩ := exists_sylow_hatImg (std4_exists_sylow_P hC.std hAc)
  let ρ : ↥(Qof S B) →* MulAut (Hat A) := (phiHom A).comp (Subgroup.inclusion hQNA)
  have hρ : ∀ x : ↥(Qof S B), ρ x = phi A (x : G) (hQNA x.2) := fun x => rfl
  have hQQ := Q_inf_Q5' hII hC hAB
  have hzP : z ∈ Pof S A := ⟨hM.z_mem_S, hM.z_mem_comp hAc⟩
  have hPQ : Pof S A ≤ Qof S B := Pof_le_Qof hM hAB
  have hker : ρ.ker = (zpowers z).subgroupOf (Qof S B) := by
    ext x
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, hρ, phi_eq_one_iff A (hQNA x.2), ← hQQ]
    constructor
    · intro hx
      exact ⟨x.2, ⟨x.2.1, hx⟩⟩
    · intro hx
      exact hx.2.2
  have hSp : IsPGroup 2 ↥S := hC.std.sylow.isPGroup
  have hQp : IsPGroup 2 ↥(Qof S B) := hSp.to_inf_left
  have hMp : IsPGroup 2 ↥ρ.range :=
    hQp.of_surjective ρ.rangeRestrict ρ.rangeRestrict_surjective
  have hDM : (Pbar : Subgroup (Hat A)).map (MulAut.conj : Hat A →* MulAut (Hat A)) ≤ ρ.range := by
    rintro _ ⟨y, hy, rfl⟩
    rw [hPbar] at hy
    obtain ⟨a', ha', rfl⟩ := mem_hatImg.1 hy
    refine ⟨⟨(a' : G), hPQ ha'⟩, ?_⟩
    rw [hρ]
    exact phi_of_mem A a'.2
  have hMD : ρ.range ≠
      (Pbar : Subgroup (Hat A)).map (MulAut.conj : Hat A →* MulAut (Hat A)) := by
    intro hEq
    have hex : ∃ q ∈ Qof S B, q ∉ Pof S A := by
      by_contra hcon
      push Not at hcon
      exact hne (le_antisymm (fun q hq => hcon q hq) hPQ)
    obtain ⟨q, hqQ, hqP⟩ := hex
    have hqM : ρ ⟨q, hqQ⟩ ∈ ρ.range := ⟨_, rfl⟩
    rw [hEq] at hqM
    obtain ⟨y, hy, hyq⟩ := hqM
    rw [hPbar] at hy
    obtain ⟨p, hpP, rfl⟩ := mem_hatImg.1 hy
    have hpN : (p : G) ∈ normalizer (A : Set G) := le_normalizer p.2
    have hqN : q ∈ normalizer (A : Set G) := hQNA hqQ
    have h1 : phi A q hqN = phi A (p : G) hpN := by
      have := hyq
      rw [hρ] at this
      rw [← this, phi_of_mem A p.2]
    have h2 : phi A (q * (p : G)⁻¹) (mul_mem hqN (inv_mem hpN)) = 1 := by
      rw [phi_mul A hqN (inv_mem hpN), phi_inv_aux A hpN (inv_mem hpN), h1, mul_inv_cancel]
    have h3 : q * (p : G)⁻¹ ∈ cSec A := (phi_eq_one_iff A _).1 h2
    have h4 : q * (p : G)⁻¹ ∈ Qof S B ⊓ Qof S A :=
      ⟨(Qof S B).mul_mem hqQ ((Qof S B).inv_mem (hPQ hpP)),
        ⟨S.mul_mem hqQ.1 (S.inv_mem hpP.1), h3⟩⟩
    rw [hQQ] at h4
    apply hqP
    have h5 : q = (q * (p : G)⁻¹) * (p : G) := by group
    rw [h5]
    exact (Pof S A).mul_mem (zpowers_le.2 hzP h4) hpP
  have hnocomm : NoCommutingDistinctInvolutions ↥(Qof S B) := fun u v huv =>
    Subtype.ext (noCommInv_of_pRank hmQ u.1 v.1 u.2 v.2 huv)
  have hnc : ¬ IsCyclic ↥(Qof S B) := by
    intro hcyc
    exact p_noncyclic G z S K₁ K₂ hC.std A (by simpa using hAc) (isCyclic_of_le' hPQ hcyc)
  obtain ⟨n, hn1, ⟨ε⟩⟩ : ∃ n : ℕ, 1 ≤ n ∧ Nonempty (QuaternionGroup (2 ^ n) ≃* ↥(Qof S B)) := by
    rcases rank_one_two_cyclic_or_quaternion hQp hnocomm with hc | h
    · exact absurd hc hnc
    · exact h
  have hzQ : z ∈ Qof S B := z_mem_Qof hM hBc
  have hz2 : orderOf z = 2 := hC.std.orderOf_z
  have : NeZero (2 ^ n) := ⟨by positivity⟩
  obtain ⟨hN, ⟨d⟩⟩ := CFSG.GH74.GLS.Stage1.Thm3.Sec7.QM.quot_equiv ε.symm hzQ hz2
  have eM : ↥ρ.range ≃* DihedralGroup (2 ^ n) :=
    (QuotientGroup.quotientKerEquivRange ρ).symm.trans
      ((QuotientGroup.quotientMulEquivOfEq hker).trans d)
  refine ⟨Pbar, ρ.range, hMp, hDM, hMD, ⟨n + 1, by omega, 2 ^ n, by rw [pow_succ]; ring, ?_, ⟨eM⟩⟩, ?_⟩
  · calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn1
  · intro x hx hxQ
    exact ⟨⟨x, hxQ⟩, rfl⟩

theorem a7_excluded52
    (h2A7 : II4_2A7) (hII : II4_4_4_center) (hC : Cfg5 G z S K₁ K₂)
    {A B : Subgroup G} (hAB : A = K₁ ∧ B = K₂ ∨ A = K₂ ∧ B = K₁) (hne : Qof S B ≠ Pof S A)
    (h7 : IsDoubleCoverOfAlt (Hat A) 7) : False := by
  obtain ⟨Pbar, M, hMp, hDM, hMD, hdih, -⟩ := QB_dihedral52 hII hC hAB hne
  rcases a7_cases h2A7 h7 M hMp Pbar hDM with h | ⟨T, hMT, hTnd, -⟩
  · exact hMD h
  · apply hTnd
    rw [hMT] at hdih
    exact hdih

theorem field_trivial52
    (hII : II4_4_4_center) (hC : Cfg5 G z S K₁ K₂) {A B : Subgroup G}
    (hAB : A = K₁ ∧ B = K₂ ∨ A = K₂ ∧ B = K₁) (hne : Qof S B ≠ Pof S A) {F : Type} [Field F]
    [Finite F] (hodd : Odd (Nat.card F)) (h3 : 3 < Nat.card F)
    (e : Hat A ≃* SpecialLinearGroup (Fin 2) F) :
    ∀ x (hx : x ∈ normalizer (A : Set G)), x ∈ Qof S B →
      (gammaOf hodd h3 (MulAut.congr e (phi A x hx))).right = 1 := by
  obtain ⟨Pbar, M, hMp, hDM, -, hdih, hmem⟩ := QB_dihedral52 hII hC hAB hne
  intro x hx hxQ
  exact sl_dihedral_field hodd h3 e M hMp Pbar hDM hdih _ (hmem x hx hxQ)

end QB

section Leaves

variable {G : Type} [Group G] [Finite G] {z : G} {S K₁ K₂ : Subgroup G}

theorem ivk_1_2j_52_of_II4
    (h44 : II4_44) (h2A7 : II4_2A7) (hII : II4_4_4_center) :
    CFSG.GH74.GLS.Stage1.Thm3.Sec5.IVK_1_2j_52 := by
  intro G _ _ z S K₁ K₂ a hC ha A B hAB hne
  classical
  have hM := m4_of_std hII hC.std
  have hAc : A = K₁ ∨ A = K₂ := by
    rcases hAB with ⟨h, _⟩ | ⟨h, _⟩
    · exact Or.inl h
    · exact Or.inr h
  have hAmem : A ∈ ({K₁, K₂} : Set (Subgroup G)) := by simpa using hAc
  have hOK := std4_hatOK h44 hC.std hAmem
  have hmQA : pRank 2 ↥(Qof S A) = 1 := by
    rcases hAB with ⟨rfl, _⟩ | ⟨rfl, _⟩
    · exact hC.m₁
    · exact hC.m₂
  obtain ⟨haNA, haFA⟩ : InducesFAut a A := by
    rcases hAB with ⟨hA, _⟩ | ⟨hA, _⟩
    · rw [hA]
      exact ha.f₁
    · rw [hA]
      exact ha.f₂
  obtain ⟨haNB, -⟩ : InducesFAut a B := by
    rcases hAB with ⟨_, hB⟩ | ⟨_, hB⟩
    · rw [hB]
      exact ha.f₂
    · rw [hB]
      exact ha.f₁
  rcases sl_or_a7 hOK.sl2 with ⟨F, hFf, hFin, hodd, h3, ⟨e⟩⟩ | h7
  · intro x hx
    obtain ⟨hxX, hxQA⟩ := hx
    have haa : a * a = 1 := mul_self_eq_one_of_orderOf_eq_two ha.inv
    have haNQ : a ∈ normalizer ((Qof S B : Subgroup G) : Set G) := normalizes_Q ha.mem haNB
    rcases CFSG.GH74.GLS.Stage1.Thm3.Sec5.mem_or_mul_inv_mem haNQ (by rw [haa]; exact one_mem _)
      hxX with hxB | hxB
    · have h1 : x ∈ Qof S B ⊓ Qof S A := ⟨hxB, hxQA⟩
      rw [Q_inf_Q5' hII hC hAB] at h1
      exact h1
    · exfalso
      have hqN : x * a⁻¹ ∈ normalizer (A : Set G) := QB_le_normalizer hII hC hAB hxB
      have hxeq : x = (x * a⁻¹) * a := by group
      have hxN : x ∈ normalizer (A : Set G) := by
        rw [hxeq]
        exact mul_mem hqN haNA
      have h1 : phi A x hxN = 1 := (phi_eq_one_iff A hxN).2 hxQA.2
      have h2 : phi A x hxN = phi A (x * a⁻¹) hqN * phi A a haNA := by
        rw [← phi_mul A hqN haNA]
        exact phi_congr A hxeq hxN _
      have hφa : phi A a haNA = (phi A (x * a⁻¹) hqN)⁻¹ := by
        rw [h1] at h2
        exact eq_inv_of_mul_eq_one_right h2.symm
      have hσq := field_trivial52 hII hC hAB hne hodd h3 e (x * a⁻¹) hqN hxB
      have hσa : (gammaOf hodd h3 (MulAut.congr e (phi A a haNA))).right = 1 := by
        have h5 : ∀ γ : PGammaL2 F, γ⁻¹.right = (γ.right)⁻¹ := fun γ =>
          map_inv SemidirectProduct.rightHom γ
        rw [hφa, map_inv, map_inv, h5, hσq, inv_one]
      have hφ1 : phi A a haNA ≠ 1 := by
        intro h1'
        have hac : a ∈ cSec A := (phi_eq_one_iff A haNA).1 h1'
        have : a = z :=
          eq_z_of_mem_Qof hM hAc hmQA hC.std.orderOf_z ⟨ha.mem, hac⟩ ha.inv
        exact ha.ne (this ▸ mem_zpowers z)
      obtain ⟨-, -, -, -, hfc⟩ := haFA
      exact not_fixedCond_of_right_eq_one hodd h3 e (phi A a haNA) hφ1 hσa hfc
  · exact (a7_excluded52 h2A7 hII hC hAB hne h7).elim

theorem ivk_1_9_52_of_II4
    (h44 : II4_44) (h2A7 : II4_2A7) (hII : II4_4_4_center) :
    CFSG.GH74.GLS.Stage1.Thm3.Sec5.IVK_1_9_52 := by
  intro G _ _ z S K₁ K₂ a hC ha A B hAB hne hX
  classical
  have hM := m4_of_std hII hC.std
  have hAc : A = K₁ ∨ A = K₂ := by
    rcases hAB with ⟨h, _⟩ | ⟨h, _⟩
    · exact Or.inl h
    · exact Or.inr h
  have hAmem : A ∈ ({K₁, K₂} : Set (Subgroup G)) := by simpa using hAc
  have hOK := std4_hatOK h44 hC.std hAmem
  obtain ⟨haNA, -⟩ : InducesFAut a A := by
    rcases hAB with ⟨hA, _⟩ | ⟨hA, _⟩
    · rw [hA]
      exact ha.f₁
    · rw [hA]
      exact ha.f₂
  rcases sl_or_a7 hOK.sl2 with ⟨F, hFf, hFin, hodd, h3, ⟨e⟩⟩ | h7
  · set X : Subgroup G := Qof S B ⊔ zpowers a with hXdef
    have hQX : Qof S B ≤ X := le_sup_left
    have hXS : X ≤ S := sup_le Qof_le_S (zpowers_le.2 ha.mem)
    have hXN : X ≤ normalizer (A : Set G) :=
      sup_le (QB_le_normalizer hII hC hAB) (zpowers_le.2 haNA)
    let ρ : ↥X →* MulAut (Hat A) := (phiHom A).comp (Subgroup.inclusion hXN)
    have hρ : ∀ x : ↥X, ρ x = phi A (x : G) (hXN x.2) := fun x => rfl
    have hSyl := std4_exists_sylow_P hC.std hAc
    have hZ := sq_eq_one_of_card_center hOK.sl2.2
    have hSp : IsPGroup 2 ↥S := hC.std.sylow.isPGroup
    have hzP : z ∈ Pof S A := ⟨hM.z_mem_S, hM.z_mem_comp hAc⟩
    have hPQ : Pof S A ≤ Qof S B := Pof_le_Qof hM hAB
    have hinner : ∀ x : ↥X, ρ x ∈ innOf (Hat A) → (x : G) ∈ Pof S A := by
      intro x hxin
      have hin : InducesInner (x : G) A := by
        rw [hρ] at hxin
        exact (phi_mem_inn_iff A (hXN x.2)).1 hxin
      obtain ⟨k₀, hk₀, hk₀c⟩ := lift_inner_gen hSp hSyl hZ (hXS x.2) (hXN x.2) hin
      have hk₀X : k₀ ∈ X := hQX (hPQ hk₀)
      have hyX : (x : G) * k₀⁻¹ ∈ X := X.mul_mem x.2 (X.inv_mem hk₀X)
      have hy : (x : G) * k₀⁻¹ ∈ X ⊓ Qof S A := ⟨hyX, hk₀c⟩
      have hyz := zpowers_le.2 hzP (hX hy)
      have h5 : (x : G) = ((x : G) * k₀⁻¹) * k₀ := by group
      rw [h5]
      exact (Pof S A).mul_mem hyz hk₀
    have hN : ∀ x : ↥X, x ∈ (Pof S A).subgroupOf X ↔ ρ x ∈ innOf (Hat A) := by
      intro x
      rw [Subgroup.mem_subgroupOf]
      constructor
      · intro hxP
        rw [hρ, phi_of_mem A hxP.2]
        exact ⟨_, rfl⟩
      · exact hinner x
    have hnormal : ((Pof S A).subgroupOf X).Normal := by
      have : (Pof S A).subgroupOf X = (innOf (Hat A)).comap ρ := Subgroup.ext hN
      rw [this]
      exact (innOf_normal (Hat A)).comap ρ
    refine ⟨hnormal, ?_⟩
    refine isCyclic_of_signs hodd h3 e ρ ((Pof S A).subgroupOf X) hN ?_
    intro x hev
    set n := orderOf (gammaOf hodd h3 (MulAut.congr e (ρ x))).right with hn
    have hinn := pow_mem_inn_of_even hodd h3 (MulAut.congr e (ρ x)) hev
    have hinn' : ρ x ^ n ∈ innOf (Hat A) := by
      obtain ⟨s, hs⟩ := hinn
      refine ⟨e.symm s, ?_⟩
      apply (MulAut.congr e).injective
      rw [congr_conj, MulEquiv.apply_symm_apply, hs, map_pow]
    have hP : ((x ^ n : ↥X) : G) ∈ Pof S A := hinner (x ^ n) (by rw [map_pow]; exact hinn')
    refine ⟨hatMk A ⟨((x ^ n : ↥X) : G), hP.2⟩, ?_, ?_⟩
    · rw [← map_pow, hρ]
      exact phi_of_mem A hP.2
    · rw [hρ, phi_mk]
      congr 1
      apply Subtype.ext
      show (x : G) * ((x ^ n : ↥X) : G) * (x : G)⁻¹ = ((x ^ n : ↥X) : G)
      have h6 : ((x ^ n : ↥X) : G) = (x : G) ^ n := rfl
      rw [h6, (Commute.self_pow (x : G) n).eq, mul_inv_cancel_right]
  · exact (a7_excluded52 h2A7 hII hC hAB hne h7).elim

end Leaves

end CFSG.GH74.GLS.IVK.Lifted
