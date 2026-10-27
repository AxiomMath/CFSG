module

public import CFSG.GroupTheory.ElementaryAbelianTransport
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection6.Defs
public import CFSG.LocalAnalysis.SectionRank.Ccomm.NonabelianCube
public import CFSG.LocalAnalysis.SectionRank.Ccomm.PowerMap
public import CFSG.RankThree.GroupTheory.SteinbergBKTwoStageAutomorphismKernel

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.Monster13

open Subgroup
open scoped commutatorElement

section Core

variable {K : Type*} [Group K]

theorem le_pCore_of_normal_isPGroup {p : ℕ} {N : Subgroup K} (hN : N.Normal) (hNp : IsPGroup p N) :
    N ≤ CFSG.pCore p K :=
  le_sSup (show N ∈ {L : Subgroup K | L.Normal ∧ IsPGroup p L} from ⟨hN, hNp⟩)

def conjRestr (N : Subgroup K) [N.Normal] : K →* MulAut N where
  toFun k :=
    { toFun := fun x => ⟨k * x * k⁻¹, Subgroup.Normal.conj_mem inferInstance _ x.2 k⟩
      invFun := fun x => ⟨k⁻¹ * x * k⁻¹⁻¹, Subgroup.Normal.conj_mem inferInstance _ x.2 k⁻¹⟩
      left_inv := fun x => Subtype.ext (by show k⁻¹ * (k * x * k⁻¹) * k⁻¹⁻¹ = x; group)
      right_inv := fun x => Subtype.ext (by show k * (k⁻¹ * x * k⁻¹⁻¹) * k⁻¹ = x; group)
      map_mul' := fun x y =>
        Subtype.ext (by show k * (x * y) * k⁻¹ = k * x * k⁻¹ * (k * y * k⁻¹); group) }
  map_one' := MulEquiv.ext fun x => Subtype.ext (by simp)
  map_mul' k₁ k₂ := MulEquiv.ext fun x =>
    Subtype.ext (by show k₁ * k₂ * x * (k₁ * k₂)⁻¹ = k₁ * (k₂ * x * k₂⁻¹) * k₁⁻¹; group)

def stab (P : Subgroup K) [P.Normal] (Z : Subgroup K) (hZc : ∀ g : K, ∀ z ∈ Z, g * z * g⁻¹ = z) :
    Subgroup K where
  carrier := {k | ∀ x ∈ P, k * x * k⁻¹ * x⁻¹ ∈ Z}
  mul_mem' := by
    intro a b ha hb x hx
    have e : a * b * x * (a * b)⁻¹ * x⁻¹ =
        a * (b * x * b⁻¹ * x⁻¹) * a⁻¹ * (a * x * a⁻¹ * x⁻¹) := by group
    show a * b * x * (a * b)⁻¹ * x⁻¹ ∈ Z
    rw [e, hZc a _ (hb x hx)]
    exact Z.mul_mem (hb x hx) (ha x hx)
  one_mem' := by
    intro x _
    simpa using Z.one_mem
  inv_mem' := by
    intro k hk x hx
    have hy : k⁻¹ * x * k⁻¹⁻¹ ∈ P := Subgroup.Normal.conj_mem inferInstance _ hx k⁻¹
    have e : k⁻¹ * x * k⁻¹⁻¹ * x⁻¹ = (k * (k⁻¹ * x * k⁻¹⁻¹) * k⁻¹ * (k⁻¹ * x * k⁻¹⁻¹)⁻¹)⁻¹ := by
      group
    show k⁻¹ * x * k⁻¹⁻¹ * x⁻¹ ∈ Z
    rw [e]
    exact Z.inv_mem (hk _ hy)


theorem sylow_normal_of_core {p : ℕ} [hp : Fact p.Prime] [Finite K]
    (hsolv : Group.IsSolvable K) (hcore : CFSG.pPrimeCore p K = ⊥)
    {c : K} (hc : orderOf c = p) (hcz : c ∈ Subgroup.center K)
    {S : Subgroup K} (hSp : IsPGroup p S)
    (hSmax : ∀ T : Subgroup K, IsPGroup p T → S ≤ T → T = S)
    (hS3 : Nat.card S = p ^ 3) (hSnab : ∃ a b : S, a * b ≠ b * a) (hcS : c ∈ S) :
    S.Normal ∧ ∀ k : K, (∀ s ∈ S, k * s = s * k) → k ∈ S := by
  have hcomm : ∀ g : K, g * c = c * g := fun g => Subgroup.mem_center_iff.1 hcz g
  have hcen : ∀ g : K, ∀ z ∈ Subgroup.zpowers c, g * z * g⁻¹ = z := by
    intro g z hz
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 hz
    have h := Commute.zpow_right (show Commute g c from hcomm g) n
    show g * c ^ n * g⁻¹ = c ^ n
    rw [show g * c ^ n = c ^ n * g from h, mul_inv_cancel_right]
  have hZn : (Subgroup.zpowers c).Normal :=
    ⟨fun n hn g => by rw [hcen g n hn]; exact hn⟩
  have hZp : IsPGroup p (Subgroup.zpowers c) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hc, pow_one])
  have hp2 := hp.out.two_le
  set P₀ : Subgroup K := CFSG.pCore p K with hP₀def
  have hP₀n : P₀.Normal := CFSG.pCore_normal
  have hP₀p : IsPGroup p P₀ := CFSG.pCore_isPGroup
  have hC₀ : Subgroup.centralizer (P₀ : Set K) ≤ P₀ :=
    CFSG.centralizer_pCore_le_pCore_of_pPrimeCore_eq_bot hsolv hcore
  have hmaxP : ∀ N : Subgroup K, N.Normal → IsPGroup p N → N ≤ P₀ :=
    fun N hN hNp => le_pCore_of_normal_isPGroup hN hNp
  have hZP : Subgroup.zpowers c ≤ P₀ := hmaxP _ hZn hZp
  have hP₀S : P₀ ≤ S := by
    haveI := hP₀n
    have h := hSmax (S ⊔ P₀) (IsPGroup.to_sup_of_normal_right hSp hP₀p) le_sup_left
    exact le_sup_right.trans h.le
  have hPdvd : Nat.card P₀ ∣ p ^ 3 := hS3 ▸ Subgroup.card_dvd_of_le hP₀S
  obtain ⟨k, hk3, hPk⟩ := (Nat.dvd_prime_pow hp.out).1 hPdvd
  have hk1 : 1 ≤ k := by
    rcases Nat.eq_zero_or_pos k with h | h
    · exfalso
      have h1 := Subgroup.card_le_of_le hZP
      rw [Nat.card_zpowers, hc, hPk, h, pow_zero] at h1
      omega
    · exact h
  interval_cases k
  ·
    exfalso
    have hPZ : P₀ = Subgroup.zpowers c :=
      (Subgroup.eq_of_le_of_card_ge hZP
        (le_of_eq (by rw [hPk, Nat.card_zpowers, hc, pow_one]))).symm
    have hall : ∀ x : K, x ∈ P₀ := by
      intro x
      apply hC₀
      rw [Subgroup.mem_centralizer_iff]
      intro h hh
      rw [hPZ] at hh
      obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 hh
      exact (Commute.zpow_left (show Commute c x from (hcomm x).symm) n).eq
    have hSP : S ≤ P₀ := fun s _ => hall s
    have h1 := Subgroup.card_le_of_le hSP
    rw [hS3, hPk, pow_one] at h1
    have h3 : p ^ 1 < p ^ 3 := Nat.pow_lt_pow_right (by omega) (by norm_num)
    rw [pow_one] at h3
    omega
  ·
    exfalso
    have hPab : ∀ x ∈ P₀, ∀ y ∈ P₀, x * y = y * x := by
      intro x hx y hy
      exact congrArg Subtype.val
        ((IsPGroup.isMulCommutative_of_card_eq_prime_sq (p := p) (G := ↥P₀) hPk).is_comm.comm
          ⟨x, hx⟩ ⟨y, hy⟩)
    obtain ⟨hcomm_eq, hZcard, -, -, -, -, -⟩ :=
      CFSG.SectionRank.Ccomm.nonabelian_prime_cube_central_structure (p := p) (S := ↥S) hS3 hSnab
    have hZs_card : Nat.card ↥((Subgroup.center ↥S).map S.subtype) = p := by
      rw [Subgroup.card_map_of_injective S.subtype_injective, hZcard]
    have hcS' : c ∈ (Subgroup.center ↥S).map S.subtype := by
      exact ⟨⟨c, hcS⟩, Subgroup.mem_center_iff.2 fun g => Subtype.ext (hcomm _), rfl⟩
    have hZS_eq : Subgroup.zpowers c = (Subgroup.center ↥S).map S.subtype := by
      refine Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.2 hcS') (le_of_eq ?_)
      rw [hZs_card, Nat.card_zpowers, hc]
    have hZS : ∀ s ∈ S, ∀ t ∈ S, s * t * s⁻¹ * t⁻¹ ∈ Subgroup.zpowers c := by
      intro s hs t ht
      have h1 : (⟨s, hs⟩ : ↥S) * ⟨t, ht⟩ * (⟨s, hs⟩ : ↥S)⁻¹ * (⟨t, ht⟩ : ↥S)⁻¹ ∈
          Subgroup.center ↥S := by
        have h2 : ⁅(⟨s, hs⟩ : ↥S), ⟨t, ht⟩⁆ ∈ commutator ↥S :=
          commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _)
        rw [hcomm_eq, commutatorElement_def] at h2
        exact h2
      have h3 := Subgroup.mem_map_of_mem S.subtype h1
      rw [← hZS_eq] at h3
      simpa using h3
    let K₁ : Subgroup K := stab P₀ (Subgroup.zpowers c) hcen
    have hK₁S : S ≤ K₁ := by
      intro s hs
      show ∀ x ∈ P₀, s * x * s⁻¹ * x⁻¹ ∈ Subgroup.zpowers c
      exact fun x hx => hZS s hs x (hP₀S hx)
    have hK₁n : K₁.Normal := by
      refine ⟨fun k hk g => ?_⟩
      have hk' : ∀ y ∈ P₀, k * y * k⁻¹ * y⁻¹ ∈ Subgroup.zpowers c := hk
      show ∀ x ∈ P₀, g * k * g⁻¹ * x * (g * k * g⁻¹)⁻¹ * x⁻¹ ∈ Subgroup.zpowers c
      intro x hx
      have hy : g⁻¹ * x * g⁻¹⁻¹ ∈ P₀ := Subgroup.Normal.conj_mem inferInstance _ hx g⁻¹
      have hz := hk' _ hy
      have e : g * k * g⁻¹ * x * (g * k * g⁻¹)⁻¹ * x⁻¹ =
          g * (k * (g⁻¹ * x * g⁻¹⁻¹) * k⁻¹ * (g⁻¹ * x * g⁻¹⁻¹)⁻¹) * g⁻¹ := by group
      rw [e, hcen g _ hz]
      exact hz
    let W : Subgroup ↥P₀ := (Subgroup.zpowers c).comap P₀.subtype
    have hWn : W.Normal := by
      refine ⟨fun w hw g => ?_⟩
      rw [Subgroup.mem_comap] at hw ⊢
      have hw' : (w : K) ∈ Subgroup.zpowers c := hw
      have e := hcen (g : K) (w : K) hw'
      show (g : K) * (w : K) * (g : K)⁻¹ ∈ Subgroup.zpowers c
      rw [e]
      exact hw
    have hWp : IsPGroup p W := hZp.comap_of_injective P₀.subtype Subtype.coe_injective
    let ψ : K₁ →* MulAut ↥P₀ := (conjRestr P₀).comp K₁.subtype
    have hAW : ∀ α ∈ ψ.range, ∀ w ∈ W, α w = w := by
      rintro α ⟨k, rfl⟩ w hw
      apply Subtype.ext
      have hwc : (w : K) ∈ Subgroup.zpowers c := Subgroup.mem_comap.1 hw
      show (k : K) * (w : K) * (k : K)⁻¹ = (w : K)
      exact hcen k _ hwc
    have hAQ : ∀ α ∈ ψ.range, ∀ x : ↥P₀, x⁻¹ * α x ∈ W := by
      rintro α ⟨k, rfl⟩ x
      rw [Subgroup.mem_comap]
      have hk' : ∀ y ∈ P₀, (k : K) * y * (k : K)⁻¹ * y⁻¹ ∈ Subgroup.zpowers c := k.2
      have hz := hk' x x.2
      have hzc : (x : K) * ((k : K) * x * (k : K)⁻¹ * (x : K)⁻¹) * (x : K)⁻¹ =
          (k : K) * x * (k : K)⁻¹ * (x : K)⁻¹ := hcen _ _ hz
      have hxz : (x : K) * ((k : K) * x * (k : K)⁻¹ * (x : K)⁻¹) =
          ((k : K) * x * (k : K)⁻¹ * (x : K)⁻¹) * (x : K) := mul_inv_eq_iff_eq_mul.1 hzc
      have e : (x : K)⁻¹ * ((k : K) * x * (k : K)⁻¹) =
          (k : K) * x * (k : K)⁻¹ * (x : K)⁻¹ := by
        calc (x : K)⁻¹ * ((k : K) * x * (k : K)⁻¹)
            = (x : K)⁻¹ * (((k : K) * x * (k : K)⁻¹ * (x : K)⁻¹) * (x : K)) := by group
          _ = (x : K)⁻¹ * ((x : K) * ((k : K) * x * (k : K)⁻¹ * (x : K)⁻¹)) := by rw [hxz]
          _ = (k : K) * x * (k : K)⁻¹ * (x : K)⁻¹ := by group
      show (x : K)⁻¹ * ((k : K) * x * (k : K)⁻¹) ∈ Subgroup.zpowers c
      rw [e]
      exact hz
    have hA : IsPGroup p ψ.range :=
      (CFSG.RankThree.GroupTheory.SteinbergBK.two_stage_automorphism_kernel W hWp ψ.range
        hAW hAQ).1
    have hK₁p : IsPGroup p K₁ := by
      intro g
      obtain ⟨n, hn⟩ := hA ⟨ψ g, MonoidHom.mem_range.2 ⟨g, rfl⟩⟩
      have hn' : (ψ g) ^ (p ^ n) = 1 := by
        have := congrArg Subtype.val hn
        simpa using this
      have hψ : ψ (g ^ (p ^ n)) = 1 := by rw [map_pow]; exact hn'
      have hcen1 : ((g : K) ^ (p ^ n)) ∈ Subgroup.centralizer (P₀ : Set K) := by
        rw [Subgroup.mem_centralizer_iff]
        intro x hx
        have h1 := congrArg Subtype.val (DFunLike.congr_fun hψ ⟨x, hx⟩)
        have h2 : (g : K) ^ (p ^ n) * x * ((g : K) ^ (p ^ n))⁻¹ = x := h1
        exact (mul_inv_eq_iff_eq_mul.1 h2).symm
      have hmemP : (g : K) ^ (p ^ n) ∈ P₀ := hC₀ hcen1
      obtain ⟨m, hm⟩ := hP₀p ⟨(g : K) ^ (p ^ n), hmemP⟩
      have hm' : ((g : K) ^ (p ^ n)) ^ (p ^ m) = 1 := by
        have := congrArg Subtype.val hm
        simpa using this
      refine ⟨n + m, Subtype.ext ?_⟩
      show (g : K) ^ (p ^ (n + m)) = 1
      rw [pow_add, pow_mul, hm']
    have hK₁P : K₁ ≤ P₀ := hmaxP K₁ hK₁n hK₁p
    have hSP : S ≤ P₀ := hK₁S.trans hK₁P
    have h1 := Subgroup.card_le_of_le hSP
    rw [hS3, hPk] at h1
    have h3 : p ^ 2 < p ^ 3 := Nat.pow_lt_pow_right (by omega) (by norm_num)
    omega
  ·
    have hPS : P₀ = S := Subgroup.eq_of_le_of_card_ge hP₀S (le_of_eq (by rw [hS3, hPk]))
    refine ⟨by rw [← hPS]; exact hP₀n, fun k hk => ?_⟩
    have hkC : k ∈ Subgroup.centralizer (P₀ : Set K) := by
      rw [Subgroup.mem_centralizer_iff]
      intro h hh
      rw [hPS] at hh
      exact (hk h hh).symm
    have := hC₀ hkC
    rw [hPS] at this
    exact this


theorem inf_eq_bot_of_not_dvd {p : ℕ} [hp : Fact p.Prime] {H T : Subgroup K}
    (hH : ¬ p ∣ Nat.card H) (hT : IsPGroup p T) : H ⊓ T = ⊥ := by
  have hp' : IsPGroup p ↥(H ⊓ T) := fun g => by
    obtain ⟨n, hn⟩ := hT ⟨(g : K), (Subgroup.mem_inf.1 g.2).2⟩
    exact ⟨n, Subtype.ext (by simpa using congrArg Subtype.val hn)⟩
  have hd : Nat.card ↥(H ⊓ T) ∣ Nat.card H := Subgroup.card_dvd_of_le inf_le_left
  rcases hp'.card_eq_or_dvd with h1 | h1
  · exact Subgroup.eq_bot_of_card_eq _ h1
  · exact absurd (dvd_trans h1 hd) hH

theorem card_subgroupOf_of_le' {R S : Subgroup K} (h : R ≤ S) :
    Nat.card (R.subgroupOf S) = Nat.card R := by
  rw [← Subgroup.card_map_of_injective S.subtype_injective, Subgroup.subgroupOf_map_subtype,
    inf_eq_left.2 h]

theorem balance_of_sylow_core {p : ℕ} [hp : Fact p.Prime] [Finite K]
    {c : K} (hc : orderOf c = p) (hcz : c ∈ Subgroup.center K)
    {S : Subgroup K} (hSp : IsPGroup p S)
    (hSmax : ∀ T : Subgroup K, IsPGroup p T → S ≤ T → T = S)
    (hS3 : Nat.card S = p ^ 3) (hSnab : ∃ a b : S, a * b ≠ b * a) (hcS : c ∈ S)
    (hSN : S.Normal) (hCS : ∀ k : K, (∀ s ∈ S, k * s = s * k) → k ∈ S)
    {R Y : Subgroup K} (hR : CFSG.Open.IsElemAbelian p R) (hR2 : Nat.card R = p ^ 2)
    (hcR : c ∈ R) (hY : ¬ p ∣ Nat.card Y) (hRY : R ≤ Subgroup.normalizer (Y : Set K)) :
    Y = ⊥ := by
  haveI hSNi : S.Normal := hSN
  have hcomm : ∀ g : K, g * c = c * g := fun g => Subgroup.mem_center_iff.1 hcz g
  have hcen : ∀ g : K, ∀ z ∈ Subgroup.zpowers c, g * z * g⁻¹ = z := by
    intro g z hz
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 hz
    have h := Commute.zpow_right (show Commute g c from hcomm g) n
    show g * c ^ n * g⁻¹ = c ^ n
    rw [show g * c ^ n = c ^ n * g from h, mul_inv_cancel_right]
  obtain ⟨hcomm_eq, hZcard, -, -, -, hsub, -⟩ :=
    CFSG.SectionRank.Ccomm.nonabelian_prime_cube_central_structure (p := p) (S := ↥S) hS3 hSnab
  have hZs_card : Nat.card ↥((Subgroup.center ↥S).map S.subtype) = p := by
    rw [Subgroup.card_map_of_injective S.subtype_injective, hZcard]
  have hcS' : c ∈ (Subgroup.center ↥S).map S.subtype :=
    ⟨⟨c, hcS⟩, Subgroup.mem_center_iff.2 fun g => Subtype.ext (hcomm _), rfl⟩
  have hZS_eq : Subgroup.zpowers c = (Subgroup.center ↥S).map S.subtype := by
    refine Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.2 hcS') (le_of_eq ?_)
    rw [hZs_card, Nat.card_zpowers, hc]
  have hcomm_mem : ∀ s ∈ S, ∀ t ∈ S, s * t * s⁻¹ * t⁻¹ ∈ Subgroup.zpowers c := by
    intro s hs t ht
    have h1 : (⟨s, hs⟩ : ↥S) * ⟨t, ht⟩ * (⟨s, hs⟩ : ↥S)⁻¹ * (⟨t, ht⟩ : ↥S)⁻¹ ∈
        Subgroup.center ↥S := by
      have h2 : ⁅(⟨s, hs⟩ : ↥S), ⟨t, ht⟩⁆ ∈ commutator ↥S :=
        commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _)
      rw [hcomm_eq, commutatorElement_def] at h2
      exact h2
    have h3 := Subgroup.mem_map_of_mem S.subtype h1
    rw [← hZS_eq] at h3
    simpa using h3
  have hZR : Subgroup.zpowers c ≤ R := (Subgroup.zpowers_le).2 hcR
  have hRS : R ≤ S := by
    haveI := hSN
    have h := hSmax (R ⊔ S)
      (IsPGroup.to_sup_of_normal_right (CFSG.Open.IsElemAbelian.isPGroup hR) hSp) le_sup_right
    exact le_sup_left.trans h.le
  have hRS' := hsub (R.subgroupOf S) (by rw [card_subgroupOf_of_le' hRS, hR2])
  obtain ⟨-, hRn', -, hcentR⟩ := hRS'
  have hRnorm : ∀ s ∈ S, ∀ r ∈ R, s * r * s⁻¹ ∈ R := by
    intro s hs r hr
    have h := Subgroup.Normal.conj_mem hRn' (⟨r, hRS hr⟩ : ↥S)
      (Subgroup.mem_subgroupOf.2 hr) ⟨s, hs⟩
    exact Subgroup.mem_subgroupOf.1 h
  have hRcent : ∀ w ∈ S, (∀ r ∈ R, w * r = r * w) → w ∈ R := by
    intro w hw hwr
    have h1 : (⟨w, hw⟩ : ↥S) ∈ Subgroup.centralizer ((R.subgroupOf S : Subgroup ↥S) : Set ↥S) := by
      rw [Subgroup.mem_centralizer_iff]
      intro t ht
      exact Subtype.ext (hwr _ (Subgroup.mem_subgroupOf.1 ht)).symm
    rw [hcentR] at h1
    exact Subgroup.mem_subgroupOf.1 h1
  obtain ⟨x, hxS, hxR⟩ : ∃ x ∈ S, x ∉ R := by
    by_contra h
    have hSR : S ≤ R := fun t ht => by_contra fun hn => h ⟨t, ht, hn⟩
    have h1 := Subgroup.card_le_of_le hSR
    rw [hS3, hR2] at h1
    have h3 : p ^ 2 < p ^ 3 := Nat.pow_lt_pow_right hp.out.one_lt (by norm_num)
    omega
  have hTS : R ⊔ Subgroup.zpowers x = S := by
    have hle : R ⊔ Subgroup.zpowers x ≤ S := sup_le hRS (Subgroup.zpowers_le.2 hxS)
    have hd1 : Nat.card R ∣ Nat.card ↥(R ⊔ Subgroup.zpowers x) :=
      Subgroup.card_dvd_of_le le_sup_left
    have hd2 : Nat.card ↥(R ⊔ Subgroup.zpowers x) ∣ p ^ 3 := hS3 ▸ Subgroup.card_dvd_of_le hle
    obtain ⟨j, hj3, hjT⟩ := (Nat.dvd_prime_pow hp.out).1 hd2
    have hj2 : 2 ≤ j := by
      rw [hR2, hjT] at hd1
      exact (Nat.pow_dvd_pow_iff_le_right hp.out.one_lt).1 hd1
    rcases (show j = 2 ∨ j = 3 by omega) with h2 | h3
    · exfalso
      have heq : R = R ⊔ Subgroup.zpowers x :=
        Subgroup.eq_of_le_of_card_ge le_sup_left (le_of_eq (by rw [hR2, hjT, h2]))
      have hxm : x ∈ R ⊔ Subgroup.zpowers x :=
        (show Subgroup.zpowers x ≤ R ⊔ Subgroup.zpowers x from le_sup_right)
          (Subgroup.mem_zpowers x)
      rw [← heq] at hxm
      exact hxR hxm
    · exact Subgroup.eq_of_le_of_card_ge hle (le_of_eq (by rw [hS3, hjT, h3]))
  have hY0 : ∀ y ∈ Y, y = 1 := by
    intro y hy
    have hyr_gen : ∀ r ∈ R, y * r * y⁻¹ = r := by
      intro r hr
      have hYS : y * r * y⁻¹ * r⁻¹ ∈ Y ⊓ S := by
        refine ⟨?_, ?_⟩
        · have h1 : r * y⁻¹ * r⁻¹ ∈ Y := (mem_normalizer_iff.1 (hRY hr) y⁻¹).1 (Y.inv_mem hy)
          have e : y * r * y⁻¹ * r⁻¹ = y * (r * y⁻¹ * r⁻¹) := by group
          rw [e]
          exact Y.mul_mem hy h1
        · exact S.mul_mem (Subgroup.Normal.conj_mem hSN r (hRS hr) y) (S.inv_mem (hRS hr))
      rw [inf_eq_bot_of_not_dvd hY hSp, Subgroup.mem_bot] at hYS
      calc y * r * y⁻¹ = (y * r * y⁻¹ * r⁻¹) * r := by group
        _ = r := by rw [hYS, one_mul]
    have hyR : ∀ r ∈ R, y * r = r * y := fun r hr => by
      calc y * r = (y * r * y⁻¹) * y := by group
        _ = r * y := by rw [hyr_gen r hr]
    have hxSg : y * x * y⁻¹ * x⁻¹ ∈ R := by
      obtain ⟨w, hw⟩ : ∃ w : K, w = y * x * y⁻¹ * x⁻¹ := ⟨_, rfl⟩
      rw [← hw]
      have hwS : w ∈ S := by
        rw [hw]
        exact S.mul_mem (Subgroup.Normal.conj_mem hSN x hxS y) (S.inv_mem hxS)
      have hyxw : y * x * y⁻¹ = w * x := by rw [hw]; group
      refine hRcent w hwS fun r hr => ?_
      obtain ⟨u, hu⟩ : ∃ u : K, u = x * r * x⁻¹ * r⁻¹ := ⟨_, rfl⟩
      have hu_mem : u ∈ Subgroup.zpowers c := by
        rw [hu]
        exact hcomm_mem x hxS r (hRS hr)
      have hwu : w * u = u * w := by
        have h := hcen w u hu_mem
        rwa [mul_inv_eq_iff_eq_mul] at h
      have hyu : y * u * y⁻¹ = u := hcen y u hu_mem
      have hconj : y * u * y⁻¹ = w * (u * r) * w⁻¹ * r⁻¹ := by
        calc y * u * y⁻¹ = (y * x * y⁻¹) * (y * r * y⁻¹) * (y * x * y⁻¹)⁻¹ * (y * r * y⁻¹)⁻¹ := by
              rw [hu]; group
          _ = (w * x) * r * (w * x)⁻¹ * r⁻¹ := by rw [hyr_gen r hr, hyxw]
          _ = w * (u * r) * w⁻¹ * r⁻¹ := by rw [hu]; group
      have h1 : u = u * (w * r * w⁻¹ * r⁻¹) := by
        calc u = y * u * y⁻¹ := hyu.symm
          _ = w * (u * r) * w⁻¹ * r⁻¹ := hconj
          _ = (w * u) * r * w⁻¹ * r⁻¹ := by group
          _ = (u * w) * r * w⁻¹ * r⁻¹ := by rw [hwu]
          _ = u * (w * r * w⁻¹ * r⁻¹) := by group
      have h2 : w * r * w⁻¹ * r⁻¹ = 1 := by
        calc w * r * w⁻¹ * r⁻¹ = u⁻¹ * (u * (w * r * w⁻¹ * r⁻¹)) := by group
          _ = u⁻¹ * u := by rw [← h1]
          _ = 1 := by group
      calc w * r = (w * r * w⁻¹ * r⁻¹) * r * w := by group
        _ = r * w := by rw [h2, one_mul]
    let Sg : Subgroup K :=
      { carrier := {s | s ∈ S ∧ y * s * y⁻¹ * s⁻¹ ∈ R}
        mul_mem' := by
          rintro a b ⟨ha, ha'⟩ ⟨hb, hb'⟩
          refine ⟨S.mul_mem ha hb, ?_⟩
          have e : y * (a * b) * y⁻¹ * (a * b)⁻¹ =
              (y * a * y⁻¹ * a⁻¹) * (a * (y * b * y⁻¹ * b⁻¹) * a⁻¹) := by group
          rw [e]
          exact R.mul_mem ha' (hRnorm a ha _ hb')
        one_mem' := ⟨S.one_mem, by simpa using R.one_mem⟩
        inv_mem' := by
          rintro a ⟨ha, ha'⟩
          refine ⟨S.inv_mem ha, ?_⟩
          have e : y * a⁻¹ * y⁻¹ * a⁻¹⁻¹ = a⁻¹ * (y * a * y⁻¹ * a⁻¹)⁻¹ * a⁻¹⁻¹ := by group
          rw [e]
          exact hRnorm a⁻¹ (S.inv_mem ha) _ (R.inv_mem ha') }
    have hRSg : R ≤ Sg := by
      intro r hr
      refine ⟨hRS hr, ?_⟩
      show y * r * y⁻¹ * r⁻¹ ∈ R
      rw [hyr_gen r hr]
      simpa using R.one_mem
    have hxSgm : x ∈ Sg := ⟨hxS, hxSg⟩
    have hSgS : S ≤ Sg := by
      have h := sup_le hRSg (Subgroup.zpowers_le.2 hxSgm)
      rw [hTS] at h
      exact h
    haveI : (R.subgroupOf S).Normal := hRn'
    have hfix : ∀ n ∈ R.subgroupOf S, CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.Monster13.conjRestr
        S y n = n := by
      intro n hn
      apply Subtype.ext
      have hnR : (n : K) ∈ R := Subgroup.mem_subgroupOf.1 hn
      show y * (n : K) * y⁻¹ = n
      exact hyr_gen _ hnR
    have hdisp : ∀ h : ↥S, h⁻¹ * CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.Monster13.conjRestr
        S y h ∈ R.subgroupOf S := by
      intro h
      rw [Subgroup.mem_subgroupOf]
      have ha : y * (h : K) * y⁻¹ * (h : K)⁻¹ ∈ R := (hSgS h.2).2
      have e : ((h⁻¹ * CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.Monster13.conjRestr S y h :
          ↥S) : K) = (h : K)⁻¹ * (y * h * y⁻¹ * (h : K)⁻¹) * (h : K)⁻¹⁻¹ := by
        show (h : K)⁻¹ * (y * (h : K) * y⁻¹) = _
        group
      rw [e]
      exact hRnorm _ (S.inv_mem h.2) _ ha
    have hpow : (CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.Monster13.conjRestr S y) ^
        (orderOf y) = 1 := by
      rw [← map_pow, pow_orderOf_eq_one, map_one]
    have hord : ¬ p ∣ orderOf y := by
      intro h
      have h1 : orderOf y ∣ Nat.card Y := by
        have := orderOf_dvd_natCard (⟨y, hy⟩ : ↥Y)
        rwa [Subgroup.orderOf_mk] at this
      exact hY (dvd_trans h h1)
    have hcop : Nat.Coprime (orderOf y) (Nat.card (R.subgroupOf S)) := by
      rw [card_subgroupOf_of_le' hRS, hR2]
      exact Nat.Coprime.pow_right 2 ((Nat.Prime.coprime_iff_not_dvd hp.out).2 hord).symm
    have hφ := CFSG.SectionRank.Ccomm.coprime_automorphism_trivial_normal_factors
      (R.subgroupOf S) (CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.Monster13.conjRestr S y)
      (Nat.succ_le_of_lt (orderOf_pos y)) hpow hcop hfix hdisp
    have hyC : ∀ s ∈ S, y * s = s * y := by
      intro s hs
      have h1 := congrArg Subtype.val (DFunLike.congr_fun hφ ⟨s, hs⟩)
      have h2 : y * s * y⁻¹ = s := h1
      exact mul_inv_eq_iff_eq_mul.1 h2
    have hyS : y ∈ S := hCS y hyC
    have hyS' : y ∈ Y ⊓ S := ⟨hy, hyS⟩
    rw [inf_eq_bot_of_not_dvd hY hSp, Subgroup.mem_bot] at hyS'
    exact hyS'
  exact eq_bot_iff.2 fun y hy => Subgroup.mem_bot.2 (hY0 y hy)

end Core

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.Monster13
