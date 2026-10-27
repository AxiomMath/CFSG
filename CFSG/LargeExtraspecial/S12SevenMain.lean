module

public import CFSG.LargeExtraspecial.S12SevenC
public import CFSG.LargeExtraspecial.S12EightMain
public import CFSG.LargeExtraspecial.S12FiveMain
public import CFSG.LargeExtraspecial.S12SevenB

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial

open Subgroup Module QuadraticMap CFSG.RankThree.OrthogonalInvolutions

universe u

namespace Setting

variable {G : Type u} [Group G] [Finite G] (S : Setting G)

theorem s12_fixed_eq_zero_or {H : Subgroup S.O} (hN : S.Mbar ≤ normalizer (H : Set S.O))
    (hH : H ≠ ⊥) :
    (∀ v : S.Qt, (∀ y ∈ H, (y : S.Qt ≃ₗ[ZMod 2] S.Qt) v = v) → v = 0) ∨ S.IsReducible12 := by
  by_cases h : ∀ v : S.Qt, (∀ y ∈ H, (y : S.Qt ≃ₗ[ZMod 2] S.Qt) v = v) → v = 0
  · exact Or.inl h
  right
  push Not at h
  obtain ⟨v₀, hv₀, hv₀0⟩ := h
  let W : Submodule (ZMod 2) S.Qt :=
    { carrier := {v | ∀ y ∈ H, (y : S.Qt ≃ₗ[ZMod 2] S.Qt) v = v}
      add_mem' := fun {v w} hv hw y hy => by rw [map_add, hv y hy, hw y hy]
      zero_mem' := fun y _ => map_zero _
      smul_mem' := fun c v hv y hy => by rw [map_smul, hv y hy] }
  refine ⟨W, fun hW => ?_, fun hW => ?_, fun m v hv y hy => ?_⟩
  · have h1 : v₀ ∈ W := hv₀
    rw [hW] at h1
    exact hv₀0 ((Submodule.mem_bot _).mp h1)
  · apply hH
    rw [eq_bot_iff]
    intro y hy
    rw [mem_bot]
    refine Subtype.ext (OrthoF2.eq_one_of_forall_apply_eq fun v => ?_)
    have h1 : v ∈ W := hW ▸ Submodule.mem_top
    exact h1 y hy
  · have hm : S.ρ m ∈ S.Mbar := ⟨m, rfl⟩
    have hy' : (S.ρ m)⁻¹ * y * (S.ρ m)⁻¹⁻¹ ∈ H :=
      (mem_normalizer_iff.mp (hN (S.Mbar.inv_mem hm)) y).mp hy
    have e := hv _ hy'
    have e2 : y * S.ρ m = S.ρ m * ((S.ρ m)⁻¹ * y * (S.ρ m)⁻¹⁻¹) := by group
    change (y : S.Qt ≃ₗ[ZMod 2] S.Qt) ((S.ρ m : S.Qt ≃ₗ[ZMod 2] S.Qt) v) =
      (S.ρ m : S.Qt ≃ₗ[ZMod 2] S.Qt) v
    rw [← LinearEquiv.mul_apply, ← Subgroup.coe_mul, e2, Subgroup.coe_mul, LinearEquiv.mul_apply,
      e]

variable {S}

theorem s12_conj_mem_zpowers {i j d : S.O} (hij : i * j = j * i) (hi3 : i ^ 3 = 1)
    (hj3 : j ^ 3 = 1)
    (hfpf : ∀ a b : ℕ, (a = 1 ∨ a = 2) → (b = 1 ∨ b = 2) →
      fixSpace ((i : S.Qt ≃ₗ[ZMod 2] S.Qt) ^ a * (j : S.Qt ≃ₗ[ZMod 2] S.Qt) ^ b) = ⊥)
    (hfix : fixSpace (i : S.Qt ≃ₗ[ZMod 2] S.Qt) ≠ ⊥) (hV : finrank (ZMod 2) S.Qt = 8)
    (hd : IsTypeA S.q (d : S.Qt ≃ₗ[ZMod 2] S.Qt) 2) {p r : ℕ} (hp : p < 3) (hr : r < 3)
    (hdi : d * i * d⁻¹ = j ^ p * i ^ r) : d * i * d⁻¹ ∈ zpowers i := by
  have hdd : d * d = 1 := Subtype.ext hd.2.2.1
  have hdinv : d⁻¹ = d := inv_eq_of_mul_eq_one_right hdd
  have h8 : ∀ {y : S.O}, fixSpace (y : S.Qt ≃ₗ[ZMod 2] S.Qt) = ⊥ →
      finrank (ZMod 2) (commSpace (y : S.Qt ≃ₗ[ZMod 2] S.Qt)) = 8 := by
    intro y hy
    have h1 := finrank_commSpace_add_finrank_fixSpace (y : S.Qt ≃ₗ[ZMod 2] S.Qt)
    rwa [hy, finrank_bot, add_zero, hV] at h1
  have hcoe : ∀ a b : ℕ, ((j ^ b * i ^ a : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) =
      (i : S.Qt ≃ₗ[ZMod 2] S.Qt) ^ a * (j : S.Qt ≃ₗ[ZMod 2] S.Qt) ^ b := by
    intro a b
    rw [((Commute.pow_pow (show Commute i j from hij) a b)).eq.symm, Subgroup.coe_mul,
      Subgroup.coe_pow, Subgroup.coe_pow]
  rcases Nat.eq_zero_or_pos p with rfl | hp0
  · rw [hdi, pow_zero, one_mul]
    exact pow_mem (mem_zpowers i) r
  exfalso
  have hp12 : p = 1 ∨ p = 2 := by omega
  rcases Nat.eq_zero_or_pos r with rfl | hr0
  ·
    rw [pow_zero, mul_one] at hdi
    have hjinv : (j ^ p)⁻¹ = j ^ (3 - p) := by
      rw [inv_eq_iff_mul_eq_one, ← pow_add, show p + (3 - p) = 3 by omega, hj3]
    set k := i * j ^ (3 - p) with hk
    have hfk : fixSpace (k : S.Qt ≃ₗ[ZMod 2] S.Qt) = ⊥ := by
      have h1 := hfpf 1 (3 - p) (Or.inl rfl) (by omega)
      rwa [pow_one, ← Subgroup.coe_pow, ← Subgroup.coe_mul] at h1
    have hk8 := h8 hfk
    have hk1 : k ≠ 1 := by
      intro h1
      rw [h1] at hk8
      have h0 : commSpace ((1 : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) = ⊥ := by
        rw [eq_bot_iff]
        intro v hv
        obtain ⟨w, rfl⟩ := mem_commSpace.mp hv
        simp
      rw [h0, finrank_bot] at hk8
      omega
    have hk3 : k ^ 3 = 1 := by
      rw [hk, (Commute.pow_right (show Commute i j from hij) (3 - p)).mul_pow, hi3, one_mul,
        ← pow_mul, show (3 - p) * 3 = 3 * (3 - p) by ring, pow_mul, hj3, one_pow]
    have hdj : d * j ^ p * d⁻¹ = i := by
      rw [← hdi]
      calc d * (d * i * d⁻¹) * d⁻¹ = (d * d) * i * (d * d)⁻¹ := by group
        _ = i := by rw [hdd]; group
    have hdk : d * k * d⁻¹ = k⁻¹ := by
      calc d * k * d⁻¹ = (d * i * d⁻¹) * (d * (j ^ p)⁻¹ * d⁻¹) := by rw [hk, ← hjinv]; group
        _ = j ^ p * (d * j ^ p * d⁻¹)⁻¹ := by rw [hdi]; group
        _ = j ^ p * i⁻¹ := by rw [hdj]
        _ = k⁻¹ := by rw [hk, ← hjinv]; group
    have h4 := s12_finrank_commSpace_of_inverted hd hk3 hk1 hdk
    omega
  ·
    have hr12 : r = 1 ∨ r = 2 := by omega
    have hf := hfpf r p hr12 hp12
    rw [← hcoe, ← hdi] at hf
    obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hfix
    have hdv : ((d * i * d⁻¹ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) ((d : S.Qt ≃ₗ[ZMod 2] S.Qt) v) =
        (d : S.Qt ≃ₗ[ZMod 2] S.Qt) v := by
      rw [hdinv, Subgroup.coe_mul, Subgroup.coe_mul, LinearEquiv.mul_apply,
        LinearEquiv.mul_apply, ← LinearEquiv.mul_apply (d : S.Qt ≃ₗ[ZMod 2] S.Qt)
          (d : S.Qt ≃ₗ[ZMod 2] S.Qt), hd.2.2.1,
        show (1 : S.Qt ≃ₗ[ZMod 2] S.Qt) v = v from rfl, mem_fixSpace.mp hv]
    have hmem : (d : S.Qt ≃ₗ[ZMod 2] S.Qt) v ∈
        fixSpace ((d * i * d⁻¹ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) := mem_fixSpace.mpr hdv
    rw [hf, Submodule.mem_bot] at hmem
    exact hv0 ((d : S.Qt ≃ₗ[ZMod 2] S.Qt).map_eq_zero_iff.mp hmem)

theorem timmesfeld_12_7 (hRI : RootInvolutionComponentsInput.{u}) {g : G}
    (haQ : g * S.z * g⁻¹ ∈ S.QG) (hne : g * S.z * g⁻¹ ≠ S.z) (hn : 4 ≤ S.width) {t : S.O}
    (ht : t ∈ S.Lbar g) (htA : IsTypeA S.q (t : S.Qt ≃ₗ[ZMod 2] S.Qt) 2) :
    S.O3Xbar12 g = ⊥ ∨ S.IsReducible12 := by
  by_cases hred : S.IsReducible12
  · exact Or.inr hred
  left
  by_contra hO
  have hn3 : 3 ≤ S.width := by omega
  have hcls := (S.timmesfeld_12_5 hRI haQ hne hn ht htA).resolve_left hred
  have hC := (S.timmesfeld_12_8 haQ hne hn ht htA).resolve_right hred
  have hZ := Z3Xbar12_ne_bot hO
  have htM : t ∈ S.Mbar := S.Lbar_le_Mbar g ht
  have htE : t ∈ S.Ebar12 g := mem_Ebar12_of_mem_Lbar ht htA
  have htt : t * t = 1 := Subtype.ext htA.2.2.1
  have hZN := Mbar_le_normalizer_Z3Xbar12 (S := S) (g := g)
  have hconjZ : ∀ {m : S.O}, m ∈ S.Mbar → ∀ y ∈ S.Z3Xbar12 g, m * y * m⁻¹ ∈ S.Z3Xbar12 g :=
    fun hm y hy => (mem_normalizer_iff.mp (hZN hm) y).mp hy
  have hV := S.finrank_Qt_eq_two_mul_width
  have hF := (S.s12_fixed_eq_zero_or hZN hZ).resolve_right hred
  have hstep1 : ∃ y ∈ S.Z3Xbar12 g, t * y * t⁻¹ ≠ y := by
    by_contra hcon
    push Not at hcon
    apply hZ
    rw [eq_bot_iff, ← hC]
    intro y hy
    refine ⟨Z3Xbar12_le_Mbar hy, ?_⟩
    have hX : S.Xbar12 g ≤ centralizer ({y} : Set S.O) := by
      rw [Xbar12, closure_le]
      intro τ hτ
      obtain ⟨x, hx, rfl⟩ := hcls τ hτ
      rw [SetLike.mem_coe, mem_centralizer_singleton_iff]
      have hy' : x⁻¹ * y * x⁻¹⁻¹ ∈ S.Z3Xbar12 g :=
        hconjZ (S.Mbar.inv_mem (Xbar12_le_Mbar hx)) y hy
      have e := hcon _ hy'
      calc x * t * x⁻¹ * y = x * (t * (x⁻¹ * y * x⁻¹⁻¹) * t⁻¹) * t * x⁻¹ := by group
        _ = x * (x⁻¹ * y * x⁻¹⁻¹) * t * x⁻¹ := by rw [e]
        _ = y * (x * t * x⁻¹) := by group
    exact mem_centralizer_iff.mpr fun x hx => mem_centralizer_singleton_iff.mp (hX hx)
  have hZc : ∀ x ∈ S.Z3Xbar12 g, ∀ y ∈ S.Z3Xbar12 g, x * y = y * x :=
    fun x hx y hy => commute_of_mem_Z3Xbar12 hx hy
  have hZodd : Odd (Nat.card (S.Z3Xbar12 g)) := by
    obtain ⟨m, hm⟩ := (isPGroup_Z3Xbar12 (S := S) (g := g)).exists_card_eq
    rw [hm]
    exact Odd.pow (by decide)
  have hcent : ∀ {c : S.O}, c ∈ S.Z3Xbar12 g → t * c * t⁻¹ = c → c ∈ S.centZ12 g t := by
    intro c hc hct
    refine mem_centZ12.mpr ⟨hc, ?_⟩
    calc c * t = (t * c * t⁻¹) * t := by rw [hct]
      _ = t * c := by group
  obtain ⟨y₀, hy₀, hy₀t⟩ := hstep1
  obtain ⟨c₀, -, i, hiZ, rfl, hc₀t, hit⟩ :=
    s12_exists_decomp hZc hZodd htt (hconjZ htM) hy₀
  have hiI : i ∈ S.invZ12 g t := ⟨hiZ, hit⟩
  have hi1 : i ≠ 1 := by
    rintro rfl
    apply hy₀t
    rw [mul_one, hc₀t]
  obtain ⟨hio, hidim⟩ := invZ12_orderOf htA hiI hi1
  have hIeq := invZ12_eq_zpowers htA hiI hi1
  have hi3 : i ^ 3 = 1 := by rw [← hio]; exact pow_orderOf_eq_one i
  by_cases hcase : ∀ x ∈ S.Xbar12 g, x * i * x⁻¹ ∈ S.invZ12 g t
  ·
    have hinvE : ∀ τ ∈ S.Ebar12 g, τ * i * τ⁻¹ = i⁻¹ := by
      intro τ hτ
      obtain ⟨x, hx, rfl⟩ := hcls τ hτ
      have h1 := (hcase x⁻¹ ((S.Xbar12 g).inv_mem hx)).2
      calc x * t * x⁻¹ * i * (x * t * x⁻¹)⁻¹ = x * (t * (x⁻¹ * i * x⁻¹⁻¹) * t⁻¹) * x⁻¹ := by
            group
        _ = x * (x⁻¹ * i * x⁻¹⁻¹)⁻¹ * x⁻¹ := by rw [h1]
        _ = i⁻¹ := by group
    have hMi : ∀ m ∈ S.Mbar, m * i * m⁻¹ ∈ S.invZ12 g t := by
      intro m hm
      refine ⟨hconjZ hm i hiZ, ?_⟩
      have h1 := hinvE _ (conj_mem_Ebar12 (S.Mbar.inv_mem hm) htE)
      calc t * (m * i * m⁻¹) * t⁻¹
          = m * ((m⁻¹ * t * m⁻¹⁻¹) * i * (m⁻¹ * t * m⁻¹⁻¹)⁻¹) * m⁻¹ := by group
        _ = m * i⁻¹ * m⁻¹ := by rw [h1]
        _ = (m * i * m⁻¹)⁻¹ := by group
    have hNi : S.Mbar ≤ normalizer ((zpowers i : Subgroup S.O) : Set S.O) := by
      intro m hm
      refine mem_normalizer_of_conj_le (fun y hy => ?_) (fun y hy => ?_)
      · obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hy
        rw [← conj_zpow, ← hIeq]
        exact (S.invZ12 g t).zpow_mem (hMi m hm) k
      · obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hy
        rw [← conj_zpow, ← hIeq]
        exact (S.invZ12 g t).zpow_mem (hMi m⁻¹ (S.Mbar.inv_mem hm)) k
    have hzp : (zpowers i : Subgroup S.O) ≠ ⊥ := by
      intro h
      apply hi1
      have h1 := mem_zpowers i
      rwa [h, mem_bot] at h1
    have hfi := (S.s12_fixed_eq_zero_or hNi hzp).resolve_right hred
    have hfix0 : fixSpace (i : S.Qt ≃ₗ[ZMod 2] S.Qt) = ⊥ := by
      rw [eq_bot_iff]
      intro v hv
      rw [Submodule.mem_bot]
      refine hfi v fun y hy => ?_
      obtain ⟨n, rfl⟩ := mem_powers_iff_mem_zpowers.mpr hy
      rw [Subgroup.coe_pow]
      exact s12_mem_fixSpace_pow (mem_fixSpace.mp hv) n
    have h1 := finrank_commSpace_add_finrank_fixSpace (i : S.Qt ≃ₗ[ZMod 2] S.Qt)
    rw [hfix0, finrank_bot, add_zero, hidim, hV] at h1
    omega
  ·
    push Not at hcase
    obtain ⟨x, hx, hjI⟩ := hcase
    set j := x * i * x⁻¹ with hj
    have hjZ : j ∈ S.Z3Xbar12 g := hconjZ (Xbar12_le_Mbar hx) i hiZ
    have hij : i * j = j * i := commute_of_mem_Z3Xbar12 hiZ hjZ
    have hj3 : j ^ 3 = 1 := by rw [hj, conj_pow, hi3]; group
    have hjdim : finrank (ZMod 2) (commSpace (j : S.Qt ≃ₗ[ZMod 2] S.Qt)) = 4 := by
      rw [hj, Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, finrank_commSpace_conj, hidim]
    obtain ⟨c', hc', k', hk', hjeq, hc't, hk't⟩ :=
      s12_exists_decomp hZc hZodd htt (hconjZ htM) hjZ
    have hk'I : k' ∈ S.invZ12 g t := ⟨hk', hk't⟩
    have hc'C : c' ∈ S.centZ12 g t := hcent hc' hc't
    have hc'1 : c' ≠ 1 := by
      rintro rfl
      apply hjI
      rw [hjeq, one_mul]
      exact hk'I
    have hZform : ∀ y ∈ S.Z3Xbar12 g, ∃ p < 3, ∃ r < 3, y = j ^ p * i ^ r := by
      intro y hy
      obtain ⟨c, hc, k, hk, rfl, hct, hkt⟩ := s12_exists_decomp hZc hZodd htt (hconjZ htM) hy
      obtain ⟨p, hp, rfl⟩ : ∃ p < 3, c = c' ^ p := by
        rcases centZ12_eq_or haQ hne hn3 ht htA (hcent hc hct) hc'C hc'1 with h | h | h
        · exact ⟨0, by norm_num, by rw [h, pow_zero]⟩
        · exact ⟨1, by norm_num, by rw [h, pow_one]⟩
        · exact ⟨2, by norm_num, h⟩
      have hc'eq : c' = j * k'⁻¹ := by rw [hjeq]; group
      have hcomm : Commute j k'⁻¹ := commute_of_mem_Z3Xbar12 hjZ ((S.Z3Xbar12 g).inv_mem hk')
      have hmem : k'⁻¹ ^ p * k ∈ zpowers i := by
        rw [← hIeq]
        exact (S.invZ12 g t).mul_mem ((S.invZ12 g t).pow_mem ((S.invZ12 g t).inv_mem hk'I) p)
          ⟨hk, hkt⟩
      obtain ⟨n, hn⟩ := mem_powers_iff_mem_zpowers.mpr hmem
      replace hn : i ^ n = k'⁻¹ ^ p * k := hn
      refine ⟨p, hp, n % 3, Nat.mod_lt _ (by norm_num), ?_⟩
      rw [← hio, pow_mod_orderOf, hn, hc'eq, hcomm.mul_pow, mul_assoc]
    have hfixij : fixSpace (i : S.Qt ≃ₗ[ZMod 2] S.Qt) ⊓
        fixSpace (j : S.Qt ≃ₗ[ZMod 2] S.Qt) = ⊥ := by
      rw [eq_bot_iff]
      rintro v ⟨hvi, hvj⟩
      rw [Submodule.mem_bot]
      refine hF v fun y hy => ?_
      obtain ⟨p, -, r, -, rfl⟩ := hZform y hy
      rw [Subgroup.coe_mul, Subgroup.coe_pow, Subgroup.coe_pow, LinearEquiv.mul_apply,
        s12_mem_fixSpace_pow (mem_fixSpace.mp hvi), s12_mem_fixSpace_pow (mem_fixSpace.mp hvj)]
    have hij' : (i : S.Qt ≃ₗ[ZMod 2] S.Qt) * j = j * i := by
      rw [← Subgroup.coe_mul, ← Subgroup.coe_mul, hij]
    have hi3' : (i : S.Qt ≃ₗ[ZMod 2] S.Qt) ^ 3 = 1 := by rw [← Subgroup.coe_pow, hi3]; rfl
    have hj3' : (j : S.Qt ≃ₗ[ZMod 2] S.Qt) ^ 3 = 1 := by rw [← Subgroup.coe_pow, hj3]; rfl
    have hsup := s12_commSpace_sup_eq_top hij' hi3' hfixij
    have hle := Submodule.finrank_add_le_finrank_add_finrank
      (commSpace (i : S.Qt ≃ₗ[ZMod 2] S.Qt)) (commSpace (j : S.Qt ≃ₗ[ZMod 2] S.Qt))
    rw [hsup, finrank_top, hidim, hjdim, hV] at hle
    have hn4 : S.width = 4 := by omega
    have hV8 : finrank (ZMod 2) S.Qt = 8 := by rw [hV, hn4]
    obtain ⟨hinf, hfi, hfj⟩ := s12_decomp_of_commute hij' hfixij hsup
      (by rw [hidim, hjdim, hV8])
    have hfpf : ∀ a b : ℕ, (a = 1 ∨ a = 2) → (b = 1 ∨ b = 2) →
        fixSpace ((i : S.Qt ≃ₗ[ZMod 2] S.Qt) ^ a * (j : S.Qt ≃ₗ[ZMod 2] S.Qt) ^ b) = ⊥ :=
      fun a b ha hb => s12_fixSpace_mul_eq_bot hi3' hj3' hsup hinf hfi hfj ha hb
    have hfix_ne : fixSpace (i : S.Qt ≃ₗ[ZMod 2] S.Qt) ≠ ⊥ := by
      rw [hfi]
      intro h
      rw [h, finrank_bot] at hjdim
      omega
    have hEi : ∀ d ∈ S.Ebar12 g, d * i * d⁻¹ ∈ zpowers i := by
      intro d hd
      obtain ⟨p, hp, r, hr, hpr⟩ := hZform _ (hconjZ (Ebar12_subset_Mbar hd) i hiZ)
      exact s12_conj_mem_zpowers hij hi3 hj3 hfpf hfix_ne hV8 (isTypeA_of_mem_Ebar12 hd) hp hr
        hpr
    have hXN : S.Xbar12 g ≤ normalizer ((zpowers i : Subgroup S.O) : Set S.O) := by
      rw [Xbar12, closure_le]
      intro d hd
      have hdinv : d⁻¹ = d :=
        inv_eq_of_mul_eq_one_right (Subtype.ext (isTypeA_of_mem_Ebar12 hd).2.2.1)
      refine mem_normalizer_of_conj_le (fun y hy => ?_) (fun y hy => ?_)
      · obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hy
        rw [← conj_zpow]
        exact zpow_mem (hEi d hd) k
      · obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hy
        rw [← conj_zpow, hdinv]
        exact zpow_mem (hEi d hd) k
    have h1 := (mem_normalizer_iff.mp (hXN hx) i).mp (mem_zpowers i)
    rw [← hIeq] at h1
    exact hjI h1

end Setting

end CFSG.LargeExtraspecial
