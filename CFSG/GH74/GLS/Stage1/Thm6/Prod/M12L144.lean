module

public import CFSG.GH74.GLS.Stage1.Thm6.Prod.M12Ctx
public import CFSG.GH74.GLS.Stage1.Thm6.Prod.M12L144Fin
public import CFSG.GH74.GLS.Stage1.Thm6.Prod.M12L144Bar

public section

namespace CFSG.GH74.GLS.Stage1.Thm6.Prod

open Subgroup CFSG CFSG.GH74.GLS CFSG.GH74.GLS.Stage1.Thm6.M12Facts
  CFSG.GH74.GLS.Stage1.Thm6.Sec13 CFSG.GH74.GLS.Stage1.Thm6.Sec14 CFSG.GH74.GLS.Stage2.Local
open scoped commutatorElement

section L144

variable {G : Type} [Group G] {S T V : Subgroup G} {a b y x : G}

theorem exists_conj_U_to_z_comm (o : Out13 G x T V S a b y) {f : G} (hf3 : Is3Element f)
    (hf : f ∈ normalizer ((closure ({a, b} : Set G) : Subgroup G) : Set G)) (hfx : f * x = x * f)
    {v : G} (hv : v ∈ nfSub o.data pU closed_pU) (hfv : f * v * f⁻¹ ≠ v) {u : G}
    (hu : u ∈ nfSub o.data pU closed_pU) (hu1 : u ≠ 1) :
    ∃ n ∈ normalizer ((closure ({a, b} : Set G) : Subgroup G) : Set G),
      n * x = x * n ∧ n * u * n⁻¹ = a ^ 2 * b ^ 2 := by
  have h := o.data
  have hmoves := f_moves_z o hf3 hf hv hfv
  have hZ : a ^ 2 * b ^ 2 = nu a b y x zNF := zG_eq
  have hZU : nu a b y x zNF ∈ nfSub h pU closed_pU :=
    (nu_mem_nfSub h closed_pU _).2 (by decide)
  have hyN := mem_normalizer_H0 o (y_mem h)
  have hfinvN : f⁻¹ ∈ normalizer ((closure ({a, b} : Set G) : Subgroup G) : Set G) :=
    Subgroup.inv_mem _ hf
  have hcf : Commute f⁻¹ x := (show Commute f x from hfx).inv_left
  have hcy : Commute (f⁻¹ * y) x := hcf.mul_left (show Commute y x from h.hyx)
  have hy' : nu a b y x yNF = y := by simp [nu, yNF]
  have swapA : y * nu a b y x (2, 0, 0, 0) * y⁻¹ = nu a b y x (0, 2, 0, 0) := by
    calc y * nu a b y x (2, 0, 0, 0) * y⁻¹
        = nu a b y x yNF * nu a b y x (2, 0, 0, 0) * (nu a b y x yNF)⁻¹ := by rw [hy']
      _ = nu a b y x (nfMul (nfMul yNF (2, 0, 0, 0)) (nfInv yNF)) := by
        rw [nu_inv h, nu_mul h, nu_mul h]
      _ = _ := by rw [U_swap_a]
  have swapB : y * nu a b y x (0, 2, 0, 0) * y⁻¹ = nu a b y x (2, 0, 0, 0) := by
    calc y * nu a b y x (0, 2, 0, 0) * y⁻¹
        = nu a b y x yNF * nu a b y x (0, 2, 0, 0) * (nu a b y x yNF)⁻¹ := by rw [hy']
      _ = nu a b y x (nfMul (nfMul yNF (0, 2, 0, 0)) (nfInv yNF)) := by
        rw [nu_inv h, nu_mul h, nu_mul h]
      _ = _ := by rw [U_swap_b]
  obtain ⟨pw, hpw, hwdef⟩ := f_norm_U o hf hZU
  have hwZ : f * nu a b y x zNF * f⁻¹ = nu a b y x pw := hwdef
  have hpwAB : pw = (2, 0, 0, 0) ∨ pw = (0, 2, 0, 0) := by
    rcases pU_cases pw hpw with rfl | rfl | h1 | h2
    · exfalso
      apply z_ne_one h
      have e : f * nu a b y x zNF * f⁻¹ = 1 := by rw [hwZ, nu_zero]
      rw [hZ]
      exact conj_inj_aux (f := f) (u := nu a b y x zNF) (w := 1) (by rw [e]; group)
    · exfalso
      apply hmoves
      rw [hZ]; exact hwZ
    · exact Or.inl h1
    · exact Or.inr h2
  obtain ⟨pu, hpu, rfl⟩ := hu
  rcases pU_cases pu hpu with rfl | rfl | rfl | rfl
  · exact absurd nu_zero hu1
  · exact ⟨1, one_mem _, by rw [one_mul, mul_one], by rw [hZ]; group⟩
  · rcases hpwAB with rfl | rfl
    · refine ⟨f⁻¹, hfinvN, hcf.eq, ?_⟩
      calc f⁻¹ * nu a b y x (2, 0, 0, 0) * f⁻¹⁻¹
          = f⁻¹ * (f * nu a b y x zNF * f⁻¹) * f := by rw [hwZ]; simp
        _ = a ^ 2 * b ^ 2 := by rw [hZ]; group
    · refine ⟨f⁻¹ * y, Subgroup.mul_mem _ hfinvN hyN, hcy.eq, ?_⟩
      calc f⁻¹ * y * nu a b y x (2, 0, 0, 0) * (f⁻¹ * y)⁻¹
          = f⁻¹ * (y * nu a b y x (2, 0, 0, 0) * y⁻¹) * f := by group
        _ = f⁻¹ * (f * nu a b y x zNF * f⁻¹) * f := by rw [swapA, hwZ]
        _ = a ^ 2 * b ^ 2 := by rw [hZ]; group
  · rcases hpwAB with rfl | rfl
    · refine ⟨f⁻¹ * y, Subgroup.mul_mem _ hfinvN hyN, hcy.eq, ?_⟩
      calc f⁻¹ * y * nu a b y x (0, 2, 0, 0) * (f⁻¹ * y)⁻¹
          = f⁻¹ * (y * nu a b y x (0, 2, 0, 0) * y⁻¹) * f := by group
        _ = f⁻¹ * (f * nu a b y x zNF * f⁻¹) * f := by rw [swapB, hwZ]
        _ = a ^ 2 * b ^ 2 := by rw [hZ]; group
    · refine ⟨f⁻¹, hfinvN, hcf.eq, ?_⟩
      calc f⁻¹ * nu a b y x (0, 2, 0, 0) * f⁻¹⁻¹
          = f⁻¹ * (f * nu a b y x zNF * f⁻¹) * f := by rw [hwZ]; simp
        _ = a ^ 2 * b ^ 2 := by rw [hZ]; group

theorem exists_zc_conj (o : Out13 G x T V S a b y) (i j : Fin 4)
    (hij : ¬ (i.val % 2 = 0 ∧ j.val % 2 = 0)) :
    ∃ p : NF, pZc p ∧ IsConj (nu a b y x (i, j, 0, 1)) (nu a b y x p) := by
  have h := o.data
  obtain ⟨f, hf3, hfN, hfx, v, hv, hfv⟩ := o.f3
  have hvU : v ∈ nfSub h pU closed_pU := by rw [← U_eq h, ← o.V_eq]; exact hv
  have hwU : nu a b y x (nfMul (i, j, 0, 0) (i, j, 0, 0)) ∈ nfSub h pU closed_pU :=
    (nu_mem_nfSub h closed_pU _).2 (pU_sq_H0 i j)
  have hw1 : nu a b y x (nfMul (i, j, 0, 0) (i, j, 0, 0)) ≠ 1 := by
    intro e
    rw [← nu_zero (a := a) (b := b) (y := y) (x := x)] at e
    exact sq_ne_zero i j hij (nu_injective h e)
  obtain ⟨n, hnN, hnx, hn⟩ := exists_conj_U_to_z_comm o hf3 hfN hfx hvU hfv hwU hw1
  have hH0 : nu a b y x (i, j, 0, 0) ∈ (closure ({a, b} : Set G) : Subgroup G) := by
    rw [H0_eq h]; exact (nu_mem_nfSub h closed_pH0 _).2 (pH0_ij i j)
  have hnH : n * nu a b y x (i, j, 0, 0) * n⁻¹ ∈ (closure ({a, b} : Set G) : Subgroup G) :=
    (Subgroup.mem_normalizer_iff.1 hnN _).1 hH0
  rw [H0_eq h] at hnH
  obtain ⟨q, hq, hqe⟩ := hnH
  have hqq : nfMul q q = zNF := by
    apply nu_injective h
    have h1 : nu a b y x q * nu a b y x q =
        n * nu a b y x (nfMul (i, j, 0, 0) (i, j, 0, 0)) * n⁻¹ := by
      rw [← hqe, ← nu_mul h (i, j, 0, 0) (i, j, 0, 0)]
      group
    rw [← nu_mul h, h1, hn]
    exact zG_eq
  obtain ⟨hqi, hqj⟩ := sq_eq_zNF_odd q hq hqq
  refine ⟨nfMul q xNF, pZc_mul_x q hq hqi hqj, isConj_iff.2 ⟨n, ?_⟩⟩
  have hx' : nu a b y x xNF = x := by simp [nu, xNF]
  have e1 : nu a b y x (i, j, 0, 1) = nu a b y x (i, j, 0, 0) * x := by
    calc nu a b y x (i, j, 0, 1) = nu a b y x (nfMul (i, j, 0, 0) xNF) := by rw [mul_x_eq]
      _ = nu a b y x (i, j, 0, 0) * nu a b y x xNF := (nu_mul h _ _).symm
      _ = nu a b y x (i, j, 0, 0) * x := by rw [hx']
  have e2 : n * x * n⁻¹ = x := by rw [hnx]; group
  have e3 : nu a b y x (nfMul q xNF) = nu a b y x q * x := by rw [← nu_mul h, hx']
  rw [e3, e1]
  calc n * (nu a b y x (i, j, 0, 0) * x) * n⁻¹
      = (n * nu a b y x (i, j, 0, 0) * n⁻¹) * (n * x * n⁻¹) := by group
    _ = nu a b y x q * x := by rw [hqe, e2]

end L144

section L144Bar

open CFSG.GH74.GLS.Stage1.Thm6.Sec14.Rn

variable {G : Type} [Group G] [Finite G] {S T V : Subgroup G} {a b y x : G}

theorem exists_odd_conj_z (h91 : IVK_9_1) (hK : IsKProperSimple G) (o : Out13 G x T V S a b y) :
    ∃ p : NF, pZc p ∧ IsConj (a ^ 2 * b ^ 2) (nu a b y x p) := by
  have h := o.data
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨S', a', b', y', x', hb⟩ := exists_barImg h91 hK o
  have hd := hb.data
  have hcen : ∀ g : CentralizerBar (a ^ 2 * b ^ 2),
      g * (a' ^ 2 * b' ^ 2) = (a' ^ 2 * b' ^ 2) * g := by
    intro g; rw [hb.hz]; exact zBar_central _ g
  have hRn : (Rsub S' a' b').Normal := normal_of_conc hcen hb.conc.R_normal
  have cfg := barCfg_of_conc hb.data hb.sylow hcen hb.conc
  obtain ⟨X⟩ : Nonempty (Sylow 3 (CentralizerBar (a ^ 2 * b ^ 2))) := inferInstance
  obtain ⟨x₀, -, hXgen, hx₀3⟩ := exists_gen_card_three (cfg.sylow3_card X)
  obtain ⟨g, hg⟩ := toBar_surj (a ^ 2 * b ^ 2) x₀
  have hR' : Rsub S' a' b' = nfSub hd pR closed_pR := R_eq hd
  have he_mem : nu a' b' y' x' (2, 0, 0, 0) ∈ Rsub S' a' b' := by
    rw [hR']; exact (nu_mem_nfSub hd closed_pR _).2 pR_a2
  have hzz : a' ^ 2 * b' ^ 2 = nu a' b' y' x' zNF := zG_eq
  have hez : nu a' b' y' x' (2, 0, 0, 0) ∉ zpowers (a' ^ 2 * b' ^ 2) := by
    rw [mem_zpowers_involution (z_sq hd), hzz]
    rintro (e | e)
    · rw [← nu_zero (a := a') (b := b') (y := y') (x := x')] at e
      exact a2_ne_one (nu_injective hd e)
    · exact a2_ne_z (nu_injective hd e)
  have hfree := cfg.free_mod_z X hXgen hx₀3 he_mem hez
  have hconj : x₀ * nu a' b' y' x' (2, 0, 0, 0) * x₀⁻¹ ∈ Rsub S' a' b' :=
    hRn.conj_mem _ he_mem x₀
  rw [hR'] at hconj
  obtain ⟨p, hpR, hpe⟩ := hconj
  have he2 : nu a' b' y' x' (2, 0, 0, 0) * nu a' b' y' x' (2, 0, 0, 0) = 1 := by
    rw [nu_mul hd, a2_mul_a2', nu_zero]
  have hsq' : nu a' b' y' x' p * nu a' b' y' x' p = 1 := by
    rw [← hpe]
    calc x₀ * nu a' b' y' x' (2, 0, 0, 0) * x₀⁻¹ * (x₀ * nu a' b' y' x' (2, 0, 0, 0) * x₀⁻¹)
        = x₀ * (nu a' b' y' x' (2, 0, 0, 0) * nu a' b' y' x' (2, 0, 0, 0)) * x₀⁻¹ := by group
      _ = 1 := by rw [he2]; group
  have hsq : nfMul p p = (0, 0, 0, 0) := by
    apply nu_injective hd
    rw [← nu_mul hd, hsq', nu_zero]
  have hp0 : p ≠ (0, 0, 0, 0) := by
    rintro rfl
    rw [nu_zero] at hpe
    have h1 : nu a' b' y' x' (2, 0, 0, 0) = 1 := by
      calc nu a' b' y' x' (2, 0, 0, 0)
          = x₀⁻¹ * (x₀ * nu a' b' y' x' (2, 0, 0, 0) * x₀⁻¹) * x₀ := by group
        _ = 1 := by rw [hpe]; group
    rw [← nu_zero (a := a') (b := b') (y := y') (x := x')] at h1
    exact a2_ne_one (nu_injective hd h1)
  have hpz : p ≠ zNF := by
    rintro rfl
    rw [← hzz] at hpe
    have h1 : nu a' b' y' x' (2, 0, 0, 0) = a' ^ 2 * b' ^ 2 := by
      calc nu a' b' y' x' (2, 0, 0, 0)
          = x₀⁻¹ * (x₀ * nu a' b' y' x' (2, 0, 0, 0) * x₀⁻¹) * x₀ := by group
        _ = x₀⁻¹ * (a' ^ 2 * b' ^ 2) * x₀ := by rw [hpe]
        _ = (a' ^ 2 * b' ^ 2) * x₀⁻¹ * x₀ := by rw [hcen x₀⁻¹]
        _ = a' ^ 2 * b' ^ 2 := by group
    rw [hzz] at h1
    exact a2_ne_z (nu_injective hd h1)
  have hp1 : p ≠ (2, 0, 0, 0) := by
    rintro rfl
    apply hfree
    rw [hpe, inv_mul_cancel]
    exact one_mem _
  have hp2 : p ≠ (0, 2, 0, 0) := by
    rintro rfl
    apply hfree
    rw [hpe, nu_inv hd, nu_mul hd, nfInv_a2, a2_mul_a2, ← hzz]
    exact mem_zpowers _
  have hsplit := inv_R_split p ⟨hpR, hsq, hp0, hpz, hp1, hp2⟩
  have hNcop : Nat.Coprime 2 (Nat.card (CFSG.pPrimeCore 2 ↥(Cen (a ^ 2 * b ^ 2)))) :=
    CFSG.pPrimeCore_coprime_card
  have hu0 : νC h (2, 0, 0, 0) * νC h (2, 0, 0, 0) = 1 := by
    rw [νC_mul h, a2_mul_a2', νC_zero h]
  have hu1 : νC h p * νC h p = 1 := by rw [νC_mul h, hsq, νC_zero h]
  have huu : (g * νC h (2, 0, 0, 0) * g⁻¹) * (g * νC h (2, 0, 0, 0) * g⁻¹) = 1 := by
    calc _ = g * (νC h (2, 0, 0, 0) * νC h (2, 0, 0, 0)) * g⁻¹ := by group
      _ = 1 := by rw [hu0]; group
  have hπ : QuotientGroup.mk' (CFSG.pPrimeCore 2 ↥(Cen (a ^ 2 * b ^ 2)))
      (g * νC h (2, 0, 0, 0) * g⁻¹) =
      QuotientGroup.mk' (CFSG.pPrimeCore 2 ↥(Cen (a ^ 2 * b ^ 2))) (νC h p) := by
    show toBar (a ^ 2 * b ^ 2) (g * νC h (2, 0, 0, 0) * g⁻¹) = toBar (a ^ 2 * b ^ 2) (νC h p)
    rw [map_mul, map_mul, map_inv, hg, hb.hnu, hb.hnu, hpe]
  obtain ⟨n, -, hnuv⟩ :=
    involutions_conj_of_coset (CFSG.pPrimeCore 2 ↥(Cen (a ^ 2 * b ^ 2))) hNcop huu hu1 hπ
  have ha2 : nu a b y x (2, 0, 0, 0) = a ^ 2 := by simp [nu]
  have hconjA2 : IsConj (a ^ 2) (nu a b y x p) := by
    refine isConj_iff.2 ⟨((n * g : ↥(Cen (a ^ 2 * b ^ 2))) : G), ?_⟩
    have hval := congrArg Subtype.val hnuv
    have e1 : ((n * (g * νC h (2, 0, 0, 0) * g⁻¹) * n⁻¹ : ↥(Cen (a ^ 2 * b ^ 2))) : G) =
        ((n * g : ↥(Cen (a ^ 2 * b ^ 2))) : G) * nu a b y x (2, 0, 0, 0) *
          ((n * g : ↥(Cen (a ^ 2 * b ^ 2))) : G)⁻¹ := by
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, νC_val]
      group
    rw [e1, ha2] at hval
    exact hval
  rcases hsplit with hX | hZ
  ·
    exfalso
    obtain ⟨q, hq⟩ := hX
    have key : ∀ (w : NF) (c : G), nu a b y x w = c → nfMul (nfMul q w) (nfInv q) = p →
        IsConj c (nu a b y x p) := by
      intro w c hwc hq'
      refine isConj_iff.2 ⟨nu a b y x q, ?_⟩
      rw [← hq', ← nu_mul h, ← nu_mul h, nu_inv h, hwc]
    have hxc : IsConj x (nu a b y x p) := by
      rcases hq with hq | hq | hq
      · exact key xNF x (by simp [nu, xNF]) hq
      · obtain ⟨g₀, hg₀⟩ := o.y_conj
        exact (isConj_iff.2 ⟨g₀, hg₀.symm⟩ : IsConj x y).trans (key yNF y (by simp [nu, yNF]) hq)
      · obtain ⟨g₀, hg₀⟩ := x_conj_yx o
        exact (isConj_iff.2 ⟨g₀, hg₀⟩ : IsConj x (y * x)).trans
          (key xyNF (y * x) (by simp [nu, xyNF]) hq)
    obtain ⟨c, hc⟩ := isConj_iff.1 (hxc.trans hconjA2.symm)
    refine o.fusion c ?_
    rw [hc]
    exact pow_mem (Subgroup.subset_closure (by simp)) 2
  ·
    refine ⟨p, hZ, ?_⟩
    obtain ⟨f, hf3, hfN, -, v, hv, hfv⟩ := o.f3
    have hvU : v ∈ nfSub h pU closed_pU := by rw [← U_eq h, ← o.V_eq]; exact hv
    have hu : nu a b y x (2, 0, 0, 0) ∈ nfSub h pU closed_pU :=
      (nu_mem_nfSub h closed_pU _).2 pU_a2
    have hu1' : nu a b y x (2, 0, 0, 0) ≠ 1 := by
      intro e
      rw [← nu_zero (a := a) (b := b) (y := y) (x := x)] at e
      exact a2_ne_one (nu_injective h e)
    obtain ⟨m, -, hm⟩ := exists_conj_U_to_z o hf3 hfN hvU hfv hu hu1'
    have hcz : IsConj (a ^ 2 * b ^ 2) (a ^ 2) := by
      refine isConj_iff.2 ⟨m⁻¹, ?_⟩
      calc m⁻¹ * (a ^ 2 * b ^ 2) * m⁻¹⁻¹
          = m⁻¹ * (m * nu a b y x (2, 0, 0, 0) * m⁻¹) * m⁻¹⁻¹ := by rw [hm]
        _ = nu a b y x (2, 0, 0, 0) := by group
        _ = a ^ 2 := ha2
    exact hcz.trans hconjA2

theorem lemma14_4 (h91 : IVK_9_1) : Lemma14_4 := by
  intro G _ _ hStd x T V S a b y o i j hij
  have h := o.data
  obtain ⟨p₁, hp₁, hz₁⟩ := exists_odd_conj_z h91 hStd.kps o
  obtain ⟨p₂, hp₂, hc₂⟩ := exists_zc_conj o i j hij
  obtain ⟨r, -, hrq⟩ := zc_conj p₂ p₁ hp₂ hp₁
  have h3 : IsConj (nu a b y x p₂) (nu a b y x p₁) :=
    isConj_iff.2 ⟨nu a b y x r, by rw [nu_inv h, nu_mul h, nu_mul h, hrq]⟩
  exact hz₁.trans (hc₂.trans h3).symm

end L144Bar

end CFSG.GH74.GLS.Stage1.Thm6.Prod
