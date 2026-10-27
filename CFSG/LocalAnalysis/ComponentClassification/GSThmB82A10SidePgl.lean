module

public import CFSG.LocalAnalysis.ComponentClassification.GSThmB82A10SideA6
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedLayerUnbalancingTriple
import CFSG.ThirdParty.QiuzhenCFSG.Theory.AutAlternating

public section

namespace CFSG.ComponentClassification.GSThmB.A10Side

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer

variable {G : Type} [Group G] [Finite G]

private theorem mem_normalizer_of_conj_mem {K : Subgroup G} {g : G}
    (h1 : ∀ x ∈ K, g * x * g⁻¹ ∈ K) : g ∈ normalizer (K : Set G) := by
  have hle : K.map (MulAut.conj g).toMonoidHom ≤ K := by
    rintro _ ⟨x, hx, rfl⟩
    exact h1 x hx
  have heq : K.map (MulAut.conj g).toMonoidHom = K :=
    eq_of_le_of_card_ge hle (by rw [card_map_of_injective (MulAut.conj g).injective])
  rw [mem_normalizer_iff]
  intro x
  refine ⟨h1 x, fun hx => ?_⟩
  rw [← heq] at hx
  obtain ⟨y, hy, hyx⟩ := hx
  have : y = x := by
    have h2 : g * y * g⁻¹ = g * x * g⁻¹ := hyx
    simpa using h2
  exact this ▸ hy

omit [Finite G] in
theorem congr_conj {Q Q' : Type*} [Group Q] [Group Q'] (e : Q ≃* Q') (q : Q) :
    MulAut.congr e (MulAut.conj q) = MulAut.conj (e q) := by
  ext y
  change e (q * e.symm y * q⁻¹) = e q * y * (e q)⁻¹
  rw [map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply]

section Action

omit [Finite G]

private noncomputable def barAut (Y : Type*) [Group Y] :
    MulAut Y →* MulAut (Y ⧸ pPrimeCore 2 Y) where
  toFun φ := QuotientGroup.congr (pPrimeCore 2 Y) (pPrimeCore 2 Y) φ (pPrimeCore_map_iso 2 φ)
  map_one' := by
    ext y
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective y
    rfl
  map_mul' φ ψ := by
    ext y
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective y
    rfl

private noncomputable def barAct (J : Subgroup G) :
    normalizer (J : Set G) →* MulAut (↥J ⧸ pPrimeCore 2 ↥J) :=
  (barAut ↥J).comp J.normalizerMonoidHom

private theorem barAct_apply_mk (J : Subgroup G) (g : normalizer (J : Set G)) (l : ↥J) :
    barAct J g (l : ↥J ⧸ pPrimeCore 2 ↥J) =
      ((⟨(g : G) * l * (g : G)⁻¹, (mem_normalizer_iff.mp g.2 l).mp l.2⟩ : ↥J) :
        ↥J ⧸ pPrimeCore 2 ↥J) := rfl

private theorem barAct_of_mem (J : Subgroup G) (l : ↥J) :
    barAct J ⟨l, le_normalizer l.2⟩ = MulAut.conj (l : ↥J ⧸ pPrimeCore 2 ↥J) := by
  ext y
  obtain ⟨m, rfl⟩ := QuotientGroup.mk_surjective y
  rw [barAct_apply_mk, MulAut.conj_apply]
  rfl

end Action

private theorem exists_fixed_lift {X : Type} [Group X] [Finite X] (β : MulAut X)
    (hβ : ∀ y, β (β y) = y) {N : Subgroup X} (hN : ∀ n ∈ N, β n ∈ N) (hodd : Odd (Nat.card N))
    (x : X) (hx : x⁻¹ * β x ∈ N) : ∃ y : X, β y = y ∧ x⁻¹ * y ∈ N := by
  classical
  have : Fintype X := Fintype.ofFinite X
  have hmapS : ∀ y : X, x⁻¹ * y ∈ N → x⁻¹ * β y ∈ N := by
    intro y hy
    have h1 : β (x⁻¹ * y) ∈ N := hN _ hy
    rw [map_mul, map_inv] at h1
    have h2 : x⁻¹ * β y = (x⁻¹ * β x) * ((β x)⁻¹ * β y) := by group
    rw [h2]
    exact N.mul_mem hx h1
  let σ : Equiv.Perm {y : X // x⁻¹ * y ∈ N} :=
    { toFun := fun y => ⟨β y.1, hmapS y.1 y.2⟩
      invFun := fun y => ⟨β y.1, hmapS y.1 y.2⟩
      left_inv := fun y => Subtype.ext (hβ y.1)
      right_inv := fun y => Subtype.ext (hβ y.1) }
  have hσ2 : σ ^ 2 ^ 1 = 1 := by
    rw [pow_one, pow_two]
    ext y
    exact hβ y.1
  have hS : Fintype.card {y : X // x⁻¹ * y ∈ N} = Nat.card N := by
    rw [← Nat.card_eq_fintype_card]
    exact Nat.card_congr
      { toFun := fun y => ⟨x⁻¹ * y.1, y.2⟩
        invFun := fun n => ⟨x * n.1, by simp [n.2]⟩
        left_inv := fun y => Subtype.ext (by simp)
        right_inv := fun n => Subtype.ext (by simp) }
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hmod := Equiv.Perm.card_compl_support_modEq (p := 2) (n := 1) hσ2
  rw [hS] at hmod
  obtain ⟨y, hy⟩ : σ.supportᶜ.Nonempty := by
    rw [← Finset.card_pos]
    by_contra h0
    have h0' : σ.supportᶜ.card = 0 := by omega
    rw [h0'] at hmod
    obtain ⟨k, hk⟩ := hodd
    unfold Nat.ModEq at hmod
    omega
  rw [Finset.mem_compl, Equiv.Perm.mem_support, not_not] at hy
  exact ⟨y.1, congrArg Subtype.val hy, y.2⟩

private theorem exists_commute_lift {J : Subgroup G} {w : G} (hw : w ∈ normalizer (J : Set G))
    (hw2 : w * w = 1) {q : ↥J ⧸ pPrimeCore 2 ↥J}
    (hq : barAct J ⟨w, hw⟩ q = q) :
    ∃ y : ↥J, (y : G) * w = w * y ∧ (y : ↥J ⧸ pPrimeCore 2 ↥J) = q := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set β : MulAut ↥J := J.normalizerMonoidHom ⟨w, hw⟩ with hβ
  have hβapp : ∀ y : ↥J, ((β y : ↥J) : G) = w * y * w⁻¹ := fun y => rfl
  have hwinv : w⁻¹ = w := inv_eq_of_mul_eq_one_right hw2
  have hββ : ∀ y, β (β y) = y := by
    intro y
    apply Subtype.ext
    rw [hβapp, hβapp, hwinv]
    calc w * (w * (y : G) * w) * w = (w * w) * y * (w * w) := by group
      _ = y := by rw [hw2, one_mul, mul_one]
  have hN : ∀ n ∈ pPrimeCore 2 ↥J, β n ∈ pPrimeCore 2 ↥J := by
    intro n hn
    have h := pPrimeCore_map_iso (G := ↥J) (G' := ↥J) 2 β
    rw [← h]
    exact mem_map_of_mem _ hn
  have hodd : Odd (Nat.card (pPrimeCore 2 ↥J)) :=
    Nat.coprime_two_left.mp pPrimeCore_coprime_card
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective q
  have hx : x⁻¹ * β x ∈ pPrimeCore 2 ↥J := by
    have h1 : ((β x : ↥J) : ↥J ⧸ pPrimeCore 2 ↥J) = (x : ↥J ⧸ pPrimeCore 2 ↥J) := hq
    exact QuotientGroup.eq.mp h1.symm
  obtain ⟨y, hy, hxy⟩ := exists_fixed_lift β hββ hN hodd x hx
  refine ⟨y, ?_, (QuotientGroup.eq.mpr hxy).symm⟩
  have h2 : w * (y : G) * w⁻¹ = y := by rw [← hβapp, hy]
  calc (y : G) * w = w * y * w⁻¹ * w := by rw [h2]
    _ = w * y := by group

theorem not_isSymSixType_of_odd {J : Subgroup G}
    (e : ↥J ⧸ pPrimeCore 2 ↥J ≃* alternatingGroup (Fin 6))
    {w : G} (hw : w ∈ normalizer (J : Set G)) (hw2 : w * w = 1)
    {D : Subgroup G} (hDN : D ≤ normalizer (J : Set G)) (hDodd : Odd (Nat.card D))
    (hDw : ∀ d ∈ D, d * w = w * d)
    (hDJ : ∀ j ∈ J, j * w = w * j → ∀ d ∈ D, j * d * j⁻¹ ∈ D)
    (hD1 : ∃ d ∈ D, ∃ j ∈ J, j⁻¹ * d⁻¹ * j * d ∉ (pPrimeCore 2 ↥J).map J.subtype)
    (φ : MulAut (↥J ⧸ pPrimeCore 2 ↥J))
    (hφ : ∀ j : ↥J, φ (j : ↥J ⧸ pPrimeCore 2 ↥J) =
      ((⟨w * j * w⁻¹, (mem_normalizer_iff.mp hw j).mp j.2⟩ : ↥J) : ↥J ⧸ pPrimeCore 2 ↥J)) :
    ¬ IsSymSixType e φ := by
  rintro ⟨σ, hσ⟩
  have hφw : φ = barAct J ⟨w, hw⟩ := by
    ext q
    obtain ⟨l, rfl⟩ := QuotientGroup.mk_surjective q
    rw [hφ, barAct_apply_mk]
  subst hφw
  set ψ : normalizer (J : Set G) →* MulAut (alternatingGroup (Fin 6)) :=
    (MulAut.congr e).toMonoidHom.comp (barAct J) with hψ
  have hψw : ψ ⟨w, hw⟩ = MulAut.conjNormal σ := hσ
  set R := (D.subgroupOf (normalizer (J : Set G))).map ψ with hR
  have hσ2 : σ * σ = 1 := by
    apply CFSG.GroupTheory.AutAlternating.conjNormal_injective_alternatingGroup 6 (by norm_num)
    rw [map_mul, ← hψw, ← map_mul, map_one]
    have : (⟨w, hw⟩ : normalizer (J : Set G)) * ⟨w, hw⟩ = 1 := Subtype.ext hw2
    rw [this, map_one]
  have hRmem : ∀ φ ∈ R, ∃ d, ∃ hd : d ∈ D, φ = ψ ⟨d, hDN hd⟩ := by
    rintro _ ⟨⟨d, hdN⟩, hd, rfl⟩
    exact ⟨d, mem_subgroupOf.mp hd, rfl⟩
  have hψmem : ∀ d (hd : d ∈ D), ψ ⟨d, hDN hd⟩ ∈ R := fun d hd =>
    mem_map_of_mem _ (mem_subgroupOf.mpr hd)
  have hRbot : R = ⊥ := by
    apply eq_bot_of_commute_conjNormal hσ2 R
    · intro φ hφ
      obtain ⟨d, hd, rfl⟩ := hRmem φ hφ
      have h1 : orderOf (ψ ⟨d, hDN hd⟩) ∣ orderOf (⟨d, hDN hd⟩ : normalizer (J : Set G)) :=
        orderOf_map_dvd _ _
      have h2 : orderOf (⟨d, hDN hd⟩ : normalizer (J : Set G)) = orderOf (⟨d, hd⟩ : D) := by
        rw [Subgroup.orderOf_mk, Subgroup.orderOf_mk]
      have h3 : orderOf (⟨d, hd⟩ : D) ∣ Nat.card D := orderOf_dvd_natCard _
      exact Odd.of_dvd_nat hDodd (h1.trans (h2 ▸ h3))
    · intro φ hφ
      obtain ⟨d, hd, rfl⟩ := hRmem φ hφ
      rw [← hψw, ← map_mul, ← map_mul]
      congr 1
      exact Subtype.ext (hDw d hd)
    · intro c hc φ hφ
      obtain ⟨d, hd, rfl⟩ := hRmem φ hφ
      have hfix : barAct J ⟨w, hw⟩ (e.symm c) = e.symm c := by
        apply e.injective
        have h1 := congrArg (fun φ : MulAut (alternatingGroup (Fin 6)) => φ c) hψw
        change e (barAct J ⟨w, hw⟩ (e.symm c)) = MulAut.conjNormal σ c at h1
        rw [h1, MulEquiv.apply_symm_apply]
        apply Subtype.ext
        rw [MulAut.conjNormal_apply, ← hc, mul_inv_cancel_right]
      obtain ⟨y, hyw, hyc⟩ := exists_commute_lift hw hw2 hfix
      have hψy : ψ ⟨(y : G), le_normalizer y.2⟩ = MulAut.conj c := by
        change MulAut.congr e (barAct J ⟨(y : G), le_normalizer y.2⟩) = _
        rw [barAct_of_mem J y, congr_conj, hyc, MulEquiv.apply_symm_apply]
      have hmem := hψmem _ (hDJ y y.2 hyw d hd)
      rw [← hψy]
      convert hmem using 1
      rw [← map_inv, ← map_mul, ← map_mul]
      congr 1
  obtain ⟨d₀, hd₀, j₀, hj₀, hnot⟩ := hD1
  apply hnot
  have h := hψmem d₀ hd₀
  rw [hRbot, mem_bot] at h
  have h1 : barAct J ⟨d₀, hDN hd₀⟩ = 1 := (MulAut.congr e).injective (h.trans (map_one _).symm)
  have hdinv : d₀⁻¹ ∈ normalizer (J : Set G) := inv_mem (hDN hd₀)
  have hj' : d₀⁻¹ * j₀ * d₀ ∈ J := by
    have := (mem_normalizer_iff.mp hdinv j₀).mp hj₀
    rwa [inv_inv] at this
  have h2 := congrArg (fun φ : MulAut (↥J ⧸ pPrimeCore 2 ↥J) =>
    φ ((⟨d₀⁻¹ * j₀ * d₀, hj'⟩ : ↥J) : ↥J ⧸ pPrimeCore 2 ↥J)) h1
  simp only [MulAut.one_apply] at h2
  rw [barAct_apply_mk] at h2
  have h3 := QuotientGroup.eq.mp h2
  refine ⟨_, h3, ?_⟩
  simp only [Subgroup.coe_subtype, coe_mul, coe_inv]
  group

theorem mem_normalizer_of_unbalancing {a w : G} {J : Subgroup G}
    (h : GSUnbalancingTriple a w J) : w ∈ normalizer (J : Set G) := by
  obtain ⟨-, hw2, -, -, -, hJw, -⟩ := h
  have hwinv : w⁻¹ = w := by
    have h1 : w ^ 2 = 1 := hw2 ▸ pow_orderOf_eq_one w
    exact inv_eq_of_mul_eq_one_right (by rw [← sq, h1])
  apply mem_normalizer_of_conj_mem
  intro j hj
  have h1 : j⁻¹ * w⁻¹ * j * w ∈ J := by
    rw [← hJw]
    exact subset_closure ⟨j, hj, rfl⟩
  have h2 : w * j * w⁻¹ = j * (j⁻¹ * w⁻¹ * j * w) := by
    rw [hwinv]
    group
  rw [h2]
  exact mul_mem hj h1

theorem not_isSymSixType_of_unbalancing {a w : G}
    {J : Subgroup G} (h : GSUnbalancingTriple a w J)
    (e : ↥J ⧸ pPrimeCore 2 ↥J ≃* alternatingGroup (Fin 6)) (φ : MulAut (↥J ⧸ pPrimeCore 2 ↥J))
    (hφ : ∀ j : ↥J, φ (j : ↥J ⧸ pPrimeCore 2 ↥J) =
      ((⟨w * j * w⁻¹, (mem_normalizer_iff.mp (mem_normalizer_of_unbalancing h) j).mp j.2⟩ :
        ↥J) : ↥J ⧸ pPrimeCore 2 ↥J)) :
    ¬ IsSymSixType e φ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hwN := mem_normalizer_of_unbalancing h
  have hw2 : orderOf w = 2 := h.2.1
  have hJC : J ≤ centralizer ({a} : Set G) := h.2.2.2.1
  have hJD := h.2.2.2.2.2.2
  have hww : w * w = 1 := by rw [← sq, ← hw2, pow_orderOf_eq_one]
  set C := centralizer ({w} : Set G) with hC
  set D := (pPrimeCore 2 ↥C).map C.subtype ⊓ centralizer ({a} : Set G) with hD
  have hcomm : ∀ j ∈ J, ∀ d ∈ D, j⁻¹ * d⁻¹ * j * d ∈ J := by
    intro j hj d hd
    rw [← hJD]
    exact subset_closure ⟨j, hj, d, hd, rfl⟩
  have hDN : D ≤ normalizer (J : Set G) := by
    intro d hd
    have h1 : d⁻¹ ∈ normalizer (J : Set G) := by
      apply mem_normalizer_of_conj_mem
      intro j hj
      rw [inv_inv]
      have h2 : d⁻¹ * j * d = j * (j⁻¹ * d⁻¹ * j * d) := by group
      rw [h2]
      exact mul_mem hj (hcomm j hj d hd)
    simpa using inv_mem h1
  have hDodd : Odd (Nat.card D) := by
    have h1 : Nat.card D ∣ Nat.card ((pPrimeCore 2 ↥C).map C.subtype) :=
      card_dvd_of_le inf_le_left
    rw [card_map_of_injective C.subtype_injective] at h1
    exact Odd.of_dvd_nat (Nat.coprime_two_left.mp pPrimeCore_coprime_card) h1
  have hDw : ∀ d ∈ D, d * w = w * d := by
    intro d hd
    obtain ⟨d', -, rfl⟩ := (mem_inf.mp hd).1
    exact mem_centralizer_singleton_iff.mp d'.2
  have hDJ : ∀ j ∈ J, j * w = w * j → ∀ d ∈ D, j * d * j⁻¹ ∈ D := by
    intro j hj hjw d hd
    obtain ⟨⟨d', hd'O, rfl⟩, hda⟩ := mem_inf.mp hd
    refine mem_inf.mpr ⟨?_, ?_⟩
    · have hjC : j ∈ C := mem_centralizer_singleton_iff.mpr hjw
      refine ⟨⟨j, hjC⟩ * d' * ⟨j, hjC⟩⁻¹, ?_, rfl⟩
      exact (inferInstance : (pPrimeCore 2 ↥C).Normal).conj_mem d' hd'O _
    · exact mul_mem (mul_mem (hJC hj) hda) (inv_mem (hJC hj))
  refine not_isSymSixType_of_odd e hwN hww hDN hDodd hDw hDJ ?_ φ hφ
  by_contra hall
  push Not at hall
  have hle : J ≤ (pPrimeCore 2 ↥J).map J.subtype := by
    have h1 : closure {y | ∃ j ∈ J, ∃ d ∈ D, y = j⁻¹ * d⁻¹ * j * d} ≤
        (pPrimeCore 2 ↥J).map J.subtype := by
      rw [closure_le]
      rintro _ ⟨j, hj, d, hd, rfl⟩
      exact hall d hd j hj
    rwa [hJD] at h1
  have htriv : ∀ q : ↥J ⧸ pPrimeCore 2 ↥J, q = 1 := by
    intro q
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective q
    rw [QuotientGroup.eq_one_iff]
    obtain ⟨y, hy, hyx⟩ := hle x.2
    rw [show x = y from Subtype.ext hyx.symm]
    exact hy
  have hne : (⟨Equiv.swap (0 : Fin 6) 1 * Equiv.swap 1 2,
      Equiv.Perm.mem_alternatingGroup.mpr (by decide)⟩ : alternatingGroup (Fin 6)) ≠ 1 := by
    intro h1
    have h2 := congrArg (fun x : alternatingGroup (Fin 6) => (x : Equiv.Perm (Fin 6))) h1
    revert h2
    decide
  apply hne
  rw [← e.apply_symm_apply ⟨_, _⟩, htriv (e.symm _), map_one]

end CFSG.ComponentClassification.GSThmB.A10Side
