module

public import CFSG.Quasithin.H13.L32AC40c
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.L32AC40b
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.L32AC30b

public section

namespace CFSG.Quasithin.H13.L32A.C

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.F7

attribute [local instance] commGroupOfFact

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G] {T L V H K : Subgroup G}

theorem exists_orderOf_three_finW_F4 {W : Type*} [Group W] [Finite W] (h1222 : Stmt12_2_2_F4)
    (h1332 : Stmt13_3_2_F4) (h1334 : A6.Stmt13_3_4_F4) (S : Setting147 G T L V H) (Ψ : ↥H →* W)
    (hker : ∀ x : ↥H, Ψ x = 1 ↔ (x : G) ∈ pCoreOf 2 H) :
    ∃ a ∈ ((l1 T L V).subgroupOf H).map Ψ, orderOf a = 3 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hL1H : l1 T L V ≤ H := le_sup_left.trans S.hz.1.1
  have hL3 := relIndex_l1_F4 h1222 h1332 h1334 S.hyp

  have hle : l1 T L V ⊓ pCoreOf 2 H ≤ pCoreOf 2 (l1 T L V) := by
    refine le_pCoreOf 2 inf_le_left ?_ ((pCoreOf_isPGroup 2 H).to_inf_right)
    constructor
    intro n hn g
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    refine ⟨(l1 T L V).mul_mem ((l1 T L V).mul_mem g.2 hn.1) ((l1 T L V).inv_mem g.2), ?_⟩
    have := (Subgroup.mem_normalizer_iff.mp
      (le_normalizer_pCoreOf 2 H (hL1H g.2)) n).mp hn.2
    simpa using this
  have hdvd : 3 ∣ Nat.card ↥(((l1 T L V).subgroupOf H).map Ψ) := by
    rw [card_map_eq_relIndex Ψ hker hL1H, ← Subgroup.inf_relIndex_right, inf_comm,
      ← Subgroup.relIndex_mul_relIndex (l1 T L V ⊓ pCoreOf 2 H) (pCoreOf 2 (l1 T L V))
      (l1 T L V) hle (pCoreOf_le 2 _), hL3]
    exact Dvd.intro_left _ rfl
  obtain ⟨a, ha⟩ := exists_prime_orderOf_dvd_card' 3 hdvd
  exact ⟨a, a.2, by rw [← ha, Subgroup.orderOf_coe]⟩

theorem s5_of_F4 (h1222 : Stmt12_2_2_F4) (h1332 : Stmt13_3_2_F4) (h1334 : A6.Stmt13_3_4_F4)
    (S : Setting147 G T L V H) (hF : HypF918 T V L (fsuV1 T V) V H K)
    (hK₀ : conjClosure K T = K) (hHKT : H = K ⊔ T) (hA5 : IsAlt 5 (cStar K))
    (hl1K : l1 T L V ≤ K) :
    quasithinO2QuotientIso H (Equiv.Perm (Fin 5)) ∧
      (∀ r ∈ pCoreOf 2 (l1 T L V ⊔ T), ∃ k ∈ K, k⁻¹ * r ∈ pCoreOf 2 H) ∧
      (pCoreOf 2 H).relIndex (pCoreOf 2 (l1 T L V ⊔ T)) = 4 := by
  have := factElem hF (le_conjClosure V H)
  have hKH : K ≤ H := le_of_mem_cComp hF.K_cComp
  have hTH : T ≤ H := hF.T_le_H
  have hKnH : H ≤ Subgroup.normalizer (K : Set G) := hK₀ ▸ hF.K₀_normal
  have hL1H : l1 T L V ≤ H := le_sup_left.trans S.hz.1.1
  have hRH : pCoreOf 2 (l1 T L V ⊔ T) ≤ H := (Setting147.R1_le_T S).trans hTH
  set Φ := phiU hF with hΦ
  have hker : ∀ x : ↥H, Φ x = 1 ↔ (x : G) ∈ pCoreOf 2 H := phiU_eq_one_iff hF
  obtain ⟨hLX, hXN, hCXL, hSyl, -⟩ := groups_of_hom Φ hker hKH hTH hKnH hF.sylow_H hHKT
  set Lb := (K.subgroupOf H).map Φ with hLb
  set Rb := ((pCoreOf 2 (l1 T L V ⊔ T)).subgroupOf H).map Φ with hRb
  obtain ⟨eL⟩ := nonempty_cStar_equiv_map Φ hker hF.K_cComp
  obtain ⟨eA⟩ := hA5
  let e : ↥Lb ≃* alternatingGroup (Fin 5) := eL.symm.trans eA
  obtain ⟨π, hπL, hπC⟩ := CFSG.RankThree.PartOne.TerminalPerm.exists_pi_of_equiv e hLX
    (fun g hg y hy => (Subgroup.mem_normalizer_iff.mp (hXN hg) y).mp hy)

  have hZ : ∀ y : ↥Lb, (∀ y' : ↥Lb, y * y' = y' * y) → y = 1 := by
    intro y hy
    have := alt5_center (e y) (fun g => by
      obtain ⟨y', rfl⟩ := e.surjective g
      rw [← map_mul, ← map_mul, hy y'])
    exact e.injective (this.trans (map_one e).symm)
  have hπinj : Function.Injective π := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro g hg
    have hc := hπC g hg
    have hgL : (g : MulAut _) ∈ Lb :=
      hCXL ⟨Subgroup.mem_centralizer_iff.mpr fun y hy => (hc y hy).symm, g.2⟩
    have h1 := hZ ⟨g, hgL⟩ (fun y' => Subtype.ext (hc y' y'.2))
    rw [Subgroup.mem_bot]
    have h2 : g.1 = 1 := by
      have := congrArg Subtype.val h1
      simpa using this
    exact Subtype.ext h2

  obtain ⟨a, haL1, ha3⟩ := exists_orderOf_three_finW_F4 h1222 h1332 h1334 S Φ hker
  have haL : a ∈ Lb := Subgroup.map_mono (fun x hx => Subgroup.mem_subgroupOf.mpr
    (hl1K (Subgroup.mem_subgroupOf.mp hx))) haL1
  have haR : ∀ r ∈ Rb, a * r * a⁻¹ ∈ Rb := by
    obtain ⟨y, hy, rfl⟩ := haL1
    rintro _ ⟨r, hr, rfl⟩
    refine ⟨y * r * y⁻¹, Subgroup.mem_subgroupOf.mpr ?_, by rw [map_mul, map_mul, map_inv]⟩
    have hyN := le_normalizer_pCoreOf 2 (l1 T L V ⊔ T)
      (le_sup_left (b := T) (Subgroup.mem_subgroupOf.mp hy))
    exact (Subgroup.mem_normalizer_iff.mp hyN _).mp (Subgroup.mem_subgroupOf.mp hr)
  have hno : ∀ r ∈ Lb, r * r = 1 → r ≠ 1 → a * r * a⁻¹ = r → False := by
    intro r hr hr2 hr1 hc
    have ha1 : a ≠ 1 := fun h => by rw [h, orderOf_one] at ha3; omega
    have ha3' : a ^ 3 = 1 := by rw [← ha3]; exact pow_orderOf_eq_one a
    refine A5Mod.alt5_not_comm (e ⟨r, hr⟩) (e ⟨a, haL⟩) ?_ ?_ ?_ ?_ ?_
    · rw [← map_mul, show (⟨r, hr⟩ : ↥Lb) * ⟨r, hr⟩ = 1 from Subtype.ext hr2, map_one]
    · exact fun h => hr1 (congrArg Subtype.val (e.injective (h.trans (map_one e).symm)))
    · rw [← map_pow, show (⟨a, haL⟩ : ↥Lb) ^ 3 = 1 from Subtype.ext (by simpa using ha3'),
        map_one]
    · exact fun h => ha1 (congrArg Subtype.val (e.injective (h.trans (map_one e).symm)))
    · rw [← map_mul, ← map_mul]
      congr 1
      apply Subtype.ext
      show r * a = a * r
      calc r * a = (a * r * a⁻¹) * a := by rw [hc]
        _ = a * r := by group
  have hSR := card_map_T_F4 h1222 h1332 h1334 S hTH Φ hker
  rw [← hRb] at hSR
  have hSR' : Nat.card ↥((T.subgroupOf H).map Φ) = 2 * Nat.card ↥Rb := hSR

  have hno2 : ∀ P : Subgroup (MulAut ↥(tildeOf (fsuV1 T V) (conjClosure V H))), P ≤ Lb →
      P ≤ Rb → Nat.card P = 2 → (∀ r ∈ P, a * r * a⁻¹ ∈ P) → False := by
    intro P hPL hPR hP2 haP
    obtain ⟨r, hrP, hr1, hr2, hor⟩ := exists_of_card_eq_two hP2
    refine hno r (hPL hrP) hr2 hr1 ?_
    rcases hor _ (haP r hrP) with h | h
    · exfalso
      apply hr1
      have : r = a⁻¹ * (a * r * a⁻¹) * a := by group
      rw [this, h]
      group
    · exact h

  have hodd : ∃ x : ↥Φ.range, π x ∉ alternatingGroup (Fin 5) := by
    by_contra hall
    push Not at hall
    have hXL : Φ.range ≤ Lb := by
      intro x hx
      obtain ⟨y, hy⟩ := e.surjective ⟨π ⟨x, hx⟩, hall ⟨x, hx⟩⟩
      have h1 : π ⟨(y : MulAut _), hLX y.2⟩ = π ⟨x, hx⟩ := by
        rw [hπL _ y.2]
        exact congrArg Subtype.val hy
      have h3 : (y : MulAut _) = x := congrArg Subtype.val (hπinj h1)
      exact h3 ▸ y.2
    have hX60 : Nat.card Φ.range = 2 ^ 2 * 15 := by
      rw [le_antisymm hXL hLX, Nat.card_congr e.toEquiv, nat_card_alternatingGroup, Nat.card_fin]
      rfl
    have hS4 := card_eq_of_isSylowTwoOf hSyl hX60 (by decide)
    have hS4' : Nat.card ↥((T.subgroupOf H).map Φ) = 4 := hS4.trans (by norm_num)
    refine hno2 Rb (fun x hx => hXL (Subgroup.map_le_range Φ _ hx)) le_rfl (by omega) haR

  have hπsurj : Function.Surjective π := by
    obtain ⟨x₀, hx₀⟩ := hodd
    intro σ
    by_cases hσ : σ ∈ alternatingGroup (Fin 5)
    · obtain ⟨y, hy⟩ := e.surjective ⟨σ, hσ⟩
      exact ⟨⟨y, hLX y.2⟩, by rw [hπL _ y.2]; exact congrArg Subtype.val hy⟩
    · have hs1 : Equiv.Perm.sign σ = -1 :=
        (Int.units_eq_one_or _).resolve_left (fun h => hσ (Equiv.Perm.mem_alternatingGroup.mpr h))
      have hs2 : Equiv.Perm.sign (π x₀) = -1 :=
        (Int.units_eq_one_or _).resolve_left (fun h => hx₀ (Equiv.Perm.mem_alternatingGroup.mpr h))
      have hτ : σ * (π x₀)⁻¹ ∈ alternatingGroup (Fin 5) := by
        rw [Equiv.Perm.mem_alternatingGroup, map_mul, map_inv, hs1, hs2]
        decide
      obtain ⟨y, hy⟩ := e.surjective ⟨_, hτ⟩
      refine ⟨⟨y, hLX y.2⟩ * x₀, ?_⟩
      rw [map_mul, hπL _ y.2, show ((e y : alternatingGroup (Fin 5)) : Equiv.Perm (Fin 5)) =
        σ * (π x₀)⁻¹ from congrArg Subtype.val hy]
      group

  let φ : ↥H →* Equiv.Perm (Fin 5) := π.comp Φ.rangeRestrict
  have hφker : φ.ker = CFSG.pCore 2 ↥H := by
    ext x
    rw [MonoidHom.mem_ker, ← subgroupOf_pCoreOf_eq_pCore H, Subgroup.mem_subgroupOf, ← hker]
    constructor
    · intro h
      exact congrArg Subtype.val (hπinj (h.trans (map_one π).symm))
    · intro h
      show π (Φ.rangeRestrict x) = 1
      rw [show Φ.rangeRestrict x = 1 from Subtype.ext h, map_one]

  have hX120 : Nat.card Φ.range = 2 ^ 3 * 15 := by
    rw [Nat.card_congr (Equiv.ofBijective π ⟨hπinj, hπsurj⟩), Nat.card_perm, Nat.card_fin]
    rfl
  have hS8 := card_eq_of_isSylowTwoOf hSyl hX120 (by decide)
  have hS8' : Nat.card ↥((T.subgroupOf H).map Φ) = 8 := hS8.trans (by norm_num)
  have hR4 : Nat.card Rb = 4 := by omega
  have hL60 : Nat.card Lb = 60 := by
    rw [Nat.card_congr e.toEquiv, nat_card_alternatingGroup, Nat.card_fin]
    rfl
  have hRL : Rb ≤ Lb := by
    by_contra hRL
    have hRX : Rb ≤ Φ.range := Subgroup.map_le_range Φ _
    have hidx : Lb.relIndex Φ.range = 2 := by
      have h1 := Subgroup.relIndex_mul_card Lb Φ.range
      rw [inf_eq_left.mpr hLX, hL60, hX120] at h1
      omega
    have hle : Lb.relIndex Rb ≤ 2 :=
      hidx ▸ Subgroup.relIndex_le_of_le_right hRX (by omega)
    have hne1 : Lb.relIndex Rb ≠ 1 := fun h => hRL (Subgroup.relIndex_eq_one.mp h)
    have h3 := Subgroup.relIndex_mul_card Lb Rb
    rw [hR4] at h3
    have h2 : Lb.relIndex Rb = 2 := by
      have : Lb.relIndex Rb ≠ 0 := fun h0 => by rw [h0, zero_mul] at h3; omega
      omega
    rw [h2] at h3
    refine hno2 (Lb ⊓ Rb) inf_le_left inf_le_right (by omega) ?_
    intro r hr
    exact ⟨Lb.mul_mem (Lb.mul_mem haL hr.1) (Lb.inv_mem haL), haR r hr.2⟩
  refine ⟨⟨φ, hπsurj.comp Φ.rangeRestrict_surjective,
    hφker.trans (CFSG.pCore_eq_open ↥H 2)⟩, ?_, ?_⟩
  · intro r hr
    obtain ⟨⟨_, k, hk, rfl⟩, hkr⟩ : ∃ y : ↥Lb, (y : MulAut _) = Φ ⟨r, hRH hr⟩ :=
      ⟨⟨_, hRL ⟨⟨r, hRH hr⟩, Subgroup.mem_subgroupOf.mpr hr, rfl⟩⟩, rfl⟩
    refine ⟨k, Subgroup.mem_subgroupOf.mp hk, ?_⟩
    have h1 : Φ (k⁻¹ * ⟨r, hRH hr⟩) = 1 := by
      rw [map_mul, map_inv, ← hkr, inv_mul_cancel]
    simpa using (hker _).mp h1
  · rw [← card_map_eq_relIndex Φ hker hRH]
    exact hR4

end CFSG.Quasithin.H13.L32A.C
