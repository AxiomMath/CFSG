module

public import CFSG.GH74.Uniqueness.SU.SU7Gen6
public import CFSG.GH74.Uniqueness.SU.SU9Cfg
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.InvolutionCountingOrderFormula

public section

namespace CFSG.GH74.Uniqueness.SU.SU9

open Subgroup CFSG.GH74.Uniqueness.SU.SU4 CFSG.GH74.Uniqueness.SU.SU5 CFSG.GH74.Uniqueness.SU.SU7
  CFSG CFSG.ShultStronglyClosedTI.InvolutionCounting

namespace Cnt

variable {G : Type} [Group G] [Finite G] {S : Sylow 2 G} {U M V : Subgroup G} {x z : G}
  {A B R : Subgroup G}

theorem cent_z_facts (h192 : Lemma192Stmt) (h194 : Lemma194Stmt) (hc : Ctx19 S U M V x z A B R) :
    (∀ c ∈ centralizer ({z} : Set G), ∀ r ∈ R, c * r * c⁻¹ ∈ R) ∧
      Nat.card ↥(centralizer ({z} : Set G)) = 1920 := by
  have hcore : pPrimeCore 2 ↥(centralizer ({z} : Set G)) = ⊥ :=
    (h194 G S U M V x z A B R hc).2 z (Cfg.z_mem_S hc) hc.conf.hz
  obtain ⟨⟨hSyl, ⟨e⟩⟩, -⟩ := h192 G S U M V x z A B R hc
  set C := centralizer ({z} : Set G) with hC
  set O : Subgroup ↥C := Op_p'p 2 ↥C with hO
  have hO2 : IsPGroup 2 ↥O := by
    have hp : IsPGroup 2 ↥(pCore 2 (↥C ⧸ pPrimeCore 2 ↥C)) := pCore_isPGroup
    have hker : IsPGroup 2 (QuotientGroup.mk' (pPrimeCore 2 ↥C)).ker := by
      rw [QuotientGroup.ker_mk', hcore]
      exact IsPGroup.of_card (n := 0) (by simp)
    exact hp.comap_of_ker_isPGroup _ hker
  have hO'2 : IsPGroup 2 ↥(O.map C.subtype) := hO2.map _
  have hR : O.map C.subtype = R := by
    obtain ⟨hle, hRp, hodd⟩ := hSyl
    obtain ⟨n, hn⟩ := hO'2.index (R.subgroupOf (O.map C.subtype))
    have hn0 : n = 0 := by
      by_contra hn0
      have h1 : Odd (R.subgroupOf (O.map C.subtype)).index := hodd
      rw [hn] at h1
      have h2 : Even (2 ^ n) := (Nat.even_pow.2 ⟨even_two, hn0⟩)
      exact (Nat.not_odd_iff_even.2 h2) h1
    rw [hn0, pow_zero] at hn
    have htop : R.subgroupOf (O.map C.subtype) = ⊤ := Subgroup.index_eq_one.1 hn
    apply le_antisymm _ hle
    intro g hg
    have : (⟨g, hg⟩ : ↥(O.map C.subtype)) ∈ R.subgroupOf (O.map C.subtype) := by
      rw [htop]; exact Subgroup.mem_top _
    exact this
  have hRn : ∀ c ∈ C, ∀ r ∈ R, c * r * c⁻¹ ∈ R := by
    intro c hcC r hr
    rw [← hR] at hr ⊢
    obtain ⟨o, ho, rfl⟩ := hr
    exact ⟨⟨c, hcC⟩ * o * ⟨c, hcC⟩⁻¹,
      (inferInstance : O.Normal).conj_mem o ho ⟨c, hcC⟩, rfl⟩
  refine ⟨hRn, ?_⟩
  have hcardC : Nat.card ↥C = Nat.card (↥C ⧸ O) * Nat.card ↥O :=
    Subgroup.card_eq_card_quotient_mul_card_subgroup O
  have hOcard : Nat.card ↥O = 32 := by
    have h1 := Subgroup.card_map_of_injective (f := C.subtype) C.subtype_injective (K := O)
    rw [hR] at h1
    rw [← h1]
    exact (IsQ8D8.facts hc.c19.R_iso).1
  have hA5 : Nat.card (alternatingGroup (Fin 5)) = 60 := by
    rw [Nat.card_eq_fintype_card, card_alternatingGroup]
    simp [Nat.factorial]
  rw [hcardC, Nat.card_congr e.toEquiv, hA5, hOcard]

omit [Finite G] in
theorem zpow_cases {v : G} (hv : v * v = 1) (k : ℤ) : v ^ k = 1 ∨ v ^ k = v := by
  have hv2 : v ^ (2 : ℤ) = 1 := by rw [zpow_two, hv]
  obtain ⟨n, rfl | rfl⟩ := Int.even_or_odd' k
  · left; rw [zpow_mul, hv2, one_zpow]
  · right; rw [zpow_add, zpow_mul, hv2, one_zpow, one_mul, zpow_one]

structure Data (S : Sylow 2 G) (U : Subgroup G) (z : G) (A B : Subgroup G) (a : G) : Prop where
  ha : a ∈ A
  haU : a ∉ U
  cover : ∀ g : G, orderOf g = 2 → IsConj z g ∨ IsConj a g
  not_conj : ¬ IsConj z a
  class_a : ∀ g ∈ (S : Subgroup G), IsConj a g ↔ ((g ∈ A ∨ g ∈ B) ∧ g ∉ U)
  cent : Nonempty (↥(centralizer ({a} : Set G)) ≃*
    alternatingGroup (Fin 4) × (Multiplicative (ZMod 2) × Multiplicative (ZMod 2)))

theorem Data.of_h196 (h196 : Lemma196Stmt) (hc : Ctx19 S U M V x z A B R) {a : G} (ha : a ∈ A)
    (haU : a ∉ U) : Data S U z A B a := by
  obtain ⟨⟨hcover, hnz⟩, hb, hcent, -⟩ := h196 G S U M V x z A B R hc a ha haU
  exact ⟨ha, haU, hcover, hnz, hb, hcent⟩

theorem isConj_z_iff (h191 : Lemma191Stmt) (hc : Ctx19 S U M V x z A B R) {a : G}
    (hd : Data S U z A B a) {s : G} (hs : s ∈ (S : Subgroup G)) (hs2 : orderOf s = 2) :
    IsConj z s ↔ (s ∈ U ∨ s ∉ Tsub S U) := by
  have hs1 : s ≠ 1 := fun h => by rw [h, orderOf_one] at hs2; omega
  constructor
  · intro hzs
    by_contra hcon
    push Not at hcon
    obtain ⟨hsU, hsT⟩ := hcon
    have hsAB : s ∈ A ∨ s ∈ B := hc.c19.invol s hsT hs2
    have : IsConj a s := (hd.class_a s hs).2 ⟨hsAB, hsU⟩
    exact hd.not_conj (hzs.trans this.symm)
  · rintro (h | h)
    · exact Cfg.isConj_z_of_mem_U hc h hs1
    · exact Cfg.isConj_z_of_not_T h191 hc hs h hs2

theorem orderOf_of_isConj_z (hc : Ctx19 S U M V x z A B R) {v : G} (hzv : IsConj z v) :
    orderOf v = 2 := by
  obtain ⟨c, hc'⟩ := isConj_iff.1 hzv
  rw [← hc', Cfg.orderOf_conj']
  exact hc.conf.hz

theorem mem_R_of_isConj_z (h191 : Lemma191Stmt) (h192 : Lemma192Stmt) (h194 : Lemma194Stmt)
    (hc : Ctx19 S U M V x z A B R) {a : G} (hd : Data S U z A B a) {v : G}
    (hvC : v ∈ centralizer ({z} : Set G)) (hzv : IsConj z v) : v ∈ R := by
  obtain ⟨hRn, -⟩ := cent_z_facts h192 h194 hc
  have hv2 : orderOf v = 2 := orderOf_of_isConj_z hc hzv
  have hvv : v ^ (2 ^ 1) = 1 := by rw [← hv2]; simp
  have hSC : (S : Subgroup G) ≤ centralizer ({z} : Set G) := fun s hs =>
    mem_centralizer_singleton_iff.2 (hc.conf.z_center s hs)
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨c, hcC, hcS⟩ := CFSG.LyonsUnitaryFour.exists_conj_mem_sylow_of_le S hSC hvC ⟨1, hvv⟩
  have hs2 : orderOf (c * v * c⁻¹) = 2 := by rw [Cfg.orderOf_conj']; exact hv2
  have hzs : IsConj z (c * v * c⁻¹) := hzv.trans (isConj_iff.2 ⟨c, rfl⟩)
  have hsR : c * v * c⁻¹ ∈ R := by
    rw [hc.c19.R_invol _ hs2]
    rcases (isConj_z_iff h191 hc hd hcS hs2).1 hzs with h | h
    · exact Or.inl h
    · exact Or.inr ⟨hcS, h⟩
  have := hRn c⁻¹ ((centralizer ({z} : Set G)).inv_mem hcC) _ hsR
  simpa [mul_assoc] using this

theorem inv_in_A (hc : Ctx19 S U M V x z A B R) {a : G} (hd : Data S U z A B a) :
    ∀ y ∈ centralizer ({a} : Set G), y * y = 1 → y ∈ A := by
  classical
  obtain ⟨e⟩ := hd.cent
  set X := centralizer ({a} : Set G) with hX
  have hAX : A ≤ X := fun g hg => mem_centralizer_singleton_iff.2 (Cfg.A_comm hc g hg a hd.ha)
  have hJ : Nat.card {g : ↥X // g * g = 1} = 16 := by
    have h1 : Nat.card {g : ↥X // g * g = 1} = Nat.card
        {m : alternatingGroup (Fin 4) × (Multiplicative (ZMod 2) × Multiplicative (ZMod 2)) //
          m * m = 1} :=
      Nat.card_congr (e.toEquiv.subtypeEquiv (fun g => by
        rw [show e.toEquiv g = e g from rfl, ← map_mul]
        exact (MulEquiv.map_eq_one_iff e).symm))
    rw [h1, Nat.card_eq_fintype_card]
    decide +kernel
  have hA'' : Nat.card ↥{g : ↥X | (g : G) ∈ A} = 16 := by
    rw [← Cfg.card_A hc]
    exact Nat.card_congr
      { toFun := fun g => ⟨g.1.1, g.2⟩
        invFun := fun g => ⟨⟨g.1, hAX g.2⟩, g.2⟩
        left_inv := fun g => rfl
        right_inv := fun g => rfl }
  have hsub : {g : ↥X | (g : G) ∈ A} ⊆ {g : ↥X | g * g = 1} := by
    intro g hg
    exact Subtype.ext (Cfg.A_sq hc g hg)
  have heq : {g : ↥X | (g : G) ∈ A} = {g : ↥X | g * g = 1} := by
    apply Set.eq_of_subset_of_ncard_le hsub
    rw [← Nat.card_coe_set_eq, ← Nat.card_coe_set_eq]
    show Nat.card {g : ↥X // g * g = 1} ≤ Nat.card ↥{g : ↥X | (g : G) ∈ A}
    rw [hJ, hA'']
  intro y hy hyy
  have : (⟨y, hy⟩ : ↥X) ∈ {g : ↥X | g * g = 1} := Subtype.ext hyy
  rw [← heq] at this
  exact this

theorem eq_z_of_cent (hc : Ctx19 S U M V x z A B R) {v ι : G} (hvS : v ∈ (S : Subgroup G))
    (hvT : v ∉ Tsub S U) (hv2 : v * v = 1) (hιT : ι ∈ Tsub S U) (hι2 : ι * ι = 1) (hι1 : ι ≠ 1)
    (hcomm : v * ι = ι * v) : ι = z := by
  have hJ := Cfg.j2 hc
  obtain ⟨g, hgS, hgx⟩ := hJ.conj_invol v hvS hvT (by rw [pow_two]; exact hv2)
  have hι'T : g⁻¹ * ι * g ∈ Tsub S U := by
    have := hJ.T_normal g⁻¹ ((S : Subgroup G).inv_mem hgS) ι hιT
    simpa using this
  have hι'x : x * (g⁻¹ * ι * g) = (g⁻¹ * ι * g) * x := by
    have h1 : g * x * g⁻¹ * ι = ι * (g * x * g⁻¹) := by rw [hgx]; exact hcomm
    calc x * (g⁻¹ * ι * g) = g⁻¹ * (g * x * g⁻¹ * ι) * g := by group
      _ = g⁻¹ * (ι * (g * x * g⁻¹)) * g := by rw [h1]
      _ = (g⁻¹ * ι * g) * x := by group
  have hι'2 : (g⁻¹ * ι * g) * (g⁻¹ * ι * g) = 1 := by
    calc (g⁻¹ * ι * g) * (g⁻¹ * ι * g) = g⁻¹ * (ι * ι) * g := by group
      _ = 1 := by rw [hι2]; group
  have hι'1 : g⁻¹ * ι * g ≠ 1 := by
    intro h
    apply hι1
    have : ι = g * (g⁻¹ * ι * g) * g⁻¹ := by group
    rw [this, h]; group
  obtain ⟨⟨e⟩, hzmem, hcen, -⟩ := hJ.Q
  have hmem : g⁻¹ * ι * g ∈ Tsub S U ⊓ centralizer ({x} : Set G) :=
    ⟨hι'T, mem_centralizer_singleton_iff.2 hι'x.symm⟩
  have hcentral : ∀ q' ∈ Tsub S U ⊓ centralizer ({x} : Set G),
      (g⁻¹ * ι * g) * q' = q' * (g⁻¹ * ι * g) := by
    intro q' hq'
    have hsq : e ⟨g⁻¹ * ι * g, hmem⟩ * e ⟨g⁻¹ * ι * g, hmem⟩ = 1 := by
      rw [← map_mul]
      have : (⟨g⁻¹ * ι * g, hmem⟩ : ↥(Tsub S U ⊓ centralizer ({x} : Set G))) *
          ⟨g⁻¹ * ι * g, hmem⟩ = 1 := Subtype.ext hι'2
      rw [this, map_one]
    have hq8 : ∀ m : QuaternionGroup 2, m * m = 1 → ∀ y : QuaternionGroup 2, m * y = y * m := by
      decide +kernel
    have := hq8 _ hsq (e ⟨q', hq'⟩)
    rw [← map_mul, ← map_mul] at this
    have := e.injective this
    exact congrArg Subtype.val this
  have h1z : g⁻¹ * ι * g = 1 ∨ g⁻¹ * ι * g = z := (hcen _ hmem).1 hcentral
  have hι'z : g⁻¹ * ι * g = z := h1z.resolve_left hι'1
  have hzS : g * z = z * g := hc.conf.z_center g hgS
  calc ι = g * (g⁻¹ * ι * g) * g⁻¹ := by group
    _ = g * z * g⁻¹ := by rw [hι'z]
    _ = z := by rw [hzS]; group

theorem z_mem_zpowers_mul (hc : Ctx19 S U M V x z A B R) {v w : G}
    (hvS : v ∈ (S : Subgroup G)) (hvT : v ∉ Tsub S U) (hv2 : v * v = 1) (hwAB : w ∈ A ∨ w ∈ B)
    (hwU : w ∉ U) (hw2 : w * w = 1) : z ∈ zpowers (v * w) := by
  have hJ := Cfg.j2 hc
  have hvinv : v⁻¹ = v := inv_eq_of_mul_eq_one_right hv2
  have hwinv : w⁻¹ = w := inv_eq_of_mul_eq_one_right hw2
  have hwT : w ∈ Tsub S U := by
    rcases hwAB with h | h
    · exact hc.c19.A_le h
    · exact hc.c19.B_le h
  have hbT : v * w * v⁻¹ ∈ Tsub S U := hJ.T_normal v hvS w hwT
  have hbU : v * w * v⁻¹ ∉ U := by
    intro h
    apply hwU
    have := Cfg.S_normalizes_U hc v⁻¹ ((S : Subgroup G).inv_mem hvS) _ h
    simpa [mul_assoc] using this
  have hbw : v * w * v⁻¹ * w ∉ A ∧ v * w * v⁻¹ * w ∉ B := by
    rcases hwAB with hwA | hwB
    · have hbB : v * w * v⁻¹ ∈ B := by
        have h1 : conjSub v A = B := Cfg.conjSub_A_of_not_T hc hvS hvT
        have : v * w * v⁻¹ ∈ conjSub v A := by
          rw [mem_conjSub]
          have e : v⁻¹ * (v * w * v⁻¹) * v = w := by group
          rw [e]; exact hwA
        rwa [h1] at this
      constructor
      · intro h
        apply hbU
        have hbA : v * w * v⁻¹ ∈ A := by
          have := A.mul_mem h (A.inv_mem hwA)
          simpa [mul_assoc] using this
        rw [← hc.c19.AB_inf]; exact ⟨hbA, hbB⟩
      · intro h
        apply hwU
        have hwB' : w ∈ B := by
          have := B.mul_mem (B.inv_mem hbB) h
          simpa [mul_assoc] using this
        rw [← hc.c19.AB_inf]; exact ⟨hwA, hwB'⟩
    · have hbA : v * w * v⁻¹ ∈ A := by
        have h1 : conjSub v B = A := Cfg.conjSub_B_of_not_T hc hvS hvT
        have : v * w * v⁻¹ ∈ conjSub v B := by
          rw [mem_conjSub]
          have e : v⁻¹ * (v * w * v⁻¹) * v = w := by group
          rw [e]; exact hwB
        rwa [h1] at this
      constructor
      · intro h
        apply hwU
        have hwA' : w ∈ A := by
          have := A.mul_mem (A.inv_mem hbA) h
          simpa [mul_assoc] using this
        rw [← hc.c19.AB_inf]; exact ⟨hwA', hwB⟩
      · intro h
        apply hbU
        have hbB : v * w * v⁻¹ ∈ B := by
          have := B.mul_mem h (B.inv_mem hwB)
          simpa [mul_assoc] using this
        rw [← hc.c19.AB_inf]; exact ⟨hbA, hbB⟩
  set y := v * w * v⁻¹ * w with hy
  have hyT : y ∈ Tsub S U := (Tsub S U).mul_mem hbT hwT
  have hcc : (v * w) * (v * w) = y := by rw [hy, hvinv]; group
  have hy1 : y ≠ 1 := fun h => hbw.1 (h ▸ A.one_mem)
  have hy2 : y * y ≠ 1 := by
    intro h
    have hyo : orderOf y = 2 := orderOf_eq_prime (by rw [pow_two]; exact h) hy1
    rcases hc.c19.invol y hyT hyo with h' | h'
    · exact hbw.1 h'
    · exact hbw.2 h'
  have hp2 : IsPGroup 2 ↥(Tsub S U) := (S.isPGroup').to_le Cfg.T_le_S
  obtain ⟨m, hm⟩ := Gen.exists_orderOf_eq_two_pow hp2 hyT
  have hm2 : 2 ≤ m := by
    by_contra hlt
    push Not at hlt
    interval_cases m
    · rw [pow_zero, orderOf_eq_one_iff] at hm; exact hy1 hm
    · rw [pow_one] at hm
      exact hy2 (by rw [← pow_two]; rw [← hm]; exact pow_orderOf_eq_one y)
  have hdvd : 2 ^ (m - 1) ∣ orderOf y := by rw [hm]; exact pow_dvd_pow 2 (Nat.sub_le m 1)
  set ι := y ^ (2 ^ (m - 1)) with hι
  have hι2 : orderOf ι = 2 := by
    rw [hι, orderOf_pow_of_dvd (by positivity) hdvd, hm]
    have : 2 ^ m = 2 * 2 ^ (m - 1) := by
      rw [← pow_succ']; congr 1; omega
    rw [this, Nat.mul_div_cancel _ (by positivity)]
  have hιT : ι ∈ Tsub S U := (Tsub S U).pow_mem hyT _
  have hι1 : ι ≠ 1 := fun h => by rw [h, orderOf_one] at hι2; omega
  have hιι : ι * ι = 1 := by rw [← pow_two]; rw [← hι2]; exact pow_orderOf_eq_one ι
  have hιc : ι = (v * w) ^ (2 * 2 ^ (m - 1)) := by
    rw [hι, ← hcc, ← pow_two, ← pow_mul]
  have hvc : v * (v * w) * v⁻¹ = (v * w)⁻¹ := by
    rw [mul_inv_rev, hvinv, hwinv, ← mul_assoc, hv2, one_mul]
  have hvι : v * ι = ι * v := by
    have h1 : v * ι * v⁻¹ = ι := by
      rw [hιc, ← conj_pow, hvc, inv_pow, ← hιc]
      exact inv_eq_of_mul_eq_one_right hιι
    rw [mul_inv_eq_iff_eq_mul] at h1
    exact h1
  have hιz : ι = z := Cnt.eq_z_of_cent hc hvS hvT hv2 hιT hιι hι1 hvι
  rw [← hιz, hιc]
  exact Subgroup.npow_mem_zpowers _ _

theorem zconj_comm_a_eq (h191 : Lemma191Stmt) (hc : Ctx19 S U M V x z A B R) {a : G}
    (hd : Data S U z A B a) :
    {y : G | IsConj z y ∧ y * a = a * y} = (U : Set G) \ {1} := by
  ext y
  constructor
  · rintro ⟨hzy, hya⟩
    have hy2 : orderOf y = 2 := orderOf_of_isConj_z hc hzy
    have hyy : y * y = 1 := by rw [← pow_two]; rw [← hy2]; exact pow_orderOf_eq_one y
    have hy1 : y ≠ 1 := fun h => by rw [h, orderOf_one] at hy2; omega
    have hyA : y ∈ A := inv_in_A hc hd y (mem_centralizer_singleton_iff.2 hya) hyy
    have hyS : y ∈ (S : Subgroup G) := Cfg.A_le_S hc hyA
    have hyT : y ∈ Tsub S U := hc.c19.A_le hyA
    rcases (isConj_z_iff h191 hc hd hyS hy2).1 hzy with h | h
    · exact ⟨h, hy1⟩
    · exact absurd hyT h
  · rintro ⟨hyU, hy1⟩
    refine ⟨Cfg.isConj_z_of_mem_U hc hyU hy1, ?_⟩
    exact Cfg.A_comm hc y (Cfg.U_le_A hc hyU) a hd.ha

theorem r_a_eq (h191 : Lemma191Stmt) (hc : Ctx19 S U M V x z A B R) {a : G}
    (hd : Data S U z A B a) : thompsonPairCount z a a = 3 := by
  have ha1 : a ≠ 1 := fun h => hd.haU (h ▸ U.one_mem)
  have haa : a * a = 1 := Cfg.A_sq hc a hd.ha
  have hzz : z * z = 1 := Cfg.z_sq hc
  have hset : thompsonPairs z a a = (fun u : G => (u, u * a)) '' ((U : Set G) \ {1}) := by
    ext p
    obtain ⟨v, w⟩ := p
    constructor
    · intro hp
      obtain ⟨hzv, haw, haz⟩ := hp
      have hvv : v * v = 1 := mul_self_eq_one_of_isConj hzz hzv
      have hww : w * w = 1 := mul_self_eq_one_of_isConj haa haw
      have hcent := mem_centralizer_of_mem_thompsonPairs hzz haa haa
        (show (v, w) ∈ thompsonPairs z a a from ⟨hzv, haw, haz⟩)
      have hvA : v ∈ A := inv_in_A hc hd v hcent.1 hvv
      have hwA : w ∈ A := inv_in_A hc hd w hcent.2 hww
      have hvw : v * w = w * v := Cfg.A_comm hc v hvA w hwA
      have hvwsq : (v * w) * (v * w) = 1 := by
        calc v * w * (v * w) = v * (w * v) * w := by group
          _ = v * (v * w) * w := by rw [← hvw]
          _ = (v * v) * (w * w) := by group
          _ = 1 := by rw [hvv, hww]; group
      have ha_eq : a = v * w := by
        obtain ⟨k, hk⟩ := mem_zpowers_iff.1 haz
        rcases zpow_cases hvwsq k with h | h
        · exact absurd (hk.symm.trans h) ha1
        · exact hk.symm.trans h
      have hvmem : v ∈ ({y : G | IsConj z y ∧ y * a = a * y}) :=
        ⟨hzv, Cfg.A_comm hc v hvA a hd.ha⟩
      rw [zconj_comm_a_eq h191 hc hd] at hvmem
      refine ⟨v, hvmem, ?_⟩
      have hw : w = v * a := by
        calc w = v * (v * w) := by rw [← mul_assoc, hvv, one_mul]
          _ = v * a := by rw [← ha_eq]
      simp only [hw]
    · rintro ⟨u, ⟨huU, hu1⟩, huv⟩
      have hu : u = v ∧ u * a = w := Prod.mk.inj huv
      obtain ⟨rfl, rfl⟩ := hu
      have huuA : u * a ∈ A := A.mul_mem (Cfg.U_le_A hc huU) hd.ha
      have huaU : u * a ∉ U := by
        intro h
        apply hd.haU
        have := U.mul_mem (U.inv_mem huU) h
        simpa using this
      have hleS : u * a ∈ (S : Subgroup G) := Cfg.A_le_S hc huuA
      refine ⟨Cfg.isConj_z_of_mem_U hc huU hu1, (hd.class_a _ hleS).2 ⟨Or.inl huuA, huaU⟩, ?_⟩
      have huu : u * u = 1 := Cfg.U_sq hc u huU
      have : u * (u * a) = a := by rw [← mul_assoc, huu, one_mul]
      rw [this]
      exact mem_zpowers a
  have hinj : Function.Injective (fun u : G => (u, u * a)) := fun u u' h => (Prod.mk.inj h).1
  unfold thompsonPairCount
  rw [hset, Nat.card_coe_set_eq, Set.ncard_image_of_injective _ hinj,
    Set.ncard_sdiff_singleton_of_mem U.one_mem, ← Nat.card_coe_set_eq]
  have : Nat.card (U : Set G) = 4 := Cfg.card_U hc
  omega

end Cnt

end CFSG.GH74.Uniqueness.SU.SU9
