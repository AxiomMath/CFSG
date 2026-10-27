module

public import CFSG.GH74.Uniqueness.SU.SU9Cfg
public import CFSG.GH74.Uniqueness.SU.SU7Gen6
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.InvolutionCountingOrderFormula

public section

namespace CFSG.GH74.Uniqueness.SU.SU9

open Subgroup CFSG.GH74.Uniqueness.SU.SU4 CFSG.GH74.Uniqueness.SU.SU5 CFSG.GH74.Uniqueness.SU.SU7
  CFSG CFSG.ShultStronglyClosedTI.InvolutionCounting
open scoped Pointwise

section General

variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
theorem card_cent_mul_ncard_class (M : Subgroup G) {a : G} (ha : a ∈ M) :
    Nat.card ↥(centralizer ({a} : Set G) ⊓ M) *
      Set.ncard {g : G | ∃ m ∈ M, m * a * m⁻¹ = g} = Nat.card M := by
  have h := card_centralizer_mul_card_conjugatesOf (⟨a, ha⟩ : ↥M)
  have h1 : Nat.card (centralizer ({(⟨a, ha⟩ : ↥M)} : Set ↥M)) =
      Nat.card ↥(centralizer ({a} : Set G) ⊓ M) := by
    refine Nat.card_congr
      { toFun := fun c => ⟨(c.1 : G), ?_, c.1.2⟩
        invFun := fun c => ⟨⟨(c : G), c.2.2⟩, ?_⟩
        left_inv := fun c => rfl
        right_inv := fun c => rfl }
    · have := mem_centralizer_singleton_iff.1 c.2
      exact mem_centralizer_singleton_iff.2 (congrArg Subtype.val this)
    · exact mem_centralizer_singleton_iff.2 (Subtype.ext (mem_centralizer_singleton_iff.1 c.2.1))
  have h2 : Nat.card (conjugatesOf (⟨a, ha⟩ : ↥M)) =
      Set.ncard {g : G | ∃ m ∈ M, m * a * m⁻¹ = g} := by
    rw [Nat.card_coe_set_eq, ← Set.ncard_image_of_injective _ (Subtype.val_injective (p := (· ∈ M)))]
    congr 1
    ext g
    constructor
    · rintro ⟨h', hh', rfl⟩
      obtain ⟨c, hc⟩ := isConj_iff.1 hh'
      exact ⟨c, c.2, by rw [← hc]; rfl⟩
    · rintro ⟨m, hm, rfl⟩
      exact ⟨⟨m * a * m⁻¹, M.mul_mem (M.mul_mem hm ha) (M.inv_mem hm)⟩,
        isConj_iff.2 ⟨⟨m, hm⟩, rfl⟩, rfl⟩
  rw [h1, h2] at h
  exact h

theorem modEq_three {E : Subgroup G} {w : G} (hw : w ∈ normalizer (E : Set G)) (hw3 : w ^ 3 = 1) :
    Nat.card E ≡ Nat.card ↥(E ⊓ centralizer ({w} : Set G)) [MOD 3] := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Fintype E := Fintype.ofFinite _
  let f : Function.End ↥E := fun e => ⟨w * e * w⁻¹, (mem_normalizer_iff.1 hw e).1 e.2⟩
  have hf3 : f ^ 3 = 1 := by
    have hw3' : w * w * w = 1 := by simpa [pow_succ, mul_assoc] using hw3
    rw [show f ^ 3 = f * f * f by rw [pow_succ, pow_succ, pow_one]]
    funext e
    apply Subtype.ext
    show w * (w * (w * (e : G) * w⁻¹) * w⁻¹) * w⁻¹ = e
    calc w * (w * (w * (e : G) * w⁻¹) * w⁻¹) * w⁻¹ = (w * w * w) * e * (w * w * w)⁻¹ := by group
      _ = e := by rw [hw3']; group
  have key := Equiv.Perm.card_fixedPoints_modEq (f := f) (p := 3) (n := 1) (by simpa using hf3)
  have hfix : Fintype.card ↑(Function.fixedPoints f) =
      Nat.card ↥(E ⊓ centralizer ({w} : Set G)) := by
    rw [← Nat.card_eq_fintype_card]
    refine Nat.card_congr
      { toFun := fun e => ⟨(e.1 : G), e.1.2, mem_centralizer_singleton_iff.2 ?_⟩
        invFun := fun g => ⟨⟨(g : G), g.2.1⟩, ?_⟩
        left_inv := fun e => rfl
        right_inv := fun g => rfl }
    · have h1 : f e.1 = e.1 := e.2
      have h2 : w * (e.1 : G) * w⁻¹ = e.1 := congrArg Subtype.val h1
      rw [mul_inv_eq_iff_eq_mul] at h2
      exact h2.symm
    · show f ⟨(g : G), g.2.1⟩ = ⟨(g : G), g.2.1⟩
      apply Subtype.ext
      show w * (g : G) * w⁻¹ = g
      have h1 : (g : G) * w = w * g := mem_centralizer_singleton_iff.1 g.2.2
      rw [mul_inv_eq_iff_eq_mul, h1]
  rw [← Nat.card_eq_fintype_card, hfix] at key
  exact key

omit [Finite G] in
theorem card_sup_eq_mul {K H : Subgroup G} (hHn : ∀ h ∈ H, ∀ k ∈ K, h * k * h⁻¹ ∈ K)
    (hdisj : K ⊓ H = ⊥) : Nat.card ↥(K ⊔ H) = Nat.card K * Nat.card H := by
  obtain ⟨ν, hsurj, hker⟩ := Gen.exists_hom_complement hHn hdisj
  have h1 := Subgroup.card_ker_mul_card_range ν
  have h2 : Nat.card ν.range = Nat.card H := by
    rw [MonoidHom.range_eq_top.2 hsurj]
    exact Nat.card_congr (Subgroup.topEquiv).toEquiv
  have h3 : Nat.card ν.ker = Nat.card K := by
    refine Nat.card_congr
      { toFun := fun p => ⟨(p.1 : G), (hker p.1).1 p.2⟩
        invFun := fun k => ⟨⟨(k : G), Subgroup.mem_sup_left k.2⟩, (hker _).2 k.2⟩
        left_inv := fun p => rfl
        right_inv := fun k => rfl }
  rw [h2, h3] at h1
  exact h1.symm

end General

namespace CM

variable {G : Type} [Group G] [Finite G] {S : Sylow 2 G} {U M V : Subgroup G} {x z : G}
  {A B R : Subgroup G}

theorem ncard_AB_diff (hc : Ctx19 S U M V x z A B R) :
    Set.ncard (((A : Set G) ∪ (B : Set G)) \ (U : Set G)) = 24 := by
  have hfin : ∀ s : Set G, s.Finite := fun s => Set.toFinite s
  have h1 := Set.ncard_union_add_ncard_inter (A : Set G) B (hfin _) (hfin _)
  have hAB : (A : Set G) ∩ (B : Set G) = (U : Set G) := by
    have := hc.c19.AB_inf
    ext g
    constructor
    · rintro ⟨h1, h2⟩
      rw [← this]; exact ⟨h1, h2⟩
    · intro hg
      rw [← this] at hg; exact hg
  have hA : (A : Set G).ncard = 16 := by
    rw [← Nat.card_coe_set_eq]; exact Cfg.card_A hc
  have hB : (B : Set G).ncard = 16 := by
    rw [← Nat.card_coe_set_eq]; exact Cfg.card_B hc
  have hU : (U : Set G).ncard = 4 := by
    rw [← Nat.card_coe_set_eq]; exact Cfg.card_U hc
  rw [hAB, hA, hB, hU] at h1
  have hsub : (U : Set G) ⊆ (A : Set G) ∪ (B : Set G) := fun g hg => Or.inl (Cfg.U_le_A hc hg)
  rw [Set.ncard_sdiff hsub (hfin _), hU]
  omega

theorem class_eq (hc : Ctx19 S U M V x z A B R) (h194M : pPrimeCore 2 ↥M = ⊥)
    (hTM' : ∀ m ∈ M, ∀ t ∈ Tsub S U, m * t * m⁻¹ ∈ Tsub S U) {a : G} (ha : a ∈ A)
    (haU : a ∉ U) :
    {g : G | ∃ m ∈ M, m * a * m⁻¹ = g} = ((A : Set G) ∪ (B : Set G)) \ (U : Set G) := by
  ext g
  constructor
  · rintro ⟨m, hm, rfl⟩
    have hT : m * a * m⁻¹ ∈ Tsub S U := hTM' m hm a (hc.c19.A_le ha)
    have hnU : m * a * m⁻¹ ∉ U := by
      intro h
      apply haU
      have := Cfg.U_normal_M hc hTM' m⁻¹ (M.inv_mem hm) _ h
      simpa [mul_assoc] using this
    have ha1 : a ≠ 1 := fun h => haU (h ▸ U.one_mem)
    have h2 : orderOf (m * a * m⁻¹) = 2 := by
      rw [Cfg.orderOf_conj']
      exact orderOf_eq_prime (by rw [pow_two]; exact Cfg.A_sq hc a ha) ha1
    exact ⟨hc.c19.invol _ hT h2, hnU⟩
  · rintro ⟨hAB, hU⟩
    have hgT : g ∈ Tsub S U := by
      rcases hAB with h | h
      · exact hc.c19.A_le h
      · exact hc.c19.B_le h
    have hgg : g * g = 1 := by
      rcases hAB with h | h
      · exact Cfg.A_sq hc g h
      · exact Cfg.B_sq hc g h
    exact Cfg.exists_M_conj hc h194M ha haU hgT hU hgg

theorem card_cent (hc : Ctx19 S U M V x z A B R) (h194M : pPrimeCore 2 ↥M = ⊥)
    (hTM' : ∀ m ∈ M, ∀ t ∈ Tsub S U, m * t * m⁻¹ ∈ Tsub S U) (hMcard : Nat.card M = 1152)
    {a : G} (ha : a ∈ A) (haU : a ∉ U) : Nat.card ↥(centralizer ({a} : Set G) ⊓ M) = 48 := by
  have haM : a ∈ M := Cfg.S_le_M hc (Cfg.A_le_S hc ha)
  have h := card_cent_mul_ncard_class M haM
  rw [class_eq hc h194M hTM' ha haU, ncard_AB_diff hc, hMcard] at h
  omega

theorem conjSub_A_of_cent (hc : Ctx19 S U M V x z A B R)
    (hTM' : ∀ m ∈ M, ∀ t ∈ Tsub S U, m * t * m⁻¹ ∈ Tsub S U) {a w : G} (ha : a ∈ A)
    (haU : a ∉ U) (hwM : w ∈ M) (hwa : w * a = a * w) : conjSub w A = A := by
  have hwN : w ∈ normalizer ((Tsub S U : Subgroup G) : Set G) :=
    Gen.mem_normalizer_of_conj_le (hTM' w hwM)
  have hle : conjSub w A ≤ Tsub S U := by
    intro y hy
    rw [mem_conjSub] at hy
    have h1 : w⁻¹ * y * w ∈ Tsub S U := hc.c19.A_le hy
    have := (mem_normalizer_iff.1 hwN _).1 h1
    simpa [mul_assoc] using this
  have hE : IsE 4 (conjSub w A) :=
    ⟨isElemAbelian_conjSub (Cfg.isE_A hc).1, by rw [card_conjSub, Cfg.card_A hc]; norm_num⟩
  have haw : a ∈ conjSub w A := by
    rw [mem_conjSub]
    have : w⁻¹ * a * w = a := by
      rw [mul_assoc, ← hwa, ← mul_assoc, inv_mul_cancel, one_mul]
    rw [this]; exact ha
  rcases Cfg.unique_E16 hc hle hE with h | h
  · exact h
  · exfalso
    rw [h] at haw
    exact haU (by rw [← hc.c19.AB_inf]; exact ⟨ha, haw⟩)

theorem card_A1_cases {A₁ : Subgroup G} (hle : A₁ ≤ A) (hA : Nat.card A = 16)
    (hmod : Nat.card A₁ % 3 = 1) : Nat.card A₁ = 1 ∨ Nat.card A₁ = 4 ∨ Nat.card A₁ = 16 := by
  have hdvd : Nat.card A₁ ∣ 16 := hA ▸ Subgroup.card_dvd_of_le hle
  have hle16 := Nat.le_of_dvd (by norm_num) hdvd
  have hpos : 0 < Nat.card A₁ := Nat.card_pos
  interval_cases h : Nat.card A₁ <;> omega

theorem conjSub_B_of_cent (hc : Ctx19 S U M V x z A B R)
    (hTM' : ∀ m ∈ M, ∀ t ∈ Tsub S U, m * t * m⁻¹ ∈ Tsub S U) {a w : G} (ha : a ∈ A)
    (haU : a ∉ U) (hwM : w ∈ M) (hwa : w * a = a * w) : conjSub w B = B := by
  have hwA := conjSub_A_of_cent hc hTM' ha haU hwM hwa
  have hwN : w ∈ normalizer ((Tsub S U : Subgroup G) : Set G) :=
    Gen.mem_normalizer_of_conj_le (hTM' w hwM)
  have hle : conjSub w B ≤ Tsub S U := by
    intro y hy
    rw [mem_conjSub] at hy
    have h1 : w⁻¹ * y * w ∈ Tsub S U := hc.c19.B_le hy
    have := (mem_normalizer_iff.1 hwN _).1 h1
    simpa [mul_assoc] using this
  have hE : IsE 4 (conjSub w B) :=
    ⟨isElemAbelian_conjSub (Cfg.isE_B hc).1, by rw [card_conjSub, Cfg.card_B hc]; norm_num⟩
  rcases Cfg.unique_E16 hc hle hE with h | h
  · exact absurd (conjSub_injective w (h.trans hwA.symm)) (Ne.symm (Cfg.A_ne_B hc))
  · exact h

theorem w_not_cent_U (hc : Ctx19 S U M V x z A B R)
    (hTM' : ∀ m ∈ M, ∀ t ∈ Tsub S U, m * t * m⁻¹ ∈ Tsub S U)
    (hCT : ∀ m ∈ M, (∀ t ∈ Tsub S U, m * t = t * m) → m ∈ Tsub S U) {a w : G} (ha : a ∈ A)
    (haU : a ∉ U) (hwM : w ∈ M) (hwa : w * a = a * w) (hw : orderOf w = 3) :
    ¬ ∀ u ∈ U, w * u = u * w := by
  intro hU
  have hw3 : w ^ 3 = 1 := by rw [← hw]; exact pow_orderOf_eq_one w
  have hwA := conjSub_A_of_cent hc hTM' ha haU hwM hwa
  have hwB := conjSub_B_of_cent hc hTM' ha haU hwM hwa
  have hwN : w ∈ normalizer (A : Set G) := Cfg.mem_normalizer_of_conjSub_eq hwA
  have hmod := modEq_three hwN hw3
  have hm1 : Nat.card ↥(A ⊓ centralizer ({w} : Set G)) % 3 = 1 := by
    have := hmod
    unfold Nat.ModEq at this
    rw [Cfg.card_A hc] at this
    omega
  have hcases := card_A1_cases (inf_le_left : A ⊓ centralizer ({w} : Set G) ≤ A) (Cfg.card_A hc) hm1
  have hUA₁ : U ≤ A ⊓ centralizer ({w} : Set G) := fun u hu =>
    ⟨Cfg.U_le_A hc hu, mem_centralizer_singleton_iff.2 (hU u hu).symm⟩
  have haA₁ : a ∈ A ⊓ centralizer ({w} : Set G) :=
    ⟨ha, mem_centralizer_singleton_iff.2 hwa.symm⟩
  have hA₁16 : Nat.card ↥(A ⊓ centralizer ({w} : Set G)) = 16 := by
    rcases hcases with h | h | h
    · exfalso
      have := Subgroup.card_dvd_of_le hUA₁
      rw [h, Cfg.card_U hc] at this
      omega
    · exfalso
      have heq : U = A ⊓ centralizer ({w} : Set G) :=
        Subgroup.eq_of_le_of_card_ge hUA₁ (by rw [h, Cfg.card_U hc])
      exact haU (by rw [heq]; exact haA₁)
    · exact h
  have hAw : ∀ g ∈ A, w * g = g * w := by
    have heq : A ⊓ centralizer ({w} : Set G) = A :=
      Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [hA₁16, Cfg.card_A hc])
    intro g hg
    have : g ∈ A ⊓ centralizer ({w} : Set G) := by rw [heq]; exact hg
    exact (mem_centralizer_singleton_iff.1 this.2).symm
  have haT : a ∈ Tsub S U := hc.c19.A_le ha
  let κ : ↥(Tsub S U) →* ↥U := OrbitData.commHom (Cfg.U_central hc) (Cfg.U_comm hc)
    (Cfg.T_comm hc) a haT
  have hκ : ∀ t : ↥(Tsub S U), ((κ t : ↥U) : G) = (t : G) * a * (t : G)⁻¹ * a⁻¹ := fun t => rfl
  have hwT : ∀ t ∈ Tsub S U, w * t * w⁻¹ ∈ Tsub S U := hTM' w hwM
  have hw3' : w * w * w = 1 := by simpa [pow_succ, mul_assoc] using hw3
  have hwa' : w⁻¹ * a * w = a := by
    rw [mul_assoc, ← hwa, ← mul_assoc, inv_mul_cancel, one_mul]
  have hwa'' : w * a * w⁻¹ = a := by rw [hwa]; group
  have hBw : ∀ b ∈ B, w * b = b * w := by
    intro b hb
    have hbT : b ∈ Tsub S U := hc.c19.B_le hb
    have hwb : w * b * w⁻¹ ∈ B := by
      have : w * b * w⁻¹ ∈ conjSub w B := by
        rw [mem_conjSub]
        have e : w⁻¹ * (w * b * w⁻¹) * w = b := by group
        rw [e]; exact hb
      rwa [hwB] at this
    have hk1 : κ ⟨w * b * w⁻¹, hwT b hbT⟩ = κ ⟨b, hbT⟩ := by
      apply Subtype.ext
      rw [hκ, hκ]
      show w * b * w⁻¹ * a * (w * b * w⁻¹)⁻¹ * a⁻¹ = b * a * b⁻¹ * a⁻¹
      have hu := hU _ (show b * a * b⁻¹ * a⁻¹ ∈ U from Cfg.T_comm hc b hbT a haT)
      have e1 : w * b * w⁻¹ * a * (w * b * w⁻¹)⁻¹ * a⁻¹ = w * (b * a * b⁻¹ * a⁻¹) * w⁻¹ := by
        calc w * b * w⁻¹ * a * (w * b * w⁻¹)⁻¹ * a⁻¹
            = w * b * (w⁻¹ * a * w) * b⁻¹ * w⁻¹ * a⁻¹ := by group
          _ = w * b * a * b⁻¹ * w⁻¹ * a⁻¹ := by rw [hwa']
          _ = w * (b * a * b⁻¹ * a⁻¹) * w⁻¹ * (w * a * w⁻¹) * a⁻¹ := by group
          _ = w * (b * a * b⁻¹ * a⁻¹) * w⁻¹ * a * a⁻¹ := by rw [hwa'']
          _ = w * (b * a * b⁻¹ * a⁻¹) * w⁻¹ := by group
      rw [e1, hu]; group
    have hk2 : κ ⟨w * b * w⁻¹ * b⁻¹, (Tsub S U).mul_mem (hwT b hbT) ((Tsub S U).inv_mem hbT)⟩ = 1 := by
      have : (⟨w * b * w⁻¹ * b⁻¹, (Tsub S U).mul_mem (hwT b hbT) ((Tsub S U).inv_mem hbT)⟩ :
          ↥(Tsub S U)) = ⟨w * b * w⁻¹, hwT b hbT⟩ * (⟨b, hbT⟩ : ↥(Tsub S U))⁻¹ := rfl
      rw [this, map_mul, map_inv, hk1, mul_inv_cancel]
    have hk3 : (w * b * w⁻¹ * b⁻¹) * a * (w * b * w⁻¹ * b⁻¹)⁻¹ * a⁻¹ = 1 := by
      have := congrArg Subtype.val hk2
      rw [hκ] at this
      exact this
    have h5 : (w * b * w⁻¹ * b⁻¹) * a = a * (w * b * w⁻¹ * b⁻¹) :=
      mul_inv_eq_iff_eq_mul.1 (mul_inv_eq_one.1 hk3)
    have hβA : w * b * w⁻¹ * b⁻¹ ∈ A := by
      rw [← hc.c19.centA a ha haU]
      exact ⟨mem_centralizer_singleton_iff.2 h5,
        (Tsub S U).mul_mem (hwT b hbT) ((Tsub S U).inv_mem hbT)⟩
    have hβB : w * b * w⁻¹ * b⁻¹ ∈ B := B.mul_mem hwb (B.inv_mem hb)
    have hβU : w * b * w⁻¹ * b⁻¹ ∈ U := by rw [← hc.c19.AB_inf]; exact ⟨hβA, hβB⟩
    set u := w * b * w⁻¹ * b⁻¹ with hu_def
    have hwu : w * u * w⁻¹ = u := by rw [hU u hβU]; group
    have e1 : w * b * w⁻¹ = u * b := by rw [hu_def]; group
    have e2 : w * (w * b * w⁻¹) * w⁻¹ = b := by
      calc w * (w * b * w⁻¹) * w⁻¹ = w * (u * b) * w⁻¹ := by rw [e1]
        _ = (w * u * w⁻¹) * (w * b * w⁻¹) := by group
        _ = u * (u * b) := by rw [hwu, e1]
        _ = (u * u) * b := by group
        _ = b := by rw [Cfg.U_sq hc u hβU]; group
    have e4 : w * (w * (w * b * w⁻¹) * w⁻¹) * w⁻¹ = b := by
      calc w * (w * (w * b * w⁻¹) * w⁻¹) * w⁻¹ = (w * w * w) * b * (w * w * w)⁻¹ := by group
        _ = b := by rw [hw3']; group
    rw [e2] at e4
    rw [mul_inv_eq_iff_eq_mul] at e4
    exact e4
  have hTw : Tsub S U ≤ centralizer ({w} : Set G) := by
    rw [← hc.c19.T_eq]
    exact sup_le (fun g hg => mem_centralizer_singleton_iff.2 (hAw g hg).symm)
      (fun g hg => mem_centralizer_singleton_iff.2 (hBw g hg).symm)
  have hwT' : w ∈ Tsub S U :=
    hCT w hwM (fun t ht => (mem_centralizer_singleton_iff.1 (hTw ht)).symm)
  have := Subgroup.orderOf_dvd_natCard (Tsub S U) hwT'
  rw [hw, Cfg.card_T hc] at this
  omega

theorem w_fpf_U (hc : Ctx19 S U M V x z A B R)
    (hTM' : ∀ m ∈ M, ∀ t ∈ Tsub S U, m * t * m⁻¹ ∈ Tsub S U)
    (hCT : ∀ m ∈ M, (∀ t ∈ Tsub S U, m * t = t * m) → m ∈ Tsub S U) {a w : G} (ha : a ∈ A)
    (haU : a ∉ U) (hwM : w ∈ M) (hwa : w * a = a * w) (hw : orderOf w = 3) :
    ∀ u ∈ U, u ≠ 1 → w * u * w⁻¹ ≠ u := by
  have hw3 : w ^ 3 = 1 := by rw [← hw]; exact pow_orderOf_eq_one w
  have hwU : w ∈ normalizer (U : Set G) :=
    Gen.mem_normalizer_of_conj_le (Cfg.U_normal_M hc hTM' w hwM)
  have hmod := modEq_three hwU hw3
  have hm1 : Nat.card ↥(U ⊓ centralizer ({w} : Set G)) % 3 = 1 := by
    have := hmod
    unfold Nat.ModEq at this
    rw [Cfg.card_U hc] at this
    omega
  have hdvd : Nat.card ↥(U ⊓ centralizer ({w} : Set G)) ∣ 4 := by
    have := Subgroup.card_dvd_of_le (inf_le_left : U ⊓ centralizer ({w} : Set G) ≤ U)
    rwa [Cfg.card_U hc] at this
  have hcases : Nat.card ↥(U ⊓ centralizer ({w} : Set G)) = 1 ∨
      Nat.card ↥(U ⊓ centralizer ({w} : Set G)) = 4 := by
    have hle := Nat.le_of_dvd (by norm_num) hdvd
    have hpos : 0 < Nat.card ↥(U ⊓ centralizer ({w} : Set G)) := Nat.card_pos
    interval_cases h : Nat.card ↥(U ⊓ centralizer ({w} : Set G)) <;> omega
  rcases hcases with h | h
  · intro u hu hu1 hfix
    have hmem : u ∈ U ⊓ centralizer ({w} : Set G) := by
      refine ⟨hu, mem_centralizer_singleton_iff.2 ?_⟩
      rw [mul_inv_eq_iff_eq_mul] at hfix
      exact hfix.symm
    have hbot : U ⊓ centralizer ({w} : Set G) = ⊥ := Subgroup.card_eq_one.1 h
    rw [hbot, Subgroup.mem_bot] at hmem
    exact hu1 hmem
  · exfalso
    apply w_not_cent_U hc hTM' hCT ha haU hwM hwa hw
    have heq : U ⊓ centralizer ({w} : Set G) = U :=
      Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [h, Cfg.card_U hc])
    intro u hu
    have : u ∈ U ⊓ centralizer ({w} : Set G) := by rw [heq]; exact hu
    exact (mem_centralizer_singleton_iff.1 this.2).symm

theorem card_A1 (hc : Ctx19 S U M V x z A B R)
    (hTM' : ∀ m ∈ M, ∀ t ∈ Tsub S U, m * t * m⁻¹ ∈ Tsub S U)
    (hCT : ∀ m ∈ M, (∀ t ∈ Tsub S U, m * t = t * m) → m ∈ Tsub S U) {a w : G} (ha : a ∈ A)
    (haU : a ∉ U) (hwM : w ∈ M) (hwa : w * a = a * w) (hw : orderOf w = 3) :
    Nat.card ↥(A ⊓ centralizer ({w} : Set G)) = 4 := by
  have hw3 : w ^ 3 = 1 := by rw [← hw]; exact pow_orderOf_eq_one w
  have hwA := conjSub_A_of_cent hc hTM' ha haU hwM hwa
  have hwN : w ∈ normalizer (A : Set G) := Cfg.mem_normalizer_of_conjSub_eq hwA
  have hmod := modEq_three hwN hw3
  have hm1 : Nat.card ↥(A ⊓ centralizer ({w} : Set G)) % 3 = 1 := by
    have := hmod
    unfold Nat.ModEq at this
    rw [Cfg.card_A hc] at this
    omega
  have hcases := card_A1_cases (inf_le_left : A ⊓ centralizer ({w} : Set G) ≤ A)
    (Cfg.card_A hc) hm1
  have haA₁ : a ∈ A ⊓ centralizer ({w} : Set G) :=
    ⟨ha, mem_centralizer_singleton_iff.2 hwa.symm⟩
  rcases hcases with h | h | h
  · exfalso
    have hbot : A ⊓ centralizer ({w} : Set G) = ⊥ := Subgroup.card_eq_one.1 h
    rw [hbot, Subgroup.mem_bot] at haA₁
    exact haU (haA₁ ▸ U.one_mem)
  · exact h
  · exfalso
    apply w_not_cent_U hc hTM' hCT ha haU hwM hwa hw
    have heq : A ⊓ centralizer ({w} : Set G) = A :=
      Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [h, Cfg.card_A hc])
    intro u hu
    have : u ∈ A ⊓ centralizer ({w} : Set G) := by rw [heq]; exact Cfg.U_le_A hc hu
    exact (mem_centralizer_singleton_iff.1 this.2).symm

omit [Finite G] in
theorem eq_one_of_sq_of_mem_zpowers {w p : G} (hw3 : w ^ 3 = 1) (hp : p ∈ zpowers w)
    (hp2 : p * p = 1) : p = 1 := by
  obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.1 hp
  have h3 : (w ^ j) ^ 3 = 1 := by
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hw3, one_zpow]
  have : (w ^ j) ^ 3 = w ^ j * (w ^ j * w ^ j) := by
    rw [pow_succ, pow_two]; group
  rw [hp2, mul_one] at this
  calc w ^ j = (w ^ j) ^ 3 := this.symm
    _ = 1 := h3

omit [Finite G] in
theorem inf_zpowers_eq_bot {K : Subgroup G} {w : G} (hw3 : w ^ 3 = 1) (hK2 : ∀ k ∈ K, k * k = 1) :
    K ⊓ zpowers w = ⊥ := by
  rw [eq_bot_iff]
  rintro g ⟨hgK, hgw⟩
  rw [Subgroup.mem_bot]
  exact eq_one_of_sq_of_mem_zpowers hw3 hgw (hK2 g hgK)

theorem zpowers_le_normalizer_U (hc : Ctx19 S U M V x z A B R)
    (hTM' : ∀ m ∈ M, ∀ t ∈ Tsub S U, m * t * m⁻¹ ∈ Tsub S U) {w : G} (hwM : w ∈ M) :
    zpowers w ≤ normalizer (U : Set G) :=
  Subgroup.zpowers_le.2 (Gen.mem_normalizer_of_conj_le (Cfg.U_normal_M hc hTM' w hwM))

theorem mem_W_iff (hc : Ctx19 S U M V x z A B R)
    (hTM' : ∀ m ∈ M, ∀ t ∈ Tsub S U, m * t * m⁻¹ ∈ Tsub S U) {w : G} (hwM : w ∈ M) {g : G} :
    g ∈ zpowers w ⊔ U ↔ ∃ p ∈ zpowers w, ∃ q ∈ U, p * q = g := by
  have h := Subgroup.coe_mul_of_left_le_normalizer_right (zpowers w) U
    (zpowers_le_normalizer_U hc hTM' hwM)
  constructor
  · intro hg
    have : g ∈ ((zpowers w : Set G) * (U : Set G)) := by rw [← h]; exact hg
    obtain ⟨p, hp, q, hq, hpq⟩ := Set.mem_mul.1 this
    exact ⟨p, hp, q, hq, hpq⟩
  · rintro ⟨p, hp, q, hq, rfl⟩
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hp) (Subgroup.mem_sup_right hq)

theorem card_W (hc : Ctx19 S U M V x z A B R)
    (hTM' : ∀ m ∈ M, ∀ t ∈ Tsub S U, m * t * m⁻¹ ∈ Tsub S U) {w : G} (hwM : w ∈ M)
    (hw : orderOf w = 3) : Nat.card ↥(zpowers w ⊔ U) = 12 := by
  have hw3 : w ^ 3 = 1 := by rw [← hw]; exact pow_orderOf_eq_one w
  have hHn : ∀ h ∈ zpowers w, ∀ k ∈ U, h * k * h⁻¹ ∈ U := fun h hh k hk =>
    (mem_normalizer_iff.1 (zpowers_le_normalizer_U hc hTM' hwM hh) k).1 hk
  have := card_sup_eq_mul hHn (inf_zpowers_eq_bot hw3 (Cfg.U_sq hc))
  rw [sup_comm, this, Nat.card_zpowers, hw, Cfg.card_U hc]

theorem A1_inf_W (hc : Ctx19 S U M V x z A B R)
    (hTM' : ∀ m ∈ M, ∀ t ∈ Tsub S U, m * t * m⁻¹ ∈ Tsub S U)
    (hCT : ∀ m ∈ M, (∀ t ∈ Tsub S U, m * t = t * m) → m ∈ Tsub S U) {a w : G} (ha : a ∈ A)
    (haU : a ∉ U) (hwM : w ∈ M) (hwa : w * a = a * w) (hw : orderOf w = 3) :
    (A ⊓ centralizer ({w} : Set G)) ⊓ (zpowers w ⊔ U) = ⊥ := by
  have hw3 : w ^ 3 = 1 := by rw [← hw]; exact pow_orderOf_eq_one w
  rw [eq_bot_iff]
  rintro g ⟨⟨hgA, hgC⟩, hgW⟩
  rw [Subgroup.mem_bot]
  obtain ⟨p, hp, q, hq, rfl⟩ := (mem_W_iff hc hTM' hwM).1 hgW
  have hpA : p ∈ A := by
    have := A.mul_mem hgA (A.inv_mem (Cfg.U_le_A hc hq))
    simpa using this
  have hp1 : p = 1 := eq_one_of_sq_of_mem_zpowers hw3 hp (Cfg.A_sq hc p hpA)
  subst hp1
  rw [one_mul] at hgC ⊢
  by_contra hq1
  refine w_fpf_U hc hTM' hCT ha haU hwM hwa hw q hq hq1 ?_
  have := mem_centralizer_singleton_iff.1 hgC
  rw [mul_inv_eq_iff_eq_mul]
  exact this.symm

theorem A1_comm_W (hc : Ctx19 S U M V x z A B R) {w : G} :
    ∀ y ∈ A ⊓ centralizer ({w} : Set G), ∀ ω ∈ zpowers w ⊔ U, y * ω = ω * y := by
  intro y hy ω hω
  have hle : zpowers w ⊔ U ≤ centralizer ((A ⊓ centralizer ({w} : Set G) : Subgroup G) : Set G) := by
    refine sup_le (Subgroup.zpowers_le.2 ?_) ?_
    · rw [mem_centralizer_iff]
      intro h hh
      exact mem_centralizer_singleton_iff.1 hh.2
    · intro u hu
      rw [mem_centralizer_iff]
      intro h hh
      exact Cfg.A_comm hc h hh.1 u (Cfg.U_le_A hc hu)
  exact mem_centralizer_iff.1 (hle hω) y hy

theorem card_A1_sup_W (hc : Ctx19 S U M V x z A B R)
    (hTM' : ∀ m ∈ M, ∀ t ∈ Tsub S U, m * t * m⁻¹ ∈ Tsub S U)
    (hCT : ∀ m ∈ M, (∀ t ∈ Tsub S U, m * t = t * m) → m ∈ Tsub S U) {a w : G} (ha : a ∈ A)
    (haU : a ∉ U) (hwM : w ∈ M) (hwa : w * a = a * w) (hw : orderOf w = 3) :
    Nat.card ↥((A ⊓ centralizer ({w} : Set G)) ⊔ (zpowers w ⊔ U)) = 48 := by
  have h := card_sup_mul_card_inf_of_commute (A ⊓ centralizer ({w} : Set G)) (zpowers w ⊔ U)
    (A1_comm_W hc)
  rw [A1_inf_W hc hTM' hCT ha haU hwM hwa hw, card_A1 hc hTM' hCT ha haU hwM hwa hw,
    card_W hc hTM' hwM hw, Subgroup.card_bot] at h
  omega

theorem cent_eq (hc : Ctx19 S U M V x z A B R) (h194M : pPrimeCore 2 ↥M = ⊥)
    (hTM' : ∀ m ∈ M, ∀ t ∈ Tsub S U, m * t * m⁻¹ ∈ Tsub S U)
    (hCT : ∀ m ∈ M, (∀ t ∈ Tsub S U, m * t = t * m) → m ∈ Tsub S U)
    (hMcard : Nat.card M = 1152) {a w : G} (ha : a ∈ A) (haU : a ∉ U) (hwM : w ∈ M)
    (hwa : w * a = a * w) (hw : orderOf w = 3) :
    centralizer ({a} : Set G) ⊓ M = (A ⊓ centralizer ({w} : Set G)) ⊔ (zpowers w ⊔ U) := by
  symm
  apply Subgroup.eq_of_le_of_card_ge
  · refine sup_le ?_ (sup_le (Subgroup.zpowers_le.2 ?_) ?_)
    · intro y hy
      exact ⟨mem_centralizer_singleton_iff.2 (Cfg.A_comm hc y hy.1 a ha),
        Cfg.S_le_M hc (Cfg.A_le_S hc hy.1)⟩
    · exact ⟨mem_centralizer_singleton_iff.2 hwa, hwM⟩
    · intro u hu
      exact ⟨mem_centralizer_singleton_iff.2 (Cfg.A_comm hc u (Cfg.U_le_A hc hu) a ha),
        Cfg.S_le_M hc (Cfg.A_le_S hc (Cfg.U_le_A hc hu))⟩
  · rw [card_cent hc h194M hTM' hMcard ha haU,
      card_A1_sup_W hc hTM' hCT ha haU hwM hwa hw]

end CM

end CFSG.GH74.Uniqueness.SU.SU9
