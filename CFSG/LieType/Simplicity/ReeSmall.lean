module

public import CFSG.LieType.Ree.ReePerfect
public import CFSG.LieType.Ree.TitsWeyl
public import CFSG.LieType.Simplicity.Torus
public import CFSG.LieType.Simplicity.RankOneQuasisimple
public import CFSG.LieType.BorelTits.DerivedQuotient

public section

namespace CFSG.LieType.Simplicity

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Chevalley.RootOps
  CFSG.LieType.Ree
open scoped commutatorElement

theorem wordProd_longWord_smul
    (t : ReeTag) (β : Root t.tag) :
    (coxeterSystem t.tag).wordProd t.longWord • β = -β := by
  apply Subtype.ext
  change (coxeterSystem t.tag).wordProd t.longWord • β.1 = -β.1
  rw [CFSG.LieType.Ree.wordProd_smul, ← root_rootPos β]
  have hlt := rootPos_lt β
  generalize rootPos β = m at hlt ⊢
  revert m
  cases t <;> decide +kernel

section Commutator

variable {t : ReeTag} {K : Type} [Field K] (a : ℕ)

theorem cartanPair_neg (j : Fin t.tag.rank) (v : Fin t.tag.rank → ℤ) :
    t.cartanPair j (-v) = -t.cartanPair j v := by
  simp [ReeTag.cartanPair, Finset.sum_neg_distrib]

theorem commutator_nrep_reeTorus_conj
    {w₀ : WeylGroup t.tag} (hw₀ : ∀ β : Root t.tag, w₀ • β = -β)
    (j : Fin t.tag.rank) (u : Kˣ) (β : Root t.tag) (c : K) :
    ⁅nrep t.tag K w₀, t.reeTorus a j u⁆ * (rootOperatorFamily t.tag).eltElement β c *
        ⁅nrep t.tag K w₀, t.reeTorus a j u⁆⁻¹ =
      (rootOperatorFamily t.tag).eltElement β
        (((u ^ (-2 * (t.cartanPair j β.1 +
          ((t.prime ^ a : ℕ) : ℤ) * t.cartanPair (t.perm j) β.1)) : Kˣ) : K) * c) := by
  obtain ⟨ε, hε, hconj⟩ := exists_conj_nrep (K := K) w₀ (-β)
  rw [hw₀ (-β), neg_neg] at hconj
  set F := rootOperatorFamily t.tag
  set n := nrep t.tag K w₀
  set T := t.reeTorus a j u
  set E := t.cartanPair j β.1 + ((t.prime ^ a : ℕ) : ℤ) * t.cartanPair (t.perm j) β.1 with hE
  have hεε : ε * ε = 1 := by rcases hε with rfl | rfl <;> ring
  have hinv : ∀ d : K, n⁻¹ * F.eltElement β d * n = F.eltElement (-β) (ε * d) := by
    intro d
    have h := hconj (ε * d)
    rw [← mul_assoc, hεε, one_mul] at h
    rw [← h]
    group
  have hTneg : ∀ d : K,
      T * F.eltElement (-β) d * T⁻¹ = F.eltElement (-β) (((u ^ (-E) : Kˣ) : K) * d) := by
    intro d
    rw [t.reeTorus_conj a j u (-β) d]
    congr 4
    change t.cartanPair j (-β.1) + ((t.prime ^ a : ℕ) : ℤ) * t.cartanPair (t.perm j) (-β.1) = -E
    rw [cartanPair_neg, cartanPair_neg, hE]
    ring
  have hTinv : ∀ d : K,
      T⁻¹ * F.eltElement β d * T = F.eltElement β (((u ^ (-E) : Kˣ) : K) * d) := by
    intro d
    have h := t.reeTorus_conj a j u β (((u ^ (-E) : Kˣ) : K) * d)
    rw [← mul_assoc, ← Units.val_mul, ← zpow_add, add_neg_cancel, zpow_zero, Units.val_one,
      one_mul] at h
    change T * F.eltElement β (((u ^ (-E) : Kˣ) : K) * d) * T⁻¹ = F.eltElement β d at h
    rw [← h]
    group
  have hsq : ((u ^ (-2 * E) : Kˣ) : K) = ((u ^ (-E) : Kˣ) : K) * ((u ^ (-E) : Kˣ) : K) := by
    rw [← Units.val_mul, ← zpow_add]
    congr 2
    ring
  rw [commutatorElement_def]
  calc n * T * n⁻¹ * T⁻¹ * F.eltElement β c * (n * T * n⁻¹ * T⁻¹)⁻¹
      = n * T * (n⁻¹ * (T⁻¹ * F.eltElement β c * T) * n) * T⁻¹ * n⁻¹ := by group
    _ = n * (T * F.eltElement (-β) (ε * (((u ^ (-E) : Kˣ) : K) * c)) * T⁻¹) * n⁻¹ := by
        rw [hTinv, hinv]
        group
    _ = F.eltElement β (ε * (((u ^ (-E) : Kˣ) : K) * (ε * (((u ^ (-E) : Kˣ) : K) * c)))) := by
        rw [hTneg, hconj]
    _ = F.eltElement β (((u ^ (-2 * E) : Kˣ) : K) * c) := by
        congr 1
        rw [hsq]
        linear_combination (((u ^ (-E) : Kˣ) : K) * ((u ^ (-E) : Kˣ) : K) * c) * hεε

theorem not_dvd_two_mul_of_goodChar {p θ A B : ℤ} (hp : 2 ≤ p) (hθ : p ≤ θ) (hA : |A| ≤ p)
    (hB : |B| ≤ p) (h : (B = 0 ∧ A ≠ 0) ∨ (B ≠ 0 ∧ |A| < p))
    (hbig : 2 * (p + θ * p) < p * θ ^ 2 - 1) : ¬ (p * θ ^ 2 - 1) ∣ (2 * (A + θ * B)) := by
  intro hd
  have hθ0 : (0 : ℤ) < θ := by linarith
  have hE : A + θ * B ≠ 0 := by
    rcases h with ⟨rfl, hA0⟩ | ⟨hB0, hAp⟩
    · simpa using hA0
    · intro h0
      have h1 : |θ * B| = |A| := by rw [show θ * B = -A by linarith, abs_neg]
      rw [abs_mul, abs_of_pos hθ0] at h1
      have hB1 : 1 ≤ |B| := Int.one_le_abs hB0
      nlinarith
  have hlt : |2 * (A + θ * B)| < p * θ ^ 2 - 1 := by
    have h1 : |A + θ * B| ≤ |A| + θ * |B| := by
      calc |A + θ * B| ≤ |A| + |θ * B| := abs_add_le _ _
        _ = |A| + θ * |B| := by rw [abs_mul, abs_of_pos hθ0]
    have h2 : θ * |B| ≤ θ * p := mul_le_mul_of_nonneg_left hB hθ0.le
    rw [abs_mul, abs_two]
    linarith
  have h0 := Int.eq_zero_of_abs_lt_dvd hd hlt
  exact hE (by linarith)

theorem exists_two_mul_char_ne_one
    (hK : Nat.card K = t.prime ^ (2 * a + 1))
    (hbig : 2 * ((t.prime : ℤ) + ((t.prime ^ a : ℕ) : ℤ) * t.prime) <
      t.prime * ((t.prime ^ a : ℕ) : ℤ) ^ 2 - 1)
    {u : Kˣ} (hu : orderOf u = Nat.card K - 1) (β : Root t.tag) (hβ : 0 < height β.1) :
    ∃ j ∈ t.longSet, ((u ^ (-2 * (t.cartanPair j β.1 +
      ((t.prime ^ a : ℕ) : ℤ) * t.cartanPair (t.perm j) β.1)) : Kˣ) : K) ≠ 1 := by
  have hm := t.charCheck (rootPos β) (rootPos_lt β) (by rw [root_rootPos]; exact hβ)
  rw [root_rootPos] at hm
  obtain ⟨j, hj, hA, hB, hcase⟩ := hm
  refine ⟨j, hj, fun h1 => ?_⟩
  rw [Units.val_eq_one, ← orderOf_dvd_iff_zpow_eq_one, hu, hK] at h1
  have hp2 : (2 : ℤ) ≤ t.prime := by cases t <;> decide
  have hθ : (t.prime : ℤ) ≤ ((t.prime ^ a : ℕ) : ℤ) := by
    rcases Nat.eq_zero_or_pos a with rfl | ha
    · exfalso
      simp only [pow_zero, Nat.cast_one] at hbig
      nlinarith
    · exact Nat.cast_le.mpr (Nat.le_self_pow (by omega) t.prime)
  refine not_dvd_two_mul_of_goodChar hp2 hθ hA hB hcase hbig ?_
  have h1p : 1 ≤ t.prime ^ (2 * a + 1) := Nat.one_le_pow _ _ (by cases t <;> decide)
  have e : ((t.prime ^ (2 * a + 1) - 1 : ℕ) : ℤ) =
      (t.prime : ℤ) * ((t.prime ^ a : ℕ) : ℤ) ^ 2 - 1 := by
    rw [Nat.cast_sub h1p]
    push_cast
    ring
  rw [e] at h1
  have := h1.neg_right
  rw [neg_mul, neg_neg] at this
  exact this

variable [Finite K] [CharP K t.prime]

omit [CharP K t.prime] in
theorem conj_mem_H_of_mem_N
    {m h : adjointGroup t.tag K} (hm : m ∈ (nativeData t.tag K).N)
    (hh : h ∈ (nativeData t.tag K).H) : m * h * m⁻¹ ∈ (nativeData t.tag K).H := by
  obtain ⟨k, hk, rfl⟩ := (RootGroupData.mem_H_iff (D := nativeData t.tag K)).mp hh
  set m' : (nativeData t.tag K).N := ⟨m, hm⟩
  refine (RootGroupData.mem_H_iff (D := nativeData t.tag K)).mpr ⟨m' * k * m'⁻¹, ?_, rfl⟩
  rw [map_mul, map_mul, hk, mul_one, map_inv, mul_inv_cancel]

omit [CharP K t.prime] in
theorem nrep_conj_mem_H
    (w : WeylGroup t.tag) {h : adjointGroup t.tag K}
    (hh : h ∈ (nativeData t.tag K).H) :
    nrep t.tag K w * h * (nrep t.tag K w)⁻¹ ∈ (nativeData t.tag K).H :=
  conj_mem_H_of_mem_N (nrep_mem_monomialGroup t.tag K w) hh

omit [CharP K t.prime] in
theorem eq_one_of_mem_U_of_forall_commutator
    (hK : Nat.card K = t.prime ^ (2 * a + 1))
    (hbig : 2 * ((t.prime : ℤ) + ((t.prime ^ a : ℕ) : ℤ) * t.prime) <
      t.prime * ((t.prime ^ a : ℕ) : ℤ) ^ 2 - 1)
    {w₀ : WeylGroup t.tag} (hw₀ : ∀ β : Root t.tag, w₀ • β = -β) {u : Kˣ}
    (hu : orderOf u = Nat.card K - 1) {x : adjointGroup t.tag K}
    (hx : x ∈ (nativeData t.tag K).U)
    (hc : ∀ j ∈ t.longSet, ⁅nrep t.tag K w₀, t.reeTorus a j u⁆ * x *
      ⁅nrep t.tag K w₀, t.reeTorus a j u⁆⁻¹ = x) : x = 1 :=
  eq_one_of_mem_U_of_forall_commute
    (A := {h | ∃ j ∈ t.longSet, h = ⁅nrep t.tag K w₀, t.reeTorus a j u⁆})
    (by
      rintro _ ⟨j, -, rfl⟩
      rw [commutatorElement_def]
      exact mul_mem (nrep_conj_mem_H w₀ (t.reeTorus_mem_H a j u))
        (inv_mem (t.reeTorus_mem_H a j u)))
    (fun β hβ y hy hyc => by
      obtain ⟨j, hj, hne⟩ := exists_two_mul_char_ne_one a hK hbig hu β hβ
      exact eq_one_of_conj_eltElement hne (commutator_nrep_reeTorus_conj a hw₀ j u β) hy
        (hyc _ ⟨j, hj, rfl⟩))
    t.isReduced_longWord t.negCheck_longWord hx (by rintro _ ⟨j, hj, rfl⟩; exact hc j hj)

end Commutator

section Derived

variable {t : ReeTag} {K : Type} [Field K] [Finite K] [CharP K t.prime] (a : ℕ)

variable (t K) in
noncomputable abbrev reeBorelPart :
    Subgroup (reeFixed t K a) :=
  (nativeData t.tag K).B.comap (reeFixed t K a).subtype

theorem reeUnipPart_le_commutator
    (ha : 1 ≤ a) (hK : Nat.card K = t.prime ^ (2 * a + 1)) :
    reeUnipPart t K a ≤ commutator (reeFixed t K a) := by
  intro x hx
  obtain ⟨y, hy, hyx⟩ := reeFixed_U_le_derived t K a ha hK x hx x.2
  rwa [Subtype.ext hyx] at hy

theorem reeUnipPart_le_derivedSeries_two
    (ha : 1 ≤ a) (hK : Nat.card K = t.prime ^ (2 * a + 1))
    (hbig : 2 * ((t.prime : ℤ) + ((t.prime ^ a : ℕ) : ℤ) * t.prime) <
      t.prime * ((t.prime ^ a : ℕ) : ℤ) ^ 2 - 1)
    {w₀ : WeylGroup t.tag} (hw₀ : ∀ β : Root t.tag, w₀ • β = -β)
    (hw₀F : nrep t.tag K w₀ ∈ reeFixed t K a) :
    reeUnipPart t K a ≤ derivedSeries (reeFixed t K a) 2 := by
  let _ := reeConjAction t K a
  set A₂ : Subgroup (reeTorusPart t K a) :=
    (commutator (reeFixed t K a)).comap (reeTorusPart t K a).subtype with hA₂
  let _ : MulDistribMulAction A₂ (reeUnipPart t K a) :=
    MulDistribMulAction.compHom _ A₂.subtype
  obtain ⟨u₀, hu₀⟩ := ReeTag.exists_orderOf_eq_card_sub_one (K := K)
  have hcj : ∀ j ∈ t.longSet, ∃ c : A₂, (((c : reeTorusPart t K a) : reeFixed t K a) :
      adjointGroup t.tag K) = ⁅nrep t.tag K w₀, t.reeTorus a j u₀⁆ := by
    intro j hj
    have hT := t.reeTorus_mem_reeFixed a hK hj u₀
    set nΓ : reeFixed t K a := ⟨nrep t.tag K w₀, hw₀F⟩
    set TΓ : reeFixed t K a := ⟨t.reeTorus a j u₀, hT⟩
    have hmemH : ((⁅nΓ, TΓ⁆ : reeFixed t K a) : adjointGroup t.tag K) ∈
        (nativeData t.tag K).H := by
      change ⁅nrep t.tag K w₀, t.reeTorus a j u₀⁆ ∈ _
      rw [commutatorElement_def]
      exact mul_mem (nrep_conj_mem_H w₀ (t.reeTorus_mem_H a j u₀))
        (inv_mem (t.reeTorus_mem_H a j u₀))
    exact ⟨⟨⟨⁅nΓ, TΓ⁆, hmemH⟩,
      Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _)⟩, rfl⟩
  have hfix : CFSG.fixedPointSubgroup A₂ (reeUnipPart t K a) = ⊥ := by
    rw [eq_bot_iff]
    intro s hs
    have h1 : ((s : reeFixed t K a) : adjointGroup t.tag K) = 1 :=
      eq_one_of_mem_U_of_forall_commutator a hK hbig hw₀ hu₀ s.2 fun j hj => by
        obtain ⟨c, hc⟩ := hcj j hj
        have h2 := congrArg (fun z : reeUnipPart t K a =>
          ((z : reeFixed t K a) : adjointGroup t.tag K)) (hs c)
        rw [← hc]
        exact h2
    exact (Subgroup.mem_bot).2 (Subtype.ext (Subtype.ext h1))
  have hSp : IsPGroup t.prime (reeUnipPart t K a) :=
    ((nativeRootSubgroups t.tag K).isPGroup_U t.prime).comap_of_injective _
      Subtype.val_injective
  have hsolv : Group.IsSolvable (reeUnipPart t K a) := by
    have := hSp.isNilpotent
    infer_instance
  have hcop : Nat.Coprime (Nat.card A₂) (Nat.card (reeUnipPart t K a)) := by
    obtain ⟨n, hn⟩ := IsPGroup.iff_card.1 hSp
    rw [hn]
    refine Nat.Coprime.pow_right n ?_
    have hH := (nativeRootSubgroups t.tag K).coprime_card_H t.prime
    have h1 : Nat.card A₂ ∣ Nat.card (reeTorusPart t K a) := Subgroup.card_subgroup_dvd_card A₂
    have h2 : Nat.card (reeTorusPart t K a) ∣ Nat.card (nativeData t.tag K).H := by
      rw [← Subgroup.card_map_of_injective (f := (reeFixed t K a).subtype)
        Subtype.val_injective]
      exact Subgroup.card_dvd_of_le (Subgroup.map_comap_le _ _)
    exact Nat.Coprime.coprime_dvd_left (h1.trans h2) hH
  have htop := CFSG.fixedPointSubgroup_sup_commutatorAction_eq_top_of_solvable_coprime hsolv hcop
  rw [hfix, bot_sup_eq] at htop
  intro x hx
  have hle : CFSG.commutatorAction (A := A₂) (G := reeUnipPart t K a) ≤
      (derivedSeries (reeFixed t K a) 2).comap (reeUnipPart t K a).subtype := by
    rw [CFSG.commutatorAction_eq_closure, Subgroup.closure_le]
    rintro _ ⟨c, g, rfl⟩
    rw [SetLike.mem_coe, Subgroup.mem_comap, derivedSeries_succ, derivedSeries_one]
    have hg : (g : reeFixed t K a) ∈ commutator (reeFixed t K a) :=
      reeUnipPart_le_commutator a ha hK g.2
    have hc : ((c : reeTorusPart t K a) : reeFixed t K a) ∈ commutator (reeFixed t K a) := c.2
    have := Subgroup.commutator_mem_commutator (inv_mem hg) hc
    convert this using 1
    rw [commutatorElement_def, inv_inv]
    change (g : reeFixed t K a)⁻¹ * (((c : reeTorusPart t K a) : reeFixed t K a) *
      (g : reeFixed t K a) * ((c : reeTorusPart t K a) : reeFixed t K a)⁻¹) = _
    simp only [mul_assoc]
  exact hle (htop ▸ Subgroup.mem_top (⟨x, hx⟩ : reeUnipPart t K a))

theorem longWord_mem_relWeylRee
    (t : ReeTag) :
    (coxeterSystem t.tag).wordProd t.longWord ∈ t.relWeylRee := by
  rw [ReeTag.mem_relWeylRee, ReeTag.weylPerm_wordProd]
  refine ext_single fun k => ?_
  rw [CFSG.LieType.Ree.wordProd_smul, CFSG.LieType.Ree.wordProd_smul]
  revert k
  cases t <;> decide +kernel

variable (t K) in
noncomputable abbrev reeLongRep :
    reeFixed t K a :=
  ⟨nrep t.tag K ((coxeterSystem t.tag).wordProd t.longWord),
    nrep_mem_reeFixed t K a (longWord_mem_relWeylRee t)⟩

omit [CharP K t.prime] in
theorem eq_one_of_nrep_longWord_conj_mem_B
    {u : adjointGroup t.tag K}
    (hu : u ∈ (nativeData t.tag K).U)
    (h : nrep t.tag K ((coxeterSystem t.tag).wordProd t.longWord) * u *
      (nrep t.tag K ((coxeterSystem t.tag).wordProd t.longWord))⁻¹ ∈ (nativeData t.tag K).B) :
    u = 1 := by
  rw [← Uminus_eq_U_of_negCheck (K := K) t.negCheck_longWord] at hu
  have h1 := nrep_conj_mem_Uneg hu
  have h2 : nrep t.tag K ((coxeterSystem t.tag).wordProd t.longWord) * u *
      (nrep t.tag K ((coxeterSystem t.tag).wordProd t.longWord))⁻¹ ∈
        (nativeData t.tag K).B ⊓ Uneg t.tag K := ⟨h, h1⟩
  rw [nativeData_B_inf_Uneg, Subgroup.mem_bot, conj_eq_one_iff] at h2
  exact h2

theorem wordProd_longWord_ne_one
    (t : ReeTag) :
    (coxeterSystem t.tag).wordProd t.longWord ≠ 1 := by
  intro h
  have key : ∀ β : Root t.tag, β = -β := fun β => by
    have h1 := wordProd_longWord_smul t β
    rwa [h, one_smul] at h1
  cases t with
  | G2 =>
    have h2 := congrFun (congrArg Subtype.val (key ⟨Pi.single (0 : Fin 2) 1,
      isRoot_single Tag.G2 (0 : Fin 2)⟩)) (0 : Fin 2)
    change (Pi.single (0 : Fin 2) (1 : ℤ) : Fin 2 → ℤ) 0 =
      -((Pi.single (0 : Fin 2) (1 : ℤ) : Fin 2 → ℤ) 0) at h2
    rw [Pi.single_eq_same] at h2
    omega
  | F4 =>
    have h2 := congrFun (congrArg Subtype.val (key ⟨Pi.single (0 : Fin 4) 1,
      isRoot_single Tag.F4 (0 : Fin 4)⟩)) (0 : Fin 4)
    change (Pi.single (0 : Fin 4) (1 : ℤ) : Fin 4 → ℤ) 0 =
      -((Pi.single (0 : Fin 4) (1 : ℤ) : Fin 4 → ℤ) 0) at h2
    rw [Pi.single_eq_same] at h2
    omega

theorem reeUnipPart_ne_bot :
    reeUnipPart t K a ≠ ⊥ := by
  obtain ⟨u, hu, hF, hn⟩ := reeFixed_hUw t K a _ (longWord_mem_relWeylRee t)
    (wordProd_longWord_ne_one t)
  intro hbot
  have : (⟨u, hF⟩ : reeFixed t K a) ∈ reeUnipPart t K a := hu
  rw [hbot, Subgroup.mem_bot] at this
  have hu1 : u = 1 := congrArg Subtype.val this
  rw [hu1, mul_one, mul_inv_cancel] at hn
  exact hn (one_mem _)

theorem isMulCommutative_reeTorusPart :
    IsMulCommutative (reeTorusPart t K a) :=
  ⟨⟨fun x y => Subtype.ext (Subtype.ext (commute_of_mem_H x.2 y.2).eq)⟩⟩

theorem exists_mul_of_mem_reeBorelPart
    {b : reeFixed t K a} (hb : b ∈ reeBorelPart t K a) :
    ∃ s ∈ reeUnipPart t K a, ∃ c ∈ reeTorusPart t K a, b = s * c := by
  obtain ⟨u, hu, huF, h, hh, hhF, hbuh⟩ := exists_mul_of_mem_B_of_mem_reeFixed a hb b.2
  exact ⟨⟨u, huF⟩, hu, ⟨h, hhF⟩, hh, Subtype.ext hbuh⟩

end Derived

section G2

variable {K : Type} [Field K] [Finite K] [CharP K ReeTag.G2.prime] (a : ℕ)

theorem eq_one_or_eq_of_mem_relWeylRee_G2
    {w : WeylGroup ReeTag.G2.tag}
    (hw : w ∈ ReeTag.G2.relWeylRee) :
    w = 1 ∨ w = (coxeterSystem ReeTag.G2.tag).wordProd ReeTag.G2.longWord := by
  have hcl := ReeTag.G2.mem_closure_blockElt _ w rfl ((ReeTag.mem_relWeylRee _).1 hw)
  set w₀ := (coxeterSystem ReeTag.G2.tag).wordProd ReeTag.G2.longWord
  have hgen : ∀ i, ReeTag.G2.blockElt i = w₀ := by
    intro i
    fin_cases i <;> rfl
  have hsq : w₀ * w₀ = 1 := by
    rw [← hgen (0 : Fin 2)]
    exact ReeTag.G2.blockElt_mul_self (0 : Fin 2)
  clear hw
  induction hcl using Subgroup.closure_induction with
  | mem x hx =>
    obtain ⟨i, rfl⟩ := hx
    exact .inr (hgen i)
  | one => exact .inl rfl
  | mul x y _ _ hx hy =>
    rcases hx with rfl | rfl <;> rcases hy with rfl | rfl
    · exact .inl (one_mul 1)
    · exact .inr (one_mul _)
    · exact .inr (mul_one _)
    · exact .inl hsq
  | inv x _ hx =>
    rcases hx with rfl | rfl
    · exact .inl inv_one
    · exact .inr (inv_eq_of_mul_eq_one_right hsq)

theorem reeFixed_G2_bruhat
    (g : reeFixed ReeTag.G2 K a) :
    g ∈ reeBorelPart ReeTag.G2 K a ∨
      ∃ b₁ ∈ reeBorelPart ReeTag.G2 K a, ∃ b₂ ∈ reeBorelPart ReeTag.G2 K a,
          g = b₁ * reeLongRep ReeTag.G2 K a * b₂ := by
  obtain ⟨w, hw, b₁, hb₁, hb₁F, b₂, hb₂, hb₂F, hg⟩ := reeFixed_bruhat ReeTag.G2 K a g g.2
  rcases eq_one_or_eq_of_mem_relWeylRee_G2 hw with rfl | rfl
  · left
    rw [nrep_one, mul_one] at hg
    change (g : adjointGroup ReeTag.G2.tag K) ∈ (nativeData ReeTag.G2.tag K).B
    rw [hg]
    exact mul_mem hb₁ hb₂
  · exact .inr ⟨⟨b₁, hb₁F⟩, hb₁, ⟨b₂, hb₂F⟩, hb₂, Subtype.ext hg⟩

theorem normalClosure_sup_reeTorusPart_G2 :
    Subgroup.normalClosure (reeUnipPart ReeTag.G2 K a : Set (reeFixed ReeTag.G2 K a)) ⊔
      reeTorusPart ReeTag.G2 K a = ⊤ := by
  set R := Subgroup.normalClosure (reeUnipPart ReeTag.G2 K a : Set (reeFixed ReeTag.G2 K a))
  have hB : ∀ b ∈ reeBorelPart ReeTag.G2 K a, b ∈ R ⊔ reeTorusPart ReeTag.G2 K a := by
    intro b hb
    obtain ⟨s, hs, c, hc, rfl⟩ := exists_mul_of_mem_reeBorelPart a hb
    exact mul_mem (Subgroup.mem_sup_left (Subgroup.subset_normalClosure hs))
      (Subgroup.mem_sup_right hc)
  set n := reeLongRep ReeTag.G2 K a
  obtain ⟨u, hu, hu1⟩ := (Subgroup.bot_or_exists_ne_one _).resolve_left
    (reeUnipPart_ne_bot (t := ReeTag.G2) (K := K) a)
  have hv : n * u * n⁻¹ ∈ R :=
    Subgroup.normalClosure_normal.conj_mem u (Subgroup.subset_normalClosure hu) n
  have hn : n ∈ R ⊔ reeTorusPart ReeTag.G2 K a := by
    rcases reeFixed_G2_bruhat a (n * u * n⁻¹) with h | ⟨b₁, hb₁, b₂, hb₂, h⟩
    · exact absurd (Subtype.ext (eq_one_of_nrep_longWord_conj_mem_B (t := ReeTag.G2) hu h)) hu1
    · rw [show reeLongRep ReeTag.G2 K a = n from rfl] at h
      have e : n = b₁⁻¹ * (n * u * n⁻¹) * b₂⁻¹ := by
        rw [h]
        group
      rw [e]
      exact mul_mem (mul_mem (inv_mem (hB b₁ hb₁)) (Subgroup.mem_sup_left hv))
        (inv_mem (hB b₂ hb₂))
  rw [eq_top_iff]
  intro g _
  rcases reeFixed_G2_bruhat a g with h | ⟨b₁, hb₁, b₂, hb₂, rfl⟩
  · exact hB g h
  · exact mul_mem (mul_mem (hB b₁ hb₁) hn) (hB b₂ hb₂)

theorem commutator_le_normalClosure_G2 :
    commutator (reeFixed ReeTag.G2 K a) ≤
      Subgroup.normalClosure (reeUnipPart ReeTag.G2 K a : Set (reeFixed ReeTag.G2 K a)) :=
  have := isMulCommutative_reeTorusPart (t := ReeTag.G2) (K := K) a
  Subgroup.Normal.commutator_le_of_self_sup_commutative_eq_top
    (normalClosure_sup_reeTorusPart_G2 a) this

theorem two_mul_lt_G2 {a : ℕ} (ha : 1 ≤ a) :
    2 * ((ReeTag.G2.prime : ℤ) + ((ReeTag.G2.prime ^ a : ℕ) : ℤ) * ReeTag.G2.prime) <
      ReeTag.G2.prime * ((ReeTag.G2.prime ^ a : ℕ) : ℤ) ^ 2 - 1 := by
  have h3 : (3 : ℤ) ≤ ((3 ^ a : ℕ) : ℤ) := by exact_mod_cast Nat.le_self_pow (by omega) 3
  change 2 * ((3 : ℤ) + ((3 ^ a : ℕ) : ℤ) * 3) < 3 * ((3 ^ a : ℕ) : ℤ) ^ 2 - 1
  nlinarith

theorem isPerfect_commutator_reeFixed_G2
    (ha : 1 ≤ a)
    (hK : Nat.card K = ReeTag.G2.prime ^ (2 * a + 1)) :
    Group.IsPerfect (commutator (reeFixed ReeTag.G2 K a)) :=
  isPerfect_commutator_of_le
    (reeUnipPart_le_derivedSeries_two a ha hK (two_mul_lt_G2 ha)
      (wordProd_longWord_smul ReeTag.G2) (reeLongRep ReeTag.G2 K a).2)
    (commutator_le_normalClosure_G2 a)

theorem isQuasisimple_commutator_reeFixed_G2
    (ha : 1 ≤ a)
    (hK : Nat.card K = ReeTag.G2.prime ^ (2 * a + 1)) :
    IsQuasisimple (commutator (reeFixed ReeTag.G2 K a)) := by
  set Γ := reeFixed ReeTag.G2 K a
  set n := reeLongRep ReeTag.G2 K a
  have hSD : reeUnipPart ReeTag.G2 K a ≤ commutator Γ := reeUnipPart_le_commutator a ha hK
  have hRD : Subgroup.normalClosure (reeUnipPart ReeTag.G2 K a : Set Γ) ≤ commutator Γ :=
    Subgroup.normalClosure_le_normal hSD
  have hn : n ∈ Subgroup.normalClosure (reeUnipPart ReeTag.G2 K a : Set Γ) ⊔
      reeTorusPart ReeTag.G2 K a :=
    (normalClosure_sup_reeTorusPart_G2 (K := K) a).symm ▸ Subgroup.mem_top n
  obtain ⟨n', hn', a₀, ha₀, hna⟩ := Subgroup.mem_sup_of_normal_left.1 hn
  have hn'D : n' ∈ commutator Γ := hRD hn'
  have hnA : ∀ c ∈ reeTorusPart ReeTag.G2 K a, n⁻¹ * c * n ∈ reeTorusPart ReeTag.G2 K a := by
    intro c hc
    have h := conj_mem_H_of_mem_N (inv_mem (nrep_mem_monomialGroup ReeTag.G2.tag K
      ((coxeterSystem ReeTag.G2.tag).wordProd ReeTag.G2.longWord))) hc
    rw [inv_inv] at h
    exact h
  have : Group.IsSolvable (nativeData ReeTag.G2.tag K).B := isSolvable_B ReeTag.G2.prime
  let f : ↥(reeBorelPart ReeTag.G2 K a ⊓ commutator Γ) →* ↥(nativeData ReeTag.G2.tag K).B :=
    MonoidHom.codRestrict (Γ.subtype.comp (reeBorelPart ReeTag.G2 K a ⊓ commutator Γ).subtype) _
      fun x => x.2.1
  have hf : Function.Injective f := fun x y h =>
    Subtype.ext (Subtype.ext (congrArg (fun z : ↥(nativeData ReeTag.G2.tag K).B =>
      (z : adjointGroup ReeTag.G2.tag K)) h))
  refine isQuasisimple_of_rankOne_subgroup (B := reeBorelPart ReeTag.G2 K a ⊓ commutator Γ)
    (U := reeUnipPart ReeTag.G2 K a) hn'D inf_le_right hSD (fun g hg => ?_)
    (isPerfect_commutator_reeFixed_G2 a ha hK)
    (Group.isSolvable_of_isSolvable_injective hf) (fun b hb u hu => ?_) (fun u hu h => ?_)
    (reeUnipPart_ne_bot a)
  · exact bruhat_of_le (reeFixed_G2_bruhat a) hSD (Subgroup.comap_mono RootGroupData.U_le_B)
      (Subgroup.comap_mono RootGroupData.H_le_B) (fun b hb => exists_mul_of_mem_reeBorelPart a hb)
      hnA hn'D ha₀ hna.symm hg
  · exact (Subgroup.mem_normalizer_iff.mp
      ((nativeRootSubgroups ReeTag.G2.tag K).B_le_normalizer_U hb.1) _).mp hu
  · have hn'eq : n' = n * a₀⁻¹ := by
      rw [← hna]
      group
    have hu' : ((a₀⁻¹ * u * a₀ : Γ) : adjointGroup ReeTag.G2.tag K) ∈
        (nativeData ReeTag.G2.tag K).U := by
      have h1 := (Subgroup.mem_normalizer_iff.mp
        (RootGroupData.H_le_normalizer_U (D := nativeData ReeTag.G2.tag K) (inv_mem ha₀)) _).mp hu
      rw [inv_inv] at h1
      exact h1
    have h' : ((n * (a₀⁻¹ * u * a₀) * n⁻¹ : Γ) : adjointGroup ReeTag.G2.tag K) ∈
        (nativeData ReeTag.G2.tag K).B := by
      have e : n * (a₀⁻¹ * u * a₀) * n⁻¹ = n' * u * n'⁻¹ := by
        rw [hn'eq]
        group
      rw [e]
      exact h.1
    have h1 : a₀⁻¹ * u * a₀ = 1 :=
      Subtype.ext (eq_one_of_nrep_longWord_conj_mem_B (t := ReeTag.G2) hu' h')
    calc u = a₀ * (a₀⁻¹ * u * a₀) * a₀⁻¹ := by group
      _ = 1 := by rw [h1]; group

end G2

theorem fam_2g2_simplicity
    (G : Type) [Group G] (p f : ℕ)
    (h : CFSG.Blueprint.ReeTitsModel G .twistedG2 p f) : Nontrivial G ∧ IsSimpleGroup G := by
  obtain ⟨hadm, a, hf, hmodel⟩ := h
  obtain ⟨-, -, -, hp, -, h3⟩ := hadm
  subst hp
  obtain ⟨K, _, _, hK, ⟨e⟩⟩ := hmodel
  have : Fact (Nat.Prime 3) := ⟨by decide⟩
  have hc : CharP K 3 := by
    have := Fintype.ofFinite K
    exact charP_of_card_eq_prime_pow (by rw [← Nat.card_eq_fintype_card, hK])
  have : CharP K ReeTag.G2.prime := hc
  have hK' : Nat.card K = ReeTag.G2.prime ^ (2 * a + 1) := by
    rw [hK, hf]
    rfl
  have hQ := isQuasisimple_commutator_reeFixed_G2 a (by omega) hK'
  have e' := e.trans (CFSG.LieType.BorelTits.derivedCentralQuotientEquiv _
    ((MulEquiv.subgroupCongr (reeFixedGroup_eq_map_reeFixed ReeTag.G2 K a)).trans
      ((reeFixed ReeTag.G2 K a).equivMapOfInjective _ Subtype.val_injective).symm))
  have := hQ.2.1
  have : Nontrivial G := e'.toEquiv.nontrivial
  exact ⟨inferInstance, IsSimpleGroup.isSimpleGroup_of_surjective e'.symm.toMonoidHom
    e'.symm.surjective⟩

end CFSG.LieType.Simplicity
