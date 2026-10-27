module

public import CFSG.Goldschmidt.Steps.G3b35L2

public section

namespace CFSG.Goldschmidt.G3b

open CFSG.Open CFSG.Walter CFSG.GorensteinWalter
open scoped MatrixGroups

section Restrict

variable {X : Type*} [Group X]

theorem fix_centralizer_of_fix {t : X} (ht : orderOf t = 2) {E : Subgroup X}
    (hEn : (E.subgroupOf (Subgroup.centralizer ({t} : Set X))).Normal)
    (hEC : E ≤ Subgroup.centralizer ({t} : Set X))
    (hCE : Subgroup.centralizer ({t} : Set X) ⊓ Subgroup.centralizer (E : Set X) =
      Subgroup.zpowers t)
    (β : MulAut X) (hβ : Odd (orderOf β)) (hβt : β t = t) (hβE : ∀ x ∈ E, β x = x) :
    ∀ c ∈ Subgroup.centralizer ({t} : Set X), β c = c := by
  intro c hc
  have htt : t * t = 1 := by rw [← pow_two, ← ht, pow_orderOf_eq_one]
  have hCtE : Subgroup.centralizer ({t} : Set X) ≤ Subgroup.normalizer (E : Set X) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hEC).mp hEn
  have hβc : β c ∈ Subgroup.centralizer ({t} : Set X) := by
    rw [Subgroup.mem_centralizer_singleton_iff] at hc ⊢
    rw [← hβt, ← map_mul, hc, map_mul]
  have hτ : c⁻¹ * β c ∈ Subgroup.centralizer ({t} : Set X) ⊓
      Subgroup.centralizer (E : Set X) := by
    refine Subgroup.mem_inf.mpr ⟨Subgroup.mul_mem _ (Subgroup.inv_mem _ hc) hβc, ?_⟩
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    have hcx : c * x * c⁻¹ ∈ E := (Subgroup.mem_normalizer_iff.mp (hCtE hc) x).mp hx
    have h1 : β (c * x * c⁻¹) = c * x * c⁻¹ := hβE _ hcx
    rw [map_mul, map_mul, map_inv, hβE x hx] at h1
    calc x * (c⁻¹ * β c) = c⁻¹ * (c * x * c⁻¹) * β c := by group
      _ = c⁻¹ * (β c * x * (β c)⁻¹) * β c := by rw [h1]
      _ = c⁻¹ * β c * x := by group
  rw [hCE] at hτ
  have h2 : (β ^ 2) c = c := by
    rcases eq_one_or_eq_of_mem_zpowers ht hτ with h | h
    · have hc' : β c = c := by
        rw [inv_mul_eq_one] at h
        exact h.symm
      rw [pow_two, MulAut.mul_apply, hc', hc']
    · have hc' : β c = c * t := by
        rw [inv_mul_eq_iff_eq_mul] at h
        exact h
      rw [pow_two, MulAut.mul_apply, hc', map_mul, hc', hβt, mul_assoc, htt, mul_one]
  obtain ⟨k, hk⟩ := mem_zpowers_sq_of_odd hβ
  rw [← hk]
  have : ∀ n : ℤ, ((β ^ 2) ^ n) c = c := by
    intro n
    induction n using Int.induction_on with
    | zero => rfl
    | succ n ih => rw [zpow_add_one, MulAut.mul_apply, h2, ih]
    | pred n ih =>
      rw [zpow_sub_one, MulAut.mul_apply]
      have h3 : (β ^ 2)⁻¹ c = c := by
        conv_lhs => rw [← h2]
        exact MulAut.inv_apply_self _ _ _
      rw [h3, ih]
  exact this k

theorem mem_of_fix_of_mem [Finite X] {t : X} (ht : orderOf t = 2) {E : Subgroup X}
    (hEn : (E.subgroupOf (Subgroup.centralizer ({t} : Set X))).Normal)
    (hEC : E ≤ Subgroup.centralizer ({t} : Set X))
    (hCE : Subgroup.centralizer ({t} : Set X) ⊓ Subgroup.centralizer (E : Set X) =
      Subgroup.zpowers t)
    [IsSimpleGroup E] (hE3 : 2 < Nat.card E) (θ : MulAut X) (hθt : θ t = t) :
    ∀ x ∈ E, θ x ∈ E := by
  classical
  have hCtE : Subgroup.centralizer ({t} : Set X) ≤ Subgroup.normalizer (E : Set X) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hEC).mp hEn
  have hθinvt : θ⁻¹ t = t := by
    conv_lhs => rw [← hθt]
    exact MulAut.inv_apply_self _ _ _
  have hfixC : ∀ β : MulAut X, β t = t → ∀ c ∈ Subgroup.centralizer ({t} : Set X),
      β c ∈ Subgroup.centralizer ({t} : Set X) := by
    intro β hβ c hc
    rw [Subgroup.mem_centralizer_singleton_iff] at hc ⊢
    rw [← hβ, ← map_mul, hc, map_mul]
  set E' := E.map θ.toMonoidHom with hE'
  have hE'C : E' ≤ Subgroup.centralizer ({t} : Set X) := by
    rintro _ ⟨x, hx, rfl⟩
    exact hfixC θ hθt x (hEC hx)
  have hE'norm : ∀ c ∈ Subgroup.centralizer ({t} : Set X), ∀ x ∈ E', c * x * c⁻¹ ∈ E' := by
    rintro c hc _ ⟨x, hx, rfl⟩
    have hc' : θ⁻¹ c ∈ Subgroup.centralizer ({t} : Set X) := hfixC θ⁻¹ hθinvt c hc
    refine ⟨θ⁻¹ c * x * (θ⁻¹ c)⁻¹, (Subgroup.mem_normalizer_iff.mp (hCtE hc') x).mp hx, ?_⟩
    simp
  have hcard : Nat.card E' = Nat.card E :=
    Subgroup.card_map_of_injective θ.injective
  have hD : ((E ⊓ E').subgroupOf E).Normal := by
    constructor
    intro d hd e
    rw [Subgroup.mem_subgroupOf] at hd ⊢
    refine Subgroup.mem_inf.mpr ⟨E.mul_mem (E.mul_mem e.2 (Subgroup.mem_inf.mp hd).1)
      (E.inv_mem e.2), ?_⟩
    exact hE'norm e (hEC e.2) d (Subgroup.mem_inf.mp hd).2
  have hEE' : E ≤ E' := by
    rcases (haveI := hD; IsSimpleGroup.eq_bot_or_eq_top_of_normal ((E ⊓ E').subgroupOf E)) with
      h | h
    · exfalso
      have hbot : ∀ x ∈ E, x ∈ E' → x = 1 := by
        intro x hx hx'
        have : (⟨x, hx⟩ : E) ∈ (E ⊓ E').subgroupOf E :=
          Subgroup.mem_subgroupOf.mpr (Subgroup.mem_inf.mpr ⟨hx, hx'⟩)
        rw [h, Subgroup.mem_bot] at this
        exact congrArg Subtype.val this
      have hE'CE : E' ≤ Subgroup.centralizer (E : Set X) := by
        intro y hy
        rw [Subgroup.mem_centralizer_iff]
        intro x hx
        have h1 : x * y * x⁻¹ * y⁻¹ ∈ E := by
          have := (Subgroup.mem_normalizer_iff.mp (hCtE (hE'C hy)) x⁻¹).mp (E.inv_mem hx)
          have h2 : x * y * x⁻¹ * y⁻¹ = x * (y * x⁻¹ * y⁻¹) := by group
          rw [h2]
          exact E.mul_mem hx this
        have h2 : x * y * x⁻¹ * y⁻¹ ∈ E' :=
          E'.mul_mem (hE'norm x (hEC hx) y hy) (E'.inv_mem hy)
        have h3 := hbot _ h1 h2
        rw [mul_inv_eq_one, mul_inv_eq_iff_eq_mul] at h3
        exact h3
      have hle : E' ≤ Subgroup.zpowers t := hCE ▸ le_inf hE'C hE'CE
      have := Subgroup.card_le_of_le hle
      rw [Nat.card_zpowers, ht, hcard] at this
      omega
    · intro x hx
      have : (⟨x, hx⟩ : E) ∈ (E ⊓ E').subgroupOf E := h ▸ Subgroup.mem_top _
      exact (Subgroup.mem_inf.mp (Subgroup.mem_subgroupOf.mp this)).2
  have heq : E = E' := Subgroup.eq_of_le_of_card_ge hEE' hcard.le
  intro x hx
  rw [heq]
  exact ⟨x, hx, rfl⟩

@[expose] noncomputable def restrictAut (E : Subgroup X) (𝒜 : Subgroup (MulAut X))
    (h𝒜 : ∀ β ∈ 𝒜, ∀ x ∈ E, β x ∈ E) : 𝒜 →* MulAut E where
  toFun β :=
    { toFun := fun x => ⟨(β : MulAut X) x, h𝒜 β β.2 x x.2⟩
      invFun := fun x => ⟨(β : MulAut X)⁻¹ x, h𝒜 _ (𝒜.inv_mem β.2) x x.2⟩
      left_inv := fun x => Subtype.ext (MulAut.inv_apply_self _ _ _)
      right_inv := fun x => Subtype.ext (MulAut.apply_inv_self _ _ _)
      map_mul' := fun x y => Subtype.ext (map_mul (β : MulAut X) (x : X) (y : X)) }
  map_one' := by
    ext x
    rfl
  map_mul' β γ := by
    ext x
    rfl

theorem restrictAut_apply (E : Subgroup X) (𝒜 : Subgroup (MulAut X))
    (h𝒜 : ∀ β ∈ 𝒜, ∀ x ∈ E, β x ∈ E) (β : 𝒜) (x : E) :
    ((restrictAut E 𝒜 h𝒜 β x : E) : X) = (β : MulAut X) x := rfl

end Restrict

section TypeII

variable {G : Type} [Group G] [Finite G]

theorem G35_one_JR
    {L A Y : Subgroup G} [L.Normal] (hLq : CFSG.Open.IsQuasisimple L)
    (hZ : Odd (Nat.card (Subgroup.center L))) (hJR : IsTypeJR (L ⧸ Subgroup.center L))
    (hAL : A ≤ L) (hAab : IsMulCommutative A) (hA2 : ∀ x ∈ A, x ^ 2 = 1)
    (hAmax : ∀ P : Subgroup G, P ≤ L → IsPGroup 2 P → A ≤ P → P = A) (hA1 : A ≠ ⊥)
    (hYA : Y ≤ Subgroup.centralizer (A : Set G)) :
    Odd (((L ⊔ Subgroup.centralizer (L : Set G)).subgroupOf Y).index) ∧
      ∃ y ∈ Y, Y ≤ Subgroup.zpowers y ⊔ (L ⊔ Subgroup.centralizer (L : Set G)) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hA2' : IsPGroup 2 A := isPGroup_two_of_sq hA2
  set π := QuotientGroup.mk' (Subgroup.center L) with hπ
  have hπs : Function.Surjective π := QuotientGroup.mk'_surjective _
  set AB : Sylow 2 (L ⧸ Subgroup.center L) :=
    (sylowOfMax hAL hA2' hAmax).mapSurjective hπs with hAB
  have hABmem : ∀ x ∈ (AB : Subgroup (L ⧸ Subgroup.center L)),
      ∃ b : G, ∃ hb : b ∈ A, x = π ⟨b, hAL hb⟩ := by
    intro x hx
    rw [hAB, Sylow.coe_mapSurjective, coe_sylowOfMax] at hx
    obtain ⟨⟨b, hbL⟩, hb, rfl⟩ := hx
    exact ⟨b, Subgroup.mem_subgroupOf.mp hb, rfl⟩
  set Φ := conjQuot L with hΦ
  have hfixAB : ∀ y ∈ Y, ∀ x ∈ (AB : Subgroup (L ⧸ Subgroup.center L)), Φ y x = x := by
    intro y hy x hx
    obtain ⟨b, hb, rfl⟩ := hABmem x hx
    rw [hΦ, hπ, QuotientGroup.mk'_apply, conjQuot_mk]
    congr 2
    rw [← Subgroup.mem_centralizer_iff.mp (hYA hy) b hb, mul_inv_cancel_right]
  obtain ⟨⟨a, haA⟩, ha1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hA1
  have ha1' : a ≠ 1 := fun h => ha1 (Subtype.ext h)
  have haL : a ∈ L := hAL haA
  set t := π ⟨a, haL⟩ with ht
  have htAB : t ∈ (AB : Subgroup (L ⧸ Subgroup.center L)) := by
    rw [hAB, Sylow.coe_mapSurjective, coe_sylowOfMax]
    exact ⟨⟨a, haL⟩, Subgroup.mem_subgroupOf.mpr haA, rfl⟩
  have ht2 : orderOf t = 2 := by
    refine orderOf_eq_prime ?_ ?_
    · rw [ht, ← map_pow]
      have : (⟨a, haL⟩ : L) ^ 2 = 1 := Subtype.ext (by simpa using hA2 a haA)
      rw [this, map_one]
    · intro h
      rw [ht, hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h
      apply ha1'
      have := eq_one_of_mem_center_of_pow hZ h (k := 1) (Subtype.ext (by simpa using hA2 a haA))
      exact congrArg Subtype.val this
  have hΦt : ∀ y ∈ Y, Φ y t = t := fun y hy => hfixAB y hy t htAB
  obtain ⟨-, p, f, hpf, E, hpodd, hf, h5, hEC, hEn, ⟨eE⟩, hCE⟩ := hJR.2.2 t ht2
  have h8 := hJR.mod_eight ht2 E hpodd hf h5 hEC hEn eE hCE
  obtain ⟨hVcard, -, -, -⟩ := hJR.sylow_two_of_mem AB htAB ht2 E hpodd hf h5 hEC hEn eE hCE
  have hE4 : 4 ≤ Nat.card (GaloisField p f) := by rw [GaloisField.card p f hf.ne']; omega
  have : IsSimpleGroup PSL(2, GaloisField p f) :=
    Matrix.ProjectiveSpecialLinearGroup.rank_two_simple hE4
  have : IsSimpleGroup E := eE.isSimpleGroup
  have hE3 : 2 < Nat.card E := by
    rw [Nat.card_congr eE.toEquiv, psl2_card_formula _
      (isOddPrimePower_of_card (GaloisField.card p f hf.ne') hpodd hf),
      GaloisField.card p f hf.ne']
    have h1 : 24 ≤ (p ^ f) ^ 2 - 1 := by
      have : 25 ≤ (p ^ f) ^ 2 := by nlinarith
      omega
    have h2 : 120 ≤ p ^ f * ((p ^ f) ^ 2 - 1) := by nlinarith
    omega
  set V := (AB : Subgroup (L ⧸ Subgroup.center L)) ⊓ E with hV
  have hVE : V ≤ E := inf_le_right
  have hVEp : IsPGroup 2 (V.subgroupOf E) := by
    refine IsPGroup.of_card (n := 2) ?_
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hVE).toEquiv, hVcard]
    norm_num
  obtain ⟨P0, hP0⟩ := hVEp.exists_le_sylow
  have hP0K := sylow_isKleinFour_of_mulEquiv eE hpodd hf h8 P0
  have hP0eq : (P0 : Subgroup E) = V.subgroupOf E := by
    symm
    apply Subgroup.eq_of_le_of_card_ge hP0
    rw [hP0K.card_four, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hVE).toEquiv, hVcard]
  obtain ⟨hcommE, ⟨Γ, hΓ, hΓmem⟩, -⟩ := mulAut_fix_props_of_mulEquiv eE hpodd hf h5 h8 P0
  have hEinv : ∀ β ∈ Y.map Φ, ∀ x ∈ E, β x ∈ E := by
    rintro _ ⟨y, hy, rfl⟩ x hx
    exact mem_of_fix_of_mem ht2 hEn hEC hCE hE3 (Φ y) (hΦt y hy) x hx
  set R : Y →* MulAut E := (restrictAut E (Y.map Φ) hEinv).comp
    ((Φ.comp Y.subtype).codRestrict (Y.map Φ) fun y => ⟨y, y.2, rfl⟩) with hR
  have hRapp : ∀ (y : Y) (x : E), ((R y x : E) : L ⧸ Subgroup.center L) = Φ y x :=
    fun _ _ => rfl
  have hRfix : ∀ y : Y, ∀ x ∈ (P0 : Subgroup E), R y x = x := by
    intro y x hx
    apply Subtype.ext
    rw [hRapp]
    rw [hP0eq, Subgroup.mem_subgroupOf] at hx
    exact hfixAB y y.2 x (Subgroup.mem_inf.mp hx).1
  have hRfixpow : ∀ y : Y, ∀ k : ℕ, ∀ x ∈ (P0 : Subgroup E), (R y ^ k) x = x := by
    intro y k x hx
    induction k with
    | zero => rfl
    | succ k ih => rw [pow_succ, MulAut.mul_apply, hRfix y x hx, ih]
  set N := Nat.card G with hNdef
  let ψ : Y →* MulAut E :=
    { toFun := fun y => R y ^ 2 ^ N
      map_one' := by simp
      map_mul' := fun y z => by
        rw [map_mul]
        exact Commute.mul_pow (hcommE _ _ (hRfix y) (hRfix z)) _ }
  have hψ : ∀ y : Y, ψ y = R y ^ 2 ^ N := fun _ => rfl
  have hodd : ∀ y : Y, Odd (orderOf (ψ y)) := by
    intro y
    rw [hψ]
    refine odd_orderOf_pow_two_pow (orderOf_pos _) ?_
    calc orderOf (R y) ≤ orderOf y := Nat.le_of_dvd (orderOf_pos _) (orderOf_map_dvd R y)
      _ = orderOf (y : G) := (Subgroup.orderOf_coe y).symm
      _ ≤ N := orderOf_le_natCard _
  have hψΓ : ψ.range ≤ Γ := by
    rintro _ ⟨y, rfl⟩
    exact hΓmem _ (hodd y) (hRfixpow y _)
  have hcyc : IsCyclic ψ.range := by
    have : IsCyclic Γ := hΓ
    exact Subgroup.isCyclic_of_le hψΓ
  refine cyclic_quotient_of_hom Y _ ψ hcyc hodd fun y hy => ?_
  apply mem_of_pow_two_pow_mem _ N
  · apply le_sup_right (a := L)
    rw [← conjQuot_eq_one_iff L hLq.1]
    set β := Φ ((y : G) ^ 2 ^ N) with hβ
    have hyN : (y : G) ^ 2 ^ N ∈ Y := Y.pow_mem y.2 _
    have hβodd : Odd (orderOf β) := by
      refine Odd.of_dvd_nat ?_ (orderOf_map_dvd Φ _)
      exact odd_orderOf_pow_two_pow (orderOf_pos _) (orderOf_le_natCard _)
    have hβE : ∀ x ∈ E, β x = x := by
      intro x hx
      have h1 : R (y ^ 2 ^ N) = 1 := by rw [map_pow]; exact hy
      have h2 := hRapp (y ^ 2 ^ N) ⟨x, hx⟩
      rw [h1] at h2
      exact h2.symm
    have hfixC := fix_centralizer_of_fix ht2 hEn hEC hCE β hβodd (hΦt _ hyN) hβE
    exact hJR.mulAut_eq_one β hβodd ht2 hfixC
  · intro k hk
    exact mem_sup_centralizer_of_isPGroup_two hLq hAL hAab hA2' hAmax hk
      ((Subgroup.centralizer (A : Set G)).pow_mem (hYA y.2) k)

theorem G35_two_JR
    {L A Y : Subgroup G} [L.Normal] (hLq : CFSG.Open.IsQuasisimple L)
    (hZ : Odd (Nat.card (Subgroup.center L))) (hJR : IsTypeJR (L ⧸ Subgroup.center L))
    (hAL : A ≤ L) (hA2 : ∀ x ∈ A, x ^ 2 = 1) {a : G} (haA : a ∈ A) (ha1 : a ≠ 1)
    (hNY : L ⊓ Subgroup.centralizer ({a} : Set G) ≤ Subgroup.normalizer (Y : Set G))
    {r : ℕ} (hr : r.Prime) (hr2 : r ≠ 2) (hYr : IsPGroup r Y) :
    Y ≤ Subgroup.centralizer (L : Set G) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact r.Prime := ⟨hr⟩
  have : IsSimpleGroup (L ⧸ Subgroup.center L) := hLq.2
  set π := QuotientGroup.mk' (Subgroup.center L) with hπ
  have hπs : Function.Surjective π := QuotientGroup.mk'_surjective _
  set Φ := conjQuot L with hΦ
  have haL : a ∈ L := hAL haA
  have haa : a * a = 1 := by rw [← pow_two]; exact hA2 a haA
  set ℓ := π ⟨a, haL⟩ with hℓ
  have hℓ2 : orderOf ℓ = 2 := by
    refine orderOf_eq_prime ?_ ?_
    · rw [hℓ, ← map_pow]
      have : (⟨a, haL⟩ : L) ^ 2 = 1 := Subtype.ext (by simpa using hA2 a haA)
      rw [this, map_one]
    · intro h
      rw [hℓ, hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h
      apply ha1
      have := eq_one_of_mem_center_of_pow hZ h (k := 1) (Subtype.ext (by simpa using hA2 a haA))
      exact congrArg Subtype.val this
  have hcardL : 2 ∣ Nat.card (L ⧸ Subgroup.center L) := hℓ2 ▸ orderOf_dvd_natCard ℓ
  have hYord : ∀ y ∈ Y, ∃ n : ℕ, orderOf y ∣ r ^ n := by
    intro y hy
    obtain ⟨n, hn⟩ := hYr ⟨y, hy⟩
    exact ⟨n, orderOf_dvd_of_pow_eq_one (by simpa using congrArg Subtype.val hn)⟩
  set U := ((L ⊓ Y).subgroupOf L).map π with hU
  have hUr : IsPGroup r U := by
    have h1 : IsPGroup r (L ⊓ Y : Subgroup G) := hYr.to_inf_right
    have h2 : IsPGroup r ((L ⊓ Y).subgroupOf L) := h1.comap_subtype
    exact h2.map π
  have hUodd : Odd (Nat.card U) := by
    obtain ⟨m, hm⟩ := hUr.exists_card_eq
    rw [hm]
    exact (hr.odd_of_ne_two hr2).pow
  have hUnorm : Subgroup.centralizer ({ℓ} : Set (L ⧸ Subgroup.center L)) ≤
      Subgroup.normalizer (U : Set (L ⧸ Subgroup.center L)) := by
    intro c hc
    obtain ⟨c', rfl⟩ := hπs c
    have hc'a : (c' : G) ∈ Subgroup.centralizer ({a} : Set G) :=
      mem_centralizer_of_mk_mem_centralizer L hZ haL haa c' hc
    have hc'N : (c' : G) ∈ Subgroup.normalizer (Y : Set G) := hNY ⟨c'.2, hc'a⟩
    have key : ∀ d : L, (d : G) ∈ Subgroup.normalizer (Y : Set G) →
        ∀ x ∈ U, π d * x * (π d)⁻¹ ∈ U := by
      intro d hd x hx
      obtain ⟨x', hx', rfl⟩ := hx
      refine ⟨d * x' * d⁻¹, ?_, by simp⟩
      have hx'' : (x' : G) ∈ L ⊓ Y := Subgroup.mem_subgroupOf.mp hx'
      show (d * x' * d⁻¹ : L) ∈ (L ⊓ Y).subgroupOf L
      rw [Subgroup.mem_subgroupOf]
      refine Subgroup.mem_inf.mpr ⟨(d * x' * d⁻¹).2, ?_⟩
      simpa using (Subgroup.mem_normalizer_iff.mp hd x').mp hx''.2
    rw [Subgroup.mem_normalizer_iff]
    intro x
    refine ⟨key c' hc'N x, fun hx => ?_⟩
    have h := key c'⁻¹ (by simpa using Subgroup.inv_mem _ hc'N) _ hx
    simpa [mul_assoc] using h
  have hU1 : U = ⊥ := by
    by_contra hU1
    have hCoat := (hJR.2.2 ℓ hℓ2).1
    have hNU : Subgroup.normalizer (U : Set (L ⧸ Subgroup.center L)) ≠ ⊤ := by
      intro h
      have hUn : U.Normal := Subgroup.normalizer_eq_top_iff.mp h
      rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal U with h' | h'
      · exact hU1 h'
      · have h2 : 2 ∣ Nat.card U := by rw [h', Subgroup.card_top]; exact hcardL
        exact (Nat.not_even_iff_odd.mpr hUodd) (even_iff_two_dvd.mpr h2)
    have hNeq := (hCoat.le_iff.mp hUnorm).resolve_left hNU
    have hUC : U ≤ Subgroup.centralizer ({ℓ} : Set (L ⧸ Subgroup.center L)) :=
      hNeq ▸ Subgroup.le_normalizer
    have hℓsq : ℓ ^ 2 = 1 := by rw [← hℓ2, pow_orderOf_eq_one]
    exact hU1 ((odd_normal_subgroup_centralizer hcardL (Or.inr hJR) hℓsq hUodd hUC hUnorm).2
      (Or.inr hJR))
  intro y hy
  rw [← conjQuot_eq_one_iff L hLq.1]
  have hodd : Odd (orderOf (Φ y)) := by
    obtain ⟨n, hn⟩ := hYord y hy
    exact Odd.of_dvd_nat (hr.odd_of_ne_two hr2).pow ((orderOf_map_dvd Φ y).trans hn)
  refine hJR.mulAut_eq_one (Φ y) hodd hℓ2 fun x hx => ?_
  obtain ⟨x', rfl⟩ := hπs x
  have hx'a : (x' : G) ∈ Subgroup.centralizer ({a} : Set G) :=
    mem_centralizer_of_mk_mem_centralizer L hZ haL haa x' hx
  have hx'N : (x' : G) ∈ Subgroup.normalizer (Y : Set G) := hNY ⟨x'.2, hx'a⟩
  rw [hΦ, hπ, QuotientGroup.mk'_apply, conjQuot_mk]
  set w : L := x'⁻¹ * ⟨y * x' * y⁻¹, (inferInstance : L.Normal).conj_mem x' x'.2 y⟩ with hw
  have hwY : (w : G) ∈ Y := by
    have h1 : (w : G) = ((x' : G)⁻¹ * y * (x' : G)⁻¹⁻¹) * y⁻¹ := by
      rw [hw]
      simp [mul_assoc]
    rw [h1]
    exact Y.mul_mem ((Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hx'N) _).mp hy)
      (Y.inv_mem hy)
  have hwU : π w ∈ U := ⟨w, Subgroup.mem_subgroupOf.mpr ⟨w.2, hwY⟩, rfl⟩
  rw [hU1, Subgroup.mem_bot, hw, map_mul, map_inv, inv_mul_eq_one] at hwU
  exact hwU.symm

end TypeII

end CFSG.Goldschmidt.G3b
