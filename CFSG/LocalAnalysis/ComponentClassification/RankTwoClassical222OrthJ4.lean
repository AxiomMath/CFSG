module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassical222OrthBeta

public section

namespace CFSG.ComponentClassification.RankTwoClassical

open Module Matrix QuadraticMap Subgroup CFSG.Assembly.LowTwoRank
open CFSG.ComponentClassification.RankTwoStandard CFSG.LieType.Universal.Spin
open scoped Matrix

section Aut

variable {G : Type} [Group G] {A : Subgroup G} {F : Type} [Field F] [Finite F] [CharP F 2]
  {φ : Multiplicative F →* G}

theorem regularOn_autCyclic_of_actsByScalar [Finite G] {J : Subgroup G}
    (hinj : Function.Injective φ) (hrange : φ.range = J)
    (hscal : ∀ a ∈ A, a ∈ normalizer (J : Set G) → ∃ l : F, l ≠ 0 ∧ ActsByScalar φ a l)
    (hlift : ∀ l : F, l ≠ 0 → ∃ a ∈ A, ActsByScalar φ a l) :
    RegularOn A J (nonidentity J) ∧ AutCyclic A J (Nat.card F - 1) := by
  classical
  have hmemJ : ∀ y, y ∈ J ↔ ∃ t : F, y = φ (Multiplicative.ofAdd t) := fun y => by
    rw [← hrange]
    exact ⟨fun ⟨s, hs⟩ => ⟨Multiplicative.toAdd s, by rw [ofAdd_toAdd, hs]⟩,
      fun ⟨t, ht⟩ => ⟨_, ht.symm⟩⟩
  have hnorm : ∀ {a : G} {l : F}, l ≠ 0 → ActsByScalar φ a l → a ∈ normalizer (J : Set G) :=
    fun {a l} hl ha => mem_normalizer_iff.mpr fun y => by
      rw [hmemJ, hmemJ]
      constructor
      · rintro ⟨t, rfl⟩
        exact ⟨l * t, ha t⟩
      · rintro ⟨s, hs⟩
        refine ⟨l⁻¹ * s, ?_⟩
        have h1 := (ha.inv hl) s
        rw [inv_inv] at h1
        rw [← h1, ← hs]
        group
  have hcent : ∀ {a : G} {l : F}, ActsByScalar φ a l → (a ∈ centralizer (J : Set G) ↔ l = 1) :=
    fun {a l} ha => by
      constructor
      · intro hc
        have h1 := mem_centralizer_iff.mp hc (φ (Multiplicative.ofAdd 1))
          ((hmemJ _).mpr ⟨1, rfl⟩)
        have h2 : a * φ (Multiplicative.ofAdd 1) * a⁻¹ = φ (Multiplicative.ofAdd 1) := by
          rw [← h1]; group
        rw [ha 1, mul_one] at h2
        have h3 := hinj h2
        exact congrArg Multiplicative.toAdd h3
      · rintro rfl
        refine mem_centralizer_iff.mpr fun y hy => ?_
        obtain ⟨t, rfl⟩ := (hmemJ y).mp hy
        have h1 := ha t
        rw [one_mul] at h1
        calc φ (Multiplicative.ofAdd t) * a =
            a * φ (Multiplicative.ofAdd t) * a⁻¹ * a := by rw [h1]
          _ = a * φ (Multiplicative.ofAdd t) := by group
  have hscal' : ∀ a : ↥(A ⊓ normalizer (J : Set G)), ∃ l : F, l ≠ 0 ∧ ActsByScalar φ a l :=
    fun a => hscal a (mem_inf.mp a.2).1 (mem_inf.mp a.2).2
  choose μ hμ0 hμ using hscal'
  have hμmul : ∀ a b, μ (a * b) = μ a * μ b := fun a b =>
    ActsByScalar.eq hinj (hμ (a * b)) ((hμ a).mul (hμ b))
  let μu : ↥(A ⊓ normalizer (J : Set G)) →* Fˣ :=
    { toFun := fun a => Units.mk0 (μ a) (hμ0 a)
      map_one' := Units.ext (ActsByScalar.eq hinj (hμ 1) fun t => by simp)
      map_mul' := fun a b => Units.ext (hμmul a b) }
  have hμu : ∀ a, ((μu a : Fˣ) : F) = μ a := fun _ => rfl
  refine ⟨⟨fun j hj j' hj' => ?_, fun a ha j hj haj => ?_⟩, ?_, ?_⟩
  · obtain ⟨t, rfl⟩ := (hmemJ j).mp hj.1
    obtain ⟨t', rfl⟩ := (hmemJ j').mp hj'.1
    have ht : t ≠ 0 := fun h => hj.2 (by rw [h, ofAdd_zero, map_one])
    have ht' : t' ≠ 0 := fun h => hj'.2 (by rw [h, ofAdd_zero, map_one])
    obtain ⟨a, haA, ha⟩ := hlift (t' * t⁻¹) (mul_ne_zero ht' (inv_ne_zero ht))
    refine ⟨a, mem_inf.mpr ⟨haA, hnorm (mul_ne_zero ht' (inv_ne_zero ht)) ha⟩, ?_⟩
    rw [ha t, mul_assoc, inv_mul_cancel₀ ht, mul_one]
  · obtain ⟨t, rfl⟩ := (hmemJ j).mp hj.1
    have ht : t ≠ 0 := fun h => hj.2 (by rw [h, ofAdd_zero, map_one])
    have h1 := hμ ⟨a, ha⟩
    rw [h1 t] at haj
    have h2 := hinj haj
    have h3 : μ ⟨a, ha⟩ * t = 1 * t := by rw [one_mul]; exact congrArg Multiplicative.toAdd h2
    exact (hcent h1).mpr (mul_right_cancel₀ ht h3)
  · have hker : (A ⊓ centralizer (J : Set G)).subgroupOf (A ⊓ normalizer (J : Set G)) =
        μu.ker := by
      ext a
      rw [mem_subgroupOf, MonoidHom.mem_ker, Units.ext_iff, hμu, Units.val_one, mem_inf]
      exact ⟨fun h => ((hcent (hμ a)).mp h.2), fun h => ⟨(mem_inf.mp a.2).1, (hcent (hμ a)).mpr h⟩⟩
    have hsurj : Function.Surjective μu := fun l => by
      obtain ⟨a, haA, ha⟩ := hlift (l : F) l.ne_zero
      refine ⟨⟨a, mem_inf.mpr ⟨haA, hnorm l.ne_zero ha⟩⟩, Units.ext ?_⟩
      rw [hμu]
      exact ActsByScalar.eq hinj (hμ _) ha
    rw [Subgroup.relIndex, hker, Subgroup.index_ker, MonoidHom.range_eq_top.mpr hsurj,
      Subgroup.card_top, Nat.card_units]
  · have hpow : ∀ {a : G} {l : F}, ActsByScalar φ a l → ∀ k : ℕ, ActsByScalar φ (a ^ k) (l ^ k) :=
      fun {a l} ha k => by
        induction k with
        | zero => exact fun t => by simp
        | succ k ih => rw [pow_succ, pow_succ]; exact ih.mul ha
    have hodd : Odd (Nat.card Fˣ) := by
      by_contra hev
      rw [Nat.not_odd_iff_even] at hev
      have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
      obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' 2 (even_iff_two_dvd.mp hev)
      have hx2 : ((x : F) - 1) ^ 2 = 0 := by
        have h1 : (x : F) ^ 2 = 1 := by
          rw [← Units.val_pow_eq_pow_val, ← hx, pow_orderOf_eq_one, Units.val_one]
        rw [sub_sq, h1, mul_one, CharTwo.two_eq_zero, zero_mul, sub_zero, one_pow,
          CharTwo.add_self_eq_zero]
      have hx1 : x = 1 := Units.ext (by
        rw [Units.val_one]
        exact sub_eq_zero.mp ((pow_eq_zero_iff two_ne_zero).mp hx2))
      rw [hx1, orderOf_one] at hx
      omega
    obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := Fˣ)
    have hgo : orderOf g = Nat.card Fˣ := by
      rw [← Nat.card_zpowers]
      exact Nat.card_congr (Equiv.subtypeUnivEquiv hg)
    obtain ⟨a₀, ha₀A, ha₀⟩ := hlift (g : F) g.ne_zero
    obtain ⟨s, r, hr, hsr⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos a₀).ne'
    refine ⟨a₀ ^ 2 ^ s, mem_inf.mpr ⟨pow_mem ha₀A _, hnorm (pow_ne_zero _ g.ne_zero)
      (hpow ha₀ _)⟩, ?_, fun a ha => ?_⟩
    · rw [orderOf_pow_of_dvd (pow_ne_zero _ two_ne_zero) ⟨r, hsr⟩, hsr,
        Nat.mul_div_cancel_left _ (pow_pos two_pos _)]
      exact hr
    have hgen : Subgroup.zpowers (g ^ 2 ^ s) = ⊤ := by
      apply Subgroup.eq_top_of_card_eq
      rw [Nat.card_zpowers, Nat.Coprime.orderOf_pow, hgo]
      rw [hgo]
      exact Nat.Coprime.pow_right _ hodd.coprime_two_right
    obtain ⟨k, hk⟩ := (mem_powers_iff_mem_zpowers (y := μu ⟨a, ha⟩)).mpr (by
      rw [hgen]; exact mem_top _)
    refine ⟨k, ?_⟩
    have h1 := ((hpow (hpow ha₀ (2 ^ s)) k).inv (pow_ne_zero _ (pow_ne_zero _ g.ne_zero))).mul
      (hμ ⟨a, ha⟩)
    refine (hcent h1).mpr ?_
    rw [← hμu, ← hk, Units.val_pow_eq_pow_val, Units.val_pow_eq_pow_val,
      inv_mul_cancel₀ (pow_ne_zero _ (pow_ne_zero _ g.ne_zero))]

end Aut

section Model

variable {G : Type} [Group G] {A : Subgroup G} {ι K : Type} [Fintype ι] [DecidableEq ι] [Field K]
  [Finite K] [CharP K 2]

theorem orthJ4_of_model [Finite G] (Q : QuadraticForm K (ι → K)) (q : (ι → K) → K)
    (hq : ⇑Q = q) (hQ : Q.polarBilin.Nondegenerate)
    (hT : ∃ T : Submodule K (ι → K), finrank K T = 3 ∧ ∀ x ∈ T, Q x = 0)
    (hι : 8 ≤ Fintype.card ι)
    {e : rankTwoQuot A ≃* StatedProj (StatedOmega q)} (hZ : Odd (Nat.card (center ↥A)))
    {p : G} {ℓ : ℕ} (hp : HasSuzukiType e (fun M v => q (((M : Matrix ι ι K) - 1) *ᵥ v)) p .c ℓ) :
    ∃ Z : Subgroup G, Nat.card Z = Nat.card K ∧ DeltaNormal A p Z ∧ DeltaCentral A p Z ∧
      RegularOn A Z (nonidentity Z) ∧ AutCyclic A Z (Nat.card K - 1) := by
  classical
  subst hq
  obtain ⟨hp2, M, hpM, hM2, hr, hev, v₀, hv₀⟩ := hp
  rw [← hr] at hev
  have hMQ : ∀ v, Q ((M : Matrix ι ι K) *ᵥ v) = Q v := statedOmega_isometry hpM.2.1
  have hM2' : M ^ 2 = 1 := by rw [← hM2]; exact pow_orderOf_eq_one M
  have hp2' : p ^ 2 = 1 := by rw [← hp2]; exact pow_orderOf_eq_one p
  have hp1 : p ≠ 1 := fun h => by rw [h, orderOf_one] at hp2; omega
  obtain ⟨z, z', y', hd⟩ := exists_typeCData hQ hMQ hM2 hev ⟨v₀, hv₀⟩
  set N := (M : Matrix ι ι K) - 1 with hNdef
  have hMN : (M : Matrix ι ι K) = 1 + N := by rw [hNdef, add_sub_cancel]
  have hiso : ∀ v, Q (v + N *ᵥ v) = Q v := fun v => by
    rw [← hMQ v, hMN, add_mulVec, one_mulVec]
  have hN : N * N = 0 := sub_one_mul_self hM2'
  have hz0 : z ≠ 0 := fun h => by
    have h1 := hd.pol_y'z
    rw [h, map_zero] at h1
    exact zero_ne_one h1
  set T := betaT Q.polarBilin N z with hTdef
  set W : K → GL ι K := fun d => sqZeroGL (T d) (betaT_mul_self hN hd.sq hd.mulVec_z d) with hWdef
  have hWc : ∀ d, (W d : Matrix ι ι K) = 1 + T d := fun d => rfl
  have hrank : ∀ d, d ≠ 0 → (T d).rank = N.rank := fun d hd0 =>
    rank_betaT hN hiso hd.sq hd.mulVec_z' hd.quad_z hd0
  have hWH : ∀ d, W d ∈ StatedOmega ⇑Q := by
    intro d
    refine mem_statedOmega_of Q hQ hT (fun v => ?_) ?_
    · rw [hWc]
      exact betaT_isometry hN hd.sq hiso hd.quad_z d v
    · rw [commRank_sqZeroGL]
      by_cases hd0 : d = 0
      · have h0 : T d = 0 := by simp [hTdef, betaT, hd0]
        rw [h0, Matrix.rank_zero]
        exact ⟨0, rfl⟩
      · rw [hrank d hd0]
        exact hev
  have hTadd : ∀ a b, T a + T b = T (a + b) := fun a b => betaT_add a b
  have hTmul : ∀ a b, T a * T b = 0 := betaT_mul hN hd.sq hd.mulVec_z
  have hWmul : ∀ a b, W (a + b) = W a * W b := by
    intro a b
    apply Units.ext
    rw [Units.val_mul, hWc, hWc, hWc, ← hTadd, add_mul, one_mul, mul_add, mul_one, hTmul,
      add_zero]
    abel
  have hWsq : ∀ d, W d ^ 2 = 1 := fun d => sqZeroGL_sq _ _
  have hW1 : W 1 = M := by
    apply Units.ext
    rw [hWc, hMN]
    simp [hTdef, betaT, CharTwo.add_self_eq_zero]
  choose β hβ2 hβ using fun d : K => exists_represents_sq_eq_one (e := e) hZ (hWH d) (hWsq d)
  have hβ2' : ∀ d, β d ^ 2 ^ 1 = 1 := fun d => by rw [pow_one]; exact hβ2 d
  have hp2'' : p ^ 2 ^ 1 = 1 := by rw [pow_one]; exact hp2'
  have hβ1 : β 1 = p := eq_of_represents hZ (hβ 1) (hW1 ▸ hpM) (hβ2' 1) hp2''
  have hβcomm : ∀ a b, β a * β b = β b * β a := fun a b =>
    commute_of_represents hZ (hβ a) (hβ b) (hβ2 b) (by rw [← hWmul, ← hWmul, add_comm])
  have hβadd : ∀ a b, β (a + b) = β a * β b := by
    intro a b
    have hrep : Represents e (β a * β b) (W (a + b)) := by
      rw [hWmul]
      exact (hβ a).mul (hβ b)
    have hsq : (β a * β b) ^ 2 ^ 1 = 1 := by
      rw [pow_one, (show Commute (β a) (β b) from hβcomm a b).mul_pow, hβ2, hβ2, one_mul]
    exact eq_of_represents hZ (hβ (a + b)) hrep (hβ2' _) hsq
  have hβ0 : β 0 = 1 := by
    have h := hβadd 0 0
    rw [add_zero] at h
    exact (mul_eq_left.mp h.symm)
  set φ : Multiplicative K →* G :=
    { toFun := fun d => β (Multiplicative.toAdd d)
      map_one' := hβ0
      map_mul' := fun a b => hβadd _ _ } with hφ
  have hφβ : ∀ t : K, φ (Multiplicative.ofAdd t) = β t := fun _ => rfl
  have hφinj : Function.Injective φ := by
    rw [injective_iff_map_eq_one]
    intro d hd1
    have h1 : Represents e (1 : G) (W (Multiplicative.toAdd d)) := hd1 ▸ hβ _
    obtain ⟨c, hc⟩ := represents_one.exists_scalar h1
    rw [one_mul] at hc
    have hT0 := eq_zero_of_sqZeroGL_eq_scalar _ hc
    by_contra hne
    have hd0 : Multiplicative.toAdd d ≠ 0 := fun h => hne (by
      rw [← ofAdd_toAdd d, h, ofAdd_zero])
    have h2 := hrank _ hd0
    rw [hT0, Matrix.rank_zero] at h2
    exact commRank_ne_zero hM2 h2.symm
  have hkey : ∀ x ∈ A ⊓ centralizer ({p} : Set G), ∀ d, x * β d = β d * x := by
    intro x hx d
    obtain ⟨X, hX⟩ := exists_represents e hx.1
    have hxp : x * p = p * x := mem_centralizer_singleton_iff.mp hx.2
    have hXM := hX.mul_comm_of_commute hpM hM2' hxp
    have hXN : (X : Matrix ι ι K) * N = N * X := by
      rw [hNdef, mul_sub, sub_mul, hXM, mul_one, one_mul]
    have hXT := commute_betaT hd.sq hQ (statedOmega_isometry hX.2.1) hXN d
    have hXW : X * W d = W d * X := by
      apply Units.ext
      rw [Units.val_mul, Units.val_mul, hWc, mul_add, add_mul, mul_one, one_mul, hXT]
    exact commute_of_represents hZ hX (hβ d) (hβ2 d) hXW
  have hpC : p ∈ A ⊓ centralizer ({p} : Set G) :=
    ⟨hpM.1, mem_centralizer_singleton_iff.mpr rfl⟩
  have hact : ∀ {a : G} {X : GL ι K}, Represents e a X → ∀ {l : K},
      (X : Matrix ι ι K) * N * ((X⁻¹ : GL ι K) : Matrix ι ι K) = T l →
      ActsByScalar φ a l := by
    intro a X hX l hXl t
    have h1 := conj_betaT_of_conj hQ hN hiso hd.sq hd.quad_z (statedOmega_isometry hX.2.1) hXl t
    have hconj : X * W t * X⁻¹ = W (l * t) := Units.ext (by
      rw [Units.val_mul, Units.val_mul, hWc, hWc, Matrix.mul_add, Matrix.mul_one,
        Matrix.add_mul, Units.mul_inv, h1])
    have h2 := (hβ t).conj hX
    rw [hconj] at h2
    rw [hφβ, hφβ]
    exact eq_of_represents hZ h2 (hβ (l * t)) (k := 1)
      (by rw [pow_one, conj_pow, hβ2, mul_one, mul_inv_cancel]) (hβ2' _)
  have hcard : Nat.card φ.range = Nat.card K := by
    have h1 : Nat.card φ.range = Nat.card (Set.range φ) :=
      Nat.card_congr (Equiv.subtypeEquivRight fun x => MonoidHom.mem_range)
    rw [h1, Nat.card_range_of_injective hφinj]
    rfl
  refine ⟨φ.range, hcard, ⟨?_, ?_, ?_, ?_⟩, ?_,
    regularOn_autCyclic_of_actsByScalar hφinj rfl ?_ ?_⟩
  · rintro _ ⟨d, rfl⟩
    exact mem_inf.mpr ⟨(hβ _).1, mem_centralizer_singleton_iff.mpr (hkey p hpC _).symm⟩
  · intro x hx
    have hconj : ∀ d, x * φ d * x⁻¹ = φ d := fun d => by
      show x * β (Multiplicative.toAdd d) * x⁻¹ = β (Multiplicative.toAdd d)
      rw [hkey x hx, mul_inv_cancel_right]
    rw [mem_normalizer_iff]
    intro y
    constructor
    · rintro ⟨d, rfl⟩
      exact ⟨d, (hconj d).symm⟩
    · rintro ⟨d, hd'⟩
      refine ⟨d, ?_⟩
      calc φ d = x⁻¹ * (x * φ d * x⁻¹) * x := by group
        _ = x⁻¹ * (x * y * x⁻¹) * x := by rw [hconj d, hd']
        _ = y := by group
  · intro g
    obtain ⟨d, hd'⟩ := g.2
    refine ⟨1, Subtype.ext ?_⟩
    rw [Subgroup.coe_pow, pow_one, Subgroup.coe_one, ← hd']
    exact hβ2 _
  · intro y hy
    rw [mem_centralizer_iff]
    rintro w ⟨b, hb, rfl, hcomm⟩
    obtain ⟨d, rfl⟩ := hy
    have hw : b * p * b⁻¹ ∈ A ⊓ centralizer ({p} : Set G) :=
      Subgroup.mem_inf.mpr ⟨A.mul_mem (A.mul_mem hb hpM.1) (A.inv_mem hb),
        mem_centralizer_singleton_iff.mpr hcomm.eq⟩
    exact hkey _ hw _
  · intro x hx hxΔ hx2
    obtain ⟨hxA, hxp⟩ := mem_inf.mp hx
    have hxp' : x * p = p * x := mem_centralizer_singleton_iff.mp hxp
    obtain ⟨X, hX⟩ := exists_represents e hxA
    have hXM : X * M = M * X := Units.ext (by
      rw [Units.val_mul, Units.val_mul]
      exact hX.mul_comm_of_commute hpM hM2' hxp')
    obtain ⟨d, hdX⟩ := commutant_typeC_orth hQ hT hι hMQ hM2 hev hd.sq hz0
      (statedOmega_isometry hX.2.1) hXM fun g hg hgM => by
        obtain ⟨b, hb⟩ := exists_represents_of_mem (e := e) hg
        have hrep := hpM.conj hb
        have hb2 : (b * p * b⁻¹) ^ 2 = 1 := by rw [conj_pow, hp2', mul_one, mul_inv_cancel]
        have hcomm : p * (b * p * b⁻¹) = b * p * b⁻¹ * p :=
          commute_of_represents hZ hpM hrep hb2 hgM.symm
        have hmem : b * p * b⁻¹ ∈ conjCommuting A p := ⟨b, hb.1, rfl, hcomm.symm⟩
        have hxc : b * p * b⁻¹ * x = x * (b * p * b⁻¹) := mem_centralizer_iff.mp hxΔ _ hmem
        have hgM2 : (g * M * g⁻¹) ^ 2 = 1 := by rw [conj_pow, hM2', mul_one, mul_inv_cancel]
        exact Units.ext (by
          rw [Units.val_mul, Units.val_mul]
          exact hX.mul_comm_of_commute hrep hgM2 hxc.symm)
    have hXW : X = W d := Units.ext (by rw [hWc]; exact hdX)
    obtain ⟨k, hk⟩ := hx2
    rw [hXW] at hX
    exact ⟨Multiplicative.ofAdd d, (eq_of_represents hZ hX (hβ d) hk (hβ2' d)).symm⟩
  · intro a haA han
    obtain ⟨X, hX⟩ := exists_represents e haA
    have hpφ : p ∈ φ.range := ⟨Multiplicative.ofAdd 1, hβ1⟩
    obtain ⟨s, hs⟩ := (mem_normalizer_iff.mp han p).mp hpφ
    have h1 := hpM.conj hX
    have h2 := hβ (Multiplicative.toAdd s)
    rw [show β (Multiplicative.toAdd s) = φ s from rfl, hs] at h2
    obtain ⟨c, hc⟩ := h1.exists_scalar h2
    set U := X * M * X⁻¹ with hU
    have hU2 : U ^ 2 = 1 := by rw [hU, conj_pow, hM2', mul_one, mul_inv_cancel]
    have hne : Nonempty ι := by
      by_contra h
      have : IsEmpty ι := not_nonempty_iff.mp h
      have hM1 : M = 1 := Units.ext (Subsingleton.elim _ _)
      rw [hM1, orderOf_one] at hM2
      omega
    have hc2 : c ^ 2 = 1 := by
      have h3 : W (Multiplicative.toAdd s) ^ 2 = 1 := hWsq _
      have hcomm : Commute U (Matrix.GeneralLinearGroup.scalar ι c) :=
        (Matrix.GeneralLinearGroup.scalar_commute c U).symm
      rw [hc, hcomm.mul_pow, hU2, one_mul, ← map_pow] at h3
      apply Units.ext
      have h4 := congrArg (fun N : GL ι K => (N : Matrix ι ι K)) h3
      simp only [Matrix.GeneralLinearGroup.coe_scalar, Units.val_one] at h4
      have h5 : Matrix.scalar ι ((c ^ 2 : Kˣ) : K) = Matrix.scalar ι (1 : K) := by
        rw [h4]; exact (Matrix.scalar_apply (1 : K)).trans Matrix.diagonal_one |>.symm
      rw [Matrix.scalar_inj] at h5
      exact h5
    have hc1 : c = 1 := by
      have h3 : ((c : K) - 1) ^ 2 = 0 := by
        have h4 := congrArg Units.val hc2
        rw [Units.val_pow_eq_pow_val, Units.val_one] at h4
        rw [sub_sq, h4, mul_one, CharTwo.two_eq_zero, zero_mul, sub_zero, one_pow,
          CharTwo.add_self_eq_zero]
      exact Units.ext (sub_eq_zero.mp ((pow_eq_zero_iff two_ne_zero).mp h3))
    rw [hc1, map_one, mul_one] at hc
    have hXN : (X : Matrix ι ι K) * N * ((X⁻¹ : GL ι K) : Matrix ι ι K) =
        T (Multiplicative.toAdd s) := by
      have h3 := congrArg (fun Y : GL ι K => (Y : Matrix ι ι K)) hc
      simp only [hU, Units.val_mul, hWc, hMN, Matrix.mul_add, Matrix.mul_one, Matrix.add_mul,
        Units.mul_inv] at h3
      exact (add_left_cancel h3).symm
    refine ⟨Multiplicative.toAdd s, fun h0 => hp1 ?_, hact hX hXN⟩
    have h3 : s = 1 := by rw [← ofAdd_toAdd s, h0, ofAdd_zero]
    rw [h3, map_one] at hs
    calc p = a⁻¹ * (a * p * a⁻¹) * a := by group
      _ = 1 := by rw [← hs]; group
  · intro l hl
    obtain ⟨d, hdH, hdN⟩ := exists_conj_eq_betaT hQ hT hN hiso hd hl
    obtain ⟨a, ha⟩ := exists_represents_of_mem (e := e) hdH
    exact ⟨a, ha.1, hact ha hdN⟩

end Model

theorem orthJ4 : OrthJ4 := by
  intro G _ _ A D hD _ hZ _ p ℓ hp
  cases D with
  | orthPlus n m hn hm K hK e =>
    have := charP_two_of_card hK
    obtain ⟨Z, -, h1, h2, h3, h4⟩ := orthJ4_of_model (quadPlus n K) (StatedQuadPlus n K)
      (coe_quadPlus n K) (nondegenerate_polarBilin_quadPlus n K)
      (exists_totallySingular_quadPlus (by omega) K)
      (by simp only [Fintype.card_sum, Fintype.card_fin]; omega) hZ hp
    refine ⟨Z, h1, h2, h3, ?_⟩
    rw [hK] at h4
    exact h4
  | orthMinus n m hn hm K hK b c hbc e =>
    have := charP_two_of_card hK
    obtain ⟨Z, -, h1, h2, h3, h4⟩ := orthJ4_of_model (quadMinus n K b c) (StatedQuadMinus n K b c)
      (coe_quadMinus n K b c) (nondegenerate_polarBilin_quadMinus_of_finite n K hbc)
      (exists_totallySingular_quadMinus hn K b c)
      (by simp only [Fintype.card_sum, Fintype.card_fin]; omega) hZ hp
    refine ⟨Z, h1, h2, h3, ?_⟩
    rw [hK] at h4
    exact h4
  | linear => simp [ClassicalModel.family] at hD
  | unitary => simp [ClassicalModel.family] at hD
  | symplectic => simp [ClassicalModel.family] at hD

end CFSG.ComponentClassification.RankTwoClassical
