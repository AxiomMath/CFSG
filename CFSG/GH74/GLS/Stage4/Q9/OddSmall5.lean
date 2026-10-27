module

public import CFSG.GH74.GLS.Stage4.Q9.Rigidity
public import CFSG.GH74.GLS.Stage4.Q9.VSupport
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.GroupAction.Quotient
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.SubgroupConjAction

public section

namespace CFSG.GH74.GLS.Stage4.Q9

theorem sl2_nine_restrict_trivial {K : Type*} [Group K] {F : Type*} [Field F] [Finite F]
    (hF : Nat.card F = 9) (e : K ≃* Matrix.SpecialLinearGroup (Fin 2) F) {Y : Type*} [Group Y]
    [Finite Y] (ρ : K →* MulAut Y) (S : Subgroup Y) (hS : ∀ k : K, ∀ s ∈ S, ρ k s ∈ S)
    (hcard : Nat.card S ∣ 25 ∨ Nat.card S ∣ 9) : ∀ k : K, ∀ s ∈ S, ρ k s = s := by
  let ψ : K →* MulAut S :=
    { toFun := fun k =>
        { toFun := fun s => ⟨ρ k s, hS k s s.2⟩
          invFun := fun s => ⟨ρ k⁻¹ s, hS k⁻¹ s s.2⟩
          left_inv := fun s => Subtype.ext (by
            have : (ρ k⁻¹) ((ρ k) (s : Y)) = s := by
              rw [← MulAut.mul_apply, ← map_mul, inv_mul_cancel, map_one]; rfl
            exact this)
          right_inv := fun s => Subtype.ext (by
            have : (ρ k) ((ρ k⁻¹) (s : Y)) = s := by
              rw [← MulAut.mul_apply, ← map_mul, mul_inv_cancel, map_one]; rfl
            exact this)
          map_mul' := fun a b => Subtype.ext (map_mul (ρ k) (a : Y) (b : Y)) }
      map_one' := by
        ext s
        simp
      map_mul' := fun a b => by
        ext s
        simp }
  have hψ : ψ = 1 := sl2_nine_hom_trivial hF e ψ (not_dvd_card_mulAut_of_card_dvd hcard)
  intro k s hs
  have h := congrArg (fun f : MulAut S => ((f ⟨s, hs⟩ : S) : Y)) (DFunLike.congr_fun hψ k)
  simpa [ψ] using h

private theorem involutive_of_mul_self_eq_one {Y K : Type*} [Group Y] [Group K] (ρ : K →* MulAut Y)
    {z₀ : K} (hz₀ : z₀ * z₀ = 1) : Function.Involutive (ρ z₀) := fun y => by
  rw [← MulAut.mul_apply, ← map_mul, hz₀, map_one]
  rfl

theorem eq_one_of_sl2_nine_fixedPointFree {Y K : Type*} [Group Y] [Finite Y] [Group K]
    {F : Type*} [Field F] [Finite F] (hF : Nat.card F = 9)
    (e : K ≃* Matrix.SpecialLinearGroup (Fin 2) F)
    (ρ : K →* MulAut Y) (z₀ : K) (hz₀ : z₀ * z₀ = 1) (hfix : ∀ y : Y, ρ z₀ y = y → y = 1)
    (hprime : ∀ p : ℕ, p.Prime → p ∣ Nat.card Y → p = 3 ∨ p = 5)
    (h3 : (Nat.card Y).factorization 3 ≤ 2) (h5 : (Nat.card Y).factorization 5 ≤ 2) :
    Nat.card Y = 1 := by
  by_contra hY1
  obtain ⟨p, hp, hpY⟩ := Nat.exists_prime_and_dvd hY1
  have : Fact p.Prime := ⟨hp⟩
  have hinv2 := involutive_of_mul_self_eq_one ρ hz₀
  have hfp : MonoidHom.FixedPointFree (ρ z₀) := hfix
  have hinv : ∀ y : Y, ρ z₀ y = y⁻¹ := fun y => congrFun (hfp.coe_eq_inv_of_involutive hinv2) y
  have hcomm : ∀ a b : Y, Commute a b := hfp.commute_all_of_involutive hinv2
  obtain ⟨S⟩ : Nonempty (Sylow p Y) := inferInstance
  have hSn : (S : Subgroup Y).Normal := ⟨fun n hn g => by
    rw [(hcomm g n).eq, mul_inv_cancel_right]
    exact hn⟩
  have hSchar : (S : Subgroup Y).Characteristic := S.characteristic_of_normal hSn
  have hstable : ∀ k : K, ∀ s ∈ (S : Subgroup Y), ρ k s ∈ (S : Subgroup Y) := fun k s hs => by
    have : s ∈ (S : Subgroup Y).comap (ρ k).toMonoidHom := by
      rw [hSchar.fixed (ρ k)]
      exact hs
    exact this
  have hvp : 0 < (Nat.card Y).factorization p :=
    hp.factorization_pos_of_dvd Nat.card_pos.ne' hpY
  have hcardS : Nat.card (S : Subgroup Y) = p ^ (Nat.card Y).factorization p :=
    S.card_eq_multiplicity
  have hS : Nat.card (S : Subgroup Y) ∣ 25 ∨ Nat.card (S : Subgroup Y) ∣ 9 := by
    rcases hprime p hp hpY with rfl | rfl
    · right
      rw [hcardS]
      exact (pow_dvd_pow 3 h3).trans (by norm_num)
    · left
      rw [hcardS]
      exact (pow_dvd_pow 5 h5).trans (by norm_num)
  have htriv := sl2_nine_restrict_trivial hF e ρ S hstable hS
  have hpS : p ∣ Nat.card (S : Subgroup Y) := by
    rw [hcardS]
    exact dvd_pow_self p hvp.ne'
  obtain ⟨s, hs⟩ := exists_prime_orderOf_dvd_card' (G := (S : Subgroup Y)) p hpS
  have h1 : ((s : (S : Subgroup Y)) : Y) = ((s : (S : Subgroup Y)) : Y)⁻¹ := by
    rw [← hinv, htriv z₀ _ s.2]
  have h2 : ((s : (S : Subgroup Y)) : Y) ^ 2 = 1 := by
    rw [pow_two]
    exact mul_eq_one_iff_eq_inv.2 h1
  have h3' : p ∣ 2 := by
    rw [← Subgroup.orderOf_coe s] at hs
    rw [← hs]
    exact orderOf_dvd_of_pow_eq_one h2
  have := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 h3'
  rcases hprime p hp hpY with h | h <;> omega

theorem card_mul_card_dvd_of_sup_eq_top {Q : Type*} [Group Q] [Finite Q] (N C₁ C₂ : Subgroup Q)
    (hN₁ : N ≤ C₁) (hN₂ : N ≤ C₂) (hsup : C₁ ⊔ C₂ = ⊤)
    (hcomm : ∀ a b : Q, a * b * a⁻¹ * b⁻¹ ∈ N) :
    Nat.card Q * Nat.card N ∣ Nat.card C₁ * Nat.card C₂ := by
  have hnorm : C₂.Normal := ⟨fun c hc q => by
    have : q * c * q⁻¹ = (q * c * q⁻¹ * c⁻¹) * c := by group
    rw [this]
    exact mul_mem (hN₂ (hcomm q c)) hc⟩
  have h1 := Subgroup.relIndex_mul_card C₂ (C₁ ⊔ C₂)
  have h2 := Subgroup.relIndex_mul_card C₂ C₁
  rw [inf_eq_left.2 le_sup_right, Subgroup.relIndex_sup_right] at h1
  rw [hsup, Subgroup.card_top] at h1
  have h3 : Nat.card Q * Nat.card ↥(C₂ ⊓ C₁) = Nat.card C₁ * Nat.card C₂ := by
    rw [← h1, ← h2]
    ring
  rw [← h3]
  exact Nat.mul_dvd_mul_left _ (Subgroup.card_dvd_of_le (le_inf hN₂ hN₁))

theorem exists_conjAction_quotient {G : Type*} [Group G] (A O X : Subgroup G)
    [hN : (X.subgroupOf O).Normal]
    (hAO : ∀ a ∈ A, ∀ o ∈ O, a * o * a⁻¹ ∈ O)
    (hAX : ∀ a ∈ A, ∀ x ∈ X, a * x * a⁻¹ ∈ X) :
    ∃ ρ : A →* MulAut (O ⧸ X.subgroupOf O), ∀ (a : A) (o : O) (h : (a : G) * o * a⁻¹ ∈ O),
      ρ a (QuotientGroup.mk o) = QuotientGroup.mk (⟨a * o * a⁻¹, h⟩ : O) := by
  have hle : A ≤ Subgroup.normalizer (O : Set G) := by
    intro a ha
    rw [Subgroup.mem_normalizer_iff]
    intro o
    refine ⟨fun ho => hAO a ha o ho, fun ho => ?_⟩
    have := hAO a⁻¹ (inv_mem ha) _ ho
    simpa [mul_assoc] using this
  have : Subgroup.Normalizes A O := ⟨hle⟩
  have hinv : CFSG.IsInvariant A O (X.subgroupOf O) := ⟨fun a g => by
    simp only [Subgroup.mem_subgroupOf,
      Subgroup.conjMulDistribMulActionOfLeNormalizer_smul_coe]
    constructor
    · exact hAX a a.2 g
    · intro h
      have := hAX a⁻¹ (inv_mem a.2) _ h
      simpa [mul_assoc] using this⟩
  let : MulDistribMulAction A (O ⧸ X.subgroupOf O) :=
    CFSG.quotientMulDistribMulAction (X.subgroupOf O) hinv
  refine ⟨MulDistribMulAction.toMulAut A (O ⧸ X.subgroupOf O), fun a o h => ?_⟩
  rw [MulDistribMulAction.toMulAut_apply]
  change QuotientGroup.mk (a • o) = _
  rfl

theorem odd_core_small5 {G : Type*} [Group G] [Finite G] {z t x : G}
    (hz : orderOf z = 2) (ht : orderOf t = 2) (hzt : z * t = t * z) (hne : z ≠ t)
    (hxo : orderOf x = 5) (hxz : z * x = x * z) (hxt : t * x = x * t)
    (O : Subgroup G) (hOodd : Odd (Nat.card O)) (hOle : O ≤ Subgroup.centralizer ({x} : Set G))
    (hOA : ∀ a ∈ Subgroup.centralizer ({x} : Set G), ∀ o ∈ O, a * o * a⁻¹ ∈ O) (hxO : x ∈ O)
    (hCOz : ∀ o ∈ O, z * o = o * z → o ∈ Subgroup.zpowers x)
    (hprime : ∀ r : ℕ, r.Prime → r ∣ Nat.card O → r = 3 ∨ r = 5)
    (h3 : (Nat.card O).factorization 3 ≤ 2)
    (h5t : (Nat.card ↥(O ⊓ Subgroup.centralizer ({t} : Set G))).factorization 5 ≤ 2)
    (h5zt : (Nat.card ↥(O ⊓ Subgroup.centralizer ({z * t} : Set G))).factorization 5 ≤ 2)
    (Kb : Subgroup G) (hKb : Kb ≤ Subgroup.centralizer ({x} : Set G)) (hzKb : z ∈ Kb)
    (_hzcent : ∀ k ∈ Kb, z * k = k * z)
    {F : Type*} [Field F] [Finite F] (hF : Nat.card F = 9)
    (eb : ↥Kb ≃* Matrix.SpecialLinearGroup (Fin 2) F) :
    ∀ o ∈ O, o ∈ Subgroup.zpowers x := by
  classical
  have hz2 : z * z = 1 := by
    rw [← pow_two, ← hz]
    exact pow_orderOf_eq_one z
  have hzi : z⁻¹ = z := inv_eq_of_mul_eq_one_right hz2
  have hzz : ∀ a : G, z * (z * a) = a := fun a => by rw [← mul_assoc, hz2, one_mul]
  have hmemC : ∀ g : G, g * x = x * g → g ∈ Subgroup.centralizer ({x} : Set G) :=
    fun g hg => Subgroup.mem_centralizer_singleton_iff.2 hg
  have hzC := hmemC z hxz
  have htC := hmemC t hxt
  have hztx : z * t * x = x * (z * t) := by
    rw [mul_assoc, hxt, ← mul_assoc, hxz, mul_assoc]
  have hXcent : ∀ g ∈ Subgroup.centralizer ({x} : Set G), ∀ y ∈ Subgroup.zpowers x,
      g * y = y * g := by
    intro g hg y hy
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hy
    have hc : Commute g x := Subgroup.mem_centralizer_singleton_iff.1 hg
    exact (hc.zpow_right k).eq
  set X := Subgroup.zpowers x with hXdef
  have hXO : X ≤ O := Subgroup.zpowers_le.2 hxO
  have hNnormal : (X.subgroupOf O).Normal := ⟨fun n hn g => by
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    have h := hXcent g (hOle g.2) n hn
    have : ((g * n * g⁻¹ : O) : G) = n := by
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      rw [h, mul_inv_cancel_right]
    rw [this]
    exact hn⟩
  obtain ⟨ρ, hρ⟩ := exists_conjAction_quotient Kb O X
    (fun a ha o ho => hOA a (hKb ha) o ho)
    (fun a ha y hy => by rw [hXcent a (hKb ha) y hy, mul_inv_cancel_right]; exact hy)
  set N : Subgroup O := X.subgroupOf O with hNdef
  let z₀ : Kb := ⟨z, hzKb⟩
  have hz₀ : z₀ * z₀ = 1 := Subtype.ext hz2
  have hfix : ∀ y : O ⧸ N, ρ z₀ y = y → y = 1 := by
    intro y
    refine QuotientGroup.induction_on y fun o hy => ?_
    have hzo : z * o * z⁻¹ ∈ O := hOA z hzC o o.2
    rw [hρ z₀ o hzo] at hy
    have hmem := QuotientGroup.eq.1 hy
    rw [Subgroup.mem_subgroupOf] at hmem
    simp only [Subgroup.coe_mul, Subgroup.coe_inv] at hmem
    change (z * (o : G) * z⁻¹)⁻¹ * o ∈ X at hmem
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 hmem
    have hk1 : x ^ k = z * (o : G)⁻¹ * z * o := by
      rw [hk]
      simp only [mul_inv_rev, hzi, mul_assoc]
    have hzx : z * x ^ k * z = x ^ k := by
      rw [((Commute.zpow_right (Subgroup.mem_centralizer_singleton_iff.1 hzC) k).eq), mul_assoc,
        hz2, mul_one]
    have hk2 : x ^ k = (o : G)⁻¹ * z * o * z := by
      calc x ^ k = z * x ^ k * z := hzx.symm
        _ = z * (z * (o : G)⁻¹ * z * o) * z := by rw [← hk1]
        _ = (o : G)⁻¹ * z * o * z := by simp only [mul_assoc, hzz]
    have hsq : x ^ k * x ^ k = 1 := by
      calc x ^ k * x ^ k = (z * (o : G)⁻¹ * z * o) * ((o : G)⁻¹ * z * o * z) := by
            rw [← hk1, ← hk2]
        _ = 1 := by
            simp only [mul_assoc, mul_inv_cancel_left, inv_mul_cancel_left, hzz, hz2]
    have hxk1 : x ^ k = 1 := by
      have hmem' : x ^ k ∈ X := Subgroup.mem_zpowers_iff.2 ⟨k, rfl⟩
      have h5 : orderOf (x ^ k) ∣ 5 := hxo ▸ orderOf_dvd_of_mem_zpowers hmem'
      have h2 : orderOf (x ^ k) ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact hsq)
      have h1 : orderOf (x ^ k) ∣ Nat.gcd 5 2 := Nat.dvd_gcd h5 h2
      exact orderOf_eq_one_iff.1 (Nat.dvd_one.1 (by simpa using h1))
    rw [hxk1] at hk
    have hfixo : z * o * z⁻¹ = o := inv_mul_eq_one.1 hk.symm
    have hcomm : z * (o : G) = o * z := mul_inv_eq_iff_eq_mul.1 hfixo
    exact (QuotientGroup.eq_one_iff o).2 (Subgroup.mem_subgroupOf.2 (hCOz o o.2 hcomm))
  have hNcard : Nat.card N = 5 := by
    have : Nat.card N = Nat.card X := Nat.card_congr (Subgroup.subgroupOfEquivOfLe hXO).toEquiv
    rw [this, Nat.card_zpowers, hxo]
  have hcardO : Nat.card O = Nat.card (O ⧸ N) * 5 := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup N, hNcard]
  have hYO : Nat.card (O ⧸ N) ∣ Nat.card O := Subgroup.card_quotient_dvd_card N
  have hY0 : Nat.card (O ⧸ N) ≠ 0 := Nat.card_pos.ne'
  have hO0 : Nat.card O ≠ 0 := Nat.card_pos.ne'
  have hprimeY : ∀ p : ℕ, p.Prime → p ∣ Nat.card (O ⧸ N) → p = 3 ∨ p = 5 :=
    fun p hp hpY => hprime p hp (hpY.trans hYO)
  have h3Y : (Nat.card (O ⧸ N)).factorization 3 ≤ 2 :=
    ((Nat.factorization_le_iff_dvd hY0 hO0).2 hYO 3).trans h3
  have hcommY : ∀ a b : O ⧸ N, Commute a b :=
    (show MonoidHom.FixedPointFree (ρ z₀) from hfix).commute_all_of_involutive
      (involutive_of_mul_self_eq_one ρ hz₀)
  have hcommN : ∀ a b : O, a * b * a⁻¹ * b⁻¹ ∈ N := by
    intro a b
    have h := (hcommY (QuotientGroup.mk a) (QuotientGroup.mk b)).eq
    rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_mul, QuotientGroup.mk_mul,
      QuotientGroup.mk_mul, QuotientGroup.mk_inv, QuotientGroup.mk_inv, h]
    group
  have hgen := odd_generation hz ht hzt hne O hOodd (hOA z hzC) (hOA t htC)
  set C₁ := O ⊓ Subgroup.centralizer ({t} : Set G) with hC₁
  set C₂ := O ⊓ Subgroup.centralizer ({z * t} : Set G) with hC₂
  have hXC₁ : X ≤ C₁ :=
    Subgroup.zpowers_le.2 ⟨hxO, Subgroup.mem_centralizer_singleton_iff.2 hxt.symm⟩
  have hXC₂ : X ≤ C₂ :=
    Subgroup.zpowers_le.2 ⟨hxO, Subgroup.mem_centralizer_singleton_iff.2 hztx.symm⟩
  have hCz : O ⊓ Subgroup.centralizer ({z} : Set G) ≤ X := fun o ho =>
    hCOz o ho.1 (Subgroup.mem_centralizer_singleton_iff.1 ho.2).symm
  have hsup' : C₁ ⊔ C₂ = O := by
    rw [sup_eq_right.2 (hCz.trans hXC₁)] at hgen
    exact hgen.symm
  have hsupQ : C₁.subgroupOf O ⊔ C₂.subgroupOf O = ⊤ := by
    rw [← Subgroup.subgroupOf_sup (inf_le_left : C₁ ≤ O) (inf_le_left : C₂ ≤ O), hsup']
    exact Subgroup.subgroupOf_self O
  have hcnt := card_mul_card_dvd_of_sup_eq_top N (C₁.subgroupOf O) (C₂.subgroupOf O)
    (fun n hn => Subgroup.mem_subgroupOf.2 (hXC₁ (Subgroup.mem_subgroupOf.1 hn)))
    (fun n hn => Subgroup.mem_subgroupOf.2 (hXC₂ (Subgroup.mem_subgroupOf.1 hn)))
    hsupQ hcommN
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (inf_le_left : C₁ ≤ O)).toEquiv,
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe (inf_le_left : C₂ ≤ O)).toEquiv] at hcnt
  have h5Y : (Nat.card (O ⧸ N)).factorization 5 ≤ 2 := by
    set a := (Nat.card (O ⧸ N)).factorization 5 with ha
    have hP0 : Nat.card C₁ * Nat.card C₂ ≠ 0 := (Nat.mul_pos Nat.card_pos Nat.card_pos).ne'
    have hdvd : 5 ^ (a + 2) ∣ Nat.card C₁ * Nat.card C₂ := by
      refine Dvd.dvd.trans ?_ hcnt
      rw [hcardO, hNcard, pow_add]
      calc 5 ^ a * 5 ^ 2 ∣ Nat.card (O ⧸ N) * (5 * 5) :=
            mul_dvd_mul (Nat.ordProj_dvd (Nat.card (O ⧸ N)) 5) (by norm_num)
        _ = Nat.card (O ⧸ N) * 5 * 5 := by ring
    have hle := (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_five hP0).1 hdvd
    rw [Nat.factorization_mul Nat.card_pos.ne' Nat.card_pos.ne'] at hle
    simp only [Finsupp.add_apply] at hle
    omega
  have hcard1 := eq_one_of_sl2_nine_fixedPointFree hF eb ρ z₀ hz₀ hfix hprimeY h3Y h5Y
  intro o ho
  have hsub : Subsingleton (O ⧸ N) := (Nat.card_eq_one_iff_unique.1 hcard1).1
  have h1 : (QuotientGroup.mk (⟨o, ho⟩ : O) : O ⧸ N) = 1 := Subsingleton.elim _ _
  exact Subgroup.mem_subgroupOf.1 ((QuotientGroup.eq_one_iff _).1 h1)

end CFSG.GH74.GLS.Stage4.Q9
