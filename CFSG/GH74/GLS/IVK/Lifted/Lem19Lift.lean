module

public import CFSG.GH74.GLS.IVK.Lifted.Outer19
public import CFSG.GH74.GLS.IVK.Lifted.Lem13a52

public section

namespace CFSG.GH74.GLS.IVK.Lifted

open Subgroup Matrix CFSG CFSG.GH74.GLS CFSG.GH74.GLS.IVK CFSG.GorensteinWalter CFSG.ABGLocalTools
  CFSG.Assembly.LowTwoRank CFSG.DisconnectedInvolutionGraph CFSG.DisconnectedInvolutionGraph.Helpers
  CFSG.GH74.GLS.Stage1.Thm2.Recip CFSG.GH74.GLS.Stage1.Thm3.Sec4 CFSG.GH74.GLS.Stage1.Thm3.Sec5
  CFSG.GH74.GLS.Stage1.Thm3.Sec6 CFSG.GH74.GLS.Stage1.Thm6
open scoped commutatorElement

section Quaternion

theorem exists_commuting_of_order_four
    {Q : Type} [Group Q] [Finite Q] (hq : CFSG.IsQuasisimple Q)
    (hno : ∀ u v : Q, orderOf u = 2 → orderOf v = 2 → u * v = v * u → u = v)
    (hconj : ∀ a b : Q, orderOf a = 4 → orderOf b = 4 → IsConj a b) (P : Sylow 2 Q) {k : Q}
    (hk : orderOf k = 4) :
    ∃ u : Q, k * u = u * k ∧ (∃ a : ℕ, orderOf u = 2 ^ a) ∧ 4 ≤ orderOf u ∧
      2 * orderOf u = Nat.card ↥(P : Subgroup Q) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hncyc := sylow_two_not_cyclic_of_quasisimple hq P
  have hrank : NoCommutingDistinctInvolutions ↥(P : Subgroup Q) := by
    intro u v huv
    have hu : orderOf ((u.1 : ↥(P : Subgroup Q)) : Q) = 2 := by
      rw [Subgroup.orderOf_coe]
      exact u.2
    have hv : orderOf ((v.1 : ↥(P : Subgroup Q)) : Q) = 2 := by
      rw [Subgroup.orderOf_coe]
      exact v.2
    have hcomm : ((u.1 : ↥(P : Subgroup Q)) : Q) * ((v.1 : ↥(P : Subgroup Q)) : Q) =
        ((v.1 : ↥(P : Subgroup Q)) : Q) * ((u.1 : ↥(P : Subgroup Q)) : Q) := by
      have := congrArg (fun x : ↥(P : Subgroup Q) => (x : Q)) huv
      simpa using this
    exact Subtype.ext (Subtype.ext (hno _ _ hu hv hcomm))
  rcases rank_one_two_cyclic_or_quaternion P.isPGroup' hrank with hc | ⟨e, he1, ⟨ε⟩⟩
  · exact absurd hc hncyc
  · obtain ⟨e', rfl⟩ : ∃ e' : ℕ, e = e' + 1 := ⟨e - 1, by omega⟩
    have : NeZero (2 ^ (e' + 1)) := ⟨by positivity⟩
    set g : Q := ((ε (QuaternionGroup.a 1) : ↥(P : Subgroup Q)) : Q) with hg
    have hgo : orderOf g = 2 * 2 ^ (e' + 1) := by
      rw [hg, Subgroup.orderOf_coe, MulEquiv.orderOf_eq]
      exact QuaternionGroup.orderOf_a_one
    have hgo' : orderOf g = 2 ^ (e' + 2) := by
      rw [hgo]
      ring
    set k₀ : Q := g ^ (2 ^ e') with hk₀
    have hk₀o : orderOf k₀ = 4 := by
      rw [hk₀, orderOf_pow_of_dvd (by positivity) (by rw [hgo']; exact pow_dvd_pow 2 (by omega)), hgo']
      have : (2 : ℕ) ^ (e' + 2) = 4 * 2 ^ e' := by ring
      rw [this]
      exact Nat.mul_div_cancel _ (by positivity)
    obtain ⟨c, hc⟩ := isConj_iff.1 (hconj k₀ k hk₀o hk)
    have hcomm : k₀ * g = g * k₀ := (Commute.pow_left (Commute.refl g) _).eq
    refine ⟨c * g * c⁻¹, ?_, ⟨e' + 2, ?_⟩, ?_, ?_⟩
    · rw [← hc]
      calc c * k₀ * c⁻¹ * (c * g * c⁻¹) = c * (k₀ * g) * c⁻¹ := by group
        _ = c * (g * k₀) * c⁻¹ := by rw [hcomm]
        _ = c * g * c⁻¹ * (c * k₀ * c⁻¹) := by group
    · have := (MulAut.conj c).orderOf_eq g
      rw [MulAut.conj_apply] at this
      rw [this, hgo']
    · have := (MulAut.conj c).orderOf_eq g
      rw [MulAut.conj_apply] at this
      rw [this, hgo']
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ (e' + 2) := Nat.pow_le_pow_right (by norm_num) (by omega)
    · have := (MulAut.conj c).orderOf_eq g
      rw [MulAut.conj_apply] at this
      rw [this, hgo', Nat.card_congr ε.toEquiv.symm, Nat.card_eq_fintype_card, QuaternionGroup.card]
      ring

end Quaternion

section Inner

variable {G : Type} [Group G] [Finite G]

theorem exists_fixed_lift {K : Subgroup G} {t : G} (htN : t ∈ normalizer (K : Set G)) (htt : t * t = 1)
    {x₀ : G} (hx₀ : x₀ ∈ K) (hfix : phi K t htN (hatMk K ⟨x₀, hx₀⟩) = hatMk K ⟨x₀, hx₀⟩) :
    ∃ (x : G) (hx : x ∈ K), t * x = x * t ∧ hatMk K ⟨x, hx⟩ = hatMk K ⟨x₀, hx₀⟩ := by
  have ht_inv : t⁻¹ = t := inv_eq_of_mul_eq_one_right htt
  have hy₁ : t * x₀ * t⁻¹ ∈ K := (Subgroup.mem_normalizer_iff.1 htN x₀).1 hx₀
  have hfix' : hatMk K ⟨t * x₀ * t⁻¹, hy₁⟩ = hatMk K ⟨x₀, hx₀⟩ := by
    rw [← hfix, phi_mk K htN ⟨x₀, hx₀⟩]
  set o : G := x₀⁻¹ * (t * x₀ * t⁻¹) with ho_def
  have hoK : o ∈ K := K.mul_mem (K.inv_mem hx₀) hy₁
  have ho : o ∈ pPrimeCoreOf 2 K := by
    refine (hatMk_eq_one_iff K ⟨o, hoK⟩).1 ?_
    have : (⟨o, hoK⟩ : ↥K) = ⟨x₀, hx₀⟩⁻¹ * ⟨t * x₀ * t⁻¹, hy₁⟩ := rfl
    rw [this, map_mul, map_inv, hfix', inv_mul_cancel]
  have hx₀o : t * x₀ * t⁻¹ = x₀ * o := by
    rw [ho_def]
    group
  have hto : t * o * t⁻¹ = o⁻¹ := by
    have h1 : x₀ = (t * x₀ * t⁻¹) * (t * o * t⁻¹) := by
      calc x₀ = (t * t) * x₀ * (t * t)⁻¹ := by rw [htt]; group
        _ = t * (t * x₀ * t⁻¹) * t⁻¹ := by group
        _ = t * (x₀ * o) * t⁻¹ := by rw [hx₀o]
        _ = (t * x₀ * t⁻¹) * (t * o * t⁻¹) := by group
    rw [hx₀o] at h1
    have h2 : o * (t * o * t⁻¹) = 1 := by
      have : x₀ * (o * (t * o * t⁻¹)) = x₀ * 1 := by rw [← mul_assoc, mul_one]; exact h1.symm
      exact mul_left_cancel this
    exact eq_inv_of_mul_eq_one_right h2
  have hodd : Odd (orderOf o) :=
    Odd.of_dvd_nat (TwoThin.card_pPrimeCoreOf_odd K) (Subgroup.orderOf_dvd_natCard _ ho)
  obtain ⟨j, hj⟩ := hodd
  have hoj : o ^ (2 * j + 1) = 1 := by rw [← hj]; exact pow_orderOf_eq_one o
  have hoj' : o * (o⁻¹) ^ (j + 1) = o ^ (j + 1) := by
    rw [inv_pow, mul_inv_eq_iff_eq_mul, ← pow_add, show j + 1 + (j + 1) = (2 * j + 1) + 1 by ring,
      pow_succ, hoj, one_mul]
  have hopow : o ^ (j + 1) ∈ pPrimeCoreOf 2 K := pow_mem ho _
  refine ⟨x₀ * o ^ (j + 1), K.mul_mem hx₀ (TwoThin.pPrimeCoreOf_le K hopow), ?_, ?_⟩
  · have h3 : t * (x₀ * o ^ (j + 1)) * t⁻¹ = x₀ * o ^ (j + 1) := by
      calc t * (x₀ * o ^ (j + 1)) * t⁻¹ = (t * x₀ * t⁻¹) * (t * o ^ (j + 1) * t⁻¹) := by group
        _ = (t * x₀ * t⁻¹) * (t * o * t⁻¹) ^ (j + 1) := by rw [conj_pow]
        _ = x₀ * o ^ (j + 1) := by rw [hx₀o, hto, mul_assoc, hoj']
    exact mul_inv_eq_iff_eq_mul.1 h3
  · have : (⟨x₀ * o ^ (j + 1), K.mul_mem hx₀ (TwoThin.pPrimeCoreOf_le K hopow)⟩ : ↥K) =
        ⟨x₀, hx₀⟩ * ⟨o ^ (j + 1), TwoThin.pPrimeCoreOf_le K hopow⟩ := rfl
    rw [this, map_mul, (hatMk_eq_one_iff K ⟨o ^ (j + 1), TwoThin.pPrimeCoreOf_le K hopow⟩).2 hopow,
      mul_one]

theorem exists_u_of_inner
    {S K : Subgroup G} {t : G} (hS2 : IsPGroup 2 ↥S)
    (hsyl : ∃ P : Sylow 2 ↥K, (P : Subgroup ↥K).map K.subtype = S ⊓ K) (hOK : HatOK (Hat K))
    (hconj : ∀ a b : Hat K, orderOf a = 4 → orderOf b = 4 → IsConj a b)
    (htN : t ∈ normalizer (K : Set G)) (htt : t * t = 1)
    (hin : phi K t htN ∈ innOf (Hat K)) (hne : phi K t htN ≠ 1) :
    ∃ u ∈ K, t * u = u * t ∧ 4 ≤ orderOf u ∧ 2 * orderOf u = Nat.card ↥(S ⊓ K) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨k, hk⟩ := hin
  have hφ2 : phi K t htN * phi K t htN = 1 := phi_mul_self K htN htt
  have hkk : MulAut.conj (k * k) = 1 := by rw [map_mul, hk]; exact hφ2
  have hkc2 : k * k ∈ Subgroup.center (Hat K) := mem_center_of_conj_eq_one hkk
  have hk4 : (k * k) * (k * k) = 1 := sq_eq_one_of_card_center hOK.sl2.2 _ hkc2
  have hknc : ¬ k * k = 1 := by
    intro h
    have hc := hat_sq_eq_one_mem_center hOK h
    exact hne (by rw [← hk]; exact conj_eq_one_of_mem_center hc)
  have hko : orderOf k = 4 := by
    have h := orderOf_eq_prime_pow (p := 2) (n := 1) (x := k) (by simpa [pow_two] using hknc)
      (by
        have : k ^ 2 ^ (1 + 1) = (k * k) * (k * k) := by
          have e : (2 : ℕ) ^ (1 + 1) = 2 + 2 := by norm_num
          rw [e, pow_add, pow_two]
        rw [this]
        exact hk4)
    simpa using h
  obtain ⟨Pbar, hPbar⟩ := exists_sylow_hatImg hsyl
  have hno := noCommInv_of_pRank hOK.rank
  obtain ⟨u', hu'k, ⟨a, hu'o⟩, hu'4, hu'P⟩ :=
    exists_commuting_of_order_four hOK.quasi hno hconj Pbar hko
  have hfixu' : phi K t htN u' = u' := by
    rw [← hk, MulAut.conj_apply]
    exact mul_inv_eq_iff_eq_mul.2 hu'k
  obtain ⟨x₀, rfl⟩ := hatMk_surjective K u'
  obtain ⟨x, hxK, hxt, hxx₀⟩ := exists_fixed_lift htN htt x₀.2 (by simpa using hfixu')
  have hxx₀' : hatMk K ⟨x, hxK⟩ = hatMk K x₀ := hxx₀
  have hn0 : orderOf x ≠ 0 := (orderOf_pos x).ne'
  obtain ⟨a₂, m, hm, hnm⟩ := Nat.exists_eq_two_pow_mul_odd hn0
  have hm0 : m ≠ 0 := hm.pos.ne'
  have hxo : orderOf (x ^ m) = 2 ^ a₂ := by
    rw [orderOf_pow_of_dvd hm0 (by rw [hnm]; exact Dvd.intro_left _ rfl), hnm]
    exact Nat.mul_div_cancel _ (Nat.pos_of_ne_zero hm0)
  have hxP : IsPGroup 2 ↥(zpowers (x ^ m)) :=
    IsPGroup.of_card (n := a₂) (by rw [Nat.card_zpowers, hxo])
  have hxmK : x ^ m ∈ K := pow_mem hxK m
  have hzle : zpowers (x ^ m) ≤ K := zpowers_le.2 hxmK
  have hord1 : orderOf (hatMk K ⟨x ^ m, hzle (mem_zpowers _)⟩) = orderOf (x ^ m) :=
    orderOf_hatMk hzle hxP (mem_zpowers _)
  have himg : hatMk K ⟨x ^ m, hzle (mem_zpowers _)⟩ = (hatMk K x₀) ^ m := by
    have : (⟨x ^ m, hzle (mem_zpowers _)⟩ : ↥K) = (⟨x, hxK⟩ : ↥K) ^ m := rfl
    rw [this, map_pow, hxx₀']
  have hcop : (orderOf (hatMk K x₀)).Coprime m := by
    rw [hu'o]
    exact Nat.Coprime.pow_left a (Nat.coprime_two_left.2 hm)
  have hord2 : orderOf (x ^ m) = orderOf (hatMk K x₀) := by
    rw [← hord1, himg, hcop.orderOf_pow]
  refine ⟨x ^ m, hxmK, (Commute.pow_right (show Commute t x from hxt) m).eq, ?_, ?_⟩
  · rw [hord2]
    exact hu'4
  · rw [hord2, hu'P, hPbar, card_hatImg_of_pgroup inf_le_right hS2.to_inf_left]

end Inner

section Outer

variable {G : Type} [Group G] [Finite G]

theorem card_P_eq_abs {S K : Subgroup G} (hS2 : IsPGroup 2 ↥S)
    (hsyl : ∃ P : Sylow 2 ↥K, (P : Subgroup ↥K).map K.subtype = S ⊓ K) :
    Nat.card ↥(S ⊓ K) = 2 ^ (Nat.card (Hat K)).factorization 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨Pbar, hPbar⟩ := exists_sylow_hatImg hsyl
  have h1 := Sylow.card_eq_multiplicity Pbar
  rw [hPbar, card_hatImg_of_pgroup inf_le_right hS2.to_inf_left] at h1
  exact h1

theorem semidihedral_of_outer_abs
    {F : Type} [Field F] [Finite F] {z : G} {S K : Subgroup G}
    (hS2 : IsPGroup 2 ↥S) (hSC : S ≤ centralizer ({z} : Set G)) (hz2 : orderOf z = 2)
    (hKC : K ≤ centralizer ({z} : Set G)) (hrk : pRank 2 ↥K = 1)
    (hsyl : ∃ P : Sylow 2 ↥K, (P : Subgroup ↥K).map K.subtype = S ⊓ K) (hzS : z ∈ S) (hzK : z ∈ K)
    {y : G} (hyS : y ∈ S) (hyy : y * y = 1) (hyN : y ∈ normalizer (K : Set G)) (hyP : y ∉ S ⊓ K)
    (hOK : HatOK (Hat K)) (hodd : Odd (Nat.card F)) (e : Hat K ≃* SpecialLinearGroup (Fin 2) F)
    (θ : ↥(K ⊔ zpowers y) →* PGL2 F)
    (hker : θ.ker = (pPrimeCoreOf 2 K ⊔ zpowers z).subgroupOf (K ⊔ zpowers y)) :
    ∃ n, IVK.IsSemidihedralTwoGroup ↥((S ⊓ K) ⊔ zpowers y) n := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set P : Subgroup G := S ⊓ K with hPdef
  set T₁ : Subgroup G := P ⊔ zpowers y with hT₁
  have hzP : z ∈ P := ⟨hzS, hzK⟩
  have hz1G : z ≠ 1 := ne_one_of_orderOf_eq_two hz2
  have hzzG : z * z = 1 := mul_self_eq_one_of_orderOf_eq_two hz2
  have hT₁S : T₁ ≤ S := sup_le inf_le_left (zpowers_le.2 hyS)
  have hT₁X : T₁ ≤ K ⊔ zpowers y := sup_le (inf_le_right.trans le_sup_left) le_sup_right
  have hPT₁ : P ≤ T₁ := le_sup_left
  have hT2 : IsPGroup 2 ↥T₁ := hS2.to_le hT₁S
  have hP2 : IsPGroup 2 ↥P := hS2.to_inf_left
  have hyPn : y ∈ normalizer (P : Set G) := by
    apply Subgroup.mem_normalizer_fintype
    intro n hn
    exact ⟨S.mul_mem (S.mul_mem hyS hn.1) (S.inv_mem hyS), (Subgroup.mem_normalizer_iff.1 hyN n).1 hn.2⟩
  have hindex := exists_index_two_pair (P := P) (T₁ := T₁) hT₁ hyP hyy hyPn
  have hzT₁ : z ∈ T₁ := hPT₁ hzP
  have hyT₁ : y ∈ T₁ := mem_sup_right (mem_zpowers y)
  let π : ↥T₁ →* PGL2 F := θ.comp (Subgroup.inclusion hT₁X)
  let z' : ↥T₁ := ⟨z, hzT₁⟩
  let y' : ↥T₁ := ⟨y, hyT₁⟩
  have hz1 : z' ≠ 1 := fun h1 => hz1G (congrArg Subtype.val h1)
  have hzz : z' * z' = 1 := Subtype.ext hzzG
  have hSKmem : ∀ t : ↥T₁, ∀ ht : (t : G) ∈ pPrimeCoreOf 2 K ⊔ zpowers z, (t : G) ∈ S ⊓ K := by
    intro t ht
    obtain ⟨hxK, -⟩ := hatMk_of_mem_sup_zpowers hzK hz2 ht
    exact ⟨hT₁S t.2, hxK⟩
  have hker' : ∀ t : ↥T₁, π t = 1 ↔ t = 1 ∨ t = z' := by
    intro t
    have h1 : π t = 1 ↔ (t : G) ∈ pPrimeCoreOf 2 K ⊔ zpowers z := by
      show θ (Subgroup.inclusion hT₁X t) = 1 ↔ _
      rw [← MonoidHom.mem_ker, hker, Subgroup.mem_subgroupOf]
      rfl
    rw [h1]
    constructor
    · intro ht
      obtain ⟨hxK, hx⟩ := hatMk_of_mem_sup_zpowers hzK hz2 ht
      have hxSK := hSKmem t ht
      rcases hx with hx | hx
      · left
        apply Subtype.ext
        have := eq_of_hatMk_eq (inf_le_right : S ⊓ K ≤ K) hP2 hxSK (one_mem (S ⊓ K))
          (by rw [hx]; exact (map_one (hatMk K)).symm)
        exact this
      · right
        apply Subtype.ext
        exact eq_of_hatMk_eq (inf_le_right : S ⊓ K ≤ K) hP2 hxSK hzP hx
    · rintro (h2 | h2)
      · rw [h2]
        exact one_mem _
      · rw [h2]
        exact mem_sup_right (mem_zpowers z)
  have hcardHat : Nat.card (Hat K) = Nat.card (PGL2 F) := by
    rw [Nat.card_congr e.toEquiv, sl2_card_formula, pgl2_card_formula]
  have hQ : Nat.card ↥(P.subgroupOf T₁) = Nat.card ↥P :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hPT₁).toEquiv
  have hQcard : Nat.card ↥(P.subgroupOf T₁) * 2 = Nat.card ↥T₁ := by
    have := Subgroup.card_mul_index (P.subgroupOf T₁)
    rw [hindex] at this
    exact this
  have hcP : Nat.card ↥P = 2 ^ (Nat.card (Hat K)).factorization 2 := card_P_eq_abs hS2 hsyl
  have hcard : Nat.card ↥T₁ = 2 * 2 ^ (Nat.card (PGL2 F)).factorization 2 := by
    rw [← hQcard, hQ, hcP, hcardHat]
    ring
  have hzQ : z' ∈ P.subgroupOf T₁ := hzP
  have hno := noCommInv_of_pRank hOK.rank
  have hQu : ∀ x ∈ P.subgroupOf T₁, x * x = 1 → x = 1 ∨ x = z' := by
    intro x hxQ hxx
    have hxP : (x : G) ∈ P := hxQ
    have hxx' : (x : G) * (x : G) = 1 := congrArg Subtype.val hxx
    by_cases hx1 : x = 1
    · exact Or.inl hx1
    right
    have hx1' : (x : G) ≠ 1 := fun h1 => hx1 (Subtype.ext h1)
    have hord : orderOf (x : G) = 2 := orderOf_eq_two_of_mul_self_eq_one hxx' hx1'
    have hcomm : (x : G) * z = z * (x : G) :=
      Subgroup.mem_centralizer_singleton_iff.1 (hKC hxP.2)
    exact Subtype.ext (eq_of_pRank_one (hrk) hxP.2 hzK hord hz2 hcomm)
  have hzc : ∀ g : ↥T₁, g * z' = z' * g := by
    intro g
    apply Subtype.ext
    exact Subgroup.mem_centralizer_singleton_iff.1 (hSC (hT₁S g.2))
  have hnoncomm : ∃ a ∈ P, ∃ b ∈ P, a * b ≠ b * a := by
    obtain ⟨Pbar, hPbar⟩ := exists_sylow_hatImg hsyl
    obtain ⟨ab, hab, bb, hbb, hne⟩ := sylow_exists_noncomm hOK.quasi hno Pbar
    rw [hPbar] at hab hbb
    obtain ⟨a, haP, rfl⟩ := mem_hatImg.1 hab
    obtain ⟨b, hbP, rfl⟩ := mem_hatImg.1 hbb
    refine ⟨(a : G), haP, (b : G), hbP, fun hc => hne ?_⟩
    rw [← map_mul, ← map_mul]
    congr 1
    apply Subtype.ext
    exact hc
  have hQnc : ∀ q₀ : ↥T₁, ¬ P.subgroupOf T₁ ≤ zpowers q₀ ⊔ zpowers z' := by
    intro q₀ hle
    obtain ⟨a, haP, b, hbP, hne⟩ := hnoncomm
    apply hne
    have ha : (⟨a, hPT₁ haP⟩ : ↥T₁) ∈ P.subgroupOf T₁ := haP
    have hb : (⟨b, hPT₁ hbP⟩ : ↥T₁) ∈ P.subgroupOf T₁ := hbP
    have := IVK.mul_comm_of_mem_zpowers_sup hzc (hle ha) (hle hb)
    exact congrArg Subtype.val this
  have hres := tshape_of_pgl_hom hT2 hodd π hz1 hzz hker' hcard (P.subgroupOf T₁) hzQ hQcard hQu
    hQnc
  rcases hres with ⟨n, hn3, ⟨ι⟩⟩ | hsd
  · exfalso
    have : NeZero (2 ^ (n - 2)) := ⟨by positivity⟩
    have hy1 : y' ≠ 1 := fun h1 => hyP (by
      have : y = 1 := congrArg Subtype.val h1
      rw [this]
      exact one_mem P)
    have hy'y : y' * y' = 1 := Subtype.ext hyy
    have h1 := quat_invol (2 ^ (n - 2)) (ι y') (by rw [← map_mul, hy'y, map_one])
      (fun h => hy1 (ι.injective (by rw [h, map_one])))
    have h2 := quat_invol (2 ^ (n - 2)) (ι z') (by rw [← map_mul, hzz, map_one])
      (fun h => hz1 (ι.injective (by rw [h, map_one])))
    have hzy : z' = y' := ι.injective (h2.trans h1.symm)
    have hzy' : z = y := congrArg Subtype.val hzy
    exact hyP (hzy' ▸ hzP)
  · exact hsd


end Outer

section Main

theorem ivk_1_9_lifted_of_II4
    (h44 : II4_44) (h2A7 : II4_2A7) (hAut : II4_Aut)
    (hII : II4_4_4_center) : IVK_1_9_lifted := by
  intro G _ _ z S K₁ K₂ hstd t htS ht2 htN hF
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hM := m4_of_std hII hstd
  have hK₁m : K₁ ∈ ({K₁, K₂} : Set (Subgroup G)) := Set.mem_insert _ _
  have hpc₁ : IsPCompIn 2 (Cz z) K₁ := rigid_isPCompIn (std4_comp_rigid hstd hK₁m)
  have hOK := std4_hatOK h44 hstd hK₁m
  have hrk : pRank 2 ↥K₁ = 1 := hstd.comp_pRank (Or.inl rfl)
  have hsyl := std4_exists_sylow_P hstd (Or.inl rfl)
  have hzS : z ∈ S := hM.z_mem_S
  have hzK : z ∈ K₁ := hM.z_mem_comp (Or.inl rfl)
  have hz2 : orderOf z = 2 := hstd.orderOf_z
  have hKC : K₁ ≤ centralizer ({z} : Set G) := hpc₁.1
  have hSC : S ≤ centralizer ({z} : Set G) := hM.S_syl.1
  have hS2 : IsPGroup 2 ↥S := hM.S_pgroup
  have htt : t * t = 1 := by
    have := pow_orderOf_eq_one t
    rwa [ht2, sq] at this
  have hPK : Pz S z ⊓ K₁ = S ⊓ K₁ := by
    rw [Pz_eq hstd]
    unfold M.Pm
    rw [inf_assoc, inf_eq_right.2 (le_sup_left : K₁ ≤ K₁ ⊔ K₂)]
  rw [hPK]
  by_cases hin : phi K₁ t htN ∈ innOf (Hat K₁)
  · right
    have hne : phi K₁ t htN ≠ 1 := fun h1 =>
      hF (inducesFAut_of_mem_cSec hstd.simple hz2 hpc₁ hrk ((phi_eq_one_iff K₁ htN).1 h1))
    exact exists_u_of_inner hS2 hsyl hOK ((hAut (Hat K₁) hOK.sl2).2.1) htN htt hin hne
  · left
    have htP : t ∉ S ⊓ K₁ := by
      intro h
      apply hin
      rw [phi_of_mem K₁ h.2]
      exact ⟨_, rfl⟩
    have hcen : Nat.card (Subgroup.center (Hat K₁)) = 2 := hOK.sl2.2
    have hφ2 : phi K₁ t htN * phi K₁ t htN = 1 := phi_mul_self K₁ htN htt
    rcases sl_or_a7 hOK.sl2 with ⟨F, hFf, hFin, hodd, h3, ⟨e⟩⟩ | h7
    · have hα2 : MulAut.congr e (phi K₁ t htN) * MulAut.congr e (phi K₁ t htN) = 1 := by
        rw [← map_mul, hφ2, map_one]
      have hσ : (gammaOf hodd h3 (MulAut.congr e (phi K₁ t htN))).right = 1 := by
        by_contra hσ
        apply hF
        refine ⟨htN, ?_⟩
        exact ⟨hOK.quasi, hOK.kgrp, hOK.rank, exists_pow_two_orderOf hφ2,
          fixedCond_of_congr e (fixedCond_of_field_part hodd h3 _ hα2 hσ)⟩
      obtain ⟨θ, -, hker⟩ := exists_pgl_hom hodd h3 e hzK hKC hz2 hcen htN htt hin hσ
      exact semidihedral_of_outer_abs hS2 hSC hz2 hKC hrk hsyl hzS hzK htS htt htN htP hOK hodd e θ
        hker
    · exfalso
      exact hF ⟨htN, (h2A7 _ h7).2.2.1 _ hφ2 hin hOK.kgrp⟩

end Main

end CFSG.GH74.GLS.IVK.Lifted
