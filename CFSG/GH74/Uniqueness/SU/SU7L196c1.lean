module

public import CFSG.GH74.Uniqueness.SU.SU9CM
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.NormalKleinFourIndexThree
public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

namespace CFSG.GH74.Uniqueness.SU.SU7

open Subgroup CFSG.GH74.Uniqueness.SU.SU4 CFSG.GH74.Uniqueness.SU.SU5 CFSG
  CFSG.GH74.Uniqueness.SU.SU9
open scoped commutatorElement

namespace L196c

section Generic

variable {G : Type*} [Group G]

theorem isKleinFour_of_card_four_sq_one (K : Subgroup G) (hK4 : Nat.card K = 4)
    (hsq : ∀ k ∈ K, k * k = 1) : IsKleinFour ↥K := by
  have hfin : Finite ↥K := Nat.finite_of_card_ne_zero (by omega)
  refine ⟨hK4, ?_⟩
  have hdvd : Monoid.exponent ↥K ∣ 2 := by
    apply Monoid.exponent_dvd_of_forall_pow_eq_one
    intro g
    apply Subtype.ext
    simpa [pow_two] using hsq g g.2
  rcases (Nat.dvd_prime Nat.prime_two).1 hdvd with h | h
  · exfalso
    have hsub : Subsingleton ↥K := Monoid.exp_eq_one_iff.1 h
    have := Finite.card_le_one_iff_subsingleton.2 hsub
    omega
  · exact h

theorem nonempty_mulEquiv_klein (K : Subgroup G) (hK4 : Nat.card K = 4)
    (hsq : ∀ k ∈ K, k * k = 1) :
    Nonempty (↥K ≃* Multiplicative (ZMod 2) × Multiplicative (ZMod 2)) := by
  have : IsKleinFour ↥K := isKleinFour_of_card_four_sq_one K hK4 hsq
  obtain ⟨e⟩ := IsKleinFour.nonempty_mulEquiv (G₁ := ↥K) (G₂ := Multiplicative (ZMod 2 × ZMod 2))
  exact ⟨e.trans (MulEquiv.prodMultiplicative (ZMod 2) (ZMod 2))⟩

theorem cent_of_mem_zpowers {w p : G} (hw3 : w ^ 3 = 1) (hp : p ∈ zpowers w) (hp1 : p ≠ 1)
    {u : G} (hpu : p * u = u * p) : w * u = u * w := by
  obtain ⟨j, rfl⟩ := mem_zpowers_iff.1 hp
  have hw3' : w ^ (3 : ℤ) = 1 := by exact_mod_cast hw3
  have hj : w ^ j = w ^ (j % 3) := zpow_eq_zpow_emod j hw3'
  have hcase : j % 3 = 0 ∨ j % 3 = 1 ∨ j % 3 = 2 := by omega
  rcases hcase with h | h | h
  · exact absurd (by rw [hj, h, zpow_zero]) hp1
  · rw [hj, h, zpow_one] at hpu
    exact hpu
  · rw [hj, h] at hpu
    have hc : Commute (w ^ (2 : ℤ)) u := hpu
    have hc' : Commute ((w ^ (2 : ℤ)) ^ 2) u := hc.pow_left 2
    have e : (w ^ (2 : ℤ)) ^ 2 = w := by
      rw [← zpow_natCast, ← zpow_mul]
      have : w ^ ((2 : ℤ) * (2 : ℕ)) = w ^ ((3 : ℤ) + 1) := by norm_num
      rw [this, zpow_add, hw3', one_mul, zpow_one]
    rw [e] at hc'
    exact hc'

theorem commutator_pq_mem {U : Subgroup G} {p p' : G} (hpp : p * p' = p' * p)
    (hp : ∀ u ∈ U, p * u * p⁻¹ ∈ U) (hp' : ∀ u ∈ U, p' * u * p'⁻¹ ∈ U)
    (hp1 : ∀ u ∈ U, p⁻¹ * u * p ∈ U) (hp'1 : ∀ u ∈ U, p'⁻¹ * u * p' ∈ U) {q q' : G}
    (hq : q ∈ U) (hq' : q' ∈ U) :
    (p * q) * (p' * q') * (p * q)⁻¹ * (p' * q')⁻¹ ∈ U := by
  have ha₁ : p'⁻¹ * q * p' ∈ U := hp'1 q hq
  have ha₂ : p⁻¹ * q' * p ∈ U := hp1 q' hq'
  have hin : (p'⁻¹ * q * p') * q' * q⁻¹ * (p⁻¹ * q' * p)⁻¹ ∈ U :=
    U.mul_mem (U.mul_mem (U.mul_mem ha₁ hq') (U.inv_mem hq)) (U.inv_mem ha₂)
  have hconj : (p * p') * ((p'⁻¹ * q * p') * q' * q⁻¹ * (p⁻¹ * q' * p)⁻¹) * (p * p')⁻¹ ∈ U := by
    have h1 := hp' _ hin
    have h2 := hp _ h1
    have e : (p * p') * ((p'⁻¹ * q * p') * q' * q⁻¹ * (p⁻¹ * q' * p)⁻¹) * (p * p')⁻¹ =
        p * (p' * ((p'⁻¹ * q * p') * q' * q⁻¹ * (p⁻¹ * q' * p)⁻¹) * p'⁻¹) * p⁻¹ := by group
    rw [e]; exact h2
  have hc : p * p'⁻¹ = p'⁻¹ * p := by
    calc p * p'⁻¹ = p'⁻¹ * (p' * p) * p'⁻¹ := by group
      _ = p'⁻¹ * (p * p') * p'⁻¹ := by rw [hpp]
      _ = p'⁻¹ * p := by group
  have e2 : (p * q) * (p' * q') * (p * q)⁻¹ * (p' * q')⁻¹ =
      (p * p') * ((p'⁻¹ * q * p') * q' * q⁻¹ * (p⁻¹ * q' * p)⁻¹) * (p * p')⁻¹ := by
    symm
    calc (p * p') * ((p'⁻¹ * q * p') * q' * q⁻¹ * (p⁻¹ * q' * p)⁻¹) * (p * p')⁻¹
        = p * q * p' * q' * q⁻¹ * p⁻¹ * q'⁻¹ * (p * p'⁻¹) * p⁻¹ := by group
      _ = p * q * p' * q' * q⁻¹ * p⁻¹ * q'⁻¹ * (p'⁻¹ * p) * p⁻¹ := by rw [hc]
      _ = (p * q) * (p' * q') * (p * q)⁻¹ * (p' * q')⁻¹ := by group
  rw [e2]; exact hconj

theorem exists_comm_eq_of_fpf {U : Subgroup G} [Finite U]
    (hUc : ∀ a ∈ U, ∀ b ∈ U, a * b = b * a) {w : G} (hwU : ∀ u ∈ U, w * u * w⁻¹ ∈ U)
    (hfpf : ∀ u ∈ U, u ≠ 1 → w * u * w⁻¹ ≠ u) :
    ∀ v ∈ U, ∃ u ∈ U, w * u * w⁻¹ * u⁻¹ = v := by
  let f : ↥U → ↥U := fun u => ⟨w * u * w⁻¹ * (u : G)⁻¹, U.mul_mem (hwU u u.2) (U.inv_mem u.2)⟩
  let φ : ↥U →* ↥U := MonoidHom.mk' f (by
    intro u u'
    apply Subtype.ext
    show w * ((u : G) * u') * w⁻¹ * ((u : G) * u')⁻¹ =
      (w * (u : G) * w⁻¹ * (u : G)⁻¹) * (w * (u' : G) * w⁻¹ * (u' : G)⁻¹)
    have hx' : w * (u' : G) * w⁻¹ ∈ U := hwU u' u'.2
    have hc : (u : G)⁻¹ * (w * (u' : G) * w⁻¹) = (w * (u' : G) * w⁻¹) * (u : G)⁻¹ :=
      hUc _ (U.inv_mem u.2) _ hx'
    have hc2 : (u' : G)⁻¹ * (u : G)⁻¹ = (u : G)⁻¹ * (u' : G)⁻¹ :=
      hUc _ (U.inv_mem u'.2) _ (U.inv_mem u.2)
    calc w * ((u : G) * u') * w⁻¹ * ((u : G) * u')⁻¹
        = (w * u * w⁻¹) * (w * u' * w⁻¹) * ((u' : G)⁻¹ * (u : G)⁻¹) := by group
      _ = (w * u * w⁻¹) * (w * u' * w⁻¹) * ((u : G)⁻¹ * (u' : G)⁻¹) := by rw [hc2]
      _ = (w * u * w⁻¹) * ((w * u' * w⁻¹) * (u : G)⁻¹) * (u' : G)⁻¹ := by group
      _ = (w * u * w⁻¹) * ((u : G)⁻¹ * (w * u' * w⁻¹)) * (u' : G)⁻¹ := by rw [← hc]
      _ = (w * u * w⁻¹ * (u : G)⁻¹) * (w * u' * w⁻¹ * (u' : G)⁻¹) := by group)
  have hinj : Function.Injective φ := by
    rw [injective_iff_map_eq_one]
    intro u hu
    by_contra hu1
    have h1 : w * (u : G) * w⁻¹ * (u : G)⁻¹ = 1 := congrArg Subtype.val hu
    apply hfpf u u.2 (fun h => hu1 (Subtype.ext h))
    exact mul_inv_eq_one.1 h1
  have hsurj : Function.Surjective φ := Finite.surjective_of_injective hinj
  intro v hv
  obtain ⟨u, hu⟩ := hsurj ⟨v, hv⟩
  exact ⟨u, u.2, congrArg Subtype.val hu⟩

theorem commutator_mul_central {y y' a b : G} (hya : Commute y a) (hyb : Commute y b)
    (hy'a : Commute y' a) (hy'b : Commute y' b) (hyy' : Commute y y') :
    (y * a) * (y' * b) * (y * a)⁻¹ * (y' * b)⁻¹ = a * b * a⁻¹ * b⁻¹ := by
  have h1 : Commute y (a * b * a⁻¹) := (hya.mul_right hyb).mul_right hya.inv_right
  have h2 : Commute y' (a * b * a⁻¹ * b⁻¹) :=
    ((hy'a.mul_right hy'b).mul_right hy'a.inv_right).mul_right hy'b.inv_right
  calc (y * a) * (y' * b) * (y * a)⁻¹ * (y' * b)⁻¹
      = y * (a * y') * b * a⁻¹ * y⁻¹ * b⁻¹ * y'⁻¹ := by group
    _ = y * (y' * a) * b * a⁻¹ * y⁻¹ * b⁻¹ * y'⁻¹ := by rw [← hy'a.eq]
    _ = y * y' * ((a * b * a⁻¹) * y⁻¹) * b⁻¹ * y'⁻¹ := by group
    _ = y * y' * (y⁻¹ * (a * b * a⁻¹)) * b⁻¹ * y'⁻¹ := by rw [h1.inv_left.eq.symm]
    _ = y' * (a * b * a⁻¹ * b⁻¹) * y'⁻¹ := by
      have : y * y' * y⁻¹ = y' := by rw [hyy'.eq]; group
      calc y * y' * (y⁻¹ * (a * b * a⁻¹)) * b⁻¹ * y'⁻¹
          = (y * y' * y⁻¹) * (a * b * a⁻¹) * b⁻¹ * y'⁻¹ := by group
        _ = y' * (a * b * a⁻¹ * b⁻¹) * y'⁻¹ := by rw [this]; group
    _ = a * b * a⁻¹ * b⁻¹ := by rw [h2.eq]; group

end Generic

section Config

variable {G : Type} [Group G] [Finite G] {S : Sylow 2 G} {U M V : Subgroup G} {x z : G}
  {A B R : Subgroup G}

theorem nonempty_mulEquiv_W (hc : Ctx19 S U M V x z A B R)
    (hTM' : ∀ m ∈ M, ∀ t ∈ Tsub S U, m * t * m⁻¹ ∈ Tsub S U)
    (hCT : ∀ m ∈ M, (∀ t ∈ Tsub S U, m * t = t * m) → m ∈ Tsub S U) {a w : G} (ha : a ∈ A)
    (haU : a ∉ U) (hwM : w ∈ M) (hwa : w * a = a * w) (hw : orderOf w = 3) :
    Nonempty (↥(zpowers w ⊔ U) ≃* alternatingGroup (Fin 4)) := by
  classical
  have hw3 : w ^ 3 = 1 := by rw [← hw]; exact pow_orderOf_eq_one w
  have hwUnc := CM.w_not_cent_U hc hTM' hCT ha haU hwM hwa hw
  set W : Subgroup G := zpowers w ⊔ U with hWdef
  have hUW : U ≤ W := le_sup_right
  have hWN : W ≤ normalizer (U : Set G) :=
    sup_le (CM.zpowers_le_normalizer_U hc hTM' hwM) Subgroup.le_normalizer
  have hnorm : (U.subgroupOf W).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hUW).2 hWN
  have hcardW : Nat.card W = 12 := CM.card_W hc hTM' hwM hw
  have hcardU' : Nat.card ↥(U.subgroupOf W) = 4 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hUW).toEquiv]; exact Cfg.card_U hc
  have hKlein : IsKleinFour ↥(U.subgroupOf W) := by
    refine isKleinFour_of_card_four_sq_one _ hcardU' ?_
    rintro ⟨k, hk⟩ hkU
    exact Subtype.ext (Cfg.U_sq hc k hkU)
  have hindex : (U.subgroupOf W).index = 3 := by
    have h := (U.subgroupOf W).card_mul_index
    rw [hcardU', hcardW] at h
    omega
  have hcent : centralizer ((U.subgroupOf W : Subgroup ↥W) : Set ↥W) = U.subgroupOf W := by
    apply le_antisymm
    · intro g hg
      obtain ⟨g, hgW⟩ := g
      obtain ⟨p, hp, q, hq, hpq⟩ := (CM.mem_W_iff hc hTM' hwM).1 hgW
      have hpU : ∀ u ∈ U, p * u = u * p := by
        intro u hu
        have hcomm := mem_centralizer_iff.1 hg ⟨u, hUW hu⟩
          (show (⟨u, hUW hu⟩ : ↥W) ∈ U.subgroupOf W from hu)
        have h1 : u * g = g * u := congrArg Subtype.val hcomm
        rw [← hpq] at h1
        have hqu : q * u = u * q := Cfg.U_comm hc q hq u hu
        have h2 : u * p * q = p * u * q := by
          calc u * p * q = u * (p * q) := by group
            _ = p * q * u := h1
            _ = p * (q * u) := by group
            _ = p * (u * q) := by rw [hqu]
            _ = p * u * q := by group
        exact (mul_right_cancel h2).symm
      by_cases hp1 : p = 1
      · rw [hp1, one_mul] at hpq
        show g ∈ U
        rw [← hpq]; exact hq
      · exact absurd (fun u hu => cent_of_mem_zpowers hw3 hp hp1 (hpU u hu)) hwUnc
    · intro g hg
      rw [mem_centralizer_iff]
      intro h hh
      exact Subtype.ext (Cfg.U_comm hc h (Subgroup.mem_subgroupOf.1 hh) g
        (Subgroup.mem_subgroupOf.1 hg))
  exact GorensteinWalter.mulEquiv_alternatingGroup_four_of_normal_kleinFour_index_three
    (U.subgroupOf W) hnorm hKlein hcent hindex

theorem nonempty_mulEquiv_A1 (hc : Ctx19 S U M V x z A B R)
    (hTM' : ∀ m ∈ M, ∀ t ∈ Tsub S U, m * t * m⁻¹ ∈ Tsub S U)
    (hCT : ∀ m ∈ M, (∀ t ∈ Tsub S U, m * t = t * m) → m ∈ Tsub S U) {a w : G} (ha : a ∈ A)
    (haU : a ∉ U) (hwM : w ∈ M) (hwa : w * a = a * w) (hw : orderOf w = 3) :
    Nonempty (↥(A ⊓ centralizer ({w} : Set G)) ≃*
      Multiplicative (ZMod 2) × Multiplicative (ZMod 2)) :=
  nonempty_mulEquiv_klein _ (CM.card_A1 hc hTM' hCT ha haU hwM hwa hw)
    (fun k hk => Cfg.A_sq hc k hk.1)

theorem nonempty_mulEquiv_cent (hc : Ctx19 S U M V x z A B R)
    (hTM' : ∀ m ∈ M, ∀ t ∈ Tsub S U, m * t * m⁻¹ ∈ Tsub S U)
    (hCT : ∀ m ∈ M, (∀ t ∈ Tsub S U, m * t = t * m) → m ∈ Tsub S U) {a w : G} (ha : a ∈ A)
    (haU : a ∉ U) (hwM : w ∈ M) (hwa : w * a = a * w) (hw : orderOf w = 3)
    (hce : centralizer ({a} : Set G) = (A ⊓ centralizer ({w} : Set G)) ⊔ (zpowers w ⊔ U)) :
    Nonempty (↥(centralizer ({a} : Set G)) ≃*
      alternatingGroup (Fin 4) × (Multiplicative (ZMod 2) × Multiplicative (ZMod 2))) := by
  obtain ⟨eW⟩ := nonempty_mulEquiv_W hc hTM' hCT ha haU hwM hwa hw
  obtain ⟨eA⟩ := nonempty_mulEquiv_A1 hc hTM' hCT ha haU hwM hwa hw
  obtain ⟨ep⟩ := Gen.nonempty_mulEquiv_prod (CM.A1_comm_W hc (w := w))
    (CM.A1_inf_W hc hTM' hCT ha haU hwM hwa hw)
  exact ⟨(MulEquiv.subgroupCongr hce).trans (ep.trans ((MulEquiv.prodCongr eA eW).trans
    MulEquiv.prodComm))⟩

theorem comm_mem_U_of_W (hc : Ctx19 S U M V x z A B R)
    (hTM' : ∀ m ∈ M, ∀ t ∈ Tsub S U, m * t * m⁻¹ ∈ Tsub S U) {w : G} (hwM : w ∈ M)
    {ω ω' : G} (hω : ω ∈ zpowers w ⊔ U) (hω' : ω' ∈ zpowers w ⊔ U) :
    ω * ω' * ω⁻¹ * ω'⁻¹ ∈ U := by
  obtain ⟨p, hp, q, hq, rfl⟩ := (CM.mem_W_iff hc hTM' hwM).1 hω
  obtain ⟨p', hp', q', hq', rfl⟩ := (CM.mem_W_iff hc hTM' hwM).1 hω'
  have hnU : ∀ g ∈ zpowers w, ∀ u ∈ U, g * u * g⁻¹ ∈ U := fun g hg u hu =>
    (mem_normalizer_iff.1 (CM.zpowers_le_normalizer_U hc hTM' hwM hg) u).1 hu
  have hnU' : ∀ g ∈ zpowers w, ∀ u ∈ U, g⁻¹ * u * g ∈ U := fun g hg u hu => by
    have := hnU g⁻¹ ((zpowers w).inv_mem hg) u hu
    simpa using this
  obtain ⟨i, rfl⟩ := mem_zpowers_iff.1 hp
  obtain ⟨j, rfl⟩ := mem_zpowers_iff.1 hp'
  refine commutator_pq_mem ?_ (hnU _ hp) (hnU _ hp') (hnU' _ hp) (hnU' _ hp') hq hq'
  rw [← zpow_add, ← zpow_add, add_comm]

theorem commutator_cent_eq (hc : Ctx19 S U M V x z A B R)
    (hTM' : ∀ m ∈ M, ∀ t ∈ Tsub S U, m * t * m⁻¹ ∈ Tsub S U)
    (hCT : ∀ m ∈ M, (∀ t ∈ Tsub S U, m * t = t * m) → m ∈ Tsub S U) {a w : G} (ha : a ∈ A)
    (haU : a ∉ U) (hwM : w ∈ M) (hwa : w * a = a * w) (hw : orderOf w = 3)
    (hce : centralizer ({a} : Set G) = (A ⊓ centralizer ({w} : Set G)) ⊔ (zpowers w ⊔ U)) :
    (commutator ↥(centralizer ({a} : Set G))).map (centralizer ({a} : Set G)).subtype = U := by
  set K : Subgroup G := centralizer ({a} : Set G) with hK
  have hUK : U ≤ K := fun u hu =>
    mem_centralizer_singleton_iff.2 (Cfg.A_comm hc u (Cfg.U_le_A hc hu) a ha)
  apply le_antisymm
  · rw [Subgroup.map_le_iff_le_comap, _root_.commutator_def, Subgroup.commutator_le]
    intro g₁ _ g₂ _
    rw [Subgroup.mem_comap]
    show (g₁ : G) * g₂ * (g₁ : G)⁻¹ * (g₂ : G)⁻¹ ∈ U
    have hg₁ : (g₁ : G) ∈ (A ⊓ centralizer ({w} : Set G)) ⊔ (zpowers w ⊔ U) := by
      rw [← hce]; exact g₁.2
    have hg₂ : (g₂ : G) ∈ (A ⊓ centralizer ({w} : Set G)) ⊔ (zpowers w ⊔ U) := by
      rw [← hce]; exact g₂.2
    obtain ⟨y₁, hy₁, ω₁, hω₁, h₁⟩ := SU5.mem_sup_of_commute (CM.A1_comm_W hc) hg₁
    obtain ⟨y₂, hy₂, ω₂, hω₂, h₂⟩ := SU5.mem_sup_of_commute (CM.A1_comm_W hc) hg₂
    rw [← h₁, ← h₂]
    rw [commutator_mul_central (CM.A1_comm_W hc y₁ hy₁ ω₁ hω₁) (CM.A1_comm_W hc y₁ hy₁ ω₂ hω₂)
      (CM.A1_comm_W hc y₂ hy₂ ω₁ hω₁) (CM.A1_comm_W hc y₂ hy₂ ω₂ hω₂)
      (Cfg.A_comm hc y₁ hy₁.1 y₂ hy₂.1)]
    exact comm_mem_U_of_W hc hTM' hwM hω₁ hω₂
  · intro v hv
    have hwU : ∀ u ∈ U, w * u * w⁻¹ ∈ U := Cfg.U_normal_M hc hTM' w hwM
    obtain ⟨u, hu, huv⟩ := exists_comm_eq_of_fpf (Cfg.U_comm hc) hwU
      (CM.w_fpf_U hc hTM' hCT ha haU hwM hwa hw) v hv
    have hwK : w ∈ K := mem_centralizer_singleton_iff.2 hwa
    have hmem : ⁅(⟨w, hwK⟩ : ↥K), ⟨u, hUK hu⟩⁆ ∈ commutator ↥K := by
      rw [_root_.commutator_def]
      exact Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _)
    exact ⟨⁅(⟨w, hwK⟩ : ↥K), ⟨u, hUK hu⟩⁆, hmem, huv⟩

end Config

end L196c

end CFSG.GH74.Uniqueness.SU.SU7
