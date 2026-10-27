module

public import CFSG.Goldschmidt75.Sig3Bal
public import CFSG.SignalizerFunctorTheorem.Solvable.SmallPrimes

public section

namespace CFSG.Goldschmidt75

open CFSG.Open CFSG.Goldschmidt Subgroup

variable {G : Type} [Group G]

@[expose] def wE (V₁ V₂ : Subgroup G) : Subgroup G :=
  ⨆ (a : G) (_ : a ∈ V₁ ⊔ V₂) (_ : a ≠ 1), theta V₁ V₂ a

theorem theta_comm (V₁ V₂ : Subgroup G) (t : G) : theta V₂ V₁ t = theta V₁ V₂ t :=
  inf_comm _ _

theorem wE_comm (V₁ V₂ : Subgroup G) : wE V₂ V₁ = wE V₁ V₂ := by
  unfold wE
  rw [sup_comm V₂ V₁]
  exact iSup_congr fun a => iSup_congr fun _ => iSup_congr fun _ => theta_comm V₁ V₂ a

variable [Finite G] {S₁ S₂ V₁ V₂ : Subgroup G}

theorem isSolvableSignalizerFunctor_theta (hp : FourPair S₁ S₂ V₁ V₂) (hsep : CoreSep S₁ S₂) :
    IsSolvableSignalizerFunctor 2 (V₁ ⊔ V₂) (theta V₁ V₂) := by
  have hO : ∀ a ∈ V₁ ⊔ V₂, theta V₁ V₂ a ≤ oddCent a := fun a ha =>
    theta_le_oddCent (le_sup_left.trans (hp.le_centralizer_of_mem ha))
  have hodd : ∀ a ∈ V₁ ⊔ V₂, Odd (Nat.card (theta V₁ V₂ a)) := fun a ha =>
    Odd.of_dvd_nat (Balance.odd_card_oddCoreOf _) (card_dvd_of_le (hO a ha))
  exact
    { le_centralizer := fun a ha _ => (hO a ha).trans (oddCent_le_centralizer a)
      coprime := fun a ha _ => Nat.coprime_two_left.mpr (hodd a ha)
      invariant := fun a ha _ x hx =>
        mem_normalizer_iff_map_conj_eq.mp (hp.le_normalizer_theta ha hx)
      balance := fun a ha ha1 b hb hb1 => theta_inf_le hp hsep ha ha1 hb hb1
      solvable := fun a ha _ => CFSG.FeitThompson.isSolvable_of_odd_natCard _ (hodd a ha) }

theorem wE_spec (hp : FourPair S₁ S₂ V₁ V₂) (hsep : CoreSep S₁ S₂) :
    Odd (Nat.card (wE V₁ V₂)) ∧
      ∀ a ∈ V₁ ⊔ V₂, a ≠ 1 → theta V₁ V₂ a = wE V₁ V₂ ⊓ centralizer ({a} : Set G) := by
  have h := CFSG.SignalizerFunctorTheorem.Solvable.glauberman_of_le_three G 2 Nat.prime_two
    (by norm_num) (V₁ ⊔ V₂) hp.isElemAbelian.1 hp.isElemAbelian.2
    (by rw [hp.card_sup]; norm_num) (theta V₁ V₂) (isSolvableSignalizerFunctor_theta hp hsep)
  exact ⟨Nat.coprime_two_left.mp h.1, h.2.2⟩

omit [Finite G] in
theorem le_normalizer_wE (hp : FourPair S₁ S₂ V₁ V₂) :
    V₁ ⊔ V₂ ≤ normalizer ((wE V₁ V₂ : Subgroup G) : Set G) := by
  intro g hg
  rw [mem_normalizer_iff_map_conj_eq]
  unfold wE
  simp only [Subgroup.map_iSup]
  exact iSup_congr fun a => iSup_congr fun ha => iSup_congr fun _ =>
    mem_normalizer_iff_map_conj_eq.mp (hp.le_normalizer_theta ha hg)

theorem wE_mem_NSet (hp : FourPair S₁ S₂ V₁ V₂) (hsep : CoreSep S₁ S₂) {B : Subgroup G}
    (hB : B ≤ V₁ ⊔ V₂) : wE V₁ V₂ ∈ NSet B := by
  obtain ⟨hodd, hθ⟩ := wE_spec hp hsep
  refine ⟨hB.trans (le_normalizer_wE hp), hodd, fun t ht ht2 => ?_⟩
  have ht1 : t ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at ht2
    exact absurd ht2 (by norm_num)
  rw [← hθ t (hB ht) ht1]
  exact theta_le_oddCent (le_sup_left.trans (hp.le_centralizer_of_mem (hB ht)))

omit [Finite G] in
theorem NSet_anti {B B' : Subgroup G} (h : B' ≤ B) {X : Subgroup G} (hX : X ∈ NSet B) :
    X ∈ NSet B' :=
  ⟨h.trans hX.1, hX.2.1, fun t ht ht2 => hX.2.2 t (h ht) ht2⟩

theorem inf_centralizer_le_thetaOne {V B X : Subgroup G} {b c : G} (hV : IsPGroup 2 V)
    (hVb : V ≤ centralizer ({b} : Set G)) (hVc : V ≤ centralizer ({c} : Set G)) (hcV : c ∈ V)
    (hc2 : orderOf c = 2) (hcB : c ∈ B) (hb2 : orderOf b = 2) (hbB : b ∈ B)
    (hcb : c * b = b * c) (hX : X ∈ NSet B) :
    X ⊓ centralizer ({b} : Set G) ≤ thetaOne V b := by
  obtain ⟨hXN, hXodd, hXC⟩ := hX
  have hYO : X ⊓ centralizer ({b} : Set G) ≤ oddCent b := hXC b hbB hb2
  have hYodd : Odd (Nat.card (X ⊓ centralizer ({b} : Set G) : Subgroup G)) :=
    Odd.of_dvd_nat hXodd (card_dvd_of_le inf_le_left)
  have hcN : zpowers c ≤ normalizer ((X ⊓ centralizer ({b} : Set G) : Subgroup G) : Set G) := by
    rw [zpowers_le]
    exact mem_normalizer_inf (hXN hcB) (le_normalizer (mem_centralizer_singleton_iff.mpr hcb))
  have hfac := le_commutator_sup_inf (isPGroup_zpowers hc2) hcN hYodd
  refine hfac.trans (sup_le ((commutator_mono hYO (zpowers_le.mpr hcV)).trans le_sup_left) ?_)
  have hZ : X ⊓ centralizer ({b} : Set G) ⊓ centralizer ((zpowers c : Subgroup G) : Set G) ≤
      oddCent c ⊓ oddCent b := by
    rw [centralizer_zpowers_eq]
    refine le_inf ?_ (inf_le_left.trans hYO)
    exact (inf_le_inf_right _ inf_le_left).trans (hXC c hcB hc2)
  refine hZ.trans ?_
  have hZN : V ≤ normalizer ((oddCent c ⊓ oddCent b : Subgroup G) : Set G) :=
    le_normalizer_inf_of_le (hVc.trans (centralizer_le_normalizer_oddCent c))
      (hVb.trans (centralizer_le_normalizer_oddCent b))
  have hZodd : Odd (Nat.card (oddCent c ⊓ oddCent b : Subgroup G)) :=
    Odd.of_dvd_nat (Balance.odd_card_oddCoreOf _) (card_dvd_of_le inf_le_right)
  refine (le_commutator_sup_inf hV hZN hZodd).trans (sup_le_sup
    (commutator_mono inf_le_right le_rfl) (le_inf ?_ (inf_le_left.trans inf_le_right)))
  exact (inf_le_inf_right _ inf_le_left).trans (oddCent_inf_le_oddCentSub hcV)

theorem le_wE_of_mem_NSet (hp : FourPair S₁ S₂ V₁ V₂) (hsep : CoreSep S₁ S₂) {b₁ b₂ : G}
    (hb₁ : b₁ ∈ V₁) (hb₁1 : b₁ ≠ 1) (hb₂ : b₂ ∈ V₂) (hb₂1 : b₂ ≠ 1) {X : Subgroup G}
    (hX : X ∈ NSet (zpowers b₁ ⊔ zpowers b₂)) : X ≤ wE V₁ V₂ := by
  obtain ⟨-, hθ⟩ := wE_spec hp hsep
  have hB₀E : zpowers b₁ ⊔ zpowers b₂ ≤ V₁ ⊔ V₂ :=
    sup_le_sup (zpowers_le.mpr hb₁) (zpowers_le.mpr hb₂)
  have hb₁E : b₁ ∈ V₁ ⊔ V₂ := mem_sup_left hb₁
  have hb₂E : b₂ ∈ V₁ ⊔ V₂ := mem_sup_right hb₂
  have hord₁ : orderOf b₁ = 2 := hp.orderOf_eq_two hb₁E hb₁1
  have hord₂ : orderOf b₂ = 2 := hp.orderOf_eq_two hb₂E hb₂1
  have hB₀el : IsElemAbelian 2 (zpowers b₁ ⊔ zpowers b₂ : Subgroup G) :=
    ⟨isMulCommutative_iff.mpr fun a b => Subtype.ext (hp.commute_mem (hB₀E a.2) (hB₀E b.2)),
      fun x hx => by rw [pow_two]; exact hp.mul_self_mem (hB₀E hx)⟩
  have hB₀card : 2 ^ (1 + 1) ≤ Nat.card (zpowers b₁ ⊔ zpowers b₂ : Subgroup G) := by
    have hn : zpowers b₂ ≤ normalizer ((zpowers b₁ : Subgroup G) : Set G) :=
      (zpowers_le.mpr hb₂).trans ((le_centralizer_iff.mp hp.comm).trans
        ((centralizer_le (SetLike.coe_subset_coe.mpr (zpowers_le.mpr hb₁))).trans
          (centralizer_le_normalizer _)))
    have hd : Disjoint (zpowers b₁) (zpowers b₂) := disjoint_iff.mpr
      (le_bot_iff.mp (hp.disj ▸ inf_le_inf (zpowers_le.mpr hb₁) (zpowers_le.mpr hb₂)))
    rw [CFSG.GorensteinWalter.card_sup_eq_mul_of_disjoint_of_le_normalizer _ _ hn hd,
      Nat.card_zpowers, Nat.card_zpowers, hord₁, hord₂]
    norm_num
  have hgen := CFSG.SignalizerFunctor.Helpers.elementary_abelian_centralizer_generation 2 1
    Nat.prime_two _ X hB₀el hB₀card hX.1 (Nat.coprime_two_left.mpr hX.2.1)
  rw [← hgen]
  refine iSup₂_le fun S hS => ?_
  obtain ⟨hSB, hScard⟩ := hS
  obtain ⟨b, hbS, hb1⟩ : ∃ b ∈ S, b ≠ 1 := by
    rcases S.bot_or_exists_ne_one with h | h
    · rw [h, Subgroup.card_bot] at hScard
      norm_num at hScard
    · exact h
  have hbE : b ∈ V₁ ⊔ V₂ := hB₀E (hSB hbS)
  have hbB : b ∈ zpowers b₁ ⊔ zpowers b₂ := hSB hbS
  have hb2 : orderOf b = 2 := hp.orderOf_eq_two hbE hb1
  refine (inf_le_inf_left _ (centralizer_le (Set.singleton_subset_iff.mpr hbS))).trans ?_
  refine (le_inf ?_ ?_ : X ⊓ centralizer ({b} : Set G) ≤ theta V₁ V₂ b).trans
    ((hθ b hbE hb1).le.trans inf_le_left)
  · exact inf_centralizer_le_thetaOne hp.isPGroup_left
      (le_sup_left.trans (hp.le_centralizer_of_mem hbE))
      (le_sup_left.trans (hp.le_centralizer_of_mem hb₁E)) hb₁ hord₁
      (mem_sup_left (mem_zpowers b₁)) hb2 hbB (hp.commute_mem hb₁E hbE) hX
  · exact inf_centralizer_le_thetaOne hp.isPGroup_right
      (le_sup_right.trans (hp.le_centralizer_of_mem hbE))
      (le_sup_right.trans (hp.le_centralizer_of_mem hb₂E)) hb₂ hord₂
      (mem_sup_right (mem_zpowers b₂)) hb2 hbB (hp.commute_mem hb₂E hbE) hX

end CFSG.Goldschmidt75
