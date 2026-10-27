module

public import CFSG.HardMathSupport.Cooperstein.Coordinator.EightFive.Twist
import CFSG.Quasithin.Background.C124BlkQuot
import CFSG.HardMathSupport.Cooperstein.Coordinator.EightFive.HeartFix
public import CFSG.HardMathSupport.Cooperstein.Coordinator.EightFive.Base7Ctx
public import CFSG.Quasithin.Background.B4Statement
public import CFSG.Sporadic.Schreier.J4SSylowBase

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.HardMathSupport.Cooperstein.Coordinator.EightFive

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.RankThree.PartTwo Equiv Equiv.Perm

theorem eq_one_of_permAct_fix {n : ℕ} (hn : 5 ≤ n) {γ : Perm (Fin n)}
    (h : ∀ m ∈ G6.coreMod n, G6.permAct n γ m = m) : γ = 1 := by
  classical
  refine Equiv.ext fun i => ?_
  obtain ⟨j, hji, -, -, -⟩ := AlternatingGeometry.exists_ne_four hn i i i i
  obtain ⟨k, hki, hkj, -, -⟩ := AlternatingGeometry.exists_ne_four hn i j j j
  have key : ∀ j : Fin n, j ≠ i → γ i = i ∨ γ i = j := by
    intro j hji
    set m : G6.PermMod n := Multiplicative.ofAdd (Pi.single i 1 + Pi.single j 1) with hm
    have hmc : m ∈ G6.coreMod n := by
      rw [G6.mem_coreMod, hm, toAdd_ofAdd]
      simp only [Pi.add_apply, Finset.sum_add_distrib, Finset.sum_pi_single']
      simp only [Finset.mem_univ, ite_true]
      decide
    have h1 := congrArg (fun x : G6.PermMod n => Multiplicative.toAdd x (γ i)) (h m hmc)
    simp only [G6.permAct_apply, perm_inv_apply_apply, hm, toAdd_ofAdd, Pi.add_apply] at h1
    by_contra hne
    push Not at hne
    rw [Pi.single_eq_same, Pi.single_eq_of_ne (Ne.symm hji), Pi.single_eq_of_ne hne.1,
      Pi.single_eq_of_ne hne.2] at h1
    exact absurd h1 (by decide)
  rcases key j hji with h1 | h1
  · exact h1
  rcases key k hki with h2 | h2
  · exact h2
  · exact absurd (h1.symm.trans h2) (Ne.symm hkj)

theorem zpowers_allOnes_inf_coreMod_seven :
    Subgroup.zpowers (G6.allOnes 7) ⊓ G6.coreMod 7 = ⊥ := by
  rw [eq_bot_iff]
  rintro m ⟨hm1, hm2⟩
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hm1
  have hm2' : G6.allOnes 7 ^ k ∈ G6.coreMod 7 := hm2
  rw [G6.mem_coreMod] at hm2'
  have hc : ∀ i, Multiplicative.toAdd (G6.allOnes 7 ^ k) i = (k : ZMod 2) := fun i => by
    rw [toAdd_zpow, G6.allOnes, toAdd_ofAdd, Pi.smul_apply, zsmul_eq_mul, mul_one]
  simp only [hc, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hm2'
  have hk : (k : ZMod 2) = 0 := by
    have h7 : ((7 : ℕ) : ZMod 2) = 1 := by decide
    rwa [h7, one_mul] at hm2'
  rw [Subgroup.mem_bot]
  apply Multiplicative.toAdd.injective
  funext i
  rw [hc, hk]
  rfl

theorem evenWeightOnes_seven : evenWeightOnes 7 = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  obtain ⟨c, hc⟩ := exists_forall_eq_of_mem_evenWeightOnes hx
  have hsum := sum_evenWeight x
  simp only [hc, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hsum
  have h7 : ((7 : ℕ) : ZMod 2) = 1 := by decide
  rw [h7, one_mul] at hsum
  rw [AddSubgroup.mem_bot]
  exact Subtype.ext (funext fun i => by rw [hc, hsum]; rfl)

variable {V : Type} [CommGroup V] [Finite V] {H : Subgroup (MulAut V)}

theorem isAltNaturalSection_of_case5 {ψ : ↥H →* Perm (Fin 7)} (hψ : Function.Injective ψ)
    (hA : alternatingGroup (Fin 7) ≤ ψ.range) {U : Subgroup V}
    (hH₀ : H ≤ stabSub (U ⊓ fixV (altPre ψ))) (hH₁ : H ≤ stabSub U)
    (hUL : ¬ IsCentralSec (altPre ψ) (U ⊓ fixV (altPre ψ)) U)
    {A₀ : Subgroup (MulAut (Sec U (U ⊓ fixV (altPre ψ))))}
    (hA₀ : IsFFStarOffender (autSec H U (U ⊓ fixV (altPre ψ))) A₀)
    (h5 : B42Case5 (autSec H U (U ⊓ fixV (altPre ψ))) A₀) :
    IsAltNaturalSection (altPre ψ) U 7 := by
  classical
  set L := altPre ψ with hLdef
  set Z := U ⊓ fixV L with hZ
  have C := ctx_autSec (Or.inr rfl) hψ hA hH₀ hH₁ hUL
  have hLJ : autSec L U Z ≤ ffJ (autSec H U Z) := C.le_ffJ hA₀
  have hcardL : Nat.card (autSec L U Z) = 2520 := by
    rw [C.card_eq, Bridge.card_alt_seven]
  obtain ⟨⟨n', hn', π, hR, -⟩, -⟩ := h5
  rcases hn' with rfl | rfl
  · exfalso
    obtain ⟨hπs, -⟩ := hR
    have h1 : Nat.card (ffJ (autSec H U Z)) ≤ Nat.card (Perm (Fin 5)) :=
      Nat.card_le_card_of_surjective π hπs
    have h2 := Subgroup.card_le_of_le hLJ
    rw [Nat.card_perm, Nat.card_fin] at h1
    have h3 : Nat.factorial 5 = 120 := rfl
    omega
  obtain ⟨hπs, -, -, -, -, -, -, β, hβs, hβ1, hβeq⟩ := hR
  let K7 : Subgroup ↥(G6.coreMod 7) :=
    (Subgroup.zpowers (G6.allOnes 7) ⊓ G6.coreMod 7).subgroupOf (G6.coreMod 7)
  let β' : Sec U Z →* ↥(G6.coreMod 7) ⧸ K7 := β.comp Subgroup.topEquiv.symm.toMonoidHom
  have hβ'1 : ∀ x, β' x = 1 → x = 1 := fun x hx =>
    Subgroup.mem_bot.1 ((hβ1 ⟨x, Subgroup.mem_top x⟩).1 hx)
  have hβ's : Function.Surjective β' := fun q => by
    obtain ⟨⟨x, hx⟩, hq⟩ := hβs q
    exact ⟨x, hq⟩
  have hβ'eq : ∀ (γ : Perm (Fin 7)) (x : Sec U Z) (m : ↥(G6.coreMod 7)),
      β' x = QuotientGroup.mk m → β' ((π γ : MulAut (Sec U Z)) x) =
        QuotientGroup.mk ⟨G6.permAct 7 γ m, G6.permAct_mem_coreMod γ m.2⟩ :=
    fun γ x m hm => hβeq γ ⟨x, Subgroup.mem_top x⟩ m (Subgroup.mem_top _)
      (G6.permAct_mem_coreMod γ m.2) hm
  let e₁ : (↥(G6.coreMod 7) ⧸ K7) ≃* ↥(G6.coreMod 7) :=
    C124.quotBotEquiv (G6.coreMod 7) (Subgroup.zpowers (G6.allOnes 7) ⊓ G6.coreMod 7)
      zpowers_allOnes_inf_coreMod_seven
  let e₂ := C124.coreEvenEquiv 7
  let mkH : Multiplicative ↥(evenWeight 7) →* Multiplicative (altHeart 7) :=
    AddMonoidHom.toMultiplicative (QuotientAddGroup.mk' (evenWeightOnes 7))
  have hmkH : Function.Injective mkH := by
    intro a b hab
    have h1 : (QuotientAddGroup.mk (Multiplicative.toAdd a) : altHeart 7) =
        QuotientAddGroup.mk (Multiplicative.toAdd b) := congrArg Multiplicative.toAdd hab
    rw [QuotientAddGroup.eq, evenWeightOnes_seven, AddSubgroup.mem_bot, neg_add_eq_zero] at h1
    exact Multiplicative.toAdd.injective h1
  let Φ : Sec U Z →* Multiplicative (altHeart 7) :=
    mkH.comp (e₂.toMonoidHom.comp (e₁.toMonoidHom.comp β'))
  have hΦ : ∀ x, Multiplicative.toAdd (Φ x) =
      (QuotientAddGroup.mk (Multiplicative.toAdd (e₂ (e₁ (β' x)))) : altHeart 7) := fun _ => rfl
  have hΦinj : Function.Injective Φ := by
    refine hmkH.comp (e₂.injective.comp (e₁.injective.comp ?_))
    rw [injective_iff_map_eq_one]
    exact hβ'1
  have hΦsurj : Function.Surjective Φ := by
    intro y
    obtain ⟨w, hw⟩ := QuotientAddGroup.mk_surjective (Multiplicative.toAdd y)
    obtain ⟨m, hm⟩ := e₂.surjective (Multiplicative.ofAdd w)
    obtain ⟨x, hx⟩ := hβ's (QuotientGroup.mk m)
    refine ⟨x, Multiplicative.toAdd.injective ?_⟩
    rw [hΦ, hx, C124.quotBotEquiv_mk, hm, toAdd_ofAdd, hw]
  have hΦeq : ∀ (γ : Perm (Fin 7)) (x : Sec U Z),
      Multiplicative.toAdd (Φ ((π γ : MulAut (Sec U Z)) x)) =
        altAct γ (Multiplicative.toAdd (Φ x)) := by
    intro γ x
    obtain ⟨m, hm⟩ := QuotientGroup.mk_surjective (β' x)
    have h1 := hβ'eq γ x m hm.symm
    rw [hΦ, hΦ, h1, ← hm, C124.quotBotEquiv_mk, C124.quotBotEquiv_mk, altAct_mk]
    congr 1
  have hπinj : Function.Injective π := by
    rw [injective_iff_map_eq_one]
    intro γ hγ
    refine eq_one_of_permAct_fix (by norm_num) fun m hm => ?_
    obtain ⟨x, hx⟩ := hΦsurj (mkH (e₂ ⟨m, hm⟩))
    have h1 := hΦeq γ x
    rw [hγ] at h1
    change Multiplicative.toAdd (Φ x) = altAct γ (Multiplicative.toAdd (Φ x)) at h1
    rw [hx] at h1
    change (QuotientAddGroup.mk (Multiplicative.toAdd (e₂ ⟨m, hm⟩)) : altHeart 7) =
      altAct γ (QuotientAddGroup.mk (Multiplicative.toAdd (e₂ ⟨m, hm⟩))) at h1
    rw [altAct_mk, QuotientAddGroup.eq, evenWeightOnes_seven, AddSubgroup.mem_bot,
      neg_add_eq_zero] at h1
    apply Multiplicative.toAdd.injective
    funext i
    have h2 := congrArg (fun w : ↥(evenWeight 7) => (w : Fin 7 → ZMod 2) i) h1
    exact h2.symm
  let πe : Perm (Fin 7) ≃* ↥(ffJ (autSec H U Z)) := MulEquiv.ofBijective π ⟨hπinj, hπs⟩
  have hL₀ : L ≤ stabSub Z := altPre_le.trans hH₀
  have hL₁ : L ≤ stabSub U := altPre_le.trans hH₁
  let σL : ↥L →* ↥(ffJ (autSec H U Z)) := (secHom hL₀ hL₁).codRestrict _ fun l =>
    hLJ ((range_secHom hL₀ hL₁) ▸ ⟨l, rfl⟩)
  have hσLinj : Function.Injective σL := by
    have hfaith : L ⊓ centSec U Z = ⊥ := by
      rw [eq_bot_iff, ← inf_centSec_eq_bot (by norm_num) hψ hA hH₀ hH₁ hUL]
      exact inf_le_inf_right _ altPre_le
    intro a b hab
    exact secHom_injective hL₀ hL₁ hfaith (congrArg Subtype.val hab)
  let α₀ : ↥L →* Perm (Fin 7) := πe.symm.toMonoidHom.comp σL
  have hπα : ∀ l : ↥L, ((π (α₀ l) : ↥(ffJ (autSec H U Z))) : MulAut (Sec U Z)) =
      secHom hL₀ hL₁ l := fun l => congrArg Subtype.val (πe.apply_symm_apply (σL l))
  have hα₀A : ∀ l : ↥L, α₀ l ∈ alternatingGroup (Fin 7) := by
    intro l
    have hperf := commutator_altPre_eq_top (by norm_num) hψ hA
    have h1 : l ∈ (Perm.sign.comp α₀).ker :=
      Abelianization.commutator_subset_ker _ (hperf ▸ Subgroup.mem_top l)
    exact Perm.mem_alternatingGroup.2 (MonoidHom.mem_ker.1 h1)
  let α : ↥L →* alternatingGroup (Fin 7) := α₀.codRestrict _ hα₀A
  have hαinj : Function.Injective α := fun a b hab =>
    hσLinj (πe.symm.injective (congrArg Subtype.val hab))
  have hαsurj : Function.Surjective α := by
    refine (hαinj.bijective_of_nat_card_le ?_).2
    rw [Nat.card_congr (altPreEquiv hψ hA).toEquiv]
  let π' : ↥U →* Multiplicative (altHeart 7) := Φ.comp (QuotientGroup.mk' (Z.subgroupOf U))
  refine isAltNaturalSection_iff_natThrough.2 ⟨α, hαsurj, π', ?_, ?_, fun l u v huv => ?_⟩
  · exact hΦsurj.comp (QuotientGroup.mk'_surjective _)
  · ext u
    rw [MonoidHom.mem_ker]
    change Φ (QuotientGroup.mk u) = 1 ↔ u ∈ Z.subgroupOf U
    rw [← map_one Φ, hΦinj.eq_iff, QuotientGroup.eq_one_iff]
  · change Multiplicative.toAdd (Φ (QuotientGroup.mk v)) =
      altAct (α₀ l) (Multiplicative.toAdd (Φ (QuotientGroup.mk u)))
    have hv : (QuotientGroup.mk v : Sec U Z) = secHom hL₀ hL₁ l (QuotientGroup.mk u) := by
      rw [secHom_mk]
      congr 1
      exact Subtype.ext huv
    rw [hv, ← hπα]
    exact hΦeq _ _

end CFSG.HardMathSupport.Cooperstein.Coordinator.EightFive
