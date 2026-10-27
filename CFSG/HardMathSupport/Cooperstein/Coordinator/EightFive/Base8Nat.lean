module

public import CFSG.HardMathSupport.Cooperstein.Coordinator.EightFive.Base7Sec
public import CFSG.HardMathSupport.Cooperstein.Coordinator.EightFive.ModuleFaith
public import CFSG.HardMathSupport.Cooperstein.Coordinator.EightFive.NatFF
public import CFSG.Quasithin.Background.C124BlkQuot
import CFSG.ThirdParty.QiuzhenCFSG.Theory.AutAlternating

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.HardMathSupport.Cooperstein.Coordinator.EightFive

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.RankThree.PartTwo Equiv Equiv.Perm
open CFSG.HardMathSupport.Cooperstein.AlternatingGeometry

@[expose] def NatSec {V : Type} [CommGroup V] {H : Subgroup (MulAut V)} {n : ℕ}
    (ψ : ↥H →* Perm (Fin n)) (Y₀ Y₁ : Subgroup V) : Prop :=
  ∃ π : ↥Y₁ →* Multiplicative (altHeart n), Function.Surjective π ∧ π.ker = Y₀.subgroupOf Y₁ ∧
    ∀ (h : ↥H) (u v : ↥Y₁), (v : V) = (h : MulAut V) (u : V) →
      Multiplicative.toAdd (π v) = altAct (ψ h) (Multiplicative.toAdd (π u))

section Model

open CFSG.Quasithin.G6

@[expose] noncomputable def coreHeart (n : ℕ) : ↥(coreMod n) →* Multiplicative (altHeart n) :=
  (AddMonoidHom.toMultiplicative (QuotientAddGroup.mk' (evenWeightOnes n))).comp
    (C124.coreEvenEquiv n).toMonoidHom

theorem toAdd_coreHeart {n : ℕ} (m : ↥(coreMod n)) :
    Multiplicative.toAdd (coreHeart n m) =
      (QuotientAddGroup.mk (Multiplicative.toAdd (C124.coreEvenEquiv n m)) : altHeart n) :=
  rfl

theorem coreHeart_surjective (n : ℕ) : Function.Surjective (coreHeart n) := by
  intro y
  obtain ⟨w, hw⟩ := QuotientAddGroup.mk_surjective (Multiplicative.toAdd y)
  obtain ⟨m, hm⟩ := (C124.coreEvenEquiv n).surjective (Multiplicative.ofAdd w)
  refine ⟨m, Multiplicative.toAdd.injective ?_⟩
  rw [toAdd_coreHeart, hm, toAdd_ofAdd, hw]

theorem coreHeart_eq_one_iff {n : ℕ} (hn : 0 < n) (m : ↥(coreMod n)) :
    coreHeart n m = 1 ↔
      m ∈ (Subgroup.zpowers (G6.allOnes n) ⊓ coreMod n).subgroupOf (coreMod n) := by
  change _ ↔ m ∈ C124.altKer n
  rw [← C124.ker_altHeartHom n hn, MonoidHom.mem_ker, C124.altHeartHom_eq_one_iff,
    ← Multiplicative.toAdd.injective.eq_iff, toAdd_coreHeart, toAdd_one,
    QuotientAddGroup.eq_zero_iff]
  constructor
  · intro h i j
    obtain ⟨c, hc⟩ := exists_forall_eq_of_mem_evenWeightOnes h
    exact (hc i).trans (hc j).symm
  · intro h
    exact mem_evenWeightOnes_of_forall_eq fun i => h i ⟨0, hn⟩

theorem toAdd_coreHeart_permAct {n : ℕ} (γ : Perm (Fin n)) (m : ↥(coreMod n)) :
    Multiplicative.toAdd (coreHeart n ⟨permAct n γ m, permAct_mem_coreMod γ m.2⟩) =
      altAct γ (Multiplicative.toAdd (coreHeart n m)) := by
  rw [toAdd_coreHeart, toAdd_coreHeart, altAct_mk]
  rfl

end Model

section Schur

variable {V : Type} [CommGroup V] {H : Subgroup (MulAut V)} {n : ℕ} {ψ : ↥H →* Perm (Fin n)}

theorem natSec_of_altPre (hn : 5 ≤ n) (hA : alternatingGroup (Fin n) ≤ ψ.range)
    {Y₀ Y₁ : Subgroup V} (hH₀ : H ≤ stabSub Y₀) (hH₁ : H ≤ stabSub Y₁)
    {π : ↥Y₁ →* Multiplicative (altHeart n)} (hπ : Function.Surjective π)
    (hker : π.ker = Y₀.subgroupOf Y₁)
    (heq : ∀ (l : ↥(altPre ψ)) (u v : ↥Y₁), (v : V) = (l : MulAut V) (u : V) →
      Multiplicative.toAdd (π v) =
        altAct (ψ (Subgroup.inclusion altPre_le l)) (Multiplicative.toAdd (π u))) :
    NatSec ψ Y₀ Y₁ := by
  classical
  refine ⟨π, hπ, hker, fun h u v huv => ?_⟩
  have hker' : ∀ a : ↥Y₁, π a = 1 ↔ (a : V) ∈ Y₀ := fun a => by
    rw [← MonoidHom.mem_ker, hker, Subgroup.mem_subgroupOf]
  let hU : ∀ g : ↥H, ↥Y₁ → ↥Y₁ := fun g a => ⟨(g : MulAut V) a, (hH₁ g.2 a).2 a.2⟩
  have hU_mul : ∀ (g : ↥H) (a b : ↥Y₁), hU g (a * b) = hU g a * hU g b :=
    fun g a b => Subtype.ext (map_mul _ _ _)
  have hU_inv : ∀ (g : ↥H) (a : ↥Y₁), hU g a⁻¹ = (hU g a)⁻¹ :=
    fun g a => Subtype.ext (map_inv _ _)
  have hresp : ∀ a b : ↥Y₁, π a = π b → π (hU h a) = π (hU h b) := by
    intro a b hab
    have h1 : π (a * b⁻¹) = 1 := by rw [map_mul, map_inv, hab, mul_inv_cancel]
    have h2 : ((hU h (a * b⁻¹) : ↥Y₁) : V) ∈ Y₀ := (hH₀ h.2 _).2 ((hker' _).1 h1)
    have h3 : π (hU h a * (hU h b)⁻¹) = 1 := by
      rw [← hU_inv, ← hU_mul]
      exact (hker' _).2 h2
    rwa [map_mul, map_inv, mul_inv_eq_one] at h3
  choose s hs using fun y : altHeart n => hπ (Multiplicative.ofAdd y)
  let g : altHeart n →+ altHeart n :=
    { toFun := fun y => altAct (ψ h)⁻¹ (Multiplicative.toAdd (π (hU h (s y))))
      map_zero' := by
        have h1 : π (hU h (s 0)) = π (hU h 1) := hresp _ _ (by rw [hs, map_one]; rfl)
        have h2 : hU h 1 = 1 := Subtype.ext (map_one _)
        simp only [h1, h2, map_one, toAdd_one, map_zero]
      map_add' := fun y₁ y₂ => by
        have h1 : π (hU h (s (y₁ + y₂))) = π (hU h (s y₁ * s y₂)) :=
          hresp _ _ (by rw [hs, map_mul, hs, hs]; rfl)
        simp only [h1, hU_mul, map_mul, toAdd_mul, map_add] }
  have hg : ∀ a : ↥Y₁,
      g (Multiplicative.toAdd (π a)) = altAct (ψ h)⁻¹ (Multiplicative.toAdd (π (hU h a))) := by
    intro a
    change altAct (ψ h)⁻¹ (Multiplicative.toAdd (π (hU h (s _)))) = _
    rw [hresp _ a (by rw [hs]; rfl)]
  have hcomm : ∀ σ ∈ alternatingGroup (Fin n), ∀ y, g (altAct σ y) = altAct σ (g y) := by
    intro σ hσ y
    obtain ⟨l, hl⟩ := altPreHom_surjective hA ⟨σ, hσ⟩
    have hlσ : ψ (Subgroup.inclusion altPre_le l) = σ := by
      rw [← coe_altPreHom, hl]
    obtain ⟨a, rfl⟩ : ∃ a : ↥Y₁, Multiplicative.toAdd (π a) = y :=
      ⟨s y, by rw [hs]; rfl⟩
    let la : ↥Y₁ := hU (Subgroup.inclusion altPre_le l) a
    have h1 : altAct σ (Multiplicative.toAdd (π a)) = Multiplicative.toAdd (π la) := by
      rw [heq l a la rfl, hlσ]
    let l' : ↥(altPre ψ) := ⟨(h : MulAut V) * l * (h : MulAut V)⁻¹, conj_mem_altPre h.2 l.2⟩
    have h2 : Multiplicative.toAdd (π (hU h la)) =
        altAct (ψ (Subgroup.inclusion altPre_le l')) (Multiplicative.toAdd (π (hU h a))) := by
      refine heq l' (hU h a) (hU h la) ?_
      change (h : MulAut V) ((l : MulAut V) a) =
        ((h : MulAut V) * l * (h : MulAut V)⁻¹) ((h : MulAut V) a)
      simp only [MulAut.mul_apply, MulAut.inv_apply_self]
    have h3 : ψ (Subgroup.inclusion altPre_le l') = ψ h * σ * (ψ h)⁻¹ := by
      have : Subgroup.inclusion altPre_le l' = h * Subgroup.inclusion altPre_le l * h⁻¹ :=
        Subtype.ext rfl
      rw [this, map_mul, map_mul, map_inv, hlσ]
    rw [h1, hg, hg, h2, h3, ← altAct_mul, ← altAct_mul]
    congr 1
    group
  have := altHeart_nontrivial (n := n) (by omega)
  rcases altHeart_endo_eq_zero_or_id hn g hcomm with h0 | hid
  · exfalso
    have hall : ∀ a : ↥Y₁, π a = 1 := by
      intro a
      let b : ↥Y₁ := hU h⁻¹ a
      have hb : hU h b = a := Subtype.ext (by
        change (h : MulAut V) (((h⁻¹ : ↥H) : MulAut V) a) = a
        rw [Subgroup.coe_inv, MulAut.apply_inv_self])
      have h4 := hg b
      rw [h0, AddMonoidHom.zero_apply, hb] at h4
      have h5 := congrArg (altAct (ψ h)) h4
      rw [map_zero, altAct_apply_inv] at h5
      exact Multiplicative.toAdd.injective (h5.symm.trans toAdd_one.symm)
    obtain ⟨y, hy⟩ := exists_ne (0 : altHeart n)
    obtain ⟨a, ha⟩ := hπ (Multiplicative.ofAdd y)
    rw [hall a] at ha
    exact hy (congrArg Multiplicative.toAdd ha).symm
  · have h4 := hg u
    rw [hid, AddMonoidHom.id_apply] at h4
    have hv : v = hU h u := Subtype.ext huv
    rw [hv, h4, altAct_apply_inv]

end Schur

section Natural

variable {V : Type} [CommGroup V] {H : Subgroup (MulAut V)} {n : ℕ}
  {ψ : ↥H →* Perm (Fin n)}

theorem natSec_of_alternatingNatural (hn5 : 5 ≤ n) (hn6 : n ≠ 6) (hψ : Function.Injective ψ)
    (hA : alternatingGroup (Fin n) ≤ ψ.range) {Y₀ Y₁ : Subgroup V} (hH₀ : H ≤ stabSub Y₀)
    (hH₁ : H ≤ stabSub Y₁) (hL : ¬ IsCentralSec (altPre ψ) Y₀ Y₁)
    (h : AlternatingNatural (autSec (altPre ψ) Y₁ Y₀) ⊤ ⊥ n) : NatSec ψ Y₀ Y₁ := by
  classical
  set L := altPre ψ with hLdef
  have hL₀ : L ≤ stabSub Y₀ := altPre_le.trans hH₀
  have hL₁ : L ≤ stabSub Y₁ := altPre_le.trans hH₁
  obtain ⟨π, hπs, -, -, -, -, -, -, β, hβs, hβ1, hβeq⟩ := h
  set K : Subgroup ↥(G6.coreMod n) :=
    (Subgroup.zpowers (G6.allOnes n) ⊓ G6.coreMod n).subgroupOf (G6.coreMod n) with hK
  have hKle : ∀ m ∈ K, coreHeart n m = 1 := fun m hm =>
    (coreHeart_eq_one_iff (by omega) m).2 hm
  let Φ₀ : (↥(G6.coreMod n) ⧸ K) →* Multiplicative (altHeart n) :=
    QuotientGroup.lift K (coreHeart n) hKle
  have hΦ₀mk : ∀ m, Φ₀ (QuotientGroup.mk m) = coreHeart n m := fun m => rfl
  let β' : Sec Y₁ Y₀ →* ↥(G6.coreMod n) ⧸ K := β.comp Subgroup.topEquiv.symm.toMonoidHom
  let Φ : Sec Y₁ Y₀ →* Multiplicative (altHeart n) := Φ₀.comp β'
  have hΦ : ∀ x, Φ x = Φ₀ (β' x) := fun x => rfl
  have hΦinj : Function.Injective Φ := by
    rw [injective_iff_map_eq_one]
    intro x hx
    obtain ⟨m, hm⟩ := QuotientGroup.mk_surjective (β' x)
    have h1 : coreHeart n m = 1 := by rw [← hΦ₀mk, hm]; exact hx
    have h2 : β' x = 1 := by
      rw [← hm]
      exact (QuotientGroup.eq_one_iff m).2 ((coreHeart_eq_one_iff (by omega) m).1 h1)
    exact Subgroup.mem_bot.1 ((hβ1 ⟨x, Subgroup.mem_top x⟩).1 h2)
  have hΦsurj : Function.Surjective Φ := by
    intro y
    obtain ⟨m, hm⟩ := coreHeart_surjective n y
    obtain ⟨⟨x, hx⟩, hxm⟩ := hβs (QuotientGroup.mk m)
    refine ⟨x, ?_⟩
    rw [hΦ, ← hm, ← hΦ₀mk]
    exact congrArg Φ₀ hxm
  have hΦeq : ∀ (γ : alternatingGroup (Fin n)) (x : Sec Y₁ Y₀),
      Multiplicative.toAdd (Φ (((π γ : ↥(autSec L Y₁ Y₀)) : MulAut (Sec Y₁ Y₀)) x)) =
        altAct (γ : Perm (Fin n)) (Multiplicative.toAdd (Φ x)) := by
    intro γ x
    obtain ⟨m, hm⟩ := QuotientGroup.mk_surjective (β' x)
    have h1 := hβeq γ ⟨x, Subgroup.mem_top x⟩ m (Subgroup.mem_top _)
      (G6.permAct_mem_coreMod _ m.2) hm.symm
    have h2 : Φ (((π γ : ↥(autSec L Y₁ Y₀)) : MulAut (Sec Y₁ Y₀)) x) =
        coreHeart n ⟨G6.permAct n (γ : Perm (Fin n)) m, G6.permAct_mem_coreMod _ m.2⟩ :=
      congrArg Φ₀ h1
    have h3 : Φ x = coreHeart n m := by rw [hΦ, ← hm, hΦ₀mk]
    rw [h2, h3]
    exact toAdd_coreHeart_permAct (γ : Perm (Fin n)) m
  let πA : alternatingGroup (Fin n) →* ↥(autSec L Y₁ Y₀) := π
  have hπinj : Function.Injective πA := by
    rw [injective_iff_map_eq_one]
    intro γ hγ
    have hγ1 : π γ = 1 := hγ
    apply Subtype.ext
    refine perm_eq_one_of_altHeart_fixed hn5 _ fun w => ?_
    obtain ⟨x, hx⟩ := hΦsurj (Multiplicative.ofAdd (w : altHeart n))
    have h1 := hΦeq γ x
    rw [hγ1] at h1
    change Multiplicative.toAdd (Φ x) = altAct (γ : Perm (Fin n)) (Multiplicative.toAdd (Φ x))
      at h1
    rw [hx, toAdd_ofAdd, altAct_mk] at h1
    exact h1.symm
  let πe : alternatingGroup (Fin n) ≃* ↥(autSec L Y₁ Y₀) :=
    MulEquiv.ofBijective πA ⟨hπinj, hπs⟩
  have hfaith : L ⊓ centSec Y₁ Y₀ = ⊥ := by
    rw [eq_bot_iff, ← inf_centSec_eq_bot hn5 hψ hA hH₀ hH₁ hL]
    exact inf_le_inf_right _ altPre_le
  let σL : ↥L →* ↥(autSec L Y₁ Y₀) := (secHom hL₀ hL₁).codRestrict _ fun l => by
    rw [← range_secHom hL₀ hL₁]
    exact ⟨l, rfl⟩
  have hσLinj : Function.Injective σL := fun a b hab =>
    secHom_injective hL₀ hL₁ hfaith (congrArg Subtype.val hab)
  let α₀ : ↥L →* alternatingGroup (Fin n) := πe.symm.toMonoidHom.comp σL
  have hα₀inj : Function.Injective α₀ := πe.symm.injective.comp hσLinj
  have hπα : ∀ l : ↥L, ((π (α₀ l) : ↥(autSec L Y₁ Y₀)) : MulAut (Sec Y₁ Y₀)) =
      secHom hL₀ hL₁ l := fun l => congrArg Subtype.val (πe.apply_symm_apply (σL l))
  have hα₀bij : Function.Bijective α₀ := hα₀inj.bijective_of_nat_card_le
    (by rw [Nat.card_congr (altPreEquiv hψ hA).toEquiv])
  let θ : alternatingGroup (Fin n) ≃* alternatingGroup (Fin n) :=
    (altPreEquiv hψ hA).symm.trans (MulEquiv.ofBijective α₀ hα₀bij)
  obtain ⟨σ, hσ⟩ :=
    (CFSG.GroupTheory.AutAlternating.aut_alternatingGroup_bijective_conj n hn5 hn6).2 θ
  have hασ : ∀ l : ↥L, ((α₀ l : alternatingGroup (Fin n)) : Perm (Fin n)) =
      σ * ψ (Subgroup.inclusion altPre_le l) * σ⁻¹ := by
    intro l
    have h1 : MulAut.conjNormal σ (altPreEquiv hψ hA l) = θ (altPreEquiv hψ hA l) := by
      rw [hσ]
    have h2 : θ (altPreEquiv hψ hA l) = α₀ l := by
      change (MulEquiv.ofBijective α₀ hα₀bij) ((altPreEquiv hψ hA).symm
        (altPreEquiv hψ hA l)) = α₀ l
      rw [MulEquiv.symm_apply_apply]
      rfl
    rw [← h2, ← h1, MulAut.conjNormal_apply, coe_altPreEquiv]
  let τ : Multiplicative (altHeart n) →* Multiplicative (altHeart n) :=
    AddMonoidHom.toMultiplicative (altAct σ⁻¹)
  have hτ : ∀ y, Multiplicative.toAdd (τ y) = altAct σ⁻¹ (Multiplicative.toAdd y) :=
    fun _ => rfl
  let π₁ : ↥Y₁ →* Multiplicative (altHeart n) :=
    τ.comp (Φ.comp (QuotientGroup.mk' (Y₀.subgroupOf Y₁)))
  have hπ₁ : ∀ u, π₁ u = τ (Φ (QuotientGroup.mk u)) := fun _ => rfl
  refine natSec_of_altPre hn5 hA hH₀ hH₁ (π := π₁) (fun y => ?_) ?_ fun l u v huv => ?_
  · obtain ⟨x, hx⟩ := hΦsurj (Multiplicative.ofAdd (altAct σ (Multiplicative.toAdd y)))
    obtain ⟨u, rfl⟩ := QuotientGroup.mk_surjective x
    refine ⟨u, Multiplicative.toAdd.injective ?_⟩
    rw [hπ₁, hτ, hx, toAdd_ofAdd, altAct_inv_apply]
  · ext u
    rw [MonoidHom.mem_ker, hπ₁]
    constructor
    · intro h1
      have h2 : Φ (QuotientGroup.mk u) = 1 := by
        apply Multiplicative.toAdd.injective
        have h3 := congrArg (fun y => altAct σ (Multiplicative.toAdd y)) h1
        simp only [hτ, altAct_apply_inv, toAdd_one, map_zero] at h3
        rw [h3, toAdd_one]
      rw [← map_one Φ] at h2
      exact (QuotientGroup.eq_one_iff u).1 (hΦinj h2)
    · intro h1
      rw [(QuotientGroup.eq_one_iff u).2 h1, map_one, map_one]
  · have hmk : (QuotientGroup.mk v : Sec Y₁ Y₀) = secHom hL₀ hL₁ l (QuotientGroup.mk u) := by
      rw [secHom_mk]
      congr 1
      exact Subtype.ext huv
    rw [hπ₁, hπ₁, hτ, hτ, hmk, ← hπα, hΦeq, hασ, ← altAct_mul, ← altAct_mul]
    congr 1
    group

end Natural

section Fix

variable {V : Type} [CommGroup V] {H : Subgroup (MulAut V)} {n : ℕ}
  {ψ : ↥H →* Perm (Fin n)} {Y₀ Y₁ : Subgroup V}

theorem NatSec.card_sec (hN : NatSec ψ Y₀ Y₁) : Nat.card (Sec Y₁ Y₀) = Nat.card (altHeart n) := by
  obtain ⟨π, hπ, hker, -⟩ := hN
  let e : Sec Y₁ Y₀ ≃* Multiplicative (altHeart n) :=
    (QuotientGroup.quotientMulEquivOfEq hker.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective π hπ)
  rw [Nat.card_congr e.toEquiv]
  rfl

theorem NatSec.card_fixV (hN : NatSec ψ Y₀ Y₁) (hH₀ : H ≤ stabSub Y₀) (hH₁ : H ≤ stabSub Y₁)
    {B : Subgroup (MulAut V)} (hBH : B ≤ H) :
    Nat.card (fixV (autSec B Y₁ Y₀)) = Nat.card (altFix n ((B.subgroupOf H).map ψ)) := by
  classical
  obtain ⟨π, hπ, hker, heq⟩ := hN
  have hker' : ∀ a : ↥Y₁, π a = 1 ↔ (a : V) ∈ Y₀ := fun a => by
    rw [← MonoidHom.mem_ker, hker, Subgroup.mem_subgroupOf]
  let e : Sec Y₁ Y₀ ≃* Multiplicative (altHeart n) :=
    (QuotientGroup.quotientMulEquivOfEq hker.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective π hπ)
  have he : ∀ u : ↥Y₁, e (QuotientGroup.mk u) = π u := fun _ => rfl
  have hB₀ : B ≤ stabSub Y₀ := hBH.trans hH₀
  have hB₁ : B ≤ stabSub Y₁ := hBH.trans hH₁
  have hmem : ∀ s : Sec Y₁ Y₀, s ∈ fixV (autSec B Y₁ Y₀) ↔
      Multiplicative.toAdd (e s) ∈ altFix n ((B.subgroupOf H).map ψ) := by
    intro s
    obtain ⟨u, rfl⟩ := QuotientGroup.mk_surjective s
    rw [mk_mem_fixV_autSec_iff hB₀ hB₁, he, mem_altFix_iff_altAct]
    constructor
    · rintro hfix _ ⟨b, hb, rfl⟩
      have hbu : (b : MulAut V) u ∈ Y₁ := (hH₁ b.2 u).2 u.2
      have h1 := heq b u ⟨_, hbu⟩ rfl
      have h2 : π (⟨_, hbu⟩ * u⁻¹) = 1 := (hker' _).2 (hfix b (Subgroup.mem_subgroupOf.1 hb))
      rw [map_mul, map_inv, mul_inv_eq_one] at h2
      rw [← h1, h2]
    · intro hfix b hb
      have hbu : b (u : V) ∈ Y₁ := (hB₁ hb u).2 u.2
      have h1 := heq ⟨b, hBH hb⟩ u ⟨_, hbu⟩ rfl
      have h2 := hfix _ ⟨⟨b, hBH hb⟩, Subgroup.mem_subgroupOf.2 hb, rfl⟩
      rw [← h1] at h2
      have h3 : π (⟨_, hbu⟩ * u⁻¹) = 1 := by
        rw [map_mul, map_inv, Multiplicative.toAdd.injective h2, mul_inv_cancel]
      exact (hker' _).1 h3
  let f : ↥(fixV (autSec B Y₁ Y₀)) ≃ ↥(altFix n ((B.subgroupOf H).map ψ)) :=
    { toFun := fun s => ⟨Multiplicative.toAdd (e s), (hmem s).1 s.2⟩
      invFun := fun x => ⟨e.symm (Multiplicative.ofAdd x), (hmem _).2 (by simp)⟩
      left_inv := fun s => by ext; simp
      right_inv := fun x => by ext; simp }
  exact Nat.card_congr f

theorem card_map_subgroupOf {ψ : ↥H →* Perm (Fin n)} (hψ : Function.Injective ψ)
    {B : Subgroup (MulAut V)} (hBH : B ≤ H) :
    Nat.card ((B.subgroupOf H).map ψ) = Nat.card B := by
  rw [Subgroup.card_map_of_injective hψ]
  exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hBH).toEquiv

theorem mul_self_of_mem_map {ψ : ↥H →* Perm (Fin n)} {B : Subgroup (MulAut V)}
    (hel : IsElemAbelian2 B) : ∀ b ∈ (B.subgroupOf H).map ψ, b * b = 1 := by
  rintro _ ⟨b, hb, rfl⟩
  have h1 : b * b = 1 := by
    apply Subtype.ext
    have := hel.2 _ (Subgroup.mem_subgroupOf.1 hb)
    rw [pow_two] at this
    simpa using this
  rw [← map_mul, h1, map_one]

theorem NatSec.card_mul_card_fixV_le (hN : NatSec ψ Y₀ Y₁) (hn : 5 ≤ n)
    (hψ : Function.Injective ψ) (hH₀ : H ≤ stabSub Y₀) (hH₁ : H ≤ stabSub Y₁)
    {B : Subgroup (MulAut V)} (hBH : B ≤ H) (hel : IsElemAbelian2 B)
    (hΔ : ¬ IsMatchingGroup ((B.subgroupOf H).map ψ)) :
    Nat.card B * Nat.card (fixV (autSec B Y₁ Y₀)) ≤ Nat.card (Sec Y₁ Y₀) := by
  rw [hN.card_fixV hH₀ hH₁ hBH, hN.card_sec, ← card_map_subgroupOf hψ hBH]
  exact natFF_le hn (mul_self_of_mem_map hel) hΔ

theorem NatSec.card_mul_card_fixV_eq (hN : NatSec ψ Y₀ Y₁) (hn : 3 ≤ n)
    (hψ : Function.Injective ψ) (hH₀ : H ≤ stabSub Y₀) (hH₁ : H ≤ stabSub Y₁)
    {B : Subgroup (MulAut V)} (hBH : B ≤ H) (hΔ : IsMatchingGroup ((B.subgroupOf H).map ψ)) :
    Nat.card B * Nat.card (fixV (autSec B Y₁ Y₀)) = 2 * Nat.card (Sec Y₁ Y₀) := by
  rw [hN.card_fixV hH₀ hH₁ hBH, hN.card_sec, ← card_map_subgroupOf hψ hBH]
  exact natFF_matching hn hΔ

end Fix

end CFSG.HardMathSupport.Cooperstein.Coordinator.EightFive
