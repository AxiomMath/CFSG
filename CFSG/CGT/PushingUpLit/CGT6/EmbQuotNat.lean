module

public import CFSG.CGT.PushingUpLit.CGT6.EmbQuot
public import CFSG.CGT.PushingUpLit.CGT6.EmbConjMod
import CFSG.CGT.PushingUpLit.CGT6.EmbQuotIso
import CFSG.CGT.PushingUpLit.CGT6.EmbModule.TwoSeven

public section

namespace CFSG.CGT.PushingUpLit.CGT6

open CFSG CFSG.RankThree.PartOne CFSG.Quasithin CFSG.CGT.PushingUpLit
  CFSG.CGT.PushingUpLit.BHS6
open scoped commutatorElement

section Hom

variable {V : Type} [CommGroup V] {G : Subgroup (MulAut V)} {A : Subgroup V} (h : GInv G A)
  {K : Subgroup (MulAut V)}

@[expose] noncomputable def commQHom (hKG : K ≤ G) : ↥(commV K) →* ↥(commV (barQ h K)) :=
  ((QuotientGroup.mk' A).comp (commV K).subtype).codRestrict (commV (barQ h K))
    (fun u => by
      rw [← commV_barQ h hKG]
      exact ⟨u, u.2, rfl⟩)

theorem coe_commQHom (hKG : K ≤ G) (u : ↥(commV K)) :
    ((commQHom h hKG u : ↥(commV (barQ h K))) : V ⧸ A) = ((u : V) : V ⧸ A) := rfl

theorem commQHom_surjective (hKG : K ≤ G) : Function.Surjective (commQHom h hKG) := by
  intro y
  have hy : (y : V ⧸ A) ∈ (commV K).map (QuotientGroup.mk' A) := by
    rw [commV_barQ h hKG]
    exact y.2
  obtain ⟨u, hu, hu'⟩ := hy
  exact ⟨⟨u, hu⟩, Subtype.ext hu'⟩

theorem commQHom_eq_one_iff (hKG : K ≤ G) (u : ↥(commV K)) :
    commQHom h hKG u = 1 ↔ (u : V) ∈ A := by
  rw [Subtype.ext_iff, coe_commQHom, OneMemClass.coe_one, QuotientGroup.eq_one_iff]

theorem isNatSectionBy_resHom {S M : Type*} [Group S] [Group M] (act : S → M → M)
    (hKG : K ≤ G) (hinj : Function.Injective (resQ G A h))
    (hinjR : Function.Injective (resHom K))
    (hK : IsNatSectionBy act (barQ h K) (commV (barQ h K)) ⊥) :
    IsNatSectionBy act (resHom K).range (⊤ : Subgroup ↥(commV K))
      (A.subgroupOf (commV K)) := by
  obtain ⟨-, θ, β, hβs, hβk, hβe⟩ := hK
  let θ' : ↥(resHom K).range ≃* S :=
    (MonoidHom.ofInjective hinjR).symm.trans ((homImgEquiv hinj hKG).trans θ)
  let ψ : ↥(⊤ : Subgroup ↥(commV K)) →* ↥(commV (barQ h K)) :=
    (commQHom h hKG).comp (⊤ : Subgroup ↥(commV K)).subtype
  refine ⟨fun _ _ _ _ => Subgroup.mem_top _, θ', β.comp ψ, ?_, ?_, ?_⟩
  · refine hβs.comp (fun y => ?_)
    obtain ⟨u, rfl⟩ := commQHom_surjective h hKG y
    exact ⟨⟨u, Subgroup.mem_top _⟩, rfl⟩
  · ext t
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply, ← MonoidHom.mem_ker, hβk,
      Subgroup.mem_subgroupOf, Subgroup.mem_bot, Subgroup.mem_subgroupOf,
      Subgroup.mem_subgroupOf]
    exact QuotientGroup.eq_one_iff _
  · rintro ⟨_, k, rfl⟩ p hp
    have hθ : θ' ⟨resHom K k, k, rfl⟩ = θ (homImgEquiv hinj hKG k) := by
      have : (⟨resHom K k, k, rfl⟩ : ↥(resHom K).range) = MonoidHom.ofInjective hinjR k := rfl
      rw [this]
      simp [θ']
    have hmem : ((homImgEquiv hinj hKG k : ↥(barQ h K)) : MulAut (V ⧸ A))
        ((commQHom h hKG p.1 : ↥(commV (barQ h K))) : V ⧸ A) ∈ commV (barQ h K) :=
      commV_invariant (homImgEquiv hinj hKG k).2 (commQHom h hKG p.1).2
    have key : commQHom h hKG ((resHom K k : MulAut ↥(commV K)) p.1) =
        ⟨((homImgEquiv hinj hKG k : ↥(barQ h K)) : MulAut (V ⧸ A))
          ((commQHom h hKG p.1 : ↥(commV (barQ h K))) : V ⧸ A), hmem⟩ := Subtype.ext rfl
    rw [hθ]
    show β (commQHom h hKG ((resHom K k : MulAut ↥(commV K)) p.1)) = _
    rw [key]
    exact hβe (homImgEquiv hinj hKG k) (commQHom h hKG p.1) hmem

end Hom

section Faithful

variable {V : Type} [CommGroup V]

theorem sq_eq_one_of_fix_commV (hV : ∀ v : V, v ^ 2 = 1) {X : Subgroup (MulAut V)}
    {x : MulAut V} (hx : x ∈ X) (htriv : ∀ w ∈ commV X, x w = w) : x ^ 2 = 1 := by
  ext v
  have hmem : x v * v⁻¹ ∈ commV X := Subgroup.subset_closure ⟨x, hx, v, rfl⟩
  have h := htriv _ hmem
  rw [map_mul, map_inv] at h
  have hvv : v * v = 1 := by rw [← pow_two]; exact hV v
  have hxx : x v * x v = 1 := by rw [← pow_two]; exact hV _
  have h2 : (x ^ 2) v = x (x v) := by simp [pow_two, MulAut.mul_apply]
  rw [h2]
  calc x (x v) = (x (x v) * (x v)⁻¹) * x v := (inv_mul_cancel_right _ _).symm
    _ = (x v * v⁻¹) * x v := by rw [h]
    _ = (x v * x v) * v⁻¹ := mul_right_comm _ _ _
    _ = v⁻¹ := by rw [hxx, one_mul]
    _ = v := inv_eq_of_mul_eq_one_right hvv

theorem injective_resHom_of_pCore (hV : ∀ v : V, v ^ 2 = 1) {X : Subgroup (MulAut V)}
    (hp : pCore 2 ↥X = ⊥) : Function.Injective (resHom X) := by
  rw [injective_iff_map_eq_one]
  intro x hx
  have hker : IsPGroup 2 ↥(resHom X).ker := by
    rintro ⟨y, hy⟩
    refine ⟨1, Subtype.ext ?_⟩
    have htriv : ∀ w ∈ commV X, (y : MulAut V) w = w := by
      intro w hw
      have := congrArg (fun φ : MulAut ↥(commV X) => ((φ ⟨w, hw⟩ : ↥(commV X)) : V))
        (MonoidHom.mem_ker.mp hy)
      simpa [resHom_apply] using this
    exact Subtype.ext (sq_eq_one_of_fix_commV hV y.2 htriv)
  have hle : (resHom X).ker ≤ pCore 2 ↥X := le_sSup ⟨(resHom X).normal_ker, hker⟩
  rw [hp] at hle
  have := hle (MonoidHom.mem_ker.mpr hx)
  simpa using this

end Faithful

section Indec

variable {V : Type} [CommGroup V] {G : Subgroup (MulAut V)} {A : Subgroup V}

theorem commV_le_of_sup_fix (D : QData G A) {K : Subgroup (MulAut V)} (hKG : K ≤ G)
    (hUS : USelf K) {P Q : Subgroup V} (hQ : ∀ x ∈ K, ∀ a ∈ Q, x a ∈ Q) (hPA : P ≤ A)
    (hsup : P ⊔ Q = commV K) : commV K ≤ Q := by
  apply hUS Q
  intro g hg u hu
  rw [← hsup] at hu
  obtain ⟨p, hp, q, hq, rfl⟩ := Subgroup.mem_sup.mp hu
  have h1 : g p = p := D.fix g (hKG hg) p (hPA hp)
  have h2 : g (p * q) * (p * q)⁻¹ = g q * q⁻¹ := by
    rw [map_mul, h1, mul_inv_rev]
    simp only [mul_comm, mul_left_comm, mul_assoc, mul_inv_cancel_left]
  rw [h2]
  exact Q.mul_mem (hQ g hg q hq) (Q.inv_mem hq)

variable [Finite V]

theorem card_commV_barQ_le_two (D : QData G A) {K : Subgroup (MulAut V)} (hKG : K ≤ G)
    {P Q : Subgroup V} (hPU : P ≤ commV K) (hQU : Q ≤ commV K) (hinf : P ⊓ Q = ⊥)
    (hP1 : P.map (QuotientGroup.mk' A) = commV (barQ D.inv K))
    (hQ1 : Q.map (QuotientGroup.mk' A) = commV (barQ D.inv K)) :
    Nat.card ↥(commV (barQ D.inv K)) ≤ 2 := by
  have hPc : Nat.card ↥(commV (barQ D.inv K)) ≤ Nat.card ↥P := by
    refine Nat.card_le_card_of_surjective
      (fun p : ↥P => commQHom D.inv hKG ⟨p, hPU p.2⟩) ?_
    intro y
    have hy : (y : V ⧸ A) ∈ P.map (QuotientGroup.mk' A) := by rw [hP1]; exact y.2
    obtain ⟨p, hp, hpy⟩ := hy
    exact ⟨⟨p, hp⟩, Subtype.ext hpy⟩
  have hQc : Nat.card ↥(commV (barQ D.inv K)) ≤ Nat.card ↥Q := by
    refine Nat.card_le_card_of_surjective
      (fun q : ↥Q => commQHom D.inv hKG ⟨q, hQU q.2⟩) ?_
    intro y
    have hy : (y : V ⧸ A) ∈ Q.map (QuotientGroup.mk' A) := by rw [hQ1]; exact y.2
    obtain ⟨q, hq, hqy⟩ := hy
    exact ⟨⟨q, hq⟩, Subtype.ext hqy⟩
  have hPQ : Nat.card ↥P * Nat.card ↥Q ≤ Nat.card ↥(commV K) := by
    rw [← Nat.card_prod]
    refine Nat.card_le_card_of_injective
      (fun pq : ↥P × ↥Q => (⟨(pq.1 : V) * pq.2, (commV K).mul_mem (hPU pq.1.2) (hQU pq.2.2)⟩ :
        ↥(commV K))) ?_
    rintro ⟨⟨p, hp⟩, ⟨q, hq⟩⟩ ⟨⟨p', hp'⟩, ⟨q', hq'⟩⟩ heq
    have h1 : p * q = p' * q' := congrArg Subtype.val heq
    have h3 : p / p' = q' / q := div_eq_div_iff_mul_eq_mul.mpr (by rw [h1, mul_comm])
    have h4 : p / p' ∈ P ⊓ Q := ⟨P.div_mem hp hp', h3 ▸ Q.div_mem hq' hq⟩
    rw [hinf, Subgroup.mem_bot, div_eq_one] at h4
    subst h4
    rw [div_self', eq_comm, div_eq_one] at h3
    subst h3
    rfl
  have hUc : Nat.card ↥(commV K) ≤ Nat.card ↥(commV (barQ D.inv K)) * 2 := by
    have hsurj := commQHom_surjective D.inv hKG
    have h1 : Nat.card ↥(commV K) =
        Nat.card (↥(commV K) ⧸ (commQHom D.inv hKG).ker) *
          Nat.card ↥(commQHom D.inv hKG).ker :=
      Subgroup.card_eq_card_quotient_mul_card_subgroup _
    have h2 : Nat.card (↥(commV K) ⧸ (commQHom D.inv hKG).ker) =
        Nat.card ↥(commV (barQ D.inv K)) :=
      Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective _ hsurj).toEquiv
    have h3 : Nat.card ↥(commQHom D.inv hKG).ker ≤ 2 := by
      refine le_trans (Nat.card_le_card_of_injective
        (fun u : ↥(commQHom D.inv hKG).ker =>
          (⟨(u.1 : V), (commQHom_eq_one_iff D.inv hKG u.1).mp u.2⟩ : ↥A)) ?_) D.card
      intro u u' h
      have h' : ((u.1 : ↥(commV K)) : V) = ((u'.1 : ↥(commV K)) : V) :=
        congrArg (fun a : ↥A => (a : V)) h
      exact Subtype.ext (Subtype.ext h')
    rw [h1, h2]
    exact Nat.mul_le_mul_left _ h3
  have hpos : 0 < Nat.card ↥(commV (barQ D.inv K)) := Nat.card_pos
  have hmul := Nat.mul_le_mul hPc hQc
  have : Nat.card ↥(commV (barQ D.inv K)) * Nat.card ↥(commV (barQ D.inv K)) ≤
      Nat.card ↥(commV (barQ D.inv K)) * 2 := hmul.trans (hPQ.trans hUc)
  exact Nat.le_of_mul_le_mul_left this hpos

theorem eq_bot_or_eq_bot_of_split (D : QData G A) {n : ℕ} (hn : 2 ≤ n)
    {K : Subgroup (MulAut V)} (hKG : K ≤ G) (hK : NatOmegaN n (barQ D.inv K)) (hUS : USelf K)
    {P Q : Subgroup V} (hP : ∀ x ∈ K, ∀ a ∈ P, x a ∈ P) (hQ : ∀ x ∈ K, ∀ a ∈ Q, x a ∈ Q)
    (hinf : P ⊓ Q = ⊥) (hsup : P ⊔ Q = commV K) : P = ⊥ ∨ Q = ⊥ := by
  have hPU : P ≤ commV K := hsup ▸ le_sup_left
  have hQU : Q ≤ commV K := hsup ▸ le_sup_right
  have hirr : ∀ R : Subgroup V, (∀ x ∈ K, ∀ a ∈ R, x a ∈ R) → R ≤ commV K →
      R.map (QuotientGroup.mk' A) = ⊥ ∨ R.map (QuotientGroup.mk' A) = commV (barQ D.inv K) := by
    intro R hR hRU
    refine NatOmegaN.irreducible hn hK _ ?_ ?_
    · intro x hx a ha
      obtain ⟨g, hg, rfl⟩ := mem_homImg.mp hx
      obtain ⟨r, hr, rfl⟩ := ha
      exact ⟨(g : MulAut V) r, hR _ hg r hr, rfl⟩
    · rw [← commV_barQ D.inv hKG]
      exact Subgroup.map_mono hRU
  have hle : ∀ R : Subgroup V, R.map (QuotientGroup.mk' A) = ⊥ → R ≤ A := by
    intro R hR x hx
    have : (QuotientGroup.mk' A) x ∈ (⊥ : Subgroup (V ⧸ A)) := hR ▸ Subgroup.mem_map_of_mem _ hx
    rwa [Subgroup.mem_bot, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at this
  rcases hirr P hP hPU with hP0 | hP1
  · left
    have hUQ := commV_le_of_sup_fix D hKG hUS hQ (hle P hP0) hsup
    rw [eq_bot_iff, ← hinf]
    exact le_inf le_rfl (hPU.trans hUQ)
  · rcases hirr Q hQ hQU with hQ0 | hQ1
    · right
      have hUP := commV_le_of_sup_fix D hKG hUS hP (hle Q hQ0) (by rw [sup_comm]; exact hsup)
      rw [eq_bot_iff, ← hinf]
      exact le_inf (hQU.trans hUP) le_rfl
    · exfalso
      have h2 := card_commV_barQ_le_two D hKG hPU hQU hinf hP1 hQ1
      have h8 : 2 ^ (4 * n) ≤ 2 := by
        rcases NatOmegaN.cases hn hK with ⟨-, hc⟩ | ⟨-, hc⟩ <;> rwa [hc] at h2
      have : 2 ^ 8 ≤ 2 ^ (4 * n) := Nat.pow_le_pow_right (by norm_num) (by omega)
      omega

end Indec

section Module

theorem eq_bot_of_natSection_top {W : Type} [CommGroup W] [Finite W] (hW : ∀ w : W, w ^ 2 = 1)
    {n : ℕ} (hn : 2 ≤ n) {G' : Subgroup (MulAut W)} {Z : Subgroup W}
    (hind : ∀ P Q : Subgroup W, GInv G' P → GInv G' Q → P ⊓ Q = ⊥ → P ⊔ Q = ⊤ →
      P = ⊥ ∨ Q = ⊥)
    (hZ : ∀ g ∈ G', ∀ a ∈ Z, g a = a) (hZtop : Z ≠ ⊤)
    (hnat : IsNatSectionBy (omegaPlusAct n) G' ⊤ Z ∨ IsNatSectionBy (omegaMinusAct n) G' ⊤ Z) :
    Z = ⊥ := by
  have hZinv : GInv G' Z := fun g hg a ha => by rw [hZ g hg a ha]; exact ha
  have htopinv : GInv G' (⊤ : Subgroup W) := fun _ _ _ _ => Subgroup.mem_top _
  have htop : ∀ g ∈ G', ∀ v : W, g v * v⁻¹ ∈ (⊤ : Subgroup W) := fun _ _ _ => Subgroup.mem_top _
  rcases hnat with h | h
  · exact (emb_two_seven W hW G' n hn hind Z ⊤ le_top hZinv htopinv hZ htop h).1
  · exact (CGT6X.extOmegaMinus_holds W hW G' n (by omega) hind Z ⊤ le_top hZinv htopinv hZ htop
      h Z hZinv).resolve_right hZtop

end Module

section Nat

variable {V : Type} [CommGroup V] [Finite V] {G : Subgroup (MulAut V)} {A : Subgroup V}

theorem QData.inf_commV_eq_bot (hV : ∀ v : V, v ^ 2 = 1) (D : QData G A) {n : ℕ} (hn : 2 ≤ n)
    {K : Subgroup (MulAut V)} (hKG : K ≤ G) (hK : NatOmegaN n (barQ D.inv K)) :
    A ⊓ commV K = ⊥ := by
  have hinj := D.resQ_injective
  have hperf : ⁅K, K⁆ = K := by
    have hKK : ⁅K, K⁆ ≤ G := (Subgroup.commutator_mono hKG hKG).trans
      (Subgroup.commutator_le_self _)
    have h1 : homImg (resQ G A D.inv) ⁅K, K⁆ = homImg (resQ G A D.inv) K := by
      rw [← homImg_commutator hKG hKG]
      exact hK.commutator_eq_self hn
    calc ⁅K, K⁆ = homPre (resQ G A D.inv) (homImg (resQ G A D.inv) ⁅K, K⁆) :=
          (homPre_homImg hinj hKK).symm
      _ = homPre (resQ G A D.inv) (homImg (resQ G A D.inv) K) := by rw [h1]
      _ = K := homPre_homImg hinj hKG
  have hUS : USelf K := USelf_of_perfect hperf
  have hp : pCore 2 ↥K = ⊥ :=
    pCore_eq_bot_of_equiv (homImgEquiv hinj hKG) (hK.pCore_eq_bot hn)
  have hinjR := injective_resHom_of_pCore hV hp
  have hW : ∀ w : ↥(commV K), w ^ 2 = 1 := fun w => Subtype.ext (by simpa using hV w)
  have hind : ∀ P Q : Subgroup ↥(commV K), GInv (resHom K).range P → GInv (resHom K).range Q →
      P ⊓ Q = ⊥ → P ⊔ Q = ⊤ → P = ⊥ ∨ Q = ⊥ := by
    intro P Q hP hQ hinf hsup
    have hinv : ∀ R : Subgroup ↥(commV K), GInv (resHom K).range R →
        ∀ x ∈ K, ∀ a ∈ R.map (commV K).subtype, x a ∈ R.map (commV K).subtype := by
      intro R hR x hx a ha
      obtain ⟨w, hw, rfl⟩ := ha
      exact ⟨resHom K ⟨x, hx⟩ w, hR _ ⟨⟨x, hx⟩, rfl⟩ w hw, rfl⟩
    have h := eq_bot_or_eq_bot_of_split D hn hKG hK hUS (hinv P hP) (hinv Q hQ)
      (by rw [← Subgroup.map_inf_eq _ _ _ (commV K).subtype_injective, hinf, Subgroup.map_bot])
      (by rw [← Subgroup.map_sup, hsup, ← MonoidHom.range_eq_map, Subgroup.range_subtype])
    rcases h with h | h
    · exact Or.inl ((Subgroup.map_eq_bot_iff_of_injective _ (commV K).subtype_injective).mp h)
    · exact Or.inr ((Subgroup.map_eq_bot_iff_of_injective _ (commV K).subtype_injective).mp h)
  have hZ : ∀ g ∈ (resHom K).range, ∀ a ∈ A.subgroupOf (commV K), g a = a := by
    rintro _ ⟨k, rfl⟩ a ha
    exact Subtype.ext (D.fix _ (hKG k.2) _ ha)
  have hZtop : A.subgroupOf (commV K) ≠ ⊤ := by
    intro htop
    apply commV_ne_bot_of_not_isPGroup (hK.not_isPGroup hn)
    rw [← commV_barQ D.inv hKG, eq_bot_iff]
    rintro _ ⟨u, hu, rfl⟩
    have : (⟨u, hu⟩ : ↥(commV K)) ∈ A.subgroupOf (commV K) := htop ▸ Subgroup.mem_top _
    exact (QuotientGroup.eq_one_iff _).mpr this
  have hnat : IsNatSectionBy (omegaPlusAct n) (resHom K).range ⊤ (A.subgroupOf (commV K)) ∨
      IsNatSectionBy (omegaMinusAct n) (resHom K).range ⊤ (A.subgroupOf (commV K)) := by
    rcases hK with h1 | h1
    · exact Or.inl (isNatSectionBy_resHom D.inv _ hKG hinj hinjR h1)
    · exact Or.inr (isNatSectionBy_resHom D.inv _ hKG hinj hinjR h1)
  have hZ0 := eq_bot_of_natSection_top hW hn hind hZ hZtop hnat
  rw [eq_bot_iff]
  rintro a ⟨ha1, ha2⟩
  have : (⟨a, ha2⟩ : ↥(commV K)) ∈ A.subgroupOf (commV K) := ha1
  rw [hZ0, Subgroup.mem_bot] at this
  simpa using congrArg Subtype.val this

theorem QData.natOmegaN_pre (hV : ∀ v : V, v ^ 2 = 1) (D : QData G A) {n : ℕ} (hn : 2 ≤ n)
    {X : Subgroup (MulAut (V ⧸ A))} (hXG : X ≤ barQ D.inv G) (hX : NatOmegaN n X) :
    A ⊓ commV (preQ D.inv X) = ⊥ ∧ NatOmegaN n (preQ D.inv X) := by
  have hrange : X ≤ (resQ G A D.inv).range := by
    have : barQ D.inv G = (resQ G A D.inv).range := homImg_self
    exact this ▸ hXG
  have hbar : barQ D.inv (preQ D.inv X) = X := homImg_homPre hrange
  have hKG : preQ D.inv X ≤ G := homPre_le X
  have hK : NatOmegaN n (barQ D.inv (preQ D.inv X)) := by rw [hbar]; exact hX
  have hA := D.inf_commV_eq_bot hV hn hKG hK
  refine ⟨hA, ?_⟩
  rcases hK with h1 | h1
  · exact Or.inl ((isNatSectionBy_barQ_iff D.inv _ hKG hA D.resQ_injective).mpr h1)
  · exact Or.inr ((isNatSectionBy_barQ_iff D.inv _ hKG hA D.resQ_injective).mpr h1)

end Nat

end CFSG.CGT.PushingUpLit.CGT6
