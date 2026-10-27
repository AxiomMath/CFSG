module

public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKD309LieMap
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKD309LieConj
public import CFSG.GroupTheory.CoprimeQuotientNormalizer

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.KD309L

open Subgroup CFSG.Open
open CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.KD309
open scoped commutatorElement

variable {Y : Type} [Group Y] [Finite Y]

theorem card_map_eq_of_inj {Z : Type} [Group Z] (π : Y →* Z) (A : Subgroup Y)
    (hinj : ∀ a ∈ A, ∀ b ∈ A, π a = π b → a = b) : Nat.card (A.map π) = Nat.card A := by
  symm
  refine Nat.card_congr (Equiv.ofBijective
    (fun x : A => (⟨π x, Subgroup.mem_map_of_mem π x.2⟩ : A.map π)) ⟨?_, ?_⟩)
  · intro a b h
    exact Subtype.ext (hinj a a.2 b b.2 (congrArg Subtype.val h))
  · rintro ⟨_, a, ha, rfl⟩
    exact ⟨⟨a, ha⟩, rfl⟩

theorem relIndex_map_dvd {Z : Type} [Group Z] (π : Y →* Z) (S N : Subgroup Y) (hSN : S ≤ N) :
    (S.map π).relIndex (N.map π) ∣ S.relIndex N := by
  set f : ↥N →* Z := π.comp N.subtype with hf
  have hrange : f.range = N.map π := by
    ext x
    constructor
    · rintro ⟨n, rfl⟩
      exact ⟨n, n.2, rfl⟩
    · rintro ⟨n, hn, rfl⟩
      exact ⟨⟨n, hn⟩, rfl⟩
  have hmap : (S.subgroupOf N).map f = S.map π := by
    ext x
    constructor
    · rintro ⟨s, hs, rfl⟩
      exact ⟨s, hs, rfl⟩
    · rintro ⟨s, hs, rfl⟩
      exact ⟨⟨s, hSN hs⟩, hs, rfl⟩
  have h := Subgroup.index_map_dvd (H := S.subgroupOf N) (f := f.rangeRestrict)
    f.rangeRestrict_surjective
  have h2 : ((S.subgroupOf N).map f.rangeRestrict) = (S.map π).subgroupOf f.range := by
    ext ⟨y, hy⟩
    constructor
    · rintro ⟨s, hs, hsy⟩
      rw [Subgroup.mem_subgroupOf, ← hmap]
      exact ⟨s, hs, congrArg Subtype.val hsy⟩
    · intro h1
      rw [Subgroup.mem_subgroupOf, ← hmap] at h1
      obtain ⟨s, hs, hsy⟩ := h1
      exact ⟨s, hs, Subtype.ext hsy⟩
  rw [Subgroup.relIndex, Subgroup.relIndex, ← hrange]
  rw [h2] at h
  exact h

theorem exists_cfg_of_quotient (O : Subgroup Y) [O.Normal] (hO : ¬ 5 ∣ Nat.card O)
    {P : Subgroup Y} (hP : IsPGroup 5 P) {z : Y} (hzP : z ∈ P) (hz5 : orderOf z = 5)
    {J' : Subgroup (Y ⧸ O)} {n' g' h' : Y ⧸ O}
    (c : KD309Cfg (P.map (QuotientGroup.mk' O)) (QuotientGroup.mk' O z) J' n' g' h') :
    ∃ (J : Subgroup Y) (n g h : Y), KD309Cfg P z J n g h := by
  classical
  haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  set π : Y →* Y ⧸ O := QuotientGroup.mk' O with hπ
  have inj : ∀ a ∈ P, ∀ b ∈ P, π a = π b → a = b := inj_of_pgroup O hO hP
  have lift : ∀ t ∈ P.map π, ∃ p ∈ P, π p = t := fun t ht => by
    obtain ⟨p, hp, hpt⟩ := ht
    exact ⟨p, hp, hpt⟩
  set J : Subgroup Y := J'.comap π ⊓ P with hJ
  have hJP : J ≤ P := inf_le_right
  have hJ' : J.map π = J' := by
    ext t
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact hx.1
    · intro ht
      obtain ⟨p, hp, hpt⟩ := lift t (c.J_le ht)
      exact ⟨p, ⟨by simpa [hpt] using ht, hp⟩, hpt⟩
  have hEP : ⁅J, P⁆ ≤ P := by
    rw [Subgroup.commutator_le]
    intro j hj p hp
    rw [commutatorElement_def]
    exact P.mul_mem (P.mul_mem (P.mul_mem (hJP hj) hp) (P.inv_mem (hJP hj))) (P.inv_mem hp)
  have hEmap : (⁅J, P⁆).map π = ⁅J', P.map π⁆ := by
    rw [Subgroup.map_commutator J P π, hJ']
  have hord : ∀ x ∈ P, orderOf (π x) = orderOf x := by
    intro x hx
    have hinj : Function.Injective (π.comp P.subtype) := fun u v huv =>
      Subtype.ext (inj u u.2 v v.2 huv)
    have := orderOf_injective _ hinj ⟨x, hx⟩
    rw [Subgroup.orderOf_mk] at this
    simpa using this
  set B : Subgroup Y := J ⊔ ⁅J, P⁆ with hB
  have hBP : B ≤ P := sup_le hJP hEP
  have hBmap : B.map π = J' ⊔ ⁅J', P.map π⁆ := by rw [hB, Subgroup.map_sup, hJ', hEmap]
  have hnormB := CFSG.GroupTheory.normal_coprime_quotient_normalizer 5 O hO B (hP.to_le hBP)
  have hn'mem : n' ∈ (normalizer (B : Set Y)).map π := by
    rw [hnormB, hBmap]
    refine Subgroup.mem_normalizer_iff_map_conj_eq.mpr ?_
    rw [Subgroup.map_sup, Subgroup.mem_normalizer_iff_map_conj_eq.mp c.n_J,
      Subgroup.mem_normalizer_iff_map_conj_eq.mp c.n_E]
  obtain ⟨n, hnB, hnπ⟩ := hn'mem
  have hnB' := Subgroup.mem_normalizer_iff_map_conj_eq.mp hnB
  have hπc : ∀ x : Y, π ((MulAut.conj n).toMonoidHom x) = (MulAut.conj n').toMonoidHom (π x) := by
    intro x
    simp [MulAut.conj_apply, hnπ]
  have hnorm1 : ∀ A : Subgroup Y, A ≤ B → (A.map π).map (MulAut.conj n').toMonoidHom = A.map π →
      n ∈ normalizer (A : Set Y) := by
    intro A hAB hA
    refine Subgroup.mem_normalizer_iff_map_conj_eq.mpr ?_
    have hle : A.map (MulAut.conj n).toMonoidHom ≤ A := by
      rintro _ ⟨a, ha, rfl⟩
      have h1 : (MulAut.conj n).toMonoidHom a ∈ B := by
        rw [← hnB']
        exact Subgroup.mem_map_of_mem _ (hAB ha)
      have h2 : π ((MulAut.conj n).toMonoidHom a) ∈ A.map π := by
        rw [hπc, ← hA]
        exact Subgroup.mem_map_of_mem _ (Subgroup.mem_map_of_mem _ ha)
      obtain ⟨a2, ha2, ha2π⟩ := h2
      have := inj a2 (hBP (hAB ha2)) _ (hBP h1) ha2π
      exact this ▸ ha2
    exact Subgroup.eq_of_le_of_card_ge hle (by
      rw [Subgroup.card_map_of_injective (MulAut.conj n).injective])
  have hJc : (J.map π).map (MulAut.conj n').toMonoidHom = J.map π := by
    rw [hJ']
    exact Subgroup.mem_normalizer_iff_map_conj_eq.mp c.n_J
  have hEc : ((⁅J, P⁆).map π).map (MulAut.conj n').toMonoidHom = (⁅J, P⁆).map π := by
    rw [hEmap]
    exact Subgroup.mem_normalizer_iff_map_conj_eq.mp c.n_E
  have hnJ : n ∈ normalizer (J : Set Y) := hnorm1 J le_sup_left hJc
  have hnE : n ∈ normalizer ((⁅J, P⁆ : Subgroup Y) : Set Y) := hnorm1 _ le_sup_right hEc
  obtain ⟨g, hgP, hgπ⟩ := lift g' c.g_mem
  obtain ⟨p0, hp0, hh'⟩ := mem_conjSub.mp c.h_mem
  obtain ⟨p, hpP, hpπ⟩ := lift p0 hp0
  have hhπ : π (n * p * n⁻¹) = h' := by rw [map_mul, map_mul, map_inv, hnπ, hpπ, hh']
  obtain ⟨cz, hcz⟩ := isConj_iff.mp c.conj_g
  obtain ⟨cz', hcz'⟩ := isConj_iff.mp c.conj_h
  have hzo : orderOf (π z) = 5 := by rw [hord z hzP, hz5]
  have hg'o : orderOf g' = 5 := by
    have := MulEquiv.orderOf_eq (MulAut.conj cz) (π z)
    rw [MulAut.conj_apply, hcz] at this
    rw [this, hzo]
  have hh'o : orderOf h' = 5 := by
    have := MulEquiv.orderOf_eq (MulAut.conj cz') (π z)
    rw [MulAut.conj_apply, hcz'] at this
    rw [this, hzo]
  have hgo : orderOf g = 5 := by rw [← hord g hgP, hgπ, hg'o]
  have hho : orderOf (n * p * n⁻¹) = 5 := by
    have h1 : orderOf (n * p * n⁻¹) = orderOf p := by
      have := MulEquiv.orderOf_eq (MulAut.conj n) p
      rwa [MulAut.conj_apply] at this
    have h2 : orderOf p = orderOf (π p) := (hord p hpP).symm
    have h3 : orderOf p0 = orderOf h' := by
      have := MulEquiv.orderOf_eq (MulAut.conj n') p0
      rw [MulAut.conj_apply, hh'] at this
      exact this.symm
    rw [h1, h2, hpπ, h3, hh'o]
  refine ⟨J, n, g, n * p * n⁻¹, ?_⟩
  refine
    { J_le := hJP
      J_abel := ⟨⟨⟨fun a b => ?_⟩⟩, fun x hx => ?_⟩
      J_card := ?_
      E_card := ?_
      z_mem := ?_
      n_J := hnJ
      n_E := hnE
      g_mem := hgP
      g_not := fun hg => c.g_not (by rw [← hgπ, ← hJ']; exact Subgroup.mem_map_of_mem π hg)
      h_mem := mem_conjSub.mpr ⟨p, hpP, rfl⟩
      h_not := fun hh => c.h_not (by rw [← hhπ, ← hJ']; exact Subgroup.mem_map_of_mem π hh)
      conj_g := isConj_of_mk_isConj O hO hz5 hgo (by rw [hgπ]; exact c.conj_g)
      conj_h := isConj_of_mk_isConj O hO hz5 hho (by rw [hhπ]; exact c.conj_h)
      irr := ?_ }
  ·
    have ha' : π a ∈ J' := by rw [← hJ']; exact Subgroup.mem_map_of_mem π a.2
    have hb' : π b ∈ J' := by rw [← hJ']; exact Subgroup.mem_map_of_mem π b.2
    have hc := congrArg Subtype.val (c.J_abel.1.is_comm.comm (⟨π a, ha'⟩ : J') ⟨π b, hb'⟩)
    refine Subtype.ext (inj _ (P.mul_mem (hJP a.2) (hJP b.2)) _
      (P.mul_mem (hJP b.2) (hJP a.2)) ?_)
    change π (a * b) = π (b * a)
    rw [map_mul, map_mul]
    exact hc
  · have hx' : π x ∈ J' := by rw [← hJ']; exact Subgroup.mem_map_of_mem π hx
    refine inj _ (P.pow_mem (hJP hx) 5) 1 P.one_mem ?_
    rw [map_pow, map_one]
    exact c.J_abel.2 _ hx'
  · rw [← card_map_eq_of_inj π J (fun a ha b hb h => inj a (hJP ha) b (hJP hb) h), hJ']
    exact c.J_card
  · rw [← card_map_eq_of_inj π ⁅J, P⁆ (fun a ha b hb h => inj a (hEP ha) b (hEP hb) h), hEmap]
    exact c.E_card
  · have : π z ∈ (⁅J, P⁆).map π := by rw [hEmap]; exact c.z_mem
    obtain ⟨e, he, heπ⟩ := this
    exact (inj e (hEP he) z hzP heπ) ▸ he
  · intro S hS hidx F hF hinv
    have hN₁ : (P ⊔ conjSub n P).map π = P.map π ⊔ conjSub n' (P.map π) := by
      rw [Subgroup.map_sup, ← hnπ, conjSub_map]
    have hS' : S.map π ≤ P.map π ⊔ conjSub n' (P.map π) := by
      rw [← hN₁]
      exact Subgroup.map_mono hS
    have hidx' : (S.map π).relIndex (P.map π ⊔ conjSub n' (P.map π)) ≤ 5 := by
      rw [← hN₁]
      refine le_trans (Nat.le_of_dvd ?_ (relIndex_map_dvd π S _ hS)) hidx
      exact Nat.pos_of_ne_zero (Subgroup.index_ne_zero_of_finite)
    have hF' : F.map π ≤ ⁅J', P.map π⁆ := by
      rw [← hEmap]
      exact Subgroup.map_mono hF
    have hinv' : ∀ s ∈ S.map π, ∀ f ∈ F.map π, s * f * s⁻¹ ∈ F.map π := by
      rintro _ ⟨s, hs, rfl⟩ _ ⟨f, hf, rfl⟩
      exact ⟨s * f * s⁻¹, hinv s hs f hf, by simp⟩
    rcases c.irr (S.map π) hS' hidx' (F.map π) hF' hinv' with h0 | h0
    · left
      rw [eq_bot_iff]
      intro x hx
      have hxπ : π x ∈ F.map π := Subgroup.mem_map_of_mem π hx
      rw [h0, Subgroup.mem_bot] at hxπ
      exact (Subgroup.mem_bot).mpr
        (inj x (hEP (hF hx)) 1 P.one_mem (by rw [hxπ, map_one]))
    · right
      refine le_antisymm hF (fun e he => ?_)
      have : π e ∈ F.map π := by
        rw [h0, ← hEmap]
        exact Subgroup.mem_map_of_mem π he
      obtain ⟨f, hf, hfπ⟩ := this
      exact (inj f (hEP (hF hf)) e (hEP he) hfπ) ▸ hf

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.KD309L
