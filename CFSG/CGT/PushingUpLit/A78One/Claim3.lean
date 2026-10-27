module

public import CFSG.CGT.PushingUpLit.A78One.OneStmts
import CFSG.CGT.PushingUpLit.A78One.CjLemmas
import CFSG.CGT.PushingUpLit.A78One.Dict
import CFSG.CGT.PushingUpLit.A78One.QEq
import CFSG.CGT.PushingUpLit.A78One.SL2Syl
import CFSG.Timmesfeld.RankOne.Basic

public section

namespace CFSG.CGT.PushingUpLit.A78One

open CFSG CFSG.RankThree.PartOne CFSG.Open CFSG.Quasithin
open CFSG.CGT.PushingUpLit.BHS CFSG.CGT.PushingUpLit.T2K CFSG.Timmesfeld
open scoped commutatorElement

variable {G : Type} [Group G]

theorem mem_normalizer_iff_cj {g : G} {S : Subgroup G} :
    g ∈ Subgroup.normalizer (S : Set G) ↔ cj g S = S :=
  RankOne.map_conj_eq_self_iff.symm

theorem isSylowOf_cj_of_normalizer [Finite G] {S L : Subgroup G}
    (h : CFSG.ABGLocalTools.IsSylowOf 2 S L) {g : G} (hg : g ∈ Subgroup.normalizer (L : Set G)) :
    CFSG.ABGLocalTools.IsSylowOf 2 (cj g S) L := by
  have hL : cj g L = L := mem_normalizer_iff_cj.1 hg
  refine CFSG.ABGLocalTools.isSylowOf_of_card ?_ ?_
  · calc cj g S ≤ cj g L := Subgroup.map_mono h.le
      _ = L := hL
  · rw [Subgroup.card_map_of_injective (MulAut.conj g).injective, h.card_eq]

def sylKer (L H : Subgroup G) : Subgroup G where
  carrier := {h | h ∈ H ∧ ∀ S, CFSG.ABGLocalTools.IsSylowOf 2 S L →
    h ∈ Subgroup.normalizer (S : Set G)}
  one_mem' := ⟨H.one_mem, fun _ _ => Subgroup.one_mem _⟩
  mul_mem' := fun ha hb =>
    ⟨H.mul_mem ha.1 hb.1, fun S hS => Subgroup.mul_mem _ (ha.2 S hS) (hb.2 S hS)⟩
  inv_mem' := fun ha => ⟨H.inv_mem ha.1, fun S hS => Subgroup.inv_mem _ (ha.2 S hS)⟩

theorem conj_mem_sylKer [Finite G] {L H : Subgroup G} (hH : H ≤ Subgroup.normalizer (L : Set G))
    {h k : G} (hh : h ∈ H) (hk : k ∈ sylKer L H) : h * k * h⁻¹ ∈ sylKer L H := by
  refine ⟨H.mul_mem (H.mul_mem hh hk.1) (H.inv_mem hh), fun S hS => ?_⟩
  have hS' := isSylowOf_cj_of_normalizer hS (hH (H.inv_mem hh))
  have hk' := mem_normalizer_iff_cj.1 (hk.2 _ hS')
  rw [mem_normalizer_iff_cj, ← cjx_cj, ← cjx_cj, hk', cjx_cj_inv]

theorem mul_pow_mem_of_pow_eq_one {L : Subgroup G} {t : G}
    (ht : t ∈ Subgroup.normalizer (L : Set G)) {l : G} (hl : l ∈ L) {m : ℕ} (hm : t ^ m = 1) :
    (l * t) ^ m ∈ L := by
  have key : ∀ m : ℕ, ∃ l' ∈ L, (l * t) ^ m = l' * t ^ m := by
    intro m
    induction m with
    | zero => exact ⟨1, L.one_mem, by simp⟩
    | succ m ih =>
      obtain ⟨l', hl', he⟩ := ih
      have hc : t ^ m * l * (t ^ m)⁻¹ ∈ L :=
        (Subgroup.mem_normalizer_iff.1 (Subgroup.pow_mem _ ht m) l).1 hl
      refine ⟨l' * (t ^ m * l * (t ^ m)⁻¹), L.mul_mem hl' hc, ?_⟩
      rw [pow_succ, he, pow_succ]
      group
  obtain ⟨l', hl', he⟩ := key m
  rw [he, hm, mul_one]
  exact hl'

theorem comm_of_mem_cj {A : Subgroup G} (hA : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a) {g u u' : G}
    (hu : u ∈ cj g A) (hu' : u' ∈ cj g A) : u * u' = u' * u := by
  have h := hA _ ((cjx_mem _ _ _).1 hu) _ ((cjx_mem _ _ _).1 hu')
  calc u * u' = g * (g⁻¹ * u * g * (g⁻¹ * u' * g)) * g⁻¹ := by group
    _ = g * (g⁻¹ * u' * g * (g⁻¹ * u * g)) * g⁻¹ := by rw [h]
    _ = u' * u := by group

namespace CexCtx

variable [Finite G] {L M : Subgroup G} {n : ℕ} {T T' : Subgroup G} {x : G}

theorem le_normalizer_T' (c : CexCtx L M n T T' x) : T' ≤ Subgroup.normalizer (L : Set G) :=
  c.le.trans (c.sylow.le.trans c.nM)

theorem H_le_normalizer (c : CexCtx L M n T T' x) : L ⊔ T' ≤ Subgroup.normalizer (L : Set G) :=
  sup_le Subgroup.le_normalizer c.le_normalizer_T'

theorem P_le (c : CexCtx L M n T T' x) : cexP L T ≤ T' := le_sup_right.trans c.ge

theorem isSylowOf_inf (c : CexCtx L M n T T' x) :
    CFSG.ABGLocalTools.IsSylowOf 2 (T' ⊓ L) L :=
  c.sylow_H.inf_of_le_normalizer le_sup_left c.H_le_normalizer

theorem P_le_sylKer (c : CexCtx L M n T T' x) : cexP L T ≤ sylKer L (L ⊔ T') := by
  intro p hp
  refine ⟨c.P_le.trans le_sup_right hp, fun S hS => ?_⟩
  have hO : oTwoIn L ≤ S := le_of_isPGroup_normal hS (oTwoIn_le L) (SixThree.le_normalizer_oTwoIn L)
    (isPGroup_oTwoIn L)
  have hUS : blockU L ≤ S := (blockU_le_oTwoIn L).trans hO
  have key : ∀ q ∈ cexP L T, ∀ s ∈ S, q * s * q⁻¹ ∈ S := by
    intro q hq s hs
    have hqM : q ∈ M ⊓ Subgroup.centralizer (blockU L : Set G) := ⟨c.sylow.le hq.1, hq.2⟩
    have h1 : ⁅q, s⁆ ∈ blockU L :=
      c.hyp.natBlock.comm_centralizer_mem_blockU c.nM hqM s (hS.le hs)
    have e : q * s * q⁻¹ = ⁅q, s⁆ * s := by simp [commutatorElement_def, mul_assoc]
    rw [e]
    exact S.mul_mem (hUS h1) hs
  rw [Subgroup.mem_normalizer_iff]
  intro y
  refine ⟨key p hp y, fun hy => ?_⟩
  have := key p⁻¹ ((cexP L T).inv_mem hp) _ hy
  simpa [mul_assoc] using this

theorem sylKer_le (c : CexCtx L M n T T' x) : sylKer L (L ⊔ T') ≤ cexP L T := by
  have hT'n := c.le_normalizer_T'
  have hKL : ∀ k ∈ sylKer L (L ⊔ T'), k ∈ L → k ∈ oTwoIn L := fun k hk hkL =>
    mem_oTwoIn_of_forall_normalizes c.hyp.natBlock hkL hk.2
  have hK2 : IsPGroup 2 (sylKer L (L ⊔ T')) := by
    intro k
    have hkH : (k : G) ∈ T' ⊔ L := by
      rw [sup_comm T' L]
      exact k.2.1
    obtain ⟨t, ht, l, hl, hk⟩ := (mem_sup_iff_of_le_normalizer hT'n).1 hkH
    obtain ⟨a, ha⟩ := c.sylow.isPGroup ⟨t, c.le ht⟩
    have hta : t ^ 2 ^ a = 1 := by simpa using congrArg Subtype.val ha
    have hl' : t * l * t⁻¹ ∈ L := (Subgroup.mem_normalizer_iff.1 (hT'n ht) l).1 hl
    have hkl : (k : G) = (t * l * t⁻¹) * t := by rw [hk]; group
    have hk1 : (k : G) ^ 2 ^ a ∈ L := by
      rw [hkl]
      exact mul_pow_mem_of_pow_eq_one (hT'n ht) hl' hta
    have hk2 : (k : G) ^ 2 ^ a ∈ oTwoIn L :=
      hKL _ ((sylKer L (L ⊔ T')).pow_mem k.2 _) hk1
    obtain ⟨j, hj⟩ := isPGroup_oTwoIn L ⟨_, hk2⟩
    refine ⟨a + j, Subtype.ext ?_⟩
    have h1 := congrArg Subtype.val hj
    simp only [Subgroup.coe_pow, OneMemClass.coe_one] at h1 ⊢
    rw [pow_add, pow_mul]
    exact h1
  have hKn : L ⊔ T' ≤ Subgroup.normalizer (sylKer L (L ⊔ T') : Set G) := by
    intro h hh
    rw [Subgroup.mem_normalizer_iff]
    intro y
    refine ⟨fun hy => conj_mem_sylKer c.H_le_normalizer hh hy, fun hy => ?_⟩
    have := conj_mem_sylKer c.H_le_normalizer ((L ⊔ T').inv_mem hh) hy
    simpa [mul_assoc] using this
  have hKH : sylKer L (L ⊔ T') ≤ L ⊔ T' := fun _ hk => hk.1
  have := SixThree.le_oTwoIn_of_isPGroup hKH hK2 hKn
  rwa [c.oTwoIn_H] at this

theorem le_sylow (c : CexCtx L M n T T' x) :
    cj x⁻¹ (cexP L T) ≤ T' ⊓ (L ⊔ cexP L T) := by
  have hHn := c.H_le_normalizer
  have hT'n := c.le_normalizer_T'
  have hPT' := c.P_le
  have hQ0 := c.sylow_eq_U1
  have hPK : cexP L T ≤ sylKer L (L ⊔ T') := c.P_le_sylKer
  have hKP : sylKer L (L ⊔ T') ≤ cexP L T := c.sylKer_le
  have hPn : L ⊔ T' ≤ Subgroup.normalizer (cexP L T : Set G) := by
    have := SixThree.le_normalizer_oTwoIn (L ⊔ T')
    rwa [c.oTwoIn_H] at this
  have hUxQ : cj x⁻¹ (blockU L) ≤ T' ⊓ (L ⊔ cexP L T) := hQ0 ▸ le_sup_left
  have hUxT' : cj x⁻¹ (blockU L) ≤ T' := hUxQ.trans inf_le_left
  have hUab : ∀ a ∈ blockU L, ∀ b ∈ blockU L, a * b = b * a :=
    fun a ha b hb => isElemAbelian_comm' c.hyp.natBlock.isElemAbelian_blockU ha hb
  have hS0 : CFSG.ABGLocalTools.IsSylowOf 2 (T' ⊓ L) L := c.isSylowOf_inf
  have hcjS0 : ∀ y ∈ T', cj y (T' ⊓ L) = T' ⊓ L := by
    intro y hy
    have h1 : cj y T' = T' := mem_normalizer_iff_cj.1 (Subgroup.le_normalizer hy)
    have h2 : cj y L = L := mem_normalizer_iff_cj.1 (hT'n hy)
    rw [cjx_inf, h1, h2]
  have hact : ∀ s ∈ T' ⊓ L, ∃ u ∈ cj x⁻¹ (blockU L),
      ∀ S, CFSG.ABGLocalTools.IsSylowOf 2 S L → cj s S = cj u S := by
    intro s hs
    have hsQ : s ∈ T' ⊓ (L ⊔ cexP L T) := ⟨hs.1, Subgroup.mem_sup_left hs.2⟩
    rw [hQ0] at hsQ
    obtain ⟨u, hu, p, hp, hsup⟩ := (mem_sup_iff_of_le_normalizer
      (fun u hu => hPn (Subgroup.mem_sup_right (hUxT' hu)))).1 hsQ
    refine ⟨u, hu, fun S hS => ?_⟩
    rw [hsup, ← cjx_cj, mem_normalizer_iff_cj.1 ((hPK hp).2 S hS)]
  intro t ht
  have ht' : x * t * x⁻¹ ∈ cexP L T := by simpa using (cjx_mem _ _ _).1 ht
  have htT' : t ∈ T' := ((Subgroup.mem_normalizer_iff.1 c.hx) t).2 (hPT' ht')
  have htH : t ∈ L ⊔ T' := Subgroup.mem_sup_right htT'
  have htcomm : ∀ u ∈ cj x⁻¹ (blockU L), t * u = u * t := by
    intro u hu
    have hu' : x * u * x⁻¹ ∈ blockU L := by simpa using (cjx_mem _ _ _).1 hu
    have hC := Subgroup.mem_centralizer_iff.1 ht'.2 _ hu'
    calc t * u = x⁻¹ * ((x * t * x⁻¹) * (x * u * x⁻¹)) * x := by group
      _ = x⁻¹ * ((x * u * x⁻¹) * (x * t * x⁻¹)) * x := by rw [hC]
      _ = u * t := by group
  have key : ∃ r ∈ cj x⁻¹ (blockU L), ∀ S, CFSG.ABGLocalTools.IsSylowOf 2 S L →
      cj t S = cj r S := by
    by_cases hex : ∃ S₁, CFSG.ABGLocalTools.IsSylowOf 2 S₁ L ∧ S₁ ≠ T' ⊓ L
    · obtain ⟨S₁, hS₁, hne⟩ := hex
      have hS₂ : CFSG.ABGLocalTools.IsSylowOf 2 (cj t S₁) L :=
        isSylowOf_cj_of_normalizer hS₁ (hHn htH)
      have hne₂ : cj t S₁ ≠ T' ⊓ L := by
        intro h
        exact hne (RankOne.map_conj_inj.1 (h.trans (hcjS0 t htT').symm))
      obtain ⟨s, hs, hsS⟩ :=
        exists_cj_eq_of_isSylowOf c.hyp.natBlock hS0 hS₁ hS₂ hne hne₂
      obtain ⟨r, hr, hrS⟩ := hact s hs
      refine ⟨r, hr, fun S hS => ?_⟩
      by_cases hS0' : S = T' ⊓ L
      · rw [hS0', hcjS0 t htT', hcjS0 r (hUxT' hr)]
      · obtain ⟨s', hs', hs'S⟩ := exists_cj_eq_of_isSylowOf c.hyp.natBlock hS0 hS₁ hS hne hS0'
        obtain ⟨u', hu', hu'S⟩ := hact s' hs'
        have e1 : S = cj u' S₁ := by rw [← hs'S]; exact hu'S S₁ hS₁
        have e2 : cj t S₁ = cj r S₁ := by rw [← hsS]; exact hrS S₁ hS₁
        have hc1 : t * u' = u' * t := htcomm u' hu'
        have hc2 : r * u' = u' * r :=
          comm_of_mem_cj hUab hr hu'
        calc cj t S = cj t (cj u' S₁) := by rw [← e1]
          _ = cj (t * u') S₁ := cjx_cj _ _ _
          _ = cj (u' * t) S₁ := by rw [hc1]
          _ = cj u' (cj t S₁) := (cjx_cj _ _ _).symm
          _ = cj u' (cj r S₁) := by rw [e2]
          _ = cj (u' * r) S₁ := cjx_cj _ _ _
          _ = cj (r * u') S₁ := by rw [hc2]
          _ = cj r (cj u' S₁) := (cjx_cj _ _ _).symm
          _ = cj r S := by rw [← e1]
    · simp only [not_exists, not_and, not_not] at hex
      refine ⟨1, Subgroup.one_mem _, fun S hS => ?_⟩
      rw [hex S hS, hcjS0 t htT', cjx_one]
  obtain ⟨r, hr, hrt⟩ := key
  have hrH : r⁻¹ ∈ L ⊔ T' := (L ⊔ T').inv_mem (Subgroup.mem_sup_right (hUxT' hr))
  have htr : t * r⁻¹ ∈ sylKer L (L ⊔ T') := by
    refine ⟨(L ⊔ T').mul_mem htH hrH, fun S hS => ?_⟩
    have hS' := isSylowOf_cj_of_normalizer hS (hHn hrH)
    rw [mem_normalizer_iff_cj, ← cjx_cj, hrt _ hS', cjx_cj_inv]
  have htr' : t * r⁻¹ ∈ cexP L T := hKP htr
  have hrQ : r ∈ T' ⊓ (L ⊔ cexP L T) := hUxQ hr
  have e : t = (t * r⁻¹) * r := by group
  rw [e]
  exact (T' ⊓ (L ⊔ cexP L T)).mul_mem ⟨hPT' htr', Subgroup.mem_sup_right htr'⟩ hrQ

end CexCtx

end CFSG.CGT.PushingUpLit.A78One
