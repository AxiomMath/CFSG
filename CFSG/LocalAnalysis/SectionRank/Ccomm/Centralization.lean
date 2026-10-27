module

public import CFSG.LocalAnalysis.SectionRank.Ccomm.RankTwo
public import CFSG.LocalAnalysis.SectionRank.Ccomm.PrimeLinear
public import CFSG.LocalAnalysis.SectionRank.Ccomm.Supercritical

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.SectionRank.Ccomm

open Subgroup CFSG.Open CFSG.SectionRank
open scoped commutatorElement

theorem GL_comm_of_le_one {R : Type*} [CommRing R] {n : ℕ} (hn : n ≤ 1) (a b : GL (Fin n) R) :
    a * b = b * a := by
  interval_cases n
  · apply Units.ext
    ext i
    exact Fin.elim0 i
  · exact GL_one_comm a b

theorem perfect_hom_eq_one_of_range_comm {G H : Type*} [Group G] [Group.IsPerfect G] [Group H]
    (f : G →* H) (hcomm : ∀ a ∈ f.range, ∀ b ∈ f.range, a * b = b * a) : f = 1 := by
  have : IsMulCommutative f.range := ⟨⟨fun a b => Subtype.ext (hcomm _ a.2 _ b.2)⟩⟩
  have : Group.IsPerfect f.range := Group.IsPerfect.range f
  have : Subsingleton f.range := Group.IsPerfect.subsingleton_of_isMulCommutative
  ext g
  have := Subsingleton.elim (⟨f g, g, rfl⟩ : f.range) 1
  exact congrArg Subtype.val this

theorem pgroup_le_center_of_perfect
    {X : Type*} [Group X] [Finite X] [Group.IsPerfect X]
    (C : Subgroup X) [C.Normal] (hodd : Odd (Nat.card C))
    (hquot : ∀ (N : Subgroup (X ⧸ C)) [N.Normal], center ((X ⧸ C) ⧸ N) = ⊥)
    {r : ℕ} [hr : Fact r.Prime] (Q : Subgroup X) [Q.Normal] (hQC : Q ≤ C)
    (hQ : IsPGroup r Q) (hrank : pRank r Q ≤ 2) : Q ≤ center X := by
  by_cases hQbot : Q = ⊥
  · rw [hQbot]
    exact bot_le
  have hQnt : Nontrivial Q := (nontrivial_iff_ne_bot Q).2 hQbot
  have hr2 : r ≠ 2 := by
    rintro rfl
    obtain ⟨n, hn0, hn⟩ := hQ.nontrivial_iff_card.1 hQnt
    have h2 : 2 ∣ Nat.card Q := hn ▸ dvd_pow_self 2 hn0.ne'
    have h2C : 2 ∣ Nat.card C := h2.trans (card_dvd_of_le hQC)
    exact (Nat.not_even_iff_odd.2 hodd) (even_iff_two_dvd.2 h2C)
  set α : X →* MulAut Q := MulAut.conjNormal with hα
  suffices hα1 : α = 1 by
    intro q hq
    rw [mem_center_iff]
    intro g
    have h := congrArg (fun φ : MulAut Q => ((φ ⟨q, hq⟩ : Q) : X)) (congrArg (· g) hα1)
    simp only [hα, MulAut.conjNormal_apply, MonoidHom.one_apply, MulAut.one_apply] at h
    calc g * q = g * q * g⁻¹ * g := by group
      _ = q * g := by rw [h]
  by_contra hα1
  obtain ⟨D, hDc, -, hDexp, -, -, hker⟩ := supercritical_witness hr2 hQ
  set W := D ⧸ frattini D
  set ρ : X →* MulAut W := (frattiniAction D).comp α with hρ
  have hDp : IsPGroup r D := hQ.to_subgroup D
  obtain ⟨-, hWcomm, hWpow⟩ := frattini_quotient_elementary hDp
  have hρ1 : ρ ≠ 1 := by
    intro hρ1
    apply hα1
    have hle : α.range ≤ (frattiniAction D).ker := by
      rintro _ ⟨x, rfl⟩
      rw [MonoidHom.mem_ker]
      exact congrArg (· x) hρ1
    have hpg : IsPGroup r α.range := hker.to_le hle
    have : Group.IsPerfect α.range := Group.IsPerfect.range α
    have : Group.IsNilpotent α.range := hpg.isNilpotent
    by_contra hne
    have : Nontrivial α.range := by
      rw [nontrivial_iff_ne_bot]
      intro hbot
      apply hne
      ext x
      have : α x ∈ α.range := ⟨x, rfl⟩
      rw [hbot, mem_bot] at this
      rw [this]
      rfl
    exact Group.IsPerfect.not_isNilpotent α.range hpg.isNilpotent
  have hDrank : pRank r (⊤ : Subgroup D) ≤ 2 := by
    let f : D →* X := Q.subtype.comp D.subtype
    have hf : Function.Injective f := Q.subtype_injective.comp D.subtype_injective
    refine (pRank_le_map hr.out.one_lt f hf ⊤).trans ((pRank_mono hr.out.one_lt ?_).trans hrank)
    rintro _ ⟨d, -, rfl⟩
    exact (d : Q).2
  obtain ⟨-, hW2⟩ := rank_two_exponent_prime_order_bound hDp
    (fun x => Subtype.ext (by rw [SubgroupClass.coe_pow, OneMemClass.coe_one]; exact hDexp _ x.2))
    hDrank
  obtain ⟨k, hk⟩ := (hDp.to_quotient (frattini D)).exists_card_eq
  have hk2 : k ≤ 2 := (Nat.pow_le_pow_iff_right hr.out.one_lt).1 (hk ▸ hW2)
  obtain ⟨e⟩ := nonempty_mulEquiv_of_elementary hWcomm hWpow hk
  set ψ := elemAutEquivGL e with hψ
  have hk2' : k = 2 := by
    by_contra hk2'
    apply hρ1
    apply perfect_hom_eq_one_of_range_comm
    intro a _ b _
    apply ψ.injective
    rw [map_mul, map_mul]
    exact GL_comm_of_le_one (by omega) _ _
  subst hk2'
  set J := ρ.range.map ψ.toMonoidHom with hJ
  have : Group.IsPerfect ρ.range := Group.IsPerfect.range ρ
  have : Group.IsPerfect J := Group.IsPerfect.map _
  have hJne : J ≠ ⊥ := by
    intro hbot
    apply hρ1
    ext x
    have h1 : ψ (ρ x) ∈ J := mem_map_of_mem _ ⟨x, rfl⟩
    rw [hbot, mem_bot] at h1
    have h2 : ρ x = 1 := by rw [← map_one ψ] at h1; exact ψ.injective h1
    rw [h2]
    rfl
  obtain ⟨_, ⟨x, rfl⟩, hx⟩ := mem_map.1 (neg_one_mem_of_perfect hr2 J hJne)
  have hxinv : ∀ w : W, ρ x w = w⁻¹ := (elemAutEquivGL_eq_neg_one_iff e (ρ x)).1 hx
  have hcentral : ∀ φ : MulAut W, ρ x * φ = φ * ρ x := by
    intro φ
    ext w
    rw [MulAut.mul_apply, MulAut.mul_apply, hxinv, hxinv, map_inv]
  have hρx2 : ρ x ^ 2 = 1 := by
    ext w
    rw [sq, MulAut.mul_apply, hxinv, hxinv, inv_inv, MulAut.one_apply]
  have hWnt : Nontrivial W := Finite.one_lt_card_iff_nontrivial.1 (by
    rw [hk]
    exact Nat.one_lt_pow two_ne_zero hr.out.one_lt)
  have hρx1 : ρ x ≠ 1 := by
    intro h1
    obtain ⟨w, hw⟩ := exists_ne (1 : W)
    have hww : w⁻¹ = w := by rw [← hxinv, h1, MulAut.one_apply]
    have hw2 : w ^ 2 = 1 := by
      rw [sq]
      calc w * w = w⁻¹ * w := by rw [hww]
        _ = 1 := inv_mul_cancel w
    have hord : orderOf w ∣ Nat.gcd 2 r :=
      Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one hw2) (orderOf_dvd_of_pow_eq_one (hWpow w))
    rw [(Nat.coprime_primes Nat.prime_two hr.out).2 (Ne.symm hr2), Nat.dvd_one,
      orderOf_eq_one_iff] at hord
    exact hw hord
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hρxord : orderOf (ρ x) = 2 := orderOf_eq_prime hρx2 hρx1
  set M := ρ.ker ⊔ C with hM
  set N := M.map (QuotientGroup.mk' C) with hN
  have hNn : N.Normal := Normal.map inferInstance _ (QuotientGroup.mk'_surjective C)
  have hZ := hquot N
  have hz : (((x : X ⧸ C)) : (X ⧸ C) ⧸ N) ∈ center ((X ⧸ C) ⧸ N) := by
    rw [mk_mem_center_iff]
    intro y
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective y
    have h1 : ⁅(x : X ⧸ C), (y : X ⧸ C)⁆ = QuotientGroup.mk' C ⁅x, y⁆ :=
      (map_commutatorElement (QuotientGroup.mk' C) x y).symm
    rw [h1]
    refine mem_map_of_mem _ (mem_sup_left ?_)
    rw [MonoidHom.mem_ker, map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
    exact hcentral (ρ y)
  rw [hZ, mem_bot, QuotientGroup.eq_one_iff] at hz
  obtain ⟨m, hm, hmx⟩ := mem_map.1 hz
  have hxM : x ∈ M := by
    have h1 : m⁻¹ * x ∈ C := QuotientGroup.eq.1 hmx
    have h2 : x = m * (m⁻¹ * x) := by group
    rw [h2]
    exact mul_mem hm (mem_sup_right h1)
  have hMρ : M.map ρ = C.map ρ := by
    rw [hM, Subgroup.map_sup, (Subgroup.map_eq_bot_iff _).2 le_rfl, bot_sup_eq]
  have hρxC : ρ x ∈ C.map ρ := hMρ ▸ mem_map_of_mem ρ hxM
  have h2dvd : 2 ∣ Nat.card C :=
    (hρxord ▸ orderOf_dvd_natCard _ hρxC).trans (card_map_dvd C ρ)
  exact (Nat.not_even_iff_odd.2 hodd) (even_iff_two_dvd.2 h2dvd)

theorem odd_nilpotent_kernel_centralization
    {X : Type*} [Group X] [Finite X]
    (hX : Group.IsPerfect X) (C : Subgroup X) [C.Normal] (hC : Group.IsNilpotent C)
    (hodd : Odd (Nat.card C))
    (hquot : ∀ (N : Subgroup (X ⧸ C)) [N.Normal], center ((X ⧸ C) ⧸ N) = ⊥)
    (hrank : ∀ r : ℕ, r.Prime → r ∣ Nat.card C → pRank r C ≤ 2) :
    C ≤ center X := by
  have hsyl : ∀ (r : ℕ) [Fact r.Prime] (P : Sylow r C),
      (P : Subgroup C).map C.subtype ≤ center X := by
    intro r hr P
    by_cases hrC : r ∣ Nat.card C
    · have : (P : Subgroup C).Characteristic := Sylow.characteristic_of_normal P inferInstance
      have : ((P : Subgroup C).map C.subtype).Normal :=
        ConjAct.normal_of_characteristic_of_normal
      refine pgroup_le_center_of_perfect C hodd hquot _ (map_subtype_le _)
        (P.isPGroup'.map C.subtype) ?_
      exact (pRank_mono hr.out.one_lt (map_subtype_le _)).trans (hrank r hr.out hrC)
    ·
      have hP1 : Nat.card P = 1 := by
        obtain ⟨n, hn⟩ := P.isPGroup'.exists_card_eq
        have hdvd := P.card_subgroup_dvd_card
        rw [hn] at hdvd ⊢
        cases n with
        | zero => rfl
        | succ n => exact absurd ((dvd_pow_self r n.succ_ne_zero).trans hdvd) hrC
      rw [card_eq_one] at hP1
      rw [hP1, Subgroup.map_bot]
      exact bot_le
  set K := (center X).subgroupOf C with hK
  have hKtop : K = ⊤ := by
    rw [← index_eq_one, Nat.eq_one_iff_not_exists_prime_dvd]
    intro r hr hdvd
    have : Fact r.Prime := ⟨hr⟩
    obtain ⟨P⟩ : Nonempty (Sylow r C) := inferInstance
    have hPK : (P : Subgroup C) ≤ K := fun g hg =>
      hsyl r P (mem_map_of_mem C.subtype hg)
    exact P.not_dvd_index (hdvd.trans (index_dvd_of_le hPK))
  intro g hg
  have : (⟨g, hg⟩ : C) ∈ K := hKtop ▸ mem_top _
  exact this

end CFSG.SectionRank.Ccomm
