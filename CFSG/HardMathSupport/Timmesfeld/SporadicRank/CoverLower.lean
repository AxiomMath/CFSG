module

public import CFSG.LocalAnalysis.AGLEmbedding.CoverModule
public import CFSG.LocalAnalysis.SectionRank.PRank
public import CFSG.LocalAnalysis.AGLEmbedding.KFacts

public section

namespace CFSG.HardMathSupport.Timmesfeld.SporadicRank

open CFSG.AGLEmbedding CFSG.Open CFSG.SectionRank

theorem succ_le_pRank_of_moduleSpec {K X : Type} [Group K] [Finite K] [Group X] {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (D : ModuleSpec X p) (hA : D.NoAlt) (hF : D.NoFun)
    (π : K →* X) (hπ : Function.Surjective π) (hker : π.ker = Subgroup.center K)
    (hZ1 : Subgroup.center K ≠ ⊥) (hZp : IsPGroup p (Subgroup.center K))
    (hZc : IsCyclic (Subgroup.center K)) : D.n + 1 ≤ CFSG.Open.pRank p (⊤ : Subgroup K) := by
  have := Fact.mk hp
  have hcomm := D.commute_of_noAlt π hp hp2 hπ hker hZp hZc hA
  have hcard := D.pow_succ_le_card_omegaOf π hp hp2 hπ hker hZ1 hZp hZc hcomm hF
  have hE := isElemAbelian_omegaOf (H := D.span.comap π) (hH := hcomm) (p := p)
  have hpg : IsPGroup p (omegaOf (D.span.comap π) hcomm p) := fun g => ⟨1, by
    rw [pow_one]; exact Subtype.ext g.2.2⟩
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hpg
  refine le_trans ?_ (le_pRank hp.one_lt (le_top : omegaOf (D.span.comap π) hcomm p ≤ ⊤) hE hk)
  rw [hk] at hcard
  exact (Nat.pow_le_pow_iff_right hp.one_lt).1 hcard

theorem center_quotient_center_eq_bot {L : Type} [Group L] (hq : CFSG.Open.IsQuasisimple L) :
    Subgroup.center (L ⧸ Subgroup.center L) = ⊥ := by
  have : IsSimpleGroup (L ⧸ Subgroup.center L) := hq.2
  have : Group.IsPerfect L := ⟨hq.1⟩
  rcases (Subgroup.center (L ⧸ Subgroup.center L)).normal_of_characteristic.eq_bot_or_eq_top
    with h | h
  · exact h
  · exfalso
    have hc : IsMulCommutative (L ⧸ Subgroup.center L) := ⟨⟨fun a b =>
      (Subgroup.mem_center_iff.mp (h ▸ Subgroup.mem_top b : b ∈ _)) a⟩⟩
    exact Group.IsPerfect.not_isMulCommutative (L ⧸ Subgroup.center L) hc

@[expose] def centralTwoTorsion (L : Type) [Group L] : Subgroup L where
  carrier := {x | x ∈ Subgroup.center L ∧ x ^ 2 = 1}
  mul_mem' := fun {a b} ha hb => ⟨mul_mem ha.1 hb.1, by
    rw [(show Commute a b from Subgroup.mem_center_iff.mp hb.1 a).mul_pow, ha.2, hb.2, one_mul]⟩
  one_mem' := ⟨one_mem _, one_pow 2⟩
  inv_mem' := fun {a} ha => ⟨inv_mem ha.1, by rw [inv_pow, ha.2, inv_one]⟩

theorem centralTwoTorsion_le_center (L : Type) [Group L] :
    centralTwoTorsion L ≤ Subgroup.center L := fun _ hx => hx.1

instance (L : Type) [Group L] : (centralTwoTorsion L).Normal :=
  Subgroup.normal_of_le_center (centralTwoTorsion_le_center L)

theorem lower_of_cover {L : Type} [Group L] [Finite L] (hq : CFSG.Open.IsQuasisimple L) {X : Type}
    [Group X] (e : L ⧸ Subgroup.center L ≃* X) (hZ6 : Nat.card (Subgroup.center L) ∣ 6)
    (h3 : 3 ∣ Nat.card (Subgroup.center L)) (D : ModuleSpec X 3) (hA : D.NoAlt) (hF : D.NoFun) :
    D.n + 1 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup L) := by
  classical
  have hp3 : Nat.Prime 3 := Nat.prime_three
  have : Fact (Nat.Prime 3) := ⟨hp3⟩
  set N := centralTwoTorsion L with hNdef
  let f : L →* X := (e : L ⧸ Subgroup.center L →* X).comp (QuotientGroup.mk' (Subgroup.center L))
  have hNf : N ≤ f.ker := by
    intro x hx
    rw [MonoidHom.mem_ker]
    simp only [f, MonoidHom.comp_apply, QuotientGroup.mk'_apply]
    rw [(QuotientGroup.eq_one_iff x).mpr hx.1, map_one]
  let π : L ⧸ N →* X := QuotientGroup.lift N f hNf
  have hπmk : ∀ l : L, π (QuotientGroup.mk l) = e (QuotientGroup.mk l) := fun l => rfl
  have hπ : Function.Surjective π := by
    intro x
    obtain ⟨q, rfl⟩ := e.surjective x
    obtain ⟨l, rfl⟩ := QuotientGroup.mk_surjective q
    exact ⟨QuotientGroup.mk l, hπmk l⟩
  have hXc : Subgroup.center X = ⊥ := by
    have h0 := center_quotient_center_eq_bot hq
    rw [eq_bot_iff]
    intro x hx
    have : e.symm x ∈ Subgroup.center (L ⧸ Subgroup.center L) := by
      rw [Subgroup.mem_center_iff] at hx ⊢
      intro g
      apply e.injective
      rw [map_mul, map_mul, MulEquiv.apply_symm_apply]
      exact hx (e g)
    rw [h0, Subgroup.mem_bot] at this
    rw [Subgroup.mem_bot]
    simpa using congrArg e this
  have hmem : ∀ l : L, π (QuotientGroup.mk l) = 1 ↔ l ∈ Subgroup.center L := by
    intro l
    rw [hπmk, ← QuotientGroup.eq_one_iff (N := Subgroup.center L) l]
    constructor
    · intro h
      simpa using h
    · intro h
      simpa using congrArg e h
  have hker : π.ker = Subgroup.center (L ⧸ N) := by
    ext k
    obtain ⟨l, rfl⟩ := QuotientGroup.mk_surjective k
    rw [MonoidHom.mem_ker, hmem]
    constructor
    · intro hl
      rw [Subgroup.mem_center_iff]
      intro g
      obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective g
      rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, Subgroup.mem_center_iff.mp hl g]
    · intro h
      have hc : π (QuotientGroup.mk l) ∈ Subgroup.center X := by
        rw [Subgroup.mem_center_iff]
        intro x
        obtain ⟨g, rfl⟩ := hπ x
        rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.mp h g]
      rw [hXc, Subgroup.mem_bot] at hc
      exact (hmem l).1 hc
  have hkerMap : π.ker = (Subgroup.center L).map (QuotientGroup.mk' N) := by
    ext k
    obtain ⟨l, rfl⟩ := QuotientGroup.mk_surjective k
    rw [MonoidHom.mem_ker, hmem, Subgroup.mem_map]
    constructor
    · intro hl
      exact ⟨l, hl, rfl⟩
    · rintro ⟨l', hl', h⟩
      rw [← hmem]
      have : QuotientGroup.mk l = (QuotientGroup.mk l' : L ⧸ N) := h.symm
      rw [this, hmem]
      exact hl'
  have hpow6 : ∀ l ∈ Subgroup.center L, l ^ 6 = 1 := by
    intro l hl
    have h1 : (⟨l, hl⟩ : Subgroup.center L) ^ Nat.card (Subgroup.center L) = 1 :=
      pow_card_eq_one'
    obtain ⟨c, hc⟩ := hZ6
    have h2 : l ^ Nat.card (Subgroup.center L) = 1 := congrArg Subtype.val h1
    rw [hc, pow_mul, h2, one_pow]
  have hcube : ∀ k ∈ π.ker, k ^ 3 = 1 := by
    intro k hk
    rw [hkerMap] at hk
    obtain ⟨l, hl, rfl⟩ := Subgroup.mem_map.mp hk
    show (QuotientGroup.mk l : L ⧸ N) ^ 3 = 1
    rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]
    refine ⟨pow_mem hl 3, ?_⟩
    rw [← pow_mul]
    exact hpow6 l hl
  obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' (G := Subgroup.center L) 3 h3
  have hzord : orderOf (z : L) = 3 := (Subgroup.orderOf_coe z).trans hz
  have hz1 : (QuotientGroup.mk (z : L) : L ⧸ N) ≠ 1 := by
    rw [Ne, QuotientGroup.eq_one_iff]
    intro h
    have := orderOf_dvd_of_pow_eq_one h.2
    rw [hzord] at this
    omega
  have hzK : (QuotientGroup.mk (z : L) : L ⧸ N) ∈ Subgroup.center (L ⧸ N) := by
    rw [← hker, MonoidHom.mem_ker, hmem]
    exact z.2
  have hZ1 : Subgroup.center (L ⧸ N) ≠ ⊥ := fun h => hz1 (by
    rw [h] at hzK
    exact Subgroup.mem_bot.mp hzK)
  have hZp : IsPGroup 3 (Subgroup.center (L ⧸ N)) := fun g => ⟨1, by
    rw [pow_one]
    exact Subtype.ext (hcube g.1 (by rw [hker]; exact g.2))⟩
  have hZcard : Nat.card (Subgroup.center (L ⧸ N)) = 3 := by
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hZp
    have hdvd : Nat.card (Subgroup.center (L ⧸ N)) ∣ 6 := by
      rw [← hker, hkerMap]
      exact (Subgroup.card_map_dvd (Subgroup.center L) (QuotientGroup.mk' N)).trans hZ6
    have hk1 : k ≠ 0 := by
      rintro rfl
      exact hZ1 (Subgroup.card_eq_one.mp (by simpa using hk))
    have hk2 : k < 2 := by
      by_contra hk2
      have : 3 ^ 2 ∣ 6 := (pow_dvd_pow 3 (not_lt.mp hk2)).trans (hk ▸ hdvd)
      omega
    have : k = 1 := by omega
    rw [hk, this, pow_one]
  have hZc : IsCyclic (Subgroup.center (L ⧸ N)) :=
    have : Fact (Nat.card (Subgroup.center (L ⧸ N))).Prime := ⟨hZcard ▸ hp3⟩
    isCyclic_of_prime_card hZcard
  have hlow := succ_le_pRank_of_moduleSpec hp3 (by norm_num) D hA hF π hπ hker hZ1 hZp hZc
  have hN2 : ¬ 3 ∣ Nat.card N := by
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have hNp : IsPGroup 2 N := fun g => ⟨1, by
      rw [pow_one]
      exact Subtype.ext g.2.2⟩
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hNp
    rw [hk]
    intro h
    have := Nat.Prime.dvd_of_dvd_pow hp3 h
    omega
  rw [← pRank_quotient_eq (p := 3) N hN2]
  exact hlow

end CFSG.HardMathSupport.Timmesfeld.SporadicRank
