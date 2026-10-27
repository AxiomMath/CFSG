module

public import CFSG.GH74.GLS.Balance.Bender.Stmts
public import CFSG.GH74.GLS.Balance.PStarLayer

public section

namespace CFSG.GH74.GLS.Balance.BenderExt

open Subgroup CFSG CFSG.GH74.GLS
open scoped commutatorElement

section Residual

variable {Y : Type*} [Group Y] {p : ℕ}

theorem mem_oResidual_of_coprime {y : Y} (hy : Nat.Coprime (orderOf y) p) :
    y ∈ oResidual p Y := Subgroup.subset_closure hy

theorem oResidual_le_of_pow_mem [Finite Y] {K : Subgroup Y}
    (hK : ∀ y : Y, ∃ k : ℕ, y ^ (p ^ k) ∈ K) : oResidual p Y ≤ K := by
  unfold oResidual
  rw [Subgroup.closure_le]
  intro y hy
  obtain ⟨k, hk⟩ := hK y
  have hy' : Nat.Coprime (orderOf y) p := hy
  have hcop : Nat.Coprime (p ^ k) (orderOf y) := (hy'.pow_right k).symm
  rcases Nat.lt_or_ge 1 (orderOf y) with h1 | h1
  · obtain ⟨m, -, hm⟩ := Nat.exists_mul_mod_eq_one_of_coprime hcop h1
    have : y = (y ^ (p ^ k)) ^ m := by
      rw [← pow_mul, ← pow_mod_orderOf, hm, pow_one]
    show y ∈ K
    rw [this]; exact K.pow_mem hk m
  · have h0 : orderOf y = 1 := le_antisymm h1 (orderOf_pos y)
    have : y = 1 := orderOf_eq_one_iff.mp h0
    rw [this]; exact K.one_mem

theorem coprime_orderOf_of_coprime_card [Finite Y] (hp : Nat.Coprime p (Nat.card Y)) (y : Y) :
    Nat.Coprime (orderOf y) p :=
  (Nat.Coprime.coprime_dvd_left (orderOf_dvd_natCard y) hp.symm)

theorem oResidual_eq_top_of_coprime [Finite Y] (hp : Nat.Coprime p (Nat.card Y)) :
    oResidual p Y = ⊤ :=
  eq_top_iff.mpr fun y _ => mem_oResidual_of_coprime (coprime_orderOf_of_coprime_card hp y)

variable {A B : Type*} [Group A] [Group B]

theorem exists_coprime_lift [Finite A] (hp : p.Prime) (f : A →* B) {b : B}
    (hb : Nat.Coprime (orderOf b) p) {a₀ : A} (ha₀ : f a₀ = b) :
    ∃ a : A, f a = b ∧ Nat.Coprime (orderOf a) p := by
  have hn : orderOf a₀ ≠ 0 := (orderOf_pos a₀).ne'
  obtain ⟨e, m, hm, hnm⟩ := Nat.exists_eq_pow_mul_and_not_dvd hn p hp.ne_one
  have hbm : orderOf b ∣ m := by
    have h1 : orderOf b ∣ p ^ e * m := by
      rw [← hnm, ← ha₀]; exact orderOf_map_dvd f a₀
    exact (Nat.Coprime.pow_right e hb).dvd_of_dvd_mul_left h1
  have hm0 : m ≠ 0 := by
    rintro rfl; rw [mul_zero] at hnm; exact hn hnm
  rcases Nat.lt_or_ge 1 m with hm1 | hm1
  · have hcop : Nat.Coprime (p ^ e) m :=
      Nat.Coprime.pow_left e ((Nat.Prime.coprime_iff_not_dvd hp).2 hm)
    obtain ⟨t, -, ht⟩ := Nat.exists_mul_mod_eq_one_of_coprime hcop hm1
    have hmod : p ^ e * t ≡ 1 [MOD m] := by
      unfold Nat.ModEq; rw [ht, Nat.mod_eq_of_lt hm1]
    refine ⟨a₀ ^ (p ^ e * t), ?_, ?_⟩
    · rw [map_pow, ha₀]
      have h2 : b ^ (p ^ e * t) = b ^ 1 := pow_eq_pow_iff_modEq.mpr (Nat.ModEq.of_dvd hbm hmod)
      rw [h2, pow_one]
    · have hdvd : orderOf (a₀ ^ (p ^ e * t)) ∣ m := by
        apply orderOf_dvd_of_pow_eq_one
        calc (a₀ ^ (p ^ e * t)) ^ m = (a₀ ^ (p ^ e * m)) ^ t := by
              rw [← pow_mul, ← pow_mul]; congr 1; ring
          _ = 1 := by rw [← hnm, pow_orderOf_eq_one, one_pow]
      exact Nat.Coprime.coprime_dvd_left hdvd ((Nat.Prime.coprime_iff_not_dvd hp).2 hm).symm
  · have hm1' : m = 1 := by omega
    have hb1 : orderOf b = 1 := by
      have := Nat.dvd_one.mp (hm1' ▸ hbm); exact this
    have : b = 1 := orderOf_eq_one_iff.mp hb1
    refine ⟨1, by rw [map_one, this], by simp⟩

theorem map_oResidual [Finite A] (hp : p.Prime) (f : A →* B) (hf : Function.Surjective f) :
    (oResidual p A).map f = oResidual p B := by
  apply le_antisymm
  · rw [Subgroup.map_le_iff_le_comap]
    unfold oResidual
    rw [Subgroup.closure_le]
    intro a ha
    show f a ∈ oResidual p B
    exact mem_oResidual_of_coprime (Nat.Coprime.coprime_dvd_left (orderOf_map_dvd f a) ha)
  · unfold oResidual
    rw [Subgroup.closure_le]
    intro b hb
    obtain ⟨a₀, rfl⟩ := hf b
    obtain ⟨a, ha, hca⟩ := exists_coprime_lift hp f hb rfl
    exact ⟨a, Subgroup.subset_closure hca, ha⟩

end Residual

section TForm

variable {p : ℕ} [Fact p.Prime]

omit [Fact p.Prime] in
theorem isPStar_iff_T {Y : Type*} [Group Y] :
    IsPStar p Y ↔ oResidual p Y = ⊤ ∧ ∀ N : Subgroup Y, N.Normal → ∀ T : Subgroup Y, T ≤ N →
      IsPGroup p ↥T → N ⊔ centralizer (T : Set Y) = ⊤ := by
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨h1, fun N hN T hTN hT => ?_⟩
    have hT' : IsPGroup p (T.subgroupOf N) := hT.comap_subtype
    obtain ⟨P, hP⟩ := hT'.exists_le_sylow
    have htop := h2 N hN P
    rw [eq_top_iff] at htop ⊢
    refine htop.trans (sup_le_sup_left (Subgroup.centralizer_le ?_) N)
    intro t ht
    exact ⟨⟨t, hTN ht⟩, hP ht, rfl⟩
  · rintro ⟨h1, h2⟩
    exact ⟨h1, fun N hN P => h2 N hN _ (Subgroup.map_subtype_le _) (P.isPGroup'.map N.subtype)⟩

variable {A B : Type*} [Group A] [Group B]

theorem IsPStar.of_surjective [Finite A] (f : A →* B) (hf : Function.Surjective f)
    (h : IsPStar p A) : IsPStar p B := by
  rw [isPStar_iff_T] at h ⊢
  obtain ⟨h1, h2⟩ := h
  have hp : p.Prime := Fact.out
  have : Finite B := Finite.of_surjective f hf
  refine ⟨?_, fun N' hN' T' hT'N' hT' => ?_⟩
  · rw [← map_oResidual hp f hf, h1, Subgroup.map_top_of_surjective f hf]
  · obtain ⟨Q', hQ'⟩ := hT'.exists_le_sylow
    obtain ⟨Q, rfl⟩ := Sylow.mapSurjective_surjective hf p Q'
    set T : Subgroup A := (Q : Subgroup A) ⊓ T'.comap f with hT
    have hTp : IsPGroup p ↥T := Q.isPGroup'.to_le inf_le_left
    have hmapT : T.map f = T' := by
      apply le_antisymm
      · rintro _ ⟨t, ht, rfl⟩
        exact ht.2
      · intro t' ht'
        have h3 : t' ∈ (Q : Subgroup A).map f := hQ' ht'
        obtain ⟨q, hq, rfl⟩ := h3
        exact ⟨q, ⟨hq, ht'⟩, rfl⟩
    have hTN : T ≤ N'.comap f := fun t ht => hT'N' ht.2
    have key := h2 (N'.comap f) (hN'.comap f) T hTN hTp
    have hmap : (N'.comap f ⊔ centralizer (T : Set A)).map f = ⊤ := by
      rw [key]; exact Subgroup.map_top_of_surjective f hf
    rw [Subgroup.map_sup, Subgroup.map_comap_eq_self_of_surjective hf] at hmap
    rw [eq_top_iff, ← hmap]
    refine sup_le_sup_left ?_ N'
    rintro _ ⟨c, hc, rfl⟩
    rw [Subgroup.mem_centralizer_iff]
    intro t' ht'
    rw [← hmapT] at ht'
    obtain ⟨t, ht, rfl⟩ := ht'
    have hct := Subgroup.mem_centralizer_iff.mp hc t ht
    rw [← map_mul, ← map_mul, hct]

end TForm

section PerfectLayer

variable {p : ℕ} [Fact p.Prime]

theorem oResidual_eq_top_of_isPerfect {G : Type*} [Group G] [Finite G] (hG : Group.IsPerfect G) :
    oResidual p G = ⊤ := by
  have hp : p.Prime := Fact.out
  have h2 : IsPGroup p (G ⧸ oResidual p G) := by
    intro q
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective q
    set n := orderOf g with hn
    have hn0 : n ≠ 0 := (orderOf_pos g).ne'
    set a := n.factorization p with ha
    refine ⟨a, ?_⟩
    show (g : G ⧸ oResidual p G) ^ (p ^ a) = 1
    rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]
    apply Subgroup.subset_closure
    show Nat.Coprime (orderOf (g ^ (p ^ a))) p
    rw [orderOf_pow' g (pow_ne_zero _ hp.ne_zero)]
    have hd : p ^ a ∣ n := Nat.ordProj_dvd n p
    rw [Nat.gcd_eq_right hd]
    exact (Nat.coprime_ordCompl hp hn0).symm
  have hnil : Group.IsNilpotent (G ⧸ oResidual p G) := h2.isNilpotent
  by_contra hne
  have hidx : (oResidual p G).index ≠ 1 := fun h => hne (Subgroup.index_eq_one.mp h)
  have hcard : Nat.card (G ⧸ oResidual p G) ≠ 1 := by
    rw [← Subgroup.index]; exact hidx
  have hpos : 0 < Nat.card (G ⧸ oResidual p G) := Nat.card_pos
  have : Nontrivial (G ⧸ oResidual p G) := Finite.one_lt_card_iff_nontrivial.mp (by omega)
  exact Group.IsPerfect.not_isNilpotent (G := G ⧸ oResidual p G) hnil

theorem isPStar_layer_general (X : Type) [Group X] [Finite X] : IsPStar p ↥(layer X) := by
  refine ⟨oResidual_eq_top_of_isPerfect (CFSG.LocalCores.layer_isPerfect), ?_⟩
  intro N hN P
  rw [eq_top_iff]
  rw [← Subgroup.map_le_map_iff_of_injective (layer X).subtype_injective]
  have hrange : (⊤ : Subgroup ↥(layer X)).map (layer X).subtype = layer X := by
    rw [← MonoidHom.range_eq_map, Subgroup.range_subtype]
  rw [hrange]
  refine sSup_le fun K hK => ?_
  have hKE : K ≤ layer X := CFSG.LocalCores.component_le_layer hK
  have hK' : IsComponent (K.subgroupOf (layer X)) := CFSG.LocalCores.component_overgroup hK hKE
  have hKmap : (K.subgroupOf (layer X)).map (layer X).subtype = K :=
    Subgroup.map_subgroupOf_eq_of_le hKE
  rw [← hKmap]
  refine Subgroup.map_mono ?_
  rcases CFSG.LocalCores.component_normal_subgroup hK' hN with h | h
  · exact h.trans le_sup_left
  · refine le_trans ?_ le_sup_right
    have h1 : K.subgroupOf (layer X) ≤ centralizer (N : Set ↥(layer X)) :=
      Subgroup.commutator_eq_bot_iff_le_centralizer.mp h
    exact h1.trans (Subgroup.centralizer_le (by
      intro y hy
      obtain ⟨p, -, rfl⟩ := hy
      exact p.2))

end PerfectLayer


end CFSG.GH74.GLS.Balance.BenderExt

namespace CFSG.GH74.GLS.Balance

open Subgroup CFSG CFSG.GH74.GLS
open CFSG.GH74.GLS.Balance.BenderExt

section Lemma52

theorem centralizer_bot_eq_top (Y : Type*) [Group Y] :
    centralizer (((⊥ : Subgroup Y) : Subgroup Y) : Set Y) = ⊤ := by
  rw [Subgroup.centralizer_eq_top_iff_subset]
  intro x hx
  rw [Subgroup.coe_bot, Set.mem_singleton_iff] at hx
  rw [hx]; exact Subgroup.one_mem _

theorem bender_l52i (p : ℕ) [Fact p.Prime] : BenderL52i p := by
  intro Y _ _ hY
  have hp : p.Prime := Fact.out
  rw [isPStar_iff_T]
  refine ⟨oResidual_eq_top_of_coprime hY, fun N _ T _ hT => ?_⟩
  have hTbot : T = ⊥ := by
    rcases hT.card_eq_or_dvd with h | h
    · exact Subgroup.eq_bot_of_card_eq T h
    · exact absurd (h.trans ((Subgroup.card_subgroup_dvd_card T))) ((Nat.Prime.coprime_iff_not_dvd hp).mp hY)
  rw [hTbot, centralizer_bot_eq_top]
  exact sup_top_eq _

theorem bender_l52ii (p : ℕ) [Fact p.Prime] : BenderL52ii p := by
  intro Y _ _ N _ h
  exact IsPStar.of_surjective (QuotientGroup.mk' N) (QuotientGroup.mk'_surjective N) h

end Lemma52

section Lemma52iv

theorem bender_l52iv (p : ℕ) [Fact p.Prime] : BenderL52iv p := by
  intro Y _ _ hY P hP hPp
  rw [isPStar_iff_T] at hY
  obtain ⟨h1, h2⟩ := hY
  have key := h2 P hP P le_rfl hPp
  have hle : oResidual p Y ≤ centralizer (P : Set Y) := by
    apply oResidual_le_of_pow_mem
    intro y
    have hy : y ∈ P ⊔ centralizer (P : Set Y) := by rw [key]; exact Subgroup.mem_top y
    have := hP
    obtain ⟨u, hu, c, hc, rfl⟩ := Subgroup.mem_sup_of_normal_left.mp hy
    obtain ⟨k, hk⟩ := hPp ⟨u, hu⟩
    refine ⟨k, ?_⟩
    have hcomm : Commute u c := Subgroup.mem_centralizer_iff.mp hc u hu
    rw [hcomm.mul_pow]
    have hu1 : u ^ (p ^ k) = 1 := by simpa using congrArg Subtype.val hk
    rw [hu1, one_mul]
    exact Subgroup.pow_mem _ hc _
  rw [h1] at hle
  intro u hu
  rw [Subgroup.mem_center_iff]
  intro g
  exact (Subgroup.mem_centralizer_iff.mp (hle (Subgroup.mem_top g)) u hu).symm

end Lemma52iv


end CFSG.GH74.GLS.Balance
