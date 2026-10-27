module

public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTheorem5InvolutionFactors
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTheorem5InvolutionRankOne

public section

open CFSG.Open
open CFSG.ComponentClassification.AschbacherTightEmbedding

namespace CFSG.ComponentClassification.AschbacherTheorem5

namespace Involution

open SectionSix

section Diagonal

variable {Q : Type*} [Group Q]

@[expose] def diagonal (σ : MulAut Q) (X : Subgroup Q)
    (hcomm : ∀ x ∈ X, ∀ y ∈ X, σ x * y = y * σ x) : X →* Q where
  toFun x := x * σ x
  map_one' := by simp
  map_mul' x y := by
    change (x : Q) * y * σ (x * y) = (x : Q) * σ x * (y * σ y)
    rw [map_mul, mul_assoc (x : Q), ← mul_assoc (y : Q), ← hcomm x x.2 y y.2]
    group

theorem diagonal_apply {σ : MulAut Q} {X : Subgroup Q}
    {hcomm : ∀ x ∈ X, ∀ y ∈ X, σ x * y = y * σ x} (x : X) :
    diagonal σ X hcomm x = x * σ x := rfl

theorem diagonal_fixed {σ : MulAut Q} (hσ : ∀ q, σ (σ q) = q) {X : Subgroup Q}
    {hcomm : ∀ x ∈ X, ∀ y ∈ X, σ x * y = y * σ x} (x : X) :
    σ (diagonal σ X hcomm x) = diagonal σ X hcomm x := by
  rw [diagonal_apply, map_mul, hσ]
  exact hcomm x x.2 x x.2

theorem diagonal_ker_le_center {σ : MulAut Q} {X Y : Subgroup Q}
    {hcomm : ∀ x ∈ X, ∀ y ∈ X, σ x * y = y * σ x} (hXY : ∀ x ∈ X, σ x ∈ Y)
    (hY : ∀ x ∈ X, ∀ y ∈ Y, x * y = y * x) :
    (diagonal σ X hcomm).ker ≤ Subgroup.center X := by
  intro x hx
  rw [MonoidHom.mem_ker, diagonal_apply] at hx
  have hxY : (x : Q) ∈ Y := by
    have h := Y.inv_mem (hXY x x.2)
    rwa [← eq_inv_of_mul_eq_one_left hx] at h
  rw [Subgroup.mem_center_iff]
  intro y
  exact Subtype.ext (hY y y.2 x hxY)

end Diagonal

theorem pRank_type_le {Q : Type*} [Group Q] [Finite Q] (X : Subgroup Q) :
    CFSG.pRank 2 X ≤ CFSG.Open.pRank 2 X := by
  rw [CFSG.SectionRank.pRank_eq_open_pRank_top]
  have h := CFSG.SectionRank.pRank_le_map (p := 2) one_lt_two X.subtype X.subtype_injective ⊤
  rwa [← MonoidHom.range_eq_map, Subgroup.range_subtype] at h

variable {G : Type} [Group G] [Finite G] {D : Subgroup G} {r : ℕ}
  {Abar : Fin r → Subgroup (D ⧸ aschbacherThm5OddCore D)}

theorem unique_involution_of_moved (hin : SectionSevenBase) (hC : Counterexample G D r Abar)
    {t g : G} (h : Hyp71 D t g) {i j k : Fin r} (hij : i ≠ j) (hki : k ≠ i) (hkj : k ≠ j)
    (htij : (aschbacherThm5Preimage D (Abar i)).map (MulAut.conj t).toMonoidHom =
      aschbacherThm5Preimage D (Abar j)) :
    ∃ c ∈ Abar i, orderOf c = 2 ∧ (∀ x ∈ Abar i, orderOf x = 2 → x = c) ∧
      onQuotient D ⟨t, h.mem⟩ c ≠ c := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set σ := onQuotient D ⟨t, h.mem⟩
  have ht2 : t ^ 2 = 1 := by rw [← h.orderOf_eq]; exact pow_orderOf_eq_one t
  have hσ : ∀ q, σ (σ q) = q := onQuotient_involutive ht2
  have hmap : (Abar i).map σ.toMonoidHom = Abar j := map_onQuotient_factor ⟨t, h.mem⟩ htij
  have hσj : ∀ x ∈ Abar i, σ x ∈ Abar j := fun x hx => hmap ▸ Subgroup.mem_map_of_mem _ hx
  have hcomm : ∀ x ∈ Abar i, ∀ y ∈ Abar i, σ x * y = y * σ x := fun x hx y hy =>
    hC.hyp.hcomm j i (Ne.symm hij) (σ x) (hσj x hx) y hy
  set δ := diagonal σ (Abar i) hcomm
  have hr : CFSG.Open.pRank 2 δ.range ≤ 1 := by
    by_contra hcon
    push Not at hcon
    obtain ⟨E, hEΔ, hE, hcard⟩ := CFSG.SectionRank.exists_isElemAbelian_card_of_le_pRank
      (p := 2) (H := δ.range) (k := 2) (by omega)
    apply no_four_group_quotient hin hC h (V := E) ⟨hE, by rw [hcard]; norm_num⟩
    · intro v hv
      obtain ⟨x, rfl⟩ := hEΔ hv
      exact diagonal_fixed hσ x
    · intro v hv _
      obtain ⟨x, rfl⟩ := hEΔ hv
      refine ⟨k, Subgroup.mul_mem _ ?_ ?_⟩
      · exact mem_centralizer_factor hC.hyp hki x.2
      · exact mem_centralizer_factor hC.hyp hkj (hσj x x.2)
  have hr' : CFSG.pRank 2 δ.range ≤ 1 := (pRank_type_le _).trans hr
  have hker : δ.rangeRestrict.ker ≤ Subgroup.center (Abar i) := by
    rw [MonoidHom.ker_rangeRestrict]
    exact diagonal_ker_le_center hσj fun x hx y hy => (hC.hyp.hcomm i j hij x hx y hy)
  obtain ⟨c, hc, hc2, huniq, hδc⟩ := unique_involution_of_rank_one_image (hC.hyp.hsemisimple i)
    δ.rangeRestrict δ.rangeRestrict_surjective hker hr'
  refine ⟨c, hc, hc2, huniq, fun hσc => hδc hc ?_⟩
  apply Subtype.ext
  change c * σ c = 1
  rw [hσc, ← pow_two, ← hc2, pow_orderOf_eq_one]

theorem exists_perfect_lift {t : G} (ht : t ∈ Subgroup.normalizer (D : Set G))
    (ht2 : orderOf t = 2) {Δ : Subgroup (D ⧸ aschbacherThm5OddCore D)} (hΔ : Group.IsPerfect Δ)
    (hfix : ∀ q ∈ Δ, onQuotient D ⟨t, ht⟩ q = q) {c : D ⧸ aschbacherThm5OddCore D}
    (hcΔ : c ∈ Δ) (hc2 : orderOf c = 2) :
    ∃ B : Subgroup G, B ≤ Subgroup.centralizer ({t} : Set G) ∧ Group.IsPerfect B ∧
      ∃ z ∈ B, orderOf z = 2 ∧ ∃ hz : z ∈ D,
        QuotientGroup.mk' (aschbacherThm5OddCore D) ⟨z, hz⟩ = c := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set H := Subgroup.normalizer (D : Set G)
  set t' : H := ⟨t, ht⟩
  have ht' : orderOf t' = 2 := by rw [← Subgroup.orderOf_coe]; exact ht2
  set ι := quotientEmbedding D
  have hι := quotientEmbedding_injective D
  set N := coreIn D
  have hN : Odd (Nat.card N) := coreIn_odd D
  have hΔc : Δ.map ι ≤ (Subgroup.centralizer ({t'} : Set H)).map (toBar D) := by
    have hcent := AschbacherToolkit.centralizer_quotient_odd N hN t' ht'
    change Δ.map ι ≤ (Subgroup.centralizer ({t'} : Set H)).map (QuotientGroup.mk' N)
    rw [← hcent]
    rintro _ ⟨q, hq, rfl⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hconj := quotientEmbedding_onQuotient t' q
    rw [hfix q hq] at hconj
    change ι q * toBar D t' = toBar D t' * ι q
    calc ι q * toBar D t' = toBar D t' * ι q * (toBar D t')⁻¹ * toBar D t' := by
          rw [← hconj]
      _ = toBar D t' * ι q := by group
  set Y := Subgroup.centralizer ({t'} : Set H) ⊓ (Δ.map ι).comap (toBar D)
  have hYmap : Y.map (toBar D) = Δ.map ι := by
    apply le_antisymm
    · rintro _ ⟨y, hy, rfl⟩
      exact hy.2
    · intro v hv
      obtain ⟨y, hy, rfl⟩ := hΔc hv
      exact ⟨y, ⟨hy, hv⟩, rfl⟩
  have : WellFoundedLT (Subgroup H) := Finite.to_wellFoundedLT
  obtain ⟨B, ⟨hBY, hBmap⟩, hBmin⟩ := (wellFounded_lt (α := Subgroup H)).has_min
    {W : Subgroup H | W ≤ Y ∧ W.map (toBar D) = Δ.map ι} ⟨Y, le_rfl, hYmap⟩
  have hBperf : Group.IsPerfect B := by
    apply Subgroup.isPerfect_iff.mpr
    by_contra hne
    apply hBmin ⁅B, B⁆ ⟨(Subgroup.commutator_le_self B).trans hBY, ?_⟩
    · exact lt_of_le_of_ne (Subgroup.commutator_le_self B) hne
    · rw [Subgroup.map_commutator, hBmap, ← Subgroup.map_commutator, Subgroup.commutator_eq_self]
  have hc2' : orderOf (ι c) = 2 := by rw [orderOf_injective ι hι, hc2]
  have hV2 : IsPGroup 2 (Subgroup.zpowers (ι c)) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hc2', pow_one])
  have hVB : Subgroup.zpowers (ι c) ≤ B.map (QuotientGroup.mk' N) := by
    rw [Subgroup.zpowers_le]
    change ι c ∈ B.map (toBar D)
    rw [hBmap]
    exact Subgroup.mem_map_of_mem _ hcΔ
  obtain ⟨W, hWB, hW2, hWcard, hWmap⟩ := exists_isPGroup_lift N hN hV2 hVB
  have hWcard2 : Nat.card W = 2 := by rw [hWcard, Nat.card_zpowers, hc2']
  have : Nontrivial W := by
    rw [← Finite.one_lt_card_iff_nontrivial, hWcard2]
    norm_num
  obtain ⟨⟨z', hz'W⟩, hz'1⟩ := _root_.exists_ne (1 : W)
  have hz'ne : z' ≠ 1 := fun h => hz'1 (Subtype.ext h)
  have hz'2 : orderOf z' = 2 := by
    have hdvd : orderOf (⟨z', hz'W⟩ : W) ∣ 2 := hWcard2 ▸ orderOf_dvd_natCard _
    rw [Subgroup.orderOf_mk] at hdvd
    rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h1 | h2
    · exact absurd (orderOf_eq_one_iff.mp h1) hz'ne
    · exact h2
  have hz'bar : toBar D z' = ι c := by
    have hmem : toBar D z' ∈ Subgroup.zpowers (ι c) := hWmap ▸ Subgroup.mem_map_of_mem _ hz'W
    obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp hmem
    have hne1 : toBar D z' ≠ 1 := by
      intro h1
      apply hz'ne
      apply AschbacherToolkit.quotient_injective_on_of_isPGroup N hN hW2 hz'W W.one_mem
      change toBar D z' = toBar D 1
      rw [h1, map_one]
    rw [← hn]
    rw [← hn] at hne1
    have hmod : (ι c) ^ n = (ι c) ^ (n % 2) := by
      simpa [hc2'] using (zpow_mod_orderOf (ι c) n).symm
    rw [hmod] at hne1 ⊢
    rcases Int.emod_two_eq_zero_or_one n with h0 | h1
    · rw [h0, zpow_zero] at hne1
      exact absurd rfl hne1
    · rw [h1, zpow_one]
  obtain ⟨d, rfl⟩ := QuotientGroup.mk'_surjective (aschbacherThm5OddCore D) c
  have hzD : (z' : G) ∈ D := by
    have hsame : QuotientGroup.mk' N z' =
        QuotientGroup.mk' N (Subgroup.inclusion Subgroup.le_normalizer d) := hz'bar
    rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq] at hsame
    have hcore := Subgroup.mem_subgroupOf.mp hsame
    have h2 : ((z' : H)⁻¹ * Subgroup.inclusion Subgroup.le_normalizer d : H).val ∈ D :=
      core_le D hcore
    have h3 : (z' : G) = ((Subgroup.inclusion Subgroup.le_normalizer d : H) : G) *
        (((z' : H)⁻¹ * Subgroup.inclusion Subgroup.le_normalizer d : H) : G)⁻¹ := by
      simp
    rw [h3]
    exact D.mul_mem d.2 (D.inv_mem h2)
  refine ⟨B.map H.subtype, ?_, ?_, z', ⟨z', hWB hz'W, rfl⟩, ?_, hzD, ?_⟩
  · rintro _ ⟨b, hb, rfl⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hbt := Subgroup.mem_centralizer_singleton_iff.mp (hBY hb).1
    exact congrArg Subtype.val hbt
  · exact Group.IsPerfect.ofSurjective
      (f := (B.equivMapOfInjective H.subtype H.subtype_injective).toMonoidHom)
      (MulEquiv.surjective _)
  · rw [Subgroup.orderOf_coe]
    exact hz'2
  · apply hι
    rw [quotientEmbedding_mk]
    change toBar D (Subgroup.inclusion Subgroup.le_normalizer ⟨(z' : G), hzD⟩) = _
    rw [← hz'bar]
    rfl

theorem perfect_fixes_factors (hyp : Hyp61 G D r Abar) (hr4 : r ≤ 4) {B : Subgroup G}
    (hBH : B ≤ Subgroup.normalizer (D : Set G)) (hB : Group.IsPerfect B) {b : G} (hb : b ∈ B)
    (k : Fin r) :
    (aschbacherThm5Preimage D (Abar k)).map (MulAut.conj b).toMonoidHom =
      aschbacherThm5Preimage D (Abar k) := by
  classical
  set F : Set (Subgroup G) := Set.range fun l : Fin r => aschbacherThm5Preimage D (Abar l)
  have hF : ∀ x ∈ B, ∀ K ∈ F, K.map (MulAut.conj x).toMonoidHom ∈ F := by
    rintro x hx _ ⟨l, rfl⟩
    obtain ⟨m, hm⟩ := hyp.hperm x (hBH hx) l
    exact ⟨m, hm.symm⟩
  have hmapmul : ∀ (x y : G) (K : Subgroup G), K.map (MulAut.conj (x * y)).toMonoidHom =
      (K.map (MulAut.conj y).toMonoidHom).map (MulAut.conj x).toMonoidHom := by
    intro x y K
    rw [Subgroup.map_map, map_mul]
    rfl
  let act : B → Equiv.Perm F := fun x =>
    { toFun := fun K => ⟨K.1.map (MulAut.conj (x : G)).toMonoidHom, hF x x.2 K.1 K.2⟩
      invFun := fun K => ⟨K.1.map (MulAut.conj (x : G)⁻¹).toMonoidHom,
        hF x⁻¹ (B.inv_mem x.2) K.1 K.2⟩
      left_inv := fun K => by
        apply Subtype.ext
        change (K.1.map _).map _ = K.1
        rw [← hmapmul, inv_mul_cancel, map_one]
        exact Subgroup.map_id K.1
      right_inv := fun K => by
        apply Subtype.ext
        change (K.1.map _).map _ = K.1
        rw [← hmapmul, mul_inv_cancel, map_one]
        exact Subgroup.map_id K.1 }
  let φ : B →* Equiv.Perm F :=
    { toFun := act
      map_one' := Equiv.ext fun K => Subtype.ext (by
        change K.1.map (MulAut.conj (1 : G)).toMonoidHom = K.1
        rw [map_one]
        exact Subgroup.map_id K.1)
      map_mul' := fun x y => Equiv.ext fun K => Subtype.ext (by
        change K.1.map (MulAut.conj ((x : G) * y)).toMonoidHom =
          (K.1.map (MulAut.conj (y : G)).toMonoidHom).map (MulAut.conj (x : G)).toMonoidHom
        rw [hmapmul]) }
  have hcard : Nat.card F ≤ 4 :=
    (Finite.card_range_le _).trans (by rw [Nat.card_eq_fintype_card, Fintype.card_fin]; exact hr4)
  have : Group.IsSolvable (Equiv.Perm F) := Equiv.Perm.isSolvable hcard
  have : Group.IsPerfect φ.range := Group.IsPerfect.ofSurjective φ.rangeRestrict_surjective
  have htriv : φ.range = ⊥ := by
    by_contra hne
    have : Nontrivial φ.range := (Subgroup.nontrivial_iff_ne_bot _).mpr hne
    exact Group.IsPerfect.not_isSolvable φ.range inferInstance
  have hφb : φ ⟨b, hb⟩ = 1 := by
    have hmem : φ ⟨b, hb⟩ ∈ φ.range := ⟨_, rfl⟩
    rw [htriv, Subgroup.mem_bot] at hmem
    exact hmem
  have hK := congrArg (fun π : Equiv.Perm F => (π ⟨_, k, rfl⟩ : F).1) hφb
  exact hK

end Involution

end CFSG.ComponentClassification.AschbacherTheorem5
