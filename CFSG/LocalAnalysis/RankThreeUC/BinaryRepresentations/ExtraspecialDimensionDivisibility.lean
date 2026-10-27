module

public import CFSG.LinearAlgebra.CoprimeActions.PrimeCyclicFixedFreeDimension
public import CFSG.LocalAnalysis.RankThreeUC.BinaryRepresentations.ExtraspecialCentralizerComplement
public import CFSG.LocalAnalysis.RankThreeUC.BinaryRepresentations.ExtraspecialModuleDecomposition
public import CFSG.LocalAnalysis.RankThreeUC.Section5.NoncentralOrderP.NoncentralOrderP
public import CFSG.LocalAnalysis.RankThreeUC.WeakClosure.WeakClosureSetting

public section

namespace CFSG.LocalAnalysis.RankThreeUC

namespace BinaryRepresentations

namespace ExtraspecialDimensionDivisibility

open Subgroup

variable {G : Type} [Group G] {V : Type} [AddCommGroup V] [Module (ZMod 2) V]

theorem extra_equiv {p : ℕ} {A B : Type} [Group A] [Group B] (e : A ≃* B)
    (h : CFSG.IsExtraspecialPGroup p A) : CFSG.IsExtraspecialPGroup p B := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  have hc : center B = (center A).map e.toMonoidHom := (Subgroup.map_center_eq e).symm
  refine ⟨h1.of_surjective e.toMonoidHom e.surjective, ?_, ?_, ?_⟩
  · have := Subgroup.map_commutator (⊤ : Subgroup A) ⊤ e.toMonoidHom
    rw [Subgroup.map_top_of_surjective _ e.surjective] at this
    rw [hc, ← h2]
    exact this.symm
  · rw [hc, ← h3]
    apply le_antisymm
    · have := frattini_le_comap_frattini_of_surjective (φ := e.symm.toMonoidHom) e.symm.surjective
      intro x hx
      have := this hx
      exact ⟨e.symm x, by simpa using this, by simp⟩
    · intro x hx
      obtain ⟨a, ha, rfl⟩ := Subgroup.mem_map.1 hx
      have := frattini_le_comap_frattini_of_surjective (φ := e.toMonoidHom) e.surjective ha
      simpa using this
  · rw [hc, ← h4]
    exact (Nat.card_congr (Subgroup.equivMapOfInjective _ e.toMonoidHom e.injective).toEquiv).symm

theorem card_centerIn {p : ℕ} (H : Subgroup G) (hH : CFSG.IsExtraspecialPGroup p H) :
    Nat.card (centerIn H) = p := by
  rw [← hH.2.2.2]
  exact (Nat.card_congr (Subgroup.equivMapOfInjective _ H.subtype H.subtype_injective).toEquiv).symm

theorem mem_centerIn_top {A : Type} [Group A] (x : A) :
    x ∈ centerIn (⊤ : Subgroup A) ↔ x ∈ center A := by
  rw [mem_center_iff]
  constructor
  · rintro ⟨y, hy, rfl⟩ g
    have := Subgroup.mem_center_iff.1 hy ⟨g, trivial⟩
    simpa using congrArg Subtype.val this
  · intro h
    refine ⟨⟨x, trivial⟩, Subgroup.mem_center_iff.2 ?_, rfl⟩
    intro g
    exact Subtype.ext (h g.1)

theorem centerIn_le_centralizer {H X : Subgroup G} (hXH : X ≤ H) :
    centerIn H ≤ centralizer (X : Set G) := by
  rintro z ⟨c, hc, rfl⟩ x hx
  have := Subgroup.mem_center_iff.1 hc ⟨x, hXH hx⟩
  simpa using congrArg Subtype.val this

@[expose] noncomputable def restrictRep (ρ : Representation (ZMod 2) G V) (S : Subgroup G)
    (W : Submodule (ZMod 2) V) (hW : ∀ s ∈ S, ∀ w ∈ W, ρ s w ∈ W) :
    Representation (ZMod 2) S W where
  toFun s := (ρ s).restrict (fun w hw => hW s s.2 w hw)
  map_one' := by ext w; simp
  map_mul' a b := by
    ext w
    simp [rho_mul_apply]

theorem commSpace_eq_top {A : Type} [Group A] [Finite A] {M : Type} [AddCommGroup M]
    [Module (ZMod 2) M] (σ : Representation (ZMod 2) A M) (B : Subgroup A)
    (hodd : Odd (Nat.card B)) (hfix : fixedSpace σ B = ⊥) : commSpace σ B = ⊤ := by
  classical
  haveI : Fintype B := Fintype.ofFinite _
  have hc : ((Fintype.card B : ℕ) : ZMod 2) = 1 := by
    rw [Fintype.card_eq_nat_card]; exact ZMod.natCast_eq_one_iff_odd.2 hodd
  rw [eq_top_iff]
  intro v _
  have hs : ∑ z : B, (σ z v - v) ∈ commSpace σ B :=
    Submodule.sum_mem _ (fun z _ => Submodule.subset_span ⟨(z : A), z.2, v, rfl⟩)
  have h0 : normOp σ B v = 0 := by
    have := mem_fixedSpace_normOp σ B v
    rwa [hfix, Submodule.mem_bot] at this
  have he : v = -(∑ z : B, (σ z v - v)) := by
    have : v - normOp σ B v = -(∑ z : B, (σ z v - v)) := by
      rw [normOp_apply, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
        ← Nat.cast_smul_eq_nsmul (ZMod 2), hc, one_smul]
      abel
    rwa [h0, sub_zero] at this
  rw [he]
  exact Submodule.neg_mem _ hs

theorem stable_inf {H X : Subgroup G} (ρ : Representation (ZMod 2) G V) (hXH : X ≤ H)
    {s : G} (hsH : s ∈ H) (hsX : s ∈ centralizer (X : Set G)) {w : V}
    (hw : w ∈ commSpace ρ (centerIn H) ⊓ fixedSpace ρ X) :
    ρ s w ∈ commSpace ρ (centerIn H) ⊓ fixedSpace ρ X := by
  have hρinv : ∀ (g : G) (w : V), ρ g⁻¹ (ρ g w) = w := by
    intro g w; rw [← rho_mul_apply, inv_mul_cancel, map_one]; rfl
  rw [Submodule.mem_inf] at hw ⊢
  refine ⟨?_, ?_⟩
  · have hle : commSpace ρ (centerIn H) ≤ (commSpace ρ (centerIn H)).comap (ρ s : V →ₗ[ZMod 2] V) := by
      apply Submodule.span_le.2
      rintro w ⟨x, hx, v, rfl⟩
      obtain ⟨z, hz, rfl⟩ := Subgroup.mem_map.1 hx
      have hzc : s * (z : G) = (z : G) * s := by
        have := Subgroup.mem_center_iff.1 hz ⟨s, hsH⟩
        have := congrArg Subtype.val this
        simpa using this
      show ρ s (ρ z v - v) ∈ commSpace ρ (centerIn H)
      rw [map_sub, ← rho_mul_apply, hzc, rho_mul_apply]
      exact Submodule.subset_span ⟨(z : G), hx, ρ s v, rfl⟩
    exact hle hw.1
  · rw [mem_fixedSpace_iff]
    intro x hx
    have hxs : x * s = s * x := hsX x hx
    rw [← rho_mul_apply, hxs, rho_mul_apply, (mem_fixedSpace_iff ρ X w).1 hw.2 x hx]

theorem dvd_base [Finite G] [Module.Finite (ZMod 2) V]
    (ρ : Representation (ZMod 2) G V) {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (H : Subgroup G) (hH : CFSG.IsExtraspecialPGroup p H)
    (X : Subgroup G) (hXH : X ≤ H) :
    WeakClosure.dOfPrime p ∣ Module.finrank (ZMod 2) ↥(commSpace ρ (centerIn H) ⊓ fixedSpace ρ X) := by
  haveI : Fact p.Prime := ⟨hp⟩
  set W := commSpace ρ (centerIn H) ⊓ fixedSpace ρ X with hWdef
  have hZc := card_centerIn H hH
  set Z := centerIn H with hZ
  have hWst : ∀ s ∈ Z, ∀ w ∈ W, ρ s w ∈ W := fun s hs w hw =>
    stable_inf ρ hXH (by obtain ⟨c, _, rfl⟩ := hs; exact c.2) (centerIn_le_centralizer hXH hs) hw
  let σ' := restrictRep ρ Z W hWst
  have hnt : Nontrivial Z := by
    rw [← Finite.one_lt_card_iff_nontrivial, hZc]; exact hp.one_lt
  obtain ⟨g, hg1⟩ := exists_ne (1 : Z)
  have hgp : g ^ p = 1 := by
    rw [← hZc]; exact pow_card_eq_one'
  have hord : orderOf g = p := by
    rcases (Nat.dvd_prime hp).1 (orderOf_dvd_of_pow_eq_one hgp) with h | h
    · exact absurd (orderOf_eq_one_iff.1 h) hg1
    · exact h
  let u := (MonoidHom.toHomUnits σ') g
  let σ : W ≃ₗ[ZMod 2] W := LinearMap.GeneralLinearGroup.generalLinearEquiv _ _ u
  have hσp : σ ^ p = 1 := by
    have : u ^ p = 1 := by rw [← map_pow, hgp, map_one]
    rw [← map_pow, this, map_one]
  have hσ : ∀ w : W, σ w = σ' g w := fun w => rfl
  have key := CFSG.LinearAlgebra.CoprimeActions.PrimeCyclicFixedFreeDimension.orderOf_two_dvd_finrank p hp2 σ hσp ?_
  · rw [WeakClosure.dOfPrime_eq_orderOf hp hp2]; exact key
  · rw [eq_bot_iff]
    intro w hw
    rw [LinearMap.mem_ker] at hw
    have hfx : σ' g w = w := by
      have : σ w - w = 0 := by simpa using hw
      rw [← hσ]; exact sub_eq_zero.1 this
    have hpow : ∀ k : ℕ, σ' (g ^ k) w = w := by
      intro k
      induction k with
      | zero => simp
      | succ k ihk =>
        rw [pow_succ, map_mul]
        show σ' (g ^ k) (σ' g w) = w
        rw [hfx, ihk]
    have hwZ : (w : V) ∈ fixedSpace ρ Z := by
      rw [mem_fixedSpace_iff]
      intro z hz
      have hz' : (⟨z, hz⟩ : Z) ∈ Subgroup.zpowers g := by
        have : Subgroup.zpowers g = ⊤ := by
          apply Subgroup.eq_top_of_card_eq
          rw [Nat.card_zpowers, hord, hZc]
        rw [this]; trivial
      obtain ⟨k, hk⟩ := mem_powers_iff_mem_zpowers.2 hz'
      have h3 : ((σ' (g ^ k) w : W) : V) = ρ z w := by
        simp only at hk; rw [hk]; rfl
      rw [← h3, hpow k]
    have hfz : (w : V) ∈ commSpace ρ Z ⊓ fixedSpace ρ Z := ⟨w.2.1, hwZ⟩
    have hodd : Odd (Nat.card Z) := by rw [hZc]; exact hp.odd_of_ne_two hp2
    have hb := ExtraspecialModuleDecomposition.fixedSpace_inf_commSpace_eq_bot ρ Z hodd
    rw [hb] at hfz
    have : (w : V) = 0 := (Submodule.mem_bot _).1 hfz
    exact (Submodule.mem_bot _).2 (Subtype.ext this)

theorem main_aux {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) : ∀ n : ℕ, ∀ (G : Type) [Group G] [Finite G]
    (V : Type) [AddCommGroup V] [Module (ZMod 2) V] [Module.Finite (ZMod 2) V]
    (ρ : Representation (ZMod 2) G V) (H : Subgroup G), CFSG.IsExtraspecialPGroup p H →
    Monoid.exponent H = p → Nat.card H = p ^ (1 + 2 * n) → ∀ X : Subgroup G, X ≤ H →
    Nat.card X = p → X ≠ centerIn H →
    p ^ (n - 1) * WeakClosure.dOfPrime p ∣
      Module.finrank (ZMod 2) ↥(commSpace ρ (centerIn H) ⊓ fixedSpace ρ X) := by
  intro n
  induction n with
  | zero =>
    intro G _ _ V _ _ _ ρ H hH hexp hcard X hXH hXp hXZ
    simpa using dvd_base ρ hp hp2 H hH X hXH
  | succ k ih =>
    intro G _ _ V _ _ _ ρ H hH hexp hcard X hXH hXp hXZ
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · simpa using dvd_base ρ hp hp2 H hH X hXH
    have hn : 1 < k + 1 := by omega
    obtain ⟨L, hLle, hLeq, hdisj, hL, hLexp, hLcard, hLZ⟩ :=
      ExtraspecialCentralizerComplement.complement_exists hp hp2 H hH hexp hcard hn X hXH hXp hXZ
    simp only [Nat.add_sub_cancel] at hLcard
    have hLH : L ≤ H := hLle.trans inf_le_left
    have hLC : L ≤ centralizer (X : Set G) := hLle.trans inf_le_right
    set W := commSpace ρ (centerIn H) ⊓ fixedSpace ρ X with hWdef
    have hWst : ∀ s ∈ L, ∀ w ∈ W, ρ s w ∈ W := fun s hs w hw =>
      stable_inf ρ hXH (hLH hs) (hLC hs) hw
    let ρ' := restrictRep ρ L W hWst
    have hLtop : CFSG.IsExtraspecialPGroup p (⊤ : Subgroup L) :=
      extra_equiv Subgroup.topEquiv.symm hL
    have hexpTop : Monoid.exponent (⊤ : Subgroup L) = p := by
      rw [← hLexp]; exact Monoid.exponent_eq_of_mulEquiv Subgroup.topEquiv
    have hcardTop : Nat.card (⊤ : Subgroup L) = p ^ (1 + 2 * k) := by
      rw [Subgroup.card_top, hLcard]
    obtain ⟨X'', hX''le, hX''p, hX''Z⟩ :=
      Section5.NoncentralOrderP.exists_subgroup hp hLtop hexpTop
    have hIH := ih L W ρ' ⊤ hLtop hexpTop hcardTop X'' hX''le hX''p hX''Z
    have hleaf := ExtraspecialModuleDecomposition.finrank_commSpace hp hp2 (⊤ : Subgroup L) hLtop hexpTop
      ρ' X'' hX''le hX''p hX''Z
    have hodd : Odd (Nat.card (centerIn (⊤ : Subgroup L))) := by
      rw [card_centerIn _ hLtop]; exact hp.odd_of_ne_two hp2
    have hfix : fixedSpace ρ' (centerIn (⊤ : Subgroup L)) = ⊥ := by
      rw [eq_bot_iff]
      intro w hw
      rw [mem_fixedSpace_iff] at hw
      have hwZ : (w : V) ∈ fixedSpace ρ (centerIn H) := by
        rw [mem_fixedSpace_iff]
        intro z hz
        rw [← hLZ] at hz
        obtain ⟨c, hc, rfl⟩ := Subgroup.mem_map.1 hz
        have := hw c ((mem_centerIn_top c).2 hc)
        exact congrArg Subtype.val this
      have hfz : (w : V) ∈ commSpace ρ (centerIn H) ⊓ fixedSpace ρ (centerIn H) := ⟨w.2.1, hwZ⟩
      have hodd' : Odd (Nat.card (centerIn H)) := by
        rw [card_centerIn H hH]; exact hp.odd_of_ne_two hp2
      have hb := ExtraspecialModuleDecomposition.fixedSpace_inf_commSpace_eq_bot ρ (centerIn H) hodd'
      rw [hb] at hfz
      exact (Submodule.mem_bot _).2 (Subtype.ext ((Submodule.mem_bot _).1 hfz))
    have htop := commSpace_eq_top ρ' _ hodd hfix
    rw [htop, finrank_top] at hleaf
    rw [htop] at hIH
    obtain ⟨c, hc⟩ := hIH
    refine ⟨c, ?_⟩
    have e1 : p ^ (k + 1 - 1) = p ^ (k - 1) * p := by
      rw [← pow_succ]; congr 1; omega
    rw [e1, hleaf, hc]
    ring

theorem dimension_dvd [Finite G] [Module.Finite (ZMod 2) V]
    (ρ : Representation (ZMod 2) G V) (hρ : Function.Injective ρ) {p n : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2)
    (H : Subgroup G) (hH : CFSG.IsExtraspecialPGroup p H) (hexp : Monoid.exponent H = p)
    (hwidth : Nat.card H = p ^ (1 + 2 * n))
    (X : Subgroup G) (hXH : X ≤ H) (hXp : Nat.card X = p) (hXZ : X ≠ centerIn H) :
    p ^ (n - 1) * WeakClosure.dOfPrime p ∣
      Module.finrank (ZMod 2) ↥(commSpace ρ (centerIn H) ⊓ fixedSpace ρ X) :=
  main_aux hp hp2 n G V ρ H hH hexp hwidth X hXH hXp hXZ

end ExtraspecialDimensionDivisibility

end BinaryRepresentations

end CFSG.LocalAnalysis.RankThreeUC
