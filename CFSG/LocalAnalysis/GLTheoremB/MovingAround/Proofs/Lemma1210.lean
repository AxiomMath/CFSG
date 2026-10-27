module

public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Sec12c

public section

namespace CFSG.LocalAnalysis.GLTheoremB.MovingAround.Lemma1210

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.LocalAnalysis.GLTheoremB.MovingAround
open CFSG.HardMathSupport.Solomon.LocalBalance (barOf)
open CFSG.HardMathSupport.Solomon.Coordinator (IsEkIn)

@[expose] def Input1210_Out13 : Prop :=
  ∀ (Y : Type) [Group Y], Nonempty (Y ≃* alternatingGroup (Fin 13)) →
    ∀ σ : MulAut Y, (∃ k : Y, ∀ x : Y, (σ ^ 3) x = k * x * k⁻¹) →
      ∃ k : Y, ∀ x : Y, σ x = k * x * k⁻¹

@[expose] def Input1210_P2 : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y], Nonempty (Y ≃* alternatingGroup (Fin 13)) →
    ∀ Q : Subgroup Y, IsSylowIn 3 ⊤ Q →
      ∃ H : Subgroup Y, H ≤ Q ∧ IsElemAbelian 3 H ∧ Nat.card H = 3 ^ 4 ∧ GLBCore 3 2 H = ⊤

section Generic

variable {Γ : Type} [Group Γ] [Finite Γ]

theorem inf_eq_bot_of_coprime {O X : Subgroup Γ} (hO : Nat.Coprime 3 (Nat.card O))
    (hX : IsPGroup 3 ↥X) : X ⊓ O = ⊥ := by
  rw [eq_bot_iff]
  intro g hg
  obtain ⟨hgX, hgO⟩ := Subgroup.mem_inf.1 hg
  obtain ⟨k, hk⟩ := hX ⟨g, hgX⟩
  have h1 : orderOf g ∣ 3 ^ k := by
    rw [orderOf_dvd_iff_pow_eq_one]
    have := congrArg Subtype.val hk
    simpa using this
  have h2 : orderOf g ∣ Nat.card O := by
    have := orderOf_dvd_natCard (⟨g, hgO⟩ : O)
    simpa [Subgroup.orderOf_mk] using this
  have h3 : orderOf g ∣ Nat.gcd (3 ^ k) (Nat.card O) := Nat.dvd_gcd h1 h2
  have h4 : Nat.gcd (3 ^ k) (Nat.card O) = 1 :=
    Nat.Coprime.pow_left k hO
  rw [h4] at h3
  exact Subgroup.mem_bot.2 (orderOf_eq_one_iff.1 (Nat.dvd_one.1 h3))

theorem card_sup_of_inf_bot {O X : Subgroup Γ} [O.Normal] (hXO : X ⊓ O = ⊥) :
    Nat.card ↥(X ⊔ O) = Nat.card X * Nat.card O := by
  have h1 := Subgroup.card_mul_index (O.subgroupOf (X ⊔ O))
  have h2 : Nat.card ↥(O.subgroupOf (X ⊔ O)) = Nat.card O :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe le_sup_right).toEquiv
  have h3 : (O.subgroupOf (X ⊔ O)).index = (O.subgroupOf X).index :=
    Subgroup.relIndex_sup_right (H := X) (K := O)
  have h4 : O.subgroupOf X = ⊥ := by
    ext x
    simp only [Subgroup.mem_subgroupOf, Subgroup.mem_bot]
    constructor
    · intro hx
      have hm : (x : Γ) ∈ X ⊓ O := ⟨x.2, hx⟩
      rw [hXO, Subgroup.mem_bot] at hm
      exact Subtype.ext hm
    · intro hx
      rw [hx]
      exact O.one_mem
  have h5 : (O.subgroupOf X).index = Nat.card X := by
    rw [h4, Subgroup.index_bot]
  rw [h2, h3, h5] at h1
  rw [← h1, mul_comm]

theorem frattini_lift (O X : Subgroup Γ) [O.Normal] (hO : Nat.Coprime 3 (Nat.card O))
    (hX : IsPGroup 3 ↥X) {n : Γ} (hn : ∀ x ∈ X, n * x * n⁻¹ ∈ X ⊔ O) :
    ∃ c ∈ X ⊔ O, ∃ m ∈ Subgroup.normalizer (X : Set Γ), n = c * m := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hXO : X ⊓ O = ⊥ := inf_eq_bot_of_coprime hO hX
  have hWc := card_sup_of_inf_bot hXO
  have hXpos : 0 < Nat.card X := Nat.card_pos
  set W : Subgroup Γ := X ⊔ O with hWdef
  set X' : Subgroup Γ := X.map (MulAut.conj n).toMonoidHom with hX'def
  have hX'W : X' ≤ W := by
    rintro _ ⟨x, hx, rfl⟩
    exact hn x hx
  have hXX' : Nat.card X' = Nat.card X :=
    Subgroup.card_map_of_injective (MulAut.conj n).injective
  have hX'p : IsPGroup 3 ↥X' := hX.map (MulAut.conj n).toMonoidHom
  have hP₁p : IsPGroup 3 ↥(X.subgroupOf W) :=
    hX.comap_of_injective W.subtype Subtype.val_injective
  have hP₂p : IsPGroup 3 ↥(X'.subgroupOf W) :=
    hX'p.comap_of_injective W.subtype Subtype.val_injective
  have hP₁c : Nat.card ↥(X.subgroupOf W) = Nat.card X :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe (le_sup_left : X ≤ W)).toEquiv
  have hP₂c : Nat.card ↥(X'.subgroupOf W) = Nat.card X := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hX'W).toEquiv, hXX']
  have hidx : ∀ H : Subgroup ↥W, Nat.card ↥H = Nat.card X → ¬ 3 ∣ H.index := by
    intro H hH
    have h1 := Subgroup.card_mul_index H
    rw [hH, hWc] at h1
    have h2 : H.index = Nat.card O := Nat.eq_of_mul_eq_mul_left hXpos (by rw [h1, mul_comm])
    rw [h2]
    intro h3
    have := Nat.Coprime.coprime_dvd_right h3 hO
    exact absurd this (by norm_num)
  have hS₁idx : ¬ 3 ∣ (X.subgroupOf W).index := hidx _ hP₁c
  have hS₂idx : ¬ 3 ∣ (X'.subgroupOf W).index := hidx _ hP₂c
  let S₁ : Sylow 3 ↥W := IsPGroup.toSylow hP₁p hS₁idx
  let S₂ : Sylow 3 ↥W := IsPGroup.toSylow hP₂p hS₂idx
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (↥W) S₁ S₂
  have hS₂coe : (S₂ : Subgroup ↥W) = X'.subgroupOf W := rfl
  have hS₁coe : (S₁ : Subgroup ↥W) = X.subgroupOf W := rfl
  have hmem : ∀ x' ∈ X', ∃ y ∈ X, (g : Γ) * y * (g : Γ)⁻¹ = x' := by
    intro x' hx'
    have h1 : (⟨x', hX'W hx'⟩ : ↥W) ∈ (S₂ : Subgroup ↥W) := by
      rw [hS₂coe]
      exact Subgroup.mem_subgroupOf.2 hx'
    rw [← hg, Sylow.coe_subgroup_smul] at h1
    obtain ⟨h, hh, hgh⟩ := (Subgroup.mem_smul_pointwise_iff_exists _ _ _).1 h1
    rw [hS₁coe] at hh
    refine ⟨(h : Γ), Subgroup.mem_subgroupOf.1 hh, ?_⟩
    have := congrArg Subtype.val hgh
    simpa [MulAut.smul_def, MulAut.conj_apply] using this
  refine ⟨(g : Γ), g.2, (g : Γ)⁻¹ * n, ?_, by simp⟩
  set m : Γ := (g : Γ)⁻¹ * n with hm
  have hsub : ∀ x ∈ X, m * x * m⁻¹ ∈ X := by
    intro x hx
    obtain ⟨y, hy, hgy⟩ := hmem (n * x * n⁻¹) ⟨x, hx, rfl⟩
    have hy' : y = (g : Γ)⁻¹ * (n * x * n⁻¹) * (g : Γ) := by
      rw [← hgy]
      group
    have : m * x * m⁻¹ = y := by
      rw [hy', hm]
      group
    rw [this]
    exact hy
  have hle : X.map (MulAut.conj m).toMonoidHom ≤ X := by
    rintro _ ⟨x, hx, rfl⟩
    exact hsub x hx
  have hXm : X.map (MulAut.conj m).toMonoidHom = X := by
    apply Subgroup.eq_of_le_of_card_ge hle
    rw [Subgroup.card_map_of_injective (MulAut.conj m).injective]
  rw [Subgroup.mem_normalizer_iff]
  intro h
  constructor
  · intro hh
    exact hsub h hh
  · intro hh
    rw [← hXm] at hh
    obtain ⟨y, hy, hyh⟩ := hh
    have : y = h := by
      have := congrArg (fun t => (MulAut.conj m).symm t) hyh
      simpa [MulAut.conj_apply] using this
    rw [← this]
    exact hy

theorem isMax_of_card_threePart {H P : Subgroup Γ} (hPH : P ≤ H)
    (hc : Nat.card ↥P = 3 ^ (Nat.card ↥H).factorization 3) :
    ∀ R : Subgroup Γ, R ≤ H → IsPGroup 3 ↥R → P ≤ R → R = P := by
  intro R hRH hR hPR
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.1 hR
  have hdvd : 3 ^ k ∣ Nat.card ↥H := by
    rw [← hk]
    exact Subgroup.card_dvd_of_le hRH
  have hne : Nat.card ↥H ≠ 0 := Nat.card_pos.ne'
  have hk_le : k ≤ (Nat.card ↥H).factorization 3 :=
    (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_three hne).1 hdvd
  have hle : Nat.card ↥R ≤ Nat.card ↥P := by
    rw [hc, hk]
    exact Nat.pow_le_pow_right (by norm_num) hk_le
  exact (Subgroup.eq_of_le_of_card_ge hPR hle).symm

theorem exists_threePart_in {H P : Subgroup Γ} (hPH : P ≤ H) (hP : IsPGroup 3 ↥P) :
    ∃ Q : Subgroup Γ, Q ≤ H ∧ IsPGroup 3 ↥Q ∧ P ≤ Q ∧
      Nat.card ↥Q = 3 ^ (Nat.card ↥H).factorization 3 := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hP' : IsPGroup 3 ↥(P.subgroupOf H) := hP.comap_of_injective H.subtype Subtype.val_injective
  obtain ⟨S, hS⟩ := IsPGroup.exists_le_sylow hP'
  refine ⟨(S : Subgroup ↥H).map H.subtype, Subgroup.map_subtype_le _,
    S.isPGroup'.map H.subtype, ?_, ?_⟩
  · intro x hx
    exact ⟨⟨x, hPH hx⟩, hS (Subgroup.mem_subgroupOf.2 hx), rfl⟩
  · rw [Subgroup.card_map_of_injective H.subtype_injective]
    exact Sylow.card_eq_multiplicity S

theorem card_comap_mk (O : Subgroup Γ) [O.Normal] (Qb : Subgroup (Γ ⧸ O)) :
    Nat.card ↥(Qb.comap (QuotientGroup.mk' O)) = Nat.card O * Nat.card ↥Qb := by
  have hsurj : Function.Surjective (QuotientGroup.mk' O) := QuotientGroup.mk'_surjective O
  have h1 := Subgroup.card_mul_index (Qb.comap (QuotientGroup.mk' O))
  have h2 : (Qb.comap (QuotientGroup.mk' O)).index = Qb.index :=
    Subgroup.index_comap_of_surjective (H := Qb) hsurj
  have h3 := Subgroup.card_mul_index Qb
  have h4 := Subgroup.card_eq_card_quotient_mul_card_subgroup O
  have hpos : 0 < Qb.index := by
    unfold Subgroup.index
    exact Nat.card_pos
  rw [h2] at h1
  have h5 : Nat.card ↥(Qb.comap (QuotientGroup.mk' O)) * Qb.index
      = (Nat.card O * Nat.card ↥Qb) * Qb.index := by
    rw [h1, h4, ← h3]
    ring
  exact Nat.eq_of_mul_eq_mul_right hpos h5

theorem card_map_mk_of_inf_eq_bot (O Q : Subgroup Γ) [O.Normal] (h : Q ⊓ O = ⊥) :
    Nat.card ↥(Q.map (QuotientGroup.mk' O)) = Nat.card ↥Q := by
  have hinj : Function.Injective ((QuotientGroup.mk' O).comp Q.subtype) := by
    rw [injective_iff_map_eq_one]
    intro x hx
    have hxO : (x : Γ) ∈ O := (QuotientGroup.eq_one_iff _).1 hx
    have hm : (x : Γ) ∈ Q ⊓ O := ⟨x.2, hxO⟩
    rw [h, Subgroup.mem_bot] at hm
    exact Subtype.ext hm
  have heq : Q.map (QuotientGroup.mk' O) =
      (⊤ : Subgroup ↥Q).map ((QuotientGroup.mk' O).comp Q.subtype) := by
    ext y
    simp only [Subgroup.mem_map, Subgroup.mem_top, true_and, MonoidHom.coe_comp,
      Function.comp_apply, MonoidHom.coe_coe, Subgroup.coe_subtype]
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨⟨x, hx⟩, rfl⟩
    · rintro ⟨x, rfl⟩
      exact ⟨x, x.2, rfl⟩
  rw [heq, Subgroup.card_map_of_injective hinj]
  simp

theorem exists_lift_sylow (O : Subgroup Γ) [O.Normal] (hO : Nat.Coprime 3 (Nat.card O))
    (Qb : Subgroup (Γ ⧸ O)) (hQb : IsPGroup 3 ↥Qb) {P : Subgroup Γ}
    (hPT : P ≤ Qb.comap (QuotientGroup.mk' O)) (hP : IsPGroup 3 ↥P) :
    ∃ Q : Subgroup Γ, Q ≤ Qb.comap (QuotientGroup.mk' O) ∧ IsPGroup 3 ↥Q ∧ P ≤ Q ∧
      Q.map (QuotientGroup.mk' O) = Qb := by
  obtain ⟨Q, hQT, hQp, hPQ, hQc⟩ := exists_threePart_in hPT hP
  have hTc := card_comap_mk O Qb
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.1 hQb
  have h3O : ¬ 3 ∣ Nat.card O := fun h => by
    have := Nat.Coprime.eq_one_of_dvd hO h
    omega
  have hO0 : Nat.card O ≠ 0 := Nat.card_pos.ne'
  have hQb0 : Nat.card ↥Qb ≠ 0 := Nat.card_pos.ne'
  have hfac : (Nat.card O * Nat.card ↥Qb).factorization 3
      = (Nat.card ↥Qb).factorization 3 := by
    rw [Nat.factorization_mul hO0 hQb0, Finsupp.add_apply,
      Nat.factorization_eq_zero_of_not_dvd h3O, zero_add]
  have hv : (Nat.card ↥Qb).factorization 3 = k := by
    rw [hk, Nat.Prime.factorization_pow Nat.prime_three, Finsupp.single_eq_same]
  have hcard : Nat.card ↥Q = Nat.card ↥Qb := by
    rw [hQc, hTc, hfac, hv, hk]
  refine ⟨Q, hQT, hQp, hPQ, ?_⟩
  have hle : Q.map (QuotientGroup.mk' O) ≤ Qb := by
    rintro _ ⟨x, hx, rfl⟩
    exact hQT hx
  have hcard' : Nat.card ↥Qb ≤ Nat.card ↥(Q.map (QuotientGroup.mk' O)) := by
    rw [card_map_mk_of_inf_eq_bot O Q (inf_eq_bot_of_coprime hO hQp), hcard]
  exact Subgroup.eq_of_le_of_card_ge hle hcard'

theorem elemAb_comm {E : Subgroup Γ} (hE : CFSG.Open.IsElemAbelian 3 E) {x y : Γ}
    (hx : x ∈ E) (hy : y ∈ E) : x * y = y * x :=
  congrArg Subtype.val (hE.1.is_comm.comm (⟨x, hx⟩ : E) ⟨y, hy⟩)

theorem commute_mk_of_comm_mod (O : Subgroup Γ) [O.Normal] {y z : Γ}
    (h : y * z * y⁻¹ * z⁻¹ ∈ O) : Commute (QuotientGroup.mk' O y) (QuotientGroup.mk' O z) := by
  have h1 : QuotientGroup.mk' O (y * z * y⁻¹ * z⁻¹) = 1 := (QuotientGroup.eq_one_iff _).2 h
  rw [map_mul, map_mul, map_mul, map_inv, map_inv] at h1
  have h3 := mul_inv_eq_one.1 h1
  show QuotientGroup.mk' O y * QuotientGroup.mk' O z = QuotientGroup.mk' O z * QuotientGroup.mk' O y
  calc QuotientGroup.mk' O y * QuotientGroup.mk' O z
      = (QuotientGroup.mk' O y * QuotientGroup.mk' O z * (QuotientGroup.mk' O y)⁻¹) *
          QuotientGroup.mk' O y := by group
    _ = QuotientGroup.mk' O z * QuotientGroup.mk' O y := by rw [h3]

def commMod (O : Subgroup Γ) [O.Normal] (P : Set Γ) : Subgroup Γ where
  carrier := {y | ∀ z ∈ P, y * z * y⁻¹ * z⁻¹ ∈ O}
  mul_mem' := by
    intro y y' hy hy' z hz
    have h1 : y * y' * z * (y * y')⁻¹ * z⁻¹
        = y * (y' * z * y'⁻¹ * z⁻¹) * y⁻¹ * (y * z * y⁻¹ * z⁻¹) := by group
    rw [h1]
    exact O.mul_mem (by
      have := Subgroup.Normal.conj_mem inferInstance _ (hy' z hz) y
      simpa [mul_assoc] using this) (hy z hz)
  one_mem' := by
    intro z _
    simp
  inv_mem' := by
    intro y hy z hz
    have h1 : y⁻¹ * z * y * z⁻¹ = y⁻¹ * (y * z * y⁻¹ * z⁻¹)⁻¹ * y⁻¹⁻¹ := by group
    have h2 := Subgroup.Normal.conj_mem inferInstance _ (O.inv_mem (hy z hz)) y⁻¹
    rw [show y⁻¹ * z * y⁻¹⁻¹ * z⁻¹ = y⁻¹ * z * y * z⁻¹ by group]
    rw [h1]
    exact h2

theorem mem_commMod {O : Subgroup Γ} [O.Normal] {P : Set Γ} {y : Γ} :
    y ∈ commMod O P ↔ ∀ z ∈ P, y * z * y⁻¹ * z⁻¹ ∈ O := Iff.rfl

theorem no_central_three (O : Subgroup Γ) [O.Normal] (hO : Nat.Coprime 3 (Nat.card O))
    (AG : Subgroup Γ) (hA : IsPGroup 3 ↥AG) (hAe : CFSG.Open.IsElemAbelian 3 AG)
    (hmax : ∀ S : Subgroup Γ, CFSG.Open.IsElemAbelian 3 S → AG ≤ S → S = AG)
    (c : Γ) (hc3 : c ^ 3 ∈ O) (hcA : ∀ a ∈ AG, a * c * a⁻¹ * c⁻¹ ∈ O) (hcn : c ∉ AG ⊔ O) : False := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set Y' : Subgroup Γ := (AG ⊔ Subgroup.zpowers c) ⊔ O with hY'
  have hAY : AG ≤ Y' := le_sup_of_le_left le_sup_left
  have hcY : c ∈ Y' := Subgroup.mem_sup_left (Subgroup.mem_sup_right (Subgroup.mem_zpowers c))
  have hOY : O ≤ Y' := le_sup_right
  have step1 : ∀ a ∈ AG, ∀ z ∈ Y', z * a * z⁻¹ * a⁻¹ ∈ O := by
    intro a ha
    have hle : Y' ≤ commMod O ({a} : Set Γ) := by
      rw [hY']
      refine sup_le (sup_le ?_ ?_) ?_
      · intro a' ha'
        rw [mem_commMod]
        intro z hz
        rw [Set.mem_singleton_iff.1 hz, elemAb_comm hAe ha' ha, mul_inv_cancel_right, mul_inv_cancel]
        exact O.one_mem
      · rw [Subgroup.zpowers_le, mem_commMod]
        intro z hz
        rw [Set.mem_singleton_iff.1 hz]
        have := O.inv_mem (hcA a ha)
        convert this using 1
        group
      · intro o ho
        rw [mem_commMod]
        intro z hz
        rw [Set.mem_singleton_iff.1 hz]
        have := Subgroup.Normal.conj_mem inferInstance _ (O.inv_mem ho) a
        convert O.mul_mem ho this using 1
        group
    intro z hz
    exact (mem_commMod.1 (hle hz)) a (Set.mem_singleton a)
  have step2 : ∀ z ∈ Y', z * c * z⁻¹ * c⁻¹ ∈ O := by
    have hle : Y' ≤ commMod O ({c} : Set Γ) := by
      rw [hY']
      refine sup_le (sup_le ?_ ?_) ?_
      · intro a ha
        rw [mem_commMod]
        intro z hz
        rw [Set.mem_singleton_iff.1 hz]
        exact hcA a ha
      · rw [Subgroup.zpowers_le, mem_commMod]
        intro z hz
        rw [Set.mem_singleton_iff.1 hz]
        simp
      · intro o ho
        rw [mem_commMod]
        intro z hz
        rw [Set.mem_singleton_iff.1 hz]
        have := Subgroup.Normal.conj_mem inferInstance _ (O.inv_mem ho) c
        convert O.mul_mem ho this using 1
        group
    intro z hz
    exact (mem_commMod.1 (hle hz)) c (Set.mem_singleton c)
  have step3 : ∀ y ∈ Y', ∀ z ∈ Y', y * z * y⁻¹ * z⁻¹ ∈ O := by
    have hle : Y' ≤ commMod O (Y' : Set Γ) := by
      rw [hY']
      refine sup_le (sup_le ?_ ?_) ?_
      · intro a ha
        rw [mem_commMod]
        intro z hz
        have hzY : z ∈ Y' := by rw [hY']; exact hz
        have := O.inv_mem (step1 a ha z hzY)
        convert this using 1
        group
      · rw [Subgroup.zpowers_le, mem_commMod]
        intro z hz
        have hzY : z ∈ Y' := by rw [hY']; exact hz
        have := O.inv_mem (step2 z hzY)
        convert this using 1
        group
      · intro o ho
        rw [mem_commMod]
        intro z hz
        have h1 := Subgroup.Normal.conj_mem inferInstance _ (O.inv_mem ho) z
        have h2 := O.mul_mem ho h1
        convert h2 using 1
        group
    intro y hy z hz
    exact (mem_commMod.1 (hle hy)) z hz
  have step4 : ∀ y ∈ Y', y ^ 3 ∈ O := by
    let Ex : Subgroup Γ :=
      { carrier := {y | y ∈ Y' ∧ y ^ 3 ∈ O}
        mul_mem' := by
          rintro y z ⟨hy, hy3⟩ ⟨hz, hz3⟩
          refine ⟨Y'.mul_mem hy hz, ?_⟩
          have hcomm : Commute (QuotientGroup.mk' O y) (QuotientGroup.mk' O z) :=
            commute_mk_of_comm_mod O (step3 y hy z hz)
          have hy3' : QuotientGroup.mk' O (y ^ 3) = 1 := (QuotientGroup.eq_one_iff _).2 hy3
          have hz3' : QuotientGroup.mk' O (z ^ 3) = 1 := (QuotientGroup.eq_one_iff _).2 hz3
          apply (QuotientGroup.eq_one_iff _).1
          show QuotientGroup.mk' O ((y * z) ^ 3) = 1
          rw [map_pow, map_mul, hcomm.mul_pow, ← map_pow, ← map_pow, hy3', hz3', one_mul]
        one_mem' := ⟨Y'.one_mem, by simp⟩
        inv_mem' := by
          rintro y ⟨hy, hy3⟩
          exact ⟨Y'.inv_mem hy, by rw [inv_pow]; exact O.inv_mem hy3⟩ }
    have hle : Y' ≤ Ex := by
      rw [hY']
      refine sup_le (sup_le ?_ ?_) ?_
      · intro a ha
        refine ⟨?_, ?_⟩
        · rw [hY']
          exact Subgroup.mem_sup_left (Subgroup.mem_sup_left ha)
        · rw [hAe.2 a ha]
          exact O.one_mem
      · rw [Subgroup.zpowers_le]
        exact ⟨hcY, hc3⟩
      · intro o ho
        refine ⟨?_, O.pow_mem ho 3⟩
        rw [hY']
        exact Subgroup.mem_sup_right ho
    intro y hy
    exact (hle hy).2
  obtain ⟨S, hSY, hSp, hAS, hSc⟩ := exists_threePart_in hAY hA
  have hSinf : S ⊓ O = ⊥ := inf_eq_bot_of_coprime hO hSp
  have hScomm : ∀ s ∈ S, ∀ t ∈ S, s * t = t * s := by
    intro s hs t ht
    have h1 : s * t * s⁻¹ * t⁻¹ ∈ O := step3 s (hSY hs) t (hSY ht)
    have h2 : s * t * s⁻¹ * t⁻¹ ∈ S :=
      S.mul_mem (S.mul_mem (S.mul_mem hs ht) (S.inv_mem hs)) (S.inv_mem ht)
    have h3 : s * t * s⁻¹ * t⁻¹ = 1 := by
      have hm : s * t * s⁻¹ * t⁻¹ ∈ S ⊓ O := ⟨h2, h1⟩
      rw [hSinf, Subgroup.mem_bot] at hm
      exact hm
    calc s * t = (s * t * s⁻¹ * t⁻¹) * (t * s) := by group
      _ = t * s := by rw [h3, one_mul]
  have hSexp : ∀ s ∈ S, s ^ 3 = 1 := by
    intro s hs
    have hm : s ^ 3 ∈ S ⊓ O := ⟨S.pow_mem hs 3, step4 s (hSY hs)⟩
    rw [hSinf, Subgroup.mem_bot] at hm
    exact hm
  haveI : IsMulCommutative S := ⟨⟨fun a b => Subtype.ext (hScomm a a.2 b b.2)⟩⟩
  have hSel : CFSG.Open.IsElemAbelian 3 S := ⟨by infer_instance, fun x hx => hSexp x hx⟩
  have hSAG : S = AG := hmax S hSel hAS
  set Wb : Subgroup (Γ ⧸ O) := Y'.map (QuotientGroup.mk' O) with hWb
  have hY'eq : Y' = Wb.comap (QuotientGroup.mk' O) := by
    rw [hWb, QuotientGroup.comap_map_mk' O Y', sup_eq_right.2 hOY]
  have hWbcard : Nat.card ↥Y' = Nat.card O * Nat.card ↥Wb := by
    conv_lhs => rw [hY'eq]
    exact card_comap_mk O Wb
  have hWbp : IsPGroup 3 ↥Wb := by
    intro w
    obtain ⟨y, hy, hwy⟩ := Subgroup.mem_map.1 w.2
    refine ⟨1, Subtype.ext ?_⟩
    show (w : Γ ⧸ O) ^ (3 ^ 1) = 1
    rw [← hwy, pow_one, ← map_pow]
    exact (QuotientGroup.eq_one_iff _).2 (step4 y hy)
  obtain ⟨m, hm⟩ := IsPGroup.iff_card.1 hWbp
  have hSWb : Nat.card ↥S = Nat.card ↥Wb := by
    rw [hSc, hWbcard, hm]
    have h3O : ¬ 3 ∣ Nat.card O := fun h => by
      have := Nat.Coprime.eq_one_of_dvd hO h
      omega
    have hO0 : Nat.card O ≠ 0 := Nat.card_pos.ne'
    rw [Nat.factorization_mul hO0 (pow_ne_zero _ (by norm_num)),
      Finsupp.add_apply, Nat.factorization_eq_zero_of_not_dvd h3O, zero_add,
      Nat.Prime.factorization_pow Nat.prime_three, Finsupp.single_eq_same]
  set Ab : Subgroup (Γ ⧸ O) := AG.map (QuotientGroup.mk' O) with hAbdef
  have hAb : Nat.card ↥Ab = Nat.card ↥AG :=
    card_map_mk_of_inf_eq_bot O AG (inf_eq_bot_of_coprime hO hA)
  have hAbWb : Ab ≤ Wb := Subgroup.map_mono hAY
  have hcWb : QuotientGroup.mk' O c ∈ Wb := Subgroup.mem_map.2 ⟨c, hcY, rfl⟩
  have hcAb : QuotientGroup.mk' O c ∉ Ab := by
    rintro ⟨a, ha, hac⟩
    have h1 : a⁻¹ * c ∈ O := by
      rw [← QuotientGroup.eq_one_iff]
      show QuotientGroup.mk' O (a⁻¹ * c) = 1
      rw [map_mul, map_inv, hac, inv_mul_cancel]
    apply hcn
    have hc' : c = a * (a⁻¹ * c) := by group
    rw [hc']
    exact Subgroup.mul_mem_sup ha h1
  have hlt : Nat.card ↥Ab < Nat.card ↥Wb := by
    rcases (Subgroup.card_le_of_le hAbWb).lt_or_eq with h | h
    · exact h
    · exact absurd (Subgroup.eq_of_le_of_card_ge hAbWb h.ge) (fun h' => hcAb (h' ▸ hcWb))
  rw [hAb, ← hSWb, hSAG] at hlt
  exact lt_irrefl _ hlt

theorem mem_normalizer_of_conj_inv_mem {Γ' : Type} [Group Γ'] [Finite Γ'] (B : Subgroup Γ') (g : Γ')
    (h : ∀ x ∈ B, g⁻¹ * x * g ∈ B) : g ∈ Subgroup.normalizer (B : Set Γ') := by
  have hmap : B.map (MulAut.conj g⁻¹).toMonoidHom = B := by
    apply Subgroup.eq_of_le_of_card_ge
    · rintro _ ⟨x, hx, rfl⟩
      exact h x hx |> fun hh => by simpa [MulAut.conj_apply, mul_assoc] using hh
    · rw [Subgroup.card_map_of_injective (MulAut.conj g⁻¹).injective]
  rw [Subgroup.mem_normalizer_iff'']
  intro x
  constructor
  · intro hx
    exact h x hx
  · intro hx
    rw [← hmap] at hx
    obtain ⟨b, hb, hbx⟩ := Subgroup.mem_map.1 hx
    have : b = x := by
      have := congrArg (fun t => (MulAut.conj g) t) hbx
      simpa [MulAut.conj_apply, mul_assoc] using this
    rw [← this]
    exact hb

theorem mem_conj_inv_of_conj_mem {Γ' : Type} [Group Γ'] [Finite Γ'] (B : Subgroup Γ') (g : Γ')
    (h : ∀ y ∈ B, g * y * g⁻¹ ∈ B) : ∀ y ∈ B, g⁻¹ * y * g ∈ B := by
  have hmap : B.map (MulAut.conj g).toMonoidHom = B := by
    apply Subgroup.eq_of_le_of_card_ge
    · rintro _ ⟨x, hx, rfl⟩
      exact h x hx
    · rw [Subgroup.card_map_of_injective (MulAut.conj g).injective]
  intro y hy
  rw [← hmap] at hy
  obtain ⟨b, hb, hby⟩ := Subgroup.mem_map.1 hy
  have : b = g⁻¹ * y * g := by
    have := congrArg (fun t => (MulAut.conj g⁻¹) t) hby
    simpa [MulAut.conj_apply, mul_assoc] using this
  rw [← this]
  exact hb

@[expose] def conjAutOf {Nb : Type} [Group Nb] (Yb : Subgroup Nb) [Yb.Normal] (n : Nb) :
    MulAut Yb where
  toFun x := ⟨n * x * n⁻¹, Subgroup.Normal.conj_mem inferInstance (x : Nb) x.2 n⟩
  invFun x := ⟨n⁻¹ * x * n, by
    have := Subgroup.Normal.conj_mem inferInstance (x : Nb) x.2 n⁻¹
    simpa [mul_assoc] using this⟩
  left_inv x := by
    ext
    simp [mul_assoc]
  right_inv x := by
    ext
    simp [mul_assoc]
  map_mul' x y := by
    ext
    simp [mul_assoc]

theorem conjAutOf_apply {Nb : Type} [Group Nb] (Yb : Subgroup Nb) [Yb.Normal] (n : Nb) (x : Yb) :
    ((conjAutOf Yb n x : Yb) : Nb) = n * x * n⁻¹ := rfl

theorem conjAutOf_pow {Nb : Type} [Group Nb] (Yb : Subgroup Nb) [Yb.Normal] (n : Nb) :
    ∀ (k : ℕ) (y : Yb), (((conjAutOf Yb n ^ k) y : Yb) : Nb) = n ^ k * y * (n ^ k)⁻¹ := by
  intro k
  induction k with
  | zero => intro y; simp
  | succ k ih =>
    intro y
    rw [pow_succ, MulAut.mul_apply, ih (conjAutOf Yb n y), conjAutOf_apply]
    simp only [pow_succ]
    group

theorem coprime_index_of_no_three {Nb : Type} [Group Nb] [Finite Nb] (Yb : Subgroup Nb) [Yb.Normal]
    (hz : ∀ y ∈ Yb, (∀ g ∈ Yb, g * y = y * g) → y = 1)
    (hcent : ∀ c : Nb, (∀ y ∈ Yb, c * y = y * c) → c ^ 3 = 1 → c = 1)
    (hout : ∀ σ : MulAut Yb, (∃ k : Yb, ∀ x : Yb, (σ ^ 3) x = k * x * k⁻¹) →
      ∃ k : Yb, ∀ x : Yb, σ x = k * x * k⁻¹) :
    Nat.Coprime 3 Yb.index := by
  have key : ∀ n : Nb, n ^ 3 ∈ Yb → n ∈ Yb := by
    intro n hn3
    obtain ⟨k, hk⟩ := hout (conjAutOf Yb n) ⟨⟨n ^ 3, hn3⟩, fun x => by
      apply Subtype.ext
      rw [conjAutOf_pow]
      simp [mul_assoc]⟩
    have hkn : ∀ y ∈ Yb, n * y * n⁻¹ = (k : Nb) * y * (k : Nb)⁻¹ := by
      intro y hy
      have := congrArg Subtype.val (hk ⟨y, hy⟩)
      simpa [conjAutOf_apply] using this
    set c : Nb := (k : Nb)⁻¹ * n with hcdef
    have hcC : ∀ y ∈ Yb, c * y = y * c := by
      intro y hy
      rw [hcdef]
      calc (k : Nb)⁻¹ * n * y = (k : Nb)⁻¹ * (n * y * n⁻¹) * n := by group
        _ = (k : Nb)⁻¹ * ((k : Nb) * y * (k : Nb)⁻¹) * n := by rw [hkn y hy]
        _ = y * ((k : Nb)⁻¹ * n) := by group
    have hkc : Commute (k : Nb) c := (hcC k k.2).symm
    have hnc : n = (k : Nb) * c := by rw [hcdef]; group
    have hc3Yb : c ^ 3 ∈ Yb := by
      have h1 : c ^ 3 = ((k : Nb) ^ 3)⁻¹ * n ^ 3 := by
        rw [hnc, hkc.mul_pow]
        group
      rw [h1]
      exact Yb.mul_mem (Yb.inv_mem (Yb.pow_mem k.2 3)) hn3
    have hc3 : c ^ 3 = 1 := by
      apply hz (c ^ 3) hc3Yb
      intro g hg
      exact (show Commute g c from (hcC g hg).symm).pow_right 3
    have hc1 : c = 1 := hcent c hcC hc3
    have hnk : n = (k : Nb) := by
      rw [hnc, hc1, mul_one]
    rw [hnk]
    exact k.2
  apply (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).2
  intro h3
  obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card' (G := Nb ⧸ Yb) 3 h3
  obtain ⟨n, rfl⟩ := QuotientGroup.mk_surjective g
  have hgp : (n : Nb ⧸ Yb) ^ 3 = 1 := by rw [← hg]; exact pow_orderOf_eq_one _
  have hn : n ^ 3 ∈ Yb := by
    apply (QuotientGroup.eq_one_iff _).1
    rw [QuotientGroup.mk_pow]
    exact hgp
  have hnY : n ∈ Yb := key n hn
  have h1 : (n : Nb ⧸ Yb) = 1 := (QuotientGroup.eq_one_iff n).2 hnY
  rw [h1, orderOf_one] at hg
  norm_num at hg

section PRank

variable {Y : Type} [Group Y] [Finite Y]

theorem pRank_bdd (p : ℕ) (hp : 1 < p) (H : Subgroup Y) :
    BddAbove {k : ℕ | ∃ E : Subgroup Y, E ≤ H ∧ IsElemAbelian p E ∧ Nat.card E = p ^ k} := by
  refine ⟨Nat.card Y, ?_⟩
  rintro k ⟨E, -, -, hk⟩
  have h1 : Nat.card E ≤ Nat.card Y := Subgroup.card_le_card_group E
  have h2 : k < p ^ k := Nat.lt_pow_self hp
  omega

theorem le_pRank_of_elemAb {p : ℕ} (hp : 1 < p) {H E : Subgroup Y} (hEH : E ≤ H)
    (hE : IsElemAbelian p E) {k : ℕ} (hk : Nat.card E = p ^ k) : k ≤ CFSG.Open.pRank p H :=
  le_csSup (pRank_bdd p hp H) ⟨E, hEH, hE, hk⟩

theorem exists_elemAb_pRank {p : ℕ} (hp : 1 < p) (H : Subgroup Y) :
    ∃ E : Subgroup Y, E ≤ H ∧ IsElemAbelian p E ∧ Nat.card E = p ^ CFSG.Open.pRank p H := by
  unfold CFSG.Open.pRank
  set S : Set ℕ := {k : ℕ | ∃ E : Subgroup Y, E ≤ H ∧ IsElemAbelian p E ∧ Nat.card E = p ^ k}
    with hS
  have hne : S.Nonempty :=
    ⟨0, ⊥, bot_le, ⟨by infer_instance, fun x hx => by rw [Subgroup.mem_bot.1 hx, one_pow]⟩,
      by simp⟩
  have hfin : S.Finite := by
    refine (Set.finite_Iic (Nat.card Y)).subset ?_
    rintro k ⟨E, -, -, hk⟩
    have h1 : Nat.card E ≤ Nat.card Y := Subgroup.card_le_card_group E
    have h2 : k < p ^ k := Nat.lt_pow_self hp
    exact show k ≤ Nat.card Y by omega
  exact hne.csSup_mem hfin

theorem isElemAbelian_map {Y Z : Type} [Group Y] [Group Z] {p : ℕ} (f : Y →* Z)
    (hf : Function.Injective f) {E : Subgroup Y} (hE : CFSG.Open.IsElemAbelian p E) :
    CFSG.Open.IsElemAbelian p (E.map f) := by
  refine ⟨⟨⟨fun a b => ?_⟩⟩, ?_⟩
  · obtain ⟨a', ha', ha'eq⟩ := Subgroup.mem_map.1 a.2
    obtain ⟨b', hb', hb'eq⟩ := Subgroup.mem_map.1 b.2
    apply Subtype.ext
    show (a : Z) * (b : Z) = (b : Z) * (a : Z)
    rw [← ha'eq, ← hb'eq, ← map_mul, ← map_mul]
    exact congrArg f (congrArg Subtype.val (hE.1.is_comm.comm (⟨a', ha'⟩ : E) ⟨b', hb'⟩))
  · intro x hx
    obtain ⟨x', hx', rfl⟩ := Subgroup.mem_map.1 hx
    rw [← map_pow, hE.2 x' hx', map_one]

theorem elemAb_lift {Γ1 Γ2 : Type} [Group Γ1] [Group Γ2] [Finite Γ1] [Finite Γ2] {p : ℕ}
    (f : Γ1 →* Γ2) (H1 : Subgroup Γ1) (H2 : Subgroup Γ2)
    (hinj : ∀ x ∈ H1, f x = 1 → x = 1) (hsur : ∀ y ∈ H2, ∃ x ∈ H1, f x = y)
    (E : Subgroup Γ2) (hEH : E ≤ H2) (hE : CFSG.Open.IsElemAbelian p E) :
    ∃ E1 : Subgroup Γ1, E1 ≤ H1 ∧ CFSG.Open.IsElemAbelian p E1 ∧ Nat.card E1 = Nat.card E := by
  set E1 : Subgroup Γ1 := H1 ⊓ E.comap f with hE1
  have hE1H : E1 ≤ H1 := inf_le_left
  have hfE1 : ∀ x ∈ E1, f x ∈ E := fun x hx => (inf_le_right : E1 ≤ E.comap f) hx
  have hinjE : ∀ x ∈ E1, ∀ y ∈ E1, f x = f y → x = y := by
    intro x hx y hy hxy
    have hxy' : x⁻¹ * y ∈ H1 := H1.mul_mem (H1.inv_mem (hE1H hx)) (hE1H hy)
    have h1 : f (x⁻¹ * y) = 1 := by rw [map_mul, map_inv, hxy, inv_mul_cancel]
    exact inv_mul_eq_one.1 (hinj _ hxy' h1)
  have hcomm' : ∀ x ∈ E1, ∀ y ∈ E1, x * y = y * x := by
    intro x hx y hy
    apply hinjE _ (E1.mul_mem hx hy) _ (E1.mul_mem hy hx)
    rw [map_mul, map_mul]
    exact congrArg Subtype.val (hE.1.is_comm.comm (⟨f x, hfE1 x hx⟩ : E) ⟨f y, hfE1 y hy⟩)
  refine ⟨E1, hE1H, ⟨⟨⟨fun a b => Subtype.ext (hcomm' a.1 a.2 b.1 b.2)⟩⟩, fun x hx => ?_⟩, ?_⟩
  · have h1 : f (x ^ p) = 1 := by rw [map_pow, hE.2 _ (hfE1 x hx)]
    exact hinj _ (H1.pow_mem (hE1H hx) p) h1
  · apply Nat.card_eq_of_bijective (fun x : E1 => (⟨f x.1, hfE1 x.1 x.2⟩ : E))
    constructor
    · intro x y hxy
      apply Subtype.ext
      apply hinjE x.1 x.2 y.1 y.2
      exact congrArg Subtype.val hxy
    · intro e
      obtain ⟨x, hxH, hfx⟩ := hsur e.1 (hEH e.2)
      refine ⟨⟨x, hxH, ?_⟩, Subtype.ext hfx⟩
      show f x ∈ E
      rw [hfx]
      exact e.2

theorem pRank_map_eq {Γ1 Γ2 : Type} [Group Γ1] [Group Γ2] [Finite Γ1] [Finite Γ2] {p : ℕ} (hp : 1 < p)
    (f : Γ1 →* Γ2) (hf : Function.Injective f) (H : Subgroup Γ1) :
    CFSG.Open.pRank p (H.map f) = CFSG.Open.pRank p H := by
  apply le_antisymm
  · obtain ⟨E, hEH, hEe, hEk⟩ := exists_elemAb_pRank hp (H.map f)
    have hsur : ∀ y ∈ H.map f, ∃ x ∈ H, f x = y := fun y hy => by
      obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.1 hy
      exact ⟨x, hx, rfl⟩
    obtain ⟨E1, hE1H, hE1e, hE1c⟩ := elemAb_lift (p := p) f H (H.map f)
      (fun x _ hx => hf (by rw [hx, map_one])) hsur E hEH hEe
    exact le_pRank_of_elemAb hp hE1H hE1e (by rw [hE1c, hEk])
  · obtain ⟨E, hEH, hEe, hEk⟩ := exists_elemAb_pRank hp H
    have hE' := isElemAbelian_map f hf hEe
    exact le_pRank_of_elemAb hp (Subgroup.map_mono hEH) hE' (by
      rw [Subgroup.card_map_of_injective hf, hEk])

end PRank

theorem normalizer_lift (O : Subgroup Γ) [O.Normal] (hO : Nat.Coprime 3 (Nat.card O))
    (X : Subgroup Γ) (hX : IsPGroup 3 ↥X) (nb : Γ ⧸ O)
    (hnb : ∀ xb ∈ X.map (QuotientGroup.mk' O), nb * xb * nb⁻¹ ∈ X.map (QuotientGroup.mk' O)) :
    ∃ m ∈ Subgroup.normalizer (X : Set Γ), ∃ xb ∈ X.map (QuotientGroup.mk' O),
      nb = xb * QuotientGroup.mk' O m := by
  obtain ⟨n, rfl⟩ := QuotientGroup.mk'_surjective O nb
  have hn : ∀ x ∈ X, n * x * n⁻¹ ∈ X ⊔ O := by
    intro x hx
    have h1 : QuotientGroup.mk' O (n * x * n⁻¹) ∈ X.map (QuotientGroup.mk' O) := by
      have := hnb (QuotientGroup.mk' O x) (Subgroup.mem_map_of_mem _ hx)
      simpa [map_mul, map_inv] using this
    obtain ⟨x', hx', hx'eq⟩ := Subgroup.mem_map.1 h1
    have h2 : x'⁻¹ * (n * x * n⁻¹) ∈ O := by
      apply (QuotientGroup.eq_one_iff _).1
      show QuotientGroup.mk' O (x'⁻¹ * (n * x * n⁻¹)) = 1
      rw [map_mul, map_inv, hx'eq, inv_mul_cancel]
    have h3 : n * x * n⁻¹ = x' * (x'⁻¹ * (n * x * n⁻¹)) := by group
    rw [h3]
    exact Subgroup.mul_mem_sup hx' h2
  obtain ⟨c, hc, m, hm, hnm⟩ := frattini_lift O X hO hX hn
  obtain ⟨x, hx, o, ho, hxo⟩ := Subgroup.mem_sup_of_normal_right.1 hc
  refine ⟨m, hm, QuotientGroup.mk' O c, Subgroup.mem_map.2 ⟨x, hx, ?_⟩, ?_⟩
  · have ho' : QuotientGroup.mk' O o = 1 := (QuotientGroup.eq_one_iff o).2 ho
    rw [← hxo, map_mul, ho', mul_one]
  · rw [hnm, map_mul]

theorem normalizer_le_GLBCore' {G : Type} [Group G] [Finite G] {p k : ℕ} {P Q : Subgroup G}
    (hQP : Q ≤ P) (hk : k ≤ CFSG.Open.pRank p Q) :
    Subgroup.normalizer (Q : Set G) ≤ GLBCore p k P := by
  unfold GLBCore
  exact le_sSup ⟨Q, hQP, hk, rfl⟩

theorem cover_of_lifts (O : Subgroup Γ) [O.Normal] (hO : Nat.Coprime 3 (Nat.card O))
    (QΓ MΓ : Subgroup Γ) (hQ : IsPGroup 3 ↥QΓ) (hQM : QΓ ≤ MΓ)
    (Yb : Subgroup (Γ ⧸ O)) (hYQ : QΓ.map (QuotientGroup.mk' O) ≤ Yb)
    (Hb : Subgroup ↥Yb) (hHb : ∀ h ∈ Hb, (h : Γ ⧸ O) ∈ QΓ.map (QuotientGroup.mk' O))
    (hHN : ∀ X : Subgroup Γ, X ≤ ((Hb.map Yb.subtype).comap (QuotientGroup.mk' O)) ⊓ QΓ →
      2 ≤ CFSG.Open.pRank 3 X → Subgroup.normalizer (X : Set Γ) ≤ MΓ) :
    GLBCore 3 2 Hb ≤ (MΓ.map (QuotientGroup.mk' O)).subgroupOf Yb := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  unfold GLBCore
  refine sSup_le ?_
  rintro _ ⟨Q', hQ'H, hpr, rfl⟩
  intro yb hyb
  rw [Subgroup.mem_subgroupOf]
  set Xg : Subgroup Γ := ((Q'.map Yb.subtype).comap (QuotientGroup.mk' O)) ⊓ QΓ with hXg
  have hXgQ : Xg ≤ QΓ := inf_le_right
  have hQ'in : ∀ q ∈ Q', (q : Γ ⧸ O) ∈ QΓ.map (QuotientGroup.mk' O) := fun q hq =>
    hHb q (hQ'H hq)
  have hXgmap : Xg.map (QuotientGroup.mk' O) = Q'.map Yb.subtype := by
    apply le_antisymm
    · rintro _ ⟨x, hx, rfl⟩
      exact hx.1
    · rintro _ ⟨q, hq, rfl⟩
      obtain ⟨x, hxQ, hxq⟩ := Subgroup.mem_map.1 (hQ'in q hq)
      refine Subgroup.mem_map.2 ⟨x, ⟨?_, hxQ⟩, hxq⟩
      show QuotientGroup.mk' O x ∈ Q'.map Yb.subtype
      rw [hxq]
      exact Subgroup.mem_map.2 ⟨q, hq, rfl⟩
  have hXgH : Xg ≤ ((Hb.map Yb.subtype).comap (QuotientGroup.mk' O)) ⊓ QΓ := by
    intro x hx
    obtain ⟨h1, h2⟩ := hx
    exact ⟨Subgroup.mem_comap.2 (Subgroup.map_mono hQ'H (Subgroup.mem_comap.1 h1)), h2⟩
  have hXgp : IsPGroup 3 ↥Xg := fun g => by
    obtain ⟨k, hk⟩ := hQ ⟨g.1, hXgQ g.2⟩
    exact ⟨k, Subtype.ext (by simpa using congrArg Subtype.val hk)⟩
  have hinjQ : ∀ x ∈ QΓ, QuotientGroup.mk' O x = 1 → x = 1 := by
    intro x hx hx1
    have hxO : x ∈ O := (QuotientGroup.eq_one_iff x).1 hx1
    have hm : x ∈ QΓ ⊓ O := ⟨hx, hxO⟩
    rw [inf_eq_bot_of_coprime hO hQ, Subgroup.mem_bot] at hm
    exact hm
  have hsurQ : ∀ q ∈ Q'.map Yb.subtype, ∃ x ∈ Xg, QuotientGroup.mk' O x = q := by
    intro y hy
    obtain ⟨q, hq, rfl⟩ := Subgroup.mem_map.1 hy
    obtain ⟨x, hxQ, hxq⟩ := Subgroup.mem_map.1 (hQ'in q hq)
    refine ⟨x, ⟨?_, hxQ⟩, ?_⟩
    · show QuotientGroup.mk' O x ∈ Q'.map Yb.subtype
      rw [hxq]
      exact Subgroup.mem_map.2 ⟨q, hq, rfl⟩
    · rw [hxq]
      rfl
  have hXgrank : 2 ≤ CFSG.Open.pRank 3 Xg := by
    obtain ⟨E, hEQ', hEe, hEk⟩ := exists_elemAb_pRank (p := 3) (by norm_num) Q'
    have hE' : CFSG.Open.IsElemAbelian 3 (E.map Yb.subtype) :=
      isElemAbelian_map Yb.subtype Yb.subtype_injective hEe
    obtain ⟨E1, hE1X, hE1e, hE1c⟩ := elemAb_lift (p := 3) (QuotientGroup.mk' O) Xg
      (Q'.map Yb.subtype) (fun x hx hx1 => hinjQ x (hXgQ hx) hx1)
      (fun y hy => hsurQ y hy) (E.map Yb.subtype) (Subgroup.map_mono hEQ') hE'
    have hk : Nat.card E1 = 3 ^ CFSG.Open.pRank 3 Q' := by
      rw [hE1c, Subgroup.card_map_of_injective Yb.subtype_injective, hEk]
    have hle := le_pRank_of_elemAb (p := 3) (by norm_num) hE1X hE1e hk
    exact le_trans hpr hle
  have hNm : Subgroup.normalizer (Xg : Set Γ) ≤ MΓ := hHN Xg hXgH hXgrank
  have hnb : ∀ xb ∈ Xg.map (QuotientGroup.mk' O),
      (yb : Γ ⧸ O) * xb * (yb : Γ ⧸ O)⁻¹ ∈ Xg.map (QuotientGroup.mk' O) := by
    intro xb hxb
    rw [hXgmap] at hxb ⊢
    obtain ⟨q, hq, rfl⟩ := Subgroup.mem_map.1 hxb
    refine Subgroup.mem_map.2 ⟨yb * q * yb⁻¹, ?_, ?_⟩
    · exact (Subgroup.mem_normalizer_iff.1 hyb q).1 hq
    · simp
  obtain ⟨m, hm, xb, hxb, hnbeq⟩ := normalizer_lift O hO Xg hXgp (yb : Γ ⧸ O) hnb
  rw [hnbeq]
  refine (MΓ.map (QuotientGroup.mk' O)).mul_mem ?_ ?_
  · obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.1 hxb
    exact Subgroup.mem_map.2 ⟨x, hQM (hXgQ hx), rfl⟩
  · exact Subgroup.mem_map.2 ⟨m, hNm hm, rfl⟩

end Generic

theorem mem_of_mk_mem_map {Γ' : Type} [Group Γ'] (O : Subgroup Γ') [O.Normal] {AΓ X : Subgroup Γ'}
    (hAO : AΓ ⊓ O = ⊥) (hX : X ≤ AΓ) {x : Γ'} (hx : x ∈ AΓ)
    (hmem : QuotientGroup.mk' O x ∈ X.map (QuotientGroup.mk' O)) : x ∈ X := by
  obtain ⟨y, hy, hyx⟩ := Subgroup.mem_map.1 hmem
  have h1 : y⁻¹ * x ∈ O := QuotientGroup.eq.1 (show QuotientGroup.mk' O y = QuotientGroup.mk' O x from hyx)
  have h2 : y⁻¹ * x ∈ AΓ := AΓ.mul_mem (AΓ.inv_mem (hX hy)) hx
  have h3 : y⁻¹ * x ∈ AΓ ⊓ O := ⟨h2, h1⟩
  rw [hAO, Subgroup.mem_bot] at h3
  have hxy : x = y := (inv_mul_eq_one.1 h3).symm
  rw [hxy]
  exact hy

section GlueA

variable {G : Type} [Group G] [Finite G]

instance instNormalO (N : Subgroup G) : (GLAPPrimeCore 3 ↥N).Normal := GLAPPrimeCore.normal 3 ↥N

theorem coprime_three_card_O (N : Subgroup G) : Nat.Coprime 3 (Nat.card ↥(GLAPPrimeCore 3 ↥N)) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  exact CFSG.pPrimeCore_coprime_card

theorem barX_eq_map (N X : Subgroup G) :
    barX 3 N X = (X.subgroupOf N).map (QuotientGroup.mk' (GLAPPrimeCore 3 ↥N)) := rfl

theorem barX_normal_of_layer (N K A : Subgroup G) (hKN : K ≤ N) (hAN : A ≤ N)
    (hAK : barX 3 N A ≤ barX 3 N K) (hL : GLAPLayer 3 N = ⨆ g ∈ A, GLBConj g K) :
    (barX 3 N K).Normal := by
  set P : Subgroup ↥N := (barX 3 N K).comap (QuotientGroup.mk' (GLAPPrimeCore 3 ↥N)) with hP
  set PG : Subgroup G := P.map N.subtype with hPG
  have hPA : ∀ g (hg : g ∈ A), (⟨g, hAN hg⟩ : ↥N) ∈ P := by
    intro g hg
    show QuotientGroup.mk' _ (⟨g, hAN hg⟩ : ↥N) ∈ barX 3 N K
    apply hAK
    exact Subgroup.mem_map.2 ⟨⟨g, hAN hg⟩, Subgroup.mem_subgroupOf.2 hg, rfl⟩
  have hKP : ∀ k (hk : k ∈ K), (⟨k, hKN hk⟩ : ↥N) ∈ P := by
    intro k hk
    show QuotientGroup.mk' _ (⟨k, hKN hk⟩ : ↥N) ∈ barX 3 N K
    exact Subgroup.mem_map.2 ⟨⟨k, hKN hk⟩, Subgroup.mem_subgroupOf.2 hk, rfl⟩
  have hconj : ∀ g ∈ A, GLBConj g K ≤ PG := by
    intro g hg
    rintro _ ⟨k, hk, rfl⟩
    show g⁻¹ * k * g⁻¹⁻¹ ∈ PG
    rw [inv_inv]
    have hgN : g⁻¹ ∈ N := N.inv_mem (hAN hg)
    have hxN : g⁻¹ * k * g ∈ N := N.mul_mem (N.mul_mem hgN (hKN hk)) (hAN hg)
    refine Subgroup.mem_map.2 ⟨⟨g⁻¹ * k * g, hxN⟩, ?_, rfl⟩
    show QuotientGroup.mk' _ (⟨g⁻¹ * k * g, hxN⟩ : ↥N) ∈ barX 3 N K
    have hel : (⟨g⁻¹ * k * g, hxN⟩ : ↥N)
        = (⟨g, hAN hg⟩ : ↥N)⁻¹ * (⟨k, hKN hk⟩ : ↥N) * (⟨g, hAN hg⟩ : ↥N) := by
      ext
      simp [mul_assoc]
    rw [hel, map_mul, map_mul, map_inv]
    have h1 := hPA g hg
    have h2 := hKP k hk
    exact (barX 3 N K).mul_mem ((barX 3 N K).mul_mem ((barX 3 N K).inv_mem h1) h2) h1
  have hL_le : GLAPLayer 3 N ≤ PG := by
    rw [hL]
    exact iSup₂_le fun g hg => hconj g hg
  have hK_le : K ≤ GLAPLayer 3 N := by
    rw [hL]
    have h1 : GLBConj 1 K = K := by
      ext x
      constructor
      · rintro ⟨y, hy, rfl⟩
        simpa using hy
      · intro hx
        exact ⟨x, hx, by simp⟩
    calc K = GLBConj 1 K := h1.symm
      _ ≤ ⨆ g ∈ A, GLBConj g K := le_iSup₂ (f := fun g _ => GLBConj g K) 1 A.one_mem
  set LG : Subgroup ↥N := (GLAPLayer 3 N).subgroupOf N with hLG
  have hLP : LG ≤ P := by
    intro x hx
    have hxPG : (x : G) ∈ PG := hL_le (Subgroup.mem_subgroupOf.1 hx)
    obtain ⟨y, hy, hyx⟩ := Subgroup.mem_map.1 hxPG
    have hyx' : y = x := Subtype.ext hyx
    rw [← hyx']
    exact hy
  have hY_eq : LG.map (QuotientGroup.mk' (GLAPPrimeCore 3 ↥N)) = barX 3 N K := by
    apply le_antisymm
    · rintro _ ⟨x, hx, rfl⟩
      exact hLP hx
    · rw [barX_eq_map]
      apply Subgroup.map_mono
      intro k hk
      exact Subgroup.mem_subgroupOf.2 (hK_le (Subgroup.mem_subgroupOf.1 hk))
  have hLnorm : LG.Normal := by
    constructor
    intro x hx n
    have hn : (n : G) ∈ Subgroup.normalizer (GLAPLayer 3 N : Set G) :=
      CFSG.HardMathSupport.Solomon.LocalBalance.Lemma512Ns.le_normalizer_gLAPLayer 3
        (Subgroup.le_normalizer) (n.2)
    have hxL : (x : G) ∈ GLAPLayer 3 N := Subgroup.mem_subgroupOf.1 hx
    have := (Subgroup.mem_normalizer_iff.1 hn (x : G)).1 hxL
    refine Subgroup.mem_subgroupOf.2 ?_
    simpa using this
  have hnorm : (LG.map (QuotientGroup.mk' (GLAPPrimeCore 3 ↥N))).Normal :=
    hLnorm.map _ (QuotientGroup.mk'_surjective _)
  rw [hY_eq] at hnorm
  exact hnorm

theorem barX_centre_trivial (N K : Subgroup G)
    (φ : ↥(barX 3 N K) ≃* ↥(alternatingGroup (Fin 13))) :
    ∀ y : ↥(barX 3 N K), (∀ g : ↥(barX 3 N K), g * y = y * g) → y = 1 := by
  intro y hy
  have hc : φ y ∈ Subgroup.center ↥(alternatingGroup (Fin 13)) := by
    rw [Subgroup.mem_center_iff]
    intro g
    obtain ⟨d, rfl⟩ := φ.surjective g
    rw [← map_mul, ← map_mul, hy d]
  rw [alternatingGroup.center_eq_bot (by simp)] at hc
  apply φ.injective
  rw [map_one]
  exact Subgroup.mem_bot.1 hc

theorem isElemAbelian_subgroupOf {p : ℕ} {A N : Subgroup G} (hA : CFSG.Open.IsElemAbelian p A)
    (hAN : A ≤ N) : CFSG.Open.IsElemAbelian p (A.subgroupOf N) := by
  refine ⟨⟨⟨fun a b => ?_⟩⟩, fun x hx => ?_⟩
  · have h : a.1.1 * b.1.1 = b.1.1 * a.1.1 :=
      congrArg Subtype.val (hA.1.is_comm.comm (⟨a.1.1, Subgroup.mem_subgroupOf.1 a.2⟩ : A)
        ⟨b.1.1, Subgroup.mem_subgroupOf.1 b.2⟩)
    exact Subtype.ext (Subtype.ext h)
  · apply Subtype.ext
    show x.1 ^ p = 1
    exact hA.2 x.1 (Subgroup.mem_subgroupOf.1 hx)

theorem barX_index_coprime (N K A : Subgroup G) (hKN : K ≤ N) (hAN : A ≤ N)
    (hAK : barX 3 N A ≤ barX 3 N K) (hL : GLAPLayer 3 N = ⨆ g ∈ A, GLBConj g K)
    (hAe : CFSG.Open.IsElemAbelian 3 A)
    (hAmax : ∀ S : Subgroup G, CFSG.Open.IsElemAbelian 3 S → A ≤ S → S = A)
    (φ : ↥(barX 3 N K) ≃* ↥(alternatingGroup (Fin 13))) (hOut : Input1210_Out13) :
    Nat.Coprime 3 (barX 3 N K).index := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI := barX_normal_of_layer N K A hKN hAN hAK hL
  have hcent : ∀ c : ↥N ⧸ GLAPPrimeCore 3 ↥N, (∀ y ∈ barX 3 N K, c * y = y * c) → c ^ 3 = 1 → c = 1 := by
    intro c hc hc3
    by_contra hc1
    obtain ⟨c', rfl⟩ := QuotientGroup.mk'_surjective (GLAPPrimeCore 3 ↥N) c
    have hAN' : CFSG.Open.IsElemAbelian 3 (A.subgroupOf N) := isElemAbelian_subgroupOf hAe hAN
    have hA' : IsPGroup 3 ↥(A.subgroupOf N) := by
      intro g
      refine ⟨1, Subtype.ext (Subtype.ext ?_)⟩
      have := hAe.2 (g.1.1) (Subgroup.mem_subgroupOf.1 g.2)
      simpa using this
    have hmax' : ∀ S : Subgroup ↥N, CFSG.Open.IsElemAbelian 3 S → A.subgroupOf N ≤ S →
        S = A.subgroupOf N := by
      intro S hS hAS
      have hSmap : CFSG.Open.IsElemAbelian 3 (S.map N.subtype) :=
        isElemAbelian_map N.subtype N.subtype_injective hS
      have hAle : A ≤ S.map N.subtype := by
        intro x hx
        exact Subgroup.mem_map.2 ⟨⟨x, hAN hx⟩, hAS (Subgroup.mem_subgroupOf.2 hx), rfl⟩
      have hSA : S.map N.subtype = A := hAmax _ hSmap hAle
      ext x
      constructor
      · intro hx
        rw [Subgroup.mem_subgroupOf, ← hSA]
        exact Subgroup.mem_map.2 ⟨x, hx, rfl⟩
      · intro hx
        rw [Subgroup.mem_subgroupOf, ← hSA] at hx
        obtain ⟨y, hy, hyx⟩ := Subgroup.mem_map.1 hx
        have hyx' : y = x := Subtype.ext hyx
        rw [← hyx']
        exact hy
    have hc3' : c' ^ 3 ∈ GLAPPrimeCore 3 ↥N := (QuotientGroup.eq_one_iff _).1 (by
      show QuotientGroup.mk' (GLAPPrimeCore 3 ↥N) (c' ^ 3) = 1
      rw [map_pow]
      exact hc3)
    have hcA' : ∀ a ∈ A.subgroupOf N, a * c' * a⁻¹ * c'⁻¹ ∈ GLAPPrimeCore 3 ↥N := by
      intro a ha
      apply (QuotientGroup.eq_one_iff _).1
      have hπa : QuotientGroup.mk' (GLAPPrimeCore 3 ↥N) a ∈ barX 3 N K :=
        hAK (by rw [barX_eq_map]; exact Subgroup.mem_map.2 ⟨a, ha, rfl⟩)
      have hcomm := hc _ hπa
      show QuotientGroup.mk' (GLAPPrimeCore 3 ↥N) (a * c' * a⁻¹ * c'⁻¹) = 1
      simp only [map_mul, map_inv]
      rw [← hcomm]
      group
    have hcn' : c' ∉ A.subgroupOf N ⊔ GLAPPrimeCore 3 ↥N := by
      intro hmem
      obtain ⟨y, hy, o, ho, hyo⟩ := Subgroup.mem_sup_of_normal_right.1 hmem
      have hcY : QuotientGroup.mk' (GLAPPrimeCore 3 ↥N) c' ∈ barX 3 N K := by
        have ho' : QuotientGroup.mk' (GLAPPrimeCore 3 ↥N) o = 1 := (QuotientGroup.eq_one_iff o).2 ho
        rw [← hyo, map_mul, ho', mul_one]
        exact hAK (by rw [barX_eq_map]; exact Subgroup.mem_map.2 ⟨y, hy, rfl⟩)
      apply hc1
      have hcen := barX_centre_trivial N K φ ⟨_, hcY⟩ (fun g => Subtype.ext (hc g.1 g.2).symm)
      exact congrArg Subtype.val hcen
    exact no_central_three (GLAPPrimeCore 3 ↥N) (coprime_three_card_O N) (A.subgroupOf N) hA' hAN'
      hmax' c' hc3' hcA' hcn'
  have hz : ∀ y ∈ barX 3 N K, (∀ g ∈ barX 3 N K, g * y = y * g) → y = 1 := by
    intro y hy hcomm
    have := barX_centre_trivial N K φ ⟨y, hy⟩ (fun g => Subtype.ext (hcomm g.1 g.2))
    exact congrArg Subtype.val this
  have hout : ∀ σ : MulAut ↥(barX 3 N K), (∃ k : ↥(barX 3 N K), ∀ x : ↥(barX 3 N K), (σ ^ 3) x = k * x * k⁻¹) →
      ∃ k : ↥(barX 3 N K), ∀ x : ↥(barX 3 N K), σ x = k * x * k⁻¹ :=
    fun σ hσ => hOut _ ⟨φ⟩ σ hσ
  exact coprime_index_of_no_three (barX 3 N K) hz hcent hout

theorem mem_of_threePower {Nb : Type} [Group Nb] [Finite Nb] (Yb : Subgroup Nb) [Yb.Normal]
    (hcop : Nat.Coprime 3 Yb.index) (n : Nb) (k : ℕ) (hn : n ^ (3 ^ k) = 1) : n ∈ Yb := by
  have h1 : (QuotientGroup.mk n : Nb ⧸ Yb) ^ (3 ^ k) = 1 := by
    rw [← QuotientGroup.mk_pow, hn]
    rfl
  have h2 : orderOf (QuotientGroup.mk n : Nb ⧸ Yb) ∣ 3 ^ k := orderOf_dvd_of_pow_eq_one h1
  have h3 : orderOf (QuotientGroup.mk n : Nb ⧸ Yb) ∣ Yb.index := by
    have := orderOf_dvd_natCard (QuotientGroup.mk n : Nb ⧸ Yb)
    exact this
  have h4 : orderOf (QuotientGroup.mk n : Nb ⧸ Yb) ∣ Nat.gcd (3 ^ k) Yb.index := Nat.dvd_gcd h2 h3
  rw [Nat.Coprime.pow_left k hcop] at h4
  have h5 : (QuotientGroup.mk n : Nb ⧸ Yb) = 1 := orderOf_eq_one_iff.1 (Nat.dvd_one.1 h4)
  exact (QuotientGroup.eq_one_iff n).1 h5

theorem factor_three_eq_of_coprime {Nb : Type} [Group Nb] [Finite Nb] (Yb : Subgroup Nb)
    (hcop : Nat.Coprime 3 Yb.index) :
    (Nat.card Nb).factorization 3 = (Nat.card ↥Yb).factorization 3 := by
  have h1 := Subgroup.card_mul_index Yb
  have hI : Yb.index ≠ 0 := (Nat.card_pos).ne'
  have h3 : ¬ 3 ∣ Yb.index := by
    intro h
    have := Nat.Coprime.eq_one_of_dvd hcop h
    omega
  rw [← h1, Nat.factorization_mul (Nat.card_pos.ne') hI, Finsupp.add_apply,
    Nat.factorization_eq_zero_of_not_dvd h3, add_zero]

theorem card_subgroupOf_isSylowIn {N Q : Subgroup G} (hQ : IsSylowIn 3 N Q) :
    Nat.card ↥(Q.subgroupOf N) = 3 ^ (Nat.card ↥N).factorization 3 := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hP : IsPGroup 3 ↥(Q.subgroupOf N) :=
    hQ.2.1.comap_of_injective N.subtype Subtype.val_injective
  obtain ⟨R, -, hRp, hPR, hRc⟩ := exists_threePart_in (H := (⊤ : Subgroup ↥N)) le_top hP
  have hRQ : R = Q.subgroupOf N := by
    have hR' : IsPGroup 3 ↥(R.map N.subtype) := hRp.map N.subtype
    have hleQ : Q ≤ R.map N.subtype := by
      intro x hx
      exact Subgroup.mem_map.2 ⟨⟨x, hQ.1 hx⟩, hPR (Subgroup.mem_subgroupOf.2 hx), rfl⟩
    have hRQ' : R.map N.subtype = Q := hQ.2.2 (R.map N.subtype) (Subgroup.map_subtype_le R) hR' hleQ
    ext x
    constructor
    · intro hx
      rw [Subgroup.mem_subgroupOf, ← hRQ']
      exact Subgroup.mem_map.2 ⟨x, hx, rfl⟩
    · intro hx
      rw [Subgroup.mem_subgroupOf, ← hRQ'] at hx
      obtain ⟨y, hy, hyx⟩ := Subgroup.mem_map.1 hx
      have hyx' : y = x := Subtype.ext hyx
      rw [← hyx']
      exact hy
  rw [← hRQ, hRc, Subgroup.card_top]

theorem liftSub_elemAb {Γ : Type} [Group Γ] [Finite Γ] (O : Subgroup Γ) [O.Normal]
    (hO : Nat.Coprime 3 (Nat.card O)) (QΓ : Subgroup Γ) (hQ : IsPGroup 3 ↥QΓ)
    (Yb : Subgroup (Γ ⧸ O)) (Hb : Subgroup ↥Yb) (hHb : CFSG.Open.IsElemAbelian 3 Hb)
    (hHbQ : ∀ x ∈ Hb, (x : Γ ⧸ O) ∈ QΓ.map (QuotientGroup.mk' O)) :
    CFSG.Open.IsElemAbelian 3 ((((Hb.map Yb.subtype).comap (QuotientGroup.mk' O)) ⊓ QΓ : Subgroup Γ)) ∧
      Nat.card ↥(((Hb.map Yb.subtype).comap (QuotientGroup.mk' O)) ⊓ QΓ : Subgroup Γ) = Nat.card Hb := by
  set HΓ : Subgroup Γ := ((Hb.map Yb.subtype).comap (QuotientGroup.mk' O)) ⊓ QΓ with hHΓ
  have hHΓQ : HΓ ≤ QΓ := inf_le_right
  have hQO : QΓ ⊓ O = ⊥ := inf_eq_bot_of_coprime hO hQ
  have hHΓO : HΓ ⊓ O = ⊥ := le_bot_iff.1 (hQO ▸ inf_le_inf_right O hHΓQ)
  have hinj : ∀ x ∈ HΓ, QuotientGroup.mk' O x = 1 → x = 1 := by
    intro x hx hx1
    have hxO : x ∈ O := (QuotientGroup.eq_one_iff x).1 hx1
    have hm : x ∈ HΓ ⊓ O := ⟨hx, hxO⟩
    rw [hHΓO, Subgroup.mem_bot] at hm
    exact hm
  have hsur : ∀ y ∈ Hb.map Yb.subtype, ∃ x ∈ HΓ, QuotientGroup.mk' O x = y := by
    intro y hy
    obtain ⟨h, hh, rfl⟩ := Subgroup.mem_map.1 hy
    obtain ⟨x, hxQ, hxq⟩ := Subgroup.mem_map.1 (hHbQ h hh)
    refine ⟨x, ⟨?_, hxQ⟩, hxq⟩
    show QuotientGroup.mk' O x ∈ Hb.map Yb.subtype
    rw [hxq]
    exact Subgroup.mem_map.2 ⟨h, hh, rfl⟩
  have himg : HΓ.map (QuotientGroup.mk' O) = Hb.map Yb.subtype := by
    apply le_antisymm
    · rintro _ ⟨x, hx, rfl⟩
      exact hx.1
    · intro y hy
      obtain ⟨x, hx, hxy⟩ := hsur y hy
      exact Subgroup.mem_map.2 ⟨x, hx, hxy⟩
  have hcard : Nat.card ↥HΓ = Nat.card Hb := by
    rw [← card_map_mk_of_inf_eq_bot O HΓ hHΓO, himg, Subgroup.card_map_of_injective Yb.subtype_injective]
  obtain ⟨E1, hE1H, hE1e, hE1c⟩ := elemAb_lift (p := 3) (QuotientGroup.mk' O) HΓ (Hb.map Yb.subtype)
    hinj hsur (Hb.map Yb.subtype) le_rfl (isElemAbelian_map Yb.subtype Yb.subtype_injective hHb)
  have hE1eq : E1 = HΓ := by
    apply Subgroup.eq_of_le_of_card_ge hE1H
    rw [hE1c, Subgroup.card_map_of_injective Yb.subtype_injective, hcard]
  refine ⟨?_, ?_⟩
  · rw [← hE1eq]
    exact hE1e
  · rw [hcard]

theorem normalizer_le_of_lift104 {m : ℕ} {B M E A N Q : Subgroup G} (h : Sec11 G m 3 B M E A)
    (hA3 : CFSG.Open.pRank 3 A = 3)
    (hQ : IsSylowIn 3 N Q) (hQM : Q ≤ M)
    (Yb : Subgroup (↥N ⧸ GLAPPrimeCore 3 ↥N)) (Hb : Subgroup ↥Yb)
    (hHb : CFSG.Open.IsElemAbelian 3 Hb) (hHbc : Nat.card ↥Hb = 3 ^ 4)
    (hHbQ : ∀ x ∈ Hb, (x : ↥N ⧸ GLAPPrimeCore 3 ↥N) ∈
      (Q.subgroupOf N).map (QuotientGroup.mk' (GLAPPrimeCore 3 ↥N))) :
    ∀ X : Subgroup ↥N,
      X ≤ ((Hb.map Yb.subtype).comap (QuotientGroup.mk' (GLAPPrimeCore 3 ↥N))) ⊓ Q.subgroupOf N →
      2 ≤ CFSG.Open.pRank 3 X → Subgroup.normalizer (X : Set ↥N) ≤ M.subgroupOf N := by
  intro X hXH hpr n hn
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hQp : IsPGroup 3 ↥(Q.subgroupOf N) :=
    hQ.2.1.comap_of_injective N.subtype Subtype.val_injective
  obtain ⟨hHΓel, hHΓc⟩ := liftSub_elemAb (GLAPPrimeCore 3 ↥N) (coprime_three_card_O N)
    (Q.subgroupOf N) hQp Yb Hb hHb hHbQ
  set HΓ : Subgroup ↥N := ((Hb.map Yb.subtype).comap (QuotientGroup.mk' (GLAPPrimeCore 3 ↥N)))
    ⊓ Q.subgroupOf N with hHΓ
  set HG : Subgroup G := HΓ.map N.subtype with hHG
  have hHG_el : CFSG.Open.IsElemAbelian 3 HG := isElemAbelian_map N.subtype N.subtype_injective hHΓel
  have hHG_c : Nat.card ↥HG = 3 ^ 4 := by
    rw [hHG, Subgroup.card_map_of_injective N.subtype_injective, hHΓc, hHbc]
  have hHG_Q : HG ≤ Q := by
    rintro _ ⟨x, hx, rfl⟩
    exact Subgroup.mem_subgroupOf.1 (inf_le_right (a := ((Hb.map Yb.subtype).comap
      (QuotientGroup.mk' (GLAPPrimeCore 3 ↥N)))) hx)
  obtain ⟨R', hR'M, hQR'⟩ := Sec12c.exists_isSylowIn_above hQM hQ.2.1
  have hEk : IsEkIn 3 4 R' HG := ⟨hHG_Q.trans hQR', hHG_el, hHG_c⟩
  obtain ⟨hv4, -⟩ := lemma104_v_holds h.toSec10Fails h.pair (Or.inr hA3) hR'M
  obtain ⟨-, -, A₁, hA₁, hHA₁⟩ := hv4 HG hEk
  have hclA₁ : GLBCore 3 2 A₁ ≤ M := hA₁.2.clause_d
  set XG : Subgroup G := X.map N.subtype with hXG
  have hXG_le : XG ≤ A₁ := by
    have h1 : XG ≤ HG := by
      rw [hXG, hHG]
      exact Subgroup.map_mono hXH
    exact h1.trans hHA₁
  have hXG_rk : 2 ≤ CFSG.Open.pRank 3 XG := by
    rw [hXG, pRank_map_eq (p := 3) (by norm_num) N.subtype N.subtype_injective X]
    exact hpr
  have hnorm : Subgroup.normalizer (XG : Set G) ≤ GLBCore 3 2 A₁ :=
    normalizer_le_GLBCore' hXG_le hXG_rk
  have hnG : (n : G) ∈ Subgroup.normalizer (XG : Set G) := by
    rw [Subgroup.mem_normalizer_iff]
    intro y
    constructor
    · intro hy
      obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.1 hy
      refine Subgroup.mem_map.2 ⟨n * x * n⁻¹, (Subgroup.mem_normalizer_iff.1 hn x).1 hx, ?_⟩
      simp
    · intro hy
      obtain ⟨x, hx, hxy⟩ := Subgroup.mem_map.1 hy
      have hx' : n⁻¹ * x * n ∈ X := (Subgroup.mem_normalizer_iff''.1 hn x).1 hx
      refine Subgroup.mem_map.2 ⟨n⁻¹ * x * n, hx', ?_⟩
      have hxy' : (x : G) = (n : G) * y * (n : G)⁻¹ := hxy
      show (n : G)⁻¹ * (x : G) * (n : G) = y
      rw [hxy']
      group
  exact Subgroup.mem_subgroupOf.2 (hclA₁ (hnorm hnG))

theorem isPGroup_map_of_isPGroup {Γ' Nb : Type} [Group Γ'] [Group Nb] (f : Γ' →* Nb) {P : Subgroup Γ'}
    (hP : IsPGroup 3 ↥P) : IsPGroup 3 ↥(P.map f) := by
  intro g
  obtain ⟨x, hx, hxg⟩ := Subgroup.mem_map.1 g.2
  obtain ⟨k, hk⟩ := hP ⟨x, hx⟩
  refine ⟨k, Subtype.ext ?_⟩
  have hx' : x ^ (3 ^ k) = 1 := by simpa using congrArg Subtype.val hk
  show (g : Nb) ^ (3 ^ k) = 1
  rw [← hxg, ← map_pow, hx', map_one]

theorem factor_three_quotient {Γ' : Type} [Group Γ'] [Finite Γ'] (O : Subgroup Γ') [O.Normal]
    (hO : Nat.Coprime 3 (Nat.card O)) :
    (Nat.card Γ').factorization 3 = (Nat.card (Γ' ⧸ O)).factorization 3 := by
  have hO0 : Nat.card O ≠ 0 := Nat.card_pos.ne'
  have hq0 : Nat.card (Γ' ⧸ O) ≠ 0 := Nat.card_pos.ne'
  have h3O : ¬ 3 ∣ Nat.card O := fun hd => by
    have := Nat.Coprime.eq_one_of_dvd hO hd
    omega
  rw [Subgroup.card_eq_card_quotient_mul_card_subgroup O, Nat.factorization_mul hq0 hO0,
    Finsupp.add_apply, Nat.factorization_eq_zero_of_not_dvd h3O, add_zero]

theorem not_le_of_sylow_contains_A {m : ℕ} {B M E A N K : Subgroup G} (h : Sec11 G m 3 B M E A)
    (hA3 : CFSG.Open.pRank 3 A = 3) (hAe : CFSG.Open.IsElemAbelian 3 A)
    (hAmax : ∀ S : Subgroup G, CFSG.Open.IsElemAbelian 3 S → A ≤ S → S = A)
    (hAN : A ≤ N) (hKN : K ≤ N)
    (hAK : barX 3 N A ≤ barX 3 N K) (hL : GLAPLayer 3 N = ⨆ g ∈ A, GLBConj g K)
    (hcovK : ¬ Covers 3 N M K) (φ : ↥(barX 3 N K) ≃* ↥(alternatingGroup (Fin 13)))
    (hP2 : Input1210_P2) (hOut : Input1210_Out13) {Q : Subgroup G} (hQ : IsSylowIn 3 N Q) (hAQ : A ≤ Q) :
    ¬ Q ≤ M := by
  intro hQM
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hcop : Nat.Coprime 3 (barX 3 N K).index :=
    barX_index_coprime N K A hKN hAN hAK hL hAe hAmax φ hOut
  haveI hYn : (barX 3 N K).Normal := barX_normal_of_layer N K A hKN hAN hAK hL
  have hQp : IsPGroup 3 ↥(Q.subgroupOf N) :=
    hQ.2.1.comap_of_injective N.subtype Subtype.val_injective
  have hQbY : (Q.subgroupOf N).map (QuotientGroup.mk' (GLAPPrimeCore 3 ↥N)) ≤ barX 3 N K := by
    rintro _ ⟨x, hx, rfl⟩
    obtain ⟨k, hk⟩ := hQp ⟨x, hx⟩
    apply mem_of_threePower (barX 3 N K) hcop _ k
    have hx' : x ^ (3 ^ k) = 1 := by simpa using congrArg Subtype.val hk
    rw [← map_pow, hx', map_one]
  have hcardQ : Nat.card ↥(Q.subgroupOf N) = 3 ^ (Nat.card ↥N).factorization 3 :=
    card_subgroupOf_isSylowIn hQ
  have hcardQb : Nat.card ↥((Q.subgroupOf N).map (QuotientGroup.mk' (GLAPPrimeCore 3 ↥N)))
      = Nat.card ↥(Q.subgroupOf N) :=
    card_map_mk_of_inf_eq_bot _ _ (inf_eq_bot_of_coprime (coprime_three_card_O N) hQp)
  have hfacN : (Nat.card ↥N).factorization 3
      = (Nat.card (↥N ⧸ GLAPPrimeCore 3 ↥N)).factorization 3 :=
    factor_three_quotient (GLAPPrimeCore 3 ↥N) (coprime_three_card_O N)
  have hfacY := factor_three_eq_of_coprime (barX 3 N K) hcop
  have hQb'card : Nat.card ↥(((Q.subgroupOf N).map (QuotientGroup.mk' (GLAPPrimeCore 3 ↥N))).subgroupOf
      (barX 3 N K)) = 3 ^ (Nat.card ↥(barX 3 N K)).factorization 3 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hQbY).toEquiv, hcardQb, hcardQ, hfacN, hfacY]
  have hQb'p : IsPGroup 3 ↥(((Q.subgroupOf N).map (QuotientGroup.mk' (GLAPPrimeCore 3 ↥N))).subgroupOf
      (barX 3 N K)) :=
    (isPGroup_map_of_isPGroup (QuotientGroup.mk' (GLAPPrimeCore 3 ↥N)) hQp).comap_of_injective
      (barX 3 N K).subtype Subtype.val_injective
  have hQb'syl : IsSylowIn 3 ⊤ (((Q.subgroupOf N).map (QuotientGroup.mk' (GLAPPrimeCore 3 ↥N))).subgroupOf
      (barX 3 N K)) := by
    refine ⟨le_top, hQb'p, ?_⟩
    have hc' : Nat.card ↥(((Q.subgroupOf N).map (QuotientGroup.mk' (GLAPPrimeCore 3 ↥N))).subgroupOf
        (barX 3 N K)) = 3 ^ (Nat.card ↥(⊤ : Subgroup ↥(barX 3 N K))).factorization 3 := by
      rw [Subgroup.card_top]
      exact hQb'card
    exact isMax_of_card_threePart le_top hc'
  obtain ⟨Hb, hHbQ, hHbel, hHbc, hHbgen⟩ := hP2 (barX 3 N K) ⟨φ⟩ _ hQb'syl
  have hHbQ' : ∀ x ∈ Hb, (x : ↥N ⧸ GLAPPrimeCore 3 ↥N) ∈
      (Q.subgroupOf N).map (QuotientGroup.mk' (GLAPPrimeCore 3 ↥N)) := fun x hx =>
    Subgroup.mem_subgroupOf.1 (hHbQ hx)
  have hHN := normalizer_le_of_lift104 h hA3 hQ hQM (barX 3 N K) Hb hHbel hHbc hHbQ'
  have hcov := cover_of_lifts (GLAPPrimeCore 3 ↥N) (coprime_three_card_O N) (Q.subgroupOf N)
    (M.subgroupOf N) hQp (fun x hx => Subgroup.mem_subgroupOf.2 (hQM (Subgroup.mem_subgroupOf.1 hx)))
    (barX 3 N K) hQbY Hb hHbQ' hHN
  rw [hHbgen] at hcov
  apply hcovK
  show barX 3 N K ≤ barX 3 N M
  intro y hy
  have hy' := hcov (Subgroup.mem_top (⟨y, hy⟩ : ↥(barX 3 N K)))
  exact Subgroup.mem_subgroupOf.1 hy'

theorem card_of_isSylowIn_top {Y : Type} [Group Y] [Finite Y] {Q : Subgroup Y}
    (hQ : IsSylowIn 3 ⊤ Q) : Nat.card ↥Q = 3 ^ (Nat.card Y).factorization 3 := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨R, -, hRp, hQR, hRc⟩ := exists_threePart_in (H := (⊤ : Subgroup Y)) le_top hQ.2.1
  have hRQ : R = Q := hQ.2.2 R le_top hRp hQR
  rw [← hRQ, hRc, Subgroup.card_top]

theorem isPGroup_subgroupOf_of_elemAb {p : ℕ} [Fact p.Prime] {N A : Subgroup G}
    (hA : CFSG.Open.IsElemAbelian p A) (hAN : A ≤ N) : IsPGroup p ↥(A.subgroupOf N) := by
  intro g
  refine ⟨1, Subtype.ext (Subtype.ext ?_)⟩
  have := hA.2 (g.1.1) (Subgroup.mem_subgroupOf.1 g.2)
  simpa using this

theorem normalizer_E_inf_le_M {m : ℕ} {B M E A : Subgroup G} (h : Sec11 G m 3 B M E A)
    (hE2 : CFSG.Open.pRank 3 (E ⊓ A) = 2) :
    Subgroup.normalizer ((E ⊓ A : Subgroup G) : Set G) ≤ M := by
  have h1 : Subgroup.normalizer ((E ⊓ A : Subgroup G) : Set G) ≤ GLBCore 3 2 E :=
    normalizer_le_GLBCore' inf_le_left hE2.ge
  have h2 : GLBCore 3 2 E ≤ M := h.pair.1.1.2.clause_d
  exact h1.trans h2

theorem barX_mono_left {N X Y : Subgroup G} (h : X ≤ Y) : barX 3 N X ≤ barX 3 N Y := by
  rw [barX_eq_map, barX_eq_map]
  apply Subgroup.map_mono
  intro x hx
  exact Subgroup.mem_subgroupOf.2 (h (Subgroup.mem_subgroupOf.1 hx))

end GlueA

theorem exists_central_prime {G : Type} [Group G] [Finite G] {p : ℕ} [hp : Fact p.Prime]
    {R : Subgroup G} (hR : IsPGroup p ↥R) (hne : ∃ x ∈ R, x ≠ 1) :
    ∃ z ∈ centerOf R, orderOf z = p := by
  obtain ⟨x0, hx0R, hx01⟩ := hne
  haveI : Nontrivial ↥R := ⟨⟨⟨x0, hx0R⟩, 1, fun h => hx01 (congrArg Subtype.val h)⟩⟩
  haveI : Nontrivial ↥(Subgroup.center ↥R) := IsPGroup.center_nontrivial hR
  have hcp : IsPGroup p ↥(Subgroup.center ↥R) := by
    intro g
    obtain ⟨k, hk⟩ := hR (g : ↥R)
    exact ⟨k, Subtype.ext (by simpa using hk)⟩
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.1 hcp
  have hn1 : 1 < Nat.card ↥(Subgroup.center ↥R) := Finite.one_lt_card
  have hn0 : n ≠ 0 := by
    rintro rfl
    rw [pow_zero] at hn
    omega
  have hpdvd : p ∣ Nat.card ↥(Subgroup.center ↥R) := by
    rw [hn]
    exact dvd_pow_self p hn0
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := ↥(Subgroup.center ↥R)) p hpdvd
  refine ⟨((x : ↥R) : G), Subgroup.mem_map.2 ⟨(x : ↥R), x.2, rfl⟩, ?_⟩
  have e1 := orderOf_injective R.subtype Subtype.val_injective (x : ↥R)
  have e2 : orderOf (x : ↥R) = orderOf x :=
    orderOf_injective (Subgroup.center ↥R).subtype Subtype.val_injective x
  exact e1.trans (e2.trans hx)

theorem le_cg_of_mem_centerOf {G : Type} [Group G] {Q : Subgroup G} {z : G} (hz : z ∈ centerOf Q) :
    Q ≤ Subgroup.centralizer ({z} : Set G) := by
  obtain ⟨c, hc, hcz⟩ := Subgroup.mem_map.1 hz
  intro q hq
  rw [Subgroup.mem_centralizer_iff]
  intro w hw
  rw [Set.mem_singleton_iff.1 hw, ← hcz]
  have h1 : (⟨q, hq⟩ : ↥Q) * c = c * ⟨q, hq⟩ := Subgroup.mem_center_iff.1 hc ⟨q, hq⟩
  have h2 : q * (c : G) = (c : G) * q := congrArg Subtype.val h1
  exact h2.symm

theorem isElemAbelian_comm_gen {G : Type} [Group G] {p : ℕ} {E : Subgroup G}
    (hE : CFSG.Open.IsElemAbelian p E) {x y : G} (hx : x ∈ E) (hy : y ∈ E) : x * y = y * x :=
  congrArg Subtype.val (hE.1.is_comm.comm (⟨x, hx⟩ : E) ⟨y, hy⟩)

theorem mem_normalizer_of_elemAb {G : Type} [Group G] [Finite G] {p : ℕ} {A B : Subgroup G}
    (hA : CFSG.Open.IsElemAbelian p A) (hBA : B ≤ A) {x : G} (hx : x ∈ A) :
    x ∈ Subgroup.normalizer (B : Set G) := by
  apply mem_normalizer_of_conj_inv_mem B x
  intro y hy
  have hc : x * y = y * x := isElemAbelian_comm_gen hA hx (hBA hy)
  have hx' : x⁻¹ * y * x = y := by
    rw [mul_assoc, ← hc, ← mul_assoc, inv_mul_cancel, one_mul]
  rw [hx']
  exact hy

theorem join_zpowers_isElemAbelian_gen {G : Type} [Group G] {p : ℕ} {C : Subgroup G} {x : G}
    (hC : CFSG.Open.IsElemAbelian p C) (hxp : x ^ p = 1) (hCx : ∀ c ∈ C, c * x = x * c) :
    CFSG.Open.IsElemAbelian p (C ⊔ Subgroup.zpowers x : Subgroup G) := by
  haveI : CFSG.IsElementaryAbelian p C :=
    (CFSG.SectionRank.isElementaryAbelian_iff_isElemAbelian p C).2 hC
  haveI : CFSG.IsElementaryAbelian p (Subgroup.zpowers x) :=
    CFSG.IsElementaryAbelian.zpowers_of_pow_eq_one hxp
  have hle : Subgroup.zpowers x ≤ Subgroup.centralizer (C : Set G) := by
    rw [Subgroup.zpowers_le]
    exact Subgroup.mem_centralizer_iff.2 fun c hc => hCx c hc
  have hY : CFSG.IsElementaryAbelian p (C ⊔ Subgroup.zpowers x : Subgroup G) :=
    CFSG.IsElementaryAbelian.sup_of_le_centralizer hle
  exact (CFSG.SectionRank.isElementaryAbelian_iff_isElemAbelian p _).1 hY

theorem isPGroup_of_le_gen {G : Type} [Group G] {p : ℕ} {P Q : Subgroup G} (hPQ : P ≤ Q)
    (hQ : IsPGroup p ↥Q) : IsPGroup p ↥P := by
  intro g
  obtain ⟨k, hk⟩ := hQ ⟨(g : G), hPQ g.2⟩
  exact ⟨k, Subtype.ext (by simpa using congrArg Subtype.val hk)⟩

theorem exists_ne_one_of_pRank {G : Type} [Group G] [Finite G] {p k : ℕ} (hp : 1 < p)
    {A : Subgroup G} (hA : CFSG.Open.pRank p A = k) (hk : 0 < k) : ∃ x ∈ A, x ≠ 1 := by
  obtain ⟨E0, hE0A, -, hcard⟩ := exists_elemAb_pRank hp A
  rw [hA] at hcard
  by_contra hcon
  push Not at hcon
  have hbot : E0 = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    exact Subgroup.mem_bot.2 (hcon x (hE0A hx))
  rw [hbot, Subgroup.card_bot] at hcard
  have : 1 < p ^ k := Nat.one_lt_pow hk.ne' hp
  omega

@[expose] def Input1210b_wreath : Prop :=
  ∀ (G : Type) [Group G] [Finite G] {m p : ℕ} {B M E A N D : Subgroup G}
    (h : Cex127 G m p B M E A N D) {K : Subgroup G},
    Lemma129Common p M E A N K →
    ((∃ Q : ℕ, p ∣ Q - 1 ∧ IsLpType p Q (barOf p K)) ∨ (p = 5 ∧ IsSporType .Fi22 (barOf p K))) →
    Lemma129IvBData p N K E A →
    ∃ (F : Subgroup G) (a : G) (H : Subgroup G),
      IsEkIn p 2 A F ∧ a ∈ E ⊓ A ∧ A = F ⊔ Subgroup.zpowers a ∧
      CFSG.Open.IsElemAbelian p H ∧ F ≤ H ∧
      (∀ y ∈ E ⊓ A, ∀ x ∈ H, y * x * y⁻¹ ∈ H) ∧
      IsPGroup p ↥(H ⊔ (E ⊓ A)) ∧ ¬ H ≤ M ∧
      (∀ x ∈ A, x ∉ H → ∀ n ∈ H ⊔ (E ⊓ A), x * n = n * x → n ∈ A) ∧
      ∃ n ∈ H ⊔ (E ⊓ A), n ∈ Subgroup.normalizer ((E ⊓ A : Subgroup G) : Set G) ∧ n ∉ A

end CFSG.LocalAnalysis.GLTheoremB.MovingAround.Lemma1210

namespace CFSG.LocalAnalysis.GLTheoremB.MovingAround

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB Lemma1210

theorem lemma1210_b_of_inputs (hW : Input1210b_wreath) : Lemma1210_bStatement := by
  intro G _ _ m p B M E A N D h K hK hb
  have hpp : p.Prime := (h.toSec11.toSec10Fails.toSec10.standing.beta).1
  haveI : Fact p.Prime := ⟨hpp⟩
  obtain ⟨F, a, H, -, haEA, hAFa, hHe, hFH, -, hHp, hHM, hcentr, n0, hn0H, hn0N, hn0A⟩ :=
    hW G h hK hb.1 hb.2
  have h11 : Sec11 G m p B M E A := h.toSec11
  have hEA := lemma104_ii_holds h11.toSec10Fails h11.pair
  have hAe : CFSG.Open.IsElemAbelian p A := hEA.2.2.1
  have hAmax : ∀ S : Subgroup G, CFSG.Open.IsElemAbelian p S → A ≤ S → S = A :=
    fun S hS hAS => hEA.2.2.2 S le_top hS hAS
  have hA3 : CFSG.Open.pRank p A = 3 := hK.2.1.1
  have hE2 : CFSG.Open.pRank p (E ⊓ A) = 2 := hK.2.1.2
  have hN0M : Subgroup.normalizer ((E ⊓ A : Subgroup G) : Set G) ≤ M :=
    (normalizer_le_GLBCore' inf_le_left hE2.ge).trans h11.pair.1.1.2.clause_d
  have hAle : A ≤ H ⊔ (E ⊓ A) := by
    have haH : a ∈ H ⊔ (E ⊓ A) := (le_sup_right : E ⊓ A ≤ H ⊔ (E ⊓ A)) haEA
    have hsub : F ⊔ Subgroup.zpowers a ≤ H ⊔ (E ⊓ A) :=
      sup_le (hFH.trans le_sup_left) (Subgroup.zpowers_le.2 haH)
    exact (le_of_eq hAFa).trans hsub
  have hNp : IsPGroup p ↥(Subgroup.normalizer ((E ⊓ A : Subgroup G) : Set G) ⊓ (H ⊔ (E ⊓ A))) :=
    isPGroup_of_le_gen inf_le_right hHp
  have hNM : Subgroup.normalizer ((E ⊓ A : Subgroup G) : Set G) ⊓ (H ⊔ (E ⊓ A)) ≤ M :=
    inf_le_left.trans hN0M
  have hANg : A ≤ Subgroup.normalizer ((E ⊓ A : Subgroup G) : Set G) ⊓ (H ⊔ (E ⊓ A)) :=
    fun x hx => Subgroup.mem_inf.2 ⟨mem_normalizer_of_elemAb hAe inf_le_right hx, hAle hx⟩
  obtain ⟨R, hRM, hNR⟩ := Sec12c.exists_isSylowIn_above hNM hNp
  have hAR : A ≤ R := hANg.trans hNR
  have hAnt : ∃ x ∈ A, x ≠ 1 := exists_ne_one_of_pRank hpp.one_lt hA3 (by norm_num)
  have hne : ∃ x ∈ R, x ≠ 1 := by
    obtain ⟨x, hxA, hx1⟩ := hAnt
    exact ⟨x, hAR hxA, hx1⟩
  obtain ⟨z, hzR, hz3⟩ := exists_central_prime hRM.2.1 hne
  have hz1 : z ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at hz3
    exact hpp.one_lt.ne hz3
  have hzp : z ^ p = 1 := by
    rw [← hz3]
    exact pow_orderOf_eq_one z
  have hzc : ∀ c ∈ A, c * z = z * c := fun c hc =>
    (Subgroup.mem_centralizer_iff.1 (le_cg_of_mem_centerOf hzR (hAR hc)) z
      (Set.mem_singleton z)).symm
  have hSp := join_zpowers_isElemAbelian_gen hAe hzp hzc
  have hAz : A ⊔ Subgroup.zpowers z = A := hAmax _ hSp le_sup_left
  have hzA : z ∈ A := by
    have h1 : z ∈ A ⊔ Subgroup.zpowers z :=
      (le_sup_right : Subgroup.zpowers z ≤ A ⊔ Subgroup.zpowers z) (Subgroup.mem_zpowers z)
    rw [hAz] at h1
    exact h1
  have hzH : z ∈ H := by
    by_contra hzH
    have hn0R : n0 ∈ R := hNR (Subgroup.mem_inf.2 ⟨hn0N, hn0H⟩)
    have hcomm : z * n0 = n0 * z :=
      Subgroup.mem_centralizer_iff.1 (le_cg_of_mem_centerOf hzR hn0R) z (Set.mem_singleton z)
    exact hn0A (hcentr z hzA hzH n0 hn0H hcomm)
  have hHc : H ≤ Subgroup.centralizer ({z} : Set G) := by
    intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro w hw
    rw [Set.mem_singleton_iff.1 hw]
    exact isElemAbelian_comm_gen hHe hzH hx
  have hnotCg : ¬ Cg z ≤ M := fun hCM => hHM (hHc.trans hCM)
  exact ⟨z, hzA, hz1, ⟨R, hRM, hzR⟩, hnotCg⟩

end CFSG.LocalAnalysis.GLTheoremB.MovingAround
