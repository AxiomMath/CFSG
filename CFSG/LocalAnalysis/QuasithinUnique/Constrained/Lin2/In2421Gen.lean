module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.General
import CFSG.GroupTheory.ElemAbelianClosure
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.Inputs

public section

namespace CFSG.QuasithinUnique.Lin2

open CFSG.Open CFSG.Quasithin
open scoped commutatorElement

section Gen

variable {G : Type*} [Group G]

theorem inf_ne_bot_of_cyclic_quotient [Finite G] {E P N : Subgroup G} (hEP : E ≤ P) (hNP : N ≤ P)
    (hN : P ≤ Subgroup.normalizer (N : Set G)) {t : G} (hT : P = N ⊔ Subgroup.zpowers t)
    (hE : IsElemAbelian 2 E) (hcard : 2 < Nat.card E) : E ⊓ N ≠ ⊥ := by
  intro hbot
  have := card_le_two_of_forall (A := E) (N := N) (fun a ha haN b hb hbN =>
    inv_mul_mem_of_sq_eq_one hNP hN hT (hEP ha) (hEP hb) (hE.2 a ha) (hE.2 b hb) haN hbN) hbot
  omega

theorem two_lt_card_inf_of_relIndex_two {E S₁ T₁ : Subgroup G} (hET : E ≤ T₁)
    (h2 : S₁.relIndex T₁ = 2) (hcard : 4 < Nat.card E) [Finite G] :
    2 < Nat.card (E ⊓ S₁ : Subgroup G) := by
  have h1 : S₁.relIndex E ≤ 2 := by
    have := Subgroup.relIndex_le_of_le_right (H := S₁) hET (by rw [h2]; norm_num)
    omega
  have h3 : (E ⊓ S₁ : Subgroup G).relIndex E = S₁.relIndex E := by
    have := Subgroup.inf_relIndex_right S₁ E
    rwa [inf_comm] at this
  have h4 : Nat.card E = Nat.card (E ⊓ S₁ : Subgroup G) * S₁.relIndex E := by
    rw [← h3]
    exact card_eq_mul_of_relIndex (inf_le_left : E ⊓ S₁ ≤ E)
  have h5 : Nat.card E ≤ Nat.card (E ⊓ S₁ : Subgroup G) * 2 := by
    rw [h4]; exact Nat.mul_le_mul_left _ h1
  omega

theorem inf_ne_bot_of_cyclic_quotient_index_two [Finite G] {E S₁ T₁ N : Subgroup G} (hET : E ≤ T₁)
    (h2 : S₁.relIndex T₁ = 2) (hNS : N ≤ S₁) (hN : S₁ ≤ Subgroup.normalizer (N : Set G)) {t : G}
    (hT : S₁ = N ⊔ Subgroup.zpowers t) (hE : IsElemAbelian 2 E) (hcard : 4 < Nat.card E) :
    E ⊓ N ≠ ⊥ := by
  have hE₁ : IsElemAbelian 2 (E ⊓ S₁ : Subgroup G) := IsElemAbelian.mono inf_le_left hE
  have := inf_ne_bot_of_cyclic_quotient (E := E ⊓ S₁) (P := S₁) (N := N) inf_le_right hNS hN hT
    hE₁ (two_lt_card_inf_of_relIndex_two hET h2 hcard)
  intro hbot
  apply this
  rw [eq_bot_iff]
  intro y hy
  have : y ∈ E ⊓ N := ⟨hy.1.1, hy.2⟩
  rwa [hbot] at this

theorem isPGroup_sup_of_le_normalizer [Finite G] {A B : Subgroup G}
    (hA : A ≤ Subgroup.normalizer (B : Set G)) (hpA : IsPGroup 2 A) (hpB : IsPGroup 2 B) :
    IsPGroup 2 ↥(A ⊔ B) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨i, hi⟩ := IsPGroup.iff_card.1 hpA
  obtain ⟨j, hj⟩ := IsPGroup.iff_card.1 hpB
  have h := card_sup_mul_card_inf hA
  have hdvd : Nat.card (A ⊔ B : Subgroup G) ∣ 2 ^ (i + j) := by
    refine ⟨Nat.card (A ⊓ B : Subgroup G), ?_⟩
    rw [pow_add, ← hi, ← hj]
    exact h.symm
  obtain ⟨m, -, hm⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hdvd
  exact IsPGroup.iff_card.2 ⟨m, hm⟩

theorem commutator_le_of_sup_commutative {R N H : Subgroup G} (hNR : N ≤ R) (hHR : H ≤ R)
    (hN : R ≤ Subgroup.normalizer (N : Set G)) (hR : R = N ⊔ H)
    (hHc : ∀ a ∈ H, ∀ b ∈ H, a * b = b * a) : ⁅R, R⁆ ≤ N := by
  have hnorm : (N.subgroupOf R).Normal := Subgroup.normal_subgroupOf_of_le_normalizer hN
  have hsup : N.subgroupOf R ⊔ H.subgroupOf R = ⊤ := by
    rw [← Subgroup.subgroupOf_sup hNR hHR, ← hR]
    exact Subgroup.subgroupOf_self R
  have hcomm : IsMulCommutative (H.subgroupOf R) :=
    ⟨⟨fun a b => Subtype.ext (Subtype.ext (hHc _ a.2 _ b.2))⟩⟩
  have hc := Subgroup.Normal.commutator_le_of_self_sup_commutative_eq_top hsup hcomm
  rw [Subgroup.commutator_le]
  intro x hx y hy
  have h1 : (⁅(⟨x, hx⟩ : R), (⟨y, hy⟩ : R)⁆ : R) ∈ commutator R := by
    rw [commutator_def]
    exact Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _)
  have h2 := hc h1
  rw [Subgroup.mem_subgroupOf] at h2
  have h3 : ((⁅(⟨x, hx⟩ : R), (⟨y, hy⟩ : R)⁆ : R) : G) = ⁅x, y⁆ := by
    simp [commutatorElement_def]
  rw [h3] at h2
  exact h2

theorem isElemAbelian_sup_commute {A B : Subgroup G} (hA : IsElemAbelian 2 A)
    (hB : IsElemAbelian 2 B) (hAB : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a) :
    IsElemAbelian 2 (A ⊔ B) := CFSG.Open.IsElemAbelian.sup_of_commute hA hB hAB

end Gen

section Fixed

variable {G : Type*} [Group G] [Finite G]

theorem card_le_sq_card_centralizer {V : Subgroup G} (hV : IsElemAbelian 2 V) {a : G}
    (hna : ∀ v ∈ V, a * v * a⁻¹ ∈ V) (ha2 : a ^ 2 = 1) :
    Nat.card V ≤ Nat.card (V ⊓ Subgroup.centralizer ({a} : Set G) : Subgroup G) ^ 2 := by
  classical
  set C : Subgroup G := V ⊓ Subgroup.centralizer ({a} : Set G) with hC
  have haa : a * a = 1 := by simpa [pow_two] using ha2
  let φ : V →* V :=
    { toFun := fun v => v * ⟨a * v * a⁻¹, hna v v.2⟩
      map_one' := by
        apply Subtype.ext
        simp
      map_mul' := by
        intro v w
        apply Subtype.ext
        simp only [Subgroup.coe_mul]
        have hc : (a * (v : G) * a⁻¹) * (w : G) = (w : G) * (a * (v : G) * a⁻¹) :=
          IsElemAbelian.comm hV (hna v v.2) w.2
        calc (v : G) * w * (a * ((v : G) * w) * a⁻¹)
            = (v : G) * (w * (a * v * a⁻¹)) * (a * w * a⁻¹) := by group
          _ = (v : G) * ((a * v * a⁻¹) * w) * (a * w * a⁻¹) := by rw [← hc]
          _ = ((v : G) * (a * v * a⁻¹)) * ((w : G) * (a * w * a⁻¹)) := by group }
  have hker : ∀ v : V, φ v = 1 → (v : G) ∈ C := by
    intro v hv
    have h1 : (v : G) * (a * v * a⁻¹) = 1 := by
      have := congrArg Subtype.val hv
      simpa [φ] using this
    have hv2 : (v : G) * v = 1 := by simpa [pow_two] using hV.2 v v.2
    have h2 : a * (v : G) * a⁻¹ = v := by
      have h3 : a * (v : G) * a⁻¹ = (v : G)⁻¹ := eq_inv_of_mul_eq_one_right h1
      rw [h3]
      exact inv_eq_of_mul_eq_one_right hv2
    refine ⟨v.2, ?_⟩
    show (v : G) ∈ Subgroup.centralizer ({a} : Set G)
    rw [Subgroup.mem_centralizer_singleton_iff]
    have : a * (v : G) = v * a := by
      calc a * (v : G) = (a * v * a⁻¹) * a := by group
        _ = v * a := by rw [h2]
    exact this.symm
  have hrange : ∀ y : V, y ∈ φ.range → (y : G) ∈ C := by
    intro y hy
    obtain ⟨v, rfl⟩ := hy
    refine ⟨(φ v).2, ?_⟩
    show ((φ v : V) : G) ∈ Subgroup.centralizer ({a} : Set G)
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hc : (a * (v : G) * a⁻¹) * (v : G) = (v : G) * (a * (v : G) * a⁻¹) :=
      IsElemAbelian.comm hV (hna v v.2) v.2
    have e : a * ((v : G) * (a * v * a⁻¹)) * a⁻¹ = (v : G) * (a * v * a⁻¹) := by
      calc a * ((v : G) * (a * v * a⁻¹)) * a⁻¹
          = (a * v * a⁻¹) * (a * a * v * a⁻¹ * a⁻¹) := by group
        _ = (a * v * a⁻¹) * v := by
            have h2 : a * a * (v : G) * a⁻¹ * a⁻¹ = v := by
              calc a * a * (v : G) * a⁻¹ * a⁻¹ = (a * a) * v * (a * a)⁻¹ := by group
                _ = v := by rw [haa]; simp
            rw [h2]
        _ = (v : G) * (a * v * a⁻¹) := hc
    have : a * ((φ v : V) : G) = ((φ v : V) : G) * a := by
      have h := e
      calc a * ((φ v : V) : G) = (a * ((φ v : V) : G) * a⁻¹) * a := by group
        _ = ((φ v : V) : G) * a := by
          show (a * ((v : G) * (a * v * a⁻¹)) * a⁻¹) * a = ((v : G) * (a * v * a⁻¹)) * a
          rw [h]
    exact this.symm
  have hk : Nat.card φ.ker ≤ Nat.card C := by
    refine Nat.card_le_card_of_injective (fun v => ⟨((v : V) : G), hker v v.2⟩) ?_
    intro v w hvw
    apply Subtype.ext
    apply Subtype.ext
    simpa using hvw
  have hr : Nat.card φ.range ≤ Nat.card C := by
    refine Nat.card_le_card_of_injective (fun y => ⟨((y : V) : G), hrange y y.2⟩) ?_
    intro v w hvw
    apply Subtype.ext
    apply Subtype.ext
    simpa using hvw
  have hmul : Nat.card φ.ker * φ.ker.index = Nat.card V := Subgroup.card_mul_index φ.ker
  rw [Subgroup.index_ker] at hmul
  rw [← hmul, sq]
  exact Nat.mul_le_mul hk hr

end Fixed

section KL

variable {G : Type} [Group G] [Finite G]

theorem commute_of_centralizes_TI (hTIA : TIAbelianTwoGroupCommute) {Z : Subgroup G}
    (hZ : IsElemAbelian 2 Z) (hTI : fusionIsTI Z) {w : G} (hw : w ∈ Z) (hw1 : w ≠ 1) {g : G}
    (hg : conjR Z g ≤ Subgroup.centralizer ({w} : Set G)) : ⁅conjR Z g, Z⁆ = ⊥ := by
  have hZgel : IsElemAbelian 2 (conjR Z g) := (isElemAbelian_conjR_iff Z g).2 hZ
  have hN : conjR Z g ≤ Subgroup.normalizer (Z : Set G) :=
    hg.trans (centralizer_le_normalizer_of_TI hTI hw hw1)
  have hp2 : IsPGroup 2 Z := fun x => ⟨1, Subtype.ext (by simpa using hZ.2 x x.2)⟩
  have hp2' : IsPGroup 2 (conjR Z g) := (isPGroup_conjR_iff 2).2 hp2
  have hZgcard : Nat.card (conjR Z g) = Nat.card Z := card_conjR Z g
  refine hTIA G (conjR Z g) Z hZgel hZ hZgcard (fusionIsTI_conjR hTI g) hTI ?_
    (isPGroup_sup_of_le_normalizer hN hp2' hp2) ?_
  · intro h hne
    have := fusionIsTI_iff_conjR.1 (fusionIsTI_conjR hTI g) (g⁻¹ * h)
      (by rwa [conjR_conjR, mul_inv_cancel_left])
    rw [conjR_conjR, mul_inv_cancel_left] at this
    rwa [inf_comm]
  · intro hbot
    have h1 : conjR Z g ⊓ Subgroup.normalizer (Z : Set G) = conjR Z g := inf_eq_left.2 hN
    rw [h1] at hbot
    have hZb : Z = ⊥ := conjR_eq_bot_iff.1 hbot
    rw [hZb, Subgroup.mem_bot] at hw
    exact hw1 hw

end KL

end CFSG.QuasithinUnique.Lin2
