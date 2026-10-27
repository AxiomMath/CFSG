module

public import CFSG.GH74.GLS.C3.Layer1.Thm1AutModel
public import CFSG.GH74.GLS.C3.Layer1.BackAction
public import CFSG.GH74.GLS.C3.Layer1.BackConj
public import CFSG.GH74.GLS.C3.Layer1.Back112Lift

public section

namespace CFSG.GH74.GLS.C3.Layer1.Thm1

open Subgroup CFSG CFSG.ABGLocalTools CFSG.GH74.GLS CFSG.GH74.GLS.IVK CFSG.GH74.GLS.C3.Layer1
open scoped commutatorElement

theorem card_eq_card_map_mul_card_inf_ker {X Y : Type*} [Group X] [Group Y] (f : X →* Y)
    (H : Subgroup X) : Nat.card ↥H = Nat.card ↥(H.map f) * Nat.card ↥(H ⊓ f.ker) := by
  have h := Subgroup.relIndex_mul_card f.ker H
  rw [Subgroup.relIndex_ker, inf_comm] at h
  exact h.symm

theorem isDihedralTwoGroup_of_equiv {X Y : Type} [Group X] [Group Y] (e : X ≃* Y) {n : ℕ}
    (h : IsDihedralTwoGroup Y n) : IsDihedralTwoGroup X n := by
  refine ⟨h.1, ?_⟩
  obtain ⟨k, hk, hk2, ⟨ψ⟩⟩ := h.2
  exact ⟨k, hk, hk2, ⟨e.trans ψ⟩⟩

theorem isSylowOf_map_hom {G G' : Type*} [Group G] [Group G'] [Finite G] {p : ℕ} [Fact p.Prime]
    (φ : G →* G') {P K : Subgroup G} (h : IsSylowOf p P K) :
    IsSylowOf p (P.map φ) (K.map φ) := by
  obtain ⟨Q, rfl⟩ := h
  let ψ : K →* K.map φ :=
    (φ.comp K.subtype).codRestrict (K.map φ) (fun x => ⟨x, x.2, rfl⟩)
  have hψ : Function.Surjective ψ := by
    rintro ⟨_, x, hx, rfl⟩
    exact ⟨⟨x, hx⟩, rfl⟩
  refine ⟨Q.mapSurjective hψ, ?_⟩
  rw [Sylow.coe_mapSurjective, Subgroup.map_map, Subgroup.map_map]
  rfl

@[expose] def CoreConcl {X : Type} [Group X] {A : Type} [Group A] (φ : X →* MulAut A)
    (T P : Subgroup X) : Prop :=
  ∃ f z : X, f ∈ T ∧ orderOf f = 2 ∧ (∀ p ∈ P, f * p = p * f) ∧ φ f ≠ 1 ∧
    P34.IsFAutL2A7 A (φ f) ∧ φ f ∉ innAut A ∧ (∃ n : ℕ, 3 ≤ n ∧ IsDihedralTwoGroup ↥P n) ∧
    z ∈ P ∧ orderOf z = 2 ∧ (∀ p ∈ P, z * p = p * z) ∧
    (∀ w ∈ P, (∀ p ∈ P, w * p = p * w) → w = 1 ∨ w = z) ∧
    (∀ f' ∈ T, orderOf f' = 2 → (∀ p ∈ P, f' * p = p * f') → φ f' ∉ innAut A →
      ∀ u ∈ P ⊔ zpowers f', orderOf u = 2 →
        ∃ g ∈ innAut A, g * φ u * g⁻¹ = φ z ∨ g * φ u * g⁻¹ = φ f' ∨ g * φ u * g⁻¹ = φ f' * φ z) ∧
    (∀ f' ∈ T, orderOf f' = 2 → (∀ p ∈ P, f' * p = p * f') → φ f' ∉ innAut A →
      P34.IsFAutL2A7 A (φ f')) ∧
    (∀ f' ∈ T, (∀ p ∈ P, f' * p = p * f') → φ f' ∈ innAut A → φ f' = 1 ∨
      (φ f' = φ z ∧ ∀ k₀ : A, (MulAut.conj k₀ : MulAut A) = φ z →
        Group.IsSolvable ↥(centralizer ({k₀} : Set A)))) ∧
    (∀ f' ∈ T, orderOf f' = 2 → (∀ p ∈ P, f' * p = p * f') → φ f' ∉ innAut A →
      GoodC A (φ f') ∨ (Nonempty (A ≃* alternatingGroup (Fin 7)) ∧ GoodC A (φ f' * φ z)))

theorem core_lift {X : Type} [Group X] [Finite X] {A : Type} [Group A] [Finite A] (φ : X →* MulAut A)
    (hAut : AutLevelF A) (T P E₁ : Subgroup X) (hT2 : IsPGroup 2 ↥T) (hPT : P ≤ T)
    (hPn : ∀ t ∈ T, ∀ p ∈ P, t * p * t⁻¹ ∈ P) (hPker : ∀ p ∈ P, φ p = 1 → p = 1)
    (hSyl : IsSylowOf 2 (P.map φ) (innAut A)) (hE₁T : E₁ ≤ T)
    (hE₁ : IsElementaryAbelian 2 ↥E₁) (hE₁16 : 16 ≤ Nat.card ↥E₁)
    (hker : Nat.card ↥(E₁ ⊓ φ.ker) ≤ 2) : CoreConcl φ T P := by
  unfold CoreConcl
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Finite (MulAut A) :=
    Finite.of_injective (fun σ : MulAut A => (σ : A → A)) (fun a b h => MulEquiv.ext (congrFun h))
  have hB2 : IsPGroup 2 ↥(T.map φ) :=
    hT2.of_surjective (φ.subgroupMap T) (φ.subgroupMap_surjective T)
  have hPB : P.map φ ≤ T.map φ ⊓ innAut A := le_inf (Subgroup.map_mono hPT) hSyl.le
  have hBinn : T.map φ ⊓ innAut A = P.map φ :=
    hSyl.eq_of_le hPB inf_le_right hB2.to_inf_left
  have hSylB : IsSylowOf 2 (T.map φ ⊓ innAut A) (innAut A) := by
    rw [hBinn]
    exact hSyl
  have hEB : E₁.map φ ≤ T.map φ := Subgroup.map_mono hE₁T
  have hE : IsElementaryAbelian 2 ↥(E₁.map φ) := by
    have := hE₁
    exact IsElementaryAbelian.map φ
  have hE8 : 8 ≤ Nat.card ↥(E₁.map φ) := by
    have h := card_eq_card_map_mul_card_inf_ker φ E₁
    by_contra hlt
    push Not at hlt
    have : Nat.card ↥(E₁.map φ) * Nat.card ↥(E₁ ⊓ φ.ker) ≤ 7 * 2 :=
      Nat.mul_le_mul (by omega) hker
    omega
  obtain ⟨σ, y, p, z, hy, hp, hσ, hσB, hσ2, hσc, hσF, hσinn, hdih, hzm, hz2, hzc, hzu, hfus, hFA,
      hsolv, hlay⟩ :=
    hAut _ hB2 hSylB _ hEB hE hE8
  obtain ⟨e₁, he₁, rfl⟩ := hy
  have hp' : p ∈ P.map φ := hBinn ▸ hp
  obtain ⟨p₀, hp₀, rfl⟩ := hp'
  have he₁T : e₁ ∈ T := hE₁T he₁
  have hp₀T : p₀ ∈ T := hPT hp₀
  have he₁sq : e₁ * e₁ = 1 := sq_eq_one_of_isElementaryAbelian' hE₁ e₁ he₁
  have he₁inv : e₁⁻¹ = e₁ := inv_eq_of_mul_eq_one_right he₁sq
  have htT : p₀⁻¹ * e₁ ∈ T := T.mul_mem (T.inv_mem hp₀T) he₁T
  have hφt : φ (p₀⁻¹ * e₁) = σ := by
    rw [map_mul, map_inv, hσ]
  have htt : (p₀⁻¹ * e₁) * (p₀⁻¹ * e₁) ∈ P := by
    have h1 : (p₀⁻¹ * e₁) * (p₀⁻¹ * e₁) = p₀⁻¹ * (e₁ * p₀⁻¹ * e₁⁻¹) := by
      rw [he₁inv]
      group
    rw [h1]
    exact P.mul_mem (P.inv_mem hp₀) (hPn e₁ he₁T _ (P.inv_mem hp₀))
  have hσσ : σ * σ = 1 := by
    have := pow_orderOf_eq_one σ
    rwa [hσ2, sq] at this
  have hφtt : φ ((p₀⁻¹ * e₁) * (p₀⁻¹ * e₁)) = 1 := by
    rw [map_mul, hφt, hσσ]
  have htt1 : (p₀⁻¹ * e₁) * (p₀⁻¹ * e₁) = 1 := hPker _ htt hφtt
  have hσ1 : σ ≠ 1 := fun h => by
    rw [h, orderOf_one] at hσ2
    omega
  have ht1 : p₀⁻¹ * e₁ ≠ 1 := fun h => hσ1 (by rw [← hφt, h, map_one])
  have ht2 : orderOf (p₀⁻¹ * e₁) = 2 := orderOf_eq_prime (by rw [sq]; exact htt1) ht1
  have htc : ∀ q ∈ P, (p₀⁻¹ * e₁) * q = q * (p₀⁻¹ * e₁) := by
    intro q hq
    have hc : (p₀⁻¹ * e₁) * q * (p₀⁻¹ * e₁)⁻¹ * q⁻¹ ∈ P :=
      P.mul_mem (hPn _ htT q hq) (P.inv_mem hq)
    have hqB : φ q ∈ T.map φ ⊓ innAut A := hBinn ▸ Subgroup.mem_map_of_mem φ hq
    have hcomm := hσc (φ q) hqB
    have hφc : φ ((p₀⁻¹ * e₁) * q * (p₀⁻¹ * e₁)⁻¹ * q⁻¹) = 1 := by
      rw [map_mul, map_mul, map_mul, hφt, map_inv, map_inv, hφt, hcomm]
      group
    have h1 := hPker _ hc hφc
    exact mul_inv_eq_iff_eq_mul.1 (mul_inv_eq_one.1 h1)
  have hinj : Function.Injective (φ.comp P.subtype) := by
    rw [injective_iff_map_eq_one]
    intro a ha
    exact Subtype.ext (hPker a a.2 ha)
  have hrange : (φ.comp P.subtype).range = P.map φ := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
  let e : ↥P ≃* ↥(T.map φ ⊓ innAut A) :=
    (MonoidHom.ofInjective hinj).trans (MulEquiv.subgroupCongr (hrange.trans hBinn.symm))
  obtain ⟨n, hn3, hn⟩ := hdih
  have hzP : z ∈ P.map φ := hBinn ▸ hzm
  obtain ⟨z₀, hz₀, rfl⟩ := hzP
  have hzz : φ z₀ * φ z₀ = 1 := by
    have := pow_orderOf_eq_one (φ z₀)
    rwa [hz2, sq] at this
  have hz₀2 : z₀ * z₀ = 1 := hPker _ (P.mul_mem hz₀ hz₀) (by rw [map_mul]; exact hzz)
  have hz₀1 : z₀ ≠ 1 := fun h => by
    rw [h, map_one, orderOf_one] at hz2
    omega
  have hz₀c : ∀ q ∈ P, z₀ * q = q * z₀ := by
    intro q hq
    have hc : z₀ * q * z₀⁻¹ * q⁻¹ ∈ P := P.mul_mem (hPn z₀ (hPT hz₀) q hq) (P.inv_mem hq)
    have hqB : φ q ∈ T.map φ ⊓ innAut A := hBinn ▸ Subgroup.mem_map_of_mem φ hq
    have hcomm := hzc (φ q) hqB
    have hφc : φ (z₀ * q * z₀⁻¹ * q⁻¹) = 1 := by
      rw [map_mul, map_mul, map_mul, map_inv, map_inv, hcomm]
      group
    have h1 := hPker _ hc hφc
    exact mul_inv_eq_iff_eq_mul.1 (mul_inv_eq_one.1 h1)
  have hzuP : ∀ w ∈ P, (∀ p ∈ P, w * p = p * w) → w = 1 ∨ w = z₀ := by
    intro w hw hwc
    have hwB : φ w ∈ T.map φ ⊓ innAut A := hBinn ▸ Subgroup.mem_map_of_mem φ hw
    have hwc' : ∀ q ∈ T.map φ ⊓ innAut A, φ w * q = q * φ w := by
      intro q hq
      obtain ⟨q₀, hq₀, rfl⟩ : q ∈ P.map φ := hBinn ▸ hq
      rw [← map_mul, ← map_mul, hwc q₀ hq₀]
    rcases hzu (φ w) hwB hwc' with h | h
    · exact Or.inl (hPker w hw h)
    · refine Or.inr ?_
      have h1 : w * z₀⁻¹ = 1 := hPker _ (P.mul_mem hw (P.inv_mem hz₀))
        (by rw [map_mul, map_inv, h]; group)
      exact mul_inv_eq_one.1 h1
  refine ⟨p₀⁻¹ * e₁, z₀, htT, ht2, htc, ?_, ?_, ?_, ⟨n, hn3, isDihedralTwoGroup_of_equiv e hn⟩, hz₀,
    orderOf_eq_prime (by rw [sq]; exact hz₀2) hz₀1, hz₀c, hzuP, ?_⟩
  · rw [hφt]
    exact hσ1
  · rw [hφt]
    exact hσF
  · rw [hφt]
    exact hσinn
  ·
    have hoc : ∀ f' ∈ T, orderOf f' = 2 → (∀ p ∈ P, f' * p = p * f') → φ f' ∉ innAut A →
        orderOf (φ f') = 2 ∧ ∀ q ∈ T.map φ ⊓ innAut A, φ f' * q = q * φ f' := by
      intro f' hf'T hf'2 hf'c hf'inn
      have hf'1 : φ f' ≠ 1 := fun h => hf'inn (h ▸ (innAut A).one_mem)
      have hff : f' * f' = 1 := by
        have := pow_orderOf_eq_one f'
        rwa [hf'2, sq] at this
      refine ⟨orderOf_eq_prime (by rw [sq, ← map_mul, hff, map_one]) hf'1, ?_⟩
      intro q hq
      obtain ⟨q₀, hq₀, rfl⟩ : q ∈ P.map φ := hBinn ▸ hq
      rw [← map_mul, ← map_mul, hf'c q₀ hq₀]
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro f' hf'T hf'2 hf'c hf'inn u hu hu2
      have hf'1 : φ f' ≠ 1 := fun h => hf'inn (h ▸ (innAut A).one_mem)
      have hff : f' * f' = 1 := by
        have := pow_orderOf_eq_one f'
        rwa [hf'2, sq] at this
      obtain ⟨hφf'2, hφf'c⟩ := hoc f' hf'T hf'2 hf'c hf'inn
      have hmem : φ u ∈ (T.map φ ⊓ innAut A) ⊔ zpowers (φ f') := by
        have h1 := Subgroup.mem_map_of_mem φ hu
        rw [Subgroup.map_sup, MonoidHom.map_zpowers, ← hBinn] at h1
        exact h1
      have huu : u * u = 1 := by
        have := pow_orderOf_eq_one u
        rwa [hu2, sq] at this
      have hφu1 : φ u ≠ 1 := by
        intro h1
        have hcomm : ∀ a ∈ P, ∀ b ∈ zpowers f', a * b = b * a := by
          intro a ha b hb
          obtain ⟨j, rfl⟩ := mem_zpowers_iff.1 hb
          exact (Commute.zpow_right (show Commute a f' from (hf'c a ha).symm) j).eq
        obtain ⟨a, ha, b, hb, hueq⟩ := Back.exists_mul_of_mem_sup_of_commute hcomm hu
        rcases mem_zpowers_of_mul_self hff hb with hb1 | hbf
        · rw [hueq, hb1, mul_one] at h1 hu2
          have := hPker a ha h1
          rw [this, orderOf_one] at hu2
          omega
        · rw [hueq, hbf, map_mul] at h1
          apply hf'inn
          have h2 : φ f' = (φ a)⁻¹ := eq_inv_of_mul_eq_one_right h1
          rw [h2]
          refine (innAut A).inv_mem ?_
          exact hSyl.le (Subgroup.mem_map_of_mem φ ha)
      have hφu2 : orderOf (φ u) = 2 :=
        orderOf_eq_prime (by rw [sq, ← map_mul, huu, map_one]) hφu1
      obtain ⟨g, hg, hgu⟩ := hfus (φ f') (Subgroup.mem_map_of_mem φ hf'T) hφf'2 hf'inn hφf'c (φ u)
        hmem hφu2
      exact ⟨g, hg, hgu⟩
    · intro f' hf'T hf'2 hf'c hf'inn
      obtain ⟨hφf'2, hφf'c⟩ := hoc f' hf'T hf'2 hf'c hf'inn
      exact hFA (φ f') (Subgroup.mem_map_of_mem φ hf'T) hφf'2 hf'inn hφf'c
    · intro f' hf'T hf'c hf'in
      have hmem : φ f' ∈ T.map φ ⊓ innAut A := ⟨Subgroup.mem_map_of_mem φ hf'T, hf'in⟩
      have hcent : ∀ q ∈ T.map φ ⊓ innAut A, φ f' * q = q * φ f' := by
        intro q hq
        obtain ⟨q₀, hq₀, rfl⟩ : q ∈ P.map φ := hBinn ▸ hq
        rw [← map_mul, ← map_mul, hf'c q₀ hq₀]
      rcases hzu (φ f') hmem hcent with h | h
      · exact Or.inl h
      · exact Or.inr ⟨h, hsolv⟩
    · intro f' hf'T hf'2 hf'c hf'inn
      obtain ⟨hφf'2, hφf'c⟩ := hoc f' hf'T hf'2 hf'c hf'inn
      exact hlay (φ f') (Subgroup.mem_map_of_mem φ hf'T) hφf'2 hf'inn hφf'c

theorem map_actHom_K {G : Type} [Group G] {C K : Subgroup G} (hKC : K ≤ C)
    (hKN : ∀ c ∈ C, ∀ k ∈ K, c * k * c⁻¹ ∈ K) :
    (K.subgroupOf C).map (Back.actHom hKN) = innAut (kBar K) := by
  ext a
  constructor
  · rintro ⟨m, hm, rfl⟩
    have hmK : (m : G) ∈ K := hm
    rw [show m = ⟨(m : G), m.2⟩ from rfl, Back.actHom_of_mem hKN hmK m.2]
    exact ⟨_, rfl⟩
  · rintro ⟨b, rfl⟩
    obtain ⟨⟨k, hk⟩, rfl⟩ := QuotientGroup.mk_surjective b
    exact ⟨⟨k, hKC hk⟩, hk, Back.actHom_of_mem hKN hk (hKC hk)⟩

theorem core_lift_G {G : Type} [Group G] [Finite G] {C K T E₁ : Subgroup G}
    (hKC : K ≤ C) (hKN : ∀ c ∈ C, ∀ k ∈ K, c * k * c⁻¹ ∈ K) (hT : IsSylowOf 2 T C)
    (hcen : Function.Injective (MulAut.conj : kBar K →* MulAut (kBar K)))
    (hAut : AutLevelF (kBar K)) (hE₁T : E₁ ≤ T) (hE₁ : IsElementaryAbelian 2 ↥E₁)
    (hE₁16 : 16 ≤ Nat.card ↥E₁)
    (hQ : ∀ A : Subgroup G, A ≤ CMK C K → IsElementaryAbelian 2 ↥A → Nat.card ↥A ≤ 2) :
    CoreConcl (Back.actHom hKN) (T.subgroupOf C) ((T ⊓ K).subgroupOf C) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hTC : T ≤ C := hT.le
  have hPC : T ⊓ K ≤ C := inf_le_right.trans hKC
  have hE₁C : E₁ ≤ C := hE₁T.trans hTC
  set φ := Back.actHom hKN with hφ
  have hT2 : IsPGroup 2 ↥(T.subgroupOf C) := hT.isPGroup.comap_subtype
  have hPT : (T ⊓ K).subgroupOf C ≤ T.subgroupOf C := fun a ha =>
    Subgroup.mem_subgroupOf.2 (Subgroup.mem_subgroupOf.1 ha).1
  have hPn : ∀ t ∈ T.subgroupOf C, ∀ p ∈ (T ⊓ K).subgroupOf C,
      t * p * t⁻¹ ∈ (T ⊓ K).subgroupOf C := by
    intro t ht p hp
    have ht' : (t : G) ∈ T := ht
    have hp' : (p : G) ∈ T ⊓ K := hp
    refine Subgroup.mem_subgroupOf.2 ⟨?_, ?_⟩
    · exact T.mul_mem (T.mul_mem ht' hp'.1) (T.inv_mem ht')
    · exact hKN t t.2 p hp'.2
  have hPker : ∀ p ∈ (T ⊓ K).subgroupOf C, φ p = 1 → p = 1 := by
    intro p hp hφp
    have hp' : (p : G) ∈ T ⊓ K := hp
    have h1 := Back.actHom_of_mem hKN hp'.2 p.2
    have h2 : (MulAut.conj (QuotientGroup.mk (⟨(p : G), hp'.2⟩ : ↥K) : kBar K)) = MulAut.conj 1 := by
      rw [map_one, ← h1]
      exact hφp
    have h3 := hcen h2
    have h4 : (⟨(p : G), hp'.2⟩ : ↥K) ∈ pPrimeCore 2 ↥K := (QuotientGroup.eq_one_iff _).1 h3
    have h5 : (p : G) ∈ pPrimeCoreOf 2 K := Back.Setup91.mem_pPrimeCoreOf_iff.2 ⟨hp'.2, h4⟩
    have h6 := Back.Setup91.inf_pPrimeCoreOf_eq_bot K hT.isPGroup
    have h7 : (p : G) ∈ T ⊓ pPrimeCoreOf 2 K := ⟨hp'.1, h5⟩
    rw [h6, Subgroup.mem_bot] at h7
    exact Subtype.ext h7
  have hSylK : IsSylowOf 2 ((T ⊓ K).subgroupOf C) (K.subgroupOf C) := by
    have hCN : C ≤ normalizer (K : Set G) := fun c hc => U1a.mem_normalizer_of_norm hKN hc
    have h := hT.inf_of_le_normalizer hKC hCN
    rw [← isSylowOf_map_subtype_iff C, Subgroup.subgroupOf_map_subtype,
      Subgroup.subgroupOf_map_subtype, inf_eq_left.2 hPC, inf_eq_left.2 hKC]
    exact h
  have hSyl : IsSylowOf 2 (((T ⊓ K).subgroupOf C).map φ) (innAut (kBar K)) := by
    have := isSylowOf_map_hom φ hSylK
    rwa [hφ, map_actHom_K hKC hKN] at this
  have hE₁T' : E₁.subgroupOf C ≤ T.subgroupOf C := fun a ha =>
    Subgroup.mem_subgroupOf.2 (hE₁T (Subgroup.mem_subgroupOf.1 ha))
  have hE₁' : IsElementaryAbelian 2 ↥(E₁.subgroupOf C) := by
    have := hE₁
    exact IsElementaryAbelian.subgroupOf hE₁C
  have hE₁16' : 16 ≤ Nat.card ↥(E₁.subgroupOf C) := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hE₁C).toEquiv]
    exact hE₁16
  have hker : Nat.card ↥(E₁.subgroupOf C ⊓ φ.ker) ≤ 2 := by
    have hinf : E₁.subgroupOf C ⊓ (CMK C K).subgroupOf C = (E₁ ⊓ CMK C K).subgroupOf C := by
      ext a
      simp [Subgroup.mem_subgroupOf]
    rw [hφ, Back.actHom_ker hKN, hinf]
    have hle : E₁ ⊓ CMK C K ≤ C := inf_le_left.trans hE₁C
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv]
    obtain ⟨hab, hsq⟩ := Back.forall_of_isElementaryAbelian hE₁
    exact hQ _ inf_le_right (Back.isElementaryAbelian_of_forall
      (fun u hu v hv => hab u hu.1 v hv.1) (fun u hu => hsq u hu.1))
  exact core_lift φ hAut (T.subgroupOf C) ((T ⊓ K).subgroupOf C) (E₁.subgroupOf C) hT2 hPT hPn hPker
    hSyl hE₁T' hE₁' hE₁16' hker

theorem transport_G {G : Type} [Group G] [Finite G] {C K T E₁ : Subgroup G} {x : G}
    (hKC : K ≤ C) (hKN : ∀ c ∈ C, ∀ k ∈ K, c * k * c⁻¹ ∈ K) (hT : IsSylowOf 2 T C)
    (hxC : x ∈ C) (hxK : ∀ k ∈ K, x * k = k * x)
    (hcen : Function.Injective (MulAut.conj : kBar K →* MulAut (kBar K)))
    (hAut : AutLevelF (kBar K)) (hE₁T : E₁ ≤ T) (hE₁ : IsElementaryAbelian 2 ↥E₁)
    (hE₁16 : 16 ≤ Nat.card ↥E₁)
    (hQ : ∀ A : Subgroup G, A ≤ CMK C K → IsElementaryAbelian 2 ↥A → Nat.card ↥A ≤ 2) :
    ∃ f z : G, f ∈ T ∧ orderOf f = 2 ∧ (∀ p ∈ T ⊓ K, f * p = p * f) ∧ f ≠ x ∧
      P34.InducesFAutL2A7 f K ∧ (∀ hfC : f ∈ C, Back.actHom hKN ⟨f, hfC⟩ ∉ innAut (kBar K)) ∧
      (∃ n : ℕ, 3 ≤ n ∧ IsDihedralTwoGroup ↥(T ⊓ K) n) ∧
      z ∈ T ⊓ K ∧ orderOf z = 2 ∧ (∀ p ∈ T ⊓ K, z * p = p * z) ∧
      ∀ w ∈ T ⊓ K, (∀ p ∈ T ⊓ K, w * p = p * w) → w = 1 ∨ w = z := by
  have hPC : T ⊓ K ≤ C := inf_le_right.trans hKC
  obtain ⟨f, z, hfT, hf2, hfc, hφf, hF, hFinn, ⟨n, hn3, hn⟩, hz, hz2, hzc, hzu, -⟩ :=
    core_lift_G hKC hKN hT hcen hAut hE₁T hE₁ hE₁16 hQ
  have hfT' : (f : G) ∈ T := hfT
  have hzT' : (z : G) ∈ T ⊓ K := hz
  refine ⟨f, z, hfT', by rw [Subgroup.orderOf_coe]; exact hf2, ?_, ?_, ?_, ?_, ?_, hzT', ?_, ?_, ?_⟩
  · intro p hp
    have := hfc ⟨p, hPC hp⟩ hp
    exact congrArg Subtype.val this
  · intro hfx
    apply hφf
    have : f = ⟨x, hxC⟩ := Subtype.ext hfx
    rw [this, Back.actHom_eq_one_iff_commutator_mem hKN]
    intro k hk
    have : ⁅k, x⁆ = 1 := by
      rw [commutatorElement_def, ← hxK k hk]
      group
    rw [this]
    exact (pPrimeCoreOf 2 K).one_mem
  · exact ⟨U1a.mem_normalizer_of_norm hKN f.2, hF⟩
  · intro hfC
    exact hFinn
  · exact ⟨n, hn3, isDihedralTwoGroup_of_equiv (Subgroup.subgroupOfEquivOfLe hPC).symm hn⟩
  · rw [Subgroup.orderOf_coe]; exact hz2
  · intro p hp
    have := hzc ⟨p, hPC hp⟩ hp
    exact congrArg Subtype.val this
  · intro w hw hwc
    have hw' : (⟨w, hPC hw⟩ : ↥C) ∈ (T ⊓ K).subgroupOf C := hw
    rcases hzu ⟨w, hPC hw⟩ hw' (fun q hq => by
      have hq' : (q : G) ∈ T ⊓ K := hq
      exact Subtype.ext (hwc q hq')) with h | h
    · exact Or.inl (congrArg Subtype.val h)
    · exact Or.inr (congrArg Subtype.val h)

theorem mem_pPrimeCoreOf_of_ker {G : Type} [Group G] {C K : Subgroup G} (hKC : K ≤ C)
    (hKN : ∀ c ∈ C, ∀ k ∈ K, c * k * c⁻¹ ∈ K)
    (hcen : Function.Injective (MulAut.conj : kBar K →* MulAut (kBar K))) {f : G} (hfC : f ∈ C)
    (hff : f * f = 1) (hfinn : Back.actHom hKN ⟨f, hfC⟩ ∉ innAut (kBar K)) :
    ∀ m ∈ K ⊔ zpowers f, ∀ hmC : m ∈ C, Back.actHom hKN ⟨m, hmC⟩ = 1 → m ∈ pPrimeCoreOf 2 K := by
  intro m hm hmC hφm
  have hle : zpowers f ≤ normalizer (K : Set G) :=
    (zpowers_le).2 (U1a.mem_normalizer_of_norm hKN hfC)
  have hm' : m ∈ ((K ⊔ zpowers f : Subgroup G) : Set G) := hm
  rw [Subgroup.coe_mul_of_right_le_normalizer_left K (zpowers f) hle] at hm'
  obtain ⟨k₁, hk₁, w, hw, hkw⟩ := hm'
  have hkw' : k₁ * w = m := hkw
  have hk₁C : k₁ ∈ C := hKC hk₁
  have hφk₁ : Back.actHom hKN ⟨k₁, hk₁C⟩ = MulAut.conj (QuotientGroup.mk (⟨k₁, hk₁⟩ : ↥K) : kBar K) :=
    Back.actHom_of_mem hKN hk₁ hk₁C
  rcases mem_zpowers_of_mul_self hff hw with hw1 | hwf
  · rw [hw1, mul_one] at hkw'
    subst hkw'
    have h2 : MulAut.conj (QuotientGroup.mk (⟨k₁, hk₁⟩ : ↥K) : kBar K) = MulAut.conj 1 := by
      rw [map_one, ← hφk₁]
      exact hφm
    have h3 := hcen h2
    exact Back.Setup91.mem_pPrimeCoreOf_iff.2 ⟨hk₁, (QuotientGroup.eq_one_iff _).1 h3⟩
  · exfalso
    apply hfinn
    have hmeq' : m = k₁ * f := by rw [← hkw', hwf]
    have hmeq : (⟨m, hmC⟩ : ↥C) = ⟨k₁, hk₁C⟩ * ⟨f, hfC⟩ := Subtype.ext hmeq'
    rw [hmeq, map_mul, hφk₁] at hφm
    have h2 : Back.actHom hKN ⟨f, hfC⟩ = (MulAut.conj (QuotientGroup.mk (⟨k₁, hk₁⟩ : ↥K) : kBar K))⁻¹ :=
      eq_inv_of_mul_eq_one_right hφm
    rw [h2]
    exact (innAut (kBar K)).inv_mem ⟨_, rfl⟩

theorem conj_of_same_image {G : Type} [Group G] [Finite G] {C K : Subgroup G} (hKC : K ≤ C)
    (hKN : ∀ c ∈ C, ∀ k ∈ K, c * k * c⁻¹ ∈ K)
    (hcen : Function.Injective (MulAut.conj : kBar K →* MulAut (kBar K))) {f : G} (hfC : f ∈ C)
    (hff : f * f = 1) (hfinn : Back.actHom hKN ⟨f, hfC⟩ ∉ innAut (kBar K)) {v w : G}
    (hvM : v ∈ K ⊔ zpowers f) (hwM : w ∈ K ⊔ zpowers f) (hv2 : orderOf v = 2)
    (hw2 : orderOf w = 2) (hvC : v ∈ C) (hwC : w ∈ C)
    (heq : Back.actHom hKN ⟨v, hvC⟩ = Back.actHom hKN ⟨w, hwC⟩) :
    ∃ h ∈ K ⊔ zpowers f, h⁻¹ * v * h = w := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set M : Subgroup G := K ⊔ zpowers f with hM
  have hKM : K ≤ M := le_sup_left
  have hMN : M ≤ normalizer (K : Set G) :=
    sup_le Subgroup.le_normalizer ((zpowers_le).2 (U1a.mem_normalizer_of_norm hKN hfC))
  have hnormal : (K.subgroupOf M).Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hKM).2 hMN
  have hcore : pPrimeCoreOf 2 K ≤ pPrimeCoreOf 2 M := pPrimeCoreOf_le_of_normal 2 hKM hnormal
  have hvwC : v * w⁻¹ ∈ C := C.mul_mem hvC (C.inv_mem hwC)
  have hbar : v * w⁻¹ ∈ pPrimeCoreOf 2 K := by
    refine mem_pPrimeCoreOf_of_ker hKC hKN hcen hfC hff hfinn (v * w⁻¹) (M.mul_mem hvM (M.inv_mem hwM))
      hvwC ?_
    have h1 : (⟨v * w⁻¹, hvwC⟩ : ↥C) = ⟨v, hvC⟩ * ⟨w, hwC⟩⁻¹ := rfl
    rw [h1, map_mul, map_inv, heq, mul_inv_cancel]
  have hbot : IsPGroup 2 ↥(⊥ : Subgroup G) := IsPGroup.of_card (n := 0) (by simp)
  obtain ⟨h, hh, -, hhvw⟩ := Back.exists_conj_centralizing (K := M) (Q := ⊥) hbot
    (fun q hq k hk => by rw [Subgroup.mem_bot.1 hq]; simpa using hk)
    (fun q hq k hk => by rw [Subgroup.mem_bot.1 hq]; simp only [commutatorElement_one_right]; exact (pPrimeCoreOf 2 M).one_mem)
    hvM hwM hv2 hw2 (fun q hq => by rw [Subgroup.mem_bot.1 hq]; simp)
    (fun q hq => by rw [Subgroup.mem_bot.1 hq]; simp)
    ⟨1, M.one_mem, by simpa using hcore hbar⟩
  exact ⟨h, hh, hhvw⟩

theorem transport_fusion_G {G : Type} [Group G] [Finite G] {C K T E₁ : Subgroup G}
    (hKC : K ≤ C) (hKN : ∀ c ∈ C, ∀ k ∈ K, c * k * c⁻¹ ∈ K) (hT : IsSylowOf 2 T C)
    (hcen : Function.Injective (MulAut.conj : kBar K →* MulAut (kBar K)))
    (hAut : AutLevelF (kBar K)) (hE₁T : E₁ ≤ T) (hE₁ : IsElementaryAbelian 2 ↥E₁)
    (hE₁16 : 16 ≤ Nat.card ↥E₁)
    (hQ : ∀ A : Subgroup G, A ≤ CMK C K → IsElementaryAbelian 2 ↥A → Nat.card ↥A ≤ 2)
    {f z : G} (hfT : f ∈ T) (hf2 : orderOf f = 2) (hfc : ∀ p ∈ T ⊓ K, f * p = p * f)
    (hfinn : ∀ hfC : f ∈ C, Back.actHom hKN ⟨f, hfC⟩ ∉ innAut (kBar K))
    (hz : z ∈ T ⊓ K) (hz2 : orderOf z = 2) (hzc : ∀ p ∈ T ⊓ K, z * p = p * z) :
    ∀ u ∈ T ⊓ K ⊔ zpowers f, orderOf u = 2 →
      ∃ g : G, g * u * g⁻¹ = z ∨ g * u * g⁻¹ = f ∨ g * u * g⁻¹ = f * z := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro u hu hu2
  have hPC : T ⊓ K ≤ C := inf_le_right.trans hKC
  have hfC : f ∈ C := hT.le hfT
  have hzC : z ∈ C := hPC hz
  have hff : f * f = 1 := by
    have := pow_orderOf_eq_one f
    rwa [hf2, sq] at this
  have hzz : z * z = 1 := by
    have := pow_orderOf_eq_one z
    rwa [hz2, sq] at this
  obtain ⟨f₁, z₁, -, -, -, -, -, -, -, hz₁, hz₁2, hz₁c, hz₁u, hfus, -, -⟩ :=
    core_lift_G hKC hKN hT hcen hAut hE₁T hE₁ hE₁16 hQ
  have hzP : (⟨z, hzC⟩ : ↥C) ∈ (T ⊓ K).subgroupOf C := hz
  have hzz₁ : (⟨z, hzC⟩ : ↥C) = z₁ := by
    rcases hz₁u ⟨z, hzC⟩ hzP (fun q hq => Subtype.ext (hzc (q : G) hq)) with h | h
    · exfalso
      have : z = 1 := congrArg Subtype.val h
      rw [this, orderOf_one] at hz2
      omega
    · exact h
  have hfCT : (⟨f, hfC⟩ : ↥C) ∈ T.subgroupOf C := hfT
  have hfC2 : orderOf (⟨f, hfC⟩ : ↥C) = 2 := by rw [Subgroup.orderOf_mk]; exact hf2
  have hfCc : ∀ p ∈ (T ⊓ K).subgroupOf C, (⟨f, hfC⟩ : ↥C) * p = p * ⟨f, hfC⟩ := by
    intro p hp
    exact Subtype.ext (hfc p hp)
  have huC : u ∈ C := by
    have hle : T ⊓ K ⊔ zpowers f ≤ C := sup_le hPC ((zpowers_le).2 hfC)
    exact hle hu
  have hmap : ((T ⊓ K).subgroupOf C ⊔ zpowers (⟨f, hfC⟩ : ↥C)).map C.subtype =
      T ⊓ K ⊔ zpowers f := by
    rw [Subgroup.map_sup, Subgroup.subgroupOf_map_subtype, inf_eq_left.2 hPC,
      MonoidHom.map_zpowers]
    rfl
  obtain ⟨u', hu', hu'u⟩ : ∃ u' ∈ (T ⊓ K).subgroupOf C ⊔ zpowers (⟨f, hfC⟩ : ↥C), (u' : G) = u := by
    rw [← hmap] at hu
    exact hu
  have hu'2 : orderOf u' = 2 := by rw [← Subgroup.orderOf_coe, hu'u]; exact hu2
  obtain ⟨g, hg, hgu⟩ := hfus ⟨f, hfC⟩ hfCT hfC2 hfCc (hfinn hfC) u' hu' hu'2
  rw [← map_actHom_K hKC hKN] at hg
  obtain ⟨k', hk', rfl⟩ := hg
  have hkK : (k' : G) ∈ K := hk'
  set k : G := (k' : G) with hk
  have hvC : k * u * k⁻¹ ∈ C := C.mul_mem (C.mul_mem k'.2 huC) (C.inv_mem k'.2)
  have hφv : Back.actHom hKN ⟨k * u * k⁻¹, hvC⟩ =
      Back.actHom hKN k' * Back.actHom hKN u' * (Back.actHom hKN k')⁻¹ := by
    rw [← map_inv, ← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (by simp [hk, hu'u])
  have hMu : u ∈ K ⊔ zpowers f := (sup_le_sup_right (inf_le_right : T ⊓ K ≤ K) _) hu
  have hMf : f ∈ K ⊔ zpowers f := Subgroup.mem_sup_right (mem_zpowers f)
  have hMz : z ∈ K ⊔ zpowers f := Subgroup.mem_sup_left hz.2
  have hMk : k ∈ K ⊔ zpowers f := Subgroup.mem_sup_left hkK
  have hMv : k * u * k⁻¹ ∈ K ⊔ zpowers f :=
    Subgroup.mul_mem _ (Subgroup.mul_mem _ hMk hMu) (Subgroup.inv_mem _ hMk)
  have hv2 : orderOf (k * u * k⁻¹) = 2 := by
    rw [← hu2]
    exact (MulAut.conj k).orderOf_eq u
  have hfzC : f * z ∈ C := C.mul_mem hfC hzC
  have hfz2 : orderOf (f * z) = 2 := by
    have hfz : f * z = z * f := hfc z hz
    have hφfz : Back.actHom hKN ⟨f * z, hfzC⟩ ∉ innAut (kBar K) := by
      intro h
      apply hfinn hfC
      have h1 : (⟨f * z, hfzC⟩ : ↥C) = ⟨f, hfC⟩ * ⟨z, hzC⟩ := rfl
      rw [h1, map_mul] at h
      have hφz : Back.actHom hKN ⟨z, hzC⟩ ∈ innAut (kBar K) := by
        rw [Back.actHom_of_mem hKN hz.2 hzC]
        exact ⟨_, rfl⟩
      have := (innAut (kBar K)).mul_mem h ((innAut (kBar K)).inv_mem hφz)
      simpa using this
    have hfz1 : f * z ≠ 1 := fun h => hφfz (by
      have : (⟨f * z, hfzC⟩ : ↥C) = 1 := Subtype.ext h
      rw [this, map_one]
      exact (innAut (kBar K)).one_mem)
    refine orderOf_eq_prime ?_ hfz1
    calc (f * z) ^ 2 = f * z * (f * z) := sq _
      _ = f * (z * f) * z := by simp only [mul_assoc]
      _ = f * (f * z) * z := by rw [← hfz]
      _ = (f * f) * (z * z) := by simp only [mul_assoc]
      _ = 1 := by rw [hff, hzz, one_mul]
  have hMfz : f * z ∈ K ⊔ zpowers f := Subgroup.mul_mem _ hMf hMz
  rw [← hzz₁] at hgu
  rcases hgu with h | h | h
  ·
    have heq : Back.actHom hKN ⟨k * u * k⁻¹, hvC⟩ = Back.actHom hKN ⟨z, hzC⟩ := by
      rw [hφv]; exact h
    obtain ⟨h₀, hh₀, hh₀v⟩ := conj_of_same_image hKC hKN hcen hfC hff (hfinn hfC) hMv hMz hv2 hz2 hvC hzC heq
    refine ⟨h₀⁻¹ * k, Or.inl ?_⟩
    rw [← hh₀v]
    group
  · have heq : Back.actHom hKN ⟨k * u * k⁻¹, hvC⟩ = Back.actHom hKN ⟨f, hfC⟩ := by
      rw [hφv]; exact h
    obtain ⟨h₀, hh₀, hh₀v⟩ := conj_of_same_image hKC hKN hcen hfC hff (hfinn hfC) hMv hMf hv2 hf2 hvC hfC heq
    refine ⟨h₀⁻¹ * k, Or.inr (Or.inl ?_)⟩
    rw [← hh₀v]
    group
  · have heq : Back.actHom hKN ⟨k * u * k⁻¹, hvC⟩ = Back.actHom hKN ⟨f * z, hfzC⟩ := by
      rw [hφv, h]
      have h1 : (⟨f * z, hfzC⟩ : ↥C) = ⟨f, hfC⟩ * ⟨z, hzC⟩ := rfl
      rw [h1, map_mul]
    obtain ⟨h₀, hh₀, hh₀v⟩ := conj_of_same_image hKC hKN hcen hfC hff (hfinn hfC) hMv hMfz hv2 hfz2 hvC hfzC heq
    refine ⟨h₀⁻¹ * k, Or.inr (Or.inr ?_)⟩
    rw [← hh₀v]
    group

theorem isSolvable_cent_of_inner {G : Type} [Group G] [Finite G] {C K : Subgroup G}
    (hKN : ∀ c ∈ C, ∀ k ∈ K, c * k * c⁻¹ ∈ K) {f : G} (hfC : f ∈ C)
    {k₀ : kBar K} (hφ : Back.actHom hKN ⟨f, hfC⟩ = MulAut.conj k₀)
    (hsolv : Group.IsSolvable ↥(centralizer ({k₀} : Set (kBar K)))) :
    Group.IsSolvable ↥(K ⊓ centralizer ({f} : Set G)) := by
  set H : Subgroup G := K ⊓ centralizer ({f} : Set G) with hH
  have hHK : H ≤ K := inf_le_left
  let ρ₀ : ↥H →* kBar K := (QuotientGroup.mk' (pPrimeCore 2 ↥K)).comp (Subgroup.inclusion hHK)
  have hρ₀ : ∀ h : ↥H, ρ₀ h = QuotientGroup.mk (⟨(h : G), hHK h.2⟩ : ↥K) := fun h => rfl
  have hrange : ∀ h : ↥H, ρ₀ h ∈ centralizer ({k₀} : Set (kBar K)) := by
    intro h
    rw [mem_centralizer_singleton_iff]
    have h1 := Back.actHom_mk hKN ⟨f, hfC⟩ ⟨(h : G), hHK h.2⟩
    have hfh : f * (h : G) * f⁻¹ = (h : G) := by
      have := mem_centralizer_singleton_iff.1 h.2.2
      rw [← this]
      group
    have h2 : Back.actHom hKN ⟨f, hfC⟩ (QuotientGroup.mk (⟨(h : G), hHK h.2⟩ : ↥K)) =
        QuotientGroup.mk (⟨(h : G), hHK h.2⟩ : ↥K) := by
      rw [h1]
      congr 1
      exact Subtype.ext hfh
    rw [hφ, MulAut.conj_apply] at h2
    rw [hρ₀]
    calc QuotientGroup.mk (⟨(h : G), hHK h.2⟩ : ↥K) * k₀
        = (k₀ * QuotientGroup.mk (⟨(h : G), hHK h.2⟩ : ↥K) * k₀⁻¹) * k₀ := by rw [h2]
      _ = k₀ * QuotientGroup.mk (⟨(h : G), hHK h.2⟩ : ↥K) := by group
  let ρ : ↥H →* ↥(centralizer ({k₀} : Set (kBar K))) := ρ₀.codRestrict _ hrange
  have hkerodd : Odd (Nat.card ↥ρ.ker) := by
    have hle : ρ.ker.map H.subtype ≤ pPrimeCoreOf 2 K := by
      rintro _ ⟨h, hh, rfl⟩
      have h0 : ρ₀ h = 1 := congrArg Subtype.val hh
      rw [hρ₀] at h0
      exact Back.Setup91.mem_pPrimeCoreOf_iff.2 ⟨hHK h.2, (QuotientGroup.eq_one_iff _).1 h0⟩
    have hdvd : Nat.card ↥(ρ.ker.map H.subtype) ∣ Nat.card ↥(pPrimeCoreOf 2 K) :=
      Subgroup.card_dvd_of_le hle
    rw [Subgroup.card_map_of_injective H.subtype_injective] at hdvd
    exact Odd.of_dvd_nat (TwoThin.card_pPrimeCoreOf_odd K) hdvd
  have hkersolv : Group.IsSolvable ↥ρ.ker := CFSG.FeitThompson.isSolvable_of_odd_natCard _ hkerodd
  exact Group.isSolvable_of_ker_le_range ρ.ker.subtype ρ (by simp)

end CFSG.GH74.GLS.C3.Layer1.Thm1
