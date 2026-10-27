module

public import CFSG.LieType.BorelTits.CentralQuotient
public import CFSG.CGT.PushingUpLit.CGT6.TwoFivePerm
import CFSG.LieType.Chevalley.EvenOddCentralizerRadicalGroup

public section

namespace CFSG.GroupTheory

open CFSG.Open Subgroup

variable {G : Type*} [Group G]

private theorem conj_facts {H : Subgroup G} {t : G} (ht : t ∈ H) (ht2 : t * t = 1)
    (hc : ∀ x ∈ H, x * t * x⁻¹ * t = t * (x * t * x⁻¹)) :
    (∀ y ∈ Group.conjugatesOfSet ({⟨t, ht⟩} : Set H), y * y = 1) ∧
      ∀ y ∈ Group.conjugatesOfSet ({⟨t, ht⟩} : Set H),
        ∀ z ∈ Group.conjugatesOfSet ({⟨t, ht⟩} : Set H), y * z = z * y := by
  constructor
  · intro y hy
    obtain ⟨a, ha, hay⟩ := Group.mem_conjugatesOfSet_iff.1 hy
    obtain ⟨c, rfl⟩ := isConj_iff.1 hay
    rw [Set.mem_singleton_iff] at ha
    subst ha
    apply Subtype.ext
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_one]
    calc (c : G) * t * (c : G)⁻¹ * ((c : G) * t * (c : G)⁻¹) = c * (t * t) * (c : G)⁻¹ := by
          group
      _ = 1 := by rw [ht2]; group
  · intro y hy z hz
    obtain ⟨a, ha, hay⟩ := Group.mem_conjugatesOfSet_iff.1 hy
    obtain ⟨c, rfl⟩ := isConj_iff.1 hay
    obtain ⟨b, hb, hbz⟩ := Group.mem_conjugatesOfSet_iff.1 hz
    obtain ⟨d, rfl⟩ := isConj_iff.1 hbz
    rw [Set.mem_singleton_iff] at ha hb
    subst ha hb
    apply Subtype.ext
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    have h := hc ((d : G)⁻¹ * c) (H.mul_mem (H.inv_mem d.2) c.2)
    calc (c : G) * t * (c : G)⁻¹ * ((d : G) * t * (d : G)⁻¹)
        = d * (((d : G)⁻¹ * c) * t * ((d : G)⁻¹ * c)⁻¹ * t) * (d : G)⁻¹ := by group
      _ = d * (t * (((d : G)⁻¹ * c) * t * ((d : G)⁻¹ * c)⁻¹)) * (d : G)⁻¹ := by rw [h]
      _ = (d : G) * t * (d : G)⁻¹ * ((c : G) * t * (c : G)⁻¹) := by group

theorem pCoreOf_ne_bot_of_commute_conj {H : Subgroup G} {t : G} (ht : t ∈ H) (ht1 : t ≠ 1)
    (ht2 : t * t = 1) (hc : ∀ x ∈ H, x * t * x⁻¹ * t = t * (x * t * x⁻¹)) :
    pCoreOf 2 H ≠ ⊥ := by
  obtain ⟨hinv, hcomm⟩ := conj_facts ht ht2 hc
  have hp : IsPGroup 2 (normalClosure ({⟨t, ht⟩} : Set H)) :=
    CFSG.CGT.PushingUpLit.CGT6.isPGroup_closure_of_commuting_involutions hinv hcomm
  have hN := CFSG.LieType.BorelTits.le_pCore 2 normalClosure_normal hp
  intro hbot
  have h1 : (pCore 2 H) = ⊥ := by
    rwa [pCoreOf, map_eq_bot_iff_of_injective _ H.subtype_injective] at hbot
  have h2 : (⟨t, ht⟩ : H) ∈ pCore 2 H := hN (subset_normalClosure rfl)
  rw [h1, mem_bot] at h2
  exact ht1 (congrArg Subtype.val h2)

theorem pCoreOf_centralizer_ne_bot_of_sq_mem_center [Finite G]
    (hZ : (Nat.card (center G)).Coprime 2) {ℓ : G} (hℓ : ℓ ∉ center G)
    (hℓ2 : ℓ ^ 2 ∈ center G) : pCoreOf 2 (centralizer ({ℓ} : Set G)) ≠ ⊥ := by
  let n := Nat.card (center G)
  let t := ℓ ^ n
  have hn : Odd n := Nat.Coprime.odd_of_right hZ
  obtain ⟨m, hm⟩ := hn
  have hsq : (ℓ ^ 2) ^ n = 1 := by
    have h := congrArg (fun y : center G => (y : G))
      (pow_card_eq_one' (G := center G) (x := ⟨ℓ ^ 2, hℓ2⟩))
    rw [Subgroup.coe_pow] at h
    exact h
  have ht2 : t * t = 1 := by
    change ℓ ^ n * ℓ ^ n = 1
    rw [← pow_add, ← two_mul, pow_mul]
    exact hsq
  have htm : ℓ = ((ℓ ^ 2) ^ m)⁻¹ * t := by
    change ℓ = ((ℓ ^ 2) ^ m)⁻¹ * ℓ ^ n
    rw [hm, pow_add, pow_mul, pow_one]
    group
  have ht1 : t ≠ 1 := by
    intro ht1
    apply hℓ
    have hℓeq : ℓ = ((ℓ ^ 2) ^ m)⁻¹ := by
      simpa only [ht1, mul_one] using htm
    rw [hℓeq]
    exact Subgroup.inv_mem (H := center G) (Subgroup.pow_mem (K := center G) hℓ2 m)
  have htmem : t ∈ centralizer ({ℓ} : Set G) := by
    rw [mem_centralizer_singleton_iff]
    change ℓ ^ n * ℓ = ℓ * ℓ ^ n
    exact (Commute.self_pow ℓ n).symm.eq
  have hc : ∀ x ∈ centralizer ({ℓ} : Set G),
      x * t * x⁻¹ * t = t * (x * t * x⁻¹) := by
    intro x hx
    have hxℓ : Commute x ℓ := mem_centralizer_singleton_iff.mp hx
    have hxt : Commute x t := hxℓ.pow_right n
    have hconj : x * t * x⁻¹ = t := by
      rw [hxt.eq]
      group
    rw [hconj]
  exact pCoreOf_ne_bot_of_commute_conj htmem ht1 ht2 hc

theorem pCoreOf_eqLocus_ne_bot_of_quotient [Finite G] (Z : Subgroup G) [Z.Normal]
    (hZ : Z ≤ center G) (hZ2 : (Nat.card Z).Coprime 2) {β : MulAut G} (hβ : β * β = 1)
    {γ : MulAut (G ⧸ Z)} (hγ : ∀ x : G, γ (QuotientGroup.mk' Z x) = QuotientGroup.mk' Z (β x))
    (h : pCoreOf 2 (γ.toMonoidHom.eqLocus (MonoidHom.id (G ⧸ Z))) ≠ ⊥) :
    pCoreOf 2 (β.toMonoidHom.eqLocus (MonoidHom.id G)) ≠ ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let π := QuotientGroup.mk' Z
  let Cbar := γ.toMonoidHom.eqLocus (MonoidHom.id (G ⧸ Z))
  let P := Cbar.comap π; let Q := pCoreOf 2 P; let E := β.toMonoidHom.eqLocus (MonoidHom.id G)
  have hQ1 : Q ≠ ⊥ := by
    intro hQbot
    refine h (le_antisymm ?_ bot_le)
    calc pCoreOf 2 Cbar ≤ Q.map π :=
          CFSG.LieType.BorelTits.pCoreOf_le_map_pCoreOf_comap Z hZ hZ2 Cbar
      _ = ⊥ := by rw [hQbot, Subgroup.map_bot]
  have hPβ : P.map β.toMonoidHom = P := by
    apply le_antisymm
    · rintro y ⟨x, hx, rfl⟩
      change γ (π (β x)) = π (β x)
      rw [← hγ x]
      exact congrArg γ (show γ (π x) = π x from hx)
    · intro x hx
      refine Subgroup.mem_map.mpr ⟨β x, ?_, ?_⟩
      · change γ (π (β x)) = π (β x)
        rw [← hγ x]
        exact congrArg γ (show γ (π x) = π x from hx)
      · exact congrArg (fun f : MulAut G => f x) hβ
  have hQβ : Q.map β.toMonoidHom = Q := by
    have hmap := CFSG.LieType.BorelTits.pCoreOf_map_mulEquiv 2 β P
    rw [hPβ] at hmap
    exact hmap.symm
  have hQp : IsPGroup 2 Q := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 P
  obtain ⟨b, hbQ, hb1, hbβ⟩ := CFSG.LieType.Chevalley.EvenOddRadical.exists_fixed_ne_one hQp hQ1
    β.toMonoidHom (fun x hx => hQβ.le (Subgroup.mem_map_of_mem β.toMonoidHom hx))
    (fun x _ => congrArg (fun f : MulAut G => f x) hβ)
  let T := Q ⊓ E
  have hEP : E ≤ P := by
    intro x hx
    change γ (π x) = π x
    rw [hγ x, show β x = x from hx]
  have hTp : IsPGroup 2 T :=
    (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 P).to_le inf_le_left
  have hEN : E ≤ Subgroup.normalizer (T : Set G) := fun x hx =>
    Subgroup.inf_normalizer_le_normalizer_inf (H := Q) (K := E)
      ⟨CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 P (hEP hx),
        Subgroup.le_normalizer (H := E) hx⟩
  have hbT : b ∈ T := ⟨hbQ, show b ∈ E from hbβ⟩
  have hbE : b ∈ pCoreOf 2 E :=
    CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 inf_le_right hEN hTp hbT
  exact fun hbot => hb1 (by rw [hbot, mem_bot] at hbE; exact hbE)

end CFSG.GroupTheory
