module

public import CFSG.Goldschmidt.StatementsH
import CFSG.Goldschmidt.Steps.Components
import CFSG.LocalAnalysis.RankThreeCoreUniqueness.LocalCore
public import CFSG.Goldschmidt.Statements

public section

namespace CFSG.Goldschmidt

open CFSG.Open CFSG.ComponentClassification

section Act

variable {G : Type*} [Group G]

private theorem comm_of_mem_isMulCommutative {H : Subgroup G} (hH : IsMulCommutative H) {x y : G}
    (hx : x ∈ H) (hy : y ∈ H) : x * y = y * x :=
  congrArg Subtype.val (hH.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)

private theorem act_mul {L : Subgroup G} {y₁ y₂ ℓ₁ ℓ₂ : G} (hℓ₁ : ℓ₁ ∈ L)
    (h₁ : ∀ x ∈ L, y₁⁻¹ * x * y₁ = ℓ₁⁻¹ * x * ℓ₁) (h₂ : ∀ x ∈ L, y₂⁻¹ * x * y₂ = ℓ₂⁻¹ * x * ℓ₂) :
    ∀ x ∈ L, (y₁ * y₂)⁻¹ * x * (y₁ * y₂) = (ℓ₁ * ℓ₂)⁻¹ * x * (ℓ₁ * ℓ₂) := by
  intro x hx
  have hx' : ℓ₁⁻¹ * x * ℓ₁ ∈ L := L.mul_mem (L.mul_mem (L.inv_mem hℓ₁) hx) hℓ₁
  calc (y₁ * y₂)⁻¹ * x * (y₁ * y₂) = y₂⁻¹ * (y₁⁻¹ * x * y₁) * y₂ := by group
    _ = y₂⁻¹ * (ℓ₁⁻¹ * x * ℓ₁) * y₂ := by rw [h₁ x hx]
    _ = ℓ₂⁻¹ * (ℓ₁⁻¹ * x * ℓ₁) * ℓ₂ := h₂ _ hx'
    _ = (ℓ₁ * ℓ₂)⁻¹ * x * (ℓ₁ * ℓ₂) := by group

private theorem act_inv {L : Subgroup G} {y ℓ : G} (hℓ : ℓ ∈ L)
    (h : ∀ x ∈ L, y⁻¹ * x * y = ℓ⁻¹ * x * ℓ) : ∀ x ∈ L, y⁻¹⁻¹ * x * y⁻¹ = ℓ⁻¹⁻¹ * x * ℓ⁻¹ := by
  intro x hx
  have h2 : y⁻¹ * (ℓ * x * ℓ⁻¹) * y = x := by
    rw [h _ (L.mul_mem (L.mul_mem hℓ hx) (L.inv_mem hℓ))]
    group
  calc y⁻¹⁻¹ * x * y⁻¹ = y⁻¹⁻¹ * (y⁻¹ * (ℓ * x * ℓ⁻¹) * y) * y⁻¹ := by rw [h2]
    _ = ℓ⁻¹⁻¹ * x * ℓ⁻¹ := by group

private theorem act_conj {L : Subgroup G} {y ℓ g : G} (hg : g ∈ L)
    (h : ∀ x ∈ L, y⁻¹ * x * y = ℓ⁻¹ * x * ℓ) :
    ∀ x ∈ L, (g⁻¹ * y * g)⁻¹ * x * (g⁻¹ * y * g) = (g⁻¹ * ℓ * g)⁻¹ * x * (g⁻¹ * ℓ * g) := by
  intro x hx
  calc (g⁻¹ * y * g)⁻¹ * x * (g⁻¹ * y * g) = g⁻¹ * (y⁻¹ * (g * x * g⁻¹) * y) * g := by group
    _ = g⁻¹ * (ℓ⁻¹ * (g * x * g⁻¹) * ℓ) * g := by
      rw [h _ (L.mul_mem (L.mul_mem hg hx) (L.inv_mem hg))]
    _ = (g⁻¹ * ℓ * g)⁻¹ * x * (g⁻¹ * ℓ * g) := by group

private theorem conj_eq_of_act {L : Subgroup G} {y ℓ g : G} (hg : g ∈ L)
    (h : ∀ x ∈ L, y⁻¹ * x * y = ℓ⁻¹ * x * ℓ) : g⁻¹ * y * g = y * ℓ⁻¹ * (g⁻¹ * ℓ * g) := by
  have hc : g * (y * ℓ⁻¹) = y * ℓ⁻¹ * g := by
    calc g * (y * ℓ⁻¹) = y * (y⁻¹ * g * y) * ℓ⁻¹ := by group
      _ = y * (ℓ⁻¹ * g * ℓ) * ℓ⁻¹ := by rw [h g hg]
      _ = y * ℓ⁻¹ * g := by group
  calc g⁻¹ * y * g = g⁻¹ * (y * ℓ⁻¹ * g) * (g⁻¹ * ℓ * g) := by group
    _ = g⁻¹ * (g * (y * ℓ⁻¹)) * (g⁻¹ * ℓ * g) := by rw [hc]
    _ = y * ℓ⁻¹ * (g⁻¹ * ℓ * g) := by group

private theorem act_pow {L : Subgroup G} {y ℓ : G} (hℓ : ℓ ∈ L)
    (h : ∀ x ∈ L, y⁻¹ * x * y = ℓ⁻¹ * x * ℓ) (m : ℕ) :
    ∀ x ∈ L, (y ^ m)⁻¹ * x * y ^ m = (ℓ ^ m)⁻¹ * x * ℓ ^ m := by
  induction m with
  | zero => intro x _; simp
  | succ m ih =>
    intro x hx
    rw [pow_succ, pow_succ]
    exact act_mul (L.pow_mem hℓ m) ih h x hx

private theorem mul_inv_mem_centralizer_of_act {L : Subgroup G} {y ℓ : G}
    (h : ∀ x ∈ L, y⁻¹ * x * y = ℓ⁻¹ * x * ℓ) : y * ℓ⁻¹ ∈ Subgroup.centralizer (L : Set G) := by
  rw [Subgroup.mem_centralizer_iff]
  intro x hx
  calc x * (y * ℓ⁻¹) = y * (y⁻¹ * x * y) * ℓ⁻¹ := by group
    _ = y * (ℓ⁻¹ * x * ℓ) * ℓ⁻¹ := by rw [h x hx]
    _ = y * ℓ⁻¹ * x := by group

private theorem coe_mem_centralizer_of_mem_center {L : Subgroup G} {z : L}
    (hz : z ∈ Subgroup.center L) : (z : G) ∈ Subgroup.centralizer (L : Set G) := by
  rw [Subgroup.mem_centralizer_iff]
  intro x hx
  exact congrArg Subtype.val (Subgroup.mem_center_iff.1 hz ⟨x, hx⟩)

private theorem mem_center_of_coe_mem_centralizer {L : Subgroup G} {z : L}
    (hz : (z : G) ∈ Subgroup.centralizer (L : Set G)) : z ∈ Subgroup.center L := by
  rw [Subgroup.mem_center_iff]
  intro x
  exact Subtype.ext (Subgroup.mem_centralizer_iff.1 hz x x.2)

private theorem mk_eq_of_act {L : Subgroup G} {ℓ₁ ℓ₂ : L}
    (h : ∀ x ∈ L, (ℓ₁ : G)⁻¹ * x * ℓ₁ = (ℓ₂ : G)⁻¹ * x * ℓ₂) :
    (ℓ₁ : L ⧸ Subgroup.center L) = (ℓ₂ : L ⧸ Subgroup.center L) := by
  rw [QuotientGroup.eq]
  apply mem_center_of_coe_mem_centralizer
  rw [Subgroup.mem_centralizer_iff]
  intro x hx
  have h1 := h ((ℓ₁ : G) * x * (ℓ₁ : G)⁻¹) (L.mul_mem (L.mul_mem ℓ₁.2 hx) (L.inv_mem ℓ₁.2))
  have h2 : x = (ℓ₂ : G)⁻¹ * ((ℓ₁ : G) * x * (ℓ₁ : G)⁻¹) * ℓ₂ := by rw [← h1]; group
  simp only [Subgroup.coe_mul, Subgroup.coe_inv]
  calc x * ((ℓ₁ : G)⁻¹ * ℓ₂)
      = (ℓ₁ : G)⁻¹ * ℓ₂ * ((ℓ₂ : G)⁻¹ * ((ℓ₁ : G) * x * (ℓ₁ : G)⁻¹) * ℓ₂) := by group
    _ = (ℓ₁ : G)⁻¹ * ℓ₂ * x := by rw [← h2]

private theorem act_of_mk_eq {L : Subgroup G} {ℓ₁ ℓ₂ : L}
    (h : (ℓ₁ : L ⧸ Subgroup.center L) = (ℓ₂ : L ⧸ Subgroup.center L)) :
    ∀ x ∈ L, (ℓ₁ : G)⁻¹ * x * ℓ₁ = (ℓ₂ : G)⁻¹ * x * ℓ₂ := by
  intro x hx
  have hc := coe_mem_centralizer_of_mem_center (QuotientGroup.eq.1 h)
  have hxl : (ℓ₁ : G)⁻¹ * x * ℓ₁ ∈ L := L.mul_mem (L.mul_mem (L.inv_mem ℓ₁.2) hx) ℓ₁.2
  have hcomm := Subgroup.mem_centralizer_iff.1 hc _ hxl
  simp only [Subgroup.coe_mul, Subgroup.coe_inv] at hcomm
  calc (ℓ₁ : G)⁻¹ * x * ℓ₁
      = ((ℓ₁ : G)⁻¹ * ℓ₂)⁻¹ * ((ℓ₁ : G)⁻¹ * ℓ₂ * ((ℓ₁ : G)⁻¹ * x * ℓ₁)) := by group
    _ = ((ℓ₁ : G)⁻¹ * ℓ₂)⁻¹ * (((ℓ₁ : G)⁻¹ * x * ℓ₁) * ((ℓ₁ : G)⁻¹ * ℓ₂)) := by rw [hcomm]
    _ = (ℓ₂ : G)⁻¹ * x * ℓ₂ := by group

private theorem sq_eq_one_of_mem_closure {k : Set G} (hk : ∀ x ∈ k, x ^ 2 = 1)
    (hcomm : IsMulCommutative (Subgroup.closure k)) {x : G} (hx : x ∈ Subgroup.closure k) :
    x ^ 2 = 1 := by
  induction hx using Subgroup.closure_induction with
  | mem x hx => exact hk x hx
  | one => exact one_pow 2
  | mul x y hx hy ihx ihy =>
    have hxy : Commute x y := comm_of_mem_isMulCommutative hcomm hx hy
    rw [hxy.mul_pow, ihx, ihy, one_mul]
  | inv x _ ih => rw [inv_pow, ih, inv_one]

private theorem exists_mem_ne_ne {H : Subgroup G} [Finite H] (h : 2 < Nat.card H) (u v : G) :
    ∃ w ∈ H, w ≠ u ∧ w ≠ v := by
  by_contra hcon
  push Not at hcon
  have hsub : (H : Set G) ⊆ {u, v} := fun w hw => by
    by_cases hwu : w = u
    · exact Or.inl hwu
    · exact Or.inr (hcon w hw hwu)
  have h1 : Nat.card H = (H : Set G).ncard := Nat.card_coe_set_eq (H : Set G)
  have h2 : (H : Set G).ncard ≤ ({u, v} : Set G).ncard := Set.ncard_le_ncard hsub (Set.toFinite _)
  have h3 : ({u, v} : Set G).ncard ≤ 2 :=
    (Set.ncard_insert_le u {v}).trans (by rw [Set.ncard_singleton])
  omega

end Act

section Sylow

private theorem exists_sylow_eq_subgroupOf {G : Type*} [Group G] [Finite G] (S : Sylow 2 G)
    {K : Subgroup G} (hK : K.IsSubnormal) :
    ∃ P : Sylow 2 K, (P : Subgroup K) = (S : Subgroup G).subgroupOf K := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨P, hP⟩ := CFSG.Walter.exists_sylow_map_eq_inf_of_isSubnormal S hK
  refine ⟨P, Subgroup.map_injective K.subtype_injective ?_⟩
  rw [hP, Subgroup.subgroupOf_map_subtype]

private theorem coe_mem_sylow_of_mem_center {G : Type} [Group G] [Finite G]
    (hO : goldschmidtOddCore G = ⊥) {K : Subgroup G} (hK : IsComponentOf K ⊤) (S : Sylow 2 G)
    {z : K} (hz : z ∈ Subgroup.center K) : (z : G) ∈ (S : Subgroup G) := by
  obtain ⟨-, hZE, -⟩ := N8d G hO
  have hzE : (z : G) ∈ goldschmidtLayer G := Layer.component_le hK z.2
  have hzc : (z : G) ∈ Subgroup.centralizer (Layer.subgroup G : Set G) :=
    ComponentAutomorphisms.center_le_layer_center K hK ⟨z, hz, rfl⟩
  have hzO : (z : G) ∈ CFSG.Open.pCore 2 G :=
    hZE ⟨⟨z, hzE⟩, Subgroup.mem_center_iff.2 fun e => Subtype.ext
      (Subgroup.mem_centralizer_iff.1 hzc e e.2), rfl⟩
  have := CFSG.RankThreeCoreUniqueness.Helpers.pCore_normal (G := G) 2
  exact (CFSG.RankThreeCoreUniqueness.Helpers.pCore_isPGroup 2).le_sylow_of_normal S hzO

private theorem mk_mem_map_iff {G : Type*} [Group G] {S K : Subgroup G}
    (hZS : ∀ z : K, z ∈ Subgroup.center K → (z : G) ∈ S) (k : K) :
    (k : K ⧸ Subgroup.center K) ∈ (S.subgroupOf K).map (QuotientGroup.mk' (Subgroup.center K)) ↔
      (k : G) ∈ S := by
  constructor
  · rintro ⟨k', hk', hkk'⟩
    have hc : k'⁻¹ * k ∈ Subgroup.center K := QuotientGroup.eq.1 hkk'
    have h2 : (k : G) = k' * ((k'⁻¹ * k : K) : G) := by simp
    rw [h2]
    exact S.mul_mem (Subgroup.mem_subgroupOf.1 hk') (hZS _ hc)
  · intro hk
    exact ⟨k, Subgroup.mem_subgroupOf.2 hk, rfl⟩

private theorem mk_sq_eq_one_iff {G : Type*} [Group G] {K : Subgroup G} (k : K) :
    (k : K ⧸ Subgroup.center K) ^ 2 = 1 ↔ (k : G) ^ 2 ∈ Subgroup.centralizer (K : Set G) := by
  rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]
  constructor
  · intro h
    simpa using coe_mem_centralizer_of_mem_center h
  · intro h
    exact mem_center_of_coe_mem_centralizer (by simpa using h)

end Sylow

theorem N17_of (h11b : S_N11b) : S_N17 := by
  intro G _ _ S A K hAS hAab hcl hO hK hKtype hind a ha
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : IsSimpleGroup (K ⧸ Subgroup.center K) := hK.2.2.2
  obtain ⟨PK, hPK⟩ := exists_sylow_eq_subgroupOf S
    (Components.mathlib_subnormal_of_chain hK.2.1 Subgroup.IsSubnormal.top)
  let T : Sylow 2 (K ⧸ Subgroup.center K) := PK.mapSurjective (QuotientGroup.mk'_surjective _)
  have hmemT : ∀ k : K, (k : K ⧸ Subgroup.center K) ∈ (T : Subgroup _) ↔
      (k : G) ∈ (S : Subgroup G) := by
    intro k
    rw [Sylow.coe_mapSurjective, hPK]
    exact mk_mem_map_iff (fun z hz => coe_mem_sylow_of_mem_center hO hK S hz) k
  have hcomm : IsMulCommutative (Omega1 (T : Subgroup (K ⧸ Subgroup.center K))) := by
    apply Subgroup.isMulCommutative_closure
    rintro s₁ ⟨hs₁T, hs₁2⟩ s₂ ⟨hs₂T, hs₂2⟩ -
    obtain ⟨k₁, rfl⟩ := QuotientGroup.mk_surjective s₁
    obtain ⟨k₂, rfl⟩ := QuotientGroup.mk_surjective s₂
    obtain ⟨a₁, ha₁, h₁⟩ :=
      hind.2 k₁ ⟨(hmemT k₁).1 hs₁T, k₁.2⟩ ((mk_sq_eq_one_iff k₁).1 hs₁2)
    obtain ⟨a₂, ha₂, h₂⟩ :=
      hind.2 k₂ ⟨(hmemT k₂).1 hs₂T, k₂.2⟩ ((mk_sq_eq_one_iff k₂).1 hs₂2)
    have h12 := act_mul k₁.2 h₁ h₂
    have h21 := act_mul k₂.2 h₂ h₁
    rw [comm_of_mem_isMulCommutative hAab ha₁ ha₂] at h12
    have heq : ((k₁ * k₂ : K) : K ⧸ Subgroup.center K) = ((k₂ * k₁ : K) : K ⧸ Subgroup.center K) :=
      mk_eq_of_act fun x hx => by
        push_cast
        rw [← h12 x hx, h21 x hx]
    show _ * _ = _ * _
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, heq]
  obtain ⟨h4, htrans⟩ := h11b (K ⧸ Subgroup.center K) hKtype T hcomm
  have hΩsq : ∀ w ∈ Omega1 (T : Subgroup (K ⧸ Subgroup.center K)), w ^ 2 = 1 :=
    fun w hw => sq_eq_one_of_mem_closure (fun x hx => hx.2) hcomm hw
  have hΩT : ∀ w ∈ Omega1 (T : Subgroup (K ⧸ Subgroup.center K)), w ∈ (T : Subgroup _) :=
    fun w hw => (Subgroup.closure_le _).2 (fun x hx => hx.1) hw
  obtain ⟨t, ⟨htS, htK⟩, ht2, hat⟩ := hind.1 a ha
  suffices hx : ∃ k : K, (k : G) ∈ A ∧
      (k : K ⧸ Subgroup.center K) = ((⟨t, htK⟩ : K) : K ⧸ Subgroup.center K) by
    obtain ⟨k, hkA, hk⟩ := hx
    refine ⟨k, ⟨hkA, k.2⟩, fun y hy => ?_⟩
    rw [hat y hy]
    exact (act_of_mk_eq hk y hy).symm
  set v : K ⧸ Subgroup.center K := ((⟨t, htK⟩ : K) : K ⧸ Subgroup.center K) with hv
  have hvΩ : v ∈ Omega1 (T : Subgroup (K ⧸ Subgroup.center K)) :=
    Subgroup.subset_closure ⟨(hmemT _).2 htS, (mk_sq_eq_one_iff _).2 ht2⟩
  by_cases hv1 : v = 1
  · exact ⟨1, A.one_mem, by rw [hv1, QuotientGroup.mk_one]⟩
  obtain ⟨w, hwΩ, hw1, hwv⟩ :=
    exists_mem_ne_ne (H := Omega1 (T : Subgroup (K ⧸ Subgroup.center K))) (by omega) 1 v
  have hwvΩ : w * v ∈ Omega1 (T : Subgroup (K ⧸ Subgroup.center K)) :=
    Subgroup.mul_mem _ hwΩ hvΩ
  have hwv1 : w * v ≠ 1 := by
    intro h
    apply hwv
    have hv2 := hΩsq v hvΩ
    rw [sq] at hv2
    calc w = w * (v * v) := by rw [hv2, mul_one]
      _ = w * v * v := by rw [mul_assoc]
      _ = v := by rw [h, one_mul]
  obtain ⟨n, -, hn⟩ := htrans w hwΩ (w * v) hwvΩ hw1 hwv1
  obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective w
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective n
  have hyS : (y : G) ∈ (S : Subgroup G) := (hmemT y).1 (hΩT _ hwΩ)
  obtain ⟨a', ha', hact⟩ := hind.2 y ⟨hyS, y.2⟩ ((mk_sq_eq_one_iff y).1 (hΩsq _ hwΩ))
  have hconj : ((g⁻¹ * y * g : K) : K ⧸ Subgroup.center K) = (y : K ⧸ Subgroup.center K) * v := by
    rw [QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv, hn]
  have hyg : (g : G)⁻¹ * y * g ∈ (S : Subgroup G) := by
    have := (hmemT (g⁻¹ * y * g)).1 (by rw [hconj]; exact hΩT _ hwvΩ)
    simpa using this
  have hag : (g : G)⁻¹ * a' * g = a' * (y : G)⁻¹ * ((g : G)⁻¹ * y * g) :=
    conj_eq_of_act g.2 hact
  have hagA : (g : G)⁻¹ * a' * g ∈ A := by
    refine hcl a' ha' g ?_
    rw [hag]
    exact (S : Subgroup G).mul_mem
      ((S : Subgroup G).mul_mem (hAS ha') ((S : Subgroup G).inv_mem hyS)) hyg
  refine ⟨y⁻¹ * (g⁻¹ * y * g), ?_, ?_⟩
  · have h1 : ((y⁻¹ * (g⁻¹ * y * g) : K) : G) = a'⁻¹ * ((g : G)⁻¹ * a' * g) := by
      rw [hag]
      push_cast
      group
    rw [h1]
    exact A.mul_mem (A.inv_mem ha') hagA
  · rw [QuotientGroup.mk_mul, hconj, QuotientGroup.mk_inv, inv_mul_cancel_left]

section Induced

variable {G : Type*} [Group G]

private def actsInnerly (L : Subgroup G) : Subgroup G where
  carrier := {z | ∃ ℓ ∈ L, ∀ x ∈ L, z⁻¹ * x * z = ℓ⁻¹ * x * ℓ}
  one_mem' := ⟨1, L.one_mem, fun x _ => by group⟩
  mul_mem' := by
    rintro y₁ y₂ ⟨ℓ₁, hℓ₁, h₁⟩ ⟨ℓ₂, hℓ₂, h₂⟩
    exact ⟨ℓ₁ * ℓ₂, L.mul_mem hℓ₁ hℓ₂, act_mul hℓ₁ h₁ h₂⟩
  inv_mem' := by
    rintro y ⟨ℓ, hℓ, h⟩
    exact ⟨ℓ⁻¹, L.inv_mem hℓ, act_inv hℓ h⟩

private def induced (B L : Subgroup G) : Subgroup (L ⧸ Subgroup.center L) where
  carrier := {s | ∃ b ∈ B, ∃ ℓ : L, (ℓ : L ⧸ Subgroup.center L) = s ∧
    ∀ x ∈ L, b⁻¹ * x * b = (ℓ : G)⁻¹ * x * ℓ}
  one_mem' := ⟨1, B.one_mem, 1, rfl, fun x _ => by simp⟩
  mul_mem' := by
    rintro _ _ ⟨b₁, hb₁, ℓ₁, rfl, h₁⟩ ⟨b₂, hb₂, ℓ₂, rfl, h₂⟩
    exact ⟨b₁ * b₂, B.mul_mem hb₁ hb₂, ℓ₁ * ℓ₂, rfl, fun x hx => by
      rw [Subgroup.coe_mul]
      exact act_mul ℓ₁.2 h₁ h₂ x hx⟩
  inv_mem' := by
    rintro _ ⟨b, hb, ℓ, rfl, h⟩
    exact ⟨b⁻¹, B.inv_mem hb, ℓ⁻¹, rfl, fun x hx => by
      rw [Subgroup.coe_inv]
      exact act_inv ℓ.2 h x hx⟩

private theorem normal_of_le_actsInnerly {L : Subgroup G} (h : ⊤ ≤ actsInnerly L) : L.Normal :=
  ⟨fun x hx g => by
    obtain ⟨ℓ, hℓ, hact⟩ := h (Subgroup.mem_top g⁻¹)
    have := hact x hx
    rw [inv_inv] at this
    rw [this]
    exact L.mul_mem (L.mul_mem (L.inv_mem hℓ) hx) hℓ⟩

variable {Z : Type} [Group Z] [Finite Z]

private theorem top_le_actsInnerly {L : Subgroup Z} (hL : IsComponentOf L ⊤)
    (hZ2 : CFSG.Open.pCore 2 Z ≤ Subgroup.center Z)
    (hZE : CFSG.Open.pCore 2 Z ⊔ goldschmidtLayer Z = ⊤) : ⊤ ≤ actsInnerly L := by
  have hO2 : CFSG.Open.pCore 2 Z ≤ actsInnerly L := fun q hq =>
    ⟨1, L.one_mem, fun x _ => by
      have := Subgroup.mem_center_iff.1 (hZ2 hq) x
      calc q⁻¹ * x * q = q⁻¹ * (x * q) := by group
        _ = q⁻¹ * (q * x) := by rw [this]
        _ = 1⁻¹ * x * 1 := by group⟩
  have hE : goldschmidtLayer Z ≤ actsInnerly L := by
    refine sSup_le fun L' hL' => ?_
    by_cases hLL : L' = L
    · intro y hy
      rw [hLL] at hy
      exact ⟨y, hy, fun x _ => rfl⟩
    · intro y hy
      refine ⟨1, L.one_mem, fun x hx => ?_⟩
      have hc := Subgroup.commutator_eq_bot_iff_le_centralizer.1 (N8b Z L' L hL' hL hLL) hy
      have := Subgroup.mem_centralizer_iff.1 hc x hx
      calc y⁻¹ * x * y = y⁻¹ * (x * y) := by group
        _ = y⁻¹ * (y * x) := by rw [this]
        _ = 1⁻¹ * x * 1 := by group
  rw [← hZE]
  exact sup_le hO2 hE

private theorem pCore_le_center_of_le {B : Subgroup Z} (hBab : IsMulCommutative B)
    (hO2B : CFSG.Open.pCore 2 Z ≤ B) (hZE : CFSG.Open.pCore 2 Z ⊔ goldschmidtLayer Z = ⊤) :
    CFSG.Open.pCore 2 Z ≤ Subgroup.center Z := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hn := CFSG.RankThreeCoreUniqueness.Helpers.pCore_normal (G := Z) 2
  have := (CFSG.RankThreeCoreUniqueness.Helpers.pCore_isPGroup (G := Z) 2).isNilpotent
  have hEC : goldschmidtLayer Z ≤ Subgroup.centralizer (CFSG.Open.pCore 2 Z : Set Z) :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.1
      (Layer.commutes_with_solvable_subnormal (CFSG.Open.pCore 2 Z)
        (Components.chain_of_mathlib_subnormal hn.isSubnormal))
  intro q hq
  rw [Subgroup.mem_center_iff]
  intro z
  have hle : CFSG.Open.pCore 2 Z ⊔ goldschmidtLayer Z ≤ Subgroup.centralizer ({q} : Set Z) := by
    refine sup_le (fun y hy => ?_) (fun y hy => ?_)
    · rw [Subgroup.mem_centralizer_singleton_iff]
      exact comm_of_mem_isMulCommutative hBab (hO2B hy) (hO2B hq)
    · rw [Subgroup.mem_centralizer_singleton_iff]
      exact (Subgroup.mem_centralizer_iff.1 (hEC hy) q hq).symm
  rw [hZE] at hle
  exact Subgroup.mem_centralizer_singleton_iff.1 (hle (Subgroup.mem_top z))

private theorem pCore_eq_bot_of_simple {Q : Type*} [Group Q] [Finite Q] [IsSimpleGroup Q]
    [Group.IsPerfect Q] : CFSG.Open.pCore 2 Q = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have := CFSG.RankThreeCoreUniqueness.Helpers.pCore_normal (G := Q) 2
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (CFSG.Open.pCore 2 Q) with h | h
  · exact h
  · exfalso
    have hp : IsPGroup 2 Q := by
      have := CFSG.RankThreeCoreUniqueness.Helpers.pCore_isPGroup (G := Q) 2
      rw [h] at this
      exact this.of_equiv Subgroup.topEquiv
    have := hp.isNilpotent
    exact Group.IsPerfect.not_isSolvable Q inferInstance

private theorem inducesOmega1_of_core {n : ℕ} (hIH : IH n) (hZn : Nat.card Z < n)
    (P : Sylow 2 Z) {B : Subgroup Z} (hBP : B ≤ P) (hBab : IsMulCommutative B)
    (hBcl : fusionStronglyClosed (B : Set Z) (P : Subgroup Z))
    (htop : Subgroup.normalClosure (B : Set Z) = ⊤) (hO : goldschmidtOddCore Z = ⊥)
    (hZ2 : CFSG.Open.pCore 2 Z ≤ Subgroup.center Z)
    (hZE : CFSG.Open.pCore 2 Z ⊔ goldschmidtLayer Z = ⊤)
    {L : Subgroup Z} (hL : IsComponentOf L ⊤) : InducesOmega1 B L P := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : IsSimpleGroup (L ⧸ Subgroup.center L) := hL.2.2.2
  have hinner := top_le_actsInnerly hL hZ2 hZE
  have hLn : L.Normal := normal_of_le_actsInnerly hinner
  obtain ⟨PL, hPL⟩ := exists_sylow_eq_subgroupOf P hLn.isSubnormal
  let PLh : Sylow 2 (L ⧸ Subgroup.center L) := PL.mapSurjective (QuotientGroup.mk'_surjective _)
  have hmemP : ∀ k : L, (k : L ⧸ Subgroup.center L) ∈ (PLh : Subgroup _) ↔
      (k : Z) ∈ (P : Subgroup Z) := by
    intro k
    rw [Sylow.coe_mapSurjective, hPL]
    exact mk_mem_map_iff (fun z hz => coe_mem_sylow_of_mem_center hO hL P hz) k
  set Bh := induced B L with hBhdef
  have hBh2 : IsPGroup 2 Bh := by
    rintro ⟨_, b, hb, ℓ, rfl, h⟩
    obtain ⟨k, hk⟩ := P.isPGroup' ⟨b, hBP hb⟩
    refine ⟨k, Subtype.ext ?_⟩
    have hbk : b ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
    have h1 := act_pow ℓ.2 h (2 ^ k)
    rw [hbk] at h1
    have h2 : ((ℓ ^ 2 ^ k : L) : L ⧸ Subgroup.center L) = ((1 : L) : L ⧸ Subgroup.center L) :=
      mk_eq_of_act fun x hx => by
        have := h1 x hx
        simp only [inv_one, one_mul, mul_one] at this
        simp [← this]
    simpa using h2
  have hconjP : ∀ s ∈ Bh, ∀ u ∈ (PLh : Subgroup _), s * u * s⁻¹ ∈ (PLh : Subgroup _) := by
    rintro _ ⟨b, hb, ℓ, rfl, h⟩ u hu
    obtain ⟨k, rfl⟩ := QuotientGroup.mk_surjective u
    rw [← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, hmemP]
    rw [hmemP] at hu
    have h' := act_inv ℓ.2 h (k : Z) k.2
    simp only [inv_inv] at h'
    push_cast
    rw [← h']
    exact (P : Subgroup Z).mul_mem ((P : Subgroup Z).mul_mem (hBP hb) hu)
      ((P : Subgroup Z).inv_mem (hBP hb))
  have hBhN : Bh ≤ Subgroup.normalizer
      ((PLh : Subgroup (L ⧸ Subgroup.center L)) : Set (L ⧸ Subgroup.center L)) := by
    intro s hs
    rw [Subgroup.mem_normalizer_iff]
    intro u
    refine ⟨hconjP s hs u, fun hu => ?_⟩
    have := hconjP s⁻¹ (Bh.inv_mem hs) _ hu
    have e : s⁻¹ * (s * u * s⁻¹) * s⁻¹⁻¹ = u := by group
    rwa [e] at this
  have hBhP : Bh ≤ (PLh : Subgroup _) :=
    le_sup_left.trans (PLh.is_maximal' (hBh2.to_sup_of_normal_right' PLh.isPGroup' hBhN)
      le_sup_right).le
  have hBhab : IsMulCommutative Bh := ⟨⟨by
    rintro ⟨_, b₁, hb₁, ℓ₁, rfl, h₁⟩ ⟨_, b₂, hb₂, ℓ₂, rfl, h₂⟩
    apply Subtype.ext
    show (ℓ₁ : L ⧸ Subgroup.center L) * ℓ₂ = ℓ₂ * ℓ₁
    have h12 := act_mul ℓ₁.2 h₁ h₂
    have h21 := act_mul ℓ₂.2 h₂ h₁
    rw [comm_of_mem_isMulCommutative hBab hb₁ hb₂] at h12
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
    exact mk_eq_of_act fun x hx => by
      push_cast
      rw [← h12 x hx, h21 x hx]⟩⟩
  have hBhcl : fusionStronglyClosed (Bh : Set (L ⧸ Subgroup.center L)) (PLh : Subgroup _) := by
    rintro _ ⟨b, hb, ℓ, rfl, h⟩ gh hg
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective gh
    have hℓP : (ℓ : Z) ∈ (P : Subgroup Z) := (hmemP ℓ).1 (hBhP ⟨b, hb, ℓ, rfl, h⟩)
    rw [← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul] at hg ⊢
    have hgP : ((g⁻¹ * ℓ * g : L) : Z) ∈ (P : Subgroup Z) := (hmemP _).1 hg
    push_cast at hgP
    have hbg : (g : Z)⁻¹ * b * g = b * (ℓ : Z)⁻¹ * ((g : Z)⁻¹ * ℓ * g) := conj_eq_of_act g.2 h
    have hbgB : (g : Z)⁻¹ * b * g ∈ B := by
      refine hBcl b hb g ?_
      rw [hbg]
      exact (P : Subgroup Z).mul_mem
        ((P : Subgroup Z).mul_mem (hBP hb) ((P : Subgroup Z).inv_mem hℓP)) hgP
    refine ⟨(g : Z)⁻¹ * b * g, hbgB, g⁻¹ * ℓ * g, rfl, fun x hx => ?_⟩
    push_cast
    exact act_conj g.2 h x hx
  have hBhne : Bh ≠ ⊥ := by
    intro hbot
    have hBC : B ≤ Subgroup.centralizer (L : Set Z) := by
      intro b hb
      obtain ⟨ℓ, hℓ, h⟩ := hinner (Subgroup.mem_top b)
      have h1 : ((⟨ℓ, hℓ⟩ : L) : L ⧸ Subgroup.center L) ∈ Bh := ⟨b, hb, ⟨ℓ, hℓ⟩, rfl, h⟩
      rw [hbot, Subgroup.mem_bot] at h1
      have h2 := act_of_mk_eq (ℓ₁ := ⟨ℓ, hℓ⟩) (ℓ₂ := 1) (by rw [h1, QuotientGroup.mk_one])
      rw [Subgroup.mem_centralizer_iff]
      intro x hx
      have h3 := (h x hx).trans (h2 x hx)
      simp only [OneMemClass.coe_one, inv_one, one_mul, mul_one] at h3
      calc x * b = b * (b⁻¹ * x * b) := by group
        _ = b * x := by rw [h3]
    have hle : Subgroup.normalClosure (B : Set Z) ≤ Subgroup.centralizer (L : Set Z) :=
      Subgroup.normalClosure_le_normal hBC
    rw [htop] at hle
    obtain ⟨q, hq⟩ := exists_ne (1 : L ⧸ Subgroup.center L)
    obtain ⟨k, rfl⟩ := QuotientGroup.mk_surjective q
    exact hq ((QuotientGroup.eq_one_iff k).2
      (mem_center_of_coe_mem_centralizer (hle (Subgroup.mem_top _))))
  have hBhtop : Subgroup.normalClosure (Bh : Set (L ⧸ Subgroup.center L)) = ⊤ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal
      (Subgroup.normalClosure (Bh : Set (L ⧸ Subgroup.center L))) with h | h
    · have := Subgroup.le_normalClosure (H := Bh)
      rw [h] at this
      exact absurd (le_bot_iff.1 this) hBhne
    · exact h
  have hLhO : goldschmidtOddCore (L ⧸ Subgroup.center L) = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal
      (goldschmidtOddCore (L ⧸ Subgroup.center L)) with h | h
    · exact h
    · exfalso
      have hodd : Odd (Nat.card (L ⧸ Subgroup.center L)) := by
        have := OddCore.odd_card (L ⧸ Subgroup.center L)
        rwa [show componentClassificationOddCore (L ⧸ Subgroup.center L) = ⊤ from h,
          Subgroup.card_top] at this
      obtain ⟨k, hk⟩ := hBh2.exists_card_eq
      have hk0 : k ≠ 0 := by
        rintro rfl
        exact hBhne (Subgroup.eq_bot_of_card_eq _ (by simpa using hk))
      exact hodd.not_two_dvd_nat
        ((dvd_pow_self 2 hk0).trans (hk ▸ Subgroup.card_subgroup_dvd_card Bh))
  have hcard : Nat.card (L ⧸ Subgroup.center L) < n := by
    have h1 : Nat.card (L ⧸ Subgroup.center L) ≤ Nat.card L := by
      rw [← Subgroup.index_eq_card]
      exact Nat.le_of_dvd Nat.card_pos (Subgroup.index_dvd_card _)
    exact h1.trans_lt ((Subgroup.card_le_card_group L).trans_lt hZn)
  obtain ⟨hLa, hLb, -⟩ :=
    hIH (L ⧸ Subgroup.center L) hcard PLh Bh hBhP hBhab hBhcl hBhtop hLhO
  have : Group.IsPerfect L := ⟨hL.2.2.1⟩
  have : Group.IsPerfect (L ⧸ Subgroup.center L) :=
    Group.IsPerfect.ofSurjective (f := QuotientGroup.mk' (Subgroup.center L))
      (QuotientGroup.mk'_surjective _)
  have hO2 : CFSG.Open.pCore 2 (L ⧸ Subgroup.center L) = ⊥ := pCore_eq_bot_of_simple
  rw [hO2, bot_sup_eq] at hLa
  rw [hO2, hLa, bot_sup_eq] at hLb
  have hBhsq : ∀ s ∈ Bh, s ^ 2 = 1 := by
    intro s hs
    rw [hLb] at hs hBhab
    exact sq_eq_one_of_mem_closure (fun x hx => hx.2) hBhab hs
  have hBhΩ : ∀ s ∈ (PLh : Subgroup _), s ^ 2 = 1 → s ∈ Bh := by
    intro s hs hs2
    rw [hLb]
    exact Subgroup.subset_closure ⟨⟨hs, Subgroup.mem_top s⟩, hs2⟩
  refine ⟨fun a ha => ?_, fun t ht ht2 => ?_⟩
  · obtain ⟨ℓ, hℓ, h⟩ := hinner (Subgroup.mem_top a)
    have hs : ((⟨ℓ, hℓ⟩ : L) : L ⧸ Subgroup.center L) ∈ Bh := ⟨a, ha, ⟨ℓ, hℓ⟩, rfl, h⟩
    exact ⟨ℓ, ⟨(hmemP ⟨ℓ, hℓ⟩).1 (hBhP hs), hℓ⟩,
      (mk_sq_eq_one_iff ⟨ℓ, hℓ⟩).1 (hBhsq _ hs), h⟩
  · obtain ⟨htP, htL⟩ := ht
    obtain ⟨b, hb, ℓ, hℓ, h⟩ :=
      hBhΩ _ ((hmemP ⟨t, htL⟩).2 htP) ((mk_sq_eq_one_iff ⟨t, htL⟩).2 ht2)
    exact ⟨b, hb, fun x hx => (h x hx).trans (act_of_mk_eq hℓ x hx)⟩

end Induced

section Setup

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
private theorem exists_sylow_of_fusionIsSylowIn {T X : Subgroup G}
    (hTX : fusionIsSylowIn 2 T X) : ∃ P : Sylow 2 X, (P : Subgroup X) = T.subgroupOf X := by
  obtain ⟨hTX, hT, hmax⟩ := hTX
  refine ⟨⟨T.subgroupOf X, hT.comap_subtype, fun {Q} hQ hTQ => ?_⟩, rfl⟩
  have h1 := hmax (Q.map X.subtype) (Subgroup.map_subtype_le Q) (hQ.map X.subtype) fun s hs =>
    ⟨⟨s, hTX hs⟩, hTQ (show (⟨s, hTX hs⟩ : X) ∈ T.subgroupOf X from hs), rfl⟩
  rw [← h1]
  exact (Subgroup.comap_map_eq_self_of_injective X.subtype_injective Q).symm

private theorem sylow_inf_and_frattini {T X M : Subgroup G} (hMX : M ≤ X)
    (hMn : (M.subgroupOf X).Normal) (PX : Sylow 2 X) (hPX : (PX : Subgroup X) = T.subgroupOf X) :
    (∃ PM : Sylow 2 M, (PM : Subgroup M) = T.subgroupOf M) ∧
      ∀ x ∈ X, ∃ h ∈ X, (∀ y ∈ T ⊓ M, h * y * h⁻¹ ∈ T) ∧ ∃ m ∈ M, x = h * m := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨P', hP'⟩ := CFSG.Walter.exists_sylow_map_eq_inf_of_isSubnormal PX hMn.isSubnormal
  refine ⟨?_, fun x hx => ?_⟩
  · let e : (M.subgroupOf X) ≃* M := Subgroup.subgroupOfEquivOfLe hMX
    have he : Function.Surjective e.toMonoidHom := fun y => ⟨e.symm y, e.apply_symm_apply y⟩
    refine ⟨P'.mapSurjective he, ?_⟩
    rw [Sylow.coe_mapSurjective]
    apply Subgroup.map_injective M.subtype_injective
    have hcomp : M.subtype.comp e.toMonoidHom = X.subtype.comp (M.subgroupOf X).subtype := by
      ext y
      rfl
    rw [Subgroup.map_map, hcomp, ← Subgroup.map_map, hP',
      Subgroup.map_inf_eq _ _ X.subtype X.subtype_injective, hPX, Subgroup.subgroupOf_map_subtype,
      Subgroup.subgroupOf_map_subtype, Subgroup.subgroupOf_map_subtype, inf_of_le_left hMX,
      inf_assoc, inf_of_le_right hMX]
  · have hN := Sylow.normalizer_sup_eq_top P'
    rw [hP'] at hN
    have hmem : (⟨x, hx⟩ : X) ∈ Subgroup.normalizer
        (((PX : Subgroup X) ⊓ M.subgroupOf X : Subgroup X) : Set X) ⊔ M.subgroupOf X := by
      rw [hN]
      exact Subgroup.mem_top _
    obtain ⟨h, hh, m, hm, hhm⟩ := Subgroup.mem_sup_of_normal_right.1 hmem
    refine ⟨h, h.2, fun y hy => ?_, m, hm, (congrArg Subtype.val hhm).symm⟩
    have h1 : (⟨y, hMX hy.2⟩ : X) ∈ (PX : Subgroup X) ⊓ M.subgroupOf X :=
      ⟨by rw [hPX]; exact hy.1, hy.2⟩
    have h2 := ((Subgroup.mem_normalizer_iff.1 hh) _).1 h1
    rw [hPX] at h2
    exact h2.1

private theorem mem_normalizer_of_conj_le {S : Sylow 2 G} {A T : Subgroup G}
    (hcl : fusionStronglyClosed (A : Set G) (S : Subgroup G)) (hAT : A ≤ T) (hT : IsPGroup 2 T)
    {g : G} (hg : ∀ a ∈ A, g * a * g⁻¹ ∈ T) : g ∈ Subgroup.normalizer (A : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨Q, hTQ, hQ⟩ := stronglyClosed_of_le_pGroup S hcl hT hAT
  have hle : conjSub g⁻¹ A ≤ (Q : Subgroup G) := by
    intro x hx
    rw [mem_conjSub, inv_inv] at hx
    have h1 := hg _ hx
    have e : g * (g⁻¹ * x * g) * g⁻¹ = x := by group
    rw [e] at h1
    exact hTQ h1
  have heq := conj_eq_of_conj_le hQ hle
  rw [Subgroup.mem_normalizer_iff]
  intro y
  constructor
  · intro hy
    have h1 : g * y * g⁻¹ ∈ conjSub g⁻¹ A := by
      rw [mem_conjSub, inv_inv]
      have e : g⁻¹ * (g * y * g⁻¹) * g = y := by group
      rw [e]
      exact hy
    rwa [heq] at h1
  · intro hy
    rw [← heq, mem_conjSub, inv_inv] at hy
    have e : g⁻¹ * (g * y * g⁻¹) * g = y := by group
    rwa [e] at hy

private theorem c4_of_sup_eq_top {A M X : Subgroup G} (hAM : A ≤ M)
    (hMnX : ∀ x ∈ X, ∀ m ∈ M, x * m * x⁻¹ ∈ M) (hA2 : IsPGroup 2 A)
    (hsup : A.subgroupOf M ⊔ goldschmidtOddCore M = ⊤) :
    M = oddCoreOf M ⊔ A ∧ (⁅oddCoreOf M, A⁆ = ⊥ → X ≤ Subgroup.normalizer (A : Set G)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine ⟨?_, fun hcomm => ?_⟩
  · have h1 := congrArg (Subgroup.map M.subtype) hsup
    rw [Subgroup.map_sup, Subgroup.subgroupOf_map_subtype, inf_of_le_left hAM,
      ← MonoidHom.range_eq_map, Subgroup.range_subtype] at h1
    exact h1.symm.trans (sup_comm _ _)
  · have hcen : oddCoreOf M ≤ Subgroup.centralizer (A : Set G) :=
      Subgroup.commutator_eq_bot_iff_le_centralizer.1 hcomm
    have hodd : Odd (Nat.card (goldschmidtOddCore M)) := OddCore.odd_card M
    obtain ⟨e, he⟩ := hA2.exists_card_eq
    have hpow : ∀ a ∈ A, a ^ 2 ^ e = 1 := fun a ha => by
      rw [← he]
      exact congrArg Subtype.val (pow_card_eq_one' (x := (⟨a, ha⟩ : A)))
    have hkey : ∀ x ∈ X, ∀ a ∈ A, x * a * x⁻¹ ∈ A := by
      intro x hx a ha
      have hw : x * a * x⁻¹ ∈ M := hMnX x hx a (hAM ha)
      have hmem : (⟨x * a * x⁻¹, hw⟩ : M) ∈ A.subgroupOf M ⊔ goldschmidtOddCore M := by
        rw [hsup]
        exact Subgroup.mem_top _
      obtain ⟨a₀, ha₀, o₀, ho₀, heq⟩ := Subgroup.mem_sup_of_normal_right.1 hmem
      have heq' : (a₀ : G) * o₀ = x * a * x⁻¹ := congrArg Subtype.val heq
      have ha₀A : (a₀ : G) ∈ A := Subgroup.mem_subgroupOf.1 ha₀
      have hco : Commute (a₀ : G)⁻¹ (x * a * x⁻¹) := by
        have h1 : (a₀ : G) * o₀ = o₀ * a₀ :=
          Subgroup.mem_centralizer_iff.1 (hcen ⟨o₀, ho₀, rfl⟩) _ ha₀A
        rw [← heq']
        show (a₀ : G)⁻¹ * (a₀ * o₀) = a₀ * o₀ * (a₀ : G)⁻¹
        calc (a₀ : G)⁻¹ * (a₀ * o₀) = o₀ := by group
          _ = o₀ * a₀ * (a₀ : G)⁻¹ := by group
          _ = a₀ * o₀ * (a₀ : G)⁻¹ := by rw [h1]
      have ho₀2 : o₀ ^ 2 ^ e = 1 := by
        apply Subtype.ext
        have h1 : (o₀ : G) = (a₀ : G)⁻¹ * (x * a * x⁻¹) := by rw [← heq']; group
        rw [SubgroupClass.coe_pow, OneMemClass.coe_one, h1, hco.mul_pow, inv_pow, hpow _ ha₀A,
          conj_pow, hpow a ha]
        group
      have hord : orderOf o₀ = 1 := by
        have hcop : Nat.Coprime (2 ^ e) (Nat.card (goldschmidtOddCore M)) :=
          Nat.Coprime.pow_left e (Nat.coprime_two_left.2 hodd)
        exact Nat.dvd_one.1 (hcop.gcd_eq_one ▸ Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one ho₀2)
          (Subgroup.orderOf_dvd_natCard _ ho₀))
      rw [orderOf_eq_one_iff] at hord
      rw [← heq', hord, OneMemClass.coe_one, mul_one]
      exact ha₀A
    intro x hx
    rw [Subgroup.mem_normalizer_iff]
    intro y
    refine ⟨hkey x hx y, fun hy => ?_⟩
    have h1 := hkey x⁻¹ (X.inv_mem hx) _ hy
    have e : x⁻¹ * (x * y * x⁻¹) * x⁻¹⁻¹ = y := by group
    rwa [e] at h1

end Setup

theorem N16_of (h1 : S_N1) :
    ∀ n : ℕ, IH n → ∀ (G : Type) [Group G] [Finite G] (S : Sylow 2 G) (A X T : Subgroup G),
      A ≤ S → IsMulCommutative A → fusionStronglyClosed (A : Set G) (S : Subgroup G) → A ≤ T →
      fusionIsSylowIn 2 T X → Nat.card X < n →
      let M := normalClosureIn X A
      Conclusion M (T.subgroupOf M) (A.subgroupOf M) ∧
      M ⊔ (X ⊓ Subgroup.normalizer (A : Set G)) = X ∧
      CFSG.Open.pCore 2 (M ⧸ goldschmidtOddCore M) ≤ Subgroup.center (M ⧸ goldschmidtOddCore M) ∧
      (∀ L : Subgroup (M ⧸ goldschmidtOddCore M), IsComponentOf L ⊤ →
        InducesOmega1 (barOf M A) L (barOf M T)) ∧
      (goldschmidtLayer (M ⧸ goldschmidtOddCore M) = ⊥ →
        M = oddCoreOf M ⊔ A ∧ (⁅oddCoreOf M, A⁆ = ⊥ → X ≤ Subgroup.normalizer (A : Set G))) := by
  intro n hIH G _ _ S A X T hAS hAab hcl hAT hTX hXn M
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hTXle, hT2, -⟩ := id hTX
  have hAX : A ≤ X := hAT.trans hTXle
  have hMX : M ≤ X := Subgroup.map_subtype_le _
  have hMn : (M.subgroupOf X).Normal := by
    have hMsub : M.subgroupOf X =
        Subgroup.normalClosure ((A.subgroupOf X : Subgroup X) : Set X) :=
      Subgroup.comap_map_eq_self_of_injective X.subtype_injective _
    rw [hMsub]
    exact Subgroup.normalClosure_normal
  have hAM : A ≤ M := fun a ha =>
    ⟨⟨a, hAX ha⟩, Subgroup.subset_normalClosure (Subgroup.mem_subgroupOf.2 ha), rfl⟩
  have hMnX : ∀ x ∈ X, ∀ m ∈ M, x * m * x⁻¹ ∈ M := fun x hx m hm =>
    hMn.conj_mem ⟨m, hMX hm⟩ hm ⟨x, hx⟩
  obtain ⟨PX, hPX⟩ := exists_sylow_of_fusionIsSylowIn hTX
  obtain ⟨⟨PM, hPM⟩, hfrat⟩ := sylow_inf_and_frattini hMX hMn PX hPX
  have hdec : ∀ x ∈ X, ∃ h ∈ X ⊓ Subgroup.normalizer (A : Set G), ∃ m ∈ M, x = h * m := by
    intro x hx
    obtain ⟨h, hhX, hhT, m, hm, rfl⟩ := hfrat x hx
    exact ⟨h, ⟨hhX, mem_normalizer_of_conj_le hcl hAT hT2 fun a ha =>
      hhT a ⟨hAT ha, hAM ha⟩⟩, m, hm, rfl⟩
  have hC1 : M ⊔ (X ⊓ Subgroup.normalizer (A : Set G)) = X := by
    refine le_antisymm (sup_le hMX inf_le_left) fun x hx => ?_
    obtain ⟨h, hh, m, hm, rfl⟩ := hdec x hx
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_right hh) (Subgroup.mem_sup_left hm)
  have htopM : Subgroup.normalClosure ((A.subgroupOf M : Subgroup M) : Set M) = ⊤ := by
    set Q := Subgroup.normalClosure ((A.subgroupOf M : Subgroup M) : Set M) with hQ
    have hconj : ∀ x ∈ X, ∀ a ∈ A, ∃ q : M, q ∈ Q ∧ (q : G) = x * a * x⁻¹ := by
      intro x hx a ha
      obtain ⟨h, ⟨hhX, hhN⟩, m, hm, rfl⟩ := hdec x hx
      have ha' : h * a * h⁻¹ ∈ A := (Subgroup.mem_normalizer_iff.1 hhN a).1 ha
      have hm' : h * m * h⁻¹ ∈ M := hMnX h hhX m hm
      refine ⟨⟨h * m * h⁻¹, hm'⟩ * ⟨h * a * h⁻¹, hAM ha'⟩ * ⟨h * m * h⁻¹, hm'⟩⁻¹, ?_, ?_⟩
      · exact Subgroup.normalClosure_normal.conj_mem _
          (Subgroup.subset_normalClosure (Subgroup.mem_subgroupOf.2 ha')) _
      · simp only [Subgroup.coe_mul, Subgroup.coe_inv]
        group
    have hle : Subgroup.normalClosure ((A.subgroupOf X : Subgroup X) : Set X) ≤
        (Q.map M.subtype).subgroupOf X := by
      change Subgroup.closure (Group.conjugatesOfSet ((A.subgroupOf X : Subgroup X) : Set X)) ≤ _
      rw [Subgroup.closure_le]
      intro y hy
      obtain ⟨a, ha, hay⟩ := Set.mem_iUnion₂.1 hy
      obtain ⟨c, rfl⟩ := isConj_iff.1 hay
      obtain ⟨q, hq, hqeq⟩ := hconj c c.2 a ha
      exact ⟨q, hq, by rw [Subgroup.coe_subtype, hqeq]; simp⟩
    rw [eq_top_iff]
    intro m _
    obtain ⟨y, hy, hym⟩ := m.2
    obtain ⟨q, hq, hqm⟩ := hle hy
    rw [show m = q from Subtype.ext (hym.symm.trans hqm.symm)]
    exact hq
  have hMcard : Nat.card M < n := (Subgroup.card_le_of_le hMX).trans_lt hXn
  have hAPM : A.subgroupOf M ≤ (PM : Subgroup M) := by
    rw [hPM]
    exact fun x hx => Subgroup.mem_subgroupOf.2 (hAT (Subgroup.mem_subgroupOf.1 hx))
  have hclM := stronglyClosed_subgroupOf S hcl hAM PM hAPM
  have hC : Conclusion M (T.subgroupOf M) (A.subgroupOf M) := by
    have := (h1 n hIH M hMcard).1 PM (A.subgroupOf M) hAPM (isMulCommutative_subgroupOf hAab M)
      hclM htopM
    rwa [hPM] at this
  obtain ⟨Sbar, hSbar, hclbar⟩ := CFSG.ShultStronglyClosedTI.quotient_stronglyClosed PM
    (A.subgroupOf M) (goldschmidtOddCore M) hAPM hclM
  obtain ⟨ha, hb, hc⟩ := id hC
  have hBab : IsMulCommutative (barOf M A) :=
    isMulCommutative_map (isMulCommutative_subgroupOf hAab M) _
  have hO2B : CFSG.Open.pCore 2 (M ⧸ goldschmidtOddCore M) ≤ barOf M A := by
    show _ ≤ (A.subgroupOf M).map (QuotientGroup.mk' (goldschmidtOddCore M))
    rw [hb]
    exact le_sup_left
  have hC2 := pCore_le_center_of_le hBab hO2B ha
  refine ⟨hC, hC1, hC2, fun L hL => ?_, fun hE => ?_⟩
  ·
    have hZn : Nat.card (M ⧸ goldschmidtOddCore M) < n := by
      have h1 : Nat.card (M ⧸ goldschmidtOddCore M) ≤ Nat.card M := by
        rw [← Subgroup.index_eq_card]
        exact Nat.le_of_dvd Nat.card_pos (Subgroup.index_dvd_card _)
      exact h1.trans_lt hMcard
    have hBP : barOf M A ≤ (Sbar : Subgroup _) := by
      rw [hSbar]
      exact Subgroup.map_mono hAPM
    have := inducesOmega1_of_core hIH hZn Sbar hBP hBab hclbar
      (normalClosure_map_eq_top htopM _ (QuotientGroup.mk'_surjective _))
      (goldschmidtOddCore_quotient_eq_bot M) hC2 ha hL
    rw [hSbar, hPM] at this
    exact this
  ·
    rw [hE, sup_bot_eq] at ha
    have hBtop : (A.subgroupOf M).map (QuotientGroup.mk' (goldschmidtOddCore M)) = ⊤ := by
      rw [eq_top_iff, ← ha, hb]
      exact le_sup_left
    have hsup : A.subgroupOf M ⊔ goldschmidtOddCore M = ⊤ := by
      have h2 := congrArg (Subgroup.comap (QuotientGroup.mk' (goldschmidtOddCore M))) hBtop
      rwa [Subgroup.comap_map_eq, QuotientGroup.ker_mk', Subgroup.comap_top] at h2
    exact c4_of_sup_eq_top hAM hMnX (S.isPGroup'.to_le hAS) hsup

end CFSG.Goldschmidt
