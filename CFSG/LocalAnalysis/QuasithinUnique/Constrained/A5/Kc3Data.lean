module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.Kc3J
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.Kc3Can
public import CFSG.GroupTheory.ABGLocalTools.Basic
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.Kc3NSC

public section

namespace CFSG.QuasithinUnique.A5

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank
  CFSG.QuasithinUnique.A5.Kc3J

section Stab

variable {K : Type} [Group K] (E : Subgroup K) (β : ↥E ≃* Multiplicative ↥(evenWeight 5))

@[expose] def S5Stab : Subgroup K where
  carrier := {n | n ∈ Subgroup.normalizer (E : Set K) ∧ ∃ σ : Equiv.Perm (Fin 5),
    ∀ v w : ↥E, (w : K) = n * v * n⁻¹ →
      Multiplicative.toAdd (β w) = Delta5.vact σ (Multiplicative.toAdd (β v))}
  one_mem' := ⟨one_mem _, 1, fun v w hw => by
    have : w = v := Subtype.ext (by simpa using hw)
    rw [this, Delta5.vact_one]⟩
  mul_mem' := by
    rintro n m ⟨hn, σ, hσ⟩ ⟨hm, τ, hτ⟩
    refine ⟨mul_mem hn hm, σ * τ, fun v w hw => ?_⟩
    have hu : m * (v : K) * m⁻¹ ∈ E := (Subgroup.mem_normalizer_iff.1 hm (v : K)).1 v.2
    let u : ↥E := ⟨m * (v : K) * m⁻¹, hu⟩
    have h1 : Multiplicative.toAdd (β u) = Delta5.vact τ (Multiplicative.toAdd (β v)) :=
      hτ v u rfl
    have hwu : (w : K) = n * (u : K) * n⁻¹ := by
      rw [hw]
      simp [u, mul_assoc]
    rw [hσ u w hwu, h1, Delta5.vact_mul]
  inv_mem' := by
    rintro n ⟨hn, σ, hσ⟩
    refine ⟨inv_mem hn, σ⁻¹, fun v w hw => ?_⟩
    have hvw : (v : K) = n * (w : K) * n⁻¹ := by
      rw [hw]
      simp [mul_assoc]
    have h1 := hσ w v hvw
    rw [h1, ← Delta5.vact_mul, inv_mul_cancel, Delta5.vact_one]

theorem S5Stab_le_normalizer : S5Stab E β ≤ Subgroup.normalizer (E : Set K) := fun _ h => h.1

end Stab

@[expose] def Kc3LocalData (K : Type) [Group K] : Prop :=
  ∀ (E : Subgroup K) (β : ↥E ≃* Multiplicative ↥(evenWeight 5)), Delta5Norm E β →
    Subgroup.centralizer (E : Set K) ≤ E ∧
      2 ∣ (S5Stab E β).relIndex (Subgroup.normalizer (E : Set K))

@[expose] def Kc3LocalFor (P : ∀ (X : Type) [Group X], Prop) : Prop :=
  ∀ (X : Type) [Group X] [Finite X], P X → Kc3LocalData X

theorem normalizer_subgroupOf_eq {G : Type} [Group G] {K V : Subgroup G} (hVK : V ≤ K) :
    Subgroup.normalizer ((V.subgroupOf K : Subgroup ↥K) : Set ↥K) =
      (K ⊓ Subgroup.normalizer (V : Set G)).subgroupOf K := by
  ext n
  rw [Subgroup.mem_subgroupOf, Subgroup.mem_inf, Subgroup.mem_normalizer_iff,
    Subgroup.mem_normalizer_iff]
  constructor
  · intro h
    refine ⟨n.2, fun x => ?_⟩
    constructor
    · intro hx
      have := (h ⟨x, hVK hx⟩).1 (Subgroup.mem_subgroupOf.2 hx)
      exact Subgroup.mem_subgroupOf.1 (by simpa using this)
    · intro hx
      have hxK : x ∈ K := by
        have h1 : (n : G)⁻¹ * ((n : G) * x * (n : G)⁻¹) * (n : G) ∈ K :=
          K.mul_mem (K.mul_mem (K.inv_mem n.2) (hVK hx)) n.2
        have e : (n : G)⁻¹ * ((n : G) * x * (n : G)⁻¹) * (n : G) = x := by group
        rwa [e] at h1
      have := (h ⟨x, hxK⟩).2 (Subgroup.mem_subgroupOf.2 (by simpa using hx))
      exact Subgroup.mem_subgroupOf.1 this
  · rintro ⟨-, h⟩ x
    have hxK : (x : G) ∈ K := x.2
    constructor
    · intro hx
      exact Subgroup.mem_subgroupOf.2 (by simpa using (h x).1 (Subgroup.mem_subgroupOf.1 hx))
    · intro hx
      exact Subgroup.mem_subgroupOf.2 ((h x).2 (by simpa using Subgroup.mem_subgroupOf.1 hx))

theorem kc3ForS_of_localFor {P : ∀ (X : Type) [Group X], Prop} (h : Kc3LocalFor P) :
    Kc3ForS P := by
  classical
  intro G _ _ K L S₀ T₀ hq hKP hZ hLK hD hperf hSL hS hT hST hTK hTS
  have hloc := h ↥K hKP
  obtain ⟨V, Q, hVQ, hQL, hQ2, hLQ, hLV, α, hα, hαQ, β, hβ⟩ := hD
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hVK : V ≤ K := hVQ.trans (hQL.trans hLK)
  have hV2 : IsPGroup 2 ↥V := hQ2.to_le hVQ
  have hact := delta5Norm_of_d5 hLK hVQ hQL hLV α hα β hβ
  obtain ⟨hC, hidx⟩ := hloc (V.subgroupOf K)
    ((Subgroup.subgroupOfEquivOfLe hVK).trans β) hact
  have hC' : K ⊓ Subgroup.centralizer (V : Set G) ≤ V := by
    intro g hg
    obtain ⟨hgK, hgC⟩ := hg
    have : (⟨g, hgK⟩ : ↥K) ∈ Subgroup.centralizer ((V.subgroupOf K : Subgroup ↥K) : Set ↥K) := by
      rw [Subgroup.mem_centralizer_iff]
      intro x hx
      have hx' : ((x : ↥K) : G) ∈ V := Subgroup.mem_subgroupOf.1 hx
      exact Subtype.ext (Subgroup.mem_centralizer_iff.1 hgC _ hx')
    exact Subgroup.mem_subgroupOf.1 (hC this)
  have hQV : Q ≤ V := by
    intro q hq
    have hqL : q ∈ L := hQL hq
    have hqK : q ∈ K := hLK hqL
    have hqC : q ∈ Subgroup.centralizer (V : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro v hv
      let l : ↥L := ⟨q, hqL⟩
      have hα1 : α l = 1 := (hαQ l).2 hq
      have hvq : q * v * q⁻¹ ∈ V := (Subgroup.mem_normalizer_iff.1 (hLV hqL) v).1 hv
      have h' := hβ l ⟨v, hv⟩ ⟨q * v * q⁻¹, hvq⟩ rfl
      have e1 : ((α l : ↥(alternatingGroup (Fin 5))) : Equiv.Perm (Fin 5)) = 1 := by
        rw [hα1]; rfl
      rw [e1, Delta5.vact_one] at h'
      have h7 : (⟨q * v * q⁻¹, hvq⟩ : ↥V) = ⟨v, hv⟩ :=
        β.injective (Multiplicative.toAdd.injective h')
      have h2 : q * v * q⁻¹ = v := congrArg Subtype.val h7
      calc v * q = (q * v * q⁻¹) * q := by rw [h2]
        _ = q * v := by group
    exact hC' ⟨hqK, hqC⟩
  have hQeq : Q = V := le_antisymm hQV hVQ
  have hSV : S₀ ≤ Subgroup.normalizer (V : Set G) := by
    intro s hs
    have := normalizer_le_normalizer_Q hQL hQ2 α hα hαQ (hSL hs)
    rwa [hQeq] at this
  set X : Subgroup G := (K ⊔ T₀) ⊓ Subgroup.normalizer (V : Set G) with hX
  have hXchar : CharTwo X := Kc3Gen.charTwo_normalizer hT hTK hV2 hVK hC'
  have hXV : X ≤ Subgroup.normalizer (V : Set G) := inf_le_right
  have hLX : L ⊔ S₀ ≤ X :=
    sup_le (le_inf (hLK.trans le_sup_left) hLV) (le_inf (hST.trans le_sup_right) hSV)
  obtain ⟨S₁, hS₀S₁, hS₁⟩ := Kc3Gen.exists_sylowTwoOf_le (X := X) (le_sup_right.trans hLX) hS
  refine ⟨X, S₁, hXchar, hLX, inf_le_left, hS₁, hS₀S₁, ?_⟩
  intro hsub
  have hYX : L ⊔ S₁ ≤ X := sup_le (le_sup_left.trans hLX) hS₁.1
  have hnsc := Kc3NSC.nsc_perm (le_sup_left : L ≤ L ⊔ S₁) (hYX.trans hXV) α hα β hβ hsub
  set N₁ : Subgroup G := K ⊓ Subgroup.normalizer (V : Set G) with hN₁
  have hN₁X : N₁ ≤ X := le_inf (inf_le_left.trans le_sup_left) inf_le_right
  have hXN₁ : X ≤ Subgroup.normalizer (N₁ : Set G) := by
    intro x hx
    rw [Subgroup.mem_normalizer_iff]
    have hxK : x ∈ Subgroup.normalizer (K : Set G) := by
      have : K ⊔ T₀ ≤ Subgroup.normalizer (K : Set G) := sup_le Subgroup.le_normalizer hTK
      exact this hx.1
    have hxV : x ∈ Subgroup.normalizer (V : Set G) := hx.2
    intro n
    have h1 := Subgroup.mem_normalizer_iff.1 hxK n
    have h2 : n ∈ Subgroup.normalizer (V : Set G) ↔
        x * n * x⁻¹ ∈ Subgroup.normalizer (V : Set G) := by
      constructor
      · intro h
        exact mul_mem (mul_mem hxV h) (inv_mem hxV)
      · intro h
        have := mul_mem (mul_mem (inv_mem hxV) h) hxV
        simpa [mul_assoc] using this
    simp only [hN₁, Subgroup.mem_inf]
    rw [h1, h2]
  have hSyl : CFSG.ABGLocalTools.IsSylowOf 2 S₁ X :=
    (CFSG.ABGLocalTools.isSylowOf_iff).2 ⟨hS₁.1, hS₁.2.1, hS₁.2.2⟩
  have hSyl' := hSyl.inf_of_le_normalizer hN₁X hXN₁
  have hodd : ¬ 2 ∣ (S₁ ⊓ N₁).relIndex N₁ :=
    ((CFSG.ABGLocalTools.isSylowOf_iff).1 hSyl').2.2
  set E : Subgroup ↥K := V.subgroupOf K with hE
  set β' : ↥E ≃* Multiplicative ↥(evenWeight 5) := (Subgroup.subgroupOfEquivOfLe hVK).trans β
    with hβ'
  have hN' : Subgroup.normalizer (E : Set ↥K) = N₁.subgroupOf K := by
    rw [hE]
    exact normalizer_subgroupOf_eq hVK
  have hSle : S₁.subgroupOf K ≤ S5Stab E β' := by
    intro n hn
    have hnS : (n : G) ∈ S₁ := Subgroup.mem_subgroupOf.1 hn
    have hnN : n ∈ Subgroup.normalizer (E : Set ↥K) := by
      rw [hN']
      exact Subgroup.mem_subgroupOf.2 ⟨n.2, hXV (hS₁.1 hnS)⟩
    refine ⟨hnN, ?_⟩
    obtain ⟨σ, hσ⟩ := hnsc (n : G) (Subgroup.mem_sup_right hnS)
    refine ⟨σ, fun v w hw => ?_⟩
    have hvG : ((v : ↥K) : G) ∈ V := Subgroup.mem_subgroupOf.1 v.2
    have hwG : ((w : ↥K) : G) ∈ V := Subgroup.mem_subgroupOf.1 w.2
    have hw' : ((w : ↥K) : G) = (n : G) * ((v : ↥K) : G) * (n : G)⁻¹ := by
      have := congrArg Subtype.val hw
      simpa using this
    exact hσ ⟨_, hvG⟩ ⟨_, hwG⟩ hw'
  have hodd' : ¬ 2 ∣ (S₁.subgroupOf K).relIndex (Subgroup.normalizer (E : Set ↥K)) := by
    rw [hN', Subgroup.relIndex_subgroupOf inf_le_left]
    intro hdvd
    apply hodd
    rw [Subgroup.inf_relIndex_right]
    exact hdvd
  exact hodd' (hidx.trans (Subgroup.relIndex_dvd_of_le_left _ hSle))

theorem kc3For_of_localFor {P : ∀ (X : Type) [Group X], Prop}
    (hP : ∀ (X Y : Type) [Group X] [Group Y], X ≃* Y → P X → P Y) (h : Kc3LocalFor P) :
    Kc3For P :=
  kc3For_of_simple hP (kc3ForS_of_localFor h)

end CFSG.QuasithinUnique.A5
