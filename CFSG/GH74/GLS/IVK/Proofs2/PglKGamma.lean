module

public import CFSG.GH74.GLS.IVK.Proofs2.PglKDihedral
public import CFSG.GH74.GLS.IVK.Proofs2.PglKPCore
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_8Four
public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.GroupTheory.DihedralTwoClassFusionSupport
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

namespace CFSG.GH74.GLS.IVK.Proofs2

open Subgroup CFSG CFSG.GH74.GLS CFSG.GH74.GLS.IVK CFSG.GorensteinWalter

section Gamma

variable {K : Type} [Group K]

@[expose] def HasD4Centralizers (K : Type) [Group K] : Prop :=
  ∀ u : K, orderOf u = 2 → Nonempty (↥(centralizer ({u} : Set K)) ≃* DihedralGroup 4)

theorem card_centralizer_of_d4 (hD4 : HasD4Centralizers K) {u : K} (hu : orderOf u = 2) :
    Nat.card ↥(centralizer ({u} : Set K)) = 8 := by
  obtain ⟨θ⟩ := hD4 u hu
  rw [Nat.card_congr θ.toEquiv, DihedralGroup.nat_card]

theorem centralizer_ne_of_d4 (hD4 : HasD4Centralizers K) {u₁ u₂ : K} (h₁ : orderOf u₁ = 2)
    (h₂ : orderOf u₂ = 2) (hne : u₁ ≠ u₂) :
    centralizer ({u₁} : Set K) ≠ centralizer ({u₂} : Set K) := by
  intro h
  obtain ⟨θ⟩ := hD4 u₁ h₁
  have hu1 : u₁ ≠ 1 := fun h' => by rw [h', orderOf_one] at h₁; omega
  have hu2 : u₂ ≠ 1 := fun h' => by rw [h', orderOf_one] at h₂; omega
  have hm1 : u₁ ∈ centralizer ({u₁} : Set K) := mem_centralizer_singleton_iff.2 rfl
  have hm2 : u₂ ∈ centralizer ({u₁} : Set K) := by
    rw [h]
    exact mem_centralizer_singleton_iff.2 rfl
  refine hne (congrArg Subtype.val (dih4_center_unique θ (z := ⟨u₁, hm1⟩) (z' := ⟨u₂, hm2⟩) ?_ ?_ ?_ ?_))
  · intro h'
    exact hu1 (congrArg Subtype.val h')
  · intro c
    exact Subtype.ext (mem_centralizer_singleton_iff.1 c.2)
  · intro h'
    exact hu2 (congrArg Subtype.val h')
  · intro c
    have hc : (c : K) ∈ centralizer ({u₂} : Set K) := by rw [← h]; exact c.2
    exact Subtype.ext (mem_centralizer_singleton_iff.1 hc)

theorem eq_of_commute_of_d4 (hD4 : HasD4Centralizers K) {u₁ u₂ : K} (h₁ : orderOf u₁ = 2)
    (h₂ : orderOf u₂ = 2) (hne : u₁ ≠ u₂) (hcomm : u₁ * u₂ = u₂ * u₁) {g : K}
    (hg1 : g * u₁ = u₁ * g) (hg2 : g * u₂ = u₂ * g) :
    g = 1 ∨ g = u₁ ∨ g = u₂ ∨ g = u₂ * u₁ := by
  obtain ⟨θ⟩ := hD4 u₁ h₁
  have hu1 : u₁ ≠ 1 := fun h' => by rw [h', orderOf_one] at h₁; omega
  have hu2 : u₂ ≠ 1 := fun h' => by rw [h', orderOf_one] at h₂; omega
  have hm1 : u₁ ∈ centralizer ({u₁} : Set K) := mem_centralizer_singleton_iff.2 rfl
  have hm2 : u₂ ∈ centralizer ({u₁} : Set K) := mem_centralizer_singleton_iff.2 hcomm.symm
  have hmg : g ∈ centralizer ({u₁} : Set K) := mem_centralizer_singleton_iff.2 hg1
  have hsq : u₂ * u₂ = 1 := by rw [← pow_two, ← h₂]; exact pow_orderOf_eq_one u₂
  have key := dih4_centralizer θ (z := ⟨u₁, hm1⟩) (a := ⟨u₂, hm2⟩) (g := ⟨g, hmg⟩)
    (fun h' => hu1 (congrArg Subtype.val h'))
    (fun c => Subtype.ext (mem_centralizer_singleton_iff.1 c.2))
    (Subtype.ext hsq) (fun h' => hu2 (congrArg Subtype.val h'))
    (fun h' => hne.symm (congrArg Subtype.val h'))
    (Subtype.ext hg2)
  rcases key with h | h | h | h
  · exact Or.inl (congrArg Subtype.val h)
  · exact Or.inr (Or.inl (congrArg Subtype.val h))
  · exact Or.inr (Or.inr (Or.inl (congrArg Subtype.val h)))
  · exact Or.inr (Or.inr (Or.inr (congrArg Subtype.val h)))

end Gamma

section Klein

variable {K : Type} [Group K] [Finite K]

omit [Finite K] in
theorem le_centralizer_normalizer_of_d4 (hD4 : HasD4Centralizers K) {V₀ : Subgroup K}
    (hV4 : Nat.card ↥V₀ = 4) (hcomm : ∀ a ∈ V₀, ∀ b ∈ V₀, a * b = b * a) {u : K} (hu : u ∈ V₀)
    (hu2 : orderOf u = 2) :
    V₀ ≤ centralizer ({u} : Set K) ∧ centralizer ({u} : Set K) ≤ normalizer (V₀ : Set K) := by
  have hVC : V₀ ≤ centralizer ({u} : Set K) := fun v hv =>
    mem_centralizer_singleton_iff.2 (hcomm v hv u hu)
  refine ⟨hVC, ?_⟩
  have hC8 := card_centralizer_of_d4 hD4 hu2
  have hidx : (V₀.subgroupOf (centralizer ({u} : Set K))).index = 2 := by
    have h1 := Subgroup.card_mul_index (V₀.subgroupOf (centralizer ({u} : Set K)))
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hVC).toEquiv, hV4, hC8] at h1
    omega
  have hN := Subgroup.normal_of_index_eq_two hidx
  have hnorm : ∀ g ∈ centralizer ({u} : Set K), ∀ v ∈ V₀, g * v * g⁻¹ ∈ V₀ := by
    intro g hg v hv
    have h1 : (⟨v, hVC hv⟩ : ↥(centralizer ({u} : Set K))) ∈
        V₀.subgroupOf (centralizer ({u} : Set K)) := hv
    exact hN.conj_mem _ h1 ⟨g, hg⟩
  intro g hg
  rw [Subgroup.mem_normalizer_iff]
  intro h
  refine ⟨fun hh => hnorm g hg h hh, fun hh => ?_⟩
  have := hnorm g⁻¹ (inv_mem hg) _ hh
  simpa [mul_assoc] using this

theorem card_normalizer_le_of_d4 (hD4 : HasD4Centralizers K) {V₀ : Subgroup K} {u₁ u₂ : K}
    (hV4 : Nat.card ↥V₀ = 4) (hu₁ : u₁ ∈ V₀) (hu₂ : u₂ ∈ V₀) (h₁ : orderOf u₁ = 2)
    (h₂ : orderOf u₂ = 2) (hne : u₁ ≠ u₂) (hcomm : u₁ * u₂ = u₂ * u₁) :
    Nat.card ↥(normalizer (V₀ : Set K)) ≤ 24 := by
  have hVN : V₀ ≤ normalizer (V₀ : Set K) := le_normalizer
  have hF4 : Nat.card ↥(V₀.subgroupOf (normalizer (V₀ : Set K))) = 4 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hVN).toEquiv]
    exact hV4
  have : (V₀.subgroupOf (normalizer (V₀ : Set K))).Normal := Subgroup.normal_in_normalizer
  refine CFSG.QuasithinUnique.Unc25Small.card_le_24_of_klein
    (V₀.subgroupOf (normalizer (V₀ : Set K))) hF4 ?_
  intro g hg
  have hf1 : (⟨u₁, hVN hu₁⟩ : ↥(normalizer (V₀ : Set K))) ∈ V₀.subgroupOf (normalizer (V₀ : Set K)) :=
    hu₁
  have hf2 : (⟨u₂, hVN hu₂⟩ : ↥(normalizer (V₀ : Set K))) ∈ V₀.subgroupOf (normalizer (V₀ : Set K)) :=
    hu₂
  have hg1 : (g : K) * u₁ = u₁ * g := congrArg Subtype.val (hg _ hf1)
  have hg2 : (g : K) * u₂ = u₂ * g := congrArg Subtype.val (hg _ hf2)
  show (g : K) ∈ V₀
  rcases eq_of_commute_of_d4 hD4 h₁ h₂ hne hcomm hg1 hg2 with h | h | h | h
  · rw [h]; exact one_mem _
  · rw [h]; exact hu₁
  · rw [h]; exact hu₂
  · rw [h]; exact V₀.mul_mem hu₂ hu₁

theorem card_gamma_eq_of_d4 (hD4 : HasD4Centralizers K) {V₀ : Subgroup K} {u₁ u₂ : K}
    (hV4 : Nat.card ↥V₀ = 4) (hu₁ : u₁ ∈ V₀) (hu₂ : u₂ ∈ V₀) (h₁ : orderOf u₁ = 2)
    (h₂ : orderOf u₂ = 2) (hne : u₁ ≠ u₂) (hcomm : u₁ * u₂ = u₂ * u₁)
    (h16 : ¬ 16 ∣ Nat.card K) {Γ : Subgroup K} (hΓ1 : centralizer ({u₁} : Set K) ≤ Γ)
    (hΓ2 : centralizer ({u₂} : Set K) ≤ Γ) (hΓN : Γ ≤ normalizer (V₀ : Set K)) :
    Nat.card ↥Γ = 24 := by
  have hN24 := card_normalizer_le_of_d4 hD4 hV4 hu₁ hu₂ h₁ h₂ hne hcomm
  have hle : Nat.card ↥Γ ≤ 24 := (Subgroup.card_le_of_le hΓN).trans hN24
  have hC1 := card_centralizer_of_d4 hD4 h₁
  have hC2 := card_centralizer_of_d4 hD4 h₂
  have h8 : 8 ∣ Nat.card ↥Γ := hC1 ▸ Subgroup.card_dvd_of_le hΓ1
  have hdvd : Nat.card ↥Γ ∣ Nat.card K := Subgroup.card_subgroup_dvd_card Γ
  have hpos : 0 < Nat.card ↥Γ := Nat.card_pos
  have h16' : Nat.card ↥Γ ≠ 16 := fun h => h16 (h ▸ hdvd)
  have h8' : Nat.card ↥Γ ≠ 8 := by
    intro h
    have e1 : centralizer ({u₁} : Set K) = Γ :=
      Subgroup.eq_of_le_of_card_ge hΓ1 (by rw [h, hC1])
    have e2 : centralizer ({u₂} : Set K) = Γ :=
      Subgroup.eq_of_le_of_card_ge hΓ2 (by rw [h, hC2])
    exact centralizer_ne_of_d4 hD4 h₁ h₂ hne (e1.trans e2.symm)
  omega

theorem map_mem_of_d4 (hD4 : HasD4Centralizers K) {V₀ : Subgroup K} {u₁ u₂ : K}
    (hV4 : Nat.card ↥V₀ = 4) (hcomm : ∀ a ∈ V₀, ∀ b ∈ V₀, a * b = b * a) (hu₁ : u₁ ∈ V₀)
    (hu₂ : u₂ ∈ V₀) (h₁ : orderOf u₁ = 2) (h₂ : orderOf u₂ = 2) (hne : u₁ ≠ u₂)
    {Γ : Subgroup K} (hΓ1 : centralizer ({u₁} : Set K) ≤ Γ) (hΓ2 : centralizer ({u₂} : Set K) ≤ Γ)
    (hΓN : Γ ≤ normalizer (V₀ : Set K)) (hΓ24 : Nat.card ↥Γ = 24) {ψ : MulAut K}
    (hψ : ∀ k ∈ Γ, ψ k ∈ Γ) : ∀ v ∈ V₀, ψ v ∈ V₀ := by
  obtain ⟨hV1, -⟩ := le_centralizer_normalizer_of_d4 hD4 hV4 hcomm hu₁ h₁
  obtain ⟨hV2, -⟩ := le_centralizer_normalizer_of_d4 hD4 hV4 hcomm hu₂ h₂
  have hVΓ : V₀ ≤ Γ := hV1.trans hΓ1
  have hVn : (V₀.subgroupOf Γ).Normal := ⟨fun n hn g => by
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    exact ((Subgroup.mem_normalizer_iff.1 (hΓN g.2) _).1 hn)⟩
  have hVcard : Nat.card ↥(V₀.subgroupOf Γ) = 4 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hVΓ).toEquiv]
    exact hV4
  have hP1 : Nat.card ↥((centralizer ({u₁} : Set K)).subgroupOf Γ) = 8 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hΓ1).toEquiv]
    exact card_centralizer_of_d4 hD4 h₁
  have hP2 : Nat.card ↥((centralizer ({u₂} : Set K)).subgroupOf Γ) = 8 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hΓ2).toEquiv]
    exact card_centralizer_of_d4 hD4 h₂
  have hPne : (centralizer ({u₁} : Set K)).subgroupOf Γ ≠
      (centralizer ({u₂} : Set K)).subgroupOf Γ := by
    intro h
    apply centralizer_ne_of_d4 hD4 h₁ h₂ hne
    have := Subgroup.subgroupOf_inj.1 h
    rwa [inf_eq_left.2 hΓ1, inf_eq_left.2 hΓ2] at this
  have hpc : pCore 2 ↥Γ = V₀.subgroupOf Γ :=
    pCore_eq_of_two_sylow hΓ24 _ hVcard _ _ hP1 hP2 hPne
      (fun x hx => hV1 hx) (fun x hx => hV2 hx)
  let α₀ : ↥Γ →* ↥Γ :=
    { toFun := fun k => ⟨ψ (k : K), hψ k k.2⟩
      map_one' := Subtype.ext (map_one ψ)
      map_mul' := fun a b => Subtype.ext (map_mul ψ (a : K) (b : K)) }
  have hα : Function.Injective α₀ := fun a b h => by
    apply Subtype.ext
    exact ψ.injective (congrArg Subtype.val h)
  let α : ↥Γ ≃* ↥Γ := MulEquiv.ofBijective α₀ (Finite.injective_iff_bijective.1 hα)
  have hmap := pCore_map_iso 2 α
  intro v hv
  have hv' : (⟨v, hVΓ hv⟩ : ↥Γ) ∈ pCore 2 ↥Γ := by rw [hpc]; exact hv
  have h2 : α ⟨v, hVΓ hv⟩ ∈ pCore 2 ↥Γ := by
    rw [← hmap]
    exact Subgroup.mem_map_of_mem _ hv'
  rw [hpc] at h2
  exact h2

end Klein

end CFSG.GH74.GLS.IVK.Proofs2
