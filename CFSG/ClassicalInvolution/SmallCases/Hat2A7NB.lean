module

public import CFSG.ClassicalInvolution.SmallCases.Hat2A7NDefs
public import CFSG.ClassicalInvolution.SmallCases.Hat2A7LocalB

public section

namespace CFSG.ClassicalInvolution.Hat2A7N

open CFSG.Open CFSG.ComponentClassification CFSG.ClassicalInvolution.Hat2A7

section Stable

variable {F : Type} [Group F]

theorem conj_conj_comm {x c : F} (hxc : x * c = c * x) (y : F) :
    x * (c * y * c⁻¹) * x⁻¹ = c * (x * y * x⁻¹) * c⁻¹ := by
  have h2 : x⁻¹ * c⁻¹ = c⁻¹ * x⁻¹ := (Commute.inv_inv (show Commute x c from hxc)).eq
  calc x * (c * y * c⁻¹) * x⁻¹ = (x * c) * y * (c⁻¹ * x⁻¹) := by group
    _ = (c * x) * y * (x⁻¹ * c⁻¹) := by rw [hxc, ← h2]
    _ = c * (x * y * x⁻¹) * c⁻¹ := by group

theorem IsTwinDiag.map_conj {K : Subgroup F} {x : F} {L : Subgroup F} (hL : IsTwinDiag K x L)
    {c : F} (hc : c ∈ Subgroup.centralizer ({x} : Set F)) :
    IsTwinDiag K x (L.map (MulAut.conj c).toMonoidHom) := by
  obtain ⟨K', hK', h, rfl⟩ := hL
  have hxc : x * c = c * x := Subgroup.mem_centralizer_iff.mp hc x rfl
  have h' : ∀ k ∈ K'.map (MulAut.conj c).toMonoidHom, ∀ k' ∈ K'.map (MulAut.conj c).toMonoidHom,
      k * (x * k' * x⁻¹) = (x * k' * x⁻¹) * k := by
    rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    have h1 := h a ha b hb
    show c * a * c⁻¹ * (x * (c * b * c⁻¹) * x⁻¹) = x * (c * b * c⁻¹) * x⁻¹ * (c * a * c⁻¹)
    rw [conj_conj_comm hxc b]
    calc c * a * c⁻¹ * (c * (x * b * x⁻¹) * c⁻¹) = c * (a * (x * b * x⁻¹)) * c⁻¹ := by group
      _ = c * ((x * b * x⁻¹) * a) * c⁻¹ := by rw [h1]
      _ = c * (x * b * x⁻¹) * c⁻¹ * (c * a * c⁻¹) := by group
  refine ⟨K'.map (MulAut.conj c).toMonoidHom, hK'.trans (isConjSubgroup_map_conj K' c), h', ?_⟩
  ext y
  constructor
  · rintro ⟨_, ⟨k, rfl⟩, rfl⟩
    refine ⟨⟨c * (k : F) * c⁻¹, (k : F), k.2, rfl⟩, ?_⟩
    show c * (k : F) * c⁻¹ * (x * (c * (k : F) * c⁻¹) * x⁻¹) =
      c * ((k : F) * (x * (k : F) * x⁻¹)) * c⁻¹
    rw [conj_conj_comm hxc (k : F)]
    group
  · rintro ⟨⟨_, k, hk, rfl⟩, rfl⟩
    refine ⟨k * (x * k * x⁻¹), ⟨⟨k, hk⟩, rfl⟩, ?_⟩
    show c * (k * (x * k * x⁻¹)) * c⁻¹ = c * k * c⁻¹ * (x * (c * k * c⁻¹) * x⁻¹)
    rw [conj_conj_comm hxc k]
    group

end Stable

section Closure

variable {F : Type} [Group F] [Finite F]

theorem oddCore_normalClosure_le_center_of_family {C L M : Subgroup F} {u v : F}
    {P : Subgroup F → Prop} (hP : ∀ N, P N → ∀ c ∈ C, P (N.map (MulAut.conj c).toMonoidHom))
    (hL : IsClassical2A7 C L u) (hM : IsClassical2A7 C M v) (hPL : P L) (hPM : P M)
    (h : ∀ (N : Subgroup F) (w : F), P N → IsClassical2A7 C N w →
      ∀ (d n : ↥C), d ∈ componentClassificationOddCore ↥C → (n : F) ∈ N → n * d = d * n) :
    classicalInvolutionOddCore ↥(normalClosureIn2A7 C (L ⊔ M)) ≤
      Subgroup.center ↥(normalClosureIn2A7 C (L ⊔ M)) := by
  have hLM : L ⊔ M ≤ C := sup_le hL.le hM.le
  intro e he
  obtain ⟨heC, heO⟩ := oddCore_normalClosure_le hLM e he
  have hgen : normalClosureIn2A7 C (L ⊔ M) ≤ Subgroup.centralizer ({(e : F)} : Set F) := by
    refine normalClosureIn2A7_le_of fun c hc => ?_
    rw [Subgroup.map_sup]
    have key : ∀ {N : Subgroup F} {w : F}, P N → IsClassical2A7 C N w →
        N.map (MulAut.conj c).toMonoidHom ≤ Subgroup.centralizer ({(e : F)} : Set F) := by
      intro N w hPN hN n hn
      have h1 := hN.conj c
      rw [map_conj_eq_of_mem hc] at h1
      rw [Subgroup.mem_centralizer_singleton_iff]
      have := h _ _ (hP N hPN c hc) h1 ⟨(e : F), heC⟩ ⟨n, h1.le hn⟩ heO hn
      exact congrArg Subtype.val this
    exact sup_le (key hPL hL) (key hPM hM)
  rw [Subgroup.mem_center_iff]
  intro y
  exact Subtype.ext (Subgroup.mem_centralizer_singleton_iff.mp (hgen y.2))

end Closure

section NarrowedB

@[expose] def A7TwoComponentOrdinaryN (F : Type) [Group F] (K : Subgroup F) (z : F) : Prop :=
  ∀ x : F, orderOf x = 2 → IsCommProd z x → ∀ (N : Subgroup F) (w : F),
    (IsConjSubgroup K N ∨ IsTwinDiag K x N) →
    IsClassical2A7 (Subgroup.centralizer ({x} : Set F)) N w →
    ∀ M : Subgroup ↥(Subgroup.centralizer ({x} : Set F)), TwoComponents.IsTwoComponent M →
      N.subgroupOf (Subgroup.centralizer ({x} : Set F)) ≤ M → IsComponentOf M ⊤

theorem localOddCentral2A7N_of_ordinaryN {F : Type} [Group F] [Finite F] {K : Subgroup F}
    {z : F} (hB : A7TwoComponentOrdinaryN F K z) : LocalOddCentral2A7N F K z := by
  intro x hx hxE hne L M u v hL hM hLc hMc
  refine oddCore_normalClosure_le_center_of_family
    (P := fun N => IsConjSubgroup K N ∨ IsTwinDiag K x N) ?_ hLc hMc hL (Or.inl hM) ?_
  · intro N hN c hc
    rcases hN with hN | hN
    · exact Or.inl (hN.trans (isConjSubgroup_map_conj N c))
    · exact Or.inr (hN.map_conj hc)
  · intro N w hN hNc d n hd hn
    exact IsClassical2A7.commute_oddCore_of_component hNc (hB x hx hxE N w hN hNc) d n hd hn

theorem A7TwoComponentOrdinaryN.of_ordinary {F : Type} [Group F] (h : A7TwoComponentOrdinary F)
    (K : Subgroup F) (z : F) : A7TwoComponentOrdinaryN F K z :=
  fun x hx _ N w _ hNc M hM hNM => h x hx N w hNc M hM hNM

@[expose] def A7BStepN : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G], (∃ a b : G, a * b ≠ b * a) →
    ∀ (K : Subgroup G) (z : G), IsClassical2A7 ⊤ K z → CITBelow2A7 (Nat.card G) →
      (Subgroup.centralizer ({z} : Set G) ≤ Subgroup.normalizer (K : Set G) →
        A7TwoComponentOrdinaryN G K z) ∧
      (¬ Subgroup.centralizer ({z} : Set G) ≤ Subgroup.normalizer (K : Set G) →
        A7TwoComponentOrdinary G)

theorem a7BStepN_of_B (h : A7BStep) : A7BStepN :=
  fun G _ _ _ hnab K z hK hB =>
    ⟨fun _ => A7TwoComponentOrdinaryN.of_ordinary (h G hnab K z hK hB) K z,
      fun _ => h G hnab K z hK hB⟩

theorem localOddCentralStep2A7N_of_BN (h : A7BStepN) : LocalOddCentralStep2A7N :=
  fun G _ _ _ hnab K z hK hB =>
    ⟨fun ht => localOddCentral2A7N_of_ordinaryN ((h G hnab K z hK hB).1 ht),
      fun ht => localOddCentral2A7_of_ordinary ((h G hnab K z hK hB).2 ht)⟩

end NarrowedB

end CFSG.ClassicalInvolution.Hat2A7N
