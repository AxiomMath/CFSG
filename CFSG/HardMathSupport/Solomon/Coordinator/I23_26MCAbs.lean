module

public import Mathlib.GroupTheory.Commutator.Basic
public import Mathlib.Data.Set.Card
public import Mathlib.Tactic.Group

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator

open scoped commutatorElement

section Abstract

variable {G : Type*} [Group G]

theorem mc_normal_of_sup {T B N : Subgroup G} (hTB : T ⊔ B = ⊤) (hBN : B ≤ N)
    (hT : ∀ c ∈ T, ∀ n ∈ N, c * n * c⁻¹ ∈ N) : N.Normal := by
  rw [← Subgroup.normalizer_eq_top_iff, eq_top_iff, ← hTB]
  refine sup_le ?_ (hBN.trans Subgroup.le_normalizer)
  intro c hc
  rw [Subgroup.mem_normalizer_iff]
  intro n
  refine ⟨fun hn => hT c hc n hn, fun hn => ?_⟩
  have h := hT c⁻¹ (inv_mem hc) _ hn
  have e : c⁻¹ * (c * n * c⁻¹) * c⁻¹⁻¹ = n := by group
  rwa [e] at h

theorem mc_conj_mem_sup {W B : Subgroup G} [B.Normal] {c : G} (hc : ∀ w ∈ W, c * w * c⁻¹ ∈ W)
    {n : G} (hn : n ∈ W ⊔ B) : c * n * c⁻¹ ∈ W ⊔ B := by
  obtain ⟨w, hw, b, hb, rfl⟩ := Subgroup.mem_sup_of_normal_right.1 hn
  have e : c * (w * b) * c⁻¹ = (c * w * c⁻¹) * (c * b * c⁻¹) := by group
  rw [e]
  exact Subgroup.mul_mem_sup (hc w hw) (Subgroup.Normal.conj_mem inferInstance b hb c)

def mcCentralPre (N : Subgroup G) [N.Normal] : Subgroup G :=
  (Subgroup.center (G ⧸ N)).comap (QuotientGroup.mk' N)

instance (N : Subgroup G) [N.Normal] : (mcCentralPre N).Normal := by
  unfold mcCentralPre
  infer_instance

theorem mem_mcCentralPre {N : Subgroup G} [N.Normal] {p : G} :
    p ∈ mcCentralPre N ↔ ∀ g : G, ⁅p, g⁆ ∈ N := by
  unfold mcCentralPre
  rw [Subgroup.mem_comap, Subgroup.mem_center_iff]
  constructor
  · intro h g
    have h1 : QuotientGroup.mk' N ⁅p, g⁆ = 1 := by
      rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
      exact (h (QuotientGroup.mk' N g)).symm
    exact (QuotientGroup.eq_one_iff _).1 h1
  · intro h q
    obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective N q
    have h1 : QuotientGroup.mk' N ⁅p, g⁆ = 1 := (QuotientGroup.eq_one_iff _).2 (h g)
    rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm] at h1
    exact h1.symm

theorem le_mcCentralPre (N : Subgroup G) [N.Normal] : N ≤ mcCentralPre N := by
  intro x hx
  rw [mem_mcCentralPre]
  intro g
  have : ⁅x, g⁆ = x * (g * x⁻¹ * g⁻¹) := by simp [commutatorElement_def, mul_assoc]
  rw [this]
  exact N.mul_mem hx (Subgroup.Normal.conj_mem inferInstance _ (N.inv_mem hx) g)

theorem mc_comm_mul_mul {a b z₁ z₂ : G} (h1b : Commute z₁ b) (h12 : Commute z₁ z₂)
    (h2a : Commute z₂ a) : ⁅a * z₁, b * z₂⁆ = ⁅a, b⁆ := by
  rw [commutatorElement_def, commutatorElement_def, mul_inv_rev, mul_inv_rev]
  have e1 : z₁ * (b * z₂) = b * z₂ * z₁ := (h1b.mul_right h12).eq
  have e2 : z₂ * a⁻¹ = a⁻¹ * z₂ := h2a.inv_right.eq
  calc a * z₁ * (b * z₂) * (z₁⁻¹ * a⁻¹) * (z₂⁻¹ * b⁻¹)
      = a * (z₁ * (b * z₂)) * z₁⁻¹ * a⁻¹ * z₂⁻¹ * b⁻¹ := by group
    _ = a * b * (z₂ * a⁻¹) * z₂⁻¹ * b⁻¹ := by rw [e1]; group
    _ = a * b * a⁻¹ * b⁻¹ := by rw [e2]; group

theorem mc_comm_central {a b z₁ z₂ : G} (h1 : z₁ ∈ Subgroup.center G)
    (h2 : z₂ ∈ Subgroup.center G) : ⁅a * z₁, b * z₂⁆ = ⁅a, b⁆ :=
  mc_comm_mul_mul (show Commute b z₁ from Subgroup.mem_center_iff.1 h1 b).symm
    (show Commute z₂ z₁ from Subgroup.mem_center_iff.1 h1 z₂).symm
    (show Commute a z₂ from Subgroup.mem_center_iff.1 h2 a).symm

theorem mc_commute_of_perfect {L : Subgroup G} (hL : ⁅L, L⁆ = L) {n : G}
    (hn : ∀ u ∈ L, n⁻¹ * u * n ∈ L)
    (hz : ∀ u ∈ L, ∀ v ∈ L, v * (u⁻¹ * (n⁻¹ * u * n)) = (u⁻¹ * (n⁻¹ * u * n)) * v) :
    ∀ u ∈ L, n * u = u * n := by
  have h : ⁅L, L⁆ ≤ L ⊓ Subgroup.centralizer ({n} : Set G) := by
    rw [Subgroup.commutator_le]
    intro u hu v hv
    refine Subgroup.mem_inf.2 ⟨hL ▸ Subgroup.commutator_mem_commutator hu hv, ?_⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hu' : n⁻¹ * u * n = u * (u⁻¹ * (n⁻¹ * u * n)) := by group
    have hv' : n⁻¹ * v * n = v * (v⁻¹ * (n⁻¹ * v * n)) := by group
    have hzu : u⁻¹ * (n⁻¹ * u * n) ∈ L := L.mul_mem (L.inv_mem hu) (hn u hu)
    have hzv : v⁻¹ * (n⁻¹ * v * n) ∈ L := L.mul_mem (L.inv_mem hv) (hn v hv)
    have hc : n⁻¹ * ⁅u, v⁆ * n = ⁅u, v⁆ := by
      have e : n⁻¹ * ⁅u, v⁆ * n = ⁅n⁻¹ * u * n, n⁻¹ * v * n⁆ := by
        simp only [commutatorElement_def]; group
      rw [e, hu', hv']
      exact mc_comm_mul_mul (h1b := (show Commute v (u⁻¹ * (n⁻¹ * u * n)) from hz u hu v hv).symm)
        (h12 := (show Commute (v⁻¹ * (n⁻¹ * v * n)) (u⁻¹ * (n⁻¹ * u * n)) from
          hz u hu _ hzv).symm)
        (h2a := (show Commute u (v⁻¹ * (n⁻¹ * v * n)) from hz v hv u hu).symm)
    have h2 : n * ⁅u, v⁆ = ⁅u, v⁆ * n := by
      calc n * ⁅u, v⁆ = n * (n⁻¹ * ⁅u, v⁆ * n) := by rw [hc]
        _ = ⁅u, v⁆ * n := by group
    exact h2.symm
  intro u hu
  have hu' : u ∈ ⁅L, L⁆ := by rw [hL]; exact hu
  have := h hu'
  exact (Subgroup.mem_centralizer_singleton_iff.1 (Subgroup.mem_inf.1 this).2).symm

theorem mc_min_support {ι : Type*} [Finite ι] (A : ι → Subgroup G) [hA : ∀ i, (A i).Normal]
    (hmax : ∀ i (N : Subgroup G), N.Normal → A i ≤ N → N = A i ∨ N = ⊤)
    (hnab : ∀ i, ¬ ⁅(⊤ : Subgroup G), (⊤ : Subgroup G)⁆ ≤ A i)
    (T : Subgroup G) (hT : ∀ i, T ⊔ A i = ⊤) (hne : ∃ t ∈ T, ∃ i, t ∉ A i) :
    ∃ t ∈ T, (∃ i, t ∉ A i) ∧ ∀ i₀ j, t ∉ A i₀ → t ∉ A j → T ⊓ A i₀ ≤ A j := by
  classical
  let S : G → Set ι := fun t => {i | t ∉ A i}
  have hex : ∃ n, ∃ t ∈ T, (S t).Nonempty ∧ (S t).ncard = n := by
    obtain ⟨t, ht, i, hi⟩ := hne
    exact ⟨_, t, ht, ⟨i, hi⟩, rfl⟩
  obtain ⟨t, ht, hSne, hcard⟩ := Nat.find_spec hex
  have hmin : ∀ s ∈ T, (S s).Nonempty → (S t).ncard ≤ (S s).ncard := by
    intro s hs hsne
    rw [hcard]
    exact Nat.find_min' hex ⟨s, hs, hsne, rfl⟩
  refine ⟨t, ht, hSne, fun i₀ j hi₀ hj => ?_⟩
  have hcomm : ∀ w ∈ T ⊓ A i₀, ∀ i, ⁅t, w⁆ ∈ A i := by
    intro w hw
    by_contra hcon
    obtain ⟨i1, hi1⟩ := not_forall.1 hcon
    have hsT : ⁅t, w⁆ ∈ T := by
      rw [commutatorElement_def]
      exact T.mul_mem (T.mul_mem (T.mul_mem ht hw.1) (T.inv_mem ht)) (T.inv_mem hw.1)
    have hsub : S ⁅t, w⁆ ⊆ S t := by
      intro i hi
      by_contra hti
      have hti' : t ∈ A i := not_not.1 hti
      apply hi
      have : ⁅t, w⁆ = t * (w * t⁻¹ * w⁻¹) := by simp [commutatorElement_def, mul_assoc]
      rw [this]
      exact (A i).mul_mem hti' (Subgroup.Normal.conj_mem inferInstance _ ((A i).inv_mem hti') w)
    have hss : S ⁅t, w⁆ ⊂ S t := by
      rw [Set.ssubset_iff_of_subset hsub]
      refine ⟨i₀, hi₀, fun h => h ?_⟩
      rw [commutatorElement_def]
      exact (A i₀).mul_mem (Subgroup.Normal.conj_mem inferInstance w hw.2 t)
        ((A i₀).inv_mem hw.2)
    have hlt := Set.ncard_lt_ncard hss
    have := hmin _ hsT ⟨i1, hi1⟩
    omega
  set W := T ⊓ A i₀ with hW
  have hWT : ∀ c ∈ T, ∀ w ∈ W, c * w * c⁻¹ ∈ W := fun c hc w hw =>
    ⟨T.mul_mem (T.mul_mem hc hw.1) (T.inv_mem hc), Subgroup.Normal.conj_mem inferInstance w hw.2 c⟩
  have hNnorm : (W ⊔ A j).Normal := mc_normal_of_sup (hT j) le_sup_right
    (fun c hc n hn => mc_conj_mem_sup (hWT c hc) hn)
  rcases hmax j _ hNnorm le_sup_right with hN | hN
  · exact le_sup_left.trans hN.le
  · exfalso
    have htz : t ∈ mcCentralPre (A j) := by
      rw [mem_mcCentralPre]
      intro g
      have hg : g ∈ W ⊔ A j := hN ▸ Subgroup.mem_top g
      obtain ⟨w, hw, a, ha, rfl⟩ := Subgroup.mem_sup_of_normal_right.1 hg
      have e : ⁅t, w * a⁆ = ⁅t, w⁆ * (w * ⁅t, a⁆ * w⁻¹) := by
        simp only [commutatorElement_def]; group
      rw [e]
      refine (A j).mul_mem (hcomm w hw j) (Subgroup.Normal.conj_mem inferInstance _ ?_ w)
      have : ⁅t, a⁆ = (t * a * t⁻¹) * a⁻¹ := by simp [commutatorElement_def, mul_assoc]
      rw [this]
      exact (A j).mul_mem (Subgroup.Normal.conj_mem inferInstance a ha t) ((A j).inv_mem ha)
    rcases hmax j (mcCentralPre (A j)) inferInstance (le_mcCentralPre _) with hZ | hZ
    · exact hj (hZ ▸ htz)
    · apply hnab j
      rw [Subgroup.commutator_le]
      intro g₁ _ g₂ _
      exact (mem_mcCentralPre.1 (hZ ▸ Subgroup.mem_top g₁)) g₂

theorem mc_final {ι : Type*} (A : ι → Subgroup G) [hA : ∀ i, (A i).Normal]
    (hmax : ∀ i (N : Subgroup G), N.Normal → A i ≤ N → N = A i ∨ N = ⊤)
    (T : Subgroup G) (hT : ∀ i, T ⊔ A i = ⊤) (B : Subgroup G) (hB : ⁅B, B⁆ = B)
    {t : G} (htT : t ∈ T) {i₀ : ι} (ht : t ∉ A i₀)
    (hj : ∀ j, A j = A i₀ ∨ (t ∈ A j ∧ B ≤ A j))
    (hZ : ∀ z : G, (∀ j, z ∈ A j) → z ∈ Subgroup.center G) : B ≤ T := by
  let V : Subgroup G := Subgroup.closure {x | ∃ c ∈ T, x = c * t * c⁻¹}
  have hVT : V ≤ T := (Subgroup.closure_le _).2 (by
    rintro _ ⟨c, hc, rfl⟩
    exact T.mul_mem (T.mul_mem hc htT) (T.inv_mem hc))
  have hVconj : ∀ c ∈ T, ∀ v ∈ V, c * v * c⁻¹ ∈ V := by
    intro c hc v hv
    induction hv using Subgroup.closure_induction with
    | mem x hx =>
      obtain ⟨c', hc', rfl⟩ := hx
      exact Subgroup.subset_closure ⟨c * c', T.mul_mem hc hc', by group⟩
    | one => simp
    | mul x y _ _ hx hy =>
      have e : c * (x * y) * c⁻¹ = (c * x * c⁻¹) * (c * y * c⁻¹) := by group
      rw [e]; exact V.mul_mem hx hy
    | inv x _ hx =>
      have e : c * x⁻¹ * c⁻¹ = (c * x * c⁻¹)⁻¹ := by group
      rw [e]; exact V.inv_mem hx
  have htV : t ∈ V := Subgroup.subset_closure ⟨1, T.one_mem, by simp⟩
  have hNnorm : (V ⊔ A i₀).Normal := mc_normal_of_sup (hT i₀) le_sup_right
    (fun c hc n hn => mc_conj_mem_sup (hVconj c hc) hn)
  have hNtop : V ⊔ A i₀ = ⊤ := by
    rcases hmax i₀ _ hNnorm le_sup_right with h | h
    · exfalso
      apply ht
      have h1 : t ∈ V ⊔ A i₀ := Subgroup.mem_sup_left htV
      rw [h] at h1
      exact h1
    · exact h
  have hdec : ∀ b ∈ B, ∃ v ∈ T, ∃ z ∈ Subgroup.center G, b = v * z := by
    intro b hb
    obtain ⟨v, hv, a, ha, hva⟩ := Subgroup.mem_sup_of_normal_right.1
      (hNtop ▸ Subgroup.mem_top b : b ∈ V ⊔ A i₀)
    refine ⟨v, hVT hv, a, hZ a fun j => ?_, hva.symm⟩
    rcases hj j with h | ⟨htj, hBj⟩
    · rw [h]; exact ha
    · have hVj : V ≤ A j := (Subgroup.closure_le _).2 (by
        rintro _ ⟨c, hc, rfl⟩
        exact Subgroup.Normal.conj_mem inferInstance t htj c)
      have : a = v⁻¹ * b := by rw [← hva]; group
      rw [this]
      exact (A j).mul_mem ((A j).inv_mem (hVj hv)) (hBj hb)
  calc B = ⁅B, B⁆ := hB.symm
    _ ≤ T := by
      rw [Subgroup.commutator_le]
      intro b₁ hb₁ b₂ hb₂
      obtain ⟨v₁, hv₁, z₁, hz₁, rfl⟩ := hdec b₁ hb₁
      obtain ⟨v₂, hv₂, z₂, hz₂, rfl⟩ := hdec b₂ hb₂
      rw [mc_comm_central hz₁ hz₂, commutatorElement_def]
      exact T.mul_mem (T.mul_mem (T.mul_mem hv₁ hv₂) (T.inv_mem hv₁)) (T.inv_mem hv₂)

end Abstract

end CFSG.HardMathSupport.Solomon.Coordinator
