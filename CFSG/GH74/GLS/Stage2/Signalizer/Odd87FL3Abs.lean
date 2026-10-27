module

public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87Cell

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Odd87

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage2.Local
open scoped commutatorElement

section Helpers

theorem mem_normalizer_of_forall {G : Type*} [Group G] {T : Subgroup G} {g : G}
    (h1 : ∀ t ∈ T, g * t * g⁻¹ ∈ T) (h2 : ∀ t ∈ T, g⁻¹ * t * g ∈ T) :
    g ∈ normalizer (T : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro t
  refine ⟨h1 t, fun ht => ?_⟩
  have := h2 _ ht
  simpa [mul_assoc] using this

theorem mem_normalizer_inf_of_normal {G : Type*} [Group G] {X C : Subgroup G} [hC : C.Normal] {g : G}
    (hg : g ∈ normalizer (X : Set G)) : g ∈ normalizer ((X ⊓ C : Subgroup G) : Set G) := by
  refine mem_normalizer_of_forall (fun t ht => ?_) (fun t ht => ?_)
  · exact ⟨(Subgroup.mem_normalizer_iff.mp hg t).mp ht.1, hC.conj_mem t ht.2 g⟩
  · have hg' : g⁻¹ ∈ normalizer (X : Set G) := (normalizer (X : Set G)).inv_mem hg
    have h1 := (Subgroup.mem_normalizer_iff.mp hg' t).mp ht.1
    have h2 := hC.conj_mem t ht.2 g⁻¹
    rw [inv_inv] at h1 h2
    exact ⟨h1, h2⟩

theorem commutator_zpowers_eq {G : Type*} [Group G] (X : Subgroup G) {u v : G} (hu : u * u = 1)
    (hv : v * v = 1) (h : ∀ x ∈ X, ⁅x, u⁆ = ⁅x, v⁆) : ⁅X, zpowers u⁆ = ⁅X, zpowers v⁆ := by
  have key : ∀ {u v : G}, u * u = 1 → (∀ x ∈ X, ⁅x, u⁆ = ⁅x, v⁆) → ⁅X, zpowers u⁆ ≤ ⁅X, zpowers v⁆ := by
    intro u v hu h
    refine Subgroup.commutator_le.mpr fun x hx y hy => ?_
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
    have hu2 : u ^ (2 : ℤ) = 1 := by rw [zpow_two]; exact hu
    rcases Int.even_or_odd' n with ⟨m, rfl | rfl⟩
    · rw [zpow_mul, hu2, one_zpow, commutatorElement_one_right]
      exact Subgroup.one_mem _
    · rw [zpow_add_one, zpow_mul, hu2, one_zpow, one_mul, h x hx]
      exact Subgroup.commutator_mem_commutator hx (Subgroup.mem_zpowers v)
  exact le_antisymm (key hu h) (key hv fun x hx => (h x hx).symm)

end Helpers

section Abs

variable {A : Type} [Group A] [Finite A] {zb : A} {p : ℕ} {X : Subgroup A}

theorem CellData.inf_centralizer_layer (hd : CellData zb p X) :
    X ⊓ centralizer ((layer A : Subgroup A) : Set A) = ⊥ := by
  have hK : (layer A).Normal := layer_normal
  have hCn : (centralizer ((layer A : Subgroup A) : Set A)).Normal := normal_centralizer_of_normal (layer A)
  set T : Subgroup A := X ⊓ centralizer ((layer A : Subgroup A) : Set A) with hT
  have hTp : IsPGroup p ↥T := hd.A4.pgroup.to_le inf_le_left
  have hzX : zb ∈ normalizer (X : Set A) := z_mem_normalizer_of_sig4A hd.A4
  have hnormT : T.Normal := by
    rw [← Subgroup.normalizer_eq_top_iff, eq_top_iff, ← hd.gen]
    refine sup_le (sup_le ?_ ?_) ?_
    · intro k hk
      refine mem_normalizer_of_forall (fun t ht => ?_) (fun t ht => ?_)
      · have h := Subgroup.mem_centralizer_iff.mp ht.2 k hk
        have e : k * t * k⁻¹ = t := by rw [h]; simp
        rw [e]; exact ht
      · have h := Subgroup.mem_centralizer_iff.mp ht.2 k⁻¹ ((layer A).inv_mem hk)
        have e : k⁻¹ * t * k = t := by rw [h]; simp
        rw [e]; exact ht
    · exact fun x hx => mem_normalizer_inf_of_normal (Subgroup.le_normalizer hx)
    · exact (Subgroup.zpowers_le).mpr (mem_normalizer_inf_of_normal hzX)
  have hle : T ≤ pCore p A := le_sSup ⟨hnormT, hTp⟩
  exact le_bot_iff.mp (hd.op ▸ hle)

theorem CellData.inner_decomp (hd : CellData zb p X) (hZ : center ↥(layer A) = ⊥) {s : A}
    (hs : s ∈ layer A) (hact : ∀ k ∈ layer A, zb * k * zb⁻¹ = s * k * s⁻¹) :
    s * s = 1 ∧ zb * s = s * zb ∧ s⁻¹ * zb ∈ centralizer ((layer A : Subgroup A) : Set A) ∧
      s⁻¹ * zb ∈ centralizer (X : Set A) ∧ (∀ x ∈ X, zb * x * zb⁻¹ = s * x * s⁻¹) ∧
      ⁅X, zpowers s⁆ = X ∧ (∀ j ∈ layer A, j * zb = zb * j ↔ j * s = s * j) := by
  have hK : (layer A).Normal := layer_normal
  have hCn : (centralizer ((layer A : Subgroup A) : Set A)).Normal := normal_centralizer_of_normal (layer A)
  have hzX : zb ∈ normalizer (X : Set A) := z_mem_normalizer_of_sig4A hd.A4
  have hS1 := hd.inf_centralizer_layer
  have hsz : zb * s = s * zb := by
    have h := hact s hs
    have h2 : zb * s * zb⁻¹ = s := by rw [h]; group
    calc zb * s = zb * s * zb⁻¹ * zb := by group
      _ = s * zb := by rw [h2]
  have hc : s⁻¹ * zb ∈ centralizer ((layer A : Subgroup A) : Set A) := by
    refine Subgroup.mem_centralizer_iff.mpr fun k hk => ?_
    have h := hact k hk
    calc k * (s⁻¹ * zb) = s⁻¹ * (s * k * s⁻¹) * zb := by group
      _ = s⁻¹ * (zb * k * zb⁻¹) * zb := by rw [h]
      _ = (s⁻¹ * zb) * k := by group
  have hss : s * s = 1 := by
    have hcc : (s⁻¹ * zb) * (s⁻¹ * zb) ∈ centralizer ((layer A : Subgroup A) : Set A) :=
      (centralizer ((layer A : Subgroup A) : Set A)).mul_mem hc hc
    have hz2 := hd.z2
    have e : (s⁻¹ * zb) * (s⁻¹ * zb) = s⁻¹ * s⁻¹ := by
      calc (s⁻¹ * zb) * (s⁻¹ * zb) = s⁻¹ * (zb * s⁻¹) * zb := by group
        _ = s⁻¹ * (s⁻¹ * zb) * zb := by
          have : zb * s⁻¹ = s⁻¹ * zb := by
            calc zb * s⁻¹ = s⁻¹ * (s * zb) * s⁻¹ := by group
              _ = s⁻¹ * (zb * s) * s⁻¹ := by rw [hsz]
              _ = s⁻¹ * zb := by group
          rw [this]
        _ = s⁻¹ * s⁻¹ * (zb * zb) := by group
        _ = s⁻¹ * s⁻¹ := by rw [hz2]; group
    rw [e] at hcc
    have hu : s⁻¹ * s⁻¹ ∈ layer A := (layer A).mul_mem ((layer A).inv_mem hs) ((layer A).inv_mem hs)
    have hmem : (⟨s⁻¹ * s⁻¹, hu⟩ : ↥(layer A)) ∈ center ↥(layer A) := by
      refine Subgroup.mem_center_iff.mpr fun g => ?_
      apply Subtype.ext
      exact Subgroup.mem_centralizer_iff.mp hcc g.1 g.2
    rw [hZ, Subgroup.mem_bot] at hmem
    have h1 : s⁻¹ * s⁻¹ = 1 := congrArg Subtype.val hmem
    calc s * s = (s⁻¹ * s⁻¹)⁻¹ := by rw [mul_inv_rev, inv_inv]
      _ = 1 := by rw [h1]; simp
  have hsN : s ∈ normalizer (X : Set A) :=
    hd.A4.inv s (Subgroup.mem_top s) (Subgroup.mem_centralizer_singleton_iff.mpr hsz.symm)
  have hcN : s⁻¹ * zb ∈ normalizer (X : Set A) :=
    (normalizer (X : Set A)).mul_mem ((normalizer (X : Set A)).inv_mem hsN) hzX
  have hcX : s⁻¹ * zb ∈ centralizer (X : Set A) := by
    refine Subgroup.mem_centralizer_iff.mpr fun x hx => ?_
    have hmem : ⁅s⁻¹ * zb, x⁆ ∈ X ⊓ centralizer ((layer A : Subgroup A) : Set A) := by
      refine ⟨?_, ?_⟩
      · have h1 : (s⁻¹ * zb) * x * (s⁻¹ * zb)⁻¹ ∈ X := (Subgroup.mem_normalizer_iff.mp hcN x).mp hx
        have : ⁅s⁻¹ * zb, x⁆ = ((s⁻¹ * zb) * x * (s⁻¹ * zb)⁻¹) * x⁻¹ := by
          simp [commutatorElement_def, mul_assoc]
        rw [this]
        exact X.mul_mem h1 (X.inv_mem hx)
      · have h1 : x * (s⁻¹ * zb)⁻¹ * x⁻¹ ∈ centralizer ((layer A : Subgroup A) : Set A) :=
          hCn.conj_mem _ ((centralizer ((layer A : Subgroup A) : Set A)).inv_mem hc) x
        have : ⁅s⁻¹ * zb, x⁆ = (s⁻¹ * zb) * (x * (s⁻¹ * zb)⁻¹ * x⁻¹) := by
          simp [commutatorElement_def, mul_assoc]
        rw [this]
        exact (centralizer ((layer A : Subgroup A) : Set A)).mul_mem hc h1
    rw [hS1, Subgroup.mem_bot] at hmem
    have h2 : (s⁻¹ * zb) * x * (s⁻¹ * zb)⁻¹ * x⁻¹ = 1 := hmem
    calc x * (s⁻¹ * zb) = ((s⁻¹ * zb) * x * (s⁻¹ * zb)⁻¹ * x⁻¹) * x * (s⁻¹ * zb) := by rw [h2]; group
      _ = (s⁻¹ * zb) * x := by group
  have hact_X : ∀ x ∈ X, zb * x * zb⁻¹ = s * x * s⁻¹ := by
    intro x hx
    have hcx := Subgroup.mem_centralizer_iff.mp hcX x hx
    calc zb * x * zb⁻¹ = s * ((s⁻¹ * zb) * x * (s⁻¹ * zb)⁻¹) * s⁻¹ := by group
      _ = s * (x * (s⁻¹ * zb) * (s⁻¹ * zb)⁻¹) * s⁻¹ := by rw [← hcx]
      _ = s * x * s⁻¹ := by group
  refine ⟨hss, hsz, hc, hcX, hact_X, ?_, ?_⟩
  · have hcomm_eq : ⁅X, zpowers s⁆ = ⁅X, zpowers zb⁆ := by
      refine commutator_zpowers_eq X hss hd.z2 fun x hx => ?_
      have h1 := hact_X x⁻¹ (X.inv_mem hx)
      calc ⁅x, s⁆ = x * (s * x⁻¹ * s⁻¹) := by simp [commutatorElement_def, mul_assoc]
        _ = x * (zb * x⁻¹ * zb⁻¹) := by rw [h1]
        _ = ⁅x, zb⁆ := by simp [commutatorElement_def, mul_assoc]
    rw [hcomm_eq]
    exact hd.A4.comm
  · intro j hj
    have hjc : j * (s⁻¹ * zb) = (s⁻¹ * zb) * j := Subgroup.mem_centralizer_iff.mp hc j hj
    constructor
    · intro h
      have h2 : j * s * (s⁻¹ * zb) = s * j * (s⁻¹ * zb) := by
        calc j * s * (s⁻¹ * zb) = j * zb := by group
          _ = zb * j := h
          _ = s * ((s⁻¹ * zb) * j) := by group
          _ = s * (j * (s⁻¹ * zb)) := by rw [hjc]
          _ = s * j * (s⁻¹ * zb) := by group
      exact mul_right_cancel h2
    · intro h
      calc j * zb = j * s * (s⁻¹ * zb) := by group
        _ = s * j * (s⁻¹ * zb) := by rw [h]
        _ = s * (j * (s⁻¹ * zb)) := by group
        _ = s * ((s⁻¹ * zb) * j) := by rw [hjc]
        _ = zb * j := by group

theorem CellData.le_layer_of_inner (hd : CellData zb p X) (hZ : center ↥(layer A) = ⊥) {s : A}
    (hs : s ∈ layer A) (hact : ∀ k ∈ layer A, zb * k * zb⁻¹ = s * k * s⁻¹) : X ≤ layer A := by
  have hK : (layer A).Normal := layer_normal
  obtain ⟨-, -, -, -, hX, -, -⟩ := hd.inner_decomp hZ hs hact
  refine x_le_layer_of_comm hd.z2 hd.A4 hd.op hd.gen fun x hx => ?_
  refine Subgroup.mem_sup_left ?_
  have h1 := hX x⁻¹ (X.inv_mem hx)
  have h2 : x * s * x⁻¹ ∈ layer A := hK.conj_mem s hs x
  have e : ⁅x, zb⁆ = (x * s * x⁻¹) * s⁻¹ := by
    calc ⁅x, zb⁆ = x * (zb * x⁻¹ * zb⁻¹) := by simp [commutatorElement_def, mul_assoc]
      _ = x * (s * x⁻¹ * s⁻¹) := by rw [h1]
      _ = (x * s * x⁻¹) * s⁻¹ := by group
  rw [e]
  exact (layer A).mul_mem h2 ((layer A).inv_mem hs)

end Abs

end CFSG.GH74.GLS.Stage2.Signalizer.Odd87
