module

public import Mathlib.GroupTheory.Index

public section

namespace CFSG.CGT.PushingUpLit.BHS7

open Subgroup

section Core

variable {B : Type*} [Group B]

theorem map_inf_centralizer_set (e : B ≃* B) (X : Subgroup B) (S : Set B) :
    (X ⊓ centralizer S).map e.toMonoidHom =
      X.map e.toMonoidHom ⊓ centralizer (e '' S) := by
  ext z
  simp only [Subgroup.mem_map, Subgroup.mem_inf, Subgroup.mem_centralizer_iff]
  constructor
  · rintro ⟨x, ⟨hxX, hxS⟩, rfl⟩
    refine ⟨⟨x, hxX, rfl⟩, ?_⟩
    rintro _ ⟨s, hs, rfl⟩
    have := hxS s hs
    have h2 := congrArg e this
    simpa [map_mul] using h2
  · rintro ⟨⟨x, hxX, rfl⟩, hz⟩
    refine ⟨x, ⟨hxX, ?_⟩, rfl⟩
    intro s hs
    have := hz (e s) ⟨s, hs, rfl⟩
    apply e.injective
    simpa [map_mul] using this

theorem map_symm_map (α : B ≃* B) (X : Subgroup B) :
    (X.map α.toMonoidHom).map α.symm.toMonoidHom = X := by
  rw [Subgroup.map_map]
  have : α.symm.toMonoidHom.comp α.toMonoidHom = MonoidHom.id B := by
    ext y; simp
  rw [this, Subgroup.map_id]

theorem map_map_symm (α : B ≃* B) (X : Subgroup B) :
    (X.map α.symm.toMonoidHom).map α.toMonoidHom = X := by
  rw [Subgroup.map_map]
  have : α.toMonoidHom.comp α.symm.toMonoidHom = MonoidHom.id B := by
    ext y; simp
  rw [this, Subgroup.map_id]

theorem mem_centralizer_map_iff (e : B ≃* B) (Y : Subgroup B) (x : B) :
    e x ∈ centralizer ((Y.map e.toMonoidHom : Subgroup B) : Set B) ↔
      x ∈ centralizer (Y : Set B) := by
  simp only [Subgroup.mem_centralizer_iff, Subgroup.coe_map, MulEquiv.coe_toMonoidHom,
    Set.mem_image, SetLike.mem_coe]
  constructor
  · intro h y hy
    have := h (e y) ⟨y, hy, rfl⟩
    apply e.injective
    simpa [map_mul] using this
  · rintro h _ ⟨y, hy, rfl⟩
    have := h y hy
    have h2 := congrArg e this
    simpa [map_mul] using h2

section Finite

variable [Finite B]

theorem relIndex_ne_zero_of_finite (H K : Subgroup B) : H.relIndex K ≠ 0 := by
  unfold Subgroup.relIndex
  exact Subgroup.index_ne_zero_of_finite

theorem transport_core (W V : Subgroup B) (hWV : W ≤ V) (q : ℕ) (W₀ : Subgroup B)
    (hN : (centralizer (W : Set B)).index ≤ q)
    (hW₀ : W₀.relIndex W = q) (hW₀W : W₀ ≤ W)
    (hfix : ∀ b : B, b ∉ centralizer (W : Set B) → W ⊓ centralizer ({b} : Set B) = W₀)
    (α : B ≃* B) (hα : ¬ (W.map α.toMonoidHom ≤ centralizer (W : Set B))) :
    (V ⊓ centralizer ((W.map α.toMonoidHom : Subgroup B) : Set B)).relIndex V = q ∧
    ((W.map α.toMonoidHom) ⊓ centralizer (V : Set B)).relIndex (W.map α.toMonoidHom) = q ∧
    ∀ a ∈ W.map α.toMonoidHom, a ∉ centralizer (V : Set B) →
      V ⊓ centralizer ((W.map α.toMonoidHom : Subgroup B) : Set B) =
        V ⊓ centralizer ({a} : Set B) := by
  classical
  set A : Subgroup B := W.map α.toMonoidHom with hA
  set N : Subgroup B := centralizer (W : Set B) with hNdef
  set V'' : Subgroup B := V.map α.symm.toMonoidHom with hV''
  have hAW : A.map α.symm.toMonoidHom = W := map_symm_map α W
  have hVV'' : V''.map α.toMonoidHom = V := map_map_symm α V
  have hT1 : (V ⊓ centralizer (A : Set B)).map α.symm.toMonoidHom = V'' ⊓ N := by
    rw [map_inf_centralizer_set]
    congr 2
    rw [← MulEquiv.coe_toMonoidHom, ← Subgroup.coe_map, hAW]
  have hT2 : (A ⊓ centralizer (V : Set B)).map α.symm.toMonoidHom =
      W ⊓ centralizer (V'' : Set B) := by
    rw [map_inf_centralizer_set, hAW]
    congr 2
  have hrel1 : (V ⊓ centralizer (A : Set B)).relIndex V = (V'' ⊓ N).relIndex V'' := by
    rw [← hT1]
    exact (Subgroup.relIndex_map_map_of_injective (V ⊓ centralizer (A : Set B)) V
      α.symm.injective).symm
  have hup : (V'' ⊓ N).relIndex V'' ≤ q := by
    have h1 : (V'' ⊓ N).relIndex V'' = N.relIndex V'' := by
      rw [inf_comm, Subgroup.inf_relIndex_right]
    have h2 : N.relIndex V'' ≤ N.relIndex ⊤ :=
      Subgroup.relIndex_le_of_le_right le_top (relIndex_ne_zero_of_finite _ _)
    rw [h1]
    refine h2.trans ?_
    rw [Subgroup.relIndex_top_right]
    exact hN
  obtain ⟨a₀, ha₀A, ha₀N⟩ := IsConcreteLE.not_le_iff_exists.mp hα
  have hlow : q ≤ (V ⊓ centralizer (A : Set B)).relIndex V := by
    have hWC : W ⊓ centralizer (A : Set B) ≤ W₀ := by
      intro x hx
      have hxC : x ∈ centralizer (A : Set B) := hx.2
      have hxa : x ∈ W ⊓ centralizer ({a₀} : Set B) := by
        refine ⟨hx.1, Subgroup.mem_centralizer_iff.mpr ?_⟩
        intro h hh
        rw [Set.mem_singleton_iff] at hh
        subst hh
        exact Subgroup.mem_centralizer_iff.mp hxC _ ha₀A
      rw [hfix a₀ ha₀N] at hxa
      exact hxa
    have h1 : W₀.relIndex W ≤ (W ⊓ centralizer (A : Set B)).relIndex W :=
      Nat.le_of_dvd (Nat.pos_of_ne_zero (relIndex_ne_zero_of_finite _ _))
        (Subgroup.relIndex_dvd_of_le_left W hWC)
    have h2 : (centralizer (A : Set B)).relIndex W ≤ (centralizer (A : Set B)).relIndex V :=
      Subgroup.relIndex_le_of_le_right hWV (relIndex_ne_zero_of_finite _ _)
    have h3 : (W ⊓ centralizer (A : Set B)).relIndex W =
        (centralizer (A : Set B)).relIndex W := by
      rw [inf_comm, Subgroup.inf_relIndex_right]
    have h4 : (V ⊓ centralizer (A : Set B)).relIndex V =
        (centralizer (A : Set B)).relIndex V := by
      rw [inf_comm, Subgroup.inf_relIndex_right]
    rw [h4, ← hW₀]
    calc W₀.relIndex W ≤ (W ⊓ centralizer (A : Set B)).relIndex W := h1
      _ = (centralizer (A : Set B)).relIndex W := h3
      _ ≤ _ := h2
  have hc1 : (V ⊓ centralizer (A : Set B)).relIndex V = q := by
    refine le_antisymm ?_ hlow
    rw [hrel1]; exact hup
  have hV''N : ¬ V'' ≤ N := by
    intro hle
    have h1 : (V'' ⊓ N).relIndex V'' = 1 := by
      rw [inf_eq_left.mpr hle]
      exact Subgroup.relIndex_self _
    have hq : q = 1 := by rw [← hc1, hrel1]; exact h1
    have hW₀eq : W₀ = W := by
      have : W₀.relIndex W = 1 := hW₀.trans hq
      exact le_antisymm hW₀W (Subgroup.relIndex_eq_one.mp this)
    have h5 := hfix a₀ ha₀N
    rw [hW₀eq] at h5
    apply ha₀N
    show a₀ ∈ centralizer (W : Set B)
    rw [Subgroup.mem_centralizer_iff]
    intro w hw
    have h6 : w ∈ W ⊓ centralizer ({a₀} : Set B) := by rw [h5]; exact hw
    have hh := Subgroup.mem_centralizer_iff.mp h6.2 a₀ (Set.mem_singleton a₀)
    exact hh.symm
  obtain ⟨v₀, hv₀V'', hv₀N⟩ := IsConcreteLE.not_le_iff_exists.mp hV''N
  have hWC2 : W ⊓ centralizer (V'' : Set B) = W₀ := by
    apply le_antisymm
    · intro x hx
      have hxC : x ∈ centralizer (V'' : Set B) := hx.2
      have hxa : x ∈ W ⊓ centralizer ({v₀} : Set B) := by
        refine ⟨hx.1, Subgroup.mem_centralizer_iff.mpr ?_⟩
        intro h hh
        rw [Set.mem_singleton_iff] at hh
        subst hh
        exact Subgroup.mem_centralizer_iff.mp hxC _ hv₀V''
      rw [hfix v₀ hv₀N] at hxa
      exact hxa
    · intro x hx
      refine ⟨hW₀W hx, Subgroup.mem_centralizer_iff.mpr ?_⟩
      intro v hv
      by_cases hvN : v ∈ N
      · have hvN' : v ∈ centralizer (W : Set B) := hvN
        exact (Subgroup.mem_centralizer_iff.mp hvN' x (hW₀W hx)).symm
      · have hvN' : v ∉ centralizer (W : Set B) := hvN
        have hx' : x ∈ W ⊓ centralizer ({v} : Set B) := by rw [hfix v hvN']; exact hx
        exact Subgroup.mem_centralizer_iff.mp hx'.2 v (Set.mem_singleton v)
  have hc2 : (A ⊓ centralizer (V : Set B)).relIndex A = q := by
    have h1 := Subgroup.relIndex_map_map_of_injective (f := α.symm.toMonoidHom)
      (A ⊓ centralizer (V : Set B)) A α.symm.injective
    rw [hT2, hAW, hWC2] at h1
    exact h1.symm.trans hW₀
  have hc3 : ∀ a ∈ A, a ∉ centralizer (V : Set B) →
      V ⊓ centralizer (A : Set B) = V ⊓ centralizer ({a} : Set B) := by
    intro a haA haV
    obtain ⟨w, hwW, rfl⟩ := Subgroup.mem_map.mp haA
    have hwV'' : w ∉ centralizer (V'' : Set B) := by
      intro h
      apply haV
      have := (mem_centralizer_map_iff α V'' w).mpr h
      rwa [hVV''] at this
    have hwW₀ : w ∉ W₀ := by
      intro h
      apply hwV''
      rw [← hWC2] at h
      exact h.2
    have hCw : V'' ⊓ centralizer ({w} : Set B) = V'' ⊓ N := by
      apply le_antisymm
      · rintro v ⟨hvV, hvw⟩
        refine ⟨hvV, ?_⟩
        by_contra hvN
        have hvN' : v ∉ centralizer (W : Set B) := hvN
        have hw' : w ∈ W ⊓ centralizer ({v} : Set B) := by
          refine ⟨hwW, Subgroup.mem_centralizer_iff.mpr ?_⟩
          intro h hh
          rw [Set.mem_singleton_iff] at hh
          subst hh
          exact (Subgroup.mem_centralizer_iff.mp hvw w (Set.mem_singleton w)).symm
        rw [hfix v hvN'] at hw'
        exact hwW₀ hw'
      · rintro v ⟨hvV, hvN⟩
        have hvN' : v ∈ centralizer (W : Set B) := hvN
        refine ⟨hvV, Subgroup.mem_centralizer_iff.mpr ?_⟩
        intro h hh
        rw [Set.mem_singleton_iff] at hh
        subst hh
        exact Subgroup.mem_centralizer_iff.mp hvN' h hwW
    have hmapC : (V ⊓ centralizer ({α w} : Set B)).map α.symm.toMonoidHom =
        V'' ⊓ centralizer ({w} : Set B) := by
      rw [map_inf_centralizer_set]
      congr 2
      simp
    have hrelc : (V ⊓ centralizer ({α w} : Set B)).relIndex V = q := by
      have h1 := Subgroup.relIndex_map_map_of_injective (f := α.symm.toMonoidHom)
        (V ⊓ centralizer ({α w} : Set B)) V α.symm.injective
      rw [hmapC, hCw, ← hrel1] at h1
      exact h1.symm.trans hc1
    have hle : V ⊓ centralizer (A : Set B) ≤ V ⊓ centralizer ({α w} : Set B) := by
      apply inf_le_inf_left
      apply Subgroup.centralizer_le
      intro x hx
      rw [Set.mem_singleton_iff] at hx
      subst hx
      exact haA
    have hmul := Subgroup.relIndex_mul_relIndex (V ⊓ centralizer (A : Set B))
      (V ⊓ centralizer ({α w} : Set B)) V hle inf_le_left
    rw [hc1, hrelc] at hmul
    have hq0 : q ≠ 0 := by rw [← hc1]; exact relIndex_ne_zero_of_finite _ _
    have h7 : (V ⊓ centralizer (A : Set B)).relIndex
        (V ⊓ centralizer ({α w} : Set B)) = 1 := by
      apply Nat.eq_of_mul_eq_mul_right (Nat.pos_of_ne_zero hq0)
      rw [hmul, one_mul]
    exact le_antisymm hle (Subgroup.relIndex_eq_one.mp h7)
  exact ⟨hc1, hc2, hc3⟩

end Finite

end Core

section Ambient

variable {Γ : Type*} [Group Γ]

@[expose] def autImage (B W : Subgroup Γ) (α : ↥B ≃* ↥B) : Subgroup Γ :=
  ((W.subgroupOf B).map α.toMonoidHom).map B.subtype

theorem autImage_le (B W : Subgroup Γ) (α : ↥B ≃* ↥B) : autImage B W α ≤ B := by
  rintro _ ⟨x, -, rfl⟩
  exact x.2

theorem subgroupOf_autImage (B W : Subgroup Γ) (α : ↥B ≃* ↥B) :
    (autImage B W α).subgroupOf B = (W.subgroupOf B).map α.toMonoidHom :=
  Subgroup.comap_map_eq_self_of_injective B.subtype_injective _

theorem subgroupOf_centralizer_set (B : Subgroup Γ) (S : Set Γ) (hS : S ⊆ B) :
    (centralizer S).subgroupOf B = centralizer (Subtype.val ⁻¹' S : Set ↥B) := by
  ext b
  simp only [Subgroup.mem_subgroupOf, Subgroup.mem_centralizer_iff, Set.mem_preimage]
  constructor
  · intro h y hy
    apply Subtype.ext
    simpa using h y.1 hy
  · intro h s hs
    have := h ⟨s, hS hs⟩ hs
    simpa using congrArg Subtype.val this

theorem subgroupOf_centralizer (B Y : Subgroup Γ) (hY : Y ≤ B) :
    (centralizer (Y : Set Γ)).subgroupOf B =
      centralizer ((Y.subgroupOf B : Subgroup ↥B) : Set ↥B) := by
  rw [subgroupOf_centralizer_set B (Y : Set Γ) hY]
  rfl

theorem subgroupOf_centralizer_singleton (B : Subgroup Γ) (b : ↥B) :
    (centralizer ({(b : Γ)} : Set Γ)).subgroupOf B = centralizer ({b} : Set ↥B) := by
  rw [subgroupOf_centralizer_set B {(b : Γ)}
    (fun x hx => by rw [Set.mem_singleton_iff.mp hx]; exact b.2)]
  have : (Subtype.val ⁻¹' ({(b : Γ)} : Set Γ) : Set ↥B) = {b} := by
    ext x
    exact ⟨fun h => Subtype.ext h, fun h => by rw [Set.mem_singleton_iff.mp h]; rfl⟩
  rw [this]

theorem inf_subgroupOf' (H K L : Subgroup Γ) :
    (H ⊓ K).subgroupOf L = H.subgroupOf L ⊓ K.subgroupOf L :=
  Subgroup.comap_inf H K L.subtype

variable [Finite Γ]

theorem transport_ambient (B W V W₀ : Subgroup Γ) (hVB : V ≤ B) (hWV : W ≤ V) (hW₀W : W₀ ≤ W)
    (q : ℕ) (hN : (B ⊓ centralizer (W : Set Γ)).relIndex B ≤ q) (hW₀ : W₀.relIndex W = q)
    (hfix : ∀ b ∈ B, b ∉ centralizer (W : Set Γ) → W ⊓ centralizer ({b} : Set Γ) = W₀)
    (α : ↥B ≃* ↥B) (hα : ¬ autImage B W α ≤ centralizer (W : Set Γ)) :
    (V ⊓ centralizer (autImage B W α : Set Γ)).relIndex V = q ∧
    (autImage B W α ⊓ centralizer (V : Set Γ)).relIndex (autImage B W α) = q ∧
    ∀ a ∈ autImage B W α, a ∉ centralizer (V : Set Γ) →
      V ⊓ centralizer (autImage B W α : Set Γ) = V ⊓ centralizer ({a} : Set Γ) := by
  classical
  have hWB : W ≤ B := hWV.trans hVB
  have hW₀B : W₀ ≤ B := hW₀W.trans hWB
  set A : Subgroup Γ := autImage B W α with hA
  have hAB : A ≤ B := autImage_le B W α
  set WB : Subgroup ↥B := W.subgroupOf B with hWBdef
  set VB : Subgroup ↥B := V.subgroupOf B with hVBdef
  set W₀B : Subgroup ↥B := W₀.subgroupOf B with hW₀Bdef
  set AB : Subgroup ↥B := WB.map α.toMonoidHom with hABdef
  have hAsub : A.subgroupOf B = AB := subgroupOf_autImage B W α
  have hWVB : WB ≤ VB := fun x hx => hWV hx
  have hW₀WB : W₀B ≤ WB := fun x hx => hW₀W hx
  have hcentW : (centralizer (W : Set Γ)).subgroupOf B = centralizer (WB : Set ↥B) :=
    subgroupOf_centralizer B W hWB
  have hcentV : (centralizer (V : Set Γ)).subgroupOf B = centralizer (VB : Set ↥B) :=
    subgroupOf_centralizer B V hVB
  have hcentA : (centralizer (A : Set Γ)).subgroupOf B = centralizer (AB : Set ↥B) := by
    rw [subgroupOf_centralizer B A hAB, hAsub]
  have hNB : (centralizer (WB : Set ↥B)).index ≤ q := by
    have h1 : (centralizer (WB : Set ↥B)).index = (centralizer (W : Set Γ)).relIndex B := by
      rw [← hcentW]; rfl
    rw [h1, ← Subgroup.inf_relIndex_left B (centralizer (W : Set Γ))]
    exact hN
  have hW₀B' : W₀B.relIndex WB = q := by
    rw [hW₀Bdef, hWBdef]
    rw [Subgroup.relIndex_subgroupOf hWB]
    exact hW₀
  have hfixB : ∀ b : ↥B, b ∉ centralizer (WB : Set ↥B) →
      WB ⊓ centralizer ({b} : Set ↥B) = W₀B := by
    intro b hb
    have hb' : (b : Γ) ∉ centralizer (W : Set Γ) := by
      intro h
      apply hb
      rw [← hcentW]
      exact h
    have h1 := hfix (b : Γ) b.2 hb'
    have h2 : (W ⊓ centralizer ({(b : Γ)} : Set Γ)).subgroupOf B = W₀.subgroupOf B := by
      rw [h1]
    rw [inf_subgroupOf', subgroupOf_centralizer_singleton] at h2
    exact h2
  have hαB : ¬ (WB.map α.toMonoidHom ≤ centralizer (WB : Set ↥B)) := by
    intro h
    apply hα
    intro x hx
    have hxB : x ∈ B := hAB hx
    have hxA : (⟨x, hxB⟩ : ↥B) ∈ A.subgroupOf B := Subgroup.mem_subgroupOf.mpr hx
    rw [hAsub] at hxA
    have := h hxA
    rw [← hcentW] at this
    exact Subgroup.mem_subgroupOf.mp this
  obtain ⟨hc1, hc2, hc3⟩ := transport_core WB VB hWVB q W₀B hNB hW₀B' hW₀WB hfixB α hαB
  refine ⟨?_, ?_, ?_⟩
  · rw [← Subgroup.relIndex_subgroupOf hVB, inf_subgroupOf', hcentA]
    exact hc1
  · rw [← Subgroup.relIndex_subgroupOf hAB, inf_subgroupOf', hcentV, hAsub]
    exact hc2
  · intro a ha hna
    have haB : a ∈ B := hAB ha
    have haAB : (⟨a, haB⟩ : ↥B) ∈ AB := by
      rw [← hAsub]
      exact Subgroup.mem_subgroupOf.mpr ha
    have hna' : (⟨a, haB⟩ : ↥B) ∉ centralizer (VB : Set ↥B) := by
      rw [← hcentV]
      exact fun h => hna (Subgroup.mem_subgroupOf.mp h)
    have h3 := hc3 ⟨a, haB⟩ haAB hna'
    have h4 : (V ⊓ centralizer (A : Set Γ)).subgroupOf B =
        (V ⊓ centralizer ({a} : Set Γ)).subgroupOf B := by
      rw [inf_subgroupOf', inf_subgroupOf', hcentA,
        show (centralizer ({a} : Set Γ)).subgroupOf B = centralizer ({(⟨a, haB⟩ : ↥B)} : Set ↥B) from
          subgroupOf_centralizer_singleton B ⟨a, haB⟩]
      exact h3
    rw [Subgroup.subgroupOf_inj] at h4
    rwa [inf_eq_left.mpr (inf_le_left.trans hVB), inf_eq_left.mpr (inf_le_left.trans hVB)] at h4

end Ambient

end CFSG.CGT.PushingUpLit.BHS7
