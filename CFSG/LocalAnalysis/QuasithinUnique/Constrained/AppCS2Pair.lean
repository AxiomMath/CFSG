module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.AppCS2Swap
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.AppCS2C56

public section

namespace CFSG.QuasithinUnique.AppCS2

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.QuasithinUnique.AppC
  CFSG.QuasithinUnique.A5.Delta5 CFSG.QuasithinUnique.A5 CFSG.QuasithinUnique.DoubleA3 Equiv Subgroup
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {T M H S L : Subgroup G}

omit [Finite G] in
theorem blockU_L₂ (L : Subgroup G) (t : G) : blockU (conjR L t) = blockU2 L t := blockU_conjR L t

omit [Finite G] in
theorem comm_sup_left {A₁ A₂ B : Subgroup G} (h1 : ∀ a ∈ A₁, ∀ b ∈ B, a * b = b * a)
    (h2 : ∀ a ∈ A₂, ∀ b ∈ B, a * b = b * a) : ∀ a ∈ A₁ ⊔ A₂, ∀ b ∈ B, a * b = b * a := by
  have : A₁ ⊔ A₂ ≤ centralizer (B : Set G) :=
    sup_le (fun a ha => Subgroup.mem_centralizer_iff.2 fun b hb => (h1 a ha b hb).symm)
      (fun a ha => Subgroup.mem_centralizer_iff.2 fun b hb => (h2 a ha b hb).symm)
  intro a ha b hb
  exact (Subgroup.mem_centralizer_iff.1 (this ha) b hb).symm

omit [Finite G] in
theorem comm_sup_sup {A₁ A₂ B₁ B₂ : Subgroup G} (h11 : ∀ a ∈ A₁, ∀ b ∈ B₁, a * b = b * a)
    (h12 : ∀ a ∈ A₁, ∀ b ∈ B₂, a * b = b * a) (h21 : ∀ a ∈ A₂, ∀ b ∈ B₁, a * b = b * a)
    (h22 : ∀ a ∈ A₂, ∀ b ∈ B₂, a * b = b * a) :
    ∀ a ∈ A₁ ⊔ A₂, ∀ b ∈ B₁ ⊔ B₂, a * b = b * a := by
  have h1 : ∀ b ∈ B₁ ⊔ B₂, ∀ a ∈ A₁, b * a = a * b := by
    have := comm_sup_left (A₁ := B₁) (A₂ := B₂) (B := A₁) (fun b hb a ha => (h11 a ha b hb).symm)
      (fun b hb a ha => (h12 a ha b hb).symm)
    exact this
  have h2 : ∀ b ∈ B₁ ⊔ B₂, ∀ a ∈ A₂, b * a = a * b := by
    have := comm_sup_left (A₁ := B₁) (A₂ := B₂) (B := A₂) (fun b hb a ha => (h21 a ha b hb).symm)
      (fun b hb a ha => (h22 a ha b hb).symm)
    exact this
  have := comm_sup_left (A₁ := A₁) (A₂ := A₂) (B := B₁ ⊔ B₂)
    (fun a ha b hb => (h1 b hb a ha).symm) (fun a ha b hb => (h2 b hb a ha).symm)
  exact this

omit [Finite G] in
theorem centralizer_sup_inf (A B : Subgroup G) :
    centralizer ((A ⊔ B : Subgroup G) : Set G) = centralizer (A : Set G) ⊓ centralizer (B : Set G) := by
  ext x
  simp only [Subgroup.mem_inf, Subgroup.mem_centralizer_iff]
  constructor
  · intro h
    exact ⟨fun a ha => h a (Subgroup.mem_sup_left ha), fun a ha => h a (Subgroup.mem_sup_right ha)⟩
  · rintro ⟨h1, h2⟩ a ha
    exact comm_sup_left (A₁ := A) (A₂ := B) (B := Subgroup.zpowers x)
      (fun a ha b hb => by
        obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hb
        exact (Commute.zpow_right (show Commute a x from h1 a ha) k).eq)
      (fun a ha b hb => by
        obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hb
        exact (Commute.zpow_right (show Commute a x from h2 a ha) k).eq)
      a ha x (Subgroup.mem_zpowers x)

omit [Finite G] in
theorem conjR_comm_aux {A B : Subgroup G} (g : G) :
    conjR ⁅A, B⁆ g = ⁅conjR A g, conjR B g⁆ := C5.conjSubgroup_commutator A B g

structure Two (T M H S L : Subgroup G) (t x : G) where
  C : Cfg2 T M H S L t
  C' : Cfg2 T M H S (conjR L t) t⁻¹
  hx : x ∈ normalizer (S : Set G)
  hUV : ⁅blockU L, conjR (blockU L) x⁆ ≠ ⊥
  M₀ : Subgroup G
  hSM : S ≤ M₀
  hMT : M₀ ≤ T
  h2 : S.relIndex M₀ = 2
  hxM : x ∈ M₀
  hxS : x ∉ S

namespace Two

variable {t x : G} (X : Two T M H S L t x)
include X

theorem hVE : X.C.P.im (conjR (blockU L) x) = Estd := X.C.im_V_eq X.hx X.hUV

theorem U₂_le_D₁ : blockU2 L t ≤ s2I S L := by
  intro u hu
  refine ⟨X.C.D.blockU2_le_baum X.C.P.toPiData hu, Subgroup.mem_centralizer_iff.2 fun a ha => ?_⟩
  exact X.C.D.comm_elem a ha u (X.C.D.blockU2_le_L₂ hu)

theorem U₁_le_D₂ : blockU L ≤ s2I S (conjR L t) := by
  intro u hu
  refine ⟨X.C.U_le_baum hu, Subgroup.mem_centralizer_iff.2 fun b hb => ?_⟩
  exact (X.C.D.comm_elem u (X.C.D.blockU_le_L hu) b hb).symm

theorem V₁_comm_U₂ {v u : G} (hv : v ∈ conjR (blockU L) x) (hu : u ∈ blockU2 L t) :
    v * u = u * v :=
  Subgroup.mem_centralizer_iff.1 (X.C.D1_le_centralizer_V X.hx X.hVE (X.U₂_le_D₁ hu)) v hv

theorem conjR_V₁_cases {g : G} (hg : g ∈ S) :
    conjR (conjR (blockU L) x) g = conjR (blockU L) x ∨
      conjR (conjR (blockU L) x) g = conjR (blockU2 L t) x := by
  have hxg : x * g * x⁻¹ ∈ S := (Subgroup.mem_normalizer_iff.1 X.hx g).1 hg
  have e : conjR (conjR (blockU L) x) g = conjR (conjR (blockU L) (x * g * x⁻¹)) x := by
    rw [Dbl.conjR_conjR, Dbl.conjR_conjR]
    congr 1
    group
  rw [e]
  rcases X.C.D.conjR_blockU_cases hxg with h | h
  · left; rw [h]
  · right; rw [h]

theorem conjR_V₂_cases {g : G} (hg : g ∈ S) :
    conjR (conjR (blockU2 L t) x) g = conjR (blockU L) x ∨
      conjR (conjR (blockU2 L t) x) g = conjR (blockU2 L t) x := by
  have hxg : x * g * x⁻¹ ∈ S := (Subgroup.mem_normalizer_iff.1 X.hx g).1 hg
  have e : conjR (conjR (blockU2 L t) x) g = conjR (conjR (blockU2 L t) (x * g * x⁻¹)) x := by
    rw [Dbl.conjR_conjR, Dbl.conjR_conjR]
    congr 1
    group
  rw [e]
  by_cases hN : x * g * x⁻¹ ∈ normalizer (L : Set G)
  · right; rw [(X.C.D.conjR_blockU_of_mem ⟨hxg, hN⟩).2]
  · left; rw [(X.C.D.conjR_blockU_of_not_mem hxg hN).2]

theorem conjR_V₁_t : conjR (conjR (blockU L) x) t = conjR (blockU2 L t) x := by
  rcases X.conjR_V₁_cases X.C.D.ht with h | h
  · exfalso
    have hcomm : ⁅blockU2 L t, conjR (blockU L) x⁆ = ⊥ := by
      rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
      intro u hu
      rw [Subgroup.mem_centralizer_iff]
      intro v hv
      exact X.V₁_comm_U₂ hv hu
    apply X.hUV
    have h1 : conjR ⁅blockU L, conjR (blockU L) x⁆ t =
        ⁅blockU2 L t, conjR (conjR (blockU L) x) t⁆ := conjR_comm_aux t
    rw [h, hcomm] at h1
    exact Lin2.conjR_eq_bot_iff.1 h1
  · exact h

theorem hUV₂ : ⁅blockU2 L t, conjR (blockU2 L t) x⁆ ≠ ⊥ := by
  intro h
  apply X.hUV
  have h1 : conjR ⁅blockU L, conjR (blockU L) x⁆ t =
      ⁅blockU2 L t, conjR (conjR (blockU L) x) t⁆ := conjR_comm_aux t
  rw [X.conjR_V₁_t, h] at h1
  exact Lin2.conjR_eq_bot_iff.1 h1

theorem hVE₂ : X.C'.P.im (conjR (blockU2 L t) x) = Estd := by
  have := X.C'.im_V_eq X.hx (by rw [blockU_L₂]; exact X.hUV₂)
  rwa [blockU_L₂] at this

theorem V₂_comm_U₁ {v u : G} (hv : v ∈ conjR (blockU2 L t) x) (hu : u ∈ blockU L) :
    v * u = u * v := by
  have hD := X.C'.D1_le_centralizer_V X.hx (by rw [blockU_L₂]; exact X.hVE₂) (X.U₁_le_D₂ hu)
  rw [blockU_L₂] at hD
  exact Subgroup.mem_centralizer_iff.1 hD v hv

theorem V₁_comm_V₂ {a b : G} (ha : a ∈ conjR (blockU L) x) (hb : b ∈ conjR (blockU2 L t) x) :
    a * b = b * a := by
  have ha' : x * a * x⁻¹ ∈ blockU L := mem_conjSubgroup_iff.1 ha
  have hb' : x * b * x⁻¹ ∈ blockU2 L t := mem_conjSubgroup_iff.1 hb
  have hc : (x * a * x⁻¹) * (x * b * x⁻¹) = (x * b * x⁻¹) * (x * a * x⁻¹) :=
    X.C.D.U1_comm_U2 _ ha' _ hb'
  have e1 : (x * a * x⁻¹) * (x * b * x⁻¹) = x * (a * b) * x⁻¹ := by group
  have e2 : (x * b * x⁻¹) * (x * a * x⁻¹) = x * (b * a) * x⁻¹ := by group
  rw [e1, e2] at hc
  have := mul_left_cancel (mul_right_cancel hc)
  exact this

theorem U₂_V₁_bot : ⁅blockU2 L t, conjR (blockU L) x⁆ = ⊥ := by
  rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
  intro u hu
  rw [Subgroup.mem_centralizer_iff]
  intro v hv
  exact X.V₁_comm_U₂ hv hu

theorem U₁_V₂_bot : ⁅blockU L, conjR (blockU2 L t) x⁆ = ⊥ := by
  rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
  intro u hu
  rw [Subgroup.mem_centralizer_iff]
  intro v hv
  exact X.V₂_comm_U₁ hv hu

theorem s2SI_le_N_V₁ : s2SI S L ≤ normalizer (conjR (blockU L) x : Set G) := by
  intro g hg
  rw [← Lin2.conjR_eq_self_iff]
  rcases X.conjR_V₁_cases hg.1 with h | h
  · exact h
  · exfalso
    have hU := (X.C.D.conjR_blockU_of_mem hg).1
    have h1 : conjR ⁅blockU L, conjR (blockU L) x⁆ g =
        ⁅conjR (blockU L) g, conjR (conjR (blockU L) x) g⁆ := conjR_comm_aux g
    rw [hU, h, X.U₁_V₂_bot] at h1
    exact X.hUV (Lin2.conjR_eq_bot_iff.1 h1)

theorem s2SI_le_N_V₂ : s2SI S L ≤ normalizer (conjR (blockU2 L t) x : Set G) := by
  intro g hg
  rw [← Lin2.conjR_eq_self_iff]
  rcases X.conjR_V₂_cases hg.1 with h | h
  · exfalso
    have hU := (X.C.D.conjR_blockU_of_mem hg).2
    have h1 : conjR ⁅blockU2 L t, conjR (blockU2 L t) x⁆ g =
        ⁅conjR (blockU2 L t) g, conjR (conjR (blockU2 L t) x) g⁆ := conjR_comm_aux g
    rw [hU, h, X.U₂_V₁_bot] at h1
    exact X.hUV₂ (Lin2.conjR_eq_bot_iff.1 h1)
  · exact h

theorem conjR_V₁_of_not_mem {g : G} (hg : g ∈ S) (hn : g ∉ normalizer (L : Set G)) :
    conjR (conjR (blockU L) x) g = conjR (blockU2 L t) x ∧
      conjR (conjR (blockU2 L t) x) g = conjR (blockU L) x := by
  obtain ⟨hU1, hU2⟩ := X.C.D.conjR_blockU_of_not_mem hg hn
  refine ⟨?_, ?_⟩
  · rcases X.conjR_V₁_cases hg with h | h
    · exfalso
      have h1 : conjR ⁅blockU L, conjR (blockU L) x⁆ g =
          ⁅conjR (blockU L) g, conjR (conjR (blockU L) x) g⁆ := conjR_comm_aux g
      rw [hU1, h, X.U₂_V₁_bot] at h1
      exact X.hUV (Lin2.conjR_eq_bot_iff.1 h1)
    · exact h
  · rcases X.conjR_V₂_cases hg with h | h
    · exact h
    · exfalso
      have h1 : conjR ⁅blockU2 L t, conjR (blockU2 L t) x⁆ g =
          ⁅conjR (blockU2 L t) g, conjR (conjR (blockU2 L t) x) g⁆ := conjR_comm_aux g
      rw [hU2, h, X.U₁_V₂_bot] at h1
      exact X.hUV₂ (Lin2.conjR_eq_bot_iff.1 h1)

theorem mem_s2SI_of_normalizer_V₁ {g : G} (hg : g ∈ S)
    (hN : g ∈ normalizer (conjR (blockU L) x : Set G)) : g ∈ s2SI S L := by
  by_contra hn
  have hn' : g ∉ normalizer (L : Set G) := fun h => hn ⟨hg, h⟩
  have h := (X.conjR_V₁_of_not_mem hg hn').1
  have hV : conjR (conjR (blockU L) x) g = conjR (blockU L) x := Lin2.conjR_eq_self_iff.2 hN
  rw [hV] at h
  apply X.hUV
  rw [h]
  exact X.U₁_V₂_bot

theorem mem_s2SI_of_comm_V₁ {g : G} (hg : g ∈ S)
    (hc : ∀ v ∈ conjR (blockU L) x, g * v = v * g) : g ∈ s2SI S L :=
  X.mem_s2SI_of_normalizer_V₁ hg
    (Subgroup.centralizer_le_normalizer _
      (Subgroup.mem_centralizer_iff.2 fun v hv => (hc v hv).symm))

end Two

end CFSG.QuasithinUnique.AppCS2
