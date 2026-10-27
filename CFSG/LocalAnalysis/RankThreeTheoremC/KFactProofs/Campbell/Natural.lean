module

public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Campbell.GL32Facts
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Campbell.Commutator

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Campbell

section
open CFSG.Open Subgroup CFSG.QuasithinUnique.Setup.Family
open scoped Pointwise commutatorElement

variable {A : Type} [Group A] [Finite A] {X K R P : Subgroup A}

theorem natB0_surj_of_invariant {B₀ D : Subgroup A} (b : ↥D →* Multiplicative (Fin 3 → ZMod 2))
    (hinv : ∀ (g : GL32) (u : ↥D), (u : A) ∈ B₀ → ∃ u' : ↥D, (u' : A) ∈ B₀ ∧
      Multiplicative.toAdd (b u') =
        ((g : GL32) : Matrix (Fin 3) (Fin 3) (ZMod 2)).mulVec (Multiplicative.toAdd (b u)))
    (hne : ∃ u : ↥D, (u : A) ∈ B₀ ∧ Multiplicative.toAdd (b u) ≠ 0) :
    ∀ v : Fin 3 → ZMod 2, ∃ u : ↥D, (u : A) ∈ B₀ ∧ Multiplicative.toAdd (b u) = v := by
  let T : AddSubgroup (Fin 3 → ZMod 2) :=
    { carrier := {v | ∃ u : ↥D, (u : A) ∈ B₀ ∧ Multiplicative.toAdd (b u) = v}
      zero_mem' := ⟨1, B₀.one_mem, by simp⟩
      add_mem' := by
        rintro _ _ ⟨u, hu, rfl⟩ ⟨u', hu', rfl⟩
        exact ⟨u * u', B₀.mul_mem hu hu', by simp⟩
      neg_mem' := by
        rintro _ ⟨u, hu, rfl⟩
        refine ⟨u⁻¹, B₀.inv_mem hu, ?_⟩
        rw [map_inv]
        rfl }
  have hT : T = ⊥ ∨ T = ⊤ := natural_irreducible (T := T) (by
    rintro g _ ⟨u, hu, rfl⟩
    exact hinv g u hu)
  rcases hT with hT | hT
  · exfalso
    obtain ⟨u, hu, hu0⟩ := hne
    have hmem : Multiplicative.toAdd (b u) ∈ T := ⟨u, hu, rfl⟩
    rw [hT] at hmem
    exact hu0 ((AddSubgroup.mem_bot).1 hmem)
  · intro v
    have hmem : v ∈ T := by rw [hT]; trivial
    exact hmem

theorem natB0_commutator_eq_bot (h : CampbellHyp X K R P)
    (hcent : ∀ k ∈ K, ∀ x ∈ (⁅omegaCenter (K ⊓ pCoreOf 2 X), K⁆ : Subgroup A),
      k * x * k⁻¹ = x) :
    ⁅omegaCenter (K ⊓ pCoreOf 2 X), K⁆ = ⊥ := by
  have hKgen := closure_odd_of_perfect h.K_perfect
  rw [eq_bot_iff, Subgroup.commutator_le]
  intro w hw k hk
  have key : ∀ k ∈ K, k * w * k⁻¹ = w := by
    refine centralizes_of_odd_generation hKgen (fun k hk _ => ?_)
    have hc : w⁻¹ * (k * w * k⁻¹) = ⁅w⁻¹, k⁆ := by
      simp [commutatorElement_def, mul_assoc]
    have hcB : ⁅w⁻¹, k⁆ ∈ ⁅omegaCenter (K ⊓ pCoreOf 2 X), K⁆ :=
      Subgroup.commutator_mem_commutator ((omegaCenter _).inv_mem hw) hk
    have hcW := h.commutator_W_le hcB
    obtain ⟨hcX, -, hc2⟩ := mem_omegaCenter.1 hcW
    rw [hc]
    exact ⟨hc2, hcent k hk _ hcB, (mem_omegaCenter.1 hw).2.1 _ hcX⟩
  rw [Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm]
  have := key k hk
  rw [mul_inv_eq_iff_eq_mul] at this
  exact this.symm

theorem CampbellHyp.natData_B0 (h : CampbellHyp X K R P) {D C₀ : Subgroup A}
    (hZD : CFSG.Quasithin.centerOf (CFSG.Quasithin.c134Q X K) ≤ D)
    (hC₀K : K ≤ centralizer (C₀ : Set A)) (hN : HasNatSection K D C₀) :
    ∃ (a : ↥K →* GL32) (b : ↥D →* Multiplicative (Fin 3 → ZMod 2)),
      Function.Surjective a ∧ a.ker = CFSG.pCore 2 ↥K ∧ b.ker = C₀.subgroupOf D ∧
      (∀ (k : ↥K) (u v : ↥D), (v : A) = k * u * k⁻¹ →
        Multiplicative.toAdd (b v) = ((a k : GL32) : Matrix (Fin 3) (Fin 3) (ZMod 2)).mulVec
          (Multiplicative.toAdd (b u))) ∧
      ⁅omegaCenter (K ⊓ pCoreOf 2 X), K⁆ ≤ D ∧
      ∀ v : Fin 3 → ZMod 2, ∃ u : ↥D,
        (u : A) ∈ ⁅omegaCenter (K ⊓ pCoreOf 2 X), K⁆ ∧ Multiplicative.toAdd (b u) = v := by
  obtain ⟨-, -, a, b, ha, hker, -, hbker, hequiv⟩ := hN
  have hBD : ⁅omegaCenter (K ⊓ pCoreOf 2 X), K⁆ ≤ D :=
    h.commutator_W_le_center_Q.trans hZD
  refine ⟨a, b, ha, hker, hbker, hequiv, hBD, ?_⟩
  have hnorm : ∀ k ∈ K, ∀ x ∈ (⁅omegaCenter (K ⊓ pCoreOf 2 X), K⁆ : Subgroup A),
      k * x * k⁻¹ ∈ (⁅omegaCenter (K ⊓ pCoreOf 2 X), K⁆ : Subgroup A) := fun k hk x hx =>
    (Subgroup.mem_normalizer_iff.1 (h.normalizer_B0 (h.K_le hk)) x).1 hx
  refine natB0_surj_of_invariant b ?_ ?_
  · intro g u hu
    obtain ⟨k, rfl⟩ := ha g
    exact ⟨⟨(k : A) * u * (k : A)⁻¹, hBD (hnorm k k.2 u hu)⟩, hnorm k k.2 u hu,
      hequiv k u _ rfl⟩
  · by_contra hcon
    push Not at hcon
    refine h.commutator_W_ne_bot (natB0_commutator_eq_bot h ?_)
    intro k hk x hx
    have hxD := hBD hx
    have hb1 : b ⟨x, hxD⟩ = 1 := by simpa using hcon ⟨x, hxD⟩ hx
    have hxC : x ∈ C₀ := by
      have hker' : (⟨x, hxD⟩ : ↥D) ∈ b.ker := hb1
      rw [hbker] at hker'
      exact hker'
    have hcomm := Subgroup.mem_centralizer_iff.1 (hC₀K hk) x hxC
    rw [mul_inv_eq_iff_eq_mul]
    exact hcomm.symm
end

section
open CFSG.Open Subgroup CFSG.QuasithinUnique.Setup.Family
open scoped Pointwise

variable {A : Type} [Group A] [Finite A] {X K R P : Subgroup A}

theorem natIndex_card_vec : Nat.card (Multiplicative (Fin 3 → ZMod 2)) = 8 := by
  rw [Nat.card_congr Multiplicative.toAdd, Nat.card_eq_fintype_card]
  simp

theorem natIndex_relIndex_eight {B₀ D C₀ : Subgroup A} (hB₀D : B₀ ≤ D)
    (b : ↥D →* Multiplicative (Fin 3 → ZMod 2)) (hbker : b.ker = C₀.subgroupOf D)
    (hbB₀ : ∀ v : Fin 3 → ZMod 2, ∃ u : ↥D, (u : A) ∈ B₀ ∧ Multiplicative.toAdd (b u) = v) :
    (B₀ ⊓ C₀).relIndex B₀ = 8 := by
  have h1 : (B₀ ⊓ C₀).relIndex B₀ = (C₀.subgroupOf D).relIndex (B₀.subgroupOf D) := by
    rw [relIndex_subgroupOf hB₀D, inf_comm, inf_relIndex_right]
  have hmap : (B₀.subgroupOf D).map b = ⊤ := by
    rw [eq_top_iff]
    intro x _
    obtain ⟨u, hu, hux⟩ := hbB₀ (Multiplicative.toAdd x)
    exact ⟨u, hu, by simpa using hux⟩
  rw [h1, ← hbker, relIndex_ker, hmap, Subgroup.card_top, natIndex_card_vec]

theorem CampbellHyp.relIndex_eight_of_hasNatSection (h : CampbellHyp X K R P) {D C₀ : Subgroup A}
    (hZD : CFSG.Quasithin.centerOf (CFSG.Quasithin.c134Q X K) ≤ D)
    (hC₀K : K ≤ centralizer (C₀ : Set A)) (hN : HasNatSection K D C₀) :
    (⁅omegaCenter (K ⊓ pCoreOf 2 X), K⁆ ⊓ C₀).relIndex
      ⁅omegaCenter (K ⊓ pCoreOf 2 X), K⁆ = 8 := by
  obtain ⟨_, b, _, _, hbker, _, hB₀D, hbB₀⟩ := h.natData_B0 hZD hC₀K hN
  exact natIndex_relIndex_eight hB₀D b hbker hbB₀
end

section
open CFSG.Open Subgroup CFSG.QuasithinUnique.Setup.Family
open scoped Pointwise

variable {A : Type} [Group A] [Finite A] {X K R P : Subgroup A}

open scoped Classical in
noncomputable def natFaith_coord (D : Subgroup A) (b : ↥D →* Multiplicative (Fin 3 → ZMod 2))
    (x : A) : Fin 3 → ZMod 2 :=
  if hx : x ∈ D then Multiplicative.toAdd (b ⟨x, hx⟩) else 0

theorem natFaith_coord_of_mem {D : Subgroup A} (b : ↥D →* Multiplicative (Fin 3 → ZMod 2)) {x : A}
    (hx : x ∈ D) : natFaith_coord D b x = Multiplicative.toAdd (b ⟨x, hx⟩) := by
  simp [natFaith_coord, hx]

theorem natFaith_coord_mul {D : Subgroup A} (b : ↥D →* Multiplicative (Fin 3 → ZMod 2)) {x y : A}
    (hx : x ∈ D) (hy : y ∈ D) :
    natFaith_coord D b (x * y) = natFaith_coord D b x + natFaith_coord D b y := by
  rw [natFaith_coord_of_mem b (D.mul_mem hx hy), natFaith_coord_of_mem b hx,
    natFaith_coord_of_mem b hy]
  have : (⟨x * y, D.mul_mem hx hy⟩ : ↥D) = ⟨x, hx⟩ * ⟨y, hy⟩ := rfl
  rw [this, map_mul, toAdd_mul]

theorem natFaith_coord_eq_zero_iff {D C₀ : Subgroup A} (b : ↥D →* Multiplicative (Fin 3 → ZMod 2))
    (hbker : b.ker = C₀.subgroupOf D) {x : A} (hx : x ∈ D) :
    natFaith_coord D b x = 0 ↔ x ∈ C₀ := by
  rw [natFaith_coord_of_mem b hx]
  have h1 : b ⟨x, hx⟩ = 1 ↔ (⟨x, hx⟩ : ↥D) ∈ b.ker := by rw [MonoidHom.mem_ker]
  rw [← toAdd_one, Multiplicative.toAdd.injective.eq_iff, h1, hbker, Subgroup.mem_subgroupOf]

theorem natFaith_eq_iff {B₀ C₀ : Subgroup A} (bc : A → (Fin 3 → ZMod 2))
    (hmul : ∀ x ∈ B₀, ∀ y ∈ B₀, bc (x * y) = bc x + bc y)
    (hker : ∀ x ∈ B₀, bc x = 0 ↔ x ∈ C₀) {x y : A} (hx : x ∈ B₀) (hy : y ∈ B₀) :
    bc x = bc y ↔ x * y⁻¹ ∈ C₀ := by
  have h1 : bc 1 = 0 := by
    have := hmul 1 B₀.one_mem 1 B₀.one_mem
    simpa using this
  have hinv : bc y⁻¹ = - bc y := by
    have := hmul y hy y⁻¹ (B₀.inv_mem hy)
    rw [mul_inv_cancel, h1] at this
    exact eq_neg_of_add_eq_zero_right this.symm
  rw [← hker _ (B₀.mul_mem hx (B₀.inv_mem hy)), hmul x hx y⁻¹ (B₀.inv_mem hy), hinv]
  exact add_neg_eq_zero.symm

theorem natFaith_conj_comm {X K Q W : Subgroup A} (hKX : K ≤ X)
    (hKnorm : X ≤ normalizer (K : Set A)) (hQnorm : X ≤ normalizer (Q : Set A))
    (hWcomm : ∀ w ∈ W, ∀ c ∈ K ⊓ Q, c * w = w * c)
    {o k u : A} (hoX : o ∈ X) (hoQ : o ∈ Q) (hkK : k ∈ K) (hw : k * u * k⁻¹ ∈ W) :
    o * (k * u * k⁻¹) * o⁻¹ = k * (o * u * o⁻¹) * k⁻¹ := by
  obtain ⟨c, hc⟩ : ∃ c : A, c = o⁻¹ * (k * o * k⁻¹) := ⟨_, rfl⟩
  have hcK : c ∈ K := by
    have h1 : o⁻¹ * k * o ∈ K := by
      have := (mem_normalizer_iff.1 (hKnorm (X.inv_mem hoX)) k).1 hkK
      simpa using this
    have h2 : c = (o⁻¹ * k * o) * k⁻¹ := by rw [hc]; group
    rw [h2]
    exact K.mul_mem h1 (K.inv_mem hkK)
  have hcQ : c ∈ Q := by
    have h1 : k * o * k⁻¹ ∈ Q := (mem_normalizer_iff.1 (hQnorm (hKX hkK)) o).1 hoQ
    rw [hc]
    exact Q.mul_mem (Q.inv_mem hoQ) h1
  have hcomm := hWcomm _ hw c ⟨hcK, hcQ⟩
  have hko : k * o * k⁻¹ = o * c := by rw [hc]; group
  have h1 : k * (o * u * o⁻¹) * k⁻¹ = (k * o * k⁻¹) * (k * u * k⁻¹) * (k * o * k⁻¹)⁻¹ := by group
  have h2 : c * (k * u * k⁻¹) * c⁻¹ = k * u * k⁻¹ := by rw [hcomm]; group
  rw [h1, hko]
  calc o * (k * u * k⁻¹) * o⁻¹ = o * (c * (k * u * k⁻¹) * c⁻¹) * o⁻¹ := by rw [h2]
    _ = o * c * (k * u * k⁻¹) * (o * c)⁻¹ := by group

theorem natFaith_trivial_action {X K B₀ C₀ W Q : Subgroup A} (hKX : K ≤ X)
    (hKnorm : X ≤ normalizer (K : Set A)) (hQnorm : X ≤ normalizer (Q : Set A))
    (hB₀X : X ≤ normalizer (B₀ : Set A)) (hC₀X : X ≤ normalizer (C₀ : Set A))
    (hB₀W : B₀ ≤ W) (hWcomm : ∀ w ∈ W, ∀ c ∈ K ⊓ Q, c * w = w * c)
    (a : ↥K →* GL32) (ha : Function.Surjective a) (bc : A → (Fin 3 → ZMod 2))
    (hmul : ∀ x ∈ B₀, ∀ y ∈ B₀, bc (x * y) = bc x + bc y)
    (hker : ∀ x ∈ B₀, bc x = 0 ↔ x ∈ C₀)
    (hsurj : ∀ v, ∃ u ∈ B₀, bc u = v)
    (hequiv : ∀ (k : ↥K), ∀ u ∈ B₀, bc ((k : A) * u * (k : A)⁻¹) =
      ((a k : GL32) : Matrix (Fin 3) (Fin 3) (ZMod 2)).mulVec (bc u))
    {o : A} (hoX : o ∈ X) (hoQ : o ∈ Q) :
    ∀ u ∈ B₀, bc (o * u * o⁻¹) = bc u := by
  classical
  choose u hu using hsurj
  have hconj : ∀ {z : A}, z ∈ X → ∀ x ∈ B₀, z * x * z⁻¹ ∈ B₀ := fun hz x hx =>
    (mem_normalizer_iff.1 (hB₀X hz) x).1 hx
  let φ : (Fin 3 → ZMod 2) → (Fin 3 → ZMod 2) := fun v => bc (o * u v * o⁻¹)
  have hφ : ∀ x ∈ B₀, φ (bc x) = bc (o * x * o⁻¹) := by
    intro x hx
    have h1 : bc (u (bc x)) = bc x := (hu _).2
    have h2 : u (bc x) * x⁻¹ ∈ C₀ := (natFaith_eq_iff bc hmul hker (hu _).1 hx).1 h1
    have h3 : o * (u (bc x) * x⁻¹) * o⁻¹ ∈ C₀ := (mem_normalizer_iff.1 (hC₀X hoX) _).1 h2
    have h4 : (o * u (bc x) * o⁻¹) * (o * x * o⁻¹)⁻¹ ∈ C₀ := by
      have : (o * u (bc x) * o⁻¹) * (o * x * o⁻¹)⁻¹ = o * (u (bc x) * x⁻¹) * o⁻¹ := by group
      rw [this]
      exact h3
    exact (natFaith_eq_iff bc hmul hker (hconj hoX _ (hu _).1) (hconj hoX x hx)).2 h4
  have hadd : ∀ x y, φ (x + y) = φ x + φ y := by
    intro x y
    have hx := hu x
    have hy := hu y
    have h1 : x + y = bc (u x * u y) := by rw [hmul _ hx.1 _ hy.1, hx.2, hy.2]
    have h2 : φ (x + y) = bc (o * (u x * u y) * o⁻¹) := by
      rw [h1, hφ _ (B₀.mul_mem hx.1 hy.1)]
    rw [h2]
    have h3 : o * (u x * u y) * o⁻¹ = (o * u x * o⁻¹) * (o * u y * o⁻¹) := by group
    rw [h3, hmul _ (hconj hoX _ hx.1) _ (hconj hoX _ hy.1)]
  have hinj : ∀ x, φ x = 0 → x = 0 := by
    intro x hx0
    have hx := hu x
    have h1 : o * u x * o⁻¹ ∈ C₀ := (hker _ (hconj hoX _ hx.1)).1 hx0
    have h2 : u x ∈ C₀ := by
      have := (mem_normalizer_iff.1 (hC₀X (X.inv_mem hoX)) _).1 h1
      simpa [mul_assoc] using this
    rw [← hx.2]
    exact (hker _ hx.1).2 h2
  have hcomm : ∀ (g : GL32) (v : Fin 3 → ZMod 2),
      φ (((g : GL32) : Matrix (Fin 3) (Fin 3) (ZMod 2)).mulVec v) =
        ((g : GL32) : Matrix (Fin 3) (Fin 3) (ZMod 2)).mulVec (φ v) := by
    intro g v
    obtain ⟨k, rfl⟩ := ha g
    have hv := hu v
    have hkX : (k : A) ∈ X := hKX k.2
    have hkB : (k : A) * u v * (k : A)⁻¹ ∈ B₀ := hconj hkX _ hv.1
    have e1 : ((a k : GL32) : Matrix (Fin 3) (Fin 3) (ZMod 2)).mulVec v =
        bc ((k : A) * u v * (k : A)⁻¹) := by rw [hequiv k _ hv.1, hv.2]
    have e2 : φ v = bc (o * u v * o⁻¹) := rfl
    rw [e1, hφ _ hkB, e2, ← hequiv k _ (hconj hoX _ hv.1)]
    congr 1
    exact natFaith_conj_comm hKX hKnorm hQnorm hWcomm hoX hoQ k.2 (hB₀W hkB)
  have hid := eq_id_of_commutes φ hadd hinj hcomm
  intro x hx
  rw [← hφ x hx]
  exact hid _

theorem natFaith_faithful {X K B₀ C₀ W Q : Subgroup A} (hKX : K ≤ X)
    (hKnorm : X ≤ normalizer (K : Set A)) (hQnorm : X ≤ normalizer (Q : Set A))
    (hQX : Q ≤ X)
    (hB₀X : X ≤ normalizer (B₀ : Set A)) (hC₀X : X ≤ normalizer (C₀ : Set A))
    (hB₀W : B₀ ≤ W) (hWcomm : ∀ w ∈ W, ∀ c ∈ K ⊓ Q, c * w = w * c)
    (hXKQ : ∀ g ∈ X, ∃ k ∈ K, ∃ o ∈ Q, g = k * o)
    (a : ↥K →* GL32) (ha : Function.Surjective a)
    (ha1 : ∀ k : ↥K, a k = 1 → (k : A) ∈ Q)
    (bc : A → (Fin 3 → ZMod 2))
    (hmul : ∀ x ∈ B₀, ∀ y ∈ B₀, bc (x * y) = bc x + bc y)
    (hker : ∀ x ∈ B₀, bc x = 0 ↔ x ∈ C₀)
    (hsurj : ∀ v, ∃ u ∈ B₀, bc u = v)
    (hequiv : ∀ (k : ↥K), ∀ u ∈ B₀, bc ((k : A) * u * (k : A)⁻¹) =
      ((a k : GL32) : Matrix (Fin 3) (Fin 3) (ZMod 2)).mulVec (bc u)) :
    ∀ g ∈ X, (∀ u ∈ B₀, g * u * g⁻¹ * u⁻¹ ∈ B₀ ⊓ C₀) → g ∈ Q := by
  intro g hgX hg
  obtain ⟨k, hkK, o, hoQ, rfl⟩ := hXKQ g hgX
  have hoX : o ∈ X := hQX hoQ
  have htriv := natFaith_trivial_action hKX hKnorm hQnorm hB₀X hC₀X hB₀W hWcomm a ha bc hmul hker
    hsurj hequiv hoX hoQ
  have hfix : ∀ v : Fin 3 → ZMod 2,
      ((a ⟨k, hkK⟩ : GL32) : Matrix (Fin 3) (Fin 3) (ZMod 2)).mulVec v = v := by
    intro v
    obtain ⟨u, hu, rfl⟩ := hsurj v
    have hconj : ∀ {z : A}, z ∈ X → ∀ x ∈ B₀, z * x * z⁻¹ ∈ B₀ := fun hz x hx =>
      (mem_normalizer_iff.1 (hB₀X hz) x).1 hx
    have h1 : (k * o) * u * (k * o)⁻¹ ∈ B₀ := hconj hgX u hu
    have h2 : bc ((k * o) * u * (k * o)⁻¹) = bc u := by
      rw [natFaith_eq_iff bc hmul hker h1 hu]
      have := (hg u hu).2
      simpa [mul_assoc] using this
    have h3 : (k * o) * u * (k * o)⁻¹ = k * (o * u * o⁻¹) * k⁻¹ := by group
    rw [h3] at h2
    calc ((a ⟨k, hkK⟩ : GL32) : Matrix (Fin 3) (Fin 3) (ZMod 2)).mulVec (bc u)
        = ((a ⟨k, hkK⟩ : GL32) : Matrix (Fin 3) (Fin 3) (ZMod 2)).mulVec
          (bc (o * u * o⁻¹)) := by rw [htriv u hu]
      _ = bc (k * (o * u * o⁻¹) * k⁻¹) := (hequiv ⟨k, hkK⟩ _ (hconj hoX u hu)).symm
      _ = bc u := h2
  have hone := eq_one_of_fixes_all hfix
  exact Q.mul_mem (ha1 ⟨k, hkK⟩ hone) hoQ

theorem CampbellHyp.faithful_of_hasNatSection (h : CampbellHyp X K R P) {D C₀ : Subgroup A}
    (hZD : CFSG.Quasithin.centerOf (CFSG.Quasithin.c134Q X K) ≤ D)
    (hC₀K : K ≤ centralizer (C₀ : Set A)) (hC₀X : X ≤ normalizer (C₀ : Set A))
    (hN : HasNatSection K D C₀) :
    ∀ g ∈ X, (∀ u ∈ ⁅omegaCenter (K ⊓ pCoreOf 2 X), K⁆,
      g * u * g⁻¹ * u⁻¹ ∈ ⁅omegaCenter (K ⊓ pCoreOf 2 X), K⁆ ⊓ C₀) → g ∈ pCoreOf 2 X := by
  obtain ⟨a, b, ha, hker, hbker, hequiv, hB₀D, hbB₀⟩ := h.natData_B0 hZD hC₀K hN
  refine natFaith_faithful h.K_le h.K_normal (normalizer_pCoreOf X) (pCoreOf_le_self X)
    h.normalizer_B0 hC₀X h.commutator_W_le ?_ (fun g hg => h.mem_X_iff.1 hg) a ha ?_
    (natFaith_coord D b) ?_ ?_ ?_ ?_
  · intro w hw c hc
    exact ((mem_omegaCenter.1 hw).2.1 c hc).symm
  · intro k hk
    have : k ∈ a.ker := hk
    rw [hker, h.pCore_K_eq] at this
    exact this
  · intro x hx y hy
    exact natFaith_coord_mul b (hB₀D hx) (hB₀D hy)
  · intro x hx
    exact natFaith_coord_eq_zero_iff b hbker (hB₀D hx)
  · intro v
    obtain ⟨u, hu, hv⟩ := hbB₀ v
    exact ⟨u, hu, by rw [natFaith_coord_of_mem b u.2]; exact hv⟩
  · intro k u hu
    have hv : (k : A) * u * (k : A)⁻¹ ∈ ⁅omegaCenter (K ⊓ pCoreOf 2 X), K⁆ :=
      (mem_normalizer_iff.1 (h.normalizer_B0 (h.K_le k.2)) u).1 hu
    rw [natFaith_coord_of_mem b (hB₀D hv), natFaith_coord_of_mem b (hB₀D hu)]
    exact hequiv k ⟨u, hB₀D hu⟩ ⟨_, hB₀D hv⟩ rfl
end

section
open CFSG.Open Subgroup CFSG.QuasithinUnique.Setup.Family
variable {A : Type} [Group A] [Finite A] {X K R P : Subgroup A}

theorem CampbellHyp.conclusion_of_hasNatSection (h : CampbellHyp X K R P) {D C₀ : Subgroup A}
    (hZD : CFSG.Quasithin.centerOf (CFSG.Quasithin.c134Q X K) ≤ D)
    (hC₀K : K ≤ centralizer (C₀ : Set A)) (hC₀X : X ≤ normalizer (C₀ : Set A))
    (hN : HasNatSection K D C₀) : CampbellConclusion X K := by
  refine ⟨⁅omegaCenter (K ⊓ pCoreOf 2 X), K⁆ ⊓ C₀, ⁅omegaCenter (K ⊓ pCoreOf 2 X), K⁆,
    inf_le_left, h.commutator_W_le, normalizer_inf_of_normalizes h.normalizer_B0 hC₀X,
    h.normalizer_B0, ?_, fun w hw k hk => Subgroup.commutator_mem_commutator hw hk,
    h.relIndex_eight_of_hasNatSection hZD hC₀K hN,
    h.faithful_of_hasNatSection hZD hC₀K hC₀X hN⟩
  intro k hk
  rw [Subgroup.mem_centralizer_iff]
  intro a ha
  exact (Subgroup.mem_centralizer_iff.1 (hC₀K hk)) a ha.2
end

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Campbell
