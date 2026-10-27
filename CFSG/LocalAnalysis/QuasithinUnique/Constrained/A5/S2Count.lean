module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.AppCOffender
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.S2Basic
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.S2Fin

public section

namespace CFSG.QuasithinUnique.A5.S2

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.QuasithinUnique.DoubleA3
  CFSG.QuasithinUnique.A5.Delta5 CFSG.QuasithinUnique.AppC Equiv
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {T M H S L : Subgroup G}

omit [Finite G] in
theorem unique3 {X Y Z : Subgroup G} (h1 : X ⊓ Y = ⊥) (h2 : Z ⊓ (X ⊔ Y) = ⊥) {x x' y y' z z' : G}
    (hx : x ∈ X) (hx' : x' ∈ X) (hy : y ∈ Y) (hy' : y' ∈ Y) (hz : z ∈ Z) (hz' : z' ∈ Z)
    (e : x * y * z = x' * y' * z') : x = x' ∧ y = y' ∧ z = z' := by
  have hxy : x * y ∈ X ⊔ Y := Subgroup.mul_mem_sup hx hy
  have hxy' : x' * y' ∈ X ⊔ Y := Subgroup.mul_mem_sup hx' hy'
  have hzz : (x' * y')⁻¹ * (x * y) = z' * z⁻¹ :=
    calc (x' * y')⁻¹ * (x * y) = (x' * y')⁻¹ * (x * y * z) * z⁻¹ := by group
      _ = (x' * y')⁻¹ * (x' * y' * z') * z⁻¹ := by rw [e]
      _ = z' * z⁻¹ := by group
  have h3 : z' * z⁻¹ ∈ Z ⊓ (X ⊔ Y) :=
    ⟨Z.mul_mem hz' (Z.inv_mem hz), hzz ▸ (X ⊔ Y).mul_mem ((X ⊔ Y).inv_mem hxy') hxy⟩
  rw [h2, Subgroup.mem_bot] at h3
  have hzeq : z = z' := by
    have : z' = z := by simpa [mul_inv_eq_one] using h3
    exact this.symm
  subst hzeq
  have hxy_eq : x * y = x' * y' := mul_right_cancel e
  have h4 : x'⁻¹ * x ∈ X ⊓ Y := by
    refine ⟨X.mul_mem (X.inv_mem hx') hx, ?_⟩
    have : x'⁻¹ * x = y' * y⁻¹ := by
      calc x'⁻¹ * x = x'⁻¹ * (x * y) * y⁻¹ := by group
        _ = x'⁻¹ * (x' * y') * y⁻¹ := by rw [hxy_eq]
        _ = y' * y⁻¹ := by group
    rw [this]
    exact Y.mul_mem hy' (Y.inv_mem hy)
  rw [h1, Subgroup.mem_bot] at h4
  have hxeq : x = x' := by
    have : x' = x := by simpa [inv_mul_eq_one] using h4
    exact this.symm
  subst hxeq
  exact ⟨rfl, mul_left_cancel hxy_eq, rfl⟩

theorem card_sup_le_of_commute {X Y : Subgroup G} (h : ∀ a ∈ X, ∀ b ∈ Y, a * b = b * a) :
    Nat.card ↥(X ⊔ Y) ≤ Nat.card X * Nat.card Y := by
  have h1 := B2F.card_sup_mul_card_inf_of_commute h
  have hpos : 0 < Nat.card ↥(X ⊓ Y) := Nat.card_pos
  calc Nat.card ↥(X ⊔ Y) = Nat.card ↥(X ⊔ Y) * 1 := (mul_one _).symm
    _ ≤ Nat.card ↥(X ⊔ Y) * Nat.card ↥(X ⊓ Y) := Nat.mul_le_mul_left _ hpos
    _ = Nat.card X * Nat.card Y := h1

theorem exact_offender {L' A : Subgroup G} (P : A5Pi L') (hE : P.im (baum S) = Estd)
    (hU : IsElemAbelian 2 (blockU L')) (hUS : blockU L' ≤ S)
    (hAN : A ≤ Subgroup.normalizer (L' : Set G)) (hAR : A ≤ baum S)
    (hA : IsMaxElemAbelian S A) :
    Nat.card (P.im A) * Nat.card ↥(blockU L' ⊓ Subgroup.centralizer (A : Set G)) = 16 := by
  have hUN : blockU L' ≤ Subgroup.normalizer (L' : Set G) :=
    (C1GN.blockU_le_self L').trans Subgroup.le_normalizer
  have hA' : IsMaxElemAbelian (S ⊓ Subgroup.normalizer (L' : Set G)) A :=
    ⟨le_inf hA.1 hAN, hA.2.1, fun B hB hBe => hA.2.2 B (hB.trans inf_le_left) hBe⟩
  have hff := P.toPiData.ff_ineq hU (le_inf hUS hUN) inf_le_right hA'
  have hle : P.im A ≤ Estd := hE ▸ P.im_mono hAR
  have h16 := card_mul_fix_eq_of_le_Estd _ hle hff
  rw [P.card_fix hAN]
  exact h16

namespace Data

variable {t : G} (h : Data T M H S L t)
include h

omit [Finite G] h in
theorem blockU₂ : blockU (cj t L) = cj t (blockU L) :=
  Lin2.blockU_map_equiv (MulAut.conj t) L

omit [Finite G] h in
theorem U₁_le_L : blockU L ≤ L := C1GN.blockU_le_self L

omit [Finite G] h in
theorem U₂_le_L₂ : blockU (cj t L) ≤ cj t L := C1GN.blockU_le_self _

theorem comm_U : ∀ u ∈ blockU L, ∀ v ∈ blockU (cj t L), u * v = v * u := fun u hu v hv =>
  h.comm_elem u (U₁_le_L hu) v (U₂_le_L₂ hv)

theorem blockU0_eq : blockU0 S L = blockU L ⊔ blockU (cj t L) := by
  apply le_antisymm
  · refine iSup_le fun s => ?_
    show cj (s : G) (blockU L) ≤ _
    have e : cj (s : G) (blockU L) = blockU (cj (s : G) L) :=
      (Lin2.blockU_map_equiv (MulAut.conj (s : G)) L).symm
    rcases h.conj_cases s.2 with h1 | h1
    · rw [e, h1]; exact le_sup_left
    · rw [e, h1]; exact le_sup_right
  · refine sup_le (C56.le_conjJoin (blockU L) (one_mem S)) ?_
    rw [blockU₂]
    exact le_iSup (fun s : S => (blockU L).map (MulAut.conj (s : G)).toMonoidHom) ⟨t, h.t_mem⟩

theorem U₁_inf_U₂ : blockU L ⊓ blockU (cj t L) = ⊥ := by
  rw [eq_bot_iff]
  rintro u ⟨hu1, hu2⟩
  have hZ : u ∈ blockZ L := ⟨hu1, Subgroup.mem_centralizer_iff.2 fun ℓ hℓ =>
    h.comm_elem ℓ hℓ u (U₂_le_L₂ hu2)⟩
  rw [AppC.blockZ_eq_bot_of_alt5 h.isShort h.alt5] at hZ
  exact hZ

theorem D₀_inf : baumD S L ⊓ (blockU L ⊔ blockU (cj t L)) = ⊥ := by
  rw [eq_bot_iff]
  rintro d ⟨hd, hd12⟩
  have hdc : ∀ x ∈ conjJoin S L, x * d = d * x := fun x hx =>
    Subgroup.mem_centralizer_iff.1 hd.2 x hx
  have hU₂N : blockU (cj t L) ≤ Subgroup.normalizer (blockU L : Set G) :=
    C5.le_normalizer_of_commute fun u hu v hv => (h.comm_U v hv u hu).symm
  obtain ⟨u₁, hu₁, u₂, hu₂, rfl⟩ := (Lin2.mem_sup_iff_of_le_normalizer hU₂N).1 hd12
  have hL₀₁ : u₁ ∈ conjJoin S L := h.L_le_L₀ (U₁_le_L hu₁)
  have hL₀₂ : u₂ ∈ conjJoin S L := h.L₂_le_L₀ (U₂_le_L₂ hu₂)
  have hu₁Z : u₁ ∈ blockZ L := by
    refine ⟨hu₁, Subgroup.mem_centralizer_iff.2 fun ℓ hℓ => ?_⟩
    have h1 := hdc ℓ (h.L_le_L₀ hℓ)
    have h2 := h.comm_elem ℓ hℓ u₂ (U₂_le_L₂ hu₂)
    have : ℓ * u₁ * u₂ = u₁ * ℓ * u₂ := by
      calc ℓ * u₁ * u₂ = ℓ * (u₁ * u₂) := by group
        _ = (u₁ * u₂) * ℓ := h1
        _ = u₁ * (u₂ * ℓ) := by group
        _ = u₁ * (ℓ * u₂) := by rw [h2]
        _ = u₁ * ℓ * u₂ := by group
    exact mul_right_cancel this
  have hu₁1 : u₁ = 1 := by
    have := hu₁Z
    rw [AppC.blockZ_eq_bot_of_alt5 h.isShort h.alt5] at this
    exact Subgroup.mem_bot.1 this
  have hu₂Z : u₂ ∈ blockZ (cj t L) := by
    refine ⟨hu₂, Subgroup.mem_centralizer_iff.2 fun ℓ hℓ => ?_⟩
    have h1 := hdc ℓ (h.L₂_le_L₀ hℓ)
    rw [hu₁1, one_mul] at h1
    exact h1
  have hu₂1 : u₂ = 1 := by
    have := hu₂Z
    rw [AppC.blockZ_eq_bot_of_alt5 h.isShort₂ h.alt5₂] at this
    exact Subgroup.mem_bot.1 this
  rw [hu₁1, hu₂1, one_mul]
  exact Subgroup.one_mem _

theorem U₁_U₂_le_L₀ : blockU L ⊔ blockU (cj t L) ≤ conjJoin S L := by
  rw [h.join]
  exact sup_le_sup U₁_le_L U₂_le_L₂

theorem D₀_comm {a b : G} (ha : a ∈ baumD S L) (hb : b ∈ blockU L ⊔ blockU (cj t L)) :
    a * b = b * a :=
  (Subgroup.mem_centralizer_iff.1 ha.2 b (h.U₁_U₂_le_L₀ hb)).symm

theorem card_Q (P₁ : A5Pi L) (P₂ : A5Pi (cj t L)) :
    Nat.card ↥(baumD S L ⊔ (blockU L ⊔ blockU (cj t L))) = Nat.card ↥(baumD S L) * 256 := by
  have hU12 : Nat.card ↥(blockU L ⊔ blockU (cj t L)) = 256 := by
    have h1 := B2F.card_sup_mul_card_inf_of_commute h.comm_U
    rw [h.U₁_inf_U₂, Subgroup.card_bot, mul_one, P₁.toPiData.card_blockU,
      P₂.toPiData.card_blockU] at h1
    omega
  have h2 := B2F.card_sup_mul_card_inf_of_commute (fun a ha b hb => h.D₀_comm ha hb)
  rw [h.D₀_inf, Subgroup.card_bot, mul_one, hU12] at h2
  exact h2

theorem A_le_sup_Q (P₁ : A5Pi L) (P₂ : A5Pi (cj t L))
    (hE₁ : P₁.im (baum S) = Estd) (hE₂ : P₂.im (baum S) = Estd)
    (hRN₁ : baum S ≤ Subgroup.normalizer (L : Set G))
    (hRN₂ : baum S ≤ Subgroup.normalizer (cj t L : Set G))
    (hU₁R : blockU L ≤ baum S) (hU₂R : blockU (cj t L) ≤ baum S)
    (hQ₁ : s2Q1 S L = baum S ⊓ Subgroup.centralizer (blockU L : Set G))
    (hQ₂ : s2Q1 S (cj t L) = baum S ⊓ Subgroup.centralizer (blockU (cj t L) : Set G))
    (hP : pCoreOf 2 H = baumD S L ⊔ blockU0 S L) (hmaxQ : IsMaxElemAbelian S (pCoreOf 2 H))
    (hQQ : s2Q1 S L ⊓ s2Q1 S (cj t L) ≤ pCoreOf 2 H)
    {A : Subgroup G} (hA : IsMaxElemAbelian S A) (hAR : A ≤ baum S) :
    A ≤ s2Q1 S L ⊔ s2Q1 S (cj t L) := by
  classical
  have hQeq : pCoreOf 2 H = baumD S L ⊔ (blockU L ⊔ blockU (cj t L)) := by
    rw [hP, h.blockU0_eq]
  have hAN₁ : A ≤ Subgroup.normalizer (L : Set G) := hAR.trans hRN₁
  have hAN₂ : A ≤ Subgroup.normalizer (cj t L : Set G) := hAR.trans hRN₂
  have hUS₁ : blockU L ≤ S := hU₁R.trans (C1GN.baum_le S)
  have hUS₂ : blockU (cj t L) ≤ S := hU₂R.trans (C1GN.baum_le S)
  have ex₁ := exact_offender P₁ hE₁ (AppC.isElemAbelian_blockU h.isShort) hUS₁ hAN₁ hAR hA
  have ex₂ := exact_offender P₂ hE₂ (AppC.isElemAbelian_blockU h.isShort₂) hUS₂ hAN₂ hAR hA
  have hcard₁ := P₁.toPiData.card_im_mul hAN₁
  have hcard₂ := P₂.toPiData.card_im_mul hAN₂
  have hAC₁ : A ⊓ Subgroup.centralizer (blockU L : Set G) = A ⊓ s2Q1 S L := by
    rw [hQ₁, ← inf_assoc, inf_eq_left.2 hAR]
  have hAC₂ : A ⊓ Subgroup.centralizer (blockU (cj t L) : Set G) = A ⊓ s2Q1 S (cj t L) := by
    rw [hQ₂, ← inf_assoc, inf_eq_left.2 hAR]
  rw [hAC₁] at hcard₁
  rw [hAC₂] at hcard₂
  have hAQ : Nat.card A = Nat.card ↥(pCoreOf 2 H) :=
    le_antisymm (hmaxQ.2.2 A hA.1 hA.2.1) (hA.2.2 _ hmaxQ.1 hmaxQ.2.1)
  have hcQ := h.card_Q P₁ P₂
  rw [← hQeq] at hcQ
  have hU₂N : blockU (cj t L) ≤ Subgroup.normalizer (blockU L : Set G) :=
    C5.le_normalizer_of_commute fun u hu v hv => (h.comm_U v hv u hu).symm
  have hU12N : blockU L ⊔ blockU (cj t L) ≤ Subgroup.normalizer (baumD S L : Set G) :=
    C5.le_normalizer_of_commute fun u hu a ha => (h.D₀_comm ha hu).symm
  have hRN₀ : baum S ≤ Subgroup.normalizer (conjJoin S L : Set G) := by
    rw [h.join]
    exact fun a ha => C1.mem_normalizer_sup (hRN₁ ha) (hRN₂ ha)
  have hAbel : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a := fun a ha b hb =>
    B2F.isElemAbelian_comm hA.2.1 ha hb
  have hinfQ : A ⊓ pCoreOf 2 H ≤
      ((blockU L ⊓ Subgroup.centralizer (A : Set G)) ⊔
        (blockU (cj t L) ⊓ Subgroup.centralizer (A : Set G))) ⊔ baumD S L := by
    rintro q ⟨hqA, hqQ⟩
    rw [hQeq] at hqQ
    obtain ⟨d, hd, w, hw, hqdw⟩ := (Lin2.mem_sup_iff_of_le_normalizer hU12N).1 hqQ
    obtain ⟨u₁, hu₁, u₂, hu₂, rfl⟩ := (Lin2.mem_sup_iff_of_le_normalizer hU₂N).1 hw
    have hq : q = u₁ * u₂ * d := by
      rw [hqdw]
      exact h.D₀_comm hd (Subgroup.mul_mem_sup hu₁ hu₂)
    have hcen : ∀ a ∈ A, a * u₁ = u₁ * a ∧ a * u₂ = u₂ * a := by
      intro a ha
      have haR : a ∈ baum S := hAR ha
      have e1 : a * u₁ * a⁻¹ ∈ blockU L :=
        (Subgroup.mem_normalizer_iff.1 (C1.mem_normalizer_blockU (hRN₁ haR)) u₁).1 hu₁
      have e2 : a * u₂ * a⁻¹ ∈ blockU (cj t L) :=
        (Subgroup.mem_normalizer_iff.1 (C1.mem_normalizer_blockU (hRN₂ haR)) u₂).1 hu₂
      have e3 : a * d * a⁻¹ ∈ baumD S L := by
        refine ⟨(baum S).mul_mem ((baum S).mul_mem haR hd.1) ((baum S).inv_mem haR),
          Subgroup.mem_centralizer_iff.2 fun x hx => ?_⟩
        have hx' : a⁻¹ * x * a ∈ conjJoin S L := by
          have := (Subgroup.mem_normalizer_iff.1 (hRN₀ ((baum S).inv_mem haR)) x).1 hx
          simpa using this
        have hc := Subgroup.mem_centralizer_iff.1 hd.2 _ hx'
        calc x * (a * d * a⁻¹) = a * ((a⁻¹ * x * a) * d) * a⁻¹ := by group
          _ = a * (d * (a⁻¹ * x * a)) * a⁻¹ := by rw [hc]
          _ = (a * d * a⁻¹) * x := by group
      have hq' : a * q * a⁻¹ = q := by
        have := hAbel a ha q hqA
        calc a * q * a⁻¹ = (q * a) * a⁻¹ := by rw [this]
          _ = q := by group
      have hdec : (a * u₁ * a⁻¹) * (a * u₂ * a⁻¹) * (a * d * a⁻¹) = u₁ * u₂ * d := by
        calc (a * u₁ * a⁻¹) * (a * u₂ * a⁻¹) * (a * d * a⁻¹) = a * (u₁ * u₂ * d) * a⁻¹ := by group
          _ = a * q * a⁻¹ := by rw [← hq]
          _ = q := hq'
          _ = u₁ * u₂ * d := hq
      obtain ⟨r1, r2, -⟩ := unique3 h.U₁_inf_U₂ h.D₀_inf e1 hu₁ e2 hu₂ e3 hd hdec
      refine ⟨?_, ?_⟩
      · calc a * u₁ = (a * u₁ * a⁻¹) * a := by group
          _ = u₁ * a := by rw [r1]
      · calc a * u₂ = (a * u₂ * a⁻¹) * a := by group
          _ = u₂ * a := by rw [r2]
    rw [hq]
    refine Subgroup.mul_mem_sup (Subgroup.mul_mem_sup ?_ ?_) hd
    · exact ⟨hu₁, Subgroup.mem_centralizer_iff.2 fun a ha => (hcen a ha).1⟩
    · exact ⟨hu₂, Subgroup.mem_centralizer_iff.2 fun a ha => (hcen a ha).2⟩
  have hJ : Nat.card ↥(((blockU L ⊓ Subgroup.centralizer (A : Set G)) ⊔
        (blockU (cj t L) ⊓ Subgroup.centralizer (A : Set G))) ⊔ baumD S L) ≤
      Nat.card ↥(blockU L ⊓ Subgroup.centralizer (A : Set G)) *
        Nat.card ↥(blockU (cj t L) ⊓ Subgroup.centralizer (A : Set G)) *
        Nat.card ↥(baumD S L) := by
    have h1 : Nat.card ↥((blockU L ⊓ Subgroup.centralizer (A : Set G)) ⊔
        (blockU (cj t L) ⊓ Subgroup.centralizer (A : Set G))) ≤
        Nat.card ↥(blockU L ⊓ Subgroup.centralizer (A : Set G)) *
          Nat.card ↥(blockU (cj t L) ⊓ Subgroup.centralizer (A : Set G)) :=
      card_sup_le_of_commute fun a ha b hb => h.comm_U a ha.1 b hb.1
    have hCC : (blockU L ⊓ Subgroup.centralizer (A : Set G)) ⊔
        (blockU (cj t L) ⊓ Subgroup.centralizer (A : Set G)) ≤ blockU L ⊔ blockU (cj t L) :=
      sup_le_sup inf_le_left inf_le_left
    have h2 := card_sup_le_of_commute (X := (blockU L ⊓ Subgroup.centralizer (A : Set G)) ⊔
        (blockU (cj t L) ⊓ Subgroup.centralizer (A : Set G))) (Y := baumD S L)
      fun a ha b hb => (h.D₀_comm hb (hCC ha)).symm
    exact h2.trans (Nat.mul_le_mul_right _ h1)
  have hcomm12 : ∀ a ∈ A ⊓ s2Q1 S L, ∀ b ∈ A ⊓ s2Q1 S (cj t L), a * b = b * a :=
    fun a ha b hb => hAbel a ha.1 b hb.1
  have h12 := B2F.card_sup_mul_card_inf_of_commute hcomm12
  have hsub : (A ⊓ s2Q1 S L) ⊓ (A ⊓ s2Q1 S (cj t L)) ≤
      ((blockU L ⊓ Subgroup.centralizer (A : Set G)) ⊔
        (blockU (cj t L) ⊓ Subgroup.centralizer (A : Set G))) ⊔ baumD S L :=
    fun x hx => hinfQ ⟨hx.1.1, hQQ ⟨hx.1.2, hx.2.2⟩⟩
  have hY : Nat.card ↥((A ⊓ s2Q1 S L) ⊓ (A ⊓ s2Q1 S (cj t L))) ≤
      Nat.card ↥(blockU L ⊓ Subgroup.centralizer (A : Set G)) *
        Nat.card ↥(blockU (cj t L) ⊓ Subgroup.centralizer (A : Set G)) *
        Nat.card ↥(baumD S L) :=
    (Subgroup.card_le_of_le hsub).trans hJ
  have hapos : 0 < Nat.card A := Nat.card_pos
  have E5 : Nat.card A = 256 * Nat.card ↥(baumD S L) := by rw [hAQ, hcQ]; ring
  have hc1 : Nat.card (P₁.im A) * Nat.card ↥(blockU L ⊓ Subgroup.centralizer (A : Set G)) = 16 :=
    ex₁
  have hc2 : Nat.card (P₂.im A) *
      Nat.card ↥(blockU (cj t L) ⊓ Subgroup.centralizer (A : Set G)) = 16 := ex₂
  have hh1 : Nat.card (P₁.im A) * Nat.card ↥(blockU L ⊓ Subgroup.centralizer (A : Set G)) *
      (Nat.card (P₂.im A) * Nat.card ↥(blockU (cj t L) ⊓ Subgroup.centralizer (A : Set G))) =
      256 := by rw [hc1, hc2]
  have hbound : Nat.card (P₁.im A) * Nat.card (P₂.im A) *
      Nat.card ↥((A ⊓ s2Q1 S L) ⊓ (A ⊓ s2Q1 S (cj t L))) ≤ Nat.card A := by
    calc Nat.card (P₁.im A) * Nat.card (P₂.im A) *
        Nat.card ↥((A ⊓ s2Q1 S L) ⊓ (A ⊓ s2Q1 S (cj t L))) ≤
        Nat.card (P₁.im A) * Nat.card (P₂.im A) *
          (Nat.card ↥(blockU L ⊓ Subgroup.centralizer (A : Set G)) *
            Nat.card ↥(blockU (cj t L) ⊓ Subgroup.centralizer (A : Set G)) *
            Nat.card ↥(baumD S L)) := Nat.mul_le_mul_left _ hY
      _ = (Nat.card (P₁.im A) * Nat.card ↥(blockU L ⊓ Subgroup.centralizer (A : Set G)) *
          (Nat.card (P₂.im A) *
            Nat.card ↥(blockU (cj t L) ⊓ Subgroup.centralizer (A : Set G)))) *
          Nat.card ↥(baumD S L) := by ring
      _ = Nat.card A := by rw [hh1, E5]
  have hsq : Nat.card A * Nat.card A =
      Nat.card ↥((A ⊓ s2Q1 S L) ⊔ (A ⊓ s2Q1 S (cj t L))) *
        (Nat.card (P₁.im A) * Nat.card (P₂.im A) *
          Nat.card ↥((A ⊓ s2Q1 S L) ⊓ (A ⊓ s2Q1 S (cj t L)))) := by
    calc Nat.card A * Nat.card A =
        (Nat.card (P₁.im A) * Nat.card ↥(A ⊓ s2Q1 S L)) *
          (Nat.card (P₂.im A) * Nat.card ↥(A ⊓ s2Q1 S (cj t L))) := by rw [hcard₁, hcard₂]
      _ = Nat.card (P₁.im A) * Nat.card (P₂.im A) *
          (Nat.card ↥(A ⊓ s2Q1 S L) * Nat.card ↥(A ⊓ s2Q1 S (cj t L))) := by ring
      _ = Nat.card (P₁.im A) * Nat.card (P₂.im A) *
          (Nat.card ↥((A ⊓ s2Q1 S L) ⊔ (A ⊓ s2Q1 S (cj t L))) *
            Nat.card ↥((A ⊓ s2Q1 S L) ⊓ (A ⊓ s2Q1 S (cj t L)))) := by rw [h12]
      _ = _ := by ring
  have hXge : Nat.card A ≤ Nat.card ↥((A ⊓ s2Q1 S L) ⊔ (A ⊓ s2Q1 S (cj t L))) := by
    have h3 : Nat.card A * Nat.card A ≤
        Nat.card ↥((A ⊓ s2Q1 S L) ⊔ (A ⊓ s2Q1 S (cj t L))) * Nat.card A := by
      rw [hsq]
      exact Nat.mul_le_mul_left _ hbound
    exact Nat.le_of_mul_le_mul_right h3 hapos
  have hle : (A ⊓ s2Q1 S L) ⊔ (A ⊓ s2Q1 S (cj t L)) ≤ A := sup_le inf_le_left inf_le_left
  have heq := Subgroup.eq_of_le_of_card_ge hle hXge
  calc A = (A ⊓ s2Q1 S L) ⊔ (A ⊓ s2Q1 S (cj t L)) := heq.symm
    _ ≤ s2Q1 S L ⊔ s2Q1 S (cj t L) := sup_le_sup inf_le_right inf_le_right

end Data

end CFSG.QuasithinUnique.A5.S2
