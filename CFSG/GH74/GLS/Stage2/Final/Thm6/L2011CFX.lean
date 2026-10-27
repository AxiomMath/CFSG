module

public import CFSG.LieType.CurtisTits.Conclusion
public import CFSG.GH74.GLS.IVK.Proofs2.Stmt413

public section

namespace CFSG.GH74.GLS.Stage2.Final.Thm6.L2011.CFT

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS.IVK CFSG.GH74.GLS.IVK.Proofs2
open scoped commutatorElement

section Inn

variable {K : Type} [Group K]

theorem conj_normal' (f : MulAut K) (g : K) : f * MulAut.conj g * f⁻¹ = MulAut.conj (f g) := by
  ext h
  simp [MulAut.conj_apply, MulAut.mul_apply]

theorem conj_injective_of_center (hZ : ∀ k : K, (∀ g : K, g * k = k * g) → k = 1) :
    Function.Injective (MulAut.conj : K →* MulAut K) := by
  intro a b hab
  have h : ∀ g : K, a * g * a⁻¹ = b * g * b⁻¹ := fun g => by
    have := congrArg (fun f : MulAut K => f g) hab
    simpa [MulAut.conj_apply] using this
  have hc : b⁻¹ * a = 1 := by
    apply hZ
    intro g
    have h1 := h g
    calc g * (b⁻¹ * a) = b⁻¹ * (b * g * b⁻¹) * a := by group
      _ = b⁻¹ * (a * g * a⁻¹) * a := by rw [h1]
      _ = (b⁻¹ * a) * g := by group
  exact (inv_mul_eq_one.1 hc).symm

variable (X : Subgroup (MulAut K)) (hX : ∀ k : K, MulAut.conj k ∈ X)

@[expose] def innIn : K →* ↥X := (MulAut.conj : K →* MulAut K).codRestrict X hX

@[simp] theorem coe_innIn (k : K) : ((innIn X hX k : ↥X) : MulAut K) = MulAut.conj k := rfl

theorem innIn_injective (hZ : ∀ k : K, (∀ g : K, g * k = k * g) → k = 1) :
    Function.Injective (innIn X hX) := by
  intro a b hab
  exact conj_injective_of_center hZ (congrArg Subtype.val hab)

@[expose] def innRange : Subgroup ↥X := (innIn X hX).range

theorem innIn_mem_innRange (k : K) : innIn X hX k ∈ innRange X hX := ⟨k, rfl⟩

theorem innRange_normal : (innRange X hX).Normal := by
  refine ⟨fun n hn g => ?_⟩
  obtain ⟨k, rfl⟩ := hn
  refine ⟨(g : MulAut K) k, ?_⟩
  apply Subtype.ext
  simp only [coe_innIn, Subgroup.coe_mul, Subgroup.coe_inv]
  exact (conj_normal' (g : MulAut K) k).symm

theorem centralizer_innRange_eq_bot (hZ : ∀ k : K, (∀ g : K, g * k = k * g) → k = 1) :
    centralizer ((innRange X hX : Subgroup ↥X) : Set ↥X) = ⊥ := by
  rw [eq_bot_iff]
  intro γ hγ
  rw [Subgroup.mem_bot]
  apply Subtype.ext
  ext k
  have hc := Subgroup.mem_centralizer_iff.1 hγ (innIn X hX k) (innIn_mem_innRange X hX k)
  have h1 : MulAut.conj k * (γ : MulAut K) = (γ : MulAut K) * MulAut.conj k := congrArg Subtype.val hc
  have h2 : MulAut.conj ((γ : MulAut K) k) = MulAut.conj k := by
    rw [← conj_normal', ← h1]; group
  have := conj_injective_of_center hZ h2
  simpa using this

theorem mem_centralizer_innIn (hZ : ∀ k : K, (∀ g : K, g * k = k * g) → k = 1) (x : K) (γ : ↥X) :
    γ ∈ centralizer ({innIn X hX x} : Set ↥X) ↔ (γ : MulAut K) x = x := by
  rw [Subgroup.mem_centralizer_singleton_iff]
  constructor
  · intro h
    have h1 : (γ : MulAut K) * MulAut.conj x = MulAut.conj x * (γ : MulAut K) := congrArg Subtype.val h
    have h2 : MulAut.conj ((γ : MulAut K) x) = MulAut.conj x := by
      rw [← conj_normal', h1]; group
    exact conj_injective_of_center hZ h2
  · intro h
    apply Subtype.ext
    have h2 : (γ : MulAut K) * MulAut.conj x * (γ : MulAut K)⁻¹ = MulAut.conj x := by
      rw [conj_normal', h]
    simp only [coe_innIn, Subgroup.coe_mul]
    calc (γ : MulAut K) * MulAut.conj x = ((γ : MulAut K) * MulAut.conj x * (γ : MulAut K)⁻¹) * (γ : MulAut K) := by
          group
      _ = MulAut.conj x * (γ : MulAut K) := by rw [h2]

theorem centralizer_inf_innRange (hZ : ∀ k : K, (∀ g : K, g * k = k * g) → k = 1) (x : K) :
    centralizer ({innIn X hX x} : Set ↥X) ⊓ innRange X hX =
      (centralizer ({x} : Set K)).map (innIn X hX) := by
  ext γ
  constructor
  · rintro ⟨hc, k, rfl⟩
    refine ⟨k, ?_, rfl⟩
    have hc' : innIn X hX k ∈ centralizer ({innIn X hX x} : Set ↥X) := hc
    have := (mem_centralizer_innIn X hX hZ x (innIn X hX k)).1 hc'
    show k ∈ centralizer ({x} : Set K)
    rw [Subgroup.mem_centralizer_singleton_iff]
    have h3 : k * x * k⁻¹ = x := by simpa [MulAut.conj_apply] using this
    calc k * x = (k * x * k⁻¹) * k := by group
      _ = x * k := by rw [h3]
  · rintro ⟨k, hk, rfl⟩
    refine ⟨?_, innIn_mem_innRange X hX k⟩
    show innIn X hX k ∈ centralizer ({innIn X hX x} : Set ↥X)
    rw [mem_centralizer_innIn X hX hZ]
    have := Subgroup.mem_centralizer_singleton_iff.1 hk
    show MulAut.conj k x = x
    rw [MulAut.conj_apply]
    calc k * x * k⁻¹ = (x * k) * k⁻¹ := by rw [this]
      _ = x := by group

@[expose] noncomputable def centEquiv (hZ : ∀ k : K, (∀ g : K, g * k = k * g) → k = 1) (x : K) :
    ↥(centralizer ({x} : Set K)) ≃*
      ↥(centralizer ({innIn X hX x} : Set ↥X) ⊓ innRange X hX) :=
  ((centralizer ({x} : Set K)).equivMapOfInjective (innIn X hX) (innIn_injective X hX hZ)).trans
    (MulEquiv.subgroupCongr (centralizer_inf_innRange X hX hZ x).symm)

end Inn

theorem isG2Sp4L4U4_of_equiv {A B : Type} [Group A] [Group B] (e : A ≃* B) {q : ℕ}
    (h : IsG2Sp4L4U4_fixed A q) : IsG2Sp4L4U4_fixed B q := by
  rcases h with ⟨p, f, hp, hq, hm⟩ | ⟨F, iF, fF, hF, ⟨f⟩⟩ | ⟨h8, hl⟩ | ⟨h8, hl⟩
  · exact Or.inl ⟨p, f, hp, hq, CFSG.LieType.CurtisTits.lieModel_of_mulEquiv e hm⟩
  · exact Or.inr (Or.inl ⟨F, iF, fF, hF, ⟨e.symm.trans f⟩⟩)
  · refine Or.inr (Or.inr (Or.inl ⟨h8, ?_⟩))
    rcases hl with ⟨h1, F, i1, i2, hF, ⟨f⟩⟩ | ⟨h1, F, i1, i2, hF, ⟨f⟩⟩
    · exact Or.inl ⟨h1, F, i1, i2, hF, ⟨e.symm.trans f⟩⟩
    · exact Or.inr ⟨h1, F, i1, i2, hF, ⟨e.symm.trans f⟩⟩
  · refine Or.inr (Or.inr (Or.inr ⟨h8, ?_⟩))
    rcases hl with ⟨h1, F, i1, i2, hF, ⟨f⟩⟩ | ⟨h1, F, i1, i2, hF, ⟨f⟩⟩
    · exact Or.inl ⟨h1, F, i1, i2, hF, ⟨e.symm.trans f⟩⟩
    · exact Or.inr ⟨h1, F, i1, i2, hF, ⟨e.symm.trans f⟩⟩

theorem isLnEps_of_equiv' {n : ℕ} {A B : Type} [Group A] [Group B] {ε : ℤ} {q : ℕ} (e : A ≃* B)
    (h : IsLnEps n A ε q) : IsLnEps n B ε q := by
  rcases h with ⟨h1, F, i1, i2, hF, ⟨f⟩⟩ | ⟨h1, F, i1, i2, hF, ⟨f⟩⟩
  · exact Or.inl ⟨h1, F, i1, i2, hF, ⟨e.symm.trans f⟩⟩
  · exact Or.inr ⟨h1, F, i1, i2, hF, ⟨e.symm.trans f⟩⟩

section Sylow

variable {K : Type} [Group K] [Finite K] (X : Subgroup (MulAut K)) (hX : ∀ k : K, MulAut.conj k ∈ X)

instance : Finite (MulAut K) :=
  Finite.of_injective (fun f : MulAut K => (f : K → K)) fun _ _ h => MulEquiv.ext (congrFun h)

omit [Finite K] in
theorem exists_sylow_cent (hZ : ∀ k : K, (∀ g : K, g * k = k * g) → k = 1) {x : K}
    (hx : IsCentralInvolution x) :
    ∃ S : Sylow 2 ↥X, innIn X hX x ∈ (S : Subgroup ↥X) ∧ orderOf (innIn X hX x) = 2 ∧
      ∀ y ∈ (S : Subgroup ↥X) ⊓ innRange X hX, y * innIn X hX x = innIn X hX x * y := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hx2, P, hxP, hPc⟩ := hx
  have hP2 : IsPGroup 2 ((P : Subgroup K).map (innIn X hX)) := P.isPGroup'.map _
  obtain ⟨S, hS⟩ := hP2.exists_le_sylow
  refine ⟨S, hS ⟨x, hxP, rfl⟩, by rw [orderOf_injective _ (innIn_injective X hX hZ) x]; exact hx2, ?_⟩
  rintro y ⟨hyS, k, rfl⟩
  have hker : IsPGroup 2 ↥(innIn X hX).ker := by
    rw [(MonoidHom.ker_eq_bot_iff _).2 (innIn_injective X hX hZ)]
    exact IsPGroup.of_card (n := 0) (by simp)
  have hQ2 : IsPGroup 2 ((S : Subgroup ↥X).comap (innIn X hX)) :=
    S.isPGroup'.comap_of_ker_isPGroup (innIn X hX) hker
  have hPQ : (P : Subgroup K) ≤ (S : Subgroup ↥X).comap (innIn X hX) := fun p hp => hS ⟨p, hp, rfl⟩
  have hQP := P.is_maximal' hQ2 hPQ
  have hkP : k ∈ (P : Subgroup K) := by
    rw [← hQP]
    exact hyS
  have := hPc k hkP
  show innIn X hX k * innIn X hX x = innIn X hX x * innIn X hX k
  rw [← map_mul, ← map_mul, this]

end Sylow

section Y0

variable {K : Type} [Group K] (X : Subgroup (MulAut K)) (hX : ∀ k : K, MulAut.conj k ∈ X)

theorem pPrimeCore_ne_bot (hZ : ∀ k : K, (∀ g : K, g * k = k * g) → k = 1) {x : K}
    {Y₀ : Subgroup (MulAut K)} (hY₀X : Y₀ ≤ X) (hY₀x : ∀ β ∈ Y₀, β x = x)
    (hY₀n : ∀ γ ∈ X, γ x = x → ∀ β ∈ Y₀, γ * β * γ⁻¹ ∈ Y₀) (hodd : Odd (Nat.card ↥Y₀))
    (hne : Y₀ ≠ ⊥) :
    (pPrimeCore 2 ↥(centralizer ({innIn X hX x} : Set ↥X))).map
      (centralizer ({innIn X hX x} : Set ↥X)).subtype ≠ ⊥ := by
  set C := centralizer ({innIn X hX x} : Set ↥X) with hC
  let ψ : ↥C →* MulAut K := X.subtype.comp C.subtype
  have hψinj : Function.Injective ψ := fun a b h => Subtype.ext (Subtype.ext h)
  have hψx : ∀ c : ↥C, ψ c x = x := fun c => (mem_centralizer_innIn X hX hZ x c.1).1 c.2
  let Y₁ : Subgroup ↥C := Y₀.comap ψ
  have hY₁n : Y₁.Normal := ⟨fun n hn g => by
    show ψ (g * n * g⁻¹) ∈ Y₀
    rw [map_mul, map_mul, map_inv]
    exact hY₀n (ψ g) g.1.2 (hψx g) (ψ n) hn⟩
  have hY₀le : Y₀ ≤ ψ.range := fun β hβ =>
    ⟨⟨⟨β, hY₀X hβ⟩, (mem_centralizer_innIn X hX hZ x _).2 (hY₀x β hβ)⟩, rfl⟩
  have hmap : Y₁.map ψ = Y₀ := Subgroup.map_comap_eq_self hY₀le
  have hcard : Nat.card ↥Y₁ = Nat.card ↥Y₀ := by
    calc Nat.card ↥Y₁ = Nat.card ↥(Y₁.map ψ) := (Subgroup.card_map_of_injective hψinj).symm
      _ = Nat.card ↥Y₀ := by rw [hmap]
  have hle : Y₁ ≤ pPrimeCore 2 ↥C := le_sSup ⟨hY₁n, Nat.coprime_two_left.2 (hcard ▸ hodd)⟩
  intro h
  have hbot : pPrimeCore 2 ↥C = ⊥ := (Subgroup.map_eq_bot_iff_of_injective _ C.subtype_injective).1 h
  have hY₁ : Y₁ = ⊥ := le_bot_iff.1 (hbot ▸ hle)
  apply hne
  rw [← hmap, hY₁, Subgroup.map_bot]

end Y0

end CFSG.GH74.GLS.Stage2.Final.Thm6.L2011.CFT
