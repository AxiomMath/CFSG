module

public import CFSG.LargeExtraspecial.AS35YFBase

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial

open Subgroup
open scoped commutatorElement

namespace Setting

theorem asc_mul_comm_of_card_le_three {Y : Type*} [Group Y] [Finite Y] (h : Nat.card Y ≤ 3)
    (a b : Y) : a * b = b * a := by
  have hpos : 0 < Nat.card Y := Nat.card_pos
  rcases (by omega : Nat.card Y = 1 ∨ Nat.card Y = 2 ∨ Nat.card Y = 3) with h1 | h1 | h1
  · have : Subsingleton Y := (Nat.card_eq_one_iff_unique.mp h1).1
    exact Subsingleton.elim _ _
  · have : Fact (Nat.Prime (Nat.card Y)) := ⟨by rw [h1]; norm_num⟩
    have := isCyclic_of_prime_card (α := Y) rfl
    exact (IsCyclic.isMulCommutative (α := Y)).is_comm.comm a b
  · have : Fact (Nat.Prime (Nat.card Y)) := ⟨by rw [h1]; norm_num⟩
    have := isCyclic_of_prime_card (α := Y) rfl
    exact (IsCyclic.isMulCommutative (α := Y)).is_comm.comm a b

theorem asc_three_lt_card_of_isQuasisimple {Y : Type*} [Group Y] [Finite Y]
    (hY : CFSG.IsQuasisimple Y) : 3 < Nat.card Y := by
  by_contra h
  push Not at h
  obtain ⟨-, -, a, b, hab⟩ := hY
  obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective a
  obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective b
  apply hab
  rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, asc_mul_comm_of_card_le_three h a b]

theorem asc_layer_eq_top {Y : Type*} [Group Y] (hY : CFSG.IsQuasisimple Y) :
    CFSG.layer Y = ⊤ :=
  eq_top_iff.mpr (CFSG.LocalCores.component_le_layer
    ⟨CFSG.LocalCores.isQuasisimple_of_mulEquiv Subgroup.topEquiv.symm hY,
      Subgroup.IsSubnormal.top⟩)

theorem asc_conj_mem_commutator {Y : Type*} [Group Y] {A : Subgroup Y} {p : Y}
    (hA : ∀ y ∈ A, p * y * p⁻¹ ∈ A) {x : Y} (hx : x ∈ ⁅A, A⁆) : p * x * p⁻¹ ∈ ⁅A, A⁆ := by
  have hle : A.map (MulAut.conj p).toMonoidHom ≤ A := by
    rintro _ ⟨y, hy, rfl⟩
    exact hA y hy
  have h1 : ⁅A, A⁆.map (MulAut.conj p).toMonoidHom ≤ ⁅A, A⁆ := by
    rw [Subgroup.map_commutator]
    exact Subgroup.commutator_mono hle hle
  exact h1 ⟨x, hx, rfl⟩

theorem asc_aut_mem_commutator {Y : Type*} [Group Y] {A : Subgroup Y} (α : MulAut Y)
    (hA : ∀ y ∈ A, α y ∈ A) {x : Y} (hx : x ∈ ⁅A, A⁆) : α x ∈ ⁅A, A⁆ := by
  have hle : A.map α.toMonoidHom ≤ A := by
    rintro _ ⟨y, hy, rfl⟩
    exact hA y hy
  have h1 : ⁅A, A⁆.map α.toMonoidHom ≤ ⁅A, A⁆ := by
    rw [Subgroup.map_commutator]
    exact Subgroup.commutator_mono hle hle
  exact h1 ⟨x, hx, rfl⟩

theorem asc_exists_quasisimple_lift {Y : Type*} [Group Y] (L : Subgroup Y)
    {K : Subgroup (L ⧸ center L)} (hK : CFSG.IsQuasisimple K) :
    ∃ X : Subgroup Y, X ≤ L ∧ CFSG.IsQuasisimple X ∧
      (∀ x (hx : x ∈ L), x ∈ X → (QuotientGroup.mk ⟨x, hx⟩ : L ⧸ center L) ∈ K) ∧
      ∀ p : Y, ∀ hpL : (∀ y ∈ L, p * y * p⁻¹ ∈ L),
        (∀ y (hy : y ∈ L), (QuotientGroup.mk ⟨y, hy⟩ : L ⧸ center L) ∈ K →
          (QuotientGroup.mk ⟨p * y * p⁻¹, hpL y hy⟩ : L ⧸ center L) ∈ K) →
        ∀ x ∈ X, p * x * p⁻¹ ∈ X := by
  set Kt : Subgroup L := K.comap (QuotientGroup.mk' (center L)) with hKt
  have hf : ∀ x : Kt, QuotientGroup.mk' (center L) (x : L) ∈ K := fun x => x.2
  set f : Kt →* K := ((QuotientGroup.mk' (center L)).comp Kt.subtype).codRestrict K hf with hfdef
  have hfs : Function.Surjective f := by
    rintro ⟨y, hy⟩
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective (center L) y
    exact ⟨⟨x, hy⟩, rfl⟩
  have hfker : f.ker ≤ center Kt := by
    intro x hx
    have hx' : (x : L) ∈ center L := by
      have h1 : f x = 1 := hx
      have h2 : QuotientGroup.mk' (center L) (x : L) = 1 := congrArg Subtype.val h1
      rwa [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h2
    exact mem_center_iff.mpr fun y => Subtype.ext (mem_center_iff.mp hx' y)
  have hQ := CFSG.LocalCores.quasisimple_central_extension_derived_of_surjective f hfs hfker hK
  set A : Subgroup Y := Kt.map L.subtype with hA
  set X : Subgroup Y := (commutator Kt).map (L.subtype.comp Kt.subtype) with hX
  have hXA : X = ⁅A, A⁆ := by
    rw [hX, hA, _root_.commutator_def, Subgroup.map_commutator, ← MonoidHom.range_eq_map,
      MonoidHom.range_comp, Subgroup.range_subtype]
  have hXle : X ≤ A := by
    rw [hXA, Subgroup.commutator_le]
    intro a ha b hb
    rw [commutatorElement_def]
    exact mul_mem (mul_mem (mul_mem ha hb) (inv_mem ha)) (inv_mem hb)
  have hAL : A ≤ L := map_subtype_le _
  refine ⟨X, hXle.trans hAL, ?_, ?_, ?_⟩
  · exact CFSG.LocalCores.isQuasisimple_of_mulEquiv
      ((commutator Kt).equivMapOfInjective _ ((L.subtype_injective).comp
        Kt.subtype_injective)) hQ
  · intro x hx hxX
    obtain ⟨y, hy, hyx⟩ := hXle hxX
    have : y = ⟨x, hx⟩ := Subtype.ext hyx
    rw [← this]
    exact hy
  · intro p hpL hpK x hx
    rw [hXA] at hx ⊢
    refine asc_conj_mem_commutator ?_ hx
    rintro _ ⟨y, hy, rfl⟩
    exact ⟨⟨_, hpL y y.2⟩, hpK y y.2 hy, rfl⟩

theorem asc_mul_comm_of_mulEquiv {A B : Type*} [Group A] [Group B] (e : A ≃* B) {k : B}
    (h : ∀ x : A, e.symm k * x = x * e.symm k) (x : B) : k * x = x * k := by
  have := congrArg e (h (e.symm x))
  simpa using this

theorem asc_exists_hom_of_mulEquiv {A K H : Type*} [Group A] [Group K] [Group H] (e : A ≃* K)
    (ρ : A →* H) (hρ : Function.Surjective ρ) (hker : ∀ k ∈ ρ.ker, ∀ x, k * x = x * k) :
    ∃ ρ' : K →* H, Function.Surjective ρ' ∧ ∀ k ∈ ρ'.ker, ∀ x, k * x = x * k := by
  refine ⟨ρ.comp e.symm.toMonoidHom, hρ.comp e.symm.surjective, fun k hk x => ?_⟩
  have hk' : e.symm k ∈ ρ.ker := hk
  exact asc_mul_comm_of_mulEquiv e (hker _ hk') x

theorem asc_nonempty_centralizer_mulEquiv {A B : Type*} [Group A] [Group B] (ψ : A ≃* B)
    (a : A) : Nonempty (centralizer ({a} : Set A) ≃* centralizer ({ψ a} : Set B)) := by
  have h : (centralizer ({a} : Set A)).map ψ.toMonoidHom = centralizer ({ψ a} : Set B) := by
    ext b
    rw [Subgroup.mem_map_equiv, mem_centralizer_singleton_iff, mem_centralizer_singleton_iff]
    constructor
    · intro hb
      have := congrArg ψ hb
      simpa using this
    · intro hb
      apply ψ.injective
      simpa using hb
  exact ⟨(ψ.subgroupMap _).trans (MulEquiv.subgroupCongr h)⟩

theorem asc_nonempty_commutator_mulEquiv {A B : Type*} [Group A] [Group B] (e : A ≃* B) :
    Nonempty (commutator A ≃* commutator B) := by
  have h : (commutator A).map e.toMonoidHom = commutator B := by
    rw [_root_.commutator_def, _root_.commutator_def, Subgroup.map_commutator,
      Subgroup.map_top_of_surjective _ e.surjective]
  exact ⟨(e.subgroupMap _).trans (MulEquiv.subgroupCongr h)⟩

section Generic

variable {Xh : Type*} [Group Xh] {τ : Xh} {𝒜 : Set (MulAut Xh)}

theorem asc_commutator_le_self (K : Subgroup Xh) : ⁅K, K⁆ ≤ K := by
  rw [Subgroup.commutator_le]
  intro a ha b hb
  rw [commutatorElement_def]
  exact mul_mem (mul_mem (mul_mem ha hb) (inv_mem ha)) (inv_mem hb)

theorem asc_false_of_hom_simple_gen
    (hub : ∀ K : Subgroup Xh, CFSG.IsQuasisimple K → (∀ y ∈ K, y * τ = τ * y) →
      (∀ α ∈ 𝒜, ∀ y ∈ K, α y ∈ K) → False)
    {K : Subgroup Xh} (hKt : ∀ y ∈ K, y * τ = τ * y) (hKP : ∀ α ∈ 𝒜, ∀ y ∈ K, α y ∈ K)
    {H : Type*} [Group H] [IsSimpleGroup H] (hH : ¬ Group.IsSolvable H) (ρ : K →* H)
    (hρ : Function.Surjective ρ) (hker : ∀ k ∈ ρ.ker, ∀ x, k * x = x * k) : False := by
  have hna : ∃ a b : H, a * b ≠ b * a := by
    by_contra h
    push Not at h
    exact hH (Group.isSolvable_of_comm h)
  have hQH := (CFSG.LocalCores.isQuasisimple_of_isSimpleGroup hna).1
  have hQ := CFSG.LocalCores.quasisimple_central_extension_derived_of_surjective ρ hρ
    (fun k hk => mem_center_iff.mpr fun x => (hker k hk x).symm) hQH
  have hK1 : (commutator K).map K.subtype = ⁅K, K⁆ := by
    rw [_root_.commutator_def, Subgroup.map_commutator, ← MonoidHom.range_eq_map,
      Subgroup.range_subtype]
  refine hub ⁅K, K⁆ ?_ (fun y hy => hKt y (asc_commutator_le_self K hy))
    (fun α hα y hy => asc_aut_mem_commutator α (hKP α hα) hy)
  rw [← hK1]
  exact CFSG.LocalCores.isQuasisimple_of_mulEquiv
    ((commutator K).equivMapOfInjective _ K.subtype_injective) hQ

theorem asc_false_of_centralizer_hom_simple_gen
    (hub : ∀ K : Subgroup Xh, CFSG.IsQuasisimple K → (∀ y ∈ K, y * τ = τ * y) →
      (∀ α ∈ 𝒜, ∀ y ∈ K, α y ∈ K) → False)
    (h𝒜 : ∀ α ∈ 𝒜, α τ = τ)
    {H : Type*} [Group H] [IsSimpleGroup H] (hH : ¬ Group.IsSolvable H)
    (ρ : centralizer ({τ} : Set Xh) →* H) (hρ : Function.Surjective ρ)
    (hker : ∀ k ∈ ρ.ker, ∀ x, k * x = x * k) : False := by
  refine asc_false_of_hom_simple_gen hub (fun y hy => mem_centralizer_singleton_iff.mp hy)
    (fun α hα y hy => ?_) hH ρ hρ hker
  rw [mem_centralizer_singleton_iff] at hy ⊢
  rw [← h𝒜 α hα, ← map_mul, ← map_mul, hy]

theorem asc_false_of_centralizer_commutator_hom_simple_gen
    (hub : ∀ K : Subgroup Xh, CFSG.IsQuasisimple K → (∀ y ∈ K, y * τ = τ * y) →
      (∀ α ∈ 𝒜, ∀ y ∈ K, α y ∈ K) → False)
    (h𝒜 : ∀ α ∈ 𝒜, α τ = τ)
    {H : Type*} [Group H] [IsSimpleGroup H] (hH : ¬ Group.IsSolvable H)
    (ρ : commutator (centralizer ({τ} : Set Xh)) →* H) (hρ : Function.Surjective ρ)
    (hker : ∀ k ∈ ρ.ker, ∀ x, k * x = x * k) : False := by
  have hCP : ∀ α ∈ 𝒜, ∀ y ∈ centralizer ({τ} : Set Xh), α y ∈ centralizer ({τ} : Set Xh) := by
    intro α hα y hy
    rw [mem_centralizer_singleton_iff] at hy ⊢
    rw [← h𝒜 α hα, ← map_mul, ← map_mul, hy]
  have hK1 : (commutator (centralizer ({τ} : Set Xh))).map (centralizer ({τ} : Set Xh)).subtype =
      ⁅centralizer ({τ} : Set Xh), centralizer ({τ} : Set Xh)⁆ := by
    rw [_root_.commutator_def, Subgroup.map_commutator, ← MonoidHom.range_eq_map,
      Subgroup.range_subtype]
  obtain ⟨ρ', hρ', hker'⟩ := asc_exists_hom_of_mulEquiv
    (((commutator _).equivMapOfInjective _ (centralizer ({τ} : Set Xh)).subtype_injective).trans
      (MulEquiv.subgroupCongr hK1)) ρ hρ hker
  exact asc_false_of_hom_simple_gen hub
    (fun y hy => mem_centralizer_singleton_iff.mp (asc_commutator_le_self _ hy))
    (fun α hα y hy => asc_aut_mem_commutator α (hCP α hα) hy) hH ρ' hρ' hker'

theorem asc_false_of_centralizer_hom_simple_equiv
    (hub : ∀ K : Subgroup Xh, CFSG.IsQuasisimple K → (∀ y ∈ K, y * τ = τ * y) →
      (∀ α ∈ 𝒜, ∀ y ∈ K, α y ∈ K) → False)
    (h𝒜 : ∀ α ∈ 𝒜, α τ = τ) {Y : Type*} [Group Y] (ψ : Xh ≃* Y)
    {H : Type*} [Group H] [IsSimpleGroup H] (hH : ¬ Group.IsSolvable H)
    (ρ : centralizer ({ψ τ} : Set Y) →* H) (hρ : Function.Surjective ρ)
    (hker : ∀ k ∈ ρ.ker, ∀ x, k * x = x * k) : False := by
  obtain ⟨e⟩ := asc_nonempty_centralizer_mulEquiv ψ τ
  obtain ⟨ρ', hρ', hker'⟩ := asc_exists_hom_of_mulEquiv e.symm ρ hρ hker
  exact asc_false_of_centralizer_hom_simple_gen hub h𝒜 hH ρ' hρ' hker'

theorem asc_false_of_centralizer_commutator_hom_simple_equiv
    (hub : ∀ K : Subgroup Xh, CFSG.IsQuasisimple K → (∀ y ∈ K, y * τ = τ * y) →
      (∀ α ∈ 𝒜, ∀ y ∈ K, α y ∈ K) → False)
    (h𝒜 : ∀ α ∈ 𝒜, α τ = τ) {Y : Type*} [Group Y] (ψ : Xh ≃* Y)
    {H : Type*} [Group H] [IsSimpleGroup H] (hH : ¬ Group.IsSolvable H)
    (ρ : commutator (centralizer ({ψ τ} : Set Y)) →* H) (hρ : Function.Surjective ρ)
    (hker : ∀ k ∈ ρ.ker, ∀ x, k * x = x * k) : False := by
  obtain ⟨e⟩ := asc_nonempty_centralizer_mulEquiv ψ τ
  obtain ⟨ec⟩ := asc_nonempty_commutator_mulEquiv e
  obtain ⟨ρ', hρ', hker'⟩ := asc_exists_hom_of_mulEquiv ec.symm ρ hρ hker
  exact asc_false_of_centralizer_commutator_hom_simple_gen hub h𝒜 hH ρ' hρ' hker'

end Generic

variable {G : Type} [Group G] [Finite G] {S : Setting G}

variable (hst : S.Asc512Standing)
include hst

theorem asc_false_of_quasisimple (h58 : S14.Asc512FiveEightStmt) (hS : S.SixHyp) {g : G}
    (htD : g * S.z * g⁻¹ ∈ S.DSet) (htM : g * S.z * g⁻¹ ∈ S.M)
    {K : Subgroup (S.LbarAsc ⧸ center S.LbarAsc)} (hK : CFSG.IsQuasisimple K)
    (hKt : ∀ y ∈ K, y * QuotientGroup.mk (ascTL htD htM) = QuotientGroup.mk (ascTL htD htM) * y)
    (hKP : ∀ p : S.Mbar, (p : S.O) ∈ S.PbarAsc g → ∀ y ∈ K, ascAct hst p y ∈ K) : False := by
  obtain ⟨X, hXL, hXQ, hXK, hXP⟩ := asc_exists_quasisimple_lift S.LbarAsc hK
  have hcard := h58 G S hS g htD htM X (hXL.trans asc_Lbar_le_Mbar)
    (fun x hx => by
      have h1 := hKt _ (hXK x (hXL hx) hx)
      have h2 := asc_commute_of_mk_commute hst (c := ⟨x, hXL hx⟩) (S.ρ_mem_DbarAsc htD htM) h1
      exact congrArg Subtype.val h2)
    (fun p hp x hx => hXP p (fun y hy => hst.normal p (asc_Pbar_le_Mbar g hp) y hy)
      (fun y hy hyK => by
        have h1 := hKP ⟨p, asc_Pbar_le_Mbar g hp⟩ hp _ hyK
        simp only [ascAct_mk] at h1
        have e : ascConjL hst ⟨p, asc_Pbar_le_Mbar g hp⟩ ⟨y, hy⟩ =
            ⟨p * y * p⁻¹, hst.normal p (asc_Pbar_le_Mbar g hp) y hy⟩ :=
          Subtype.ext (ascConjL_apply hst _ _)
        rwa [e] at h1) x hx)
    (by rw [asc_layer_eq_top hXQ, sup_top_eq])
  have := asc_three_lt_card_of_isQuasisimple hXQ
  omega

theorem ascAct_tbar (hP : S14.Asc512PbarStmt) (hS : S.SixHyp) {g : G}
    (htD : g * S.z * g⁻¹ ∈ S.DSet) (htM : g * S.z * g⁻¹ ∈ S.M) {p : S.Mbar}
    (hp : (p : S.O) ∈ S.PbarAsc g) :
    ascAct hst p (QuotientGroup.mk (ascTL htD htM)) = QuotientGroup.mk (ascTL htD htM) := by
  simp only [ascAct_mk]
  congr 1
  apply Subtype.ext
  rw [ascConjL_apply]
  have h := asc_commute_tbar hP hS htD htM hp
  calc (p : S.O) * ((ascTL htD htM : S.LbarAsc) : S.O) * (p : S.O)⁻¹ =
      (p : S.O) * S.ρ ⟨_, htM⟩ * (p : S.O)⁻¹ := rfl
    _ = S.ρ ⟨_, htM⟩ := by rw [h, mul_inv_cancel_right]

theorem asc_hub (h58 : S14.Asc512FiveEightStmt) (hS : S.SixHyp) {g : G}
    (htD : g * S.z * g⁻¹ ∈ S.DSet) (htM : g * S.z * g⁻¹ ∈ S.M) :
    ∀ K : Subgroup (S.LbarAsc ⧸ center S.LbarAsc), CFSG.IsQuasisimple K →
      (∀ y ∈ K, y * QuotientGroup.mk (ascTL htD htM) = QuotientGroup.mk (ascTL htD htM) * y) →
      (∀ α ∈ {α | ∃ p : S.Mbar, (p : S.O) ∈ S.PbarAsc g ∧ α = ascAct hst p},
        ∀ y ∈ K, α y ∈ K) → False := by
  intro K hK hKt hKP
  exact asc_false_of_quasisimple hst h58 hS htD htM hK hKt
    (fun p hp y hy => hKP _ ⟨p, hp, rfl⟩ y hy)

theorem asc_hub_fix (hP : S14.Asc512PbarStmt) (hS : S.SixHyp) {g : G}
    (htD : g * S.z * g⁻¹ ∈ S.DSet) (htM : g * S.z * g⁻¹ ∈ S.M) :
    ∀ α ∈ {α | ∃ p : S.Mbar, (p : S.O) ∈ S.PbarAsc g ∧ α = ascAct hst p},
      α (QuotientGroup.mk (ascTL htD htM)) = QuotientGroup.mk (ascTL htD htM) := by
  rintro _ ⟨p, hp, rfl⟩
  exact ascAct_tbar hst hP hS htD htM hp

theorem asc_hub_E {g : G} :
    ∀ α ∈ {α | ∃ p : S.Mbar, (p : S.O) ∈ S.PbarAsc g ∧ α = ascAct hst p},
      ∀ e ∈ S.EhatAsc, α e ∈ S.EhatAsc := by
  rintro _ ⟨p, -, rfl⟩ _ ⟨d, hd, rfl⟩
  simp only [QuotientGroup.mk'_apply, ascAct_mk]
  refine ⟨ascConjL hst p d, ?_, rfl⟩
  show ((ascConjL hst p d : S.LbarAsc) : S.O) ∈ S.DbarAsc
  rw [ascConjL_apply]
  exact S.conj_mem_DbarAsc_L p.2 hd

end Setting

end CFSG.LargeExtraspecial
