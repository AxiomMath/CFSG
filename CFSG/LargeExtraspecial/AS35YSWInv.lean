module

public import CFSG.LargeExtraspecial.AS35QCoCent
public import CFSG.LargeExtraspecial.AS35TPbar
public import CFSG.LargeExtraspecial.AS35YRU33

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial

open Subgroup Module QuadraticMap CFSG.Blueprint CFSG.RankThree.OrthogonalInvolutions
open CFSG.GH74.KGroups CFSG.GH74.KGroups.U33

namespace AS35YS

theorem exists_involution_of_card {H : Type*} [Group H] (X : Subgroup H) [Finite X] {τ : H}
    (hττ : τ * τ = 1) (hτ1 : τ ≠ 1) (hτc : ∀ x ∈ X, τ * x = x * τ)
    (hsq : ∀ x ∈ X, x * x = 1 ∨ x * x = τ) (h16 : 16 ≤ Nat.card X) :
    ∃ b ∈ X, b * b = 1 ∧ b ≠ 1 ∧ b ≠ τ := by
  classical
  by_contra hne
  push Not at hne
  have hsq' : ∀ x ∈ X, x ≠ 1 → x ≠ τ → x * x = τ := fun x hx h1 hτ' =>
    (hsq x hx).resolve_left fun h => hτ' (hne x hx h h1)
  have hex : ∀ l : List H, l.length < 16 → ∃ x ∈ X, x ∉ l := by
    intro l hl
    by_contra hcon
    push Not at hcon
    have h1 : Nat.card X ≤ l.length := by
      calc Nat.card X = (X : Set H).ncard := Nat.card_coe_set_eq _
        _ ≤ (l.toFinset : Set H).ncard :=
          Set.ncard_le_ncard (fun x hx => by simpa using hcon x hx) (Finset.finite_toSet _)
        _ = l.toFinset.card := Set.ncard_coe_finset _
        _ ≤ l.length := List.toFinset_card_le l
    omega
  have hinv : ∀ x : H, x * x = τ → x⁻¹ = x * τ := fun x h =>
    inv_eq_of_mul_eq_one_right (by rw [← mul_assoc, h, hττ])
  obtain ⟨u, hu, hul⟩ := hex [1, τ] (by norm_num)
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hul
  have hu2 := hsq' u hu hul.1 hul.2
  obtain ⟨v, hv, hvl⟩ := hex [1, τ, u, u * τ] (by norm_num)
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hvl
  have hv2 := hsq' v hv hvl.1 hvl.2.1
  obtain ⟨w, hw, hwl⟩ := hex [1, τ, u, u * τ, v, v * τ, u * v, u * v * τ] (by norm_num)
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hwl
  obtain ⟨hw1, hwτ, hwu, hwuτ, hwv, hwvτ, hwuv, hwuvτ⟩ := hwl
  have hw2 := hsq' w hw hw1 hwτ
  have hprod : ∀ x ∈ X, ∀ y ∈ X, x * x = τ → y ≠ x * τ → y ≠ x → (x * y) * (x * y) = τ := by
    intro x hx y hy hx2 hy1 hy2
    refine hsq' _ (X.mul_mem hx hy) (fun h => hy1 ?_) (fun h => hy2 ?_)
    · calc y = x⁻¹ * (x * y) := by group
        _ = x * τ := by rw [h, mul_one, hinv x hx2]
    · calc y = x⁻¹ * (x * y) := by group
        _ = x * τ * τ := by rw [h, hinv x hx2]
        _ = x := by rw [mul_assoc, hττ, mul_one]
  have huv := hprod u hu v hv hu2 hvl.2.2.2 hvl.2.2.1
  have huw := hprod u hu w hw hu2 hwuτ hwu
  have hvw := hprod v hv w hw hv2 hwvτ hwv
  have huvw := hprod (u * v) (X.mul_mem hu hv) w hw huv hwuvτ hwuv
  have hanti : ∀ x : H, x * x = τ → (x * w) * (x * w) = τ → w * x = x * w * τ := by
    intro x hx2 hxw
    calc w * x = x⁻¹ * ((x * w) * (x * w)) * w⁻¹ := by group
      _ = x⁻¹ * τ * w⁻¹ := by rw [hxw]
      _ = x * τ * τ * (w * τ) := by rw [hinv x hx2, hinv w hw2]
      _ = x * (τ * τ) * w * τ := by group
      _ = x * w * τ := by rw [hττ, mul_one]
  have hwu' := hanti u hu2 huw
  have hwv' := hanti v hv2 hvw
  have hτv := hτc v hv
  have hwa : w * (u * v) = u * v * w := by
    calc w * (u * v) = (w * u) * v := by group
      _ = (u * w * τ) * v := by rw [hwu']
      _ = u * w * (τ * v) := by group
      _ = u * w * (v * τ) := by rw [hτv]
      _ = u * (w * v) * τ := by group
      _ = u * (v * w * τ) * τ := by rw [hwv']
      _ = u * v * w * (τ * τ) := by group
      _ = u * v * w := by rw [hττ, mul_one]
  have h1 : (u * v * w) * (u * v * w) = 1 := by
    calc (u * v * w) * (u * v * w) = (u * v) * (w * (u * v)) * w := by group
      _ = (u * v) * ((u * v) * w) * w := by rw [hwa]
      _ = ((u * v) * (u * v)) * (w * w) := by group
      _ = τ * τ := by rw [huv, hw2]
      _ = 1 := hττ
  rw [huvw] at h1
  exact hτ1 h1

theorem sixteen_le_card_inf {O : Type*} [Group O] [Finite O] {M L P : Subgroup O}
    (hLM : L ≤ M) (hPM : P ≤ M) (hM : Nat.card M ≤ 12096) (hL : Nat.card L = 6048)
    (hP : Nat.card P = 32) : 16 ≤ Nat.card (L ⊓ P : Subgroup O) := by
  have h1 := Subgroup.relIndex_mul_card L M
  rw [inf_of_le_left hLM, hL] at h1
  have h2 := Subgroup.relIndex_mul_card L P
  rw [hP] at h2
  have hne : L.relIndex M ≠ 0 := by
    intro h
    rw [h, zero_mul] at h1
    have := Nat.card_pos (α := M)
    omega
  have h3 := Subgroup.relIndex_le_of_le_right (H := L) hPM hne
  have h4 : L.relIndex M ≤ 2 := by
    by_contra h
    push Not at h
    have : 3 * 6048 ≤ L.relIndex M * 6048 := Nat.mul_le_mul_right _ h
    omega
  by_contra h
  push Not at h
  have : L.relIndex P * Nat.card (L ⊓ P : Subgroup O) ≤ 2 * 15 :=
    Nat.mul_le_mul (h3.trans h4) (by omega)
  omega

end AS35YS

namespace Setting

variable {G : Type} [Group G] [Finite G] {S : Setting G}

theorem pbar_sq_YS {g : G} (htM : g * S.z * g⁻¹ ∈ S.M) {σ : S.O} (hσ : σ ∈ S.PbarAsc g) :
    σ * σ = 1 ∨ σ * σ = S.ρ ⟨_, htM⟩ := by
  obtain ⟨⟨p, hpM⟩, hpQt, rfl⟩ := (AS35T.mem_pbar_iff S).mp hσ
  have e : S.ρ ⟨p, hpM⟩ * S.ρ ⟨p, hpM⟩ = S.ρ ⟨p ^ 2, S.M.pow_mem hpM 2⟩ := by
    rw [← map_mul]
    congr 1
    exact Subtype.ext (pow_two p).symm
  rw [e]
  rcases AS35T.sq_eq_one_or_of_mem_Qa S hpQt with h | h
  · left
    have h' : (⟨p ^ 2, S.M.pow_mem hpM 2⟩ : S.M) = 1 := Subtype.ext h
    rw [h', map_one]
  · right
    congr 1
    exact Subtype.ext h

theorem pbar_comm_t_YS {g : G} (htM : g * S.z * g⁻¹ ∈ S.M) {σ : S.O} (hσ : σ ∈ S.PbarAsc g) :
    S.ρ ⟨_, htM⟩ * σ = σ * S.ρ ⟨_, htM⟩ := by
  obtain ⟨⟨p, hpM⟩, hpQt, rfl⟩ := (AS35T.mem_pbar_iff S).mp hσ
  rw [← map_mul, ← map_mul]
  congr 1
  exact Subtype.ext (AS35T.commute_of_mem_Qa S hpQt).symm

theorem mem_DbarAsc_of_inv_u33_YS
    (hS : S.SixHyp)
    (hst : S.Asc512Standing) (hnd : InspNondeg _ S.EhatAsc)
    (hL : LieModel (S.LbarAsc ⧸ center S.LbarAsc) .PSU 3 3 1) {t b : S.O}
    (htD : t ∈ S.DbarAsc) (hbL : b ∈ S.LbarAsc) (hbb : b * b = 1) (hb1 : b ≠ 1) :
    b ∈ S.DbarAsc := by
  have hc := center_LbarAsc_eq_bot_YL hS hst hnd
  obtain ⟨e⟩ := equiv_of_lieModel hL
  set θ : S.LbarAsc ≃* QP.originalSubgroup := (AS35YL.quotEquiv_YL S.LbarAsc hc).symm.trans e
    with hθ
  have htL : t ∈ S.LbarAsc := subset_closure htD
  have hinvP : ∀ (y : S.O) (hy : y ∈ S.LbarAsc), y * y = 1 → y ≠ 1 →
      ∃ c ∈ QP.originalSubgroup, c * (θ ⟨y, hy⟩ : Equiv.Perm (Fin 28)) * c⁻¹ = AS35YR.u33d0 := by
    intro y hy hyy hy1
    refine AS35YR.exists_conj_u33d0 (θ ⟨y, hy⟩).2 ?_ ?_
    · have h1 : (⟨y, hy⟩ : S.LbarAsc) * ⟨y, hy⟩ = 1 := Subtype.ext hyy
      have h2 := congrArg (fun a => ((θ a : QP.originalSubgroup) : Equiv.Perm (Fin 28))) h1
      simpa only [map_mul, map_one, Subgroup.coe_mul, Subgroup.coe_one] using h2
    · intro h
      apply hy1
      have h2 : θ ⟨y, hy⟩ = 1 := Subtype.ext h
      exact congrArg Subtype.val (θ.injective (h2.trans (map_one θ).symm))
  obtain ⟨c₁, hc₁, hb⟩ := hinvP b hbL hbb hb1
  obtain ⟨c₂, hc₂, ht⟩ := hinvP t htL (mul_self_of_mem_DbarAsc_YL htD)
    (fun h => (isTypeA_of_mem_DbarAsc_YL hS htD).2.1 (by rw [h]; rfl))
  set k : S.LbarAsc := θ.symm ⟨c₁⁻¹ * c₂, QP.originalSubgroup.mul_mem
    (QP.originalSubgroup.inv_mem hc₁) hc₂⟩ with hk
  have hkt : k * ⟨t, htL⟩ * k⁻¹ = ⟨b, hbL⟩ := by
    apply θ.injective
    apply Subtype.ext
    rw [map_mul, map_mul, map_inv, hk, MulEquiv.apply_symm_apply]
    change c₁⁻¹ * c₂ * (θ ⟨t, htL⟩ : Equiv.Perm (Fin 28)) * (c₁⁻¹ * c₂)⁻¹ =
      (θ ⟨b, hbL⟩ : Equiv.Perm (Fin 28))
    calc c₁⁻¹ * c₂ * (θ ⟨t, htL⟩ : Equiv.Perm (Fin 28)) * (c₁⁻¹ * c₂)⁻¹
        = c₁⁻¹ * (c₂ * (θ ⟨t, htL⟩ : Equiv.Perm (Fin 28)) * c₂⁻¹) * c₁ := by group
      _ = c₁⁻¹ * (c₁ * (θ ⟨b, hbL⟩ : Equiv.Perm (Fin 28)) * c₁⁻¹) * c₁ := by rw [ht, hb]
      _ = (θ ⟨b, hbL⟩ : Equiv.Perm (Fin 28)) := by group
  have h1 := conj_mem_DbarAsc_YL k.2 htD
  have h2 : (k : S.O) * t * (k : S.O)⁻¹ = b := congrArg Subtype.val hkt
  rwa [h2] at h1

theorem exists_dbar_mem_pbar_YS
    (hS : S.SixHyp)
    (hst : S.Asc512Standing) (hnd : InspNondeg _ S.EhatAsc)
    (hL : LieModel (S.LbarAsc ⧸ center S.LbarAsc) .PSU 3 3 1) (h4 : S.width = 4)
    (hM : Nat.card S.Mbar ≤ 12096) {g : G} (ht : g * S.z * g⁻¹ ∈ S.DSet)
    (htM : g * S.z * g⁻¹ ∈ S.M) :
    ∃ b ∈ S.LbarAsc ⊓ S.PbarAsc g, b ∈ S.DbarAsc ∧ b ≠ S.ρ ⟨_, htM⟩ := by
  have := AS35QCo.finite_lin S
  have hc := center_LbarAsc_eq_bot_YL hS hst hnd
  obtain ⟨e⟩ := equiv_of_lieModel hL
  have hLcard : Nat.card S.LbarAsc = 6048 := by
    rw [Nat.card_congr ((AS35YL.quotEquiv_YL S.LbarAsc hc).symm.trans e).toEquiv,
      AS35YR.card_QP]
  have hPcard : Nat.card (S.PbarAsc g) = 32 := by
    rw [AS35T.card_pbar hS ht, h4]
    norm_num
  have hPM : S.PbarAsc g ≤ S.Mbar := map_le_range _ _
  have h16 := AS35YS.sixteen_le_card_inf LbarAsc_le_Mbar_YL hPM hM hLcard hPcard
  have htD : S.ρ ⟨_, htM⟩ ∈ S.DbarAsc := ⟨_, ht, htM, rfl⟩
  have htt : S.ρ ⟨_, htM⟩ * S.ρ ⟨_, htM⟩ = 1 := mul_self_of_mem_DbarAsc_YL htD
  have ht1 : S.ρ ⟨_, htM⟩ ≠ 1 := fun h => (isTypeA_of_mem_DbarAsc_YL hS htD).2.1 (by rw [h]; rfl)
  obtain ⟨b, hbX, hbb, hb1, hbt⟩ := AS35YS.exists_involution_of_card (S.LbarAsc ⊓ S.PbarAsc g)
    htt ht1 (fun x hx => pbar_comm_t_YS htM (mem_inf.mp hx).2)
    (fun x hx => pbar_sq_YS htM (mem_inf.mp hx).2) h16
  exact ⟨b, hbX, mem_DbarAsc_of_inv_u33_YS hS hst hnd hL htD (mem_inf.mp hbX).1 hbb hb1, hbt⟩

end Setting

end CFSG.LargeExtraspecial
