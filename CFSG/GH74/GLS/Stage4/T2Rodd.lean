module

public import CFSG.GH74.GLS.Stage4.T2Ctx

public section

namespace CFSG.GH74.GLS.Stage4.Rest

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.Stage4.Hex CFSG.GH74.GLS.Stage4.Rest.T2

section Rodd

variable {G : Type} [Group G] [Finite G] {Gs : Type} [Group Gs] {q₁ q₂ : ℕ} {z t : G}
  {K₁ K₂ S : Subgroup G} {F₁ F₂ : Type} [Field F₁] [Field F₂]

theorem t2C_R_odd_trivial (hSet : Ch6Setup G Gs q₁ q₂ z K₁ K₂ F₁ F₂) (hRem : Ch6Rem z K₁ K₂ F₁ F₂ t)
    (ctx : T2Ctx z K₁ K₂ S) :
    ∀ x ∈ centralizer ({z} : Set G), Odd (orderOf x) → (∀ k ∈ K₁ ⊔ K₂, x * k = k * x) → x = 1 := by
  classical
  intro x hxC hxodd hxK
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set C : Subgroup G := centralizer ({z} : Set G) with hCdef
  set C₁ : Subgroup G := oPrimeResidualOf 2 C with hC₁def
  have hC₁C : C₁ ≤ C := ctx.C₁C
  have hKC : ∀ k ∈ K₁ ⊔ K₂, k ∈ C := fun k hk => hSet.le_centralizer hk
  let R : Subgroup G := Subgroup.centralizer ((K₁ ⊔ K₂ : Subgroup G) : Set G) ⊓ C
  have hRmem : ∀ y, y ∈ R ↔ y ∈ C ∧ ∀ k ∈ K₁ ⊔ K₂, y * k = k * y := by
    intro y
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨h2, fun k hk => ((Subgroup.mem_centralizer_iff.1 h1) k hk).symm⟩
    · rintro ⟨h1, h2⟩
      exact ⟨Subgroup.mem_centralizer_iff.2 (fun k hk => (h2 k hk).symm), h1⟩
  have hRC : R ≤ C := inf_le_right
  have hxR : x ∈ R := (hRmem x).2 ⟨hxC, hxK⟩
  have hzR : z ∈ R := (hRmem z).2 ⟨Subgroup.mem_centralizer_singleton_iff.2 rfl, fun k hk =>
    (Subgroup.mem_centralizer_singleton_iff.1 (hKC k hk)).symm⟩
  have hRnorm : ∀ c ∈ C, ∀ r ∈ R, c * r * c⁻¹ ∈ R := by
    intro c hc r hr
    obtain ⟨hrC, hrK⟩ := (hRmem r).1 hr
    refine (hRmem _).2 ⟨C.mul_mem (C.mul_mem hc hrC) (C.inv_mem hc), fun k hk => ?_⟩
    have hk' : c⁻¹ * k * c ∈ K₁ ⊔ K₂ := by simpa using ctx.Kn c⁻¹ (C.inv_mem hc) k hk
    have h1 := hrK _ hk'
    calc c * r * c⁻¹ * k = c * (r * (c⁻¹ * k * c)) * c⁻¹ := by group
      _ = c * ((c⁻¹ * k * c) * r) * c⁻¹ := by rw [h1]
      _ = k * (c * r * c⁻¹) := by group
  have hRC₁ : ∀ y ∈ R, y ∈ C₁ → y ∈ Subgroup.zpowers z := fun y hy hyC₁ =>
    t2C_centK_C₁ hSet hRem ctx.C y hyC₁ ((hRmem y).1 hy).2
  have hzC₁ : z ∈ C₁ := by
    have h : z ∈ K₁ ⊔ K₂ ⊔ S := Subgroup.mem_sup_left (Subgroup.mem_sup_left hSet.z_mem₁)
    rw [ctx.KS] at h
    exact h
  have hZeq : Subgroup.zpowers z = C₁ ⊓ R := by
    apply le_antisymm
    · exact le_inf (Subgroup.zpowers_le.2 hzC₁) (Subgroup.zpowers_le.2 hzR)
    · rintro y ⟨hy1, hy2⟩
      exact hRC₁ y hy2 hy1
  have hC₁idx : ¬ 2 ∣ C₁.relIndex C := by
    have h1 : S.relIndex C₁ * C₁.relIndex C = S.relIndex C :=
      Subgroup.relIndex_mul_relIndex S C₁ C ctx.SC₁ hC₁C
    have h2 : S.relIndex C ∣ S.index := Subgroup.relIndex_dvd_index_of_le (ctx.SC₁.trans hC₁C)
    intro h
    exact ctx.Sctx.Sidx ((h.trans (Dvd.intro_left _ h1)).trans h2)
  have hRidx : ¬ 2 ∣ ((Subgroup.zpowers z).subgroupOf R).index := by
    have e1 : ((Subgroup.zpowers z).subgroupOf R).index = C₁.relIndex R := by
      rw [hZeq]; exact Subgroup.inf_relIndex_right C₁ R
    have hn : (C₁.subgroupOf C).Normal := ⟨fun n hn g => by
      rw [Subgroup.mem_subgroupOf] at hn ⊢
      simpa using ctx.C₁norm (g : G) g.2 (n : G) hn⟩
    have e2 := Subgroup.relIndex_dvd_index_of_normal (H := C₁.subgroupOf C) (K := R.subgroupOf C)
    rw [Subgroup.relIndex_subgroupOf hRC] at e2
    rw [e1]
    exact fun h => hC₁idx (h.trans e2)
  have hZp0 : IsPGroup 2 ↥(Subgroup.zpowers z) := by
    intro g
    refine ⟨1, ?_⟩
    apply Subtype.ext
    rcases t2C_zpowers_cases ctx.zz g.2 with h | h
    · simp [h]
    · simp [h, pow_two, ctx.zz]
  have hZp : IsPGroup 2 ↥((Subgroup.zpowers z).subgroupOf R) := hZp0.comap_subtype
  have hZc : ∀ a ∈ (Subgroup.zpowers z).subgroupOf R, ∀ y : ↥R, a * y = y * a := by
    intro a ha y
    obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.1 (Subgroup.mem_subgroupOf.1 ha)
    apply Subtype.ext
    have hc : Commute z (y : G) := (Subgroup.mem_centralizer_singleton_iff.1 (hRC y.2)).symm
    show ((a : ↥R) : G) * (y : G) = (y : G) * ((a : ↥R) : G)
    rw [← hn]
    exact (hc.zpow_left n).eq
  obtain ⟨M, hMn, hModd, hMall, -, -⟩ := t2C_exists_odd_normal _ hZp hRidx hZc
  let M' : Subgroup G := M.map R.subtype
  have hM'C : M' ≤ C := fun y ⟨m, _, hm⟩ => hm ▸ hRC m.2
  have hM'odd : ∀ y ∈ M', Odd (orderOf y) := by
    rintro _ ⟨m, hm, rfl⟩
    have h1 : orderOf (⟨m, hm⟩ : ↥M) ∣ Nat.card ↥M := orderOf_dvd_natCard _
    rw [Subgroup.orderOf_mk] at h1
    show Odd (orderOf (m : G))
    rw [Subgroup.orderOf_coe]
    exact Odd.of_dvd_nat hModd h1
  have hM'norm : ∀ c ∈ C, ∀ y ∈ M', c * y * c⁻¹ ∈ M' := by
    intro c hc y hy
    obtain ⟨m, hm, rfl⟩ := hy
    have hmR : (m : G) ∈ R := m.2
    have hcm : c * (m : G) * c⁻¹ ∈ R := hRnorm c hc _ hmR
    have hodd : Odd (orderOf (c * (m : G) * c⁻¹)) := by
      have h1 : orderOf (c * (m : G) * c⁻¹) = orderOf (m : G) := by
        have := MulEquiv.orderOf_eq (MulAut.conj c) (m : G)
        simpa [MulAut.conj_apply] using this
      rw [h1]
      exact hM'odd _ ⟨m, hm, rfl⟩
    have hmem : (⟨c * (m : G) * c⁻¹, hcm⟩ : ↥R) ∈ M := by
      apply hMall
      rw [Subgroup.orderOf_mk]
      exact hodd
    exact ⟨⟨c * (m : G) * c⁻¹, hcm⟩, hmem, rfl⟩
  have hM'N : (M'.subgroupOf C).Normal := ⟨fun n hn g => by
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    simpa using hM'norm (g : C) g.2 (n : G) hn⟩
  have hM'card : Odd (Nat.card ↥(M'.subgroupOf C)) := by
    have h1 : Nat.card ↥(M'.subgroupOf C) = Nat.card ↥M' :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hM'C).toEquiv
    have h2 : Nat.card ↥M' = Nat.card ↥M := Subgroup.card_map_of_injective R.subtype_injective
    rw [h1, h2]
    exact hModd
  have hle : M'.subgroupOf C ≤ pPrimeCore 2 ↥C := by
    unfold pPrimeCore
    exact le_sSup ⟨hM'N, Nat.coprime_two_left.2 hM'card⟩
  rw [hSet.O2prime] at hle
  have hxM : (⟨x, hxR⟩ : ↥R) ∈ M := by
    apply hMall
    rw [Subgroup.orderOf_mk]
    exact hxodd
  have hxM' : x ∈ M' := ⟨⟨x, hxR⟩, hxM, rfl⟩
  have hmem : (⟨x, hxC⟩ : ↥C) ∈ M'.subgroupOf C := Subgroup.mem_subgroupOf.2 hxM'
  have h0 := hle hmem
  rw [Subgroup.mem_bot] at h0
  simpa using congrArg Subtype.val h0

end Rodd

end CFSG.GH74.GLS.Stage4.Rest
