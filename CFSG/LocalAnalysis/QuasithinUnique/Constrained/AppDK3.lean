module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.AppDK2

public section

namespace CFSG.QuasithinUnique.AppD

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.QuasithinUnique.DoubleA3

variable {G : Type} [Group G] [Finite G] {T M H S L : Subgroup G} {s : G}

namespace A3x

variable {h : A3A3 T M H S L s} (sp : Spec h)

theorem fix_le {a : G} (ha : a ∈ baum S) (ha1 : a ∉ Subgroup.centralizer (blockU L : Set G))
    (ha2 : a ∉ Subgroup.centralizer (blockU2 L s : Set G)) {x : G}
    (hx : x ∈ blockU L ⊔ blockU2 L s) (hxa : x * a = a * x) :
    x ∈ Subgroup.zpowers sp.z₁ ⊔ Subgroup.zpowers sp.z₂ := by
  obtain ⟨u₁, hu₁, u₂, hu₂, rfl⟩ := C5.mem_sup_of_commute sp.kp.comm hx
  have hv₁ : a * u₁ * a⁻¹ ∈ blockU L := (Subgroup.mem_normalizer_iff.1 (B_le_N_U₁ h ha) u₁).1 hu₁
  have hv₂ : a * u₂ * a⁻¹ ∈ blockU2 L s :=
    (Subgroup.mem_normalizer_iff.1 (B_le_N_U₂ h ha) u₂).1 hu₂
  have hprod : (a * u₁ * a⁻¹) * (a * u₂ * a⁻¹) = u₁ * u₂ := by
    calc (a * u₁ * a⁻¹) * (a * u₂ * a⁻¹) = a * (u₁ * u₂) * a⁻¹ := by group
      _ = u₁ * u₂ := by rw [← hxa]; group
  have key : u₁⁻¹ * (a * u₁ * a⁻¹) = u₂ * (a * u₂ * a⁻¹)⁻¹ := by
    calc u₁⁻¹ * (a * u₁ * a⁻¹) = u₁⁻¹ * ((a * u₁ * a⁻¹) * (a * u₂ * a⁻¹)) * (a * u₂ * a⁻¹)⁻¹ := by
          group
      _ = u₂ * (a * u₂ * a⁻¹)⁻¹ := by rw [hprod]; group
  have hl : u₁⁻¹ * (a * u₁ * a⁻¹) ∈ blockU L := mul_mem (inv_mem hu₁) hv₁
  have hr : u₂ * (a * u₂ * a⁻¹)⁻¹ ∈ blockU2 L s := mul_mem hu₂ (inv_mem hv₂)
  have h1 : u₁⁻¹ * (a * u₁ * a⁻¹) = 1 := sp.kp.cross hl hr key
  have h2 : u₂ * (a * u₂ * a⁻¹)⁻¹ = 1 := by rw [← key]; exact h1
  have e1 : a * u₁ * a⁻¹ = u₁ := by
    have := congrArg (fun y => u₁ * y) h1
    simpa using this
  have e2 : a * u₂ * a⁻¹ = u₂ := (mul_inv_eq_one.1 h2).symm
  have c1 : u₁ * a = a * u₁ := by
    calc u₁ * a = (a * u₁ * a⁻¹) * a := by rw [e1]
      _ = a * u₁ := by group
  have c2 : u₂ * a = a * u₂ := by
    calc u₂ * a = (a * u₂ * a⁻¹) * a := by rw [e2]
      _ = a * u₂ := by group
  exact mul_mem (Subgroup.mem_sup_left ((sp.cent₁ a ha ha1 u₁ hu₁).2 c1))
    (Subgroup.mem_sup_right ((sp.cent₂ a ha ha2 u₂ hu₂).2 c2))

theorem card_zpowers_sup : Nat.card ↥(Subgroup.zpowers sp.z₁ ⊔ Subgroup.zpowers sp.z₂) = 4 := by
  have hc : ∀ a ∈ Subgroup.zpowers sp.z₁, ∀ b ∈ Subgroup.zpowers sp.z₂, a * b = b * a := by
    intro a ha b hb
    obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.1 ha
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 hb
    exact ((Commute.zpow_zpow (sp.kp.comm _ sp.kp.hz₁ _ sp.kp.hz₂) m n)).eq
  have h := B2F.card_sup_mul_card_inf_of_commute hc
  have hinf : Subgroup.zpowers sp.z₁ ⊓ Subgroup.zpowers sp.z₂ = ⊥ := by
    refine eq_bot_iff.2 fun y hy => ?_
    have h1 : y ∈ blockU L := (Subgroup.zpowers_le.2 sp.kp.hz₁) hy.1
    have h2 : y ∈ blockU2 L s := (Subgroup.zpowers_le.2 sp.kp.hz₂) hy.2
    exact Subgroup.mem_bot.2 (sp.kp.cross h1 h2 rfl)
  have c1 : Nat.card ↥(Subgroup.zpowers sp.z₁) = 2 := by
    rw [Nat.card_zpowers, orderOf_eq_prime (sp.kp.sq₁ _ sp.kp.hz₁) sp.kp.z₁_ne]
  have c2 : Nat.card ↥(Subgroup.zpowers sp.z₂) = 2 := by
    rw [Nat.card_zpowers, orderOf_eq_prime (sp.kp.sq₂ _ sp.kp.hz₂) sp.kp.z₂_ne]
  rw [hinf, Subgroup.card_bot, c1, c2] at h
  omega

include h in
theorem exists_max_not_le_cent₁ :
    ∃ A, IsMaxElemAbelian S A ∧ ¬ A ≤ Subgroup.centralizer (blockU L : Set G) := by
  by_contra hcon
  push Not at hcon
  have : thompsonJ S ≤ Subgroup.centralizer (blockU L : Set G) :=
    iSup₂_le fun A hA => hcon A hA
  exact C56.a3_not_le_centralizer h.isShort h.a3 h.cs.thompson this

include h in
theorem U_le_S : blockU L ⊔ blockU2 L s ≤ S :=
  sup_le ((U₁_le_B h).trans (baum_le_S' S)) ((U₂_le_B h).trans (baum_le_S' S))

include sp in
theorem Q_ne : baum S ⊓ Subgroup.centralizer (blockU L : Set G) ≠
    baum S ⊓ Subgroup.centralizer (blockU2 L s : Set G) := by
  intro hQ
  obtain ⟨A, hA, hAc⟩ := exists_max_not_le_cent₁ (h := h)
  have hAB : A ≤ baum S := (GammaExtra.le_thompsonJ hA).trans (C5.thompsonJ_le_baum' S)
  obtain ⟨a, haA, hac⟩ : ∃ a ∈ A, a ∉ Subgroup.centralizer (blockU L : Set G) := by
    by_contra hcon
    push Not at hcon
    exact hAc fun x hx => hcon x hx
  have haB : a ∈ baum S := hAB haA
  have hac2 : a ∉ Subgroup.centralizer (blockU2 L s : Set G) := by
    intro hc
    have : a ∈ baum S ⊓ Subgroup.centralizer (blockU2 L s : Set G) := ⟨haB, hc⟩
    rw [← hQ] at this
    exact hac this.2
  set U := blockU L ⊔ blockU2 L s with hU
  set K₀ := A ⊓ Subgroup.centralizer (U : Set G) with hK₀
  have hK₀eq : K₀ = Subgroup.centralizer (blockU L : Set G) ⊓ A := by
    ext x
    constructor
    · rintro ⟨hxA, hxC⟩
      exact ⟨Subgroup.centralizer_le (SetLike.coe_subset_coe.2 le_sup_left) hxC, hxA⟩
    · rintro ⟨hxC, hxA⟩
      refine ⟨hxA, Subgroup.mem_centralizer_iff.2 fun u hu => ?_⟩
      obtain ⟨u₁, hu₁, u₂, hu₂, rfl⟩ := C5.mem_sup_of_commute sp.kp.comm hu
      have hxB : x ∈ baum S := hAB hxA
      have hxC2 : x ∈ Subgroup.centralizer (blockU2 L s : Set G) := by
        have : x ∈ baum S ⊓ Subgroup.centralizer (blockU L : Set G) := ⟨hxB, hxC⟩
        rw [hQ] at this
        exact this.2
      have c1 := Subgroup.mem_centralizer_iff.1 hxC u₁ hu₁
      have c2 := Subgroup.mem_centralizer_iff.1 hxC2 u₂ hu₂
      calc u₁ * u₂ * x = u₁ * (u₂ * x) := by group
        _ = u₁ * (x * u₂) := by rw [c2]
        _ = (u₁ * x) * u₂ := by group
        _ = (x * u₁) * u₂ := by rw [c1]
        _ = x * (u₁ * u₂) := by group
  have hB2 : (Subgroup.centralizer (blockU L : Set G)).relIndex (baum S) = 2 :=
    (Subgroup.inf_relIndex_left (H := baum S)
      (K := Subgroup.centralizer (blockU L : Set G))).symm.trans sp.idx₁
  have hrel : (Subgroup.centralizer (blockU L : Set G)).relIndex A = 2 := by
    have h1 : (Subgroup.centralizer (blockU L : Set G)).relIndex A ≠ 1 := fun h1 =>
      hAc (Subgroup.relIndex_eq_one.1 h1)
    have h2 : (Subgroup.centralizer (blockU L : Set G)).relIndex A ≤ 2 := by
      have := Subgroup.relIndex_le_of_le_right (H := Subgroup.centralizer (blockU L : Set G)) hAB
        (by rw [hB2]; norm_num)
      rwa [hB2] at this
    have h3 : (Subgroup.centralizer (blockU L : Set G)).relIndex A ≠ 0 := by
      intro h0
      have := Subgroup.relIndex_mul_card (H := Subgroup.centralizer (blockU L : Set G)) (K := A)
      rw [h0, zero_mul] at this
      exact absurd this.symm Nat.card_pos.ne'
    omega
  have hcardA : Nat.card A = 2 * Nat.card ↥K₀ := by
    have := Subgroup.relIndex_mul_card (H := Subgroup.centralizer (blockU L : Set G)) (K := A)
    rw [hrel, ← hK₀eq] at this
    exact this.symm
  have hK₀e : IsElemAbelian 2 K₀ := B2F.isElemAbelian_mono inf_le_left hA.2.1
  have hcomm : ∀ k ∈ K₀, ∀ u ∈ U, k * u = u * k := fun k hk u hu =>
    (Subgroup.mem_centralizer_iff.1 hk.2 u hu).symm
  have hAU : IsElemAbelian 2 (K₀ ⊔ U) :=
    B2F.isElemAbelian_sup_of_commute hK₀e sp.kp.elemAbelian_sup hcomm
  have hAUS : K₀ ⊔ U ≤ S := sup_le (inf_le_left.trans hA.1) (U_le_S (h := h))
  have hle : Nat.card ↥(K₀ ⊔ U) ≤ Nat.card A := hA.2.2 _ hAUS hAU
  have hprod := B2F.card_sup_mul_card_inf_of_commute hcomm
  rw [sp.kp.card_sup] at hprod
  have hinf : Nat.card ↥(K₀ ⊓ U) ≤ 4 := by
    rw [← card_zpowers_sup sp]
    refine Subgroup.card_le_of_le fun x hx => ?_
    exact fix_le sp haB hac hac2 hx.2
      (B2F.isElemAbelian_comm hA.2.1 hx.1.1 haA)
  have hKpos : 0 < Nat.card ↥K₀ := Nat.card_pos
  have h5 := Nat.mul_le_mul hle hinf
  nlinarith

include sp in
theorem exists_swap_elements :
    (∃ b ∈ baum S, b ∉ Subgroup.centralizer (blockU L : Set G) ∧
        b ∈ Subgroup.centralizer (blockU2 L s : Set G)) ∧
      ∃ b ∈ baum S, b ∈ Subgroup.centralizer (blockU L : Set G) ∧
        b ∉ Subgroup.centralizer (blockU2 L s : Set G) := by
  have hne := Q_ne sp
  have hcard : ∀ Q : Subgroup G, Q ≤ baum S → Q.relIndex (baum S) = 2 →
      2 * Nat.card ↥Q = Nat.card (baum S) := by
    intro Q hQ hrel
    have := Subgroup.relIndex_mul_card (H := Q) (K := baum S)
    rw [inf_eq_left.2 hQ, hrel] at this
    exact this
  have c1 := hcard _ inf_le_left sp.idx₁
  have c2 := hcard _ inf_le_left sp.idx₂
  constructor
  · by_contra hcon
    push Not at hcon
    apply hne
    symm
    refine Subgroup.eq_of_le_of_card_ge (fun b hb => ⟨hb.1, ?_⟩) (by omega)
    by_contra hb1
    exact hcon b hb.1 hb1 hb.2
  · by_contra hcon
    push Not at hcon
    apply hne
    exact Subgroup.eq_of_le_of_card_ge (fun b hb => ⟨hb.1, hcon b hb.1 hb.2⟩) (by omega)

end A3x

end CFSG.QuasithinUnique.AppD
