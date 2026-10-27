module

public import CFSG.CGT.Stroth77.Section310CharB

public section

namespace CFSG.CGT.Stroth77

variable {G : Type} [Group G] [Finite G] {F : StrothFrame G} {D : Subgroup G}
  {τ : StrothTypeIndex} {dD : StrothWeakTypeData D τ}

theorem card_le_two_mul_card_inf_of_mem_or {K C : Subgroup G} {y₁ : G} (hy₁ : y₁ ∈ K)
    (hK : ∀ y ∈ K, y ∈ C ∨ y₁⁻¹ * y ∈ C) : Nat.card K ≤ 2 * Nat.card ↥(K ⊓ C) := by
  classical
  let f : K → (K ⊓ C : Subgroup G) ⊕ (K ⊓ C : Subgroup G) := fun y =>
    if hy : (y : G) ∈ C then Sum.inl ⟨y, y.2, hy⟩
    else Sum.inr ⟨y₁⁻¹ * y, K.mul_mem (K.inv_mem hy₁) y.2, (hK y y.2).resolve_left hy⟩
  have hf : Function.Injective f := by
    intro a b hab
    by_cases ha : (a : G) ∈ C <;> by_cases hb : (b : G) ∈ C <;>
      simp only [f, ha, hb, dif_pos, dif_neg, not_false_eq_true, Sum.inl.injEq, Sum.inr.injEq,
        reduceCtorEq, Subtype.mk.injEq, mul_right_inj] at hab
    · exact Subtype.ext (congrArg (fun z : (K ⊓ C : Subgroup G) => (z : G)) hab)
    · exact Subtype.ext (mul_left_cancel
        (congrArg (fun z : (K ⊓ C : Subgroup G) => (z : G)) hab))
  calc Nat.card K ≤ Nat.card ((K ⊓ C : Subgroup G) ⊕ (K ⊓ C : Subgroup G)) :=
        Nat.card_le_card_of_injective f hf
    _ = 2 * Nat.card ↥(K ⊓ C) := by rw [Nat.card_sum]; ring

theorem StrothFrame.IsD.mem_normalizer_omegaIn_of_count (h : F.IsD D dD) (hτ : τ.m ≠ τ.n)
    (hk : ∀ i, 1 ≤ τ.k i) (huvR : ¬ ∀ w ∈ omegaIn 1 D, w * dD.uv = dD.uv * w)
    (h226 : ∀ B : Subgroup G, B ≤ (F.S : Subgroup G) ⊓ Subgroup.normalizer (D : Set G) ⊓
        Subgroup.centralizer ((omegaIn 1 D : Subgroup G) : Set G) →
      (∀ x ∈ (F.S : Subgroup G) ⊓ Subgroup.normalizer (D : Set G) ⊓
          Subgroup.centralizer ((omegaIn 1 D : Subgroup G) : Set G), ∀ b ∈ B,
        x * b * x⁻¹ ∈ B) →
      B ≠ D → (∃ g : G, B = D.map (MulAut.conj g).toMonoidHom) → τ.m = τ.n)
    (hA2 : ∀ x ∈ (F.S : Subgroup G) ⊓ Subgroup.normalizer (D : Set G) ⊓
        Subgroup.centralizer ((omegaIn 1 D : Subgroup G) : Set G),
      2 * Nat.card ↥(D ⊓ Subgroup.centralizer ({dD.uv * x} : Set G)) < Nat.card D)
    (hA4 : ∀ x ∈ (F.S : Subgroup G) ⊓ Subgroup.normalizer (D : Set G) ⊓
        Subgroup.centralizer ((omegaIn 1 D : Subgroup G) : Set G),
      ∀ y ∈ (F.S : Subgroup G) ⊓ Subgroup.normalizer (D : Set G),
      (¬ ∀ w ∈ omegaIn 1 D, w * y = y * w) →
      (¬ ∀ w ∈ omegaIn 1 D, w * (dD.uv⁻¹ * y) = dD.uv⁻¹ * y * w) →
      4 * Nat.card ↥(D ⊓ Subgroup.centralizer ({dD.uv * x} : Set G) ⊓
        Subgroup.centralizer ({y} : Set G)) < Nat.card D)
    (hB2 : ∀ x ∈ (F.S : Subgroup G) ⊓ Subgroup.normalizer (D : Set G) ⊓
        Subgroup.centralizer ((omegaIn 1 D : Subgroup G) : Set G),
      ∀ Q : Subgroup G, Q ≤ (F.S : Subgroup G) ⊓ Subgroup.normalizer (D : Set G) ⊓
        Subgroup.centralizer ((omegaIn 1 D : Subgroup G) : Set G) → ¬ Q ≤ D →
      (∀ a ∈ Q, ∀ b ∈ Q, a * b = b * a) →
      2 * D.relIndex Q * Nat.card ↥(D ⊓ Subgroup.centralizer ({dD.uv * x} : Set G) ⊓
        Subgroup.centralizer (Q : Set G)) < Nat.card D)
    (hB4 : ∀ x ∈ (F.S : Subgroup G) ⊓ Subgroup.normalizer (D : Set G) ⊓
        Subgroup.centralizer ((omegaIn 1 D : Subgroup G) : Set G),
      ∀ Q : Subgroup G, Q ≤ (F.S : Subgroup G) ⊓ Subgroup.normalizer (D : Set G) ⊓
        Subgroup.centralizer ((omegaIn 1 D : Subgroup G) : Set G) → ¬ Q ≤ D →
      (∀ a ∈ Q, ∀ b ∈ Q, a * b = b * a) →
      ∀ y ∈ (F.S : Subgroup G) ⊓ Subgroup.normalizer (D : Set G),
      (¬ ∀ w ∈ omegaIn 1 D, w * y = y * w) →
      (¬ ∀ w ∈ omegaIn 1 D, w * (dD.uv⁻¹ * y) = dD.uv⁻¹ * y * w) →
      4 * D.relIndex Q * Nat.card ↥(D ⊓ Subgroup.centralizer ({dD.uv * x} : Set G) ⊓
        Subgroup.centralizer (Q : Set G) ⊓ Subgroup.centralizer ({y} : Set G)) < Nat.card D)
    {g : G}
    (hgN : g ∈ Subgroup.normalizer
      (((F.S : Subgroup G) ⊓ Subgroup.normalizer (D : Set G) : Subgroup G) : Set G)) :
    g ∈ Subgroup.normalizer ((omegaIn 1 D : Subgroup G) : Set G) := by
  classical
  set N : Subgroup G := (F.S : Subgroup G) ⊓ Subgroup.normalizer (D : Set G) with hN
  set Ω : Subgroup G := omegaIn 1 D with hΩ
  set C : Subgroup G := Subgroup.centralizer (Ω : Set G) with hC
  set R : Subgroup G := N ⊓ C with hRdef
  have hDc : IsMulCommutative D := dD.isMulCommutative
  have hcommD : ∀ x ∈ D, ∀ y ∈ D, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hDc.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  have hDN : D ≤ N := le_inf h.le_S Subgroup.le_normalizer
  have hDC : D ≤ C := fun x hx => Subgroup.mem_centralizer_iff.mpr fun w hw =>
    hcommD _ (omegaIn_le 1 D hw) _ hx
  have hDR : D ≤ R := le_inf hDN hDC
  have huvN : dD.uv ∈ N := ⟨h.uv_eq ▸ F.uv_mem_S, dD.uv_mem⟩
  set K : Subgroup G := D.map (MulAut.conj g).toMonoidHom with hK
  have hmemK : ∀ k ∈ K, ∃ d ∈ D, k = g * d * g⁻¹ := by
    rintro k ⟨d, hd, rfl⟩
    exact ⟨d, hd, rfl⟩
  have hKN : K ≤ N := by
    intro k hk'
    obtain ⟨d, hd, rfl⟩ := hmemK k hk'
    exact (Subgroup.mem_normalizer_iff.mp hgN d).mp (hDN hd)
  have hKc : ∀ a ∈ K, ∀ b ∈ K, a * b = b * a := by
    intro a ha b hb
    obtain ⟨d, hd, rfl⟩ := hmemK a ha
    obtain ⟨d', hd', rfl⟩ := hmemK b hb
    calc g * d * g⁻¹ * (g * d' * g⁻¹) = g * (d * d') * g⁻¹ := by group
      _ = g * (d' * d) * g⁻¹ := by rw [hcommD _ hd _ hd']
      _ = g * d' * g⁻¹ * (g * d * g⁻¹) := by group
  have hKnorm : ∀ x ∈ N, ∀ k ∈ K, x * k * x⁻¹ ∈ K := by
    intro x hx k hk'
    obtain ⟨d, hd, rfl⟩ := hmemK k hk'
    have hxN : g⁻¹ * x * g ∈ N := (Subgroup.mem_normalizer_iff''.mp hgN x).mp hx
    have hd' : (g⁻¹ * x * g) * d * (g⁻¹ * x * g)⁻¹ ∈ D :=
      (Subgroup.mem_normalizer_iff.mp hxN.2 d).mp hd
    refine ⟨_, hd', ?_⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    group
  have hcardK : Nat.card K = Nat.card D :=
    Subgroup.card_map_of_injective (MulAut.conj g).injective
  have hKR : ∀ y ∈ K, ∀ w ∈ Ω, w * y = y * w := by
    by_contra hKR
    obtain ⟨⟨y, hyK, hyR⟩, hcount0⟩ := h.exists_mem_uv_mul_of_normal hk huvR hKN hKnorm hKc hKR
    have hcount : Nat.card K ≤ 4 * Nat.card ↥(K ⊓ C) := hcount0
    set x := dD.uv⁻¹ * y with hx_def
    have hxC : x ∈ C := Subgroup.mem_centralizer_iff.mpr fun w hw => hyR w hw
    have hxR : x ∈ R := ⟨N.mul_mem (N.inv_mem huvN) (hKN hyK), hxC⟩
    have hyx : dD.uv * x = y := by rw [hx_def, mul_inv_cancel_left]
    set Q : Subgroup G := K ⊓ R with hQ
    have hKCR : K ⊓ C = Q := by
      ext z
      exact ⟨fun hz => ⟨hz.1, hKN hz.1, hz.2⟩, fun hz => ⟨hz.1, hz.2.2⟩⟩
    have hQR : Q ≤ R := inf_le_right
    have hQc : ∀ a ∈ Q, ∀ b ∈ Q, a * b = b * a := fun a ha b hb => hKc a ha.1 b hb.1
    have e1 := Subgroup.relIndex_mul_card (H := D) (K := Q)
    have hDQ : D ⊓ Q = K ⊓ D := by
      ext z
      exact ⟨fun hz => ⟨hz.2.1, hz.1⟩, fun hz => ⟨hz.2, hz.1, hDR hz.2⟩⟩
    rw [hDQ] at e1
    have hKD : K ⊓ D ≤ D ⊓ Subgroup.centralizer ({dD.uv * x} : Set G) ⊓
        Subgroup.centralizer (Q : Set G) := by
      intro z hz
      refine ⟨⟨hz.2, Subgroup.mem_centralizer_iff.mpr ?_⟩, Subgroup.mem_centralizer_iff.mpr ?_⟩
      · rintro _ rfl
        rw [hyx]
        exact hKc _ hyK _ hz.1
      · intro q hq
        exact hKc _ hq.1 _ hz.1
    have hKDx : K ⊓ D ≤ D ⊓ Subgroup.centralizer ({dD.uv * x} : Set G) := fun z hz =>
      (hKD hz).1
    have hQD : Q ≤ D → Nat.card Q ≤ Nat.card ↥(K ⊓ D) := fun hc =>
      Subgroup.card_le_of_le fun z hz => ⟨hz.1, hc hz⟩
    by_cases hy₂ : ∃ y₂ ∈ K, (¬ ∀ w ∈ Ω, w * y₂ = y₂ * w) ∧
        (¬ ∀ w ∈ Ω, w * (dD.uv⁻¹ * y₂) = dD.uv⁻¹ * y₂ * w)
    · obtain ⟨y₂, hy₂K, hy₂C, hy₂C'⟩ := hy₂
      have hKD2 : K ⊓ D ≤ D ⊓ Subgroup.centralizer ({dD.uv * x} : Set G) ⊓
          Subgroup.centralizer (Q : Set G) ⊓ Subgroup.centralizer ({y₂} : Set G) :=
        fun z hz => ⟨hKD hz, Subgroup.mem_centralizer_iff.mpr fun _ hw => by
          rw [Set.mem_singleton_iff.mp hw]
          exact hKc _ hy₂K _ hz.1⟩
      rw [hKCR] at hcount
      by_cases hcase : Q ≤ D
      · have hKD3 : K ⊓ D ≤ D ⊓ Subgroup.centralizer ({dD.uv * x} : Set G) ⊓
            Subgroup.centralizer ({y₂} : Set G) :=
          fun z hz => ⟨(hKD2 hz).1.1, (hKD2 hz).2⟩
        have hb := hA4 x hxR y₂ (hKN hy₂K) hy₂C hy₂C'
        have h1 := Subgroup.card_le_of_le hKD3
        have h2 := hQD hcase
        omega
      · have hb := hB4 x hxR Q hQR hcase hQc y₂ (hKN hy₂K) hy₂C hy₂C'
        have h1 := Subgroup.card_le_of_le hKD2
        have h2 : Nat.card K ≤ 4 * (D.relIndex Q * Nat.card ↥(K ⊓ D)) := by
          rw [e1]; exact hcount
        have h3 : 4 * (D.relIndex Q * Nat.card ↥(K ⊓ D)) ≤ 4 * D.relIndex Q *
            Nat.card ↥(D ⊓ Subgroup.centralizer ({dD.uv * x} : Set G) ⊓
              Subgroup.centralizer (Q : Set G) ⊓ Subgroup.centralizer ({y₂} : Set G)) := by
          rw [← mul_assoc]
          exact Nat.mul_le_mul_left _ h1
        omega
    ·
      have hmem : ∀ z ∈ K, z ∈ C ∨ y⁻¹ * z ∈ C := by
        intro z hz
        by_cases hzC : z ∈ C
        · exact Or.inl hzC
        refine Or.inr ?_
        have hz' : ∀ w ∈ Ω, w * (dD.uv⁻¹ * z) = dD.uv⁻¹ * z * w := by
          by_contra hz'
          exact hy₂ ⟨z, hz, fun hzw => hzC (Subgroup.mem_centralizer_iff.mpr hzw), hz'⟩
        have hzC' : dD.uv⁻¹ * z ∈ C := Subgroup.mem_centralizer_iff.mpr hz'
        have e2 : y⁻¹ * z = x⁻¹ * (dD.uv⁻¹ * z) := by rw [hx_def]; group
        rw [e2]
        exact C.mul_mem (C.inv_mem hxC) hzC'
      have hcount2 := card_le_two_mul_card_inf_of_mem_or hyK hmem
      rw [hKCR] at hcount2
      by_cases hcase : Q ≤ D
      · have hb := hA2 x hxR
        have h1 := Subgroup.card_le_of_le hKDx
        have h2 := hQD hcase
        omega
      · have hb := hB2 x hxR Q hQR hcase hQc
        have h1 := Subgroup.card_le_of_le hKD
        have h2 : Nat.card K ≤ 2 * (D.relIndex Q * Nat.card ↥(K ⊓ D)) := by
          rw [e1]; exact hcount2
        have h3 : 2 * (D.relIndex Q * Nat.card ↥(K ⊓ D)) ≤ 2 * D.relIndex Q *
            Nat.card ↥(D ⊓ Subgroup.centralizer ({dD.uv * x} : Set G) ⊓
              Subgroup.centralizer (Q : Set G)) := by
          rw [← mul_assoc]
          exact Nat.mul_le_mul_left _ h1
        omega
  have hKeq : K = D := by
    by_contra hne
    refine hτ (h226 K (fun y hy => ⟨hKN hy, Subgroup.mem_centralizer_iff.mpr
      fun w hw => hKR y hy w hw⟩) (fun x hx b hb => hKnorm x hx.1 b hb) hne ⟨g, rfl⟩)
  have hgD : g ∈ Subgroup.normalizer (D : Set G) := by
    refine Subgroup.mem_normalizer_iff.mpr fun x => ⟨fun hx => ?_, fun hx => ?_⟩
    · rw [← hKeq]; exact ⟨x, hx, rfl⟩
    · rw [← hKeq] at hx
      obtain ⟨d, hd, hdx⟩ := hmemK _ hx
      have : x = d := by simpa using hdx
      exact this ▸ hd
  exact normalizer_le_normalizer_omegaIn D hgD

end CFSG.CGT.Stroth77
