module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10FSimple

public section

namespace CFSG.LocalAnalysis.GLTheoremA.Y10F

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB

theorem exists_two_lift {K S : Type} [Group K] [Group S] [Finite K] (π : K →* S)
    (hπ : Function.Surjective π) {s : S} {b : ℕ} (hs : s ^ (2 ^ b) = 1) :
    ∃ x : K, π x = s ∧ ∃ a : ℕ, x ^ (2 ^ a) = 1 := by
  obtain ⟨x₀, hx₀⟩ := hπ s
  have hn : orderOf x₀ ≠ 0 := (orderOf_pos x₀).ne'
  obtain ⟨a, m, hm, hnm⟩ := Nat.exists_eq_two_pow_mul_odd hn
  have hco : Nat.Coprime (2 ^ a) m := Nat.Coprime.pow_left a ((Nat.coprime_two_left).2 hm)
  obtain ⟨k, hk1, hk2⟩ := Nat.chineseRemainder hco 1 0
  refine ⟨x₀ ^ k, ?_, a, ?_⟩
  · have h1 : s ^ (orderOf x₀) = 1 := by rw [← hx₀, ← map_pow, pow_orderOf_eq_one, map_one]
    have h2 : orderOf s ∣ 2 ^ b := orderOf_dvd_of_pow_eq_one hs
    have h3 : orderOf s ∣ orderOf x₀ := orderOf_dvd_of_pow_eq_one h1
    have h4 : orderOf s ∣ 2 ^ a := by
      have h5 : orderOf s ∣ 2 ^ a * m := hnm ▸ h3
      have hc : Nat.Coprime (orderOf s) m := by
        obtain ⟨c, hc, hcc⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 h2
        rw [hcc]
        exact Nat.Coprime.pow_left c ((Nat.coprime_two_left).2 hm)
      exact hc.dvd_of_dvd_mul_right h5
    rw [map_pow, hx₀]
    have : k ≡ 1 [MOD orderOf s] := (hk1.of_dvd h4)
    rw [pow_eq_pow_iff_modEq.2 (show k ≡ 1 [MOD orderOf s] from this), pow_one]
  · have : orderOf x₀ ∣ k * 2 ^ a := by
      rw [hnm, mul_comm k, mul_comm (2 ^ a) m]
      exact Nat.mul_dvd_mul (Nat.modEq_zero_iff_dvd.1 hk2) (dvd_refl _) |>.trans (by simp [mul_comm])
    rw [← pow_mul]
    exact orderOf_dvd_iff_pow_eq_one.1 this

@[expose] def Z2 (K : Type) [Group K] : Subgroup K where
  carrier := {z | z ∈ Subgroup.center K ∧ ∃ k : ℕ, z ^ (2 ^ k) = 1}
  one_mem' := ⟨Subgroup.one_mem _, 0, by simp⟩
  mul_mem' := by
    rintro a b ⟨ha, i, hai⟩ ⟨hb, j, hbj⟩
    refine ⟨Subgroup.mul_mem _ ha hb, i + j, ?_⟩
    have hc : Commute a b := (Subgroup.mem_center_iff.1 ha b).symm
    rw [hc.mul_pow, pow_add, pow_mul, hai, one_pow, mul_comm (2 ^ i) (2 ^ j), pow_mul, hbj, one_pow,
      mul_one]
  inv_mem' := by
    rintro a ⟨ha, i, hai⟩
    exact ⟨Subgroup.inv_mem _ ha, i, by rw [inv_pow, hai, inv_one]⟩

theorem Z2_le_center (K : Type) [Group K] : Z2 K ≤ Subgroup.center K := fun _ h => h.1

instance Z2_normal (K : Type) [Group K] : (Z2 K).Normal := by
  refine ⟨fun n hn g => ?_⟩
  have : g * n * g⁻¹ = n := by
    have := Subgroup.mem_center_iff.1 hn.1 g
    calc g * n * g⁻¹ = n * g * g⁻¹ := by rw [this]
      _ = n := by group
  rw [this]; exact hn

theorem map_Z2 (K : Type) [Group K] (σ : MulAut K) : (Z2 K).map σ.toMonoidHom = Z2 K := by
  have hle : ∀ τ : MulAut K, (Z2 K).map τ.toMonoidHom ≤ Z2 K := by
    intro τ
    rintro _ ⟨z, ⟨hz, k, hk⟩, rfl⟩
    refine ⟨?_, k, ?_⟩
    · rw [Subgroup.mem_center_iff]
      intro g
      obtain ⟨g', rfl⟩ := τ.surjective g
      have h1 := Subgroup.mem_center_iff.1 hz g'
      show τ g' * τ z = τ z * τ g'
      calc τ g' * τ z = τ (g' * z) := (map_mul τ g' z).symm
        _ = τ (z * g') := by rw [h1]
        _ = τ z * τ g' := map_mul τ z g'
    · rw [← map_pow]
      show τ (z ^ (2 ^ k)) = 1
      rw [hk, map_one]
  refine le_antisymm (hle σ) ?_
  have h := Subgroup.map_mono (f := σ.toMonoidHom) (hle σ⁻¹)
  rw [Subgroup.map_map] at h
  have hid : σ.toMonoidHom.comp σ⁻¹.toMonoidHom = MonoidHom.id K := by
    ext x; simp
  rwa [hid, Subgroup.map_id] at h

theorem isPGroup_Z2 (K : Type) [Group K] : IsPGroup 2 ↥(Z2 K) := by
  intro z
  obtain ⟨k, hk⟩ := z.2.2
  exact ⟨k, Subtype.ext (by simpa using hk)⟩

theorem not_dvd_card_Z2 (K : Type) [Group K] [Finite K] {q : ℕ} (hq : q.Prime) (hq2 : q ≠ 2) :
    ¬ q ∣ Nat.card (Z2 K) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨j, hj⟩ := (isPGroup_Z2 K).exists_card_eq
  rw [hj]
  intro hd
  exact hq2 ((Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).1 (hq.dvd_of_dvd_pow hd))

theorem exists_fixed_two_lift {K : Type} [Group K] [Finite K] {q : ℕ} (hq : q.Prime) (hq2 : q ≠ 2)
    {F : Subgroup (MulAut K)} (hF : IsPGroup q ↥F) {s : K ⧸ Subgroup.center K} {b : ℕ}
    (hs : s ^ (2 ^ b) = 1) (hfix : ∀ f ∈ F, centerQuotAut K f s = s) :
    ∃ x : K, (QuotientGroup.mk x : K ⧸ Subgroup.center K) = s ∧ ∀ f ∈ F, f x = x := by
  haveI : Fact q.Prime := ⟨hq⟩
  obtain ⟨x₁, hx₁s, a, hx₁a⟩ := exists_two_lift (QuotientGroup.mk' (Subgroup.center K))
    (QuotientGroup.mk'_surjective _) hs
  have hρ : ∀ y : MulAut K, (Z2 K).map (MonoidHom.id (MulAut K) y).toMonoidHom = Z2 K :=
    fun y => map_Z2 K y
  have hx : ∀ f ∈ F, quotAutHom (Z2 K) (MonoidHom.id (MulAut K)) hρ f
      (QuotientGroup.mk x₁) = QuotientGroup.mk x₁ := by
    intro f hf
    rw [quotAutHom_mk]
    show (QuotientGroup.mk (f x₁) : K ⧸ Z2 K) = QuotientGroup.mk x₁
    have hz : x₁⁻¹ * f x₁ ∈ Subgroup.center K := by
      have h1 : (QuotientGroup.mk' (Subgroup.center K)) (x₁⁻¹ * f x₁) = 1 := by
        rw [map_mul, map_inv]
        have h2 : (QuotientGroup.mk' (Subgroup.center K)) (f x₁) =
            centerQuotAut K f (QuotientGroup.mk' (Subgroup.center K) x₁) :=
          (centerQuotAut_mk K f x₁).symm
        rw [h2, hx₁s, hfix f hf, inv_mul_cancel]
      exact (QuotientGroup.eq_one_iff _).1 h1
    have hc : Commute x₁ (x₁⁻¹ * f x₁) := Subgroup.mem_center_iff.1 hz x₁
    have hz2 : (x₁⁻¹ * f x₁) ^ (2 ^ a) = 1 := by
      have h3 : (x₁ * (x₁⁻¹ * f x₁)) ^ (2 ^ a) = 1 := by
        have : x₁ * (x₁⁻¹ * f x₁) = f x₁ := by group
        rw [this, ← map_pow, hx₁a, map_one]
      rw [hc.mul_pow, hx₁a, one_mul] at h3
      exact h3
    rw [QuotientGroup.eq]
    have hmem : x₁⁻¹ * f x₁ ∈ Z2 K := ⟨hz, a, hz2⟩
    have : (f x₁)⁻¹ * x₁ = (x₁⁻¹ * f x₁)⁻¹ := by group
    rw [this]
    exact (Z2 K).inv_mem hmem
  obtain ⟨k, hk1, hk2⟩ := exists_fixed_lift (Z2 K) (MonoidHom.id (MulAut K)) hρ hF
    (not_dvd_card_Z2 K hq hq2) (QuotientGroup.mk x₁) hx
  refine ⟨k, ?_, fun f hf => hk2 f hf⟩
  have h1 : k⁻¹ * x₁ ∈ Z2 K := QuotientGroup.eq.1 hk1
  have h2 : (QuotientGroup.mk' (Subgroup.center K)) (k⁻¹ * x₁) = 1 :=
    (QuotientGroup.eq_one_iff _).2 (Z2_le_center K h1)
  rw [map_mul, map_inv, hx₁s] at h2
  exact inv_mul_eq_one.1 h2

@[expose] def SeitzSimpleStmt (S : Type) [Group S] [Finite S] : Prop :=
  ∀ q : ℕ, q.Prime → q ≠ 2 → ∀ E : Subgroup (MulAut S), IsElemAbelian q E → E ≠ ⊥ →
    Nat.card E ≤ q ^ 3 →
    (∃ U : Subgroup S, U ≠ ⊥ ∧ IsPGroup 2 ↥U ∧ ∀ φ ∈ E, ∀ u ∈ U, φ u ∈ U) →
    (⨆ (F : Subgroup (MulAut S)) (_ : F ≤ E ∧ F.relIndex E = q),
      CFSG.GH74.GLS.oPrimeResidualOf 2 (CFSG.LieType.Seitz.fixedPoints F)) = ⊤

theorem isElemAbelian_map_hom {X Y : Type} [Group X] [Group Y] {q : ℕ} (f : X →* Y) {E : Subgroup X}
    (hE : IsElemAbelian q E) : IsElemAbelian q (E.map f) := by
  refine ⟨⟨⟨fun a b => Subtype.ext ?_⟩⟩, fun x hx => ?_⟩
  · obtain ⟨a', ha', ha⟩ := Subgroup.mem_map.1 a.2
    obtain ⟨b', hb', hb⟩ := Subgroup.mem_map.1 b.2
    show (a : Y) * b = b * a
    rw [← ha, ← hb, ← map_mul, ← map_mul, isElemAbelian_commute hE ha' hb']
  · obtain ⟨x', hx', rfl⟩ := Subgroup.mem_map.1 hx
    rw [← map_pow, hE.2 x' hx', map_one]

theorem eq_one_of_trivial_centerQuot {K : Type} [Group K] (hperf : commutator K = ⊤) (σ : MulAut K)
    (h : centerQuotAut K σ = 1) : σ = 1 := by
  have hz : ∀ k : K, k⁻¹ * σ k ∈ Subgroup.center K := by
    intro k
    have h1 : (QuotientGroup.mk' (Subgroup.center K)) (σ k) = QuotientGroup.mk' (Subgroup.center K) k := by
      have := centerQuotAut_mk K σ k
      rw [h] at this
      exact this.symm
    have h2 : (QuotientGroup.mk' (Subgroup.center K)) (k⁻¹ * σ k) = 1 := by
      rw [map_mul, map_inv, h1, inv_mul_cancel]
    exact (QuotientGroup.eq_one_iff _).1 h2
  let φ : K →* K :=
    { toFun := fun k => k⁻¹ * σ k
      map_one' := by simp
      map_mul' := fun a b => by
        have hc := Subgroup.mem_center_iff.1 (hz a) b⁻¹
        calc (a * b)⁻¹ * σ (a * b) = b⁻¹ * (a⁻¹ * σ a) * σ b := by rw [map_mul]; group
          _ = (a⁻¹ * σ a) * (b⁻¹ * σ b) := by rw [hc]; group }
  have hφ : ∀ k, φ k = k⁻¹ * σ k := fun k => rfl
  have hle : commutator K ≤ φ.ker := by
    rw [commutator_def, Subgroup.commutator_le]
    intro a _ b _
    have h : φ b * φ a = φ a * φ b := Subgroup.mem_center_iff.mp (hz a) (φ b)
    simp only [commutatorElement_def, MonoidHom.mem_ker, map_mul, map_inv]
    calc φ a * φ b * (φ a)⁻¹ * (φ b)⁻¹ = φ b * φ a * (φ a)⁻¹ * (φ b)⁻¹ := by rw [h]
      _ = 1 := by group
  rw [hperf] at hle
  ext k
  have h3 : k⁻¹ * σ k = 1 := hle (Subgroup.mem_top k)
  exact (inv_mul_eq_one.1 h3).symm

theorem comm_mul_central_left {K : Type} [Group K] {z : K} (hz : z ∈ Subgroup.center K) (x y : K) :
    (x * z) * y * (x * z)⁻¹ * y⁻¹ = x * y * x⁻¹ * y⁻¹ := by
  have h := Subgroup.mem_center_iff.1 hz y
  calc (x * z) * y * (x * z)⁻¹ * y⁻¹ = x * (z * y) * z⁻¹ * x⁻¹ * y⁻¹ := by group
    _ = x * (y * z) * z⁻¹ * x⁻¹ * y⁻¹ := by rw [h]
    _ = x * y * x⁻¹ * y⁻¹ := by group

theorem comm_mul_central_right {K : Type} [Group K] {z : K} (hz : z ∈ Subgroup.center K) (x y : K) :
    x * (y * z) * x⁻¹ * (y * z)⁻¹ = x * y * x⁻¹ * y⁻¹ := by
  have h := Subgroup.mem_center_iff.1 hz x⁻¹
  calc x * (y * z) * x⁻¹ * (y * z)⁻¹ = x * y * (z * x⁻¹) * z⁻¹ * y⁻¹ := by group
    _ = x * y * (x⁻¹ * z) * z⁻¹ * y⁻¹ := by rw [h]
    _ = x * y * x⁻¹ * y⁻¹ := by group

theorem eq_top_of_sup_center {K : Type} [Group K] (hperf : commutator K = ⊤) {Θ : Subgroup K}
    (hΘ : ∀ k : K, ∃ θ ∈ Θ, θ⁻¹ * k ∈ Subgroup.center K) : Θ = ⊤ := by
  rw [eq_top_iff, ← hperf, commutator_def, Subgroup.commutator_le]
  intro a _ b _
  obtain ⟨θa, hθa, hza⟩ := hΘ a
  obtain ⟨θb, hθb, hzb⟩ := hΘ b
  have ha : a = θa * (θa⁻¹ * a) := by group
  have hb : b = θb * (θb⁻¹ * b) := by group
  rw [commutatorElement_def, ha, hb, comm_mul_central_left hza, comm_mul_central_right hzb]
  have := Θ.mul_mem (Θ.mul_mem (Θ.mul_mem hθa hθb) (Θ.inv_mem hθa)) (Θ.inv_mem hθb)
  exact this

theorem seitzGen_of_simple (C : ∀ (S : Type) [Group S], Prop)
    (hC : ∀ (K : Type) [Group K] [Finite K], HasLabel K (fun _ => True) → C (K ⧸ Subgroup.center K))
    (hS : ∀ (S : Type) [Group S] [Finite S], C S → SeitzSimpleStmt S) : SeitzGen := by
  intro K _ _ hK q hq hq2 E hE hcard hT
  obtain ⟨T, hT2, hTc, hTinv⟩ := hT
  haveI : Fact q.Prime := ⟨hq⟩
  obtain ⟨hperf, -⟩ := hasLabel_isQuasisimple hK
  have hfinj : Function.Injective (centerQuotAut K) :=
    (injective_iff_map_eq_one _).2 fun σ h => eq_one_of_trivial_centerQuot hperf σ h
  by_cases hE0 : E = ⊥
  · refine eq_top_iff.2 (le_trans ?_ (le_iSup₂_of_le E ⟨le_rfl, ?_⟩ le_rfl))
    · intro k _
      rw [mem_centFixAut]
      intro φ hφ
      rw [hE0, Subgroup.mem_bot] at hφ
      rw [hφ]
      rfl
    · rw [Subgroup.relIndex_self]
      exact hq.one_lt.le
  · have hEtel : IsElemAbelian q (E.map (centerQuotAut K)) := isElemAbelian_map_hom _ hE
    have hEt0 : E.map (centerQuotAut K) ≠ ⊥ := by
      intro h
      apply hE0
      rw [eq_bot_iff]
      intro σ hσ
      have h1 : centerQuotAut K σ ∈ E.map (centerQuotAut K) := Subgroup.mem_map_of_mem _ hσ
      rw [h, Subgroup.mem_bot, ← map_one (centerQuotAut K)] at h1
      exact Subgroup.mem_bot.2 (hfinj h1)
    have hU : ∃ U : Subgroup (K ⧸ Subgroup.center K), U ≠ ⊥ ∧ IsPGroup 2 ↥U ∧
        ∀ φ ∈ E.map (centerQuotAut K), ∀ u ∈ U, φ u ∈ U := by
      refine ⟨T.map (QuotientGroup.mk' (Subgroup.center K)), ?_,
        isPGroup_map_hom _ hT2, ?_⟩
      · intro h
        apply hTc
        intro t ht
        have h1 : QuotientGroup.mk' (Subgroup.center K) t ∈
            T.map (QuotientGroup.mk' (Subgroup.center K)) := Subgroup.mem_map_of_mem _ ht
        rw [h, Subgroup.mem_bot] at h1
        exact (QuotientGroup.eq_one_iff _).1 h1
      · rintro _ ⟨σ, hσ, rfl⟩ _ ⟨t, ht, rfl⟩
        exact ⟨σ t, hTinv σ hσ t ht, (centerQuotAut_mk K σ t).symm⟩
    have hcardt : Nat.card (E.map (centerQuotAut K)) ≤ q ^ 3 :=
      (card_map_le_of_finite (centerQuotAut K) E).trans hcard
    have hmain := hS (K ⧸ Subgroup.center K) (hC K hK) q hq hq2 _ hEtel hEt0 hcardt hU
    have hle : (⨆ (Ft : Subgroup (MulAut (K ⧸ Subgroup.center K)))
        (_ : Ft ≤ E.map (centerQuotAut K) ∧ Ft.relIndex (E.map (centerQuotAut K)) = q),
        CFSG.GH74.GLS.oPrimeResidualOf 2 (CFSG.LieType.Seitz.fixedPoints Ft)) ≤
        (⨆ (F : Subgroup (MulAut K)) (_ : F ≤ E ∧ F.relIndex E ≤ q), centFixAut F).map
          (QuotientGroup.mk' (Subgroup.center K)) := by
      refine iSup₂_le fun Ft ⟨hFtE, hFti⟩ => ?_
      have hFE : Ft.comap (centerQuotAut K) ≤ E := by
        intro σ hσ
        obtain ⟨σ', hσ', h'⟩ := Subgroup.mem_map.1 (hFtE hσ)
        rw [← hfinj h']
        exact hσ'
      have hFi : (Ft.comap (centerQuotAut K)).relIndex E ≤ q := by
        have h1 : (Ft.comap (centerQuotAut K)).relIndex E =
            Ft.relIndex (E.map (centerQuotAut K)) := Subgroup.relIndex_comap Ft (centerQuotAut K) E
        exact (h1.trans hFti).le
      have hFp : IsPGroup q ↥(Ft.comap (centerQuotAut K)) :=
        IsPGroup.to_le (isPGroup_of_isElemAbelian hE) hFE
      refine le_trans ?_ (Subgroup.map_mono (le_iSup₂_of_le (Ft.comap (centerQuotAut K))
        ⟨hFE, hFi⟩ le_rfl))
      unfold CFSG.GH74.GLS.oPrimeResidualOf CFSG.GH74.GLS.oPrimeResidual
      rw [Subgroup.map_le_iff_le_comap, Subgroup.closure_le]
      rintro ⟨s, hsfix⟩ ⟨k, hk⟩
      have hs : s ^ (2 ^ k) = 1 := by
        have := congrArg Subtype.val hk
        simpa using this
      have hfix : ∀ f ∈ Ft.comap (centerQuotAut K), centerQuotAut K f s = s :=
        fun f hf => hsfix (centerQuotAut K f) hf
      obtain ⟨y, hy, hyfix⟩ := exists_fixed_two_lift hq hq2 hFp hs hfix
      exact ⟨y, mem_centFixAut.2 hyfix, hy⟩
    have htop : (⨆ (F : Subgroup (MulAut K)) (_ : F ≤ E ∧ F.relIndex E ≤ q), centFixAut F).map
        (QuotientGroup.mk' (Subgroup.center K)) = ⊤ := eq_top_iff.2 (hmain.ge.trans hle)
    refine eq_top_of_sup_center hperf fun k => ?_
    obtain ⟨θ, hθ, hθk⟩ := Subgroup.mem_map.1 (htop ▸ Subgroup.mem_top
      (QuotientGroup.mk' (Subgroup.center K) k))
    exact ⟨θ, hθ, QuotientGroup.eq.1 hθk⟩

end CFSG.LocalAnalysis.GLTheoremA.Y10F
