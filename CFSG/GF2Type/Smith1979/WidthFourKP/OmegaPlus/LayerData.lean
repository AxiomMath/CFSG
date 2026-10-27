module

public import Mathlib.GroupTheory.PGroup

public section

namespace CFSG.GF2Type.Smith1979.OmegaPlus

structure LayerData (X : Type) [Group X] [Finite X] (A : Subgroup (MulAut X)) (τ : MulAut X)
    (B : Subgroup X) : Prop where
  card_A : Nat.card A = 8
  sq_A : ∀ a ∈ A, a * a = 1
  mem_A : τ ∈ A
  ne_one : τ ≠ 1
  B_ne : B ≠ ⊥
  B_exp : ∀ b ∈ B, b ^ 3 = 1
  B_comm : ∀ b ∈ B, ∀ b' ∈ B, b * b' = b' * b
  B_fix : ∀ b ∈ B, τ b = b
  B_norm : ∀ c : X, τ c = c → ∀ b ∈ B, c * b * c⁻¹ ∈ B
  two_quot : ∀ c : X, τ c = c → c ^ 32 ∈ B
  inner : 15120 < Nat.card X → ∃ x : X, τ = MulAut.conj x
  core : ∀ T : Subgroup X, (∀ y ∈ T, τ y = y) → IsPGroup 2 T →
    (∀ σ : MulAut X, σ * τ = τ * σ → ∀ y ∈ T, σ y ∈ T) →
    Nat.card T ≤ 4 ∧ (Nat.card T = 4 → ∃ y₁ ∈ T, ∃ y₂ ∈ T, orderOf y₁ = 2 ∧ orderOf y₂ = 2 ∧
      ¬ IsConj y₁ y₂)

variable {X Y : Type} [Group X] [Finite X] [Group Y] [Finite Y]
  {A : Subgroup (MulAut X)} {τ : MulAut X} {B : Subgroup X}

theorem LayerData.map (D : LayerData X A τ B) (e : X ≃* Y) :
    LayerData Y (A.map (MulAut.congr e).toMonoidHom) (MulAut.congr e τ) (B.map e.toMonoidHom) := by
  have hcongr : ∀ (σ : MulAut X) (b : X), (MulAut.congr e σ) (e b) = e (σ b) := by
    intro σ b
    rw [MulAut.congr_apply]
    simp [MulEquiv.trans_apply]
  have hconj : ∀ x : X, MulAut.congr e (MulAut.conj x) = MulAut.conj (e x) := by
    intro x
    ext y
    simp [MulAut.congr_apply, MulEquiv.trans_apply, MulAut.conj_apply]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [Subgroup.card_map_of_injective (MulAut.congr e).injective, D.card_A]
  · rintro a ⟨a₀, ha₀, rfl⟩
    calc MulAut.congr e a₀ * MulAut.congr e a₀ = MulAut.congr e (a₀ * a₀) :=
          (map_mul (MulAut.congr e) a₀ a₀).symm
      _ = 1 := by rw [D.sq_A a₀ ha₀, map_one]
  · exact Subgroup.mem_map.mpr ⟨τ, D.mem_A, rfl⟩
  · intro h
    apply D.ne_one
    apply (MulAut.congr e).injective
    calc (MulAut.congr e) τ = 1 := h
      _ = (MulAut.congr e) 1 := (map_one (MulAut.congr e)).symm
  · intro h
    apply D.B_ne
    have hker : e.toMonoidHom.ker = ⊥ :=
      (MonoidHom.ker_eq_bot_iff e.toMonoidHom).mpr e.injective
    rw [Subgroup.map_eq_bot_iff, hker, le_bot_iff] at h
    exact h
  · rintro b ⟨b₀, hb₀, rfl⟩
    calc e b₀ ^ 3 = e (b₀ ^ 3) := (map_pow e b₀ 3).symm
      _ = 1 := by rw [D.B_exp b₀ hb₀, map_one]
  · rintro b ⟨b₀, hb₀, rfl⟩ b' ⟨b₁, hb₁, rfl⟩
    calc e b₀ * e b₁ = e (b₀ * b₁) := (map_mul e b₀ b₁).symm
      _ = e (b₁ * b₀) := by rw [D.B_comm b₀ hb₀ b₁ hb₁]
      _ = e b₁ * e b₀ := map_mul e b₁ b₀
  · rintro b ⟨b₀, hb₀, rfl⟩
    change (MulAut.congr e τ) (e b₀) = e b₀
    rw [hcongr, D.B_fix b₀ hb₀]
  · intro c hc b hb
    rcases Subgroup.mem_map.mp hb with ⟨b₀, hb₀, rfl⟩
    have hc₀ : τ (e.symm c) = e.symm c := by
      apply e.injective
      have h' : e (τ (e.symm c)) = c := by
        calc e (τ (e.symm c)) = (MulAut.congr e τ) (e (e.symm c)) :=
              (hcongr τ (e.symm c)).symm
          _ = (MulAut.congr e τ) c := by rw [e.apply_symm_apply]
          _ = c := hc
      rw [h', e.apply_symm_apply]
    refine Subgroup.mem_map.mpr ⟨e.symm c * b₀ * (e.symm c)⁻¹, D.B_norm _ hc₀ b₀ hb₀, ?_⟩
    change e (e.symm c * b₀ * (e.symm c)⁻¹) = c * e b₀ * c⁻¹
    simp [map_mul, map_inv, e.apply_symm_apply]
  · intro c hc
    have hc₀ : τ (e.symm c) = e.symm c := by
      apply e.injective
      have h' : e (τ (e.symm c)) = c := by
        calc e (τ (e.symm c)) = (MulAut.congr e τ) (e (e.symm c)) :=
              (hcongr τ (e.symm c)).symm
          _ = (MulAut.congr e τ) c := by rw [e.apply_symm_apply]
          _ = c := hc
      rw [h', e.apply_symm_apply]
    refine Subgroup.mem_map.mpr ⟨(e.symm c) ^ 32, D.two_quot _ hc₀, ?_⟩
    change e ((e.symm c) ^ 32) = c ^ 32
    rw [map_pow, e.apply_symm_apply]
  · intro hcard
    have hcardX : 15120 < Nat.card X := by
      rw [Nat.card_congr e.toEquiv]
      exact hcard
    rcases D.inner hcardX with ⟨x, hx⟩
    exact ⟨e x, by rw [hx, hconj]⟩
  · intro T hfixT h2 hinv
    let T' : Subgroup X := T.map e.symm.toMonoidHom
    have hcardT' : Nat.card T' = Nat.card T :=
      Subgroup.card_map_of_injective e.symm.injective
    have hfixT' : ∀ y ∈ T', τ y = y := by
      intro y hy
      rcases Subgroup.mem_map.mp hy with ⟨t, ht, rfl⟩
      apply e.injective
      change e (τ (e.symm t)) = e (e.symm t)
      have h' : e (τ (e.symm t)) = t := by
        calc e (τ (e.symm t)) = (MulAut.congr e τ) (e (e.symm t)) :=
              (hcongr τ (e.symm t)).symm
          _ = (MulAut.congr e τ) t := by rw [e.apply_symm_apply]
          _ = t := hfixT t ht
      rw [h', e.apply_symm_apply]
    have h2' : IsPGroup 2 T' := IsPGroup.map h2 e.symm.toMonoidHom
    have hinv' : ∀ σ : MulAut X, σ * τ = τ * σ → ∀ y ∈ T', σ y ∈ T' := by
      intro σ hσ y hy
      rcases Subgroup.mem_map.mp hy with ⟨t, ht, rfl⟩
      let σ' : MulAut Y := MulAut.congr e σ
      have hσ' : σ' * MulAut.congr e τ = MulAut.congr e τ * σ' := by
        have h := congrArg (MulAut.congr e) hσ
        simpa [σ', map_mul] using h
      refine Subgroup.mem_map.mpr ⟨σ' t, hinv σ' hσ' t ht, ?_⟩
      have hσ't : σ' t = e (σ (e.symm t)) := by
        change (MulAut.congr e σ) t = e (σ (e.symm t))
        simpa [e.apply_symm_apply] using hcongr σ (e.symm t)
      rw [hσ't]
      exact e.symm_apply_apply _
    obtain ⟨hcore1, hcore2⟩ := D.core T' hfixT' h2' hinv'
    refine ⟨?_, ?_⟩
    · rw [← hcardT']
      exact hcore1
    · intro hcardT
      have hcardT'4 : Nat.card T' = 4 := by rw [hcardT', hcardT]
      obtain ⟨y₁, hy₁, y₂, hy₂, ho₁, ho₂, hnc⟩ := hcore2 hcardT'4
      have hy₁T : e y₁ ∈ T := by
        rcases Subgroup.mem_map.mp hy₁ with ⟨t, ht, hte⟩
        rw [← hte]
        change e (e.symm t) ∈ T
        simpa using ht
      have hy₂T : e y₂ ∈ T := by
        rcases Subgroup.mem_map.mp hy₂ with ⟨t, ht, hte⟩
        rw [← hte]
        change e (e.symm t) ∈ T
        simpa using ht
      refine ⟨e y₁, hy₁T, e y₂, hy₂T, ?_, ?_, ?_⟩
      · rw [MulEquiv.orderOf_eq e y₁, ho₁]
      · rw [MulEquiv.orderOf_eq e y₂, ho₂]
      · intro hconj
        apply hnc
        rcases isConj_iff.mp hconj with ⟨c, hc⟩
        rw [isConj_iff]
        refine ⟨e.symm c, ?_⟩
        apply e.injective
        simpa [map_mul, map_inv, e.apply_symm_apply] using hc

theorem LayerData.false_of_W1 (D : LayerData X A τ B)
    (h : ∀ y : X, τ y = y → y ^ 3 = 1 → y = 1) : False := by
  rcases Subgroup.ne_bot_iff_exists_ne_one.mp D.B_ne with ⟨b, hbne⟩
  have hbne' : (b : X) ≠ 1 := fun h' => hbne (Subtype.ext h')
  exact hbne' (h (b : X) (D.B_fix _ b.2) (D.B_exp _ b.2))

theorem LayerData.false_of_W2 (D : LayerData X A τ B) {y₁ y₂ : X} (h₁ : τ y₁ = y₁)
    (h₂ : τ y₂ = y₂) (h₁3 : y₁ ^ 3 = 1) (h₂3 : y₂ ^ 3 = 1) (h : (y₁ * y₂) ^ 3 ≠ 1) : False := by
  have mem_B : ∀ y : X, τ y = y → y ^ 3 = 1 → y ∈ B := by
    intro y hy hy3
    have hy32 : y ^ 32 ∈ B := D.two_quot y hy
    have hy2 : y ^ 2 ∈ B := by
      have hpow : y ^ 32 = y ^ 2 := by
        calc y ^ 32 = y ^ (3 * 10 + 2) := by norm_num
          _ = (y ^ 3) ^ 10 * y ^ 2 := by rw [pow_add, pow_mul]
          _ = y ^ 2 := by rw [hy3, one_pow, one_mul]
      rwa [hpow] at hy32
    have hy4 : y ^ 4 = y := by
      rw [show (4 : ℕ) = 3 + 1 by norm_num, pow_add, hy3, one_mul, pow_one]
    have hy_eq : y = (y ^ 2) ^ 2 := by
      rw [← pow_mul, show (2 * 2 : ℕ) = 4 by norm_num, hy4]
    rw [hy_eq]
    exact pow_mem hy2 2
  have hB : y₁ * y₂ ∈ B := B.mul_mem (mem_B y₁ h₁ h₁3) (mem_B y₂ h₂ h₂3)
  exact h (D.B_exp (y₁ * y₂) hB)

theorem LayerData.false_of_W5 (D : LayerData X A τ B) {T : Subgroup X}
    (hfix : ∀ y ∈ T, τ y = y) (h2 : IsPGroup 2 T)
    (hinv : ∀ σ : MulAut X, σ * τ = τ * σ → ∀ y ∈ T, σ y ∈ T)
    (h4 : Nat.card T = 4)
    (hconj : ∀ y₁ ∈ T, ∀ y₂ ∈ T, orderOf y₁ = 2 → orderOf y₂ = 2 → IsConj y₁ y₂) : False := by
  obtain ⟨-, h⟩ := D.core T hfix h2 hinv
  obtain ⟨y₁, hy₁, y₂, hy₂, ho₁, ho₂, hnc⟩ := h h4
  exact hnc (hconj y₁ hy₁ y₂ hy₂ ho₁ ho₂)

theorem LayerData.false_of_outTwo [IsSimpleGroup X] (hnonab : ∃ a b : X, a * b ≠ b * a)
    (D : LayerData X A τ B) (hA : Nat.card (MulAut X) ≤ 2 * Nat.card X)
    (hC : ∀ v y : X, orderOf v = 2 → y * v = v * y → y ^ 3 = 1 → y = 1) : False := by
  classical
  have hZ : Subgroup.center X = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center X) with h | h
    · exact h
    · exfalso
      obtain ⟨a, b, hab⟩ := hnonab
      exact hab (Subgroup.mem_center_iff.mp (h ▸ Subgroup.mem_top b) a)
  have hinj : Function.Injective (MulAut.conj : X →* MulAut X) := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro z hz
    rw [MonoidHom.mem_ker] at hz
    rw [← hZ, Subgroup.mem_center_iff]
    intro g
    have h := congrArg (fun φ : MulAut X => φ g) hz
    simp only [MulAut.conj_apply, MulAut.one_apply] at h
    calc g * z = z * g * z⁻¹ * z := by rw [h]
      _ = z * g := by group
  let I : Subgroup (MulAut X) := (MulAut.conj : X →* MulAut X).range
  have hIcard : Nat.card I = Nat.card X :=
    (Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv).symm
  have hIindex : I.index ≤ 2 := by
    have h := Subgroup.index_mul_card I
    rw [hIcard] at h
    have hle : I.index * Nat.card X ≤ 2 * Nat.card X := by
      rw [h]
      exact hA
    exact Nat.le_of_mul_le_mul_right hle (by
      haveI : Nonempty X := ⟨1⟩
      exact Nat.card_pos)
  have hrel : I.relIndex A ≤ 2 := by
    have h0 : I.relIndex (⊤ : Subgroup (MulAut X)) ≠ 0 := by
      rw [Subgroup.relIndex_top_right]
      exact Subgroup.index_ne_zero_of_finite
    calc I.relIndex A ≤ I.relIndex ⊤ := Subgroup.relIndex_le_of_le_right le_top h0
      _ = I.index := Subgroup.relIndex_top_right I
      _ ≤ 2 := hIindex
  have hcardIA : 4 ≤ Nat.card ↥(I ⊓ A) := by
    have h := Subgroup.relIndex_mul_card I A
    rw [D.card_A] at h
    have hpos : 0 < I.relIndex A :=
      Nat.pos_of_dvd_of_pos (Subgroup.relIndex_dvd_card I A) (by rw [D.card_A]; norm_num)
    have h12 : I.relIndex A = 1 ∨ I.relIndex A = 2 := by omega
    rcases h12 with h1 | h2
    · rw [h1, one_mul] at h
      omega
    · rw [h2] at h
      omega
  letI := Fintype.ofFinite ↥(I ⊓ A)
  have htwo : 1 < (Finset.univ.erase (1 : ↥(I ⊓ A))).card := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ,
      ← Nat.card_eq_fintype_card]
    omega
  obtain ⟨u, hu, v, hv, huv⟩ := Finset.one_lt_card.mp htwo
  have hu1 : (u : MulAut X) ≠ 1 := by
    intro h
    exact (Finset.mem_erase.mp hu).1 (Subtype.ext h)
  have hv1 : (v : MulAut X) ≠ 1 := by
    intro h
    exact (Finset.mem_erase.mp hv).1 (Subtype.ext h)
  have huv' : (u : MulAut X) ≠ (v : MulAut X) := fun h => huv (Subtype.ext h)
  have hAcomm : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a := by
    intro a ha b hb
    have ha' : a⁻¹ = a := inv_eq_of_mul_eq_one_right (D.sq_A a ha)
    have hb' : b⁻¹ = b := inv_eq_of_mul_eq_one_right (D.sq_A b hb)
    have h := D.sq_A (a * b) (A.mul_mem ha hb)
    have h' : (a * b)⁻¹ = a * b := inv_eq_of_mul_eq_one_right h
    calc a * b = (a * b)⁻¹ := h'.symm
      _ = b⁻¹ * a⁻¹ := mul_inv_rev a b
      _ = b * a := by rw [ha', hb']
  have huA : (u : MulAut X) ∈ A := (Subgroup.mem_inf.mp u.2).2
  have hvA : (v : MulAut X) ∈ A := (Subgroup.mem_inf.mp v.2).2
  have huI : (u : MulAut X) ∈ I := (Subgroup.mem_inf.mp u.2).1
  have hvI : (v : MulAut X) ∈ I := (Subgroup.mem_inf.mp v.2).1
  rcases huI with ⟨x₁, hx₁⟩
  rcases hvI with ⟨x₂, hx₂⟩
  have hx₁' : MulAut.conj x₁ = (u : MulAut X) := hx₁
  have hx₂' : MulAut.conj x₂ = (v : MulAut X) := hx₂
  have hx₁ne : x₁ ≠ 1 := by
    intro h
    apply hu1
    rw [← hx₁', h]
    simp
  have hx₂ne : x₂ ≠ 1 := by
    intro h
    apply hv1
    rw [← hx₂', h]
    simp
  have hx12 : x₁ ≠ x₂ := by
    intro h
    apply huv'
    rw [← hx₁', ← hx₂', h]
  have hx₁sq : x₁ * x₁ = 1 := by
    apply hinj
    rw [map_mul, hx₁', D.sq_A (u : MulAut X) huA, map_one]
  have hx₂sq : x₂ * x₂ = 1 := by
    apply hinj
    rw [map_mul, hx₂', D.sq_A (v : MulAut X) hvA, map_one]
  have hx₁ord : orderOf x₁ = 2 := orderOf_eq_prime (by simpa [pow_two] using hx₁sq) hx₁ne
  have hx₂ord : orderOf x₂ = 2 := orderOf_eq_prime (by simpa [pow_two] using hx₂sq) hx₂ne
  have hfix₁ : τ x₁ = x₁ := by
    have hcomm : (u : MulAut X) * τ = τ * (u : MulAut X) := hAcomm _ huA _ D.mem_A
    apply hinj
    calc MulAut.conj (τ x₁) = τ * MulAut.conj x₁ * τ⁻¹ := by
          ext y
          simp [MulAut.conj_apply, MulAut.mul_apply, map_mul, map_inv]
      _ = τ * (u : MulAut X) * τ⁻¹ := by rw [hx₁']
      _ = (u : MulAut X) := by
          rw [← hcomm]
          group
      _ = MulAut.conj x₁ := hx₁'.symm
  have hfix₂ : τ x₂ = x₂ := by
    have hcomm : (v : MulAut X) * τ = τ * (v : MulAut X) := hAcomm _ hvA _ D.mem_A
    apply hinj
    calc MulAut.conj (τ x₂) = τ * MulAut.conj x₂ * τ⁻¹ := by
          ext y
          simp [MulAut.conj_apply, MulAut.mul_apply, map_mul, map_inv]
      _ = τ * (v : MulAut X) * τ⁻¹ := by rw [hx₂']
      _ = (v : MulAut X) := by
          rw [← hcomm]
          group
      _ = MulAut.conj x₂ := hx₂'.symm
  have hx₁₂comm : x₁ * x₂ = x₂ * x₁ := by
    apply hinj
    rw [map_mul, map_mul, hx₁', hx₂']
    exact hAcomm _ huA _ hvA
  have hx₁₂sq : x₁ * x₂ * (x₁ * x₂) = 1 := by
    calc x₁ * x₂ * (x₁ * x₂) = x₁ * (x₂ * x₁) * x₂ := by group
      _ = x₁ * (x₁ * x₂) * x₂ := by rw [← hx₁₂comm]
      _ = x₁ * x₁ * (x₂ * x₂) := by group
      _ = 1 := by rw [hx₁sq, hx₂sq]; group
  have hx₁₂ne : x₁ * x₂ ≠ 1 := by
    intro h
    apply hx12
    rw [eq_inv_of_mul_eq_one_left h, inv_eq_of_mul_eq_one_right hx₂sq]
  have hx₁₂ord : orderOf (x₁ * x₂) = 2 :=
    orderOf_eq_prime (by simpa [pow_two] using hx₁₂sq) hx₁₂ne
  have hx₁₂fix : τ (x₁ * x₂) = x₁ * x₂ := by rw [map_mul, hfix₁, hfix₂]
  rcases Subgroup.ne_bot_iff_exists_ne_one.mp D.B_ne with ⟨b, hbne_sub⟩
  let bX : X := (b : X)
  have hbB : bX ∈ B := b.2
  have hbne : bX ≠ 1 := fun h => hbne_sub (Subtype.ext h)
  have hb3 : bX ^ 3 = 1 := D.B_exp bX hbB
  have hbconj : ∀ x : X, orderOf x = 2 → τ x = x → x * bX * x⁻¹ = bX⁻¹ := by
    intro x hxord hxfix
    have hxbB : x * bX * x⁻¹ ∈ B := D.B_norm x hxfix bX hbB
    have hxsq : x * x = 1 := by
      have h := pow_orderOf_eq_one x
      rw [hxord] at h
      simpa [pow_two] using h
    have hxinv : x⁻¹ = x := inv_eq_of_mul_eq_one_right hxsq
    let w : X := bX * (x * bX * x⁻¹)
    have hwB : w ∈ B := B.mul_mem hbB hxbB
    have hw3 : w ^ 3 = 1 := D.B_exp w hwB
    have hxw : x * w * x⁻¹ = w := by
      change x * (bX * (x * bX * x⁻¹)) * x⁻¹ = bX * (x * bX * x⁻¹)
      calc x * (bX * (x * bX * x⁻¹)) * x⁻¹
          = (x * bX * x⁻¹) * (x * (x * bX * x⁻¹) * x⁻¹) := by group
        _ = (x * bX * x⁻¹) * bX := by
            congr 1
            calc x * (x * bX * x⁻¹) * x⁻¹
                = (x * x) * bX * (x⁻¹ * x⁻¹) := by group
              _ = bX := by rw [hxinv, hxsq]; group
        _ = bX * (x * bX * x⁻¹) := D.B_comm _ hxbB bX hbB
    have hwcomm : w * x = x * w := by
      nth_rewrite 1 [← hxw]
      calc (x * w * x⁻¹) * x = (x * w * x) * x := by rw [hxinv]
        _ = (x * w) * (x * x) := by group
        _ = x * w := by rw [hxsq, mul_one]
    have hw1 : w = 1 := hC x w hxord hwcomm hw3
    have hw1' : bX * (x * bX * x⁻¹) = 1 := hw1
    exact (inv_eq_of_mul_eq_one_right hw1').symm
  have hb₁ : x₁ * bX * x₁⁻¹ = bX⁻¹ := hbconj x₁ hx₁ord hfix₁
  have hb₂ : x₂ * bX * x₂⁻¹ = bX⁻¹ := hbconj x₂ hx₂ord hfix₂
  have hconj12 : (x₁ * x₂) * bX * (x₁ * x₂)⁻¹ = bX := by
    calc (x₁ * x₂) * bX * (x₁ * x₂)⁻¹
        = x₁ * (x₂ * bX * x₂⁻¹) * x₁⁻¹ := by group
      _ = x₁ * bX⁻¹ * x₁⁻¹ := by rw [hb₂]
      _ = (x₁ * bX * x₁⁻¹)⁻¹ := by group
      _ = (bX⁻¹)⁻¹ := by rw [hb₁]
      _ = bX := inv_inv bX
  have hcomm12 : bX * (x₁ * x₂) = (x₁ * x₂) * bX := by
    calc bX * (x₁ * x₂) = ((x₁ * x₂) * bX * (x₁ * x₂)⁻¹) * (x₁ * x₂) := by
          rw [hconj12]
      _ = (x₁ * x₂) * bX := by group
  exact hbne (hC (x₁ * x₂) bX hx₁₂ord hcomm12 hb3)

theorem LayerData.inner_of_outOdd [IsSimpleGroup X] (hnonab : ∃ a b : X, a * b ≠ b * a)
    (D : LayerData X A τ B) {k : ℕ} (hk : Odd k) (hA : Nat.card (MulAut X) = k * Nat.card X) :
    ∃ x : X, τ = MulAut.conj x := by
  have hZ : Subgroup.center X = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center X) with h | h
    · exact h
    · exfalso
      obtain ⟨a, b, hab⟩ := hnonab
      exact hab (Subgroup.mem_center_iff.mp (h ▸ Subgroup.mem_top b) a)
  have hinj : Function.Injective (MulAut.conj : X →* MulAut X) := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro z hz
    rw [MonoidHom.mem_ker] at hz
    rw [← hZ, Subgroup.mem_center_iff]
    intro g
    have h := congrArg (fun φ : MulAut X => φ g) hz
    simp only [MulAut.conj_apply, MulAut.one_apply] at h
    calc g * z = z * g * z⁻¹ * z := by rw [h]
      _ = z * g := by group
  let I : Subgroup (MulAut X) := (MulAut.conj : X →* MulAut X).range
  have hInorm : I.Normal := by
    refine ⟨fun x hx f => ?_⟩
    obtain ⟨k, rfl⟩ := hx
    refine ⟨f k, ?_⟩
    ext y
    change f k * y * (f k)⁻¹ = f (k * f⁻¹ y * k⁻¹)
    rw [map_mul, map_mul, map_inv, MulAut.apply_inv_self]
  have hIcard : Nat.card I = Nat.card X :=
    (Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv).symm
  have hIindex : I.index = k := by
    have h := Subgroup.index_mul_card I
    rw [hIcard, hA] at h
    exact Nat.mul_right_cancel (by
      haveI : Nonempty X := ⟨1⟩
      exact Nat.card_pos) h
  haveI : I.Normal := hInorm
  have hquot : Nat.card (MulAut X ⧸ I) = k := by
    rw [← Subgroup.index_eq_card, hIindex]
  let q : MulAut X ⧸ I := QuotientGroup.mk τ
  have hq2 : q ^ 2 = 1 := by
    change (QuotientGroup.mk τ : MulAut X ⧸ I) ^ 2 = 1
    have hτ2 : τ ^ 2 = 1 := by simpa [pow_two] using D.sq_A τ D.mem_A
    rw [← QuotientGroup.mk_pow, hτ2, QuotientGroup.mk_one]
  have hqordk : orderOf q ∣ k := by
    rw [← hquot]
    exact orderOf_dvd_natCard q
  have hqord2 : orderOf q ∣ 2 := orderOf_dvd_of_pow_eq_one hq2
  have hcop : Nat.Coprime (orderOf q) k :=
    Nat.Coprime.coprime_dvd_left hqord2 (Nat.coprime_two_left.mpr hk)
  have hqord1 : orderOf q = 1 := hcop.eq_one_of_dvd hqordk
  have hq1 : q = 1 := orderOf_eq_one_iff.mp hqord1
  have hmem : τ ∈ I := (QuotientGroup.eq_one_iff (N := I) τ).mp hq1
  rcases hmem with ⟨x, hx⟩
  exact ⟨x, hx.symm⟩

end CFSG.GF2Type.Smith1979.OmegaPlus

end
