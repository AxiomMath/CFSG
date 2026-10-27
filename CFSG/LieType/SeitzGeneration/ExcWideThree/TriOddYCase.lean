module

public import CFSG.LieType.SeitzGeneration.ExcWideThree.TriOddOpen
public import CFSG.LieType.SeitzGeneration.ExcWideThree.TriOddSL2Aut
public import CFSG.LieType.SeitzGeneration.ExcWideThree.TriOddModelA
public import CFSG.LieType.SeitzGeneration.ExcWideThree.TriOddModelB

public section

namespace CFSG.LieType.SeitzGeneration.ExcWideThree

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.SeitzGeneration
  CFSG.LieType.SeitzGeneration.ExcWideThree CFSG.Fischer CFSG.RankThree.PartOne.CTP
  CFSG.RankThree.PartTwo.Sec11 CFSG.RankThree.PartTwo.Sec19
open scoped MatrixGroups

section Plain

theorem triOdd_restrict_aut {G S : Type*} [Group G] [Group S] [Finite S] (ι : S →* G)
    (hι : Function.Injective ι) (β : MulAut G) (hβ3 : β ^ 3 = 1)
    (hβA : ∀ M, ∃ N, ι N = β (ι M)) :
    ∃ ρ : MulAut S, ρ ^ 3 = 1 ∧ ∀ M, ι (ρ M) = β (ι M) := by
  classical
  choose r hr using hβA
  have hmul : ∀ M N, r (M * N) = r M * r N := fun M N => by
    apply hι
    calc ι (r (M * N)) = β (ι (M * N)) := hr _
      _ = β (ι M) * β (ι N) := by rw [map_mul, map_mul]
      _ = ι (r M) * ι (r N) := by rw [hr, hr]
      _ = ι (r M * r N) := (map_mul ι _ _).symm
  have hrinj : Function.Injective r := fun M N h => by
    apply hι
    have h1 : β (ι M) = β (ι N) := by rw [← hr M, ← hr N, h]
    exact β.injective h1
  have hbij : Function.Bijective r := Finite.injective_iff_bijective.1 hrinj
  let ρ : MulAut S := MulEquiv.ofBijective (MonoidHom.mk' r hmul) hbij
  have hρ : ∀ M, ι (ρ M) = β (ι M) := fun M => hr M
  refine ⟨ρ, ?_, hρ⟩
  refine MulEquiv.ext fun M => ?_
  apply hι
  have h3 : ∀ x : G, β (β (β x)) = x := fun x => by
    have := congrArg (fun φ : MulAut G => φ x) hβ3
    simpa [pow_succ, MulAut.mul_apply] using this
  have : (ρ ^ 3) M = ρ (ρ (ρ M)) := by simp [pow_succ, MulAut.mul_apply]
  rw [this, hρ, hρ, hρ, h3]
  rfl

end Plain

section Model


variable {X : Type} [Field X] [Finite X] (σ : X ≃+* X)

theorem triOdd_hasGLine_map (φ : MulAut (C0 σ)) (E : Subgroup (MulAut (C0 σ)))
    (h : TriOddHasGLine σ (E.map (MulAut.congr φ).toMonoidHom)) : TriOddHasGLine σ E := by
  obtain ⟨β', ⟨β, hβE, rfl⟩, ψ, hψ⟩ := h
  refine ⟨β, hβE, ψ * φ, ?_⟩
  have e : (MulAut.congr φ).toMonoidHom β = φ * β * φ⁻¹ := congr_apply_eq φ β
  rw [e] at hψ
  rcases hψ with h | h
  · left; rw [← h]; group
  · right; rw [← h]; group

theorem triOdd_conj_mul_pow_three (g : C0 σ) (φ : MulAut (C0 σ)) (hφ : φ ^ 3 = 1) :
    (MulAut.conj g * φ) ^ 3 = MulAut.conj (g * φ g * φ (φ g)) := by
  refine MulEquiv.ext fun k => ?_
  have h3 : ∀ x : C0 σ, φ (φ (φ x)) = x := fun x => by
    have := congrArg (fun ψ : MulAut (C0 σ) => ψ x) hφ
    simpa [pow_succ, MulAut.mul_apply] using this
  simp only [pow_succ, pow_zero, one_mul, MulAut.mul_apply, MulAut.conj_apply, map_mul, map_inv, h3]

theorem triOdd_comm_of_commute (hZ : Subgroup.center (C0 σ) = ⊥) {b g : C0 σ} {φ : MulAut (C0 σ)}
    (hφb : φ b = b) (hcomm : Commute (MulAut.conj b) (MulAut.conj g * φ)) : b * g = g * b := by
  have key : ∀ k : C0 σ, (b * g) * φ k * (b * g)⁻¹ = (g * b) * φ k * (g * b)⁻¹ := by
    intro k
    have h1 := congrArg (fun ψ : MulAut (C0 σ) => ψ k) hcomm.eq
    simp only [MulAut.mul_apply, MulAut.conj_apply] at h1
    rw [map_mul, map_mul, map_inv, hφb] at h1
    calc (b * g) * φ k * (b * g)⁻¹ = b * (g * φ k * g⁻¹) * b⁻¹ := by group
      _ = g * (b * φ k * b⁻¹) * g⁻¹ := h1
      _ = (g * b) * φ k * (g * b)⁻¹ := by group
  have hconj : MulAut.conj (b * g) = MulAut.conj (g * b) := by
    refine MulEquiv.ext fun m => ?_
    have := key (φ⁻¹ m)
    rw [MulAut.apply_inv_self] at this
    simpa only [MulAut.conj_apply] using this
  exact nf1_conj_injective hZ hconj

theorem triOdd_tauPow_apply_B (hB : ∀ b ∈ Bsub σ, tauAut σ b = b) (n : ℕ) {b : C0 σ}
    (hb : b ∈ Bsub σ) : (tauAut σ ^ n) b = b := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ', MulAut.mul_apply, ih, hB b hb]

theorem triOdd_tauPow_mem_A (hA : ∀ a ∈ Asub σ, tauAut σ a ∈ Asub σ) (n : ℕ) {a : C0 σ}
    (ha : a ∈ Asub σ) : (tauAut σ ^ n) a ∈ Asub σ := by
  induction n with
  | zero => simpa using ha
  | succ n ih => rw [pow_succ', MulAut.mul_apply]; exact hA _ ih

theorem triOdd_sl2_map_map {F : Type} [Field F] (f g : F ≃+* F)
    (M : Matrix.SpecialLinearGroup (Fin 2) F) :
    Matrix.SpecialLinearGroup.map f.toRingHom (Matrix.SpecialLinearGroup.map g.toRingHom M) =
      Matrix.SpecialLinearGroup.map (f * g).toRingHom M := by
  apply Subtype.ext
  ext i j
  rfl

theorem triOdd_chart_tauPow (ι : Matrix.SpecialLinearGroup (Fin 2) X →* C0 σ)
    (hιτ : ∀ M, tauAut σ (ι M) = ι (Matrix.SpecialLinearGroup.map σ.toRingHom M)) (n : ℕ)
    (M : Matrix.SpecialLinearGroup (Fin 2) X) :
    (tauAut σ ^ n) (ι M) = ι (Matrix.SpecialLinearGroup.map (σ ^ n).toRingHom M) := by
  induction n with
  | zero =>
    simp only [pow_zero]
    have : Matrix.SpecialLinearGroup.map (1 : X ≃+* X).toRingHom M = M := by
      apply Subtype.ext
      ext i j
      rfl
    rw [this]
    rfl
  | succ n ih =>
    rw [pow_succ', MulAut.mul_apply, ih, hιτ, triOdd_sl2_map_map, pow_succ']

end Model

section Main


variable {X : Type} [Field X] [Finite X] (σ : X ≃+* X)

theorem triOdd_hasGLine_of_mem_B {ℓ f : ℕ} (hℓ : ℓ.Prime) (hℓ2 : ℓ ≠ 2) (hℓ3 : ℓ ≠ 3)
    (hf : 1 ≤ f) (hX : Nat.card X = (ℓ ^ f) ^ 3) (hσ : ∀ c : X, σ c = c ^ (ℓ ^ f))
    (E : Subgroup (MulAut (C0 σ))) (hE : CFSG.IsElementaryAbelian 3 E)
    (hcard : Nat.card E = 3 ^ 2) (hout : ¬ E ≤ innerAut (C0 σ)) (b : C0 σ) (hb3 : b ^ 3 = 1)
    (hb1 : b ≠ 1) (hbB : b ∈ Bsub σ) (hcb : MulAut.conj b ∈ E) : TriOddHasGLine σ E := by
  classical
  have hσ3 : σ ^ 3 = 1 := triOdd_sigma_pow_three σ (ℓ ^ f) hX hσ
  have hq2 : 2 ≤ ℓ ^ f := by
    calc 2 ≤ ℓ := hℓ.two_le
      _ = ℓ ^ 1 := (pow_one ℓ).symm
      _ ≤ ℓ ^ f := Nat.pow_le_pow_right hℓ.pos hf
  have hσ1 : σ ≠ 1 := triOdd_sigma_ne_one σ (ℓ ^ f) hq2 hX hσ
  have hσ2 : σ ^ 2 ≠ 1 := nf1_sq_ne_one σ hσ3 hσ1
  obtain ⟨-, -, -, -, -, -, hZ, -⟩ :=
    odd_triality_exact_automorphism_normal_form hℓ hℓ2 hf X hX σ hσ
  have hinj : Function.Injective (MulAut.conj : C0 σ →* MulAut (C0 σ)) := nf1_conj_injective hZ
  have hτ3 : tauAut σ ^ 3 = 1 := by
    rw [← triOdd_fieldActor_pow σ 3, hσ3]
    exact fieldActor_one σ
  have hτin := triOdd_tauAut_not_mem_innerAut σ hℓ hℓ2 hf hX hσ
  obtain ⟨x₀, hx₀3, hx₀1, g₀, e, he, hβ3, -, hEeq⟩ :=
    triOdd_plane_shape σ hℓ hℓ2 hf hX hσ E hE hcard hout
  set β : MulAut (C0 σ) := MulAut.conj g₀ * tauAut σ ^ e with hβdef
  have hβE : β ∈ E := by rw [hEeq]; exact Subgroup.subset_closure (by simp)
  have hτe : tauAut σ ^ e ∉ innerAut (C0 σ) := by
    rcases he with rfl | rfl
    · simpa using hτin
    · intro h
      apply hτin
      have h4 : tauAut σ = (tauAut σ ^ 2) ^ 2 := by
        rw [← pow_mul, show 2 * 2 = 3 + 1 from rfl, pow_succ, hτ3, one_mul]
      rw [h4]
      exact pow_mem h 2
  have hβout : β ∉ innerAut (C0 σ) := by
    intro h
    apply hτe
    have : tauAut σ ^ e = (MulAut.conj g₀)⁻¹ * β := by rw [hβdef]; group
    rw [this]
    exact mul_mem (inv_mem ⟨g₀, rfl⟩) h
  haveI : Finite E := Nat.finite_of_card_ne_zero (by rw [hcard]; norm_num)
  have hcb1 : MulAut.conj b ≠ 1 := fun h => hb1 (hinj (h.trans (map_one _).symm))
  have hcb3 : MulAut.conj b ^ 3 = 1 := by rw [← map_pow, hb3, map_one]
  have hβ1 : β ≠ 1 := fun h => hβout (h ▸ one_mem _)
  have hβb : β ≠ MulAut.conj b := fun h => hβout ⟨b, h.symm⟩
  have hβb2 : β ≠ MulAut.conj b ^ 2 := fun h =>
    hβout ⟨b ^ 2, by rw [map_pow]; exact h.symm⟩
  have hEcl : E = Subgroup.closure ({MulAut.conj b, β} : Set (MulAut (C0 σ))) :=
    nf1_closure_pair_eq E hcard hcb hβE hcb1 hcb3 hβ1 hβb hβb2
  have hcomm : Commute (MulAut.conj b) β := by
    have := elemAb_comm hE _ hcb _ hβE
    exact this
  have hBτ : ∀ b' ∈ Bsub σ, tauAut σ b' = b' := triOdd_bsub_tau σ hℓ hℓ2 hℓ3 hf hX hσ
  have hbg : b * g₀ = g₀ * b :=
    triOdd_comm_of_commute σ hZ (triOdd_tauPow_apply_B σ hBτ e hbB) hcomm
  obtain ⟨ι, hιinj, hιA, hιτ⟩ := triOdd_asub_chart σ hℓ hℓ2 hℓ3 hf hX hσ
  have hτA : ∀ a ∈ Asub σ, tauAut σ a ∈ Asub σ := fun a ha => by
    obtain ⟨M, rfl⟩ := (hιA a).1 ha
    exact (hιA _).2 ⟨_, (hιτ M).symm⟩
  have h3q : ¬ 3 ∣ ℓ ^ f := fun h => hℓ3 (((Nat.prime_dvd_prime_iff_eq Nat.prime_three hℓ).1
    (Nat.Prime.dvd_of_dvd_pow Nat.prime_three h)).symm)
  have hB3 := KS11Lie6Proof.d4ThreeBCent_holds X (ℓ ^ f) σ hX hσ h3q b hbB hb3 hb1
  have haC : ∀ a ∈ Asub σ, a ∈ Subgroup.centralizer ({b} : Set (C0 σ)) := fun a ha =>
    Subgroup.mem_centralizer_singleton_iff.2 (Subgroup.mem_centralizer_iff.1 hbB a ha)
  have hg₀C : g₀ ∈ Subgroup.centralizer ({b} : Set (C0 σ)) :=
    Subgroup.mem_centralizer_singleton_iff.2 hbg.symm
  have hnorm : ∀ a ∈ Asub σ, g₀ * a * g₀⁻¹ ∈ Asub σ := fun a ha => by
    have h := hB3.1 g₀ hg₀C a (haC a ha)
    have : g₀ * a * g₀⁻¹ = (g₀ * a * g₀⁻¹ * a⁻¹) * a := by group
    rw [this]
    exact mul_mem h ha
  have hβA : ∀ a ∈ Asub σ, β a ∈ Asub σ := fun a ha => by
    show (MulAut.conj g₀ * tauAut σ ^ e) a ∈ _
    rw [MulAut.mul_apply, MulAut.conj_apply]
    exact hnorm _ (triOdd_tauPow_mem_A σ hτA e ha)
  haveI : Finite (C0 σ) := by
    have : Finite (ModGL TwistTag.D4.tag X) := finite_modGL
    exact Finite.of_injective (fun x : C0 σ => (x : ModGL TwistTag.D4.tag X)) Subtype.val_injective
  obtain ⟨ρ, hρ3, hρι⟩ := triOdd_restrict_aut ι hιinj β hβ3
    (fun M => (hιA _).1 (hβA _ ((hιA _).2 ⟨M, rfl⟩)))
  have hK2 : ringChar X ≠ 2 := by
    haveI : CharP X ℓ := CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic
      hℓ (k := f * 3) (by omega) (by rw [hX, pow_mul])
    rw [ringChar.eq X ℓ]
    exact hℓ2
  have hK4 : 4 ≤ Nat.card X := by
    rw [hX]
    have := Nat.pow_le_pow_left hq2 3
    omega
  have hφ3 : (tauAut σ ^ e) ^ 3 = 1 := by rw [← pow_mul, mul_comm, pow_mul, hτ3, one_pow]
  have hAmem : ∀ M, ι M ∈ Asub σ := fun M => (hιA _).2 ⟨M, rfl⟩
  rcases triOddSL2_aut_three hK2 hK4 σ hσ3 hσ1 ρ hρ3 with ⟨a₁, ha₁⟩ | ⟨a, s, hs, has⟩
  ·
    exfalso
    set α₁ : C0 σ := ι a₁ with hα₁
    have hfixA : ∀ y ∈ Asub σ,
        (MulAut.conj (α₁⁻¹ * g₀) * fieldActor (t := TwistTag.D4) σ (σ ^ e)) y = y := by
      intro y hy
      obtain ⟨M, rfl⟩ := (hιA y).1 hy
      rw [triOdd_fieldActor_pow, MulAut.mul_apply, MulAut.conj_apply]
      have h1 : β (ι M) = α₁ * ι M * α₁⁻¹ := by
        rw [← hρι, ha₁, map_mul, map_mul, map_inv]
      have h2 : β (ι M) = g₀ * (tauAut σ ^ e) (ι M) * g₀⁻¹ := by
        rw [hβdef, MulAut.mul_apply, MulAut.conj_apply]
      calc (α₁⁻¹ * g₀) * (tauAut σ ^ e) (ι M) * (α₁⁻¹ * g₀)⁻¹
          = α₁⁻¹ * (g₀ * (tauAut σ ^ e) (ι M) * g₀⁻¹) * α₁ := by group
        _ = α₁⁻¹ * (α₁ * ι M * α₁⁻¹) * α₁ := by rw [← h2, h1]
        _ = ι M := by group
    have hδ3 : (σ ^ e) ^ 3 = 1 := by rw [← pow_mul, mul_comm, pow_mul, hσ3, one_pow]
    have := triOdd_fieldActor_fix_A σ hℓ hℓ2 hℓ3 hf hX hσ (α₁⁻¹ * g₀) (σ ^ e) hδ3 hfixA
    rcases he with rfl | rfl
    · exact hσ1 (by simpa using this)
    · exact hσ2 this
  ·
    obtain ⟨e', he', hse⟩ : ∃ e' : ℕ, (e' = 1 ∨ e' = 2) ∧ s = σ ^ e' := by
      rcases hs with rfl | rfl
      · exact ⟨1, Or.inl rfl, (pow_one _).symm⟩
      · exact ⟨2, Or.inr rfl, rfl⟩
    set α : C0 σ := ι a with hα
    have hαA : α ∈ Asub σ := hAmem a
    have hαb : α * b = b * α := Subgroup.mem_centralizer_iff.1 hbB α hαA
    set β'' : MulAut (C0 σ) := MulAut.conj α⁻¹ * β * MulAut.conj α with hβ''def
    have hβ''apply : ∀ x, β'' x = α⁻¹ * β (α * x * α⁻¹) * α := fun x => by
      simp [hβ''def, MulAut.mul_apply, MulAut.conj_apply]
    have hβ''A : ∀ M, β'' (ι M) = (tauAut σ ^ e') (ι M) := by
      intro M
      have h1 : ρ (a * M * a⁻¹) = a * Matrix.SpecialLinearGroup.map s.toRingHom M * a⁻¹ := by
        rw [has]
        have : a⁻¹ * (a * M * a⁻¹) * a = M := by group
        rw [this]
      have hιconj : ι (a * M * a⁻¹) = α * ι M * α⁻¹ := by rw [map_mul, map_mul, map_inv]
      have hιρ : ι (ρ (a * M * a⁻¹)) = α * (tauAut σ ^ e') (ι M) * α⁻¹ := by
        rw [h1, map_mul, map_mul, map_inv, hse, ← triOdd_chart_tauPow σ ι hιτ e' M]
      have h2 : β (α * ι M * α⁻¹) = α * (tauAut σ ^ e') (ι M) * α⁻¹ := by
        rw [← hιconj, ← hρι]
        exact hιρ
      rw [hβ''apply, h2]
      group
    set g'' : C0 σ := α⁻¹ * g₀ * (tauAut σ ^ e) α with hg''
    have hβ''eq : β'' = MulAut.conj g'' * tauAut σ ^ e := by
      have hc : tauAut σ ^ e * MulAut.conj α * (tauAut σ ^ e)⁻¹ =
          MulAut.conj ((tauAut σ ^ e) α) := aut_conj_conj _ α
      calc β'' = MulAut.conj α⁻¹ * MulAut.conj g₀ *
            (tauAut σ ^ e * MulAut.conj α * (tauAut σ ^ e)⁻¹) * tauAut σ ^ e := by
              rw [hβ''def, hβdef]; group
        _ = MulAut.conj g'' * tauAut σ ^ e := by
              rw [hc, ← map_mul, ← map_mul]
    have hζfix : ∀ y ∈ Asub σ, (tauAut σ ^ (3 - e') * β'') y = y := by
      intro y hy
      obtain ⟨M, rfl⟩ := (hιA y).1 hy
      rw [MulAut.mul_apply, hβ''A, ← MulAut.mul_apply, ← pow_add,
        show 3 - e' + e' = 3 by omega, hτ3]
      rfl
    have hζeq : tauAut σ ^ (3 - e') * β'' = MulAut.conj ((tauAut σ ^ (3 - e')) g'') *
        fieldActor (t := TwistTag.D4) σ (σ ^ ((3 - e') + e)) := by
      rw [triOdd_fieldActor_pow, pow_add, hβ''eq]
      have hc := aut_conj_conj (tauAut σ ^ (3 - e')) g''
      calc tauAut σ ^ (3 - e') * (MulAut.conj g'' * tauAut σ ^ e)
          = (tauAut σ ^ (3 - e') * MulAut.conj g'' * (tauAut σ ^ (3 - e'))⁻¹) *
              (tauAut σ ^ (3 - e') * tauAut σ ^ e) := by group
        _ = _ := by rw [hc]
    have hδ3 : (σ ^ ((3 - e') + e)) ^ 3 = 1 := by rw [← pow_mul, mul_comm, pow_mul, hσ3, one_pow]
    have hδ1 := triOdd_fieldActor_fix_A σ hℓ hℓ2 hℓ3 hf hX hσ ((tauAut σ ^ (3 - e')) g'')
      (σ ^ ((3 - e') + e)) hδ3 (fun y hy => by rw [← hζeq]; exact hζfix y hy)
    have hee : e = e' := by
      rcases he with rfl | rfl <;> rcases he' with rfl | rfl
      · rfl
      · exfalso
        exact hσ2 (by simpa using hδ1)
      · exfalso
        apply hσ1
        have h4 : σ ^ 4 = σ := by rw [show (4 : ℕ) = 3 + 1 from rfl, pow_succ, hσ3, one_mul]
        rw [← h4]
        simpa using hδ1
      · rfl
    subst hee
    set u : C0 σ := (tauAut σ ^ (3 - e)) g'' with hudef
    have hζconj : tauAut σ ^ (3 - e) * β'' = MulAut.conj u := by
      rw [hζeq, show 3 - e + e = 3 by omega, hσ3, fieldActor_one, mul_one]
    have huB : u ∈ Bsub σ := by
      refine Subgroup.mem_centralizer_iff.2 fun y hy => ?_
      have h1 := hζfix y hy
      rw [hζconj, MulAut.conj_apply] at h1
      calc y * u = (u * y * u⁻¹) * u := by rw [h1]
        _ = u * y := by group
    have hβ''u : β'' = MulAut.conj u * tauAut σ ^ e := by
      have h1 : β'' = tauAut σ ^ e * (tauAut σ ^ (3 - e) * β'') := by
        rw [← mul_assoc, ← pow_add, show e + (3 - e) = 3 by omega, hτ3, one_mul]
      rw [h1, hζconj]
      have hc := aut_conj_conj (tauAut σ ^ e) u
      rw [triOdd_tauPow_apply_B σ hBτ e huB] at hc
      calc tauAut σ ^ e * MulAut.conj u
          = (tauAut σ ^ e * MulAut.conj u * (tauAut σ ^ e)⁻¹) * tauAut σ ^ e := by group
        _ = MulAut.conj u * tauAut σ ^ e := by rw [hc]
    have hcα : Commute (MulAut.conj b) (MulAut.conj α⁻¹) := by
      show MulAut.conj b * MulAut.conj α⁻¹ = MulAut.conj α⁻¹ * MulAut.conj b
      rw [← map_mul, ← map_mul]
      congr 1
      calc b * α⁻¹ = α⁻¹ * (α * b) * α⁻¹ := by group
        _ = α⁻¹ * (b * α) * α⁻¹ := by rw [hαb]
        _ = α⁻¹ * b := by group
    have hcα' : Commute (MulAut.conj b) (MulAut.conj α) := by
      show MulAut.conj b * MulAut.conj α = MulAut.conj α * MulAut.conj b
      rw [← map_mul, ← map_mul, hαb.symm]
    have hcomm'' : Commute (MulAut.conj b) β'' := by
      rw [hβ''def]
      exact (hcα.mul_right hcomm).mul_right hcα'
    have hbu : b * u = u * b :=
      triOdd_comm_of_commute σ hZ (triOdd_tauPow_apply_B σ hBτ e hbB) (hβ''u ▸ hcomm'')
    have hβ''3 : β'' ^ 3 = 1 := by
      have hc : β'' = (MulAut.conj α)⁻¹ * β * ((MulAut.conj α)⁻¹)⁻¹ := by
        rw [hβ''def, map_inv, inv_inv]
      rw [hc, conj_pow, hβ3]
      group
    have hu3 : u ^ 3 = 1 := by
      have h1 : (MulAut.conj u * tauAut σ ^ e) ^ 3 = 1 := by rw [← hβ''u]; exact hβ''3
      rw [triOdd_conj_mul_pow_three σ u _ hφ3, triOdd_tauPow_apply_B σ hBτ e huB,
        triOdd_tauPow_apply_B σ hBτ e huB] at h1
      have h2 := hinj (h1.trans (map_one _).symm)
      simpa [pow_succ, mul_assoc] using h2
    have hz : u ∈ Subgroup.zpowers b :=
      triOdd_bsub_zpowers σ hℓ hℓ2 hℓ3 hf hX hσ b hbB u huB hb3 hb1 hu3 hbu
    obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.1 hz
    apply triOdd_hasGLine_map σ (MulAut.conj α⁻¹) E
    set E' := E.map (MulAut.congr (MulAut.conj α⁻¹)).toMonoidHom with hE'
    have hcb' : MulAut.conj b ∈ E' := by
      refine ⟨MulAut.conj b, hcb, ?_⟩
      show (MulAut.congr (MulAut.conj α⁻¹)) (MulAut.conj b) = MulAut.conj b
      rw [congr_apply_eq, ← hcα.eq]
      group
    have hβ''E' : β'' ∈ E' := by
      refine ⟨β, hβE, ?_⟩
      show (MulAut.congr (MulAut.conj α⁻¹)) β = β''
      rw [congr_apply_eq, hβ''def, map_inv, inv_inv]
    have hτe' : tauAut σ ^ e ∈ E' := by
      have h1 : tauAut σ ^ e = (MulAut.conj u)⁻¹ * β'' := by rw [hβ''u]; group
      rw [h1]
      refine mul_mem (inv_mem ?_) hβ''E'
      have h2 : MulAut.conj u = (MulAut.conj b) ^ m := by rw [← hm, map_zpow]
      rw [h2]
      exact zpow_mem hcb' m
    have hτ' : tauAut σ ∈ E' := by
      rcases he with rfl | rfl
      · simpa using hτe'
      · have h4 : tauAut σ = (tauAut σ ^ 2) ^ 2 := by
          rw [← pow_mul, show 2 * 2 = 3 + 1 from rfl, pow_succ, hτ3, one_mul]
        rw [h4]
        exact pow_mem hτe' 2
    exact ⟨tauAut σ, hτ', 1, Or.inl (by simp)⟩

theorem triOddYGLine : TriOddYGLine := by
  intro ℓ f hℓ hℓ2 hℓ3 hf K _ _ hK σ hσ E x hE hcard hout hx3 hx1 hcx hY
  classical
  obtain ⟨h, hh⟩ := hY
  obtain ⟨-, -, -, -, -, -, hZ, -⟩ := odd_triality_exact_automorphism_normal_form hℓ hℓ2 hf K hK σ hσ
  have hinj : Function.Injective (MulAut.conj : C0 σ →* MulAut (C0 σ)) := nf1_conj_injective hZ
  set b : C0 σ := h * x * h⁻¹ with hbdef
  have hb3 : b ^ 3 = 1 := by rw [hbdef, conj_pow, hx3]; group
  have hb1 : b ≠ 1 := fun h1 => hx1 (by
    have : x = h⁻¹ * b * h := by rw [hbdef]; group
    rw [this, h1]; group)
  set E' : Subgroup (MulAut (C0 σ)) := E.map (MulAut.congr (MulAut.conj h)).toMonoidHom with hE'def
  have hE' : CFSG.IsElementaryAbelian 3 E' := isElementaryAbelian_map_three hE _
  haveI : Finite E := Nat.finite_of_card_ne_zero (by rw [hcard]; norm_num)
  have hcard' : Nat.card E' = 3 ^ 2 := by
    rw [hE'def, Subgroup.card_map_of_injective (MulAut.congr (MulAut.conj h)).injective, hcard]
  have hout' : ¬ E' ≤ innerAut (C0 σ) := by
    intro hle
    apply hout
    intro ψ hψ
    have hmem : (MulAut.congr (MulAut.conj h)).toMonoidHom ψ ∈ innerAut (C0 σ) := hle ⟨ψ, hψ, rfl⟩
    obtain ⟨g, hg⟩ := hmem
    refine ⟨h⁻¹ * g * h, ?_⟩
    have h1 : MulAut.conj h * ψ * (MulAut.conj h)⁻¹ = MulAut.conj g :=
      (congr_apply_eq (MulAut.conj h) ψ).symm.trans hg.symm
    have h2 : ψ = (MulAut.conj h)⁻¹ * MulAut.conj g * MulAut.conj h := by
      rw [← h1]; group
    rw [h2, ← map_inv, ← map_mul, ← map_mul]
  have hcb' : MulAut.conj b ∈ E' := by
    refine ⟨MulAut.conj x, hcx, ?_⟩
    show (MulAut.congr (MulAut.conj h)) (MulAut.conj x) = MulAut.conj b
    rw [congr_apply_eq, hbdef, map_mul, map_mul, map_inv]
  have key := triOdd_hasGLine_of_mem_B σ hℓ hℓ2 hℓ3 hf hK hσ E' hE' hcard' hout' b hb3 hb1 hh hcb'
  exact triOdd_hasGLine_map σ (MulAut.conj h) E key

theorem trialityThreePlanesOdd_of_X (hX : TriOddXNoG) : TrialityThreePlanesOdd :=
  trialityThreePlanesOdd_of_open triOddYGLine hX

end Main

end CFSG.LieType.SeitzGeneration.ExcWideThree
