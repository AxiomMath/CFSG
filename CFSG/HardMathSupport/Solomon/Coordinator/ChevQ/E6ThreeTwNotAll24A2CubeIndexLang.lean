module

public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeTwNotAll24A2CubeShape
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.TwCompSU
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeTwNotAll24A2CubeClass
public import CFSG.HardMathSupport.Solomon.Coordinator.LayerCentralFix

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three

namespace KSNotAll24

open CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Steinberg.Adjoint CFSG.LieType.AlgebraicGroups
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.HardMathSupport.Dickson.Sec6
  CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.TwE6UniqAbs
open scoped MatrixGroups

set_option linter.unusedSectionVars false

section Cyc

theorem a2ci_iterHom_fixed {G : Type*} [Group G] {F : G →* G} {x : G} (hx : F x = x) (n : ℕ) :
    iterHom F n x = x := by
  induction n with
  | zero => rfl
  | succ n ih => rw [iterHom_succ, ih, hx]

theorem a2ci_val_sub_one_succ {s : ℕ} [NeZero s] (k : ZMod s) :
    (k - 1).val + 1 = if k = 0 then s else k.val := by
  have h := CycFamily.val_sub_one_succ_mod k
  have hlt := ZMod.val_lt (k - 1)
  split_ifs with hk
  · subst hk
    rw [ZMod.val_zero] at h
    rcases Nat.lt_or_ge ((0 - 1 : ZMod s).val + 1) s with h' | h'
    · rw [Nat.mod_eq_of_lt h'] at h
      omega
    · omega
  · rcases Nat.lt_or_ge ((k - 1).val + 1) s with h' | h'
    · rwa [Nat.mod_eq_of_lt h'] at h
    · exfalso
      have e : (k - 1).val + 1 = s := by omega
      rw [e, Nat.mod_self] at h
      exact hk ((ZMod.val_eq_zero k).1 h.symm)

variable {G : Type*} [Group G] {F : G →* G} {s : ℕ} [NeZero s] (P : CycFamily F s)

theorem a2ci_F_norm (y : P.S 0) :
    F (P.norm y) = (iterHom F s (y : G) * (y : G)⁻¹) * P.norm y := by
  classical
  have hc : iterHom F s (y : G) * (y : G)⁻¹ ∈ P.S 0 :=
    mul_mem (P.iterHom_s_mem y.2) (inv_mem y.2)
  have hsh : P.shift (P.diag y) =
      Pi.mulSingle (M := fun j => P.S j) 0 ⟨_, hc⟩ * P.diag y := by
    funext k
    apply Subtype.ext
    rw [P.coe_shift_apply, CycFamily.coe_diag_apply, ← iterHom_succ, a2ci_val_sub_one_succ]
    simp only [Pi.mul_apply, Subgroup.coe_mul, CycFamily.coe_diag_apply]
    split_ifs with hk
    · subst hk
      rw [P.val_mulSingle_of_eq rfl, ZMod.val_zero, iterHom_zero, inv_mul_cancel_right]
    · rw [P.val_mulSingle_of_ne hk, one_mul]
  show F (P.mu (P.diag y)) = _ * P.mu (P.diag y)
  rw [P.F_mu, hsh, map_mul, P.mu_mulSingle]

theorem a2ci_mem_of_mem_Z (H : Subgroup G)
    (hH : ∀ k, ∀ g ∈ P.S k, (∀ x ∈ P.S k, g * x = x * g) → g ∈ H) {ζ : G} (hζZ : ζ ∈ P.Z)
    (hζA : ζ ∈ P.A) : ζ ∈ H := by
  classical
  obtain ⟨f, rfl⟩ := P.mem_A_iff.1 hζA
  have hcomm : ∀ k, ∀ x ∈ P.S k, (f k : G) * x = x * (f k : G) := by
    intro k x hx
    have hf' : f = Pi.mulSingle k (f k) * Function.update f k 1 := by
      funext j
      by_cases hj : j = k
      · subst hj
        simp
      · simp [Pi.mul_apply, Pi.mulSingle_eq_of_ne hj, Function.update_of_ne hj]
    set m := P.mu (Function.update f k 1) with hm
    have hmu : P.mu f = (f k : G) * m := by
      conv_lhs => rw [hf', map_mul, P.mu_mulSingle]
    have c1 : m * x = x * m := by
      have h := P.commute_mu_of_commute (Function.update f k 1)
        (Pi.mulSingle k ⟨x, hx⟩) (by
          funext j
          by_cases hj : j = k
          · subst hj
            simp
          · simp [Pi.mul_apply, Pi.mulSingle_eq_of_ne hj])
      rw [P.mu_mulSingle] at h
      exact h.eq
    have c2 : x * P.mu f = P.mu f * x := (P.mem_Z.1 hζZ) x (P.S_le_A k hx)
    rw [hmu] at c2
    have e : x * (f k : G) * m = (f k : G) * x * m := by
      rw [mul_assoc, c2, mul_assoc, c1, ← mul_assoc]
    exact (mul_right_cancel e).symm
  unfold CycFamily.mu
  rw [Subgroup.noncommPiCoprod_apply]
  exact Subgroup.noncommProd_mem _ _ fun k _ => hH k _ (f k).2 (hcomm k)

end Cyc

section Centre

variable {L : Type} [Field L]

theorem a2ci_pow_three_of_mem_center {X : SL(3, L)} (hX : X ∈ Subgroup.center SL(3, L)) :
    X ^ 3 = 1 := by
  rw [Matrix.SpecialLinearGroup.mem_center_iff] at hX
  obtain ⟨r, hr3, hrX⟩ := hX
  rw [Fintype.card_fin] at hr3
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_pow, ← hrX, ← map_pow, hr3, map_one,
    Matrix.SpecialLinearGroup.coe_one]

theorem a2ci_eq_pow_of_mem_center {X Y : SL(3, L)} (hX : X ∈ Subgroup.center SL(3, L))
    (hY : Y ∈ Subgroup.center SL(3, L)) (hY1 : Y ≠ 1) : ∃ m : ℕ, m < 3 ∧ X = Y ^ m := by
  rw [Matrix.SpecialLinearGroup.mem_center_iff] at hX hY
  obtain ⟨r, hr3, hrX⟩ := hX
  obtain ⟨u, hu3, huY⟩ := hY
  rw [Fintype.card_fin] at hr3 hu3
  have hu1 : u ≠ 1 := by
    rintro rfl
    apply hY1
    apply Subtype.ext
    rw [← huY, map_one, Matrix.SpecialLinearGroup.coe_one]
  have hsum : u ^ 2 + u + 1 = 0 := by
    have h : (u - 1) * (u ^ 2 + u + 1) = 0 := by linear_combination hu3
    exact (mul_eq_zero.1 h).resolve_left (sub_ne_zero.2 hu1)
  have hprod : (r - 1) * (r - u) * (r - u ^ 2) = 0 := by
    linear_combination hr3 + (r - r ^ 2) * hsum + (r - 1) * hu3
  have hpow : ∀ m : ℕ, ((Y ^ m : SL(3, L)) : Matrix (Fin 3) (Fin 3) L) =
      Matrix.scalar (Fin 3) (u ^ m) := by
    intro m
    rw [Matrix.SpecialLinearGroup.coe_pow, ← huY, map_pow]
  rcases mul_eq_zero.1 hprod with h | h
  · rcases mul_eq_zero.1 h with h | h
    · refine ⟨0, by norm_num, Subtype.ext ?_⟩
      rw [hpow, ← hrX, pow_zero, sub_eq_zero.1 h]
    · refine ⟨1, by norm_num, Subtype.ext ?_⟩
      rw [hpow, ← hrX, pow_one, sub_eq_zero.1 h]
  · refine ⟨2, by norm_num, Subtype.ext ?_⟩
    rw [hpow, ← hrX, sub_eq_zero.1 h]

theorem a2ci_frame_center {G : Type*} [Group G] (ψ : SL(3, L) →* G) {d : G} (hd : d ∈ ψ.range)
    (hdc : ∀ Y, d * ψ Y = ψ Y * d) (hd1 : d ≠ 1) :
    d ^ 3 = 1 ∧ Function.Injective ψ ∧
      ∀ g ∈ ψ.range, (∀ Y, g * ψ Y = ψ Y * g) → g ∈ Subgroup.zpowers d := by
  obtain ⟨Xd, rfl⟩ := hd
  have hker : ψ.ker ≠ ⊤ := fun h => hd1 (by
    have h' : Xd ∈ ψ.ker := h ▸ Subgroup.mem_top Xd
    exact h')
  have hXd : Xd ∈ Subgroup.center SL(3, L) := mem_center_SL_of_commute le_rfl ψ hker hdc
  have hXd1 : Xd ≠ 1 := by
    rintro rfl
    exact hd1 (map_one ψ)
  have hd3 : ψ Xd ^ 3 = 1 := by rw [← map_pow, a2ci_pow_three_of_mem_center hXd, map_one]
  refine ⟨hd3, ?_, ?_⟩
  · rw [injective_iff_map_eq_one]
    intro X hX
    have hXc : X ∈ Subgroup.center SL(3, L) :=
      mem_center_SL_of_commute le_rfl ψ hker fun Y => by rw [hX, one_mul, mul_one]
    obtain ⟨m, hm, rfl⟩ := a2ci_eq_pow_of_mem_center hXc hXd hXd1
    rw [map_pow] at hX
    interval_cases m
    · exact pow_zero _
    · exact absurd (by simpa using hX) hd1
    · exfalso
      apply hd1
      calc ψ Xd = ψ Xd ^ 3 * (ψ Xd ^ 2)⁻¹ := by group
        _ = 1 := by rw [hd3, hX, inv_one, mul_one]
  · rintro _ ⟨X, rfl⟩ hXc
    have hXc' : X ∈ Subgroup.center SL(3, L) := mem_center_SL_of_commute le_rfl ψ hker hXc
    obtain ⟨m, -, rfl⟩ := a2ci_eq_pow_of_mem_center hXc' hXd hXd1
    rw [map_pow]
    exact Subgroup.npow_mem_zpowers _ m

end Centre

section Torus


variable {τ : Tag} {L : Type} [Field L]

theorem a2ci_rootTorusSL2_eq {β : Fin τ.rank → ℤ} (hβ : IsRoot τ β) (c : Lˣ) :
    rootTorusSL2 τ L β c =
      rootDiagUnit τ (fun i => c ^ (2 * iform β (Pi.single i 1) / iform β β)) := by
  obtain ⟨-, hdH, -, -, hact, -, -, -⟩ := exceptional_Lang_root_rank_one_torus_transport τ L hβ
  obtain ⟨a, ha⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup (hdH c)
  rw [ha]
  congr 1
  funext i
  have h1 := (hact c).2 (Pi.single i 1) (isRoot_single τ i)
  rw [ha] at h1
  have h2 : (((rootDiagUnit τ a : ModGL τ L) : Module.End L (RootModule τ L))
      (rootVec τ L (Pi.single i 1))) = ((a i : Lˣ) : L) • rootVec τ L (Pi.single i 1) := by
    change rootDiag a (rootVec τ L (Pi.single i 1)) = _
    have hs : rootChar a (Pi.single i 1 : Fin τ.rank → ℤ) = a i := by
      have := rootChar_nsmul_single a i 1
      rwa [one_smul, pow_one] at this
    rw [rootDiag_rootVec _ (isRoot_single τ i), hs]
  rw [h2] at h1
  have hne : rootVec τ L (Pi.single i 1) ≠ 0 := by
    rw [rootVec_eq_single_of_isRoot (isRoot_single τ i)]
    exact Finsupp.single_ne_zero.2 one_ne_zero
  exact Units.ext (smul_left_injective L hne h1)

theorem a2ci_rootTorusSL2_mem_rootSpan {S : Set (Fin τ.rank → ℤ)} {β : Fin τ.rank → ℤ}
    (hβ : IsRoot τ β) (h₁ : β ∈ S) (h₂ : -β ∈ S) (c : Lˣ) :
    rootTorusSL2 τ L β c ∈ rootSpan τ L S := by
  have hR := (exceptional_Lang_root_rank_one_torus_transport τ L hβ).1
  have hmem : rootTorusSL2 τ L β c ∈ rootRankOneGroup τ L β := ⟨_, rfl⟩
  rw [hR] at hmem
  have hle : ∀ γ ∈ S, rootSubgroup τ L γ ≤ rootSpan τ L S := fun γ hγ =>
    le_iSup₂ (f := fun γ (_ : γ ∈ S) => rootSubgroup τ L γ) γ hγ
  exact sup_le (hle β h₁) (hle (-β) h₂) hmem

theorem a2ci_rootDiagUnit_mem_rootSpan {a : Fin Tag.E6.rank → Lˣ} (ha : ∀ j, a j ^ 3 = 1)
    (h1 : rootDiagUnit Tag.E6 a ≠ 1) (i : KernelComponent (rootCharHom a))
    (hi6 : (componentRoots (rootCharHom a) i).ncard = 6) :
    rootDiagUnit Tag.E6 a ∈ rootSpan Tag.E6 L (componentRoots (rootCharHom a) i) := by
  obtain ⟨γ₁, γ₂, hP, hΨeq, hglueAll⟩ := Up34Exc.RD.glue_of_check2 Up34Exc.RD.noG2_E6 73
    Up34Exc.RD.okE6 (by norm_num) Up34Exc.RD.rdCheck2_E6 a ha i hi6
  have ha1 : ∃ j, a j ≠ 1 := by
    by_contra hcon
    push Not at hcon
    apply h1
    have : a = 1 := funext hcon
    rw [this, CFSG.LieType.Chevalley.rootDiagUnit_one]
  obtain ⟨j0, hj0⟩ := ha1
  obtain ⟨ε, -, hglue⟩ := hglueAll (a j0) (ha j0) hj0
  obtain ⟨hγ₁, hγ₂, -, -⟩ := hP
  have hsplit : a = (fun j => (a j0 ^ ε) ^ (2 * iform γ₁ (Pi.single j 1) / iform γ₁ γ₁)) *
      (fun j => (a j0 ^ (2 * ε)) ^ (2 * iform γ₂ (Pi.single j 1) / iform γ₂ γ₂)) := by
    funext j
    rw [Pi.mul_apply, ← zpow_mul, ← zpow_mul, ← zpow_add]
    conv_lhs => rw [hglue j]
    congr 1
    change ε * (corootPair γ₁ (Pi.single j 1 : Fin Tag.E6.rank → ℤ) +
      2 * corootPair γ₂ (Pi.single j 1 : Fin Tag.E6.rank → ℤ)) = _
    unfold corootPair
    ring
  have hd : rootDiagUnit Tag.E6 a = rootTorusSL2 Tag.E6 L γ₁ (a j0 ^ ε) *
      rootTorusSL2 Tag.E6 L γ₂ (a j0 ^ (2 * ε)) := by
    rw [a2ci_rootTorusSL2_eq hγ₁, a2ci_rootTorusSL2_eq hγ₂, ← rootDiagUnit_mul]
    exact congrArg (rootDiagUnit Tag.E6) hsplit
  rw [hd]
  refine mul_mem (a2ci_rootTorusSL2_mem_rootSpan hγ₁ ?_ ?_ _)
    (a2ci_rootTorusSL2_mem_rootSpan hγ₂ ?_ ?_ _) <;> rw [hΨeq] <;> simp

end Torus

section Unitary

open CFSG.LocalAnalysis.ComponentInitial Matrix CFSG.RankThree.Classical
  CFSG.RankThree.Classical2 CFSG.SectionRank.OddCover
open scoped commutatorElement


variable {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] {p : ℕ} (S : LangSetup τ L p)
  {ta : Fin τ.rank → Lˣ}

theorem a2ci_exists_unitary_fixed (hT : rootDiagUnit τ ta ∈ S.D.torus)
    (i : KernelComponent (rootCharHom ta)) {ν : ℕ} (hν : 3 ≤ ν)
    {ψ : SL(ν, L) →* ModGL τ L} {σ : Fin ν → Fin ν → Fin τ.rank → ℤ} (hψ : IsSLFrame ψ σ)
    (hψinj : Function.Injective ψ)
    (hΨ : componentRoots (rootCharHom ta) i = frameRoots σ) (π : Equiv.Perm (Fin ν))
    (hπ : ∀ a b, a ≠ b → (S.ρ : (Fin τ.rank → ℤ) → _)^[componentOrbitLength S.ρ
      (componentRoots (rootCharHom ta) i)] (σ a b) = σ (π b) (π a))
    (hQne : (ν, S.D.q ^ componentOrbitLength S.ρ (componentRoots (rootCharHom ta) i)) ≠ (3, 2)) :
    ∃ (H : Subgroup SL(ν, L)) (θ : H →* ModGL τ L), Group.IsPerfect H ∧
      (∀ c, θ c ∈ rootSpan τ L (componentRoots (rootCharHom ta) i)) ∧
      (∀ c, iterHom S.D.step (componentOrbitLength S.ρ (componentRoots (rootCharHom ta) i))
        (θ c) = θ c) ∧
      ∀ g ∈ rootSpan τ L (componentRoots (rootCharHom ta) i),
        iterHom S.D.step (componentOrbitLength S.ρ (componentRoots (rootCharHom ta) i)) g = g →
          ∃ c, θ c = g := by
  classical
  obtain ⟨hs0, -, -⟩ := outer_componentOrbitLength_spec S hT i
  set s := componentOrbitLength S.ρ (componentRoots (rootCharHom ta) i) with hsdef
  obtain ⟨r, e, hr, hchar, he, hq⟩ := exists_char_pow S
  have : Fact r.Prime := ⟨hr⟩
  have : CharP L r := hchar
  obtain ⟨σQ, hσQ⟩ := exists_ringEquiv_frob (L := L) r (e * s)
  have hσc : ∀ c, σQ c = c ^ (r ^ (e * s)) := fun c => by
    have h1 : σQ c = iterateFrobenius L r (e * s) c := by
      rw [← hσQ]
      rfl
    rw [h1, iterateFrobenius_def]
  have hQ : S.D.q ^ s = r ^ (e * s) := by rw [hq, ← pow_mul]
  set Fs : ModGL τ L →* ModGL τ L := iterHom S.D.step s with hFs
  choose! ε hε using fun (a b : Fin ν) (hab : a ≠ b) => hψ.transv a b hab
  have hπne : ∀ a b : Fin ν, a ≠ b → π b ≠ π a := fun a b hab => (π.injective.ne hab).symm
  have hstepU : ∀ a b : Fin ν, a ≠ b → ∃ μ : Lˣ, ∀ c : L,
      Fs (pinnedX τ L (σ a b) c) = pinnedX τ L (σ (π b) (π a)) ((μ : L) * σQ c) := by
    intro a b hab
    obtain ⟨μ, hμ0, hμ⟩ := iter_step_pinnedX S s (hψ.isRoot a b hab)
    refine ⟨Units.mk0 μ hμ0, fun c => ?_⟩
    rw [hFs, iterHom_eq_iterate, hμ, hπ a b hab, hσc, ← hQ]
    rfl
  choose! μ hμ using hstepU
  set β : Fin ν → Fin ν → Lˣ := fun a b =>
    μ a b * ε a b ^ (r ^ (e * s)) * (ε (π b) (π a))⁻¹ with hβ
  have hkey : ∀ (a b : Fin ν) (hab : a ≠ b) (t : L),
      Fs (ψ (Matrix.SpecialLinearGroup.transvection hab t)) =
        ψ (Matrix.SpecialLinearGroup.transvection (hπne a b hab) ((β a b : L) * σQ t)) := by
    intro a b hab t
    rw [hε a b hab t, hμ a b hab, hε (π b) (π a) (hπne a b hab)]
    congr 1
    rw [map_mul, hσc (ε a b : L), hβ]
    simp only [Units.val_mul, Units.val_pow_eq_pow_val, Units.val_inv_eq_inv_val]
    have h0 : (ε (π b) (π a) : L) ≠ 0 := Units.ne_zero _
    field_simp
  have hcoc : ∀ a b c : Fin ν, a ≠ b → b ≠ c → a ≠ c → β a c = -(β a b * β b c) := by
    intro a b c hab hbc hac
    have hcomm := Matrix.SpecialLinearGroup.commutatorElement_transvection hab hbc hac (1 : L) 1
    rw [mul_one] at hcomm
    have h1 := congrArg (fun X => Fs (ψ X)) hcomm
    simp only [map_commutatorElement] at h1
    rw [hkey a b hab, hkey b c hbc, hkey a c hac, map_one, mul_one, mul_one, mul_one,
      ← map_commutatorElement ψ,
      commutator_transvection_rev (hπne a b hab) (hπne b c hbc) (hπne a c hac),
      hε _ _ (hπne a c hac), hε _ _ (hπne a c hac)] at h1
    have h2 := pinnedX_injective τ L _ h1
    have h0 : (ε (π c) (π a) : L) ≠ 0 := Units.ne_zero _
    apply Units.ext
    have h3 := mul_left_cancel₀ h0 h2
    rw [Units.val_neg, Units.val_mul]
    exact h3.symm
  obtain ⟨d, hd⟩ := exists_units_of_cocycle hν β hcoc
  set M : GL (Fin ν) L := diagHom ν d * (permGL π : GL (Fin ν) L)⁻¹ with hMdef
  obtain ⟨B, hB⟩ := exists_specialLinear_conj_eq (n := ν) (by omega) M
  have hBconj : ∀ (a b : Fin ν) (hab : a ≠ b) (u : L),
      B * Matrix.SpecialLinearGroup.transvection (hπne a b hab) u * B⁻¹ =
        Matrix.SpecialLinearGroup.transvection (Ne.symm hab) ((d b : L) * u * ((d a)⁻¹ : Lˣ)) := by
    intro a b hab u
    apply Subtype.ext
    rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul,
      Matrix.SpecialLinearGroup.transvection_coe, Matrix.SpecialLinearGroup.transvection_coe, hB]
    have hM : ∀ Y : Matrix (Fin ν) (Fin ν) L, (M : Matrix (Fin ν) (Fin ν) L) * Y *
        (↑M⁻¹ : Matrix (Fin ν) (Fin ν) L) = (diagHom ν d : Matrix (Fin ν) (Fin ν) L) *
          ((↑(permGL π : GL (Fin ν) L)⁻¹ : Matrix (Fin ν) (Fin ν) L) * Y *
            ((permGL π : GL (Fin ν) L) : Matrix (Fin ν) (Fin ν) L)) *
              (↑(diagHom ν d)⁻¹ : Matrix (Fin ν) (Fin ν) L) := by
      intro Y
      simp only [hMdef, _root_.mul_inv_rev, inv_inv, Units.val_mul, Matrix.mul_assoc]
    rw [hM, Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, Units.inv_mul,
      permGL_inv_mul_single_mul, diagHom_mul_one_add_single_mul d (Ne.symm hab) u]
  have hstd : ∀ X : SL(ν, L), ψ B * Fs (ψ X) * (ψ B)⁻¹ = ψ (stdUnitary σQ.toRingHom X) := by
    have h : (MulAut.conj (ψ B)).toMonoidHom.comp (Fs.comp ψ) =
        ψ.comp (stdUnitary σQ.toRingHom) := by
      refine MonoidHom.eq_of_eqOn_dense
        (CFSG.LinearGroups.special_linear_elementary_generation (n := ν) (K := L)) ?_
      rintro _ ⟨a, b, hab, t, rfl⟩
      simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      rw [hkey a b hab t, ← map_mul, ← map_inv, ← map_mul, hBconj a b hab,
        stdUnitary_transvection]
      congr 2
      rw [hd a b hab]
      simp only [Units.val_neg, Units.val_mul, Units.val_inv_eq_inv_val,
        RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom]
      have h0 : (d a : L) ≠ 0 := Units.ne_zero _
      have h0' : (d b : L) ≠ 0 := Units.ne_zero _
      field_simp
    intro X
    have := DFunLike.congr_fun h X
    simpa [MulAut.conj_apply] using this
  have hψS : ∀ X, ψ X ∈ rootSpan τ L (componentRoots (rootCharHom ta) i) := fun X => by
    rw [hΨ, ← hψ.range]
    exact ⟨X, rfl⟩
  have hy₁ : ψ B ∈ rootSpan τ L (kernelRoots (rootCharHom ta)) :=
    rootSpan_mono (fun γ hγ => hγ.1) (hψS B)
  obtain ⟨z, hz, hnorm⟩ := exists_lang_mul_T S hT hs0 hy₁
  have hconj : ∀ X : SL(ν, L), Fs (z * ψ X * z⁻¹) = z * ψ (stdUnitary σQ.toRingHom X) * z⁻¹ := by
    intro X
    rw [← hstd X, map_mul, map_mul, map_inv, hz]
    group
  have hpre : ∀ g ∈ rootSpan τ L (componentRoots (rootCharHom ta) i),
      ∃ X : SL(ν, L), g = z * ψ X * z⁻¹ := by
    intro g hg
    have h1 : z⁻¹ * g * z ∈ rootSpan τ L (componentRoots (rootCharHom ta) i) := (hnorm i _).2 (by
      have e : z * (z⁻¹ * g * z) * z⁻¹ = g := by group
      rw [e]
      exact hg)
    rw [hΨ, ← hψ.range] at h1
    obtain ⟨X, hX⟩ := h1
    exact ⟨X, by rw [hX]; group⟩
  set C := fixSubgroup (stdUnitaryEquiv (ν := ν) σQ) with hCdef
  have hCmem : ∀ X : SL(ν, L), X ∈ C ↔ stdUnitary σQ.toRingHom X = X := fun X => by
    rw [hCdef, mem_fixSubgroup, stdUnitaryEquiv_apply]
  let θ : C →* ModGL τ L := (MulAut.conj z).toMonoidHom.comp (ψ.comp C.subtype)
  have hθ : ∀ c : C, θ c = z * ψ c * z⁻¹ := fun c => rfl
  obtain ⟨-, hqsC, -⟩ := stdUnitary_fixSubgroup (ν := ν) hr (Nat.mul_pos he hs0) σQ hσc hν
  refine ⟨C, θ, (hqsC (by rw [← hQ]; exact hQne)).1, fun c => ?_, fun c => ?_,
    fun g hg hgF => ?_⟩
  · rw [hθ]
    exact (hnorm i _).1 (hψS c)
  · rw [hθ, hconj, (hCmem c).1 c.2]
  · obtain ⟨X, rfl⟩ := hpre g hg
    rw [hconj] at hgF
    have h1 : ψ (stdUnitary σQ.toRingHom X) = ψ X := mul_left_cancel (mul_right_cancel hgF)
    exact ⟨⟨X, (hCmem X).2 (hψinj h1)⟩, rfl⟩

end Unitary

section Lang


theorem a2cube_inf_rootSpan_le_rationalComponent
    {L : Type} [Field L] [IsAlgClosed L] {p : ℕ} (S : LangSetup Tag.E6 L p)
    {ta : Fin Tag.E6.rank → Lˣ} (hT : rootDiagUnit Tag.E6 ta ∈ S.D.torus)
    (hap : ∀ j, ta j ^ 3 = 1) (h1 : rootDiagUnit Tag.E6 ta ≠ 1)
    (h3 : ((3 : ℕ) : L) ≠ 0)
    (h18 : (kernelRoots (rootCharHom ta)).ncard = 18)
    (hrat : ∀ i : KernelComponent (rootCharHom ta),
      componentOrbitLength S.ρ (componentRoots (rootCharHom ta) i) = 3 ∧
        rationalRoots S.ρ (rootCharHom ta) i = kernelRoots (rootCharHom ta))
    (h3q : 3 ∣ S.D.q + 1) (hout : rootDiagUnit Tag.E6 ta ∉ S.Γ)
    (i : KernelComponent (rootCharHom ta)) :
    S.Γ ⊓ rootSpan Tag.E6 L (kernelRoots (rootCharHom ta)) ≤
      rationalComponent S.ρ S.Γ (rootCharHom ta) i := by
  classical
  obtain ⟨c, hc, hc6⟩ := kernel_classes_of_ncard_eighteen h3 hap h18
  have hall6 : ∀ j, (componentRoots (rootCharHom ta) j).ncard = 6 := fun j => by
    obtain ⟨k, rfl⟩ := hc.2 j
    exact hc6 k
  obtain ⟨hs3, hratI⟩ := hrat i
  obtain ⟨hs0, hs, hmin⟩ := outer_componentOrbitLength_spec S hT i
  set s := componentOrbitLength S.ρ (componentRoots (rootCharHom ta) i) with hsdef
  haveI : NeZero s := ⟨hs0.ne'⟩
  set P := outerOrbitFamily S hT i hs hmin with hP
  have hPA : P.A = rootSpan Tag.E6 L (kernelRoots (rootCharHom ta)) := by
    rw [hP, outerOrbitFamily_A, hratI]
  have hP0 : P.S 0 = rootSpan Tag.E6 L (componentRoots (rootCharHom ta) i) := by
    rw [hP, outerOrbitFamily_S, ZMod.val_zero]
    simp only [Function.iterate_zero, id_eq, Set.image_id']
  set d := rootDiagUnit Tag.E6 ta with hd
  have hdF : S.D.step d = d := (Subgroup.mem_inf.1 hT).2
  have hdcomm : ∀ g ∈ rootSpan Tag.E6 L (kernelRoots (rootCharHom ta)), d * g = g * d :=
    fun g hg => (Subgroup.mem_centralizer_singleton_iff.1
      (rootSpan_le_centralizer ta (fun γ hγ => hγ) hg)).symm
  have hd0 : d ∈ P.S 0 := by
    rw [hP0]
    exact a2ci_rootDiagUnit_mem_rootSpan hap h1 i (hall6 i)
  have hdk : ∀ k : ZMod s, d ∈ P.S k := by
    intro k
    have h := P.iterHom_mem k.val hd0
    rwa [ZMod.natCast_zmod_val, a2ci_iterHom_fixed hdF] at h
  have hfr : ∀ (j : KernelComponent (rootCharHom ta)) (ψ : SL(3, L) →* ModGL Tag.E6 L)
      (σ : Fin 3 → Fin 3 → Fin Tag.E6.rank → ℤ), IsSLFrame ψ σ →
      componentRoots (rootCharHom ta) j = frameRoots σ →
      d ∈ rootSpan Tag.E6 L (componentRoots (rootCharHom ta) j) →
      d ^ 3 = 1 ∧ Function.Injective ψ ∧
        ∀ g ∈ rootSpan Tag.E6 L (componentRoots (rootCharHom ta) j),
          (∀ x ∈ rootSpan Tag.E6 L (componentRoots (rootCharHom ta) j), g * x = x * g) →
            g ∈ Subgroup.zpowers d := by
    intro j ψ σ hψ hΨ hdj
    have hrange : ψ.range = rootSpan Tag.E6 L (componentRoots (rootCharHom ta) j) := by
      rw [hΨ, hψ.range]
    have hψK : ∀ Y, ψ Y ∈ rootSpan Tag.E6 L (kernelRoots (rootCharHom ta)) := fun Y =>
      rootSpan_mono (componentRoots_subset_kernelRoots _ j) (hrange ▸ ⟨Y, rfl⟩)
    obtain ⟨hd3, hinj, hZ⟩ := a2ci_frame_center ψ (hrange ▸ hdj) (fun Y => hdcomm _ (hψK Y)) h1
    refine ⟨hd3, hinj, fun g hg hgc => hZ g (hrange ▸ hg) fun Y => hgc _ (hrange ▸ ⟨Y, rfl⟩)⟩
  have hcent : ∀ k : ZMod s, ∀ g ∈ P.S k, (∀ x ∈ P.S k, g * x = x * g) →
      g ∈ Subgroup.zpowers d := by
    intro k g hg hgc
    obtain ⟨j, hj⟩ := outer_iterate_image_component S hT i k.val
    have hSk : P.S k = rootSpan Tag.E6 L (componentRoots (rootCharHom ta) j) := by
      rw [hP, outerOrbitFamily_S, ← hj]
    obtain ⟨ψ, σ, hψ, -, hΨ⟩ := (kac_facts h3 hap).frame j (hall6 j)
    rw [hSk] at hg hgc
    exact (hfr j ψ σ hψ hΨ (hSk ▸ hdk k)).2.2 g hg hgc
  have hodd : s % 2 = 1 := by omega
  obtain ⟨ψ, σ, π, hψ, hΨ, hπ⟩ :=
    exists_unitary_frame_of_odd_orbit S h3 hT hap h1 i (hall6 i) hodd h3q
  obtain ⟨hd3, hψinj, -⟩ := hfr i ψ σ hψ hΨ (hP0 ▸ hd0)
  have hQne : (3, S.D.q ^ s) ≠ (3, 2) := by
    intro h
    have h2 : S.D.q ^ s = 2 := congrArg Prod.snd h
    have hq1 : 2 ≤ S.D.q := S.hqpow.1.two_le
    rw [hs3] at h2
    have h8 : 2 ^ 3 ≤ S.D.q ^ 3 := Nat.pow_le_pow_left hq1 3
    rw [h2] at h8
    norm_num at h8
  obtain ⟨H, θ, hHperf, hθS, hθfix, hθonto⟩ :=
    a2ci_exists_unitary_fixed S hT i le_rfl hψ hψinj hΨ π hπ hQne
  let θ₀ : H →* P.S 0 := θ.codRestrict (P.S 0) fun c => by
    rw [hP0]
    exact hθS c
  have hθ₀fix : ∀ x, iterHom S.D.step s ((θ₀ x : P.S 0) : ModGL Tag.E6 L) = θ₀ x :=
    fun x => hθfix x
  have hΓF : ∀ g ∈ S.Γ, S.D.step g = g := fun g hg =>
    (Subgroup.mem_inf.1 (Subgroup.commutator_le_self S.D.model hg)).2
  have hRΓ : rationalComponent S.ρ S.Γ (rootCharHom ta) i ≤ S.Γ :=
    (Subgroup.commutator_le_self _).trans inf_le_right
  intro x hx
  obtain ⟨hxΓ, hxA⟩ := Subgroup.mem_inf.1 hx
  have hxF : S.D.step x = x := hΓF x hxΓ
  rw [← hPA] at hxA
  obtain ⟨y, -, ζ, hζZ, hζA, rfl⟩ := P.exists_eq_zeta_norm hxA hxF
  have hζd : ζ ∈ Subgroup.zpowers d := a2ci_mem_of_mem_Z P _ hcent hζZ hζA
  have hζF : S.D.step ζ = ζ := by
    obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.1 hζd
    rw [map_zpow, hdF]
  have hyfix : iterHom S.D.step s (y : ModGL Tag.E6 L) = y := by
    rw [map_mul, hζF, a2ci_F_norm P y] at hxF
    have hc := mul_right_cancel ((mul_left_cancel hxF).trans (one_mul _).symm)
    exact mul_inv_eq_one.1 hc
  obtain ⟨c₀, hc₀⟩ := hθonto y (by rw [← hP0]; exact y.2) hyfix
  have hy' : y = θ₀ c₀ := Subtype.ext hc₀.symm
  have hNR : P.norm y ∈ rationalComponent S.ρ S.Γ (rootCharHom ta) i := by
    rw [hy']
    exact outer_norm_mem_rationalComponent S hT i hs hmin hHperf θ₀ hθ₀fix c₀
  have hζΓ : ζ ∈ S.Γ := by
    have h := mul_mem hxΓ (inv_mem (hRΓ hNR))
    rwa [mul_inv_cancel_right] at h
  have hζ1 : ζ = 1 := by
    haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    have hord : orderOf d = 3 := orderOf_eq_prime hd3 h1
    obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.1 hζd
    have hm : d ^ m = d ^ (m % 3) := by
      rw [← zpow_mod_orderOf, hord, Nat.cast_ofNat]
    have hr : m % 3 = 0 ∨ m % 3 = 1 ∨ m % 3 = 2 := by omega
    rcases hr with h | h | h
    · rw [hm, h, zpow_zero]
    · exfalso
      apply hout
      rw [hm, h, zpow_one] at hζΓ
      exact hζΓ
    · exfalso
      apply hout
      rw [hm, h] at hζΓ
      have e : (d ^ (2 : ℤ)) ^ 2 = d := by
        rw [zpow_ofNat, ← pow_mul, show 2 * 2 = 3 + 1 by rfl, pow_succ, hd3, one_mul]
      rw [← e]
      exact pow_mem hζΓ 2
  rw [hζ1, one_mul]
  exact hNR

end Lang

end KSNotAll24

end CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three
