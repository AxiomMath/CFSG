module

public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoHS.Le4.SAFxPGStage
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoHS.Le4.SAFyGHWr

public section

namespace CFSG.EvenSporadicStandard.TwoHS

open Subgroup Matrix

theorem card_fixedPoints_eq (A : SoMat5) (hA : IsSO5 A) :
    Fintype.card (Function.fixedPoints (MulAction.toPermHom PGSp45 OmegaPts (mkPG A hA))) =
      fixCount A := by
  unfold fixCount
  apply Fintype.card_congr
  exact Equiv.subtypeEquivRight fun v => by
    simp only [Function.mem_fixedPoints, Function.IsFixedPt, MulAction.toPermHom_apply,
      MulAction.toPerm_apply]
    rw [Subtype.ext_iff]
    rfl

theorem chiPG_mkPG (hchi : PGChi) (A : SoMat5) (hA : IsSO5 A) (hAA : A * A = 1) :
    chiPG (mkPG A hA) = (-1) ^ ((600 - fixCount A) / 2) := by
  have hg : mkPG A hA * mkPG A hA = 1 := pg_ext (by simpa using hAA)
  rw [chiPG_of_sq _ hg, card_fixedPoints_eq, hchi.1]

theorem pgRefl_so {k : ℕ} (hk : k < 4) : IsSO5 (pgRefl k) := by
  have := pg_sr_so (k : ZMod 4)
  rwa [ZMod.val_natCast_of_lt hk] at this

def pgReflElt {k : ℕ} (hk : k < 4) : PGSp45 := mkPG (pgRefl k) (pgRefl_so hk)

theorem chi_tau1 (hst : PGStage1) (hchi : PGChi) :
    chiPG (mkPG pgTau1 pgTau1_so) = 1 := by
  have h11 : pgTau1 * pgTau1 = 1 := (hst.reps 0).2
  rw [chiPG_mkPG hchi _ _ h11, hchi.fixT1]
  exact Even.neg_one_pow ⟨145, by norm_num⟩

theorem chi_s1 (hco : PGCore) (hchi : PGChi) :
    chiPG (mkPG pgS1 pgS1_so) = -1 := by
  rw [chiPG_mkPG hchi _ _ hco.s1sq, hchi.fixS1]
  exact Odd.neg_one_pow ⟨142, by norm_num⟩

theorem chi_refl_0 (hco : PGCore) (hchi : PGChi) :
    chiPG (mkPG (pgRefl 0) (pgRefl_so (by norm_num))) = 1 := by
  rw [chiPG_mkPG hchi _ _ (hco.refl2 0 (by simp)), hchi.fix0]
  exact Even.neg_one_pow ⟨150, by norm_num⟩

theorem chi_refl_1 (hco : PGCore) (hchi : PGChi) :
    chiPG (mkPG (pgRefl 1) (pgRefl_so (by norm_num))) = -1 := by
  rw [chiPG_mkPG hchi _ _ (hco.refl2 1 (by simp)), hchi.fix1]
  exact Odd.neg_one_pow ⟨149, by norm_num⟩

theorem chi_refl_2 (hco : PGCore) (hchi : PGChi) :
    chiPG (mkPG (pgRefl 2) (pgRefl_so (by norm_num))) = 1 := by
  rw [chiPG_mkPG hchi _ _ (hco.refl2 2 (by simp)), hchi.fix2]
  exact Even.neg_one_pow ⟨150, by norm_num⟩

theorem chi_refl_3 (hco : PGCore) (hchi : PGChi) :
    chiPG (mkPG (pgRefl 3) (pgRefl_so (by norm_num))) = -1 := by
  rw [chiPG_mkPG hchi _ _ (hco.refl2 3 (by simp)), hchi.fix3]
  exact Odd.neg_one_pow ⟨149, by norm_num⟩

theorem chi_R (hco : PGCore) (hchi : PGChi) : chiPG (mkPG pgR0 pgR0_so) = -1 := by
  have h1 : mkPG (pgRefl 1) (pgRefl_so (by norm_num)) = mkPG pgSf0 pgSf0_so * mkPG pgR0 pgR0_so :=
    pg_ext (by simpa using hco.sr.symm)
  have h0 : mkPG (pgRefl 0) (pgRefl_so (by norm_num)) = mkPG pgSf0 pgSf0_so :=
    pg_ext (by simp [pgRefl])
  have := chi_refl_1 hco hchi
  rw [h1, map_mul, ← h0, chi_refl_0 hco hchi, one_mul] at this
  exact this

section Core

def mm {X : Type} [Group X] (φ : X ≃* PGSp45) (x : X) : SoMat5 := (φ x).1.1

variable {X : Type} [Group X] (φ : X ≃* PGSp45)

theorem mm_mul (x y : X) : mm φ (x * y) = mm φ x * mm φ y := by simp [mm]

theorem mm_one : mm φ (1 : X) = 1 := by simp [mm]

theorem mm_inj {x y : X} (h : mm φ x = mm φ y) : x = y := φ.injective (pg_ext h)

theorem mm_so (x : X) : IsSO5 (mm φ x) := (φ x).2

theorem mm_pow (x : X) (n : ℕ) : mm φ (x ^ n) = mm φ x ^ n := by simp [mm]

def eltOf (A : SoMat5) (hA : IsSO5 A) : X := φ.symm (mkPG A hA)

theorem mm_eltOf (A : SoMat5) (hA : IsSO5 A) : mm φ (eltOf φ A hA) = A := by
  simp [mm, eltOf]

theorem phi_eq_mkPG {x : X} {A : SoMat5} (hA : IsSO5 A) (h : mm φ x = A) : φ x = mkPG A hA :=
  pg_ext h

theorem nat_card_mem_list {α : Type*} [DecidableEq α] (l : List α) (hnd : l.Nodup) :
    Nat.card {a // a ∈ l} = l.length := by
  rw [Nat.card_congr (Equiv.subtypeEquivRight (fun a => (List.mem_toFinset (l := l)).symm)),
    Nat.card_eq_fintype_card, Fintype.card_coe, List.toFinset_card_of_nodup hnd]

variable [Finite X] {τ : X} {D S : Subgroup X} {eD : D ≃* DihedralGroup 4}
  {eS : S ≃* Equiv.Perm (Fin 5)}

theorem mm_cent_mem (hco : PGCore) (h : LocalPair τ D S eD eS) (hφ : φ τ = mkPG pgTau1 pgTau1_so)
    {x : X} (hx : x * τ = τ * x) : mm φ x ∈ pgCList := by
  have hCso : ∀ A ∈ pgCList, IsSO5 A := fun A hA => (hco.cent A hA).1
  let f : {A : SoMat5 // A ∈ pgCList} → centralizer ({τ} : Set X) := fun A =>
    ⟨eltOf φ A.1 (hCso A.1 A.2), by
      rw [mem_centralizer_singleton_iff]
      apply φ.injective
      rw [map_mul, map_mul, eltOf, MulEquiv.apply_symm_apply, hφ]
      exact pg_ext (hco.cent A.1 A.2).2⟩
  have hinj : Function.Injective f := by
    intro A B hAB
    apply Subtype.ext
    have := congrArg (fun z : centralizer ({τ} : Set X) => mm φ z.1) hAB
    simpa [f, mm_eltOf] using this
  have hcard : Nat.card {A : SoMat5 // A ∈ pgCList} = 960 := by
    rw [nat_card_mem_list _ hco.ndC, hco.lenC]
  have hbij := hinj.bijective_of_nat_card_le (by rw [hcard, h.card_cent])
  obtain ⟨A, hA⟩ := hbij.2 ⟨x, mem_centralizer_singleton_iff.2 hx⟩
  have : mm φ x = A.1 := by
    have := congrArg (fun z : centralizer ({τ} : Set X) => mm φ z.1) hA
    simpa [f, mm_eltOf] using this.symm
  rw [this]
  exact A.2

omit [Finite X] in
theorem LocalPair.D_comm (h : LocalPair τ D S eD eS) {d : X} (hd : d ∈ D) : d * τ = τ * d :=
  (h.cent d).2 ⟨d, hd, 1, one_mem S, (mul_one d).symm⟩

omit [Finite X] in
theorem LocalPair.S_comm (h : LocalPair τ D S eD eS) {s : X} (hs : s ∈ S) : s * τ = τ * s :=
  (h.cent s).2 ⟨1, one_mem D, s, hs, (one_mul s).symm⟩

omit [Finite X] in
theorem mm_tau (hφ : φ τ = mkPG pgTau1 pgTau1_so) : mm φ τ = pgTau1 := by
  rw [mm, hφ]; rfl

theorem mm_D_mem (hco : PGCore) (h : LocalPair τ D S eD eS) (hφ : φ τ = mkPG pgTau1 pgTau1_so)
    {d : X} (hd : d ∈ D) : mm φ d ∈ pgD0List := by
  apply hco.p2 _ (mm_cent_mem φ hco h hφ (h.D_comm hd))
  intro c hc
  have hcC := hco.s0c c hc
  have hcso := (hco.cent c hcC).1
  set y : X := eltOf φ c hcso with hy
  have hyc : y * τ = τ * y := by
    apply φ.injective
    rw [map_mul, map_mul, hy, eltOf, MulEquiv.apply_symm_apply, hφ]
    exact pg_ext (hco.cent c hcC).2
  rcases h.cent_comm_D hyc hd with h1 | h1
  · left
    have := congrArg (mm φ) h1
    rwa [mm_mul, mm_mul, hy, mm_eltOf] at this
  · right
    have := congrArg (mm φ) h1
    rwa [mm_mul, mm_mul, mm_mul, hy, mm_eltOf, mm_tau φ hφ] at this

theorem exists_D_mm (hco : PGCore) (h : LocalPair τ D S eD eS)
    (hφ : φ τ = mkPG pgTau1 pgTau1_so) {A : SoMat5} (hA : A ∈ pgD0List) :
    ∃ d ∈ D, mm φ d = A := by
  let f : D → {A : SoMat5 // A ∈ pgD0List} := fun d => ⟨mm φ d.1, mm_D_mem φ hco h hφ d.2⟩
  have hinj : Function.Injective f := fun a b hab =>
    Subtype.ext (mm_inj φ (congrArg Subtype.val hab))
  have hcard : Nat.card D = Nat.card {A : SoMat5 // A ∈ pgD0List} := by
    rw [nat_card_mem_list _ hco.ndD0, hco.lenD0, Nat.card_congr eD.toEquiv,
      Nat.card_eq_fintype_card, DihedralGroup.card]
  obtain ⟨d, hd⟩ := (hinj.bijective_of_nat_card_le hcard.ge).2 ⟨A, hA⟩
  exact ⟨d.1, d.2, congrArg Subtype.val hd⟩

theorem mm_S_mem (hco : PGCore) (h : LocalPair τ D S eD eS) (hφ : φ τ = mkPG pgTau1 pgTau1_so)
    {s : X} (hs : s ∈ S) : mm φ s ∈ pgS0List ∨ pgTau1 * mm φ s ∈ pgS0List := by
  obtain ⟨dR, hdR, hmR⟩ := exists_D_mm φ hco h hφ hco.rmem
  obtain ⟨dS, hdS, hmS⟩ := exists_D_mm φ hco h hφ hco.smem
  apply hco.p3 _ (mm_cent_mem φ hco h hφ (h.S_comm hs))
  · have := congrArg (mm φ) (h.comm dR hdR s hs)
    rw [mm_mul, mm_mul, hmR] at this
    exact this.symm
  · have := congrArg (mm φ) (h.comm dS hdS s hs)
    rw [mm_mul, mm_mul, hmS] at this
    exact this.symm

omit [Finite X] in
theorem LocalPair.tau_ne_one (h : LocalPair τ D S eD eS) : τ ≠ 1 := by
  intro h1
  obtain ⟨hτD, hτe⟩ := h.tau_mem
  have h2 : (⟨τ, hτD⟩ : D) = 1 := Subtype.ext h1
  rw [h2, map_one] at hτe
  exact absurd hτe (by decide)

omit [Finite X] in
theorem LocalPair.tau_not_mem_S (h : LocalPair τ D S eD eS) : τ ∉ S := by
  intro hS
  exact h.tau_ne_one (h.inf τ h.tau_mem.1 hS)

theorem exists_sstar (hco : PGCore) (h : LocalPair τ D S eD eS) (hφ : φ τ = mkPG pgTau1 pgTau1_so)
    (hst : PGStage1) : ∃ s ∈ S, mm φ s = pgS1 ∨ mm φ s = pgTau1 * pgS1 := by
  classical
  have hmτ := mm_tau φ hφ
  have hT1 : pgTau1 * pgTau1 = 1 := (hst.reps 0).2
  let f : S → {A : SoMat5 // A ∈ pgS0List} := fun s =>
    ⟨if mm φ s.1 ∈ pgS0List then mm φ s.1 else pgTau1 * mm φ s.1, by
      split_ifs with hc
      · exact hc
      · exact (mm_S_mem φ hco h hφ s.2).resolve_left hc⟩
  have hτs : ∀ {a b : S}, mm φ a.1 = pgTau1 * mm φ b.1 → False := by
    intro a b hab
    have : a.1 = τ * b.1 := mm_inj φ (by rw [mm_mul, hmτ]; exact hab)
    apply h.tau_not_mem_S
    have : τ = a.1 * b.1⁻¹ := by rw [this]; group
    rw [this]
    exact mul_mem a.2 (inv_mem b.2)
  have hinj : Function.Injective f := by
    intro a b hab
    have hab' := congrArg Subtype.val hab
    apply Subtype.ext
    by_cases ha : mm φ a.1 ∈ pgS0List <;> by_cases hb : mm φ b.1 ∈ pgS0List
    · simp only [f, ha, hb, ite_true] at hab'
      exact mm_inj φ hab'
    · simp only [f, ha, hb, ite_true, ite_false] at hab'
      exact (hτs hab').elim
    · simp only [f, ha, hb, ite_true, ite_false] at hab'
      exact (hτs hab'.symm).elim
    · simp only [f, ha, hb, ite_false] at hab'
      have : mm φ a.1 = mm φ b.1 := by
        have h2 := congrArg (fun A => pgTau1 * A) hab'
        simpa [← Matrix.mul_assoc, hT1] using h2
      exact mm_inj φ this
  have hcard : Nat.card S = Nat.card {A : SoMat5 // A ∈ pgS0List} := by
    rw [nat_card_mem_list _ hco.ndS0, hco.lenS0, Nat.card_congr eS.toEquiv,
      Nat.card_eq_fintype_card, Fintype.card_perm]
    decide
  obtain ⟨s, hs⟩ := (hinj.bijective_of_nat_card_le hcard.ge).2 ⟨pgS1, hco.s1mem⟩
  refine ⟨s.1, s.2, ?_⟩
  have hs' := congrArg Subtype.val hs
  by_cases hc : mm φ s.1 ∈ pgS0List
  · left
    simpa [f, hc] using hs'
  · right
    simp only [f, hc, ite_false] at hs'
    calc mm φ s.1 = (pgTau1 * pgTau1) * mm φ s.1 := by rw [hT1, Matrix.one_mul]
      _ = pgTau1 * (pgTau1 * mm φ s.1) := by rw [Matrix.mul_assoc]
      _ = pgTau1 * pgS1 := by rw [hs']

omit [Finite X] in
theorem conj_of_mm (hφ : φ τ = mkPG pgTau1 pgTau1_so) {x : X} {F : SoMat5} (hF : IsSO5 F)
    (h : F * pgTau1 = mm φ x * F) : ∃ g : X, x = g * τ * g⁻¹ := by
  refine ⟨eltOf φ F hF, ?_⟩
  apply φ.injective
  rw [map_mul, map_mul, map_inv, eltOf, MulEquiv.apply_symm_apply, hφ]
  exact (conj_eq_of_mat (g := mkPG F hF) (t := mkPG pgTau1 pgTau1_so) (u := φ x) h).symm

theorem dihedral_order4_sq : ∀ a : DihedralGroup 4, a ^ 4 = 1 → a ^ 2 ≠ 1 →
    a * a = DihedralGroup.r 2 := by
  decide

set_option maxRecDepth 100000 in
theorem perm_five_swap : ∀ σ : Equiv.Perm (Fin 5), σ * σ = 1 → Equiv.Perm.sign σ = -1 →
    ∃ a b : Fin 5, a ≠ b ∧ σ = Equiv.swap a b := by
  decide

theorem signData_core (hst : PGStage1) (hchi : PGChi) (hco : PGCore) (h : LocalPair τ D S eD eS)
    (hφ : φ τ = mkPG pgTau1 pgTau1_so) :
    ∃ χ : X →* ℤˣ, (∀ d ∈ D, orderOf d = 4 → χ d = -1) ∧
      (∀ s : S, Equiv.Perm.sign (eS s) = -1 → χ s = -1) ∧
      (∀ d ∈ D, d ≠ 1 → d ≠ τ → d * d = 1 → ¬ ∃ g : X, d = g * τ * g⁻¹) ∧
      (∀ d ∈ D, d ≠ 1 → d ≠ τ → d * d = 1 → χ d = -1 →
        ∀ s ∈ S, s ≠ 1 → s * s = 1 → χ s = -1 → ∃ g : X, d * s = g * τ * g⁻¹) := by
  have hmτ : mm φ τ = pgTau1 := mm_tau φ hφ
  set χ : X →* ℤˣ := chiPG.comp φ.toMonoidHom with hχdef
  have hχ : ∀ {x : X} {A : SoMat5} (hA : IsSO5 A), mm φ x = A → χ x = chiPG (mkPG A hA) := by
    intro x A hA hx
    show chiPG (φ x) = _
    rw [phi_eq_mkPG φ hA hx]
  have ha : ∀ d ∈ D, orderOf d = 4 → χ d = -1 := by
    intro d hd hord
    have h4 : (eD ⟨d, hd⟩) ^ 4 = 1 := by
      rw [← map_pow]
      have : (⟨d, hd⟩ : D) ^ 4 = 1 := Subtype.ext (by
        have := pow_orderOf_eq_one d
        rwa [hord] at this)
      rw [this, map_one]
    have h2 : (eD ⟨d, hd⟩) ^ 2 ≠ 1 := by
      intro h2
      have : (⟨d, hd⟩ : D) ^ 2 = 1 := eD.injective (by rw [map_pow, h2, map_one])
      have h3 : d ^ 2 = 1 := congrArg Subtype.val this
      exact pow_ne_one_of_lt_orderOf (by norm_num) (by rw [hord]; norm_num) h3
    obtain ⟨hτD, hτe⟩ := h.tau_mem
    have hdd : d * d = τ := by
      have := dihedral_order4_sq _ h4 h2
      rw [← map_mul, ← hτe] at this
      have h5 := eD.injective this
      exact congrArg Subtype.val h5
    have hdd' : mm φ d * mm φ d = pgTau1 := by rw [← mm_mul, hdd, hmτ]
    rcases hco.ord4 _ (mm_D_mem φ hco h hφ hd) hdd' with h1 | h1
    · rw [hχ pgR0_so h1, chi_R hco hchi]
    · have : φ d = (mkPG pgR0 pgR0_so) ^ 3 := pg_ext (by
        rw [pg_pow_val, mkPG_val]; exact h1)
      show chiPG (φ d) = -1
      rw [this, map_pow, chi_R hco hchi]
      exact Odd.neg_one_pow ⟨1, by norm_num⟩
  obtain ⟨ss, hssS, hss⟩ := exists_sstar φ hco h hφ hst
  have hT1 : mkPG pgTau1 pgTau1_so ≠ 1 := fun e => h.tau_ne_one (by
    apply φ.injective
    rw [hφ, e, map_one])
  have hχss : χ ss = -1 := by
    rcases hss with h1 | h1
    · rw [hχ pgS1_so h1, chi_s1 hco hchi]
    · have : φ ss = mkPG pgTau1 pgTau1_so * mkPG pgS1 pgS1_so := pg_ext (by
        rw [pg_mul_val, mkPG_val, mkPG_val]; exact h1)
      show chiPG (φ ss) = -1
      rw [this, map_mul, chi_tau1 hst hchi, chi_s1 hco hchi, one_mul]
  have hψ : (χ.comp (S.subtype.comp eS.symm.toMonoidHom) : Equiv.Perm (Fin 5) →* ℤˣ) =
      Equiv.Perm.sign := by
    apply Equiv.Perm.eq_sign_of_surjective_hom
    intro u
    rcases Int.units_eq_one_or u with rfl | rfl
    · exact ⟨1, map_one _⟩
    · refine ⟨eS ⟨ss, hssS⟩, ?_⟩
      simpa using hχss
  have hsign : ∀ s : S, χ s = Equiv.Perm.sign (eS s) := by
    intro s
    have := congrArg (fun f : Equiv.Perm (Fin 5) →* ℤˣ => f (eS s)) hψ
    simpa using this
  have hb : ∀ s : S, Equiv.Perm.sign (eS s) = -1 → χ s = -1 := fun s hs => by
    rw [hsign s]; exact hs
  have hc : ∀ d ∈ D, d ≠ 1 → d ≠ τ → d * d = 1 → ¬ ∃ g : X, d = g * τ * g⁻¹ := by
    intro d hd hd1 hdτ hdd ⟨g, hg⟩
    have hm := mm_D_mem φ hco h hφ hd
    have hmm : mm φ d * mm φ d = 1 := by rw [← mm_mul, hdd, mm_one]
    have hne1 : mm φ d ≠ 1 := fun e => hd1 (mm_inj φ (by rw [e, mm_one]))
    have hneτ : mm φ d ≠ pgTau1 := fun e => hdτ (mm_inj φ (by rw [e, hmτ]))
    apply hco.trace _ hm hmm hne1 hneτ
    have := pg_trace_conj (φ g) (φ τ)
    rw [hφ, mkPG_val] at this
    have h2 : φ d = φ g * φ τ * (φ g)⁻¹ := by rw [hg, map_mul, map_mul, map_inv]
    show ((φ d).1.1).trace = _
    rw [h2, hφ]
    simpa using this
  have hd : ∀ d ∈ D, d ≠ 1 → d ≠ τ → d * d = 1 → χ d = -1 →
      ∀ s ∈ S, s ≠ 1 → s * s = 1 → χ s = -1 → ∃ g : X, d * s = g * τ * g⁻¹ := by
    intro d hdD hd1 hdτ hdd hχd s hsS hs1 hss1 hχs
    have hm := mm_D_mem φ hco h hφ hdD
    have hmm : mm φ d * mm φ d = 1 := by rw [← mm_mul, hdd, mm_one]
    have hne1 : mm φ d ≠ 1 := fun e => hd1 (mm_inj φ (by rw [e, mm_one]))
    have hneτ : mm φ d ≠ pgTau1 := fun e => hdτ (mm_inj φ (by rw [e, hmτ]))
    have hk : ∃ k ∈ ([1, 3] : List ℕ), mm φ d = pgRefl k := by
      rcases hco.refl _ hm hmm hne1 hneτ with h0 | h1 | h2 | h3
      · exfalso
        have := hχ (pgRefl_so (by norm_num : 0 < 4)) h0
        rw [chi_refl_0 hco hchi] at this
        rw [this] at hχd
        exact absurd hχd (by decide)
      · exact ⟨1, by simp, h1⟩
      · exfalso
        have := hχ (pgRefl_so (by norm_num : 2 < 4)) h2
        rw [chi_refl_2 hco hchi] at this
        rw [this] at hχd
        exact absurd hχd (by decide)
      · exact ⟨3, by simp, h3⟩
    obtain ⟨k, hkmem, hdk⟩ := hk
    have hss_sq : ss * ss = 1 := by
      apply mm_inj φ
      rw [mm_mul, mm_one]
      rcases hss with h1 | h1
      · rw [h1]; exact hco.s1sq
      · rw [h1]
        calc pgTau1 * pgS1 * (pgTau1 * pgS1) = pgTau1 * (pgS1 * pgTau1) * pgS1 := by
              simp only [Matrix.mul_assoc]
          _ = pgTau1 * (pgTau1 * pgS1) * pgS1 := by rw [hco.ts]
          _ = (pgTau1 * pgTau1) * (pgS1 * pgS1) := by simp only [Matrix.mul_assoc]
          _ = 1 := by rw [hco.tt, hco.s1sq, Matrix.one_mul]
    have hsq' : eS ⟨s, hsS⟩ * eS ⟨s, hsS⟩ = 1 := by
      rw [← map_mul]
      have : (⟨s, hsS⟩ : S) * ⟨s, hsS⟩ = 1 := Subtype.ext hss1
      rw [this, map_one]
    have hssq' : eS ⟨ss, hssS⟩ * eS ⟨ss, hssS⟩ = 1 := by
      rw [← map_mul]
      have : (⟨ss, hssS⟩ : S) * ⟨ss, hssS⟩ = 1 := Subtype.ext hss_sq
      rw [this, map_one]
    have hsg : Equiv.Perm.sign (eS ⟨s, hsS⟩) = -1 := by rw [← hsign ⟨s, hsS⟩]; exact hχs
    have hssg : Equiv.Perm.sign (eS ⟨ss, hssS⟩) = -1 := by rw [← hsign ⟨ss, hssS⟩]; exact hχss
    obtain ⟨a, b, hab, hs_sw⟩ := perm_five_swap _ hsq' hsg
    obtain ⟨c, e, hce, hss_sw⟩ := perm_five_swap _ hssq' hssg
    obtain ⟨u, hu⟩ := isConj_iff.1 (Equiv.Perm.isConj_swap hce hab)
    set u0 : S := eS.symm u with hu0
    have hconjS : (u0 : X) * ss * (u0 : X)⁻¹ = s := by
      have : u0 * ⟨ss, hssS⟩ * u0⁻¹ = ⟨s, hsS⟩ := by
        apply eS.injective
        rw [map_mul, map_mul, map_inv, hu0, MulEquiv.apply_symm_apply, hss_sw, hs_sw, hu]
      exact congrArg Subtype.val this
    have hdss : ∃ g : X, d * ss = g * τ * g⁻¹ := by
      rcases hss with h1 | h1
      · obtain ⟨hso, hcj⟩ := hst.f2 k hkmem 0 (by simp)
        refine conj_of_mm φ hφ hso ?_
        rw [mm_mul, hdk, h1]
        simpa using hcj
      · obtain ⟨hso, hcj⟩ := hst.f2 k hkmem 1 (by simp)
        refine conj_of_mm φ hφ hso ?_
        rw [mm_mul, hdk, h1]
        simpa using hcj
    obtain ⟨g, hg⟩ := hdss
    refine ⟨(u0 : X) * g, ?_⟩
    have hcomm : d * (u0 : X) = (u0 : X) * d := h.comm d hdD u0 u0.2
    calc d * s = d * ((u0 : X) * ss * (u0 : X)⁻¹) := by rw [hconjS]
      _ = (u0 : X) * (d * ss) * (u0 : X)⁻¹ := by
        calc d * ((u0 : X) * ss * (u0 : X)⁻¹) = (d * (u0 : X)) * ss * (u0 : X)⁻¹ := by group
          _ = ((u0 : X) * d) * ss * (u0 : X)⁻¹ := by rw [hcomm]
          _ = (u0 : X) * (d * ss) * (u0 : X)⁻¹ := by group
      _ = (u0 : X) * g * τ * ((u0 : X) * g)⁻¹ := by rw [hg]; group
  exact ⟨χ, ha, hb, hc, hd⟩

end Core

theorem signDataPGSpXS_of (hst : PGStage1) (hchi : PGChi) (hco : PGCore) : SignDataPGSpXS := by
  intro X _ _ φ τ D S eD eS hP h
  obtain ⟨P, ⟨ι⟩⟩ := hP
  have hsyl : Nat.card (pgP0 hst) = 2 ^ (Nat.card PGSp45).factorization 2 := by
    have hP128 : Nat.card ↥(P : Subgroup X) = 128 :=
      (Nat.card_congr ι.toEquiv).trans SAFyGH.card_W8
    rw [card_pgP0, ← hP128, Sylow.card_eq_multiplicity, Nat.card_congr φ.toEquiv]
  obtain ⟨g, hg⟩ := tau_conj_tau1 hst φ hsyl h
  have hφ : (φ.trans (MulAut.conj g)) τ = mkPG pgTau1 pgTau1_so := by
    simpa [MulAut.conj_apply] using hg
  exact signData_core (φ.trans (MulAut.conj g)) hst hchi hco h hφ

end CFSG.EvenSporadicStandard.TwoHS
