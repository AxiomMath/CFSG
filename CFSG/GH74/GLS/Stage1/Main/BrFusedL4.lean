module

public import CFSG.GH74.GLS.Stage1.Main.BrFusedPair
public import CFSG.GH74.GLS.Stage1.Main.BrTwoClassU

public section

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage2.Local CFSG.GH74.GLS.Stage2.Final
  CFSG.LocalAnalysis.ComponentInitial CFSG.GH74.GLS.LU.Local CFSG.GorensteinWalter
open scoped commutatorElement Pointwise

namespace CFSG.GH74.GLS.Stage1.Main

section Abstract

variable {Γ : Type} [Group Γ]

theorem relIndex_le_two_of_sq [Finite Γ] {A : Subgroup Γ} {n : Γ} (hnN : n ∈ normalizer (A : Set Γ))
    (hn2 : n * n ∈ A) : A.relIndex (A ⊔ zpowers n) ≤ 2 := by
  classical
  have hzw : zpowers n ≤ normalizer (A : Set Γ) := Subgroup.zpowers_le.2 hnN
  have hBN : A ⊔ zpowers n ≤ normalizer (A : Set Γ) := sup_le Subgroup.le_normalizer hzw
  have hLB : A ≤ A ⊔ zpowers n := le_sup_left
  have hn : (A.subgroupOf (A ⊔ zpowers n)).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hLB).2 hBN
  have hmul := Subgroup.coe_mul_of_right_le_normalizer_left A (zpowers n) hzw
  let f : Bool → ↥(A ⊔ zpowers n) ⧸ A.subgroupOf (A ⊔ zpowers n) := fun b =>
    if b then QuotientGroup.mk ⟨n, Subgroup.mem_sup_right (mem_zpowers n)⟩ else 1
  have hsurj : Function.Surjective f := by
    intro y
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective y
    have hx : (x : Γ) ∈ (A : Set Γ) * (zpowers n : Set Γ) := by
      rw [← hmul]
      exact x.2
    obtain ⟨l, hl, a, ha, hla⟩ := Set.mem_mul.1 hx
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 ha
    rcases Int.even_or_odd' k with ⟨m, rfl | rfl⟩
    · refine ⟨false, ?_⟩
      show (1 : ↥(A ⊔ zpowers n) ⧸ _) = QuotientGroup.mk x
      rw [eq_comm, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
      have h1 : n ^ (2 * m) = (n * n) ^ m := by
        rw [zpow_mul, zpow_two]
      rw [← hla, h1]
      exact A.mul_mem hl (A.zpow_mem hn2 m)
    · refine ⟨true, ?_⟩
      show QuotientGroup.mk (⟨n, _⟩ : ↥(A ⊔ zpowers n)) = QuotientGroup.mk x
      rw [QuotientGroup.eq, Subgroup.mem_subgroupOf]
      show n⁻¹ * (x : Γ) ∈ A
      have h1 : n ^ (2 * m + 1) = (n * n) ^ m * n := by
        rw [zpow_add_one, zpow_mul, zpow_two]
      rw [← hla, h1]
      have : n⁻¹ * (l * ((n * n) ^ m * n)) = (n⁻¹ * l * n) * (n⁻¹ * (n * n) ^ m * n) := by group
      rw [this]
      refine A.mul_mem ?_ ?_
      · have := (Subgroup.mem_normalizer_iff.1 ((normalizer (A : Set Γ)).inv_mem hnN) l).1 hl
        simpa using this
      · have h2 : (n * n) ^ m ∈ A := A.zpow_mem hn2 m
        have := (Subgroup.mem_normalizer_iff.1 ((normalizer (A : Set Γ)).inv_mem hnN) _).1 h2
        simpa using this
  have h1 := Nat.card_le_card_of_surjective f hsurj
  have h2 : Nat.card Bool = 2 := by simp
  have h3 : Nat.card (↥(A ⊔ zpowers n) ⧸ A.subgroupOf (A ⊔ zpowers n)) =
      A.relIndex (A ⊔ zpowers n) := rfl
  omega

theorem fusedInd_aux {Gs : Type} [Group Gs] [Finite Gs] {z : Gs} {Ea Eb S : Subgroup Gs} {t n : Gs}
    {q : ℕ} (hodd : Odd q) (h3 : 3 < q) (hcomm : ∀ a ∈ Ea, ∀ b ∈ Eb, a * b = b * a)
    (hperf : Group.IsPerfect ↥Ea) (hnS : n ∈ S) (hnN : n ∈ normalizer (Ea : Set Gs))
    (hEN : Ea ⊔ Eb ≤ normalizer (Ea : Set Gs))
    (hdec : ∀ s ∈ S, ∃ k ∈ S ⊓ (Ea ⊔ Eb), s = k ∨ s = k * t ∨ s = k * n ∨ s = k * (t * n))
    (ht : t ∉ normalizer (Ea : Set Gs)) (hF : FusedPGL z Ea n q) :
    InducedPGL2 Ea (S ⊓ normalizer (Ea : Set Gs)) q := by
  classical
  obtain ⟨Z, hZC, hZB, hzZ, hsq, hn, F₀, iF, fF, hq, ⟨φ⟩⟩ := hF
  set B : Subgroup Gs := Ea ⊔ zpowers n with hB
  set T : Subgroup Gs := S ⊓ normalizer (Ea : Set Gs) with hT
  have hEB : Ea ≤ B := le_sup_left
  have hnB : n ∈ B := Subgroup.mem_sup_right (mem_zpowers n)
  have hBN : B ≤ normalizer (Ea : Set Gs) :=
    sup_le Subgroup.le_normalizer (Subgroup.zpowers_le.2 hnN)
  have hTN : T ≤ normalizer (Ea : Set Gs) := inf_le_right
  have hnT : n ∈ T := ⟨hnS, hnN⟩
  have hBT : B ≤ Ea ⊔ T := sup_le le_sup_left (Subgroup.zpowers_le.2 (Subgroup.mem_sup_right hnT))
  have hA : Ea ⊔ T ≤ B ⊔ centralizer (Ea : Set Gs) := by
    refine sup_le (hEB.trans le_sup_left) ?_
    intro x hx
    obtain ⟨k, hk, hcases⟩ := hdec x hx.1
    have hkE : k ∈ Ea ⊔ Eb := hk.2
    have hkn : k ∈ normalizer (Ea : Set Gs) := hEN hkE
    obtain ⟨e₁, he₁, e₂, he₂, hk'⟩ :=
      CFSG.GH74.GLS.Stage1.Thm3.Sec8.Basic.mem_sup_of_commute' hcomm hkE
    have he₂C : e₂ ∈ centralizer (Ea : Set Gs) := by
      rw [Subgroup.mem_centralizer_iff]
      intro g hg
      exact hcomm g hg e₂ he₂
    have hke : k ∈ B ⊔ centralizer (Ea : Set Gs) := by
      rw [hk']
      exact Subgroup.mul_mem _ (Subgroup.mem_sup_left (hEB he₁)) (Subgroup.mem_sup_right he₂C)
    rcases hcases with h1 | h1 | h1 | h1
    · rw [h1]; exact hke
    · exfalso
      apply ht
      have : t = k⁻¹ * x := by rw [h1]; group
      rw [this]
      exact mul_mem (inv_mem hkn) hx.2
    · rw [h1]
      exact Subgroup.mul_mem _ hke (Subgroup.mem_sup_left hnB)
    · exfalso
      apply ht
      have : t = k⁻¹ * x * n⁻¹ := by rw [h1]; group
      rw [this]
      exact mul_mem (mul_mem (inv_mem hkn) hx.2) (inv_mem hnN)
  have hBC : B ⊓ centralizer (Ea : Set Gs) = Z := by
    apply le_antisymm
    · have hZnorm : B ≤ normalizer (Z : Set Gs) := (Subgroup.normal_subgroupOf_iff_le_normalizer hZB).1 hn
      have hnNA : n ∈ normalizer ((Ea ⊔ Z : Subgroup Gs) : Set Gs) := by
        rw [Subgroup.mem_normalizer_iff_map_conj_eq, Subgroup.map_sup,
          Subgroup.mem_normalizer_iff_map_conj_eq.1 hnN,
          Subgroup.mem_normalizer_iff_map_conj_eq.1 (hZnorm hnB)]
      have hBeq : Ea ⊔ Z ⊔ zpowers n = B :=
        le_antisymm (sup_le (sup_le hEB hZB) le_sup_right) (sup_le_sup_right le_sup_left _)
      have hidx : (Ea ⊔ Z).relIndex B ≤ 2 := by
        rw [← hBeq]
        exact relIndex_le_two_of_sq hnNA (by
          have := Subgroup.mul_mem _ (Subgroup.mem_sup_left hnB) (Subgroup.mem_sup_right hnB)
          exact hsq)
      have hFodd : Odd (Nat.card F₀) := by rw [hq]; exact hodd
      have hFop := CFSG.ABGLocalTools.isOddPrimePower_card_of_odd hFodd
      have hF3 : 3 < Nat.card F₀ := by rw [hq]; exact h3
      exact inf_centralizer_le_Z' (hZn := hn) hEB hZB hperf hidx hFop hF3 φ
    · exact le_inf hZB hZC
  obtain ⟨hCn, ⟨e⟩⟩ := inducedQuot_equiv hBN hTN hBT hA hBC (hZn := hn)
  exact ⟨hCn, F₀, iF, fF, hq, ⟨e.trans φ⟩⟩

end Abstract

section Norm

theorem mem_normalizer_map_iff {A B : Type*} [Group A] [Group B] (f : A →* B)
    (hf : Function.Injective f) (H : Subgroup A) (a : A) :
    f a ∈ normalizer ((H.map f : Subgroup B) : Set B) ↔ a ∈ normalizer (H : Set A) := by
  have key : ∀ x : A, (f a * f x * (f a)⁻¹ ∈ H.map f ↔ a * x * a⁻¹ ∈ H) := by
    intro x
    rw [← map_inv, ← map_mul, ← map_mul, Subgroup.mem_map_iff_mem hf]
  rw [Subgroup.mem_normalizer_iff, Subgroup.mem_normalizer_iff]
  constructor
  · intro h x
    rw [← key x, ← Subgroup.mem_map_iff_mem hf (K := H)]
    exact h (f x)
  · intro h b
    by_cases hb : b ∈ Set.range f
    · obtain ⟨x, rfl⟩ := hb
      rw [Subgroup.mem_map_iff_mem hf, key x]
      exact h x
    · constructor
      · intro hbH
        exact absurd (Subgroup.map_le_range f H hbH) hb
      · intro hbH
        exfalso
        obtain ⟨w, hw⟩ := Subgroup.map_le_range f H hbH
        apply hb
        refine ⟨a⁻¹ * w * a, ?_⟩
        rw [map_mul, map_mul, map_inv, hw]
        group

variable {G : Type} [Group G] {z : G} {S : Subgroup G} {ε : Bool} {Gs : Type} [Group Gs] [Finite Gs]
  {p f : ℕ} (C : FusedCtx z S ε Gs p f)

omit [Finite Gs] in
theorem FusedCtx.mem_normalizer_pull (K : Subgroup Gs) (hK : K ≤ C.X) (x : ↥C.X) :
    C.emb x ∈ normalizer ((C.pull K : Subgroup (CentralizerBar z)) : Set (CentralizerBar z)) ↔
      (x : Gs) ∈ normalizer (K : Set Gs) := by
  unfold FusedCtx.pull
  rw [mem_normalizer_map_iff C.emb C.emb_injective]
  have := mem_normalizer_map_iff C.X.subtype C.X.subtype_injective (K.subgroupOf C.X) x
  rw [Subgroup.map_subgroupOf_eq_of_le hK] at this
  exact this.symm

theorem mem_S1_iff [Finite G] {s : G} :
    s ∈ S1 S z ↔ s ∈ S ∧ ∃ hsC : s ∈ Cen z, ∀ K : Subgroup (CentralizerBar z), IsComponent K →
      K ≤ LBar z → toBar z ⟨s, hsC⟩ ∈ normalizer (K : Set (CentralizerBar z)) := by
  unfold S1
  rw [Subgroup.mem_inf, Subgroup.mem_map]
  constructor
  · rintro ⟨hs, c, hc, rfl⟩
    refine ⟨hs, c.2, fun K hK hKL => ?_⟩
    have := Subgroup.mem_iInf.1 hc K
    have := Subgroup.mem_iInf.1 this ⟨hK, hKL⟩
    exact this
  · rintro ⟨hs, hsC, h⟩
    refine ⟨hs, ⟨s, hsC⟩, ?_, rfl⟩
    refine Subgroup.mem_iInf.2 fun K => Subgroup.mem_iInf.2 fun hK => ?_
    exact h K hK.1 hK.2

theorem FusedCtx.comp_iff [Finite G] (hcen : Cen2 G z S) (K : Subgroup (CentralizerBar z)) :
    (IsComponent K ∧ K ≤ LBar z) ↔ (K = C.pull C.E₁ ∨ K = C.pull C.E₂) := by
  have hSp : IsPGroup 2 ↥(barOf z S) := (isSylowOf_barOf hcen.sylow).isPGroup
  constructor
  · rintro ⟨hK, -⟩
    have : K ∈ {K : Subgroup (CentralizerBar z) | IsComponent K} := hK
    rw [C.comps hSp] at this
    exact this
  · intro h
    refine ⟨?_, ?_⟩
    · have : K ∈ {K : Subgroup (CentralizerBar z) | IsComponent K} := by rw [C.comps hSp]; exact h
      exact this
    · rw [C.LBar_eq_pull hcen]
      rcases h with rfl | rfl
      · exact C.pull_mono le_sup_left
      · exact C.pull_mono le_sup_right

omit [Finite Gs] in
theorem FusedCtx.emb_symm_apply (x : ↥C.X) :
    C.emb x = ((C.Ψ.symm x : ↥(Stage1.Thm3.Sec8.layerSBar z S)) : CentralizerBar z) := rfl

theorem FusedCtx.hperm [Finite G] {w : Gs} (hw : w ∈ centralizer ({C.z₁} : Set Gs)) :
    w ∈ normalizer (C.E₁ : Set Gs) ↔ w ∈ normalizer (C.E₂ : Set Gs) := by
  have hcomp := C.pkg.data.comps
  constructor
  · intro hN
    have h := Subgroup.mem_normalizer_iff_map_conj_eq.1 hN
    rcases hcomp.perm hw with ⟨-, h2⟩ | ⟨h1, -⟩
    · exact Subgroup.mem_normalizer_iff_map_conj_eq.2 h2
    · exact absurd (h1.symm.trans h).symm hcomp.ne
  · intro hN
    have h := Subgroup.mem_normalizer_iff_map_conj_eq.1 hN
    rcases hcomp.perm hw with ⟨h1, -⟩ | ⟨-, h2⟩
    · exact Subgroup.mem_normalizer_iff_map_conj_eq.2 h1
    · exact absurd (h2.symm.trans h) hcomp.ne

theorem FusedCtx.T_eq [Finite G] (hcen : Cen2 G z S) :
    SBar (S1 S z) z = C.pull ((C.S₁ : Subgroup Gs) ⊓ normalizer (C.E₁ : Set Gs)) := by
  have hSp := hcen.sylow.isPGroup
  ext y
  constructor
  · rintro ⟨c, hc, rfl⟩
    obtain ⟨hcS, hcC, hnorm⟩ := mem_S1_iff.1 hc
    have hyS : toBar z c ∈ barOf z S := ⟨c, hcS, rfl⟩
    have hyΓ : toBar z c ∈ Stage1.Thm3.Sec8.layerSBar z S := by
      rw [layerSBar_eq_sup]; exact Subgroup.mem_sup_right hyS
    have hxS := (C.hΨ ⟨_, hyΓ⟩).1 hyS
    have hemb : C.emb (C.Ψ ⟨toBar z c, hyΓ⟩) = toBar z c := by
      rw [C.emb_symm_apply, MulEquiv.symm_apply_apply]
    have hN₁ : toBar z c ∈ normalizer ((C.pull C.E₁ : Subgroup (CentralizerBar z)) : Set _) :=
      hnorm _ ((C.comp_iff hcen _).2 (Or.inl rfl)).1 ((C.comp_iff hcen _).2 (Or.inl rfl)).2
    rw [← hemb, C.mem_normalizer_pull C.E₁ C.E₁_le_X] at hN₁
    exact (C.mem_pull_iff _ _).2 ⟨hyΓ, hxS, hN₁⟩
  · intro hy
    obtain ⟨hyΓ, hw⟩ := (C.mem_pull_iff _ _).1 hy
    have hyS : y ∈ barOf z S := (C.hΨ ⟨y, hyΓ⟩).2 hw.1
    obtain ⟨c, hcS, hcy⟩ := hyS
    refine ⟨c, ?_, hcy⟩
    have hemb : C.emb (C.Ψ ⟨y, hyΓ⟩) = y := by
      rw [C.emb_symm_apply, MulEquiv.symm_apply_apply]
    refine mem_S1_iff.2 ⟨hcS, c.2, fun K hK hKL => ?_⟩
    have hc : toBar z ⟨((c : ↥(Cen z)) : G), c.2⟩ = y := hcy
    show toBar z ⟨((c : ↥(Cen z)) : G), c.2⟩ ∈ normalizer (K : Set (CentralizerBar z))
    rw [hc, ← hemb]
    rcases (C.comp_iff hcen K).1 ⟨hK, hKL⟩ with rfl | rfl
    · exact (C.mem_normalizer_pull C.E₁ C.E₁_le_X _).2 hw.2
    · exact (C.mem_normalizer_pull C.E₂ C.E₂_le_X _).2
        ((C.hperm (C.X_le_Cen (C.Ψ ⟨y, hyΓ⟩).2)).1 hw.2)

omit [Finite Gs] in
theorem FusedPkg.t_sq {q : ℕ} {ε : ℤ} {z' : Gs} {S' : Sylow 2 Gs} {E₁ E₂ : Subgroup Gs} {t' u' n' : Gs}
    (h : FusedPkg Gs q ε z' S' E₁ E₂ t' u' n') : t' * t' = 1 := by
  have hs := h.data.syl
  obtain ⟨c, hc'⟩ := isConj_iff.1 hs.t_conj
  have h1 := MulEquiv.orderOf_eq (MulAut.conj c) z'
  rw [MulAut.conj_apply, hc'] at h1
  have ho : orderOf t' = 2 := by rw [h1]; exact hs.z_inv
  have := pow_orderOf_eq_one t'
  rwa [ho, pow_two] at this

omit [Finite Gs] in
theorem FusedPkg.t_not_normalizer₂ {q : ℕ} {ε : ℤ} {z' : Gs} {S' : Sylow 2 Gs} {E₁ E₂ : Subgroup Gs}
    {t' u' n' : Gs} (h : FusedPkg Gs q ε z' S' E₁ E₂ t' u' n') :
    t' ∉ normalizer (E₂ : Set Gs) := by
  intro ht
  have h1 : E₂.map (MulAut.conj t').toMonoidHom = E₂ :=
    Subgroup.mem_normalizer_iff_map_conj_eq.1 ht
  apply h.data.comps.ne
  have h2 := h.data.syl.t_swap
  calc E₁ = (E₁.map (MulAut.conj t').toMonoidHom).map (MulAut.conj t').toMonoidHom :=
        (map_conj_conj_of_sq h.t_sq E₁).symm
    _ = E₂.map (MulAut.conj t').toMonoidHom := by rw [h2]
    _ = E₂ := h1

theorem FusedCtx.induced₁ [Finite G] (hcen : Cen2 G z S) (hodd : Odd (p ^ f)) (h5 : 5 ≤ p ^ f) :
    InducedPGL2 (C.pull C.E₁) (SBar (S1 S z) z) (p ^ f) := by
  have hcomp := C.pkg.data.comps
  rw [C.T_eq hcen]
  have hmodel : InducedPGL2 C.E₁ ((C.S₁ : Subgroup Gs) ⊓ normalizer (C.E₁ : Set Gs)) (p ^ f) :=
    fusedInd_aux (Eb := C.E₂) (S := (C.S₁ : Subgroup Gs)) (t := C.t₁) (n := C.n₁) hodd (by omega)
      hcomp.comm hcomp.quasi₁.1 C.pkg.n_mem C.pkg.n_norm₁ C.pkg.E_le_normalizer₁ C.pkg.dec
      C.pkg.t_not_normalizer₁ C.pkg.pgl
  have h1 : InducedPGL2 (C.E₁.subgroupOf C.X)
      (((C.S₁ : Subgroup Gs) ⊓ normalizer (C.E₁ : Set Gs)).subgroupOf C.X) (p ^ f) := by
    rw [← inducedPGL2_map_iff C.X.subtype C.X.subtype_injective,
      Subgroup.map_subgroupOf_eq_of_le C.E₁_le_X,
      Subgroup.map_subgroupOf_eq_of_le (inf_le_left.trans C.S₁_le_X)]
    exact hmodel
  exact (inducedPGL2_map_iff C.emb C.emb_injective _ _ _).2 h1

theorem FusedCtx.induced₂ [Finite G] (hcen : Cen2 G z S) (hodd : Odd (p ^ f)) (h5 : 5 ≤ p ^ f) :
    InducedPGL2 (C.pull C.E₂) (SBar (S1 S z) z) (p ^ f) := by
  have hcomp := C.pkg.data.comps
  rw [C.T_eq hcen]
  have hTeq : (C.S₁ : Subgroup Gs) ⊓ normalizer (C.E₁ : Set Gs) =
      (C.S₁ : Subgroup Gs) ⊓ normalizer (C.E₂ : Set Gs) := by
    ext x
    constructor
    · rintro ⟨hx, hxN⟩
      exact ⟨hx, (C.hperm (C.S₁_le_Cen hx)).1 hxN⟩
    · rintro ⟨hx, hxN⟩
      exact ⟨hx, (C.hperm (C.S₁_le_Cen hx)).2 hxN⟩
  rw [hTeq]
  have hmodel : InducedPGL2 C.E₂ ((C.S₁ : Subgroup Gs) ⊓ normalizer (C.E₂ : Set Gs)) (p ^ f) :=
    fusedInd_aux (Ea := C.E₂) (Eb := C.E₁) (S := (C.S₁ : Subgroup Gs)) (t := C.t₁) (n := C.n₁)
      hodd (by omega) (fun a ha b hb => (hcomp.comm b hb a ha).symm) hcomp.quasi₂.1 C.pkg.n_mem
      C.pkg.n_norm₂ (by rw [sup_comm]; exact C.pkg.E_le_normalizer₂)
      (by rw [sup_comm]; exact C.pkg.dec) C.pkg.t_not_normalizer₂ C.pkg.pgl₂
  have h1 : InducedPGL2 (C.E₂.subgroupOf C.X)
      (((C.S₁ : Subgroup Gs) ⊓ normalizer (C.E₂ : Set Gs)).subgroupOf C.X) (p ^ f) := by
    rw [← inducedPGL2_map_iff C.X.subtype C.X.subtype_injective,
      Subgroup.map_subgroupOf_eq_of_le C.E₂_le_X,
      Subgroup.map_subgroupOf_eq_of_le (inf_le_left.trans C.S₁_le_X)]
    exact hmodel
  exact (inducedPGL2_map_iff C.emb C.emb_injective _ _ _).2 h1

theorem FusedCtx.induced [Finite G] (hcen : Cen2 G z S) (hodd : Odd (p ^ f)) (h5 : 5 ≤ p ^ f)
    {L : Subgroup (CentralizerBar z)} (hL : L = C.pull C.E₁ ∨ L = C.pull C.E₂) :
    InducedPGL2 L (SBar (S1 S z) z) (p ^ f) := by
  rcases hL with rfl | rfl
  · exact C.induced₁ hcen hodd h5
  · exact C.induced₂ hcen hodd h5

omit [Finite Gs] in
theorem eq_of_hasSL2Model {A : Type} [Group A] {q q' : ℕ} (h : HasSL2Model A (fun r => r = q))
    (h' : HasSL2Model A (fun r => r = q')) : q = q' := by
  obtain ⟨F, iF, fF, hq, ⟨e⟩⟩ := h
  obtain ⟨F', iF', fF', hq', ⟨e'⟩⟩ := h'
  have hc := Nat.card_congr (e.symm.trans e').toEquiv
  rw [card_statedSL_two' F, card_statedSL_two' F', hq, hq'] at hc
  have hq2 : 2 ≤ q := by
    have : 1 < Nat.card F := Finite.one_lt_card
    omega
  have hq2' : 2 ≤ q' := by
    have : 1 < Nat.card F' := Finite.one_lt_card
    omega
  by_contra hne
  rcases Nat.lt_or_gt_of_ne hne with hlt | hlt
  · have h1 : q ^ 2 < q' ^ 2 := Nat.pow_lt_pow_left hlt (by norm_num)
    have h2 : q ^ 2 - 1 < q' ^ 2 - 1 :=
      Nat.sub_lt_sub_right (Nat.one_le_pow _ _ (by omega)) h1
    have : q * (q ^ 2 - 1) < q' * (q' ^ 2 - 1) :=
      lt_of_le_of_lt (Nat.mul_le_mul_left q h2.le) (Nat.mul_lt_mul_of_pos_right hlt (by omega))
    omega
  · have h1 : q' ^ 2 < q ^ 2 := Nat.pow_lt_pow_left hlt (by norm_num)
    have h2 : q' ^ 2 - 1 < q ^ 2 - 1 :=
      Nat.sub_lt_sub_right (Nat.one_le_pow _ _ (by omega)) h1
    have : q' * (q' ^ 2 - 1) < q * (q ^ 2 - 1) :=
      lt_of_le_of_lt (Nat.mul_le_mul_left q' h2.le) (Nat.mul_lt_mul_of_pos_right hlt (by omega))
    omega

include C in
theorem FusedCtx.relIndex_le [Finite G] (hcen : Cen2 G z S) : (RC S z).relIndex S ≤ 4 := by
  obtain ⟨σ, hσ⟩ := C.exists_sigma hcen
  set H : Subgroup ↥(C.S₁ : Subgroup Gs) :=
    ((C.S₁ : Subgroup Gs) ⊓ (C.E₁ ⊔ C.E₂)).subgroupOf (C.S₁ : Subgroup Gs) with hH
  have hcomap : (RC S z).subgroupOf S = H.comap σ.toMonoidHom := by
    ext s
    rw [Subgroup.mem_comap, Subgroup.mem_subgroupOf, hH, Subgroup.mem_subgroupOf]
    constructor
    · intro hs
      exact ⟨(σ s).2, (hσ s).1 hs.2⟩
    · intro hs
      exact ⟨s.2, (hσ s).2 hs.2⟩
  have h1 : (RC S z).relIndex S = H.index := by
    rw [Subgroup.relIndex, hcomap, Subgroup.index_comap_of_surjective _ σ.surjective]
  have h2 : Nat.card ↥H * H.index = Nat.card ↥(C.S₁ : Subgroup Gs) := Subgroup.card_mul_index H
  have h3 : Nat.card ↥H = Nat.card ↥((C.S₁ : Subgroup Gs) ⊓ (C.E₁ ⊔ C.E₂)) :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv
  have h4 := C.pkg.data.syl.card_S
  have hpos : 0 < Nat.card ↥((C.S₁ : Subgroup Gs) ⊓ (C.E₁ ⊔ C.E₂)) := Nat.card_pos
  rw [h1]
  rw [h3, h4] at h2
  have : H.index = 4 := by
    have h5 : Nat.card ↥((C.S₁ : Subgroup Gs) ⊓ (C.E₁ ⊔ C.E₂)) * H.index =
        Nat.card ↥((C.S₁ : Subgroup Gs) ⊓ (C.E₁ ⊔ C.E₂)) * 4 := by rw [h2]; ring
    exact Nat.eq_of_mul_eq_mul_left hpos h5
  omega

end Norm

section Stage3

theorem l4FExtra_of_leaf (hfus : FusedModelLeaf) : L4FExtra := by
  intro G _ _ z S ε q hcen hE L₁ L₂ hpair
  obtain ⟨hone, Gs, iG, fG, p, f, hp, hp2, hm, hS, hC⟩ := id hE
  obtain ⟨C⟩ := fused_ctx_of hfus hcen hp hp2 hm hS hC
  have hq5 : 5 ≤ p ^ f := by
    rcases hm with ⟨-, h8, -⟩ | ⟨-, h8, h3, -⟩ <;> omega
  have hodd : Odd (p ^ f) := (hp.odd_of_ne_two hp2).pow
  have hcomp := C.pkg.data.comps
  have hset : ({L₁, L₂} : Set (Subgroup (CentralizerBar z))) = {C.pull C.E₁, C.pull C.E₂} :=
    hpair.comps.symm.trans (C.comps (isSylowOf_barOf hcen.sylow).isPGroup)
  have hL₁ : L₁ = C.pull C.E₁ ∨ L₁ = C.pull C.E₂ := by
    have : L₁ ∈ ({C.pull C.E₁, C.pull C.E₂} : Set (Subgroup (CentralizerBar z))) := by
      rw [← hset]; exact Or.inl rfl
    exact this
  have hL₂ : L₂ = C.pull C.E₁ ∨ L₂ = C.pull C.E₂ := by
    have : L₂ ∈ ({C.pull C.E₁, C.pull C.E₂} : Set (Subgroup (CentralizerBar z))) := by
      rw [← hset]; exact Or.inr rfl
    exact this
  have hqq : q = p ^ f := by
    have hs : HasSL2Model ↥L₁ (fun r => r = q) := hpair.sl₁
    have hs' : HasSL2Model ↥L₁ (fun r => r = p ^ f) := by
      rcases hL₁ with rfl | rfl
      · exact ModelLUT.hasSL2Model_of_equiv (C.pullEquiv C.E₁_le_X) hcomp.sl₁
      · exact ModelLUT.hasSL2Model_of_equiv (C.pullEquiv C.E₂_le_X) hcomp.sl₂
    exact eq_of_hasSL2Model hs hs'
  subst hqq
  refine ⟨?_, C.relIndex_le hcen, C.induced hcen hodd hq5 hL₁, C.induced hcen hodd hq5 hL₂⟩
  rcases hm with ⟨h1, h8, -⟩ | ⟨h1, h8, -, -⟩
  · subst h1; simpa using h8
  · subst h1; simpa using h8

end Stage3

theorem l4FExtra_thm : L4FExtra := l4FExtra_of_leaf fusedModelLeaf

end CFSG.GH74.GLS.Stage1.Main
