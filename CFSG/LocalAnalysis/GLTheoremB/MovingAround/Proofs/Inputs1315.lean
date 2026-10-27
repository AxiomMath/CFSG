module

public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Lemma1315b
public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Prop1310a5
public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.SchurFacts
public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Lemma129b
public import CFSG.ClassicalInvolution.SmallCases.A7MSLIso
public import CFSG.LocalAnalysis.GLTheoremA.CatC.LieCompHolds
public import CFSG.HardMathSupport.Dickson.KD.CharP
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I112DiagChev
public import CFSG.Adapters.StatedSmallProjOrders
public import CFSG.Quasithin.EmptyFaithful.T1515C4Mod

public section

namespace CFSG.LocalAnalysis.GLTheoremB.MovingAround.Inputs1315

open CFSG.Open Matrix

section Model

variable {F : Type} [Field F]

abbrev L2S (F : Type) [Field F] : Type := StatedProj (StatedSL 2 F)

@[expose] def uGL (v : F) : GL (Fin 2) F :=
  ⟨!![1, v; 0, 1], !![1, -v; 0, 1], by simp [Matrix.mul_fin_two, Matrix.one_fin_two],
    by simp [Matrix.mul_fin_two, Matrix.one_fin_two]⟩

@[expose] def lGL (v : F) : GL (Fin 2) F :=
  ⟨!![1, 0; v, 1], !![1, 0; -v, 1], by simp [Matrix.mul_fin_two, Matrix.one_fin_two],
    by simp [Matrix.mul_fin_two, Matrix.one_fin_two]⟩

theorem coe_uGL (v : F) : ((uGL v : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) = !![1, v; 0, 1] :=
  rfl

theorem coe_lGL (v : F) : ((lGL v : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) = !![1, 0; v, 1] :=
  rfl

theorem uGL_mem (v : F) : uGL v ∈ StatedSL 2 F :=
  StatedAPI.mem_statedSL_of_det (by rw [coe_uGL, Matrix.det_fin_two_of]; ring)

theorem lGL_mem (v : F) : lGL v ∈ StatedSL 2 F :=
  StatedAPI.mem_statedSL_of_det (by rw [coe_lGL, Matrix.det_fin_two_of]; ring)

@[expose] def uS (v : F) : StatedSL 2 F := ⟨uGL v, uGL_mem v⟩

@[expose] def lS (v : F) : StatedSL 2 F := ⟨lGL v, lGL_mem v⟩

theorem entries_of_eq {X Y : Matrix (Fin 2) (Fin 2) F} (h : X = Y) :
    X 0 0 = Y 0 0 ∧ X 0 1 = Y 0 1 ∧ X 1 0 = Y 1 0 ∧ X 1 1 = Y 1 1 :=
  ⟨by rw [h], by rw [h], by rw [h], by rw [h]⟩

theorem matrix_ext_two {X Y : Matrix (Fin 2) (Fin 2) F} (h00 : X 0 0 = Y 0 0) (h01 : X 0 1 = Y 0 1)
    (h10 : X 1 0 = Y 1 0) (h11 : X 1 1 = Y 1 1) : X = Y := by
  ext i j
  fin_cases i <;> fin_cases j <;> assumption

theorem center_eq_bot : Subgroup.center (L2S F) = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  induction x using QuotientGroup.induction_on with
  | H A =>
    rw [Subgroup.mem_bot]
    set M : Matrix (Fin 2) (Fin 2) F := ((A : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) with hM
    have hdet : M 0 0 * M 1 1 - M 0 1 * M 1 0 = 1 := by
      rw [← Matrix.det_fin_two]
      exact StatedAPI.det_of_mem_statedSL A.2
    have hu := Subgroup.mem_center_iff.1 hx (QuotientGroup.mk (uS 1))
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, StatedAPI.statedProj_mk_eq_iff] at hu
    obtain ⟨c, hc⟩ := hu
    have hc' : M * !![1, 1; 0, 1] = !![1, 1; 0, 1] * M * ((c : F) • (1 : Matrix (Fin 2) (Fin 2) F)) := by
      simpa [uS, coe_uGL, hM] using hc
    obtain ⟨e00, e01, e10, e11⟩ := entries_of_eq hc'
    simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.one_apply, Matrix.vecMul, dotProduct] at e00 e01 e10 e11
    have hl := Subgroup.mem_center_iff.1 hx (QuotientGroup.mk (lS 1))
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, StatedAPI.statedProj_mk_eq_iff] at hl
    obtain ⟨c', hc''⟩ := hl
    have hl' : M * !![1, 0; 1, 1] = !![1, 0; 1, 1] * M * ((c' : F) • (1 : Matrix (Fin 2) (Fin 2) F)) := by
      simpa [lS, coe_lGL, hM] using hc''
    obtain ⟨f00, f01, f10, f11⟩ := entries_of_eq hl'
    simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.one_apply, Matrix.vecMul, dotProduct] at f00 f01 f10 f11
    have hc1 : (c : F) = 1 := by
      by_contra hne
      have hne' : (c : F) - 1 ≠ 0 := sub_ne_zero.2 hne
      have he : M 1 0 = 0 := by
        have : M 1 0 * ((c : F) - 1) = 0 := by linear_combination -e10
        exact (mul_eq_zero.1 this).resolve_right hne'
      have ha : M 0 0 = 0 := by
        have : M 0 0 * ((c : F) - 1) = 0 := by linear_combination -e00 - (c : F) * he
        exact (mul_eq_zero.1 this).resolve_right hne'
      rw [ha, he] at hdet
      simp at hdet
    have hc1' : (c' : F) = 1 := by
      by_contra hne
      have hne' : (c' : F) - 1 ≠ 0 := sub_ne_zero.2 hne
      have hb : M 0 1 = 0 := by
        have : M 0 1 * ((c' : F) - 1) = 0 := by linear_combination -f01
        exact (mul_eq_zero.1 this).resolve_right hne'
      have ha : M 0 0 = 0 := by
        have : M 0 0 * ((c' : F) - 1) = 0 := by linear_combination -f00 + hb
        exact (mul_eq_zero.1 this).resolve_right hne'
      rw [ha, hb] at hdet
      simp at hdet
    rw [hc1] at e00 e01
    rw [hc1'] at f00
    have he : M 1 0 = 0 := by linear_combination -e00
    have hb : M 0 1 = 0 := by linear_combination f00
    have hd : M 1 1 = M 0 0 := by linear_combination -e01
    have ha0 : M 0 0 ≠ 0 := by
      intro h0
      rw [h0, he] at hdet
      simp at hdet
    rw [QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf, StatedScalars, MonoidHom.mem_range]
    refine ⟨Units.mk0 (M 0 0) ha0, Units.ext ?_⟩
    rw [Matrix.GeneralLinearGroup.coe_scalar]
    refine matrix_ext_two ?_ ?_ ?_ ?_ <;> simp [hM.symm, he, hb, hd]

theorem uGL_add (v w : F) : uGL (v + w) = uGL v * uGL w := by
  apply Units.ext
  rw [Units.val_mul, coe_uGL, coe_uGL, coe_uGL, Matrix.mul_fin_two]
  simp [add_comm]

theorem uGL_zero : uGL (0 : F) = 1 := by
  apply Units.ext
  rw [coe_uGL, Units.val_one, Matrix.one_fin_two]

@[expose] noncomputable def uHom : Multiplicative F →* L2S F where
  toFun v := QuotientGroup.mk (uS (Multiplicative.toAdd v))
  map_one' := by
    rw [toAdd_one]
    have : uS (0 : F) = 1 := Subtype.ext uGL_zero
    rw [this, QuotientGroup.mk_one]
  map_mul' v w := by
    rw [toAdd_mul, ← QuotientGroup.mk_mul]
    congr 1
    exact Subtype.ext (uGL_add _ _)

theorem uHom_apply (v : F) : uHom (Multiplicative.ofAdd v) = QuotientGroup.mk (uS v) := rfl

theorem uHom_injective : Function.Injective (uHom : Multiplicative F →* L2S F) := by
  rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
  intro v hv
  rw [MonoidHom.mem_ker] at hv
  change (QuotientGroup.mk (uS (Multiplicative.toAdd v)) : L2S F) = 1 at hv
  rw [QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf, StatedScalars, MonoidHom.mem_range] at hv
  obtain ⟨c, hc⟩ := hv
  have h := congrArg (fun g : GL (Fin 2) F => (g : Matrix (Fin 2) (Fin 2) F) 0 1) hc
  simp only [Matrix.GeneralLinearGroup.coe_scalar, uS, coe_uGL] at h
  simp at h
  rw [Subgroup.mem_bot]
  apply Multiplicative.toAdd.injective
  rw [toAdd_one]
  exact h.symm

@[expose] noncomputable def Ubar (F : Type) [Field F] : Subgroup (L2S F) := (uHom (F := F)).range

theorem mem_Ubar_iff {x : L2S F} : x ∈ Ubar F ↔ ∃ v : F, QuotientGroup.mk (uS v) = x := by
  constructor
  · rintro ⟨v, rfl⟩
    exact ⟨Multiplicative.toAdd v, rfl⟩
  · rintro ⟨v, rfl⟩
    exact ⟨Multiplicative.ofAdd v, rfl⟩

theorem card_Ubar [Finite F] : Nat.card (Ubar F) = Nat.card F := by
  rw [Ubar, ← Nat.card_congr (MonoidHom.ofInjective uHom_injective).toEquiv]
  exact Nat.card_congr Multiplicative.toAdd

theorem isElemAbelian_Ubar (p : ℕ) [CharP F p] : IsElemAbelian p (Ubar F) := by
  refine ⟨⟨⟨fun a b => ?_⟩⟩, fun x hx => ?_⟩
  · obtain ⟨v, hv⟩ := a.2
    obtain ⟨w, hw⟩ := b.2
    apply Subtype.ext
    change (a : L2S F) * b = b * a
    rw [← hv, ← hw, ← map_mul, ← map_mul, mul_comm]
  · obtain ⟨v, rfl⟩ := hx
    rw [← map_pow]
    have : v ^ p = 1 := by
      apply Multiplicative.toAdd.injective
      rw [toAdd_pow, toAdd_one, nsmul_eq_mul, CharP.cast_eq_zero, zero_mul]
    rw [this, map_one]

end Model

section Sylow

theorem exists_le_conj {G : Type*} [Group G] [Finite G] {p : ℕ} [hp : Fact p.Prime] {k : ℕ}
    {U : Subgroup G} (hU : Nat.card U = p ^ k) (hG : ¬ p ^ (k + 1) ∣ Nat.card G)
    {S : Subgroup G} (hS : IsPGroup p S) :
    ∃ g : G, S ≤ U.map (MulAut.conj g).toMonoidHom := by
  have hUp : IsPGroup p U := IsPGroup.of_card hU
  obtain ⟨P, hUP⟩ := hUp.exists_le_sylow
  have hPU : (P : Subgroup G) = U := by
    obtain ⟨m, hm⟩ := (IsPGroup.iff_card.1 P.isPGroup')
    have hdvd : p ^ m ∣ Nat.card G := hm ▸ Subgroup.card_subgroup_dvd_card (P : Subgroup G)
    have hmk : m ≤ k := by
      by_contra hlt
      exact hG ((pow_dvd_pow p (by omega : k + 1 ≤ m)).trans hdvd)
    symm
    refine Subgroup.eq_of_le_of_card_ge hUP ?_
    rw [hm, hU]
    exact Nat.pow_le_pow_right hp.out.pos hmk
  obtain ⟨Q, hSQ⟩ := hS.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G P Q
  refine ⟨g, fun x hx => ?_⟩
  have hxQ : x ∈ (Q : Subgroup G) := hSQ hx
  rw [← hg, Sylow.coe_subgroup_smul, hPU] at hxQ
  obtain ⟨u, hu, hux⟩ := (Subgroup.mem_smul_pointwise_iff_exists x (MulAut.conj g) U).1 hxQ
  exact ⟨u, hu, hux⟩

variable {F : Type} [Field F]

theorem charP_of_card [Finite F] {p n : ℕ} (hp : p.Prime) (hF : Nat.card F = p ^ n) : CharP F p := by
  haveI := Fintype.ofFinite F
  haveI : Fact p.Prime := ⟨hp⟩
  exact charP_of_card_eq_prime_pow (by rw [← Nat.card_eq_fintype_card]; exact hF)

theorem not_dvd_card_L2S [Finite F] {p n : ℕ} (hp : p.Prime) (hn : 1 ≤ n) (hF : Nat.card F = p ^ n) :
    ¬ p ^ (n + 1) ∣ Nat.card (L2S F) := by
  intro h
  have h1 : Nat.card (L2S F) ∣ Nat.card (StatedSL 2 F) := Subgroup.card_quotient_dvd_card _
  rw [StatedAPI.card_statedSL_two, hF] at h1
  have h2 := h.trans h1
  rw [pow_succ] at h2
  have h3 : p ∣ (p ^ n) ^ 2 - 1 := Nat.dvd_of_mul_dvd_mul_left (pow_pos hp.pos n) h2
  have h4 : p ∣ (p ^ n) ^ 2 := dvd_pow (dvd_pow_self p (by omega)) two_ne_zero
  have h5 : 1 ≤ (p ^ n) ^ 2 := Nat.one_le_pow _ _ (pow_pos hp.pos n)
  have h6 : p ∣ 1 := by
    have := Nat.dvd_sub h4 h3
    rwa [Nat.sub_sub_self h5] at this
  exact hp.one_lt.ne' (Nat.dvd_one.1 h6)

theorem exists_le_conj_Ubar [Finite F] {p n : ℕ} [hp : Fact p.Prime] (hn : 1 ≤ n)
    (hF : Nat.card F = p ^ n) {S : Subgroup (L2S F)} (hS : IsPGroup p S) :
    ∃ g : L2S F, S ≤ (Ubar F).map (MulAut.conj g).toMonoidHom :=
  exists_le_conj (by rw [card_Ubar, hF]) (not_dvd_card_L2S hp.out hn hF) hS

theorem pGroup_facts [Finite F] {p n : ℕ} [hp : Fact p.Prime] (hn : 1 ≤ n)
    (hF : Nat.card F = p ^ n) {S : Subgroup (L2S F)} (hS : IsPGroup p S) :
    IsElemAbelian p S ∧ Nat.card S ≤ p ^ n := by
  haveI := charP_of_card hp.out hF
  obtain ⟨g, hg⟩ := exists_le_conj_Ubar hn hF hS
  have hel : IsElemAbelian p ((Ubar F).map (MulAut.conj g).toMonoidHom) :=
    CFSG.SectionRank.isElemAbelian_map (isElemAbelian_Ubar p) _
  refine ⟨Lemma1315b.elemAbelian_mono hel hg, ?_⟩
  calc Nat.card S ≤ Nat.card ((Ubar F).map (MulAut.conj g).toMonoidHom) := Subgroup.card_le_of_le hg
    _ = Nat.card (Ubar F) := Subgroup.card_map_of_injective (MulAut.conj g).injective
    _ = p ^ n := by rw [card_Ubar, hF]

theorem exists_pGroup_card [Finite F] {p n : ℕ} [hp : Fact p.Prime] (hF : Nat.card F = p ^ n) :
    ∃ S : Subgroup (L2S F), IsPGroup p S ∧ Nat.card S = p ^ n := by
  haveI := charP_of_card hp.out hF
  exact ⟨Ubar F, Lemma1315b.isPGroup_of_elemAbelian (isElemAbelian_Ubar p), by rw [card_Ubar, hF]⟩

end Sylow

section Torus

variable {F : Type} [Field F]

@[expose] noncomputable def dGL (a : Fˣ) : GL (Fin 2) F :=
  ⟨!![(a : F), 0; 0, (a : F)⁻¹], !![(a : F)⁻¹, 0; 0, (a : F)],
    by simp [Matrix.mul_fin_two, Matrix.one_fin_two],
    by simp [Matrix.mul_fin_two, Matrix.one_fin_two]⟩

theorem coe_dGL (a : Fˣ) :
    ((dGL a : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) = !![(a : F), 0; 0, (a : F)⁻¹] := rfl

theorem dGL_mem (a : Fˣ) : dGL a ∈ StatedSL 2 F :=
  StatedAPI.mem_statedSL_of_det (by rw [coe_dGL, Matrix.det_fin_two_of]; simp)

@[expose] noncomputable def dS (a : Fˣ) : StatedSL 2 F := ⟨dGL a, dGL_mem a⟩

theorem dGL_mul_uGL (a : Fˣ) (v : F) : dGL a * uGL v = uGL ((a : F) ^ 2 * v) * dGL a := by
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, coe_dGL, coe_uGL, coe_uGL]
  have ha : (a : F) ≠ 0 := a.ne_zero
  refine matrix_ext_two ?_ ?_ ?_ ?_ <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
  field_simp

theorem conj_uHom (a : Fˣ) (v : F) :
    (QuotientGroup.mk (dS a) : L2S F) * QuotientGroup.mk (uS v) * (QuotientGroup.mk (dS a))⁻¹ =
      QuotientGroup.mk (uS ((a : F) ^ 2 * v)) := by
  rw [mul_inv_eq_iff_eq_mul, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
  congr 1
  exact Subtype.ext (dGL_mul_uGL a v)

theorem mem_normalizer_of_conj_mem {G : Type*} [Group G] {S : Subgroup G} [Finite S] {n : G}
    (h : ∀ x ∈ S, n * x * n⁻¹ ∈ S) : n ∈ Subgroup.normalizer (S : Set G) := by
  have hle : S.map (MulAut.conj n).toMonoidHom ≤ S := by
    rintro _ ⟨x, hx, rfl⟩
    exact h x hx
  have heq : S.map (MulAut.conj n).toMonoidHom = S :=
    Subgroup.eq_of_le_of_card_ge hle (by rw [Subgroup.card_map_of_injective (MulAut.conj n).injective])
  rw [Subgroup.mem_normalizer_iff]
  intro x
  refine ⟨h x, fun hx => ?_⟩
  rw [← heq] at hx
  obtain ⟨y, hy, hyx⟩ := hx
  have : y = x := by
    have hyx' : n * y * n⁻¹ = n * x * n⁻¹ := hyx
    simpa using hyx'
  rwa [← this]

theorem torus_fact [Finite F] {p n : ℕ} [hp : Fact p.Prime] (hp5 : 5 ≤ p) (hn : 1 ≤ n)
    (hF : Nat.card F = p ^ n) {S : Subgroup (L2S F)} (hS : IsPGroup p S) (hSp : Nat.card S = p) :
    ∃ m ∈ Subgroup.normalizer (S : Set (L2S F)), ∃ s ∈ S, m * s * m⁻¹ ≠ s := by
  haveI := charP_of_card hp.out hF
  obtain ⟨g, hg⟩ := exists_le_conj_Ubar hn hF hS
  have hS1 : (⊥ : Subgroup (L2S F)) ≠ S := by
    intro h
    rw [← h, Subgroup.card_bot] at hSp
    exact hp.out.one_lt.ne hSp
  obtain ⟨s, hsS, hs1⟩ : ∃ s ∈ S, s ≠ 1 := by
    by_contra hcon
    push Not at hcon
    exact hS1 ((Subgroup.eq_bot_iff_forall S).2 hcon).symm
  obtain ⟨y, hyU, rfl⟩ := hg hsS
  obtain ⟨v, rfl⟩ := mem_Ubar_iff.1 hyU
  have h2 : (2 : F) ≠ 0 := by
    intro h
    have h2' : ((2 : ℕ) : F) = 0 := by exact_mod_cast h
    rw [CharP.cast_eq_zero_iff F p] at h2'
    have := Nat.le_of_dvd (by norm_num) h2'
    omega
  set t : L2S F := QuotientGroup.mk (dS (Units.mk0 2 h2)) with ht
  set m : L2S F := g * t * g⁻¹ with hm
  have hconj : ∀ w : F, m * (MulAut.conj g (QuotientGroup.mk (uS w))) * m⁻¹ =
      MulAut.conj g (QuotientGroup.mk (uS (4 * w))) := by
    intro w
    have h4 : ((Units.mk0 (2 : F) h2 : Fˣ) : F) ^ 2 * w = 4 * w := by
      rw [Units.val_mk0]; norm_num
    have key := conj_uHom (Units.mk0 (2 : F) h2) w
    rw [h4] at key
    simp only [MulAut.conj_apply, hm, ← key, ht]
    group
  have hpow : ∀ w : F, (QuotientGroup.mk (uS (4 * w)) : L2S F) = (QuotientGroup.mk (uS w)) ^ 4 := by
    intro w
    rw [← uHom_apply, ← uHom_apply, ← map_pow]
    congr 1
    apply Multiplicative.toAdd.injective
    rw [toAdd_pow, toAdd_ofAdd, toAdd_ofAdd, nsmul_eq_mul]
    norm_num
  set s0 : L2S F := MulAut.conj g (QuotientGroup.mk (uS v)) with hs0
  have hms : m * s0 * m⁻¹ = s0 ^ 4 := by
    rw [hs0, hconj, hpow, map_pow]
  have hord : orderOf s0 = p := by
    have hdvd : orderOf s0 ∣ p := hSp ▸ Subgroup.orderOf_dvd_natCard S hsS
    rcases (Nat.dvd_prime hp.out).1 hdvd with h | h
    · exact absurd (orderOf_eq_one_iff.1 h) hs1
    · exact h
  have hSz : S = Subgroup.zpowers s0 := by
    symm
    refine Subgroup.eq_of_le_of_card_ge ((Subgroup.zpowers_le).2 hsS) ?_
    rw [Nat.card_zpowers, hord, hSp]
  refine ⟨m, mem_normalizer_of_conj_mem fun x hx => ?_, s0, hsS, ?_⟩
  · rw [hSz] at hx ⊢
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.1 hx
    have : m * s0 ^ i * m⁻¹ = (s0 ^ 4) ^ i := by
      rw [← hms, conj_zpow]
    rw [this, ← zpow_natCast, ← _root_.zpow_mul]
    exact Subgroup.zpow_mem_zpowers _ _
  · rw [hms]
    intro h
    have h3 : s0 ^ 3 = 1 := by
      have : s0 ^ 4 = s0 ^ 3 * s0 := pow_succ s0 3
      rw [this] at h
      exact mul_eq_right.1 h
    have := orderOf_dvd_of_pow_eq_one h3
    rw [hord] at this
    have := Nat.le_of_dvd (by norm_num) this
    omega

end Torus

@[expose] def InputAutPSL2 : Prop :=
  ∀ (p : ℕ), p.Prime → ∀ (F : Type) [Field F] [Finite F], CharP F p →
    ∀ α : MulAut (StatedProj (StatedSL 2 F)), ∃ (g : GL (Fin 2) F) (j : ℕ),
      ∀ A B : StatedSL 2 F,
        ((B : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) =
          (g : Matrix (Fin 2) (Fin 2) F) *
              ((A : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F).map (· ^ p ^ j) *
            ((g⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) →
        α (QuotientGroup.mk A) = QuotientGroup.mk B

section Aut

open CFSG.HardMathSupport.Solomon.LocalBalance (innerAut)

variable {F : Type} [Field F] (p : ℕ) [hp : Fact p.Prime] [CharP F p]

noncomputable abbrev frobGL (j : ℕ) : GL (Fin 2) F →* GL (Fin 2) F :=
  Matrix.GeneralLinearGroup.map (iterateFrobenius F p j)

theorem coe_frobGL (j : ℕ) (A : GL (Fin 2) F) :
    ((frobGL p j A : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) =
      (A : Matrix (Fin 2) (Fin 2) F).map (· ^ p ^ j) := rfl

theorem frobGL_mem {j : ℕ} {A : GL (Fin 2) F} (hA : A ∈ StatedSL 2 F) : frobGL p j A ∈ StatedSL 2 F := by
  apply StatedAPI.mem_statedSL_of_det
  have h := (iterateFrobenius F p j).map_det (A : Matrix (Fin 2) (Fin 2) F)
  rw [StatedAPI.det_of_mem_statedSL hA, map_one] at h
  exact h.symm

theorem statedSL_normal : (StatedSL 2 F).Normal := by
  rw [StatedAPI.statedSL_eq_ker_det]
  exact MonoidHom.normal_ker _

@[expose] noncomputable def semiS (g : GL (Fin 2) F) (j : ℕ) (A : StatedSL 2 F) : StatedSL 2 F :=
  ⟨g * frobGL p j A * g⁻¹, (statedSL_normal (F := F)).conj_mem _ (frobGL_mem p A.2) g⟩

@[expose] def IsSemi (α : MulAut (L2S F)) (g : GL (Fin 2) F) (j : ℕ) : Prop :=
  ∀ A : StatedSL 2 F, α (QuotientGroup.mk A) = QuotientGroup.mk (semiS p g j A)

theorem isSemi_of_input [Finite F] (hI : InputAutPSL2) (α : MulAut (L2S F)) :
    ∃ (g : GL (Fin 2) F) (j : ℕ), IsSemi p α g j := by
  obtain ⟨g, j, h⟩ := hI p hp.out F inferInstance α
  exact ⟨g, j, fun A => h A (semiS p g j A) rfl⟩

theorem frobGL_frobGL (i j : ℕ) (A : GL (Fin 2) F) :
    frobGL p j (frobGL p i A) = frobGL p (i + j) A := by
  apply Units.ext
  ext k l
  simp only [coe_frobGL, Matrix.map_apply]
  rw [← pow_mul, ← pow_add]

theorem frobGL_zero (A : GL (Fin 2) F) : frobGL p 0 A = A := by
  apply Units.ext
  ext k l
  simp [coe_frobGL]

theorem frobGL_eq_self {j : ℕ} (hfix : ∀ x : F, x ^ p ^ j = x) (A : GL (Fin 2) F) :
    frobGL p j A = A := by
  apply Units.ext
  ext k l
  simp only [coe_frobGL, Matrix.map_apply]
  exact hfix _

theorem frobGL_uGL (j : ℕ) (v : F) : frobGL p j (uGL v) = uGL (v ^ p ^ j) := by
  apply Units.ext
  rw [coe_frobGL, coe_uGL, coe_uGL]
  have h0 : (0 : F) ^ p ^ j = 0 := zero_pow (pow_ne_zero j hp.out.ne_zero)
  refine matrix_ext_two ?_ ?_ ?_ ?_ <;> simp [h0]

theorem IsSemi.mul {α β : MulAut (L2S F)} {g h : GL (Fin 2) F} {j i : ℕ} (hα : IsSemi p α g j)
    (hβ : IsSemi p β h i) : IsSemi p (α * β) (g * frobGL p j h) (i + j) := by
  intro A
  rw [MulAut.mul_apply, hβ A, hα]
  congr 1
  apply Subtype.ext
  change g * frobGL p j (h * frobGL p i A * h⁻¹) * g⁻¹ =
    g * frobGL p j h * frobGL p (i + j) A * (g * frobGL p j h)⁻¹
  rw [map_mul, map_mul, map_inv, frobGL_frobGL]
  group

theorem IsSemi.one : IsSemi p (1 : MulAut (L2S F)) 1 0 := by
  intro A
  rw [MulAut.one_apply]
  congr 1
  apply Subtype.ext
  change (A : GL (Fin 2) F) = 1 * frobGL p 0 A * 1⁻¹
  rw [frobGL_zero]
  group

theorem IsSemi.pow {α : MulAut (L2S F)} {g : GL (Fin 2) F} {j : ℕ} (hα : IsSemi p α g j) :
    ∀ k : ℕ, ∃ G : GL (Fin 2) F, IsSemi p (α ^ k) G (j * k)
  | 0 => ⟨1, by rw [pow_zero, mul_zero]; exact IsSemi.one p⟩
  | k + 1 => by
    obtain ⟨G, hG⟩ := hα.pow k
    refine ⟨G * frobGL p (j * k) g, ?_⟩
    have h := hG.mul p hα
    rw [show j * (k + 1) = j + j * k by ring, pow_succ]
    exact h

theorem inner_of_semi {z : MulAut (L2S F)} {k : GL (Fin 2) F} {j : ℕ} (hz : IsSemi p z k j)
    (hfix : ∀ x : F, x ^ p ^ j = x) {μ : Fˣ}
    (hμ : (k : Matrix (Fin 2) (Fin 2) F).det = (μ : F) ^ 2) : z ∈ innerAut (L2S F) := by
  set s : GL (Fin 2) F := Matrix.GeneralLinearGroup.scalar (Fin 2) μ⁻¹ with hs
  have hscen : s ∈ Subgroup.center (GL (Fin 2) F) := by
    rw [Matrix.GeneralLinearGroup.center_eq_range_scalar]
    exact ⟨μ⁻¹, rfl⟩
  set c : GL (Fin 2) F := s * k with hc
  have hcS : c ∈ StatedSL 2 F := by
    apply StatedAPI.mem_statedSL_of_det
    rw [hc, Units.val_mul, Matrix.det_mul, hμ, hs, Matrix.GeneralLinearGroup.coe_scalar]
    simp
  refine ⟨QuotientGroup.mk ⟨c, hcS⟩, ?_⟩
  ext x
  induction x using QuotientGroup.induction_on with
  | H A =>
    rw [MulAut.conj_apply, hz A, ← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul,
      ← QuotientGroup.mk_mul]
    congr 1
    apply Subtype.ext
    change c * (A : GL (Fin 2) F) * c⁻¹ = k * frobGL p j A * k⁻¹
    rw [frobGL_eq_self p hfix, hc, _root_.mul_inv_rev]
    have h1 : s * (k * (A : GL (Fin 2) F) * k⁻¹) = (k * (A : GL (Fin 2) F) * k⁻¹) * s :=
      (Subgroup.mem_center_iff.1 hscen _).symm
    calc s * k * (A : GL (Fin 2) F) * (k⁻¹ * s⁻¹) = s * (k * (A : GL (Fin 2) F) * k⁻¹) * s⁻¹ := by
          group
      _ = k * (A : GL (Fin 2) F) * k⁻¹ := by rw [h1]; group

theorem frobFix_mul {j : ℕ} {x : F} (hfix : x ^ p ^ j = x) : ∀ m : ℕ, x ^ p ^ (j * m) = x
  | 0 => by simp
  | m + 1 => by
    rw [show j * (m + 1) = j * m + j by ring, pow_add, pow_mul, frobFix_mul hfix m, hfix]

theorem inner_of_semi_of_pow (hp2 : p ≠ 2) {z : MulAut (L2S F)} {g : GL (Fin 2) F} {j : ℕ}
    (hz : IsSemi p z g j) (hfix : ∀ x : F, x ^ p ^ j = x) (hzp : z ^ p = 1) :
    z ∈ innerAut (L2S F) := by
  have hodd : Odd p := hp.out.odd_of_ne_two hp2
  set m := (p + 1) / 2 with hm
  have hm2 : m + m = p + 1 := by obtain ⟨r, hr⟩ := hodd; omega
  obtain ⟨h, hh⟩ := hz.pow p m
  have hww := hh.mul p hh
  have hzz : z ^ m * z ^ m = z := by
    rw [← pow_add, hm2, pow_succ, hzp, one_mul]
  rw [hzz] at hww
  have hfix' : ∀ x : F, x ^ p ^ (j * m + j * m) = x := by
    intro x
    rw [show j * m + j * m = j * (m + m) by ring]
    exact frobFix_mul p (hfix x) _
  obtain ⟨r, hr⟩ : ∃ r, 1 + p ^ (j * m) = 2 * r := by
    obtain ⟨t, ht⟩ : Odd (p ^ (j * m)) := hodd.pow
    exact ⟨t + 1, by omega⟩
  set δ : Fˣ := Matrix.GeneralLinearGroup.det h with hδ
  refine inner_of_semi p hww hfix' (μ := δ ^ r) ?_
  rw [Units.val_mul, Matrix.det_mul]
  have hdet : ((frobGL p (j * m) h : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F).det =
      (h : Matrix (Fin 2) (Fin 2) F).det ^ p ^ (j * m) :=
    ((iterateFrobenius F p (j * m)).map_det (h : Matrix (Fin 2) (Fin 2) F)).symm
  rw [hdet, Units.val_pow_eq_pow_val, hδ, Matrix.GeneralLinearGroup.val_det_apply, ← pow_mul,
    ← pow_succ', mul_comm r 2, ← hr, add_comm]

theorem frobFix_of_card [Finite F] {n : ℕ} (hF : Nat.card F = p ^ n) (m : ℕ) (x : F) :
    x ^ p ^ (n * m) = x := by
  haveI := Fintype.ofFinite F
  rw [pow_mul, ← hF, Nat.card_eq_fintype_card]
  exact FiniteField.pow_card_pow m x

theorem not_dvd_of_semi [Finite F] (hp2 : p ≠ 2) (hF : Nat.card F = p ^ p) {x : MulAut (L2S F)}
    {g : GL (Fin 2) F} {j : ℕ} (hx : IsSemi p x g j) (hxp : x ^ p = 1)
    (hxI : x ∉ innerAut (L2S F)) : ¬ p ∣ j := by
  rintro ⟨m, rfl⟩
  exact hxI (inner_of_semi_of_pow p hp2 hx (frobFix_of_card p hF m) hxp)

theorem fix_pow_p [Finite F] (hF : Nat.card F = p ^ p) {j : ℕ} (hj : ¬ p ∣ j) {t : F}
    (ht : t ^ p ^ j = t) : t ^ p = t := by
  have hj0 : (j : ZMod p) ≠ 0 := by rwa [Ne, ZMod.natCast_eq_zero_iff]
  set k := ((j : ZMod p)⁻¹).val with hk
  have hk1 : ((j * k : ℕ) : ZMod p) = ((1 : ℕ) : ZMod p) := by
    push_cast
    rw [hk, ZMod.natCast_zmod_val]
    exact mul_inv_cancel₀ hj0
  have hmod : j * k % p = 1 := by
    rw [(ZMod.natCast_eq_natCast_iff' (j * k) 1 p).1 hk1]
    exact Nat.mod_eq_of_lt hp.out.one_lt
  have hjk : j * k = p * (j * k / p) + 1 := by
    have := Nat.div_add_mod (j * k) p
    omega
  have h1 : t ^ p ^ (j * k) = t := frobFix_mul p ht k
  rw [hjk, pow_succ, pow_mul, frobFix_of_card p hF _ t] at h1
  exact h1

theorem card_fix_le [Finite F] : Nat.card {t : F // t ^ p = t} ≤ p := by
  classical
  haveI := Fintype.ofFinite F
  have hP : (Polynomial.X ^ p - Polynomial.X : Polynomial F) ≠ 0 :=
    FiniteField.X_pow_card_sub_X_ne_zero F hp.out.one_lt
  have hdeg : (Polynomial.X ^ p - Polynomial.X : Polynomial F).natDegree = p :=
    FiniteField.X_pow_card_sub_X_natDegree_eq F hp.out.one_lt
  have hZ : (Finset.univ.filter (fun t : F => t ^ p = t)).val ⊆
      (Polynomial.X ^ p - Polynomial.X : Polynomial F).roots := by
    intro t ht
    rw [Polynomial.mem_roots hP, Polynomial.IsRoot, Polynomial.eval_sub, Polynomial.eval_pow,
      Polynomial.eval_X, sub_eq_zero]
    exact (Finset.mem_filter.1 ht).2
  have h := Polynomial.card_le_degree_of_subset_roots hZ
  rw [hdeg] at h
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  exact h

theorem entries_fix {D : GL (Fin 2) F} {v w : F} {lam : Fˣ}
    (h : uGL v * D = D * uGL w * Matrix.GeneralLinearGroup.scalar (Fin 2) lam) :
    v * (D : Matrix (Fin 2) (Fin 2) F) 1 0 = 0 ∧
      v * (D : Matrix (Fin 2) (Fin 2) F) 1 1 = (D : Matrix (Fin 2) (Fin 2) F) 0 0 * w := by
  have hM := congrArg (fun g : GL (Fin 2) F => (g : Matrix (Fin 2) (Fin 2) F)) h
  simp only [Units.val_mul, coe_uGL, Matrix.GeneralLinearGroup.coe_scalar] at hM
  obtain ⟨e00, e01, e10, e11⟩ := entries_of_eq hM
  simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.scalar_apply, Matrix.diagonal_apply] at e00 e01 e10 e11
  have hdet := Matrix.GeneralLinearGroup.det_ne_zero D
  rw [Matrix.det_fin_two] at hdet
  have hl : (lam : F) = 1 := by
    by_contra hne
    have hne' : (lam : F) - 1 ≠ 0 := sub_ne_zero.2 hne
    have hc : (D : Matrix (Fin 2) (Fin 2) F) 1 0 = 0 := by
      have : (D : Matrix (Fin 2) (Fin 2) F) 1 0 * ((lam : F) - 1) = 0 := by linear_combination -e10
      exact (mul_eq_zero.1 this).resolve_right hne'
    have hd : (D : Matrix (Fin 2) (Fin 2) F) 1 1 = 0 := by
      have : (D : Matrix (Fin 2) (Fin 2) F) 1 1 * ((lam : F) - 1) = 0 := by
        linear_combination -e11 - w * (lam : F) * hc
      exact (mul_eq_zero.1 this).resolve_right hne'
    rw [hc, hd] at hdet
    simp at hdet
  rw [hl] at e00 e01
  exact ⟨by linear_combination e00, by linear_combination e01⟩

theorem fix_relation {x : MulAut (L2S F)} {g : GL (Fin 2) F} {j : ℕ} (hx : IsSemi p x g j)
    (C : StatedSL 2 F) (v : F)
    (hfix : x (MulAut.conj (QuotientGroup.mk C : L2S F) (QuotientGroup.mk (uS v))) =
      MulAut.conj (QuotientGroup.mk C : L2S F) (QuotientGroup.mk (uS v))) :
    ∃ lam : Fˣ, uGL v * ((C : GL (Fin 2) F)⁻¹ * g * frobGL p j C) =
      ((C : GL (Fin 2) F)⁻¹ * g * frobGL p j C) * uGL (v ^ p ^ j) *
        Matrix.GeneralLinearGroup.scalar (Fin 2) lam := by
  rw [MulAut.conj_apply, ← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul,
    hx, StatedAPI.statedProj_mk_eq_iff] at hfix
  obtain ⟨lam, hlam⟩ := hfix
  refine ⟨lam, ?_⟩
  set Λ : GL (Fin 2) F := Matrix.GeneralLinearGroup.scalar (Fin 2) lam with hΛdef
  have hcen : Λ ∈ Subgroup.center (GL (Fin 2) F) := by
    rw [Matrix.GeneralLinearGroup.center_eq_range_scalar]
    exact ⟨lam, rfl⟩
  have hGL : (C : GL (Fin 2) F) * uGL v * (C : GL (Fin 2) F)⁻¹ =
      g * (frobGL p j C * uGL (v ^ p ^ j) * (frobGL p j C)⁻¹) * g⁻¹ * Λ := by
    apply Units.ext
    have h1 : ((C * uS v * C⁻¹ : StatedSL 2 F) : GL (Fin 2) F) =
        (C : GL (Fin 2) F) * uGL v * (C : GL (Fin 2) F)⁻¹ := rfl
    have h2 : ((semiS p g j (C * uS v * C⁻¹) : StatedSL 2 F) : GL (Fin 2) F) =
        g * (frobGL p j C * uGL (v ^ p ^ j) * (frobGL p j C)⁻¹) * g⁻¹ := by
      change g * frobGL p j ((C : GL (Fin 2) F) * uGL v * (C : GL (Fin 2) F)⁻¹) * g⁻¹ = _
      rw [map_mul, map_mul, map_inv, frobGL_uGL]
    rw [← h1, hlam, h2]
    simp only [Units.val_mul, hΛdef, Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply,
      Matrix.smul_one_eq_diagonal]
  have hΛ : Λ * (g * frobGL p j C) = (g * frobGL p j C) * Λ :=
    (Subgroup.mem_center_iff.1 hcen _).symm
  calc uGL v * ((C : GL (Fin 2) F)⁻¹ * g * frobGL p j C)
      = (C : GL (Fin 2) F)⁻¹ * ((C : GL (Fin 2) F) * uGL v * (C : GL (Fin 2) F)⁻¹) *
          (g * frobGL p j C) := by group
    _ = (C : GL (Fin 2) F)⁻¹ * (g * (frobGL p j C * uGL (v ^ p ^ j) * (frobGL p j C)⁻¹) * g⁻¹) *
          (Λ * (g * frobGL p j C)) := by rw [hGL]; group
    _ = (C : GL (Fin 2) F)⁻¹ * (g * (frobGL p j C * uGL (v ^ p ^ j) * (frobGL p j C)⁻¹) * g⁻¹) *
          ((g * frobGL p j C) * Λ) := by rw [hΛ]
    _ = ((C : GL (Fin 2) F)⁻¹ * g * frobGL p j C) * uGL (v ^ p ^ j) * Λ := by group

theorem fixed_card_le [Finite F] (hp5 : 5 ≤ p) (hF : Nat.card F = p ^ p) (hI : InputAutPSL2)
    {x : MulAut (L2S F)} (hx : orderOf x = p) (hxI : x ∉ innerAut (L2S F))
    {S : Subgroup (L2S F)} (hS : IsPGroup p S) (hfix : ∀ s ∈ S, x s = s) : Nat.card S ≤ p := by
  have hp2 : p ≠ 2 := by omega
  obtain ⟨g, j, hxs⟩ := isSemi_of_input p hI x
  have hxp : x ^ p = 1 := hx ▸ pow_orderOf_eq_one x
  have hj := not_dvd_of_semi p hp2 hF hxs hxp hxI
  obtain ⟨c, hc⟩ := exists_le_conj_Ubar (n := p) hp.out.one_lt.le hF hS
  obtain ⟨C, rfl⟩ := QuotientGroup.mk_surjective c
  set D : GL (Fin 2) F := (C : GL (Fin 2) F)⁻¹ * g * frobGL p j C with hD
  have hrel : ∀ v : F, MulAut.conj (QuotientGroup.mk C : L2S F) (QuotientGroup.mk (uS v)) ∈ S →
      v * (D : Matrix (Fin 2) (Fin 2) F) 1 0 = 0 ∧
        v * (D : Matrix (Fin 2) (Fin 2) F) 1 1 = (D : Matrix (Fin 2) (Fin 2) F) 0 0 * v ^ p ^ j := by
    intro v hv
    obtain ⟨lam, hlam⟩ := fix_relation p hxs C v (hfix _ hv)
    exact entries_fix hlam
  have hcov : ∀ s ∈ S, ∃ v : F,
      MulAut.conj (QuotientGroup.mk C : L2S F) (QuotientGroup.mk (uS v)) = s := by
    intro s hs
    obtain ⟨y, hyU, rfl⟩ := hc hs
    obtain ⟨v, rfl⟩ := mem_Ubar_iff.1 hyU
    exact ⟨v, rfl⟩
  by_cases hbot : S = ⊥
  · rw [hbot, Subgroup.card_bot]
    exact hp.out.one_lt.le
  obtain ⟨s₀, hs₀, hs₀1⟩ : ∃ s ∈ S, s ≠ 1 := by
    by_contra hcon
    push Not at hcon
    exact hbot ((Subgroup.eq_bot_iff_forall S).2 hcon)
  obtain ⟨v₀, hv₀⟩ := hcov s₀ hs₀
  have hv₀0 : v₀ ≠ 0 := by
    rintro rfl
    apply hs₀1
    rw [← hv₀, ← uHom_apply, ofAdd_zero, map_one, map_one]
  obtain ⟨h10, h11⟩ := hrel v₀ (hv₀ ▸ hs₀)
  have hD10 : (D : Matrix (Fin 2) (Fin 2) F) 1 0 = 0 :=
    (mul_eq_zero.1 h10).resolve_left hv₀0
  have hdet := Matrix.GeneralLinearGroup.det_ne_zero D
  rw [Matrix.det_fin_two, hD10, mul_zero, sub_zero] at hdet
  have hD00 : (D : Matrix (Fin 2) (Fin 2) F) 0 0 ≠ 0 := left_ne_zero_of_mul hdet
  have hD11 : (D : Matrix (Fin 2) (Fin 2) F) 1 1 ≠ 0 := right_ne_zero_of_mul hdet
  have hv₀p : v₀ ^ p ^ j ≠ 0 := pow_ne_zero _ hv₀0
  choose! vs hvs using hcov
  have hfixed : ∀ s ∈ S, (vs s / v₀) ^ p = vs s / v₀ := by
    intro s hs
    apply fix_pow_p p hF hj
    have hs' := (hrel (vs s) ((hvs s hs).symm ▸ hs)).2
    rw [div_pow, div_eq_div_iff hv₀p hv₀0]
    exact mul_left_cancel₀ hD00 (by linear_combination -v₀ * hs' + vs s * h11)
  let φ : S → {t : F // t ^ p = t} := fun s => ⟨vs s / v₀, hfixed s s.2⟩
  have hφ : Function.Injective φ := by
    intro s s' hss'
    have h1 : vs s / v₀ = vs s' / v₀ := congrArg Subtype.val hss'
    have h2 : vs s = vs s' := (div_left_inj' hv₀0).1 h1
    apply Subtype.ext
    rw [← hvs s s.2, ← hvs s' s'.2, h2]
  exact (Nat.card_le_card_of_injective φ hφ).trans (card_fix_le p)

theorem conj_injective {K : Type*} [Group K] (hZ : Subgroup.center K = ⊥) :
    Function.Injective (MulAut.conj : K →* MulAut K) := by
  rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
  intro a ha
  have := Lemma1315b.mem_center_of_conj_eq_one (MonoidHom.mem_ker.1 ha)
  rwa [hZ] at this

theorem conj_apply_aut {K : Type*} [Group K] (x : MulAut K) (s : K) :
    MulAut.conj (x s) = x * MulAut.conj s * x⁻¹ := by
  ext y
  simp only [MulAut.conj_apply, MulAut.mul_apply, map_mul, MulAut.apply_inv_self, map_inv]

theorem comap_conj_facts {K : Type} [Group K] [Finite K] {p : ℕ} (hZ : Subgroup.center K = ⊥)
    {E : Subgroup (MulAut K)} (hEI : E ≤ innerAut K) (hE : IsElemAbelian p E) :
    Nat.card (E.comap (MulAut.conj : K →* MulAut K)) = Nat.card E ∧
      IsElemAbelian p (E.comap (MulAut.conj : K →* MulAut K)) := by
  have hinj := conj_injective hZ
  refine ⟨?_, ⟨⟨fun a b => ?_⟩⟩, fun s hs => ?_⟩
  · have hmap := Subgroup.map_comap_eq_self (f := (MulAut.conj : K →* MulAut K)) hEI
    conv_rhs => rw [← hmap]
    exact (Subgroup.card_map_of_injective hinj).symm
  · apply Subtype.ext
    apply hinj
    change MulAut.conj ((a : K) * b) = MulAut.conj ((b : K) * a)
    rw [map_mul, map_mul]
    exact Lemma1315b.comm_of_mem hE (Subgroup.mem_comap.1 a.2) (Subgroup.mem_comap.1 b.2)
  · apply hinj
    rw [map_pow, map_one]
    exact hE.2 _ hs

theorem elemAbelian_aut_card [Finite F] (hp5 : 5 ≤ p) (hF : Nat.card F = p ^ p) (hI : InputAutPSL2)
    {E : Subgroup (MulAut (L2S F))} (hE : IsElemAbelian p E) :
    Nat.card E ≤ p ^ p ∧ (Nat.card E = p ^ p → E ≤ innerAut (L2S F)) := by
  have hp2 : p ≠ 2 := by omega
  have hZ : Subgroup.center (L2S F) = ⊥ := center_eq_bot
  by_cases hEI : E ≤ innerAut (L2S F)
  · obtain ⟨hcard, hel⟩ := comap_conj_facts hZ hEI hE
    refine ⟨?_, fun _ => hEI⟩
    rw [← hcard]
    exact (pGroup_facts (n := p) hp.out.one_lt.le hF (Lemma1315b.isPGroup_of_elemAbelian hel)).2
  ·
    obtain ⟨x, hxE, hxI⟩ := Set.not_subset.1 hEI
    have hx1 : x ≠ 1 := fun h => hxI (h ▸ Subgroup.one_mem _)
    have hxp : x ^ p = 1 := hE.2 x hxE
    have hxo : orderOf x = p := orderOf_eq_prime hxp hx1
    set E₀ := E ⊓ innerAut (L2S F) with hE₀
    have hE₀el : IsElemAbelian p E₀ := Lemma1315b.elemAbelian_mono hE inf_le_left
    obtain ⟨hcard₀, hel₀⟩ := comap_conj_facts hZ (inf_le_right : E₀ ≤ innerAut (L2S F)) hE₀el
    have hfix₀ : ∀ s ∈ E₀.comap (MulAut.conj : L2S F →* MulAut (L2S F)), x s = s := by
      intro s hs
      apply conj_injective hZ
      rw [conj_apply_aut]
      have hc : x * MulAut.conj s = MulAut.conj s * x :=
        Lemma1315b.comm_of_mem hE hxE (Subgroup.mem_inf.1 (Subgroup.mem_comap.1 hs)).1
      rw [hc, mul_inv_cancel_right]
    have hS₀ : Nat.card (E₀.comap (MulAut.conj : L2S F →* MulAut (L2S F))) ≤ p :=
      fixed_card_le p hp5 hF hI hxo hxI (Lemma1315b.isPGroup_of_elemAbelian hel₀) hfix₀
    obtain ⟨g, j, hxs⟩ := isSemi_of_input p hI x
    have hj := not_dvd_of_semi p hp2 hF hxs hxp hxI
    have hj0 : (j : ZMod p) ≠ 0 := by rwa [Ne, ZMod.natCast_eq_zero_iff]
    have hcov : ∀ y ∈ E, ∃ e ∈ E₀, ∃ b ∈ Subgroup.zpowers x, y = e * b := by
      intro y hy
      obtain ⟨h, i, hys⟩ := isSemi_of_input p hI y
      set k := (-(i : ZMod p) * (j : ZMod p)⁻¹).val with hk
      have hdvd : p ∣ j * k + i := by
        rw [← ZMod.natCast_eq_zero_iff, Nat.cast_add, Nat.cast_mul, hk, ZMod.natCast_zmod_val,
          show (j : ZMod p) * (-(i : ZMod p) * (j : ZMod p)⁻¹) =
            -(i : ZMod p) * ((j : ZMod p) * (j : ZMod p)⁻¹) by ring, mul_inv_cancel₀ hj0, mul_one]
        exact neg_add_cancel _
      obtain ⟨G, hG⟩ := hxs.pow p k
      have hz := hys.mul p hG
      have hzE : y * x ^ k ∈ E := E.mul_mem hy (E.pow_mem hxE k)
      have hzI : y * x ^ k ∈ innerAut (L2S F) := by
        obtain ⟨m, hm⟩ := hdvd
        refine inner_of_semi_of_pow p hp2 hz ?_ (hE.2 _ hzE)
        intro t
        rw [hm]
        exact frobFix_of_card p hF m t
      exact ⟨y * x ^ k, ⟨hzE, hzI⟩, (x ^ k)⁻¹,
        Subgroup.inv_mem _ (Subgroup.pow_mem _ (Subgroup.mem_zpowers x) k), by group⟩
    have hle : Nat.card E ≤ Nat.card E₀ * Nat.card (Subgroup.zpowers x) := by
      let f : ↥E₀ × ↥(Subgroup.zpowers x) → ↥E := fun ab =>
        ⟨(ab.1 : MulAut (L2S F)) * ab.2, E.mul_mem ab.1.2.1 ((Subgroup.zpowers_le.2 hxE) ab.2.2)⟩
      have hf : Function.Surjective f := by
        rintro ⟨y, hy⟩
        obtain ⟨e, he, b, hb, rfl⟩ := hcov y hy
        exact ⟨(⟨e, he⟩, ⟨b, hb⟩), rfl⟩
      rw [← Nat.card_prod]
      exact Nat.card_le_card_of_surjective f hf
    rw [Nat.card_zpowers, hxo, ← hcard₀] at hle
    have hp2le : Nat.card E ≤ p ^ 2 := by
      calc Nat.card E ≤ Nat.card (E₀.comap (MulAut.conj : L2S F →* MulAut (L2S F))) * p := hle
        _ ≤ p * p := Nat.mul_le_mul_right p hS₀
        _ = p ^ 2 := (sq p).symm
    have hlt : p ^ 2 < p ^ p := Nat.pow_lt_pow_right hp.out.one_lt (by omega)
    exact ⟨hp2le.trans hlt.le, fun h => absurd (h ▸ hp2le) (not_le.2 hlt)⟩

end Aut

section AutProof

open CFSG.GorensteinWalter CFSG.ComponentClassification.CatalogueSchreierLinearTwo

variable {F : Type} [Field F]

theorem exists_frobenius_pow [Finite F] (p : ℕ) [Fact p.Prime] [CharP F p] (σ : F ≃+* F) :
    ∃ j : ℕ, ∀ x : F, σ x = x ^ p ^ j := by
  letI : Algebra (ZMod p) F := ZMod.algebra F p
  let σ' : F ≃ₐ[ZMod p] F := AlgEquiv.ofRingEquiv (f := σ) fun x =>
    DFunLike.congr_fun (RingHom.ext_zmod (σ.toRingHom.comp (algebraMap (ZMod p) F))
      (algebraMap (ZMod p) F)) x
  obtain ⟨n, hn⟩ := (FiniteField.bijective_frobeniusAlgEquivOfAlgebraic_pow (ZMod p) F).2 σ'
  refine ⟨n.1, fun x => ?_⟩
  have h := DFunLike.congr_fun hn x
  change ((FiniteField.frobeniusAlgEquivOfAlgebraic (ZMod p) F) ^ n.1) x = σ x at h
  rw [← h, AlgEquiv.coe_pow, FiniteField.coe_frobeniusAlgEquivOfAlgebraic_iterate, ZMod.card]

@[expose] noncomputable def ιP : L2S F →* Matrix.ProjGenLinGroup (Fin 2) F :=
  (Subgroup.subtype _).comp (StatedAPI.mapMkEquivStatedProj (StatedSL 2 F)).symm.toMonoidHom

theorem ιP_mk (A : StatedSL 2 F) :
    ιP (QuotientGroup.mk A : L2S F) = Matrix.ProjGenLinGroup.mk (A : GL (Fin 2) F) :=
  StatedAPI.coe_mapMkEquivStatedProj_symm_mk _ A

theorem ιP_injective : Function.Injective (ιP (F := F)) :=
  Subtype.val_injective.comp (MulEquiv.injective _)

theorem ιP_equiv (y : Matrix.ProjectiveSpecialLinearGroup (Fin 2) F) :
    ιP (CFSG.Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj 2 F y) =
      Matrix.ProjectiveSpecialLinearGroup.toPGL y := by
  induction y using QuotientGroup.induction_on with
  | H A =>
    rw [Matrix.ProjectiveSpecialLinearGroup.toPGL_mk]
    exact ιP_mk _

theorem inputAutPSL2_holds : InputAutPSL2 := by
  intro p hp F _ _ hchar α
  haveI : Fact p.Prime := ⟨hp⟩
  set e := CFSG.Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj 2 F with he
  set α' : MulAut (Matrix.ProjectiveSpecialLinearGroup (Fin 2) F) := MulAut.congr e.symm α with hα'
  obtain ⟨g, σ, hg⟩ := CFSG.RankThree.PartTwo.KFacts.exists_pglAction_mul_psl2FieldAut α'
  obtain ⟨gt, rfl⟩ := Matrix.ProjGenLinGroup.mk_surjective g
  obtain ⟨j, hj⟩ := exists_frobenius_pow p σ
  refine ⟨gt, j, fun A B hB => ?_⟩
  apply ιP_injective
  have h1 : α (QuotientGroup.mk A) = e (α' (e.symm (QuotientGroup.mk A))) := by
    simp [hα', MulAut.congr_apply]
  rw [h1, ιP_equiv, hg, MulAut.mul_apply, toPGL_pglAction, CFSG.GorensteinWalter.psl2FieldAut_toPGL,
    ← ιP_equiv, MulEquiv.apply_symm_apply, ιP_mk, ιP_mk, pgl2FieldAut_apply]
  change Matrix.ProjGenLinGroup.mk gt *
      pgl2RingEquiv σ (QuotientGroup.mk' (Subgroup.center _) (A : GL (Fin 2) F)) *
        (Matrix.ProjGenLinGroup.mk gt)⁻¹ = _
  rw [pgl2RingEquiv_mk]
  change Matrix.ProjGenLinGroup.mk gt * Matrix.ProjGenLinGroup.mk
      (Matrix.GeneralLinearGroup.map σ.toRingHom (A : GL (Fin 2) F)) *
        (Matrix.ProjGenLinGroup.mk gt)⁻¹ = _
  rw [← map_inv, ← map_mul, ← map_mul]
  congr 1
  apply Units.ext
  rw [hB, Units.val_mul, Units.val_mul]
  congr 2
  ext k l
  simp [Matrix.map_apply, hj]

end AutProof

section InputL2

open CFSG.HardMathSupport.Solomon.LocalBalance (innerAut)

theorem l2Facts_model {F : Type} [Field F] [Finite F] {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    (hF : Nat.card F = p ^ p) : Lemma1315b.L2Facts p (L2S F) := by
  haveI : Fact p.Prime := ⟨hp⟩
  haveI := charP_of_card hp hF
  have h1 : 1 ≤ p := hp.one_lt.le
  exact ⟨center_eq_bot, fun S hS => pGroup_facts h1 hF hS, exists_pGroup_card hF,
    fun E hE => elemAbelian_aut_card p hp5 hF inputAutPSL2_holds hE,
    fun x hx hxI S hS hfix => fixed_card_le p hp5 hF inputAutPSL2_holds hx hxI hS hfix,
    fun S hS hSp => torus_fact hp5 h1 hF hS hSp⟩

theorem elemAbelian_of_map_injective {G H : Type*} [Group G] [Group H] {f : G →* H}
    (hf : Function.Injective f) {p : ℕ} {S : Subgroup G} (h : IsElemAbelian p (S.map f)) :
    IsElemAbelian p S := by
  refine ⟨⟨⟨fun a b => ?_⟩⟩, fun s hs => ?_⟩
  · apply Subtype.ext
    apply hf
    rw [Subgroup.coe_mul, Subgroup.coe_mul, map_mul, map_mul]
    exact congrArg Subtype.val (h.1.is_comm.comm ⟨f a, a, a.2, rfl⟩ ⟨f b, b, b.2, rfl⟩)
  · apply hf
    rw [map_pow, map_one]
    exact h.2 _ ⟨s, hs, rfl⟩

theorem inner_of_congr {K K' : Type*} [Group K] [Group K'] (e : K ≃* K') {α : MulAut K}
    (h : MulAut.congr e α ∈ innerAut K') : α ∈ innerAut K := by
  obtain ⟨k', hk'⟩ := h
  refine ⟨e.symm k', ?_⟩
  ext y
  have h1 := DFunLike.congr_fun hk' (e y)
  simp only [MulAut.congr_apply, MulAut.conj_apply, MulEquiv.trans_apply,
    MulEquiv.symm_apply_apply] at h1
  rw [MulAut.conj_apply]
  apply e.injective
  rw [map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply, h1]

theorem l2Facts_of_mulEquiv {p : ℕ} {K K' : Type} [Group K] [Finite K] [Group K'] [Finite K']
    (e : K ≃* K') (h : Lemma1315b.L2Facts p K') : Lemma1315b.L2Facts p K := by
  obtain ⟨hZ, hP, ⟨S₀, hS₀p, hS₀c⟩, hE, hX, hT⟩ := h
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · have h1 := Subgroup.map_center_eq e
    rw [hZ] at h1
    exact (Subgroup.map_eq_bot_iff_of_injective _ e.injective).1 h1
  · intro S hS
    obtain ⟨hel, hc⟩ := hP (S.map e.toMonoidHom) (hS.map _)
    refine ⟨elemAbelian_of_map_injective e.injective hel, ?_⟩
    rwa [Subgroup.card_map_of_injective e.injective] at hc
  · refine ⟨S₀.map e.symm.toMonoidHom, hS₀p.map _, ?_⟩
    rw [Subgroup.card_map_of_injective e.symm.injective, hS₀c]
  · intro E hE'
    obtain ⟨hc, hinn⟩ := hE (E.map (MulAut.congr e).toMonoidHom)
      (CFSG.SectionRank.isElemAbelian_map hE' _)
    rw [Subgroup.card_map_of_injective (MulAut.congr e).injective] at hc hinn
    exact ⟨hc, fun h α hα => inner_of_congr e (hinn h ⟨α, hα, rfl⟩)⟩
  · intro x hx hxI S hS hfix
    have h := hX (MulAut.congr e x) (by rw [MulEquiv.orderOf_eq]; exact hx)
      (fun h => hxI (inner_of_congr e h)) (S.map e.toMonoidHom) (hS.map _) (by
        rintro _ ⟨s, hs, rfl⟩
        simp [MulAut.congr_apply, hfix s hs])
    rwa [Subgroup.card_map_of_injective e.injective] at h
  · intro S hS hSp
    obtain ⟨n', hn', s', hs', hne⟩ := hT (S.map e.toMonoidHom) (hS.map _)
      (by rw [Subgroup.card_map_of_injective e.injective, hSp])
    refine ⟨e.symm n', ?_, e.symm s', ?_, ?_⟩
    · rw [Subgroup.mem_normalizer_iff]
      intro y
      have key := (Subgroup.mem_normalizer_iff.1 hn') (e y)
      have h1 : n' * e y * n'⁻¹ = e (e.symm n' * y * (e.symm n')⁻¹) := by simp
      rw [h1] at key
      simpa only [Subgroup.mem_map_equiv, MulEquiv.symm_apply_apply] using key
    · obtain ⟨s, hs, rfl⟩ := hs'
      simpa using hs
    · intro h
      apply hne
      have h1 := congrArg e h
      simpa using h1

theorem inputL2_holds : Lemma1315b.InputL2 := by
  intro p hp hp5 K _ _ hK
  obtain ⟨F, _, _, hF, ⟨e⟩⟩ := hK
  exact l2Facts_of_mulEquiv e (l2Facts_model hp hp5 hF)

end InputL2

theorem input23_19_prop1310a5_of (h : Lemma1315b.Input23_19) : Prop1310a5.Input23_19 := by
  intro X _ _ hX p hp hp2 B hB hB4 hBr K hK htype
  refine h X hX p hp hp2 B hB hB4 hBr K hK ?_
  rcases htype with hA | ⟨q, hqp, idx, ⟨e⟩, hq⟩ | hc
  · exact Or.inl hA
  · refine Or.inr (Or.inl ⟨q, hq ▸ idx.1.characteristic_prime, hqp, ?_⟩)
    rw [← hq]
    exact Lemma1315b.isChevSimple_of_lie e
  · exact Or.inr (Or.inr hc)

theorem input3_3_of_chevTwoOdd (h : Prop1116Design.InputChevTwoOdd) : Lemma1315b.Input3_3 := by
  intro p hp hp5 K _ _ hK hcore h2 hpchev
  have hcases := h (K ⧸ Subgroup.center K) p hp (by omega) (by omega) hpchev h2
  have hZ : Subgroup.center K = ⊥ := by
    apply SchurFacts.center_eq_bot_of_not_sq_dvd hp hK.1 hcore
    apply SchurFacts.not_sq_dvd_sixty_or_168 hp (by omega)
    rcases hcases with ⟨⟨f⟩, -⟩ | ⟨h7, -⟩
    · exact Or.inl ((Nat.card_congr f.toEquiv).trans Prop1116Design.card_alt_five)
    · exact Or.inr (Prop1116Design.card_statedProj_two_seven h7)
  have eZ : K ≃* K ⧸ Subgroup.center K :=
    ((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot).symm
  rcases hcases with ⟨⟨f⟩, rfl⟩ | ⟨h7, rfl⟩
  · haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
    obtain ⟨g⟩ := CFSG.ClassicalInvolution.A7M.nonempty_mulEquiv_alternatingGroup_five_psl
    exact ⟨Or.inl rfl, ZMod 5, inferInstance, inferInstance, Nat.card_zmod 5,
      ⟨eZ.trans (f.trans (g.trans
        (CFSG.Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj 2 (ZMod 5))))⟩⟩
  · exact ⟨Or.inr rfl, Lemma129b.isLpType_of_center_bot hZ h7⟩

section ChevDown

open CFSG.Yardstones.Md0ec50421ce4 (IsChevSimple PSimple PQuot CentMod InducesInnerMod)
open CFSG.HardMathSupport.Solomon.LocalBalance (innerAut barOf)

theorem glaPComponent_self_of_quasisimple {Y : Type*} [Group Y] {p : ℕ} {S : Subgroup Y}
    (hq : CFSG.Open.IsQuasisimple ↥S) (hO : GLAPPrimeCore p ↥S = ⊥) : GLAPComponent p S S := by
  have hker : (QuotientGroup.mk' (GLAPPrimeCore p ↥S)).ker = ⊥ := by
    rw [QuotientGroup.ker_mk', hO]
  have hinj : Function.Injective (QuotientGroup.mk' (GLAPPrimeCore p ↥S)) :=
    (MonoidHom.ker_eq_bot_iff _).1 hker
  have hL : (S.subgroupOf S).map (QuotientGroup.mk' (GLAPPrimeCore p ↥S)) = ⊤ := by
    rw [Subgroup.subgroupOf_self, Subgroup.map_top, MonoidHom.range_eq_top]
    exact QuotientGroup.mk'_surjective _
  refine ⟨le_rfl, IsSubnormal.refl S, ⟨le_top, ?_, ?_⟩, ?_⟩
  · rw [hL]; exact IsSubnormal.refl _
  · rw [hL]
    let e : ↥S ≃* ↥(⊤ : Subgroup (↥S ⧸ GLAPPrimeCore p ↥S)) :=
      (MulEquiv.ofBijective (QuotientGroup.mk' (GLAPPrimeCore p ↥S))
        ⟨hinj, QuotientGroup.mk'_surjective _⟩).trans Subgroup.topEquiv.symm
    exact CFSG.SignalizerFunctorTheorem.TransportA.isQuasisimple_of_mulEquiv e hq
  · intro J hJ _ h
    have h1 : J.subgroupOf S = S.subgroupOf S := Subgroup.map_injective hinj h
    rw [Subgroup.subgroupOf_self] at h1
    exact absurd (Subgroup.subgroupOf_eq_top.mp h1) (not_le_of_gt hJ)

abbrev Hol (K : Type) [Group K] : Type := K ⋊[MonoidHom.id (MulAut K)] MulAut K

theorem hol_finite (K : Type) [Group K] [Finite K] : Finite (Hol K) :=
  Finite.of_injective (fun z : Hol K => (z.left, z.right)) fun a b h =>
    SemidirectProduct.ext (congrArg Prod.fst h) (congrArg Prod.snd h)

variable {K : Type} [Group K] [Finite K]

abbrev Kin (K : Type) [Group K] : Subgroup (Hol K) := (SemidirectProduct.inl : K →* Hol K).range

theorem inl_conj (x : MulAut K) (k : K) :
    (SemidirectProduct.inr x : Hol K) * SemidirectProduct.inl k * (SemidirectProduct.inr x)⁻¹ =
      SemidirectProduct.inl (x k) := by
  rw [← map_inv]
  exact (SemidirectProduct.inl_aut x k).symm

theorem kin_inf_centralizer (x : MulAut K) :
    Kin K ⊓ Subgroup.centralizer ({(SemidirectProduct.inr x : Hol K)} : Set (Hol K)) =
      (Lemma1314.fixSub x).map (SemidirectProduct.inl : K →* Hol K) := by
  ext g
  constructor
  · rintro ⟨⟨k, rfl⟩, hc⟩
    refine ⟨k, ?_, rfl⟩
    change x k = k
    have hc' := Subgroup.mem_centralizer_singleton_iff.1 hc
    apply SemidirectProduct.inl_injective (φ := MonoidHom.id (MulAut K))
    rw [← inl_conj, ← hc', mul_inv_cancel_right]
  · rintro ⟨k, hk, rfl⟩
    refine ⟨⟨k, rfl⟩, Subgroup.mem_centralizer_singleton_iff.2 ?_⟩
    have hk' : x k = k := hk
    have h1 := inl_conj x k
    rw [hk', mul_inv_eq_iff_eq_mul] at h1
    exact h1.symm

@[expose] noncomputable def kinEquiv (K : Type) [Group K] : K ≃* ↥(Kin K) :=
  MonoidHom.ofInjective (SemidirectProduct.inl_injective (φ := MonoidHom.id (MulAut K)))

theorem kin_core_eq_bot {p : ℕ} (hO : GLAPPrimeCore p K = ⊥) : GLAPPrimeCore p ↥(Kin K) = ⊥ := by
  have h := glaPPrimeCore_map_iso p (kinEquiv K)
  rw [hO, Subgroup.map_bot] at h
  exact h.symm

theorem kin_coreOf_eq_bot {p : ℕ} (hO : GLAPPrimeCore p K = ⊥) : GLAPPrimeCoreOf p (Kin K) = ⊥ := by
  rw [GLAPPrimeCoreOf, kin_core_eq_bot hO, Subgroup.map_bot]

theorem kin_component {p : ℕ} (hK : CFSG.Open.IsQuasisimple K) (hO : GLAPPrimeCore p K = ⊥) :
    GLAPComponent p (Kin K) (Kin K) :=
  glaPComponent_self_of_quasisimple
    (CFSG.SignalizerFunctorTheorem.TransportA.isQuasisimple_of_mulEquiv (kinEquiv K) hK)
    (kin_core_eq_bot hO)

theorem pSimple_kin_equiv {p : ℕ} (hO : GLAPPrimeCore p K = ⊥) :
    Nonempty (PSimple p (Kin K) ≃* K ⧸ Subgroup.center K) := by
  have e1 : PQuot p (Kin K) ≃* K :=
    ((QuotientGroup.quotientMulEquivOfEq (kin_core_eq_bot hO)).trans
      QuotientGroup.quotientBot).trans (kinEquiv K).symm
  exact ⟨Lemma1315b.centerQuotEquiv e1⟩

theorem input14_4_1_of_kd
    (hD : ∀ p q : ℕ, p.Prime → 5 ≤ p → CFSG.LocalAnalysis.GLTheoremA.KDChevDownQ p q)
    (hI : ∀ p : ℕ, p.Prime → 5 ≤ p → CFSG.LocalAnalysis.GLTheoremA.KDChevInner p) :
    Lemma1315b.Input14_4_1 := by
  intro p q hp hp5 hq K _ _ hK hO hchev J _ x ⟨hx, J1, hJ1, ⟨eJ⟩⟩
  haveI := hol_finite K
  set a : Hol K := SemidirectProduct.inr x with ha
  have hKc : GLAPComponent p (Kin K) (Kin K) := kin_component hK.1 hO
  obtain ⟨eS⟩ := pSimple_kin_equiv (K := K) hO
  have hchev' : IsChevSimple q (PSimple p (Kin K)) := Lemma1315b.isChevSimple_of_equiv eS hchev
  have hnorm : a ∈ Subgroup.normalizer ((Kin K : Subgroup (Hol K)) : Set (Hol K)) := by
    have hN : (Kin K).Normal := by
      rw [Kin, SemidirectProduct.range_inl_eq_ker_rightHom]
      exact MonoidHom.normal_ker _
    haveI := hN
    rw [Subgroup.normalizer_eq_top (Kin K)]
    exact Subgroup.mem_top _
  have hap : a ^ p = 1 := by
    rw [ha, ← map_pow, ← hx, pow_orderOf_eq_one, map_one]
  have hL : GLAPComponent p (Kin K ⊓ Subgroup.centralizer ({a} : Set (Hol K)))
      (J1.map (SemidirectProduct.inl : K →* Hol K)) := by
    rw [ha, kin_inf_centralizer]
    refine glaPComponent_map hp _ ?_ hJ1
    rw [(MonoidHom.ker_eq_bot_iff _).2 (SemidirectProduct.inl_injective (φ := MonoidHom.id (MulAut K))),
      inf_bot_eq, Subgroup.card_bot]
    exact Nat.coprime_one_right p
  refine ⟨?_, ?_⟩
  · have h1 := CFSG.LocalAnalysis.GLTheoremA.chevQ_step hp (hD p q hp hp5) hKc hchev' hnorm hap hL
    have e1 : ↥(J1.map (SemidirectProduct.inl : K →* Hol K)) ≃* ↥J1 :=
      (Subgroup.equivMapOfInjective J1 _
        (SemidirectProduct.inl_injective (φ := MonoidHom.id (MulAut K)))).symm
    exact Lemma1315b.isChevSimple_of_equiv
      (Lemma1315b.centerQuotEquiv ((Lemma1315b.barCongr p e1).trans eJ)).symm h1
  · rintro rfl ⟨k, hk⟩
    apply CFSG.LocalAnalysis.GLTheoremA.chev_one_element_inner hp (hI _ hp hp5) hKc hchev' hnorm hap
      ?_ ?_ _ hL
    ·
      rintro ⟨-, hcm⟩
      rw [kin_coreOf_eq_bot hO, Subgroup.commutator_le] at hcm
      apply hp.one_lt.ne'
      rw [← hx, orderOf_eq_one_iff]
      ext m
      have h1 := hcm _ ⟨m, rfl⟩ a (Subgroup.mem_zpowers a)
      rw [Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at h1
      apply SemidirectProduct.inl_injective (φ := MonoidHom.id (MulAut K))
      rw [MulAut.one_apply, ← inl_conj, ← h1, mul_inv_cancel_right]
    ·
      refine ⟨SemidirectProduct.inl k, ⟨k, rfl⟩, ?_⟩
      rintro _ ⟨m, rfl⟩
      have h1 : a⁻¹ * SemidirectProduct.inl m * a = SemidirectProduct.inl (k⁻¹ * m * k) := by
        have h2 := inl_conj x⁻¹ m
        rw [map_inv, inv_inv] at h2
        rw [ha, h2, ← hk, MulAut.conj_inv_apply]
      rw [h1, ← map_inv, ← map_mul, ← map_mul, inv_mul_cancel]
      exact Subgroup.one_mem _

end ChevDown

section Chev2Arith

theorem eq_psl_two_of_sylow_le {t : StatedLieTag} {n p f : ℕ} (hadm : StatedLieAdmissible t n p f)
    (h : CFSG.ComponentClassification.CatLeaf.lieSylowExponent t n * f ≤ 1) :
    t = .PSL ∧ n = 2 ∧ f = 1 := by
  obtain ⟨-, hf, ht⟩ := hadm
  have key : ∀ A : ℕ, 2 ≤ A → A * f ≤ 1 → False := fun A hA hAf => by nlinarith
  cases t <;> simp only [CFSG.ComponentClassification.CatLeaf.lieSylowExponent] at h
  case PSL =>
    have hn : 2 ≤ n := ht.1
    have h1 : 1 ≤ n * (n - 1) / 2 :=
      (Nat.le_div_iff_mul_le (by norm_num)).2 (by
        have := Nat.mul_le_mul hn (show 1 ≤ n - 1 by omega)
        omega)
    have hf1 : f = 1 := by nlinarith
    subst hf1
    refine ⟨rfl, ?_, rfl⟩
    by_contra hne
    have h3 : 3 ≤ n * (n - 1) / 2 :=
      (Nat.le_div_iff_mul_le (by norm_num)).2 (by
        have := Nat.mul_le_mul (show 3 ≤ n by omega) (show 2 ≤ n - 1 by omega)
        omega)
    omega
  case PSU =>
    have hn : 3 ≤ n := ht.1
    exact (key _ ((Nat.le_div_iff_mul_le (by norm_num)).2 (by
      have := Nat.mul_le_mul hn (show 2 ≤ n - 1 by omega)
      omega)) h).elim
  case PSp =>
    exact (key (n ^ 2) (by nlinarith [ht.1]) h).elim
  case POmegaOdd =>
    exact (key (n ^ 2) (by nlinarith [ht.1]) h).elim
  case POmegaPlus =>
    exact (key (n * (n - 1)) (by
      have := Nat.mul_le_mul ht (show 1 ≤ n - 1 by omega)
      omega) h).elim
  case POmegaMinus =>
    exact (key (n * (n - 1)) (by
      have := Nat.mul_le_mul ht (show 1 ≤ n - 1 by omega)
      omega) h).elim
  all_goals omega

theorem factorization_le_one {q N : ℕ} (hq : q.Prime) (hq2 : q ≠ 2) (hq3 : q ≠ 3)
    (hN : N = 60 ∨ N = 168 ∨ N = 360 ∨ N = 6048 ∨ N = 25920) : N.factorization q ≤ 1 := by
  obtain ⟨a, b, r, hr, rfl⟩ : ∃ a b r : ℕ, (r = 5 ∨ r = 7) ∧ N = 2 ^ a * 3 ^ b * r := by
    rcases hN with rfl | rfl | rfl | rfl | rfl
    · exact ⟨2, 1, 5, Or.inl rfl, by norm_num⟩
    · exact ⟨3, 1, 7, Or.inr rfl, by norm_num⟩
    · exact ⟨3, 2, 5, Or.inl rfl, by norm_num⟩
    · exact ⟨5, 3, 7, Or.inr rfl, by norm_num⟩
    · exact ⟨6, 4, 5, Or.inl rfl, by norm_num⟩
  have hr' : r.Prime := by rcases hr with rfl | rfl <;> norm_num
  rw [Nat.factorization_mul (by positivity) hr'.ne_zero,
    Nat.factorization_mul (by positivity) (by positivity), Nat.factorization_pow,
    Nat.factorization_pow, Nat.prime_two.factorization, Nat.prime_three.factorization,
    hr'.factorization]
  simp only [Finsupp.add_apply, Finsupp.smul_apply, Finsupp.single_apply, smul_eq_mul]
  split_ifs <;> omega

end Chev2Arith

section CertInner


theorem kdChevInner_five_le {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) :
    CFSG.LocalAnalysis.GLTheoremA.KDChevInner p :=
  CFSG.LocalAnalysis.GLTheoremA.kdChevInner_of hp (by omega)
    (CFSG.HardMathSupport.Dickson.KD.kdCharP_holds hp (by omega))
    (CFSG.LocalAnalysis.GLTheoremA.kdAmbSolv_holds hp (by omega)
      CFSG.LocalAnalysis.GLTheoremA.u42_fixSubgroup_solvable)

end CertInner

section CertChevTwo


theorem inputChevTwoOdd_holds : Prop1116Design.InputChevTwoOdd := by
  intro S _ q hq hq2 hq3 hchq hch2
  rcases hchq with ⟨i, hi, ⟨e⟩⟩ | ⟨i, hi, ⟨e⟩⟩
  · cases i with
    | cyclic r hr => exact hi.elim
    | alternating n hn => exact hi.elim
    | sporadic s => exact hi.elim
    | lie d =>
      have hdq : d.1.characteristic = q := hi
      obtain ⟨t, n, f, hX⟩ := CFSG.HardMathSupport.Dickson.Sec6.exists_blueprint_lieModel_of_odd d
        (by rw [hdq]; exact hq2) e
      rw [hdq] at hX
      have hadm := CFSG.Blueprint.LieModel.admissible hX
      have hodd : CFSG.Blueprint.OddLieType S := ⟨t, n, q, f, hq, hq2, hadm, hX⟩
      obtain ⟨hfin, -, hsyl⟩ :=
        CFSG.ComponentClassification.CatLeafProof.lieOrderFormulasInput S t n q f hadm hX
      have hset : Nat.card S = 60 ∨ Nat.card S = 168 ∨ Nat.card S = 360 ∨ Nat.card S = 6048 ∨
          Nat.card S = 25920 := by
        rcases CFSG.LocalAnalysis.GLTheoremA.i112d_lie_or_card hch2 with ⟨t', n', f', hX'⟩ | h | h
        · have hadm' := CFSG.Blueprint.LieModel.admissible hX'
          have hcard := (CFSG.ComponentClassification.CatLeafProof.lieOrderFormulasInput
            S t' n' 2 f' hadm' hX').2.1
          rcases CFSG.SeitzReduction.CrossChar.eq_of_lieModel_two_of_oddLieType
              CFSG.ComponentClassification.CatLeafProof.lieOrderFormulasInput hX' hodd with
            ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
          · rw [show CFSG.ComponentClassification.CatLeaf.lieOrderNumerator .PSL 2 (2 ^ 2) = 60 from by
                decide,
              show CFSG.ComponentClassification.CatLeaf.lieOrderDivisor .PSL 2 (2 ^ 2) = 1 from rfl]
              at hcard
            omega
          · rw [show CFSG.ComponentClassification.CatLeaf.lieOrderNumerator .PSL 3 (2 ^ 1) = 168 from by
                decide,
              show CFSG.ComponentClassification.CatLeaf.lieOrderDivisor .PSL 3 (2 ^ 1) = 1 from rfl]
              at hcard
            omega
          · rw [show CFSG.ComponentClassification.CatLeaf.lieOrderNumerator .PSU 4 (2 ^ 1) = 25920 from by
                decide,
              show CFSG.ComponentClassification.CatLeaf.lieOrderDivisor .PSU 4 (2 ^ 1) = 1 from rfl]
              at hcard
            omega
        · exact Or.inr (Or.inr (Or.inl h))
        · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
      have hle : CFSG.ComponentClassification.CatLeaf.lieSylowExponent t n * f ≤ 1 :=
        hsyl ▸ factorization_le_one hq hq2 hq3 hset
      obtain ⟨rfl, rfl, rfl⟩ := eq_psl_two_of_sylow_le hadm hle
      rcases hX with ⟨-, -, K, _, _, hK, ⟨eK⟩⟩ | ⟨h0, -⟩ | ⟨h0, -⟩ | ⟨h0, -⟩
      · rw [pow_one] at hK
        have hKodd : Odd (Nat.card K) := hK ▸ hq.odd_of_ne_two hq2
        have hc := CFSG.Open.StatedAPI.card_statedProj_statedSL_two_of_odd hKodd
        rw [← Nat.card_congr eK.toEquiv, hK] at hc
        have hq5 : 5 ≤ q := by
          have := hq.two_le
          rcases (by omega : q = 2 ∨ q = 3 ∨ q = 4 ∨ 5 ≤ q) with h | h | h | h
          · exact absurd h hq2
          · exact absurd h hq3
          · exact absurd (h ▸ hq) (by norm_num)
          · exact h
        have hq37 : q ≤ 37 := by
          by_contra hgt
          have h1 : 38 * (38 ^ 2 - 1) ≤ q * (q ^ 2 - 1) :=
            Nat.mul_le_mul (by omega) (Nat.sub_le_sub_right (Nat.pow_le_pow_left (by omega) 2) 1)
          have h2 : 38 * (38 ^ 2 - 1) / 2 ≤ q * (q ^ 2 - 1) / 2 := Nat.div_le_div_right h1
          rw [← hc] at h2
          rcases hset with h | h | h | h | h <;> rw [h] at h2 <;> norm_num at h2
        have hq57 : q = 5 ∨ q = 7 := by
          interval_cases q <;> first
            | (left; rfl)
            | (right; rfl)
            | (exfalso; norm_num at hq; done)
            | (exfalso; rw [hc] at hset; norm_num at hset; done)
        rcases hq57 with rfl | rfl
        · obtain ⟨eA⟩ := CFSG.ClassicalModels.nonempty_statedLinearModel_equiv_alternating_five K
            (Or.inr hK)
          exact Or.inl ⟨⟨eK.trans eA⟩, rfl⟩
        · exact Or.inr ⟨⟨K, inferInstance, inferInstance, hK, ⟨eK⟩⟩, rfl⟩
      all_goals exact absurd h0 (by norm_num)
  · cases i with
    | cyclic r hr => exact hi.elim
    | sporadic s => exact hi.elim
    | alternating n hn =>
      simp only [CFSG.Yardstones.Md0ec50421ce4.ambiguousChev] at hi
      rcases hi with ⟨rfl, h | rfl⟩ | ⟨-, h | h⟩ | ⟨-, h⟩
      · exact absurd h hq2
      · exact Or.inl ⟨⟨e⟩, rfl⟩
      · exact absurd h hq2
      · exact absurd h hq3
      · exact absurd h hq2
    | lie d =>
      exfalso
      obtain ⟨d, hv⟩ := d
      unfold CFSG.Yardstones.Md0ec50421ce4.ambiguousChev at hi
      split at hi <;> try simp_all
      all_goals (split at hi <;> simp_all)

theorem input3_3_holds : Lemma1315b.Input3_3 :=
  input3_3_of_chevTwoOdd inputChevTwoOdd_holds

end CertChevTwo

section CertDown


theorem kdChevDownQ_five_le {p q : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) :
    CFSG.LocalAnalysis.GLTheoremA.KDChevDownQ p q :=
  CFSG.LocalAnalysis.GLTheoremA.kdChevDownQ_of_lieComps hp
    (CFSG.LocalAnalysis.GLTheoremA.lieCompsOn_holds hp hp5) (fun _ => kdChevInner_five_le hp hp5)
    (CFSG.LocalAnalysis.GLTheoremA.kdAmbDownQ_holds hp (by omega) (kdChevInner_five_le hp hp5)
      (CFSG.LocalAnalysis.GLTheoremA.kdAmbSolv_holds hp (by omega)
        CFSG.LocalAnalysis.GLTheoremA.u42_fixSubgroup_solvable))

theorem input14_4_1_holds : Lemma1315b.Input14_4_1 :=
  input14_4_1_of_kd (fun _ _ hp hp5 => kdChevDownQ_five_le hp hp5)
    (fun _ hp hp5 => kdChevInner_five_le hp hp5)

theorem lemma1315_of_remaining_inputs (h1314 : Lemma1314Statement)
    (hI2319 : Lemma1315b.Input23_19) (hI255 : Lemma1315b.Input25_5)
    (hI1418 : Lemma1315b.Input14_18) (hI1415 : Lemma1314.Input14_15)
    (hFi23 : Lemma1314.Input23_24Fi23) (hI112 : CFSG.HardMathSupport.Solomon.LocalBalance.Input11_2)
    (hI183 : Prop115.Input18_3Gen) (hDiag : Lemma1315b.Input18_3DiagZ) : Lemma1315Statement :=
  lemma1315_of_inputs h1314 hI2319 hI255 input3_3_holds input14_4_1_holds hI1418 hI1415 hFi23 hI112
    hI183 hDiag inputL2_holds

theorem lemma1315_extras_of_remaining_inputs (h1314 : Lemma1314Statement)
    (hI2319 : Lemma1315b.Input23_19) (hI255 : Lemma1315b.Input25_5)
    (hI1418 : Lemma1315b.Input14_18) (hI1415 : Lemma1314.Input14_15)
    (hFi23 : Lemma1314.Input23_24Fi23) (hI112 : CFSG.HardMathSupport.Solomon.LocalBalance.Input11_2)
    (hI183 : Prop115.Input18_3Gen) (hDiag : Lemma1315b.Input18_3DiagZ) :
    Lemma1315b.ExtrasStatement :=
  lemma1315_extras_of_inputs h1314 hI2319 hI255 input3_3_holds input14_4_1_holds hI1418 hI1415 hFi23
    hI112 hI183 hDiag inputL2_holds

end CertDown

end CFSG.LocalAnalysis.GLTheoremB.MovingAround.Inputs1315
