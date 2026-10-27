module

public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Claims1110b

public section

namespace CFSG.LocalAnalysis.GLTheoremB.MovingAround.Claims1110c

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.LocalAnalysis.GLTheoremB.MovingAround
open CFSG.LocalAnalysis.GLTheoremB.MovingAround.Claims1110
open CFSG.LocalAnalysis.GLTheoremB.MovingAround.Claims1110b
open CFSG.HardMathSupport.Solomon.Coordinator (IsEkIn)
open CFSG.HardMathSupport.Solomon.LocalBalance (barOf barAut Fi22Facts IsFiTwentyTwo)
open CFSG.HardMathSupport.Solomon.LocalBalance.Lemma512Ns (conj_mem_gLAPPrimeCoreOf gLAPPrimeCoreOf_le)

section IeStar

variable {G : Type} [Group G] [Finite G]

@[expose] def IeStarOf (K : Subgroup G) (e : G) : Subgroup G :=
  ⨆ g ∈ Cg e, GLBConj g (IeOf K e)

theorem ieOf_le_ieStarOf (K : Subgroup G) (e : G) : IeOf K e ≤ IeStarOf K e := by
  intro x hx
  have h1 : x ∈ GLBConj 1 (IeOf K e) := by
    rw [mem_gLBConj]
    simpa using hx
  exact (le_iSup₂ (f := fun g (_ : g ∈ Cg e) => GLBConj g (IeOf K e)) 1 (Subgroup.one_mem _)) h1

theorem ieStarOf_le_cg (K : Subgroup G) (e : G) : IeStarOf K e ≤ Cg e := by
  refine iSup₂_le fun g hg => ?_
  intro x hx
  rw [mem_gLBConj] at hx
  have hxC : g * x * g⁻¹ ∈ Cg e := ieOf_le_cg K e hx
  have := (Cg e).mul_mem ((Cg e).mul_mem ((Cg e).inv_mem hg) hxC) hg
  simpa [mul_assoc] using this

theorem cg_le_normalizer_ieStarOf (K : Subgroup G) (e : G) :
    Cg e ≤ Subgroup.normalizer ((IeStarOf K e : Subgroup G) : Set G) := by
  have hle : ∀ h ∈ Cg e, ∀ x ∈ IeStarOf K e, h * x * h⁻¹ ∈ IeStarOf K e := by
    intro h hh x hx
    have h1 : IeStarOf K e ≤ (IeStarOf K e).comap (MulAut.conj h).toMonoidHom := by
      refine iSup₂_le fun g hg => ?_
      intro y hy
      rw [mem_gLBConj] at hy
      show h * y * h⁻¹ ∈ IeStarOf K e
      have h2 : h * y * h⁻¹ ∈ GLBConj (g * h⁻¹) (IeOf K e) := by
        rw [mem_gLBConj]
        have e' : g * h⁻¹ * (h * y * h⁻¹) * (g * h⁻¹)⁻¹ = g * y * g⁻¹ := by group
        rw [e']
        exact hy
      exact (le_iSup₂ (f := fun g (_ : g ∈ Cg e) => GLBConj g (IeOf K e)) (g * h⁻¹)
        ((Cg e).mul_mem hg ((Cg e).inv_mem hh))) h2
    exact h1 hx
  intro h hh
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · exact hle h hh x
  · intro hx
    have := hle h⁻¹ ((Cg e).inv_mem hh) _ hx
    simpa [mul_assoc] using this

@[expose] def CRIeStar (R K : Subgroup G) (e : G) : Subgroup G where
  carrier := {x | x ∈ R ∧ x ∈ Cg e ∧ ∀ y ∈ IeStarOf K e, x * y * x⁻¹ * y⁻¹ ∈ GLAPPrimeCoreOf 5 (Cg e)}
  mul_mem' := by
    rintro x x' ⟨hxR, hxC, hx⟩ ⟨hx'R, hx'C, hx'⟩
    refine ⟨R.mul_mem hxR hx'R, (Cg e).mul_mem hxC hx'C, fun y hy => ?_⟩
    have h1 := conj_mem_gLAPPrimeCoreOf 5 (Cg e) hxC (hx' y hy)
    have hm := (GLAPPrimeCoreOf 5 (Cg e)).mul_mem h1 (hx y hy)
    have e' : x * x' * y * (x * x')⁻¹ * y⁻¹ =
        x * (x' * y * x'⁻¹ * y⁻¹) * x⁻¹ * (x * y * x⁻¹ * y⁻¹) := by group
    rw [e']
    exact hm
  one_mem' := ⟨R.one_mem, (Cg e).one_mem, fun y _ => by simp⟩
  inv_mem' := by
    rintro x ⟨hxR, hxC, hx⟩
    refine ⟨R.inv_mem hxR, (Cg e).inv_mem hxC, fun y hy => ?_⟩
    have h1 := conj_mem_gLAPPrimeCoreOf 5 (Cg e) ((Cg e).inv_mem hxC)
      ((GLAPPrimeCoreOf 5 (Cg e)).inv_mem (hx y hy))
    have e' : x⁻¹ * y * x⁻¹⁻¹ * y⁻¹ = x⁻¹ * (x * y * x⁻¹ * y⁻¹)⁻¹ * x⁻¹⁻¹ := by group
    rw [e']
    exact h1

theorem mem_cRIeStar {R K : Subgroup G} {e x : G} :
    x ∈ CRIeStar R K e ↔ x ∈ R ∧ x ∈ Cg e ∧
      ∀ y ∈ IeStarOf K e, x * y * x⁻¹ * y⁻¹ ∈ GLAPPrimeCoreOf 5 (Cg e) := Iff.rfl

theorem cRIeStar_le (R K : Subgroup G) (e : G) : CRIeStar R K e ≤ R := fun _ hx => hx.1

theorem inf_ieStarOf_normal {R K : Subgroup G} {e : G} (hRC : R ≤ Cg e) :
    ((R ⊓ IeStarOf K e).subgroupOf R).Normal := by
  rw [Subgroup.normal_subgroupOf_iff_le_normalizer inf_le_left]
  intro r hr
  have hrN := cg_le_normalizer_ieStarOf K e (hRC hr)
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · intro hx
    exact Subgroup.mem_inf.2 ⟨R.mul_mem (R.mul_mem hr (Subgroup.mem_inf.1 hx).1) (R.inv_mem hr),
      (Subgroup.mem_normalizer_iff.1 hrN x).1 (Subgroup.mem_inf.1 hx).2⟩
  · intro hx
    refine Subgroup.mem_inf.2 ⟨?_, (Subgroup.mem_normalizer_iff.1 hrN x).2 (Subgroup.mem_inf.1 hx).2⟩
    have := R.mul_mem (R.mul_mem (R.inv_mem hr) (Subgroup.mem_inf.1 hx).1) hr
    simpa [mul_assoc] using this

theorem cRIeStar_normal {R K : Subgroup G} {e : G} (hRC : R ≤ Cg e) :
    ((CRIeStar R K e).subgroupOf R).Normal := by
  have key : ∀ r ∈ R, ∀ x ∈ CRIeStar R K e, r * x * r⁻¹ ∈ CRIeStar R K e := by
    intro r hr x hx
    obtain ⟨hxR, hxC, hxI⟩ := (mem_cRIeStar).1 hx
    have hrC : r ∈ Cg e := hRC hr
    refine (mem_cRIeStar).2 ⟨R.mul_mem (R.mul_mem hr hxR) (R.inv_mem hr),
      (Cg e).mul_mem ((Cg e).mul_mem hrC hxC) ((Cg e).inv_mem hrC), fun z hz => ?_⟩
    have hz' : r⁻¹ * z * r ∈ IeStarOf K e := by
      have := (Subgroup.mem_normalizer_iff.1
        (Subgroup.inv_mem _ (cg_le_normalizer_ieStarOf K e hrC)) z).1 hz
      simpa using this
    have h1 := conj_mem_gLAPPrimeCoreOf 5 (Cg e) hrC (hxI _ hz')
    have e' : r * x * r⁻¹ * z * (r * x * r⁻¹)⁻¹ * z⁻¹ =
        r * (x * (r⁻¹ * z * r) * x⁻¹ * (r⁻¹ * z * r)⁻¹) * r⁻¹ := by group
    rw [e']
    exact h1
  rw [Subgroup.normal_subgroupOf_iff_le_normalizer (cRIeStar_le R K e)]
  intro r hr
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · exact key r hr x
  · intro hx
    have := key r⁻¹ (R.inv_mem hr) _ hx
    simpa [mul_assoc] using this

end IeStar

section Cover

variable {G : Type} [Group G] [Finite G]

theorem exists_conj_B_le {m : ℕ} {B M E A : Subgroup G} {a : G} {K : Subgroup G}
    (h : Cex117 G m 5 B M E A a K) {R : Subgroup G} (hR : IsSylowIn 5 M R) :
    ∃ B₁ : Subgroup G, B₁ ≤ R ∧ inD 5 M B₁ ∧ IsElemAbelian 5 B₁ ∧ Nat.card ↥B₁ = 5 ^ m := by
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have hS := h.toCex117Base.toSec11.toSec10Fails
  have hBM : B ≤ M := le_of_isPreUniquenessTwoLocal hS.standing hS.bOne hS.pre
  have hBel : IsElemAbelian 5 B := hS.bOne.1.1
  obtain ⟨y, hyM, T, hTp, hTM, hRT, hBT⟩ :=
    exists_conj_le_pGroup' hR.1 hR.2.1 hBM (isPGroup_of_elemAb hBel)
  have hTR : T = R := hR.2.2 T hTM hTp hRT
  rw [hTR] at hBT
  exact ⟨GLBConj y B, hBT, (lemma101_i_holds hS hyM (lemma101_ii_holds hS) h.pair.1.2.1).1,
    isElemAbelian_conj y hBel, by rw [card_conj, hS.standing.card_eq hS.bOne]⟩

theorem normalizer_plane_le {m : ℕ} {B M E A : Subgroup G} {a : G} {K : Subgroup G}
    (h119 : Lemma119Statement) (h : Cex117 G m 5 B M E A a K) {B₁ V : Subgroup G}
    (hB₁D : inD 5 M B₁) (hB₁el : IsElemAbelian 5 B₁) (hB₁c : Nat.card ↥B₁ = 5 ^ m)
    (hVp : IsPPlane 5 V) (hB₁V : B₁ ≤ Subgroup.normalizer (V : Set G)) :
    Subgroup.normalizer (V : Set G) ≤ M := by
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have hS := h.toCex117Base.toSec11.toSec10Fails
  obtain ⟨hrk, -, -, -⟩ := h119 h
  have hm4 : 4 ≤ m := hS.standing.four_le
  have hlines := card_le_mul_inf_centralizer (isPGroup_of_elemAb hB₁el) hVp.2 hB₁V
  set Cb := B₁ ⊓ Subgroup.centralizer (V : Set G) with hCb
  have hCb3 : 5 ^ 3 ≤ Nat.card ↥Cb := by
    rw [hB₁c] at hlines
    have h5 : 5 ^ 4 ≤ 5 ^ m := Nat.pow_le_pow_right (by norm_num) hm4
    have : 5 * 5 ^ 3 ≤ 5 * Nat.card ↥Cb := by
      calc 5 * 5 ^ 3 = 5 ^ 4 := by norm_num
        _ ≤ 5 ^ m := h5
        _ ≤ 5 * Nat.card ↥Cb := hlines
    omega
  have hCbel : IsElemAbelian 5 Cb := l1110_isElemAbelian_of_le hB₁el inf_le_left
  have hVCb : V ≤ Subgroup.centralizer (Cb : Set G) := Subgroup.le_centralizer_iff.1 inf_le_right
  have hVCel : IsElemAbelian 5 (V ⊔ Cb) := isElemAbelian_sup_of_commute hVp.1 hCbel hVCb
  obtain ⟨A₁, hA₁sc, hA₁⟩ := exists_isSCp_top_above' hVCel
  obtain ⟨U₃, hU₃, hU₃Cb⟩ := exists_isEkIn_le (X := ⊤) le_top hCbel hCb3
  have hU₃A₁ : U₃ ≤ A₁ := hU₃Cb.trans (le_sup_right.trans hA₁)
  have hU₃B₁ : U₃ ≤ B₁ := hU₃Cb.trans inf_le_left
  have hconn : IsKConnectedIn 5 (CFSG.Open.pRank 5 (E ⊓ A) + 1) ⊤ A₁ B₁ := by
    rw [hrk]
    refine ⟨le_top, hA₁sc.2.1, ?_, le_top, hB₁el, ?_, Or.inr ⟨U₃, U₃, hU₃, hU₃,
      le_centralizer_of_le hA₁sc.2.1 le_rfl hU₃A₁, Relation.ReflTransGen.refl,
      le_centralizer_of_le hB₁el hU₃B₁ le_rfl⟩⟩
    · calc 5 ^ 3 = Nat.card ↥U₃ := hU₃.2.2.symm
        _ ≤ Nat.card ↥A₁ := Subgroup.card_le_of_le hU₃A₁
    · rw [hB₁c]
      exact Nat.pow_le_pow_right (by norm_num) (by omega)
  have hA₁D : inD 5 M A₁ := lemma104_iii_holds hS h.pair hA₁sc hB₁D hconn
  have hVrk : 2 ≤ CFSG.Open.pRank 5 V := by
    have h1 : CFSG.Open.pRank 5 V = 2 := Nat.pow_right_injective (by norm_num : 2 ≤ 5)
      ((l1110_card_eq_pow_pRank hVp.1).symm.trans hVp.2)
    omega
  exact (l1110_normalizer_le_glbCore (le_sup_left.trans hA₁) hVrk).trans hA₁D.2.clause_d

theorem ieStarOf_le_M_of_not_isCyclic (h119 : Lemma119Statement) (h111 : Prop111Statement)
    {m : ℕ} {B M E A : Subgroup G} {a : G} {K : Subgroup G} (h : Cex117 G m 5 B M E A a K)
    {R : Subgroup G} (hR : IsSylowIn 5 M R) (hEAR : E ⊔ A ≤ R) {e : G}
    (heZ : e ∈ omegaOne 5 (centerOf R)) (he1 : e ≠ 1) (hnc : ¬ IsCyclic ↥(CRIeStar R K e)) :
    IeStarOf K e ≤ M := by
  have hp : Nat.Prime 5 := by norm_num
  haveI : Fact (Nat.Prime 5) := ⟨hp⟩
  have hS := h.toCex117Base.toSec11.toSec10Fails
  have hsc := lemma104_ii_holds hS h.pair
  have hZle : omegaOne 5 (centerOf R) ≤ E ⊓ A :=
    le_inf (l1110_omegaOne_centerOf_le hsc.1 (le_sup_left.trans hEAR))
      (l1110_omegaOne_centerOf_le hsc.2 (le_sup_right.trans hEAR))
  have heA : e ∈ A := (Subgroup.mem_inf.1 (hZle heZ)).2
  have hRC : R ≤ Cg e := fun r hr => Subgroup.mem_centralizer_singleton_iff.2
    (comm_of_mem_centerOf (omegaOne_le' 5 _ heZ) hr)
  have hOM : GLAPPrimeCoreOf 5 (Cg e) ≤ M := h111 h.toCex117Base.toSec11 heA he1
  have hOcop := CFSG.HardMathSupport.Solomon.LocalBalance.Lemma512Ns.card_gLAPPrimeCoreOf_coprime 5 (Cg e)
  have hCeO := CFSG.HardMathSupport.Solomon.LocalBalance.Lemma512Ns.le_normalizer_gLAPPrimeCoreOf 5 (Cg e)
  obtain ⟨V, hVC, hV, hVn⟩ :=
    exists_normal_plane_le hR.2.1 (cRIeStar_le R K e) (cRIeStar_normal hRC) hnc
  obtain ⟨B₁, hB₁R, hB₁D, hB₁el, hB₁c⟩ := exists_conj_B_le h hR
  have hRV : R ≤ Subgroup.normalizer (V : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hV.1).1 hVn
  have hVM := normalizer_plane_le h119 h hB₁D hB₁el hB₁c ⟨hV.2.1, hV.2.2⟩ (hB₁R.trans hRV)
  intro z hz
  have hzC : z ∈ Cg e := ieStarOf_le_cg K e hz
  have hVR : V ≤ R := hV.1
  obtain ⟨c, hc, o, ho, rfl⟩ := exists_fixed_mul (hR.2.1.to_le hVR) (hVR.trans hRC) hCeO hOcop hzC
    (fun v hv => ((mem_cRIeStar).1 (hVC hv)).2.2 z hz)
  exact M.mul_mem (hVM (Subgroup.centralizer_le_normalizer _ hc)) (hOM ho)

end Cover

section Ke

variable {G : Type} [Group G] [Finite G]

open CFSG.HardMathSupport.Solomon.LocalBalance (barAut_mk)

theorem exists_orderOf_five_mem_ke (hI1421 : Input14_21) (hF : Fi22Facts) (h119 : Lemma119Statement)
    {m : ℕ} {B M E A : Subgroup G} {a : G} {K : Subgroup G} (h : Cex117 G m 5 B M E A a K)
    (hfi : IsSporType .Fi22 (barOf 5 K)) {e : G} (heA : e ∈ E ⊓ A) (he1 : e ≠ 1) :
    ∃ x ∈ GLAPLayer 5 (K ⊓ Cg e), orderOf x = 5 := by
  have hp : Nat.Prime 5 := by norm_num
  haveI : Fact (Nat.Prime 5) := ⟨hp⟩
  have hS := h.toCex117Base.toSec11.toSec10Fails
  have hsc := lemma104_ii_holds hS h.pair
  obtain ⟨-, hN, hfaith, hinn⟩ := h119 h
  have heN : e ∈ Subgroup.normalizer (K : Set G) := hN heA
  obtain ⟨k, hkK, hkc⟩ := hinn e heA
  obtain ⟨hZ, -, -, -⟩ := hF (barOf 5 K) hfi
  set O' : Subgroup ↥K := GLAPPrimeCore 5 ↥K with hO'
  set π : ↥K →* ↥K ⧸ O' := QuotientGroup.mk' O' with hπ
  have hkN : k ∈ Subgroup.normalizer (K : Set G) := Subgroup.le_normalizer hkK
  have hbe : barAut 5 K ⟨e, heN⟩ = MulAut.conj (π ⟨k, hkK⟩) := by
    obtain ⟨-, hcN, hc1⟩ := mem_centBar_iff'.1 hkc
    have hsplit : (⟨e, heN⟩ : ↥(Subgroup.normalizer (K : Set G))) = ⟨k, hkN⟩ * ⟨k⁻¹ * e, hcN⟩ :=
      Subtype.ext (by simp)
    rw [hsplit, map_mul, hc1, mul_one, barAut_of_mem hkK]
    rfl
  set kb : ↥K ⧸ O' := π ⟨k, hkK⟩ with hkb
  have he5 : e ^ 5 = 1 := hsc.2.2.1.2 e (Subgroup.mem_inf.1 heA).2
  have hconj_one : ∀ z : ↥K ⧸ O', MulAut.conj z = 1 → z = 1 := by
    intro z hz
    have hc : z ∈ Subgroup.center (↥K ⧸ O') := by
      rw [Subgroup.mem_center_iff]
      intro w
      have h1 := congrArg (fun φ : MulAut (↥K ⧸ O') => φ w) hz
      simp only [MulAut.conj_apply, MulAut.one_apply] at h1
      exact (mul_inv_eq_iff_eq_mul.1 h1).symm
    have hZ' : Subgroup.center (↥K ⧸ O') = ⊥ := hZ
    rw [hZ', Subgroup.mem_bot] at hc
    exact hc
  have hkb5 : kb ^ 5 = 1 := by
    refine hconj_one _ ?_
    rw [map_pow, ← hbe, ← map_pow]
    have : (⟨e, heN⟩ : ↥(Subgroup.normalizer (K : Set G))) ^ 5 = 1 := Subtype.ext (by simpa using he5)
    rw [this, map_one]
  have hkb1 : kb ≠ 1 := by
    intro h1
    apply he1
    refine hfaith e heA (mem_centBar_iff'.2 ⟨trivial, heN, ?_⟩)
    rw [hbe, h1, map_one]
  have hkbo : orderOf kb = 5 := orderOf_eq_prime hkb5 hkb1
  obtain ⟨ψ⟩ := hI1421 (barOf 5 K) hfi kb hkbo
  have hLc : Nat.card ↥(GLAPLayer 5 (Subgroup.centralizer ({kb} : Set (↥K ⧸ O')))) = 60 := by
    rw [Nat.card_congr ψ.toEquiv]
    exact CFSG.GH74.GLS.LU.Local.Five.nat_card_alternatingGroup_five
  obtain ⟨ℓ, hℓ⟩ := exists_prime_orderOf_dvd_card'
    (G := ↥(GLAPLayer 5 (Subgroup.centralizer ({kb} : Set (↥K ⧸ O'))))) 5 (by rw [hLc]; norm_num)
  set C' : Subgroup ↥K := (Cg e).subgroupOf K with hC'
  have hbar : ∀ (j : ℤ) (y : ↥K), π ⟨e ^ j * (y : G) * (e ^ j)⁻¹,
      (Subgroup.mem_normalizer_iff.1 (Subgroup.zpow_mem _ heN j) y).1 y.2⟩ = kb ^ j * π y * (kb ^ j)⁻¹ := by
    intro j y
    have h1 := barAut_mk 5 K ⟨e ^ j, Subgroup.zpow_mem _ heN j⟩ y
    have h2 : barAut 5 K ⟨e ^ j, Subgroup.zpow_mem _ heN j⟩ = MulAut.conj (kb ^ j) := by
      have : (⟨e ^ j, Subgroup.zpow_mem _ heN j⟩ : ↥(Subgroup.normalizer (K : Set G))) =
          (⟨e, heN⟩ : ↥(Subgroup.normalizer (K : Set G))) ^ j := Subtype.ext (by simp)
      rw [this, map_zpow, hbe, ← map_zpow]
    rw [h2, MulAut.conj_apply] at h1
    exact h1.symm
  have hCmap : C'.map π = Subgroup.centralizer ({kb} : Set (↥K ⧸ O')) := by
    apply le_antisymm
    · rintro _ ⟨y, hy, rfl⟩
      have hye : e * (y : G) * e⁻¹ = y := by
        have h1 : (y : G) * e = e * y := Subgroup.mem_centralizer_singleton_iff.1 (Subgroup.mem_subgroupOf.1 hy)
        rw [← h1]
        group
      have h2 := hbar 1 y
      simp only [zpow_one] at h2
      have h3 : (⟨e * (y : G) * e⁻¹, (Subgroup.mem_normalizer_iff.1 heN y).1 y.2⟩ : ↥K) = y :=
        Subtype.ext hye
      rw [Subgroup.mem_centralizer_singleton_iff]
      have h4 : π y = kb * π y * kb⁻¹ := by
        rw [← h2]
        exact congrArg π h3.symm
      calc π y * kb = (kb * π y * kb⁻¹) * kb := by rw [← h4]
        _ = kb * π y := by group
    · intro yb hyb
      obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective O' yb
      have hcomm : Commute kb (π y) := (Subgroup.mem_centralizer_singleton_iff.1 hyb).symm
      set O := GLAPPrimeCoreOf 5 K with hO
      have hOcop := CFSG.HardMathSupport.Solomon.LocalBalance.Lemma512Ns.card_gLAPPrimeCoreOf_coprime 5 K
      have hVX : Subgroup.zpowers e ≤ Subgroup.normalizer (O : Set G) :=
        (Subgroup.zpowers_le).2
          (CFSG.HardMathSupport.Solomon.LocalBalance.Lemma512Ns.mem_normalizer_gLAPPrimeCoreOf 5 heN)
      have hzX : (y : G) ∈ Subgroup.normalizer (O : Set G) :=
        CFSG.HardMathSupport.Solomon.LocalBalance.Lemma512Ns.le_normalizer_gLAPPrimeCoreOf 5 K y.2
      have hep : IsPGroup 5 ↥(Subgroup.zpowers e) :=
        IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, orderOf_eq_of_pow he5 he1, pow_one])
      have hz : ∀ v ∈ Subgroup.zpowers e, v * (y : G) * v⁻¹ * (y : G)⁻¹ ∈ O := by
        intro v hv
        obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.1 hv
        have h1 := hbar j y
        have h2 : kb ^ j * π y * (kb ^ j)⁻¹ = π y := by
          rw [(hcomm.zpow_left j).eq]
          group
        rw [h2] at h1
        set u : ↥K := ⟨e ^ j * (y : G) * (e ^ j)⁻¹,
          (Subgroup.mem_normalizer_iff.1 (Subgroup.zpow_mem _ heN j) y).1 y.2⟩ with hu
        have h3 : u⁻¹ * y ∈ O' := QuotientGroup.eq.1 h1
        have h4 : u * y⁻¹ ∈ O' := by
          have h5 := O'.inv_mem ((GLAPPrimeCore.normal 5 ↥K).conj_mem _ h3 y)
          have e' : (y * (u⁻¹ * y) * y⁻¹)⁻¹ = u * y⁻¹ := by group
          rwa [e'] at h5
        exact (CFSG.HardMathSupport.Solomon.LocalBalance.Lemma512Ns.mem_gLAPPrimeCoreOf_iff 5 K _).2
          ⟨(u * y⁻¹).2, h4⟩
      obtain ⟨c, hc, o, ho, hyco⟩ := exists_fixed_mul hep hVX le_rfl hOcop hzX hz
      have hoK : o ∈ K := gLAPPrimeCoreOf_le 5 K ho
      have hcK : c ∈ K := by
        have : c = (y : G) * o⁻¹ := by rw [hyco]; group
        rw [this]
        exact K.mul_mem y.2 (K.inv_mem hoK)
      refine ⟨⟨c, hcK⟩, Subgroup.mem_subgroupOf.2 (Subgroup.mem_centralizer_singleton_iff.2
        ((Subgroup.mem_centralizer_iff.1 hc e (Subgroup.mem_zpowers e)).symm)), ?_⟩
      obtain ⟨hoK', ho'⟩ := (CFSG.HardMathSupport.Solomon.LocalBalance.Lemma512Ns.mem_gLAPPrimeCoreOf_iff 5 K o).1 ho
      have hy' : y = ⟨c, hcK⟩ * ⟨o, hoK⟩ := Subtype.ext hyco
      rw [hy', map_mul, show π ⟨o, hoK⟩ = 1 from (QuotientGroup.eq_one_iff _).2 ho', mul_one]
  have hker1 : Nat.Coprime 5 (Nat.card ↥(C' ⊓ π.ker)) := by
    refine Nat.Coprime.coprime_dvd_right (Subgroup.card_dvd_of_le inf_le_right) ?_
    rw [hπ, QuotientGroup.ker_mk']
    exact CFSG.HardMathSupport.Solomon.LocalBalance.coprime_card_gLAPPrimeCore_aux 5 ↥K
  have h1 := CFSG.HardMathSupport.Solomon.Coordinator.i227m_glaPLayer_map hp π hker1
  have hker2 : Nat.Coprime 5 (Nat.card ↥(C' ⊓ (K.subtype).ker)) := by
    rw [Subgroup.ker_subtype, inf_bot_eq, Subgroup.card_bot]
    exact Nat.coprime_one_right 5
  have h2 := CFSG.HardMathSupport.Solomon.Coordinator.i227m_glaPLayer_map hp K.subtype hker2
  have hCK : C'.map K.subtype = K ⊓ Cg e := by
    rw [hC', Subgroup.subgroupOf_map_subtype, inf_comm]
  rw [hCK] at h2
  have hℓmem : (ℓ : ↥K ⧸ O') ∈ (GLAPLayer 5 C').map π := by
    rw [← h1, hCmap]
    exact ℓ.2
  obtain ⟨z, hz, hzℓ⟩ := hℓmem
  have hzKe : (z : G) ∈ GLAPLayer 5 (K ⊓ Cg e) := by
    rw [h2]
    exact ⟨z, hz, rfl⟩
  have hdvd : 5 ∣ orderOf (z : G) := by
    have h3 : orderOf (π z) = 5 := by rw [hzℓ, Subgroup.orderOf_coe, hℓ]
    rw [Subgroup.orderOf_coe, ← h3]
    exact orderOf_map_dvd π z
  have hz0 : orderOf (z : G) ≠ 0 := (orderOf_pos _).ne'
  exact ⟨(z : G) ^ (orderOf (z : G) / 5), Subgroup.pow_mem _ hzKe _,
    orderOf_pow_orderOf_div hz0 hdvd⟩

theorem inf_ne_bot_of_sylow {p : ℕ} [Fact p.Prime] {R N : Subgroup G} (hR : IsSylowIn p ⊤ R)
    (hRN : R ≤ Subgroup.normalizer (N : Set G)) {x : G} (hxN : x ∈ N) (hx : orderOf x = p) :
    R ⊓ N ≠ ⊥ := by
  have hzx : IsPGroup p ↥(Subgroup.zpowers x) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hx, pow_one])
  have hxX : Subgroup.zpowers x ≤ Subgroup.normalizer (N : Set G) :=
    (Subgroup.zpowers_le).2 (Subgroup.le_normalizer hxN)
  obtain ⟨y, hyX, S, hSp, -, hRS, hyS⟩ := exists_conj_le_pGroup' hRN hR.2.1 hxX hzx
  have hSR : S = R := hR.2.2 S le_top hSp hRS
  rw [hSR] at hyS
  have h1 : y⁻¹ * x * y ∈ R := hyS (by
    rw [mem_gLBConj]
    simpa [mul_assoc] using Subgroup.mem_zpowers x)
  have h2 : y⁻¹ * x * y ∈ N := by
    have := (Subgroup.mem_normalizer_iff.1 (Subgroup.inv_mem _ hyX) x).1 hxN
    simpa using this
  have hx1 : x ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at hx
    exact (Fact.out : p.Prime).one_lt.ne hx
  intro hbot
  have h3 : y⁻¹ * x * y ∈ R ⊓ N := Subgroup.mem_inf.2 ⟨h1, h2⟩
  rw [hbot, Subgroup.mem_bot] at h3
  apply hx1
  have := congrArg (fun t => y * t * y⁻¹) h3
  simpa [mul_assoc] using this

end Ke

@[expose] def IeStarClaim : Prop :=
  ∀ {G : Type} [Group G] [Finite G] {m p : ℕ} {B M E A : Subgroup G} {a : G} {K : Subgroup G},
    Cex117 G m p B M E A a K → Type117b p K →
    ∀ R : Subgroup G, IsSylowIn 5 M R → E ⊔ A ≤ R →
    ∀ e ∈ omegaOne 5 (centerOf R), e ≠ 1 →
      e ∉ IeStarOf K e ∧ (R ⊓ IeStarOf K e) ⊓ CRIeStar R K e = ⊥ ∧
      (IsCyclic ↥(R ⊓ IeStarOf K e) → ∀ F : Subgroup G, F ≤ R → IsElemAbelian 5 F →
        Nat.card ↥F ≤ 5 * Nat.card ↥(F ⊓ ((R ⊓ IeStarOf K e) ⊔ CRIeStar R K e))) ∧
      (IsSylowIn 5 ⊤ R → omegaOne 5 (centerOf R) = E ⊓ A → A = (E ⊓ A) ⊔ Subgroup.zpowers a →
        E ⊓ A = A ⊓ K → IsSylowIn 5 (Cg a) A → Cg a ≤ Subgroup.normalizer (K : Set G) →
        ¬ GLAPLayer 5 (K ⊓ Cg e) ≤ M → IsCyclic ↥(CRIeStar R K e) →
        ∀ X : Subgroup G, (R ⊓ IeStarOf K e) ⊔ CRIeStar R K e ≤ X → X ≤ R →
          (∀ x ∈ X, ∀ y ∈ X, x * y * x⁻¹ * y⁻¹ ∈ (R ⊓ IeStarOf K e) ⊔ CRIeStar R K e) →
          (∀ x ∈ X, x ^ 5 ∈ (R ⊓ IeStarOf K e) ⊔ CRIeStar R K e) →
          Nat.card ↥X ≤ 5 * Nat.card ↥((R ⊓ IeStarOf K e) ⊔ CRIeStar R K e))

section Reductions

variable {G : Type} [Group G] [Finite G]

theorem le_cg_of_mem_omegaOne {R : Subgroup G} {e : G} (heZ : e ∈ omegaOne 5 (centerOf R)) :
    R ≤ Cg e := fun r hr => Subgroup.mem_centralizer_singleton_iff.2
  (comm_of_mem_centerOf (omegaOne_le' 5 _ heZ) hr)

end Reductions

theorem reIRCClaim_of_ieStar (hI1421 : Input14_21) (hF : Fi22Facts) (h119 : Lemma119Statement)
    (hIe : IeStarClaim) : ReIRCClaim := by
  intro G _ _ m p B M E A a K h hb R hR hEAR e heZ he1
  obtain ⟨rfl, hfi⟩ := hb
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have hS := h.toCex117Base.toSec11.toSec10Fails
  have hsc := lemma104_ii_holds hS h.pair
  obtain ⟨hrk, -, -, -⟩ := h119 h
  obtain ⟨hi, hii, hiii, -⟩ := hIe h ⟨rfl, hfi⟩ R hR hEAR e heZ he1
  have hZle : omegaOne 5 (centerOf R) ≤ E ⊓ A :=
    le_inf (l1110_omegaOne_centerOf_le hsc.1 (le_sup_left.trans hEAR))
      (l1110_omegaOne_centerOf_le hsc.2 (le_sup_right.trans hEAR))
  have hRC : R ≤ Cg e := le_cg_of_mem_omegaOne heZ
  have hRG : IsSylowIn 5 ⊤ R := (lemma104_iv_holds hS h.pair hrk hR).2.2
  obtain ⟨x, hxKe, hxo⟩ := exists_orderOf_five_mem_ke hI1421 hF h119 h hfi (hZle heZ) he1
  have hxI : x ∈ IeStarOf K e := ieOf_le_ieStarOf K e (ke_le_ieOf K e hxKe)
  have hW1 := inf_ne_bot_of_sylow hRG (hRC.trans (cg_le_normalizer_ieStarOf K e)) hxI hxo
  exact ⟨R ⊓ IeStarOf K e, CRIeStar R K e, inf_le_left, cRIeStar_le R K e, inf_ieStarOf_normal hRC,
    cRIeStar_normal hRC, hW1, fun heW => hi (Subgroup.mem_inf.1 heW).2, hii, hiii⟩

theorem reIMetaClaim_of_ieStar (h119 : Lemma119Statement) (h111 : Prop111Statement)
    (hIe : IeStarClaim) : ReIMetaClaim := by
  intro G _ _ m p B M E A a K h hb R hR hEAR hRG hZ hAeq hA2 hASyl hCaN e he he1 hKe
  obtain ⟨rfl, hfi⟩ := hb
  have heZ : e ∈ omegaOne 5 (centerOf R) := hZ ▸ he
  obtain ⟨hi, -, -, hiv⟩ := hIe h ⟨rfl, hfi⟩ R hR hEAR e heZ he1
  have hRC : R ≤ Cg e := le_cg_of_mem_omegaOne heZ
  by_cases hc : IsCyclic ↥(CRIeStar R K e)
  · exact ⟨R ⊓ IeStarOf K e, CRIeStar R K e, inf_le_left, cRIeStar_le R K e, inf_ieStarOf_normal hRC,
      cRIeStar_normal hRC, fun heW => hi (Subgroup.mem_inf.1 heW).2, hc,
      hiv hRG hZ hAeq hA2 hASyl hCaN hKe hc⟩
  · exact absurd ((ke_le_ieOf K e).trans ((ieOf_le_ieStarOf K e).trans
      (ieStarOf_le_M_of_not_isCyclic h119 h111 h hR hEAR heZ he1 hc))) hKe

theorem lemma1110CaseB_of_ieStar (h119 : Lemma119Statement) (h111 : Prop111Statement)
    (hK0 : Input24_2K0) (hF : Fi22Facts) (hI : Claims1110.InputFi22OneClassFive)
    (hIe : IeStarClaim) (h6 : Step6Claim) : Lemma1110CaseB := by
  intro G _ _ m p B M E A a K h hb _ _ _ hI1421
  exact Claims1110.false_of_typeB h119 hF hI
    (step12Claim_of_reIRC h119 (reIRCClaim_of_ieStar hI1421 hF h119 hIe))
    (step4Claim_of_reIMeta (reIMetaClaim_of_ieStar h119 h111 hIe))
    (step56Claim_of_step6 h119 h111 hK0 h6) h hb

end CFSG.LocalAnalysis.GLTheoremB.MovingAround.Claims1110c
