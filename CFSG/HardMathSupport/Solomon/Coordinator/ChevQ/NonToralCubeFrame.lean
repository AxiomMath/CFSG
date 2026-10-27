module

public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.SeitzExcOpenRest3
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.NonToralCoreDefs
public import CFSG.LieType.SeitzGeneration.ExcHighThree.KillsRootGroup

public noncomputable section

namespace CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.NonToralCore

open CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Steinberg.Adjoint CFSG.HardMathSupport.Timmesfeld.Torality
  CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.LieType.AlgebraicGroups
  CFSG.LieType.SeitzGeneration.ExcHighThree

set_option linter.unusedSectionVars false

section Monomial

variable {τ : Tag}


theorem weylQuotientHom_mem_rootCharStabilizer {L : Type} [Field L] {ι : Type}
    {a : ι → Fin τ.rank → Lˣ} {n : ModGL τ L} (hn : n ∈ monomialSubgroup τ L)
    (hna : ∀ i, rootDiagUnit τ (a i) * n = n * rootDiagUnit τ (a i)) (i : ι) :
    weylQuotientHom τ L ⟨n, hn⟩ ∈ rootCharStabilizer (a i) := by
  obtain ⟨w, k, hk, e⟩ := monomialSubgroup_le_torusWeylCosets hn
  subst e
  have hπ : weylQuotientHom τ L ⟨_, hn⟩ = w := weylQuotientHom_torus_mul hk w hn
  rw [hπ, ← conj_canonicalRep_eq_iff]
  have hdk : rootDiagUnit τ (a i) * k = k * rootDiagUnit τ (a i) :=
    rootDiagUnit_mul_comm_of_mem_torusGroup (a i) hk
  have h1 : rootDiagUnit τ (a i) * canonicalRep (coxeterSystem τ) L w =
      canonicalRep (coxeterSystem τ) L w * rootDiagUnit τ (a i) := by
    have e1 : rootDiagUnit τ (a i) * canonicalRep (coxeterSystem τ) L w =
        k⁻¹ * (rootDiagUnit τ (a i) * (k * canonicalRep (coxeterSystem τ) L w)) := by
      rw [← mul_assoc (rootDiagUnit τ (a i)) k, hdk]
      group
    rw [e1, hna i]
    group
  rw [h1, mul_inv_cancel_right]

theorem monomialElt_comm_of_mem_rootCharStabilizer {L : Type} [Field L] [IsAlgClosed L]
    {a : Fin τ.rank → Lˣ} (b : Fin τ.rank → Lˣ) {ω : WeylGroup τ}
    (hω : ω ∈ rootCharStabilizer a) :
    rootDiagUnit τ a * monomialElt τ L b ω = monomialElt τ L b ω * rootDiagUnit τ a := by
  have hdb : rootDiagUnit τ a * rootDiagUnit τ b = rootDiagUnit τ b * rootDiagUnit τ a :=
    rootDiagUnit_mul_comm_of_mem_torusGroup a (rootDiagUnit_mem_torusGroup b)
  have hcr : rootDiagUnit τ a * canonicalRep (coxeterSystem τ) L ω =
      canonicalRep (coxeterSystem τ) L ω * rootDiagUnit τ a := by
    have h := (conj_canonicalRep_eq_iff (K := L) (a := a) (w := ω)).2 hω
    calc rootDiagUnit τ a * canonicalRep (coxeterSystem τ) L ω
        = (rootDiagUnit τ a * canonicalRep (coxeterSystem τ) L ω * (rootDiagUnit τ a)⁻¹) *
            rootDiagUnit τ a := by group
      _ = canonicalRep (coxeterSystem τ) L ω * rootDiagUnit τ a := by rw [h]
  unfold monomialElt
  calc rootDiagUnit τ a * (rootDiagUnit τ b * canonicalRep (coxeterSystem τ) L ω)
      = (rootDiagUnit τ a * rootDiagUnit τ b) * canonicalRep (coxeterSystem τ) L ω := by group
    _ = rootDiagUnit τ b * (rootDiagUnit τ a * canonicalRep (coxeterSystem τ) L ω) := by
        rw [hdb]; group
    _ = rootDiagUnit τ b * (canonicalRep (coxeterSystem τ) L ω * rootDiagUnit τ a) := by
        rw [hcr]
    _ = rootDiagUnit τ b * canonicalRep (coxeterSystem τ) L ω * rootDiagUnit τ a := by group

theorem exists_eq_monomialElt {L : Type} [Field L] {n : ModGL τ L}
    (hn : n ∈ monomialSubgroup τ L) :
    ∃ b : Fin τ.rank → Lˣ, n = monomialElt τ L b (weylQuotientHom τ L ⟨n, hn⟩) := by
  obtain ⟨w, k, hk, e⟩ := monomialSubgroup_le_torusWeylCosets hn
  obtain ⟨b, hb⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup hk
  subst e
  exact ⟨b, by rw [weylQuotientHom_torus_mul hk w hn, monomialElt, hb]⟩

theorem monomialElt_mem_monomialSubgroup {L : Type} [Field L] [IsAlgClosed L]
    (b : Fin τ.rank → Lˣ) (ω : WeylGroup τ) : monomialElt τ L b ω ∈ monomialSubgroup τ L :=
  mul_mem (torusGroup_le_monomialSubgroup (rootDiagUnit_mem_torusGroup b))
    (canonicalRep_mem_monomialSubgroup L ω)

theorem exists_conj_mem_torusGroup_of_weyl_mem_kernel {p : ℕ} (hmon : MonomialToralAt τ p)
    {L : Type} [Field L] [IsAlgClosed L] (hL : ringChar L ≠ p) {ι : Type}
    {a : ι → Fin τ.rank → Lˣ} {n : ModGL τ L} (hn : n ∈ monomialSubgroup τ L)
    (hp : n ^ p = 1) (hwS : weylQuotientHom τ L ⟨n, hn⟩ ∈ kernelWeylGroup (familyChar a)) :
    ∃ g ∈ adjointGroup τ L, (∀ i, rootDiagUnit τ (a i) * g = g * rootDiagUnit τ (a i)) ∧
      g * n * g⁻¹ ∈ torusGroup τ L := by
  obtain ⟨g, hg, hgn⟩ := hmon L hL (ι → Lˣ) (familyChar a) _ hn hwS
    (weylQuotientHom_pow_eq_one hn hp)
  refine ⟨g, rootSpan_le_adjointGroup L _ hg, fun i => ?_, hgn⟩
  have hgc : g ∈ Subgroup.centralizer {rootDiagUnit τ (a i)} := by
    refine rootSpan_le_centralizer (a i) (S := kernelRoots (familyChar a)) (fun α hα => ?_) hg
    rw [kernelRoots_familyChar] at hα
    exact ⟨hα.1, hα.2 i⟩
  exact (Subgroup.mem_centralizer_singleton_iff.1 hgc).symm

end Monomial

section StabExt

variable {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] {ι : Type}


@[expose] def stabExt (a : ι → Fin τ.rank → Lˣ) : Subgroup (ModGL τ L) where
  carrier := {g | ∃ m ∈ familyGroup (K := L) a, ∃ x : WeylGroup τ,
    (fun α => x • α) '' familyKernel a = familyKernel a ∧
      g = m * canonicalRep (coxeterSystem τ) L x}
  one_mem' := ⟨1, one_mem _, 1, by simp, by rw [canonicalRep_one, mul_one]⟩
  mul_mem' := by
    rintro _ _ ⟨m, hm, x, hx, rfl⟩ ⟨m', hm', y, hy, rfl⟩
    obtain ⟨k, hk, hkxy⟩ := canonicalRep_mul_mem (R := L) x y
    have hnorm := canonicalRep_mem_normalizer_of_image (K := L) (a := a) hx
    have hc : canonicalRep (coxeterSystem τ) L x * m' *
        (canonicalRep (coxeterSystem τ) L x)⁻¹ ∈ familyGroup (K := L) a :=
      (Subgroup.mem_normalizer_iff.1 hnorm m').1 hm'
    refine ⟨m * (canonicalRep (coxeterSystem τ) L x * m' *
      (canonicalRep (coxeterSystem τ) L x)⁻¹) * k,
      mul_mem (mul_mem hm hc) (torus_le_familyGroup a hk), x * y, ?_, ?_⟩
    · have : (fun α => (x * y) • α) '' familyKernel a =
          (fun α => x • α) '' ((fun α => y • α) '' familyKernel a) := by
        rw [Set.image_image]
        simp only [mul_smul]
      rw [this, hy, hx]
    · set nx := canonicalRep (coxeterSystem τ) L x
      set ny := canonicalRep (coxeterSystem τ) L y
      calc m * nx * (m' * ny) = m * (nx * m' * nx⁻¹) * (nx * ny) := by group
        _ = m * (nx * m' * nx⁻¹) * (k * canonicalRep (coxeterSystem τ) L (x * y)) := by
            rw [hkxy]
        _ = m * (nx * m' * nx⁻¹) * k * canonicalRep (coxeterSystem τ) L (x * y) := by group
  inv_mem' := by
    rintro _ ⟨m, hm, x, hx, rfl⟩
    obtain ⟨k, hk, hkx⟩ := canonicalRep_inv_eq (K := L) (τ := τ) x
    have hx' : (fun α => x⁻¹ • α) '' familyKernel a = familyKernel a := by
      calc (fun α => x⁻¹ • α) '' familyKernel a
          = (fun α => x⁻¹ • α) '' ((fun α => x • α) '' familyKernel a) := by rw [hx]
        _ = familyKernel a := by
            rw [Set.image_image]
            simp only [inv_smul_smul, Set.image_id']
    have hnorm := canonicalRep_mem_normalizer_of_image (K := L) (a := a) hx'
    have hc : canonicalRep (coxeterSystem τ) L x⁻¹ * m⁻¹ *
        (canonicalRep (coxeterSystem τ) L x⁻¹)⁻¹ ∈ familyGroup (K := L) a :=
      (Subgroup.mem_normalizer_iff.1 hnorm m⁻¹).1 (inv_mem hm)
    refine ⟨k * (canonicalRep (coxeterSystem τ) L x⁻¹ * m⁻¹ *
      (canonicalRep (coxeterSystem τ) L x⁻¹)⁻¹), mul_mem (torus_le_familyGroup a hk) hc, x⁻¹,
      hx', ?_⟩
    set ni := canonicalRep (coxeterSystem τ) L x⁻¹
    calc (m * canonicalRep (coxeterSystem τ) L x)⁻¹
        = (canonicalRep (coxeterSystem τ) L x)⁻¹ * m⁻¹ := mul_inv_rev _ _
      _ = k * ni * m⁻¹ := by rw [hkx]
      _ = k * (ni * m⁻¹ * ni⁻¹) * ni := by group

theorem mem_stabExt {a : ι → Fin τ.rank → Lˣ} {g : ModGL τ L} :
    g ∈ stabExt a ↔ ∃ m ∈ familyGroup (K := L) a, ∃ x : WeylGroup τ,
      (fun α => x • α) '' familyKernel a = familyKernel a ∧
        g = m * canonicalRep (coxeterSystem τ) L x := Iff.rfl

theorem familyCentralizer_le_stabExt (a : ι → Fin τ.rank → Lˣ) {g : ModGL τ L}
    (hg : g ∈ familyCentralizer τ L a) : g ∈ stabExt a := by
  obtain ⟨w, hw, m, hm, rfl⟩ := familyCentralizer_le_mul τ L a hg
  exact ⟨m, hm, w, image_familyKernel hw, rfl⟩

theorem canonicalRep_mem_stabExt (a : ι → Fin τ.rank → Lˣ) {x : WeylGroup τ}
    (hx : (fun α => x • α) '' familyKernel a = familyKernel a) :
    canonicalRep (coxeterSystem τ) L x ∈ stabExt a :=
  ⟨1, one_mem _, x, hx, (one_mul _).symm⟩

theorem entrywiseFrobGL_mem_stabExt (ℓ : ℕ) [Fact ℓ.Prime] [CharP L ℓ]
    (a : ι → Fin τ.rank → Lˣ) (e : ℕ) {g : ModGL τ L} (hg : g ∈ stabExt a) :
    entrywiseFrobGL τ L ℓ e g ∈ stabExt a := by
  obtain ⟨m, hm, x, hx, rfl⟩ := hg
  refine ⟨entrywiseFrobGL τ L ℓ e m, entrywiseFrobGL_mem_familyGroup ℓ a e hm, x, hx, ?_⟩
  rw [map_mul]
  exact congrArg (_ * ·)
    (CFSG.RankThree.PartOne.KE.frobenius_canonicalRep (iterateFrobenius L ℓ e) x)

theorem cocycle_mem_stabExt (ℓ : ℕ) [Fact ℓ.Prime] [CharP L ℓ] (a : ι → Fin τ.rank → Lˣ)
    (e : ℕ) {w : WeylGroup τ} (hw : (fun α => w • α) '' familyKernel a = familyKernel a)
    {z : ModGL τ L} (hz : z ∈ familyCentralizer τ L a) :
    z * canonicalRep (coxeterSystem τ) L w * (entrywiseFrobGL τ L ℓ e z)⁻¹ ∈ stabExt a :=
  mul_mem (mul_mem (familyCentralizer_le_stabExt a hz) (canonicalRep_mem_stabExt a hw))
    (inv_mem (entrywiseFrobGL_mem_stabExt ℓ a e (familyCentralizer_le_stabExt a hz)))

end StabExt

section Frame

variable {τ : Tag} {K : Type} [Field K] [Finite K]


theorem ringChar_algebraicClosure_ne_three (hK3 : ¬ 3 ∣ Nat.card K) :
    ringChar (AlgebraicClosure K) ≠ 3 := by
  haveI : Fact (ringChar K).Prime := ⟨CharP.char_is_prime K (ringChar K)⟩
  haveI : CharP (AlgebraicClosure K) (ringChar K) :=
    charP_of_injective_algebraMap (algebraMap K (AlgebraicClosure K)).injective _
  rw [ringChar.eq (AlgebraicClosure K) (ringChar K)]
  intro h
  apply hK3
  obtain ⟨e, he, hcard⟩ := card_eq_pow_ringChar K
  rw [hcard, h]
  exact dvd_pow_self 3 (by omega)

structure CubeFrame {P : Subgroup (adjointGroup τ K)} (D : LangPlaneData τ K P)
    (z : adjointGroup τ K) where
  a : Fin 2 → Fin τ.rank → (AlgebraicClosure K)ˣ
  g : ModGL τ (AlgebraicClosure K)
  b : Fin τ.rank → (AlgebraicClosure K)ˣ
  ω : WeylGroup τ
  m : ModGL τ (AlgebraicClosure K)
  x : WeylGroup τ
  exp3 : ∀ s i, a s i ^ 3 = 1
  g_mem : g ∈ adjointGroup τ (AlgebraicClosure K)
  conj_z : g * monomialElt τ (AlgebraicClosure K) b ω * g⁻¹ =
    baseChangeGL (algebraMap K (AlgebraicClosure K)) (z : ModGL τ K)
  ω_pow : ω ^ 3 = 1
  ω_stab : ∀ s, ω ∈ rootCharStabilizer (a s)
  frame : Units.map (entrywiseHom D.Fr) g =
    g * (m * canonicalRep (coxeterSystem τ) (AlgebraicClosure K) x)
  m_mem : m ∈ familyGroup (K := AlgebraicClosure K) a
  x_stab : (fun α => x • α) '' familyKernel a = familyKernel a
  plane : ∀ p ∈ P, g⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K)) (p : ModGL τ K) * g ∈
    Subgroup.closure (Set.range fun s => rootDiagUnit τ (a s))
  kills : ∀ α, IsRoot τ α → D.Kills α → α ∈ familyKernel a

theorem nonempty_cubeFrame (hK3 : ¬ 3 ∣ Nat.card K)
    {E₀ P : Subgroup (adjointGroup τ K)} (hE₀ : IsElemAbelian 3 E₀) (hc : Nat.card E₀ = 3 ^ 3)
    (hPE : P ≤ E₀) (hPc : Nat.card P = 3 ^ 2) (D : LangPlaneData τ K P)
    {z : adjointGroup τ K} (hz : z ∈ E₀) : Nonempty (CubeFrame D z) := by
  classical
  have hp3 : Nat.Prime 3 := Nat.prime_three
  haveI : Fact (Nat.Prime 3) := ⟨hp3⟩
  haveI : Fact (ringChar K).Prime := ⟨CharP.char_is_prime K (ringChar K)⟩
  set L := AlgebraicClosure K with hLdef
  haveI : CharP L (ringChar K) :=
    charP_of_injective_algebraMap (algebraMap K L).injective (ringChar K)
  obtain ⟨e, he, hcard⟩ := card_eq_pow_ringChar K
  have hℓ : ringChar K ≠ 3 := by
    intro h
    apply hK3
    rw [hcard, h]
    exact dvd_pow_self 3 (by omega)
  have halg := isAlgebraic_zmod_algebraicClosure_of_finite K (ringChar K)
  have hexpE : ∀ x ∈ E₀, x ^ 3 = 1 := hE₀.2
  have hcommE : ∀ x ∈ E₀, ∀ y ∈ E₀, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hE₀.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  have hFrEq : D.Fr = iterateFrobenius L (ringChar K) e :=
    RingHom.ext fun c => by rw [D.hFr c, iterateFrobenius_def, hcard]
  have hΦ : ∀ y : ModGL τ L, Units.map (entrywiseHom D.Fr) y =
      entrywiseFrobGL τ L (ringChar K) e y := by
    intro y
    rw [hFrEq]
  set ι : K →+* L := algebraMap K L with hι
  set φ : ↥(adjointGroup τ K) →* ModGL τ L :=
    (baseChangeGL ι).comp (adjointGroup τ K).subtype with hφ
  have hφG : ∀ x, φ x ∈ adjointGroup τ L := fun x =>
    CFSG.LieType.Chevalley.baseChangeGL_mem_adjointGroup ι x.2
  have hdiag : ∀ x ∈ P, ∃ a' : Fin τ.rank → Lˣ,
      rootDiagUnit τ a' = D.g0⁻¹ * baseChangeGL ι
        ((D.c * x * D.c⁻¹ : adjointGroup τ K) : ModGL τ K) * D.g0 ∧
      canonicalRep (coxeterSystem τ) L D.w * Units.map (entrywiseHom D.Fr) (rootDiagUnit τ a') *
        (canonicalRep (coxeterSystem τ) L D.w)⁻¹ = rootDiagUnit τ a' := by
    intro x hx
    obtain ⟨t, ht, hte⟩ := Subgroup.mem_map.1 (D.hc x hx)
    obtain ⟨hT, hfix⟩ := CFSG.RankThree.PartOne.KE.mem_twistedTorusOf.1 ht
    obtain ⟨a', ha'⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup hT
    refine ⟨a', ?_, by rw [← ha']; exact hfix⟩
    rw [← ha']
    have hte' : D.g0 * t * D.g0⁻¹ =
        baseChangeGL ι ((D.c * x * D.c⁻¹ : adjointGroup τ K) : ModGL τ K) := hte
    calc t = D.g0⁻¹ * (D.g0 * t * D.g0⁻¹) * D.g0 := by group
      _ = _ := by rw [hte']
  haveI : Finite E₀ := Nat.finite_of_card_ne_zero (by rw [hc]; norm_num)
  obtain ⟨x₀, hx₀P, y₀, hy₀P, hP⟩ := SeitzExcOpenRest3.exists_two_gen_of_card_sq' hp3 P hPc
    (fun x hx => hexpE x (hPE hx))
  obtain ⟨a, ha, haF⟩ := hdiag x₀ hx₀P
  obtain ⟨b, hb, hbF⟩ := hdiag y₀ hy₀P
  set C₀ : ModGL τ L := D.g0⁻¹ * φ D.c with hC₀
  have hC₀G : C₀ ∈ adjointGroup τ L := mul_mem (inv_mem D.hg0C) (hφG D.c)
  have hconj : ∀ x : adjointGroup τ K, D.g0⁻¹ * baseChangeGL ι
      ((D.c * x * D.c⁻¹ : adjointGroup τ K) : ModGL τ K) * D.g0 = C₀ * φ x * C₀⁻¹ := by
    intro x
    have e : baseChangeGL ι ((D.c * x * D.c⁻¹ : adjointGroup τ K) : ModGL τ K) =
        φ D.c * φ x * (φ D.c)⁻¹ := by
      rw [← map_inv, ← map_mul, ← map_mul]
      rfl
    rw [e, hC₀]
    group
  let a2 : Fin 2 → Fin τ.rank → Lˣ := ![a, b]
  let gens : Fin 2 → adjointGroup τ K := ![x₀, y₀]
  have ha2 : ∀ s, rootDiagUnit τ (a2 s) = C₀ * φ (gens s) * C₀⁻¹ := by
    intro s
    fin_cases s
    · exact ha.trans (hconj x₀)
    · exact hb.trans (hconj y₀)
  have ha2F : ∀ s, canonicalRep (coxeterSystem τ) L D.w *
      Units.map (entrywiseHom D.Fr) (rootDiagUnit τ (a2 s)) *
        (canonicalRep (coxeterSystem τ) L D.w)⁻¹ = rootDiagUnit τ (a2 s) := by
    intro s
    fin_cases s
    · exact haF
    · exact hbF
  have hgensP : ∀ s, gens s ∈ P := by
    intro s
    fin_cases s
    · exact hx₀P
    · exact hy₀P
  have hgensE : ∀ s, gens s ∈ E₀ := fun s => hPE (hgensP s)
  have hexpDiag : ∀ x ∈ E₀, ∀ a' : Fin τ.rank → Lˣ,
      rootDiagUnit τ a' = C₀ * φ x * C₀⁻¹ → ∀ i, a' i ^ 3 = 1 := by
    intro x hx a' ha'
    have h : rootDiagUnit τ (a' ^ 3) = rootDiagUnit τ 1 := by
      rw [rootDiagUnit_pow', rootDiagUnit_one, ha']
      exact conj_pow_eq_one' C₀ (by rw [← map_pow, hexpE x hx, map_one])
    intro i
    have := congrFun (CFSG.LieType.Chevalley.rootDiagUnit_injective h) i
    simpa using this
  have ha2p : ∀ s i, a2 s i ^ 3 = 1 := fun s => hexpDiag _ (hgensE s) _ (ha2 s)
  set A'' : Subgroup (ModGL τ L) := (E₀.map φ).map (MulAut.conj C₀).toMonoidHom with hA''
  have hA''mem : ∀ y ∈ A'', ∃ x ∈ E₀, y = C₀ * φ x * C₀⁻¹ := by
    rintro _ ⟨_, ⟨x, hx, rfl⟩, rfl⟩
    exact ⟨x, hx, rfl⟩
  have hA''C : A'' ≤ adjointGroup τ L := by
    intro y hy
    obtain ⟨x, -, rfl⟩ := hA''mem y hy
    exact mul_mem (mul_mem hC₀G (hφG x)) (inv_mem hC₀G)
  have hA''fin : (A'' : Set (ModGL τ L)).Finite := by
    have : Finite (E₀.map φ) := by
      haveI : Finite ↥E₀ := inferInstance
      exact Finite.of_surjective _ (Subgroup.equivMapOfInjective E₀ φ
        ((baseChangeGL_injective ι).comp Subtype.val_injective)).surjective
    exact Set.Finite.image _ (Set.toFinite _)
  have hA''a : ∀ y ∈ A'', ∀ s, rootDiagUnit τ (a2 s) * y = y * rootDiagUnit τ (a2 s) := by
    intro y hy s
    obtain ⟨x, hx, rfl⟩ := hA''mem y hy
    rw [ha2 s]
    have h := hcommE _ (hgensE s) x hx
    calc C₀ * φ (gens s) * C₀⁻¹ * (C₀ * φ x * C₀⁻¹) = C₀ * φ (gens s * x) * C₀⁻¹ := by
          rw [map_mul]; group
      _ = C₀ * φ (x * gens s) * C₀⁻¹ := by rw [h]
      _ = C₀ * φ x * C₀⁻¹ * (C₀ * φ (gens s) * C₀⁻¹) := by rw [map_mul]; group
  have hA''exp : ∀ y ∈ A'', y ^ 3 = 1 := by
    intro y hy
    obtain ⟨x, hx, rfl⟩ := hA''mem y hy
    refine conj_pow_eq_one' C₀ ?_
    rw [← map_pow, hexpE x hx, map_one]
  obtain ⟨z₂, hz₂, hz₂d, hz₂N⟩ :=
    SeitzExcOpenRest3.exists_conj_le_monomial_familyCentralizer_bar hℓ halg a2 hA''C hA''fin
      hA''a hA''exp
  have hzA'' : C₀ * φ z * C₀⁻¹ ∈ A'' := ⟨φ z, ⟨z, hz, rfl⟩, rfl⟩
  set n'' := z₂ * (C₀ * φ z * C₀⁻¹) * z₂⁻¹ with hn''
  have hn''N : n'' ∈ monomialSubgroup τ L := hz₂N _ hzA''
  have hz₂d' : ∀ s, rootDiagUnit τ (a2 s) * z₂⁻¹ = z₂⁻¹ * rootDiagUnit τ (a2 s) := by
    intro s
    calc rootDiagUnit τ (a2 s) * z₂⁻¹ =
          z₂⁻¹ * (z₂ * rootDiagUnit τ (a2 s)) * z₂⁻¹ := by group
      _ = z₂⁻¹ * (rootDiagUnit τ (a2 s) * z₂) * z₂⁻¹ := by rw [hz₂d s]
      _ = z₂⁻¹ * rootDiagUnit τ (a2 s) := by group
  have hn''a : ∀ s, rootDiagUnit τ (a2 s) * n'' = n'' * rootDiagUnit τ (a2 s) := by
    intro s
    have h1 := hA''a _ hzA'' s
    calc rootDiagUnit τ (a2 s) * n'' =
          (rootDiagUnit τ (a2 s) * z₂) * (C₀ * φ z * C₀⁻¹) * z₂⁻¹ := by rw [hn'']; group
      _ = z₂ * (rootDiagUnit τ (a2 s) * (C₀ * φ z * C₀⁻¹)) * z₂⁻¹ := by
          rw [hz₂d s]; group
      _ = z₂ * (C₀ * φ z * C₀⁻¹) * (rootDiagUnit τ (a2 s) * z₂⁻¹) := by rw [h1]; group
      _ = n'' * rootDiagUnit τ (a2 s) := by rw [hz₂d' s, hn'']; group
  have hn''p : n'' ^ 3 = 1 := conj_pow_eq_one' z₂ (hA''exp _ hzA'')
  obtain ⟨b', hb'⟩ := exists_eq_monomialElt hn''N
  set ω := weylQuotientHom τ L ⟨n'', hn''N⟩ with hωdef
  have hz₂C : z₂ ∈ familyCentralizer τ L a2 := by
    refine mem_familyCentralizer.2 ⟨hz₂, fun s => ?_⟩
    rw [hz₂d s]
    group
  have hconjw : ∀ s, rootDiagUnit τ (a2 s) = canonicalRep (coxeterSystem τ) L D.w *
      entrywiseFrobGL τ L (ringChar K) e (rootDiagUnit τ (a2 s)) *
        (canonicalRep (coxeterSystem τ) L D.w)⁻¹ := by
    intro s
    have h := ha2F s
    rw [hΦ] at h
    exact h.symm
  have hrel : ∀ s v, rootChar (a2 s) (D.w • v) = rootChar (a2 s) v ^ (ringChar K ^ e) :=
    fun s v => rootChar_frob_of_conj (a2 s) D.w (hconjw s) v
  have hSw : ∀ β ∈ familyKernel a2, D.w • β ∈ familyKernel a2 ∧ D.w⁻¹ • β ∈ familyKernel a2 :=
    fun β hβ => family_w_stab a2 hrel hβ
  have hwS : (fun β => D.w • β) '' familyKernel a2 = familyKernel a2 :=
    image_eq_of_mem_stab _ D.w (fun β hβ => (hSw β hβ).1) (fun β hβ => (hSw β hβ).2)
  have hΦι : ∀ y : ModGL τ K, Units.map (entrywiseHom D.Fr) (baseChangeGL ι y) =
      baseChangeGL ι y := CFSG.RankThree.PartOne.KE.baseChangeGL_frobenius_fixed D.Fr D.hFr
  have hΦC₀ : Units.map (entrywiseHom D.Fr) C₀ =
      (D.g0 * canonicalRep (coxeterSystem τ) L D.w)⁻¹ * φ D.c := by
    rw [hC₀, map_mul, map_inv, D.hg0]
    exact congrArg _ (hΦι _)
  set g : ModGL τ L := (z₂ * C₀)⁻¹ with hgdef
  have hνg : g⁻¹ * Units.map (entrywiseHom D.Fr) g = z₂ * canonicalRep (coxeterSystem τ) L D.w *
      (entrywiseFrobGL τ L (ringChar K) e z₂)⁻¹ := by
    rw [hgdef, inv_inv, map_inv, map_mul, hΦC₀, hΦ z₂, hC₀]
    group
  obtain ⟨m, hm, x, hx, hνmx⟩ :=
    mem_stabExt.1 (cocycle_mem_stabExt (ringChar K) a2 e hwS hz₂C)
  have hCx : ∀ s, (z₂ * C₀) * φ (gens s) * (z₂ * C₀)⁻¹ = rootDiagUnit τ (a2 s) := by
    intro s
    calc (z₂ * C₀) * φ (gens s) * (z₂ * C₀)⁻¹ = z₂ * (C₀ * φ (gens s) * C₀⁻¹) * z₂⁻¹ := by group
      _ = z₂ * rootDiagUnit τ (a2 s) * z₂⁻¹ := by rw [ha2 s]
      _ = rootDiagUnit τ (a2 s) := by rw [← hz₂d s]; group
  have hplane : ∀ p ∈ P, g⁻¹ * baseChangeGL ι (p : ModGL τ K) * g ∈
      Subgroup.closure (Set.range fun s => rootDiagUnit τ (a2 s)) := by
    intro p hp
    rw [hP] at hp
    have key : ∀ q ∈ Subgroup.closure ({x₀, y₀} : Set (adjointGroup τ K)),
        (z₂ * C₀) * φ q * (z₂ * C₀)⁻¹ ∈
          Subgroup.closure (Set.range fun s => rootDiagUnit τ (a2 s)) := by
      intro q hq
      induction hq using Subgroup.closure_induction with
      | mem q hq =>
        rcases hq with rfl | rfl
        · rw [show q = gens 0 from rfl, hCx 0]
          exact Subgroup.subset_closure ⟨0, rfl⟩
        · rw [show q = gens 1 from rfl, hCx 1]
          exact Subgroup.subset_closure ⟨1, rfl⟩
      | one =>
        rw [map_one]
        simp
      | mul q r _ _ hq hr =>
        rw [map_mul]
        have e : (z₂ * C₀) * (φ q * φ r) * (z₂ * C₀)⁻¹ =
            ((z₂ * C₀) * φ q * (z₂ * C₀)⁻¹) * ((z₂ * C₀) * φ r * (z₂ * C₀)⁻¹) := by group
        rw [e]
        exact mul_mem hq hr
      | inv q _ hq =>
        rw [map_inv]
        have e : (z₂ * C₀) * (φ q)⁻¹ * (z₂ * C₀)⁻¹ = ((z₂ * C₀) * φ q * (z₂ * C₀)⁻¹)⁻¹ := by
          group
        rw [e]
        exact inv_mem hq
    have e : g⁻¹ * baseChangeGL ι (p : ModGL τ K) * g = (z₂ * C₀) * φ p * (z₂ * C₀)⁻¹ := by
      rw [hgdef, inv_inv]
      rfl
    rw [e]
    exact key p hp
  have hkills : ∀ α, IsRoot τ α → D.Kills α → α ∈ familyKernel a2 := by
    intro α hα hk
    refine ⟨hα, fun s => ?_⟩
    obtain ⟨a', ha', hα'⟩ := hk (gens s) (hgensP s)
    have h1 : rootDiagUnit τ a' = rootDiagUnit τ (a2 s) := by
      rw [ha', ha2 s]
      exact hconj (gens s)
    have h2 : a' = a2 s := CFSG.LieType.Chevalley.rootDiagUnit_injective h1
    rw [← h2]
    exact hα'
  refine ⟨⟨a2, g, b', ω, m, x, ha2p, inv_mem (mul_mem hz₂ hC₀G), ?_,
    weylQuotientHom_pow_eq_one hn''N hn''p,
    fun s => weylQuotientHom_mem_rootCharStabilizer hn''N hn''a s, ?_, hm, hx, hplane, hkills⟩⟩
  · rw [← hb', hn'', hgdef]
    show _ = φ z
    group
  · have h : g⁻¹ * Units.map (entrywiseHom D.Fr) g =
        m * canonicalRep (coxeterSystem τ) L x := hνg.trans hνmx
    calc Units.map (entrywiseHom D.Fr) g = g * (g⁻¹ * Units.map (entrywiseHom D.Fr) g) := by group
      _ = _ := by rw [h]

theorem CubeFrame.commute_plane {P : Subgroup (adjointGroup τ K)} {D : LangPlaneData τ K P}
    {z : adjointGroup τ K} (F : CubeFrame D z) {u : ModGL τ (AlgebraicClosure K)}
    (hu : u ∈ familyGroup (K := AlgebraicClosure K) F.a) :
    ∀ p ∈ P, Commute u
      (F.g⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K)) (p : ModGL τ K) * F.g) := by
  intro p hp
  have hle : Subgroup.closure (Set.range fun s => rootDiagUnit τ (F.a s)) ≤
      Subgroup.centralizer {u} := by
    rw [Subgroup.closure_le]
    rintro _ ⟨s, rfl⟩
    rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff]
    exact (familyGroup_comm F.a s hu).symm
  exact (Subgroup.mem_centralizer_singleton_iff.1 (hle (F.plane p hp))).symm

theorem CubeFrame.exists_torus {P : Subgroup (adjointGroup τ K)} {D : LangPlaneData τ K P}
    {z : adjointGroup τ K} (F : CubeFrame D z) (hmon : MonomialToralAt τ 3)
    (hK3 : ¬ 3 ∣ Nat.card K) {E₀ : Subgroup (adjointGroup τ K)}
    (hE : E₀ ≤ P ⊔ Subgroup.zpowers z) (hz3 : z ^ 3 = 1)
    (hω : F.ω ∈ kernelWeylGroup (familyChar F.a)) :
    ∃ h ∈ adjointGroup τ (AlgebraicClosure K), ∀ x ∈ E₀,
      h⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K)) (x : ModGL τ K) * h ∈
        torusGroup τ (AlgebraicClosure K) := by
  classical
  set L := AlgebraicClosure K with hLdef
  set ι : K →+* L := algebraMap K L with hι
  set n : ModGL τ L := monomialElt τ L F.b F.ω with hn
  have hnN : n ∈ monomialSubgroup τ L := monomialElt_mem_monomialSubgroup F.b F.ω
  have hπ : weylQuotientHom τ L ⟨n, hnN⟩ = F.ω :=
    weylQuotientHom_torus_mul (rootDiagUnit_mem_torusGroup F.b) F.ω hnN
  have hgn : F.g⁻¹ * baseChangeGL ι (z : ModGL τ K) * F.g = n := by
    rw [← F.conj_z, hn]
    group <;> rfl
  have hn3 : n ^ 3 = 1 := by
    have hz3' : (z : ModGL τ K) ^ 3 = 1 := by rw [← Subgroup.coe_pow, hz3, Subgroup.coe_one]
    have h : baseChangeGL ι (z : ModGL τ K) ^ 3 = 1 := by rw [← map_pow, hz3', map_one]
    calc n ^ 3 = (F.g⁻¹ * baseChangeGL ι (z : ModGL τ K) * F.g) ^ 3 := by rw [hgn]
      _ = F.g⁻¹ * baseChangeGL ι (z : ModGL τ K) ^ 3 * F.g := by
          have := conj_pow (a := F.g⁻¹) (b := baseChangeGL ι (z : ModGL τ K)) (i := 3)
          rwa [inv_inv] at this
      _ = 1 := by rw [h]; group
  obtain ⟨h', hh', hh'd, hh'n⟩ := exists_conj_mem_torusGroup_of_weyl_mem_kernel hmon
    (ringChar_algebraicClosure_ne_three hK3) hnN hn3 (by rw [hπ]; exact hω)
  have hcentral : ∀ q ∈ Subgroup.closure (Set.range fun s => rootDiagUnit τ (F.a s)),
      h' * q * h'⁻¹ = q ∧ q ∈ torusGroup τ L := by
    intro q hq
    have hle : Subgroup.closure (Set.range fun s => rootDiagUnit τ (F.a s)) ≤
        Subgroup.centralizer {h'} := by
      rw [Subgroup.closure_le]
      rintro _ ⟨s, rfl⟩
      rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff]
      exact hh'd s
    have hle' : Subgroup.closure (Set.range fun s => rootDiagUnit τ (F.a s)) ≤ torusGroup τ L := by
      rw [Subgroup.closure_le]
      rintro _ ⟨s, rfl⟩
      exact rootDiagUnit_mem_torusGroup _
    refine ⟨?_, hle' hq⟩
    have := Subgroup.mem_centralizer_singleton_iff.1 (hle hq)
    rw [← this]
    group
  set S : Subgroup (adjointGroup τ K) :=
    (torusGroup τ L).comap ((MulAut.conj (F.g * h'⁻¹)⁻¹).toMonoidHom.comp
      ((baseChangeGL ι).comp (adjointGroup τ K).subtype)) with hS
  have hPS : P ≤ S := by
    intro p hp
    change (F.g * h'⁻¹)⁻¹ * baseChangeGL ι (p : ModGL τ K) * (F.g * h'⁻¹) ∈ torusGroup τ L
    have e : (F.g * h'⁻¹)⁻¹ * baseChangeGL ι (p : ModGL τ K) * (F.g * h'⁻¹) =
        h' * (F.g⁻¹ * baseChangeGL ι (p : ModGL τ K) * F.g) * h'⁻¹ := by group
    obtain ⟨h1, h2⟩ := hcentral _ (F.plane p hp)
    rw [e, h1]
    exact h2
  have hzS : z ∈ S := by
    change (F.g * h'⁻¹)⁻¹ * baseChangeGL ι (z : ModGL τ K) * (F.g * h'⁻¹) ∈ torusGroup τ L
    have e : (F.g * h'⁻¹)⁻¹ * baseChangeGL ι (z : ModGL τ K) * (F.g * h'⁻¹) =
        h' * (F.g⁻¹ * baseChangeGL ι (z : ModGL τ K) * F.g) * h'⁻¹ := by group
    rw [e, hgn]
    exact hh'n
  have hES : E₀ ≤ S := hE.trans (sup_le hPS ((Subgroup.zpowers_le).2 hzS))
  exact ⟨F.g * h'⁻¹, mul_mem F.g_mem (inv_mem hh'), fun x hx => hES hx⟩

end Frame

end CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.NonToralCore

end
