module

public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeInnerDefs
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeCenDefs
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeTwNotAll24Grp

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeInner

open CFSG.Open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Seitz
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.LieType.SeitzGeneration.ExcWideThree
  CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three

set_option linter.unusedSectionVars false

section Grp

variable {G : Type*} [Group G]

theorem e6Plane_pow_mod_three {x : G} (hx : x ^ 3 = 1) (k : ℕ) : x ^ k = x ^ (k % 3) := by
  conv_lhs => rw [← Nat.div_add_mod k 3, pow_add, pow_mul, hx, one_pow, one_mul]

theorem e6Plane_exists_pow_of_mem_zpowers {x y : G} (hx : x ^ 3 = 1)
    (hy : y ∈ Subgroup.zpowers x) : ∃ k : ℕ, y = x ^ k := by
  obtain ⟨z, rfl⟩ := Subgroup.mem_zpowers_iff.1 hy
  refine ⟨(z % 3).toNat, ?_⟩
  have h3 : x ^ (3 : ℤ) = 1 := by exact_mod_cast hx
  rw [← zpow_natCast, Int.toNat_of_nonneg (Int.emod_nonneg _ (by norm_num))]
  conv_lhs => rw [← Int.mul_ediv_add_emod z 3, zpow_add, zpow_mul, h3, one_zpow, one_mul]

theorem e6Plane_exists_pow_mul_pow {a b : G} (hab : Commute a b) (ha : a ^ 3 = 1)
    (hb : b ^ 3 = 1) {y : G} (hy : y ∈ Subgroup.zpowers a ⊔ Subgroup.zpowers b) :
    ∃ i j : ℕ, y = a ^ i * b ^ j := by
  have key : ∀ i j k l : ℕ, a ^ i * b ^ j * (a ^ k * b ^ l) = a ^ (i + k) * b ^ (j + l) := by
    intro i j k l
    have h := (hab.pow_pow k j).eq
    calc a ^ i * b ^ j * (a ^ k * b ^ l) = a ^ i * (b ^ j * a ^ k) * b ^ l := by
          simp only [mul_assoc]
      _ = a ^ i * (a ^ k * b ^ j) * b ^ l := by rw [h]
      _ = a ^ (i + k) * b ^ (j + l) := by
          rw [pow_add, pow_add]
          simp only [mul_assoc]
  let T : Subgroup G :=
    { carrier := {y | ∃ i j : ℕ, y = a ^ i * b ^ j}
      mul_mem' := by
        rintro _ _ ⟨i, j, rfl⟩ ⟨k, l, rfl⟩
        exact ⟨i + k, j + l, key i j k l⟩
      one_mem' := ⟨0, 0, by simp⟩
      inv_mem' := by
        rintro _ ⟨i, j, rfl⟩
        refine ⟨i * 2, j * 2, inv_eq_of_mul_eq_one_right ?_⟩
        rw [key]
        have e1 : a ^ (i + i * 2) = 1 := by
          rw [show i + i * 2 = 3 * i by ring, pow_mul, ha, one_pow]
        have e2 : b ^ (j + j * 2) = 1 := by
          rw [show j + j * 2 = 3 * j by ring, pow_mul, hb, one_pow]
        rw [e1, e2, one_mul] }
  have hle : Subgroup.zpowers a ⊔ Subgroup.zpowers b ≤ T :=
    sup_le (Subgroup.zpowers_le.2 ⟨1, 0, by simp⟩) (Subgroup.zpowers_le.2 ⟨0, 1, by simp⟩)
  exact hle hy

end Grp

section Weyl

theorem e6Plane_fixesForm_one (l : Fin Tag.E6.rank → ℤ) :
    FixesForm (1 : WeylGroup Tag.E6) l := fun β => by rw [one_smul]

theorem e6Plane_fixesForm_of_inv {w : WeylGroup Tag.E6} {l : Fin Tag.E6.rank → ℤ}
    (h : FixesForm w⁻¹ l) : FixesForm w l := fun β => by
  have := h (w • β)
  rw [inv_smul_smul] at this
  exact this.symm

theorem e6Plane_not_fixesForm_pow {w : WeylGroup Tag.E6} (hw : w ^ 3 = 1)
    (hell : ∀ l : Fin Tag.E6.rank → ℤ, l ≠ 0 → ¬ FixesForm w l) {j : ℕ} (hj : j % 3 ≠ 0) :
    ∀ l : Fin Tag.E6.rank → ℤ, l ≠ 0 → ¬ FixesForm (w ^ j) l := by
  intro l hl
  have hj' : j % 3 = 1 ∨ j % 3 = 2 := by omega
  rw [e6Plane_pow_mod_three hw]
  rcases hj' with h | h
  · rw [h, pow_one]
    exact hell l hl
  · rw [h]
    have h2 : w ^ 2 = w⁻¹ := eq_inv_of_mul_eq_one_left (by rw [← pow_succ]; exact hw)
    rw [h2]
    exact fun hf => hell l hl (e6Plane_fixesForm_of_inv hf)

end Weyl

section Transport


theorem e6Plane_bmMono_conj_line {K : Type} [Field K] (ω : Kˣ) :
    BmMono (MulAut.conj (e6LineElt ω)) 1 :=
  ⟨1, e6LineChar ω, by rw [OneMemClass.coe_one]; exact one_mem _,
    by rw [OneMemClass.coe_one]; exact mapsRootLines_one, by
      rw [map_one, one_mul, bm_conj_e6LineElt]⟩

theorem e6Plane_pow_three_of_conj {K : Type} [Field K] [Finite K] (s : adjointGroup Tag.E6 K)
    (h : MulAut.conj s ^ 3 = 1) : s ^ 3 = 1 :=
  conj_injective_of_center_eq_bot' (G := adjointGroup Tag.E6 K) center_adjointGroup_eq_bot
    (by rw [map_pow, h, map_one])

theorem e6Plane_finrank_inv {K : Type} [Field K] (s : adjointGroup Tag.E6 K) :
    Module.finrank K (LinearMap.ker
      ((((s⁻¹ : adjointGroup Tag.E6 K) : ModGL .E6 K) : Module.End K (RootModule .E6 K)) - 1)) =
    Module.finrank K (LinearMap.ker
      (((s : ModGL .E6 K) : Module.End K (RootModule .E6 K)) - 1)) := by
  have hker : LinearMap.ker
      ((((s⁻¹ : adjointGroup Tag.E6 K) : ModGL .E6 K) : Module.End K (RootModule .E6 K)) - 1) =
      LinearMap.ker (((s : ModGL .E6 K) : Module.End K (RootModule .E6 K)) - 1) := by
    rw [InvMemClass.coe_inv]
    generalize (s : ModGL .E6 K) = u
    ext x
    simp only [LinearMap.mem_ker, LinearMap.sub_apply, Module.End.one_apply, sub_eq_zero]
    constructor
    · intro h
      have h2 : (u : Module.End K (RootModule .E6 K))
          (((u⁻¹ : ModGL .E6 K) : Module.End K (RootModule .E6 K)) x) = x := by
        rw [← Module.End.mul_apply, Units.mul_inv, Module.End.one_apply]
      rw [h] at h2
      exact h2
    · intro h
      have h2 : ((u⁻¹ : ModGL .E6 K) : Module.End K (RootModule .E6 K))
          ((u : Module.End K (RootModule .E6 K)) x) = x := by
        rw [← Module.End.mul_apply, Units.inv_mul, Module.End.one_apply]
      rw [h] at h2
      exact h2
  rw [hker]

theorem e6Plane_cube_map {K : Type} [Field K] [Finite K] (φ : MulAut (adjointGroup Tag.E6 K))
    {E : Subgroup (MulAut (adjointGroup Tag.E6 K))} (hE : IsElemAbelian 3 E)
    (hEc : Nat.card E = 3 ^ 3) (hEi : E ≤ CFSG.Fischer.innerAut (adjointGroup Tag.E6 K))
    (hER : ¬ E6NormalizesR K E) :
    IsElemAbelian 3 (E.map (MulAut.congr φ).toMonoidHom) ∧
      Nat.card (E.map (MulAut.congr φ).toMonoidHom) = 3 ^ 3 ∧
      E.map (MulAut.congr φ).toMonoidHom ≤ CFSG.Fischer.innerAut (adjointGroup Tag.E6 K) ∧
      ¬ E6NormalizesR K (E.map (MulAut.congr φ).toMonoidHom) := by
  refine ⟨hE.map _, ?_, ?_, fun h => hER (e6NormalizesR_of_map_congr φ h)⟩
  · rw [Subgroup.card_map_of_injective (MulAut.congr φ).injective, hEc]
  · rintro _ ⟨ε, hε, rfl⟩
    obtain ⟨s, rfl⟩ := CFSG.Fischer.mem_innerAut.1 (hEi hε)
    rw [congr_toMonoidHom_apply, e6Cen_mul_conj_mul_inv]
    exact CFSG.Fischer.mem_innerAut.2 ⟨_, rfl⟩

theorem e6Plane_map {K : Type} [Field K] [Finite K] {φ : MulAut (adjointGroup Tag.E6 K)}
    (hφ : φ ∈ e6Inndiag K) {E : Subgroup (MulAut (adjointGroup Tag.E6 K))}
    (h : ∃ P ≤ E.map (MulAut.congr φ).toMonoidHom, Nat.card P = 3 ^ 2 ∧
      ∀ s : adjointGroup Tag.E6 K, MulAut.conj s ∈ P → s ≠ 1 →
        Module.finrank K (LinearMap.ker
          (((s : ModGL .E6 K) : Module.End K (RootModule .E6 K)) - 1)) = 24) :
    ∃ P ≤ E, Nat.card P = 3 ^ 2 ∧ ∀ s : adjointGroup Tag.E6 K, MulAut.conj s ∈ P → s ≠ 1 →
      Module.finrank K (LinearMap.ker
        (((s : ModGL .E6 K) : Module.End K (RootModule .E6 K)) - 1)) = 24 := by
  obtain ⟨P, hPE, hPc, hP⟩ := h
  refine ⟨P.map (MulAut.congr φ⁻¹).toMonoidHom, fun ε hε => ?_, ?_, fun s hs hs1 => ?_⟩
  · have h1 := (e6Cen_mem_map_congr (φ⁻¹) (E := P)).1 hε
    have h2 := (e6Cen_mem_map_congr φ).1 (hPE h1)
    simpa [mul_assoc] using h2
  · rw [Subgroup.card_map_of_injective (MulAut.congr φ⁻¹).injective, hPc]
  · have hs' := (e6Cen_mem_map_congr (φ⁻¹) (E := P)).1 hs
    rw [inv_inv, e6Cen_mul_conj_mul_inv] at hs'
    have h2 : φ s ≠ 1 := fun h' => hs1 (φ.injective (h'.trans (map_one φ).symm))
    rw [← e6Cen_finrank_apply hφ s]
    exact hP (φ s) hs' h2

end Transport

section Plane


theorem e6Plane_exists_elliptic (hFix : E6MonoFixNormalizes) (hWeyl : E6WeylEllipticOfNoFixed)
    {K : Type} [Field K] [Finite K] (hK : 3 ∣ Nat.card K - 1)
    {E : Subgroup (MulAut (adjointGroup Tag.E6 K))} (hE : IsElemAbelian 3 E)
    (hER : ¬ E6NormalizesR K E) (hmono : ∀ X ∈ E, ∃ v, BmMono X v) :
    ∃ X ∈ E, ∃ w, BmMono X w ∧ ∀ l : Fin Tag.E6.rank → ℤ, l ≠ 0 → ¬ FixesForm w l := by
  have hK4 : 4 ≤ Nat.card K := e6Cen_four_le_card hK
  have hnofix : ∀ l : Fin Tag.E6.rank → ℤ, l ≠ 0 → ∃ w ∈ e6CenImage E, ¬ FixesForm w l := by
    intro l hl
    by_contra hall
    push Not at hall
    refine hER (hFix K E l hl fun X hX => ?_)
    obtain ⟨v, hv⟩ := hmono X hX
    exact ⟨v, hv, hall v ⟨X, hX, hv⟩⟩
  obtain ⟨w, ⟨X, hX, hXw⟩, hw⟩ := hWeyl (e6CenImage E)
    (fun w hw => e6CenImage_pow_three hK4 hE hw)
    (fun w hw u hu => e6CenImage_mul_comm hK4 hE hw hu) hnofix
  exact ⟨X, hX, w, hXw, hw⟩

theorem e6Plane_of_elliptic (hF24 : E6MonoEllipticFix24) (hWit : E6ThreeA2WitnessStmt)
    {K : Type} [Field K] [Finite K] (hK3 : ringChar K ≠ 3) (hK : 3 ∣ Nat.card K - 1)
    {ω : Kˣ} (h3 : ω ^ 3 = 1) (h1 : ω ≠ 1)
    {E : Subgroup (MulAut (adjointGroup Tag.E6 K))} (hE : IsElemAbelian 3 E)
    (hσ : MulAut.conj (e6LineElt ω) ∈ E) {X : MulAut (adjointGroup Tag.E6 K)} (hX : X ∈ E)
    {w : WeylGroup Tag.E6} (hXw : BmMono X w)
    (hell : ∀ l : Fin Tag.E6.rank → ℤ, l ≠ 0 → ¬ FixesForm w l) :
    ∃ P ≤ E, Nat.card P = 3 ^ 2 ∧ ∀ s : adjointGroup Tag.E6 K, MulAut.conj s ∈ P → s ≠ 1 →
      Module.finrank K (LinearMap.ker
        (((s : ModGL .E6 K) : Module.End K (RootModule .E6 K)) - 1)) = 24 := by
  classical
  have hK4 : 4 ≤ Nat.card K := e6Cen_four_le_card hK
  have hinj := conj_injective_of_center_eq_bot' (G := adjointGroup Tag.E6 K)
    center_adjointGroup_eq_bot
  have hσ1 : MulAut.conj (e6LineElt ω) ≠ 1 := bm_ch_ne_one h1
  have hσ3 : MulAut.conj (e6LineElt ω) ^ 3 = 1 := hE.2 _ hσ
  have hh3 : e6LineElt ω ^ 3 = 1 := hinj (by rw [map_pow, hσ3, map_one])
  have hX3 : X ^ 3 = 1 := hE.2 X hX
  have hcomm : Commute (MulAut.conj (e6LineElt ω)) X :=
    congrArg Subtype.val (hE.1.is_comm.comm (⟨_, hσ⟩ : E) ⟨X, hX⟩)
  have hw3 : w ^ 3 = 1 := by
    have h := hXw.pow 3
    rw [hX3] at h
    exact (BmMono.unique hK4 bmMono_one h).symm
  have hwne : w ≠ 1 := by
    rintro rfl
    exact hell (Pi.single e6KacNode 1) (fun h => by simpa using congrFun h e6KacNode)
      (e6Plane_fixesForm_one _)
  have hnzp : X ∉ Subgroup.zpowers (MulAut.conj (e6LineElt ω)) := by
    intro hmem
    obtain ⟨k, hk⟩ := e6Plane_exists_pow_of_mem_zpowers hσ3 hmem
    have h' : BmMono X (1 ^ k) := by
      rw [hk]
      exact (e6Plane_bmMono_conj_line ω).pow k
    exact hwne ((BmMono.unique hK4 hXw h').trans (one_pow k))
  have hPE : Subgroup.zpowers (MulAut.conj (e6LineElt ω)) ⊔ Subgroup.zpowers X ≤ E :=
    sup_le (Subgroup.zpowers_le.2 hσ) (Subgroup.zpowers_le.2 hX)
  refine ⟨Subgroup.zpowers (MulAut.conj (e6LineElt ω)) ⊔ Subgroup.zpowers X, hPE,
    KSNotAll24.card_zpowers_sup_zpowers hcomm hσ1 hσ3 hX3 hnzp, ?_⟩
  intro s hs hs1
  have hs3 : s ^ 3 = 1 := e6Plane_pow_three_of_conj s (hE.2 _ (hPE hs))
  obtain ⟨i, j, hij⟩ := e6Plane_exists_pow_mul_pow hcomm hσ3 hX3 hs
  by_cases hj : j % 3 = 0
  ·
    have hXj : X ^ j = 1 := by rw [e6Plane_pow_mod_three hX3, hj, pow_zero]
    have hsi : s = e6LineElt ω ^ i := by
      apply hinj
      rw [map_pow, hij, hXj, mul_one]
    rw [e6Plane_pow_mod_three hh3] at hsi
    have hi : i % 3 = 1 ∨ i % 3 = 2 := by
      by_contra hc
      have h0 : i % 3 = 0 := by omega
      rw [h0, pow_zero] at hsi
      exact hs1 hsi
    have hdim0 := hWit K ω h3 h1
    rcases hi with hi | hi
    · rw [hi, pow_one] at hsi
      rw [hsi]
      exact hdim0
    · rw [hi] at hsi
      have h2 : e6LineElt ω ^ 2 = (e6LineElt ω)⁻¹ :=
        eq_inv_of_mul_eq_one_left (by rw [← pow_succ]; exact hh3)
      rw [hsi, h2, e6Plane_finrank_inv]
      exact hdim0
  ·
    have hBm : BmMono (MulAut.conj s) (w ^ j) := by
      have h := ((e6Plane_bmMono_conj_line ω).pow i).mul (hXw.pow j)
      rw [one_pow, one_mul] at h
      rw [hij]
      exact h
    exact hF24 K hK3 hK s hs3 (w ^ j) hBm (e6Plane_not_fixesForm_pow hw3 hell hj)

theorem e6Plane_of_line (hLine : E6InnerSylowMonoLine) (hFix : E6MonoFixNormalizes)
    (hWeyl : E6WeylEllipticOfNoFixed) (hF24 : E6MonoEllipticFix24) (hWit : E6ThreeA2WitnessStmt)
    {K : Type} [Field K] [Finite K] (hK3 : ringChar K ≠ 3) (hK : 3 ∣ Nat.card K - 1)
    {ω : Kˣ} (h3 : ω ^ 3 = 1) (h1 : ω ≠ 1)
    {E : Subgroup (MulAut (adjointGroup Tag.E6 K))} (hE : IsElemAbelian 3 E)
    (hEc : Nat.card E = 3 ^ 3) (hEi : E ≤ CFSG.Fischer.innerAut (adjointGroup Tag.E6 K))
    (hER : ¬ E6NormalizesR K E) (hσ : MulAut.conj (e6LineElt ω) ∈ E) :
    ∃ P ≤ E, Nat.card P = 3 ^ 2 ∧ ∀ s : adjointGroup Tag.E6 K, MulAut.conj s ∈ P → s ≠ 1 →
      Module.finrank K (LinearMap.ker
        (((s : ModGL .E6 K) : Module.End K (RootModule .E6 K)) - 1)) = 24 := by
  have hcomm : ∀ X ∈ E, Commute X (MulAut.conj (e6LineElt ω)) := fun X hX =>
    congrArg Subtype.val (hE.1.is_comm.comm (⟨X, hX⟩ : E) ⟨_, hσ⟩)
  obtain ⟨φ, hφ, hφc, hmono⟩ := hLine K hK3 hK ω h3 h1 E (hEi.trans (innerAut_le_e6Inndiag K))
    (CFSG.Open.IsElemAbelian.isPGroup hE) hcomm
  refine e6Plane_map hφ ?_
  obtain ⟨hE', -, -, hER'⟩ := e6Plane_cube_map φ hE hEc hEi hER
  obtain ⟨X, hX, w, hXw, hell⟩ := e6Plane_exists_elliptic hFix hWeyl hK hE' hER' hmono
  have hσ' : MulAut.conj (e6LineElt ω) ∈ E.map (MulAut.congr φ).toMonoidHom :=
    ⟨_, hσ, by rw [congr_toMonoidHom_apply, hφc.eq, mul_inv_cancel_right]⟩
  exact e6Plane_of_elliptic hF24 hWit hK3 hK h3 h1 hE' hσ' hX hXw hell

theorem e6Plane_of_mono (hLine : E6InnerSylowMonoLine) (hFix : E6MonoFixNormalizes)
    (hWeyl : E6WeylEllipticOfNoFixed) (hF24 : E6MonoEllipticFix24) (hS3 : E6ThreeA2ConjStmt)
    (hWit : E6ThreeA2WitnessStmt) {K : Type} [Field K] [Finite K] (hK3 : ringChar K ≠ 3)
    (hK : 3 ∣ Nat.card K - 1) {E : Subgroup (MulAut (adjointGroup Tag.E6 K))}
    (hE : IsElemAbelian 3 E) (hEc : Nat.card E = 3 ^ 3)
    (hEi : E ≤ CFSG.Fischer.innerAut (adjointGroup Tag.E6 K)) (hER : ¬ E6NormalizesR K E)
    (hmono : ∀ X ∈ E, ∃ v, BmMono X v) :
    ∃ P ≤ E, Nat.card P = 3 ^ 2 ∧ ∀ s : adjointGroup Tag.E6 K, MulAut.conj s ∈ P → s ≠ 1 →
      Module.finrank K (LinearMap.ker
        (((s : ModGL .E6 K) : Module.End K (RootModule .E6 K)) - 1)) = 24 := by
  obtain ⟨ω, h3, h1⟩ := e6Line_exists_cube_root_unit hK
  obtain ⟨X, hX, w, hXw, hell⟩ := e6Plane_exists_elliptic hFix hWeyl hK hE hER hmono
  obtain ⟨s, rfl⟩ := CFSG.Fischer.mem_innerAut.1 (hEi hX)
  have hs3 : s ^ 3 = 1 := e6Plane_pow_three_of_conj s (hE.2 _ hX)
  have hdim := hF24 K hK3 hK s hs3 w hXw hell
  obtain ⟨g, hgC, hg⟩ := hS3 K ω h3 h1 (s : ModGL .E6 K) s.2
    (by have := congrArg Subtype.val hs3; simpa using this) hdim
  obtain ⟨g', hg'⟩ : ∃ g' : adjointGroup Tag.E6 K, (g' : ModGL .E6 K) = g := ⟨⟨g, hgC⟩, rfl⟩
  have hgs : g' * s * g'⁻¹ = e6LineElt ω := by
    apply Subtype.ext
    rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, hg', coe_e6LineElt]
    exact hg
  refine e6Plane_map (φ := MulAut.conj g') (innerAut_le_e6Inndiag K ⟨g', rfl⟩) ?_
  obtain ⟨hE', hEc', hEi', hER'⟩ := e6Plane_cube_map (MulAut.conj g') hE hEc hEi hER
  have hσ : MulAut.conj (e6LineElt ω) ∈ E.map (MulAut.congr (MulAut.conj g')).toMonoidHom :=
    ⟨_, hX, by rw [congr_toMonoidHom_apply, ← hgs, map_mul, map_mul, map_inv]⟩
  exact e6Plane_of_line hLine hFix hWeyl hF24 hWit hK3 hK h3 h1 hE' hEc' hEi' hER' hσ

theorem e6InnerAll24Plane_of_pieces (hSyl : E6InnerSylowMono) (hLine : E6InnerSylowMonoLine)
    (hFix : E6MonoFixNormalizes) (hWeyl : E6WeylEllipticOfNoFixed) (hF24 : E6MonoEllipticFix24)
    (hS3 : E6ThreeA2ConjStmt) (hWit : E6ThreeA2WitnessStmt) : E6InnerAll24Plane := by
  intro K _ _ hK3 hK _ E hE hEc hEi hER
  obtain ⟨φ, hφ, hmono⟩ := hSyl K hK3 hK E (hEi.trans (innerAut_le_e6Inndiag K))
    (CFSG.Open.IsElemAbelian.isPGroup hE)
  refine e6Plane_map hφ ?_
  obtain ⟨hE', hEc', hEi', hER'⟩ := e6Plane_cube_map φ hE hEc hEi hER
  exact e6Plane_of_mono hLine hFix hWeyl hF24 hS3 hWit hK3 hK hE' hEc' hEi' hER' hmono

end Plane

end CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeInner
