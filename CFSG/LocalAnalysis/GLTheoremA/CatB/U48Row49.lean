module

public import CFSG.LocalAnalysis.GLTheoremA.CatB.U48Row40
public import CFSG.LocalAnalysis.GLTheoremA.CatB.U48Dict
public import CFSG.LocalAnalysis.GLTheoremA.CatB.YS09U42E27
public import CFSG.LocalAnalysis.GLTheoremA.CatB.YS09U42T
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFacts.A6.PSp43.ThreeC
public import Certificates.Kernel.ThCent.Leaves
public import CFSG.Sporadic.ThSchreier.AutCore

public section

namespace CFSG.LocalAnalysis.GLTheoremA.CatB.U48

open Matrix CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.LocalAnalysis.GLTheoremA CFSG.LocalAnalysis.GLTheoremA.CatB
open CFSG.LocalAnalysis.GLTheoremA.S10
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open CFSG.RankThree.PartTwo.Sec4.Item434SmallTwoIVU48
open CFSG.RankThree.PartTwo.KFacts.KS21 (torusExt pow_mul_tau card_torusExt)
open CFSG.RankThree.PartTwo.KFacts.KS21.DFT (rot3 rot3_fixed rot3_ne powVec powVec_apply)
open CFSG.RankThree.PartTwo.KFacts.KS21.U58 (K ζ9 ζ9_pow_nine)
open CFSG.LocalAnalysis.RankThreeTheoremC.A6.PSp43 (factorization_three_25920)

noncomputable section

namespace Row49

@[expose] def dz : ZMod 3 →+ ZMod 9 :=
  AddMonoidHom.mk' (fun x : ZMod 3 => ((3 * x.val : ℕ) : ZMod 9)) (by decide)

theorem dz_val : ∀ x : ZMod 3, (dz x).val = 3 * x.val := by decide

@[expose] def tau3 : Multiplicative (Fin 3 → ZMod 3) →* SU4 :=
  tau4.comp (AddMonoidHom.toMultiplicative (AddMonoidHom.compLeft dz (Fin 3)))

theorem tau3_apply (v : Fin 3 → ZMod 3) :
    tau3 (.ofAdd v) = tau4 (.ofAdd (fun i => dz (v i))) := rfl

theorem tau3_injective : Function.Injective tau3 := by
  intro a b h
  have hv : (fun i => dz (a.toAdd i)) = fun i => dz (b.toAdd i) :=
    Multiplicative.ofAdd.injective (tau4_injective h)
  refine Multiplicative.toAdd.injective (funext fun i => ?_)
  have h2 := congrArg ZMod.val (congrFun hv i)
  rw [dz_val, dz_val] at h2
  exact ZMod.val_injective _ (by omega)

theorem w4_mul_tau3 (v : Fin 3 → ZMod 3) :
    w4 * tau3 (.ofAdd v) = tau3 (.ofAdd (rot3 v)) * w4 := by
  have h := w4_mul_tau4 (fun i => dz (v i))
  have h2 : (fun i => dz (rot3 v i)) = rot3 (fun i => dz (v i)) := by
    funext i; fin_cases i <;> rfl
  rw [tau3_apply, tau3_apply, h2]
  exact h

theorem tau3_eq_torus (v : Fin 3 → ZMod 3) :
    tau3 (.ofAdd v) = CFSG.RankThree.PartTwo.Sec4.Item434SmallTwoIVU48.torusSU4
      (fun i => ⟨ζ9 ^ (3 * (v i).val), by
        rw [mem_rootsOfUnity, ← pow_mul, show 3 * (v i).val * 3 = 9 * (v i).val by ring, pow_mul,
          ζ9_pow_nine, one_pow]⟩) := by
  apply Subtype.ext
  apply Units.ext
  rw [tau3_apply, coe_tau4, coe_torusSU4]
  have h : powVec ζ9 ζ9_pow_nine (.ofAdd fun i => dz (v i)) =
      fun i => ((⟨ζ9 ^ (3 * (v i).val), by
        rw [mem_rootsOfUnity, ← pow_mul, show 3 * (v i).val * 3 = 9 * (v i).val by ring, pow_mul,
          ζ9_pow_nine, one_pow]⟩ : μ3) : Kˣ) := by
    funext i
    rw [powVec_apply, dz_val]
  rw [h]

theorem tau3_mem_Dstd (v : Fin 3 → ZMod 3) : tau3 (.ofAdd v) ∈ Dstd := ⟨_, (tau3_eq_torus v).symm⟩

theorem fieldSU4_w4 (φ : K ≃+* K) : fieldSU4 φ w4 = w4 := by
  apply Subtype.ext
  apply Units.ext
  rw [coe_fieldSU4, coe_glAut]
  change ((TauCeti.permutationGL (k := K) c4 : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K).map φ =
    ((TauCeti.permutationGL (k := K) c4 : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K)
  ext i j
  simp [TauCeti.permutationGL_coe, Equiv.Perm.permMatrix, PEquiv.toMatrix_apply, apply_ite φ]

abbrev R₃ : Subgroup SU4 := torusExt (rot3 (R := ZMod 3)) tau3 w4 w4_pow_three w4_mul_tau3

theorem card_R₃ : Nat.card R₃ = 81 := by
  haveI : Fact (1 < 3) := ⟨by norm_num⟩
  rw [card_torusExt tau3_injective w4_pow_three w4_mul_tau3 rot3_ne, Nat.card_fun, Nat.card_fin,
    Nat.card_zmod]
  norm_num

theorem R₃_le_fixSub {φ : K ≃+* K} (hφ3 : φ ^ 3 = 1) : R₃ ≤ fixSub (fieldSU4 φ) := by
  rintro _ ⟨v, j, rfl⟩
  show fieldSU4 φ (tau3 (.ofAdd v) * w4 ^ j) = tau3 (.ofAdd v) * w4 ^ j
  rw [map_mul, map_pow, fieldSU4_apply_of_mem_Dstd hφ3 (tau3_mem_Dstd v), fieldSU4_w4]

theorem tau3_mem_R₃ (v : Fin 3 → ZMod 3) : tau3 (.ofAdd v) ∈ R₃ :=
  ⟨v, 0, by rw [pow_zero, mul_one]⟩

theorem w4_mem_R₃ : w4 ∈ R₃ := ⟨0, 1, by rw [ofAdd_zero, map_one, one_mul, pow_one]⟩

theorem central_R₃ {z : SU4} (hz : z ∈ R₃) (hc : ∀ q ∈ R₃, q * z = z * q) :
    ∃ a : ZMod 9, z = tau4 (.ofAdd fun _ => a) := by
  haveI : Fact (1 < 3) := ⟨by norm_num⟩
  obtain ⟨v, j, rfl⟩ := hz
  obtain ⟨r, hr, hzr⟩ : ∃ r < 3, tau3 (.ofAdd v) * w4 ^ j = tau3 (.ofAdd v) * w4 ^ r :=
    ⟨j % 3, Nat.mod_lt _ (by norm_num), by rw [← pow_eq_pow_mod j w4_pow_three]⟩
  rw [hzr] at hc ⊢
  have hr0 : r = 0 := by
    obtain ⟨u, hu⟩ := rot3_ne (R := ZMod 3)
    have h := hc (tau3 (.ofAdd u)) (tau3_mem_R₃ u)
    have hp := pow_mul_tau (σ := rot3 (R := ZMod 3)) (τ := tau3) (w := w4) w4_mul_tau3 r u
    have h4 : tau3 (.ofAdd u) * tau3 (.ofAdd v) = tau3 (.ofAdd v) * tau3 (.ofAdd u) := by
      rw [← map_mul tau3, ← map_mul tau3]
      exact congrArg tau3 (mul_comm _ _)
    have h2 : tau3 (.ofAdd u) * tau3 (.ofAdd v) * w4 ^ r =
        tau3 (.ofAdd v) * tau3 (.ofAdd ((rot3 (R := ZMod 3))^[r] u)) * w4 ^ r := by
      calc tau3 (.ofAdd u) * tau3 (.ofAdd v) * w4 ^ r
          = tau3 (.ofAdd u) * (tau3 (.ofAdd v) * w4 ^ r) := by rw [mul_assoc]
        _ = tau3 (.ofAdd v) * (w4 ^ r * tau3 (.ofAdd u)) := by rw [h, mul_assoc]
        _ = tau3 (.ofAdd v) * tau3 (.ofAdd ((rot3 (R := ZMod 3))^[r] u)) * w4 ^ r := by
          rw [hp, mul_assoc]
    rw [h4, mul_left_inj, mul_right_inj] at h2
    have h1 : (rot3 (R := ZMod 3))^[r] u = u :=
      (Multiplicative.ofAdd.injective (tau3_injective h2)).symm
    by_contra hne
    have h3 : ∀ w : Fin 3 → ZMod 3, rot3 (rot3 (rot3 w)) = w := fun w => by
      funext i; fin_cases i <;> rfl
    rcases (by omega : r = 1 ∨ r = 2) with rfl | rfl
    · exact hu h1
    · exact hu ((h3 u).symm.trans (congrArg rot3 h1)).symm
  subst hr0
  simp only [pow_zero, mul_one] at hc ⊢
  have hv : rot3 v = v := by
    have h := hc w4 w4_mem_R₃
    rw [w4_mul_tau3] at h
    exact Multiplicative.ofAdd.injective (tau3_injective (mul_right_cancel h))
  obtain ⟨a, rfl⟩ : ∃ a, v = fun _ => a := ⟨v 0, rot3_fixed hv⟩
  exact ⟨dz a, rfl⟩

theorem tau4_const_central (a : ZMod 9) :
    ∀ q ∈ P₀, q * tau4 (.ofAdd fun _ => a) = tau4 (.ofAdd fun _ => a) * q := by
  rintro _ ⟨u, j, rfl⟩
  have hw : Commute (tau4 (.ofAdd fun _ => a)) w4 := by
    have h := w4_mul_tau4 (fun _ => a)
    have : rot3 (fun _ : Fin 3 => a) = fun _ => a := by funext i; fin_cases i <;> rfl
    rw [this] at h
    exact h.symm
  calc tau4 (.ofAdd u) * w4 ^ j * tau4 (.ofAdd fun _ => a)
      = tau4 (.ofAdd u) * ((w4 ^ j) * tau4 (.ofAdd fun _ => a)) := by rw [mul_assoc]
    _ = tau4 (.ofAdd u) * (tau4 (.ofAdd fun _ => a) * w4 ^ j) := by rw [(hw.pow_right j).eq]
    _ = (tau4 (.ofAdd fun _ => a) * tau4 (.ofAdd u)) * w4 ^ j := by rw [← mul_assoc, tau4_comm]
    _ = tau4 (.ofAdd fun _ => a) * (tau4 (.ofAdd u) * w4 ^ j) := by rw [mul_assoc]

theorem exists_sylow_of_conj (g z : SU4) (hz : g * z * g⁻¹ ∈ P₀)
    (hc : ∀ q ∈ P₀, q * (g * z * g⁻¹) = (g * z * g⁻¹) * q) :
    ∃ Q : Sylow 3 SU4, z ∈ (Q : Subgroup SU4) ∧ ∀ q ∈ (Q : Subgroup SU4), q * z = z * q := by
  obtain ⟨P, hP⟩ := exists_sylow_P₀
  obtain ⟨Q, hg⟩ : ∃ Q : Sylow 3 SU4, g • Q = P := ⟨g⁻¹ • P, smul_inv_smul g P⟩
  have key : ∀ x, x ∈ (Q : Subgroup SU4) ↔ g * x * g⁻¹ ∈ P₀ := by
    intro x
    rw [← hP, ← hg, Sylow.coe_subgroup_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem]
    have : (MulAut.conj g)⁻¹ • (g * x * g⁻¹) = x := by simp [MulAut.smul_def, mul_assoc]
    rw [this]
  refine ⟨Q, (key z).2 hz, fun q hq => ?_⟩
  have h1 := hc (g * q * g⁻¹) ((key q).1 hq)
  calc q * z = g⁻¹ * ((g * q * g⁻¹) * (g * z * g⁻¹)) * g := by group
    _ = g⁻¹ * ((g * z * g⁻¹) * (g * q * g⁻¹)) * g := by rw [h1]
    _ = z * q := by group

theorem exists_sylow_central {α : MulAut SU4} (hα3 : α ^ 3 = 1) (hα1 : fieldFactor4 α ≠ 1)
    (hcard : Nat.card (fixSub α) = 25920) {S : Subgroup SU4} (hSF : S ≤ fixSub α)
    (hS : Nat.card S = 81) {z : SU4} (hzS : z ∈ S) (hzc : ∀ q ∈ S, q * z = z * q) :
    ∃ Q : Sylow 3 SU4, z ∈ (Q : Subgroup SU4) ∧ ∀ q ∈ (Q : Subgroup SU4), q * z = z * q := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨h, hh⟩ := exists_conj_fieldSU4 hα3 hα1
  have hφ3 : fieldFactor4 α ^ 3 = 1 := by rw [← map_pow, hα3, map_one]
  set F := fixSub α with hF
  set R : Subgroup SU4 := R₃.map (MulAut.conj h).toMonoidHom with hR
  have hRF : R ≤ F := by
    rintro _ ⟨r, hr, rfl⟩
    show α (h * r * h⁻¹) = h * r * h⁻¹
    rw [hh r, show fieldSU4 (fieldFactor4 α) r = r from R₃_le_fixSub hφ3 hr]
  have h81 : (3 : ℕ) ^ (Nat.card F).factorization 3 = 81 := by
    rw [hcard, factorization_three_25920]; norm_num
  let SR : Sylow 3 ↥F := Sylow.ofCard (R.subgroupOf F) (by
    rw [h81, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hRF).toEquiv,
      Subgroup.card_map_of_injective (MulAut.conj h).injective, card_R₃])
  let SS : Sylow 3 ↥F := Sylow.ofCard (S.subgroupOf F)
    (by rw [h81, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hSF).toEquiv, hS])
  obtain ⟨f, hf⟩ := MulAction.exists_smul_eq ↥F SS SR
  have hSR : (SR : Subgroup ↥F) = R.subgroupOf F := rfl
  have hSS : (SS : Subgroup ↥F) = S.subgroupOf F := rfl
  have key : ∀ x : ↥F, x ∈ R.subgroupOf F ↔ f⁻¹ * x * f ∈ S.subgroupOf F := by
    intro x
    rw [← hSR, ← hSS, ← hf, Sylow.coe_subgroup_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem]
    have : (MulAut.conj f)⁻¹ • x = f⁻¹ * x * f := by simp [MulAut.smul_def, mul_assoc]
    rw [this]
  set g : SU4 := h⁻¹ * (f : SU4) with hg
  have hz' : g * z * g⁻¹ ∈ R₃ := by
    have h1 := (key (f * ⟨z, hSF hzS⟩ * f⁻¹)).2 (by
      rw [show f⁻¹ * (f * (⟨z, hSF hzS⟩ : ↥F) * f⁻¹) * f = ⟨z, hSF hzS⟩ by group]
      exact Subgroup.mem_subgroupOf.2 hzS)
    obtain ⟨r, hr, hrz⟩ := Subgroup.mem_subgroupOf.1 h1
    have : g * z * g⁻¹ = r := by
      have h2 : h * r * h⁻¹ = (f : SU4) * z * (f : SU4)⁻¹ := hrz
      rw [hg]
      calc h⁻¹ * (f : SU4) * z * (h⁻¹ * (f : SU4))⁻¹
          = h⁻¹ * ((f : SU4) * z * (f : SU4)⁻¹) * h := by group
        _ = r := by rw [← h2]; group
    rwa [this]
  have hc' : ∀ q ∈ R₃, q * (g * z * g⁻¹) = (g * z * g⁻¹) * q := by
    intro q hq
    have hqR : h * q * h⁻¹ ∈ R := ⟨q, hq, rfl⟩
    have h1 := (key ⟨_, hRF hqR⟩).1 (Subgroup.mem_subgroupOf.2 hqR)
    have h3 := hzc _ (Subgroup.mem_subgroupOf.1 h1)
    simp only [Subgroup.coe_mul, Subgroup.coe_inv] at h3
    calc q * (g * z * g⁻¹) = g * (((f : SU4)⁻¹ * (h * q * h⁻¹) * f) * z) * g⁻¹ := by rw [hg]; group
      _ = g * (z * ((f : SU4)⁻¹ * (h * q * h⁻¹) * f)) * g⁻¹ := by rw [h3]
      _ = (g * z * g⁻¹) * q := by rw [hg]; group
  obtain ⟨a, ha⟩ := central_R₃ hz' hc'
  refine exists_sylow_of_conj g z ?_ ?_
  · rw [ha]; exact tau4_mem_P₀ _
  · rw [ha]; exact tau4_const_central a

theorem isSimple_of_u4two {S : Type} [Group S] (h : catalogIs S S9.isU4two) : IsSimpleGroup S := by
  obtain ⟨eS⟩ := bridge_u4two h
  have hPS : IsSimpleGroup CFSG.GH74.Exceptional.PSp43 :=
    CFSG.ClassicalGroups.Symplectic.isSimpleGroup_statedProj_statedSp (ZMod 3) 2 (by norm_num)
      (Or.inr (Or.inl ⟨by rw [Nat.card_eq_fintype_card, ZMod.card], le_rfl⟩))
  haveI := hPS
  exact MulEquiv.isSimpleGroup eS

theorem isCentralIn_of_surj {G : Type} [Group G] [Finite G] {L : Subgroup G} {M : Type} [Group M]
    [Finite M] (φ : ↥L →* M) (hφ : Function.Surjective φ) (hker : ¬ 3 ∣ Nat.card φ.ker) {y : ↥L}
    (hy : IsPGroup 3 (Subgroup.zpowers y)) (Q : Sylow 3 M) (hyQ : φ y ∈ (Q : Subgroup M))
    (hc : ∀ q ∈ (Q : Subgroup M), q * φ y = φ y * q) : IsCentralIn 3 (y : G) L := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨W, hW3, hyW, hWmap, hWinj⟩ := exists_pSubgroup_lift_of_le Nat.prime_three φ hker Q.2
    (by rw [MonoidHom.range_eq_top_of_surjective φ hφ]; exact le_top) hy
    (by rw [MonoidHom.map_zpowers]; exact Subgroup.zpowers_le.2 hyQ)
  have hyW' : y ∈ W := hyW (Subgroup.mem_zpowers y)
  refine ⟨y.2, W.map L.subtype, Subgroup.map_subtype_le W, hW3.map L.subtype,
    ⟨y, hyW', rfl⟩, ?_, ?_⟩
  · rintro _ ⟨w, hw, rfl⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hwQ : φ w ∈ (Q : Subgroup M) := hWmap ▸ Subgroup.mem_map_of_mem φ hw
    have h := hWinj (a₁ := ⟨w * y, W.mul_mem hw hyW'⟩) (a₂ := ⟨y * w, W.mul_mem hyW' hw⟩)
      (by
        show φ (w * y) = φ (y * w)
        rw [map_mul, map_mul]
        exact hc _ hwQ)
    simpa using congrArg (fun x : W => ((x : ↥L) : G)) h
  · intro Q' hPQ' hQ'L hQ'3
    set Q'' : Subgroup ↥L := Q'.subgroupOf L with hQ''
    have hQ''3 : IsPGroup 3 Q'' := hQ'3.of_equiv (Subgroup.subgroupOfEquivOfLe hQ'L).symm
    have hWQ'' : W ≤ Q'' := fun x hx => Subgroup.mem_subgroupOf.2 (hPQ' ⟨x, hx, rfl⟩)
    have hmap : Q''.map φ = Q := Q.3 (hQ''3.map φ) (by rw [← hWmap]; exact Subgroup.map_mono hWQ'')
    have hcard : Nat.card Q'' = Nat.card W := by
      rw [card_eq_of_injective_comp_subtype φ (injective_comp_subtype Nat.prime_three φ hker hQ''3),
        hmap, ← hWmap, ← card_eq_of_injective_comp_subtype φ hWinj]
    have hWeq : W = Q'' := Subgroup.eq_of_le_of_card_ge hWQ'' hcard.le
    have hQ'eq : Subgroup.map L.subtype Q'' = Q' := Subgroup.map_subgroupOf_eq_of_le hQ'L
    rw [← hQ'eq, ← hWeq]

end Row49

end

end CFSG.LocalAnalysis.GLTheoremA.CatB.U48

namespace CFSG.LocalAnalysis.GLTheoremA.CatB.Row49One

open CFSG.LocalAnalysis.RankThreeTheoremC.A6.PSp43 CFSG.ComponentClassification.CatFactsSmall.PSp43
  Subgroup
open CFSG.LocalAnalysis.GLTheoremA.CatB.YS09U42T2

theorem finite_P_three {z : Equiv.Perm (Fin 45)} (hz1 : z ≠ 1)
    {S : Subgroup (Equiv.Perm (Fin 45))} (hSP : S ≤ P) (hScard : Nat.card S = 64) (hzS : z ∈ S)
    (hSc : ∀ s ∈ S, z * s = s * z) {F : Subgroup (Equiv.Perm (Fin 45))} (hFP : F ≤ P)
    (hFc : ∀ f ∈ F, z * f = f * z) (hFcard : Nat.card F = 9) :
    ∃ y ∈ F, y ≠ 1 ∧ ∃ Q : Subgroup (Equiv.Perm (Fin 45)), Q ≤ P ∧ Nat.card Q = 81 ∧ y ∈ Q ∧
      ∀ q ∈ Q, q * y = y * q := by
  obtain ⟨g, hgP, rfl⟩ := exists_conj_of_sylow hz1 hSP hScard hzS hSc
  have hFH : ∀ f ∈ F, g⁻¹ * f * g ∈ H0 := by
    intro f hf
    refine Subgroup.mem_inf.2 ⟨mul_mem (mul_mem (inv_mem hgP) (hFP hf)) hgP, ?_⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hc := hFc f hf
    calc g⁻¹ * f * g * tauPerm 0 = g⁻¹ * (f * (g * tauPerm 0 * g⁻¹)) * g := by group
      _ = g⁻¹ * ((g * tauPerm 0 * g⁻¹) * f) * g := by rw [hc]
      _ = tauPerm 0 * (g⁻¹ * f * g) := by group
  set F' : Subgroup (Equiv.Perm (Fin 45)) := F.map (MulAut.conj g⁻¹).toMonoidHom with hF'
  have hF'H : F' ≤ H0 := by
    rintro _ ⟨f, hf, rfl⟩
    simpa [MulAut.conj_apply, mul_assoc] using hFH f hf
  have hF'c : Nat.card F' = 9 := by
    rw [hF', Subgroup.card_map_of_injective (MulAut.conj g⁻¹).injective, hFcard]
  obtain ⟨h, hh, hFeq⟩ := exists_conj_E0 hF'H hF'c
  have hhP : h ∈ P := (Subgroup.mem_inf.1 hh).1
  have hkP : g * h ∈ P := mul_mem hgP hhP
  have hcP3 : wperm cW ∈ P3 := by
    rw [show wperm cW = wperm [4, 3] * wperm [1, 0] from wperm_append [4, 3] [1, 0]]
    exact mul_mem (wperm_mem_gen (ws := P3gens) (by simp [P3gens]))
      (wperm_mem_gen (ws := P3gens) (by simp [P3gens]))
  have hc1 : wperm cW ≠ 1 := fun h1 => c_noncomm (by
    have h2 : wperm [4, 3, 1, 0] = 1 := h1
    rw [h2]; simp)
  have hyF' : h * wperm cW * h⁻¹ ∈ F' := by rw [hFeq]; exact ⟨wperm cW, c_mem_E0, rfl⟩
  obtain ⟨f, hf, hfeq⟩ := hyF'
  have hfk : f = (g * h) * wperm cW * (g * h)⁻¹ := by
    have h1 : g⁻¹ * f * g = h * wperm cW * h⁻¹ := by simpa [MulAut.conj_apply] using hfeq
    calc f = g * (g⁻¹ * f * g) * g⁻¹ := by group
      _ = g * (h * wperm cW * h⁻¹) * g⁻¹ := by rw [h1]
      _ = (g * h) * wperm cW * (g * h)⁻¹ := by group
  refine ⟨f, hf, ?_, P3.map (MulAut.conj (g * h)).toMonoidHom, ?_, ?_, ?_, ?_⟩
  · intro h1
    apply hc1
    calc wperm cW = (g * h)⁻¹ * ((g * h) * wperm cW * (g * h)⁻¹) * (g * h) := by group
      _ = 1 := by rw [← hfk, h1]; group
  · rintro _ ⟨p, hp, rfl⟩
    exact mul_mem (mul_mem hkP (P3_le_P hp)) (inv_mem hkP)
  · rw [Subgroup.card_map_of_injective (MulAut.conj (g * h)).injective, card_P3]
  · exact ⟨wperm cW, hcP3, hfk.symm⟩
  · rintro _ ⟨p, hp, rfl⟩
    have hpc : p * wperm cW = wperm cW * p :=
      Subgroup.mem_centralizer_singleton_iff.1 (P3_le_centralizer_c hp)
    rw [hfk]
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    calc g * h * p * (g * h)⁻¹ * (g * h * wperm cW * (g * h)⁻¹)
        = (g * h) * (p * wperm cW) * (g * h)⁻¹ := by group
      _ = (g * h) * (wperm cW * p) * (g * h)⁻¹ := by rw [hpc]
      _ = g * h * wperm cW * (g * h)⁻¹ * (g * h * p * (g * h)⁻¹) := by group

theorem finite_psp43_three {z : CFSG.GH74.Exceptional.PSp43} (hz1 : z ≠ 1)
    {S : Subgroup CFSG.GH74.Exceptional.PSp43} (hScard : Nat.card S = 64) (hzS : z ∈ S)
    (hSc : ∀ s ∈ S, z * s = s * z) {F : Subgroup CFSG.GH74.Exceptional.PSp43}
    (hFc : ∀ f ∈ F, z * f = f * z) (hFcard : Nat.card F = 9) :
    ∃ y ∈ F, y ≠ 1 ∧ ∃ Q : Subgroup CFSG.GH74.Exceptional.PSp43, Nat.card Q = 81 ∧ y ∈ Q ∧
      ∀ q ∈ Q, q * y = y * q := by
  have hinj : Function.Injective psi := psi_injective'
  have hPr := range_psi_eq
  set ψ := psi with hψ
  have hSP : S.map ψ ≤ P := by rw [← hPr]; exact Subgroup.map_le_range ψ S
  have hFP : F.map ψ ≤ P := by rw [← hPr]; exact Subgroup.map_le_range ψ F
  obtain ⟨yP, hyPF, hyP1, Q, hQP, hQcard, hyQ, hQc⟩ := finite_P_three
    (fun h => hz1 (hinj (h.trans (map_one ψ).symm))) hSP
    (by rw [Subgroup.card_map_of_injective hinj, hScard]) (Subgroup.mem_map_of_mem ψ hzS)
    (by rintro _ ⟨s, hs, rfl⟩; rw [← map_mul, ← map_mul, hSc s hs]) hFP
    (by rintro _ ⟨f, hf, rfl⟩; rw [← map_mul, ← map_mul, hFc f hf])
    (by rw [Subgroup.card_map_of_injective hinj, hFcard])
  obtain ⟨y, hyF, rfl⟩ := hyPF
  have hQr : Q ≤ ψ.range := by rw [hPr]; exact hQP
  refine ⟨y, hyF, fun h => hyP1 (by rw [h, map_one]), Q.comap ψ, ?_, hyQ, fun q hq => ?_⟩
  · have hmap : (Q.comap ψ).map ψ = Q := by rw [Subgroup.map_comap_eq, inf_eq_right.2 hQr]
    have h1 := Subgroup.card_map_of_injective (f := ψ) hinj (K := Q.comap ψ)
    rw [hmap, hQcard] at h1
    exact h1.symm
  · apply hinj
    rw [map_mul, map_mul]
    exact hQc (ψ q) hq

end CFSG.LocalAnalysis.GLTheoremA.CatB.Row49One

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.LocalAnalysis.GLTheoremA.S10
open CFSG.LocalAnalysis.GLTheoremA.CatB CFSG.LocalAnalysis.GLTheoremA.CatB.U48
open CFSG.LocalAnalysis.GLTheoremA.CatB.U48.Row49
open CFSG.LocalAnalysis.RankThreeTheoremC.A6.PSp43 (factorization_three_25920 factorization_two_25920
  card_PSp43_eq card_subgroupOf_of_le)
open CFSG.RankThree.PartTwo.Sec4.Item434SmallTwoIVU48 (SU4 fieldFactor4
  mem_range_conj_of_fieldFactor4_eq_one)

section Row49


theorem i307At_two_holds (G : Type) [Group G] [Finite G] (X L : Subgroup G) (b y : G)
    (hL : GLAPComponent 3 X L) (hcat : catalogIs (PSimple 3 L) S9.isU4eight)
    (hFO : FieldOn 3 b L) (hb3 : b ^ 3 = 1) (hyc : IsCentralIn 3 y (Ipart 3 L b)) :
    IsCentralIn 3 y L := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hb : b ∈ Subgroup.normalizer (L : Set G) := hFO.1
  have hZ := center_pquot_eq_bot_of_u48 hL hcat
  let e := pqModelP hZ hcat
  let γ : MulAut SU4 := MulAut.congr e (barAut L b hb)
  have hγ : ∀ q : PQuot 3 L, γ (e q) = e (barAut L b hb q) := by
    intro q
    change (MulAut.congr e (barAut L b hb)) (e q) = _
    rw [MulAut.congr_apply]
    simp only [MulEquiv.trans_apply, MulEquiv.symm_apply_apply]
  have hγ3 : γ ^ 3 = 1 := by
    have h : (MulAut.congr e) (barAut L b hb ^ 3) = 1 := by
      rw [barAut_pow_three L b hb hb3, map_one]
    rwa [map_pow] at h
  let τ : PSimple 3 L ≃* SU4 :=
    ((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot).trans e
  obtain ⟨-, hγ1⟩ := dict_outer hcat hFO τ γ (fun q => hγ q)
  have hff : fieldFactor4 γ ≠ 1 := fun h => hγ1 (mem_range_conj_of_fieldFactor4_eq_one h)
  obtain ⟨hcatF, hcardF⟩ := catalogIs_fixSub hγ3 hff
  set F : Subgroup SU4 := fixSub γ with hFdef
  set Y : Subgroup G := L ⊓ Subgroup.centralizer ({b} : Set G) with hY
  have hYL : Y ≤ L := inf_le_left
  have hπF : ∀ x : ↥Y, (piOf L e) (Subgroup.inclusion hYL x) ∈ F := fun x =>
    gamma_fixed_of_mem hb e γ hγ (Subgroup.inclusion hYL x) x.2.2
  have hsurj : ∀ c ∈ F, ∃ x : ↥Y, (piOf L e) (Subgroup.inclusion hYL x) = c := by
    intro c hc
    obtain ⟨x, rfl⟩ := piOf_surjective L e c
    have hfix : (QuotientGroup.mk (conjL L b hb x) : PQuot 3 L) = QuotientGroup.mk x := by
      have h2 : γ (e (QuotientGroup.mk x)) = e (QuotientGroup.mk x) := hc
      rw [hγ, barAut_mk] at h2
      exact e.injective h2
    obtain ⟨x', hx'c, hx'mk⟩ := exists_cent_lift_outer hb hb3 x hfix
    refine ⟨⟨(x' : G), x'.2, Subgroup.mem_centralizer_singleton_iff.2 hx'c⟩, ?_⟩
    change e (QuotientGroup.mk x') = e (QuotientGroup.mk x)
    rw [hx'mk]
  let ψ : ↥Y →* ↥F := restrictTo (piOf L e) F hYL hπF
  have hψs : Function.Surjective ψ := restrictTo_surjective (piOf L e) F hYL hπF hsurj
  have hψk : ¬ 3 ∣ Nat.card ψ.ker :=
    restrictTo_ker (piOf L e) F hYL hπF (not_three_dvd_card_ker_piOf e)
  have hcardF' : Nat.card ↥F = 25920 := hcardF
  haveI hsimp : IsSimpleGroup ↥F := isSimple_of_u4two hcatF
  have hC : GLAPPrimeCore 3 ↥F = ⊥ := pPrimeCore_eq_bot_of_simple (by rw [hcardF']; norm_num)
  have hS : CFSG.Open.IsQuasisimple ↥(⊤ : Subgroup ↥F) := by
    haveI : IsSimpleGroup ↥(⊤ : Subgroup ↥F) := Subgroup.topEquiv.isSimpleGroup
    refine isQuasisimple_of_simple_nonabelian ?_
    intro hcomm
    have hp := (@Group.is_simple_iff_prime_card ↥(⊤ : Subgroup ↥F) _ hcomm).1 inferInstance
    rw [Subgroup.card_top, hcardF'] at hp
    norm_num at hp
  obtain ⟨J, hJ, hJl, himg, -⟩ := layer_of_surj ψ hψs hψk hC ⊤ hS (fun T _ => le_top)
  have hyc' : IsCentralIn 3 y J := by rw [← hJl]; exact hyc
  obtain ⟨hyJ, P, hPJ, hP3, hyP, hPc, hPmax⟩ := hyc'
  have hJY : J ≤ Y := hJ.1
  have hJL : J ≤ L := hJY.trans hYL
  let ψJ : ↥J →* ↥F := ψ.comp (Subgroup.inclusion hJY)
  have hψJs : Function.Surjective ψJ := by
    intro c
    have hc : c ∈ (J.subgroupOf Y).map ψ := by rw [himg]; exact Subgroup.mem_top c
    obtain ⟨x, hx, rfl⟩ := hc
    exact ⟨⟨x.1, Subgroup.mem_subgroupOf.1 hx⟩, rfl⟩
  have hψJk : ¬ 3 ∣ Nat.card ψJ.ker := by
    intro h3
    apply hψk
    refine h3.trans ?_
    rw [← Subgroup.card_map_of_injective (K := ψJ.ker) (Subgroup.inclusion_injective hJY)]
    apply Subgroup.card_dvd_of_le
    rintro _ ⟨x, hx, rfl⟩
    exact hx
  obtain ⟨S, hSdef⟩ := sylow_image hPJ hP3 hPmax ψJ hψJs hψJk
  set S' : Subgroup SU4 := (S : Subgroup ↥F).map F.subtype with hS'
  have hS'F : S' ≤ F := Subgroup.map_subtype_le _
  have hS'card : Nat.card S' = 81 := by
    rw [hS', Subgroup.card_map_of_injective F.subtype_injective, Sylow.card_eq_multiplicity S,
      hcardF', factorization_three_25920]
    norm_num
  let yL : ↥L := ⟨y, hJL hyJ⟩
  let yJ : ↥J := ⟨y, hyJ⟩
  have hyJP : yJ ∈ P.subgroupOf J := Subgroup.mem_subgroupOf.2 hyP
  have hzS : piOf L e yL ∈ S' := ⟨ψJ yJ, by rw [hSdef]; exact ⟨yJ, hyJP, rfl⟩, rfl⟩
  have hzc : ∀ q ∈ S', q * piOf L e yL = piOf L e yL * q := by
    rintro _ ⟨s, hs, rfl⟩
    rw [hSdef] at hs
    obtain ⟨p, hp, rfl⟩ := hs
    have hpy : (p : G) * y = y * (p : G) :=
      Subgroup.mem_centralizer_singleton_iff.1 (hPc (Subgroup.mem_subgroupOf.1 hp))
    have h2 := congrArg (fun x : ↥J => ((ψJ x : ↥F) : SU4)) (Subtype.ext hpy : p * yJ = yJ * p)
    rw [show piOf L e yL = ((ψJ yJ : ↥F) : SU4) from rfl]
    simpa [map_mul] using h2
  obtain ⟨Q, hzQ, hQc⟩ := exists_sylow_central hγ3 hff hcardF' hS'F hS'card hzS hzc
  have hy : IsPGroup 3 (Subgroup.zpowers yL) := by
    obtain ⟨k, hk⟩ := hP3 ⟨y, hyP⟩
    have hk' : yL ^ 3 ^ k = 1 := Subtype.ext (by simpa using congrArg Subtype.val hk)
    intro g
    obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.1 g.2
    refine ⟨k, Subtype.ext ?_⟩
    rw [Subgroup.coe_pow, ← hm, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hk',
      one_zpow]
    rfl
  exact isCentralIn_of_surj (piOf L e) (piOf_surjective L e) (not_three_dvd_card_ker_piOf e) hy Q
    hzQ hQc

theorem i307At_one_holds (G : Type) [Group G] [Finite G] (X K E : Subgroup G) (z : G)
    (hK : GLAPComponent 3 X K) (hcat : catalogIs (PSimple 3 K) S9.isU4two)
    (hodd : Odd (Nat.card (GLAPPrimeCoreOf 3 K))) (hzc : IsCentralIn 2 z K) (hz2 : z ^ 2 = 1)
    (hz1 : z ≠ 1) (hEc : E ≤ K ⊓ Subgroup.centralizer ({z} : Set G)) (hEel : IsElemAbelian 3 E)
    (hEcard : Nat.card E = 3 ^ 2) : ∃ y ∈ E, y ≠ 1 ∧ IsCentralIn 3 y K := by
  have hq := isQuasisimple_pQuot_of_glaPComponent Nat.prime_three hK
  have hZ := center_pQuot_eq_bot_u4two
    CFSG.Milestones.cl_lit_griess_schur_multipliers_all_models_statement hq hcat
  obtain ⟨e⟩ := bridge_u4two hcat
  obtain ⟨π, hπs, hkc⟩ := exists_hom_of_simple_equiv e
  have hk3 : ¬ 3 ∣ Nat.card π.ker := not_three_dvd_card_ker K hkc hZ
  have hk2 : ¬ 2 ∣ Nat.card π.ker := odd_card_ker K hkc hodd
  have hrange : π.range = ⊤ := MonoidHom.range_eq_top_of_surjective π hπs
  have hKcard : Nat.card K = Nat.card π.ker * 25920 := by
    have h1 := π.ker.card_mul_index
    rw [Subgroup.index_ker, hrange, Subgroup.card_top, card_PSp43_eq] at h1
    exact h1.symm
  have hKfac : (Nat.card K).factorization 2 = 6 := by
    rw [hKcard, Nat.factorization_mul Nat.card_pos.ne' (by norm_num), Finsupp.add_apply,
      Nat.factorization_eq_zero_of_not_dvd hk2, factorization_two_25920, zero_add]
  obtain ⟨hzK, P', hP'K, hP'2, hzP', hP'c, hmax⟩ := hzc
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hW2 : IsPGroup 2 (P'.subgroupOf K) := hP'2.of_equiv (Subgroup.subgroupOfEquivOfLe hP'K).symm
  have hP'card : Nat.card P' = 64 := by
    obtain ⟨R, hR⟩ := hW2.exists_le_sylow
    have hRK : (R : Subgroup K).map K.subtype = P' := by
      refine hmax _ ?_ (Subgroup.map_subtype_le _) (R.2.map K.subtype)
      intro x hx
      exact ⟨⟨x, hP'K hx⟩, hR (Subgroup.mem_subgroupOf.2 hx), rfl⟩
    rw [← hRK, Subgroup.card_map_of_injective K.subtype_injective, Sylow.card_eq_multiplicity R,
      hKfac]
    norm_num
  set W := P'.subgroupOf K with hWdef
  have hWinj : Function.Injective (π.comp W.subtype) :=
    injective_comp_subtype Nat.prime_two π hk2 hW2
  have hWcard : Nat.card (W.map π) = 64 := by
    rw [← card_eq_of_injective_comp_subtype π hWinj, hWdef, card_subgroupOf_of_le hP'K, hP'card]
  have hSbc : ∀ s ∈ W.map π, π ⟨z, hzK⟩ * s = s * π ⟨z, hzK⟩ := by
    rintro _ ⟨w, hw, rfl⟩
    rw [← map_mul, ← map_mul]
    congr 1
    apply Subtype.ext
    exact (Subgroup.mem_centralizer_singleton_iff.1 (hP'c (Subgroup.mem_subgroupOf.1 hw))).symm
  have hzbS : π ⟨z, hzK⟩ ∈ W.map π := Subgroup.mem_map_of_mem π (Subgroup.mem_subgroupOf.2 hzP')
  have hzb1 : π ⟨z, hzK⟩ ≠ 1 := by
    intro h
    have hmem : (⟨z, hzK⟩ : K) ∈ π.ker := h
    have hne : (⟨⟨z, hzK⟩, hmem⟩ : π.ker) ≠ 1 := fun h1 =>
      hz1 (congrArg Subtype.val (congrArg Subtype.val h1))
    have hsq : (⟨⟨z, hzK⟩, hmem⟩ : π.ker) ^ 2 = 1 :=
      Subtype.ext (Subtype.ext (by simpa using hz2))
    have hdvd := orderOf_dvd_natCard (⟨⟨z, hzK⟩, hmem⟩ : π.ker)
    rw [orderOf_eq_prime hsq hne] at hdvd
    exact hk2 hdvd
  have hEK : E ≤ K := fun x hx => (Subgroup.mem_inf.1 (hEc hx)).1
  set W3 := E.subgroupOf K with hW3def
  have hW3 : IsPGroup 3 W3 :=
    (isPGroup_of_isElemAbelian hEel).of_equiv (Subgroup.subgroupOfEquivOfLe hEK).symm
  have hW3inj : Function.Injective (π.comp W3.subtype) :=
    injective_comp_subtype Nat.prime_three π hk3 hW3
  have hEbcard : Nat.card (W3.map π) = 9 := by
    rw [← card_eq_of_injective_comp_subtype π hW3inj, hW3def, card_subgroupOf_of_le hEK, hEcard]
    norm_num
  have hEbc : ∀ f ∈ W3.map π, π ⟨z, hzK⟩ * f = f * π ⟨z, hzK⟩ := by
    rintro _ ⟨a, ha, rfl⟩
    rw [← map_mul, ← map_mul]
    congr 1
    apply Subtype.ext
    exact (Subgroup.mem_centralizer_singleton_iff.1
      (Subgroup.mem_inf.1 (hEc (Subgroup.mem_subgroupOf.1 ha))).2).symm
  obtain ⟨yb, ⟨a, ha, hay⟩, hyb1, Q, hQcard, hybQ, hQc⟩ :=
    Row49One.finite_psp43_three hzb1 hWcard hzbS hSbc hEbc hEbcard
  have haE : (a : G) ∈ E := Subgroup.mem_subgroupOf.1 ha
  have ha3 : a ^ 3 = 1 := Subtype.ext (by simpa using hEel.2 (a : G) haE)
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have h81 : (3 : ℕ) ^ (Nat.card CFSG.GH74.Exceptional.PSp43).factorization 3 = 81 := by
    rw [card_PSp43_eq, factorization_three_25920]; norm_num
  let SQ : Sylow 3 CFSG.GH74.Exceptional.PSp43 := Sylow.ofCard Q (by rw [hQcard, h81])
  refine ⟨(a : G), haE, fun h1 => hyb1 ?_, isCentralIn_of_surj π hπs hk3
    (isPGroup_zpowers_of_pow_eq_one ha3) SQ (hay ▸ hybQ) fun q hq => hay ▸ hQc q hq⟩
  rw [← hay, show a = 1 from Subtype.ext h1, map_one]

theorem i307At_holds (G : Type) [Group G] [Finite G] : I307At G :=
  ⟨fun X K E z hK hcat hodd hzc hz2 hz1 hEc hEel hEcard =>
      i307At_one_holds G X K E z hK hcat hodd hzc hz2 hz1 hEc hEel hEcard,
    fun X L b y hL hcat hFO hb3 hyc => i307At_two_holds G X L b y hL hcat hFO hb3 hyc⟩

end Row49

end CFSG.LocalAnalysis.GLTheoremA
