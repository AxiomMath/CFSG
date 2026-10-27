module

public import CFSG.LieType.SeitzGeneration.UnitaryReduce
public import CFSG.LieType.SeitzGeneration.UnitaryCenters
public import CFSG.LieType.SeitzGeneration.UnitaryMixing

public section

namespace CFSG.LieType.SeitzGeneration

open CFSG.Open CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
  CFSG.RankThree.PartOne.KCUnitaryPlane

namespace Nonsplit

section Numerics

variable {ℓ f p : ℕ} {K : Type} [Field K]

theorem three_le_ordNegQ (hp : p.Prime) (hp5 : 5 ≤ p) (hℓ : ℓ.Prime) (hpℓ : p ≠ ℓ) (hf : 1 ≤ f)
    (hpq1 : ¬ p ∣ ℓ ^ f + 1) (hpq : ¬ p ∣ ℓ ^ f - 1) : 3 ≤ ordNegQ ℓ f p := by
  have hpos := pos_ordNegQ (f := f) hp hpℓ hℓ
  have h1 : ordNegQ ℓ f p ≠ 1 := fun h => hpq1 ((ordNegQ_eq_one_iff hp).mp h)
  have h2 : ordNegQ ℓ f p ≠ 2 := fun h => hpq (ordNegQ_eq_two hp (by omega) hℓ h hf).1
  omega

theorem exists_norm_ne_one (hU : UnitaryFieldData ℓ f K) (hq : ℓ ^ f ≠ 2) :
    ∃ s : K, s ≠ 0 ∧ hU.bar s * s ≠ 1 := by
  have := hU.finite
  have hq2 : 2 ≤ ℓ ^ f := by
    have := hU.one_lt_pow
    omega
  have hcard : 2 < (hU.fixedField : Set K).ncard := by
    rw [← Nat.card_coe_set_eq]
    change 2 < Nat.card hU.fixedField
    rw [hU.card_fixedField]
    omega
  obtain ⟨a, b, c, ha, hb, hc, hab, hac, hbc⟩ := (Set.two_lt_ncard_iff (Set.toFinite _)).1 hcard
  obtain ⟨d, hd, hd0, hd1⟩ : ∃ d ∈ (hU.fixedField : Set K), d ≠ 0 ∧ d ≠ 1 := by
    by_cases h0 : a = 0 ∨ a = 1
    · by_cases h1 : b = 0 ∨ b = 1
      · refine ⟨c, hc, ?_, ?_⟩
        · rintro rfl
          rcases h0 with rfl | rfl <;> rcases h1 with rfl | rfl <;> simp_all
        · rintro rfl
          rcases h0 with rfl | rfl <;> rcases h1 with rfl | rfl <;> simp_all
      · push Not at h1
        exact ⟨b, hb, h1.1, h1.2⟩
    · push Not at h0
      exact ⟨a, ha, h0.1, h0.2⟩
  obtain ⟨s, hs⟩ := hU.normHom_surjective ⟨d, hd⟩
  have hs' : s * hU.bar s = d := congrArg Subtype.val hs
  refine ⟨s, ?_, ?_⟩
  · rintro rfl
    rw [zero_mul] at hs'
    exact hd0 hs'.symm
  · rw [mul_comm, hs']
    exact hd1

end Numerics

section Bridge

open CFSG.ClassicalGroups.Unitary CFSG.LieType.Universal.Unitary CFSG.LieType.BorelTits
  CFSG.RankThree.PartOne CFSG.RankThree.PartOne.KCUnitaryModel CFSG.LinearGroups

variable {ℓ f n : ℕ} {K : Type} [Field K] [Finite K] [Fact ℓ.Prime] [CharP K ℓ]

theorem idForm_eq_herm (hU : UnitaryFieldData ℓ f K) (x y : Fin n → K) :
    idForm hU n x y = herm (unitaryInvolution K ℓ f) x y := by
  rw [idForm, gramForm_apply, herm_def, dotProduct]
  simp only [idGram, Units.val_one, Matrix.one_mulVec]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [unitaryInvolution_apply, UnitaryFieldData.bar_apply]

theorem isUnitaryInvolution (hU : UnitaryFieldData ℓ f K) :
    IsUnitaryInvolution (unitaryInvolution K ℓ f) :=
  isUnitaryInvolution_unitaryInvolution hU.card_eq_sq

theorem unitaryInvolution_eq_bar (hU : UnitaryFieldData ℓ f K) (c : K) :
    unitaryInvolution K ℓ f c = hU.bar c := by
  rw [unitaryInvolution_apply, UnitaryFieldData.bar_apply]

theorem hasONBasis_of_separatingLeft (hU : UnitaryFieldData ℓ f K) (W : Submodule K (Fin n → K))
    (hW : ((idForm hU n).domRestrict₁₂ W W).SeparatingLeft)
    (hdim : 4 ≤ Module.finrank K W ∨ (3 ≤ Module.finrank K W ∧
      ∃ s : K, s ≠ 0 ∧ unitaryInvolution K ℓ f s * s ≠ 1)) :
    Centers.HasONBasis (unitaryInvolution K ℓ f) W := by
  have hB : (idForm hU n).IsSymm := idForm_isSymm hU n
  obtain ⟨b, hb⟩ := hU.exists_orthonormal_basis (hB.domRestrict W) hW
  refine ⟨Module.finrank K W, fun i => (b i : Fin n → K), fun i j => ?_, ?_, hdim⟩
  · have := hb i j
    rw [LinearMap.domRestrict₁₂_apply, idForm_eq_herm] at this
    exact this
  · have h1 : Submodule.span K (Set.range fun i => (b i : Fin n → K)) =
        (Submodule.span K (Set.range b)).map W.subtype := by
      rw [Submodule.map_span, ← Set.range_comp]
      rfl
    rw [h1, b.span_eq, Submodule.map_top, Submodule.range_subtype]

end Bridge

section Geometry

open CFSG.ClassicalGroups.Unitary CFSG.LieType.Universal.Unitary

variable {K : Type} [Field K] {σ : K ≃+* K} {n : ℕ}

theorem exists_isotropic_pairing (hσ : IsUnitaryInvolution σ) {W : Submodule K (Fin n → K)}
    (hW : Centers.HasONBasis σ W) {w : Fin n → K} (hw : w ∈ W) (hw0 : w ≠ 0) :
    ∃ w₀ ∈ W, herm σ w₀ w₀ = 0 ∧ herm σ w w₀ ≠ 0 := by
  obtain ⟨m, x, hx, hspan, hm⟩ := hW
  obtain ⟨c', rfl⟩ := (Centers.mem_span_range_iff x w).1 (hspan ▸ hw)
  have hc' : c' ≠ 0 := fun h => hw0 (by rw [h, map_zero])
  have hm3 : 3 ≤ m := by rcases hm with h | ⟨h, _⟩ <;> omega
  obtain ⟨a₀, ha₀0, ha₀⟩ := Centers.exists_isotropic_ne_zero hσ (by omega : 2 ≤ m)
  obtain ⟨d, hdi, -, hcd⟩ := exists_cno hσ ha₀0 ha₀ hc'
  refine ⟨Centers.orthoEmb x d, hspan ▸ Centers.orthoEmb_mem_span x d, ?_, ?_⟩
  · rw [Centers.herm_orthoEmb hx]
    exact hdi
  · rw [Centers.herm_orthoEmb hx]
    exact hcd

theorem isCenter_of_fixed (hσ : ∀ c, σ (σ c) = c) {H : Subgroup (SUid σ n)} {y : SUid σ n}
    (hH : ∀ g : SUid σ n, g * y = y * g → g ∈ H) {v : Fin n → K} (hv : herm σ v v = 0)
    (hyv : y • v = v) : Centers.IsCenter H v := by
  refine ⟨hv, fun c hc => ⟨tv hσ hv hc, hH _ ?_, tv_smul hσ hv hc⟩⟩
  apply ext_smul σ
  intro u
  have h1 : herm σ v (y • u) = herm σ v u := by
    have := herm_smul_smul σ y v u
    rwa [hyv] at this
  rw [mul_smul, mul_smul, tv_smul, tv_smul, smul_add, smul_comm y (c * herm σ v u) v, hyv, h1]

theorem separatingLeft_sup {R : Type*} [Field R] {τ : R →+* R} {V : Type*} [AddCommGroup V]
    [Module R V] {B : V →ₛₗ[τ] V →ₗ[R] R} (hB : B.IsSymm) {W₁ W₂ : Submodule R V}
    (h₁ : (B.domRestrict₁₂ W₁ W₁).SeparatingLeft) (h₂ : (B.domRestrict₁₂ W₂ W₂).SeparatingLeft)
    (horth : ∀ u ∈ W₁, ∀ v ∈ W₂, B u v = 0) :
    (B.domRestrict₁₂ (W₁ ⊔ W₂) (W₁ ⊔ W₂)).SeparatingLeft := by
  intro z hz
  obtain ⟨z₁, hz₁, z₂, hz₂, hzz⟩ := Submodule.mem_sup.mp z.2
  have horth' : ∀ u ∈ W₂, ∀ v ∈ W₁, B u v = 0 := fun u hu v hv => by
    rw [← hB.eq v u, horth v hv u hu, map_zero]
  have h1 : (⟨z₁, hz₁⟩ : W₁) = 0 := by
    refine h₁ _ fun y => ?_
    have := hz ⟨(y : V), Submodule.mem_sup_left y.2⟩
    rw [LinearMap.domRestrict₁₂_apply] at this ⊢
    have e : (z : V) = z₁ + z₂ := hzz.symm
    simp only at this ⊢
    rw [e, map_add, LinearMap.add_apply, horth' z₂ hz₂ y y.2, add_zero] at this
    exact this
  have h2 : (⟨z₂, hz₂⟩ : W₂) = 0 := by
    refine h₂ _ fun y => ?_
    have := hz ⟨(y : V), Submodule.mem_sup_right y.2⟩
    rw [LinearMap.domRestrict₁₂_apply] at this ⊢
    have e : (z : V) = z₁ + z₂ := hzz.symm
    simp only at this ⊢
    rw [e, map_add, LinearMap.add_apply, horth z₁ hz₁ y y.2, zero_add] at this
    exact this
  refine Subtype.ext ?_
  rw [← hzz]
  have h1' : z₁ = 0 := congrArg Subtype.val h1
  have h2' : z₂ = 0 := congrArg Subtype.val h2
  rw [h1', h2', add_zero]
  rfl

theorem forall_sup_sup {R : Type*} [Field R] {τ : R →+* R} {V : Type*} [AddCommGroup V]
    [Module R V] {B : V →ₛₗ[τ] V →ₗ[R] R} {X₁ X₂ Y₁ Y₂ : Submodule R V}
    (h11 : ∀ x ∈ X₁, ∀ y ∈ Y₁, B x y = 0) (h12 : ∀ x ∈ X₁, ∀ y ∈ Y₂, B x y = 0)
    (h21 : ∀ x ∈ X₂, ∀ y ∈ Y₁, B x y = 0) (h22 : ∀ x ∈ X₂, ∀ y ∈ Y₂, B x y = 0) :
    ∀ u ∈ X₁ ⊔ X₂, ∀ v ∈ Y₁ ⊔ Y₂, B u v = 0 := by
  intro u hu v hv
  obtain ⟨x₁, hx₁, x₂, hx₂, rfl⟩ := Submodule.mem_sup.mp hu
  obtain ⟨y₁, hy₁, y₂, hy₂, rfl⟩ := Submodule.mem_sup.mp hv
  simp only [map_add, LinearMap.add_apply, h11 x₁ hx₁ y₁ hy₁, h12 x₁ hx₁ y₂ hy₂,
    h21 x₂ hx₂ y₁ hy₁, h22 x₂ hx₂ y₂ hy₂, add_zero]

end Geometry

section Core

open Matrix CFSG.ClassicalGroups.Unitary CFSG.LieType.Universal.Unitary CFSG.LieType.BorelTits
  CFSG.RankThree.PartOne CFSG.RankThree.PartOne.KCUnitaryModel
  CFSG.RankThree.PartOne.KCUnitaryExact CFSG.RankThree.PartOne.KCUnitary
  CFSG.RankThree.PartOne.KCUnitaryMixing CFSG.RankThree.PartOne.KCPrimary Polynomial

variable {ℓ f p n : ℕ} {K : Type} [Field K] [Finite K] [Fact ℓ.Prime] [CharP K ℓ]

theorem mem_closure_centralizers (hU : UnitaryFieldData ℓ f K) (hp5 : 5 ≤ p)
    (hpq1 : ¬ p ∣ ℓ ^ f + 1) (hpq : ¬ p ∣ ℓ ^ f - 1)
    {Ahat : Subgroup (gramSU hU (idGram K n))} (S : PlaneSetup hU n p Ahat)
    (g : GL (Fin n) K) (hg : g ∈ gramSU hU (idGram K n)) :
    g ∈ Subgroup.closure {g : GL (Fin n) K | g ∈ gramSU hU (idGram K n) ∧
      ∃ x : gramSU hU (idGram K n), x ∈ Ahat ∧ x ≠ 1 ∧
        g * (x : GL (Fin n) K) = (x : GL (Fin n) K) * g} := by
  classical
  have hℓ := hU.prime
  have hf := hU.one_le
  set σ := unitaryInvolution K ℓ f with hσdef
  have hσ : IsUnitaryInvolution σ := isUnitaryInvolution hU
  have hSG : SUid σ n = gramSU hU (idGram K n) := by
    rw [hσdef, SUid_eq_statedSU hU.card_eq_sq n]
    exact (unitarySU_eq_gramSU hU n)
  have he3 : 3 ≤ ordNegQ ℓ f p := three_le_ordNegQ S.prime hp5 hℓ S.ne_char hf hpq1 hpq
  have hdec := planeKernelDecomposition (h := hU) S.prime S.ne_char S.elem S.card
  have : Finite ↥Ahat := inferInstance
  have : Fintype ↥Ahat := Fintype.ofFinite _
  set ρ := planeRep hU n Ahat with hρdef
  set B := idForm hU n with hBdef
  set 𝒞 : Set (GL (Fin n) K) := {g | g ∈ gramSU hU (idGram K n) ∧
    ∃ x : gramSU hU (idGram K n), x ∈ Ahat ∧ x ≠ 1 ∧
      g * (x : GL (Fin n) K) = (x : GL (Fin n) K) * g} with h𝒞
  set Hgl : Subgroup (GL (Fin n) K) := Subgroup.closure 𝒞 with hHgl
  let H : Subgroup (SUid σ n) := Hgl.comap (SUid σ n).subtype
  have hHmem : ∀ (gS : SUid σ n) (x : gramSU hU (idGram K n)), x ∈ Ahat → x ≠ 1 →
      (gS : GL (Fin n) K) * (x : GL (Fin n) K) = (x : GL (Fin n) K) * gS → gS ∈ H := by
    intro gS x hx hx1 hcomm
    have hgS : (gS : GL (Fin n) K) ∈ gramSU hU (idGram K n) := hSG ▸ gS.2
    exact Subgroup.subset_closure ⟨hgS, x, hx, hx1, hcomm⟩
  have hexL : ∀ L : Subgroup ↥Ahat, Nat.card L = p → ∃ t : ↥Ahat, t ∈ L ∧ t ≠ 1 := by
    intro N hN
    have h1 : Nontrivial ↥N :=
      Finite.one_lt_card_iff_nontrivial.mp (by rw [hN]; exact S.prime.one_lt)
    obtain ⟨t, ht⟩ := exists_ne (1 : ↥N)
    exact ⟨t, t.2, fun h' => ht (Subtype.ext h')⟩
  let toS : ↥Ahat → SUid σ n := fun t =>
    ⟨((t.1 : gramSU hU (idGram K n)) : GL (Fin n) K), by rw [hSG]; exact t.1.2⟩
  have hact : ∀ (t : ↥Ahat) (v : Fin n → K), act ρ t v = toS t • v := fun t v => by
    rw [smul_def σ (toS t) v]
    simp [act, hρdef, planeRep, toLinU, toUnitary, toS]
    rfl
  have hAll : ∀ L : Subgroup ↥Ahat, Nat.card L = p →
      Centers.AllCenters H (fixedSpace ρ ⊤ ⊔ lineSpace ρ B L) := by
    intro L hL v hv hvi
    obtain ⟨t, htL, ht1⟩ := hexL L hL
    have hker := hdec.ker_eq L hL t htL ht1
    have hv' : v ∈ LinearMap.ker (act ρ t - 1) := hker ▸ hv
    have hfix : toS t • v = v := by
      rw [← hact]
      simpa [sub_eq_zero] using hv'
    refine isCenter_of_fixed hσ.invol (fun g hg => hHmem g t.1 t.2
      (fun h => ht1 (Subtype.ext h)) ?_) hvi hfix
    have := congrArg (fun z : SUid σ n => (z : GL (Fin n) K)) hg
    simpa [toS] using this
  have hfin : ∀ L : Subgroup ↥Ahat, Nat.card L = p → lineSpace ρ B L ≠ ⊥ →
      ordNegQ ℓ f p ≤ Module.finrank K (lineSpace ρ B L) := by
    intro L hL hV
    have hdvd := hdec.dvd_finrank L hL
    have hpos : 1 ≤ Module.finrank K (lineSpace ρ B L) := Submodule.one_le_finrank_iff.mpr hV
    exact Nat.le_of_dvd hpos hdvd
  have hdimOK : ∀ L : Subgroup ↥Ahat, Nat.card L = p → lineSpace ρ B L ≠ ⊥ →
      (4 ≤ Module.finrank K (lineSpace ρ B L) ∨ (3 ≤ Module.finrank K (lineSpace ρ B L) ∧
        ∃ s : K, s ≠ 0 ∧ σ s * s ≠ 1)) := by
    intro L hL hV
    have hle := hfin L hL hV
    by_cases hq : ℓ ^ f = 2
    · left
      have := four_le_ordNegQ_of_two S.prime (by omega : 3 < p) S.ne_char hℓ hq
      omega
    · right
      refine ⟨by omega, ?_⟩
      obtain ⟨s, hs0, hs⟩ := exists_norm_ne_one hU hq
      refine ⟨s, hs0, ?_⟩
      rw [hσdef, unitaryInvolution_eq_bar hU]
      exact hs
  have hBsymm : B.IsSymm := idForm_isSymm hU n
  obtain ⟨L₁, M₁, hL₁, hM₁, hL₁M₁, hVL₁, hVM₁⟩ := hdec.exists_two_active
  let ι := {L : Subgroup ↥Ahat // Nat.card L = p ∧ lineSpace ρ B L ≠ ⊥}
  let i₁ : ι := ⟨L₁, hL₁, hVL₁⟩
  let Z : ι → Submodule K (Fin n → K) := fun i => if i = i₁ then fixedSpace ρ ⊤ else ⊥
  let W : ι → Submodule K (Fin n → K) := fun i => lineSpace ρ B i.1 ⊔ Z i
  have hZV : ∀ i, Z i ≤ fixedSpace ρ ⊤ := fun i => by
    simp only [Z]
    split_ifs
    · exact le_rfl
    · exact bot_le
  have hZdisj : ∀ i j : ι, i ≠ j → Z i = ⊥ ∨ Z j = ⊥ := fun i j hij => by
    by_cases hi : i = i₁
    · right
      have hj : j ≠ i₁ := fun hj => hij (hi.trans hj.symm)
      simp [Z, hj]
    · left
      simp [Z, hi]
  have hWle : ∀ i : ι, W i ≤ fixedSpace ρ ⊤ ⊔ lineSpace ρ B i.1 := fun i =>
    sup_le le_sup_right (le_sup_of_le_left (hZV i))
  have hA : ∀ i : ι, Centers.AllCenters H (W i) := fun i v hv hvi =>
    hAll i.1 i.2.1 v (hWle i hv) hvi
  have hON : ∀ i : ι, Centers.HasONBasis σ (W i) := by
    intro i
    by_cases hi : i = i₁
    · have hZi : Z i = fixedSpace ρ ⊤ := by simp [Z, hi]
      have hsep : (B.domRestrict₁₂ (W i) (W i)).SeparatingLeft := by
        refine separatingLeft_sup hBsymm (hdec.nondegenerate_line i.1 i.2.1) ?_ ?_
        · rw [hZi]
          exact hdec.nondegenerate_fixed
        · intro u hu v hv
          rw [hZi] at hv
          rw [← hBsymm.eq v u, hdec.orthogonal_fixed_line i.1 i.2.1 v hv u hu, map_zero]
      have hle : Module.finrank K (lineSpace ρ B i.1) ≤ Module.finrank K (W i) :=
        Submodule.finrank_mono le_sup_left
      refine hasONBasis_of_separatingLeft hU (W i) hsep ?_
      rcases hdimOK i.1 i.2.1 i.2.2 with h | ⟨h, hs⟩
      · exact Or.inl (by omega)
      · exact Or.inr ⟨by omega, hs⟩
    · have hZi : Z i = ⊥ := by simp [Z, hi]
      have hWi : W i = lineSpace ρ B i.1 := by simp [W, hZi]
      rw [hWi]
      exact hasONBasis_of_separatingLeft hU _ (hdec.nondegenerate_line i.1 i.2.1)
        (hdimOK i.1 i.2.1 i.2.2)
  have horthB : ∀ i j : ι, i ≠ j → ∀ u ∈ W i, ∀ v ∈ W j, B u v = 0 := by
    intro i j hij
    have hne : i.1 ≠ j.1 := fun h => hij (Subtype.ext h)
    have hVV := hdec.orthogonal_line_line i.1 j.1 i.2.1 j.2.1 hne
    refine forall_sup_sup hVV ?_ ?_ ?_
    · intro x hx y hy
      have hy' := hZV j hy
      rw [← hBsymm.eq y x, hdec.orthogonal_fixed_line i.1 i.2.1 y hy' x hx, map_zero]
    · intro x hx y hy
      exact hdec.orthogonal_fixed_line j.1 j.2.1 x (hZV i hx) y hy
    · intro x hx y hy
      rcases hZdisj i j hij with h | h
      · rw [h] at hx
        rw [(Submodule.mem_bot K).mp hx, map_zero, LinearMap.zero_apply]
      · rw [h] at hy
        rw [(Submodule.mem_bot K).mp hy, map_zero]
  have horth : ∀ i j : ι, i ≠ j → ∀ u ∈ W i, ∀ v ∈ W j, herm σ u v = 0 :=
    fun i j hij u hu v hv => by
      rw [← idForm_eq_herm hU]
      exact horthB i j hij u hu v hv
  have htop : ⨆ i : ι, W i = ⊤ := by
    refine top_unique ?_
    rw [← hdec.sup_eq_top]
    refine iSup_le fun k => ?_
    rcases k with _ | L
    · exact le_iSup_of_le i₁ (by
        change fixedSpace ρ ⊤ ≤ lineSpace ρ B L₁ ⊔ Z i₁
        have : Z i₁ = fixedSpace ρ ⊤ := by simp [Z]
        rw [this]
        exact le_sup_right)
    · by_cases hV : lineSpace ρ B L.1 = ⊥
      · change lineSpace ρ B L.1 ≤ _
        rw [hV]
        exact bot_le
      · exact le_iSup_of_le ⟨L.1, L.2, hV⟩ le_sup_left
  have hmix : ∀ i j : ι, i ≠ j → ∃ w₁ ∈ W i, ∃ w₂ ∈ W j, w₁ ≠ 0 ∧ w₂ ≠ 0 ∧
      Centers.IsCenter H (w₁ + w₂) := by
    intro i j hij
    have hne : i.1 ≠ j.1 := fun h => hij (Subtype.ext h)
    obtain ⟨x, hxA, hx1, a, ha1, ⟨v, hvL, hva, hv0⟩, ⟨w, hwM, hwa, hw0⟩⟩ :=
      exists_mixing_factor S hdec hpq1 i.2.1 j.2.1 hne i.2.2 j.2.2
    set xabs : LinearMap.GeneralLinearGroup K (Fin n → K) := toLinU hU n (liftUnitary x)
      with hxabs
    have hxmem : xabs ∈ sesqUnitaryGroup B := toLinU_mem _
    have hsq : Squarefree (minpoly K (xabs : Module.End K (Fin n → K))) :=
      (S.planeData hxA).squarefree_minpoly
    have hVMon : Centers.HasONBasis σ (lineSpace ρ B j.1) :=
      hasONBasis_of_separatingLeft hU _ (hdec.nondegenerate_line j.1 j.2.1)
        (hdimOK j.1 j.2.1 j.2.2)
    have hKI : ∀ w ∈ lineSpace ρ B j.1, w ≠ 0 →
        ∃ w₀ ∈ lineSpace ρ B j.1, B w₀ w₀ = 0 ∧ B w w₀ ≠ 0 := by
      intro w hw hw0
      obtain ⟨w₀, hw₀, h1, h2⟩ := exists_isotropic_pairing hσ hVMon hw hw0
      exact ⟨w₀, hw₀, by rw [hBdef, idForm_eq_herm]; exact h1,
        by rw [hBdef, idForm_eq_herm]; exact h2⟩
    have hdeg : dualPoly hU.bar (a.1 : K[X]) = a.1 → 2 ≤ (a.1 : K[X]).natDegree := by
      intro hself
      have hfd : (a.1 : K[X]) ∣ X ^ p - 1 := primaryFactor_dvd_pow_sub_one S ⟨x, hxA⟩ a.1.2
      have hfmon := monic_of_mem_primaryFactors a.1.2
      have hne1 := natDegree_ne_one_of_selfDual (h := hU) S.prime hpq1 hfmon hfd ha1 hself
      have hpos : 0 < (a.1 : K[X]).natDegree :=
        (irreducible_of_mem_primaryFactors a.1.2).natDegree_pos
      omega
    obtain ⟨g, hg, hgdet, w₀, hw₀, hw₀0, hw₀i, u'', hu'', w'', hw'', hu''0, hw''0, hgw⟩ :=
      Mixing.exists_mixing_element (a := a.1) hBsymm (idForm_separatingLeft hU n) hxmem hsq hdeg
        (fun s hs => lineSpace_stable S ⟨x, hxA⟩ hs) (fun s hs => lineSpace_stable S ⟨x, hxA⟩ hs)
        (disjoint_lineSpace hdec i.2.1 j.2.1 hne)
        (hdec.orthogonal_line_line i.1 j.1 i.2.1 j.2.1 hne) (hdec.nondegenerate_line i.1 i.2.1)
        (hdec.nondegenerate_line j.1 j.2.1) hKI hvL hva hv0 hwM hwa hw0
    have hgsesq := (mem_unitaryCentralizer.mp hg).1
    have hgcomm := (mem_unitaryCentralizer.mp hg).2
    obtain ⟨gS, hgS⟩ : ∃ gS : SUid σ n, ∀ v, gS • v = (g : Module.End K (Fin n → K)) v := by
      let gm : GL (Fin n) K := Matrix.GeneralLinearGroup.toLin.symm g
      have hgm : ∀ v, (gm : Matrix (Fin n) (Fin n) K) *ᵥ v = (g : Module.End K (Fin n → K)) v := by
        intro v
        have h1 : (Matrix.GeneralLinearGroup.toLin gm : LinearMap.GeneralLinearGroup K (Fin n → K))
            = g := MulEquiv.apply_symm_apply _ g
        have h2 := congrArg (fun φ : LinearMap.GeneralLinearGroup K (Fin n → K) =>
          (φ : Module.End K (Fin n → K)) v) h1
        simpa [Matrix.GeneralLinearGroup.coe_toLin, Matrix.toLin'_apply] using h2
      have heq : (g : Module.End K (Fin n → K)) = Matrix.toLin' (gm : Matrix (Fin n) (Fin n) K) :=
        LinearMap.ext fun v => by rw [Matrix.toLin'_apply, hgm]
      refine ⟨⟨gm, (mem_SUid_iff σ).mpr ⟨?_, fun v w => ?_⟩⟩, fun v => hgm v⟩
      · rw [← LinearMap.det_toLin', ← heq]
        exact hgdet
      · rw [hgm, hgm, ← idForm_eq_herm hU, ← idForm_eq_herm hU]
        exact hgsesq v w
    have hcommS : gS * toS ⟨x, hxA⟩ = toS ⟨x, hxA⟩ * gS := by
      refine ext_smul σ fun v => ?_
      rw [mul_smul, mul_smul, ← hact, ← hact, hgS, hgS]
      exact LinearMap.congr_fun hgcomm.eq v
    have hgH : gS ∈ H := hHmem gS x hxA hx1 (by
      have := congrArg (fun z : SUid σ n => (z : GL (Fin n) K)) hcommS
      simpa [toS] using this)
    have hCw₀ : Centers.IsCenter H w₀ := hAll j.1 j.2.1 w₀ (Submodule.mem_sup_right hw₀)
      (by rw [← idForm_eq_herm hU]; exact hw₀i)
    have hCg := hCw₀.map hgH
    rw [hgS, hgw] at hCg
    exact ⟨u'', (le_sup_left : lineSpace ρ B i.1 ≤ W i) hu'', w'',
      (le_sup_left : lineSpace ρ B j.1 ≤ W j) hw'', hu''0, hw''0, hCg⟩
  have hn4 : 4 ≤ n := by
    have hdisj := disjoint_lineSpace hdec hL₁ hM₁ hL₁M₁
    have h1 := hfin L₁ hL₁ hVL₁
    have h2 := hfin M₁ hM₁ hVM₁
    have h3 := Submodule.finrank_sup_add_finrank_inf_eq (lineSpace ρ B L₁) (lineSpace ρ B M₁)
    rw [hdisj.eq_bot, finrank_bot] at h3
    have h4 := Submodule.finrank_le (lineSpace ρ B L₁ ⊔ lineSpace ρ B M₁)
    rw [Module.finrank_fin_fun] at h4
    omega
  have : Finite ι := Subtype.finite
  have : Fintype ι := Fintype.ofFinite ι
  have : Nonempty ι := ⟨i₁⟩
  have hHtop : H = ⊤ := Centers.eq_top_of_blocks hσ hn4 W hON horth hA hmix htop
  have hmem : (⟨g, by rw [hSG]; exact hg⟩ : SUid σ n) ∈ H := hHtop ▸ Subgroup.mem_top _
  exact hmem

end Core

end Nonsplit

open Nonsplit in
theorem unitarySUNonsplit : UnitarySUNonsplit := by
  intro ℓ f p n K _ hU hp hp5 hpℓ hpq1 hpq hn E hcomm hexp hcard
  classical
  have := hU.finite
  have : Fact ℓ.Prime := ⟨hU.prime⟩
  have : CharP K ℓ := hU.charP
  have hGG : unitarySU ℓ f K n = CFSG.ClassicalGroups.UnitaryFlag.gramSU hU
      (CFSG.RankThree.PartOne.KCUnitaryModel.idGram K n) := unitarySU_eq_gramSU hU n
  have hinj : Function.Injective (Subgroup.inclusion hGG.le) := Subgroup.inclusion_injective hGG.le
  let Ahat : Subgroup (CFSG.ClassicalGroups.UnitaryFlag.gramSU hU
      (CFSG.RankThree.PartOne.KCUnitaryModel.idGram K n)) := E.map (Subgroup.inclusion hGG.le)
  have hAmem : ∀ x : CFSG.ClassicalGroups.UnitaryFlag.gramSU hU
      (CFSG.RankThree.PartOne.KCUnitaryModel.idGram K n), x ∈ Ahat ↔
      ∃ e ∈ E, Subgroup.inclusion hGG.le e = x := fun x => Subgroup.mem_map
  have hAcard : Nat.card Ahat = p ^ 2 := by
    rw [← hcard]
    exact Subgroup.card_map_of_injective hinj
  have hAel : CFSG.IsElementaryAbelian p Ahat := by
    refine (CFSG.SectionRank.isElementaryAbelian_iff_isElemAbelian p Ahat).mpr
      ⟨⟨⟨fun a b => ?_⟩⟩, fun x hx => ?_⟩
    · obtain ⟨e₁, he₁, h₁⟩ := (hAmem a.1).mp a.2
      obtain ⟨e₂, he₂, h₂⟩ := (hAmem b.1).mp b.2
      refine Subtype.ext ?_
      change a.1 * b.1 = b.1 * a.1
      rw [← h₁, ← h₂, ← map_mul, ← map_mul, hcomm e₁ he₁ e₂ he₂]
    · obtain ⟨e, he, h1⟩ := (hAmem x).mp hx
      rw [← h1, ← map_pow, hexp e he, map_one]
  have h2e : 2 * ordNegQ ℓ f p ≤ n := CFSG.RankThree.PartOne.CTP.two_mul_ordNegQ_le hU hp hpℓ E
    hexp hcard
  have he3 : 3 ≤ ordNegQ ℓ f p := three_le_ordNegQ hp hp5 hU.prime hpℓ hU.one_le hpq1 hpq
  have hS : CFSG.RankThree.PartOne.KCUnitaryExact.PlaneSetup hU n p Ahat :=
    { three_le := hn
      ne := fun h => by omega
      prime := hp
      ne_char := hpℓ
      noTorsion := fun c hc _ hcp => by
        have h1 : (c : K) ^ (ℓ ^ f + 1) = 1 := by rw [← hU.norm_eq_pow]; exact hc
        have h2 : c ^ (ℓ ^ f + 1) = 1 := Units.ext (by simpa using h1)
        have hgcd : Nat.gcd p (ℓ ^ f + 1) = 1 := (Nat.Prime.coprime_iff_not_dvd hp).mpr hpq1
        have h3 : c ^ Nat.gcd p (ℓ ^ f + 1) = 1 := pow_gcd_eq_one.mpr ⟨hcp, h2⟩
        rwa [hgcd, pow_one] at h3
      elem := hAel
      card := hAcard }
  rw [eq_top_iff]
  intro g _
  have hgmem : (g : GL (Fin n) K) ∈ CFSG.ClassicalGroups.UnitaryFlag.gramSU hU
      (CFSG.RankThree.PartOne.KCUnitaryModel.idGram K n) := hGG ▸ g.2
  have hmain := mem_closure_centralizers hU hp5 hpq1 hpq hS (g : GL (Fin n) K) hgmem
  let S₀ : Set (unitarySU ℓ f K n) := {g | ∃ x ∈ E, x ≠ 1 ∧ g * x = x * g}
  have himg : (unitarySU ℓ f K n).subtype '' S₀ = {g : GL (Fin n) K |
      g ∈ CFSG.ClassicalGroups.UnitaryFlag.gramSU hU
        (CFSG.RankThree.PartOne.KCUnitaryModel.idGram K n) ∧
      ∃ x : CFSG.ClassicalGroups.UnitaryFlag.gramSU hU
        (CFSG.RankThree.PartOne.KCUnitaryModel.idGram K n), x ∈ Ahat ∧ x ≠ 1 ∧
        g * (x : GL (Fin n) K) = (x : GL (Fin n) K) * g} := by
    ext g'
    constructor
    · rintro ⟨g₀, ⟨x, hx, hx1, hcomm'⟩, rfl⟩
      refine ⟨hGG ▸ g₀.2, Subgroup.inclusion hGG.le x, (hAmem _).mpr ⟨x, hx, rfl⟩,
        fun h => hx1 (hinj (by rw [h, map_one])), ?_⟩
      have := congrArg (fun z : unitarySU ℓ f K n => (z : GL (Fin n) K)) hcomm'
      simpa using this
    · rintro ⟨hg', x', hx', hx'1, hcomm'⟩
      obtain ⟨x, hx, rfl⟩ := (hAmem x').mp hx'
      refine ⟨⟨g', hGG ▸ hg'⟩, ⟨x, hx, fun h => hx'1 (by rw [h, map_one]), Subtype.ext ?_⟩, rfl⟩
      simpa using hcomm'
  rw [← himg, ← MonoidHom.map_closure] at hmain
  obtain ⟨y, hy, hyg⟩ := hmain
  have hyg' : y = g := Subtype.ext hyg
  rw [← hyg']
  exact hy


theorem unitarySUNontoral : UnitarySUNontoral := unitarySUNontoral_of_nonsplit unitarySUNonsplit

open CFSG.AGLEmbeddingD2 in
theorem kFactSeitzRankTwo_of_remaining_leaves (hO : OrthogonalOddPlanes)
    (hP : OrthogonalPlusPlanes) (hM : OrthogonalMinusPlanes) (hN : SeitzInnerClassicalNonab)
    (hX : SeitzInnerExceptionalFive) (h3 : SeitzInnerThree) (ho : KFactSeitzRankTwoOuter) :
    KFactSeitzRankTwo :=
  kFactSeitzRankTwo_of_nonsplit_leaves unitarySUNonsplit hO hP hM hN hX h3 ho

end CFSG.LieType.SeitzGeneration
