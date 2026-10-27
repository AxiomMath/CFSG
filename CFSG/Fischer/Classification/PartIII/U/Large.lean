module

public import CFSG.Fischer.Classification.PartIII.U.Stars
public import CFSG.Fischer.Classification.PartIII.U.Defect

public section

namespace CFSG.Fischer.Classification.LocalU

open CFSG.Blueprint.Fischer CFSG.Fischer CFSG.Fischer.Classification
  CFSG.Fischer.Classification.Unitary CFSG.Fischer.Classification.LocalR3
  CFSG.ClassicalGroups.Unitary

variable {n : ℕ}

theorem exists_section_fun (hn : 1 ≤ n) {S : Set (PG (n + 2))}
    (hSsub : S ⊆ LocalClass (DG (n + 2)) (tq (v₀ n)))
    (hτ : ∀ a ∈ S, ∀ b ∈ S, a * b * a ∈ S)
    (hT : TwinFree (LocalClass (DG (n + 2)) (tq (v₀ n))) S)
    (hM : MeetsTwins (LocalClass (DG (n + 2)) (tq (v₀ n))) S) :
    ∃ γ : (Fin n → K) → K,
      (∀ x : Fin n → K, x ≠ 0 → herm frob x x = 0 → tq (sv (γ x) x) ∈ S) ∧
      (∀ x : Fin n → K, x ≠ 0 → herm frob x x = 0 → ∀ c : K, c ≠ 0 → γ (c • x) = c * γ x) ∧
      (∀ x x' : Fin n → K, x ≠ 0 → herm frob x x = 0 → x' ≠ 0 → herm frob x' x' = 0 →
        herm frob x x' ≠ 0 → γ (x' + herm frob x x' • x) = γ x' + herm frob x x' * γ x) := by
  have hex : ∀ x : Fin n → K, x ≠ 0 → herm frob x x = 0 → ∃ α, tq (sv α x) ∈ S := by
    intro x hx0 hx
    obtain ⟨b, hb, htw⟩ := hM _ (tq_sv_mem_localClass hn 0 hx0 hx)
    obtain ⟨β, y, hy0, hy, rfl⟩ := exists_sv_of_mem_localClass hn (hSsub hb)
    obtain ⟨c, rfl⟩ := (isTwin_sv_iff hn hx0 hx hy0 hy).1 htw
    have hc : c ≠ 0 := by rintro rfl; exact hy0 (zero_smul K x)
    refine ⟨c⁻¹ * β, ?_⟩
    rwa [(tq_sv_eq_tq_sv_iff (α := c⁻¹ * β) (α' := β) hn hx0 hx hy0 hy).2
      ⟨c, rfl, by field_simp⟩]
  have huniq : ∀ x : Fin n → K, x ≠ 0 → herm frob x x = 0 → ∀ α α' : K,
      tq (sv α x) ∈ S → tq (sv α' x) ∈ S → α = α' := by
    intro x hx0 hx α α' h h'
    have heq := hT _ h _ h' ((isTwin_sv_iff hn hx0 hx hx0 hx).2 ⟨1, (one_smul K x).symm⟩)
    obtain ⟨c, hc, hα⟩ := (tq_sv_eq_tq_sv_iff hn hx0 hx hx0 hx).1 heq
    have hc1 : c = 1 := by
      have h1 : (1 - c) • x = 0 := by rw [sub_smul, one_smul, ← hc, sub_self]
      exact (sub_eq_zero.1 ((smul_eq_zero.1 h1).resolve_right hx0)).symm
    rw [hα, hc1, one_mul]
  choose γ₀ hγ₀ using hex
  classical
  let γ : (Fin n → K) → K := fun x =>
    if h : x ≠ 0 ∧ herm frob x x = 0 then γ₀ x h.1 h.2 else 0
  have hγS : ∀ x : Fin n → K, x ≠ 0 → herm frob x x = 0 → tq (sv (γ x) x) ∈ S :=
    fun x hx0 hx => by
      have hγx : γ x = γ₀ x hx0 hx := dite_eq_left_of_eq_true (eq_true ⟨hx0, hx⟩)
      rw [hγx]
      exact hγ₀ x hx0 hx
  refine ⟨γ, hγS, fun x hx0 hx c hc => ?_, fun x x' hx0 hx hx0' hx' hxx' => ?_⟩
  · have hcx0 : c • x ≠ 0 := smul_ne_zero hc hx0
    have hcx : herm frob (c • x) (c • x) = 0 := by rw [herm_smul_smul_self hx]
    refine huniq _ hcx0 hcx _ _ (hγS _ hcx0 hcx) ?_
    rw [← (tq_sv_eq_tq_sv_iff hn hx0 hx hcx0 hcx).2 ⟨c, rfl, rfl⟩]
    exact hγS x hx0 hx
  · have hy0 : x' + herm frob x x' • x ≠ 0 := tvv_ne_zero hx hx0'
    have hy : herm frob (x' + herm frob x x' • x) (x' + herm frob x x' • x) = 0 := by
      have := herm_tvv_self (y := x) (z := x') hx
      rw [tvv] at this
      rw [this, hx']
    refine huniq _ hy0 hy _ _ (hγS _ hy0 hy) ?_
    rw [← tq_sv_mul_mul hx hx']
    exact hτ _ (hγS x hx0 hx) _ (hγS x' hx0' hx')

theorem false_of_localPG_large {G : Type} [Group G] {D : Set G} (hH : Hyp G D)
    (hnab : NonabelianCommutator G) {d : G} (hd : d ∈ D) (hn : 5 ≤ n)
    (φ : LocalQuotient D d ≃* PG (n + 2)) (hφ : φ '' LocalImages D d = DG (n + 2)) : False := by
  obtain ⟨hP, hZ, hS⟩ := hH
  have hna : ∃ a b : commutator G, a * b ≠ b * a := hnab
  have hPG := pair_DG (m := n + 2) (by omega)
  obtain ⟨x, hx, hxd⟩ : ∃ x ∈ D, x * d ≠ d * x := by
    by_contra! h
    have hdZ : d ∈ Subgroup.center G := (Pair.mem_center_iff hP).2 h
    rw [hZ, Subgroup.mem_bot] at hdZ
    exact Pair.ne_one hP hd hdZ
  obtain ⟨f₀, hf₀⟩ := Pair.muSet_nonempty hP (Pair.connected_of_nonabelian hP hS hna) hd hx hxd
  have hι₁ := isChart_of_localQuotientEquiv hP (Pair.starImage_injective_of_simple hP hZ hS hd)
    φ hφ
  obtain ⟨ψ, hψD, hψ⟩ := Pair.exists_mulEquiv hPG (hι₁.mem hf₀.1)
    (tq_mem_DG v₀_ne_zero herm_v₀_v₀)
  set φ' := φ.trans ψ with hφ'def
  have hφ' : φ' '' LocalImages D d = DG (n + 2) := by
    rw [hφ'def, MulEquiv.coe_trans, Set.image_comp, hφ, hψD]
  have hιf₀ : (φ' ∘ lqMap D d) f₀ = tq (v₀ n) := hψ
  have hF := muSections_DG (n := n) (by omega)
  set M := (φ' ∘ lqMap D d) '' muSet D d x with hMdef
  have hT := twinFree_inter hP hZ hS hd φ' hφ' hF hx hxd hf₀
  have hMe := meetsTwins_inter hP hZ hS hd φ' hφ' hF hx hxd hf₀
  rw [hιf₀] at hT hMe
  have hτ : ∀ a ∈ M ∩ LocalClass (DG (n + 2)) (tq (v₀ n)),
      ∀ b ∈ M ∩ LocalClass (DG (n + 2)) (tq (v₀ n)),
        a * b * a ∈ M ∩ LocalClass (DG (n + 2)) (tq (v₀ n)) := by
    rintro _ ⟨⟨a, ha, rfl⟩, ha'⟩ _ ⟨⟨b, hb, rfl⟩, hb'⟩
    exact ⟨mul_mul_mem_image_muSet hP φ' ha hb, Pair.mul_mul_mem_localClass_of_mem hPG ha' hb'⟩
  obtain ⟨γ, hγS, h1, h2⟩ := exists_section_fun (by omega) Set.inter_subset_right hτ hT hMe
  set i : Fin 5 ↪ Fin n := Fin.castLEEmb hn
  have hadd := map_add_eq γ h1 h2 i
  obtain ⟨ha0, ha, hb0, hb, hab0, hab⟩ := goodPair_std i
  set a := ee (i 0) + ee (i 1) with hadef
  set b := ee (i 2) + ee (i 3) with hbdef
  have hab' := herm_std i
  rw [← hadef, ← hbdef] at hab'
  set P := sv (γ a) a with hPdef
  set Q := sv (γ b) b with hQdef
  have hp := hγS a ha0 ha
  have hq := hγS b hb0 hb
  have hq' := hγS (a + b) hab0 hab
  have hQP : sv (γ (a + b)) (a + b) = Q + (1 : K) • P := by
    rw [one_smul, hadd, hPdef, hQdef, sv_add, add_comm (γ b), add_comm b]
  rw [hQP] at hq'
  have hPQ : herm frob P Q = 0 := by rw [hPdef, hQdef, herm_sv_sv, hab']
  have hQnP : ∀ c : K, Q ≠ c • P := fun c h => std_ne_smul i c (by
    have := congrArg (π n) h
    rwa [hQdef, hPdef, π_sv, map_smul, π_sv] at this)
  have htw := isTwin_add_smul (by omega) (sv_ne_zero _ ha0) (isotropic_sv _ ha)
    (sv_ne_zero _ hb0) (isotropic_sv _ hb) hPQ hQnP 1
  obtain ⟨⟨f₁, hf₁, hf₁P⟩, -⟩ := hp
  have hT₁ := twinFree_inter hP hZ hS hd φ' hφ' hF hx hxd hf₁
  rw [hf₁P] at hT₁
  have heq := hT₁ _ ⟨hq.1, htw.1⟩ _ ⟨hq'.1, htw.2.1⟩ htw
  rw [← hQP] at heq
  obtain ⟨c, hc, -⟩ := (tq_sv_eq_tq_sv_iff (by omega) hb0 hb hab0 hab).1 heq
  have := congrFun hc (i 0)
  simp [hadef, hbdef] at this

end CFSG.Fischer.Classification.LocalU

namespace CFSG.Fischer.Classification

open CFSG.Blueprint.Fischer CFSG.Fischer CFSG.Fischer.Classification.Unitary
  CFSG.Fischer.Classification.LocalU

theorem false_of_localU2_large {G : Type} [Group G] {D : Set G} (hH : Hyp G D)
    (hnab : NonabelianCommutator G) {d : G} (hd : d ∈ D) {m : ℕ} (hm : 7 ≤ m)
    (φ : LocalQuotient D d ≃* U2 m) (hφ : φ '' LocalImages D d = DU m) : False := by
  obtain ⟨n, rfl⟩ : ∃ n, m = n + 2 := ⟨m - 2, by omega⟩
  refine false_of_localPG_large hH hnab hd (by omega) (φ.trans (u2Equiv (n + 2))) ?_
  rw [MulEquiv.coe_trans, Set.image_comp, hφ, image_DU]

theorem false_of_local_case4_large {G : Type} [Group G] {D : Set G} (hH : Hyp G D)
    (hnab : NonabelianCommutator G) {d : G} (hd : d ∈ D) {m : ℕ} (hm : 7 ≤ m)
    (h : CFSG.Open.fischerCentralQuotientModel (LocalImages D d) (SUm m) (TU m)) : False := by
  obtain ⟨φ, hφ⟩ := fischerCentralQuotientModel_iff_U2.1 h
  exact false_of_localU2_large hH hnab hd hm φ hφ

end CFSG.Fischer.Classification
