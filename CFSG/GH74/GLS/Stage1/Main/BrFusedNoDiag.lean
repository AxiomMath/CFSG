module

public import CFSG.GH74.GLS.Stage2.Final.ModelInvolE
public import CFSG.GH74.GLS.Stage1.Main.BrFusedL4
public import CFSG.GH74.GLS.Stage2.Local.Lemma23

public section

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Blueprint CFSG.Assembly.LowTwoRank CFSG.GH74.L5U5 Matrix
  CFSG.GH74.GLS.Stage2.Local CFSG.GH74.GLS.Stage2.Final CFSG.GH74.GLS.Stage2.Final.ModelBlock
  CFSG.GH74.GLS.LU.Local

namespace CFSG.GH74.GLS.Stage1.Main

@[expose] def NoDiagInv {X : Type} [Group X] (z' : X) (E₁ E₂ : Subgroup X) : Prop :=
  ∀ x : X, x ∈ centralizer ({z'} : Set X) → x ∈ normalizer (E₁ : Set X) → x * x = 1 → x ∈ E₁ ⊔ E₂

theorem NoDiagInv.map {X Y : Type} [Group X] [Group Y] (Φ : X ≃* Y) {z : X} {E₁ E₂ : Subgroup X}
    (h : NoDiagInv z E₁ E₂) :
    NoDiagInv (Φ z) (E₁.map Φ.toMonoidHom) (E₂.map Φ.toMonoidHom) := by
  intro y hyC hyN hy2
  have hxC : Φ.symm y ∈ centralizer ({z} : Set X) := by
    rw [mem_centralizer_singleton_iff] at hyC ⊢
    apply Φ.injective
    rw [map_mul, map_mul, MulEquiv.apply_symm_apply]
    exact hyC
  have hxN : Φ.symm y ∈ normalizer (E₁ : Set X) := by
    have := ModelLUT.normalizer_map Φ.symm hyN
    rwa [ModelLUT.map_symm_map] at this
  have hx2 : Φ.symm y * Φ.symm y = 1 := by
    rw [← map_mul, hy2, map_one]
  have h1 := h _ hxC hxN hx2
  have h3 : Φ (Φ.symm y) ∈ (E₁ ⊔ E₂).map Φ.toMonoidHom := Subgroup.mem_map_of_mem _ h1
  rw [MulEquiv.apply_symm_apply, Subgroup.map_sup] at h3
  exact h3

section ModelNI

variable {F : Type} [Field F]

theorem noDiagInv_lin [Finite F] (h2 : (2 : F) ≠ 0) (h5 : 5 ≤ Nat.card F) (h8 : Nat.card F % 8 = 5) :
    NoDiagInv (yP (ModelData.lin F)) (K1 (ModelData.lin F)) (K2 (ModelData.lin F)) :=
  fun _ hxC hxN hx2 =>
    invol_Cg_N1_mem_E (goodModel_lin h2 h5) (hno8_lin h2 h8) (hi_lin (by omega)) hxC hxN hx2

theorem noDiagInv_uni [Finite F] {p f : ℕ} [Fact p.Prime] [CharP F p]
    (hF : Nat.card F = (p ^ f) ^ 2) (hp2 : p ≠ 2) (h5 : 5 ≤ p ^ f) (h8 : p ^ f % 8 = 3) :
    NoDiagInv (yP (ModelData.uni hF)) (K1 (ModelData.uni hF)) (K2 (ModelData.uni hF)) :=
  fun _ hxC hxN hx2 =>
    invol_Cg_N1_mem_E (goodModel_uni hF hp2 h5)
      (hno8_uni hF (goodModel_uni hF hp2 h5).two_ne_zero h8) (hi_uni hF h8) hxC hxN hx2

theorem fusedPkg_transferNI {Gs : Type} [Group Gs] [Finite Gs] [Finite F] {M : ModelData F}
    (e : Gs ≃* PG M) {S₀ : Sylow 2 (PG M)} (hS₀ : CenterIs (S₀ : Subgroup (PG M)) (yP M))
    (h2 : (2 : F) ≠ 0) (S' : Sylow 2 Gs) (z' : Gs)
    (hz' : (Subgroup.center ↥(S' : Subgroup Gs)).map (S' : Subgroup Gs).subtype = Subgroup.zpowers z')
    {q : ℕ} {ε : ℤ} {t u n : PG M}
    (hdata : FusedPkg (PG M) q ε (yP M) S₀ (K1 M) (K2 M) t u n)
    (hNI : NoDiagInv (yP M) (K1 M) (K2 M)) :
    ∃ (E₁' E₂' : Subgroup Gs) (t' u' n' : Gs),
      FusedPkg Gs q ε z' S' E₁' E₂' t' u' n' ∧ NoDiagInv z' E₁' E₂' := by
  obtain ⟨Φ, hΦ⟩ := exists_equiv_sylow e S₀ S'
  have hz'c : CenterIs (S' : Subgroup Gs) z' := (centerIs_iff _ _).1 hz'
  have hΦz : Φ z' = yP M := equiv_center_eq Φ (orderOf_yP M h2) hΦ hz'c hS₀
  have hS : (S₀ : Subgroup (PG M)) = (S' : Subgroup Gs).map Φ.toMonoidHom := hΦ.symm
  have key := FusedPkg.map Φ.symm (S := S₀) (S' := S') (by
    rw [hS, CFSG.GH74.GLS.Stage2.Final.ModelLUT.map_symm_map]) hdata
  have hNI' := hNI.map Φ.symm
  have hz : Φ.symm (yP M) = z' := by rw [← hΦz]; simp
  rw [hz] at key hNI'
  exact ⟨_, _, _, _, _, key, hNI'⟩

end ModelNI

theorem fusedModelLeafNI :
    ∀ (Gs : Type) [Group Gs] [Finite Gs] (p f : ℕ), p.Prime → p ≠ 2 → 5 ≤ p ^ f →
      ∀ (S' : Sylow 2 Gs) (z' : Gs),
        (center ↥(S' : Subgroup Gs)).map (S' : Subgroup Gs).subtype = zpowers z' →
        ((p ^ f % 8 = 5 ∧ LieModel Gs .PSL 4 p f) →
          ∃ (E₁ E₂ : Subgroup Gs) (t' u' n' : Gs),
            FusedPkg Gs (p ^ f) 1 z' S' E₁ E₂ t' u' n' ∧ NoDiagInv z' E₁ E₂) ∧
        ((p ^ f % 8 = 3 ∧ LieModel Gs .PSU 4 p f) →
          ∃ (E₁ E₂ : Subgroup Gs) (t' u' n' : Gs),
            FusedPkg Gs (p ^ f) (-1) z' S' E₁ E₂ t' u' n' ∧ NoDiagInv z' E₁ E₂) := by
  intro Gs _ _ p f hp hp2 hq S' z' hz'
  constructor
  · rintro ⟨h8, hL⟩
    obtain ⟨hf, F, iF, fF, hF, ⟨e⟩⟩ := lieModel_psl_unpack hL
    have h2 : (2 : F) ≠ 0 := CFSG.ClassicalInvolution.two_ne_zero_of_card_eq_prime_pow hp hp2 hF
    have h5 : 5 ≤ Nat.card F := by rw [hF]; exact hq
    have h8' : Nat.card F % 8 = 5 := by rw [hF]; exact h8
    obtain ⟨S₀, t, u, n, hd⟩ := fusedPkg_lin h2 h5 h8'
    rw [hF] at hd
    exact fusedPkg_transferNI (show Gs ≃* PG (ModelData.lin F) from e)
      ((centerIs_iff _ _).1 hd.data.syl.z_cen) h2 S' z' hz' hd (noDiagInv_lin h2 h5 h8')
  · rintro ⟨h8, hU⟩
    obtain ⟨hf, F, iF, fF, hF, ⟨e⟩⟩ := lieModel_psu_unpack hU
    have : Fact p.Prime := ⟨hp⟩
    have hF' : Nat.card F = p ^ (2 * f) := by rw [hF, ← pow_mul, mul_comm]
    have : CharP F p := by
      have := Fintype.ofFinite F
      exact charP_of_card_eq_prime_pow (f := 2 * f) (by rw [← Nat.card_eq_fintype_card]; exact hF')
    have h2 : (2 : F) ≠ 0 := CFSG.ClassicalInvolution.two_ne_zero_of_card_eq_prime_pow hp hp2 hF'
    obtain ⟨S₀, t, u, n, hd⟩ := fusedPkg_uni hF hp2 hq h8
    exact fusedPkg_transferNI (show Gs ≃* PG (ModelData.uni hF) from e)
      ((centerIs_iff _ _).1 hd.data.syl.z_cen) h2 S' z' hz' hd (noDiagInv_uni hF hp2 hq h8)

theorem fused_ctx_ni_of {G : Type} [Group G] [Finite G] {z : G}
    {S : Subgroup G} (hcen : Cen2 G z S) {ε : Bool} {Gs : Type} [Group Gs] [Finite Gs] {p f : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2)
    (hm : (ε = true ∧ p ^ f % 8 = 5 ∧ LieModel Gs .PSL 4 p f) ∨
      (ε = false ∧ p ^ f % 8 = 3 ∧ 3 < p ^ f ∧ LieModel Gs .PSU 4 p f))
    (hS : ∃ S' : Sylow 2 Gs, Nonempty (↥S ≃* ↥(S' : Subgroup Gs)))
    (hC : ∀ (z' : Gs) (S' : Sylow 2 ↥(centralizer ({z'} : Set Gs))), IsCentralInvolution z' →
      ∀ S'' : Sylow 2 Gs, Nonempty (↥S ≃* ↥(S'' : Subgroup Gs)) →
        (S'' : Subgroup Gs) = (S' : Subgroup ↥(centralizer ({z'} : Set Gs))).map
            (centralizer ({z'} : Set Gs)).subtype →
          Nonempty (↥(Stage1.Thm3.Sec8.layerSBar z S) ≃* ↥(Stage1.Thm3.Sec8.layerSBar z' (S'' : Subgroup Gs)))) :
    ∃ C : FusedCtx z S ε Gs p f, NoDiagInv C.z₁ C.E₁ C.E₂ := by
  have hfus := CFSG.GH74.GLS.Stage1.Main.fusedModelLeafNI
  obtain ⟨S₁, hSS₁⟩ := hS
  have hq5 : 5 ≤ p ^ f ∧ 3 < p ^ f := by
    rcases hm with ⟨-, h8, -⟩ | ⟨-, h8, h3, -⟩ <;> omega
  have hGs : IsClassicalModel Gs p f ∧ (LieModel Gs .PSL 4 p f ∨ LieModel Gs .PSU 4 p f) := by
    rcases hm with ⟨-, h8, hL⟩ | ⟨-, h8, -, hL⟩
    · exact ⟨⟨hp, hp2, hq5.2, Or.inr (Or.inl ⟨by omega, hL⟩)⟩, Or.inl hL⟩
    · exact ⟨⟨hp, hp2, hq5.2, Or.inr (Or.inr ⟨by omega, hL⟩)⟩, Or.inr hL⟩
  obtain ⟨hGsm, hLU0⟩ := hGs
  obtain ⟨z₁, hz₁o, hcen₁⟩ := modelCenter Gs p f hGsm S₁
  obtain ⟨E₁, E₂, t₁, u₁, n₁, hpkg, hNI⟩ : ∃ (E₁ E₂ : Subgroup Gs) (t u n : Gs),
      FusedPkg Gs (p ^ f) (if ε then 1 else -1) z₁ S₁ E₁ E₂ t u n ∧ NoDiagInv z₁ E₁ E₂ := by
    rcases hm with ⟨hε, h8, hL⟩ | ⟨hε, h8, -, hL⟩
    · subst hε
      simpa using (hfus Gs p f hp hp2 hq5.1 S₁ z₁ hcen₁).1 ⟨h8, hL⟩
    · subst hε
      simpa using (hfus Gs p f hp hp2 hq5.1 S₁ z₁ hcen₁).2 ⟨h8, hL⟩
  obtain ⟨Ψ, hΨ⟩ := exists_fused_psi hcen hGsm hLU0 S₁ hSS₁ hz₁o hcen₁ hC
  exact ⟨⟨S₁, z₁, E₁, E₂, t₁, u₁, n₁, hpkg, Ψ, hΨ⟩, hNI⟩

theorem fused_noDiag {G : Type} [Group G] [Finite G] {z : G} {S : Subgroup G} {ε : Bool}
    (hcen : Cen2 G z S) (hE : L4U4TermTypeE ε G z S) :
    ∀ y ∈ S1 S z, y * y = 1 → y ∈ RC S z := by
  obtain ⟨-, Gs, iGs, fGs, p, f, hp, hp2, hm, hS, hC⟩ := hE
  obtain ⟨C, hNI⟩ := fused_ctx_ni_of hcen hp hp2 hm hS hC
  intro y hy hy2
  obtain ⟨hyS, hyC, -⟩ := mem_S1_iff.1 hy
  have hyB : toBar z ⟨y, hyC⟩ ∈ SBar (S1 S z) z := ⟨⟨y, hyC⟩, hy, rfl⟩
  rw [C.T_eq hcen] at hyB
  obtain ⟨hyΓ, hw⟩ := (C.mem_pull_iff _ _).1 hyB
  have hwC : ((C.Ψ ⟨toBar z ⟨y, hyC⟩, hyΓ⟩ : ↥C.X) : Gs) ∈ centralizer ({C.z₁} : Set Gs) :=
    C.S₁_le_Cen hw.1
  have hy2' : (⟨toBar z ⟨y, hyC⟩, hyΓ⟩ : ↥(Stage1.Thm3.Sec8.layerSBar z S)) *
      ⟨toBar z ⟨y, hyC⟩, hyΓ⟩ = 1 := by
    apply Subtype.ext
    show toBar z ⟨y, hyC⟩ * toBar z ⟨y, hyC⟩ = 1
    rw [← map_mul]
    have : (⟨y, hyC⟩ : ↥(Cen z)) * ⟨y, hyC⟩ = 1 := Subtype.ext hy2
    rw [this, map_one]
  have hw2 : ((C.Ψ ⟨toBar z ⟨y, hyC⟩, hyΓ⟩ : ↥C.X) : Gs) * ((C.Ψ ⟨toBar z ⟨y, hyC⟩, hyΓ⟩ : ↥C.X) : Gs) = 1 := by
    have h1 : C.Ψ (⟨toBar z ⟨y, hyC⟩, hyΓ⟩ * ⟨toBar z ⟨y, hyC⟩, hyΓ⟩) = 1 := by rw [hy2', map_one]
    rw [map_mul] at h1
    exact congrArg (fun x : ↥C.X => (x : Gs)) h1
  have hwE := hNI _ hwC hw.2 hw2
  have hybar : toBar z ⟨y, hyC⟩ ∈ LBar z := by
    rw [C.LBar_eq_pull hcen]
    exact (C.mem_pull_iff _ _).2 ⟨hyΓ, hwE⟩
  have hord : ∃ a : ℕ, orderOf y = 2 ^ a := by
    have h1 : orderOf y ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact hy2)
    rcases (Nat.dvd_prime Nat.prime_two).1 h1 with h | h
    · exact ⟨0, by simpa using h⟩
    · exact ⟨1, by simpa using h⟩
  exact ⟨hyS, mem_LC_of_toBar_mem z hyC hord hybar⟩

theorem noDiag_isCentralInvolution_of_isConj {G : Type} [Group G] {z x : G}
    (hz : IsCentralInvolution z) (h : IsConj z x) : IsCentralInvolution x := by
  obtain ⟨hord, S₀, hzS, hzc⟩ := hz
  obtain ⟨c, hc⟩ := isConj_iff.1 h
  refine ⟨?_, c • S₀, ?_, ?_⟩
  · have h1 := MulEquiv.orderOf_eq (MulAut.conj c) z
    rw [MulAut.conj_apply] at h1
    rw [← hc, h1]
    exact hord
  · rw [Sylow.coe_subgroup_smul, Subgroup.pointwise_smul_def]
    exact ⟨z, hzS, by rw [← hc]; rfl⟩
  · intro s hs
    rw [Sylow.coe_subgroup_smul, Subgroup.pointwise_smul_def] at hs
    obtain ⟨s', hs', rfl⟩ := hs
    have := hzc s' hs'
    rw [← hc]
    show (c * s' * c⁻¹) * (c * z * c⁻¹) = (c * z * c⁻¹) * (c * s' * c⁻¹)
    calc (c * s' * c⁻¹) * (c * z * c⁻¹) = c * (s' * z) * c⁻¹ := by group
      _ = c * (z * s') * c⁻¹ := by rw [this]
      _ = (c * z * c⁻¹) * (c * s' * c⁻¹) := by group

theorem noDiag_of_twoClass {G : Type} [Group G] [Finite G] {z : G} {S : Subgroup G} {q : ℕ}
    {L₁ L₂ : Subgroup (CentralizerBar z)} {x : G} (hc : IsCentralInvolution z)
    (hx : TwoClassData G z S L₁ L₂ q x) :
    (∀ u v : G, orderOf u = 2 → orderOf v = 2 → IsConj u v) →
      ∀ y ∈ S1 S z, y * y = 1 → y ∈ RC S z :=
  fun hone => (hx.x_nonCentral (noDiag_isCentralInvolution_of_isConj hc
    (hone z x hc.1 hx.x_inv))).elim

end CFSG.GH74.GLS.Stage1.Main
