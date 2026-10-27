module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.S172ALayerFull
public import CFSG.LocalAnalysis.GLTheoremA.CatA.S172AExistBase
public import CFSG.LocalAnalysis.GLTheoremA.CatA.S172AExistRank
public import CFSG.LocalAnalysis.GLTheoremA.CatA.S172ALayerGL

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S172A

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4
open CFSG.LocalAnalysis.GLTheoremA.KD264Lie.X1LinCore.Transfer (VecAut projEquiv)

theorem centralizer_sup {G : Type*} [Group G] (H K : Subgroup G) :
    Subgroup.centralizer ((H ⊔ K : Subgroup G) : Set G) =
      Subgroup.centralizer (H : Set G) ⊓ Subgroup.centralizer (K : Set G) := by
  rw [Subgroup.sup_eq_closure, Subgroup.centralizer_closure]
  ext g
  simp only [Subgroup.mem_centralizer_iff, Subgroup.mem_inf, Set.forall_mem_union]

theorem exists_gen {Ω : Type} [Group Ω] [Finite Ω] {B D' : Subgroup Ω} {x : Ω} {m : ℕ}
    (φ : ↥B →* VecAut m) (hker : ∀ b : ↥B, φ b = 1 ↔ (b : Ω) ∈ Subgroup.zpowers x)
    (hBel : IsElemAbelian 3 B) (hxB : x ∈ B) (hx1 : x ≠ 1) (hDB : D' ≤ B) (hxD : x ∈ D')
    (hD9 : Nat.card D' = 3 ^ 2) :
    ∃ d ∈ φ.range, d ≠ 1 ∧ d ^ 3 = 1 ∧
      ∀ b : ↥B, (b : Ω) ∈ D' ↔ φ b ∈ Subgroup.zpowers d := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let D'' : Subgroup ↥B := D'.subgroupOf B
  have hD''card : Nat.card D'' = 9 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hDB).toEquiv, hD9]; norm_num
  let ψ : ↥D'' →* VecAut m := φ.comp D''.subtype
  have hkerle : φ.ker ≤ D'' := by
    intro b hb
    rw [Subgroup.mem_subgroupOf]
    have := (hker b).1 (MonoidHom.mem_ker.1 hb)
    exact (Subgroup.zpowers_le.2 hxD) this
  have hkerψ : Nat.card ψ.ker = 3 := by
    have h1 : ψ.ker = φ.ker.subgroupOf D'' := (MonoidHom.comap_ker φ D''.subtype).symm
    rw [h1, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hkerle).toEquiv,
      card_ker_eq_three φ hker hBel hxB hx1]
  have hrange3 : Nat.card ψ.range = 3 := by
    have := Subgroup.card_ker_mul_card_range ψ
    rw [hD''card, hkerψ] at this
    omega
  have hψrange : ψ.range = D''.map φ := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
  obtain ⟨d, hdψ, hd1⟩ : ∃ d ∈ ψ.range, d ≠ 1 := by
    by_contra hcon
    push Not at hcon
    have : Nat.card ψ.range ≤ 1 := by
      refine Finite.card_le_one_iff_subsingleton.2 ⟨fun a b => Subtype.ext ?_⟩
      rw [hcon a.1 a.2, hcon b.1 b.2]
    omega
  have hdφ : d ∈ φ.range := by
    obtain ⟨⟨b, hb⟩, rfl⟩ := hdψ
    exact ⟨b, rfl⟩
  have hd3 : d ^ 3 = 1 := by
    obtain ⟨b, rfl⟩ := hdφ
    rw [← map_pow]
    have : b ^ 3 = (1 : ↥B) := Subtype.ext (by simpa using hBel.2 b b.2)
    rw [this, map_one]
  have hord : orderOf d = 3 := orderOf_eq_prime hd3 hd1
  have hzp : Subgroup.zpowers d = ψ.range := by
    apply Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.2 hdψ)
    rw [Nat.card_zpowers, hord, hrange3]
  refine ⟨d, hdφ, hd1, hd3, fun b => ?_⟩
  rw [← hzp] at hψrange
  constructor
  · intro hb
    have hbD : b ∈ D'' := hb
    rw [hψrange]
    exact ⟨b, hbD, rfl⟩
  · intro hb
    rw [hψrange] at hb
    obtain ⟨δ, hδ, hδb⟩ := hb
    have : b * δ⁻¹ ∈ φ.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, ← hδb, mul_inv_cancel]
    have hbd : b * δ⁻¹ ∈ D'' := hkerle this
    have : b ∈ D'' := by
      have := D''.mul_mem hbd hδ
      simpa using this
    exact this


theorem inf_cs_eq_map {Ω : Type} [Group Ω] {S B D' : Subgroup Ω} {m : ℕ} (Θ : VecAut m →* Ω)
    (φ : ↥B →* VecAut m) (hDB : D' ≤ B) (hΘ : Function.Injective Θ) (hΘS : Θ.range = S)
    (hconj : ∀ (b : ↥B) (g : VecAut m), (b : Ω) * Θ g * (b : Ω)⁻¹ = Θ (φ b * g * (φ b)⁻¹))
    {d : VecAut m} (hd : d ∈ φ.range)
    (hD : ∀ b : ↥B, (b : Ω) ∈ D' ↔ φ b ∈ Subgroup.zpowers d) :
    S ⊓ Subgroup.centralizer (D' : Set Ω) =
      (Subgroup.centralizer ({d} : Set (VecAut m))).map Θ := by
  obtain ⟨b₀, hb₀⟩ := hd
  ext y
  constructor
  · rintro ⟨hyS, hyc⟩
    rw [← hΘS] at hyS
    obtain ⟨g, rfl⟩ := hyS
    refine ⟨g, ?_, rfl⟩
    rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff]
    have hb₀D : (b₀ : Ω) ∈ D' := (hD b₀).2 (by rw [hb₀]; exact Subgroup.mem_zpowers d)
    have h1 := (Subgroup.mem_centralizer_iff.1 hyc) _ hb₀D
    have h2 := hconj b₀ g
    rw [hb₀] at h2
    have h4 : (b₀ : Ω) * Θ g * (b₀ : Ω)⁻¹ = Θ g := by rw [h1, mul_inv_cancel_right]
    have h5 : g = d * g * d⁻¹ := hΘ (h4.symm.trans h2)
    rw [eq_mul_inv_iff_mul_eq] at h5
    exact h5
  · rintro ⟨g, hg, rfl⟩
    refine ⟨?_, ?_⟩
    · rw [← hΘS]; exact ⟨g, rfl⟩
    · refine Subgroup.mem_centralizer_iff.2 ?_
      intro y hy
      let c : ↥B := ⟨y, hDB hy⟩
      have hcZ : φ c ∈ Subgroup.zpowers d := (hD c).1 hy
      have hge : g * d = d * g := Subgroup.mem_centralizer_singleton_iff.1 hg
      obtain ⟨k, hk⟩ := hcZ
      have hcomm : φ c * g = g * φ c := by
        rw [← hk]
        exact ((Commute.zpow_left (show Commute d g from hge.symm) k).eq)
      have h2 := hconj c g
      have h4 : Θ (φ c * g * (φ c)⁻¹) = Θ g := by
        rw [hcomm, mul_inv_cancel_right]
      rw [h4, mul_inv_eq_iff_eq_mul] at h2
      exact h2


theorem normal_map_subgroupOf {G Ω : Type*} [Group G] [Group Ω] (Θ : G →* Ω) {N C : Subgroup G}
    (hNC : N ≤ C) (hn : (N.subgroupOf C).Normal) :
    ((N.map Θ).subgroupOf (C.map Θ)).Normal := by
  rw [Subgroup.normal_subgroupOf_iff (Subgroup.map_mono hNC)]
  rintro _ _ ⟨n', hn', rfl⟩ ⟨c, hc, rfl⟩
  have := (Subgroup.normal_subgroupOf_iff hNC).1 hn n' c hn' hc
  exact ⟨c * n' * c⁻¹, this, by simp [map_mul, map_inv]⟩

theorem isQuasisimple_map_inj {G Ω : Type*} [Group G] [Group Ω] (Θ : G →* Ω)
    (hΘ : Function.Injective Θ) {N : Subgroup G} (h : CFSG.Open.IsQuasisimple ↥N) :
    CFSG.Open.IsQuasisimple ↥(N.map Θ) :=
  CFSG.SignalizerFunctorTheorem.TransportA.isQuasisimple_of_mulEquiv
    (Subgroup.equivMapOfInjective N Θ hΘ) h

theorem eq_layer_of_normal_quasisimple {G : Type} [Group G] {H N K : Subgroup G} (hNH : N ≤ H)
    (hnorm : (N.subgroupOf H).Normal) (hq : CFSG.Open.IsQuasisimple ↥N)
    (hK : K = GLALayer H) (hKc : CFSG.Open.IsComponentOf K H) : N = K := by
  have hcomp : CFSG.Open.IsComponentOf N H :=
    ⟨hNH, CFSG.Open.IsSubnormal.step hNH hnorm (CFSG.Open.IsSubnormal.refl H), hq⟩
  have hNK : N ≤ K := by
    rw [hK]
    unfold GLALayer
    exact le_sSup hcomp
  have hnormK : (N.subgroupOf K).Normal := by
    rw [Subgroup.normal_subgroupOf_iff hNK]
    intro h g hh hg
    have := (Subgroup.normal_subgroupOf_iff hNH).1 hnorm h g hh (hKc.1 hg)
    exact this
  have hcompK : CFSG.Open.IsComponentOf N K :=
    ⟨hNK, CFSG.Open.IsSubnormal.step hNK hnormK (CFSG.Open.IsSubnormal.refl K), hq⟩
  exact CFSG.Fischer.Classification.Recognition.IsComponentOf.eq_of_isQuasisimple hcompK hKc.2.2


theorem catalogIs_isLnA_four_of_three_le {m : ℕ} (hm : 3 ≤ m) {X : Type} [Group X]
    (e : X ≃* Matrix.ProjectiveSpecialLinearGroup (Fin m) (GaloisField 2 2)) :
    catalogIs X (isLnA m 4) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨r, rfl⟩ : ∃ r, m = r + 1 := ⟨m - 1, by omega⟩
  let q : TauCeti.PrimePower := ⟨2, 2, Nat.prime_two, two_pos⟩
  have hadm : StatedLieAdmissible .PSL (r + 1) 2 2 := by
    refine ⟨Nat.prime_two, by norm_num, ?_, ?_, ?_⟩
    · omega
    · intro h'
      simp only [Prod.mk.injEq] at h'
      omega
    · intro h'
      simp only [Prod.mk.injEq] at h'
      omega
  have hdup : ¬ (TauCeti.LieTypeIndex.A r q).IsDuplicateRepresentative := by
    rw [TauCeti.LieTypeIndex.isDuplicateRepresentative_iff]
    rintro (⟨h1, -⟩ | ⟨-, h2⟩ | ⟨-, h2⟩)
    · omega
    · exact absurd h2 (by simp [q, TauCeti.PrimePower.card_def])
    · exact absurd h2 (by simp [q, TauCeti.PrimePower.card_def])
  have hv : (TauCeti.LieTypeIndex.A r q).Valid :=
    CFSG.ClassicalModels.linearCatalog_index_valid (r + 1) 2 2 hadm hdup
  refine ⟨.lie ⟨.A r q, hv⟩, Or.inl ⟨rfl, by simp [q, TauCeti.PrimePower.card_def]⟩, ?_⟩
  exact ⟨e.trans (CFSG.ClassicalModels.linearCatalogCandidateEquivPSL r q hv).symm⟩

theorem catalogIs_isLnA_four_two {X : Type} [Group X]
    (e : X ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField 2 2)) :
    catalogIs X (isLnA 2 4) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hK4 : Nat.card (GaloisField 2 2) = 4 := by
    rw [GaloisField.card _ _ (by norm_num)]; norm_num
  obtain ⟨e5⟩ := CFSG.ClassicalModels.nonempty_statedLinearModel_equiv_alternating_five
    (GaloisField 2 2) (Or.inl hK4)
  let eS := CFSG.Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj 2 (GaloisField 2 2)
  exact ⟨.alternating 5 le_rfl, Or.inr (Or.inl ⟨rfl, Or.inl rfl, rfl⟩),
    ⟨e.trans (eS.trans e5)⟩⟩

theorem pSimple_equiv_centerQuot {Ω : Type} [Group Ω] [Finite Ω] {K : Subgroup Ω}
    (hq : CFSG.Open.IsQuasisimple ↥K) (h3 : 3 ∣ Nat.card ↥K) :
    Nonempty (↥K ⧸ Subgroup.center ↥K ≃* PSimple 3 K) := by
  haveI : Group.IsPerfect ↥K := ⟨hq.1⟩
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hOne : GLAPPrimeCore 3 ↥K ≠ ⊤ := by
    intro htop
    have hc : Nat.Coprime 3 (Nat.card (GLAPPrimeCore 3 ↥K)) :=
      CFSG.pPrimeCore_coprime_card (p := 3) (G := ↥K)
    rw [htop, Subgroup.card_top] at hc
    exact (by norm_num : (3 : ℕ) ≠ 1) (Nat.Coprime.eq_one_of_dvd hc h3)
  have hOZ := CFSG.LocalAnalysis.GLTheoremA.le_center_of_normal_of_isQuasisimple hq inferInstance hOne
  exact ⟨pSimpleEquivCenterQuot 3 hOZ⟩


structure LSetup (n r : ℕ) (Ω : Type) [Group Ω] (S B : Subgroup Ω) (x : Ω) where
  hn : n = 2 * r + 1
  hr : 3 ≤ r
  Θ : VecAut n →* Ω
  φ : ↥B →* VecAut n
  hΘ : Function.Injective Θ
  hΘS : Θ.range = S
  hconj : ∀ (b : ↥B) (g : VecAut n), (b : Ω) * Θ g * (b : Ω)⁻¹ = Θ (φ b * g * (φ b)⁻¹)
  hker : ∀ b : ↥B, φ b = 1 ↔ (b : Ω) ∈ Subgroup.zpowers x
  hBel : IsElemAbelian 3 B
  hxB : x ∈ B
  hx1 : x ≠ 1
  hcard : 3 ^ r ≤ Nat.card φ.range

theorem classify_gen {n r : ℕ} {Ω : Type} [Group Ω] [Finite Ω] {S B : Subgroup Ω} {x : Ω}
    (L : LSetup n r Ω S B x) {D' K' : Subgroup Ω} (hstd : GLAStdSubPre 3 B x S D' K') :
    ∃ d : VecAut n, d ∈ L.φ.range ∧ d ≠ 1 ∧ d ^ 3 = 1 ∧
      (∀ b : ↥B, (b : Ω) ∈ D' ↔ L.φ b ∈ Subgroup.zpowers d) ∧
      ((Module.finrank (ZMod 2) (GL.comSp d) = 2 ∧ catalogIs (PSimple 3 K') (isLnA (n - 2) 2)) ∨
       (Module.finrank (ZMod 2) (GL.fixSp d) = 1 ∧ catalogIs (PSimple 3 K') (isLnA r 4))) := by
  classical
  obtain ⟨hDB, hDel, hD9, hxD, hKeq, hKc, hDeq⟩ := hstd
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨d, hdE, hd1, hd3, hD⟩ := exists_gen L.φ L.hker L.hBel L.hxB L.hx1 hDB hxD hD9
  refine ⟨d, hdE, hd1, hd3, hD, ?_⟩
  have hcent := inf_cs_eq_map L.Θ L.φ hDB L.hΘ L.hΘS L.hconj hdE hD
  have hV : Module.finrank (ZMod 2) (Fin n → ZMod 2) = 2 * r + 1 := by
    rw [Module.finrank_fin_fun, L.hn]
  have hsum := GL.finrank_fixSp hd3
  obtain ⟨m, hm⟩ := GL.even_finrank_comSp hd3
  have hEel := isElemAbelian_range L.φ L.hBel
  have hr3 := L.hr
  have hsum' : Module.finrank (ZMod 2) (GL.fixSp d) + Module.finrank (ZMod 2) (GL.comSp d) =
      2 * r + 1 := by rw [hsum, hV]
  have hcodd : Module.finrank (ZMod 2) (GL.fixSp d) = 1 ∨
      3 ≤ Module.finrank (ZMod 2) (GL.fixSp d) := by omega
  rcases hcodd with hc1 | hc3
  ·
    right
    refine ⟨hc1, ?_⟩
    have ha : Module.finrank (ZMod 2) (GL.comSp d) = 2 * r := by omega
    obtain ⟨F, hFC, hFn, hFc, hFq, hF3, ⟨eQ⟩⟩ := GL.fullLayer hd3 hc1 ha (by omega : 2 ≤ r)
    have hKF : F.map L.Θ = K' := by
      refine eq_layer_of_normal_quasisimple (H := S ⊓ Subgroup.centralizer (D' : Set Ω)) ?_ ?_ ?_
        hKeq hKc
      · rw [hcent]; exact Subgroup.map_mono hFC
      · rw [hcent]; exact normal_map_subgroupOf L.Θ hFC hFn
      · exact isQuasisimple_map_inj L.Θ L.hΘ hFq
    rw [← hKF]
    have hq' := isQuasisimple_map_inj L.Θ L.hΘ hFq
    have h3' : 3 ∣ Nat.card ↥(F.map L.Θ) := by
      rw [← Nat.card_congr (Subgroup.equivMapOfInjective F L.Θ L.hΘ).toEquiv]
      exact hF3
    obtain ⟨eP⟩ := pSimple_equiv_centerQuot hq' h3'
    let eM : ↥(F.map L.Θ) ⧸ Subgroup.center ↥(F.map L.Θ) ≃* ↥F ⧸ Subgroup.center ↥F :=
      QuotientGroup.congr _ _ (Subgroup.equivMapOfInjective F L.Θ L.hΘ).symm
        (Subgroup.map_center_eq (Subgroup.equivMapOfInjective F L.Θ L.hΘ).symm)
    exact catalogIs_isLnA_four_of_three_le hr3 (eP.symm.trans (eM.trans eQ))
  ·
    left
    have hNq : CFSG.Open.IsQuasisimple ↥(GL.Nsub hd3) :=
      GL.Nsub_isQuasisimple_c hc3 hd3 rfl
    have hNle := GL.Nsub_le_cent hd3
    have hNnorm := GL.Nsub_normal hd3
    have hKN : (GL.Nsub hd3).map L.Θ = K' := by
      refine eq_layer_of_normal_quasisimple (H := S ⊓ Subgroup.centralizer (D' : Set Ω)) ?_ ?_ ?_
        hKeq hKc
      · rw [hcent]; exact Subgroup.map_mono hNle
      · rw [hcent]; exact normal_map_subgroupOf L.Θ hNle hNnorm
      · exact isQuasisimple_map_inj L.Θ L.hΘ hNq
    have hsmall : ∀ K0 : Subgroup (VecAut n), K0 ≤ L.φ.range →
        (∀ g ∈ K0, ∀ h ∈ GL.Nsub hd3, g * h = h * g) → Nat.card K0 ≤ 3 := by
      intro K0 hK0 hcomm
      have hle : K0 ≤ Subgroup.zpowers d := by
        intro k hk
        obtain ⟨b, hb⟩ := hK0 hk
        have hbD : (b : Ω) ∈ D' := by
          rw [hDeq]
          refine ⟨b.2, ?_⟩
          refine Subgroup.mem_centralizer_iff.2 ?_
          intro y hy
          rw [← hKN] at hy
          obtain ⟨n', hn', rfl⟩ := hy
          have h2 := L.hconj b n'
          rw [hb] at h2
          have hk' := hcomm k hk n' hn'
          have h4 : L.Θ (k * n' * k⁻¹) = L.Θ n' := by rw [hk', mul_inv_cancel_right]
          rw [h4, mul_inv_eq_iff_eq_mul] at h2
          exact h2.symm
        have := (hD b).1 hbD
        rwa [hb] at this
      calc Nat.card K0 ≤ Nat.card (Subgroup.zpowers d) := Subgroup.card_le_of_le hle
        _ = 3 := by rw [Nat.card_zpowers, orderOf_eq_prime hd3 hd1]
    have ha2 : Module.finrank (ZMod 2) (GL.comSp d) = 2 :=
      GL.finrank_comSp_eq_two hV hEel L.hcard hdE hd3 hd1 hsmall
    refine ⟨ha2, ?_⟩
    have hc' : Module.finrank (ZMod 2) (GL.fixSp d) = 2 * r - 1 := by omega
    rw [← hKN]
    let eN := GL.NsubEquivC hd3 hc'
    let eK : ↥((GL.Nsub hd3).map L.Θ) ≃* ↥(GL.Nsub hd3) :=
      (Subgroup.equivMapOfInjective (GL.Nsub hd3) L.Θ L.hΘ).symm
    obtain ⟨hs, hnab⟩ := GL.Nsub_simple_nonab_c (by omega : 3 ≤ 2 * r - 1) hd3 hc'
    have hKsn := GL.simple_nonab_of_equiv eK ⟨hs, hnab⟩
    haveI := hKsn.1
    have hKZ : Subgroup.center ↥((GL.Nsub hd3).map L.Θ) = ⊥ :=
      GL.center_eq_bot_of_simple_nonab hKsn.2
    have hK3 : 3 ∣ Nat.card ↥((GL.Nsub hd3).map L.Θ) := by
      rw [Nat.card_congr eK.toEquiv]
      exact GL.three_dvd_card_Nsub_c (k := r - 1) (by omega) hd3 (by omega)
    have hKq := isQuasisimple_map_inj L.Θ L.hΘ hNq
    obtain ⟨eP⟩ := pSimple_equiv hKq hKZ hK3
    have hn2 : n - 2 = 2 * r - 1 := by have := L.hn; omega
    rw [hn2]
    exact catalogIs_isLnA_of_vecAut (by omega) (eP.trans (eK.trans eN))


theorem not_both_types (hb : CFSG.LocalAnalysis.GLTheoremA.CatDistinct.OrderBridge) {r : ℕ}
    (hr : 3 ≤ r) {X : Type} [Group X] [Finite X] (h1 : catalogIs X (isLnA r 4))
    (h2 : catalogIs X (isLnA (2 * r - 1) 2)) : False := by
  have h1' : catalogIs X (isLnA r (2 ^ 2)) := by norm_num; exact h1
  have h2' : catalogIs X (isLnA (2 * r - 1) (2 ^ 1)) := by norm_num; exact h2
  obtain ⟨-, -, e1⟩ := CFSG.LocalAnalysis.GLTheoremA.S172.v2_isLnA hb (by norm_num) h1'
  obtain ⟨-, -, e2⟩ := CFSG.LocalAnalysis.GLTheoremA.S172.v2_isLnA hb (by norm_num) h2'
  obtain ⟨s, rfl⟩ : ∃ s, r = s + 1 := ⟨r - 1, by omega⟩
  have hs : 2 ≤ s := by omega
  have e3 : 2 * (s + 1) - 1 = 2 * s + 1 := by omega
  rw [e3] at e2
  have e4 : 2 * s + 1 - 1 = 2 * s := by omega
  simp only [e4, Nat.add_sub_cancel] at e1 e2
  nlinarith


theorem catalogIs_isLnA_four_of_two_le {m : ℕ} (hm : 2 ≤ m) {X : Type}
    [Group X] (e : X ≃* Matrix.ProjectiveSpecialLinearGroup (Fin m) (GaloisField 2 2)) :
    catalogIs X (isLnA m 4) := by
  rcases Nat.eq_or_lt_of_le hm with rfl | h
  · exact catalogIs_isLnA_four_two e
  · exact catalogIs_isLnA_four_of_three_le (by omega) e

theorem catalogIs_pSimple_map {Ω Γ : Type} [Group Ω] [Finite Ω]
    [Group Γ] (Ξ : Γ →* Ω) (hΞ : Function.Injective Ξ) {F : Subgroup Γ}
    (hFq : CFSG.Open.IsQuasisimple ↥F) (hF3 : 3 ∣ Nat.card ↥F) {m : ℕ} (hm : 2 ≤ m)
    (eQ : ↥F ⧸ Subgroup.center ↥F ≃* Matrix.ProjectiveSpecialLinearGroup (Fin m) (GaloisField 2 2)) :
    catalogIs (PSimple 3 (F.map Ξ)) (isLnA m 4) := by
  have hq' := isQuasisimple_map_inj Ξ hΞ hFq
  have h3' : 3 ∣ Nat.card ↥(F.map Ξ) := by
    rw [← Nat.card_congr (Subgroup.equivMapOfInjective F Ξ hΞ).toEquiv]
    exact hF3
  obtain ⟨eP⟩ := pSimple_equiv_centerQuot hq' h3'
  let eM : ↥(F.map Ξ) ⧸ Subgroup.center ↥(F.map Ξ) ≃* ↥F ⧸ Subgroup.center ↥F :=
    QuotientGroup.congr _ _ (Subgroup.equivMapOfInjective F Ξ hΞ).symm
      (Subgroup.map_center_eq (Subgroup.equivMapOfInjective F Ξ hΞ).symm)
  exact catalogIs_isLnA_four_of_two_le hm (eP.symm.trans (eM.trans eQ))

theorem catalogIs_pSimple_congr {Ω : Type} [Group Ω] {K K' : Subgroup Ω} (h : K = K')
    {P : TauCeti.CFSGIndex → Prop} (hK : catalogIs (PSimple 3 K) P) :
    catalogIs (PSimple 3 K') P := by
  subst h
  exact hK

open CFSG.LocalAnalysis.GLTheoremA.S172 (Cfg172) in
open CFSG.LocalAnalysis.GLTheoremA.S10 (cs) in
theorem exists_lsetup
    {n r : ℕ} (hn : n = 2 * r + 1) (hr3 : 3 ≤ r) {Ω : Type} [Group Ω] [Finite Ω]
    {S B D K : Subgroup Ω} {x : Ω} (hcfg : Cfg172 3 S B D K x)
    (hS : catalogIs (PSimple 3 S) (isLnA n 2)) : Nonempty (LSetup n r Ω S B x) := by
  classical
  haveI : S.Normal := hcfg.normal
  obtain ⟨hZ, ⟨θ⟩, hin⟩ := exists_theta (n := n) (by omega) hcfg.qs hS
  obtain ⟨Θ, φ, hΘ, hΘS, hconj, hker'⟩ :=
    exists_action (B := B) (fun b hb => hcfg.elem.2 b hb) hZ θ hin
  have hker : ∀ b : ↥B, φ b = 1 ↔ (b : Ω) ∈ Subgroup.zpowers x := by
    intro b
    rw [hker', ← hcfg.cent b b.2, Subgroup.mem_centralizer_iff]
    constructor
    · intro h s hs
      exact (h s hs).symm
    · intro h s hs
      exact (h s hs).symm
  have hxS : ∀ g : VecAut n, x * Θ g = Θ g * x := by
    intro g
    have hxc : x ∈ Subgroup.centralizer (S : Set Ω) :=
      (hcfg.cent x hcfg.mem).2 (Subgroup.mem_zpowers x)
    have hg : Θ g ∈ S := by rw [← hΘS]; exact ⟨g, rfl⟩
    exact ((Subgroup.mem_centralizer_iff.1 hxc) _ hg).symm
  have hZ' : Subgroup.center (VecAut n) = ⊥ := by
    rw [← Subgroup.map_center_eq θ, hZ, Subgroup.map_bot]
  have hcard := card_range_ge (n := n) (r := r) hn hr3 Θ φ hΘ hker hcfg.elem hcfg.mem
    hcfg.ne_one hxS hZ' hcfg.rank
  exact ⟨⟨hn, hr3, Θ, φ, hΘ, hΘS, hconj, hker, hcfg.elem, hcfg.mem, hcfg.ne_one, hcard⟩⟩

end CFSG.LocalAnalysis.GLTheoremA.S172A

end
