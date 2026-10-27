module

public import CFSG.LocalAnalysis.GLTheoremB.Prop95I1920Thompson
public import CFSG.LocalAnalysis.GLTheoremB.Prop95I1920Three
public import CFSG.LocalAnalysis.GLTheoremB.Prop95I1920Strong

public section

namespace CFSG.LocalAnalysis.GLTheoremB.Prop95I1920

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.LocalAnalysis.GLTheoremB.Prop95Iv
open CFSG.LocalAnalysis.GLTheoremB.Prop95Parts.Input18 (le_pCoreOf_of_normal)
open CFSG.LocalAnalysis.GLTheoremB.Prop95I1921
open CFSG.LieType.ChevTwo (Chev2CoreCent Chev2KDOut autCentralizer)
open CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData (IsChevTwo)
open scoped commutatorElement

section YGeneral

variable {X : Type} [Group X] [Finite X] {K : Subgroup X}

noncomputable abbrev KhY (K : Subgroup X) (Y : Subgroup (MulAut (Kbar K))) : Subgroup ↥Y :=
  (Kinn K).subgroupOf Y

@[expose] noncomputable def thetaY (hK : IsComponentOf K ⊤) {Y : Subgroup (MulAut (Kbar K))}
    (hY : Kinn K ≤ Y) : Kbar K ≃* ↥(KhY K Y) :=
  (MonoidHom.ofInjective (f := (MulAut.conj : Kbar K →* MulAut (Kbar K)))
      (conj_injective_of_center_bot (center_Kbar hK))).trans
    (Subgroup.subgroupOfEquivOfLe hY).symm

theorem thetaY_coe (hK : IsComponentOf K ⊤) {Y : Subgroup (MulAut (Kbar K))} (hY : Kinn K ≤ Y)
    (a : Kbar K) : (((thetaY hK hY a : ↥(KhY K Y)) : ↥Y) : MulAut (Kbar K)) = MulAut.conj a := rfl

theorem isSimpleGroup_KhY (hK : IsComponentOf K ⊤) {Y : Subgroup (MulAut (Kbar K))}
    (hY : Kinn K ≤ Y) : IsSimpleGroup ↥(KhY K Y) := by
  haveI : IsSimpleGroup (Kbar K) := hK.2.2.2
  exact (thetaY hK hY).symm.isSimpleGroup

theorem centralizer_KhY (hK : IsComponentOf K ⊤) {Y : Subgroup (MulAut (Kbar K))}
    (hY : Kinn K ≤ Y) :
    Subgroup.centralizer ((KhY K Y : Subgroup ↥Y) : Set ↥Y) = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  rw [Subgroup.mem_bot]
  have hZ := center_Kbar hK
  obtain ⟨φ, hφ⟩ : ∃ φ : MulAut (Kbar K), φ = (x : MulAut (Kbar K)) := ⟨_, rfl⟩
  have hcomm : ∀ c : Kbar K, MulAut.conj c * φ = φ * MulAut.conj c := fun c => by
    have h0 := Subgroup.mem_centralizer_iff.1 hx (thetaY hK hY c) (SetLike.coe_mem (thetaY hK hY c))
    have h2 := congrArg (fun y : ↥Y => (y : MulAut (Kbar K))) h0
    simpa [thetaY_coe, hφ] using h2
  have hfix : ∀ b : Kbar K, φ b = b := by
    intro b
    have hcent : (φ b)⁻¹ * b ∈ Subgroup.center (Kbar K) := by
      rw [Subgroup.mem_center_iff]
      intro g
      obtain ⟨z, hz⟩ := φ.surjective g
      have h1 := congrArg (fun ψ : MulAut (Kbar K) => ψ z) (hcomm b)
      simp only [MulAut.mul_apply, MulAut.conj_apply] at h1
      rw [map_mul, map_mul, map_inv] at h1
      rw [← hz]
      calc φ z * ((φ b)⁻¹ * b) = (φ b)⁻¹ * (φ b * φ z * (φ b)⁻¹) * b := by group
        _ = (φ b)⁻¹ * (b * φ z * b⁻¹) * b := by rw [← h1]
        _ = (φ b)⁻¹ * b * φ z := by group
    rw [hZ, Subgroup.mem_bot] at hcent
    exact inv_mul_eq_one.1 hcent
  apply Subtype.ext
  rw [← hφ]
  exact MulEquiv.ext hfix

@[expose] noncomputable def iotaY (hK : IsComponentOf K ⊤) (hZ : Subgroup.center ↥K = ⊥)
    {Y : Subgroup (MulAut (Kbar K))} (hY : Kinn K ≤ Y) : ↥K ≃* ↥(KhY K Y) :=
  (QuotientGroup.quotientBot.symm.trans (QuotientGroup.quotientMulEquivOfEq hZ.symm)).trans
    (thetaY hK hY)

theorem iotaY_coe (hK : IsComponentOf K ⊤) (hZ : Subgroup.center ↥K = ⊥)
    {Y : Subgroup (MulAut (Kbar K))} (hY : Kinn K ≤ Y) (a : ↥K) :
    (((iotaY hK hZ hY a : ↥(KhY K Y)) : ↥Y) : MulAut (Kbar K)) =
      MulAut.conj (QuotientGroup.mk a : Kbar K) := by
  show (((thetaY hK hY (QuotientGroup.mk a) : ↥(KhY K Y)) : ↥Y) : MulAut (Kbar K)) = _
  exact thetaY_coe hK hY _

theorem congr_iotaY_normalizerMonoidHom (hK : IsComponentOf K ⊤) (hZ : Subgroup.center ↥K = ⊥)
    {Y : Subgroup (MulAut (Kbar K))} (hY : Kinn K ≤ Y)
    (n : ↥(Subgroup.normalizer (K : Set X))) (hn : rhoK K n ∈ Y) :
    MulAut.congr (iotaY hK hZ hY) (K.normalizerMonoidHom n) =
      (KhY K Y).normalizerMonoidHom
        ⟨⟨rhoK K n, hn⟩, Subgroup.le_normalizer_of_normal (Subgroup.mem_top _)⟩ := by
  apply MulEquiv.ext
  intro a
  obtain ⟨b, rfl⟩ := (iotaY hK hZ hY).surjective a
  show (iotaY hK hZ hY) (K.normalizerMonoidHom n ((iotaY hK hZ hY).symm ((iotaY hK hZ hY) b))) = _
  rw [MulEquiv.symm_apply_apply]
  apply Subtype.ext
  rw [Subgroup.normalizerMonoidHom_apply_apply_coe]
  apply Subtype.ext
  show ((((iotaY hK hZ hY) (K.normalizerMonoidHom n b) : ↥(KhY K Y)) : ↥Y) : MulAut (Kbar K)) = _
  rw [iotaY_coe]
  simp only [Subgroup.coe_mul, Subgroup.coe_inv, iotaY_coe]
  rw [mulAut_mul_conj_mul_inv, rhoK_mk]

theorem KhY_nonabelian (hK : IsComponentOf K ⊤) {Y : Subgroup (MulAut (Kbar K))}
    (hY : Kinn K ≤ Y) : ∃ a b : ↥(KhY K Y), a * b ≠ b * a := by
  obtain ⟨a, b, hab⟩ := (isQuasisimple_of_comp hK).2.2
  refine ⟨thetaY hK hY a, thetaY hK hY b, fun h => hab ?_⟩
  rw [← map_mul, ← map_mul] at h
  exact (thetaY hK hY).injective h

theorem isChevTwo_KhY (hK : IsComponentOf K ⊤) {Y : Subgroup (MulAut (Kbar K))}
    (hY : Kinn K ≤ Y) (hCh : IsChevTwo (Kbar K)) : IsChevTwo ↥(KhY K Y) :=
  CFSG.HardMathSupport.Meierfrankenfeld.AGL81.FF531.isChevTwo_of_mulEquiv (thetaY hK hY) hCh

end YGeneral

section Construction

variable {X : Type} [Group X] [Finite X] {K : Subgroup X}

theorem exists_mem_centralizer_of_commute (hK : IsComponentOf K ⊤) (hZ : Subgroup.center ↥K = ⊥)
    {dN : ↥(Subgroup.normalizer (K : Set X))} {Γ : Subgroup ↥(Subgroup.normalizer (K : Set X))}
    (hΓ : Γ ≤ Subgroup.centralizer ({dN} : Set ↥(Subgroup.normalizer (K : Set X))))
    {c : MulAut (Kbar K)}
    (hc : c ∈ (K.subgroupOf (Subgroup.normalizer (K : Set X)) ⊔ Γ).map (rhoK K))
    (hca : c * rhoK K dN = rhoK K dN * c) :
    ∃ m ∈ Subgroup.centralizer ({dN} : Set ↥(Subgroup.normalizer (K : Set X))),
      c = rhoK K m := by
  obtain ⟨m, hm, rfl⟩ := Subgroup.mem_map.1 hc
  obtain ⟨κ, hκ, γ, hγ, rfl⟩ := Subgroup.mem_sup_of_normal_left.1 hm
  have hγC : γ ∈ Subgroup.centralizer ({dN} : Set ↥(Subgroup.normalizer (K : Set X))) := hΓ hγ
  have hργ : rhoK K γ * rhoK K dN = rhoK K dN * rhoK K γ := by
    rw [← map_mul, ← map_mul, Subgroup.mem_centralizer_singleton_iff.1 hγC]
  have hκa : rhoK K κ * rhoK K dN = rhoK K dN * rhoK K κ := by
    have h1 : rhoK K κ * rhoK K γ * rhoK K dN = rhoK K dN * (rhoK K κ * rhoK K γ) := by
      rw [← map_mul, ← map_mul, ← map_mul]
      have := hca
      rwa [← map_mul, ← map_mul] at this
    have h2 : rhoK K κ * rhoK K dN * rhoK K γ = rhoK K dN * rhoK K κ * rhoK K γ := by
      calc rhoK K κ * rhoK K dN * rhoK K γ
          = rhoK K κ * (rhoK K γ * rhoK K dN) := by rw [mul_assoc, ← hργ]
        _ = rhoK K κ * rhoK K γ * rhoK K dN := by rw [mul_assoc]
        _ = rhoK K dN * (rhoK K κ * rhoK K γ) := h1
        _ = rhoK K dN * rhoK K κ * rhoK K γ := by rw [mul_assoc]
    exact mul_right_cancel h2
  have hκC : κ ∈ Subgroup.centralizer ({dN} : Set ↥(Subgroup.normalizer (K : Set X))) := by
    set k : ↥K := ⟨(κ : X), Subgroup.mem_subgroupOf.1 hκ⟩ with hk
    have hκk : κ = ⟨(k : X), Subgroup.le_normalizer k.2⟩ := Subtype.ext rfl
    have hρκ : rhoK K κ = MulAut.conj (QuotientGroup.mk k : Kbar K) := by
      rw [hκk]
      exact rhoK_conj k
    have h1 : rhoK K dN (QuotientGroup.mk k : Kbar K) = QuotientGroup.mk k := by
      apply conj_injective_of_center_bot (center_Kbar hK)
      rw [← mulAut_mul_conj_mul_inv, ← hρκ]
      have := hκa
      calc rhoK K dN * rhoK K κ * (rhoK K dN)⁻¹ = rhoK K κ * rhoK K dN * (rhoK K dN)⁻¹ := by
            rw [← this]
        _ = rhoK K κ := by group
    rw [rhoK_mk] at h1
    have h2 : K.normalizerMonoidHom dN k = k := by
      have h3 := QuotientGroup.eq.1 h1.symm
      rw [hZ, Subgroup.mem_bot] at h3
      exact (inv_mul_eq_one.1 h3).symm
    have h4 := congrArg (fun z : ↥K => (z : X)) h2
    have h5 : (dN : X) * (κ : X) * (dN : X)⁻¹ = (κ : X) := by
      simpa [Subgroup.normalizerMonoidHom_apply_apply_coe, hk] using h4
    rw [Subgroup.mem_centralizer_singleton_iff]
    apply Subtype.ext
    show (κ : X) * (dN : X) = (dN : X) * (κ : X)
    calc (κ : X) * (dN : X) = ((dN : X) * (κ : X) * (dN : X)⁻¹) * (dN : X) := by rw [h5]
      _ = (dN : X) * (κ : X) := by group
  exact ⟨κ * γ, Subgroup.mul_mem _ hκC hγC, rfl⟩

variable (K)

noncomputable abbrev Gam1 (D1 : Subgroup ↥(Subgroup.normalizer (K : Set X))) :
    Subgroup ↥(Subgroup.normalizer (K : Set X)) :=
  Subgroup.centralizer (D1 : Set ↥(Subgroup.normalizer (K : Set X))) ⊔ D1

noncomputable abbrev Yg (D1 : Subgroup ↥(Subgroup.normalizer (K : Set X))) :
    Subgroup (MulAut (Kbar K)) :=
  (K.subgroupOf (Subgroup.normalizer (K : Set X)) ⊔ Gam1 K D1).map (rhoK K)

variable {K} {D1 : Subgroup ↥(Subgroup.normalizer (K : Set X))}

theorem Gam1_le_centralizer (hab : ∀ a ∈ D1, ∀ b ∈ D1, a * b = b * a)
    {d : ↥(Subgroup.normalizer (K : Set X))} (hd : d ∈ D1) :
    Gam1 K D1 ≤ Subgroup.centralizer ({d} : Set ↥(Subgroup.normalizer (K : Set X))) :=
  sup_le (Subgroup.centralizer_le (Set.singleton_subset_iff.2 hd))
    (fun e he => Subgroup.mem_centralizer_singleton_iff.2 (hab e he d hd))

theorem Kinn_le_Yg (K : Subgroup X) (D1 : Subgroup ↥(Subgroup.normalizer (K : Set X))) :
    Kinn K ≤ Yg K D1 := by
  rintro _ ⟨a, rfl⟩
  obtain ⟨k, rfl⟩ := QuotientGroup.mk_surjective a
  exact ⟨⟨(k : X), Subgroup.le_normalizer k.2⟩,
    Subgroup.mem_sup_left (Subgroup.mem_subgroupOf.2 k.2), rhoK_conj k⟩

theorem rho_mem_Yg_of_mem_Gam1 {m : ↥(Subgroup.normalizer (K : Set X))} (hm : m ∈ Gam1 K D1) :
    rhoK K m ∈ Yg K D1 :=
  Subgroup.mem_map_of_mem _ (Subgroup.mem_sup_right hm)

theorem rho_mem_Yg_of_mem {d : ↥(Subgroup.normalizer (K : Set X))} (hd : d ∈ D1) :
    rhoK K d ∈ Yg K D1 :=
  rho_mem_Yg_of_mem_Gam1 (Subgroup.mem_sup_right hd)

theorem rho_mem_Yg_of_centralizer {q : ↥(Subgroup.normalizer (K : Set X))}
    (hq : q ∈ Subgroup.centralizer (D1 : Set ↥(Subgroup.normalizer (K : Set X)))) :
    rhoK K q ∈ Yg K D1 :=
  rho_mem_Yg_of_mem_Gam1 (Subgroup.mem_sup_left hq)

theorem rho_pCore_mem_Yg (hKD : Chev2KDOut) (hCore : Chev2CoreCent) (hK : IsComponentOf K ⊤)
    (hCh : IsChevTwo (Kbar K)) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hD1 : IsPGroup p D1)
    (hab : ∀ a ∈ D1, ∀ b ∈ D1, a * b = b * a) {d : ↥(Subgroup.normalizer (K : Set X))}
    (hd : d ∈ D1) (hdp : d ^ p = 1) {s : ↥(Subgroup.normalizer (K : Set X))}
    (hs : s ∈ pCoreOf 2 (Subgroup.centralizer ({d} : Set ↥(Subgroup.normalizer (K : Set X))))) :
    rhoK K s ∈ Yg K D1 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hSD : D1 ≤ Subgroup.normalizer
      ((pCoreOf 2 (Subgroup.centralizer ({d} : Set ↥(Subgroup.normalizer (K : Set X))))
        : Subgroup _) : Set ↥(Subgroup.normalizer (K : Set X))) := fun e he =>
    CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 _
      (Subgroup.mem_centralizer_singleton_iff.2 (hab e he d hd))
  obtain ⟨q, -, hqC, hρ⟩ := exists_centralizing_rho_eq hKD hCore hK hCh hp hp2 D1 hD1 _
    (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _) hSD d hdp le_rfl s hs
  rw [hρ]
  exact rho_mem_Yg_of_centralizer hqC

theorem rho_pCore_subgroupOf_le (hK : IsComponentOf K ⊤) (hZ : Subgroup.center ↥K = ⊥)
    (hab : ∀ a ∈ D1, ∀ b ∈ D1, a * b = b * a) {d : ↥(Subgroup.normalizer (K : Set X))}
    (hd : d ∈ D1) :
    ((pCoreOf 2 (Subgroup.centralizer ({d} : Set ↥(Subgroup.normalizer (K : Set X))))).map
        (rhoK K)).subgroupOf (Yg K D1) ≤
      pCoreOf 2 (Subgroup.centralizer
        ({(⟨rhoK K d, rho_mem_Yg_of_mem hd⟩ : ↥(Yg K D1))} : Set ↥(Yg K D1))) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine le_pCoreOf_of_normal ?_ ?_ ?_
  · intro x hx
    obtain ⟨q, hq, hqx⟩ := Subgroup.mem_map.1 (Subgroup.mem_subgroupOf.1 hx)
    rw [Subgroup.mem_centralizer_singleton_iff]
    apply Subtype.ext
    show (x : MulAut (Kbar K)) * rhoK K d = rhoK K d * (x : MulAut (Kbar K))
    rw [← hqx, ← map_mul, ← map_mul,
      Subgroup.mem_centralizer_singleton_iff.1 (CFSG.LieType.BorelTits.pCoreOf_le 2 _ hq)]
  · intro c hc x hx
    have hca : (c : MulAut (Kbar K)) * rhoK K d = rhoK K d * (c : MulAut (Kbar K)) :=
      congrArg Subtype.val (Subgroup.mem_centralizer_singleton_iff.1 hc)
    obtain ⟨m, hmC, hcm⟩ := exists_mem_centralizer_of_commute hK hZ (Gam1_le_centralizer hab hd)
      c.2 hca
    have hmN := Subgroup.le_normalizer_map (rhoK K)
      (Subgroup.mem_map_of_mem (rhoK K) (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 _ hmC))
    rw [← hcm] at hmN
    have h1 := (Subgroup.mem_normalizer_iff.1 hmN (x : MulAut (Kbar K))).1 (Subgroup.mem_subgroupOf.1 hx)
    exact Subgroup.mem_subgroupOf.2 h1
  · exact ((CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _).map (rhoK K)).comap_of_injective
      (Yg K D1).subtype (Yg K D1).subtype_injective

end Construction

section Family

variable {X : Type} [Group X] [Finite X] {K : Subgroup X}
  {D1 : Subgroup ↥(Subgroup.normalizer (K : Set X))}

variable (K D1) in
noncomputable abbrev DYg : Subgroup ↥(Yg K D1) := (D1.map (rhoK K)).subgroupOf (Yg K D1)

variable (K D1) in
noncomputable abbrev SYg : ↥(Yg K D1) → Subgroup ↥(Yg K D1) := fun y =>
  pCoreOf 2 (Subgroup.centralizer ({y} : Set ↥(Yg K D1)))

theorem signalizerFamilyYg {p : ℕ} (hab : ∀ a ∈ D1, ∀ b ∈ D1, a * b = b * a)
    (hDp : ∀ e ∈ D1, e ^ p = 1) : SignalizerFamily p (DYg K D1) (SYg K D1) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hcomm : ∀ a ∈ DYg K D1, ∀ b ∈ DYg K D1, a * b = b * a := by
    intro a ha b hb
    obtain ⟨a', ha', ha'x⟩ := Subgroup.mem_map.1 (Subgroup.mem_subgroupOf.1 ha)
    obtain ⟨b', hb', hb'x⟩ := Subgroup.mem_map.1 (Subgroup.mem_subgroupOf.1 hb)
    apply Subtype.ext
    show (a : MulAut (Kbar K)) * b = b * a
    rw [← ha'x, ← hb'x, ← map_mul, ← map_mul, hab a' ha' b' hb']
  refine ⟨⟨isMulCommutative_iff.2 fun a b => Subtype.ext (hcomm a a.2 b b.2), fun x hx => ?_⟩,
    fun x _ _ => le_rfl, fun x hx _ e he => ?_⟩
  · obtain ⟨x', hx', hx'x⟩ := Subgroup.mem_map.1 (Subgroup.mem_subgroupOf.1 hx)
    apply Subtype.ext
    show (x : MulAut (Kbar K)) ^ p = 1
    rw [← hx'x, ← map_pow, hDp x' hx', map_one]
  · apply CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact hcomm e he x hx

end Family

theorem input19_20_3_of_kdout_corecent (hKD : Chev2KDOut) (hCore : Chev2CoreCent)
    (hS3 : Input19_20_3Core) (hZ1 : OmegaFourComponentCentre) : Input19_20_3 := by
  intro X _ _ p hp hp2 K hK hCh D Sd hfam n ε hn hΩ hnc
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hDp : ∀ x ∈ D, x ^ p = 1 := hfam.elemAbelian.2
  have hZK : Subgroup.center ↥K = ⊥ := center_eq_bot_of_omega hZ1 hK hn ε hΩ
  have hB1 : ∀ d ∈ D, d ≠ 1 →
      pCoreOf 2 (Subgroup.centralizer ({d} : Set X)) ≤ Subgroup.normalizer (K : Set X) :=
    fun d hd _ => pCoreOf_le_normalizer_of_chev hCore hp hp2 hK hCh (hDp d hd)
  haveI : IsSimpleGroup (Kbar K) := hK.2.2.2
  set D1 : Subgroup ↥(Subgroup.normalizer (K : Set X)) :=
    D.subgroupOf (Subgroup.normalizer (K : Set X)) with hD1def
  have hD1p : IsPGroup p D1 := isPGroup_subgroupOf_of_exponent hDp
  have hab : ∀ a ∈ D1, ∀ b ∈ D1, a * b = b * a := by
    intro a ha b hb
    have := isMulCommutative_iff.1 hfam.elemAbelian.1 ⟨(a : X), Subgroup.mem_subgroupOf.1 ha⟩
      ⟨(b : X), Subgroup.mem_subgroupOf.1 hb⟩
    have h : (a : X) * (b : X) = (b : X) * (a : X) := congrArg Subtype.val this
    exact Subtype.ext h
  have hD1exp : ∀ e ∈ D1, e ^ p = 1 := fun e he =>
    Subtype.ext (by simpa using hDp (e : X) (Subgroup.mem_subgroupOf.1 he))
  have hKY : Kinn K ≤ Yg K D1 := Kinn_le_Yg K D1
  have hfamY := signalizerFamilyYg (K := K) (D1 := D1) hab hD1exp
  haveI : (KhY K (Yg K D1)).Normal := inferInstance
  have hint := (input19_20_2CoreStrong_of hKD hCore) ↥(Yg K D1) (KhY K (Yg K D1))
    (isSimpleGroup_KhY hK hKY) (KhY_nonabelian hK hKY) (isChevTwo_KhY hK hKY hCh)
    (centralizer_KhY hK hKY) p hp hp2 (DYg K D1) (SYg K D1) hfamY
  set σ := sigmaFam (DYg K D1) (SYg K D1) with hσdef
  have htriv : ∀ (s : X) (hsN : s ∈ Subgroup.normalizer (K : Set X)),
      s ∈ Subgroup.centralizer (K : Set X) →
        rhoK K ⟨s, hsN⟩ ∈ σ.map (Yg K D1).subtype := by
    intro s hsN hsC
    have h1 : rhoK K ⟨s, hsN⟩ = 1 := (rhoK_eq_one_iff hK hsN).2 hsC
    rw [h1]
    exact (σ.map (Yg K D1).subtype).one_mem
  have hkey : ∀ d ∈ D, d ≠ 1 → ∀ s ∈ Sd d, ∃ hsN : s ∈ Subgroup.normalizer (K : Set X),
      rhoK K ⟨s, hsN⟩ ∈ σ.map (Yg K D1).subtype := by
    intro d hd hd1 s hs
    have hsT := hfam.le_pCore d hd hd1 hs
    have hsN := hB1 d hd hd1 hsT
    refine ⟨hsN, ?_⟩
    by_cases hdN : d ∈ Subgroup.normalizer (K : Set X)
    · by_cases hdC : d ∈ Subgroup.centralizer (K : Set X)
      · exact htriv s hsN (pCoreOf_le_centralizer_of_mem_centralizer hK hdC (hB1 d hd hd1) hsT)
      · set dN : ↥(Subgroup.normalizer (K : Set X)) := ⟨d, hdN⟩ with hdNdef
        have hdD1 : dN ∈ D1 := Subgroup.mem_subgroupOf.2 hd
        have hdp : dN ^ p = 1 := hD1exp dN hdD1
        have hsmem : (⟨s, hsN⟩ : ↥(Subgroup.normalizer (K : Set X))) ∈
            pCoreOf 2 (Subgroup.centralizer ({dN} : Set ↥(Subgroup.normalizer (K : Set X)))) :=
          subgroupOf_pCoreOf_le hdN (Subgroup.mem_subgroupOf.2 hsT)
        have hsY := rho_pCore_mem_Yg hKD hCore hK hCh hp hp2 hD1p hab hdD1 hdp hsmem
        have h1 : (⟨rhoK K ⟨s, hsN⟩, hsY⟩ : ↥(Yg K D1)) ∈
            SYg K D1 ⟨rhoK K dN, rho_mem_Yg_of_mem hdD1⟩ :=
          rho_pCore_subgroupOf_le hK hZK hab hdD1
            (Subgroup.mem_subgroupOf.2 (Subgroup.mem_map_of_mem _ hsmem))
        have hdh1 : (⟨rhoK K dN, rho_mem_Yg_of_mem hdD1⟩ : ↥(Yg K D1)) ≠ 1 := fun h =>
          hdC ((rhoK_eq_one_iff hK hdN).1 (congrArg Subtype.val h))
        have hdhD : (⟨rhoK K dN, rho_mem_Yg_of_mem hdD1⟩ : ↥(Yg K D1)) ∈ DYg K D1 :=
          Subgroup.mem_subgroupOf.2 (Subgroup.mem_map_of_mem _ hdD1)
        have h2 : (⟨rhoK K ⟨s, hsN⟩, hsY⟩ : ↥(Yg K D1)) ∈ σ :=
          (le_iSup₂_of_le _ hdhD (le_iSup_of_le hdh1 le_rfl) :
            SYg K D1 ⟨rhoK K dN, rho_mem_Yg_of_mem hdD1⟩ ≤ σ) h1
        exact ⟨_, h2, rfl⟩
    · exact htriv s hsN (le_centralizer_of_not_mem_normalizer' hp hK (hDp d hd) hdN
        (hB1 d hd hd1) le_rfl hsT)
  have hSdS : ∀ d ∈ D, d ≠ 1 → Sd d ≤ sigmaFam D Sd := fun d hd hd1 =>
    le_iSup_of_le d (le_iSup_of_le hd (le_iSup_of_le hd1 le_rfl))
  have hpull : ∀ s ∈ sigmaFam D Sd, ∃ hsN : s ∈ Subgroup.normalizer (K : Set X),
      rhoK K ⟨s, hsN⟩ ∈ σ.map (Yg K D1).subtype := by
    have hgen : ∀ T : Subgroup X, (∀ d ∈ D, d ≠ 1 → Sd d ≤ T) → sigmaFam D Sd ≤ T := by
      intro T hT
      unfold sigmaFam
      exact iSup_le fun d => iSup_le fun hd => iSup_le fun hd1 => hT d hd hd1
    have hle := hgen
      (((σ.map (Yg K D1).subtype).comap (rhoK K)).map (Subgroup.normalizer (K : Set X)).subtype)
      (fun d hd hd1 s hs => by
        obtain ⟨hsN, hmem⟩ := hkey d hd hd1 s hs
        exact ⟨⟨s, hsN⟩, Subgroup.mem_comap.2 hmem, rfl⟩)
    intro s hs
    obtain ⟨n, hn, rfl⟩ := hle hs
    exact ⟨n.2, hn⟩
  obtain ⟨d₀, hd₀, hd₀1, s₀, hs₀, hs₀C⟩ : ∃ d₀ ∈ D, d₀ ≠ 1 ∧ ∃ s₀ ∈ Sd d₀,
      s₀ ∉ Subgroup.centralizer (K : Set X) := by
    by_contra hcon
    push Not at hcon
    apply hnc
    unfold sigmaFam
    exact iSup_le fun d => iSup_le fun hd => iSup_le fun hd1 s hs => hcon d hd hd1 s hs
  have hs₀S : s₀ ∈ sigmaFam D Sd := hSdS d₀ hd₀ hd₀1 hs₀
  obtain ⟨hsN₀, hmem₀⟩ := hpull s₀ hs₀S
  have hσne : σ ≠ ⊥ := by
    intro h
    obtain ⟨y, hyσ, hy⟩ := Subgroup.mem_map.1 hmem₀
    rw [h, Subgroup.mem_bot] at hyσ
    rw [hyσ] at hy
    exact hs₀C ((rhoK_eq_one_iff hK hsN₀).1 (by simpa using hy.symm))
  have hΩY : IsOmegaTwo ε (n + 1) ↥(KhY K (Yg K D1)) :=
    isOmegaTwo_of_mulEquiv (iotaY hK hZK hKY) ε (n + 1) hΩ
  obtain ⟨hact, hfpf⟩ := hS3 ↥(Yg K D1) (KhY K (Yg K D1)) (isSimpleGroup_KhY hK hKY)
    (centralizer_KhY hK hKY) p hp hp2 (DYg K D1) (SYg K D1) hfamY hint.1 n ε hn hΩY hσne
  refine ⟨?_, hfpf⟩
  refine actsAsTransvectionAt_transport ε n (sigmaFam D Sd) K σ (KhY K (Yg K D1))
    (iotaY hK hZK hKY) ?_ ?_ hact
  · intro ψ hψ
    obtain ⟨φ, hφ, rfl⟩ := Subgroup.mem_map.1 hψ
    obtain ⟨w, hw, hwS, rfl⟩ := mem_inducedAutGroup.1 hφ
    obtain ⟨hwN, hmem⟩ := hpull w hwS
    obtain ⟨y, hyσ, hyw⟩ := Subgroup.mem_map.1 hmem
    have hwY : rhoK K ⟨w, hw⟩ ∈ Yg K D1 := by
      have := y.2
      rwa [show (y : MulAut (Kbar K)) = rhoK K ⟨w, hwN⟩ from hyw] at this
    have hyeq : (⟨rhoK K ⟨w, hw⟩, hwY⟩ : ↥(Yg K D1)) = y := Subtype.ext hyw.symm
    refine mem_inducedAutGroup.2 ⟨⟨rhoK K ⟨w, hw⟩, hwY⟩,
      Subgroup.le_normalizer_of_normal (Subgroup.mem_top _), ?_, ?_⟩
    · rw [hyeq]
      exact hyσ
    · exact (congr_iotaY_normalizerMonoidHom hK hZK hKY ⟨w, hw⟩ hwY).symm
  · intro h
    have hmem : (MulAut.congr (iotaY hK hZK hKY)).toMonoidHom
        (K.normalizerMonoidHom ⟨s₀, hsN₀⟩) ∈
        (inducedAutGroup (sigmaFam D Sd) K).map (MulAut.congr (iotaY hK hZK hKY)).toMonoidHom :=
      Subgroup.mem_map_of_mem _ (mem_inducedAutGroup.2 ⟨s₀, hsN₀, hs₀S, rfl⟩)
    rw [h, Subgroup.mem_bot] at hmem
    have h1 : K.normalizerMonoidHom ⟨s₀, hsN₀⟩ = 1 :=
      (MulAut.congr (iotaY hK hZK hKY)).injective (hmem.trans (map_one _).symm)
    exact hs₀C ((normalizerMonoidHom_eq_one_iff hsN₀).1 h1)

end CFSG.LocalAnalysis.GLTheoremB.Prop95I1920
