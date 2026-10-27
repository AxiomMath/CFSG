module

public import CFSG.GH74.GLS.Stage1.Thm3.Sec8.Fin81Cfg
public import CFSG.GH74.GLS.Stage1.Thm3.Sec8.Fin81AutSL2
public import CFSG.GH74.GLS.Stage1.Main.BrFusedPkg
public import CFSG.GH74.GLS.Stage2.Final.ModelLayerBar
public import CFSG.GroupTheory.QuasisimpleCommutingProductBound

public section

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.GH74.GLS.LU.Local

namespace CFSG.GH74.GLS.Stage1.Thm3.Sec8.Fin81

namespace ModelCfg

variable {Gs : Type} [Group Gs] {q : ℕ} {z' : Gs} {E₁ E₂ : Subgroup Gs}

theorem comm_of_comps [Finite Gs] (hc : LUComps Gs q z' E₁ E₂) :
    ∀ a ∈ E₁, ∀ b ∈ E₂, a * b = b * a := by
  intro a ha b hb
  have h1 := hc.comp₁
  have h2 := hc.comp₂
  rcases CFSG.LocalCores.distinct_components_commute h1.2 h2.2 with h | h
  · exfalso
    apply hc.ne
    have := congrArg (fun H : Subgroup ↥(centralizer ({z'} : Set Gs)) =>
      H.map (centralizer ({z'} : Set Gs)).subtype) h
    simpa [Subgroup.map_subgroupOf_eq_of_le h1.1, Subgroup.map_subgroupOf_eq_of_le h2.1] using this
  · have hle := Subgroup.commutator_eq_bot_iff_le_centralizer.mp h
    have hx : (⟨a, h1.1 ha⟩ : ↥(centralizer ({z'} : Set Gs))) ∈
        E₁.subgroupOf (centralizer ({z'} : Set Gs)) := ha
    have hy : (⟨b, h2.1 hb⟩ : ↥(centralizer ({z'} : Set Gs))) ∈
        E₂.subgroupOf (centralizer ({z'} : Set Gs)) := hb
    have := Subgroup.mem_centralizer_iff.mp (hle hx) _ hy
    exact (congrArg Subtype.val this).symm

theorem z_mem_left (hc : LUComps Gs q z' E₁ E₂) : z' ∈ E₁ := by
  have h : z' ∈ (center ↥E₁).map E₁.subtype := by
    rw [hc.cen₁]; exact Subgroup.mem_zpowers z'
  obtain ⟨x, -, hx⟩ := h
  rw [← hx]; exact x.2

theorem z_mem_right (hc : LUComps Gs q z' E₁ E₂) : z' ∈ E₂ := by
  have h : z' ∈ (center ↥E₂).map E₂.subtype := by
    rw [hc.cen₂]; exact Subgroup.mem_zpowers z'
  obtain ⟨x, -, hx⟩ := h
  rw [← hx]; exact x.2

theorem mem_zpowers_of_central_left (hc : LUComps Gs q z' E₁ E₂) {x : Gs} (hx : x ∈ E₁)
    (hcen : ∀ y ∈ E₁, x * y = y * x) : x ∈ zpowers z' := by
  have hmem : (⟨x, hx⟩ : ↥E₁) ∈ center ↥E₁ := by
    rw [Subgroup.mem_center_iff]
    intro g
    exact Subtype.ext (hcen g g.2).symm
  have h : x ∈ (center ↥E₁).map E₁.subtype := ⟨_, hmem, rfl⟩
  rwa [hc.cen₁] at h

theorem mem_zpowers_of_central_right (hc : LUComps Gs q z' E₁ E₂) {x : Gs} (hx : x ∈ E₂)
    (hcen : ∀ y ∈ E₂, x * y = y * x) : x ∈ zpowers z' := by
  have hmem : (⟨x, hx⟩ : ↥E₂) ∈ center ↥E₂ := by
    rw [Subgroup.mem_center_iff]
    intro g
    exact Subtype.ext (hcen g g.2).symm
  have h : x ∈ (center ↥E₂).map E₂.subtype := ⟨_, hmem, rfl⟩
  rwa [hc.cen₂] at h

theorem inf_eq_zpowers [Finite Gs] (hc : LUComps Gs q z' E₁ E₂) : E₁ ⊓ E₂ = zpowers z' := by
  apply le_antisymm
  · intro x hx
    exact mem_zpowers_of_central_left hc hx.1 fun y hy => (comm_of_comps hc y hy x hx.2).symm
  · exact Subgroup.zpowers_le.mpr ⟨z_mem_left hc, z_mem_right hc⟩

theorem card_inf_eq_two [Finite Gs] (hc : LUComps Gs q z' E₁ E₂) (hz : orderOf z' = 2) :
    Nat.card ↥(E₁ ⊓ E₂) = 2 := by
  rw [inf_eq_zpowers hc, Nat.card_zpowers, hz]

theorem Ez_le_centralizer (z : Gs) : IVK.Ez z ≤ centralizer ({z} : Set Gs) :=
  Subgroup.map_subtype_le _

theorem centralizer_le_normalizer_Ez (z : Gs) :
    centralizer ({z} : Set Gs) ≤ normalizer ((IVK.Ez z : Subgroup Gs) : Set Gs) := by
  have hn : ((IVK.Ez z).subgroupOf (centralizer ({z} : Set Gs))).Normal := by
    have h : (IVK.Ez z).subgroupOf (centralizer ({z} : Set Gs)) =
        layer ↥(centralizer ({z} : Set Gs)) := by
      unfold IVK.Ez
      rw [Subgroup.subgroupOf, Subgroup.comap_map_eq_self_of_injective
        (centralizer ({z} : Set Gs)).subtype_injective]
    rw [h]
    have : (layer ↥(centralizer ({z} : Set Gs))).Characteristic :=
      CFSG.LocalCores.layer_characteristic
    infer_instance
  exact (Subgroup.normal_subgroupOf_iff_le_normalizer (Ez_le_centralizer z)).mp hn

theorem z_mem_of_center {S : Subgroup Gs}
    (hz : (center ↥S).map S.subtype = zpowers z') : z' ∈ S := by
  have h : z' ∈ (center ↥S).map S.subtype := by
    rw [hz]; exact Subgroup.mem_zpowers z'
  obtain ⟨x, -, hx⟩ := h
  rw [← hx]; exact x.2

theorem comm_of_center {S : Subgroup Gs}
    (hz : (center ↥S).map S.subtype = zpowers z') : ∀ s ∈ S, s * z' = z' * s := by
  have h : z' ∈ (center ↥S).map S.subtype := by
    rw [hz]; exact Subgroup.mem_zpowers z'
  obtain ⟨x, hx, rfl⟩ := h
  intro s hs
  have := Subgroup.mem_center_iff.mp hx ⟨s, hs⟩
  exact congrArg Subtype.val this

theorem le_centralizer_of_center {S : Subgroup Gs}
    (hz : (center ↥S).map S.subtype = zpowers z') : S ≤ centralizer ({z'} : Set Gs) := by
  intro s hs
  rw [Subgroup.mem_centralizer_singleton_iff]
  exact comm_of_center hz s hs

theorem isSylowOf_of_le [Finite Gs] (S : Sylow 2 Gs) {K : Subgroup Gs}
    (hSK : (S : Subgroup Gs) ≤ K) : CFSG.ABGLocalTools.IsSylowOf 2 (S : Subgroup Gs) K := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have htop : CFSG.ABGLocalTools.IsSylowOf 2 (S : Subgroup Gs) ⊤ := by
    rw [CFSG.ABGLocalTools.isSylowOf_iff]
    refine ⟨le_top, S.isPGroup', ?_⟩
    rw [Subgroup.relIndex_top_right]
    exact S.not_dvd_index
  exact htop.of_le hSK le_top

theorem isSylowOf_inf_Ez [Finite Gs] (S : Sylow 2 Gs) {z : Gs}
    (hS : (S : Subgroup Gs) ≤ centralizer ({z} : Set Gs)) :
    CFSG.ABGLocalTools.IsSylowOf 2 ((S : Subgroup Gs) ⊓ IVK.Ez z) (IVK.Ez z) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact (isSylowOf_of_le S hS).inf_of_le_normalizer (Ez_le_centralizer z)
    (centralizer_le_normalizer_Ez z)

theorem sup_le_normalizer_left {A B : Subgroup Gs} (hcomm : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a) :
    A ⊔ B ≤ normalizer (A : Set Gs) := by
  refine sup_le Subgroup.le_normalizer ?_
  refine le_trans ?_ (Subgroup.centralizer_le_normalizer (A : Set Gs))
  intro b hb
  rw [Subgroup.mem_centralizer_iff]
  intro a ha
  exact hcomm a ha b hb

theorem isSylowOf_inf_left [Finite Gs] (S : Sylow 2 Gs) {z : Gs}
    (hS : (S : Subgroup Gs) ≤ centralizer ({z} : Set Gs)) {A B : Subgroup Gs}
    (hcomm : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a) (hE : IVK.Ez z = A ⊔ B) :
    CFSG.ABGLocalTools.IsSylowOf 2 ((S : Subgroup Gs) ⊓ A) A := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h := isSylowOf_inf_Ez S hS
  rw [hE] at h
  have h1 := h.inf_of_le_normalizer (N := A) le_sup_left (sup_le_normalizer_left hcomm)
  have e : (A ⊔ B) ⊓ A = A := inf_eq_right.mpr le_sup_left
  rwa [inf_assoc, e] at h1

theorem card_sylow_eq_eight [Finite Gs] {A P : Subgroup Gs}
    (hP : CFSG.ABGLocalTools.IsSylowOf 2 P A) (hq8 : q % 8 = 3 ∨ q % 8 = 5)
    (hA : Nat.card ↥A = q * (q ^ 2 - 1)) : Nat.card ↥P = 8 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [hP.card_eq, hA, factorization_two_card_sl2 q hq8]
  norm_num

theorem nonempty_mulEquiv_SL2 {X : Subgroup Gs} (h : HasSL2Model ↥X (fun r => r = q))
    (F : Type) [Field F] [Finite F] (hF : Nat.card F = q) :
    Nonempty (↥X ≃* Matrix.SpecialLinearGroup (Fin 2) F) := by
  obtain ⟨F₀, _, _, hF₀, ⟨e⟩⟩ := h
  have : Fintype F := Fintype.ofFinite F
  have : Fintype F₀ := Fintype.ofFinite F₀
  have hcard : Fintype.card F = Fintype.card F₀ := by
    rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, hF, hF₀]
  let φ : F ≃+* F₀ := FiniteField.ringEquivOfCardEq hcard
  exact ⟨e.trans ((specialLinearGroupEquivStatedSL 2 F₀).symm.trans
    (CFSG.ClassicalModels.specialLinearFieldEquiv φ.symm (Fin 2)))⟩

theorem card_of_equiv_SL2 {X : Subgroup Gs} (F : Type) [Field F] [Finite F] (hF : Nat.card F = q)
    (e : ↥X ≃* Matrix.SpecialLinearGroup (Fin 2) F) : Nat.card ↥X = q * (q ^ 2 - 1) := by
  rw [Nat.card_congr e.toEquiv, CFSG.SL2MinimalFaithful.card_specialLinearGroup_fin_two, hF]

theorem inf_sup_eq_sup_inf [Finite Gs] {S : Subgroup Gs} {A B : Subgroup Gs} {z : Gs}
    (hq8 : q % 8 = 3 ∨ q % 8 = 5) (hz : orderOf z = 2) (hzS : z ∈ S)
    (hcomm : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a) (hAB : A ⊓ B = zpowers z)
    (hSyl : CFSG.ABGLocalTools.IsSylowOf 2 (S ⊓ (A ⊔ B)) (A ⊔ B))
    (hA : Nat.card ↥A = q * (q ^ 2 - 1)) (hB : Nat.card ↥B = q * (q ^ 2 - 1))
    (hPA : Nat.card ↥(S ⊓ A) = 8) (hPB : Nat.card ↥(S ⊓ B) = 8) :
    S ⊓ (A ⊔ B) = (S ⊓ A) ⊔ (S ⊓ B) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hle : (S ⊓ A) ⊔ (S ⊓ B) ≤ S ⊓ (A ⊔ B) :=
    sup_le (inf_le_inf_left _ le_sup_left) (inf_le_inf_left _ le_sup_right)
  refine (Subgroup.eq_of_le_of_card_ge hle ?_).symm
  have hinf : (S ⊓ A) ⊓ (S ⊓ B) = zpowers z := by
    apply le_antisymm
    · intro x hx
      rw [← hAB]
      exact ⟨hx.1.2, hx.2.2⟩
    · intro x hx
      have hx' : x ∈ A ⊓ B := hAB ▸ hx
      have hxS : x ∈ S := (Subgroup.zpowers_le.mpr hzS) hx
      exact ⟨⟨hxS, hx'.1⟩, ⟨hxS, hx'.2⟩⟩
  have h1 := (CFSG.GroupTheory.card_sup_mul_card_inf_of_commute (S ⊓ A) (S ⊓ B)
    (fun x hx y hy => hcomm x hx.2 y hy.2)).1
  rw [hinf, Nat.card_zpowers, hz, hPA, hPB] at h1
  have hP : Nat.card ↥((S ⊓ A) ⊔ (S ⊓ B)) = 32 := by omega
  have h2 := (CFSG.GroupTheory.card_sup_mul_card_inf_of_commute A B hcomm).1
  rw [hAB, Nat.card_zpowers, hz, hA, hB] at h2
  have hpos : 0 < Nat.card ↥(A ⊔ B) := Nat.card_pos
  have hm3 : (q * (q ^ 2 - 1)).factorization 2 = 3 := factorization_two_card_sl2 q hq8
  have hm0 : q * (q ^ 2 - 1) ≠ 0 := by
    intro h0
    rw [h0] at h2
    omega
  have hf : (Nat.card ↥(A ⊔ B)).factorization 2 = 5 := by
    have h3 : (Nat.card ↥(A ⊔ B) * 2).factorization 2 =
        (q * (q ^ 2 - 1) * (q * (q ^ 2 - 1))).factorization 2 := by rw [h2]
    rw [Nat.factorization_mul hpos.ne' (by norm_num), Nat.factorization_mul hm0 hm0] at h3
    simp [hm3, Nat.prime_two.factorization_self] at h3
    omega
  rw [hP, hSyl.card_eq, hf]
  norm_num

end ModelCfg

theorem fusedCfg_of_fusedPkg {Gs : Type} [Group Gs] [Finite Gs] {q : ℕ} {ε : ℤ} {z' : Gs}
    {S' : Sylow 2 Gs} {E₁ E₂ : Subgroup Gs} {t u n : Gs}
    (hpkg : CFSG.GH74.GLS.Stage1.Main.FusedPkg Gs q ε z' S' E₁ E₂ t u n)
    (hq8 : q % 8 = 3 ∨ q % 8 = 5) (h5 : 5 ≤ q) (F : Type) [Field F] [Finite F]
    (hF : Nat.card F = q) : FusedCfg E₁ E₂ (S' : Subgroup Gs) F := by
  have _h5 := h5
  have hc := hpkg.data.comps
  have hs := hpkg.data.syl
  have hcomm := ModelCfg.comm_of_comps hc
  obtain ⟨e₁⟩ := ModelCfg.nonempty_mulEquiv_SL2 hc.sl₁ F hF
  obtain ⟨e₂⟩ := ModelCfg.nonempty_mulEquiv_SL2 hc.sl₂ F hF
  have hSC : (S' : Subgroup Gs) ≤ centralizer ({z'} : Set Gs) :=
    ModelCfg.le_centralizer_of_center hs.z_cen
  have hS1 := ModelCfg.isSylowOf_inf_left S' hSC hcomm hpkg.layer
  have hS2 := ModelCfg.isSylowOf_inf_left S' hSC (fun b hb a ha => (hcomm a ha b hb).symm)
    (hpkg.layer.trans (sup_comm E₁ E₂))
  have hE := ModelCfg.isSylowOf_inf_Ez S' hSC
  rw [hpkg.layer] at hE
  have hA₁ := ModelCfg.card_of_equiv_SL2 F hF e₁
  have hA₂ := ModelCfg.card_of_equiv_SL2 F hF e₂
  have hcard₁ := ModelCfg.card_sylow_eq_eight hS1 hq8 hA₁
  have hcard₂ := ModelCfg.card_sylow_eq_eight hS2 hq8 hA₂
  have hzS : z' ∈ (S' : Subgroup Gs) := ModelCfg.z_mem_of_center hs.z_cen
  exact
    { e₁ := ⟨e₁⟩
      e₂ := ⟨e₂⟩
      comm := hcomm
      card_inf := ModelCfg.card_inf_eq_two hc hs.z_inv
      cen₁ := fun x hx hx' => Subgroup.zpowers_le.mpr (ModelCfg.z_mem_right hc)
        (ModelCfg.mem_zpowers_of_central_left hc hx hx')
      cen₂ := fun x hx hx' => Subgroup.zpowers_le.mpr (ModelCfg.z_mem_left hc)
        (ModelCfg.mem_zpowers_of_central_right hc hx hx')
      pgroup := S'.isPGroup'
      norm := by
        rw [← hpkg.layer]
        exact hSC.trans (ModelCfg.centralizer_le_normalizer_Ez z')
      card₁ := hcard₁
      card₂ := hcard₂
      prod := ModelCfg.inf_sup_eq_sup_inf hq8 hs.z_inv hzS hcomm (ModelCfg.inf_eq_zpowers hc) hE
        hA₁ hA₂ hcard₁ hcard₂
      z_ex := ⟨z', ⟨ModelCfg.z_mem_left hc, ModelCfg.z_mem_right hc⟩, hs.z_inv, hzS,
        ModelCfg.comm_of_center hs.z_cen⟩ }

theorem model_c1_equiv {Gs : Type} [Group Gs] [Finite Gs] {p f : ℕ} {ε : ℤ} {z' : Gs}
    {S' : Sylow 2 Gs} {E₁ E₂ : Subgroup Gs} {t u n : Gs}
    (hpkg : CFSG.GH74.GLS.Stage1.Main.FusedPkg Gs (p ^ f) ε z' S' E₁ E₂ t u n) (hp : p.Prime)
    (hp2 : p ≠ 2) (h5 : 5 ≤ p ^ f)
    (hlie : (p ^ f % 8 = 5 ∧ LieModel Gs .PSL 4 p f) ∨ (p ^ f % 8 = 3 ∧ LieModel Gs .PSU 4 p f)) :
    Nonempty (↥(E₁ ⊔ E₂ ⊔ (S' : Subgroup Gs)) ≃* ↥(oPrimeResidual 2 (CentralizerBar z'))) := by
  have hcl : CFSG.GH74.GLS.Stage2.Final.IsClassicalModel Gs p f := by
    refine ⟨hp, hp2, by omega, ?_⟩
    rcases hlie with ⟨h8, hL⟩ | ⟨h8, hU⟩
    · exact Or.inr (Or.inl ⟨by omega, hL⟩)
    · exact Or.inr (Or.inr ⟨by omega, hU⟩)
  obtain ⟨hint, himg⟩ := CFSG.GH74.GLS.Stage2.Final.modelLayerBar Gs p f S' z' hcl
    (hlie.imp (fun h => h.2) (fun h => h.2)) hpkg.data.syl.z_inv hpkg.data.syl.z_cen
  have hX : layerTimesSylow z' (S' : Subgroup Gs) = E₁ ⊔ E₂ ⊔ (S' : Subgroup Gs) := by
    show IVK.Ez z' ⊔ _ = _
    rw [hpkg.layer]
  rw [hX] at hint himg
  have hXC : E₁ ⊔ E₂ ⊔ (S' : Subgroup Gs) ≤ centralizer ({z'} : Set Gs) :=
    sup_le (by rw [← hpkg.layer]; exact ModelCfg.Ez_le_centralizer z')
      (ModelCfg.le_centralizer_of_center hpkg.data.syl.z_cen)
  let φ : ↥(E₁ ⊔ E₂ ⊔ (S' : Subgroup Gs)) →* CentralizerBar z' :=
    (CFSG.GH74.GLS.Stage2.Local.toBar z').comp (Subgroup.inclusion hXC)
  have hinj : Function.Injective φ := by
    rw [injective_iff_map_eq_one]
    intro x hx
    have h1 : (⟨(x : Gs), hXC x.2⟩ : ↥(centralizer ({z'} : Set Gs))) ∈
        pPrimeCore 2 ↥(centralizer ({z'} : Set Gs)) := (QuotientGroup.eq_one_iff _).mp hx
    have h2 : (x : Gs) ∈ CFSG.GH74.GLS.Stage2.Local.OddCore z' := ⟨_, h1, rfl⟩
    have h3 : (x : Gs) ∈ (E₁ ⊔ E₂ ⊔ (S' : Subgroup Gs)) ⊓
        CFSG.GH74.GLS.Stage2.Local.OddCore z' := ⟨x.2, h2⟩
    rw [hint] at h3
    exact Subtype.ext (Subgroup.mem_bot.mp h3)
  have hrange : φ.range = oPrimeResidual 2 (CentralizerBar z') := by
    rw [← himg]
    ext y
    constructor
    · rintro ⟨x, rfl⟩
      exact ⟨Subgroup.inclusion hXC x, x.2, rfl⟩
    · rintro ⟨c, hc, rfl⟩
      exact ⟨⟨(c : Gs), hc⟩, rfl⟩
  exact ⟨(MonoidHom.ofInjective hinj).trans (MulEquiv.subgroupCongr hrange)⟩

end CFSG.GH74.GLS.Stage1.Thm3.Sec8.Fin81
