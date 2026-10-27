module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanRankOneCoreLin
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanRankOneCoreUnitary
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanRankOneCoreRee
public import CFSG.CharacterTheory.PSL2Table.Classes

public section

namespace CFSG.AGLEmbedding.KFactProofs.RankOneCore

def CommBorel (K : Type*) [Group K] (T : Subgroup K) : Prop :=
  ∃ C : Subgroup K, (∀ x ∈ C, ∀ y ∈ C, x * y = y * x) ∧
    Subgroup.normalizer (T : Set K) = T ⊔ C

theorem CommBorel.comm_mem {K : Type*} [Group K] {T : Subgroup K} (h : CommBorel K T) {x y : K}
    (hx : x ∈ Subgroup.normalizer (T : Set K)) (hy : y ∈ Subgroup.normalizer (T : Set K)) :
    x * y * x⁻¹ * y⁻¹ ∈ T := by
  obtain ⟨C, hC, hN⟩ := h
  have hCN : C ≤ Subgroup.normalizer (T : Set K) := hN ▸ le_sup_right
  set N : Subgroup K := Subgroup.normalizer (T : Set K) with hNdef
  have hsup : T.subgroupOf N ⊔ C.subgroupOf N = ⊤ := by
    rw [← Subgroup.subgroupOf_sup Subgroup.le_normalizer hCN, ← hN]
    exact Subgroup.subgroupOf_self N
  let φ : C.subgroupOf N →* N ⧸ T.subgroupOf N :=
    (QuotientGroup.mk' (T.subgroupOf N)).comp (C.subgroupOf N).subtype
  have hφ : Function.Surjective φ := by
    intro q
    obtain ⟨n, rfl⟩ := QuotientGroup.mk_surjective q
    have hn : n ∈ T.subgroupOf N ⊔ C.subgroupOf N := by rw [hsup]; exact Subgroup.mem_top n
    obtain ⟨t, ht, c, hc, rfl⟩ := Subgroup.mem_sup_of_normal_left.mp hn
    refine ⟨⟨c, hc⟩, ?_⟩
    simp only [φ, MonoidHom.coe_comp, Function.comp_apply, QuotientGroup.mk'_apply,
      Subgroup.coe_subtype]
    rw [QuotientGroup.mk_mul, (QuotientGroup.eq_one_iff t).mpr ht, one_mul]
  have hcomm : IsMulCommutative (N ⧸ T.subgroupOf N) := by
    refine ⟨⟨fun q₁ q₂ => ?_⟩⟩
    obtain ⟨c₁, rfl⟩ := hφ q₁
    obtain ⟨c₂, rfl⟩ := hφ q₂
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (Subtype.ext (hC _ c₁.2 _ c₂.2))
  have hle := Subgroup.Normal.quotient_commutative_iff_commutator_le.mp hcomm
  have := hle (Subgroup.commutator_mem_commutator (Subgroup.mem_top (⟨x, hx⟩ : N))
    (Subgroup.mem_top (⟨y, hy⟩ : N)))
  exact this

theorem exists_mem_normalizer_map_eq {G L : Type*} [Group G] [Finite G] [Group L] {p : ℕ}
    [Fact p.Prime] (π : G →* L) (hπ : Function.Surjective π) (S : Sylow p G) (TL : Subgroup L)
    (hS : (S : Subgroup G).map π = TL) {x : L} (hx : x ∈ Subgroup.normalizer (TL : Set L)) :
    ∃ a ∈ Subgroup.normalizer ((S : Subgroup G) : Set G), π a = x := by
  obtain ⟨g, rfl⟩ := hπ x
  set M : Subgroup G := TL.comap π with hM
  have hSM : (S : Subgroup G) ≤ M := by
    rw [hM, ← Subgroup.map_le_iff_le_comap, hS]
  have hgS : ((g • S : Sylow p G) : Subgroup G) ≤ M := by
    intro z hz
    rw [Sylow.coe_subgroup_smul, Subgroup.pointwise_smul_def] at hz
    obtain ⟨s, hs, rfl⟩ := hz
    have hπs : π s ∈ TL := hS ▸ Subgroup.mem_map_of_mem π hs
    have := (Subgroup.mem_normalizer_iff.mp hx (π s)).mp hπs
    show π (g * s * g⁻¹) ∈ TL
    simpa [map_mul, map_inv] using this
  obtain ⟨m, hm⟩ := MulAction.exists_smul_eq M ((g • S).subtype hgS) (S.subtype hSM)
  rw [Sylow.smul_subtype hgS m] at hm
  have hm' : (m : G) • (g • S : Sylow p G) = S := Sylow.subtype_injective hm
  have ha : ((m : G) * g) ∈ Subgroup.normalizer ((S : Subgroup G) : Set G) :=
    Sylow.smul_eq_iff_mem_normalizer.mp (by rw [mul_smul]; exact hm')
  have hπm : π (m : G) ∈ (S : Subgroup G).map π := by rw [hS]; exact m.2
  obtain ⟨s, hs, hsm⟩ := hπm
  refine ⟨s⁻¹ * ((m : G) * g), Subgroup.mul_mem _ (Subgroup.inv_mem _
    (Subgroup.le_normalizer hs)) ha, ?_⟩
  rw [map_mul, map_inv, map_mul, hsm]
  group

theorem comm_mem_normalizer_of_section {K L : Type*} [Group K] [Finite K] [Group L] {p : ℕ}
    [Fact p.Prime] (hTI : ∀ T : Sylow p K, RankOneCoreData K (T : Subgroup K))
    (hCB : ∀ T : Sylow p K, CommBorel K (T : Subgroup K)) (A : Subgroup K) (π : A →* L)
    (hπ : Function.Surjective π) (TL : Sylow p L) (hTL : (TL : Subgroup L) ≠ ⊥) {x y : L}
    (hx : x ∈ Subgroup.normalizer ((TL : Subgroup L) : Set L))
    (hy : y ∈ Subgroup.normalizer ((TL : Subgroup L) : Set L)) :
    x * y * x⁻¹ * y⁻¹ ∈ (TL : Subgroup L) := by
  classical
  obtain ⟨S, hS⟩ := Sylow.mapSurjective_surjective hπ p TL
  have hS' : (S : Subgroup A).map π = TL := by
    have := congrArg (fun P : Sylow p L => (P : Subgroup L)) hS
    simpa using this
  have hSne : (S : Subgroup A) ≠ ⊥ := by
    intro h
    apply hTL
    rw [← hS', h, Subgroup.map_bot]
  obtain ⟨a, ha, rfl⟩ := exists_mem_normalizer_map_eq π hπ S (TL : Subgroup L) hS' hx
  obtain ⟨b, hb, rfl⟩ := exists_mem_normalizer_map_eq π hπ S (TL : Subgroup L) hS' hy
  set S'' : Subgroup K := (S : Subgroup A).map A.subtype with hS''
  have hp'' : IsPGroup p S'' := S.2.map A.subtype
  obtain ⟨T, hT⟩ := hp''.exists_le_sylow
  have hne : S'' ≠ ⊥ := by
    intro h
    rw [hS'', Subgroup.map_eq_bot_iff, A.ker_subtype, le_bot_iff] at h
    exact hSne h
  have hN : ∀ c ∈ Subgroup.normalizer ((S : Subgroup A) : Set A),
      (c : K) ∈ Subgroup.normalizer (S'' : Set K) := fun c hc =>
    Subgroup.le_normalizer_map A.subtype (Subgroup.mem_map_of_mem A.subtype hc)
  have h1 := (hTI T).normalizer_le S'' hT hne (hN a ha)
  have h2 := (hTI T).normalizer_le S'' hT hne (hN b hb)
  have h3 := (hCB T).comm_mem h1 h2
  have hTA : (T : Subgroup K).comap A.subtype = (S : Subgroup A) := by
    refine S.is_maximal' ?_ ?_
    · exact T.2.comap_of_injective A.subtype A.subtype_injective
    · intro s hs
      exact hT (Subgroup.mem_map_of_mem A.subtype hs)
  have h4 : a * b * a⁻¹ * b⁻¹ ∈ (S : Subgroup A) := by
    rw [← hTA]
    exact h3
  have h5 := Subgroup.mem_map_of_mem π h4
  rw [hS'] at h5
  simpa using h5

open CFSG.AGLEmbedding.KFactProofs.SmallGamma

theorem CommBorel.of_equiv {L L' : Type*} [Group L] [Group L'] {T : Subgroup L}
    {T' : Subgroup L'} (e : L ≃* L') (hT : ∀ g, g ∈ T ↔ e g ∈ T') (h : CommBorel L' T') :
    CommBorel L T := by
  obtain ⟨C', hC', hN'⟩ := h
  have hTm : T = T'.map e.symm.toMonoidHom := by
    ext g
    rw [Subgroup.mem_map_equiv]
    simpa using hT g
  have hNm : Subgroup.normalizer (T : Set L) =
      (Subgroup.normalizer (T' : Set L')).map e.symm.toMonoidHom := by
    ext g
    rw [Subgroup.mem_map_equiv]
    simpa using SmallGammaData.mem_normalizer_iff e hT g
  refine ⟨C'.map e.symm.toMonoidHom, ?_, ?_⟩
  · rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    simp only [MulEquiv.coe_toMonoidHom, ← map_mul]
    exact congrArg e.symm (hC' x hx y hy)
  · rw [hNm, hN', Subgroup.map_sup, ← hTm]

theorem CommBorel.of_equiv_map {L L' : Type*} [Group L] [Group L'] {T : Subgroup L}
    {T' : Subgroup L'} (e : L ≃* L') (hT : T.map e.toMonoidHom = T') (h : CommBorel L' T') :
    CommBorel L T :=
  CommBorel.of_equiv e (fun g => by
    rw [← hT, Subgroup.mem_map_equiv, MulEquiv.symm_apply_apply]) h

theorem CommBorel.of_equiv_sylow {L L' : Type*} [Group L] [Finite L] [Group L'] {p : ℕ}
    [Fact p.Prime] (e : L ≃* L') (U : Sylow p L) (S : Sylow p L')
    (hS : CommBorel L' (S : Subgroup L')) : CommBorel L (U : Subgroup L) := by
  obtain ⟨e', he'⟩ := exists_equiv_map_eq e U S
  exact CommBorel.of_equiv_map e' he' hS

theorem mul_comm_of_isCyclic {K : Type*} [Group K] {C : Subgroup K} (h : IsCyclic C) :
    ∀ x ∈ C, ∀ y ∈ C, x * y = y * x := by
  intro x hx y hy
  let _ : CommGroup C := IsCyclic.commGroup
  exact congrArg Subtype.val (mul_comm (⟨x, hx⟩ : C) ⟨y, hy⟩)

section LinTwo

open CFSG.PSL2Table CFSG.GH74.GLS.IVK
open scoped MatrixGroups

theorem commBorel_unipotent {F : Type} [Field F] [Finite F] (h2 : (2 : F) ≠ 0) :
    CommBorel PSL(2, F) (unipotent F) :=
  ⟨splitTorus F, mul_comm_of_isCyclic splitTorus_isCyclic, by
    rw [L2Borel.normalizer_unipotent_eq h2, L2Borel.unipotent_sup_splitTorus]⟩

theorem commBorel_linTwo {L : Type} [Group L] [Finite L] {p n : ℕ} [Fact p.Prime]
    (hp2 : p ≠ 2) (hn : 1 ≤ n) {d : TauCeti.ValidLieTypeIndex} (hd : IsLinTwoIndex p n d)
    (h : Nonempty (L ≃* CatGroup d)) (U : Sylow p L) : CommBorel L (U : Subgroup L) := by
  obtain ⟨eP⟩ := nonempty_mulEquiv_psl2GF_of_isLinTwoIndex hd
  obtain ⟨e₀⟩ := h
  let e : L ≃* PSL2GF p n := e₀.trans eP
  have hF : Nat.card (GaloisField p n) = p ^ n := GaloisField.card p n (by omega)
  have : Fintype (GaloisField p n) := Fintype.ofFinite _
  have h2 : (2 : GaloisField p n) ≠ 0 := by
    intro h0
    have h1 : ((2 : ℕ) : GaloisField p n) = 0 := by simpa using h0
    have := (CharP.cast_eq_zero_iff (GaloisField p n) p 2).1 h1
    exact hp2 ((Nat.prime_dvd_prime_iff_eq Fact.out Nat.prime_two).1 this)
  obtain ⟨Q, hQ⟩ := L2Borel.exists_sylow_unipotent (F := GaloisField p n) hF
  refine CommBorel.of_equiv_sylow e U Q ?_
  rw [hQ]
  exact commBorel_unipotent h2

end LinTwo

section Unitary

open CFSG.BenderSuzuki.MatrixGroups CFSG.UnitaryThreeRecognition.Model

variable {K : Type} [Field K] [Finite K] (J : HermitianForm 3 K)
  (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0]) {p f : ℕ}
  (hK : Nat.card K = (p ^ f) ^ 2) (hfix : Nat.card {x : K // J.conj x = x} = p ^ f)

include hK hfix

theorem commBorel_rootGroup [Fact p.Prime] (hq : 2 < p ^ f) :
    CommBorel (ProjectiveSpecialUnitaryMatrixGroup J) (rootGroup J hJ) :=
  ⟨torusGroup J hJ, mul_comm_of_isCyclic (isCyclic_torusGroup J hJ (p ^ f) hK hfix), by
    rw [UnitaryModel.normalizer_rootGroup_eq_stabilizer J hJ hK hfix hq,
      rootGroup_sup_torusGroup J hJ (p ^ f) hK hfix]⟩

end Unitary

theorem commBorel_unitary {L : Type} [Group L] [Finite L] {p : ℕ}
    {d : TauCeti.ValidLieTypeIndex} (hd : IsUnitaryIndex p d) (h : Nonempty (L ≃* CatGroup d))
    (U : Sylow p L) : CommBorel L (U : Subgroup L) := by
  obtain ⟨hp, hf, hq, K, _, _, J, hJ, hK, hfix, ⟨e⟩⟩ :=
    UnitaryModel.exists_equiv_psu (UnitaryModel.statedClassicalModel hd h)
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨S, hS⟩ := UnitaryModel.exists_sylow_eq_rootGroup J hJ hK hfix hf
  refine CommBorel.of_equiv_sylow e U S ?_
  rw [hS]
  exact commBorel_rootGroup J hJ hK hfix hq

section Ree

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Ree CFSG.LieType.Ree.ReeTag

theorem reeFixedBorel_eq_sup {t : ReeTag} {a : ℕ} {K : Type} [Field K] [Finite K]
    [CharP K t.prime] :
    t.reeFixedBorel K a = t.reeFixedPosUnipotent K a ⊔ t.reeFixedTorus K a := by
  refine le_antisymm (fun b hb => ?_) (sup_le reeFixedPosUnipotent_le_reeFixedBorel
    reeFixedTorus_le_reeFixedBorel)
  have hb' : b ∈ (t.reeFixedBorel K a : Set (ModGL t.tag K)) := hb
  rw [reeFixedBorel_eq_mul] at hb'
  obtain ⟨h, hh, u, hu, rfl⟩ := hb'
  rw [sup_comm]
  exact Subgroup.mul_mem_sup hh hu

theorem commBorel_stdU {a : ℕ} {K : Type} [Field K] [Finite K]
    [CharP K ReeTag.G2.prime] (hK : Nat.card K = 3 ^ (2 * a + 1)) :
    CommBorel ↥(ReeTag.G2.reeGamma K a) (ReeModel.stdU a K) := by
  obtain ⟨-, hNU, -, -⟩ := ReeModel.std_facts hK
  refine ⟨(ReeTag.G2.reeFixedTorus K a).subgroupOf (ReeTag.G2.reeGamma K a), ?_, ?_⟩
  · intro x hx y hy
    exact Subtype.ext (reeFixedTorus_mul_comm hx hy)
  · rw [hNU]
    show (ReeTag.G2.reeFixedBorel K a).subgroupOf (ReeTag.G2.reeGamma K a) =
      (ReeTag.G2.reeFixedPosUnipotent K a).subgroupOf (ReeTag.G2.reeGamma K a) ⊔
        (ReeTag.G2.reeFixedTorus K a).subgroupOf (ReeTag.G2.reeGamma K a)
    have hH : ReeTag.G2.reeFixedTorus K a ≤ ReeTag.G2.reeGamma K a := inf_le_right
    rw [← Subgroup.subgroupOf_sup reeFixedPosUnipotent_le_reeGamma hH, reeFixedBorel_eq_sup]

theorem commBorel_ree {L : Type} [Group L] [Finite L]
    {d : TauCeti.ValidLieTypeIndex} (hd : IsReeGTwoIndex 3 d) (h : Nonempty (L ≃* CatGroup d))
    (U : Sylow 3 L) : CommBorel L (U : Subgroup L) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨a, ha, hfe, ⟨e⟩⟩ := ReeModel.exists_equiv_reeGamma hd h
  have hK : Nat.card (GaloisField 3 (2 * a + 1)) = 3 ^ (2 * a + 1) :=
    GaloisField.card 3 (2 * a + 1) (by omega)
  obtain ⟨⟨P, hP⟩, -, -, -⟩ := ReeModel.std_facts hK
  refine CommBorel.of_equiv_sylow e U P ?_
  rw [hP]
  exact commBorel_stdU hK

end Ree

theorem comm_mem_normalizer_of_section_rankOne
    {K L : Type} [Group K] [Finite K] [Group L] {p : ℕ}
    [Fact p.Prime] (hp2 : p ≠ 2) {d : TauCeti.ValidLieTypeIndex}
    (hd : (∃ n : ℕ, 3 ≤ n ∧ IsLinTwoIndex p n d) ∨ (IsUnitaryIndex p d ∧ 2 ≤ d.1.fieldExponent) ∨
      IsReeGTwoIndex p d)
    (hK : Nonempty (K ≃* CatGroup d)) (A : Subgroup K) (π : A →* L)
    (hπ : Function.Surjective π) (TL : Sylow p L) (hTL : (TL : Subgroup L) ≠ ⊥) {x y : L}
    (hx : x ∈ Subgroup.normalizer ((TL : Subgroup L) : Set L))
    (hy : y ∈ Subgroup.normalizer ((TL : Subgroup L) : Set L)) :
    x * y * x⁻¹ * y⁻¹ ∈ (TL : Subgroup L) := by
  rcases hd with ⟨n, hn, hlin⟩ | ⟨hu, -⟩ | ⟨rfl, hm⟩
  · exact comm_mem_normalizer_of_section (fun T => rankOneCoreData_linTwo hp2 (by omega) hlin hK T)
      (fun T => commBorel_linTwo hp2 (by omega) hlin hK T) A π hπ TL hTL hx hy
  · exact comm_mem_normalizer_of_section (fun T => rankOneCoreData_unitary hu hK T)
      (fun T => commBorel_unitary hu hK T) A π hπ TL hTL hx hy
  · exact comm_mem_normalizer_of_section (fun T => rankOneCoreData_ree ⟨rfl, hm⟩ hK T)
      (fun T => commBorel_ree ⟨rfl, hm⟩ hK T) A π hπ TL hTL hx hy

end CFSG.AGLEmbedding.KFactProofs.RankOneCore
