module

public import CFSG.LocalAnalysis.QuasithinUnique.K1.ExceptionalCatCommon
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogG2EvenAutomorphisms
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogG2EvenInvolutions
public import CFSG.LieType.Chevalley.SimpleRootComplement
public import CFSG.LieType.Chevalley.IntrinsicSimplePairs
public import CFSG.LieType.Chevalley.AdjointCenter
public import CFSG.Blueprint.Catalog
public import Certificates.Certificate45
public import Certificates.Certificate46
public import Certificates.Certificate47
public import Certificates.Certificate48
public import Certificates.Certificate49
public import Certificates.Certificate50
public import Certificates.Certificate51
public import Certificates.Certificate52
public import Certificates.Certificate53
public import Certificates.Certificate54
public import Certificates.Certificate55
public import Certificates.Certificate56
public import Certificates.Certificate57
public import Certificates.Certificate58
public import Certificates.Certificate59
public import Certificates.Certificate60
public import Certificates.Certificate61
public import Certificates.Certificate62
public import Certificates.Certificate63
public import Certificates.Certificate64
public import Certificates.Certificate65
public import Certificates.Certificate66
public import Certificates.Certificate67
public import Certificates.Certificate68
public import Certificates.Certificate69
public import Certificates.Certificate70
public import Certificates.Certificate71
public import Certificates.Certificate72
public import Certificates.Certificate73
public import Certificates.Certificate74
public import Certificates.Certificate75
public import Certificates.Certificate113
public import Certificates.Certificate114
public import Certificates.Certificate117
public import Certificates.Certificate3951
public import CFSG.Foundations
public import CFSG.GroupTheory.Fitting.CharacteristicP
public import CFSG.LocalAnalysis.ComponentClassification.DisjointSolvableKernels
public import CFSG.LocalAnalysis.ComponentClassification.LayerMultiplication
public import CFSG.LocalAnalysis.ComponentClassification.MinimalBCenter
public import CFSG.LocalAnalysis.ComponentClassification.OrdinaryComponentJoins
public import CFSG.LocalAnalysis.ComponentClassification.TwoLayer
public import CFSG.LocalAnalysis.ComponentClassification.UniversalOrbitBlock

public section

namespace CFSG.QuasithinUnique.K1

open CFSG.Open CFSG.QuasithinUnique CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.LocalAnalysis.ComponentInitial CFSG.ComponentClassification.UnbalancedCatalog
open scoped commutatorElement

section Rigid

variable {τ : Tag} {K : Type} [Field K]

theorem simpleRootSubgroup_le_posUnipotent
    (i : Fin τ.rank) :
    rootSubgroup τ K (Pi.single i 1) ≤ posUnipotent τ K :=
  le_iSup₂_of_le (Pi.single i 1) ⟨isRoot_single τ i, by rw [height_single]; exact one_pos⟩ le_rfl

theorem eq_one_of_exactNormalAut_inner
    {δ : MulAut (adjointGroup τ K)} {a : Fin τ.rank → Kˣ}
    {σ : K ≃+* K} (hδ : δ = exactNormalAut τ K a σ 0) {w : adjointGroup τ K}
    (hwU : w ∈ (posUnipotent τ K).subgroupOf (adjointGroup τ K))
    (hw : ∀ x ∈ (posUnipotent τ K).subgroupOf (adjointGroup τ K), δ x = w * x * w⁻¹) :
    δ = 1 := by
  have hX : ∀ i c, (a i : K) * σ c = c := by
    intro i c
    obtain ⟨hle, hnorm, hprod, -, -, -, hu2⟩ := simple_positive_root_complement τ K i
    have hxmem : ∀ d : K, xUnit τ K i d ∈ rootSubgroup τ K (Pi.single i 1) := fun d => by
      rw [← SetLike.mem_coe, coe_rootSubgroup_single]
      exact ⟨d, rfl⟩
    have hxU : adjX τ K i c ∈ (posUnipotent τ K).subgroupOf (adjointGroup τ K) :=
      simpleRootSubgroup_le_posUnipotent i (hxmem c)
    have h1 : δ (adjX τ K i c) = adjX τ K i ((a i : K) * σ c) := by
      rw [hδ, exactNormalAut_zero_adjX]
    have h2 := hw _ hxU
    have h3 : (w : ModGL τ K) * xUnit τ K i c * (w : ModGL τ K)⁻¹ =
        xUnit τ K i ((a i : K) * σ c) := by
      have := congrArg (fun g : adjointGroup τ K => (g : ModGL τ K)) (h2.symm.trans h1)
      exact this
    refine eq_of_conj_eq_of_complement (xUnit τ K i) hle hnorm
      (fun d => simpleRootSubgroup_le_posUnipotent i (hxmem d))
      (fun d d' => by rw [← xUnit_add, ← xUnit_add, add_comm]) ?_ ?_
      (Subgroup.mem_subgroupOf.mp hwU) h3
    · rw [← coe_rootSubgroup_single]
      exact hprod
    · intro n hn n' hn' d d' h
      obtain ⟨h1, h2⟩ := hu2 (xUnit τ K i d) (hxmem d) (xUnit τ K i d') (hxmem d') n hn n' hn' h
      exact ⟨h2, pinnedX_injective τ K (Pi.single i 1)
        (by rw [pinnedX_single, pinnedX_single]; exact h1)⟩
  have ha1 : ∀ i, (a i : K) = 1 := fun i => by
    simpa using hX i 1
  have hσ : ∀ c, σ c = c := fun c => by
    have := hX ⟨0, τ.rank_pos⟩ c
    rwa [ha1, one_mul] at this
  refine mulAut_ext_adjX_adjY (fun i c => ?_) (fun i c => ?_)
  · rw [hδ, exactNormalAut_zero_adjX, MulAut.one_apply, ha1 i, one_mul, hσ]
  · rw [hδ, exactNormalAut_zero_adjY, MulAut.one_apply, hσ c, Units.val_inv_eq_inv_val, ha1 i,
      inv_one, one_mul]

end Rigid

section StrongClosure

variable {K : Type} [Field K] [Finite K] [CharP K 2]

local notation "X" => pinnedX Tag.G2 K

theorem g2N_center
    (hK : 4 ≤ Nat.card K) {A B C D E F : K}
    (hr : ∀ s : K, X g2r s * g2N A B C D E F * X g2r s = g2N A B C D E F)
    (ha : ∀ s : K, X g2a s * g2N A B C D E F * X g2a s = g2N A B C D E F) :
    A = 0 ∧ B = 0 ∧ C = 0 ∧ D = 0 ∧ E = 0 := by
  obtain ⟨ω, hω0, hω1⟩ := exists_ne_zero_one hK
  have hA : A = 0 := by
    have h := (g2N_injective ((conj_a 1 A B C D E F).symm.trans (ha 1))).2.2.1
    simpa using h
  have hB : B = 0 := by
    have h := (g2N_injective ((conj_r 1 A B C D E F).symm.trans (hr 1))).2.2.1
    simpa using h
  subst hA
  subst hB
  have hCD : ∀ s : K, C * s ^ 2 + D * s = 0 := by
    intro s
    have h := (g2N_injective ((conj_r s 0 0 C D E F).symm.trans (hr s))).2.2.2.2.1
    linear_combination h
  have hC : C = 0 := by
    have h1 := hCD 1
    have h2 := hCD ω
    have h3 : C * (ω * (ω - 1)) = 0 := by linear_combination h2 - ω * h1
    rcases mul_eq_zero.1 h3 with h | h
    · exact h
    · rcases mul_eq_zero.1 h with h | h
      · exact absurd h hω0
      · exact absurd (sub_eq_zero.1 h) hω1
  have hD : D = 0 := by
    have h1 := hCD 1
    rw [hC] at h1
    simpa using h1
  subst hC
  subst hD
  have hE : E = 0 := by
    have h := (g2N_injective ((conj_a 1 0 0 0 0 E F).symm.trans (ha 1))).2.2.2.2.2
    simpa using h
  exact ⟨rfl, rfl, rfl, rfl, hE⟩

theorem noStronglyClosedElemAbelian_g2
    (hK : 4 ≤ Nat.card K) :
    NoStronglyClosedElemAbelian (adjointGroup .G2 K) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have := finite_modGL (τ := .G2) (K := K)
  obtain ⟨w₀, hw₀⟩ := Finite.exists_max (coxeterSystem .G2).length
  obtain ⟨⟨P, hP⟩, -⟩ := exceptional_ordinary_Sylow_opposition .G2 K 2 w₀ hw₀
  have hQ : IsSylowTwoOf ((posUnipotent .G2 K).subgroupOf (adjointGroup .G2 K)) ⊤ := by
    rw [← hP]
    exact isSylowTwoOf_top_iff.mpr ⟨P.isPGroup', P.not_dvd_index⟩
  refine noStronglyClosedElemAbelian_of_witnesses _ hQ ?_
  intro z hz hz1 hzc
  have hzU : (z : ModGL .G2 K) ∈ posUnipotent .G2 K := hz
  obtain ⟨A, B, C, D, E, F, hzN⟩ := exists_g2N_of_mem_posUnipotent hzU
  have hconj : ∀ (α : Fin Tag.G2.rank → ℤ) (s : K), X α s ∈ posUnipotent .G2 K →
      X α s * (z : ModGL .G2 K) * X α s = (z : ModGL .G2 K) := by
    intro α s hαU
    have hmem : (⟨X α s, pinnedX_mem_adjointGroup α s⟩ : adjointGroup .G2 K) ∈
        (posUnipotent .G2 K).subgroupOf (adjointGroup .G2 K) := hαU
    have h := congrArg Subtype.val (hzc _ hmem)
    simp only [Subgroup.coe_mul] at h
    calc X α s * (z : ModGL .G2 K) * X α s = (z : ModGL .G2 K) * X α s * X α s := by rw [h]
      _ = (z : ModGL .G2 K) := by rw [mul_assoc, pinnedX_mul_self, mul_one]
  have hr : ∀ s : K, X g2r s * g2N A B C D E F * X g2r s = g2N A B C D E F := fun s => by
    have := hconj g2r s (by rw [pinnedX_r_eq_g2N]; exact g2N_mem_posUnipotent _ _ _ _ _ _)
    rwa [← hzN] at this
  have ha : ∀ s : K, X g2a s * g2N A B C D E F * X g2a s = g2N A B C D E F := fun s => by
    have := hconj g2a s (by rw [pinnedX_a_eq_g2N]; exact g2N_mem_posUnipotent _ _ _ _ _ _)
    rwa [← hzN] at this
  obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ := g2N_center hK hr ha
  have hzc' : (z : ModGL .G2 K) = X g2c F := by
    rw [← hzN, pinnedX_c_eq_g2N]
  have hF : F ≠ 0 := by
    rintro rfl
    apply hz1
    apply Subtype.ext
    simp [hzc', pinnedX_zero]
  obtain ⟨g, hgC, hg⟩ := G2Conj.b_c F
  obtain ⟨h, hhC, hh⟩ := (G2Conj.a_b F).trans (G2Conj.b_c F)
  let g' : adjointGroup .G2 K := ⟨g, hgC⟩
  let h' : adjointGroup .G2 K := ⟨h, hhC⟩
  have hgz : ((g'⁻¹ * z * g' : adjointGroup .G2 K) : ModGL .G2 K) = X g2b F := by
    change g⁻¹ * (z : ModGL .G2 K) * g = _
    rw [hzc', ← hg]
    group
  have hhz : ((h'⁻¹ * z * h' : adjointGroup .G2 K) : ModGL .G2 K) = X g2a F := by
    change h⁻¹ * (z : ModGL .G2 K) * h = _
    rw [hzc', ← hh]
    group
  refine ⟨g', h', ?_, ?_, ?_⟩
  · show ((g'⁻¹ * z * g' : adjointGroup .G2 K) : ModGL .G2 K) ∈ posUnipotent .G2 K
    rw [hgz, pinnedX_b_eq_g2N]
    exact g2N_mem_posUnipotent _ _ _ _ _ _
  · show ((h'⁻¹ * z * h' : adjointGroup .G2 K) : ModGL .G2 K) ∈ posUnipotent .G2 K
    rw [hhz, pinnedX_a_eq_g2N]
    exact g2N_mem_posUnipotent _ _ _ _ _ _
  · intro hcomm
    have h1 : X g2b F * X g2a F = X g2a F * X g2b F := by
      have := congrArg Subtype.val hcomm
      rw [← hgz, ← hhz]
      exact this
    have h2 : ⁅X g2a F, X g2b F⁆ = 1 := commutatorElement_eq_one_iff_mul_comm.mpr h1.symm
    rw [comm_a_b] at h2
    have h3 : F * F = 0 :=
      pinnedX_injective Tag.G2 K g2c (h2.trans (pinnedX_zero Tag.G2 K g2c).symm)
    exact hF (mul_self_eq_zero.mp h3)

end StrongClosure

section Aut

variable {K : Type} [Field K] [Finite K] [CharP K 2]

theorem sylowCentralizingAutInner_g2
    (hK : 4 ≤ Nat.card K) :
    SylowCentralizingAutInner (adjointGroup .G2 K) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have := finite_modGL (τ := .G2) (K := K)
  obtain ⟨w₀, hw₀⟩ := Finite.exists_max (coxeterSystem .G2).length
  obtain ⟨⟨PU, hPU⟩, ⟨PV, hPV⟩, hUV, hopp, -, -⟩ :=
    exceptional_ordinary_Sylow_opposition .G2 K 2 w₀ hw₀
  have hU : IsSylowTwoOf ((posUnipotent .G2 K).subgroupOf (adjointGroup .G2 K)) ⊤ := by
    rw [← hPU]
    exact isSylowTwoOf_top_iff.mpr ⟨PU.isPGroup', PU.not_dvd_index⟩
  have hV : IsSylowTwoOf ((negUnipotent .G2 K).subgroupOf (adjointGroup .G2 K)) ⊤ := by
    rw [← hPV]
    exact isSylowTwoOf_top_iff.mpr ⟨PV.isPGroup', PV.not_dvd_index⟩
  have hUV' : (posUnipotent .G2 K).subgroupOf (adjointGroup .G2 K) ⊓
      (negUnipotent .G2 K).subgroupOf (adjointGroup .G2 K) = ⊥ := by
    refine eq_bot_iff.2 fun x hx => ?_
    have h : (x : ModGL .G2 K) ∈ posUnipotent .G2 K ⊓ negUnipotent .G2 K :=
      Subgroup.mem_inf.2 ⟨(Subgroup.mem_inf.1 hx).1, (Subgroup.mem_inf.1 hx).2⟩
    rw [hUV, Subgroup.mem_bot] at h
    exact Subgroup.mem_bot.2 (Subtype.ext h)
  refine sylowCentralizingAutInner_of_opposite hU hV hUV' ?_ ?_
  · intro S hS hUS
    obtain ⟨hp, hi⟩ := isSylowTwoOf_top_iff.mp hS
    have hcoe : ((hp.toSylow hi : Sylow 2 (adjointGroup .G2 K)) : Subgroup (adjointGroup .G2 K)) =
        S := IsPGroup.toSylow_coe hp hi
    obtain ⟨u, hu, hSu⟩ := (hopp (hp.toSylow hi)).1 (by rw [hcoe]; exact hUS)
    exact ⟨u, hu, hcoe ▸ hSu⟩
  · rintro δ hUδ hVδ ⟨w, hwU, hw⟩
    have hδA : δ ∈ unipotentPairAut .G2 K := ⟨hUδ, hVδ⟩
    obtain ⟨a, σ, hδ⟩ := exists_exactNormalAut_zero_eq_of_even_G2 hK hδA
    exact eq_one_of_exactNormalAut_inner hδ hwU hw

end Aut

theorem centralizes_of_g2
    {G : Type} [Group G] [Finite G] {H S U L : Subgroup G}
    (h : StrongClosureComponent H S U L) {f : ℕ} (hf : 2 ≤ f)
    (hmodel : CFSG.Blueprint.ChevalleyExceptionalModel (L ⧸ Subgroup.center L) .G2 2 f) {w : G}
    (hwU : w ∈ U) (hwS : w ∈ Subgroup.centralizer (S : Set G)) :
    L ≤ Subgroup.centralizer ({w} : Set G) := by
  obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := hmodel
  have : CharP K 2 := finite_field_prime_power_characteristic Nat.prime_two (by omega) hK
  have hK4 : 4 ≤ Nat.card K := by
    rw [hK]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
  let e' : L ⧸ Subgroup.center L ≃* adjointGroup .G2 K :=
    e.trans ((QuotientGroup.quotientMulEquivOfEq center_adjointGroup_eq_bot).trans
      QuotientGroup.quotientBot)
  exact centralizes_of_mulEquiv h e' (noStronglyClosedElemAbelian_g2 hK4)
    (sylowCentralizingAutInner_g2 hK4) hwU hwS

end CFSG.QuasithinUnique.K1
