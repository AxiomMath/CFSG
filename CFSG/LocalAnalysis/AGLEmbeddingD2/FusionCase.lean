module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.LieChar
import CFSG.LocalAnalysis.AGLEmbedding.SporadicBeta
import CFSG.LocalAnalysis.AGLEmbedding.TheoremZAux
import CFSG.RankThree.PartOne.KP.SporadicDefs
public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.Assembly.LowTwoRankDefs
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.RankThree.PartOne.CTP.FusionSound

public section

namespace CFSG.AGLEmbeddingD2

open CFSG.Open CFSG.ComponentClassification.OuterAutomorphisms
open CFSG.RankThree.PartOne.CTP.Fus (FusionGenerationOf)

section Fusion

variable {X : Type*} [Group X] [Finite X] {p : ℕ} {R : Sylow p X} {A X₀ K : Subgroup X}

theorem mem_normalizer_zpowers_of_commute {Y : Type*} [Group Y] {x y : Y} (h : Commute x y) :
    x ∈ Subgroup.normalizer ((Subgroup.zpowers y : Subgroup Y) : Set Y) := by
  rw [Subgroup.mem_normalizer_iff]
  intro z
  have hk : ∀ k : ℤ, x * y ^ k * x⁻¹ = y ^ k := fun k => by
    rw [(h.zpow_right k).eq, mul_inv_cancel_right]
  constructor
  · intro hz
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz
    rw [hk k]
    exact Subgroup.zpow_mem_zpowers y k
  · intro hz
    obtain ⟨k, hk'⟩ := Subgroup.mem_zpowers_iff.mp hz
    have : z = y ^ k := by
      calc z = x⁻¹ * (x * z * x⁻¹) * x := by group
        _ = x⁻¹ * y ^ k * x := by rw [← hk']
        _ = y ^ k := by rw [mul_assoc, ← (h.zpow_right k).eq, inv_mul_cancel_left]
    rw [this]
    exact Subgroup.zpow_mem_zpowers y k

theorem D2AlmostSimple.mem_of_fusion (hK : D2AlmostSimple p X R A X₀ K)
    (hRA : (R : Subgroup X) = A) {g e : X} (he : e ∈ A) (he1 : e ≠ 1)
    (hge : g * e * g⁻¹ ∈ A) : g ∈ X₀ := by
  have : Fact p.Prime := ⟨hK.prime⟩
  have hcomm : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (hK.elem.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  have he₁1 : g * e * g⁻¹ ≠ 1 := by
    rw [Ne, conj_eq_one_iff]
    exact he1
  have hY : Subgroup.zpowers (g * e * g⁻¹) ≤ A := (Subgroup.zpowers_le).mpr hge
  have hYne : Subgroup.zpowers (g * e * g⁻¹) ≠ ⊥ := by rwa [Ne, Subgroup.zpowers_eq_bot]
  have hNY := hK.normalizer_le_of_le_A _ hY hYne
  have hAX : A ≤ X₀ := hRA ▸ hK.sylow_le
  have hAp : IsPGroup p A := hRA ▸ R.isPGroup'
  have hA' : A.map (MulAut.conj g).toMonoidHom ≤ X₀ := by
    rintro _ ⟨a, ha, rfl⟩
    refine hNY (mem_normalizer_zpowers_of_commute ?_)
    have h1 := hcomm a ha e he
    change g * a * g⁻¹ * (g * e * g⁻¹) = g * e * g⁻¹ * (g * a * g⁻¹)
    calc g * a * g⁻¹ * (g * e * g⁻¹) = g * (a * e) * g⁻¹ := by group
      _ = g * (e * a) * g⁻¹ := by rw [h1]
      _ = g * e * g⁻¹ * (g * a * g⁻¹) := by group
  have hidx : ¬ p ∣ (A.subgroupOf X₀).index := by
    intro hd
    have := R.not_dvd_index
    rw [hRA] at this
    exact this (hd.trans (Subgroup.relIndex_dvd_index_of_le hAX))
  obtain ⟨l, hl, hmap⟩ := CFSG.AGLEmbedding.exists_mem_map_conj_eq_of_card_eq hAX hA' hAp
    (hAp.map _) hidx (Subgroup.card_map_of_injective (MulAut.conj g).injective)
  have hnorm : l⁻¹ * g ∈ Subgroup.normalizer (A : Set X) := by
    refine Subgroup.mem_normalizer_iff_map_conj_eq.mpr ?_
    have e1 : (MulAut.conj (l⁻¹ * g)).toMonoidHom =
        (MulAut.conj l⁻¹).toMonoidHom.comp (MulAut.conj g).toMonoidHom :=
      MonoidHom.ext fun x => by simp [MulAut.conj_apply, mul_assoc]
    have e2 : (MulAut.conj l⁻¹).toMonoidHom.comp (MulAut.conj l).toMonoidHom =
        MonoidHom.id X := MonoidHom.ext fun x => by simp [MulAut.conj_apply, mul_assoc]
    change A.map (MulAut.conj (l⁻¹ * g)).toMonoidHom = A
    rw [e1, ← Subgroup.map_map, ← hmap, Subgroup.map_map, e2, Subgroup.map_id]
  have hAne : A ≠ ⊥ := by
    intro hA
    have hc := hK.card_A
    rw [hA, Subgroup.card_bot] at hc
    have := Nat.one_lt_pow two_ne_zero hK.prime.one_lt
    omega
  have hNA := hK.normalizer_le_of_le_A A le_rfl hAne
  have hg : g = l * (l⁻¹ * g) := by group
  rw [hg]
  exact X₀.mul_mem hl (hNA hnorm)

theorem D2AlmostSimple.false_of_fusion (hK : D2AlmostSimple p X R A X₀ K)
    (hRA : (R : Subgroup X) = A) (hgen : FusionGenerationOf K p) : False := by
  have : Fact p.Prime := ⟨hK.prime⟩
  have hKn : K.Normal := hK.normal
  obtain ⟨E, Γ, hEp, -, hΓ, hfus⟩ := hgen
  obtain ⟨S, hES⟩ := (hEp.map K.subtype).exists_le_sylow
  obtain ⟨l, -, hl⟩ := CFSG.AGLEmbedding.exists_mem_map_conj_eq_of_card_eq
    (L := ⊤) (le_top : (R : Subgroup X) ≤ ⊤) le_top R.isPGroup' S.isPGroup'
    (by
      change ¬ p ∣ (R : Subgroup X).relIndex ⊤
      rw [Subgroup.relIndex_top_right]
      exact R.not_dvd_index)
    (by rw [Sylow.card_eq_multiplicity S, Sylow.card_eq_multiplicity R])
  have hconjA : ∀ e ∈ E, l⁻¹ * (e : X) * l ∈ A := fun e he => by
    have hS : (e : X) ∈ (S : Subgroup X) := hES ⟨e, he, rfl⟩
    rw [← hl] at hS
    obtain ⟨r, hr, hre⟩ := hS
    rw [← hRA, ← hre]
    have hrr : l⁻¹ * (MulAut.conj l).toMonoidHom r * l = r := by
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      group
    rw [hrr]
    exact hr
  have hΓX : ∀ γ ∈ Γ, l⁻¹ * (γ : X) * l ∈ X₀ := fun γ hγ => by
    obtain ⟨e, he, he1, hγe⟩ := hfus γ hγ
    refine hK.mem_of_fusion hRA (hconjA e he) ?_ ?_
    · intro h1
      apply he1
      have h2 : (e : X) = l * (l⁻¹ * (e : X) * l) * l⁻¹ := by group
      rw [h1] at h2
      exact Subtype.ext (by simpa using h2)
    · have h := hconjA _ hγe
      have heq : l⁻¹ * (γ : X) * l * (l⁻¹ * (e : X) * l) * (l⁻¹ * (γ : X) * l)⁻¹ =
          l⁻¹ * ((γ * e * γ⁻¹ : K) : X) * l := by
        simp only [Subgroup.coe_mul, Subgroup.coe_inv]
        group
      rw [heq]
      exact h
  have hcl : Subgroup.closure Γ ≤ (X₀.comap (MulAut.conj l⁻¹).toMonoidHom).subgroupOf K := by
    refine (Subgroup.closure_le _).mpr fun γ hγ => ?_
    simp only [SetLike.mem_coe, Subgroup.mem_subgroupOf, Subgroup.mem_comap,
      MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
    exact hΓX γ hγ
  apply hK.not_le
  intro k hk
  have hk2 : l * k * l⁻¹ ∈ K := hKn.conj_mem k hk l
  have hmem : (⟨l * k * l⁻¹, hk2⟩ : K) ∈ Subgroup.closure Γ := hΓ ▸ Subgroup.mem_top _
  have := hcl hmem
  simp only [Subgroup.mem_subgroupOf, Subgroup.mem_comap, MulEquiv.coe_toMonoidHom,
    MulAut.conj_apply, inv_inv] at this
  simpa [mul_assoc] using this

theorem D2AlmostSimple.sylow_eq_A_of_card (hK : D2AlmostSimple p X R A X₀ K)
    (hout : ¬ p ∣ Nat.card (Outer K)) (h3 : ¬ p ^ 3 ∣ Nat.card K) : (R : Subgroup X) = A := by
  have : Fact p.Prime := ⟨hK.prime⟩
  have hRK := hK.sylow_le_of_not_dvd_card_outer hout
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp R.isPGroup'
  have hdvd : Nat.card R ∣ Nat.card K := Subgroup.card_dvd_of_le hRK
  have hn2 : n ≤ 2 := by
    by_contra hlt
    exact h3 ((pow_dvd_pow p (by omega)).trans (hn ▸ hdvd))
  refine (Subgroup.eq_of_le_of_card_ge hK.A_le ?_).symm
  rw [hn, hK.card_A]
  exact Nat.pow_le_pow_right hK.prime.pos hn2

theorem D2AlmostSimple.false_of_fusion_of_card (hK : D2AlmostSimple p X R A X₀ K)
    (hout : ¬ p ∣ Nat.card (Outer K)) (h3 : ¬ p ^ 3 ∣ Nat.card K)
    (hgen : FusionGenerationOf K p) : False :=
  hK.false_of_fusion (hK.sylow_eq_A_of_card hout h3) hgen

theorem D2AlmostSimple.false_of_core (hK : D2AlmostSimple p X R A X₀ K)
    (hout : ¬ p ∣ Nat.card (Outer K))
    (hcore : ∀ S : Sylow p K, GLBCore p 2 (S : Subgroup K) = ⊤) : False := by
  have : Fact p.Prime := ⟨hK.prime⟩
  have hRK := hK.sylow_le_of_not_dvd_card_outer hout
  have h := hcore (R.subtype hRK)
  have hle : GLBCore p 2 ((R.subtype hRK : Sylow p K) : Subgroup K) ≤ X₀.subgroupOf K := by
    refine (CFSG.PreuniquenessRankFour.Helpers.fullCore_le_iff p 2 _ _).mpr fun Q hQ hrank => ?_
    have hQX : Q.map K.subtype ≤ (R : Subgroup X) := by
      rintro _ ⟨q, hq, rfl⟩
      have := hQ hq
      rw [Sylow.coe_subtype, Subgroup.mem_subgroupOf] at this
      exact this
    have hQp : IsPGroup p (Q.map K.subtype) := R.isPGroup'.to_le hQX
    have hrank' : 2 ≤ Open.pRank p (Q.map K.subtype) := by
      rwa [CFSG.PreuniquenessRankFour.Helpers.pRank_map_of_injective p hK.prime K.subtype
        K.subtype_injective Q]
    have hN := hK.normalizer_le_of_rank _ (hQX.trans hK.sylow_le) hQp hrank'
    intro n hn
    rw [Subgroup.mem_subgroupOf]
    refine hN (Subgroup.mem_normalizer_iff.mpr fun x => ?_)
    constructor
    · rintro ⟨q, hq, rfl⟩
      exact ⟨n * q * n⁻¹, (Subgroup.mem_normalizer_iff.mp hn q).mp hq, by simp⟩
    · rintro ⟨q, hq, hqx⟩
      have hq' : (q : X) = (n : X) * x * (n : X)⁻¹ := hqx
      have hx : x = (n : X)⁻¹ * (q : X) * (n : X) := by
        rw [hq']
        group
      have hxK : x ∈ K := by
        rw [hx]
        exact K.mul_mem (K.mul_mem (K.inv_mem n.2) q.2) n.2
      refine ⟨⟨x, hxK⟩, (Subgroup.mem_normalizer_iff.mp hn ⟨x, hxK⟩).mpr ?_, rfl⟩
      have : n * ⟨x, hxK⟩ * n⁻¹ = q := Subtype.ext (by simp [hq'])
      rw [this]
      exact hq
  apply hK.not_le
  intro k hk
  have := hle (h ▸ Subgroup.mem_top (⟨k, hk⟩ : K))
  rwa [Subgroup.mem_subgroupOf] at this

end Fusion

theorem d2IndexCaseAt_of_fusion {i : TauCeti.CFSGIndex} {Pp : ℕ → Prop}
    (h : ∀ p, Pp p → ¬ p ∣ Nat.card (Outer i.Group) ∧ ¬ p ^ 3 ∣ Nat.card i.Group ∧
      FusionGenerationOf i.Group p) : D2IndexCaseAt i Pp := by
  intro G _ _ _ _ p hpc P M A H R _ _ _ Rbar K _ hK ⟨e⟩
  obtain ⟨hout, h3, hgen⟩ := h p hpc
  refine hK.false_of_fusion_of_card ?_ ?_
    (CFSG.AGLEmbedding.fusionGenerationOf_of_mulEquiv e.symm hgen)
  · rwa [CFSG.RankThree.PartOne.card_outer_eq_of_mulEquiv e]
  · rwa [Nat.card_congr e.toEquiv]

theorem glbCore_two_eq_top_of_sylow {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    (S : Sylow p G) (h : GLBCore p 2 (S : Subgroup G) = ⊤) (S' : Sylow p G) :
    GLBCore p 2 (S' : Subgroup G) = ⊤ := by
  obtain ⟨l, -, hl⟩ := CFSG.AGLEmbedding.exists_mem_map_conj_eq_of_card_eq
    (L := ⊤) (le_top : (S : Subgroup G) ≤ ⊤) le_top S.isPGroup' S'.isPGroup'
    (by
      change ¬ p ∣ (S : Subgroup G).relIndex ⊤
      rw [Subgroup.relIndex_top_right]
      exact S.not_dvd_index)
    (by rw [Sylow.card_eq_multiplicity S', Sylow.card_eq_multiplicity S])
  have hle : GLBCore p 2 (S : Subgroup G) ≤
      (GLBCore p 2 (S' : Subgroup G)).comap (MulAut.conj l).toMonoidHom := by
    refine (CFSG.PreuniquenessRankFour.Helpers.fullCore_le_iff p 2 _ _).mpr fun Q hQ hrank => ?_
    intro n hn
    rw [Subgroup.mem_comap]
    refine CFSG.AGLEmbeddingD2.normalizer_le_glbCore p 2 (Q := Q.map (MulAut.conj l).toMonoidHom)
      (by rw [← hl]; exact Subgroup.map_mono hQ) ?_ ?_
    · rwa [CFSG.PreuniquenessRankFour.Helpers.pRank_map_of_injective p Fact.out _
        (MulAut.conj l).injective Q]
    · exact Subgroup.le_normalizer_map (MulAut.conj l).toMonoidHom ⟨n, hn, rfl⟩
  rw [eq_top_iff]
  intro x _
  have hx := hle (h ▸ Subgroup.mem_top (l⁻¹ * x * l))
  rw [Subgroup.mem_comap] at hx
  simpa [MulAut.conj_apply, mul_assoc] using hx

@[expose] def D2IndexDatum (K : Type*) [Group K] [Finite K] (p : ℕ) : Prop :=
  ¬ p ∣ Nat.card (Outer K) ∧
    (¬ p ^ 2 ∣ Nat.card K ∨ 3 ≤ Open.pRank p (⊤ : Subgroup K) ∨
      (¬ p ^ 3 ∣ Nat.card K ∧ FusionGenerationOf K p) ∨
      ∀ S : Sylow p K, GLBCore p 2 (S : Subgroup K) = ⊤)

theorem D2AlmostSimple.sq_dvd_card {X : Type*} [Group X] [Finite X] {p : ℕ} {R : Sylow p X}
    {A X₀ K : Subgroup X} (hK : D2AlmostSimple p X R A X₀ K)
    (hout : ¬ p ∣ Nat.card (Outer K)) : p ^ 2 ∣ Nat.card K := by
  have hRK := hK.sylow_le_of_not_dvd_card_outer hout
  rw [← hK.card_A]
  exact Subgroup.card_dvd_of_le (hK.A_le.trans hRK)

theorem d2IndexCaseAt_of_datum {i : TauCeti.CFSGIndex} {Pp : ℕ → Prop}
    (h : ∀ (L : Type) [Group L] [Finite L], Nonempty (L ≃* i.Group) → ∀ p, Pp p →
      D2IndexDatum L p) : D2IndexCaseAt i Pp := by
  intro G _ _ _ _ p hpc P M A H R _ _ _ Rbar K _ hK he
  have : Fact p.Prime := ⟨hK.prime⟩
  obtain ⟨hout, hd⟩ := h K he p hpc
  rcases hd with h2 | h3 | ⟨h3, hgen⟩ | hcore
  · exact h2 (hK.sq_dvd_card hout)
  · exact hK.false_of_three_le_pRank h3
  · exact hK.false_of_fusion_of_card hout h3 hgen
  · exact hK.false_of_core hout hcore

end CFSG.AGLEmbeddingD2
