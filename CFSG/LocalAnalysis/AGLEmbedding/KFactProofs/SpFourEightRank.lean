module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.JStarResidualReduce
public import CFSG.LocalAnalysis.ComponentInitial.SymplecticTorusWeylMatrices
import CFSG.LocalAnalysis.AGLEmbedding.TimmesfeldRouteAux
import CFSG.LocalAnalysis.ComponentInitial.BasicFacts
import CFSG.LieType.Classical.SteinbergBLSymplectic
import CFSG.LinearAlgebra.SL2MinimalFaithfulMatrix
import CFSG.LocalAnalysis.QuasithinUnique.SQTK.TypeB2Carrier
import CFSG.GroupTheory.ElemAbelianClosure

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.Assembly.LowTwoRank
open CFSG.LocalAnalysis.ComponentInitial.SymplecticTorusWeyl (lam commute_lam_lam isSupp_lam
  coe_lam pairMat_apply_pair)

theorem card_le_three_of_elemAbelian_sl2 {K : Type} [Field K] [Finite K] [CharP K 2]
    (hK : Nat.card K = 8) {E : Subgroup (Matrix.SpecialLinearGroup (Fin 2) K)}
    (hE : IsElemAbelian 3 E) : Nat.card E ≤ 3 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let π := QuotientGroup.mk' (Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) K))
  have hπ : Function.Injective π := by
    rw [← MonoidHom.ker_eq_bot_iff, QuotientGroup.ker_mk',
      center_specialLinearGroup_fin_two_eq_bot]
  set E' : Subgroup (Matrix.ProjectiveSpecialLinearGroup (Fin 2) K) := E.map π with hE'
  have hcard : Nat.card E' = Nat.card E := Subgroup.card_map_of_injective hπ
  have hE'p : ∀ c ∈ E', c ^ 3 = 1 := by
    rintro _ ⟨c, hc, rfl⟩
    rw [← map_pow, hE.2 c hc, map_one]
  have hpg : IsPGroup 3 ↥E' := fun g => ⟨1, by
    apply Subtype.ext
    simpa using hE'p g g.2⟩
  obtain ⟨R, hR⟩ := hpg.exists_le_sylow
  have hcyc : IsCyclic R :=
    CFSG.GorensteinWalter.psl2_sylow_isCyclic_of_coprime_field_card K (p := 2) (f := 3)
      (by rw [hK]; norm_num) (by rw [hK]; norm_num) 3 (by norm_num)
      (by rw [hK]; norm_num) R
  have hEcyc : IsCyclic ↥E' := by
    have : IsCyclic ↥(E'.subgroupOf
        (R : Subgroup (Matrix.ProjectiveSpecialLinearGroup (Fin 2) K))) :=
      Subgroup.isCyclic _
    exact isCyclic_of_surjective (Subgroup.subgroupOfEquivOfLe hR).toMonoidHom
      (Subgroup.subgroupOfEquivOfLe hR).surjective
  obtain ⟨g, hg⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := ↥E')
  have h1 : orderOf g ∣ 3 := by
    apply orderOf_dvd_of_pow_eq_one
    apply Subtype.ext
    simpa using hE'p g g.2
  rw [hg, hcard] at h1
  exact Nat.le_of_dvd (by norm_num) h1


section Sylow

theorem exists_conj_map_le_sylow {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    (P : Sylow p G) {E : Subgroup G} (hE : IsPGroup p E) :
    ∃ c : G, E.map (MulAut.conj c).toMonoidHom ≤ (P : Subgroup G) := by
  obtain ⟨Q, hEQ⟩ := hE.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G P Q
  refine ⟨g⁻¹, ?_⟩
  rintro _ ⟨x, hx, rfl⟩
  have hxQ : x ∈ ((g • P : Sylow p G) : Subgroup G) := by rw [hg]; exact hEQ hx
  rw [Sylow.coe_subgroup_smul, Subgroup.mem_smul_pointwise_iff_exists] at hxQ
  obtain ⟨s, hs, hsx⟩ := hxQ
  rw [MulAut.smul_def, MulAut.conj_apply] at hsx
  have : (MulAut.conj g⁻¹).toMonoidHom x = s := by
    rw [← hsx]; simp; group
  rw [this]; exact hs

end Sylow

variable {K : Type} [Field K]

theorem lam_eq_one_iff {r : ℕ} (i : Fin r) (g : Matrix.SpecialLinearGroup (Fin 2) K) :
    lam i g = 1 ↔ g = 1 := by
  refine ⟨fun h => ?_, fun h => by rw [h, map_one]⟩
  have h1 : (((lam i g : StatedSp r K) : GL (Fin r ⊕ Fin r) K) :
      Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) = 1 := by
    rw [h]; rfl
  rw [coe_lam] at h1
  obtain ⟨h00, h01, h10, h11⟩ := pairMat_apply_pair
    (Sum.inl_ne_inr : (Sum.inl i : Fin r ⊕ Fin r) ≠ Sum.inr i) (g : Matrix (Fin 2) (Fin 2) K)
  rw [h1] at h00 h01 h10 h11
  apply Subtype.ext
  ext a b
  fin_cases a <;> fin_cases b <;> simp_all


noncomputable def sl2Pair (K : Type) [Field K] :
    Matrix.SpecialLinearGroup (Fin 2) K × Matrix.SpecialLinearGroup (Fin 2) K →* StatedSp 2 K :=
  (lam (0 : Fin 2)).noncommCoprod (lam (1 : Fin 2)) fun g g' =>
    commute_lam_lam (by decide) g g'

theorem sl2Pair_apply (g g' : Matrix.SpecialLinearGroup (Fin 2) K) :
    sl2Pair K (g, g') = lam (0 : Fin 2) g * lam (1 : Fin 2) g' := by
  simp [sl2Pair, MonoidHom.noncommCoprod_apply]

theorem sl2Pair_injective : Function.Injective (sl2Pair K) := by
  rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
  rintro ⟨g, g'⟩ hker
  have h : lam (0 : Fin 2) g * lam (1 : Fin 2) g' = 1 := by
    rw [← sl2Pair_apply]; exact hker
  have hM : (((lam (0 : Fin 2) g : StatedSp 2 K) : GL (Fin 2 ⊕ Fin 2) K) :
      Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *
      (((lam (1 : Fin 2) g' : StatedSp 2 K) : GL (Fin 2 ⊕ Fin 2) K) :
      Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) = 1 := by
    have := congrArg (fun z : StatedSp 2 K => ((z : GL (Fin 2 ⊕ Fin 2) K) :
      Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K)) h
    simpa using this
  have hdisj : Disjoint ({Sum.inl (0 : Fin 2), Sum.inr (0 : Fin 2)} : Set (Fin 2 ⊕ Fin 2))
      {Sum.inl (1 : Fin 2), Sum.inr (1 : Fin 2)} := by
    rw [Set.disjoint_left]
    rintro x (rfl | rfl) <;> simp
  have hg : g = 1 := by
    rw [← lam_eq_one_iff (0 : Fin 2)]
    apply Subtype.ext
    apply Units.ext
    ext x y
    by_cases hx : x ∈ ({Sum.inl (0 : Fin 2), Sum.inr (0 : Fin 2)} : Set (Fin 2 ⊕ Fin 2))
    · have := (isSupp_lam (0 : Fin 2) g).mul_apply_of_mem (isSupp_lam (1 : Fin 2) g') hdisj hx y
      rw [hM] at this
      exact this.symm
    · exact (isSupp_lam (0 : Fin 2) g) x y (Or.inl hx)
  subst hg
  rw [map_one, one_mul] at h
  have hg' : g' = 1 := (lam_eq_one_iff (1 : Fin 2) g').1 h
  subst hg'
  rfl


theorem isElemAbelian_of_forall {G : Type*} [Group G] {p : ℕ} (E : Subgroup G)
    (hc : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a) (hp : ∀ a ∈ E, a ^ p = 1) : IsElemAbelian p E :=
  ⟨⟨⟨fun a b => Subtype.ext (hc a a.2 b b.2)⟩⟩, hp⟩

theorem elemAbelian_comm {G : Type*} [Group G] {p : ℕ} {E : Subgroup G} (hE : IsElemAbelian p E)
    {a b : G} (ha : a ∈ E) (hb : b ∈ E) : a * b = b * a := CFSG.Open.IsElemAbelian.comm hE ha hb

theorem mk_statedSp_injective [CharP K 2] :
    Function.Injective (QuotientGroup.mk'
      ((StatedScalars (Fin 2 ⊕ Fin 2) K).subgroupOf (StatedSp 2 K))) := by
  rw [← MonoidHom.ker_eq_bot_iff, QuotientGroup.ker_mk', eq_bot_iff]
  intro x hx
  obtain ⟨c, hc⟩ := Subgroup.mem_subgroupOf.mp hx
  have hcS : Matrix.GeneralLinearGroup.scalar (Fin 2 ⊕ Fin 2) c ∈ StatedSp 2 K := by
    rw [hc]; exact x.2
  have hc2 : c ^ 2 = 1 := (CFSG.LieType.Classical.scalar_mem_statedSp_iff (by norm_num) c).1 hcS
  have hK2 : (2 : K) = 0 := CharP.cast_eq_zero K 2
  have hc1 : c = 1 := by
    have h1 : ((c : K) - 1) ^ 2 = 0 := by
      have : (c : K) ^ 2 = 1 := by rw [← Units.val_pow_eq_pow_val, hc2, Units.val_one]
      linear_combination this + (1 - (c : K)) * hK2
    exact Units.ext (sub_eq_zero.1 (pow_eq_zero_iff (by norm_num) |>.1 h1))
  rw [Subgroup.mem_bot]
  apply Subtype.ext
  rw [← hc, hc1, map_one]
  rfl

theorem card_le_nine_of_elemAbelian_statedProj_sp {K : Type} [Field K] [Finite K] [CharP K 2]
    (hK : Nat.card K = 8) (hcard : Nat.card (StatedProj (StatedSp 2 K)) = 1056706560)
    {E : Subgroup (StatedProj (StatedSp 2 K))} (hE : IsElemAbelian 3 E) : Nat.card E ≤ 9 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let φ : Matrix.SpecialLinearGroup (Fin 2) K × Matrix.SpecialLinearGroup (Fin 2) K →*
      StatedProj (StatedSp 2 K) := (QuotientGroup.mk' _).comp (sl2Pair K)
  have hφ : Function.Injective φ := mk_statedSp_injective.comp sl2Pair_injective
  have hSL : Nat.card (Matrix.SpecialLinearGroup (Fin 2) K) = 504 := by
    rw [CFSG.SL2MinimalFaithful.card_specialLinearGroup_fin_two, hK]
    norm_num
  have hprod : Nat.card (Matrix.SpecialLinearGroup (Fin 2) K × Matrix.SpecialLinearGroup (Fin 2) K)
      = 504 ^ 2 := by rw [Nat.card_prod, hSL]; ring
  obtain ⟨Ph, hPh⟩ := Sylow.exists_subgroup_card_pow_prime 3 (n := 4) (by rw [hprod]; norm_num)
  set P : Subgroup (StatedProj (StatedSp 2 K)) := Ph.map φ with hP
  have hPcard : Nat.card P = 3 ^ 4 := by rw [hP, Subgroup.card_map_of_injective hφ, hPh]
  obtain ⟨Q, hPQ⟩ := (IsPGroup.of_card hPcard).exists_le_sylow
  have hv : (Nat.card (StatedProj (StatedSp 2 K))).factorization 3 = 4 := by
    have hne : Nat.card (StatedProj (StatedSp 2 K)) ≠ 0 := Nat.card_pos.ne'
    have h4 := (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_three hne).mp
      (by rw [hcard]; decide : 3 ^ 4 ∣ Nat.card (StatedProj (StatedSp 2 K)))
    have h5 : ¬ 5 ≤ (Nat.card (StatedProj (StatedSp 2 K))).factorization 3 := fun h =>
      (by rw [hcard]; decide : ¬ 3 ^ 5 ∣ Nat.card (StatedProj (StatedSp 2 K)))
        ((Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_three hne).mpr h)
    omega
  have hQcard : Nat.card Q = 3 ^ 4 := by rw [Q.card_eq_multiplicity, hv]
  have hPQ' : P = Q := Subgroup.eq_of_le_of_card_ge hPQ (by rw [hQcard, hPcard])
  have hEp : IsPGroup 3 E := fun g => ⟨1, by
    apply Subtype.ext
    simpa using hE.2 g g.2⟩
  obtain ⟨c, hc⟩ := exists_conj_map_le_sylow Q hEp
  set E₂ := E.map (MulAut.conj c).toMonoidHom with hE₂
  have hE₂card : Nat.card E₂ = Nat.card E :=
    Subgroup.card_map_of_injective (MulAut.conj c).injective
  have hE₂P : E₂ ≤ P := hPQ' ▸ hc
  have hE₂comm : ∀ x ∈ E₂, ∀ y ∈ E₂, x * y = y * x := by
    rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    simp only [MulEquiv.coe_toMonoidHom]
    rw [← map_mul, ← map_mul, elemAbelian_comm hE ha hb]
  have hE₂exp : ∀ x ∈ E₂, x ^ 3 = 1 := by
    rintro _ ⟨a, ha, rfl⟩
    rw [MulEquiv.coe_toMonoidHom, ← map_pow, hE.2 a ha, map_one]
  set Ê : Subgroup (Matrix.SpecialLinearGroup (Fin 2) K × Matrix.SpecialLinearGroup (Fin 2) K) :=
    E₂.comap φ with hÊ
  have hÊmap : Ê.map φ = E₂ := by
    rw [hÊ, Subgroup.map_comap_eq, inf_of_le_right]
    exact hE₂P.trans (by
      rw [hP]; exact Subgroup.map_le_range _ _)
  have hÊcard : Nat.card Ê = Nat.card E := by
    rw [← hE₂card, ← hÊmap, Subgroup.card_map_of_injective hφ]
  have hÊcomm : ∀ a ∈ Ê, ∀ b ∈ Ê, a * b = b * a := by
    intro a ha b hb
    apply hφ
    rw [map_mul, map_mul]
    exact hE₂comm _ ha _ hb
  have hÊexp : ∀ a ∈ Ê, a ^ 3 = 1 := by
    intro a ha
    apply hφ
    rw [map_pow, map_one]
    exact hE₂exp _ ha
  have h1 : Nat.card (Ê.map (MonoidHom.fst _ _)) ≤ 3 := by
    refine card_le_three_of_elemAbelian_sl2 hK (isElemAbelian_of_forall _ ?_ ?_)
    · rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
      simp only [MonoidHom.coe_fst]
      rw [← Prod.fst_mul, ← Prod.fst_mul, hÊcomm a ha b hb]
    · rintro _ ⟨a, ha, rfl⟩
      rw [← map_pow, hÊexp a ha, map_one]
  have h2 : Nat.card (Ê.map (MonoidHom.snd _ _)) ≤ 3 := by
    refine card_le_three_of_elemAbelian_sl2 hK (isElemAbelian_of_forall _ ?_ ?_)
    · rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
      simp only [MonoidHom.coe_snd]
      rw [← Prod.snd_mul, ← Prod.snd_mul, hÊcomm a ha b hb]
    · rintro _ ⟨a, ha, rfl⟩
      rw [← map_pow, hÊexp a ha, map_one]
  have hle : Ê ≤ (Ê.map (MonoidHom.fst _ _)).prod (Ê.map (MonoidHom.snd _ _)) := by
    intro a ha
    exact ⟨⟨a, ha, rfl⟩, ⟨a, ha, rfl⟩⟩
  have h3 : Nat.card Ê ≤ Nat.card ((Ê.map (MonoidHom.fst _ _)).prod (Ê.map (MonoidHom.snd _ _))) :=
    Subgroup.card_le_of_le hle
  rw [Nat.card_congr (Subgroup.prodEquiv _ _).toEquiv, Nat.card_prod] at h3
  rw [← hÊcard]
  nlinarith


theorem card_le_nine_of_elemAbelian_spFourEight {L : Type} [Group L] [Finite L]
    {d : TauCeti.ValidLieTypeIndex} (hd : IsSpFourEightIndex d) (e : L ≃* CatGroup d)
    {E : Subgroup L} (hE : IsElemAbelian 3 E) : Nat.card E ≤ 9 := by
  obtain ⟨q, hq2, hq3, hdq⟩ := hd
  obtain ⟨x, hv⟩ := d
  obtain rfl : x = TauCeti.LieTypeIndex.B 2 q := hdq
  obtain ⟨-, K, hF, hFin, hK, ⟨eK⟩⟩ :=
    CFSG.QuasithinUnique.SQTK.statedClassicalModel_typeB2 q hv e
  rw [hq2, hq3] at hK
  have : CharP K 2 := CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic
    Nat.prime_two (by norm_num) hK
  have hK8 : Nat.card K = 8 := by rw [hK]; norm_num
  have hcard : Nat.card (StatedProj (StatedSp 2 K)) = 1056706560 := by
    rw [← Nat.card_congr eK.toEquiv, Nat.card_congr e.toEquiv, card_catGroup_B2 (d := ⟨_, hv⟩) rfl,
      hq2, hq3]
    decide
  have hE' : IsElemAbelian 3 (E.map eK.toMonoidHom) := by
    refine isElemAbelian_of_forall _ ?_ ?_
    · rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
      simp only [MulEquiv.coe_toMonoidHom]
      rw [← map_mul, ← map_mul, elemAbelian_comm hE ha hb]
    · rintro _ ⟨a, ha, rfl⟩
      rw [MulEquiv.coe_toMonoidHom, ← map_pow, hE.2 a ha, map_one]
  have := card_le_nine_of_elemAbelian_statedProj_sp hK8 hcard hE'
  rwa [Subgroup.card_map_of_injective eK.injective] at this

theorem jStarResidualSp48Three : JStarResidualSp48Three := by
  intro L _ _ hs d hd ⟨e⟩
  obtain ⟨q, hq2, hq3, hdq⟩ := hd
  have hcard : Nat.card L = 1056706560 := by
    rw [Nat.card_congr e.toEquiv, card_catGroup_B2 hdq, hq2, hq3]
    decide
  have h4 : 3 ^ 4 ∣ Nat.card L := by rw [hcard]; decide
  have hnc : ∃ a b : L, a * b ≠ b * a :=
    nonabelian_of_simple_of_sq_dvd Nat.prime_three ((pow_dvd_pow 3 (by norm_num : 2 ≤ 4)).trans h4)
  exact not_jStarElimData_three_three_of_rank (center_bot_of_simple_nonab hnc) h4
    fun E hE => card_le_nine_of_elemAbelian_spFourEight ⟨q, hq2, hq3, hdq⟩ e hE

end CFSG.AGLEmbedding
