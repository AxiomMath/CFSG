module

public import CFSG.LocalAnalysis.AGLEmbedding.OneLieMData
public import CFSG.LocalAnalysis.AGLEmbedding.OneLieMDataAux
public import CFSG.LocalAnalysis.AGLEmbedding.LinTwoBorelSolvable
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.SmallRankOneKFacts
public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallSPLIbTorus
public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallSPLIbMData
public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallSPLK0ThmZ
public import CFSG.LocalAnalysis.AGLEmbedding.OneLieReduced
public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallPosT

public section
namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.PreuniquenessRankFour.Helpers
open CFSG.RankThreeCoreUniqueness.Helpers

section Borel

variable {Y : Type} [Group Y] [Finite Y] {p : ℕ} [Fact p.Prime] {Rb : Sylow p Y}
  {K : Subgroup Y}

omit [Finite Y] [Fact p.Prime] in
theorem le_centralizer_of_perfect_of_solvable [K.Normal] (T₁ : Sylow p K) {Y₀ : Subgroup Y}
    (hT₁ : (T₁ : Subgroup K).map K.subtype = (Rb : Subgroup Y) ⊓ K)
    (hsolv : ∀ A : Subgroup (MulAut K),
      (∀ α ∈ A, (T₁ : Subgroup K).map (α : K ≃* K).toMonoidHom = T₁) → Group.IsSolvable A)
    (hY₀T : Y₀ ≤ Subgroup.normalizer ((((Rb : Subgroup Y) ⊓ K : Subgroup Y)) : Set Y))
    {W : Subgroup Y} (hWY₀ : W ≤ Y₀) (hperf : ⁅W, W⁆ = W) :
    W ≤ Subgroup.centralizer (K : Set Y) := by
  set f : Y →* MulAut K := MulAut.conjNormal (H := K) with hf
  have hA : ∀ α ∈ W.map f, (T₁ : Subgroup K).map (α : K ≃* K).toMonoidHom = T₁ := by
    rintro _ ⟨w, hw, rfl⟩
    have hwN := hY₀T (hWY₀ hw)
    apply Subgroup.map_injective K.subtype_injective
    rw [hT₁]
    ext y
    constructor
    · rintro ⟨_, ⟨k, hk, rfl⟩, rfl⟩
      have hkT : (k : Y) ∈ (Rb : Subgroup Y) ⊓ K := hT₁ ▸ ⟨k, hk, rfl⟩
      simp only [MulEquiv.coe_toMonoidHom, Subgroup.coe_subtype, hf, MulAut.conjNormal_apply]
      exact (Subgroup.mem_normalizer_iff.mp hwN _).mp hkT
    · intro hy
      have hy' : w⁻¹ * y * w ∈ (Rb : Subgroup Y) ⊓ K := by
        have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hwN) y).mp hy
        simpa [mul_assoc] using this
      rw [← hT₁] at hy'
      obtain ⟨k, hk, hky⟩ := hy'
      refine ⟨_, ⟨k, hk, rfl⟩, ?_⟩
      simp only [MulEquiv.coe_toMonoidHom, Subgroup.coe_subtype, hf, MulAut.conjNormal_apply]
      have hky' : (k : Y) = w⁻¹ * y * w := hky
      rw [hky']; group
  have hsolv' := hsolv (W.map f) hA
  have hperf' : ⁅W.map f, W.map f⁆ = W.map f := by rw [← Subgroup.map_commutator, hperf]
  have hbot := eq_bot_of_commutator_eq_self_of_le le_rfl hsolv' hperf'
  rw [Subgroup.map_eq_bot_iff, hf, ker_conjNormal_eq_centralizer] at hbot
  exact hbot

end Borel

section Data

variable {G : Type} [Group G] [Finite G] {p : ℕ} {P : Sylow p G} {M H R : Subgroup G}
  {Rbar : Sylow p (H ⧸ primeComplementCore (G := H) p)}
  {K : Subgroup (H ⧸ primeComplementCore (G := H) p)}

theorem solvable_automizer_of_isSmallLinTwo {L : Type} [Group L] [Finite L] [Fact p.Prime]
    (hp2 : p ≠ 2) (hL : IsSmallLinTwo p L) (T : Sylow p L) (A : Subgroup (MulAut L))
    (hA : ∀ α ∈ A, (T : Subgroup L).map (α : L ≃* L).toMonoidHom = T) : Group.IsSolvable A := by
  obtain ⟨d, hdL, ⟨e₁⟩⟩ := hL
  obtain ⟨e₂⟩ := nonempty_mulEquiv_psl2GF_of_isLinTwoIndex hdL
  set f : L ≃* PSL2GF p 2 := e₁.trans e₂
  have hfs : Function.Surjective (f : L →* PSL2GF p 2) := f.surjective
  set U : Sylow p (PSL2GF p 2) := T.mapSurjective hfs with hU
  have hUT : (U : Subgroup (PSL2GF p 2)) = (T : Subgroup L).map (f : L →* PSL2GF p 2) :=
    Sylow.coe_mapSurjective hfs T
  let F : MulAut L →* MulAut (PSL2GF p 2) := (MulAut.congr f).toMonoidHom
  have hF : Function.Injective F := (MulAut.congr f).injective
  have hFA : ∀ β ∈ A.map F,
      (U : Subgroup (PSL2GF p 2)).map (β : PSL2GF p 2 ≃* PSL2GF p 2).toMonoidHom = U := by
    rintro _ ⟨α, hα, rfl⟩
    rw [hUT, Subgroup.map_map]
    conv_rhs => rw [← hA α hα, Subgroup.map_map]
    congr 1
    ext x
    simp [F]
  have := kFactL2SylowNormalizerSolvable p 2 hp2 (by norm_num) U (A.map F) hFA
  exact Group.isSolvable_of_isSolvable_injective
    (f := (A.equivMapOfInjective F hF).toMonoidHom) (A.equivMapOfInjective F hF).injective

theorem D1OneSmallData.isCyclic_of_le_d1PlusCore [Fact p.Prime]
    (hd : D1OneSmallData p P M H R Rbar K) {A : Subgroup G} (hAN : A ≤ d1PlusCore p H K)
    (hA : IsPGroup p A) : IsCyclic A :=
  hd.toCore.isCyclic_of_le_d1PlusCore hAN hA

theorem D1OneSmallData.smallMDataP_linTwo [Fact p.Prime] (hK7 : KFactOneLieSmallLie)
    (hK8 : KFactSmallBorelSolvable) (hd : D1OneSmallData p P M H R Rbar K) (hp7 : 7 ≤ p)
    (hL : IsSmallLinTwo p K) :
    ∃ t : G, D1SmallMDataP p P M H R (d1PlusCore p H K) (d1LiftX p H R K) ((p + 1) / 2) t := by
  have hp : p.Prime := Fact.out
  have hp2 : p ≠ 2 := hd.cfg.red.ne_two
  have hp5 : 5 ≤ p := by omega
  obtain ⟨T₁, hT₁, -, -, h3⟩ := hd.exists_oneLieFacts hK7 hK8 hp5 (Or.inl hL)
  obtain ⟨φ, -⟩ := hd.exists_torus_linTwo h3 hL
  obtain ⟨t, htK, htX, hirr⟩ := hd.exists_irr_linTwo_period h3 hL
  obtain ⟨hNle, -, hcore⟩ := hd.d1PlusCore_facts
  set π := QuotientGroup.mk' (primeComplementCore (G := H) p) with hπ
  set X := d1LiftX p H R K with hXdef
  have hXH : X ≤ H := d1LiftX_le_H p H R K
  have hXel : IsElemAbelian p X := by
    refine ⟨⟨⟨fun a b => ?_⟩⟩, fun x hx => ?_⟩
    · obtain ⟨a', rfl⟩ := φ.surjective a
      obtain ⟨b', rfl⟩ := φ.surjective b
      rw [← map_mul, ← map_mul, mul_comm]
    · obtain ⟨a, ha⟩ := φ.surjective ⟨x, hx⟩
      have hap : a ^ p = 1 := by
        apply Multiplicative.toAdd.injective
        rw [toAdd_pow, toAdd_one, nsmul_eq_mul, CharP.cast_eq_zero, zero_mul]
      have : (⟨x, hx⟩ : X) ^ p = 1 := by rw [← ha, ← map_pow, hap, map_one]
      simpa using congrArg Subtype.val this
  have hXcard : Nat.card X = p ^ 2 := by
    rw [← Nat.card_congr φ.toEquiv, Nat.card_congr Multiplicative.toAdd,
      GaloisField.card p 2 (by norm_num)]
  have hKn : K.Normal := hd.cfg.red.normal_of_rankOne hd.comp hd.noncyclic
  obtain ⟨T, hT, hsimple, hnonab, hcat, hTnc, hΓ, -⟩ := hd.exists_sylow
  have hcoat : IsCoatom (Subgroup.normalizer ((T : Subgroup K) : Set K)) :=
    (smallRankOneData_of_small hp hp5 (Or.inl hL) T).maximal
  have hY₀T := hd.cfg.red.le_normalizer_of_borel_coatom hd.comp hd.noncyclic hd.z T hT hcoat
  have hperf : ∀ L : Subgroup G, L ≤ H ⊓ M → ⁅L, L⁆ = L → L ≤ d1PlusCore p H K := by
    intro L hL' hLL
    exact le_d1PlusCore_of_map_le (hL'.trans inf_le_left)
      (le_centralizer_of_perfect_of_solvable T hT
        (solvable_automizer_of_isSmallLinTwo hp2 hL T) hY₀T
        (Subgroup.map_mono (Subgroup.subgroupOf_mono H hL'))
        (commutator_map_eq_self (hL'.trans inf_le_left) hLL))
  have hcomm : ∀ x ∈ X, ∀ c ∈ d1PlusCore p H K, x * c * x⁻¹ * c⁻¹ ∈ GLBPrimeCore p H := by
    intro x hx c hc
    obtain ⟨c', hc'C, rfl⟩ := hc
    have hxH := hXH hx
    have hxK : π ⟨x, hxH⟩ ∈ K := by
      have h1 : π ⟨x, hxH⟩ ∈ (X.subgroupOf H).map π :=
        ⟨⟨x, hxH⟩, Subgroup.mem_subgroupOf.mpr hx, rfl⟩
      rw [hXdef, hd.cfg.map_d1LiftX_eq_inf] at h1
      exact h1.2
    have hcomm' := Subgroup.mem_centralizer_iff.mp hc'C _ hxK
    refine (mem_glbPrimeCore_iff_mk_eq_one (⟨x, hxH⟩ * c' * (⟨x, hxH⟩ : H)⁻¹ * c'⁻¹)).mpr ?_
    rw [map_mul, map_mul, map_mul, map_inv, map_inv, mul_inv_eq_one, mul_inv_eq_iff_eq_mul]
    exact hcomm'
  exact ⟨t, h3, hd.cfg.ind, d1LiftX_le p H R K, hXel, hXcard.ge, by omega, htK, htX, hirr, hNle,
    hcore, fun A hAN hA => hd.isCyclic_of_le_d1PlusCore hAN hA, hperf, hcomm⟩

end Data

end CFSG.AGLEmbedding
