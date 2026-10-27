module

public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD1426Common
public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD1426LieFacts
public import CFSG.HardMathSupport.Solomon.Coordinator.I19_10FiCover
public import CFSG.HardMathSupport.Solomon.Coordinator.I23_26Comp
public import CFSG.HardMathSupport.Timmesfeld.OrthogonalGeneration.LiftGen
public import CFSG.GroupTheory.PerfectLeSupCenter
public import CFSG.GroupTheory.PLayer.CenterQuotientAction
public import CFSG.GroupTheory.PLayer.UniqueComponent
public import CFSG.GroupTheory.CentralQuotientTwoLift
public import CFSG.HardMathSupport.Curtis.NaturalModuleCensus.AltIb.Shared
public import CFSG.Timmesfeld.Orders.ClassicalLinearThree
public import CFSG.Timmesfeld.Orders.ClassicalUnitaryThree
public import CFSG.GroupTheory.PCore.SubgroupCore
public import CFSG.Models.PGLSimple

public section

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.HardMathSupport.Solomon.Coordinator CFSG.LocalAnalysis.GLTheoremA.KD2027Aux
open scoped commutatorElement

namespace CFSG.LocalAnalysis.GLTheoremA.KD1426Lie

variable {Y : Type} [Group Y] [Finite Y]

theorem four_of_facts (hF : L3AutFourFacts) {K B : Subgroup Y}
    (hq : CFSG.Open.IsQuasisimple ↥K) (hcore : GLAPPrimeCore 3 ↥K = ⊥)
    (hcat : catalogIs (↥K ⧸ Subgroup.center ↥K) (onLie k3Lie))
    (hB : IsElemAbelian 3 B) (hBN : B ≤ Subgroup.normalizer (K : Set Y))
    (hlay : ∀ b ∈ B, b ∉ Subgroup.centralizer (K : Set Y) →
      GLAPLayer 3 (K ⊓ Subgroup.centralizer ({b} : Set Y)) = ⊥) :
    (B ⊓ Subgroup.centralizer (K : Set Y)).relIndex B ≤ 9 ∧
      ((B ⊓ Subgroup.centralizer (K : Set Y)).relIndex B = 9 → ∃ T : Subgroup Y, T ≤ K ∧
        IsElemAbelian 2 T ∧ Nat.card T = 4 ∧ B ≤ Subgroup.normalizer (T : Set Y) ∧
          ⁅B, T⁆ = T) := by
  classical
  set S : Type := ↥K ⧸ Subgroup.center ↥K with hS
  set π : ↥K →* S := QuotientGroup.mk' (Subgroup.center ↥K) with hπ
  let ψ : ↥B →* MulAut S := normalizerToCenterQuotientAut K B hBN
  have hmodel : L3Model S := l3Model_of_catalogIs hcat
  have hAel : IsElemAbelian 3 ψ.range := KD1426Common.isElemAbelian_range hB ψ
  have hAne : ∀ α ∈ ψ.range, α ≠ 1 → GLAPLayer 3 (fixSubgroup α) = ⊥ := by
    rintro α ⟨b, rfl⟩ h1
    have hbC : (b : Y) ∉ Subgroup.centralizer (K : Set Y) := by
      intro hbC
      exact h1 ((normalizerToCenterQuotientAut_eq_one_iff ⟨hq.1⟩ hBN b).2
        (Subgroup.mem_inf.2 ⟨b.2, hbC⟩))
    exact (glaPLayer_inf_centralizer_eq_bot_iff Nat.prime_three hBN b).1
      (hlay b b.2 hbC)
  obtain ⟨h9, hfour⟩ := hF S hmodel ψ.range hAel hAne
  have hcard : Nat.card ψ.range = (B ⊓ Subgroup.centralizer (K : Set Y)).relIndex B :=
    card_range_normalizerToCenterQuotientAut ⟨hq.1⟩ hBN
  refine ⟨?_, ?_⟩
  · rw [← hcard]
    exact h9
  · intro hidx
    have hcard9 : Nat.card ψ.range = 9 := by rw [hcard, hidx]
    obtain ⟨Tbar, hTbarEl, hTbarCard, hTbarNorm, α, hαmem, hα⟩ := hfour hcard9
    obtain ⟨b₀, hb₀ψ⟩ := hαmem
    have hodd : Odd (Nat.card π.ker) := by
      rw [show π.ker = Subgroup.center ↥K from QuotientGroup.ker_mk' _]
      exact CFSG.HardMathSupport.Timmesfeld.OrthogonalGeneration.odd_card_center_of_primeCore_eq_bot
        (by norm_num) Nat.prime_three hcore
    have hker : π.ker ≤ Subgroup.center ↥K := by
      rw [show π.ker = Subgroup.center ↥K from QuotientGroup.ker_mk' _]
    obtain ⟨T0, hT0map, hT0el, hT0card, hT0disj, hT0nat⟩ :=
      CFSG.exists_lift_elemAbelian_two_of_central_odd_ker
        (f := π) (QuotientGroup.mk'_surjective _) hker hodd hTbarEl hTbarCard
    have hπinj : ∀ x ∈ T0, ∀ y ∈ T0, π x = π y → x = y := by
      intro x hx y hy hxy
      have hmem : x⁻¹ * y ∈ T0 ⊓ π.ker := by
        refine Subgroup.mem_inf.2 ⟨T0.mul_mem (T0.inv_mem hx) hy, ?_⟩
        rw [MonoidHom.mem_ker, map_mul, map_inv, hxy, inv_mul_cancel]
      rw [hT0disj] at hmem
      exact inv_mul_eq_one.mp (Subgroup.mem_bot.1 hmem)
    have hψmem : ∀ b : ↥B, ∀ q ∈ Tbar, normalizerToCenterQuotientAut K B hBN b q ∈ Tbar := by
      intro b q hq
      have hmap := hTbarNorm (normalizerToCenterQuotientAut K B hBN b)
        (MonoidHom.mem_range.2 ⟨b, rfl⟩)
      rw [← hmap]
      exact Subgroup.mem_map_of_mem _ hq
    have hconjT0 : ∀ b : ↥B, ∀ t ∈ T0,
        normalizerConjAutOfMem K B hBN b t ∈ T0 := by
      intro b t ht
      exact hT0nat (normalizerConjAutOfMem K B hBN b) (normalizerToCenterQuotientAut K B hBN b)
        (fun k => normalizerConjAutOfMem_comp_mk K B hBN b k) (hψmem b) t ht
    let T : Subgroup Y := T0.map K.subtype
    have hTK : T ≤ K := Subgroup.map_subtype_le T0
    have hTel : IsElemAbelian 2 T := hT0el.map K.subtype
    have hTcard : Nat.card T = 4 := by
      rw [show T = T0.map K.subtype from rfl,
        Subgroup.card_map_of_injective K.subtype_injective, hT0card]
    have hconj : ∀ b ∈ B, ∀ t ∈ T, b * t * b⁻¹ ∈ T := by
      intro b hb t ht
      obtain ⟨x, hx, rfl⟩ := ht
      refine Subgroup.mem_map.2 ⟨normalizerConjAutOfMem K B hBN ⟨b, hb⟩ x, hconjT0 ⟨b, hb⟩ x hx, ?_⟩
      exact Subgroup.normalizerMonoidHom_apply_apply_coe (H := K)
        (Subgroup.inclusion hBN ⟨b, hb⟩) x
    have hTnorm : B ≤ Subgroup.normalizer (T : Set Y) := by
      intro b hb
      rw [Subgroup.mem_normalizer_iff]
      intro x
      constructor
      · intro hx
        exact hconj b hb x hx
      · intro hx
        have hb' : b⁻¹ ∈ B := B.inv_mem hb
        have h := hconj b⁻¹ hb' (b * x * b⁻¹) hx
        simpa [mul_assoc] using h
    have hBT : ⁅B, T⁆ ≤ T := by
      refine Subgroup.commutator_le.2 fun b hb t ht => ?_
      rw [commutatorElement_def]
      exact T.mul_mem (hconj b hb t ht) (T.inv_mem ht)
    have hTB : T ≤ ⁅B, T⁆ := by
      intro t ht
      obtain ⟨x, hx, rfl⟩ := ht
      have hq : π x ∈ Tbar := by
        rw [← hT0map]
        exact Subgroup.mem_map_of_mem _ hx
      obtain ⟨s, hs, hqs⟩ := hα (π x) hq
      obtain ⟨y, hy, hys⟩ := Subgroup.mem_map.1 (hT0map ▸ hs)
      set z : ↥K := normalizerConjAutOfMem K B hBN b₀ y * y⁻¹ with hz
      have hzT0 : z ∈ T0 := T0.mul_mem (hconjT0 b₀ y hy) (T0.inv_mem hy)
      have hπz : π z = π x := by
        rw [hz, map_mul, map_inv, normalizerConjAutOfMem_comp_mk, hys]
        rw [show normalizerToCenterQuotientAut K B hBN b₀ = ψ b₀ from rfl, hb₀ψ]
        exact hqs.symm
      have hxz : x = z := hπinj x hx z hzT0 hπz.symm
      have hmem : ⁅(b₀ : Y), K.subtype y⁆ ∈ ⁅B, T⁆ :=
        Subgroup.commutator_mem_commutator b₀.2 (Subgroup.mem_map_of_mem _ hy)
      have hzY : K.subtype z = ⁅(b₀ : Y), K.subtype y⁆ := by
        have hφy : K.subtype ((normalizerConjAutOfMem K B hBN b₀) y) =
            (b₀ : Y) * K.subtype y * (b₀ : Y)⁻¹ :=
          Subgroup.normalizerMonoidHom_apply_apply_coe (H := K)
            (Subgroup.inclusion hBN b₀) y
        rw [hz, map_mul, hφy, map_inv, commutatorElement_def, mul_assoc]
      rw [hxz, hzY]
      exact hmem
    exact ⟨T, hTK, hTel, hTcard, hTnorm, le_antisymm hBT hTB⟩


private theorem eight_dvd_of_mul_gcd {P q g t : ℕ} (hq : q % 2 = 1) (hg : g ∣ 3)
    (hform : P * g = q ^ 3 * ((q ^ 2 - 1) * t)) : 8 ∣ P := by
  have hqodd : Odd q := Nat.odd_iff.mpr hq
  have h8 : 8 ∣ q ^ 2 - 1 := Nat.eight_dvd_sq_sub_one_of_odd hqodd
  have h8rhs : 8 ∣ q ^ 3 * ((q ^ 2 - 1) * t) := (h8.mul_right t).mul_left (q ^ 3)
  rw [← hform] at h8rhs
  have hgodd : Odd g := Odd.of_dvd_nat (by norm_num : Odd 3) hg
  have hcop : Nat.Coprime 8 g := (Nat.coprime_two_left.mpr hgodd).pow_left 3
  exact hcop.dvd_of_dvd_mul_right h8rhs

private theorem eight_dvd_card_of_l3Model {S : Type} [Group S] (h : L3Model S) :
    8 ∣ Nat.card S := by
  rcases h with ⟨K, hK, hKf, hmod, ⟨e⟩⟩ | ⟨K, hK, hKf, p, f, hp, hf, hmod, hcard, ⟨e⟩⟩
  · have hqodd : Nat.card K % 2 = 1 := by omega
    have hform := CFSG.Timmesfeld.ClassicalOrders.card_psl_three_mul_gcd (K := K)
    have h8 : 8 ∣ Nat.card (StatedProj (StatedSL 3 K)) :=
      eight_dvd_of_mul_gcd hqodd (Nat.gcd_dvd_left 3 (Nat.card K - 1)) hform
    exact (Nat.card_congr e.toEquiv).symm ▸ h8
  · have hqodd : p ^ f % 2 = 1 := by omega
    have hform := CFSG.Timmesfeld.ClassicalOrders.card_psu_three_mul_gcd (K := K) hp hf hcard
    have h8 : 8 ∣ Nat.card (StatedProj (StatedSU 3 (p ^ f) K)) :=
      eight_dvd_of_mul_gcd hqodd (Nat.gcd_dvd_left 3 (p ^ f + 1)) hform
    exact (Nat.card_congr e.toEquiv).symm ▸ h8

private theorem not_prime_card_of_l3Model {S : Type} [Group S] (h : L3Model S) :
    ¬ (Nat.card S).Prime := by
  have h8 := eight_dvd_card_of_l3Model h
  intro hp
  have h2 : 2 ∣ Nat.card S := dvd_trans (by norm_num : 2 ∣ 8) h8
  have hP2 : Nat.card S = 2 := (hp.dvd_iff_eq (by norm_num)).1 h2
  have h82 : 8 ∣ 2 := by rwa [hP2] at h8
  norm_num at h82

theorem isSimpleGroup_of_l3Model {S : Type} [Group S] (h : L3Model S) :
    IsSimpleGroup S := by
  rcases h with ⟨K, hK, hKf, hmod, ⟨e⟩⟩ | ⟨K, hK, hKf, p, f, hp, hf, hmod, hcard, ⟨e⟩⟩
  · haveI : IsSimpleGroup (StatedProj (StatedSL 3 K)) :=
      CFSG.Open.StatedAPI.isSimpleGroup_statedProj_statedSL (d := 3) K (by norm_num)
        (Or.inl (by norm_num)) (Or.inl (by norm_num))
    exact e.isSimpleGroup
  · haveI : Fact p.Prime := ⟨hp⟩
    have hne : (3, p ^ f) ≠ (3, 2) := by
      intro hpair
      have h2 : p ^ f = 2 := by simpa using congrArg Prod.snd hpair
      omega
    haveI : IsSimpleGroup (StatedProj (StatedSU 3 (p ^ f) K)) :=
      CFSG.ClassicalGroups.Unitary.isSimpleGroup_statedProj_statedSU K p f hcard 3
        (by norm_num) hne
    exact e.isSimpleGroup

theorem center_eq_bot_of_l3Model {S : Type} [Group S] (h : L3Model S) :
    Subgroup.center S = ⊥ := by
  haveI := isSimpleGroup_of_l3Model h
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center S) with hbot | htop
  · exact hbot
  · exfalso
    have hcomm : IsMulCommutative S := IsMulCommutative.of_comm fun a b =>
      Subgroup.mem_center_iff.1 (htop ▸ Subgroup.mem_top b) a
    let _ : CommGroup S := { ‹Group S› with mul_comm := hcomm.is_comm.comm }
    have hp : (Nat.card S).Prime := Group.is_simple_iff_prime_card.mp inferInstance
    exact not_prime_card_of_l3Model h hp


private theorem three_dvd_card_of_l3Model {S : Type} [Group S] (h : L3Model S) :
    3 ∣ Nat.card S := by
  rcases h with ⟨K, hK, hKf, hmod, ⟨e⟩⟩ | ⟨K, hK, hKf, p, f, hp, hf, hmod, hcard, ⟨e⟩⟩
  · have hq3 : Nat.card K % 3 ≠ 0 := by omega
    have h3 : 3 ∣ Nat.card (StatedProj (StatedSL 3 K)) :=
      CFSG.HardMathSupport.Solomon.Coordinator.i2326c_three_dvd_card_psl hq3
    exact (Nat.card_congr e.toEquiv).symm ▸ h3
  · have hq3 : p ^ f % 3 ≠ 0 := by omega
    have h3 : 3 ∣ Nat.card (StatedProj (StatedSU 3 (p ^ f) K)) :=
      CFSG.HardMathSupport.Solomon.Coordinator.i2326c_three_dvd_card_psu hcard hq3
    exact (Nat.card_congr e.toEquiv).symm ▸ h3

theorem field_of_facts (hL : L3AutFieldFacts) {K B : Subgroup Y}
    (hq : CFSG.Open.IsQuasisimple ↥K) (hcore : GLAPPrimeCore 3 ↥K = ⊥)
    (hcat : catalogIs (↥K ⧸ Subgroup.center ↥K) (onLie k3Lie))
    (hB : IsElemAbelian 3 B) (hBN : B ≤ Subgroup.normalizer (K : Set Y))
    (h27 : 27 ≤ (B ⊓ Subgroup.centralizer (K : Set Y)).relIndex B) :
    ∃ b ∈ B, b ∉ Subgroup.centralizer (K : Set Y) ∧
      GLAPComponent 3 (K ⊓ Subgroup.centralizer ({b} : Set Y))
        (GLAPLayer 3 (K ⊓ Subgroup.centralizer ({b} : Set Y))) ∧
      CFSG.Open.IsQuasisimple ↥(GLAPLayer 3 (K ⊓ Subgroup.centralizer ({b} : Set Y))) ∧
      GLAPPrimeCore 3 ↥(GLAPLayer 3 (K ⊓ Subgroup.centralizer ({b} : Set Y))) = ⊥ ∧
      catalogIs (↥(GLAPLayer 3 (K ⊓ Subgroup.centralizer ({b} : Set Y))) ⧸
        Subgroup.center ↥(GLAPLayer 3 (K ⊓ Subgroup.centralizer ({b} : Set Y)))) (onLie k3Lie) := by
  classical
  set S : Type := ↥K ⧸ Subgroup.center ↥K with hS
  set π : ↥K →* S := QuotientGroup.mk' (Subgroup.center ↥K) with hπ
  let ψ : ↥B →* MulAut S := normalizerToCenterQuotientAut K B hBN
  have hmodel : L3Model S := l3Model_of_catalogIs hcat
  have hAel : IsElemAbelian 3 ψ.range := KD1426Common.isElemAbelian_range hB ψ
  have hcard : Nat.card ψ.range = (B ⊓ Subgroup.centralizer (K : Set Y)).relIndex B :=
    card_range_normalizerToCenterQuotientAut ⟨hq.1⟩ hBN
  have hcard27 : 27 ≤ Nat.card ψ.range := by rw [hcard]; exact h27
  obtain ⟨α, hαmem, hαne, hcompα, hcatα⟩ := hL S hmodel ψ.range hAel hcard27
  obtain ⟨b, hbψ⟩ := hαmem
  have hcomp : GLAPComponent 3 (fixSubgroup (ψ b)) (GLAPLayer 3 (fixSubgroup (ψ b))) := by
    rwa [← hbψ] at hcompα
  have hcatb : catalogIs ↥(GLAPLayer 3 (fixSubgroup (ψ b))) (onLie k3Lie) := by
    rwa [← hbψ] at hcatα
  have hbnot : (b : Y) ∉ Subgroup.centralizer (K : Set Y) := by
    intro hbC
    have hψ1 : normalizerToCenterQuotientAut K B hBN b = 1 :=
      (normalizerToCenterQuotientAut_eq_one_iff ⟨hq.1⟩ hBN b).2 (Subgroup.mem_inf.2 ⟨b.2, hbC⟩)
    have hα1 : α = 1 := by
      rw [← hbψ]
      exact hψ1
    exact hαne hα1
  set β : MulAut ↥K := normalizerConjAutOfMem K B hBN b with hβ
  set X : Subgroup ↥K := fixSubgroup β with hX
  set Xbar : Subgroup S := fixSubgroup (ψ b) with hXbar
  set Jbar : Subgroup S := GLAPLayer 3 Xbar with hJbar
  have hcompJbar : GLAPComponent 3 Xbar Jbar := hcomp
  have hαβ : ∀ k : ↥K, π (β k) = ψ b (π k) :=
    fun k => normalizerConjAutOfMem_comp_mk K B hBN b k
  have hker : π.ker ≤ Subgroup.center ↥K := by
    rw [hπ, QuotientGroup.ker_mk']
  have huniq : ∀ C : Subgroup S, GLAPComponent 3 Xbar C → C = Jbar :=
    fun C hC => glaPComponent_eq_of_glaPLayer hcompJbar rfl hC
  obtain ⟨A, hAcomp, hAmap⟩ :=
    exists_glaPComponent_map_fixSubgroup π hker β (ψ b) hαβ
      (QuotientGroup.mk'_surjective _) Nat.prime_three hcompJbar
  have hmapLayer : (GLAPLayer 3 X).map π = Jbar :=
    map_glaPLayer_fixSubgroup_eq π hker β (ψ b) hαβ (QuotientGroup.mk'_surjective _)
      Nat.prime_three
  have hcomp_le_A : ∀ C : Subgroup ↥K, GLAPComponent 3 X C → C ≤ A := by
    intro C hC
    have hCbar : GLAPComponent 3 Xbar (C.map π) :=
      glaPComponent_map_fixSubgroup π hker β (ψ b) hαβ (QuotientGroup.mk'_surjective _)
        Nat.prime_three hC
    have hCbarEq : C.map π = Jbar := huniq _ hCbar
    have hCZA : C ≤ A ⊔ Subgroup.center ↥K := by
      intro c hc
      have hcπ : π c ∈ A.map π := by
        rw [hAmap, ← hCbarEq]
        exact Subgroup.mem_map_of_mem _ hc
      obtain ⟨a, ha, hac⟩ := Subgroup.mem_map.1 hcπ
      have hmem : c * a⁻¹ ∈ Subgroup.center ↥K := by
        have h1 : π (c * a⁻¹) = 1 := by
          rw [map_mul, map_inv, hac, mul_inv_cancel]
        exact (QuotientGroup.eq_one_iff (c * a⁻¹)).1 h1
      have hc' : c = (c * a⁻¹) * a := by group
      rw [hc']
      exact (A ⊔ Subgroup.center ↥K).mul_mem (Subgroup.mem_sup_right hmem)
        (Subgroup.mem_sup_left ha)
    exact CFSG.le_of_perfect_of_le_sup_center (glaPComponent_perfect hAcomp)
      (glaPComponent_perfect hC) hCZA
  have hlayerX : GLAPLayer 3 X = A := by
    apply le_antisymm
    · refine sSup_le fun C hC => hcomp_le_A C hC
    · exact le_sSup hAcomp
  have hsub : X.map K.subtype = K ⊓ Subgroup.centralizer ({(b : Y)} : Set Y) := by
    rw [hX, hβ]
    exact CFSG.map_eqLocus_normalizerMonoidHom K (hBN b.2)
  have hmapY : (GLAPLayer 3 X).map K.subtype =
      GLAPLayer 3 (K ⊓ Subgroup.centralizer ({(b : Y)} : Set Y)) := by
    rw [← hsub]
    exact CFSG.glaPLayer_map_eq_of_injective Nat.prime_three K.subtype K.subtype_injective X
  have hkerCop : Nat.Coprime 3 (Nat.card ↥(X ⊓ K.subtype.ker)) := by
    have hbot : X ⊓ K.subtype.ker = ⊥ := by
      rw [eq_bot_iff]
      intro y hy
      have : (y : ↥K) ∈ K.subtype.ker := hy.2
      simpa [Subgroup.ker_subtype] using this
    rw [hbot, Subgroup.card_bot]
    exact Nat.coprime_one_right 3
  have hAmapY : A.map K.subtype =
      GLAPLayer 3 (K ⊓ Subgroup.centralizer ({(b : Y)} : Set Y)) := by
    rw [← hlayerX, hmapY]
  have hcompJ : GLAPComponent 3 (K ⊓ Subgroup.centralizer ({(b : Y)} : Set Y))
      (GLAPLayer 3 (K ⊓ Subgroup.centralizer ({(b : Y)} : Set Y))) := by
    have hmap := glaPComponent_map Nat.prime_three K.subtype hkerCop hAcomp
    rw [hsub, hAmapY] at hmap
    exact hmap
  have hAperf : Group.IsPerfect ↥A := Subgroup.isPerfect_iff.mpr (glaPComponent_perfect hAcomp)
  have hkA : (MonoidHom.subgroupMap π A).ker ≤ Subgroup.center ↥A := by
    intro a ha
    rw [MonoidHom.mem_ker] at ha
    have haZ : (a : ↥K) ∈ Subgroup.center ↥K := by
      have h1 : π (a : ↥K) = 1 := by simpa using congrArg Subtype.val ha
      exact (QuotientGroup.eq_one_iff (a : ↥K)).1 h1
    rw [Subgroup.mem_center_iff]
    intro a'
    apply Subtype.ext
    exact Subgroup.mem_center_iff.1 haZ (a' : ↥K)
  have hZbar : Subgroup.center Jbar = ⊥ := center_eq_bot_of_l3Model (l3Model_of_catalogIs hcatb)
  let eAZ : (↥A ⧸ Subgroup.center ↥A) ≃*
      (↥(A.map π) ⧸ Subgroup.center ↥(A.map π)) :=
    CFSG.HardMathSupport.Curtis.NaturalModuleCensus.AltIb.centerQuotientEquiv hAperf
      (MonoidHom.subgroupMap π A) (MonoidHom.subgroupMap_surjective π A) hkA
  rw [hAmap] at eAZ
  have hJbarSimple : IsSimpleGroup (↥Jbar ⧸ Subgroup.center ↥Jbar) := by
    haveI := isSimpleGroup_of_l3Model (l3Model_of_catalogIs hcatb)
    exact ((QuotientGroup.quotientMulEquivOfEq hZbar).trans QuotientGroup.quotientBot).isSimpleGroup
  have hAq : CFSG.Open.IsQuasisimple ↥A := by
    refine ⟨hAperf.commutator_eq_top, ?_⟩
    exact (MulEquiv.isSimpleGroup_congr eAZ).mpr hJbarSimple
  let eAJ : ↥A ≃* ↥(A.map K.subtype) := Subgroup.equivMapOfInjective A K.subtype K.subtype_injective
  have hJq : CFSG.Open.IsQuasisimple
      ↥(GLAPLayer 3 (K ⊓ Subgroup.centralizer ({(b : Y)} : Set Y))) :=
    KD1426Common.isQuasisimple_of_mulEquiv
      (eAJ.trans (MulEquiv.subgroupCongr hAmapY)) hAq
  have eZ : (↥A ⧸ Subgroup.center ↥A) ≃*
      (↥(GLAPLayer 3 (K ⊓ Subgroup.centralizer ({(b : Y)} : Set Y))) ⧸
        Subgroup.center ↥(GLAPLayer 3 (K ⊓ Subgroup.centralizer ({(b : Y)} : Set Y)))) :=
    (QuotientGroup.congr (Subgroup.center ↥A)
      (Subgroup.center ↥(A.map K.subtype)) eAJ (Subgroup.map_center_eq eAJ)).trans
      (QuotientGroup.congr (Subgroup.center ↥(A.map K.subtype))
        (Subgroup.center ↥(GLAPLayer 3 (K ⊓ Subgroup.centralizer ({(b : Y)} : Set Y))))
        (MulEquiv.subgroupCongr hAmapY)
        (Subgroup.map_center_eq (MulEquiv.subgroupCongr hAmapY)))
  have eJbar : (↥(GLAPLayer 3 (K ⊓ Subgroup.centralizer ({(b : Y)} : Set Y))) ⧸
        Subgroup.center ↥(GLAPLayer 3 (K ⊓ Subgroup.centralizer ({(b : Y)} : Set Y)))) ≃*
      ↥Jbar :=
    eZ.symm.trans <|
      (eAZ.trans ((QuotientGroup.quotientMulEquivOfEq hZbar).trans QuotientGroup.quotientBot))
  have hcatJ : catalogIs (↥(GLAPLayer 3 (K ⊓ Subgroup.centralizer ({(b : Y)} : Set Y))) ⧸
        Subgroup.center ↥(GLAPLayer 3 (K ⊓ Subgroup.centralizer ({(b : Y)} : Set Y))))
      (onLie k3Lie) := by
    obtain ⟨i, hi, ⟨e2⟩⟩ := hcatb
    exact ⟨i, hi, ⟨eJbar.trans e2⟩⟩
  let ZJbar : Subgroup S := Jbar ⊓ Subgroup.centralizer (Jbar : Set S)
  have hZJbarBot : ZJbar = ⊥ := by
    rw [show ZJbar = Jbar ⊓ Subgroup.centralizer (Jbar : Set S) from rfl,
      CFSG.GroupTheory.inf_centralizer_eq_map_center, hZbar, Subgroup.map_bot]
  have hcomapA := CFSG.LocalCores.comap_center_eq_of_perfect hAperf
    (MonoidHom.subgroupMap π A) (MonoidHom.subgroupMap_surjective π A) hkA
  have hZmap : Subgroup.center ↥(A.map π) = ⊥ := by
    rw [hAmap]
    exact hZbar
  rw [hZmap, MonoidHom.comap_bot] at hcomapA
  have hZA : (Subgroup.center ↥A).map A.subtype ≤ Subgroup.center ↥K := by
    intro x hx
    obtain ⟨a, ha, rfl⟩ := Subgroup.mem_map.1 hx
    have haKer : a ∈ (MonoidHom.subgroupMap π A).ker := by rw [hcomapA]; exact ha
    rw [MonoidHom.mem_ker] at haKer
    have h1 : π (a : ↥K) = 1 := by simpa using congrArg Subtype.val haKer
    exact (QuotientGroup.eq_one_iff (a : ↥K)).1 h1
  have hZJp : IsPGroup 3 (Subgroup.center
      ↥(GLAPLayer 3 (K ⊓ Subgroup.centralizer ({(b : Y)} : Set Y)))) := by
    set J : Subgroup Y := GLAPLayer 3 (K ⊓ Subgroup.centralizer ({(b : Y)} : Set Y)) with hJ
    set ZK : Subgroup Y := (Subgroup.center ↥K).map K.subtype with hZK
    have hJK : J ≤ K := by
      rw [hJ]
      unfold GLAPLayer
      exact sSup_le fun L hL => hL.1.trans inf_le_left
    have hJsub : J.subgroupOf K = GLAPLayer 3 X := by
      rw [← hmapY]
      exact Subgroup.comap_map_eq_self_of_injective K.subtype_injective _
    have hJmap : (J.subgroupOf K).map π = Jbar := by
      rw [hJsub]
      exact hmapLayer
    have hZKp : IsPGroup 3 ZK :=
      (CFSG.HardMathSupport.Solomon.Coordinator.isPGroup_center_of_pPrimeCore_eq_bot
        Nat.prime_three hcore).map K.subtype
    have hZKcomap : IsPGroup 3 (ZK.comap J.subtype) :=
      hZKp.comap_of_injective J.subtype J.subtype_injective
    have hZle : Subgroup.center ↥J ≤ ZK.comap J.subtype := by
      intro z hz
      rw [Subgroup.mem_comap]
      have hmemJ : π (⟨z.1, hJK z.2⟩ : ↥K) ∈ Jbar := by
        have h1 : π (⟨z.1, hJK z.2⟩ : ↥K) ∈ (J.subgroupOf K).map π :=
          Subgroup.mem_map_of_mem π (K := J.subgroupOf K)
            (x := ⟨z.1, hJK z.2⟩) ((Subgroup.mem_subgroupOf).2 z.2)
        rwa [hJmap] at h1
      have hcen : π (⟨z.1, hJK z.2⟩ : ↥K) ∈ Subgroup.centralizer (Jbar : Set S) := by
        rw [Subgroup.mem_centralizer_iff]
        intro y hy
        have hy' : y ∈ (J.subgroupOf K).map π := by
          rw [hJmap]
          exact hy
        obtain ⟨j, hj, hjq⟩ := Subgroup.mem_map.1 hy'
        let jJ : ↥J := ⟨(j : ↥K), (Subgroup.mem_subgroupOf).1 hj⟩
        have hcomm : jJ * z = z * jJ := Subgroup.mem_center_iff.1 hz jJ
        have hcommK : (⟨z.1, hJK z.2⟩ : ↥K) * j = j * (⟨z.1, hJK z.2⟩ : ↥K) := by
          apply Subtype.ext
          exact congrArg J.subtype hcomm.symm
        rw [← hjq, ← map_mul, ← map_mul, hcommK]
      have hbot : π (⟨z.1, hJK z.2⟩ : ↥K) ∈ ZJbar := Subgroup.mem_inf.2 ⟨hmemJ, hcen⟩
      rw [hZJbarBot, Subgroup.mem_bot] at hbot
      exact Subgroup.mem_map_of_mem _ ((QuotientGroup.eq_one_iff _).1 hbot)
    exact hZKcomap.of_injective (Subgroup.inclusion hZle) (Subgroup.inclusion_injective hZle)
  have hcoreJ : GLAPPrimeCore 3
      ↥(GLAPLayer 3 (K ⊓ Subgroup.centralizer ({(b : Y)} : Set Y))) = ⊥ := by
    set J : Subgroup Y := GLAPLayer 3 (K ⊓ Subgroup.centralizer ({(b : Y)} : Set Y)) with hJ
    have h3bar : 3 ∣ Nat.card Jbar := three_dvd_card_of_l3Model (l3Model_of_catalogIs hcatb)
    have h3quot : 3 ∣ Nat.card (↥J ⧸ Subgroup.center ↥J) := by
      rw [Nat.card_congr eJbar.toEquiv]
      exact h3bar
    exact CFSG.gLAPPrimeCore_eq_bot_of_quasisimple_of_isPGroup_center
      Nat.prime_three hJq hZJp h3quot
  exact ⟨(b : Y), b.2, hbnot, hcompJ, hJq, hcoreJ, hcatJ⟩

end CFSG.LocalAnalysis.GLTheoremA.KD1426Lie

end
