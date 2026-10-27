module

public import CFSG.CGT.PushingUpLit.LIT.Foote.TheoremADef
public import CFSG.RankThree.Coprime.ThompsonElementaryComplement
public import CFSG.Timmesfeld.Basic
public import CFSG.CGT.PushingUp.BenderBridge
public import CFSG.CGT.PushingUp.BlockOrder
public import CFSG.CGT.PushingUpLit.BHS.SymNatDefs
public import CFSG.CGT.PushingUpLit.CGT6.EmbeddingNodes
public import CFSG.CGT.PushingUpLit.LIT.Foote.Top
public import CFSG.CGT.PushingUpLit.LIT.Foote.ZSub
public import CFSG.CGT.PushingUpLit.LIT.FooteSplit
public import CFSG.CGT.PushingUpLit.Statements
public import CFSG.CGT.PushingUpLit.T2K.Basic
public import CFSG.Foundations
public import CFSG.GH74.SectionalRank
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherKnownGroupFacts
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTheorem3WeakClosure
public import CFSG.LocalAnalysis.ComponentClassification.DisjointSolvableKernels
public import CFSG.LocalAnalysis.ComponentClassification.LBalanceComponentLifts
public import CFSG.LocalAnalysis.ComponentClassification.LayerMultiplication
public import CFSG.LocalAnalysis.ComponentClassification.MinimalBCenter
public import CFSG.LocalAnalysis.ComponentClassification.OrdinaryComponentJoins
public import CFSG.LocalAnalysis.ComponentClassification.SmallLocalFitting
public import CFSG.LocalAnalysis.ComponentClassification.TwoLayer
public import CFSG.LocalAnalysis.ComponentClassification.UniversalOrbitBlock
public import CFSG.LocalAnalysis.ComponentInitial.CommutingBlock
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.CampbellMotion
public import CFSG.LocalAnalysis.SectionRank.Ccomm.OddCritical
public import CFSG.LocalAnalysis.SectionRank.Framework.SylowRank
public import CFSG.LocalAnalysis.SignalizerFunctor
public import CFSG.Quasithin.Background.A1cModuleCoprime
public import CFSG.Quasithin.Background.B15P4LayerDict
public import CFSG.Quasithin.Background.B1MoreElevenB
public import CFSG.Quasithin.Background.B1MoreNineG
public import CFSG.RankThree.PartTwo.Sec6.Statements
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PSL2Contragredient
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.ProjectiveSemilinear
public import CFSG.Walter.Defs

public section

namespace CFSG.CGT.PushingUpLit.LIT.Foote

open CFSG CFSG.CGT.PushingUpLit
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem centralizes_of_central_commutators {Γ : Type*} [Group Γ] {Kh P : Subgroup Γ} [Kh.Normal]
    [P.Normal] (hperf : ⁅Kh, Kh⁆ = Kh) (hQ : ⁅P ⊓ Kh, Kh⁆ = ⊥) : ⁅Kh, P⁆ = ⊥ := by
  have h1 : ⁅Kh, P⁆ ≤ P ⊓ Kh :=
    le_inf (Subgroup.commutator_le_right Kh P) (Subgroup.commutator_le_left Kh P)
  have h2 : ⁅⁅Kh, P⁆, Kh⁆ = ⊥ := eq_bot_iff.2 (hQ ▸ Subgroup.commutator_mono h1 le_rfl)
  have h3 : ⁅⁅P, Kh⁆, Kh⁆ = ⊥ := by rw [Subgroup.commutator_comm P Kh]; exact h2
  have h4 := Subgroup.commutator_commutator_eq_bot_of_rotate (H₁ := Kh) (H₂ := Kh) (H₃ := P) h2 h3
  rwa [hperf] at h4

theorem exists_odd_prime_inverted {Γ : Type*} [Group Γ] [Finite Γ] {a b : Γ} (ha : a * a = 1)
    (hb : b * b = 1) (hnot : ¬ IsPGroup 2 (Subgroup.closure ({a, b} : Set Γ))) :
    ∃ c : Γ, ∃ p : ℕ, p.Prime ∧ p ≠ 2 ∧ orderOf c = p ∧ a * c * a⁻¹ = c⁻¹ := by
  set t := a * b with ht
  have hnot2 : ¬ ∃ k : ℕ, t ^ 2 ^ k = 1 := fun ⟨k, hk⟩ =>
    hnot (CFSG.Timmesfeld.isPGroup_two_closure_pair ha hb hk)
  have ho : orderOf t ≠ 0 := (orderOf_pos t).ne'
  obtain ⟨s, m, hm, hsm⟩ := Nat.exists_eq_two_pow_mul_odd ho
  have hm1 : m ≠ 1 := by
    intro h1
    apply hnot2
    refine ⟨s, ?_⟩
    rw [← orderOf_dvd_iff_pow_eq_one, hsm, h1, mul_one]
  have hpm : (Nat.minFac m).Prime := Nat.minFac_prime hm1
  have hpdvd : Nat.minFac m ∣ orderOf t := hsm ▸ Dvd.dvd.mul_left (Nat.minFac_dvd m) _
  have hpodd : Nat.minFac m ≠ 2 := by
    intro h2
    have : 2 ∣ m := h2 ▸ Nat.minFac_dvd m
    exact (Nat.not_even_iff_odd.2 hm) (even_iff_two_dvd.2 this)
  refine ⟨t ^ (orderOf t / Nat.minFac m), Nat.minFac m, hpm, hpodd, ?_, ?_⟩
  · exact orderOf_pow_orderOf_div ho hpdvd
  · have hainv : a⁻¹ = a := inv_eq_of_mul_eq_one_right ha
    have hbinv : b⁻¹ = b := inv_eq_of_mul_eq_one_right hb
    have hat : a * t * a⁻¹ = t⁻¹ := by
      rw [ht, mul_inv_rev, hbinv, hainv]
      calc a * (a * b) * a = (a * a) * b * a := by group
        _ = b * a := by rw [ha, one_mul]
    rw [← conj_pow, hat, inv_pow]

theorem exists_lift_primePower {X Y : Type*} [Group X] [Group Y] [Finite X] (f : X →* Y)
    {p : ℕ} [hp : Fact p.Prime] {c : Y} (hc : c ∈ f.range) {s : ℕ} (hcs : c ^ p ^ s = 1) :
    ∃ x : X, f x = c ∧ ∃ m : ℕ, x ^ p ^ m = 1 := by
  obtain ⟨x₀, hx₀⟩ := hc
  have hn : orderOf x₀ ≠ 0 := (orderOf_pos x₀).ne'
  obtain ⟨e, n', hn', hn⟩ := Nat.exists_eq_pow_mul_and_not_dvd hn p hp.out.ne_one
  have hcop : Nat.Coprime (p ^ e) n' :=
    Nat.Coprime.pow_left e ((Nat.Prime.coprime_iff_not_dvd hp.out).2 hn')
  obtain ⟨k, hk1, hk2⟩ := Nat.chineseRemainder hcop 1 0
  refine ⟨x₀ ^ k, ?_, e, ?_⟩
  · rw [map_pow, hx₀]
    have h1 : orderOf c ∣ p ^ s := orderOf_dvd_of_pow_eq_one hcs
    have h2 : orderOf c ∣ orderOf x₀ := by rw [← hx₀]; exact orderOf_map_dvd f x₀
    obtain ⟨t, -, hge⟩ := (Nat.dvd_prime_pow hp.out).1 h1
    have h3 : p ^ t ∣ p ^ e := by
      have h5 : p ^ t ∣ p ^ e * n' := by rw [← hge, ← hn]; exact h2
      have hcop' : Nat.Coprime (p ^ t) n' :=
        Nat.Coprime.pow_left t ((Nat.Prime.coprime_iff_not_dvd hp.out).2 hn')
      exact (Nat.Coprime.dvd_of_dvd_mul_right hcop' h5)
    have h4 : k ≡ 1 [MOD orderOf c] := hk1.of_dvd (hge ▸ h3)
    rw [pow_eq_pow_iff_modEq.2 h4, pow_one]
  · rw [← pow_mul, ← orderOf_dvd_iff_pow_eq_one, hn]
    have : n' ∣ k := (Nat.modEq_zero_iff_dvd).1 hk2
    obtain ⟨c', hc'⟩ := this
    exact ⟨c', by rw [hc']; ring⟩

theorem exists_fixed_ne_one_of_two_element {S : Subgroup G} (h2 : 2 ∣ Nat.card S) {m : G}
    (hmN : m ∈ Subgroup.normalizer (S : Set G)) {n : ℕ} (hm : m ^ (2 ^ n) = 1) :
    ∃ d ∈ S, d ≠ 1 ∧ m * d = d * m := by
  classical
  have hf : ∀ x : G, (MulAut.toPerm G (MulAut.conj m)) x ∈ S ↔ x ∈ S := fun x =>
    (Subgroup.mem_normalizer_iff.1 hmN x).symm
  let σ : Equiv.Perm {x // x ∈ S} := (MulAut.toPerm G (MulAut.conj m)).subtypePerm hf
  have hfpow : (MulAut.toPerm G (MulAut.conj m)) ^ 2 ^ n = 1 := by
    rw [← map_pow, ← map_pow, hm, map_one, map_one]
  have hσ : σ ^ 2 ^ n = 1 := by
    ext ⟨x, hx⟩
    simp only [σ, Equiv.Perm.subtypePerm_pow, Equiv.Perm.subtypePerm_apply, hfpow,
      Equiv.Perm.coe_one, id_eq]
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fintype ↥S := Fintype.ofFinite _
  have hcard : 2 ∣ Fintype.card {x // x ∈ S} := by
    rw [← Nat.card_eq_fintype_card]
    exact h2
  have h1 : σ ⟨1, S.one_mem⟩ = ⟨1, S.one_mem⟩ := by
    apply Subtype.ext
    show m * 1 * m⁻¹ = 1
    group
  obtain ⟨b, hb, hb1⟩ := Equiv.Perm.exists_fixed_point_of_prime' hcard hσ h1
  refine ⟨b, b.2, fun h => hb1 (Subtype.ext h), ?_⟩
  have hb' : m * (b : G) * m⁻¹ = b := congrArg Subtype.val hb
  calc m * (b : G) = m * (b : G) * m⁻¹ * m := by group
    _ = (b : G) * m := by rw [hb']

theorem exists_fixed_of_comm {K : Subgroup G} (hK : QBlock K) {y : G}
    (hyK : y ∈ Subgroup.normalizer (K : Set G))
    (hy2 : y * y ∈ Subgroup.centralizer (blockU K : Set G))
    (hc : ∀ k ∈ K, ∀ v ∈ blockU K, ⁅y, k⁆ * v = v * ⁅y, k⁆) :
    ∃ a ∈ blockU K, a * y = y * a ∧ ∃ k ∈ K, a * k ≠ k * a := by
  by_contra hcon
  push Not at hcon
  have hVy : ∀ v ∈ blockU K, y * v * y⁻¹ ∈ blockU K := fun v hv => conj_mem_blockU hyK hv
  have hsq := hK.blockU_sq_eq_one
  have hφ : ∀ v ∈ blockU K, ∀ k ∈ K,
      (v * (y * v * y⁻¹)⁻¹) * k = k * (v * (y * v * y⁻¹)⁻¹) := by
    intro v hv k hk
    have hφV : v * (y * v * y⁻¹)⁻¹ ∈ blockU K :=
      (blockU K).mul_mem hv ((blockU K).inv_mem (hVy v hv))
    refine hcon _ hφV ?_ k hk
    have hy2v : (y * y) * v⁻¹ = v⁻¹ * (y * y) :=
      (Subgroup.mem_centralizer_iff.1 hy2 _ ((blockU K).inv_mem hv)).symm
    have h1 : y * (v * (y * v * y⁻¹)⁻¹) * y⁻¹ = (v * (y * v * y⁻¹)⁻¹)⁻¹ := by
      calc y * (v * (y * v * y⁻¹)⁻¹) * y⁻¹
          = (y * v * y⁻¹) * ((y * y) * v⁻¹ * (y * y)⁻¹) := by group
        _ = (y * v * y⁻¹) * v⁻¹ := by rw [hy2v]; group
        _ = (v * (y * v * y⁻¹)⁻¹)⁻¹ := by group
    have h2 : (v * (y * v * y⁻¹)⁻¹)⁻¹ = v * (y * v * y⁻¹)⁻¹ :=
      inv_eq_of_mul_eq_one_right (hsq _ hφV)
    rw [h2] at h1
    calc (v * (y * v * y⁻¹)⁻¹) * y = (y * (v * (y * v * y⁻¹)⁻¹) * y⁻¹) * y := by rw [h1]
      _ = y * (v * (y * v * y⁻¹)⁻¹) := by group
  have hu : ∀ k ∈ K, ∀ v ∈ blockU K,
      (k * v * k⁻¹ * v⁻¹) * y = y * (k * v * k⁻¹ * v⁻¹) := by
    intro k hk v hv
    have hwV : y * v * y⁻¹ ∈ blockU K := hVy v hv
    have hφV : v * (y * v * y⁻¹)⁻¹ ∈ blockU K :=
      (blockU K).mul_mem hv ((blockU K).inv_mem hwV)
    have hφk := hφ v hv k hk
    have hcV : ∀ u ∈ blockU K, ⁅y, k⁆ * u = u * ⁅y, k⁆ := hc k hk
    have hkwV : k * (y * v * y⁻¹) * k⁻¹ ∈ blockU K := QBlock.conj_mem_blockU' hk hwV
    have hyk : y * k * y⁻¹ = ⁅y, k⁆ * k := by rw [commutatorElement_def]; group
    have h1 : y * (k * v * k⁻¹ * v⁻¹) * y⁻¹ =
        (k * (y * v * y⁻¹) * k⁻¹) * (y * v * y⁻¹)⁻¹ := by
      calc y * (k * v * k⁻¹ * v⁻¹) * y⁻¹
          = (y * k * y⁻¹) * (y * v * y⁻¹) * (y * k * y⁻¹)⁻¹ * (y * v * y⁻¹)⁻¹ := by group
        _ = (⁅y, k⁆ * k) * (y * v * y⁻¹) * (⁅y, k⁆ * k)⁻¹ * (y * v * y⁻¹)⁻¹ := by rw [hyk]
        _ = ⁅y, k⁆ * (k * (y * v * y⁻¹) * k⁻¹) * ⁅y, k⁆⁻¹ * (y * v * y⁻¹)⁻¹ := by group
        _ = (k * (y * v * y⁻¹) * k⁻¹) * ⁅y, k⁆ * ⁅y, k⁆⁻¹ * (y * v * y⁻¹)⁻¹ := by
            rw [hcV _ hkwV]
        _ = (k * (y * v * y⁻¹) * k⁻¹) * (y * v * y⁻¹)⁻¹ := by group
    have hX : (k * (y * v * y⁻¹) * k⁻¹) * (y * v * y⁻¹)⁻¹ ∈ blockU K :=
      (blockU K).mul_mem hkwV ((blockU K).inv_mem hwV)
    have hφX : (v * (y * v * y⁻¹)⁻¹) * ((k * (y * v * y⁻¹) * k⁻¹) * (y * v * y⁻¹)⁻¹) =
        ((k * (y * v * y⁻¹) * k⁻¹) * (y * v * y⁻¹)⁻¹) * (v * (y * v * y⁻¹)⁻¹) :=
      hK.blockU_comm _ hφV _ hX
    have hkφ : k * (v * (y * v * y⁻¹)⁻¹) * k⁻¹ = v * (y * v * y⁻¹)⁻¹ := by
      rw [← hφk]; group
    have h2 : k * v * k⁻¹ * v⁻¹ = (k * (y * v * y⁻¹) * k⁻¹) * (y * v * y⁻¹)⁻¹ := by
      calc k * v * k⁻¹ * v⁻¹
          = (k * (v * (y * v * y⁻¹)⁻¹) * k⁻¹) * (k * (y * v * y⁻¹) * k⁻¹) * (y * v * y⁻¹)⁻¹ *
              (v * (y * v * y⁻¹)⁻¹)⁻¹ := by group
        _ = (v * (y * v * y⁻¹)⁻¹) * (k * (y * v * y⁻¹) * k⁻¹) * (y * v * y⁻¹)⁻¹ *
              (v * (y * v * y⁻¹)⁻¹)⁻¹ := by rw [hkφ]
        _ = (v * (y * v * y⁻¹)⁻¹) * ((k * (y * v * y⁻¹) * k⁻¹) * (y * v * y⁻¹)⁻¹) *
              (v * (y * v * y⁻¹)⁻¹)⁻¹ := by group
        _ = ((k * (y * v * y⁻¹) * k⁻¹) * (y * v * y⁻¹)⁻¹) * (v * (y * v * y⁻¹)⁻¹) *
              (v * (y * v * y⁻¹)⁻¹)⁻¹ := by rw [hφX]
        _ = (k * (y * v * y⁻¹) * k⁻¹) * (y * v * y⁻¹)⁻¹ := by group
    have h3 : y * (k * v * k⁻¹ * v⁻¹) * y⁻¹ = k * v * k⁻¹ * v⁻¹ := h1.trans h2.symm
    calc (k * v * k⁻¹ * v⁻¹) * y = (y * (k * v * k⁻¹ * v⁻¹) * y⁻¹) * y := by rw [h3]
      _ = y * (k * v * k⁻¹ * v⁻¹) := by group
  have hVle : blockU K ≤ Subgroup.centralizer (K : Set G) := by
    rw [← hK.blockU_stable]
    refine Subgroup.commutator_le.2 fun v hv k hk => ?_
    have he : ⁅v, k⁆ = (k * v * k⁻¹ * v⁻¹)⁻¹ := by
      simp only [commutatorElement_def]; group
    rw [he]
    refine (Subgroup.centralizer (K : Set G)).inv_mem
      (Subgroup.mem_centralizer_iff.2 fun k' hk' => ?_)
    have hmem : k * v * k⁻¹ * v⁻¹ ∈ blockU K :=
      (blockU K).mul_mem (QBlock.conj_mem_blockU' hk hv) ((blockU K).inv_mem hv)
    exact (hcon _ hmem (hu k hk v hv) k' hk').symm
  exact absurd (le_inf le_rfl hVle : blockU K ≤ blockZ K)
    (not_le_of_gt (blockZ_lt_of_short hK.short))

@[expose] def commSub (k : G) (V : Subgroup G) : Subgroup G :=
  Subgroup.closure {w | ∃ v ∈ V, w = k * v * k⁻¹ * v⁻¹}

theorem exists_fixed_of_odd {K : Subgroup G} (hK : QBlock K) {y : G}
    (hyK : y ∈ Subgroup.normalizer (K : Set G)) {n : ℕ} (hn : y ^ 2 ^ n = 1) {k₁ : G}
    (hk₁ : k₁ ∈ K) {p m : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hk₁p : k₁ ^ p ^ m = 1)
    (hnt : ∃ v ∈ blockU K, k₁ * v ≠ v * k₁)
    (hinv : ∀ v ∈ blockU K,
      (y * k₁ * y⁻¹) * v * (y * k₁ * y⁻¹)⁻¹ = k₁⁻¹ * v * k₁) :
    ∃ a ∈ blockU K, a * y = y * a ∧ ∃ k ∈ K, a * k ≠ k * a := by
  classical
  have hVy : ∀ v ∈ blockU K, y * v * y⁻¹ ∈ blockU K := fun v hv => conj_mem_blockU hyK hv
  have hk₁V : ∀ v ∈ blockU K, k₁ * v * k₁⁻¹ ∈ blockU K := fun v hv =>
    QBlock.conj_mem_blockU' hk₁ hv
  have hk₁Vinv : ∀ v ∈ blockU K, k₁⁻¹ * v * k₁ ∈ blockU K := fun v hv => by
    have := QBlock.conj_mem_blockU' (K.inv_mem hk₁) hv
    simpa using this
  have hgen : ∀ v ∈ blockU K, k₁ * v * k₁⁻¹ * v⁻¹ ∈ commSub k₁ (blockU K) := fun v hv =>
    Subgroup.subset_closure ⟨v, hv, rfl⟩
  have hV₀V : commSub k₁ (blockU K) ≤ blockU K := by
    refine (Subgroup.closure_le _).2 ?_
    rintro _ ⟨v, hv, rfl⟩
    exact (blockU K).mul_mem (hk₁V v hv) ((blockU K).inv_mem hv)
  obtain ⟨v₀, hv₀, hv₀ne⟩ := hnt
  have hV₀ne : commSub k₁ (blockU K) ≠ ⊥ := by
    intro hbot
    have hmem := hgen v₀ hv₀
    rw [hbot, Subgroup.mem_bot] at hmem
    apply hv₀ne
    calc k₁ * v₀ = (k₁ * v₀ * k₁⁻¹ * v₀⁻¹) * v₀ * k₁ := by group
      _ = v₀ * k₁ := by rw [hmem]; group
  have hconj_gen : ∀ v ∈ blockU K,
      y * (k₁ * v * k₁⁻¹ * v⁻¹) * y⁻¹ ∈ commSub k₁ (blockU K) := by
    intro v hv
    have hv'V : y * v * y⁻¹ ∈ blockU K := hVy v hv
    have huV : k₁⁻¹ * (y * v * y⁻¹) * k₁ ∈ blockU K := hk₁Vinv _ hv'V
    have h1 : y * (k₁ * v * k₁⁻¹ * v⁻¹) * y⁻¹ =
        (k₁⁻¹ * (y * v * y⁻¹) * k₁) * (y * v * y⁻¹)⁻¹ := by
      calc y * (k₁ * v * k₁⁻¹ * v⁻¹) * y⁻¹
          = ((y * k₁ * y⁻¹) * (y * v * y⁻¹) * (y * k₁ * y⁻¹)⁻¹) * (y * v * y⁻¹)⁻¹ := by group
        _ = (k₁⁻¹ * (y * v * y⁻¹) * k₁) * (y * v * y⁻¹)⁻¹ := by rw [hinv _ hv'V]
    have h2 : (k₁⁻¹ * (y * v * y⁻¹) * k₁) * (y * v * y⁻¹)⁻¹ =
        (k₁ * (k₁⁻¹ * (y * v * y⁻¹) * k₁) * k₁⁻¹ * (k₁⁻¹ * (y * v * y⁻¹) * k₁)⁻¹)⁻¹ := by
      group
    rw [h1, h2]
    exact (commSub k₁ (blockU K)).inv_mem (hgen _ huV)
  have hconj : ∀ w ∈ commSub k₁ (blockU K), y * w * y⁻¹ ∈ commSub k₁ (blockU K) := by
    intro w hw
    refine Subgroup.closure_induction (p := fun w _ => y * w * y⁻¹ ∈ commSub k₁ (blockU K))
      ?_ ?_ ?_ ?_ hw
    · rintro _ ⟨v, hv, rfl⟩
      exact hconj_gen v hv
    · simp
    · intro a b _ _ ha hb
      have : y * (a * b) * y⁻¹ = (y * a * y⁻¹) * (y * b * y⁻¹) := by group
      rw [this]
      exact (commSub k₁ (blockU K)).mul_mem ha hb
    · intro a _ ha
      have : y * a⁻¹ * y⁻¹ = (y * a * y⁻¹)⁻¹ := by group
      rw [this]
      exact (commSub k₁ (blockU K)).inv_mem ha
  have hle : (commSub k₁ (blockU K)).map (MulAut.conj y).toMonoidHom ≤ commSub k₁ (blockU K) := by
    rintro _ ⟨w, hw, rfl⟩
    exact hconj w hw
  have hcard : Nat.card ((commSub k₁ (blockU K)).map (MulAut.conj y).toMonoidHom) =
      Nat.card (commSub k₁ (blockU K)) := Subgroup.card_map_of_injective (MulAut.conj y).injective
  have heq : (commSub k₁ (blockU K)).map (MulAut.conj y).toMonoidHom = commSub k₁ (blockU K) :=
    Subgroup.eq_of_le_of_card_ge hle (le_of_eq hcard.symm)
  have hyV₀ : y ∈ Subgroup.normalizer (commSub k₁ (blockU K) : Set G) := by
    rw [Subgroup.mem_normalizer_iff]
    intro h
    constructor
    · intro hh
      exact hconj h hh
    · intro hh
      have hmem : y * h * y⁻¹ ∈ (commSub k₁ (blockU K)).map (MulAut.conj y).toMonoidHom := by
        rw [heq]; exact hh
      obtain ⟨w, hw, hwh⟩ := hmem
      have hwh' : y * w * y⁻¹ = y * h * y⁻¹ := hwh
      have : w = h := by
        have := mul_left_cancel (mul_right_cancel hwh')
        exact this
      rwa [← this]
  have hV₀2 : IsPGroup 2 (commSub k₁ (blockU K)) := (hK.isPGroup_blockU).to_le hV₀V
  have h2dvd : 2 ∣ Nat.card (commSub k₁ (blockU K)) := by
    rcases hV₀2.card_eq_or_dvd with h1 | h1
    · exact absurd ((Subgroup.eq_bot_iff_card _).2 h1) hV₀ne
    · exact h1
  obtain ⟨a, haV₀, ha1, hay⟩ := exists_fixed_ne_one_of_two_element h2dvd hyV₀ hn
  refine ⟨a, hV₀V haV₀, hay.symm, ?_⟩
  by_contra hcon
  push Not at hcon
  have hBV : Subgroup.zpowers k₁ ≤ Subgroup.normalizer (blockU K : Set G) :=
    Subgroup.zpowers_le.2 (le_normalizer_blockU K hk₁)
  have hcop : Nat.Coprime (Nat.card (Subgroup.zpowers k₁)) (Nat.card (blockU K)) := by
    obtain ⟨j, hj⟩ := (hK.isPGroup_blockU).exists_card_eq
    have hB' : Nat.card (Subgroup.zpowers k₁) ∣ p ^ m := by
      rw [Nat.card_zpowers]
      exact orderOf_dvd_of_pow_eq_one hk₁p
    obtain ⟨i, -, hi⟩ := (Nat.dvd_prime_pow hp).1 hB'
    rw [hi, hj]
    exact Nat.Coprime.pow i j ((Nat.coprime_primes hp Nat.prime_two).2 hp2)
  have hbot := CFSG.RankThree.Coprime.commutator_inf_centralizer_eq_bot hK.blockU_comm hBV hcop
  have haB : a ∈ ⁅Subgroup.zpowers k₁, blockU K⁆ := by
    have hsub : commSub k₁ (blockU K) ≤ ⁅Subgroup.zpowers k₁, blockU K⁆ := by
      refine (Subgroup.closure_le _).2 ?_
      rintro _ ⟨v, hv, rfl⟩
      exact Subgroup.commutator_mem_commutator (Subgroup.mem_zpowers k₁) hv
    exact hsub haV₀
  have haC : a ∈ Subgroup.centralizer (Subgroup.zpowers k₁ : Set G) := by
    have hle' : Subgroup.zpowers k₁ ≤ Subgroup.centralizer ({a} : Set G) := by
      refine Subgroup.zpowers_le.2 ?_
      exact Subgroup.mem_centralizer_singleton_iff.2 (hcon k₁ hk₁).symm
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    exact Subgroup.mem_centralizer_singleton_iff.1 (hle' hh)
  have : a ∈ (⊥ : Subgroup G) := hbot ▸ Subgroup.mem_inf.2 ⟨haB, haC⟩
  exact ha1 (Subgroup.mem_bot.1 this)

theorem mem_of_odd_order {Γ : Type*} [Group Γ] {Kh : Subgroup Γ} [Kh.Normal] {a : Γ}
    (ha : a * a = 1) {c : Γ} (hc : ∃ j : ℤ, ∃ κ ∈ Kh, c = a ^ j * κ) {p : ℕ} (hp : Odd p)
    (hcp : c ^ p = 1) : c ∈ Kh := by
  obtain ⟨j, κ, hκ, rfl⟩ := hc
  have ha2 : a ^ (2 : ℤ) = 1 := by rw [zpow_two]; exact ha
  rcases Int.even_or_odd j with ⟨i, hi⟩ | ⟨i, hi⟩
  · have : a ^ j = 1 := by
      rw [hi, ← two_mul, zpow_mul, ha2, one_zpow]
    rw [this, one_mul]
    exact hκ
  · have : a ^ j = a := by
      rw [hi, zpow_add_one, zpow_mul, ha2, one_zpow, one_mul]
    rw [this] at hcp ⊢
    have hcc : (a * κ) * (a * κ) ∈ Kh := by
      have hainv : a⁻¹ = a := inv_eq_of_mul_eq_one_right ha
      have : (a * κ) * (a * κ) = (a * κ * a⁻¹) * κ := by rw [hainv]; group
      rw [this]
      exact Kh.mul_mem (Subgroup.Normal.conj_mem inferInstance κ hκ a) hκ
    obtain ⟨m', hm'⟩ := hp
    have e : p + 1 = 2 * (m' + 1) := by omega
    have h1 : (a * κ) = ((a * κ) * (a * κ)) ^ (m' + 1) := by
      calc (a * κ) = (a * κ) ^ p * (a * κ) := by rw [hcp, one_mul]
        _ = (a * κ) ^ (p + 1) := (pow_succ _ _).symm
        _ = ((a * κ) * (a * κ)) ^ (m' + 1) := by rw [e, pow_mul, pow_two]
    rw [h1]
    exact Kh.pow_mem hcc _

theorem foote_normal_dichotomy {K : Subgroup G} (h : QBlock K) {A : Subgroup G} (hAK : A ≤ K)
    (hKA : K ≤ Subgroup.normalizer (A : Set G)) : K ≤ A ∨ ⁅A, K⁆ ≤ oTwoIn K := by
  have hAn : (A.subgroupOf K).Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hAK).2 hKA
  have hNn := hAn.map (QBlock.topHom K) QBlock.topHom_surjective
  rcases LocalCores.quasisimple_normal_subgroups h.quasisimple hNn with htop | hcen
  · exact Or.inl (h.le_of_map_top hAK hKA htop)
  · right
    refine Subgroup.commutator_le.2 fun a ha g hg => ?_
    have hmem : QBlock.topHom K ⟨a, hAK ha⟩ ∈ Subgroup.center (↥K ⧸ pCore 2 ↥K) :=
      hcen ⟨⟨a, hAK ha⟩, Subgroup.mem_subgroupOf.2 ha, rfl⟩
    have h1 : QBlock.topHom K ⟨⁅a, g⁆, h.commutator_mem (hAK ha) hg⟩ = 1 := by
      rw [h.topHom_commutator (hAK ha) hg]
      exact commutatorElement_eq_one_iff_mul_comm.2
        (Subgroup.mem_center_iff.1 hmem (QBlock.topHom K ⟨g, hg⟩)).symm
    exact QBlock.topHom_eq_one_iff.1 h1

theorem footeTheoremA : FooteTheoremA := by
  intro G _ _ K hK y hyK hy2' hy2
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨n, hn⟩ := hy2'
  have hKV : K ≤ Subgroup.normalizer (blockU K : Set G) := le_normalizer_blockU K
  have hyV : y ∈ Subgroup.normalizer (blockU K : Set G) := by
    rw [Subgroup.mem_normalizer_iff]
    intro u
    refine ⟨fun hu => conj_mem_blockU hyK hu, fun hu => ?_⟩
    have := conj_mem_blockU (inv_mem hyK) hu
    simpa [mul_assoc] using this
  set H : Subgroup G := Subgroup.zpowers y ⊔ K with hHdef
  have hKH : K ≤ H := le_sup_right
  have hyH : y ∈ H := Subgroup.mem_sup_left (Subgroup.mem_zpowers y)
  have hHV : H ≤ Subgroup.normalizer (blockU K : Set G) :=
    sup_le (Subgroup.zpowers_le.2 hyV) hKV
  have hHK : H ≤ Subgroup.normalizer (K : Set G) :=
    sup_le (Subgroup.zpowers_le.2 hyK) Subgroup.le_normalizer
  have hmulH : ∀ h ∈ H, ∃ j : ℤ, ∃ k ∈ K, h = y ^ j * k := by
    intro h hh
    have hset := Subgroup.coe_mul_of_left_le_normalizer_right (Subgroup.zpowers y) K
      (Subgroup.zpowers_le.2 hyK)
    have hh' : h ∈ ((Subgroup.zpowers y ⊔ K : Subgroup G) : Set G) := hh
    rw [hset] at hh'
    obtain ⟨a, ha, k, hk, rfl⟩ := Set.mem_mul.1 hh'
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.1 ha
    exact ⟨j, k, hk, rfl⟩
  let ρ : ↥H →* MulAut ↥(blockU K) :=
    (Subgroup.normalizerMonoidHom (blockU K)).comp (Subgroup.inclusion hHV)
  have hρ : ∀ (h : ↥H) (v : ↥(blockU K)), ((ρ h v : ↥(blockU K)) : G) = h * v * (h : G)⁻¹ :=
    fun h v => Subgroup.normalizerMonoidHom_apply_apply_coe (blockU K) (Subgroup.inclusion hHV h) v
  have hρ1 : ∀ h : ↥H, ρ h = 1 ↔ ∀ v ∈ blockU K, (h : G) * v = v * (h : G) := by
    intro h
    constructor
    · intro h1 v hv
      have e := hρ h ⟨v, hv⟩
      rw [h1] at e
      have e' : (h : G) * v * (h : G)⁻¹ = v := e.symm
      calc (h : G) * v = (h : G) * v * (h : G)⁻¹ * (h : G) := by group
        _ = v * h := by rw [e']
    · intro hc
      refine MulEquiv.ext fun v => Subtype.ext ?_
      rw [hρ]
      show (h : G) * v * (h : G)⁻¹ = v
      calc (h : G) * v * (h : G)⁻¹ = v * h * (h : G)⁻¹ := by rw [hc v v.2]
        _ = v := by group
  let π : ↥H →* ↥H ⧸ ρ.ker := QuotientGroup.mk' ρ.ker
  have hπ : ∀ a b : ↥H, π a = π b ↔ ρ a = ρ b := by
    intro a b
    constructor
    · intro h1
      have := QuotientGroup.eq.1 h1
      rw [MonoidHom.mem_ker, map_mul, map_inv, inv_mul_eq_one] at this
      exact this
    · intro h1
      apply QuotientGroup.eq.2
      rw [MonoidHom.mem_ker, map_mul, map_inv, h1, inv_mul_cancel]
  have hπ1 : ∀ a : ↥H, π a = 1 ↔ ρ a = 1 := fun a => by
    rw [← map_one π, hπ, map_one]
  have hyy : π ⟨y, hyH⟩ * π ⟨y, hyH⟩ = 1 := by
    rw [← map_mul, hπ1, hρ1]
    intro v hv
    have := Subgroup.mem_centralizer_iff.1 hy2 v hv
    exact this.symm
  let ι : ↥K →* ↥H ⧸ ρ.ker := π.comp (Subgroup.inclusion hKH)
  have hιπ : ∀ k : ↥K, ι k = π ⟨(k : G), hKH k.2⟩ := fun k => rfl
  set P : Subgroup (↥H ⧸ ρ.ker) := CFSG.pCore 2 (↥H ⧸ ρ.ker) with hPdef
  have hPn : P.Normal := CFSG.pCore_normal
  set Kh : Subgroup (↥H ⧸ ρ.ker) := ι.range with hKhdef
  have hKhn : Kh.Normal := ⟨fun x hx g => by
    obtain ⟨k, rfl⟩ := hx
    obtain ⟨h, rfl⟩ := QuotientGroup.mk_surjective g
    have hkh : (h : G) * (k : G) * (h : G)⁻¹ ∈ K :=
      (Subgroup.mem_normalizer_iff.1 (hHK h.2) (k : G)).1 k.2
    refine ⟨⟨(h : G) * (k : G) * (h : G)⁻¹, hkh⟩, ?_⟩
    have e : (⟨(h : G) * (k : G) * (h : G)⁻¹, hKH hkh⟩ : ↥H) =
        h * ⟨(k : G), hKH k.2⟩ * h⁻¹ := Subtype.ext (by simp)
    show π ⟨(h : G) * (k : G) * (h : G)⁻¹, hKH hkh⟩ = _
    rw [e, map_mul, map_mul, map_inv]
    rfl⟩
  have hKperf : Group.IsPerfect ↥K := Subgroup.isPerfect_iff.2 hK.perfect
  by_cases hyP : π ⟨y, hyH⟩ ∈ P
  ·
    refine exists_fixed_of_comm hK hyK hy2 ?_
    have hperf : ⁅Kh, Kh⁆ = Kh := by
      have h1 : Kh = (⊤ : Subgroup ↥K).map ι := MonoidHom.range_eq_map ι
      have h2 : ⁅(⊤ : Subgroup ↥K), (⊤ : Subgroup ↥K)⁆ = (⊤ : Subgroup ↥K) := by
        have := hKperf.commutator_eq_top
        rwa [_root_.commutator_def] at this
      rw [h1, ← Subgroup.map_commutator, h2]
    have hQ : ⁅P ⊓ Kh, Kh⁆ = ⊥ := by
      let A : Subgroup G := (P.comap ι).map K.subtype
      have hAK : A ≤ K := by
        rintro _ ⟨a, -, rfl⟩
        exact a.2
      have hconjA : ∀ k ∈ K, ∀ a ∈ A, k * a * k⁻¹ ∈ A := by
        intro k hk a ha
        obtain ⟨a', ha', rfl⟩ := ha
        refine ⟨⟨k, hk⟩ * a' * ⟨k, hk⟩⁻¹, ?_, by simp⟩
        show ι (⟨k, hk⟩ * a' * ⟨k, hk⟩⁻¹) ∈ P
        rw [map_mul, map_mul, map_inv]
        exact hPn.conj_mem _ ha' _
      have hKA : K ≤ Subgroup.normalizer (A : Set G) := by
        intro k hk
        rw [Subgroup.mem_normalizer_iff]
        intro x
        refine ⟨fun hx => hconjA k hk x hx, fun hx => ?_⟩
        have := hconjA k⁻¹ (K.inv_mem hk) _ hx
        have e : k⁻¹ * (k * x * k⁻¹) * k⁻¹⁻¹ = x := by group
        rwa [e] at this
      rcases foote_normal_dichotomy hK hAK hKA with hKA' | hcomm
      · exfalso
        have hιP : ∀ k : ↥K, ι k ∈ P := by
          intro k
          obtain ⟨a', ha', hak⟩ := hKA' k.2
          have : a' = k := Subtype.ext hak
          rw [← this]
          exact ha'
        let ψ : ↥K →* ↥P := ι.codRestrict P hιP
        have hnil : Group.IsNilpotent ↥P :=
          (CFSG.pCore_isPGroup (p := 2) (G := ↥H ⧸ ρ.ker)).isNilpotent
        have hψ : ∀ k, ψ k = 1 := fun k => hom_eq_one_of_perfect_of_solvable ψ k
        have hι1 : ∀ k : ↥K, ι k = 1 := fun k => congrArg Subtype.val (hψ k)
        have hKV' : ∀ k ∈ K, ∀ v ∈ blockU K, k * v = v * k := by
          intro k hk v hv
          exact (hρ1 _).1 ((hπ1 _).1 (hι1 ⟨k, hk⟩)) v hv
        have hbot : ⁅blockU K, K⁆ = ⊥ := by
          refine eq_bot_iff.2 (Subgroup.commutator_le.2 fun v hv k hk => ?_)
          rw [Subgroup.mem_bot]
          exact commutatorElement_eq_one_iff_mul_comm.2 (hKV' k hk v hv).symm
        rw [hK.blockU_stable] at hbot
        exact blockU_ne_bot_of_short hK.short hbot
      · refine eq_bot_iff.2 (Subgroup.commutator_le.2 fun x hx g hg => ?_)
        obtain ⟨a, rfl⟩ := hx.2
        obtain ⟨b, rfl⟩ := hg
        have haA : (a : G) ∈ A := ⟨a, hx.1, rfl⟩
        have hbK : (b : G) ∈ K := b.2
        have h1 : ⁅(a : G), (b : G)⁆ ∈ oTwoIn K :=
          hcomm (Subgroup.commutator_mem_commutator haA hbK)
        have h2 : ∀ v ∈ blockU K, (⁅(a : G), (b : G)⁆) * v = v * ⁅(a : G), (b : G)⁆ :=
          fun v hv => (Subgroup.mem_centralizer_iff.1 (hK.oTwoIn_le_centralizer h1) v hv).symm
        have h3 : ρ (Subgroup.inclusion hKH ⁅a, b⁆) = 1 := by
          rw [hρ1]
          intro v hv
          have e : ((Subgroup.inclusion hKH ⁅a, b⁆ : ↥H) : G) = ⁅(a : G), (b : G)⁆ := by
            simp [commutatorElement_def]
          rw [e]
          exact h2 v hv
        rw [Subgroup.mem_bot, ← map_commutatorElement]
        exact (hπ1 _).2 h3
    have hKP : ⁅Kh, P⁆ = ⊥ := centralizes_of_central_commutators hperf hQ
    intro k hk v hv
    have hmem : ⁅ι ⟨k, hk⟩, π ⟨y, hyH⟩⁆ ∈ ⁅Kh, P⁆ :=
      Subgroup.commutator_mem_commutator ⟨⟨k, hk⟩, rfl⟩ hyP
    rw [hKP, Subgroup.mem_bot] at hmem
    have hc1 : π ⁅(⟨y, hyH⟩ : ↥H), ⟨k, hKH hk⟩⁆ = 1 := by
      rw [map_commutatorElement]
      exact commutatorElement_eq_one_iff_mul_comm.2
        (commutatorElement_eq_one_iff_mul_comm.1 hmem).symm
    have := (hρ1 _).1 ((hπ1 _).1 hc1) v hv
    have e : ((⁅(⟨y, hyH⟩ : ↥H), ⟨k, hKH hk⟩⁆ : ↥H) : G) = ⁅y, k⁆ := by
      simp [commutatorElement_def]
    rwa [e] at this
  ·
    have hnot : ∃ g : ↥H ⧸ ρ.ker, ¬ IsPGroup 2 (Subgroup.closure
        ({π ⟨y, hyH⟩, g * π ⟨y, hyH⟩ * g⁻¹} : Set (↥H ⧸ ρ.ker))) := by
      by_contra hcon
      push Not at hcon
      exact hyP ((CFSG.BaerSuzuki.baer_suzuki_iff (p := 2) (π ⟨y, hyH⟩)).2 hcon)
    obtain ⟨g, hg⟩ := hnot
    have hb : (g * π ⟨y, hyH⟩ * g⁻¹) * (g * π ⟨y, hyH⟩ * g⁻¹) = 1 := by
      calc (g * π ⟨y, hyH⟩ * g⁻¹) * (g * π ⟨y, hyH⟩ * g⁻¹)
          = g * (π ⟨y, hyH⟩ * π ⟨y, hyH⟩) * g⁻¹ := by group
        _ = 1 := by rw [hyy]; group
    obtain ⟨c, p, hp, hp2, hcp, hinvc⟩ := exists_odd_prime_inverted hyy hb hg
    have hp' : Odd p := hp.odd_of_ne_two hp2
    have hcp1 : c ^ p = 1 := by rw [← hcp]; exact pow_orderOf_eq_one c
    obtain ⟨h₂, rfl⟩ := QuotientGroup.mk_surjective c
    have hcK : (QuotientGroup.mk h₂ : ↥H ⧸ ρ.ker) ∈ Kh := by
      obtain ⟨j, k, hk, hh₂⟩ := hmulH h₂ h₂.2
      refine mem_of_odd_order (Kh := Kh) (a := π ⟨y, hyH⟩) hyy
        ⟨j, ι ⟨k, hk⟩, ⟨⟨k, hk⟩, rfl⟩, ?_⟩ hp' hcp1
      have : h₂ = (⟨y, hyH⟩ : ↥H) ^ j * ⟨k, hKH hk⟩ := Subtype.ext (by simpa using hh₂)
      show π h₂ = _
      rw [this, map_mul, map_zpow]
      rfl
    have : Fact p.Prime := ⟨hp⟩
    obtain ⟨k₁, hk₁c, m, hk₁m⟩ := exists_lift_primePower ι hcK (s := 1)
      (by rw [pow_one]; exact hcp1)
    have hk₁K : (k₁ : G) ∈ K := k₁.2
    have hk₁p : (k₁ : G) ^ p ^ m = 1 := by
      have := congrArg Subtype.val hk₁m
      simpa using this
    have hnt : ∃ v ∈ blockU K, (k₁ : G) * v ≠ v * (k₁ : G) := by
      by_contra hcon
      push Not at hcon
      have h1 : ρ (Subgroup.inclusion hKH k₁) = 1 := (hρ1 _).2 fun v hv => hcon v hv
      have h2 : ι k₁ = 1 := (hπ1 _).2 h1
      have h3 : (QuotientGroup.mk h₂ : ↥H ⧸ ρ.ker) = 1 := hk₁c.symm.trans h2
      rw [h3, orderOf_one] at hcp
      have := hp.one_lt
      omega
    have hinv : ∀ v ∈ blockU K,
        (y * (k₁ : G) * y⁻¹) * v * (y * (k₁ : G) * y⁻¹)⁻¹ = (k₁ : G)⁻¹ * v * (k₁ : G) := by
      intro v hv
      have h1 : π ((⟨y, hyH⟩ : ↥H) * Subgroup.inclusion hKH k₁ * (⟨y, hyH⟩ : ↥H)⁻¹) =
          π (Subgroup.inclusion hKH k₁)⁻¹ := by
        rw [map_mul, map_mul, map_inv, map_inv]
        have : π (Subgroup.inclusion hKH k₁) = QuotientGroup.mk h₂ := hk₁c
        rw [this]
        exact hinvc
      have h2 := (hπ _ _).1 h1
      have h3 := congrArg (fun φ : MulAut ↥(blockU K) => ((φ ⟨v, hv⟩ : ↥(blockU K)) : G)) h2
      simp only [hρ] at h3
      simpa using h3
    exact exists_fixed_of_odd hK hyK hn hk₁K hp hp2 hk₁p hnt hinv

end CFSG.CGT.PushingUpLit.LIT.Foote
