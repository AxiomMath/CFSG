module

public import CFSG.RankThree.PartOne.S12.PushingUp
import CFSG.LocalAnalysis.AGLEmbedding.AscEightFive
import CFSG.CGT.PushingUpLit.BHS7.BorelMax
import CFSG.ThirdParty.QiuzhenCFSG.Glauberman.DicksonSplitTorusMatrices
public import CFSG.LocalAnalysis.QuasithinUnique.Defs
import CFSG.LocalAnalysis.QuasithinUnique.EscapingLocalAux
import CFSG.Quasithin.Background.B6Sections

public section

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique
open scoped commutatorElement

namespace CFSG.AGLEmbedding

namespace AscEightSix

variable {G : Type} [Group G] [Finite G] {X S L : Subgroup G}

section SL2Torus

open Matrix CFSG.QuasithinUnique.Setup.Campbell
open scoped LinearAlgebra.Projectivization

omit [Finite G] in
theorem exists_two_pow_odd_orderOf_pow {M : Type*} [Group M] [Finite M] (x : M) :
    ∃ a : ℕ, Odd (orderOf (x ^ 2 ^ a)) := by
  obtain ⟨a, m, hm, hn⟩ := Nat.exists_eq_two_pow_mul_odd (n := orderOf x)
    (orderOf_pos x).ne'
  refine ⟨a, ?_⟩
  rw [orderOf_pow' x (by positivity), hn, Nat.gcd_mul_right_left, Nat.mul_div_cancel_left _
    (by positivity)]
  exact hm

omit [Finite G] in
theorem pow_two_pow_ne_one_of_odd {M : Type*} [Monoid M] {g : M} (hg : g ≠ 1)
    (hodd : Odd (orderOf g)) (a : ℕ) : g ^ 2 ^ a ≠ 1 := by
  intro h
  have hd : orderOf g ∣ 2 ^ a := orderOf_dvd_of_pow_eq_one h
  obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hd
  rcases k with _ | k
  · rw [pow_zero] at hk
    exact hg (orderOf_eq_one_iff.mp hk)
  · rw [hk] at hodd
    exact (Nat.not_odd_iff_even.mpr (Nat.even_pow.mpr ⟨even_two, by omega⟩)) hodd

omit [Finite G] in
theorem exists_odd_fix {F : Type} [Field F] [Fintype F] [CharP F 2] (hF : 4 ≤ Fintype.card F)
    (ℓ : ℙ F (Fin 2 → F)) :
    ∃ g : SpecialLinearGroup (Fin 2) F, g • ℓ = ℓ ∧ g ≠ 1 ∧ Odd (orderOf g) := by
  classical
  obtain ⟨t, ht0, ht1⟩ : ∃ t : F, t ≠ 0 ∧ t ≠ 1 := by
    by_contra h
    push Not at h
    have hsub : (Finset.univ : Finset F) ⊆ {0, 1} := by
      intro t _
      by_cases ht : t = 0
      · simp [ht]
      · simp [h t ht]
    have h1 := Finset.card_le_card hsub
    rw [Finset.card_univ] at h1
    have h2 : ({0, 1} : Finset F).card ≤ 2 := Finset.card_le_two
    omega
  set u : Fˣ := Units.mk0 t ht0 with hu
  set d := CFSG.Glauberman.Dickson.splitTorusSLHom F u with hd
  have hdeq : d = Matrix.SpecialLinearGroup.diag2 t ht0 := by
    apply Subtype.ext
    rw [Matrix.SpecialLinearGroup.diag2_coe']
    simp [hd, u]
  have hd0 : d • (pt0 : ℙ F (Fin 2 → F)) = pt0 := by
    unfold pt0
    rw [Projectivization.smul_mk, Projectivization.mk_eq_mk_iff]
    refine ⟨u, ?_⟩
    rw [hdeq]
    erw [Matrix.SpecialLinearGroup.diag2_smul_single_i₁]
    rfl
  have hd1 : d ≠ 1 := by
    intro h
    have := congrArg (fun g : SpecialLinearGroup (Fin 2) F => (g : Matrix (Fin 2) (Fin 2) F) 0 0) h
    simp [hd, u] at this
    exact ht1 this
  have hdodd : Odd (orderOf d) := by
    have hinj : Function.Injective (CFSG.Glauberman.Dickson.splitTorusSLHom F) := by
      intro a b hab
      have := congrArg (fun g : SpecialLinearGroup (Fin 2) F =>
        (g : Matrix (Fin 2) (Fin 2) F) 0 0) hab
      simp at this
      exact Units.ext this
    rw [hd, orderOf_injective _ hinj u]
    have hdvd : orderOf u ∣ Fintype.card Fˣ := orderOf_dvd_card
    rw [Fintype.card_units] at hdvd
    obtain ⟨n, hp, hn⟩ := FiniteField.card F 2
    have hq : Even (Fintype.card F) := by
      rw [hn]
      exact (Nat.even_pow.mpr ⟨even_two, n.pos.ne'⟩)
    have hodd' : Odd (Fintype.card F - 1) := by
      obtain ⟨k, hk⟩ := hq
      exact ⟨k - 1, by omega⟩
    exact Odd.of_dvd_nat hodd' hdvd
  obtain ⟨s, hs⟩ := exists_smul_pt0 ℓ
  refine ⟨s * d * s⁻¹, ?_, ?_, ?_⟩
  · rw [← hs]
    have h1 : s⁻¹ • s • (pt0 : ℙ F (Fin 2 → F)) = pt0 := inv_smul_smul s pt0
    simp only [mul_smul]
    erw [h1, hd0]
  · intro h
    apply hd1
    have : d = s⁻¹ * (s * d * s⁻¹) * s := by group
    rw [this, h]
    group
  · have h := orderOf_injective (MulAut.conj s).toMonoidHom (MulAut.conj s).injective d
    rw [← h] at hdodd
    simpa [MulAut.conj_apply] using hdodd

end SL2Torus

open scoped LinearAlgebra.Projectivization in
theorem exists_odd_normalizer_sl {E T : Subgroup G} {F : Type} [Field F] [Fintype F] [CharP F 2]
    (hF : 4 ≤ Fintype.card F) (hT : IsSylowTwoOf T E)
    (π : ↥E →* Matrix.SpecialLinearGroup (Fin 2) F) (hπ : Function.Surjective π)
    (hker : π.ker ≤ T.subgroupOf E) :
    ∃ x : ↥E, (x : G) ∈ Subgroup.normalizer (T : Set G) ∧ Odd (orderOf x) ∧ π x ≠ 1 := by
  obtain ⟨ℓ, hℓ⟩ := CFSG.CGT.PushingUpLit.BHS.exists_rootGrp_eq_map_of_isSylowTwoOf hT π hπ
  obtain ⟨g, hgℓ, hg1, hgodd⟩ := exists_odd_fix hF ℓ
  obtain ⟨x₀, hx₀⟩ := hπ g
  have hx₀N : (x₀ : G) ∈ Subgroup.normalizer (T : Set G) := by
    refine (CFSG.CGT.PushingUpLit.BHS7.mem_normalizer_iff_smul_eq π hπ hT.1 hker hℓ x₀).mpr ?_
    rw [hx₀]
    exact hgℓ
  obtain ⟨a, ha⟩ := exists_two_pow_odd_orderOf_pow x₀
  refine ⟨x₀ ^ 2 ^ a, ?_, ha, ?_⟩
  · have := Subgroup.pow_mem _ hx₀N (2 ^ a)
    simpa using this
  · rw [map_pow, hx₀]
    exact pow_two_pow_ne_one_of_odd hg1 hgodd a

omit [Finite G] in
theorem not_commutator_le_of_center {E : Subgroup G}
    (hc : ∀ z : ↥E ⧸ CFSG.pCore 2 ↥E, (∀ w, z * w = w * z) → z = 1) {x : ↥E}
    (hx : QuotientGroup.mk' (CFSG.pCore 2 ↥E) x ≠ 1) :
    ¬ ⁅Subgroup.zpowers (x : G), E⁆ ≤ pCoreOf 2 E := by
  intro h
  apply hx
  apply hc
  intro w
  induction w using QuotientGroup.induction_on with
  | H e =>
    have hm : ⁅(x : G), (e : G)⁆ ∈ pCoreOf 2 E :=
      h (Subgroup.commutator_mem_commutator (Subgroup.mem_zpowers _) e.2)
    obtain ⟨y, hy, hye⟩ := hm
    have hy' : ⁅x, e⁆ ∈ CFSG.pCore 2 ↥E := by
      have : y = ⁅x, e⁆ := Subtype.ext (by simpa [commutatorElement_def] using hye)
      rw [← this]; exact hy
    have h1 : QuotientGroup.mk' (CFSG.pCore 2 ↥E) ⁅x, e⁆ = 1 :=
      (QuotientGroup.eq_one_iff _).mpr hy'
    rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm] at h1
    exact h1

omit [Finite G] in
theorem sl2_central_eq_one {F : Type} [Field F] [CharP F 2]
    (z : Matrix.SpecialLinearGroup (Fin 2) F) (hz : ∀ w, z * w = w * z) : z = 1 := by
  have hmem : z ∈ Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) F) :=
    Subgroup.mem_center_iff.mpr fun w => (hz w).symm
  obtain ⟨r, hr, hrz⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp hmem
  rw [Fintype.card_fin] at hr
  have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
  have hr1 : r = 1 := by
    have h3 : (r - 1) ^ 2 = 0 := by linear_combination hr - (r - 1) * h2
    exact sub_eq_zero.mp (pow_eq_zero_iff two_ne_zero |>.mp h3)
  apply Subtype.ext
  rw [← hrz, hr1]
  simp

omit [Finite G] in
theorem alt_central_eq_one {m : ℕ} (hm : 2 ≤ m) (z : alternatingGroup (Fin (2 * m + 1)))
    (hz : ∀ w, z * w = w * z) : z = 1 := by
  have hmem : z ∈ Subgroup.center (alternatingGroup (Fin (2 * m + 1))) :=
    Subgroup.mem_center_iff.mpr fun w => (hz w).symm
  rw [alternatingGroup.center_eq_bot (by simp; omega)] at hmem
  exact hmem

omit [Finite G] in
theorem central_eq_one_of_mulEquiv {A B : Type*} [Group A] [Group B] (φ : A ≃* B)
    (h : ∀ z : B, (∀ w, z * w = w * z) → z = 1) (z : A) (hz : ∀ w, z * w = w * z) : z = 1 := by
  have : φ z = 1 := h (φ z) fun w => by
    obtain ⟨v, rfl⟩ := φ.surjective w
    rw [← map_mul, ← map_mul, hz v]
  simpa using this

theorem exists_odd_of_sl {E : Subgroup G} (hSE : IsSylowTwoOf (S ⊓ E) E) {n : ℕ} (hn : 2 ≤ n)
    (hnat : CFSG.RankThree.PartOne.IsNaturalSLTwoModule ↥E n) :
    ∃ x : ↥E, (x : G) ∈ Subgroup.normalizer ((S ⊓ E : Subgroup G) : Set G) ∧
      Odd (orderOf x) ∧ ¬ ⁅Subgroup.zpowers (x : G), E⁆ ≤ pCoreOf 2 E := by
  obtain ⟨φ, -⟩ := hnat
  set π : ↥E →* Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 n) :=
    φ.toMonoidHom.comp (QuotientGroup.mk' (CFSG.pCore 2 ↥E)) with hπdef
  have hπ : Function.Surjective π := φ.surjective.comp (QuotientGroup.mk'_surjective _)
  have hker : π.ker ≤ (S ⊓ E).subgroupOf E := by
    intro y hy
    have hy1 : QuotientGroup.mk' (CFSG.pCore 2 ↥E) y = 1 := by
      apply φ.injective
      rw [map_one]
      exact hy
    have hy' : y ∈ CFSG.pCore 2 ↥E := (QuotientGroup.eq_one_iff y).mp hy1
    have hyQ : (y : G) ∈ pCoreOf 2 E := ⟨y, hy', rfl⟩
    exact CFSG.QuasithinUnique.EscapingLocal.pCoreOf_le_of_isSylowTwoOf hSE hyQ
  let _ : Fintype (GaloisField 2 n) := Fintype.ofFinite _
  have hF : 4 ≤ Fintype.card (GaloisField 2 n) := by
    rw [← Nat.card_eq_fintype_card, GaloisField.card 2 n (by omega)]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  obtain ⟨x, hxN, hxodd, hx1⟩ := exists_odd_normalizer_sl hF hSE π hπ hker
  refine ⟨x, hxN, hxodd, not_commutator_le_of_center
    (central_eq_one_of_mulEquiv φ (sl2_central_eq_one)) ?_⟩
  intro h
  apply hx1
  show φ (QuotientGroup.mk' (CFSG.pCore 2 ↥E) x) = 1
  rw [h, map_one]

theorem exists_odd_of_alt {E C : Subgroup G} {m : ℕ} (hm : 2 ≤ m)
    (hnat : CFSG.RankThree.PartOne.IsNaturalAltModule ↥E m)
    (ι : ↥(((C ⊓ E).subgroupOf E).map (QuotientGroup.mk' (CFSG.pCore 2 ↥E))) ≃*
      alternatingGroup (Fin (2 * m))) :
    ∃ x : ↥E, (x : G) ∈ C ∧ Odd (orderOf x) ∧ ¬ ⁅Subgroup.zpowers (x : G), E⁆ ≤ pCoreOf 2 E := by
  obtain ⟨φ, -⟩ := hnat
  have h0 : (0 : ℕ) < 2 * m := by omega
  have h1 : (1 : ℕ) < 2 * m := by omega
  have h2 : (2 : ℕ) < 2 * m := by omega
  set a0 : Fin (2 * m) := ⟨0, h0⟩
  set a1 : Fin (2 * m) := ⟨1, h1⟩
  set a2 : Fin (2 * m) := ⟨2, h2⟩
  have h3c : (Equiv.swap a0 a1 * Equiv.swap a0 a2).IsThreeCycle :=
    Equiv.Perm.isThreeCycle_swap_mul_swap_same (by simp [a0, a1, Fin.ext_iff])
      (by simp [a0, a2, Fin.ext_iff]) (by simp [a1, a2, Fin.ext_iff])
  set c : alternatingGroup (Fin (2 * m)) := ⟨_, h3c.mem_alternatingGroup⟩ with hc
  have hc3 : orderOf c = 3 := by
    rw [← Subgroup.orderOf_coe]
    exact h3c.orderOf
  set y := ι.symm c with hy
  have hy3 : orderOf (y : ↥E ⧸ CFSG.pCore 2 ↥E) = 3 := by
    rw [Subgroup.orderOf_coe, hy, MulEquiv.orderOf_eq]
    exact hc3
  obtain ⟨e, he, hey⟩ := Subgroup.mem_map.mp y.2
  obtain ⟨k, hk⟩ := exists_two_pow_odd_orderOf_pow e
  have hy1 : (y : ↥E ⧸ CFSG.pCore 2 ↥E) ≠ 1 := by
    intro h; rw [h, orderOf_one] at hy3; omega
  have hyodd : Odd (orderOf (y : ↥E ⧸ CFSG.pCore 2 ↥E)) := by rw [hy3]; decide
  refine ⟨e ^ 2 ^ k, ?_, hk, not_commutator_le_of_center
    (central_eq_one_of_mulEquiv φ (alt_central_eq_one hm)) ?_⟩
  · have := Subgroup.pow_mem _ (Subgroup.mem_subgroupOf.mp he) (2 ^ k)
    simpa using this.1
  · rw [map_pow, hey]
    exact pow_two_pow_ne_one_of_odd hy1 hyodd k

omit [Finite G] in
theorem false_of_alt_one {E : Subgroup G} (hp : ⁅E, E⁆ = E)
    (hnat : CFSG.RankThree.PartOne.IsNaturalAltModule ↥E 1) : False := by
  obtain ⟨φ, -⟩ := hnat
  have hcard : Nat.card (alternatingGroup (Fin (2 * 1 + 1))) = 3 := by
    rw [Nat.card_eq_fintype_card, card_alternatingGroup]
    simp [Nat.factorial]
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hcyc : IsCyclic (alternatingGroup (Fin (2 * 1 + 1))) := isCyclic_of_prime_card hcard
  have hcomm : ∀ a b : alternatingGroup (Fin (2 * 1 + 1)), a * b = b * a := fun a b =>
    (IsCyclic.isMulCommutative (α := alternatingGroup (Fin (2 * 1 + 1)))).is_comm.comm a b
  have hc2 : ∀ a b : ↥E ⧸ CFSG.pCore 2 ↥E, a * b = b * a := fun a b =>
    φ.injective (by rw [map_mul, map_mul, hcomm])
  have hperf : commutator ↥E = ⊤ :=
    (AscEightFive.isPerfect_of_commutator_eq hp).commutator_eq_top
  have hq : commutator (↥E ⧸ CFSG.pCore 2 ↥E) = ⊤ := by
    rw [commutator_def, ← Subgroup.map_top_of_surjective _
      (QuotientGroup.mk'_surjective (CFSG.pCore 2 ↥E)), ← Subgroup.map_commutator,
      ← commutator_def, hperf, Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective _)]
  have hbot : commutator (↥E ⧸ CFSG.pCore 2 ↥E) = ⊥ := by
    rw [commutator_def]
    exact Subgroup.commutator_eq_bot_iff_le_centralizer.mpr fun a _ =>
      Subgroup.mem_centralizer_iff.mpr fun b _ => hc2 b a
  have hsub : Subsingleton (↥E ⧸ CFSG.pCore 2 ↥E) := by
    refine ⟨fun a b => ?_⟩
    have ha : a ∈ commutator (↥E ⧸ CFSG.pCore 2 ↥E) := hq ▸ Subgroup.mem_top a
    have hb : b ∈ commutator (↥E ⧸ CFSG.pCore 2 ↥E) := hq ▸ Subgroup.mem_top b
    rw [hbot, Subgroup.mem_bot] at ha hb
    rw [ha, hb]
  have h1 : Nat.card (↥E ⧸ CFSG.pCore 2 ↥E) = 3 := (Nat.card_congr φ.toEquiv).trans hcard
  have h2 : Nat.card (↥E ⧸ CFSG.pCore 2 ↥E) ≤ 1 := Finite.card_le_one_iff_subsingleton.mpr hsub
  omega

end AscEightSix

end CFSG.AGLEmbedding
