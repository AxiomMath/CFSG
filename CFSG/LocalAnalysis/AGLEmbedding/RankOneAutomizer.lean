module

public import CFSG.LocalAnalysis.AGLEmbedding.KFacts
public import CFSG.LocalAnalysis.AGLEmbedding.ConstrainedSLAux
public import CFSG.LocalAnalysis.AGLEmbedding.RankLemmas
public import CFSG.LinearAlgebra.LinearGroups.Perfect

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.Assembly.LowTwoRank Matrix

section Derived

variable {G H : Type*} [Group G] [Group H]

theorem map_secondDerived (f : G →* H) (A : Subgroup G) :
    (⁅⁅A, A⁆, ⁅A, A⁆⁆).map f = ⁅⁅A.map f, A.map f⁆, ⁅A.map f, A.map f⁆⁆ := by
  rw [Subgroup.map_commutator, Subgroup.map_commutator]

theorem secondDerived_mono {A B : Subgroup G} (h : A ≤ B) :
    ⁅⁅A, A⁆, ⁅A, A⁆⁆ ≤ ⁅⁅B, B⁆, ⁅B, B⁆⁆ :=
  Subgroup.commutator_mono (Subgroup.commutator_mono h h) (Subgroup.commutator_mono h h)

end Derived

section SL

open scoped MatrixGroups

open scoped commutatorElement in
theorem neg_one_mem_secondDerived_SL_three :
    (-1 : SL(2, ZMod 3)) ∈ ⁅commutator SL(2, ZMod 3), commutator SL(2, ZMod 3)⁆ := by
  obtain ⟨u, w, h⟩ : ∃ u w : SL(2, ZMod 3), ⁅⁅u, w⁆, ⁅u, u * w * u⁻¹⁆⁆ = -1 :=
    ⟨⟨!![1, 1; 0, 1], by decide⟩, ⟨!![1, 0; 1, 1], by decide⟩, by decide⟩
  rw [← h]
  exact Subgroup.commutator_mem_commutator
    (Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _))
    (Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _))

theorem neg_one_mem_secondDerived_SL {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) :
    (-1 : SL(2, ZMod p)) ∈ ⁅commutator SL(2, ZMod p), commutator SL(2, ZMod p)⁆ := by
  rcases eq_or_ne p 3 with rfl | hp3
  · exact neg_one_mem_secondDerived_SL_three
  · have hp4 : 4 ≤ (Finset.univ : Finset (ZMod p)).card := by
      rw [Finset.card_univ, ZMod.card]
      have := (Fact.out : p.Prime).two_le
      omega
    obtain ⟨s, -, hs⟩ := Finset.exists_subset_card_eq hp4
    have := CFSG.LinearGroups.special_linear_dimension_two_perfect ⟨s, hs⟩
    have htop : commutator SL(2, ZMod p) = ⊤ := Group.IsPerfect.commutator_eq_top
    rw [htop, ← commutator_def, htop]
    exact Subgroup.mem_top _

theorem neg_one_mem_secondDerived_statedSL {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) :
    (-1 : GL (Fin 2) (ZMod p)) ∈ ⁅⁅StatedSL 2 (ZMod p), StatedSL 2 (ZMod p)⁆,
      ⁅StatedSL 2 (ZMod p), StatedSL 2 (ZMod p)⁆⁆ := by
  have h := Subgroup.mem_map_of_mem SpecialLinearGroup.toGL (neg_one_mem_secondDerived_SL hp2)
  rw [commutator_def, map_secondDerived, ← MonoidHom.range_eq_map,
    ← statedSL_eq_range_toGL] at h
  convert h using 1
  ext i j
  simp [SpecialLinearGroup.coe_GL_coe_matrix]

theorem neg_one_pow_prime_pow_ne_one {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) (k : ℕ) :
    (-1 : GL (Fin 2) (ZMod p)) ^ (p ^ k) ≠ 1 := by
  rw [Odd.neg_one_pow ((Nat.Prime.odd_of_ne_two Fact.out hp2).pow)]
  intro h
  have h00 := congrArg
    (fun A : GL (Fin 2) (ZMod p) => (A : Matrix (Fin 2) (Fin 2) (ZMod p)) 0 0) h
  simp only [Units.val_neg, Units.val_one, Matrix.neg_apply, Matrix.one_apply_eq] at h00
  rw [neg_one_eq_one_iff, ZMod.ringChar_zmod_n] at h00
  exact hp2 h00

end SL

section Conj

variable {K : Type*} [Group K]

theorem mulAut_mul_conj_mul_inv (σ : MulAut K) (k : K) :
    σ * MulAut.conj k * σ⁻¹ = MulAut.conj (σ k) := by
  ext x
  simp [MulAut.mul_apply, MulAut.inv_apply, MulAut.conj_apply]

theorem mulAut_conj_injective (hZ : Subgroup.center K = ⊥) :
    Function.Injective (MulAut.conj : K →* MulAut K) := by
  refine (injective_iff_map_eq_one _).mpr fun k hk => ?_
  have hk' : k ∈ Subgroup.center K := Subgroup.mem_center_iff.mpr fun g => by
    have h := DFunLike.congr_fun hk g
    rw [MulAut.conj_apply, MulAut.one_apply] at h
    calc g * k = k * g * k⁻¹ * k := by rw [h]
      _ = k * g := by group
  rw [hZ] at hk'
  exact Subgroup.mem_bot.mp hk'

end Conj

section Image

variable {X : Type*} [Group X] {p : ℕ} {K : Subgroup X} [K.Normal] {E : Subgroup X}

theorem mk_eq_mk_iff_conjNormal_eq
    (hEC : E ⊓ Subgroup.centralizer (K : Set X) = (Subgroup.center E).map E.subtype) (u v : E) :
    (u : E ⧸ Subgroup.center E) = v ↔
      MulAut.conjNormal (H := K) (u : X) = MulAut.conjNormal (H := K) (v : X) := by
  rw [QuotientGroup.eq, ← Subgroup.mem_map_iff_mem E.subtype_injective, ← hEC,
    Subgroup.mem_inf, Subgroup.subtype_apply, and_iff_right (u⁻¹ * v).2,
    ← ker_conjNormal_eq_centralizer, MonoidHom.mem_ker, Subgroup.coe_mul, Subgroup.coe_inv,
    map_mul, map_inv, inv_mul_eq_one]

theorem isElemAbelian_map_conjNormal {n : ℕ} (hEexp : ∀ x ∈ E, x ^ p = 1)
    (hEC : E ⊓ Subgroup.centralizer (K : Set X) = (Subgroup.center E).map E.subtype)
    (e : E ⧸ Subgroup.center E ≃* Multiplicative (Fin n → ZMod p)) :
    IsElemAbelian p (E.map (MulAut.conjNormal (H := K))) := by
  refine ⟨isMulCommutative_iff.mpr fun a b => Subtype.ext ?_, fun y hy => ?_⟩
  · obtain ⟨x, hx, hxa⟩ := Subgroup.mem_map.mp a.2
    obtain ⟨y, hy, hyb⟩ := Subgroup.mem_map.mp b.2
    have hq : ((⟨x, hx⟩ * ⟨y, hy⟩ : E) : E ⧸ Subgroup.center E) =
        ((⟨y, hy⟩ * ⟨x, hx⟩ : E) : E ⧸ Subgroup.center E) := by
      apply e.injective
      rw [QuotientGroup.mk_mul, QuotientGroup.mk_mul, map_mul, map_mul, mul_comm]
    have h := (mk_eq_mk_iff_conjNormal_eq hEC _ _).mp hq
    simp only [Subgroup.coe_mul, map_mul] at h
    rw [Subgroup.coe_mul, Subgroup.coe_mul, ← hxa, ← hyb, h]
  · obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp hy
    rw [← map_pow, hEexp x hx, map_one]

theorem card_map_conjNormal [Fact p.Prime] (hEcard : Nat.card E = p ^ 3)
    (hEC : E ⊓ Subgroup.centralizer (K : Set X) = (Subgroup.center E).map E.subtype)
    (e : E ⧸ Subgroup.center E ≃* Multiplicative (Fin 2 → ZMod p)) :
    Nat.card (E.map (MulAut.conjNormal (H := K))) = p ^ 2 := by
  have hp := (Fact.out : p.Prime)
  have hQ : Nat.card (E ⧸ Subgroup.center E) = p ^ 2 := by
    rw [Nat.card_congr e.toEquiv]
    simp
  have hZ : Nat.card (Subgroup.center E) = p := by
    have h := Subgroup.card_eq_card_quotient_mul_card_subgroup (Subgroup.center E)
    rw [hEcard, hQ] at h
    have h' : p ^ 2 * Nat.card (Subgroup.center E) = p ^ 2 * p := by
      rw [← h]
      ring
    exact Nat.eq_of_mul_eq_mul_left (pow_pos hp.pos 2) h'
  have hmul := Subgroup.relIndex_mul_card (MulAut.conjNormal (H := K)).ker E
  rw [Subgroup.relIndex_ker, ker_conjNormal_eq_centralizer, inf_comm, hEC,
    Subgroup.card_map_of_injective E.subtype_injective, hZ, hEcard] at hmul
  have h' : Nat.card (E.map (MulAut.conjNormal (H := K))) * p = p ^ 2 * p := by
    rw [hmul]
    ring
  exact Nat.eq_of_mul_eq_mul_right hp.pos h'

end Image

section Automizer

variable {X : Type} [Group X] {p : ℕ} {K : Subgroup X} [K.Normal] {E : Subgroup X}

theorem map_conjNormal_inf_range_conj_ne_bot [Fact p.Prime] (hOut : KOutRankLeOne p K)
    (hEcard : Nat.card E = p ^ 3) (hEexp : ∀ x ∈ E, x ^ p = 1)
    (hEC : E ⊓ Subgroup.centralizer (K : Set X) = (Subgroup.center E).map E.subtype)
    (e : E ⧸ Subgroup.center E ≃* Multiplicative (Fin 2 → ZMod p)) :
    E.map (MulAut.conjNormal (H := K)) ⊓ (MulAut.conj : K →* MulAut K).range ≠ ⊥ := by
  intro h
  have hle := hOut _ (isElemAbelian_map_conjNormal hEexp hEC e) h
  rw [card_map_conjNormal hEcard hEC e] at hle
  have hp := (Fact.out : p.Prime).one_lt
  nlinarith

theorem conjNormal_apply_mem_comap {g : X} (hg : g ∈ Subgroup.normalizer (E : Set X)) {k : K}
    (hk : k ∈ (E.map (MulAut.conjNormal (H := K))).comap MulAut.conj) :
    MulAut.conjNormal g k ∈ (E.map (MulAut.conjNormal (H := K))).comap MulAut.conj := by
  rw [Subgroup.mem_comap] at hk ⊢
  obtain ⟨x, hx, hxk⟩ := Subgroup.mem_map.mp hk
  rw [← mulAut_mul_conj_mul_inv, ← hxk, ← map_inv, ← map_mul, ← map_mul]
  exact Subgroup.mem_map_of_mem _ ((Subgroup.mem_normalizer_iff.mp hg x).mp hx)

theorem map_conjNormal_sylow_le (hTI : KSylowTI p K) (U : Sylow p K)
    (hVU : (E.map (MulAut.conjNormal (H := K))).comap MulAut.conj ≤ U)
    (hV : (E.map (MulAut.conjNormal (H := K))).comap MulAut.conj ≠ ⊥) {g : X}
    (hg : g ∈ Subgroup.normalizer (E : Set X)) :
    (U : Subgroup K).map (MulAut.conjNormal g).toMonoidHom ≤ U := by
  obtain ⟨W, hW⟩ := (U.isPGroup'.map (MulAut.conjNormal g).toMonoidHom).exists_le_sylow
  have hVW : (E.map (MulAut.conjNormal (H := K))).comap MulAut.conj ≤ W := by
    intro v hv
    refine hW ⟨MulAut.conjNormal g⁻¹ v, hVU (conjNormal_apply_mem_comap (inv_mem hg) hv), ?_⟩
    simp [MulAut.inv_apply]
  have hUW := hTI U W fun h => hV (eq_bot_iff.mpr (h ▸ le_inf hVU hVW))
  subst hUW
  exact hW

theorem conjNormal_mem_normalizer [Finite X] (hTI : KSylowTI p K) (U : Sylow p K)
    (hVU : (E.map (MulAut.conjNormal (H := K))).comap MulAut.conj ≤ U)
    (hV : (E.map (MulAut.conjNormal (H := K))).comap MulAut.conj ≠ ⊥) {g : X}
    (hg : g ∈ Subgroup.normalizer (E : Set X)) :
    MulAut.conjNormal g ∈ Subgroup.normalizer
      (((U : Subgroup K).map (MulAut.conj : K →* MulAut K) : Subgroup (MulAut K)) :
        Set (MulAut K)) := by
  refine Subgroup.mem_normalizer_fintype fun n hn => ?_
  obtain ⟨u, hu, rfl⟩ := Subgroup.mem_map.mp hn
  rw [mulAut_mul_conj_mul_inv]
  exact Subgroup.mem_map_of_mem _ (map_conjNormal_sylow_le hTI U hVU hV hg ⟨u, hu, rfl⟩)

theorem conjNormal_mem_of_mem_secondDerived [Finite X] (hTI : KSylowTI p K)
    (hBor : KBorelMetabelian p K) (U : Sylow p K)
    (hVU : (E.map (MulAut.conjNormal (H := K))).comap MulAut.conj ≤ U)
    (hV : (E.map (MulAut.conjNormal (H := K))).comap MulAut.conj ≠ ⊥)
    {g : Subgroup.normalizer (E : Set X)}
    (hg : g ∈ ⁅commutator (Subgroup.normalizer (E : Set X)),
      commutator (Subgroup.normalizer (E : Set X))⁆) :
    MulAut.conjNormal (g : X) ∈ (U : Subgroup K).map (MulAut.conj : K →* MulAut K) := by
  let ψ := (MulAut.conjNormal (H := K)).comp (Subgroup.normalizer (E : Set X)).subtype
  have hle : (⊤ : Subgroup (Subgroup.normalizer (E : Set X))).map ψ ≤ Subgroup.normalizer
      (((U : Subgroup K).map (MulAut.conj : K →* MulAut K) : Subgroup (MulAut K)) :
        Set (MulAut K)) := by
    rintro _ ⟨h, -, rfl⟩
    exact conjNormal_mem_normalizer hTI U hVU hV h.2
  have h := Subgroup.mem_map_of_mem ψ hg
  rw [commutator_def, map_secondDerived] at h
  exact hBor U (secondDerived_mono hle h)

end Automizer

section Action

variable {X : Type*} [Group X] {p : ℕ} [Fact p.Prime] {K : Subgroup X} [K.Normal]
  {E : Subgroup X}

theorem centerQuotientAction_eq_one_of_conjNormal_eq_one {n : ℕ}
    (hEC : E ⊓ Subgroup.centralizer (K : Set X) = (Subgroup.center E).map E.subtype)
    (e : E ⧸ Subgroup.center E ≃* Multiplicative (Fin n → ZMod p))
    {g : Subgroup.normalizer (E : Set X)} (hg : MulAut.conjNormal (H := K) (g : X) = 1) :
    centerQuotientAction E e g = 1 := by
  refine centerQuotientAction_eq E e g 1 fun u v huv => ?_
  have hvu : (v : E ⧸ Subgroup.center E) = u := by
    refine (mk_eq_mk_iff_conjNormal_eq hEC v u).mpr ?_
    rw [huv, map_mul, map_mul, hg, map_inv, hg, one_mul, inv_one, mul_one]
  rw [Units.val_one, Matrix.one_mulVec, hvu]

end Action

theorem false_of_rankOneLieAutFacts {X : Type} [Group X] [Finite X] {p : ℕ} [Fact p.Prime]
    (hp2 : p ≠ 2) {K : Subgroup X} [K.Normal] (hZK : Subgroup.center K = ⊥)
    (hK : RankOneLieAutFacts p K) {E L : Subgroup X} (hEcard : Nat.card E = p ^ 3)
    (hEexp : ∀ x ∈ E, x ^ p = 1)
    (hEC : E ⊓ Subgroup.centralizer (K : Set X) = (Subgroup.center E).map E.subtype)
    (e : E ⧸ Subgroup.center E ≃* Multiplicative (Fin 2 → ZMod p))
    (hSL : StatedSL 2 (ZMod p) ≤
      (L.subgroupOf (Subgroup.normalizer (E : Set X))).map (centerQuotientAction E e)) :
    False := by
  obtain ⟨hOut, hTI, hBor⟩ := hK
  have hne := map_conjNormal_inf_range_conj_ne_bot hOut hEcard hEexp hEC e
  have hVp : IsPGroup p ((E.map (MulAut.conjNormal (H := K))).comap MulAut.conj) :=
    ((IsPGroup.of_card hEcard).map _).comap_of_injective _ (mulAut_conj_injective hZK)
  have hV : (E.map (MulAut.conjNormal (H := K))).comap MulAut.conj ≠ ⊥ := by
    intro h
    apply hne
    rw [inf_comm, ← Subgroup.map_comap_eq, h, Subgroup.map_bot]
  obtain ⟨U, hVU⟩ := hVp.exists_le_sylow
  have h1 := secondDerived_mono hSL (neg_one_mem_secondDerived_statedSL hp2)
  rw [← map_secondDerived] at h1
  obtain ⟨g, hg, hgρ⟩ := Subgroup.mem_map.mp h1
  have hgU := conjNormal_mem_of_mem_secondDerived hTI hBor U hVU hV
    (secondDerived_mono le_top hg)
  obtain ⟨k, hk⟩ := U.isPGroup'.map (MulAut.conj : K →* MulAut K) ⟨_, hgU⟩
  have hk' : MulAut.conjNormal (H := K) ((g ^ p ^ k : Subgroup.normalizer (E : Set X)) : X) =
      1 := by
    rw [Subgroup.coe_pow, map_pow]
    exact congrArg Subtype.val hk
  have h := centerQuotientAction_eq_one_of_conjNormal_eq_one hEC e hk'
  rw [map_pow, hgρ] at h
  exact neg_one_pow_prime_pow_ne_one hp2 k h

end CFSG.AGLEmbedding
