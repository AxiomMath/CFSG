module

public import CFSG.HardMathSupport.Curtis.NaturalModuleCensus.ExcCross.CoprimeCentralizer
public import CFSG.HardMathSupport.Curtis.NaturalModuleCensus.ExcCross.ExcE6CWCard
public import CFSG.HardMathSupport.Curtis.NaturalModuleCensus.ExcCross.ExcE6Torus
public import CFSG.HardMathSupport.Malle.E27Lie.ExcCross.E6TwoPair

public noncomputable section

set_option linter.unusedSectionVars false

namespace CFSG.HardMathSupport.Curtis.NaturalModuleCensus.ExcCross

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.PartOne.KE
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open CFSG.LieType.SeitzGeneration (e6TwoWord)
open CFSG.HardMathSupport.Curtis.UnitaryLevi (wordW wordW_append wordW_eq_of_matrix card_centralizer_conj)
open CFSG.HardMathSupport.Malle.E27Lie.ExcCross (R6 bK6 Lk6 ATw6 mp6 e6A_a_data e6A_b_data
  e6_hQ_a e6_hQ_b nine_dvd_card_closure_words wordW_pow_three_of_mp6 e6XAB e6XAB2 e6ZsAB e6ZsAB2
  e6L2AB e6L2AB2 e6ZsAB_W e6ZsAB2_W e6ZsAB_mem e6ZsAB2_mem e6ZsAB_comm_w e6ZsAB2_comm_w e6Z_ab_D
  e6Z_ab2_D e6Z_ab_solve e6Z_ab2_solve e6Z_ab_point e6Z_ab2_point)
open scoped Matrix

section Matrix6


theorem weylMat_mul' {τ : Tag} (u v : WeylGroup τ) : weylMat (u * v) = weylMat u * weylMat v :=
  weylMat_eq_of_smul fun x => by
    rw [mul_smul, ← weylMat_mulVec v x, ← weylMat_mulVec u, Matrix.mulVec_mulVec]

theorem Atw_mul' {τ : Tag} (u v : WeylGroup τ) : Atw (u * v) = Atw u * Atw v := by
  simp only [Atw, mul_inv_rev, weylMat_mul', Matrix.transpose_mul]

@[expose] def A6 (x : WeylGroup Tag.E6) : Matrix (Fin 4) (Fin 4) ℤ := E6Bp * Atw x * E6B

theorem A6_wordW (l : List (Fin Tag.E6.rank)) : A6 (wordW Tag.E6 l) = R6 l := by
  rw [A6, Atw_wordW]
  rfl

theorem Atw_mul_E6B {u : WeylGroup Tag.E6}
    (hu : u ∈ Subgroup.centralizer ({wE6W} : Set (WeylGroup Tag.E6))) :
    Atw u * E6B = E6B * A6 u := by
  have hc : E6A * Atw u = Atw u * E6A := by
    have := congrArg Atw (Subgroup.mem_centralizer_singleton_iff.1 hu)
    rw [Atw_mul', Atw_mul', Atw_wE6] at this
    exact this.symm
  have hX : (E6A + 1) * (Atw u * E6B) = 0 := by
    rw [Matrix.add_mul, Matrix.one_mul, ← Matrix.mul_assoc, hc, Matrix.mul_assoc, E6A_mul_B,
      Matrix.mul_neg]
    exact neg_add_cancel _
  have hcol : ∀ j, (Atw u * E6B).col j = E6B.mulVec (E6Bp.mulVec ((Atw u * E6B).col j)) := by
    intro j
    refine E6_kernel_eq _ ?_
    ext i
    have := congrFun (congrFun hX i) j
    simpa [Matrix.mul_apply, Matrix.mulVec, dotProduct] using this
  have hmat : ∀ i j, (Atw u * E6B) i j = ((E6B * E6Bp) * (Atw u * E6B)) i j := by
    intro i j
    have h := congrFun (hcol j) i
    rw [Matrix.col_apply, Matrix.mulVec_mulVec, Matrix.mulVec, dotProduct] at h
    simp only [Matrix.col_apply] at h
    exact h.trans Matrix.mul_apply.symm
  ext i j
  rw [hmat i j, A6]
  simp only [Matrix.mul_assoc]

end Matrix6

section Setup

variable
  {F L : Type} [Field F] [Finite F] [Field L] [Algebra F L] [IsAlgClosure F L] [IsAlgClosed L]
  {Fr : L →+* L}

abbrev NE6 (Fr : L →+* L) : Type :=
  ↥(NFix (canonicalRep (coxeterSystem Tag.E6) L wE6W) Fr)

abbrev πE6 (Fr : L →+* L) : NE6 Fr →* WeylGroup Tag.E6 :=
  NFixToWeyl (canonicalRep (coxeterSystem Tag.E6) L wE6W) Fr

abbrev NQ (F : Type) [Field F] [Finite F] (Fr : L →+* L) : Type := NE6 Fr ⧸ T'NFix F Fr

theorem NFix_conj_rootDiagUnit {τ : Tag} {n : ModGL τ L} (g : NFix n Fr) (a : Fin τ.rank → Lˣ) :
    (g : ModGL τ L) * rootDiagUnit τ a * (g : ModGL τ L)⁻¹ =
      rootDiagUnit τ (weylTuple (NFixToWeyl n Fr g) a) := by
  obtain ⟨u, k, hk, hgk⟩ := monomialSubgroup_le_torusWeylCosets g.2.1
  have hmaps : MapsRootLines (g : ModGL τ L) u := by
    rw [hgk]
    simpa using (mapsRootLines_of_mem_torusGroup hk).mul (mapsRootLines_canonicalRep (R := L) u)
  rw [NFixToWeyl_eq hmaps, ← canonicalRep_conj_rootDiagUnit, hgk]
  have e2 : k * canonicalRep (coxeterSystem τ) L u * rootDiagUnit τ a *
      (k * canonicalRep (coxeterSystem τ) L u)⁻¹ =
      k * (canonicalRep (coxeterSystem τ) L u * rootDiagUnit τ a *
        (canonicalRep (coxeterSystem τ) L u)⁻¹) * k⁻¹ := by group
  rw [e2]
  set D := canonicalRep (coxeterSystem τ) L u * rootDiagUnit τ a *
    (canonicalRep (coxeterSystem τ) L u)⁻¹ with hD
  have hDt : D ∈ torusGroup τ L := by
    rw [hD, canonicalRep_conj_rootDiagUnit]
    exact rootDiagUnit_mem_torusGroup _
  exact (mul_inv_eq_iff_eq_mul).2 (torusGroup_mul_comm hk hDt)

theorem coe_mactC (M : Matrix (Fin 4) (Fin 4) ℤ) (b : Fin 4 → μ3 F L) :
    (fun k => ((mactC M b k : μ3 F L) : Lˣ)) = ract M (fun k => (b k : Lˣ)) := by
  funext k
  simp [mactC, ract]

variable (hFr : ∀ c, Fr c = c ^ Nat.card F) (h3 : 3 ∣ Nat.card F + 1)

@[expose] def ι3N : (Fin 4 → μ3 F L) →* NE6 Fr :=
  (ι3 F L).codRestrict (NFix (canonicalRep (coxeterSystem Tag.E6) L wE6W) Fr)
    fun b => twistedTorusOf_le_NFix _ _ (ι3_mem_T hFr b)

theorem ι3N_coe (b : Fin 4 → μ3 F L) :
    ((ι3N hFr b : NE6 Fr) : ModGL Tag.E6 L) = ι3 F L b := rfl

theorem NE6_conj_ι3 (g : NE6 Fr) (b : Fin 4 → μ3 F L) :
    g * ι3N hFr b * g⁻¹ = ι3N hFr (mactC (A6 (πE6 Fr g)) b) := by
  apply Subtype.ext
  have hu : πE6 Fr g ∈ Subgroup.centralizer ({wE6W} : Set (WeylGroup Tag.E6)) :=
    NFixToWeyl_mem_centralizer Fr wE6W g
  show (g : ModGL Tag.E6 L) * ι3 F L b * (g : ModGL Tag.E6 L)⁻¹ =
    ι3 F L (mactC (A6 (πE6 Fr g)) b)
  rw [ι3_apply, ι3_apply, NFix_conj_rootDiagUnit, weylTuple_eq_mactC, mactC_eq_ract, ← ract_mul,
    Atw_mul_E6B hu, ract_mul, coe_mactC]

theorem T'NFix_le_ker : T'NFix F Fr ≤ (πE6 Fr).ker := by
  intro x hx
  rw [NFixToWeyl_ker, Subgroup.mem_subgroupOf]
  exact T'E6_le (mem_T'NFix.1 hx)

@[expose] def ιQ : (Fin 4 → μ3 F L) →* NQ F Fr :=
  (QuotientGroup.mk' (T'NFix F Fr)).comp (ι3N hFr)

variable (F Fr) in
@[expose] def πQ : NQ F Fr →* WeylGroup Tag.E6 :=
  QuotientGroup.lift (T'NFix F Fr) (πE6 Fr) T'NFix_le_ker

theorem πQ_mk (g : NE6 Fr) : πQ F Fr (QuotientGroup.mk g) = πE6 Fr g := rfl

include h3 in
theorem ιQ_injective : Function.Injective (ιQ hFr) := by
  rw [injective_iff_map_eq_one]
  intro b hb
  have h1 : ι3N hFr b ∈ T'NFix F Fr := (QuotientGroup.eq_one_iff _).1 hb
  have h2 : ι3 F L b ∈ T'E6 F Fr := mem_T'NFix.1 h1
  exact ι3_injective ((T'E6_inter_range hFr h3 h2 ⟨b, rfl⟩).trans (map_one _).symm)

theorem πQ_ιQ (b : Fin 4 → μ3 F L) : πQ F Fr (ιQ hFr b) = 1 := by
  show πE6 Fr (ι3N hFr b) = 1
  rw [← MonoidHom.mem_ker, NFixToWeyl_ker, Subgroup.mem_subgroupOf]
  exact ι3_mem_T hFr b

include h3 in
theorem πQ_ker (x : NQ F Fr) (hx : πQ F Fr x = 1) : x ∈ (ιQ hFr).range := by
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective x
  have hg : g ∈ (πE6 Fr).ker := hx
  rw [NFixToWeyl_ker, Subgroup.mem_subgroupOf] at hg
  obtain ⟨t₃, t', ht₃, ht₃3, ht', hgt⟩ := T'E6_decomp hFr h3 hg
  obtain ⟨b, hb⟩ := T3_le_range hFr h3 ht₃ ht₃3
  refine ⟨b, ?_⟩
  show QuotientGroup.mk (ι3N hFr b) = QuotientGroup.mk g
  rw [QuotientGroup.eq]
  show (ι3 F L b)⁻¹ * (g : ModGL Tag.E6 L) ∈ T'E6 F Fr
  rw [hb, hgt, inv_mul_cancel_left]
  exact ht'

theorem NQ_conj (x : NQ F Fr) (b : Fin 4 → μ3 F L) :
    x * ιQ hFr b * x⁻¹ = ιQ hFr (mactC (A6 (πQ F Fr x)) b) := by
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective x
  show QuotientGroup.mk g * QuotientGroup.mk (ι3N hFr b) * (QuotientGroup.mk g)⁻¹ =
    QuotientGroup.mk (ι3N hFr (mactC (A6 (πE6 Fr g)) b))
  rw [← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, NE6_conj_ι3]

include h3 in
theorem exists_orderOf_three_μ3 : ∃ ω : μ3 F L, orderOf ω = 3 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hv : 1 ≤ padicValNat 3 (Nat.card F + 1) :=
    one_le_padicValNat_of_dvd (Nat.succ_ne_zero _) h3
  have hcard : Nat.card (μ3 F L) = 3 ^ padicValNat 3 (Nat.card F + 1) := natCard_μ3 h3
  have : Finite (μ3 F L) := Nat.finite_of_card_ne_zero (by rw [hcard]; positivity)
  exact exists_prime_orderOf_dvd_card' 3 (by rw [hcard]; exact dvd_pow_self 3 (by omega))

include hFr in
theorem exists_hom_lift (Q : Subgroup (WeylGroup Tag.E6)) (hQ : IsPGroup 3 Q)
    (hQw : Q ≤ Subgroup.centralizer ({wE6W} : Set (WeylGroup Tag.E6))) :
    ∃ f : Q →* NQ F Fr, ∀ q : Q, πQ F Fr (f q) = q := by
  obtain ⟨C, hCinj, hCsurj, -⟩ := exists_nfix_lift Fr hFr wE6W Q hQ hQw
  choose g hgC hg using fun q : Q => hCsurj q q.2
  refine ⟨MonoidHom.mk' (fun q => (QuotientGroup.mk (g q) : NQ F Fr)) ?_, fun q => ?_⟩
  · intro a b
    have : g (a * b) = g a * g b := hCinj _ (hgC _) _ (mul_mem (hgC _) (hgC _)) (by
      rw [map_mul, hg, hg, hg]; rfl)
    show (QuotientGroup.mk (g (a * b)) : NQ F Fr) = QuotientGroup.mk (g a) * QuotientGroup.mk (g b)
    rw [this, QuotientGroup.mk_mul]
  · show πE6 Fr (g q) = q
    exact hg q

theorem isPGroup_closure_pair6 {a b : WeylGroup Tag.E6} (hab : a * b = b * a) (ha : a ^ 3 = 1)
    (hb : b ^ 3 = 1) : IsPGroup 3 (Subgroup.closure ({a, b} : Set (WeylGroup Tag.E6))) := by
  have hcomm := pair_comm_of_closure6 a b hab
  have hcube : ∀ x ∈ Subgroup.closure ({a, b} : Set (WeylGroup Tag.E6)), x ^ 3 = 1 := by
    intro x hx
    induction hx using Subgroup.closure_induction with
    | mem y hy => rcases hy with rfl | rfl; exact ha; exact hb
    | one => simp
    | mul u v hu hv hu3 hv3 =>
      rw [(show Commute u v from hcomm u hu v hv).mul_pow, hu3, hv3, one_mul]
    | inv u hu hu3 => simp [inv_pow, hu3]
  exact fun x => ⟨1, by
    ext
    simpa using hcube x x.2⟩

variable (F Fr) in
@[expose] def Bd6 (x : WeylGroup Tag.E6) : Prop :=
  ∀ s : NQ F Fr, πQ F Fr s = x → s ^ 3 = 1 → 81 ∣ Nat.card (Subgroup.centralizer ({s} : Set (NQ F Fr)))

theorem Bd6.inv {x : WeylGroup Tag.E6} (h : Bd6 F Fr x) : Bd6 F Fr x⁻¹ := by
  intro s hs hs3
  have h1 := h s⁻¹ (by rw [map_inv, hs, inv_inv]) (by rw [inv_pow, hs3, inv_one])
  have : Subgroup.centralizer ({s⁻¹} : Set (NQ F Fr)) = Subgroup.centralizer ({s} : Set (NQ F Fr)) := by
    ext c
    rw [Subgroup.mem_centralizer_singleton_iff, Subgroup.mem_centralizer_singleton_iff]
    exact Commute.inv_right_iff
  rwa [this] at h1

include hFr h3 in
theorem boundA6_core (lx ly : List (Fin Tag.E6.rank)) (hx : wordW Tag.E6 lx ∈ Q6)
    (hy : wordW Tag.E6 ly ∈ Q6) (Φ Ψ : Matrix (Fin 4) (Fin 4) ℤ)
    (hid : 1 - R6 ly = (1 - R6 lx) * Φ + Ψ * (1 + R6 lx + R6 lx * R6 lx))
    (c₁ c₂ : Fin 4 → ℤ) (p₁ p₂ : Fin 4)
    (hf₁ : ∀ i : Fin 4, (3 : ℤ) ∣ ((R6 lx).mulVec c₁) i - c₁ i)
    (hf₂ : ∀ i : Fin 4, (3 : ℤ) ∣ ((R6 lx).mulVec c₂) i - c₂ i)
    (h11 : c₁ p₁ = 1) (h12 : c₂ p₁ = 0) (h21 : c₁ p₂ = 0) (h22 : c₂ p₂ = 1)
    (hQ : 9 ∣ Nat.card (Subgroup.closure ({wordW Tag.E6 lx, wordW Tag.E6 ly} :
      Set (WeylGroup Tag.E6))))
    (s : NQ F Fr) (hs : πQ F Fr s = wordW Tag.E6 lx) (hs3 : s ^ 3 = 1) :
    81 ∣ Nat.card (Subgroup.centralizer ({s} : Set (NQ F Fr))) := by
  obtain ⟨ω, hω⟩ := exists_orderOf_three_μ3 h3 (F := F) (L := L)
  obtain ⟨f, hf⟩ := exists_hom_lift hFr Q6 Q6_pGroup Q6_le_centralizer
  have hcomm : f ⟨_, hy⟩ * f ⟨_, hx⟩ = f ⟨_, hx⟩ * f ⟨_, hy⟩ := by
    rw [← map_mul, ← map_mul]
    exact congrArg f (Subtype.ext (Q6_comm _ hy _ hx))
  have hgx3 : f ⟨_, hx⟩ ^ 3 = 1 := by
    rw [← map_pow]
    have : (⟨_, hx⟩ : Q6) ^ 3 = 1 := Subtype.ext (Q6_cube _ hx)
    rw [this, map_one]
  refine caseA_ab (ιQ hFr) (πQ F Fr) A6 (ιQ_injective hFr h3) (πQ_ker hFr h3) (πQ_ιQ hFr)
    (NQ_conj hFr) _ _ s (f ⟨_, hx⟩) (f ⟨_, hy⟩) hs (hf _) (hf _) hcomm hgx3 hs3 Φ Ψ ?_ ω hω c₁ c₂
    p₁ p₂ ?_ ?_ h11 h12 h21 h22 hQ
  · rw [A6_wordW, A6_wordW]; exact hid
  · rw [A6_wordW]; exact hf₁
  · rw [A6_wordW]; exact hf₂

include hFr h3 in
theorem boundB6_core (lx l₁ l₂ : List (Fin Tag.E6.rank))
    (ys : Fin 4 → List (Fin Tag.E6.rank)) (Ξ : Matrix (Fin 4) (Fin 4) ℤ)
    (hΞ : (1 - R6 lx) * Ξ = (3 : ℤ) • 1)
    (hsolve : ∀ c : Fin 4 → ℤ, ∃ i : Fin 4, ∃ d : Fin 4 → ℤ,
      (1 - R6 lx).mulVec d = (1 - R6 (ys i)).mulVec c)
    (hpt : ∀ κ : Fin 4 → ℤ, ∃ c d₁ d₂ : Fin 4 → ℤ,
      (1 - R6 lx).mulVec d₁ = (1 - R6 l₁).mulVec c ∧
      (1 - R6 lx).mulVec d₂ = (1 - R6 l₂).mulVec (c - κ))
    (c₁ c₂ : Fin 4 → ℤ) (p₁ p₂ : Fin 4)
    (hf₁ : ∀ i : Fin 4, (3 : ℤ) ∣ ((R6 lx).mulVec c₁) i - c₁ i)
    (hf₂ : ∀ i : Fin 4, (3 : ℤ) ∣ ((R6 lx).mulVec c₂) i - c₂ i)
    (h11 : c₁ p₁ = 1) (h12 : c₂ p₁ = 0) (h21 : c₁ p₂ = 0) (h22 : c₂ p₂ = 1)
    (hx : wordW Tag.E6 lx ∈ Q6) (hy₁ : wordW Tag.E6 l₁ ∈ Q6)
    (hx3 : wordW Tag.E6 lx ^ 3 = 1) (hy3 : wordW Tag.E6 l₂ ^ 3 = 1)
    (hxy : wordW Tag.E6 lx * wordW Tag.E6 l₂ = wordW Tag.E6 l₂ * wordW Tag.E6 lx)
    (hy₂ : wordW Tag.E6 l₂ ∈ Subgroup.centralizer ({wE6W} : Set (WeylGroup Tag.E6)))
    (hys : ∀ i, wordW Tag.E6 (ys i) ∈ Subgroup.closure
      ({wordW Tag.E6 l₁, wordW Tag.E6 l₂} : Set (WeylGroup Tag.E6)))
    (hQ : ∀ i, 9 ∣ Nat.card (Subgroup.closure
      ({wordW Tag.E6 lx, wordW Tag.E6 (ys i)} : Set (WeylGroup Tag.E6))))
    (s : NQ F Fr) (hs : πQ F Fr s = wordW Tag.E6 lx) :
    81 ∣ Nat.card (Subgroup.centralizer ({s} : Set (NQ F Fr))) := by
  obtain ⟨ω, hω⟩ := exists_orderOf_three_μ3 h3 (F := F) (L := L)
  obtain ⟨f, hf⟩ := exists_hom_lift hFr Q6 Q6_pGroup Q6_le_centralizer
  have hc₁ : f ⟨_, hy₁⟩ * f ⟨_, hx⟩ = f ⟨_, hx⟩ * f ⟨_, hy₁⟩ := by
    rw [← map_mul, ← map_mul]
    exact congrArg f (Subtype.ext (Q6_comm _ hy₁ _ hx))
  have hcl : Subgroup.closure ({wordW Tag.E6 lx, wordW Tag.E6 l₂} : Set (WeylGroup Tag.E6)) ≤
      Subgroup.centralizer ({wE6W} : Set (WeylGroup Tag.E6)) := by
    rw [Subgroup.closure_le]
    rintro _ (rfl | rfl)
    · exact Q6_le_centralizer hx
    · exact hy₂
  obtain ⟨f₂, hq₂⟩ := exists_hom_lift hFr _ (isPGroup_closure_pair6 hxy hx3 hy3) hcl
  have hxm : wordW Tag.E6 lx ∈ Subgroup.closure
      ({wordW Tag.E6 lx, wordW Tag.E6 l₂} : Set (WeylGroup Tag.E6)) :=
    Subgroup.subset_closure (Set.mem_insert _ _)
  have hym : wordW Tag.E6 l₂ ∈ Subgroup.closure
      ({wordW Tag.E6 lx, wordW Tag.E6 l₂} : Set (WeylGroup Tag.E6)) :=
    Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)
  have hc₂ : f₂ ⟨_, hym⟩ * f₂ ⟨_, hxm⟩ = f₂ ⟨_, hxm⟩ * f₂ ⟨_, hym⟩ := by
    rw [← map_mul, ← map_mul]
    exact congrArg f₂ (Subtype.ext hxy.symm)
  refine caseB_pair (ιQ hFr) (πQ F Fr) A6 (ιQ_injective hFr h3) (πQ_ker hFr h3) (πQ_ιQ hFr)
    (NQ_conj hFr) _ _ _ (fun i => wordW Tag.E6 (ys i)) hys s (f ⟨_, hx⟩) (f ⟨_, hy₁⟩)
    (f₂ ⟨_, hxm⟩) (f₂ ⟨_, hym⟩) hs (hf _) (hf _) hc₁ (hq₂ _) (hq₂ _) hc₂ ?_ Ξ ?_ ?_ ω hω
    c₁ c₂ p₁ p₂ ?_ ?_ h11 h12 h21 h22 hQ
  · intro κ
    obtain ⟨c, d₁, d₂, e₁, e₂⟩ := hpt κ
    exact ⟨c, d₁, d₂, by rw [A6_wordW, A6_wordW]; exact e₁,
      by rw [A6_wordW, A6_wordW]; exact e₂⟩
  · rw [A6_wordW]; exact hΞ
  · intro c
    obtain ⟨i, d, hd⟩ := hsolve c
    exact ⟨i, d, by rw [A6_wordW, A6_wordW]; exact hd⟩
  · rw [A6_wordW]; exact hf₁
  · rw [A6_wordW]; exact hf₂

theorem mem_centralizer_of_mp6 {l : List (Fin Tag.E6.rank)}
    (h : mp6 (l ++ wE6) = mp6 (wE6 ++ l)) :
    wordW Tag.E6 l ∈ Subgroup.centralizer ({wE6W} : Set (WeylGroup Tag.E6)) := by
  have := wordW_eq_of_matrix Tag.E6 _ _ h
  rw [wordW_append, wordW_append] at this
  exact Subgroup.mem_centralizer_singleton_iff.2 this

theorem wordW_comm_of_mp6 {l l' : List (Fin Tag.E6.rank)} (h : mp6 (l ++ l') = mp6 (l' ++ l)) :
    wordW Tag.E6 l * wordW Tag.E6 l' = wordW Tag.E6 l' * wordW Tag.E6 l := by
  have := wordW_eq_of_matrix Tag.E6 _ _ h
  rwa [wordW_append, wordW_append] at this

theorem wordW_e6XAB_mem : wordW Tag.E6 e6XAB ∈ Q6 := by
  rw [show e6XAB = laE6 ++ lbE6 from rfl, wordW_append]
  exact mul_mem wa6_mem wb6_mem

theorem wordW_e6XAB2_mem : wordW Tag.E6 e6XAB2 ∈ Q6 := by
  rw [show e6XAB2 = laE6 ++ lbE6 ++ lbE6 from rfl, wordW_append, wordW_append]
  exact mul_mem (mul_mem wa6_mem wb6_mem) wb6_mem

include hFr h3 in
theorem bd6_wa : Bd6 F Fr wa6 := fun s hs hs3 => by
  obtain ⟨hid, hf₁, hf₂, h11, h12, h21, h22⟩ := e6A_a_data
  exact boundA6_core hFr h3 laE6 lbE6 wa6_mem wb6_mem _ _ hid _ _ 0 2 hf₁ hf₂ h11 h12 h21 h22
    e6_hQ_a s hs hs3

include hFr h3 in
theorem bd6_wb : Bd6 F Fr wb6 := fun s hs hs3 => by
  obtain ⟨hid, hf₁, hf₂, h11, h12, h21, h22⟩ := e6A_b_data
  exact boundA6_core hFr h3 lbE6 laE6 wb6_mem wa6_mem _ _ hid _ _ 1 2 hf₁ hf₂ h11 h12 h21 h22
    e6_hQ_b s hs hs3

include hFr h3 in
theorem bd6_ab : Bd6 F Fr (wa6 * wb6) := by
  intro s hs _
  obtain ⟨-, -, -, hΞ, hf₁, hf₂, h11, h12, h21, h22⟩ := e6Z_ab_D
  obtain ⟨hW1, hW2, hW3⟩ := e6ZsAB_W
  refine boundB6_core hFr h3 e6XAB laE6 e6L2AB e6ZsAB _ hΞ e6Z_ab_solve e6Z_ab_point _ _ 0 2
    hf₁ hf₂ h11 h12 h21 h22 wordW_e6XAB_mem wa6_mem
    (wordW_pow_three_of_mp6 e6XAB (hW1 0).1) (wordW_pow_three_of_mp6 e6L2AB hW2)
    (wordW_comm_of_mp6 hW3) (mem_centralizer_of_mp6 e6ZsAB_comm_w.2) e6ZsAB_mem
    (fun i => nine_dvd_card_closure_words _ _ (hW1 i)) s ?_
  rw [hs, show e6XAB = laE6 ++ lbE6 from rfl, wordW_append]
  rfl

include hFr h3 in
theorem bd6_ab2 : Bd6 F Fr (wa6 * wb6 * wb6) := by
  intro s hs _
  obtain ⟨-, -, -, hΞ, hf₁, hf₂, h11, h12, h21, h22⟩ := e6Z_ab2_D
  obtain ⟨hW1, hW2, hW3⟩ := e6ZsAB2_W
  refine boundB6_core hFr h3 e6XAB2 laE6 e6L2AB2 e6ZsAB2 _ hΞ e6Z_ab2_solve e6Z_ab2_point _ _ 0 2
    hf₁ hf₂ h11 h12 h21 h22 wordW_e6XAB2_mem wa6_mem
    (wordW_pow_three_of_mp6 e6XAB2 (hW1 0).1) (wordW_pow_three_of_mp6 e6L2AB2 hW2)
    (wordW_comm_of_mp6 hW3) (mem_centralizer_of_mp6 e6ZsAB2_comm_w.2) e6ZsAB2_mem
    (fun i => nine_dvd_card_closure_words _ _ (hW1 i)) s ?_
  rw [hs, show e6XAB2 = laE6 ++ lbE6 ++ lbE6 from rfl, wordW_append, wordW_append]
  rfl

theorem inv_eq_sq6 {g : WeylGroup Tag.E6} (h : g ^ 3 = 1) : g⁻¹ = g ^ 2 :=
  inv_eq_of_mul_eq_one_right (by rw [← pow_succ']; exact h)

theorem inv_ab6 : (wa6 * wb6)⁻¹ = wa6 ^ 2 * wb6 ^ 2 := by
  rw [mul_inv_rev, inv_eq_sq6 wa6_cube, inv_eq_sq6 wb6_cube]
  exact ((show Commute wa6 wb6 from wa6_wb6_comm).symm.pow_pow 2 2).eq

theorem inv_ab2_6 : (wa6 * wb6 * wb6)⁻¹ = wa6 ^ 2 * wb6 ^ 1 := by
  rw [mul_inv_rev, mul_inv_rev, inv_eq_sq6 wa6_cube, inv_eq_sq6 wb6_cube]
  have h4 : wb6 ^ 2 * wb6 ^ 2 = wb6 := by
    calc wb6 ^ 2 * wb6 ^ 2 = wb6 ^ 3 * wb6 := by group
      _ = wb6 := by rw [wb6_cube, one_mul]
  calc wb6 ^ 2 * (wb6 ^ 2 * wa6 ^ 2) = (wb6 ^ 2 * wb6 ^ 2) * wa6 ^ 2 := (mul_assoc _ _ _).symm
    _ = wb6 * wa6 ^ 2 := by rw [h4]
    _ = wa6 ^ 2 * wb6 ^ 1 := by
      rw [pow_one]
      exact (((show Commute wa6 wb6 from wa6_wb6_comm).symm).pow_right 2).eq

include hFr h3 in
theorem bd6_of_Q6 {x : WeylGroup Tag.E6} (hx : x ∈ Q6) (hx1 : x ≠ 1) : Bd6 F Fr x := by
  obtain ⟨i, j, rfl⟩ := mem_Q6 hx
  rw [pow_eq_pow_mod i wa6_cube, pow_eq_pow_mod j wb6_cube] at hx1 ⊢
  have hi : i % 3 < 3 := Nat.mod_lt _ (by norm_num)
  have hj : j % 3 < 3 := Nat.mod_lt _ (by norm_num)
  generalize i % 3 = a at hi hx1 ⊢
  generalize j % 3 = b at hj hx1 ⊢
  interval_cases a <;> interval_cases b
  · exact absurd (by simp) hx1
  · simpa using bd6_wb hFr h3
  · have := (bd6_wb hFr h3).inv
    rwa [inv_eq_sq6 wb6_cube, ← one_mul (wb6 ^ 2), ← pow_zero wa6] at this
  · simpa using bd6_wa hFr h3
  · simpa using bd6_ab hFr h3
  · have := bd6_ab2 hFr h3
    simpa [pow_two, mul_assoc] using this
  · have := (bd6_wa hFr h3).inv
    rwa [inv_eq_sq6 wa6_cube, ← mul_one (wa6 ^ 2), ← pow_zero wb6] at this
  · have := (bd6_ab2 hFr h3).inv
    rwa [inv_ab2_6] at this
  · have := (bd6_ab hFr h3).inv
    rwa [inv_ab6] at this

include hFr h3 in
theorem bd6_torus (s : NQ F Fr) (hs : πQ F Fr s = 1) :
    81 ∣ Nat.card (Subgroup.centralizer ({s} : Set (NQ F Fr))) := by
  obtain ⟨t, rfl⟩ := πQ_ker hFr h3 s hs
  have hle : (ιQ hFr).range ≤ Subgroup.centralizer ({ιQ hFr t} : Set (NQ F Fr)) := by
    rintro _ ⟨u, rfl⟩
    rw [Subgroup.mem_centralizer_singleton_iff, ← map_mul, ← map_mul, mul_comm]
  have hcard : Nat.card (ιQ hFr).range = (3 ^ padicValNat 3 (Nat.card F + 1)) ^ 4 := by
    rw [← Nat.card_congr (MonoidHom.ofInjective (ιQ_injective hFr h3)).toEquiv, Nat.card_pi]
    simp [natCard_μ3 h3]
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hv : 1 ≤ padicValNat 3 (Nat.card F + 1) :=
    one_le_padicValNat_of_dvd (Nat.succ_ne_zero _) h3
  have h81 : 81 ∣ (3 ^ padicValNat 3 (Nat.card F + 1)) ^ 4 := by
    have : (3 : ℕ) ^ 4 ∣ (3 ^ padicValNat 3 (Nat.card F + 1)) ^ 4 :=
      pow_dvd_pow_of_dvd (dvd_pow_self 3 (by omega)) 4
    simpa using this
  exact (hcard ▸ h81).trans (Subgroup.card_dvd_of_le hle)

end Setup

section Final


theorem nfixE6TwoNLevel : ∀ (F : Type) [Field F] [Finite F] (L : Type) [Field L] [Algebra F L]
    [IsAlgClosure F L] (Fr : L →+* L), (∀ c, Fr c = c ^ Nat.card F) → 3 ∣ Nat.card F + 1 →
    ∀ s : NFix (canonicalRep (coxeterSystem Tag.E6) L
      ((coxeterSystem Tag.E6).wordProd e6TwoWord)) Fr, s ^ 3 = 1 → s ≠ 1 →
      81 ∣ Nat.card (Subgroup.centralizer ({s} : Set (NFix (canonicalRep (coxeterSystem Tag.E6) L
        ((coxeterSystem Tag.E6).wordProd e6TwoWord)) Fr))) := by
  intro F _ _ L _ _ _ Fr hFr h3 s hs3 _
  have : IsAlgClosed L := IsAlgClosure.isAlgClosed F
  have := finite_NFix_E6 Fr hFr
  have hq : 2 ≤ Nat.card F := Finite.one_lt_card
  refine eightyOne_dvd_of_quotient (T'NFix F Fr) T'NFix_comm (coprime_card_T'NFix hFr h3) s hs3 ?_
  set sb : NQ F Fr := QuotientGroup.mk s with hsb
  have hsb3 : sb ^ 3 = 1 := by rw [hsb, ← QuotientGroup.mk_pow, hs3, QuotientGroup.mk_one]
  by_cases hz1 : πQ F Fr sb = 1
  · exact bd6_torus hFr h3 sb hz1
  · have hz3 : (πQ F Fr sb) ^ 3 = 1 := by rw [← map_pow, hsb3, map_one]
    have hzc : πQ F Fr sb ∈ Subgroup.centralizer ({wE6W} : Set (WeylGroup Tag.E6)) :=
      NFixToWeyl_mem_centralizer Fr wE6W s
    obtain ⟨g, hgc, hg⟩ := exists_conj_centralizer_mem_Q6 hzc hz3
    obtain ⟨g', hg'⟩ := NFixToWeyl_surjective_centralizer Fr wE6W hq hFr hgc
    have hconj : πQ F Fr ((QuotientGroup.mk g' : NQ F Fr) * sb * (QuotientGroup.mk g')⁻¹) =
        g * πQ F Fr sb * g⁻¹ := by
      rw [map_mul, map_mul, map_inv]
      show πE6 Fr g' * πQ F Fr sb * (πE6 Fr g')⁻¹ = _
      rw [hg']
    have hne : g * πQ F Fr sb * g⁻¹ ≠ 1 := by
      intro h
      apply hz1
      have h' := mul_inv_eq_one.1 h
      exact mul_left_cancel (h'.trans (mul_one g).symm)
    have hQ := bd6_of_Q6 hFr h3 hg hne _ hconj (by rw [conj_pow, hsb3]; simp)
    rwa [card_centralizer_conj] at hQ

end Final

end CFSG.HardMathSupport.Curtis.NaturalModuleCensus.ExcCross

end
