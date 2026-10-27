module

public import CFSG.HardMathSupport.Solomon.LocalBalance.InnDiagThree
public import CFSG.HardMathSupport.Solomon.LocalBalance.Sec5Statements
public import CFSG.HardMathSupport.Solomon.LocalBalance.Sec3Statements
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma24
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma32
public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Inputs7

public section

namespace CFSG.HardMathSupport.Solomon.LocalBalance

namespace Lemma53Ns

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.HardMathSupport.Solomon.Coordinator
  CFSG.HardMathSupport.Solomon.UniquenessMaximal

@[expose] def fixSub {Y : Type*} [Group Y] (α : MulAut Y) : Subgroup Y where
  carrier := {y | α y = y}
  mul_mem' := fun {a b} ha hb => by
    show α (a * b) = a * b
    rw [map_mul]
    exact congrArg₂ (· * ·) ha hb
  one_mem' := map_one α
  inv_mem' := fun {a} ha => by
    show α a⁻¹ = a⁻¹
    rw [map_inv]
    exact congrArg (·⁻¹) ha

export CFSG.HardMathSupport.Solomon.LocalBalance (IsConjByGL IsInnDiagPSL3 IsInnDiagPSU3
  IsInnDiagThree IsThreeType)

@[expose] def Input19_1_2 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G], (∃ a b : G, a * b ≠ b * a) →
    CFSG.Open.IsKProper G → ∀ p : ℕ, p.Prime → ∀ D : Subgroup G, IsElemAbelian p D → D ≠ ⊥ →
      ∀ b ∈ Subgroup.centralizer (D : Set G), b ≠ 1 → b ^ p = 1 →
        (∀ L : Subgroup G, GLAPComponent p (Subgroup.centralizer ({b} : Set G)) L →
          GLADelta p D ⊓ Subgroup.centralizer ({b} : Set G) ≤ Subgroup.normalizer (L : Set G)) ∧
        ∀ L : Subgroup G, GLAPComponent p (Subgroup.centralizer ({b} : Set G)) L →
          ¬ ⁅L, GLADelta p D ⊓ Subgroup.centralizer ({b} : Set G)⁆ ≤
              GLAPPrimeCoreOf p (Subgroup.centralizer ({b} : Set G)) →
            kerB p D L = ⊥ ∧ D ≤ Subgroup.normalizer (L : Set G) ∧
              ((((GLADelta p D ⊓ Subgroup.centralizer ({b} : Set G)).subgroupOf
                    (Subgroup.normalizer (L : Set G))).map (barAut p L)) ≤
                localDeltaIn p
                  ((((GLADelta p D ⊓ Subgroup.centralizer ({b} : Set G)) ⊔ L).subgroupOf
                    (Subgroup.normalizer (L : Set G))).map (barAut p L))
                  ((D.subgroupOf (Subgroup.normalizer (L : Set G))).map (barAut p L)))

@[expose] def Input19_7_3b : Prop :=
  ∀ (K : Type) [Group K] [Finite K], CFSG.Open.IsQuasisimple K → IsThreeType K →
    ∀ D H : Subgroup (MulAut K), IsEkIn 3 2 ⊤ D → innerAut K ≤ H →
      D ≤ Subgroup.normalizer (H : Set (MulAut K)) → localDeltaIn 3 H D ≠ ⊥ →
        ∀ α ∈ localDeltaIn 3 H D, IsInnDiagThree α → α = 1

@[expose] def Input7_AutQuotAbelian : Prop :=
  ∀ (K : Type) [Group K] [Finite K], CFSG.Open.IsQuasisimple K → IsThreeType K →
    ∀ α β : MulAut K, IsInnDiagThree (α * β * α⁻¹ * β⁻¹)

@[expose] def Input7_FieldInn : Prop :=
  ∀ (K : Type) [Group K] [Finite K], CFSG.Open.IsQuasisimple K → ∀ α : MulAut K,
    IsFieldAutThree α → α ∈ innerAut K → α = 1

@[expose] def Input9_5 : Prop :=
  ∀ (K : Type) [Group K] [Finite K], CFSG.Open.IsQuasisimple K → GLAPPrimeCore 3 K = ⊥ →
    ∀ α : MulAut K, IsFieldAutThree α → orderOf α = 3 → GLAPLayer 3 (fixSub α) ≠ ⊥ →
      ∀ β : MulAut K, (∀ y ∈ GLAPLayer 3 (fixSub α), β y = y) → β ∈ Subgroup.zpowers α

@[expose] def Input9_2_8 : Prop :=
  ∀ (K : Type) [Group K] [Finite K], CFSG.Open.IsQuasisimple K → GLAPPrimeCore 3 K = ⊥ →
    ∀ α : MulAut K, IsFieldAutThree α → orderOf α = 3 → GLAPPrimeCoreOf 3 (fixSub α) = ⊥

@[expose] def Input14_5Aut : Prop :=
  ∀ (K : Type) [Group K] [Finite K], CFSG.Open.IsQuasisimple K → GLAPPrimeCore 3 K = ⊥ →
    ∀ α : MulAut K, IsFieldAutThree α → orderOf α = 3 →
      GLAPLayer 3 (fixSub α) = ⊥ ∨ CFSG.Open.IsQuasisimple ↥(GLAPLayer 3 (fixSub α))

@[expose] def Input3_3_ON : Prop :=
  (∀ (K : Type) (_ : Field K) (_ : Finite K),
      IsEmpty ((TauCeti.CFSGIndex.sporadic TauCeti.SporadicName.ONan).Group ≃*
        StatedProj (StatedSL 3 K))) ∧
  (∀ (K : Type) (_ : Field K) (_ : Finite K) (q : ℕ), Nat.card K = q ^ 2 →
      IsEmpty ((TauCeti.CFSGIndex.sporadic TauCeti.SporadicName.ONan).Group ≃*
        StatedProj (StatedSU 3 q K)))

structure Hyp53 {G : Type} [Group G] [Finite G] (m : ℕ) (B : Subgroup G) (b : G)
    (L : Subgroup G) (x : G) : Prop where
  hS : GLStanding G m 3
  hC : GLCaseFour G 3
  hB : IsBOneMax 3 B
  hb : b ∈ B
  hb1 : b ≠ 1
  hL : GLAPComponent 3 (Subgroup.centralizer ({b} : Set G)) L
  hx : x ∈ B
  hx1 : x ≠ 1
  hxN : x ∈ Subgroup.normalizer (L : Set G)
  hxF : IsFieldAutThree (barAut 3 L ⟨x, hxN⟩)

@[expose] def CSpec {G : Type} [Group G] [Finite G] (b x : G) (J : Subgroup G)
    (𝒞 : Set (Subgroup G)) : Prop :=
  (∀ M ∈ 𝒞, GLAPComponent 3 (Subgroup.centralizer ({x} : Set G)) M) ∧
    (⨆ M ∈ 𝒞, M) = ⨆ g ∈ GLAPLayer 3 (Subgroup.centralizer ({x} : Set G)), GLBConj g J ∧
    (∀ M ∈ 𝒞, ∀ e ∈ Subgroup.zpowers b, GLBConj e M ∈ 𝒞) ∧
    ∀ M ∈ 𝒞, ∀ M' ∈ 𝒞, ∃ e ∈ Subgroup.zpowers b, GLBConj e M = M'

section Quasi

variable {Y : Type} [Group Y] [Finite Y]

theorem A2_commutator_mul_central {Y : Type*} [Group Y] (s t z w : Y) (hz : z ∈ Subgroup.center Y) (hw : w ∈ Subgroup.center Y) :
    s * z * (t * w) * (s * z)⁻¹ * (t * w)⁻¹ = s * t * s⁻¹ * t⁻¹ := by
  have h1 := Subgroup.mem_center_iff.1 hz
  have h2 := Subgroup.mem_center_iff.1 hw
  have e1 : s * z * (t * w) * (s * z)⁻¹ * (t * w)⁻¹ = s * (z * (t * w) * z⁻¹) * s⁻¹ * (w⁻¹ * t⁻¹) := by group
  have e2 : z * (t * w) * z⁻¹ = t * w := by
    rw [← h1 (t * w)]; group
  have e3 : w⁻¹ * t⁻¹ = t⁻¹ * w⁻¹ := by
    rw [← mul_inv_rev, ← mul_inv_rev, h2 t]
  rw [e1, e2, e3]
  have e4 : s * (t * w) * s⁻¹ * (t⁻¹ * w⁻¹) = s * t * (w * (s⁻¹ * t⁻¹) * w⁻¹) := by group
  rw [e4, ← h2 (s⁻¹ * t⁻¹)]
  group

theorem A2_eq_bot_or_top_of_isSubnormal {S : Type*} [Group S] [IsSimpleGroup S]
    {H K : Subgroup S} (h : IsSubnormal H K) (hK : K = ⊥ ∨ K = ⊤) : H = ⊥ ∨ H = ⊤ :=
  by
    rcases hK with rfl | rfl
    · exact Or.inl (le_bot_iff.1 h.le)
    · exact h.eq_bot_or_top

omit [Finite Y] in
theorem eq_top_of_perfect_subnormal (hY : CFSG.Open.IsQuasisimple Y) {S : Subgroup Y}
    (hS : IsSubnormal S ⊤) (hperf : ⁅S, S⁆ = S) (hne : S ≠ ⊥) : S = ⊤ := by
  have : IsSimpleGroup (Y ⧸ Subgroup.center Y) := hY.2
  have hsn := CFSG.LocalAnalysis.GLTheoremB.isSubnormal_map'
    (QuotientGroup.mk' (Subgroup.center Y)) hS
  rw [Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective _)] at hsn
  rcases A2_eq_bot_or_top_of_isSubnormal hsn (Or.inr rfl) with h | h
  · exfalso
    apply hne
    have hle : S ≤ Subgroup.center Y := by
      intro x hx
      have : QuotientGroup.mk' (Subgroup.center Y) x ∈ (⊥ : Subgroup (Y ⧸ Subgroup.center Y)) := by
        rw [← h]; exact Subgroup.mem_map_of_mem _ hx
      exact (QuotientGroup.eq_one_iff x).1 this
    have h2 : ⁅S, S⁆ = ⊥ :=
      Subgroup.commutator_eq_bot_iff_le_centralizer.2 (hle.trans (Subgroup.center_le_centralizer _))
    rw [← hperf, h2]
  · have hY1 : (⊤ : Subgroup Y) ≤ S := by
      rw [← hY.1, commutator, ← hperf]
      refine Subgroup.commutator_le.2 fun a _ b _ => ?_
      have ha : QuotientGroup.mk' (Subgroup.center Y) a ∈ (S.map (QuotientGroup.mk' (Subgroup.center Y))) := by
        rw [h]; trivial
      have hb : QuotientGroup.mk' (Subgroup.center Y) b ∈ (S.map (QuotientGroup.mk' (Subgroup.center Y))) := by
        rw [h]; trivial
      obtain ⟨s, hs, hsa⟩ := ha
      obtain ⟨t, ht, htb⟩ := hb
      have hza : s⁻¹ * a ∈ Subgroup.center Y := QuotientGroup.eq.1 hsa
      have hzb : t⁻¹ * b ∈ Subgroup.center Y := QuotientGroup.eq.1 htb
      obtain ⟨z, hz⟩ : ∃ z ∈ Subgroup.center Y, a = s * z := ⟨s⁻¹ * a, hza, by simp⟩
      obtain ⟨w, hw⟩ : ∃ w ∈ Subgroup.center Y, b = t * w := ⟨t⁻¹ * b, hzb, by simp⟩
      have key : a * b * a⁻¹ * b⁻¹ = s * t * s⁻¹ * t⁻¹ := by
        rw [hz.2, hw.2]
        exact A2_commutator_mul_central s t z w hz.1 hw.1
      rw [commutatorElement_def, key]
      exact Subgroup.commutator_mem_commutator hs ht
    exact top_le_iff.1 hY1

omit [Finite Y] in
theorem eq_of_perfect_subnormal_of_quasisimple {Q S : Subgroup Y}
    (hQ : CFSG.Open.IsQuasisimple ↥Q) (hSQ : S ≤ Q) (hS : IsSubnormal S Q) (hperf : ⁅S, S⁆ = S)
    (hne : S ≠ ⊥) : S = Q := by
  have hsn : IsSubnormal (S.subgroupOf Q) ⊤ := by
    have := CFSG.LocalAnalysis.GLTheoremB.isSubnormal_comap' Q.subtype hS
    have h2 : Q.comap Q.subtype = ⊤ := by ext; simp
    rwa [h2] at this
  have hperf' : ⁅S.subgroupOf Q, S.subgroupOf Q⁆ = S.subgroupOf Q := by
    apply Subgroup.map_injective Q.subtype_injective
    rw [Subgroup.map_commutator, Subgroup.map_subgroupOf_eq_of_le hSQ]
    exact hperf
  have hne' : S.subgroupOf Q ≠ ⊥ := by
    intro h
    apply hne
    rw [← Subgroup.map_subgroupOf_eq_of_le hSQ, h, Subgroup.map_bot]
  have h := eq_top_of_perfect_subnormal (Y := ↥Q) hQ hsn hperf' hne'
  refine le_antisymm hSQ fun q hq => ?_
  have : (⟨q, hq⟩ : ↥Q) ∈ S.subgroupOf Q := by rw [h]; trivial
  exact this

end Quasi

section Generic

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem A2_commutator_le_of_le {X A B : Subgroup G} (hA : A ≤ X) (hB : B ≤ X) : ⁅A, B⁆ ≤ X :=
  Subgroup.commutator_le.2 fun _ ha _ hb =>
    X.mul_mem (X.mul_mem (X.mul_mem (hA ha) (hB hb)) (X.inv_mem (hA ha))) (X.inv_mem (hB hb))

omit [Finite G] in
theorem A2_subgroupOf_commutator {X A B : Subgroup G} (hA : A ≤ X) (hB : B ≤ X) :
    (⁅A, B⁆).subgroupOf X = ⁅A.subgroupOf X, B.subgroupOf X⁆ := by
  apply Subgroup.map_injective X.subtype_injective
  rw [Subgroup.map_commutator, Subgroup.map_subgroupOf_eq_of_le hA,
    Subgroup.map_subgroupOf_eq_of_le hB, Subgroup.map_subgroupOf_eq_of_le
      (A2_commutator_le_of_le hA hB)]

omit [Finite G] in
theorem A2_barX_commutator (p : ℕ) {X A B : Subgroup G} (hA : A ≤ X) (hB : B ≤ X) :
    barX p X ⁅A, B⁆ = ⁅barX p X A, barX p X B⁆ := by
  unfold barX
  rw [A2_subgroupOf_commutator hA hB, Subgroup.map_commutator]

omit [Finite G] in
theorem A2_barX_mono (p : ℕ) {X S T : Subgroup G} (h : S ≤ T) : barX p X S ≤ barX p X T :=
  Subgroup.map_mono fun _ hx => (Subgroup.mem_subgroupOf).2 (h ((Subgroup.mem_subgroupOf).1 hx))

omit [Finite G] in
theorem A2_barX_perfect {p : ℕ} {X K : Subgroup G} (hK : GLAPComponent p X K) :
    ⁅barX p X K, barX p X K⁆ = barX p X K :=
  Subgroup.isPerfect_iff.1 ⟨hK.2.2.1.2.2.1⟩

omit [Finite G] in
theorem A2_barX_ne_bot {p : ℕ} {X K : Subgroup G} (hK : GLAPComponent p X K) :
    barX p X K ≠ ⊥ := by
  intro h
  have hs : IsSimpleGroup (↥(barX p X K) ⧸ Subgroup.center ↥(barX p X K)) := hK.2.2.1.2.2.2
  obtain ⟨a, b, hab⟩ := exists_pair_ne (↥(barX p X K) ⧸ Subgroup.center ↥(barX p X K))
  apply hab
  obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective a
  obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective b
  have ha : a = 1 := Subtype.ext (by simpa [h] using a.2)
  have hb : b = 1 := Subtype.ext (by simpa [h] using b.2)
  rw [ha, hb]

omit [Finite G] in
theorem glaPComponent_perfect {p : ℕ} {X K : Subgroup G} (hK : GLAPComponent p X K) :
    ⁅K, K⁆ = K := by
  have hperf := A2_barX_perfect hK
  obtain ⟨hKX, hsn, hcomp, hmin⟩ := hK
  have hJK : ⁅K, K⁆ ≤ K := A2_commutator_le_of_le le_rfl le_rfl
  by_contra hne
  have hlt : ⁅K, K⁆ < K := lt_of_le_of_ne hJK hne
  have hnorm : (⁅K, K⁆.subgroupOf K).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hJK).2
      (Subgroup.le_normalizer_iff_commutator_le_left.2 (Subgroup.commutator_mono hJK le_rfl))
  exact hmin _ hlt (IsSubnormal.step hJK hnorm hsn)
    (by show barX p X ⁅K, K⁆ = barX p X K
        rw [A2_barX_commutator p hKX hKX, hperf])

omit [Finite G] in
theorem glaPComponent_eq_of_le {p : ℕ} (_hp : p.Prime) {X M L : Subgroup G}
    (hM : GLAPComponent p X M) (hL : GLAPComponent p X L) (hML : M ≤ L) : M = L := by
  have hle : barX p X M ≤ barX p X L := A2_barX_mono p hML
  have hMc : IsComponentOf (barX p X M) ⊤ := hM.2.2.1
  have hLc : IsComponentOf (barX p X L) ⊤ := hL.2.2.1
  have hsn : IsSubnormal (barX p X M) (barX p X L) :=
    isSubnormal_of_le_of_le hMc.2.1 hle le_top
  have heq : barX p X M = barX p X L :=
    eq_of_perfect_subnormal_of_quasisimple hLc.2.2 hle hsn (A2_barX_perfect hM)
      (A2_barX_ne_bot hM)
  by_contra hne
  exact hL.2.2.2 M (lt_of_le_of_ne hML hne) hM.2.1 heq

theorem A2_isQuasisimple_of_mulEquiv {A B : Type*} [Group A] [Group B] (e : A ≃* B)
    (h : CFSG.Open.IsQuasisimple A) : CFSG.Open.IsQuasisimple B :=
  h.of_mulEquiv e.symm

omit [Finite G] in
theorem A2_isSubnormal_barX_top (p : ℕ) {M K : Subgroup G} (h : IsSubnormal K M) :
    IsSubnormal (barX p M K) ⊤ := by
  have h1 := CFSG.LocalAnalysis.GLTheoremB.isSubnormal_comap' M.subtype h
  have h2 : M.comap M.subtype = ⊤ := by ext; simp
  rw [h2] at h1
  have h3 := CFSG.LocalAnalysis.GLTheoremB.isSubnormal_map'
    (QuotientGroup.mk' (GLAPPrimeCore p ↥M)) h1
  rwa [Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective _)] at h3

theorem A2_barX_le_of_barMap {p : ℕ} (hp : p.Prime) {H M K J : Subgroup G} (hHM : H ≤ M)
    (hKH : K ≤ H) (hsnH : IsSubnormal K H) (hsnM : IsSubnormal K M) (hJK : J ≤ K)
    (h : barX p M K ≤ barX p M J) : barX p H K ≤ barX p H J := by
  have hKM : K ≤ M := hKH.trans hHM
  rintro _ ⟨x, hx, rfl⟩
  have hxK : (x : G) ∈ K := hx
  have hmem : QuotientGroup.mk' (GLAPPrimeCore p ↥M) (Subgroup.inclusion hHM x) ∈ barX p M K :=
    ⟨Subgroup.inclusion hHM x, hxK, rfl⟩
  obtain ⟨y, hy, hyx⟩ := h hmem
  have hyJ : (y : G) ∈ J := hy
  have hyK : (y : G) ∈ K := hJK hyJ
  have hyH : (y : G) ∈ H := hKH hyK
  let j : ↥K := ⟨y, hyK⟩
  let k : ↥K := ⟨x, hxK⟩
  have h1 : j⁻¹ * k ∈ (barMap p hKM).ker := by
    rw [MonoidHom.mem_ker]
    apply Subtype.ext
    show QuotientGroup.mk' (GLAPPrimeCore p ↥M) (Subgroup.inclusion hKM (j⁻¹ * k)) = 1
    have : Subgroup.inclusion hKM (j⁻¹ * k) = y⁻¹ * Subgroup.inclusion hHM x := Subtype.ext rfl
    rw [this]
    exact (QuotientGroup.eq_one_iff _).2 (QuotientGroup.eq.1 hyx)
  rw [ker_barMap_eq hp hKM hsnM, ← ker_barMap_eq hp hKH hsnH, MonoidHom.mem_ker] at h1
  have h2 : QuotientGroup.mk' (GLAPPrimeCore p ↥H) (Subgroup.inclusion hKH (j⁻¹ * k)) = 1 :=
    congrArg Subtype.val h1
  refine ⟨⟨y, hyH⟩, hyJ, ?_⟩
  have h3 : (⟨y, hyH⟩ : ↥H)⁻¹ * x ∈ GLAPPrimeCore p ↥H := by
    have := (QuotientGroup.eq_one_iff _).1 h2
    exact this
  exact QuotientGroup.eq.2 h3

theorem glaPComponent_of_isSubnormal {p : ℕ} (hp : p.Prime) {H M K : Subgroup G}
    (hK : GLAPComponent p H K) (hHM : H ≤ M) (hsnM : IsSubnormal K M) :
    GLAPComponent p M K := by
  obtain ⟨hKH, hsnH, hcompH, hminH⟩ := hK
  have hKM : K ≤ M := hKH.trans hHM
  let e : ↥(barX p H K) ≃* ↥(barX p M K) :=
    (quotEquivBarX hp hKH hsnH).symm.trans (quotEquivBarX hp hKM hsnM)
  have hq : CFSG.Open.IsQuasisimple ↥(barX p H K) := hcompH.2.2
  refine ⟨hKM, hsnM, ⟨le_top, A2_isSubnormal_barX_top p hsnM, ?_⟩, ?_⟩
  · exact A2_isQuasisimple_of_mulEquiv e hq
  · intro J hJ hJsn heq
    have hJH : J ≤ H := hJ.le.trans hKH
    have hJsnH : IsSubnormal J H := isSubnormal_of_le_of_le hJsn hJH hHM
    refine hminH J hJ hJsnH ?_
    show barX p H J = barX p H K
    exact le_antisymm (A2_barX_mono p hJ.le)
      (A2_barX_le_of_barMap hp hHM hKH hsnH hsnM hJ.le (heq.symm.le))

theorem A2_commute_of_comm_bot {Y : Type*} [Group Y] {A B : Subgroup Y} (h : ⁅A, B⁆ = ⊥) {a b : Y}
    (ha : a ∈ A) (hb : b ∈ B) : a * b = b * a := by
  have := Subgroup.commutator_mem_commutator ha hb
  rw [h, Subgroup.mem_bot, commutatorElement_def] at this
  calc a * b = (a * b * a⁻¹ * b⁻¹) * b * a := by group
    _ = b * a := by rw [this, one_mul]

theorem mem_normalizer_of_mem_glaPLayer {p : ℕ} (_hp : p.Prime) {X M : Subgroup G}
    (hM : GLAPComponent p X M) {g : G} (hg : g ∈ GLAPLayer p X) :
    g ∈ Subgroup.normalizer (M : Set G) := by
  have hle : GLAPLayer p X ≤ Subgroup.normalizer (M : Set G) := by
    refine sSup_le fun M' hM' m' hm' => ?_
    by_cases hMM : M' = M
    · subst hMM
      exact Subgroup.le_normalizer hm'
    · have hm'X : m' ∈ X := hM'.1 hm'
      have hbar : barX p X M ≠ barX p X M' := fun h => hMM (glaPComponent_uniqueAux hM hM' h).symm
      have hcomm : ⁅barX p X M, barX p X M'⁆ = ⊥ :=
        CFSG.ComponentClassification.LocalComponents.commute_of_ne _ _ hM.2.2.1 hM'.2.2.1 hbar
      have hcomp := glaPComponent_gLBConj m' hM
      have hXX : GLBConj m' X = X := mem_normalizer_iff_gLBConj_eq.1 (Subgroup.le_normalizer hm'X)
      rw [hXX] at hcomp
      set mb := QuotientGroup.mk' (GLAPPrimeCore p ↥X) ⟨m', hm'X⟩ with hmb
      have hmbM' : mb ∈ barX p X M' := ⟨⟨m', hm'X⟩, (Subgroup.mem_subgroupOf).2 hm', rfl⟩
      have hbarEq : barX p X (GLBConj m' M) = barX p X M := by
        ext z
        constructor
        · rintro ⟨w, hw, rfl⟩
          have hw' : m' * (w : G) * m'⁻¹ ∈ M := mem_gLBConj.1 ((Subgroup.mem_subgroupOf).1 hw)
          have hw2X : m' * (w : G) * m'⁻¹ ∈ X :=
            X.mul_mem (X.mul_mem hm'X w.2) (X.inv_mem hm'X)
          have hmem : QuotientGroup.mk' (GLAPPrimeCore p ↥X) ⟨m' * (w : G) * m'⁻¹, hw2X⟩ ∈
              barX p X M := ⟨⟨_, hw2X⟩, (Subgroup.mem_subgroupOf).2 hw', rfl⟩
          have hc := A2_commute_of_comm_bot hcomm hmem hmbM'
          have : QuotientGroup.mk' (GLAPPrimeCore p ↥X) ⟨m' * (w : G) * m'⁻¹, hw2X⟩ =
              mb * QuotientGroup.mk' (GLAPPrimeCore p ↥X) w * mb⁻¹ := by
            rw [hmb, ← map_inv, ← map_mul, ← map_mul]
            rfl
          have h4 : QuotientGroup.mk' (GLAPPrimeCore p ↥X) w =
              QuotientGroup.mk' (GLAPPrimeCore p ↥X) ⟨m' * (w : G) * m'⁻¹, hw2X⟩ := by
            calc QuotientGroup.mk' (GLAPPrimeCore p ↥X) w
                = mb⁻¹ * (mb * QuotientGroup.mk' (GLAPPrimeCore p ↥X) w * mb⁻¹) * mb := by group
              _ = mb⁻¹ * QuotientGroup.mk' (GLAPPrimeCore p ↥X) ⟨m' * (w : G) * m'⁻¹, hw2X⟩ *
                    mb := by rw [this]
              _ = QuotientGroup.mk' (GLAPPrimeCore p ↥X) ⟨m' * (w : G) * m'⁻¹, hw2X⟩ := by
                rw [mul_assoc, hc, ← mul_assoc, inv_mul_cancel, one_mul]
          rw [h4]
          exact hmem
        · rintro ⟨w, hw, rfl⟩
          have hw2X : m'⁻¹ * (w : G) * m' ∈ X :=
            X.mul_mem (X.mul_mem (X.inv_mem hm'X) w.2) hm'X
          have hmem : QuotientGroup.mk' (GLAPPrimeCore p ↥X) w ∈ barX p X M :=
            ⟨w, hw, rfl⟩
          have hc := A2_commute_of_comm_bot hcomm hmem hmbM'
          have hwM : (w : G) ∈ M := (Subgroup.mem_subgroupOf).1 hw
          have hmem2 : (⟨m'⁻¹ * (w : G) * m', hw2X⟩ : ↥X) ∈ (GLBConj m' M).subgroupOf X := by
            rw [Subgroup.mem_subgroupOf, mem_gLBConj]
            have e : m' * (m'⁻¹ * (w : G) * m') * m'⁻¹ = w := by group
            show m' * (m'⁻¹ * (w : G) * m') * m'⁻¹ ∈ M
            rw [e]
            exact hwM
          refine ⟨⟨m'⁻¹ * (w : G) * m', hw2X⟩, hmem2, ?_⟩
          have : QuotientGroup.mk' (GLAPPrimeCore p ↥X) ⟨m'⁻¹ * (w : G) * m', hw2X⟩ =
              mb⁻¹ * QuotientGroup.mk' (GLAPPrimeCore p ↥X) w * mb := by
            rw [hmb, ← map_inv, ← map_mul, ← map_mul]
            rfl
          rw [this]
          calc mb⁻¹ * QuotientGroup.mk' (GLAPPrimeCore p ↥X) w * mb
              = mb⁻¹ * (QuotientGroup.mk' (GLAPPrimeCore p ↥X) w * mb) := by group
            _ = mb⁻¹ * (mb * QuotientGroup.mk' (GLAPPrimeCore p ↥X) w) := by rw [hc]
            _ = QuotientGroup.mk' (GLAPPrimeCore p ↥X) w := by group
      have hMeq : GLBConj m' M = M := glaPComponent_uniqueAux hcomp hM hbarEq
      exact mem_normalizer_iff_gLBConj_eq.2 hMeq
  exact hle hg

theorem exists_fixed_in_coset {p : ℕ} (hp : p.Prime) {x : G} (hx : x ^ p = 1) {N : Subgroup G}
    (hN : x ∈ Subgroup.normalizer (N : Set G)) (hcop : Nat.Coprime p (Nat.card N)) {g : G}
    (hg : g⁻¹ * (x * g * x⁻¹) ∈ N) : ∃ n ∈ N, x * (g * n) * x⁻¹ = g * n := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have hNx : ∀ n : G, n ∈ N ↔ x * n * x⁻¹ ∈ N := fun n => by
    simpa using (Subgroup.mem_normalizer_iff.1 hN n)
  have key : ∀ y : G, g⁻¹ * y ∈ N → g⁻¹ * (x * y * x⁻¹) ∈ N := by
    intro y hy
    have h1 : x * (g⁻¹ * y) * x⁻¹ ∈ N := (hNx _).1 hy
    have := N.mul_mem hg h1
    have e : g⁻¹ * (x * g * x⁻¹) * (x * (g⁻¹ * y) * x⁻¹) = g⁻¹ * (x * y * x⁻¹) := by group
    rwa [e] at this
  set S : Type := {y : G // g⁻¹ * y ∈ N} with hS
  let f : Function.End S := fun y => ⟨x * y.1 * x⁻¹, key y.1 y.2⟩
  have hfpow : ∀ k : ℕ, ∀ y : S, ((f ^ k) y).1 = x ^ k * y.1 * (x ^ k)⁻¹ := by
    intro k
    induction k with
    | zero => intro y; rw [pow_zero]; show y.1 = _; simp
    | succ k ih =>
      intro y
      rw [pow_succ]
      show ((f ^ k) (f y)).1 = _
      rw [ih]
      simp only [f]
      group
  have hf : f ^ p ^ 1 = 1 := by
    funext y
    apply Subtype.ext
    rw [pow_one, hfpow, hx]
    show _ = y.1
    simp
  have : Finite S := inferInstance
  have := Fintype.ofFinite S
  have hmod := Equiv.Perm.card_fixedPoints_modEq (p := p) (n := 1) hf
  have hcard : Fintype.card S = Nat.card N := by
    rw [← Nat.card_eq_fintype_card]
    exact Nat.card_congr (Equiv.subtypeEquiv (Equiv.mulLeft g⁻¹) (fun y => Iff.rfl))
  rw [hcard] at hmod
  have hne : Fintype.card f.fixedPoints ≠ 0 := by
    intro h0
    rw [h0] at hmod
    have : p ∣ Nat.card N := (Nat.modEq_zero_iff_dvd).1 hmod
    exact hp.one_lt.ne' (Nat.eq_one_of_dvd_coprimes hcop dvd_rfl this) 
  obtain ⟨⟨y, hyfix⟩⟩ := Fintype.card_pos_iff.1 (Nat.pos_of_ne_zero hne)
  refine ⟨g⁻¹ * y.1, y.2, ?_⟩
  have := congrArg Subtype.val hyfix
  simp only [f] at this
  simpa using this

omit [Finite G] in
theorem commutator_iSup_le_of_normal {X N S : Subgroup G} (hN : (N.subgroupOf X).Normal)
    {𝒞 : Set (Subgroup G)} (h𝒞 : ∀ K ∈ 𝒞, K ≤ X) (hS : S ≤ X)
    (h : ∀ K ∈ 𝒞, ⁅K, S⁆ ≤ N) : ⁅⨆ K ∈ 𝒞, K, S⁆ ≤ N := by
  have hcX : ∀ a b : G, a ∈ X → b ∈ X → a * b * a⁻¹ * b⁻¹ ∈ X := fun a b ha hb =>
    X.mul_mem (X.mul_mem (X.mul_mem ha hb) (X.inv_mem ha)) (X.inv_mem hb)
  have hconj : ∀ a n : G, a ∈ X → n ∈ X → n ∈ N → a * n * a⁻¹ ∈ N := fun a n ha hn hnN => by
    have := hN.conj_mem ⟨n, hn⟩ (Subgroup.mem_subgroupOf.2 hnN) ⟨a, ha⟩
    exact Subgroup.mem_subgroupOf.1 this
  let T : Subgroup G :=
    { carrier := {a | a ∈ X ∧ ∀ s ∈ S, a * s * a⁻¹ * s⁻¹ ∈ N}
      one_mem' := ⟨X.one_mem, fun s _ => by simp⟩
      mul_mem' := by
        rintro a b ⟨haX, ha⟩ ⟨hbX, hb⟩
        refine ⟨X.mul_mem haX hbX, fun s hs => ?_⟩
        have hsX : s ∈ X := hS hs
        have h1 := hconj a (b * s * b⁻¹ * s⁻¹) haX (hcX b s hbX hsX) (hb s hs)
        have h2 := N.mul_mem h1 (ha s hs)
        have e : a * (b * s * b⁻¹ * s⁻¹) * a⁻¹ * (a * s * a⁻¹ * s⁻¹) = a * b * s * (a * b)⁻¹ * s⁻¹ := by
          group
        rwa [e] at h2
      inv_mem' := by
        rintro a ⟨haX, ha⟩
        refine ⟨X.inv_mem haX, fun s hs => ?_⟩
        have hsX : s ∈ X := hS hs
        have h1 := hconj a⁻¹ (a * s * a⁻¹ * s⁻¹)⁻¹ (X.inv_mem haX) (X.inv_mem (hcX a s haX hsX))
          (N.inv_mem (ha s hs))
        have e : a⁻¹ * (a * s * a⁻¹ * s⁻¹)⁻¹ * a⁻¹⁻¹ = a⁻¹ * s * a⁻¹⁻¹ * s⁻¹ := by
          group
        rwa [e] at h1 }
  have hle : (⨆ K ∈ 𝒞, K) ≤ T := by
    refine iSup₂_le fun K hK a ha => ⟨h𝒞 K hK ha, fun s hs => ?_⟩
    exact h K hK (Subgroup.commutator_mem_commutator ha hs)
  rw [Subgroup.commutator_le]
  intro a ha s hs
  exact (hle ha).2 s hs

theorem centralizer_ne_top {m : ℕ} {x : G} (hx1 : x ≠ 1) (hS : GLStanding G m 3) :
    Subgroup.centralizer ({x} : Set G) ≠ ⊤ := by
  have := hS.simple
  intro h
  have hx' : x ∈ Subgroup.center G := by
    rw [Subgroup.mem_center_iff]
    intro g
    have : g ∈ Subgroup.centralizer ({x} : Set G) := h ▸ Subgroup.mem_top g
    exact (Subgroup.mem_centralizer_iff.1 this x rfl).symm
  rcases (inferInstance : (Subgroup.center G).Normal).eq_bot_or_eq_top with h1 | h1
  · exact hx1 (Subgroup.mem_bot.1 (h1 ▸ hx'))
  · obtain ⟨a, b, hab⟩ := hS.nonabelian
    exact hab (Subgroup.mem_center_iff.1 (h1 ▸ Subgroup.mem_top a) b).symm

omit [Finite G] in
theorem A1_exists_ne_one {D : Subgroup G} (hD : D ≠ ⊥) : ∃ d ∈ D, d ≠ 1 := by
  obtain ⟨d, hd1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).1 hD
  exact ⟨d, d.2, fun h => hd1 (Subtype.ext h)⟩

theorem A1_coprime_card_core (p : ℕ) (H : Subgroup G) :
    Nat.Coprime p (Nat.card (GLAPPrimeCoreOf p H)) := by
  have hc := coprime_card_gLAPPrimeCore_aux p ↥H
  have hcard : Nat.card (GLAPPrimeCoreOf p H) = Nat.card (GLAPPrimeCore p ↥H) :=
    Subgroup.card_map_of_injective H.subtype_injective
  rwa [hcard]

theorem coprime_orderOf_of_mem_gLADelta {p : ℕ} (_hp : p.Prime) {D : Subgroup G} (hD : D ≠ ⊥)
    {c : G} (hc : c ∈ GLADelta p D) : Nat.Coprime p (orderOf c) := by
  obtain ⟨d, hdD, hd1⟩ := A1_exists_ne_one hD
  have hle : GLADelta p D ≤ GLAPPrimeCoreOf p (Subgroup.centralizer ({d} : Set G)) :=
    iInf₂_le_of_le d hdD (iInf_le _ hd1)
  have hcop := A1_coprime_card_core p (Subgroup.centralizer ({d} : Set G))
  exact (hcop.coprime_dvd_right (Subgroup.orderOf_dvd_natCard _ (hle hc))).symm.symm

theorem coprime_card_gLADelta {p : ℕ} (_hp : p.Prime) {D : Subgroup G} (hD : D ≠ ⊥) :
    Nat.Coprime p (Nat.card (GLADelta p D)) := by
  obtain ⟨d, hdD, hd1⟩ := A1_exists_ne_one hD
  have hle : GLADelta p D ≤ GLAPPrimeCoreOf p (Subgroup.centralizer ({d} : Set G)) :=
    iInf₂_le_of_le d hdD (iInf_le _ hd1)
  exact (A1_coprime_card_core p _).coprime_dvd_right (Subgroup.card_dvd_of_le hle)

theorem A1_inf_le (p : ℕ) (K H : Subgroup G) :
    GLAPPrimeCoreOf p K ⊓ H ≤ GLAPPrimeCoreOf p (K ⊓ H) := by
  rintro y ⟨hyK, hyH⟩
  let N : Subgroup ↥(K ⊓ H) := (GLAPPrimeCoreOf p K).comap (K ⊓ H).subtype
  have hN : N.Normal :=
    ⟨fun n hn g => by
      change ((g * n * g⁻¹ : ↥(K ⊓ H)) : G) ∈ GLAPPrimeCoreOf p K
      have := mem_gLAPPrimeCoreOf_conj (x := (n : G)) (h := (g : G)) hn g.2.1
      simpa using this⟩
  have hcop : Nat.Coprime p (Nat.card N) := by
    have hle : N.map (K ⊓ H).subtype ≤ GLAPPrimeCoreOf p K := by
      rintro _ ⟨n, hn, rfl⟩
      exact hn
    have h1 := Subgroup.card_dvd_of_le hle
    rw [Subgroup.card_map_of_injective (Subgroup.subtype_injective _)] at h1
    exact (A1_coprime_card_core p K).coprime_dvd_right h1
  have hyK' : y ∈ K := Subgroup.map_subtype_le _ hyK
  have hyN : (⟨y, ⟨hyK', hyH⟩⟩ : ↥(K ⊓ H)) ∈ N := hyK
  exact ⟨⟨y, ⟨hyK', hyH⟩⟩,
    le_sSup (show N ∈ {N : Subgroup ↥(K ⊓ H) | N.Normal ∧ Nat.Coprime p (Nat.card N)} from
      ⟨hN, hcop⟩) hyN, rfl⟩

theorem commutator_le_core_of_normalizes {p : ℕ} {C L X : Subgroup G}
    (hL : GLAPComponent p C L) (hX : X ≤ Subgroup.normalizer (L : Set G))
    (h : ⁅L, X⁆ ≤ GLAPPrimeCoreOf p C) : ⁅L, X⁆ ≤ GLAPPrimeCoreOf p L := by
  have hLX : ⁅L, X⁆ ≤ L := by
    rw [Subgroup.commutator_le]
    intro l hl y hy
    have hy' := (Subgroup.mem_normalizer_iff.1 (hX hy)) l⁻¹
    have h1 : y * l⁻¹ * y⁻¹ ∈ L := hy'.1 (L.inv_mem hl)
    have e : l * y * l⁻¹ * y⁻¹ = l * (y * l⁻¹ * y⁻¹) := by group
    show l * y * l⁻¹ * y⁻¹ ∈ L
    rw [e]
    exact L.mul_mem hl h1
  have := A1_inf_le p C L
  rw [inf_eq_right.2 hL.1] at this
  exact fun z hz => this ⟨h hz, hLX hz⟩

omit [Finite G] in
theorem centralizer_singleton_eq_of_mem_zpowers {b x : G} (hb3 : b ^ 3 = 1) (hx1 : x ≠ 1)
    (hx : x ∈ Subgroup.zpowers b) :
    Subgroup.centralizer ({x} : Set G) = Subgroup.centralizer ({b} : Set G) := by
  have hcomm : ∀ {u v : G}, v ∈ Subgroup.zpowers u → ∀ c : G, Commute u c → Commute v c := by
    intro u v hv c hc
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hv
    exact hc.zpow_left k
  have hb3z : b ^ (3 : ℤ) = 1 := by exact_mod_cast hb3
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hx
  have hk : ¬ (3 : ℤ) ∣ k := by
    rintro ⟨m, rfl⟩
    apply hx1
    rw [zpow_mul, hb3z, one_zpow]
  have hk2 : k * k = 3 * (k * k / 3) + 1 := by
    have h1 : k % 3 = 1 ∨ k % 3 = 2 := by omega
    have h2 : k * k % 3 = 1 := by
      rcases h1 with h | h <;> simp [Int.mul_emod, h]
    omega
  have hbx : b ∈ Subgroup.zpowers (b ^ k) := by
    refine Subgroup.mem_zpowers_iff.2 ⟨k, ?_⟩
    rw [← zpow_mul, hk2, zpow_add, zpow_mul, hb3z, one_zpow, one_mul, zpow_one]
  ext c
  rw [Subgroup.mem_centralizer_singleton_iff, Subgroup.mem_centralizer_singleton_iff]
  constructor
  · intro hc
    exact (hcomm hbx c hc.symm).symm.eq
  · intro hc
    exact (hcomm (Subgroup.mem_zpowers_iff.2 ⟨k, rfl⟩) c hc.symm).symm.eq

theorem isUpsilonComponent_of_centralizer_eq {B : Subgroup G} {b x : G} {L : Subgroup G}
    (h : Subgroup.centralizer ({x} : Set G) = Subgroup.centralizer ({b} : Set G))
    (hL : IsUpsilonComponent B b L) : IsUpsilonComponent B x L := by
  unfold IsUpsilonComponent lambdaOf IsStronglyLocallyOneBalanced at *
  rw [h]
  exact hL

theorem A3_false_of_comm {Q : Type} [Group Q] (K : Subgroup Q)
    (hq : CFSG.Open.IsQuasisimple K) (hc : ⁅K, K⁆ = ⊥) : False := by
  obtain ⟨h, hs⟩ := hq
  have h1 : K = ⊥ := by
    have := Subgroup.map_subtype_commutator K
    rw [h, hc, Subgroup.map_top, Subgroup.range_subtype] at this
    exact this
  have hsub : Subsingleton K := ⟨fun a b => by
    apply Subtype.ext
    have ha : (a : Q) ∈ (⊥ : Subgroup Q) := h1 ▸ a.2
    have hb : (b : Q) ∈ (⊥ : Subgroup Q) := h1 ▸ b.2
    rw [Subgroup.mem_bot] at ha hb
    rw [ha, hb]⟩
  have : Subsingleton (K ⧸ Subgroup.center K) := inferInstance
  exact (hs.toNontrivial.exists_pair_ne).elim fun a ⟨b, hab⟩ => hab (Subsingleton.elim a b)

theorem not_stronglyBalanced_of_le_lambdaOf {B : Subgroup G} {b : G} {L : Subgroup G}
    (hL : GLAPComponent 3 (Subgroup.centralizer ({b} : Set G)) L) (h : L ≤ lambdaOf 3 B b) :
    ¬ IsStronglyLocallyOneBalanced 3 B b L := by
  intro hbal
  set X := Subgroup.centralizer ({b} : Set G) with hX
  let W : Subgroup G :=
    ((Subgroup.centralizer (barX 3 X L : Set (↥X ⧸ GLAPPrimeCore 3 ↥X))).comap
      (QuotientGroup.mk' (GLAPPrimeCore 3 ↥X))).map X.subtype
  have hmem : ∀ M : Subgroup G, GLAPComponent 3 X M → M ≠ L → M ≤ W := by
    intro M hM hne m hm
    have hcomm : ⁅barX 3 X M, barX 3 X L⁆ = ⊥ :=
      CFSG.ComponentClassification.LocalComponents.commute_of_ne _ _ hM.2.2.1 hL.2.2.1
        (fun h => hne (glaPComponent_uniqueAux hM hL h))
    have hmX : m ∈ X := hM.1 hm
    refine ⟨⟨m, hmX⟩, ?_, rfl⟩
    have hmb : QuotientGroup.mk' (GLAPPrimeCore 3 ↥X) ⟨m, hmX⟩ ∈ barX 3 X M :=
      ⟨⟨m, hmX⟩, (Subgroup.mem_subgroupOf).2 hm, rfl⟩
    exact Subgroup.commutator_eq_bot_iff_le_centralizer.1 hcomm hmb
  have hS : sSup {L | GLAPComponent 3 X L ∧ ¬ IsStronglyLocallyOneBalanced 3 B b L} ≤ W := by
    refine sSup_le fun M hM => hmem M hM.1 ?_
    rintro rfl
    exact hM.2 hbal
  have hLW : L ≤ W := h.trans hS
  have hcen : barX 3 X L ≤ Subgroup.centralizer (barX 3 X L : Set (↥X ⧸ GLAPPrimeCore 3 ↥X)) := by
    rintro _ ⟨⟨ℓ, hℓX⟩, hℓ, rfl⟩
    obtain ⟨⟨w, hwX⟩, hw, hwe⟩ := hLW (show ℓ ∈ L from hℓ)
    have : (⟨w, hwX⟩ : ↥X) = ⟨ℓ, hℓX⟩ := Subtype.ext hwe
    rw [this] at hw
    exact hw
  have hc : ⁅barX 3 X L, barX 3 X L⁆ = ⊥ := Subgroup.commutator_eq_bot_iff_le_centralizer.2 hcen
  have hq : CFSG.Open.IsQuasisimple (barX 3 X L) := hL.2.2.1.2.2
  exact A3_false_of_comm _ hq hc

omit [Finite G] in
theorem A3_comm {B : Subgroup G} (hB : IsMulCommutative B) {x y : G} (hx : x ∈ B)
    (hy : y ∈ B) : x * y = y * x :=
  congrArg Subtype.val (hB.is_comm.comm (⟨x, hx⟩ : B) ⟨y, hy⟩)

omit [Finite G] in
theorem A3_conj_comm {B : Subgroup G} (hB : IsMulCommutative B) {x g : G} (hx : x ∈ B)
    (hg : g ∈ B) (H : Subgroup G) : GLBConj x (GLBConj g H) = GLBConj g (GLBConj x H) := by
  rw [gLBConj_gLBConj, gLBConj_gLBConj, A3_comm hB hx hg]

omit [Finite G] in
theorem A3_conj_le_iff (g : G) (H T : Subgroup G) :
    GLBConj g H ≤ T ↔ H ≤ GLBConj g⁻¹ T := by
  constructor
  · intro h
    have := gLBConj_mono g⁻¹ h
    rwa [gLBConj_inv_gLBConj] at this
  · intro h
    have := gLBConj_mono g h
    rwa [gLBConj_gLBConj_inv] at this

omit [Finite G] in
theorem A3_gLBConj_commutator (g : G) (X Y : Subgroup G) :
    GLBConj g ⁅X, Y⁆ = ⁅GLBConj g X, GLBConj g Y⁆ :=
  Subgroup.map_commutator X Y (MulAut.conj g⁻¹).toMonoidHom

omit [Finite G] in
theorem A3_conj_centralizer {B : Subgroup G} (hB : IsMulCommutative B) {b g : G} (hb : b ∈ B)
    (hg : g ∈ B) :
    GLBConj g (Subgroup.centralizer ({b} : Set G)) = Subgroup.centralizer ({b} : Set G) :=
  gLBConj_eq_of_mem_normalizer (Subgroup.le_normalizer (by
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    rw [Set.mem_singleton_iff] at hh
    rw [hh]
    exact A3_comm hB hb hg))

omit [Finite G] in
theorem A3_conj_centralizer_B {B : Subgroup G} (hB : IsMulCommutative B) {g : G} (hg : g ∈ B) :
    GLBConj g (Subgroup.centralizer (B : Set G)) = Subgroup.centralizer (B : Set G) :=
  gLBConj_eq_of_mem_normalizer (Subgroup.le_normalizer (by
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    exact A3_comm hB hh hg))

omit [Finite G] in
theorem A3_slb_conj {B : Subgroup G} (hB : IsMulCommutative B) {b g : G} {L : Subgroup G}
    (hb : b ∈ B) (hg : g ∈ B) (h : IsStronglyLocallyOneBalanced 3 B b L) :
    IsStronglyLocallyOneBalanced 3 B b (GLBConj g L) := by
  intro S hS hcop hBS
  have hg' : g⁻¹ ∈ B := B.inv_mem hg
  have hS' : GLBConj g⁻¹ S ≤ Subgroup.normalizer (L : Set G) ⊓ Subgroup.centralizer ({b} : Set G) := by
    have h1 := gLBConj_mono g⁻¹ hS
    rw [gLBConj_inf, normalizer_gLBConj, gLBConj_inv_gLBConj, A3_conj_centralizer hB hb hg'] at h1
    exact h1
  have hcop' : Nat.Coprime 3 (Nat.card (GLBConj g⁻¹ S)) := by
    unfold GLBConj
    rwa [Subgroup.card_map_of_injective (MulAut.conj g⁻¹⁻¹).injective]
  have hBS' : B ⊓ Subgroup.normalizer (L : Set G) ≤ Subgroup.normalizer ((GLBConj g⁻¹ S : Subgroup G) : Set G) := by
    rintro x ⟨hxB, hxN⟩
    have hxN' : x ∈ Subgroup.normalizer ((GLBConj g L : Subgroup G) : Set G) := by
      have hxN0 : x ∈ Subgroup.normalizer (L : Set G) := hxN
      rw [mem_normalizer_iff_gLBConj_eq] at hxN0 ⊢
      rw [A3_conj_comm hB hxB hg, hxN0]
    have h1 := mem_normalizer_iff_gLBConj_eq.1 (hBS ⟨hxB, hxN'⟩)
    rw [mem_normalizer_iff_gLBConj_eq, A3_conj_comm hB hxB hg', h1]
  have := h _ hS' hcop' hBS'
  have h2 := gLBConj_mono g this
  rw [A3_gLBConj_commutator, gLBConj_gLBConj_inv] at h2
  rwa [← glaPPrimeCoreOf_gLBConj] at h2

omit [Finite G] in
theorem A3_bClosure_conj {B : Subgroup G} {g : G} (hg : g ∈ B) (L : Subgroup G) :
    bClosure B (GLBConj g L) = bClosure B L := by
  unfold bClosure
  apply le_antisymm
  · refine iSup_le fun x => iSup_le fun hx => ?_
    rw [gLBConj_gLBConj]
    exact le_iSup_of_le (g * x) (le_iSup_of_le (B.mul_mem hg hx) le_rfl)
  · refine iSup_le fun x => iSup_le fun hx => ?_
    refine le_iSup_of_le (g⁻¹ * x) (le_iSup_of_le (B.mul_mem (B.inv_mem hg) hx) ?_)
    rw [gLBConj_gLBConj, mul_inv_cancel_left]

theorem A3_psiOf_conj_le {B : Subgroup G} (hB : IsMulCommutative B) {b γ : G} (hb : b ∈ B)
    (hγ : γ ∈ B) : GLBConj γ (psiOf 3 B b) ≤ psiOf 3 B b := by
  rw [A3_conj_le_iff]
  refine sSup_le fun L hL => ?_
  rw [← A3_conj_le_iff]
  refine le_sSup ⟨?_, ?_, ?_⟩
  · have := glaPComponent_gLBConj γ hL.1
    rwa [A3_conj_centralizer hB hb hγ] at this
  · intro hs
    apply hL.2.1
    have := A3_slb_conj hB hb (B.inv_mem hγ) hs
    rwa [gLBConj_inv_gLBConj] at this
  · unfold IsInGOne
    rw [A3_bClosure_conj hγ]
    exact hL.2.2

theorem gLBConj_psiStarGroup {B : Subgroup G} (hB : IsMulCommutative B) {β : G} (hβ : β ∈ B) :
    GLBConj β (psiStarGroup 3 B) = psiStarGroup 3 B := by
  have key : ∀ γ ∈ B, GLBConj γ (psiStarGroup 3 B) ≤ psiStarGroup 3 B := by
    intro γ hγ
    rw [A3_conj_le_iff]
    refine iSup_le fun b => iSup_le fun hb => iSup_le fun hb1 => ?_
    rw [← A3_conj_le_iff]
    refine le_trans ?_ (le_iSup_of_le b (le_iSup_of_le hb (le_iSup_of_le hb1 le_rfl)))
    unfold psiStar
    unfold GLBConj
    rw [Subgroup.map_sup, Subgroup.map_sup]
    change GLBConj γ _ ⊔ GLBConj γ _ ⊔ GLBConj γ _ ≤ _
    rw [← glaPPrimeCoreOf_gLBConj, ← glaPPrimeCoreOf_gLBConj, A3_conj_centralizer hB hb hγ,
      A3_conj_centralizer_B hB hγ]
    refine sup_le_sup_right (sup_le_sup_right (A3_psiOf_conj_le hB hb hγ) _) _
  refine le_antisymm (key β hβ) ?_
  have h1 := gLBConj_mono β (key β⁻¹ (B.inv_mem hβ))
  rwa [gLBConj_gLBConj_inv] at h1

theorem glaPPrimeCoreOf_le_psiStarGroup {B : Subgroup G} {b : G} (hb : b ∈ B) (hb1 : b ≠ 1)
    {L : Subgroup G}
    (hL : IsSubnormal L (Subgroup.centralizer ({b} : Set G))) :
    GLAPPrimeCoreOf 3 L ≤ psiStarGroup 3 B := by
  refine (glaPPrimeCoreOf_le_of_isSubnormal 3 hL).trans ?_
  refine le_trans ?_ (le_iSup_of_le b (le_iSup_of_le hb (le_iSup_of_le hb1 le_rfl)))
  exact le_sup_right.trans (le_sup_left : _ ≤ psiStar 3 B b)

theorem gLBConj_lambdaOf_le {B : Subgroup G} {x g : G}
    (hg : g ∈ GLAPLayer 3 (Subgroup.centralizer ({x} : Set G))) :
    GLBConj g (lambdaOf 3 B x) ≤ lambdaOf 3 B x := by
  unfold lambdaOf
  unfold GLBConj
  rw [Subgroup.map_le_iff_le_comap]
  refine sSup_le fun M hM y hy => ?_
  have hn := mem_normalizer_of_mem_glaPLayer (by norm_num : Nat.Prime 3) hM.1 hg
  have h1 : GLBConj g M = M := mem_normalizer_iff_gLBConj_eq.1 hn
  have h2 : (MulAut.conj g⁻¹).toMonoidHom y ∈ GLBConj g M := ⟨y, hy, rfl⟩
  rw [h1] at h2
  exact le_sSup hM h2

end Generic

section YLevel

variable {Y : Type} [Group Y] [Finite Y]

omit [Finite Y] in
theorem A4_fixSub_one {α : MulAut Y} (h : α = 1) : fixSub α = ⊤ := by
  ext y
  simp [fixSub, h]

omit [Finite Y] in
theorem A4_core_top (hcore : GLAPPrimeCore 3 Y = ⊥) : GLAPPrimeCoreOf 3 (⊤ : Subgroup Y) = ⊥ := by
  unfold GLAPPrimeCoreOf GLAPPrimeCore
  rw [← le_bot_iff, Subgroup.map_le_iff_le_comap]
  refine sSup_le fun N hN n hn => ?_
  have hnorm : (N.map (⊤ : Subgroup Y).subtype).Normal :=
    hN.1.map _ (fun y => ⟨⟨y, trivial⟩, rfl⟩)
  have hcard : Nat.Coprime 3 (Nat.card (N.map (⊤ : Subgroup Y).subtype)) := by
    rw [Subgroup.card_map_of_injective (⊤ : Subgroup Y).subtype_injective]
    exact hN.2
  have hle : N.map (⊤ : Subgroup Y).subtype ≤ GLAPPrimeCore 3 Y :=
    le_sSup ⟨hnorm, hcard⟩
  rw [hcore] at hle
  exact hle ⟨n, hn, rfl⟩

theorem core_fixSub_eq_bot (i6 : Input9_2_8) (hY : CFSG.Open.IsQuasisimple Y)
    (hcore : GLAPPrimeCore 3 Y = ⊥) {α : MulAut Y} (hα : IsFieldAutThree α) (hα3 : α ^ 3 = 1) :
    GLAPPrimeCoreOf 3 (fixSub α) = ⊥ := by
  by_cases h1 : α = 1
  · rw [A4_fixSub_one h1]
    exact A4_core_top hcore
  · have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    exact i6 Y hY hcore α hα (orderOf_eq_prime hα3 h1)

theorem A4_ne_bot {X L : Subgroup Y} (h : GLAPComponent 3 X L) : L ≠ ⊥ := by
  intro hL
  have h3 := h.2.2.1
  subst hL
  have hbot : ((⊥ : Subgroup Y).subgroupOf X).map (QuotientGroup.mk' (GLAPPrimeCore 3 ↥X)) = ⊥ := by
    rw [Subgroup.bot_subgroupOf, Subgroup.map_bot]
  rw [hbot] at h3
  obtain ⟨-, hsimple⟩ := h3.2.2
  have := hsimple.toNontrivial
  have hss : Subsingleton (↥(⊥ : Subgroup (↥X ⧸ GLAPPrimeCore 3 ↥X)) ⧸
      Subgroup.center ↥(⊥ : Subgroup (↥X ⧸ GLAPPrimeCore 3 ↥X))) := inferInstance
  exact (not_subsingleton_iff_nontrivial.2 inferInstance) hss

theorem eq_one_of_fixes_component (i5 : Input9_5) (i7 : Input14_5Aut)
    (hY : CFSG.Open.IsQuasisimple Y) (hcore : GLAPPrimeCore 3 Y = ⊥) {α : MulAut Y}
    (hα : IsFieldAutThree α) (hα3 : α ^ 3 = 1)
    {γ : MulAut Y} (hγ : Nat.Coprime 3 (orderOf γ))
    {S : Subgroup Y} (hS : GLAPComponent 3 (fixSub α) S) (hfix : ∀ y ∈ S, γ y = y) : γ = 1 := by
  have hne : S ≠ ⊥ := A4_ne_bot hS
  have hperf : ⁅S, S⁆ = S := glaPComponent_perfect hS
  by_cases h1 : α = 1
  · have hfs : fixSub α = ⊤ := A4_fixSub_one h1
    have hsn : IsSubnormal S ⊤ := by
      have := hS.2.1
      rwa [hfs] at this
    have hST : S = ⊤ := eq_top_of_perfect_subnormal hY hsn hperf hne
    ext y
    have := hfix y (hST ▸ Subgroup.mem_top y)
    simpa using this
  · have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    have hord : orderOf α = 3 := orderOf_eq_prime hα3 h1
    have hSJ : S ≤ GLAPLayer 3 (fixSub α) := le_sSup hS
    have hJne : GLAPLayer 3 (fixSub α) ≠ ⊥ := fun h => hne (le_bot_iff.1 (h ▸ hSJ))
    have hJle : GLAPLayer 3 (fixSub α) ≤ fixSub α := sSup_le fun L hL => hL.1
    have hq : CFSG.Open.IsQuasisimple ↥(GLAPLayer 3 (fixSub α)) :=
      (i7 Y hY hcore α hα hord).resolve_left hJne
    have hsn : IsSubnormal S (GLAPLayer 3 (fixSub α)) :=
      isSubnormal_of_le_of_le hS.2.1 hSJ hJle
    have hSeq : S = GLAPLayer 3 (fixSub α) :=
      eq_of_perfect_subnormal_of_quasisimple hq hSJ hsn hperf hne
    have hmem : γ ∈ Subgroup.zpowers α :=
      i5 Y hY hcore α hα hord hJne γ (fun y hy => hfix y (hSeq ▸ hy))
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hmem
    have h3 : (α ^ k) ^ 3 = 1 := by
      rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hα3, one_zpow]
    have hd : orderOf (α ^ k) ∣ 3 := orderOf_dvd_of_pow_eq_one h3
    have : orderOf (α ^ k) = 1 :=
      Nat.Coprime.eq_one_of_dvd (Nat.Coprime.symm hγ) hd
    exact orderOf_eq_one_iff.1 this

end YLevel

section BarLevel

variable {G : Type} [Group G] [Finite G]

theorem isQuasisimple_barOf {X L : Subgroup G} (hL : GLAPComponent 3 X L) :
    CFSG.Open.IsQuasisimple (barOf 3 L) := by
  have hcomp : IsComponentOf (barX 3 X L) ⊤ := hL.2.2.1
  exact CFSG.ComponentClassification.Components.quasisimple_of_equiv
    (quotEquivBarX Nat.prime_three hL.1 hL.2.1) hcomp.2.2

theorem pPrimeCore_barOf_eq_bot (p : ℕ) (hp : p.Prime) (L : Subgroup G) :
    GLAPPrimeCore p (barOf p L) = ⊥ := by
  have : Fact p.Prime := ⟨hp⟩
  exact CFSG.pPrimeCore_quotient_pPrimeCore_eq_bot p

omit [Finite G] in
theorem barAut_eq_one_iff {L : Subgroup G} {g : G} (hg : g ∈ Subgroup.normalizer (L : Set G)) :
    barAut 3 L ⟨g, hg⟩ = 1 ↔ ⁅L, Subgroup.zpowers g⁆ ≤ GLAPPrimeCoreOf 3 L := by
  have hmem : ∀ {x : G} (hx : x ∈ L), x ∈ GLAPPrimeCoreOf 3 L ↔
      (⟨x, hx⟩ : ↥L) ∈ GLAPPrimeCore 3 ↥L := by
    intro x hx
    constructor
    · rintro ⟨y, hy, hyx⟩
      have : y = ⟨x, hx⟩ := Subtype.ext hyx
      exact this ▸ hy
    · intro h
      exact ⟨⟨x, hx⟩, h, rfl⟩
  constructor
  · intro h
    refine Subgroup.commutator_le.2 fun a ha b hb => ?_
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 hb
    have hgn : g ^ n ∈ Subgroup.normalizer (L : Set G) := Subgroup.zpow_mem _ hg n
    have h1 : barAut 3 L ⟨g ^ n, hgn⟩ = 1 := by
      have : (⟨g ^ n, hgn⟩ : ↥(Subgroup.normalizer (L : Set G))) = ⟨g, hg⟩ ^ n :=
        Subtype.ext (by simp)
      rw [this, map_zpow, h, one_zpow]
    have h2 := congrArg (fun φ => φ (QuotientGroup.mk (⟨a⁻¹, L.inv_mem ha⟩ : ↥L))) h1
    simp only [MulAut.one_apply] at h2
    rw [barAut_mk] at h2
    have h5 := QuotientGroup.eq.1 h2.symm
    have h3 : a * (g ^ n * a⁻¹ * (g ^ n)⁻¹) ∈ L :=
      L.mul_mem ha ((Subgroup.mem_normalizer_iff.1 hgn a⁻¹).1 (L.inv_mem ha))
    have e : (⟨a * (g ^ n * a⁻¹ * (g ^ n)⁻¹), h3⟩ : ↥L) =
        (⟨a⁻¹, L.inv_mem ha⟩ : ↥L)⁻¹ * L.normalizerMonoidHom ⟨g ^ n, hgn⟩ ⟨a⁻¹, L.inv_mem ha⟩ :=
      Subtype.ext (by
        show a * (g ^ n * a⁻¹ * (g ^ n)⁻¹) = a⁻¹⁻¹ * (g ^ n * a⁻¹ * (g ^ n)⁻¹)
        simp)
    have h4 := (hmem h3).2 (e ▸ h5)
    rw [commutatorElement_def]
    simpa [mul_assoc] using h4
  · intro h
    ext y
    induction y using QuotientGroup.induction_on with | H z => ?_
    rw [barAut_mk]
    simp only [MulAut.one_apply]
    rw [QuotientGroup.eq]
    have hc := h (Subgroup.commutator_mem_commutator (L.inv_mem z.2) (Subgroup.mem_zpowers g))
    rw [commutatorElement_def] at hc
    have hc' := (GLAPPrimeCoreOf 3 L).inv_mem hc
    have hx : (g * (z : G) * g⁻¹)⁻¹ * z ∈ L :=
      L.mul_mem (L.inv_mem ((Subgroup.mem_normalizer_iff.1 hg z).1 z.2)) z.2
    have e : ((L.normalizerMonoidHom ⟨g, hg⟩ z)⁻¹ * z : ↥L) =
        ⟨(g * (z : G) * g⁻¹)⁻¹ * z, hx⟩ := Subtype.ext rfl
    rw [e]
    refine (hmem hx).1 ?_
    convert hc' using 1
    simp [mul_assoc]

omit [Finite G] in
theorem barAut_conj {L : Subgroup G} {l : G} (hl : l ∈ L)
    (hlN : l ∈ Subgroup.normalizer (L : Set G)) :
    barAut 3 L ⟨l, hlN⟩ = MulAut.conj (QuotientGroup.mk' (GLAPPrimeCore 3 ↥L) ⟨l, hl⟩) := by
  ext z
  obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective z
  rw [barAut_mk]
  change QuotientGroup.mk (L.normalizerMonoidHom ⟨l, hlN⟩ y) =
    QuotientGroup.mk (⟨l, hl⟩ * y * ⟨l, hl⟩⁻¹)
  congr 1

omit [Finite G] in
theorem A6a_le_primeCore {p : ℕ} {Z N : Subgroup G} (hNZ : N ≤ Z) (hn : (N.subgroupOf Z).Normal)
    (hcop : Nat.Coprime p (Nat.card N)) : N ≤ GLAPPrimeCoreOf p Z := by
  have hcop' : Nat.Coprime p (Nat.card (N.subgroupOf Z)) := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hNZ).toEquiv]
    exact hcop
  intro y hy
  exact ⟨⟨y, hNZ hy⟩,
    le_sSup (show N.subgroupOf Z ∈ {N : Subgroup ↥Z | N.Normal ∧ Nat.Coprime p (Nat.card N)} from
      ⟨hn, hcop'⟩) ((Subgroup.mem_subgroupOf).2 hy), rfl⟩

omit [Finite G] in
theorem A6a_normalizer_core {L : Subgroup G} {x : G} (hxN : x ∈ Subgroup.normalizer (L : Set G)) :
    x ∈ Subgroup.normalizer (GLAPPrimeCoreOf 3 L : Set G) := by
  rw [mem_normalizer_iff_gLBConj_eq, ← glaPPrimeCoreOf_gLBConj,
    mem_normalizer_iff_gLBConj_eq.1 hxN]

theorem exists_lift_fixed {L : Subgroup G} {x : G} (hxN : x ∈ Subgroup.normalizer (L : Set G))
    (hx3 : x ^ 3 = 1) {y : barOf 3 L} (hy : barAut 3 L ⟨x, hxN⟩ y = y) :
    ∃ (l : G) (hl : l ∈ L), l ∈ Subgroup.centralizer ({x} : Set G) ∧
      QuotientGroup.mk' (GLAPPrimeCore 3 ↥L) ⟨l, hl⟩ = y := by
  obtain ⟨l0, rfl⟩ := QuotientGroup.mk'_surjective (GLAPPrimeCore 3 ↥L) y
  have hcop := A1_coprime_card_core 3 L
  have hy' : QuotientGroup.mk (L.normalizerMonoidHom ⟨x, hxN⟩ l0) =
      (QuotientGroup.mk l0 : barOf 3 L) := by
    have := hy
    rw [QuotientGroup.mk'_apply, barAut_mk] at this
    exact this
  have h1 := QuotientGroup.eq.1 hy'.symm
  have h1' : (l0 : G)⁻¹ * (x * (l0 : G) * x⁻¹) ∈ GLAPPrimeCoreOf 3 L :=
    ⟨_, h1, rfl⟩
  obtain ⟨n, hn, hfix⟩ := exists_fixed_in_coset Nat.prime_three hx3 (A6a_normalizer_core hxN) hcop h1'
  have hnL : n ∈ L := Subgroup.map_subtype_le _ hn
  refine ⟨(l0 : G) * n, L.mul_mem l0.2 hnL, ?_, ?_⟩
  · rw [Subgroup.mem_centralizer_singleton_iff]
    have := hfix
    rw [mul_inv_eq_iff_eq_mul] at this
    exact this.symm
  · have e : (⟨(l0 : G) * n, L.mul_mem l0.2 hnL⟩ : ↥L) = l0 * ⟨n, hnL⟩ := Subtype.ext rfl
    rw [e, map_mul]
    have : QuotientGroup.mk' (GLAPPrimeCore 3 ↥L) ⟨n, hnL⟩ = 1 := by
      rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
      obtain ⟨n', hn', rfl⟩ := hn
      exact hn'
    rw [this, mul_one]

theorem barX_inf_centralizer_eq_fixSub {L : Subgroup G} {x : G}
    (hxN : x ∈ Subgroup.normalizer (L : Set G)) (hx3 : x ^ 3 = 1) :
    barX 3 L (L ⊓ Subgroup.centralizer ({x} : Set G)) = fixSub (barAut 3 L ⟨x, hxN⟩) := by
  ext y
  constructor
  · rintro ⟨z, hz, rfl⟩
    have hz' := (Subgroup.mem_subgroupOf).1 hz
    have hcx : x * (z : G) = (z : G) * x :=
      Subgroup.mem_centralizer_singleton_iff.1 hz'.2 |>.symm
    show barAut 3 L ⟨x, hxN⟩ (QuotientGroup.mk' _ z) = QuotientGroup.mk' _ z
    rw [QuotientGroup.mk'_apply, barAut_mk]
    congr 1
    apply Subtype.ext
    show x * (z : G) * x⁻¹ = z
    rw [hcx]; group
  · intro hy
    obtain ⟨l, hl, hlx, hly⟩ := exists_lift_fixed hxN hx3 hy
    exact ⟨⟨l, hl⟩, (Subgroup.mem_subgroupOf).2 ⟨hl, hlx⟩, hly⟩

theorem barX_primeCore_eq_bot {L : Subgroup G} {x : G}
    (hxN : x ∈ Subgroup.normalizer (L : Set G)) (hx3 : x ^ 3 = 1)
    (hcore : GLAPPrimeCoreOf 3 (fixSub (barAut 3 L ⟨x, hxN⟩)) = ⊥) :
    barX 3 L (GLAPPrimeCoreOf 3 (L ⊓ Subgroup.centralizer ({x} : Set G))) = ⊥ := by
  set X0 := L ⊓ Subgroup.centralizer ({x} : Set G) with hX0
  let g : ↥X0 →* barOf 3 L :=
    (QuotientGroup.mk' (GLAPPrimeCore 3 ↥L)).comp (Subgroup.inclusion inf_le_left)
  have hrange : g.range = fixSub (barAut 3 L ⟨x, hxN⟩) := by
    rw [← barX_inf_centralizer_eq_fixSub hxN hx3]
    ext y
    constructor
    · rintro ⟨z, rfl⟩
      exact ⟨Subgroup.inclusion inf_le_left z, (Subgroup.mem_subgroupOf).2 z.2, rfl⟩
    · rintro ⟨z, hz, rfl⟩
      exact ⟨⟨z, (Subgroup.mem_subgroupOf).1 hz⟩, rfl⟩
  set T' := GLAPPrimeCore 3 ↥X0 with hT'
  set M : Subgroup (barOf 3 L) := T'.map g with hM
  have hMnorm : (M.subgroupOf (fixSub (barAut 3 L ⟨x, hxN⟩))).Normal := by
    refine ⟨fun n hn k => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    obtain ⟨t, ht, htn⟩ := hn
    have hk : (k : barOf 3 L) ∈ g.range := by rw [hrange]; exact k.2
    obtain ⟨z, hz⟩ := hk
    refine ⟨z * t * z⁻¹, (GLAPPrimeCore.normal 3 ↥X0).conj_mem t ht z, ?_⟩
    simp [hz, htn]
  have hMle : M ≤ fixSub (barAut 3 L ⟨x, hxN⟩) := by
    rintro _ ⟨t, -, rfl⟩
    rw [← hrange]
    exact ⟨t, rfl⟩
  have hMcop : Nat.Coprime 3 (Nat.card M) :=
    (coprime_card_gLAPPrimeCore_aux 3 ↥X0).coprime_dvd_right (Subgroup.card_map_dvd T' g)
  have hMbot : M ≤ ⊥ := hcore ▸ A6a_le_primeCore hMle hMnorm hMcop
  rw [eq_bot_iff]
  rintro _ ⟨z, hz, rfl⟩
  have hz' := (Subgroup.mem_subgroupOf).1 hz
  obtain ⟨t, ht, htz⟩ := hz'
  have hzX0 : (z : G) ∈ X0 := Subgroup.map_subtype_le _ ⟨t, ht, htz⟩
  have : g t = QuotientGroup.mk' _ z := by
    have htz' : (t : G) = z := htz
    show QuotientGroup.mk' _ (Subgroup.inclusion inf_le_left t) = _
    congr 1
    exact Subtype.ext htz'
  have h2 : QuotientGroup.mk' _ z ∈ M := ⟨t, ht, this⟩
  exact hMbot h2

omit [Finite G] in
theorem A6b_glaPComponent_of_core_bot {p : ℕ} {X S : Subgroup G}
    (hcore : GLAPPrimeCore p ↥X = ⊥) (hSX : S ≤ X) (hsn : IsSubnormal S X)
    (hq : CFSG.Open.IsQuasisimple ↥S) : GLAPComponent p X S := by
  have hinj : Function.Injective (QuotientGroup.mk' (GLAPPrimeCore p ↥X)) := by
    rw [← MonoidHom.ker_eq_bot_iff, QuotientGroup.ker_mk', hcore]
  refine ⟨hSX, hsn, ⟨le_top, A2_isSubnormal_barX_top p hsn, ?_⟩, ?_⟩
  · exact A2_isQuasisimple_of_mulEquiv
      ((Subgroup.subgroupOfEquivOfLe hSX).symm.trans
        (Subgroup.equivMapOfInjective (S.subgroupOf X) _ hinj)) hq
  · intro J hJ _ heq
    have h1 : J.subgroupOf X = S.subgroupOf X := Subgroup.map_injective hinj heq
    have h2 : S ≤ J := fun y hy => by
      have : (⟨y, hSX hy⟩ : ↥X) ∈ S.subgroupOf X := (Subgroup.mem_subgroupOf).2 hy
      rw [← h1] at this
      exact (Subgroup.mem_subgroupOf).1 this
    exact absurd h2 (not_le_of_gt hJ)

@[expose] def A6b_g (L X0 : Subgroup G) (h : X0 ≤ L) : ↥X0 →* barOf 3 L :=
  (QuotientGroup.mk' (GLAPPrimeCore 3 ↥L)).comp (Subgroup.inclusion h)

omit [Finite G] in
theorem A6b_g_eq_one_iff {L X0 : Subgroup G} (h : X0 ≤ L) (z : ↥X0) :
    A6b_g L X0 h z = 1 ↔ (z : G) ∈ GLAPPrimeCoreOf 3 L := by
  show QuotientGroup.mk' (GLAPPrimeCore 3 ↥L) (Subgroup.inclusion h z) = 1 ↔ _
  rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
  constructor
  · intro hz
    exact ⟨_, hz, rfl⟩
  · rintro ⟨y, hy, hyz⟩
    have : y = Subgroup.inclusion h z := Subtype.ext hyz
    exact this ▸ hy

theorem A6b_ker_g {L X0 : Subgroup G} (h : X0 ≤ L)
    (hbot : barX 3 L (GLAPPrimeCoreOf 3 X0) = ⊥) :
    (A6b_g L X0 h).ker = GLAPPrimeCore 3 ↥X0 := by
  apply le_antisymm
  · intro z hz
    have hzR : (z : G) ∈ GLAPPrimeCoreOf 3 L := (A6b_g_eq_one_iff h z).1 hz
    set N : Subgroup G := GLAPPrimeCoreOf 3 L ⊓ X0 with hN
    have hNX : N ≤ X0 := inf_le_right
    have hkerN : N.subgroupOf X0 = (A6b_g L X0 h).ker := by
      ext w
      rw [Subgroup.mem_subgroupOf, MonoidHom.mem_ker, A6b_g_eq_one_iff]
      exact ⟨fun hw => hw.1, fun hw => ⟨hw, w.2⟩⟩
    have hnorm : (N.subgroupOf X0).Normal := hkerN ▸ MonoidHom.normal_ker _
    have hcop : Nat.Coprime 3 (Nat.card N) :=
      (A1_coprime_card_core 3 L).coprime_dvd_right (Subgroup.card_dvd_of_le inf_le_left)
    have hzN : (z : G) ∈ GLAPPrimeCoreOf 3 X0 :=
      A6a_le_primeCore hNX hnorm hcop ⟨hzR, z.2⟩
    obtain ⟨t, ht, htz⟩ := hzN
    have : t = z := Subtype.ext htz
    exact this ▸ ht
  · intro t ht
    rw [MonoidHom.mem_ker, A6b_g_eq_one_iff]
    have hmem : QuotientGroup.mk' (GLAPPrimeCore 3 ↥L) (Subgroup.inclusion h t) ∈
        barX 3 L (GLAPPrimeCoreOf 3 X0) :=
      ⟨Subgroup.inclusion h t, (Subgroup.mem_subgroupOf).2 ⟨t, ht, rfl⟩, rfl⟩
    rw [hbot] at hmem
    have h1 : A6b_g L X0 h t = 1 := hmem
    exact (A6b_g_eq_one_iff h t).1 h1

theorem barX_glaPComponent {L : Subgroup G} {x : G}
    (hxN : x ∈ Subgroup.normalizer (L : Set G)) (hx3 : x ^ 3 = 1)
    (hcore : GLAPPrimeCoreOf 3 (fixSub (barAut 3 L ⟨x, hxN⟩)) = ⊥) {J : Subgroup G}
    (hJ : GLAPComponent 3 (L ⊓ Subgroup.centralizer ({x} : Set G)) J) :
    GLAPComponent 3 (fixSub (barAut 3 L ⟨x, hxN⟩)) (barX 3 L J) := by
  set X0 := L ⊓ Subgroup.centralizer ({x} : Set G) with hX0
  have hX0L : X0 ≤ L := inf_le_left
  have hbot := barX_primeCore_eq_bot hxN hx3 hcore
  have hker := A6b_ker_g hX0L hbot
  have hrange : barX 3 L X0 = fixSub (barAut 3 L ⟨x, hxN⟩) :=
    barX_inf_centralizer_eq_fixSub hxN hx3
  have hJX0 : J ≤ X0 := hJ.1
  have hcore' : GLAPPrimeCore 3 ↥(fixSub (barAut 3 L ⟨x, hxN⟩)) = ⊥ :=
    (Subgroup.map_eq_bot_iff_of_injective _ (Subgroup.subtype_injective _)).1 hcore
  have hSX : barX 3 L J ≤ fixSub (barAut 3 L ⟨x, hxN⟩) := hrange ▸ A2_barX_mono 3 hJX0
  have hsn : IsSubnormal (barX 3 L J) (fixSub (barAut 3 L ⟨x, hxN⟩)) := by
    have h1 := CFSG.LocalAnalysis.GLTheoremB.isSubnormal_comap' L.subtype hJ.2.1
    have h2 := CFSG.LocalAnalysis.GLTheoremB.isSubnormal_map'
      (QuotientGroup.mk' (GLAPPrimeCore 3 ↥L)) h1
    rw [← hrange]
    exact h2
  refine A6b_glaPComponent_of_core_bot hcore' hSX hsn ?_
  set T' := GLAPPrimeCore 3 ↥X0 with hT'
  let ψ : (↥X0 ⧸ T') →* barOf 3 L := QuotientGroup.lift T' (A6b_g L X0 hX0L) hker.ge
  have hψ : ∀ a : ↥X0, ψ (QuotientGroup.mk a) = A6b_g L X0 hX0L a := fun a => rfl
  have hinj : Function.Injective ψ := by
    intro a b hab
    induction a using QuotientGroup.induction_on with | H a => ?_
    induction b using QuotientGroup.induction_on with | H b => ?_
    rw [hψ, hψ] at hab
    apply QuotientGroup.eq.2
    rw [← hker, MonoidHom.mem_ker, map_mul, map_inv, hab, inv_mul_cancel]
  have hmap : (barX 3 X0 J).map ψ = barX 3 L J := by
    ext y
    constructor
    · rintro ⟨_, ⟨z, hz, rfl⟩, rfl⟩
      exact ⟨⟨z, hX0L z.2⟩, (Subgroup.mem_subgroupOf).2 ((Subgroup.mem_subgroupOf).1 hz), rfl⟩
    · rintro ⟨w, hw, rfl⟩
      have hwJ : (w : G) ∈ J := (Subgroup.mem_subgroupOf).1 hw
      exact ⟨QuotientGroup.mk ⟨w, hJX0 hwJ⟩,
        ⟨⟨w, hJX0 hwJ⟩, (Subgroup.mem_subgroupOf).2 hwJ, rfl⟩, rfl⟩
  have hq : CFSG.Open.IsQuasisimple ↥(barX 3 X0 J) := hJ.2.2.1.2.2
  exact A2_isQuasisimple_of_mulEquiv
    ((Subgroup.equivMapOfInjective (barX 3 X0 J) ψ hinj).trans (MulEquiv.subgroupCongr hmap)) hq

theorem barAut_eq_one_of_centralizes (i5 : Input9_5) (i6 : Input9_2_8) (i7 : Input14_5Aut)
    {m : ℕ} {B : Subgroup G} {b : G} {L : Subgroup G} {x : G} (H : Hyp53 m B b L x) {c : G}
    (hcN : c ∈ Subgroup.normalizer (L : Set G)) (hcop : Nat.Coprime 3 (orderOf c))
    {J : Subgroup G} (hJ : GLAPComponent 3 (L ⊓ Subgroup.centralizer ({x} : Set G)) J)
    (hcomm : ⁅J, Subgroup.zpowers c⁆ ≤ GLAPPrimeCoreOf 3 (L ⊓ Subgroup.centralizer ({x} : Set G))) :
    barAut 3 L ⟨c, hcN⟩ = 1 := by
  have hx3 : x ^ 3 = 1 := H.hB.1.1.2 x H.hx
  have hY := isQuasisimple_barOf H.hL
  have hcore := pPrimeCore_barOf_eq_bot 3 Nat.prime_three L
  set α := barAut 3 L ⟨x, H.hxN⟩ with hα
  have hα3 : α ^ 3 = 1 := by
    rw [hα, ← map_pow]
    have : (⟨x, H.hxN⟩ : ↥(Subgroup.normalizer (L : Set G))) ^ 3 = 1 := Subtype.ext hx3
    rw [this, map_one]
  have hC0 := core_fixSub_eq_bot i6 hY hcore H.hxF hα3
  have hS := barX_glaPComponent H.hxN hx3 hC0 hJ
  have hγ : Nat.Coprime 3 (orderOf (barAut 3 L ⟨c, hcN⟩)) := by
    refine hcop.coprime_dvd_right ?_
    have h1 := orderOf_map_dvd (barAut 3 L) (⟨c, hcN⟩ : ↥(Subgroup.normalizer (L : Set G)))
    have h2 : orderOf (⟨c, hcN⟩ : ↥(Subgroup.normalizer (L : Set G))) = orderOf c :=
      Subgroup.orderOf_mk c hcN
    rwa [h2] at h1
  have hbot := barX_primeCore_eq_bot H.hxN hx3 hC0
  refine eq_one_of_fixes_component i5 i7 hY hcore H.hxF hα3 hγ hS ?_
  rintro y ⟨z, hz, rfl⟩
  have hzJ : (z : G) ∈ J := (Subgroup.mem_subgroupOf).1 hz
  have hzL : (z : G) ∈ L := z.2
  show barAut 3 L ⟨c, hcN⟩ (QuotientGroup.mk' _ z) = QuotientGroup.mk' _ z
  rw [QuotientGroup.mk'_apply, barAut_mk]
  symm
  rw [QuotientGroup.eq]
  have hc1 := hcomm (Subgroup.commutator_mem_commutator ((J.inv_mem hzJ)) (Subgroup.mem_zpowers c))
  rw [commutatorElement_def] at hc1
  have hLmem : (z : G)⁻¹ * (c * z * c⁻¹) ∈ L :=
    L.mul_mem (L.inv_mem hzL) ((Subgroup.mem_normalizer_iff.1 hcN z).1 hzL)
  have hc1' : (z : G)⁻¹ * (c * z * c⁻¹) ∈
      GLAPPrimeCoreOf 3 (L ⊓ Subgroup.centralizer ({x} : Set G)) := by
    simpa [mul_assoc] using hc1
  have hbarmem : QuotientGroup.mk' (GLAPPrimeCore 3 ↥L) (⟨_, hLmem⟩ : ↥L) ∈
      barX 3 L (GLAPPrimeCoreOf 3 (L ⊓ Subgroup.centralizer ({x} : Set G))) :=
    ⟨⟨_, hLmem⟩, (Subgroup.mem_subgroupOf).2 hc1', rfl⟩
  rw [hbot, Subgroup.mem_bot, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hbarmem
  have e : (z : ↥L)⁻¹ * L.normalizerMonoidHom ⟨c, hcN⟩ z =
      ⟨(z : G)⁻¹ * (c * z * c⁻¹), hLmem⟩ := Subtype.ext rfl
  rw [e]
  exact hbarmem

theorem le_sup_core_of_trivial_action {m : ℕ} {B : Subgroup G} {b : G} {L : Subgroup G} {x : G}
    (H : Hyp53 m B b L x) (hxtriv : ⁅L, Subgroup.zpowers x⁆ ≤ GLAPPrimeCoreOf 3 L)
    {J : Subgroup G} (hJ : GLAPComponent 3 (L ⊓ Subgroup.centralizer ({x} : Set G)) J) :
    L ≤ J ⊔ GLAPPrimeCoreOf 3 L := by
  have hx3 : x ^ 3 = 1 := H.hB.1.1.2 x H.hx
  have hY := isQuasisimple_barOf H.hL
  have hcore := pPrimeCore_barOf_eq_bot 3 Nat.prime_three L
  have hα1 : barAut 3 L ⟨x, H.hxN⟩ = 1 := (barAut_eq_one_iff H.hxN).2 hxtriv
  have hfix : fixSub (barAut 3 L ⟨x, H.hxN⟩) = ⊤ := by
    rw [eq_top_iff]
    intro y _
    show barAut 3 L ⟨x, H.hxN⟩ y = y
    rw [hα1]; rfl
  have hC0 : GLAPPrimeCoreOf 3 (fixSub (barAut 3 L ⟨x, H.hxN⟩)) = ⊥ := by
    rw [hfix]
    have h1 := glaPPrimeCore_map_iso 3 (Subgroup.topEquiv : (⊤ : Subgroup (barOf 3 L)) ≃* barOf 3 L)
    rw [hcore] at h1
    have h2 : GLAPPrimeCore 3 ↥(⊤ : Subgroup (barOf 3 L)) = ⊥ := by
      rw [eq_bot_iff]
      intro t ht
      have : (Subgroup.topEquiv : (⊤ : Subgroup (barOf 3 L)) ≃* barOf 3 L) t ∈
          (GLAPPrimeCore 3 ↥(⊤ : Subgroup (barOf 3 L))).map
            (Subgroup.topEquiv : (⊤ : Subgroup (barOf 3 L)) ≃* barOf 3 L).toMonoidHom := ⟨t, ht, rfl⟩
      rw [h1, Subgroup.mem_bot] at this
      exact (Subgroup.mem_bot).2 (Subgroup.topEquiv.injective (this.trans (map_one _).symm))
    unfold GLAPPrimeCoreOf
    rw [h2, Subgroup.map_bot]
  have hS := barX_glaPComponent H.hxN hx3 hC0 hJ
  rw [hfix] at hS
  have hperf := glaPComponent_perfect hS
  have hne : barX 3 L J ≠ ⊥ := A4_ne_bot hS
  have hsub : IsSubnormal (barX 3 L J) ⊤ := hS.2.1
  have htop := eq_top_of_perfect_subnormal hY hsub hperf hne
  intro l hl
  have hmem : QuotientGroup.mk' (GLAPPrimeCore 3 ↥L) ⟨l, hl⟩ ∈ barX 3 L J := by
    rw [htop]; exact Subgroup.mem_top _
  obtain ⟨j, hj, hjl⟩ := hmem
  have hjJ : (j : G) ∈ J := (Subgroup.mem_subgroupOf).1 hj
  have h1 : (j⁻¹ * ⟨l, hl⟩ : ↥L) ∈ GLAPPrimeCore 3 ↥L := by
    rw [← QuotientGroup.eq]
    exact hjl
  have h2 : (j : G)⁻¹ * l ∈ GLAPPrimeCoreOf 3 L := ⟨_, h1, rfl⟩
  have : l = (j : G) * ((j : G)⁻¹ * l) := by simp
  rw [this]
  exact Subgroup.mul_mem_sup hjJ h2

end BarLevel

section Reduction

variable {G : Type} [Group G] [Finite G]

theorem exists_cspec (h18 : Input18_3_4) {m : ℕ} {B : Subgroup G} {b : G} {L : Subgroup G} {x : G}
    (H : Hyp53 m B b L x) {J : Subgroup G}
    (hJ : GLAPComponent 3 (L ⊓ Subgroup.centralizer ({x} : Set G)) J) :
    ∃ 𝒞 : Set (Subgroup G), CSpec b x J 𝒞 := by
  have hcomm : ∀ u ∈ B, ∀ v ∈ B, u * v = v * u := fun u hu v hv =>
    H.hB.1.1.1.is_comm.comm ⟨u, hu⟩ ⟨v, hv⟩ |> fun h => congrArg Subtype.val h
  have hbx : b ∈ Subgroup.centralizer ({x} : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    rw [Set.mem_singleton_iff] at hh
    subst hh
    exact (hcomm _ H.hx _ H.hb)
  have hEX : Subgroup.zpowers b ≤ Subgroup.centralizer ({x} : Set G) :=
    (Subgroup.zpowers_le).2 hbx
  have hEab : IsElemAbelian 3 (Subgroup.zpowers b) := by
    refine ⟨⟨⟨?_⟩⟩, ?_⟩
    · rintro ⟨_, m, rfl⟩ ⟨_, n, rfl⟩
      exact Subtype.ext ((Commute.refl b).zpow_zpow m n).eq
    · rintro _ ⟨n, rfl⟩
      have hb3 : b ^ 3 = 1 := H.hB.1.1.2 b H.hb
      rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hb3, one_zpow]
  have hCb : ∀ g ∈ Subgroup.centralizer ({b} : Set G),
      g ∈ Subgroup.centralizer (Subgroup.zpowers b : Set G) := by
    intro g hg
    rw [Subgroup.mem_centralizer_iff] at hg ⊢
    rintro _ ⟨n, rfl⟩
    exact ((show Commute b g from hg b rfl).zpow_left n).eq
  have hLE : L ≤ Subgroup.centralizer (Subgroup.zpowers b : Set G) :=
    fun g hg => hCb g (H.hL.1 hg)
  have hCE : Subgroup.centralizer (Subgroup.zpowers b : Set G) ≤
      Subgroup.centralizer ({b} : Set G) :=
    Subgroup.centralizer_le (by simp)
  set M := Subgroup.centralizer ({x} : Set G) ⊓
    Subgroup.centralizer (Subgroup.zpowers b : Set G) with hM
  have hHM : L ⊓ Subgroup.centralizer ({x} : Set G) ≤ M :=
    fun g hg => ⟨hg.2, hLE hg.1⟩
  have hsn1 : IsSubnormal (L ⊓ M) (Subgroup.centralizer ({b} : Set G) ⊓ M) :=
    isSubnormal_inf H.hL.2.1 M
  have e1 : L ⊓ M = L ⊓ Subgroup.centralizer ({x} : Set G) := by
    ext g; constructor
    · rintro ⟨h1, h2, _⟩; exact ⟨h1, h2⟩
    · rintro ⟨h1, h2⟩; exact ⟨h1, h2, hLE h1⟩
  have e2 : Subgroup.centralizer ({b} : Set G) ⊓ M = M :=
    inf_eq_right.2 (fun g hg => hCE hg.2)
  rw [e1, e2] at hsn1
  have hsn : IsSubnormal J M := isSubnormal_trans' hJ.2.1 hsn1
  have hGM : GLAPComponent 3 M J :=
    glaPComponent_of_isSubnormal Nat.prime_three hJ hHM hsn
  exact h18 G (Subgroup.centralizer ({x} : Set G))
    (isKGroup_of_isKProper H.hS.kProper (centralizer_ne_top H.hx1 H.hS)) 3 Nat.prime_three
    (Subgroup.zpowers b) hEX hEab J hGM

theorem K_le_upsilon_of (h18 : Input18_3_4) {m : ℕ} {B : Subgroup G} {b : G} {L : Subgroup G}
    {x : G} (H : Hyp53 m B b L x)
    (hall : ∀ J : Subgroup G,
      GLAPComponent 3 (L ⊓ Subgroup.centralizer ({x} : Set G)) J → ∀ 𝒞 : Set (Subgroup G),
        CSpec b x J 𝒞 → ∀ M ∈ 𝒞, IsUpsilonComponent B x M) :
    (⨆ g ∈ GLAPLayer 3 (Subgroup.centralizer ({x} : Set G)),
        GLBConj g (GLAPLayer 3 (L ⊓ Subgroup.centralizer ({x} : Set G)))) ≤ upsilonOf B x := by
  refine iSup₂_le fun g hg => ?_
  have hmap : GLBConj g (GLAPLayer 3 (L ⊓ Subgroup.centralizer ({x} : Set G))) =
      ⨆ J ∈ {J | GLAPComponent 3 (L ⊓ Subgroup.centralizer ({x} : Set G)) J}, GLBConj g J := by
    unfold GLBConj GLAPLayer
    rw [sSup_eq_iSup, Subgroup.map_iSup]
    refine iSup_congr fun J => ?_
    rw [Subgroup.map_iSup]
  rw [hmap]
  refine iSup₂_le fun J hJ => ?_
  obtain ⟨𝒞, hC⟩ := exists_cspec h18 H hJ
  have h1 : GLBConj g J ≤ ⨆ g ∈ GLAPLayer 3 (Subgroup.centralizer ({x} : Set G)), GLBConj g J :=
    le_iSup₂_of_le g hg le_rfl
  rw [← hC.2.1] at h1
  refine h1.trans (iSup₂_le fun M hM => ?_)
  exact le_sSup (hall J hJ 𝒞 hC M hM)

end Reduction

section CaseOne

variable {G : Type} [Group G] [Finite G]

theorem comm_le_core_of_cspec {m : ℕ} {B : Subgroup G} {b : G} {L : Subgroup G} {x : G}
    (_H : Hyp53 m B b L x) {c : G} (hcN : c ∈ Subgroup.normalizer (L : Set G))
    (hcb : c ∈ Subgroup.centralizer ({b} : Set G))
    (hcx : c ∈ Subgroup.centralizer ({x} : Set G)) {J : Subgroup G}
    (hJ : GLAPComponent 3 (L ⊓ Subgroup.centralizer ({x} : Set G)) J) {𝒞 : Set (Subgroup G)}
    (hC : CSpec b x J 𝒞) {M : Subgroup G} (hM : M ∈ 𝒞)
    (hbad : ⁅M, Subgroup.zpowers c⁆ ≤ GLAPPrimeCoreOf 3 M) :
    ⁅J, Subgroup.zpowers c⁆ ≤ GLAPPrimeCoreOf 3 (L ⊓ Subgroup.centralizer ({x} : Set G)) := by
  set X := Subgroup.centralizer ({x} : Set G) with hX
  set X0 := L ⊓ X with hX0
  have hbc : Commute b c := (Subgroup.mem_centralizer_singleton_iff.1 hcb).symm
  have hall : ∀ M' ∈ 𝒞, ⁅M', Subgroup.zpowers c⁆ ≤ GLAPPrimeCoreOf 3 M' := by
    intro M' hM'
    obtain ⟨e, he, rfl⟩ := hC.2.2.2 M hM M' hM'
    have hec : ∀ k ∈ Subgroup.zpowers c, e * k * e⁻¹ = k := by
      intro k hk
      obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 he
      obtain ⟨r, rfl⟩ := Subgroup.mem_zpowers_iff.1 hk
      have : Commute (b ^ n) (c ^ r) := (hbc.zpow_left n).zpow_right r
      rw [this.eq]; group
    refine Subgroup.commutator_le.2 fun y hy k hk => ?_
    have hy' : e * y * e⁻¹ ∈ M := mem_gLBConj.1 hy
    have h1 : (e * y * e⁻¹) * k * (e * y * e⁻¹)⁻¹ * k⁻¹ ∈ GLAPPrimeCoreOf 3 M := by
      refine hbad ?_
      have := Subgroup.commutator_mem_commutator hy' hk
      rwa [commutatorElement_def] at this
    have h2 : e * (y * k * y⁻¹ * k⁻¹) * e⁻¹ ∈ GLAPPrimeCoreOf 3 M := by
      convert h1 using 1
      have := hec k hk
      have h3 : e * k⁻¹ * e⁻¹ = k⁻¹ := by
        rw [show e * k⁻¹ * e⁻¹ = (e * k * e⁻¹)⁻¹ by group, this]
      calc e * (y * k * y⁻¹ * k⁻¹) * e⁻¹
          = (e * y * e⁻¹) * (e * k * e⁻¹) * (e * y⁻¹ * e⁻¹) * (e * k⁻¹ * e⁻¹) := by group
        _ = _ := by rw [this, h3]; group
    rw [glaPPrimeCoreOf_gLBConj]
    rw [commutatorElement_def]
    exact mem_gLBConj.2 h2
  have hNle : GLAPPrimeCoreOf 3 X ≤ X := Subgroup.map_subtype_le _
  have hNn : ((GLAPPrimeCoreOf 3 X).subgroupOf X).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hNle).2 (le_normalizer_glaPPrimeCoreOf 3 X)
  have hcle : Subgroup.zpowers c ≤ X := Subgroup.zpowers_le.2 hcx
  have hK : ⁅⨆ K ∈ 𝒞, K, Subgroup.zpowers c⁆ ≤ GLAPPrimeCoreOf 3 X :=
    commutator_iSup_le_of_normal hNn (fun K hK => (hC.1 K hK).1) hcle fun K hK =>
      (hall K hK).trans (glaPPrimeCoreOf_le_of_isSubnormal 3 (hC.1 K hK).2.1)
  have hJle : J ≤ ⨆ K ∈ 𝒞, K := by
    rw [hC.2.1]
    refine le_iSup₂_of_le 1 (one_mem _) ?_
    rw [gLBConj_one]
  have h1 : ⁅J, Subgroup.zpowers c⁆ ≤ GLAPPrimeCoreOf 3 X :=
    (Subgroup.commutator_mono hJle le_rfl).trans hK
  have h2 : ⁅J, Subgroup.zpowers c⁆ ≤ X0 := by
    refine Subgroup.commutator_le.2 fun j hj k hk => ?_
    have hjX0 : j ∈ X0 := hJ.1 hj
    have hkN : k ∈ Subgroup.normalizer (L : Set G) :=
      (Subgroup.zpowers_le.2 hcN) hk
    have hkX : k ∈ X := hcle hk
    rw [commutatorElement_def]
    refine ⟨?_, ?_⟩
    · have := L.mul_mem hjX0.1 ((Subgroup.mem_normalizer_iff.1 hkN j⁻¹).1 (L.inv_mem hjX0.1))
      simpa [mul_assoc] using this
    · have := X.mul_mem (hjX0.2) (X.mul_mem (X.mul_mem hkX (X.inv_mem hjX0.2)) (X.inv_mem hkX))
      simpa [mul_assoc] using this
  intro y hy
  have := A1_inf_le 3 X X0 ⟨h1 hy, h2 hy⟩
  rwa [inf_eq_right.2 (inf_le_right : X0 ≤ X)] at this

omit [Finite G] in
theorem A8_conj_mem_core {p : ℕ} {J : Subgroup G} {g : G}
    (hg : g ∈ Subgroup.normalizer (J : Set G)) {y : G} (hy : y ∈ GLAPPrimeCoreOf p J) :
    g * y * g⁻¹ ∈ GLAPPrimeCoreOf p J := by
  obtain ⟨y', hy', rfl⟩ := hy
  refine ⟨J.normalizerMonoidHom ⟨g, hg⟩ y',
    map_gLAPPrimeCore_le p (J.normalizerMonoidHom ⟨g, hg⟩) ⟨y', hy', rfl⟩, ?_⟩
  rfl

omit [Finite G] in
theorem A8_mem_kerB {L D : Subgroup G} {d : G} (hd : d ∈ D)
    (hdN : d ∈ Subgroup.normalizer (L : Set G)) (h1 : barAut 3 L ⟨d, hdN⟩ = 1) :
    d ∈ kerB 3 D L := by
  refine ⟨hd, hdN, ?_, fun y hy => ?_⟩
  · rw [Subgroup.mem_normalizer_iff]
    intro y
    refine ⟨fun hy => A8_conj_mem_core hdN hy, fun hy => ?_⟩
    have := A8_conj_mem_core (inv_mem hdN) hy
    simpa [mul_assoc] using this
  · have := (barAut_eq_one_iff hdN).1 h1
      (Subgroup.commutator_mem_commutator hy (Subgroup.mem_zpowers d))
    rwa [commutatorElement_def] at this

theorem A8_card_map_of_inj {Γ Δ : Type*} [Group Γ] [Group Δ] (f : Γ →* Δ) (K : Subgroup Γ)
    (h : ∀ k ∈ K, f k = 1 → k = 1) : Nat.card (K.map f) = Nat.card K := by
  have hinj : Function.Injective (f.comp K.subtype) := by
    rw [injective_iff_map_eq_one]
    intro k hk
    exact Subtype.ext (h k.1 k.2 hk)
  have hr : (f.comp K.subtype).range = K.map f := by
    ext y
    simp [MonoidHom.mem_range, Subgroup.mem_map]
  rw [← hr]
  exact (Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv).symm

theorem case1_exists_c (i1 : Input19_1_2) (i3 : Input19_7_3b) (i4 : Input7_AutQuotAbelian)
    {m : ℕ} {B : Subgroup G} {b : G} {L : Subgroup G} {x : G} (H : Hyp53 m B b L x)
    {D : Subgroup G} (hD : IsEkIn 3 2 B D)
    (hnot : ¬ ⁅L, GLADelta 3 D ⊓ Subgroup.centralizer ({b} : Set G)⁆ ≤ GLAPPrimeCoreOf 3 L) :
    ∃ (c : G) (hcN : c ∈ Subgroup.normalizer (L : Set G)),
      c ∈ GLADelta 3 D ⊓ Subgroup.centralizer ({b} : Set G) ∧
        c ∈ Subgroup.centralizer ({x} : Set G) ∧ barAut 3 L ⟨c, hcN⟩ ≠ 1 := by
  classical
  have hS := H.hS
  have := hS.simple
  have hDel : IsElemAbelian 3 D := hD.2.1
  have hBel : IsElemAbelian 3 B := H.hB.1.1
  have hD0 : D ≠ ⊥ := by
    intro h
    have h2 := hD.2.2
    rw [h, Subgroup.card_bot] at h2
    norm_num at h2
  have hbD : b ∈ Subgroup.centralizer (D : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro d hd
    exact elemAbelian_comm hBel (hD.1 hd) H.hb
  have hb3 : b ^ 3 = 1 := hBel.2 b H.hb
  have hx3 : x ^ 3 = 1 := hBel.2 x H.hx
  obtain ⟨hXN, h2⟩ := i1 G hS.nonabelian hS.kProper 3 Nat.prime_three D hDel hD0 b hbD H.hb1 hb3
  have hX1N := hXN L H.hL
  obtain ⟨hker, hDN, himg⟩ :=
    h2 L H.hL (fun h => hnot (commutator_le_core_of_normalizes H.hL hX1N h))
  have hBX : ∀ g ∈ B, ∀ c ∈ GLADelta 3 D ⊓ Subgroup.centralizer ({b} : Set G),
      g * c * g⁻¹ ∈ GLADelta 3 D ⊓ Subgroup.centralizer ({b} : Set G) := by
    intro g hg c hc
    refine ⟨(Subgroup.mem_normalizer_iff.1 (le_normalizer_gLADelta hBel hD.1 hg) c).1 hc.1, ?_⟩
    have hg' : Commute g b := elemAbelian_comm hBel hg H.hb
    have hc' : Commute c b := Subgroup.mem_centralizer_singleton_iff.1 hc.2
    exact Subgroup.mem_centralizer_singleton_iff.2 ((hg'.mul_left hc').mul_left hg'.inv_left)
  set X1 : Subgroup G := GLADelta 3 D ⊓ Subgroup.centralizer ({b} : Set G) with hX1
  set N : Subgroup G := Subgroup.normalizer (L : Set G) with hN
  have hc0 : ∃ (c0 : G) (hc : c0 ∈ X1), barAut 3 L ⟨c0, hX1N hc⟩ ≠ 1 := by
    by_contra hcon
    push Not at hcon
    apply hnot
    refine Subgroup.commutator_le.2 fun l hl c hc => ?_
    exact (barAut_eq_one_iff (hX1N hc)).1 (hcon c hc)
      (Subgroup.commutator_mem_commutator hl (Subgroup.mem_zpowers c))
  have hconjS : ∀ d ∈ D, ∀ g ∈ X1 ⊔ L, d * g * d⁻¹ ∈ X1 ⊔ L := by
    intro d hd
    have : X1 ⊔ L ≤ (X1 ⊔ L).comap (MulAut.conj d).toMonoidHom := by
      refine sup_le (fun g hg => ?_) (fun g hg => ?_)
      · exact Subgroup.mem_sup_left (hBX d (hD.1 hd) g hg)
      · exact Subgroup.mem_sup_right ((Subgroup.mem_normalizer_iff.1 (hDN hd) g).1 hg)
    exact fun g hg => by simpa using this hg
  have key : ∀ (c : G) (hc : c ∈ X1),
      barAut 3 L ⟨c, hX1N hc⟩ * barAut 3 L ⟨x, H.hxN⟩ =
        barAut 3 L ⟨x, H.hxN⟩ * barAut 3 L ⟨c, hX1N hc⟩ := by
    intro c hc
    by_cases hα : barAut 3 L ⟨x, H.hxN⟩ = 1
    · rw [hα]; simp
    have hF : IsFieldAutPSL3 (barAut 3 L ⟨x, H.hxN⟩) ∨ IsFieldAutPSU3 (barAut 3 L ⟨x, H.hxN⟩) :=
      H.hxF.resolve_left hα
    have hQ := isQuasisimple_barOf H.hL
    have hT : IsThreeType (barOf 3 L) := by
      rcases hF with ⟨K, i1', i2', θ, -⟩ | ⟨K, i1', i2', q, θ, -, -, -, hq, -⟩
      · exact Or.inl ⟨K, i1', i2', ⟨θ⟩⟩
      · exact Or.inr ⟨K, i1', i2', q, hq, ⟨θ⟩⟩
    set Ht : Subgroup (MulAut (barOf 3 L)) := ((X1 ⊔ L).subgroupOf N).map (barAut 3 L) with hHt
    set Dt : Subgroup (MulAut (barOf 3 L)) := (D.subgroupOf N).map (barAut 3 L) with hDt
    have hDtE : IsEkIn 3 2 ⊤ Dt := by
      refine ⟨le_top, isElemAbelian_map (isElemAbelian_subgroupOf hDel) _, ?_⟩
      rw [hDt, A8_card_map_of_inj]
      · rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hDN).toEquiv]
        exact hD.2.2
      · intro d hd h1
        have hd' : (d : G) ∈ D := Subgroup.mem_subgroupOf.1 hd
        have := A8_mem_kerB hd' d.2 h1
        rw [hker] at this
        exact Subtype.ext (Subgroup.mem_bot.1 this)
    have hInn : innerAut (barOf 3 L) ≤ Ht := by
      rintro φ ⟨y, rfl⟩
      induction y using QuotientGroup.induction_on with | H z => ?_
      refine ⟨⟨z.1, Subgroup.le_normalizer z.2⟩, ?_, barAut_conj z.2 (Subgroup.le_normalizer z.2)⟩
      exact Subgroup.mem_subgroupOf.2 (Subgroup.mem_sup_right z.2)
    have hDtN : Dt ≤ Subgroup.normalizer (Ht : Set (MulAut (barOf 3 L))) := by
      rintro _ ⟨d, hd, rfl⟩
      apply Subgroup.mem_normalizer_fintype
      rintro _ ⟨g, hg, rfl⟩
      refine ⟨d * g * d⁻¹, ?_, by simp [map_mul, map_inv]⟩
      have hd' : (d : G) ∈ D := Subgroup.mem_subgroupOf.1 hd
      have hg' : (g : G) ∈ X1 ⊔ L := Subgroup.mem_subgroupOf.1 hg
      exact Subgroup.mem_subgroupOf.2 (hconjS _ hd' _ hg')
    have hne : localDeltaIn 3 Ht Dt ≠ ⊥ := by
      obtain ⟨c0, hc0X, hc0ne⟩ := hc0
      intro hbot
      apply hc0ne
      have : barAut 3 L ⟨c0, hX1N hc0X⟩ ∈ localDeltaIn 3 Ht Dt :=
        himg ⟨⟨c0, hX1N hc0X⟩, Subgroup.mem_subgroupOf.2 hc0X, rfl⟩
      rw [hbot] at this
      exact Subgroup.mem_bot.1 this
    have hzmem : barAut 3 L ⟨c, hX1N hc⟩ * barAut 3 L ⟨x, H.hxN⟩ * (barAut 3 L ⟨c, hX1N hc⟩)⁻¹ *
        (barAut 3 L ⟨x, H.hxN⟩)⁻¹ ∈ localDeltaIn 3 Ht Dt := by
      apply himg
      refine ⟨(⟨c, hX1N hc⟩ : ↥N) * ⟨x, H.hxN⟩ * (⟨c, hX1N hc⟩ : ↥N)⁻¹ * (⟨x, H.hxN⟩ : ↥N)⁻¹,
        ?_, by simp only [map_mul, map_inv]⟩
      refine Subgroup.mem_subgroupOf.2 ?_
      show c * x * c⁻¹ * x⁻¹ ∈ X1
      have := X1.mul_mem hc (hBX x H.hx c⁻¹ (X1.inv_mem hc))
      simpa [mul_assoc] using this
    have hInnD := i4 _ hQ hT (barAut 3 L ⟨c, hX1N hc⟩) (barAut 3 L ⟨x, H.hxN⟩)
    have h1 := i3 _ hQ hT Dt Ht hDtE hInn hDtN hne _ hzmem hInnD
    exact mul_inv_eq_iff_eq_mul.1 (mul_inv_eq_one.1 h1)
  obtain ⟨c0, hc0X, hc0ne⟩ := hc0
  let N0 : Subgroup G := (X1.subgroupOf N ⊓ (barAut 3 L).ker).map N.subtype
  have hmem0 : ∀ n : G, n ∈ N0 ↔ ∃ hn : n ∈ X1, barAut 3 L ⟨n, hX1N hn⟩ = 1 := by
    intro n
    constructor
    · rintro ⟨y, ⟨hy1, hy2⟩, rfl⟩
      exact ⟨Subgroup.mem_subgroupOf.1 hy1, hy2⟩
    · rintro ⟨h1, h2⟩
      exact ⟨⟨n, hX1N h1⟩, ⟨Subgroup.mem_subgroupOf.2 h1, h2⟩, rfl⟩
  have hN0X : N0 ≤ X1 := fun n hn => ((hmem0 n).1 hn).1
  have hxN0 : x ∈ Subgroup.normalizer (N0 : Set G) := by
    apply Subgroup.mem_normalizer_fintype
    intro n hn
    obtain ⟨hnX, hn1⟩ := (hmem0 n).1 hn
    have hX' : x * n * x⁻¹ ∈ X1 := hBX x H.hx n hnX
    refine (hmem0 _).2 ⟨hX', ?_⟩
    have : barAut 3 L ⟨x * n * x⁻¹, hX1N hX'⟩ =
        barAut 3 L ⟨x, H.hxN⟩ * barAut 3 L ⟨n, hX1N hnX⟩ * (barAut 3 L ⟨x, H.hxN⟩)⁻¹ := by
      show barAut 3 L ((⟨x, H.hxN⟩ : ↥N) * ⟨n, hX1N hnX⟩ * (⟨x, H.hxN⟩ : ↥N)⁻¹) = _
      simp only [map_mul, map_inv]
    rw [this, hn1]
    simp
  have hcop : Nat.Coprime 3 (Nat.card N0) := by
    have hle : N0 ≤ GLADelta 3 D := fun n hn => (hN0X hn).1
    exact (coprime_card_gLADelta Nat.prime_three hD0).coprime_dvd_right
      (Subgroup.card_dvd_of_le hle)
  have hg : c0⁻¹ * (x * c0 * x⁻¹) ∈ N0 := by
    have hX' : x * c0 * x⁻¹ ∈ X1 := hBX x H.hx c0 hc0X
    have hmem : c0⁻¹ * (x * c0 * x⁻¹) ∈ X1 := X1.mul_mem (X1.inv_mem hc0X) hX'
    refine (hmem0 _).2 ⟨hmem, ?_⟩
    have : barAut 3 L ⟨c0⁻¹ * (x * c0 * x⁻¹), hX1N hmem⟩ = (barAut 3 L ⟨c0, hX1N hc0X⟩)⁻¹ *
        (barAut 3 L ⟨x, H.hxN⟩ * barAut 3 L ⟨c0, hX1N hc0X⟩ * (barAut 3 L ⟨x, H.hxN⟩)⁻¹) := by
      show barAut 3 L ((⟨c0, hX1N hc0X⟩ : ↥N)⁻¹ * ((⟨x, H.hxN⟩ : ↥N) * ⟨c0, hX1N hc0X⟩ *
        (⟨x, H.hxN⟩ : ↥N)⁻¹)) = _
      simp only [map_mul, map_inv]
    rw [this, ← key c0 hc0X, mul_inv_cancel_right, inv_mul_cancel]
  obtain ⟨n', hn', hfix⟩ := exists_fixed_in_coset Nat.prime_three hx3 hxN0 hcop hg
  obtain ⟨hn'X, hn'1⟩ := (hmem0 n').1 hn'
  have hcX : c0 * n' ∈ X1 := X1.mul_mem hc0X hn'X
  refine ⟨c0 * n', hX1N hcX, hcX, ?_, ?_⟩
  · rw [Subgroup.mem_centralizer_singleton_iff]
    exact mul_inv_eq_iff_eq_mul.1 hfix |>.symm
  · have : barAut 3 L ⟨c0 * n', hX1N hcX⟩ =
        barAut 3 L ⟨c0, hX1N hc0X⟩ * barAut 3 L ⟨n', hX1N hn'X⟩ := by
      show barAut 3 L ((⟨c0, hX1N hc0X⟩ : ↥N) * ⟨n', hX1N hn'X⟩) = _
      simp only [map_mul]
    rw [this, hn'1, mul_one]
    exact hc0ne

theorem case1_contra (i5 : Input9_5) (i6 : Input9_2_8) (i7 : Input14_5Aut)
    {m : ℕ} {B : Subgroup G} {b : G} {L : Subgroup G} {x : G} (H : Hyp53 m B b L x)
    {D : Subgroup G} (hD : IsEkIn 3 2 B D) {c : G} (hcN : c ∈ Subgroup.normalizer (L : Set G))
    (hcΔ : c ∈ GLADelta 3 D ⊓ Subgroup.centralizer ({b} : Set G))
    (hcx : c ∈ Subgroup.centralizer ({x} : Set G)) (hc1 : barAut 3 L ⟨c, hcN⟩ ≠ 1)
    {J : Subgroup G} (hJ : GLAPComponent 3 (L ⊓ Subgroup.centralizer ({x} : Set G)) J)
    {𝒞 : Set (Subgroup G)} (hC : CSpec b x J 𝒞) {M : Subgroup G} (hM : M ∈ 𝒞)
    (hbad : ⁅M, GLADelta 3 D ⊓ Subgroup.centralizer ({x} : Set G)⁆ ≤ GLAPPrimeCoreOf 3 M) :
    False := by
  have hD0 : D ≠ ⊥ := by
    intro h
    have h2 := hD.2.2
    rw [h, Subgroup.card_bot] at h2
    norm_num at h2
  have hcop : Nat.Coprime 3 (orderOf c) := coprime_orderOf_of_mem_gLADelta Nat.prime_three hD0 hcΔ.1
  have hcomm : ⁅M, Subgroup.zpowers c⁆ ≤ GLAPPrimeCoreOf 3 M := by
    refine le_trans (Subgroup.commutator_mono le_rfl ?_) hbad
    rw [Subgroup.zpowers_le]
    exact ⟨hcΔ.1, hcx⟩
  exact hc1 (barAut_eq_one_of_centralizes i5 i6 i7 H hcN hcop hJ
    (comm_le_core_of_cspec H hcN hcΔ.2 hcx hJ hC hM hcomm))

end CaseOne

section CaseTwo

variable {G : Type} [Group G] [Finite G]

theorem lemma31_iii_or_iv (h31 : Lemma31) {m : ℕ} {B : Subgroup G} {b : G} {L : Subgroup G}
    {x : G} (H : Hyp53 m B b L x) (hlam : L ≤ lambdaOf 3 B b) (hpsi : ¬ L ≤ psiStarGroup 3 B) :
    Lemma31iii 3 B L ∨ Lemma31iv 3 B L := by
  have hB := H.hB
  have hSC : IsSCp 3 ⊤ B := CFSG.LocalAnalysis.GLTheoremB.lemma23_proved G m 3 H.hS B hB
  have hnb := not_stronglyBalanced_of_le_lambdaOf H.hL hlam
  rcases h31 G m 3 H.hS B hB.1 hSC b H.hb H.hb1 L H.hL with h | h | h | h | h
  · exact absurd h hnb
  · exfalso
    apply hpsi
    have h1 : L ≤ psiOf 3 B b := le_sSup ⟨H.hL, hnb, h⟩
    have h2 : psiOf 3 B b ≤ psiStar 3 B b := le_sup_left.trans le_sup_left
    exact (h1.trans h2).trans
      (le_iSup_of_le b (le_iSup_of_le H.hb (le_iSup_of_le H.hb1 le_rfl)) :
        psiStar 3 B b ≤ psiStarGroup 3 B)
  · exact Or.inl h
  · exact Or.inr h
  · exact absurd h.1 (by norm_num)

theorem A9_aut_eq_one {Y : Type} [Group Y] (hY : CFSG.Open.IsQuasisimple Y) (γ : MulAut Y)
    (h : ∀ y : Y, y⁻¹ * γ y ∈ Subgroup.center Y) : γ = 1 := by
  have hfix : ∀ y : Y, ∃ z ∈ Subgroup.center Y, γ y = y * z :=
    fun y => ⟨y⁻¹ * γ y, h y, by simp⟩
  have hle : (⊤ : Subgroup Y) ≤ fixSub γ := by
    rw [← hY.1, commutator]
    refine Subgroup.commutator_le.2 fun a _ b _ => ?_
    obtain ⟨z, hz, ha⟩ := hfix a
    obtain ⟨w, hw, hb⟩ := hfix b
    show γ (a * b * a⁻¹ * b⁻¹) = a * b * a⁻¹ * b⁻¹
    rw [map_mul, map_mul, map_mul, map_inv, map_inv, ha, hb]
    exact A2_commutator_mul_central a b z w hz hw
  ext y
  exact hle (Subgroup.mem_top y)

theorem A9_pCore_le_center {Y : Type} [Group Y] [Finite Y] (hY : CFSG.Open.IsQuasisimple Y) :
    CFSG.pCore 3 Y ≤ Subgroup.center Y := by
  have hS : IsSimpleGroup (Y ⧸ Subgroup.center Y) := hY.2
  have hN : ((CFSG.pCore 3 Y).map (QuotientGroup.mk' (Subgroup.center Y))).Normal :=
    (CFSG.pCore_normal (p := 3) (G := Y)).map _ (QuotientGroup.mk'_surjective _)
  rcases hN.eq_bot_or_eq_top with h | h
  · intro n hn
    have : QuotientGroup.mk' (Subgroup.center Y) n ∈ (⊥ : Subgroup (Y ⧸ Subgroup.center Y)) :=
      h ▸ Subgroup.mem_map_of_mem _ hn
    exact (QuotientGroup.eq_one_iff n).1 this
  · exfalso
    have hp : IsPGroup 3 (↥(⊤ : Subgroup (Y ⧸ Subgroup.center Y))) := by
      rw [← h]
      exact (CFSG.pCore_isPGroup (p := 3) (G := Y)).map _
    have hp' : IsPGroup 3 (Y ⧸ Subgroup.center Y) :=
      hp.of_equiv Subgroup.topEquiv
    have : Group.IsNilpotent (Y ⧸ Subgroup.center Y) := hp'.isNilpotent
    have hcomm : ∀ a b : Y ⧸ Subgroup.center Y, a * b = b * a := fun a b => mul_comm a b
    have hcen : (⊤ : Subgroup Y) ≤ Subgroup.center Y := by
      rw [← hY.1, commutator]
      refine Subgroup.commutator_le.2 fun a _ b _ => ?_
      have h1 : QuotientGroup.mk' (Subgroup.center Y) (a * b * a⁻¹ * b⁻¹) = 1 := by
        rw [map_mul, map_mul, map_mul, map_inv, map_inv]
        have := hcomm (QuotientGroup.mk' (Subgroup.center Y) a) (QuotientGroup.mk' (Subgroup.center Y) b)
        rw [this]; group
      exact (QuotientGroup.eq_one_iff _).1 h1
    have hsub : Subsingleton (Y ⧸ Subgroup.center Y) := ⟨fun a b => by
      obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective a
      obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective b
      have ha := (QuotientGroup.eq_one_iff a).2 (hcen (Subgroup.mem_top a))
      have hb := (QuotientGroup.eq_one_iff b).2 (hcen (Subgroup.mem_top b))
      exact ha.trans hb.symm⟩
    obtain ⟨a, b, hab⟩ := hS.toNontrivial.exists_pair_ne
    exact hab (Subsingleton.elim a b)

theorem barAut_mem_innerAut_of_lemma31iii {m : ℕ} {B : Subgroup G} {b : G} {L : Subgroup G}
    {x : G} (H : Hyp53 m B b L x) (h : Lemma31iii 3 B L) :
    barAut 3 L ⟨x, H.hxN⟩ ∈ innerAut (barOf 3 L) := by
  obtain ⟨l, hl, hc⟩ := h.2.2.2.2 x ⟨H.hx, H.hxN⟩
  have hY := isQuasisimple_barOf H.hL
  have hlN : l ∈ Subgroup.normalizer (L : Set G) := Subgroup.le_normalizer hl
  have hcN : l⁻¹ * x ∈ Subgroup.normalizer (L : Set G) := hc.1
  have hγ : barAut 3 L ⟨l⁻¹ * x, hcN⟩ = 1 := by
    refine A9_aut_eq_one hY _ fun y => ?_
    obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective y
    rw [barAut_mk]
    have h1 := hc.2.2 (a : G)⁻¹ (L.inv_mem a.2)
    let w : ↥L := a⁻¹ * L.normalizerMonoidHom ⟨l⁻¹ * x, hcN⟩ a
    have hw : (w : G) ∈ oPrimePOf 3 L := by
      have : (w : G) = (a : G)⁻¹ * (l⁻¹ * x) * ((a : G)⁻¹)⁻¹ * (l⁻¹ * x)⁻¹ := by
        simp [w, Subgroup.normalizerMonoidHom_apply_apply_coe, mul_assoc]
      rw [this]; exact h1
    obtain ⟨u, hu, hu'⟩ := hw
    have huw : u = w := Subtype.ext hu'
    rw [huw] at hu
    have hmem : QuotientGroup.mk' (GLAPPrimeCore 3 ↥L) w ∈ CFSG.pCore 3 (barOf 3 L) := hu
    exact A9_pCore_le_center hY hmem
  have hx : (⟨x, H.hxN⟩ : ↥(Subgroup.normalizer (L : Set G))) =
      ⟨l, hlN⟩ * ⟨l⁻¹ * x, hcN⟩ := Subtype.ext (by simp)
  rw [hx, map_mul, hγ, mul_one, barAut_conj hl hlN]
  exact ⟨_, rfl⟩

theorem trivial_action (i8 : Input7_FieldInn) (i9 : Input3_3_ON) {m : ℕ} {B : Subgroup G}
    {b : G} {L : Subgroup G} {x : G} (H : Hyp53 m B b L x)
    (h : Lemma31iii 3 B L ∨ Lemma31iv 3 B L) :
    ⁅L, Subgroup.zpowers x⁆ ≤ GLAPPrimeCoreOf 3 L := by
  have hY := isQuasisimple_barOf H.hL
  refine (barAut_eq_one_iff H.hxN).1 ?_
  have hF : barAut 3 L ⟨x, H.hxN⟩ = 1 ∨ IsFieldAutPSL3 (barAut 3 L ⟨x, H.hxN⟩) ∨
      IsFieldAutPSU3 (barAut 3 L ⟨x, H.hxN⟩) := H.hxF
  rcases h with h3 | h4
  · exact i8 _ hY _ H.hxF (barAut_mem_innerAut_of_lemma31iii H h3)
  · obtain ⟨-, -, ⟨e⟩⟩ := h4.2.2.1
    rcases hF with h1 | ⟨K, hK, hKf, θ, -⟩ | ⟨K, hK, hKf, q, θ, -, -, -, hq, -⟩
    · exact h1
    · exact ((i9.1 K hK hKf).false (e.symm.trans θ)).elim
    · exact ((i9.2 K hK hKf q hq).false (e.symm.trans θ)).elim

omit [Finite G] in
theorem A9_mem_centralizerQuot {L U : Subgroup G} (hUL : U ≤ L) {g : G}
    (hg : g ∈ Subgroup.normalizer (L : Set G)) (h : ∀ y ∈ L, y * g * y⁻¹ * g⁻¹ ∈ U) :
    g ∈ centralizerQuot L U := by
  refine ⟨hg, ?_, h⟩
  rw [Subgroup.mem_normalizer_iff]
  intro u
  have hgL : ∀ h : G, h ∈ L ↔ g * h * g⁻¹ ∈ L := fun h => Subgroup.mem_normalizer_iff.1 hg h
  constructor
  · intro hu
    have h1 := h u⁻¹ (L.inv_mem (hUL hu))
    have e : g * u * g⁻¹ = u * (u⁻¹ * g * u⁻¹⁻¹ * g⁻¹) := by group
    rw [e]
    exact U.mul_mem hu h1
  · intro hu
    have huL : u ∈ L := (hgL u).2 (hUL hu)
    have h1 := h u⁻¹ (L.inv_mem huL)
    have e : u = (g * u * g⁻¹) * (u⁻¹ * g * u⁻¹⁻¹ * g⁻¹)⁻¹ := by group
    rw [e]
    exact U.mul_mem hu (U.inv_mem h1)

omit [Finite G] in
theorem A9_oPrimePOf_le (L : Subgroup G) : oPrimePOf 3 L ≤ L := by
  rintro _ ⟨y, -, rfl⟩
  exact y.2

omit [Finite G] in
theorem A9_core_le_oPrimeP (L : Subgroup G) : GLAPPrimeCoreOf 3 L ≤ oPrimePOf 3 L := by
  rintro _ ⟨y, hy, rfl⟩
  refine ⟨y, ?_, rfl⟩
  have h1 : QuotientGroup.mk' (GLAPPrimeCore 3 ↥L) y = 1 := (QuotientGroup.eq_one_iff y).2 hy
  show QuotientGroup.mk' (GLAPPrimeCore 3 ↥L) y ∈ CFSG.pCore 3 (↥L ⧸ GLAPPrimeCore 3 ↥L)
  rw [h1]
  exact one_mem _

omit [Finite G] in
theorem A9_mem_centralizerQuot_of_centralizes {L U : Subgroup G} (hUL : U ≤ L) {b : G}
    (hbL : L ≤ Subgroup.centralizer ({b} : Set G)) : b ∈ centralizerQuot L U := by
  have hc : ∀ y ∈ L, b * y = y * b := fun y hy =>
    Subgroup.mem_centralizer_iff.1 (hbL hy) b rfl
  refine A9_mem_centralizerQuot hUL ?_ fun y hy => ?_
  · rw [Subgroup.mem_normalizer_iff]
    intro h
    constructor
    · intro hh
      have e : b * h * b⁻¹ = h := by
        rw [hc h hh]; group
      rw [e]; exact hh
    · intro hh
      have h1 := hc _ hh
      have e : b * h * b⁻¹ = h := by
        calc b * h * b⁻¹ = b⁻¹ * (b * (b * h * b⁻¹)) := by group
          _ = b⁻¹ * ((b * h * b⁻¹) * b) := by rw [h1]
          _ = h := by group
      rw [← e]; exact hh
  · rw [← hc y hy]
    simp

theorem normalizer_or_mem_zpowers {m : ℕ} {B : Subgroup G} {b : G} {L : Subgroup G} {x : G}
    (H : Hyp53 m B b L x) (h : Lemma31iii 3 B L ∨ Lemma31iv 3 B L)
    (hxtriv : ⁅L, Subgroup.zpowers x⁆ ≤ GLAPPrimeCoreOf 3 L) :
    B ≤ Subgroup.normalizer (L : Set G) ∨ x ∈ Subgroup.zpowers b := by
  by_contra hcon
  rw [not_or] at hcon
  obtain ⟨hBN, hxb⟩ := hcon
  have hhB := H.hB
  have hb3 : b ^ 3 = 1 := hhB.1.1.2 b H.hb
  have hord : orderOf b = 3 := orderOf_eq_prime hb3 H.hb1
  have hbL : L ≤ Subgroup.centralizer ({b} : Set G) := H.hL.1
  have hrank : GLATwoLocalRank 3 G = 4 := h.elim (fun h3 => h3.2.1) (fun h4 => h4.2.1)
  have hm : m = 4 := by
    have := H.hS.rank_eq
    omega
  have hcardB : Nat.card B = 3 ^ 4 := by
    rw [H.hS.card_eq H.hB, hm]
  set NB : Subgroup G := B ⊓ Subgroup.normalizer (L : Set G) with hNB
  have hNBle : NB ≤ B := inf_le_left
  have hNBlt : Nat.card NB < Nat.card B := by
    by_contra hge
    push Not at hge
    have := Subgroup.eq_of_le_of_card_ge hNBle hge
    exact hBN (this ▸ inf_le_right)
  have hdvd : Nat.card NB ∣ 3 ^ 4 := hcardB ▸ Subgroup.card_dvd_of_le hNBle
  have hle27 : Nat.card NB ≤ 27 := by
    obtain ⟨k, hk, hk'⟩ := (Nat.dvd_prime_pow Nat.prime_three).1 hdvd
    have hk4 : k < 4 := by
      by_contra hk4
      have : k = 4 := by omega
      rw [this, ← hcardB] at hk'
      omega
    rw [hk']
    calc 3 ^ k ≤ 3 ^ 3 := Nat.pow_le_pow_right (by norm_num) (by omega)
      _ = 27 := by norm_num
  have hbNB : b ∈ NB :=
    ⟨H.hb, (A9_mem_centralizerQuot_of_centralizes (A9_oPrimePOf_le L) hbL).1⟩
  have hcnt : ∀ C : Subgroup G, b ∈ C → 3 ∣ Nat.card ↥(C ⊓ NB) := by
    intro C hbC
    have hmem : b ∈ C ⊓ NB := ⟨hbC, hbNB⟩
    have := orderOf_dvd_natCard (⟨b, hmem⟩ : ↥(C ⊓ NB))
    rwa [Subgroup.orderOf_mk, hord] at this
  have hpos : ∀ C : Subgroup G, 0 < Nat.card ↥(C ⊓ NB) := fun C => Nat.card_pos
  rcases h with h3 | h4
  · set C := centralizerQuot L (oPrimePOf 3 L) with hC
    have hbC : b ∈ C := A9_mem_centralizerQuot_of_centralizes (A9_oPrimePOf_le L) hbL
    have hmul := Subgroup.relIndex_mul_card (H := C) (K := NB)
    rw [h3.2.2.2.1] at hmul
    have h3d := hcnt C hbC
    have hp := hpos C
    have hcard3 : Nat.card ↥(C ⊓ NB) = 3 := by omega
    have hzle : Subgroup.zpowers b ≤ C ⊓ NB := by
      rw [Subgroup.zpowers_le]; exact ⟨hbC, hbNB⟩
    have hz : Nat.card (Subgroup.zpowers b) = 3 := by rw [Nat.card_zpowers, hord]
    have heq : Subgroup.zpowers b = C ⊓ NB :=
      Subgroup.eq_of_le_of_card_ge hzle (by omega)
    have hxC : x ∈ C := by
      refine A9_mem_centralizerQuot (A9_oPrimePOf_le L) H.hxN fun y hy => ?_
      have := Subgroup.commutator_mem_commutator hy (Subgroup.mem_zpowers x)
      rw [commutatorElement_def] at this
      exact A9_core_le_oPrimeP L (hxtriv this)
    apply hxb
    rw [heq]
    exact ⟨hxC, H.hx, H.hxN⟩
  · set C := centralizerQuot L (GLAPPrimeCoreOf 3 L) with hC
    have hbC : b ∈ C := A9_mem_centralizerQuot_of_centralizes
      ((A9_core_le_oPrimeP L).trans (A9_oPrimePOf_le L)) hbL
    have hmul := Subgroup.relIndex_mul_card (H := C) (K := NB)
    rw [h4.2.2.2] at hmul
    have h3d := hcnt C hbC
    have hp := hpos C
    omega

theorem case2_comp (h31 : Lemma31) (h33 : Lemma33) (i8 : Input7_FieldInn) (i9 : Input3_3_ON)
    {m : ℕ} {B : Subgroup G} {b : G} {L : Subgroup G} {x : G} (H : Hyp53 m B b L x)
    (hLU : IsUpsilonComponent B b L) (hlam : L ≤ lambdaOf 3 B b) (hpsi : ¬ L ≤ psiStarGroup 3 B)
    {J : Subgroup G} (hJ : GLAPComponent 3 (L ⊓ Subgroup.centralizer ({x} : Set G)) J)
    {𝒞 : Set (Subgroup G)} (hC : CSpec b x J 𝒞) {M : Subgroup G} (hM : M ∈ 𝒞) :
    IsUpsilonComponent B x M := by
  have hS := H.hS
  have hB := H.hB
  have hh := lemma31_iii_or_iv h31 H hlam hpsi
  have hxtriv := trivial_action i8 i9 H hh
  have hb3 : b ^ 3 = 1 := hB.1.1.2 b H.hb
  have hJ1 : J ≤ ⨆ g ∈ GLAPLayer 3 (Subgroup.centralizer ({x} : Set G)), GLBConj g J := by
    refine le_iSup₂_of_le 1 (one_mem _) ?_
    rw [gLBConj_one]
  have hJL : J ≤ L := hJ.1.trans inf_le_left
  have hJlay : J ≤ GLAPLayer 3 (L ⊓ Subgroup.centralizer ({x} : Set G)) := le_sSup hJ
  rcases normalizer_or_mem_zpowers H hh hxtriv with hBN | hxb
  ·
    have hnb := not_stronglyBalanced_of_le_lambdaOf H.hL hlam
    have hSC : IsSCp 3 ⊤ B := CFSG.LocalAnalysis.GLTheoremB.lemma23_proved G m 3 hS B hB
    have hJle : GLAPLayer 3 (L ⊓ Subgroup.centralizer ({x} : Set G)) ≤ lambdaOf 3 B x :=
      h33 G m 3 hS B hB.1 hSC b H.hb H.hb1 L H.hL hnb hBN x H.hx H.hx1 hxtriv
    have hKle : (⨆ M ∈ 𝒞, M) ≤ lambdaOf 3 B x := by
      rw [hC.2.1]
      refine iSup₂_le fun g hg => ?_
      calc GLBConj g J ≤ GLBConj g (lambdaOf 3 B x) := by
            unfold GLBConj; exact Subgroup.map_mono (hJlay.trans hJle)
        _ ≤ lambdaOf 3 B x := gLBConj_lambdaOf_le hg
    have hMle : M ≤ lambdaOf 3 B x :=
      le_trans (le_iSup₂ (f := fun M (_ : M ∈ 𝒞) => M) M hM) hKle
    refine ⟨hC.1 M hM, Or.inl ⟨hMle, ?_⟩⟩
    intro hMpsi
    have hall : ∀ M' ∈ 𝒞, M' ≤ psiStarGroup 3 B := by
      intro M' hM'
      obtain ⟨e, he, rfl⟩ := hC.2.2.2 M hM M' hM'
      have heB : e ∈ B := (Subgroup.zpowers_le.2 H.hb) he
      calc GLBConj e M ≤ GLBConj e (psiStarGroup 3 B) := by
            unfold GLBConj; exact Subgroup.map_mono hMpsi
        _ = psiStarGroup 3 B := gLBConj_psiStarGroup hB.1.1.1 heB
    have hJpsi : J ≤ psiStarGroup 3 B := by
      rw [← hC.2.1] at hJ1
      exact hJ1.trans (iSup₂_le fun M' hM' => hall M' hM')
    have hR : GLAPPrimeCoreOf 3 L ≤ psiStarGroup 3 B :=
      glaPPrimeCoreOf_le_psiStarGroup H.hb H.hb1 H.hL.2.1
    exact hpsi ((le_sup_core_of_trivial_action H hxtriv hJ).trans (sup_le hJpsi hR))
  ·
    have hCeq := centralizer_singleton_eq_of_mem_zpowers hb3 H.hx1 hxb
    have hLsub : ∀ g ∈ GLAPLayer 3 (Subgroup.centralizer ({x} : Set G)),
        g ∈ Subgroup.normalizer (L : Set G) := by
      intro g hg
      rw [hCeq] at hg
      exact mem_normalizer_of_mem_glaPLayer Nat.prime_three H.hL hg
    have hKL : (⨆ M ∈ 𝒞, M) ≤ L := by
      rw [hC.2.1]
      refine iSup₂_le fun g hg => ?_
      calc GLBConj g J ≤ GLBConj g L := by unfold GLBConj; exact Subgroup.map_mono hJL
        _ = L := mem_normalizer_iff_gLBConj_eq.1 (hLsub g hg)
    have hML : M ≤ L := le_trans (le_iSup₂ (f := fun M (_ : M ∈ 𝒞) => M) M hM) hKL
    have hMc : GLAPComponent 3 (Subgroup.centralizer ({b} : Set G)) M := hCeq ▸ hC.1 M hM
    have hMeq : M = L := glaPComponent_eq_of_le Nat.prime_three hMc H.hL hML
    rw [hMeq]
    exact isUpsilonComponent_of_centralizer_eq hCeq hLU

end CaseTwo

end Lemma53Ns

open Lemma53Ns CFSG.HardMathSupport.Solomon.UniquenessMaximal in
theorem lemma53_of_inputs (h33 : Lemma33) (h31 : Lemma31) (h18 : Input18_3_4)
    (i1 : Input19_1_2) (i3 : Input19_7_3b) (i4 : Input7_AutQuotAbelian) (i5 : Input9_5)
    (i6 : Input9_2_8) (i7 : Input14_5Aut) (i8 : Input7_FieldInn) (i9 : Input3_3_ON) :
    Lemma53 := by
  intro G _ _ m hS hC B hB b hb hb1 L hL x hx hx1 hxF
  obtain ⟨hxN, hF⟩ := hxF
  have H : Hyp53 m B b L x := ⟨hS, hC, hB, hb, hb1, hL.1, hx, hx1, hxN, hF⟩
  refine K_le_upsilon_of h18 H ?_
  intro J hJ 𝒞 hCS M hM
  rcases hL.2 with ⟨hlam, hpsi⟩ | ⟨D, hD, hnot⟩
  · exact case2_comp h31 h33 i8 i9 H hL hlam hpsi hJ hCS hM
  · refine ⟨hCS.1 M hM, Or.inr ⟨D, hD, fun hbad => ?_⟩⟩
    obtain ⟨c, hcN, hcΔ, hcx, hc1⟩ := case1_exists_c i1 i3 i4 H hD hnot
    exact case1_contra i5 i6 i7 H hD hcN hcΔ hcx hc1 hJ hCS hM hbad

end CFSG.HardMathSupport.Solomon.LocalBalance
