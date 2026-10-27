module

public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.NonToralCoreDefs
import CFSG.LieType.SeitzGeneration.ExcHighThree.KillsRootGroup
public import CFSG.HardMathSupport.Timmesfeld.Torality.LangAssembly

public noncomputable section

namespace CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.NonToralCore

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.HardMathSupport.Timmesfeld.Torality CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.LieType.AlgebraicGroups CFSG.LieType.SeitzGeneration.ExcHighThree

set_option linter.unusedSectionVars false

section Cyclic

variable {X : Type*} {G : Type*} [Group G] [MulAction G X]

private theorem image_eq_of_cyc (S : Set X) (blk : Fin 3 → Set X) (hsub : ∀ j, blk j ⊆ S)
    (hcover : ∀ α ∈ S, ∃ j, α ∈ blk j) (ω : G)
    (hω : ∀ j : Fin 3, (fun α => ω • α) '' blk j = blk (j + 1)) :
    (fun α => ω • α) '' S = S := by
  ext δ
  constructor
  · rintro ⟨α, hα, rfl⟩
    obtain ⟨j, hj⟩ := hcover α hα
    exact hsub (j + 1) (by rw [← hω j]; exact ⟨α, hj, rfl⟩)
  · intro hδ
    obtain ⟨j, hj⟩ := hcover δ hδ
    rw [← sub_add_cancel j 1, ← hω] at hj
    obtain ⟨α, hα, rfl⟩ := hj
    exact ⟨α, hsub _ hα, rfl⟩

private theorem exists_inv_pow_smul_mem_of_cyc (blk : Fin 3 → Set X) (ω : G)
    (hω : ∀ j : Fin 3, (fun α => ω • α) '' blk j = blk (j + 1)) (j : Fin 3) {δ : X}
    (h : δ ∈ blk j) : ∃ n : ℕ, (ω ^ n)⁻¹ • δ ∈ blk 0 := by
  have step : ∀ i : Fin 3, ∀ {γ : X}, γ ∈ blk (i + 1) → ω⁻¹ • γ ∈ blk i := by
    intro i γ hγ
    rw [← hω i] at hγ
    obtain ⟨α, hα, rfl⟩ := hγ
    rwa [inv_smul_smul]
  fin_cases j
  · exact ⟨0, by simpa using h⟩
  · exact ⟨1, by simpa using step 0 h⟩
  · refine ⟨2, ?_⟩
    rw [pow_two, mul_inv_rev, mul_smul]
    exact step 0 (step 1 h)

end Cyclic


section Monomial

variable {τ : Tag} {L : Type} [Field L]

private def IsMonoAt (g : ModGL τ L) (w : WeylGroup τ) : Prop :=
  ∀ δ : Fin τ.rank → ℤ, IsRoot τ δ → ∃ μ : Lˣ, ∀ c : L,
    g * pinnedX τ L δ c * g⁻¹ = pinnedX τ L (w • δ) ((μ : L) * c)

private theorem isMonoAt_one : IsMonoAt (1 : ModGL τ L) 1 := fun _ _ => ⟨1, fun c => by simp⟩

private theorem isMonoAt_mul {g h : ModGL τ L} {w v : WeylGroup τ} (hg : IsMonoAt g w)
    (hh : IsMonoAt h v) : IsMonoAt (g * h) (w * v) := by
  intro δ hδ
  obtain ⟨μ₁, h1⟩ := hh δ hδ
  obtain ⟨μ₂, h2⟩ := hg (v • δ) (CFSG.LieType.Chevalley.IsRoot.smul hδ v)
  refine ⟨μ₂ * μ₁, fun c => ?_⟩
  calc g * h * pinnedX τ L δ c * (g * h)⁻¹ = g * (h * pinnedX τ L δ c * h⁻¹) * g⁻¹ := by group
    _ = pinnedX τ L ((w * v) • δ) (((μ₂ * μ₁ : Lˣ) : L) * c) := by
      rw [h1, h2, mul_smul, Units.val_mul, mul_assoc]

private theorem isMonoAt_inv {g : ModGL τ L} {w : WeylGroup τ} (hg : IsMonoAt g w) :
    IsMonoAt g⁻¹ w⁻¹ := by
  intro δ hδ
  obtain ⟨μ, h⟩ := hg (w⁻¹ • δ) (CFSG.LieType.Chevalley.IsRoot.smul hδ w⁻¹)
  refine ⟨μ⁻¹, fun c => ?_⟩
  have e := h (((μ⁻¹ : Lˣ) : L) * c)
  rw [smul_inv_smul, ← mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, one_mul] at e
  rw [← e]
  group

private theorem isMonoAt_pow {g : ModGL τ L} {w : WeylGroup τ} (hg : IsMonoAt g w) :
    ∀ n : ℕ, IsMonoAt (g ^ n) (w ^ n)
  | 0 => by
    rw [pow_zero, pow_zero]
    exact isMonoAt_one
  | n + 1 => by
    rw [pow_succ, pow_succ]
    exact isMonoAt_mul (isMonoAt_pow hg n) hg

private theorem isMonoAt_rootDiagUnit (b : Fin τ.rank → Lˣ) : IsMonoAt (rootDiagUnit τ b) 1 :=
  fun δ hδ => ⟨rootChar b δ, fun c => by rw [rootDiagUnit_conj_pinnedX b hδ c, one_smul]⟩

private theorem isMonoAt_canonicalRep (w : WeylGroup τ) :
    IsMonoAt (canonicalRep (coxeterSystem τ) L w) w := by
  obtain ⟨s, hs⟩ := exists_sign_family (L := L) w
  intro δ hδ
  refine ⟨Units.mkOfMulEqOne (s δ) (s δ) (hs δ hδ).1, fun c => ?_⟩
  rw [Units.val_mkOfMulEqOne]
  exact (hs δ hδ).2 c

private theorem IsMonoAt.conj_mem_rootSpan {g : ModGL τ L} {w : WeylGroup τ}
    (hg : IsMonoAt g w) {S S' : Set (Fin τ.rank → ℤ)} (hS : ∀ δ ∈ S, IsRoot τ δ)
    (hmap : ∀ δ ∈ S, w • δ ∈ S') {u : ModGL τ L} (hu : u ∈ rootSpan τ L S) :
    g * u * g⁻¹ ∈ rootSpan τ L S' := by
  have hle : rootSpan τ L S ≤ (rootSpan τ L S').comap (MulAut.conj g).toMonoidHom := by
    refine iSup₂_le fun δ hδ => (Subgroup.closure_le _).2 ?_
    rintro _ ⟨c, rfl⟩
    obtain ⟨μ, hμ⟩ := hg δ (hS δ hδ)
    show g * pinnedX τ L δ c * g⁻¹ ∈ rootSpan τ L S'
    rw [hμ]
    exact pinnedX_mem_rootSpan (hmap δ hδ) _
  exact hle hu

private theorem exists_not_comm_negRoot {β : Fin τ.rank → ℤ} (hβ : IsRoot τ β) {u : L}
    (hu : u ≠ 0) :
    ∃ ε : L, pinnedX τ L (-β) ε * pinnedX τ L β u ≠ pinnedX τ L β u * pinnedX τ L (-β) ε := by
  obtain ⟨ε, -, hv⟩ := exists_rootSL2_vSL_eq (K := L) hβ
  refine ⟨ε, fun heq => hu ?_⟩
  have hss : ∀ c : L, (pinnedData τ β).2.2 • ((pinnedData τ β).2.2 • c) = c := by
    intro c
    rcases pinnedSign_eq τ β with h | h <;> rw [h] <;> simp
  have e1 : pinnedX τ L (-β) ε = rootSL2 τ L β (vSL 1) := by rw [hv 1, mul_one]
  have e2 : pinnedX τ L β u = rootSL2 τ L β (uSL ((pinnedData τ β).2.2 • u)) := by
    rw [rootSL2_uSL_eq, hss]
  rw [e1, e2, ← map_mul, ← map_mul] at heq
  have h := congrArg (fun A : SL2 L => (A : Matrix (Fin 2) (Fin 2) L) 0 0)
    (CFSG.RankThree.Chevalley.rootSL2_injective_of_field β heq)
  simp only [Matrix.SpecialLinearGroup.coe_mul] at h
  simp [vSL, uSL, Matrix.mul_apply, Fin.sum_univ_two] at h
  rcases h with h | h
  · exfalso
    rcases pinnedSign_eq τ β with hs | hs <;> rw [hs] at h <;> simp at h
  · exact h

private theorem rootSpan_commute_of_iform (hτ : τ = .D4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8)
    {S₁ S₂ : Set (Fin τ.rank → ℤ)} (hS₁ : ∀ r ∈ S₁, IsRoot τ r) (hS₂ : ∀ r ∈ S₂, IsRoot τ r)
    (horth : ∀ α ∈ S₁, ∀ β ∈ S₂, iform α β = 0) {u v : ModGL τ L} (hu : u ∈ rootSpan τ L S₁)
    (hv : v ∈ rootSpan τ L S₂) : Commute u v :=
  CFSG.RankThree.PartOne.KE.rootSpan_commute_of_orth hτ hS₁ hS₂
    (fun α hα β hβ => by rw [dotProduct_mulVec_eq_iform]; exact horth α hα β hβ) u hu v hv

private theorem familyGroup_le_normalizer_blk (hτ : τ = .D4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8)
    {ι : Type} (a : ι → Fin τ.rank → Lˣ) (blk : Fin 3 → Set (Fin τ.rank → ℤ))
    (hsub : ∀ j, blk j ⊆ familyKernel a) (hcover : ∀ α ∈ familyKernel a, ∃ j, α ∈ blk j)
    (horth : ∀ j j', j ≠ j' → ∀ γ ∈ blk j, ∀ δ ∈ blk j', iform γ δ = 0) (j₀ : Fin 3) :
    familyGroup (K := L) a ≤ Subgroup.normalizer (rootSpan τ L (blk j₀) : Set (ModGL τ L)) := by
  have hroot : ∀ j, ∀ δ ∈ blk j, IsRoot τ δ := fun j δ hδ => (hsub j hδ).1
  refine sup_le (torusGroup_le_normalizer_rootSpan (hroot j₀)) ?_
  refine iSup₂_le fun α hα => ?_
  obtain ⟨j, hj⟩ := hcover α hα
  have hαj : rootSubgroup τ L α ≤ rootSpan τ L (blk j) :=
    le_iSup₂_of_le (f := fun δ (_ : δ ∈ blk j) => rootSubgroup τ L δ) α hj le_rfl
  by_cases hjj : j = j₀
  · rw [hjj] at hαj
    exact hαj.trans Subgroup.le_normalizer
  · refine le_trans ?_ (Subgroup.centralizer_le_normalizer _)
    intro g hg
    rw [Subgroup.mem_centralizer_iff]
    intro u hu
    exact (rootSpan_commute_of_iform hτ (hroot j) (hroot j₀) (horth j j₀ hjj) (hαj hg) hu).symm

private theorem exists_blockCore (hτ : τ = .D4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8) [IsAlgClosed L]
    (p : ℕ) [Fact p.Prime] [CharP L p] {e : ℕ} (he : 1 ≤ e) (Fr : L →+* L)
    (hFr : ∀ c, Fr c = c ^ (p ^ e)) {ι : Type} (a : ι → Fin τ.rank → Lˣ)
    (blk : Fin 3 → Set (Fin τ.rank → ℤ)) (hne : (blk 0).Nonempty)
    (hsub : ∀ j, blk j ⊆ familyKernel a) (hcover : ∀ α ∈ familyKernel a, ∃ j, α ∈ blk j)
    (hneg : ∀ γ ∈ blk 0, -γ ∈ blk 0)
    (horth : ∀ j j', j ≠ j' → ∀ γ ∈ blk j, ∀ δ ∈ blk j', iform γ δ = 0)
    (htrans : ∀ γ ∈ blk 0, ∀ δ ∈ blk 0,
      ∃ y ∈ Subgroup.closure (rootReflection '' familyKernel a), y • γ = δ)
    {z : ModGL τ L} {ω : WeylGroup τ} (hz : IsMonoAt z ω)
    (hzN : z ∈ Subgroup.normalizer (familyGroup (K := L) a : Set (ModGL τ L)))
    (hω : ∀ j : Fin 3, (fun α => ω • α) '' blk j = blk (j + 1))
    {m : ModGL τ L} {x : WeylGroup τ} (hm : m ∈ familyGroup (K := L) a)
    (hx : (fun α => x • α) '' familyKernel a = familyKernel a) :
    ∃ (u₁ : ModGL τ L) (k : ℕ), u₁ ∈ adjointGroup τ L ∧ u₁ ∈ familyGroup (K := L) a ∧
      u₁ ^ p = 1 ∧
      (m * canonicalRep (coxeterSystem τ) L x) * Units.map (entrywiseHom Fr) u₁ *
          (m * canonicalRep (coxeterSystem τ) L x)⁻¹ = z ^ k * u₁ * (z ^ k)⁻¹ ∧
      Commute u₁ (z * u₁ * z⁻¹) ∧ u₁ * (z * u₁ * z⁻¹) * (z ^ 2 * u₁ * (z ^ 2)⁻¹) ≠ 1 := by
  have hFrEq : Fr = iterateFrobenius L p e :=
    RingHom.ext fun c => by rw [hFr c, iterateFrobenius_def]
  have hFrob : ∀ g : ModGL τ L,
      Units.map (entrywiseHom Fr) g = entrywiseFrobGL τ L p e g := by
    intro g
    rw [hFrEq]
  have hq : 2 ≤ p ^ e :=
    (Fact.out : p.Prime).two_le.trans (Nat.le_self_pow (by omega) p)
  have hroot : ∀ j, ∀ δ ∈ blk j, IsRoot τ δ := fun j δ hδ => (hsub j hδ).1
  obtain ⟨β, hβ⟩ := hne
  have hβR : IsRoot τ β := hroot 0 β hβ
  have hxβ : x • β ∈ familyKernel a := by
    rw [← hx]
    exact ⟨β, hsub 0 hβ, rfl⟩
  obtain ⟨j, hj⟩ := hcover _ hxβ
  obtain ⟨k, hk⟩ := exists_inv_pow_smul_mem_of_cyc blk ω hω j hj
  obtain ⟨y, hy, hyγ⟩ := htrans _ hk β hβ
  have hyM : canonicalRep (coxeterSystem τ) L y ∈ familyGroup (K := L) a :=
    canonicalRep_closure_mem_familyGroup a hy
  obtain ⟨μ, hμ⟩ := isMonoAt_mul (isMonoAt_canonicalRep (L := L) y)
    (isMonoAt_mul (isMonoAt_inv (isMonoAt_pow hz k)) (isMonoAt_canonicalRep (L := L) x)) β hβR
  have hyβ : (y * ((ω ^ k)⁻¹ * x)) • β = β := by rw [mul_smul, mul_smul, hyγ]
  rw [hyβ] at hμ
  have hzkN : (z ^ k)⁻¹ ∈ Subgroup.normalizer (familyGroup (K := L) a : Set (ModGL τ L)) :=
    inv_mem (pow_mem hzN k)
  have hm₁ : (z ^ k)⁻¹ * m * z ^ k ∈ familyGroup (K := L) a := by
    have h := (Subgroup.mem_normalizer_iff.1 hzkN m).1 hm
    rwa [inv_inv] at h
  have hQN : (z ^ k)⁻¹ * (m * canonicalRep (coxeterSystem τ) L x) ∈
      Subgroup.normalizer (familyGroup (K := L) a : Set (ModGL τ L)) :=
    mul_mem hzkN (mul_mem (Subgroup.le_normalizer hm) (canonicalRep_mem_normalizer_of_image hx))
  set Q := (z ^ k)⁻¹ * (m * canonicalRep (coxeterSystem τ) L x) with hQ
  set m₂ := (z ^ k)⁻¹ * m * z ^ k * (canonicalRep (coxeterSystem τ) L y)⁻¹ with hm₂def
  have hm₂ : m₂ ∈ familyGroup (K := L) a := mul_mem hm₁ (inv_mem hyM)
  have hQX : ∀ c, Q * pinnedX τ L β c * Q⁻¹ = m₂ * pinnedX τ L β ((μ : L) * c) * m₂⁻¹ := by
    intro c
    rw [← hμ c, hQ, hm₂def]
    group
  obtain ⟨ζ, hζ, hζQ⟩ := lang_familyGroup p a e he Q hQN m₂⁻¹ (inv_mem hm₂)
  have hA : Q * entrywiseFrobGL τ L p e ζ * Q⁻¹ = ζ * m₂⁻¹ := by
    calc Q * entrywiseFrobGL τ L p e ζ * Q⁻¹
        = ζ * (ζ⁻¹ * (Q * entrywiseFrobGL τ L p e ζ * Q⁻¹)) := by group
      _ = ζ * m₂⁻¹ := by rw [hζQ]
  obtain ⟨t, ht⟩ := IsAlgClosed.exists_pow_nat_eq ((μ⁻¹ : Lˣ) : L)
    (show 0 < p ^ e - 1 by omega)
  have ht0 : t ≠ 0 := by
    rintro rfl
    rw [zero_pow (by omega)] at ht
    exact (Units.ne_zero μ⁻¹) ht.symm
  have hμt : (μ : L) * Fr t = t := by
    rw [hFr t, show p ^ e = p ^ e - 1 + 1 by omega, pow_succ, ht, ← mul_assoc, ← Units.val_mul,
      mul_inv_cancel, Units.val_one, one_mul]
  have hMA := familyGroup_le_normalizer_blk hτ a blk hsub hcover horth 0
  have hconjA : ∀ g ∈ familyGroup (K := L) a, ∀ u ∈ rootSpan τ L (blk 0),
      g * u * g⁻¹ ∈ rootSpan τ L (blk 0) :=
    fun g hg u hu => (Subgroup.mem_normalizer_iff.1 (hMA hg) u).1 hu
  have hzA : ∀ (i : Fin 3) {u : ModGL τ L}, u ∈ rootSpan τ L (blk i) →
      z * u * z⁻¹ ∈ rootSpan τ L (blk (i + 1)) := fun i u hu =>
    hz.conj_mem_rootSpan (hroot i) (fun δ hδ => by rw [← hω i]; exact ⟨δ, hδ, rfl⟩) hu
  have hu₁A : ζ * pinnedX τ L β t * ζ⁻¹ ∈ rootSpan τ L (blk 0) :=
    hconjA ζ hζ _ (pinnedX_mem_rootSpan hβ t)
  have hu₁M : ζ * pinnedX τ L β t * ζ⁻¹ ∈ familyGroup (K := L) a :=
    mul_mem (mul_mem hζ (rootSpan_le_familyGroup a (pinnedX_mem_rootSpan (hsub 0 hβ) t)))
      (inv_mem hζ)
  refine ⟨ζ * pinnedX τ L β t * ζ⁻¹, k, familyGroup_le_adjoint a hu₁M, hu₁M, ?_, ?_, ?_, ?_⟩
  · rw [conj_pow, pinnedX_pow_char p, mul_one, mul_inv_cancel]
  · rw [map_mul, map_mul, map_inv, CFSG.RankThree.PartOne.KE.units_map_entrywiseHom_pinnedX,
      hFrob ζ]
    have hν : m * canonicalRep (coxeterSystem τ) L x = z ^ k * Q := by
      rw [hQ]
      group
    rw [hν]
    calc z ^ k * Q * (entrywiseFrobGL τ L p e ζ * pinnedX τ L β (Fr t) *
          (entrywiseFrobGL τ L p e ζ)⁻¹) * (z ^ k * Q)⁻¹
        = z ^ k * ((Q * entrywiseFrobGL τ L p e ζ * Q⁻¹) * (Q * pinnedX τ L β (Fr t) * Q⁻¹) *
            (Q * entrywiseFrobGL τ L p e ζ * Q⁻¹)⁻¹) * (z ^ k)⁻¹ := by group
      _ = z ^ k * ((ζ * m₂⁻¹) * (m₂ * pinnedX τ L β t * m₂⁻¹) * (ζ * m₂⁻¹)⁻¹) * (z ^ k)⁻¹ := by
          rw [hA, hQX, hμt]
      _ = z ^ k * (ζ * pinnedX τ L β t * ζ⁻¹) * (z ^ k)⁻¹ := by group
  · exact rootSpan_commute_of_iform hτ (hroot 0) (hroot 1) (horth 0 1 (by decide)) hu₁A
      (hzA 0 hu₁A)
  · intro h1
    obtain ⟨u₁, hu₁⟩ : ∃ u, ζ * pinnedX τ L β t * ζ⁻¹ = u := ⟨_, rfl⟩
    rw [hu₁] at h1 hu₁A
    have hu₂ : z * u₁ * z⁻¹ ∈ rootSpan τ L (blk 1) := hzA 0 hu₁A
    have hu₃ : z ^ 2 * u₁ * (z ^ 2)⁻¹ ∈ rootSpan τ L (blk 2) := by
      have h := hzA 1 hu₂
      rwa [show z * (z * u₁ * z⁻¹) * z⁻¹ = z ^ 2 * u₁ * (z ^ 2)⁻¹ by
        rw [pow_two, mul_inv_rev]; group] at h
    obtain ⟨ε, hε⟩ := exists_not_comm_negRoot hβR ht0
    have hv : ζ * pinnedX τ L (-β) ε * ζ⁻¹ ∈ rootSpan τ L (blk 0) :=
      hconjA ζ hζ _ (pinnedX_mem_rootSpan (hneg β hβ) ε)
    have c2 : Commute (z * u₁ * z⁻¹)⁻¹ (ζ * pinnedX τ L (-β) ε * ζ⁻¹) :=
      rootSpan_commute_of_iform hτ (hroot 1) (hroot 0) (horth 1 0 (by decide)) (inv_mem hu₂) hv
    have c3 : Commute (z ^ 2 * u₁ * (z ^ 2)⁻¹)⁻¹ (ζ * pinnedX τ L (-β) ε * ζ⁻¹) :=
      rootSpan_commute_of_iform hτ (hroot 2) (hroot 0) (horth 2 0 (by decide)) (inv_mem hu₃) hv
    have hu₁eq : u₁ = (z ^ 2 * u₁ * (z ^ 2)⁻¹)⁻¹ * (z * u₁ * z⁻¹)⁻¹ := by
      rw [← mul_inv_rev]
      exact eq_inv_of_mul_eq_one_left (by rw [← mul_assoc]; exact h1)
    have hcomm : Commute u₁ (ζ * pinnedX τ L (-β) ε * ζ⁻¹) := by
      have h := Commute.mul_left c3 c2
      rwa [← hu₁eq] at h
    apply hε
    calc pinnedX τ L (-β) ε * pinnedX τ L β t
        = ζ⁻¹ * ((ζ * pinnedX τ L (-β) ε * ζ⁻¹) * (ζ * pinnedX τ L β t * ζ⁻¹)) * ζ := by group
      _ = ζ⁻¹ * ((ζ * pinnedX τ L β t * ζ⁻¹) * (ζ * pinnedX τ L (-β) ε * ζ⁻¹)) * ζ := by
          rw [hu₁, ← hcomm.eq]
      _ = pinnedX τ L β t * pinnedX τ L (-β) ε := by group

end Monomial

theorem nonToralBlockCore_holds : NonToralBlockCore := by
  intro τ hτ K _ _ Fr hFr ι a B b ω hω m x hm hx
  obtain ⟨e, he, hcard⟩ := card_eq_pow_ringChar K
  haveI : Fact (ringChar K).Prime := ⟨CharP.char_is_prime K (ringChar K)⟩
  have hωS := image_eq_of_cyc (familyKernel a) B.blk B.sub B.cover ω hω
  have hz : IsMonoAt (monomialElt τ (AlgebraicClosure K) b ω) ω := by
    have h := isMonoAt_mul (isMonoAt_rootDiagUnit b)
      (isMonoAt_canonicalRep (L := AlgebraicClosure K) ω)
    rw [one_mul] at h
    exact h
  have hzN : monomialElt τ (AlgebraicClosure K) b ω ∈ Subgroup.normalizer
      (familyGroup (K := AlgebraicClosure K) a : Set (ModGL τ (AlgebraicClosure K))) :=
    mul_mem (Subgroup.le_normalizer (torus_le_familyGroup a (rootDiagUnit_mem_torusGroup b)))
      (canonicalRep_mem_normalizer_of_image hωS)
  exact exists_blockCore (Or.inr (Or.inr hτ)) (ringChar K) he Fr (fun c => by rw [hFr c, hcard])
    a B.blk (B.nonempty 0) B.sub B.cover (B.neg 0) B.orth (B.trans 0) hz hzN hω hm hx

end CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.NonToralCore

end
