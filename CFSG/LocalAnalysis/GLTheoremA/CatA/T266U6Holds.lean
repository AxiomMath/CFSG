module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.T266U6Facts
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T266U6Holds2
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10GInnExcLabel
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10R166Label
public import CFSG.LocalAnalysis.GLTheoremA.CatB.I1015U6

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T266U6

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open CFSG.ClassicalGroups.UnitaryFlag
open CFSG.RankThree.PartOne.KCUnitaryModel (idGram idForm)

open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup mem_fixSubgroup)

open scoped commutatorElement

@[expose] def U6MatInput : Prop :=
  ∀ (n : ℕ) (K : Type) [Field K] [Finite K] (h : UnitaryFieldData 2 n K), Odd n → 1 < n →
    ∀ (Ab : Subgroup (MulAut (primeFormP h (idGram K 6)))), Ab ≤ primeFormD h (idGram K 6) →
      IsElemAbelian 3 Ab → 27 ≤ Nat.card Ab →
      ∀ (Tb : Subgroup (primeFormP h (idGram K 6))), IsPGroup 2 Tb →
        (∀ α ∈ Ab, Tb.map α.toMonoidHom = Tb) → (∃ α ∈ Ab, ∃ t ∈ Tb, α t ≠ t) → U6MatConcl h Ab

section Core

variable {Ω : Type} [Group Ω] {S : Subgroup Ω}

private theorem tr_coreOf_eq_bot (hcore : GLAPPrimeCore 3 ↥S = ⊥) : GLAPPrimeCoreOf 3 S = ⊥ := by
  show (GLAPPrimeCore 3 ↥S).map S.subtype = ⊥
  rw [hcore, Subgroup.map_bot]

private theorem tr_pQuotHom_injective (hcore : GLAPPrimeCore 3 ↥S = ⊥) :
    Function.Injective (pQuotHom 3 S) :=
  (MonoidHom.ker_eq_bot_iff _).1 (by rw [ker_pQuotHom, hcore])

private theorem tr_mem_ker {P : Type} [Group P] (Φ : PSimple 3 S ≃* P) {x : ↥S}
    (hx : x ∈ (Φ.toMonoidHom.comp (chevQuotHom 3 S)).ker) :
    pQuotHom 3 S x ∈ Subgroup.center (PQuot 3 S) := by
  have h1 : chevQuotHom 3 S x = 1 := by
    have h := MonoidHom.mem_ker.1 hx
    rw [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulEquiv.map_eq_one_iff] at h
    exact h
  have h2 : pQuotHom 3 S x ∈ (QuotientGroup.mk' (Subgroup.center (PQuot 3 S))).ker :=
    MonoidHom.mem_ker.2 h1
  rwa [QuotientGroup.ker_mk'] at h2

private theorem tr_ker_le_center (hcore : GLAPPrimeCore 3 ↥S = ⊥) {P : Type} [Group P]
    (Φ : PSimple 3 S ≃* P) : (Φ.toMonoidHom.comp (chevQuotHom 3 S)).ker ≤ Subgroup.center ↥S := by
  intro x hx
  have h2 := tr_mem_ker Φ hx
  rw [Subgroup.mem_center_iff] at h2 ⊢
  intro y
  apply tr_pQuotHom_injective hcore
  rw [map_mul, map_mul]
  exact h2 (pQuotHom 3 S y)

private theorem tr_ker_isPGroup [Finite Ω] (hcore : GLAPPrimeCore 3 ↥S = ⊥) {P : Type} [Group P]
    (Φ : PSimple 3 S ≃* P) : IsPGroup 3 (Φ.toMonoidHom.comp (chevQuotHom 3 S)).ker :=
  IsPGroup.to_le ((I2611.isPGroup_center_pQuot' Nat.prime_three S).comap_of_injective
    (pQuotHom 3 S) (tr_pQuotHom_injective hcore)) (fun _ hx => tr_mem_ker Φ hx)

end Core

private theorem tr_hasLabel_U6 {Ω : Type} [Group Ω] [Finite Ω] {X S : Subgroup Ω}
    (hS : GLAPComponent 3 X S) {n : ℕ} (hcat : catalogIs (PSimple 3 S) (S10.isU6n n)) :
    Y10F.HasLabel (PQuot 3 S) (· = ⟨.twA, 5, n⟩) := by
  obtain ⟨q, hv, hp, hn, ⟨f⟩⟩ := CatB.I1015.lieIndex_isU6n hcat
  have hm := CFSG.QuasithinUnique.SQTK.statedClassicalModel_twistedA 5 q hv f
  rw [hp, hn] at hm
  have hs := chev_pSimple_simple_nonabelian Nat.prime_three hS
  exact Y10F.hasLabel_of_statedClassicalModel_PSU (r := 5)
    ⟨⟨(isQuasisimple_pQuot_of_glaPComponent Nat.prime_three hS).1⟩, hs.1, hs.2⟩ hm

private theorem tr_eq_of_canonLabel {lab : GLALabel} {n : ℕ} (h : canonLabel lab = ⟨.twA, 5, n⟩) :
    lab = ⟨.twA, 5, n⟩ := by
  obtain ⟨t, k, m⟩ := lab
  cases t <;> simp only [canonLabel] at h <;> (try split_ifs at h) <;> simp_all

private theorem tr_le_normalizer_of_commute {G : Type} [Group G] {H K : Subgroup G}
    (h : ∀ k ∈ K, ∀ x ∈ H, x * k = k * x) : K ≤ Subgroup.normalizer (H : Set G) := by
  intro k hk
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · intro hx
    rw [← h k hk x hx, mul_inv_cancel_right]
    exact hx
  · intro hx
    have h1 := h k hk _ hx
    have h2 : x = k * x * k⁻¹ := by
      have e : k * x * k⁻¹ * k = k * x := by group
      rw [e] at h1
      exact mul_left_cancel h1
    rw [h2]
    exact hx

private theorem tr_le_fix {S P : Type} [Group S] [Group P] (π : S →* P)
    (hker : π.ker ≤ Subgroup.center S) (α : MulAut S) (β : MulAut P)
    (hαβ : ∀ k, π (α k) = β (π k)) {J : Subgroup S} (hJ : ⁅J, J⁆ = J)
    (hJβ : ∀ j ∈ J, β (π j) = π j) : J ≤ fixSubgroup α := by
  rw [← hJ, Subgroup.commutator_le]
  intro x hx y hy
  exact CFSG.HardMathSupport.Solomon.Coordinator.comm_mem_fixSubgroup π hker α β hαβ
    (mem_fixSubgroup.2 (hJβ x hx)) (mem_fixSubgroup.2 (hJβ y hy))

private theorem tr_isElemAbelian_range {Ω : Type} [Group Ω] {A : Subgroup Ω} {M : Type} [Group M]
    (hA : IsElemAbelian 3 A) (f : ↥A →* M) : IsElemAbelian 3 f.range := by
  refine ⟨⟨⟨fun x y => ?_⟩⟩, fun x hx => ?_⟩
  · obtain ⟨a, ha⟩ := x.2
    obtain ⟨b, hb⟩ := y.2
    apply Subtype.ext
    show (x : M) * y = y * x
    rw [← ha, ← hb, ← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (isElemAbelian_commute hA a.2 b.2)
  · obtain ⟨a, rfl⟩ := hx
    rw [← map_pow]
    have : a ^ 3 = 1 := Subtype.ext (hA.2 a a.2)
    rw [this, map_one]

section Transport

variable {Ω : Type} [Group Ω] [Finite Ω] {S A : Subgroup Ω} {P : Type} [Group P]

private theorem tr_mem_normalizer (hSn : S.Normal) (g : Ω) :
    g ∈ Subgroup.normalizer (S : Set Ω) := by
  haveI := hSn
  rw [Subgroup.normalizer_eq_top S]
  exact Subgroup.mem_top g

private theorem tr_card_range (hSn : S.Normal) (hcore : GLAPPrimeCore 3 ↥S = ⊥)
    (hSperf : commutator ↥S = ⊤) (hrank : 3 ^ GLATwoLocalRank 3 Ω ≤ Nat.card A)
    (hAel : IsElemAbelian 3 A)
    (hE : ∃ E T : Subgroup Ω, E ≤ S ∧ IsElemAbelian 3 E ∧
      Nat.card E = 27 * Nat.card (Subgroup.center (PQuot 3 S)) ∧ T ≤ S ∧ IsPGroup 2 T ∧
      ¬ T ≤ GLAPPrimeCoreOf 3 S ∧ E ≤ Subgroup.normalizer (T : Set Ω))
    (π : ↥S →* P) (hker : π.ker ≤ Subgroup.center ↥S) (ψ : ↥A →* MulAut P)
    (hψ : ∀ (g : Ω) (hg : g ∈ A) (k k' : ↥S), (k' : Ω) = g * k * g⁻¹ → ψ ⟨g, hg⟩ (π k) = π k') :
    27 ≤ Nat.card ψ.range := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hcent : ∀ a : ↥A, ψ a = 1 → ∀ s ∈ S, s * (a : Ω) = a * s := by
    intro a ha1 s hs
    have hle := tr_le_fix π hker (S.normalizerMonoidHom ⟨(a : Ω), tr_mem_normalizer hSn a⟩) 1
      (fun k => by
        rw [MulAut.one_apply, ← hψ a a.2 k _ rfl]
        show ψ a (π k) = π k
        rw [ha1, MulAut.one_apply])
      (J := ⊤) (by rw [← commutator_def]; exact hSperf) (fun j _ => rfl)
    have h1 := mem_fixSubgroup.1 (hle (Subgroup.mem_top ⟨s, hs⟩))
    have h2 : (a : Ω) * s * (a : Ω)⁻¹ = s := congrArg Subtype.val h1
    calc s * (a : Ω) = (a : Ω) * s * (a : Ω)⁻¹ * a := by rw [h2]
      _ = a * s := by group
  set C : Subgroup Ω := ψ.ker.map A.subtype
  have hCcent : ∀ c ∈ C, ∀ s ∈ S, s * c = c * s := by
    rintro _ ⟨a, ha, rfl⟩ s hs
    exact hcent a (MonoidHom.mem_ker.1 ha) s hs
  have hCel : IsElemAbelian 3 C := isElemAbelian_mono hAel (Subgroup.map_subtype_le _)
  obtain ⟨E, T₀, hES, hEel, hEcard, hT₀S, hT₀2, hT₀n, hEN⟩ := hE
  have hT₀ne : T₀ ≠ ⊥ := by
    rintro rfl
    exact hT₀n bot_le
  have hEC : IsElemAbelian 3 (E ⊔ C) :=
    I2611.isElemAbelian_sup_of_commute hEel hCel (fun e he c hc => hCcent c hc e (hES he))
  have hECN : E ⊔ C ≤ Subgroup.normalizer (T₀ : Set Ω) :=
    sup_le hEN (tr_le_normalizer_of_commute fun c hc x hx => hCcent c hc x (hT₀S hx))
  have hcardEC : Nat.card ↥(E ⊔ C) ≤ 3 ^ GLATwoLocalRank 3 Ω :=
    GL83.PiGen.card_le_pow_twoLocalRank hEC hT₀2 hT₀ne hECN
  have hCN : C ≤ Subgroup.normalizer (E : Set Ω) :=
    tr_le_normalizer_of_commute fun c hc x hx => hCcent c hc x (hES hx)
  have hsup := CFSG.GroupTheory.CoprimeActionSupport.NormalSubgroupSylowJoin.card_sup_mul_card_inf hCN
  have hCE : C ⊓ E ≤ (Subgroup.center ↥S).map S.subtype := by
    rintro x ⟨hxC, hxE⟩
    exact ⟨⟨x, hES hxE⟩, Subgroup.mem_center_iff.2 fun s => Subtype.ext (hCcent x hxC s s.2), rfl⟩
  have hzS : Nat.card (Subgroup.center ↥S) ≤ Nat.card (Subgroup.center (PQuot 3 S)) := by
    rw [← Subgroup.card_map_of_injective (f := pQuotHom 3 S) (tr_pQuotHom_injective hcore)]
    exact Subgroup.card_le_of_le
      (Subgroup.map_center_le_center (f := pQuotHom 3 S) (pQuotHom_surjective 3 S))
  have hinf : Nat.card ↥(C ⊓ E) ≤ Nat.card (Subgroup.center (PQuot 3 S)) :=
    calc Nat.card ↥(C ⊓ E) ≤ Nat.card ((Subgroup.center ↥S).map S.subtype) :=
          Subgroup.card_le_of_le hCE
      _ = Nat.card (Subgroup.center ↥S) := Subgroup.card_subtype _ _
      _ ≤ _ := hzS
  have hz : 0 < Nat.card (Subgroup.center (PQuot 3 S)) := by
    have := Nat.card_pos (α := ↥E)
    omega
  have hA := Subgroup.card_ker_mul_card_range ψ
  have hCcard : Nat.card C = Nat.card ψ.ker := Subgroup.card_subtype A ψ.ker
  have hle1 : Nat.card ↥(C ⊔ E) ≤ Nat.card ψ.ker * Nat.card ψ.range := by
    rw [sup_comm, hA]
    exact hcardEC.trans hrank
  have hc0 : 0 < Nat.card ψ.ker := Nat.card_pos
  have h4 := Nat.mul_le_mul hle1 hinf
  rw [hsup, hCcard, hEcard] at h4
  have h5 : (Nat.card ψ.ker * Nat.card (Subgroup.center (PQuot 3 S))) * 27 ≤
      (Nat.card ψ.ker * Nat.card (Subgroup.center (PQuot 3 S))) * Nat.card ψ.range := by
    calc _ = Nat.card ψ.ker * (27 * Nat.card (Subgroup.center (PQuot 3 S))) := by ring
      _ ≤ _ := h4
      _ = _ := by ring
  exact Nat.le_of_mul_le_mul_left h5 (Nat.mul_pos hc0 hz)

private theorem tr_Tb (hSn : S.Normal) (π : ↥S →* P) (hker3 : IsPGroup 3 π.ker) (ψ : ↥A →* MulAut P)
    (hψ : ∀ (g : Ω) (hg : g ∈ A) (k k' : ↥S), (k' : Ω) = g * k * g⁻¹ → ψ ⟨g, hg⟩ (π k) = π k')
    (hT : ∃ T : Subgroup Ω, T ≤ S ∧ IsPGroup 2 T ∧ A ≤ Subgroup.normalizer (T : Set Ω) ∧
      (⁅T, A⁆ : Subgroup Ω) ≠ ⊥) :
    ∃ Tb : Subgroup P, IsPGroup 2 Tb ∧ (∀ α ∈ ψ.range, Tb.map α.toMonoidHom = Tb) ∧
      ∃ α ∈ ψ.range, ∃ t ∈ Tb, α t ≠ t := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨T, hTS, hT2, hTN, hTA⟩ := hT
  have hT2' : IsPGroup 2 (T.subgroupOf S) := (Y10F.isPGroup_subgroupOf_iff hTS).2 hT2
  refine ⟨(T.subgroupOf S).map π, hT2'.map π, ?_, ?_⟩
  · rintro _ ⟨a, rfl⟩
    obtain ⟨g, hg⟩ := a
    ext x
    constructor
    · rintro ⟨_, ⟨k, hk, rfl⟩, rfl⟩
      refine ⟨⟨g * k * g⁻¹, hSn.conj_mem k k.2 g⟩, ?_, (hψ g hg k _ rfl).symm⟩
      exact Subgroup.mem_subgroupOf.2
        ((Subgroup.mem_normalizer_iff.1 (hTN hg) k).1 (Subgroup.mem_subgroupOf.1 hk))
    · rintro ⟨k, hk, rfl⟩
      have hk' : g⁻¹ * k * g ∈ S := by
        have := hSn.conj_mem k k.2 g⁻¹
        rwa [inv_inv] at this
      refine ⟨π ⟨g⁻¹ * k * g, hk'⟩, ⟨⟨g⁻¹ * k * g, hk'⟩, ?_, rfl⟩, ?_⟩
      · have h1 := (Subgroup.mem_normalizer_iff.1 (hTN (A.inv_mem hg)) k).1
          (Subgroup.mem_subgroupOf.1 hk)
        rw [inv_inv] at h1
        exact Subgroup.mem_subgroupOf.2 h1
      · show ψ ⟨g, hg⟩ (π ⟨g⁻¹ * k * g, hk'⟩) = π k
        exact hψ g hg _ k (by simp [mul_assoc])
  · by_contra hcon
    push Not at hcon
    apply hTA
    rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
    intro t ht
    rw [Subgroup.mem_centralizer_iff]
    intro a ha
    have hk' : a * t * a⁻¹ ∈ S := hSn.conj_mem t (hTS ht) a
    have h1 := hcon (ψ ⟨a, ha⟩) ⟨⟨a, ha⟩, rfl⟩ (π ⟨t, hTS ht⟩)
      ⟨⟨t, hTS ht⟩, Subgroup.mem_subgroupOf.2 ht, rfl⟩
    rw [hψ a ha ⟨t, hTS ht⟩ ⟨a * t * a⁻¹, hk'⟩ rfl] at h1
    have hmem : (⟨a * t * a⁻¹, hk'⟩ : ↥S) * (⟨t, hTS ht⟩ : ↥S)⁻¹ ∈ π.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, h1, mul_inv_cancel]
    have hmemT : (⟨a * t * a⁻¹, hk'⟩ : ↥S) * (⟨t, hTS ht⟩ : ↥S)⁻¹ ∈ T.subgroupOf S := by
      rw [Subgroup.mem_subgroupOf]
      exact T.mul_mem ((Subgroup.mem_normalizer_iff.1 (hTN ha) t).1 ht) (T.inv_mem ht)
    have hdisj := IsPGroup.disjoint_of_ne 2 3 (by norm_num) (T.subgroupOf S) π.ker hT2' hker3
    have h2 := Subgroup.disjoint_def.1 hdisj hmemT hmem
    have h3 : a * t * a⁻¹ = t := congrArg Subtype.val (mul_inv_eq_one.1 h2)
    calc a * t = a * t * a⁻¹ * a := by group
      _ = t * a := by rw [h3]

private theorem tr_conclude {n : ℕ} [Finite P] (hSn : S.Normal) (hcore : GLAPPrimeCore 3 ↥S = ⊥)
    (π : ↥S →* P) (hπ : Function.Surjective π) (hker : π.ker ≤ Subgroup.center ↥S)
    (hker3 : IsPGroup 3 π.ker) (ψ : ↥A →* MulAut P)
    (hψ : ∀ (g : Ω) (hg : g ∈ A) (k k' : ↥S), (k' : Ω) = g * k * g⁻¹ → ψ ⟨g, hg⟩ (π k) = π k')
    {Eb : Subgroup (MulAut P)} {yb : MulAut P} (hEb : Eb ≤ ψ.range)
    (hEbc : Nat.card ψ.range ≤ 3 * Nat.card Eb) (hyb : yb ∈ Eb) (hyb1 : yb ≠ 1)
    {Jb : Subgroup P} (hJb : GLAPComponent 3 (fixSubgroup yb) Jb)
    (hJbE : ∀ ε ∈ Eb, Jb ≤ fixSubgroup ε) (hJbcat : catalogIs (PSimple 3 Jb) (S10.isUrn n))
    {Tb' : Subgroup P} (hTb'2 : IsPGroup 2 Tb') (hTb'y : Tb' ≤ fixSubgroup yb)
    (hTb'N : ∀ α ∈ ψ.range, Tb'.map α.toMonoidHom = Tb')
    (hTb'A : ∃ α ∈ ψ.range, ∃ t ∈ Tb', α t ≠ t) (hTb'8 : Nat.card Tb' ≠ 8) :
    ∃ (E₀ : Subgroup Ω) (y : Ω), E₀ ≤ A ∧ Nat.card A ≤ 3 * Nat.card E₀ ∧ y ∈ E₀ ∧
      GLAPLayer 3 (S ⊓ Subgroup.centralizer (E₀ : Set Ω)) ≠ ⊥ ∧ ¬ CentMod 3 S y ∧
      ∃ J : Subgroup Ω, GLAPComponent 3 (S ⊓ Subgroup.centralizer ({y} : Set Ω)) J ∧
        catalogIs (PSimple 3 J) (S10.isUrn n) ∧
      ∃ T : Subgroup Ω, T ≤ S ⊓ Subgroup.centralizer ({y} : Set Ω) ∧ IsPGroup 2 T ∧
        A ≤ Subgroup.normalizer (T : Set Ω) ∧ (⁅T, A⁆ : Subgroup Ω) ≠ ⊥ ∧
        IsEmpty (T ≃* QuaternionGroup 2) := by
  classical
  have hp3 : Nat.Prime 3 := Nat.prime_three
  haveI : Fact (Nat.Prime 3) := ⟨hp3⟩
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hN := tr_mem_normalizer hSn
  have hψα : ∀ (g : Ω) (hg : g ∈ A) (k : ↥S),
      ψ ⟨g, hg⟩ (π k) = π (S.normalizerMonoidHom ⟨g, hN g⟩ k) :=
    fun g hg k => hψ g hg k _ rfl
  obtain ⟨⟨y, hyA⟩, hyb'⟩ := hEb hyb
  have hcard : Nat.card A ≤ 3 * Nat.card ((Eb.comap ψ).map A.subtype) := by
    rw [Subgroup.card_subtype, ← Subgroup.index_mul_card (Eb.comap ψ), Subgroup.index_comap]
    have h1 := Subgroup.relIndex_mul_card Eb ψ.range
    rw [inf_eq_left.2 hEb] at h1
    have hpos : 0 < Nat.card Eb := Nat.card_pos
    have h3 : Eb.relIndex ψ.range ≤ 3 := by
      by_contra hc
      push Not at hc
      have : 4 * Nat.card Eb ≤ Eb.relIndex ψ.range * Nat.card Eb := Nat.mul_le_mul_right _ hc
      omega
    exact Nat.mul_le_mul_right _ h3
  have hyE₀ : y ∈ (Eb.comap ψ).map A.subtype :=
    ⟨⟨y, hyA⟩, show ψ ⟨y, hyA⟩ ∈ Eb by rw [hyb']; exact hyb, rfl⟩
  have hncent : ¬ CentMod 3 S y := by
    intro hc
    apply hyb1
    rw [← hyb']
    ext x
    obtain ⟨k, rfl⟩ := hπ x
    rw [hψα, MulAut.one_apply]
    congr 1
    apply Subtype.ext
    show y * k * y⁻¹ = k
    have h1 : ⁅(k : Ω), y⁆ ∈ GLAPPrimeCoreOf 3 S :=
      hc.2 (Subgroup.commutator_mem_commutator k.2 (Subgroup.mem_zpowers y))
    rw [tr_coreOf_eq_bot hcore, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at h1
    rw [← h1, mul_inv_cancel_right]
  have hαβ : ∀ k, π (S.normalizerMonoidHom ⟨y, hN y⟩ k) = yb (π k) := fun k => by
    rw [← hyb', hψα]
  obtain ⟨J₀, hJ₀, hJ₀m⟩ := CFSG.HardMathSupport.Solomon.Coordinator.exists_glaPComponent_map_fixSubgroup
    π hker _ yb hαβ hπ hp3 hJb
  subst hJ₀m
  rw [fixSubgroup_normalizerMonoidHom (hN y)] at hJ₀
  have hJ : GLAPComponent 3 (S ⊓ Subgroup.centralizer ({y} : Set Ω)) (J₀.map S.subtype) := by
    have := (Y10F.glaPComponent_map_iff hp3 S.subtype_injective).2 hJ₀
    rwa [Y10F.subgroupOf_map_subtype_of_le inf_le_left] at this
  have hJcat : catalogIs (PSimple 3 (J₀.map S.subtype)) (S10.isUrn n) := by
    obtain ⟨e₁⟩ := nonempty_pSimple_equiv_map hp3 S.subtype hJ₀ hJ
    obtain ⟨e₂⟩ := nonempty_pSimple_equiv_map hp3 π hJ₀ hJb
    obtain ⟨i, hi, ⟨f⟩⟩ := hJbcat
    exact ⟨i, hi, ⟨(e₁.symm.trans e₂).trans f⟩⟩
  have hJE : ∀ e ∈ (Eb.comap ψ).map A.subtype, ∀ j ∈ J₀.map S.subtype, e * j = j * e := by
    rintro _ ⟨⟨e, heA⟩, he, rfl⟩ _ ⟨j, hj, rfl⟩
    have hle := tr_le_fix π hker (S.normalizerMonoidHom ⟨e, hN e⟩) (ψ ⟨e, heA⟩)
      (fun k => (hψα e heA k).symm) (GLTheoremB.glaPComponent_perfect hJ₀)
      (fun j hj => mem_fixSubgroup.1 (hJbE (ψ ⟨e, heA⟩) he ⟨j, hj, rfl⟩))
    have h2 : e * j * e⁻¹ = j := congrArg Subtype.val (mem_fixSubgroup.1 (hle hj))
    show e * j = j * e
    calc e * (j : Ω) = e * j * e⁻¹ * e := by group
      _ = j * e := by rw [h2]
  have hJle : J₀.map S.subtype ≤
      S ⊓ Subgroup.centralizer (((Eb.comap ψ).map A.subtype : Subgroup Ω) : Set Ω) := by
    intro x hx
    exact Subgroup.mem_inf.2 ⟨Subgroup.map_subtype_le _ hx,
      Subgroup.mem_centralizer_iff.2 fun e he => hJE e he x hx⟩
  have hCle : S ⊓ Subgroup.centralizer (((Eb.comap ψ).map A.subtype : Subgroup Ω) : Set Ω) ≤
      S ⊓ Subgroup.centralizer ({y} : Set Ω) :=
    inf_le_inf_left _ (Subgroup.centralizer_le (Set.singleton_subset_iff.2 hyE₀))
  have hJE₀ := GLTheoremB.glaPComponent_of_le hp3 hJ hJle hCle
  have hlayer : GLAPLayer 3 (S ⊓ Subgroup.centralizer
      (((Eb.comap ψ).map A.subtype : Subgroup Ω) : Set Ω)) ≠ ⊥ := by
    intro hbot
    have hle : J₀.map S.subtype ≤ GLAPLayer 3 (S ⊓ Subgroup.centralizer
        (((Eb.comap ψ).map A.subtype : Subgroup Ω) : Set Ω)) := le_sSup hJE₀
    rw [hbot, le_bot_iff] at hle
    exact glaPComponent_ne_bot' hJE₀ hle
  have hC2 : ¬ 2 ∣ Nat.card π.ker := by
    obtain ⟨m, hm⟩ := hker3.exists_card_eq
    rw [hm]
    intro h2
    have := Nat.Prime.dvd_of_dvd_pow Nat.prime_two h2
    omega
  have hmemT₁ : ∀ e : ↥S, e ∈ CFSG.LieType.CentralExt.liftSubgroup 2 π Tb' ↔
      π e ∈ Tb' ∧ ∃ m : ℕ, orderOf e = 2 ^ m := fun e =>
    CFSG.LieType.CentralExt.mem_liftSubgroup_iff hker hTb'2
  have hT₁inv : ∀ g (hg : g ∈ A), ∀ k ∈ CFSG.LieType.CentralExt.liftSubgroup 2 π Tb',
      S.normalizerMonoidHom ⟨g, hN g⟩ k ∈ CFSG.LieType.CentralExt.liftSubgroup 2 π Tb' := by
    intro g hg k hk
    rw [hmemT₁] at hk ⊢
    obtain ⟨hk1, m, hm⟩ := hk
    refine ⟨?_, m, by rw [MulEquiv.orderOf_eq]; exact hm⟩
    have h1 := Subgroup.mem_map_of_mem (ψ ⟨g, hg⟩).toMonoidHom hk1
    rw [hTb'N (ψ ⟨g, hg⟩) ⟨⟨g, hg⟩, rfl⟩] at h1
    rw [← hψα g hg k]
    exact h1
  refine ⟨(Eb.comap ψ).map A.subtype, y, Subgroup.map_subtype_le _, hcard, hyE₀, hlayer, hncent,
    J₀.map S.subtype, hJ, hJcat, (CFSG.LieType.CentralExt.liftSubgroup 2 π Tb').map S.subtype,
    ?_, (CFSG.LieType.CentralExt.liftSubgroup_isPGroup hker hTb'2).map S.subtype, ?_, ?_, ?_⟩
  ·
    rintro _ ⟨k, hk, rfl⟩
    refine Subgroup.mem_inf.2 ⟨k.2, Subgroup.mem_centralizer_singleton_iff.2 ?_⟩
    have heq : S.normalizerMonoidHom ⟨y, hN y⟩ k = k := by
      apply CFSG.LieType.CentralExt.eq_of_pElement hker hC2
      · rw [hαβ]
        exact mem_fixSubgroup.1 (hTb'y ((hmemT₁ k).1 hk).1)
      · exact ((hmemT₁ _).1 (hT₁inv y hyA k hk)).2
      · exact ((hmemT₁ k).1 hk).2
    have h2 : y * k * y⁻¹ = k := congrArg Subtype.val heq
    show (k : Ω) * y = y * k
    calc (k : Ω) * y = y * k * y⁻¹ * y := by rw [h2]
      _ = y * k := by group
  ·
    have hfwd : ∀ g ∈ A, ∀ x ∈ (CFSG.LieType.CentralExt.liftSubgroup 2 π Tb').map S.subtype,
        g * x * g⁻¹ ∈ (CFSG.LieType.CentralExt.liftSubgroup 2 π Tb').map S.subtype := by
      rintro g hg _ ⟨k, hk, rfl⟩
      exact ⟨_, hT₁inv g hg k hk, rfl⟩
    intro a ha
    rw [Subgroup.mem_normalizer_iff]
    intro x
    refine ⟨hfwd a ha x, fun hx => ?_⟩
    have := hfwd a⁻¹ (A.inv_mem ha) _ hx
    simpa [mul_assoc] using this
  ·
    obtain ⟨_, ⟨⟨a, ha⟩, rfl⟩, t, ht, hne⟩ := hTb'A
    intro hbot
    have hpt : ∃ m : ℕ, orderOf t = 2 ^ m :=
      CFSG.LieType.CentralExt.exists_orderOf_eq_pow_of_mem hTb'2 ⟨t, ht⟩
    obtain ⟨k, hk, hkt⟩ : ∃ k ∈ CFSG.LieType.CentralExt.liftSubgroup 2 π Tb', π k = t :=
      ⟨_, CFSG.LieType.CentralExt.pLift_mem_liftSubgroup hπ hker hC2 hTb'2 ht,
        CFSG.LieType.CentralExt.map_pLift hπ hC2 hpt⟩
    apply hne
    rw [← hkt, hψα a ha]
    congr 1
    apply Subtype.ext
    show a * (k : Ω) * a⁻¹ = k
    have hc : ⁅(k : Ω), a⁆ ∈
        (⁅(CFSG.LieType.CentralExt.liftSubgroup 2 π Tb').map S.subtype, A⁆ : Subgroup Ω) :=
      Subgroup.commutator_mem_commutator ⟨k, hk, rfl⟩ ha
    rw [hbot, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at hc
    rw [← hc, mul_inv_cancel_right]
  ·
    refine ⟨fun e => hTb'8 ?_⟩
    have h1 : Nat.card ((CFSG.LieType.CentralExt.liftSubgroup 2 π Tb').map S.subtype) =
        Nat.card Tb' := by
      rw [Subgroup.card_subtype]
      exact Nat.card_congr (CFSG.LieType.CentralExt.liftSubgroupEquiv hπ hker hC2 hTb'2).toEquiv
    rw [← h1, Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card, QuaternionGroup.card]

end Transport

section Certs


theorem t266U6Fact_of_matInput (hmat : U6MatInput) :
    ∀ n, CFSG.LocalAnalysis.GLTheoremA.T266.T266U6Fact n := by
  intro n Ω _ _ S A hn hn1 hSn hSq hcore _ hcat hAel _ hrank _ hInn hT _
  classical
  have hSc : GLAPComponent 3 S S :=
    CFSG.HardMathSupport.Timmesfeld.Proving.glaPComponent_self hSq hcore
  obtain ⟨hX, lab, hlam, hraw⟩ := hInn.2
  have hXL : Y10F.HasLabel (PQuot 3 S) (· = lab) :=
    ⟨hX, lab, hlam, CFSG.StandardType.Canonical.largeEvenRawDatum_mono
      (fun _ _ _ _ ⟨hs, hna, θ, _⟩ => ⟨hs, hna, θ, rfl⟩) hraw⟩
  have hc := Y10GInnExcLabel.canonLabel_eq_of_hasLabel CFSG.StandardType.ggLabelRigidInput_holds
    hXL (tr_hasLabel_U6 hSc hcat)
  have hlab : lab = ⟨.twA, 5, n⟩ := tr_eq_of_canonLabel (by rw [hc]; rfl)
  subst hlab
  obtain ⟨K, _, _, hKcard, -, -, θ, hall⟩ := hraw
  have hKcard' : Nat.card K = (2 ^ n) ^ 2 := hKcard
  have h : UnitaryFieldData 2 n K :=
    ⟨Nat.prime_two, by omega, by rw [hKcard', ← pow_mul, mul_comm]⟩
  have hd : (1 : ℕ) ≤ 6 := by norm_num
  set Φ : PSimple 3 S ≃* primeFormP h (idGram K 6) :=
    θ.trans (CFSG.StandardType.InndiagSU.projEquiv h hd)
  set π : ↥S →* primeFormP h (idGram K 6) := Φ.toMonoidHom.comp (chevQuotHom 3 S)
  set ψ : ↥A →* MulAut (primeFormP h (idGram K 6)) :=
    ((MulAut.congr Φ).toMonoidHom.comp (chevAut 3 S)).comp (Subgroup.inclusion hInn.1)
  have hπs : Function.Surjective π := Φ.surjective.comp (chevQuotHom_surjective 3 S)
  have hker : π.ker ≤ Subgroup.center ↥S := tr_ker_le_center hcore Φ
  have hker3 : IsPGroup 3 π.ker := tr_ker_isPGroup hcore Φ
  have hψ : ∀ (g : Ω) (hg : g ∈ A) (k k' : ↥S), (k' : Ω) = g * k * g⁻¹ →
      ψ ⟨g, hg⟩ (π k) = π k' := by
    intro g hg k k' hk'
    show Φ (chevAut 3 S ⟨g, hInn.1 hg⟩ (Φ.symm (Φ (chevQuotHom 3 S k)))) = Φ (chevQuotHom 3 S k')
    rw [MulEquiv.symm_apply_apply, chevAut_chevQuotHom]
    congr 2
    exact Subtype.ext ((chev_coe_normalizerMonoidHom _ _).trans hk'.symm)
  have hψD : ψ.range ≤ primeFormD h (idGram K 6) := by
    rintro _ ⟨⟨a, ha⟩, rfl⟩
    obtain ⟨φ, hφ, hind⟩ := hall a⁻¹ (A.inv_mem ha)
    have hφeq : φ = MulAut.congr θ (chevAut 3 S ⟨a, hInn.1 ha⟩) := by
      ext x
      obtain ⟨s, rfl⟩ := θ.surjective x
      obtain ⟨q, rfl⟩ := QuotientGroup.mk_surjective s
      obtain ⟨k, rfl⟩ := QuotientGroup.mk_surjective q
      rw [MulAut.congr_apply, MulEquiv.trans_apply, MulEquiv.trans_apply, MulEquiv.symm_apply_apply]
      have hc := chevAut_chevQuotHom 3 S ⟨a, hInn.1 ha⟩ k
      have hi := hind (QuotientGroup.mk k) (QuotientGroup.mk (S.normalizerMonoidHom ⟨a, hInn.1 ha⟩ k))
        ⟨k, S.normalizerMonoidHom ⟨a, hInn.1 ha⟩ k, rfl, rfl,
          by rw [chev_coe_normalizerMonoidHom, inv_inv]⟩
      exact hi.trans (congrArg θ hc.symm)
    have hmem := CFSG.StandardType.InndiagSU.congr_mem_primeFormD h hd hKcard' hφ
    rw [hφeq] at hmem
    convert hmem using 1
    ext x
    rfl
  have hel : IsElemAbelian 3 ψ.range := tr_isElemAbelian_range hAel ψ
  have hGA : GriessAllModelsStatement :=
    CFSG.Milestones.cl_lit_griess_schur_multipliers_all_models_statement
  have h27 := tr_card_range hSn hcore hSq.1 hrank hAel (CatB.I1015.u6_exists_E_T hGA hn hSc hcat)
    π hker ψ hψ
  obtain ⟨Tb, hTb2, hTbN, hTbA⟩ := tr_Tb hSn π hker3 ψ hψ hT
  obtain ⟨Eb, yb, hEb, hEbc, hyb, hyb1, ⟨Jb, hJb, hJbE, hJbcat⟩, Tb', hTb'2, hTb'y, hTb'N, hTb'A,
    hTb'8⟩ := hmat n K h hn hn1 ψ.range hψD hel h27 Tb hTb2 hTbN hTbA
  exact tr_conclude hSn hcore π hπs hker hker3 ψ hψ hEb hEbc hyb hyb1 hJb hJbE hJbcat hTb'2 hTb'y
    hTb'N hTb'A hTb'8

theorem t266U6Fact_holds : ∀ n, CFSG.LocalAnalysis.GLTheoremA.T266.T266U6Fact n :=
  t266U6Fact_of_matInput fun _ _ _ _ h hn hn1 _ hAbD hAbel hAbcard _ hTb2 hTbN hTbA =>
    u6MatConcl_of_twoGroup h hn hn1 hAbD hAbel hAbcard hTb2 hTbN hTbA

end Certs

end CFSG.LocalAnalysis.GLTheoremA.T266U6

end
