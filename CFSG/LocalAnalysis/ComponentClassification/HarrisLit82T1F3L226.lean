module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1F3L226Bar
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1F3FGDefs

public noncomputable section

namespace CFSG.ComponentClassification.HarrisLit.T1

open CFSG Subgroup Assembly.LowTwoRank CFSG.ComponentClassification.UnbalancedLayer
open scoped commutatorElement

@[expose] def Harris82Lemma226ThreePerfect : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (z₁ z₂ : G), orderOf z₁ = 2 → orderOf z₂ = 2 → z₁ ≠ z₂ →
    z₁ * z₂ = z₂ * z₁ → ∀ L₁ L₂ : Subgroup G,
    IsSolvableTwoComponentIn L₁ (centralizer {z₁} ⊓ centralizer {z₂}) →
    IsTwoComponentIn L₂ (centralizer {z₁} ⊓ centralizer {z₂}) → z₂ ∈ L₂ →
    ¬ (((pPrimeCore 2 ↥(centralizer ({z₁} : Set G))).map (centralizer {z₁}).subtype ⊔
        GH74.GLS.oPrimeResidualOf 3 L₁).subgroupOf (centralizer {z₁})).IsSubnormal →
    ∃ K : Subgroup G, IsTwoComponentIn K (centralizer {z₁}) ∧
      GH74.GLS.oPrimeResidualOf 2 L₂ ≤ K ∧
      centralizer {z₁} ⊓ centralizer {z₂} ≤ normalizer (K : Set G) ∧
      ⁅K, GH74.GLS.oPrimeResidualOf 3 L₁⁆ = K ∧
      ∃ hz₂K : z₂ ∈ K, (QuotientGroup.mk ⟨z₂, hz₂K⟩ : ↥K ⧸ pPrimeCore 2 ↥K) ∉
        center (↥K ⧸ pPrimeCore 2 ↥K)

@[expose] def Harris82Lemma226ThreeSolvable : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (z₁ z₂ : G), orderOf z₁ = 2 → orderOf z₂ = 2 → z₁ ≠ z₂ →
    z₁ * z₂ = z₂ * z₁ → ∀ L₁ L₂ : Subgroup G,
    IsSolvableTwoComponentIn L₁ (centralizer {z₁} ⊓ centralizer {z₂}) →
    IsSolvableTwoComponentIn L₂ (centralizer {z₁} ⊓ centralizer {z₂}) → z₂ ∈ L₂ →
    ¬ (((pPrimeCore 2 ↥(centralizer ({z₁} : Set G))).map (centralizer {z₁}).subtype ⊔
        GH74.GLS.oPrimeResidualOf 3 L₁).subgroupOf (centralizer {z₁})).IsSubnormal →
    ∃ K : Subgroup G, IsTwoComponentIn K (centralizer {z₁}) ∧
      GH74.GLS.oPrimeResidualOf 2 L₂ ≤ K ∧
      centralizer {z₁} ⊓ centralizer {z₂} ≤ normalizer (K : Set G) ∧
      ⁅K, GH74.GLS.oPrimeResidualOf 3 L₁⁆ = K ∧
      ∃ hz₂K : z₂ ∈ K, (QuotientGroup.mk ⟨z₂, hz₂K⟩ : ↥K ⧸ pPrimeCore 2 ↥K) ∉
        center (↥K ⧸ pPrimeCore 2 ↥K)

theorem harris82Lemma226Three_of_split (hP : Harris82Lemma226ThreePerfect)
    (hS : Harris82Lemma226ThreeSolvable) : Harris82Lemma226Three := by
  intro G _ _ z₁ z₂ hz₁ hz₂ hne hc L₁ L₂ hL₁ hL₂ hz₂L hns
  rcases hL₂ with h | h
  · exact hP G z₁ z₂ hz₁ hz₂ hne hc L₁ L₂ hL₁ h hz₂L hns
  · exact hS G z₁ z₂ hz₁ hz₂ hne hc L₁ L₂ hL₁ h hz₂L hns

namespace F3L226

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem hatIn_mono {w : G} {J L : Subgroup G} (h : J ≤ L) : hatIn w J ≤ hatIn w L := by
  rintro _ ⟨x, hx, rfl⟩
  exact ⟨x, h hx, rfl⟩

omit [Finite G] in
theorem oPrimeResidual_normal (p : ℕ) (X : Type*) [Group X] :
    (GH74.GLS.oPrimeResidual p X).Normal := by
  refine ⟨fun n hn g => ?_⟩
  unfold GH74.GLS.oPrimeResidual at hn ⊢
  induction hn using Subgroup.closure_induction with
  | mem x hx =>
    obtain ⟨k, hk⟩ := hx
    refine Subgroup.subset_closure ⟨k, ?_⟩
    calc (g * x * g⁻¹) ^ (p ^ k) = g * x ^ (p ^ k) * g⁻¹ := by rw [conj_pow]
      _ = 1 := by rw [hk]; group
  | one => simp
  | mul a b _ _ ha hb =>
    have h1 : g * (a * b) * g⁻¹ = (g * a * g⁻¹) * (g * b * g⁻¹) := by group
    rw [h1]
    exact Subgroup.mul_mem _ ha hb
  | inv a _ ha =>
    have h1 : g * a⁻¹ * g⁻¹ = (g * a * g⁻¹)⁻¹ := by group
    rw [h1]
    exact Subgroup.inv_mem _ ha

omit [Finite G] in
theorem conj_mem_oPrimeResidualOf (p : ℕ) {L : Subgroup G} {g x : G} (hg : g ∈ L)
    (hx : x ∈ GH74.GLS.oPrimeResidualOf p L) : g * x * g⁻¹ ∈ GH74.GLS.oPrimeResidualOf p L := by
  obtain ⟨y, hy, rfl⟩ := hx
  exact ⟨⟨g, hg⟩ * y * ⟨g, hg⟩⁻¹, (oPrimeResidual_normal p ↥L).conj_mem y hy _, rfl⟩

omit [Finite G] in
theorem hatIn_le_normalizer {w : G} {J K : Subgroup G} (hJN : J ≤ normalizer (K : Set G)) :
    hatIn w J ≤ normalizer ((hatIn w K : Subgroup (MBar w)) : Set (MBar w)) := by
  rintro _ ⟨j, hj, rfl⟩
  have hjN : (j : G) ∈ normalizer (K : Set G) := hJN hj
  rw [mem_normalizer_iff]
  intro y
  constructor
  · rintro ⟨k, hk, rfl⟩
    refine ⟨j * k * j⁻¹, ?_, by simp⟩
    exact (mem_normalizer_iff.mp hjN k).mp hk
  · rintro ⟨k, hk, hky⟩
    refine ⟨j⁻¹ * k * j, ?_, ?_⟩
    · have h1 := (mem_normalizer_iff.mp (inv_mem hjN) k).mp hk
      rw [inv_inv] at h1
      exact h1
    · have h2 : y = (QuotientGroup.mk' (pPrimeCore 2 ↥(centralizer ({w} : Set G))) j)⁻¹ *
          (QuotientGroup.mk' (pPrimeCore 2 ↥(centralizer ({w} : Set G))) j * y *
            (QuotientGroup.mk' (pPrimeCore 2 ↥(centralizer ({w} : Set G))) j)⁻¹) *
          QuotientGroup.mk' (pPrimeCore 2 ↥(centralizer ({w} : Set G))) j := by group
      rw [h2, ← hky]
      simp only [map_mul, map_inv]

theorem mem_pPrimeCore_iff {w : G} {K : Subgroup G} (hK : IsTwoComponentIn K (centralizer {w}))
    {x : G} (hx : x ∈ K) :
    (⟨x, hx⟩ : ↥K) ∈ pPrimeCore 2 ↥K ↔
      (⟨x, hK.1 hx⟩ : ↥(centralizer ({w} : Set G))) ∈
        pPrimeCore 2 ↥(centralizer ({w} : Set G)) := by
  set C := centralizer ({w} : Set G) with hC
  have key := F3L221.map_pPrimeCore_eq_inf (X := ↥C) (L := K.subgroupOf C) hK.2.1
  let eK : ↥(K.subgroupOf C) ≃* ↥K := subgroupOfEquivOfLe hK.1
  have hiso := pPrimeCore_map_iso 2 eK
  constructor
  · intro h
    rw [← hiso] at h
    obtain ⟨y, hy, hyx⟩ := h
    have h1 : ((y : ↥C) : ↥C) ∈ K.subgroupOf C ⊓ pPrimeCore 2 ↥C := by
      rw [← key]
      exact ⟨y, hy, rfl⟩
    have h2 : (y : ↥C) = ⟨x, hK.1 hx⟩ := by
      apply Subtype.ext
      have h3 := congrArg Subtype.val hyx
      exact h3
    rw [← h2]
    exact (mem_inf.mp h1).2
  · intro h
    have h1 : (⟨x, hK.1 hx⟩ : ↥C) ∈ (pPrimeCore 2 ↥(K.subgroupOf C)).map (K.subgroupOf C).subtype
        := by
      rw [key]
      exact mem_inf.mpr ⟨hx, h⟩
    obtain ⟨y, hy, hyx⟩ := h1
    rw [← hiso]
    refine ⟨y, hy, ?_⟩
    apply Subtype.ext
    have h5 := congrArg Subtype.val hyx
    exact h5

theorem commutator_eq_of_le_hatIn {w : G} {K Y₃ : Subgroup G}
    (hK : IsTwoComponentIn K (centralizer {w})) (hY₃N : Y₃ ≤ normalizer (K : Set G))
    (h : hatIn w K ≤ ⁅hatIn w K, hatIn w Y₃⁆) :
    ⁅K, Y₃⁆ = K := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set C := centralizer ({w} : Set G) with hC
  set π := QuotientGroup.mk' (pPrimeCore 2 ↥C) with hπ
  set N₃ := ⁅K, Y₃⁆ with hN₃
  have hle : N₃ ≤ K := commutator_le_of_le_normalizer hY₃N
  have hNC : N₃ ≤ C := hle.trans hK.1
  have himg : ⁅hatIn w K, hatIn w Y₃⁆ ≤ hatIn w N₃ := by
    rw [Subgroup.commutator_le]
    rintro _ ⟨k, hk, rfl⟩ _ ⟨y, hy, rfl⟩
    refine ⟨⁅k, y⁆, ?_, by simp [commutatorElement_def]⟩
    have h1 := commutator_mem_commutator (show (k : G) ∈ K from hk) (show (y : G) ∈ Y₃ from hy)
    rw [commutatorElement_def] at h1
    show ((k : G) * y * (k : G)⁻¹ * (y : G)⁻¹) ∈ N₃
    exact h1
  have hdec : ∀ k (hk : k ∈ K), ∃ n ∈ N₃, ∃ ho : n⁻¹ * k ∈ K,
      (⟨n⁻¹ * k, ho⟩ : ↥K) ∈ pPrimeCore 2 ↥K := by
    intro k hk
    obtain ⟨n, hn, hnk⟩ := himg (h ⟨⟨k, hK.1 hk⟩, hk, rfl⟩)
    have hn' : (n : G) ∈ N₃ := hn
    have ho : (n : G)⁻¹ * k ∈ K := mul_mem (inv_mem (hle hn')) hk
    refine ⟨n, hn', ho, (mem_pPrimeCore_iff hK ho).mpr ?_⟩
    have h1 : n⁻¹ * ⟨k, hK.1 hk⟩ ∈ pPrimeCore 2 ↥C := QuotientGroup.eq.mp hnk
    exact h1
  have hNn : (N₃.subgroupOf K).Normal := commutator_normal_subgroupOf
  set Qt := ↥K ⧸ N₃.subgroupOf K with hQt
  have : Group.IsPerfect ↥K := hK.2.2.1
  have hQp : Group.IsPerfect Qt := Group.IsPerfect.ofSurjective (QuotientGroup.mk'_surjective _)
  have hsolO : Group.IsSolvable ↥(pPrimeCore 2 ↥K) :=
    CFSG.FeitThompson.isSolvable_of_odd_natCard _ (odd_card_pPrimeCore_two ↥K)
  have hsurj : Function.Surjective
      ((QuotientGroup.mk' (N₃.subgroupOf K)).comp (pPrimeCore 2 ↥K).subtype) := by
    intro q
    obtain ⟨⟨k, hk⟩, rfl⟩ := QuotientGroup.mk'_surjective (N₃.subgroupOf K) q
    obtain ⟨n, hn, ho, hO⟩ := hdec k hk
    refine ⟨⟨⟨n⁻¹ * k, ho⟩, hO⟩, ?_⟩
    simp only [MonoidHom.coe_comp, Function.comp_apply, coe_subtype]
    rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq]
    have h1 : (⟨n⁻¹ * k, ho⟩ : ↥K)⁻¹ * ⟨k, hk⟩ = ⟨k, hk⟩⁻¹ * ⟨n, hle hn⟩ * ⟨k, hk⟩⁻¹⁻¹ := by
      apply Subtype.ext
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, inv_inv]
      group
    rw [h1]
    exact hNn.conj_mem ⟨n, hle hn⟩ (show (⟨n, hle hn⟩ : ↥K) ∈ N₃.subgroupOf K from hn) _
  have hQs : Group.IsSolvable Qt := Group.isSolvable_of_surjective hsurj
  have hsub : Subsingleton Qt := by
    by_contra hns
    have : Nontrivial Qt := not_subsingleton_iff_nontrivial.1 hns
    have h1 := Group.IsSolvable.commutator_lt_top_of_nontrivial Qt
    rw [Group.IsPerfect.commutator_eq_top] at h1
    exact lt_irrefl _ h1
  apply le_antisymm hle
  intro k hk
  have h1 : (QuotientGroup.mk (⟨k, hk⟩ : ↥K) : Qt) = 1 := Subsingleton.elim _ _
  rw [QuotientGroup.eq_one_iff, mem_subgroupOf] at h1
  exact h1

theorem lemma226_perfect {z₁ z₂ : G} (hz₂ : orderOf z₂ = 2) (hc : z₁ * z₂ = z₂ * z₁)
    {L₁ L₂ : Subgroup G} (hL₁ : IsSolvableTwoComponentIn L₁ (centralizer {z₁} ⊓ centralizer {z₂}))
    (hL₂ : IsTwoComponentIn L₂ (centralizer {z₁} ⊓ centralizer {z₂})) (hz₂L : z₂ ∈ L₂)
    (hns : ¬ (((pPrimeCore 2 ↥(centralizer ({z₁} : Set G))).map (centralizer {z₁}).subtype ⊔
        GH74.GLS.oPrimeResidualOf 3 L₁).subgroupOf (centralizer {z₁})).IsSubnormal) :
    ∃ K : Subgroup G, IsTwoComponentIn K (centralizer {z₁}) ∧
      GH74.GLS.oPrimeResidualOf 2 L₂ ≤ K ∧
      centralizer {z₁} ⊓ centralizer {z₂} ≤ normalizer (K : Set G) ∧
      ⁅K, GH74.GLS.oPrimeResidualOf 3 L₁⁆ = K ∧
      ∃ hz₂K : z₂ ∈ K, (QuotientGroup.mk ⟨z₂, hz₂K⟩ : ↥K ⧸ pPrimeCore 2 ↥K) ∉
        center (↥K ⧸ pPrimeCore 2 ↥K) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set C := centralizer ({z₁} : Set G) with hC
  set π := QuotientGroup.mk' (pPrimeCore 2 ↥C) with hπ
  have hz₂C : z₂ ∈ C := mem_centralizer_singleton_iff.mpr hc.symm
  obtain ⟨K₀, hK₀, -, -, hL₂K₀⟩ := T23.exists_pumpup_of_mem hz₂ hz₂C hL₂ hz₂L
  set K := K₀.map C.subtype with hKdef
  have hK : IsTwoComponentIn K C := T23.isTwoComponentIn_map_subtype hK₀
  have hL₂K : L₂ ≤ K := by
    intro x hx
    have hxC : x ∈ C := (hL₂.1 hx).1
    have h1 : (⟨x, hxC⟩ : ↥C) ∈ L₂.subgroupOf C := hx
    exact ⟨⟨x, hxC⟩, (hL₂K₀.1 h1).1, rfl⟩
  have hz₂K : z₂ ∈ K := hL₂K hz₂L
  have hL₁C : L₁ ≤ C := hL₁.1.trans inf_le_left
  set t : MBar z₁ := QuotientGroup.mk (⟨z₂, hz₂C⟩ : ↥C) with ht
  obtain ⟨hKc, hKq⟩ := isComponentOf_hatIn hK
  have htK : t ∈ hatIn z₁ K := mk_mem_hatIn hz₂K hz₂C
  have hM := isSolvableTwoComponentIn_hatIn hz₂ hz₂C hL₁
  set M := hatIn z₁ L₁ with hMdef
  have hMsol : Group.IsSolvable ↥M := F3L221.isSolvable_of_isSolvableTwoComponentIn hM
  set L₃ := GH74.GLS.oPrimeResidualOf 3 L₁ with hL₃
  have hL₃L₁ : L₃ ≤ L₁ := map_subtype_le _
  have hL₃C : L₃ ≤ C := hL₃L₁.trans hL₁C
  set X := hatIn z₁ L₃ with hXdef
  have hXM : X ≤ M := hatIn_mono hL₃L₁
  have hXn : (X.subgroupOf M).Normal := by
    refine ⟨fun n hn g => ?_⟩
    rw [mem_subgroupOf] at hn ⊢
    obtain ⟨x, hx, hxn⟩ := hn
    obtain ⟨m, hm, hmg⟩ := g.2
    refine ⟨m * x * m⁻¹, ?_, ?_⟩
    · exact conj_mem_oPrimeResidualOf 3 hm hx
    · simp only [Subgroup.coe_mul, Subgroup.coe_inv, ← hxn, ← hmg, map_mul, map_inv]
  have hXs : (X.subgroupOf (centralizer {t})).IsSubnormal :=
    CFSG.GroupTheory.isSubnormal_subgroupOf_trans hXM hM.1 hXn.isSubnormal hM.2.1
  have hXsol : Group.IsSolvable ↥X :=
    Group.isSolvable_of_isSolvable_injective (f := inclusion hXM) (inclusion_injective hXM)
  have hXC : X ≤ centralizer {t} := hXM.trans hM.1
  have hXns : ¬ X.IsSubnormal := by
    intro hsn
    apply hns
    have h1 := hsn.comap π
    have h3 : X.comap π = L₃.subgroupOf C ⊔ pPrimeCore 2 ↥C := by
      rw [hXdef, hatIn, comap_map_eq, QuotientGroup.ker_mk']
    rw [h3] at h1
    have h2 : ((pPrimeCore 2 ↥C).map C.subtype ⊔ L₃).subgroupOf C =
        L₃.subgroupOf C ⊔ pPrimeCore 2 ↥C := by
      rw [Subgroup.subgroupOf_sup (map_subtype_le _) hL₃C, sup_comm]
      congr 1
      exact comap_map_eq_self_of_injective C.subtype_injective _
    rw [h2]
    exact h1
  have hNt := compCentralizer_le_centralizer hKc htK
  have hXK : ¬ ∀ x ∈ X, ∀ d ∈ hatIn z₁ K, d * x = x * d := fun hcen =>
    hXns (isSubnormal_of_le_compCentralizer (le_compCentralizer hKc htK hXC hXs hXsol hcen)
      hNt hXs)
  have hnc : ¬ ∀ y ∈ hatIn z₁ K, y * t = t * y := by
    intro hcen
    apply hXK
    have hKC : hatIn z₁ K ≤ centralizer {t} := fun y hy =>
      mem_centralizer_singleton_iff.mpr (hcen y hy)
    intro x hx d hd
    exact (F3L221.commute_of_isQuasisimple hKC (isSubnormal_of_isComponentOf hKc).subgroupOf hKq
      hXC hXs hXsol x hx d hd).symm
  have hnorm : centralizer {z₁} ⊓ centralizer {z₂} ≤ normalizer (K : Set G) := by
    intro c hc'
    obtain ⟨hc₁, hc₂⟩ := mem_inf.mp hc'
    rw [F3L221.mem_normalizer_iff_map_conj_eq]
    by_contra hne
    have hmapC : C.map (MulAut.conj c).toMonoidHom = C := by
      ext y
      rw [mem_map_equiv, MulAut.conj_symm_apply]
      constructor
      · intro hy
        have h1 := mul_mem (mul_mem hc₁ hy) (inv_mem hc₁)
        rwa [show c * (c⁻¹ * y * c) * c⁻¹ = y by group] at h1
      · intro hy
        exact mul_mem (mul_mem (inv_mem hc₁) hy) hc₁
    have hK' : IsTwoComponentIn (K.map (MulAut.conj c).toMonoidHom) C := by
      have h1 := L35.isTwoComponentIn_map_of_injective (MulAut.conj c).toMonoidHom
        (MulAut.conj c).injective hK
      rwa [hmapC] at h1
    have hz₂K' : z₂ ∈ K.map (MulAut.conj c).toMonoidHom := by
      refine ⟨z₂, hz₂K, ?_⟩
      have h1 : c * z₂ = z₂ * c := mem_centralizer_singleton_iff.mp hc₂
      show c * z₂ * c⁻¹ = z₂
      rw [h1, mul_inv_cancel_right]
    apply hnc
    intro y hy
    exact hatIn_commute hK hK' (Ne.symm hne) hy (mk_mem_hatIn hz₂K' hz₂C)
  have hL₃N : L₃ ≤ normalizer (K : Set G) := (hL₃L₁.trans hL₁.1).trans hnorm
  have hXN : X ≤ normalizer ((hatIn z₁ K : Subgroup (MBar z₁)) : Set (MBar z₁)) :=
    hatIn_le_normalizer hL₃N
  have hcomm : ⁅K, L₃⁆ = K := by
    rcases commute_or_le_commutator hKc hXN with h | h
    · exact absurd h hXK
    · exact commutator_eq_of_le_hatIn hK hL₃N h
  refine ⟨K, hK, (map_subtype_le _).trans hL₂K, hnorm, hcomm, hz₂K, fun hcen => hnc ?_⟩
  rintro _ ⟨⟨k, hkC⟩, hk, rfl⟩
  replace hk : k ∈ K := hk
  have h1 := mem_center_iff.mp hcen (QuotientGroup.mk ⟨k, hk⟩)
  rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq] at h1
  have h2 := (mem_pPrimeCore_iff hK (mul_mem (inv_mem (mul_mem hk hz₂K)) (mul_mem hz₂K hk))).mp
    (by convert h1 using 1)
  have h3 : (QuotientGroup.mk (⟨k, hkC⟩ * ⟨z₂, hz₂C⟩) : MBar z₁) =
      QuotientGroup.mk (⟨z₂, hz₂C⟩ * ⟨k, hkC⟩) := by
    rw [QuotientGroup.eq]
    convert h2 using 1
  rw [QuotientGroup.mk_mul, QuotientGroup.mk_mul] at h3
  exact h3

end F3L226

theorem harris82Lemma226ThreePerfect_holds : Harris82Lemma226ThreePerfect := by
  intro G _ _ z₁ z₂ _ hz₂ _ hc L₁ L₂ hL₁ hL₂ hz₂L hns
  exact F3L226.lemma226_perfect hz₂ hc hL₁ hL₂ hz₂L hns

theorem harris82Lemma226Three_of_solvable (hS : Harris82Lemma226ThreeSolvable) :
    Harris82Lemma226Three :=
  harris82Lemma226Three_of_split harris82Lemma226ThreePerfect_holds hS

end CFSG.ComponentClassification.HarrisLit.T1
