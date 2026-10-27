module

public import CFSG.LocalAnalysis.ABGTheoremB.CorollaryV61
public import CFSG.LocalAnalysis.ABGTheoremB.SettingAPI
import CFSG.LocalAnalysis.ABGTheoremB.IV1
import CFSG.GroupTheory.ABGLocalTools.OddInvolution
import CFSG.GroupTheory.ABGLocalTools.CoreLemmas
import CFSG.CharacterTheory.Semidihedral.OddCentralSL2Kernel
import CFSG.LinearAlgebra.LinearGroups.Perfect
import CFSG.LocalAnalysis.ComponentInitial.QuaternionMatrices
import CFSG.LocalAnalysis.SignalizerFunctor.PrimeValueHull
import CFSG.FeitThompson.OddOrderTheorem
public import CFSG.LocalAnalysis.ABGTheoremB.Facts

public section

namespace CFSG.ABGTheoremB

open CFSG.QuasiDihedralFusion CFSG.ABGLocalTools
open scoped Pointwise commutatorElement

universe u

section General

variable {G : Type u} [Group G]

private theorem eq_one_of_mem_of_pow_two_pow {O : Subgroup G} (hO : Odd (Nat.card O)) {g : G}
    (hg : g ∈ O) {k : ℕ} (hk : g ^ (2 ^ k) = 1) : g = 1 := by
  have hodd : Odd (orderOf g) := hO.of_dvd_nat (Subgroup.orderOf_dvd_natCard O hg)
  have h2 : orderOf g ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one hk
  exact orderOf_eq_one_iff.mp (((Nat.coprime_two_right.mpr hodd).pow_right k).eq_one_of_dvd h2)

private theorem mem_of_mem_sup_of_isPGroup {O Z P : Subgroup G} (hO : Odd (Nat.card O))
    (hP : IsPGroup 2 P) (hZP : Z ≤ P) (hZO : Z ≤ Subgroup.normalizer (O : Set G)) {s : G}
    (hs : s ∈ P) (hsOZ : s ∈ O ⊔ Z) : s ∈ Z := by
  have hs' : s ∈ ((O ⊔ Z : Subgroup G) : Set G) := hsOZ
  rw [Subgroup.coe_mul_of_right_le_normalizer_left _ _ hZO] at hs'
  obtain ⟨a, ha, z, hz, hza⟩ := hs'
  have hza : a * z = s := hza
  have haP : a ∈ P := by
    have : a = s * z⁻¹ := by rw [← hza]; group
    rw [this]
    exact P.mul_mem hs (P.inv_mem (hZP hz))
  obtain ⟨k, hk⟩ := hP ⟨a, haP⟩
  have hk' : a ^ (2 ^ k) = 1 := by simpa using congrArg Subtype.val hk
  rw [← hza, eq_one_of_mem_of_pow_two_pow hO ha hk', one_mul]
  exact hz

private theorem exists_mem_inf_mul_of_le_sup {L O K : Subgroup G} (hOL : O ≤ L)
    (hKO : K ≤ Subgroup.normalizer (O : Set G)) (h : L ≤ K ⊔ O) {l : G} (hl : l ∈ L) :
    ∃ k ∈ K ⊓ L, ∃ a ∈ O, l = k * a := by
  have hl' : l ∈ ((K ⊔ O : Subgroup G) : Set G) := h hl
  rw [Subgroup.coe_mul_of_left_le_normalizer_right K O hKO] at hl'
  obtain ⟨k, hk, a, ha, rfl⟩ := hl'
  refine ⟨k, ⟨hk, ?_⟩, a, ha, rfl⟩
  have : k = k * a * a⁻¹ := by group
  rw [this]
  exact L.mul_mem hl (L.inv_mem (hOL ha))

private theorem map_inf_eq_range {L O K : Subgroup G} (hOL : O ≤ L)
    (hKO : K ≤ Subgroup.normalizer (O : Set G)) (h : L ≤ K ⊔ O) {Γ : Type*} [Group Γ]
    (ψ : L →* Γ) (hker : O.subgroupOf L ≤ ψ.ker) :
    ((K ⊓ L).subgroupOf L).map ψ = ψ.range := by
  refine le_antisymm (Subgroup.map_le_range _ _) ?_
  rintro _ ⟨l, rfl⟩
  obtain ⟨k, hk, a, ha, hla⟩ := exists_mem_inf_mul_of_le_sup hOL hKO h l.2
  refine ⟨⟨k, hk.2⟩, hk, ?_⟩
  have hl : l = ⟨k, hk.2⟩ * ⟨a, hOL ha⟩ := Subtype.ext hla
  have ha' : ψ ⟨a, hOL ha⟩ = 1 := hker ha
  rw [hl, map_mul, ha', mul_one]

private theorem le_sup_of_map_eq_top {L O X : Subgroup G} {Γ : Type*} [Group Γ] (ψ : L →* Γ)
    (hker : ψ.ker = O.subgroupOf L) (h : (X.subgroupOf L).map ψ = ⊤) : L ≤ X ⊔ O := by
  intro l hl
  obtain ⟨x, hx, hxl⟩ : ψ ⟨l, hl⟩ ∈ (X.subgroupOf L).map ψ := h ▸ Subgroup.mem_top _
  have hk : x⁻¹ * ⟨l, hl⟩ ∈ ψ.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, hxl, inv_mul_cancel]
  rw [hker, Subgroup.mem_subgroupOf] at hk
  have : l = (x : G) * ((x⁻¹ * ⟨l, hl⟩ : L) : G) := by simp
  rw [this]
  exact Subgroup.mul_mem_sup hx hk

private theorem le_of_forall_isSylowOf_le [Finite G] {H K : Subgroup G}
    (h : ∀ p : ℕ, p.Prime → ∃ P : Subgroup G, IsSylowOf p P K ∧ P ≤ H) : K ≤ H := by
  have hidx : (H ⊓ K).relIndex K = 1 := by
    rw [Nat.eq_one_iff_not_exists_prime_dvd]
    intro p hp hdvd
    have : Fact p.Prime := ⟨hp⟩
    obtain ⟨P, hP, hPH⟩ := h p hp
    have hPHK : P ≤ H ⊓ K := le_inf hPH hP.le
    have hsyl := (isSylowOf_iff.mp hP).2.2
    apply hsyl
    rw [← Subgroup.relIndex_mul_relIndex P (H ⊓ K) K hPHK inf_le_right]
    exact Dvd.dvd.mul_left hdvd _
  exact (Subgroup.relIndex_eq_one.mp hidx).trans inf_le_left

private theorem ringChar_ne_two_of_odd_card {F : Type*} [Field F] [Finite F]
    (h : Odd (Nat.card F)) : ringChar F ≠ 2 := by
  have : Fintype F := Fintype.ofFinite F
  intro hchar
  have h2 := (FiniteField.even_card_iff_char_two (F := F)).mp hchar
  rw [← Nat.card_eq_fintype_card] at h2
  obtain ⟨k, hk⟩ := h
  omega

private theorem conj_mul_comm_of_commute {a c y : G} (hc : a * c = c * a) (hy : y * a = a * y) :
    c * y * c⁻¹ * a = a * (c * y * c⁻¹) := by
  have hc' : c⁻¹ * a * c = a := by rw [mul_assoc, hc]; group
  calc c * y * c⁻¹ * a = c * y * (c⁻¹ * a * c) * c⁻¹ := by group
    _ = c * (y * a) * c⁻¹ := by rw [hc']; group
    _ = c * (a * y) * c⁻¹ := by rw [hy]
    _ = (c * a) * y * c⁻¹ := by group
    _ = (a * c) * y * c⁻¹ := by rw [hc]
    _ = a * (c * y * c⁻¹) := by group

private theorem conj_inv_of_commute {a c y : G} (hc : a * c = c * a) (hy : a * y * a⁻¹ = y⁻¹) :
    a * (c * y * c⁻¹) * a⁻¹ = (c * y * c⁻¹)⁻¹ := by
  calc a * (c * y * c⁻¹) * a⁻¹ = (a * c) * y * (a * c)⁻¹ := by group
    _ = (c * a) * y * (c * a)⁻¹ := by rw [hc]
    _ = c * (a * y * a⁻¹) * c⁻¹ := by group
    _ = (c * y * c⁻¹)⁻¹ := by rw [hy]; group

private theorem commutator_mem_centralizer_of_inverts {R : Subgroup G} {a k : G}
    (ha : ∀ y ∈ R, a * y * a⁻¹ = y⁻¹) (hk : k ∈ Subgroup.normalizer (R : Set G)) :
    k * a * k⁻¹ * a⁻¹ ∈ Subgroup.centralizer (R : Set G) := by
  rw [Subgroup.mem_centralizer_iff]
  intro r hr
  have hs : k⁻¹ * r * k ∈ R := by
    have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hk) r).mp hr
    simpa using this
  have h1 : a⁻¹ * r = r⁻¹ * a⁻¹ := by
    have e := ha r⁻¹ (R.inv_mem hr)
    rw [inv_inv] at e
    calc a⁻¹ * r = a⁻¹ * (a * r⁻¹ * a⁻¹) := by rw [e]
      _ = r⁻¹ * a⁻¹ := by group
  have h2 : a * (k⁻¹ * r * k)⁻¹ = (k⁻¹ * r * k) * a := by
    have e := ha (k⁻¹ * r * k)⁻¹ (R.inv_mem hs)
    rw [inv_inv] at e
    calc a * (k⁻¹ * r * k)⁻¹ = a * (k⁻¹ * r * k)⁻¹ * a⁻¹ * a := by group
      _ = (k⁻¹ * r * k) * a := by rw [e]
  symm
  calc k * a * k⁻¹ * a⁻¹ * r = k * a * k⁻¹ * (a⁻¹ * r) := by group
    _ = k * a * k⁻¹ * (r⁻¹ * a⁻¹) := by rw [h1]
    _ = k * (a * (k⁻¹ * r * k)⁻¹) * k⁻¹ * a⁻¹ := by group
    _ = k * ((k⁻¹ * r * k) * a) * k⁻¹ * a⁻¹ := by rw [h2]
    _ = r * (k * a * k⁻¹ * a⁻¹) := by group

private theorem mem_normalizer_of_map_conj_le [Finite G] {H : Subgroup G} {g : G}
    (h : H.map (MulAut.conj g).toMonoidHom ≤ H) : g ∈ Subgroup.normalizer (H : Set G) := by
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  apply Subgroup.eq_of_le_of_card_ge h
  rw [Subgroup.card_map_of_injective (MulAut.conj g).injective]

private theorem normalizer_le_normalizer_commutator (R : Subgroup G) :
    Subgroup.normalizer (R : Set G) ≤ Subgroup.normalizer ((⁅R, R⁆ : Subgroup G) : Set G) := by
  intro n hn
  rw [Subgroup.mem_normalizer_iff_map_conj_eq] at hn ⊢
  rw [Subgroup.map_commutator, hn]

private theorem normalizer_le_normalizer_centralizer (O : Subgroup G) :
    Subgroup.normalizer (O : Set G) ≤
      Subgroup.normalizer ((Subgroup.centralizer (O : Set G) : Subgroup G) : Set G) :=
  Subgroup.le_normalizer_of_normal_subgroupOf (Subgroup.centralizer_le_normalizer (O : Set G))

private theorem sl2_isPerfect {F : Type*} [Field F] [Finite F] (hF : 4 ≤ Nat.card F) :
    Group.IsPerfect (Matrix.SpecialLinearGroup (Fin 2) F) := by
  have : Fintype F := Fintype.ofFinite F
  apply CFSG.LinearGroups.special_linear_dimension_two_perfect
  obtain ⟨t, -, ht⟩ := Finset.exists_subset_card_eq (s := (Finset.univ : Finset F)) (n := 4)
    (by rw [Finset.card_univ, ← Nat.card_eq_fintype_card]; exact hF)
  exact ⟨t, ht⟩

private theorem exists_pow_mem_of_mem_sup {p : ℕ} {A P : Subgroup G} (hP : IsPGroup p P)
    (hPA : P ≤ Subgroup.normalizer (A : Set G)) {b : G} (hb : b ∈ A ⊔ P) :
    ∃ k : ℕ, b ^ (p ^ k) ∈ A := by
  have hb' : b ∈ ((A ⊔ P : Subgroup G) : Set G) := hb
  rw [Subgroup.coe_mul_of_right_le_normalizer_left A P hPA] at hb'
  obtain ⟨a, ha, t, ht, rfl⟩ := hb'
  have key : ∀ m : ℕ, ∃ a' ∈ A, (a * t) ^ m = a' * t ^ m := by
    intro m
    induction m with
    | zero => exact ⟨1, A.one_mem, by simp⟩
    | succ m ih =>
      obtain ⟨a', ha', hm⟩ := ih
      refine ⟨a' * (t ^ m * a * (t ^ m)⁻¹), A.mul_mem ha' ?_, ?_⟩
      · exact (Subgroup.mem_normalizer_iff.mp (hPA (P.pow_mem ht m)) a).mp ha
      · rw [pow_succ, hm, pow_succ]
        group
  obtain ⟨k, hk⟩ := hP ⟨t, ht⟩
  have hk' : t ^ (p ^ k) = 1 := by
    have := congrArg Subtype.val hk
    simpa using this
  obtain ⟨a', ha', h⟩ := key (p ^ k)
  refine ⟨k, ?_⟩
  rw [h, hk', mul_one]
  exact ha'

private theorem eq_top_of_isPerfect_of_pow_mem {Γ : Type*} [Group Γ] [Finite Γ]
    [Group.IsPerfect Γ] {p : ℕ} [Fact p.Prime] (M : Subgroup Γ) [M.Normal]
    (h : ∀ g : Γ, ∃ k : ℕ, g ^ (p ^ k) ∈ M) : M = ⊤ := by
  have hpg : IsPGroup p (Γ ⧸ M) := by
    intro g
    obtain ⟨γ, rfl⟩ := QuotientGroup.mk'_surjective M g
    obtain ⟨k, hk⟩ := h γ
    refine ⟨k, ?_⟩
    rw [← map_pow, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    exact hk
  have hsub : Subsingleton (Γ ⧸ M) := by
    by_contra hnt
    rw [not_subsingleton_iff_nontrivial] at hnt
    exact Group.IsPerfect.not_isNilpotent (Γ ⧸ M) hpg.isNilpotent
  rw [eq_top_iff]
  intro g _
  have h1 : (QuotientGroup.mk' M) g = 1 := Subsingleton.elim _ _
  rwa [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1

private theorem le_of_le_sup_of_isPGroup [Finite G] {p : ℕ} [Fact p.Prime] {L A P : Subgroup G}
    {Γ : Type*} [Group Γ] [Finite Γ] [Group.IsPerfect Γ] (ψ : L →* Γ)
    (hψ : Function.Surjective ψ) (hker : ψ.ker ≤ A.subgroupOf L) (hLAP : L ≤ A ⊔ P)
    (hP : IsPGroup p P) (hPA : P ≤ Subgroup.normalizer (A : Set G)) : L ≤ A := by
  have hLA : L ≤ Subgroup.normalizer (A : Set G) :=
    hLAP.trans (sup_le Subgroup.le_normalizer hPA)
  have hA' : (A.subgroupOf L).Normal := Subgroup.normal_subgroupOf_of_le_normalizer hLA
  let M : Subgroup Γ := (A.subgroupOf L).map ψ
  have hM : M.Normal := hA'.map ψ hψ
  have hMtop : M = ⊤ := by
    refine eq_top_of_isPerfect_of_pow_mem (p := p) M fun g => ?_
    obtain ⟨l, rfl⟩ := hψ g
    obtain ⟨k, hk⟩ := exists_pow_mem_of_mem_sup hP hPA (hLAP l.2)
    exact ⟨k, ⟨l ^ (p ^ k), by simpa [Subgroup.mem_subgroupOf] using hk, map_pow ψ l _⟩⟩
  intro l hl
  have hmem : ψ ⟨l, hl⟩ ∈ M := hMtop ▸ Subgroup.mem_top _
  obtain ⟨a, ha, hal⟩ := hmem
  have hker' : a⁻¹ * ⟨l, hl⟩ ∈ ψ.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, hal, inv_mul_cancel]
  have h2 := hker hker'
  have ha'' : (a : G) ∈ A := ha
  rw [Subgroup.mem_subgroupOf] at h2
  have : l = (a : G) * ((a⁻¹ * ⟨l, hl⟩ : L) : G) := by simp
  rw [this]
  exact A.mul_mem ha'' h2

private theorem exists_le_mulEquiv_of_le_map [Finite G] {L X O : Subgroup G} {Γ : Type*}
    [Group Γ] (ψ : L →* Γ) (hker : ψ.ker = O.subgroupOf L) (hO : Odd (Nat.card O))
    {Q₀ : Subgroup Γ} (hQ₀ : IsPGroup 2 Q₀)
    (hQ₀X : Q₀ ≤ (X.subgroupOf L).map ψ) :
    ∃ Q : Subgroup G, Q ≤ X ∧ IsPGroup 2 Q ∧ Nonempty (Q ≃* Q₀) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let W : Subgroup L := X.subgroupOf L ⊓ Q₀.comap ψ
  let φ : W →* Q₀ := (ψ.comp W.subtype).codRestrict Q₀ (fun w => w.2.2)
  have hφ : Function.Surjective φ := by
    rintro ⟨q, hq⟩
    obtain ⟨l, hl, hlq⟩ := hQ₀X hq
    refine ⟨⟨l, hl, show ψ l ∈ Q₀ from hlq ▸ hq⟩, Subtype.ext ?_⟩
    exact hlq
  obtain ⟨P⟩ : Nonempty (Sylow 2 W) := inferInstance
  let P' := P.mapSurjective hφ
  have hP'top : (P' : Subgroup Q₀) = ⊤ := (P'.is_maximal' (hQ₀.to_subgroup ⊤) le_top).symm
  let φP : (P : Subgroup W) →* Q₀ := φ.comp (P : Subgroup W).subtype
  have hinj : Function.Injective φP := by
    rw [injective_iff_map_eq_one]
    rintro ⟨w, hw⟩ h1
    have hk : (w : L) ∈ ψ.ker := by
      have := congrArg Subtype.val h1
      exact this
    rw [hker, Subgroup.mem_subgroupOf] at hk
    obtain ⟨k, hk2⟩ := P.isPGroup' ⟨w, hw⟩
    have hk2' : (((w : L) : G)) ^ (2 ^ k) = 1 := by
      have := congrArg (fun z : (P : Subgroup W) => (((z : W) : L) : G)) hk2
      simpa using this
    have := eq_one_of_mem_of_pow_two_pow hO hk hk2'
    apply Subtype.ext
    apply Subtype.ext
    apply Subtype.ext
    exact this
  have hsurj : Function.Surjective φP := by
    intro q
    have hq : q ∈ (P' : Subgroup Q₀) := hP'top ▸ Subgroup.mem_top q
    rw [Sylow.coe_mapSurjective] at hq
    obtain ⟨w, hw, rfl⟩ := hq
    exact ⟨⟨w, hw⟩, rfl⟩
  let ι : (P : Subgroup W) →* G := L.subtype.comp (W.subtype.comp (P : Subgroup W).subtype)
  have hι : Function.Injective ι :=
    L.subtype_injective.comp (W.subtype_injective.comp (P : Subgroup W).subtype_injective)
  refine ⟨ι.range, ?_, ?_, ⟨(MonoidHom.ofInjective hι).symm.trans
    (MulEquiv.ofBijective φP ⟨hinj, hsurj⟩)⟩⟩
  · rintro _ ⟨w, rfl⟩
    exact (w : W).2.1
  · exact P.isPGroup'.of_equiv (MonoidHom.ofInjective hι)

private theorem exists_conj_le_sylow_inf [Finite G] {X Q : Subgroup G} (S : Sylow 2 G)
    (hSX : (S : Subgroup G) ≤ Subgroup.normalizer (X : Set G)) (hQX : Q ≤ X)
    (hQ : IsPGroup 2 Q) :
    ∃ g ∈ X, Q.map (MulAut.conj g).toMonoidHom ≤ (S : Subgroup G) ⊓ X := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hSK : IsSylowOf 2 (S : Subgroup G) (X ⊔ (S : Subgroup G)) := by
    rw [isSylowOf_iff]
    refine ⟨le_sup_right, S.isPGroup', fun hdvd => S.not_dvd_index ?_⟩
    rw [← Subgroup.relIndex_mul_index (le_sup_right : (S : Subgroup G) ≤ X ⊔ S)]
    exact hdvd.mul_right _
  have hSX' : IsSylowOf 2 ((S : Subgroup G) ⊓ X) X :=
    hSK.inf_of_le_normalizer le_sup_left (sup_le Subgroup.le_normalizer hSX)
  obtain ⟨P, hP⟩ := (hQ.comap_subtype (K := X)).exists_le_sylow
  have hP' : IsSylowOf 2 ((P : Subgroup X).map X.subtype) X := ⟨P, rfl⟩
  obtain ⟨k, hk, hkP⟩ := hSX'.exists_mem_conj hP'
  refine ⟨k⁻¹, X.inv_mem hk, ?_⟩
  rintro _ ⟨q, hq, rfl⟩
  have hqP : q ∈ (P : Subgroup X).map X.subtype := ⟨⟨q, hQX hq⟩, hP hq, rfl⟩
  have := (hkP q).mp hqP
  simpa [MulAut.conj_apply] using this

private theorem layer_of_le_centralizer_sup [Finite G] {L O K : Subgroup G} {F : Type} [Field F]
    [Finite F] (ψ : L →* Matrix.SpecialLinearGroup (Fin 2) F) (hψ : Function.Surjective ψ)
    (hker : ψ.ker = O.subgroupOf L) (hOL : O ≤ L) (hO : Odd (Nat.card O))
    (hKO : K ≤ Subgroup.centralizer (O : Set G)) (hcov : L ≤ K ⊔ O) {p f : ℕ} (hp : p.Prime)
    (hpodd : Odd p) (hf : 1 ≤ f) (hF : Nat.card F = p ^ f) (hq : 5 ≤ p ^ f) :
    L = ⁅K ⊓ L, K ⊓ L⁆ ⊔ O ∧
      ((⁅K ⊓ L, K ⊓ L⁆ ⊓ O = ⊥ ∧
          Nonempty ((⁅K ⊓ L, K ⊓ L⁆ : Subgroup G) ≃* Matrix.SpecialLinearGroup (Fin 2) F)) ∨
        (p ^ f = 9 ∧ Nat.card (⁅K ⊓ L, K ⊓ L⁆ ⊓ O : Subgroup G) = 3)) := by
  set R : Subgroup G := K ⊓ L with hR
  set J : Subgroup G := ⁅R, R⁆ with hJ
  have hKN : K ≤ Subgroup.normalizer (O : Set G) :=
    hKO.trans (Subgroup.centralizer_le_normalizer _)
  have hRL : R ≤ L := inf_le_right
  have hJR : J ≤ R := Subgroup.commutator_le.mpr fun g₁ h₁ g₂ h₂ => by
    rw [commutatorElement_def]
    exact R.mul_mem (R.mul_mem (R.mul_mem h₁ h₂) (R.inv_mem h₁)) (R.inv_mem h₂)
  have hJL : J ≤ L := hJR.trans hRL
  have hJO : J ≤ Subgroup.centralizer (O : Set G) := hJR.trans (inf_le_left.trans hKO)
  have hperfF : Group.IsPerfect (Matrix.SpecialLinearGroup (Fin 2) F) :=
    sl2_isPerfect (by rw [hF]; omega)
  have hRtop : (R.subgroupOf L).map ψ = ⊤ := by
    rw [map_inf_eq_range hOL hKN hcov ψ hker.ge, MonoidHom.range_eq_top.mpr hψ]
  have hJsub : J.subgroupOf L = ⁅R.subgroupOf L, R.subgroupOf L⁆ := by
    have h1 : J = (⁅R.subgroupOf L, R.subgroupOf L⁆).map L.subtype := by
      rw [Subgroup.map_commutator, Subgroup.map_subgroupOf_eq_of_le hRL]
    rw [h1, Subgroup.subgroupOf, Subgroup.comap_map_eq_self_of_injective L.subtype_injective]
  have hJtop : (J.subgroupOf L).map ψ = ⊤ := by
    rw [hJsub, Subgroup.map_commutator, hRtop]
    exact Group.IsPerfect.commutator_eq_top
  have hLJO : L = J ⊔ O := le_antisymm (le_sup_of_map_eq_top ψ hker hJtop) (sup_le hJL hOL)
  have hdecomp : ∀ r ∈ R, ∃ j ∈ J, ∃ z ∈ O, r = j * z := by
    intro r hr
    obtain ⟨j, hj, hjr⟩ : ψ ⟨r, hRL hr⟩ ∈ (J.subgroupOf L).map ψ := hJtop ▸ Subgroup.mem_top _
    have hk : j⁻¹ * ⟨r, hRL hr⟩ ∈ ψ.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hjr, inv_mul_cancel]
    rw [hker, Subgroup.mem_subgroupOf] at hk
    exact ⟨j, hj, _, hk, by simp⟩
  have hcomm : ∀ w ∈ R, ∀ z ∈ O, w * z = z * w := fun w hw z hz =>
    (Subgroup.mem_centralizer_iff.mp (inf_le_left.trans hKO hw) z hz).symm
  have hJperf : ⁅J, J⁆ = J := by
    refine le_antisymm (Subgroup.commutator_mono hJR hJR) ?_
    rw [hJ, Subgroup.commutator_le]
    intro r₁ hr₁ r₂ hr₂
    obtain ⟨j₁, hj₁, z₁, hz₁, rfl⟩ := hdecomp r₁ hr₁
    obtain ⟨j₂, hj₂, z₂, hz₂, rfl⟩ := hdecomp r₂ hr₂
    have hz₁R : z₁ ∈ R := by
      have : z₁ = j₁⁻¹ * (j₁ * z₁) := by group
      rw [this]
      exact R.mul_mem (R.inv_mem (hJR hj₁)) hr₁
    have hz₂R : z₂ ∈ R := by
      have : z₂ = j₂⁻¹ * (j₂ * z₂) := by group
      rw [this]
      exact R.mul_mem (R.inv_mem (hJR hj₂)) hr₂
    have e1 : j₂ * z₁ = z₁ * j₂ := hcomm j₂ (hJR hj₂) z₁ hz₁
    have e2 : j₁ * z₂ = z₂ * j₁ := hcomm j₁ (hJR hj₁) z₂ hz₂
    have e3 : z₁ * z₂ = z₂ * z₁ := hcomm z₁ hz₁R z₂ hz₂
    have : ⁅j₁ * z₁, j₂ * z₂⁆ = ⁅j₁, j₂⁆ := by
      have c3 : Commute z₂ j₁⁻¹ := (Commute.inv_right e2.symm)
      simp only [commutatorElement_def, mul_inv_rev]
      calc j₁ * z₁ * (j₂ * z₂) * (z₁⁻¹ * j₁⁻¹) * (z₂⁻¹ * j₂⁻¹)
          = j₁ * (z₁ * j₂) * z₂ * z₁⁻¹ * j₁⁻¹ * z₂⁻¹ * j₂⁻¹ := by group
        _ = j₁ * (j₂ * z₁) * z₂ * z₁⁻¹ * j₁⁻¹ * z₂⁻¹ * j₂⁻¹ := by rw [e1]
        _ = j₁ * j₂ * (z₁ * z₂) * z₁⁻¹ * j₁⁻¹ * z₂⁻¹ * j₂⁻¹ := by group
        _ = j₁ * j₂ * (z₂ * z₁) * z₁⁻¹ * j₁⁻¹ * z₂⁻¹ * j₂⁻¹ := by rw [e3]
        _ = j₁ * j₂ * (z₂ * j₁⁻¹) * z₂⁻¹ * j₂⁻¹ := by group
        _ = j₁ * j₂ * (j₁⁻¹ * z₂) * z₂⁻¹ * j₂⁻¹ := by rw [c3.eq]
        _ = j₁ * j₂ * j₁⁻¹ * j₂⁻¹ := by group
    rw [this]
    exact Subgroup.commutator_mem_commutator hj₁ hj₂
  have hJP : Group.IsPerfect J := Subgroup.isPerfect_iff.mpr hJperf
  let β : J →* Matrix.SpecialLinearGroup (Fin 2) F := ψ.comp (Subgroup.inclusion hJL)
  have hβ : Function.Surjective β := by
    intro γ
    obtain ⟨x, hx, rfl⟩ : γ ∈ (J.subgroupOf L).map ψ := hJtop ▸ Subgroup.mem_top _
    exact ⟨⟨x, hx⟩, rfl⟩
  have hβker : β.ker = O.subgroupOf J := by
    ext x
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    change ψ (Subgroup.inclusion hJL x) = 1 ↔ _
    rw [← MonoidHom.mem_ker, hker, Subgroup.mem_subgroupOf]
    rfl
  have hcard : Nat.card β.ker = Nat.card (J ⊓ O : Subgroup G) := by
    rw [hβker, ← Subgroup.inf_subgroupOf_left]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv
  have hodd : Odd (Nat.card β.ker) := by
    rw [hcard]
    exact hO.of_dvd_nat (Subgroup.card_dvd_of_le inf_le_right)
  have hcentral : β.ker ≤ Subgroup.center J := by
    intro x hx
    rw [hβker, Subgroup.mem_subgroupOf] at hx
    rw [Subgroup.mem_center_iff]
    intro j
    apply Subtype.ext
    exact (Subgroup.mem_centralizer_iff.mp (hJO j.2) x hx).symm
  have h2F : (2 : F) ≠ 0 :=
    Ring.two_ne_zero (ringChar_ne_two_of_odd_card (by rw [hF]; exact hpodd.pow))
  obtain ⟨t₀, ht₀⟩ := hβ (CFSG.Semidihedral.OddFieldSL2.minusIdentity F)
  have hc : t₀ ^ 2 ∈ β.ker := by
    rw [MonoidHom.mem_ker, map_pow, ht₀, CFSG.Semidihedral.OddFieldSL2.minusIdentity_square]
  have hm : Odd (orderOf (t₀ ^ 2)) := hodd.of_dvd_nat (Subgroup.orderOf_dvd_natCard _ hc)
  set t := t₀ ^ orderOf (t₀ ^ 2) with ht
  have hβt : β t = CFSG.Semidihedral.OddFieldSL2.minusIdentity F := by
    obtain ⟨k, hk⟩ := hm
    rw [ht, map_pow, ht₀, hk, pow_succ, pow_mul,
      CFSG.Semidihedral.OddFieldSL2.minusIdentity_square, one_pow, one_mul]
  have ht2 : t ^ 2 = 1 := by
    rw [ht, ← pow_mul, mul_comm, pow_mul, pow_orderOf_eq_one]
  have ht1 : t ≠ 1 := by
    intro h1
    apply CFSG.Semidihedral.OddFieldSL2.minusIdentity_ne_one F h2F
    rw [← hβt, h1, map_one]
  have htord : orderOf t = 2 := orderOf_eq_prime ht2 ht1
  have htcen : t ∈ Subgroup.center J := by
    rw [Subgroup.mem_center_iff]
    intro j
    have hd : j * t * j⁻¹ * t⁻¹ ∈ β.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_mul, map_mul, map_inv, map_inv, hβt]
      have hz := CFSG.Semidihedral.OddFieldSL2.minusIdentity_mem_center F
      rw [Subgroup.mem_center_iff] at hz
      rw [hz (β j)]
      group
    have hdc := hcentral hd
    rw [Subgroup.mem_center_iff] at hdc
    set d := j * t * j⁻¹ * t⁻¹ with hdd
    have hd2 : d ^ (2 ^ 1) = 1 := by
      have e : j * t * j⁻¹ = d * t := by rw [hdd]; group
      have e2 : (j * t * j⁻¹) ^ 2 = 1 := by
        rw [sq, show j * t * j⁻¹ * (j * t * j⁻¹) = j * (t * t) * j⁻¹ by group, ← sq, ht2]
        group
      rw [e, sq, show d * t * (d * t) = d * (t * d) * t by group, hdc t,
        show d * (d * t) * t = d * d * (t * t) by group, ← sq t, ht2, mul_one] at e2
      rw [pow_one, sq]
      exact e2
    have hd1 : d = 1 := eq_one_of_mem_of_pow_two_pow hodd hd hd2
    rw [hdd] at hd1
    have : j * t * j⁻¹ = t := by
      rw [← mul_inv_eq_one]
      exact hd1
    calc j * t = j * t * j⁻¹ * j := by group
      _ = t * j := by rw [this]
  have hbounds := CFSG.Semidihedral.OddCentralSL2Kernel.central_odd_SL2_cover_kernel_bounds F hp
    hpodd hf hF hq β hβ hcentral hodd t htcen htord hβt
  have hfirst : β.ker = ⊥ → J ⊓ O = ⊥ ∧ Nonempty (J ≃* Matrix.SpecialLinearGroup (Fin 2) F) := by
    intro hbot
    refine ⟨?_, ⟨MulEquiv.ofBijective β ⟨(MonoidHom.ker_eq_bot_iff β).mp hbot, hβ⟩⟩⟩
    rw [← Subgroup.card_eq_one, ← hcard, hbot, Subgroup.card_bot]
  refine ⟨hLJO, ?_⟩
  by_cases h9 : p ^ f = 9
  · obtain ⟨-, hle⟩ := hbounds.2 h9
    have hpos : 0 < Nat.card β.ker := Nat.card_pos
    obtain ⟨k, hk⟩ := hodd
    rcases (show Nat.card β.ker = 1 ∨ Nat.card β.ker = 3 by omega) with h1 | h3
    · exact Or.inl (hfirst (Subgroup.eq_bot_of_card_eq _ h1))
    · exact Or.inr ⟨h9, hcard ▸ h3⟩
  · exact Or.inl (hfirst (hbounds.1 h9))

private theorem mem_of_orderOf_of_normal_hall [Finite G] {K B : Subgroup G} {π : Set ℕ}
    (hBK : B ≤ K) (hKB : K ≤ Subgroup.normalizer (B : Set G))
    (hB : ∀ q : ℕ, q.Prime → q ∣ Nat.card B → q ∈ π)
    (hidx : ∀ q : ℕ, q.Prime → q ∣ B.relIndex K → q ∉ π) {g : G} (hgK : g ∈ K)
    (hg : ∀ q : ℕ, q.Prime → q ∣ orderOf g → q ∈ π) : g ∈ B := by
  set Z : Subgroup G := B ⊔ Subgroup.zpowers g with hZ
  have hgB : Subgroup.zpowers g ≤ Subgroup.normalizer (B : Set G) :=
    Subgroup.zpowers_le.mpr (hKB hgK)
  have hBZ : B ≤ Z := le_sup_left
  have hZK : Z ≤ K := sup_le hBK (Subgroup.zpowers_le.mpr hgK)
  have hcardZ : Nat.card Z ∣ Nat.card B * orderOf g := by
    have h := card_sup_mul_card_inf_of_le_normalizer hgB
    rw [Nat.card_zpowers] at h
    exact Dvd.intro _ h
  have hrelZ : B.relIndex Z ∣ Nat.card Z := by
    have h := Subgroup.relIndex_mul_card B Z
    rw [inf_eq_left.mpr hBZ] at h
    exact Dvd.intro _ h
  have hrel : B.relIndex Z = 1 := by
    rw [Nat.eq_one_iff_not_exists_prime_dvd]
    intro q hq hqdvd
    apply hidx q hq ((hqdvd.trans (Dvd.intro _ (Subgroup.relIndex_mul_relIndex B Z K hBZ hZK))))
    rcases (Nat.Prime.dvd_mul hq).mp (hqdvd.trans (hrelZ.trans hcardZ)) with h | h
    · exact hB q hq h
    · exact hg q hq h
  exact (Subgroup.relIndex_eq_one.mp hrel) (Subgroup.mem_sup_right (Subgroup.mem_zpowers g))

private theorem exists_inverted_hall [Finite G] {K : Subgroup G} (hK : Odd (Nat.card K)) {a : G}
    (ha : orderOf a = 2) (haK : a ∈ Subgroup.normalizer (K : Set G))
    (hdich : ∀ r : ℕ, r.Prime → ∀ R : Subgroup G, IsSylowOf r R K →
      a ∈ Subgroup.normalizer (R : Set G) →
        R ≤ Subgroup.centralizer ({a} : Set G) ∨ ∀ y ∈ R, a * y * a⁻¹ = y⁻¹) :
    ∃ B : Subgroup G, B ≤ K ∧
      Subgroup.normalizer (K : Set G) ≤ Subgroup.normalizer (B : Set G) ∧
      (∀ y ∈ B, a * y * a⁻¹ = y⁻¹) ∧
      ∀ r : ℕ, r.Prime → ∀ R : Subgroup G, IsSylowOf r R K →
        a ∈ Subgroup.normalizer (R : Set G) → (∀ y ∈ R, a * y * a⁻¹ = y⁻¹) → R ≤ B := by
  classical
  set A : Subgroup G := Subgroup.zpowers a with hA
  have hA2 : IsPGroup 2 A := IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, ha, pow_one])
  have hAK : A ≤ Subgroup.normalizer (K : Set G) := Subgroup.zpowers_le.mpr haK
  set π : Set Nat.Primes := {p | ∀ R : Subgroup G, IsSylowOf p R K →
    a ∈ Subgroup.normalizer (R : Set G) → ∀ y ∈ R, a * y * a⁻¹ = y⁻¹} with hπ
  have hcen : ∀ p : Nat.Primes, p ∉ π → ∀ R : Subgroup G, IsSylowOf p R K →
      a ∈ Subgroup.normalizer (R : Set G) → R ≤ Subgroup.centralizer ({a} : Set G) := by
    intro p hp R hR haR
    simp only [hπ, Set.mem_ofPred_eq, not_forall] at hp
    obtain ⟨R', hR', haR', y', hy', hy'inv⟩ := hp
    have hR'c : R' ≤ Subgroup.centralizer ({a} : Set G) :=
      (hdich p p.2 R' hR' haR').resolve_right fun h => hy'inv (h y' hy')
    obtain ⟨c, hc, hcR⟩ := exists_conj_eq_of_isSylowOf_normalized_of_odd p.2 hA2 hAK hK hR' hR
      (Subgroup.zpowers_le.mpr haR') (Subgroup.zpowers_le.mpr haR)
    have hca : a * c = c * a := Subgroup.mem_centralizer_iff.mp hc.2 a (Subgroup.mem_zpowers a)
    intro y hy
    rw [← hcR] at hy
    obtain ⟨y₀, hy₀, rfl⟩ := hy
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact conj_mul_comm_of_commute hca (Subgroup.mem_centralizer_singleton_iff.mp (hR'c hy₀))
  have hsolv : Group.IsSolvable K := CFSG.FeitThompson.isSolvable_of_odd_natCard K hK
  let _ : MulDistribMulAction A K := CFSG.SignalizerFunctor.Helpers.conjugationAction A K hAK
  have hcop : Nat.Coprime (Nat.card A) (Nat.card K) := by
    rw [Nat.card_zpowers, ha]
    exact Nat.coprime_two_left.mpr hK
  obtain ⟨H₀, hH₀, hH₀inv⟩ := CFSG.exists_isHallSubgroup_isInvariant (G := K) (A := A) hsolv hcop π
  set B : Subgroup G := H₀.map K.subtype with hB
  have hBK : B ≤ K := Subgroup.map_subtype_le H₀
  have hBcard : Nat.card B = Nat.card H₀ :=
    Subgroup.card_map_of_injective K.subtype_injective
  have hBodd : Odd (Nat.card B) := hK.of_dvd_nat (Subgroup.card_dvd_of_le hBK)
  have hBsub : B.subgroupOf K = H₀ :=
    Subgroup.comap_map_eq_self_of_injective K.subtype_injective H₀
  have hBidx : B.relIndex K = H₀.index := by rw [Subgroup.relIndex, hBsub]
  set π' : Set ℕ := {n | ∃ hq : n.Prime, (⟨n, hq⟩ : Nat.Primes) ∈ π} with hπ'
  have hBπ : ∀ q : ℕ, q.Prime → q ∣ Nat.card B → q ∈ π' := fun q hq hdvd =>
    ⟨hq, hH₀.p_in_pi_of_p_dvd_card ⟨q, hq⟩ (hBcard ▸ hdvd)⟩
  have hidxπ : ∀ q : ℕ, q.Prime → q ∣ B.relIndex K → q ∉ π' := fun q hq hdvd ⟨_, hmem⟩ =>
    hH₀.p_in_pi_of_p_dvd_index ⟨q, hq⟩ (hBidx ▸ hdvd) hmem
  have haB : a ∈ Subgroup.normalizer (B : Set G) :=
    CFSG.SignalizerFunctor.Helpers.invariant_subgroup_map_normalized A K hAK H₀
      (fun b x hx => (hH₀inv.invariant b x).mp hx) (Subgroup.mem_zpowers a)
  have hFB : B ⊓ Subgroup.centralizer ({a} : Set G) = ⊥ := by
    rw [eq_bot_iff]
    intro g hg
    rw [Subgroup.mem_bot]
    by_contra hg1
    obtain ⟨p, hp, hpg⟩ := Nat.exists_prime_and_dvd (mt orderOf_eq_one_iff.mp hg1)
    have : Fact p.Prime := ⟨hp⟩
    have hg'ord : orderOf (g ^ (orderOf g / p)) = p :=
      orderOf_pow_orderOf_div (orderOf_pos g).ne' hpg
    have hg'B : g ^ (orderOf g / p) ∈ B ⊓ Subgroup.centralizer ({a} : Set G) :=
      Subgroup.pow_mem _ hg _
    set g' := g ^ (orderOf g / p) with hg'
    have hpB : p ∣ Nat.card B := hg'ord ▸ Subgroup.orderOf_dvd_natCard B hg'B.1
    have hpπ : (⟨p, hp⟩ : Nat.Primes) ∈ π := hH₀.p_in_pi_of_p_dvd_card ⟨p, hp⟩ (hBcard ▸ hpB)
    have hZK : Subgroup.zpowers g' ≤ K := Subgroup.zpowers_le.mpr (hBK hg'B.1)
    have hZp : IsPGroup p (Subgroup.zpowers g') :=
      IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hg'ord, pow_one])
    have hga : g' * a = a * g' := Subgroup.mem_centralizer_singleton_iff.mp hg'B.2
    have haZ : a ∈ Subgroup.centralizer (Subgroup.zpowers g' : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro h hh
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hh
      exact ((Commute.zpow_left hga k)).eq
    have hAZ : A ≤ Subgroup.normalizer (Subgroup.zpowers g' : Set G) :=
      Subgroup.zpowers_le.mpr (Subgroup.centralizer_le_normalizer _ haZ)
    obtain ⟨R, hR, hZR, hAR⟩ := exists_isSylowOf_normalized_ge_of_odd hp hA2 hAK hK hZK hZp hAZ
    have hinv := hpπ R hR (hAR (Subgroup.mem_zpowers a)) g' (hZR (Subgroup.mem_zpowers g'))
    have hcomm : a * g' * a⁻¹ = g' := by rw [← hga]; group
    rw [hcomm] at hinv
    have h2 : g' ^ 2 = 1 := by
      rw [sq]
      nth_rewrite 2 [hinv]
      exact mul_inv_cancel g'
    have hp2 : p ∣ 2 := hg'ord ▸ orderOf_dvd_of_pow_eq_one h2
    have hpK : p ∣ Nat.card K := hpB.trans (Subgroup.card_dvd_of_le hBK)
    obtain rfl := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp hp2
    exact (Nat.not_even_iff_odd.mpr hK) (even_iff_two_dvd.mpr hpK)
  have hBinv : ∀ y ∈ B, a * y * a⁻¹ = y⁻¹ := by
    intro y hy
    obtain ⟨h1, -⟩ := odd_fixed_mul_inverted hBodd ha haB
    have hy' : y ∈ (B : Set G) := hy
    rw [h1, hFB] at hy'
    obtain ⟨f, hf, j, hj, hfj⟩ := hy'
    have hfj : f * j = y := hfj
    rw [Subgroup.coe_bot, Set.mem_singleton_iff] at hf
    rw [← hfj, hf, one_mul]
    exact hj.2
  set I : Set G := OddInversion.invertedSet K a with hI
  have hBI : (B : Set G) ⊆ I := fun y hy => ⟨hBK hy, hBinv y hy⟩
  have hIcard : Nat.card I = (Subgroup.centralizer ({a} : Set G)).relIndex K :=
    (OddInversion.odd_inversion_coset_count hK haK (OddInversion.notMem_of_odd_card hK ha) ha).2.2
  have hCK := Subgroup.relIndex_mul_card (Subgroup.centralizer ({a} : Set G)) K
  have hBK' := Subgroup.relIndex_mul_card B K
  rw [inf_eq_left.mpr hBK] at hBK'
  have hdvd : B.relIndex K ∣ Nat.card (Subgroup.centralizer ({a} : Set G) ⊓ K : Subgroup G) := by
    have hpos1 : B.relIndex K ≠ 0 := by
      intro h0
      rw [h0, zero_mul] at hBK'
      exact Nat.card_pos.ne' hBK'.symm
    have hpos2 : Nat.card (Subgroup.centralizer ({a} : Set G) ⊓ K : Subgroup G) ≠ 0 :=
      Nat.card_pos.ne'
    rw [← Nat.factorization_prime_le_iff_dvd hpos1 hpos2]
    intro p hp
    by_cases hpd : p ∣ B.relIndex K
    · have : Fact p.Prime := ⟨hp⟩
      have hpπ : (⟨p, hp⟩ : Nat.Primes) ∉ π :=
        hH₀.p_in_pi_of_p_dvd_index ⟨p, hp⟩ (hBidx ▸ hpd)
      obtain ⟨R, hR, hAR⟩ := exists_isSylowOf_normalized_of_odd hp hA2 hAK hK
      have hRC := hcen ⟨p, hp⟩ hpπ R hR (hAR (Subgroup.mem_zpowers a))
      have hRle : R ≤ Subgroup.centralizer ({a} : Set G) ⊓ K := le_inf hRC hR.le
      have h1 : p ^ (Nat.card K).factorization p ∣
          Nat.card (Subgroup.centralizer ({a} : Set G) ⊓ K : Subgroup G) :=
        hR.card_eq ▸ Subgroup.card_dvd_of_le hRle
      have h2 := (hp.pow_dvd_iff_le_factorization hpos2).mp h1
      refine le_trans ?_ h2
      exact (Nat.factorization_le_iff_dvd hpos1 Nat.card_pos.ne').mpr
        (Dvd.intro _ hBK') p
    · rw [Nat.factorization_eq_zero_of_not_dvd hpd]
      exact Nat.zero_le _
  have hIle : Nat.card I ≤ Nat.card B := by
    have hle := Nat.le_of_dvd Nat.card_pos hdvd
    have hpos : 0 < Nat.card (Subgroup.centralizer ({a} : Set G) ⊓ K : Subgroup G) := Nat.card_pos
    rw [hIcard]
    refine Nat.le_of_mul_le_mul_right ?_ hpos
    calc (Subgroup.centralizer ({a} : Set G)).relIndex K *
          Nat.card (Subgroup.centralizer ({a} : Set G) ⊓ K : Subgroup G) = Nat.card K := hCK
      _ = B.relIndex K * Nat.card B := hBK'.symm
      _ ≤ Nat.card (Subgroup.centralizer ({a} : Set G) ⊓ K : Subgroup G) * Nat.card B :=
          Nat.mul_le_mul_right _ hle
      _ = Nat.card B * Nat.card (Subgroup.centralizer ({a} : Set G) ⊓ K : Subgroup G) :=
          mul_comm _ _
  have hBeq : (B : Set G) = I := by
    apply Set.eq_of_subset_of_ncard_le hBI _ (Set.toFinite I)
    rw [← Nat.card_coe_set_eq, ← Nat.card_coe_set_eq, SetLike.coe_sort_coe]
    exact hIle
  have hKB : K ≤ Subgroup.normalizer (B : Set G) := by
    intro k hk
    apply mem_normalizer_of_map_conj_le
    rintro _ ⟨b, hb, rfl⟩
    change k * b * k⁻¹ ∈ B
    obtain ⟨h1, -⟩ := odd_fixed_mul_inverted hK ha haK
    have hk' : k ∈ (K : Set G) := hk
    rw [h1] at hk'
    obtain ⟨f, hf, j, hj, hfj⟩ := hk'
    have hfj : f * j = k := hfj
    have hjB : j ∈ B := by rw [← SetLike.mem_coe, hBeq]; exact hj
    have hjb : j * b * j⁻¹ ∈ B := B.mul_mem (B.mul_mem hjB hb) (B.inv_mem hjB)
    have hfa : a * f = f * a :=
      (Subgroup.mem_centralizer_singleton_iff.mp (Subgroup.mem_inf.mp hf).2).symm
    have hmem : f * (j * b * j⁻¹) * f⁻¹ ∈ I := by
      refine ⟨K.mul_mem (K.mul_mem (Subgroup.mem_inf.mp hf).1 (hBK hjb))
        (K.inv_mem (Subgroup.mem_inf.mp hf).1), ?_⟩
      exact conj_inv_of_commute hfa (hBinv _ hjb)
    rw [← hBeq] at hmem
    rw [← hfj]
    have : f * j * b * (f * j)⁻¹ = f * (j * b * j⁻¹) * f⁻¹ := by group
    rw [this]
    exact hmem
  refine ⟨B, hBK, ?_, hBinv, ?_⟩
  · intro n hn
    apply mem_normalizer_of_map_conj_le
    rintro _ ⟨b, hb, rfl⟩
    change n * b * n⁻¹ ∈ B
    refine mem_of_orderOf_of_normal_hall hBK hKB hBπ hidxπ
      ((Subgroup.mem_normalizer_iff.mp hn b).mp (hBK hb)) fun q hq hqd => hBπ q hq ?_
    have hord : orderOf (n * b * n⁻¹) = orderOf b := MulEquiv.orderOf_eq (MulAut.conj n) b
    exact hqd.trans (hord ▸ Subgroup.orderOf_dvd_natCard B hb)
  · intro r hr R hR haR hinv y hy
    rw [← SetLike.mem_coe, hBeq]
    exact ⟨hR.le hy, hinv y hy⟩

private theorem le_normalizer_centralizer_sup [Finite G] {N O R : Subgroup G} {p : ℕ}
    (hp : p.Prime) (hR : IsSylowOf p R O) (hON : O ≤ N)
    (hNO : N ≤ Subgroup.normalizer (O : Set G)) {x x₂ : G} (hx : ∀ n ∈ N, n * x = x * n)
    (hx₂ : x₂ ∈ N)
    (hRx₂ : R ≤ Subgroup.centralizer ({x₂} : Set G) ∨ ∀ y ∈ R, x₂ * y * x₂⁻¹ = y⁻¹) :
    N ≤ Subgroup.normalizer ((N ⊓ Subgroup.centralizer (R : Set G) ⊔
      Subgroup.closure ({x, x₂} : Set G) ⊔ O : Subgroup G) : Set G) := by
  have : Fact p.Prime := ⟨hp⟩
  set H : Subgroup G := N ⊓ Subgroup.centralizer (R : Set G) ⊔
    Subgroup.closure ({x, x₂} : Set G) ⊔ O with hH
  intro n hn
  have hRn : IsSylowOf p (R.map (MulAut.conj n).toMonoidHom) O := by
    apply isSylowOf_of_card
    · rintro _ ⟨r, hr, rfl⟩
      exact (Subgroup.mem_normalizer_iff.mp (hNO hn) r).mp (hR.le hr)
    · rw [Subgroup.card_map_of_injective (MulAut.conj n).injective, hR.card_eq]
  obtain ⟨a, ha, hka⟩ := hR.exists_mem_conj hRn
  have hkR : a⁻¹ * n ∈ Subgroup.normalizer (R : Set G) := by
    rw [Subgroup.mem_normalizer_iff]
    intro r
    constructor
    · intro hr
      have := (hka (n * r * n⁻¹)).mp ⟨r, hr, rfl⟩
      simpa [mul_assoc] using this
    · intro hr
      have h1 : n * r * n⁻¹ ∈ R.map (MulAut.conj n).toMonoidHom := by
        rw [hka]
        simpa [mul_assoc] using hr
      obtain ⟨r', hr', hrr'⟩ := h1
      have : r' = r := by
        simpa using hrr'
      rw [← this]
      exact hr'
  set k := a⁻¹ * n with hk
  have hkN : k ∈ N := N.mul_mem (N.inv_mem (hON ha)) hn
  have hkH : k ∈ Subgroup.normalizer (H : Set G) := by
    apply mem_normalizer_of_map_conj_le
    rw [Subgroup.map_le_iff_le_comap]
    have hK₀ : N ⊓ Subgroup.centralizer (R : Set G) ≤ H.comap (MulAut.conj k).toMonoidHom := by
      intro c ⟨hcN, hcR⟩
      rw [Subgroup.mem_comap]
      change k * c * k⁻¹ ∈ H
      refine Subgroup.mem_sup_left (Subgroup.mem_sup_left ⟨N.mul_mem (N.mul_mem hkN hcN)
        (N.inv_mem hkN), ?_⟩)
      exact (Subgroup.mem_normalizer_iff.mp (normalizer_le_normalizer_centralizer R hkR) c).mp
        hcR
    have hT : Subgroup.closure ({x, x₂} : Set G) ≤ H.comap (MulAut.conj k).toMonoidHom := by
      rw [Subgroup.closure_le]
      rintro t (rfl | rfl)
      · change k * t * k⁻¹ ∈ H
        have : k * t * k⁻¹ = t := by
          rw [hx k hkN]
          group
        rw [this]
        exact Subgroup.mem_sup_left (Subgroup.mem_sup_right
          (Subgroup.subset_closure (Set.mem_insert _ _)))
      · change k * t * k⁻¹ ∈ H
        have hd : k * t * k⁻¹ * t⁻¹ ∈ N ⊓ Subgroup.centralizer (R : Set G) := by
          refine ⟨N.mul_mem (N.mul_mem (N.mul_mem hkN hx₂) (N.inv_mem hkN)) (N.inv_mem hx₂), ?_⟩
          rcases hRx₂ with hcen | hinv
          · have hx₂C : t ∈ Subgroup.centralizer (R : Set G) := by
              rw [Subgroup.mem_centralizer_iff]
              intro r hr
              exact Subgroup.mem_centralizer_singleton_iff.mp (hcen hr)
            refine Subgroup.mul_mem _ ?_ (Subgroup.inv_mem _ hx₂C)
            exact (Subgroup.mem_normalizer_iff.mp
              (normalizer_le_normalizer_centralizer R hkR) t).mp hx₂C
          · exact commutator_mem_centralizer_of_inverts hinv hkR
        have : k * t * k⁻¹ = (k * t * k⁻¹ * t⁻¹) * t := by group
        rw [this]
        exact Subgroup.mem_sup_left (Subgroup.mul_mem_sup hd
          (Subgroup.subset_closure (Set.mem_insert_of_mem _ (Set.mem_singleton _))))
    have hO : O ≤ H.comap (MulAut.conj k).toMonoidHom := by
      intro b hb
      rw [Subgroup.mem_comap]
      change k * b * k⁻¹ ∈ H
      exact Subgroup.mem_sup_right ((Subgroup.mem_normalizer_iff.mp (hNO hkN) b).mp hb)
    exact sup_le (sup_le hK₀ hT) hO
  have haH : a ∈ Subgroup.normalizer (H : Set G) :=
    Subgroup.le_normalizer (Subgroup.mem_sup_right ha)
  have : n = a * k := by rw [hk]; group
  rw [this]
  exact Subgroup.mul_mem _ haH hkH

structure LayerHyp (N O L : Subgroup G) (S : Sylow 2 G) (x x₂ : G) {F : Type} [Field F]
    (ψ : L →* Matrix.SpecialLinearGroup (Fin 2) F) (p f : ℕ) : Prop where
  surj : Function.Surjective ψ
  ker : ψ.ker = O.subgroupOf L
  O_le_L : O ≤ L
  odd_O : Odd (Nat.card O)
  O_le_N : O ≤ N
  N_le_normalizer_O : N ≤ Subgroup.normalizer (O : Set G)
  N_le_normalizer_L : N ≤ Subgroup.normalizer (L : Set G)
  S_le_N : (S : Subgroup G) ≤ N
  p_prime : p.Prime
  odd_p : Odd p
  one_le_f : 1 ≤ f
  card_F : Nat.card F = p ^ f
  five_le : 5 ≤ p ^ f
  x_central : ∀ n ∈ N, n * x = x * n
  x_mem : x ∈ (S : Subgroup G)
  x₂_mem : x₂ ∈ (S : Subgroup G)
  x₂_notMem_center : x₂ ∉ centerOf (S : Subgroup G)
  minimalNormal : ∀ K : Subgroup G, K ≤ N → N ≤ Subgroup.normalizer (K : Set G) →
    ¬ K ≤ O ⊔ centerOf (S : Subgroup G) → L ≤ K ⊔ (O ⊔ centerOf (S : Subgroup G))
  coverTransfer : ∀ K : Subgroup G, K ≤ N → L ≤ K ⊔ (O ⊔ centerOf (S : Subgroup G)) →
    (L : Set G) ⊆ (K : Set G) * (O : Set G)

namespace LayerHyp

variable [Finite G] {N O L : Subgroup G} {S : Sylow 2 G} {x x₂ : G} {F : Type} [Field F]
  [Finite F] {ψ : L →* Matrix.SpecialLinearGroup (Fin 2) F} {p f : ℕ}

theorem layer (hL : LayerHyp N O L S x x₂ ψ p f)
    (h : ¬ N ⊓ Subgroup.centralizer (O : Set G) ≤ O ⊔ centerOf (S : Subgroup G)) :
    ∃ J : Subgroup G, J ≤ L ∧ L = J ⊔ O ∧ J ≤ Subgroup.centralizer (O : Set G) ∧
      N ≤ Subgroup.normalizer (J : Set G) ∧
      ((J ⊓ O = ⊥ ∧ Nonempty (J ≃* Matrix.SpecialLinearGroup (Fin 2) F)) ∨
        (p ^ f = 9 ∧ Nat.card (J ⊓ O : Subgroup G) = 3)) := by
  set K : Subgroup G := N ⊓ Subgroup.centralizer (O : Set G) with hK
  have hKN : K ≤ N := inf_le_left
  have hNK : N ≤ Subgroup.normalizer (K : Set G) :=
    (le_inf Subgroup.le_normalizer
      (hL.N_le_normalizer_O.trans (normalizer_le_normalizer_centralizer O))).trans
      Subgroup.inf_normalizer_le_normalizer_inf
  have hcov := hL.coverTransfer K hKN (hL.minimalNormal K hKN hNK h)
  have hcov' : L ≤ K ⊔ O := fun l hl => by
    obtain ⟨k, hk, a, ha, rfl⟩ := hcov hl
    exact Subgroup.mul_mem_sup hk ha
  obtain ⟨hLJO, halt⟩ := layer_of_le_centralizer_sup ψ hL.surj hL.ker hL.O_le_L hL.odd_O
    inf_le_right hcov' hL.p_prime hL.odd_p hL.one_le_f hL.card_F hL.five_le
  have hRL : K ⊓ L ≤ L := inf_le_right
  have hJR : ⁅K ⊓ L, K ⊓ L⁆ ≤ K ⊓ L := Subgroup.commutator_le.mpr fun g₁ h₁ g₂ h₂ => by
    rw [commutatorElement_def]
    exact (K ⊓ L).mul_mem ((K ⊓ L).mul_mem ((K ⊓ L).mul_mem h₁ h₂)
      ((K ⊓ L).inv_mem h₁)) ((K ⊓ L).inv_mem h₂)
  refine ⟨⁅K ⊓ L, K ⊓ L⁆, hJR.trans hRL, hLJO, hJR.trans (inf_le_left.trans inf_le_right),
    ((le_inf hNK hL.N_le_normalizer_L).trans Subgroup.inf_normalizer_le_normalizer_inf).trans
      (normalizer_le_normalizer_commutator _), halt⟩

open CFSG.LocalAnalysis.ComponentInitial.QuaternionMatrices in
private theorem mem_centralizer_sylow (hL : LayerHyp N O L S x x₂ ψ p f) {y : G}
    (hy : ∀ X : Subgroup G, X ≤ S → (S : Subgroup G) ≤ Subgroup.normalizer (X : Set G) →
      (∃ Q : Subgroup G, Q ≤ X ∧ Nonempty (Q ≃* QuaternionGroup 2)) → y ∈ X)
    {r : ℕ} (hr : r.Prime) {R : Subgroup G} (hR : IsSylowOf r R O)
    (hSR : (S : Subgroup G) ≤ Subgroup.normalizer (R : Set G))
    (hRx₂ : R ≤ Subgroup.centralizer ({x₂} : Set G) ∨ ∀ y ∈ R, x₂ * y * x₂⁻¹ = y⁻¹) :
    y ∈ Subgroup.centralizer (R : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set T : Subgroup G := Subgroup.closure ({x, x₂} : Set G) with hT
  have hTS : T ≤ S := by
    rw [hT, Subgroup.closure_le]
    rintro t (rfl | rfl)
    · exact hL.x_mem
    · exact hL.x₂_mem
  set K₀ : Subgroup G := N ⊓ Subgroup.centralizer (R : Set G) with hK₀
  set H : Subgroup G := K₀ ⊔ T ⊔ O with hH
  have hHN : H ≤ N := sup_le (sup_le inf_le_left (hTS.trans hL.S_le_N)) hL.O_le_N
  have hNH : N ≤ Subgroup.normalizer (H : Set G) :=
    le_normalizer_centralizer_sup hr hR hL.O_le_N hL.N_le_normalizer_O hL.x_central
      (hL.S_le_N hL.x₂_mem) hRx₂
  have hHS : ¬ H ≤ O ⊔ centerOf (S : Subgroup G) := fun h =>
    hL.x₂_notMem_center (mem_of_mem_sup_of_isPGroup hL.odd_O S.isPGroup' inf_le_left
      ((inf_le_left.trans hL.S_le_N).trans hL.N_le_normalizer_O) hL.x₂_mem
      (h (Subgroup.mem_sup_left (Subgroup.mem_sup_right
        (Subgroup.subset_closure (Set.mem_insert_of_mem _ (Set.mem_singleton _)))))))
  have hL₀ := hL.minimalNormal H hHN hNH hHS
  have hSK₀ : (S : Subgroup G) ≤ Subgroup.normalizer (K₀ : Set G) :=
    (le_inf (hL.S_le_N.trans Subgroup.le_normalizer)
      (hSR.trans (normalizer_le_normalizer_centralizer R))).trans
      Subgroup.inf_normalizer_le_normalizer_inf
  have hPS : T ⊔ centerOf (S : Subgroup G) ≤ S := sup_le hTS inf_le_left
  have hP2 : IsPGroup 2 (T ⊔ centerOf (S : Subgroup G) : Subgroup G) := S.isPGroup'.to_le hPS
  have hPA : T ⊔ centerOf (S : Subgroup G) ≤ Subgroup.normalizer ((K₀ ⊔ O : Subgroup G) : Set G) :=
    hPS.trans ((le_inf hSK₀ (hL.S_le_N.trans hL.N_le_normalizer_O)).trans
      (normalizer_inf_normalizer_le_normalizer_sup _ _))
  have hLAP : L ≤ K₀ ⊔ O ⊔ (T ⊔ centerOf (S : Subgroup G)) := by
    refine hL₀.trans ?_
    refine sup_le (sup_le (sup_le ?_ ?_) ?_) (sup_le ?_ ?_)
    · exact le_sup_left.trans le_sup_left
    · exact le_sup_left.trans le_sup_right
    · exact le_sup_right.trans le_sup_left
    · exact le_sup_right.trans le_sup_left
    · exact le_sup_right.trans le_sup_right
  have hFodd : Odd (Nat.card F) := by
    rw [hL.card_F]
    exact hL.odd_p.pow
  have hperf : Group.IsPerfect (Matrix.SpecialLinearGroup (Fin 2) F) :=
    sl2_isPerfect (by rw [hL.card_F]; exact hL.five_le.trans' (by omega))
  have hLA : L ≤ K₀ ⊔ O := by
    refine le_of_le_sup_of_isPGroup ψ hL.surj ?_ hLAP hP2 hPA
    rw [hL.ker]
    intro z hz
    rw [Subgroup.mem_subgroupOf] at hz ⊢
    exact Subgroup.mem_sup_right hz
  have hK₀N : K₀ ≤ Subgroup.normalizer (O : Set G) := inf_le_left.trans hL.N_le_normalizer_O
  have hXtop : ((K₀ ⊓ L).subgroupOf L).map ψ = ⊤ := by
    rw [map_inf_eq_range hL.O_le_L hK₀N hLA ψ hL.ker.ge, MonoidHom.range_eq_top.mpr hL.surj]
  obtain ⟨⟨a, b, hab⟩, hQ⟩ := odd_field_two_dimensional_quaternion_matrices (K := F)
    (ringChar_ne_two_of_odd_card hFodd)
  obtain ⟨-, -, -, -, -, Q₀, -, hQ₀card, ⟨eQ₀⟩, -⟩ := hQ a b hab
  have hQ₀2 : IsPGroup 2 Q₀ := IsPGroup.of_card (n := 3) (by rw [hQ₀card]; norm_num)
  obtain ⟨Q, hQX, hQ2, ⟨eQ⟩⟩ :=
    exists_le_mulEquiv_of_le_map ψ hL.ker hL.odd_O hQ₀2 (hXtop ▸ le_top)
  have hSX : (S : Subgroup G) ≤ Subgroup.normalizer ((K₀ ⊓ L : Subgroup G) : Set G) :=
    (le_inf hSK₀ (hL.S_le_N.trans hL.N_le_normalizer_L)).trans
      Subgroup.inf_normalizer_le_normalizer_inf
  obtain ⟨g, -, hgQ⟩ := exists_conj_le_sylow_inf S hSX hQX hQ2
  have hiso : Nonempty (Q.map (MulAut.conj g).toMonoidHom ≃* QuaternionGroup 2) :=
    ⟨((Q.equivMapOfInjective _ (MulAut.conj g).injective).symm.trans eQ).trans eQ₀⟩
  have hSSX : (S : Subgroup G) ≤
      Subgroup.normalizer (((S : Subgroup G) ⊓ (K₀ ⊓ L) : Subgroup G) : Set G) :=
    (le_inf Subgroup.le_normalizer hSX).trans Subgroup.inf_normalizer_le_normalizer_inf
  have hyX := hy _ inf_le_left hSSX ⟨_, hgQ, hiso⟩
  exact hyX.2.1.2

theorem not_le_of_quaternion (hL : LayerHyp N O L S x x₂ ψ p f)
    (hdich : ∀ r : ℕ, r.Prime → ∀ R : Subgroup G, IsSylowOf r R O →
      (S : Subgroup G) ≤ Subgroup.normalizer (R : Set G) →
        R ≤ Subgroup.centralizer ({x₂} : Set G) ∨ ∀ y ∈ R, x₂ * y * x₂⁻¹ = y⁻¹)
    {y : G} (hyS : y ∈ (S : Subgroup G)) (hyZ : y ∉ centerOf (S : Subgroup G))
    (hy : ∀ X : Subgroup G, X ≤ S → (S : Subgroup G) ≤ Subgroup.normalizer (X : Set G) →
      (∃ Q : Subgroup G, Q ≤ X ∧ Nonempty (Q ≃* QuaternionGroup 2)) → y ∈ X) :
    ¬ N ⊓ Subgroup.centralizer (O : Set G) ≤ O ⊔ centerOf (S : Subgroup G) := by
  have hOy : O ≤ Subgroup.centralizer ({y} : Set G) := by
    apply le_of_forall_isSylowOf_le
    intro r hr
    obtain ⟨R, hR, hSR⟩ := exists_isSylowOf_normalized_of_odd hr S.isPGroup'
      (hL.S_le_N.trans hL.N_le_normalizer_O) hL.odd_O
    refine ⟨R, hR, fun z hz => ?_⟩
    have hyR := hL.mem_centralizer_sylow hy hr hR hSR (hdich r hr R hR hSR)
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact Subgroup.mem_centralizer_iff.mp hyR z hz
  intro hle
  have hyC : y ∈ N ⊓ Subgroup.centralizer (O : Set G) := by
    refine Subgroup.mem_inf.mpr ⟨hL.S_le_N hyS, ?_⟩
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    exact Subgroup.mem_centralizer_singleton_iff.mp (hOy hz)
  exact hyZ (mem_of_mem_sup_of_isPGroup hL.odd_O S.isPGroup' inf_le_left
    ((inf_le_left.trans hL.S_le_N).trans hL.N_le_normalizer_O) hyS (hle hyC))

end LayerHyp

end General

namespace Setting

variable {G : Type u} [Group G] [Finite G] (σ : Setting G)

@[expose] def PropIV51 : Prop :=
  ∀ J : Subgroup G, J ≤ σ.L₀ → σ.L₀ = J ⊔ σ.ON → J ≤ Subgroup.centralizer (σ.ON : Set G) →
    σ.N ≤ Subgroup.normalizer (J : Set G) → σ.q = 9 → Nat.card (J ⊓ σ.ON : Subgroup G) = 3 →
      σ.height = 1

omit [Finite G] in
theorem propIV51_of_height_eq_one (h : σ.height = 1) : σ.PropIV51 :=
  fun _ _ _ _ _ _ _ => h

private theorem odd_p (hσ : σ.IsValid) : Odd σ.p :=
  hσ.p_prime.eq_two_or_odd'.resolve_left hσ.p_ne_two

private theorem layerHyp (hσ : σ.IsValid) (hII : σ.ChapterIIFacts) {F : Type} [Field F]
    {ψ : σ.L₀ →* Matrix.SpecialLinearGroup (Fin 2) F} (hψ : Function.Surjective ψ)
    (hker : ψ.ker = σ.ON.subgroupOf σ.L₀) (hF : Nat.card F = σ.q) :
    LayerHyp σ.N σ.ON σ.L₀ σ.S σ.x σ.x₂ ψ σ.p σ.f where
  surj := hψ
  ker := hker
  O_le_L := hσ.ON_le_L₀
  odd_O := σ.odd_card_ON
  O_le_N := σ.ON_le_N
  N_le_normalizer_O := σ.N_le_normalizer_ON
  N_le_normalizer_L := hσ.N_le_normalizer_L₀
  S_le_N := σ.S_le_N hσ
  p_prime := hσ.p_prime
  odd_p := σ.odd_p hσ
  one_le_f := hσ.one_le_f
  card_F := hF
  five_le := hσ.five_lt_q.le
  x_central := fun n hn => (σ.mem_N_iff n).mp hn
  x_mem := σ.x_mem_S hσ
  x₂_mem := hσ.x₂_mem
  x₂_notMem_center := fun h => hσ.x_ne_x₂ (hσ.center_involution σ.x₂ h hσ.x₂_order).symm
  minimalNormal := fun K hKN hNK hK => by
    have h := hII.N_minimalNormal K hKN hNK (by rwa [hII.N_solvRad])
    rwa [hII.N_solvRad] at h
  coverTransfer := fun K hKN hLK => hII.N_coverTransfer K hKN (by rwa [hII.N_solvRad])

theorem layer_of_not_centralizer_le (hσ : σ.IsValid) (hII : σ.ChapterIIFacts)
    (h : ¬ σ.N ⊓ Subgroup.centralizer (σ.ON : Set G) ≤ solvRadIn σ.N) :
    ∃ J : Subgroup G, J ≤ σ.L₀ ∧ σ.L₀ = J ⊔ σ.ON ∧
      J ≤ Subgroup.centralizer (σ.ON : Set G) ∧ σ.N ≤ Subgroup.normalizer (J : Set G) ∧
      ((J ⊓ σ.ON = ⊥ ∧ ∃ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = σ.q ∧
          Nonempty (J ≃* Matrix.SpecialLinearGroup (Fin 2) F)) ∨
        (σ.q = 9 ∧ Nat.card (J ⊓ σ.ON : Subgroup G) = 3)) := by
  obtain ⟨F, _, _, hFcard, ψ, hψ, hker⟩ := hσ.L₀_quotient
  rw [hII.N_solvRad] at h
  obtain ⟨J, hJL, hLJ, hJC, hNJ, halt⟩ := (σ.layerHyp hσ hII hψ hker hFcard).layer h
  refine ⟨J, hJL, hLJ, hJC, hNJ, ?_⟩
  rcases halt with ⟨hbot, hiso⟩ | ⟨h9, h3⟩
  · exact Or.inl ⟨hbot, F, inferInstance, inferInstance, hFcard, hiso⟩
  · exact Or.inr ⟨h9, h3⟩

omit [Finite G] in
private theorem mem_C_iff (g : G) : g ∈ σ.C ↔ σ.x * g = g * σ.x ∧ σ.x₂ * g = g * σ.x₂ := by
  rw [C, T, Subgroup.mem_centralizer_iff]
  constructor
  · intro h
    exact ⟨h _ (Subgroup.subset_closure (Set.mem_insert _ _)),
      h _ (Subgroup.subset_closure (Set.mem_insert_of_mem _ (Set.mem_singleton _)))⟩
  · rintro ⟨h1, h2⟩ t ht
    have hle : Subgroup.closure ({σ.x, σ.x₂} : Set G) ≤ Subgroup.centralizer {g} := by
      rw [Subgroup.closure_le]
      rintro a (rfl | rfl) <;> rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff]
      · exact h1
      · exact h2
    exact Subgroup.mem_centralizer_singleton_iff.mp (hle ht)

theorem inverted_of_totallyInverted (hσ : σ.IsValid) {r : ℕ} (hr : r.Prime)
    (_hdiv : r ∣ Nat.card σ.ON) (hti : σ.TotallyInverted r) : σ.Inverted r := by
  have hT2 : IsPGroup 2 σ.T := σ.S.isPGroup'.to_le (σ.T_le_S hσ)
  obtain ⟨R, hR, hTR⟩ := exists_isSylowOf_normalized_of_odd hr hT2
    ((σ.T_le_N hσ).trans σ.N_le_normalizer_ON) σ.odd_card_ON
  refine ⟨R, hR, hTR, ?_⟩
  have hRodd : Odd (Nat.card R) := σ.odd_card_ON.of_dvd_nat (Subgroup.card_dvd_of_le hR.le)
  have hx₂R : σ.x₂ ∈ Subgroup.normalizer (R : Set G) := hTR σ.x₂_mem_T
  have hF : R ⊓ Subgroup.centralizer {σ.x₂} = ⊥ := by
    have hle : R ⊓ Subgroup.centralizer {σ.x₂} ≤ σ.C ⊓ σ.L := by
      intro g ⟨hgR, hgx₂⟩
      refine ⟨(σ.mem_C_iff g).mpr ⟨?_, ?_⟩, show g ∈ σ.L₀ ⊔ (σ.S : Subgroup G) from
        Subgroup.mem_sup_left (hσ.ON_le_L₀ (hR.le hgR))⟩
      · exact ((σ.mem_N_iff g).mp (σ.ON_le_N (hR.le hgR))).symm
      · exact (Subgroup.mem_centralizer_singleton_iff.mp hgx₂).symm
    have : Fact r.Prime := ⟨hr⟩
    obtain ⟨k, hk⟩ := (hR.isPGroup.to_le inf_le_left :
      IsPGroup r (R ⊓ Subgroup.centralizer {σ.x₂} : Subgroup G)).exists_card_eq
    apply Subgroup.eq_bot_of_card_eq
    rcases Nat.eq_zero_or_pos k with rfl | hk0
    · rw [hk, pow_zero]
    · exfalso
      apply hti
      exact (dvd_pow_self r hk0.ne').trans (hk ▸ Subgroup.card_dvd_of_le hle)
  intro y hy
  obtain ⟨h1, -⟩ := odd_fixed_mul_inverted hRodd hσ.x₂_order hx₂R
  have hy' : y ∈ (R : Set G) := hy
  rw [h1, hF] at hy'
  obtain ⟨f, hf, j, hj, hfj⟩ := hy'
  rw [Subgroup.coe_bot, Set.mem_singleton_iff] at hf
  have hyj : y = j := by rw [← hfj, hf]; exact one_mul j
  rw [hyj]
  exact hj.2

theorem sylow_centralized_or_inverted_of_prime (hσ : σ.IsValid) {r : ℕ} (hr : r.Prime)
    (h : r ∣ Nat.card σ.ON → σ.Centralized r ∨ σ.Inverted r) {R : Subgroup G}
    (hR : IsSylowOf r R σ.ON) (hTR : σ.T ≤ Subgroup.normalizer (R : Set G)) :
    R ≤ Subgroup.centralizer ({σ.x₂} : Set G) ∨ ∀ y ∈ R, σ.x₂ * y * σ.x₂⁻¹ = y⁻¹ := by
  have hT2 : IsPGroup 2 σ.T := σ.S.isPGroup'.to_le (σ.T_le_S hσ)
  have hTON : σ.T ≤ Subgroup.normalizer (σ.ON : Set G) :=
    (σ.T_le_N hσ).trans σ.N_le_normalizer_ON
  by_cases hdiv : r ∣ Nat.card σ.ON
  · have hconj : ∀ R₀ : Subgroup G, IsSylowOf r R₀ σ.ON →
        σ.T ≤ Subgroup.normalizer (R₀ : Set G) →
        ∃ c, σ.x₂ * c = c * σ.x₂ ∧ ∀ y ∈ R, ∃ y₀ ∈ R₀, y = c * y₀ * c⁻¹ := by
      intro R₀ hR₀ hTR₀
      obtain ⟨c, hc, hcR⟩ := exists_conj_eq_of_isSylowOf_normalized_of_odd hr hT2 hTON
        σ.odd_card_ON hR₀ hR hTR₀ hTR
      refine ⟨c, Subgroup.mem_centralizer_iff.mp hc.2 σ.x₂ σ.x₂_mem_T, fun y hy => ?_⟩
      rw [← hcR] at hy
      obtain ⟨y₀, hy₀, rfl⟩ := hy
      exact ⟨y₀, hy₀, rfl⟩
    rcases h hdiv with ⟨R₀, hR₀, hTR₀, hcen⟩ | ⟨R₀, hR₀, hTR₀, hinv⟩
    · left
      obtain ⟨c, hc, hcR⟩ := hconj R₀ hR₀ hTR₀
      intro y hy
      obtain ⟨y₀, hy₀, rfl⟩ := hcR y hy
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact conj_mul_comm_of_commute hc (Subgroup.mem_centralizer_iff.mp (hcen σ.x₂_mem_T) y₀ hy₀)
    · right
      obtain ⟨c, hc, hcR⟩ := hconj R₀ hR₀ hTR₀
      intro y hy
      obtain ⟨y₀, hy₀, rfl⟩ := hcR y hy
      exact conj_inv_of_commute hc (hinv y₀ hy₀)
  · left
    have : Fact r.Prime := ⟨hr⟩
    have hRbot : R = ⊥ := by
      apply Subgroup.eq_bot_of_card_eq
      rw [hR.card_eq, Nat.factorization_eq_zero_of_not_dvd hdiv, pow_zero]
    rw [hRbot]
    exact bot_le

theorem sylow_centralized_or_inverted_of_forall (hσ : σ.IsValid)
    (h : ∀ r : ℕ, r.Prime → r ∣ Nat.card σ.ON → σ.Centralized r ∨ σ.Inverted r)
    {r : ℕ} (hr : r.Prime) {R : Subgroup G} (hR : IsSylowOf r R σ.ON)
    (hTR : σ.T ≤ Subgroup.normalizer (R : Set G)) :
    R ≤ Subgroup.centralizer ({σ.x₂} : Set G) ∨ ∀ y ∈ R, σ.x₂ * y * σ.x₂⁻¹ = y⁻¹ :=
  σ.sylow_centralized_or_inverted_of_prime hσ hr (h r hr) hR hTR

theorem layer_of_centralized_or_inverted (hσ : σ.IsValid) (hII : σ.ChapterIIFacts)
    (h : ∀ r : ℕ, r.Prime → r ∣ Nat.card σ.ON → σ.Centralized r ∨ σ.Inverted r)
    (h_II_1_1 : ∃ y ∈ (σ.S : Subgroup G), y ∉ centerOf (σ.S : Subgroup G) ∧
      ∀ X : Subgroup G, X ≤ σ.S → (σ.S : Subgroup G) ≤ Subgroup.normalizer (X : Set G) →
        (∃ Q : Subgroup G, Q ≤ X ∧ Nonempty (Q ≃* QuaternionGroup 2)) → y ∈ X) :
    ∃ J : Subgroup G, J ≤ σ.L₀ ∧ σ.L₀ = J ⊔ σ.ON ∧
      J ≤ Subgroup.centralizer (σ.ON : Set G) ∧ σ.N ≤ Subgroup.normalizer (J : Set G) ∧
      ((J ⊓ σ.ON = ⊥ ∧ ∃ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = σ.q ∧
          Nonempty (J ≃* Matrix.SpecialLinearGroup (Fin 2) F)) ∨
        (σ.q = 9 ∧ Nat.card (J ⊓ σ.ON : Subgroup G) = 3)) := by
  obtain ⟨y, hyS, hyZ, hy⟩ := h_II_1_1
  apply σ.layer_of_not_centralizer_le hσ hII
  obtain ⟨F, _, _, hFcard, ψ, hψ, hker⟩ := hσ.L₀_quotient
  rw [hII.N_solvRad]
  exact (σ.layerHyp hσ hII hψ hker hFcard).not_le_of_quaternion
    (fun r hr R hR hSR => σ.sylow_centralized_or_inverted_of_forall hσ h hr hR
      ((σ.T_le_S hσ).trans hSR)) hyS hyZ hy

theorem corollaryV61 (hσ : σ.IsValid) (hII : σ.ChapterIIFacts)
    (hV : σ.NotTotallyInvertedOrdinary) (h51 : σ.PropIV51)
    (h_II_1_1 : ∃ y ∈ (σ.S : Subgroup G), y ∉ centerOf (σ.S : Subgroup G) ∧
      ∀ X : Subgroup G, X ≤ σ.S → (σ.S : Subgroup G) ≤ Subgroup.normalizer (X : Set G) →
        (∃ Q : Subgroup G, Q ≤ X ∧ Nonempty (Q ≃* QuaternionGroup 2)) → y ∈ X) :
    σ.CorollaryV61 := by
  have h : ∀ r : ℕ, r.Prime → r ∣ Nat.card σ.ON → σ.Centralized r ∨ σ.Inverted r := by
    intro r hr hdiv
    by_cases hti : σ.TotallyInverted r
    · exact Or.inr (σ.inverted_of_totallyInverted hσ hr hdiv hti)
    · exact (hV r hr hdiv hti).2
  have hi : ∀ r : ℕ, r.Prime → ∀ R : Subgroup G, IsSylowOf r R σ.ON →
      σ.T ≤ Subgroup.normalizer (R : Set G) →
        R ≤ Subgroup.centralizer ({σ.x₂} : Set G) ∨ ∀ y ∈ R, σ.x₂ * y * σ.x₂⁻¹ = y⁻¹ :=
    fun r hr R hR hTR => σ.sylow_centralized_or_inverted_of_forall hσ h hr hR hTR
  refine ⟨hi, ?_, ?_⟩
  · obtain ⟨J, hJL, hLJ, hJC, hNJ, halt⟩ := σ.layer_of_centralized_or_inverted hσ hII h h_II_1_1
    refine ⟨J, hJL, hLJ, hJC, hNJ, ?_⟩
    rcases halt with h1 | ⟨h9, h3⟩
    · exact Or.inl h1
    · exact Or.inr ⟨h9, h51 J hJL hLJ hJC hNJ h9 h3, h3⟩
  · have hx₂ON : σ.x₂ ∈ Subgroup.normalizer (σ.ON : Set G) :=
      σ.N_le_normalizer_ON (σ.x₂_mem_N hσ)
    have hdich : ∀ r : ℕ, r.Prime → ∀ R : Subgroup G, IsSylowOf r R σ.ON →
        σ.x₂ ∈ Subgroup.normalizer (R : Set G) →
          R ≤ Subgroup.centralizer ({σ.x₂} : Set G) ∨ ∀ y ∈ R, σ.x₂ * y * σ.x₂⁻¹ = y⁻¹ := by
      intro r hr R hR hx₂R
      refine hi r hr R hR ?_
      rw [T, Subgroup.closure_le]
      rintro t (rfl | rfl)
      · apply Subgroup.centralizer_le_normalizer
        rw [Subgroup.mem_centralizer_iff]
        intro g hg
        exact (σ.mem_N_iff g).mp (σ.ON_le_N (hR.le hg))
      · exact hx₂R
    obtain ⟨B, hBK, hNB, hBinv, hBR⟩ :=
      exists_inverted_hall σ.odd_card_ON hσ.x₂_order hx₂ON hdich
    exact ⟨B, hBK, σ.N_le_normalizer_ON.trans hNB, hBinv,
      fun r hr R hR hTR hinv => hBR r hr R hR (hTR σ.x₂_mem_T) hinv⟩

end Setting

end CFSG.ABGTheoremB
