module

public import CFSG.LocalAnalysis.ComponentClassification.GSThmB82A10TLayer
public import CFSG.LocalAnalysis.ComponentClassification.GSThmBCatalog82A10Perm
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBAlternatingLocal
public import CFSG.ThirdParty.QiuzhenCFSG.Theory.AutAlternating
import CFSG.LocalAnalysis.ComponentClassification.GSThmB8Action
import CFSG.LocalAnalysis.ComponentClassification.GSThmB5aOddQuotTools

public section

namespace CFSG.ComponentClassification.GSThmB.A10T

open CFSG Subgroup Equiv Equiv.Perm CFSG.ComponentClassification.UnbalancedLayer
open CFSG.ComponentClassification.GSThmB.Catalog82A10

variable {X : Type} [Group X] [Finite X]

@[expose] def IsRep {N : Subgroup X} {n : ℕ} (φ : ↥N →* Perm (Fin n)) (M : Subgroup X)
    (A : Subgroup (Perm (Fin n))) : Prop :=
  M ≤ N ∧ (M.subgroupOf N).map φ = A ∧
    ∀ m (hm : m ∈ M) (hmN : m ∈ N), φ ⟨m, hmN⟩ = 1 ↔ m ∈ oddCoreIn M

private theorem fix_of_commute_altOn_of_four {α : Type*} [DecidableEq α] [Fintype α]
    {Δ : Finset α} (hΔ : 4 ≤ Δ.card) {σ : Perm α} (h : ∀ g ∈ altOn Δ, σ * g = g * σ) :
    ∀ i ∈ Δ, σ i = i := by
  intro i hi
  have hcard : 2 < (Δ.erase i).card := by
    rw [Finset.card_erase_of_mem hi]
    omega
  obtain ⟨a, b, c, ha, hb, hc, hab, hac, hbc⟩ := Finset.two_lt_card_iff.mp hcard
  rw [Finset.mem_erase] at ha hb hc
  have key : ∀ x y, x ∈ Δ → y ∈ Δ → x ≠ i → y ≠ i → x ≠ y → σ i = i ∨ σ i = x ∨ σ i = y := by
    intro x y hx hy hxi hyi hxy
    have hnd : [i, x, y].Nodup := by
      simp only [List.nodup_cons, List.mem_cons, List.mem_singleton, List.not_mem_nil,
        or_false, not_or, List.nodup_nil, not_false_eq_true, and_true]
      exact ⟨⟨hxi.symm, hyi.symm⟩, hxy⟩
    have hsupp := support_swap_mul_swap hnd
    have hmem : swap i x * swap x y ∈ altOn Δ := by
      refine mem_altOn.mpr ⟨?_, ?_⟩
      · rw [mem_alternatingGroup, Perm.sign_mul, sign_swap hxi.symm, sign_swap hxy]
        decide
      · rw [hsupp]
        intro z hz
        simp only [Finset.mem_insert, Finset.mem_singleton] at hz
        rcases hz with rfl | rfl | rfl
        · exact hi
        · exact hx
        · exact hy
    have h1 := (Catalog82A10.mem_support_iff_of_commute (h _ hmem) i).mpr (by
      rw [hsupp]; exact Finset.mem_insert_self _ _)
    rw [hsupp] at h1
    simpa only [Finset.mem_insert, Finset.mem_singleton] using h1
  rcases key a b ha.2 hb.2 ha.1 hb.1 hab with h1 | h1 | h1
  · exact h1
  · rcases key b c hb.2 hc.2 hb.1 hc.1 hbc with h2 | h2 | h2
    · exact h2
    · exact absurd (h1.symm.trans h2) hab
    · exact absurd (h1.symm.trans h2) hac
  · rcases key a c ha.2 hc.2 ha.1 hc.1 hac with h2 | h2 | h2
    · exact h2
    · exact absurd (h1.symm.trans h2) hab.symm
    · exact absurd (h1.symm.trans h2) hbc

namespace IsRep

variable {N M : Subgroup X} {n : ℕ} {φ : ↥N →* Perm (Fin n)} {A : Subgroup (Perm (Fin n))}

theorem nonempty_equiv (h : IsRep φ M A) : Nonempty (↥M ⧸ pPrimeCore 2 ↥M ≃* ↥A) := by
  obtain ⟨hMN, hmap, hker⟩ := h
  let f : ↥M →* ↥A := (φ.comp (inclusion hMN)).codRestrict A fun m => by
    rw [← hmap]
    exact ⟨inclusion hMN m, m.2, rfl⟩
  have hf : Function.Surjective f := by
    rintro ⟨a, ha⟩
    rw [← hmap] at ha
    obtain ⟨x, hx, rfl⟩ := ha
    exact ⟨⟨x, hx⟩, rfl⟩
  have hk : f.ker = pPrimeCore 2 ↥M := by
    ext m
    rw [MonoidHom.mem_ker, ← Subtype.coe_inj, OneMemClass.coe_one]
    change φ ⟨m, hMN m.2⟩ = 1 ↔ _
    rw [hker m m.2 (hMN m.2)]
    exact mem_map_iff_mem M.subtype_injective
  exact ⟨(QuotientGroup.quotientMulEquivOfEq hk.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective f hf)⟩

theorem mem_coreActionKernel_iff (h : IsRep φ M A) {g : X} (hgN : g ∈ N)
    (hgM : g ∈ normalizer (M : Set X)) :
    g ∈ coreActionKernel M ↔ ∀ α ∈ A, φ ⟨g, hgN⟩ * α = α * φ ⟨g, hgN⟩ := by
  obtain ⟨hMN, hmap, hker⟩ := h
  have hc : ∀ j ∈ M, j⁻¹ * g⁻¹ * j * g ∈ M := fun j hj => by
    have h1 := (mem_normalizer_iff.mp (inv_mem hgM) j).mp hj
    rw [inv_inv] at h1
    rw [show j⁻¹ * g⁻¹ * j * g = j⁻¹ * (g⁻¹ * j * g) by group]
    exact mul_mem (inv_mem hj) h1
  have hcN : ∀ j ∈ N, j⁻¹ * g⁻¹ * j * g ∈ N := fun j hjN =>
    mul_mem (mul_mem (mul_mem (inv_mem hjN) (inv_mem hgN)) hjN) hgN
  have hφc : ∀ j (hjN : j ∈ N), φ ⟨j⁻¹ * g⁻¹ * j * g, hcN j hjN⟩ =
      (φ ⟨j, hjN⟩)⁻¹ * (φ ⟨g, hgN⟩)⁻¹ * φ ⟨j, hjN⟩ * φ ⟨g, hgN⟩ := fun j hjN => by
    rw [← map_inv, ← map_inv, ← map_mul, ← map_mul, ← map_mul]
    rfl
  rw [mem_coreActionKernel]
  constructor
  · rintro ⟨-, hcore⟩ α hα
    rw [← hmap] at hα
    obtain ⟨⟨j, hjN⟩, hj, rfl⟩ := hα
    have h1 := (hker _ (hc j hj) (hcN j hjN)).mpr (hcore j hj)
    rw [hφc j hjN] at h1
    generalize φ ⟨j, hjN⟩ = a at h1 ⊢
    generalize φ ⟨g, hgN⟩ = b at h1 ⊢
    calc b * a = b * a * (a⁻¹ * b⁻¹ * a * b) := by rw [h1, mul_one]
      _ = a * b := by group
  · intro hcomm
    refine ⟨hgM, fun j hj => (hker _ (hc j hj) (hcN j (hMN hj))).mp ?_⟩
    rw [hφc j (hMN hj)]
    have h1 := hcomm (φ ⟨j, hMN hj⟩) (by rw [← hmap]; exact ⟨⟨j, hMN hj⟩, hj, rfl⟩)
    rw [mul_assoc _ (φ ⟨j, hMN hj⟩), ← h1]
    group

theorem mem_coreActionKernel_iff_eq_one (h : IsRep φ M (alternatingGroup (Fin n))) (hn : 4 ≤ n)
    {g : X} (hgN : g ∈ N) (hgM : g ∈ normalizer (M : Set X)) :
    g ∈ coreActionKernel M ↔ φ ⟨g, hgN⟩ = 1 := by
  rw [h.mem_coreActionKernel_iff hgN hgM]
  constructor
  · intro hc
    apply GroupTheory.AutAlternating.conjNormal_injective_alternatingGroup n hn
    rw [map_one]
    refine MulEquiv.ext fun a => Subtype.ext ?_
    rw [MulAut.conjNormal_apply, hc a a.2, mul_inv_cancel_right]
    rfl
  · intro h1 α _
    rw [h1, one_mul, mul_one]

theorem fix_of_mem_coreActionKernel {Δ : Finset (Fin n)} (h : IsRep φ M (altOn Δ))
    (hΔ : 4 ≤ Δ.card) {g : X} (hgN : g ∈ N) (hgM : g ∈ normalizer (M : Set X))
    (hg : g ∈ coreActionKernel M) : ∀ i ∈ Δ, φ ⟨g, hgN⟩ i = i :=
  fix_of_commute_altOn_of_four hΔ ((h.mem_coreActionKernel_iff hgN hgM).mp hg)

end IsRep

theorem isRep_of_equiv {M : Subgroup X} {n : ℕ} (hn : 5 ≤ n) (hn6 : n ≠ 6)
    (e : ↥M ⧸ pPrimeCore 2 ↥M ≃* alternatingGroup (Fin n)) :
    ∃ φ : ↥(normalizer (M : Set X)) →* Perm (Fin n),
      IsRep φ M (alternatingGroup (Fin n)) ∧
      ∀ g : ↥(normalizer (M : Set X)), φ g = 1 ↔ (g : X) ∈ coreActionKernel M := by
  set cN : Perm (Fin n) ≃* MulAut (alternatingGroup (Fin n)) := MulEquiv.ofBijective
    MulAut.conjNormal (GroupTheory.AutAlternating.aut_alternatingGroup_bijective_conj n hn hn6)
    with hcN
  set θ := Eight.oddBarAction M with hθ
  set φ : ↥(normalizer (M : Set X)) →* Perm (Fin n) :=
    cN.symm.toMonoidHom.comp ((MulAut.congr e).toMonoidHom.comp θ)
  have hφM : ∀ m : ↥M, φ ⟨m, le_normalizer m.2⟩ =
      ((e (m : ↥M ⧸ pPrimeCore 2 ↥M) : alternatingGroup (Fin n)) : Perm (Fin n)) := by
    intro m
    have h1 : MulAut.congr e (θ ⟨m, le_normalizer m.2⟩) =
        MulAut.conj (e (m : ↥M ⧸ pPrimeCore 2 ↥M)) := by
      rw [hθ, Eight.oddBarAction_of_mem]
      refine MulEquiv.ext fun a => ?_
      simp only [MulAut.congr_apply, MulEquiv.trans_apply, MulAut.conj_apply, map_mul, map_inv,
        MulEquiv.apply_symm_apply]
    change cN.symm (MulAut.congr e (θ ⟨m, le_normalizer m.2⟩)) = _
    rw [h1, MulEquiv.symm_apply_eq, hcN, MulEquiv.ofBijective_apply, MulAut.conjNormal_val]
  refine ⟨φ, ⟨le_normalizer, ?_, fun m hm hmN => ?_⟩, fun g => ?_⟩
  · ext σ
    constructor
    · rintro ⟨⟨g, hg⟩, hgM, rfl⟩
      have hgM' : g ∈ M := hgM
      rw [show (⟨g, hg⟩ : ↥(normalizer (M : Set X))) =
        ⟨((⟨g, hgM'⟩ : ↥M) : X), le_normalizer hgM'⟩ from rfl, hφM]
      exact (e _).2
    · intro hσ
      obtain ⟨q, hq⟩ := e.surjective ⟨σ, hσ⟩
      obtain ⟨m, rfl⟩ := QuotientGroup.mk_surjective q
      exact ⟨⟨m, le_normalizer m.2⟩, m.2, by rw [hφM, hq]⟩
  · rw [show (⟨m, hmN⟩ : ↥(normalizer (M : Set X))) =
      ⟨((⟨m, hm⟩ : ↥M) : X), le_normalizer hm⟩ from rfl, hφM, OneMemClass.coe_eq_one,
      map_eq_one_iff _ e.injective, QuotientGroup.eq_one_iff]
    exact (mem_map_iff_mem M.subtype_injective).symm
  · rw [← Eight.mem_ker_oddBarAction, MonoidHom.mem_ker, ← hθ]
    change cN.symm (MulAut.congr e (θ g)) = 1 ↔ θ g = 1
    rw [map_eq_one_iff _ cN.symm.injective, map_eq_one_iff _ (MulAut.congr e).injective]

private theorem inf_centralizer_subgroupOf {N E : Subgroup X} (hE : E ≤ N) (M : Subgroup X) :
    (M ⊓ centralizer (E : Set X)).subgroupOf N =
      M.subgroupOf N ⊓ centralizer ((E.subgroupOf N : Subgroup N) : Set N) := by
  ext ⟨x, hx⟩
  simp only [mem_subgroupOf, mem_inf, mem_centralizer_iff, SetLike.mem_coe]
  constructor
  · rintro ⟨hxM, hxE⟩
    exact ⟨hxM, fun e he => Subtype.ext (hxE e he)⟩
  · rintro ⟨hxM, hxE⟩
    exact ⟨hxM, fun e he => congrArg Subtype.val (hxE ⟨e, hE he⟩ he)⟩

private theorem not_two_dvd_orderOf_of_mem_oddCoreIn {M : Subgroup X} {x : X}
    (hx : x ∈ oddCoreIn M) : ¬ 2 ∣ orderOf x := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨o, ho, rfl⟩ := hx
  intro h2
  have h1 : orderOf (⟨o, ho⟩ : pPrimeCore 2 ↥M) ∣ Nat.card (pPrimeCore 2 ↥M) :=
    orderOf_dvd_natCard _
  rw [Subgroup.orderOf_mk, ← orderOf_injective M.subtype M.subtype_injective o] at h1
  exact (Nat.prime_two.coprime_iff_not_dvd.mp pPrimeCore_coprime_card) (h2.trans h1)

private theorem not_two_dvd_card_of_forall {K : Type*} [Group K] [Finite K]
    (h : ∀ k : K, ¬ 2 ∣ orderOf k) : ¬ 2 ∣ Nat.card K := fun h2 => by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨k, hk⟩ := exists_prime_orderOf_dvd_card' 2 h2
  exact h k (hk ▸ dvd_rfl)

private theorem conj_mem_oddCoreIn {M : Subgroup X} {m x : X} (hm : m ∈ M)
    (hx : x ∈ oddCoreIn M) : m * x * m⁻¹ ∈ oddCoreIn M := by
  obtain ⟨o, ho, rfl⟩ := hx
  exact ⟨⟨m, hm⟩ * o * ⟨m, hm⟩⁻¹, Subgroup.Normal.conj_mem inferInstance o ho _, rfl⟩

private theorem inf_oddCoreIn_le {Y M : Subgroup X} (hYM : Y ≤ M) :
    Y ⊓ oddCoreIn M ≤ oddCoreIn Y := by
  set K : Subgroup ↥Y := (oddCoreIn M).subgroupOf Y with hK
  have hn : K.Normal := ⟨fun k hk y => by
    rw [hK, mem_subgroupOf] at hk ⊢
    exact conj_mem_oddCoreIn (hYM y.2) hk⟩
  have hcop : Nat.Coprime 2 (Nat.card K) := Nat.prime_two.coprime_iff_not_dvd.mpr
    (not_two_dvd_card_of_forall fun k => by
      rw [← Subgroup.orderOf_coe, ← Subgroup.orderOf_coe]
      exact not_two_dvd_orderOf_of_mem_oddCoreIn (mem_subgroupOf.mp k.2))
  have hle : K ≤ pPrimeCore 2 ↥Y := le_sSup ⟨hn, hcop⟩
  rintro x ⟨hxY, hxO⟩
  exact ⟨⟨x, hxY⟩, hle (mem_subgroupOf.mpr hxO), rfl⟩

private theorem le_of_perfect_of_le_sup_odd {A O W : Subgroup X} (hW : Group.IsPerfect W)
    (hO : Odd (Nat.card O)) (hOA : O ≤ normalizer (A : Set X)) (hWle : W ≤ A ⊔ O) : W ≤ A := by
  set J : Subgroup X := A ⊔ O
  have hOJ : O ≤ J := le_sup_right
  have hJA : J ≤ normalizer (A : Set X) := sup_le le_normalizer hOA
  have hAn : (A.subgroupOf J).Normal := by
    rw [normal_subgroupOf_iff le_sup_left]
    exact fun h k hh hk => (mem_normalizer_iff.mp (hJA hk) h).mp hh
  set π : ↥J →* ↥J ⧸ A.subgroupOf J := QuotientGroup.mk' _
  set ψ : ↥W →* ↥J ⧸ A.subgroupOf J := π.comp (inclusion hWle)
  have hrange : ψ.range ≤ (O.subgroupOf J).map π := by
    rintro _ ⟨w, rfl⟩
    have hx : (w : X) ∈ ((A ⊔ O : Subgroup X) : Set X) := hWle w.2
    rw [coe_mul_of_right_le_normalizer_left A O hOA] at hx
    obtain ⟨a, ha, o, ho, hao⟩ := hx
    refine ⟨⟨o, hOJ ho⟩, mem_subgroupOf.mpr ho, ?_⟩
    change π ⟨o, hOJ ho⟩ = π (inclusion hWle w)
    rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq]
    change (o : X)⁻¹ * (w : X) ∈ A
    rw [← hao, show o⁻¹ * (a * o) = o⁻¹ * a * o⁻¹⁻¹ by group]
    exact (mem_normalizer_iff.mp (inv_mem (hOA ho)) a).mp ha
  have hodd : Odd (Nat.card ((O.subgroupOf J).map π)) := by
    refine Odd.of_dvd_nat hO ((card_map_dvd _ _).trans ?_)
    exact (Nat.card_congr (subgroupOfEquivOfLe hOJ).toEquiv).dvd
  have := CFSG.FeitThompson.isSolvable_of_odd_natCard _ hodd
  have hsolv : Group.IsSolvable ψ.range :=
    Group.isSolvable_of_isSolvable_injective (inclusion_injective hrange)
  have : Group.IsPerfect ψ.range :=
    Group.IsPerfect.ofSurjective (f := ψ.rangeRestrict) ψ.rangeRestrict_surjective
  have hbot : ψ.range = ⊥ := by
    by_contra hne
    have : Nontrivial ψ.range := (nontrivial_iff_ne_bot _).mpr hne
    exact Group.IsPerfect.not_isSolvable (G := ψ.range) hsolv
  intro w hw
  have h1 : ψ ⟨w, hw⟩ ∈ ψ.range := ⟨⟨w, hw⟩, rfl⟩
  rw [hbot, mem_bot] at h1
  have h2 : (inclusion hWle ⟨w, hw⟩ : ↥J) ∈ A.subgroupOf J := (QuotientGroup.eq_one_iff _).mp h1
  exact h2

private theorem pPrimeCore_eq_bot_of_two_dvd {S : Type*} [Group S] [IsSimpleGroup S]
    (h2 : 2 ∣ Nat.card S) : pPrimeCore 2 S = ⊥ := by
  refine pPrimeCore_eq_bot_iff.mpr fun K hK hcop => ?_
  refine (@IsSimpleGroup.eq_bot_or_eq_top_of_normal _ _ _ K hK).resolve_right fun htop => ?_
  rw [htop, Subgroup.card_top] at hcop
  exact absurd (Nat.Coprime.eq_one_of_dvd hcop h2) (by norm_num)

private theorem isPComponent_top_of_isSimpleGroup {S : Type*} [Group S] [IsSimpleGroup S]
    (hnonab : ∃ a b : S, a * b ≠ b * a) (hO : pPrimeCore 2 S = ⊥) :
    IsPComponent 2 (⊤ : Subgroup S) := by
  let e : S ⧸ pPrimeCore 2 S ≃* S :=
    (QuotientGroup.quotientMulEquivOfEq hO).trans QuotientGroup.quotientBot
  have : Nontrivial (S ⧸ pPrimeCore 2 S) := e.symm.injective.nontrivial
  refine ⟨⊤, ⟨LocalCores.isQuasisimple_of_mulEquiv (e.symm.trans Subgroup.topEquiv.symm)
    (LocalCores.isQuasisimple_of_isSimpleGroup hnonab).1, Subgroup.IsSubnormal.top⟩,
    Subgroup.IsSubnormal.top, Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective _),
    fun J hJ hJsub hJmap => ?_⟩
  rcases Subgroup.IsSubnormal.eq_bot_or_top_of_isSimpleGroup inferInstance hJsub with rfl | rfl
  · rw [Subgroup.map_bot] at hJmap
    exact bot_ne_top hJmap
  · exact lt_irrefl _ hJ

section AltOn

variable {α : Type*} [DecidableEq α] [Fintype α]

private theorem two_dvd_card_altOn {Δ : Finset α} (hΔ : 4 ≤ Δ.card) :
    2 ∣ Nat.card (altOn Δ) := by
  rw [card_altOn Δ (by omega)]
  obtain ⟨m, hm⟩ := Nat.factorial_dvd_factorial hΔ
  rw [hm, show Nat.factorial 4 = 24 from rfl]
  omega

private theorem exists_mul_ne_mul_altOn {Δ : Finset α} (hΔ : 4 ≤ Δ.card) :
    ∃ a b : altOn Δ, a * b ≠ b * a := by
  have h4 : 4 ≤ Nat.card Δ := by rw [Nat.card_eq_fintype_card, Fintype.card_coe]; exact hΔ
  have : Nontrivial (alternatingGroup Δ) :=
    alternatingGroup.nontrivial_of_three_le_card (by omega)
  by_contra h
  push Not at h
  have hZ : center (alternatingGroup Δ) = ⊤ := eq_top_iff.2 fun a _ => mem_center_iff.2 fun b => by
    have h1 := h (altOnEquiv Δ b) (altOnEquiv Δ a)
    rw [← map_mul, ← map_mul] at h1
    exact (altOnEquiv Δ).injective h1
  rw [alternatingGroup.center_eq_bot h4] at hZ
  exact bot_ne_top hZ

private theorem isPComponent_top_altOn {Δ : Finset α} (h5 : 5 ≤ Δ.card) :
    IsPComponent 2 (⊤ : Subgroup (altOn Δ)) := by
  have := isSimpleGroup_altOn Δ h5
  exact isPComponent_top_of_isSimpleGroup (exists_mul_ne_mul_altOn (by omega))
    (pPrimeCore_eq_bot_of_two_dvd (two_dvd_card_altOn (by omega)))

end AltOn

private theorem altOn_isPComponent {n : ℕ} {P F : Subgroup (Perm (Fin n))}
    (hF : F = alternatingGroup (Fin n) ⊓ centralizer (P : Set (Perm (Fin n))))
    {Δ : Finset (Fin n)} (hΔ : ∀ i, (∀ p ∈ P, p i = i) ↔ i ∈ Δ) (h5 : 5 ≤ Δ.card) :
    altOn Δ ≤ F ∧ IsPComponent 2 ((altOn Δ).subgroupOf F) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  subst hF
  have hpres : ∀ f ∈ alternatingGroup (Fin n) ⊓ centralizer (P : Set (Perm (Fin n))),
      ∀ i ∈ Δ, f i ∈ Δ := by
    intro f hf i hi
    refine (hΔ _).mp fun p hp => ?_
    have h1 := mem_centralizer_iff.mp (mem_inf.mp hf).2 p hp
    rw [← Perm.mul_apply, h1, Perm.mul_apply, (hΔ i).mpr hi p hp]
  have hle : altOn Δ ≤ alternatingGroup (Fin n) ⊓ centralizer (P : Set (Perm (Fin n))) := by
    intro g hg
    obtain ⟨hgA, hgS⟩ := mem_altOn.mp hg
    refine mem_inf.mpr ⟨hgA, mem_centralizer_iff.mpr fun p hp => ?_⟩
    have hdisj : Perm.Disjoint p g := by
      intro x
      by_cases hx : x ∈ Δ
      · exact .inl ((hΔ x).mpr hx p hp)
      · exact .inr (Perm.notMem_support.mp fun h => hx (hgS h))
    exact hdisj.commute.eq
  have hconj : ∀ f ∈ alternatingGroup (Fin n) ⊓ centralizer (P : Set (Perm (Fin n))),
      ∀ g ∈ altOn Δ, f * g * f⁻¹ ∈ altOn Δ := by
    intro f hf g hg
    obtain ⟨hgA, hgS⟩ := mem_altOn.mp hg
    refine mem_altOn.mpr ⟨(alternatingGroup.normal (α := Fin n)).conj_mem g hgA f, ?_⟩
    rw [Perm.support_conj]
    intro x hx
    obtain ⟨y, hy, rfl⟩ := Finset.mem_map.mp hx
    exact hpres f hf y (hgS hy)
  have hn : ((altOn Δ).subgroupOf
      (alternatingGroup (Fin n) ⊓ centralizer (P : Set (Perm (Fin n))))).Normal := by
    refine (normal_subgroupOf_iff_le_normalizer hle).mpr fun f hf =>
      mem_normalizer_iff.mpr fun g => ⟨hconj f hf g, fun h => ?_⟩
    have h1 := hconj f⁻¹ (inv_mem hf) _ h
    rwa [show f⁻¹ * (f * g * f⁻¹) * f⁻¹⁻¹ = g by group] at h1
  refine ⟨hle, (CatalogueBPrimeJoin.pComponent_subgroupOf_iff_of_subnormal le_rfl hle
    hn.isSubnormal).mpr ?_⟩
  rw [subgroupOf_self]
  exact isPComponent_top_altOn h5

private theorem eq_altOn_of_isPComponent {n : ℕ} {P F : Subgroup (Perm (Fin n))}
    (hP : IsPGroup 2 P)
    (hF : F = alternatingGroup (Fin n) ⊓ centralizer (P : Set (Perm (Fin n))))
    {Δ : Finset (Fin n)} (hΔ : ∀ i, (∀ p ∈ P, p i = i) ↔ i ∈ Δ) {W : Subgroup (Perm (Fin n))}
    (hWF : W ≤ F) (hW : IsPComponent 2 (W.subgroupOf F)) : 5 ≤ Δ.card ∧ W = altOn Δ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set Nq := normalizer (P : Set (Perm (Fin n)))
  have hFN : F ≤ Nq := hF ▸ inf_le_right.trans (centralizer_le_normalizer _)
  have hFn : (F.subgroupOf Nq).Normal := by
    refine (normal_subgroupOf_iff_le_normalizer hFN).mpr ?_
    rw [hF]
    exact (le_inf le_normalizer_of_normal
      (CatalogueBPrimeJoin.normalizer_le_normalizer_centralizer P)).trans
      inf_normalizer_le_normalizer_inf
  have h1 := (CatalogueBPrimeJoin.pComponent_subgroupOf_iff_of_subnormal hWF hFN
    hFn.isSubnormal).mpr hW
  obtain ⟨h5', hWeq, -⟩ := CatalogueBAlternating.symmetric_normalizer_pComponent 2 P hP _ h1
  have hcard : Nat.card (MulAction.fixedPoints P (Fin n)) = Δ.card := by
    have hset : MulAction.fixedPoints P (Fin n) = (Δ : Set (Fin n)) := by
      ext i
      rw [MulAction.mem_fixedPoints, Finset.mem_coe, ← hΔ]
      exact ⟨fun h p hp => h ⟨p, hp⟩, fun h p => h p p.2⟩
    rw [hset, Nat.card_coe_set_eq, Set.ncard_coe_finset]
  have h5 : 5 ≤ Δ.card := hcard ▸ h5'
  obtain ⟨hle, hA⟩ := altOn_isPComponent hF hΔ h5
  have h3 := (CatalogueBPrimeJoin.pComponent_subgroupOf_iff_of_subnormal hle hFN
    hFn.isSubnormal).mpr hA
  obtain ⟨-, hAeq, -⟩ := CatalogueBAlternating.symmetric_normalizer_pComponent 2 P hP _ h3
  refine ⟨h5, ?_⟩
  have h2 : W.subgroupOf Nq = (altOn Δ).subgroupOf Nq := hWeq.trans hAeq.symm
  rwa [subgroupOf_inj, inf_of_le_left (hWF.trans hFN), inf_of_le_left (hle.trans hFN)] at h2

private theorem isRep_altOn_of_map_eq {N M Y : Subgroup X} {n : ℕ} {φ : ↥N →* Perm (Fin n)}
    (hφ : IsRep φ M (alternatingGroup (Fin n))) (hYM : Y ≤ M) {Δ : Finset (Fin n)}
    (h5 : 5 ≤ Δ.card) (hY : (Y.subgroupOf N).map φ = altOn Δ) : IsRep φ Y (altOn Δ) := by
  obtain ⟨hMN, -, hker⟩ := hφ
  refine ⟨hYM.trans hMN, hY, fun y hy hyN => ⟨fun h1 => inf_oddCoreIn_le hYM
    ⟨hy, (hker y (hYM hy) hyN).mp h1⟩, fun h1 => ?_⟩⟩
  have hOY : oddCoreIn Y ≤ Y := map_subtype_le _
  set K := ((oddCoreIn Y).subgroupOf N).map φ
  have hKA : K ≤ altOn Δ := by
    rw [← hY]
    exact map_mono fun x hx => hOY hx
  set K' : Subgroup ↥(altOn Δ) := K.subgroupOf (altOn Δ) with hK'
  have hn : K'.Normal := ⟨fun k hk g => by
    rw [hK', mem_subgroupOf] at hk ⊢
    obtain ⟨x, hx, hxk⟩ := hk
    have hg : (g : Perm (Fin n)) ∈ (Y.subgroupOf N).map φ := by
      rw [hY]
      exact g.2
    obtain ⟨y', hy', hy'g⟩ := hg
    refine ⟨y' * x * y'⁻¹, ?_, ?_⟩
    · exact conj_mem_oddCoreIn (mem_subgroupOf.mp hy') (mem_subgroupOf.mp hx)
    · rw [map_mul, map_mul, map_inv, hxk, hy'g]
      rfl⟩
  have hcop : Nat.Coprime 2 (Nat.card K') := Nat.prime_two.coprime_iff_not_dvd.mpr
    (not_two_dvd_card_of_forall fun k h2 => by
      rw [← Subgroup.orderOf_coe, ← Subgroup.orderOf_coe] at h2
      obtain ⟨x, hx, hxk⟩ := mem_subgroupOf.mp k.2
      rw [← hxk] at h2
      have h3 := h2.trans (orderOf_map_dvd φ x)
      rw [← Subgroup.orderOf_coe] at h3
      exact not_two_dvd_orderOf_of_mem_oddCoreIn (mem_subgroupOf.mp hx) h3)
  have hbot : K' = ⊥ := by
    have hle : K' ≤ pPrimeCore 2 ↥(altOn Δ) := le_sSup ⟨hn, hcop⟩
    have := isSimpleGroup_altOn Δ h5
    rwa [pPrimeCore_eq_bot_of_two_dvd (two_dvd_card_altOn (by omega)), le_bot_iff] at hle
  have hmem : φ ⟨y, hyN⟩ ∈ K := ⟨⟨y, hyN⟩, h1, rfl⟩
  have h2 : (⟨φ ⟨y, hyN⟩, hKA hmem⟩ : altOn Δ) ∈ K' := hmem
  rw [hbot, mem_bot] at h2
  exact congrArg Subtype.val h2

private theorem natural_aux {N M E : Subgroup X} {n : ℕ} {φ : ↥N →* Perm (Fin n)}
    (hφ : IsRep φ M (alternatingGroup (Fin n))) (hEN : E ≤ N)
    (hEM : E ≤ normalizer (M : Set X)) (hE : IsPGroup 2 E) {Δ : Finset (Fin n)}
    (hΔ : ∀ i, (∀ e (he : e ∈ E), φ ⟨e, hEN he⟩ i = i) ↔ i ∈ Δ) :
    (∀ Y : Subgroup X, Y ≤ M ⊓ centralizer (E : Set X) →
        IsPComponent 2 (Y.subgroupOf (M ⊓ centralizer (E : Set X))) →
        5 ≤ Δ.card ∧ (Y.subgroupOf N).map φ = altOn Δ) ∧
    (5 ≤ Δ.card → ∃ Y : Subgroup X, Y ≤ M ⊓ centralizer (E : Set X) ∧
        IsPComponent 2 (Y.subgroupOf (M ⊓ centralizer (E : Set X))) ∧
        (Y.subgroupOf N).map φ = altOn Δ) ∧
    (∀ Y₁ Y₂ : Subgroup X, Y₁ ≤ M ⊓ centralizer (E : Set X) →
        Y₂ ≤ M ⊓ centralizer (E : Set X) →
        IsPComponent 2 (Y₁.subgroupOf (M ⊓ centralizer (E : Set X))) →
        IsPComponent 2 (Y₂.subgroupOf (M ⊓ centralizer (E : Set X))) →
        (Y₁.subgroupOf N).map φ = (Y₂.subgroupOf N).map φ → Y₁ = Y₂) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hMN, hmap, hker⟩ := hφ
  set C := M ⊓ centralizer (E : Set X) with hC
  have hCN : C ≤ N := inf_le_left.trans hMN
  set C₁ := C.subgroupOf N with hC₁
  set E₁ := E.subgroupOf N
  set P := E₁.map φ
  set T := C₁.map φ with hT
  have hE₁ : IsPGroup 2 E₁ := hE.of_equiv (subgroupOfEquivOfLe hEN).symm
  have hE₁M₁ : E₁ ≤ normalizer ((M.subgroupOf N : Subgroup N) : Set N) := fun e he =>
    mem_normalizer_iff.mpr fun h => mem_normalizer_iff.mp (hEM he) h
  have hkerM : ∀ x : ↥N, (x : X) ∈ M → φ x = 1 → ¬ 2 ∣ orderOf x := fun x hx h1 => by
    rw [← Subgroup.orderOf_coe]
    exact not_two_dvd_orderOf_of_mem_oddCoreIn ((hker x hx x.2).mp h1)
  have hkerM₁ : ¬ 2 ∣ Nat.card (φ.domRestrict (M.subgroupOf N)).ker :=
    not_two_dvd_card_of_forall fun k => by
      rw [← Subgroup.orderOf_coe, ← Subgroup.orderOf_coe]
      exact hkerM _ (k : M.subgroupOf N).2 k.2
  have hTF : T = alternatingGroup (Fin n) ⊓ centralizer (P : Set (Perm (Fin n))) := by
    rw [hT, hC₁, hC, inf_centralizer_subgroupOf hEN M, ← hmap]
    exact OddQuot.map_inf_centralizer φ hE₁ hE₁M₁ hkerM₁
  have hP2 : IsPGroup 2 P := hE₁.map φ
  have hPΔ : ∀ i, (∀ p ∈ P, p i = i) ↔ i ∈ Δ := by
    intro i
    rw [← hΔ]
    constructor
    · intro h e he
      exact h _ ⟨⟨e, hEN he⟩, he, rfl⟩
    · rintro h _ ⟨e₁, he₁, rfl⟩
      exact h e₁ he₁
  set ψ := φ.subgroupMap C₁
  have hψk : ¬ 2 ∣ Nat.card ψ.ker := not_two_dvd_card_of_forall fun k => by
    rw [← Subgroup.orderOf_coe, ← Subgroup.orderOf_coe]
    exact hkerM _ (mem_inf.mp (mem_subgroupOf.mp (k : C₁).2)).1 (congrArg Subtype.val k.2)
  obtain ⟨hbij, -, -⟩ := CatalogueBPrimeJoin.prime_complement_quotient_p_component_bijection ψ
    (φ.subgroupMap_surjective C₁) hψk
  have htr : ∀ Y : Subgroup X, IsPComponent 2 ((Y.subgroupOf N).subgroupOf C₁) ↔
      IsPComponent 2 (Y.subgroupOf C) := fun Y =>
    UnbalancedCorr.isPComponent_subgroupOf_subgroupOf_iff' hCN 2 Nat.prime_two
  have himg : ∀ Y : Subgroup X, Y ≤ C →
      ((Y.subgroupOf N).subgroupOf C₁).map ψ = ((Y.subgroupOf N).map φ).subgroupOf T :=
    fun Y hY => OddQuot.map_subgroupOf_subgroupMap φ fun x hx => hY hx
  have hle : ∀ Y : Subgroup X, Y ≤ C → (Y.subgroupOf N).map φ ≤ T :=
    fun Y hY => map_mono fun x hx => hY hx
  have heq : ∀ Y₁ Y₂ : Subgroup X, Y₁ ≤ N → Y₂ ≤ N →
      (Y₁.subgroupOf N).subgroupOf C₁ = (Y₂.subgroupOf N).subgroupOf C₁ →
      Y₁.subgroupOf N ≤ C₁ → Y₂.subgroupOf N ≤ C₁ → Y₁ = Y₂ := by
    intro Y₁ Y₂ h1 h2 h h1' h2'
    rw [subgroupOf_inj, inf_of_le_left h1', inf_of_le_left h2', subgroupOf_inj,
      inf_of_le_left h1, inf_of_le_left h2] at h
    exact h
  refine ⟨fun Y hYC hY => ?_, fun h5 => ?_, fun Y₁ Y₂ hY₁ hY₂ hc₁ hc₂ h => ?_⟩
  · have h1 := hbij.mapsTo ((htr Y).mpr hY)
    rw [Set.mem_setOf_eq, himg Y hYC] at h1
    exact eq_altOn_of_isPComponent hP2 hTF hPΔ (hle Y hYC) h1
  · obtain ⟨hAT, hA⟩ := altOn_isPComponent hTF hPΔ h5
    obtain ⟨L, hL, hLA⟩ := hbij.surjOn hA
    replace hLA : L.map ψ = (altOn Δ).subgroupOf T := hLA
    set Y : Subgroup X := (L.map C₁.subtype).map N.subtype
    have hYN : Y.subgroupOf N = L.map C₁.subtype :=
      comap_map_eq_self_of_injective N.subtype_injective _
    have hYL : (Y.subgroupOf N).subgroupOf C₁ = L := by
      rw [hYN]
      exact comap_map_eq_self_of_injective C₁.subtype_injective _
    have hYC : Y ≤ C := by
      rintro _ ⟨_, ⟨l, -, rfl⟩, rfl⟩
      exact l.2
    refine ⟨Y, hYC, (htr Y).mp (hYL ▸ hL), ?_⟩
    have h1 := himg Y hYC
    rw [hYL, hLA, subgroupOf_inj, inf_of_le_left hAT, inf_of_le_left (hle Y hYC)] at h1
    exact h1.symm
  · have h1 := hbij.injOn ((htr Y₁).mpr hc₁) ((htr Y₂).mpr hc₂)
      (by rw [himg Y₁ hY₁, himg Y₂ hY₂, h])
    exact heq Y₁ Y₂ (hY₁.trans hCN) (hY₂.trans hCN) h1 (fun x hx => hY₁ hx)
      (fun x hx => hY₂ hx)

theorem exists_natural_component {N M E : Subgroup X} {n : ℕ} {φ : ↥N →* Perm (Fin n)}
    (hφ : IsRep φ M (alternatingGroup (Fin n))) (hEN : E ≤ N)
    (hEM : E ≤ normalizer (M : Set X)) (hE : IsPGroup 2 E) {Δ : Finset (Fin n)}
    (hΔ : ∀ i, (∀ e (he : e ∈ E), φ ⟨e, hEN he⟩ i = i) ↔ i ∈ Δ) (h5 : 5 ≤ Δ.card) :
    ∃ Y : Subgroup X, Y ≤ M ⊓ centralizer (E : Set X) ∧
      IsPComponent 2 (Y.subgroupOf (M ⊓ centralizer (E : Set X))) ∧
      IsRep φ Y (altOn Δ) ∧
      (∀ W : Subgroup X, W ≤ M ⊓ centralizer (E : Set X) → Group.IsPerfect W →
        (W.subgroupOf N).map φ ≤ altOn Δ → W ≤ Y) ∧
      (∀ Y' : Subgroup X, Y' ≤ M ⊓ centralizer (E : Set X) →
        IsPComponent 2 (Y'.subgroupOf (M ⊓ centralizer (E : Set X))) → Y' = Y) ∧
      N ⊓ normalizer (M : Set X) ⊓ normalizer (E : Set X) ≤ normalizer (Y : Set X) := by
  obtain ⟨h1, h2, h3⟩ := natural_aux hφ hEN hEM hE hΔ
  set C := M ⊓ centralizer (E : Set X)
  obtain ⟨Y, hYC, hY, hYimg⟩ := h2 h5
  have huniq : ∀ Y' : Subgroup X, Y' ≤ C → IsPComponent 2 (Y'.subgroupOf C) → Y' = Y :=
    fun Y' hY'C hY' => h3 Y' Y hY'C hYC hY' hY ((h1 Y' hY'C hY').2.trans hYimg.symm)
  have hnorm : ∀ g ∈ normalizer (C : Set X), g ∈ normalizer (Y : Set X) := by
    intro g hgC
    set c : MulAut ↥C := C.normalizerMonoidHom ⟨g, hgC⟩
    have hYgC : Y.map (MulAut.conj g) ≤ C := by
      rintro _ ⟨y, hy, rfl⟩
      exact (mem_normalizer_iff.mp hgC y).mp (hYC hy)
    have hmap : (Y.subgroupOf C).map c.toMonoidHom = (Y.map (MulAut.conj g)).subgroupOf C := by
      ext ⟨x, hx⟩
      rw [mem_map, mem_subgroupOf, mem_map]
      constructor
      · rintro ⟨⟨y, hyC⟩, hy, hyx⟩
        exact ⟨y, hy, congrArg Subtype.val hyx⟩
      · rintro ⟨y, hy, hyx⟩
        exact ⟨⟨y, hYC hy⟩, hy, Subtype.ext hyx⟩
    have hY' := CatalogueBAlternating.pComponent_map_equiv 2 c (Y.subgroupOf C) hY
    rw [hmap] at hY'
    exact mem_normalizer_iff_map_conj_eq.mpr (huniq _ hYgC hY')
  refine ⟨Y, hYC, hY, isRep_altOn_of_map_eq hφ (hYC.trans inf_le_left) h5 hYimg,
    fun W hWC hWp hWimg => ?_, huniq, fun g hg => hnorm g (inf_normalizer_le_normalizer_inf
      ⟨(mem_inf.mp (mem_inf.mp hg).1).2,
        CatalogueBPrimeJoin.normalizer_le_normalizer_centralizer E (mem_inf.mp hg).2⟩)⟩
  have hMN := hφ.1
  have hker := hφ.2.2
  set K : Subgroup X := C ⊓ φ.ker.map N.subtype
  have hKY : K ≤ normalizer (Y : Set X) := fun k hk => hnorm k (le_normalizer hk.1)
  have hKodd : Odd (Nat.card K) := Nat.odd_iff.mpr (Nat.two_dvd_ne_zero.mp
    (not_two_dvd_card_of_forall fun k => by
      obtain ⟨hkC, x, hx, hxk⟩ := k.2
      have hxk' : (x : X) = k := hxk
      rw [← Subgroup.orderOf_coe, ← hxk']
      have hxM : (x : X) ∈ M := by
        rw [hxk']
        exact (mem_inf.mp hkC).1
      exact not_two_dvd_orderOf_of_mem_oddCoreIn ((hker x hxM x.2).mp hx)))
  refine le_of_perfect_of_le_sup_odd hWp hKodd hKY fun w hw => ?_
  have hwN : w ∈ N := hMN (mem_inf.mp (hWC hw)).1
  have hwA : φ ⟨w, hwN⟩ ∈ (Y.subgroupOf N).map φ := hYimg ▸ hWimg ⟨⟨w, hwN⟩, hw, rfl⟩
  obtain ⟨y, hy, hyw⟩ := hwA
  have hk : y⁻¹ * ⟨w, hwN⟩ ∈ φ.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, hyw, inv_mul_cancel]
  have hyY : (y : X) ∈ Y := mem_subgroupOf.mp hy
  have hyw' : (y : X)⁻¹ * w ∈ K :=
    mem_inf.mpr ⟨mul_mem (inv_mem (hYC hyY)) (hWC hw), y⁻¹ * ⟨w, hwN⟩, hk, rfl⟩
  have h1 : (y : X) * ((y : X)⁻¹ * w) ∈ Y ⊔ K :=
    mul_mem (mem_sup_left hyY) (mem_sup_right hyw')
  rwa [mul_inv_cancel_left] at h1

theorem isRep_of_pComponent {N M E : Subgroup X} {n : ℕ} {φ : ↥N →* Perm (Fin n)}
    (hφ : IsRep φ M (alternatingGroup (Fin n))) (hEN : E ≤ N)
    (hEM : E ≤ normalizer (M : Set X)) (hE : IsPGroup 2 E) {Δ : Finset (Fin n)}
    (hΔ : ∀ i, (∀ e (he : e ∈ E), φ ⟨e, hEN he⟩ i = i) ↔ i ∈ Δ) {Y : Subgroup X}
    (hYC : Y ≤ M ⊓ centralizer (E : Set X))
    (hY : IsPComponent 2 (Y.subgroupOf (M ⊓ centralizer (E : Set X)))) :
    5 ≤ Δ.card ∧ IsRep φ Y (altOn Δ) := by
  obtain ⟨h5, himg⟩ := (natural_aux hφ hEN hEM hE hΔ).1 Y hYC hY
  exact ⟨h5, isRep_altOn_of_map_eq hφ (hYC.trans inf_le_left) h5 himg⟩

end CFSG.ComponentClassification.GSThmB.A10T
