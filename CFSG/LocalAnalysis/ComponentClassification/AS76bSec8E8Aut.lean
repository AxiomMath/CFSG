module

public import CFSG.LocalAnalysis.ComponentClassification.AS76bSec8E8Torus
public import CFSG.LocalAnalysis.ComponentClassification.AS76bSec8D4Aut
public import CFSG.LieType.Chevalley.ExceptionalG2F4ModelSchreier

public section

namespace CFSG.ComponentClassification.RankTwoExceptional.E8

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open CFSG.SeitzReduction (highRoot isRoot_highRoot)

variable {K : Type} [Field K]

theorem odd_card_of_forall_pow_eq_one {G : Type*} [Group G] [Finite G] {N : ℕ} (hN : Odd N)
    (h : ∀ g : G, g ^ N = 1) : Odd (Nat.card G) := by
  by_contra hne
  rw [Nat.not_odd_iff_even, even_iff_two_dvd] at hne
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card' 2 hne
  have h2 : orderOf g ∣ N := orderOf_dvd_of_pow_eq_one (h g)
  rw [hg] at h2
  exact (Nat.not_even_iff_odd.2 hN) (even_iff_two_dvd.2 h2)

theorem odd_card_torusGroup_e8
    [Finite K] {m : ℕ} (hm : 1 ≤ m) (hK : Nat.card K = 2 ^ m) :
    Odd (Nat.card (torusGroup .E8 K)) := by
  have : Finite (ModGL .E8 K) := finite_modGL
  exact odd_card_of_forall_pow_eq_one (odd_card_units_e8 hm hK) fun g =>
    Subtype.ext (by
      rw [Subgroup.coe_pow, Subgroup.coe_one]
      exact pow_card_units_eq_one_of_mem_torusGroup g.2)

theorem odd_card_e8T
    [Finite K] {m : ℕ} (hm : 1 ≤ m) (hK : Nat.card K = 2 ^ m) :
    Odd (Nat.card (e8T K)) := by
  have : Finite (ModGL .E8 K) := finite_modGL
  exact odd_card_of_forall_pow_eq_one (odd_card_units_e8 hm hK) fun g =>
    Subtype.ext (Subtype.ext (by
      rw [Subgroup.coe_pow, Subgroup.coe_pow, Subgroup.coe_one, Subgroup.coe_one]
      exact pow_card_units_eq_one_of_mem_torusGroup g.2))

theorem four_le_card_e8 [Finite K] {m : ℕ} (hK : Nat.card K = 2 ^ m) (hq : 2 < 2 ^ m) :
    4 ≤ Nat.card K := by
  have h := three_le_card_units_e8 hK hq
  rw [Nat.card_units] at h
  omega

theorem e8_leviData
    [Finite K] {m : ℕ} (hm : 1 ≤ m) (hK : Nat.card K = 2 ^ m) (hq : 2 < 2 ^ m)
    {Z : Subgroup (adjointGroup .E8 K)} (hZ : Z ≤ e8L K) :
    Exc.LeviData Z (e8D K) (e8Q K) (e8T K) (e8L K) where
  D_perfect := commutator_e8D (four_le_card_e8 hK hq)
  D_le := e8D_le_centralizer_e8L.trans (Subgroup.centralizer_le hZ)
  Q_le := e8Q_le_e8D
  Q_ne_bot := e8Q_ne_bot hK hq
  odd_Q := odd_card_e8Q hm hK
  Q_le_H := e8Q_le_e8T
  H_comm := e8T_comm
  H_le := e8T_le_normalizer_e8L
  L_le := e8L_le_centralizer_e8Q
  cent_eq := exists_mem_e8T_inv_mul_mem_e8L hK hq
  quasisimple := (e8L_recognition hm hK).1
  odd_center := odd_card_center_e8L hm hK
  Z_le := hZ

theorem ncard_posRoots_E8_le :
    {α : Fin Tag.E8.rank → ℤ | IsRoot .E8 α ∧ 0 < height α}.ncard ≤ 120 := by
  set t := (Tag.artifactRoots .E8).filter fun l => decide (0 < l.sum) with htdef
  have ht : t.length = 120 := by
    rw [htdef]
    decide +kernel
  have hmaps : ∀ α ∈ {α : Fin Tag.E8.rank → ℤ | IsRoot .E8 α ∧ 0 < height α},
      List.ofFn α ∈ ((t.toFinset : Finset (List ℤ)) : Set (List ℤ)) := by
    rintro α ⟨hr, hpos⟩
    simp only [Finset.mem_coe, List.mem_toFinset, htdef, List.mem_filter, decide_eq_true_eq]
    refine ⟨isRoot_iff_mem_artifactRoots.1 hr, ?_⟩
    rw [List.sum_ofFn]
    exact hpos
  calc _ ≤ ((t.toFinset : Finset (List ℤ)) : Set (List ℤ)).ncard :=
        Set.ncard_le_ncard_of_injOn List.ofFn hmaps List.ofFn_injective.injOn
          (Finset.finite_toSet _)
    _ = t.toFinset.card := Set.ncard_coe_finset _
    _ ≤ t.length := List.toFinset_card_le t
    _ = 120 := ht

@[expose] def e8E7PosRootLists : List (List ℤ) :=
  (Tag.artifactRoots .E8).filter fun l => decide (0 < l.sum) && decide (l.getD 7 0 = 0)

theorem e8E7PosRootLists_spec : e8E7PosRootLists.length = 63 ∧ e8E7PosRootLists.Nodup ∧
    ∀ l ∈ e8E7PosRootLists, l.length = 8 := by
  decide +kernel

@[expose] def e8ListVec (l : List ℤ) : Fin Tag.E8.rank → ℤ := fun i => l.getD i.val 0

theorem ofFn_e8ListVec {l : List ℤ} (hl : l.length = 8) : List.ofFn (e8ListVec l) = l := by
  refine List.ext_getElem (by rw [List.length_ofFn, hl]; rfl) fun n h₁ h₂ => ?_
  rw [List.getElem_ofFn, e8ListVec, List.getD_eq_getElem _ _ h₂]

theorem le_ncard_parabolicPosRoots_e8 :
    63 ≤ (parabolicPosRoots .E8 e8LeviNodes).ncard := by
  obtain ⟨hl, hnd, hlen⟩ := e8E7PosRootLists_spec
  have hmaps : ∀ l ∈ ((e8E7PosRootLists.toFinset : Finset (List ℤ)) : Set (List ℤ)),
      e8ListVec l ∈ parabolicPosRoots .E8 e8LeviNodes := by
    intro l hl'
    rw [Finset.mem_coe, List.mem_toFinset] at hl'
    have h8 := hlen l hl'
    have hmem := hl'
    simp only [e8E7PosRootLists, List.mem_filter, Bool.and_eq_true, decide_eq_true_eq] at hmem
    obtain ⟨h1, h2, h3⟩ := hmem
    have hr : IsRoot .E8 (e8ListVec l) := by
      rw [isRoot_iff_mem_artifactRoots, ofFn_e8ListVec h8]
      exact h1
    refine ⟨⟨hr, fun i hi => ?_⟩, hr, ?_⟩
    · have hi7 : i = e8Top := by simpa [e8LeviNodes] using hi
      rw [hi7]
      exact h3
    · have h4 : height (e8ListVec l) = (List.ofFn (e8ListVec l)).sum := by
        rw [List.sum_ofFn]
        rfl
      rw [h4, ofFn_e8ListVec h8]
      exact h2
  have hinj : Set.InjOn e8ListVec
      ((e8E7PosRootLists.toFinset : Finset (List ℤ)) : Set (List ℤ)) := by
    intro l₁ h₁ l₂ h₂ he
    rw [Finset.mem_coe, List.mem_toFinset] at h₁ h₂
    rw [← ofFn_e8ListVec (hlen l₁ h₁), ← ofFn_e8ListVec (hlen l₂ h₂), he]
  calc 63 = e8E7PosRootLists.toFinset.card := by rw [List.toFinset_card_of_nodup hnd, hl]
    _ = ((e8E7PosRootLists.toFinset : Finset (List ℤ)) : Set (List ℤ)).ncard :=
        (Set.ncard_coe_finset _).symm
    _ ≤ _ := Set.ncard_le_ncard_of_injOn e8ListVec hmaps hinj
        ((finite_setOf_isRoot .E8).subset fun v hv => hv.1.1)

theorem not_two_pow_dvd_card_adjointGroup_e8
    {K₀ : Type} [Field K₀] [Finite K₀] {e : ℕ} (he : 1 ≤ e) (hK₀ : Nat.card K₀ = 2 ^ e) :
    ¬ 2 ^ (121 * e) ∣ Nat.card (adjointGroup .E8 K₀) := by
  classical
  intro hdvd
  rw [card_adjointGroup] at hdvd
  have : Fintype (WeylGroup .E8) := Fintype.ofFinite _
  have hT := odd_card_torusGroup_e8 he hK₀
  have hS : Odd (∑ᶠ w : WeylGroup .E8, Nat.card K₀ ^ (coxeterSystem .E8).length w) := by
    rw [finsum_eq_sum_of_fintype, ← Finset.add_sum_erase _ _ (Finset.mem_univ 1),
      CoxeterSystem.length_one, pow_zero]
    refine Even.one_add (Finset.even_sum _ fun w hw => ?_)
    have hl : (coxeterSystem .E8).length w ≠ 0 := fun h =>
      Finset.ne_of_mem_erase hw ((coxeterSystem .E8).length_eq_zero_iff.1 h)
    rw [hK₀]
    exact Nat.even_pow.2 ⟨Nat.even_pow.2 ⟨even_two, by omega⟩, hl⟩
  have hcop : Nat.Coprime (2 ^ (121 * e)) (Nat.card (torusGroup .E8 K₀) *
      ∑ᶠ w : WeylGroup .E8, Nat.card K₀ ^ (coxeterSystem .E8).length w) :=
    Nat.Coprime.pow_left _ (Nat.coprime_two_left.2 (hT.mul hS))
  rw [show Nat.card (torusGroup .E8 K₀) *
      Nat.card K₀ ^ {α : Fin Tag.E8.rank → ℤ | IsRoot .E8 α ∧ 0 < height α}.ncard *
        ∑ᶠ w : WeylGroup .E8, Nat.card K₀ ^ (coxeterSystem .E8).length w =
      Nat.card K₀ ^ {α : Fin Tag.E8.rank → ℤ | IsRoot .E8 α ∧ 0 < height α}.ncard *
        (Nat.card (torusGroup .E8 K₀) *
          ∑ᶠ w : WeylGroup .E8, Nat.card K₀ ^ (coxeterSystem .E8).length w) by ring] at hdvd
  have h1 := hcop.dvd_of_dvd_mul_right hdvd
  rw [hK₀, ← pow_mul] at h1
  have h2 := (Nat.pow_dvd_pow_iff_le_right (by norm_num : 1 < 2)).1 h1
  have h3 := ncard_posRoots_E8_le
  nlinarith

theorem card_e8L :
    Nat.card (e8L K) = Nat.card (subsystemGroup .E8 K e8LeviNodes) := by
  have hmap : (e8L K).map (adjointGroup .E8 K).subtype = subsystemGroup .E8 K e8LeviNodes := by
    rw [e8L, Subgroup.map_comap_eq_self (by
      rw [Subgroup.range_subtype]
      exact subsystemGroup_le_adjointGroup_e8 _)]
  rw [← hmap, Subgroup.card_map_of_injective (adjointGroup .E8 K).subtype_injective]

theorem two_pow_dvd_card_e8L
    [Finite K]
    {e : ℕ} (hK : Nat.card K = 2 ^ (2 * e)) : 2 ^ (121 * e) ∣ Nat.card (e8L K) := by
  rw [card_e8L]
  have h1 := Subgroup.card_dvd_of_le
    (parabolicLeviUnipotent_le_subsystemGroup (τ := .E8) (K := K) (A := e8LeviNodes))
  rw [card_parabolicLeviUnipotent, hK, ← pow_mul] at h1
  refine dvd_trans (pow_dvd_pow 2 ?_) h1
  have := le_ncard_parabolicPosRoots_e8
  nlinarith

theorem e8_autFix
    [Finite K] {m : ℕ} (hm : 1 ≤ m) (hK : Nat.card K = 2 ^ m) (hq : 2 < 2 ^ m) :
    Exc.AutFix (e8Q K) (e8L K) := by
  classical
  have hZ : Subgroup.center (adjointGroup .E8 K) = ⊥ := center_adjointGroup_eq_bot
  have hL := e8_leviData hm hK hq (Z := ⊥) bot_le
  have hHodd := odd_card_e8T hm hK
  obtain ⟨hNF, Θ, hΘ, -, hker, hinv⟩ :=
    even_E7_E8_exact_inner_field_automorphism_normal_form hm K hK .E8 (Or.inr rfl)
  have hinner : ∀ β : MulAut (adjointGroup .E8 K),
      β ∈ (MulAut.conj : adjointGroup .E8 K →* MulAut (adjointGroup .E8 K)).range →
      (∃ j : ℕ, β ^ 2 ^ j = 1) → (∀ y ∈ e8Q K, β y = y) → (∀ y ∈ e8L K, β y = y) →
        β = 1 := by
    rintro β ⟨c, rfl⟩ ⟨j, hj⟩ hβQ hβL
    rw [D4.conj_eq_one_of_fix_d4 hZ hL hHodd hj hβQ hβL, map_one]
  intro α ⟨k, hk⟩ hQ hLf
  have hfix : ∀ S : Subgroup (adjointGroup .E8 K), (∀ y ∈ S, α y = y) →
      ∀ n : ℕ, ∀ y ∈ S, (α ^ n) y = y := by
    intro S hS n
    induction n with
    | zero => intro y _; rfl
    | succ n ih => intro y hy; rw [pow_succ, MulAut.mul_apply, hS y hy, ih y hy]
  have hpow2 : ∀ n : ℕ, ∃ j : ℕ, (α ^ n) ^ 2 ^ j = 1 :=
    fun n => ⟨k, by rw [← pow_mul, mul_comm, pow_mul, hk, one_pow]⟩
  have hex : ∃ j, α ^ 2 ^ j ∈
      (MulAut.conj : adjointGroup .E8 K →* MulAut (adjointGroup .E8 K)).range :=
    ⟨k, by rw [hk]; exact one_mem _⟩
  rcases Nat.eq_zero_or_pos (Nat.find hex) with h0 | hpos
  · have hα := Nat.find_spec hex
    rw [h0, pow_zero, pow_one] at hα
    exact hinner α hα ⟨k, hk⟩ hQ hLf
  exfalso
  obtain ⟨j, hj⟩ : ∃ j, Nat.find hex = j + 1 := ⟨Nat.find hex - 1, by omega⟩
  have hβo : α ^ 2 ^ j ∉
      (MulAut.conj : adjointGroup .E8 K →* MulAut (adjointGroup .E8 K)).range :=
    Nat.find_min hex (by omega)
  have hβ2' : (α ^ 2 ^ j) ^ 2 ∈
      (MulAut.conj : adjointGroup .E8 K →* MulAut (adjointGroup .E8 K)).range := by
    rw [← pow_mul, ← pow_succ, ← hj]
    exact Nat.find_spec hex
  have hβ2 : (α ^ 2 ^ j) ^ 2 = 1 := by
    rw [← pow_mul]
    exact hinner _ (by rw [pow_mul]; exact hβ2') (hpow2 _) (hfix _ hQ _) (hfix _ hLf _)
  have hβL : ∀ y ∈ e8L K, (α ^ 2 ^ j) y = y := hfix _ hLf _
  obtain ⟨⟨g, σ⟩, hgσ, -⟩ := hNF (α ^ 2 ^ j)
  have hΘβ : Θ (α ^ 2 ^ j) = σ := hΘ _ g σ hgσ
  have hσ1 : Θ (α ^ 2 ^ j) ≠ 1 := fun h1 => hβo (by
    rw [← MonoidHom.mem_ker, hker] at h1
    exact h1)
  obtain ⟨⟨e, he⟩, hσc⟩ := (hinv _ hβ2).resolve_left hσ1
  rw [hΘβ] at hσc
  have he1 : 1 ≤ e := by omega
  have hK' : Nat.card K = 2 ^ (2 * e) := by rw [hK, he, two_mul]
  have hσ' : ∀ c, σ c = c ^ 2 ^ e := fun c => by rw [hσc, show m / 2 = e by omega]
  obtain ⟨hQ1, -⟩ :=
    even_exceptional_quadratic_field_graph_field_involution_descent he1 K hK' σ.toRingHom hσ'
  obtain ⟨β₀, hβ₀, hdesc⟩ := hQ1 .E8
  obtain ⟨-, hdα⟩ := hdesc g fun _ => 1
  have hβform : ∀ u, ((α ^ 2 ^ j) u : ModGL .E8 K) = (g : ModGL .E8 K) *
      rootDiagUnit .E8 (fun _ => 1) * Units.map (entrywiseHom σ.toRingHom) (u : ModGL .E8 K) *
        (rootDiagUnit .E8 fun _ => 1)⁻¹ * (g : ModGL .E8 K)⁻¹ := by
    intro u
    rw [show (fun _ => (1 : Kˣ)) = (1 : Fin Tag.E8.rank → Kˣ) from rfl, rootDiagUnit_one, mul_one,
      inv_one, mul_one]
    exact hgσ u
  obtain ⟨ψ, -, hfixψ, -⟩ := hdα (α ^ 2 ^ j) hβform (by rw [← pow_two]; exact hβ2)
  have hβ₀e : β₀ = entrywiseAdjointAut .E8 σ :=
    MulEquiv.ext fun u => Subtype.ext (by rw [hβ₀ u, coe_entrywiseAdjointAut])
  obtain ⟨-, -, -, hmap, ⟨-, -, -, -, hmodel⟩, -⟩ :=
    even_E7_E8_canonical_field_full_centralizer .E8 (Or.inr rfl) he1 K hK' σ hσ'
  have hcard1 : Nat.card (e8L K) ∣
      Nat.card ((α ^ 2 ^ j).toMonoidHom.eqLocus (MonoidHom.id (adjointGroup .E8 K))) :=
    Subgroup.card_dvd_of_le fun y hy => hβL y hy
  have hcard2 : Nat.card ((α ^ 2 ^ j).toMonoidHom.eqLocus (MonoidHom.id (adjointGroup .E8 K))) =
      Nat.card (fixedFieldImage .E8 σ) := by
    rw [← hmap, Subgroup.card_map_of_injective (adjointGroup .E8 K).subtype_injective, ← hβ₀e,
      ← hfixψ, Subgroup.card_map_of_injective ψ.injective]
  obtain ⟨K₀, _, _, hK₀, ⟨E⟩⟩ := nonempty_mulEquiv_adjointGroup .E8 (hmodel rfl).2
  have hcard3 : Nat.card (fixedFieldImage .E8 σ) = Nat.card (adjointGroup .E8 K₀) :=
    Nat.card_congr E.toEquiv
  exact not_two_pow_dvd_card_adjointGroup_e8 he1 hK₀
    (by rw [← hcard3, ← hcard2]; exact (two_pow_dvd_card_e8L hK').trans hcard1)

end CFSG.ComponentClassification.RankTwoExceptional.E8
