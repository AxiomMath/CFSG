module

public import CFSG.LieType.Chevalley.MinimalBorelOvergroups
public import CFSG.LieType.Chevalley.BruhatCellFactorization
public import CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
public import Mathlib.GroupTheory.Sylow
public import Mathlib.GroupTheory.Perm.Cycle.Type

public noncomputable section

namespace CFSG.LieType.Chevalley

open CFSG.Blueprint.Chevalley CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open scoped Pointwise

variable {τ : Tag} {K : Type} [Field K]

theorem pow_card_sub_one_eq_one_of_mem_diagonalGroup [Finite K] {g : ModGL τ K}
    (hg : g ∈ diagonalGroup) : g ^ (Nat.card K - 1) = 1 := by
  have : Fintype K := Fintype.ofFinite K
  refine Units.ext (end_ext_single fun b => ?_)
  obtain ⟨c, hc⟩ := exists_apply_single_of_mem_diagonalGroup hg b
  have hpow : ∀ n : ℕ, ((g ^ n : ModGL τ K) : Module.End K (RootModule τ K))
      (Finsupp.single b 1) = ((c : K) ^ n) • Finsupp.single b 1 := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [pow_succ, Units.val_mul, Module.End.mul_apply, hc, map_smul, ih, smul_smul, pow_succ,
        mul_comm]
  rw [hpow, Nat.card_eq_fintype_card, FiniteField.pow_card_sub_one_eq_one _ c.ne_zero, one_smul,
    Units.val_one, Module.End.one_apply]

theorem finite_modGL [Finite K] : Finite (ModGL τ K) := by
  have : Finite (Module.End K (RootModule τ K)) := Module.finite_of_finite K
  infer_instance

theorem prime_dvd_card [Finite K] (p : ℕ) [Fact p.Prime] [CharP K p] : p ∣ Nat.card K := by
  have : Fintype K := Fintype.ofFinite K
  obtain ⟨n, -, hcard⟩ := FiniteField.card K p
  rw [Nat.card_eq_fintype_card, hcard]
  exact dvd_pow_self p n.ne_zero

theorem not_dvd_card_torusGroup
    [Finite K] (p : ℕ) [Fact p.Prime] [CharP K p] :
    ¬ p ∣ Nat.card (torusGroup τ K) := by
  intro hdvd
  have := finite_modGL (τ := τ) (K := K)
  obtain ⟨h, hh⟩ := exists_prime_orderOf_dvd_card' p hdvd
  have h1 : (h : ModGL τ K) ^ (Nat.card K - 1) = 1 :=
    pow_card_sub_one_eq_one_of_mem_diagonalGroup (torusGroup_le_diagonalGroup h.2)
  have h2 : orderOf h ∣ Nat.card K - 1 :=
    orderOf_dvd_of_pow_eq_one (Subtype.ext (by simpa using h1))
  rw [hh] at h2
  have hq := prime_dvd_card (K := K) p
  have hq1 : 1 ≤ Nat.card K := Nat.card_pos
  have h3 := Nat.dvd_sub hq h2
  rw [Nat.sub_sub_self hq1] at h3
  exact (Fact.out : p.Prime).one_lt.ne' (Nat.dvd_one.1 h3)

theorem not_dvd_sum_length
    [Finite K] (p : ℕ) [Fact p.Prime] [CharP K p] :
    ¬ p ∣ ∑ᶠ w : WeylGroup τ, Nat.card K ^ (coxeterSystem τ).length w := by
  classical
  have : Fintype (WeylGroup τ) := Fintype.ofFinite _
  rw [finsum_eq_sum_of_fintype, ← Finset.add_sum_erase _ _ (Finset.mem_univ 1),
    (coxeterSystem τ).length_one, pow_zero]
  intro h
  have hrest : p ∣ ∑ w ∈ Finset.univ.erase 1, Nat.card K ^ (coxeterSystem τ).length w := by
    refine Finset.dvd_sum fun w hw => ?_
    have hw1 : w ≠ 1 := Finset.ne_of_mem_erase hw
    have hl : (coxeterSystem τ).length w ≠ 0 := fun h0 =>
      hw1 ((coxeterSystem τ).length_eq_zero_iff.1 h0)
    exact (prime_dvd_card (K := K) p).trans (dvd_pow_self _ hl)
  exact (Fact.out : p.Prime).one_lt.ne' (Nat.dvd_one.1 ((Nat.dvd_add_right hrest).1 (by
    rwa [add_comm] at h)))

theorem card_subgroupOf_of_le {G : Type*} [Group G] {X C : Subgroup G} (h : X ≤ C) :
    Nat.card (X.subgroupOf C) = Nat.card X :=
  Nat.card_congr (Subgroup.subgroupOfEquivOfLe h).toEquiv

theorem isPGroup_and_not_dvd_index
    [Finite K] (p : ℕ) [Fact p.Prime] [CharP K p]
    {X : Subgroup (ModGL τ K)} (hXC : X ≤ adjointGroup τ K)
    (hX : Nat.card X = Nat.card K ^ {α : Fin τ.rank → ℤ | IsRoot τ α ∧ 0 < height α}.ncard) :
    IsPGroup p (X.subgroupOf (adjointGroup τ K)) ∧
      ¬ p ∣ (X.subgroupOf (adjointGroup τ K)).index := by
  have : Fintype K := Fintype.ofFinite K
  have := finite_modGL (τ := τ) (K := K)
  obtain ⟨n, -, hcard⟩ := FiniteField.card K p
  have hqcard : Nat.card K = p ^ (n : ℕ) := by rw [Nat.card_eq_fintype_card, hcard]
  set N := {α : Fin τ.rank → ℤ | IsRoot τ α ∧ 0 < height α}.ncard
  have hXs : Nat.card (X.subgroupOf (adjointGroup τ K)) = Nat.card K ^ N := by
    rw [card_subgroupOf_of_le hXC, hX]
  refine ⟨IsPGroup.of_card (n := (n : ℕ) * N) (by rw [hXs, hqcard, ← pow_mul]), fun hdvd => ?_⟩
  have hmul := Subgroup.card_mul_index (X.subgroupOf (adjointGroup τ K))
  rw [hXs, card_adjointGroup, mul_comm (Nat.card (torusGroup τ K)), mul_assoc] at hmul
  have hpos : 0 < Nat.card K ^ N := pow_pos Nat.card_pos N
  have hidx := Nat.eq_of_mul_eq_mul_left hpos hmul
  rw [hidx] at hdvd
  rcases (Nat.Prime.dvd_mul Fact.out).1 hdvd with h | h
  · exact not_dvd_card_torusGroup p h
  · exact not_dvd_sum_length p h

theorem map_mulAut_mul {G : Type*} [Group G] (H : Subgroup G) (f g : MulAut G) :
    H.map (f * g).toMonoidHom = (H.map g.toMonoidHom).map f.toMonoidHom := by
  rw [Subgroup.map_map]
  rfl

theorem map_conj_self {G : Type*} [Group G] {H : Subgroup G} {h : G} (hh : h ∈ H) :
    H.map (MulAut.conj h).toMonoidHom = H :=
  map_conj_eq_of_mem_normalizer (Subgroup.le_normalizer hh)

theorem map_conj_subgroupOf {G : Type*} [Group G] {C X : Subgroup G} (hXC : X ≤ C) (c : C) :
    (X.subgroupOf C).map (MulAut.conj c).toMonoidHom =
      (X.map (MulAut.conj (c : G)).toMonoidHom).subgroupOf C := by
  ext y
  simp only [Subgroup.mem_map, Subgroup.mem_subgroupOf, MulEquiv.coe_toMonoidHom,
    MulAut.conj_apply]
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨x, hx, by simp⟩
  · rintro ⟨x, hx, hxy⟩
    exact ⟨⟨x, hXC hx⟩, hx, Subtype.ext (by simpa using hxy)⟩

theorem coe_smul_sylow_eq_map {G : Type*} [Group G] {p : ℕ} (g : G) (P : Sylow p G) :
    ((g • P : Sylow p G) : Subgroup G) = (P : Subgroup G).map (MulAut.conj g).toMonoidHom := by
  ext x
  rw [Sylow.coe_subgroup_smul, Subgroup.mem_smul_pointwise_iff_exists, Subgroup.mem_map]
  rfl

theorem coe_mulAut_smul_sylow {G : Type*} [Group G] {p : ℕ} (α : MulAut G) (P : Sylow p G) :
    ((α • P : Sylow p G) : Subgroup G) = (P : Subgroup G).map α.toMonoidHom := by
  ext x
  rw [Sylow.pointwise_smul_def, Subgroup.mem_smul_pointwise_iff_exists, Subgroup.mem_map]
  rfl

theorem map_conj_posUnipotent_of_mem_borelGroup
    {b : ModGL τ K} (hb : b ∈ borelGroup τ K) :
    (posUnipotent τ K).map (MulAut.conj b).toMonoidHom = posUnipotent τ K :=
  map_conj_eq_of_mem_normalizer ((Subgroup.normal_subgroupOf_iff_le_normalizer le_sup_right).1
    (triangular_borel_structure.{0, 0} τ K).2.2.2.2.2.2.2.2.1 hb)

theorem posUnipotent_inf_negUnipotent
    : posUnipotent τ K ⊓ negUnipotent τ K = ⊥ :=
  eq_bot_iff.2 fun x hx => by
    have hUB : posUnipotent τ K ≤ borelGroup τ K := le_sup_right
    rw [← borelGroup_inf_negUnipotent (τ := τ) (K := K)]
    exact Subgroup.mem_inf.2 ⟨hUB (Subgroup.mem_inf.1 hx).1, (Subgroup.mem_inf.1 hx).2⟩

theorem map_conj_canonicalRep_longest
    {w₀ : WeylGroup τ}
    (hw₀ : ∀ w, (coxeterSystem τ).length w ≤ (coxeterSystem τ).length w₀) :
    (posUnipotent τ K).map (MulAut.conj (canonicalRep (coxeterSystem τ) K w₀)).toMonoidHom =
      negUnipotent τ K := by
  obtain ⟨w₁, -, huniq, himage, -⟩ := weyl_longest_element τ
  obtain rfl : w₀ = w₁ := huniq w₀ hw₀
  rw [posUnipotent, (canonical_weyl_root_transport τ K).1 w₀ _ fun α hα => hα.1, himage]
  rfl

theorem posUnipotent_inf_map_conj_eq_bot_iff
    {w₀ : WeylGroup τ}
    (hw₀ : ∀ w, (coxeterSystem τ).length w ≤ (coxeterSystem τ).length w₀) {w : WeylGroup τ}
    {g : ModGL τ K} (hg : g ∈ bruhatCell τ K w) :
    posUnipotent τ K ⊓ (posUnipotent τ K).map (MulAut.conj g).toMonoidHom = ⊥ ↔ w = w₀ := by
  obtain ⟨b, hb, b', hb', rfl⟩ := mem_bruhatCell.1 hg
  set n := canonicalRep (coxeterSystem τ) K w with hn
  have hred : posUnipotent τ K ⊓ (posUnipotent τ K).map (MulAut.conj (b * n * b')).toMonoidHom =
      (posUnipotent τ K ⊓ (posUnipotent τ K).map (MulAut.conj n).toMonoidHom).map
        (MulAut.conj b).toMonoidHom := by
    rw [map_conj_mul, map_conj_mul, map_conj_posUnipotent_of_mem_borelGroup hb',
      Subgroup.map_inf_eq _ _ _ (MulAut.conj b).injective,
      map_conj_posUnipotent_of_mem_borelGroup hb]
  rw [hred, Subgroup.map_eq_bot_iff_of_injective _ (MulAut.conj b).injective]
  have h₀ := reversesSigns_of_forall_length_le hw₀
  constructor
  · intro hbot
    by_contra hne
    have hnot : ¬ ReversesSigns w := fun hw => hne (hw.eq h₀)
    simp only [ReversesSigns, not_forall] at hnot
    obtain ⟨α, hα, hpos, hwα⟩ := hnot
    have hwpos : 0 < height (w • α) := by
      rcases IsRoot.height_pos_or_neg (IsRoot.smul hα w) with h | h
      · exact h
      · exact absurd h hwα
    have hx : pinnedX τ K (w • α) 1 ∈
        posUnipotent τ K ⊓ (posUnipotent τ K).map (MulAut.conj n).toMonoidHom := by
      refine Subgroup.mem_inf.2 ⟨pinnedX_mem_rootSpan
        (S := {α | IsRoot τ α ∧ 0 < height α}) ⟨IsRoot.smul hα w, hwpos⟩ 1, ?_⟩
      rw [posUnipotent, (canonical_weyl_root_transport τ K).1 w _ fun α hα => hα.1]
      exact pinnedX_mem_rootSpan (S := (fun α => w • α) '' {α | IsRoot τ α ∧ 0 < height α})
        ⟨α, ⟨hα, hpos⟩, rfl⟩ 1
    rw [hbot, Subgroup.mem_bot] at hx
    exact one_ne_zero (pinnedX_injective τ K _ (hx.trans (pinnedX_zero τ K _).symm))
  · rintro rfl
    rw [map_conj_canonicalRep_longest hw₀]
    exact posUnipotent_inf_negUnipotent

theorem card_negUnipotent
    {w₀ : WeylGroup τ}
    (hw₀ : ∀ w, (coxeterSystem τ).length w ≤ (coxeterSystem τ).length w₀) :
    Nat.card (negUnipotent τ K) =
      Nat.card K ^ {α : Fin τ.rank → ℤ | IsRoot τ α ∧ 0 < height α}.ncard := by
  rw [← map_conj_canonicalRep_longest (K := K) hw₀,
    Subgroup.card_map_of_injective (MulAut.conj _).injective, card_posUnipotent]

theorem map_mulAut_one {G : Type*} [Group G] (H : Subgroup G) :
    H.map (1 : MulAut G).toMonoidHom = H := by
  ext x
  simp

theorem exceptional_ordinary_Sylow_opposition
    (τ : Tag) (K : Type) [Field K] [Finite K]
    (p : ℕ) [Fact p.Prime] [CharP K p] (w₀ : WeylGroup τ)
    (hw₀ : ∀ w, (coxeterSystem τ).length w ≤ (coxeterSystem τ).length w₀) :
    (∃ P : Sylow p (adjointGroup τ K),
      (P : Subgroup (adjointGroup τ K)) = (posUnipotent τ K).subgroupOf (adjointGroup τ K)) ∧
    (∃ P : Sylow p (adjointGroup τ K),
      (P : Subgroup (adjointGroup τ K)) = (negUnipotent τ K).subgroupOf (adjointGroup τ K)) ∧
    posUnipotent τ K ⊓ negUnipotent τ K = ⊥ ∧
    (∀ S : Sylow p (adjointGroup τ K),
      (posUnipotent τ K).subgroupOf (adjointGroup τ K) ⊓ S = ⊥ ↔
        ∃ u ∈ (posUnipotent τ K).subgroupOf (adjointGroup τ K),
          (S : Subgroup (adjointGroup τ K)) =
            ((negUnipotent τ K).subgroupOf (adjointGroup τ K)).map (MulAut.conj u).toMonoidHom) ∧
    (∀ (w : WeylGroup τ), ∀ g ∈ bruhatCell τ K w,
      posUnipotent τ K ⊓ (posUnipotent τ K).map (MulAut.conj g).toMonoidHom = ⊥ ↔ w = w₀) ∧
    ∀ α : MulAut (adjointGroup τ K), ∃ (c : adjointGroup τ K) (β : MulAut (adjointGroup τ K)),
      ((posUnipotent τ K).subgroupOf (adjointGroup τ K)).map β.toMonoidHom =
        (posUnipotent τ K).subgroupOf (adjointGroup τ K) ∧
      ((negUnipotent τ K).subgroupOf (adjointGroup τ K)).map β.toMonoidHom =
        (negUnipotent τ K).subgroupOf (adjointGroup τ K) ∧
      α = MulAut.conj c * β := by
  have := finite_modGL (τ := τ) (K := K)
  have hBC : borelGroup τ K ≤ adjointGroup τ K :=
    ((triangular_borel_structure.{0, 0} τ K).2.2.2.2.2.2.2.2.2.2.2 K).1
  have hUC : posUnipotent τ K ≤ adjointGroup τ K := le_trans le_sup_right hBC
  have hn₀ := canonicalRep_mem_adjointGroup (coxeterSystem τ) K w₀
  have hVC : negUnipotent τ K ≤ adjointGroup τ K := by
    rw [← map_conj_canonicalRep_longest (K := K) hw₀]
    rintro _ ⟨u, hu, rfl⟩
    exact mul_mem (mul_mem hn₀ (hUC hu)) (inv_mem hn₀)
  obtain ⟨hUp, hUi⟩ := isPGroup_and_not_dvd_index p hUC card_posUnipotent
  obtain ⟨hVp, hVi⟩ := isPGroup_and_not_dvd_index p hVC (card_negUnipotent hw₀)
  have hPU := IsPGroup.toSylow_coe hUp hUi
  have hPV := IsPGroup.toSylow_coe hVp hVi
  set PU : Sylow p (adjointGroup τ K) := hUp.toSylow hUi
  set PV : Sylow p (adjointGroup τ K) := hVp.toSylow hVi
  set UC := (posUnipotent τ K).subgroupOf (adjointGroup τ K) with hUCdef
  set VC := (negUnipotent τ K).subgroupOf (adjointGroup τ K) with hVCdef
  have hUV : UC ⊓ VC = ⊥ := by
    refine eq_bot_iff.2 fun x hx => ?_
    have h : (x : ModGL τ K) ∈ posUnipotent τ K ⊓ negUnipotent τ K :=
      Subgroup.mem_inf.2 ⟨(Subgroup.mem_inf.1 hx).1, (Subgroup.mem_inf.1 hx).2⟩
    rw [posUnipotent_inf_negUnipotent, Subgroup.mem_bot] at h
    exact Subgroup.mem_bot.2 (Subtype.ext h)
  have hkey : ∀ S : Sylow p (adjointGroup τ K), UC ⊓ S = ⊥ →
      ∃ u ∈ UC, (S : Subgroup (adjointGroup τ K)) = VC.map (MulAut.conj u).toMonoidHom := by
    intro S hS
    obtain ⟨c, hc⟩ := MulAction.exists_smul_eq (adjointGroup τ K) PU S
    have hSc : (S : Subgroup (adjointGroup τ K)) = UC.map (MulAut.conj c).toMonoidHom := by
      rw [← hc, coe_smul_sylow_eq_map, hPU]
    rw [hSc, map_conj_subgroupOf hUC] at hS ⊢
    have hamb : posUnipotent τ K ⊓
        (posUnipotent τ K).map (MulAut.conj (c : ModGL τ K)).toMonoidHom = ⊥ := by
      refine eq_bot_iff.2 fun x hx => ?_
      have hxC : x ∈ adjointGroup τ K := hUC (Subgroup.mem_inf.1 hx).1
      have h : (⟨x, hxC⟩ : adjointGroup τ K) ∈ UC ⊓ ((posUnipotent τ K).map
          (MulAut.conj (c : ModGL τ K)).toMonoidHom).subgroupOf (adjointGroup τ K) :=
        Subgroup.mem_inf.2 ⟨(Subgroup.mem_inf.1 hx).1, (Subgroup.mem_inf.1 hx).2⟩
      rw [hS, Subgroup.mem_bot] at h
      exact Subgroup.mem_bot.2 (congrArg Subtype.val h)
    have hcell : (c : ModGL τ K) ∈ ⋃ w ∈ parabolicWeylGroup τ Set.univ, bruhatCell τ K w := by
      rw [← (standard_parabolic_cells τ K).1, (standard_parabolic_cells τ K).2.2.2.2.2.1]
      exact c.2
    obtain ⟨w, -, hcw⟩ := Set.mem_iUnion₂.1 hcell
    obtain rfl := (posUnipotent_inf_map_conj_eq_bot_iff hw₀ hcw).1 hamb
    obtain ⟨b, hb, b', hb', hbb⟩ := mem_bruhatCell.1 hcw
    have hb'' : b ∈ (posUnipotent τ K : Set (ModGL τ K)) * (torusGroup τ K : Set _) := by
      rw [← (triangular_borel_structure.{0, 0} τ K).2.2.2.2.2.1]
      exact hb
    obtain ⟨u, hu, h, hh, rfl⟩ := hb''
    have hmapc : (posUnipotent τ K).map (MulAut.conj (c : ModGL τ K)).toMonoidHom =
        (negUnipotent τ K).map (MulAut.conj u).toMonoidHom := by
      rw [← hbb, map_conj_mul, map_conj_mul, map_conj_posUnipotent_of_mem_borelGroup hb',
        map_conj_canonicalRep_longest hw₀, map_conj_mul,
        map_conj_eq_of_mem_normalizer (torusGroup_le_normalizer_negUnipotent hh)]
    refine ⟨⟨u, hUC hu⟩, hu, ?_⟩
    rw [hmapc, map_conj_subgroupOf hVC]
  have hkey' : ∀ S : Sylow p (adjointGroup τ K),
      (∃ u ∈ UC, (S : Subgroup (adjointGroup τ K)) = VC.map (MulAut.conj u).toMonoidHom) →
        UC ⊓ S = ⊥ := by
    rintro S ⟨u, hu, hS⟩
    rw [hS, ← map_conj_self hu, ← Subgroup.map_inf_eq _ _ _ (MulAut.conj u).injective, hUV,
      Subgroup.map_bot]
  have hAut : ∀ α : MulAut (adjointGroup τ K), ∃ (c : adjointGroup τ K)
      (β : MulAut (adjointGroup τ K)), UC.map β.toMonoidHom = UC ∧ VC.map β.toMonoidHom = VC ∧
        α = MulAut.conj c * β := by
    intro α
    obtain ⟨c, hc⟩ := MulAction.exists_smul_eq (adjointGroup τ K) PU (α • PU)
    have hαU : UC.map α.toMonoidHom = UC.map (MulAut.conj c).toMonoidHom := by
      rw [← hPU, ← coe_mulAut_smul_sylow, ← coe_smul_sylow_eq_map, hc]
    set α₁ := (MulAut.conj c)⁻¹ * α with hα₁
    have hα₁U : UC.map α₁.toMonoidHom = UC := by
      rw [map_mulAut_mul, hαU, ← map_mulAut_mul, inv_mul_cancel, map_mulAut_one]
    have hS : UC ⊓ ((α₁ • PV : Sylow p (adjointGroup τ K)) : Subgroup (adjointGroup τ K)) = ⊥ := by
      rw [coe_mulAut_smul_sylow, hPV, ← hα₁U, ← Subgroup.map_inf_eq _ _ _ α₁.injective, hUV,
        Subgroup.map_bot]
    obtain ⟨u, hu, hu'⟩ := hkey _ hS
    rw [coe_mulAut_smul_sylow, hPV] at hu'
    refine ⟨c * u, (MulAut.conj u)⁻¹ * α₁, ?_, ?_, ?_⟩
    · rw [map_mulAut_mul, hα₁U, ← map_inv, map_conj_self (inv_mem hu)]
    · rw [map_mulAut_mul, hu', ← map_mulAut_mul, inv_mul_cancel, map_mulAut_one]
    · rw [hα₁, map_mul]
      group
  exact ⟨⟨PU, hPU⟩, ⟨PV, hPV⟩, posUnipotent_inf_negUnipotent, fun S => ⟨hkey S, hkey' S⟩,
    fun w g hg => posUnipotent_inf_map_conj_eq_bot_iff hw₀ hg, hAut⟩

end CFSG.LieType.Chevalley
