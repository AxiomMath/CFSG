module

public import CFSG.Holt.H78.Lemma27Blocks
import CFSG.Holt.H78.AltModelSylow
import CFSG.Holt.H78.SEModelFive
import CFSG.Holt.H78.DataSylow
public import CFSG.FeitThompson.OddOrderTheorem

public section

namespace CFSG.Holt.H78

open MulAction CFSG.Holt CFSG.Holt.General Equiv
open scoped Pointwise

section Sections

variable {N : Type*} [Group N]

theorem not_subsingleton_of_ne_comm (hN : ∃ a b : N, a * b ≠ b * a) : ¬ Subsingleton N := by
  intro h
  obtain ⟨a, b, hab⟩ := hN
  exact hab (Subsingleton.elim _ _)

variable [IsSimpleGroup N]

theorem not_isSolvable_of_surjective_of_ne_comm {A : Type*} [Group A] {ψ : A →* N}
    (hψ : Function.Surjective ψ) (hN : ∃ a b : N, a * b ≠ b * a) : ¬ Group.IsSolvable A := by
  intro hA
  have : Group.IsSolvable N := Group.isSolvable_of_surjective hψ
  obtain ⟨a, b, hab⟩ := hN
  exact hab (IsSimpleGroup.comm_iff_isSolvable.mpr this a b)

theorem le_ker_of_isSolvable_of_ne_comm {A : Type*} [Group A] {ψ : A →* N}
    (hψ : Function.Surjective ψ) (hN : ∃ a b : N, a * b ≠ b * a) {B : Subgroup A}
    [hBn : B.Normal] (hB : Group.IsSolvable B) : B ≤ ψ.ker := by
  have : (B.map ψ).Normal := hBn.map ψ hψ
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (B.map ψ) with h | h
  · exact (Subgroup.map_eq_bot_iff _).mp h
  · refine absurd hB (not_isSolvable_of_surjective_of_ne_comm (ψ := ψ.comp B.subtype)
      (fun n => ?_) hN)
    obtain ⟨b, hb, rfl⟩ : n ∈ B.map ψ := h ▸ Subgroup.mem_top n
    exact ⟨⟨b, hb⟩, rfl⟩

theorem exists_surjective_map_of_isSolvable_ker {G G' : Type*} [Group G] [Group G']
    {f : G →* G'} (hf : Group.IsSolvable f.ker) {L : Subgroup G} {ψ : L →* N}
    (hψ : Function.Surjective ψ) (hN : ∃ a b : N, a * b ≠ b * a) :
    ∃ ψ' : L.map f →* N, Function.Surjective ψ' := by
  set g := f.subgroupMap L
  have hg : Function.Surjective g := f.subgroupMap_surjective L
  have hker : Group.IsSolvable g.ker := by
    let k : g.ker →* f.ker := (L.subtype.comp g.ker.subtype).codRestrict f.ker fun x => by
      have hx : g x = 1 := x.2
      exact congrArg Subtype.val hx
    refine Group.isSolvable_of_isSolvable_injective (f := k) fun x y hxy => ?_
    have := congrArg Subtype.val hxy
    exact Subtype.ext (Subtype.ext this)
  have hle : g.ker ≤ ψ.ker := le_ker_of_isSolvable_of_ne_comm hψ hN hker
  refine ⟨(MonoidHom.liftOfSurjective g hg) ⟨ψ, hle⟩, fun n => ?_⟩
  obtain ⟨x, rfl⟩ := hψ n
  exact ⟨g x, MonoidHom.liftOfRightInverse_comp_apply _ _ _ _ x⟩

private theorem relIndex_ne_zero_of_finite' {G : Type*} [Group G] [Finite G] (H K : Subgroup G) :
    H.relIndex K ≠ 0 :=
  Subgroup.index_ne_zero_of_finite

theorem exists_surjective_inf_of_relIndex_le_two {G : Type*} [Group G] [Finite G]
    {P Q L : Subgroup G} (hLQ : L ≤ Q) (hPQ : P.relIndex Q ≤ 2) {ψ : L →* N}
    (hψ : Function.Surjective ψ) (hN : ∃ a b : N, a * b ≠ b * a) :
    ∃ ψ' : ↥(L ⊓ P) →* N, Function.Surjective ψ' := by
  set I := (P.subgroupOf L).map ψ
  have hPL : P.relIndex L ≤ 2 :=
    (Subgroup.relIndex_le_of_le_right hLQ (relIndex_ne_zero_of_finite' P Q)).trans hPQ
  have hdvd : I.index ∣ P.relIndex L := Subgroup.index_map_dvd _ hψ
  have hI : I = ⊤ := by
    have h0 := Nat.pos_of_ne_zero (relIndex_ne_zero_of_finite' P L)
    have hpos : 0 < I.index := Nat.pos_of_dvd_of_pos hdvd h0
    have hle : I.index ≤ 2 := (Nat.le_of_dvd h0 hdvd).trans hPL
    interval_cases h : I.index
    · exact Subgroup.index_eq_one.mp h
    · have : I.Normal := Subgroup.normal_of_index_eq_two h
      rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal I with hb | ht
      · exfalso
        rw [hb, Subgroup.index_bot] at h
        have : Fact (Nat.card N).Prime := ⟨h ▸ Nat.prime_two⟩
        have : IsCyclic N := isCyclic_of_prime_card rfl
        obtain ⟨a, b, hab⟩ := hN
        exact hab (IsCyclic.commGroup.mul_comm a b)
      · exact ht
  refine ⟨ψ.comp (Subgroup.inclusion inf_le_left), fun n => ?_⟩
  obtain ⟨x, hx, rfl⟩ : n ∈ I := hI ▸ Subgroup.mem_top n
  exact ⟨⟨x, x.2, hx⟩, rfl⟩

theorem eq_bot_or_eq_of_le_of_isSimpleGroup {G : Type*} [Group G] {P M : Subgroup G}
    [IsSimpleGroup P] (hMP : M ≤ P) (hM : ∀ p ∈ P, ∀ x ∈ M, p * x * p⁻¹ ∈ M) :
    M = ⊥ ∨ M = P := by
  have : (M.subgroupOf P).Normal := ⟨fun x hx p => hM p p.2 x hx⟩
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (M.subgroupOf P) with h | h
  · left
    rw [Subgroup.subgroupOf_eq_bot] at h
    exact disjoint_iff.mp (h.mono_right le_rfl) |>.symm ▸ (inf_eq_left.mpr hMP).symm
  · exact Or.inr (le_antisymm hMP (Subgroup.subgroupOf_eq_top.mp h))

omit [IsSimpleGroup N] in
theorem nonempty_mulEquiv_of_surjective_of_ne_comm {A : Type*} [Group A] [IsSimpleGroup A]
    {ψ : A →* N} (hψ : Function.Surjective ψ) (hN : ∃ a b : N, a * b ≠ b * a) :
    Nonempty (A ≃* N) := by
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal ψ.ker with h | h
  · exact ⟨MulEquiv.ofBijective ψ ⟨(MonoidHom.ker_eq_bot_iff ψ).mp h, hψ⟩⟩
  · refine absurd ⟨fun a b => ?_⟩ (not_subsingleton_of_ne_comm hN)
    obtain ⟨x, rfl⟩ := hψ a
    obtain ⟨y, rfl⟩ := hψ b
    have h1 : ∀ z, ψ z = 1 := fun z => (h ▸ Subgroup.mem_top z : z ∈ ψ.ker)
    rw [h1, h1]

theorem exists_surjective_of_le_pi {ι : Type*} [Finite ι] {G : ι → Type*} [∀ i, Group (G i)]
    {P : ∀ i, Subgroup (G i)} {L : Subgroup (∀ i, G i)} (hLP : L ≤ Subgroup.pi Set.univ P)
    (hLn : ∀ p ∈ Subgroup.pi Set.univ P, ∀ x ∈ L, p * x * p⁻¹ ∈ L) {ψ : L →* N}
    (hψ : Function.Surjective ψ) (hN : ∃ a b : N, a * b ≠ b * a) :
    ∃ i, ∃ M : Subgroup (G i), M ≤ P i ∧ (∀ p ∈ P i, ∀ x ∈ M, p * x * p⁻¹ ∈ M) ∧
      ∃ ψ' : M →* N, Function.Surjective ψ' := by
  classical
  set E : ι → Subgroup (∀ i, G i) := fun i => L ⊓ Subgroup.pi ({i}ᶜ : Set ι) fun _ => ⊥ with hE
  have hsupp : ∀ {i} {x : ∀ i, G i}, x ∈ E i → ∀ j, j ≠ i → x j = 1 := fun hx j hj =>
    Subgroup.mem_bot.mp ((Subgroup.mem_pi _).mp hx.2 j hj)
  have hsingle : ∀ i (y : G i), y ∈ P i → Pi.mulSingle i y ∈ Subgroup.pi Set.univ P := by
    intro i y hy
    refine (Subgroup.mem_pi _).mpr fun j _ => ?_
    rcases eq_or_ne j i with rfl | hji
    · rwa [Pi.mulSingle_eq_same]
    · rw [Pi.mulSingle_eq_of_ne hji]
      exact (P j).one_mem
  by_cases h : ∃ i, ∀ n : N, ∃ x : L, (x : ∀ i, G i) ∈ E i ∧ ψ x = n
  · obtain ⟨i, hi⟩ := h
    set π := (Pi.evalMonoidHom G i).subgroupMap (E i)
    have hπ : Function.Surjective π := (Pi.evalMonoidHom G i).subgroupMap_surjective (E i)
    have hker : π.ker ≤ (ψ.comp (Subgroup.inclusion inf_le_left)).ker := by
      intro x hx
      have hx1 : (x : ∀ i, G i) i = 1 := congrArg Subtype.val hx
      have hx' : (x : ∀ i, G i) = 1 := funext fun j => by
        rcases eq_or_ne j i with rfl | hji
        · exact hx1
        · exact hsupp x.2 j hji
      rw [MonoidHom.mem_ker, MonoidHom.comp_apply,
        show Subgroup.inclusion inf_le_left x = 1 from Subtype.ext hx', map_one]
    refine ⟨i, (E i).map (Pi.evalMonoidHom G i), ?_, ?_,
      (MonoidHom.liftOfSurjective π hπ) ⟨_, hker⟩, fun n => ?_⟩
    · rintro _ ⟨x, hx, rfl⟩
      exact (Subgroup.mem_pi _).mp (hLP hx.1) i trivial
    · rintro p hp _ ⟨x, hx, rfl⟩
      refine ⟨Pi.mulSingle i p * x * (Pi.mulSingle i p)⁻¹, ⟨hLn _ (hsingle i p hp) x hx.1,
        (Subgroup.mem_pi _).mpr fun j hj => ?_⟩, ?_⟩
      · rw [Subgroup.mem_bot, Pi.mul_apply, Pi.mul_apply, Pi.inv_apply,
          Pi.mulSingle_eq_of_ne hj, hsupp hx j hj]
        group
      · simp [Pi.evalMonoidHom]
    · obtain ⟨x, hx, rfl⟩ := hi n
      exact ⟨π ⟨x, hx⟩, MonoidHom.liftOfRightInverse_comp_apply _ _ _ _ _⟩
  · exfalso
    push Not at h
    have hEn : ∀ i, ((E i).subgroupOf L).Normal := fun i => ⟨fun x hx g => by
      refine ⟨L.mul_mem (L.mul_mem g.2 x.2) (L.inv_mem g.2), (Subgroup.mem_pi _).mpr
        fun j hj => Subgroup.mem_bot.mpr ?_⟩
      have h1 : (x : ∀ i, G i) j = 1 := hsupp hx j hj
      change ((g : ∀ i, G i) * x * (g : ∀ i, G i)⁻¹) j = 1
      rw [Pi.mul_apply, Pi.mul_apply, Pi.inv_apply, h1, mul_one, mul_inv_cancel]⟩
    have hkill : ∀ i (x : L), (x : ∀ i, G i) ∈ E i → ψ x = 1 := by
      intro i x hx
      have : (((E i).subgroupOf L).map ψ).Normal := (hEn i).map ψ hψ
      rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (((E i).subgroupOf L).map ψ) with hb | ht
      · exact (Subgroup.map_eq_bot_iff _).mp hb hx
      · obtain ⟨n, hn⟩ := h i
        obtain ⟨y, hy, hyn⟩ : n ∈ ((E i).subgroupOf L).map ψ := ht ▸ Subgroup.mem_top n
        exact absurd hyn (hn y hy)
    have hcomm : ∀ x y : L, ψ (x * y * x⁻¹ * y⁻¹) = 1 := by
      intro x y
      have hZ : ((x * y * x⁻¹ * y⁻¹ : L) : ∀ i, G i) ∈ ψ.ker.map L.subtype := by
        refine Subgroup.pi_mem_of_mulSingle_mem _ fun i => ?_
        set m := Pi.mulSingle i ((y : ∀ i, G i) i)
        have hm : m ∈ Subgroup.pi Set.univ P :=
          hsingle i _ ((Subgroup.mem_pi _).mp (hLP y.2) i trivial)
        have hc : Pi.mulSingle i (((x * y * x⁻¹ * y⁻¹ : L) : ∀ i, G i) i) =
            (x : ∀ i, G i) * m * (x : ∀ i, G i)⁻¹ * m⁻¹ := by
          funext j
          rcases eq_or_ne j i with rfl | hji
          · simp [m]
          · simp [m, Pi.mulSingle_eq_of_ne hji]
        have hcL : (x : ∀ i, G i) * m * (x : ∀ i, G i)⁻¹ * m⁻¹ ∈ L := by
          have := L.mul_mem x.2 (hLn m hm _ (L.inv_mem x.2))
          simpa only [mul_assoc] using this
        have hcs : ∀ j, j ≠ i → ((x : ∀ i, G i) * m * (x : ∀ i, G i)⁻¹ * m⁻¹) j = 1 :=
          fun j hj => by rw [← hc, Pi.mulSingle_eq_of_ne hj]
        rw [hc]
        exact ⟨⟨_, hcL⟩, hkill i ⟨_, hcL⟩ ⟨hcL, (Subgroup.mem_pi _).mpr fun j hj =>
          Subgroup.mem_bot.mpr (hcs j hj)⟩, rfl⟩
      obtain ⟨z, hz, hzx⟩ := hZ
      rw [← Subtype.ext hzx]
      exact hz
    obtain ⟨a, b, hab⟩ := hN
    obtain ⟨x, rfl⟩ := hψ a
    obtain ⟨y, rfl⟩ := hψ b
    have := hcomm x y
    rw [map_mul, map_mul, map_mul, map_inv, map_inv, mul_inv_eq_one, mul_inv_eq_iff_eq_mul] at this
    exact hab this

end Sections

section Factors

variable {Δ : Type*} [Fintype Δ] [DecidableEq Δ]

theorem map_ofSubtype_alternatingGroup_pair (a b : Δ) :
    (alternatingGroup {x // x ≠ a ∧ x ≠ b}).map
        (Perm.ofSubtype : Perm {x // x ≠ a ∧ x ≠ b} →* Perm Δ) =
      alternatingGroup Δ ⊓ stabilizer (Perm Δ) a ⊓ stabilizer (Perm Δ) b := by
  ext g
  rw [Subgroup.mem_map, Subgroup.mem_inf, Subgroup.mem_inf, Perm.mem_alternatingGroup,
    mem_stabilizer_iff, mem_stabilizer_iff, Perm.smul_def, Perm.smul_def]
  constructor
  · rintro ⟨f, hf, rfl⟩
    rw [Perm.mem_alternatingGroup] at hf
    refine ⟨⟨by rw [Perm.sign_ofSubtype, hf], Perm.ofSubtype_apply_of_not_mem f ?_⟩,
      Perm.ofSubtype_apply_of_not_mem f ?_⟩ <;> simp
  · rintro ⟨⟨hsign, ha⟩, hb⟩
    have h₁ : ∀ x, (g x ≠ a ∧ g x ≠ b) ↔ (x ≠ a ∧ x ≠ b) := fun x => by
      constructor
      · rintro ⟨h1, h2⟩
        exact ⟨fun h => h1 (by rw [h, ha]), fun h => h2 (by rw [h, hb])⟩
      · rintro ⟨h1, h2⟩
        exact ⟨fun h => h1 (g.injective (h.trans ha.symm)),
          fun h => h2 (g.injective (h.trans hb.symm))⟩
    have h₂ : ∀ x, g x ≠ x → (x ≠ a ∧ x ≠ b) := fun x hx =>
      ⟨fun h => hx (h ▸ ha), fun h => hx (h ▸ hb)⟩
    refine ⟨Perm.subtypePerm g h₁, ?_, Perm.ofSubtype_subtypePerm h₁ h₂⟩
    rw [Perm.mem_alternatingGroup, ← Perm.sign_ofSubtype, Perm.ofSubtype_subtypePerm h₁ h₂,
      hsign]

theorem nonempty_alternatingGroup_inf_stabilizer_pair_mulEquiv {a b : Δ} (hab : a ≠ b) :
    Nonempty ((alternatingGroup Δ ⊓ stabilizer (Perm Δ) a ⊓ stabilizer (Perm Δ) b :
      Subgroup (Perm Δ)) ≃* alternatingGroup (Fin (Fintype.card Δ - 2))) := by
  have hcard : Fintype.card {x // x ≠ a ∧ x ≠ b} = Fintype.card Δ - 2 := by
    rw [Fintype.card_subtype]
    have : (Finset.univ.filter fun x : Δ => x ≠ a ∧ x ≠ b) = Finset.univ \ {a, b} := by
      ext x
      simp
    rw [this, Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ,
      Finset.card_pair hab]
  exact ⟨(((alternatingGroup _).equivMapOfInjective _ Perm.ofSubtype_injective).trans
    (MulEquiv.subgroupCongr (map_ofSubtype_alternatingGroup_pair a b))).symm.trans
    (Fintype.equivFinOfCardEq hcard).altCongrHom⟩

theorem nonempty_alternatingGroup_inf_stabilizer_mulEquiv (a : Δ) :
    Nonempty ((alternatingGroup Δ ⊓ stabilizer (Perm Δ) a : Subgroup (Perm Δ)) ≃*
      alternatingGroup (Fin (Fintype.card Δ - 1))) := by
  have hcard : Fintype.card {x // x ≠ a} = Fintype.card Δ - 1 := by simp
  exact ⟨(alternatingGroupStabilizerEquiv a).symm.trans
    (Fintype.equivFinOfCardEq hcard).altCongrHom⟩

theorem HoltData.isSolvable_or_alternating_pairProducts {G : Type*} [Group G] [Finite G]
    {Ω : Type*} [MulAction G Ω] (D : HoltData G Ω) (i : D.ι) (a b : D.Ψc i) :
    Group.IsSolvable (pairProducts (D.ρ i).range a b) ∨
      ∃ m, 5 ≤ m ∧ Nonempty (pairProducts (D.ρ i).range a b ≃* alternatingGroup (Fin m)) := by
  rcases D.factor i with ⟨hA, h7⟩ | hSE
  · right
    have hAN : alternatingGroup (D.Ψc i) ≤ (D.ρ i).range := hA ▸ Subgroup.map_le_range _ _
    have hs := D.rho_mem_longInv D.t_mem i
    have hsN : D.ρ i ⟨D.t, mem_jHull_of_mem_longInv D.t_mem⟩ ∈ (D.ρ i).range := ⟨_, rfl⟩
    rcases eq_or_ne a b with rfl | hab
    · have hJ := longInv_perm_subset_of_alternatingGroup_le hAN hsN hs
      have hsw : ∀ x, x ∈ swapSet (D.ρ i).range a a ↔ x ∈ longInvAt (Perm (D.Ψc i)) (D.Ψc i) a :=
        fun x => ⟨fun hx => ⟨hx.2.1, hx.2.2⟩, fun hx => ⟨hJ hx.1, hx.1, hx.2⟩⟩
      have hP : pairProducts (D.ρ i).range a a =
          alternatingGroup (D.Ψc i) ⊓ stabilizer (Perm (D.Ψc i)) a := by
        rw [← closure_mul_longInvAt_perm_eq (D.odd_card_Ψc i) h7 a, pairProducts]
        simp_rw [hsw]
      rw [hP]
      exact ⟨_, by omega, nonempty_alternatingGroup_inf_stabilizer_mulEquiv a⟩
    · rw [pairProducts_eq_of_alternatingGroup_le hAN hsN hs hab]
      exact ⟨_, by omega, nonempty_alternatingGroup_inf_stabilizer_pair_mulEquiv hab⟩
  · left
    have hR := D.range_rho_of_not_isOuterFactor hSE.not_isOuterFactor
    have hle := pairProducts_le (D.ρ i).range a b
    rw [hR] at hle ⊢
    obtain ⟨n, k, e, hB⟩ := hSE.exists_isBenderAction
    have := hB.isSolvable_stabilizer_pair a b
    have hPM : pairProducts (D.M i) a b ≤ D.M i := fun x hx => (hle hx).1.1
    let φ : pairProducts (D.M i) a b →* stabilizer (D.M i) ({a, b} : Set (D.Ψc i)) :=
      (Subgroup.inclusion hPM).codRestrict _ fun x => by
        have h := hle x.2
        rw [mem_stabilizer_iff, Set.smul_set_insert, Set.smul_set_singleton]
        have ha : (Subgroup.inclusion hPM x) • a = a := h.1.2
        have hb : (Subgroup.inclusion hPM x) • b = b := h.2
        rw [ha, hb]
    refine Group.isSolvable_of_isSolvable_injective (f := φ) fun x y hxy => ?_
    have := congrArg (fun z : stabilizer (D.M i) ({a, b} : Set (D.Ψc i)) => ((z : D.M i) :
      Perm (D.Ψc i))) hxy
    exact Subtype.ext this

end Factors

section AFL

private theorem isSolvable_of_card_le_two {Q : Type*} [Group Q] [Finite Q]
    (h : Nat.card Q ≤ 2) : Group.IsSolvable Q := by
  have h0 : 0 < Nat.card Q := Nat.card_pos
  interval_cases hQ : Nat.card Q
  · have : Subsingleton Q := (Nat.card_eq_one_iff_unique.mp hQ).1
    exact Group.isSolvable_of_comm fun a b => Subsingleton.elim _ _
  · have : Fact (Nat.card Q).Prime := ⟨hQ ▸ Nat.prime_two⟩
    have : IsCyclic Q := isCyclic_of_prime_card rfl
    exact Group.isSolvable_of_comm fun a b => IsCyclic.commGroup.mul_comm a b

theorem closure_preimage_eq_subgroupOf {G : Type*} [Group G] {H : Subgroup G} {s : Set G}
    (hs : s ⊆ H) : Subgroup.closure ((↑) ⁻¹' s : Set H) = (Subgroup.closure s).subgroupOf H := by
  have hs' : s ⊆ Set.range (Subtype.val : H → G) := by
    rw [Subtype.range_coe_subtype]
    exact hs
  apply Subgroup.map_injective H.subtype_injective
  rw [MonoidHom.map_closure, Subgroup.subgroupOf_map_subtype, Subgroup.coe_subtype,
    Set.image_preimage_eq_of_subset hs', inf_of_le_left ((Subgroup.closure_le H).mpr hs)]

variable {G : Type*} [Group G] [Finite G] {Ω : Type*} [MulAction G Ω]

theorem HoltData.isSolvable_jOrbitKernel (D : HoltData G Ω) :
    Group.IsSolvable (jOrbitKernel G Ω) := by
  set O := (jOddCore G Ω).subgroupOf (jOrbitKernel G Ω)
  have : Group.IsSolvable O := by
    have hodd : Odd (Nat.card O) := by
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe jOddCore_le_jOrbitKernel).toEquiv]
      exact odd_card_jOddCore
    exact CFSG.FeitThompson.isSolvable_of_odd_natCard _ hodd
  have : Group.IsSolvable (jOrbitKernel G Ω ⧸ O) :=
    isSolvable_of_card_le_two D.relIndex_jOddCore_jOrbitKernel_le_two
  exact Group.isSolvable_of_subgroup_quotient O

theorem HoltData.exists_mulEquiv_alternatingGroup (D : HoltData G Ω) (α β : Ω)
    {L : Subgroup (Subgroup.closure (longInvSwap G Ω α β))} (hL : L.Normal)
    {N : Type*} [Group N] [IsSimpleGroup N] (hN : ∃ a b : N, a * b ≠ b * a)
    {ψ : L →* N} (hψ : Function.Surjective ψ) :
    ∃ m : ℕ, 5 ≤ m ∧ Nonempty (N ≃* alternatingGroup (Fin m)) := by
  classical
  obtain ⟨s, hs⟩ : (longInvSwap G Ω α β).Nonempty := by
    by_contra hne
    rw [Set.not_nonempty_iff_eq_empty] at hne
    have h1 : ∀ x : L, x = 1 := fun x => by
      have hx : ((x : Subgroup.closure (longInvSwap G Ω α β)) : G) ∈ (⊥ : Subgroup G) := by
        rw [← Subgroup.closure_empty, ← hne]
        exact (x : Subgroup.closure (longInvSwap G Ω α β)).2
      exact Subtype.ext (Subtype.ext (Subgroup.mem_bot.mp hx))
    refine not_subsingleton_of_ne_comm hN ⟨fun a b => ?_⟩
    obtain ⟨x, rfl⟩ := hψ a
    obtain ⟨y, rfl⟩ := hψ b
    rw [h1 x, h1 y]
  have hCH : Subgroup.closure (longInvSwap G Ω α β) ≤ jHull G Ω :=
    Subgroup.closure_mono fun t ht => ht.1
  set e : Subgroup.closure (longInvSwap G Ω α β) →* jHull G Ω := Subgroup.inclusion hCH
  set f : Subgroup.closure (longInvSwap G Ω α β) →* (∀ i, Perm (D.Ψc i)) :=
    (MonoidHom.pi D.ρ).comp e
  have hf : Group.IsSolvable f.ker := by
    have := D.isSolvable_jOrbitKernel
    let k : f.ker →* jOrbitKernel G Ω :=
      ((Subgroup.closure (longInvSwap G Ω α β)).subtype.comp f.ker.subtype).codRestrict _
        fun x => (D.mem_jOrbitKernel_iff_rho (h := e x)).mpr fun i => congrFun (x.2 : f x = 1) i
    refine Group.isSolvable_of_isSolvable_injective (f := k) fun x y hxy => ?_
    have := congrArg Subtype.val hxy
    exact Subtype.ext (Subtype.ext this)
  obtain ⟨ψ₁, hψ₁⟩ := exists_surjective_map_of_isSolvable_ker hf hψ hN
  set Q := (Subgroup.closure ((↑) ⁻¹' longInvSwap G Ω α β : Set (jHull G Ω))).map
    (MonoidHom.pi D.ρ)
  have he : e.range = (Subgroup.closure (longInvSwap G Ω α β)).subgroupOf (jHull G Ω) := by
    ext x
    rw [MonoidHom.mem_range, Subgroup.mem_subgroupOf]
    refine ⟨fun ⟨c, hc⟩ => ?_, fun hx => ⟨⟨x, hx⟩, rfl⟩⟩
    rw [← hc]
    exact c.2
  have hrange : f.range = Q := by
    rw [MonoidHom.range_comp, he,
      ← closure_preimage_eq_subgroupOf fun t ht => mem_jHull_of_mem_longInv ht.1]
  set P := Subgroup.pi Set.univ fun i => pairProducts (D.ρ i).range (D.coord α i) (D.coord β i)
  have hLQ : L.map f ≤ Q := hrange ▸ Subgroup.map_le_range f L
  have hLn : ∀ q ∈ Q, ∀ x ∈ L.map f, q * x * q⁻¹ ∈ L.map f := by
    rintro q hq _ ⟨l, hl, rfl⟩
    obtain ⟨c, rfl⟩ : q ∈ f.range := hrange ▸ hq
    exact ⟨c * l * c⁻¹, hL.conj_mem l hl c, by rw [map_mul, map_mul, map_inv]⟩
  have hs' : ((⟨s, mem_jHull_of_mem_longInv hs.1⟩ : jHull G Ω) : G) ∈ longInvSwap G Ω α β := hs
  obtain ⟨ψ₂, hψ₂⟩ := exists_surjective_inf_of_relIndex_le_two hLQ
    (D.relIndex_pi_pairProducts_le_two hs') hψ₁ hN
  have hPQ : P ≤ Q := D.pi_pairProducts_le_map_closure ⟨s, hs⟩
  obtain ⟨i, M, hMP, hMn, ψ₃, hψ₃⟩ := exists_surjective_of_le_pi (L := L.map f ⊓ P)
    inf_le_right (fun p hp x hx => ⟨hLn p (hPQ hp) x hx.1,
      P.mul_mem (P.mul_mem hp hx.2) (P.inv_mem hp)⟩) hψ₂ hN
  rcases D.isSolvable_or_alternating_pairProducts i (D.coord α i) (D.coord β i) with
    hsol | ⟨m, hm, ⟨φ⟩⟩
  · have : Group.IsSolvable M :=
      Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective hMP)
    exact absurd this (not_isSolvable_of_surjective_of_ne_comm hψ₃ hN)
  · have : IsSimpleGroup (alternatingGroup (Fin m)) :=
      alternatingGroup.isSimpleGroup (by rwa [Nat.card_eq_fintype_card, Fintype.card_fin])
    have : IsSimpleGroup (pairProducts (D.ρ i).range (D.coord α i) (D.coord β i)) :=
      φ.isSimpleGroup
    rcases eq_bot_or_eq_of_le_of_isSimpleGroup hMP hMn with hM | hM
    · exfalso
      refine not_subsingleton_of_ne_comm hN ⟨fun a b => ?_⟩
      have h1 : ∀ x : M, x = 1 := fun x => Subtype.ext (Subgroup.mem_bot.mp (hM ▸ x.2))
      obtain ⟨x, rfl⟩ := hψ₃ a
      obtain ⟨y, rfl⟩ := hψ₃ b
      rw [h1 x, h1 y]
    · have : IsSimpleGroup M := (MulEquiv.subgroupCongr hM).isSimpleGroup
      obtain ⟨χ⟩ := nonempty_mulEquiv_of_surjective_of_ne_comm hψ₃ hN
      exact ⟨m, hm, ⟨χ.symm.trans ((MulEquiv.subgroupCongr hM).trans φ)⟩⟩

end AFL

end CFSG.Holt.H78
