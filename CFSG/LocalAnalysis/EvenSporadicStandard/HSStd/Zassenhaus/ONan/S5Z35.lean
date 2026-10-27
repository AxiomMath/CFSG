module

public import Mathlib.GroupTheory.IsPerfect
public import CFSG.GroupTheory.OrderBelowSixtySolvable
import CFSG.Mathlib.GroupTheory.PermCommute

public section

namespace CFSG.EvenSporadicStandard.HSStd.Zassenhaus.ONan.S5

open Subgroup Equiv.Perm

abbrev Z35 : Type := Multiplicative (ZMod 3) × Equiv.Perm (Fin 5)

private abbrev A5z35 : Subgroup Z35 :=
  (alternatingGroup (Fin 5)).map (MonoidHom.inr (Multiplicative (ZMod 3)) (Equiv.Perm (Fin 5)))

private lemma inr_injective_z35 :
    Function.Injective (MonoidHom.inr (Multiplicative (ZMod 3)) (Equiv.Perm (Fin 5))) := by
  intro a b h
  simpa using congrArg Prod.snd h

private lemma nat_card_alternatingGroup_five : Nat.card (alternatingGroup (Fin 5)) = 60 := by
  rw [nat_card_alternatingGroup, Nat.card_eq_fintype_card]
  decide

private lemma five_le_card_fin5 : 5 ≤ Nat.card (Fin 5) := by
  rw [Nat.card_eq_fintype_card]
  norm_num

private lemma nat_card_A5z35 : Nat.card A5z35 = 60 := by
  rw [A5z35, Subgroup.card_map_of_injective inr_injective_z35,
    nat_card_alternatingGroup_five]

private theorem isPerfect_of_simple {G : Type*} [Group G] (hG : IsSimpleGroup G)
    (hcomm : ∃ x y : G, x * y ≠ y * x) : Group.IsPerfect G := by
  rw [Group.isPerfect_def]
  haveI : (commutator G).Normal := inferInstance
  rcases hG.eq_bot_or_eq_top_of_normal (commutator G) with h | h
  · exfalso
    have hc : Subgroup.center G = ⊤ := (commutator_eq_bot_iff_center_eq_top G).mp h
    obtain ⟨x, y, hxy⟩ := hcomm
    refine hxy ?_
    have hx : x ∈ Subgroup.center G := by rw [hc]; trivial
    exact (Subgroup.mem_center_iff.mp hx y).symm
  · exact h

private theorem eq_A5z35_of_simple {K : Subgroup Z35} (hK : IsSimpleGroup ↥K)
    (hK' : ∃ x ∈ K, ∃ y ∈ K, x * y ≠ y * x) : K = A5z35 := by
  haveI : IsSimpleGroup ↥K := hK
  haveI : Group.IsPerfect ↥K := by
    refine isPerfect_of_simple hK ?_
    obtain ⟨x, hx, y, hy, hne⟩ := hK'
    exact ⟨⟨x, hx⟩, ⟨y, hy⟩, fun h => hne (by simpa using congrArg Subtype.val h)⟩
  have hperfself : ⁅K, K⁆ = K := Subgroup.commutator_eq_self (H := K)
  have hle : K ≤ A5z35 := by
    let ψ : Z35 →* Multiplicative (ZMod 3) × ℤˣ :=
      MonoidHom.prodMap (MonoidHom.id (Multiplicative (ZMod 3)))
        (Equiv.Perm.sign (α := Fin 5))
    have hcomm : ⁅K, K⁆ ≤ ψ.ker := by
      rw [Subgroup.commutator_le]
      intro a _ha b _hb
      rw [MonoidHom.mem_ker, map_commutatorElement]
      exact commutatorElement_eq_one_iff_mul_comm.mpr (mul_comm _ _)
    rw [hperfself] at hcomm
    intro k hk
    have hkker : k ∈ ψ.ker := hcomm hk
    rw [MonoidHom.mem_ker] at hkker
    have hpair : (k.1, Equiv.Perm.sign k.2) = (1, 1) := by
      simpa [ψ, MonoidHom.coe_prodMap, Prod.map] using hkker
    have h1 : k.1 = 1 := congrArg Prod.fst hpair
    have h2 : Equiv.Perm.sign k.2 = 1 := congrArg Prod.snd hpair
    rw [Subgroup.mem_map]
    exact ⟨k.2, Equiv.Perm.mem_alternatingGroup.mpr h2, Prod.ext h1.symm rfl⟩
  have hcardK : Nat.card K = 60 := by
    by_contra hne
    have hne' : K ≠ A5z35 := fun h => hne (by rw [h, nat_card_A5z35])
    have hlt : K < A5z35 := lt_of_le_of_ne hle hne'
    have hca : Nat.card K < 60 := by
      rw [← nat_card_A5z35]
      exact Subgroup.card_lt_of_lt hlt
    have hsolv : Group.IsSolvable ↥K :=
      CFSG.GroupTheory.groups_order_below_sixty_solvable (G := ↥K) hca
    exact Group.IsPerfect.not_isSolvable (G := ↥K) hsolv
  exact Subgroup.eq_of_le_of_card_ge hle
    (by rw [nat_card_A5z35]; exact le_of_eq hcardK.symm)

theorem card_z35 : Nat.card Z35 = 360 := by
  rw [Nat.card_prod, Nat.card_eq_fintype_card, Nat.card_eq_fintype_card,
    Fintype.card_multiplicative, ZMod.card, Fintype.card_perm, Fintype.card_fin]
  decide

theorem eq_bot_of_normal_of_coprime_z35 {K : Subgroup Z35} (hK : K.Normal)
    (hc : Nat.Coprime 3 (Nat.card K)) : K = ⊥ := by
  let f : Z35 →* Equiv.Perm (Fin 5) := MonoidHom.snd _ _
  have hf : Function.Surjective f := fun x => ⟨(1, x), rfl⟩
  haveI hKf : (K.map f).Normal := hK.map f hf
  have hc' : Nat.Coprime 3 (Nat.card (K.map f)) :=
    hc.of_dvd_right (Subgroup.card_map_dvd K f)
  have hbot : K.map f = ⊥ := by
    by_contra hne
    haveI : Nontrivial (K.map f) := (Subgroup.nontrivial_iff_ne_bot _).mpr hne
    have hle := Equiv.Perm.alternatingGroup_le_of_normal (α := Fin 5) five_le_card_fin5
      (N := K.map f) (inferInstance : Nontrivial (K.map f))
    have h60 : Nat.card (alternatingGroup (Fin 5)) = 60 :=
      nat_card_alternatingGroup_five
    have hdvd : (60 : ℕ) ∣ Nat.card (K.map f) :=
      h60 ▸ Subgroup.card_dvd_of_le hle
    exact (Nat.prime_three.coprime_iff_not_dvd.mp hc')
      (dvd_trans (by norm_num : 3 ∣ 60) hdvd)
  have hle_ker : K ≤ f.ker := (Subgroup.map_eq_bot_iff K).mp hbot
  let φ : ↥K →* Multiplicative (ZMod 3) := (MonoidHom.fst _ _).comp K.subtype
  have hφ : Function.Injective φ := by
    intro a b hab
    have h1 : a.1.1 = b.1.1 := by simpa [φ] using hab
    have h2 : a.1.2 = 1 := by
      have hmem := hle_ker a.2
      change a.1 ∈ (MonoidHom.snd (Multiplicative (ZMod 3)) (Equiv.Perm (Fin 5))).ker at hmem
      rw [MonoidHom.ker_snd, Subgroup.mem_prod, Subgroup.mem_bot] at hmem
      exact hmem.2
    have h3 : b.1.2 = 1 := by
      have hmem := hle_ker b.2
      change b.1 ∈ (MonoidHom.snd (Multiplicative (ZMod 3)) (Equiv.Perm (Fin 5))).ker at hmem
      rw [MonoidHom.ker_snd, Subgroup.mem_prod, Subgroup.mem_bot] at hmem
      exact hmem.2
    exact Subtype.ext (Prod.ext h1 (by rw [h2, h3]))
  have hdvd3 : Nat.card ↥K ∣ Nat.card (Multiplicative (ZMod 3)) :=
    Subgroup.card_dvd_of_injective φ hφ
  have hcard3 : Nat.card (Multiplicative (ZMod 3)) = 3 := by
    rw [Nat.card_eq_fintype_card, Fintype.card_multiplicative, ZMod.card]
  rw [hcard3] at hdvd3
  exact Subgroup.eq_bot_of_card_eq K (Nat.eq_one_of_dvd_coprimes hc hdvd3 dvd_rfl)

theorem exists_simple_z35 :
    ∃ K : Subgroup Z35, IsSimpleGroup ↥K ∧ ∃ x ∈ K, ∃ y ∈ K, x * y ≠ y * x := by
  let g : Equiv.Perm (Fin 5) →* Z35 :=
    MonoidHom.inr (Multiplicative (ZMod 3)) (Equiv.Perm (Fin 5))
  have hg : Function.Injective g := inr_injective_z35
  let σ : Equiv.Perm (Fin 5) := Equiv.swap (0 : Fin 5) 1 * Equiv.swap (0 : Fin 5) 2
  let τ : Equiv.Perm (Fin 5) := Equiv.swap (0 : Fin 5) 1 * Equiv.swap (0 : Fin 5) 3
  have hσ : σ ∈ alternatingGroup (Fin 5) :=
    (Equiv.Perm.isThreeCycle_swap_mul_swap_same (a := (0 : Fin 5)) (b := 1) (c := 2)
      (by decide) (by decide) (by decide)).mem_alternatingGroup
  have hτ : τ ∈ alternatingGroup (Fin 5) :=
    (Equiv.Perm.isThreeCycle_swap_mul_swap_same (a := (0 : Fin 5)) (b := 1) (c := 3)
      (by decide) (by decide) (by decide)).mem_alternatingGroup
  have hsimp : IsSimpleGroup ↥A5z35 := by
    haveI : IsSimpleGroup ↥(alternatingGroup (Fin 5)) := alternatingGroup.isSimpleGroup (by simp)
    exact (Subgroup.equivMapOfInjective (alternatingGroup (Fin 5)) g hg).symm.isSimpleGroup
  have hne : σ * τ ≠ τ * σ := by decide
  refine ⟨A5z35, hsimp, g σ, Subgroup.mem_map.mpr ⟨σ, hσ, rfl⟩,
    g τ, Subgroup.mem_map.mpr ⟨τ, hτ, rfl⟩, ?_⟩
  intro h
  exact hne (hg (by rw [map_mul, map_mul]; exact h))

theorem eq_of_simple_z35 {K L : Subgroup Z35} (hK : IsSimpleGroup ↥K)
    (hK' : ∃ x ∈ K, ∃ y ∈ K, x * y ≠ y * x) (hL : IsSimpleGroup ↥L)
    (hL' : ∃ x ∈ L, ∃ y ∈ L, x * y ≠ y * x) : K = L := by
  rw [eq_A5z35_of_simple hK hK', eq_A5z35_of_simple hL hL']

theorem eq_zpowers_of_normal_z35 {M : Subgroup Z35} (hM : M.Normal) {z : Z35}
    (hz : ∀ y : Z35, y * z = z * y) (hz3 : orderOf z = 3) (hzM : z ∈ M)
    (h9 : ¬ 9 ∣ Nat.card M) : M = zpowers z := by
  have hz_snd : z.2 = 1 := by
    apply CFSG.perm_eq_one_of_forall_commute (by simp)
    intro τ
    have h := hz (1, τ)
    have h' : τ * z.2 = z.2 * τ := by
      have := congrArg Prod.snd h
      simpa [Prod.mul_def, Prod.snd_mul] using this
    exact h'.symm
  have hz1ne : z.1 ≠ 1 := by
    intro h
    have hz_eq : z = 1 := Prod.ext h hz_snd
    rw [hz_eq, orderOf_one] at hz3
    norm_num at hz3
  let f : Z35 →* Multiplicative (ZMod 3) := MonoidHom.fst _ _
  let K : Subgroup Z35 := M ⊓ f.ker
  let g : ↥M →* Multiplicative (ZMod 3) := f.comp M.subtype
  have hker : g.ker = K.subgroupOf M := by
    show (f.comp M.subtype).ker = (M ⊓ f.ker).subgroupOf M
    rw [← MonoidHom.comap_ker, Subgroup.comap_subtype,
      ← Subgroup.inf_subgroupOf_left (H := f.ker) (K := M)]
  have hcardK : Nat.card g.ker = Nat.card K := by
    rw [hker]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe (inf_le_left : K ≤ M)).toEquiv
  have hcard_mult : Nat.card (Multiplicative (ZMod 3)) = 3 := by
    rw [Nat.card_eq_fintype_card, Fintype.card_multiplicative, ZMod.card]
  have hrange_ne : g.range ≠ ⊥ := by
    intro hbot
    have hmem : g ⟨z, hzM⟩ ∈ (⊥ : Subgroup (Multiplicative (ZMod 3))) := by
      rw [← hbot]
      exact ⟨⟨z, hzM⟩, rfl⟩
    rw [Subgroup.mem_bot] at hmem
    exact hz1ne (by simpa [g, f] using hmem)
  have hrange : Nat.card g.range = 3 := by
    have hdvd : Nat.card g.range ∣ Nat.card (Multiplicative (ZMod 3)) := by
      simpa [Subgroup.card_top] using Subgroup.card_dvd_of_le (le_top : g.range ≤ ⊤)
    rw [hcard_mult] at hdvd
    rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h1 | h3
    · exact absurd (Subgroup.eq_bot_of_card_eq (g.range) h1) hrange_ne
    · exact h3
  have hcardM : Nat.card M = 3 * Nat.card K := by
    have h := Subgroup.card_ker_mul_card_range g
    rw [hcardK, hrange] at h
    rw [← h, Nat.mul_comm]
  have hcop : Nat.Coprime 3 (Nat.card K) := by
    rw [Nat.prime_three.coprime_iff_not_dvd]
    intro h3dvd
    apply h9
    obtain ⟨k, hk⟩ := h3dvd
    refine ⟨k, ?_⟩
    rw [hcardM, hk]
    ring
  haveI : M.Normal := hM
  have hK_normal : K.Normal := by
    show (M ⊓ f.ker).Normal
    infer_instance
  have hKbot : K = ⊥ := eq_bot_of_normal_of_coprime_z35 hK_normal hcop
  have hcardM3 : Nat.card M = 3 := by
    rw [hcardM, hKbot, Subgroup.card_bot, mul_one]
  have hzle : zpowers z ≤ M := zpowers_le.mpr hzM
  have hcardZ : Nat.card (zpowers z) = 3 := by rw [Nat.card_zpowers, hz3]
  refine (Subgroup.eq_of_le_of_card_ge hzle ?_).symm
  omega

theorem exists_simple_le_of_mulEquiv {Y : Type*} [Group Y] {C : Subgroup Y} (e : ↥C ≃* Z35) :
    ∃ K : Subgroup Y, K ≤ C ∧ IsSimpleGroup ↥K ∧ ∃ x ∈ K, ∃ y ∈ K, x * y ≠ y * x := by
  obtain ⟨K₀, hK₀simp, x₀, hx₀, y₀, hy₀, hne₀⟩ := exists_simple_z35
  let K₁ : Subgroup ↥C := K₀.map e.symm.toMonoidHom
  let K : Subgroup Y := K₁.map C.subtype
  have hKC : K ≤ C := Subgroup.map_subtype_le K₁
  have hsimp : IsSimpleGroup ↥K := by
    haveI : IsSimpleGroup ↥K₀ := hK₀simp
    have h₁ : IsSimpleGroup ↥K₁ :=
      (Subgroup.equivMapOfInjective K₀ e.symm.toMonoidHom e.symm.injective).symm.isSimpleGroup
    haveI : IsSimpleGroup ↥K₁ := h₁
    exact (Subgroup.equivMapOfInjective K₁ C.subtype C.subtype_injective).symm.isSimpleGroup
  let x : Y := C.subtype (e.symm x₀)
  let y : Y := C.subtype (e.symm y₀)
  have hxK : x ∈ K :=
    Subgroup.mem_map.mpr ⟨e.symm x₀, Subgroup.mem_map.mpr ⟨x₀, hx₀, rfl⟩, rfl⟩
  have hyK : y ∈ K :=
    Subgroup.mem_map.mpr ⟨e.symm y₀, Subgroup.mem_map.mpr ⟨y₀, hy₀, rfl⟩, rfl⟩
  have hne : x * y ≠ y * x := by
    intro h
    apply hne₀
    have h1 : e.symm x₀ * e.symm y₀ = e.symm y₀ * e.symm x₀ := by
      apply C.subtype_injective
      rw [map_mul, map_mul]
      simpa only [x, y] using h
    have := congrArg e h1
    simpa [map_mul] using this
  exact ⟨K, hKC, hsimp, x, hxK, y, hyK, hne⟩

theorem eq_of_simple_le_of_mulEquiv {Y : Type*} [Group Y] {C : Subgroup Y} (e : ↥C ≃* Z35)
    {K L : Subgroup Y} (hKC : K ≤ C) (hLC : L ≤ C) (hK : IsSimpleGroup ↥K)
    (hK' : ∃ x ∈ K, ∃ y ∈ K, x * y ≠ y * x) (hL : IsSimpleGroup ↥L)
    (hL' : ∃ x ∈ L, ∃ y ∈ L, x * y ≠ y * x) : K = L := by
  let K₀ : Subgroup Z35 := (K.subgroupOf C).map e.toMonoidHom
  let L₀ : Subgroup Z35 := (L.subgroupOf C).map e.toMonoidHom
  have hK₀simp : IsSimpleGroup ↥K₀ := by
    haveI : IsSimpleGroup ↥K := hK
    exact ((Subgroup.equivMapOfInjective (K.subgroupOf C) e.toMonoidHom e.injective).symm.trans
      (Subgroup.subgroupOfEquivOfLe hKC)).isSimpleGroup
  have hL₀simp : IsSimpleGroup ↥L₀ := by
    haveI : IsSimpleGroup ↥L := hL
    exact ((Subgroup.equivMapOfInjective (L.subgroupOf C) e.toMonoidHom e.injective).symm.trans
      (Subgroup.subgroupOfEquivOfLe hLC)).isSimpleGroup
  have hK₀' : ∃ x ∈ K₀, ∃ y ∈ K₀, x * y ≠ y * x := by
    obtain ⟨x, hxK, y, hyK, hne⟩ := hK'
    refine ⟨e ⟨x, hKC hxK⟩,
      Subgroup.mem_map.mpr ⟨⟨x, hKC hxK⟩, hxK, rfl⟩,
      e ⟨y, hKC hyK⟩,
      Subgroup.mem_map.mpr ⟨⟨y, hKC hyK⟩, hyK, rfl⟩, ?_⟩
    intro h
    apply hne
    have h' : (⟨x, hKC hxK⟩ : ↥C) * ⟨y, hKC hyK⟩ =
        ⟨y, hKC hyK⟩ * ⟨x, hKC hxK⟩ := by
      have heq : e ((⟨x, hKC hxK⟩ : ↥C) * ⟨y, hKC hyK⟩) =
          e (⟨y, hKC hyK⟩ * ⟨x, hKC hxK⟩) := by
        rw [map_mul, map_mul]
        exact h
      exact e.injective heq
    simpa using congrArg Subtype.val h'
  have hL₀' : ∃ x ∈ L₀, ∃ y ∈ L₀, x * y ≠ y * x := by
    obtain ⟨x, hxL, y, hyL, hne⟩ := hL'
    refine ⟨e ⟨x, hLC hxL⟩,
      Subgroup.mem_map.mpr ⟨⟨x, hLC hxL⟩, hxL, rfl⟩,
      e ⟨y, hLC hyL⟩,
      Subgroup.mem_map.mpr ⟨⟨y, hLC hyL⟩, hyL, rfl⟩, ?_⟩
    intro h
    apply hne
    have h' : (⟨x, hLC hxL⟩ : ↥C) * ⟨y, hLC hyL⟩ =
        ⟨y, hLC hyL⟩ * ⟨x, hLC hxL⟩ := by
      have heq : e ((⟨x, hLC hxL⟩ : ↥C) * ⟨y, hLC hyL⟩) =
          e (⟨y, hLC hyL⟩ * ⟨x, hLC hxL⟩) := by
        rw [map_mul, map_mul]
        exact h
      exact e.injective heq
    simpa using congrArg Subtype.val h'
  have hKL : K₀ = L₀ := eq_of_simple_z35 hK₀simp hK₀' hL₀simp hL₀'
  have h₁ : K.subgroupOf C = L.subgroupOf C := by
    apply Subgroup.map_injective (f := e.toMonoidHom) e.injective
    exact hKL
  have h₂ : K ⊓ C = L ⊓ C := Subgroup.subgroupOf_inj.mp h₁
  rw [← inf_eq_left.mpr hKC, ← inf_eq_left.mpr hLC]
  exact h₂

theorem inf_eq_zpowers_of_mulEquiv {Y : Type*} [Group Y] {C : Subgroup Y} (e : ↥C ≃* Z35)
    {c : Y} (hcC : c ∈ C) (hc : ∀ y ∈ C, y * c = c * y) (hc3 : orderOf c = 3)
    {M : Subgroup Y} (hM : C ≤ normalizer (M : Set Y)) (hcM : c ∈ M)
    (h9 : ¬ 9 ∣ Nat.card ↥(M ⊓ C)) : M ⊓ C = zpowers c := by
  let c' : ↥C := ⟨c, hcC⟩
  let z : Z35 := e c'
  let M' : Subgroup Z35 := (M.subgroupOf C).map e.toMonoidHom
  have hM'_normal : M'.Normal := by
    have hnormal : (M.subgroupOf C).Normal :=
      ⟨fun n hn k => by
        rw [Subgroup.mem_subgroupOf] at hn ⊢
        exact (Subgroup.mem_normalizer_iff.mp (hM k.2) n.1).mp hn⟩
    exact hnormal.map e.toMonoidHom e.surjective
  have hz_central : ∀ y : Z35, y * z = z * y := by
    intro y
    have hcc : (e.symm y) * c' = c' * (e.symm y) := by
      apply Subtype.ext
      simpa using hc (e.symm y).1 (e.symm y).2
    calc
      y * z = e (e.symm y) * e c' := by simp [z]
      _ = e (e.symm y * c') := (map_mul e _ _).symm
      _ = e (c' * e.symm y) := by rw [hcc]
      _ = e c' * e (e.symm y) := map_mul e _ _
      _ = z * y := by simp [z]
  have hz3 : orderOf z = 3 := by
    have h1 : orderOf z = orderOf c' := MulEquiv.orderOf_eq e c'
    have h2 : orderOf c' = orderOf c := Subgroup.orderOf_mk c hcC
    rw [h1, h2, hc3]
  have hzM' : z ∈ M' :=
    Subgroup.mem_map.mpr ⟨c', Subgroup.mem_subgroupOf.mpr hcM, rfl⟩
  have hcardM' : Nat.card M' = Nat.card ↥(M ⊓ C) := by
    show Nat.card ((M.subgroupOf C).map e.toMonoidHom) = Nat.card ↥(M ⊓ C)
    rw [Subgroup.card_map_of_injective e.injective]
    rw [← Subgroup.inf_subgroupOf_right M C]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe (inf_le_right : M ⊓ C ≤ C)).toEquiv
  have h9' : ¬ 9 ∣ Nat.card M' := by rwa [hcardM']
  have hM'eq : M' = zpowers z :=
    eq_zpowers_of_normal_z35 hM'_normal hz_central hz3 hzM' h9'
  have hsub : M.subgroupOf C = zpowers c' := by
    apply Subgroup.map_injective (f := e.toMonoidHom) e.injective
    rw [MonoidHom.map_zpowers]
    exact hM'eq
  have h := congrArg (Subgroup.map C.subtype) hsub
  rw [Subgroup.subgroupOf_map_subtype, MonoidHom.map_zpowers] at h
  exact h

end CFSG.EvenSporadicStandard.HSStd.Zassenhaus.ONan.S5
