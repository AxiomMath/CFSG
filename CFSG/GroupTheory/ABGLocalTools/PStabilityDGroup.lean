module

public import CFSG.GroupTheory.PStableAction
import CFSG.GroupTheory.ABGLocalTools.RelativeStability
import CFSG.GroupTheory.QuasiDihedralFusion.OddKernel
import CFSG.LinearAlgebra.LinearGroups.OddPStableActions
public import CFSG.GroupTheory.ABGLocalTools.Constraint
public import CFSG.GroupTheory.QuasiDihedralFusion.Defs

public section

open Subgroup
open scoped commutatorElement

namespace CFSG.ABGLocalTools

open CFSG.QuasiDihedralFusion CFSG.GroupTheory

variable {H : Type*} [Group H] {p : ℕ}

section Transfer

omit [Group H] in
theorem map_pCore_le_of_injective_of_normal {X Y : Type*} [Group X] [Group Y] (f : X →* Y)
    (hf : Function.Injective f) (hn : f.range.Normal) : (pCore p X).map f ≤ pCore p Y := by
  have h1 : (pCore p X).map f = (pCore p f.range).map f.range.subtype := by
    rw [← pCore_map_iso p (MonoidHom.ofInjective hf), Subgroup.map_map]
    rfl
  rw [h1]
  exact le_sSup ⟨inferInstance, (pCore_isPGroup (G := f.range) (p := p)).map _⟩

noncomputable def comapNormalizerConj {G : Type*} [Group G] (ι : G →* H) (P : Subgroup H) :
    (normalizer (P : Set H)).comap ι →* MulAut P :=
  (normalizerMonoidHom P).comp (ι.subgroupComap (normalizer (P : Set H)))

theorem comapNormalizerConj_apply_coe {G : Type*} [Group G] (ι : G →* H) (P : Subgroup H)
    (m : (normalizer (P : Set H)).comap ι) (u : P) :
    ((comapNormalizerConj ι P m u : P) : H) = ι m * u * (ι m)⁻¹ := by
  rw [comapNormalizerConj, MonoidHom.comp_apply, normalizerMonoidHom_apply_apply_coe]
  rfl

theorem comapNormalizerConj_eq_one_iff {G : Type*} [Group G] (ι : G →* H) (P : Subgroup H)
    (m : (normalizer (P : Set H)).comap ι) :
    comapNormalizerConj ι P m = 1 ↔ ι m ∈ centralizer (P : Set H) := by
  rw [mem_centralizer_iff]
  constructor
  · intro h u hu
    have h' := congrArg (fun φ : MulAut P => ((φ ⟨u, hu⟩ : P) : H)) h
    simp only [comapNormalizerConj_apply_coe, MulAut.one_apply] at h'
    calc u * ι m = ι m * u * (ι m)⁻¹ * ι m := by rw [h']
      _ = ι m * u := by group
  · intro h
    ext u
    rw [comapNormalizerConj_apply_coe, MulAut.one_apply]
    have hu : (u : H) * ι m = ι m * u := h u.1 u.2
    calc ι m * u * (ι m)⁻¹ = u * ι m * (ι m)⁻¹ := by rw [hu]
      _ = u := by group

theorem le_normalizerPCoreModCentralizer_of_isPStableAction {G : Type*} [Group G] (ι : G →* H)
    (hιn : ι.range.Normal) {P A : Subgroup H} (hAι : A ≤ ι.range)
    (hAN : A ≤ normalizer (P : Set H)) (hcomm : ⁅⁅P, A⁆, A⁆ = ⊥)
    (hstab : ∀ (M : Subgroup G) (ρ : M →* MulAut P), IsPStableAction p ρ) :
    A ≤ normalizerPCoreModCentralizer p P := by
  set N := normalizer (P : Set H) with hNdef
  set Cn := (centralizer (P : Set H)).subgroupOf N with hCndef
  set M := N.comap ι with hMdef
  set ψ : M →* N ⧸ Cn := (QuotientGroup.mk' Cn).comp (ι.subgroupComap N) with hψdef
  have hker : ∀ m : M, m ∈ (comapNormalizerConj ι P).ker ↔ m ∈ ψ.ker := by
    intro m
    rw [MonoidHom.mem_ker, MonoidHom.mem_ker, comapNormalizerConj_eq_one_iff, hψdef,
      MonoidHom.comp_apply, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, hCndef,
      mem_subgroupOf]
    rfl
  have hle : (comapNormalizerConj ι P).ker ≤ ψ.ker := fun m hm => (hker m).mp hm
  set ψbar : M ⧸ (comapNormalizerConj ι P).ker →* N ⧸ Cn :=
    QuotientGroup.lift (comapNormalizerConj ι P).ker ψ hle with hψbar
  have hψbar_inj : Function.Injective ψbar := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro y hy
    obtain ⟨m, rfl⟩ := QuotientGroup.mk_surjective y
    rw [MonoidHom.mem_ker, hψbar, QuotientGroup.lift_mk] at hy
    rw [Subgroup.mem_bot, QuotientGroup.eq_one_iff]
    exact (hker m).mpr hy
  have hrange : ψbar.range = (ι.range.subgroupOf N).map (QuotientGroup.mk' Cn) := by
    ext y
    constructor
    · rintro ⟨z, rfl⟩
      obtain ⟨m, rfl⟩ := QuotientGroup.mk_surjective z
      exact ⟨ι.subgroupComap N m, mem_subgroupOf.mpr ⟨m, rfl⟩, rfl⟩
    · rintro ⟨n, hn, rfl⟩
      obtain ⟨g, hg⟩ := mem_subgroupOf.mp hn
      have hgM : g ∈ M := by
        rw [hMdef, mem_comap, hg]
        exact n.2
      refine ⟨(⟨g, hgM⟩ : M), ?_⟩
      rw [hψbar, QuotientGroup.lift_mk, hψdef, MonoidHom.comp_apply]
      congr 1
      exact Subtype.ext hg
  have hnormal : ψbar.range.Normal := by
    rw [hrange]
    have : (ι.range.subgroupOf N).Normal := Subgroup.normal_subgroupOf
    exact this.map _ (QuotientGroup.mk'_surjective Cn)
  have hcore := map_pCore_le_of_injective_of_normal (p := p) ψbar hψbar_inj hnormal
  intro a ha
  obtain ⟨g, hg⟩ := hAι ha
  have hgM : g ∈ M := by
    rw [hMdef, mem_comap, hg]
    exact hAN ha
  have hm : (⟨g, hgM⟩ : M) ∈ actionPCore p (comapNormalizerConj ι P) := by
    apply hstab M (comapNormalizerConj ι P) ⟨g, hgM⟩
    intro u
    rw [double_commutator_eq_one_iff]
    apply Subtype.ext
    have hι1 : ι (((⟨g, hgM⟩ : M)⁻¹ : M) : G) = a⁻¹ := by
      rw [InvMemClass.coe_inv, map_inv]
      change (ι g)⁻¹ = a⁻¹
      rw [hg]
    have hc : ((u⁻¹ * comapNormalizerConj ι P (⟨g, hgM⟩ : M)⁻¹ u : P) : H) =
        ⁅(u : H)⁻¹, a⁻¹⁆ := by
      rw [Subgroup.coe_mul, Subgroup.coe_inv, comapNormalizerConj_apply_coe, hι1,
        commutatorElement_def, inv_inv, inv_inv]
      group
    rw [comapNormalizerConj_apply_coe, hι1, hc]
    have hmem : ⁅⁅(u : H)⁻¹, a⁻¹⁆, a⁻¹⁆ ∈ ⁅⁅P, A⁆, A⁆ :=
      commutator_mem_commutator (commutator_mem_commutator (inv_mem u.2) (inv_mem ha))
        (inv_mem ha)
    rw [hcomm, Subgroup.mem_bot, commutatorElement_eq_one_iff_commute] at hmem
    calc a⁻¹ * ⁅(u : H)⁻¹, a⁻¹⁆ * a⁻¹⁻¹ = ⁅(u : H)⁻¹, a⁻¹⁆ * a⁻¹ * a⁻¹⁻¹ := by
          rw [hmem.symm.eq]
      _ = ⁅(u : H)⁻¹, a⁻¹⁆ := by group
  rw [mem_normalizerPCoreModCentralizer_iff]
  refine ⟨hAN ha, ?_⟩
  have hmem := hcore ⟨QuotientGroup.mk' (comapNormalizerConj ι P).ker ⟨g, hgM⟩, hm, rfl⟩
  have hval : ψbar (QuotientGroup.mk' (comapNormalizerConj ι P).ker ⟨g, hgM⟩) =
      QuotientGroup.mk' Cn (⟨a, hAN ha⟩ : N) := by
    rw [hψbar, QuotientGroup.mk'_apply, QuotientGroup.lift_mk, hψdef, MonoidHom.comp_apply]
    congr 1
    exact Subtype.ext hg
  rw [hval] at hmem
  exact hmem

end Transfer

section AbelianTwoGroups

theorem isCyclic_of_isPGroup_two_of_comm {Q : Type*} [Group Q] [Finite Q] (hQ : IsPGroup 2 Q)
    (hcomm : ∀ a b : Q, a * b = b * a)
    (huniq : ∀ u v : Q, orderOf u = 2 → orderOf v = 2 → u = v) : IsCyclic Q := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hord : ∀ x : Q, ∃ i, orderOf x = 2 ^ i := fun x => by
    obtain ⟨i, -, hi⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp
      (orderOf_dvd_of_pow_eq_one (hQ x).choose_spec)
    exact ⟨i, hi⟩
  obtain ⟨g, hgmax⟩ := Finite.exists_max (fun x : Q => orderOf x)
  obtain ⟨j, hj⟩ := hord g
  have hpowj : ∀ x : Q, x ^ (2 ^ j) = 1 := by
    intro x
    obtain ⟨i, hi⟩ := hord x
    have hle : 2 ^ i ≤ 2 ^ j := hi ▸ hj ▸ hgmax x
    have hij : i ≤ j := (Nat.pow_le_pow_iff_right (by norm_num)).mp hle
    exact orderOf_dvd_iff_pow_eq_one.mp (hi ▸ Nat.pow_dvd_pow 2 hij)
  by_contra hcyc
  have hne : zpowers g ≠ ⊤ := by
    intro htop
    exact hcyc ⟨g, fun x => by
      have hx : x ∈ zpowers g := by rw [htop]; exact mem_top x
      exact mem_zpowers_iff.mp hx⟩
  have : (zpowers g).Normal := ⟨fun x hx y => by
    have hyx : y * x * y⁻¹ = x := by rw [hcomm y x, mul_inv_cancel_right]
    rw [hyx]
    exact hx⟩
  have hquot : IsPGroup 2 (Q ⧸ zpowers g) := hQ.to_quotient _
  have hnt : Nontrivial (Q ⧸ zpowers g) := by
    rw [QuotientGroup.nontrivial_iff]
    exact hne
  obtain ⟨k, hk⟩ := hquot.exists_card_eq
  have hk0 : k ≠ 0 := by
    rintro rfl
    rw [pow_zero] at hk
    exact (Finite.one_lt_card_iff_nontrivial.mpr hnt).ne' hk
  obtain ⟨hbar, hhbar⟩ := exists_prime_orderOf_dvd_card' (G := Q ⧸ zpowers g) 2
    (by rw [hk]; exact dvd_pow_self 2 hk0)
  obtain ⟨h, rfl⟩ := QuotientGroup.mk_surjective hbar
  have hh : h ∉ zpowers g := by
    intro hmem
    have : (h : Q ⧸ zpowers g) = 1 := (QuotientGroup.eq_one_iff h).mpr hmem
    rw [this, orderOf_one] at hhbar
    exact absurd hhbar (by norm_num)
  have hsq : h ^ 2 ∈ zpowers g := by
    rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_pow, ← hhbar, pow_orderOf_eq_one]
  obtain ⟨n, hn⟩ : ∃ n : ℕ, g ^ n = h ^ 2 :=
    Submonoid.mem_powers_iff _ _ |>.mp (mem_powers_iff_mem_zpowers.mpr hsq)
  have hj0 : j ≠ 0 := by
    rintro rfl
    apply hh
    have h1 : h = 1 := by simpa using hpowj h
    rw [h1]
    exact one_mem _
  have hsplit : 2 ^ j = 2 * 2 ^ (j - 1) := by
    rw [← pow_succ']
    congr 1
    omega
  have hn_even : 2 ∣ n := by
    have h2 : g ^ (n * 2 ^ (j - 1)) = 1 := by
      rw [pow_mul, hn, ← pow_mul, ← hsplit]
      exact hpowj h
    have h3 := orderOf_dvd_of_pow_eq_one h2
    rw [hj, hsplit, mul_comm n, mul_comm 2 (2 ^ (j - 1))] at h3
    exact Nat.dvd_of_mul_dvd_mul_left (pow_pos (by norm_num : 0 < 2) _) h3
  obtain ⟨n', rfl⟩ := hn_even
  set h' := h * (g ^ n')⁻¹ with hh'def
  have hh'sq : h' ^ 2 = 1 := by
    have hc : (g ^ n')⁻¹ * h = h * (g ^ n')⁻¹ := (hcomm h _).symm
    calc h' ^ 2 = h * ((g ^ n')⁻¹ * h) * (g ^ n')⁻¹ := by rw [hh'def, pow_two]; group
      _ = (h * h) * ((g ^ n') * (g ^ n'))⁻¹ := by rw [hc]; group
      _ = 1 := by
        rw [← pow_two, ← pow_two, ← pow_mul, mul_comm n' 2, hn, mul_inv_cancel]
  have hh'ne : h' ≠ 1 := by
    intro h1
    apply hh
    have : h = g ^ n' := by
      rw [hh'def, mul_inv_eq_one] at h1
      exact h1
    rw [this]
    exact pow_mem (mem_zpowers g) n'
  have hh'ord : orderOf h' = 2 := orderOf_eq_prime hh'sq hh'ne
  have hg2 : orderOf (g ^ (2 ^ (j - 1))) = 2 := by
    rw [orderOf_pow' g (pow_ne_zero _ (by norm_num)), hj, hsplit,
      Nat.gcd_mul_left_left, Nat.mul_div_cancel _ (pow_pos (by norm_num) _)]
  have heq := huniq _ _ hh'ord hg2
  apply hh
  have : h = g ^ (2 ^ (j - 1)) * g ^ n' := by
    rw [← heq, hh'def, inv_mul_cancel_right]
  rw [this]
  exact mul_mem (pow_mem (mem_zpowers g) _) (pow_mem (mem_zpowers g) n')

end AbelianTwoGroups

section DGroups

variable [Finite H]

theorem sections_cyclic_of_abelian_sylow {G : Type*} [Group G] [Finite G]
    (hab : ∀ P : Sylow 2 G, IsMulCommutative P) :
    ∀ D : Subgroup G, IsPGroup 2 D → ∀ (E : Subgroup D) [E.Normal],
      (∀ u v : D ⧸ E, orderOf u = 2 → orderOf v = 2 → u = v) → IsCyclic (D ⧸ E) := by
  intro D hD E _ huniq
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨P, hDP⟩ := hD.exists_le_sylow
  have hPc := hab P
  have hDc : ∀ a b : D, a * b = b * a := by
    intro a b
    have h := hPc.is_comm.comm (⟨a, hDP a.2⟩ : (P : Subgroup G)) ⟨b, hDP b.2⟩
    apply Subtype.ext
    have h' := congrArg Subtype.val h
    simpa using h'
  refine isCyclic_of_isPGroup_two_of_comm (hD.to_quotient E) ?_ huniq
  intro x y
  obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective x
  obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective y
  rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, hDc]

theorem exists_stable_kernel_of_isDGroup [Fact p.Prime] (hp : p ≠ 2) (hH : IsDGroup H)
    (Q : Type*) [Group Q] [Finite Q] (hQ : IsPGroup p Q) :
    ∃ K : Subgroup H, K.Normal ∧ (∀ X : Subgroup H, Odd (Nat.card X) → X ≤ K) ∧
      ∀ (M : Subgroup K) (ρ : M →* MulAut Q), IsPStableAction p ρ := by
  have hpp : p.Prime := Fact.out
  have hodd : Odd p := hpp.odd_of_ne_two hp
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rcases hH with ⟨hDih, -⟩ | ⟨K, hK⟩
  ·
    refine ⟨⊤, inferInstance, fun X _ => le_top, ?_⟩
    obtain ⟨S⟩ : Nonempty (Sylow 2 H) := inferInstance
    obtain ⟨m, hm, ⟨e⟩⟩ := hDih S
    obtain ⟨T, ⟨eT⟩⟩ := exists_sylow_equiv (Subgroup.topEquiv : (⊤ : Subgroup H) ≃* H) S
    have hT : Nonempty (DihedralGroup (2 ^ (m + 1 - 1)) ≃* (T : Subgroup (⊤ : Subgroup H))) := by
      rw [Nat.add_sub_cancel]
      exact ⟨(eT.trans e).symm⟩
    intro M ρ
    exact CFSG.LinearGroups.dihedral_subgroup_actions_are_odd_p_stable T (by omega) hT M hpp
      hodd Q hQ ρ
  · refine ⟨K, hK.normal, fun X hX => ?_, ?_⟩
    · have : K.Normal := hK.normal
      exact le_of_odd_of_two_pow_index K ⟨1, by rw [hK.index_eq_two, pow_one]⟩ X hX
    rcases hK.sylow with ⟨n, -, hKD⟩ | ⟨n, -, hab⟩
    ·
      obtain ⟨S⟩ : Nonempty (Sylow 2 K) := inferInstance
      obtain ⟨m, hm, ⟨e⟩⟩ := hKD S
      have hS : Nonempty (DihedralGroup (2 ^ (m + 1 - 1)) ≃* (S : Subgroup K)) := by
        rw [Nat.add_sub_cancel]
        exact ⟨e.symm⟩
      intro M ρ
      exact CFSG.LinearGroups.dihedral_subgroup_actions_are_odd_p_stable S (by omega) hS M hpp
        hodd Q hQ ρ
    ·
      intro M ρ
      exact CFSG.LinearGroups.cyclic_unique_involution_two_sections_have_stable_odd_prime_actions
        (sections_cyclic_of_abelian_sylow hab) M hpp hodd Q hQ ρ

theorem le_normalizerPCoreModCentralizer_of_isDGroup [Fact p.Prime] (hp : p ≠ 2)
    (hH : IsDGroup H) {P A : Subgroup H} (hP : IsPGroup p P) (hA : IsPGroup p A)
    (hAN : A ≤ normalizer (P : Set H)) (hcomm : ⁅⁅P, A⁆, A⁆ = ⊥) :
    A ≤ normalizerPCoreModCentralizer p P := by
  have hpp : p.Prime := Fact.out
  obtain ⟨K, hKn, hoddK, hstab⟩ := exists_stable_kernel_of_isDGroup hp hH P hP
  have hAodd : Odd (Nat.card A) := by
    obtain ⟨k, hk⟩ := hA.exists_card_eq
    rw [hk]
    exact (hpp.odd_of_ne_two hp).pow
  have hAK : A ≤ K := hoddK A hAodd
  refine le_normalizerPCoreModCentralizer_of_isPStableAction K.subtype ?_ ?_ hAN hcomm hstab
  · rw [K.range_subtype]
    exact hKn
  · rw [K.range_subtype]
    exact hAK

theorem isPStable_of_isDGroup [Fact p.Prime] (hp : p ≠ 2) (hH : IsDGroup H)
    (hOp : pCore p H ≠ ⊥) : IsPStable p H :=
  ⟨hOp, fun _ _ _ hP _ hA hAN hcomm =>
    le_normalizerPCoreModCentralizer_of_isDGroup hp hH hP hA hAN hcomm⟩

end DGroups

end CFSG.ABGLocalTools
