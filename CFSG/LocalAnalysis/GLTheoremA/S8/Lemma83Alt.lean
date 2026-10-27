module

public import CFSG.LocalAnalysis.GLTheoremA.S6.InputsAlt72
public import CFSG.LocalAnalysis.GLTheoremA.PartI.AltDown
public import CFSG.LocalAnalysis.GLTheoremA.PartI.AltDownPerm
public import CFSG.LocalAnalysis.GLTheoremA.PartI.AltDownComp

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup)
open CFSG.HardMathSupport.Solomon.LocalBalance (barAut)
open scoped commutatorElement

namespace S8.L83

variable {G : Type} [Group G] [Finite G]

theorem imageMod_mono {p : ℕ} {K I J : Subgroup G} (h : I ≤ J) : imageMod p K I ≤ imageMod p K J := by
  rintro _ ⟨x, hx, rfl⟩
  exact ⟨x, h hx, rfl⟩

theorem isPGroup_imageMod {p : ℕ} {K S : Subgroup G} (hS : IsPGroup 2 S) :
    IsPGroup 2 (imageMod p K S) :=
  (hS.comap_of_injective K.subtype K.subtype_injective).map _

theorem imageMod_le_normalizer {p : ℕ} {K I S : Subgroup G}
    (hIS : I ≤ Subgroup.normalizer (S : Set G)) :
    imageMod p K I ≤ Subgroup.normalizer (imageMod p K S : Set (PQuot p K)) := by
  refine le_trans ?_ (Subgroup.le_normalizer_map (QuotientGroup.mk' (GLAPPrimeCore p ↥K)))
  refine Subgroup.map_mono ?_
  intro x hx
  rw [Subgroup.mem_normalizer_iff]
  intro h
  rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
  exact (Subgroup.mem_normalizer_iff.1 (hIS (Subgroup.mem_subgroupOf.1 hx))) h

theorem barAut_pow_three {K : Subgroup G} {d : G} (hdK : d ∈ Subgroup.normalizer (K : Set G))
    (hd3 : d ^ 3 = 1) : (barAut 3 K ⟨d, hdK⟩) ^ 3 = 1 := by
  rw [← map_pow]
  have h : (⟨d, hdK⟩ : ↥(Subgroup.normalizer (K : Set G))) ^ 3 = 1 := Subtype.ext (by simpa using hd3)
  rw [h, map_one]

theorem pquot_imageMod {p : ℕ} (hp : p.Prime) {K J : Subgroup G} (hJK : J ≤ K) :
    Nonempty (PQuot p (imageMod p K J) ≃* PQuot p J) := by
  have hN : ¬ p ∣ Nat.card (QuotientGroup.mk' (GLAPPrimeCore p ↥K)).ker := by
    rw [QuotientGroup.ker_mk']
    haveI : Fact p.Prime := ⟨hp⟩
    exact fun h => hp.one_lt.ne' (Nat.eq_one_of_dvd_coprimes CFSG.pPrimeCore_coprime_card dvd_rfl h)
  obtain ⟨f⟩ := nonempty_pQuot_equiv_map hp hN (J.subgroupOf K)
  obtain ⟨g⟩ := nonempty_pQuot_equiv_subgroupOf p hJK
  exact ⟨f.symm.trans g⟩

theorem comm_le_core_of_imageMod {p : ℕ} {K I S : Subgroup G} (hIK : I ≤ K) (hSK : S ≤ K)
    (h : imageMod p K I ≤ Subgroup.centralizer (imageMod p K S : Set (PQuot p K))) :
    (⁅S, I⁆ : Subgroup G) ≤ GLAPPrimeCoreOf p K := by
  rw [Subgroup.commutator_le]
  intro s hs i hi
  have hsK := hSK hs
  have hiK := hIK hi
  have hmI : QuotientGroup.mk' (GLAPPrimeCore p ↥K) ⟨i, hiK⟩ ∈ imageMod p K I :=
    ⟨⟨i, hiK⟩, Subgroup.mem_subgroupOf.2 hi, rfl⟩
  have hmS : QuotientGroup.mk' (GLAPPrimeCore p ↥K) ⟨s, hsK⟩ ∈ imageMod p K S :=
    ⟨⟨s, hsK⟩, Subgroup.mem_subgroupOf.2 hs, rfl⟩
  have hc := Subgroup.mem_centralizer_iff.1 (h hmI) _ hmS
  have hmem : ⁅(⟨s, hsK⟩ : ↥K), ⟨i, hiK⟩⁆ ∈ GLAPPrimeCore p ↥K := by
    rw [← QuotientGroup.ker_mk' (GLAPPrimeCore p ↥K), MonoidHom.mem_ker, commutatorElement_def,
      map_mul, map_mul, map_mul, map_inv, map_inv, hc]
    group
  exact ⟨_, hmem, rfl⟩

theorem imageMod_component_fix {K J : Subgroup G} {d : G} (hdK : d ∈ Subgroup.normalizer (K : Set G))
    (hd3 : d ^ 3 = 1) (hJ : GLAPComponent 3 (K ⊓ Subgroup.centralizer ({d} : Set G)) J) :
    GLAPComponent 3 (fixSubgroup (barAut 3 K ⟨d, hdK⟩)) (imageMod 3 K J) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set φ : ↥K →* PQuot 3 K := QuotientGroup.mk' (GLAPPrimeCore 3 ↥K) with hφ
  set C : Subgroup ↥K := (K ⊓ Subgroup.centralizer ({d} : Set G)).subgroupOf K with hC
  have hJC : GLAPComponent 3 C (J.subgroupOf K) :=
    glaPComponent_subgroupOf Nat.prime_three inf_le_left hJ
  have hcop : Nat.Coprime 3 (Nat.card ↥(GLAPPrimeCore 3 ↥K)) := CFSG.pPrimeCore_coprime_card
  have hker : Nat.Coprime 3 (Nat.card ↥(C ⊓ φ.ker)) := by
    rw [hφ, QuotientGroup.ker_mk']
    exact hcop.coprime_dvd_right (Subgroup.card_dvd_of_le inf_le_right)
  have hmap := glaPComponent_map Nat.prime_three φ hker hJC
  have hfix : C.map φ = fixSubgroup (barAut 3 K ⟨d, hdK⟩) := by
    apply le_antisymm
    · rintro _ ⟨c, hc, rfl⟩
      have hcd : (c : G) * d = d * c :=
        Subgroup.mem_centralizer_singleton_iff.1 (Subgroup.mem_inf.1 (Subgroup.mem_subgroupOf.1 hc)).2
      have h1 : K.normalizerMonoidHom ⟨d, hdK⟩ c = c := by
        apply Subtype.ext
        show d * (c : G) * d⁻¹ = c
        rw [← hcd]
        group
      show barAut 3 K ⟨d, hdK⟩ (QuotientGroup.mk c) = QuotientGroup.mk c
      rw [CFSG.HardMathSupport.Solomon.LocalBalance.barAut_mk, h1]
    · intro y hy
      obtain ⟨k, rfl⟩ := QuotientGroup.mk'_surjective (GLAPPrimeCore 3 ↥K) y
      have hy' : barAut 3 K ⟨d, hdK⟩ (QuotientGroup.mk k) = QuotientGroup.mk k := hy
      rw [CFSG.HardMathSupport.Solomon.LocalBalance.barAut_mk, QuotientGroup.eq] at hy'
      set N : Subgroup G := GLAPPrimeCoreOf 3 K with hN
      have hw : (d * (k : G) * d⁻¹)⁻¹ * k ∈ N := ⟨_, hy', rfl⟩
      have hNK : N ≤ K := Subgroup.map_subtype_le _
      set M : Subgroup G := Subgroup.normalizer (K : Set G) with hM
      have hNM : N ≤ M := hNK.trans Subgroup.le_normalizer
      have hMN : M ≤ Subgroup.normalizer (N : Set G) := normalizer_le_normalizer_glaPPrimeCoreOf 3 K
      haveI hN'n : (N.subgroupOf M).Normal :=
        (Subgroup.normal_subgroupOf_iff_le_normalizer hNM).2 hMN
      set π : ↥M →* ↥M ⧸ N.subgroupOf M := QuotientGroup.mk' (N.subgroupOf M) with hπ
      have hπker : ¬ 3 ∣ Nat.card π.ker := by
        rw [hπ, QuotientGroup.ker_mk',
          Nat.card_congr (Subgroup.subgroupOfEquivOfLe hNM).toEquiv]
        exact not_dvd_card_glaPPrimeCoreOf Nat.prime_three K
      set y₀ : ↥M := ⟨d, hdK⟩ with hy₀
      have hy₀p : IsPGroup 3 (Subgroup.zpowers y₀) :=
        isPGroup_zpowers_of_pow_eq_one (Subtype.ext (by simpa using hd3))
      set k₀ : ↥M := ⟨(k : G), Subgroup.le_normalizer k.2⟩ with hk₀
      have hk : π k₀ * π y₀ = π y₀ * π k₀ := by
        rw [← map_mul, ← map_mul, hπ, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply,
          QuotientGroup.eq, Subgroup.mem_subgroupOf]
        have hdinv : d⁻¹ ∈ Subgroup.normalizer (N : Set G) := hMN (M.inv_mem hdK)
        have h2 := (Subgroup.mem_normalizer_iff.1 hdinv ((d * (k : G) * d⁻¹)⁻¹ * k)⁻¹).1 (N.inv_mem hw)
        convert h2 using 1
        simp only [hy₀, hk₀, Subgroup.coe_mul, Subgroup.coe_inv]
        group
      obtain ⟨n, hn, hcomm⟩ := exists_mem_ker_mul_commute Nat.prime_three π hπker hy₀p hk
      rw [hπ, QuotientGroup.ker_mk', Subgroup.mem_subgroupOf] at hn
      obtain ⟨n', hn', hn'e⟩ := hn
      have hcommG : (k : G) * n * d = d * ((k : G) * n) := by
        have := congrArg Subtype.val hcomm
        simpa [hy₀, hk₀] using this
      refine ⟨k * n', ?_, ?_⟩
      · rw [SetLike.mem_coe, hC, Subgroup.mem_subgroupOf, Subgroup.coe_mul]
        refine ⟨(K.mul_mem k.2 n'.2), Subgroup.mem_centralizer_singleton_iff.2 ?_⟩
        rw [show ((n' : ↥K) : G) = (n : G) from hn'e]
        exact hcommG
      · rw [map_mul, hφ, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply,
          (QuotientGroup.eq_one_iff n').2 hn', mul_one]
  rw [hfix] at hmap
  exact hmap

theorem pow_transport_apply {Q A : Type*} [Group Q] [Group A] (e : Q ≃* A) (α : MulAut Q) (k : ℕ)
    (x : A) : (((e.symm.trans α).trans e : MulAut A) ^ k) x = e ((α ^ k) (e.symm x)) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ', MulAut.mul_apply, ih, pow_succ', MulAut.mul_apply]
    simp

theorem root9_aux {n : ℕ} {β : MulAut ↥(alternatingGroup (Fin n))} (hβ : β ^ 3 = 1)
    {J₂ : Subgroup ↥(alternatingGroup (Fin n))} (hJ₂ : GLAPComponent 3 (fixSubgroup β) J₂)
    (hJ9 : IsAltPType 3 J₂ 9) :
    ∃ s : Finset (Fin n), s.card = 9 ∧ J₂ = (alternatingGroup.ofSubtype s).range := by
  classical
  haveI : Nontrivial ↥J₂ := AltDown.nontrivial_of_glaPComponent Nat.prime_three hJ₂
  haveI : Group.IsPerfect ↥J₂ := Subgroup.isPerfect_iff.2 (glaPComponent_perfect hJ₂)
  have hne : J₂ ≠ ⊥ := (Subgroup.nontrivial_iff_ne_bot J₂).1 inferInstance
  have hcardJ : ∀ (m : ℕ), (↥J₂ ≃* ↥(alternatingGroup (Fin m))) → 5 ≤ m → m = 9 := by
    intro m f hm5
    haveI : IsSimpleGroup ↥(alternatingGroup (Fin m)) :=
      alternatingGroup.isSimpleGroup (by simpa using hm5)
    obtain ⟨g⟩ := AltDown.nonempty_pSimple_equiv Nat.prime_three hJ₂
      (alternatingGroup.center_eq_bot (by simp; omega)) f
    obtain ⟨h9⟩ := hJ9
    have hZ9 : Subgroup.center ↥(alternatingGroup (Fin 9)) = ⊥ :=
      alternatingGroup.center_eq_bot (by simp)
    have g9 : PSimple 3 J₂ ≃* ↥(alternatingGroup (Fin 9)) :=
      (QuotientGroup.congr (Subgroup.center (PQuot 3 J₂)) (Subgroup.center ↥(alternatingGroup (Fin 9)))
        h9 (Subgroup.map_center_eq h9)).trans
        ((QuotientGroup.quotientMulEquivOfEq hZ9).trans QuotientGroup.quotientBot)
    have hc := Nat.card_congr (g.symm.trans g9).toEquiv
    haveI : Nontrivial (Fin m) := Fin.nontrivial_iff_two_le.2 (by omega)
    rw [nat_card_alternatingGroup, nat_card_alternatingGroup, Nat.card_fin, Nat.card_fin] at hc
    have hm2 : 2 ∣ m.factorial := Nat.dvd_factorial (by norm_num) (by omega)
    have h92 : 2 ∣ (9 : ℕ).factorial := Nat.dvd_factorial (by norm_num) (by norm_num)
    have hf : m.factorial = (9 : ℕ).factorial := (Nat.div_left_inj hm2 h92).1 hc
    exact (Nat.factorial_inj (by omega)).1 hf
  have h24 : ∀ (H : Subgroup ↥(alternatingGroup (Fin n))) (m : ℕ),
      (↥H ≃* ↥(alternatingGroup (Fin m))) → J₂ ≤ H → 5 ≤ m := by
    intro H m f hJH
    by_contra hlt
    push Not at hlt
    have h1 : Nat.card ↥J₂ ∣ 24 := by
      refine (Subgroup.card_dvd_of_le hJH).trans ?_
      rw [Nat.card_congr f.toEquiv]
      refine (AltDown.natCard_alternatingGroup_dvd_factorial (Fin m)).trans ?_
      simpa using AltDown.factorial_dvd_twentyFour hlt
    exact AltDown.false_of_isPerfect_of_card_dvd_twentyFour h1
  have hn5 : 5 ≤ n := h24 ⊤ n Subgroup.topEquiv le_top
  by_cases hβ1 : β = 1
  · subst hβ1
    have htop : fixSubgroup (1 : MulAut ↥(alternatingGroup (Fin n))) = ⊤ := by
      ext x
      simp [CFSG.HardMathSupport.Solomon.Coordinator.mem_fixSubgroup]
    rw [htop] at hJ₂
    haveI : IsSimpleGroup ↥(alternatingGroup (Fin n)) :=
      alternatingGroup.isSimpleGroup (by simpa using hn5)
    haveI : IsSimpleGroup ↥(⊤ : Subgroup ↥(alternatingGroup (Fin n))) :=
      Subgroup.topEquiv.isSimpleGroup
    have hJtop : J₂ = ⊤ := AltDown.eq_of_isSubnormal_of_isSimpleGroup hJ₂.2.1 hne
    have hn9 : n = 9 := hcardJ n ((MulEquiv.subgroupCongr hJtop).trans Subgroup.topEquiv) hn5
    refine ⟨Finset.univ, by simp [hn9], ?_⟩
    rw [hJtop, eq_comm, eq_top_iff]
    intro k _
    rw [alternatingGroup.mem_range_ofSubtype_iff]
    exact Finset.subset_univ _
  · obtain ⟨x, -, hx3, rfl⟩ := AltDown.exists_conj_of_alt hn5 Nat.prime_three (by norm_num) hβ hβ1
    have hJF := AltDown.le_range_ofSubtype_of_glaPComponent Nat.prime_three (by norm_num) hx3 hJ₂
    set s : Finset (Fin n) := ((x : Equiv.Perm (Fin n)).support)ᶜ with hs
    obtain ⟨eF⟩ := AltDown.nonempty_range_ofSubtype_equiv s s.card rfl
    have hm5 : 5 ≤ s.card := h24 _ s.card eF hJF
    haveI : IsSimpleGroup ↥(alternatingGroup (Fin s.card)) :=
      alternatingGroup.isSimpleGroup (by simpa using hm5)
    haveI : IsSimpleGroup ↥(alternatingGroup.ofSubtype s).range := eF.isSimpleGroup
    have hFC : (alternatingGroup.ofSubtype s).range ≤ fixSubgroup (MulAut.conj x) := fun k hk =>
      AltDown.mem_fixSubgroup_conj.2 (Subtype.ext (AltDown.commute_of_mem_range_ofSubtype_compl hk).eq)
    have hJeq := AltDown.eq_of_isSubnormal_of_isSimpleGroup
      (glaPComponent_of_le Nat.prime_three hJ₂ hJF hFC).2.1 hne
    exact ⟨s, hcardJ s.card ((MulEquiv.subgroupCongr hJeq).trans eF) hm5, hJeq⟩

theorem root9_of_fix_component {Q : Type} [Group Q] [Finite Q] {n : ℕ}
    (e : Q ≃* ↥(alternatingGroup (Fin n))) {α : MulAut Q} (hα : α ^ 3 = 1) {J₁ : Subgroup Q}
    (hJ₁ : GLAPComponent 3 (fixSubgroup α) J₁) (hJ9 : IsAltPType 3 J₁ 9) : IsRootAlt e J₁ 9 := by
  classical
  set β : MulAut ↥(alternatingGroup (Fin n)) := (e.symm.trans α).trans e with hβdef
  have hβ3 : β ^ 3 = 1 := by
    refine MulEquiv.ext fun x => ?_
    rw [pow_transport_apply e α 3 x, hα, MulAut.one_apply, MulAut.one_apply, e.apply_symm_apply]
  have hfix : (fixSubgroup α).map e.toMonoidHom = fixSubgroup β := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      have hx' : α x = x := hx
      show β (e x) = e x
      rw [hβdef, MulEquiv.trans_apply, MulEquiv.trans_apply, e.symm_apply_apply, hx']
    · intro hy
      have hy' : β y = y := hy
      refine ⟨e.symm y, ?_, by simp⟩
      show α (e.symm y) = e.symm y
      have h1 : e (α (e.symm y)) = y := hy'
      calc α (e.symm y) = e.symm (e (α (e.symm y))) := (e.symm_apply_apply _).symm
        _ = e.symm y := by rw [h1]
  have hkerbot : e.toMonoidHom.ker = ⊥ := (MonoidHom.ker_eq_bot_iff _).2 e.injective
  have hker : Nat.Coprime 3 (Nat.card ↥(fixSubgroup α ⊓ e.toMonoidHom.ker)) := by
    rw [hkerbot, inf_bot_eq, Subgroup.card_bot]
    exact Nat.coprime_one_right 3
  have hJ₂ : GLAPComponent 3 (fixSubgroup β) (J₁.map e.toMonoidHom) := by
    rw [← hfix]
    exact glaPComponent_map Nat.prime_three e.toMonoidHom hker hJ₁
  have hJ9' : IsAltPType 3 (J₁.map e.toMonoidHom) 9 := by
    obtain ⟨f⟩ := nonempty_pQuot_equiv_map Nat.prime_three (ψ := e.toMonoidHom)
      (by rw [hkerbot, Subgroup.card_bot]; norm_num) J₁
    obtain ⟨g⟩ := hJ9
    exact ⟨f.symm.trans g⟩
  obtain ⟨s, hs9, hJs⟩ := root9_aux hβ3 hJ₂ hJ9'
  refine ⟨?_, ?_⟩
  · obtain ⟨eF⟩ := AltDown.nonempty_range_ofSubtype_equiv s 9 hs9
    exact ⟨((Subgroup.equivMapOfInjective J₁ e.toMonoidHom e.injective).trans
      (MulEquiv.subgroupCongr hJs)).trans eF⟩
  · have hmov : movedLettersOf e J₁ = (s : Set (Fin n)) := by
      ext i
      constructor
      · rintro ⟨h, hh, hhi⟩
        have hmem : e h ∈ (alternatingGroup.ofSubtype s).range := hJs ▸ ⟨h, hh, rfl⟩
        rw [alternatingGroup.mem_range_ofSubtype_iff] at hmem
        exact hmem (Equiv.Perm.mem_support.2 hhi)
      · intro hi
        have hi' : i ∈ s := hi
        have h8 : (s.erase i).card = 8 := by rw [Finset.card_erase_of_mem hi', hs9]
        obtain ⟨v, hv⟩ : (s.erase i).Nonempty := Finset.card_pos.1 (by omega)
        have h7 : ((s.erase i).erase v).card = 7 := by rw [Finset.card_erase_of_mem hv, h8]
        obtain ⟨w, hw⟩ : ((s.erase i).erase v).Nonempty := Finset.card_pos.1 (by omega)
        obtain ⟨hwv, hw'⟩ := Finset.mem_erase.1 hw
        obtain ⟨hwi, hws⟩ := Finset.mem_erase.1 hw'
        obtain ⟨hvi, hvs⟩ := Finset.mem_erase.1 hv
        set σ : Equiv.Perm (Fin n) := Equiv.swap i v * Equiv.swap v w with hσdef
        have hσ : σ ∈ alternatingGroup (Fin n) := by
          rw [Equiv.Perm.mem_alternatingGroup, hσdef, Equiv.Perm.sign_mul,
            Equiv.Perm.sign_swap (Ne.symm hvi), Equiv.Perm.sign_swap (Ne.symm hwv)]
          simp
        have hσs : (⟨σ, hσ⟩ : ↥(alternatingGroup (Fin n))) ∈ (alternatingGroup.ofSubtype s).range := by
          rw [alternatingGroup.mem_range_ofSubtype_iff]
          intro u hu
          have hu' := Equiv.Perm.support_mul_le _ _ hu
          rw [Equiv.Perm.support_swap (Ne.symm hvi), Equiv.Perm.support_swap (Ne.symm hwv)] at hu'
          simp only [Finset.sup_eq_union, Finset.mem_union, Finset.mem_insert,
            Finset.mem_singleton] at hu'
          rcases hu' with (rfl | rfl) | (rfl | rfl) <;> assumption
        rw [← hJs] at hσs
        obtain ⟨h, hh, hhe⟩ := hσs
        refine ⟨h, hh, ?_⟩
        have hσe : ((e h : ↥(alternatingGroup (Fin n))) : Equiv.Perm (Fin n)) = σ :=
          congrArg Subtype.val hhe
        rw [hσe, hσdef, Equiv.Perm.mul_apply, Equiv.swap_apply_of_ne_of_ne (Ne.symm hvi) (Ne.symm hwi),
          Equiv.swap_apply_left]
        exact hvi
    rw [MovesExactly, hmov, Set.ncard_coe_finset, hs9]

theorem alt8_of_le_alt9 {Q : Type} [Group Q] [Finite Q] {J₁ H : Subgroup Q}
    (hJ : Nonempty (↥J₁ ≃* ↥(alternatingGroup (Fin 9)))) (hHJ : H ≤ J₁) (hH : IsAltPType 3 H 8) :
    Nonempty (↥H ≃* ↥(alternatingGroup (Fin 8))) := by
  obtain ⟨f⟩ := hJ
  obtain ⟨g⟩ := hH
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hJc : Nat.card J₁ = 181440 := by
    rw [Nat.card_congr f.toEquiv, nat_card_alternatingGroup]
    simp [Nat.factorial]
  have hQc : Nat.card (PQuot 3 H) = 20160 := by
    rw [Nat.card_congr g.toEquiv, nat_card_alternatingGroup]
    simp [Nat.factorial]
  have hHc := Subgroup.card_eq_card_quotient_mul_card_subgroup (GLAPPrimeCore 3 ↥H)
  have hdvd : Nat.card H ∣ 181440 := hJc ▸ Subgroup.card_dvd_of_le hHJ
  have hcop : Nat.Coprime 3 (Nat.card ↥(GLAPPrimeCore 3 ↥H)) := CFSG.pPrimeCore_coprime_card
  set m := Nat.card ↥(GLAPPrimeCore 3 ↥H) with hm
  have hm9 : m ∣ 9 := by
    rw [hHc] at hdvd
    change Nat.card (PQuot 3 H) * m ∣ 181440 at hdvd
    rw [hQc] at hdvd
    exact (Nat.mul_dvd_mul_iff_left (by norm_num : 0 < 20160)).1 (by simpa using hdvd)
  have hm1 : m = 1 := by
    rcases (Nat.dvd_prime_pow Nat.prime_three).1 (show m ∣ 3 ^ 2 by simpa using hm9) with ⟨k, hk, hk'⟩
    interval_cases k
    · simpa using hk'
    · rw [hk'] at hcop; norm_num at hcop
    · rw [hk'] at hcop; norm_num at hcop
  have hbot : GLAPPrimeCore 3 ↥H = ⊥ := Subgroup.eq_bot_of_card_eq _ hm1
  exact ⟨(QuotientGroup.quotientBot.symm.trans (QuotientGroup.quotientMulEquivOfEq hbot.symm)).trans g⟩

theorem not_fixed_of_order_three {n : ℕ} {s : Finset (Fin n)} (hs : s.card = 9)
    {H : Subgroup ↥(alternatingGroup (Fin n))}
    (hHs : ∀ h ∈ H, ∀ i ∉ s, (h : Equiv.Perm (Fin n)) i = i)
    (hH : Nonempty (↥H ≃* ↥(alternatingGroup (Fin 8))))
    (hno : ∀ i ∈ s, ∃ h ∈ H, (h : Equiv.Perm (Fin n)) i ≠ i) :
    ∀ t ∈ H, orderOf t = 3 → ∀ j ∈ s, (t : Equiv.Perm (Fin n)) j ≠ j := by
  classical
  obtain ⟨e⟩ := hH
  haveI : IsSimpleGroup ↥(alternatingGroup (Fin 8)) := alternatingGroup.isSimpleGroup (by simp)
  haveI : IsSimpleGroup ↥H := e.isSimpleGroup
  have hHc : Nat.card ↥H = 20160 := by
    rw [Nat.card_congr e.toEquiv, nat_card_alternatingGroup]
    simp [Nat.factorial]
  have hpres : ∀ h : ↥H, ∀ i ∈ s, h • i ∈ s := by
    intro h i hi
    by_contra hni
    have h2 : h • i = i :=
      ((h : ↥(alternatingGroup (Fin n))) : Equiv.Perm (Fin n)).injective (hHs _ h.2 _ hni)
    exact hni (by rw [h2]; exact hi)
  have horb_s : ∀ i ∈ s, MulAction.orbit ↥H i ⊆ (s : Set (Fin n)) := by
    rintro i hi _ ⟨h, rfl⟩
    exact hpres h i hi
  have horb8 : ∀ i ∈ s, 8 ≤ (MulAction.orbit ↥H i).ncard := by
    intro i hi
    set O := MulAction.orbit ↥H i with hO
    let ρ := MulAction.toPermHom ↥H ↥O
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal ρ.ker with hk | hk
    · have hinj : Function.Injective ρ := (MonoidHom.ker_eq_bot_iff ρ).1 hk
      have h1 := Nat.card_le_card_of_injective ρ hinj
      rw [hHc, Nat.card_perm, Nat.card_coe_set_eq] at h1
      by_contra hlt
      push Not at hlt
      have h2 : O.ncard.factorial ≤ (7 : ℕ).factorial := Nat.factorial_le (by omega)
      have h7 : (7 : ℕ).factorial = 5040 := by decide
      omega
    · obtain ⟨h, hh, hhi⟩ := hno i hi
      exfalso
      apply hhi
      have hmem : (⟨h, hh⟩ : ↥H) ∈ ρ.ker := hk ▸ Subgroup.mem_top _
      have h1 := congrArg (fun σ : Equiv.Perm ↥O => (σ ⟨i, MulAction.mem_orbit_self i⟩ : Fin n))
        (MonoidHom.mem_ker.1 hmem)
      simp only [ρ, MulAction.toPermHom_apply, MulAction.toPerm_apply, Equiv.Perm.one_apply] at h1
      exact h1
  have horb9 : ∀ i ∈ s, (MulAction.orbit ↥H i).ncard = 9 := by
    intro i hi
    have hle : (MulAction.orbit ↥H i).ncard ≤ 9 := by
      have h1 := Set.ncard_le_ncard (horb_s i hi)
      rwa [Set.ncard_coe_finset, hs] at h1
    have h8 := horb8 i hi
    by_contra h9
    have hO8 : (MulAction.orbit ↥H i).ncard = 8 := by omega
    obtain ⟨j, hjs, hjO⟩ : ∃ j ∈ s, j ∉ MulAction.orbit ↥H i := by
      by_contra hcon
      push Not at hcon
      have h2 := Set.ncard_le_ncard (show (s : Set (Fin n)) ⊆ MulAction.orbit ↥H i from
        fun j hj => hcon j hj)
      rw [Set.ncard_coe_finset, hs, hO8] at h2
      omega
    have hdisj : Disjoint (MulAction.orbit ↥H j) (MulAction.orbit ↥H i) := by
      rcases MulAction.orbit.eq_or_disjoint (G := ↥H) j i with h | h
      · exact absurd (h ▸ MulAction.mem_orbit_self j) hjO
      · exact h
    have h3 := Set.ncard_le_ncard (Set.union_subset (horb_s j hjs) (horb_s i hi))
    rw [Set.ncard_union_eq hdisj, Set.ncard_coe_finset, hs] at h3
    have h8j := horb8 j hjs
    omega
  intro t ht ht3 j hj htj
  have hstab : Nat.card (MulAction.stabilizer ↥H j) = 2240 := by
    have h1 := MulAction.index_stabilizer ↥H j
    have h2 := Subgroup.card_mul_index (MulAction.stabilizer ↥H j)
    rw [h1, horb9 j hj, hHc] at h2
    omega
  have hmem : (⟨t, ht⟩ : ↥H) ∈ MulAction.stabilizer ↥H j := htj
  have hord : orderOf (⟨t, ht⟩ : ↥H) = 3 := by
    rw [← Subgroup.orderOf_coe]
    exact ht3
  have hdvd := Subgroup.orderOf_dvd_natCard _ hmem
  rw [hord, hstab] at hdvd
  norm_num at hdvd

theorem eq_one_of_commute_fpf {n : ℕ} {s : Finset (Fin n)} (hs : s.card = 9) {t z : Equiv.Perm (Fin n)}
    (ht3 : t ^ 3 = 1) (hz5 : z ^ 5 = 1) (htz : Commute t z) (hts : ∀ j ∈ s, t j ≠ j)
    (hts' : ∀ j ∈ s, t j ∈ s) (hzs' : ∀ j ∈ s, z j ∈ s) (hzs : ∀ j ∉ s, z j = j) : z = 1 := by
  classical
  by_contra hz1
  obtain ⟨j, hjs, hzj⟩ : ∃ j ∈ s, z j ≠ j := by
    by_contra h
    push Not at h
    exact hz1 (Equiv.ext fun x => by
      by_cases hx : x ∈ s
      · exact h x hx
      · exact hzs x hx)
  have hmod : ∀ (u : Equiv.Perm (Fin n)) (k N : ℕ), u ^ k = 1 → u ^ N = u ^ (N % k) := by
    intro u k N hk
    conv_lhs => rw [← Nat.div_add_mod N k, pow_add, pow_mul, hk, one_pow, one_mul]
  have hfixpow : ∀ (u : Equiv.Perm (Fin n)) (i : Fin n), u i = i → ∀ c : ℕ, (u ^ c) i = i := by
    intro u i hu c
    induction c with
    | zero => simp
    | succ c ih => rw [pow_succ, Equiv.Perm.mul_apply, hu, ih]
  have hpow_s : ∀ (u : Equiv.Perm (Fin n)), (∀ i ∈ s, u i ∈ s) → ∀ k : ℕ, ∀ i ∈ s, (u ^ k) i ∈ s := by
    intro u hu k
    induction k with
    | zero => intro i hi; simpa using hi
    | succ k ih => intro i hi; rw [pow_succ, Equiv.Perm.mul_apply]; exact ih _ (hu i hi)
  have htr : ∀ r, r < 3 → 0 < r → (t ^ r) j ≠ j := by
    intro r hr hr0 h
    interval_cases r
    · exact hts j hjs (by simpa using h)
    · apply hts j hjs
      have h1 : (t ^ 3) j = t j := by rw [pow_succ', Equiv.Perm.mul_apply, h]
      rw [ht3, Equiv.Perm.one_apply] at h1
      exact h1.symm
  have hzr : ∀ r, r < 5 → 0 < r → (z ^ r) j ≠ j := by
    intro r hr hr0 h
    apply hzj
    have hc := hfixpow _ _ h
    interval_cases r
    · simpa using h
    · have := hc 3
      rwa [← pow_mul, hmod z 5 _ hz5, pow_one] at this
    · have := hc 2
      rwa [← pow_mul, hmod z 5 _ hz5, pow_one] at this
    · have := hc 4
      rwa [← pow_mul, hmod z 5 _ hz5, pow_one] at this
  set g : Equiv.Perm (Fin n) := t * z with hg
  have hgpow : ∀ k : ℕ, g ^ k = t ^ k * z ^ k := fun k => htz.mul_pow k
  have hgm : ∀ m, 0 < m → m < 15 → (g ^ m) j ≠ j := by
    intro m hm0 hm15 h
    have h5 : (t ^ ((5 * m) % 3)) j = j := by
      have h1 := hfixpow _ _ h 5
      rw [← pow_mul, hgpow, mul_comm m 5, pow_mul z 5, hz5, one_pow, mul_one, hmod t 3 _ ht3] at h1
      exact h1
    have h3 : (z ^ ((3 * m) % 5)) j = j := by
      have h1 := hfixpow _ _ h 3
      rw [← pow_mul, hgpow, mul_comm m 3, pow_mul t 3, ht3, one_pow, one_mul, hmod z 5 _ hz5] at h1
      exact h1
    have hA : (5 * m) % 3 = 0 := by
      by_contra hne
      exact htr _ (Nat.mod_lt _ (by norm_num)) (Nat.pos_of_ne_zero hne) h5
    have hB : (3 * m) % 5 = 0 := by
      by_contra hne
      exact hzr _ (Nat.mod_lt _ (by norm_num)) (Nat.pos_of_ne_zero hne) h3
    omega
  have hgs : ∀ i ∈ s, g i ∈ s := fun i hi => by
    rw [hg, Equiv.Perm.mul_apply]
    exact hts' _ (hzs' i hi)
  have hinj : Set.InjOn (fun k : Fin 15 => (g ^ (k : ℕ)) j) (Finset.univ : Finset (Fin 15)) := by
    intro k _ k' _ hkk
    simp only at hkk
    by_contra hne
    rcases lt_or_gt_of_ne (Fin.val_ne_of_ne hne) with hlt | hlt
    · apply hgm ((k' : ℕ) - k) (by omega) (by omega)
      have e1 : g ^ (k' : ℕ) = g ^ (k : ℕ) * g ^ ((k' : ℕ) - k) := by
        rw [← pow_add, Nat.add_sub_cancel' hlt.le]
      rw [e1, Equiv.Perm.mul_apply] at hkk
      exact ((g ^ (k : ℕ)).injective hkk).symm
    · apply hgm ((k : ℕ) - k') (by omega) (by omega)
      have e1 : g ^ (k : ℕ) = g ^ (k' : ℕ) * g ^ ((k : ℕ) - k') := by
        rw [← pow_add, Nat.add_sub_cancel' hlt.le]
      rw [e1, Equiv.Perm.mul_apply] at hkk
      exact (g ^ (k' : ℕ)).injective hkk
  have hcard := Finset.card_le_card_of_injOn (fun k : Fin 15 => (g ^ (k : ℕ)) j)
    (fun k _ => hpow_s g hgs _ j hjs) hinj
  rw [Finset.card_univ, Fintype.card_fin, hs] at hcard
  omega

private theorem perm_c3_c5 :
    Equiv.Perm.sign (Equiv.swap (0 : Fin 8) 1 * Equiv.swap 1 2) = 1 ∧
      Equiv.Perm.sign (Equiv.swap (3 : Fin 8) 4 * Equiv.swap 4 5 * Equiv.swap 5 6 * Equiv.swap 6 7) = 1 ∧
      (Equiv.swap (0 : Fin 8) 1 * Equiv.swap 1 2) ^ 3 = 1 ∧
      Equiv.swap (0 : Fin 8) 1 * Equiv.swap 1 2 ≠ 1 ∧
      (Equiv.swap (3 : Fin 8) 4 * Equiv.swap 4 5 * Equiv.swap 5 6 * Equiv.swap 6 7) ^ 5 = 1 ∧
      Equiv.swap (3 : Fin 8) 4 * Equiv.swap 4 5 * Equiv.swap 5 6 * Equiv.swap 6 7 ≠ 1 ∧
      (Equiv.swap (0 : Fin 8) 1 * Equiv.swap 1 2) *
          (Equiv.swap (3 : Fin 8) 4 * Equiv.swap 4 5 * Equiv.swap 5 6 * Equiv.swap 6 7) =
        (Equiv.swap (3 : Fin 8) 4 * Equiv.swap 4 5 * Equiv.swap 5 6 * Equiv.swap 6 7) *
          (Equiv.swap (0 : Fin 8) 1 * Equiv.swap 1 2) := by
  decide

theorem exists_fixed_of_alt8 {n : ℕ} {s : Finset (Fin n)} (hs : s.card = 9)
    {H : Subgroup ↥(alternatingGroup (Fin n))}
    (hHs : ∀ h ∈ H, ∀ i ∉ s, (h : Equiv.Perm (Fin n)) i = i)
    (hH : Nonempty (↥H ≃* ↥(alternatingGroup (Fin 8)))) :
    ∃ i ∈ s, ∀ h ∈ H, (h : Equiv.Perm (Fin n)) i = i := by
  obtain ⟨hs3, hs5, h33, h31, h55, h51, hcc⟩ := perm_c3_c5
  by_contra hcon
  push Not at hcon
  obtain ⟨e⟩ := hH
  have hpres : ∀ h ∈ H, ∀ i ∈ s, (h : Equiv.Perm (Fin n)) i ∈ s := by
    intro h hh i hi
    by_contra hni
    have h2 : (h : Equiv.Perm (Fin n)) i = i := (h : Equiv.Perm (Fin n)).injective (hHs h hh _ hni)
    exact hni (by rw [h2]; exact hi)
  set c3 : ↥(alternatingGroup (Fin 8)) := ⟨_, Equiv.Perm.mem_alternatingGroup.2 hs3⟩ with hc3def
  set c5 : ↥(alternatingGroup (Fin 8)) := ⟨_, Equiv.Perm.mem_alternatingGroup.2 hs5⟩ with hc5def
  have hc33 : c3 ^ 3 = 1 := Subtype.ext (by simpa [hc3def] using h33)
  have hc31 : c3 ≠ 1 := fun h => h31 (by simpa [hc3def] using congrArg Subtype.val h)
  have hc55 : c5 ^ 5 = 1 := Subtype.ext (by simpa [hc5def] using h55)
  have hc51 : c5 ≠ 1 := fun h => h51 (by simpa [hc5def] using congrArg Subtype.val h)
  have hc35 : c3 * c5 = c5 * c3 := Subtype.ext (by simpa [hc3def, hc5def] using hcc)
  set t : ↥H := e.symm c3 with htdef
  set z : ↥H := e.symm c5 with hzdef
  have ht3 : t ^ 3 = 1 := by rw [htdef, ← map_pow, hc33, map_one]
  have hz5 : z ^ 5 = 1 := by rw [hzdef, ← map_pow, hc55, map_one]
  have hz1 : z ≠ 1 := fun h => hc51 (by rw [← e.apply_symm_apply c5, ← hzdef, h, map_one])
  have htz : t * z = z * t := by rw [htdef, hzdef, ← map_mul, ← map_mul, hc35]
  have ht1 : t ≠ 1 := fun h => hc31 (by rw [← e.apply_symm_apply c3, ← htdef, h, map_one])
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hordt : orderOf ((t : ↥(alternatingGroup (Fin n)))) = 3 := by
    rw [Subgroup.orderOf_coe]
    exact orderOf_eq_prime ht3 ht1
  have hfpf := not_fixed_of_order_three hs hHs ⟨e⟩ hcon _ t.2 hordt
  have ht3' : ((t : ↥(alternatingGroup (Fin n))) : Equiv.Perm (Fin n)) ^ 3 = 1 := by
    simpa using congrArg (fun w : ↥H => ((w : ↥(alternatingGroup (Fin n))) : Equiv.Perm (Fin n))) ht3
  have hz5' : ((z : ↥(alternatingGroup (Fin n))) : Equiv.Perm (Fin n)) ^ 5 = 1 := by
    simpa using congrArg (fun w : ↥H => ((w : ↥(alternatingGroup (Fin n))) : Equiv.Perm (Fin n))) hz5
  have htz' : ((t : ↥(alternatingGroup (Fin n))) : Equiv.Perm (Fin n)) *
      ((z : ↥(alternatingGroup (Fin n))) : Equiv.Perm (Fin n)) =
      ((z : ↥(alternatingGroup (Fin n))) : Equiv.Perm (Fin n)) *
      ((t : ↥(alternatingGroup (Fin n))) : Equiv.Perm (Fin n)) := by
    simpa using congrArg (fun w : ↥H => ((w : ↥(alternatingGroup (Fin n))) : Equiv.Perm (Fin n))) htz
  have hz := eq_one_of_commute_fpf hs ht3' hz5' htz' hfpf (hpres _ t.2) (hpres _ z.2) (hHs _ z.2)
  exact hz1 (Subtype.ext (Subtype.ext hz))

theorem root8_of_le_root9 {Q : Type} [Group Q] [Finite Q] {n : ℕ}
    (e : Q ≃* ↥(alternatingGroup (Fin n))) {J₁ H : Subgroup Q} (hJ : IsRootAlt e J₁ 9) (hHJ : H ≤ J₁)
    (hH : Nonempty (↥H ≃* ↥(alternatingGroup (Fin 8)))) : IsRootAlt e H 8 := by
  classical
  refine ⟨hH, ?_⟩
  obtain ⟨f⟩ := hH
  set s : Finset (Fin n) := (Set.toFinite (movedLettersOf e J₁)).toFinset with hsdef
  have hs : s.card = 9 := by
    rw [← hJ.2, hsdef, Set.ncard_eq_toFinset_card _ (Set.toFinite _)]
  have hmemS : ∀ i, i ∈ s ↔ i ∈ movedLettersOf e J₁ := fun i => Set.Finite.mem_toFinset _
  set H' : Subgroup ↥(alternatingGroup (Fin n)) := H.map e.toMonoidHom with hH'
  have hH'f : Nonempty (↥H' ≃* ↥(alternatingGroup (Fin 8))) :=
    ⟨(Subgroup.equivMapOfInjective H e.toMonoidHom e.injective).symm.trans f⟩
  have hH's : ∀ h ∈ H', ∀ i ∉ s, (h : Equiv.Perm (Fin n)) i = i := by
    rintro _ ⟨x, hx, rfl⟩ i hi
    by_contra hne
    exact hi ((hmemS i).2 ⟨x, hHJ hx, hne⟩)
  obtain ⟨i₀, hi₀s, hi₀⟩ := exists_fixed_of_alt8 hs hH's hH'f
  have hsub : movedLettersOf e H ⊆ ((s.erase i₀ : Finset (Fin n)) : Set (Fin n)) := by
    rintro i ⟨x, hx, hxi⟩
    rw [Finset.coe_erase, Set.mem_diff, Set.mem_singleton_iff]
    refine ⟨(hmemS i).2 ⟨x, hHJ hx, hxi⟩, ?_⟩
    rintro rfl
    exact hxi (hi₀ _ ⟨x, hx, rfl⟩)
  have heq : movedLettersOf e H = ((s.erase i₀ : Finset (Fin n)) : Set (Fin n)) := by
    refine Set.Subset.antisymm hsub ?_
    intro j hj
    by_contra hjH
    set T : Finset (Fin n) := (s.erase i₀).erase j with hT
    have hTc : T.card = 7 := by
      rw [hT, Finset.card_erase_of_mem hj, Finset.card_erase_of_mem hi₀s, hs]
    have hle : H' ≤ (alternatingGroup.ofSubtype Tᶜᶜ).range := by
      intro h hh
      rw [AltDown.mem_range_ofSubtype_compl_iff]
      intro u hu
      by_cases hus : u ∈ s
      · by_cases hui : u = i₀
        · rw [hui]; exact hi₀ h hh
        · have huj : u = j := by
            by_contra hne
            exact (Finset.mem_compl.1 hu) (Finset.mem_erase.2 ⟨hne, Finset.mem_erase.2 ⟨hui, hus⟩⟩)
          rw [huj]
          obtain ⟨x, hx, rfl⟩ := hh
          by_contra hne
          exact hjH ⟨x, hx, hne⟩
      · exact hH's h hh u hus
    rw [compl_compl] at hle
    obtain ⟨g7⟩ := AltDown.nonempty_range_ofSubtype_equiv T 7 hTc
    have h1 := Subgroup.card_le_of_le hle
    rw [Nat.card_congr g7.toEquiv, nat_card_alternatingGroup, Nat.card_congr hH'f.some.toEquiv,
      nat_card_alternatingGroup] at h1
    simp [Nat.factorial] at h1
  rw [MovesExactly, heq, Set.ncard_coe_finset, Finset.card_erase_of_mem hi₀s, hs]

theorem alt_case (h2013 : I2013At) {K J I S : Subgroup G} {d : G} {n : ℕ} (hKn : IsAltPType 3 K n)
    (hdK : d ∈ Subgroup.normalizer (K : Set G)) (hd3 : d ^ 3 = 1)
    (hJ : GLAPComponent 3 (K ⊓ Subgroup.centralizer ({d} : Set G)) J) (hJ9 : IsAltPType 3 J 9)
    (hIJ : I ≤ J) (hI8 : IsAltPType 3 I 8) (hSK : S ≤ K) (hS2 : IsPGroup 2 S)
    (hIS : I ≤ Subgroup.normalizer (S : Set G)) : (⁅S, I⁆ : Subgroup G) ≤ GLAPPrimeCoreOf 3 K := by
  obtain ⟨e⟩ := hKn
  have hJK : J ≤ K := hJ.1.trans inf_le_left
  have hIK : I ≤ K := hIJ.trans hJK
  have hcomp := imageMod_component_fix hdK hd3 hJ
  have hJ9' : IsAltPType 3 (imageMod 3 K J) 9 := by
    obtain ⟨f⟩ := pquot_imageMod Nat.prime_three hJK
    obtain ⟨g⟩ := hJ9
    exact ⟨f.trans g⟩
  have hroot9 := root9_of_fix_component e (barAut_pow_three hdK hd3) hcomp hJ9'
  have hI8' : IsAltPType 3 (imageMod 3 K I) 8 := by
    obtain ⟨f⟩ := pquot_imageMod Nat.prime_three hIK
    obtain ⟨g⟩ := hI8
    exact ⟨f.trans g⟩
  have hIle : imageMod 3 K I ≤ imageMod 3 K J := imageMod_mono hIJ
  have hroot8 := root8_of_le_root9 e hroot9 hIle (alt8_of_le_alt9 hroot9.1 hIle hI8')
  have h8n : 8 ≤ n := by
    have h := Set.ncard_le_ncard (Set.subset_univ (movedLettersOf e (imageMod 3 K J)))
      (Set.toFinite _)
    rw [Set.ncard_univ, Nat.card_eq_fintype_card, Fintype.card_fin] at h
    have h9 : (movedLettersOf e (imageMod 3 K J)).ncard = 9 := hroot9.2
    omega
  have hcent := h2013 (PQuot 3 K) n 8 e (imageMod 3 K I) (by norm_num) h8n hroot8
    (imageMod 3 K S) (isPGroup_imageMod hS2) (imageMod_le_normalizer hIS)
  exact comm_le_core_of_imageMod hIK hSK hcent

end S8.L83

end CFSG.LocalAnalysis.GLTheoremA
