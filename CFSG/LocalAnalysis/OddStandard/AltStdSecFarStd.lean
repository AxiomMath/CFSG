module

public import CFSG.LocalAnalysis.OddStandard.AltStdSecFarCbar

public section

namespace CFSG.OddStandard.AltStdSec

open Subgroup Equiv Equiv.Perm
open scoped commutatorElement

section Std

variable {G : Type} [Group G] {z : G} {m : ℕ} (O : OverData G z m) (h4 : 4 ≤ m + 3)

noncomputable abbrev Jbar : Subgroup (Cbar O h4) := centralizer (L0bar O h4 : Set (Cbar O h4))

theorem psiL_injective : Function.Injective (psiL O h4) := by
  rw [injective_iff_map_eq_one]
  intro l hl
  rw [psiL_apply] at hl
  rcases (mem_zpowers_selfC_iff (wA_mul_self O h4)).1 ((QuotientGroup.eq_one_iff _).1 hl) with
    h | h
  · exact Subtype.ext (O.φ_injective (h.trans (map_one _).symm))
  · exfalso
    have h' : (l : Perm (Fin (m + 3))) = emb4 h4 kA4 := O.φ_injective h
    have h0 := altSub_compl_le l.2 ⟨0, by omega⟩ (by simp [mem_fourSet])
    rw [h'] at h0
    exact emb4_kA4_apply_ne h4 (i := ⟨0, by omega⟩) (by simp) h0

@[expose] noncomputable def L0barEquiv (hm : 1 ≤ m) : L0bar O h4 ≃* alternatingGroup (Fin (m - 1)) :=
  (MonoidHom.ofInjective (psiL_injective O h4)).symm.trans
    ((altSubEquiv _).trans (Equiv.altCongrHom (finCongr (card_fourSet_compl hm))))

theorem card_kbar_le : Nat.card (kbar O h4) ≤ 4 := by
  have h1 : (kbar O h4 : Set (Cbar O h4)) ⊆ {1, ebar O h4, fbar O h4, ybar O h4} := fun x hx => by
    rcases (mem_kbar_iff O h4).1 hx with h | h | h | h <;> simp [h]
  have h2 := Set.ncard_le_ncard h1 (Set.toFinite _)
  have h3 : ({1, ebar O h4, fbar O h4, ybar O h4} : Set (Cbar O h4)).ncard ≤ 4 := by
    calc ({1, ebar O h4, fbar O h4, ybar O h4} : Set (Cbar O h4)).ncard ≤
        ({ebar O h4, fbar O h4, ybar O h4} : Set (Cbar O h4)).ncard + 1 := Set.ncard_insert_le _ _
      _ ≤ (({fbar O h4, ybar O h4} : Set (Cbar O h4)).ncard + 1) + 1 := by
          gcongr; exact Set.ncard_insert_le _ _
      _ ≤ ((({ybar O h4} : Set (Cbar O h4)).ncard + 1) + 1) + 1 := by
          gcongr; exact Set.ncard_insert_le _ _
      _ = 4 := by rw [Set.ncard_singleton]
  have h4' : Nat.card (kbar O h4) = (kbar O h4 : Set (Cbar O h4)).ncard :=
    Nat.card_coe_set_eq _
  omega

variable [Finite G]

omit [Finite G] in
theorem isPGroup_kbarJ : IsPGroup 2 ((kbar O h4).subgroupOf (Jbar O h4)) := by
  intro x
  refine ⟨1, ?_⟩
  apply Subtype.ext
  apply Subtype.ext
  have hx : ((x : Jbar O h4) : Cbar O h4) ∈ kbar O h4 := x.2
  have := mul_self_of_mem_kbar O h4 hx
  simpa [pow_two] using this

theorem sylow_le_kbar (hm : 10 ≤ m) (P : Sylow 2 ↥(Jbar O h4))
    (hKP : (kbar O h4).subgroupOf (Jbar O h4) ≤ P) :
    (P : Subgroup (Jbar O h4)) ≤ (kbar O h4).subgroupOf (Jbar O h4) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hKJ : kbar O h4 ≤ Jbar O h4 := kbar_le_centralizer O h4
  by_contra hcon
  set H : Subgroup ↥(P : Subgroup (Jbar O h4)) :=
    ((kbar O h4).subgroupOf (Jbar O h4)).subgroupOf (P : Subgroup (Jbar O h4)) with hH
  have hlt : H < ⊤ := by
    rw [lt_top_iff_ne_top]
    intro htop
    apply hcon
    intro x hx
    have : (⟨x, hx⟩ : ↥(P : Subgroup (Jbar O h4))) ∈ H := htop ▸ mem_top _
    exact this
  have := (P.isPGroup').isNilpotent
  obtain ⟨n, hn, hnH⟩ := IsConcreteLE.exists_of_lt (Group.normalizerCondition_of_isNilpotent H hlt)
  have heJ : ebar O h4 ∈ Jbar O h4 := hKJ ⟨_, rfl⟩
  have heK : (⟨ebar O h4, heJ⟩ : Jbar O h4) ∈ (kbar O h4).subgroupOf (Jbar O h4) :=
    (⟨_, rfl⟩ : ebar O h4 ∈ kbar O h4)
  have heH : (⟨⟨ebar O h4, heJ⟩, hKP heK⟩ : ↥(P : Subgroup (Jbar O h4))) ∈ H := heK
  have h1 := (mem_normalizer_iff.1 hn _).1 heH
  have h2 : ((n : Jbar O h4) : Cbar O h4) * ebar O h4 * ((n : Jbar O h4) : Cbar O h4)⁻¹ ∈
      kbar O h4 := h1
  have h3 := eq_of_isConj_of_mem_kbar O h4 hm ⟨_, rfl⟩ h2
    (isConj_iff.2 ⟨((n : Jbar O h4) : Cbar O h4), rfl⟩)
  have h4' : ((n : Jbar O h4) : Cbar O h4) * ebar O h4 =
      ebar O h4 * ((n : Jbar O h4) : Cbar O h4) := by
    calc ((n : Jbar O h4) : Cbar O h4) * ebar O h4 = (((n : Jbar O h4) : Cbar O h4) *
        ebar O h4 * ((n : Jbar O h4) : Cbar O h4)⁻¹) * ((n : Jbar O h4) : Cbar O h4) := by
          group
      _ = ebar O h4 * ((n : Jbar O h4) : Cbar O h4) := by rw [← h3]
  exact hnH (mem_kbar_of_comm_ebar O h4 (by omega) h4' (n : Jbar O h4).2)

theorem exists_conj_kbar (hm : 10 ≤ m) {Q : Subgroup (Cbar O h4)} (hQJ : Q ≤ Jbar O h4)
    (hQ : IsPGroup 2 Q) : ∃ j ∈ Jbar O h4, ∀ q ∈ Q, j⁻¹ * q * j ∈ kbar O h4 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨P, hKP⟩ := (isPGroup_kbarJ O h4).exists_le_sylow
  have hPK := sylow_le_kbar O h4 hm P hKP
  have hQ' : IsPGroup 2 (Q.subgroupOf (Jbar O h4)) := by
    intro x
    obtain ⟨k, hk⟩ := hQ ⟨((x : Jbar O h4) : Cbar O h4), x.2⟩
    refine ⟨k, ?_⟩
    apply Subtype.ext
    apply Subtype.ext
    have := congrArg Subtype.val hk
    simpa using this
  obtain ⟨P', hQP'⟩ := hQ'.exists_le_sylow
  obtain ⟨j, hj⟩ := MulAction.exists_smul_eq (Jbar O h4) P P'
  refine ⟨(j : Cbar O h4), j.2, fun q hq => ?_⟩
  have hqJ : q ∈ Jbar O h4 := hQJ hq
  have h1 : (⟨q, hqJ⟩ : Jbar O h4) ∈ (P' : Subgroup (Jbar O h4)) := hQP' hq
  rw [← hj, Sylow.coe_subgroup_smul, Subgroup.mem_smul_pointwise_iff_exists] at h1
  obtain ⟨p, hp, hpq⟩ := h1
  have h2 : ((p : Jbar O h4) : Cbar O h4) = (j : Cbar O h4)⁻¹ * q * j := by
    have := congrArg Subtype.val hpq
    rw [MulAut.smul_def, MulAut.conj_apply] at this
    simp only [Subgroup.coe_mul, Subgroup.coe_inv] at this
    rw [← this]
    group
  rw [← h2]
  exact hPK hp

theorem exists_conj_kbar_of_mul_self (hm : 10 ≤ m) {s : Cbar O h4} (hs : s ∈ Jbar O h4)
    (hs2 : s * s = 1) (hs1 : s ≠ 1) :
    ∃ j ∈ Jbar O h4, j⁻¹ * s * j ∈ kbar O h4 ∧ j⁻¹ * s * j ≠ 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have ho : orderOf s = 2 := orderOf_eq_prime (by rw [pow_two]; exact hs2) hs1
  have hQ : IsPGroup 2 (zpowers s) := IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, ho, pow_one])
  obtain ⟨j, hj, hjk⟩ := exists_conj_kbar O h4 hm (zpowers_le.2 hs) hQ
  refine ⟨j, hj, hjk s (mem_zpowers s), fun h => hs1 ?_⟩
  calc s = j * (j⁻¹ * s * j) * j⁻¹ := by group
    _ = 1 := by rw [h]; group

theorem normalizer_le_normalizer_centralizer' {X : Type*} [Group X] (A : Subgroup X) :
    normalizer (A : Set X) ≤ normalizer (centralizer (A : Set X) : Set X) := by
  intro g hg
  have key : ∀ g ∈ normalizer (A : Set X), ∀ x ∈ centralizer (A : Set X),
      g * x * g⁻¹ ∈ centralizer (A : Set X) := by
    intro g hg x hx
    rw [mem_centralizer_iff] at hx ⊢
    intro a ha
    have ha' : g⁻¹ * a * g ∈ A := by
      have := (mem_normalizer_iff.1 (inv_mem hg) a).1 ha
      simpa using this
    have := hx _ ha'
    calc a * (g * x * g⁻¹) = g * ((g⁻¹ * a * g) * x) * g⁻¹ := by group
      _ = g * (x * (g⁻¹ * a * g)) * g⁻¹ := by rw [this]
      _ = g * x * g⁻¹ * a := by group
  rw [mem_normalizer_iff]
  intro x
  refine ⟨key g hg x, fun hx => ?_⟩
  have := key g⁻¹ (inv_mem hg) _ hx
  simpa [mul_assoc] using this

theorem centralizer_le_normalizer' {X : Type*} [Group X] (A : Subgroup X) :
    centralizer (A : Set X) ≤ normalizer (A : Set X) := by
  intro g hg
  rw [mem_normalizer_iff]
  intro a
  constructor
  · intro ha
    have h1 := mem_centralizer_iff.1 hg a ha
    have e : g * a * g⁻¹ = a := by rw [← h1]; group
    rw [e]; exact ha
  · intro ha
    have h1 := mem_centralizer_iff.1 hg _ ha
    have e : a = g * a * g⁻¹ := by
      calc a = g⁻¹ * ((g * a * g⁻¹) * g) := by group
        _ = g⁻¹ * (g * (g * a * g⁻¹)) := by rw [h1]
        _ = g * a * g⁻¹ := by group
    rw [e]; exact ha

omit [Finite G] in
theorem isQuasisimple_L0bar (hm : 6 ≤ m) : CFSG.Open.IsQuasisimple ↥(L0bar O h4) := by
  have e := L0barEquiv O h4 (by omega)
  have hs : IsSimpleGroup ↥(L0bar O h4) := isSimpleGroup_of_alt (by omega) e
  have hc : center ↥(L0bar O h4) = ⊥ := center_eq_bot_of_alt (by omega) e
  refine ⟨?_, ?_⟩
  · rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (commutator ↥(L0bar O h4)) with h | h
    · exfalso
      have htop : center ↥(L0bar O h4) = ⊤ := by
        rw [eq_top_iff]
        intro x _
        rw [mem_center_iff]
        intro y
        have h1 : ⁅y, x⁆ ∈ commutator ↥(L0bar O h4) :=
          commutator_mem_commutator (mem_top y) (mem_top x)
        rw [h, mem_bot] at h1
        exact commutatorElement_eq_one_iff_mul_comm.1 h1
      rw [hc] at htop
      exact bot_ne_top htop
    · exact h
  · have e2 : ↥(L0bar O h4) ⧸ center ↥(L0bar O h4) ≃* ↥(L0bar O h4) :=
      (QuotientGroup.quotientMulEquivOfEq hc).trans QuotientGroup.quotientBot
    exact e2.isSimpleGroup

theorem isStandard_L0bar (hNE : L0Normal O (kleinR h4)) (hNy : L0Normal O (cycR h4))
    (hm : 10 ≤ m) : CFSG.Open.standardComponentIsStandard (L0bar O h4) := by
  have hNL : normalizer (L0bar O h4 : Set (Cbar O h4)) ≤
      normalizer (Jbar O h4 : Set (Cbar O h4)) := normalizer_le_normalizer_centralizer' _
  have hJL : Jbar O h4 ≤ normalizer (L0bar O h4 : Set (Cbar O h4)) :=
    centralizer_le_normalizer' _
  have hcent : ∀ {t : Cbar O h4}, t ∈ kbar O h4 → t ≠ 1 →
      centralizer ({t} : Set (Cbar O h4)) ≤ normalizer (L0bar O h4 : Set (Cbar O h4)) :=
    fun ht ht1 => centralizer_le_normalizer_L0bar O h4 hNE hNy ht ht1
  have heK : ebar O h4 ∈ kbar O h4 := ⟨_, rfl⟩
  have he1 : ebar O h4 ≠ 1 := psi4_ne_one O h4 _ (by decide) (by decide)
  have he2 : ebar O h4 * ebar O h4 = 1 := mul_self_of_mem_kbar O h4 heK
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine ⟨isQuasisimple_L0bar O h4 (by omega), ?_, ?_, ?_, ?_⟩
  ·
    have h2 : orderOf (ebar O h4) = 2 := orderOf_eq_prime (by rw [pow_two]; exact he2) he1
    rw [even_iff_two_dvd, ← h2]
    exact Subgroup.orderOf_dvd_natCard _ (kbar_le_centralizer O h4 heK)
  ·
    intro g hg
    by_contra hodd
    rw [Nat.not_odd_iff_even] at hodd
    obtain ⟨s, hs⟩ := exists_prime_orderOf_dvd_card'
      (G := ↥(Jbar O h4 ⊓ (Jbar O h4).map (MulAut.conj g).toMonoidHom)) 2
      (even_iff_two_dvd.1 hodd)
    have hs2 : (s : Cbar O h4) * s = 1 := by
      have := pow_orderOf_eq_one s
      rw [hs, pow_two] at this
      exact congrArg Subtype.val this
    have hs1 : (s : Cbar O h4) ≠ 1 := fun h => by
      have : s = 1 := Subtype.ext h
      rw [this, orderOf_one] at hs
      omega
    obtain ⟨hsJ, hsJg⟩ := Subgroup.mem_inf.1 s.2
    obtain ⟨s', hs'J, hs's⟩ := hsJg
    have hs's' : g * s' * g⁻¹ = (s : Cbar O h4) := by
      rw [← hs's, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    have hs'2 : s' * s' = 1 := by
      have : g * (s' * s') * g⁻¹ = 1 := by
        calc g * (s' * s') * g⁻¹ = (g * s' * g⁻¹) * (g * s' * g⁻¹) := by group
          _ = 1 := by rw [hs's', hs2]
      calc s' * s' = g⁻¹ * (g * (s' * s') * g⁻¹) * g := by group
        _ = 1 := by rw [this]; group
    have hs'1 : s' ≠ 1 := fun h => hs1 (by rw [← hs's', h]; group)
    obtain ⟨j₁, hj₁, ht₁, ht₁1⟩ := exists_conj_kbar_of_mul_self O h4 (by omega) hsJ hs2 hs1
    obtain ⟨j₂, hj₂, ht₂, -⟩ := exists_conj_kbar_of_mul_self O h4 (by omega) hs'J hs'2 hs'1
    have hxe : (j₂⁻¹ * g⁻¹ * j₁) * (j₁⁻¹ * (s : Cbar O h4) * j₁) * (j₂⁻¹ * g⁻¹ * j₁)⁻¹ =
        j₂⁻¹ * s' * j₂ := by
      rw [← hs's']; group
    have heq := eq_of_isConj_of_mem_kbar O h4 (by omega) ht₁ ht₂ (isConj_iff.2 ⟨_, hxe⟩)
    have hx : j₂⁻¹ * g⁻¹ * j₁ ∈ centralizer ({j₁⁻¹ * (s : Cbar O h4) * j₁} : Set (Cbar O h4)) := by
      rw [mem_centralizer_singleton_iff]
      calc (j₂⁻¹ * g⁻¹ * j₁) * (j₁⁻¹ * (s : Cbar O h4) * j₁) =
          ((j₂⁻¹ * g⁻¹ * j₁) * (j₁⁻¹ * (s : Cbar O h4) * j₁) * (j₂⁻¹ * g⁻¹ * j₁)⁻¹) *
            (j₂⁻¹ * g⁻¹ * j₁) := by group
        _ = (j₁⁻¹ * (s : Cbar O h4) * j₁) * (j₂⁻¹ * g⁻¹ * j₁) := by rw [hxe, ← heq]
    have hxN := hNL (hcent ht₁ ht₁1 hx)
    have hj₁N : j₁ ∈ normalizer (Jbar O h4 : Set (Cbar O h4)) := le_normalizer hj₁
    have hj₂N : j₂ ∈ normalizer (Jbar O h4 : Set (Cbar O h4)) := le_normalizer hj₂
    apply hg
    have e : g = (j₂ * (j₂⁻¹ * g⁻¹ * j₁) * j₁⁻¹)⁻¹ := by group
    rw [e]
    exact inv_mem (mul_mem (mul_mem hj₂N hxN) (inv_mem hj₁N))
  ·
    refine le_antisymm (fun g hg => ?_) hNL
    have heJ : ebar O h4 ∈ Jbar O h4 := kbar_le_centralizer O h4 heK
    have hsJ : g * ebar O h4 * g⁻¹ ∈ Jbar O h4 := (mem_normalizer_iff.1 hg _).1 heJ
    have hs2 : (g * ebar O h4 * g⁻¹) * (g * ebar O h4 * g⁻¹) = 1 := by
      calc (g * ebar O h4 * g⁻¹) * (g * ebar O h4 * g⁻¹) = g * (ebar O h4 * ebar O h4) * g⁻¹ := by
            group
        _ = 1 := by rw [he2]; group
    have hs1 : g * ebar O h4 * g⁻¹ ≠ 1 := fun h => he1 (by
      calc ebar O h4 = g⁻¹ * (g * ebar O h4 * g⁻¹) * g := by group
        _ = 1 := by rw [h]; group)
    obtain ⟨j, hj, ht, -⟩ := exists_conj_kbar_of_mul_self O h4 (by omega) hsJ hs2 hs1
    have heq := eq_of_isConj_of_mem_kbar O h4 (by omega) heK ht
      (isConj_iff.2 ⟨j⁻¹ * g, by group⟩)
    have hx : j⁻¹ * g ∈ centralizer ({ebar O h4} : Set (Cbar O h4)) := by
      rw [mem_centralizer_singleton_iff]
      calc j⁻¹ * g * ebar O h4 = (j⁻¹ * (g * ebar O h4 * g⁻¹) * j) * (j⁻¹ * g) := by group
        _ = ebar O h4 * (j⁻¹ * g) := by rw [← heq]
    have hjN : j ∈ normalizer (L0bar O h4 : Set (Cbar O h4)) := hJL hj
    have e : g = j * (j⁻¹ * g) := by group
    rw [e]
    exact mul_mem hjN (hcent heK he1 hx)
  ·
    intro g h
    have hle : (L0bar O h4).map (MulAut.conj g).toMonoidHom ≤ Jbar O h4 := by
      rw [commutator_comm] at h
      exact commutator_eq_bot_iff_le_centralizer.1 h
    set Lg := (L0bar O h4).map (MulAut.conj g).toMonoidHom with hLg
    have hcardLg : Nat.card Lg = Nat.card (alternatingGroup (Fin (m - 1))) := by
      rw [hLg, Subgroup.card_map_of_injective (MulAut.conj g).injective]
      exact Nat.card_congr (L0barEquiv O h4 (by omega)).toEquiv
    have h8 : 2 ^ 3 ∣ Nat.card Lg := by
      rw [hcardLg]
      have : Nontrivial (Fin (m - 1)) := Fin.nontrivial_iff_two_le.2 (by omega)
      have h2 := two_mul_nat_card_alternatingGroup (α := Fin (m - 1))
      rw [Nat.card_perm, Nat.card_fin] at h2
      have h16 : 16 ∣ (m - 1).factorial :=
        (show 16 ∣ Nat.factorial 6 by decide).trans (Nat.factorial_dvd_factorial (by omega))
      rw [← h2] at h16
      have : (16 : ℕ) = 2 * 8 := by norm_num
      rw [this] at h16
      exact Nat.dvd_of_mul_dvd_mul_left (by norm_num) h16
    obtain ⟨K, hK⟩ := Sylow.exists_subgroup_card_pow_prime 2 h8
    set Q := K.map Lg.subtype with hQ
    have hQcard : Nat.card Q = 8 := by
      rw [hQ, Subgroup.card_map_of_injective Lg.subtype_injective, hK]; norm_num
    have hQJ : Q ≤ Jbar O h4 := by
      rintro _ ⟨k, -, rfl⟩
      exact hle k.2
    have hQp : IsPGroup 2 Q := IsPGroup.of_card (n := 3) (by rw [hQcard]; norm_num)
    obtain ⟨j, -, hjk⟩ := exists_conj_kbar O h4 (by omega) hQJ hQp
    have hinj : Function.Injective (fun q : Q => (⟨j⁻¹ * q * j, hjk q q.2⟩ : kbar O h4)) := by
      intro a b hab
      have := congrArg Subtype.val hab
      simp only at this
      exact Subtype.ext (by simpa using this)
    have := Nat.card_le_card_of_injective _ hinj
    have h4' := card_kbar_le O h4
    omega

end Std

end CFSG.OddStandard.AltStdSec
