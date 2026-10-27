module

public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec7ToolsB
public import CFSG.LocalAnalysis.GLTheoremB.PCompBasics
public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Inputs710

public section

namespace CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec7L710

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.HardMathSupport.Solomon.Coordinator
open CFSG.HardMathSupport.Solomon.UniquenessMaximal

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem isPGroup_three_zpowers_iff {c : G} :
    IsPGroup 3 (Subgroup.zpowers c) ↔ ∃ n : ℕ, c ^ (3 ^ n) = 1 := by
  constructor
  · intro h
    obtain ⟨n, hn⟩ := h ⟨c, Subgroup.mem_zpowers c⟩
    exact ⟨n, congrArg Subtype.val hn⟩
  · rintro ⟨n, hn⟩ ⟨x, hx⟩
    obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.1 hx
    refine ⟨n, Subtype.ext ?_⟩
    show (c ^ m) ^ (3 ^ n) = 1
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hn, one_zpow]

omit [Finite G] in
theorem le_normalizer_closure_three_elements (L : Subgroup G) :
    L ≤ Subgroup.normalizer
      ((Subgroup.closure {x : G | x ∈ L ∧ ∃ n : ℕ, x ^ (3 ^ n) = 1} : Subgroup G) : Set G) := by
  have key : ∀ g ∈ L, ∀ j ∈ Subgroup.closure {x : G | x ∈ L ∧ ∃ n : ℕ, x ^ (3 ^ n) = 1},
      g * j * g⁻¹ ∈ Subgroup.closure {x : G | x ∈ L ∧ ∃ n : ℕ, x ^ (3 ^ n) = 1} := by
    intro g hg j hj
    refine Subgroup.closure_induction (p := fun j _ => g * j * g⁻¹ ∈ Subgroup.closure
      {x : G | x ∈ L ∧ ∃ n : ℕ, x ^ (3 ^ n) = 1}) (fun x hx => ?_) (by simp [one_mem])
      (fun u v _ _ hu hv => ?_) (fun u _ hu => ?_) hj
    · obtain ⟨hxL, n, hn⟩ := hx
      refine Subgroup.subset_closure ⟨L.mul_mem (L.mul_mem hg hxL) (L.inv_mem hg), n, ?_⟩
      rw [conj_pow, hn]
      simp
    · have : g * (u * v) * g⁻¹ = (g * u * g⁻¹) * (g * v * g⁻¹) := by group
      rw [this]; exact mul_mem hu hv
    · have : g * u⁻¹ * g⁻¹ = (g * u * g⁻¹)⁻¹ := by group
      rw [this]; exact inv_mem hu
  intro g hg
  rw [Subgroup.mem_normalizer_iff]
  intro j
  exact ⟨key g hg j, fun hj => by
    have := key g⁻¹ (inv_mem hg) _ hj
    simpa [mul_assoc] using this⟩

theorem closure_three_eq_of_component {X L : Subgroup G} (hL : GLAPComponent 3 X L)
    (h : IsLThreeFour (↥L ⧸ GLAPPrimeCore 3 ↥L)) :
    Subgroup.closure {x : G | x ∈ L ∧ ∃ n : ℕ, x ^ (3 ^ n) = 1} = L := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set S : Set G := {x : G | x ∈ L ∧ ∃ n : ℕ, x ^ (3 ^ n) = 1} with hS
  set J : Subgroup G := Subgroup.closure S with hJ
  have hJL : J ≤ L := (Subgroup.closure_le L).2 fun x hx => hx.1
  have hJnorm : (J.subgroupOf L).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hJL).2 (le_normalizer_closure_three_elements L)
  have hJsn : IsSubnormal J X := IsSubnormal.step hJL hJnorm hL.2.1
  obtain ⟨hsimple, -⟩ := isSimpleGroup_of_isLThreeFour h
  have hQcard : Nat.card (↥L ⧸ GLAPPrimeCore 3 ↥L) = 20160 := card_eq_of_isLThreeFour h
  set π := QuotientGroup.mk' (GLAPPrimeCore 3 ↥L) with hπ
  set M : Subgroup (↥L ⧸ GLAPPrimeCore 3 ↥L) := (J.subgroupOf L).map π with hM
  have hMn : M.Normal := hJnorm.map π (QuotientGroup.mk'_surjective _)
  have hMtop : M = ⊤ := by
    rcases hMn.eq_bot_or_eq_top with hbot | htop
    · exfalso
      have h3L : 3 ∣ Nat.card ↥L := by
        have := Subgroup.card_dvd_of_le (le_top : GLAPPrimeCore 3 ↥L ≤ ⊤)
        have h2 : Nat.card (↥L ⧸ GLAPPrimeCore 3 ↥L) ∣ Nat.card ↥L :=
          ⟨Nat.card (GLAPPrimeCore 3 ↥L), by
            rw [mul_comm, ← Subgroup.card_mul_index (GLAPPrimeCore 3 ↥L)]
            rfl⟩
        exact (hQcard ▸ (by norm_num : 3 ∣ 20160)).trans h2
      obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := ↥L) 3 h3L
      have hxS : (x : G) ∈ S := ⟨x.2, 1, by
        have : x ^ 3 = 1 := by rw [← hx]; exact pow_orderOf_eq_one x
        simpa using congrArg Subtype.val this⟩
      have hxJ : x ∈ J.subgroupOf L := Subgroup.subset_closure hxS
      have hπx : π x ∈ M := ⟨x, hxJ, rfl⟩
      rw [hbot, Subgroup.mem_bot, hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hπx
      have hcop : Nat.Coprime 3 (Nat.card (GLAPPrimeCore 3 ↥L)) := CFSG.pPrimeCore_coprime_card
      have hord : orderOf (⟨x, hπx⟩ : GLAPPrimeCore 3 ↥L) ∣ Nat.card (GLAPPrimeCore 3 ↥L) :=
        orderOf_dvd_natCard _
      rw [Subgroup.orderOf_mk, hx] at hord
      exact absurd (Nat.Coprime.eq_one_of_dvd hcop hord) (by norm_num)
    · exact htop
  have hbar : barX 3 X L ≤ barX 3 X J := by
    refine barX_le_of_forall (hJL.trans hL.1) fun k hk => ?_
    have hkM : π ⟨k, hk⟩ ∈ M := hMtop ▸ Subgroup.mem_top _
    obtain ⟨j, hj, hjk⟩ := hkM
    refine ⟨(j : G), (Subgroup.mem_subgroupOf).1 hj, ?_⟩
    have hker : j⁻¹ * ⟨k, hk⟩ ∈ GLAPPrimeCore 3 ↥L := by
      rw [← QuotientGroup.eq]; exact hjk
    exact glaPPrimeCoreOf_le_of_isSubnormal Nat.prime_three hL.2.1 ⟨_, hker, rfl⟩
  by_contra hne
  have hlt : J < L := lt_of_le_of_ne hJL hne
  exact hL.2.2.2 J hlt hJsn (le_antisymm (barX_mono 3 hJL) hbar)

theorem mem_of_mem_preimBarX_of_three {X I : Subgroup G} (hI : GLAPComponent 3 X I) {x : G}
    (hx : x ∈ preimBarX 3 X I) {n : ℕ} (hn : x ^ (3 ^ n) = 1) : x ∈ I := by
  obtain ⟨k, hk, hko⟩ := exists_mul_of_mem_preimBarX 3 hx
  set P := preimBarX 3 X I with hP
  have hIP : I ≤ P := le_preimBarX 3 hI.1
  have hnorm : (I.subgroupOf P).Normal := glaPComponent_normal_preimBarX hI
  set o : G := k⁻¹ * x with ho
  have hoP : o ∈ P := P.mul_mem (P.inv_mem (hIP hk)) hx
  have hxo : x = k * o := by simp [ho]
  set π := QuotientGroup.mk' (I.subgroupOf P) with hπ
  have hkπ : π ⟨k, hIP hk⟩ = 1 := (QuotientGroup.eq_one_iff _).2 ((Subgroup.mem_subgroupOf).2 hk)
  have hπx : π ⟨x, hx⟩ = π ⟨o, hoP⟩ := by
    have : (⟨x, hx⟩ : ↥P) = ⟨k, hIP hk⟩ * ⟨o, hoP⟩ := Subtype.ext hxo
    rw [this, map_mul, hkπ, one_mul]
  have h1 : (π ⟨o, hoP⟩) ^ (3 ^ n) = 1 := by
    rw [← hπx, ← map_pow]
    have : (⟨x, hx⟩ : ↥P) ^ (3 ^ n) = 1 := Subtype.ext (by simpa using hn)
    rw [this, map_one]
  have hcop : Nat.Coprime 3 (Nat.card (GLAPPrimeCoreOf 3 X)) :=
    (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).2 (not_dvd_card_glaPPrimeCoreOf Nat.prime_three X)
  have hoO : o ∈ GLAPPrimeCoreOf 3 X := hko
  have h2 : orderOf o ∣ Nat.card (GLAPPrimeCoreOf 3 X) := by
    have := orderOf_dvd_natCard (⟨o, hoO⟩ : GLAPPrimeCoreOf 3 X)
    rwa [Subgroup.orderOf_mk] at this
  have h3 : orderOf (π ⟨o, hoP⟩) ∣ orderOf o := by
    have := orderOf_map_dvd π (⟨o, hoP⟩ : ↥P)
    rwa [Subgroup.orderOf_mk] at this
  have h4 : orderOf (π ⟨o, hoP⟩) ∣ 3 ^ n := orderOf_dvd_of_pow_eq_one h1
  have h5 : orderOf (π ⟨o, hoP⟩) = 1 := by
    have h6 : orderOf (π ⟨o, hoP⟩) ∣ Nat.card (GLAPPrimeCoreOf 3 X) := h3.trans h2
    have h7 : Nat.Coprime (3 ^ n) (Nat.card (GLAPPrimeCoreOf 3 X)) := Nat.Coprime.pow_left n hcop
    exact Nat.Coprime.eq_one_of_dvd (Nat.Coprime.coprime_dvd_left h4 h7) h6
  have h8 : π ⟨o, hoP⟩ = 1 := orderOf_eq_one_iff.1 h5
  have hoI : o ∈ I := by
    have := (QuotientGroup.eq_one_iff _).1 h8
    exact (Subgroup.mem_subgroupOf).1 this
  rw [hxo]
  exact I.mul_mem hk hoI

omit [Finite G] in
private theorem eq_one_of_isPGroup_of_mem_core {L : Subgroup G} [Finite G]
    {x : ↥L} (hx : x ∈ GLAPPrimeCore 3 ↥L) {n : ℕ} (hn : x ^ (3 ^ n) = 1) : x = 1 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hcop : Nat.Coprime 3 (Nat.card (GLAPPrimeCore 3 ↥L)) := CFSG.pPrimeCore_coprime_card
  have hord : orderOf (⟨x, hx⟩ : GLAPPrimeCore 3 ↥L) ∣ Nat.card (GLAPPrimeCore 3 ↥L) :=
    orderOf_dvd_natCard _
  rw [Subgroup.orderOf_mk] at hord
  have h4 : orderOf x ∣ 3 ^ n := orderOf_dvd_of_pow_eq_one hn
  have h7 : Nat.Coprime (3 ^ n) (Nat.card (GLAPPrimeCore 3 ↥L)) := Nat.Coprime.pow_left n hcop
  exact orderOf_eq_one_iff.1
    (Nat.Coprime.eq_one_of_dvd (Nat.Coprime.coprime_dvd_left h4 h7) hord)

theorem card_le_nine_of_isLThreeFour {I : Subgroup G}
    (h : IsLThreeFour (↥I ⧸ GLAPPrimeCore 3 ↥I)) {R : Subgroup G} (hRI : R ≤ I)
    (hR : IsPGroup 3 ↥R) : Nat.card ↥R ≤ 9 := by
  have hQcard : Nat.card (↥I ⧸ GLAPPrimeCore 3 ↥I) = 20160 := card_eq_of_isLThreeFour h
  set R' : Subgroup ↥I := R.subgroupOf I with hR'
  have hR'3 : IsPGroup 3 ↥R' := hR.comap_subtype
  set f : ↥R' →* (↥I ⧸ GLAPPrimeCore 3 ↥I) := (QuotientGroup.mk' (GLAPPrimeCore 3 ↥I)).comp R'.subtype
  have hf : Function.Injective f := by
    rw [injective_iff_map_eq_one]
    intro x hx
    obtain ⟨n, hn⟩ := hR'3 x
    have hxc : (x : ↥I) ∈ GLAPPrimeCore 3 ↥I :=
      (QuotientGroup.eq_one_iff _).1 hx
    have := eq_one_of_isPGroup_of_mem_core hxc (n := n) (congrArg Subtype.val hn)
    exact Subtype.ext this
  have hcardR : Nat.card ↥R = Nat.card ↥R' :=
    (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hRI).toEquiv).symm
  obtain ⟨k, hk⟩ := hR'3.exists_card_eq
  have hdvd : Nat.card ↥R' ∣ 20160 := by
    rw [← hQcard, ← Nat.card_range_of_injective hf]
    exact Subgroup.card_subgroup_dvd_card f.range
  rw [hk] at hdvd
  rw [hcardR, hk]
  by_contra hlt
  have hk3 : 3 ≤ k := by
    by_contra hk3
    push Not at hk3
    interval_cases k <;> simp at hlt
  have : 3 ^ 3 ∣ 3 ^ k := pow_dvd_pow 3 hk3
  have := this.trans hdvd
  norm_num at this

theorem oPrimeP_le_of_isLThreeFour {I : Subgroup G}
    (h : IsLThreeFour (↥I ⧸ GLAPPrimeCore 3 ↥I)) : oPrimeP 3 I ≤ GLAPPrimeCoreOf 3 I := by
  obtain ⟨hsimple, -⟩ := isSimpleGroup_of_isLThreeFour h
  have hQcard : Nat.card (↥I ⧸ GLAPPrimeCore 3 ↥I) = 20160 := card_eq_of_isLThreeFour h
  have hcore : CFSG.Open.pCore 3 (↥I ⧸ GLAPPrimeCore 3 ↥I) = ⊥ := by
    rw [CFSG.pCore_eq_iSup]
    refine le_bot_iff.1 (iSup_le fun N => iSup_le fun hN => iSup_le fun hNp => ?_)
    rcases hN.eq_bot_or_eq_top with hb | ht
    · exact hb ▸ le_rfl
    · exfalso
      subst ht
      obtain ⟨k, hk⟩ := hNp.exists_card_eq
      rw [Subgroup.card_top, hQcard] at hk
      have h3 : 2 ∣ 3 ^ k := hk ▸ (by norm_num : 2 ∣ 20160)
      exact absurd (Nat.Prime.dvd_of_dvd_pow Nat.prime_two h3) (by norm_num)
  unfold oPrimeP GLAPPrimeCoreOf
  rw [hcore]
  exact Subgroup.map_mono fun x hx =>
    (QuotientGroup.eq_one_iff x).1 (Subgroup.mem_bot.1 (Subgroup.mem_comap.1 hx))

end CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec7L710
