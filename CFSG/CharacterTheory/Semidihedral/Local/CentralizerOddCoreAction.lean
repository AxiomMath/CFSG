module

public import CFSG.CharacterTheory.Semidihedral.Local.CoprimeCentralizerQuotient

public section

open scoped commutatorElement

namespace CFSG.Semidihedral.Local

open CFSG.Semidihedral.Principal

theorem mem_of_pow_eq_one_of_index {H : Type*} [Group H] [Finite H] {p : ℕ} [Fact p.Prime]
    (L : Subgroup H) [L.Normal] (hL : ¬ p ∣ L.index) {y : H} {k : ℕ} (hy : y ^ p ^ k = 1) :
    y ∈ L := by
  have h1 : orderOf (QuotientGroup.mk' L y) ∣ p ^ k := by
    apply orderOf_dvd_of_pow_eq_one
    rw [← map_pow, hy, map_one]
  have h2 : orderOf (QuotientGroup.mk' L y) ∣ L.index := by
    rw [Subgroup.index]
    exact orderOf_dvd_natCard _
  have hcop : Nat.Coprime (p ^ k) L.index :=
    Nat.Coprime.pow_left _ ((Nat.Prime.coprime_iff_not_dvd Fact.out).mpr hL)
  have h3 := Nat.eq_one_of_dvd_coprimes hcop h1 h2
  rw [orderOf_eq_one_iff] at h3
  exact (QuotientGroup.eq_one_iff y).mp h3

theorem centralizer_odd_core_action_from_odd_index_subgroup {G : Type*} [Group G] [Finite G]
    (p : ℕ) [Fact p.Prime] (N : Subgroup G) [N.Normal] (hN : ¬ p ∣ Nat.card N)
    (L : Subgroup (G ⧸ N)) [L.Normal] (hL : ¬ p ∣ L.index) (x : G)
    (hx : ∃ k : ℕ, orderOf x = p ^ k)
    (hcore : CFSG.pPrimeCore p ↥(L ⊓ Subgroup.centralizer {QuotientGroup.mk' N x}) ≤
      Subgroup.center (L ⊓ Subgroup.centralizer {QuotientGroup.mk' N x} : Subgroup (G ⧸ N))) :
    ∀ P : Subgroup G, P ≤ Subgroup.centralizer {x} → IsPGroup p P →
      ⁅P, (CFSG.pPrimeCore p (Subgroup.centralizer ({x} : Set G))).map
        (Subgroup.centralizer ({x} : Set G)).subtype⁆ ≤ N := by
  intro P hPx hP
  obtain ⟨k, hk⟩ := hx
  have hpx : IsPGroup p (Subgroup.zpowers x) :=
    IsPGroup.of_card (n := k) (by rw [Nat.card_zpowers, hk])
  have hcore_map := (coprime_centralizer_prime_complement_core_quotient p N hN
    (Subgroup.zpowers x) hpx).2.1
  rw [MonoidHom.map_zpowers] at hcore_map
  rw [Subgroup.zpowers_eq_closure, Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure,
    Subgroup.centralizer_closure] at hcore_map
  set π := QuotientGroup.mk' N with hπ
  set C : Subgroup (G ⧸ N) := Subgroup.centralizer {π x} with hC
  set CL : Subgroup (G ⧸ N) := L ⊓ C with hCL
  set B : Subgroup (G ⧸ N) := (CFSG.pPrimeCore p C).map C.subtype with hB
  have hPbar : ∀ g ∈ P, π g ∈ CL := by
    intro g hg
    obtain ⟨j, hj⟩ := hP ⟨g, hg⟩
    have hgj : g ^ p ^ j = 1 := by simpa using congrArg Subtype.val hj
    refine Subgroup.mem_inf.mpr
      ⟨mem_of_pow_eq_one_of_index L hL (k := j) (by rw [← map_pow, hgj, map_one]), ?_⟩
    rw [hC, Subgroup.mem_centralizer_singleton_iff]
    rw [← map_mul, ← map_mul, Subgroup.mem_centralizer_singleton_iff.mp (hPx hg)]
  have hBnormal : ∀ c ∈ C, ∀ b ∈ B, c * b * c⁻¹ ∈ B := by
    intro c hc b hb
    obtain ⟨b', hb', rfl⟩ := hb
    exact ⟨⟨c, hc⟩ * b' * ⟨c, hc⟩⁻¹,
      (CFSG.pPrimeCore_normal (p := p) (G := C)).conj_mem b' hb' ⟨c, hc⟩, rfl⟩
  have hBcop : Nat.Coprime p (Nat.card B) := by
    rw [hB, Subgroup.card_map_of_injective C.subtype_injective]
    exact CFSG.pPrimeCore_coprime_card (p := p) (G := C)
  have hJcentral : ∀ j ∈ B ⊓ L, ∀ y ∈ CL, y * j = j * y := by
    intro j hj y hy
    have hjCL : j ∈ CL := ⟨hj.2, (Subgroup.map_subtype_le _) hj.1⟩
    let J' : Subgroup CL := (B ⊓ L).subgroupOf CL
    have hJ'normal : J'.Normal := by
      constructor
      intro a ha c
      rw [Subgroup.mem_subgroupOf] at ha ⊢
      refine ⟨hBnormal c (c.2.2) a ha.1, ?_⟩
      exact (inferInstance : L.Normal).conj_mem a ha.2 c
    have hJ'cop : Nat.Coprime p (Nat.card J') := by
      refine hBcop.coprime_dvd_right ?_
      rw [← Subgroup.card_map_of_injective CL.subtype_injective, Subgroup.subgroupOf_map_subtype]
      exact Subgroup.card_dvd_of_le (inf_le_left.trans inf_le_left)
    have hJ'core : J' ≤ CFSG.pPrimeCore p CL := le_sSup ⟨hJ'normal, hJ'cop⟩
    have hjcenter : (⟨j, hjCL⟩ : CL) ∈ Subgroup.center CL := hcore (hJ'core hj)
    have := (Subgroup.mem_center_iff.mp hjcenter) ⟨y, hy⟩
    exact congrArg Subtype.val this
  have hcomm : ∀ y ∈ CL, ∀ b ∈ B, y * b * y⁻¹ * b⁻¹ ∈ B ⊓ L := by
    intro y hy b hb
    refine ⟨B.mul_mem (hBnormal y hy.2 b hb) (B.inv_mem hb), ?_⟩
    have h1 : b * y⁻¹ * b⁻¹ ∈ L := (inferInstance : L.Normal).conj_mem _ (L.inv_mem hy.1) b
    have h2 := L.mul_mem hy.1 h1
    rwa [← mul_assoc, ← mul_assoc] at h2
  have hPB : ∀ g ∈ P, ∀ b ∈ B, π g * b = b * π g := by
    have : (CFSG.pPrimeCore p C).Normal := CFSG.pPrimeCore_normal (p := p) (G := C)
    let ι : P →* C := (π.comp P.subtype).codRestrict C (fun a => (hPbar a a.2).2)
    let α : P →* MulAut (CFSG.pPrimeCore p C) := MulAut.conjNormal.comp ι
    let Jc : Subgroup (CFSG.pPrimeCore p C) :=
      L.comap (C.subtype.comp (CFSG.pPrimeCore p C).subtype)
    have hJc : ¬ p ∣ Nat.card Jc := by
      intro hdvd
      have h1 : Nat.card Jc ∣ Nat.card (CFSG.pPrimeCore p C) := Subgroup.card_subgroup_dvd_card Jc
      exact (Nat.Prime.coprime_iff_not_dvd Fact.out).mp
        (CFSG.pPrimeCore_coprime_card (p := p) (G := C)) (hdvd.trans h1)
    have hα : ∀ (a : P) (y : CFSG.pPrimeCore p C),
        (((α a y : CFSG.pPrimeCore p C) : C) : G ⧸ N) = π a * ((y : C) : G ⧸ N) * (π a)⁻¹ := by
      intro a y
      simp [α, ι]
      rfl
    have hJcmem : ∀ y : CFSG.pPrimeCore p C, y ∈ Jc ↔ ((y : C) : G ⧸ N) ∈ L := fun y => Iff.rfl
    intro g hg b hb
    obtain ⟨b', hb', rfl⟩ := hb
    have hbB : ((b' : C) : G ⧸ N) ∈ B := ⟨b', hb', rfl⟩
    obtain ⟨c, hcJ, hfix⟩ := (coprime_invariant_coset_fixed p hP α Jc hJc ⟨b', hb'⟩).1 (by
      intro a y hy
      rw [hJcmem] at hy ⊢
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, hα] at hy ⊢
      have h1 := (inferInstance : L.Normal).conj_mem _ hy (π a)
      have h2 := (hcomm (π a) (hPbar a a.2) _ hbB).2
      have heq : π a * ((y : C) : G ⧸ N) * (π a)⁻¹ * ((b' : C) : G ⧸ N)⁻¹ =
          (π a * (((y : C) : G ⧸ N) * ((b' : C) : G ⧸ N)⁻¹) * (π a)⁻¹) *
            (π a * ((b' : C) : G ⧸ N) * (π a)⁻¹ * ((b' : C) : G ⧸ N)⁻¹) := by group
      rw [heq]
      exact L.mul_mem h1 h2)
    have hfixa := congrArg (fun z : CFSG.pPrimeCore p C => ((z : C) : G ⧸ N)) (hfix ⟨g, hg⟩)
    simp only [hα] at hfixa
    rw [hJcmem] at hcJ
    simp only [Subgroup.coe_mul, Subgroup.coe_inv] at hcJ
    have hjB : ((c : C) : G ⧸ N) * ((b' : C) : G ⧸ N)⁻¹ ∈ B := by
      refine ⟨((c * ⟨b', hb'⟩⁻¹ : CFSG.pPrimeCore p C) : C), (c * ⟨b', hb'⟩⁻¹).2, ?_⟩
      simp
    have hcomm1 : Commute (π g) ((c : C) : G ⧸ N) := by
      rw [mul_inv_eq_iff_eq_mul] at hfixa
      exact hfixa
    have hcomm2 : Commute (π g) (((c : C) : G ⧸ N) * ((b' : C) : G ⧸ N)⁻¹) :=
      hJcentral _ ⟨hjB, hcJ⟩ _ (hPbar g hg)
    have h := hcomm2.inv_right.mul_right hcomm1
    have heq : (((c : C) : G ⧸ N) * ((b' : C) : G ⧸ N)⁻¹)⁻¹ * ((c : C) : G ⧸ N) =
        ((b' : C) : G ⧸ N) := by group
    rw [heq] at h
    exact h
  rw [Subgroup.commutator_le]
  intro g hg h hh
  rw [← QuotientGroup.eq_one_iff (N := N), ← QuotientGroup.mk'_apply]
  have hhB : π h ∈ B := by
    rw [← hcore_map]
    exact ⟨h, hh, rfl⟩
  change π ⁅g, h⁆ = 1
  rw [map_commutatorElement, commutatorElement_def, hPB g hg _ hhB]
  group

end CFSG.Semidihedral.Local
